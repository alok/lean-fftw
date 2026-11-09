import LeanFFTW.Asm.Planner

open LeanFFTW LeanFFTW.Asm LeanFFTW.Gen

/-- Pseudo-random doubles in `[-1, 1)`. -/
def randArr (n : Nat) (seed : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  let mut x : UInt64 := UInt64.ofNat (seed * 2654435761 + 12345)
  for _ in [0:n] do
    x := x * 6364136223846793005 + 1442695040888963407
    a := a.push (((x >>> 11).toFloat / 9007199254740992.0) * 2.0 - 1.0)
  return a

def zeros (n : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  for _ in [0:n] do a := a.push 0.0
  return a

def firstDiff (a b : FloatArray) : Option Nat := Id.run do
  if a.size != b.size then return some 0
  for i in [0:a.size] do
    if a[i]!.toBits != b[i]!.toBits then return some i
  return none

/-- Radix sequences of the in-place schedule for `N`: first radix in `{8, 16, 32}`. -/
partial def seqs (N : Nat) : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  for f in [8, 16, 32] do
    if N % f == 0 && N > f then
      out := out ++ (tails (N / f) #[f])
  return out
where
  tails (M : Nat) (rs : Array Nat) : Array (Array Nat) := Id.run do
    let mut out : Array (Array Nat) := #[]
    if M == 1 then return #[rs]
    for m in [2, 4, 8, 16, 32] do
      if M % m == 0 then out := out ++ tails (M / m) (rs.push m)
    return out

def checkOne (N : Nat) (fwd : Bool) (rs : Array Nat) (T Q : Nat) (inplace : Bool)
    (base inp ref : FloatArray) (ran : IO.Ref Nat) : IO Bool := do
  let some src := inplacePlan N fwd rs T Q inplace base | return true
  ran.modify (· + 1)
  let plan ← src.build inplace
  let out := if inplace then randArr (2 * N) 1 else zeros (2 * N)
  -- `inp` was produced by the same generator with the same seed
  plan.run (if inplace then addr out else addr inp) (addr out)
  match firstDiff out ref with
  | none => return true
  | some i =>
      IO.println s!"MISMATCH N={N} fwd={fwd} rs={rs} T={T} Q={Q} inplace={inplace} at {i}: {out[i]!} vs {ref[i]!}"
      return false

/-- `time N T Q R₀ R₁ …`: time one in-place plan (best of 8). -/
def timeMain (args : List String) : IO UInt32 := do
  let nums := args.map String.toNat!
  let N := nums[0]!
  let T := nums[1]!
  let Q := nums[2]!
  let rs := (nums.drop 3).toArray
  let base := baseTable N true
  let some src := inplacePlan N true rs T Q false base | IO.println "unsupported"; return 1
  let plan ← src.build false
  let inp := zeros (2 * N + 8)
  -- a different size: equal pure calls are shared, and the arrays must be distinct
  let out := zeros (2 * N + 16)
  let ia := (addr inp + 63) / 64 * 64
  let oa := (addr out + 63) / 64 * 64
  let mut reps : Nat := 1
  repeat
    let t0 ← IO.monoNanosNow
    plan.run ia oa reps.toUSize
    let t1 ← IO.monoNanosNow
    if t1 - t0 > 10000000 then break
    reps := reps * 2
  let mut best : Float := 1e30
  for _ in [0:8] do
    let t0 ← IO.monoNanosNow
    plan.run ia oa reps.toUSize
    let t1 ← IO.monoNanosNow
    let d := (t1 - t0).toFloat / reps.toFloat
    if d < best then best := d
  IO.println s!"N={N} T={T} Q={Q} R={rs}  time {best} ns  (inp {inp.size} out {out.size})"
  return 0

def timeNode (src : PlanSrc) (ia oa : USize) : IO Float := do
  let plan ← src.build false
  let mut reps : Nat := 1
  repeat
    let t0 ← IO.monoNanosNow
    plan.run ia oa reps.toUSize
    let t1 ← IO.monoNanosNow
    if t1 - t0 > 2000000 then break
    reps := reps * 2
  let mut best : Float := 1e30
  for _ in [0:9] do
    let t0 ← IO.monoNanosNow
    plan.run ia oa reps.toUSize
    let t1 ← IO.monoNanosNow
    let d := (t1 - t0).toFloat / reps.toFloat
    if d < best then best := d
  return best

/-- `prof N R₀ R₁ …`: time the passes of the in-place schedule one by one (`T = 0`). -/
def profMain (args : List String) : IO UInt32 := do
  let nums := args.map String.toNat!
  let N := nums[0]!
  let rs := (nums.drop 1).toArray
  let base := baseTable N true
  let some src := inplacePlan N true rs 0 0 false base | IO.println "unsupported"; return 1
  let inp := zeros (2 * N + 8)
  -- a different size: equal pure calls are shared, and the arrays must be distinct
  let out := zeros (2 * N + 16)
  let ia := (addr inp + 63) / 64 * 64
  let oa := (addr out + 63) / 64 * 64
  let .loop _ _ _ _ _ ch := src.root | return 1
  let mut tot := 0.0
  for i in [0:ch.size] do
    let t ← timeNode { src with root := .seq #[ch[i]!] } ia oa
    tot := tot + t
    IO.println s!"pass {i} R={rs[i]!}  {t} ns  {t / N.toFloat} ns/elt"
  IO.println s!"sum {tot} ns; whole plan {← timeNode src ia oa} ns"
  -- the arrays must stay alive while their addresses are in use
  if inp.size + out.size == 0 then return 1
  return 0

/-- Bit-exact check of the whole-transform kernels. -/
def smallMain : IO UInt32 := do
  let mut bad := 0
  let mut n := 0
  for fwd in [true, false] do
    for (mode, tag) in [(Mode.csmall, "csmall"), (Mode.cfused, "cfused"), (Mode.ctwo, "ctwo")] do
      let cands : List (Array Nat) :=
        if mode == .csmall then csmallSizes.map (#[·])
        else ((if mode == .cfused then Asm.cfusedSet else Asm.ctwoSet).map fun (a, b, _) => #[a, b]).eraseDups
      for rs in cands do
        let N := rs.foldl (· * ·) 1
        let inp := randArr (2 * N) 1
        let ref := refTransform fwd N rs inp
        for inplace in [false, true] do
          let some src := smallPlan N fwd rs mode inplace | continue
          let plan ← src.build inplace
          let out := if inplace then randArr (2 * N) 1 else zeros (2 * N)
          plan.run (if inplace then addr out else addr inp) (addr out)
          n := n + 1
          if let some i := firstDiff out ref then
            bad := bad + 1
            IO.println s!"MISMATCH {tag} N={N} fwd={fwd} rs={rs} inplace={inplace} at {i}: {out[i]!} vs {ref[i]!}"
          if inp.size == 0 then return 1
  IO.println s!"small transforms: {n} plans, {bad} mismatches"
  return if bad == 0 then 0 else 1

/-- `plan lo hi`: plan every `N = 2^lo … 2^hi`, check the chosen plan bit for bit, print it. -/
def planMain (args : List String) : IO UInt32 := do
  let nums := args.map String.toNat!
  let mut bad := 0
  -- `LF_THREADS=n`: plan and run on `n` threads
  Pool.start ((← IO.getEnv "LF_THREADS").getD "1").toNat!
  for lg in [nums[0]!:nums[1]! + 1] do
    let N := 2 ^ lg
    for inplace in [false, true] do
      let ofs := ((← IO.getEnv "LF_OFS").getD "0").toNat!
      let inp := zeros (2 * N + 8)
      let out := zeros (2 * N + 16 + 8 * ofs)
      let ia := (addr inp + 63) / 64 * 64
      let oa := if inplace then ia else (addr out + 63) / 64 * 64 + (64 * ofs).toUSize
      if !inplace && ia == oa then IO.println "arrays not distinct"; return 1
      let t0 ← IO.monoNanosNow
      let some (plan, c) ← Planner.planMeasure N true ia oa (← Planner.effortFromEnv)
        | IO.println s!"N={N}: no plan"; bad := bad + 1
      let t1 ← IO.monoNanosNow
      -- check on fresh arrays
      let x := randArr (2 * N) 1
      let ref := refTransform true N c.rs x
      let y := if inplace then randArr (2 * N) 1 else zeros (2 * N)
      plan.run (if inplace then addr y else addr x) (addr y)
      let ok := (firstDiff y ref).isNone
      if !ok then bad := bad + 1
      IO.println s!"N={N} inplace={inplace} {Planner.modeTag c.mode} {c.rs.toList} T={c.T} Q={c.Q}{if c.par then " threads" else ""}  {c.t * 1e9} ns  planned in {(t1 - t0).toFloat * 1e-9} s  {if ok then "ok" else "MISMATCH"}"
      if inp.size + out.size + x.size == 0 then return 1
  Pool.stop
  return if bad == 0 then 0 else 1

/-- Mutants of a block: an instruction deleted, or an arithmetic or shuffle instruction
changed to a similar one; for the instructions `j ≡ phase (mod stride)`. -/
def mutants (is : Array Instr) (stride phase : Nat) : Array (String × Array Instr) := Id.run do
  let mut out : Array (String × Array Instr) := #[]
  for j in [0:is.size] do
    if j % stride != phase % stride then continue
    out := out.push ("delete", is.extract 0 j ++ is.extract (j + 1) is.size)
    let alt : Option (String × Instr) := match is[j]! with
      | .vfma op form w d s2 s3 =>
          let op' : VFma := match op with
            | .fmadd => .fmsub | .fmsub => .fmadd | .fnmadd => .fmadd
            | .fmaddsub => .fmsubadd | .fmsubadd => .fmaddsub
          some ("fused op", .vfma op' form w d s2 s3)
      | .vbin op w d s1 s2 =>
          let op' : VBin := match op with
            | .add => .sub | .sub => .add | .mul => .add | .xor => .add
            | .unpcklo => .unpckhi | .unpckhi => .unpcklo
          some ("binary op", .vbin op' w d s1 s2)
      | .vshufpd w d s1 s2 imm => some ("shuffle", .vshufpd w d s1 s2 (imm ^^^ 1))
      | .vshuff64x2 w d s1 s2 imm => some ("shuffle", .vshuff64x2 w d s1 s2 (imm ^^^ 1))
      | .vstore w m r => some ("store", .vstore w m ⟨(r.n + 1) % 32⟩)
      | _ => none
    if let some (k, i') := alt then out := out.push (k, is.set! j i')
  return out

/-- The checker must reject corrupted blocks: mutate every block the generator emits. An
accepted mutant is still correct (the checker is proved sound); the count shows how much of
each block the specification pins down. `asm_test mutate STRIDE` mutates one instruction
in `STRIDE` (all of them take about an hour). -/
def mutateMain (stride : Nat) : IO UInt32 := do
  match engineFile with
  | .error e => IO.eprintln e; return 1
  | .ok f =>
      let consts := f.pool.consts
      let mut blocks := 0
      let mut total := 0
      let mut accepted : Std.HashMap String Nat := {}
      let mut tried : Std.HashMap String Nat := {}
      for fn in f.fns do
        for (sp, w, is) in fn.blocks do
          blocks := blocks + 1
          unless check consts sp w is.toList do
            IO.eprintln s!"{fn.name}: the emitted block is rejected"; return 1
          for (k, m) in mutants is stride blocks do
            total := total + 1
            tried := tried.insert k (tried.getD k 0 + 1)
            if check consts sp w m.toList then accepted := accepted.insert k (accepted.getD k 0 + 1)
      let acc := accepted.fold (fun n _ v => n + v) 0
      IO.println s!"{blocks} blocks, {total} mutants, {total - acc} rejected, {acc} accepted"
      for (k, n) in tried.toList do
        IO.println s!"  {k}: {n} mutants, {accepted.getD k 0} accepted"
      return if acc * 100 ≤ total then 0 else 1

def main (args : List String) : IO UInt32 := do
  if args.head? == some "mutate" then return ← mutateMain ((args.getD 1 "1").toNat!)
  if args.head? == some "plan" then return ← planMain args.tail
  if args.head? == some "time" then return ← timeMain args.tail
  if args.head? == some "prof" then return ← profMain args.tail
  if args.head? == some "small" then return ← smallMain
  let maxLog := (args.getD 0 "12").toNat!
  let mut bad := 0
  let mut n := 0
  let ran ← IO.mkRef 0
  for lg in [6:maxLog + 1] do
    let N := 2 ^ lg
    for fwd in [true, false] do
      let base := baseTable N fwd
      let inp := randArr (2 * N) 1
      for rs in seqs N do
        let ref := refTransform fwd N rs inp
        for (T, Q) in [(0, 0), (1, 0), (1, 32), (2, 0), (2, 8), (2, 64), (3, 0), (3, 128)] do
          for inplace in [false, true] do
            n := n + 1
            if !(← checkOne N fwd rs T Q inplace base inp ref ran) then bad := bad + 1
    IO.println s!"N=2^{lg}: {← ran.get} of {n} plans ran so far, {bad} mismatches"
  return if bad == 0 then 0 else 1
