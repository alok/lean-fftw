import LeanFFTW.Native.Exec

/-!
Check and time the Lean-compiled backend.

  lake exe native_bench [check|time] [kmax]

`check`: for every size `2^k`, `k ≤ kmax`, and every radix sequence the backend runs (all
orders, for `N ≤ 2^10`; otherwise those in nonincreasing and nondecreasing order), compares
`exec` with the binary64 reference `refTransform` bit for bit, both directions.

`time`: for each size, measures each candidate plan of the backend (multisets of radices in
both orders), keeps the fastest, and prints its time per transform in nanoseconds, together
with the time of the reference implementation (the specification run as a program, boxed
`Array Float`) for sizes up to `2^12`.
-/

open LeanFFTW LeanFFTW.Gen LeanFFTW.Native

/-- Radix sequences over {2,4,8,16} with product `2^k` (all orders). -/
partial def seqs (k : Nat) : List (List Nat) :=
  if k == 0 then [[]] else
  [1, 2, 3, 4].foldr (fun e acc =>
    if e ≤ k then (seqs (k - e)).map (2 ^ e :: ·) ++ acc else acc) []

/-- Multisets of radices with product `2^k`, each in nonincreasing and nondecreasing order. -/
def sortedSeqs (k : Nat) : List (List Nat) :=
  let desc := (seqs k).filter fun l => l == l.mergeSort (· ≥ ·)
  desc ++ (desc.map List.reverse).filter (fun l => l != l.reverse)

def input (N : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity (2 * N)
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  for _ in [0:2 * N] do
    s := s * 6364136223846793005 + 1442695040888963407
    a := a.push ((s >>> 11).toFloat / 9007199254740992.0 - 0.5)
  return a

def bitEq (a b : FloatArray) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => a[i]!.toBits == b[i]!.toBits

/-- Best of `reps` rounds of `iters` transforms, in nanoseconds per transform. -/
def timeIt (iters reps : Nat) (f : FloatArray → FloatArray) (y0 : FloatArray) : IO Float := do
  let mut best : Float := 1e30
  let mut y := y0
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    for _ in [0:iters] do
      y := f y
    let t1 ← IO.monoNanosNow
    best := min best ((t1 - t0).toFloat / iters.toFloat)
  if y.size == 7 then IO.println "" -- keep `y` live
  return best

/-- Iterations so that one round takes about `target` ns. -/
def calibrate (f : FloatArray → FloatArray) (y0 : FloatArray) (target : Float) : IO Nat := do
  let mut n := 1
  repeat
    let t ← timeIt n 1 f y0
    if t * n.toFloat ≥ target / 4 || n ≥ 1 <<< 26 then
      return max 1 (target / t).toUInt64.toNat
    n := n * 4
  return n

def check (kmax : Nat) : IO Unit := do
  let mut nplans := 0
  let mut bad := 0
  for k in [1:kmax + 1] do
    let N := 2 ^ k
    let x := input N
    let cands := if k ≤ 10 then seqs k else sortedSeqs k
    for l in cands do
      for fwd in [true, false] do
        let rs := l.toArray
        match Plan.make? fwd N rs with
        | none => IO.println s!"not a plan: {N} {rs}"; bad := bad + 1
        | some p =>
          nplans := nplans + 1
          let ref := refTransform fwd N rs x
          -- a fresh output, and a reused output buffer holding stale data
          unless bitEq (exec p x) ref && bitEq (execInto p x (input N)) ref do
            IO.println s!"MISMATCH in-place N={N} fwd={fwd} rs={rs}"
            bad := bad + 1
  IO.println s!"{nplans} plans checked bit for bit against refTransform, {bad} failures"
  if bad > 0 then IO.Process.exit 1

/-- The executors timed. (Draft PR #1, branch `experiment/lean-vectorized-schedules`, also had an
out-of-place Stockham and a lane-batched split-format schedule; both were slower.) -/
def engines : List (String × (Plan → FloatArray → FloatArray → FloatArray)) :=
  [("ip", fun p x y => execInto p x y)]

def timeAll (kmax : Nat) : IO Unit := do
  IO.println "N best_engine best_rs native_ns reference_ns"
  for k in [1:kmax + 1] do
    let N := 2 ^ k
    let x := input N
    let mut best : Float := 1e30
    let mut bestRs : Array Nat := #[]
    let mut bestE := "ip"
    for l in sortedSeqs k do
      let rs := l.toArray
      let some p := Plan.make? true N rs | continue
      for (nm, e) in engines do
        let f := fun y => e p x y
        let it ← calibrate f (zeros (2 * N)) 1e7
        let t ← timeIt it 3 f (zeros (2 * N))
        if t < best then best := t; bestRs := rs; bestE := nm
    -- re-time the winner
    let some p := Plan.make? true N bestRs | continue
    let some (_, e) := engines.find? (·.1 == bestE) | continue
    let f := fun y => e p x y
    let it ← calibrate f (zeros (2 * N)) 5e7
    let t ← timeIt it 5 f (zeros (2 * N))
    let tref ← if k ≤ 12 then do
        let g := fun (_ : FloatArray) => refTransform true N bestRs x
        let it ← calibrate g x 5e7
        timeIt it 3 g x
      else pure 0.0
    IO.println s!"{N} {bestE} {bestRs} {t} {tref}"

/-- Time of each pass kind, in ns per point: `leaf R` and `dit R ns` on size `N`. -/
unsafe def passProfileU (N : Nat) : IO Unit := do
  let x := input N
  for R in [2, 4, 8, 16] do
    let some p := Plan.make? true R #[R] | continue
    let _ := p
    -- leaf of a plan [R, 2, 2, ...] of size N: offsets from the full plan
    let rest := (List.replicate (Nat.log2 (N / R)) 2).toArray
    let some q := Plan.make? true N (#[R] ++ rest) | continue
    let n := (N / R).toUSize
    let f := fun y => leafPassf R x q.ofs n n y
    let it ← calibrate f (zeros (2 * N)) 2e7
    let t ← timeIt it 3 f (zeros (2 * N))
    IO.println s!"leaf R={R} N={N}: {t / N.toFloat} ns/point"
  for R in [2, 4, 8, 16] do
    let mut ns := 1
    while ns * R ≤ N do
      let tw := passTwiddles (Trig.cosSin2PiTable N) true N R ns
      let nB := (N / (ns * R)).toUSize
      let f := fun y => ditPassf R tw ns.toUSize nB y
      let it ← calibrate f (own (zeros (2 * N))) 2e7
      let t ← timeIt it 3 f (own (zeros (2 * N)))
      IO.println s!"dit R={R} ns={ns} N={N}: {t / N.toFloat} ns/point"
      ns := ns * R

@[implemented_by passProfileU] opaque passProfile (N : Nat) : IO Unit

def cmpPlan (rs : Array Nat) : IO Unit := do
  let N := rs.toList.prod
  let x := input N
  let some p := Plan.make? true N rs | IO.println "not a plan"
  for (nm, e) in engines do
    let f := fun y => e p x y
    let it ← calibrate f (zeros (2 * N)) 2e7
    let t ← timeIt it 5 f (zeros (2 * N))
    IO.println s!"{nm} N={N} rs={rs}: {t} ns"

def main (args : List String) : IO Unit := do
  let kmax := (args.getD 1 "").toNat?.getD 18
  match args.headD "check" with
  | "time" => timeAll kmax
  | "passes" => passProfile (2 ^ kmax)
  | "plan" => cmpPlan ((args.drop 1).filterMap String.toNat?).toArray
  | _ => check kmax
