/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Asm.Plan
import LeanFFTW.Gen.OpCount

/-!
# The planner of the assembly engine

For a size `N` the planner chooses the radix sequence and the schedule that run fastest on
this machine, by measuring candidates, as FFTW's planner does. Everything here is Lean: the
candidates are plans built by `LeanFFTW/Asm/Plan.lean` (records in a `FloatArray`), run by
the generated assembly. A plan is an ordinary Lean value; plans that lose are freed by
reference counting.

The only raw addresses are those of the caller's arrays, which the planner times on (as
FFTW does) and which it overwrites.
-/

namespace LeanFFTW.Asm.Planner

open LeanFFTW LeanFFTW.Gen

/-- A candidate plan: radix sequence, schedule and (in-place schedule) cache blocking. -/
structure Cand where
  rs : Array Nat
  mode : Mode
  T : Nat := 0
  Q : Nat := 0
  /-- the loops over groups of blocks and over chunks of columns run on the thread pool -/
  par : Bool := false
  /-- prefetch variant of the first pass (`leafPrefetch`) -/
  pf : Nat := 0
  /-- measured seconds per transform -/
  t : Float := 1e30
  deriving Inhabited

/-! ## Enumeration: a first radix, then a monotone tail -/

def firsts : Array Nat := #[2, 4, 8, 16, 32]
def mids : Array Nat := #[32, 16, 8, 4, 2]
/-- radices of the plans of sizes that are not powers of two -/
def firstsM : Array Nat :=
  #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16] ++
    (bstk0Radices.filter fun R => !stkRadices.contains R).toArray
def midsM : Array Nat := #[16, 15, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2]

def isPow2 (N : Nat) : Bool := N &&& (N - 1) == 0
def maxPass : Nat := 24

/-- Schedules that cover a radix sequence. -/
def modesOf (N : Nat) (rs : Array Nat) : List Mode :=
  let two (set : List (Nat × Nat × Nat)) : Bool :=
    rs.size == 2 && [4, 2].any fun vlc => set.contains (rs[0]!, rs[1]!, vlc)
  (if rs == #[N] && csmallSizes.contains N then [.csmall] else []) ++
  (if two cfusedSet then [.cfused] else []) ++
  (if two ctwoSet then [.ctwo] else []) ++
  (if rs.size ≥ 2 && leafRadices.contains rs[0]! && rs.all ditRadices.contains &&
      N / rs[0]! ≥ 8 then [.inplace] else []) ++
  (if !isPow2 N && rs.all stkRadices.contains then [.stockham] else []) ++
  (if !isPow2 N && rs.size ≥ 2 && bstk0Radices.contains rs[0]! && N / rs[0]! ≥ 8 &&
      (rs.extract 1 rs.size).all stkRadices.contains then [.blocked] else [])

def emitAll (N : Nat) (rs : Array Nat) (acc : Array Cand) : Array Cand :=
  (modesOf N rs).foldl (fun acc mode => acc.push { rs, mode }) acc

/-- Tails of radix sequences for the remaining size `M`. `dir = 0`: non-increasing radices
(`mids[i]`, `i ≥ lo`); `dir = 1`: non-decreasing and not constant (constant tails are
enumerated by `dir = 0`). -/
partial def tails (mids : Array Nat) (N : Nat) (rs : Array Nat) (M lo dir : Nat)
    (first strict : Bool) (acc : Array Cand) : Array Cand :=
  if M == 1 then (if dir == 0 || strict then emitAll N rs acc else acc)
  else if rs.size ≥ maxPass then acc
  else (List.range mids.size).foldl (fun acc i =>
    if (if dir == 0 then i < lo else i > lo) then acc
    else
      let m := mids[i]!
      if M % m == 0 then
        tails mids N (rs.push m) (M / m) i dir false (strict || (!first && i != lo)) acc
      else acc) acc

/-- All candidate plans of `N` (radix sequences × schedules). -/
def enumerate (N : Nat) : Array Cand := Id.run do
  let (fs, ms) := if isPow2 N then (firsts, mids) else (firstsM, midsM)
  let mut acc : Array Cand := emitAll N #[N] #[]
  for f in fs do
    if N % f == 0 && N > f then
      acc := tails ms N #[f] (N / f) 0 0 true false acc
      acc := tails ms N #[f] (N / f) (ms.size - 1) 1 true false acc
  -- two-pass kernels whose radices are not all among the above
  for (a, b, _) in cfusedSet ++ ctwoSet do
    if a * b == N && !(acc.any fun c => c.rs == #[a, b]) then acc := emitAll N #[a, b] acc
  return acc

/-! ## Measurement -/

def seconds (t0 t1 : Nat) : Float := (t1 - t0).toFloat * 1e-9

/-- Minimum over `k` measurements of at least `tmin` seconds each (the repetition count is
doubled until one measurement lasts `tmin`). If the first measurement exceeds `cutoff`, it
is returned at once: the candidate has lost the race. -/
def timePlan (p : Plan) (inp out : USize) (k : Nat) (tmin : Float) (cutoff : Float := 1e30) :
    IO Float := do
  p.run inp out 1
  let mut reps : Nat := 1
  repeat
    let t0 ← IO.monoNanosNow
    p.run inp out reps.toUSize
    let t1 ← IO.monoNanosNow
    if seconds t0 t1 ≥ tmin || reps ≥ 2 ^ 24 then break
    reps := reps * 2
  let mut best : Float := 1e30
  for _ in [0:k] do
    let t0 ← IO.monoNanosNow
    p.run inp out reps.toUSize
    let t1 ← IO.monoNanosNow
    let d := seconds t0 t1 / reps.toFloat
    if d < best then best := d
    if best > cutoff then break
  return best

/-- Build the plan of a candidate. -/
def build (N : Nat) (fwd inplace : Bool) (base : FloatArray) (c : Cand) : IO (Option Plan) := do
  let some src := mkPlan N fwd c.rs c.mode c.T c.Q inplace base c.par c.pf | return none
  return some (← src.build inplace)

/-- Build and time. -/
def measure (N : Nat) (fwd inplace : Bool) (base : FloatArray) (inp out : USize) (cutoff : Float)
    (c : Cand) : IO Cand := do
  let some p ← build N fwd inplace base c | return { c with t := 1e30 }
  let t ← timePlan p inp out 5 2e-4 cutoff
  return { c with t }

def byTime (a b : Cand) : Bool := a.t < b.t

/-! ## Operation counts of candidates -/

/-- Per-butterfly `(arithmetic operations, memory operations)` of every radix used by the
candidates (`bflyCost` with `Weights.arith` and `Weights.mem`). -/
def bflyTable (fwd : Bool) (cs : Array Cand) : Std.HashMap (Nat × Bool) (Nat × Nat) := Id.run do
  let mut tab : Std.HashMap (Nat × Bool) (Nat × Nat) := {}
  for c in cs do
    for t in [0:c.rs.size] do
      let key := (c.rs[t]!, decide (t ≥ 1))
      if !tab.contains key then
        let k := butterflyK fwd key.1 key.2
        tab := tab.insert key (bflyCost .arith k key.1 key.2, bflyCost .mem k key.1 key.2)
  return tab

/-- `(stockhamCost .arith, stockhamCost .mem)` of a candidate (`stockhamCost_eq_by`). -/
def counts (tab : Std.HashMap (Nat × Bool) (Nat × Nat)) (N : Nat) (c : Cand) : Nat × Nat :=
  (stockhamCostBy (fun R tw => (tab.getD (R, tw) (0, 0)).1) N c.rs,
   stockhamCostBy (fun R tw => (tab.getD (R, tw) (0, 0)).2) N c.rs)

def modeTag : Mode → String
  | .csmall => "csmall" | .cfused => "cfused" | .ctwo => "ctwo" | .inplace => "inplace"
  | .stockham => "stockham"
  | .blocked => "blocked"

/-- Optional log of every measured candidate (`LF_PLAN_LOG=<file>`). -/
def logCands (N : Nat) (fwd : Bool) (stage : String) (cs : Array Cand) : IO Unit := do
  let some path ← IO.getEnv "LF_PLAN_LOG" | return
  let h ← IO.FS.Handle.mk path .append
  let tab := bflyTable fwd cs
  for c in cs do
    let (a, m) := counts tab N c
    h.putStrLn s!"{N} {if fwd then 1 else 0} {stage}{if c.par then "-par" else ""} {modeTag c.mode} {c.T} {c.Q} {c.t * 1e9} {a} {m} {c.rs.toList}"

/-- How hard the planner searches. -/
inductive Effort where
  /-- time every candidate fully (5 measurements each) -/
  | exhaustive
  /-- race: candidates are timed in order of their operation counts, and one whose first
  measurement is `raceCut` times slower than the best so far is dropped at once -/
  | race
  deriving BEq, Inhabited

def raceCut : Float := 1.3

/-- `LF_PLANNER=exhaustive` selects the exhaustive search; the default is the race. -/
def effortFromEnv : IO Effort := do
  return if (← IO.getEnv "LF_PLANNER") == some "exhaustive" then .exhaustive else .race

/-- Operations of a candidate (`stockhamCost .arith + stockhamCost .mem`). The race times
candidates in this order. -/
def opScore (tab : Std.HashMap (Nat × Bool) (Nat × Nat)) (N : Nat) (c : Cand) : Float :=
  let (a, m) := counts tab N c
  (a + m).toFloat

/-- The race only times candidates within `pruneCut` of the fewest operations among
candidates of the same schedule. -/
def pruneCut : Float := 1.5

/-- Candidates the race keeps, in the order it times them. -/
def raceOrder (N : Nat) (fwd : Bool) (cs : Array Cand) : Array Cand := Id.run do
  let tab := bflyTable fwd cs
  let scored := cs.map fun c => (c, opScore tab N c)
  let key (c : Cand) : Nat := match c.mode with
    | .csmall => 0 | .cfused => 1 | .ctwo => 2 | .inplace => 3 | .stockham => 4 | .blocked => 4
  let mut best : Std.HashMap Nat Float := {}
  for (c, x) in scored do
    if x < best.getD (key c) 1e300 then best := best.insert (key c) x
  let kept := scored.filter fun (c, x) => x ≤ pruneCut * best.getD (key c) 1e300
  return (kept.qsort fun a b => a.2 < b.2).map (·.1)

/-- Time candidates in order; under the race, a candidate slower than `raceCut` times the
best so far is dropped after one measurement. -/
def measureAll (N : Nat) (fwd inplace : Bool) (base : FloatArray) (inp out : USize)
    (effort : Effort) (cs : Array Cand) (best0 : Float := 1e30) : IO (Array Cand) := do
  let mut best := best0
  let mut res := #[]
  for c in cs do
    let cutoff := if effort == .race then raceCut * best else 1e30
    let c' ← measure N fwd inplace base inp out cutoff c
    if c'.t < best then best := c'.t
    res := res.push c'
  return res

/-- The measuring planner: time the candidates, search cache blockings of the best
in-place plans for large sizes, then re-time the leaders interleaved and return the
fastest. `inp == out` plans the in-place transform. The arrays (`2N` doubles each) are
overwritten. -/
def planMeasure (N : Nat) (fwd : Bool) (inp out : USize) (effort : Effort) :
    IO (Option (Plan × Cand)) := do
  let inplace := inp == out
  let base := baseTable N fwd
  zeroRaw inp (2 * N).toUSize
  -- 1: every radix sequence and schedule (the race: in order of operation counts)
  let cands := enumerate N
  let cands := if effort == .race then raceOrder N fwd cands else cands
  let mut cs ← measureAll N fwd inplace base inp out effort cands
  logCands N fwd "all" cs
  cs := (cs.filter (·.t < 1e30)).qsort byTime
  -- 2: cache blocking of the best in-place plans of large sizes
  if N ≥ 2 ^ 15 then
    let lead := cs.extract 0 8
    let mut blocked : Array Cand := #[]
    for c in lead do
      if c.mode != .inplace then continue
      let s := c.rs.size
      for T in [(if s ≥ 4 then s - 3 else 1):s] do
        -- chunks of whole pages (256 columns) stay within a fraction of the cache sets
        for Q in [0, 32, 128, 256, 512] do
          blocked := blocked.push { c with T, Q }
    let bs ← measureAll N fwd inplace base inp out effort blocked (cs[0]?.map (·.t) |>.getD 1e30)
    logCands N fwd "blocked" bs
    cs := (cs ++ bs.filter (·.t < 1e30)).qsort byTime
    -- 2a: the leaders again, prefetching the outputs of the first pass
    let pcs := (cs.filter (·.mode == .inplace)).extract 0 8 |>.map ({ · with pf := 2 })
    let ps ← measureAll N fwd inplace base inp out effort pcs (cs[0]?.map (·.t) |>.getD 1e30)
    logCands N fwd "prefetch" ps
    cs := (cs ++ ps.filter (·.t < 1e30)).qsort byTime
  -- 2b: with a thread pool, the same plans with their loops shared among the threads
  let threads ← Pool.threads
  if threads > 1 && N ≥ 2 ^ 9 then
    let lead := (cs.filter (·.mode == .inplace)).extract 0 6
    let mut pc : Array Cand := #[]
    for c in lead do
      let s := c.rs.size
      for T in [1:s] do
        let nsT := passNs c.rs T
        for Q in [32, 128, 512, nsT / threads, nsT / (4 * threads)] do
          if Q ≥ 8 && Q % 8 == 0 && nsT % Q == 0 && nsT / Q ≥ threads && N / nsT ≥ 8 * threads &&
              !(pc.any fun d => d.rs == c.rs && d.T == T && d.Q == Q) then
            pc := pc.push { c with T, Q, par := true }
    let bs ← measureAll N fwd inplace base inp out effort pc (cs[0]?.map (·.t) |>.getD 1e30)
    logCands N fwd "threads" bs
    cs := (cs ++ bs.filter (·.t < 1e30)).qsort byTime
  -- 3: re-time the leaders, interleaved, to reduce the effect of noise
  let top := cs.extract 0 4
  let mut ps : Array Plan := #[]
  let mut keep : Array Cand := #[]
  for c in top do
    if let some p ← build N fwd inplace base c then
      ps := ps.push p; keep := keep.push c
  if ps.size == 0 then return none
  let mut ts : Array Float := ps.map fun _ => 1e30
  for _ in [0:3] do
    for i in [0:ps.size] do
      let t ← timePlan ps[i]! inp out 3 5e-4
      if t < ts[i]! then ts := ts.set! i t
  let mut b := 0
  for i in [1:ps.size] do
    if ts[i]! < ts[b]! then b := i
  return some (ps[b]!, { keep[b]! with t := ts[b]! })

/-! ## C entry points -/

/-- Plan a transform of size `N` on the caller's arrays (`inp == out`: in place); their
contents are overwritten. Returns the plan's memory (run it with
`lfa_call(data address, in, out)`), or an empty array when the engine does not cover `N` (a prime factor above 13). -/
@[export lfa_plan_measure]
def planMeasureFFI (N : USize) (fwd : UInt8) (inp out : USize) : IO FloatArray := do
  let n := N.toNat
  if n < 2 then return FloatArray.empty
  match ← planMeasure n (fwd != 0) inp out (← effortFromEnv) with
  | some (p, c) =>
      if (← IO.getEnv "LF_PLAN_SHOW").isSome then
        IO.eprintln s!"lfa plan N={n} {modeTag c.mode} {c.rs.toList} T={c.T} Q={c.Q} pf={c.pf}{if c.par then " threads" else ""} {c.t * 1e9} ns"
      return p.mem
  | none => return FloatArray.empty

/-- Run plans on `n` threads (plans made afterwards use them). -/
@[export lfa_set_threads]
def setThreadsFFI (n : USize) : IO Unit := Pool.start n.toNat

end LeanFFTW.Asm.Planner
