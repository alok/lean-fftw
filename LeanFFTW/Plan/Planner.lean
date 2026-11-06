/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Core.Trig
import LeanFFTW.Gen.OpCount

/-!
# The planner, in Lean

The planner chooses, for a size `N`, the radix sequence and the schedule of the fast engine
that runs fastest on this machine, by measuring candidates, as FFTW's planner does. It is
Lean code compiled by Lean; the plans it builds and times are C objects of the fast
engine (`csrc/lf_fast.c`, running the kernels Lean printed).

## The unsafe boundary

C objects are passed to Lean as raw pointers (`USize`): a plan, the work arrays, nothing
else. The `extern` functions below are thin calls into `csrc/lf_lean.c`. Only this module
uses them, and it owns every pointer it creates: each plan it builds is destroyed except
the one it returns, and the arrays it allocates are freed before it returns. The rest of
the planner (enumeration, the cost model, the measurement policy, the search) is ordinary
Lean.
-/

namespace LeanFFTW.Planner

open LeanFFTW.Gen

/-! ## The C engine, seen from Lean -/

/-- Vector length of a radix sequence in a schedule (`0`: no generated kernels cover it). -/
@[extern "lfp_mode_vl"]
opaque modeVL (N : USize) (fwd : UInt8) (rs : @& FloatArray) (mode : UInt8) : UInt32

/-- Build a plan; `0` if unsupported or if the blocking `(T, Q)` is invalid. -/
@[extern "lfp_build"]
opaque buildRaw (N : USize) (fwd : UInt8) (rs : @& FloatArray) (mode : UInt8) (T : UInt32)
  (Q : USize) (base : @& FloatArray) : IO USize

/-- Execute a plan `reps` times on interleaved arrays `inp`, `out`. -/
@[extern "lfp_run"]
opaque run (p inp out reps : USize) : IO Unit

@[extern "lfp_destroy"]
opaque destroy (p : USize) : IO Unit

/-- A zeroed, 64-byte aligned array of `n` doubles. -/
@[extern "lfp_alloc"]
opaque alloc (n : USize) : IO USize

@[extern "lfp_free"]
opaque free (p : USize) : IO Unit

/-- Set `n` doubles to zero. -/
@[extern "lfp_zero"]
opaque zero (p n : USize) : IO Unit

/-! ## Candidates -/

/-- Schedules of the fast engine (`lf_fast.h`). -/
def modeStockham : Nat := 0
def modeFused : Nat := 1
def modeInplace : Nat := 2
def modeCFused : Nat := 3
def modeCTwo : Nat := 4
def nModes : Nat := 5
def maxPass : Nat := 24

/-- A candidate plan: radix sequence, schedule and (in-place schedule) cache blocking. -/
structure Cand where
  rs : Array Nat
  mode : Nat
  T : Nat := 0
  Q : Nat := 0
  /-- measured seconds per transform -/
  t : Float := 1e30
  deriving Inhabited

def radixArg (rs : Array Nat) : FloatArray := ⟨rs.map (·.toFloat)⟩

def fwdArg (fwd : Bool) : UInt8 := if fwd then 1 else 0

def vlOf (N : Nat) (fwd : Bool) (rs : Array Nat) (mode : Nat) : Nat :=
  (modeVL N.toUSize (fwdArg fwd) (radixArg rs) mode.toUInt8).toNat

/-! ## Enumeration: a first radix, then a monotone tail -/

def firsts2 : Array Nat := #[2, 4, 8, 16, 32]
def mids2 : Array Nat := #[32, 16, 8, 4, 2]
/-- radices of mixed-radix plans (`N` not a power of two) -/
def firstsM : Array Nat := #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 32]
def midsM : Array Nat := #[32, 16, 15, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2]

/-- Every schedule that covers `rs`. -/
def emitAll (N : Nat) (fwd : Bool) (rs : Array Nat) (acc : Array Cand) : Array Cand :=
  (List.range nModes).foldl (fun acc mode =>
    if vlOf N fwd rs mode != 0 then acc.push { rs, mode } else acc) acc

/-- Tails of radix sequences for the remaining size `M`. `dir = 0`: non-increasing radices
(`mids[i]`, `i ≥ lo`); `dir = 1`: non-decreasing and not constant (constant tails are
enumerated by `dir = 0`). -/
partial def tails (N : Nat) (fwd : Bool) (mids : Array Nat) (rs : Array Nat) (M lo dir : Nat)
    (first strict : Bool) (acc : Array Cand) : Array Cand :=
  if M == 1 then (if dir == 0 || strict then emitAll N fwd rs acc else acc)
  else if rs.size ≥ maxPass then acc
  else (List.range mids.size).foldl (fun acc i =>
    if (if dir == 0 then i < lo else i > lo) then acc
    else
      let m := mids[i]!
      if M % m == 0 then
        tails N fwd mids (rs.push m) (M / m) i dir false (strict || (!first && i != lo)) acc
      else acc) acc

/-- All candidate plans of size `N` (radix sequences × schedules). -/
def enumerate (N : Nat) (fwd : Bool) : Array Cand := Id.run do
  let pow2 := N &&& (N - 1) == 0
  let firsts := if pow2 then firsts2 else firstsM
  let mids := if pow2 then mids2 else midsM
  let mut acc : Array Cand := #[]
  for mode in [modeStockham, modeCFused] do
    if vlOf N fwd #[N] mode != 0 then acc := acc.push { rs := #[N], mode }
  for f in firsts do
    if N % f == 0 && N > f then
      acc := tails N fwd mids #[f] (N / f) 0 0 true false acc
      acc := tails N fwd mids #[f] (N / f) (mids.size - 1) 1 true false acc
  return acc

/-! ## Measurement -/

def seconds (t0 t1 : Nat) : Float := (t1 - t0).toFloat * 1e-9

/-- Minimum over `k` measurements of at least `tmin` seconds each (the repetition count is
doubled until one measurement lasts `tmin`). If the first measurement exceeds `cutoff`, it
is returned at once: the candidate has lost the race. -/
def timePlan (p inp out : USize) (k : Nat) (tmin : Float) (cutoff : Float := 1e30) : IO Float := do
  run p inp out 1
  let mut reps : Nat := 1
  repeat
    let t0 ← IO.monoNanosNow
    run p inp out reps.toUSize
    let t1 ← IO.monoNanosNow
    if seconds t0 t1 ≥ tmin || reps ≥ 2 ^ 24 then break
    reps := reps * 2
  let mut best : Float := 1e30
  for _ in [0:k] do
    let t0 ← IO.monoNanosNow
    run p inp out reps.toUSize
    let t1 ← IO.monoNanosNow
    let d := seconds t0 t1 / reps.toFloat
    if d < best then best := d
    if best > cutoff then break
  return best

/-- The base twiddle table `ω_N^m`, `m < N`, interleaved (as `fastBaseTableFFI`). -/
def baseTable (N : Nat) (fwd : Bool) : FloatArray := Id.run do
  let tab := Trig.cosSin2PiTable N
  let mut out := FloatArray.emptyWithCapacity (2 * N)
  for (c, s) in tab do
    out := (out.push c).push (if fwd then Trig.negZ s else s)
  return out

/-- Build the plan of a candidate (`0` if unsupported). -/
def build (N : Nat) (fwd : Bool) (base : FloatArray) (c : Cand) : IO USize :=
  buildRaw N.toUSize (fwdArg fwd) (radixArg c.rs) c.mode.toUInt8 c.T.toUInt32 c.Q.toUSize base

/-- Build, time and destroy. -/
def measure (N : Nat) (fwd : Bool) (base : FloatArray) (inp out : USize) (cutoff : Float)
    (c : Cand) : IO Cand := do
  let p ← build N fwd base c
  if p == 0 then return { c with t := 1e30 }
  let t ← timePlan p inp out 5 2e-4 cutoff
  destroy p
  return { c with t }

def byTime (a b : Cand) : Bool := a.t < b.t

/-! ## Operation counts of candidates (the proved cost model) -/

/-- Per-butterfly `(arithmetic operations, memory operations)` of every radix used by the
candidates, from the generated kernels (`bflyCost` with `Weights.arith` and `Weights.mem`). -/
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

/-- Optional log of every measured candidate (`LF_PLAN_LOG=<file>`), for fitting and
checking the cost model. -/
def logCands (N : Nat) (fwd : Bool) (stage : String) (cs : Array Cand) : IO Unit := do
  let some path ← IO.getEnv "LF_PLAN_LOG" | return
  let h ← IO.FS.Handle.mk path .append
  let tab := bflyTable fwd cs
  for c in cs do
    let (a, m) := counts tab N c
    h.putStrLn s!"{N} {if fwd then 1 else 0} {stage} {c.mode} {c.T} {c.Q} {c.t * 1e9} {vlOf N fwd c.rs c.mode} {a} {m} {c.rs.toList}"

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

/-- Vector lanes of a candidate: `vlOf`, except that mixed-radix Stockham plans (`vlOf = 1`
with several passes) choose 8 or 4 per pass; they count as 8. -/
def lanes (N : Nat) (fwd : Bool) (c : Cand) : Nat :=
  let vl := vlOf N fwd c.rs c.mode
  if c.mode == modeStockham && c.rs.size > 1 && vl ≤ 1 then 8 else max vl 1

/-- Operations per vector lane: the proved counts `stockhamCost .arith + stockhamCost .mem`
over the lanes. The race times candidates in this order. -/
def opScore (tab : Std.HashMap (Nat × Bool) (Nat × Nat)) (N : Nat) (fwd : Bool) (c : Cand) : Float :=
  let (a, m) := counts tab N c
  (a + m).toFloat / (lanes N fwd c).toFloat

/-- The race only times candidates within `pruneCut` of the fewest operations per lane among
candidates of the same schedule. On every size of the benchmark sets (power-of-two and
benchFFT's), the fastest plan was within 1.4 (`tools/costmodel.py`, `docs/ITERATIONS.md`). -/
def pruneCut : Float := 1.5

/-- Candidates the race keeps, in the order it times them. -/
def raceOrder (N : Nat) (fwd : Bool) (cs : Array Cand) : Array Cand := Id.run do
  let tab := bflyTable fwd cs
  let scored := cs.map fun c => (c, opScore tab N fwd c)
  let mut best : Std.HashMap Nat Float := {}
  for (c, x) in scored do
    if x < best.getD c.mode 1e300 then best := best.insert c.mode x
  let kept := scored.filter fun (c, x) => x ≤ pruneCut * best.getD c.mode 1e300
  return (kept.qsort fun a b => a.2 < b.2).map (·.1)

/-- Time candidates in order; under the race, a candidate slower than `raceCut` times the
best so far is dropped after one measurement. -/
def measureAll (N : Nat) (fwd : Bool) (base : FloatArray) (inp out : USize) (effort : Effort)
    (cs : Array Cand) (best0 : Float := 1e30) : IO (Array Cand) := do
  let mut best := best0
  let mut res := #[]
  for c in cs do
    let cutoff := if effort == .race then raceCut * best else 1e30
    let c' ← measure N fwd base inp out cutoff c
    if c'.t < best then best := c'.t
    res := res.push c'
  return res

/-- The measuring planner: time the candidates, search cache blockings of the best
in-place plans for large sizes, then re-time the leaders interleaved and return the
fastest, built (with the arrays it was timed on). -/
def planMeasure (N : Nat) (fwd : Bool) (inp out : USize) (effort : Effort) :
    IO (USize × Cand) := do
  let base := baseTable N fwd
  zero inp (2 * N).toUSize
  -- 1: every radix sequence and schedule (the race: in order of operation counts)
  let cands := enumerate N fwd
  let cands := if effort == .race then raceOrder N fwd cands else cands
  let mut cs ← measureAll N fwd base inp out effort cands
  logCands N fwd "all" cs
  cs := cs.qsort byTime
  -- 2: cache blocking of the best in-place plans of large sizes
  if N ≥ 2 ^ 15 then
    let lead := cs.extract 0 8
    let mut blocked : Array Cand := #[]
    for c in lead do
      if c.mode != modeInplace then continue
      let s := c.rs.size
      for T in [(if s ≥ 4 then s - 3 else 1):s] do
        for Q in [0, 32, 128] do
          blocked := blocked.push { c with T, Q }
    let bs ← measureAll N fwd base inp out effort blocked (cs[0]?.map (·.t) |>.getD 1e30)
    cs := (cs ++ bs.filter (·.t < 1e30)).qsort byTime
  -- 3: re-time the leaders, interleaved, to reduce the effect of noise
  let top := cs.extract 0 4
  let ps ← top.mapM (build N fwd base)
  let mut ts : Array Float := top.map fun _ => 1e30
  for _ in [0:3] do
    for i in [0:top.size] do
      let p := ps[i]!
      if p != 0 then
        let t ← timePlan p inp out 3 5e-4
        if t < ts[i]! then ts := ts.set! i t
  let mut b := 0
  for i in [1:top.size] do
    if ts[i]! < ts[b]! then b := i
  for i in [0:top.size] do
    if i != b then destroy ps[i]!
  if top.size == 0 then return (0, default)
  return (ps[b]!, { top[b]! with t := ts[b]! })

/-! ## C entry points -/

/-- Plan a transform of size `N` on the caller's arrays (`inp == out`: in place); their
contents are overwritten. Returns the plan (a C `lf_plan *`), or `0`. -/
@[export lfftw_plan_measure]
def planMeasureFFI (N : USize) (fwd : UInt8) (inp out : USize) : IO USize := do
  let (p, _) ← planMeasure N.toNat (fwd != 0) inp out (← effortFromEnv)
  return p

/-- The candidates of size `N`, flattened: for each, `s, mode, R₀, …, R_{s-1}`. -/
@[export lfftw_enumerate]
def enumerateFFI (N : USize) (fwd : UInt8) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity 64
  for c in enumerate N.toNat (fwd != 0) do
    out := (out.push c.rs.size.toFloat).push c.mode.toFloat
    for r in c.rs do
      out := out.push r.toFloat
  return out

end LeanFFTW.Planner
