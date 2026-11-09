import LeanFFTW.Asm.Kernels

open LeanFFTW.Asm

/-- Write the assembly of the fast engine: `gen_asm OUT.s [PREFIX=foldLimit,sched …]`.
Each further argument sets the generator options of the functions whose name starts with
`PREFIX` (later arguments win); for experiments. -/
def main (args : List String) : IO UInt32 := do
  let out := args.getD 0 "lf_kernels.s"
  let rules := (args.drop 1).filterMap fun a =>
    match a.splitOn "=" with
    | [pre, v] =>
        match v.splitOn "," with
        | [f, s] => some (pre, ({ foldLimit := f.toNat!, sched := s.toNat! } : GenOpts))
        | _ => none
    | _ => none
  let opts (name : String) : GenOpts :=
    rules.foldl (fun o (pre, v) => if name.startsWith pre then v else o) {}
  match engineAsm opts with
  | .ok (s, checked, unchecked) =>
      IO.FS.writeFile out s
      IO.eprintln s!"vector blocks: {checked} checked against their specification, {unchecked} without one"
      return 0
  | .error e => IO.eprintln e; return 1
