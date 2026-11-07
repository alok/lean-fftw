import LeanFFTW.Gen.LeanEmit

/-! Writes the Lean backend's kernels: `lake env lean --run scripts/GenLeanKernels.lean` -/

def main (args : List String) : IO Unit := do
  let out := args.headD "LeanFFTW/Native/Kernels.lean"
  IO.FS.writeFile out LeanFFTW.Gen.emitLeanKernels
  IO.println s!"wrote {out}"
