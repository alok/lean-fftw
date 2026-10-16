import LeanFFTW.Gen.Stockham

/-! Writes the generated SIMD kernels of the fast engine: `lake env lean --run scripts/GenKernels.lean <out.c>` -/

def main (args : List String) : IO Unit := do
  let out := args.headD "csrc/lf_kernels_gen.c"
  IO.FS.writeFile out (LeanFFTW.Gen.emitKernels)
  IO.println s!"wrote {out}"
