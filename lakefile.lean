import Lake
open Lake DSL

package «lean-fftw» where
  version := v!"0.1.0"
  description := "An FFTW-class FFT library implemented and verified in Lean 4."
  license := "MIT"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]


require cslib from git
  "https://github.com/leanprover/cslib" @ "1ade21e1bd8d03a4ca9f6f632a15c032926054f7"

require floatlib from git
  "https://github.com/lean-dojo/FloatLib" @ "1f5771b3e36a98f17fcac2c6d76aaa024b36aa37"

-- Mathlib last, so that its versions of shared dependencies take precedence.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib LeanFFTW where
  roots := #[`LeanFFTW]

/-- The executable engine (no Mathlib dependency), packaged as a static library. -/
lean_lib LeanFFTWExec where
  roots := #[`LeanFFTW.FFI]
  globs := #[.one `LeanFFTW.FFI, .submodules `LeanFFTW.Core, .submodules `LeanFFTW.Gen,
    .submodules `LeanFFTW.Asm]

/-- The Lean-compiled backend: generated kernels over unboxed `FloatArray`. -/
lean_lib LeanFFTWNative where
  roots := #[`LeanFFTW.Native.Exec]
  globs := #[.submodules `LeanFFTW.Native]
  -- FMA instructions for `Float.fma`, no contraction of other operations;
  -- and enough runtime alias checks for clang to vectorize the loops over butterflies
  moreLeancArgs := #["-march=native", "-mprefer-vector-width=512", "-ffp-contract=off",
    "-mllvm", "-runtime-memory-check-threshold=8192",
    "-mllvm", "-vectorize-memory-check-threshold=8192"]

/-- Bit-exact check and timing of the Lean-compiled backend. -/
lean_exe native_bench where
  root := `NativeBench
  srcDir := "scripts"
  moreLeancArgs := #["-march=native", "-ffp-contract=off"]

/-- Writes the assembly of the fast engine (`gen_asm OUT.s`): the code generator, the register
allocator and the checker of the emitted code all run here, in Lean. -/
lean_exe gen_asm where
  root := `GenAsm
  srcDir := "scripts"

/-- Tests of the assembly engine. Links the assembled engine: build with `scripts/build.sh`. -/
lean_exe asm_test where
  root := `AsmTest
  srcDir := "scripts"
  moreLinkArgs := #[".lake/build/asm/lf_asm.o"]
