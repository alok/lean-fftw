import Lake
open Lake DSL

package «lean-fftw» where
  version := v!"0.1.0"
  description := "An FFTW-class FFT library implemented and verified in Lean 4."
  license := "MIT"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

require floatlib from git
  "https://github.com/lean-dojo/FloatLib" @ "1f5771b3e36a98f17fcac2c6d76aaa024b36aa37"

@[default_target]
lean_lib LeanFFTW where
  roots := #[`LeanFFTW]

/-- The executable engine (no Mathlib dependency), packaged as a static library for C. -/
lean_lib LeanFFTWExec where
  roots := #[`LeanFFTW.FFI]
  globs := #[.one `LeanFFTW.FFI, .submodules `LeanFFTW.Core]
