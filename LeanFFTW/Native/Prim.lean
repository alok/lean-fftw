/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/

/-!
# Unchecked array access for the Lean backend

The generated kernels of `LeanFFTW/Native` read and write `FloatArray`s without bounds
checks, and write without the copy-on-write check. This is the backend's unsafe boundary:
`LeanFFTW.Native.exec` is a safe function whose definition is the proved schedule
(`inplaceWith floatArith`), and these primitives are used only by its `implemented_by`
implementation, which sizes every array it indexes and makes its output array unshared
(`own`) before the first `wr`.

`wr` compiles to one C store. With no call left in a loop body, the C compiler can
vectorize the loops over butterflies.
-/

namespace LeanFFTW.Native

@[inline] unsafe def rd (a : @& FloatArray) (i : USize) : Float := a.uget i lcProof

/-- Store without bounds or sharing checks: `a` must be unshared and `i < a.size`. -/
@[extern c inline "(lean_float_array_cptr(#1)[#2] = #3, #1)"]
unsafe def wr (a : FloatArray) (i : USize) (v : Float) : FloatArray := a.uset i v lcProof

/-- `a`, unshared (copied if it is shared): one checked store of its first element. -/
@[inline] def own (a : FloatArray) : FloatArray :=
  if h : 0 < a.size then a.set 0 a[0] h else a

/-- A fresh `FloatArray` of size `n`, uninitialized (every element is written before it is
read). `never_extract` keeps the compiler from merging two allocations into one array. -/
@[never_extract, extern c inline "lean_alloc_sarray(sizeof(double), #1, #1)"]
unsafe def alloc (n : USize) : FloatArray := ⟨Array.replicate n.toNat 0.0⟩

/-- The constant with bits `b`, compiled to a C literal. Left to itself the compiler would
hoist `Float.ofBits b` into a lazily initialized global, read through a once-check at every
use, which also blocks vectorization. -/
@[never_extract, extern c inline "(((union { uint64_t u; double d; }){ .u = #1 }).d)"]
unsafe def cst (b : UInt64) : Float := Float.ofBits b

end LeanFFTW.Native
