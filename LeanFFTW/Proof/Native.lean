/-
Copyright (c) 2026 Lean FFTW contributors. Released under MIT license.
-/
import LeanFFTW.Native.Exec
import LeanFFTW.Proof.InPlace

/-!
# The Lean-compiled backend computes the reference transform

`LeanFFTW.Native.exec` is defined as the in-place schedule of its plan. By
`inplaceWith_eq_stockhamWith` it equals the binary64 reference `refTransform` (the Stockham
schedule) bit for bit, for every valid plan. Its compiled implementation (`execU`, generated
straight-line kernels) is the trusted part, checked against the same reference by
`scripts/NativeBench.lean`.
-/

namespace LeanFFTW.Native

open LeanFFTW.Gen

theorem exec_eq_refTransform (p : Plan) (x : FloatArray) :
    exec p x = refTransform p.fwd p.N p.rs x := by
  have hv := p.valid
  simp only [validPlan, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true]
    at hv
  obtain ⟨⟨hne, hall⟩, hN⟩ := hv
  have hpos : ∀ r ∈ p.rs, 0 < r := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
    have := hall i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  show (⟨inplaceWith floatArith p.fwd p.N p.rs (refTw p.fwd p.N p.rs) x.data⟩ : FloatArray) = _
  rw [inplaceWith_eq_stockhamWith floatArith p.fwd p.rs hne hpos p.N hN.symm]
  rfl

theorem execInto_eq_refTransform (p : Plan) (x y : FloatArray) :
    execInto p x y = refTransform p.fwd p.N p.rs x :=
  exec_eq_refTransform p x

end LeanFFTW.Native
