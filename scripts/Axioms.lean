import LeanFFTW

/-! Axiom audit: every main theorem must depend only on `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms LeanFFTW.dftSum_true_eq_dft
#print axioms LeanFFTW.dftSum_false_eq_invDft
#print axioms LeanFFTW.dftSum_ct
#print axioms LeanFFTW.exec_mkPlan_exact
#print axioms LeanFFTW.exec_mkPlan_exact_eq_dft
#print axioms LeanFFTW.Gen.cse_correct
#print axioms LeanFFTW.Gen.exec_sym
#print axioms LeanFFTW.Gen.butterflyK_correct
#print axioms LeanFFTW.Gen.stockInv_pass
#print axioms LeanFFTW.Gen.stockhamWith_exact
#print axioms LeanFFTW.Gen.Kernel.eval_error
#print axioms LeanFFTW.Gen.Kernel.eval_error_depth
#print axioms LeanFFTW.Gen.stockhamWith_err
#print axioms LeanFFTW.Gen.stockhamWith_error_dft
#print axioms LeanFFTW.Gen.stockhamWith_errArith_le_depth
#print axioms LeanFFTW.Gen.toReal_ofModel_fma_toModel_eq_roundAt
#print axioms LeanFFTW.Gen.floatArith_stdModel
#print axioms LeanFFTW.Gen.Kernel.eval_float_error
#print axioms LeanFFTW.Gen.Kernel.eval_float_error_depth
#print axioms LeanFFTW.Gen.stockhamWith_float_error_dft
#print axioms LeanFFTW.Gen.refTransform_error
#print axioms LeanFFTW.Gen.refTransform_error_depth
#print axioms LeanFFTW.execFloat_eq_fast
#print axioms LeanFFTW.Fast.execArr_eq
#print axioms LeanFFTW.exec_congr
#print axioms LeanFFTW.Gen.ev_contract
#print axioms LeanFFTW.Gen.evC_rotQ
