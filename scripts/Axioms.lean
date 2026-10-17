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
