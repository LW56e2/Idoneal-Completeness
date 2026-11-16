import Idoneal.Main

/-! Statements and axioms of the conditional theorems. Run from the repository root:
`lake env lean scripts/AxiomsConditional.lean` (after `lake build Idoneal`). -/

#check @Idoneal.idoneal_numbers_completeness_of_noRealZeros
#check @Idoneal.idoneal_numbers_completeness_of_zeroFree
#check @Idoneal.isIdoneal_iff_mem_known_of_noRealZeros
#check @Idoneal.isIdoneal_of_mem_known

#print axioms Idoneal.small_range
#print axioms Idoneal.high_omega
#print axioms Idoneal.analytic_bound
#print axioms Idoneal.isIdoneal_of_mem_known
#print axioms Idoneal.idoneal_numbers_completeness_of_noRealZeros
#print axioms Idoneal.idoneal_numbers_completeness_of_zeroFree
#print axioms Idoneal.idoneal_numbers_completeness_of_dirichlet_nonvanishing
#print axioms Idoneal.isIdoneal_iff_mem_known_of_noRealZeros
#print axioms Idoneal.isIdoneal_iff_mem_known_of_dirichlet_nonvanishing
