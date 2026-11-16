import IdonealUnconditional

/-! Statements and axioms of the unconditional theorems. Run from the repository root:
`lake env lean scripts/AxiomsUnconditional.lean` (after `lake build`). -/

#check @idoneal_numbers_completeness
#check @isIdoneal_iff_mem_knownIdonealNumbers

#print axioms idoneal_numbers_completeness
#print axioms isIdoneal_iff_mem_knownIdonealNumbers
#print axioms RH.Transport.dirichlet_nonvanishing
