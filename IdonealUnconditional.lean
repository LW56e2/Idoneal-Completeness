import Idoneal.Main
import Transport.Nonvanishing

/-!
# Euler's list of idoneal numbers is complete (unconditional)

This file joins the two projects: `Idoneal` (this repository) and `quasi-riemann-improved`
(`RH.Transport.dirichlet_nonvanishing`: no zero of any Dirichlet L-function with
`Re s > 4374785349/5000000000`, apart from the pole). It needs both projects built in one
workspace; see `lakefile.toml` next to this file.
-/

/-- **Completeness of Euler's list of 65 idoneal numbers**
(the statement `Idoneal.idoneal_numbers_completeness` of `google-deepmind/formal-conjectures`). -/
theorem idoneal_numbers_completeness :
    ∀ n : ℕ, Idoneal.IsIdoneal n → n ∈ Idoneal.knownIdonealNumbers :=
  Idoneal.idoneal_numbers_completeness_of_dirichlet_nonvanishing
    RH.Transport.dirichlet_nonvanishing

/-- Euler's list is exactly the set of idoneal numbers. -/
theorem isIdoneal_iff_mem_knownIdonealNumbers (n : ℕ) :
    Idoneal.IsIdoneal n ↔ n ∈ Idoneal.knownIdonealNumbers :=
  Idoneal.isIdoneal_iff_mem_known_of_dirichlet_nonvanishing
    RH.Transport.dirichlet_nonvanishing n
