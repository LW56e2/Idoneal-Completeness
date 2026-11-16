import Idoneal.Elementary
import Idoneal.Analytic
import Idoneal.Threshold
import Idoneal.Compute
import Idoneal.Converse

/-!
# Completeness of Euler's list of idoneal numbers (blueprint §1 (M))

Main results:

* `idoneal_numbers_completeness_of_noRealZeros`: the statement of
  `google-deepmind/formal-conjectures` (`Idoneal.idoneal_numbers_completeness`), under
  `NoRealZeros`.
* `idoneal_numbers_completeness_of_zeroFree`: the same from a zero-free half-plane
  `Re s > T` with `T < 19/20` for all Dirichlet L-functions, in the form of the theorem
  `dirichlet_nonvanishing` of `quasi-riemann-improved`.
-/

namespace Idoneal

theorem le_of_mem_knownIdonealNumbers : ∀ m ∈ knownIdonealNumbers, m ≤ 1848 := by
  intro m hm
  simp only [knownIdonealNumbers, Finset.mem_insert, Finset.mem_singleton] at hm
  omega

/-- Every positive integer outside the list is of the form `ab + bc + ca`, `0 < a < b < c`. -/
theorem hasTriple_of_not_known (h : NoRealZeros) :
    ∀ n : ℕ, 0 < n → n ∉ knownIdonealNumbers → HasTriple n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hnk
    by_cases hsmall : n < 4000000
    · exact small_range hn0 hsmall hnk
    · rw [not_lt] at hsmall
      by_cases hsf : Squarefree n
      · by_contra hno
        have hns : ¬ HasStrictForm n := fun hs => hno ((hasTriple_iff_hasStrictForm n).mpr hs)
        have hA := analytic_bound h (by omega : 1000000 ≤ n) hns
        exact hno (high_omega hsf hsmall (threshold hsmall hsf hA))
      · obtain ⟨p, hp, hdvd⟩ : ∃ p, p.Prime ∧ p * p ∣ n := by
          by_contra hcon
          exact hsf (Nat.squarefree_iff_prime_squarefree.mpr fun p hp hd => hcon ⟨p, hp, hd⟩)
        obtain ⟨m, rfl⟩ := hdvd
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm; simp at hn0
          · exact hm
        have hp2 : 2 ≤ p := hp.two_le
        by_cases hmk : m ∈ knownIdonealNumbers
        · have hm : m ≤ 1848 := le_of_mem_knownIdonealNumbers m hmk
          have hp47 : 47 ≤ p := by
            by_contra hlt
            rw [not_le] at hlt
            have h1 : p * p ≤ 46 * 46 := Nat.mul_le_mul (by omega) (by omega)
            have h2 : p * p * m ≤ 46 * 46 * 1848 := Nat.mul_le_mul h1 hm
            omega
          have hs := hasStrictForm_prime_sq_mul hp hp47 hm0 hm
          rw [← hasTriple_iff_hasStrictForm] at hs
          rwa [pow_two] at hs
        · have hlt : m < p * p * m := by
            have h1 : 4 ≤ p * p := Nat.mul_le_mul hp2 hp2
            nlinarith
          have ht := (ih m hlt hm0 hmk).sq_mul hp.pos
          rwa [pow_two] at ht

/-- **Completeness of Euler's list of 65 idoneal numbers**, assuming that no Dirichlet
L-function of a nontrivial character has a real zero in `[19/20, 1)`. -/
theorem idoneal_numbers_completeness_of_noRealZeros (h : NoRealZeros) :
    ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers := by
  intro n hn
  by_contra hnk
  exact hn.2 (hasTriple_of_not_known h n hn.1 hnk)

/-- A zero-free half-plane `Re s > T` with `T < 19/20` gives `NoRealZeros`. -/
theorem noRealZeros_of_zeroFree {T : ℝ} (hT : T < 19 / 20)
    (hz : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), T < s.re →
      ¬(χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) : NoRealZeros := by
  intro q _ χ hχ σ hσ _
  refine hz χ (σ : ℂ) ?_ ?_
  · rw [Complex.ofReal_re]; linarith
  · exact fun hc => hχ hc.1

/-- **Completeness of Euler's list of 65 idoneal numbers** from a zero-free half-plane
`Re s > T`, `T < 19/20`, for all Dirichlet L-functions. -/
theorem idoneal_numbers_completeness_of_zeroFree {T : ℝ} (hT : T < 19 / 20)
    (hz : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), T < s.re →
      ¬(χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) :
    ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers :=
  idoneal_numbers_completeness_of_noRealZeros (noRealZeros_of_zeroFree hT hz)

/-- The same with the explicit half-plane of `quasi-riemann-improved`. The hypothesis is, word
for word, the statement of the theorem `RH.Transport.dirichlet_nonvanishing` of that project
(`Transport/Nonvanishing.lean`), so in a workspace containing both projects the conclusion is
`idoneal_numbers_completeness_of_dirichlet_nonvanishing RH.Transport.dirichlet_nonvanishing`. -/
theorem idoneal_numbers_completeness_of_dirichlet_nonvanishing
    (dirichlet_nonvanishing : ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) (s : ℂ)
      (_hs : (4374785349/5000000000 : ℝ)<s.re)
      (_hpole : ¬(χ=1 ∧ s=1)), χ.LFunction s≠0) :
    ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers :=
  idoneal_numbers_completeness_of_zeroFree (by norm_num) dirichlet_nonvanishing

/-- Under `NoRealZeros`, Euler's list is exactly the set of idoneal numbers. (The direction
`←` is unconditional: `isIdoneal_of_mem_known`.) -/
theorem isIdoneal_iff_mem_known_of_noRealZeros (h : NoRealZeros) (n : ℕ) :
    IsIdoneal n ↔ n ∈ knownIdonealNumbers :=
  ⟨idoneal_numbers_completeness_of_noRealZeros h n, isIdoneal_of_mem_known⟩

/-- Euler's list is exactly the set of idoneal numbers, from the zero-free half-plane of
`quasi-riemann-improved` (hypothesis as in
`idoneal_numbers_completeness_of_dirichlet_nonvanishing`). -/
theorem isIdoneal_iff_mem_known_of_dirichlet_nonvanishing
    (dirichlet_nonvanishing : ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) (s : ℂ)
      (_hs : (4374785349/5000000000 : ℝ)<s.re)
      (_hpole : ¬(χ=1 ∧ s=1)), χ.LFunction s≠0) (n : ℕ) :
    IsIdoneal n ↔ n ∈ knownIdonealNumbers :=
  ⟨idoneal_numbers_completeness_of_dirichlet_nonvanishing dirichlet_nonvanishing n,
    isIdoneal_of_mem_known⟩

end Idoneal
