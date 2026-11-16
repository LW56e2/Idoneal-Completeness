import Idoneal.Character

/-!
# Bridge to Mathlib's `DirichletCharacter.LFunction` (blueprint §1 (LB))

Statements below are the fixed interface. Replace each `sorry`; add private lemmas freely.
Use only the *statements* of `Idoneal/Character.lean` (in particular `chi_natCast`, `chi_ne_one`,
`abs_sum_chiZ_le`).
-/

namespace Idoneal

/-- The real number `L(σ, chi n)`. -/
noncomputable def Lreal (n : ℕ) [NeZero n] (σ : ℝ) : ℝ :=
  (DirichletCharacter.LFunction (chi n) (σ : ℂ)).re

namespace LBridgeAux

open Filter Topology Finset MeasureTheory Asymptotics

/-- Complex coefficients. -/
noncomputable def aC (n m : ℕ) : ℂ := ((chiZ n m : ℤ) : ℂ)

lemma chiZ_zero' (n : ℕ) : chiZ n 0 = 0 := by simp [chiZ]

lemma chiZ_one' (n : ℕ) : chiZ n 1 = 1 := by simp [chiZ, jacobiSym.one_right]

lemma aC_zero (n : ℕ) : aC n 0 = 0 := by simp [aC, chiZ_zero']

lemma abs_chiZ_le (n m : ℕ) : |(chiZ n m : ℝ)| ≤ 1 := by
  rcases chiZ_trichotomy n m with h | h | h <;> simp [h]

/-- The partial-sum function `S(t)`. -/
noncomputable def Sfun (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Icc 1 ⌊t⌋₊, aC n k

lemma norm_sum_aC_le (n : ℕ) [NeZero n] (m : ℕ) : ‖∑ k ∈ Icc 1 m, aC n k‖ ≤ n := by
  have h := abs_sum_chiZ_le (Nat.pos_of_ne_zero (NeZero.ne n)) m
  have : ∑ k ∈ Icc 1 m, aC n k = (((∑ k ∈ Icc 1 m, chiZ n k : ℤ) : ℝ) : ℂ) := by
    simp [aC]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast h

lemma norm_Sfun_le (n : ℕ) [NeZero n] (t : ℝ) : ‖Sfun n t‖ ≤ n := norm_sum_aC_le n _

lemma Sfun_eq_zero {n : ℕ} {t : ℝ} (ht : t < 1) : Sfun n t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [Sfun, this]

/-- Abel summation with a complex exponent. -/
lemma tendsto_abel (n : ℕ) [NeZero n] {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ k ∈ Icc 0 N, ((k : ℝ) : ℂ) ^ (-s) * aC n k) atTop
      (𝓝 (s * ∫ t in Set.Ioi (1 : ℝ), Sfun n t * (t : ℂ) ^ (-(s + 1)))) := by
  have h₂ : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have h₁ : (-s - 1).re + 0 < -1 := by simp; linarith
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
  have h₄ : ∀ m, ∑ k ∈ Icc 0 m, aC n k = ∑ k ∈ Icc 1 m, aC n k := fun m ↦ by
    rw [← insert_Icc_add_one_left_eq_Icc m.zero_le, sum_insert (by simp), aC_zero, zero_add, zero_add]
  have hO : (fun m : ℕ ↦ ∑ k ∈ Icc 0 m, aC n k) =O[atTop] fun m : ℕ ↦ (m : ℝ) ^ (0 : ℝ) := by
    refine IsBigO.of_bound (n : ℝ) (Eventually.of_forall fun m ↦ ?_)
    rw [h₄]; simpa using norm_sum_aC_le n m
  convert tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := aC n)
      (f := fun x : ℝ ↦ (x : ℂ) ^ (-s)) (l := 0) (aC_zero n) h₃ ?_
      ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁) using 2
  · rw [zero_sub, ← integral_neg, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [Complex.deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne']
    · simp only [Sfun]; rw [← h₄]; ring_nf
    · exact neg_ne_zero.mpr h₂
  · refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using hs)).locallyIntegrableOn
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(s.re - 0))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by simpa using hs)).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
    · exact isBigO_norm_left.mp <| (Complex.norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  · refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) 0 _ ?_ ?_
      (by rw [← Complex.neg_re, neg_add'])
    · simpa [-neg_add_rev, neg_add'] using! isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow le_rfl (eventually_ge_atTop 0)

/-- The function `G(s) = s ∫_{t > 1} S(t) t^{-(s+1)} dt`. -/
noncomputable def G (n : ℕ) (s : ℂ) : ℂ := s * ∫ t in Set.Ioi (1 : ℝ), Sfun n t * (t : ℂ) ^ (-(s + 1))

lemma G_differentiableAt (n : ℕ) [NeZero n] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (G n) s := by
  have hG : G n = fun z => z * mellin (Sfun n) (-z) := by
    funext z
    simp only [G, mellin]
    congr 1
    have h1 : ∀ t : ℝ, (t : ℂ) ^ (-z - 1) • Sfun n t = Sfun n t * (t : ℂ) ^ (-(z + 1)) := by
      intro t; rw [smul_eq_mul, mul_comm, neg_add']
    simp_rw [h1]
    rw [← integral_Ici_eq_integral_Ioi]
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x (hx : (1 : ℝ) ≤ x) => (lt_of_lt_of_le one_pos hx : (0 : ℝ) < x)) ?_
    rintro x ⟨-, hx1⟩
    simp only [Set.mem_Ici, not_le] at hx1
    rw [Sfun_eq_zero hx1, zero_mul]
  have hfc : LocallyIntegrableOn (Sfun n) (Set.Ioi 0) := by
    have := locallyIntegrableOn_mul_sum_Icc (aC n) (m := 1) (le_refl (0 : ℝ))
      (g := fun _ => (1 : ℂ)) (locallyIntegrableOn_const 1)
    have h2 : LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, aC n k) (Set.Ioi 0) := by
      simpa using this.mono_set Set.Ioi_subset_Ici_self
    exact h2
  have htop : Sfun n =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound (n : ℝ) (Eventually.of_forall fun t => ?_)
    simpa using norm_Sfun_le n t
  have hbot : Sfun n =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-s.re - 1))) := by
    have : Sfun n =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht using Sfun_eq_zero ht.2
    exact this.trans_isBigO (isBigO_zero _ _)
  have hm : DifferentiableAt ℂ (mellin (Sfun n)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hfc htop (by simp; linarith) hbot (by simp)
  rw [hG]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

lemma aC_eq (n : ℕ) [NeZero n] : (fun m : ℕ => chi n (m : ZMod (4 * n))) = aC n :=
  funext fun m => chi_natCast n m

lemma LFunction_eq_G_of_one_lt (n : ℕ) [NeZero n] {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction (chi n) s = G n s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  have hsum : LSeriesSummable (aC n) s := by
    rw [← aC_eq]; exact DirichletCharacter.LSeriesSummable_of_one_lt_re (chi n) hs
  have hO : (fun m : ℕ ↦ ∑ k ∈ Icc 1 m, aC n k) =O[atTop] fun m : ℕ ↦ (m : ℝ) ^ (0 : ℝ) := by
    refine IsBigO.of_bound (n : ℝ) (Eventually.of_forall fun m ↦ ?_)
    simpa using norm_sum_aC_le n m
  rw [aC_eq, G, LSeries_eq_mul_integral (aC n) le_rfl (by linarith) hsum hO]
  rfl

lemma LFunction_eq_G (n : ℕ) [NeZero n] {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction (chi n) s = G n s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction (chi n)) {z : ℂ | 0 < z.re} :=
    (DirichletCharacter.differentiable_LFunction (chi_ne_one n)).differentiableOn.analyticOnNhd hU
  have hGd : DifferentiableOn ℂ (G n) {z : ℂ | 0 < z.re} :=
    fun z hz => (G_differentiableAt n hz).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ (G n) {z : ℂ | 0 < z.re} := hGd.analyticOnNhd hU
  refine hL.eqOn_of_preconnected_of_eventuallyEq hGa (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz using LFunction_eq_G_of_one_lt n hz

lemma partial_eq (n : ℕ) (σ : ℝ) (N : ℕ) :
    (((∑ d ∈ Finset.Icc 1 N, (chiZ n d : ℝ) / (d : ℝ) ^ σ : ℝ)) : ℂ) =
      ∑ k ∈ Icc 0 N, ((k : ℝ) : ℂ) ^ (-(σ : ℂ)) * aC n k := by
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), aC_zero, mul_zero,
    zero_add, zero_add, Complex.ofReal_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.cpow_neg, aC,
    div_eq_mul_inv, mul_comm]
  push_cast
  ring

lemma tendsto_complex (n : ℕ) [NeZero n] {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => (((∑ d ∈ Finset.Icc 1 N, (chiZ n d : ℝ) / (d : ℝ) ^ σ : ℝ)) : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction (chi n) (σ : ℂ))) := by
  simp_rw [partial_eq]
  rw [LFunction_eq_G n (by simpa using hσ)]
  exact tendsto_abel n (by simpa using hσ)

end LBridgeAux

open Filter Topology LBridgeAux

/-- For `σ > 0` the partial sums of `∑ chiZ n d / d^σ` converge to `Lreal n σ`. -/
theorem tendsto_partial_sums_Lreal (n : ℕ) [NeZero n] {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, (chiZ n d : ℝ) / (d : ℝ) ^ σ)
      Filter.atTop (nhds (Lreal n σ)) := by
  have := (Complex.continuous_re.tendsto _).comp (tendsto_complex n hσ)
  simpa [Function.comp_def, Lreal] using this

namespace LBridgeAux

open Filter Topology Finset

lemma LFunction_eq_ofReal (n : ℕ) [NeZero n] {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction (chi n) (σ : ℂ) = (Lreal n σ : ℂ) :=
  tendsto_nhds_unique (tendsto_complex n hσ)
    ((Complex.continuous_ofReal.tendsto _).comp (tendsto_partial_sums_Lreal n hσ))

lemma partial_two_ge (n : ℕ) (N : ℕ) (hN : 1 ≤ N) :
    1 / 3 + 2 / (2 * (N : ℝ) + 1) ≤ ∑ d ∈ Finset.Icc 1 N, (chiZ n d : ℝ) / (d : ℝ) ^ (2 : ℝ) := by
  simp_rw [Real.rpow_two]
  induction N, hN using Nat.le_induction with
  | base => simp [chiZ_one']; norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hab := abs_chiZ_le n (N + 1)
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hterm : -1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ (chiZ n (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith [neg_abs_le (chiZ n (N + 1) : ℝ)]) hpos.le
    have key : 1 / ((N : ℝ) + 1) ^ 2 + 2 / (2 * ((N : ℝ) + 1) + 1) ≤ 2 / (2 * N + 1) := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      ring_nf; nlinarith
    push_cast at hterm ⊢
    have : -1 / ((N : ℝ) + 1) ^ 2 = -(1 / ((N : ℝ) + 1) ^ 2) := by ring
    linarith

lemma Lreal_two_pos (n : ℕ) [NeZero n] : 0 < Lreal n 2 := by
  have h := tendsto_partial_sums_Lreal n (σ := 2) two_pos
  have : (1 / 3 : ℝ) ≤ Lreal n 2 := by
    refine ge_of_tendsto h ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    refine le_trans ?_ (partial_two_ge n N hN)
    have : (0 : ℝ) ≤ 2 / (2 * (N : ℝ) + 1) := by positivity
    linarith
  linarith

lemma continuous_Lreal (n : ℕ) [NeZero n] : Continuous (Lreal n) :=
  Complex.continuous_re.comp
    ((DirichletCharacter.differentiable_LFunction (chi_ne_one n)).continuous.comp
      Complex.continuous_ofReal)

end LBridgeAux

theorem Lreal_nonneg_of_noRealZeros (h : NoRealZeros) (n : ℕ) [NeZero n] {σ : ℝ}
    (hσ : 19 / 20 ≤ σ) (hσ1 : σ < 1) : 0 ≤ Lreal n σ := by
  by_contra hneg
  push Not at hneg
  have hle : σ ≤ 2 := by linarith
  have hmem : (0 : ℝ) ∈ Set.Icc (Lreal n σ) (Lreal n 2) := ⟨hneg.le, (Lreal_two_pos n).le⟩
  obtain ⟨c, ⟨hc1, hc2⟩, hc⟩ :=
    intermediate_value_Icc hle (continuous_Lreal n).continuousOn hmem
  have hcpos : 0 < c := by linarith
  have hL : DirichletCharacter.LFunction (chi n) (c : ℂ) = 0 := by
    rw [LFunction_eq_ofReal n hcpos, hc, Complex.ofReal_zero]
  rcases lt_or_ge c 1 with hc1' | hc1'
  · exact h (4 * n) (chi n) (chi_ne_one n) c (by linarith) hc1' hL
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (chi n) (Or.inl (chi_ne_one n))
      (by simpa using hc1') hL

end Idoneal
