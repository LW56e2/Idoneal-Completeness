import Idoneal.Roots
import Idoneal.Forms
import Idoneal.Lattice
import Idoneal.LBridge
import Idoneal.Pintz

/-!
# The analytic bound (blueprint §1 (A))

For `n ≥ 10⁶` without a strict form, under `NoRealZeros`:
`√n ≤ π · τ(n) · (log n + 16)`.
-/

namespace Idoneal

open Finset

/-- The Pintz data for `a = chiZ n`, `M = n`, `L = Lreal n`. -/
theorem pintzData_chi (h : NoRealZeros) (n : ℕ) [NeZero n] :
    PintzData (fun d => (chiZ n d : ℝ)) (n : ℝ) (Lreal n) where
  abs_le_one := by
    intro d
    rcases chiZ_trichotomy n d with h0 | h1 | h2
    · simp [h0]
    · simp [h1]
    · simp [h2]
  partial_sums := by
    intro N
    have h1 := abs_sum_chiZ_le (Nat.pos_of_ne_zero (NeZero.ne n)) N
    have h2 : ((|∑ d ∈ Icc 1 N, chiZ n d| : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h1
    simpa using h2
  conv_nonneg := by
    intro k
    have h1 := gZ_nonneg n k
    have h2 : (0 : ℝ) ≤ ((gZ n k : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [gZ] using h2
  conv_sq := by
    intro j hj
    have h1 := one_le_gZ_sq n hj
    have h2 : (1 : ℝ) ≤ ((gZ n (j ^ 2) : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [gZ] using h2
  tendsto := fun _ hσ => tendsto_partial_sums_Lreal n hσ
  nonneg := fun _ h1 h2 => Lreal_nonneg_of_noRealZeros h n h1 h2

/-- For every `X`: `2 (X L₁ - (4n+1)√X) ≤ τ(n) (π X/√n + 5√X + 5)`. -/
theorem key_inequality (h : NoRealZeros) (n : ℕ) [NeZero n] (hns : ¬ HasStrictForm n) (X : ℕ) :
    2 * ((X : ℝ) * Lreal n 1 - (4 * (n : ℝ) + 1) * Real.sqrt X)
      ≤ (n.divisors.card : ℝ) * (Real.pi * X / Real.sqrt n + 5 * Real.sqrt X + 5) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hP := (pintzData_chi h n).sum_conv_ge hn1 X
  have hR : (∑ k ∈ Icc 1 X, ∑ d ∈ k.divisors, (chiZ n d : ℝ)) ≤
      ((∑ k ∈ Icc 1 X, ∑ e ∈ (Icc 1 k).filter (fun e => e ^ 2 ∣ k),
        rho n (k / e ^ 2) : ℕ) : ℝ) := by
    have h1 : (∑ k ∈ Icc 1 X, gZ n k) ≤ ∑ k ∈ Icc 1 X,
        ∑ e ∈ (Icc 1 k).filter (fun e => e ^ 2 ∣ k), (rho n (k / e ^ 2) : ℤ) :=
      Finset.sum_le_sum fun k hk => gZ_le_sum_rho hn (by
        have := (Finset.mem_Icc.mp hk).1; omega)
    have h2 : ((∑ k ∈ Icc 1 X, gZ n k : ℤ) : ℝ) ≤ ((∑ k ∈ Icc 1 X,
        ∑ e ∈ (Icc 1 k).filter (fun e => e ^ 2 ∣ k), (rho n (k / e ^ 2) : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast h1
    simpa [gZ] using h2
  have hF : (2 : ℝ) * ((∑ k ∈ Icc 1 X, ∑ e ∈ (Icc 1 k).filter (fun e => e ^ 2 ∣ k),
      rho n (k / e ^ 2) : ℕ) : ℝ) ≤ ((∑ f ∈ ambiguousForms n, latticeCount f X : ℕ) : ℝ) := by
    exact_mod_cast two_mul_sum_rho_le_lattice hn hns X
  have hpos : 0 ≤ Real.pi * X / Real.sqrt n + 5 * Real.sqrt X + 5 := by positivity
  have hL : ((∑ f ∈ ambiguousForms n, latticeCount f X : ℕ) : ℝ) ≤
      ((ambiguousForms n).card : ℝ) * (Real.pi * X / Real.sqrt n + 5 * Real.sqrt X + 5) := by
    push_cast
    calc ∑ f ∈ ambiguousForms n, (latticeCount f X : ℝ)
        ≤ ∑ _f ∈ ambiguousForms n, (Real.pi * X / Real.sqrt n + 5 * Real.sqrt X + 5) :=
          Finset.sum_le_sum fun f hf => latticeCount_le hn ((mem_ambiguousForms hn f).mp hf) X
      _ = ((ambiguousForms n).card : ℝ) * (Real.pi * X / Real.sqrt n + 5 * Real.sqrt X + 5) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hC : ((ambiguousForms n).card : ℝ) ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast card_ambiguousForms_le hn
  have hCm := mul_le_mul_of_nonneg_right hC hpos
  linarith

/-- Letting `X → ∞` in `key_inequality`: `2 L₁ ≤ π τ(n) / √n`. -/
theorem two_mul_Lreal_one_le (h : NoRealZeros) (n : ℕ) [NeZero n] (hns : ¬ HasStrictForm n) :
    2 * Lreal n 1 ≤ (n.divisors.card : ℝ) * Real.pi / Real.sqrt n := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (n.divisors.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 * Lreal n 1 - τ * Real.pi / Real.sqrt n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * (4 * (n : ℝ) + 1) + 5 * τ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hδpos : 0 < δ := by rw [hδ, hτ]; linarith
  obtain ⟨K, hK⟩ := exists_nat_gt ((C + 5 * τ) / δ + 1)
  have hq0 : 0 ≤ (C + 5 * τ) / δ := div_nonneg (by linarith) hδpos.le
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have key := key_inequality h n hns (K ^ 2)
  have hsq : Real.sqrt ((K ^ 2 : ℕ) : ℝ) = K := by
    push_cast
    exact Real.sqrt_sq (by positivity)
  rw [hsq] at key
  push_cast at key
  rw [← hτ] at key
  have e : τ * (Real.pi * (K : ℝ) ^ 2 / Real.sqrt n + 5 * K + 5) =
      (τ * Real.pi / Real.sqrt n) * (K : ℝ) ^ 2 + 5 * τ * K + 5 * τ := by ring
  rw [e] at key
  have h1 : δ * (K : ℝ) ^ 2 ≤ C * K + 5 * τ := by
    rw [hδ, hC]; nlinarith [key]
  have h2 : C + 5 * τ < δ * K := by
    have h3 : (C + 5 * τ) / δ < K := by linarith
    have := (div_lt_iff₀ hδpos).mp h3
    linarith
  nlinarith [h1, h2, hK1, hτ0, hC0]

/-- The analytic bound (★). -/
theorem analytic_bound (h : NoRealZeros) {n : ℕ} (hn : 1000000 ≤ n) (hns : ¬ HasStrictForm n) :
    Real.sqrt n ≤ Real.pi * (n.divisors.card : ℝ) * (Real.log n + 16) := by
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨hn0.ne'⟩
  have h1 := two_mul_Lreal_one_le h n hns
  have h2 := (pintzData_chi h n).one_le (by exact_mod_cast hn)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlog : 0 < Real.log (n : ℝ) + 16 := by linarith
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  have h3 : 1 / (Real.log (n : ℝ) + 16) ≤ (n.divisors.card : ℝ) * Real.pi / Real.sqrt n := by
    have e : 1 / (Real.log (n : ℝ) + 16) = 2 * (1 / (2 * (Real.log (n : ℝ) + 16))) := by
      field_simp
    rw [e]; linarith
  rw [div_le_div_iff₀ hlog hsqrt] at h3
  linarith

end Idoneal
