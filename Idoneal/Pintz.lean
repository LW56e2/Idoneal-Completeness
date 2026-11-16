import Mathlib

/-!
# A Pintz-type lower bound for `L(1)`, abstract version (blueprint §1 (P))

Interface: the structure `PintzData` and the theorems `PintzData.sum_conv_ge`, `PintzData.one_le`.
-/

namespace Idoneal

/-- The data of the argument: a bounded sequence `a` with bounded partial sums, whose
convolution with `1` is nonnegative and `≥ 1` at squares, with `L σ = ∑ a d / d^σ` for `σ > 0`
and `L σ ≥ 0` on `[19/20, 1)`. -/
structure PintzData (a : ℕ → ℝ) (M : ℝ) (L : ℝ → ℝ) : Prop where
  abs_le_one : ∀ d : ℕ, |a d| ≤ 1
  partial_sums : ∀ N : ℕ, |∑ d ∈ Finset.Icc 1 N, a d| ≤ M
  conv_nonneg : ∀ k : ℕ, 0 ≤ ∑ d ∈ k.divisors, a d
  conv_sq : ∀ j : ℕ, 0 < j → 1 ≤ ∑ d ∈ (j ^ 2).divisors, a d
  tendsto : ∀ σ : ℝ, 0 < σ →
    Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, a d / (d : ℝ) ^ σ)
      Filter.atTop (nhds (L σ))
  nonneg : ∀ σ : ℝ, 19 / 20 ≤ σ → σ < 1 → 0 ≤ L σ

open Finset

private lemma Icc_one_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x; simp; omega

/-- Split `Icc 1 X` at `Y`. -/
private lemma sum_Icc_split (f : ℕ → ℝ) {Y X : ℕ} (h : Y ≤ X) :
    ∑ d ∈ Icc 1 X, f d = ∑ d ∈ Icc 1 Y, f d + ∑ d ∈ Ioc Y X, f d := by
  rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, sum_Ioc_consecutive _ (Nat.zero_le Y) h]

/-- Abel summation, auxiliary form. -/
private lemma abel_aux (b w : ℕ → ℝ) (C : ℝ) (Y : ℕ)
    (hS : ∀ n, Y < n → |∑ d ∈ Ioc Y n, b d| ≤ C)
    (hw : ∀ n, Y + 1 ≤ n → w (n + 1) ≤ w n) (X : ℕ) (hYX : Y + 1 ≤ X) :
    |∑ d ∈ Ioc Y X, b d * w d - (∑ d ∈ Ioc Y X, b d) * w X| ≤ C * (w (Y + 1) - w X) := by
  induction X, hYX using Nat.le_induction with
  | base => simp [Nat.Ioc_succ_singleton]
  | succ X hX ih =>
    rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
    have h1 := hS X (by omega)
    have h2 := hw X hX
    have e : ∑ d ∈ Ioc Y X, b d * w d + b (X + 1) * w (X + 1)
        - (∑ d ∈ Ioc Y X, b d + b (X + 1)) * w (X + 1)
        = (∑ d ∈ Ioc Y X, b d * w d - (∑ d ∈ Ioc Y X, b d) * w X)
          + (∑ d ∈ Ioc Y X, b d) * (w X - w (X + 1)) := by ring
    rw [e]
    calc _ ≤ |∑ d ∈ Ioc Y X, b d * w d - (∑ d ∈ Ioc Y X, b d) * w X|
          + |(∑ d ∈ Ioc Y X, b d) * (w X - w (X + 1))| := abs_add_le _ _
      _ ≤ C * (w (Y + 1) - w X) + C * (w X - w (X + 1)) := by
          gcongr
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ w X - w (X + 1))]
          exact mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = _ := by ring

/-- Abel summation: bounded partial sums against a nonnegative nonincreasing weight. -/
private lemma abel_bound (b w : ℕ → ℝ) (C : ℝ) (Y X : ℕ) (hC : 0 ≤ C)
    (hS : ∀ n, Y < n → |∑ d ∈ Ioc Y n, b d| ≤ C)
    (hw : ∀ n, Y + 1 ≤ n → n + 1 ≤ X → w (n + 1) ≤ w n)
    (hw0 : ∀ n, Y + 1 ≤ n → n ≤ X → 0 ≤ w n) (hwY : 0 ≤ w (Y + 1)) :
    |∑ d ∈ Ioc Y X, b d * w d| ≤ C * w (Y + 1) := by
  rcases Nat.lt_or_ge Y X with hYX | hYX
  · -- modify `w` beyond `X` to be constant, to apply `abel_aux`
    set w' : ℕ → ℝ := fun n => if n ≤ X then w n else w X with hw'
    have hw'mono : ∀ n, Y + 1 ≤ n → w' (n + 1) ≤ w' n := by
      intro n hn
      simp only [hw']
      by_cases h1 : n + 1 ≤ X
      · rw [if_pos h1, if_pos (by omega)]; exact hw n hn h1
      · rw [if_neg h1]
        by_cases h2 : n ≤ X
        · rw [if_pos h2]; have : n = X := by omega
          rw [this]
        · rw [if_neg h2]
    have key := abel_aux b w' C Y hS hw'mono X hYX
    have eqs : ∑ d ∈ Ioc Y X, b d * w' d = ∑ d ∈ Ioc Y X, b d * w d := by
      apply sum_congr rfl
      intro d hd
      simp only [hw', if_pos (mem_Ioc.1 hd).2]
    have e1 : w' X = w X := by simp [hw']
    have e2 : w' (Y + 1) = w (Y + 1) := by simp only [hw', if_pos (show Y + 1 ≤ X by omega)]
    rw [eqs, e1, e2] at key
    have hX0 : 0 ≤ w X := hw0 X (by omega) le_rfl
    have hS' := hS X hYX
    calc _ = |(∑ d ∈ Ioc Y X, b d * w d - (∑ d ∈ Ioc Y X, b d) * w X)
            + (∑ d ∈ Ioc Y X, b d) * w X| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ C * (w (Y + 1) - w X) + C * w X := by
          gcongr
          rw [abs_mul, abs_of_nonneg hX0]
          exact mul_le_mul_of_nonneg_right hS' hX0
      _ = _ := by ring
  · rw [Ioc_eq_empty (by omega)]
    simpa using mul_nonneg hC hwY

namespace PintzData

variable {a : ℕ → ℝ} {M : ℝ} {L : ℝ → ℝ}

lemma M_nonneg (h : PintzData a M L) : 0 ≤ M := by
  simpa using h.partial_sums 0

lemma partial_Ioc (h : PintzData a M L) (Y n : ℕ) (hn : Y ≤ n) :
    |∑ d ∈ Ioc Y n, a d| ≤ 2 * M := by
  have e := sum_Icc_split a hn
  have h1 := h.partial_sums n
  have h2 := h.partial_sums Y
  have : ∑ d ∈ Ioc Y n, a d = ∑ d ∈ Icc 1 n, a d - ∑ d ∈ Icc 1 Y, a d := by linarith
  rw [this]
  calc _ ≤ |∑ d ∈ Icc 1 n, a d| + |∑ d ∈ Icc 1 Y, a d| := abs_sub _ _
    _ ≤ _ := by linarith

/-- Abel bound for the sequence `a`. -/
lemma abel (h : PintzData a M L) (w : ℕ → ℝ) (Y X : ℕ)
    (hw : ∀ n, Y + 1 ≤ n → n + 1 ≤ X → w (n + 1) ≤ w n)
    (hw0 : ∀ n, Y + 1 ≤ n → n ≤ X → 0 ≤ w n) (hwY : 0 ≤ w (Y + 1)) :
    |∑ d ∈ Ioc Y X, a d * w d| ≤ 2 * M * w (Y + 1) :=
  abel_bound a w (2 * M) Y X (by linarith [h.M_nonneg])
    (fun n hn => h.partial_Ioc Y n hn.le) hw hw0 hwY

/-- (Abel 1) Tail bound for the Dirichlet series. -/
lemma tail (h : PintzData a M L) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    |L σ - ∑ d ∈ Icc 1 N, a d / (d : ℝ) ^ σ| ≤ 2 * M / ((N : ℝ) + 1) ^ σ := by
  set f : ℕ → ℝ := fun n => ∑ d ∈ Icc 1 n, a d / (d : ℝ) ^ σ with hf
  have hlim : Filter.Tendsto (fun n => |f n - f N|) Filter.atTop (nhds |L σ - f N|) :=
    ((h.tendsto σ hσ).sub_const (f N)).abs
  refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have e : f n - f N = ∑ d ∈ Ioc N n, a d * (1 / (d : ℝ) ^ σ) := by
    simp only [hf]
    rw [sum_Icc_split _ hn]
    simp [div_eq_mul_inv]
  rw [e]
  have := h.abel (fun d => 1 / (d : ℝ) ^ σ) N n ?_ ?_ ?_
  · simpa [div_eq_mul_inv] using this
  · intro m hm _
    apply one_div_le_one_div_of_le
    · apply Real.rpow_pos_of_pos; exact_mod_cast (show 0 < m by omega)
    · apply Real.rpow_le_rpow (by positivity) (by push_cast; linarith) hσ.le
  · intro m _ _; positivity
  · positivity

/-- Divisor-sum interchange. -/
lemma sum_divisors_interchange (a φ : ℕ → ℝ) (X : ℕ) :
    ∑ k ∈ Icc 1 X, (∑ d ∈ k.divisors, a d) * φ k
      = ∑ d ∈ Icc 1 X, a d * ∑ m ∈ Icc 1 (X / d), φ (d * m) := by
  have inner : ∀ d ∈ Icc 1 X, ∑ m ∈ Icc 1 (X / d), φ (d * m)
      = ∑ k ∈ (Icc 1 X).filter (fun k => d ∣ k), φ k := by
    intro d hd
    have hd1 : 0 < d := by simp at hd; omega
    apply sum_nbij' (fun m => d * m) (fun k => k / d)
    · intro m hm
      simp only [mem_Icc, coe_filter, mem_filter, mem_coe] at hm ⊢
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).1 hm.2
      linarith [mul_comm m d]
    · intro k hk
      simp only [mem_Icc, coe_filter, mem_filter, mem_coe] at hk ⊢
      obtain ⟨⟨hk1, hk2⟩, hdk⟩ := hk
      refine ⟨Nat.div_pos (Nat.le_of_dvd hk1 hdk) hd1, Nat.div_le_div_right hk2⟩
    · intro m _; simp [Nat.mul_div_cancel_left m hd1]
    · intro k hk
      simp only [coe_filter, mem_filter, mem_coe] at hk
      exact Nat.mul_div_cancel' hk.2
    · intro m _; rfl
  rw [show ∑ d ∈ Icc 1 X, a d * ∑ m ∈ Icc 1 (X / d), φ (d * m)
      = ∑ d ∈ Icc 1 X, a d * ∑ k ∈ (Icc 1 X).filter (fun k => d ∣ k), φ k from
      sum_congr rfl (fun d hd => by rw [inner d hd])]
  simp_rw [sum_mul, mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [mem_filter, mem_Icc, Nat.mem_divisors] at hk ⊢
  constructor
  · rintro ⟨hx, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hx (by omega), (Nat.le_of_dvd (by omega) hx).trans hk.2⟩, hx⟩
  · rintro ⟨_, hx⟩; exact ⟨hx, by omega⟩

end PintzData

/-- Hyperbola method: `∑_{k ≤ X} (1 * a)(k) ≥ X · L 1 - (4M + 1) √X`. -/
theorem PintzData.sum_conv_ge {a : ℕ → ℝ} {M : ℝ} {L : ℝ → ℝ} (h : PintzData a M L)
    (hM : 1 ≤ M) (X : ℕ) :
    (X : ℝ) * L 1 - (4 * M + 1) * Real.sqrt X
      ≤ ∑ k ∈ Finset.Icc 1 X, ∑ d ∈ k.divisors, a d := by
  have hM0 := h.M_nonneg
  set Y := Nat.sqrt X with hYdef
  have hYX : Y ≤ X := Nat.sqrt_le_self X
  have e0 : ∑ k ∈ Icc 1 X, ∑ d ∈ k.divisors, a d
      = ∑ d ∈ Icc 1 X, a d * ((X / d : ℕ) : ℝ) := by
    have := PintzData.sum_divisors_interchange a (fun _ => 1) X
    simpa using this
  rw [e0, sum_Icc_split _ hYX]
  have hhead : ∀ d ∈ Icc 1 Y, (X:ℝ) * (a d / (d:ℝ) ^ (1:ℝ)) - 1 ≤ a d * ((X / d : ℕ) : ℝ) := by
    intro d hd
    have hd0 : 0 < d := by simp at hd; omega
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
    rw [Real.rpow_one]
    have q1 : ((X / d : ℕ) : ℝ) ≤ (X:ℝ) / d := Nat.cast_div_le
    have q2 : (X:ℝ) / d < ((X / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by linarith)]
      have := Nat.lt_mul_div_succ X hd0
      have : (X:ℝ) < (d:ℝ) * (((X / d : ℕ) : ℝ) + 1) := by exact_mod_cast this
      linarith
    have ha := abs_le.1 (h.abs_le_one d)
    have ht := mul_le_mul_of_nonneg_right ha.2 (sub_nonneg.2 q1)
    have : (X:ℝ) * (a d / d) = a d * ((X:ℝ) / d) := by ring
    nlinarith
  have hsum1 := sum_le_sum hhead
  rw [sum_sub_distrib, ← mul_sum] at hsum1
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one, Real.rpow_one] at hsum1
  have ht1 := abs_le.1 (h.tail one_pos Y)
  simp only [Real.rpow_one] at ht1
  -- tail part
  have htail := h.abel (fun n => ((X / n : ℕ) : ℝ)) Y X
    (fun n hn _ => by exact_mod_cast Nat.div_le_div_left (Nat.le_succ n) (by omega))
    (fun n _ _ => by positivity) (by positivity)
  have htail' := (abs_le.1 htail).1
  have hq : ((X / (Y + 1) : ℕ) : ℝ) ≤ (X:ℝ) / ((Y:ℝ) + 1) := by
    have := (Nat.cast_div_le (α := ℝ) (m := X) (n := Y + 1)); push_cast at this; exact this
  have hsq1 : (Y:ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  have hsq2 : Real.sqrt X < (Y:ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hXY : (X:ℝ) / ((Y:ℝ) + 1) ≤ Real.sqrt X := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.mul_self_sqrt (Nat.cast_nonneg X : (0:ℝ) ≤ X)
    nlinarith [Real.sqrt_nonneg (X:ℝ)]
  set S1 := ∑ d ∈ Icc 1 Y, a d / (d:ℝ)
  have h1 : (X:ℝ) * (L 1 - 2 * M / ((Y:ℝ) + 1)) ≤ X * S1 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg X)
  have h2 : (X:ℝ) * (2 * M / ((Y:ℝ) + 1)) = 2 * M * ((X:ℝ) / ((Y:ℝ) + 1)) := by ring
  have h3 : 2 * M * ((X:ℝ) / ((Y:ℝ) + 1)) ≤ 2 * M * Real.sqrt X := by gcongr
  have h4 : 2 * M * ((X / (Y + 1) : ℕ) : ℝ) ≤ 2 * M * Real.sqrt X := by
    have := hq.trans hXY; gcongr
  nlinarith

/-! ### Partial sums of `m^{-β}` -/

/-- Tangent line bound for the concave function `t ↦ t ^ s`, `0 ≤ s ≤ 1`. -/
private lemma tangent {s u v : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu : 0 < u) (hv : 0 ≤ v) :
    v ^ s ≤ u ^ s + s * u ^ (s - 1) * (v - u) := by
  have hx : -1 ≤ (v - u) / u := by rw [le_div_iff₀ hu]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hx hs0 hs1
  have hv' : v = u * (1 + (v - u) / u) := by field_simp; ring
  have hus : u ^ (s - 1) = u ^ s / u := Real.rpow_sub_one hu.ne' s
  have h1 : 0 ≤ 1 + (v - u) / u := by linarith
  calc v ^ s = u ^ s * (1 + (v - u) / u) ^ s := by
        conv_lhs => rw [hv']
        rw [Real.mul_rpow hu.le h1]
    _ ≤ u ^ s * (1 + s * ((v - u) / u)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hu.le _)
    _ = _ := by rw [hus]; field_simp

private lemma rpow_neg_eq {β y : ℝ} (hy : 0 < y) : y ^ (-β) = y ^ (1 - β) / y := by
  rw [show -β = (1 - β) - 1 by ring, Real.rpow_sub_one hy.ne']

/-- `H(N) = ∑_{m ≤ N} m^{-β}`. -/
private noncomputable def Hs (β : ℝ) (N : ℕ) : ℝ := ∑ m ∈ Icc 1 N, (m : ℝ) ^ (-β)

/-- `D(N) = N^{1-β}/(1-β) - H(N)`. -/
private noncomputable def Ds (β : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 - β) / (1 - β) - Hs β N

private lemma Hs_succ (β : ℝ) (N : ℕ) : Hs β (N + 1) = Hs β N + ((N : ℝ) + 1) ^ (-β) := by
  unfold Hs
  rw [sum_Icc_succ_top (by omega)]
  push_cast; ring

private lemma Hs_nonneg (β : ℝ) (N : ℕ) : 0 ≤ Hs β N :=
  sum_nonneg (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _)

private lemma Hs_mono (β : ℝ) {N N' : ℕ} (h : N ≤ N') : Hs β N ≤ Hs β N' :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h)
    (fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg m) _)

private lemma Ds_step_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (N : ℕ) :
    Ds β N ≤ Ds β (N + 1) := by
  have hs0 : 0 < 1 - β := by linarith
  have ht := tangent (s := 1 - β) (u := (N : ℝ) + 1) (v := N) hs0.le (by linarith)
    (by positivity) (Nat.cast_nonneg N)
  rw [show (1 - β) - 1 = -β by ring] at ht
  have key : ((N : ℝ) + 1) ^ (-β) ≤ (((N : ℝ) + 1) ^ (1 - β) - (N : ℝ) ^ (1 - β)) / (1 - β) := by
    rw [le_div_iff₀ hs0]; nlinarith
  unfold Ds
  rw [Hs_succ]
  push_cast
  have : (((N : ℝ) + 1) ^ (1 - β) - (N : ℝ) ^ (1 - β)) / (1 - β)
      = ((N : ℝ) + 1) ^ (1 - β) / (1 - β) - (N : ℝ) ^ (1 - β) / (1 - β) := by ring
  linarith

private lemma Ds_step_upper {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N : ℕ} (hN : 1 ≤ N) :
    Ds β (N + 1) ≤ Ds β N + (N : ℝ) ^ (-β) - ((N : ℝ) + 1) ^ (-β) := by
  have hs0 : 0 < 1 - β := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht := tangent (s := 1 - β) (u := (N : ℝ)) (v := (N : ℝ) + 1) hs0.le (by linarith)
    hNr (by positivity)
  rw [show (1 - β) - 1 = -β by ring, show (N : ℝ) + 1 - N = 1 by ring, mul_one] at ht
  have key : (((N : ℝ) + 1) ^ (1 - β) - (N : ℝ) ^ (1 - β)) / (1 - β) ≤ (N : ℝ) ^ (-β) := by
    rw [div_le_iff₀ hs0]; nlinarith
  unfold Ds
  rw [Hs_succ]
  push_cast
  have : (((N : ℝ) + 1) ^ (1 - β) - (N : ℝ) ^ (1 - β)) / (1 - β)
      = ((N : ℝ) + 1) ^ (1 - β) / (1 - β) - (N : ℝ) ^ (1 - β) / (1 - β) := by ring
  linarith

private lemma Ds_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N N' : ℕ} (h : N ≤ N') :
    Ds β N ≤ Ds β N' := by
  induction N', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Ds_step_lower hβ0 hβ1 n)

private lemma Ds_diff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N N' : ℕ} (hN : 1 ≤ N) (h : N ≤ N') :
    Ds β N' ≤ Ds β N + (N : ℝ) ^ (-β) - (N' : ℝ) ^ (-β) := by
  induction N', h using Nat.le_induction with
  | base => linarith
  | succ n hn ih =>
    have := Ds_step_upper hβ0 hβ1 (hN.trans hn)
    push_cast
    linarith

private lemma Ds_zero {β : ℝ} (hβ1 : β < 1) : Ds β 0 = 0 := by
  simp [Ds, Hs, Real.zero_rpow (show (1 - β) ≠ 0 by linarith)]

private lemma Ds_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (N : ℕ) : 0 ≤ Ds β N := by
  have := Ds_mono hβ0 hβ1 (Nat.zero_le N)
  rwa [Ds_zero hβ1] at this

private lemma Ds_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (N : ℕ) : Ds β N ≤ 1 / (1 - β) := by
  have hs0 : 0 < 1 - β := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Ds_zero hβ1]; positivity
  · have h1 := Ds_diff hβ0 hβ1 (le_refl 1) hN
    have hD1 : Ds β 1 = 1 / (1 - β) - 1 := by simp [Ds, Hs]
    have : 0 ≤ (N : ℝ) ^ (-β) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    simp only [Nat.cast_one, Real.one_rpow] at h1
    linarith

private lemma Hs_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (N : ℕ) :
    Hs β N ≤ (N : ℝ) ^ (1 - β) / (1 - β) := by
  have := Ds_nonneg hβ0 hβ1 N
  unfold Ds at this
  linarith

/-- The contribution of one small `d` (`2 d ≤ X`). -/
private lemma head_term {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {X d : ℕ} (hd : 1 ≤ d)
    (h2d : 2 * d ≤ X) {ad : ℝ} (had : |ad| ≤ 1) :
    ad * ((d : ℝ) ^ (-β) * Hs β (X / d))
      ≤ (X : ℝ) ^ (1 - β) / (1 - β) * (ad / d) - Ds β X * (ad / (d : ℝ) ^ β)
        + 2 * (X : ℝ) ^ (1 - β) / X := by
  have hs0 : 0 < 1 - β := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdX : d ≤ X := by omega
  have hN1 : 1 ≤ X / d := Nat.div_pos hdX hd
  have hNX : X / d ≤ X := Nat.div_le_self X d
  set N := X / d with hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have q1 : (N : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
  have q2 : (X : ℝ) < (d : ℝ) * ((N : ℝ) + 1) := by
    have := Nat.lt_mul_div_succ X (show 0 < d by omega)
    exact_mod_cast this
  have hdN1 : (d : ℝ) * N ≤ X := by
    rw [le_div_iff₀ hd0] at q1; linarith
  have h2dr : 2 * (d : ℝ) ≤ X := by exact_mod_cast h2d
  have hdN2 : (X : ℝ) / 2 ≤ d * N := by nlinarith
  -- bounds on `D`
  have hD1 : Ds β N ≤ Ds β X := Ds_mono hβ0 hβ1 hNX
  have hD2 : Ds β X ≤ Ds β N + (N : ℝ) ^ (-β) - (X : ℝ) ^ (-β) := Ds_diff hβ0 hβ1 hN1 hNX
  have hXb : 0 ≤ (X : ℝ) ^ (-β) := Real.rpow_nonneg hXr.le _
  have hNb : 0 ≤ (N : ℝ) ^ (-β) := Real.rpow_nonneg hNr.le _
  have he1 : (N : ℝ) ^ (1 - β) ≤ ((X : ℝ) / d) ^ (1 - β) := Real.rpow_le_rpow hNr.le q1 hs0.le
  have he2 : ((X : ℝ) / d) ^ (1 - β) ≤ (N : ℝ) ^ (1 - β) + (1 - β) * (N : ℝ) ^ (-β) := by
    have ht := tangent (s := 1 - β) (u := N) (v := (X : ℝ) / d) hs0.le (by linarith) hNr
      (by positivity)
    rw [show (1 - β) - 1 = -β by ring] at ht
    have hlt : (X : ℝ) / d - N ≤ 1 := by
      rw [div_sub' hd0.ne', div_le_iff₀ hd0]; linarith
    have : (1 - β) * (N : ℝ) ^ (-β) * ((X : ℝ) / d - N) ≤ (1 - β) * (N : ℝ) ^ (-β) :=
      mul_le_of_le_one_right (by positivity) hlt
    linarith
  have hH : Hs β N = (N : ℝ) ^ (1 - β) / (1 - β) - Ds β N := by unfold Ds; ring
  set ρ := Hs β N - (((X : ℝ) / d) ^ (1 - β) / (1 - β) - Ds β X) with hρ
  have hρe : ρ = ((N : ℝ) ^ (1 - β) - ((X : ℝ) / d) ^ (1 - β)) / (1 - β)
      + (Ds β X - Ds β N) := by rw [hρ, hH]; ring
  have hq1 : ((N : ℝ) ^ (1 - β) - ((X : ℝ) / d) ^ (1 - β)) / (1 - β) ≤ 0 := by
    rw [div_le_iff₀ hs0]; linarith
  have hq2 : -(N : ℝ) ^ (-β) ≤ ((N : ℝ) ^ (1 - β) - ((X : ℝ) / d) ^ (1 - β)) / (1 - β) := by
    rw [le_div_iff₀ hs0]; linarith
  have habs : |ρ| ≤ (N : ℝ) ^ (-β) := abs_le.2 ⟨by linarith, by linarith⟩
  -- algebra
  have hkey : (d : ℝ) ^ (-β) * ((X : ℝ) / d) ^ (1 - β) = (X : ℝ) ^ (1 - β) / d := by
    rw [rpow_neg_eq hd0, Real.div_rpow hXr.le hd0.le]
    have : 0 < (d : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hd0 _
    field_simp
  have hdβ : (d : ℝ) ^ (-β) = 1 / (d : ℝ) ^ β := by rw [Real.rpow_neg hd0.le, one_div]
  have hHρ : Hs β N = ((X : ℝ) / d) ^ (1 - β) / (1 - β) - Ds β X + ρ := by rw [hρ]; ring
  have hexp : ad * ((d : ℝ) ^ (-β) * Hs β N)
      = (X : ℝ) ^ (1 - β) / (1 - β) * (ad / d) - Ds β X * (ad / (d : ℝ) ^ β)
        + ad * ((d : ℝ) ^ (-β) * ρ) := by
    rw [hHρ]
    linear_combination (ad / (1 - β)) * hkey - ad * Ds β X * hdβ
  have hp : 0 ≤ (d : ℝ) ^ (-β) := Real.rpow_nonneg hd0.le _
  have hpN : (d : ℝ) ^ (-β) * (N : ℝ) ^ (-β) ≤ 2 * (X : ℝ) ^ (1 - β) / X := by
    rw [← Real.mul_rpow hd0.le hNr.le, rpow_neg_eq (by positivity)]
    have h1 : ((d : ℝ) * N) ^ (1 - β) ≤ (X : ℝ) ^ (1 - β) :=
      Real.rpow_le_rpow (by positivity) hdN1 hs0.le
    have hEpos : 0 < (X : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hXr _
    calc ((d : ℝ) * N) ^ (1 - β) / (d * N) ≤ (X : ℝ) ^ (1 - β) / (d * N) := by gcongr
      _ ≤ (X : ℝ) ^ (1 - β) / ((X : ℝ) / 2) := by gcongr
      _ = _ := by field_simp
  have herr : ad * ((d : ℝ) ^ (-β) * ρ) ≤ (d : ℝ) ^ (-β) * (N : ℝ) ^ (-β) := by
    calc ad * ((d : ℝ) ^ (-β) * ρ) ≤ |ad * ((d : ℝ) ^ (-β) * ρ)| := le_abs_self _
      _ = |ad| * ((d : ℝ) ^ (-β) * |ρ|) := by rw [abs_mul, abs_mul, abs_of_nonneg hp]
      _ ≤ 1 * ((d : ℝ) ^ (-β) * (N : ℝ) ^ (-β)) := by gcongr
      _ = _ := one_mul _
  rw [hexp]
  linarith

namespace PintzData

variable {a : ℕ → ℝ} {M : ℝ} {L : ℝ → ℝ}

lemma G_upper (h : PintzData a M L) {β : ℝ} (hβ0 : 19 / 20 ≤ β) (hβ1 : β < 1) {X Y : ℕ}
    (hY : 1 ≤ Y) (hYX : 2 * Y ≤ X) :
    ∑ k ∈ Icc 1 X, (∑ d ∈ k.divisors, a d) * (k : ℝ) ^ (-β)
      ≤ (X : ℝ) ^ (1 - β) / (1 - β) * (L 1 + 6 * M / ((Y : ℝ) + 1))
        + 2 * (X : ℝ) ^ (1 - β) * Y / X := by
  have hβpos : 0 < β := by linarith
  have hs0 : 0 < 1 - β := by linarith
  have hM0 := h.M_nonneg
  have hYX' : Y ≤ X := by omega
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hY1r : (0 : ℝ) < (Y : ℝ) + 1 := by positivity
  have hY1X : ((Y : ℝ) + 1) ≤ X := by exact_mod_cast (show Y + 1 ≤ X by omega)
  set E := (X : ℝ) ^ (1 - β) with hE
  have hEpos : 0 < E := Real.rpow_pos_of_pos hXr _
  -- step A: interchange
  have eA : ∑ k ∈ Icc 1 X, (∑ d ∈ k.divisors, a d) * (k : ℝ) ^ (-β)
      = ∑ d ∈ Icc 1 X, a d * ((d : ℝ) ^ (-β) * Hs β (X / d)) := by
    rw [sum_divisors_interchange a (fun k => (k : ℝ) ^ (-β)) X]
    apply sum_congr rfl; intro d _
    congr 1
    unfold Hs; rw [mul_sum]
    apply sum_congr rfl; intro m _
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [eA, sum_Icc_split _ hYX']
  -- head
  have hhead := sum_le_sum (fun d (hd : d ∈ Icc 1 Y) =>
    head_term hβpos hβ1 (X := X) (d := d) (by simp at hd; omega) (by simp at hd; omega)
      (h.abs_le_one d))
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hhead
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hhead
  set S1 := ∑ d ∈ Icc 1 Y, a d / (d : ℝ)
  set Sβ := ∑ d ∈ Icc 1 Y, a d / (d : ℝ) ^ β
  have ht1 := abs_le.1 (h.tail one_pos Y)
  simp only [Real.rpow_one] at ht1
  have htβ := abs_le.1 (h.tail hβpos Y)
  have hLβ := h.nonneg β hβ0 hβ1
  have hΔ0 := Ds_nonneg hβpos hβ1 X
  have hΔ1 := Ds_le hβpos hβ1 X
  have hYβ : 2 * M / ((Y : ℝ) + 1) ^ β ≤ 2 * M * (E / ((Y : ℝ) + 1)) := by
    have e1 : 1 / ((Y : ℝ) + 1) ^ β = ((Y : ℝ) + 1) ^ (1 - β) / ((Y : ℝ) + 1) := by
      rw [← rpow_neg_eq hY1r, Real.rpow_neg hY1r.le, one_div]
    have h2 : ((Y : ℝ) + 1) ^ (1 - β) ≤ E := Real.rpow_le_rpow hY1r.le hY1X hs0.le
    rw [div_eq_mul_one_div (2 * M), e1]
    gcongr
  set Q := E / ((1 - β) * ((Y : ℝ) + 1)) with hQ
  -- tail
  have hw : ((Y : ℝ) + 1) ^ (-β) * Hs β (X / (Y + 1)) ≤ Q := by
    have h1 := Hs_le hβpos hβ1 (X / (Y + 1))
    have hc : (((X / (Y + 1) : ℕ)) : ℝ) ≤ (X : ℝ) / ((Y : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := X) (n := Y + 1); push_cast at this; exact this
    have h2 : (((X / (Y + 1) : ℕ)) : ℝ) ^ (1 - β) ≤ E / ((Y : ℝ) + 1) ^ (1 - β) := by
      rw [hE, ← Real.div_rpow hXr.le hY1r.le]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hc hs0.le
    have h3 : Hs β (X / (Y + 1)) ≤ E / ((Y : ℝ) + 1) ^ (1 - β) / (1 - β) :=
      h1.trans (by gcongr)
    rw [rpow_neg_eq hY1r]
    have hp : 0 < ((Y : ℝ) + 1) ^ (1 - β) := Real.rpow_pos_of_pos hY1r _
    calc ((Y : ℝ) + 1) ^ (1 - β) / ((Y : ℝ) + 1) * Hs β (X / (Y + 1))
        ≤ ((Y : ℝ) + 1) ^ (1 - β) / ((Y : ℝ) + 1)
            * (E / ((Y : ℝ) + 1) ^ (1 - β) / (1 - β)) := by gcongr
      _ = Q := by rw [hQ]; field_simp
  have htail := h.abel (fun n => (n : ℝ) ^ (-β) * Hs β (X / n)) Y X ?_ ?_ ?_
  rotate_left
  · intro n hn _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply mul_le_mul _ (Hs_mono β (Nat.div_le_div_left (Nat.le_succ n) (by omega)))
      (Hs_nonneg _ _) (Real.rpow_nonneg hn0.le _)
    exact Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith) (by linarith)
  · intro n _ _
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Hs_nonneg _ _)
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Hs_nonneg _ _)
  simp only [Nat.cast_add, Nat.cast_one] at htail
  have htail' := (abs_le.1 htail).2
  have htail2 : 2 * M * (((Y : ℝ) + 1) ^ (-β) * Hs β (X / (Y + 1))) ≤ 2 * M * Q := by gcongr
  -- combine
  have hq1 : E / (1 - β) * (2 * M / ((Y : ℝ) + 1)) = 2 * M * Q := by rw [hQ]; field_simp
  have hq2 : 1 / (1 - β) * (2 * M * (E / ((Y : ℝ) + 1))) = 2 * M * Q := by rw [hQ]; field_simp
  have hq3 : E / (1 - β) * (L 1 + 6 * M / ((Y : ℝ) + 1)) = E / (1 - β) * L 1 + 6 * M * Q := by
    rw [hQ]; field_simp
  have hq4 : (Y : ℝ) * (2 * E / X) = 2 * E * Y / X := by ring
  have hS1' : E / (1 - β) * S1 ≤ E / (1 - β) * (L 1 + 2 * M / ((Y : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hΔa : -(Ds β X * Sβ) ≤ Ds β X * (2 * M / ((Y : ℝ) + 1) ^ β) := by
    have := mul_le_mul_of_nonneg_left (show L β - 2 * M / ((Y : ℝ) + 1) ^ β ≤ Sβ by linarith) hΔ0
    nlinarith [mul_nonneg hΔ0 hLβ]
  have hΔb : Ds β X * (2 * M / ((Y : ℝ) + 1) ^ β) ≤ 1 / (1 - β) * (2 * M * (E / ((Y : ℝ) + 1))) :=
    mul_le_mul hΔ1 hYβ (by positivity) (by positivity)
  rw [hq3]
  nlinarith

lemma G_lower (h : PintzData a M L) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {X : ℕ} (hX : 25 ≤ X) :
    (5269 / 3600 : ℝ) ≤ ∑ k ∈ Icc 1 X, (∑ d ∈ k.divisors, a d) * (k : ℝ) ^ (-β) := by
  have hterm : ∀ j ∈ (Icc 1 5 : Finset ℕ), 1 / ((j : ℝ) ^ 2)
      ≤ (∑ d ∈ (j ^ 2).divisors, a d) * (((j ^ 2 : ℕ) : ℝ)) ^ (-β) := by
    intro j hj
    have hj0 : 0 < j := by simp at hj; omega
    have hg := h.conv_sq j hj0
    have hk : (1 : ℝ) ≤ ((j ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hj0
    have hr : ((j ^ 2 : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((j ^ 2 : ℕ) : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hk (by linarith)
    rw [Real.rpow_neg_one] at hr
    have e : 1 / ((j : ℝ) ^ 2) = (((j ^ 2 : ℕ) : ℝ))⁻¹ := by push_cast; ring
    rw [e]
    have : 0 ≤ ((j ^ 2 : ℕ) : ℝ)⁻¹ := by positivity
    nlinarith
  have hinj : Set.InjOn (fun j : ℕ => j ^ 2) (Icc 1 5 : Finset ℕ) := by
    intro x _ y _ hxy
    exact Nat.pow_left_injective (by norm_num) hxy
  have hsub : (Icc 1 5).image (fun j : ℕ => j ^ 2) ⊆ Icc 1 X := by
    intro k hk
    simp only [mem_image, mem_Icc] at hk ⊢
    obtain ⟨j, ⟨hj1, hj5⟩, rfl⟩ := hk
    exact ⟨Nat.one_le_pow _ _ hj1, (Nat.pow_le_pow_left hj5 2).trans (by omega)⟩
  calc (5269 / 3600 : ℝ) = ∑ j ∈ (Icc 1 5 : Finset ℕ), 1 / ((j : ℝ) ^ 2) := by
        rw [show (Icc 1 5 : Finset ℕ) = {1, 2, 3, 4, 5} by decide]
        simp; norm_num
    _ ≤ ∑ j ∈ Icc 1 5, (∑ d ∈ (j ^ 2).divisors, a d) * (((j ^ 2 : ℕ) : ℝ)) ^ (-β) :=
        sum_le_sum hterm
    _ = ∑ k ∈ (Icc 1 5).image (fun j : ℕ => j ^ 2),
          (∑ d ∈ k.divisors, a d) * (k : ℝ) ^ (-β) := by rw [sum_image hinj]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
        mul_nonneg (h.conv_nonneg k) (Real.rpow_nonneg (Nat.cast_nonneg k) _))

end PintzData

/-- The lower bound `L 1 ≥ 1 / (2 (log M + 16))`. -/
theorem PintzData.one_le {a : ℕ → ℝ} {M : ℝ} {L : ℝ → ℝ} (h : PintzData a M L)
    (hM : 1000000 ≤ M) : 1 / (2 * (Real.log M + 16)) ≤ L 1 := by
  have hM0 : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  set T := Real.log M + 16 with hT
  have hT16 : 16 ≤ T := by linarith
  set Y : ℕ := ⌈1000 * M * T⌉₊ with hYdef
  set X : ℕ := 1000 * Y with hXdef
  have hYlo : 1000 * M * T ≤ (Y : ℝ) := Nat.le_ceil _
  have hYhi : (Y : ℝ) < 1000 * M * T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMT : 16000000 ≤ M * T := by nlinarith
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := by nlinarith
    exact_mod_cast this
  have hXr : (X : ℝ) = 1000 * Y := by simp [hXdef]
  have h2YX : 2 * Y ≤ X := by omega
  have hX25 : 25 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by rw [hXr]; positivity
  -- bounds for `log X`
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hlogX_up : Real.log X ≤ 1.05 * T := by
    have hXle : (X : ℝ) ≤ 1001000 * (M * T) := by rw [hXr]; nlinarith
    have h1 : Real.log X ≤ Real.log 1001000 + Real.log M + Real.log T := by
      calc Real.log X ≤ Real.log (1001000 * (M * T)) := Real.log_le_log hXpos hXle
        _ = _ := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity)
            (by positivity)]
          ring
    have h2 : Real.log 1001000 ≤ 14 := by
      rw [Real.log_le_iff_le_exp (by norm_num), show (14 : ℝ) = ((14 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_nat_mul]
      calc (1001000 : ℝ) ≤ 2.7182818283 ^ 14 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) he1.le 14
    have h3 : Real.log T ≤ T / 20 + 2 := by
      have hl := Real.log_le_sub_one_of_pos (show 0 < T / 20 by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at hl
      have h20 : Real.log 20 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num,
          Real.exp_nat_mul]
        calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) he1.le 3
      linarith
    linarith
  have hlogX_lo : 20 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos, show (20 : ℝ) = ((20 : ℕ) : ℝ) * 1 by norm_num,
      Real.exp_nat_mul]
    calc Real.exp 1 ^ 20 ≤ 2.7182818286 ^ 20 := pow_le_pow_left₀ (by positivity) he2.le 20
      _ ≤ 1000 * (1000 * M * T) := by nlinarith
      _ ≤ X := by rw [hXr]; linarith
  have hlogXpos : 0 < Real.log X := by linarith
  set s := 1 / Real.log X with hs
  have hs0 : 0 < s := by positivity
  have hs20 : s ≤ 1 / 20 := by
    rw [hs]; exact one_div_le_one_div_of_le (by norm_num) hlogX_lo
  have hβ0 : 19 / 20 ≤ 1 - s := by linarith
  have hβ1 : 1 - s < 1 := by linarith
  have hup := h.G_upper hβ0 hβ1 hY1 h2YX
  have hlow := h.G_lower (β := 1 - s) (by linarith) hβ1.le hX25
  have hE : (X : ℝ) ^ (1 - (1 - s)) = Real.exp 1 := by
    rw [sub_sub_cancel, Real.rpow_def_of_pos hXpos, hs]
    congr 1; field_simp
  rw [hE, sub_sub_cancel] at hup
  have hYX' : 2 * Real.exp 1 * Y / X = 2 * Real.exp 1 / 1000 := by
    rw [hXr]; field_simp
  have hEs : Real.exp 1 / s = Real.exp 1 * Real.log X := by rw [hs]; field_simp
  rw [hYX', hEs] at hup
  set P := L 1 + 6 * M / ((Y : ℝ) + 1) with hP
  have hP1 : 1.458 ≤ Real.exp 1 * Real.log X * P := by linarith
  have hPpos : 0 < P := by
    by_contra hneg
    push_neg at hneg
    have : Real.exp 1 * Real.log X * P ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hP2 : Real.exp 1 * Real.log X * P ≤ 2.7182818286 * (1.05 * T) * P := by
    gcongr
  have hTP : 0.51 ≤ T * P := by nlinarith
  have h6 : T * (6 * M / ((Y : ℝ) + 1)) ≤ 0.006 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hTL : 0.504 ≤ T * L 1 := by
    have : T * P = T * L 1 + T * (6 * M / ((Y : ℝ) + 1)) := by rw [hP]; ring
    linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Idoneal
