import Idoneal.Defs

/-!
# Lattice points in an ellipse (blueprint §1 (Lat))

The statement below is the fixed interface. Replace the `sorry`; add private lemmas freely.
Only the reducedness part of `IsAmbiguousForm` is needed.
-/

namespace Idoneal

open Finset Real

/-- Quarter-disc area: `∫₀^R √(R² - t²) dt = π R² / 4`. -/
private lemma integral_quarter_disc (R : ℝ) (hR : 0 ≤ R) :
    ∫ t in (0:ℝ)..R, √(R ^ 2 - t ^ 2) = π * R ^ 2 / 4 := by
  have hc : Continuous (fun x : ℝ => √(1 - x ^ 2)) := by fun_prop
  have h1 : ∫ x in (0:ℝ)..1, √(1 - x ^ 2) = π / 4 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := MeasureTheory.volume) (-1) 0) (hc.intervalIntegrable 0 1)
    have hneg := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1)
      (fun x : ℝ => √(1 - x ^ 2))
    simp only [neg_sq, neg_zero] at hneg
    have := integral_sqrt_one_sub_sq
    linarith
  rcases hR.lt_or_eq with hR0 | hR0
  · have hsub := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
      (fun t : ℝ => √(R ^ 2 - t ^ 2)) hR0.ne'
    have hfun : (fun x : ℝ => √(R ^ 2 - (R * x) ^ 2)) = fun x => R * √(1 - x ^ 2) := by
      funext x
      rw [show R ^ 2 - (R * x) ^ 2 = R ^ 2 * (1 - x ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]
    simp only [hfun, intervalIntegral.integral_const_mul, h1, mul_zero, mul_one,
      smul_eq_mul] at hsub
    field_simp at hsub
    linarith
  · subst hR0; simp

/-- Symmetric sum of an even function over `[-Y, Y]`. -/
private lemma sum_Icc_even (g : ℤ → ℝ) (hg : ∀ y, g (-y) = g y) (Y : ℕ) :
    ∑ y ∈ Icc (-(Y:ℤ)) Y, g y = g 0 + 2 * ∑ k ∈ range Y, g ((k:ℤ) + 1) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    have hset : Icc (-((Y + 1 : ℕ) : ℤ)) ((Y + 1 : ℕ) : ℤ) =
        insert ((Y:ℤ) + 1) (insert (-((Y:ℤ) + 1)) (Icc (-(Y:ℤ)) Y)) := by
      ext z; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_range_succ,
      hg]
    ring

/-- Integers in a real interval `[a, b]`. -/
private lemma card_Icc_ceil_floor (a b : ℝ) (hab : a ≤ b) :
    ((Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b - a + 1 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le b
  have h2 := Int.le_ceil a
  have key : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℤ) : ℝ) ≤ b - a + 1 := by
    rw [Int.toNat_eq_max]; push_cast; apply max_le <;> linarith
  exact_mod_cast key

theorem latticeCount_le {n : ℕ} (hn : 0 < n) {f : ℕ × ℕ × ℕ} (hf : IsAmbiguousForm n f)
    (X : ℕ) :
    (latticeCount f X : ℝ) ≤ Real.pi * X / Real.sqrt n + 5 * Real.sqrt X + 5 := by
  obtain ⟨A, B, C⟩ := f
  obtain ⟨hAC, h2B, hAC', hA, -⟩ := hf
  simp only at hAC h2B hAC' hA
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hAR : (0:ℝ) < A := by exact_mod_cast hA
  set R : ℝ := √(A * X / n) with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = A * X / n := Real.sq_sqrt (by positivity)
  have hnR2 : (n:ℝ) * R ^ 2 = A * X := by rw [hR2]; field_simp
  set Y : ℕ := ⌊R⌋₊ with hYdef
  have hY : (Y:ℝ) ≤ R := Nat.floor_le hR0
  set s : ℤ → ℝ := fun y => √n * √(R ^ 2 - (y:ℝ) ^ 2) with hsdef
  have hs0 : ∀ y, 0 ≤ s y := fun y => by positivity
  set F : ℤ → Finset ℤ := fun y => Icc ⌈(-s y - B * y) / A⌉ ⌊(s y - B * y) / A⌋ with hFdef
  set U : Finset (ℤ × ℤ) := (Icc (-(Y:ℤ)) Y).biUnion (fun y => (F y).image (fun x => (x, y)))
    with hUdef
  -- every admissible point lies in `U`
  have hmem : ∀ v : ℤ × ℤ, formVal (A, B, C) v.1 v.2 ≤ X → v ∈ U := by
    rintro ⟨x, y⟩ h
    have hACz : (A:ℤ) * C = n + B ^ 2 := by exact_mod_cast hAC
    have hid : (A:ℤ) * formVal (A, B, C) x y = (A * x + B * y) ^ 2 + n * y ^ 2 := by
      simp only [formVal]; linear_combination y ^ 2 * hACz
    have hz : (A * x + B * y) ^ 2 + n * y ^ 2 ≤ (A:ℤ) * X := by
      rw [← hid]; exact mul_le_mul_of_nonneg_left h (by positivity)
    have hr : ((A:ℝ) * x + B * y) ^ 2 + n * (y:ℝ) ^ 2 ≤ A * X := by exact_mod_cast hz
    -- bound on `y`
    have hy2 : (y:ℝ) ^ 2 ≤ R ^ 2 := by
      rw [hR2, le_div_iff₀ hnR]; nlinarith [sq_nonneg ((A:ℝ) * x + B * y)]
    have hyabs : |(y:ℝ)| ≤ R := by
      have := Real.abs_le_sqrt hy2; rwa [Real.sqrt_sq hR0] at this
    have hyN : y.natAbs ≤ Y := by
      apply Nat.le_floor; rw [Nat.cast_natAbs]; exact_mod_cast hyabs
    have hyI : y ∈ Icc (-(Y:ℤ)) Y := by rw [mem_Icc]; omega
    -- bound on `x`
    have hx2 : ((A:ℝ) * x + B * y) ^ 2 ≤ n * (R ^ 2 - (y:ℝ) ^ 2) := by nlinarith
    have hxabs : |(A:ℝ) * x + B * y| ≤ s y := by
      have := Real.abs_le_sqrt hx2
      rwa [Real.sqrt_mul hnR.le] at this
    rw [abs_le] at hxabs
    have hxI : x ∈ F y := by
      simp only [hFdef, mem_Icc, Int.ceil_le, Int.le_floor]
      constructor
      · rw [div_le_iff₀ hAR]; linarith
      · rw [le_div_iff₀ hAR]; linarith
    simp only [hUdef, mem_biUnion, mem_image]
    exact ⟨y, hyI, x, hxI, rfl⟩
  have hcard : (latticeCount (A, B, C) X : ℝ) ≤ U.card := by
    have : latticeCount (A, B, C) X ≤ Nat.card U := by
      unfold latticeCount
      refine Nat.card_le_card_of_injective (fun v => ⟨v.1, hmem v.1 v.2.2⟩) ?_
      intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext hab'
    rw [Nat.card_eq_finsetCard] at this
    exact_mod_cast this
  have hU : (U.card : ℝ) ≤ ∑ y ∈ Icc (-(Y:ℤ)) Y, (2 * s y / A + 1) := by
    calc (U.card : ℝ) ≤ ((∑ y ∈ Icc (-(Y:ℤ)) Y, (F y).card : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le.trans (sum_le_sum fun y _ => card_image_le)
      _ = ∑ y ∈ Icc (-(Y:ℤ)) Y, ((F y).card : ℝ) := by push_cast; rfl
      _ ≤ _ := by
          apply sum_le_sum
          intro y _
          have hle : (-s y - B * y) / A ≤ (s y - B * y) / A := by
            apply div_le_div_of_nonneg_right _ hAR.le; linarith [hs0 y]
          have := card_Icc_ceil_floor _ _ hle
          calc ((F y).card : ℝ) ≤ (s y - B * y) / A - (-s y - B * y) / A + 1 := this
            _ = 2 * s y / A + 1 := by field_simp; ring
  have hsum : ∑ y ∈ Icc (-(Y:ℤ)) Y, (2 * s y / A + 1) =
      (2 / A) * (s 0 + 2 * ∑ k ∈ range Y, s ((k:ℤ) + 1)) + (2 * Y + 1) := by
    have heven : ∀ y, s (-y) = s y := fun y => by simp [hsdef]
    rw [sum_add_distrib, sum_const, Int.card_Icc,
      show ∑ y ∈ Icc (-(Y:ℤ)) Y, 2 * s y / A = (2 / A) * ∑ y ∈ Icc (-(Y:ℤ)) Y, s y by
        rw [mul_sum]; congr 1; funext y; ring,
      sum_Icc_even s heven]
    congr 1
    rw [nsmul_eq_mul, mul_one]
    have : ((Y:ℤ) + 1 - -(Y:ℤ)).toNat = 2 * Y + 1 := by omega
    rw [this]; push_cast; ring
  have hint : ∑ k ∈ range Y, s ((k:ℤ) + 1) ≤ √n * (π * R ^ 2 / 4) := by
    set τ : ℝ → ℝ := fun t => √(R ^ 2 - t ^ 2) with hτ
    have hanti : AntitoneOn τ (Set.Icc 0 (0 + (Y:ℝ))) := by
      intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      apply Real.sqrt_le_sqrt
      nlinarith
    have h1 := AntitoneOn.sum_le_integral hanti
    simp only [zero_add] at h1
    have hτc : Continuous τ := by fun_prop
    have h2 : ∫ t in (0:ℝ)..Y, τ t ≤ ∫ t in (0:ℝ)..R, τ t :=
      intervalIntegral.integral_mono_interval le_rfl (Nat.cast_nonneg _) hY
        (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)
        (hτc.intervalIntegrable _ _)
    have h3 := integral_quarter_disc R hR0
    have hrw : ∑ k ∈ range Y, s ((k:ℤ) + 1) = √n * ∑ i ∈ range Y, τ ((i + 1 : ℕ) : ℝ) := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; simp [hsdef, hτ]
    rw [hrw]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [← h3]; exact h1.trans h2
  -- final estimate
  have hsX : 0 ≤ √(X:ℝ) := Real.sqrt_nonneg _
  have hsn : √(n:ℝ) * √(n:ℝ) = n := Real.mul_self_sqrt hnR.le
  have hsnpos : 0 < √(n:ℝ) := Real.sqrt_pos.mpr hnR
  have hsXX : √(X:ℝ) * √(X:ℝ) = X := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs0' : s 0 = √n * R := by simp [hsdef, Real.sqrt_sq hR0]
  -- 3 A ≤ 4 n
  have h3A : 3 * A ≤ 4 * n := by
    have h1 : A * A ≤ A * C := Nat.mul_le_mul_left _ hAC'
    nlinarith
  have h3AR : (3:ℝ) * A ≤ 4 * n := by exact_mod_cast h3A
  have hA1 : (1:ℝ) ≤ A := by exact_mod_cast hA
  -- the three pieces
  have hmain : (2 / A) * (2 * (√n * (π * R ^ 2 / 4))) = π * X / √n := by
    rw [hR2]; field_simp
    have hsn2 : √(n:ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
    linear_combination (4 * (X:ℝ)) * hsn2
  have herr1 : (2 / A) * (√n * R) ≤ 2 * √X := by
    have hsq : (√n * R) ^ 2 = A * X := by rw [mul_pow, Real.sq_sqrt hnR.le, hnR2]
    have hle : √n * R ≤ A * √X := by
      have hpos : 0 ≤ √n * R := by positivity
      rw [← Real.sqrt_sq hpos, hsq, ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ A * √X)]
      apply Real.sqrt_le_sqrt
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have hX0 : (0:ℝ) ≤ X := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hA1 (mul_nonneg hAR.le hX0)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hAR]; nlinarith
  have herr2 : R ≤ 3 / 2 * √X := by
    rw [hRdef, Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      div_le_iff₀ hnR]
    nlinarith [(Nat.cast_nonneg X : (0:ℝ) ≤ X)]
  calc (latticeCount (A, B, C) X : ℝ) ≤ U.card := hcard
    _ ≤ _ := hU
    _ = _ := hsum
    _ ≤ (2 / A) * (√n * R + 2 * (√n * (π * R ^ 2 / 4))) + (2 * R + 1) := by
        rw [hs0']
        gcongr
    _ = (2 / A) * (√n * R) + (2 / A) * (2 * (√n * (π * R ^ 2 / 4))) + (2 * R + 1) := by ring
    _ ≤ 2 * √X + π * X / √n + (2 * (3 / 2 * √X) + 1) := by
        rw [hmain]; gcongr
    _ ≤ π * X / √n + 5 * √X + 5 := by linarith

end Idoneal
