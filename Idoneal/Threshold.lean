import Idoneal.Defs

/-!
# Thresholds (blueprint §1 (T))

The statement below is the fixed interface. Replace the `sorry`; add private lemmas freely.
-/

namespace Idoneal

open Real

/-- Monotonicity step: a check at `N` propagates to all `x ≥ N`. -/
private lemma key (c C N L s : ℝ) (hc : 0 < c) (hcC : c ≤ C) (hN : 0 < N) (h1N : 1 ≤ N) (hs : 0 ≤ s)
    (hsN : s ^ 2 ≤ N) (hL : N ≤ exp L) (h2c : 2 * C ≤ s) (hmain : C * (L + 16) < s)
    (x : ℝ) (hx : N ≤ x) : c * (log x + 16) < sqrt x := by
  have hsqN : s ≤ sqrt N := Real.le_sqrt_of_sq_le hsN
  have hlogN : log N ≤ L := by
    rw [Real.log_le_iff_le_exp hN]; exact hL
  set t := x / N with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hN]; linarith
  have ht0 : 0 < t := by linarith
  have hxt : x = N * t := by rw [ht]; field_simp
  have hst : 1 ≤ sqrt t := by rw [show (1:ℝ) = sqrt 1 by simp]; exact Real.sqrt_le_sqrt ht1
  have hst0 : 0 < sqrt t := by linarith
  have hlogt : log t ≤ 2 * (sqrt t - 1) := by
    have h1 := Real.log_le_sub_one_of_pos hst0
    have h2 : log t = 2 * log (sqrt t) := by
      rw [Real.log_sqrt ht0.le]; ring
    rw [h2]; linarith
  have hlogx : log x = log N + log t := by
    rw [hxt, Real.log_mul hN.ne' ht0.ne']
  have hsqx : sqrt x = sqrt N * sqrt t := by
    rw [hxt, Real.sqrt_mul hN.le]
  rw [hlogx, hsqx]
  have hC : 0 < C := by linarith
  have e1 : c * (log N + log t + 16) ≤ C * (L + 16) + 2 * C * (sqrt t - 1) := by
    have hpos : 0 ≤ log N + log t + 16 := by
      have : 0 ≤ log N := Real.log_nonneg h1N
      have : 0 ≤ log t := Real.log_nonneg ht1
      linarith
    calc c * (log N + log t + 16) ≤ C * (log N + log t + 16) :=
          mul_le_mul_of_nonneg_right hcC hpos
      _ ≤ C * (L + 16 + 2 * (sqrt t - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le; linarith
      _ = _ := by ring
  have e2 : 2 * C * (sqrt t - 1) ≤ s * (sqrt t - 1) :=
    mul_le_mul_of_nonneg_right h2c (by linarith)
  have e3 : s * sqrt t ≤ sqrt N * sqrt t := mul_le_mul_of_nonneg_right hsqN hst0.le
  nlinarith

private lemma exp_ge (m : ℕ) (r : ℝ) (hr : 0 ≤ r) : (2.7 : ℝ) ^ m * (1 + r) ≤ exp (m + r) := by
  rw [Real.exp_add, show (m : ℝ) = m * 1 by ring, Real.exp_nat_mul]
  have h1 : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ m ≤ exp 1 ^ m := pow_le_pow_left₀ (by norm_num) h1.le m
  have h3 : 1 + r ≤ exp r := by linarith [Real.add_one_le_exp r]
  exact mul_le_mul h2 h3 (by linarith) (by positivity)

/-- `P₁₁ = 2·3·5·…·31`. -/
private def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

private lemma lower_bound {n : ℕ} (hsf : Squarefree n) (hk : 11 ≤ n.primeFactors.card) :
    200560490130 * 37 ^ (n.primeFactors.card - 11) ≤ n := by
  set s := n.primeFactors with hs
  have hprod : ∏ p ∈ s, p = n := Nat.prod_primeFactors_of_squarefree hsf
  set t := s.filter (· < 37) with htdef
  set u := s.filter (fun p => ¬ p < 37) with hudef
  have hsplit : (∏ p ∈ t, p) * ∏ p ∈ u, p = ∏ p ∈ s, p :=
    Finset.prod_filter_mul_prod_filter_not s (· < 37) (fun p => p)
  have hcard : t.card + u.card = s.card :=
    Finset.card_filter_add_card_filter_not (· < 37)
  have hu : 37 ^ u.card ≤ ∏ p ∈ u, p := by
    apply Finset.pow_card_le_prod
    intro p hp
    rw [hudef, Finset.mem_filter] at hp
    omega
  have hts : t ⊆ smallPrimes := by
    intro p hp
    rw [htdef, Finset.mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have hlt := hp.2
    interval_cases p <;> first | (simp [smallPrimes]; done) | (norm_num at hpp)
  have htcard : t.card ≤ 11 := by
    have := Finset.card_le_card hts
    simpa [smallPrimes] using this
  -- ∏ t * 37^(11 - |t|) ≥ P₁₁
  have hsmall : 200560490130 ≤ (∏ p ∈ t, p) * 37 ^ (11 - t.card) := by
    have e : ∏ p ∈ smallPrimes, (if p ∈ t then p else 37) =
        (∏ p ∈ t, p) * 37 ^ (11 - t.card) := by
      rw [Finset.prod_ite, Finset.prod_const]
      have h1 : smallPrimes.filter (· ∈ t) = t := by
        ext p; simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hts h, h⟩⟩
      have h2 : (smallPrimes.filter (fun p => ¬ p ∈ t)).card = 11 - t.card := by
        have := Finset.card_filter_add_card_filter_not (s := smallPrimes) (· ∈ t)
        rw [h1] at this
        have h11 : smallPrimes.card = 11 := by decide
        omega
      rw [h1, h2]
    rw [← e]
    have : ∏ p ∈ smallPrimes, p ≤ ∏ p ∈ smallPrimes, (if p ∈ t then p else 37) := by
      apply Finset.prod_le_prod (fun p hp => ?_)
      split_ifs
      · exact le_rfl
      · simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
        omega
    have hP : ∏ p ∈ smallPrimes, p = 200560490130 := by decide
    omega
  have hucard : u.card = (s.card - 11) + (11 - t.card) := by omega
  calc 200560490130 * 37 ^ (s.card - 11)
      ≤ (∏ p ∈ t, p) * 37 ^ (11 - t.card) * 37 ^ (s.card - 11) :=
        Nat.mul_le_mul_right _ hsmall
    _ = (∏ p ∈ t, p) * 37 ^ u.card := by rw [hucard, pow_add]; ring
    _ ≤ (∏ p ∈ t, p) * ∏ p ∈ u, p := Nat.mul_le_mul_left _ hu
    _ = n := by rw [hsplit, hprod]

/-- Induction for `k ≥ 11`. -/
private lemma big (j : ℕ) (x : ℝ) (hx : 200560490130 * 37 ^ j ≤ x) :
    π * 2 ^ (11 + j) * (log x + 16) < sqrt x := by
  induction j generalizing x with
  | zero =>
    simp only [pow_zero, mul_one, add_zero] at hx ⊢
    apply key _ (2048 * 3.15) 200560490130 27 447000 (by positivity)
      (by nlinarith [Real.pi_lt_d2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
      (by norm_num) (by norm_num) x hx
    have := exp_ge 27 0 le_rfl
    norm_num at this ⊢
    linarith
  | succ j ih =>
    set y := x / 37 with hy
    have hxy : x = 37 * y := by rw [hy]; ring
    have hy' : 200560490130 * 37 ^ j ≤ y := by
      rw [hy, le_div_iff₀ (by norm_num)]; rw [pow_succ] at hx; linarith
    have hy0 : 1 ≤ y := by
      have : (1:ℝ) ≤ 200560490130 * 37 ^ j := by
        have : (1:ℝ) ≤ 37 ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      linarith
    have ihy := ih y hy'
    have hlogy : 0 ≤ log y := Real.log_nonneg hy0
    have hlog37 : log 37 < 16 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := exp_ge 16 0 le_rfl
      norm_num at this ⊢
      linarith
    have hlogx : log x = log y + log 37 := by
      rw [hxy, Real.log_mul (by norm_num) (by linarith)]; ring
    have hsqx : sqrt x = sqrt 37 * sqrt y := by rw [hxy, Real.sqrt_mul (by norm_num)]
    have h37 : 4 ≤ sqrt 37 := Real.le_sqrt_of_sq_le (by norm_num)
    have hc : 0 < π * 2 ^ (11 + j) := by positivity
    have hsy : 0 ≤ sqrt y := Real.sqrt_nonneg y
    rw [hlogx, hsqx, show 11 + (j + 1) = (11 + j) + 1 by ring, pow_succ]
    have e1 : π * 2 ^ (11 + j) * log 37 < sqrt y := by
      have : π * 2 ^ (11 + j) * log 37 ≤ π * 2 ^ (11 + j) * (log y + 16) :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
      linarith
    have e2 : 4 * sqrt y ≤ sqrt 37 * sqrt y := mul_le_mul_of_nonneg_right h37 hsy
    nlinarith

theorem threshold {n : ℕ} (hn : 4000000 ≤ n) (hsf : Squarefree n)
    (h : Real.sqrt n ≤ Real.pi * (n.divisors.card : ℝ) * (Real.log n + 16)) :
    (n.primeFactors.card = 5 ∧ n < 13000000) ∨
    (n.primeFactors.card = 6 ∧ n < 50000000) ∨
    (n.primeFactors.card = 7 ∧ n < 210000000) ∨
    (n.primeFactors.card = 8 ∧ n < 900000000) ∨
    (n.primeFactors.card = 9 ∧ n < 3900000000) ∨
    (n.primeFactors.card = 10 ∧ n < 17000000000) := by
  have hn0 : n ≠ 0 := by omega
  set k := n.primeFactors.card with hk
  have hdiv : n.divisors.card = 2 ^ k := by
    rw [Nat.card_divisors hn0, hk, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hsf (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  rw [hdiv] at h
  push_cast at h
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hx : (n : ℝ) = n := rfl
  -- generic contradiction at threshold N with constant C
  have contra : ∀ (C N L s : ℝ), π * 2 ^ k ≤ C → 1 ≤ N → 0 ≤ s → s ^ 2 ≤ N → N ≤ exp L →
      2 * C ≤ s → C * (L + 16) < s → N ≤ (n : ℝ) → False := by
    intro C N L s h1 h2 h3 h4 h5 h6 h7 h8
    have := key (π * 2 ^ k) C N L s (by positivity) h1 (by linarith) h2 h3 h4 h5 h6 h7 n h8
    linarith
  have e := fun m r hr => exp_ge m r hr
  have hnR : (4000000 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hk4 : k ≤ 4
  · exfalso
    have h2k : (2:ℝ) ^ k ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hk4
    refine contra (16 * 3.15) 4000000 16 2000 (by nlinarith) (by norm_num) (by norm_num)
      (by norm_num) ?_ (by norm_num) (by norm_num) hnR
    have := e 16 0 le_rfl; norm_num at this ⊢; linarith
  by_cases hk10 : k ≤ 10
  · have hk' : k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
    rcases hk' with hk' | hk' | hk' | hk' | hk' | hk' <;> rw [hk'] <;> simp only [true_and]
    · left
      by_contra hc; push Not at hc
      have hc' : (13000000 : ℝ) ≤ n := by exact_mod_cast hc
      refine contra (32 * 3.15) 13000000 17 3605 (by rw [hk']; nlinarith) (by norm_num)
        (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) hc'
      have := e 17 0 le_rfl; norm_num at this ⊢; linarith
    · right; left
      by_contra hc; push Not at hc
      have hc' : (50000000 : ℝ) ≤ n := by exact_mod_cast hc
      refine contra (64 * 3.15) 50000000 18 7071 (by rw [hk']; nlinarith) (by norm_num)
        (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) hc'
      have := e 18 0 le_rfl; norm_num at this ⊢; linarith
    · right; right; left
      by_contra hc; push Not at hc
      have hc' : (210000000 : ℝ) ≤ n := by exact_mod_cast hc
      refine contra (128 * 3.15) 210000000 (19 + 1/2) 14491 (by rw [hk']; nlinarith)
        (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) hc'
      have := e 19 (1/2) (by norm_num); norm_num at this ⊢; linarith
    · right; right; right; left
      by_contra hc; push Not at hc
      have hc' : (900000000 : ℝ) ≤ n := by exact_mod_cast hc
      refine contra (256 * 3.15) 900000000 21 30000 (by rw [hk']; nlinarith) (by norm_num)
        (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) hc'
      have := e 21 0 le_rfl; norm_num at this ⊢; linarith
    · right; right; right; right; left
      by_contra hc; push Not at hc
      have hc' : (3900000000 : ℝ) ≤ n := by exact_mod_cast hc
      refine contra (512 * 3.15) 3900000000 (22 + 1/2) 62449 (by rw [hk']; nlinarith)
        (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) hc'
      have := e 22 (1/2) (by norm_num); norm_num at this ⊢; linarith
    · right; right; right; right; right
      by_contra hc; push Not at hc
      have hc' : (17000000000 : ℝ) ≤ n := by exact_mod_cast hc
      refine contra (1024 * 3.15) 17000000000 24 130384 (by rw [hk']; nlinarith) (by norm_num)
        (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) hc'
      have := e 24 0 le_rfl; norm_num at this ⊢; linarith
  · exfalso
    have hk11 : 11 ≤ k := by omega
    have hlb := lower_bound hsf hk11
    rw [← hk] at hlb
    have hlbR : (200560490130 : ℝ) * 37 ^ (k - 11) ≤ n := by exact_mod_cast hlb
    have := big (k - 11) n hlbR
    rw [show 11 + (k - 11) = k by omega] at this
    linarith

end Idoneal
