import Idoneal.Defs

/-!
# Binary quadratic forms of determinant `n` (blueprint §1 (F))

Statements below are the fixed interface. Replace each `sorry`; add private lemmas freely.
-/

namespace Idoneal

theorem mem_ambiguousForms {n : ℕ} (hn : 0 < n) (f : ℕ × ℕ × ℕ) :
    f ∈ ambiguousForms n ↔ IsAmbiguousForm n f := by
  obtain ⟨A, B, C⟩ := f
  simp only [ambiguousForms, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  rintro ⟨h1, h2, h3, h4, -⟩
  simp only at h1 h2 h3 h4
  have hA2 : A * A ≤ A * C := Nat.mul_le_mul_left _ h3
  have hB : 4 * B ^ 2 ≤ A * A := by nlinarith
  have hA : A ≤ n + 1 := by nlinarith
  refine ⟨by omega, by omega, ?_⟩
  have hC : C ≤ A * C := Nat.le_mul_of_pos_left _ h4
  nlinarith

/-- Map from ambiguous forms to divisors. -/
private def divMap (f : ℕ × ℕ × ℕ) : ℕ :=
  if f.2.1 = 0 then f.1 else if 2 * f.2.1 = f.1 then 2 * f.2.2 - f.2.1 else f.1 + f.2.1

/-- Its left inverse. -/
private def divInv (n v : ℕ) : ℕ × ℕ × ℕ :=
  if v * v ≤ n then (v, 0, n / v)
  else if 3 * (n / v) ≤ v then (2 * (n / v), n / v, (v + n / v) / 2)
  else ((n / v + v) / 2, (v - n / v) / 2, (n / v + v) / 2)

private lemma divMap_spec {n : ℕ} (_hn : 0 < n) {f : ℕ × ℕ × ℕ} (hf : IsAmbiguousForm n f) :
    divMap f ∣ n ∧ divInv n (divMap f) = f := by
  obtain ⟨A, B, C⟩ := f
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf
  simp only at h1 h2 h3 h4 h5
  by_cases hB : B = 0
  · subst hB
    have hdm : divMap (A, 0, C) = A := by simp [divMap]
    rw [hdm]
    have hn' : n = A * C := by simpa using h1.symm
    refine ⟨⟨C, hn'⟩, ?_⟩
    have hAA : A * A ≤ n := by rw [hn']; exact Nat.mul_le_mul_left _ h3
    have hd : n / A = C := by rw [hn']; exact Nat.mul_div_cancel_left C h4
    simp [divInv, hAA, hd]
  by_cases hAB : 2 * B = A
  · subst hAB
    have hdm : divMap (2 * B, B, C) = 2 * C - B := by simp [divMap, hB]
    rw [hdm]
    obtain ⟨v, hv⟩ : ∃ v, 2 * C = v + B := ⟨2 * C - B, by omega⟩
    have hv' : 2 * C - B = v := by omega
    rw [hv']
    have hBv : n = B * v := by nlinarith
    have hBpos : 0 < B := Nat.pos_of_ne_zero hB
    have hvpos : 0 < v := by omega
    refine ⟨⟨B, by rw [hBv, mul_comm]⟩, ?_⟩
    have hd : n / v = B := by rw [hBv]; exact Nat.mul_div_cancel B hvpos
    have h3v : 3 * B ≤ v := by omega
    have hvv : ¬ v * v ≤ n := by rw [hBv]; intro h; nlinarith
    simp only [divInv, hvv, ite_false, hd, h3v, ite_true]
    ext <;> simp <;> omega
  · have hAC : A = C := by omega
    subst hAC
    have hdm : divMap (A, B, A) = A + B := by simp [divMap, hB, hAB]
    rw [hdm]
    have hBpos : 0 < B := Nat.pos_of_ne_zero hB
    obtain ⟨u, hu⟩ : ∃ u, A = u + B := ⟨A - B, by omega⟩
    subst hu
    have hn' : n = u * (u + B + B) := by nlinarith
    have hvpos : 0 < u + B + B := by omega
    refine ⟨⟨u, by rw [hn', mul_comm]⟩, ?_⟩
    have hd : n / (u + B + B) = u := by rw [hn']; exact Nat.mul_div_cancel u hvpos
    have h3v : ¬ 3 * u ≤ u + B + B := by omega
    have hvv : ¬ (u + B + B) * (u + B + B) ≤ n := by
      rw [hn']; intro h; nlinarith
    simp only [divInv, hvv, ite_false, hd, h3v]
    ext <;> simp <;> omega

theorem card_ambiguousForms_le {n : ℕ} (hn : 0 < n) :
    (ambiguousForms n).card ≤ n.divisors.card := by
  apply Finset.card_le_card_of_injOn divMap
  · intro f hf
    have hf' := (mem_ambiguousForms hn f).mp hf
    simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨(divMap_spec hn hf').1, hn.ne'⟩
  · intro f hf g hg hfg
    have hf' := (mem_ambiguousForms hn f).mp hf
    have hg' := (mem_ambiguousForms hn g).mp hg
    rw [← (divMap_spec hn hf').2, ← (divMap_spec hn hg').2, hfg]


/-! ### The `SL₂(ℤ)` action on integer forms -/

/-- Substitution `(x, y) ↦ (p x + q y, r x + s y)` applied to the form `f = (a, b, c)`. -/
private def act (f : ℤ × ℤ × ℤ) (p q r s : ℤ) : ℤ × ℤ × ℤ :=
  (f.1 * p ^ 2 + 2 * f.2.1 * p * r + f.2.2 * r ^ 2,
   f.1 * p * q + f.2.1 * (p * s + q * r) + f.2.2 * r * s,
   f.1 * q ^ 2 + 2 * f.2.1 * q * s + f.2.2 * s ^ 2)

private lemma act_act (f : ℤ × ℤ × ℤ) (p q r s p' q' r' s' : ℤ) :
    act (act f p q r s) p' q' r' s' =
      act f (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  obtain ⟨a, b, c⟩ := f
  simp only [act, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Cast of a natural triple. -/
private def castF (F : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ := ((F.1 : ℤ), (F.2.1 : ℤ), (F.2.2 : ℤ))

private lemma formVal_eq_act (F : ℕ × ℕ × ℕ) (p q r s : ℤ) :
    formVal F p r = (act (castF F) p q r s).1 := by
  simp [formVal, act, castF]

/-- `f` is equivalent to an ambiguous form. -/
private def Rep (n : ℕ) (f : ℤ × ℤ × ℤ) : Prop :=
  ∃ F, IsAmbiguousForm n F ∧ ∃ p q r s : ℤ, p * s - q * r = 1 ∧ f = act (castF F) p q r s

private lemma Rep.of_act {n : ℕ} {g f : ℤ × ℤ × ℤ} (hg : Rep n g) {p q r s : ℤ}
    (hd : p * s - q * r = 1) (hf : f = act g p q r s) : Rep n f := by
  obtain ⟨F, hF, p', q', r', s', hd', rfl⟩ := hg
  refine ⟨F, hF, _, _, _, _, ?_, hf.trans (act_act _ _ _ _ _ _ _ _ _)⟩
  rw [show (p' * p + q' * r) * (r' * q + s' * s) - (p' * q + q' * s) * (r' * p + s' * r) =
    (p' * s' - q' * r') * (p * s - q * r) by ring, hd, hd', one_mul]

private lemma rep_nonneg {n : ℕ} {a b c : ℤ} (ha : 0 < a) (hb : 0 ≤ b) (h2b : 2 * b ≤ a) (hac : a ≤ c)
    (hdet : a * c - b ^ 2 = n) (h : b = 0 ∨ 2 * b = a ∨ a = c) : Rep n (a, b, c) := by
  lift a to ℕ using ha.le
  lift b to ℕ using hb
  lift c to ℕ using (ha.le.trans hac)
  refine ⟨(a, b, c), ⟨?_, ?_, ?_, ?_, ?_⟩, 1, 0, 0, 1, by norm_num, by simp [act, castF]⟩
  · simp only; exact_mod_cast (by linarith : (a : ℤ) * c = n + b ^ 2)
  · simp only; exact_mod_cast h2b
  · simp only; exact_mod_cast hac
  · simp only; exact_mod_cast ha
  · simp only; exact_mod_cast h

private lemma rep_reduced {n : ℕ} (hns : ¬ HasStrictForm n) {a b c : ℤ} (ha : 0 < a)
    (h2b : -a ≤ 2 * b) (h2b' : 2 * b ≤ a) (hac : a ≤ c)
    (hdet : a * c - b ^ 2 = n) : Rep n (a, b, c) := by
  have htri : b = 0 ∨ 2 * b = a ∨ 2 * b = -a ∨ a = c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    apply hns
    refine ⟨a.toNat, b.natAbs, c.toNat, by omega, by omega, by omega, ?_⟩
    have hc : 0 ≤ c := by linarith
    have : ((a.toNat * c.toNat : ℕ) : ℤ) = ((n + b.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hc, sq_abs]
      linarith
    exact_mod_cast this
  rcases le_or_gt 0 b with hb | hb
  · exact rep_nonneg ha hb (by linarith) hac hdet (by omega)
  · rcases htri with h | h | h | h
    · omega
    · omega
    · -- `a = -2 b`: translate
      have hg : Rep n (a, -b, c) :=
        rep_nonneg ha (by linarith) (by linarith) hac (by linarith) (Or.inr (Or.inl (by linarith)))
      refine hg.of_act (p := 1) (q := -1) (r := 0) (s := 1) (by norm_num) ?_
      simp only [act, Prod.mk.injEq]
      refine ⟨by ring, by linear_combination h, by linear_combination (-1 : ℤ) * h⟩
    · subst h
      have hg : Rep n (a, -b, a) :=
        rep_nonneg ha (by linarith) (by linarith) le_rfl (by linarith) (Or.inr (Or.inr rfl))
      refine hg.of_act (p := 0) (q := 1) (r := -1) (s := 0) (by norm_num) ?_
      simp only [act, Prod.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩

private lemma rep_all {n : ℕ} (hn : 0 < n) (hns : ¬ HasStrictForm n) :
    ∀ N : ℕ, ∀ a b c : ℤ, 0 < a → a ≤ N → a * c - b ^ 2 = n → Rep n (a, b, c) := by
  intro N
  induction N with
  | zero => intro a b c ha haN; push_cast at haN; omega
  | succ N ih =>
    intro a b c ha haN hdet
    -- translate to get `-a ≤ 2 b' ≤ a`
    obtain ⟨u, hu1, hu2⟩ : ∃ u : ℤ, -a ≤ 2 * (b + a * u) ∧ 2 * (b + a * u) ≤ a := by
      have h0 := Int.emod_nonneg b ha.ne'
      have h1 := Int.emod_lt_of_pos b ha
      have h2 := Int.emod_add_mul_ediv b a
      by_cases h : 2 * (b % a) ≤ a
      · exact ⟨-(b / a), by nlinarith, by nlinarith⟩
      · exact ⟨-(b / a) - 1, by nlinarith, by nlinarith⟩
    set b' := b + a * u with hb'
    set c' := a * u ^ 2 + 2 * b * u + c with hc'
    have hdet' : a * c' - b' ^ 2 = n := by rw [hb', hc']; linear_combination hdet
    have hg : Rep n (a, b', c') := by
      rcases le_or_gt a c' with hac | hac
      · exact rep_reduced hns ha hu1 hu2 hac hdet'
      · have hc'pos : 0 < c' := by
          by_contra hneg
          push_neg at hneg
          have : a * c' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hneg
          have : (0 : ℤ) < n := by exact_mod_cast hn
          nlinarith
        have hg' : Rep n (c', -b', a) :=
          ih c' (-b') a hc'pos (by push_cast at haN ⊢; linarith) (by linear_combination hdet')
        refine hg'.of_act (p := 0) (q := 1) (r := -1) (s := 0) (by norm_num) ?_
        simp only [act, Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩
    refine hg.of_act (p := 1) (q := -u) (r := 0) (s := 1) (by norm_num) ?_
    simp only [act, Prod.mk.injEq, hb', hc']
    refine ⟨by ring, by ring, by ring⟩

private lemma rep_of_div {n : ℕ} (hn : 0 < n) (hns : ¬ HasStrictForm n) {m b : ℕ} (hm : 0 < m)
    (hmb : m ∣ b ^ 2 + n) :
    ∃ F, IsAmbiguousForm n F ∧ ∃ p q r s : ℤ, p * s - q * r = 1 ∧
      (act (castF F) p q r s).1 = m ∧ (act (castF F) p q r s).2.1 = b := by
  obtain ⟨c, hc⟩ := hmb
  obtain ⟨F, hF, p, q, r, s, hd, he⟩ :=
    rep_all hn hns m (m : ℤ) b c (by exact_mod_cast hm) le_rfl
      (by have : ((b ^ 2 + n : ℕ) : ℤ) = ((m * c : ℕ) : ℤ) := by rw [hc]
          push_cast at this; linarith)
  exact ⟨F, hF, p, q, r, s, hd, by rw [← he], by rw [← he]⟩


/-! ### Uniqueness of the middle coefficient modulo the first one -/

private lemma mid_congr (f : ℤ × ℤ × ℤ) (p q r s q' s' : ℤ) (h : p * s - q * r = 1)
    (h' : p * s' - q' * r = 1) :
    ∃ t, (act f p q' r s').2.1 = (act f p q r s).2.1 + t * (act f p q r s).1 := by
  set t := (q' - q) * s - (s' - s) * q with ht
  have hq : q' = q + t * p := by rw [ht]; linear_combination (-(q' - q)) * h + q * (h' - h)
  have hs : s' = s + t * r := by rw [ht]; linear_combination (-(s' - s)) * h + s * (h' - h)
  refine ⟨t, ?_⟩
  rw [hq, hs]
  obtain ⟨a, b, c⟩ := f
  simp only [act]
  ring

/-- The data chosen for a pair `(m, b)`: an ambiguous form and a matrix of determinant one
carrying it to a form with first coefficient `m` and middle coefficient `b`. -/
private def Good (n m b : ℕ) (x : (ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ × ℤ)) : Prop :=
  IsAmbiguousForm n x.1 ∧ x.2.1 * x.2.2.2.2 - x.2.2.1 * x.2.2.2.1 = 1 ∧
    (act (castF x.1) x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1 = m ∧
    (act (castF x.1) x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2.1 = b

private lemma eps_sq {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

private lemma key {n m1 m2 b1 b2 e1 e2 : ℕ} {x1 x2 : (ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ × ℤ)} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (he1 : 0 < e1) (hb1 : b1 < m1) (hb2 : b2 < m2)
    (h1 : Good n m1 b1 x1) (h2 : Good n m2 b2 x2) (hF : x1.1 = x2.1)
    (hx : (e1 : ℤ) * x1.2.1 = ε * ((e2 : ℤ) * x2.2.1))
    (hy : (e1 : ℤ) * x1.2.2.2.1 = ε * ((e2 : ℤ) * x2.2.2.2.1)) :
    e1 = e2 ∧ m1 = m2 ∧ b1 = b2 := by
  obtain ⟨F1, p1, q1, r1, s1⟩ := x1
  obtain ⟨F2, p2, q2, r2, s2⟩ := x2
  obtain ⟨-, hd1, hv1, hm1⟩ := h1
  obtain ⟨-, hd2, hv2, hm2⟩ := h2
  simp only at hF hx hy hd1 hd2 hv1 hv2 hm1 hm2
  subst hF
  have hε2 := eps_sq hε
  have g1 : Int.gcd ((e1 : ℤ) * p1) ((e1 : ℤ) * r1) = e1 := by
    rw [Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp ⟨s1, -q1, by linear_combination hd1⟩]
    simp
  have g2 : Int.gcd (ε * ((e2 : ℤ) * p2)) (ε * ((e2 : ℤ) * r2)) = e2 := by
    rw [← mul_assoc, ← mul_assoc, Int.gcd_mul_left,
      Int.isCoprime_iff_gcd_eq_one.mp ⟨s2, -q2, by linear_combination hd2⟩]
    rcases hε with rfl | rfl <;> simp
  have hee : e1 = e2 := by rw [← g1, ← g2, hx, hy]
  subst hee
  have he0 : (e1 : ℤ) ≠ 0 := by exact_mod_cast he1.ne'
  have hp : p1 = ε * p2 := mul_left_cancel₀ he0 (by rw [hx]; ring)
  have hr : r1 = ε * r2 := mul_left_cancel₀ he0 (by rw [hy]; ring)
  subst hp hr
  obtain ⟨A, B, C⟩ := F1
  have hm : (m1 : ℤ) = m2 := by
    rw [← hv1, ← hv2]
    simp only [act, castF]
    linear_combination ((A : ℤ) * p2 ^ 2 + 2 * (B : ℤ) * p2 * r2 + (C : ℤ) * r2 ^ 2) * hε2
  have hm' : m1 = m2 := by exact_mod_cast hm
  subst hm'
  obtain ⟨t, ht⟩ := mid_congr (castF (A, B, C)) (ε * p2) (ε * q2) (ε * r2) (ε * s2) q1 s1
    (by linear_combination hd2 + (p2 * s2 - q2 * r2) * hε2 - hd2 * 0) hd1
  have hmid : (act (castF (A, B, C)) (ε * p2) (ε * q2) (ε * r2) (ε * s2)).2.1 = b2 := by
    rw [← hm2]
    simp only [act, castF]
    linear_combination ((A : ℤ) * p2 * q2 + (B : ℤ) * (p2 * s2 + q2 * r2) +
      (C : ℤ) * r2 * s2) * hε2
  have hfirst : (act (castF (A, B, C)) (ε * p2) (ε * q2) (ε * r2) (ε * s2)).1 = m1 := by
    rw [← hv1]; simp [act, castF]
  rw [hm1, hmid, hfirst] at ht
  refine ⟨rfl, rfl, ?_⟩
  have hb1' : (b1 : ℤ) < m1 := by exact_mod_cast hb1
  have hb2' : (b2 : ℤ) < m1 := by exact_mod_cast hb2
  have hb10 : (0 : ℤ) ≤ b1 := by positivity
  have hb20 : (0 : ℤ) ≤ b2 := by positivity
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with h | h | h
    · have : t * (m1 : ℤ) ≤ -m1 := by nlinarith
      linarith
    · exact h
    · have : t * (m1 : ℤ) ≥ m1 := by nlinarith
      linarith
  rw [ht0] at ht
  exact_mod_cast (by linarith : (b1 : ℤ) = b2)

/-! ### Finiteness of lattice point sets -/

private lemma formVal_two_ge {n : ℕ} {F : ℕ × ℕ × ℕ} (hF : IsAmbiguousForm n F) (x y : ℤ) :
    x ^ 2 + y ^ 2 ≤ 2 * formVal F x y := by
  obtain ⟨A, B, C⟩ := F
  obtain ⟨-, h2, h3, h4, -⟩ := hF
  simp only at h2 h3 h4
  have h2' : 2 * (B : ℤ) ≤ A := by exact_mod_cast h2
  have h3' : (A : ℤ) ≤ C := by exact_mod_cast h3
  have h4' : (1 : ℤ) ≤ A := by exact_mod_cast h4
  have hB : (0 : ℤ) ≤ B := by positivity
  simp only [formVal]
  nlinarith [mul_nonneg hB (sq_nonneg (x + y)), sq_nonneg x, sq_nonneg y,
    mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * A - 2 * B - 1) (sq_nonneg x),
    mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * C - 2 * B - 1) (sq_nonneg y)]

/-- The box containing all points of height `≤ X` of a reduced form. -/
private def box (X : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(2 * (X : ℤ))) (2 * X) ×ˢ Finset.Icc (-(2 * (X : ℤ))) (2 * X)

private lemma int_bound {x X : ℤ} (hX : 0 ≤ X) (h : x ^ 2 ≤ 2 * X) : -(2 * X) ≤ x ∧ x ≤ 2 * X := by
  constructor
  · by_contra hc; push_neg at hc; nlinarith
  · by_contra hc; push_neg at hc; nlinarith

private lemma mem_box {n X : ℕ} {F : ℕ × ℕ × ℕ} (hF : IsAmbiguousForm n F) {x y : ℤ}
    (h : formVal F x y ≤ X) : (x, y) ∈ box X := by
  have h1 := formVal_two_ge hF x y
  have hX : (0 : ℤ) ≤ X := by positivity
  have hx := int_bound hX (by nlinarith [sq_nonneg y] : x ^ 2 ≤ 2 * (X : ℤ))
  have hy := int_bound hX (by nlinarith [sq_nonneg x] : y ^ 2 ≤ 2 * (X : ℤ))
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  exact ⟨hx, hy⟩

private lemma latticeCount_eq {n X : ℕ} {F : ℕ × ℕ × ℕ} (hF : IsAmbiguousForm n F) :
    latticeCount F X =
      ((box X).filter (fun v : ℤ × ℤ => v ≠ 0 ∧ formVal F v.1 v.2 ≤ X)).card := by
  unfold latticeCount
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun v => ?_)
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨mem_box hF h2, h1, h2⟩
  · rintro ⟨-, h⟩; exact h

theorem two_mul_sum_rho_le_lattice {n : ℕ} (hn : 0 < n) (hns : ¬ HasStrictForm n) (X : ℕ) :
    2 * ∑ k ∈ Finset.Icc 1 X,
        ∑ e ∈ (Finset.Icc 1 k).filter (fun e => e ^ 2 ∣ k), rho n (k / e ^ 2)
      ≤ ∑ f ∈ ambiguousForms n, latticeCount f X := by
  classical
  have hex : ∀ m b : ℕ, ∃ x : (ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ × ℤ),
      0 < m → m ∣ b ^ 2 + n → Good n m b x := by
    intro m b
    by_cases h : 0 < m ∧ m ∣ b ^ 2 + n
    · obtain ⟨F, hF, p, q, r, s, hd, h1, h2⟩ := rep_of_div hn hns h.1 h.2
      exact ⟨(F, p, q, r, s), fun _ _ => ⟨hF, hd, h1, h2⟩⟩
    · exact ⟨default, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using hex
  set T : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) := (Finset.Icc 1 X).sigma (fun k =>
    ((Finset.Icc 1 k).filter (fun e => e ^ 2 ∣ k)).sigma (fun e =>
      (Finset.range (k / e ^ 2)).filter (fun b => k / e ^ 2 ∣ b ^ 2 + n))) with hTdef
  have hT : ∑ k ∈ Finset.Icc 1 X,
        ∑ e ∈ (Finset.Icc 1 k).filter (fun e => e ^ 2 ∣ k), rho n (k / e ^ 2) = T.card := by
    rw [hTdef, Finset.card_sigma]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.card_sigma]
    rfl
  set W : Finset (Σ _ : ℕ × ℕ × ℕ, ℤ × ℤ) := (ambiguousForms n).sigma (fun F =>
    (box X).filter (fun v : ℤ × ℤ => v ≠ 0 ∧ formVal F v.1 v.2 ≤ X)) with hWdef
  have hW : ∑ f ∈ ambiguousForms n, latticeCount f X = W.card := by
    rw [hWdef, Finset.card_sigma]
    exact Finset.sum_congr rfl (fun F hF => latticeCount_eq ((mem_ambiguousForms hn F).mp hF))
  -- the data attached to an element of `T`
  have hdata : ∀ t ∈ T, 0 < t.2.1 ∧ t.2.2 < t.1 / t.2.1 ^ 2 ∧
      t.2.1 ^ 2 * (t.1 / t.2.1 ^ 2) = t.1 ∧ t.1 ≤ X ∧
      Good n (t.1 / t.2.1 ^ 2) t.2.2 (g (t.1 / t.2.1 ^ 2) t.2.2) := by
    rintro ⟨k, e, b⟩ ht
    simp only [hTdef, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_range] at ht
    obtain ⟨⟨-, hkX⟩, ⟨⟨he, -⟩, hek⟩, hb, hmb⟩ := ht
    exact ⟨he, hb, Nat.mul_div_cancel' hek, hkX, hg _ _ (by dsimp only; omega) hmb⟩
  let Φ : ℤ → (Σ _ : ℕ, Σ _ : ℕ, ℕ) → (Σ _ : ℕ × ℕ × ℕ, ℤ × ℤ) := fun ε t =>
    ⟨(g (t.1 / t.2.1 ^ 2) t.2.2).1,
      (ε * ((t.2.1 : ℤ) * (g (t.1 / t.2.1 ^ 2) t.2.2).2.1),
       ε * ((t.2.1 : ℤ) * (g (t.1 / t.2.1 ^ 2) t.2.2).2.2.2.1))⟩
  -- main uniqueness: `Φ ε₁ t₁ = Φ ε₂ t₂` forces `t₁ = t₂` and `ε₁ = ε₂`
  have huniq : ∀ ε1 ε2 : ℤ, (ε1 = 1 ∨ ε1 = -1) → (ε2 = 1 ∨ ε2 = -1) →
      ∀ t1 ∈ T, ∀ t2 ∈ T, Φ ε1 t1 = Φ ε2 t2 → t1 = t2 ∧ ε1 = ε2 := by
    intro ε1 ε2 hε1 hε2 t1 ht1 t2 ht2 heq
    obtain ⟨he1, hb1, hk1, -, hG1⟩ := hdata t1 ht1
    obtain ⟨he2, hb2, hk2, -, hG2⟩ := hdata t2 ht2
    simp only [Φ, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at heq
    obtain ⟨hF, hx, hy⟩ := heq
    have hε1sq := eps_sq hε1
    have hε : ε1 * ε2 = 1 ∨ ε1 * ε2 = -1 := by
      rcases hε1 with rfl | rfl <;> rcases hε2 with rfl | rfl <;> norm_num
    obtain ⟨he, hm, hb⟩ := key (e2 := t2.2.1) hε he1 hb1 hb2 hG1 hG2 hF
      (by linear_combination ε1 * hx - ((t1.2.1 : ℤ) * (g (t1.1 / t1.2.1 ^ 2) t1.2.2).2.1) * hε1sq)
      (by linear_combination ε1 * hy -
        ((t1.2.1 : ℤ) * (g (t1.1 / t1.2.1 ^ 2) t1.2.2).2.2.2.1) * hε1sq)
    obtain ⟨k1, e1, b1⟩ := t1
    obtain ⟨k2, e2, b2⟩ := t2
    simp only at he hm hb hk1 hk2 hx hy he1 hG1
    subst he hb
    have hk : k1 = k2 := by rw [← hk1, ← hk2, hm]
    subst hk
    refine ⟨rfl, ?_⟩
    -- now `ε1 * (e p) = ε2 * (e p)` and the same for `r`; `(p, r) ≠ 0`
    obtain ⟨-, hd, -, -⟩ := hG1
    have he0 : (e1 : ℤ) ≠ 0 := by exact_mod_cast he1.ne'
    set x := g (k1 / e1 ^ 2) b1 with hxdef
    by_contra hne
    have hsub : ε1 - ε2 ≠ 0 := sub_ne_zero.mpr hne
    have hp : x.2.1 = 0 := by
      have : (ε1 - ε2) * ((e1 : ℤ) * x.2.1) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hsub
      · exact (mul_eq_zero.mp h).resolve_left he0
    have hr : x.2.2.2.1 = 0 := by
      have : (ε1 - ε2) * ((e1 : ℤ) * x.2.2.2.1) = 0 := by linear_combination hy
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hsub
      · exact (mul_eq_zero.mp h).resolve_left he0
    rw [hp, hr] at hd
    simp at hd
  have hinj : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → Set.InjOn (Φ ε) T := fun ε hε t1 ht1 t2 ht2 h =>
    (huniq ε ε hε hε t1 ht1 t2 ht2 h).1
  have hmaps : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ∀ t ∈ T, Φ ε t ∈ W := by
    intro ε hε t ht
    obtain ⟨he, hb, hk, hkX, hG⟩ := hdata t ht
    obtain ⟨hA, hd, hv, -⟩ := hG
    have hε2 := eps_sq hε
    set x := g (t.1 / t.2.1 ^ 2) t.2.2 with hxdef
    simp only [Φ, hWdef, Finset.mem_sigma, Finset.mem_filter]
    have hval : formVal x.1 (ε * ((t.2.1 : ℤ) * x.2.1)) (ε * ((t.2.1 : ℤ) * x.2.2.2.1)) =
        (t.1 : ℤ) := by
      have h1 : formVal x.1 (ε * ((t.2.1 : ℤ) * x.2.1)) (ε * ((t.2.1 : ℤ) * x.2.2.2.1)) =
          (t.2.1 : ℤ) ^ 2 * formVal x.1 x.2.1 x.2.2.2.1 := by
        simp only [formVal]
        linear_combination ((t.2.1 : ℤ) ^ 2 * ((x.1.1 : ℤ) * x.2.1 ^ 2 + 2 * (x.1.2.1 : ℤ) * x.2.1 * x.2.2.2.1 + (x.1.2.2 : ℤ) * x.2.2.2.1 ^ 2)) * hε2
      rw [h1, formVal_eq_act x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, hv]
      exact_mod_cast hk
    have hle : formVal x.1 (ε * ((t.2.1 : ℤ) * x.2.1)) (ε * ((t.2.1 : ℤ) * x.2.2.2.1)) ≤ X := by
      rw [hval]; exact_mod_cast hkX
    refine ⟨(mem_ambiguousForms hn _).mpr hA, mem_box hA hle, ?_, hle⟩
    intro h0
    simp only [Prod.mk_eq_zero, mul_eq_zero] at h0
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have he0 : (t.2.1 : ℤ) ≠ 0 := by exact_mod_cast he.ne'
    obtain ⟨h1, h2⟩ := h0
    have hp : x.2.1 = 0 := by tauto
    have hr : x.2.2.2.1 = 0 := by tauto
    rw [hp, hr] at hd
    simp at hd
  have hdisj : Disjoint (T.image (Φ 1)) (T.image (Φ (-1))) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨t2, ht2, h⟩ := Finset.mem_image.mp hy2
    have := (huniq 1 (-1) (Or.inl rfl) (Or.inr rfl) t1 ht1 t2 ht2 h.symm).2
    norm_num at this
  have hsub : T.image (Φ 1) ∪ T.image (Φ (-1)) ⊆ W := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact hmaps 1 (Or.inl rfl) t ht
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact hmaps (-1) (Or.inr rfl) t ht
  rw [hT, hW]
  calc 2 * T.card = (T.image (Φ 1)).card + (T.image (Φ (-1))).card := by
        rw [Finset.card_image_of_injOn (hinj 1 (Or.inl rfl)),
          Finset.card_image_of_injOn (hinj (-1) (Or.inr rfl))]
        ring
    _ = (T.image (Φ 1) ∪ T.image (Φ (-1))).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ W.card := Finset.card_le_card hsub

end Idoneal
