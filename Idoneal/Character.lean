import Idoneal.Defs

/-!
# The character `chiZ n = J(-n | ·)` (blueprint §1 (C))

Statements below are the fixed interface. Replace each `sorry`; add private lemmas freely.
The definition of `chi` must be filled in (it is a `sorry` only in the skeleton).
-/

namespace Idoneal

theorem chiZ_one (n : ℕ) : chiZ n 1 = 1 := by
  simp [chiZ, jacobiSym.one_right]

private theorem chiZ_of_even {n m : ℕ} (h : m % 2 = 0) : chiZ n m = 0 := by
  simp [chiZ, h]

private theorem chiZ_zero (n : ℕ) : chiZ n 0 = 0 := chiZ_of_even rfl

theorem chiZ_mul (n a b : ℕ) : chiZ n (a * b) = chiZ n a * chiZ n b := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · rw [chiZ_of_even ha, chiZ_of_even (by rw [Nat.mul_mod, ha]; simp), zero_mul]
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · rw [chiZ_of_even hb, chiZ_of_even (by rw [Nat.mul_mod, hb]; simp), mul_zero]
  have hab : a * b % 2 = 1 := by rw [Nat.mul_mod, ha, hb]
  simp only [chiZ, ha, hb, hab, ite_true]
  exact jacobiSym.mul_right' _ (by omega) (by omega)

theorem chiZ_trichotomy (n m : ℕ) : chiZ n m = 0 ∨ chiZ n m = 1 ∨ chiZ n m = -1 := by
  unfold chiZ
  split_ifs
  · exact jacobiSym.trichotomy _ _
  · exact Or.inl rfl

theorem chiZ_add_period {n : ℕ} (hn : 0 < n) (m : ℕ) : chiZ n (m + 4 * n) = chiZ n m := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [chiZ_of_even hm, chiZ_of_even (by omega)]
  have hm' : (m + 4 * n) % 2 = 1 := by omega
  simp only [chiZ, hm, hm', ite_true]
  rw [jacobiSym.mod_right _ (Nat.odd_iff.2 hm'), jacobiSym.mod_right _ (Nat.odd_iff.2 hm)]
  congr 1
  simp

private theorem chiZ_add_mul_period {n : ℕ} (hn : 0 < n) (m k : ℕ) :
    chiZ n (m + 4 * n * k) = chiZ n m := by
  induction k with
  | zero => simp
  | succ k ih => rw [mul_add, mul_one, ← add_assoc, chiZ_add_period hn, ih]

private theorem chiZ_mod {n : ℕ} (hn : 0 < n) (m : ℕ) : chiZ n (m % (4 * n)) = chiZ n m := by
  conv_rhs => rw [← Nat.mod_add_div m (4 * n)]
  rw [chiZ_add_mul_period hn]

theorem chiZ_eq_zero_iff {n : ℕ} (hn : 0 < n) (m : ℕ) :
    chiZ n m = 0 ↔ ¬ Nat.Coprime m (4 * n) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [chiZ_of_even hm]
    simp only [true_iff]
    intro h
    have h2 : 2 ∣ Nat.gcd m (4 * n) :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hm) (Dvd.intro (2 * n) (by ring))
    rw [h] at h2
    omega
  simp only [chiZ, hm, ite_true]
  haveI : NeZero m := ⟨by omega⟩
  rw [jacobiSym.eq_zero_iff_not_coprime]
  have hg : Int.gcd (-(n : ℤ)) (m : ℤ) = Nat.gcd n m := by
    show Nat.gcd (-(n : ℤ)).natAbs (m : ℤ).natAbs = _
    simp
  rw [hg, not_iff_not]
  have hm2 : Nat.Coprime m 4 := by
    have : Nat.Coprime m 2 := by
      rw [Nat.coprime_two_right]; exact Nat.odd_iff.2 hm
    simpa using Nat.Coprime.pow_right 2 this
  rw [Nat.coprime_mul_iff_right]
  constructor
  · intro h; exact ⟨hm2, Nat.Coprime.symm h⟩
  · rintro ⟨_, h⟩; exact Nat.Coprime.symm h

theorem chiZ_four_mul_sub_one {n : ℕ} (hn : 0 < n) : chiZ n (4 * n - 1) = -1 := by
  have hb : (4 * n - 1) % 2 = 1 := by omega
  have hbo : Odd (4 * n - 1) := Nat.odd_iff.2 hb
  simp only [chiZ, hb, ite_true]
  have h1 : jacobiSym (4 * -(n : ℤ)) (4 * n - 1) = jacobiSym (-(n : ℤ)) (4 * n - 1) := by
    rw [jacobiSym.mul_left, jacobiSym.at_four hbo, one_mul]
  have h2 : jacobiSym (4 * -(n : ℤ)) (4 * n - 1) = jacobiSym (-1) (4 * n - 1) := by
    apply jacobiSym.mod_left'
    have : ((4 * n - 1 : ℕ) : ℤ) = 4 * (n : ℤ) - 1 := by push_cast [Nat.one_le_iff_ne_zero]; omega
    rw [this]
    have e : 4 * -(n : ℤ) = -1 + (4 * n - 1) * (-1) := by ring
    rw [e, Int.add_mul_emod_self_left]
  rw [← h1, h2, jacobiSym.at_neg_one hbo, ZMod.χ₄_nat_three_mod_four (by omega)]

/-- For an odd prime `p ∤ n`: `chiZ n p = 1` iff `-n` is a square mod `p`. -/
theorem chiZ_prime_eq_one_iff {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    chiZ n p = 1 ↔ ∃ b : ℕ, p ∣ b ^ 2 + n := by
  haveI := Fact.mk hp
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  simp only [chiZ, hodd, ite_true]
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have h0 : ((-(n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    exact hpn
  rw [legendreSym.eq_one_iff p h0]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r.val, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val, sq, ← hr]
    ring
  · rintro ⟨b, hb⟩
    refine ⟨(b : ZMod p), ?_⟩
    rw [← ZMod.natCast_eq_zero_iff] at hb
    push_cast at hb ⊢
    linear_combination -hb

/-! ### Partial sums -/

private theorem chiZ_reflect {n : ℕ} (hn : 0 < n) {d : ℕ} (hd : d ≤ 4 * n) :
    chiZ n (4 * n - d) = - chiZ n d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · rw [chiZ_zero, Nat.sub_zero, chiZ_of_even (by omega)]; simp
  have e : d * (4 * n - 1) = (4 * n - d) + 4 * n * (d - 1) := by
    zify [hd, (by omega : 1 ≤ 4 * n), (by omega : 1 ≤ d)]
    ring
  have := chiZ_mul n d (4 * n - 1)
  rw [e, chiZ_add_mul_period hn, chiZ_four_mul_sub_one hn] at this
  rw [this]; ring

private def A (n k : ℕ) : ℤ := ∑ i ∈ Finset.range k, chiZ n i

private theorem abs_A_le (n k : ℕ) : |A n k| ≤ ((k / 2 : ℕ) : ℤ) := by
  induction k with
  | zero => simp [A]
  | succ k ih =>
    unfold A at *
    rw [Finset.sum_range_succ]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [chiZ_of_even hk, add_zero]
      refine ih.trans ?_
      exact_mod_cast Nat.div_le_div_right (Nat.le_succ k)
    · have h1 : |chiZ n k| ≤ 1 := by
        rcases chiZ_trichotomy n k with h | h | h <;> rw [h] <;> simp
      have : ((k + 1) / 2 : ℕ) = k / 2 + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one]
      exact (abs_add_le _ _).trans (by linarith)

private theorem A_period_zero {n : ℕ} (hn : 0 < n) : A n (4 * n) = 0 := by
  have h1 : A n (4 * n + 1) = A n (4 * n) := by
    unfold A
    rw [Finset.sum_range_succ, chiZ_of_even (by omega), add_zero]
  have h2 : A n (4 * n + 1) = ∑ i ∈ Finset.range (4 * n), chiZ n (i + 1) := by
    unfold A
    rw [Finset.sum_range_succ', chiZ_zero, add_zero]
  have h3 : ∑ i ∈ Finset.range (4 * n), chiZ n (i + 1) = - A n (4 * n) := by
    rw [← Finset.sum_range_reflect, A, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show 4 * n - 1 - i + 1 = 4 * n - i by omega, chiZ_reflect hn hi.le]
  linarith

private theorem A_add_period {n : ℕ} (hn : 0 < n) (N : ℕ) : A n (4 * n + N) = A n N := by
  unfold A
  rw [Finset.sum_range_add]
  have := A_period_zero hn
  unfold A at this
  rw [this, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm, chiZ_add_period hn]

private theorem A_mod {n : ℕ} (hn : 0 < n) (N : ℕ) : A n N = A n (N % (4 * n)) := by
  conv_lhs => rw [← Nat.mod_add_div N (4 * n)]
  generalize N / (4 * n) = q
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show N % (4 * n) + 4 * n * (q + 1) = 4 * n + (N % (4 * n) + 4 * n * q) by ring,
      A_add_period hn, ih]

private theorem abs_A_le_n {n : ℕ} (hn : 0 < n) (N : ℕ) : |A n N| ≤ (n : ℤ) := by
  rw [A_mod hn]
  set r := N % (4 * n) with hr
  have hr4 : r < 4 * n := Nat.mod_lt _ (by omega)
  by_cases hr2 : r ≤ 2 * n
  · refine (abs_A_le n r).trans ?_
    exact_mod_cast (by omega : r / 2 ≤ n)
  · -- complementary block of length k = 4n - r
    set k := 4 * n - r with hk
    have hsplit : A n (4 * n) = A n r + ∑ i ∈ Finset.range k, chiZ n (r + i) := by
      unfold A
      rw [← Finset.sum_range_add, show r + k = 4 * n by omega]
    have hrefl : ∑ i ∈ Finset.range k, chiZ n (r + i) = - A n (k + 1) := by
      rw [← Finset.sum_range_reflect]
      have : A n (k + 1) = ∑ i ∈ Finset.range k, chiZ n (i + 1) := by
        unfold A; rw [Finset.sum_range_succ', chiZ_zero, add_zero]
      rw [this, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show r + (k - 1 - i) = 4 * n - (i + 1) by omega, chiZ_reflect hn (by omega)]
    rw [A_period_zero hn, hrefl] at hsplit
    have : A n r = A n (k + 1) := by linarith
    rw [this]
    refine (abs_A_le n (k + 1)).trans ?_
    exact_mod_cast (by omega : (k + 1) / 2 ≤ n)

/-- Partial sums are bounded by `n`. -/
theorem abs_sum_chiZ_le {n : ℕ} (hn : 0 < n) (N : ℕ) :
    |∑ d ∈ Finset.Icc 1 N, chiZ n d| ≤ (n : ℤ) := by
  have h : ∀ N, ∑ d ∈ Finset.Icc 1 N, chiZ n d = A n (N + 1) := by
    intro N
    induction N with
    | zero => simp [A, chiZ_zero]
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      unfold A
      rw [Finset.sum_range_succ _ (N + 1)]
  rw [h]
  exact abs_A_le_n hn _

/-! ### The convolution `gZ` -/

private def chiAF (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨chiZ n, chiZ_zero n⟩

private theorem chiAF_mult (n : ℕ) : (chiAF n).IsMultiplicative :=
  ⟨chiZ_one n, fun {a b} _ => chiZ_mul n a b⟩

private theorem gZ_eq (n k : ℕ) :
    gZ n k = ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * chiAF n) k := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  rfl

theorem gZ_mul_of_coprime (n : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    gZ n (a * b) = gZ n a * gZ n b := by
  simp only [gZ_eq]
  exact ((ArithmeticFunction.isMultiplicative_zeta.natCast).mul (chiAF_mult n)).map_mul_of_coprime
    hab

private theorem chiZ_pow (n p i : ℕ) : chiZ n (p ^ i) = chiZ n p ^ i := by
  induction i with
  | zero => simp [chiZ_one]
  | succ i ih => rw [pow_succ, chiZ_mul, ih, pow_succ]

theorem gZ_prime_pow (n : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    gZ n (p ^ j) = ∑ i ∈ Finset.range (j + 1), chiZ n p ^ i := by
  unfold gZ
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [chiZ_pow]

private theorem geom_bounds {c : ℤ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (2 * k), c ^ i ∧ 1 ≤ ∑ i ∈ Finset.range (2 * k + 1), c ^ i := by
  have step : ∀ m, 0 ≤ c ^ m * (1 + c) := by
    intro m
    rcases hc with rfl | rfl | rfl
    · rw [add_zero, mul_one]; exact pow_nonneg le_rfl _
    · simp
    · simp
  have two : ∀ m, ∑ i ∈ Finset.range (m + 2), c ^ i
      = ∑ i ∈ Finset.range m, c ^ i + c ^ m * (1 + c) := by
    intro m
    rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]; ring
  induction k with
  | zero => simp
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, two]
      linarith [step (2 * k), ih.1]
    · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, two]
      linarith [step (2 * k + 1), ih.2]

private theorem geom_nonneg {c : ℤ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (m : ℕ) :
    0 ≤ ∑ i ∈ Finset.range m, c ^ i := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · exact (geom_bounds hc k).1
  · exact le_trans zero_le_one (geom_bounds hc k).2

theorem gZ_nonneg (n k : ℕ) : 0 ≤ gZ n k := by
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p j hp _ =>
    rw [gZ_prime_pow n hp]
    exact geom_nonneg (chiZ_trichotomy n p) _
  | zero => simp [gZ]
  | one => simp [gZ, chiZ_one]
  | coprime a b _ _ hab ha hb =>
    rw [gZ_mul_of_coprime n hab]
    exact mul_nonneg ha hb

theorem one_le_gZ_sq (n : ℕ) {j : ℕ} (hj : 0 < j) : 1 ≤ gZ n (j ^ 2) := by
  induction j using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp _ =>
    rw [← pow_mul, gZ_prime_pow n hp, mul_comm]
    exact (geom_bounds (chiZ_trichotomy n p) e).2
  | zero => omega
  | one => simp [gZ, chiZ_one]
  | coprime a b ha1 hb1 hab ha hb =>
    rw [mul_pow, gZ_mul_of_coprime n (Nat.Coprime.pow 2 2 hab)]
    have h1 := ha (by omega)
    have h2 := hb (by omega)
    nlinarith

/-! ### The Dirichlet character -/

private theorem chiZ_val_mul (n : ℕ) [NeZero n] (x y : ZMod (4 * n)) :
    chiZ n (x * y).val = chiZ n x.val * chiZ n y.val := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [ZMod.val_mul, chiZ_mod hn, chiZ_mul]

/-- The Dirichlet character mod `4n` with values `chiZ n`. -/
noncomputable def chi (n : ℕ) [NeZero n] : DirichletCharacter ℂ (4 * n) where
  toFun x := ((chiZ n x.val : ℤ) : ℂ)
  map_one' := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [ZMod.val_one'' (by omega), chiZ_one]; simp
  map_mul' x y := by
    simp only [chiZ_val_mul, Int.cast_mul]
  map_nonunit' x hx := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have : ¬ Nat.Coprime x.val (4 * n) := by
      intro h
      apply hx
      rw [← ZMod.natCast_zmod_val x]
      exact (ZMod.isUnit_iff_coprime _ _).2 h
    rw [(chiZ_eq_zero_iff hn _).2 this]; simp

theorem chi_natCast (n : ℕ) [NeZero n] (m : ℕ) :
    chi n (m : ZMod (4 * n)) = ((chiZ n m : ℤ) : ℂ) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  show ((chiZ n (m : ZMod (4 * n)).val : ℤ) : ℂ) = _
  rw [ZMod.val_natCast, chiZ_mod hn]

theorem chi_ne_one (n : ℕ) [NeZero n] : chi n ≠ 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  intro h
  have hcop : Nat.Coprime (4 * n - 1) (4 * n) := by
    by_contra hc
    have := (chiZ_eq_zero_iff hn _).2 hc
    rw [chiZ_four_mul_sub_one hn] at this
    exact absurd this (by norm_num)
  have hu : IsUnit ((4 * n - 1 : ℕ) : ZMod (4 * n)) := (ZMod.isUnit_iff_coprime _ _).2 hcop
  have h1 := chi_natCast n (4 * n - 1)
  rw [h, chiZ_four_mul_sub_one hn] at h1
  have h2 : (1 : DirichletCharacter ℂ (4 * n)) ((4 * n - 1 : ℕ) : ZMod (4 * n)) = 1 :=
    MulChar.one_apply_coe hu.unit
  rw [h2] at h1
  norm_num at h1

end Idoneal
