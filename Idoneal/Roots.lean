import Idoneal.Character

/-!
# Square roots of `-n` modulo `m` (blueprint §1 (R))

The statement below is the fixed interface. Replace the `sorry`; add private lemmas freely.
Use only the *statements* of `Idoneal/Character.lean`.
-/

namespace Idoneal

namespace RootsAux

/-- The right-hand side `∑_{e² ∣ k} rho n (k / e²)`. -/
def S (n k : ℕ) : ℤ :=
  ∑ e ∈ (Finset.Icc 1 k).filter (fun e => e ^ 2 ∣ k), (rho n (k / e ^ 2) : ℤ)

theorem rho_one (n : ℕ) : rho n 1 = 1 := by
  simp [rho]

theorem rho_eq_card (n m : ℕ) [NeZero m] :
    rho n m = (Finset.univ.filter fun x : ZMod m => x ^ 2 + (n : ZMod m) = 0).card := by
  unfold rho
  refine Finset.card_nbij' (fun b => (b : ZMod m)) (fun x => x.val) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have := (ZMod.natCast_eq_zero_iff (b ^ 2 + n) m).2 hb.2
    push_cast at this
    exact this
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hx
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hb
    simp only [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hb.1
  · intro x _
    simp only [ZMod.natCast_zmod_val]

theorem rho_mul (n : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    rho n (a * b) = rho n a * rho n b := by
  have : NeZero a := ⟨by omega⟩
  have : NeZero b := ⟨by omega⟩
  have : NeZero (a * b) := ⟨by positivity⟩
  rw [rho_eq_card, rho_eq_card, rho_eq_card, ← Finset.card_product, ← Finset.filter_product,
    Finset.univ_product_univ]
  set e := ZMod.chineseRemainder hab
  refine Finset.card_nbij' (fun x => e x) (fun y => e.symm y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have h := congrArg e hx
    rw [map_add, map_pow, map_natCast, map_zero] at h
    exact ⟨by simpa using congrArg Prod.fst h, by simpa using congrArg Prod.snd h⟩
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    apply e.injective
    rw [map_add, map_pow, map_natCast, map_zero, RingEquiv.apply_symm_apply]
    exact Prod.ext (by simpa using hy.1) (by simpa using hy.2)
  · intro x _
    simp
  · intro y _
    simp

theorem S_nonneg (n k : ℕ) : 0 ≤ S n k :=
  Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

theorem S_mul_ge (n : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    S n a * S n b ≤ S n (a * b) := by
  unfold S
  set A := (Finset.Icc 1 a).filter (fun e => e ^ 2 ∣ a) with hA
  set B := (Finset.Icc 1 b).filter (fun e => e ^ 2 ∣ b) with hB
  set C := (Finset.Icc 1 (a * b)).filter (fun e => e ^ 2 ∣ a * b) with hC
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have key : ∀ x ∈ A ×ˢ B, ((rho n (a / x.1 ^ 2) : ℤ) * (rho n (b / x.2 ^ 2) : ℤ))
      = (fun e => (rho n (a * b / e ^ 2) : ℤ)) (x.1 * x.2) := by
    rintro ⟨e1, e2⟩ hx
    simp only [Finset.mem_product, hA, hB, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨h1, _⟩, d1⟩, ⟨⟨h2, _⟩, d2⟩⟩ := hx
    have hc : Nat.Coprime (a / e1 ^ 2) (b / e2 ^ 2) :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd d1)
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd d2) hab)
    rw [← Nat.cast_mul, ← rho_mul n (Nat.div_pos (Nat.le_of_dvd ha d1) (pow_pos (by omega) 2))
      (Nat.div_pos (Nat.le_of_dvd hb d2) (pow_pos (by omega) 2)) hc, Nat.div_mul_div_comm d1 d2,
      ]
    simp only [mul_pow]
  rw [Finset.sum_congr rfl key, ← Finset.sum_image (f := fun e => (rho n (a * b / e ^ 2) : ℤ))
    (g := fun x : ℕ × ℕ => x.1 * x.2)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      simp only [Finset.mem_image, Finset.mem_product, hA, hB, Finset.mem_filter,
        Finset.mem_Icc] at he
      obtain ⟨⟨e1, e2⟩, ⟨⟨⟨h1, h1'⟩, d1⟩, ⟨⟨h2, h2'⟩, d2⟩⟩, rfl⟩ := he
      simp only [hC, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by simpa using Nat.mul_le_mul h1 h2, Nat.mul_le_mul h1' h2'⟩, ?_⟩
      rw [mul_pow]; exact Nat.mul_dvd_mul d1 d2
    · intro _ _ _; exact Int.natCast_nonneg _
  · have g : ∀ u v, 0 < u → u ^ 2 ∣ a → v ^ 2 ∣ b → Nat.gcd (u * v) a = u := by
      intro u v _ hu hv
      have hua : u ∣ a := (dvd_pow_self u two_ne_zero).trans hu
      have hvb : v ∣ b := (dvd_pow_self v two_ne_zero).trans hv
      have hva : Nat.Coprime v a := Nat.Coprime.coprime_dvd_left hvb hab.symm
      rw [Nat.Coprime.gcd_mul_right_cancel u hva]
      exact Nat.gcd_eq_left hua
    rintro ⟨e1, e2⟩ hx ⟨f1, f2⟩ hy hxy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hA, hB, Finset.mem_filter,
      Finset.mem_Icc] at hx hy hxy
    obtain ⟨⟨⟨h1, _⟩, d1⟩, ⟨⟨h2, _⟩, d2⟩⟩ := hx
    obtain ⟨⟨⟨k1, _⟩, c1⟩, ⟨⟨k2, _⟩, c2⟩⟩ := hy
    have he : e1 = f1 := by
      rw [← g e1 e2 (by omega) d1 d2, ← g f1 f2 (by omega) c1 c2, hxy]
    subst he
    have : e2 = f2 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
    rw [this]

theorem rho_prime_of_chi_zero {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (h : chiZ n p = 0) :
    1 ≤ rho n p := by
  have hnc := (chiZ_eq_zero_iff hn p).1 h
  rw [Nat.Prime.coprime_iff_not_dvd hp, not_not] at hnc
  show 0 < rho n p
  unfold rho
  rcases (Nat.Prime.dvd_mul hp).1 hnc with h4 | hpn
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    subst hp2
    refine Finset.card_pos.2 ⟨n % 2, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (by norm_num), ?_⟩
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · rw [h0]; simpa using Nat.dvd_of_mod_eq_zero h0
    · rw [h1]; apply Nat.dvd_of_mod_eq_zero; omega
  · exact Finset.card_pos.2 ⟨0, by simp [hp.pos, hpn]⟩

theorem rho_prime_pow_of_chi_one {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (h : chiZ n p = 1)
    {l : ℕ} (hl : 0 < l) : 2 ≤ rho n (p ^ l) := by
  have hne : chiZ n p ≠ 0 := by rw [h]; norm_num
  have hcop : Nat.Coprime p (4 * n) := by
    by_contra hc; exact hne ((chiZ_eq_zero_iff hn p).2 hc)
  rw [Nat.Prime.coprime_iff_not_dvd hp] at hcop
  have hp2 : p ≠ 2 := by rintro rfl; exact hcop ⟨2 * n, by ring⟩
  have hpn : ¬ p ∣ n := fun hd => hcop (Dvd.dvd.mul_left hd 4)
  obtain ⟨b0, hb0⟩ := (chiZ_prime_eq_one_iff hp hp2 hpn).1 h
  have hpb0 : ¬ p ∣ b0 := by
    intro hd
    exact hpn ((Nat.dvd_add_right (Dvd.dvd.pow hd two_ne_zero)).1 hb0)
  have hens : ∀ m : ℕ, ∃ B : ℕ, p ^ (m + 1) ∣ B ^ 2 + n ∧ ¬ p ∣ B := by
    intro m
    induction m with
    | zero => exact ⟨b0, by simpa using hb0, hpb0⟩
    | succ m ih =>
      obtain ⟨B, ⟨c, hc⟩, hB⟩ := ih
      have := Fact.mk hp
      have h2B : ((2 * B : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h2 | hb
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
        · exact hB hb
      obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
          (t : ZMod p) = -(c : ZMod p) * ((2 * B : ℕ) : ZMod p)⁻¹ :=
        ⟨_, ZMod.natCast_zmod_val _⟩
      have ht : p ∣ c + 2 * B * t := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul (2 * B) t, ht_def,
          mul_comm (-(c : ZMod p)), ← mul_assoc, mul_inv_cancel₀ h2B]
        ring
      obtain ⟨s, hs⟩ := ht
      refine ⟨B + t * p ^ (m + 1), ⟨s + t ^ 2 * p ^ m, ?_⟩, ?_⟩
      · calc (B + t * p ^ (m + 1)) ^ 2 + n
            = (B ^ 2 + n) + 2 * B * t * p ^ (m + 1) + t ^ 2 * p ^ (2 * m + 2) := by ring
          _ = p ^ (m + 1) * (c + 2 * B * t) + t ^ 2 * p ^ (2 * m + 2) := by rw [hc]; ring
          _ = _ := by rw [hs]; ring
      · intro hd
        apply hB
        have h1 : p ∣ t * p ^ (m + 1) := Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero m)) t
        rw [add_comm] at hd
        exact (Nat.dvd_add_right h1).1 hd
  obtain ⟨B, hB, hpB⟩ := hens (l - 1)
  rw [Nat.sub_add_cancel hl] at hB
  have hqpos : 0 < p ^ l := pow_pos hp.pos l
  have hpq : p ∣ p ^ l := dvd_pow_self p (by omega)
  have hr : B % p ^ l ≠ 0 := by
    intro h0; apply hpB; exact hpq.trans (Nat.dvd_of_mod_eq_zero h0)
  have hodd : p ^ l % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hlt : B % p ^ l < p ^ l := Nat.mod_lt _ hqpos
  have hB' := (ZMod.natCast_eq_zero_iff _ _).2 hB
  push_cast at hB'
  have mem : ∀ r, r < p ^ l → ((r : ZMod (p ^ l)) = B ∨ (r : ZMod (p ^ l)) = -B) →
      r ∈ (Finset.range (p ^ l)).filter (fun b => p ^ l ∣ b ^ 2 + n) := by
    intro r hrq hr'
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hrq, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rcases hr' with h | h
    · rw [h]; exact hB'
    · rw [h, neg_sq]; exact hB'
  calc 2 = ({B % p ^ l, p ^ l - B % p ^ l} : Finset ℕ).card := by
        rw [Finset.card_pair (by omega)]
    _ ≤ rho n (p ^ l) := by
      unfold rho
      apply Finset.card_le_card
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact mem _ hlt (Or.inl (by rw [ZMod.natCast_mod]))
      · refine mem _ (Nat.sub_lt hqpos (Nat.pos_of_ne_zero hr)) (Or.inr ?_)
        rw [Nat.cast_sub hlt.le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem S_prime_pow_ge (n : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ∑ i ∈ Finset.range (j / 2 + 1), (rho n (p ^ (j - 2 * i)) : ℤ) ≤ S n (p ^ j) := by
  unfold S
  have hterm : ∀ i ∈ Finset.range (j / 2 + 1), (rho n (p ^ (j - 2 * i)) : ℤ)
      = (fun e => (rho n (p ^ j / e ^ 2) : ℤ)) (p ^ i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only
    rw [← pow_mul, Nat.pow_div (by omega) hp.pos, mul_comm i 2]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_image (f := fun e => (rho n (p ^ j / e ^ 2) : ℤ))
    (g := fun i => p ^ i)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      simp only [Finset.mem_image, Finset.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.one_le_pow _ _ hp.pos, Nat.pow_le_pow_right hp.pos (by omega)⟩, ?_⟩
      rw [← pow_mul]; exact pow_dvd_pow p (by omega)
    · intro _ _ _; exact Int.natCast_nonneg _
  · intro x _ y _ hxy
    exact Nat.pow_right_injective hp.two_le hxy

theorem gZ_prime_pow_le (n : ℕ) (hn : 0 < n) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    gZ n (p ^ j) ≤ S n (p ^ j) := by
  refine le_trans ?_ (S_prime_pow_ge n hp j)
  rw [gZ_prime_pow n hp]
  have step : ∀ l, chiZ n p ^ l + chiZ n p ^ (l + 1) ≤ (rho n (p ^ (l + 1)) : ℤ) := by
    intro l
    rcases chiZ_trichotomy n p with h0 | h1 | hm
    · rcases Nat.eq_zero_or_pos l with rfl | hl
      · simp only [h0, zero_add, pow_zero, pow_one, add_zero]
        exact_mod_cast rho_prime_of_chi_zero hn hp h0
      · rw [h0, zero_pow (by omega), zero_pow (by omega), add_zero]
        exact Int.natCast_nonneg _
    · rw [h1, one_pow, one_pow]
      exact_mod_cast rho_prime_pow_of_chi_one hn hp h1 (by omega)
    · have : (-1 : ℤ) ^ l + (-1) ^ (l + 1) = 0 := by rw [pow_succ]; ring
      rw [hm, this]
      exact Int.natCast_nonneg _
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | _ | j
    · simp [rho_one]
    · have := step 0
      simpa [Finset.sum_range_succ] using this
    · have e1 : (j + 1 + 1) / 2 + 1 = (j / 2 + 1) + 1 := by omega
      rw [e1, Finset.sum_range_succ' (fun i => (rho n (p ^ (j + 1 + 1 - 2 * i)) : ℤ)) (j / 2 + 1),
        Finset.sum_range_succ (fun i => chiZ n p ^ i) (j + 1 + 1),
        Finset.sum_range_succ (fun i => chiZ n p ^ i) (j + 1)]
      have e2 : ∀ i, j + 1 + 1 - 2 * (i + 1) = j - 2 * i := fun i => by omega
      simp only [e2, Nat.mul_zero, Nat.sub_zero]
      have h1 := ih j (by omega)
      have h2 := step (j + 1)
      linarith

theorem gZ_le_S {n : ℕ} (hn : 0 < n) : ∀ k, 0 < k → gZ n k ≤ S n k := by
  intro k
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p j hp _ => intro _; exact gZ_prime_pow_le n hn hp j
  | zero => intro h; omega
  | one =>
    intro _
    have := gZ_prime_pow_le n hn Nat.prime_two 0
    rwa [pow_zero] at this
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [gZ_mul_of_coprime n hab]
    calc gZ n a * gZ n b ≤ S n a * S n b :=
          mul_le_mul (iha (by omega)) (ihb (by omega)) (gZ_nonneg n b) (S_nonneg n a)
      _ ≤ S n (a * b) := S_mul_ge n (by omega) (by omega) hab

end RootsAux

theorem gZ_le_sum_rho {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    gZ n k ≤ ∑ e ∈ (Finset.Icc 1 k).filter (fun e => e ^ 2 ∣ k), (rho n (k / e ^ 2) : ℤ) :=
  RootsAux.gZ_le_S hn k hk

end Idoneal
