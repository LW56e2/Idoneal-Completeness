import Idoneal.Defs

/-!
# Elementary layer (blueprint §1 (E))

Statements below are the fixed interface. Replace each `sorry`; add private lemmas freely.
-/

namespace Idoneal

/-- `A = a + b`, `B = a`, `C = a + c`. -/
theorem hasTriple_iff_hasStrictForm (n : ℕ) : HasTriple n ↔ HasStrictForm n := by
  constructor
  · rintro ⟨a, b, c, ha, hab, hbc, rfl⟩
    exact ⟨a + b, a, a + c, ha, by omega, by omega, by ring⟩
  · rintro ⟨A, B, C, hB, hBA, hAC, h⟩
    obtain ⟨b, rfl⟩ : ∃ b, A = B + b := ⟨A - B, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, C = B + c := ⟨C - B, by omega⟩
    refine ⟨B, b, c, hB, by omega, by omega, ?_⟩
    nlinarith

theorem isIdoneal_iff (n : ℕ) : IsIdoneal n ↔ 0 < n ∧ ¬ HasStrictForm n := by
  rw [← hasTriple_iff_hasStrictForm]
  rfl

/-- Scaling a triple by `t`. -/
theorem HasTriple.sq_mul {m : ℕ} (h : HasTriple m) {t : ℕ} (ht : 0 < t) :
    HasTriple (t ^ 2 * m) := by
  obtain ⟨a, b, c, ha, hab, hbc, rfl⟩ := h
  refine ⟨t * a, t * b, t * c, Nat.mul_pos ht ha, Nat.mul_lt_mul_of_pos_left hab ht,
    Nat.mul_lt_mul_of_pos_left hbc ht, by ring⟩

/-- A strict form from `A ∣ n + B²`, `0 < B`, `2B < A`, `A² < n`. -/
private lemma strictForm_of (n A B : ℕ) (hd : A ∣ n + B ^ 2) (hB : 0 < B) (h2B : 2 * B < A)
    (hA : A ^ 2 < n) : HasStrictForm n := by
  obtain ⟨C, hC⟩ := hd
  refine ⟨A, B, C, hB, h2B, ?_, hC.symm⟩
  by_contra hle
  push Not at hle
  have : A * C ≤ A * A := Nat.mul_le_mul_left A hle
  nlinarith

/-- The key construction: from `A ∣ n + x²` with `A ∤ x`, `A ∤ 2x`, `A² < n`. -/
private lemma strictForm_of_x (n A x : ℕ) (hd : A ∣ n + x ^ 2) (h1 : ¬ A ∣ x)
    (h2 : ¬ A ∣ 2 * x) (hA : A ^ 2 < n) : HasStrictForm n := by
  have hA0 : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h
      exact absurd (zero_dvd_iff.mpr (by
        have := zero_dvd_iff.mp hd; omega)) h1
    · exact h
  set q := x / A
  set r := x % A
  have hx : x = A * q + r := (Nat.div_add_mod x A).symm
  have hrA : r < A := Nat.mod_lt x hA0
  have hr0 : r ≠ 0 := by
    intro h; apply h1; exact Nat.dvd_of_mod_eq_zero h
  have h2r : 2 * r ≠ A := by
    intro h; apply h2
    exact ⟨2 * q + 1, by rw [hx]; nlinarith⟩
  have hn : A ∣ n + r ^ 2 := by
    have : n + x ^ 2 = (n + r ^ 2) + A * (q * (A * q + 2 * r)) := by rw [hx]; ring
    rw [this] at hd
    exact (Nat.dvd_add_left (dvd_mul_right A _)).mp hd
  rcases lt_or_gt_of_ne h2r with hlt | hgt
  · exact strictForm_of n A r hn (Nat.pos_of_ne_zero hr0) hlt hA
  · obtain ⟨s, hs⟩ : ∃ s, A = s + r := ⟨A - r, by omega⟩
    have hn' : A ∣ n + s ^ 2 := by
      have : (n + s ^ 2) + A * (2 * r) = (n + r ^ 2) + A * A := by rw [hs]; ring
      have h3 : A ∣ (n + s ^ 2) + A * (2 * r) := by
        rw [this]; exact dvd_add hn (dvd_mul_right A A)
      exact (Nat.dvd_add_left (dvd_mul_right A _)).mp h3
    exact strictForm_of n A s hn' (by omega) (by omega) hA

/-- Non-divisibility from coprimality. -/
private lemma not_dvd_two_mul (A y p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime A y)
    (h1 : A ≠ 1) (h2 : A ≠ 2) (hAp : A ≠ p) (hA2p : A ≠ 2 * p) : ¬ A ∣ 2 * (y * p) := by
  intro h
  have h' : A ∣ y * (2 * p) := by rw [show y * (2 * p) = 2 * (y * p) by ring]; exact h
  have hd : A ∣ 2 * p := hcop.dvd_of_dvd_mul_left h'
  obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := dvd_mul.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd₁ with rfl | rfl <;>
    rcases (Nat.dvd_prime hp).mp hd₂ with rfl | rfl <;> simp_all

private lemma coprime_one_add (y l : ℕ) : Nat.Coprime (1 + y * l) y := by
  rw [show 1 + y * l = 1 + l * y by ring, Nat.coprime_add_mul_right_left]
  exact Nat.coprime_one_left y

/-- Step B of the blueprint. -/
theorem hasStrictForm_prime_sq_mul {p m : ℕ} (hp : p.Prime) (hp47 : 47 ≤ p)
    (hm0 : 0 < m) (hm : m ≤ 1848) : HasStrictForm (p ^ 2 * m) := by
  by_cases hbad : m = 1 ∨ m + 1 = p ∨ m + 1 = 2 * p
  · -- λ = 2: A = 1 + 4m, x = 2 m p
    have hcop : Nat.Coprime (1 + (2 * m) * 2) (2 * m) := coprime_one_add _ _
    have hnd := not_dvd_two_mul (1 + (2 * m) * 2) (2 * m) p hp hcop (by omega) (by omega)
      (by omega) (by omega)
    apply strictForm_of_x (p ^ 2 * m) (1 + (2 * m) * 2) (2 * m * p)
    · exact ⟨p ^ 2 * m, by ring⟩
    · exact fun h => hnd (dvd_trans h (dvd_mul_left _ _))
    · exact hnd
    · rcases hbad with rfl | h | h
      · nlinarith
      · subst h
        have : m ^ 2 * 46 ≤ m ^ 2 * m := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      · have h4 : 4 * (p ^ 2 * m) = (m + 1) ^ 2 * m := by rw [h]; ring
        have hm93 : 93 ≤ m := by omega
        have : m ^ 2 * 93 ≤ m ^ 2 * m := Nat.mul_le_mul_left _ hm93
        nlinarith
  · -- λ = 1: A = 1 + m, x = m p
    push Not at hbad
    obtain ⟨h1, h2, h3⟩ := hbad
    have hcop : Nat.Coprime (1 + m * 1) m := coprime_one_add _ _
    have hnd := not_dvd_two_mul (1 + m * 1) m p hp hcop (by omega) (by omega)
      (by omega) (by omega)
    apply strictForm_of_x (p ^ 2 * m) (1 + m * 1) (m * p)
    · exact ⟨p ^ 2 * m, by ring⟩
    · exact fun h => hnd (dvd_trans h (dvd_mul_left _ _))
    · exact hnd
    · have hp2 : 47 * 47 ≤ p ^ 2 := by nlinarith
      have hmm : m * m ≤ 1848 * m := Nat.mul_le_mul_right m hm
      have : 2209 * m ≤ p ^ 2 * m := Nat.mul_le_mul_right m hp2
      nlinarith

end Idoneal
