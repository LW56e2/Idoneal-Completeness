import Idoneal.Defs

/-!
# The 65 numbers of the list are idoneal (unconditional)

The easy direction: no number of Euler's list is of the form `ab + bc + ca` with `0 < a < b < c`.
A triple for `n` gives a pair `(u, a) = (a + b, a)` with `0 < a`, `2a < u`, `u ∣ n + a²` and
`u² < n + a²`; for `n ≤ 1848` this forces `u < 50` and `a < 25`, and the finitely many cases are
checked by the kernel (`decide +kernel`, no `native_decide`).
-/

namespace Idoneal

/-- A triple gives `u = a + b` and `a` with `0 < a`, `2a < u`, `u ∣ n + a²`, `u² < n + a²`. -/
theorem HasTriple.exists_pair {n : ℕ} (h : HasTriple n) :
    ∃ u a : ℕ, 0 < a ∧ 2 * a < u ∧ u ∣ n + a ^ 2 ∧ u ^ 2 < n + a ^ 2 := by
  obtain ⟨a, b, c, ha, hab, hbc, hn⟩ := h
  have h2 : (a + b) * (a + c) = n + a ^ 2 := by rw [hn]; ring
  refine ⟨a + b, a, ha, by omega, ⟨a + c, h2.symm⟩, ?_⟩
  have h1 : (a + b) * (a + b) < (a + b) * (a + c) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  calc (a + b) ^ 2 = (a + b) * (a + b) := by ring
    _ < (a + b) * (a + c) := h1
    _ = n + a ^ 2 := h2

/-- The list as a `List`, for kernel evaluation. -/
def knownListConv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848]

theorem mem_knownListConv_of_mem {n : ℕ} (h : n ∈ knownIdonealNumbers) : n ∈ knownListConv := by
  simp only [knownIdonealNumbers, Finset.mem_insert, Finset.mem_singleton] at h
  simp only [knownListConv, List.mem_cons, List.mem_nil_iff, or_false]
  exact h

/-- The finite check: no admissible pair `(u, a)` with `u < 50`, `a < 25` for a number of the
list. -/
theorem no_pair_of_known : ∀ n ∈ knownListConv, ∀ u < 50, ∀ a < 25,
    ¬(0 < a ∧ 2 * a < u ∧ u ∣ n + a ^ 2 ∧ u ^ 2 < n + a ^ 2) := by
  decide +kernel

/-- Every number of Euler's list is idoneal. -/
theorem isIdoneal_of_mem_known {n : ℕ} (h : n ∈ knownIdonealNumbers) : IsIdoneal n := by
  have hl := mem_knownListConv_of_mem h
  have hbd : 0 < n ∧ n ≤ 1848 := by
    simp only [knownIdonealNumbers, Finset.mem_insert, Finset.mem_singleton] at h
    omega
  refine ⟨hbd.1, fun ht => ?_⟩
  obtain ⟨u, a, ha, hu, hdvd, hlt⟩ := HasTriple.exists_pair ht
  have h4 : (2 * a) ^ 2 < u ^ 2 := Nat.pow_lt_pow_left hu (by norm_num)
  have hu50 : u < 50 := by
    by_contra hge
    rw [not_lt] at hge
    have : 50 ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hge 2
    nlinarith [hbd.2]
  have ha25 : a < 25 := by omega
  exact no_pair_of_known n hl u hu50 a ha25 ⟨ha, hu, hdvd, hlt⟩

end Idoneal
