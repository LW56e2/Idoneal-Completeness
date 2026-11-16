import Mathlib

/-!
# Idoneal numbers: shared definitions

`IsIdoneal` and `knownIdonealNumbers` are copied verbatim from
`google-deepmind/formal-conjectures`, `FormalConjectures/Wikipedia/IdonealCompleteness.lean`.
Everything else is auxiliary. See `BLUEPRINT.md`.
-/

namespace Idoneal

/-- A positive integer `n` is idoneal if and only if it cannot be written as
`ab + bc + ac` for distinct positive integers `a, b, c`. -/
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧
    ¬ ∃ a b c : ℕ,
      0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/-- The 65 known idoneal numbers. -/
def knownIdonealNumbers : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848}

/-- `n = ab + bc + ca` with `0 < a < b < c`. -/
def HasTriple (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/-- A strictly reduced form `A x² + 2B xy + C y²` of determinant `n`:
`0 < 2B < A < C` and `A C = n + B²`. -/
def HasStrictForm (n : ℕ) : Prop :=
  ∃ A B C : ℕ, 0 < B ∧ 2 * B < A ∧ A < C ∧ A * C = n + B ^ 2

/-- The analytic hypothesis: no real zero in `[19/20, 1)` for a nontrivial Dirichlet character. -/
def NoRealZeros : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ σ : ℝ, 19 / 20 ≤ σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0

instance instNeZeroFourMul (n : ℕ) [NeZero n] : NeZero (4 * n) :=
  ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩

/-- `J(-n | m)` for odd `m`, and `0` for even `m`. -/
def chiZ (n m : ℕ) : ℤ := if m % 2 = 1 then jacobiSym (-(n : ℤ)) m else 0

/-- The Dirichlet convolution `1 * chiZ n`. -/
def gZ (n k : ℕ) : ℤ := ∑ d ∈ k.divisors, chiZ n d

/-- Number of `0 ≤ b < m` with `m ∣ b² + n`. -/
def rho (n m : ℕ) : ℕ := ((Finset.range m).filter fun b => m ∣ b ^ 2 + n).card

/-- The value `A x² + 2 B x y + C y²` of the form `f = (A, B, C)`. -/
def formVal (f : ℕ × ℕ × ℕ) (x y : ℤ) : ℤ :=
  (f.1 : ℤ) * x ^ 2 + 2 * (f.2.1 : ℤ) * x * y + (f.2.2 : ℤ) * y ^ 2

/-- Number of nonzero integer points `(x, y)` with `formVal f x y ≤ X`. -/
noncomputable def latticeCount (f : ℕ × ℕ × ℕ) (X : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ // v ≠ 0 ∧ formVal f v.1 v.2 ≤ (X : ℤ)}

/-- `f = (A, B, C)` is a normalized reduced form of determinant `n` of ambiguous type:
`A C = n + B²`, `2B ≤ A ≤ C`, `0 < A`, and `B = 0` or `2B = A` or `A = C`. -/
def IsAmbiguousForm (n : ℕ) (f : ℕ × ℕ × ℕ) : Prop :=
  f.1 * f.2.2 = n + f.2.1 ^ 2 ∧ 2 * f.2.1 ≤ f.1 ∧ f.1 ≤ f.2.2 ∧ 0 < f.1 ∧
    (f.2.1 = 0 ∨ 2 * f.2.1 = f.1 ∨ f.1 = f.2.2)

instance (n : ℕ) : DecidablePred (IsAmbiguousForm n) := fun f => by
  unfold IsAmbiguousForm; infer_instance

/-- The finite set of forms satisfying `IsAmbiguousForm n` (see `mem_ambiguousForms`). -/
def ambiguousForms (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 2) ×ˢ Finset.range (n + 2) ×ˢ Finset.range (n ^ 2 + n + 2)).filter
    (IsAmbiguousForm n)

end Idoneal
