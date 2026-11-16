# Idoneal completeness from a zero-free segment: blueprint

Goal (statement taken verbatim from `google-deepmind/formal-conjectures`,
`FormalConjectures/Wikipedia/IdonealCompleteness.lean`, where it is tagged `research open`):

```lean
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧ ¬ ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

theorem idoneal_numbers_completeness : ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers
```

We prove it under the hypothesis

```lean
def NoRealZeros : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ σ : ℝ, 19 / 20 ≤ σ → σ < 1 → χ.LFunction (σ : ℂ) ≠ 0
```

which follows at once from any zero-free half-plane `Re s > T` with `T < 19/20`
(the theorem `RH.Transport.dirichlet_nonvanishing` of the vendored project
`quasi-riemann-improved` has `T = 4374785349/5000000000`).

Everything in this blueprint is proved in `Idoneal/`, with no `sorry`; §3 joins it with the
zero-free theorem. How to build, and the record of the verification run, are in `README.md`.

Rules for every file: Lean `v4.34.1`, Mathlib at the pinned revision, `import Mathlib` allowed.
No `sorry`, no `native_decide`, no new axioms (`#print axioms` must show only
`propext`, `Classical.choice`, `Quot.sound`). Kernel computations use `decide`/`decide +kernel`/`rfl`.

## 0. Notation

* A *triple* for `n`: `0 < a < b < c`, `n = ab + bc + ca` (`HasTriple n`).
* A *strict form* for `n`: naturals `0 < 2B < A < C` with `A C = n + B²` (`HasStrictForm n`).
  This is a strictly reduced form `A x² + 2B xy + C y²` of determinant `n`.
* `HasTriple n ↔ HasStrictForm n` via `A = a + b, B = a, C = a + c`.
* `chiZ n m` = Jacobi symbol `J(-n | m)` for odd `m`, and `0` for even `m`. It is completely
  multiplicative, periodic mod `4n`, zero exactly when `gcd(m, 4n) ≠ 1`, and `chiZ n (4n-1) = -1`.
  `chi n` is the corresponding `DirichletCharacter ℂ (4 * n)`; it is not principal.
* `gZ n k = ∑_{d ∣ k} chiZ n d ≥ 0`, with `gZ n (j²) ≥ 1`.
* `rho n m = #{0 ≤ b < m : m ∣ b² + n}`.
* `latticeCount (A,B,C) X = #{(x,y) ∈ ℤ² \ {0} : A x² + 2B xy + C y² ≤ X}`.
* `τ(n)` = number of divisors, `ω(n)` = number of prime factors.

## 1. The chain

**(E) Elementary.**
1. `HasTriple m → HasTriple (t² m)` (scale the triple by `t`).
2. *Step B.* For a prime `p ≥ 47` and `1 ≤ m ≤ 1848`: `HasStrictForm (p² m)`.
   Take `λ ∈ {1, 2}`, `A = 1 + m λ²`, `r = (m λ p) mod A`, `B = min(r, A - r)`, `C = (p² m + B²)/A`.
   Then `B² ≡ (mλp)² ≡ -m p² (mod A)` because `m λ² ≡ -1`, so `A ∣ p² m + B²`.
   `B > 0` iff `A ∤ p` (as `gcd(A, mλ) = 1`), `2B ≠ A` if `A ∤ 2p`, and `A < C` if `A² < p² m`.
   For `p ≥ 47`, `m ≤ 1848`: `λ = 1` works unless `1 + m ∈ {2, p, 2p}`, and then `λ = 2` works
   (`(1+m)² < p² m` since `(1+m)/√m ≤ 43.1`; in the bad cases `m ≥ 46` or `m = 1`, and then
   `(1+4m)² < p² m` and `1 + 4m ∉ {p, 2p}`).

**(C) Character.** Facts about `chiZ`, `chi`, `gZ` listed in §0, plus
`|∑_{d=1}^{N} chiZ n d| ≤ n` (period `4n`, zero sum over a period, even terms vanish), and for an odd
prime `p ∤ n`: `chiZ n p = 1 ↔ -n` is a square mod `p`.

**(R) Roots.** `gZ n k ≤ ∑_{e ≥ 1, e² ∣ k} rho n (k / e²)` for `n, k ≥ 1`.
Both sides are multiplicative in `k` (CRT for `rho`). At a prime power `p^j`:
* `chiZ n p = 0` (`p ∣ 2n`): left side is `1`; the right side contains `rho n 1 = 1` (`j` even) or
  `rho n p ≥ 1` (`j` odd; `b = 0` if `p ∣ n`, `b = 1` if `p = 2 ∤ n`).
* `chiZ n p = -1`: left side is `1` (`j` even) or `0` (`j` odd); right side contains `rho n 1` for even `j`.
* `chiZ n p = 1`: left side is `j + 1`; `rho n (p^l) ≥ 2` for `l ≥ 1` by lifting the two roots mod `p`
  (`p ∤ 2n`), so the right side is at least `j + 1`.

**(F) Forms.** Integer forms `(a, b, c)` meaning `a x² + 2b xy + c y²`, `a > 0`, `a c - b² = n`.
`SL₂(ℤ)` acts by substitution; the determinant is preserved.
1. *Reduction.* Every such form is equivalent to one with `2|b| ≤ a ≤ c`
   (translate `x ↦ x + t y` to get `2|b| ≤ a`; if `a > c` swap `(x,y) ↦ (y,-x)`; induct on `a`).
2. If `¬ HasStrictForm n`, a reduced form has `b = 0` or `2|b| = a` or `a = c`
   (otherwise `(a, |b|, c)` is a strict form). One more substitution makes `b ≥ 0`.
   So every form is equivalent to an element of `ambiguousForms n`:
   natural triples `(A,B,C)`, `A C = n + B²`, `2B ≤ A ≤ C`, `0 < A`, and (`B = 0` or `2B = A` or `A = C`).
3. `#ambiguousForms n ≤ τ(n)`: `(A,0,C) ↦ A` (a divisor with `A² ≤ n`);
   `(2u, u, C) ↦ v = 2C - u` and `(A,B,A) ↦ v = A + B` (divisors with `v² > n`; the two families are
   separated by `v ≥ 3u` versus `v < 3u`, where `u = n / v`).
4. *Counting.* For `X : ℕ` let `T(X) = {(e, m, b) : e, m ≥ 1, e² m ≤ X, b < m, m ∣ b² + n}`, so
   `#T(X) = ∑_{k ≤ X} ∑_{e² ∣ k} rho n (k/e²)`. Send `(e, m, b)` to `(F, (e x, e y))`, where the form
   `f₀ = (m, b, (b²+n)/m)` equals `F ∘ δ` with `F ∈ ambiguousForms n`, `δ ∈ SL₂(ℤ)` (chosen once),
   and `(x, y)` is the first column of `δ`. Then `F(ex, ey) = e² m ≤ X`.
   The map is injective, and its image never contains both `P` and `-P` for the same `F`
   (from `(F, (x,y))` one recovers `m = F(x,y)` and `b mod m`, because the middle coefficient of
   `F ∘ δ` depends on the second column of `δ` only modulo `m`). Hence
   `2 · #T(X) ≤ ∑_{F ∈ ambiguousForms n} latticeCount F X`.

**(Lat) Lattice points.** For `A C = n + B²`, `2B ≤ A ≤ C`, `0 < A`, `n ≥ 1`, `X : ℕ`:
`latticeCount (A,B,C) X ≤ π X / √n + 5 √X + 5`.
For fixed `y` the admissible `x` satisfy `(A x + B y)² ≤ A X - n y²`: at most
`(2/A) √(A X - n y²) + 1` integers. Sum over `|y| ≤ R = √(A X / n)` and compare the sum of the
even, unimodal function with its integral: `∑_y (2/A)√(A X - n y²) ≤ 2√(X/A) + π X/√n`.

**(Ab) Abel summation, abstract.** (No separate module: `Pintz.lean` and `LBridge.lean` each prove
the form they need.) For `a : ℕ → ℝ` with `|∑_{d=1}^{N} a d| ≤ M` for all `N` and `σ > 0`:
the partial sums of `∑ a d / d^σ` converge, and `|limit - ∑_{d ≤ N}| ≤ 2M / (N+1)^σ`. Also the monotone
weight inequality: for `w` nonnegative and antitone on `(Y, X]`: `|∑_{Y<d≤X} a d · w d| ≤ 2 M w(Y+1)`.

**(LB) Bridge to Mathlib's `LFunction`.** For `σ > 0` real:
`(chi n).LFunction σ` is real and equals `lim_N ∑_{d ≤ N} chiZ n d / d^σ`.
(`s ↦ s ∫_1^∞ S(t) t^{-s-1} dt` is analytic on `Re s > 0`, agrees with the L-series for `Re s > 1`;
identity theorem; `chi n ≠ 1` so `LFunction` is entire.) Under `NoRealZeros`:
`Lreal n σ > 0` for `19/20 ≤ σ ≤ 1` (positive at `σ = 2`, no zero on `[σ, 2]`, intermediate values).

**(P) Pintz-type inequality, abstract.** Data: `a : ℕ → ℝ`, `|a d| ≤ 1`, partial sums bounded by `M ≥ 10⁶`,
`g k = ∑_{d ∣ k} a d ≥ 0`, `g(j²) ≥ 1`, `L σ = lim ∑ a d / d^σ` for `σ > 0`, and `L σ ≥ 0` on `[19/20, 1)`.
1. `∑_{k ≤ X} g k ≥ X · L 1 - (4M + 1) √X` for `X : ℕ` (hyperbola split at `√X`).
2. `L 1 ≥ 1 / (2 (log M + 16))`.
   With `0 < β < 1`, `H(y) = ∑_{m ≤ y} m^{-β} = y^{1-β}/(1-β) - Δ + r(y)`, `Δ > 0`, `0 ≤ r(y) ≤ y^{-β}` (integer `y`),
   and `G(X) = ∑_{k ≤ X} g k · k^{-β}`:
   `G(X) ≤ X^{1-β} L 1 /(1-β) - Δ · L β + Err`, `Err ≤ 4 M X^{1-β} / (Y (1-β)) + 2 M Δ Y^{-β} + c₁ Y X^{-β}`,
   `Δ ≤ 1/(1-β)`. Since `Δ · L β ≥ 0` and `G(X) ≥ ∑_{j ≤ 10} j^{-2} > 1.549`:
   `L 1 ≥ (1-β) X^{β-1} (1.549 - Err)`. Take `β = 1 - 1/log X`, `Y ≈ 400 M log X`, `X ≈ 180 Y`.
   Then `Err < 0.1`, `β ≥ 19/20`, and `(1.449/e)/log X ≥ 1/(2(log M + 16))` with a wide margin.

**(A) Analytic bound.** For `n ≥ 10⁶` with `¬ HasStrictForm n`, under `NoRealZeros`:
`√n ≤ π · τ(n) · (log n + 16)`.
From (R), (F), (Lat), (P1) with `a = chiZ n`, `M = n`: for every `X`,
`2 (X L1 - (4n+1)√X) ≤ τ(n) (π X/√n + 5√X + 5)`; let `X → ∞`: `2 L1 ≤ π τ(n)/√n`. Then use (P2).

**(T) Thresholds.** For squarefree `n ≥ 4·10⁶`, `τ(n) = 2^{ω(n)}`. The inequality of (A) forces
`ω = 5, n < 1.3·10⁷` or `ω = 6, n < 5·10⁷` or `ω = 7, n < 2.1·10⁸` or `ω = 8, n < 9·10⁸`
or `ω = 9, n < 3.9·10⁹` or `ω = 10, n < 1.7·10¹⁰` (the bounds used in `Threshold.lean` and
`Compute.lean`; slightly looser than the sharp crossing points, to leave room in the numerics).
(`ω ≤ 4`: `√n > 16π(log n + 16)` for `n ≥ 4·10⁶`. `ω ≥ 11`: `n ≥ 2·3·…·31` and induction.)

**(K) Kernel computations.**
* `small_range`: every `0 < n < 4·10⁶` outside the list has a triple.
* `high_omega`: every squarefree `n ≥ 4·10⁶` in one of the six classes of (T) has a triple
  (verified enumeration of squarefree numbers with exactly `k` prime factors below a bound).

**(M) Main.** Strong induction on `n`: for `n > 0`, `n ∉ knownIdonealNumbers`, show `HasTriple n`.
* `n < 4·10⁶`: `small_range`.
* `n ≥ 4·10⁶`, not squarefree: `p² ∣ n`, `m = n/p²`. If `m ∈ knownIdonealNumbers` then `m ≤ 1848`,
  `p² ≥ 2164`, so `p ≥ 47`: Step B. Otherwise the induction hypothesis gives a triple for `m`; scale it.
* `n ≥ 4·10⁶`, squarefree: if there were no strict form, (A) and (T) put `n` in a class of `high_omega`.

## 2. Modules and interfaces

All shared definitions are in `Idoneal/Defs.lean`. The statements listed in §1 are the interfaces
between the modules of `Idoneal/`; everything else in a module is auxiliary.

| file | content |
|---|---|
| `Defs.lean` | definitions |
| `Elementary.lean` | (E) |
| `Character.lean` | (C) |
| `Roots.lean` | (R) |
| `Forms.lean` | (F) |
| `Lattice.lean` | (Lat) |
| `LBridge.lean` | (LB) |
| `Pintz.lean` | (P), including its own Abel summation |
| `Analytic.lean` | (A) |
| `Threshold.lean` | (T) |
| `ComputeCore.lean` | (K): Boolean checkers, their soundness, and the assembly theorems |
| `ComputeRuns/*` | (K): one `decide +kernel` fact per file; the long runs |
| `Compute.lean` | (K): `small_range` and `high_omega`, from the runs |
| `Converse.lean` | the 65 listed numbers are idoneal (no hypothesis; a finite kernel check) |
| `Main.lean` | (M), the corollaries for a zero-free half-plane, and the "if and only if" forms |

## 3. The unconditional statement

`IdonealUnconditional.lean` (at the root of the repository) imports `Idoneal.Main` and
`Transport.Nonvanishing` (project `quasi-riemann-improved`, package `RHTransport`, in `vendor/`)
and proves, in one line each,

```lean
theorem idoneal_numbers_completeness :
    ∀ n : ℕ, Idoneal.IsIdoneal n → n ∈ Idoneal.knownIdonealNumbers
theorem isIdoneal_iff_mem_knownIdonealNumbers (n : ℕ) :
    Idoneal.IsIdoneal n ↔ n ∈ Idoneal.knownIdonealNumbers
```

The first is `Idoneal.idoneal_numbers_completeness_of_dirichlet_nonvanishing` applied to
`RH.Transport.dirichlet_nonvanishing`; the hypothesis of the former is, word for word, the
statement of the latter. The second adds `Idoneal.isIdoneal_of_mem_known`.

Only a small part of the zero-free theorem is used: real zeros in `[19/20, 1)` of the characters
`chi n` (the Kronecker-type character `m ↦ J(-n | m)` modulo `4n`).
