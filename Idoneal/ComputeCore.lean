import Idoneal.Defs

/-!
# Kernel-checkable certificates for blueprint §1 (K)

Bool-valued checkers built only from `Nat.rec` (no well-founded recursion) and the
GMP-accelerated kernel primitives (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`,
`Nat.pow`, `Nat.gcd`, `Nat.beq`, `Nat.ble`), their soundness theorems, and the assembly theorems
`small_range_of_runs` and `high_omega_of_runs`, which reduce the two statements of
`Idoneal/Compute.lean` to closed facts `<checker> = true` proved in `Idoneal/ComputeRuns/` by
`decide +kernel`.

Loops are written as `Nat.rec` on a fuel `len`, and the loop variable is recomputed from the fuel
(`x = hi - (k + 1)`), so that the kernel never builds chains `((x + 1) + 1) + ...`.
-/

namespace Idoneal

/-! ## Loop combinators -/

/-- `P x` for all `x ∈ [hi - len, hi)`. -/
noncomputable def allR (P : ℕ → Bool) (hi len : ℕ) : Bool :=
  Nat.rec true (fun k r => P (hi - (k + 1)) && r) len

/-- `P x` for some `x ∈ [hi - len, hi)`. -/
noncomputable def anyR (P : ℕ → Bool) (hi len : ℕ) : Bool :=
  Nat.rec false (fun k r => P (hi - (k + 1)) || r) len

/-- Scan `x = hi - len, ..., hi - 1` upwards; stop with `true` at the first `x` with `S x`;
otherwise require `P x`. -/
noncomputable def allStop (S P : ℕ → Bool) (hi len : ℕ) : Bool :=
  Nat.rec true (fun k r => S (hi - (k + 1)) || (P (hi - (k + 1)) && r)) len

/-! ## The witness search -/

/-- `u ∣ n + a²`, `2a < u`, `u² < n + a²`. -/
def wit (n u a : ℕ) : Bool :=
  Nat.beq ((n + a * a) % u) 0 &&
    (Nat.blt (2 * a) u && Nat.blt (u * u) (n + a * a))

/-- Some `a ∈ [1, f]` is a witness for `(n, u)`. -/
noncomputable def searchA (n u f : ℕ) : Bool := Nat.rec false (fun a r => wit n u (a + 1) || r) f

/-- Some `u ∈ [3, F + 2]` and `a ∈ [1, (u-1)/2]` form a witness. -/
noncomputable def searchU (n F : ℕ) : Bool :=
  Nat.rec false (fun k r => searchA n (F + 3 - (k + 1)) ((F + 3 - (k + 1) - 1) / 2) || r) F

/-- Same, restricted to `u` coprime to `n` (a fast first pass). -/
noncomputable def searchUc (n F : ℕ) : Bool :=
  Nat.rec false (fun k r => (Nat.beq (Nat.gcd (F + 3 - (k + 1)) n) 1 &&
    searchA n (F + 3 - (k + 1)) ((F + 3 - (k + 1) - 1) / 2)) || r) F

/-- The witness search for `n`: first `u` coprime to `n`, then all `u`. -/
noncomputable def search (n : ℕ) : Bool := searchUc n n || searchU n n

/-! ## `small_range` checker -/

/-- The 65 known idoneal numbers, as a list. -/
def knownList : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848]

def knownB (n : ℕ) : Bool := knownList.any (Nat.beq n)

/-- `n = 0`, or `n` is in the list, or the search succeeds. -/
noncomputable def checkOne (n : ℕ) : Bool :=
  Nat.beq n 0 || (Nat.ble n 1848 && knownB n) || searchU n n

/-- `checkOne` on `[lo, lo + len)`: split in halves `d` times, then a linear loop. -/
noncomputable def rng (d lo len : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun lo len => allR checkOne (lo + len) len)
    (fun _ r lo len => r lo (len / 2) && r (lo + len / 2) (len - len / 2)) d lo len

/-! ## `high_omega` checker -/

/-- A filter that is `true` on every prime (trial division while `d² ≤ p`). -/
noncomputable def isPrimeB (p : ℕ) : Bool :=
  Nat.ble 2 p && allStop (fun d => Nat.blt p (d * d)) (fun d => !(Nat.beq (p % d) 0)) (p + 2) p

/-- A cheap filter that is `true` on every prime: `q ≤ 23` or `q` coprime to `2·3·…·23`. -/
def filt (q : ℕ) : Bool := Nat.ble q 23 || Nat.beq (Nat.gcd q 223092870) 1

/-- The search succeeds on `acc * q` for `q ∈ [q0, q0 + len)` passing `filt` with `acc * q < B`. -/
noncomputable def leaf (acc B q0 len : ℕ) : Bool :=
  allStop (fun q => Nat.ble B (acc * q)) (fun q => !(filt q) || search (acc * q)) (q0 + len) len

/-- For `p ∈ [lo, hi)` with `acc * p ^ e < B` and `isPrimeB p`: `g (p+1) (acc*p)`. -/
noncomputable def loopP (g : ℕ → ℕ → Bool) (e acc B lo hi : ℕ) : Bool :=
  allStop (fun p => Nat.ble B (acc * p ^ e)) (fun p => !(isPrimeB p) || g (p + 1) (acc * p))
    hi (hi - lo)

def bmax (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

/-- The leaf level of `goodB`. -/
noncomputable def goodLeaf (B lo acc : ℕ) : Bool :=
  leaf acc B (bmax lo ((4000000 + acc - 1) / acc))
    (B / acc + 1 - bmax lo ((4000000 + acc - 1) / acc))

/-- `goodB B j lo acc` certifies `Good (j+1) lo acc B`. -/
noncomputable def goodB (B j : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (goodLeaf B)
    (fun j g lo acc => loopP g (j + 2) acc B lo B) j

/-- The primes `p ∈ [lo, hi)` of the top loop of `goodB B (j+1) _ acc`. -/
noncomputable def segB (B j acc lo hi : ℕ) : Bool := loopP (goodB B j) (j + 2) acc B lo hi


/-! ## Soundness: loop combinators -/

theorem allR_succ (P : ℕ → Bool) (hi k : ℕ) :
    allR P hi (k + 1) = (P (hi - (k + 1)) && allR P hi k) := rfl

theorem anyR_succ (P : ℕ → Bool) (hi k : ℕ) :
    anyR P hi (k + 1) = (P (hi - (k + 1)) || anyR P hi k) := rfl

theorem allStop_succ (S P : ℕ → Bool) (hi k : ℕ) :
    allStop S P hi (k + 1) = (S (hi - (k + 1)) || (P (hi - (k + 1)) && allStop S P hi k)) := rfl

theorem allR_sound {P : ℕ → Bool} {hi len : ℕ} (h : allR P hi len = true) :
    ∀ x, hi - len ≤ x → x < hi → P x = true := by
  induction len with
  | zero => intro x h1 h2; omega
  | succ k ih =>
    rw [allR_succ, Bool.and_eq_true] at h
    intro x h1 h2
    by_cases hx : hi - k ≤ x
    · exact ih h.2 x hx h2
    · have : x = hi - (k + 1) := by omega
      rw [this]; exact h.1

theorem anyR_sound {P : ℕ → Bool} {hi len : ℕ} (h : anyR P hi len = true) :
    ∃ x, P x = true := by
  induction len with
  | zero => exact absurd h (by simp [anyR])
  | succ k ih =>
    rw [anyR_succ, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨_, h⟩
    · exact ih h

theorem allStop_sound {S P : ℕ → Bool} (hS : ∀ y z, y ≤ z → S y = true → S z = true)
    {hi len : ℕ} (h : allStop S P hi len = true) :
    ∀ x, hi - len ≤ x → x < hi → S x = false → P x = true := by
  induction len with
  | zero => intro x h1 h2; omega
  | succ k ih =>
    rw [allStop_succ, Bool.or_eq_true, Bool.and_eq_true] at h
    intro x h1 h2 h3
    rcases h with h | h
    · have := hS _ x (by omega) h
      rw [h3] at this; exact absurd this (by simp)
    · by_cases hx : hi - k ≤ x
      · exact ih h.2 x hx h2 h3
      · have : x = hi - (k + 1) := by omega
        rw [this]; exact h.1

theorem allStop_complete {S P : ℕ → Bool} {hi len : ℕ} (hlen : len ≤ hi)
    (h : ∀ x, hi - len ≤ x → x < hi → S x = true ∨ P x = true) :
    allStop S P hi len = true := by
  induction len with
  | zero => rfl
  | succ k ih =>
    rw [allStop_succ, Bool.or_eq_true, Bool.and_eq_true]
    rcases h (hi - (k + 1)) (by omega) (by omega) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1, ih (by omega) fun x hx1 hx2 => h x (by omega) hx2⟩

/-! ## Soundness: the witness search -/

theorem wit_sound {n u a : ℕ} (ha : 0 < a) (h : wit n u a = true) : HasTriple n := by
  simp only [wit, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨hmod, h2a, huu⟩ := h
  obtain ⟨v, hv⟩ : u ∣ n + a * a := Nat.dvd_of_mod_eq_zero hmod
  have huv : u < v := by
    by_contra hc
    have : u * v ≤ u * u := Nat.mul_le_mul_left u (by omega)
    omega
  obtain ⟨b, rfl⟩ : ∃ b, u = a + b := ⟨u - a, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, v = a + c := ⟨v - a, by omega⟩
  refine ⟨a, b, c, by omega, by omega, by omega, ?_⟩
  have : (a + b) * (a + c) = a * a + (a * b + b * c + a * c) := by ring
  omega

theorem searchA_sound {n u f : ℕ} (h : searchA n u f = true) : HasTriple n := by
  induction f with
  | zero => exact absurd h (by simp [searchA])
  | succ a ih =>
    have e : searchA n u (a + 1) = (wit n u (a + 1) || searchA n u a) := rfl
    rw [e, Bool.or_eq_true] at h
    rcases h with h | h
    · exact wit_sound (Nat.succ_pos a) h
    · exact ih h

theorem searchU_sound {n F : ℕ} (h : searchU n F = true) : HasTriple n := by
  have e : searchU n F = anyR (fun u => searchA n u ((u - 1) / 2)) (F + 3) F := rfl
  rw [e] at h
  obtain ⟨u, hu⟩ := anyR_sound h
  exact searchA_sound hu

theorem searchUc_sound {n F : ℕ} (h : searchUc n F = true) : HasTriple n := by
  have e : searchUc n F =
      anyR (fun u => Nat.beq (Nat.gcd u n) 1 && searchA n u ((u - 1) / 2)) (F + 3) F := rfl
  rw [e] at h
  obtain ⟨u, hu⟩ := anyR_sound h
  rw [Bool.and_eq_true] at hu
  exact searchA_sound hu.2

theorem search_sound {n : ℕ} (h : search n = true) : HasTriple n := by
  rw [search, Bool.or_eq_true] at h
  rcases h with h | h
  · exact searchUc_sound h
  · exact searchU_sound h

/-! ## Soundness: `small_range` -/

theorem knownB_sound {n : ℕ} (h : knownB n = true) : n ∈ knownIdonealNumbers := by
  rw [knownB, List.any_eq_true] at h
  obtain ⟨x, hx, hnx⟩ := h
  rw [Nat.beq_eq] at hnx
  subst hnx
  have key : ∀ y ∈ knownList, y ∈ knownIdonealNumbers := by decide +kernel
  exact key _ hx

theorem checkOne_sound {n : ℕ} (h : checkOne n = true) (h0 : 0 < n)
    (hnot : n ∉ knownIdonealNumbers) : HasTriple n := by
  simp only [checkOne, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with (h | h) | h
  · omega
  · exact absurd (knownB_sound h.2) hnot
  · exact searchU_sound h

theorem rng_succ (d lo len : ℕ) :
    rng (d + 1) lo len = (rng d lo (len / 2) && rng d (lo + len / 2) (len - len / 2)) := rfl

theorem rng_sound {d lo len : ℕ} (h : rng d lo len = true) :
    ∀ n, lo ≤ n → n < lo + len → checkOne n = true := by
  induction d generalizing lo len with
  | zero =>
    intro n h1 h2
    exact allR_sound (P := checkOne) (hi := lo + len) (len := len) h n (by omega) h2
  | succ d ih =>
    rw [rng_succ, Bool.and_eq_true] at h
    intro n h1 h2
    by_cases hn : n < lo + len / 2
    · exact ih h.1 n h1 hn
    · exact ih h.2 n (by omega) (by omega)

/-- **Assembly theorem for `small_range`.** -/
theorem small_range_of_runs (h : ∀ i, i < 80 → rng 12 (i * 50000) 50000 = true)
    {n : ℕ} (h0 : 0 < n) (hn : n < 4000000) (hnot : n ∉ knownIdonealNumbers) : HasTriple n := by
  have hi : n / 50000 < 80 := by omega
  refine checkOne_sound (rng_sound (h _ hi) n ?_ ?_) h0 hnot
  · have := Nat.div_mul_le_self n 50000; omega
  · have := Nat.lt_div_mul_add (a := n) (b := 50000) (by norm_num); omega

/-! ## Soundness: prime filters -/

theorem isPrimeB_of_prime {p : ℕ} (hp : p.Prime) : isPrimeB p = true := by
  rw [isPrimeB, Bool.and_eq_true, Nat.ble_eq]
  refine ⟨hp.two_le, allStop_complete (by omega) fun d h1 h2 => ?_⟩
  simp only [Nat.blt_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.beq_eq]
  by_cases hdd : p < d * d
  · exact Or.inl hdd
  · right
    have hd2 : 2 ≤ d := by omega
    intro hmod
    have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases (Nat.dvd_prime hp).1 hdvd with hd | hd
    · omega
    · rw [hd] at hd2 hdd
      have : p * 2 ≤ p * p := Nat.mul_le_mul_left p hd2
      omega

theorem filt_of_prime {q : ℕ} (hq : q.Prime) : filt q = true := by
  rw [filt, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq]
  by_cases h23 : q ≤ 23
  · exact Or.inl h23
  · right
    rw [← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd hq]
    intro hd
    have h : (223092870 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 := by norm_num
    rw [h] at hd
    simp only [Nat.Prime.dvd_mul hq] at hd
    rcases hd with ((((((((hd | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) <;>
      exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)

/-! ## Soundness: `high_omega` -/

/-- Every squarefree `m` with `k` prime factors, all `≥ lo`, with `4·10⁶ ≤ acc * m < B`, gives
a triple for `acc * m`. -/
def Good (k lo acc B : ℕ) : Prop :=
  ∀ m, Squarefree m → m.primeFactors.card = k → (∀ p, p.Prime → p ∣ m → lo ≤ p) →
    4000000 ≤ acc * m → acc * m < B → HasTriple (acc * m)

theorem leaf_sound {acc B q0 len : ℕ} (h : leaf acc B q0 len = true) :
    ∀ q, q0 ≤ q → q < q0 + len → acc * q < B → q.Prime → HasTriple (acc * q) := by
  intro q h1 h2 h3 hq
  have hS : ∀ y z, y ≤ z → Nat.ble B (acc * y) = true → Nat.ble B (acc * z) = true := by
    intro y z hyz hy
    rw [Nat.ble_eq] at hy ⊢
    exact le_trans hy (Nat.mul_le_mul_left acc hyz)
  have := allStop_sound hS h q (by omega) h2 (by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega)
  rw [Bool.or_eq_true, filt_of_prime hq] at this
  rcases this with h | h
  · exact absurd h (by simp)
  · exact search_sound h

theorem loopP_sound {g : ℕ → ℕ → Bool} {e acc B lo hi : ℕ} (h : loopP g e acc B lo hi = true) :
    ∀ p, lo ≤ p → p < hi → p.Prime → acc * p ^ e < B → g (p + 1) (acc * p) = true := by
  intro p h1 h2 hp h3
  have hS : ∀ y z, y ≤ z → Nat.ble B (acc * y ^ e) = true → Nat.ble B (acc * z ^ e) = true := by
    intro y z hyz hy
    rw [Nat.ble_eq] at hy ⊢
    exact le_trans hy (Nat.mul_le_mul_left acc (Nat.pow_le_pow_left hyz e))
  have := allStop_sound hS h p (by omega) h2 (by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega)
  rw [Bool.or_eq_true, isPrimeB_of_prime hp] at this
  rcases this with h | h
  · exact absurd h (by simp)
  · exact h

theorem bmax_le {a b x : ℕ} (ha : a ≤ x) (hb : b ≤ x) : bmax a b ≤ x := by
  unfold bmax
  cases h : Nat.ble a b <;> simpa [h]

theorem good_zero_acc (k lo B : ℕ) : Good k lo 0 B := by
  intro m _ _ _ h4
  omega

theorem goodLeaf_sound {B lo acc : ℕ} (h : goodLeaf B lo acc = true) : Good 1 lo acc B := by
  intro m hsf hcard hlo h4 hB
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hcard
  have hm : q = m := by
    symm
    rw [← Nat.prod_primeFactors_of_squarefree hsf, hq, Finset.prod_singleton]
  have hqm : q ∈ m.primeFactors := by rw [hq]; exact Finset.mem_singleton_self q
  rw [Nat.mem_primeFactors] at hqm
  subst hm
  have hacc : 0 < acc := by
    rcases Nat.eq_zero_or_pos acc with h0 | h0
    · subst h0; omega
    · exact h0
  have hc : (4000000 + acc - 1) / acc ≤ q := by
    have : (4000000 + acc - 1) / acc < q + 1 := by
      rw [Nat.div_lt_iff_lt_mul hacc]
      have : acc * q = q * acc := Nat.mul_comm _ _
      rw [Nat.add_mul, one_mul]; omega
    omega
  have hqB : q ≤ B / acc := by
    rw [Nat.le_div_iff_mul_le hacc, Nat.mul_comm]; omega
  have h0 : bmax lo ((4000000 + acc - 1) / acc) ≤ q := bmax_le (hlo q hqm.1 dvd_rfl) hc
  exact leaf_sound h q h0 (by omega) hB hqm.1

theorem good_step {k lo acc B : ℕ}
    (hstep : ∀ p, p.Prime → lo ≤ p → acc * p ^ (k + 1) < B → Good k (p + 1) (acc * p) B) :
    Good (k + 1) lo acc B := by
  intro m hsf hcard hlo h4 hB
  have hm0 : m ≠ 0 := hsf.ne_zero
  have hm1 : m ≠ 1 := by
    rintro rfl; simp at hcard
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  obtain ⟨m', hm'⟩ : p ∣ m := Nat.minFac_dvd m
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm'; exact hm0 hm'
  have hsf' : Squarefree m' := hsf.squarefree_of_dvd ⟨p, by rw [hm', Nat.mul_comm]⟩
  have hpm' : ¬ p ∣ m' := by
    rintro ⟨t, ht⟩
    have := hsf p ⟨t, by rw [hm', ht, Nat.mul_assoc]⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hpf : m.primeFactors = insert p m'.primeFactors := by
    rw [hm', Nat.primeFactors_mul hp.ne_zero hm'0, hp.primeFactors]; rfl
  have hcard' : m'.primeFactors.card = k := by
    rw [hpf, Finset.card_insert_of_notMem (fun h => hpm' (Nat.dvd_of_mem_primeFactors h))] at hcard
    omega
  have hbig : ∀ r, r.Prime → r ∣ m' → p + 1 ≤ r := by
    intro r hr hrd
    have h1 : p ≤ r := Nat.minFac_le_of_dvd hr.two_le (dvd_trans hrd ⟨p, by rw [hm', Nat.mul_comm]⟩)
    have h2 : r ≠ p := by rintro rfl; exact hpm' hrd
    omega
  have hpow : p ^ (k + 1) ≤ m := by
    have : p ^ k ≤ m' := by
      have h := Finset.pow_card_le_prod m'.primeFactors (fun r => r) p (fun r hr => by
        have := Nat.mem_primeFactors.1 hr
        have := hbig r this.1 this.2.1
        omega)
      rw [hcard', Nat.prod_primeFactors_of_squarefree hsf'] at h
      exact h
    rw [hm', pow_succ, Nat.mul_comm (p ^ k)]
    exact Nat.mul_le_mul_left p this
  have hpB : acc * p ^ (k + 1) < B := lt_of_le_of_lt (Nat.mul_le_mul_left acc hpow) hB
  have hlop : lo ≤ p := hlo p hp (Nat.minFac_dvd m)
  have key := hstep p hp hlop hpB m' hsf' hcard' hbig
  have heq : acc * m = acc * p * m' := by rw [hm', Nat.mul_assoc]
  rw [heq] at h4 hB ⊢
  exact key h4 hB

theorem goodB_succ (B j lo acc : ℕ) :
    goodB B (j + 1) lo acc = loopP (goodB B j) (j + 2) acc B lo B := rfl

theorem goodB_sound {B j lo acc : ℕ} (h : goodB B j lo acc = true) : Good (j + 1) lo acc B := by
  induction j generalizing lo acc with
  | zero => exact goodLeaf_sound h
  | succ j ih =>
    rw [goodB_succ] at h
    refine good_step fun p hp hlo hpB => ?_
    by_cases hpB' : p < B
    · exact ih (loopP_sound h p hlo hpB' hp hpB)
    · have hacc : acc = 0 := by
        by_contra hne
        have : p ≤ acc * p ^ (j + 1 + 1) :=
          le_trans (Nat.le_self_pow (by omega) p) (Nat.le_mul_of_pos_left _ (by omega))
        omega
      subst hacc
      rw [Nat.zero_mul]; exact good_zero_acc _ _ _

/-- The primes `p ∈ [lo, hi)` below the top loop of a `Good (j+2) _ acc B` node are handled. -/
def Cov (B j acc lo hi : ℕ) : Prop :=
  ∀ p, p.Prime → lo ≤ p → p < hi → acc * p ^ (j + 2) < B → Good (j + 1) (p + 1) (acc * p) B

theorem cov_of_segB {B j acc lo hi : ℕ} (h : segB B j acc lo hi = true) : Cov B j acc lo hi :=
  fun p hp h1 h2 h3 => goodB_sound (loopP_sound h p h1 h2 hp h3)

theorem cov_of_good {B j acc p : ℕ} (h : Good (j + 1) (p + 1) (acc * p) B) :
    Cov B j acc p (p + 1) := by
  intro r _ h1 h2 _
  obtain rfl : r = p := by omega
  exact h

theorem cov_trans {B j acc a b c : ℕ} (h1 : Cov B j acc a b) (h2 : Cov B j acc b c) :
    Cov B j acc a c := by
  intro p hp ha hc hB
  by_cases hb : p < b
  · exact h1 p hp ha hb hB
  · exact h2 p hp (by omega) hc hB

theorem good_of_cov {B j acc lo : ℕ} (h : Cov B j acc lo B) : Good (j + 2) lo acc B := by
  refine good_step fun p hp hlo hpB => ?_
  by_cases hpB' : p < B
  · exact h p hp hlo hpB' hpB
  · have hacc : acc = 0 := by
      by_contra hne
      have : p ≤ acc * p ^ (j + 1 + 1) :=
        le_trans (Nat.le_self_pow (by omega) p) (Nat.le_mul_of_pos_left _ (by omega))
      omega
    subst hacc
    rw [Nat.zero_mul]; exact good_zero_acc _ _ _

theorem hasTriple_of_good {k B n : ℕ} (h : Good k 2 1 B) (hsf : Squarefree n)
    (hk : n.primeFactors.card = k) (hn : 4000000 ≤ n) (hB : n < B) : HasTriple n := by
  have := h n hsf hk (fun p hp _ => hp.two_le) (by omega) (by omega)
  rwa [one_mul] at this


/-! ## Assembly for `high_omega`

The split of the enumerations into pieces (`segB` facts) follows the planned cost of each piece;
heavy single primes `p` are handled by a node `Good (j+1) (p+1) (acc*p) B` built one level
deeper. -/

theorem good5_of_runs
    (a1 : segB 13000000 0 30 6 79 = true) (a2 : segB 13000000 0 30 79 13000000 = true)
    (a3 : segB 13000000 1 6 4 5 = true) (a4 : segB 13000000 1 6 6 11 = true)
    (a5 : segB 13000000 1 6 11 29 = true) (a6 : segB 13000000 1 6 29 13000000 = true)
    (a7 : segB 13000000 1 10 6 37 = true) (a8 : segB 13000000 1 10 37 13000000 = true)
    (a9 : segB 13000000 2 2 4 5 = true) (a10 : segB 13000000 2 2 6 13000000 = true)
    (a11 : segB 13000000 2 3 4 7 = true) (a12 : segB 13000000 2 3 7 13000000 = true)
    (a13 : segB 13000000 3 1 4 13000000 = true) :
    Good 5 2 1 13000000 := by
  have g2_6_30 : Good 2 6 30 13000000 :=
    good_of_cov (cov_trans (cov_of_segB a1) (cov_of_segB a2))
  have g3_4_6 : Good 3 4 6 13000000 :=
    good_of_cov (cov_trans (cov_of_segB a3) (cov_trans
      (cov_of_good (j := 1) (acc := 6) (p := 5) g2_6_30 : Cov 13000000 1 6 5 6)
      (cov_trans (cov_of_segB a4) (cov_trans (cov_of_segB a5) (cov_of_segB a6)))))
  have g3_6_10 : Good 3 6 10 13000000 :=
    good_of_cov (cov_trans (cov_of_segB a7) (cov_of_segB a8))
  have g4_3_2 : Good 4 3 2 13000000 :=
    good_of_cov (cov_trans
      (cov_of_good (j := 2) (acc := 2) (p := 3) g3_4_6 : Cov 13000000 2 2 3 4)
      (cov_trans (cov_of_segB a9) (cov_trans
        (cov_of_good (j := 2) (acc := 2) (p := 5) g3_6_10 : Cov 13000000 2 2 5 6)
        (cov_of_segB a10))))
  have g4_4_3 : Good 4 4 3 13000000 :=
    good_of_cov (cov_trans (cov_of_segB a11) (cov_of_segB a12))
  exact good_of_cov (cov_trans
    (cov_of_good (j := 3) (acc := 1) (p := 2) g4_3_2 : Cov 13000000 3 1 2 3)
    (cov_trans (cov_of_good (j := 3) (acc := 1) (p := 3) g4_4_3 : Cov 13000000 3 1 3 4)
      (cov_of_segB a13)))

theorem good6_of_runs
    (b1 : segB 50000000 0 210 8 193 = true) (b2 : segB 50000000 0 210 193 50000000 = true)
    (b3 : segB 50000000 1 30 6 7 = true) (b4 : segB 50000000 1 30 8 17 = true)
    (b5 : segB 50000000 1 30 17 50000000 = true)
    (b6 : segB 50000000 1 42 8 47 = true) (b7 : segB 50000000 1 42 47 50000000 = true)
    (b8 : segB 50000000 2 6 4 5 = true) (b9 : segB 50000000 2 6 6 7 = true)
    (b10 : segB 50000000 2 6 8 50000000 = true)
    (b11 : segB 50000000 3 2 4 7 = true) (b12 : segB 50000000 3 2 7 50000000 = true)
    (b13 : segB 50000000 4 1 3 50000000 = true) :
    Good 6 2 1 50000000 := by
  have g2_8_210 : Good 2 8 210 50000000 :=
    good_of_cov (cov_trans (cov_of_segB b1) (cov_of_segB b2))
  have g3_6_30 : Good 3 6 30 50000000 :=
    good_of_cov (cov_trans (cov_of_segB b3) (cov_trans
      (cov_of_good (j := 1) (acc := 30) (p := 7) g2_8_210 : Cov 50000000 1 30 7 8)
      (cov_trans (cov_of_segB b4) (cov_of_segB b5))))
  have g3_8_42 : Good 3 8 42 50000000 :=
    good_of_cov (cov_trans (cov_of_segB b6) (cov_of_segB b7))
  have g4_4_6 : Good 4 4 6 50000000 :=
    good_of_cov (cov_trans (cov_of_segB b8) (cov_trans
      (cov_of_good (j := 2) (acc := 6) (p := 5) g3_6_30 : Cov 50000000 2 6 5 6)
      (cov_trans (cov_of_segB b9) (cov_trans
        (cov_of_good (j := 2) (acc := 6) (p := 7) g3_8_42 : Cov 50000000 2 6 7 8)
        (cov_of_segB b10)))))
  have g5_3_2 : Good 5 3 2 50000000 :=
    good_of_cov (cov_trans
      (cov_of_good (j := 3) (acc := 2) (p := 3) g4_4_6 : Cov 50000000 3 2 3 4)
      (cov_trans (cov_of_segB b11) (cov_of_segB b12)))
  exact good_of_cov (cov_trans
    (cov_of_good (j := 4) (acc := 1) (p := 2) g5_3_2 : Cov 50000000 4 1 2 3)
    (cov_of_segB b13))

theorem good7_of_runs
    (c1 : segB 210000000 1 210 8 19 = true) (c2 : segB 210000000 1 210 19 210000000 = true)
    (c3 : segB 210000000 2 30 6 7 = true) (c4 : segB 210000000 2 30 8 210000000 = true)
    (c5 : segB 210000000 3 6 4 5 = true) (c6 : segB 210000000 3 6 6 210000000 = true)
    (c7 : segB 210000000 4 2 4 210000000 = true)
    (c8 : segB 210000000 5 1 3 210000000 = true) :
    Good 7 2 1 210000000 := by
  have g3_8_210 : Good 3 8 210 210000000 :=
    good_of_cov (cov_trans (cov_of_segB c1) (cov_of_segB c2))
  have g4_6_30 : Good 4 6 30 210000000 :=
    good_of_cov (cov_trans (cov_of_segB c3) (cov_trans
      (cov_of_good (j := 2) (acc := 30) (p := 7) g3_8_210 : Cov 210000000 2 30 7 8)
      (cov_of_segB c4)))
  have g5_4_6 : Good 5 4 6 210000000 :=
    good_of_cov (cov_trans (cov_of_segB c5) (cov_trans
      (cov_of_good (j := 3) (acc := 6) (p := 5) g4_6_30 : Cov 210000000 3 6 5 6)
      (cov_of_segB c6)))
  have g6_3_2 : Good 6 3 2 210000000 :=
    good_of_cov (cov_trans
      (cov_of_good (j := 4) (acc := 2) (p := 3) g5_4_6 : Cov 210000000 4 2 3 4)
      (cov_of_segB c7))
  exact good_of_cov (cov_trans
    (cov_of_good (j := 5) (acc := 1) (p := 2) g6_3_2 : Cov 210000000 5 1 2 3)
    (cov_of_segB c8))

/-- **Assembly theorem for `high_omega`.** -/
theorem high_omega_of_runs
    (a1 : segB 13000000 0 30 6 79 = true) (a2 : segB 13000000 0 30 79 13000000 = true)
    (a3 : segB 13000000 1 6 4 5 = true) (a4 : segB 13000000 1 6 6 11 = true)
    (a5 : segB 13000000 1 6 11 29 = true) (a6 : segB 13000000 1 6 29 13000000 = true)
    (a7 : segB 13000000 1 10 6 37 = true) (a8 : segB 13000000 1 10 37 13000000 = true)
    (a9 : segB 13000000 2 2 4 5 = true) (a10 : segB 13000000 2 2 6 13000000 = true)
    (a11 : segB 13000000 2 3 4 7 = true) (a12 : segB 13000000 2 3 7 13000000 = true)
    (a13 : segB 13000000 3 1 4 13000000 = true)
    (b1 : segB 50000000 0 210 8 193 = true) (b2 : segB 50000000 0 210 193 50000000 = true)
    (b3 : segB 50000000 1 30 6 7 = true) (b4 : segB 50000000 1 30 8 17 = true)
    (b5 : segB 50000000 1 30 17 50000000 = true)
    (b6 : segB 50000000 1 42 8 47 = true) (b7 : segB 50000000 1 42 47 50000000 = true)
    (b8 : segB 50000000 2 6 4 5 = true) (b9 : segB 50000000 2 6 6 7 = true)
    (b10 : segB 50000000 2 6 8 50000000 = true)
    (b11 : segB 50000000 3 2 4 7 = true) (b12 : segB 50000000 3 2 7 50000000 = true)
    (b13 : segB 50000000 4 1 3 50000000 = true)
    (c1 : segB 210000000 1 210 8 19 = true) (c2 : segB 210000000 1 210 19 210000000 = true)
    (c3 : segB 210000000 2 30 6 7 = true) (c4 : segB 210000000 2 30 8 210000000 = true)
    (c5 : segB 210000000 3 6 4 5 = true) (c6 : segB 210000000 3 6 6 210000000 = true)
    (c7 : segB 210000000 4 2 4 210000000 = true)
    (c8 : segB 210000000 5 1 3 210000000 = true)
    (d1 : goodB 900000000 7 2 1 = true)
    (e1 : goodB 3900000000 8 2 1 = true)
    (f1 : goodB 17000000000 9 2 1 = true)
    {n : ℕ} (hsf : Squarefree n) (hn : 4000000 ≤ n)
    (h : (n.primeFactors.card = 5 ∧ n < 13000000) ∨
      (n.primeFactors.card = 6 ∧ n < 50000000) ∨
      (n.primeFactors.card = 7 ∧ n < 210000000) ∨
      (n.primeFactors.card = 8 ∧ n < 900000000) ∨
      (n.primeFactors.card = 9 ∧ n < 3900000000) ∨
      (n.primeFactors.card = 10 ∧ n < 17000000000)) : HasTriple n := by
  rcases h with h | h | h | h | h | h
  · exact hasTriple_of_good (good5_of_runs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
      hsf h.1 hn h.2
  · exact hasTriple_of_good (good6_of_runs b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13)
      hsf h.1 hn h.2
  · exact hasTriple_of_good (good7_of_runs c1 c2 c3 c4 c5 c6 c7 c8) hsf h.1 hn h.2
  · exact hasTriple_of_good (goodB_sound d1) hsf h.1 hn h.2
  · exact hasTriple_of_good (goodB_sound e1) hsf h.1 hn h.2
  · exact hasTriple_of_good (goodB_sound f1) hsf h.1 hn h.2


end Idoneal
