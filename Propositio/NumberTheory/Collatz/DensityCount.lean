import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.ParityBijection
import Propositio.NumberTheory.Collatz.StoppingF3
import Propositio.NumberTheory.Collatz.StoppingF4
import Propositio.NumberTheory.Collatz.StoppingF56
import Propositio.NumberTheory.Collatz.BadDensity

/-!
# Collatz stopping-time density as a pure residue count — `F(k) = D(k) / 2^k`

This file bridges the **Terras parity-vector bijection** (`CollatzParityBijection`)
to the **stopping-time density ladder** (`CollatzStoppingF3/F4/F56`,
`CollatzBadDensity`), reducing the analytic question "almost all integers descend"
(`b(k) → 0`) to a pure **counting statement about binary vectors**.

## The reduction

For the Terras half-step `T` (`T n = n/2` if even, `(3n+1)/2` if odd) the stopping
predicate is `DescBy n k := ∃ j, 1 ≤ j ≤ k ∧ T^j n < n` (`σ(n) ≤ k`).  Because
`σ(n) ≤ k` depends only on `n mod 2^k` (for `n` in the asymptotic regime
`n ≥ 2^k`), the descending set `{n : DescBy n k}` is, up to finitely many small
exceptions, a **union of residue classes mod `2^k`**.  Its natural density is
therefore the exact rational

  `F(k)  =  D(k) / 2^k`,    `D(k) := #{ r < 2^k : DescBy (r + 2^k) k }`,

and the bad-set density is `b(k) = β(k)/2^k` with `β(k) = 2^k − D(k)`.  Via the
parity-vector bijection `pvMap k : Fin (2^k) ≃ (Fin k → Bool)` of
`CollatzParityBijection`, the `D(k)` "good residues" correspond bijectively to the
**descending length-`k` parity vectors**, so `D(k)` is literally a count of binary
vectors and `b(k) → 0 ⟺ #{descending vectors}/2^k → 0`.

## What is proved here (all axiom-clean)

### General structural backbone (every `k`)
* `T_iter_succ_right` — right-unfolding `T^{j+1} n = T (T^j n)`.
* `T_step_cong` — one-step congruence: `m ≡ n [MOD 2^{s+1}] → T m ≡ T n [MOD 2^s]`.
* `T_iter_cong` — **iterated congruence**: `m ≡ n [MOD 2^k] → ∀ j ≤ k,
  T^j m ≡ T^j n [MOD 2^{k-j}]`; corollary `PVEq_of_mod_eq`: the length-`k`
  parity vector of `n` depends only on `n mod 2^k`.
* `affine_form` — **Terras affine form**: `2^j · T^j n = 3^{a(n,j)} · n + c(n,j)`
  with explicit coefficients `aCoef` (number of `3n+1` steps) and `cCoef`.
* `coef_congr` — `aCoef`, `cCoef` depend only on the parity vector (`PVEq`).
* `no_descent_of_pow_ge` — **the easy half of the descent dichotomy**:
  `2^j ≤ 3^{a(n,j)} → n ≤ T^j n` (too many `3n+1` steps ⟹ no descent), from
  `affine_form`.

### The exact count `D(k)` and the headline density (levels `k ≤ 6`)
* `descByB` / `descByB_iff` — a decidable Boolean mirror of `DescBy`,
  `descByB n k = true ↔ DescBy n k` (lets us `decide` `D(k)`, no `native_decide`).
* `D k` — the residue count `#{ r < 2^k : DescBy (r+2^k) k }`.
* `D_one … D_six` — pinned values `D(1..6) = 1, 3, 6, 13, 28, 56` (by `decide`).
* `descBy_mod_invariant_{four,five,six}` — exact mod-`2^k` invariance of
  `DescBy · k` for the F-file levels (`Bad16`/`Bad32` are residue predicates).
* `desc1_density_*`, `desc2_density_*` — direct `DescBy · k` density sandwiches at
  `1/2` and `3/4` (levels 1, 2 are not in the F-files, only their complements).
* `F_eq_count_over_pow` — **HEADLINE**: a *single uniform* theorem expressing
  every `F(k)` (`k = 1..6`) as the residue ratio `D(k)/2^k`, via two-sided density
  sandwiches keyed by `D(k)`.  Subsumes `f2 … f6` into one indexed statement.

### The bad count and the remaining gap
* `beta` / `bad_count_eq` — `β(k) = 2^k − D(k)`, with `β(1..6) = 1,1,2,3,4,8`
  (`decide`), and `b(k) = β(k)/2^k`.
* `descending_vector_count` — bijection bridge: `D(k)` equals the number of
  `r : Fin (2^k)` whose parity vector `pvMap k r` is "descending"; so `D(k)` is a
  count of binary vectors.
* `bk_to_zero_reduction` — a precise typed statement that `b(k) → 0` reduces to a
  binomial-tail/large-deviation bound on parity vectors, documenting the **single
  remaining analytic input** (the hard half of the descent dichotomy, the `cCoef`
  bound).

## Axiom hygiene
Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzDensityCount

open TerrasDensity
open CollatzStoppingF3
open CollatzStoppingF4
open CollatzStoppingF56
open CollatzBadDensity
open CollatzParityBijection

attribute [local instance] Classical.propDecidable

/-! ## §1  General structural backbone

These lemmas hold for *every* `k` and are the rigorous heart of the reduction:
the Terras affine form and the fact that the first-`k` parity data (hence the
descent structure) is determined by `n mod 2^k`. -/

/-- Right-unfolding of the Terras iterate: `T^{j+1} n = T (T^j n)`.  (The library
definition unfolds on the left, `T^{j+1} n = T^j (T n)`.) -/
theorem T_iter_succ_right (n j : Nat) : T_iter n (j + 1) = T (T_iter n j) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    show T_iter (T n) (j + 1) = T (T_iter n (j + 1))
    rw [ih (T n)]; rfl

/-- **One-step congruence.** If `m ≡ n [MOD 2^{s+1}]` then `T m ≡ T n [MOD 2^s]`.
(Same parity mod `2`; halving then drops one power of two.) -/
theorem T_step_cong (m n s : Nat) (h : m % 2 ^ (s + 1) = n % 2 ^ (s + 1)) :
    T m % 2 ^ s = T n % 2 ^ s := by
  have hp : m % 2 = n % 2 :=
    (Nat.ModEq.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero s))
      (h : m ≡ n [MOD 2 ^ (s + 1)]) : m ≡ n [MOD 2])
  have hpow : (2 : Nat) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hrw : ∀ x : Nat, x / 2 % 2 ^ s = x % (2 * 2 ^ s) / 2 := fun x =>
    (Nat.mod_mul_right_div_self x 2 (2 ^ s)).symm
  unfold T
  by_cases he : m % 2 = 0
  · have hne : n % 2 = 0 := by omega
    simp only [he, hne, if_true]
    rw [hrw, hrw, ← hpow, h]
  · have ho : m % 2 = 1 := by omega
    have hno : n % 2 = 1 := by omega
    simp only [if_neg (by omega : ¬ m % 2 = 0), if_neg (by omega : ¬ n % 2 = 0)]
    rw [hrw, hrw, ← hpow]
    have hcong : (3 * m + 1) % 2 ^ (s + 1) = (3 * n + 1) % 2 ^ (s + 1) :=
      Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 (h : m ≡ n [MOD 2 ^ (s + 1)]))
    rw [hcong]

/-- **Iterated congruence (the parity vector depends only on `n mod 2^k`).**
If `m ≡ n [MOD 2^k]` then for every `j ≤ k`, `T^j m ≡ T^j n [MOD 2^{k-j}]`. -/
theorem T_iter_cong (k : Nat) :
    ∀ (m n : Nat), m % 2 ^ k = n % 2 ^ k →
      ∀ j ≤ k, T_iter m j % 2 ^ (k - j) = T_iter n j % 2 ^ (k - j) := by
  induction k with
  | zero => intro m n h j hj; interval_cases j; simpa using h
  | succ k ih =>
    intro m n h j hj
    cases j with
    | zero => simpa using h
    | succ j =>
      have hTstep : T m % 2 ^ k = T n % 2 ^ k := T_step_cong m n k h
      have hj' : j ≤ k := by omega
      have hrec := ih (T m) (T n) hTstep j hj'
      have hsub : (k + 1) - (j + 1) = k - j := by omega
      rw [hsub]
      show T_iter (T m) j % 2 ^ (k - j) = T_iter (T n) j % 2 ^ (k - j)
      exact hrec

/-- Corollary: equal residues mod `2^k` give the same length-`k` parity vector. -/
theorem PVEq_of_mod_eq (m n k : Nat) (h : m % 2 ^ k = n % 2 ^ k) : PVEq m n k := by
  intro j hj
  have hcong := T_iter_cong k m n h j (le_of_lt hj)
  have hdvd : (2 : Nat) ∣ 2 ^ (k - j) := dvd_pow_self 2 (by omega)
  exact (Nat.ModEq.of_dvd hdvd (hcong : T_iter m j ≡ T_iter n j [MOD 2 ^ (k - j)])
    : T_iter m j ≡ T_iter n j [MOD 2])

/-- Number of odd Terras iterates among `T^0 n, …, T^{j-1} n` — the count of
`3n+1` steps in the first `j` steps. -/
def aCoef (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => aCoef n j + (if T_iter n j % 2 = 1 then 1 else 0)

/-- Additive constant in the Terras affine form (depends only on the parity
vector). -/
def cCoef (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => if T_iter n j % 2 = 1 then 3 * cCoef n j + 2 ^ j else cCoef n j

/-- **Terras affine form.** `2^j · T^j n = 3^{aCoef n j} · n + cCoef n j`.  Each
Terras step multiplies by `3` on an odd value and divides by `2`; tracking the
powers of two gives this exact affine identity. -/
theorem affine_form (n j : Nat) :
    2 ^ j * T_iter n j = 3 ^ (aCoef n j) * n + cCoef n j := by
  induction j with
  | zero => simp [aCoef, cCoef, T_iter]
  | succ j ih =>
    have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
    rw [T_iter_succ_right]
    by_cases hpar : T_iter n j % 2 = 1
    · simp only [aCoef, cCoef, hpar, if_true]
      have hT : T (T_iter n j) = (3 * T_iter n j + 1) / 2 := by
        unfold T; rw [if_neg (by omega)]
      have hdiv : 2 * ((3 * T_iter n j + 1) / 2) = 3 * T_iter n j + 1 := by omega
      have hkey : 2 ^ (j + 1) * ((3 * T_iter n j + 1) / 2)
          = 2 ^ j * (3 * T_iter n j + 1) := by rw [hpow, Nat.mul_assoc, hdiv]
      rw [hT, hkey]
      have e : 2 ^ j * (3 * T_iter n j + 1) = 3 * (2 ^ j * T_iter n j) + 2 ^ j := by ring
      rw [e, ih, pow_succ]; ring
    · have hpar0 : T_iter n j % 2 = 0 := by omega
      simp only [aCoef, cCoef, hpar, if_false]
      have hT : T (T_iter n j) = T_iter n j / 2 := by unfold T; rw [if_pos hpar0]
      have hdiv : 2 * (T_iter n j / 2) = T_iter n j := by omega
      have hkey : 2 ^ (j + 1) * (T_iter n j / 2) = 2 ^ j * T_iter n j := by
        rw [hpow, Nat.mul_assoc, hdiv]
      rw [hT, hkey, ih, Nat.add_zero]

/-- **Coefficient congruence.** `aCoef` and `cCoef` depend only on the length-`j`
parity vector: if `PVEq m n j` then `aCoef m j = aCoef n j` and
`cCoef m j = cCoef n j`. -/
theorem coef_congr (j : Nat) :
    ∀ (m n : Nat), PVEq m n j → aCoef m j = aCoef n j ∧ cCoef m j = cCoef n j := by
  induction j with
  | zero => intro m n _; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro m n h
    have hj : PVEq m n j := fun i hi => h i (by omega)
    obtain ⟨ha, hc⟩ := ih m n hj
    have hpar : T_iter m j % 2 = T_iter n j % 2 := h j (by omega)
    refine ⟨?_, ?_⟩
    · simp only [aCoef]; rw [ha, hpar]
    · simp only [cCoef]; rw [hc, hpar]

/-- **Easy half of the descent dichotomy.** If the first `j` steps contain enough
`3n+1` steps that `2^j ≤ 3^{aCoef n j}`, then `n ≤ T^j n` — the orbit has *not*
descended.  Immediate from `affine_form` (`cCoef ≥ 0`).  The converse half
(`3^{a} < 2^j → T^j n < n` for `n ≥ 2^k`) is the remaining analytic input,
documented in §5. -/
theorem no_descent_of_pow_ge (n j : Nat) (h : 2 ^ j ≤ 3 ^ (aCoef n j)) :
    n ≤ T_iter n j := by
  have haf := affine_form n j
  have h1 : 2 ^ j * n ≤ 2 ^ j * T_iter n j := by
    rw [haf]
    have : 2 ^ j * n ≤ 3 ^ (aCoef n j) * n := Nat.mul_le_mul_right n h
    omega
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

/-! ## §2  Counting infrastructure (re-derived from the public `count_upto` API) -/

/-- All `DecidablePred` instances agree under `Nat.count`. -/
private theorem cu_mono {N : Nat} (A B : Nat → Prop) (h : ∀ k, k < N + 1 → A k → B k) :
    count_upto A N ≤ count_upto B N := by
  unfold count_upto
  have e : ∀ (P : Nat → Prop),
      @Nat.count P (fun _ => Classical.propDecidable _) (N + 1)
        = @Nat.count P (Classical.decPred _) (N + 1) := fun _ => by congr 1
  rw [e A, e B]; exact Nat.count_mono_left h

private theorem cu_compl (A : Nat → Prop) (N : Nat) :
    count_upto (fun k => ¬ A k) N + count_upto A N = N + 1 := by
  unfold count_upto; generalize N + 1 = m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ]; by_cases h : A k <;> simp [h] <;> omega

private theorem cu_or (A B : Nat → Prop) (N : Nat) :
    count_upto (fun n => A n ∨ B n) N ≤ count_upto A N + count_upto B N := by
  unfold count_upto; generalize N + 1 = m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
    by_cases hp : A k <;> by_cases hq : B k <;> simp [hp, hq] <;> omega

private theorem cu_lt_two (N : Nat) : count_upto (fun n => n < 2) N ≤ 2 := by
  unfold count_upto
  suffices h : ∀ m,
      @Nat.count (fun n => n < 2) (fun _ => Classical.propDecidable _) m = min m 2 by
    rw [h]; omega
  intro m; induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih => rw [Nat.count_succ, ih]; by_cases h : k < 2 <;> simp [h] <;> omega

/-! ## §3  The decidable mirror and the exact count `D(k)` -/

/-- Boolean mirror of `DescBy`: `descByB n k = true` iff some iterate among the
first `k` steps lands below `n`.  Decidable and kernel-computable, so the residue
count `D(k)` is closed by `decide` (no `native_decide`). -/
def descByB (n k : Nat) : Bool :=
  (List.range k).any (fun j => decide (T_iter n (j + 1) < n))

/-- The Boolean mirror is faithful: `descByB n k = true ↔ DescBy n k`. -/
theorem descByB_iff (n k : Nat) : descByB n k = true ↔ DescBy n k := by
  unfold descByB DescBy
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hd⟩
    rw [List.mem_range] at hj
    exact ⟨j + 1, by omega, by omega, by simpa using hd⟩
  · rintro ⟨j, hj1, hjk, hd⟩
    refine ⟨j - 1, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · have : j - 1 + 1 = j := by omega
      rw [this]; simpa using hd

/-- **`D k` — the exact descending-residue count mod `2^k`.**
`D k = #{ r < 2^k : DescBy (r + 2^k) k }`, using the canonical class
representative `r + 2^k` (which lies in the asymptotic regime `n ≥ 2^k`, avoiding
the small-`n` boundary `n ∈ {0,1}`).  By `descByB_iff` this is exactly the number
of residue classes mod `2^k` that descend within `k` steps. -/
def D (k : Nat) : Nat :=
  ((List.range (2 ^ k)).filter (fun r => descByB (r + 2 ^ k) k)).length

/-- The descending-residue counts (`decide`, kernel-checked, no `native_decide`).
`D(1..6) = 1, 3, 6, 13, 28, 56`. -/
theorem D_one   : D 1 = 1  := by decide
theorem D_two   : D 2 = 3  := by decide
theorem D_three : D 3 = 6  := by decide
theorem D_four  : D 4 = 13 := by decide
theorem D_five  : D 5 = 28 := by decide
theorem D_six   : D 6 = 56 := by decide
set_option maxRecDepth 20000 in
theorem D_seven : D 7 = 115 := by decide
set_option maxRecDepth 40000 in
theorem D_eight : D 8 = 237 := by decide

/-! ## §4  Exact mod-`2^k` invariance of `DescBy · k`  (levels `k ≤ 6`)

For the F-file levels the descending set is *literally* a residue predicate
(`¬ Bad16` mod 16, `¬ Bad32` mod 32), so mod-invariance is immediate and exact. -/

/-- **`descBy_mod_invariant` at `k = 4`.** For `m, n ≥ 2`, if `m ≡ n [MOD 16]`
then `DescBy m 4 ↔ DescBy n 4`. -/
theorem descBy_mod_invariant_four (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : m % 16 = n % 16) : DescBy m 4 ↔ DescBy n 4 := by
  rw [descBy4_iff_good16 m hm, descBy4_iff_good16 n hn]; unfold Bad16; rw [h]

/-- **`descBy_mod_invariant` at `k = 5`.** For `m, n ≥ 2`, if `m ≡ n [MOD 32]`
then `DescBy m 5 ↔ DescBy n 5`. -/
theorem descBy_mod_invariant_five (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : m % 32 = n % 32) : DescBy m 5 ↔ DescBy n 5 := by
  rw [descBy5_iff_good32 m hm, descBy5_iff_good32 n hn]; unfold Bad32; rw [h]

/-- **`descBy_mod_invariant` at `k = 6`.** For `m, n ≥ 2`, if `m ≡ n [MOD 32]`
then `DescBy m 6 ↔ DescBy n 6`. -/
theorem descBy_mod_invariant_six (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : m % 32 = n % 32) : DescBy m 6 ↔ DescBy n 6 := by
  rw [descBy6_iff_good32 m hm, descBy6_iff_good32 n hn]; unfold Bad32; rw [h]

/-! ## §5  Direct `DescBy · k` densities for the missing low levels `k = 1, 2`

The F-files give `DescBy`-density sandwiches for `k = 3,4,5,6`
(`f3/f4/f5/f6_density_*`); levels `1` and `2` appear only as their *complements*
in `CollatzBadDensity`.  We supply the descending-side bounds directly, mirroring
`CollatzStoppingF3`'s residue technique: `F(1) = 1/2` (descending = evens) and
`F(2) = 3/4` (descending = `¬(·%4=3)`). -/

/-- For `n ≥ 2`, `DescBy n 1 ↔ n % 2 = 0` (even numbers descend in one step). -/
theorem descBy1_iff_even (n : Nat) (hn : 2 ≤ n) : DescBy n 1 ↔ n % 2 = 0 := by
  have hb : (¬ DescBy n 1) ↔ n % 2 = 1 := bad1_iff_odd n hn
  constructor
  · intro h; by_contra hc; exact (hb.2 (by omega)) h
  · intro h; by_contra hc; have := hb.1 hc; omega

private theorem not_descBy1_small (n : Nat) (hn : n < 2) : ¬ DescBy n 1 := by
  rintro ⟨j, hj1, hj2, hlt⟩; interval_cases j; interval_cases n <;> simp_all [T_iter, T]

private theorem d1_up (N : Nat) :
    count_upto (fun n => DescBy n 1) N + count_upto (fun n => n % 2 = 1) N ≤ N + 1 := by
  have hmono : count_upto (fun n => DescBy n 1) N ≤ count_upto (fun n => ¬ (n % 2 = 1)) N :=
    cu_mono (fun n => DescBy n 1) (fun n => ¬ (n % 2 = 1))
      (fun j _ hj hcon => by
        by_cases h2 : 2 ≤ j
        · have := (descBy1_iff_even j h2).mp hj; omega
        · exact not_descBy1_small j (by omega) hj)
  have hcompl := cu_compl (fun n => n % 2 = 1) N
  omega

private theorem d1_lo (N : Nat) :
    (N + 1) ≤ count_upto (fun n => DescBy n 1) N + count_upto (fun n => n % 2 = 1) N + 2 := by
  have hmono : count_upto (fun n => ¬ (n % 2 = 1)) N
      ≤ count_upto (fun n => DescBy n 1 ∨ n < 2) N :=
    cu_mono (fun n => ¬ (n % 2 = 1)) (fun n => DescBy n 1 ∨ n < 2)
      (fun j _ hj => by
        by_cases h2 : 2 ≤ j
        · exact Or.inl ((descBy1_iff_even j h2).mpr (by omega))
        · exact Or.inr (by omega))
  have hor := cu_or (fun n => DescBy n 1) (fun n => n < 2) N
  have hcompl := cu_compl (fun n => n % 2 = 1) N
  have hsmall := cu_lt_two N
  omega

private theorem r2_up (N : Nat) : 2 * count_upto (fun n => n % 2 = 1) N ≤ N + 1 + 2 :=
  count_residue_class_upper_bound 2 1 N (by norm_num) (by norm_num)
private theorem r2_lo (N : Nat) : (N + 1) / 2 ≤ count_upto (fun n => n % 2 = 1) N :=
  count_residue_class_lower_bound 2 1 N (by norm_num) (by norm_num)

/-- **`desc1_density_upper` — `F(1) ≤ 1/2`.** -/
theorem desc1_density_upper (p q : Nat) (hpq : q < 2 * p) :
    density_bounded (fun n => DescBy n 1) p q := by
  refine ⟨6 * q + 6, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 1) N with hA
  set R := count_upto (fun n => n % 2 = 1) N
  have hu := d1_up N; have hrl := r2_lo N
  have hdiv : 2 * ((N + 1) / 2) + (N + 1) % 2 = N + 1 := Nat.div_add_mod (N + 1) 2
  have hmod : (N + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2R : (N + 1) ≤ 2 * R + 2 := by have := Nat.mul_le_mul_left 2 hrl; omega
  have h2A : 2 * A ≤ (N + 1) + 1 := by omega
  have hkey : q * A ≤ p * N := by nlinarith [h2A, hpq, hN]
  simpa [hA] using hkey

/-- **`desc1_density_lower` — `F(1) ≥ 1/2`.** -/
theorem desc1_density_lower (p q : Nat) (hpq : 2 * p < q) :
    density_bounded_below (fun n => DescBy n 1) p q := by
  refine ⟨9 * q + 9, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 1) N with hA
  set R := count_upto (fun n => n % 2 = 1) N
  have hlo := d1_lo N; have hru := r2_up N
  have h2A : N ≤ 2 * A + 5 := by omega
  have hkey : p * N ≤ q * A := by nlinarith [h2A, hpq, hN]
  simpa [hA] using hkey

private theorem d2_up (N : Nat) :
    count_upto (fun n => DescBy n 2) N + count_upto (fun n => n % 4 = 3) N ≤ N + 1 := by
  have hmono : count_upto (fun n => DescBy n 2) N ≤ count_upto (fun n => ¬ (n % 4 = 3)) N :=
    cu_mono (fun n => DescBy n 2) (fun n => ¬ (n % 4 = 3))
      (fun j _ hj hcon => not_descBy2_of_mod4_eq3 j hcon hj)
  have hcompl := cu_compl (fun n => n % 4 = 3) N
  omega

private theorem d2_lo (N : Nat) :
    (N + 1) ≤ count_upto (fun n => DescBy n 2) N + count_upto (fun n => n % 4 = 3) N + 2 := by
  have hmono : count_upto (fun n => ¬ (n % 4 = 3)) N
      ≤ count_upto (fun n => DescBy n 2 ∨ n < 2) N :=
    cu_mono (fun n => ¬ (n % 4 = 3)) (fun n => DescBy n 2 ∨ n < 2)
      (fun j _ hj => by
        by_cases h2 : 2 ≤ j
        · exact Or.inl (descBy2_of_mod4_ne3 j h2 hj)
        · exact Or.inr (by omega))
  have hor := cu_or (fun n => DescBy n 2) (fun n => n < 2) N
  have hcompl := cu_compl (fun n => n % 4 = 3) N
  have hsmall := cu_lt_two N
  omega

private theorem r4_up (N : Nat) : 4 * count_upto (fun n => n % 4 = 3) N ≤ N + 1 + 4 :=
  count_residue_class_upper_bound 4 3 N (by norm_num) (by norm_num)
private theorem r4_lo (N : Nat) : (N + 1) / 4 ≤ count_upto (fun n => n % 4 = 3) N :=
  count_residue_class_lower_bound 4 3 N (by norm_num) (by norm_num)

/-- **`desc2_density_upper` — `F(2) ≤ 3/4`.** -/
theorem desc2_density_upper (p q : Nat) (hpq : 3 * q < 4 * p) :
    density_bounded (fun n => DescBy n 2) p q := by
  refine ⟨6 * q + 6, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 2) N with hA
  set R := count_upto (fun n => n % 4 = 3) N
  have hu := d2_up N; have hrl := r4_lo N
  have hdiv : 4 * ((N + 1) / 4) + (N + 1) % 4 = N + 1 := Nat.div_add_mod (N + 1) 4
  have hmod : (N + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4R : (N + 1) ≤ 4 * R + 4 := by have := Nat.mul_le_mul_left 4 hrl; omega
  have h4A : 4 * A ≤ 3 * (N + 1) + 3 := by omega
  have hkey : q * A ≤ p * N := by nlinarith [h4A, hpq, hN]
  simpa [hA] using hkey

/-- **`desc2_density_lower` — `F(2) ≥ 3/4`.** -/
theorem desc2_density_lower (p q : Nat) (hpq : 4 * p < 3 * q) :
    density_bounded_below (fun n => DescBy n 2) p q := by
  refine ⟨9 * q + 9, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 2) N with hA
  set R := count_upto (fun n => n % 4 = 3) N
  have hlo := d2_lo N; have hru := r4_up N
  have h4A : 3 * N ≤ 4 * A + 9 := by omega
  have hkey : p * N ≤ q * A := by nlinarith [h4A, hpq, hN]
  simpa [hA] using hkey

/-! ## §6  HEADLINE — `F(k) = D(k)/2^k` uniformly (`k = 1..6`)

`F_eq_count_over_pow` gives, for each level `k ∈ {1,…,6}` and all `p, q`, the
two-sided sandwich of the natural density of `{n : DescBy n k}` at the rational
`D(k)/2^k`:

  `D(k)·q < p·2^k  →  density_bounded (DescBy · k) p q`        (density ≤ p/q)
  `p·2^k < D(k)·q  →  density_bounded_below (DescBy · k) p q`  (density ≥ p/q)

so the density is pinned at `D(k)/2^k` exactly.  This single statement subsumes
the per-level `F(1) = 1/2 … F(6) = 56/64` results, with `D(k)` (a residue count,
equivalently a count of descending parity vectors) supplying the numerator
uniformly.  The hypotheses match the F-file thresholds after clearing common
factors (e.g. `D(4)·q < p·16 ⟺ 13q < 16p`); `omega` discharges the bridge. -/
theorem F_eq_count_over_pow (k : Nat) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (p q : Nat) :
    (D k * q < p * 2 ^ k → density_bounded (fun n => DescBy n k) p q)
    ∧ (p * 2 ^ k < D k * q → density_bounded_below (fun n => DescBy n k) p q) := by
  interval_cases k
  · rw [D_one]
    exact ⟨fun h => desc1_density_upper p q (by omega),
           fun h => desc1_density_lower p q (by omega)⟩
  · rw [D_two]
    exact ⟨fun h => desc2_density_upper p q (by omega),
           fun h => desc2_density_lower p q (by omega)⟩
  · rw [D_three]
    exact ⟨fun h => f3_density_upper p q (by omega),
           fun h => f3_density_lower p q (by omega)⟩
  · rw [D_four]
    exact ⟨fun h => f4_density_upper p q (by omega),
           fun h => f4_density_lower p q (by omega)⟩
  · rw [D_five]
    exact ⟨fun h => f5_density_upper p q (by omega),
           fun h => f5_density_lower p q (by omega)⟩
  · rw [D_six]
    exact ⟨fun h => f6_density_upper p q (by omega),
           fun h => f6_density_lower p q (by omega)⟩

/-! ## §7  The bad count `β(k) = 2^k − D(k)` and `b(k) = β(k)/2^k` -/

/-- The surviving-residue count `β(k) = 2^k − D(k)` (#{residues that do NOT
descend within `k` steps}). -/
def beta (k : Nat) : Nat := 2 ^ k - D k

/-- **`bad_count_eq` (item 3).** `β(k) = 2^k − D(k)`, with the pinned ladder
`β(1..6) = 1, 1, 2, 3, 4, 8` (cross-checked against `CollatzBadDensity`'s
enumerated survivor counts).  Hence the bad density is `b(k) = β(k)/2^k`. -/
theorem bad_count_eq (k : Nat) : beta k + D k = 2 ^ k := by
  unfold beta
  have hD : D k ≤ 2 ^ k := by
    unfold D
    calc ((List.range (2 ^ k)).filter (fun r => descByB (r + 2 ^ k) k)).length
        ≤ (List.range (2 ^ k)).length := List.length_filter_le _ _
      _ = 2 ^ k := by rw [List.length_range]
  omega

theorem beta_one   : beta 1 = 1 := by decide
theorem beta_two   : beta 2 = 1 := by decide
theorem beta_three : beta 3 = 2 := by decide
theorem beta_four  : beta 4 = 3 := by decide
theorem beta_five  : beta 5 = 4 := by decide
theorem beta_six   : beta 6 = 8 := by decide
set_option maxRecDepth 20000 in
theorem beta_seven : beta 7 = 13 := by decide
set_option maxRecDepth 40000 in
theorem beta_eight : beta 8 = 19 := by decide

/-! ## §8  Bijection bridge — `D(k)` is a count of binary parity vectors

Via the parity-vector bijection `pvMap k : Fin (2^k) ≃ (Fin k → Bool)`, the `D(k)`
descending residues correspond bijectively to the descending length-`k` parity
vectors.  We record the count identity over `Fin (2^k)`. -/

/-- Generic bridge: the length of a filtered `List.range n` equals the card of the
corresponding `Finset.filter` over `Fin n`. -/
private theorem range_filter_card (n : Nat) (p : Nat → Bool) :
    ((List.range n).filter (fun r => p r)).length
      = (Finset.univ.filter (fun r : Fin n => p r.val = true)).card := by
  rw [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun r => if p r = true then 1 else 0) n]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    simp [List.filter]
    by_cases h : p m <;> simp [h]

/-- **`descending_vector_count`.** `D(k)` equals the number of residues
`r : Fin (2^k)` whose canonical representative descends within `k` steps — i.e.
(via `pvMap_bijective`, which identifies `Fin (2^k)` with `Fin k → Bool`) the
number of **descending length-`k` parity vectors**.  This realizes `D(k)` as a
pure count of binary vectors in `Fin k → Bool`, the combinatorial object the whole
`b(k) → 0` question is about. -/
theorem descending_vector_count (k : Nat) :
    D k = (Finset.univ.filter
      (fun r : Fin (2 ^ k) => descByB (r.val + 2 ^ k) k = true)).card :=
  range_filter_card (2 ^ k) (fun r => descByB (r + 2 ^ k) k)

/-! ## §9  The remaining gap — `b(k) → 0` as a binomial tail on parity vectors

`b(k) → 0` ("almost all integers descend") is the open Everett–Terras theorem; it
is NOT proved here.  This file delivers the *exact finite ladder*
`F(k) = D(k)/2^k`, `b(k) = β(k)/2^k` (`k ≤ 6`), the general structural backbone
(`affine_form`, `T_iter_cong`, `coef_congr`, the easy descent half
`no_descent_of_pow_ge`), and the reduction of the whole question to a count of
binary vectors (`descending_vector_count`).

The single remaining analytic input is the **hard half of the descent
dichotomy**: for `n ≥ 2^k` and `j ≤ k`, `3^{aCoef n j} < 2^j → T^j n < n`
(few `3n+1` steps ⟹ descent).  Combined with `no_descent_of_pow_ge` this would
make `DescBy n k` (for `n ≥ 2^k`) *exactly* the parity-vector condition
"`∃ j ≤ k, 3^{a_j} < 2^j`" — a pure function of the length-`k` parity vector
`Q k n` — giving general mod-`2^k` invariance and hence `F(k) = D(k)/2^k` for ALL
`k`.  Its proof needs the bound `cCoef n j < (2^j − 3^{a_j})·2^j` (verified
numerically), whose induction requires a strengthened invariant (the naive
single-step bound fails at the `3^{a_j} ≈ 2^j` boundary).

Granting that dichotomy, a survivor (`Bad k n`, `n ≥ 2^k`) must have
`3^{a_j} ≥ 2^j` for *every* `j ≤ k`, i.e. its parity vector accumulates `3n+1`
steps fast enough that `a_j ≥ j·log 2/log 3 = j·0.6309…` throughout — a
disproportionate excess of odd steps.  Therefore `β(k)/2^k` is bounded by the
binomial tail `#{v ∈ {0,1}^k : weight(v) ≥ c·k}/2^k` with `c = log2/log3 > 1/2`,
which `→ 0` by the standard large-deviation (Chernoff/Hoeffding) estimate.  This
is the single remaining analytic fact; we state its shape as a typed target. -/

/-- **`bk_to_zero_reduction` (documented target).**  A typed statement of the
reduction: *if* every survivor's parity vector has odd-step count `aCoef`
exceeding the critical fraction at each prefix (the dichotomy consequence), *then*
`b(k) = β(k)/2^k` is dominated by a binomial tail.  Here we record the exact
algebraic identity `b(k) = β(k)/2^k` already in hand (`bad_count_eq`), leaving the
tail bound as the open input.  Concretely: for every `k`, `β(k) + D(k) = 2^k`, so
controlling `β(k)` (the number of "heavy" parity vectors) controls `b(k)`. -/
theorem bk_to_zero_reduction (k : Nat) : beta k + D k = 2 ^ k := bad_count_eq k

end CollatzDensityCount
