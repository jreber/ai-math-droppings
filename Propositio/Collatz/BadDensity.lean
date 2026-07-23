import Propositio.Collatz.Basic
import Propositio.Collatz.StoppingF3
import Propositio.Collatz.StoppingF4

/-!
# Collatz bad-set density ladder — `b(k) = density{ σ > k }` and its decrease

This file consolidates the Terras stopping-time ladder of `CollatzStoppingF3.lean`
and `CollatzStoppingF4.lean` into the **"almost all integers descend"** structure:
the *bad set* `Bad k := { n : σ(n) > k }` of integers that have NOT yet dropped
below themselves within the first `k` Terras steps, and its natural density

  `b(k)  :=  density { n : σ(n) > k }  =  1 − F(k).`

## The Terras map and the stopping predicate

For `T` (`TerrasDensity.T`: `T n = n/2` if `n` even, `(3n+1)/2` if `n` odd) the
stopping time `σ(n)` is the least number of `T`-steps that bring the orbit
strictly below `n`.  We reuse `CollatzStoppingF3.DescBy`:

  `DescBy n k  :=  ∃ j, 1 ≤ j ∧ j ≤ k ∧ T_iter n j < n`   ("`σ(n) ≤ k`")

and set `Bad k n := ¬ DescBy n k`   ("`σ(n) > k`").

## The bad-set ladder (all DENSITY statements — NOT per-orbit termination)

This is a **density** result.  It does NOT assert that any individual Collatz
trajectory terminates; it characterises the *proportion* of integers whose
stopping time exceeds `k`.

The surviving-residue counts `β(k) = #{ r < 2^k : r is a bad residue mod 2^k }`,
pinned by a `#eval` sweep (`big`-offset stable across offsets `100000 … 1234567`):

  `β(1), β(2), β(3), β(4), β(5), β(6)  =  1, 1, 2, 3, 4, 8`

with explicit survivor sets
  `mod 8 : {3,7}`,   `mod 16 : {7,11,15}`,
  `mod 32 : {7,15,27,31}`,   `mod 64 : {7,15,27,31,39,47,59,63}`.

The corresponding densities are

  `b(1) = 1/2,   b(2) = 1/4,   b(3) = 1/4,   b(4) = 3/16,`

a (weakly) decreasing ladder.  What is proved here:

1. **`bad_antitone`** : `Bad (k+1) n → Bad k n`  (the bad sets shrink), and the
   counting-level monotonicity `count_upto (Bad (k+1)) N ≤ count_upto (Bad k) N`,
   i.e. `b(k+1) ≤ b(k)`.
2. **Ladder values** : for each `k ≤ 4`, `bad_density_le k` / `bad_density_ge k`
   sandwiching `b(k)` at its value above (`1/2, 1/4, 1/4, 3/16`).
3. **Strict improvement `b4_lt_b2`** : a rational gap `13/64 < 15/64` separating
   `b(4) ≤ 13/64` from `b(2) ≥ 15/64`, so the survivors genuinely thin out.
4. (stretch) the enumerated `β(5), β(6)` documented above, and a precise
   statement of the remaining gap to `b(k) → 0` (Everett–Terras).

## Axiom hygiene

Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzBadDensity

open TerrasDensity
open CollatzStoppingF3
open CollatzStoppingF4

attribute [local instance] Classical.propDecidable

/-! ## §1  The bad-set predicate and its antitonicity -/

/-- `Bad k n`: the orbit of `n` has NOT dropped below `n` within `k` Terras steps,
i.e. the stopping time satisfies `σ(n) > k`.  This is the complement of
`CollatzStoppingF3.DescBy`. -/
def Bad (k n : Nat) : Prop := ¬ DescBy n k

/-- **`bad_antitone` (item 1).** The bad sets shrink as `k` grows:
`Bad (k+1) n → Bad k n`.  Equivalently `DescBy n k → DescBy n (k+1)`, i.e.
`{σ ≤ k} ⊆ {σ ≤ k+1}` — the contrapositive of `CollatzStoppingF3.desc_by_mono`. -/
theorem bad_antitone (k n : Nat) (h : Bad (k + 1) n) : Bad k n :=
  fun hk => h (desc_by_mono n k hk)

/-! ## §2  Counting bridge for the bad sets

We reuse the `count_upto` algebra developed in `CollatzStoppingF3` /
`CollatzStoppingF4`, re-deriving the small lemmas locally so this file depends
only on the public API.  -/

/-- Instance-bridging for `Nat.count` (all `DecidablePred` instances agree). -/
private theorem count_inst_eq {P : Nat → Prop} (i₁ i₂ : DecidablePred P) (n : Nat) :
    @Nat.count P i₁ n = @Nat.count P i₂ n := by
  cases Subsingleton.elim i₁ i₂; rfl

/-- `count_upto` monotonicity for included predicates. -/
private theorem count_upto_mono {N : Nat} (A B : Nat → Prop)
    (h : ∀ k, k < N + 1 → A k → B k) :
    count_upto A N ≤ count_upto B N := by
  unfold count_upto
  rw [count_inst_eq (fun a => Classical.propDecidable _) (Classical.decPred _) (N + 1),
      count_inst_eq (fun a => Classical.propDecidable _) (Classical.decPred _) (N + 1)]
  exact Nat.count_mono_left h

/-- Subadditivity of `count_upto` over a disjunction. -/
private theorem count_upto_or (A B : Nat → Prop) (N : Nat) :
    count_upto (fun n => A n ∨ B n) N ≤ count_upto A N + count_upto B N := by
  unfold count_upto
  generalize N + 1 = m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
    by_cases hp : A k <;> by_cases hq : B k <;> simp [hp, hq] <;> omega

/-- `count_upto {n < 2} N ≤ 2`. -/
private theorem count_upto_lt_two (N : Nat) : count_upto (fun n => n < 2) N ≤ 2 := by
  unfold count_upto
  suffices h : ∀ m, @Nat.count (fun n => n < 2)
      (fun a => Classical.propDecidable _) m = min m 2 by rw [h]; omega
  intro m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, ih]
    by_cases h : k < 2
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- `count_upto {n = 1} N ≤ 1`. -/
private theorem count_upto_eq_one (N : Nat) : count_upto (fun n => n = 1) N ≤ 1 := by
  unfold count_upto
  suffices h : ∀ m, @Nat.count (fun n => n = 1)
      (fun a => Classical.propDecidable _) m = (if 2 ≤ m then 1 else 0) by
    rw [h]; split <;> omega
  intro m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, ih]
    by_cases h : k = 1
    · subst h; simp
    · by_cases hk : 2 ≤ k <;> simp [h, hk] <;> omega

/-- Complement identity through `count_upto`. -/
private theorem count_upto_compl (A : Nat → Prop) (N : Nat) :
    count_upto (fun k => ¬ A k) N + count_upto A N = N + 1 := by
  unfold count_upto
  generalize N + 1 = m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ]
    by_cases h : A k <;> simp [h] <;> omega

/-- **`bad_count_antitone` (item 1, counting level).** At every cutoff `N`,
`count_upto (Bad (k+1)) N ≤ count_upto (Bad k) N`.  Hence `b(k+1) ≤ b(k)`. -/
theorem bad_count_antitone (k N : Nat) :
    count_upto (fun n => Bad (k + 1) n) N ≤ count_upto (fun n => Bad k n) N :=
  count_upto_mono _ _ (fun j _ hj => bad_antitone k j hj)

/-! ## §3  `Bad k` as the complement count

Because `count_upto (¬ DescBy · k) N + count_upto (DescBy · k) N = N + 1`, every
upper/lower bound on the descending count `A_k = count_upto (DescBy · k)` flips
into a lower/upper bound on the bad count `B_k = count_upto (Bad k)`, and from
those we read off the bad density `b(k) = 1 − F(k)`. -/

/-- The descending count and the bad count are complementary. -/
theorem bad_count_compl (k N : Nat) :
    count_upto (fun n => Bad k n) N + count_upto (fun n => DescBy n k) N = N + 1 :=
  count_upto_compl (fun n => DescBy n k) N

/-! ### §3a  Level 2 — `b(2) = 1/4` (the bad class is `n ≡ 3 (mod 4)`)

`CollatzStoppingF3` proves the level-3 facts; level 2 is the *first two* steps.
We re-derive `DescBy n 2 ↔ n%4 ≠ 3` (for `n ≥ 2`) from the two-step descent
`desc2_of_mod4_ne3` and the non-descent half of `nondesc3_of_mod4_eq3`. -/

/-- `n % 4 = 3 → ¬ DescBy n 2` (all `n`): the first two iterates of an
`n ≡ 3 (mod 4)` number stay `≥ n`.  (First two conjuncts of
`CollatzStoppingF3.nondesc3_of_mod4_eq3`.) -/
theorem not_descBy2_of_mod4_eq3 (n : Nat) (h : n % 4 = 3) : ¬ DescBy n 2 := by
  intro hd
  obtain ⟨j, hj1, hj2, hlt⟩ := hd
  obtain ⟨h1, h2, _⟩ := nondesc3_of_mod4_eq3 n h
  interval_cases j
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)

/-- `n ≥ 2` and `n % 4 ≠ 3 → DescBy n 2`: descent within the first two steps
(lift of `CollatzStoppingF3.desc2_of_mod4_ne3`). -/
theorem descBy2_of_mod4_ne3 (n : Nat) (hn : 2 ≤ n) (h : n % 4 ≠ 3) : DescBy n 2 := by
  rcases desc2_of_mod4_ne3 n hn h with h1 | h2
  · exact ⟨1, by omega, by omega, h1⟩
  · exact ⟨2, by omega, by omega, h2⟩

/-- **Upper inclusion for `Bad 2`.** `Bad 2 n → n % 4 = 3 ∨ n < 2`, so the bad
count is at most the `{·%4 = 3}` count plus the two small exceptions. -/
private theorem bad2_count_upper (N : Nat) :
    count_upto (fun n => Bad 2 n) N
      ≤ count_upto (fun n => n % 4 = 3) N + 2 := by
  -- `Bad 2 ⊆ {·%4 = 3} ∪ {·<2}`.
  have hmono :
      count_upto (fun n => Bad 2 n) N
        ≤ count_upto (fun n => n % 4 = 3 ∨ n < 2) N := by
    refine count_upto_mono _ _ (fun j _ hj => ?_)
    by_cases hj2 : 2 ≤ j
    · by_cases hm : j % 4 = 3
      · exact Or.inl hm
      · exact absurd (descBy2_of_mod4_ne3 j hj2 hm) hj
    · exact Or.inr (by omega)
  have hsub := count_upto_or (fun n => n % 4 = 3) (fun n => n < 2) N
  have hsmall := count_upto_lt_two N
  omega

/-- **Lower inclusion for `Bad 2`.** `n % 4 = 3 → Bad 2 n`, so the bad count is
at least the `{·%4 = 3}` count. -/
private theorem bad2_count_lower (N : Nat) :
    count_upto (fun n => n % 4 = 3) N ≤ count_upto (fun n => Bad 2 n) N :=
  count_upto_mono _ _ (fun j _ hj => not_descBy2_of_mod4_eq3 j hj)

/-- Residue bounds (m = 4) for the bad-2 class `{·%4 = 3}`. -/
private theorem res43_upper (N : Nat) :
    4 * count_upto (fun n => n % 4 = 3) N ≤ N + 1 + 4 :=
  count_residue_class_upper_bound 4 3 N (by norm_num) (by norm_num)
private theorem res43_lower (N : Nat) :
    (N + 1) / 4 ≤ count_upto (fun n => n % 4 = 3) N :=
  count_residue_class_lower_bound 4 3 N (by norm_num) (by norm_num)

/-- **`bad_density_le_two` — `b(2) ≤ 1/4` (upper half).**
The bad set `{σ > 2}` has natural density at most `p/q` for every `p/q > 1/4`
(i.e. `q < 4*p`). -/
theorem bad_density_le_two (p q : Nat) (hpq : q < 4 * p) :
    density_bounded (fun n => Bad 2 n) p q := by
  refine ⟨13 * q + 13, fun N hN => ?_⟩
  set B := count_upto (fun n => Bad 2 n) N with hB
  set R := count_upto (fun n => n % 4 = 3) N with hR
  have hbu : B ≤ R + 2 := bad2_count_upper N
  have hru : 4 * R ≤ N + 1 + 4 := res43_upper N
  -- `4B ≤ 4R + 8 ≤ N + 13`, so `4B ≤ N + 13`.
  have h4B : 4 * B ≤ N + 13 := by omega
  -- `4qB = q(4B) ≤ q(N+13)`, and `(q+1)N ≤ 4pN`, with `13q ≤ N`.
  have e1 : q * (4 * B) ≤ q * (N + 13) := Nat.mul_le_mul_left q h4B
  have e2 : (q + 1) * N ≤ 4 * p * N := Nat.mul_le_mul_right N (by omega)
  have hkey : q * B ≤ p * N := by nlinarith [e1, e2, hN]
  simpa [hB] using hkey

/-- **`bad_density_ge_two` — `b(2) ≥ 1/4` (lower half).**
The bad set `{σ > 2}` has natural density at least `p/q` for every `p/q < 1/4`
(i.e. `4*p < q`). -/
theorem bad_density_ge_two (p q : Nat) (hpq : 4 * p < q) :
    density_bounded_below (fun n => Bad 2 n) p q := by
  refine ⟨8 * q + 8, fun N hN => ?_⟩
  set B := count_upto (fun n => Bad 2 n) N with hB
  set R := count_upto (fun n => n % 4 = 3) N with hR
  have hbl : R ≤ B := bad2_count_lower N
  have hrl : (N + 1) / 4 ≤ R := res43_lower N
  have hdiv : 4 * ((N + 1) / 4) + (N + 1) % 4 = N + 1 := Nat.div_add_mod (N + 1) 4
  have hmod : (N + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  -- `4B ≥ 4R ≥ 4·((N+1)/4) ≥ N + 1 − 3 = N − 2`.
  have h4R : N + 1 ≤ 4 * R + 4 := by
    have := Nat.mul_le_mul_left 4 hrl; omega
  have h4B : N ≤ 4 * B + 3 := by omega
  have hkey : p * N ≤ q * B := by nlinarith [h4B, hpq, hN]
  simpa [hB] using hkey

/-! ### §3b  Level 3 — `b(3) = 1/4` (same bad class; `F(3) = F(2)`)

`CollatzStoppingF3.desc_three_iff_two` says no integer has stopping time exactly
`3`, so `Bad 3 = Bad 2` pointwise and `b(3) = b(2) = 1/4`. -/

/-- `Bad 3 n ↔ Bad 2 n` (no integer has stopping time exactly 3):
the complement of `CollatzStoppingF3.desc_three_iff_two`. -/
theorem bad3_iff_bad2 (n : Nat) : Bad 3 n ↔ Bad 2 n :=
  not_congr (desc_three_iff_two n)

/-- **`bad_density_le_three` — `b(3) ≤ 1/4`.**  Same bound as level 2. -/
theorem bad_density_le_three (p q : Nat) (hpq : q < 4 * p) :
    density_bounded (fun n => Bad 3 n) p q := by
  obtain ⟨N₀, h⟩ := bad_density_le_two p q hpq
  refine ⟨N₀, fun N hN => ?_⟩
  -- `count_upto (Bad 3) N = count_upto (Bad 2) N` since the predicates agree.
  have heq : count_upto (fun n => Bad 3 n) N = count_upto (fun n => Bad 2 n) N :=
    le_antisymm
      (count_upto_mono _ _ (fun j _ hj => (bad3_iff_bad2 j).mp hj))
      (count_upto_mono _ _ (fun j _ hj => (bad3_iff_bad2 j).mpr hj))
  rw [heq]; exact h N hN

/-- **`bad_density_ge_three` — `b(3) ≥ 1/4`.** -/
theorem bad_density_ge_three (p q : Nat) (hpq : 4 * p < q) :
    density_bounded_below (fun n => Bad 3 n) p q := by
  obtain ⟨N₀, h⟩ := bad_density_ge_two p q hpq
  refine ⟨N₀, fun N hN => ?_⟩
  have heq : count_upto (fun n => Bad 3 n) N = count_upto (fun n => Bad 2 n) N :=
    le_antisymm
      (count_upto_mono _ _ (fun j _ hj => (bad3_iff_bad2 j).mp hj))
      (count_upto_mono _ _ (fun j _ hj => (bad3_iff_bad2 j).mpr hj))
  rw [heq]; exact h N hN

/-! ### §3c  Level 4 — `b(4) = 3/16` (bad class `{7,11,15} (mod 16)`)

We reuse `CollatzStoppingF4.countUpper` / `countLower`, which bound the
*descending* count `A_4` against `count_upto Bad16`, together with the bad/desc
complement identity to convert into bounds on `B_4 = count_upto (Bad 4)`.  We
also re-derive the `Bad16` count sandwich `3(N+1) − 45 ≤ 16·#Bad16 ≤ 3(N+1)+48`
from the three residue classes. -/

/-- Exact decomposition of `count_upto Bad16` into three disjoint residue counts. -/
private theorem countBad16_eq (N : Nat) :
    count_upto Bad16 N =
      count_upto (fun n => n % 16 = 7) N
      + count_upto (fun n => n % 16 = 11) N
      + count_upto (fun n => n % 16 = 15) N := by
  have hdisj : ∀ (A B : Nat → Prop), (∀ k, ¬ (A k ∧ B k)) →
      count_upto (fun n => A n ∨ B n) N = count_upto A N + count_upto B N := by
    intro A B hdis
    unfold count_upto
    generalize N + 1 = m
    induction m with
    | zero => simp [Nat.count_zero]
    | succ k ih =>
      rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
      by_cases hp : A k <;> by_cases hq : B k <;>
        simp [hp, hq] <;> first | omega | exact absurd ⟨hp, hq⟩ (hdis k)
  have hrw : count_upto Bad16 N
      = count_upto (fun n => n % 16 = 7 ∨ (n % 16 = 11 ∨ n % 16 = 15)) N := rfl
  rw [hrw,
      hdisj (fun n => n % 16 = 7) (fun n => n % 16 = 11 ∨ n % 16 = 15) (by intro k; omega),
      hdisj (fun n => n % 16 = 11) (fun n => n % 16 = 15) (by intro k; omega)]
  omega

private theorem res16_upper (r N : Nat) (hr : r < 16) :
    16 * count_upto (fun n => n % 16 = r) N ≤ N + 1 + 16 :=
  count_residue_class_upper_bound 16 r N (by norm_num) hr
private theorem res16_lower (r N : Nat) (hr : r < 16) :
    (N + 1) / 16 ≤ count_upto (fun n => n % 16 = r) N :=
  count_residue_class_lower_bound 16 r N (by norm_num) hr

/-- `16 · #Bad16 ≤ 3(N+1) + 48`. -/
private theorem bad16_count_upper (N : Nat) :
    16 * count_upto Bad16 N ≤ 3 * (N + 1) + 48 := by
  rw [countBad16_eq N]
  have h7 := res16_upper 7 N (by norm_num)
  have h11 := res16_upper 11 N (by norm_num)
  have h15 := res16_upper 15 N (by norm_num)
  omega

/-- `3(N+1) ≤ 16 · #Bad16 + 45`. -/
private theorem bad16_count_lower (N : Nat) :
    3 * (N + 1) ≤ 16 * count_upto Bad16 N + 45 := by
  rw [countBad16_eq N]
  have h7 := res16_lower 7 N (by norm_num)
  have h11 := res16_lower 11 N (by norm_num)
  have h15 := res16_lower 15 N (by norm_num)
  have hdiv : 16 * ((N + 1) / 16) + (N + 1) % 16 = N + 1 := Nat.div_add_mod (N + 1) 16
  have hmod : (N + 1) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have e7 := Nat.mul_le_mul_left 16 h7
  have e11 := Nat.mul_le_mul_left 16 h11
  have e15 := Nat.mul_le_mul_left 16 h15
  omega

/-- `Bad 4 n` and `Bad16 n` differ only on `n < 2`, so their counts differ by `≤ 2`.
Concretely we get the two-sided bound used below. -/
private theorem bad4_count_eq_bad16 (N : Nat) :
    count_upto (fun n => Bad 4 n) N ≤ count_upto Bad16 N + 2
      ∧ count_upto Bad16 N ≤ count_upto (fun n => Bad 4 n) N := by
  constructor
  · -- `Bad 4 ⊆ Bad16 ∪ {·<2}` : if `n ≥ 2` and `¬Bad16 n` then `DescBy n 4`.
    have hmono :
        count_upto (fun n => Bad 4 n) N
          ≤ count_upto (fun n => Bad16 n ∨ n < 2) N := by
      refine count_upto_mono _ _ (fun j _ hj => ?_)
      by_cases hj2 : 2 ≤ j
      · by_cases hb : Bad16 j
        · exact Or.inl hb
        · exact absurd (descBy4_of_not_bad16 j hj2 hb) hj
      · exact Or.inr (by omega)
    have hsub := count_upto_or Bad16 (fun n => n < 2) N
    have hsmall := count_upto_lt_two N
    omega
  · -- `Bad16 ⊆ Bad 4` : `Bad16 n → ¬ DescBy n 4` (contrapositive of
    -- `not_bad16_of_descBy4 : DescBy n 4 → ¬ Bad16 n`).
    exact count_upto_mono _ _ (fun j _ hj => fun hd => not_bad16_of_descBy4 j hd hj)

/-- **`bad_density_le_four` — `b(4) ≤ 3/16` (upper half).**
The bad set `{σ > 4}` has natural density at most `p/q` for every `p/q > 3/16`
(i.e. `3*q < 16*p`). -/
theorem bad_density_le_four (p q : Nat) (hpq : 3 * q < 16 * p) :
    density_bounded (fun n => Bad 4 n) p q := by
  refine ⟨96 * q + 96, fun N hN => ?_⟩
  set B := count_upto (fun n => Bad 4 n) N with hB
  set C := count_upto Bad16 N with hC
  obtain ⟨hbc, _⟩ := bad4_count_eq_bad16 N
  have hcu : 16 * C ≤ 3 * (N + 1) + 48 := bad16_count_upper N
  -- `16B ≤ 16C + 32 ≤ 3(N+1) + 80 = 3N + 83`.
  have h16B : 16 * B ≤ 3 * N + 83 := by omega
  have e1 : q * (16 * B) ≤ q * (3 * N + 83) := Nat.mul_le_mul_left q h16B
  have e2 : (3 * q + 1) * N ≤ 16 * p * N := Nat.mul_le_mul_right N (by omega)
  have hkey : q * B ≤ p * N := by nlinarith [e1, e2, hN]
  simpa [hB] using hkey

/-- **`bad_density_ge_four` — `b(4) ≥ 3/16` (lower half).**
The bad set `{σ > 4}` has natural density at least `p/q` for every `p/q < 3/16`
(i.e. `16*p < 3*q`). -/
theorem bad_density_ge_four (p q : Nat) (hpq : 16 * p < 3 * q) :
    density_bounded_below (fun n => Bad 4 n) p q := by
  refine ⟨96 * q + 96, fun N hN => ?_⟩
  set B := count_upto (fun n => Bad 4 n) N with hB
  set C := count_upto Bad16 N with hC
  obtain ⟨_, hcb⟩ := bad4_count_eq_bad16 N
  have hcl : 3 * (N + 1) ≤ 16 * C + 45 := bad16_count_lower N
  -- `16B ≥ 16C ≥ 3(N+1) − 45 = 3N − 42`.
  have h16B : 3 * N ≤ 16 * B + 42 := by omega
  have hkey : p * N ≤ q * B := by nlinarith [h16B, hpq, hN]
  simpa [hB] using hkey

/-! ## §4  `b(1) = 1/2` (the bad class is the odd numbers)

Level 1: `DescBy n 1 ↔ T n < n ↔ n even` (for `n ≥ 1`); the bad set is the odds. -/

/-- An even `n ≥ 2` descends in one step; an odd `n` does not. -/
theorem bad1_iff_odd (n : Nat) (hn : 2 ≤ n) : Bad 1 n ↔ n % 2 = 1 := by
  unfold Bad DescBy
  constructor
  · intro h
    by_contra hodd
    have he : n % 2 = 0 := by omega
    exact h ⟨1, by omega, by omega, by rw [T_iter_one, T_step_even n he]; omega⟩
  · intro hodd ⟨j, hj1, hj1', hlt⟩
    -- only j = 1; T n = (3n+1)/2 ≥ n for odd n.
    have hj : j = 1 := by omega
    subst hj
    rw [T_iter_one, T_step_odd n hodd] at hlt
    omega

/-- **Upper inclusion for `Bad 1`.** `Bad 1 ⊆ {·%2 = 1} ∪ {·<2}`. -/
private theorem bad1_count_upper (N : Nat) :
    count_upto (fun n => Bad 1 n) N ≤ count_upto (fun n => n % 2 = 1) N + 2 := by
  have hmono :
      count_upto (fun n => Bad 1 n) N
        ≤ count_upto (fun n => n % 2 = 1 ∨ n < 2) N := by
    refine count_upto_mono _ _ (fun j _ hj => ?_)
    by_cases hj2 : 2 ≤ j
    · exact Or.inl ((bad1_iff_odd j hj2).mp hj)
    · exact Or.inr (by omega)
  have hsub := count_upto_or (fun n => n % 2 = 1) (fun n => n < 2) N
  have hsmall := count_upto_lt_two N
  omega

/-- **Lower inclusion for `Bad 1`.** `{·%2 = 1, ·≥2} ⊆ Bad 1`; the odd count
beyond `n ≥ 2` is at least the odd count minus the single small odd `1`. -/
private theorem bad1_count_lower (N : Nat) :
    count_upto (fun n => n % 2 = 1) N ≤ count_upto (fun n => Bad 1 n) N + 1 := by
  -- `{·%2=1} ⊆ Bad 1 ∪ {·<2}`, and `count {·<2} ≤ 2`; but the only small odd is `1`,
  -- so the slack is `1`.  We route through the `∪ {·=1}` set to get slack `1`.
  have hmono :
      count_upto (fun n => n % 2 = 1) N
        ≤ count_upto (fun n => Bad 1 n ∨ n = 1) N := by
    refine count_upto_mono _ _ (fun j _ hj => ?_)
    by_cases hj2 : 2 ≤ j
    · exact Or.inl ((bad1_iff_odd j hj2).mpr hj)
    · -- j < 2 and j odd ⇒ j = 1
      exact Or.inr (by omega)
  have hsub := count_upto_or (fun n => Bad 1 n) (fun n => n = 1) N
  have hsmall := count_upto_eq_one N
  omega

private theorem res21_upper (N : Nat) :
    2 * count_upto (fun n => n % 2 = 1) N ≤ N + 1 + 2 :=
  count_residue_class_upper_bound 2 1 N (by norm_num) (by norm_num)
private theorem res21_lower (N : Nat) :
    (N + 1) / 2 ≤ count_upto (fun n => n % 2 = 1) N :=
  count_residue_class_lower_bound 2 1 N (by norm_num) (by norm_num)

/-- **`bad_density_le_one` — `b(1) ≤ 1/2`.** -/
theorem bad_density_le_one (p q : Nat) (hpq : q < 2 * p) :
    density_bounded (fun n => Bad 1 n) p q := by
  refine ⟨7 * q + 7, fun N hN => ?_⟩
  set B := count_upto (fun n => Bad 1 n) N with hB
  set R := count_upto (fun n => n % 2 = 1) N with hR
  have hbu : B ≤ R + 2 := bad1_count_upper N
  have hru : 2 * R ≤ N + 1 + 2 := res21_upper N
  -- `2B ≤ 2R + 4 ≤ N + 7`.
  have h2B : 2 * B ≤ N + 7 := by omega
  have e1 : q * (2 * B) ≤ q * (N + 7) := Nat.mul_le_mul_left q h2B
  have e2 : (q + 1) * N ≤ 2 * p * N := Nat.mul_le_mul_right N (by omega)
  have hkey : q * B ≤ p * N := by nlinarith [e1, e2, hN]
  simpa [hB] using hkey

/-- **`bad_density_ge_one` — `b(1) ≥ 1/2`.** -/
theorem bad_density_ge_one (p q : Nat) (hpq : 2 * p < q) :
    density_bounded_below (fun n => Bad 1 n) p q := by
  refine ⟨4 * q + 4, fun N hN => ?_⟩
  set B := count_upto (fun n => Bad 1 n) N with hB
  set R := count_upto (fun n => n % 2 = 1) N with hR
  have hbl : R ≤ B + 1 := bad1_count_lower N
  have hrl : (N + 1) / 2 ≤ R := res21_lower N
  have hdiv : 2 * ((N + 1) / 2) + (N + 1) % 2 = N + 1 := Nat.div_add_mod (N + 1) 2
  have hmod : (N + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2R : N + 1 ≤ 2 * R + 2 := by
    have := Nat.mul_le_mul_left 2 hrl; omega
  -- `2B ≥ 2R − 2 ≥ (N+1) − 2 − 2 = N − 3`.
  have h2B : N ≤ 2 * B + 3 := by omega
  have hkey : p * N ≤ q * B := by nlinarith [h2B, hpq, hN]
  simpa [hB] using hkey

/-! ## §5  Strict improvement of the ladder: `b(4) < b(2)` -/

/-- **`b4_lt_b2` (item 3) — the ladder strictly tightens.**

The survivor density genuinely drops between level `2` and level `4`: there is a
rational gap `13/64 < 15/64` separating them.  Concretely
`b(4) ≤ 13/64 < 15/64 ≤ b(2)`, since `13/64 > 3/16 = 12/64` and
`15/64 < 1/4 = 16/64`.  The pair of density bounds (an upper bound on `b(4)` and a
lower bound on `b(2)` with `13/64 < 15/64`) witnesses `b(4) < b(2)`. -/
theorem b4_lt_b2 :
    density_bounded (fun n => Bad 4 n) 13 64
      ∧ density_bounded_below (fun n => Bad 2 n) 15 64
      ∧ (13 : Nat) < 15 :=
  ⟨bad_density_le_four 13 64 (by norm_num),
   bad_density_ge_two 15 64 (by norm_num),
   by norm_num⟩

/-! ## §6  Enumeration record and the remaining gap to `b(k) → 0`

**Pinned survivor counts** (`#eval`, stable across offsets):

  `β(1), β(2), β(3), β(4), β(5), β(6)  =  1, 1, 2, 3, 4, 8`

with survivor residue sets
  `mod 8 : {3,7}`, `mod 16 : {7,11,15}`,
  `mod 32 : {7,15,27,31}`, `mod 64 : {7,15,27,31,39,47,59,63}`.

So `b(5) = β(5)/32 = 4/32 = 1/8` and `b(6) = β(6)/64 = 8/64 = 1/8` — the ladder
continues `1/2, 1/4, 1/4, 3/16, 1/8, 1/8, …` (each value is `β(k)/2^k`).

**The remaining gap (`b(k) → 0`, Everett–Terras).**  The full theorem
`b(k) → 0` ("almost all integers descend") is NOT proved here.  What this file
establishes is the *ladder of finitely many exact values* together with
**`bad_antitone` / `bad_count_antitone`** (`b` is weakly decreasing) and the
**strict drop `b4_lt_b2`**.  The general limit requires the equidistribution of
the Terras *parity vectors*: that `#{ r < 2^k : r survives k steps } / 2^k → 0`,
equivalently that the surviving-residue fraction `β(k)/2^k` tends to `0`.  This
needs the Terras/Everett structural input that the parity-vector map
`r ↦ (Q(r), 2^k)` is a bijection of `ℤ/2^k` whose "no descent in k steps"
fibre has density `→ 0` — a statement beyond the finitely-many-residue
case-analysis used for `k ≤ 4` here.  A first structural step toward it
(`bad_antitone`) is in place; the equidistribution itself is the open input. -/

end CollatzBadDensity
