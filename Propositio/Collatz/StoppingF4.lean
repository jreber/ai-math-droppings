import Propositio.Collatz.Basic
import Propositio.Collatz.StoppingF3

/-!
# Collatz stopping-time density at level 4 — `F(4) = 13/16`

This file extends the Terras stopping-time density theory one further level, from
`F(3) = F(2) = 3/4` (see `CollatzStoppingF3.lean`) to the **fourth** stopping-time
level, where the density strictly increases for the first time.

## The stopping time and `F(k)`

For the Terras half-step map `T` (`TerrasDensity.T`: `T n = n/2` if `n` even,
`(3n+1)/2` if `n` odd) the *stopping time* `σ(n)` is the least number of
`T`-steps that bring the orbit strictly below `n`, and `F(k)` is the natural
density of `{ n : σ(n) ≤ k }`.  As in `CollatzStoppingF3`, we work with

  `DescBy n k  :=  ∃ j, 1 ≤ j ∧ j ≤ k ∧ T_iter n j < n`   ("`σ(n) ≤ k`")

reusing `CollatzStoppingF3.DescBy`.

## What is proved (all DENSITY statements — NOT termination)

This is a **density** result about the proportion of integers with a short
stopping time.  It does NOT assert that every Collatz trajectory terminates.

1. **Enumeration-pinned value.**  A `#eval` sweep over residues mod `16` shows the
   residues with `σ ≤ 4` are exactly the `13` classes
   `{0,1,2,3,4,5,6,8,9,10,12,13,14}`; the non-descenders are `{7,11,15}`
   (i.e. `n % 4 = 3` *and* `n % 16 ≠ 3`).  Hence **`F(4) = 13/16`**.
   The single class that *newly* drops at level `4` (relative to level `3`) is
   `n ≡ 3 (mod 16)`: for `n = 16q+3` the iterates are `24q+5, 36q+8, 18q+4, 9q+2`
   and `9q+2 < 16q+3`, so the descent happens exactly at the **fourth** step.

2. **Residue characterization** (`descBy4_iff_good16`).  For `n ≥ 2`,
   `DescBy n 4 ↔ ¬(n%16 = 7 ∨ n%16 = 11 ∨ n%16 = 15)`.

3. **Density `F(4) = 13/16` (sandwich).**
   - `f4_density_upper` : `density_bounded {σ≤4} p q`        for `13*q < 16*p`.
   - `f4_density_lower` : `density_bounded_below {σ≤4} p q`   for `16*p < 13*q`.
   Together these sandwich the natural density of `{σ≤4}` at exactly `13/16`.

4. **Monotonicity / strict gain.**  `f3_le_f4` (`{σ≤3} ⊆ {σ≤4}` at the counting
   level) and `desc4_newly_drops` (`n ≡ 3 (mod 16)` is in `{σ≤4}` but not
   `{σ≤3}`), witnessing `F(4) > F(3)`.

## Axiom hygiene

Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzStoppingF4

open TerrasDensity
open CollatzStoppingF3

attribute [local instance] Classical.propDecidable

/-! ## §1  Fourth-iterate unfolding -/

/-- Iterate unfolding: `T_iter n 4 = T (T (T (T n)))`. -/
theorem T_iter_four (n : Nat) : T_iter n 4 = T (T (T (T n))) := rfl

/-! ## §2  The newly-dropping class `n ≡ 3 (mod 16)` -/

/-- **New descent at level 4: `n ≡ 3 (mod 16)` descends on the fourth step.**

For `n = 16q+3` the Terras iterates are
`T n = 24q+5` (odd), `T² n = 36q+8` (even), `T³ n = 18q+4` (even),
`T⁴ n = 9q+2`, and `9q+2 < 16q+3`.  This is the single residue class mod `16`
that drops at level `4` but not at level `3`. -/
theorem desc4_of_mod16_eq3 (n : Nat) (h : n % 16 = 3) : T_iter n 4 < n := by
  rw [T_iter_four]
  have ho : n % 2 = 1 := by omega
  have hTn : T n = (3 * n + 1) / 2 := T_step_odd n ho
  have hTn_odd : (T n) % 2 = 1 := by rw [hTn]; omega
  have hT2 : T (T n) = (3 * (T n) + 1) / 2 := T_step_odd (T n) hTn_odd
  have hT2_even : (T (T n)) % 2 = 0 := by rw [hT2, hTn]; omega
  have hT3 : T (T (T n)) = (T (T n)) / 2 := T_step_even _ hT2_even
  have hT3_even : (T (T (T n))) % 2 = 0 := by rw [hT3, hT2, hTn]; omega
  have hT4 : T (T (T (T n))) = (T (T (T n))) / 2 := T_step_even _ hT3_even
  rw [hT4, hT3, hT2, hTn]; omega

/-- `n ≡ 3 (mod 16)` is in `{σ ≤ 4}` (lift of `desc4_of_mod16_eq3`). -/
theorem descBy4_of_mod16_eq3 (n : Nat) (h : n % 16 = 3) : DescBy n 4 :=
  ⟨4, by omega, by omega, desc4_of_mod16_eq3 n h⟩

/-! ## §3  The bad residues `{7,11,15} (mod 16)` do not descend within 4 steps -/

/-- `Bad16 n`: the level-4 non-descending residues mod 16, namely
`n % 16 ∈ {7, 11, 15}`.  Equivalently `n % 4 = 3 ∧ n % 16 ≠ 3`. -/
def Bad16 (n : Nat) : Prop := n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15

set_option maxHeartbeats 1000000 in
/-- **Non-descent: a `Bad16` number does not descend within four Terras steps.**

For `n` with `n % 16 ∈ {7,11,15}`, all four of `T n, T² n, T³ n, T⁴ n` are `≥ n`.
The intermediate parities differ between the three sub-classes, so the proof
case-splits on the parities of `T² n` and `T³ n` (each determined by `n % 16`);
in every branch `omega` closes the four inequalities. -/
theorem nondesc4_of_bad16 (n : Nat) (h : Bad16 n) :
    n ≤ T_iter n 1 ∧ n ≤ T_iter n 2 ∧ n ≤ T_iter n 3 ∧ n ≤ T_iter n 4 := by
  rw [T_iter_one, T_iter_two, T_iter_three, T_iter_four]
  -- Name the four iterates and pin each to a *linear* relation, so `omega` never
  -- has to reason about nested `Nat`-division.
  have ho : n % 2 = 1 := by rcases h with h|h|h <;> omega
  -- step 1 (n odd): T n =: a, with 2a = 3n+1
  have hTn : T n = (3 * n + 1) / 2 := T_step_odd n ho
  set a := T n with ha
  have ha2 : 2 * a = 3 * n + 1 := by rw [hTn]; omega
  clear_value a; clear hTn ha ho
  have hao : a % 2 = 1 := by rcases h with h|h|h <;> omega
  -- step 2 (a odd): T a =: b, with 2b = 3a+1
  have hT2 : T a = (3 * a + 1) / 2 := T_step_odd a hao
  set b := T a with hb
  have hb2 : 2 * b = 3 * a + 1 := by rw [hT2]; omega
  clear_value b; clear hT2 hb hao
  -- step 3: parity of b is determined by n%16; both possibilities give 2·c relations
  by_cases hbe : b % 2 = 0
  · -- `n ≡ 11 (mod 16)`: b even, T b = b/2
    have hT3 : T b = b / 2 := T_step_even b hbe
    set c := T b with hc
    have hc2 : 2 * c = b := by rw [hT3]; omega
    clear_value c; clear hT3 hc
    have hco : c % 2 = 1 := by rcases h with h|h|h <;> omega
    have hT4 : T c = (3 * c + 1) / 2 := T_step_odd c hco
    set d := T c with hd
    have hd2 : 2 * d = 3 * c + 1 := by rw [hT4]; omega
    clear_value d; clear hT4 hd
    rcases h with h|h|h <;> omega
  · -- `n ≡ 7 or 15 (mod 16)`: b odd, T b = (3b+1)/2
    have hbo : b % 2 = 1 := by omega
    have hT3 : T b = (3 * b + 1) / 2 := T_step_odd b hbo
    set c := T b with hc
    have hc2 : 2 * c = 3 * b + 1 := by rw [hT3]; omega
    clear_value c; clear hT3 hc
    by_cases hce : c % 2 = 0
    · -- `n ≡ 7 (mod 16)`: c even, T c = c/2
      have hT4 : T c = c / 2 := T_step_even c hce
      set d := T c with hd
      have hd2 : 2 * d = c := by rw [hT4]; omega
      clear_value d; clear hT4 hd
      rcases h with h|h|h <;> omega
    · -- `n ≡ 15 (mod 16)`: c odd, T c = (3c+1)/2
      have hco : c % 2 = 1 := by omega
      have hT4 : T c = (3 * c + 1) / 2 := T_step_odd c hco
      set d := T c with hd
      have hd2 : 2 * d = 3 * c + 1 := by rw [hT4]; omega
      clear_value d; clear hT4 hd
      rcases h with h|h|h <;> omega

/-- **`DescBy n 4 → ¬ Bad16 n`** (all `n`).  Contrapositive of `nondesc4_of_bad16`:
a `Bad16` number is not in `{σ ≤ 4}`. -/
theorem not_bad16_of_descBy4 (n : Nat) (h : DescBy n 4) : ¬ Bad16 n := by
  intro hbad
  obtain ⟨j, hj1, hj4, hlt⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := nondesc4_of_bad16 n hbad
  interval_cases j
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)

/-! ## §4  The descent direction: `¬ Bad16 n` (and `n ≥ 2`) implies `DescBy n 4` -/

/-- **`¬ Bad16 n` and `n ≥ 2` imply `DescBy n 4`.**

Reduce to `n % 16`.  If `n % 4 ≠ 3` then `n` already descends within `3 ≤ 4`
steps (by `descBy3_of_mod4_ne3` from `CollatzStoppingF3`, lifted via
`desc_by_mono`).  Otherwise `n % 4 = 3` and `¬ Bad16 n` forces `n % 16 = 3`,
handled by `descBy4_of_mod16_eq3`. -/
theorem descBy4_of_not_bad16 (n : Nat) (hn : 2 ≤ n) (h : ¬ Bad16 n) :
    DescBy n 4 := by
  by_cases hm4 : n % 4 = 3
  · -- `n % 4 = 3`: the only non-`Bad16` sub-class mod 16 is `n % 16 = 3`.
    have hm16 : n % 16 = 3 := by
      unfold Bad16 at h
      -- `n % 4 = 3 ⇒ n % 16 ∈ {3,7,11,15}`; `¬Bad16` rules out `7,11,15`.
      omega
    exact descBy4_of_mod16_eq3 n hm16
  · exact desc_by_mono n 3 (descBy3_of_mod4_ne3 n hn hm4)

/-- **`descBy4_iff_good16`.** For `n ≥ 2`, the level-4 descending set is exactly
the complement of the three bad residue classes `{7,11,15} (mod 16)`. -/
theorem descBy4_iff_good16 (n : Nat) (hn : 2 ≤ n) :
    DescBy n 4 ↔ ¬ Bad16 n :=
  ⟨not_bad16_of_descBy4 n, descBy4_of_not_bad16 n hn⟩

/-! ## §5  Counting bridge: `count_upto` of `DescBy · 4` vs the `Bad16` classes

We mirror the F(3) counting bridge.  The three residue classes `7,11,15 (mod 16)`
each have density `1/16`, so `{σ≤4}` has density `1 - 3/16 = 13/16`.  We relate
`count_upto (DescBy · 4)` to `count_upto Bad16` and bound the latter via three
applications of `count_residue_class_{upper,lower}_bound` with `m = 16`. -/

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

/-- Exact additivity of `count_upto` over a *disjoint* disjunction. -/
private theorem count_upto_or_disjoint (A B : Nat → Prop)
    (hdis : ∀ k, ¬ (A k ∧ B k)) (N : Nat) :
    count_upto (fun n => A n ∨ B n) N = count_upto A N + count_upto B N := by
  unfold count_upto
  generalize N + 1 = m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
    by_cases hp : A k <;> by_cases hq : B k <;>
      simp [hp, hq] <;> first | omega | exact absurd ⟨hp, hq⟩ (hdis k)

/-- `count_upto {n < 2} N ≤ 2`. -/
private theorem count_upto_lt_two (N : Nat) : count_upto (fun n => n < 2) N ≤ 2 := by
  unfold count_upto
  suffices h : ∀ m, @Nat.count (fun n => n < 2) (fun a => Classical.propDecidable _) m = min m 2 by
    rw [h]; omega
  intro m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, ih]
    by_cases h : k < 2
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-! ### §5a  Counting the `Bad16` class via three residue classes -/

/-- **Exact decomposition of `count_upto Bad16`** into its three disjoint
residue-class counts `(·%16 = 7) + (·%16 = 11) + (·%16 = 15)`. -/
private theorem countBad16_eq (N : Nat) :
    count_upto Bad16 N =
      count_upto (fun n => n % 16 = 7) N
      + count_upto (fun n => n % 16 = 11) N
      + count_upto (fun n => n % 16 = 15) N := by
  -- `Bad16 = (·=7) ∨ ((·=11) ∨ (·=15))` definitionally.
  have hrw : count_upto Bad16 N
      = count_upto (fun n => n % 16 = 7 ∨ (n % 16 = 11 ∨ n % 16 = 15)) N := rfl
  rw [hrw,
      count_upto_or_disjoint (fun n => n % 16 = 7)
        (fun n => n % 16 = 11 ∨ n % 16 = 15) (by intro k; omega) N,
      count_upto_or_disjoint (fun n => n % 16 = 11) (fun n => n % 16 = 15)
        (by intro k; omega) N]
  omega

/-- Residue-class bounds (m = 16) specialised to our three classes. -/
private theorem res7_upper (N : Nat) :
    16 * count_upto (fun n => n % 16 = 7) N ≤ N + 1 + 16 :=
  count_residue_class_upper_bound 16 7 N (by norm_num) (by norm_num)
private theorem res11_upper (N : Nat) :
    16 * count_upto (fun n => n % 16 = 11) N ≤ N + 1 + 16 :=
  count_residue_class_upper_bound 16 11 N (by norm_num) (by norm_num)
private theorem res15_upper (N : Nat) :
    16 * count_upto (fun n => n % 16 = 15) N ≤ N + 1 + 16 :=
  count_residue_class_upper_bound 16 15 N (by norm_num) (by norm_num)
private theorem res7_lower (N : Nat) :
    (N + 1) / 16 ≤ count_upto (fun n => n % 16 = 7) N :=
  count_residue_class_lower_bound 16 7 N (by norm_num) (by norm_num)
private theorem res11_lower (N : Nat) :
    (N + 1) / 16 ≤ count_upto (fun n => n % 16 = 11) N :=
  count_residue_class_lower_bound 16 11 N (by norm_num) (by norm_num)
private theorem res15_lower (N : Nat) :
    (N + 1) / 16 ≤ count_upto (fun n => n % 16 = 15) N :=
  count_residue_class_lower_bound 16 15 N (by norm_num) (by norm_num)

/-! ### §5b  Bridging `{σ≤4}` to `Bad16` -/

/-- **Upper inclusion.** `DescBy n 4 → ¬ Bad16 n`, so the descending count plus
the `Bad16` count is at most `N + 1`. -/
theorem countUpper (N : Nat) :
    count_upto (fun n => DescBy n 4) N + count_upto Bad16 N ≤ N + 1 := by
  have hmono : count_upto (fun n => DescBy n 4) N ≤ count_upto (fun n => ¬ Bad16 n) N :=
    count_upto_mono _ _ (fun k _ hk => not_bad16_of_descBy4 k hk)
  have hcompl := count_upto_compl Bad16 N
  omega

/-- **Lower inclusion.** For `n ≥ 2` with `¬ Bad16 n` we have `DescBy n 4`; only
`n ∈ {0,1}` can fail.  Hence `(N+1) ≤ A4 N + Bad16-count N + 2`. -/
theorem countLower (N : Nat) :
    (N + 1) ≤ count_upto (fun n => DescBy n 4) N + count_upto Bad16 N + 2 := by
  have hmono :
      count_upto (fun n => ¬ Bad16 n) N
        ≤ count_upto (fun n => DescBy n 4 ∨ n < 2) N := by
    refine count_upto_mono _ _ (fun k _ hk => ?_)
    by_cases hk2 : 2 ≤ k
    · exact Or.inl (descBy4_of_not_bad16 k hk2 hk)
    · exact Or.inr (by omega)
  have hsub := count_upto_or (fun n => DescBy n 4) (fun n => n < 2) N
  have hcompl := count_upto_compl Bad16 N
  have hsmall := count_upto_lt_two N
  omega

/-! ## §6  `F(4) = 13/16` density sandwich -/

/-- A `Bad16` lower bound: `16 · B ≥ 3(N+1) - 45`, where `B = count_upto Bad16 N`.
Each of the three disjoint residue classes has count `≥ (N+1)/16`, and
`16 · ((N+1)/16) ≥ (N+1) - 15`. -/
private theorem bad16_lower (N : Nat) :
    3 * (N + 1) ≤ 16 * count_upto Bad16 N + 45 := by
  rw [countBad16_eq N]
  have h7 := res7_lower N
  have h11 := res11_lower N
  have h15 := res15_lower N
  have hdiv : 16 * ((N + 1) / 16) + (N + 1) % 16 = N + 1 := Nat.div_add_mod (N + 1) 16
  have hmod : (N + 1) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have e7 := Nat.mul_le_mul_left 16 h7
  have e11 := Nat.mul_le_mul_left 16 h11
  have e15 := Nat.mul_le_mul_left 16 h15
  omega

/-- A `Bad16` upper bound: `16 · B ≤ 3(N+1) + 48`. -/
private theorem bad16_upper (N : Nat) :
    16 * count_upto Bad16 N ≤ 3 * (N + 1) + 48 := by
  rw [countBad16_eq N]
  have h7 := res7_upper N
  have h11 := res11_upper N
  have h15 := res15_upper N
  omega

/-- **`f4_density_upper` (upper half of the sandwich).**

The natural density of `{σ≤4}` is bounded above by `p/q` for every rational
`p/q > 13/16` (i.e. `13*q < 16*p`).  Concretely `density_bounded {σ≤4} p q`.
The three bad classes `{7,11,15} (mod 16)` together remove `3/16`, leaving
`{σ≤4}` with density `13/16`. -/
theorem f4_density_upper (p q : Nat) (hpq : 13 * q < 16 * p) :
    density_bounded (fun n => DescBy n 4) p q := by
  refine ⟨96 * q + 96, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 4) N with hA
  set B := count_upto Bad16 N with hB
  have hup : A + B ≤ N + 1 := countUpper N
  have hbl : 3 * (N + 1) ≤ 16 * B + 45 := bad16_lower N
  -- `16A ≤ 16(N+1) - 16B ≤ 16(N+1) - (3(N+1) - 45) = 13(N+1) + 45`.
  have h16A : 16 * A ≤ 13 * (N + 1) + 45 := by omega
  have hkey : q * A ≤ p * N := by nlinarith [h16A, hpq, hN]
  simpa [hA] using hkey

/-- **`f4_density_lower` (lower half of the sandwich) — the "almost all descend"
direction.**

The natural density of `{σ≤4}` is bounded below by `p/q` for every rational
`p/q < 13/16` (i.e. `16*p < 13*q`).  Concretely `density_bounded_below {σ≤4} p q`. -/
theorem f4_density_lower (p q : Nat) (hpq : 16 * p < 13 * q) :
    density_bounded_below (fun n => DescBy n 4) p q := by
  refine ⟨96 * q + 96, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 4) N with hA
  set B := count_upto Bad16 N with hB
  have hlo : (N + 1) ≤ A + B + 2 := countLower N
  have hbu : 16 * B ≤ 3 * (N + 1) + 48 := bad16_upper N
  -- `16A ≥ 16(N+1) - 16B - 32 ≥ 16(N+1) - (3(N+1)+48) - 32 = 13(N+1) - 80 ≥ 13N - 80`.
  have h16A : 13 * N ≤ 16 * A + 80 := by omega
  have hkey : p * N ≤ q * A := by nlinarith [h16A, hpq, hN]
  simpa [hA] using hkey

/-! ## §7  Monotonicity and the strict gain `F(4) > F(3)` -/

/-- **`f3_le_f4` — monotonicity of the partial densities (item 3).**

At every cutoff `N`, the count of `{σ≤3}` is `≤` the count of `{σ≤4}`
(immediate from `{σ≤3} ⊆ {σ≤4}`).  Hence `F(3) ≤ F(4)`. -/
theorem f3_le_f4 (N : Nat) :
    count_upto (fun n => DescBy n 3) N ≤ count_upto (fun n => DescBy n 4) N :=
  count_upto_mono _ _ (fun k _ hk => desc_by_mono k 3 hk)

/-- **`desc4_newly_drops` — the strict gain at level 4.**

The residue class `n ≡ 3 (mod 16)` is in `{σ≤4}` but **not** in `{σ≤3}`: it is
the single class that newly drops at level `4`.  (For `n = 16q+3`, descent
happens exactly at the fourth step.)  This witnesses `F(4) > F(3) = 3/4`. -/
theorem desc4_newly_drops (n : Nat) (h : n % 16 = 3) :
    DescBy n 4 ∧ ¬ DescBy n 3 := by
  refine ⟨descBy4_of_mod16_eq3 n h, ?_⟩
  intro h3
  -- `DescBy n 3 → n % 4 ≠ 3` (from `CollatzStoppingF3.mod4_ne3_of_descBy3`),
  -- but `n % 16 = 3 ⇒ n % 4 = 3`.
  exact (mod4_ne3_of_descBy3 n h3) (by omega)

end CollatzStoppingF4
