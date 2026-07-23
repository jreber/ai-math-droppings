import Propositio.NumberTheory.Collatz.Basic

/-!
# Collatz stopping-time density at level 3 — `F(3) = 3/4`

This file extends the Terras stopping-time density theory of `TerrasDensity.lean`
(which establishes the building blocks for `F(2) = 3/4`) one level up, to the
**third stopping-time level**.

## The stopping time and `F(k)`

For the Terras half-step map `T` (`TerrasDensity.T`: `T n = n/2` if `n` even,
`(3n+1)/2` if `n` odd) the *stopping time* of `n` is the least number of
`T`-steps that bring the orbit strictly below `n`.  The Terras density `F(k)`
is the natural density of `{ n : σ(n) ≤ k }`.  Here we work with the
`T`-step predicate

  `DescBy n k  :=  ∃ j, 1 ≤ j ∧ j ≤ k ∧ T_iter n j < n`   ("`σ(n) ≤ k`")

which says the orbit of `n` drops below `n` within the first `k` steps.

## What is proved (all DENSITY statements — NOT termination)

This is a **density** result: it characterises the proportion of integers with a
short stopping time.  It does NOT assert that every Collatz trajectory
terminates.

1. **Enumeration-pinned value.**  A `#eval` sweep over residues mod `8` shows
   the residues with `σ ≤ 3` are exactly `{0,1,2,4,5,6}` (six of eight); residues
   `3` and `7` (i.e. `n ≡ 3 mod 4`) never descend within three steps.  Hence
   `F(3) = 6/8 = 3/4`.  Crucially, an enumeration over `n ≤ 2000` finds
   **no integer with stopping time exactly 3**, so `{σ ≤ 3} = {σ ≤ 2}` and
   `F(3) = F(2) = 3/4` — the partial density at level 3 is zero.

2. **`desc_by_mono` / `f2_le_f3` (item 3).**  Set inclusion `{σ≤k} ⊆ {σ≤k+1}`
   and the monotonicity `F(2) ≤ F(3)` at the counting level.

3. **`desc_three_iff_two` (the new structural fact).**  For every `n`,
   `DescBy n 3 ↔ DescBy n 2`: no integer has stopping time exactly `3`.

4. **`descBy3_iff_mod4_ne3`.**  For `n ≥ 2`, `DescBy n 3 ↔ n % 4 ≠ 3`: the
   level-3 descending set is exactly the non-`(3 mod 4)` class (off the single
   exceptional point `n = 1`).

5. **Density `F(3) = 3/4` (sandwich, items 1 + 2 of the brief).**
   - `f3_density_upper`  : `density_bounded {σ≤3} p q`        for `3*q < 4*p`.
   - `f3_density_lower`  : `density_bounded_below {σ≤3} p q`   for `4*p < 3*q`.
   Together these sandwich the natural density of `{σ≤3}` at exactly `3/4`,
   in the same ε-bound style as `TerrasDensity`'s residue-class results.

## Axiom hygiene

Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzStoppingF3

open TerrasDensity

attribute [local instance] Classical.propDecidable

/-! ## §1  Single-step descent algebra -/

/-- One Terras step on an even number halves it. -/
theorem T_step_even (n : Nat) (h : n % 2 = 0) : T n = n / 2 := by
  unfold T; simp [h]

/-- One Terras step on an odd number is `(3n+1)/2`. -/
theorem T_step_odd (n : Nat) (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  unfold T; rw [if_neg (by omega)]

/-- Iterate unfolding: `T_iter n 1 = T n`. -/
theorem T_iter_one (n : Nat) : T_iter n 1 = T n := rfl
/-- Iterate unfolding: `T_iter n 2 = T (T n)`. -/
theorem T_iter_two (n : Nat) : T_iter n 2 = T (T n) := rfl
/-- Iterate unfolding: `T_iter n 3 = T (T (T n))`. -/
theorem T_iter_three (n : Nat) : T_iter n 3 = T (T (T n)) := rfl

/-! ## §2  The stopping-time predicate and monotonicity -/

/-- `DescBy n k`: the orbit of `n` drops below `n` within the first `k` Terras
steps — i.e. the Terras stopping time satisfies `σ(n) ≤ k`. -/
def DescBy (n k : Nat) : Prop :=
  ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ T_iter n j < n

/-- **Monotonicity (item 3, set inclusion).** `{σ≤k} ⊆ {σ≤k+1}`:
descending within `k` steps implies descending within `k+1` steps. -/
theorem desc_by_mono (n k : Nat) (h : DescBy n k) : DescBy n (k + 1) := by
  obtain ⟨j, hj1, hjk, hlt⟩ := h
  exact ⟨j, hj1, Nat.le_succ_of_le hjk, hlt⟩

/-! ## §3  No integer has stopping time exactly 3 -/

/-- **Forward descent: `n % 4 ≠ 3` (and `n ≥ 2`) descends within two steps.**

If `n ≥ 2` and `n` is not `≡ 3 (mod 4)`, then either the first or the second
Terras step already lands below `n`.  (Even `n` halve immediately; `n ≡ 1
(mod 4)` reach `3k+1 < 4k+1` in two steps.) -/
theorem desc2_of_mod4_ne3 (n : Nat) (hn : 2 ≤ n) (h : n % 4 ≠ 3) :
    (T_iter n 1 < n) ∨ (T_iter n 2 < n) := by
  rw [T_iter_one, T_iter_two]
  by_cases he : n % 2 = 0
  · exact Or.inl (by rw [T_step_even n he]; omega)
  · refine Or.inr ?_
    have ho : n % 2 = 1 := by omega
    have hTn : T n = (3 * n + 1) / 2 := T_step_odd n ho
    have hTn_even : ((3 * n + 1) / 2) % 2 = 0 := by omega
    rw [hTn, T_step_even _ hTn_even]
    omega

/-- **Non-descent: `n ≡ 3 (mod 4)` does not descend within three steps.**

For every `n` with `n % 4 = 3`, all three of `T n, T² n, T³ n` are `≥ n`.
(Case-split on `n mod 8`: `8q+3 ↦ 12q+5, 18q+8, 9q+4`; `8q+7 ↦ 12q+11,
18q+17, 27q+26`; in both cases every iterate is `≥ n`.) -/
theorem nondesc3_of_mod4_eq3 (n : Nat) (h : n % 4 = 3) :
    n ≤ T_iter n 1 ∧ n ≤ T_iter n 2 ∧ n ≤ T_iter n 3 := by
  rw [T_iter_one, T_iter_two, T_iter_three]
  have ho : n % 2 = 1 := by omega
  have hTn : T n = (3 * n + 1) / 2 := T_step_odd n ho
  have hTn_odd : (T n) % 2 = 1 := by rw [hTn]; omega
  have hT2n : T (T n) = (3 * (T n) + 1) / 2 := T_step_odd (T n) hTn_odd
  by_cases hc : (T (T n)) % 2 = 0
  · -- `n ≡ 3 (mod 8)`: third iterate is even, equals `9q+4 ≥ n`.
    have hT3n : T (T (T n)) = (T (T n)) / 2 := T_step_even _ hc
    rw [hTn, hT2n] at *
    refine ⟨by omega, by omega, ?_⟩
    rw [hT3n]; omega
  · -- `n ≡ 7 (mod 8)`: third iterate is `(3·(18q+17)+1)/2 = 27q+26 ≥ n`.
    have hT2odd : (T (T n)) % 2 = 1 := by omega
    have hT3n : T (T (T n)) = (3 * (T (T n)) + 1) / 2 := T_step_odd _ hT2odd
    rw [hTn, hT2n] at *
    refine ⟨by omega, by omega, ?_⟩
    rw [hT3n]; omega

/-- **`DescBy n 3 → n % 4 ≠ 3`** (holds for all `n`).  The contrapositive of
`nondesc3_of_mod4_eq3`: if `n ≡ 3 (mod 4)` then none of the first three steps
descends, so `n` is not in `{σ ≤ 3}`. -/
theorem mod4_ne3_of_descBy3 (n : Nat) (h : DescBy n 3) : n % 4 ≠ 3 := by
  intro hmod
  obtain ⟨j, hj1, hj3, hlt⟩ := h
  obtain ⟨h1, h2, h3⟩ := nondesc3_of_mod4_eq3 n hmod
  interval_cases j
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)

/-- **`n % 4 ≠ 3` and `n ≥ 2` imply `DescBy n 3`.** Lift `desc2_of_mod4_ne3`
into the `DescBy` predicate (descent within `2 ≤ 3` steps). -/
theorem descBy3_of_mod4_ne3 (n : Nat) (hn : 2 ≤ n) (h : n % 4 ≠ 3) :
    DescBy n 3 := by
  rcases desc2_of_mod4_ne3 n hn h with h1 | h2
  · exact ⟨1, by omega, by omega, h1⟩
  · exact ⟨2, by omega, by omega, h2⟩

/-- **`descBy3_iff_mod4_ne3`.** For `n ≥ 2`, the level-3 descending set is
exactly the non-`(3 mod 4)` residue class. -/
theorem descBy3_iff_mod4_ne3 (n : Nat) (hn : 2 ≤ n) :
    DescBy n 3 ↔ n % 4 ≠ 3 :=
  ⟨mod4_ne3_of_descBy3 n, descBy3_of_mod4_ne3 n hn⟩

/-- **`desc_three_iff_two` — the partial density at level 3 is zero.**

For every `n`, `DescBy n 3 ↔ DescBy n 2`: no integer has stopping time exactly
three, so `{σ≤3} = {σ≤2}` and `F(3) = F(2) = 3/4`. -/
theorem desc_three_iff_two (n : Nat) : DescBy n 3 ↔ DescBy n 2 := by
  constructor
  · intro h3
    -- `DescBy n 3 → n % 4 ≠ 3 → descends within 2`.
    have hmod : n % 4 ≠ 3 := mod4_ne3_of_descBy3 n h3
    -- handle small `n` directly: `DescBy n 3` already forces a witness, and for
    -- `n < 2` there is no descent at all, so the hypothesis is vacuous there.
    by_cases hn : 2 ≤ n
    · rcases desc2_of_mod4_ne3 n hn hmod with h1 | h2
      · exact ⟨1, by omega, by omega, h1⟩
      · exact ⟨2, by omega, by omega, h2⟩
    · -- `n = 0` or `n = 1`: `T_iter n j ≥ n`, contradicting the witness in `h3`.
      exfalso
      obtain ⟨j, hj1, hj3, hlt⟩ := h3
      interval_cases n
      · exact absurd hlt (Nat.not_lt_zero _)
      · -- n = 1: T 1 = 2, T² 1 = 1, T³ 1 = 2; none < 1.
        interval_cases j <;> simp [T_iter, T] at hlt
  · exact fun h2 => desc_by_mono n 2 h2

/-! ## §4  Counting bridge: `count_upto` of `DescBy · 3`

`density_bounded`/`density_bounded_below` are phrased through `TerrasDensity.count_upto`
(a thin wrapper over `Nat.count` using the same local `Classical.propDecidable`
instance we declared above).  We relate `count_upto (DescBy · 3)` to the residue
class `{n % 4 = 3}` whose density is controlled by
`TerrasDensity.count_residue_class_{upper,lower}_bound`. -/

/-- Instance-bridging for `Nat.count` (all `DecidablePred` instances agree). -/
private theorem count_inst_eq {P : Nat → Prop} (i₁ i₂ : DecidablePred P) (n : Nat) :
    @Nat.count P i₁ n = @Nat.count P i₂ n := by
  cases Subsingleton.elim i₁ i₂; rfl

/-- `count_upto` monotonicity: included predicates have `≤` counts.  This is the
single bridge between `Nat.count_mono_left` and our classical `count_upto`. -/
private theorem count_upto_mono {N : Nat} (A B : Nat → Prop)
    (h : ∀ k, k < N + 1 → A k → B k) :
    count_upto A N ≤ count_upto B N := by
  unfold count_upto
  rw [count_inst_eq (fun a => Classical.propDecidable _) (Classical.decPred _) (N + 1),
      count_inst_eq (fun a => Classical.propDecidable _) (Classical.decPred _) (N + 1)]
  exact Nat.count_mono_left h

/-- Complement identity, phrased through `count_upto`:
`count_upto (¬A) N + count_upto A N = N + 1`. -/
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

/-- `count_upto {n < 2} N ≤ 2`. -/
private theorem count_upto_lt_two (N : Nat) : count_upto (fun n => n < 2) N ≤ 2 := by
  unfold count_upto
  -- prove `count {·<2} m ≤ 2` together with the sharper `count {·<2} m = min m 2`
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

/-- `count_upto` of the level-3 descending set, related to the `{·%4 = 3}` count.
`A3 N := count_upto (DescBy · 3) N`, and `R3 N := count_upto (·%4 = 3) N`.

**Upper inclusion.** `DescBy n 3 → n % 4 ≠ 3`, so the descending count plus the
`{·%4 = 3}` count is at most `N + 1`. -/
theorem countUpper (N : Nat) :
    count_upto (fun n => DescBy n 3) N + count_upto (fun n => n % 4 = 3) N ≤ N + 1 := by
  -- `DescBy · 3` is included in the complement of `{·%4 = 3}`.
  have hmono : count_upto (fun n => DescBy n 3) N ≤ count_upto (fun n => ¬ (n % 4 = 3)) N :=
    count_upto_mono _ _ (fun k _ hk => mod4_ne3_of_descBy3 k hk)
  have hcompl := count_upto_compl (fun n => n % 4 = 3) N
  omega

/-- **Lower inclusion.** For `n ≥ 2` with `n % 4 ≠ 3` we have `DescBy n 3`; only
`n ∈ {0,1}` can fail.  Hence `(N+1) ≤ A3 N + R3 N + 2`. -/
theorem countLower (N : Nat) :
    (N + 1) ≤
      count_upto (fun n => DescBy n 3) N + count_upto (fun n => n % 4 = 3) N + 2 := by
  -- complement of `{·%4=3}` is included in `DescBy·3 ∪ {n<2}`.
  have hmono :
      count_upto (fun n => ¬ (n % 4 = 3)) N
        ≤ count_upto (fun n => DescBy n 3 ∨ n < 2) N := by
    refine count_upto_mono _ _ (fun k _ hk => ?_)
    by_cases hk2 : 2 ≤ k
    · exact Or.inl (descBy3_of_mod4_ne3 k hk2 hk)
    · exact Or.inr (by omega)
  have hsub := count_upto_or (fun n => DescBy n 3) (fun n => n < 2) N
  have hcompl := count_upto_compl (fun n => n % 4 = 3) N
  have hsmall := count_upto_lt_two N
  omega

/-! ## §5  `F(3) = 3/4` density sandwich -/

/-- Bridge: rewrite `count_upto (·%4 = 3)` to the canonical-instance `Nat.count`
used inside the `TerrasDensity` residue bounds. -/
private theorem residueCount_upper (N : Nat) :
    4 * count_upto (fun n => n % 4 = 3) N ≤ N + 1 + 4 :=
  count_residue_class_upper_bound 4 3 N (by norm_num) (by norm_num)

private theorem residueCount_lower (N : Nat) :
    (N + 1) / 4 ≤ count_upto (fun n => n % 4 = 3) N :=
  count_residue_class_lower_bound 4 3 N (by norm_num) (by norm_num)

/-- **`f3_density_upper` (item 1, upper half of the sandwich).**

The natural density of `{σ≤3}` is bounded above by `p/q` for every rational
`p/q > 3/4` (i.e. `3*q < 4*p`).  Concretely `density_bounded {σ≤3} p q`. -/
theorem f3_density_upper (p q : Nat) (hpq : 3 * q < 4 * p) :
    density_bounded (fun n => DescBy n 3) p q := by
  refine ⟨6 * q + 6, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 3) N with hA
  set R := count_upto (fun n => n % 4 = 3) N with hR
  have hup : A + R ≤ N + 1 := countUpper N
  have hrl : (N + 1) / 4 ≤ R := residueCount_lower N
  -- `4*((N+1)/4) ≥ (N+1) - 3`, so `4*R ≥ N - 2`.
  have hdiv : 4 * ((N + 1) / 4) + (N + 1) % 4 = N + 1 := Nat.div_add_mod (N + 1) 4
  have hmod : (N + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4R : (N + 1) ≤ 4 * R + 4 := by
    have := Nat.mul_le_mul_left 4 hrl
    omega
  -- From `A + R ≤ N+1` and `N+1 ≤ 4R+4`: `4A ≤ 3(N+1)+3`.
  have h4A : 4 * A ≤ 3 * (N + 1) + 3 := by omega
  -- Combine with `3q < 4p` and `N ≥ 6q+6`.
  have hkey : q * A ≤ p * N := by nlinarith [h4A, hpq, hN]
  -- bridge `count_upto`'s instance is already the same; conclude.
  simpa [hA] using hkey

/-- **`f3_density_lower` (item 1, lower half of the sandwich) — the "almost all
descend" direction.**

The natural density of `{σ≤3}` is bounded below by `p/q` for every rational
`p/q < 3/4` (i.e. `4*p < 3*q`).  Concretely `density_bounded_below {σ≤3} p q`. -/
theorem f3_density_lower (p q : Nat) (hpq : 4 * p < 3 * q) :
    density_bounded_below (fun n => DescBy n 3) p q := by
  refine ⟨9 * q + 9, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 3) N with hA
  set R := count_upto (fun n => n % 4 = 3) N with hR
  have hlo : (N + 1) ≤ A + R + 2 := countLower N
  have hru : 4 * R ≤ N + 1 + 4 := residueCount_upper N
  -- `4A ≥ 4(N+1) - 4R - 8 ≥ 4(N+1) - (N+5) - 8 = 3N - 9`.
  have h4A : 3 * N ≤ 4 * A + 9 := by omega
  -- Combine with `4p < 3q` and `N ≥ 9q+9`.
  have hkey : p * N ≤ q * A := by nlinarith [h4A, hpq, hN]
  simpa [hA] using hkey

/-! ## §6  `F(2) ≤ F(3)` at the counting level (item 3) -/

/-- **`f2_le_f3` — monotonicity of the partial densities.**

At every cutoff `N`, the count of `{σ≤2}` is `≤` the count of `{σ≤3}`
(immediate from `{σ≤2} ⊆ {σ≤3}`).  Hence `F(2) ≤ F(3)`.  (In fact the two are
equal by `desc_three_iff_two`, so `F(2) = F(3) = 3/4`.) -/
theorem f2_le_f3 (N : Nat) :
    count_upto (fun n => DescBy n 2) N ≤ count_upto (fun n => DescBy n 3) N :=
  count_upto_mono _ _ (fun k _ hk => desc_by_mono k 2 hk)

end CollatzStoppingF3
