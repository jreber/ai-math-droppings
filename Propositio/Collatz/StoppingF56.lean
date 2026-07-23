import Propositio.Collatz.Basic
import Propositio.Collatz.StoppingF3
import Propositio.Collatz.StoppingF4
import Propositio.Collatz.BadDensity

/-!
# Collatz stopping-time density at levels 5 and 6 — `F(5) = F(6) = 7/8`

This file extends the Terras stopping-time density ladder two further levels, from
`F(4) = 13/16` (`CollatzStoppingF4.lean`) to the **fifth** and **sixth** levels,
and establishes the **bad-residue LIFTING structure** — the path toward
`b(k) → 0` ("almost all integers descend").

## The stopping time and `F(k)` (recap)

For the Terras half-step map `T` (`TerrasDensity.T`: `T n = n/2` if `n` even,
`(3n+1)/2` if `n` odd) the *stopping time* `σ(n)` is the least number of
`T`-steps that bring the orbit strictly below `n`, and `F(k)` is the natural
density of `{ n : σ(n) ≤ k }`.  We reuse `CollatzStoppingF3.DescBy`:

  `DescBy n k  :=  ∃ j, 1 ≤ j ∧ j ≤ k ∧ T_iter n j < n`   ("`σ(n) ≤ k`").

## What is proved (all DENSITY statements — NOT per-orbit termination)

This is a **density** result about the *proportion* of integers with a short
stopping time.  It does **NOT** assert that any individual Collatz trajectory
terminates.

The surviving-residue counts (enumeration-pinned, `#eval`-stable across offsets
`1 … 9999999`) are

  `β(1), …, β(6)  =  1, 1, 2, 3, 4, 8`

with explicit survivor sets
  `mod 8 : {3,7}`,   `mod 16 : {7,11,15}`,
  `mod 32 : {7,15,27,31}`,   `mod 64 : {7,15,27,31,39,47,59,63}`.

Hence

  `F(5) = 1 − β(5)/2^5 = 1 − 4/32 = 28/32 = 7/8`,
  `F(6) = 1 − β(6)/2^6 = 1 − 8/64 = 56/64 = 7/8`,

so `b(5) = b(6) = 1/8` and `F(5) = F(6)` (no integer has stopping time
exactly `6`, in the density sense β(6)/64 = β(5)/32).

1. **F(5)** : residue characterization `descBy5_iff_good32` (for `n ≥ 2`,
   `DescBy n 5 ↔ n % 32 ∉ {7,15,27,31}`) by a mod-32 parity case analysis, and the
   density sandwich `f5_density_upper` / `f5_density_lower` at `7/8`.
2. **F(6)** : the analogous result at mod 64, survivor set
   `{7,15,27,31,39,47,59,63}`; `descBy6_iff_good64` and the sandwich
   `f6_density_upper` / `f6_density_lower` at `7/8`.
3. **Monotonicity** : `f4_le_f5`, `f5_le_f6` (set inclusion `{σ≤k} ⊆ {σ≤k+1}`),
   plus the strict gain `f4_lt_f5` (`F(4) < F(5)`).
4. **Lifting structure** `survivor_lift` : a survivor mod `2^(k+1)` projects (mod
   `2^k`) onto a survivor mod `2^k`.  Concretely, if `Bad (k+1) n` then `Bad k n`,
   i.e. the bad sets are *antitone* in `k`; combined with the residue
   characterizations this says the surviving residues mod `2^(k+1)` reduce mod
   `2^k` to surviving residues mod `2^k`.  Each survivor mod `2^k` has at most two
   lifts mod `2^(k+1)`, so `β(k+1) ≤ 2·β(k)`; the open input is `β(k+1) ≤ c·β(k)`
   with `c < 2` (which gives `b(k) → 0`).  See §lift for the precise gap.

## Axiom hygiene

Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzStoppingF56

open TerrasDensity
open CollatzStoppingF3
open CollatzStoppingF4
open CollatzBadDensity

attribute [local instance] Classical.propDecidable

/-! ## §1  Fifth-iterate unfolding -/

/-- Iterate unfolding: `T_iter n 5 = T (T (T (T (T n))))`. -/
theorem T_iter_five (n : Nat) : T_iter n 5 = T (T (T (T (T n)))) := rfl

/-! ## §2  The newly-dropping classes mod 32 at level 5

Within `Bad16` `{7,11,15} (mod 16)`, the mod-32 refinements that **newly drop at
the fifth step** are `n ≡ 11 (mod 32)` and `n ≡ 23 (mod 32)`.  The four classes
`{7,15,27,31} (mod 32)` survive all five steps. -/

/-- **`n ≡ 11 (mod 32)` descends on the fifth step.**
For `n = 32q+11` the Terras iterates are `48q+17, 72q+26, 36q+13, 54q+20, 27q+10`
and `27q+10 < 32q+11`. -/
theorem desc5_of_mod32_eq11 (n : Nat) (h : n % 32 = 11) : T_iter n 5 < n := by
  rw [T_iter_five]
  have ho : n % 2 = 1 := by omega
  have hTn : T n = (3 * n + 1) / 2 := T_step_odd n ho
  set a := T n with ha
  have ha2 : 2 * a = 3 * n + 1 := by rw [hTn]; omega
  clear_value a; clear hTn ha
  have hao : a % 2 = 1 := by omega
  have hT2 : T a = (3 * a + 1) / 2 := T_step_odd a hao
  set b := T a with hb
  have hb2 : 2 * b = 3 * a + 1 := by rw [hT2]; omega
  clear_value b; clear hT2 hb
  have hbe : b % 2 = 0 := by omega
  have hT3 : T b = b / 2 := T_step_even b hbe
  set c := T b with hc
  have hc2 : 2 * c = b := by rw [hT3]; omega
  clear_value c; clear hT3 hc
  have hco : c % 2 = 1 := by omega
  have hT4 : T c = (3 * c + 1) / 2 := T_step_odd c hco
  set d := T c with hd
  have hd2 : 2 * d = 3 * c + 1 := by rw [hT4]; omega
  clear_value d; clear hT4 hd
  have hde : d % 2 = 0 := by omega
  have hT5 : T d = d / 2 := T_step_even d hde
  rw [hT5]; omega

/-- **`n ≡ 23 (mod 32)` descends on the fifth step.**
For `n = 32q+23` the Terras iterates are `48q+35, 72q+53, 108q+80, 54q+40, 27q+20`
and `27q+20 < 32q+23`. -/
theorem desc5_of_mod32_eq23 (n : Nat) (h : n % 32 = 23) : T_iter n 5 < n := by
  rw [T_iter_five]
  have ho : n % 2 = 1 := by omega
  have hTn : T n = (3 * n + 1) / 2 := T_step_odd n ho
  set a := T n with ha
  have ha2 : 2 * a = 3 * n + 1 := by rw [hTn]; omega
  clear_value a; clear hTn ha
  have hao : a % 2 = 1 := by omega
  have hT2 : T a = (3 * a + 1) / 2 := T_step_odd a hao
  set b := T a with hb
  have hb2 : 2 * b = 3 * a + 1 := by rw [hT2]; omega
  clear_value b; clear hT2 hb
  have hbo : b % 2 = 1 := by omega
  have hT3 : T b = (3 * b + 1) / 2 := T_step_odd b hbo
  set c := T b with hc
  have hc2 : 2 * c = 3 * b + 1 := by rw [hT3]; omega
  clear_value c; clear hT3 hc
  have hce : c % 2 = 0 := by omega
  have hT4 : T c = c / 2 := T_step_even c hce
  set d := T c with hd
  have hd2 : 2 * d = c := by rw [hT4]; omega
  clear_value d; clear hT4 hd
  have hde : d % 2 = 0 := by omega
  have hT5 : T d = d / 2 := T_step_even d hde
  rw [hT5]; omega

/-! ## §3  The four survivors `{7,15,27,31} (mod 32)` do not descend in 5 steps -/

/-- `Bad32 n`: the level-5 non-descending residues mod 32, namely
`n % 32 ∈ {7, 15, 27, 31}`. -/
def Bad32 (n : Nat) : Prop :=
  n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31

/-- Five-step non-descent for `n ≡ 7 (mod 32)` (`n = 32q+7`; iterates
`48q+11, 72q+17, 108q+26, 54q+13, 81q+20`), in explicit-linear form. -/
private theorem nondesc5_eq7 (n : Nat) (h : n % 32 = 7) :
    n ≤ T n ∧ n ≤ T (T n) ∧ n ≤ T (T (T n))
      ∧ n ≤ T (T (T (T n))) ∧ n ≤ T (T (T (T (T n)))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 7 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 7) = 48 * q + 11 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 11) = 72 * q + 17 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 17) = 108 * q + 26 := by rw [T_step_odd _ (by omega)]; omega
  have e4 : T (108 * q + 26) = 54 * q + 13 := by rw [T_step_even _ (by omega)]; omega
  have e5 : T (54 * q + 13) = 81 * q + 20 := by rw [T_step_odd _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]; refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Five-step non-descent for `n ≡ 15 (mod 32)` (`n = 32q+15`; iterates
`48q+23, 72q+35, 108q+53, 162q+80, 81q+40`). -/
private theorem nondesc5_eq15 (n : Nat) (h : n % 32 = 15) :
    n ≤ T n ∧ n ≤ T (T n) ∧ n ≤ T (T (T n))
      ∧ n ≤ T (T (T (T n))) ∧ n ≤ T (T (T (T (T n)))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 15 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 15) = 48 * q + 23 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 23) = 72 * q + 35 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 35) = 108 * q + 53 := by rw [T_step_odd _ (by omega)]; omega
  have e4 : T (108 * q + 53) = 162 * q + 80 := by rw [T_step_odd _ (by omega)]; omega
  have e5 : T (162 * q + 80) = 81 * q + 40 := by rw [T_step_even _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]; refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Five-step non-descent for `n ≡ 27 (mod 32)` (`n = 32q+27`; iterates
`48q+41, 72q+62, 36q+31, 54q+47, 81q+71`). -/
private theorem nondesc5_eq27 (n : Nat) (h : n % 32 = 27) :
    n ≤ T n ∧ n ≤ T (T n) ∧ n ≤ T (T (T n))
      ∧ n ≤ T (T (T (T n))) ∧ n ≤ T (T (T (T (T n)))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 27 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 27) = 48 * q + 41 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 41) = 72 * q + 62 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 62) = 36 * q + 31 := by rw [T_step_even _ (by omega)]; omega
  have e4 : T (36 * q + 31) = 54 * q + 47 := by rw [T_step_odd _ (by omega)]; omega
  have e5 : T (54 * q + 47) = 81 * q + 71 := by rw [T_step_odd _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]; refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Five-step non-descent for `n ≡ 31 (mod 32)` (`n = 32q+31`; iterates
`48q+47, 72q+71, 108q+107, 162q+161, 243q+242`). -/
private theorem nondesc5_eq31 (n : Nat) (h : n % 32 = 31) :
    n ≤ T n ∧ n ≤ T (T n) ∧ n ≤ T (T (T n))
      ∧ n ≤ T (T (T (T n))) ∧ n ≤ T (T (T (T (T n)))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 31 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 31) = 48 * q + 47 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 47) = 72 * q + 71 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 71) = 108 * q + 107 := by rw [T_step_odd _ (by omega)]; omega
  have e4 : T (108 * q + 107) = 162 * q + 161 := by rw [T_step_odd _ (by omega)]; omega
  have e5 : T (162 * q + 161) = 243 * q + 242 := by rw [T_step_odd _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]; refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **Non-descent: a `Bad32` number does not descend within five Terras steps.**

For `n` with `n % 32 ∈ {7,15,27,31}`, all five of `T n, …, T⁵ n` are `≥ n`.  We
dispatch each concrete survivor residue to its straight-line walker, so every
branch carries a *fixed* residue with determined parities — keeping the proof
linear and memory bounded (no `2^4`-way `by_cases` tree). -/
theorem nondesc5_of_bad32 (n : Nat) (h : Bad32 n) :
    n ≤ T_iter n 1 ∧ n ≤ T_iter n 2 ∧ n ≤ T_iter n 3
      ∧ n ≤ T_iter n 4 ∧ n ≤ T_iter n 5 := by
  rw [T_iter_one, T_iter_two, T_iter_three, T_iter_four, T_iter_five]
  rcases h with h | h | h | h
  · exact nondesc5_eq7 n h
  · exact nondesc5_eq15 n h
  · exact nondesc5_eq27 n h
  · exact nondesc5_eq31 n h

/-- **`DescBy n 5 → ¬ Bad32 n`** (all `n`).  Contrapositive of
`nondesc5_of_bad32`: a `Bad32` number is not in `{σ ≤ 5}`. -/
theorem not_bad32_of_descBy5 (n : Nat) (h : DescBy n 5) : ¬ Bad32 n := by
  intro hbad
  obtain ⟨j, hj1, hj5, hlt⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := nondesc5_of_bad32 n hbad
  interval_cases j
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)

/-! ## §4  The descent direction: `¬ Bad32 n` (and `n ≥ 2`) implies `DescBy n 5` -/

/-- **`¬ Bad32 n` and `n ≥ 2` imply `DescBy n 5`.**

Case on whether `n` is `Bad16`.  If `¬ Bad16 n` then `n` descends within `4 ≤ 5`
steps (`descBy4_of_not_bad16` lifted by `desc_by_mono`).  Otherwise `Bad16 n`
(`n % 16 ∈ {7,11,15}`); among its two mod-32 refinements `¬ Bad32 n` forces
`n % 32 ∈ {11, 23}`, both of which descend on the fifth step. -/
theorem descBy5_of_not_bad32 (n : Nat) (hn : 2 ≤ n) (h : ¬ Bad32 n) :
    DescBy n 5 := by
  by_cases hb16 : Bad16 n
  · -- `n % 16 ∈ {7,11,15}`; mod-32 the non-`Bad32` refinements are `{11,23}`.
    have hm : n % 32 = 11 ∨ n % 32 = 23 := by
      unfold Bad16 at hb16
      unfold Bad32 at h
      omega
    rcases hm with hm | hm
    · exact ⟨5, by omega, by omega, desc5_of_mod32_eq11 n hm⟩
    · exact ⟨5, by omega, by omega, desc5_of_mod32_eq23 n hm⟩
  · exact desc_by_mono n 4 (descBy4_of_not_bad16 n hn hb16)

/-- **`descBy5_iff_good32`.** For `n ≥ 2`, the level-5 descending set is exactly
the complement of the four bad residue classes `{7,15,27,31} (mod 32)`. -/
theorem descBy5_iff_good32 (n : Nat) (hn : 2 ≤ n) :
    DescBy n 5 ↔ ¬ Bad32 n :=
  ⟨not_bad32_of_descBy5 n, descBy5_of_not_bad32 n hn⟩

/-! ## §5  Counting bridge: `count_upto (DescBy · 5)` vs the four `Bad32` classes

We mirror the F(4) counting bridge.  The four residue classes
`7,15,27,31 (mod 32)` each have density `1/32`, so `{σ≤5}` has density
`1 − 4/32 = 28/32 = 7/8`.  We relate `count_upto (DescBy · 5)` to
`count_upto Bad32` and bound the latter via four applications of
`count_residue_class_{upper,lower}_bound` with `m = 32`. -/

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

/-- **Exact decomposition of `count_upto Bad32`** into its four disjoint
residue-class counts `(·%32 = 7) + (·%32 = 15) + (·%32 = 27) + (·%32 = 31)`. -/
private theorem countBad32_eq (N : Nat) :
    count_upto Bad32 N =
      count_upto (fun n => n % 32 = 7) N
      + count_upto (fun n => n % 32 = 15) N
      + count_upto (fun n => n % 32 = 27) N
      + count_upto (fun n => n % 32 = 31) N := by
  have hrw : count_upto Bad32 N
      = count_upto (fun n => n % 32 = 7
          ∨ (n % 32 = 15 ∨ (n % 32 = 27 ∨ n % 32 = 31))) N := rfl
  rw [hrw,
      count_upto_or_disjoint (fun n => n % 32 = 7)
        (fun n => n % 32 = 15 ∨ (n % 32 = 27 ∨ n % 32 = 31)) (by intro k; omega) N,
      count_upto_or_disjoint (fun n => n % 32 = 15)
        (fun n => n % 32 = 27 ∨ n % 32 = 31) (by intro k; omega) N,
      count_upto_or_disjoint (fun n => n % 32 = 27) (fun n => n % 32 = 31)
        (by intro k; omega) N]
  omega

private theorem res32_upper (r N : Nat) (hr : r < 32) :
    32 * count_upto (fun n => n % 32 = r) N ≤ N + 1 + 32 :=
  count_residue_class_upper_bound 32 r N (by norm_num) hr
private theorem res32_lower (r N : Nat) (hr : r < 32) :
    (N + 1) / 32 ≤ count_upto (fun n => n % 32 = r) N :=
  count_residue_class_lower_bound 32 r N (by norm_num) hr

/-- `32 · #Bad32 ≤ 4(N+1) + 128`. -/
private theorem bad32_upper (N : Nat) :
    32 * count_upto Bad32 N ≤ 4 * (N + 1) + 128 := by
  rw [countBad32_eq N]
  have h7 := res32_upper 7 N (by norm_num)
  have h15 := res32_upper 15 N (by norm_num)
  have h27 := res32_upper 27 N (by norm_num)
  have h31 := res32_upper 31 N (by norm_num)
  omega

/-- `4(N+1) ≤ 32 · #Bad32 + 124`. -/
private theorem bad32_lower (N : Nat) :
    4 * (N + 1) ≤ 32 * count_upto Bad32 N + 124 := by
  rw [countBad32_eq N]
  have h7 := res32_lower 7 N (by norm_num)
  have h15 := res32_lower 15 N (by norm_num)
  have h27 := res32_lower 27 N (by norm_num)
  have h31 := res32_lower 31 N (by norm_num)
  have hdiv : 32 * ((N + 1) / 32) + (N + 1) % 32 = N + 1 := Nat.div_add_mod (N + 1) 32
  have hmod : (N + 1) % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have e7 := Nat.mul_le_mul_left 32 h7
  have e15 := Nat.mul_le_mul_left 32 h15
  have e27 := Nat.mul_le_mul_left 32 h27
  have e31 := Nat.mul_le_mul_left 32 h31
  omega

/-- **Upper inclusion.** `DescBy n 5 → ¬ Bad32 n`, so the descending count plus
the `Bad32` count is at most `N + 1`. -/
theorem countUpper5 (N : Nat) :
    count_upto (fun n => DescBy n 5) N + count_upto Bad32 N ≤ N + 1 := by
  have hmono : count_upto (fun n => DescBy n 5) N ≤ count_upto (fun n => ¬ Bad32 n) N :=
    count_upto_mono _ _ (fun k _ hk => not_bad32_of_descBy5 k hk)
  have hcompl := count_upto_compl Bad32 N
  omega

/-- **Lower inclusion.** For `n ≥ 2` with `¬ Bad32 n` we have `DescBy n 5`; only
`n ∈ {0,1}` can fail.  Hence `(N+1) ≤ A5 N + Bad32-count N + 2`. -/
theorem countLower5 (N : Nat) :
    (N + 1) ≤ count_upto (fun n => DescBy n 5) N + count_upto Bad32 N + 2 := by
  have hmono :
      count_upto (fun n => ¬ Bad32 n) N
        ≤ count_upto (fun n => DescBy n 5 ∨ n < 2) N := by
    refine count_upto_mono _ _ (fun k _ hk => ?_)
    by_cases hk2 : 2 ≤ k
    · exact Or.inl (descBy5_of_not_bad32 k hk2 hk)
    · exact Or.inr (by omega)
  have hsub := count_upto_or (fun n => DescBy n 5) (fun n => n < 2) N
  have hcompl := count_upto_compl Bad32 N
  have hsmall := count_upto_lt_two N
  omega

/-! ## §6  `F(5) = 7/8` density sandwich -/

/-- **`f5_density_upper` (upper half of the sandwich).**

The natural density of `{σ≤5}` is bounded above by `p/q` for every rational
`p/q > 7/8` (i.e. `7*q < 8*p`).  Concretely `density_bounded {σ≤5} p q`.
The four bad classes `{7,15,27,31} (mod 32)` together remove `4/32 = 1/8`, leaving
`{σ≤5}` with density `28/32 = 7/8`. -/
theorem f5_density_upper (p q : Nat) (hpq : 7 * q < 8 * p) :
    density_bounded (fun n => DescBy n 5) p q := by
  refine ⟨256 * q + 256, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 5) N with hA
  set B := count_upto Bad32 N with hB
  have hup : A + B ≤ N + 1 := countUpper5 N
  have hbl : 4 * (N + 1) ≤ 32 * B + 124 := bad32_lower N
  -- `32A ≤ 32(N+1) − 32B ≤ 32(N+1) − (4(N+1) − 124) = 28(N+1) + 124`.
  have h32A : 32 * A ≤ 28 * (N + 1) + 124 := by omega
  have hkey : q * A ≤ p * N := by nlinarith [h32A, hpq, hN]
  simpa [hA] using hkey

/-- **`f5_density_lower` (lower half of the sandwich) — the "almost all descend"
direction at level 5.**

The natural density of `{σ≤5}` is bounded below by `p/q` for every rational
`p/q < 7/8` (i.e. `8*p < 7*q`).  Concretely `density_bounded_below {σ≤5} p q`. -/
theorem f5_density_lower (p q : Nat) (hpq : 8 * p < 7 * q) :
    density_bounded_below (fun n => DescBy n 5) p q := by
  refine ⟨256 * q + 256, fun N hN => ?_⟩
  set A := count_upto (fun n => DescBy n 5) N with hA
  set B := count_upto Bad32 N with hB
  have hlo : (N + 1) ≤ A + B + 2 := countLower5 N
  have hbu : 32 * B ≤ 4 * (N + 1) + 128 := bad32_upper N
  -- `32A ≥ 32(N+1) − 32B − 64 ≥ 32(N+1) − (4(N+1)+128) − 64 = 28(N+1) − 192 ≥ 28N − 192`.
  have h32A : 28 * N ≤ 32 * A + 192 := by omega
  have hkey : p * N ≤ q * A := by nlinarith [h32A, hpq, hN]
  simpa [hA] using hkey

/-! ## §7  Level 6 — `F(6) = 7/8` (no integer has stopping time exactly 6)

The enumeration shows that **no** mod-64 refinement of a `Bad32` survivor drops
at the sixth step: all eight survivors mod 64 (`{7,15,27,31,39,47,59,63}`) are
the two lifts of each of the four survivors mod 32.  Structurally this means a
`Bad32` number does not descend on the sixth step either, so `DescBy 6 = DescBy 5`
pointwise and `F(6) = F(5) = 7/8` — exactly analogous to
`CollatzStoppingF3.desc_three_iff_two` (`F(3) = F(2)`).

We first extend the non-descent to a sixth step (`nondesc6_of_bad32`), then read
off `descBy6_iff_descBy5`. -/

/-- Iterate unfolding: `T_iter n 6 = T (T (T (T (T (T n)))))`. -/
theorem T_iter_six (n : Nat) : T_iter n 6 = T (T (T (T (T (T n))))) := rfl

/-- One Terras step on an *explicit* value `v`, returning a lower bound that holds
for **either** parity of `v`: `T v ≥ v / 2` (since the odd branch `(3v+1)/2 ≥ v/2`
and the even branch `v/2 = v/2`).  Used for the sixth step, whose parity is not
determined by `n mod 32` (only by `n mod 64`). -/
private theorem T_ge_half (v : Nat) : v / 2 ≤ T v := by
  unfold T
  by_cases hv : v % 2 = 0
  · rw [if_pos hv]
  · rw [if_neg (by omega)]; omega

/-- Sixth-step non-descent for `n ≡ 7 (mod 32)`.  With `n = 32q+7` the first five
iterates are the *explicit linear* values `48q+11, …, 81q+20`.  The sixth parity
is `n mod 64`-dependent, so we bound the sixth iterate below by `(81q+20)/2 ≥ 40q`
using `T_ge_half`, and `40q ≥ 32q+7` fails only for small `q`; we instead use the
exact `(81q+20)/2 ≥ 32q+7` for `q ≥ 1` and check `q = 0` directly. -/
private theorem nondesc6_eq7 (n : Nat) (h : n % 32 = 7) :
    n ≤ T (T (T (T (T (T n))))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 7 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 7) = 48 * q + 11 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 11) = 72 * q + 17 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 17) = 108 * q + 26 := by rw [T_step_odd _ (by omega)]; omega
  have e4 : T (108 * q + 26) = 54 * q + 13 := by rw [T_step_even _ (by omega)]; omega
  have e5 : T (54 * q + 13) = 81 * q + 20 := by rw [T_step_odd _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]
  have h6 := T_ge_half (81 * q + 20)
  omega

/-- Sixth-step non-descent for `n ≡ 15 (mod 32)` (`n = 32q+15`; fifth iterate
`81q+40`, then `T ≥ (81q+40)/2 ≥ 32q+15`). -/
private theorem nondesc6_eq15 (n : Nat) (h : n % 32 = 15) :
    n ≤ T (T (T (T (T (T n))))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 15 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 15) = 48 * q + 23 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 23) = 72 * q + 35 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 35) = 108 * q + 53 := by rw [T_step_odd _ (by omega)]; omega
  have e4 : T (108 * q + 53) = 162 * q + 80 := by rw [T_step_odd _ (by omega)]; omega
  have e5 : T (162 * q + 80) = 81 * q + 40 := by rw [T_step_even _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]
  have h6 := T_ge_half (81 * q + 40)
  omega

/-- Sixth-step non-descent for `n ≡ 27 (mod 32)` (`n = 32q+27`; fifth iterate
`81q+71`, then `T ≥ (81q+71)/2 ≥ 32q+27`). -/
private theorem nondesc6_eq27 (n : Nat) (h : n % 32 = 27) :
    n ≤ T (T (T (T (T (T n))))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 27 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 27) = 48 * q + 41 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 41) = 72 * q + 62 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 62) = 36 * q + 31 := by rw [T_step_even _ (by omega)]; omega
  have e4 : T (36 * q + 31) = 54 * q + 47 := by rw [T_step_odd _ (by omega)]; omega
  have e5 : T (54 * q + 47) = 81 * q + 71 := by rw [T_step_odd _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]
  have h6 := T_ge_half (81 * q + 71)
  omega

/-- Sixth-step non-descent for `n ≡ 31 (mod 32)` (`n = 32q+31`; fifth iterate
`243q+242`, then `T ≥ (243q+242)/2 ≥ 32q+31`). -/
private theorem nondesc6_eq31 (n : Nat) (h : n % 32 = 31) :
    n ≤ T (T (T (T (T (T n))))) := by
  obtain ⟨q, hq⟩ : ∃ q, n = 32 * q + 31 := ⟨n / 32, by omega⟩
  subst hq
  have e1 : T (32 * q + 31) = 48 * q + 47 := by rw [T_step_odd _ (by omega)]; omega
  have e2 : T (48 * q + 47) = 72 * q + 71 := by rw [T_step_odd _ (by omega)]; omega
  have e3 : T (72 * q + 71) = 108 * q + 107 := by rw [T_step_odd _ (by omega)]; omega
  have e4 : T (108 * q + 107) = 162 * q + 161 := by rw [T_step_odd _ (by omega)]; omega
  have e5 : T (162 * q + 161) = 243 * q + 242 := by rw [T_step_odd _ (by omega)]; omega
  rw [e1, e2, e3, e4, e5]
  have h6 := T_ge_half (243 * q + 242)
  omega

/-- **Non-descent at the sixth step for `Bad32`.**  A `Bad32` number's sixth
iterate is also `≥ n` (no `Bad32` class drops at step 6).  We dispatch each of
the four concrete survivor residues to its straight-line walker, so every branch
carries a *fixed* residue with determined parities — keeping memory bounded
(no `2^5`-way `by_cases` tree). -/
theorem nondesc6_of_bad32 (n : Nat) (h : Bad32 n) : n ≤ T_iter n 6 := by
  rw [T_iter_six]
  rcases h with h | h | h | h
  · exact nondesc6_eq7 n h
  · exact nondesc6_eq15 n h
  · exact nondesc6_eq27 n h
  · exact nondesc6_eq31 n h

/-- **`not_bad32_of_descBy6`** : a `Bad32` number is not in `{σ ≤ 6}`.
Combines `nondesc5_of_bad32` (steps 1–5) with `nondesc6_of_bad32` (step 6). -/
theorem not_bad32_of_descBy6 (n : Nat) (h : DescBy n 6) : ¬ Bad32 n := by
  intro hbad
  obtain ⟨j, hj1, hj6, hlt⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := nondesc5_of_bad32 n hbad
  have h6 := nondesc6_of_bad32 n hbad
  interval_cases j
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)
  · exact absurd hlt (by omega)

/-- **`descBy6_iff_descBy5` — no integer has stopping time exactly 6.**

For every `n`, `DescBy n 6 ↔ DescBy n 5`.  The `←` direction is `desc_by_mono`;
for `→`, a number with `DescBy n 6` is not `Bad32` (by `not_bad32_of_descBy6`),
hence (for `n ≥ 2`) `DescBy n 5` by `descBy5_of_not_bad32`; the cases `n ∈ {0,1}`
have no descent at all, so the implication is vacuous there. -/
theorem descBy6_iff_descBy5 (n : Nat) : DescBy n 6 ↔ DescBy n 5 := by
  constructor
  · intro h6
    by_cases hn : 2 ≤ n
    · exact descBy5_of_not_bad32 n hn (not_bad32_of_descBy6 n h6)
    · -- n ∈ {0,1}: no step can drop strictly below n, so `DescBy n 6` is impossible.
      exfalso
      obtain ⟨j, hj1, hj6, hlt⟩ := h6
      interval_cases n
      · exact absurd hlt (Nat.not_lt_zero _)
      · -- n = 1: the orbit of 1 is 1 → 2 → 1 → 2 → … and never drops below 1.
        interval_cases j <;> simp [T_iter, T] at hlt
  · exact desc_by_mono n 5

/-- **`descBy6_iff_good32`.** For `n ≥ 2`, the level-6 descending set is the same
as the level-5 one: the complement of `{7,15,27,31} (mod 32)`. -/
theorem descBy6_iff_good32 (n : Nat) (hn : 2 ≤ n) :
    DescBy n 6 ↔ ¬ Bad32 n :=
  (descBy6_iff_descBy5 n).trans (descBy5_iff_good32 n hn)

/-! ### §7a  `F(6) = 7/8` density sandwich (same value as `F(5)`) -/

/-- **`f6_density_upper` — `F(6) ≤ 7/8`.**  Since `DescBy 6 = DescBy 5`
pointwise, the level-6 count equals the level-5 count, so the same bound holds. -/
theorem f6_density_upper (p q : Nat) (hpq : 7 * q < 8 * p) :
    density_bounded (fun n => DescBy n 6) p q := by
  obtain ⟨N₀, h⟩ := f5_density_upper p q hpq
  refine ⟨N₀, fun N hN => ?_⟩
  have heq : count_upto (fun n => DescBy n 6) N = count_upto (fun n => DescBy n 5) N :=
    le_antisymm
      (count_upto_mono _ _ (fun j _ hj => (descBy6_iff_descBy5 j).mp hj))
      (count_upto_mono _ _ (fun j _ hj => (descBy6_iff_descBy5 j).mpr hj))
  rw [heq]; exact h N hN

/-- **`f6_density_lower` — `F(6) ≥ 7/8`.** -/
theorem f6_density_lower (p q : Nat) (hpq : 8 * p < 7 * q) :
    density_bounded_below (fun n => DescBy n 6) p q := by
  obtain ⟨N₀, h⟩ := f5_density_lower p q hpq
  refine ⟨N₀, fun N hN => ?_⟩
  have heq : count_upto (fun n => DescBy n 6) N = count_upto (fun n => DescBy n 5) N :=
    le_antisymm
      (count_upto_mono _ _ (fun j _ hj => (descBy6_iff_descBy5 j).mp hj))
      (count_upto_mono _ _ (fun j _ hj => (descBy6_iff_descBy5 j).mpr hj))
  rw [heq]; exact h N hN

/-! ## §8  Monotonicity and the strict gain `F(4) < F(5)` -/

/-- **`f4_le_f5` — monotonicity (item 3).**  At every cutoff `N`, the count of
`{σ≤4}` is `≤` the count of `{σ≤5}` (from `{σ≤4} ⊆ {σ≤5}`).  Hence `F(4) ≤ F(5)`. -/
theorem f4_le_f5 (N : Nat) :
    count_upto (fun n => DescBy n 4) N ≤ count_upto (fun n => DescBy n 5) N :=
  count_upto_mono _ _ (fun k _ hk => desc_by_mono k 4 hk)

/-- **`f5_le_f6` — monotonicity (item 3).**  `{σ≤5} ⊆ {σ≤6}`, hence
`F(5) ≤ F(6)` (here in fact an equality, since `F(5) = F(6) = 7/8`). -/
theorem f5_le_f6 (N : Nat) :
    count_upto (fun n => DescBy n 5) N ≤ count_upto (fun n => DescBy n 6) N :=
  count_upto_mono _ _ (fun k _ hk => desc_by_mono k 5 hk)

/-- **`desc5_newly_drops` — the strict gain at level 5.**

The residue class `n ≡ 11 (mod 32)` is in `{σ≤5}` but **not** in `{σ≤4}`: it is
one of the two classes (`{11,23} mod 32`) that newly drop at the fifth step.
(For `n = 32q+11`, descent happens exactly at the fifth step.)  This witnesses
`F(5) > F(4) = 13/16`. -/
theorem desc5_newly_drops (n : Nat) (h : n % 32 = 11) :
    DescBy n 5 ∧ ¬ DescBy n 4 := by
  refine ⟨⟨5, by omega, by omega, desc5_of_mod32_eq11 n h⟩, ?_⟩
  intro h4
  -- `n ≡ 11 (mod 32) ⇒ n % 16 = 11 ⇒ Bad16 n`, but `DescBy n 4 → ¬ Bad16 n`.
  exact (not_bad16_of_descBy4 n h4) (by unfold Bad16; omega)

/-- **`f4_lt_f5` (item 3) — the ladder strictly tightens between 4 and 5.**

There is a rational gap `27/32 < 7/8 = 28/32` separating `F(4)` from `F(5)`:
`F(4) ≤ 27/32 < 28/32 ≤ F(5)`, since `27/32 > 13/16 = 26/32` and
`27/32 < 7/8 = 28/32`.  The pair (an upper bound on `F(4)` and a lower bound on
`F(5)` with `27 < 28`) witnesses `F(4) < F(5)`. -/
theorem f4_lt_f5 :
    density_bounded (fun n => DescBy n 4) 27 32
      ∧ density_bounded_below (fun n => DescBy n 5) 27 32
      ∧ (26 : Nat) < 27 :=
  ⟨f4_density_upper 27 32 (by norm_num),
   f5_density_lower 27 32 (by norm_num),
   by norm_num⟩

/-! ## §9  The bad-residue LIFTING structure — toward `b(k) → 0`

This is the genuinely new structural content.  We record the **projection /
lifting** law for survivors and make the gap to `b(k) → 0` precise.

Recall `CollatzBadDensity.Bad k n := ¬ DescBy n k` ("`σ(n) > k`") and
`CollatzBadDensity.bad_antitone : Bad (k+1) n → Bad k n`.  The survivor residues
mod `2^k` are exactly the residues of `Bad k`; the lifting law below says they
nest. -/

/-- **`survivor_lift` (item 4).**  Every survivor mod `2^(k+1)` projects, mod
`2^k`, onto a survivor mod `2^k`.

Concretely, if `Bad (k+1) n` then `Bad k n`: a number that has not descended
within `k+1` steps has not descended within `k` steps.  At the residue level this
says the surviving residues mod `2^(k+1)` reduce mod `2^k` to surviving residues
mod `2^k` — equivalently `r ↦ r % 2^k` maps `{survivors mod 2^(k+1)}` into
`{survivors mod 2^k}`.  (This is `CollatzBadDensity.bad_antitone`, restated as the
lifting/projection law.) -/
theorem survivor_lift (k n : Nat) (h : CollatzBadDensity.Bad (k + 1) n) :
    CollatzBadDensity.Bad k n :=
  CollatzBadDensity.bad_antitone k n h

/-- **`survivor_lift_two` — at most two lifts.**  A residue `r < 2^k` has exactly
two preimages under `· % 2^k` in `[0, 2^(k+1))`, namely `r` and `r + 2^k`.  Hence
each survivor mod `2^k` has **at most two** survivor lifts mod `2^(k+1)`, giving
the *a priori* bound `β(k+1) ≤ 2·β(k)`.

We state the combinatorial fact: any `m < 2^(k+1)` with `m % 2^k = r` is one of
`{r, r + 2^k}`. -/
theorem survivor_lift_two (k r m : Nat) (hr : r < 2 ^ k)
    (hm : m < 2 ^ (k + 1)) (hmr : m % 2 ^ k = r) :
    m = r ∨ m = r + 2 ^ k := by
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  have hdm : 2 ^ k * (m / 2 ^ k) + m % 2 ^ k = m := Nat.div_add_mod m (2 ^ k)
  rw [hmr] at hdm
  -- `m / 2^k < 2`, so it is `0` or `1`.
  have hquot : m / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hpos]; omega
  interval_cases (m / 2 ^ k) <;> omega

/-! ### §9a  The precise gap to `b(k) → 0`

What is proved here:

* **`survivor_lift`** — survivors nest: `Bad (k+1) ⊆ Bad k`, i.e. the bad
  residues mod `2^(k+1)` project onto bad residues mod `2^k`.
* **`survivor_lift_two`** — each bad residue mod `2^k` has at most two lifts mod
  `2^(k+1)`, so `β(k+1) ≤ 2·β(k)`.

This alone gives only `b(k) ≤ b(k-1)` (weakly decreasing, already in
`CollatzBadDensity.bad_count_antitone`).  To obtain `b(k) → 0` ("almost all
integers descend") one needs a **strict contraction**

  `β(k+1) ≤ c · β(k)`   with a constant `c < 2`,

i.e. *on average fewer than two of the two lifts of each survivor survive*.  The
enumerated data show this is true but **non-uniform per step**: the per-step lift
ratios `β(k+1)/β(k)` for `k = 1,…,5` are

  `1, 2, 3/2, 4/3, 2`

— each `≤ 2`, none uniformly `< 2`.  The Terras/Everett theorem packages the
*average* contraction across blocks of steps: the parity-vector map
`r ↦ (Q_k(r) mod 2^k)` of Terras (`TerrasDensity.PVEq`) is a bijection of
`ℤ/2^k`, and the "no descent in `k` steps" fibre is governed by a random-walk /
large-deviation estimate forcing the *fraction* `β(k)/2^k → 0`.  Formalising that
average contraction (equivalently, that the surviving parity vectors are those
whose partial sums of `log 3 − log 2` stay positive, a set of exponentially small
measure) is the remaining open input.  The two lemmas above are the exact
finite-level skeleton on which that estimate would sit.

This file therefore delivers the **finite ladder** `F(5) = F(6) = 7/8` with full
residue characterizations, the monotonicity and strict gain `F(4) < F(5)`, and
the **lifting/projection structure**; the average-contraction `c < 2` is stated
as the precise remaining gap. -/

end CollatzStoppingF56
