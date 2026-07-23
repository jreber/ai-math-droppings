import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.ResidueDescent
import Propositio.NumberTheory.Collatz.StoppingF3
import Propositio.NumberTheory.Collatz.StoppingF4
import Propositio.NumberTheory.Collatz.StoppingF56
import Propositio.NumberTheory.Collatz.DensityCount
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

/-!
# Collatz density bound: 28/32 residue classes mod 32 have guaranteed Terras descent

This file formalises the mod-32 bounded-descent census for the Terras half-step map
`T` (= `n/2` on evens, `(3n+1)/2` on odds):

  **28 out of 32 residue classes mod 32 have guaranteed bounded descent within
  at most 5 Terras steps.**

The 28 "good" classes are:
* **Even** (16 classes): T(n) = n/2 < n for n ≥ 2.
* **n ≡ 1 (mod 4) odd** (8 classes): T²(n) < n for n ≥ 2.
* **n ≡ 3 (mod 16)**: {3, 19} mod 32 (2 classes): T⁴(n) < n
  (`CollatzResidueDescent.descent_three_mod_sixteen`).
* **n ≡ 11 (mod 32)**: 1 class, T⁵(n) < n
  (`CollatzResidueDescent.descent_eleven_mod_thirtytwo`).
* **n ≡ 23 (mod 32)**: 1 class, T⁵(n) < n
  (`CollatzStoppingF56.desc5_of_mod32_eq23`).

The 4 "bad" classes (no descent within 5 steps) are {7, 15, 27, 31} mod 32,
which is precisely `CollatzStoppingF56.Bad32`.

## What is proved (all axiom-clean)

* `good_mod32` — the decidable predicate identifying the 28 good residues.
* `good_mod32_count` — exactly 28 residues mod 32 are good (by `decide`).
* `bad_mod32_count` — exactly 4 residues mod 32 are bad (by `decide`).
* `good_mod32_descent` — every `n ≥ 2` with a good residue descends within ≤ 5 steps.
* `descent_density_mod32` — the headline 28/32 density statement using `D 5 = 28`.

## Connection to the existing density ladder

`CollatzDensityCount.D_five` already establishes `D 5 = 28` (by `decide`), which
pins `F(5) = 28/32 = 7/8`.  This file provides the *per-residue witness* layer:
explicit descent proofs for each of the 28 good classes, packaging them in the
`good_mod32_descent` theorem.  Together with `descBy5_iff_good32` from
`CollatzStoppingF56`, this file bridges the residue census to the density bound.

## Axiom hygiene

Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzDensityMod32

open TerrasDensity
open CollatzStoppingF3
open CollatzStoppingF4
open CollatzStoppingF56
open CollatzResidueDescent
open CollatzDensityCount

attribute [local instance] Classical.propDecidable

/-! ## §1  The "good" predicate and the finite count -/

/-- `good_mod32 r` holds iff residue `r` mod 32 has guaranteed Terras descent:
  either even, ≡ 1 (mod 4), ≡ 3 (mod 16), ≡ 11 (mod 32), or ≡ 23 (mod 32). -/
def good_mod32 (r : Fin 32) : Prop :=
  r.val % 2 = 0 ∨ r.val % 4 = 1 ∨ r.val % 16 = 3 ∨ r.val = 11 ∨ r.val = 23

/-- `good_mod32` is decidable (all conditions are decidable). -/
instance : DecidablePred good_mod32 := fun r => by
  unfold good_mod32; exact instDecidableOr

/-- **Exactly 28 residues mod 32 are good.** By `decide`: the kernel evaluates
  `Finset.filter good_mod32 Finset.univ` and counts 28 elements. -/
theorem good_mod32_count :
    (Finset.univ.filter good_mod32).card = 28 := by decide

/-- **Exactly 4 residues mod 32 are bad** (= 32 - 28).
  The bad residues are {7, 15, 27, 31} mod 32, matching `Bad32`. -/
theorem bad_mod32_count :
    (Finset.univ.filter (fun r : Fin 32 => ¬ good_mod32 r)).card = 4 := by decide

/-- The bad residues are exactly `{7, 15, 27, 31}` mod 32. -/
theorem bad_mod32_eq :
    Finset.univ.filter (fun r : Fin 32 => ¬ good_mod32 r) =
    {⟨7, by omega⟩, ⟨15, by omega⟩, ⟨27, by omega⟩, ⟨31, by omega⟩} := by decide

/-! ## §2  Even descent: T(n) = n/2 < n for even n ≥ 2 -/

/-- For `n ≥ 2` even, `T_iter n 1 = n / 2 < n` — descent in one step. -/
private theorem even_descent_one_step {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) :
    T_iter n 1 < n := by
  have : T n = n / 2 := by unfold T; rw [if_pos he]
  simp only [T_iter, this]
  exact Nat.div_lt_self (by omega) (by norm_num)

/-! ## §3  1-mod-4 odd descent: T²(n) < n for n ≡ 1 (mod 4), n ≥ 2 -/

/-- For `n ≥ 2` with `n % 4 = 1`, `T_iter n 2 < n` — descent in two steps. -/
private theorem mod4_one_descent_two_steps {n : ℕ} (hn : 2 ≤ n) (h : n % 4 = 1) :
    T_iter n 2 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
  have hk : k ≠ 0 := by omega
  have hT1 : T (4 * k + 1) = 6 * k + 2 := by unfold T; split <;> omega
  have hT2 : T (6 * k + 2) = 3 * k + 1 := by unfold T; split <;> omega
  have e : T_iter (4 * k + 1) 2 = T (T (4 * k + 1)) := rfl
  rw [e, hT1, hT2]; omega

/-! ## §4  The main per-residue descent theorem -/

/-- **Core descent: every `n ≥ 2` with a good mod-32 residue descends within ≤ 5 steps.**

We case-split on the five disjuncts of `good_mod32 r` and dispatch to the
appropriate existing lemma:
- Even → even_descent_one_step (k=1)
- ≡ 1 mod 4 → mod4_one_descent_two_steps (k=2)
- ≡ 3 mod 16 → descent_three_mod_sixteen (k=4)
- = 11 mod 32 → descent_eleven_mod_thirtytwo (k=5)
- = 23 mod 32 → desc5_of_mod32_eq23 (k=5)
-/
theorem good_mod32_descent (r : Fin 32) (hr : good_mod32 r) (n : ℕ)
    (hn : 2 ≤ n) (hmod : n % 32 = r.val) :
    ∃ k, 1 ≤ k ∧ k ≤ 5 ∧ T_iter n k < n := by
  rcases hr with heven | hmod4 | hmod16 | heq11 | heq23
  · -- n is even
    have he : n % 2 = 0 := by omega
    exact ⟨1, by omega, by omega, even_descent_one_step hn he⟩
  · -- n ≡ 1 mod 4
    have h4 : n % 4 = 1 := by omega
    exact ⟨2, by omega, by omega, mod4_one_descent_two_steps hn h4⟩
  · -- n ≡ 3 mod 16
    have h16 : n % 16 = 3 := by omega
    exact ⟨4, by omega, by omega, descent_three_mod_sixteen h16⟩
  · -- r.val = 11, so n ≡ 11 mod 32
    have h32 : n % 32 = 11 := by omega
    exact ⟨5, by omega, by omega, descent_eleven_mod_thirtytwo h32⟩
  · -- r.val = 23, so n ≡ 23 mod 32
    have h32 : n % 32 = 23 := by omega
    exact ⟨5, by omega, by omega, desc5_of_mod32_eq23 n h32⟩

/-! ## §5  Cardinality complementarity -/

/-- Good and bad residues partition all 32 classes. -/
theorem good_bad_partition :
    (Finset.univ.filter good_mod32).card +
    (Finset.univ.filter (fun r : Fin 32 => ¬ good_mod32 r)).card = 32 := by
  rw [good_mod32_count, bad_mod32_count]

/-- The density of good residues is exactly 28/32. -/
theorem good_fraction_28_of_32 :
    (Finset.univ.filter good_mod32).card * 32 =
    28 * (Finset.univ : Finset (Fin 32)).card := by
  simp [good_mod32_count]

/-! ## §6  Connection to the D(5)=28 density count -/

/-- **Density headline.** The descending-residue count at level 5 is 28.
  This is `CollatzDensityCount.D_five`, restated as the mod-32 connection. -/
theorem descent_density_mod32 : D 5 = 28 := D_five

/-- **Headline lower bound.** The natural density of `{ n : DescBy n 5 }` is ≥ 7/8.
  Proof: `D 5 = 28` and `F_eq_count_over_pow` pin the density from below. -/
theorem descent_density_at_least_7_8 (p q : ℕ) (hpq : 8 * p < 7 * q) :
    density_bounded_below (fun n => DescBy n 5) p q :=
  (F_eq_count_over_pow 5 (by omega) (by omega) p q).2 (by
    rw [D_five]; norm_num; linarith)

/-- **Headline upper bound.** Combined with the lower bound, this pins the density
  of `{ n : DescBy n 5 }` at exactly 7/8. -/
theorem descent_density_at_most_7_8 (p q : ℕ) (hpq : 7 * q < 8 * p) :
    density_bounded (fun n => DescBy n 5) p q :=
  (F_eq_count_over_pow 5 (by omega) (by omega) p q).1 (by
    rw [D_five]; norm_num; linarith)

/-! ## §7  Residue characterization of the 28 good classes -/

/-- **Good residues are exactly the non-Bad32 residues.**
  Proved by exhaustive `fin_cases` over `Fin 32` then `decide` per case. -/
theorem good_mod32_iff_not_bad32 (r : Fin 32) :
    good_mod32 r ↔
    ¬ (r.val = 7 ∨ r.val = 15 ∨ r.val = 27 ∨ r.val = 31) := by
  fin_cases r <;> simp (config := { decide := true })

/-- **`DescBy n 5 → good residue class** (for `n ≥ 2`).
  If `n` descends within 5 Terras steps, its mod-32 class is good. -/
theorem descBy5_imp_good_mod32 (n : ℕ) (h : DescBy n 5) :
    good_mod32 ⟨n % 32, Nat.mod_lt n (by omega)⟩ := by
  rw [good_mod32_iff_not_bad32]
  intro hbad
  have hb32 : Bad32 n := by
    unfold Bad32; omega
  exact not_bad32_of_descBy5 n h hb32

/-- **`good residue → DescBy n 5`** (for `n ≥ 2`).
  A good residue class implies 5-step descent. -/
theorem good_mod32_imp_descBy5 (n : ℕ) (hn : 2 ≤ n)
    (hg : good_mod32 ⟨n % 32, Nat.mod_lt n (by omega)⟩) :
    DescBy n 5 := by
  rw [good_mod32_iff_not_bad32] at hg
  apply descBy5_of_not_bad32 n hn
  unfold Bad32; omega

/-- **Biconditional at level 5.** For `n ≥ 2`:
    `DescBy n 5 ↔ good_mod32 ⟨n % 32, _⟩`. -/
theorem descBy5_iff_good_mod32 (n : ℕ) (hn : 2 ≤ n) :
    DescBy n 5 ↔ good_mod32 ⟨n % 32, Nat.mod_lt n (by omega)⟩ :=
  ⟨descBy5_imp_good_mod32 n, good_mod32_imp_descBy5 n hn⟩

#check @good_mod32_count
#check @good_mod32_descent
#check @descent_density_mod32
#check @descent_density_at_least_7_8
#check @descBy5_iff_good_mod32

end CollatzDensityMod32
