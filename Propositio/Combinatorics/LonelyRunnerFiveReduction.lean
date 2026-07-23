/-
# Lonely Runner `k = 5`: the `{2·, 3·, 5·}`-residual reduction (first step)

This file proves the **first reduction step** for the `k = 5` Lonely Runner Conjecture
(four pairwise-distinct nonzero integer relative speeds, target bound `1/5`), mirroring
`LonelyRunnerCoprimeKernel`'s successful `k = 4` pattern exactly, but with **three** primes
instead of two.

## What is proved here

For each prime `p ∈ {2, 3, 5}`, a fixed time `t = 1/p` gives nearest-integer distance
`≥ 1/5` to *any* speed `v` that is **not** a multiple of `p` (the residue `r = v mod p`
is nonzero, hence lands in the band that is `≥ 1/5` away from an integer at time `1/p`):

* **`nid_half_time`** — `¬ (2 ∣ v) → 1/5 ≤ nid (v · (1/2))`. (In fact `nid = 1/2`.)
* **`nid_third_time`** — `¬ (3 ∣ v) → 1/5 ≤ nid (v · (1/3))`. (In fact `nid = 1/3`.)
* **`nid_fifth_time`** — `¬ (5 ∣ v) → 1/5 ≤ nid (v · (1/5))`. (`nid ∈ {1/5, 2/5}`; the
  residues `r = 1, 4` are *exactly* `1/5`, tight, matching the hand-verified claim.)

Consequently `t = 1/2` solves any quadruple with **no** multiple of `2`; `t = 1/3` solves
any quadruple with **no** multiple of `3`; `t = 1/5` solves any quadruple with **no**
multiple of `5`.  Hence:

* **`FiveResidual`** — the thin residual `Prop`: quadruples that contain a multiple of `2`,
  a multiple of `3`, **and** a multiple of `5` (possibly the same speed, possibly different
  speeds).  This is the direct `k = 5` analogue of `LonelyRunnerCoprimeKernel.FourThreeResidual`.

* **`fiveKernel_of_residual`** — if the `1/5`-bound holds for every pairwise-distinct
  positive quadruple in the residual `FiveResidual`, then it holds for **all** pairwise-distinct
  positive quadruples.  The proof is a three-way case split (mirroring
  `coprimeKernel_of_residual`'s two-way split): quadruples missing a multiple of `2`, `3`, or
  `5` are each discharged unconditionally by the corresponding fixed-time witness above; only
  the residual needs `H`.

This reduction is honest: `FiveResidual` remains **open** and is stated as an explicit
hypothesis — it is *not* attempted here (the genuinely hard part, out of scope for this
dispatch).  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Propositio.Combinatorics.LonelyRunnerSmallK

namespace LonelyRunnerFiveReduction

open LonelyRunnerSmallK

/-- **Reusable `1/5` residue bound.** Nearest-integer distance of a rational `m / n` is
`≥ 1/5` whenever its residue `r = m mod n` lies in the middle band `[n/5, 4·n/5]`, i.e.
`n ≤ 5·r` and `5·r ≤ 4·n`.  This is the `1/5` analogue of
`LonelyRunnerCoprimeKernel.nid_ge_quarter_of_residue`, general in the modulus `n` (unlike
that lemma, which fixes `n = 4`) since here the target bound `1/5` is fixed by `k = 5` while
the modulus ranges over the primes `2, 3, 5`. -/
lemma nid_ge_fifth_of_residue (m : ℤ) (n : ℕ) (hn : 0 < n) (r : ℤ)
    (hr : m % (n : ℤ) = r) (h1 : (n : ℝ) ≤ 5 * (r : ℝ)) (h2 : 5 * (r : ℝ) ≤ 4 * (n : ℝ)) :
    (1 : ℝ) / 5 ≤ nid ((m : ℝ) / (n : ℝ)) := by
  rw [nid_eq, Int.fract_div_intCast_eq_div_intCast_mod, hr]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (1 : ℝ) / 5 ≤ (r : ℝ) / n := by
    rw [le_div_iff₀ hn']; linarith
  have e2 : (r : ℝ) / n ≤ 4 / 5 := by
    rw [div_le_iff₀ hn']; linarith
  exact le_min e1 (by linarith)

/-- **`t = 1/2` witness.** If `v` is not a multiple of `2`, then at time `t = 1/2` the runner
of speed `v` is at nearest-integer distance `≥ 1/5` (in fact `= 1/2`). -/
lemma nid_half_time (v : ℕ) (hv : ¬ (2 ∣ v)) :
    (1 : ℝ) / 5 ≤ nid ((v : ℝ) * (1 / 2)) := by
  have h0 : 0 ≤ (v : ℤ) % 2 := Int.emod_nonneg _ (by norm_num)
  have h2 : (v : ℤ) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hne : (v : ℤ) % 2 ≠ 0 := by
    intro h
    apply hv
    have hd : (2 : ℤ) ∣ (v : ℤ) := Int.dvd_of_emod_eq_zero h
    exact_mod_cast hd
  set r : ℤ := (v : ℤ) % 2 with hrdef
  have hr1 : (1 : ℤ) ≤ r := by omega
  have hr1' : r ≤ (1 : ℤ) := by omega
  have hcast : (v : ℝ) * (1 / 2) = ((v : ℤ) : ℝ) / ((2 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  refine nid_ge_fifth_of_residue (v : ℤ) 2 (by norm_num) r hrdef.symm ?_ ?_
  · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    push_cast; linarith
  · have : (r : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hr1'
    push_cast; linarith

/-- **`t = 1/3` witness.** If `v` is not a multiple of `3`, then at time `t = 1/3` the runner
of speed `v` is at nearest-integer distance `≥ 1/5` (in fact `= 1/3`). -/
lemma nid_third_time (v : ℕ) (hv : ¬ (3 ∣ v)) :
    (1 : ℝ) / 5 ≤ nid ((v : ℝ) * (1 / 3)) := by
  have h0 : 0 ≤ (v : ℤ) % 3 := Int.emod_nonneg _ (by norm_num)
  have h3 : (v : ℤ) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hne : (v : ℤ) % 3 ≠ 0 := by
    intro h
    apply hv
    have hd : (3 : ℤ) ∣ (v : ℤ) := Int.dvd_of_emod_eq_zero h
    exact_mod_cast hd
  set r : ℤ := (v : ℤ) % 3 with hrdef
  have hr1 : (1 : ℤ) ≤ r := by omega
  have hr2 : r ≤ (2 : ℤ) := by omega
  have hcast : (v : ℝ) * (1 / 3) = ((v : ℤ) : ℝ) / ((3 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  refine nid_ge_fifth_of_residue (v : ℤ) 3 (by norm_num) r hrdef.symm ?_ ?_
  · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    push_cast; linarith
  · have : (r : ℝ) ≤ (2 : ℝ) := by exact_mod_cast hr2
    push_cast; linarith

/-- **`t = 1/5` witness.** If `v` is not a multiple of `5`, then at time `t = 1/5` the runner
of speed `v` is at nearest-integer distance `≥ 1/5`.  The residues `r = 1, 4` give exactly
`nid = 1/5` (tight, not slack); `r = 2, 3` give `nid = 2/5`. -/
lemma nid_fifth_time (v : ℕ) (hv : ¬ (5 ∣ v)) :
    (1 : ℝ) / 5 ≤ nid ((v : ℝ) * (1 / 5)) := by
  have h0 : 0 ≤ (v : ℤ) % 5 := Int.emod_nonneg _ (by norm_num)
  have h5 : (v : ℤ) % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  have hne : (v : ℤ) % 5 ≠ 0 := by
    intro h
    apply hv
    have hd : (5 : ℤ) ∣ (v : ℤ) := Int.dvd_of_emod_eq_zero h
    exact_mod_cast hd
  set r : ℤ := (v : ℤ) % 5 with hrdef
  have hr1 : (1 : ℤ) ≤ r := by omega
  have hr4 : r ≤ (4 : ℤ) := by omega
  have hcast : (v : ℝ) * (1 / 5) = ((v : ℤ) : ℝ) / ((5 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  refine nid_ge_fifth_of_residue (v : ℤ) 5 (by norm_num) r hrdef.symm ?_ ?_
  · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    push_cast; linarith
  · have : (r : ℝ) ≤ (4 : ℝ) := by exact_mod_cast hr4
    push_cast; linarith

/-- **No multiple of `2` ⇒ `t = 1/2` solves the quadruple.** Needs neither distinctness nor
any divisibility hypothesis on the other primes. -/
lemma kernel_of_no_two (v1 v2 v3 v4 : ℕ)
    (h1 : ¬ (2 ∣ v1)) (h2 : ¬ (2 ∣ v2)) (h3 : ¬ (2 ∣ v3)) (h4 : ¬ (2 ∣ v4)) :
    ∃ t : ℝ, (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v4 : ℝ) * t) :=
  ⟨1 / 2, nid_half_time v1 h1, nid_half_time v2 h2, nid_half_time v3 h3, nid_half_time v4 h4⟩

/-- **No multiple of `3` ⇒ `t = 1/3` solves the quadruple.** -/
lemma kernel_of_no_three (v1 v2 v3 v4 : ℕ)
    (h1 : ¬ (3 ∣ v1)) (h2 : ¬ (3 ∣ v2)) (h3 : ¬ (3 ∣ v3)) (h4 : ¬ (3 ∣ v4)) :
    ∃ t : ℝ, (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v4 : ℝ) * t) :=
  ⟨1 / 3, nid_third_time v1 h1, nid_third_time v2 h2, nid_third_time v3 h3, nid_third_time v4 h4⟩

/-- **No multiple of `5` ⇒ `t = 1/5` solves the quadruple.** -/
lemma kernel_of_no_five (v1 v2 v3 v4 : ℕ)
    (h1 : ¬ (5 ∣ v1)) (h2 : ¬ (5 ∣ v2)) (h3 : ¬ (5 ∣ v3)) (h4 : ¬ (5 ∣ v4)) :
    ∃ t : ℝ, (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v4 : ℝ) * t) :=
  ⟨1 / 5, nid_fifth_time v1 h1, nid_fifth_time v2 h2, nid_fifth_time v3 h3, nid_fifth_time v4 h4⟩

/-- The `{2·, 3·, 5·}`-**residual**: the `k = 5` bound restricted to pairwise-distinct
positive quadruples that contain **a** multiple of `2`, **a** multiple of `3`, and **a**
multiple of `5` (possibly the same speed satisfying more than one, possibly different
speeds).  This is the direct `k = 5` analogue of
`LonelyRunnerCoprimeKernel.FourThreeResidual`, with a third prime added.  It remains open
and is packaged here as a reusable hypothesis shape. -/
def FiveResidual : Prop :=
  ∀ v1 v2 v3 v4 : ℕ, 1 ≤ v1 → 1 ≤ v2 → 1 ≤ v3 → 1 ≤ v4 →
    v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v2 ≠ v3 → v2 ≠ v4 → v3 ≠ v4 →
    (2 ∣ v1 ∨ 2 ∣ v2 ∨ 2 ∣ v3 ∨ 2 ∣ v4) →
    (3 ∣ v1 ∨ 3 ∣ v2 ∨ 3 ∣ v3 ∨ 3 ∣ v4) →
    (5 ∣ v1 ∨ 5 ∣ v2 ∨ 5 ∣ v3 ∨ 5 ∣ v4) →
    ∃ t : ℝ, (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v4 : ℝ) * t)

/-- **Reduction of the `k = 5` bound to the `{2·, 3·, 5·}`-residual.** If the `1/5`-bound
holds for every pairwise-distinct positive quadruple that contains a multiple of `2`, a
multiple of `3`, and a multiple of `5`, then it holds for **all** pairwise-distinct positive
quadruples.

Quadruples with no multiple of `2` are solved unconditionally by `t = 1/2`; those with no
multiple of `3` (among the rest) by `t = 1/3`; those with no multiple of `5` (among the rest)
by `t = 1/5`; the only remaining quadruples are the residual, where `H` applies. -/
theorem fiveKernel_of_residual (H : FiveResidual) :
    ∀ v1 v2 v3 v4 : ℕ, 1 ≤ v1 → 1 ≤ v2 → 1 ≤ v3 → 1 ≤ v4 →
      v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v2 ≠ v3 → v2 ≠ v4 → v3 ≠ v4 →
      ∃ t : ℝ, (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * t) ∧
        (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v4 : ℝ) * t) := by
  intro v1 v2 v3 v4 h1 h2 h3 h4 h12 h13 h14 h23 h24 h34
  by_cases hd2 : 2 ∣ v1 ∨ 2 ∣ v2 ∨ 2 ∣ v3 ∨ 2 ∣ v4
  · by_cases hd3 : 3 ∣ v1 ∨ 3 ∣ v2 ∨ 3 ∣ v3 ∨ 3 ∣ v4
    · by_cases hd5 : 5 ∣ v1 ∨ 5 ∣ v2 ∨ 5 ∣ v3 ∨ 5 ∣ v4
      · exact H v1 v2 v3 v4 h1 h2 h3 h4 h12 h13 h14 h23 h24 h34 hd2 hd3 hd5
      · rw [not_or, not_or, not_or] at hd5
        exact kernel_of_no_five v1 v2 v3 v4 hd5.1 hd5.2.1 hd5.2.2.1 hd5.2.2.2
    · rw [not_or, not_or, not_or] at hd3
      exact kernel_of_no_three v1 v2 v3 v4 hd3.1 hd3.2.1 hd3.2.2.1 hd3.2.2.2
  · rw [not_or, not_or, not_or] at hd2
    exact kernel_of_no_two v1 v2 v3 v4 hd2.1 hd2.2.1 hd2.2.2.1 hd2.2.2.2

end LonelyRunnerFiveReduction
