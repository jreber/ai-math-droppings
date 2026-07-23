/-
# Lonely Runner `k = 4`: reducing the coprime kernel to the `{4·, 3·}`-residual

This file attacks `LonelyRunnerFourResidual.CoprimeKernel`, the honest open heart of the
`k = 4` Lonely Runner Conjecture (three pairwise-distinct, pairwise-coprime positive integer
speeds, target bound `1/4`).  `LonelyRunnerFourResidual.lonely_runner_four_reduce` already
shows this kernel is *exactly* the residual left after the equal-magnitude and gcd-pair cases.

## What is proved here

The kernel is reduced further, unconditionally, by two elementary explicit witnesses:

* **`nid_ge_quarter_of_residue`** — the `1/4` analogue of `LonelyRunnerSmallK.nid_ge_of_residue`:
  a rational `m / n` is at nearest-integer distance `≥ 1/4` as soon as its residue `r = m mod n`
  lies in the middle band `[n/4, 3n/4]`.  Reusable.

* **`nid_quarter_time`** — for any speed `v` with `¬ (4 ∣ v)`, the fixed time `t = 1/4` gives
  `nid (v · (1/4)) ≥ 1/4`.  (Residue `v mod 4 ∈ {1,2,3}` ⇒ band condition.)

* **`nid_third_time`** — for any speed `v` with `¬ (3 ∣ v)`, the fixed time `t = 1/3` gives
  `nid (v · (1/3)) ≥ 1/4`.  (Residue `v mod 3 ∈ {1,2}` ⇒ `nid = 1/3 ≥ 1/4`.)

Consequently `t = 1/4` solves *any* triple with **no** multiple of `4`, and `t = 1/3` solves
*any* triple with **no** multiple of `3`.  Hence:

* **`coprimeKernel_of_residual`** — if the kernel holds for the thin residual `R` of triples
  that contain **both** a multiple of `4` and a multiple of `3`, then the full `CoprimeKernel`
  holds.  `R` is exactly the Barajas–Serra arc-compression regime (one speed `≡ 0 mod 4`, one
  `≡ 0 mod 3`); its numeric extremal value is `≥ 2/7 > 1/4`, so the genuinely tight instance
  `(1,2,3)` — which has *no* multiple of `4` — is discharged here by `t = 1/4`.

The reduction is honest: `R` remains open and is stated as the explicit hypothesis
`FourThreeResidual`.  No `sorry`, no `axiom`, no `native_decide`.
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
import Propositio.Combinatorics.LonelyRunnerFourResidual

namespace LonelyRunnerCoprimeKernel

open LonelyRunnerSmallK LonelyRunnerFourResidual

/-- **Reusable `1/4` residue bound.** Nearest-integer distance of a rational `m / n` is
`≥ 1/4` whenever its residue `r = m mod n` lies in the middle band `[n/4, 2·n − n/4]`, i.e.
`n ≤ 4·r ≤ 3·n`.  This is the `1/4` analogue of `LonelyRunnerSmallK.nid_ge_of_residue`. -/
lemma nid_ge_quarter_of_residue (m : ℤ) (n : ℕ) (hn : 0 < n) (r : ℤ)
    (hr : m % (n : ℤ) = r) (h1 : (n : ℝ) ≤ 4 * (r : ℝ)) (h2 : 4 * (r : ℝ) ≤ 3 * (n : ℝ)) :
    (1 : ℝ) / 4 ≤ nid ((m : ℝ) / (n : ℝ)) := by
  rw [nid_eq, Int.fract_div_intCast_eq_div_intCast_mod, hr]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (1 : ℝ) / 4 ≤ (r : ℝ) / n := by
    rw [le_div_iff₀ hn']; linarith
  have e2 : (r : ℝ) / n ≤ 3 / 4 := by
    rw [div_le_iff₀ hn']; linarith
  exact le_min e1 (by linarith)

/-- **`t = 1/4` witness.** If `v` is not a multiple of `4`, then at time `t = 1/4` the runner
of speed `v` is at nearest-integer distance `≥ 1/4`. -/
lemma nid_quarter_time (v : ℕ) (hv : ¬ (4 ∣ v)) :
    (1 : ℝ) / 4 ≤ nid ((v : ℝ) * (1 / 4)) := by
  have h0 : 0 ≤ (v : ℤ) % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : (v : ℤ) % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hne : (v : ℤ) % 4 ≠ 0 := by
    intro h
    apply hv
    have hd : (4 : ℤ) ∣ (v : ℤ) := Int.dvd_of_emod_eq_zero h
    exact_mod_cast hd
  -- residue `r = v mod 4 ∈ {1,2,3}`
  set r : ℤ := (v : ℤ) % 4 with hrdef
  have hr1 : (1 : ℤ) ≤ r := by omega
  have hr3 : r ≤ (3 : ℤ) := by omega
  have hcast : (v : ℝ) * (1 / 4) = ((v : ℤ) : ℝ) / ((4 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  refine nid_ge_quarter_of_residue (v : ℤ) 4 (by norm_num) r hrdef.symm ?_ ?_
  · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    push_cast; linarith
  · have : (r : ℝ) ≤ (3 : ℝ) := by exact_mod_cast hr3
    push_cast; linarith

/-- **`t = 1/3` witness.** If `v` is not a multiple of `3`, then at time `t = 1/3` the runner
of speed `v` is at nearest-integer distance `≥ 1/4` (in fact `= 1/3`). -/
lemma nid_third_time (v : ℕ) (hv : ¬ (3 ∣ v)) :
    (1 : ℝ) / 4 ≤ nid ((v : ℝ) * (1 / 3)) := by
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
  refine nid_ge_quarter_of_residue (v : ℤ) 3 (by norm_num) r hrdef.symm ?_ ?_
  · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    push_cast; linarith
  · have : (r : ℝ) ≤ (2 : ℝ) := by exact_mod_cast hr2
    push_cast; linarith

/-- **No multiple of `4` ⇒ `t = 1/4` solves the triple.** Needs neither coprimality nor
distinctness. -/
lemma kernel_of_no_four (x y z : ℕ) (hx : ¬ (4 ∣ x)) (hy : ¬ (4 ∣ y)) (hz : ¬ (4 ∣ z)) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t) :=
  ⟨1 / 4, nid_quarter_time x hx, nid_quarter_time y hy, nid_quarter_time z hz⟩

/-- **No multiple of `3` ⇒ `t = 1/3` solves the triple.** Needs neither coprimality nor
distinctness. -/
lemma kernel_of_no_three (x y z : ℕ) (hx : ¬ (3 ∣ x)) (hy : ¬ (3 ∣ y)) (hz : ¬ (3 ∣ z)) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t) :=
  ⟨1 / 3, nid_third_time x hx, nid_third_time y hy, nid_third_time z hz⟩

/-- The `{4·, 3·}`-**residual** kernel: the coprime kernel restricted to triples that contain
**both** a multiple of `4` and a multiple of `3`.  This is the Barajas–Serra arc-compression
regime and remains open; it is packaged here as a reusable hypothesis shape. -/
def FourThreeResidual : Prop :=
  ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → 1 ≤ z → x ≠ y → x ≠ z → y ≠ z →
    Nat.Coprime x y → Nat.Coprime x z → Nat.Coprime y z →
    (4 ∣ x ∨ 4 ∣ y ∨ 4 ∣ z) → (3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z) →
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t)

/-- **Reduction of the coprime kernel to the `{4·, 3·}`-residual.** If the kernel holds for
every pairwise-distinct pairwise-coprime positive triple that contains both a multiple of `4`
and a multiple of `3`, then the full `CoprimeKernel` holds.

Triples with no multiple of `4` are solved unconditionally by `t = 1/4`; triples with no
multiple of `3` by `t = 1/3`; the only remaining triples are the residual `R`, where `H`
applies.  In particular the extremal tight triple `(1,2,3)` — which has no multiple of `4` —
is discharged here by `t = 1/4`. -/
theorem coprimeKernel_of_residual (H : FourThreeResidual) : CoprimeKernel := by
  intro x y z hx hy hz hxy hxz hyz cxy cxz cyz
  by_cases h4 : 4 ∣ x ∨ 4 ∣ y ∨ 4 ∣ z
  · by_cases h3 : 3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z
    · exact H x y z hx hy hz hxy hxz hyz cxy cxz cyz h4 h3
    · rw [not_or, not_or] at h3
      exact kernel_of_no_three x y z h3.1 h3.2.1 h3.2.2
  · rw [not_or, not_or] at h4
    exact kernel_of_no_four x y z h4.1 h4.2.1 h4.2.2

end LonelyRunnerCoprimeKernel
