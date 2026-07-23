/-
# Lonely Runner `k = 4`: partial progress on `FourThreeResidualCaseA`

This file attacks `LonelyRunnerFourThreeResidualCaseB.FourThreeResidualCaseA`, the sole
remaining open residual of `k = 4` Lonely Runner (see that module and
`docs/kb/conjectures/conj-2026-07-09-lonelyrunner-k4-true.json` for the full picture):
pairwise-distinct, pairwise-coprime, positive triples `x, y, z` where a *single* element is
divisible by `12` (carries both the `4` and the `3` factor at once).

## What this file does NOT do

It does **not** close `FourThreeResidualCaseA` in general. Extensive numeric and
theoretical exploration this session (see the dispatch report) confirms the prior finding
for the parent `CoprimeKernel` residual: the required witness genuinely depends on the
deep factorization structure of the `12`-carrier's cofactor (`a = x / 12`, or whichever
element carries the `12`) in a hierarchical, prime-by-prime way (e.g. for `x = 12, y = 1,
z = 5`, the closed-form witness `t = 2/7` works for *most* residues of a scaling cofactor
`a` modulo `7`, but fails whenever `7 ∣ a`, requiring a different fallback witness — and
that fallback itself fails for yet other residues). No single closed-form formula, no
fixed-modulus residue construction, and no slack/perturbation argument suffices in
general — this matches the documented conclusion of
`docs/kb/failed/2026-07-09__conj-2026-07-09-lonelyrunner-k4-true__coprimekernel-tight.json`
that the genuine route is the Barajas–Serra descending-valuation Prime Filtering Lemma, a
multi-file research-level formalization effort that was not completed in a prior escalated
session and is not completed here either.

## What this file DOES prove

An honest, unconditional **partial** result covering the "dominant speed" sub-case: if one
of the three speeds is at least `3×` the magnitude of the larger of the other two, a lonely
time at bound `1/4` exists — with **no** coprimality or `12`-divisibility hypothesis needed
at all (the argument is purely a magnitude/continuity one). This is the direct `1/4`-bound
analogue of `LonelyRunnerFour.lonely_runner_four_dominant` (which proves the same *shape*
of result at the weaker bound `1/5` with a milder `1.5×` domination hypothesis): tightening
the target from `1/5` to `1/4` costs exactly the extra slack margin (`1/3 − 1/4 = 1/12`
instead of `1/3 − 1/5 = 2/15`), which forces the domination factor up from `1.5×` to `3×`
(worked out via the same `nid` 1-Lipschitz + local-steering argument, re-derived here at
the `1/4` threshold).

A finite numeric sweep (`x < 60`, `12 ∣ x`, pairwise-coprime, pairwise-distinct) shows this
dominant sub-case covers roughly 8% of `FourThreeResidualCaseA` instances (59 / 720) — a
real but partial slice. The genuinely hard "comparable magnitude" instances (e.g.
`x = 12, y = 1, z = 5`) are *not* covered and remain open.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Propositio.Combinatorics.LonelyRunnerSmallK
import Propositio.Combinatorics.LonelyRunnerFour
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseB

namespace LonelyRunnerFourThreeResidualCaseA

open LonelyRunnerSmallK LonelyRunnerFour

/-- **`1/4`-bound local steering lemma.** From any starting point `x0`, a shift of size at
most `1/4` suffices to bring `x0` to nearest-integer distance `≥ 1/4`. The `1/4` analogue
of `LonelyRunnerFour.nid_shift_exists` (which is the `1/5` version). -/
lemma nid_shift_exists_quarter (x0 : ℝ) : ∃ ε : ℝ, |ε| ≤ 1 / 4 ∧ (1 : ℝ) / 4 ≤ nid (x0 + ε) := by
  have hf0 : 0 ≤ Int.fract x0 := Int.fract_nonneg x0
  have hf1 : Int.fract x0 < 1 := Int.fract_lt_one x0
  rcases lt_or_ge (Int.fract x0) (1 / 4 : ℝ) with h1 | h1
  · refine ⟨1 / 4 - Int.fract x0, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; linarith
    · have he : Int.fract (x0 + (1 / 4 - Int.fract x0)) = 1 / 4 := by
        have hstep := fract_add_eq x0 (1 / 4 - Int.fract x0) (by linarith) (by linarith)
        rw [hstep]; ring
      rw [nid_eq, he]
      exact le_min (by norm_num) (by norm_num)
  · rcases lt_or_ge (3 / 4 : ℝ) (Int.fract x0) with h2 | h2
    · refine ⟨3 / 4 - Int.fract x0, ?_, ?_⟩
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have he : Int.fract (x0 + (3 / 4 - Int.fract x0)) = 3 / 4 := by
          have hstep := fract_add_eq x0 (3 / 4 - Int.fract x0) (by linarith) (by linarith)
          rw [hstep]; ring
        rw [nid_eq, he]
        exact le_min (by norm_num) (by norm_num)
    · refine ⟨0, by norm_num, ?_⟩
      rw [add_zero, nid_eq]
      exact le_min h1 (by linarith)

/-- **Lonely Runner dominant-speed bound, target `1/4`** (the honest `k = 4` bound). Three
distinct nonzero integer speeds `v1, v2, v3` with the third at least `3×` the magnitude of
the larger of the other two (`4 |v3| ≥ 12 · max(|v1|,|v2|)`, i.e. `|v3| ≥ 3 max(|v1|,|v2|)`):
there is a time `t` with `nid (vi·t) ≥ 1/4` for all three `i`. No coprimality hypothesis is
needed. -/
theorem lonely_runner_four_quarter_dominant (v1 v2 v3 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0)
    (h3 : v3 ≠ 0) (h12 : v1 ≠ v2)
    (hdom : 4 * |(v3 : ℝ)| ≥ 12 * max |(v1 : ℝ)| |(v2 : ℝ)|) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((v3 : ℝ) * t) := by
  set M : ℝ := max |(v1 : ℝ)| |(v2 : ℝ)| with hMdef
  set C : ℝ := |(v3 : ℝ)| with hCdef
  have hv1R : (v1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
  have hv3R : (v3 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h3
  have hCpos : 0 < C := by rw [hCdef]; exact abs_pos.mpr hv3R
  have hM1 : |(v1 : ℝ)| ≤ M := le_max_left _ _
  have hM2 : |(v2 : ℝ)| ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le (abs_pos.mpr hv1R) hM1
  -- Step 1: get `t0` good for `v1, v2` with the *stronger* bound `1/3`.
  obtain ⟨t0, ht1, ht2⟩ := lonely_runner_three v1 v2 h1 h2 h12
  -- Step 2: locally steer `v3 * t0` into the good zone with a small shift `ε`.
  obtain ⟨ε, hεabs, hεnid⟩ := nid_shift_exists_quarter ((v3 : ℝ) * t0)
  set δ : ℝ := ε / (v3 : ℝ) with hδdef
  have hδeq : (v3 : ℝ) * δ = ε := by rw [hδdef]; field_simp
  have hδabs : |δ| ≤ (1 / 4) / C := by
    have heq : |δ| = |ε| / C := by rw [hδdef, abs_div, ← hCdef]
    rw [heq]
    gcongr
  -- Step 3: the margin `1/3 - 1/4 = 1/12` absorbs the perturbation for `v1, v2`.
  have step2 : M * (1 / 4 / C) ≤ 1 / 12 := by
    rw [← mul_div_assoc, div_le_iff₀ hCpos]
    linarith [hdom]
  have hbound1 : |(v1 : ℝ)| * |δ| ≤ 1 / 12 := by
    calc |(v1 : ℝ)| * |δ| ≤ M * |δ| := mul_le_mul_of_nonneg_right hM1 (abs_nonneg δ)
      _ ≤ M * ((1 / 4) / C) := by gcongr
      _ ≤ 1 / 12 := step2
  have hbound2 : |(v2 : ℝ)| * |δ| ≤ 1 / 12 := by
    calc |(v2 : ℝ)| * |δ| ≤ M * |δ| := mul_le_mul_of_nonneg_right hM2 (abs_nonneg δ)
      _ ≤ M * ((1 / 4) / C) := by gcongr
      _ ≤ 1 / 12 := step2
  have key1 : (1 : ℝ) / 4 ≤ nid ((v1 : ℝ) * (t0 + δ)) := by
    have habs : |(v1 : ℝ) * t0 - (v1 : ℝ) * (t0 + δ)| = |(v1 : ℝ)| * |δ| := by
      have e : (v1 : ℝ) * t0 - (v1 : ℝ) * (t0 + δ) = -((v1 : ℝ) * δ) := by ring
      rw [e, abs_neg, abs_mul]
    have h := nid_le_add_dist ((v1 : ℝ) * t0) ((v1 : ℝ) * (t0 + δ))
    rw [habs] at h
    linarith [ht1, hbound1, h]
  have key2 : (1 : ℝ) / 4 ≤ nid ((v2 : ℝ) * (t0 + δ)) := by
    have habs : |(v2 : ℝ) * t0 - (v2 : ℝ) * (t0 + δ)| = |(v2 : ℝ)| * |δ| := by
      have e : (v2 : ℝ) * t0 - (v2 : ℝ) * (t0 + δ) = -((v2 : ℝ) * δ) := by ring
      rw [e, abs_neg, abs_mul]
    have h := nid_le_add_dist ((v2 : ℝ) * t0) ((v2 : ℝ) * (t0 + δ))
    rw [habs] at h
    linarith [ht2, hbound2, h]
  have key3 : (1 : ℝ) / 4 ≤ nid ((v3 : ℝ) * (t0 + δ)) := by
    have e : (v3 : ℝ) * (t0 + δ) = (v3 : ℝ) * t0 + ε := by
      have e0 : (v3 : ℝ) * (t0 + δ) = (v3 : ℝ) * t0 + (v3 : ℝ) * δ := by ring
      rw [e0, hδeq]
    rw [e]; exact hεnid
  exact ⟨t0 + δ, key1, key2, key3⟩

/-- **Nat-level symmetric wrapper.** For three pairwise-distinct positive naturals with
*some* one of them at least `3×` the max of the other two, a lonely time at bound `1/4`
exists. No coprimality or divisibility hypothesis needed — this covers a genuine slice of
`FourThreeResidualCaseA` (and more generally of the full `CoprimeKernel`) via pure
magnitude/continuity, complementing (not replacing) the still-open "comparable magnitude"
residual. -/
theorem caseA_dominant_cover (x y z : ℕ) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : 3 * max y z ≤ x ∨ 3 * max x z ≤ y ∨ 3 * max x y ≤ z) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t) := by
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  have hxZ : (x : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hx0
  have hyZ : (y : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hy0
  have hzZ : (z : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hz0
  have hxyZ : (x : ℤ) ≠ (y : ℤ) := by exact_mod_cast hxy
  have hxzZ : (x : ℤ) ≠ (z : ℤ) := by exact_mod_cast hxz
  have hyzZ : (y : ℤ) ≠ (z : ℤ) := by exact_mod_cast hyz
  rcases hdom with hxd | hyd | hzd
  · -- `x` dominates: apply with `(v1,v2,v3) = (y,z,x)`.
    have hdomR : 4 * |(x : ℝ)| ≥ 12 * max |(y : ℝ)| |(z : ℝ)| := by
      have hcast : (3 * max y z : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxd
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)), abs_of_nonneg (by positivity : (0:ℝ) ≤ (y:ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (z:ℝ))]
      push_cast at hcast
      linarith [hcast]
    obtain ⟨t, hty, htz, htx⟩ :=
      lonely_runner_four_quarter_dominant (y : ℤ) (z : ℤ) (x : ℤ) hyZ hzZ hxZ hyzZ hdomR
    exact ⟨t, htx, hty, htz⟩
  · -- `y` dominates: apply with `(v1,v2,v3) = (x,z,y)`.
    have hdomR : 4 * |(y : ℝ)| ≥ 12 * max |(x : ℝ)| |(z : ℝ)| := by
      have hcast : (3 * max x z : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyd
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (y:ℝ)), abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (z:ℝ))]
      push_cast at hcast
      linarith [hcast]
    obtain ⟨t, htx, htz, hty⟩ :=
      lonely_runner_four_quarter_dominant (x : ℤ) (z : ℤ) (y : ℤ) hxZ hzZ hyZ hxzZ hdomR
    exact ⟨t, htx, hty, htz⟩
  · -- `z` dominates: apply with `(v1,v2,v3) = (x,y,z)`.
    have hdomR : 4 * |(z : ℝ)| ≥ 12 * max |(x : ℝ)| |(y : ℝ)| := by
      have hcast : (3 * max x y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzd
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (z:ℝ)), abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (y:ℝ))]
      push_cast at hcast
      linarith [hcast]
    obtain ⟨t, htx, hty, htz⟩ :=
      lonely_runner_four_quarter_dominant (x : ℤ) (y : ℤ) (z : ℤ) hxZ hyZ hzZ hxyZ hdomR
    exact ⟨t, htx, hty, htz⟩

/-- **Partial coverage of `FourThreeResidualCaseA` via magnitude domination.** Given the
full `FourThreeResidualCaseA` hypotheses (positivity, distinctness, pairwise coprimality,
`12` dividing one element) *plus* the extra domination hypothesis that one element is `≥ 3×`
the max of the other two, the conclusion holds. Coprimality and the `12`-divisibility
hypothesis are not actually used (the underlying `caseA_dominant_cover` is more general) —
they are threaded through only so this lemma has *exactly* the shape of a restricted
instance of `LonelyRunnerFourThreeResidualCaseB.FourThreeResidualCaseA`, for direct
combination with any future case split on domination vs. comparable magnitude. -/
theorem caseA_partial_dominant (x y z : ℕ) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (_cxy : Nat.Coprime x y) (_cxz : Nat.Coprime x z) (_cyz : Nat.Coprime y z)
    (_h12 : 12 ∣ x ∨ 12 ∣ y ∨ 12 ∣ z)
    (hdom : 3 * max y z ≤ x ∨ 3 * max x z ≤ y ∨ 3 * max x y ≤ z) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t) :=
  caseA_dominant_cover x y z hx1 hy1 hz1 hxy hxz hyz hdom

end LonelyRunnerFourThreeResidualCaseA
