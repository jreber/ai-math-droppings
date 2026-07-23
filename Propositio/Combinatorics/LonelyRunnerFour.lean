/-
# Lonely Runner Conjecture: a dominant-speed bound with 3 relative speeds, target `1/5`

**Naming correction (caught by adversarial panel review):** this file was originally
titled as attempting "the `k = 4` case," matching the (mislabeled) research-queue card
`conj-2026-07-05-007`. That is NOT the correct correspondence. This repo's own
established convention (`LonelyRunnerSmallK.lean`) is unambiguous: `lonely_runner_two`
uses **1** relative speed and proves bound `1/2` (labeled `k = 2`); `lonely_runner_three`
uses **2** relative speeds and proves bound `1/3` (labeled `k = 3`). By that pattern, the
honest `k = 4` case uses **3** relative speeds and should target bound `1/4`, NOT `1/5`
(a bound of `1/5` with only 3 relative speeds corresponds to neither `k=4` — wrong bound —
nor `k=5` — wrong speed count, which needs 4 relative speeds). This file proves a
**true, standalone, but non-standard** statement: 3 relative speeds, dominant-speed
hypothesis, target `1/5` (a strictly *weaker*/easier target than the honest `k=4` bound
of `1/4` would be). It does **not** resolve `k=4` LRC in any indexing convention. The
research-queue card should be corrected to either restate the target as `1/4` (harder,
not attempted here) or be relabeled to match what's actually proved.

## What this file actually proves

**Not** the fully general `k = 4` statement. After substantial analysis (recorded in the
session report / KB), the "sum-modulus + Bézout" trick that makes `k = 3` work
(`LonelyRunnerSmallK.core`) does **not** lift to three simultaneous residue constraints:
with a single degree of freedom `t` (or `m` after discretizing to `t = m/s`), one Bézout
inversion can tie together *two* residues via the self-dual relation `b ≡ -a (mod a+b)`,
but there is no analogous three-way identity forcing a *third* independent residue into
place. A naive measure/covering (union-bound) argument over one period also fails: each
"bad set" `{t : nid(vi t) < 1/5}` has measure `2/5` of the period, and `3 · 2/5 = 6/5 > 1`,
so the trivial union bound cannot rule out the bad sets covering everything. The genuine
`k = 4` theorem (Betke–Wills 1972 / Cusick 1974) requires real case analysis beyond what
was tractable to reconstruct and formalize soundly in this session.

**What *is* proved here** is an honest, unconditional partial result:
`lonely_runner_four_dominant` — the `k = 4` statement holds whenever one of the three
speeds is at least (a comfortable multiple of) the size of the other two. The idea: pick
the two smaller-magnitude speeds `v1, v2` and apply `lonely_runner_three` to get a time
`t0` with both at distance `≥ 1/3` (more slack than the `1/5` we ultimately need). The
nearest-integer-distance function `nid` is `1`-Lipschitz, so a *small* perturbation
`t0 ↦ t0 + δ` keeps `v1, v2` safely above `1/5` while giving enough freedom in the
image `v3 * t` to steer it into the "good" arc `[1/5, 4/5]` for the dominant third speed
`v3`, since that arc has room `1/5` on each side (a purely local/continuity argument, not
a Diophantine one). Quantitatively: if `2 * |v3| ≥ 3 * max(|v1|, |v2|)` then the required
perturbation exists.

This is real, unconditional, and covers an infinite family of speed-triples (e.g. any
triple where the speeds are sufficiently spread in magnitude), but it is **not** the full
conjecture: triples of comparable magnitude (e.g. `v1,v2,v3` close together, no dominant
speed) are not covered and, per the analysis above, seem to genuinely need the
Betke–Wills-style case analysis.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Propositio.Combinatorics.LonelyRunnerSmallK

namespace LonelyRunnerFour

open LonelyRunnerSmallK

/-- `nid x ≤ |x - z|` for any integer `z` — this is just `round_le` unfolded through the
definition of `nid`. -/
lemma nid_le_abs_sub_intCast (x : ℝ) (z : ℤ) : nid x ≤ |x - (z : ℝ)| := by
  unfold nid
  exact round_le x z

/-- **`nid` is `1`-Lipschitz.** -/
lemma nid_le_add_dist (x y : ℝ) : nid x ≤ nid y + |x - y| := by
  have h := nid_le_abs_sub_intCast x (round y)
  have htri : |x - (round y : ℝ)| ≤ |x - y| + |y - (round y : ℝ)| := by
    have e : x - (round y : ℝ) = (x - y) + (y - (round y : ℝ)) := by ring
    rw [e]; exact abs_add_le _ _
  have hnidy : nid y = |y - (round y : ℝ)| := rfl
  rw [hnidy]
  linarith [h, htri]

/-- If `Int.fract x0 + ε` stays in `[0, 1)`, then it computes `Int.fract (x0 + ε)`. -/
lemma fract_add_eq (x0 ε : ℝ) (h0 : 0 ≤ Int.fract x0 + ε) (h1 : Int.fract x0 + ε < 1) :
    Int.fract (x0 + ε) = Int.fract x0 + ε := by
  have hbase : Int.fract x0 + (⌊x0⌋ : ℝ) = x0 := Int.fract_add_floor x0
  have hfl : ⌊x0 + ε⌋ = ⌊x0⌋ := by
    rw [Int.floor_eq_iff]
    refine ⟨by linarith, by linarith⟩
  have hbase2 : Int.fract (x0 + ε) + (⌊x0 + ε⌋ : ℝ) = x0 + ε := Int.fract_add_floor (x0 + ε)
  rw [hfl] at hbase2
  linarith [hbase, hbase2]

/-- **Local steering lemma.** From any starting point `x0`, a shift of size at most `1/5`
suffices to bring `x0` to nearest-integer distance `≥ 1/5`. This is the continuity/local
argument that replaces the (unavailable, for 3 simultaneous constraints) Diophantine
covering step. -/
lemma nid_shift_exists (x0 : ℝ) : ∃ ε : ℝ, |ε| ≤ 1 / 5 ∧ (1 : ℝ) / 5 ≤ nid (x0 + ε) := by
  have hf0 : 0 ≤ Int.fract x0 := Int.fract_nonneg x0
  have hf1 : Int.fract x0 < 1 := Int.fract_lt_one x0
  rcases lt_or_ge (Int.fract x0) (1 / 5 : ℝ) with h1 | h1
  · refine ⟨1 / 5 - Int.fract x0, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; linarith
    · have he : Int.fract (x0 + (1 / 5 - Int.fract x0)) = 1 / 5 := by
        have hstep := fract_add_eq x0 (1 / 5 - Int.fract x0) (by linarith) (by linarith)
        rw [hstep]; ring
      rw [nid_eq, he]
      exact le_min (by norm_num) (by norm_num)
  · rcases lt_or_ge (4 / 5 : ℝ) (Int.fract x0) with h2 | h2
    · refine ⟨4 / 5 - Int.fract x0, ?_, ?_⟩
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have he : Int.fract (x0 + (4 / 5 - Int.fract x0)) = 4 / 5 := by
          have hstep := fract_add_eq x0 (4 / 5 - Int.fract x0) (by linarith) (by linarith)
          rw [hstep]; ring
        rw [nid_eq, he]
        exact le_min (by norm_num) (by norm_num)
    · refine ⟨0, by norm_num, ?_⟩
      rw [add_zero, nid_eq]
      exact le_min h1 (by linarith)

/-- **Lonely Runner dominant-speed bound, target `1/5`** (3 relative speeds; NOT the
honest `k = 4` case, which would target `1/4` — see module docstring for the naming
correction). Three distinct nonzero integer speeds `v1, v2, v3` with the third at least
`1.5×` the magnitude of the larger of the other two (`2|v3| ≥ 3·max(|v1|,|v2|)`): there
is a time `t` with `nid (vi·t) ≥ 1/5` for all three `i`. -/
theorem lonely_runner_four_dominant (v1 v2 v3 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2)
    (hdom : 2 * |(v3 : ℝ)| ≥ 3 * max |(v1 : ℝ)| |(v2 : ℝ)|) :
    ∃ t : ℝ, (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * t) := by
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
  obtain ⟨ε, hεabs, hεnid⟩ := nid_shift_exists ((v3 : ℝ) * t0)
  set δ : ℝ := ε / (v3 : ℝ) with hδdef
  have hδeq : (v3 : ℝ) * δ = ε := by rw [hδdef]; field_simp
  have hδabs : |δ| ≤ (1 / 5) / C := by
    have heq : |δ| = |ε| / C := by rw [hδdef, abs_div, ← hCdef]
    rw [heq]
    gcongr
  -- Step 3: the margin `1/3 - 1/5 = 2/15` absorbs the perturbation for `v1, v2`.
  have step2 : M * (1 / 5 / C) ≤ 2 / 15 := by
    rw [← mul_div_assoc, div_le_iff₀ hCpos]
    linarith [hdom]
  have hbound1 : |(v1 : ℝ)| * |δ| ≤ 2 / 15 := by
    calc |(v1 : ℝ)| * |δ| ≤ M * |δ| := mul_le_mul_of_nonneg_right hM1 (abs_nonneg δ)
      _ ≤ M * ((1 / 5) / C) := by gcongr
      _ ≤ 2 / 15 := step2
  have hbound2 : |(v2 : ℝ)| * |δ| ≤ 2 / 15 := by
    calc |(v2 : ℝ)| * |δ| ≤ M * |δ| := mul_le_mul_of_nonneg_right hM2 (abs_nonneg δ)
      _ ≤ M * ((1 / 5) / C) := by gcongr
      _ ≤ 2 / 15 := step2
  have key1 : (1 : ℝ) / 5 ≤ nid ((v1 : ℝ) * (t0 + δ)) := by
    have habs : |(v1 : ℝ) * t0 - (v1 : ℝ) * (t0 + δ)| = |(v1 : ℝ)| * |δ| := by
      have e : (v1 : ℝ) * t0 - (v1 : ℝ) * (t0 + δ) = -((v1 : ℝ) * δ) := by ring
      rw [e, abs_neg, abs_mul]
    have h := nid_le_add_dist ((v1 : ℝ) * t0) ((v1 : ℝ) * (t0 + δ))
    rw [habs] at h
    linarith [ht1, hbound1, h]
  have key2 : (1 : ℝ) / 5 ≤ nid ((v2 : ℝ) * (t0 + δ)) := by
    have habs : |(v2 : ℝ) * t0 - (v2 : ℝ) * (t0 + δ)| = |(v2 : ℝ)| * |δ| := by
      have e : (v2 : ℝ) * t0 - (v2 : ℝ) * (t0 + δ) = -((v2 : ℝ) * δ) := by ring
      rw [e, abs_neg, abs_mul]
    have h := nid_le_add_dist ((v2 : ℝ) * t0) ((v2 : ℝ) * (t0 + δ))
    rw [habs] at h
    linarith [ht2, hbound2, h]
  have key3 : (1 : ℝ) / 5 ≤ nid ((v3 : ℝ) * (t0 + δ)) := by
    have e : (v3 : ℝ) * (t0 + δ) = (v3 : ℝ) * t0 + ε := by
      have e0 : (v3 : ℝ) * (t0 + δ) = (v3 : ℝ) * t0 + (v3 : ℝ) * δ := by ring
      rw [e0, hδeq]
    rw [e]; exact hεnid
  exact ⟨t0 + δ, key1, key2, key3⟩
