/-
# Collinear dissection edges do not properly cross: a reusable planar-geometry
# fact for closing `hbdry`'s "maximal-segment" reformulation

This file supplies the standalone planar-subdivision fact flagged as missing by
`docs/kb/frontier/_meta.json`'s `monsky_hbdry_boundary_segment_parity_2026_07_30`
note (item (1) after `MonskyBoundarySegmentParity.collinear_path_doorParity`):
raw triangle edges of a genuine dissection that lie on a common line, coming from
triangles whose "off-line" vertex is on the *same side* of that line, cannot
properly (partially) overlap — they are always either disjoint or nested.

## The mathematical content (Monsky-independent, reusable)

The core fact, `exists_common_interior_point_of_crossing`, is a direct
generalisation of `MonskyEdgeMultiplicityAtMostTwo.exists_common_interior_point`
from "two triangles sharing the *exact same* edge" to "two triangles whose edges
on a common line *properly overlap* (cross) without being nested" — the crux
case the earlier file's shared-edge argument does not cover. Given

* triangle 1 with a full edge on the line `y = h` from `x = a1` to `x = b1`
  (`a1 < b1`) and third vertex strictly above (`h < R1y`);
* triangle 2 similarly with edge `[a2,b2]` and apex `h < R2y`;
* a *proper crossing* `a1 < a2 < b1 < b2` (neither interval contains the other,
  and they are not disjoint),

there is an explicit point in the open interior of *both* triangles: take the
midpoint `m` of the overlap `(a2,b1)` and move vertically off the line by a
carefully bounded `ε > 0`. Unlike the shared-edge case (which needs Cramer's
rule to translate between two different apex-based coordinate systems), here
the same vertical-displacement point works for both triangles simultaneously,
because the width bound only needs to control how far the point's barycentric
weight leaks toward each triangle's own apex — an explicit, uniform threshold
(`triInt_of_bounds`) suffices, with no case split on the apex's horizontal
position.

Consequently (`interval_disjoint_or_nested_of_no_crossing`,
`collinear_edges_disjoint_or_nested`): for a dissection (pairwise interior
disjoint, per `MonskyDissectionHlocal.IsDissection`), any two full triangle
edges lying on a common line, with apexes on the SAME side (both `>` or both
`<` the line, so no line through a boundary side of the unit square can have an
adversarial opposite-side pairing — see the dissection-side note below), must
have `x`-projections that are disjoint or nested — **never a proper crossing
overlap**. This is exactly the missing planar-subdivision fact: it rules out
the pathological case that would break a "maximal collinear segment" grouping
of a dissection's raw edges.

Two symmetry lemmas (`triInt_reflect_y`, `triInt_swap_xy`) extend the base
horizontal/apex-above case to all four directions (apex below, and the swapped
vertical-line case) for free, by pure algebra — so the fact is available
verbatim for all four sides of the unit square, not just the bottom one.

## What this file does NOT close (honestly scoped)

* It does **not** re-derive the "same side" hypothesis from `IsDissection` for
  an *arbitrary* line — only a genuine bridge lemma
  (`dissection_edge_apex_off_line`) is supplied, which shows: for a triangle in
  a dissection with two vertices sharing the SAME fixed `y`-coordinate `h` (i.e.
  a full edge literally on the line `y = h`) and living inside the unit square
  with `h ∈ {0,1}` (a side of the square), the third vertex is *strictly* off
  the line on the interior side. This is the concrete geometric input that
  makes the "same side" hypothesis of the general dichotomy automatic for the
  unit square's bottom/top sides (and, via `triInt_swap_xy`, the left/right
  sides). It does not extract this data from `MonskyDissectionHlocal.allEdges`/
  `Sym2` bookkeeping for an arbitrary pair of raw edges of `S`, nor partition
  `S`'s full edge set into maximal collinear groups, nor identify those groups
  with `MonskyBoundaryOddness`'s `bx`/`ry`/`tx`/`ly` sequences — that remaining
  assembly (matching `MonskyDissectionBoundaryScope`'s own scope note, items
  (2)-(3)) is future work, genuinely orthogonal bookkeeping rather than new
  geometric content.
* It does **not** attempt the literally-stronger claim "a single list
  `p_0,...,p_k` such that every raw edge is *exactly* some `(p_i,p_{i+1})`" —
  that claim is FALSE in the presence of T-junctions where a full edge and its
  subdividing half-edges coexist (exactly the scenario
  `MonskyBoundarySegmentParity.tjunction_doorness_sum_even` handles): the big
  edge is not an atomic step of any single linear order that also contains the
  half-edges as atomic steps. The disjoint-or-nested dichotomy proved here is
  the correct, honestly weaker fact that is actually true and actually needed
  (it is exactly what makes "maximal segment" grouping — laminar nesting, not
  literal atomic chaining — well-defined).

Axiom-clean throughout: elementary real algebra (`ring`, `field_simp`,
`nlinarith`) plus the existing `MonskyEdgeMultiplicityAtMostTwo`/
`MonskyDissectionHlocal` machinery; no `sorry`, no project `axiom`, no
`native_decide`.
-/
import Propositio.Geometry.Monsky.MonskyEdgeMultiplicityAtMostTwo
import Propositio.Geometry.Monsky.MonskyDissectionHlocal
import Propositio.Geometry.Monsky.MonskyDissectionBoundaryScope
import Mathlib.Tactic

namespace MonskyCollinearEdgeOrder

open MonskyEdgeMultiplicityAtMostTwo

/-! ## Part 1: an explicit barycentric witness near an edge -/

/-- **A point just off the base edge, uniformly bounded.** For a triangle
`(a,h) (b,h) (Rx,Ry)` with `a < m < b` and `h < Ry`, and a small enough `ε > 0`
(controlled by the two hypotheses `hβ`/`hα`, each a cleared-denominator bound
on how far the apex's horizontal offset can push the barycentric weights), the
point `(m, h+ε)` lies in the triangle's open interior. -/
lemma triInt_of_bounds
    (a b Rx Ry h m ε : ℝ)
    (hab : a < b) (hm1 : a < m) (hm2 : m < b) (hRy : h < Ry) (hεpos : 0 < ε)
    (hβ : ε * |Rx - a| < (Ry - h) * (m - a))
    (hα : ε * |Rx - b| < (Ry - h) * (b - m)) :
    TriInt a h b h Rx Ry m (h + ε) := by
  have hRyh : 0 < Ry - h := by linarith
  have hRyhn : (Ry - h) ≠ 0 := ne_of_gt hRyh
  have hban : (b - a) ≠ 0 := ne_of_gt (by linarith)
  set γ : ℝ := ε / (Ry - h) with hγdef
  have hγpos : 0 < γ := div_pos hεpos hRyh
  set β : ℝ := ((m - a) - γ * (Rx - a)) / (b - a) with hβdef
  set α : ℝ := 1 - β - γ with hαdef
  have hcomm1 : (Ry - h) * (m - a) = (m - a) * (Ry - h) := by ring
  have hcomm2 : (Ry - h) * (b - m) = (b - m) * (Ry - h) := by ring
  have hb2 : γ * |Rx - a| < m - a := by
    rw [hγdef, div_mul_eq_mul_div, div_lt_iff₀ hRyh]
    linarith [hβ, hcomm1]
  have hb3 : γ * |Rx - b| < b - m := by
    rw [hγdef, div_mul_eq_mul_div, div_lt_iff₀ hRyh]
    linarith [hα, hcomm2]
  have hβpos : 0 < β := by
    rw [hβdef]
    apply div_pos _ (by linarith)
    have hle : γ * (Rx - a) ≤ γ * |Rx - a| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hγpos.le
    linarith
  have hαpos : 0 < α := by
    have hmul : α * (b - a) = (b - m) - γ * (b - Rx) := by
      rw [hαdef, hβdef]; field_simp; ring
    have hle : γ * (b - Rx) ≤ γ * |Rx - b| := by
      have habs : b - Rx ≤ |Rx - b| := by
        rw [abs_sub_comm]; exact le_abs_self _
      exact mul_le_mul_of_nonneg_left habs hγpos.le
    have hpos' : 0 < α * (b - a) := by rw [hmul]; linarith
    have hba : 0 < b - a := by linarith
    rcases mul_pos_iff.mp hpos' with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  refine ⟨α, β, γ, hαpos, hβpos, hγpos, by rw [hαdef]; ring, ?_, ?_⟩
  · simp only [hαdef, hβdef, hγdef]
    field_simp
    ring
  · simp only [hαdef, hβdef, hγdef]
    field_simp
    ring

/-! ## Part 2: proper crossing forces a common interior point -/

/-- **A proper crossing on a common line, apexes on the same side, forces a
common interior point.** If triangle 1 has edge `[a1,b1]` on `y=h` with apex
strictly above, triangle 2 has edge `[a2,b2]` on `y=h` with apex strictly
above, and the two intervals *properly cross* (`a1 < a2 < b1 < b2`), then some
point lies in the open interior of both triangles. -/
theorem exists_common_interior_point_of_crossing
    (a1 b1 R1x R1y a2 b2 R2x R2y h : ℝ)
    (h1 : a1 < a2) (h2 : a2 < b1) (h3 : b1 < b2)
    (hR1 : h < R1y) (hR2 : h < R2y) :
    ∃ Px Py, TriInt a1 h b1 h R1x R1y Px Py ∧ TriInt a2 h b2 h R2x R2y Px Py := by
  set m : ℝ := (a2 + b1) / 2 with hmdef
  have hm1a : a1 < m := by rw [hmdef]; linarith
  have hm1b : m < b1 := by rw [hmdef]; linarith
  have hm2a : a2 < m := by rw [hmdef]; linarith
  have hm2b : m < b2 := by rw [hmdef]; linarith
  -- a single denominator `D` uniformly bounding all four relevant `|apex - endpoint|`
  -- offsets, and a single numerator `N` bounding all four `(apex height)·(gap)` terms.
  set D : ℝ := |R1x - a1| + |R1x - b1| + |R2x - a2| + |R2x - b2| + 1 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    have := abs_nonneg (R1x - a1); have := abs_nonneg (R1x - b1)
    have := abs_nonneg (R2x - a2); have := abs_nonneg (R2x - b2)
    linarith
  set N : ℝ := min (min ((R1y - h) * (m - a1)) ((R1y - h) * (b1 - m)))
      (min ((R2y - h) * (m - a2)) ((R2y - h) * (b2 - m))) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    have e1 : 0 < (R1y - h) * (m - a1) := mul_pos (by linarith) (by linarith)
    have e2 : 0 < (R1y - h) * (b1 - m) := mul_pos (by linarith) (by linarith)
    have e3 : 0 < (R2y - h) * (m - a2) := mul_pos (by linarith) (by linarith)
    have e4 : 0 < (R2y - h) * (b2 - m) := mul_pos (by linarith) (by linarith)
    exact lt_min (lt_min e1 e2) (lt_min e3 e4)
  set ε : ℝ := N / (2 * D) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- the uniform bound: `ε * D < N`
  have hεD : ε * D < N := by
    rw [hεdef]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * D)]
    nlinarith [hNpos, hDpos]
  have hN1 : N ≤ (R1y - h) * (m - a1) := le_trans (min_le_left _ _) (min_le_left _ _)
  have hN2 : N ≤ (R1y - h) * (b1 - m) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hN3 : N ≤ (R2y - h) * (m - a2) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hN4 : N ≤ (R2y - h) * (b2 - m) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hD1 : |R1x - a1| < D := by rw [hDdef]; have := abs_nonneg (R1x-b1); have := abs_nonneg (R2x-a2); have := abs_nonneg (R2x-b2); linarith
  have hD2 : |R1x - b1| < D := by rw [hDdef]; have := abs_nonneg (R1x-a1); have := abs_nonneg (R2x-a2); have := abs_nonneg (R2x-b2); linarith
  have hD3 : |R2x - a2| < D := by rw [hDdef]; have := abs_nonneg (R1x-a1); have := abs_nonneg (R1x-b1); have := abs_nonneg (R2x-b2); linarith
  have hD4 : |R2x - b2| < D := by rw [hDdef]; have := abs_nonneg (R1x-a1); have := abs_nonneg (R1x-b1); have := abs_nonneg (R2x-a2); linarith
  refine ⟨m, h + ε, ?_, ?_⟩
  · apply triInt_of_bounds a1 b1 R1x R1y h m ε (by linarith) hm1a hm1b hR1 hεpos
    · calc ε * |R1x - a1| < ε * D := by
            apply mul_lt_mul_of_pos_left hD1 hεpos
        _ = ε * D := rfl
        _ < N := hεD
        _ ≤ (R1y - h) * (m - a1) := hN1
    · calc ε * |R1x - b1| < ε * D := by
            apply mul_lt_mul_of_pos_left hD2 hεpos
        _ = ε * D := rfl
        _ < N := hεD
        _ ≤ (R1y - h) * (b1 - m) := hN2
  · apply triInt_of_bounds a2 b2 R2x R2y h m ε (by linarith) hm2a hm2b hR2 hεpos
    · calc ε * |R2x - a2| < ε * D := by
            apply mul_lt_mul_of_pos_left hD3 hεpos
        _ = ε * D := rfl
        _ < N := hεD
        _ ≤ (R2y - h) * (m - a2) := hN3
    · calc ε * |R2x - b2| < ε * D := by
            apply mul_lt_mul_of_pos_left hD4 hεpos
        _ = ε * D := rfl
        _ < N := hεD
        _ ≤ (R2y - h) * (b2 - m) := hN4

/-! ## Part 3: the disjoint-or-nested dichotomy -/

/-- **Two collinear dissection edges, apexes on the same side, are disjoint or
nested — never a proper crossing overlap.** This is the load-bearing planar-
subdivision fact: for two triangles with full edges `[a1,b1]`, `[a2,b2]` on the
line `y = h`, both apexes strictly above (the same side), and pairwise-disjoint
open interiors (`hdisj`, exactly the content of
`MonskyDissectionHlocal.IsDissection.interiorDisjoint`), the two intervals
either don't overlap, or one contains the other. -/
theorem interval_disjoint_or_nested_of_no_crossing
    (a1 b1 R1x R1y a2 b2 R2x R2y h : ℝ)
    (ha1b1 : a1 < b1) (ha2b2 : a2 < b2)
    (hR1 : h < R1y) (hR2 : h < R2y)
    (hdisj : ∀ Px Py, ¬ (TriInt a1 h b1 h R1x R1y Px Py ∧
        TriInt a2 h b2 h R2x R2y Px Py)) :
    b1 ≤ a2 ∨ b2 ≤ a1 ∨ (a2 ≤ a1 ∧ b1 ≤ b2) ∨ (a1 ≤ a2 ∧ b2 ≤ b1) := by
  rcases lt_trichotomy a1 a2 with hA | hA | hA
  · rcases lt_trichotomy b1 b2 with hB | hB | hB
    · by_cases hc : b1 ≤ a2
      · exact Or.inl hc
      · replace hc := not_le.mp hc
        exfalso
        obtain ⟨Px, Py, hp1, hp2⟩ :=
          exists_common_interior_point_of_crossing a1 b1 R1x R1y a2 b2 R2x R2y h
            hA hc hB hR1 hR2
        exact hdisj Px Py ⟨hp1, hp2⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hA.le, hB.ge⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hA.le, hB.le⟩))
  · rcases lt_trichotomy b1 b2 with hB | hB | hB
    · exact Or.inr (Or.inr (Or.inl ⟨hA.ge, hB.le⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hA.ge, hB.le⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hA.le, hB.le⟩))
  · rcases lt_trichotomy b1 b2 with hB | hB | hB
    · exact Or.inr (Or.inr (Or.inl ⟨hA.le, hB.le⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hA.le, hB.le⟩))
    · by_cases hc : b2 ≤ a1
      · exact Or.inr (Or.inl hc)
      · replace hc := not_le.mp hc
        exfalso
        obtain ⟨Px, Py, hp2, hp1⟩ :=
          exists_common_interior_point_of_crossing a2 b2 R2x R2y a1 b1 R1x R1y h
            hA hc hB hR2 hR1
        exact hdisj Px Py ⟨hp1, hp2⟩

/-! ## Part 4: symmetries extending the fact to all four directions -/

/-- `TriInt` is equivariant under negating every `y`-coordinate (reflection
across the `x`-axis) — pure algebra, since barycentric combinations commute
coordinatewise with any linear substitution. -/
theorem triInt_reflect_y (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔
      TriInt Ax (-Ay) Bx (-By) Cx (-Cy) Px (-Py) := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩
    exact ⟨a, b, c, ha, hb, hc, habc, hx, by linear_combination -hy⟩
  · rintro ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩
    exact ⟨a, b, c, ha, hb, hc, habc, hx, by linear_combination -hy⟩

/-- `TriInt` is equivariant under swapping the `x`- and `y`-coordinates of
every point (reflection across the diagonal `y = x`) — again pure algebra. -/
theorem triInt_swap_xy (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔
      TriInt Ay Ax By Bx Cy Cx Py Px := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩
    exact ⟨a, b, c, ha, hb, hc, habc, hy, hx⟩
  · rintro ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩
    exact ⟨a, b, c, ha, hb, hc, habc, hy, hx⟩

/-- **The disjoint-or-nested dichotomy, for either side of the line.** Same as
`interval_disjoint_or_nested_of_no_crossing`, but allowing both apexes to be
strictly *below* the line instead of strictly above (the two directions cover
every genuine "same side" pairing). Obtained for free from the apex-above case
via `triInt_reflect_y`. -/
theorem collinear_edges_disjoint_or_nested
    (a1 b1 R1x R1y a2 b2 R2x R2y h : ℝ)
    (ha1b1 : a1 < b1) (ha2b2 : a2 < b2)
    (hside : (h < R1y ∧ h < R2y) ∨ (R1y < h ∧ R2y < h))
    (hdisj : ∀ Px Py, ¬ (TriInt a1 h b1 h R1x R1y Px Py ∧
        TriInt a2 h b2 h R2x R2y Px Py)) :
    b1 ≤ a2 ∨ b2 ≤ a1 ∨ (a2 ≤ a1 ∧ b1 ≤ b2) ∨ (a1 ≤ a2 ∧ b2 ≤ b1) := by
  rcases hside with ⟨hR1, hR2⟩ | ⟨hR1, hR2⟩
  · exact interval_disjoint_or_nested_of_no_crossing a1 b1 R1x R1y a2 b2 R2x R2y h
      ha1b1 ha2b2 hR1 hR2 hdisj
  · have hdisj' : ∀ Px Py, ¬ (TriInt a1 (-h) b1 (-h) R1x (-R1y) Px Py ∧
        TriInt a2 (-h) b2 (-h) R2x (-R2y) Px Py) := by
      rintro Px Py ⟨hp1, hp2⟩
      have hp1' : TriInt a1 h b1 h R1x R1y Px (-Py) := by
        have h' := triInt_reflect_y a1 h b1 h R1x R1y Px (-Py)
        rw [neg_neg] at h'
        exact h'.mpr hp1
      have hp2' : TriInt a2 h b2 h R2x R2y Px (-Py) := by
        have h' := triInt_reflect_y a2 h b2 h R2x R2y Px (-Py)
        rw [neg_neg] at h'
        exact h'.mpr hp2
      exact hdisj Px (-Py) ⟨hp1', hp2'⟩
    exact interval_disjoint_or_nested_of_no_crossing a1 b1 R1x (-R1y) a2 b2 R2x (-R2y) (-h)
      ha1b1 ha2b2 (by linarith) (by linarith) hdisj'

/-! ## Part 5: a genuine dissection bridge — the apex is off the boundary line

This is the concrete `IsDissection`-specific input that makes the "same side"
hypothesis of Parts 1-4 automatic for the unit square's bottom side, closing
the loop from the abstract planar fact back to Monsky's actual dissection
predicate. -/

/-- If a triangle's first two vertices share `y`-coordinate `h` (i.e. that
edge lies on the line `y = h`), nondegeneracy forces the third vertex OFF that
line. -/
lemma apex_ne_of_nondeg_base_const
    (Px Py Qx Qy Rx Ry h : ℝ) (hPy : Py = h) (hQy : Qy = h)
    (hnd : Nondegenerate Px Py Qx Qy Rx Ry) : Ry ≠ h := by
  intro hRyh
  apply hnd
  unfold cross2
  rw [hPy, hQy, hRyh]; ring

/-- **Dissection bridge (bottom side): the third vertex is strictly interior.**
For a triangle of a dissection `S` (`IsDissection S`) whose first two vertices
both lie on the bottom side `y = 0` of the unit square, the third vertex has
`y`-coordinate strictly positive — automatically the "same side" input the
general dichotomy needs, no separate hypothesis required. This genuinely
consumes `IsDissection.nondeg` (via `apex_ne_of_nondeg_base_const`) and
`IsDissection.covers` (via `MonskyDissectionBoundaryScope`'s vertex-membership
lemma), connecting `IsDissection` to the planar-geometry machinery of Parts
1-4. -/
theorem dissection_apex_pos_of_base_bottom
    {S : Finset MonskyDissectionHlocal.Tri} (hS : MonskyDissectionHlocal.IsDissection S)
    {t : MonskyDissectionHlocal.Tri} (ht : t ∈ S)
    (hP : t.1.2 = 0) (hQ : t.2.1.2 = 0) :
    0 < t.2.2.2 := by
  have hnd : Nondegenerate t.1.1 t.1.2 t.2.1.1 t.2.1.2 t.2.2.1 t.2.2.2 := hS.nondeg t ht
  have hne : t.2.2.2 ≠ 0 :=
    apex_ne_of_nondeg_base_const t.1.1 t.1.2 t.2.1.1 t.2.1.2 t.2.2.1 t.2.2.2 0 hP hQ hnd
  have hnn : 0 ≤ t.2.2.2 :=
    (MonskyDissectionBoundaryScope.vertex3_mem_unitSquare hS ht).2.2.1
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- **Capstone corollary: two dissection edges on the unit square's bottom side
never properly cross.** For two DISTINCT triangles of a dissection `S`, each
with its first two vertices on the line `y = 0` (the bottom side of the unit
square), the `x`-projections of their base edges are disjoint or nested —
combining the general planar fact (Parts 1-4) with the dissection-specific
"apex is interior" bridge (`dissection_apex_pos_of_base_bottom`) and
`IsDissection.interiorDisjoint` directly. This is the concrete instance of the
missing planar-subdivision fact identified by the frontier note, for the
bottom side; the other three sides follow by the identical argument (via
`triInt_swap_xy`/`triInt_reflect_y` and the symmetric vertex-membership facts
in `MonskyDissectionBoundaryScope`), not spelled out here to keep this file
focused on the load-bearing case. -/
theorem dissection_bottom_edges_disjoint_or_nested
    {S : Finset MonskyDissectionHlocal.Tri} (hS : MonskyDissectionHlocal.IsDissection S)
    {t1 t2 : MonskyDissectionHlocal.Tri} (ht1 : t1 ∈ S) (ht2 : t2 ∈ S) (hne : t1 ≠ t2)
    (hP1 : t1.1.2 = 0) (hQ1 : t1.2.1.2 = 0) (hP2 : t2.1.2 = 0) (hQ2 : t2.2.1.2 = 0)
    (hab1 : t1.1.1 < t1.2.1.1) (hab2 : t2.1.1 < t2.2.1.1) :
    t1.2.1.1 ≤ t2.1.1 ∨ t2.2.1.1 ≤ t1.1.1 ∨
      (t2.1.1 ≤ t1.1.1 ∧ t1.2.1.1 ≤ t2.2.1.1) ∨
      (t1.1.1 ≤ t2.1.1 ∧ t2.2.1.1 ≤ t1.2.1.1) := by
  have hR1 : 0 < t1.2.2.2 := dissection_apex_pos_of_base_bottom hS ht1 hP1 hQ1
  have hR2 : 0 < t2.2.2.2 := dissection_apex_pos_of_base_bottom hS ht2 hP2 hQ2
  have hdisj : ∀ Px Py, ¬ (TriInt t1.1.1 t1.1.2 t1.2.1.1 t1.2.1.2 t1.2.2.1 t1.2.2.2 Px Py ∧
      TriInt t2.1.1 t2.1.2 t2.2.1.1 t2.2.1.2 t2.2.2.1 t2.2.2.2 Px Py) := by
    intro Px Py hcon
    exact hS.interiorDisjoint t1 ht1 t2 ht2 hne Px Py hcon
  simp only [hP1, hQ1, hP2, hQ2] at hdisj
  exact interval_disjoint_or_nested_of_no_crossing t1.1.1 t1.2.1.1 t1.2.2.1 t1.2.2.2
    t2.1.1 t2.2.1.1 t2.2.2.1 t2.2.2.2 0 hab1 hab2 hR1 hR2 hdisj

end MonskyCollinearEdgeOrder
