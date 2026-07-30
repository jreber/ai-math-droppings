/-
# Perimeter edges of a unit-square triangulation have multiplicity exactly 1

This is sub-theorem **(1)** of the three concrete geometric bricks scoped by
`docs/kb/failed/2026-07-26__MonskyBoundaryDoorBridge_conj-2026-07-19-002_hbdry_via_direct_perime.json`
for discharging the `hbdry` hypothesis of
`MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`: for a triangulation of
`[0,1]²`, an edge lying along the square's boundary belongs to **exactly one**
triangle (`MonskySpernerParity.mult inc e = 1`), unlike a generic interior
edge, which belongs to exactly two.

## A precise correction to the naive statement

The failed-attempt record describes the target informally as "perimeter edges
(both endpoints on the boundary) have multiplicity 1". That literal reading is
**false**: `MonskyDiagonalInstance.mult_diagonal` already proves the diagonal
edge `s((0,0),(1,1))` of the two-triangle split has multiplicity **2**, and
*both* its endpoints `(0,0)` and `(1,1)` are corners of the square, hence
"on the boundary" under the naive reading. The correct geometric statement —
proved here — needs the edge's two endpoints to lie on a **common side** of
the square (`SameSide` below), not merely each be *some* boundary point. This
is exactly what distinguishes a genuine perimeter edge from an interior
diagonal that happens to connect two boundary vertices.

## Formalization and proof strategy

Building directly on `MonskyEdgeMultiplicityAtMostTwo` (`cross2`,
`Nondegenerate`, `TriInt`, `exists_common_interior_point`): that file shows
two triangles sharing a full edge `(A,B)` with apexes on the *same side* of
line `AB` have overlapping interiors (hence at most one of them can exist in
an interior-disjoint family unless the *other* apex is on the opposite side).
For a **perimeter** edge — `A,B` both on one fixed side of the square, e.g.
`Ay = By = 0` — every triangle containing that edge must have its apex
strictly *inside* the square (`InSquare`), and a triangle vertex inside the
square automatically lies strictly on the *inward* side of the line through
`A,B` (e.g. strictly `Cy > 0` when `Ay = By = 0`): there is no room "outside"
the square for a second triangle to occupy the opposite side. So *any* two
candidate triangles sharing a perimeter edge automatically have same-signed
`cross2` apex terms (`cross2_same_sign_of_sameSide`), triggering
`exists_common_interior_point` and contradicting interior-disjointness. This
is what forces multiplicity `≤ 1` (`perimeter_edge_card_le_one`); combined
with the edge actually being used by some triangle, multiplicity is exactly
`1` (`perimeter_edge_multiplicity_one`).

Axiom-clean: only `ring`/`nlinarith`-level real algebra plus
`MonskyEdgeMultiplicityAtMostTwo`'s existing (also axiom-clean) local-geometry
lemma; no additional axioms beyond the ambient
`[propext, Classical.choice, Quot.sound]`.
-/
import Propositio.Geometry.Monsky.MonskyEdgeMultiplicityAtMostTwo
import Propositio.Geometry.Monsky.MonskySpernerParity
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

namespace MonskyPerimeterEdgeMultiplicity

open MonskyEdgeMultiplicityAtMostTwo

/-! ## The square, its boundary sides, and the "same side" predicate -/

/-- A point lies in the closed unit square `[0,1]²`. -/
def InSquare (x y : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1

/-- The edge `(A,B)` lies along one fixed side of the unit square: both
endpoints share the same `x = 0` (left), `x = 1` (right), `y = 0` (bottom), or
`y = 1` (top) coordinate. This is the correct formalization of "perimeter
edge" — strictly stronger than "both endpoints are individually on the
boundary" (see the file docstring for why the weaker reading is false, via
the diagonal counterexample). -/
def SameSide (Ax Ay Bx By : ℝ) : Prop :=
  (Ax = 0 ∧ Bx = 0) ∨ (Ax = 1 ∧ Bx = 1) ∨ (Ay = 0 ∧ By = 0) ∨ (Ay = 1 ∧ By = 1)

/-! ## The key sign-forcing lemma -/

/-- **Two candidate apexes of a perimeter edge always give same-signed
`cross2`.** If `A,B` lie on a common side of the square, and `C,D` are each
in the (closed) square and each form a nondegenerate triangle with `A,B`,
then `cross2 A B C` and `cross2 A B D` have the same sign: geometrically,
both `C` and `D` are forced to the unique *inward* side of the line through
`A,B`, since the square has no room on the other side. -/
private lemma cross2_same_sign_of_sameSide
    {Ax Ay Bx By Cx Cy Dx Dy : ℝ}
    (hside : SameSide Ax Ay Bx By)
    (hndC : Nondegenerate Ax Ay Bx By Cx Cy)
    (hndD : Nondegenerate Ax Ay Bx By Dx Dy)
    (hinC : InSquare Cx Cy) (hinD : InSquare Dx Dy) :
    0 < cross2 Ax Ay Bx By Cx Cy * cross2 Ax Ay Bx By Dx Dy := by
  obtain ⟨hCx0, hCx1, hCy0, hCy1⟩ := hinC
  obtain ⟨hDx0, hDx1, hDy0, hDy1⟩ := hinD
  rcases hside with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · -- left side: Ax = 0, Bx = 0
    subst hA; subst hB
    have hcC : cross2 0 Ay 0 By Cx Cy = -(Cx * (By - Ay)) := by unfold cross2; ring
    have hcD : cross2 0 Ay 0 By Dx Dy = -(Dx * (By - Ay)) := by unfold cross2; ring
    unfold Nondegenerate at hndC hndD
    rw [hcC] at hndC; rw [hcD] at hndD; rw [hcC, hcD]
    have hCxne : Cx ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hDxne : Dx ≠ 0 := by intro h; apply hndD; rw [h]; ring
    have hBAne : By - Ay ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hCxpos : 0 < Cx := lt_of_le_of_ne hCx0 hCxne.symm
    have hDxpos : 0 < Dx := lt_of_le_of_ne hDx0 hDxne.symm
    have hsq : 0 < (By - Ay) * (By - Ay) := mul_self_pos.mpr hBAne
    have hprod : 0 < Cx * Dx * ((By - Ay) * (By - Ay)) :=
      mul_pos (mul_pos hCxpos hDxpos) hsq
    have heq : -(Cx * (By - Ay)) * -(Dx * (By - Ay))
        = Cx * Dx * ((By - Ay) * (By - Ay)) := by ring
    rw [heq]; exact hprod
  · -- right side: Ax = 1, Bx = 1
    subst hA; subst hB
    have hcC : cross2 1 Ay 1 By Cx Cy = (1 - Cx) * (By - Ay) := by unfold cross2; ring
    have hcD : cross2 1 Ay 1 By Dx Dy = (1 - Dx) * (By - Ay) := by unfold cross2; ring
    unfold Nondegenerate at hndC hndD
    rw [hcC] at hndC; rw [hcD] at hndD; rw [hcC, hcD]
    have hCxne : Cx ≠ 1 := by intro h; apply hndC; rw [h]; ring
    have hDxne : Dx ≠ 1 := by intro h; apply hndD; rw [h]; ring
    have hBAne : By - Ay ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hCxlt : Cx < 1 := lt_of_le_of_ne hCx1 hCxne
    have hDxlt : Dx < 1 := lt_of_le_of_ne hDx1 hDxne
    have hCxpos : 0 < 1 - Cx := by linarith
    have hDxpos : 0 < 1 - Dx := by linarith
    have hsq : 0 < (By - Ay) * (By - Ay) := mul_self_pos.mpr hBAne
    have hprod : 0 < (1 - Cx) * (1 - Dx) * ((By - Ay) * (By - Ay)) :=
      mul_pos (mul_pos hCxpos hDxpos) hsq
    have heq : (1 - Cx) * (By - Ay) * ((1 - Dx) * (By - Ay))
        = (1 - Cx) * (1 - Dx) * ((By - Ay) * (By - Ay)) := by ring
    rw [heq]; exact hprod
  · -- bottom side: Ay = 0, By = 0
    subst hA; subst hB
    have hcC : cross2 Ax 0 Bx 0 Cx Cy = (Bx - Ax) * Cy := by unfold cross2; ring
    have hcD : cross2 Ax 0 Bx 0 Dx Dy = (Bx - Ax) * Dy := by unfold cross2; ring
    unfold Nondegenerate at hndC hndD
    rw [hcC] at hndC; rw [hcD] at hndD; rw [hcC, hcD]
    have hBAne : Bx - Ax ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hCyne : Cy ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hDyne : Dy ≠ 0 := by intro h; apply hndD; rw [h]; ring
    have hCypos : 0 < Cy := lt_of_le_of_ne hCy0 hCyne.symm
    have hDypos : 0 < Dy := lt_of_le_of_ne hDy0 hDyne.symm
    have hsq : 0 < (Bx - Ax) * (Bx - Ax) := mul_self_pos.mpr hBAne
    have hprod : 0 < (Bx - Ax) * (Bx - Ax) * (Cy * Dy) :=
      mul_pos hsq (mul_pos hCypos hDypos)
    have heq : (Bx - Ax) * Cy * ((Bx - Ax) * Dy)
        = (Bx - Ax) * (Bx - Ax) * (Cy * Dy) := by ring
    rw [heq]; exact hprod
  · -- top side: Ay = 1, By = 1
    subst hA; subst hB
    have hcC : cross2 Ax 1 Bx 1 Cx Cy = (Bx - Ax) * (Cy - 1) := by unfold cross2; ring
    have hcD : cross2 Ax 1 Bx 1 Dx Dy = (Bx - Ax) * (Dy - 1) := by unfold cross2; ring
    unfold Nondegenerate at hndC hndD
    rw [hcC] at hndC; rw [hcD] at hndD; rw [hcC, hcD]
    have hBAne : Bx - Ax ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hCyne : Cy - 1 ≠ 0 := by intro h; apply hndC; rw [h]; ring
    have hDyne : Dy - 1 ≠ 0 := by intro h; apply hndD; rw [h]; ring
    have hCyneg : Cy - 1 < 0 := lt_of_le_of_ne (by linarith) hCyne
    have hDyneg : Dy - 1 < 0 := lt_of_le_of_ne (by linarith) hDyne
    have hsq : 0 < (Bx - Ax) * (Bx - Ax) := mul_self_pos.mpr hBAne
    have hCD : 0 < (Cy - 1) * (Dy - 1) := mul_pos_of_neg_of_neg hCyneg hDyneg
    have hprod : 0 < (Bx - Ax) * (Bx - Ax) * ((Cy - 1) * (Dy - 1)) :=
      mul_pos hsq hCD
    have heq : (Bx - Ax) * (Cy - 1) * ((Bx - Ax) * (Dy - 1))
        = (Bx - Ax) * (Bx - Ax) * ((Cy - 1) * (Dy - 1)) := by ring
    rw [heq]; exact hprod

/-! ## The geometric core theorem: at most one triangle on a perimeter edge -/

/-- **A perimeter edge of a unit-square triangulation belongs to at most one
triangle.** `Ax,Ay,Bx,By` are the (fixed) coordinates of the shared edge's
endpoints, lying along a common side of the square (`hside`); `Cx t, Cy t`
give the third vertex ("apex") of each candidate triangle `t : T` sharing
that edge, each forming a nondegenerate triangle with `A,B` (`hnd`) and lying
in the closed square (`hin`); `hdisj` is the standard triangulation axiom
that distinct triangles have disjoint (open) interiors. Then there is at most
one such triangle. -/
theorem perimeter_edge_card_le_one
    {T : Type*} [Fintype T]
    (Ax Ay Bx By : ℝ) (Cx Cy : T → ℝ)
    (hside : SameSide Ax Ay Bx By)
    (hnd : ∀ t, Nondegenerate Ax Ay Bx By (Cx t) (Cy t))
    (hin : ∀ t, InSquare (Cx t) (Cy t))
    (hdisj : ∀ t₁ t₂ : T, t₁ ≠ t₂ →
      ∀ Px Py, ¬ (TriInt Ax Ay Bx By (Cx t₁) (Cy t₁) Px Py ∧
                   TriInt Ax Ay Bx By (Cx t₂) (Cy t₂) Px Py)) :
    Fintype.card T ≤ 1 := by
  by_contra hcontra
  push_neg at hcontra
  have h2 : 1 < (Finset.univ : Finset T).card := by
    rw [Finset.card_univ]; omega
  obtain ⟨t1, -, t2, -, ht12⟩ := Finset.one_lt_card.mp h2
  have hsign := cross2_same_sign_of_sameSide hside (hnd t1) (hnd t2) (hin t1) (hin t2)
  obtain ⟨Px, Py, h1, h2'⟩ :=
    exists_common_interior_point Ax Ay Bx By (Cx t1) (Cy t1) (Cx t2) (Cy t2)
      (hnd t1) (hnd t2) hsign
  exact hdisj t1 t2 ht12 Px Py ⟨h1, h2'⟩

/-! ## Bridging to `MonskySpernerParity.mult` / `MonskyThreeColorDoors.triEdges` -/

/-- The perimeter edge `s(A,B)` has `MonskySpernerParity` multiplicity at
most `1` in an incidence structure built from `MonskyThreeColorDoors.triEdges
A B (apex t)` — i.e. every candidate triangle `t : T` is presented with `A,B`
as its first two listed vertices and `apex t` as its third — under the same
geometric hypotheses as `perimeter_edge_card_le_one`. -/
theorem perimeter_edge_multiplicity_le_one
    {V T : Type*} [DecidableEq V] [Fintype T]
    (coord : V → ℝ × ℝ) (A B : V) (apex : T → V)
    (inc : T → Finset (Sym2 V))
    (hinc : ∀ t, inc t = MonskyThreeColorDoors.triEdges A B (apex t))
    (hside : SameSide (coord A).1 (coord A).2 (coord B).1 (coord B).2)
    (hnd : ∀ t, Nondegenerate
             (coord A).1 (coord A).2 (coord B).1 (coord B).2
             (coord (apex t)).1 (coord (apex t)).2)
    (hin : ∀ t, InSquare (coord (apex t)).1 (coord (apex t)).2)
    (hdisj : ∀ t₁ t₂ : T, t₁ ≠ t₂ →
      ∀ Px Py, ¬ (TriInt
                    (coord A).1 (coord A).2 (coord B).1 (coord B).2
                    (coord (apex t₁)).1 (coord (apex t₁)).2 Px Py ∧
                  TriInt
                    (coord A).1 (coord A).2 (coord B).1 (coord B).2
                    (coord (apex t₂)).1 (coord (apex t₂)).2 Px Py)) :
    MonskySpernerParity.mult inc (s(A, B)) ≤ 1 := by
  have hmem : ∀ t, s(A, B) ∈ inc t := by
    intro t
    rw [hinc t]
    unfold MonskyThreeColorDoors.triEdges
    simp
  have hcard : Fintype.card T ≤ 1 :=
    perimeter_edge_card_le_one (coord A).1 (coord A).2 (coord B).1 (coord B).2
      (fun t => (coord (apex t)).1) (fun t => (coord (apex t)).2) hside hnd hin hdisj
  rw [MonskySpernerParity.mult_apply]
  have hfilt : (Finset.univ.filter (fun t => s(A, B) ∈ inc t)) = (Finset.univ : Finset T) :=
    Finset.filter_true_of_mem (fun t _ => hmem t)
  rw [hfilt, Finset.card_univ]
  exact hcard

/-- **Perimeter edge multiplicity is exactly `1`.** Same hypotheses as
`perimeter_edge_multiplicity_le_one`, plus `Nonempty T` (the edge is actually
used by at least one triangle — necessary, since an unused edge trivially has
multiplicity `0`). This is sub-theorem (1) of the `hbdry` reduction scoped by
`docs/kb/failed/2026-07-26__MonskyBoundaryDoorBridge_...json`. -/
theorem perimeter_edge_multiplicity_one
    {V T : Type*} [DecidableEq V] [Fintype T]
    (coord : V → ℝ × ℝ) (A B : V) (apex : T → V)
    (inc : T → Finset (Sym2 V))
    (hinc : ∀ t, inc t = MonskyThreeColorDoors.triEdges A B (apex t))
    (hside : SameSide (coord A).1 (coord A).2 (coord B).1 (coord B).2)
    (hnd : ∀ t, Nondegenerate
             (coord A).1 (coord A).2 (coord B).1 (coord B).2
             (coord (apex t)).1 (coord (apex t)).2)
    (hin : ∀ t, InSquare (coord (apex t)).1 (coord (apex t)).2)
    (hdisj : ∀ t₁ t₂ : T, t₁ ≠ t₂ →
      ∀ Px Py, ¬ (TriInt
                    (coord A).1 (coord A).2 (coord B).1 (coord B).2
                    (coord (apex t₁)).1 (coord (apex t₁)).2 Px Py ∧
                  TriInt
                    (coord A).1 (coord A).2 (coord B).1 (coord B).2
                    (coord (apex t₂)).1 (coord (apex t₂)).2 Px Py))
    (hne : Nonempty T) :
    MonskySpernerParity.mult inc (s(A, B)) = 1 := by
  have hle := perimeter_edge_multiplicity_le_one coord A B apex inc hinc hside hnd hin hdisj
  have hge : 1 ≤ MonskySpernerParity.mult inc (s(A, B)) := by
    rw [MonskySpernerParity.mult_apply]
    have hmem : ∀ t, s(A, B) ∈ inc t := by
      intro t; rw [hinc t]; unfold MonskyThreeColorDoors.triEdges; simp
    have hfilt : (Finset.univ.filter (fun t => s(A, B) ∈ inc t)) = (Finset.univ : Finset T) :=
      Finset.filter_true_of_mem (fun t _ => hmem t)
    rw [hfilt, Finset.card_univ]
    exact Fintype.card_pos_iff.mpr hne
  omega

end MonskyPerimeterEdgeMultiplicity
