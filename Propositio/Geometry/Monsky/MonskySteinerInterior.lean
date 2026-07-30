/-
# Interior Steiner vertices do not affect the perimeter (boundary-door) structure

This is sub-theorem **(2)** of the three concrete geometric bricks scoped by
`docs/kb/failed/2026-07-26__MonskyBoundaryDoorBridge_conj-2026-07-19-002_hbdry_via_direct_perime.json`
for discharging the `hbdry` hypothesis of
`MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`, building directly on
sub-theorem (1), `MonskyPerimeterEdgeMultiplicity.perimeter_edge_multiplicity_one`
(now promoted to `Propositio.Geometry.Monsky.MonskyPerimeterEdgeMultiplicity`).

## What "Steiner vertex" means here, and the two claims

A genuine triangulation of `[0,1]²` (Monsky's setting) has, in general, extra
*interior* vertices beyond the four corners and whatever points subdivide the
four sides — the classical "Steiner points" of the dissection. We formalize
an interior Steiner vertex as a point strictly inside the square, on none of
the four sides:

  `Steiner x y := 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1`

(deliberately the *strict* complement of `MonskyPerimeterEdgeMultiplicity.
InSquare`, which is the closed, non-strict square membership used by sub-
theorem (1)'s apex hypothesis `hin`). The informal claim scoped by the
failed-attempt record splits into exactly two precise statements, both proved
below:

1. **"Steiner vertices don't create new perimeter edges."** A perimeter edge
   is, by sub-theorem (1)'s `SameSide` predicate, a pair of points sharing a
   *fixed* boundary coordinate (`x = 0`, `x = 1`, `y = 0`, or `y = 1`). A
   Steiner point satisfies *none* of these four equalities (all its
   coordinates are strict, open-interval inequalities), so it can never be
   *either* endpoint of a `SameSide` pair, regardless of what the other point
   is (`steiner_not_sameSide_left`, `steiner_not_sameSide_right`). In
   particular, the two endpoints of a genuine perimeter edge are themselves
   never Steiner vertices — this is the first component of the main theorem
   below.

2. **"Steiner vertices don't change perimeter-edge multiplicities."** Sub-
   theorem (1)'s multiplicity-one conclusion only needs each candidate
   triangle's apex to lie in the *closed* square (`InSquare`, hypothesis
   `hin`) — it does not care whether that apex sits on the boundary or
   strictly in the interior. Since `Steiner` is strictly stronger than
   `InSquare` (`steiner_in_square`), allowing some (or all) apexes of the
   triangles sharing a perimeter edge to be genuine interior Steiner points,
   rather than requiring them to be boundary points, changes nothing: sub-
   theorem (1) applies verbatim and still forces multiplicity exactly `1`.
   This is the second component of the main theorem.

## Main theorem

`steiner_interior_does_not_affect_boundary` packages both components: under
the same hypotheses as `perimeter_edge_multiplicity_one` except that the apex
hypothesis is *weakened* from `∀ t, InSquare (apex t)` to
`∀ t, Steiner (apex t) ∨ InSquare (apex t)` (i.e. triangles on the perimeter
edge may have either an interior Steiner apex or an ordinary in-square apex),
the conclusion is threefold: the edge's own endpoints `A`, `B` are not Steiner
vertices, and the multiplicity is still exactly `1`.

Axiom-clean: only the corner-case real inequalities (`linarith`) plus
`MonskyPerimeterEdgeMultiplicity.perimeter_edge_multiplicity_one` (itself
axiom-clean); no additional axioms beyond the ambient
`[propext, Classical.choice, Quot.sound]`.
-/
import Propositio.Geometry.Monsky.MonskyPerimeterEdgeMultiplicity
import Mathlib.Data.Sym.Sym2

namespace MonskySteinerInterior

/-! ## Interior Steiner points -/

/-- An interior **Steiner vertex**: a point strictly inside the unit square,
lying on *none* of its four sides. This is the strict complement of
`MonskyPerimeterEdgeMultiplicity.InSquare`'s boundary-inclusive membership. -/
def Steiner (x y : ℝ) : Prop := 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1

/-- A Steiner point is (weakly) in the closed square: `Steiner` is strictly
stronger than `InSquare`. -/
theorem steiner_in_square {x y : ℝ} (h : Steiner x y) :
    MonskyPerimeterEdgeMultiplicity.InSquare x y := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := h
  exact ⟨le_of_lt hx0, le_of_lt hx1, le_of_lt hy0, le_of_lt hy1⟩

/-! ## Steiner vertices cannot be endpoints of a perimeter edge -/

/-- **A Steiner vertex is never the first endpoint of a `SameSide` pair.**
None of the four boundary-coordinate equalities defining `SameSide` can hold
for a point with all-strict interior inequalities, whatever the other
endpoint's coordinates are. -/
theorem steiner_not_sameSide_left {Ax Ay Bx By : ℝ} (h : Steiner Ax Ay) :
    ¬ MonskyPerimeterEdgeMultiplicity.SameSide Ax Ay Bx By := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := h
  unfold MonskyPerimeterEdgeMultiplicity.SameSide
  rintro (⟨hA, -⟩ | ⟨hA, -⟩ | ⟨hA, -⟩ | ⟨hA, -⟩) <;> linarith

/-- **A Steiner vertex is never the second endpoint of a `SameSide` pair**
either, by the symmetric argument. -/
theorem steiner_not_sameSide_right {Ax Ay Bx By : ℝ} (h : Steiner Bx By) :
    ¬ MonskyPerimeterEdgeMultiplicity.SameSide Ax Ay Bx By := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := h
  unfold MonskyPerimeterEdgeMultiplicity.SameSide
  rintro (⟨-, hB⟩ | ⟨-, hB⟩ | ⟨-, hB⟩ | ⟨-, hB⟩) <;> linarith

/-- **No edge with a Steiner endpoint is a perimeter edge**, packaged at the
abstract-vertex level (`coord : V → ℝ × ℝ`): if `u`'s coordinates are a
Steiner point, the pair `(u, v)` never satisfies `SameSide`, for any `v`.
This is the precise sense in which "interior Steiner vertices don't create
new perimeter edges." -/
theorem steiner_edge_not_perimeter
    {V : Type*} (coord : V → ℝ × ℝ) (u v : V)
    (hu : Steiner (coord u).1 (coord u).2) :
    ¬ MonskyPerimeterEdgeMultiplicity.SameSide
        (coord u).1 (coord u).2 (coord v).1 (coord v).2 :=
  steiner_not_sameSide_left hu

/-! ## Main theorem: Steiner apexes neither create new perimeter edges nor
change perimeter-edge multiplicities -/

/-- **Interior Steiner vertices do not affect the perimeter.** Same setup as
`MonskyPerimeterEdgeMultiplicity.perimeter_edge_multiplicity_one`, except the
apex hypothesis is weakened to allow each candidate triangle's apex to be
*either* a genuine interior Steiner vertex *or* an ordinary (boundary-
inclusive) in-square point (`hapex`). The conclusion is threefold:

* the perimeter edge's own endpoints `A`, `B` are never Steiner vertices
  (Steiner vertices create no new perimeter edges), and
* the edge's multiplicity is still exactly `1` (Steiner apexes do not change
  perimeter-edge multiplicities), obtained by reusing sub-theorem (1)
  unchanged after weakening `hapex` back down to plain `InSquare` via
  `steiner_in_square`. -/
theorem steiner_interior_does_not_affect_boundary
    {V T : Type*} [DecidableEq V] [Fintype T]
    (coord : V → ℝ × ℝ) (A B : V) (apex : T → V)
    (inc : T → Finset (Sym2 V))
    (hinc : ∀ t, inc t = MonskyThreeColorDoors.triEdges A B (apex t))
    (hside : MonskyPerimeterEdgeMultiplicity.SameSide
               (coord A).1 (coord A).2 (coord B).1 (coord B).2)
    (hnd : ∀ t, MonskyEdgeMultiplicityAtMostTwo.Nondegenerate
             (coord A).1 (coord A).2 (coord B).1 (coord B).2
             (coord (apex t)).1 (coord (apex t)).2)
    (hapex : ∀ t, Steiner (coord (apex t)).1 (coord (apex t)).2
               ∨ MonskyPerimeterEdgeMultiplicity.InSquare
                   (coord (apex t)).1 (coord (apex t)).2)
    (hdisj : ∀ t₁ t₂ : T, t₁ ≠ t₂ →
      ∀ Px Py, ¬ (MonskyEdgeMultiplicityAtMostTwo.TriInt
                    (coord A).1 (coord A).2 (coord B).1 (coord B).2
                    (coord (apex t₁)).1 (coord (apex t₁)).2 Px Py ∧
                  MonskyEdgeMultiplicityAtMostTwo.TriInt
                    (coord A).1 (coord A).2 (coord B).1 (coord B).2
                    (coord (apex t₂)).1 (coord (apex t₂)).2 Px Py))
    (hne : Nonempty T) :
    ¬ Steiner (coord A).1 (coord A).2 ∧
    ¬ Steiner (coord B).1 (coord B).2 ∧
    MonskySpernerParity.mult inc (s(A, B)) = 1 := by
  refine ⟨fun hA => steiner_not_sameSide_left hA hside,
    fun hB => steiner_not_sameSide_right hB hside, ?_⟩
  have hin : ∀ t, MonskyPerimeterEdgeMultiplicity.InSquare
                     (coord (apex t)).1 (coord (apex t)).2 := by
    intro t
    rcases hapex t with h | h
    · exact steiner_in_square h
    · exact h
  exact MonskyPerimeterEdgeMultiplicity.perimeter_edge_multiplicity_one
    coord A B apex inc hinc hside hnd hin hdisj hne

end MonskySteinerInterior
