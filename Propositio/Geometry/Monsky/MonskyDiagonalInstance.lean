/-
# The diagonal split of the unit square: a concrete instance of the full
Sperner/3-colour-door chain

`MonskySpernerParity.rainbow_card_parity`, `MonskyThreeColorDoors.
threeColored_card_parity`, and `MonskyBoundaryOddness.col`/corner-lemmas are
each proved abstractly or for a general triangulation. This file ties them
together on the *simplest possible* concrete geometric data: the unit
square `[0,1]²` split into two triangles by the diagonal `(0,0)-(1,1)`.

  triangle `false` = `{(0,0), (1,0), (1,1)}`   (lower-right)
  triangle `true`  = `{(0,0), (1,1), (0,1)}`   (upper-left)

This is a **validation/template** instance, not progress on the genuine
(odd-triangulation) Monsky obstruction: `2` is an *even* split, so it lies
outside the domain where a rainbow triangle is actually forced to exist by
`hbdry`'s odd-boundary hypothesis being unreachable (a genuine `hbdry` proof
needs `MonskyBoundaryOddness.boundary_doors_odd`, which is about the whole
boundary of an arbitrary triangulation, not just this 2-triangle instance).
Its value is exercising every piece of the pipeline — `MonskyThreeColorDoors.
triEdges`, `doorCount12`, `rainbow3`, `rainbow_eq_threeColored`,
`threeColored_card_parity`, and `MonskySpernerParity.mult`/`boundary`/
`rainbow`/`rainbow_card_parity` — against real point data and the *already
proved* corner colours (`MonskyBoundaryOddness.col_origin`, `col_10`,
`col_11`, `col_01`), confirming the whole machinery composes with no
type-mismatch or off-by-one surprise, and giving a genuine base-case
template for a future ear-decomposition triangulation formalization.

## The vertex type

To make `inc`/`door`/`mult` genuinely finite, decidable data (rather than
opaque predicates ranging over all of `ℝ × ℝ`), we work over the explicit
4-element vertex type `Vert` (the square's four corners), with `coord`
mapping each vertex to its real-plane coordinates and `vcol` its colour.
`vcol` is a *computable* literal assignment matching the values forced by
`MonskyBoundaryOddness`'s corner lemmas — `vcol_eq_col` below proves the two
agree, tying this concrete instance back to the actual geometric colouring.

`door` is defined here directly as the single top edge `s((1,1),(0,1))` —
the only edge that actually appears among the two triangles' six
(with multiplicity) edges and carries the `{1,2}` colour pattern. (Note:
this is deliberately *not* obtained via `MonskyThreeColorDoors.
triEdgeInter_card`'s global `hdoor` hypothesis, which quantifies over *all*
pairs of the vertex type — on our 4-point `Vert` that would force the
"phantom" non-adjacent pair `(1,0)-(0,1)` into `door` too, since it also
has colour pattern `{1,2}`, despite never being an edge of either triangle.
Scoping `door` to the edges actually realised by `inc` — exactly as the
real geometric triangulation argument does — is what recovers `door` as the
single top edge; the per-triangle door-count identity `hlocal` is verified
directly by computation below instead.)
-/

import Propositio.Geometry.Monsky.MonskySpernerParity
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Propositio.Geometry.Monsky.MonskyBoundaryOddness
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

namespace MonskyDiagonalInstance

open MonskyThreeColorDoors MonskySpernerParity

/-- The four corners of the unit square, as an explicit finite vertex type. -/
inductive Vert
  | v00 | v10 | v11 | v01
  deriving DecidableEq, Repr

open Vert

/-- The real-plane coordinates of each vertex. -/
def coord : Vert → ℝ × ℝ
  | v00 => (0, 0)
  | v10 => (1, 0)
  | v11 => (1, 1)
  | v01 => (0, 1)

/-- The 3-colouring of each vertex (a computable literal assignment,
matching the values forced by `MonskyBoundaryOddness`'s corner lemmas — see
`vcol_eq_col`). -/
def vcol : Vert → Fin 3
  | v00 => 0
  | v10 => 1
  | v11 => 1
  | v01 => 2

/-- **`vcol` genuinely computes `MonskyBoundaryOddness.col`** at each
vertex's real coordinates: this ties the concrete literal colouring back to
the actual geometric 2-adic colouring via the already-proved corner
lemmas. -/
theorem vcol_eq_col (v : Vert) :
    vcol v = MonskyBoundaryOddness.col (coord v).1 (coord v).2 := by
  cases v
  · exact MonskyBoundaryOddness.col_origin.symm
  · exact MonskyBoundaryOddness.col_10.symm
  · exact MonskyBoundaryOddness.col_11.symm
  · exact MonskyBoundaryOddness.col_01.symm

/-- The two triangles of the diagonal split `(0,0)-(1,1)`: `false` is the
lower-right triangle `{(0,0),(1,0),(1,1)}`, `true` the upper-left triangle
`{(0,0),(1,1),(0,1)}`. -/
def triVerts : Bool → Vert × Vert × Vert
  | false => (v00, v10, v11)
  | true => (v00, v11, v01)

/-- Each triangle's edge set, via `MonskyThreeColorDoors.triEdges`. -/
def inc (t : Bool) : Finset (Sym2 Vert) :=
  triEdges (triVerts t).1 (triVerts t).2.1 (triVerts t).2.2

/-- The three vertex-colours of each triangle, as required by
`MonskyThreeColorDoors.rainbow_eq_threeColored` / `threeColored_card_parity`. -/
def vc (t : Bool) : Fin 3 × Fin 3 × Fin 3 :=
  (vcol (triVerts t).1, vcol (triVerts t).2.1, vcol (triVerts t).2.2)

/-- The door set for this instantiation: exactly the top edge
`s((1,1),(0,1))`, the only edge (among the five edges actually realised
across both triangles) whose endpoints carry colours `{1,2}`. -/
def door : Finset (Sym2 Vert) := {s(v11, v01)}

/-! ## (i) Multiplicities: the diagonal has multiplicity 2, every other
realised edge has multiplicity 1. -/

theorem mult_diagonal : MonskySpernerParity.mult inc (s(v00, v11)) = 2 := by decide

theorem mult_bottom : MonskySpernerParity.mult inc (s(v00, v10)) = 1 := by decide

theorem mult_right : MonskySpernerParity.mult inc (s(v10, v11)) = 1 := by decide

theorem mult_top : MonskySpernerParity.mult inc (s(v11, v01)) = 1 := by decide

theorem mult_left : MonskySpernerParity.mult inc (s(v00, v01)) = 1 := by decide

/-! ## `hmult`: every door-edge has multiplicity 1 or 2 (the hypothesis
needed for `rainbow_card_parity`/`threeColored_card_parity`). -/

theorem hmult : ∀ e ∈ door, MonskySpernerParity.mult inc e = 1
    ∨ MonskySpernerParity.mult inc e = 2 := by decide

/-! ## `hlocal`: the per-triangle door-count identity, verified directly by
computation (not via `triEdgeInter_card`'s global `hdoor` — see the file
docstring). -/

theorem hlocal : ∀ t : Bool,
    (inc t ∩ door).card = doorCount12 (vc t).1 (vc t).2.1 (vc t).2.2 := by decide

/-! ## (ii)-(iii) `door` itself is the boundary: card 1, odd. -/

theorem boundary_eq_door : MonskySpernerParity.boundary inc door = door := by decide

theorem boundary_card_odd : Odd (MonskySpernerParity.boundary inc door).card := by decide

/-! ## (iv) The rainbow set is exactly `{true}`: one rainbow triangle,
matching `rainbow_card_parity`'s mod-2 prediction `1 ≡ 1`. -/

theorem rainbow_eq_true : MonskySpernerParity.rainbow inc door = {true} := by decide

/-- Reusing the abstract engine directly: the door-counting parity identity
holds for this instance (a genuine, non-vacuous check that
`rainbow_card_parity`'s general statement composes with concrete data). -/
theorem rainbow_card_parity_instance :
    ((MonskySpernerParity.rainbow inc door).card : ZMod 2)
      = ((MonskySpernerParity.boundary inc door).card : ZMod 2) :=
  MonskySpernerParity.rainbow_card_parity inc door hmult

/-! ## Reusing `MonskyThreeColorDoors`'s 3-colour engine on the same data. -/

/-- The engine's `rainbow` set is exactly the genuinely 3-coloured
triangles, for this concrete instance. -/
theorem rainbow_eq_threeColored_instance :
    MonskySpernerParity.rainbow inc door
      = Finset.univ.filter (fun t => rainbow3 (vc t).1 (vc t).2.1 (vc t).2.2) :=
  MonskyThreeColorDoors.rainbow_eq_threeColored inc door vc hlocal

/-- The genuine 3-colour Sperner door-counting conclusion, instantiated. -/
theorem threeColored_card_parity_instance :
    ((Finset.univ.filter
        (fun t => rainbow3 (vc t).1 (vc t).2.1 (vc t).2.2)).card : ZMod 2)
      = ((MonskySpernerParity.boundary inc door).card : ZMod 2) :=
  MonskyThreeColorDoors.threeColored_card_parity inc door vc hlocal hmult

/-! ## (v) The rainbow triangle (`true`, vertices `(0,0),(1,1),(0,1)`,
colours `0,1,2`) is genuinely 3-coloured. -/

theorem rainbow3_true : rainbow3 (vc true).1 (vc true).2.1 (vc true).2.2 := by decide

/-- `false` is *not* rainbow: its two shared-diagonal-plus-bottom colours
`0, 1, 1` repeat. -/
theorem not_rainbow3_false : ¬ rainbow3 (vc false).1 (vc false).2.1 (vc false).2.2 := by
  decide

end MonskyDiagonalInstance
