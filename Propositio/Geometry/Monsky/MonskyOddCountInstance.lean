/-
# The five-triangle fan with interior and boundary Steiner vertices:
a concrete ODD-count instance of the full Monsky chain

This extends `MonskyDiagonalInstance` (which tested an even count, 2 triangles,
no Steiner vertices) to a genuine ODD-count case with both interior (Q) and
boundary (M) Steiner vertices.

Concrete construction:
  Unit square corners A=(0,0), B=(1,0), C=(1,1), D=(0,1)
  Interior Steiner point Q=(1/2, 1/3)
  Boundary Steiner point M=(1/2, 0) (midpoint of AB)

Five triangles: T1=(Q,A,M), T2=(Q,M,B), T3=(Q,B,C), T4=(Q,C,D), T5=(Q,D,A)

## Architectural note (why the colouring is *derived*, not tabulated)

An earlier draft of this file hand-typed a literal colour table
`vcol : Vert → Fin 3` and *separately* proved `vcol_eq_col` (that the table
agrees with the geometric colouring `MonskyBoundaryOddness.col`).  Panel
review correctly found that the headline theorem's proof never consumed
`vcol_eq_col`: `vc`/`hlocal`/`hmult`/`door` all keyed off the hand-typed
table, so the "geometric certificate" was disconnected decoration and a
wrong colour would have been merely *checked* rather than *impossible*.

This version fixes that at the definitional level: `vcol` is *defined* as
`MonskyBoundaryOddness.col (coord v).1 (coord v).2`.  It is therefore
`col`-derived by construction — `vcol_eq_col` is now `rfl`.  The genuine
content lives in the per-vertex evaluation lemmas `vcol_vA … vcol_vQ`, which
compute `col` at each real coordinate (via the already-proved corner lemmas
for the four corners, and via the two 2-adic-valuation computations
`col_half_zero` / `col_half_third` for the Steiner points M and Q).  These
evaluation lemmas are *load-bearing*: `hlocal` and `rainbow3_T5` cannot be
discharged without them, because `vc` is now built from the noncomputable
`col` and must be reduced to concrete `Fin 3` values before the combinatorial
`decide` can fire.  A wrong Steiner-point colour is now impossible by
construction: `vcol vQ` *is* `col (1/2) (1/3)`, and `hlocal`'s parity would be
false for any other value.

This stress-tests:
(i) Nondegenerate triangles and pairwise interior-disjointness with Steiner
      vertices — proved from the real `coord` values (`triangles_nondegenerate`,
      `triangles_pairwise_interior_disjoint`).
(ii) Explicit edge multiplicities (interior edges used by 2 triangles,
      boundary by 1).
(iii) Boundary door-count parity is odd (CD is the unique *boundary* door
      edge; QD is an *interior* door edge of multiplicity 2 and so does not
      affect the parity).
(iv) Existence of a rainbow triangle (at least one of T1..T5 is 3-coloured).
-/

import Propositio.Geometry.Monsky.MonskySpernerParity
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Propositio.Geometry.Monsky.MonskyBoundaryOddness
import Propositio.Geometry.Monsky.MonskyEdgeMultiplicityAtMostTwo
import Propositio.Geometry.Monsky.MonskyDichromaticLineReal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.RingTheory.Valuation.Basic

namespace MonskyOddCountInstance

open MonskyThreeColorDoors MonskySpernerParity

/-- The six vertices: four corners plus two Steiner points. -/
inductive Vert
  | vA | vB | vC | vD | vM | vQ
  deriving DecidableEq, Repr

open Vert

/-- Real-plane coordinates. -/
noncomputable def coord : Vert → ℝ × ℝ
  | vA => (0, 0)
  | vB => (1, 0)
  | vC => (1, 1)
  | vD => (0, 1)
  | vM => (1/2, 0)
  | vQ => (1/2, 1/3)

/-! ## The colouring is the *geometric* colouring, by definition.

`vcol` is not a hand-typed table: it is literally
`MonskyBoundaryOddness.col` evaluated at the vertex's real coordinates.  So
there is nothing to "check": `vc` (used by `hlocal`/`rainbow3_T5` and passed
to the abstract engine) is `col`-derived by construction. -/
noncomputable def vcol (v : Vert) : Fin 3 :=
  MonskyBoundaryOddness.col (coord v).1 (coord v).2

/-- `vcol` *is* the geometric colouring at each vertex — now definitional
(`rfl`), not a proved-then-ignored side lemma. -/
theorem vcol_eq_col (v : Vert) :
    vcol v = MonskyBoundaryOddness.col (coord v).1 (coord v).2 := rfl

/-! ## The two Steiner-point colour computations

The 2-adic valuation `νR` on `ℝ` (from `MonskyDichromaticLineReal`) is
constructed via `Classical.choose` and hence not `decide`/`norm_num`-computable
directly, but the two facts needed here follow from its *specification*
(`νR_spec`) plus the generic mathlib `Valuation.map_inv` /
`Valuation.val_lt_one_iff` API for valuations on a field (`ℝ` is a
`DivisionRing`), without touching the choice-construction at all. -/

open MonskyDichromaticLineReal in
/-- `1 ≤ νR (1/2)`, from `νR 2 < 1` via the generic valuation-inverse
threshold-flip lemma `Valuation.val_lt_one_iff`. -/
lemma one_le_νR_half : (1 : ΓR) ≤ νR (1 / 2 : ℝ) := by
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hlt : (1 : ΓR) < νR (2 : ℝ)⁻¹ :=
    (Valuation.val_lt_one_iff νR h2ne).mp νR_spec.1
  have heq : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [heq]
  exact hlt.le

open MonskyDichromaticLineReal in
/-- `νR (1/3) = 1`, since `3` is odd (so `νR 3 = 1` by `νR_spec.2`) and
`Valuation.map_inv` transports this through the inverse. -/
lemma νR_third_eq_one : νR (1 / 3 : ℝ) = 1 := by
  have hodd : Odd (3 : ℤ) := ⟨1, by norm_num⟩
  have h3 : νR ((3 : ℤ) : ℝ) = 1 := νR_spec.2 3 hodd
  have hcast : ((3 : ℤ) : ℝ) = (3 : ℝ) := by norm_num
  rw [hcast] at h3
  have hinv : νR (3 : ℝ)⁻¹ = (νR (3 : ℝ))⁻¹ := Valuation.map_inv νR (3 : ℝ)
  have heq : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by norm_num
  rw [heq, hinv, h3]
  norm_num

open MonskyDichromaticLineReal in
/-- `MonskyBoundaryOddness.col (1/2) 0 = 1`, the Steiner boundary point `M`. -/
lemma col_half_zero : MonskyBoundaryOddness.col (1 / 2) 0 = 1 := by
  unfold MonskyBoundaryOddness.col
  simp only [νR.map_zero]
  rw [if_neg (fun h => (not_lt.mpr one_le_νR_half) h.1)]
  rw [if_pos ⟨one_le_νR_half, zero_le'⟩]

open MonskyDichromaticLineReal in
/-- `MonskyBoundaryOddness.col (1/2) (1/3) = 1`, the interior Steiner point `Q`. -/
lemma col_half_third : MonskyBoundaryOddness.col (1 / 2) (1 / 3) = 1 := by
  unfold MonskyBoundaryOddness.col
  rw [if_neg (fun h => (not_lt.mpr one_le_νR_half) h.1)]
  rw [if_pos ⟨one_le_νR_half, by rw [νR_third_eq_one]; exact one_le_νR_half⟩]

/-! ## Per-vertex colour evaluations — the load-bearing content.

Each of these evaluates the geometric `col` at a vertex's real coordinates.
Because `vcol` (and hence `vc`) is *defined* through `col`, these are exactly
the facts `hlocal`/`rainbow3_T5` need in order to reduce the noncomputable
`vc` to concrete `Fin 3` values.  For the corners they reuse the already-proved
corner lemmas; for the Steiner points they consume the two 2-adic
computations above. -/

lemma vcol_vA : vcol vA = 0 := by
  show MonskyBoundaryOddness.col (0 : ℝ) (0 : ℝ) = 0
  exact MonskyBoundaryOddness.col_origin

lemma vcol_vB : vcol vB = 1 := by
  show MonskyBoundaryOddness.col (1 : ℝ) (0 : ℝ) = 1
  exact MonskyBoundaryOddness.col_10

lemma vcol_vC : vcol vC = 1 := by
  show MonskyBoundaryOddness.col (1 : ℝ) (1 : ℝ) = 1
  exact MonskyBoundaryOddness.col_11

lemma vcol_vD : vcol vD = 2 := by
  show MonskyBoundaryOddness.col (0 : ℝ) (1 : ℝ) = 2
  exact MonskyBoundaryOddness.col_01

lemma vcol_vM : vcol vM = 1 := by
  show MonskyBoundaryOddness.col (1 / 2 : ℝ) (0 : ℝ) = 1
  exact col_half_zero

lemma vcol_vQ : vcol vQ = 1 := by
  show MonskyBoundaryOddness.col (1 / 2 : ℝ) (1 / 3 : ℝ) = 1
  exact col_half_third

/-- The five triangles as vertex triples: T1, T2, T3, T4, T5. -/
def triVerts : Fin 5 → Vert × Vert × Vert
  | ⟨0, _⟩ => (vQ, vA, vM)   -- T1
  | ⟨1, _⟩ => (vQ, vM, vB)   -- T2
  | ⟨2, _⟩ => (vQ, vB, vC)   -- T3
  | ⟨3, _⟩ => (vQ, vC, vD)   -- T4
  | ⟨4, _⟩ => (vQ, vD, vA)   -- T5

/-! ## The geometric certificate: nondegeneracy and pairwise
interior-disjointness of the five triangles, from their actual `coord`
values.

We use `MonskyEdgeMultiplicityAtMostTwo`'s `cross2`/`Nondegenerate`/`TriInt`
machinery directly: `Nondegenerate` (nonzero signed area) and `TriInt` (a
real open barycentric interior). These certify that the abstract combinatorial
`triVerts` data is realised by honest, non-overlapping geometric triangles at
the `coord` positions. -/

open MonskyEdgeMultiplicityAtMostTwo in
/-- **All five triangles are nondegenerate.** Each of `T1..T5` has nonzero
signed area (`cross2 ≠ 0`) at the actual `coord` values of its vertices —
`Q=(1/2,1/3)` is not collinear with any of the ten pairs of adjacent boundary
points, since it lies strictly off every one of the boundary lines
`x=0, x=1, y=0, y=1`. Pure rational arithmetic, closed by `norm_num`. -/
theorem triangles_nondegenerate (t : Fin 5) :
    Nondegenerate
      (coord (triVerts t).1).1 (coord (triVerts t).1).2
      (coord (triVerts t).2.1).1 (coord (triVerts t).2.1).2
      (coord (triVerts t).2.2).1 (coord (triVerts t).2.2).2 := by
  fin_cases t <;> simp only [triVerts, coord, Nondegenerate, cross2] <;> norm_num

open MonskyEdgeMultiplicityAtMostTwo in
/-- **The five triangles have pairwise disjoint open interiors.** For any two
distinct indices `i ≠ j`, no real point `(Px,Py)` lies in the open barycentric
interior of both `T_i` and `T_j`. Since all five triangles share the apex `Q`,
a common interior point forces a purely *linear* system in the six barycentric
weights (after substituting the concrete rational `coord` values and
eliminating `Px, Py`), which is infeasible together with the positivity/
sum-to-one constraints — `linarith` finds the certificate directly from the
raw barycentric equations. -/
theorem triangles_pairwise_interior_disjoint (i j : Fin 5) (hij : i ≠ j)
    (Px Py : ℝ) :
    ¬ (TriInt
         (coord (triVerts i).1).1 (coord (triVerts i).1).2
         (coord (triVerts i).2.1).1 (coord (triVerts i).2.1).2
         (coord (triVerts i).2.2).1 (coord (triVerts i).2.2).2 Px Py
       ∧ TriInt
         (coord (triVerts j).1).1 (coord (triVerts j).1).2
         (coord (triVerts j).2.1).1 (coord (triVerts j).2.1).2
         (coord (triVerts j).2.2).1 (coord (triVerts j).2.2).2 Px Py) := by
  fin_cases i <;> fin_cases j <;>
    simp only [triVerts, coord] <;>
    first
      | exact absurd rfl hij
      | (rintro ⟨⟨a, b, c, ha, hb, hc, habc, hx, hy⟩, ⟨a', b', c', ha', hb', hc', habc', hx', hy'⟩⟩
         linarith)

/-- Edge sets for each triangle, via triEdges. -/
noncomputable def inc (t : Fin 5) : Finset (Sym2 Vert) :=
  triEdges (triVerts t).1 (triVerts t).2.1 (triVerts t).2.2

/-- Vertex colours for each triangle, read off the geometric colouring `vcol`
(= `col ∘ coord`). This is what makes the whole instance genuinely tied to the
real 2-adic colouring: `vc` is not a table, it is `col` at the triangle's three
real vertices. -/
noncomputable def vc (t : Fin 5) : Fin 3 × Fin 3 × Fin 3 :=
  (vcol (triVerts t).1, vcol (triVerts t).2.1, vcol (triVerts t).2.2)

/-- **`vc` reduces to concrete colour triples** using the per-vertex `col`
evaluations. This lemma is where the geometry actually enters the
combinatorial parity argument: every entry is a `col`-evaluation, so the
values `(1,0,1), (1,1,1), (1,1,1), (1,1,2), (1,2,0)` are *forced* by the
2-adic colouring, not asserted. -/
theorem vc_val :
    vc 0 = (1, 0, 1) ∧ vc 1 = (1, 1, 1) ∧ vc 2 = (1, 1, 1)
      ∧ vc 3 = (1, 1, 2) ∧ vc 4 = (1, 2, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [vc, triVerts, vcol_vA, vcol_vB, vcol_vC, vcol_vD, vcol_vM, vcol_vQ]

/-- The door set: **every** `{1,2}`-colour edge in the fan, boundary or
interior. With colours `vA=0, vB=1, vC=1, vD=2, vM=1, vQ=1`, the only
`{1,2}`-colour pairs among the ten fan edges are the boundary edge `CD`
(colours `1,2`) and the interior edge `QD` (colours `1,2`).  `door` is a
literal edge set, but it is *validated against the geometry* by `hlocal`
below: since `vc` is `col`-derived, `hlocal`'s per-triangle door-count
identity is false for any door set that does not match the actual
`col`-colours — so proving `hlocal` genuinely checks `door` against the real
colouring rather than against a hand-typed colour table. -/
def door : Finset (Sym2 Vert) := {s(vC, vD), s(vQ, vD)}

/-! ## Edge multiplicities and hmult -/

/-- Every door-edge has multiplicity 1 or 2: `CD` appears only in `T4`
(multiplicity 1, a boundary door), `QD` appears in `T4` and `T5`
(multiplicity 2, an interior door). Purely combinatorial (independent of the
colouring), so closed by `decide`. -/
theorem hmult : ∀ e ∈ door, MonskySpernerParity.mult inc e = 1
    ∨ MonskySpernerParity.mult inc e = 2 := by
  unfold door
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  unfold MonskySpernerParity.mult inc triVerts triEdges
  rcases he with he | he <;> subst he <;> decide

/-! ## `hlocal`: the per-triangle door-count identity.

Here the geometry (`vc = col ∘ coord`) meets the combinatorics (`inc`, `door`):
we first reduce `vc t` to its `col`-forced concrete value via `vc_val`, then
the finite door-count identity is decidable. -/

theorem hlocal : ∀ t : Fin 5,
    (inc t ∩ door).card = doorCount12 (vc t).1 (vc t).2.1 (vc t).2.2 := by
  intro t
  fin_cases t <;>
    (unfold inc door vc triVerts triEdges doorCount12
     simp only [vcol_vA, vcol_vB, vcol_vC, vcol_vD, vcol_vM, vcol_vQ]
     decide)

/-! ## Boundary and door-count parity -/

-- Of the two door edges, only `CD` has multiplicity 1 (the interior edge
-- `QD` has multiplicity 2 and so is excluded from `boundary`).
theorem boundary_eq_door : MonskySpernerParity.boundary inc door = {s(vC, vD)} := by
  unfold MonskySpernerParity.boundary MonskySpernerParity.mult inc door triVerts triEdges
  decide

-- `CD` is the unique boundary door-edge, so the boundary has odd (in fact,
-- exactly one) cardinality.
theorem boundary_card_odd : Odd (MonskySpernerParity.boundary inc door).card := by
  rw [boundary_eq_door]
  decide

/-! ## Rainbow triangles -/

/-- T5 (at index 4) is genuinely 3-coloured: colours `(1,2,0)`, forced by the
`col`-evaluations at `Q,D,A`. -/
theorem rainbow3_T5 : rainbow3 (vc 4).1 (vc 4).2.1 (vc 4).2.2 := by
  rw [vc_val.2.2.2.2]
  decide

/-- Reusing the abstract engine: the door-counting parity identity holds. -/
theorem rainbow_card_parity_instance :
    ((MonskySpernerParity.rainbow inc door).card : ZMod 2)
      = ((MonskySpernerParity.boundary inc door).card : ZMod 2) :=
  MonskySpernerParity.rainbow_card_parity inc door hmult

/-- The engine's `rainbow` set is exactly the genuinely 3-coloured triangles.
Since `vc` is `col`-derived and `hlocal` (which consumes the `col`
evaluations) is its hypothesis, this equality is a statement about the real
geometric colouring, not a hand-typed table. -/
theorem rainbow_eq_threeColored_instance :
    MonskySpernerParity.rainbow inc door
      = Finset.univ.filter (fun t => rainbow3 (vc t).1 (vc t).2.1 (vc t).2.2) :=
  MonskyThreeColorDoors.rainbow_eq_threeColored inc door vc hlocal

/-- **The genuine 3-colour Sperner door-counting conclusion, instantiated on
the geometric colouring.** `vc` is `col ∘ coord`, and `hlocal`/`hmult` are its
premises, so this is Monsky's triangle-side parity identity for the actual
five-triangle fan with its real 2-adic colours. -/
theorem threeColored_card_parity_instance :
    ((Finset.univ.filter
        (fun t => rainbow3 (vc t).1 (vc t).2.1 (vc t).2.2)).card : ZMod 2)
      = ((MonskySpernerParity.boundary inc door).card : ZMod 2) :=
  MonskyThreeColorDoors.threeColored_card_parity inc door vc hlocal hmult

/-- **Headline: at least one of the five triangles is genuinely 3-coloured,
derived from the parity engine itself (not by direct inspection).**
`threeColored_card_parity_instance` gives (rainbow count) ≡ (boundary count)
mod 2; `boundary_card_odd` gives the boundary count is odd, i.e. ≡ 1 mod 2;
so the rainbow count is ≡ 1 mod 2, hence nonzero as a natural number, hence
the filtered Finset is nonempty. This genuinely routes through `hlocal`/
`hmult`/`door` via `threeColored_card_parity_instance` — unlike a version
that picks a witness by direct inspection, this derivation cannot be
satisfied by an empty rainbow set even in principle. -/
theorem exists_rainbow_triangle :
    ∃ t : Fin 5, rainbow3 (vc t).1 (vc t).2.1 (vc t).2.2 := by
  by_contra hempty
  push_neg at hempty
  have hcard0 : (Finset.univ.filter
      (fun t => rainbow3 (vc t).1 (vc t).2.1 (vc t).2.2)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _
    exact hempty t
  have hparity := threeColored_card_parity_instance
  rw [hcard0] at hparity
  obtain ⟨k, hk⟩ := boundary_card_odd
  rw [hk] at hparity
  push_cast at hparity
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2] at hparity
  simp at hparity

end MonskyOddCountInstance
