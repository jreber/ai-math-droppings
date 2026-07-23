/-
# Wiring the abstract dissection boundary to the unit square's four sides:
partial results and a rigorous scope of the remaining planar-topology gap

This file addresses `conj-2026-07-18-010`: closing `dissection_exists_rainbow`'s
`hbdry` hypothesis (`Odd (MonskySpernerParity.boundary (incS S) (doorSet S)).card`)
for an arbitrary `MonskyDissectionHlocal.IsDissection S`, by wiring the abstract
boundary-edge set to `MonskyBoundaryOddness.boundary_doors_odd`'s concrete
four-point-sequence signature.

## What is proved here (genuine, `covers`-consuming bricks)

The clean, honestly closable half of task step (2) — "every boundary edge of `S`
has both endpoints on the perimeter of the unit square" — splits into

1. every boundary edge's endpoints lie **in the closed unit square** (proved here,
   unconditionally, from `IsDissection.covers`); and
2. they lie on the **perimeter** (`x ∈ {0,1} ∨ y ∈ {0,1}`) — NOT proved, and in
   fact **false for general dissections**; see the scope note below.

The load-bearing lemmas here are:

* `triClosed_mem_unitSquare` — every point of any triangle's closed hull lies in
  the unit square (`covers.mpr`); the *converse* half of the covering `iff`, which
  says the triangles do not stick out of the square.
* `vertex{1,2,3}_mem_unitSquare` — hence every triangle vertex is in the square.
* `allEdges_endpoints_mem_sq` — hence both endpoints of every edge occurring in the
  dissection are in the square.
* `boundary_endpoint_mem_unitSquare` — hence **both endpoints of every boundary
  door-edge** `e ∈ MonskySpernerParity.boundary (incS S) (doorSet S)` are in the
  closed unit square. This is a statement directly about the target object of
  `hbdry`, and its proof genuinely consumes `hS.covers` (through the vertex lemmas)
  — not a disconnected certificate.

Every one of these consumes the geometric `IsDissection` hypothesis (specifically
`covers`); none is a standalone bookkeeping fact.

## Scope note: why full general `hbdry` closure is NOT available by this route

The remaining step — "boundary door-edges lie on the perimeter and chain into four
corner-to-corner sequences" — is **false for general (non-edge-to-edge)
dissections**, because `MonskySpernerParity.boundary` is defined on the *literal*
`Sym2`-edges of triangle vertices (`mult inc e = 1`), i.e. it silently assumes the
subdivision is edge-to-edge (simplicial). Concretely, take the unit square split by
the main diagonal `(0,0)–(1,1)` into a lower triangle `A = {(0,0),(1,1),(1,0)}` and
an upper region, and subdivide the upper region with an extra vertex `M = (½,½)` on
the diagonal into `B = {(0,0),M,(0,1)}` and `C = {M,(1,1),(0,1)}`. Then the interior
diagonal is covered by three edges — the full edge `s((0,0),(1,1))` of `A` and the
two half-edges `s((0,0),M)`, `s(M,(1,1))` of `B`, `C` — and each of these three
edges belongs to exactly **one** triangle, so each has `mult = 1`. Interior edges
with `mult = 1` are thus possible, so "`mult inc e = 1` ⟹ on the perimeter" is
false. Monsky's genuine odd equidissections are generally **not** edge-to-edge (they
carry interior vertices producing exactly such T-junctions), so this is not a corner
case that can be assumed away.

Consequences for closing `hbdry` in general:

* The `boundary_doors_odd` four-sides wiring is sound only for **edge-to-edge
  (simplicial)** subdivisions, where `mult = 1` edges are exactly the perimeter
  edges and chain into the four sides. To use it, `IsDissection` would need an
  explicit edge-to-edge hypothesis (each pair of triangles meets in a common vertex,
  a common full edge, or not at all).
* For genuinely general dissections, the classical Aigner–Ziegler / Monsky argument
  counts doors along **maximal boundary segments**, not literal triangle edges — a
  different combinatorial object than `MonskySpernerParity.boundary`, and one whose
  parity identity would have to be re-established. That is a separate multi-session
  development (a planar "maximal-segment" refinement of `MonskySpernerParity`), and
  it is the concrete missing machinery: mathlib has no planar-subdivision /
  outer-face-walk theory to draw on.

So the honest status is: the "endpoints in the square" half of the perimeter step is
closed here in general (below); the "on the perimeter, same side, chained" half is
either (a) an edge-to-edge restriction away, or (b) a maximal-segment reformulation
away — and full unconditional closure by the literal-edge route is *blocked*, not
merely unfinished.

Axiom-clean: only `covers`-application, `Sym2`/`Finset` bookkeeping, and elementary
real inequalities; no `sorry`, no project `axiom`, no `native_decide`.
-/

import Propositio.Geometry.Monsky.MonskyDissectionHlocal
import Propositio.Geometry.Monsky.MonskySpernerParity
import Mathlib.Tactic

namespace MonskyDissectionBoundaryScope

open MonskyDissectionHlocal MonskyThreeColorDoors

/-! ## Every point of a triangle's closed hull is in the unit square -/

/-- The converse half of the covering `iff`: no triangle of a dissection sticks
out of the unit square, so **every** point of any triangle's closed hull lies in
the square.  This genuinely consumes `hS.covers` (its `mpr` direction). -/
lemma triClosed_mem_unitSquare {S : Finset Tri} (hS : IsDissection S)
    {t : Tri} (ht : t ∈ S) {Px Py : ℝ} (h : TriClosedP t Px Py) :
    inUnitSquare Px Py :=
  (hS.covers Px Py).mpr ⟨t, ht, h⟩

/-- The first vertex is in its triangle's closed hull (barycentric `(1,0,0)`). -/
lemma vertex1_triClosed (t : Tri) : TriClosedP t t.1.1 t.1.2 :=
  ⟨1, 0, 0, by norm_num, le_refl 0, le_refl 0, by norm_num, by ring, by ring⟩

/-- The second vertex is in its triangle's closed hull (barycentric `(0,1,0)`). -/
lemma vertex2_triClosed (t : Tri) : TriClosedP t t.2.1.1 t.2.1.2 :=
  ⟨0, 1, 0, le_refl 0, by norm_num, le_refl 0, by norm_num, by ring, by ring⟩

/-- The third vertex is in its triangle's closed hull (barycentric `(0,0,1)`). -/
lemma vertex3_triClosed (t : Tri) : TriClosedP t t.2.2.1 t.2.2.2 :=
  ⟨0, 0, 1, le_refl 0, le_refl 0, by norm_num, by norm_num, by ring, by ring⟩

/-- Every triangle vertex of a dissection lies in the closed unit square. -/
lemma vertex1_mem_unitSquare {S : Finset Tri} (hS : IsDissection S)
    {t : Tri} (ht : t ∈ S) : inUnitSquare t.1.1 t.1.2 :=
  triClosed_mem_unitSquare hS ht (vertex1_triClosed t)

lemma vertex2_mem_unitSquare {S : Finset Tri} (hS : IsDissection S)
    {t : Tri} (ht : t ∈ S) : inUnitSquare t.2.1.1 t.2.1.2 :=
  triClosed_mem_unitSquare hS ht (vertex2_triClosed t)

lemma vertex3_mem_unitSquare {S : Finset Tri} (hS : IsDissection S)
    {t : Tri} (ht : t ∈ S) : inUnitSquare t.2.2.1 t.2.2.2 :=
  triClosed_mem_unitSquare hS ht (vertex3_triClosed t)

/-! ## Both endpoints of every dissection edge are in the unit square -/

/-- If `s(x,y) = s(a,b)` then any property holding at both `a` and `b` holds at
both `x` and `y`. -/
lemma prop_of_edge_eq {x y a b : Pt} (h : s(x, y) = s(a, b))
    (P : Pt → Prop) (ha : P a) (hb : P b) : P x ∧ P y := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨hx ▸ ha, hy ▸ hb⟩
  · exact ⟨hx ▸ hb, hy ▸ ha⟩

/-- Both endpoints of any edge occurring in the dissection lie in the closed unit
square.  Consumes `hS.covers` through the vertex-membership lemmas. -/
lemma allEdges_endpoints_mem_sq {S : Finset Tri} (hS : IsDissection S)
    {x y : Pt} (he : s(x, y) ∈ allEdges S) :
    inUnitSquare x.1 x.2 ∧ inUnitSquare y.1 y.2 := by
  obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp he
  simp only [triEdges, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hv1 : inUnitSquare t.1.1 t.1.2 := vertex1_mem_unitSquare hS ht
  have hv2 : inUnitSquare t.2.1.1 t.2.1.2 := vertex2_mem_unitSquare hS ht
  have hv3 : inUnitSquare t.2.2.1 t.2.2.2 := vertex3_mem_unitSquare hS ht
  -- `P p := inUnitSquare p.1 p.2`; each `t.i` satisfies `P` definitionally.
  rcases hmem with h | h | h
  · exact prop_of_edge_eq h (fun p => inUnitSquare p.1 p.2) hv1 hv2
  · exact prop_of_edge_eq h (fun p => inUnitSquare p.1 p.2) hv2 hv3
  · exact prop_of_edge_eq h (fun p => inUnitSquare p.1 p.2) hv1 hv3

/-! ## The boundary door-edges have endpoints in the unit square -/

/-- The abstract boundary door-edge set is a subset of the dissection's edges. -/
lemma boundary_subset_allEdges (S : Finset Tri) :
    MonskySpernerParity.boundary (incS S) (doorSet S) ⊆ allEdges S := by
  intro e he
  rw [MonskySpernerParity.boundary_apply, Finset.mem_filter] at he
  exact doorSet_subset_allEdges S he.1

/-- **Both endpoints of every boundary door-edge lie in the closed unit square.**

For an arbitrary `IsDissection S`, every edge `e` in the abstract boundary set
`MonskySpernerParity.boundary (incS S) (doorSet S)` — i.e. every `{1,2}`-colour
door-edge of multiplicity exactly one, which is precisely what `hbdry` counts — has
*both* of its endpoints in `[0,1]²`.

This is the "endpoints in the square" half of task step (2) ("boundary edge ⟹ both
endpoints on the perimeter"), closed here in full generality.  Its proof genuinely
consumes `hS.covers` (via the vertex-membership lemmas), so it is a real geometric
consequence of the dissection predicate, not a disconnected certificate.  The
remaining "on the perimeter (`x∈{0,1}∨y∈{0,1}`), same side, chained" half is blocked
for general dissections (see the file's scope note). -/
theorem boundary_endpoint_mem_unitSquare {S : Finset Tri} (hS : IsDissection S)
    {e : Sym2 Pt} (he : e ∈ MonskySpernerParity.boundary (incS S) (doorSet S))
    {p : Pt} (hp : p ∈ e) : inUnitSquare p.1 p.2 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hall : s(x, y) ∈ allEdges S := boundary_subset_allEdges S he
    obtain ⟨hx, hy⟩ := allEdges_endpoints_mem_sq hS hall
    rw [Sym2.mem_iff] at hp
    rcases hp with rfl | rfl
    · exact hx
    · exact hy

/-! ## The perimeter side classification (real-analysis helpers)

These are the "side classifier" the conjecture's engineer-lens calls for: given a
point known to lie on the *perimeter* of the unit square, decide which of the four
sides it lies on.  They are unconditional real facts, reusable by any future
edge-to-edge or maximal-segment closure of the remaining half.  (They do NOT
establish that a boundary door-edge's endpoints ARE on the perimeter — that is the
blocked step — only how to classify such a point once it is known to be there.) -/

/-- On the bottom side (`y = 0`). -/
def onBottom (p : Pt) : Prop := inUnitSquare p.1 p.2 ∧ p.2 = 0
/-- On the right side (`x = 1`). -/
def onRight (p : Pt) : Prop := inUnitSquare p.1 p.2 ∧ p.1 = 1
/-- On the top side (`y = 1`). -/
def onTop (p : Pt) : Prop := inUnitSquare p.1 p.2 ∧ p.2 = 1
/-- On the left side (`x = 0`). -/
def onLeft (p : Pt) : Prop := inUnitSquare p.1 p.2 ∧ p.1 = 0

/-- A perimeter point (a square point with a coordinate pinned to `0` or `1`) lies
on at least one of the four sides.  This is the exhaustiveness of the side
classification. -/
lemma onSide_of_perimeter {p : Pt} (hsq : inUnitSquare p.1 p.2)
    (hbd : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) :
    onBottom p ∨ onRight p ∨ onTop p ∨ onLeft p := by
  rcases hbd with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr ⟨hsq, h⟩))
  · exact Or.inr (Or.inl ⟨hsq, h⟩)
  · exact Or.inl ⟨hsq, h⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hsq, h⟩))

/-- The four corners are each on two sides, consistently with
`MonskyBoundaryOddness`'s corner convention.  (Sanity: the classification is
non-degenerate at the corners.) -/
lemma origin_onBottom : onBottom ((0 : ℝ), (0 : ℝ)) :=
  ⟨⟨le_refl 0, by norm_num, le_refl 0, by norm_num⟩, rfl⟩

lemma origin_onLeft : onLeft ((0 : ℝ), (0 : ℝ)) :=
  ⟨⟨le_refl 0, by norm_num, le_refl 0, by norm_num⟩, rfl⟩

end MonskyDissectionBoundaryScope
