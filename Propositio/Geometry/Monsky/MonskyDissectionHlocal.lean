/-
# A `Finset`-of-triangles dissection predicate, and the general discharge of
`hlocal` (and `hmult`) for Monsky's theorem

This file closes the last *per-instance-only* hypothesis of the abstract
door-counting engine `MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`
— its `hlocal` premise — **in general**, for an arbitrary dissection of the
plane presented as a `Finset` of triangles.  It also discharges `hmult` in
general from the same data.  Only `hbdry` (the boundary door-count being odd)
is left as an explicit input; that is the genuinely global/geometric ingredient
supplied concretely by `MonskyBoundaryOddness.boundary_doors_odd`, and wiring an
abstract `Finset`-boundary to the unit square's four sides is out of scope here
(see the scope note at the end).

## The reframing (per `conj-2026-07-18-008`)

Rather than a from-scratch inductive `Triangulation` type, a dissection is a
**predicate on a `Finset` of triangles** (`IsDissection`), each triangle a
triple of real-plane points.  The colouring is *col-derived by construction*
(`vcolS t := colPt` of the triangle's three vertices, `colPt p := col p.1 p.2`),
never a hand-typed table — this is the exact architecture that finally closed
the single 5-triangle instance (`MonskyOddCountInstance`), avoiding the
"geometric certificate is disconnected decoration" bug that recurred there.

## Why `hlocal` is *not* the hard part once framed correctly

`hlocal` says: for each triangle `t`, the number of its edges lying in the
`{1,2}`-door set equals `doorCount12` of its three vertex colours.  This is
exactly `MonskyThreeColorDoors.triEdgeInter_card` (a per-edge colour count),
whose only real hypotheses are:

* the three vertices are pairwise distinct — supplied here in general by
  `nondeg_ne_v12/23/13`, derived from `Nondegenerate` (`cross2 ≠ 0`); and
* the door set genuinely characterises `{1,2}`-colour edges — supplied here by
  `doorSet` being *defined* as the `{1,2}`-colour filter of the dissection's
  own edge set (`door12Bool`, a `Sym2.lift` of the symmetric `pairIs12` on
  `colPt`), so the per-edge characterisation `mem_doorSet_of_edge` holds for
  every edge that actually occurs.

Since both are general, `dissection_hlocal` holds for *every* `IsDissection`.

## Why `hmult` also follows generally

`MonskyHmultWiring.mult_le_two` already gives `mult ≤ 2` for any finite family
of pairwise-interior-disjoint nondegenerate triangles — exactly the content of
`IsDissection`.  Combined with the trivial `mult ≥ 1` for door edges (they lie
in the family's edge set), `dissection_hmult` gives `mult ∈ {1,2}` in general.

## Load-bearing check

`dissection_exists_rainbow` = `exists_rainbow_of_odd_boundary` applied to
`incS`/`doorSet`/`vcolS` with `dissection_hlocal`/`dissection_hmult`.  Every one
of these is *derived from the geometry* (`colPt`/`cross2`/`TriInt`/`triEdges`):
there is no hand-typed colour or door table anywhere.  `dissection_hlocal`'s
proof consumes `hS.nondeg` (through the distinctness lemmas) and the geometric
`doorSet`; `dissection_hmult`'s proof consumes `hS.nondeg` *and*
`hS.interiorDisjoint` (through `mult_le_two`).  So the geometric hypotheses are
genuine premises, not siblings proved and ignored.

Axiom-clean: only elementary real algebra (`ring`), finite `Finset`/`Sym2`
bookkeeping, and the already-axiom-clean imported Monsky machinery; no `sorry`,
no project `axiom`, no `native_decide`.
-/

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Propositio.Geometry.Monsky.MonskyEdgeMultiplicityAtMostTwo
import Propositio.Geometry.Monsky.MonskyHmultWiring
import Propositio.Geometry.Monsky.MonskyBoundaryOddness
import Propositio.Geometry.Monsky.MonskySpernerParity

namespace MonskyDissectionHlocal

open MonskyThreeColorDoors

/-! ## Basic types: points and triangles as tuples -/

/-- A point in the real plane. -/
abbrev Pt := ℝ × ℝ

/-- A triangle as an ordered triple of points. -/
abbrev Tri := Pt × Pt × Pt

/-- The geometric 2-adic colouring, evaluated at a point.  This is
`MonskyBoundaryOddness.col` composed with the coordinate projections — the
*same* col-derived colouring used by the closed 5-triangle instance, never a
hand-typed table. -/
noncomputable def colPt (p : Pt) : Fin 3 := MonskyBoundaryOddness.col p.1 p.2

/-- Nondegeneracy of a triangle (nonzero signed area of its three vertices). -/
def Nondeg (t : Tri) : Prop :=
  MonskyEdgeMultiplicityAtMostTwo.Nondegenerate
    t.1.1 t.1.2 t.2.1.1 t.2.1.2 t.2.2.1 t.2.2.2

/-- The open barycentric interior of a triangle at a point. -/
def TriIntP (t : Tri) (Px Py : ℝ) : Prop :=
  MonskyEdgeMultiplicityAtMostTwo.TriInt
    t.1.1 t.1.2 t.2.1.1 t.2.1.2 t.2.2.1 t.2.2.2 Px Py

/-- The closed barycentric hull of a triangle at a point (non-strict weights). -/
def TriClosedP (t : Tri) (Px Py : ℝ) : Prop :=
  ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
    Px = a * t.1.1 + b * t.2.1.1 + c * t.2.2.1 ∧
    Py = a * t.1.2 + b * t.2.1.2 + c * t.2.2.2

/-- Membership in the closed unit square `[0,1]²`. -/
def inUnitSquare (Px Py : ℝ) : Prop := 0 ≤ Px ∧ Px ≤ 1 ∧ 0 ≤ Py ∧ Py ≤ 1

/-! ## The dissection predicate -/

/-- **A dissection of the unit square, as a predicate on a `Finset` of
triangles.**  A finite set `S` of triangles is a dissection when

* every triangle is nondegenerate (`nondeg`);
* distinct triangles have disjoint open interiors (`interiorDisjoint`); and
* the closed triangles exactly cover the unit square (`covers`, an `iff` of
  point-membership).

This is a `Prop` on `Finset Tri` — no from-scratch inductive triangulation
type — exactly the `conj-2026-07-18-008` reframing. -/
structure IsDissection (S : Finset Tri) : Prop where
  /-- Every triangle in the dissection is nondegenerate. -/
  nondeg : ∀ t ∈ S, Nondeg t
  /-- Distinct triangles have disjoint open interiors. -/
  interiorDisjoint : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ →
    ∀ Px Py : ℝ, ¬ (TriIntP t₁ Px Py ∧ TriIntP t₂ Px Py)
  /-- The closed triangles exactly cover the unit square. -/
  covers : ∀ Px Py : ℝ, inUnitSquare Px Py ↔ ∃ t ∈ S, TriClosedP t Px Py

/-! ## Nondegeneracy forces pairwise-distinct vertices -/

lemma nondeg_ne_v12 {t : Tri} (h : Nondeg t) : t.1 ≠ t.2.1 := by
  unfold Nondeg MonskyEdgeMultiplicityAtMostTwo.Nondegenerate at h
  intro he
  apply h
  have h1 : t.1.1 = t.2.1.1 := congrArg Prod.fst he
  have h2 : t.1.2 = t.2.1.2 := congrArg Prod.snd he
  unfold MonskyEdgeMultiplicityAtMostTwo.cross2
  rw [h1, h2]; ring

lemma nondeg_ne_v23 {t : Tri} (h : Nondeg t) : t.2.1 ≠ t.2.2 := by
  unfold Nondeg MonskyEdgeMultiplicityAtMostTwo.Nondegenerate at h
  intro he
  apply h
  have h1 : t.2.1.1 = t.2.2.1 := congrArg Prod.fst he
  have h2 : t.2.1.2 = t.2.2.2 := congrArg Prod.snd he
  unfold MonskyEdgeMultiplicityAtMostTwo.cross2
  rw [h1, h2]; ring

lemma nondeg_ne_v13 {t : Tri} (h : Nondeg t) : t.1 ≠ t.2.2 := by
  unfold Nondeg MonskyEdgeMultiplicityAtMostTwo.Nondegenerate at h
  intro he
  apply h
  have h1 : t.1.1 = t.2.2.1 := congrArg Prod.fst he
  have h2 : t.1.2 = t.2.2.2 := congrArg Prod.snd he
  unfold MonskyEdgeMultiplicityAtMostTwo.cross2
  rw [h1, h2]; ring

/-! ## The col-derived `{1,2}`-door set -/

/-- The `{1,2}`-door predicate on an *unordered* edge, as a `Bool` — the
symmetric `pairIs12` on `colPt` lifted through `Sym2.lift`. -/
noncomputable def door12Bool (p : Sym2 Pt) : Bool :=
  Sym2.lift ⟨fun x y => decide (pairIs12 (colPt x) (colPt y)),
    fun x y => decide_eq_decide.mpr (pairIs12_symm (colPt x) (colPt y))⟩ p

@[simp] lemma door12Bool_mk (x y : Pt) :
    door12Bool s(x, y) = decide (pairIs12 (colPt x) (colPt y)) := rfl

/-- All edges occurring in the dissection. -/
noncomputable def allEdges (S : Finset Tri) : Finset (Sym2 Pt) :=
  S.biUnion (fun t => triEdges t.1 t.2.1 t.2.2)

/-- **The door set**: the `{1,2}`-colour edges among the dissection's edges.
Defined geometrically from `colPt`, so it is genuinely validated against the
2-adic colouring by `hlocal` below — no hand-typed door table. -/
noncomputable def doorSet (S : Finset Tri) : Finset (Sym2 Pt) :=
  (allEdges S).filter (fun e => door12Bool e = true)

lemma mem_doorSet (S : Finset Tri) (e : Sym2 Pt) :
    e ∈ doorSet S ↔ e ∈ allEdges S ∧ door12Bool e = true := by
  unfold doorSet; exact Finset.mem_filter

/-- For an edge that actually occurs in the dissection, membership in the door
set is exactly the `{1,2}`-colour condition on its endpoints. -/
lemma mem_doorSet_of_edge (S : Finset Tri) {x y : Pt}
    (hmem : s(x, y) ∈ allEdges S) :
    s(x, y) ∈ doorSet S ↔ pairIs12 (colPt x) (colPt y) := by
  rw [mem_doorSet]
  constructor
  · rintro ⟨_, hb⟩
    rw [door12Bool_mk] at hb
    exact of_decide_eq_true hb
  · intro hp
    exact ⟨hmem, by rw [door12Bool_mk]; exact decide_eq_true hp⟩

/-! ## The local door-count identity (weakened, per-edge hypotheses)

A version of `MonskyThreeColorDoors.triEdgeInter_card` whose door
characterisation is required only on the *three edges of the triangle in
question* — exactly what the geometric `doorSet` provides.  (The original
`triEdgeInter_card` demands the characterisation for *all* pairs, which a
finite `doorSet` cannot satisfy since it does not contain the whole plane's
`{1,2}`-edges.  The proof is otherwise identical.) -/
lemma triEdgeInter_card_local {V : Type*} [DecidableEq V]
    (col : V → Fin 3) (door : Finset (Sym2 V))
    {a b c : V}
    (hab_d : s(a, b) ∈ door ↔ pairIs12 (col a) (col b))
    (hbc_d : s(b, c) ∈ door ↔ pairIs12 (col b) (col c))
    (hac_d : s(a, c) ∈ door ↔ pairIs12 (col a) (col c))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (triEdges a b c ∩ door).card = doorCount12 (col a) (col b) (col c) := by
  classical
  have hfilter : triEdges a b c ∩ door
      = (triEdges a b c).filter (fun e => e ∈ door) := by
    rw [Finset.filter_mem_eq_inter]
  rw [hfilter, Finset.card_filter]
  have e_ab_bc : s(a, b) ≠ s(b, c) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hab h1
    · exact hac h1
  have e_ab_ac : s(a, b) ≠ s(a, c) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact hbc h2
    · exact hac h1
  have e_bc_ac : s(b, c) ≠ s(a, c) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hab h1.symm
    · exact hbc h1
  have hbc_ne : s(b, c) ∉ ({s(a, c)} : Finset (Sym2 V)) :=
    Finset.notMem_singleton.mpr e_bc_ac
  have hab_ne : s(a, b) ∉ ({s(b, c), s(a, c)} : Finset (Sym2 V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨e_ab_bc, e_ab_ac⟩
  unfold triEdges
  rw [Finset.sum_insert hab_ne, Finset.sum_insert hbc_ne, Finset.sum_singleton]
  simp only [hab_d, hbc_d, hac_d, doorCount12]
  omega

/-! ## The engine data for a dissection: `incS`, `vcolS`, and the vertex maps -/

/-- First vertex selector. -/
def v1S (S : Finset Tri) : ↥S → Pt := fun t => t.val.1
/-- Second vertex selector. -/
def v2S (S : Finset Tri) : ↥S → Pt := fun t => t.val.2.1
/-- Third vertex selector. -/
def v3S (S : Finset Tri) : ↥S → Pt := fun t => t.val.2.2

/-- Triangle-incidence: the three edges of each triangle in the dissection. -/
noncomputable def incS (S : Finset Tri) : ↥S → Finset (Sym2 Pt) :=
  fun t => triEdges t.val.1 t.val.2.1 t.val.2.2

/-- Per-triangle vertex colours, **col-derived** (each entry is `colPt` at a
real vertex), so the whole engine keys off the actual 2-adic colouring. -/
noncomputable def vcolS (S : Finset Tri) : ↥S → Fin 3 × Fin 3 × Fin 3 :=
  fun t => (colPt t.val.1, colPt t.val.2.1, colPt t.val.2.2)

/-! ## The general `hlocal` -/

/-- **General `hlocal` for a `Finset` dissection.**  For every triangle of any
`IsDissection`, the number of its door-edges equals `doorCount12` of its three
(col-derived) vertex colours — the exact `hlocal` hypothesis of
`exists_rainbow_of_odd_boundary`, discharged from the geometry (nondegeneracy
supplies vertex-distinctness; the geometric `doorSet` supplies the per-edge
colour characterisation).  No hand-typed table. -/
theorem dissection_hlocal (S : Finset Tri) (hS : IsDissection S) :
    ∀ t : ↥S, (incS S t ∩ doorSet S).card
      = doorCount12 (vcolS S t).1 (vcolS S t).2.1 (vcolS S t).2.2 := by
  intro t
  have hnd : Nondeg t.val := hS.nondeg t.val t.property
  have hsub : triEdges t.val.1 t.val.2.1 t.val.2.2 ⊆ allEdges S :=
    fun e he => Finset.mem_biUnion.mpr ⟨t.val, t.property, he⟩
  have hab_mem : s(t.val.1, t.val.2.1) ∈ allEdges S :=
    hsub (by simp [triEdges])
  have hbc_mem : s(t.val.2.1, t.val.2.2) ∈ allEdges S :=
    hsub (by simp [triEdges])
  have hac_mem : s(t.val.1, t.val.2.2) ∈ allEdges S :=
    hsub (by simp [triEdges])
  exact triEdgeInter_card_local colPt (doorSet S)
    (mem_doorSet_of_edge S hab_mem)
    (mem_doorSet_of_edge S hbc_mem)
    (mem_doorSet_of_edge S hac_mem)
    (nondeg_ne_v12 hnd) (nondeg_ne_v23 hnd) (nondeg_ne_v13 hnd)

/-! ## The general `hmult` -/

/-- The `≤ 2` half of `hmult`, in general, straight from
`MonskyHmultWiring.mult_le_two` (which needs exactly nondegeneracy +
pairwise interior-disjointness — the content of `IsDissection`). -/
theorem dissection_mult_le_two (S : Finset Tri) (hS : IsDissection S)
    (e : Sym2 Pt) : MonskySpernerParity.mult (incS S) e ≤ 2 := by
  have h := MonskyHmultWiring.mult_le_two (T := ↥S) (v1S S) (v2S S) (v3S S)
    (fun t => hS.nondeg t.val t.property)
    (fun t1 t2 hne Px Py => hS.interiorDisjoint t1.val t1.property t2.val t2.property
      (fun heq => hne (Subtype.ext heq)) Px Py) e
  exact h

/-- **General `hmult` for a `Finset` dissection.**  Every door edge has
multiplicity `1` or `2`: `≤ 2` from `dissection_mult_le_two`, and `≥ 1` because
a door edge occurs in the dissection (so lies in at least one triangle). -/
theorem dissection_hmult (S : Finset Tri) (hS : IsDissection S) :
    ∀ e ∈ doorSet S,
      MonskySpernerParity.mult (incS S) e = 1
        ∨ MonskySpernerParity.mult (incS S) e = 2 := by
  intro e he
  have hle : MonskySpernerParity.mult (incS S) e ≤ 2 := dissection_mult_le_two S hS e
  have he_all : e ∈ allEdges S := ((mem_doorSet S e).mp he).1
  obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he_all
  have hpos : 0 < MonskySpernerParity.mult (incS S) e := by
    rw [MonskySpernerParity.mult_apply]
    apply Finset.card_pos.mpr
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact het
  omega

/-! ## Capstone: an odd boundary forces a rainbow triangle, in general -/

/-- **The general triangle-side conclusion for a `Finset` dissection.**  For any
`IsDissection` of the unit square whose boundary carries an *odd* number of
`{1,2}`-doors (`hbdry`, the one remaining geometric input — supplied concretely
by `MonskyBoundaryOddness.boundary_doors_odd` for the unit square's four sides),
some triangle of the dissection is genuinely 3-coloured (rainbow) under the real
2-adic colouring.

This is `exists_rainbow_of_odd_boundary` with `hlocal` and `hmult` both
discharged *in general* from the `Finset` dissection predicate — closing the
last per-instance-only hypothesis of the abstract engine. -/
theorem dissection_exists_rainbow (S : Finset Tri) (hS : IsDissection S)
    (hbdry : Odd (MonskySpernerParity.boundary (incS S) (doorSet S)).card) :
    ∃ t : ↥S, rainbow3 (vcolS S t).1 (vcolS S t).2.1 (vcolS S t).2.2 :=
  MonskyThreeColorDoors.exists_rainbow_of_odd_boundary
    (incS S) (doorSet S) (vcolS S)
    (dissection_hlocal S hS) (dissection_hmult S hS) hbdry

/-! ## Sanity lemmas -/

/-- The door set is a subset of the dissection's edge set. -/
lemma doorSet_subset_allEdges (S : Finset Tri) : doorSet S ⊆ allEdges S :=
  Finset.filter_subset _ _

end MonskyDissectionHlocal
