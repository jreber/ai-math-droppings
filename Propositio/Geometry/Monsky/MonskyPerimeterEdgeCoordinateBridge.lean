/-
# Bridging sub-theorem (1) to a REAL triangulation's full triangle index type

Sub-theorem (1), `MonskyPerimeterEdgeMultiplicity.perimeter_edge_multiplicity_one`
(and its `≤ 1` core, `perimeter_edge_card_le_one`), computes the multiplicity
of a perimeter edge `(A,B)` only over an *already-filtered* `Fintype T` whose
every element is presented via `apex : T → V` with `inc t = triEdges A B
(apex t)` for ALL `t : T` — i.e. `T` is pre-restricted to triangles that
already contain the edge. It says nothing about a real triangulation's *full*
triangle-index type, most of whose triangles do not touch `(A,B)` at all.

This file builds exactly the missing bridge, identified precisely in the
frontier note `monsky_hbdry_subtheorem2_2026_07_29_VACUITY_CAVEAT`: given a
genuine dissection `S : Finset MonskyDissectionHlocal.Tri` (the "real
triangulation's full triangle-index type" is `↥S`, `inc_real = incS S`), show
that the multiplicity `MonskySpernerParity.mult (incS S) (s(A,B))`, computed
by filtering over ALL of `↥S`, equals `1` for a genuine perimeter edge
`(A,B)` (one satisfying `SameSide`).

## Strategy

1. **Permutation invariance of the three local geometric predicates.**
   `MonskyThreeColorDoors.triEdges`, `MonskyEdgeMultiplicityAtMostTwo.
   Nondegenerate` (via `cross2`), and `MonskyEdgeMultiplicityAtMostTwo.TriInt`
   are each defined via ONE fixed ordering `(a,b,c)` of a triangle's three
   vertices, but the underlying geometric content (the edge set, the
   nonzero-area condition, the open barycentric interior) does not depend on
   that ordering. We prove the six-permutation invariance of each (generated
   by two transpositions, `swap12`/`swap23`, composed).

2. **Apex extraction (`apex_extraction`).** Given a nondegenerate,
   in-square triangle `(a,b,c)` and a hypothesis that `(A,B)` is one of its
   three edges, extract the third vertex ("apex") together with the
   TRANSFERRED `Nondegenerate A B apex`, `InSquare apex`, and (crucially) an
   `iff` relating `TriInt A B apex` to the triangle's own `TriIntP` (its
   *native* order `a,b,c`) — this is what lets us reuse
   `IsDissection.interiorDisjoint` (stated in native `a,b,c` order) as the
   `hdisj` hypothesis of `perimeter_edge_card_le_one` (stated in `A,B,apex`
   order), without needing to rebuild interior-disjointness from scratch.

3. **The bridge theorem (`dissection_perimeter_edge_multiplicity_one`).** For
   a real dissection `S`/`hS : IsDissection S` and a genuine perimeter edge
   `(A,B)` (`SameSide`) occurring in at least one triangle, form the subtype
   `Tsub := {t : ↥S // s(A,B) ∈ incS S t}`, extract an apex function on it via
   (2) + classical choice, apply `perimeter_edge_card_le_one` directly (not
   the `apex`/`inc`-wrapped `perimeter_edge_multiplicity_one`, since we do not
   need to reconstruct a matching `inc'` — the raw cardinality bound suffices)
   to get `Fintype.card Tsub ≤ 1`, combine with the nonempty witness to get
   `= 1`, and transfer to `MonskySpernerParity.mult (incS S) (s(A,B)) = 1` via
   `Fintype.card_subtype` + `mult_apply`.

Axiom-clean throughout: only elementary algebra (`ring`, `linarith`),
`Sym2`/`Finset`/`Fintype` bookkeeping, and the already axiom-clean imported
Monsky machinery (`MonskyPerimeterEdgeMultiplicity`, `MonskyDissectionHlocal`,
`MonskyDissectionBoundaryScope`, `MonskyEdgeMultiplicityAtMostTwo`,
`MonskyThreeColorDoors`, `MonskySpernerParity`); no `sorry`, no project
`axiom`, no `native_decide`.

## Honest scope note

This closes the bridge from sub-theorem (1)'s abstract pre-filtered `T` to a
REAL dissection's full triangle-index type `↥S`, for a SINGLE perimeter edge
known to satisfy `SameSide` and to occur in the dissection. It does **not**
by itself discharge `hbdry` in
`MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`: that still additionally
needs (a) the identification of `MonskySpernerParity.boundary (incS S)
(doorSet S)`'s edges with genuine `SameSide` perimeter edges in the first
place — which `MonskyDissectionBoundaryScope`'s own scope note documents as
BLOCKED in general (non-edge-to-edge dissections can have `mult = 1` interior
edges, e.g. its explicit diagonal/T-junction counterexample) — and (b) the
parity count itself (`MonskyBoundaryOddness.boundary_doors_odd`). This file
supplies the piece the frontier note asked for (the `T`-to-`↥S` cardinality
bridge); it is a genuine, non-vacuous addition, but it composes with, rather
than replaces, `MonskyDissectionBoundaryScope`'s documented general blocker.
-/

import Propositio.Geometry.Monsky.MonskyPerimeterEdgeMultiplicity
import Propositio.Geometry.Monsky.MonskyDissectionHlocal
import Propositio.Geometry.Monsky.MonskyDissectionBoundaryScope
import Propositio.Geometry.Monsky.MonskyEdgeMultiplicityAtMostTwo
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Propositio.Geometry.Monsky.MonskySpernerParity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

namespace MonskyPerimeterEdgeCoordinateBridge

open MonskyThreeColorDoors
open MonskyEdgeMultiplicityAtMostTwo
open MonskyPerimeterEdgeMultiplicity (InSquare SameSide)
open MonskyDissectionHlocal (Pt Tri IsDissection incS inUnitSquare)

/-! ## Part 0: `InSquare` / `inUnitSquare` are the same predicate -/

/-- `MonskyPerimeterEdgeMultiplicity.InSquare` and `MonskyDissectionHlocal.
inUnitSquare` are literally the same closed-square membership predicate
(same definition, different file); converting between them is definitional. -/
lemma inSquare_of_inUnitSquare {x y : ℝ} (h : inUnitSquare x y) : InSquare x y := h

/-! ## Part 1: `triEdges` is invariant, as a `Finset`, under permuting its
three vertex arguments -/

variable {V : Type*} [DecidableEq V]

lemma triEdges_swap12 (a b c : V) : triEdges a b c = triEdges b a c := by
  unfold triEdges
  have h : (s(a, b) : Sym2 V) = s(b, a) := Sym2.eq_swap
  rw [h]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triEdges_swap23 (a b c : V) : triEdges a b c = triEdges a c b := by
  unfold triEdges
  have h : (s(b, c) : Sym2 V) = s(c, b) := Sym2.eq_swap
  rw [h]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triEdges_rot (a b c : V) : triEdges a b c = triEdges b c a :=
  (triEdges_swap12 a b c).trans (triEdges_swap23 b a c)

lemma triEdges_rot2 (a b c : V) : triEdges a b c = triEdges c a b :=
  (triEdges_swap23 a b c).trans (triEdges_swap12 a c b)

lemma triEdges_swap13 (a b c : V) : triEdges a b c = triEdges c b a :=
  ((triEdges_swap12 a b c).trans (triEdges_swap23 b a c)).trans (triEdges_swap12 b c a)

/-! ## Part 2: `cross2` / `Nondegenerate` sign transfer under permutation -/

private lemma cross2_swap12 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Ax Ay Bx By Cx Cy = -cross2 Bx By Ax Ay Cx Cy := by
  unfold cross2; ring

private lemma cross2_swap23 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Ax Ay Bx By Cx Cy = -cross2 Ax Ay Cx Cy Bx By := by
  unfold cross2; ring

private lemma nondeg_swap12 {Ax Ay Bx By Cx Cy : ℝ}
    (h : Nondegenerate Ax Ay Bx By Cx Cy) : Nondegenerate Bx By Ax Ay Cx Cy := by
  unfold Nondegenerate at h ⊢
  rw [cross2_swap12] at h
  exact neg_ne_zero.mp h

private lemma nondeg_swap23 {Ax Ay Bx By Cx Cy : ℝ}
    (h : Nondegenerate Ax Ay Bx By Cx Cy) : Nondegenerate Ax Ay Cx Cy Bx By := by
  unfold Nondegenerate at h ⊢
  rw [cross2_swap23] at h
  exact neg_ne_zero.mp h

private lemma nondeg_rot {Ax Ay Bx By Cx Cy : ℝ}
    (h : Nondegenerate Ax Ay Bx By Cx Cy) : Nondegenerate Bx By Cx Cy Ax Ay :=
  nondeg_swap23 (nondeg_swap12 h)

private lemma nondeg_rot2 {Ax Ay Bx By Cx Cy : ℝ}
    (h : Nondegenerate Ax Ay Bx By Cx Cy) : Nondegenerate Cx Cy Ax Ay Bx By :=
  nondeg_swap12 (nondeg_swap23 h)

private lemma nondeg_swap13 {Ax Ay Bx By Cx Cy : ℝ}
    (h : Nondegenerate Ax Ay Bx By Cx Cy) : Nondegenerate Cx Cy Bx By Ax Ay :=
  nondeg_swap12 (nondeg_swap23 (nondeg_swap12 h))

/-! ## Part 3: `TriInt` (open barycentric interior) is invariant, as a `Prop`,
under permuting its three vertex arguments -/

private lemma triInt_swap12 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Bx By Ax Ay Cx Cy Px Py := by
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
    exact ⟨β, α, γ, hβ, hα, hγ, by linarith, by linarith, by linarith⟩
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
    exact ⟨β, α, γ, hβ, hα, hγ, by linarith, by linarith, by linarith⟩

private lemma triInt_swap23 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Ax Ay Cx Cy Bx By Px Py := by
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
    exact ⟨α, γ, β, hα, hγ, hβ, by linarith, by linarith, by linarith⟩
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
    exact ⟨α, γ, β, hα, hγ, hβ, by linarith, by linarith, by linarith⟩

private lemma triInt_rot (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Bx By Cx Cy Ax Ay Px Py :=
  (triInt_swap12 Ax Ay Bx By Cx Cy Px Py).trans (triInt_swap23 Bx By Ax Ay Cx Cy Px Py)

private lemma triInt_rot2 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Cx Cy Ax Ay Bx By Px Py :=
  (triInt_swap23 Ax Ay Bx By Cx Cy Px Py).trans (triInt_swap12 Ax Ay Cx Cy Bx By Px Py)

private lemma triInt_swap13 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Cx Cy Bx By Ax Ay Px Py :=
  ((triInt_swap12 Ax Ay Bx By Cx Cy Px Py).trans
    (triInt_swap23 Bx By Ax Ay Cx Cy Px Py)).trans
    (triInt_swap12 Bx By Cx Cy Ax Ay Px Py)

/-! ## Part 4: apex extraction -/

/-- **Apex extraction.** Given a nondegenerate, in-square triangle `(a,b,c)`
(raw point coordinates) and a hypothesis that the edge `(A,B)` is one of its
three edges, extract the third vertex ("apex") together with:

* the transferred nondegeneracy `Nondegenerate A B apex`,
* the transferred in-square membership `InSquare apex`, and
* an `iff` identifying `TriInt A B apex` with the triangle's *native*
  `(a,b,c)`-ordered open interior — this is what lets a caller reuse an
  interior-disjointness hypothesis stated in native order (as
  `IsDissection.interiorDisjoint` is) to discharge the `(A,B,apex)`-ordered
  `hdisj` hypothesis of `perimeter_edge_card_le_one`.

Proof: a six-way case split on which of the triangle's three edges equals
`(A,B)` and in which orientation, each case closed by the matching
`nondeg_*`/`triInt_*` permutation lemma from Parts 2–3. -/
private lemma apex_extraction
    {a b c A B : Pt}
    (hnd : Nondegenerate a.1 a.2 b.1 b.2 c.1 c.2)
    (hina : InSquare a.1 a.2) (hinb : InSquare b.1 b.2) (hinc : InSquare c.1 c.2)
    (hmem : s(A, B) ∈ triEdges a b c) :
    ∃ apex : Pt,
      Nondegenerate A.1 A.2 B.1 B.2 apex.1 apex.2 ∧
      InSquare apex.1 apex.2 ∧
      (∀ Px Py : ℝ, TriInt A.1 A.2 B.1 B.2 apex.1 apex.2 Px Py ↔
                     TriInt a.1 a.2 b.1 b.2 c.1 c.2 Px Py) := by
  have hmem' : s(A, B) = s(a, b) ∨ s(A, B) = s(b, c) ∨ s(A, B) = s(a, c) := by
    simpa [triEdges, Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hmem' with h1 | h2 | h3
  · rw [Sym2.eq_iff] at h1
    rcases h1 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · rw [hA, hB]
      exact ⟨c, hnd, hinc, fun _ _ => Iff.rfl⟩
    · rw [hA, hB]
      exact ⟨c, nondeg_swap12 hnd, hinc,
        fun Px Py => (triInt_swap12 a.1 a.2 b.1 b.2 c.1 c.2 Px Py).symm⟩
  · rw [Sym2.eq_iff] at h2
    rcases h2 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · rw [hA, hB]
      exact ⟨a, nondeg_rot hnd, hina,
        fun Px Py => (triInt_rot a.1 a.2 b.1 b.2 c.1 c.2 Px Py).symm⟩
    · rw [hA, hB]
      exact ⟨a, nondeg_swap13 hnd, hina,
        fun Px Py => (triInt_swap13 a.1 a.2 b.1 b.2 c.1 c.2 Px Py).symm⟩
  · rw [Sym2.eq_iff] at h3
    rcases h3 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · rw [hA, hB]
      exact ⟨b, nondeg_swap23 hnd, hinb,
        fun Px Py => (triInt_swap23 a.1 a.2 b.1 b.2 c.1 c.2 Px Py).symm⟩
    · rw [hA, hB]
      exact ⟨b, nondeg_rot2 hnd, hinb,
        fun Px Py => (triInt_rot2 a.1 a.2 b.1 b.2 c.1 c.2 Px Py).symm⟩

/-! ## Part 4b: the pre-filtered subtype and its `Fintype` instance -/

/-- The subtype of `↥S`-triangles that actually use the edge `(A,B)`. This is
the real triangulation's full triangle-index type `↥S`, filtered down to the
triangles touching a fixed edge — the object sub-theorem (1)'s abstract `T`
should have been (but wasn't) connected to. -/
private def Tsub (S : Finset Tri) (A B : Pt) : Type :=
  {t : ↥S // s(A, B) ∈ incS S t}

private noncomputable instance instFintypeTsub (S : Finset Tri) (A B : Pt) :
    Fintype (Tsub S A B) := by
  classical
  unfold Tsub
  infer_instance

/-! ## Part 5: the bridge theorem -/

/-- **The `T`-to-`↥S` multiplicity bridge.** For a real dissection `S`
(`hS : IsDissection S`) and a genuine perimeter edge `(A,B)` — one satisfying
`SameSide` and occurring in at least one triangle of `S` (`hex`) — the
`MonskySpernerParity` multiplicity of `(A,B)`, computed over the FULL
triangle-index type `↥S` with the REAL incidence map `incS S` (not a
pre-filtered abstract `T`), is exactly `1`.

This is the bridge scoped by the frontier note
`monsky_hbdry_subtheorem2_2026_07_29_VACUITY_CAVEAT`: it connects
`MonskyPerimeterEdgeMultiplicity.perimeter_edge_card_le_one` (which only
handles an abstract, already-filtered `T`) to a genuine dissection's full
triangle-index type. See the file docstring's "Honest scope note" for what
this does and does not close toward `hbdry`. -/
theorem dissection_perimeter_edge_multiplicity_one
    {S : Finset Tri} (hS : IsDissection S) (A B : Pt)
    (hside : SameSide A.1 A.2 B.1 B.2)
    (hex : ∃ t : ↥S, s(A, B) ∈ incS S t) :
    MonskySpernerParity.mult (incS S) (s(A, B)) = 1 := by
  classical
  -- Per-element apex, extracted via `apex_extraction` + classical choice.
  have hspec : ∀ t : Tsub S A B,
      ∃ apex : Pt,
        Nondegenerate A.1 A.2 B.1 B.2 apex.1 apex.2 ∧
        InSquare apex.1 apex.2 ∧
        (∀ Px Py : ℝ, TriInt A.1 A.2 B.1 B.2 apex.1 apex.2 Px Py ↔
          TriInt t.val.val.1.1 t.val.val.1.2 t.val.val.2.1.1 t.val.val.2.1.2
            t.val.val.2.2.1 t.val.val.2.2.2 Px Py) := by
    intro t
    have hnd : Nondegenerate t.val.val.1.1 t.val.val.1.2 t.val.val.2.1.1
        t.val.val.2.1.2 t.val.val.2.2.1 t.val.val.2.2.2 := hS.nondeg t.val.val t.val.property
    have hina := inSquare_of_inUnitSquare
      (MonskyDissectionBoundaryScope.vertex1_mem_unitSquare hS t.val.property)
    have hinb := inSquare_of_inUnitSquare
      (MonskyDissectionBoundaryScope.vertex2_mem_unitSquare hS t.val.property)
    have hinc := inSquare_of_inUnitSquare
      (MonskyDissectionBoundaryScope.vertex3_mem_unitSquare hS t.val.property)
    have hmem : s(A, B) ∈ triEdges t.val.val.1 t.val.val.2.1 t.val.val.2.2 := t.property
    exact apex_extraction hnd hina hinb hinc hmem
  -- The apex function, and its properties, via classical choice.
  let apexOf : Tsub S A B → Pt := fun t => Classical.choose (hspec t)
  have hnd_apex : ∀ t : Tsub S A B, Nondegenerate A.1 A.2 B.1 B.2 (apexOf t).1 (apexOf t).2 :=
    fun t => (Classical.choose_spec (hspec t)).1
  have hin_apex : ∀ t : Tsub S A B, InSquare (apexOf t).1 (apexOf t).2 :=
    fun t => (Classical.choose_spec (hspec t)).2.1
  have hiff_apex : ∀ t : Tsub S A B, ∀ Px Py : ℝ,
      TriInt A.1 A.2 B.1 B.2 (apexOf t).1 (apexOf t).2 Px Py ↔
        TriInt t.val.val.1.1 t.val.val.1.2 t.val.val.2.1.1 t.val.val.2.1.2
          t.val.val.2.2.1 t.val.val.2.2.2 Px Py :=
    fun t => (Classical.choose_spec (hspec t)).2.2
  -- Interior-disjointness, transferred from `IsDissection.interiorDisjoint`
  -- (native `a,b,c` order) to the `(A,B,apex)` order via `hiff_apex`.
  have hdisj : ∀ t₁ t₂ : Tsub S A B, t₁ ≠ t₂ → ∀ Px Py : ℝ,
      ¬ (TriInt A.1 A.2 B.1 B.2 (apexOf t₁).1 (apexOf t₁).2 Px Py ∧
         TriInt A.1 A.2 B.1 B.2 (apexOf t₂).1 (apexOf t₂).2 Px Py) := by
    intro t₁ t₂ hne Px Py ⟨h1, h2⟩
    have hne' : t₁.val.val ≠ t₂.val.val := by
      intro heq
      apply hne
      apply Subtype.ext
      exact Subtype.ext heq
    exact hS.interiorDisjoint t₁.val.val t₁.val.property t₂.val.val t₂.val.property hne' Px Py
      ⟨(hiff_apex t₁ Px Py).mp h1, (hiff_apex t₂ Px Py).mp h2⟩
  -- Apply the geometric core lemma directly: `Fintype.card (Tsub S A B) ≤ 1`.
  have hcard_le : Fintype.card (Tsub S A B) ≤ 1 :=
    MonskyPerimeterEdgeMultiplicity.perimeter_edge_card_le_one A.1 A.2 B.1 B.2
      (fun t => (apexOf t).1) (fun t => (apexOf t).2)
      hside hnd_apex hin_apex hdisj
  -- Nonempty witness from `hex`.
  obtain ⟨t0, ht0⟩ := hex
  have hTsub_ne : Nonempty (Tsub S A B) := ⟨⟨t0, ht0⟩⟩
  have hcard_pos : 0 < Fintype.card (Tsub S A B) := Fintype.card_pos_iff.mpr hTsub_ne
  have hcard_eq : Fintype.card (Tsub S A B) = 1 := by omega
  -- Transfer to `MonskySpernerParity.mult` via `Fintype.card_subtype`.
  have htrans : Fintype.card (Tsub S A B)
      = (Finset.univ.filter (fun t : ↥S => s(A, B) ∈ incS S t)).card :=
    Fintype.card_subtype (fun t : ↥S => s(A, B) ∈ incS S t)
  rw [MonskySpernerParity.mult_apply]
  rw [← htrans]
  exact hcard_eq

end MonskyPerimeterEdgeCoordinateBridge
