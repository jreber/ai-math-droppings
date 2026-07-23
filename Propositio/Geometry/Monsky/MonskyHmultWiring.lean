/-
# Wiring the edge-multiplicity-≤-2 geometric lemma into the Sperner engine

`docs/kb/conjectures/conj-2026-07-10-001.json`: the just-landed geometric fact
`MonskyEdgeMultiplicityAtMostTwo.card_le_two_of_shared_full_edge` (a segment
cannot be a full edge of three pairwise-interior-disjoint triangles) wires
*directly* into `MonskySpernerParity.mult`, the abstract multiplicity function
whose `≤ 2` bound is (together with the trivial `≥ 1` for door-edges) exactly
the `hmult` hypothesis of `MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`.

## Setup

A finite index type `T` of triangles, three vertex-selector functions
`v1 v2 v3 : T → ℝ × ℝ`, nondegeneracy of every triangle
(`Nondegenerate` on its coordinates) and pairwise interior-disjointness of any
two distinct triangles (`TriInt`-disjointness). Set

  `inc t := MonskyThreeColorDoors.triEdges (v1 t) (v2 t) (v3 t)`.

**Main result (`mult_le_two`).** For every edge `e : Sym2 (ℝ × ℝ)`,
`MonskySpernerParity.mult inc e ≤ 2`.

## Proof strategy

Fix `e`; by `Sym2.ind` write `e = s(A, B)` for concrete points `A B : ℝ × ℝ`.
`MonskySpernerParity.mult inc e` unfolds (via `Fintype.card_subtype`) to
`Fintype.card {t // e ∈ inc t}`. For every `t` in this subtype, exactly one of
the triangle's three edges equals `{A, B}` (nondegeneracy forces the three
vertices `v1 t, v2 t, v3 t` pairwise distinct, so the three edges are pairwise
distinct as `Sym2` elements and cannot coincide as sets unless the underlying
vertex-pairs coincide) — this yields a well-defined **apex** map
`C : {t // e ∈ inc t} → ℝ × ℝ` extracting the vertex not in `{A, B}`
(`apex_extraction`, the one genuinely new small lemma: `Nondegenerate` and
`TriInt` both transport along the vertex relabelling this apex-extraction
induces — `cross2` is alternating under any transposition of two vertices
[`ring` identities `cross2_swap12/23/13`, `cross2_rot1/2`], and `TriInt`'s
barycentric witness simply permutes along with the vertex order
[`TriInt_symm12/23`, `TriInt_swap13`, `TriInt_rot1/2`]). Feeding the resulting
family into `card_le_two_of_shared_full_edge` gives
`Fintype.card {t // e ∈ inc t} ≤ 2`, i.e. `mult inc e ≤ 2` by definition.

## Scope

This covers **edge-to-edge (conforming)** families of pairwise
interior-disjoint triangles: the geometric input
`card_le_two_of_shared_full_edge` is about a segment being a *full* shared
edge of the triangles that contain it. A general Monsky dissection may have
hanging T-vertices (a small triangle's full edge lying along only part of a
larger triangle's edge); that case is **not** covered here and would need a
separate reduction argument. This file establishes `hmult` unconditionally
for the conforming case only.

Axiom-clean: reuses `MonskyEdgeMultiplicityAtMostTwo.card_le_two_of_shared_full_edge`
(itself only elementary real algebra) and `MonskySpernerParity.mult_apply`; the
new content here is pure `ring`-level algebraic permutation bookkeeping plus a
`Sym2`/`Finset` case bash. No axioms beyond the ambient
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic
import Propositio.Geometry.Monsky.MonskyEdgeMultiplicityAtMostTwo
import Propositio.Geometry.Monsky.MonskySpernerParity
import Propositio.Geometry.Monsky.MonskyThreeColorDoors

namespace MonskyHmultWiring

open MonskyEdgeMultiplicityAtMostTwo

/-! ## Permutation invariance of `cross2` (pure `ring` identities) -/

lemma cross2_swap12 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Bx By Ax Ay Cx Cy = - cross2 Ax Ay Bx By Cx Cy := by
  unfold cross2; ring

lemma cross2_swap23 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Ax Ay Cx Cy Bx By = - cross2 Ax Ay Bx By Cx Cy := by
  unfold cross2; ring

lemma cross2_swap13 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Cx Cy Bx By Ax Ay = - cross2 Ax Ay Bx By Cx Cy := by
  unfold cross2; ring

lemma cross2_rot1 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Bx By Cx Cy Ax Ay = cross2 Ax Ay Bx By Cx Cy := by
  unfold cross2; ring

lemma cross2_rot2 (Ax Ay Bx By Cx Cy : ℝ) :
    cross2 Cx Cy Ax Ay Bx By = cross2 Ax Ay Bx By Cx Cy := by
  unfold cross2; ring

/-! ## Permutation invariance of `TriInt` (barycentric-witness relabelling) -/

private lemma TriInt_swap_fst_snd (Ax Ay Bx By Cx Cy Px Py : ℝ)
    (h : TriInt Ax Ay Bx By Cx Cy Px Py) : TriInt Bx By Ax Ay Cx Cy Px Py := by
  obtain ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩ := h
  exact ⟨b, a, c, hb, ha, hc, by linarith, by rw [hx]; ring, by rw [hy]; ring⟩

private lemma TriInt_swap_snd_third (Ax Ay Bx By Cx Cy Px Py : ℝ)
    (h : TriInt Ax Ay Bx By Cx Cy Px Py) : TriInt Ax Ay Cx Cy Bx By Px Py := by
  obtain ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩ := h
  exact ⟨a, c, b, ha, hc, hb, by linarith, by rw [hx]; ring, by rw [hy]; ring⟩

private lemma TriInt_swap13_fwd (Ax Ay Bx By Cx Cy Px Py : ℝ)
    (h : TriInt Ax Ay Bx By Cx Cy Px Py) : TriInt Cx Cy Bx By Ax Ay Px Py := by
  obtain ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩ := h
  exact ⟨c, b, a, hc, hb, ha, by linarith, by rw [hx]; ring, by rw [hy]; ring⟩

private lemma TriInt_rot_fwd (Ax Ay Bx By Cx Cy Px Py : ℝ)
    (h : TriInt Ax Ay Bx By Cx Cy Px Py) : TriInt Bx By Cx Cy Ax Ay Px Py := by
  obtain ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩ := h
  exact ⟨b, c, a, hb, hc, ha, by linarith, by rw [hx]; ring, by rw [hy]; ring⟩

/-- Swapping the first two vertices of `TriInt` doesn't change the set of
interior points (the barycentric witness just relabels `(a,b) ↦ (b,a)`). -/
lemma TriInt_symm12 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Bx By Ax Ay Cx Cy Px Py :=
  ⟨TriInt_swap_fst_snd Ax Ay Bx By Cx Cy Px Py, TriInt_swap_fst_snd Bx By Ax Ay Cx Cy Px Py⟩

/-- Swapping the last two vertices of `TriInt` doesn't change the set of
interior points. -/
lemma TriInt_symm23 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Ax Ay Cx Cy Bx By Px Py :=
  ⟨TriInt_swap_snd_third Ax Ay Bx By Cx Cy Px Py, TriInt_swap_snd_third Ax Ay Cx Cy Bx By Px Py⟩

/-- Reversing all three vertices of `TriInt` doesn't change the set of
interior points. -/
lemma TriInt_swap13 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Cx Cy Bx By Ax Ay Px Py :=
  ⟨TriInt_swap13_fwd Ax Ay Bx By Cx Cy Px Py, TriInt_swap13_fwd Cx Cy Bx By Ax Ay Px Py⟩

/-- Cyclically rotating the three vertices of `TriInt` doesn't change the set
of interior points. -/
lemma TriInt_rot1 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Bx By Cx Cy Ax Ay Px Py :=
  ⟨TriInt_rot_fwd Ax Ay Bx By Cx Cy Px Py,
    fun h => TriInt_rot_fwd Cx Cy Ax Ay Bx By Px Py (TriInt_rot_fwd Bx By Cx Cy Ax Ay Px Py h)⟩

/-- The opposite cyclic rotation. -/
lemma TriInt_rot2 (Ax Ay Bx By Cx Cy Px Py : ℝ) :
    TriInt Ax Ay Bx By Cx Cy Px Py ↔ TriInt Cx Cy Ax Ay Bx By Px Py :=
  (TriInt_rot1 Cx Cy Ax Ay Bx By Px Py).symm

/-! ## Apex extraction: the one genuinely new geometric-bookkeeping lemma -/

/-- **Apex extraction.** If `s(A, B)` is one of the three edges of the
nondegenerate triangle `(a1, a2, a3)`, there is a (unique, though we only need
existence) third vertex `C ∈ {a1, a2, a3}` — the *apex* opposite the edge
`(A, B)` — such that `(A, B, C)` is itself nondegenerate and has *exactly* the
same open interior as `(a1, a2, a3)`.

This is the vertex-permutation-invariance fact the wiring needs: it lets us
uniformly relabel every triangle sharing the edge `{A, B}` into the
`(A, B, apex)` form expected by `card_le_two_of_shared_full_edge`. -/
lemma apex_extraction (a1 a2 a3 A B : ℝ × ℝ)
    (hnd : Nondegenerate a1.1 a1.2 a2.1 a2.2 a3.1 a3.2)
    (hmem : s(A, B) ∈ MonskyThreeColorDoors.triEdges a1 a2 a3) :
    ∃ C : ℝ × ℝ, (C = a1 ∨ C = a2 ∨ C = a3) ∧
      Nondegenerate A.1 A.2 B.1 B.2 C.1 C.2 ∧
      ∀ Px Py : ℝ, TriInt A.1 A.2 B.1 B.2 C.1 C.2 Px Py ↔
        TriInt a1.1 a1.2 a2.1 a2.2 a3.1 a3.2 Px Py := by
  unfold MonskyThreeColorDoors.triEdges at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h12 | h23 | h13
  · rcases Sym2.eq_iff.mp h12 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · -- A = a1, B = a2, apex = a3 : the identity case
      refine ⟨a3, Or.inr (Or.inr rfl), ?_, ?_⟩
      · rw [hA, hB]; exact hnd
      · intro Px Py; rw [hA, hB]
    · -- A = a2, B = a1, apex = a3
      refine ⟨a3, Or.inr (Or.inr rfl), ?_, ?_⟩
      · rw [hA, hB]
        unfold Nondegenerate at hnd ⊢
        rw [cross2_swap12]
        exact neg_ne_zero.mpr hnd
      · intro Px Py; rw [hA, hB]
        exact (TriInt_symm12 a1.1 a1.2 a2.1 a2.2 a3.1 a3.2 Px Py).symm
  · rcases Sym2.eq_iff.mp h23 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · -- A = a2, B = a3, apex = a1
      refine ⟨a1, Or.inl rfl, ?_, ?_⟩
      · rw [hA, hB]
        unfold Nondegenerate at hnd ⊢
        rw [cross2_rot1]
        exact hnd
      · intro Px Py; rw [hA, hB]
        exact (TriInt_rot1 a1.1 a1.2 a2.1 a2.2 a3.1 a3.2 Px Py).symm
    · -- A = a3, B = a2, apex = a1
      refine ⟨a1, Or.inl rfl, ?_, ?_⟩
      · rw [hA, hB]
        unfold Nondegenerate at hnd ⊢
        rw [cross2_swap13]
        exact neg_ne_zero.mpr hnd
      · intro Px Py; rw [hA, hB]
        exact (TriInt_swap13 a1.1 a1.2 a2.1 a2.2 a3.1 a3.2 Px Py).symm
  · rcases Sym2.eq_iff.mp h13 with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · -- A = a1, B = a3, apex = a2
      refine ⟨a2, Or.inr (Or.inl rfl), ?_, ?_⟩
      · rw [hA, hB]
        unfold Nondegenerate at hnd ⊢
        rw [cross2_swap23]
        exact neg_ne_zero.mpr hnd
      · intro Px Py; rw [hA, hB]
        exact (TriInt_symm23 a1.1 a1.2 a2.1 a2.2 a3.1 a3.2 Px Py).symm
    · -- A = a3, B = a1, apex = a2
      refine ⟨a2, Or.inr (Or.inl rfl), ?_, ?_⟩
      · rw [hA, hB]
        unfold Nondegenerate at hnd ⊢
        rw [cross2_rot2]
        exact hnd
      · intro Px Py; rw [hA, hB]
        exact (TriInt_rot2 a1.1 a1.2 a2.1 a2.2 a3.1 a3.2 Px Py).symm

/-! ## Main theorem: `mult inc e ≤ 2` for conforming triangulations -/

/-- **The multiplicity of any edge is at most 2**, for any finite family of
pairwise-interior-disjoint nondegenerate triangles in the plane given by
vertex-selectors `v1 v2 v3 : T → ℝ × ℝ`. This is the `≤ 2` half of the
`hmult` hypothesis of `MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`
(combined with the trivial `≥ 1` fact for edges actually drawn from the
triangulation, this closes `hmult` unconditionally for edge-to-edge/conforming
triangulations — see the file docstring for the scope caveat on general
dissections with hanging T-vertices). -/
theorem mult_le_two
    {T : Type*} [Fintype T]
    (v1 v2 v3 : T → ℝ × ℝ)
    (hnd : ∀ t : T, Nondegenerate (v1 t).1 (v1 t).2 (v2 t).1 (v2 t).2 (v3 t).1 (v3 t).2)
    (hdisj : ∀ t1 t2 : T, t1 ≠ t2 → ∀ Px Py : ℝ,
      ¬ (TriInt (v1 t1).1 (v1 t1).2 (v2 t1).1 (v2 t1).2 (v3 t1).1 (v3 t1).2 Px Py ∧
         TriInt (v1 t2).1 (v1 t2).2 (v2 t2).1 (v2 t2).2 (v3 t2).1 (v3 t2).2 Px Py))
    (e : Sym2 (ℝ × ℝ)) :
    MonskySpernerParity.mult (fun t => MonskyThreeColorDoors.triEdges (v1 t) (v2 t) (v3 t)) e
      ≤ 2 := by
  classical
  induction e using Sym2.ind with
  | _ A B =>
    rw [MonskySpernerParity.mult_apply, ← Fintype.card_subtype]
    set Te := {t : T // s(A, B) ∈ MonskyThreeColorDoors.triEdges (v1 t) (v2 t) (v3 t)} with hTe
    have happex : ∀ t : Te, ∃ C : ℝ × ℝ,
        (C = v1 t.1 ∨ C = v2 t.1 ∨ C = v3 t.1) ∧
        Nondegenerate A.1 A.2 B.1 B.2 C.1 C.2 ∧
        ∀ Px Py : ℝ, TriInt A.1 A.2 B.1 B.2 C.1 C.2 Px Py ↔
          TriInt (v1 t.1).1 (v1 t.1).2 (v2 t.1).1 (v2 t.1).2 (v3 t.1).1 (v3 t.1).2 Px Py :=
      fun t => apex_extraction (v1 t.1) (v2 t.1) (v3 t.1) A B (hnd t.1) t.2
    choose C _hCmem hCnd hCiff using happex
    have hcard := MonskyEdgeMultiplicityAtMostTwo.card_le_two_of_shared_full_edge
      (T := Te) A.1 A.2 B.1 B.2 (fun t => (C t).1) (fun t => (C t).2)
      hCnd
      (by
        intro t1 t2 ht12 Px Py hcon
        obtain ⟨hp1, hp2⟩ := hcon
        exact hdisj t1.1 t2.1 (fun h => ht12 (Subtype.ext h)) Px Py
          ⟨(hCiff t1 Px Py).mp hp1, (hCiff t2 Px Py).mp hp2⟩)
    exact hcard

end MonskyHmultWiring
