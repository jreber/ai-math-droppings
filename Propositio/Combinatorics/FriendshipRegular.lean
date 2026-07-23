/-
# Friendship Theorem — the regularity brick

The Friendship Theorem (Erdős–Rényi–Sós) states that in a finite simple graph in
which every two distinct vertices have *exactly one* common neighbour, some vertex
is adjacent to all others.

This file proves the elementary combinatorial first step: such a "friendship graph"
that has **no universal vertex** (no vertex adjacent to all others) is **regular**
(every vertex has the same degree).

The argument is the classical eigenvalue-free one:

* `nonadj_deg_eq` — two non-adjacent (distinct) vertices have equal degree, via an
  injective pairing of their neighbourhoods using the unique-common-neighbour map.
* `friendship_regular_of_no_universal` — globally regular: if the graph were not
  regular, the unique common neighbour `z` of a degree-mismatched adjacent pair `u, v`
  forces every vertex outside `{u, v}` to have degree exactly `2`, and then one of
  `u, v` turns out to be universal — contradicting the hypothesis.

The friendship hypothesis is encoded as the genuine
`∀ u v, u ≠ v → ∃! w, G.Adj w u ∧ G.Adj w v`
(`w` is adjacent to both `u` and `v`, i.e. a common neighbour, and it is unique).
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card

namespace FriendshipRegular

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The friendship hypothesis: any two distinct vertices have a unique common neighbour. -/
abbrev Friendship : Prop := ∀ u v : V, u ≠ v → ∃! w, G.Adj w u ∧ G.Adj w v

/-- For two non-adjacent vertices `u, v`, the unique-common-neighbour-with-`v` map sends
neighbours of `u` injectively into neighbours of `v`, so `deg u ≤ deg v`. -/
theorem nonadj_deg_le (hfriend : Friendship G) {u v : V} (huv : ¬ G.Adj u v) :
    G.degree u ≤ G.degree v := by
  classical
  show (G.neighborFinset u).card ≤ (G.neighborFinset v).card
  apply Finset.card_le_card_of_injOn
    (fun w => if h : G.Adj u w then (hfriend w v (fun e => huv (e ▸ h))).choose else v)
  · -- maps neighbours of `u` to neighbours of `v`
    intro w hw
    rw [Finset.mem_coe, G.mem_neighborFinset] at hw
    have hwv : w ≠ v := fun e => huv (e ▸ hw)
    simp only [dif_pos hw]
    rw [Finset.mem_coe, G.mem_neighborFinset]
    exact ((hfriend w v hwv).choose_spec.1.2).symm
  · -- injective on neighbours of `u`
    intro w1 hw1 w2 hw2 hEq
    rw [Finset.mem_coe, G.mem_neighborFinset] at hw1 hw2
    have hw1v : w1 ≠ v := fun e => huv (e ▸ hw1)
    have hw2v : w2 ≠ v := fun e => huv (e ▸ hw2)
    simp only [dif_pos hw1, dif_pos hw2] at hEq
    change (hfriend w1 v hw1v).choose = (hfriend w2 v hw2v).choose at hEq
    obtain ⟨hz1w, hz1v⟩ := (hfriend w1 v hw1v).choose_spec.1
    obtain ⟨hz2w, hz2v⟩ := (hfriend w2 v hw2v).choose_spec.1
    set z := (hfriend w1 v hw1v).choose with hzdef
    rw [← hEq] at hz2w hz2v
    -- `z` is a common neighbour of `w1`, `w2` and `v`; `z ≠ u` since `z ~ v` but `¬ u ~ v`
    have hzu : z ≠ u := fun e => huv (e ▸ hz1v)
    obtain ⟨c, _, hc⟩ := hfriend u z (Ne.symm hzu)
    exact (hc w1 ⟨hw1.symm, hz1w.symm⟩).trans (hc w2 ⟨hw2.symm, hz2w.symm⟩).symm

/-- Two non-adjacent vertices have equal degree. -/
theorem nonadj_deg_eq (hfriend : Friendship G) {u v : V} (huv : ¬ G.Adj u v) :
    G.degree u = G.degree v :=
  le_antisymm (nonadj_deg_le G hfriend huv) (nonadj_deg_le G hfriend (fun h => huv h.symm))

/-- **Regularity brick of the Friendship Theorem.**
In a finite simple graph where every two distinct vertices have exactly one common
neighbour, if no vertex is adjacent to all others then the graph is regular. -/
theorem friendship_regular_of_no_universal
    (hfriend : Friendship G)
    (hno_univ : ¬ ∃ u, ∀ v, v ≠ u → G.Adj u v) :
    ∀ u v, G.degree u = G.degree v := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, v, hdeg_ne⟩ := hcon
  -- non-adjacent distinct vertices are equal-degree, so a degree mismatch forces adjacency
  have huv : G.Adj u v := by
    by_contra h
    exact hdeg_ne (nonadj_deg_eq G hfriend h)
  have huv_ne : u ≠ v := G.ne_of_adj huv
  -- `z` : the unique common neighbour of `u` and `v`
  obtain ⟨z, ⟨hzu, hzv⟩, hzuniq⟩ := hfriend u v huv_ne
  have hzu_ne : z ≠ u := G.ne_of_adj hzu
  have hzv_ne : z ≠ v := G.ne_of_adj hzv
  -- the neighbours of `z` are exactly `u` and `v`
  have hadjz : ∀ t, G.Adj z t → t = u ∨ t = v := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    obtain ⟨htu, htv⟩ := hcon
    by_cases hut : G.Adj u t
    · by_cases hvt : G.Adj v t
      · -- `t` is a common neighbour of `u, v`, hence `t = z`, contradicting `z ~ t`
        have : t = z := hzuniq t ⟨hut.symm, hvt.symm⟩
        exact G.irrefl (this ▸ ht)
      · -- the unique common neighbour of `t` and `v` is `u`; but `z` is one too, so `z = u`
        obtain ⟨c, _, hc⟩ := hfriend t v htv
        have h1 : u = c := hc u ⟨hut, huv⟩
        have h2 : z = c := hc z ⟨ht, hzv⟩
        exact hzu_ne (h2.trans h1.symm)
    · by_cases hvt : G.Adj v t
      · -- symmetric: the unique common neighbour of `t` and `u` is `v`, so `z = v`
        obtain ⟨c, _, hc⟩ := hfriend t u htu
        have h1 : v = c := hc v ⟨hvt, huv.symm⟩
        have h2 : z = c := hc z ⟨ht, hzu⟩
        exact hzv_ne (h2.trans h1.symm)
      · -- `t` non-adjacent to both `u` and `v`: forces `deg u = deg v`, contradiction
        have e1 : G.degree u = G.degree t := nonadj_deg_eq G hfriend hut
        have e2 : G.degree v = G.degree t := nonadj_deg_eq G hfriend hvt
        exact hdeg_ne (e1.trans e2.symm)
  -- `deg z = 2`
  have hdegz : G.degree z = 2 := by
    have hset : G.neighborFinset z = {u, v} := by
      ext t
      simp only [G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact hadjz t
      · rintro (rfl | rfl)
        · exact hzu
        · exact hzv
    rw [← G.card_neighborFinset_eq_degree, hset, Finset.card_insert_of_notMem (by
      simp [huv_ne]), Finset.card_singleton]
  -- every vertex outside `{u, v}` has degree `2`
  have hdeg2 : ∀ t, t ≠ u → t ≠ v → G.degree t = 2 := by
    intro t htu htv
    by_cases htz : t = z
    · rw [htz]; exact hdegz
    · have hzt : ¬ G.Adj z t := by
        intro h
        rcases hadjz t h with h | h
        · exact htu h
        · exact htv h
      rw [← nonadj_deg_eq G hfriend hzt]
      exact hdegz
  -- not regular ⇒ one of `u, v` is universal, contradicting `hno_univ`
  apply hno_univ
  rcases ne_or_eq (G.degree u) 2 with hu2 | hu2
  · -- `deg u ≠ 2` ⇒ `u` is universal
    refine ⟨u, fun b hbu => ?_⟩
    by_cases hbv : b = v
    · rw [hbv]; exact huv
    · by_contra hub
      have hdb : G.degree b = 2 := hdeg2 b hbu hbv
      have := nonadj_deg_eq G hfriend hub
      rw [hdb] at this
      exact hu2 this
  · -- `deg u = 2` ⇒ `deg v ≠ 2` ⇒ `v` is universal
    have hv2 : G.degree v ≠ 2 := fun h => hdeg_ne (hu2.trans h.symm)
    refine ⟨v, fun b hbv => ?_⟩
    by_cases hbu : b = u
    · rw [hbu]; exact huv.symm
    · by_contra hvb
      have hdb : G.degree b = 2 := hdeg2 b hbu hbv
      have := nonadj_deg_eq G hfriend hvb
      rw [hdb] at this
      exact hv2 this

end FriendshipRegular
