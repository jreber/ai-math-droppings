/-
# The Friendship Theorem (Erdős–Rényi–Sós) — capstone assembly

This file assembles the classical **Friendship Theorem**: in a finite simple graph
`G` in which every two distinct vertices have exactly one common neighbour, some
vertex is adjacent to all others (a "universal" or "hub" vertex).

  `friendship_theorem (hf : Friendship G) [Nonempty V] :`
  `    ∃ v : V, ∀ u : V, u ≠ v → G.Adj v u`

## Proof

By contradiction: suppose `G` has no universal vertex.

* `FriendshipRegular.friendship_regular_of_no_universal` then shows `G` is
  `k`-regular for some `k` (namely `k = G.degree v₀` for any fixed `v₀`).
* `FriendshipVertexCount.friendship_card_eq` gives `Fintype.card V = k² − k + 1`.
* **`k = 0` branch**: then `Fintype.card V = 1`, so `V` is a singleton; the fixed
  vertex `v₀` is *vacuously* universal (there is no `u ≠ v₀`), directly
  contradicting the "no universal vertex" assumption.
* **`k ≥ 1` branch**: `FriendshipKEqualsTwo.k_eq_two` forces `k = 2`, hence
  `Fintype.card V = 3`. A `2`-regular vertex on a `3`-vertex graph has degree
  `Fintype.card V − 1`, so (elementary cardinality lemma
  `adj_of_degree_eq_card_sub_one` below) it is adjacent to every other vertex —
  again contradicting "no universal vertex".

Either way we contradict the standing assumption, completing the proof.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Propositio.Combinatorics.FriendshipRegular
import Propositio.Combinatorics.FriendshipKEqualsTwo
import Propositio.Combinatorics.FriendshipVertexCount

namespace FriendshipTheorem

open SimpleGraph Finset FriendshipRegular

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Elementary cardinality lemma.** If `v`'s degree equals `Fintype.card V − 1`
(the maximum possible), then `v` is adjacent to every other vertex: its
`neighborFinset` has the same cardinality as `univ \ {v}` and is contained in it,
hence the two finsets coincide. -/
theorem adj_of_degree_eq_card_sub_one {v : V}
    (hd : G.degree v = Fintype.card V - 1) :
    ∀ u : V, u ≠ v → G.Adj v u := by
  classical
  have hsub : G.neighborFinset v ⊆ Finset.univ \ ({v} : Finset V) := by
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨Finset.mem_univ w, fun hwv => ?_⟩
    exact G.notMem_neighborFinset_self v (hwv ▸ hw)
  have hcardT : (Finset.univ \ ({v} : Finset V)).card = Fintype.card V - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr (Finset.mem_univ v)),
      Finset.card_univ, Finset.card_singleton]
  have hcardS : (G.neighborFinset v).card = Fintype.card V - 1 := by
    rw [G.card_neighborFinset_eq_degree]; exact hd
  have heq : G.neighborFinset v = Finset.univ \ ({v} : Finset V) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardT, hcardS])
  intro u hu
  have : u ∈ G.neighborFinset v := by
    rw [heq, Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ u, hu⟩
  exact (G.mem_neighborFinset v u).mp this

/-- **The Friendship Theorem (Erdős–Rényi–Sós).**
A finite simple graph in which every two distinct vertices have exactly one
common neighbour has a universal vertex: some `v` adjacent to every other
vertex. -/
theorem friendship_theorem (hf : Friendship G) [Nonempty V] :
    ∃ v : V, ∀ u : V, u ≠ v → G.Adj v u := by
  classical
  by_contra hcon
  -- `hcon : ¬ ∃ v, ∀ u, u ≠ v → G.Adj v u`, which is exactly the "no universal
  -- vertex" hypothesis needed by `friendship_regular_of_no_universal`.
  have hregular : ∀ u v, G.degree u = G.degree v :=
    friendship_regular_of_no_universal G hf hcon
  obtain ⟨v0⟩ : Nonempty V := inferInstance
  set k : ℕ := G.degree v0 with hk_def
  have hregdeg : G.IsRegularOfDegree k := fun v => hregular v v0
  have hcard : (Fintype.card V : ℤ) = (k : ℤ) ^ 2 - k + 1 :=
    FriendshipVertexCount.friendship_card_eq G hf hregdeg
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- `k = 0` ⇒ `Fintype.card V = 1` ⇒ `v0` is vacuously universal.
    apply hcon
    have hcard1 : (Fintype.card V : ℤ) = 1 := by rw [hcard, hk0]; ring
    have hcard1' : Fintype.card V = 1 := by exact_mod_cast hcard1
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard1'
    refine ⟨v0, fun u hu => absurd ((hx u).trans (hx v0).symm) hu⟩
  · -- `k ≥ 1` ⇒ `k = 2` ⇒ `Fintype.card V = 3` ⇒ `v0` has full degree ⇒ universal.
    have hk2 : k = 2 := FriendshipKEqualsTwo.k_eq_two (G := G) hf hregdeg hk1
    have hcard3 : (Fintype.card V : ℤ) = 3 := by rw [hcard, hk2]; ring
    have hcard3' : Fintype.card V = 3 := by exact_mod_cast hcard3
    have hdeg2 : G.degree v0 = 2 := by rw [← hk_def, hk2]
    apply hcon
    refine ⟨v0, adj_of_degree_eq_card_sub_one G (v := v0) ?_⟩
    rw [hcard3']; omega

end FriendshipTheorem
