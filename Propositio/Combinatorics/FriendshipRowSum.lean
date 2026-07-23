/-
# Friendship graph — the A² row-sum identity

For a finite simple graph `G` with the **friendship property** (every two distinct
vertices have exactly one common neighbour), the sum of the degrees of the neighbours
of any vertex `v` equals `deg v + (|V| - 1)`:

  ∑_{w ∈ N(v)} deg w = deg v + (card V - 1).

This is the row-sum of the squared adjacency matrix `A²` at `v`: the `(v, u)` entry of
`A²` counts common neighbours of `v` and `u`, which is `deg v` for `u = v` and exactly
`1` for `u ≠ v` (friendship). Summing that row gives `deg v + (card V - 1)`.

The proof is elementary double counting:

  ∑_{w ∈ N(v)} deg w = ∑_{w ∈ N(v)} ∑_{u} 1[w ~ u]        (degree as indicator sum)
                     = ∑_{u} ∑_{w ∈ N(v)} 1[w ~ u]        (swap order, `Finset.sum_comm`)
                     = ∑_{u} |{w ∈ N(v) : w ~ u}|         (common neighbours of v and u)
                     = deg v + ∑_{u ≠ v} 1                 (u = v term is deg v; u ≠ v gives 1)
                     = deg v + (card V - 1).

The friendship hypothesis is the genuine
`∀ u v, u ≠ v → ∃! w, G.Adj w u ∧ G.Adj w v` (same shape as `FriendshipRegular.Friendship`),
so the result is a faithful, non-vacuous implication about friendship graphs
(e.g. the triangle `K₃` and the windmill graphs satisfy the hypothesis).
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace FriendshipRowSum

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The friendship hypothesis: any two distinct vertices have a unique common neighbour.
Identical logical content to `FriendshipRegular.Friendship`. -/
abbrev Friendship : Prop := ∀ u v : V, u ≠ v → ∃! w, G.Adj w u ∧ G.Adj w v

/-- **A² row-sum identity for friendship graphs.**
The sum of the degrees of the neighbours of `v` equals `deg v + (|V| - 1)`. -/
theorem friendship_row_sum (hfriend : Friendship G) (v : V) :
    ∑ w ∈ G.neighborFinset v, G.degree w = G.degree v + (Fintype.card V - 1) := by
  classical
  -- degree as a sum of adjacency indicators
  have hdeg : ∀ w : V, G.degree w = ∑ u : V, if G.Adj w u then 1 else 0 := by
    intro w
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter]
  -- reindex the double sum: LHS = ∑_u |{w ∈ N(v) : w ~ u}|
  have key : ∑ w ∈ G.neighborFinset v, G.degree w
      = ∑ u : V, ((G.neighborFinset v).filter (fun w => G.Adj w u)).card := by
    rw [Finset.sum_congr rfl (fun w _ => hdeg w), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.card_filter]
  -- the u = v term: the filter is all of N(v), so its card is deg v
  have hfv : (G.neighborFinset v).filter (fun w => G.Adj w v) = G.neighborFinset v := by
    apply Finset.filter_true_of_mem
    intro w hw
    rw [G.mem_neighborFinset] at hw
    exact hw.symm
  -- the u ≠ v term: exactly one common neighbour, by friendship
  have hfu : ∀ u ∈ Finset.univ.erase v,
      ((G.neighborFinset v).filter (fun w => G.Adj w u)).card = 1 := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨huv, -⟩ := hu
    rw [Finset.card_eq_one]
    obtain ⟨w0, ⟨hw0v, hw0u⟩, hw0uniq⟩ := hfriend v u huv.symm
    refine ⟨w0, ?_⟩
    ext w
    simp only [Finset.mem_filter, G.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hwv, hwu⟩
      exact hw0uniq w ⟨hwv.symm, hwu⟩
    · rintro rfl
      exact ⟨hw0v.symm, hw0u⟩
  -- assemble
  rw [key, ← Finset.add_sum_erase _ _ (Finset.mem_univ v), hfv,
    G.card_neighborFinset_eq_degree, Finset.sum_congr rfl hfu, Finset.sum_const,
    smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

end FriendshipRowSum

-- Non-vacuity note: the friendship hypothesis is satisfiable (e.g. the triangle K₃ and the
-- windmill/friendship graphs), so `friendship_row_sum` is a genuine implication, not vacuous.
