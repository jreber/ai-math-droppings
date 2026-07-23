/-
# Is the line graph of a friendship graph always a clique?

`docs/kb/conjectures/conj-2026-07-17-039.json` asks: for a friendship graph `G` (every two
distinct vertices have exactly one common neighbour), is the line graph `L(G)` a clique —
i.e. do every two distinct edges of `G` always share a vertex?

## What this file actually establishes

The claim is **true for the degenerate single-triangle case** (and, more generally, true
whenever *every* edge of `G` passes through one common vertex — the star/windmill-hub
situation) but **false in general**: the *bowtie* graph (two triangles glued at a shared hub
vertex, on 5 vertices — the same example used to refute the sibling conjecture
`conj-2026-07-17-046` in `FriendshipComplementCliques.lean`) is a genuine friendship graph, yet
its two "wing" edges `{1, 2}` and `{3, 4}` share no vertex at all. So the line graph of the
bowtie graph is *not* a clique, and the conjecture as universally stated over all friendship
graphs is false.

This mirrors the sibling refutation: a friendship graph need not have *every* edge incident to
its hub — only the edges of a single triangle do; additional triangles glued at the hub
contribute wing edges that are mutually non-adjacent (as edges of `G`) whenever they lie in
different wings.

* `allEdgesIncidentTo`, `star_graph_line_graph_clique` — the conditional positive result:
  *if* every edge of `G` is incident to some fixed vertex `u` (the honest "star" hypothesis),
  *then* `L(G)` is a clique. This part is unconditionally true for any simple graph, no
  friendship hypothesis needed — it is exactly the sound content salvaged from the prior
  (incomplete) attempt at this conjecture.
* `bowtie_wing_edges_exist` — the two wing edges `⟨1, 2, ...⟩` and `⟨3, 4, ...⟩` of `bowtie`
  are genuine edges (`bowtie.Adj 1 2` and `bowtie.Adj 3 4`, machine-checked).
* `bowtie_wing_edges_not_share_vertex` — those two edges do **not** satisfy
  `edgesShareVertex`, machine-checked.
* `friendship_line_graph_clique_false` — the headline: there exists a friendship graph `G`
  and two distinct edges of `G` that share no vertex, i.e. `L(G)` is not a clique in general.
  This is a genuine, machine-checked refutation of the conjecture as universally stated.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Propositio.Combinatorics.FriendshipRegular
import Propositio.Combinatorics.FriendshipComplementCliques

namespace FriendshipLineGraphClique

open SimpleGraph Finset FriendshipRegular FriendshipComplementCliques

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An edge is a pair of distinct adjacent vertices. This is the vertex set of the line graph
`L(G)`: `L(G)`'s vertices are the edges of `G`. -/
structure Edge where
  u : V
  v : V
  h_adj : G.Adj u v
  h_ne : u ≠ v

/-- Two edges share a common vertex iff their endpoints overlap. This is exactly `L(G)`-
adjacency: `e₁` and `e₂` are adjacent in the line graph iff they share an endpoint in `G`. -/
def edgesShareVertex (e₁ e₂ : Edge G) : Prop :=
  e₁.u = e₂.u ∨ e₁.u = e₂.v ∨ e₁.v = e₂.u ∨ e₁.v = e₂.v

/-- A vertex is universal if it is adjacent to all other vertices. -/
def isUniversal (u : V) : Prop := ∀ v : V, v ≠ u → G.Adj u v

/-- Every edge of `G` passes through the fixed vertex `u` — the honest "star" hypothesis. -/
def allEdgesIncidentTo (u : V) : Prop :=
  ∀ e : Edge G, e.u = u ∨ e.v = u

/-! ## The conditional positive result: star graphs have clique line graphs

This direction is unconditionally true for *any* simple graph — no friendship hypothesis is
needed once `allEdgesIncidentTo` is assumed directly. -/

/-- **If every edge of `G` is incident to a common vertex `u_center`, the line graph of `G` is
a clique**: any two edges share `u_center` as a common endpoint. -/
theorem star_graph_line_graph_clique
    {u_center : V}
    (h_star : allEdgesIncidentTo G u_center)
    (e₁ e₂ : Edge G) :
    edgesShareVertex G e₁ e₂ := by
  unfold allEdgesIncidentTo at h_star
  unfold edgesShareVertex
  have he₁ : e₁.u = u_center ∨ e₁.v = u_center := h_star e₁
  have he₂ : e₂.u = u_center ∨ e₂.v = u_center := h_star e₂
  cases he₁ with
  | inl h1u =>
    cases he₂ with
    | inl h2u => exact Or.inl (h1u.trans h2u.symm)
    | inr h2v => exact Or.inr (Or.inl (h1u.trans h2v.symm))
  | inr h1v =>
    cases he₂ with
    | inl h2u => exact Or.inr (Or.inr (Or.inl (h1v.trans h2u.symm)))
    | inr h2v => exact Or.inr (Or.inr (Or.inr (h1v.trans h2v.symm)))

/-! ## The counterexample: the bowtie graph's two wing edges do not share a vertex

We reuse the `bowtie` graph from `FriendshipComplementCliques` (two triangles glued at hub
vertex `0`, on `Fin 5`), already proved to satisfy `Friendship` there. -/

/-- The wing-1 edge `{1, 2}` of `bowtie` is a genuine edge. -/
theorem bowtie_adj_one_two : bowtie.Adj 1 2 := by decide

/-- The wing-2 edge `{3, 4}` of `bowtie` is a genuine edge. -/
theorem bowtie_adj_three_four : bowtie.Adj 3 4 := by decide

/-- The wing-1 edge of `bowtie`, as an `Edge bowtie`. -/
def bowtieWing1 : Edge bowtie := ⟨1, 2, bowtie_adj_one_two, by decide⟩

/-- The wing-2 edge of `bowtie`, as an `Edge bowtie`. -/
def bowtieWing2 : Edge bowtie := ⟨3, 4, bowtie_adj_three_four, by decide⟩

/-- **The two wing edges of the bowtie graph share no vertex.** Vertex `0` is the hub, but
neither wing edge touches it; wing-1 (`{1, 2}`) and wing-2 (`{3, 4}`) are on disjoint vertex
pairs, so as edges of `L(bowtie)` they are non-adjacent. -/
theorem bowtie_wing_edges_not_share_vertex :
    ¬ edgesShareVertex bowtie bowtieWing1 bowtieWing2 := by
  unfold edgesShareVertex bowtieWing1 bowtieWing2
  decide

/-! ## Headline: the conjecture is false for general friendship graphs -/

/-- **The line graph of a friendship graph need not be a clique.**

There exists a friendship graph `G` (the bowtie graph, a genuine two-triangle windmill) and two
distinct edges of `G` — the two wing edges `{1, 2}` and `{3, 4}` — that share no common vertex.
Equivalently, `L(G)` is not a clique in general.

This directly refutes the universally-quantified reading of
`docs/kb/conjectures/conj-2026-07-17-039.json` ("the line graph `L(G)` of any friendship graph
`G` is a clique"): the claim only holds when every edge of `G` is incident to a single common
vertex (the degenerate single-triangle `K₃` case, or more generally whenever
`allEdgesIncidentTo` holds directly — see `star_graph_line_graph_clique` above), and fails as
soon as the friendship graph has two or more triangles glued at the hub, exactly as its sibling
conjecture about complements (`conj-2026-07-17-046`, refuted in
`FriendshipComplementCliques.lean`) does. -/
theorem friendship_line_graph_clique_false :
    ∃ (G : SimpleGraph (Fin 5)) (_ : DecidableRel G.Adj), Friendship G ∧
      ∃ e₁ e₂ : Edge G, ¬ edgesShareVertex G e₁ e₂ := by
  refine ⟨bowtie, inferInstance, bowtie_friendship, bowtieWing1, bowtieWing2, ?_⟩
  exact bowtie_wing_edges_not_share_vertex

end FriendshipLineGraphClique
