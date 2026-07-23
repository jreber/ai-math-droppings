/-
# The complement of a friendship graph — is it a disjoint union of cliques?

`docs/kb/conjectures/conj-2026-07-17-046.json` asks: for a friendship graph `G` (every two
distinct vertices have exactly one common neighbour), is the complement `Gᶜ` a disjoint union
of cliques — equivalently, is "equal-or-non-adjacent-in-`G`"

  `SameCliqueRel G u v := u = v ∨ Gᶜ.Adj u v`

an equivalence relation on `V`?

## What this file actually establishes

`SameCliqueRel G` is **always** reflexive and symmetric (for *any* simple graph `G`, no
friendship hypothesis needed) — that part of "disjoint union of cliques" is free. But
**transitivity fails in general**, even for genuine friendship graphs with more than one
triangle: the *bowtie* graph (two triangles glued at a shared hub vertex, on 5 vertices) is a
friendship graph — this is the classical `k = 2`-triangle windmill, a completely legitimate
instance of `Friendship` distinct from the degenerate `K₃` case — but its complement is a
4-cycle on the four non-hub vertices, which is connected without being complete, so it is
*not* a disjoint union of cliques.

So the conjecture as stated is **false** for general friendship graphs; it happens to hold only
in the degenerate single-triangle (`K₃`) case, where the complement has no edges at all. This
file gives:

* `sameCliqueRel_reflexive`, `sameCliqueRel_symmetric` — the two directions that hold for
  every simple graph, friendship or not.
* `bowtie` — the explicit 5-vertex two-triangle windmill.
* `bowtie_friendship` — `bowtie` satisfies the friendship hypothesis (machine-checked, `decide`).
* `bowtie_sameCliqueRel_not_transitive` — `SameCliqueRel bowtie` is not transitive, exhibited
  by the concrete triple `1, 3, 2` (`decide`).
* `friendship_complement_clique_union_false` — the headline: there exists a friendship graph
  `G` for which `SameCliqueRel G` is *not* an equivalence relation, i.e. `Gᶜ` is *not* a
  disjoint union of cliques in general. This is a genuine, machine-checked refutation of the
  conjecture as universally stated, built directly from `bowtie_friendship` and
  `bowtie_sameCliqueRel_not_transitive`.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.FinCases
import Propositio.Combinatorics.FriendshipRegular

namespace FriendshipComplementCliques

open SimpleGraph FriendshipRegular

/-! ## The candidate equivalence relation, and what always holds -/

variable {V : Type*} (G : SimpleGraph V)

/-- "Equal, or non-adjacent in `G`" — equivalently "equal, or adjacent in the complement `Gᶜ`".
`Gᶜ` being a disjoint union of cliques is exactly the statement that this relation is an
equivalence relation on `V` (its equivalence classes are then the cliques of `Gᶜ`, with no
`Gᶜ`-edges between distinct classes since non-membership means `G`-adjacency, i.e. `Gᶜ`-
non-adjacency). Declared as `abbrev` (reducible) so that `Decidable` instances for `Gᶜ.Adj`
transfer to it automatically, which the `decide`-based proofs below rely on. -/
abbrev SameCliqueRel (u v : V) : Prop := u = v ∨ Gᶜ.Adj u v

/-- `SameCliqueRel G` is reflexive for *every* simple graph `G` — no friendship hypothesis
needed. -/
theorem sameCliqueRel_reflexive : Reflexive (SameCliqueRel G) :=
  fun _ => Or.inl rfl

/-- `SameCliqueRel G` is symmetric for *every* simple graph `G` — no friendship hypothesis
needed. -/
theorem sameCliqueRel_symmetric : Symmetric (SameCliqueRel G) := by
  rintro u v (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr h.symm

/-! ## The counterexample: the bowtie graph (two triangles sharing a hub) -/

/-- Adjacency for the bowtie graph on `Fin 5`: vertex `0` is the hub, adjacent to every other
vertex; `{1, 2}` and `{3, 4}` are the two triangle "wings" (each wing-pair is also adjacent to
each other, forming a triangle with the hub). No edges run between the two wings. -/
def bowtieAdj (v w : Fin 5) : Prop :=
  v ≠ w ∧
    (v = 0 ∨ w = 0 ∨ (v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 1) ∨ (v = 3 ∧ w = 4) ∨ (v = 4 ∧ w = 3))

instance : DecidableRel bowtieAdj := fun _ _ => by unfold bowtieAdj; infer_instance

/-- The bowtie graph: two triangles sharing a common hub vertex `0`. This is the classical
`k = 2`-triangle windmill graph, a legitimate friendship graph on 5 vertices. -/
def bowtie : SimpleGraph (Fin 5) where
  Adj := bowtieAdj
  symm := by intro v w h; unfold bowtieAdj at *; tauto
  loopless := ⟨fun v h => h.1 rfl⟩

instance : DecidableRel bowtie.Adj := inferInstanceAs (DecidableRel bowtieAdj)

/-- The bowtie graph satisfies the friendship hypothesis: every two distinct vertices have
exactly one common neighbour. Machine-checked over the 5-vertex graph, following the same
`fin_cases`/`ExistsUnique`-unfolding pattern as `FriendshipK3Example.k3_friendship`. -/
theorem bowtie_friendship : Friendship bowtie := by
  intro u v huv
  fin_cases u <;> fin_cases v <;>
    first
      | exact absurd rfl huv
      | (simp only [ExistsUnique, ne_eq, bowtie, bowtieAdj]; decide)

/-- `SameCliqueRel bowtie` is **not** transitive: vertex `1` (wing-1) and vertex `3` (wing-2)
are non-adjacent in `bowtie` (hence related), `3` and `2` (wing-1) are non-adjacent (hence
related), but `1` and `2` *are* adjacent in `bowtie` (same triangle wing) — so they are *not*
related. This is exactly the obstruction: the complement of the bowtie graph is a 4-cycle on
`{1, 2, 3, 4}` (plus the isolated hub `0`), which is connected but not complete, hence not a
disjoint union of cliques. -/
theorem bowtie_sameCliqueRel_not_transitive :
    ¬ (∀ a b c : Fin 5, SameCliqueRel bowtie a b → SameCliqueRel bowtie b c →
        SameCliqueRel bowtie a c) := by
  intro htrans
  have h13 : SameCliqueRel bowtie 1 3 := by decide
  have h32 : SameCliqueRel bowtie 3 2 := by decide
  have h12 : SameCliqueRel bowtie 1 2 := htrans 1 3 2 h13 h32
  revert h12
  decide

/-! ## Headline: the conjecture is false for general friendship graphs -/

/-- **The complement of a friendship graph need not be a disjoint union of cliques.**

There exists a friendship graph `G` (the bowtie graph, a genuine two-triangle windmill) for
which `SameCliqueRel G` — "equal, or non-adjacent in `G`" — is *not* an equivalence relation,
because transitivity fails. Equivalently: `Gᶜ` is not a disjoint union of cliques in general.

This directly refutes the universally-quantified reading of
`docs/kb/conjectures/conj-2026-07-17-046.json` ("for a friendship graph `G`, `Gᶜ` is a disjoint
union of cliques"): that statement only holds in the degenerate single-triangle (`K₃`) case,
where the complement has no edges at all, and fails as soon as the friendship graph has two or
more triangles glued at the hub. -/
theorem friendship_complement_clique_union_false :
    ∃ (G : SimpleGraph (Fin 5)), Friendship G ∧ ¬ Equivalence (SameCliqueRel G) := by
  refine ⟨bowtie, bowtie_friendship, ?_⟩
  intro heqv
  exact bowtie_sameCliqueRel_not_transitive (fun a b c hab hbc => heqv.trans hab hbc)

end FriendshipComplementCliques
