/-
# The 3-uniform "friendship hypergraph" conjecture — refuted by the Fano plane

`docs/kb/conjectures/conj-2026-07-17-042.json` asks: for a 3-uniform hypergraph `H` on a
finite vertex set `V` in which every pair of distinct vertices lies in exactly one common
hyperedge (i.e. `∀ u ≠ v, ∃! e ∈ H, u ∈ e ∧ v ∈ e`), does there necessarily exist a
*universal* vertex — one that belongs to every hyperedge of `H`?

This is exactly the classical definition of a **Steiner triple system**: a collection of
3-element "blocks" (hyperedges) on a point set such that every pair of points lies in exactly
one block. The friendship theorem (the `k = 2` / graph case, already formalized in
`FriendshipTheorem.lean`) says the analogous 2-uniform statement *does* force a universal
vertex (a "hub"). The natural guess is that the 3-uniform generalization should behave the
same way. It does not.

## What this file actually establishes

The **smallest nontrivial Steiner triple system**, `STS(7)`, better known as the **Fano
plane** — 7 points, 7 lines (blocks) of size 3, every pair of points on exactly one line — is
a genuine 3-uniform hypergraph satisfying the hypothesis exactly, but it has **no universal
point**: every point of the Fano plane lies on exactly `r = 3` of the `b = 7` lines (a
standard fact of design theory, `r · (k - 1) = v - 1` with `v = 7`, `k = 3` gives `r = 3`,
and `b = v·r/k = 7`), so no point is on all `7` lines. This directly refutes the conjecture
as universally stated — the 3-uniform "friendship" generalization is **false** in general,
unlike the graph case.

* `ThreeUniformFriendshipConjecture` — the formal statement of the conjecture, over a
  genuine `Finset (Finset V)` incidence structure (no hand-typed literals disconnected from a
  real structure): 3-uniformity as `∀ e ∈ H, e.card = 3`, the friendship hypothesis as the
  literal bounded `∃!` from the conjecture statement, and universality as `∃ v, ∀ e ∈ H, v ∈ e`.
* `fanoLine0, …, fanoLine6` — the 7 explicit 3-point lines of the Fano plane on `Fin 7`,
  built from the perfect difference set `{0, 1, 3}` mod `7` (so line `x` is `{x, x+1, x+3}`
  mod `7` for `x = 0, …, 6` — every nonzero residue mod `7` arises as exactly one difference
  of two elements of the base block, which is what makes every pair of points meet in exactly
  one line).
* `fano` — the resulting `Finset (Finset (Fin 7))` of all 7 lines.
* `fano_uniform` — every Fano line has exactly `3` points (machine-checked, `decide`).
* `fano_pair_unique` — every two distinct points of the Fano plane lie on exactly one common
  line (machine-checked over all `42` ordered pairs, `fin_cases` + `decide`) — this is the
  literal 3-uniform friendship hypothesis for `fano`.
* `fano_no_universal_point` — no point of the Fano plane lies on all `7` lines (machine-checked,
  `decide`) — each point lies on only `3` of the `7` lines.
* `three_uniform_friendship_conjecture_false` — the headline: `fano` is a genuine witness that
  `ThreeUniformFriendshipConjecture` is false, built directly from the three facts above.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

namespace FriendshipHypergraphUniversal

/-! ## The conjecture, stated over a real incidence structure -/

/-- The 3-uniform "friendship hypergraph" conjecture: for any finite vertex type `V` and any
`3`-uniform hypergraph `H` (a `Finset (Finset V)` all of whose members have cardinality `3`)
in which every two distinct vertices lie in exactly one common hyperedge, there is a vertex
belonging to every hyperedge of `H`. This is the literal formalization of
`docs/kb/conjectures/conj-2026-07-17-042.json`. -/
def ThreeUniformFriendshipConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
    (∀ e ∈ H, e.card = 3) →
    (∀ u v : V, u ≠ v → ∃! e ∈ H, u ∈ e ∧ v ∈ e) →
    ∃ v : V, ∀ e ∈ H, v ∈ e

/-! ## The counterexample: the Fano plane `STS(7)` -/

/-- The 7 lines of the Fano plane on `Fin 7`, from the perfect difference set `{0, 1, 3}`
mod `7`: line `x` is `{x, x + 1, x + 3}` (mod `7`). Written out explicitly (mod-`7` arithmetic
already carried out) so each line is a plain literal `Finset (Fin 7)`. -/
def fanoLine0 : Finset (Fin 7) := {0, 1, 3}

def fanoLine1 : Finset (Fin 7) := {1, 2, 4}

def fanoLine2 : Finset (Fin 7) := {2, 3, 5}

def fanoLine3 : Finset (Fin 7) := {3, 4, 6}

def fanoLine4 : Finset (Fin 7) := {0, 4, 5}

def fanoLine5 : Finset (Fin 7) := {1, 5, 6}

def fanoLine6 : Finset (Fin 7) := {0, 2, 6}

/-- The Fano plane `STS(7)`: the `7` lines above, as a `Finset (Finset (Fin 7))`. -/
def fano : Finset (Finset (Fin 7)) :=
  {fanoLine0, fanoLine1, fanoLine2, fanoLine3, fanoLine4, fanoLine5, fanoLine6}

set_option maxRecDepth 4000 in
/-- `fano` has exactly `7` distinct lines. -/
theorem fano_card : fano.card = 7 := by decide

set_option maxRecDepth 4000 in
/-- `fano` is `3`-uniform: every line has exactly `3` points. -/
theorem fano_uniform : ∀ e ∈ fano, e.card = 3 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- Every two distinct points of the Fano plane lie on exactly one common line — the literal
`3`-uniform friendship hypothesis, machine-checked over all `42` ordered pairs of distinct
points of `Fin 7`. -/
theorem fano_pair_unique : ∀ u v : Fin 7, u ≠ v → ∃! e ∈ fano, u ∈ e ∧ v ∈ e := by
  intro u v huv
  fin_cases u <;> fin_cases v <;>
    first
      | exact absurd rfl huv
      | (simp only [ExistsUnique]; decide)

set_option maxRecDepth 4000 in
/-- No point of the Fano plane lies on every line: each point lies on exactly `3` of the `7`
lines (a standard fact of Steiner triple system design: `r = (v - 1) / (k - 1) = 6 / 2 = 3`),
so no point is universal. -/
theorem fano_no_universal_point : ¬ ∃ v : Fin 7, ∀ e ∈ fano, v ∈ e := by decide

/-! ## Headline: the conjecture is false -/

/-- **The 3-uniform "friendship hypergraph" conjecture is false.** The Fano plane `STS(7)` is
a genuine `3`-uniform hypergraph on `7` points in which every two distinct points lie in
exactly one common hyperedge, yet it has no universal point — every point lies on only `3` of
its `7` lines. This directly refutes the universally-quantified reading of
`docs/kb/conjectures/conj-2026-07-17-042.json`: unlike the `k = 2` (graph) friendship theorem,
the `3`-uniform generalization does not force a hub vertex. -/
theorem three_uniform_friendship_conjecture_false : ¬ ThreeUniformFriendshipConjecture := by
  intro hconj
  exact fano_no_universal_point (hconj (Fin 7) fano fano_uniform fano_pair_unique)

end FriendshipHypergraphUniversal
