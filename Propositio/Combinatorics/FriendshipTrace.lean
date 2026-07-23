/-
# Friendship Theorem — trace facts for the adjacency matrix

Two clean trace identities for the adjacency matrix `A = G.adjMatrix ℝ` used in the
spectral (`k = 2`) proof of the Friendship Theorem:

* `trace_adjMatrix_eq_zero` — `tr(A) = 0` for *any* simple graph (no self-loops: the
  diagonal entries `A v v = if G.Adj v v then 1 else 0` vanish since `G.Adj v v` is
  false by `SimpleGraph.irrefl`).
* `trace_adjMatrix_sq_of_regular` — for a `k`-regular graph, `tr(A²) = n · k`: every
  diagonal entry of `A²` is the degree of its vertex (`adjMatrix_sq_diag`, no friendship
  hypothesis needed), and regularity makes every degree `= k`, so the sum over `n`
  vertices is `n · k`.

## Main mathlib API used
* `Matrix.trace`, `Matrix.diag_apply`
* `SimpleGraph.adjMatrix_apply`, `SimpleGraph.irrefl`
* `Finset.sum_eq_zero`, `Finset.sum_const`, `Finset.card_univ`
* `FriendshipMatrixEquation.adjMatrix_sq_diag`
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Propositio.Combinatorics.FriendshipMatrixEquation

namespace FriendshipTrace

open SimpleGraph Finset Matrix FriendshipMatrixEquation

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **The adjacency matrix is traceless.** For *any* simple graph `G` (no friendship or
regularity hypothesis needed), `tr(A) = 0` since a simple graph has no self-loops, so
every diagonal entry `A v v = if G.Adj v v then 1 else 0` is `0`. -/
theorem trace_adjMatrix_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (G.adjMatrix ℝ) = 0 := by
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro v _
  rw [Matrix.diag_apply, SimpleGraph.adjMatrix_apply]
  simp only [if_neg (G.irrefl)]

/-- **`tr(A²) = n·k` for a `k`-regular graph.** Every diagonal entry of `A²` is the
degree of its vertex (`adjMatrix_sq_diag`, holds for any graph, no friendship
hypothesis), and `k`-regularity makes each of the `n` degrees equal to `k`. -/
theorem trace_adjMatrix_sq_of_regular {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hreg : G.IsRegularOfDegree k) :
    Matrix.trace ((G.adjMatrix ℝ) ^ 2) = (Fintype.card V : ℝ) * k := by
  have hdeg : ∀ v, ((G.adjMatrix ℝ) ^ 2) v v = (k : ℝ) := by
    intro v
    rw [adjMatrix_sq_diag G v, hreg v]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, hdeg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end FriendshipTrace
