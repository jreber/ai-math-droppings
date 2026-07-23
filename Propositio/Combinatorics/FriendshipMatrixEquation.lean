/-
# Friendship Theorem — the matrix equation `A² = J + diag(deg − 1)`

For a finite simple graph `G` with the **friendship property** (every two distinct
vertices have exactly one common neighbour), the square of the adjacency matrix
`A = G.adjMatrix ℝ` satisfies the fundamental algebraic identity at the heart of the
spectral (`k = 2`) proof of the Friendship Theorem:

  A² = J + diag(deg v − 1),

where `J` is the all-ones matrix. Entry-wise this is the statement that the `(u, v)`
entry of `A²` counts the common neighbours of `u` and `v`:

* **Diagonal** `(A²) v v = deg v`   (a vertex's common neighbours with itself are its
  own neighbours);
* **Off-diagonal** `(A²) u v = 1` for `u ≠ v`   (friendship: exactly one common
  neighbour).

These two entry-wise facts (`adjMatrix_sq_diag`, `adjMatrix_sq_offdiag`) are the real
combinatorial content; the matrix identity `adjMatrix_sq_eq` is assembled from them by
`Matrix.ext`. With regularity added (all degrees `= k`) we obtain the classical form
`A² = J + (k − 1)·I` (`adjMatrix_sq_eq_of_regular`).

The friendship hypothesis is the genuine
`∀ u v, u ≠ v → ∃! w, G.Adj w u ∧ G.Adj w v` (same shape as
`FriendshipRegular.Friendship`), so all results are faithful, non-vacuous implications
about friendship graphs (e.g. the triangle `K₃` and the windmill graphs satisfy it).

## Main mathlib API used
* `SimpleGraph.adjMatrix_apply` — `A i j = if G.Adj i j then 1 else 0`
* `SimpleGraph.adjMatrix_mul_apply` — `(A * M) v w = ∑ u ∈ N(v), M u w`
* `SimpleGraph.adjMatrix_mul_self_apply_self` — `(A * A) i i = deg i`
* `Finset.sum_boole`, `Finset.card_eq_one`, `SimpleGraph.mem_neighborFinset`
* `Matrix.diagonal_apply_eq` / `_ne`, `Matrix.of_apply`, `Matrix.add_apply`,
  `Matrix.smul_apply`, `Matrix.one_apply_eq` / `_ne`
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Propositio.Combinatorics.FriendshipRegular

namespace FriendshipMatrixEquation

open SimpleGraph Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The friendship hypothesis: any two distinct vertices have a unique common neighbour.
Identical logical content to `FriendshipRegular.Friendship`. -/
abbrev Friendship : Prop := ∀ u v : V, u ≠ v → ∃! w, G.Adj w u ∧ G.Adj w v

/-- **Diagonal entry of `A²`.** The `(v, v)` entry of the squared adjacency matrix is the
degree of `v` (the common neighbours of `v` with itself are exactly its neighbours). -/
theorem adjMatrix_sq_diag (v : V) :
    ((G.adjMatrix ℝ) ^ 2) v v = (G.degree v : ℝ) := by
  rw [pow_two]
  exact G.adjMatrix_mul_self_apply_self v

/-- **Off-diagonal entry of `A²`.** For distinct `u ≠ v`, the `(u, v)` entry of the
squared adjacency matrix is `1`: by the friendship hypothesis, `u` and `v` have exactly
one common neighbour. -/
theorem adjMatrix_sq_offdiag (hfriend : Friendship G) {u v : V} (huv : u ≠ v) :
    ((G.adjMatrix ℝ) ^ 2) u v = 1 := by
  classical
  rw [pow_two, adjMatrix_mul_apply]
  -- `(A * A) u v = ∑ w ∈ N(u), (if G.Adj w v then 1 else 0)`
  simp only [adjMatrix_apply]
  rw [Finset.sum_boole]
  -- reduce to: the common neighbours of `u` and `v` form a singleton
  have hcard : #{w ∈ G.neighborFinset u | G.Adj w v} = 1 := by
    rw [Finset.card_eq_one]
    obtain ⟨w0, ⟨hw0u, hw0v⟩, hw0uniq⟩ := hfriend u v huv
    refine ⟨w0, ?_⟩
    ext w
    simp only [Finset.mem_filter, G.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hwu, hwv⟩
      exact hw0uniq w ⟨hwu.symm, hwv⟩
    · rintro rfl
      exact ⟨hw0u.symm, hw0v⟩
  rw [hcard, Nat.cast_one]

/-- **The Friendship matrix equation.**
For a finite friendship graph, the squared adjacency matrix over `ℝ` equals the all-ones
matrix plus the diagonal matrix `diag(deg v − 1)`:

  `A² = J + diag(deg v − 1)`.
-/
theorem adjMatrix_sq_eq (hfriend : Friendship G) :
    (G.adjMatrix ℝ) ^ 2
      = Matrix.of (fun _ _ => (1 : ℝ)) + Matrix.diagonal (fun v => (G.degree v : ℝ) - 1) := by
  ext u v
  by_cases h : u = v
  · subst h
    rw [adjMatrix_sq_diag, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply_eq]
    ring
  · rw [adjMatrix_sq_offdiag G hfriend h, Matrix.add_apply, Matrix.of_apply,
      Matrix.diagonal_apply_ne _ h]
    ring

/-- **The Friendship matrix equation, regular form.**
If the friendship graph is `k`-regular, then `A² = J + (k − 1)·I`, the classical form used
in the spectral proof. -/
theorem adjMatrix_sq_eq_of_regular (hfriend : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) :
    (G.adjMatrix ℝ) ^ 2
      = Matrix.of (fun _ _ => (1 : ℝ)) + ((k : ℝ) - 1) • (1 : Matrix V V ℝ) := by
  rw [adjMatrix_sq_eq G hfriend]
  congr 1
  ext u v
  by_cases h : u = v
  · subst h
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, hreg u]
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply, Matrix.one_apply_ne h,
      smul_eq_mul, mul_zero]

end FriendshipMatrixEquation

-- Non-vacuity note: the friendship hypothesis is satisfiable (e.g. the triangle K₃ and the
-- windmill/friendship graphs), so these results are genuine implications, not vacuous.
