/-
# Friendship Theorem — the vertex-count identity `n = k² − k + 1`

For a `k`-regular friendship graph `G` on `n = |V|` vertices, the friendship matrix
equation `A² = J + (k − 1)·I` (`FriendshipMatrixEquation.adjMatrix_sq_eq_of_regular`)
forces the classical vertex-count identity

  n = k² − k + 1        (equivalently k² = n + k − 1).

The proof evaluates both sides of the matrix identity on the all-ones vector `1`,
using regularity twice on the left (`A · 1 = k · 1`, so `A² · 1 = A · (k · 1) = k² · 1`)
and the structure of `J` and `I` on the right (`J · 1 = n · 1`, `I · 1 = 1`), then reads
off the coefficient at any fixed vertex.

## Main mathlib API used
* `SimpleGraph.adjMatrix_mulVec_const_apply_of_regular` — `(A *ᵥ const a) v = d * a` for
  `d`-regular `G`
* `Matrix.mulVec_mulVec`, `Matrix.add_mulVec`, `Matrix.smul_mulVec`, `Matrix.one_mulVec`
* `Matrix.mulVec`, `Matrix.dotProduct`, `Matrix.of_apply`, `Finset.sum_const`,
  `Finset.card_univ`
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Propositio.Combinatorics.FriendshipMatrixEquation

namespace FriendshipVertexCount

open SimpleGraph Finset Matrix FriendshipMatrixEquation

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Vertex-count identity for regular friendship graphs.**
If `G` is a `k`-regular friendship graph on `n = |V|` vertices, then `n = k² − k + 1`. -/
theorem friendship_card_eq (hfriend : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) [Nonempty V] :
    (Fintype.card V : ℤ) = (k : ℤ) ^ 2 - k + 1 := by
  classical
  obtain ⟨v0⟩ : Nonempty V := inferInstance
  -- Step 1: `A *ᵥ const 1 = const k`, as a function `V → ℝ` (row sums are `k` by regularity).
  have hA1 : (G.adjMatrix ℝ) *ᵥ (Function.const V (1 : ℝ)) = Function.const V (k : ℝ) := by
    funext v
    rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (G := G) hreg]
    simp
  -- Step 2: `A *ᵥ (A *ᵥ const 1) = const (k^2)`, applying regularity a second time.
  have hA2 : (G.adjMatrix ℝ) *ᵥ ((G.adjMatrix ℝ) *ᵥ (Function.const V (1 : ℝ)))
      = Function.const V ((k : ℝ) ^ 2) := by
    rw [hA1]
    funext v
    rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (G := G) hreg]
    simp only [Function.const_apply]
    ring
  -- Step 3: repackage as `A² *ᵥ const 1 = const (k^2)`.
  have hsq : ((G.adjMatrix ℝ) ^ 2) *ᵥ (Function.const V (1 : ℝ))
      = Function.const V ((k : ℝ) ^ 2) := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
    exact hA2
  -- Step 4: substitute the friendship matrix equation `A² = J + (k − 1)·I`.
  rw [FriendshipMatrixEquation.adjMatrix_sq_eq_of_regular G hfriend hreg,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hsq
  -- Step 5: evaluate the resulting function equation at the fixed vertex `v0`.
  have hval := congrFun hsq v0
  have hJ : (Matrix.of (fun _ _ : V => (1 : ℝ)) *ᵥ Function.const V (1 : ℝ)) v0
      = (Fintype.card V : ℝ) := by
    simp [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.const_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Function.const_apply, smul_eq_mul, mul_one] at hval
  rw [hJ] at hval
  -- `hval : (Fintype.card V : ℝ) + ((k : ℝ) - 1) = (k : ℝ) ^ 2`
  have hreal : (Fintype.card V : ℝ) = (k : ℝ) ^ 2 - k + 1 := by linarith
  have hcast : ((Fintype.card V : ℤ) : ℝ) = (((k : ℤ) ^ 2 - k + 1 : ℤ) : ℝ) := by
    push_cast
    linarith [hreal]
  exact_mod_cast hcast

end FriendshipVertexCount

-- Non-vacuity: the triangle `K₃` is a `2`-regular friendship graph on `3` vertices, so
-- `friendship_card_eq` is a genuine (non-vacuous) implication: `3 = 2² − 2 + 1`. (A machine-
-- checked `example` instance is a natural follow-up; it needs the `Decidable`/`DecidableRel`
-- instances for `Friendship`/`IsRegularOfDegree` on a concrete finite graph.)
