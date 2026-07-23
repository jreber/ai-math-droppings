/-
# Friendship Theorem — the restricted eigenvalue relation on `1⊥`

Building on `FriendshipMatrixEquation.adjMatrix_sq_eq_of_regular`
(`A² = J + (k − 1)·I` for a `k`-regular friendship graph), this file records the
action of `A²` on the orthogonal complement of the all-ones vector.

If `x : V → ℝ` satisfies `∑ i, x i = 0` (i.e. `x ⊥ 1`), then `J.mulVec x = 0`
(each entry is `∑ j, x j = 0`), so from `A² = J + (k − 1)·I`:

  `(A²).mulVec x = (k − 1) • x`.

This is the spectral heart of the Friendship Theorem: on `1⊥` the operator `A²`
acts as the scalar `k − 1`. The eigenvalue corollary `eigenvalue_sq_eq_of_perp`
deduces that any real eigenvalue `λ` of `A` with an eigenvector orthogonal to `1`
satisfies `λ² = k − 1` — the algebraic constraint that (with the trace / spectral
argument, not formalized here) forces `k = 2`.

## Main mathlib API used
* `Matrix.add_mulVec`, `Matrix.smul_mulVec`, `Matrix.one_mulVec`
* `Matrix.mulVec`, `dotProduct` (to evaluate `J.mulVec x`)
* `Matrix.mulVec_mulVec`, `Matrix.mulVec_smul` (for the `A²` eigen-computation)
* `sub_smul`, `smul_eq_zero`
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Propositio.Combinatorics.FriendshipMatrixEquation

namespace FriendshipEigenPerp

open SimpleGraph Finset Matrix FriendshipMatrixEquation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **The all-ones matrix annihilates `1⊥`.** If `∑ i, x i = 0`, then each entry of
`J.mulVec x` is `∑ j, x j = 0`, hence `J.mulVec x = 0`. -/
theorem allOnes_mulVec_of_sum_zero {x : V → ℝ} (hx : ∑ i, x i = 0) :
    (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix V V ℝ).mulVec x = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Pi.zero_apply]
  exact hx

/-- **TARGET A — the restricted eigenvalue relation.**
For a `k`-regular friendship graph and any vector `x ⊥ 1` (`∑ i, x i = 0`),
the squared adjacency matrix acts on `x` as the scalar `k − 1`:

  `(A²).mulVec x = (k − 1) • x`.
-/
theorem adjMatrix_sq_mulVec_of_sum_zero (hf : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) {x : V → ℝ} (hx : ∑ i, x i = 0) :
    (G.adjMatrix ℝ ^ 2).mulVec x = (k - 1 : ℝ) • x := by
  rw [adjMatrix_sq_eq_of_regular G hf hreg, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, allOnes_mulVec_of_sum_zero hx, zero_add]

/-- **TARGET B (eigenvalue corollary) — `λ² = k − 1`.**
If `λ` is a real eigenvalue of the adjacency matrix `A` of a `k`-regular friendship
graph, witnessed by a nonzero eigenvector `y` orthogonal to the all-ones vector
(`∑ i, y i = 0`), then `λ² = k − 1`.

This is the algebraic constraint on the restricted spectrum that (together with the
trace / integrality argument, not formalized here) forces `k = 2`. -/
theorem eigenvalue_sq_eq_of_perp (hf : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) {y : V → ℝ} (hy0 : ∑ i, y i = 0) (hyne : y ≠ 0)
    {lam : ℝ} (heig : (G.adjMatrix ℝ).mulVec y = lam • y) :
    lam ^ 2 = (k - 1 : ℝ) := by
  -- Compute `A².mulVec y` two ways.
  have hAsq : (G.adjMatrix ℝ ^ 2).mulVec y = lam ^ 2 • y := by
    rw [pow_two, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, heig, smul_smul, ← pow_two]
  have hval := adjMatrix_sq_mulVec_of_sum_zero hf hreg hy0
  rw [hAsq] at hval
  -- `lam² • y = (k − 1) • y`, so `(lam² − (k − 1)) • y = 0`; since `y ≠ 0`, the scalar is `0`.
  have hzero : (lam ^ 2 - (k - 1 : ℝ)) • y = 0 := by
    rw [sub_smul, hval, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hyne

end FriendshipEigenPerp
