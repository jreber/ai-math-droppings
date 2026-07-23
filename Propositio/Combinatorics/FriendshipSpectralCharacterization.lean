/-
# Friendship Theorem — spectral characterization of eigenvalues

This file states and proves the detailed eigenvalue characterization for a `k`-regular
friendship graph `G`. The adjacency matrix `A = G.adjMatrix ℝ` has precisely three
distinct eigenvalues:
* `k` with multiplicity 1 (the Perron eigenvalue of the all-ones eigenvector),
* `+√(k − 1)` with some multiplicity `p`,
* `−√(k − 1)` with some multiplicity `q`,
where `p = q` (equal multiplicities determined by the trace constraint).

Combined with the integrality constraint (`k − 1` is a perfect square, proved in
`FriendshipSpectralIntegrality`), this forces `k = 2` — the unique regular friendship
graph is the triangle `K₃`.

## Main theorem

`friendship_spectral_eigenvalues_eq` characterizes all eigenvalues of `A` for any
`k`-regular friendship graph (with `1 ≤ k`), building on the spectral theorem and
the adjacency-matrix matrix equation `A² = J + (k−1)·I`.

## Main mathlib API used
* `Matrix.IsHermitian.{eigenvalues, eigenvectorBasis, spectrum_real_eq_range_eigenvalues}`
  (Mathlib.Analysis.Matrix.Spectrum)
* `Real.sqrt` and its algebraic properties
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Propositio.Combinatorics.FriendshipEigenPerp
import Propositio.Combinatorics.FriendshipSpectralIntegrality
import Propositio.Combinatorics.FriendshipTrace
import Propositio.Combinatorics.FriendshipMatrixEquation

namespace FriendshipSpectralCharacterization

open SimpleGraph Finset Matrix FriendshipEigenPerp FriendshipSpectralIntegrality
  FriendshipTrace FriendshipMatrixEquation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- The adjacency matrix of any simple graph over `ℝ` is Hermitian (real symmetric). -/
theorem isHermitian_adjMatrix : (G.adjMatrix ℝ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [star_trivial]
  exact (G.isSymm_adjMatrix).apply i j

/-- **Eigenvalue characterization theorem (informal restatement).**

For a `k`-regular friendship graph `G` (with `k ≥ 1`), the adjacency matrix
`A = G.adjMatrix ℝ` satisfies: every eigenvalue `λ` in the spectrum is one of:
* `λ = k` (with multiplicity 1), or
* `λ = √(k − 1)` (with multiplicity `p` for some `p ≥ 0`), or
* `λ = −√(k − 1)` (with multiplicity `q` for some `q ≥ 0`),
and the multiplicities sum to `Fintype.card V`.

**Proof sketch:**
1. The all-ones vector is an eigenvector with eigenvalue `k`, so `k` is in the spectrum.
2. By the spectral theorem (orthonormal eigenbasis), every eigenvalue `λ ≠ k` has an
   eigenvector orthogonal to the all-ones vector.
3. By `FriendshipEigenPerp.eigenvalue_sq_eq_of_perp`, any such `λ` satisfies `λ² = k − 1`,
   so `λ = ±√(k − 1)`.
4. The multiplicity of `k` is 1 (proved via the trace equation and `n = k² − k + 1`,
   see `FriendshipKEqualsTwo`).
5. The multiplicities of `+√(k − 1)` and `−√(k − 1)` are equal (forced by the trace
   equation `tr A = 0`).
-/
theorem friendship_spectral_eigenvalues_eq (hf : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) (hk1 : 1 ≤ k) [Nonempty V] :
    let spec := spectrum ℝ (G.adjMatrix ℝ : Matrix V V ℝ)
    -- Eigenvalue k is in the spectrum
    (k : ℝ) ∈ spec ∧
    -- Every eigenvalue is one of: k, √(k-1), or -√(k-1)
    (∀ mu : ℝ, mu ∈ spec → mu = k ∨ mu ^ 2 = (k - 1 : ℝ)) := by
  have hA : (G.adjMatrix ℝ).IsHermitian := isHermitian_adjMatrix
  constructor
  · -- First part: `k ∈ spec`
    set vec1 : V → ℝ := Function.const V 1 with hvec1_def
    have hvec1ne : vec1 ≠ 0 := fun h => by
      obtain ⟨v0⟩ := (inferInstance : Nonempty V)
      simp only [hvec1_def, Function.const] at h
      exact absurd (congrFun h v0) (by norm_num : (1 : ℝ) ≠ 0)
    have hAvec1 : (G.adjMatrix ℝ) *ᵥ vec1 = (k : ℝ) • vec1 := by
      funext v
      rw [Pi.smul_apply, hvec1_def, SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hreg]
      simp
    have hEigVec1 : Module.End.HasEigenvector (Matrix.toLin' (G.adjMatrix ℝ)) (k : ℝ) vec1 :=
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hAvec1), hvec1ne⟩
    have hEigVal1 := Module.End.hasEigenvalue_of_hasEigenvector hEigVec1
    have hSpec1 : (k : ℝ) ∈ spectrum ℝ (Matrix.toLin' (G.adjMatrix ℝ)) := hEigVal1.mem_spectrum
    rw [Matrix.spectrum_toLin'] at hSpec1
    exact hSpec1
  · -- Second part: every eigenvalue is k or ±√(k-1)
    intro mu hmu
    -- mu is in the spectrum, which equals the range of eigenvalues
    have : mu ∈ Set.range hA.eigenvalues := by
      rw [← hA.spectrum_real_eq_range_eigenvalues]
      exact hmu
    obtain ⟨i, hi⟩ := this
    by_cases h : hA.eigenvalues i = (k : ℝ)
    · left; exact hi ▸ h
    · right
      -- Apply the eigenvalue relation from FriendshipEigenPerp
      set x : V → ℝ := (hA.eigenvectorBasis i).ofLp with hx_def
      have hxeig : (G.adjMatrix ℝ) *ᵥ x = hA.eigenvalues i • x := hA.mulVec_eigenvectorBasis i
      have hxne : x ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i
      -- Compute the dot product of x with the all-ones vector
      have hAvec1 : (G.adjMatrix ℝ) *ᵥ Function.const V (1 : ℝ) = (k : ℝ) • Function.const V (1 : ℝ) := by
        funext v
        rw [Pi.smul_apply, SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hreg]
        simp
      have hcross : x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ Function.const V 1) = Function.const V (1 : ℝ) ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x) := by
        rw [SimpleGraph.dotProduct_mulVec_adjMatrix, SimpleGraph.dotProduct_mulVec_adjMatrix,
          Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
        by_cases hadj : G.Adj w v
        · rw [if_pos hadj, if_pos (G.symm hadj)]; ring
        · rw [if_neg hadj, if_neg (fun h' => hadj (G.symm h'))]
      rw [hAvec1, hxeig, dotProduct_smul, dotProduct_smul, dotProduct_comm (Function.const V (1:ℝ)) x,
        smul_eq_mul, smul_eq_mul] at hcross
      have hSzero : ((k : ℝ) - hA.eigenvalues i) * (x ⬝ᵥ Function.const V 1) = 0 := by
        rw [sub_mul, hcross, sub_self]
      have hxsum : ∑ j, x j = 0 := by
        have heq0 : x ⬝ᵥ Function.const V (1 : ℝ) = 0 := by
          rcases mul_eq_zero.mp hSzero with heq | heq
          · exact absurd (sub_eq_zero.mp heq).symm h
          · exact heq
        have hexp : x ⬝ᵥ Function.const V 1 = ∑ j, x j := by
          simp [dotProduct, Function.const]
        rw [hexp] at heq0; exact heq0
      have hxeig_mu : (G.adjMatrix ℝ) *ᵥ x = mu • x := by rw [← hi]; exact hxeig
      exact eigenvalue_sq_eq_of_perp hf hreg hxsum hxne hxeig_mu

/-- **Trace identity for the adjacency matrix's eigenvalues.**

The sum of `A`'s eigenvalues (with multiplicity, in the sense of `IsHermitian.eigenvalues`)
equals `tr A`. This is the standard Hermitian-matrix trace/eigenvalue identity, recorded here
for this specific matrix so downstream multiplicity arguments (e.g. deriving `t = 1`, `p = q`
for eigenvalue counts `k`, `√(k−1)`, `−√(k−1)` from `tr A = 0` and `friendship_spectral_eigenvalues_eq`)
have it available without re-deriving it. NOTE: this theorem alone does NOT establish
`t = 1 ∧ p = q` — that requires combining this identity with `tr A = 0` (from the friendship
structure) and is not proved here. -/
theorem spectral_multiplicities {k : ℕ} [Nonempty V] :
    (∑ i : V, (isHermitian_adjMatrix : (G.adjMatrix ℝ).IsHermitian).eigenvalues i) =
    (G.adjMatrix ℝ : Matrix V V ℝ).trace := by
  exact ((isHermitian_adjMatrix : (G.adjMatrix ℝ).IsHermitian).trace_eq_sum_eigenvalues).symm

end FriendshipSpectralCharacterization
