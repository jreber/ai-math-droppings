/-
# Friendship Theorem — spectral integrality: `k − 1` is a perfect square

The classical spectral-integrality step of the Friendship Theorem. For a `k`-regular
friendship graph `G` (any `k ≥ 1`; this is the "no universal vertex" spectral branch),
we show `k − 1` is a perfect square:

  `∃ m : ℕ, k − 1 = m ^ 2`.

## Proof sketch

`A = G.adjMatrix ℝ` is a real symmetric (Hermitian) matrix, so mathlib's spectral
theorem (`Matrix.IsHermitian.eigenvectorBasis`, `.eigenvalues`) gives an orthonormal
eigenbasis of `A` with real eigenvalues.

* Since `A` is `k`-regular, the all-ones vector `1` is an eigenvector with eigenvalue
  `k`; hence `k` is *among* the spectral eigenvalues (`k = hA.eigenvalues i₀` for some
  `i₀`).
* For any *other* index `i` with `hA.eigenvalues i ≠ k`, the corresponding eigenvector
  is automatically orthogonal to `1` (distinct eigenvalues of a symmetric operator have
  orthogonal eigenvectors — proved here directly via the adjacency-matrix dot-product
  symmetry, not via general Hermitian adjoint machinery), so by
  `FriendshipEigenPerp.eigenvalue_sq_eq_of_perp`, `hA.eigenvalues i ^ 2 = k − 1`, i.e.
  `hA.eigenvalues i = ±√(k − 1)`.
* `Matrix.trace A = ∑ i, hA.eigenvalues i` (`trace_eq_sum_eigenvalues`) and
  `Matrix.trace A = 0` (`FriendshipTrace.trace_adjMatrix_eq_zero`, no self-loops).
  Splitting the sum over `{i | eigenvalues i = k}` (multiplicity `t ≥ 1`) and its
  complement (partitioned by sign of `±√(k−1)`, multiplicities `p`, `q`) gives
  `t·k + (p − q)·√(k − 1) = 0`, i.e. `t·k = (q − p)·√(k − 1)`.
* Since `t ≥ 1` and `k ≥ 1`, the left side is a nonzero integer. If `k − 1` were *not*
  a perfect square, `√(k − 1)` would be irrational (`irrational_sqrt_natCast_iff`), so
  this equation (integer = integer × irrational) forces `q − p = 0` and hence
  `t·k = 0`, contradiction. Hence `k − 1` **is** a perfect square.

## Main mathlib API used
* `Matrix.IsHermitian.{eigenvalues, eigenvectorBasis, mulVec_eigenvectorBasis,
  trace_eq_sum_eigenvalues, spectrum_real_eq_range_eigenvalues}`
  (`Mathlib.Analysis.Matrix.Spectrum`)
* `Module.End.{HasEigenvector, hasEigenvalue_of_hasEigenvector, HasEigenvalue.mem_spectrum}`,
  `Matrix.spectrum_toLin'` (to bridge matrix eigenvalue membership into the spectrum)
* `irrational_sqrt_natCast_iff : Irrational (√(n:ℝ)) ↔ ¬ IsSquare n`,
  `Irrational.ne_rational` (`Mathlib.NumberTheory.Real.Irrational`)
* `Orthonormal.ne_zero`, `WithLp.ofLp_eq_zero` (bridging `EuclideanSpace` nonzero-ness
  to the underlying function being nonzero)
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Propositio.Combinatorics.FriendshipEigenPerp
import Propositio.Combinatorics.FriendshipTrace
import Propositio.Combinatorics.FriendshipMatrixEquation

namespace FriendshipSpectralIntegrality

open SimpleGraph Finset Matrix FriendshipMatrixEquation FriendshipEigenPerp FriendshipTrace

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- The adjacency matrix of any simple graph over `ℝ` is Hermitian (real symmetric). -/
theorem isHermitian_adjMatrix : (G.adjMatrix ℝ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [star_trivial]
  exact (G.isSymm_adjMatrix).apply i j

omit [DecidableEq V] in
/-- **Adjoint symmetry.** For the (symmetric) adjacency matrix, the dot product satisfies
the adjoint identity `x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x)`. -/
theorem dotProduct_mulVec_comm (x y : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = y ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by
  rw [SimpleGraph.dotProduct_mulVec_adjMatrix, SimpleGraph.dotProduct_mulVec_adjMatrix,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  by_cases h : G.Adj w v
  · rw [if_pos h, if_pos (G.symm h)]; ring
  · rw [if_neg h, if_neg (fun h' => h (G.symm h'))]

/-- **Main theorem — spectral integrality.**
For a `k`-regular friendship graph with `k ≥ 1`, `k − 1` is a perfect square. -/
theorem k_sub_one_isSquare (hf : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) (hk1 : 1 ≤ k) [Nonempty V] :
    ∃ m : ℕ, k - 1 = m ^ 2 := by
  classical
  rcases eq_or_lt_of_le hk1 with hk1' | hk2
  · -- Trivial case `k = 1`: `k − 1 = 0 = 0²`.
    exact ⟨0, by rw [← hk1']; norm_num⟩
  -- Main case `k ≥ 2`.
  have hHerm : (G.adjMatrix ℝ).IsHermitian := isHermitian_adjMatrix
  set vec1 : V → ℝ := Function.const V 1 with hvec1_def
  have hvec1ne : vec1 ≠ 0 := by
    obtain ⟨v0⟩ := (inferInstance : Nonempty V)
    intro hcontra
    have h0 := congrFun hcontra v0
    simp [hvec1_def] at h0
  have hAvec1 : G.adjMatrix ℝ *ᵥ vec1 = (k : ℝ) • vec1 := by
    funext v
    rw [Pi.smul_apply, hvec1_def,
      SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hreg]
    simp
  -- `k` is an eigenvalue of `A` (witnessed by `vec1`), hence lies among the spectral
  -- eigenvalues given by mathlib's Hermitian spectral theorem.
  have hEigVec1 : Module.End.HasEigenvector (Matrix.toLin' (G.adjMatrix ℝ)) (k : ℝ) vec1 :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hAvec1), hvec1ne⟩
  have hEigVal1 := Module.End.hasEigenvalue_of_hasEigenvector hEigVec1
  have hSpec1 : (k : ℝ) ∈ spectrum ℝ (Matrix.toLin' (G.adjMatrix ℝ)) := hEigVal1.mem_spectrum
  have hSpecA : (k : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ) := by
    rw [Matrix.spectrum_toLin'] at hSpec1; exact hSpec1
  obtain ⟨i0, hi0⟩ : (k : ℝ) ∈ Set.range hHerm.eigenvalues := by
    rw [← hHerm.spectrum_real_eq_range_eigenvalues]; exact hSpecA
  -- Every OTHER eigenvalue `λ ≠ k` satisfies `λ² = k − 1`.
  have hOther : ∀ i : V, hHerm.eigenvalues i ≠ (k : ℝ) → hHerm.eigenvalues i ^ 2 = (k : ℝ) - 1 := by
    intro i hine
    set x : V → ℝ := (hHerm.eigenvectorBasis i).ofLp with hx_def
    have hxeig : G.adjMatrix ℝ *ᵥ x = hHerm.eigenvalues i • x := hHerm.mulVec_eigenvectorBasis i
    have hxne : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 <| hHerm.eigenvectorBasis.orthonormal.ne_zero i
    -- `x ⬝ᵥ vec1 = 0` from the adjoint symmetry cross-computation.
    have hcross : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ vec1) = vec1 ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) :=
      dotProduct_mulVec_comm x vec1
    rw [hAvec1, hxeig, dotProduct_smul, dotProduct_smul, dotProduct_comm vec1 x,
      smul_eq_mul, smul_eq_mul] at hcross
    have hSzero : ((k : ℝ) - hHerm.eigenvalues i) * (x ⬝ᵥ vec1) = 0 := by
      rw [sub_mul, hcross, sub_self]
    have hxvec1 : x ⬝ᵥ vec1 = 0 := by
      rcases mul_eq_zero.mp hSzero with h | h
      · exact absurd (sub_eq_zero.mp h).symm hine
      · exact h
    have hsum0 : ∑ j, x j = 0 := by
      have hexp : x ⬝ᵥ vec1 = ∑ j, x j := by simp [dotProduct, hvec1_def]
      rw [hexp] at hxvec1; exact hxvec1
    exact eigenvalue_sq_eq_of_perp hf hreg hsum0 hxne hxeig
  -- Split `V` into `T = {eigenvalue = k}` and its complement.
  set T := Finset.univ.filter (fun i : V => hHerm.eigenvalues i = (k : ℝ)) with hT_def
  set Tc := Finset.univ.filter (fun i : V => hHerm.eigenvalues i ≠ (k : ℝ)) with hTc_def
  have hTsplit : ∑ i ∈ T, hHerm.eigenvalues i + ∑ i ∈ Tc, hHerm.eigenvalues i
      = ∑ i, hHerm.eigenvalues i :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => hHerm.eigenvalues i = (k : ℝ)) _
  have hTcard : 1 ≤ T.card := Finset.card_pos.mpr ⟨i0, by simp [hT_def, hi0]⟩
  have hTsum : ∑ i ∈ T, hHerm.eigenvalues i = (T.card : ℝ) * k := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  -- `√(k-1) > 0` since `k ≥ 2`.
  have hkm1pos : (0:ℝ) < (k:ℝ) - 1 := by
    have : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    linarith
  have hsqrtpos : 0 < Real.sqrt ((k:ℝ) - 1) := Real.sqrt_pos.mpr hkm1pos
  -- Every `i ∈ Tc` has `eigenvalues i = √(k-1)` or `eigenvalues i = -√(k-1)`.
  have hTcVal : ∀ i ∈ Tc, hHerm.eigenvalues i = Real.sqrt ((k:ℝ) - 1)
      ∨ hHerm.eigenvalues i = -Real.sqrt ((k:ℝ) - 1) := by
    intro i hi
    have hine : hHerm.eigenvalues i ≠ (k:ℝ) := (Finset.mem_filter.mp hi).2
    have hsq := hOther i hine
    have hfact : (hHerm.eigenvalues i - Real.sqrt ((k:ℝ)-1)) *
        (hHerm.eigenvalues i + Real.sqrt ((k:ℝ)-1)) = 0 := by
      have hsqrtsq : Real.sqrt ((k:ℝ) - 1) ^ 2 = (k:ℝ) - 1 :=
        Real.sq_sqrt hkm1pos.le
      nlinarith [hsq, hsqrtsq]
    rcases mul_eq_zero.mp hfact with h | h
    · left; linarith [sub_eq_zero.mp h]
    · right; linarith [h]
  set P := Tc.filter (fun i => hHerm.eigenvalues i = Real.sqrt ((k:ℝ) - 1)) with hP_def
  set Q := Tc.filter (fun i => hHerm.eigenvalues i = -Real.sqrt ((k:ℝ) - 1)) with hQ_def
  have hPQsplit : ∑ i ∈ P, hHerm.eigenvalues i + ∑ i ∈ Q, hHerm.eigenvalues i
      = ∑ i ∈ Tc, hHerm.eigenvalues i := by
    have hPQ_eq : Q = Tc.filter (fun i => ¬ hHerm.eigenvalues i = Real.sqrt ((k:ℝ) - 1)) := by
      apply Finset.filter_congr
      intro i hi
      have := hTcVal i hi
      constructor
      · intro h he
        rw [h] at he
        exact absurd (he.symm.trans he) (by nlinarith [hsqrtpos])
      · intro hne
        rcases this with h | h
        · exact absurd h hne
        · exact h
    rw [hPQ_eq]
    exact Finset.sum_filter_add_sum_filter_not Tc (fun i => hHerm.eigenvalues i = Real.sqrt ((k:ℝ) - 1)) _
  have hPsum : ∑ i ∈ P, hHerm.eigenvalues i = (P.card : ℝ) * Real.sqrt ((k:ℝ) - 1) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hQsum : ∑ i ∈ Q, hHerm.eigenvalues i = (Q.card : ℝ) * (-Real.sqrt ((k:ℝ) - 1)) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  -- Trace equation: `T.card * k + (P.card - Q.card) * √(k-1) = 0`.
  have htrace0 : (G.adjMatrix ℝ).trace = 0 := FriendshipTrace.trace_adjMatrix_eq_zero G
  have htraceSum : (G.adjMatrix ℝ).trace = ∑ i, (hHerm.eigenvalues i : ℝ) :=
    hHerm.trace_eq_sum_eigenvalues
  have hmain : (T.card : ℝ) * k
      + ((P.card : ℝ) - (Q.card : ℝ)) * Real.sqrt ((k:ℝ) - 1) = 0 := by
    have hchain : (T.card : ℝ) * k + ((P.card:ℝ) * Real.sqrt ((k:ℝ)-1)
        + (Q.card:ℝ) * (-Real.sqrt ((k:ℝ)-1))) = 0 := by
      rw [← hPsum, ← hQsum, hPQsplit, ← hTsum, hTsplit, ← htraceSum, htrace0]
    nlinarith [hchain]
  -- Conclude: `k − 1` must be a perfect square.
  by_contra hns
  push_neg at hns
  have hnsq : ¬ IsSquare (k - 1 : ℕ) := by
    intro ⟨m, hm⟩
    exact hns m (by rw [hm]; ring)
  have hirr : Irrational (Real.sqrt ((k - 1 : ℕ) : ℝ)) := irrational_sqrt_natCast_iff.mpr hnsq
  have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
    have h1k : (1:ℕ) ≤ k := hk1
    rw [Nat.cast_sub h1k, Nat.cast_one]
  rw [hcast] at hirr
  set c : ℤ := (Q.card : ℤ) - (P.card : ℤ) with hc_def
  have hcne : c ≠ 0 := by
    intro hc0
    have hPQeq : (P.card : ℝ) = (Q.card : ℝ) := by
      have : (Q.card : ℤ) = (P.card : ℤ) := by omega
      exact_mod_cast this.symm
    rw [hPQeq] at hmain
    have : (T.card : ℝ) * k = 0 := by linarith
    have hTpos : (0:ℝ) < (T.card : ℝ) * k := by
      have h1 : (0:ℝ) < (T.card : ℝ) := by exact_mod_cast hTcard
      have h2 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      positivity
    linarith
  have heqn : (T.card : ℝ) * k = (c : ℝ) * Real.sqrt ((k:ℝ) - 1) := by
    have hc' : (c : ℝ) = (Q.card : ℝ) - (P.card : ℝ) := by rw [hc_def]; push_cast; ring
    rw [hc']; linarith [hmain]
  have hsqrtval : Real.sqrt ((k:ℝ) - 1) = ((T.card * k : ℤ) : ℝ) / (c : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hcne : (c:ℝ) ≠ 0)]
    push_cast
    linarith [heqn]
  exact (hirr.ne_rational (T.card * k : ℤ) c) hsqrtval

end FriendshipSpectralIntegrality
