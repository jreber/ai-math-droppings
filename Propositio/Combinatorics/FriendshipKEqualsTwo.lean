/-
# Friendship Theorem — the spectral finish: a regular friendship graph has `k = 2`

This is the capstone integrality step of the classical (Erdős–Rényi–Sós) Friendship
Theorem. Building on the merged bricks

* `FriendshipMatrixEquation.adjMatrix_sq_eq_of_regular` : `A² = J + (k−1)·I`,
* `FriendshipVertexCount.friendship_card_eq` : `n = k² − k + 1`,
* `FriendshipTrace.{trace_adjMatrix_eq_zero, trace_adjMatrix_sq_of_regular}` :
  `tr A = 0` and `tr A² = n·k`,
* `FriendshipEigenPerp.eigenvalue_sq_eq_of_perp` : eigenvectors `⊥ 1` have `λ² = k − 1`,

we prove that a `k`-regular friendship graph (with `1 ≤ k`, i.e. the "no universal
vertex" spectral branch) must have

  `k = 2`

— so the only regular friendship graph is the triangle `K₃` (windmill of order one).

## Proof

`A = G.adjMatrix ℝ` is real symmetric, so mathlib's spectral theorem gives an
orthonormal eigenbasis with real eigenvalues `λ i`.

* The all-ones vector is an eigenvector with eigenvalue `k`, so `k` is among the `λ i`.
* Any *other* eigenvalue is (its eigenvector being `⊥ 1`) a root of `λ² = k − 1`, hence
  `± s` where `s = √(k−1)`.

Let `t` be the multiplicity of the eigenvalue `k`, and `p`, `q` the multiplicities of
`+s`, `−s`. Two trace identities plus the dimension count pin everything down:

* `tr A² = n·k`  gives, since every non-`k` eigenvalue squares to `k − 1`,
  `t·k² + (n − t)·(k − 1) = n·k`, which — using `n = k² − k + 1` — forces `t = 1`
  (**the Perron eigenvalue is simple**, with no Perron–Frobenius machinery required).
* `tr A = 0` with `t = 1` gives `k = (q − p)·s`. Squaring: `k² = (q − p)²·(k − 1)`, an
  **integer** identity. Hence `k − 1 ∣ k²`; but `gcd(k − 1, k) = 1`, so
  `(k − 1)·((q−p)² − k − 1) = 1`, forcing `k − 1 = 1`, i.e. `k = 2`.

The `k = 1` case is impossible (`n = 1`, but a `1`-regular graph needs a neighbour), so
the full statement holds for all `1 ≤ k`.

## Main mathlib API used
* `Matrix.IsHermitian.{eigenvalues, eigenvectorBasis, mulVec_eigenvectorBasis,
  spectral_theorem, trace_eq_sum_eigenvalues, spectrum_real_eq_range_eigenvalues}`
* `Unitary.{conjStarAlgAut_apply, coe_star_mul_self}`, `Matrix.trace_mul_cycle`,
  `Matrix.diagonal_mul_diagonal`, `Matrix.trace_diagonal`
* `Module.End.{HasEigenvector, hasEigenvalue_of_hasEigenvector, HasEigenvalue.mem_spectrum}`,
  `Matrix.spectrum_toLin'`
* `Int.isUnit_iff`, `isUnit_of_mul_eq_one`, `SimpleGraph.degree_lt_card_verts`
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic.Linarith
import Propositio.Combinatorics.FriendshipEigenPerp
import Propositio.Combinatorics.FriendshipTrace
import Propositio.Combinatorics.FriendshipMatrixEquation
import Propositio.Combinatorics.FriendshipVertexCount
import Propositio.Combinatorics.FriendshipRegular

namespace FriendshipKEqualsTwo

open SimpleGraph Finset Matrix
  FriendshipMatrixEquation FriendshipEigenPerp FriendshipTrace FriendshipVertexCount

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

/-- **Sum of squared eigenvalues = trace of the square.** For any real Hermitian matrix
`A`, `tr(A²) = ∑ λ_i²` where `λ` are its (real) eigenvalues, via the unitary
diagonalization `A = U · diag λ · U*` and cyclicity of the trace. -/
theorem trace_sq_eq_sum_eigenvalues_sq (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, (hA.eigenvalues i) ^ 2 := by
  rw [sq A]
  conv_lhs => rw [hA.spectral_theorem, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **The Friendship Theorem — spectral `k = 2` finish.**
A `k`-regular friendship graph with `1 ≤ k` (the "no universal vertex" branch) has
`k = 2`; i.e. the only regular friendship graph is the triangle. -/
theorem k_eq_two (hf : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) (hk1 : 1 ≤ k) [Nonempty V] : k = 2 := by
  classical
  -- Dispose of `k = 1`: then `n = 1`, but a `1`-regular graph needs a neighbour.
  rcases eq_or_lt_of_le hk1 with hk1' | hk2
  · exfalso
    obtain ⟨v0⟩ := (inferInstance : Nonempty V)
    have hcard : (Fintype.card V : ℤ) = 1 := by
      rw [friendship_card_eq G hf hreg]; rw [← hk1']; ring
    have hcardnat : Fintype.card V = 1 := by exact_mod_cast hcard
    have hdeg : G.degree v0 = k := hreg v0
    have hlt : G.degree v0 < Fintype.card V := G.degree_lt_card_verts v0
    omega
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
  -- `k` is an eigenvalue of `A` (witnessed by `vec1`).
  have hEigVec1 : Module.End.HasEigenvector (Matrix.toLin' (G.adjMatrix ℝ)) (k : ℝ) vec1 :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hAvec1), hvec1ne⟩
  have hEigVal1 := Module.End.hasEigenvalue_of_hasEigenvector hEigVec1
  have hSpec1 : (k : ℝ) ∈ spectrum ℝ (Matrix.toLin' (G.adjMatrix ℝ)) := hEigVal1.mem_spectrum
  have hSpecA : (k : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ) := by
    rw [Matrix.spectrum_toLin'] at hSpec1; exact hSpec1
  obtain ⟨i0, hi0⟩ : (k : ℝ) ∈ Set.range hHerm.eigenvalues := by
    rw [← hHerm.spectrum_real_eq_range_eigenvalues]; exact hSpecA
  -- Every OTHER eigenvalue `λ ≠ k` satisfies `λ² = k − 1`.
  have hOther : ∀ i : V, hHerm.eigenvalues i ≠ (k : ℝ) →
      hHerm.eigenvalues i ^ 2 = (k : ℝ) - 1 := by
    intro i hine
    set x : V → ℝ := (hHerm.eigenvectorBasis i).ofLp with hx_def
    have hxeig : G.adjMatrix ℝ *ᵥ x = hHerm.eigenvalues i • x := hHerm.mulVec_eigenvectorBasis i
    have hxne : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 <| hHerm.eigenvectorBasis.orthonormal.ne_zero i
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
  -- Split `V` into `T = {λ = k}` and `Tc = {λ ≠ k}`.
  set T := Finset.univ.filter (fun i : V => hHerm.eigenvalues i = (k : ℝ)) with hT_def
  set Tc := Finset.univ.filter (fun i : V => hHerm.eigenvalues i ≠ (k : ℝ)) with hTc_def
  -- `√(k-1) > 0` since `k ≥ 2`.
  have hkm1pos : (0:ℝ) < (k:ℝ) - 1 := by
    have : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    linarith
  set S := Real.sqrt ((k:ℝ) - 1) with hS_def
  have hSpos : 0 < S := Real.sqrt_pos.mpr hkm1pos
  have hSsq : S ^ 2 = (k:ℝ) - 1 := Real.sq_sqrt hkm1pos.le
  -- ── Trace-A² relation and the multiplicity `t = 1` ────────────────────────────
  -- `∑_{i∈T} λ² = |T|·k²`, `∑_{i∈Tc} λ² = |Tc|·(k−1)`.
  have hTsq : ∑ i ∈ T, hHerm.eigenvalues i ^ 2 = (T.card : ℝ) * (k:ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hTcsq : ∑ i ∈ Tc, hHerm.eigenvalues i ^ 2 = (Tc.card : ℝ) * ((k:ℝ) - 1) := by
    rw [Finset.sum_congr rfl (fun i hi => hOther i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsumSqSplit : ∑ i ∈ T, hHerm.eigenvalues i ^ 2
      + ∑ i ∈ Tc, hHerm.eigenvalues i ^ 2 = ∑ i, hHerm.eigenvalues i ^ 2 :=
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => hHerm.eigenvalues i = (k : ℝ)) _
  have htrSq : (∑ i, hHerm.eigenvalues i ^ 2) = (Fintype.card V : ℝ) * k := by
    rw [← trace_sq_eq_sum_eigenvalues_sq (G.adjMatrix ℝ) hHerm]
    exact trace_adjMatrix_sq_of_regular hreg
  -- card decomposition `|V| = |T| + |Tc|`.
  have hcardV : (T.card : ℝ) + (Tc.card : ℝ) = (Fintype.card V : ℝ) := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (p := fun i => hHerm.eigenvalues i = (k : ℝ))
    rw [Finset.card_univ] at this
    exact_mod_cast this
  -- Vertex count `n = k² − k + 1`, as a real equation.
  have hNval : (Fintype.card V : ℝ) = (k:ℝ) ^ 2 - k + 1 := by
    have h := friendship_card_eq G hf hreg
    have : ((Fintype.card V : ℤ) : ℝ) = (((k : ℤ) ^ 2 - k + 1 : ℤ) : ℝ) := by
      rw [h]
    push_cast at this
    linarith [this]
  -- Solve for the multiplicity: `t·(k²−k+1) = n`, and `n = k²−k+1`, so `t = 1`.
  have hB : (T.card : ℝ) * (k:ℝ) ^ 2 + (Tc.card : ℝ) * ((k:ℝ) - 1)
      = (Fintype.card V : ℝ) * k := by
    rw [← hTsq, ← hTcsq, hsumSqSplit, htrSq]
  have hTeq : (T.card : ℝ) * ((k:ℝ) ^ 2 - k + 1) = (Fintype.card V : ℝ) := by
    have hTc' : (Tc.card : ℝ) = (Fintype.card V : ℝ) - (T.card : ℝ) := by linarith [hcardV]
    rw [hTc'] at hB
    linear_combination hB
  have hNpos : (0:ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have htcard1 : T.card = 1 := by
    have hmul : (T.card : ℝ) * (Fintype.card V : ℝ) = (Fintype.card V : ℝ) := by
      rw [← hNval] at hTeq; exact hTeq
    have : (T.card : ℝ) = 1 :=
      mul_right_cancel₀ (ne_of_gt hNpos) (by rw [hmul, one_mul])
    exact_mod_cast this
  -- ── Trace-A relation, sign split, and the final integrality squeeze ───────────
  -- Every `i ∈ Tc` has `λ = S` or `λ = −S`.
  have hTcVal : ∀ i ∈ Tc, hHerm.eigenvalues i = S ∨ hHerm.eigenvalues i = -S := by
    intro i hi
    have hine : hHerm.eigenvalues i ≠ (k:ℝ) := (Finset.mem_filter.mp hi).2
    have hsq := hOther i hine
    have hfact : (hHerm.eigenvalues i - S) * (hHerm.eigenvalues i + S) = 0 := by
      nlinarith [hsq, hSsq]
    rcases mul_eq_zero.mp hfact with h | h
    · left; linarith [sub_eq_zero.mp h]
    · right; linarith [h]
  set P := Tc.filter (fun i => hHerm.eigenvalues i = S) with hP_def
  set Q := Tc.filter (fun i => hHerm.eigenvalues i = -S) with hQ_def
  have hPQsplit : ∑ i ∈ P, hHerm.eigenvalues i + ∑ i ∈ Q, hHerm.eigenvalues i
      = ∑ i ∈ Tc, hHerm.eigenvalues i := by
    have hPQ_eq : Q = Tc.filter (fun i => ¬ hHerm.eigenvalues i = S) := by
      apply Finset.filter_congr
      intro i hi
      have := hTcVal i hi
      constructor
      · intro h he; rw [h] at he
        exact absurd (he.symm.trans he) (by nlinarith [hSpos])
      · intro hne
        rcases this with h | h
        · exact absurd h hne
        · exact h
    rw [hPQ_eq]
    exact Finset.sum_filter_add_sum_filter_not Tc (fun i => hHerm.eigenvalues i = S) _
  have hPsum : ∑ i ∈ P, hHerm.eigenvalues i = (P.card : ℝ) * S := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hQsum : ∑ i ∈ Q, hHerm.eigenvalues i = (Q.card : ℝ) * (-S) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hTsum : ∑ i ∈ T, hHerm.eigenvalues i = (T.card : ℝ) * k := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsumSplit : ∑ i ∈ T, hHerm.eigenvalues i + ∑ i ∈ Tc, hHerm.eigenvalues i
      = ∑ i, hHerm.eigenvalues i :=
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => hHerm.eigenvalues i = (k : ℝ)) _
  have htr0 : (∑ i, hHerm.eigenvalues i) = 0 := by
    have h := hHerm.trace_eq_sum_eigenvalues
    rw [trace_adjMatrix_eq_zero] at h
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    exact h.symm
  -- `t·k + (p − q)·S = 0`, and with `t = 1`: `k = (q − p)·S`.
  have hmainA : (T.card : ℝ) * k + ((P.card : ℝ) - (Q.card : ℝ)) * S = 0 := by
    have hchain : (T.card : ℝ) * k + ((P.card:ℝ) * S + (Q.card:ℝ) * (-S)) = 0 := by
      rw [← hPsum, ← hQsum, hPQsplit, ← hTsum, hsumSplit, htr0]
    nlinarith [hchain]
  have hkeq : (k:ℝ) = ((Q.card : ℝ) - (P.card : ℝ)) * S := by
    rw [htcard1] at hmainA
    push_cast at hmainA
    linarith [hmainA]
  -- Square: `k² = (q − p)²·(k − 1)`, an INTEGER identity.
  have hsqR : (k:ℝ) ^ 2 = ((Q.card : ℝ) - (P.card : ℝ)) ^ 2 * ((k:ℝ) - 1) := by
    have : (k:ℝ) ^ 2 = (((Q.card : ℝ) - (P.card : ℝ)) * S) ^ 2 := by rw [← hkeq]
    rw [this, mul_pow, hSsq]
  -- Transfer to `ℤ`.
  have hsqZ : (k : ℤ) ^ 2 = ((Q.card : ℤ) - (P.card : ℤ)) ^ 2 * ((k : ℤ) - 1) := by
    have hcast : ((k : ℤ) ^ 2 : ℝ)
        = (((Q.card : ℤ) - (P.card : ℤ)) ^ 2 * ((k : ℤ) - 1) : ℤ) := by
      push_cast
      rw [hsqR]
    exact_mod_cast hcast
  -- `(k − 1)·((q − p)² − k − 1) = 1`, so `k − 1` is a unit; with `k ≥ 2`, `k − 1 = 1`.
  set w : ℤ := (Q.card : ℤ) - (P.card : ℤ) with hw_def
  have hfactor : ((k : ℤ) - 1) * (w ^ 2 - (k : ℤ) - 1) = 1 := by
    linear_combination -hsqZ
  have hunit : IsUnit ((k : ℤ) - 1) := IsUnit.of_mul_eq_one _ hfactor
  have hk2Z : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk2
  rcases Int.isUnit_iff.mp hunit with h | h
  · -- `k − 1 = 1`
    have : (k : ℤ) = 2 := by omega
    exact_mod_cast this
  · -- `k − 1 = −1` impossible since `k ≥ 2`
    omega

end FriendshipKEqualsTwo
