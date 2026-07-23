import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Mertens' third theorem (upper bound): `∏_{p ≤ n}(1 - 1/p) ≤ 1/log n`

Mathlib has the Euler-product machinery but no statement of the prime-product bound
`∏_{p ≤ n, p prime}(1 - 1/p) ≤ 1 / log n`.  This file fills that gap.

## Proof outline

1. **Euler product over smooth numbers.**  Using mathlib's
   `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric` with the
   completely multiplicative `f(k) = 1/k`, we get
   `P := ∏_{p < n+1} (1 - 1/p)⁻¹ = Σ'_{m ∈ (n+1)-smooth} 1/m`.
2. **Harmonic lower bound.**  Every `1 ≤ m ≤ n` is `(n+1)`-smooth, so the smooth-number sum
   dominates `harmonic n ≥ log (n+1) ≥ log n`.  Hence `log n ≤ P`.
3. **Reciprocals.**  Each factor `1 - 1/p > 0`, so `Q := ∏(1-1/p) > 0` and `P = Q⁻¹`.
   From `log n ≤ Q⁻¹` with `Q > 0`, `log n > 0`, conclude `Q ≤ 1 / log n`.

(Steps 1–2 replicate the corresponding part of `MertensReciprocalLower.key`, which derives
`log n ≤ P` locally rather than exposing it as a reusable lemma.)
-/

open Real Finset

namespace MertensProductUpper

/-- The completely multiplicative function `f(k) = 1/k`, as a monoid hom `ℕ →* ℝ`. -/
noncomputable def finv : ℕ →* ℝ where
  toFun k := (k : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by push_cast; rw [mul_inv]

@[simp] lemma finv_apply (k : ℕ) : finv k = (k : ℝ)⁻¹ := rfl

/-- For a prime `p`, `‖1/p‖ < 1`. -/
lemma norm_finv_prime_lt_one {p : ℕ} (hp : p.Prime) : ‖finv p‖ < 1 := by
  have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [finv_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_lt_one₀ hpos).mpr h1

/-- **Key bound (re-derived locally):** `log n ≤ ∏_{p ≤ n}(1 - 1/p)⁻¹` for `n ≥ 3`. -/
theorem log_le_prod (n : ℕ) (hn : 3 ≤ n) :
    Real.log n ≤ ∏ p ∈ (n + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  -- Euler product over `(n+1)`-smooth numbers.
  obtain ⟨hsum, hHS⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := finv) (fun {p} hp => norm_finv_prime_lt_one hp) (n + 1)
  set P : ℝ := ∏ p ∈ (n + 1).primesBelow, (1 - finv p)⁻¹ with hP
  -- Indicator summability and value of the smooth-number sum.
  have hsum' : Summable (fun m : (n + 1).smoothNumbers ↦ finv ↑m) := hsum.of_norm
  have hgsum : Summable (((n + 1).smoothNumbers).indicator (fun k => (k : ℝ)⁻¹)) := by
    rw [← summable_subtype_iff_indicator]
    exact hsum'
  have hPsum : ∑' k, ((n + 1).smoothNumbers).indicator (fun k => (k : ℝ)⁻¹) k = P := by
    rw [← tsum_subtype ((n + 1).smoothNumbers) (fun k => (k : ℝ)⁻¹)]
    exact hHS.tsum_eq
  -- Each indicator term on `range (n+1)` equals `1/i`.
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((n + 1).smoothNumbers).indicator (fun k => (k : ℝ)⁻¹) i = (i : ℝ)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hmem : i ∈ (n + 1).smoothNumbers
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      have hi0 : i = 0 := by
        by_contra h0
        exact hmem (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero h0) hi)
      rw [hi0]; simp
  -- `Σ_{i < n+1} 1/i = harmonic n`.
  have hsum_eq : ∑ i ∈ Finset.range (n + 1), (i : ℝ)⁻¹ = (harmonic n : ℝ) := by
    rw [Finset.sum_range_succ', harmonic]
    push_cast
    simp
  -- `harmonic n ≤ P`.
  have hharm : (harmonic n : ℝ) ≤ P := by
    have h1 : (harmonic n : ℝ)
        = ∑ i ∈ Finset.range (n + 1),
            ((n + 1).smoothNumbers).indicator (fun k => (k : ℝ)⁻¹) i := by
      rw [← hsum_eq]; exact (Finset.sum_congr rfl hterm).symm
    rw [h1, ← hPsum]
    exact Summable.sum_le_tsum _
      (fun i _ => Set.indicator_nonneg (fun a _ => inv_nonneg.mpr (Nat.cast_nonneg a)) i) hgsum
  -- `log n ≤ P`.
  have hlogP : Real.log n ≤ P := by
    have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
    have h3 : Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) := by
      have h := log_add_one_le_harmonic n
      rw [Nat.cast_add, Nat.cast_one] at h
      exact h
    linarith [hharm]
  -- Rewrite `P` with `finv p = 1/p`.
  have hPeq : P = ∏ p ∈ (n + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [hP]; apply Finset.prod_congr rfl; intro p hp; rw [finv_apply]
  rw [← hPeq]; exact hlogP

/-- **Mertens' third theorem, upper bound (with explicit threshold).**
There is a threshold `N` such that for all `n ≥ N`,
`∏_{p ≤ n, p prime}(1 - 1/p) ≤ 1 / log n`.  We provide `N = 3`. -/
theorem prod_one_sub_inv_le :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1 - (1:ℝ)/p) ≤ 1 / Real.log n := by
  refine ⟨3, fun n hn => ?_⟩
  -- `(n+1).primesBelow = (range (n+1)).filter Nat.Prime` definitionally.
  have hset : (n + 1).primesBelow = (Finset.range (n + 1)).filter Nat.Prime := rfl
  -- Each factor `1 - 1/p > 0`.
  have hfacpos : ∀ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp : p.Prime := hp.2
    have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hinv_lt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr h1
    linarith
  -- `Q := ∏(1-1/p)`.
  set Q : ℝ := ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) with hQ
  have hQpos : (0 : ℝ) < Q := by
    rw [hQ]; exact Finset.prod_pos hfacpos
  -- `P = Q⁻¹`.
  have hPQ : ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ = Q⁻¹ := by
    rw [hQ, ← Finset.prod_inv_distrib]
  -- `log n > 0`.
  have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  -- `log n ≤ Q⁻¹`.
  have hkey : Real.log n ≤ Q⁻¹ := by
    have := log_le_prod n hn
    rw [hset, hPQ] at this
    exact this
  -- From `log n ≤ Q⁻¹`, `Q > 0`: `log n * Q ≤ 1`, hence `Q ≤ 1 / log n`.
  have hmul : Real.log n * Q ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hkey hQpos.le
    rwa [inv_mul_cancel₀ hQpos.ne'] at this
  -- Convert `1 - 1/p` cast form `1/p = p⁻¹`.
  have hgoal : Q ≤ 1 / Real.log n := by
    rw [le_div_iff₀ hlogpos, mul_comm]
    exact hmul
  -- Rewrite the goal's `1/↑p` as `(↑p)⁻¹`.
  have hcast : ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1 - (1:ℝ)/p)
      = Q := by
    rw [hQ]; apply Finset.prod_congr rfl; intro p hp; rw [one_div]
  rw [hcast]; exact hgoal

end MertensProductUpper
