import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Mertens' second theorem (lower bound): `Σ_{p ≤ n} 1/p ≥ log log n − O(1)`

Mathlib proves that `Σ 1/p` over the primes *diverges*
(`not_summable_one_div_on_primes`), but does not give the explicit `log log n` growth
rate.  This file fills that gap with the classical Euler-product argument, obtaining the
lower half of Mertens' second theorem with explicit constants `c = 1`, `C = 1`:

`Σ_{p ≤ n, p prime} 1/p ≥ log (log n) − 1`  for all `n ≥ 3`.

## Proof outline

1. **Euler product over smooth numbers.**  Using mathlib's
   `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric` with the
   completely multiplicative `f(k) = 1/k` (which only requires `‖f p‖ < 1`, *not* global
   summability — crucial, as `Σ 1/k` diverges), we get
   `∏_{p < n+1} (1 - 1/p)⁻¹ = Σ'_{m ∈ (n+1)-smooth} 1/m`.
2. **Harmonic lower bound.**  Every `1 ≤ m ≤ n` is `(n+1)`-smooth, so the smooth-number sum
   dominates `Σ_{k=1}^{n} 1/k = harmonic n ≥ log (n+1) ≥ log n`
   (`log_add_one_le_harmonic`).  Hence `P := ∏_{p ≤ n}(1-1/p)⁻¹ ≥ log n`.
3. **Take logs.**  `log log n ≤ log P = Σ_{p ≤ n} -log(1 - 1/p)`.
4. **Pointwise upper bound.**  `-log(1 - 1/p) ≤ 1/(p-1)` (from `log y ≤ y - 1`).
5. **Telescope the correction.**  `Σ_{p ≤ n} (1/(p-1) - 1/p) ≤ Σ_{k=2}^{n}(1/(k-1)-1/k) ≤ 1`.
   Combining, `log log n ≤ Σ_{p ≤ n} 1/p + 1`.
-/

open Real Finset

namespace MertensReciprocalLower

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

/-- Pointwise upper bound `-log(1 - 1/p) ≤ 1/(p-1)`. -/
lemma neg_log_one_sub_inv_le {p : ℕ} (hp : p.Prime) :
    -Real.log (1 - (p : ℝ)⁻¹) ≤ ((p : ℝ) - 1)⁻¹ := by
  have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hinv_lt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr h1
  have hsub : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
  have hy : (0 : ℝ) < (1 - (p : ℝ)⁻¹)⁻¹ := inv_pos.mpr hsub
  have hle := Real.log_le_sub_one_of_pos hy
  rw [Real.log_inv] at hle
  have hp0 : (p : ℝ) ≠ 0 := hpos.ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1.ne'
  have heq : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = ((p : ℝ) - 1)⁻¹ := by
    field_simp
    ring
  linarith [hle, heq.le, heq.ge]

/-- Telescoping identity: `Σ_{k=2}^{m+1} (1/(k-1) - 1/k) = 1 - 1/(m+1)`. -/
lemma corr_sum_eq (m : ℕ) :
    ∑ k ∈ Finset.Icc 2 (m + 1), (((k : ℝ) - 1)⁻¹ - (k : ℝ)⁻¹) = 1 - ((m : ℝ) + 1)⁻¹ := by
  induction m with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) from by decide, Finset.sum_empty]
    norm_num
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ j + 1 + 1), ih]
    push_cast
    rw [show (j : ℝ) + 1 + 1 - 1 = (j : ℝ) + 1 from by ring]
    ring

/-- Correction sum is bounded by `1`. -/
lemma corr_sum_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 n, (((k : ℝ) - 1)⁻¹ - (k : ℝ)⁻¹) ≤ 1 := by
  rcases n with _ | m
  · rw [show Finset.Icc 2 0 = (∅ : Finset ℕ) from by decide, Finset.sum_empty]; norm_num
  · rw [corr_sum_eq m]
    have : (0 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ := by positivity
    linarith

/-- **Mertens' second theorem, lower bound (with explicit constant)**:
`Σ_{p ≤ n} 1/p ≥ log(log n) − 1` for `n ≥ 3`. -/
theorem key (n : ℕ) (hn : 3 ≤ n) :
    Real.log (Real.log n) - 1 ≤ ∑ p ∈ (n + 1).primesBelow, ((p : ℝ))⁻¹ := by
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
  -- `log log n ≤ log P`.
  have hloglog : Real.log (Real.log n) ≤ Real.log P :=
    Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < n))) hlogP
  -- `log P = Σ_{p ≤ n} -log(1 - 1/p)`.
  have hPpos : ∀ p ∈ (n + 1).primesBelow, (1 - finv p)⁻¹ ≠ 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hinv_lt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr h1
    rw [finv_apply]
    have hposs : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
    exact inv_ne_zero hposs.ne'
  have hlogprod : Real.log P = ∑ p ∈ (n + 1).primesBelow, -Real.log (1 - (p : ℝ)⁻¹) := by
    rw [hP, Real.log_prod hPpos]
    apply Finset.sum_congr rfl
    intro p hp
    rw [finv_apply, Real.log_inv]
  -- Sum the pointwise bound.
  have hpw : ∑ p ∈ (n + 1).primesBelow, -Real.log (1 - (p : ℝ)⁻¹)
      ≤ ∑ p ∈ (n + 1).primesBelow, ((p : ℝ) - 1)⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    exact neg_log_one_sub_inv_le (Nat.prime_of_mem_primesBelow hp)
  -- Split `1/(p-1) = 1/p + (1/(p-1) - 1/p)`.
  have hsplit : ∑ p ∈ (n + 1).primesBelow, ((p : ℝ) - 1)⁻¹
      = (∑ p ∈ (n + 1).primesBelow, (p : ℝ)⁻¹)
        + ∑ p ∈ (n + 1).primesBelow, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp; ring
  -- Correction sum `≤ 1`.
  have hcorr : ∑ p ∈ (n + 1).primesBelow, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) ≤ 1 := by
    apply le_trans _ (corr_sum_le n)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpp := Nat.prime_of_mem_primesBelow hp
      have hlt := Nat.lt_of_mem_primesBelow hp
      rw [Finset.mem_Icc]
      exact ⟨hpp.two_le, by omega⟩
    · intro k hk _
      rw [Finset.mem_Icc] at hk
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      have hle : (k : ℝ) - 1 ≤ (k : ℝ) := by linarith
      have hcomp : ((k : ℝ))⁻¹ ≤ ((k : ℝ) - 1)⁻¹ := inv_anti₀ hkm1 hle
      linarith
  -- Combine.
  have hchain : Real.log (Real.log n)
      ≤ (∑ p ∈ (n + 1).primesBelow, (p : ℝ)⁻¹) + 1 := by
    calc Real.log (Real.log n)
        ≤ Real.log P := hloglog
      _ = ∑ p ∈ (n + 1).primesBelow, -Real.log (1 - (p : ℝ)⁻¹) := hlogprod
      _ ≤ ∑ p ∈ (n + 1).primesBelow, ((p : ℝ) - 1)⁻¹ := hpw
      _ = (∑ p ∈ (n + 1).primesBelow, (p : ℝ)⁻¹)
            + ∑ p ∈ (n + 1).primesBelow, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := hsplit
      _ ≤ (∑ p ∈ (n + 1).primesBelow, (p : ℝ)⁻¹) + 1 := by linarith [hcorr]
  linarith [hchain]

/-- **Mertens' second theorem (lower bound).**  There are constants `c > 0`, `C` and a
threshold `N` such that for all `n ≥ N`,
`c · log(log n) − C ≤ Σ_{p ≤ n, p prime} 1/p`.  We provide `c = 1`, `C = 1`, `N = 3`. -/
theorem sum_reciprocal_primes_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * Real.log (Real.log n) - C
        ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p := by
  refine ⟨1, one_pos, 1, 3, fun n hn => ?_⟩
  rw [one_mul]
  have hk := key n hn
  have hset : (n + 1).primesBelow = (Finset.range (n + 1)).filter Nat.Prime := rfl
  rw [hset] at hk
  have heq : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p
      = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp; rw [one_div]
  rw [heq]
  exact hk

end MertensReciprocalLower
