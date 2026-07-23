/-
# Average order of the sum-of-divisors function σ

Let `σ(n) = ∑_{d ∣ n} d` be the sum of divisors of `n`, and
`Σ(N) = ∑_{n=1}^{N} σ(n)` its summatory function.

We prove the classical **average order** estimate
    `Σ(N) = (π²/12)·N² + O(N log N)`,
with the leading term `(π²/12)·N²` *exact* and an explicit `O(N log N)` error
(here with the explicit constant `C = 4` and threshold `N₀ = 3`):
    `|Σ(N) − (π²/12)·N²| ≤ 4·(N·log N)`  for all `N ≥ 3`.

This mirrors `DivisorSummatory.divisor_summatory_asymptotic` (same `Finset.Icc`
floor-sum engine, same explicit two-sided error formulation).  The engine here is
the **cofactor reindexing**
    `∑_{n=1}^{N} σ(n) = ∑_{e=1}^{N} ∑_{m=1}^{⌊N/e⌋} m = ∑_{e=1}^{N} ⌊N/e⌋(⌊N/e⌋+1)/2`,
obtained by writing `σ(n) = ∑_{d ∣ n} (n/d)` and counting the cofactor `e = n/d`,
plus the Basel value `∑ 1/e² = π²/6` (`hasSum_zeta_two`) with a telescoping tail
bound `∑_{e>N} 1/e² ≤ 1/N`, and the harmonic bound `H_N ≤ 1 + log N`.

mathlib has σ, the Basel sum, and the harmonic bounds, but not this asymptotic;
all lemmas below are new.
-/
import Propositio.NumberTheory.Analytic.DivisorSummatory
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open Finset
open scoped ArithmeticFunction.sigma

namespace SigmaSummatory

/-- Gauss triangular sum over `Icc 1 M`, in `ℝ`: `∑_{m=1}^{M} m = M(M+1)/2`. -/
theorem sum_Icc_one_id (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (m : ℝ) = (M : ℝ) * ((M : ℝ) + 1) / 2 := by
  induction M with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ k + 1), ih]
      push_cast
      ring

/-- The multiples of `k` in `Icc 1 N`, divided by `k`, sum to `∑_{m=1}^{⌊N/k⌋} m`.
The bijection `n ↦ n/k` (inverse `m ↦ k·m`) matches the cofactors. -/
theorem sum_filter_div_eq (N k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ (Finset.Icc 1 N).filter (k ∣ ·), n / k
      = ∑ m ∈ Finset.Icc 1 (N / k), m := by
  apply Finset.sum_bij' (i := fun n _ => n / k) (j := fun m _ => k * m)
  · -- i maps into the target
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, hdvd⟩ := hn
    refine ⟨?_, Nat.div_le_div_right h2⟩
    exact Nat.one_le_div_iff (by omega) |>.mpr (Nat.le_of_dvd (by omega) hdvd)
  · -- j maps into the source
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := hm
    refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
    · calc 1 ≤ k := hk
        _ = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * m := Nat.mul_le_mul_left k h1
    · calc k * m ≤ k * (N / k) := Nat.mul_le_mul_left k h2
        _ ≤ N := Nat.mul_div_le N k
  · -- left inverse: k * (n / k) = n
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · -- right inverse: (k * m) / k = m
    intro m _
    exact Nat.mul_div_cancel_left m (by omega)
  · -- the summands agree
    intro n _
    rfl

/-- **Cofactor reindexing of the summatory σ.**
`∑_{n=1}^{N} σ(n) = ∑_{k=1}^{N} ∑_{m=1}^{⌊N/k⌋} m`. -/
theorem sum_sigma_eq_sum_tri (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, σ 1 n
      = ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / k), m := by
  -- For each `n`, rewrite `σ(n) = ∑_{d ∣ n} (n/d)` as a filtered count over `Icc 1 N`.
  have step1 : ∀ n ∈ Finset.Icc 1 N,
      σ 1 n = ∑ k ∈ Finset.Icc 1 N, (if k ∣ n then n / k else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors n (fun d => d),
      DivisorSummatory.divisors_eq_filter_Icc hn.1 hn.2, Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [← Finset.sum_filter]
  exact sum_filter_div_eq N k hk.1

/-- **Average order of the sum-of-divisors function.**
With `Σ(N) = ∑_{n=1}^{N} σ(n)`, we have `Σ(N) = (π²/12)·N² + O(N·log N)`, here
with the explicit constant `C = 4` and threshold `N₀ = 3`:
    `|Σ(N) − (π²/12)·N²| ≤ 4·(N·log N)`  for all `N ≥ 3`. -/
theorem sigma_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ)) - Real.pi ^ 2 / 12 * (N : ℝ) ^ 2|
        ≤ C * ((N : ℝ) * Real.log N) := by
  refine ⟨4, 3, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  -- `log N ≥ 1` for `N ≥ 3` (since `N ≥ 3 > e`).
  have hexp : Real.exp 1 ≤ (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.exp_one_lt_three
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hexp
  -- Abbreviations.
  set D : ℝ := ∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ) with hDdef
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2 with hSdef
  -- The Basel function and its total.
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hfdef
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf_sum : HasSum f (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hf_summable : Summable f := hf_sum.summable
  -- D as a sum of triangular numbers.
  have hD : D = ∑ k ∈ Finset.Icc 1 N,
      ((N / k : ℕ) : ℝ) * (((N / k : ℕ) : ℝ) + 1) / 2 := by
    have h := sum_sigma_eq_sum_tri N
    have hcast : D = ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / k), (m : ℝ) := by
      rw [hDdef, ← Nat.cast_sum, h]
      push_cast
      rfl
    rw [hcast]
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_Icc_one_id]
  -- Per-term floor error bound.
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      |((N / k : ℕ) : ℝ) * (((N / k : ℕ) : ℝ) + 1) / 2
        - (N : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2)|
      ≤ 3 / 2 * (N : ℝ) * (k : ℝ)⁻¹ + 1 / 2 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk.1
    set x : ℝ := (N : ℝ) / (k : ℝ) with hxdef
    set q : ℝ := ((N / k : ℕ) : ℝ) with hqdef
    have hq0 : 0 ≤ q := by positivity
    have hqx : q ≤ x := by rw [hqdef, hxdef]; exact Nat.cast_div_le
    have hxq1 : x < q + 1 := by
      rw [hxdef, hqdef, div_lt_iff₀ hkpos]
      have hnat : N < k * (N / k + 1) := by
        have h1 : k * (N / k) + N % k = N := Nat.div_add_mod N k
        have h2 : N % k < k := Nat.mod_lt N (by omega)
        calc N = k * (N / k) + N % k := h1.symm
          _ < k * (N / k) + k := by omega
          _ = k * (N / k + 1) := by ring
      have : (N : ℝ) < (k : ℝ) * (((N / k : ℕ) : ℝ) + 1) := by
        have := (Nat.cast_lt (α := ℝ)).mpr hnat
        push_cast at this
        linarith
      linarith
    have hmain_eq : (N : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2) = x ^ 2 / 2 := by
      rw [hxdef]; field_simp
    have hxk : x = (N : ℝ) * (k : ℝ)⁻¹ := by rw [hxdef, div_eq_mul_inv]
    rw [hmain_eq]
    rw [show 3 / 2 * (N : ℝ) * (k : ℝ)⁻¹ + 1 / 2 = 3 / 2 * x + 1 / 2 by rw [hxk]; ring]
    rw [abs_le]
    constructor
    · nlinarith [hqx, hxq1, hq0, mul_nonneg hq0 (sub_nonneg.mpr hqx), sq_nonneg (x - q),
        mul_pos hkpos hkpos]
    · nlinarith [hqx, hxq1, hq0, mul_nonneg hq0 (sub_nonneg.mpr hqx), sq_nonneg (x - q)]
  -- The floor-error half: `|D − (N²/2)·S| ≤ (3/2)·N·log N + 2N`.
  have hfloor : |D - (N : ℝ) ^ 2 / 2 * S| ≤ 3 / 2 * ((N : ℝ) * Real.log N) + 2 * N := by
    have hRM : (N : ℝ) ^ 2 / 2 * S
        = ∑ k ∈ Finset.Icc 1 N, (N : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2) := by
      rw [hSdef, Finset.mul_sum]
    have hsumeq : ∑ k ∈ Finset.Icc 1 N, (3 / 2 * (N : ℝ) * (k : ℝ)⁻¹ + 1 / 2)
        = 3 / 2 * (N : ℝ) * (harmonic N : ℝ) + 1 / 2 * N := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, DivisorSummatory.sum_inv_eq_harmonic]
      rw [Finset.sum_const, Nat.card_Icc]
      push_cast
      ring
    calc |D - (N : ℝ) ^ 2 / 2 * S|
        = |∑ k ∈ Finset.Icc 1 N,
            (((N / k : ℕ) : ℝ) * (((N / k : ℕ) : ℝ) + 1) / 2
              - (N : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2))| := by
          rw [hD, hRM, ← Finset.sum_sub_distrib]
      _ ≤ ∑ k ∈ Finset.Icc 1 N,
            |((N / k : ℕ) : ℝ) * (((N / k : ℕ) : ℝ) + 1) / 2
              - (N : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N, (3 / 2 * (N : ℝ) * (k : ℝ)⁻¹ + 1 / 2) :=
            Finset.sum_le_sum hterm
      _ = 3 / 2 * (N : ℝ) * (harmonic N : ℝ) + 1 / 2 * N := hsumeq
      _ ≤ 3 / 2 * (N : ℝ) * (1 + Real.log N) + 1 / 2 * N := by
            have hH : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
            have : 3 / 2 * (N : ℝ) * (harmonic N : ℝ) ≤ 3 / 2 * (N : ℝ) * (1 + Real.log N) := by
              apply mul_le_mul_of_nonneg_left hH (by positivity)
            linarith
      _ = 3 / 2 * ((N : ℝ) * Real.log N) + 2 * N := by ring
  -- The tail half: `|(N²/2)·S − (π²/12)·N²| ≤ N/2`.
  -- Telescoping tail bound: `∑_{i} 1/(i+N+1)² ≤ 1/N`.
  have htail_le : ∑' i, f (i + (N + 1)) ≤ 1 / (N : ℝ) := by
    apply Real.tsum_le_of_sum_range_le (fun i => hf_nonneg _)
    intro n
    set g : ℕ → ℝ := fun j => 1 / ((j : ℝ) + N) with hgdef
    have hgsub : ∑ i ∈ Finset.range n, (g i - g (i + 1)) = g 0 - g n :=
      Finset.sum_range_sub' g n
    have hle : ∑ i ∈ Finset.range n, f (i + (N + 1))
        ≤ ∑ i ∈ Finset.range n, (g i - g (i + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have ha : (0 : ℝ) < (i : ℝ) + N := by positivity
      have hfval : f (i + (N + 1)) = 1 / ((i : ℝ) + N + 1) ^ 2 := by
        rw [hfdef]; push_cast; ring_nf
      have hgval : g i - g (i + 1) = 1 / (((i : ℝ) + N) * ((i : ℝ) + N + 1)) := by
        rw [hgdef]; push_cast; field_simp; ring
      rw [hfval, hgval]
      apply one_div_le_one_div_of_le (mul_pos ha (by linarith))
      nlinarith [ha]
    have hgn : 0 ≤ g n := by rw [hgdef]; positivity
    have hg0 : g 0 = 1 / (N : ℝ) := by rw [hgdef]; push_cast; ring
    calc ∑ i ∈ Finset.range n, f (i + (N + 1))
        ≤ ∑ i ∈ Finset.range n, (g i - g (i + 1)) := hle
      _ = g 0 - g n := hgsub
      _ ≤ g 0 := by linarith
      _ = 1 / (N : ℝ) := hg0
  -- Connect the tail tsum to `π²/6 − S`.
  have hsplit : (∑ i ∈ Finset.range (N + 1), f i) + ∑' i, f (i + (N + 1))
      = Real.pi ^ 2 / 6 := by
    rw [hf_summable.sum_add_tsum_nat_add (N + 1), hf_sum.tsum_eq]
  have hPS : ∑ i ∈ Finset.range (N + 1), f i = S := by
    rw [hSdef]
    have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp)]
    rw [hfdef]
    simp
  have htail_eq : Real.pi ^ 2 / 6 - S = ∑' i, f (i + (N + 1)) := by
    rw [← hPS]; linarith [hsplit]
  have htail_nonneg : 0 ≤ ∑' i, f (i + (N + 1)) :=
    tsum_nonneg (fun i => hf_nonneg _)
  have hC : |(N : ℝ) ^ 2 / 2 * S - Real.pi ^ 2 / 12 * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 := by
    have key : (N : ℝ) ^ 2 / 2 * S - Real.pi ^ 2 / 12 * (N : ℝ) ^ 2
        = -((N : ℝ) ^ 2 / 2 * (Real.pi ^ 2 / 6 - S)) := by ring
    have hpos : 0 ≤ (N : ℝ) ^ 2 / 2 * (Real.pi ^ 2 / 6 - S) := by
      apply mul_nonneg (by positivity)
      rw [htail_eq]; exact htail_nonneg
    have hbound : (N : ℝ) ^ 2 / 2 * (Real.pi ^ 2 / 6 - S) ≤ (N : ℝ) / 2 := by
      rw [htail_eq]
      calc (N : ℝ) ^ 2 / 2 * (∑' i, f (i + (N + 1)))
          ≤ (N : ℝ) ^ 2 / 2 * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left htail_le (by positivity)
        _ = (N : ℝ) / 2 := by field_simp
    rw [key, abs_neg, abs_of_nonneg hpos]
    exact hbound
  -- `N ≤ N·log N` since `log N ≥ 1`, so the `O(N)` terms fold into `O(N log N)`.
  have hNlogN : (N : ℝ) ≤ (N : ℝ) * Real.log N := by nlinarith [hNpos, hlog1]
  calc |D - Real.pi ^ 2 / 12 * (N : ℝ) ^ 2|
      ≤ |D - (N : ℝ) ^ 2 / 2 * S| + |(N : ℝ) ^ 2 / 2 * S - Real.pi ^ 2 / 12 * (N : ℝ) ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ (3 / 2 * ((N : ℝ) * Real.log N) + 2 * N) + (N : ℝ) / 2 := by
        linarith [hfloor, hC]
    _ ≤ 4 * ((N : ℝ) * Real.log N) := by nlinarith [hNlogN, hNpos]

end SigmaSummatory
