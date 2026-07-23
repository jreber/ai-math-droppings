/-
# Average order of Euler's totient `φ`

Let `φ(n)` be Euler's totient and `Φ(N) = ∑_{n=1}^{N} φ(n)` its summatory function.

We prove the classical **average order** estimate
    `Φ(N) = (3/π²)·N² + O(N log N)`,
with the leading term `(3/π²)·N²` *exact* and an explicit `O(N log N)` error
(here with the explicit constant `C = 4` and threshold `N₀ = 3`):
    `|Φ(N) − (3/π²)·N²| ≤ 4·(N·log N)`  for all `N ≥ 3`.

This mirrors `SigmaSummatory.sigma_summatory_asymptotic` / `DivisorSummatory.divisor_summatory_asymptotic`
(same `Finset.Icc` floor-sum / cofactor-reindex engine, same explicit two-sided error formulation),
the new ingredient being the **Möbius-inversion identity** `φ = μ ∗ id`, i.e.
    `φ(n) = ∑_{d ∣ n} μ(d)·(n/d)`,
obtained from `∑_{d ∣ n} φ(d) = n` (`Nat.sum_totient`) via mathlib's
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`.  The cofactor reindexing
    `∑_{n=1}^{N} φ(n) = ∑_{d=1}^{N} μ(d) · ∑_{m=1}^{⌊N/d⌋} m
                     = ∑_{d=1}^{N} μ(d) · ⌊N/d⌋(⌊N/d⌋+1)/2`
is exactly the `SigmaSummatory` triangular engine, weighted by `μ(d)` outside.  The main term
comes from the Möbius/zeta keystone `∑' μ(d)/d² = 6/π²` (`MobiusZetaTwo.tsum_moebius_div_sq`),
with the partial-sum error controlled by the telescoping tail bound `∑_{d>N} 1/d² ≤ 1/N` and
`|μ| ≤ 1`.

mathlib has `φ`, the Möbius inversion machinery, and the Basel/Möbius–zeta values, but not this
asymptotic; all lemmas below are new.
-/
import Propositio.NumberTheory.Analytic.SigmaSummatory
import Propositio.NumberTheory.Analytic.MobiusZetaTwo
import Propositio.NumberTheory.Analytic.MobiusPartialSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

open Finset

namespace TotientSummatory

/-- **Möbius inversion for the totient.**  For `n > 0`,
`φ(n) = ∑_{d ∣ n} μ(d)·(n/d)` (the identity `φ = μ ∗ id`), proved over `ℝ`. -/
theorem totient_eq_sum_div (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
  -- `∑_{d ∣ m} φ(d) = m` over `ℝ`, the hypothesis of Möbius inversion.
  have hhyp : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, (Nat.totient i : ℝ) = (m : ℝ) := by
    intro m _
    have h : (∑ i ∈ m.divisors, Nat.totient i : ℕ) = m := Nat.sum_totient m
    calc ∑ i ∈ m.divisors, (Nat.totient i : ℝ)
        = ((∑ i ∈ m.divisors, Nat.totient i : ℕ) : ℝ) := by push_cast; rfl
      _ = (m : ℝ) := by rw [h]
  -- Möbius inversion: `∑_{(d,e): de=n} μ(d)·e = φ(n)`.
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℝ) (f := fun k => (Nat.totient k : ℝ)) (g := fun k => (k : ℝ))).mp hhyp n hn
  rw [← hinv]
  exact (Nat.sum_divisorsAntidiagonal
    (fun d e => (ArithmeticFunction.moebius d : ℝ) * (e : ℝ)))

set_option maxHeartbeats 1000000 in
/-- **Cofactor reindexing of the summatory totient.**
`∑_{n=1}^{N} φ(n) = ∑_{d=1}^{N} μ(d) · ∑_{m=1}^{⌊N/d⌋} m`. -/
theorem sum_totient_eq_sum_tri (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)
          * ∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) := by
  -- Per-`n`, rewrite `φ(n) = ∑_{d ∣ n} μ(d)(n/d)` as a filtered count over `Icc 1 N`.
  have step1 : ∀ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [totient_eq_sum_div n (by omega),
      DivisorSummatory.divisors_eq_filter_Icc hn.1 hn.2, Finset.sum_filter]
  -- Unweighted cofactor identity (the `SigmaSummatory` ℕ-engine, cast to `ℝ`).
  have hinner : ∀ d : ℕ, 1 ≤ d →
      ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then ((n / d : ℕ) : ℝ) else 0)
        = ∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) := by
    intro d hd
    rw [← Finset.sum_filter, ← Nat.cast_sum,
      SigmaSummatory.sum_filter_div_eq N d hd, Nat.cast_sum]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  rw [← hinner d hd.1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_ite, mul_zero]

set_option maxHeartbeats 1000000 in
/-- **Average order of Euler's totient.**
With `Φ(N) = ∑_{n=1}^{N} φ(n)`, we have `Φ(N) = (3/π²)·N² + O(N·log N)`, here with the
explicit constant `C = 4` and threshold `N₀ = 3`:
    `|Φ(N) − (3/π²)·N²| ≤ 4·(N·log N)`  for all `N ≥ 3`. -/
theorem totient_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2|
        ≤ C * ((N : ℝ) * Real.log N) := by
  refine ⟨4, 3, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- `log N ≥ 1` for `N ≥ 3` (since `N ≥ 3 > e`).
  have hexp : Real.exp 1 ≤ (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.exp_one_lt_three
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hexp
  -- Abbreviations.
  set D : ℝ := ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) with hDdef
  set am : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 with hamdef
  set bsl : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hbsldef
  set S : ℝ := ∑ d ∈ Finset.Icc 1 N, am d with hSdef
  -- The Basel function and its total.
  have hbsl_sum : HasSum bsl (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hbsl_summable : Summable bsl := hbsl_sum.summable
  have hbsl_nonneg : ∀ n, 0 ≤ bsl n := fun n => by positivity
  -- `|μ(n)/n²| ≤ 1/n²`.
  have hle_norm : ∀ n, |am n| ≤ bsl n := by
    intro n
    simp only [hamdef, hbsldef]
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    gcongr
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  -- Summability of the Möbius series and its absolute value.
  have ham_norm_summable : Summable (fun n => |am n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle_norm hbsl_summable
  have ham_summable : Summable am := summable_abs_iff.mp ham_norm_summable
  -- The keystone value `∑' μ(n)/n² = 6/π²`.
  have ham_tsum : ∑' n, am n = 6 / Real.pi ^ 2 := by
    simp only [hamdef]; exact MobiusZetaTwo.tsum_moebius_div_sq
  -- `D` as a sum of `μ`-weighted triangular numbers.
  have hD : D = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)
        * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
    rw [hDdef, sum_totient_eq_sum_tri N]
    apply Finset.sum_congr rfl
    intro d _
    rw [SigmaSummatory.sum_Icc_one_id]
  -- Per-term floor error bound (`|μ| ≤ 1` × the `SigmaSummatory` triangular bound).
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      |(ArithmeticFunction.moebius d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
        - (ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2))|
      ≤ 3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hsig : |((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2
        - (N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2)|
        ≤ 3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2 := by
      set x : ℝ := (N : ℝ) / (d : ℝ) with hxdef
      set q : ℝ := ((N / d : ℕ) : ℝ) with hqdef
      have hq0 : 0 ≤ q := by positivity
      have hqx : q ≤ x := by rw [hqdef, hxdef]; exact Nat.cast_div_le
      have hxq1 : x < q + 1 := by
        rw [hxdef, hqdef, div_lt_iff₀ hdpos]
        have hnat : N < d * (N / d + 1) := by
          have h1 : d * (N / d) + N % d = N := Nat.div_add_mod N d
          have h2 : N % d < d := Nat.mod_lt N (by omega)
          calc N = d * (N / d) + N % d := h1.symm
            _ < d * (N / d) + d := by omega
            _ = d * (N / d + 1) := by ring
        have : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
          have := (Nat.cast_lt (α := ℝ)).mpr hnat
          push_cast at this
          linarith
        linarith
      have hmain_eq : (N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2) = x ^ 2 / 2 := by
        rw [hxdef]; field_simp
      have hxk : x = (N : ℝ) * (d : ℝ)⁻¹ := by rw [hxdef, div_eq_mul_inv]
      rw [hmain_eq]
      rw [show 3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2 = 3 / 2 * x + 1 / 2 by rw [hxk]; ring]
      rw [abs_le]
      constructor
      · nlinarith [hqx, hxq1, hq0, mul_nonneg hq0 (sub_nonneg.mpr hqx), sq_nonneg (x - q),
          mul_pos hdpos hdpos]
      · nlinarith [hqx, hxq1, hq0, mul_nonneg hq0 (sub_nonneg.mpr hqx), sq_nonneg (x - q)]
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc |(ArithmeticFunction.moebius d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
          - (ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2))|
        = |(ArithmeticFunction.moebius d : ℝ)|
            * |((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2
                - (N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2)| := by
          rw [← mul_sub, abs_mul]
      _ ≤ 1 * (3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2) :=
          mul_le_mul hμ hsig (abs_nonneg _) (by norm_num)
      _ = 3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2 := by ring
  -- The floor-error half: `|D − (N²/2)·S| ≤ (3/2)·N·log N + 2N`.
  have hfloor : |D - (N : ℝ) ^ 2 / 2 * S| ≤ 3 / 2 * ((N : ℝ) * Real.log N) + 2 * N := by
    have hRM : (N : ℝ) ^ 2 / 2 * S
        = ∑ d ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2)) := by
      rw [hSdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hamdef]
      ring
    have hsumeq : ∑ d ∈ Finset.Icc 1 N, (3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2)
        = 3 / 2 * (N : ℝ) * (harmonic N : ℝ) + 1 / 2 * N := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, DivisorSummatory.sum_inv_eq_harmonic]
      rw [Finset.sum_const, Nat.card_Icc]
      push_cast
      ring
    calc |D - (N : ℝ) ^ 2 / 2 * S|
        = |∑ d ∈ Finset.Icc 1 N,
            ((ArithmeticFunction.moebius d : ℝ)
                * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
              - (ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2)))| := by
          rw [hD, hRM, ← Finset.sum_sub_distrib]
      _ ≤ ∑ d ∈ Finset.Icc 1 N,
            |(ArithmeticFunction.moebius d : ℝ)
                * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
              - (ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (3 / 2 * (N : ℝ) * (d : ℝ)⁻¹ + 1 / 2) :=
            Finset.sum_le_sum hterm
      _ = 3 / 2 * (N : ℝ) * (harmonic N : ℝ) + 1 / 2 * N := hsumeq
      _ ≤ 3 / 2 * (N : ℝ) * (1 + Real.log N) + 1 / 2 * N := by
            have hH : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
            have : 3 / 2 * (N : ℝ) * (harmonic N : ℝ) ≤ 3 / 2 * (N : ℝ) * (1 + Real.log N) := by
              apply mul_le_mul_of_nonneg_left hH (by positivity)
            linarith
      _ = 3 / 2 * ((N : ℝ) * Real.log N) + 2 * N := by ring
  -- Telescoping tail bound `∑_{i} 1/(i+N+1)² ≤ 1/N` (reused from the Basel engine).
  have htail_le : ∑' i, bsl (i + (N + 1)) ≤ 1 / (N : ℝ) := by
    apply Real.tsum_le_of_sum_range_le (fun i => hbsl_nonneg _)
    intro n
    set g : ℕ → ℝ := fun j => 1 / ((j : ℝ) + N) with hgdef
    have hgsub : ∑ i ∈ Finset.range n, (g i - g (i + 1)) = g 0 - g n :=
      Finset.sum_range_sub' g n
    have hle : ∑ i ∈ Finset.range n, bsl (i + (N + 1))
        ≤ ∑ i ∈ Finset.range n, (g i - g (i + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have ha : (0 : ℝ) < (i : ℝ) + N := by positivity
      have hfval : bsl (i + (N + 1)) = 1 / ((i : ℝ) + N + 1) ^ 2 := by
        rw [hbsldef]; push_cast; ring_nf
      have hgval : g i - g (i + 1) = 1 / (((i : ℝ) + N) * ((i : ℝ) + N + 1)) := by
        rw [hgdef]; push_cast; field_simp; ring
      rw [hfval, hgval]
      apply one_div_le_one_div_of_le (mul_pos ha (by linarith))
      nlinarith [ha]
    have hgn : 0 ≤ g n := by rw [hgdef]; positivity
    have hg0 : g 0 = 1 / (N : ℝ) := by rw [hgdef]; push_cast; ring
    calc ∑ i ∈ Finset.range n, bsl (i + (N + 1))
        ≤ ∑ i ∈ Finset.range n, (g i - g (i + 1)) := hle
      _ = g 0 - g n := hgsub
      _ ≤ g 0 := by linarith
      _ = 1 / (N : ℝ) := hg0
  -- `∑_{i∈range (N+1)} am i = S` (the `i = 0` term vanishes).
  have ham0 : am 0 = 0 := by simp [hamdef]
  have hPS : ∑ i ∈ Finset.range (N + 1), am i = S := by
    have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp), ham0, zero_add, hSdef]
  -- Connect the Möbius tail to `6/π² − S`.
  have hsplit : (∑ i ∈ Finset.range (N + 1), am i) + ∑' i, am (i + (N + 1)) = 6 / Real.pi ^ 2 := by
    rw [ham_summable.sum_add_tsum_nat_add (N + 1)]; exact ham_tsum
  have htail_eq : 6 / Real.pi ^ 2 - S = ∑' i, am (i + (N + 1)) := by linarith [hsplit, hPS]
  -- `|6/π² − S| ≤ 1/N` via `|tail| ≤ ∑ |am| ≤ ∑ 1/n² ≤ 1/N`.
  have ham_norm' : Summable (fun n => ‖am n‖) := by
    simpa [Real.norm_eq_abs] using ham_norm_summable
  have hshift_norm : Summable (fun i => ‖am (i + (N + 1))‖) :=
    (summable_nat_add_iff (N + 1)).2 ham_norm'
  have hshift_bsl : Summable (fun i => bsl (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 hbsl_summable
  have htail_abs : |6 / Real.pi ^ 2 - S| ≤ 1 / (N : ℝ) := by
    rw [htail_eq]
    have h1 : |∑' i, am (i + (N + 1))| ≤ ∑' i, ‖am (i + (N + 1))‖ := by
      rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hshift_norm
    have hle : ∀ i, ‖am (i + (N + 1))‖ ≤ bsl (i + (N + 1)) := by
      intro i; rw [Real.norm_eq_abs]; exact hle_norm _
    have h2 : ∑' i, ‖am (i + (N + 1))‖ ≤ ∑' i, bsl (i + (N + 1)) :=
      hshift_norm.tsum_le_tsum hle hshift_bsl
    calc |∑' i, am (i + (N + 1))|
        ≤ ∑' i, ‖am (i + (N + 1))‖ := h1
      _ ≤ ∑' i, bsl (i + (N + 1)) := h2
      _ ≤ 1 / (N : ℝ) := htail_le
  -- The tail half: `|(N²/2)·S − (3/π²)·N²| ≤ N/2`.
  have hC : |(N : ℝ) ^ 2 / 2 * S - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 := by
    have key : (N : ℝ) ^ 2 / 2 * S - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2
        = (N : ℝ) ^ 2 / 2 * (S - 6 / Real.pi ^ 2) := by ring
    rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2)]
    calc (N : ℝ) ^ 2 / 2 * |S - 6 / Real.pi ^ 2|
        = (N : ℝ) ^ 2 / 2 * |6 / Real.pi ^ 2 - S| := by rw [abs_sub_comm]
      _ ≤ (N : ℝ) ^ 2 / 2 * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left htail_abs (by positivity)
      _ = (N : ℝ) / 2 := by field_simp
  -- `N ≤ N·log N` since `log N ≥ 1`, so the `O(N)` terms fold into `O(N log N)`.
  have hNlogN : (N : ℝ) ≤ (N : ℝ) * Real.log N := by nlinarith [hNpos, hlog1]
  calc |D - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2|
      ≤ |D - (N : ℝ) ^ 2 / 2 * S| + |(N : ℝ) ^ 2 / 2 * S - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ (3 / 2 * ((N : ℝ) * Real.log N) + 2 * N) + (N : ℝ) / 2 := by
        linarith [hfloor, hC]
    _ ≤ 4 * ((N : ℝ) * Real.log N) := by nlinarith [hNlogN, hNpos]

end TotientSummatory
