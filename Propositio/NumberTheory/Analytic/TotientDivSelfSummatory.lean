/-
# Average order of `φ(n)/n`: `∑_{n≤N} φ(n)/n = (6/π²)·N + O(log N)`

Let `φ(n)` be Euler's totient.  We prove the classical **average order** estimate
    `∑_{n=1}^{N} φ(n)/n = (6/π²)·N + O(log N)`,
with the leading term `(6/π²)·N` *exact* and an explicit `O(log N)` error (here with the
explicit constant `C = 3` and threshold `N₀ = 3`):
    `|∑_{n=1}^{N} φ(n)/n − (6/π²)·N| ≤ 3·log N`  for all `N ≥ 3`.

This is the `φ(n)/n` companion to `TotientSummatory.totient_summatory_asymptotic`
(`∑ φ(n) = (3/π²)N² + O(N log N)`), but *simpler*: dividing the Möbius-inversion identity
`φ(n) = ∑_{d ∣ n} μ(d)·(n/d)` by `n` collapses the cofactor `n/d` and gives
    `φ(n)/n = ∑_{d ∣ n} μ(d)/d`.
The cofactor reindexing (counting multiples, `MobiusPartialSum`-style) then yields
    `∑_{n=1}^{N} φ(n)/n = ∑_{d=1}^{N} (μ(d)/d)·⌊N/d⌋`,
a *floor* sum rather than a triangular one.  Writing `⌊N/d⌋ = N/d − {N/d}`:
* the main term is `N·∑_{d≤N} μ(d)/d² = (6/π²)·N + O(1)`, from the Möbius/zeta keystone
  `∑' μ(d)/d² = 6/π²` (`MobiusZetaTwo.tsum_moebius_div_sq`) with the telescoping tail bound
  `∑_{d>N} 1/d² ≤ 1/N` and `|μ| ≤ 1`;
* the error `∑_{d≤N} (μ(d)/d){N/d}` is bounded in absolute value by `∑_{d≤N} 1/d = H_N ≤ 1 + log N`
  (harmonic, `DivisorSummatory.sum_inv_eq_harmonic` / `harmonic_le_one_add_log`).

mathlib has `φ`, the Möbius inversion machinery, and the Basel/Möbius–zeta values, but not this
asymptotic; the lemmas below are new.
-/
import Propositio.NumberTheory.Analytic.TotientSummatory
import Propositio.NumberTheory.Analytic.MobiusZetaTwo
import Propositio.NumberTheory.Analytic.MobiusPartialSum
import Propositio.NumberTheory.Analytic.DivisorSummatory
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

open Finset

namespace TotientDivSelfSummatory

set_option maxHeartbeats 1000000 in
/-- **Cofactor reindexing for `φ(n)/n`.**
`∑_{n=1}^{N} φ(n)/n = ∑_{d=1}^{N} (μ(d)/d)·⌊N/d⌋`.  The per-`n` identity is
`φ(n)/n = ∑_{d ∣ n} μ(d)/d` (Möbius inversion divided by `n`), and swapping the order turns the
divisor sum into a count of multiples `#{n ≤ N : d ∣ n} = ⌊N/d⌋`. -/
theorem sum_totient_div_self_eq_sum_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) / (n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * ((N / d : ℕ) : ℝ) := by
  -- Per-`n`: `φ(n)/n = ∑_{d ∈ Icc 1 N} [d ∣ n]·(μ(d)/d)`.
  have step1 : ∀ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) / (n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : 0 < n := by omega
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [TotientSummatory.totient_eq_sum_div n hnpos, Finset.sum_div,
      DivisorSummatory.divisors_eq_filter_Icc hn.1 hn.2, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    by_cases h : d ∣ n
    · rw [if_pos h, if_pos h, Nat.cast_div h hd0]
      field_simp
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  -- The count of multiples of `d` in `Icc 1 N` is `⌊N/d⌋`.
  have hcount : ((Finset.Icc 1 N).filter (d ∣ ·)).card = N / d := by
    have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  rw [← Finset.sum_filter, Finset.sum_const, hcount, nsmul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- **Average order of `φ(n)/n`.**
With `T(N) = ∑_{n=1}^{N} φ(n)/n`, we have `T(N) = (6/π²)·N + O(log N)`, here with the
explicit constant `C = 3` and threshold `N₀ = 3`:
    `|T(N) − (6/π²)·N| ≤ 3·log N`  for all `N ≥ 3`. -/
theorem totient_div_self_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) / (n : ℝ)) - 6 / Real.pi ^ 2 * (N : ℝ)|
        ≤ C * Real.log N := by
  refine ⟨3, 3, ?_⟩
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
  set D : ℝ := ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) / (n : ℝ) with hDdef
  set am : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 with hamdef
  set bsl : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hbsldef
  set S : ℝ := ∑ d ∈ Finset.Icc 1 N, am d with hSdef
  set E : ℝ := ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))
    with hEdef
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
  -- The reindexed floor sum.
  have hReidx : D = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * ((N / d : ℕ) : ℝ) := by
    rw [hDdef]; exact sum_totient_div_self_eq_sum_floor N
  -- `N·S = ∑ (μ(d)/d)·(N/d)` (real division).
  have hNS : (N : ℝ) * S
      = ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * ((N : ℝ) / (d : ℝ)) := by
    rw [hSdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hamdef]
    ring
  -- Split `⌊N/d⌋ = N/d − {N/d}`: `D = N·S − E`.
  have hDE : (N : ℝ) * S - E = D := by
    rw [hNS, hEdef, hReidx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  -- Per-term error bound: `|(μ(d)/d)·{N/d}| ≤ 1/d`.
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
          * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))| ≤ (d : ℝ)⁻¹ := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hfrac_nonneg : 0 ≤ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := d); linarith
    have hfrac_le : (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) ≤ 1 := by
      have hdm : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast Nat.div_add_mod N d
      have hmod : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt N (by omega)
      have hle : (N : ℝ) / (d : ℝ) ≤ ((N / d : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ hdpos]; nlinarith [hdm, hmod]
      linarith
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_mul, abs_div, abs_of_pos hdpos, abs_of_nonneg hfrac_nonneg,
      div_mul_eq_mul_div, inv_eq_one_div]
    gcongr
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ) hfrac_nonneg, hfrac_le]
  -- `|E| ≤ ∑ 1/d = H_N ≤ 1 + log N`.
  have hEbound : |E| ≤ (harmonic N : ℝ) := by
    rw [hEdef]
    calc |∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = (harmonic N : ℝ) := DivisorSummatory.sum_inv_eq_harmonic N
  have hEub : |E| ≤ 1 + Real.log N := le_trans hEbound (harmonic_le_one_add_log N)
  -- The main-term bound: `|N·S − (6/π²)·N| ≤ 1`.
  have hmain : |(N : ℝ) * S - 6 / Real.pi ^ 2 * (N : ℝ)| ≤ 1 := by
    have key : (N : ℝ) * S - 6 / Real.pi ^ 2 * (N : ℝ) = (N : ℝ) * (S - 6 / Real.pi ^ 2) := by
      ring
    rw [key, abs_mul, abs_of_nonneg (le_of_lt hNpos)]
    calc (N : ℝ) * |S - 6 / Real.pi ^ 2|
        = (N : ℝ) * |6 / Real.pi ^ 2 - S| := by rw [abs_sub_comm]
      _ ≤ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left htail_abs (le_of_lt hNpos)
      _ = 1 := by field_simp
  -- Assemble.
  have hrw : D - 6 / Real.pi ^ 2 * (N : ℝ)
      = ((N : ℝ) * S - 6 / Real.pi ^ 2 * (N : ℝ)) - E := by
    rw [← hDE]; ring
  calc |D - 6 / Real.pi ^ 2 * (N : ℝ)|
      = |((N : ℝ) * S - 6 / Real.pi ^ 2 * (N : ℝ)) - E| := by rw [hrw]
    _ ≤ |(N : ℝ) * S - 6 / Real.pi ^ 2 * (N : ℝ)| + |E| := by
        have := abs_add_le ((N : ℝ) * S - 6 / Real.pi ^ 2 * (N : ℝ)) (-E)
        simpa [sub_eq_add_neg, abs_neg] using this
    _ ≤ 1 + (1 + Real.log N) := add_le_add hmain hEub
    _ ≤ 3 * Real.log N := by nlinarith [hlog1]

end TotientDivSelfSummatory
