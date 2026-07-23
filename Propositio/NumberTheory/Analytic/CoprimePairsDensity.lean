/-
# Probability that two integers are coprime is `6/π²`

The classical density result, a genuine mathlib gap.  With
`P(N) = #{(a,b) ∈ [1,N]² : gcd(a,b) = 1}` we prove
    `P(N) = (6/π²)·N² + O(N log N)`,
with the **leading constant `6/π²` exact** and an explicit `O(N log N)` error
(constant `C = 6`, threshold `N₀ = 3`):
    `|P(N) − (6/π²)·N²| ≤ 6·N·log N`  for all `N ≥ 3`.

The argument is the standard Möbius sieve / hyperbola split:

* **Indicator identity** (`moebius_coprime_eq_sum`).  For `1 ≤ a,b ≤ N`,
    `∑_{e ≤ N} [e ∣ a ∧ e ∣ b]·μ(e) = [gcd(a,b) = 1]`,
  because the divisors `e ≤ N` of `a` and `b` are exactly the divisors of `gcd(a,b)`
  (which is `≤ a ≤ N`), and `∑_{e ∣ g} μ(e) = [g = 1]` via the Möbius convolution
  `μ ∗ ζ = 1` (`moebius_mul_coe_zeta`, `coe_mul_zeta_apply`, `one_apply`).

* **Hyperbola reindexing** (`coprime_count_eq_sum`).  Swapping the order of summation
  turns `P(N)` into `∑_{e ≤ N} μ(e)·⌊N/e⌋²` (the count of multiples of `e` in `[1,N]`
  squared, via `Nat.Ioc_filter_dvd_card_eq_div`), exactly as in `MobiusPartialSum.lean`
  but with a *squared* count.

* **Main term + error.**  Writing `⌊N/e⌋ = N/e − {N/e}` gives
  `⌊N/e⌋² = (N/e)² − (2(N/e){N/e} − {N/e}²)`, so
  `P(N) = N²·∑_{e ≤ N} μ(e)/e² − E`.  The keystone `MobiusZetaTwo.tsum_moebius_div_sq`
  (`∑' μ(e)/e² = 6/π²`) plus a `1/e²`-tail bound gives `N²·∑ = (6/π²)·N² + O(N)`, and
  `|E| ≤ ∑_{e ≤ N}(2N/e + 1) = 2N·H_N + N = O(N log N)` via the harmonic bound
  `H_N ≤ 1 + log N`.  Total error `O(N log N)`.

Imports the keystone (`MobiusZetaTwo`), the floor engine (`MobiusPartialSum`), the `1/e²`
tail engine (`SquarefreeCount`), and the harmonic-sum lemma (`DivisorSummatory`).
-/
import Propositio.NumberTheory.Analytic.MobiusZetaTwo
import Propositio.NumberTheory.Analytic.MobiusPartialSum
import Propositio.NumberTheory.Analytic.DivisorSummatory
import Propositio.NumberTheory.Analytic.SquarefreeCount
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open Finset ArithmeticFunction

set_option maxHeartbeats 1200000

namespace CoprimePairsDensity

/-! ### The coprimality indicator as a Möbius sum over common divisors -/

/-- **Indicator identity.**  For `1 ≤ a,b ≤ N`,
`∑_{e ≤ N} [e ∣ a ∧ e ∣ b]·μ(e) = [Coprime a b]`. -/
theorem moebius_coprime_eq_sum (a b N : ℕ) (ha : 1 ≤ a) (haN : a ≤ N)
    (_hb : 1 ≤ b) (_hbN : b ≤ N) :
    (∑ e ∈ Finset.Icc 1 N, (if e ∣ a ∧ e ∣ b then (ArithmeticFunction.moebius e : ℤ) else 0))
      = if Nat.Coprime a b then 1 else 0 := by
  have hg1 : 1 ≤ Nat.gcd a b := Nat.one_le_iff_ne_zero.mpr (by
    intro h
    rw [Nat.gcd_eq_zero_iff] at h
    omega)
  have hgN : Nat.gcd a b ≤ N :=
    le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)) haN
  -- the common divisors `e ≤ N` of `a` and `b` are exactly the divisors of `gcd a b`
  have hset : (Finset.Icc 1 N).filter (fun e => e ∣ a ∧ e ∣ b) = (Nat.gcd a b).divisors := by
    rw [MobiusPartialSum.divisors_eq_filter_Icc hg1 hgN]
    apply Finset.filter_congr
    intro e _
    rw [Nat.dvd_gcd_iff]
  rw [← Finset.sum_filter, hset, ← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-! ### Hyperbola reindexing of the coprime-pair count -/

/-- **Hyperbola form of the coprime-pair count.**
`#{(a,b) ∈ [1,N]² : gcd(a,b) = 1} = ∑_{e ≤ N} μ(e)·⌊N/e⌋²`. -/
theorem coprime_count_eq_sum (N : ℕ) :
    (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.Coprime p.1 p.2)).card : ℤ)
      = ∑ e ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius e : ℤ) * ((N / e : ℕ) : ℤ) ^ 2 := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  -- replace each indicator by its Möbius sum, then swap the order of summation
  have hstep : ∀ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
      (if Nat.Coprime p.1 p.2 then (1 : ℤ) else 0)
        = ∑ e ∈ Finset.Icc 1 N,
            (if e ∣ p.1 ∧ e ∣ p.2 then (ArithmeticFunction.moebius e : ℤ) else 0) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    exact (moebius_coprime_eq_sum p.1 p.2 N hp.1.1 hp.1.2 hp.2.1 hp.2.2).symm
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  -- the count of `(a,b) ∈ [1,N]²` with `e ∣ a ∧ e ∣ b` is `⌊N/e⌋²`
  have hcount : ((N / e : ℕ) : ℤ) = ∑ a ∈ Finset.Icc 1 N, (if e ∣ a then (1 : ℤ) else 0) := by
    have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hIcc, ← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]
    push_cast
    rfl
  rw [Finset.sum_product]
  -- collapse the inner `b`-sum
  have hinner : ∀ a,
      (∑ b ∈ Finset.Icc 1 N, (if e ∣ a ∧ e ∣ b then (ArithmeticFunction.moebius e : ℤ) else 0))
        = (if e ∣ a then (1 : ℤ) else 0) * ((ArithmeticFunction.moebius e : ℤ) * ((N / e : ℕ) : ℤ)) := by
    intro a
    by_cases ha : e ∣ a
    · have hb : ∀ b, (if e ∣ a ∧ e ∣ b then (ArithmeticFunction.moebius e : ℤ) else 0)
          = (ArithmeticFunction.moebius e : ℤ) * (if e ∣ b then (1 : ℤ) else 0) := by
        intro b; by_cases hb : e ∣ b <;> simp [ha, hb]
      rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum, ← hcount, if_pos ha, one_mul]
    · have hb : ∀ b, (if e ∣ a ∧ e ∣ b then (ArithmeticFunction.moebius e : ℤ) else 0) = 0 := by
        intro b; simp [ha]
      rw [Finset.sum_congr rfl (fun b _ => hb b), if_neg ha]
      simp
  rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.sum_mul, ← hcount]
  ring

/-! ### The asymptotic -/

/-- **Probability that two integers are coprime is `6/π²`.**
With `P(N) = #{(a,b) ∈ [1,N]² : gcd(a,b) = 1}`, we have `P(N) = (6/π²)·N² + O(N log N)`,
here with the explicit constant `C = 6` and threshold `N₀ = 3`:
    `|P(N) − (6/π²)·N²| ≤ 6·N·log N`  for all `N ≥ 3`. -/
theorem coprime_pairs_count_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ)
         - 6 / Real.pi ^ 2 * (N : ℝ) ^ 2| ≤ C * ((N : ℝ) * Real.log N) := by
  refine ⟨6, 3, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- `P(N) = ∑_{e ≤ N} μ(e)·⌊N/e⌋²` over `ℝ`
  have hcount_eq : (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun p => Nat.Coprime p.1 p.2)).card : ℝ)
      = ∑ e ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius e : ℝ) * ((N / e : ℕ) : ℝ) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (coprime_count_eq_sum N)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h
    exact h
  rw [hcount_eq]
  set T : ℝ := ∑ e ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius e : ℝ) / (e : ℝ) ^ 2 with hT
  set E : ℝ := ∑ e ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius e : ℝ)
      * (2 * ((N : ℝ) / (e : ℝ)) * ((N : ℝ) / (e : ℝ) - ((N / e : ℕ) : ℝ))
          - ((N : ℝ) / (e : ℝ) - ((N / e : ℕ) : ℝ)) ^ 2) with hE
  -- `∑ μ(e)·⌊N/e⌋² = N²·T − E`  (the `⌊·⌋ = N/e − {N/e}` split, squared)
  have hF : (∑ e ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius e : ℝ) * ((N / e : ℕ) : ℝ) ^ 2)
      = (N : ℝ) ^ 2 * T - E := by
    rw [hT, hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_Icc] at he
    have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he.1
    have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
    field_simp
    ring
  rw [hF]
  have key : (N : ℝ) ^ 2 * T - E - 6 / Real.pi ^ 2 * (N : ℝ) ^ 2
      = (N : ℝ) ^ 2 * (T - 6 / Real.pi ^ 2) - E := by ring
  rw [key]
  -- ### Main-term tail: `|T − 6/π²| ≤ 1/N`  (identical to the squarefree-count engine)
  have hTbound : |T - 6 / Real.pi ^ 2| ≤ 1 / (N : ℝ) := by
    set a : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 with ha
    set g : ℕ → ℝ := fun d => (1 : ℝ) / (d : ℝ) ^ 2 with hg
    have hnorm : Summable (fun d => ‖a d‖) := by
      apply Summable.of_nonneg_of_le (fun d => norm_nonneg _) ?_
        (Real.summable_one_div_nat_pow.mpr one_lt_two)
      intro d
      simp only [ha, Real.norm_eq_abs, abs_div]
      have hden : |(d : ℝ) ^ 2| = (d : ℝ) ^ 2 := abs_of_nonneg (by positivity)
      rw [hden]
      gcongr
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hsummable : Summable a := hnorm.of_norm
    have hg_sum : Summable g := Real.summable_one_div_nat_pow.mpr one_lt_two
    have habt : ∀ k, ‖a k‖ ≤ g k := by
      intro k
      simp only [ha, hg, Real.norm_eq_abs, abs_div]
      have hden : |(k : ℝ) ^ 2| = (k : ℝ) ^ 2 := abs_of_nonneg (by positivity)
      rw [hden]
      gcongr
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    have htsum : ∑' d, a d = 6 / Real.pi ^ 2 := MobiusZetaTwo.tsum_moebius_div_sq
    have hTrange : (∑ d ∈ Finset.range (N + 1), a d) = T := by
      have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hins, Finset.sum_insert (by simp), show a 0 = 0 from by simp [ha], zero_add, hT]
    have hsplit : (∑ d ∈ Finset.range (N + 1), a d) + ∑' i, a (i + (N + 1)) = 6 / Real.pi ^ 2 := by
      rw [hsummable.sum_add_tsum_nat_add (N + 1), htsum]
    have htail : 6 / Real.pi ^ 2 - T = ∑' i, a (i + (N + 1)) := by
      rw [← hTrange]; linarith [hsplit]
    have hnorm_shift : Summable (fun i => ‖a (i + (N + 1))‖) :=
      (summable_nat_add_iff (N + 1)).mpr hnorm
    have hg_shift : Summable (fun i => g (i + (N + 1))) :=
      (summable_nat_add_iff (N + 1)).mpr hg_sum
    have htail_g : ∑' i, g (i + (N + 1)) ≤ 1 / (N : ℝ) := by
      apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
      intro n
      have hcongr : ∑ i ∈ Finset.range n, g (i + (N + 1))
          = ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + (N : ℝ) + 1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [hg]; push_cast; ring_nf
      rw [hcongr]
      exact SquarefreeCount.sum_range_inv_sq_shift N hN1 n
    have habs : |∑' i, a (i + (N + 1))| ≤ 1 / (N : ℝ) := by
      calc |∑' i, a (i + (N + 1))|
          = ‖∑' i, a (i + (N + 1))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' i, ‖a (i + (N + 1))‖ := norm_tsum_le_tsum_norm hnorm_shift
        _ ≤ ∑' i, g (i + (N + 1)) := Summable.tsum_le_tsum (fun i => habt _) hnorm_shift hg_shift
        _ ≤ 1 / (N : ℝ) := htail_g
    rw [show T - 6 / Real.pi ^ 2 = -(6 / Real.pi ^ 2 - T) by ring, abs_neg, htail]
    exact habs
  have h1 : |(N : ℝ) ^ 2 * (T - 6 / Real.pi ^ 2)| ≤ (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
    calc (N : ℝ) ^ 2 * |T - 6 / Real.pi ^ 2|
        ≤ (N : ℝ) ^ 2 * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hTbound (by positivity)
      _ = (N : ℝ) := by
            rw [mul_one_div, sq, mul_div_assoc, div_self hNne, mul_one]
  -- ### Error term: `|E| ≤ 2N·H_N + N ≤ 2N(1+log N) + N`
  have h2 : |E| ≤ 2 * (N : ℝ) * (1 + Real.log N) + (N : ℝ) := by
    set ψ : ℕ → ℝ := fun e =>
      |(ArithmeticFunction.moebius e : ℝ)
        * (2 * ((N : ℝ) / (e : ℝ)) * ((N : ℝ) / (e : ℝ) - ((N / e : ℕ) : ℝ))
            - ((N : ℝ) / (e : ℝ) - ((N / e : ℕ) : ℝ)) ^ 2)| with hψ
    have hEle : |E| ≤ ∑ e ∈ Finset.Icc 1 N, ψ e := by
      rw [hE]; exact Finset.abs_sum_le_sum_abs _ _
    -- per-term: `ψ e ≤ 2N/e + 1`
    have hψle : ∀ e ∈ Finset.Icc 1 N, ψ e ≤ 2 * ((N : ℝ) / (e : ℝ)) + 1 := by
      intro e he
      rw [Finset.mem_Icc] at he
      have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he.1
      have heN : (e : ℝ) ≤ (N : ℝ) := by exact_mod_cast he.2
      have hNe1 : (1 : ℝ) ≤ (N : ℝ) / (e : ℝ) := by
        rw [le_div_iff₀ hepos]; linarith
      simp only [hψ]
      set r : ℝ := (N : ℝ) / (e : ℝ) - ((N / e : ℕ) : ℝ) with hr
      -- `0 ≤ r ≤ 1` (fractional part)
      have hr0 : 0 ≤ r := by
        rw [hr]
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := e)
        linarith
      have hr1 : r ≤ 1 := by
        rw [hr]
        have hdm : (e : ℝ) * ((N / e : ℕ) : ℝ) + ((N % e : ℕ) : ℝ) = (N : ℝ) := by
          exact_mod_cast Nat.div_add_mod N e
        have hmod : ((N % e : ℕ) : ℝ) < (e : ℝ) := by
          exact_mod_cast Nat.mod_lt N (by omega : 0 < e)
        have hle : (N : ℝ) / (e : ℝ) ≤ ((N / e : ℕ) : ℝ) + 1 := by
          rw [div_le_iff₀ hepos]; nlinarith [hdm, hmod]
        linarith
      -- since `e ≤ N`, `N/e ≥ 1`, so the bracket is nonnegative and `≤ 2N/e + 1`
      have hexpr_nn : 0 ≤ 2 * ((N : ℝ) / (e : ℝ)) * r - r ^ 2 := by
        nlinarith [hr0, hr1, hNe1]
      have hexpr_le : 2 * ((N : ℝ) / (e : ℝ)) * r - r ^ 2 ≤ 2 * ((N : ℝ) / (e : ℝ)) + 1 := by
        nlinarith [hr0, hr1, hNe1]
      have hμ : |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      rw [abs_mul]
      calc |(ArithmeticFunction.moebius e : ℝ)| * |2 * ((N : ℝ) / (e : ℝ)) * r - r ^ 2|
          ≤ 1 * |2 * ((N : ℝ) / (e : ℝ)) * r - r ^ 2| :=
            mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
        _ = 2 * ((N : ℝ) / (e : ℝ)) * r - r ^ 2 := by rw [one_mul, abs_of_nonneg hexpr_nn]
        _ ≤ 2 * ((N : ℝ) / (e : ℝ)) + 1 := hexpr_le
    -- sum the per-term bound
    have hsum_le : ∑ e ∈ Finset.Icc 1 N, ψ e
        ≤ ∑ e ∈ Finset.Icc 1 N, (2 * ((N : ℝ) / (e : ℝ)) + 1) :=
      Finset.sum_le_sum hψle
    -- evaluate the RHS: `2N·H_N + N`
    have hNH : ∑ e ∈ Finset.Icc 1 N, (N : ℝ) / (e : ℝ) = (N : ℝ) * (harmonic N : ℝ) := by
      rw [← DivisorSummatory.sum_inv_eq_harmonic, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [div_eq_mul_inv]
    have hcard : ∑ _e ∈ Finset.Icc 1 N, (1 : ℝ) = (N : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc]; simp
    have hRHS : ∑ e ∈ Finset.Icc 1 N, (2 * ((N : ℝ) / (e : ℝ)) + 1)
        = 2 * (N : ℝ) * (harmonic N : ℝ) + (N : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hNH, hcard]; ring
    have hHbound : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    have hψnn : 0 ≤ ∑ e ∈ Finset.Icc 1 N, ψ e :=
      Finset.sum_nonneg (fun e _ => by rw [hψ]; exact abs_nonneg _)
    calc |E| ≤ ∑ e ∈ Finset.Icc 1 N, ψ e := hEle
      _ ≤ ∑ e ∈ Finset.Icc 1 N, (2 * ((N : ℝ) / (e : ℝ)) + 1) := hsum_le
      _ = 2 * (N : ℝ) * (harmonic N : ℝ) + (N : ℝ) := hRHS
      _ ≤ 2 * (N : ℝ) * (1 + Real.log N) + (N : ℝ) := by
            have : 2 * (N : ℝ) * (harmonic N : ℝ) ≤ 2 * (N : ℝ) * (1 + Real.log N) :=
              mul_le_mul_of_nonneg_left hHbound (by positivity)
            linarith
  -- ### Combine: total error `≤ 2N log N + 4N ≤ 6 N log N` for `N ≥ 3`
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by
      have hexp : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) h3
  calc |(N : ℝ) ^ 2 * (T - 6 / Real.pi ^ 2) - E|
      ≤ |(N : ℝ) ^ 2 * (T - 6 / Real.pi ^ 2)| + |E| := by
        have h := abs_add_le ((N : ℝ) ^ 2 * (T - 6 / Real.pi ^ 2)) (-E)
        simpa [sub_eq_add_neg, abs_neg] using h
    _ ≤ (N : ℝ) + (2 * (N : ℝ) * (1 + Real.log N) + (N : ℝ)) := by linarith [h1, h2]
    _ ≤ 6 * ((N : ℝ) * Real.log N) := by
        nlinarith [hlogN, hNpos, mul_nonneg hNpos.le (sub_nonneg.mpr hlogN)]

end CoprimePairsDensity
