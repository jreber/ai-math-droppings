/-
# Asymptotic density of squarefree numbers `#{n ≤ N : Squarefree n} = (6/π²)·N + O(√N)`

The classical squarefree-counting estimate, a genuine mathlib gap.  With
`Q(N) = #{n ∈ [1,N] : Squarefree n}` we prove
    `Q(N) = (6/π²)·N + O(√N)`,
with the **leading constant `6/π²` exact** and an explicit `O(√N)` error
(constant `C = 6`, threshold `N₀ = 1`):
    `|Q(N) − (6/π²)·N| ≤ 6·√N`  for all `N ≥ 1`.

The argument is the standard squarefree sieve / hyperbola split:

* **Indicator identity** (`moebius_sq_eq_sum`).  For `1 ≤ n ≤ N`,
    `∑_{d ≤ N} [d² ∣ n]·μ(d) = [Squarefree n]`.
  Proved via the square-decomposition `n = b²·a` with `a` squarefree
  (`Nat.sq_mul_squarefree_of_pos`): a `p`-adic valuation computation shows
  `{d : d² ∣ n} = b.divisors`, and `∑_{d ∣ b} μ(d) = [b = 1] = [Squarefree n]`
  via the Möbius convolution `μ ∗ ζ = 1`.

* **Hyperbola reindexing** (`squarefree_count_eq_sum`).  Swapping the order of
  summation turns `Q(N)` into `∑_{d ≤ N} μ(d)·⌊N/d²⌋` (`Nat.Ioc_filter_dvd_card_eq_div`
  with divisor `d²`), exactly as in `MobiusPartialSum.lean`.

* **Main term + error.**  Writing `⌊N/d²⌋ = N/d² − {N/d²}` gives
  `Q(N) = N·∑_{d ≤ N} μ(d)/d² − E`.  The keystone `MobiusZetaTwo.tsum_moebius_div_sq`
  (`∑' μ(d)/d² = 6/π²`) plus a telescoping `1/d²`-tail bound gives
  `N·∑_{d ≤ N} μ(d)/d² = (6/π²)·N + O(1)`, and a Dirichlet split of `E` at `√N`
  (the `d ≤ √N` block contributes `≤ √N` fractional parts; the `d > √N` block has
  `⌊N/d²⌋ = 0`, so `{N/d²} = N/d²` and telescopes to `N/√N = O(√N)`) gives
  `|E| ≤ 2√N + 3`.  Total error `O(√N)`.

Imports the keystone (`MobiusZetaTwo`) and the floor-engine file (`MobiusPartialSum`).
-/
import Propositio.NumberTheory.Analytic.MobiusZetaTwo
import Propositio.NumberTheory.Analytic.MobiusPartialSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset ArithmeticFunction

set_option maxHeartbeats 1200000

namespace SquarefreeCount

/-! ### A telescoping `1/d²` tail bound (shared) -/

/-- Telescoping bound: `∑_{i<K} 1/(i+M+1)² ≤ 1/M` for `M ≥ 1`. -/
theorem sum_range_inv_sq_shift (M : ℕ) (hM : 1 ≤ M) (K : ℕ) :
    ∑ i ∈ Finset.range K, (1 : ℝ) / ((i : ℝ) + (M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) := by
  set h : ℕ → ℝ := fun j => 1 / ((j : ℝ) + M) with hh
  have hsub : ∑ i ∈ Finset.range K, (h i - h (i + 1)) = h 0 - h K :=
    Finset.sum_range_sub' h K
  have hle : ∑ i ∈ Finset.range K, (1 : ℝ) / ((i : ℝ) + M + 1) ^ 2
      ≤ ∑ i ∈ Finset.range K, (h i - h (i + 1)) := by
    apply Finset.sum_le_sum
    intro i _
    have ha : (0 : ℝ) < (i : ℝ) + M := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      linarith
    have hb : (0 : ℝ) < (i : ℝ) + M + 1 := by linarith
    have hne1 : ((i : ℝ) + M) ≠ 0 := ne_of_gt ha
    have hne2 : ((i : ℝ) + M + 1) ≠ 0 := ne_of_gt hb
    have hval : h i - h (i + 1) = 1 / (((i : ℝ) + M) * ((i : ℝ) + M + 1)) := by
      rw [hh]; push_cast; field_simp; ring
    rw [hval]
    apply one_div_le_one_div_of_le (mul_pos ha hb)
    nlinarith [ha, hb]
  have hh0 : h 0 = 1 / (M : ℝ) := by rw [hh]; push_cast; ring
  have hhK : 0 ≤ h K := by rw [hh]; positivity
  calc ∑ i ∈ Finset.range K, (1 : ℝ) / ((i : ℝ) + M + 1) ^ 2
      ≤ ∑ i ∈ Finset.range K, (h i - h (i + 1)) := hle
    _ = h 0 - h K := hsub
    _ ≤ h 0 := by linarith
    _ = 1 / (M : ℝ) := hh0

/-- Finite tail of the `1/d²`-series: `∑_{M < d ≤ N} 1/d² ≤ 1/M` for `M ≥ 1`. -/
theorem finite_inv_sq_tail (M N : ℕ) (hM : 1 ≤ M) :
    ∑ d ∈ Finset.Ioc M N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  have hIoc : Finset.Ioc M N = Finset.Ico (M + 1) (N + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hcongr : ∑ i ∈ Finset.range (N + 1 - (M + 1)), (1 : ℝ) / ((M + 1 + i : ℕ) : ℝ) ^ 2
      = ∑ i ∈ Finset.range (N + 1 - (M + 1)), (1 : ℝ) / ((i : ℝ) + (M : ℝ) + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    push_cast; ring_nf
  rw [hcongr]
  exact sum_range_inv_sq_shift M hM _

/-! ### The squarefree indicator as a Möbius sum over square divisors -/

/-- **Indicator identity.**  For `1 ≤ n ≤ N`,
`∑_{d ≤ N} [d² ∣ n]·μ(d) = [Squarefree n]`. -/
theorem moebius_sq_eq_sum (n N : ℕ) (h1 : 1 ≤ n) (hnN : n ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℤ) else 0))
      = if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, hab, hasq⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < n by omega)
  have hn0 : n ≠ 0 := by omega
  have hb0' : b ≠ 0 := by omega
  have ha0' : a ≠ 0 := by omega
  -- `d² ∣ n ↔ d ∣ b` for `d ≠ 0` (valuation computation)
  have hdvd_iff : ∀ d : ℕ, d ≠ 0 → (d ^ 2 ∣ n ↔ d ∣ b) := by
    intro d hd
    constructor
    · intro hd2
      rw [← Nat.factorization_le_iff_dvd hd hb0', Finsupp.le_def]
      intro p
      have hle : (d ^ 2).factorization p ≤ n.factorization p :=
        ((Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) hn0).mpr hd2) p
      have hnf : n.factorization p = 2 * b.factorization p + a.factorization p := by
        conv_lhs => rw [← hab]
        rw [Nat.factorization_mul (pow_ne_zero 2 hb0') ha0', Nat.factorization_pow]
        simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      have hd2f : (d ^ 2).factorization p = 2 * d.factorization p := by
        rw [Nat.factorization_pow]
        simp [Finsupp.smul_apply, smul_eq_mul]
      have hale : a.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one ha0').mp hasq p
      rw [hd2f, hnf] at hle
      omega
    · intro hdb
      exact (pow_dvd_pow_of_dvd hdb 2).trans ⟨a, hab.symm⟩
  -- `b ≤ N`
  have hb_dvd_n : b ∣ n := (dvd_pow_self b (two_ne_zero)).trans ⟨a, hab.symm⟩
  have hbN : b ≤ N := le_trans (Nat.le_of_dvd (by omega) hb_dvd_n) hnN
  -- the filtered square-divisor set is exactly `b.divisors`
  have hset : (Finset.Icc 1 N).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _hdN⟩, hd2⟩
      exact ⟨(hdvd_iff d (by omega)).mp hd2, hb0'⟩
    · rintro ⟨hdb, _⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdb (by omega)
      exact ⟨⟨hd1, le_trans (Nat.le_of_dvd (by omega) hdb) hbN⟩,
        (hdvd_iff d (by omega)).mpr hdb⟩
  -- `Squarefree n ↔ b = 1`
  have hsf : Squarefree n ↔ b = 1 := by
    constructor
    · intro hsq
      by_contra hb1
      obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hb1
      have hppn : p * p ∣ n := by
        have hpp : p * p ∣ b * b := mul_dvd_mul hpb hpb
        have hbb : b * b ∣ n := ⟨a, by rw [← hab]; ring⟩
        exact hpp.trans hbb
      exact (hp.one_lt.ne') (Nat.isUnit_iff.mp (hsq p hppn))
    · intro hb1
      rw [← hab, hb1, one_pow, one_mul]
      exact hasq
  rw [← Finset.sum_filter, hset, ← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  simp only [hsf]

/-! ### Hyperbola reindexing of the squarefree count -/

/-- **Hyperbola form of the squarefree count.**
`#{n ∈ [1,N] : Squarefree n} = ∑_{d ≤ N} μ(d)·⌊N/d²⌋`. -/
theorem squarefree_count_eq_sum (N : ℕ) :
    (((Finset.Icc 1 N).filter Squarefree).card : ℤ)
      = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_congr rfl
      (fun n hn => (moebius_sq_eq_sum n N (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2).symm),
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hcount : ((N / d ^ 2 : ℕ) : ℤ)
      = ∑ n ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (1 : ℤ) else 0) := by
    have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hIcc, ← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]
    push_cast
    rfl
  calc ∑ n ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℤ) else 0)
      = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℤ) * (if d ^ 2 ∣ n then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases h : d ^ 2 ∣ n <;> simp [h]
    _ = (ArithmeticFunction.moebius d : ℤ) * ∑ n ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (1 : ℤ) else 0) := by
        rw [Finset.mul_sum]
    _ = (ArithmeticFunction.moebius d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by rw [← hcount]

/-! ### The asymptotic -/

/-- **Asymptotic density of squarefree numbers.**
With `Q(N) = #{n ∈ [1,N] : Squarefree n}`, we have `Q(N) = (6/π²)·N + O(√N)`,
here with the explicit constant `C = 6` and threshold `N₀ = 1`:
    `|Q(N) − (6/π²)·N| ≤ 6·√N`  for all `N ≥ 1`. -/
theorem squarefree_count_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(((Finset.Icc 1 N).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * (N : ℝ)|
        ≤ C * Real.sqrt N := by
  refine ⟨6, 1, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- `Q(N) = ∑_{d ≤ N} μ(d)·⌊N/d²⌋` over `ℝ`
  have hcount_eq : (((Finset.Icc 1 N).filter Squarefree).card : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (squarefree_count_eq_sum N)
    push_cast at h
    exact h
  rw [hcount_eq]
  set T : ℝ := ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 with hT
  set E : ℝ := ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ)) with hE
  have hF : (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ))
      = (N : ℝ) * T - E := by
    rw [hT, hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hF]
  have key : (N : ℝ) * T - E - 6 / Real.pi ^ 2 * N
      = (N : ℝ) * (T - 6 / Real.pi ^ 2) - E := by ring
  rw [key]
  -- ### Main-term tail: `|T − 6/π²| ≤ 1/N`
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
    -- `T = ∑_{d < N+1} a d`
    have hTrange : (∑ d ∈ Finset.range (N + 1), a d) = T := by
      have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hins, Finset.sum_insert (by simp), show a 0 = 0 from by simp [ha], zero_add, hT]
    -- split: `6/π² − T = ∑' a (i+N+1)`
    have hsplit : (∑ d ∈ Finset.range (N + 1), a d) + ∑' i, a (i + (N + 1)) = 6 / Real.pi ^ 2 := by
      rw [hsummable.sum_add_tsum_nat_add (N + 1), htsum]
    have htail : 6 / Real.pi ^ 2 - T = ∑' i, a (i + (N + 1)) := by
      rw [← hTrange]; linarith [hsplit]
    -- bound the tail
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
      exact sum_range_inv_sq_shift N hN n
    have habs : |∑' i, a (i + (N + 1))| ≤ 1 / (N : ℝ) := by
      calc |∑' i, a (i + (N + 1))|
          = ‖∑' i, a (i + (N + 1))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' i, ‖a (i + (N + 1))‖ := norm_tsum_le_tsum_norm hnorm_shift
        _ ≤ ∑' i, g (i + (N + 1)) := Summable.tsum_le_tsum (fun i => habt _) hnorm_shift hg_shift
        _ ≤ 1 / (N : ℝ) := htail_g
    rw [show T - 6 / Real.pi ^ 2 = -(6 / Real.pi ^ 2 - T) by ring, abs_neg, htail]
    exact habs
  have h1 : |(N : ℝ) * (T - 6 / Real.pi ^ 2)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hNpos]
    calc (N : ℝ) * |T - 6 / Real.pi ^ 2|
        ≤ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hTbound (le_of_lt hNpos)
      _ = 1 := by field_simp
  -- ### Error term: `|E| ≤ 2√N + 3`
  have h2 : |E| ≤ 2 * Real.sqrt N + 3 := by
    set φ : ℕ → ℝ := fun d =>
      |(ArithmeticFunction.moebius d : ℝ) * ((N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ))| with hφ
    have hEle : |E| ≤ ∑ d ∈ Finset.Icc 1 N, φ d := by
      rw [hE]; exact Finset.abs_sum_le_sum_abs _ _
    set M := Nat.sqrt N with hMdef
    have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.le_sqrt'.mpr (by simpa using hN)
    have hMN : M ≤ N := by rw [hMdef]; exact Nat.sqrt_le_self N
    have hMRpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have hss : N < (M + 1) ^ 2 := by rw [hMdef]; exact Nat.lt_succ_sqrt' N
    have hMsqleN : M ^ 2 ≤ N := by rw [hMdef]; exact Nat.sqrt_le' N
    have hMsqle : (M : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hMsqleN
    have hNltsucc : (N : ℝ) < ((M : ℝ) + 1) ^ 2 := by exact_mod_cast hss
    have hMle : (M : ℝ) ≤ Real.sqrt N := by
      rw [show (M : ℝ) = Real.sqrt ((M : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hMsqle
    -- fractional part bounds
    have hfrac : ∀ d : ℕ, 1 ≤ d →
        0 ≤ (N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ)
        ∧ (N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ) ≤ 1 := by
      intro d hd1
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hd2pos : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos hdpos 2
      have hd2nat : 0 < d ^ 2 := pow_pos (show 0 < d by omega) 2
      refine ⟨?_, ?_⟩
      · have h := Nat.cast_div_le (α := ℝ) (m := N) (n := d ^ 2)
        push_cast at h
        linarith [h]
      · have hdiv : d ^ 2 * (N / d ^ 2) + N % d ^ 2 = N := Nat.div_add_mod N (d ^ 2)
        have hmod : N % d ^ 2 < d ^ 2 := Nat.mod_lt N hd2nat
        have hle : (N : ℝ) / (d : ℝ) ^ 2 ≤ ((N / d ^ 2 : ℕ) : ℝ) + 1 := by
          rw [div_le_iff₀ hd2pos]
          have hcast : ((d ^ 2 : ℕ) : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) + ((N % d ^ 2 : ℕ) : ℝ) = (N : ℝ) := by
            exact_mod_cast hdiv
          have hmodR : ((N % d ^ 2 : ℕ) : ℝ) < ((d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmod
          push_cast at hcast hmodR
          nlinarith [hcast, hmodR]
        linarith [hle]
    have hμle : ∀ d, |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := fun d => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    -- block `d ≤ M`: each `φ d ≤ 1`
    have hpart1 : ∑ d ∈ Finset.Ioc 0 M, φ d ≤ (M : ℝ) := by
      calc ∑ d ∈ Finset.Ioc 0 M, φ d
          ≤ ∑ _d ∈ Finset.Ioc 0 M, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro d hd
            rw [Finset.mem_Ioc] at hd
            have hd1 : 1 ≤ d := hd.1
            have hf := hfrac d hd1
            calc φ d = |(ArithmeticFunction.moebius d : ℝ)|
                      * |(N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ)| := by rw [hφ]; exact abs_mul _ _
              _ = |(ArithmeticFunction.moebius d : ℝ)|
                      * ((N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ)) := by rw [abs_of_nonneg hf.1]
              _ ≤ 1 * 1 := mul_le_mul (hμle d) hf.2 hf.1 (by norm_num)
              _ = 1 := by norm_num
        _ = (M : ℝ) := by
            rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one]
    -- block `d > M`: `⌊N/d²⌋ = 0`, so `φ d ≤ N/d²`, and the tail telescopes
    have hpart2 : ∑ d ∈ Finset.Ioc M N, φ d ≤ (N : ℝ) * (1 / (M : ℝ)) := by
      calc ∑ d ∈ Finset.Ioc M N, φ d
          ≤ ∑ d ∈ Finset.Ioc M N, (N : ℝ) / (d : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro d hd
            rw [Finset.mem_Ioc] at hd
            have hd1 : 1 ≤ d := by omega
            have hdM : M + 1 ≤ d := hd.1
            have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
            have hd2gt : N < d ^ 2 := lt_of_lt_of_le hss (Nat.pow_le_pow_left hdM 2)
            have hq0 : (N / d ^ 2 : ℕ) = 0 := Nat.div_eq_of_lt hd2gt
            have hfraceq : (N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ) = (N : ℝ) / (d : ℝ) ^ 2 := by
              rw [hq0]; simp
            have hfrnn : (0 : ℝ) ≤ (N : ℝ) / (d : ℝ) ^ 2 := by positivity
            calc φ d = |(ArithmeticFunction.moebius d : ℝ)|
                      * |(N : ℝ) / (d : ℝ) ^ 2 - ((N / d ^ 2 : ℕ) : ℝ)| := by rw [hφ]; exact abs_mul _ _
              _ = |(ArithmeticFunction.moebius d : ℝ)| * ((N : ℝ) / (d : ℝ) ^ 2) := by
                    rw [hfraceq, abs_of_nonneg hfrnn]
              _ ≤ 1 * ((N : ℝ) / (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (hμle d) hfrnn
              _ = (N : ℝ) / (d : ℝ) ^ 2 := by ring
        _ = (N : ℝ) * ∑ d ∈ Finset.Ioc M N, (1 : ℝ) / (d : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _; ring
        _ ≤ (N : ℝ) * (1 / (M : ℝ)) :=
            mul_le_mul_of_nonneg_left (finite_inv_sq_tail M N hM1) (le_of_lt hNpos)
    have hNM : (N : ℝ) * (1 / (M : ℝ)) ≤ Real.sqrt N + 3 := by
      rw [mul_one_div]
      have e1 : ((M : ℝ) + 1) ^ 2 / (M : ℝ) = (M : ℝ) + 2 + 1 / (M : ℝ) := by
        field_simp; ring
      have hinvle : 1 / (M : ℝ) ≤ 1 := by rw [div_le_one hMRpos]; exact_mod_cast hM1
      calc (N : ℝ) / (M : ℝ)
          ≤ ((M : ℝ) + 1) ^ 2 / (M : ℝ) := by
            have hN_le : (N : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := le_of_lt hNltsucc
            gcongr
        _ = (M : ℝ) + 2 + 1 / (M : ℝ) := e1
        _ ≤ Real.sqrt N + 2 + 1 := by linarith [hMle, hinvle]
        _ = Real.sqrt N + 3 := by ring
    -- assemble
    have hIcc0N : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hsumsplit : ∑ d ∈ Finset.Ioc 0 N, φ d
        = ∑ d ∈ Finset.Ioc 0 M, φ d + ∑ d ∈ Finset.Ioc M N, φ d :=
      (Finset.sum_Ioc_consecutive φ (Nat.zero_le M) hMN).symm
    calc |E| ≤ ∑ d ∈ Finset.Icc 1 N, φ d := hEle
      _ = ∑ d ∈ Finset.Ioc 0 M, φ d + ∑ d ∈ Finset.Ioc M N, φ d := by rw [hIcc0N, hsumsplit]
      _ ≤ (M : ℝ) + (Real.sqrt N + 3) := add_le_add hpart1 (le_trans hpart2 hNM)
      _ ≤ 2 * Real.sqrt N + 3 := by linarith [hMle]
  -- ### Combine
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  calc |(N : ℝ) * (T - 6 / Real.pi ^ 2) - E|
      ≤ |(N : ℝ) * (T - 6 / Real.pi ^ 2)| + |E| := by
        have h := abs_add_le ((N : ℝ) * (T - 6 / Real.pi ^ 2)) (-E)
        simpa [sub_eq_add_neg, abs_neg] using h
    _ ≤ 1 + (2 * Real.sqrt N + 3) := by linarith [h1, h2]
    _ ≤ 6 * Real.sqrt N := by nlinarith [hsqrt1]

end SquarefreeCount
