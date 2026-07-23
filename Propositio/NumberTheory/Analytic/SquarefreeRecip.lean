/-
# Reciprocal sum of squarefree numbers `∑_{n≤N} μ(n)²/n = (6/π²)·log N + O(1)`

The squarefree-reciprocal (or "average of `μ²/n`") estimate, a genuine mathlib gap.
Writing `μ(n)² = [Squarefree n]`, we prove
    `∑_{n≤N} μ(n)²/n = (6/π²)·log N + O(1)`,
with the **leading constant `6/π²` exact** and an explicit **constant** error term
`O(1)` (the error is bounded by a single absolute constant `C`, independent of `N`).

The argument is the standard squarefree convolution / hyperbola split:

* **Indicator identity** (reusing `SquarefreeCount.moebius_sq_eq_sum`).  For `1 ≤ n ≤ N`,
    `μ(n)² = [Squarefree n] = ∑_{d ≤ N} [d² ∣ n]·μ(d)`.

* **Reindexing** (`recip_eq_sum`).  Substituting `n = d²·m` and swapping summation order,
    `∑_{n≤N} μ(n)²/n = ∑_{d≤N} (μ(d)/d²)·H_{⌊N/d²⌋}`,
  where `H_M = ∑_{m≤M} 1/m` is the harmonic number (`DivisorSummatory.sum_inv_eq_harmonic`).

* **Main term + error.**  For `d ≤ √N` the floor `Q = ⌊N/d²⌋ ≥ 1` and the mathlib harmonic
  bounds `log(Q+1) ≤ H_Q ≤ 1 + log Q` pinch
    `log N − 2 log d ≤ H_{⌊N/d²⌋} ≤ 1 + log N − 2 log d`,
  so `|H_{⌊N/d²⌋} − log N| ≤ 2 log d + 1`.  Splitting at `M = ⌊√N⌋` (the `d > M` block has
  `⌊N/d²⌋ = 0`, hence `H = 0`),
    `∑ = log N · ∑_{d≤M} μ(d)/d²  +  ∑_{d≤M} (μ(d)/d²)(H_{⌊N/d²⌋} − log N)`.
  The keystone `MobiusZetaTwo.tsum_moebius_div_sq` (`∑' μ(d)/d² = 6/π²`) with a telescoping
  `1/d²` tail (`SquarefreeCount.sum_range_inv_sq_shift`) gives
    `log N · ∑_{d≤M} μ(d)/d² = (6/π²) log N + O(1)`   (since `log N / √N` is bounded),
  while `|∑_{d≤M}(μ(d)/d²)(H − log N)| ≤ ∑_d (2 log d + 1)/d² = O(1)`, the latter convergent
  because `∑ (log d)/d²` converges (comparison `log d ≤ 2√d` with `∑ d^{-3/2}`).

Reuses the keystone (`MobiusZetaTwo`), the squarefree sieve (`SquarefreeCount`), the harmonic
engine (`DivisorSummatory`), and the floor reindexing (`MobiusPartialSum`).
-/
import Propositio.NumberTheory.Analytic.SquarefreeCount
import Propositio.NumberTheory.Analytic.MobiusZetaTwo
import Propositio.NumberTheory.Analytic.DivisorSummatory
import Propositio.NumberTheory.Analytic.MobiusPartialSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open Finset ArithmeticFunction

set_option maxHeartbeats 1600000

namespace SquarefreeRecip

/-! ### `μ(n)²` as a squarefree indicator over `ℝ` -/

/-- `(μ n)² = [Squarefree n]` over `ℝ`. -/
theorem moebius_sq_real (n : ℕ) :
    ((moebius n : ℝ))^2 = if Squarefree n then 1 else 0 := by
  by_cases h : Squarefree n
  · rw [if_pos h, moebius_apply_of_squarefree h]; push_cast
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  · rw [if_neg h, moebius_eq_zero_of_not_squarefree h]; simp

/-! ### Convergence of `∑ (log d)/d²` -/

/-- `∑_d (log d)/d²` converges (comparison `log d ≤ 2√d` against `∑ d^{-3/2}`). -/
theorem summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  have hg : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 2
  apply Summable.of_nonneg_of_le ?_ ?_ hg
  · intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      exact div_nonneg (Real.log_nonneg this) (by positivity)
  · intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hsqpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
      have hl1 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hsqpos
      have hl2 : Real.log (Real.sqrt n) = Real.log n / 2 := Real.log_sqrt (le_of_lt hnpos)
      have hlog : Real.log n ≤ 2 * Real.sqrt n := by nlinarith [hl1, hl2]
      have hsplit : (n : ℝ) ^ 2 = (n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos, ← Real.rpow_natCast (n : ℝ) 2]
        norm_num
      have h32pos : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hnpos _
      rw [hsplit, div_le_iff₀ (by positivity), mul_comm 2 (1 / (n : ℝ) ^ ((3 : ℝ) / 2)),
        mul_assoc, one_div, inv_mul_eq_div, le_div_iff₀ h32pos]
      nlinarith [hlog, hsqpos, h32pos, Real.sqrt_nonneg (n : ℝ)]

/-! ### Tail of the Möbius zeta-two partial sum -/

/-- `|∑_{d≤M} μ(d)/d² − 6/π²| ≤ 1/M`, the keystone `∑' μ(d)/d² = 6/π²` truncated at `M`.
Mirrors the inline argument in `SquarefreeCount.squarefree_count_asymptotic`. -/
theorem abs_sum_moebius_div_sq_sub (M : ℕ) (hM : 1 ≤ M) :
    |(∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤ 1 / (M : ℝ) := by
  set a : ℕ → ℝ := fun d => (moebius d : ℝ) / (d : ℝ) ^ 2 with ha
  set g : ℕ → ℝ := fun d => (1 : ℝ) / (d : ℝ) ^ 2 with hg
  set T : ℝ := ∑ d ∈ Finset.Icc 1 M, a d with hT
  have hnorm : Summable (fun d => ‖a d‖) := by
    apply Summable.of_nonneg_of_le (fun d => norm_nonneg _) ?_
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    intro d
    simp only [ha, Real.norm_eq_abs, abs_div]
    have hden : |(d : ℝ) ^ 2| = (d : ℝ) ^ 2 := abs_of_nonneg (by positivity)
    rw [hden]; gcongr
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hsummable : Summable a := hnorm.of_norm
  have hg_sum : Summable g := Real.summable_one_div_nat_pow.mpr one_lt_two
  have habt : ∀ k, ‖a k‖ ≤ g k := by
    intro k
    simp only [ha, hg, Real.norm_eq_abs, abs_div]
    have hden : |(k : ℝ) ^ 2| = (k : ℝ) ^ 2 := abs_of_nonneg (by positivity)
    rw [hden]; gcongr
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  have htsum : ∑' d, a d = 6 / Real.pi ^ 2 := MobiusZetaTwo.tsum_moebius_div_sq
  have hTrange : (∑ d ∈ Finset.range (M + 1), a d) = T := by
    have hins : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp), show a 0 = 0 from by simp [ha], zero_add, hT]
  have hsplit : (∑ d ∈ Finset.range (M + 1), a d) + ∑' i, a (i + (M + 1)) = 6 / Real.pi ^ 2 := by
    rw [hsummable.sum_add_tsum_nat_add (M + 1), htsum]
  have htail : 6 / Real.pi ^ 2 - T = ∑' i, a (i + (M + 1)) := by
    rw [← hTrange]; linarith [hsplit]
  have hnorm_shift : Summable (fun i => ‖a (i + (M + 1))‖) :=
    (summable_nat_add_iff (M + 1)).mpr hnorm
  have hg_shift : Summable (fun i => g (i + (M + 1))) :=
    (summable_nat_add_iff (M + 1)).mpr hg_sum
  have htail_g : ∑' i, g (i + (M + 1)) ≤ 1 / (M : ℝ) := by
    apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
    intro n
    have hcongr : ∑ i ∈ Finset.range n, g (i + (M + 1))
        = ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + (M : ℝ) + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _; simp only [hg]; push_cast; ring_nf
    rw [hcongr]
    exact SquarefreeCount.sum_range_inv_sq_shift M hM n
  have habs : |∑' i, a (i + (M + 1))| ≤ 1 / (M : ℝ) := by
    calc |∑' i, a (i + (M + 1))|
        = ‖∑' i, a (i + (M + 1))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' i, ‖a (i + (M + 1))‖ := norm_tsum_le_tsum_norm hnorm_shift
      _ ≤ ∑' i, g (i + (M + 1)) := Summable.tsum_le_tsum (fun i => habt _) hnorm_shift hg_shift
      _ ≤ 1 / (M : ℝ) := htail_g
  rw [show T - 6 / Real.pi ^ 2 = -(6 / Real.pi ^ 2 - T) by ring, abs_neg, htail]
  exact habs

/-! ### Reindexing: `∑_{n≤N} μ(n)²/n = ∑_{d≤N} (μ(d)/d²)·H_{⌊N/d²⌋}` -/

/-- **Reindexing identity.** Substituting `n = d²·m` and swapping the order of summation. -/
theorem recip_eq_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((moebius n : ℝ) ^ 2) / (n : ℝ))
      = ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) / (d : ℝ) ^ 2 * (harmonic (N / d ^ 2) : ℝ) := by
  -- step 1: `(μ n)² = ∑_d [d²∣n]·μ(d)` over `ℝ`, then divide by `n`
  have e1 : (∑ n ∈ Finset.Icc 1 N, ((moebius n : ℝ) ^ 2) / (n : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          (if d ^ 2 ∣ n then (moebius d : ℝ) else 0) / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [← Finset.sum_div]
    congr 1
    rw [moebius_sq_real]
    have hint := SquarefreeCount.moebius_sq_eq_sum n N hn.1 hn.2
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hint
    push_cast at hcast
    exact hcast.symm
  rw [e1, Finset.sum_comm]
  -- step 2: per `d`, reindex the inner sum
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd1 : 1 ≤ d := hd.1
  have hk : 0 < d ^ 2 := by positivity
  -- collapse the `if` into a filtered sum
  have hfilter : ∑ n ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (moebius d : ℝ) else 0) / (n : ℝ)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n), (moebius d : ℝ) / (n : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : d ^ 2 ∣ n <;> simp [h]
  rw [hfilter]
  -- factor `μ(d)`
  have hfac : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n), (moebius d : ℝ) / (n : ℝ)
      = (moebius d : ℝ) * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n), (1 : ℝ) / (n : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
  rw [hfac]
  -- reindex `n = d²·m`
  have hre : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n), (1 : ℝ) / (n : ℝ)
      = ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (1 : ℝ) / ((d ^ 2 * m : ℕ) : ℝ) := by
    refine (Finset.sum_nbij' (fun m => d ^ 2 * m) (fun n => n / d ^ 2) ?_ ?_ ?_ ?_ ?_).symm
    · intro m hm
      rw [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · nlinarith [hm.1, hk]
      · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hk).mp hm.2
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
      exact ⟨(Nat.one_le_div_iff hk).mpr (Nat.le_of_dvd (by omega) hdvd),
        Nat.div_le_div_right hnN⟩
    · intro m _; exact Nat.mul_div_cancel_left m hk
    · intro n hn
      rw [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _; rfl
  rw [hre]
  -- pull out `1/d²` and recognise the harmonic number
  have hpull : ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (1 : ℝ) / ((d ^ 2 * m : ℕ) : ℝ)
      = (1 / (d : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (1 : ℝ) / (m : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by
      have : 1 ≤ m := hm.1; positivity
    push_cast
    field_simp
  have hharm : ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (1 : ℝ) / (m : ℝ) = (harmonic (N / d ^ 2) : ℝ) := by
    rw [← DivisorSummatory.sum_inv_eq_harmonic]
    apply Finset.sum_congr rfl; intro m _; rw [one_div]
  rw [hpull, hharm]
  ring

/-! ### The asymptotic -/

/-- **Reciprocal sum of squarefree numbers.**
`∑_{n≤N} μ(n)²/n = (6/π²)·log N + O(1)`, with the leading constant `6/π²` exact and a
constant (`O(1)`) error: there is an absolute `C` with
`|∑_{n≤N} μ(n)²/n − (6/π²)·log N| ≤ C` for all `N ≥ 1`. -/
theorem squarefree_recip_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℝ) ^ 2) / (n : ℝ))
        - 6 / Real.pi ^ 2 * Real.log N| ≤ C := by
  have hsumB : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := summable_log_div_sq
  have hsumC : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  set CB : ℝ := ∑' (n : ℕ), Real.log (n : ℝ) / (n : ℝ) ^ 2 with hCB
  set CC : ℝ := ∑' (n : ℕ), (1 : ℝ) / (n : ℝ) ^ 2 with hCC
  refine ⟨2 + 2 * CB + CC, 1, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN_nonneg : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  set M := Nat.sqrt N with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.le_sqrt'.mpr (by simpa using hN)
  have hMN : M ≤ N := by rw [hMdef]; exact Nat.sqrt_le_self N
  have hMRpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hMsqleN : M ^ 2 ≤ N := by rw [hMdef]; exact Nat.sqrt_le' N
  have hss : N < (M + 1) ^ 2 := by rw [hMdef]; exact Nat.lt_succ_sqrt' N
  -- `log N ≤ 2 M`
  have hlogN_le : Real.log N ≤ 2 * (M : ℝ) := by
    have h1 : (N : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by
      have : N ≤ (M + 1) ^ 2 := le_of_lt hss
      calc (N : ℝ) ≤ (((M + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
        _ = ((M : ℝ) + 1) ^ 2 := by push_cast; ring
    have h2 : Real.log N ≤ Real.log (((M : ℝ) + 1) ^ 2) := Real.log_le_log hNpos h1
    have h3 : Real.log (((M : ℝ) + 1) ^ 2) = 2 * Real.log ((M : ℝ) + 1) := by
      rw [Real.log_pow]; push_cast; ring
    have h4 : Real.log ((M : ℝ) + 1) ≤ (M : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (M : ℝ) + 1 by positivity)
      linarith
    rw [h3] at h2; linarith
  -- rewrite the sum and drop the `d > √N` tail (where `H_{⌊N/d²⌋} = H_0 = 0`)
  rw [recip_eq_sum N]
  have htail0 : (∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) / (d : ℝ) ^ 2 * (harmonic (N / d ^ 2) : ℝ))
      = ∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2 * (harmonic (N / d ^ 2) : ℝ) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro d hd; rw [Finset.mem_Icc] at hd ⊢; exact ⟨hd.1, le_trans hd.2 hMN⟩
    · intro d hdN hdM
      rw [Finset.mem_Icc] at hdN
      have hdgt : M < d := by
        by_contra hle
        exact hdM (Finset.mem_Icc.mpr ⟨hdN.1, Nat.le_of_not_lt hle⟩)
      have hNd2 : N < d ^ 2 := lt_of_lt_of_le hss (Nat.pow_le_pow_left (by omega : M + 1 ≤ d) 2)
      rw [Nat.div_eq_of_lt hNd2, harmonic_zero]; simp
  rw [htail0]
  -- decompose into main term + correction
  have hdecomp : (∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2 * (harmonic (N / d ^ 2) : ℝ))
      = Real.log N * (∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2)
        + ∑ d ∈ Finset.Icc 1 M,
            (moebius d : ℝ) / (d : ℝ) ^ 2 * ((harmonic (N / d ^ 2) : ℝ) - Real.log N) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _; ring
  rw [hdecomp]
  have hrw : Real.log N * (∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2)
        + (∑ d ∈ Finset.Icc 1 M,
            (moebius d : ℝ) / (d : ℝ) ^ 2 * ((harmonic (N / d ^ 2) : ℝ) - Real.log N))
        - 6 / Real.pi ^ 2 * Real.log N
      = Real.log N * ((∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2)
        + ∑ d ∈ Finset.Icc 1 M,
            (moebius d : ℝ) / (d : ℝ) ^ 2 * ((harmonic (N / d ^ 2) : ℝ) - Real.log N) := by ring
  rw [hrw]
  refine le_trans (abs_add_le _ _) ?_
  -- main term: `|log N · (∑ μ/d² − 6/π²)| ≤ 2`
  have hpart1 : |Real.log N
      * ((∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg hlogN_nonneg]
    calc Real.log N * |(∑ d ∈ Finset.Icc 1 M, (moebius d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2|
        ≤ Real.log N * (1 / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (abs_sum_moebius_div_sq_sub M hM1) hlogN_nonneg
      _ ≤ 2 := by rw [mul_one_div, div_le_iff₀ hMRpos]; linarith [hlogN_le]
  -- correction: `|∑ (μ/d²)(H − log N)| ≤ 2 CB + CC`
  have hpart2 : |∑ d ∈ Finset.Icc 1 M,
      (moebius d : ℝ) / (d : ℝ) ^ 2 * ((harmonic (N / d ^ 2) : ℝ) - Real.log N)| ≤ 2 * CB + CC := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 M,
        |(moebius d : ℝ) / (d : ℝ) ^ 2 * ((harmonic (N / d ^ 2) : ℝ) - Real.log N)|
          ≤ 2 * (Real.log d / (d : ℝ) ^ 2) + (1 : ℝ) / (d : ℝ) ^ 2 := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd1 : 1 ≤ d := hd.1
      have hdM : d ≤ M := hd.2
      have hdpos : 0 < d := hd1
      have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hd2pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
      have hlogd_nonneg : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
      have hd2leN : d ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hdM 2) hMsqleN
      set Q := N / d ^ 2 with hQ
      have hQ1 : 1 ≤ Q := (Nat.one_le_div_iff (by positivity)).mpr hd2leN
      have hQRpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
      -- harmonic pinch `|H_Q − log N| ≤ 2 log d + 1`
      have hlogdiv : Real.log ((N : ℝ) / (d : ℝ) ^ 2) = Real.log N - 2 * Real.log d := by
        rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hd2pos), Real.log_pow]; push_cast; ring
      have hNd2pos : (0 : ℝ) < (N : ℝ) / (d : ℝ) ^ 2 := div_pos hNpos hd2pos
      have hQle : (Q : ℝ) ≤ (N : ℝ) / (d : ℝ) ^ 2 := by
        rw [le_div_iff₀ hd2pos]
        have hmul : Q * d ^ 2 ≤ N := Nat.div_mul_le_self N (d ^ 2)
        calc (Q : ℝ) * (d : ℝ) ^ 2 = ((Q * d ^ 2 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (N : ℝ) := by exact_mod_cast hmul
      have hltQ1 : (N : ℝ) / (d : ℝ) ^ 2 < (Q : ℝ) + 1 := by
        rw [div_lt_iff₀ hd2pos]
        have hltmul : N < (Q + 1) * d ^ 2 := by
          have hN_eq : d ^ 2 * Q + N % d ^ 2 = N := Nat.div_add_mod N (d ^ 2)
          have hmodlt : N % d ^ 2 < d ^ 2 := Nat.mod_lt N (pow_pos hdpos 2)
          have hstep : N < d ^ 2 * Q + d ^ 2 := by omega
          calc N < d ^ 2 * Q + d ^ 2 := hstep
            _ = (Q + 1) * d ^ 2 := by ring
        calc (N : ℝ) < (((Q + 1) * d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hltmul
          _ = ((Q : ℝ) + 1) * (d : ℝ) ^ 2 := by push_cast; ring
      have hupper : (harmonic Q : ℝ) ≤ 1 + (Real.log N - 2 * Real.log d) := by
        have h1 := harmonic_le_one_add_log Q
        have h2 : Real.log (Q : ℝ) ≤ Real.log ((N : ℝ) / (d : ℝ) ^ 2) :=
          Real.log_le_log hQRpos hQle
        rw [hlogdiv] at h2; linarith
      have hlower : Real.log N - 2 * Real.log d ≤ (harmonic Q : ℝ) := by
        have h1 := log_add_one_le_harmonic Q
        have h2 : Real.log ((N : ℝ) / (d : ℝ) ^ 2) ≤ Real.log ((Q : ℝ) + 1) :=
          Real.log_le_log hNd2pos (le_of_lt hltQ1)
        rw [hlogdiv] at h2
        have h3 : Real.log ((Q + 1 : ℕ) : ℝ) = Real.log ((Q : ℝ) + 1) := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [h3] at h1; linarith
      have hharm_bound : |(harmonic Q : ℝ) - Real.log N| ≤ 2 * Real.log d + 1 := by
        rw [abs_le]; constructor
        · linarith [hlower, hlogd_nonneg]
        · linarith [hupper, hlogd_nonneg]
      have habsμ : |(moebius d : ℝ) / (d : ℝ) ^ 2| ≤ (1 : ℝ) / (d : ℝ) ^ 2 := by
        rw [abs_div, abs_of_nonneg (le_of_lt hd2pos)]
        gcongr
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      rw [abs_mul]
      calc |(moebius d : ℝ) / (d : ℝ) ^ 2| * |(harmonic Q : ℝ) - Real.log N|
          ≤ (1 / (d : ℝ) ^ 2) * (2 * Real.log d + 1) :=
            mul_le_mul habsμ hharm_bound (abs_nonneg _) (by positivity)
        _ = 2 * (Real.log d / (d : ℝ) ^ 2) + (1 : ℝ) / (d : ℝ) ^ 2 := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hB_le : ∑ d ∈ Finset.Icc 1 M, Real.log d / (d : ℝ) ^ 2 ≤ CB := by
      rw [hCB]
      refine hsumB.sum_le_tsum _ (fun i _ => ?_)
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (by positivity)
    have hC_le : ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ) ^ 2 ≤ CC := by
      rw [hCC]
      exact hsumC.sum_le_tsum _ (fun i _ => by positivity)
    linarith [hB_le, hC_le]
  linarith [hpart1, hpart2]

end SquarefreeRecip
