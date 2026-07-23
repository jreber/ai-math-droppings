import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Propositio.NumberTheory.Analytic.OmegaSummatory

/-!
# Average order of `Ω(n)`: `Σ_{n ≤ N} Ω(n) = N·log log N + O(N)`

`Ω(n)` (mathlib `(Nat.primeFactorsList n).length`, i.e. `ArithmeticFunction.cardFactors`)
counts the prime factors of `n` **with multiplicity**.  This file fills a mathlib gap by
proving its summatory function has the classical asymptotic with leading term `N·log log N`
and a two-sided `O(N)` error.

The result is obtained from the corresponding statement for `ω(n) = n.primeFactors.card`
(`OmegaSummatory.omega_summatory_asymptotic`) plus a bounded prime-power correction:
`Σ_{n ≤ N} (Ω(n) − ω(n)) ≤ N`.

## Proof outline

1. **Per-`n` decomposition.**  For `1 ≤ n ≤ N`,
   `Ω(n) = ω(n) + Σ_{p ≤ N prime} Σ_{2 ≤ k ≤ N} [p^k ∣ n]`,
   because `Ω(n) − ω(n) = Σ_{p ∣ n} (v_p(n) − 1)` and `v_p(n) − 1 = #{k ≥ 2 : p^k ∣ n}`.
2. **Order swap.**  Summing over `n` and swapping the order of summation,
   `Σ_{n ≤ N} (Ω(n) − ω(n)) = Σ_{p ≤ N prime} Σ_{2 ≤ k ≤ N} ⌊N/p^k⌋`.
3. **Tail bound.**  `⌊N/p^k⌋ ≤ N/p^k`, a geometric sum in `k` gives `≤ N/(p(p−1))`,
   and a telescoping comparison `Σ_p 1/(p(p−1)) ≤ Σ_{m≥2} (1/(m−1) − 1/m) ≤ 1` yields
   `Σ_{n ≤ N}(Ω(n) − ω(n)) ≤ N`.
4. **Triangle inequality** with `omega_summatory_asymptotic` finishes.
-/

open Real Finset

namespace BigOmegaSummatory

/-- **Per-prime power count.**  For a prime `p` and `1 ≤ n ≤ N`, the number of exponents
`k ∈ [2, N]` with `p^k ∣ n` equals `v_p(n) − 1`.  (Both sides are `0` when `p ∤ n`.) -/
theorem count_pow_dvd (N : ℕ) {n p : ℕ} (hp : p.Prime) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ((Finset.Icc 2 N).filter (fun k => p ^ k ∣ n)).card = n.factorization p - 1 := by
  have hn0 : n ≠ 0 := by omega
  have hlt : n.factorization p < n := Nat.factorization_lt p hn0
  have hset : (Finset.Icc 2 N).filter (fun k => p ^ k ∣ n)
      = Finset.Icc 2 (n.factorization p) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, hp.pow_dvd_iff_le_factorization hn0]
    constructor
    · rintro ⟨⟨h2, _⟩, hle⟩; exact ⟨h2, hle⟩
    · rintro ⟨h2, hle⟩; exact ⟨⟨h2, by omega⟩, hle⟩
  rw [hset, Nat.card_Icc]
  omega

/-- **Per-`n` decomposition** of `Ω(n)` into `ω(n)` plus the prime-power correction. -/
theorem length_eq (N : ℕ) {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (Nat.primeFactorsList n).length
      = n.primeFactors.card
        + ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ∑ k ∈ Finset.Icc 2 N, (if p ^ k ∣ n then 1 else 0) := by
  have hn0 : n ≠ 0 := by omega
  have hlen : (Nat.primeFactorsList n).length = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [← ArithmeticFunction.cardFactors_apply,
        ArithmeticFunction.cardFactors_eq_sum_factorization]
    simp [Finsupp.sum]
  have key : ∀ p ∈ n.primeFactors,
      n.factorization p = 1 + ∑ k ∈ Finset.Icc 2 N, (if p ^ k ∣ n then 1 else 0) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    have hpp := hp.1
    have hpd := hp.2.1
    have hpos : 1 ≤ n.factorization p := hpp.factorization_pos_of_dvd hn0 hpd
    rw [← Finset.card_filter, count_pow_dvd N hpp hn1 hnN]
    omega
  rw [hlen, Finset.sum_congr rfl key, Finset.sum_add_distrib,
      Finset.card_eq_sum_ones n.primeFactors]
  congr 1
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.1.one_lt.le, le_trans (Nat.le_of_dvd (by omega) hp.2.1) hnN⟩, hp.1⟩
  · intro p hpSset hpPF
    rw [Finset.mem_filter] at hpSset
    have hpp : p.Prime := hpSset.2
    have hpndvd : ¬ p ∣ n := by
      intro hdvd
      apply hpPF
      rw [Nat.mem_primeFactors]; exact ⟨hpp, hdvd, hn0⟩
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    intro hcontra
    apply hpndvd
    rw [Finset.mem_Icc] at hk
    exact dvd_trans (dvd_pow_self p (by omega)) hcontra

/-- A finite geometric tail bound: `Σ_{2 ≤ k ≤ N} r^k ≤ r²/(1−r)` for `0 ≤ r < 1`. -/
theorem geom_Icc_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, r ^ k ≤ r ^ 2 / (1 - r) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hempty : Finset.Icc 2 N = ∅ := by rw [Finset.Icc_eq_empty]; omega
    rw [hempty, Finset.sum_empty]
    positivity
  · have hIco : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIco, Finset.sum_Ico_eq_sum_range]
    have hpow : ∀ i, r ^ (2 + i) = r ^ 2 * r ^ i := fun i => by rw [pow_add]
    rw [Finset.sum_congr rfl (fun i _ => hpow i), ← Finset.mul_sum]
    have hgeom : ∑ i ∈ Finset.range (N + 1 - 2), r ^ i ≤ 1 / (1 - r) := by
      rw [le_div_iff₀ h1r]
      have hmul := geom_sum_mul r (N + 1 - 2)
      have hm : (∑ i ∈ Finset.range (N + 1 - 2), r ^ i) * (1 - r) = 1 - r ^ (N + 1 - 2) := by
        linear_combination -hmul
      rw [hm]
      have hp0 : 0 ≤ r ^ (N + 1 - 2) := pow_nonneg hr0 _
      linarith
    calc r ^ 2 * ∑ i ∈ Finset.range (N + 1 - 2), r ^ i
        ≤ r ^ 2 * (1 / (1 - r)) := by
          apply mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = r ^ 2 / (1 - r) := by rw [mul_one_div]

/-- **Per-prime correction bound.**  For `2 ≤ p`, `Σ_{2 ≤ k ≤ N} ⌊N/p^k⌋ ≤ N·(1/(p−1) − 1/p)`. -/
theorem per_prime_bound {N p : ℕ} (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 2 N, ((N / p ^ k : ℕ) : ℝ)
      ≤ (N : ℝ) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hrpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := le_of_lt hrpos
  have hr1 : (p : ℝ)⁻¹ < 1 := by
    nlinarith [inv_mul_cancel₀ (ne_of_gt hp0), hp1, hrpos]
  have hterm : ∀ k ∈ Finset.Icc 2 N,
      ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) * ((p : ℝ)⁻¹) ^ k := by
    intro k _
    have h := Nat.cast_div_le (m := N) (n := p ^ k) (α := ℝ)
    rw [Nat.cast_pow] at h
    calc ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ k := h
      _ = (N : ℝ) * ((p : ℝ) ^ k)⁻¹ := by rw [div_eq_mul_inv]
      _ = (N : ℝ) * ((p : ℝ)⁻¹) ^ k := by rw [inv_pow]
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hp1ne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp1)
  have hfeq : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) = 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
    rw [eq_sub_iff_add_eq]
    field_simp
    ring
  calc ∑ k ∈ Finset.Icc 2 N, ((N / p ^ k : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 2 N, (N : ℝ) * ((p : ℝ)⁻¹) ^ k := Finset.sum_le_sum hterm
    _ = (N : ℝ) * ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹)) := by
        apply mul_le_mul_of_nonneg_left (geom_Icc_bound hr0 hr1 N) (Nat.cast_nonneg N)
    _ = (N : ℝ) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by rw [hfeq]

/-- **Average order of `Ω`.**  There is a constant `C` and threshold `N₀` such that for all
`N ≥ N₀`, `|Σ_{n=1}^{N} Ω(n) − N·log log N| ≤ C·N`, where `Ω(n) = (n.primeFactorsList).length`
is the number of prime factors of `n` counted with multiplicity.  Leading term exactly
`N·log log N`, two-sided error `O(N)`. -/
theorem bigOmega_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ((Nat.primeFactorsList n).length : ℝ))
          - N * Real.log (Real.log N)| ≤ C * N := by
  obtain ⟨Cω, Nω, hω⟩ := OmegaSummatory.omega_summatory_asymptotic
  refine ⟨1 + Cω, max Nω 1, ?_⟩
  intro N hN
  have hNω : Nω ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  set Sset := (Finset.Icc 1 N).filter Nat.Prime with hSset
  -- ℕ-level identity: Σ Ω = Σ ω + Σ_p Σ_k ⌊N/p^k⌋.
  have hbig : ∑ n ∈ Finset.Icc 1 N, (Nat.primeFactorsList n).length
      = (∑ n ∈ Finset.Icc 1 N, n.primeFactors.card)
        + ∑ p ∈ Sset, ∑ k ∈ Finset.Icc 2 N, (N / p ^ k) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, (Nat.primeFactorsList n).length
        = ∑ n ∈ Finset.Icc 1 N,
            (n.primeFactors.card
              + ∑ p ∈ Sset, ∑ k ∈ Finset.Icc 2 N, (if p ^ k ∣ n then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [hSset]
      exact length_eq N hn.1 hn.2
    rw [h1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.card_filter]
    have hIoc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hIoc]
    exact Nat.Ioc_filter_dvd_card_eq_div N (p ^ k)
  -- Real correction term.
  set R : ℝ := ∑ p ∈ Sset, ∑ k ∈ Finset.Icc 2 N, ((N / p ^ k : ℕ) : ℝ) with hR
  have hbigR : (∑ n ∈ Finset.Icc 1 N, ((Nat.primeFactorsList n).length : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ)) + R := by
    have hc := congrArg (fun x : ℕ => (x : ℝ)) hbig
    push_cast at hc
    rw [← hR] at hc
    exact hc
  -- Correction bound: R ≤ N.
  have hRle : R ≤ (N : ℝ) := by
    rw [hR]
    have step1 : ∑ p ∈ Sset, ∑ k ∈ Finset.Icc 2 N, ((N / p ^ k : ℕ) : ℝ)
        ≤ ∑ p ∈ Sset, (N : ℝ) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : 2 ≤ p := by
        rw [hSset, Finset.mem_filter] at hp
        exact hp.2.two_le
      exact per_prime_bound hp2
    refine le_trans step1 ?_
    rw [← Finset.mul_sum]
    have hsum_le_one : ∑ p ∈ Sset, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) ≤ 1 := by
      have hsub : Sset ⊆ Finset.Icc 2 N := by
        intro p hp
        rw [hSset, Finset.mem_filter, Finset.mem_Icc] at hp
        rw [Finset.mem_Icc]
        exact ⟨hp.2.two_le, hp.1.2⟩
      have hnn : ∀ m ∈ Finset.Icc 2 N, m ∉ Sset →
          0 ≤ (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) := by
        intro m hm _
        rw [Finset.mem_Icc] at hm
        have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
        have hpos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
        have hle : (1 : ℝ) / (m : ℝ) ≤ 1 / ((m : ℝ) - 1) :=
          one_div_le_one_div_of_le hpos (by linarith)
        linarith
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
      have hIco : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIco, Finset.sum_Ico_eq_sum_range]
      have heq : ∀ i ∈ Finset.range (N + 1 - 2),
          (1 : ℝ) / (((2 + i : ℕ) : ℝ) - 1) - 1 / ((2 + i : ℕ) : ℝ)
            = (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) i
              - (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) (i + 1) := by
        intro i _
        show (1 : ℝ) / (((2 + i : ℕ) : ℝ) - 1) - 1 / ((2 + i : ℕ) : ℝ)
            = (1 : ℝ) / ((i : ℝ) + 1) - 1 / (((i + 1 : ℕ) : ℝ) + 1)
        push_cast
        ring
      rw [Finset.sum_congr rfl heq,
          Finset.sum_range_sub' (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) (N + 1 - 2)]
      show (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) - (1 : ℝ) / (((N + 1 - 2 : ℕ) : ℝ) + 1) ≤ 1
      have hnn2 : 0 ≤ (1 : ℝ) / (((N + 1 - 2 : ℕ) : ℝ) + 1) := by positivity
      have h0 : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
      rw [h0]; linarith
    calc (N : ℝ) * ∑ p ∈ Sset, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))
        ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum_le_one (Nat.cast_nonneg N)
      _ = (N : ℝ) := mul_one _
  have hRnn : 0 ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun k _ => by positivity))
  have hRabs : |R| ≤ (N : ℝ) := by rw [abs_of_nonneg hRnn]; exact hRle
  have hωN : |(∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
      - N * Real.log (Real.log N)| ≤ Cω * N := hω N hNω
  calc |(∑ n ∈ Finset.Icc 1 N, ((Nat.primeFactorsList n).length : ℝ))
          - N * Real.log (Real.log N)|
      = |R + ((∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
              - N * Real.log (Real.log N))| := by
        rw [hbigR]; congr 1; ring
    _ ≤ |R| + |(∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
          - N * Real.log (Real.log N)| := abs_add_le _ _
    _ ≤ (N : ℝ) + Cω * N := by linarith [hRabs, hωN]
    _ = (1 + Cω) * N := by ring

end BigOmegaSummatory
