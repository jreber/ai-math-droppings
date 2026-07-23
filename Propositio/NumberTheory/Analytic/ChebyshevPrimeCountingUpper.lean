import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Propositio.NumberTheory.Analytic.ChebyshevThetaLower
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingLower

/-!
# Chebyshev's upper bound for the prime-counting function `π`

mathlib's `Mathlib/NumberTheory/PrimeCounting.lean` provides only a crude *upper* bound
(`Nat.primeCounting'_add_le`) for `π`.  This file supplies Chebyshev's sharp upper bound
`π(⌊x⌋) ≤ C·x / log x` for large `x`, which together with the matching lower bound
(`ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge`) completes Chebyshev's theorem
`π(x) ≍ x / log x`.

## The √x-splitting argument

The key idea (Chebyshev's): every prime `p` with `√x < p ≤ x` contributes
`log p > log √x = (log x)/2` to `θ(x) = ∑_{p ≤ x prime} log p`.  Restricting `θ(x)` to
those primes gives

`θ(x) ≥ (π(⌊x⌋) − π(⌊√x⌋)) · (log x)/2`,

so with mathlib's upper bound `θ(x) ≤ log 4 · x` we get
`π(⌊x⌋) − π(⌊√x⌋) ≤ 2·log 4·x / log x`.  The small part is controlled by
`π(⌊√x⌋) ≤ ⌊√x⌋ ≤ √x ≤ x / log x` (valid once `log x ≤ √x`, i.e. `x ≥ 256`), giving

`π(⌊x⌋) ≤ (2·log 4 + 1)·x / log x`.

## Main result

* `ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le` :
  `∃ C > 0, ∃ x₀, ∀ x ≥ x₀, π(⌊x⌋) ≤ C·x / log x`, with `C = 2·log 4 + 1` and `x₀ = 256`.
-/

open Chebyshev Finset Real

namespace ChebyshevPrimeCountingUpper

/-- **The sub-sum lower bound.**  Restricting `θ(x)` to the primes in `(⌊√x⌋, ⌊x⌋]`, each
contributes at least `log √x = (log x)/2`, so
`θ(x) ≥ #{primes in (⌊√x⌋, ⌊x⌋]} · (log x)/2`. -/
theorem theta_ge_sub {x : ℝ} (hx : 0 < x) :
    (((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) * (Real.log x / 2)
      ≤ Chebyshev.theta x := by
  rw [Chebyshev.theta]
  -- The sub-Finset of primes in `(⌊√x⌋, ⌊x⌋]` sits inside the full prime range `(0, ⌊x⌋]`.
  have hGsub : (Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime
      ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
  -- On the sub-Finset every term `log p ≥ (log x)/2`, so the constant sum is a lower bound.
  have hstep2 :
      (((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) * (Real.log x / 2)
        ≤ ∑ p ∈ (Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hsp, _hpm⟩, _hpp⟩ := hp
    -- `(log x)/2 = log √x ≤ log p` because `√x < ⌊√x⌋ + 1 ≤ p`.
    rw [← Real.log_sqrt hx.le]
    apply Real.log_le_log (Real.sqrt_pos.mpr hx)
    have h1 : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt x)
    have h2 : (⌊Real.sqrt x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hsp
    linarith
  -- Drop back up to the full `θ(x)` sum (extra terms are `log p ≥ 0`).
  refine le_trans hstep2 ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg hGsub
  intro p hp _
  rw [Finset.mem_filter] at hp
  have : 1 ≤ (p : ℝ) := by exact_mod_cast hp.2.one_le
  exact Real.log_nonneg this

/-- **The `(√x, x]` prime count.**  Splitting `(0, ⌊x⌋]` at `⌊√x⌋` gives
`π(⌊x⌋) = π(⌊√x⌋) + #{primes in (⌊√x⌋, ⌊x⌋]}`. -/
theorem count_split {x : ℝ} (hsm : ⌊Real.sqrt x⌋₊ ≤ ⌊x⌋₊) :
    Nat.primeCounting ⌊x⌋₊
      = Nat.primeCounting ⌊Real.sqrt x⌋₊
        + ((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  rw [← ChebyshevPrimeCountingLower.card_primes_Ioc ⌊x⌋₊,
      ← ChebyshevPrimeCountingLower.card_primes_Ioc ⌊Real.sqrt x⌋₊,
      ← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hsm,
      Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le (le_refl _)))]

/-- **Chebyshev's upper bound for the prime-counting function.**  There is an explicit positive
constant `C = 2·log 4 + 1` and a threshold `x₀ = 256` with `π(⌊x⌋) ≤ C·x / log x` for all
`x ≥ x₀`. -/
theorem chebyshev_primeCounting_le :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / Real.log x := by
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨2 * Real.log 4 + 1, by linarith, 256, ?_⟩
  intro x hx256
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  -- √x facts
  have hsqrtx_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx_le : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le hsqrtx_nonneg
  -- `√x ≤ x` (since `x ≥ 1`), hence `⌊√x⌋ ≤ ⌊x⌋`.
  have hsqrt_le_x : Real.sqrt x ≤ x := (Real.sqrt_le_left (le_of_lt hxpos)).mpr (by nlinarith)
  have hsm : ⌊Real.sqrt x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hsqrt_le_x
  -- `log x ≤ √x` for `x ≥ 256`, via `t := x^(1/4) ≥ 4` and `log x ≤ 4 t ≤ t² = √x`.
  set t := Real.sqrt (Real.sqrt x) with ht_def
  have htt : t * t = Real.sqrt x := Real.mul_self_sqrt hsqrtx_nonneg
  have h256 : Real.sqrt 256 = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrtx_ge : (16 : ℝ) ≤ Real.sqrt x := by rw [← h256]; exact Real.sqrt_le_sqrt hx256
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have ht_ge : (4 : ℝ) ≤ t := by rw [ht_def, ← h16]; exact Real.sqrt_le_sqrt hsqrtx_ge
  have hlog_half : Real.log (Real.sqrt x) ≤ 2 * t :=
    ChebyshevThetaLower.log_le_two_sqrt (Real.sqrt_pos.mpr hxpos)
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hxpos.le
  have hlogx_le_4t : Real.log x ≤ 4 * t := by rw [hlogsqrt] at hlog_half; linarith
  have hlogx_le_sqrt : Real.log x ≤ Real.sqrt x := by nlinarith [hlogx_le_4t, ht_ge, htt]
  -- `√x · log x ≤ √x · √x = x`, hence `√x ≤ x / log x`.
  have hsqrtlog : Real.sqrt x * Real.log x ≤ x := by
    calc Real.sqrt x * Real.log x
        ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hlogx_le_sqrt hsqrtx_nonneg
      _ = x := Real.mul_self_sqrt hxpos.le
  -- `π(⌊√x⌋) ≤ ⌊√x⌋ ≤ √x`.
  have hpis_nat : Nat.primeCounting ⌊Real.sqrt x⌋₊ ≤ ⌊Real.sqrt x⌋₊ := by
    rw [← ChebyshevPrimeCountingLower.card_primes_Ioc ⌊Real.sqrt x⌋₊]
    calc ((Finset.Ioc 0 ⌊Real.sqrt x⌋₊).filter Nat.Prime).card
        ≤ (Finset.Ioc 0 ⌊Real.sqrt x⌋₊).card := Finset.card_filter_le _ _
      _ = ⌊Real.sqrt x⌋₊ := by rw [Nat.card_Ioc, Nat.sub_zero]
  have hpis_real : (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x :=
    le_trans (by exact_mod_cast hpis_nat) hsx_le
  -- combine the sub-sum bound with mathlib's `θ(x) ≤ log 4 · x`.
  have hsubsum := theta_ge_sub hxpos
  have hupper := Chebyshev.theta_le_log4_mul_x hxpos.le
  have hsub2 :
      (((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) * (Real.log x / 2)
        ≤ Real.log 4 * x := le_trans hsubsum hupper
  have hCcard :
      (((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) * Real.log x
        ≤ 2 * Real.log 4 * x := by nlinarith [hsub2]
  -- `π(⌊x⌋) = π(⌊√x⌋) + card`.
  have hcount := count_split hsm
  have hcount_real :
      (Nat.primeCounting ⌊x⌋₊ : ℝ)
        = (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ)
          + (((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast hcount
  -- assemble: multiply the goal through by `log x > 0`.
  rw [le_div_iff₀ hlogpos]
  -- `π(⌊x⌋)·log x = π(⌊√x⌋)·log x + card·log x ≤ √x·log x + 2 log4 x ≤ x + 2 log4 x`.
  have hpis_log : (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ) * Real.log x
      ≤ Real.sqrt x * Real.log x :=
    mul_le_mul_of_nonneg_right hpis_real hlogpos.le
  rw [hcount_real]
  nlinarith [hpis_log, hsqrtlog, hCcard, hlogpos]

end ChebyshevPrimeCountingUpper
