import Propositio.NumberTheory.Collatz.Chebyshev30ThetaTight
import Propositio.NumberTheory.Collatz.Chebyshev30Aentropy
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingLower
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# A tighter Chebyshev `π`-upper bound

`ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le` supplies `π(x) ≤ (2·log4+1)·x/log x
≈ 3.77·x/log x` via a `√x`-split of `θ`, which loses a factor of (essentially) `2` relative to
the true asymptotic constant `1`: primes in `(√x, x]` only certify `log p > (log x)/2`.

This file removes that loss by splitting at `y = x / (log x)²` instead of `√x`.  Since
`log y = log x - 2·log(log x) = (1 - o(1))·log x` and `y = o(x / log x)`, the same argument gives
a constant arbitrarily close to the `θ`-upper slope itself, rather than twice it.  Combined with
this project's *tight* `θ`-upper bound `θ(x) ≤ 1.15·x + θ(57600)`
(`CollatzChebyshev30.theta_tight`, slope `23/20`, `CollatzChebyshev30.theta_tight_slope_lt`),
this yields `π(x) ≤ 1.22·x/log x` for large `x` — tight enough to beat `2·c_lo` for the `θ`-lower
constant `c_lo = 0.65` from `ChebyshevThetaLowerTight.theta_ge_065`, closing the K = 2 dyadic
Bertrand gap recorded in `conj-2026-06-28-prime-dyadic-interval-count`.

## Main result

* `ChebyshevPrimeCountingUpperTight.chebyshev_primeCounting_le_tight` :
  `∃ x₀, ∀ x ≥ x₀, π(⌊x⌋) ≤ (61/50)·x / log x`.
-/

open Chebyshev Finset Real

namespace ChebyshevPrimeCountingUpperTight

/-- **The sub-sum lower bound at a general split point `y`.**  Restricting `θ(x)` to the primes
in `(⌊y⌋, ⌊x⌋]`, each contributes at least `log y`. -/
theorem theta_ge_sub_y {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (((Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) * Real.log y
      ≤ Chebyshev.theta x := by
  rw [Chebyshev.theta]
  have hGsub : (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime
      ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
  have hstep2 :
      (((Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) * Real.log y
        ≤ ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hsp, _hpm⟩, _hpp⟩ := hp
    apply Real.log_le_log hy
    have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : (⌊y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hsp
    linarith
  refine le_trans hstep2 ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg hGsub
  intro p hp _
  rw [Finset.mem_filter] at hp
  have : 1 ≤ (p : ℝ) := by exact_mod_cast hp.2.one_le
  exact Real.log_nonneg this

/-- **The `(y, x]` prime count.**  Splitting `(0, ⌊x⌋]` at `⌊y⌋`. -/
theorem count_split_y {x y : ℝ} (hsm : ⌊y⌋₊ ≤ ⌊x⌋₊) :
    Nat.primeCounting ⌊x⌋₊
      = Nat.primeCounting ⌊y⌋₊
        + ((Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  rw [← ChebyshevPrimeCountingLower.card_primes_Ioc ⌊x⌋₊,
      ← ChebyshevPrimeCountingLower.card_primes_Ioc ⌊y⌋₊,
      ← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hsm,
      Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le (le_refl _)))]

/-- `θ(x) ≤ (23/20)·x + θ(57600)` for `x ≥ 0`, from the project's tight Chebyshev-30 bound. -/
theorem theta_le_115 (x : ℝ) (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ (23 / 20 : ℝ) * x + Chebyshev.theta 57600 := by
  have h := CollatzChebyshev30.theta_tight x hx
  have hs := CollatzChebyshev30.theta_tight_slope_lt
  have hc : (0 : ℝ) ≤ 23 / 20 - (6 * (CollatzChebyshev30.Aentropy + 1 / 30) / 5) := by linarith
  have hle : (6 * (CollatzChebyshev30.Aentropy + 1 / 30) / 5) * x ≤ (23 / 20 : ℝ) * x := by
    nlinarith [mul_nonneg hc hx]
  linarith [h, hle]

/-- **Tight Chebyshev upper bound for `π`.**  There is a threshold `x₀` with
`π(⌊x⌋) ≤ (61/50)·x/log x` for all `x ≥ x₀`. -/
theorem chebyshev_primeCounting_le_tight :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (61 / 50 : ℝ) * x / Real.log x := by
  set K0 : ℝ := Chebyshev.theta 57600 with hK0_def
  have hK0nn : 0 ≤ K0 := Chebyshev.theta_nonneg _
  -- threshold: log x ≥ 40000 handles the log-log absorption; x ≥ K0-dependent term handles K0.
  refine ⟨max (Real.exp 40000) (2500 * K0 / 49 + 1), ?_⟩
  intro x hx
  have hxe : Real.exp 40000 ≤ x := le_trans (le_max_left _ _) hx
  have hxK0 : 2500 * K0 / 49 + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 40000) hxe
  have hlogx_ge : (40000 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 40000) hxe
    rwa [Real.log_exp] at this
  have hlogxpos : 0 < Real.log x := by linarith
  -- y = x / (log x)^2
  set y : ℝ := x / (Real.log x) ^ 2 with hy_def
  have hlogx2pos : 0 < (Real.log x) ^ 2 := by positivity
  have hypos : 0 < y := by rw [hy_def]; positivity
  have hyx : y ≤ x := by
    rw [hy_def, div_le_iff₀ hlogx2pos]
    have h1 : (1 : ℝ) ≤ (Real.log x) ^ 2 := by nlinarith [hlogx_ge]
    nlinarith [h1, hxpos.le]
  have hsm : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  -- log y ≥ (49/50) log x
  have hlogy : Real.log y = Real.log x - 2 * Real.log (Real.log x) := by
    rw [hy_def, Real.log_div hxpos.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have hlls : Real.log (Real.log x) ≤ 2 * Real.sqrt (Real.log x) :=
    ChebyshevThetaLower.log_le_two_sqrt hlogxpos
  have hsqrtlogx_ge : (200 : ℝ) ≤ Real.sqrt (Real.log x) := by
    have h1 : Real.sqrt (200 ^ 2) ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt (by nlinarith [hlogx_ge])
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hlogx_eq : Real.log x = Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
    (Real.mul_self_sqrt hlogxpos.le).symm
  have hmul : (200 : ℝ) * Real.sqrt (Real.log x) ≤ Real.log x := by
    have hprod : (0 : ℝ) ≤ (Real.sqrt (Real.log x) - 200) * Real.sqrt (Real.log x) :=
      mul_nonneg (by linarith [hsqrtlogx_ge]) (Real.sqrt_nonneg _)
    nlinarith [hlogx_eq, hprod]
  have hlogy_ge : (49 / 50 : ℝ) * Real.log x ≤ Real.log y := by
    rw [hlogy]
    nlinarith [hlls, hmul]
  have hlogypos : 0 < Real.log y := by nlinarith [hlogy_ge, hlogx_ge]
  -- the sub-sum bound at y, converted to a card ≤ bound
  have hsub := theta_ge_sub_y hxpos hypos
  have hup := theta_le_115 x hxpos.le
  set card : ℝ := (((Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) with hcard_def
  have hcardnn : 0 ≤ card := Nat.cast_nonneg _
  have hcard1 : card * Real.log y ≤ (23 / 20 : ℝ) * x + K0 := le_trans hsub hup
  have hcard2 : card * ((49 / 50 : ℝ) * Real.log x) ≤ card * Real.log y :=
    mul_le_mul_of_nonneg_left hlogy_ge hcardnn
  have hcard3 : card * ((49 / 50 : ℝ) * Real.log x) ≤ (23 / 20 : ℝ) * x + K0 :=
    le_trans hcard2 hcard1
  have hcard4 : card * Real.log x ≤ (115 / 98 : ℝ) * x + (50 / 49 : ℝ) * K0 := by
    nlinarith [hcard3]
  -- π(y) ≤ y
  have hpis_nat : Nat.primeCounting ⌊y⌋₊ ≤ ⌊y⌋₊ := by
    rw [← ChebyshevPrimeCountingLower.card_primes_Ioc ⌊y⌋₊]
    calc ((Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime).card
        ≤ (Finset.Ioc 0 ⌊y⌋₊).card := Finset.card_filter_le _ _
      _ = ⌊y⌋₊ := by rw [Nat.card_Ioc, Nat.sub_zero]
  have hpis_real : (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ y :=
    le_trans (by exact_mod_cast hpis_nat) (Nat.floor_le hypos.le)
  -- y * log x ≤ x / 50
  have hylogx : y * Real.log x ≤ x / 50 := by
    have heq : y * Real.log x = x / Real.log x := by
      rw [hy_def, sq]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left hxpos.le (by norm_num)
      (by linarith [hlogx_ge] : (50 : ℝ) ≤ Real.log x)
  -- K0 term: (50/49) K0 ≤ x / 50
  have hK0x : (50 / 49 : ℝ) * K0 ≤ x / 50 := by
    nlinarith [hxK0]
  -- π(x) = π(y) + card
  have hcount := count_split_y hsm
  have hcount_real :
      (Nat.primeCounting ⌊x⌋₊ : ℝ) = (Nat.primeCounting ⌊y⌋₊ : ℝ) + card := by
    rw [hcard_def]; exact_mod_cast hcount
  rw [le_div_iff₀ hlogxpos]
  -- assemble: π(x)·log x = π(y)·log x + card·log x
  have hpis_log : (Nat.primeCounting ⌊y⌋₊ : ℝ) * Real.log x ≤ y * Real.log x :=
    mul_le_mul_of_nonneg_right hpis_real hlogxpos.le
  rw [hcount_real]
  nlinarith [hpis_log, hylogx, hcard4, hK0x]

end ChebyshevPrimeCountingUpperTight
