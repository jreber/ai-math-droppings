import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Real.Sqrt
import Propositio.NumberTheory.Analytic.ChebyshevThetaLower
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingLower
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingUpper

/-!
# Growth rate of the `n`th prime: `pₙ = Θ(n log n)`

Let `pₙ := Nat.nth Nat.Prime n` be the `n`th prime (0-indexed, so `p₀ = 2`).
Inverting Chebyshev's two-sided estimate for the prime-counting function `π`
(`π(x) = Θ(x / log x)`, available in this repository as
`ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge` and
`ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le`) yields the classical
order-of-magnitude statement

`pₙ = Θ(n log n)`.

mathlib has only the weak lower bound `Nat.add_two_le_nth_prime` (`n + 2 ≤ pₙ`),
so this asymptotic is a genuine gap.

## The inversion

The bridge between `pₙ` and `π` is the Galois connection between `Nat.nth` and
`Nat.count` (`= Nat.primeCounting'`):

* `nth_prime_le_of_lt_primeCounting` : `n < π m → pₙ ≤ m`
  (so a lower bound on `π` gives an *upper* bound on `pₙ`);
* `primeCounting_nth_prime` : `π pₙ = n + 1`
  (so an upper bound on `π` gives a *lower* bound on `pₙ`).

## The two directions

* **Upper** `pₙ ≤ K·n log n` (`K = 4/c`): with `x = K·n log n` the lower Chebyshev
  bound gives `π(⌊x⌋) ≥ c·x / log x`.  The key analytic input is
  `log x ≤ 2 log n` for large `n` (since `log K + log log n ≤ log n` eventually,
  using `log L ≤ 2√L ≤ L/2` for `L = log n ≥ 16`), whence
  `π(⌊x⌋) ≥ c·x / (2 log n) = (cK/2)·n = 2n ≥ n + 1`, so `pₙ ≤ ⌊x⌋ ≤ x`.
* **Lower** `n log n ≤ C·pₙ`: from `π pₙ = n + 1` and the upper Chebyshev bound,
  `n + 1 ≤ C·pₙ / log pₙ`, hence `n log n ≤ (n+1) log pₙ ≤ C·pₙ`.

## Main results

* `NthPrimeGrowth.nth_prime_isBigO`        : `pₙ =O[atTop] n log n`.
* `NthPrimeGrowth.nth_prime_isBigO_lower`  : `n log n =O[atTop] pₙ`.
* `NthPrimeGrowth.nth_prime_isTheta`       : `pₙ =Θ[atTop] n log n`.
-/

open Asymptotics Filter Real

namespace NthPrimeGrowth

/-! ## The `nth ↔ primeCounting` inversion -/

/-- **Inversion (upper-bound direction).** If there are more than `n` primes `≤ m`
(`n < π m`), then the `n`th prime is `≤ m`.  This is the Galois connection
`Nat.lt_nth_iff_count_lt` applied to `Nat.Prime`, using
`π m = Nat.count Nat.Prime (m + 1)`. -/
theorem nth_prime_le_of_lt_primeCounting {n m : ℕ}
    (h : n < Nat.primeCounting m) : Nat.nth Nat.Prime n ≤ m := by
  have hinf := Nat.infinite_setOf_prime
  have h' : n < Nat.count Nat.Prime (m + 1) := h
  exact Nat.lt_succ_iff.mp ((Nat.lt_nth_iff_count_lt hinf).mp h')

/-- **Inversion (lower-bound direction).** `π pₙ = n + 1`: the primes `≤ pₙ` are
exactly `p₀, …, pₙ`.  This is `Nat.count_nth_succ_of_infinite`, using
`π pₙ = Nat.count Nat.Prime (pₙ + 1)`. -/
theorem primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 :=
  Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime n

/-! ## Upper bound: `pₙ = O(n log n)` -/

/-- **Upper bound.** The `n`th prime is `O(n log n)`. -/
theorem nth_prime_isBigO :
    (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log n) := by
  obtain ⟨c, hcpos, x₀, hc⟩ := ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge
  set K : ℝ := 4 / c with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hcK : c * K = 4 := by rw [hKdef]; field_simp
  rw [Asymptotics.isBigO_iff]
  refine ⟨K, ?_⟩
  have hlogtt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htop : Tendsto (fun n : ℕ => K * ((n : ℝ) * Real.log n)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hlogtt).const_mul_atTop hKpos
  filter_upwards [eventually_ge_atTop 2, hlogtt.eventually_ge_atTop (16 : ℝ),
    hlogtt.eventually_ge_atTop (2 * Real.log K),
    htop.eventually_ge_atTop x₀, htop.eventually_ge_atTop (2 : ℝ)]
    with n hn2 hL16 hLlogK hxx0 hx2
  -- abbreviations
  set L : ℝ := Real.log n with hLdef
  set xv : ℝ := K * ((n : ℝ) * L) with hxvdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hLpos : 0 < L := by linarith
  have hnLpos : 0 < (n : ℝ) * L := by positivity
  have hxvpos : 0 < xv := by rw [hxvdef]; positivity
  -- `log xv = log K + log n + log L`
  have hlogxv_eq : Real.log xv = Real.log K + (L + Real.log L) := by
    rw [hxvdef, Real.log_mul (ne_of_gt hKpos) (ne_of_gt hnLpos),
        Real.log_mul (by positivity) (ne_of_gt hLpos)]
  -- `log K ≤ L/2`
  have hlogK_le : Real.log K ≤ L / 2 := by linarith
  -- `log L ≤ 2√L ≤ L/2`  (valid since `L ≥ 16`)
  have hsqrt : Real.log L ≤ 2 * Real.sqrt L := ChebyshevThetaLower.log_le_two_sqrt hLpos
  have hsqrtL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt_ge : (4 : ℝ) ≤ Real.sqrt L := by rw [← h16]; exact Real.sqrt_le_sqrt hL16
  have hlogL_le : Real.log L ≤ L / 2 := by
    nlinarith [hsqrt, hsqrtL, mul_nonneg (sub_nonneg.2 hsqrt_ge) (Real.sqrt_nonneg L)]
  have hlogxv_le : Real.log xv ≤ 2 * L := by rw [hlogxv_eq]; linarith
  -- `0 < log xv`  (since `xv ≥ 2`)
  have hlogxv_pos : 0 < Real.log xv := Real.log_pos (by linarith)
  -- `c · xv = 4 · (n·L)`
  have hcxv : c * xv = 4 * ((n : ℝ) * L) := by rw [hxvdef, ← mul_assoc, hcK]
  -- `n + 1 ≤ c·xv / log xv`
  have hkey : (n : ℝ) + 1 ≤ c * xv / Real.log xv := by
    rw [le_div_iff₀ hlogxv_pos, hcxv]
    have hmul : ((n : ℝ) + 1) * Real.log xv ≤ ((n : ℝ) + 1) * (2 * L) :=
      mul_le_mul_of_nonneg_left hlogxv_le (by positivity)
    nlinarith [hmul, mul_nonneg (sub_nonneg.2 hn1) hLpos.le]
  -- Chebyshev lower bound at `x = xv`
  have hge : c * xv / Real.log xv ≤ (Nat.primeCounting ⌊xv⌋₊ : ℝ) := hc xv hxx0
  have hcount : (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊xv⌋₊ : ℝ) := le_trans hkey hge
  have hcount_nat : n + 1 ≤ Nat.primeCounting ⌊xv⌋₊ := by exact_mod_cast hcount
  have hlt : n < Nat.primeCounting ⌊xv⌋₊ := by omega
  have hle : Nat.nth Nat.Prime n ≤ ⌊xv⌋₊ := nth_prime_le_of_lt_primeCounting hlt
  have hfloor : (⌊xv⌋₊ : ℝ) ≤ xv := Nat.floor_le hxvpos.le
  have hple : (Nat.nth Nat.Prime n : ℝ) ≤ xv := le_trans (by exact_mod_cast hle) hfloor
  -- finish (norms)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg hnLpos.le, ← hxvdef]
  exact hple

/-! ## Lower bound: `n log n = O(pₙ)` -/

/-- **Lower bound.** `n log n` is `O(pₙ)`, i.e. `pₙ` grows at least like `n log n`. -/
theorem nth_prime_isBigO_lower :
    (fun n : ℕ => (n : ℝ) * Real.log n) =O[atTop]
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) := by
  obtain ⟨C, hCpos, x₀, hc⟩ := ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop x₀] with n hn1 hnx0
  set p := Nat.nth Nat.Prime n with hpdef
  have hp2 : n + 2 ≤ p := Nat.add_two_le_nth_prime n
  have hpn_ge : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : n ≤ p)
  have hppos : 0 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 2 ≤ p)
    linarith
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 2 ≤ p)
    linarith)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := by linarith
  have hlogn_nonneg : 0 ≤ Real.log n := Real.log_nonneg hn1R
  -- `π p = n + 1`
  have hpi : Nat.primeCounting p = n + 1 := primeCounting_nth_prime n
  -- Chebyshev upper bound at `x = p`
  have hx0p : x₀ ≤ (p : ℝ) := le_trans hnx0 hpn_ge
  have hub := hc (p : ℝ) hx0p
  rw [Nat.floor_natCast, hpi] at hub
  have hub' : (n : ℝ) + 1 ≤ C * (p : ℝ) / Real.log p := by exact_mod_cast hub
  rw [le_div_iff₀ hlogp_pos] at hub'
  -- `log n ≤ log p`
  have hloglog : Real.log n ≤ Real.log p := Real.log_le_log hnpos hpn_ge
  -- `n log n ≤ (n+1) log p`
  have hstep : (n : ℝ) * Real.log n ≤ ((n : ℝ) + 1) * Real.log p := by
    nlinarith [mul_le_mul_of_nonneg_left hloglog hnpos.le, hlogp_pos]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogn_nonneg),
      abs_of_nonneg (Nat.cast_nonneg _)]
  linarith [hstep, hub']

/-! ## The two-sided result -/

/-- **The growth rate of the `n`th prime.** `pₙ =Θ(n log n)`. -/
theorem nth_prime_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ))
      (fun n : ℕ => (n : ℝ) * Real.log n) :=
  ⟨nth_prime_isBigO, nth_prime_isBigO_lower⟩

end NthPrimeGrowth
