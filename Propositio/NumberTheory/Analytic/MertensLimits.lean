import Propositio.NumberTheory.Analytic.MertensReciprocalLower
import Propositio.NumberTheory.Analytic.MertensProductUpper

/-!
# Mertens limits: Euler's divergence and the prime-product collapse

Two asymptotic corollaries of the explicit Mertens bounds proven elsewhere in this tree:

* `sum_reciprocal_primes_tendsto_atTop` — **Euler's theorem on the divergence of the
  reciprocals of the primes**: `Σ_{p ≤ n} 1/p → ∞`.  It follows from the lower bound
  `MertensReciprocalLower.sum_reciprocal_primes_ge` (the partial sums are eventually
  `≥ c·log(log n) − C`) together with `log(log n) → ∞`.

* `prod_one_sub_inv_tendsto_zero` — the Euler product `∏_{p ≤ n}(1 − 1/p) → 0`.  Each
  partial product is nonnegative and, by `MertensProductUpper.prod_one_sub_inv_le`,
  eventually `≤ 1/log n → 0`; the squeeze theorem closes it.
-/

open Filter

namespace MertensLimits

/-- **Euler's theorem (divergence of the reciprocals of the primes).**
The partial sums `Σ_{p ≤ n, p prime} 1/p` tend to `+∞`. -/
theorem sum_reciprocal_primes_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
      Filter.atTop Filter.atTop := by
  obtain ⟨c, hc, C, N, hge⟩ := MertensReciprocalLower.sum_reciprocal_primes_ge
  -- `log (log ↑n) → ∞`.
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  -- `c · log(log ↑n) − C → ∞`.
  have hg : Tendsto (fun n : ℕ => c * Real.log (Real.log n) - C) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => c * Real.log (Real.log n)) atTop atTop :=
      hloglog.const_mul_atTop hc
    have h2 : Tendsto (fun n : ℕ => c * Real.log (Real.log n) + (-C)) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-C) h1
    simpa [sub_eq_add_neg] using h2
  -- The partial sum eventually dominates `g`, so it also tends to `∞`.
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop N] with n hn using hge n hn

/-- The Euler product `∏_{p ≤ n, p prime}(1 − 1/p)` tends to `0`. -/
theorem prod_one_sub_inv_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - (1 : ℝ) / p))
      Filter.atTop (nhds 0) := by
  obtain ⟨N, hle⟩ := MertensProductUpper.prod_one_sub_inv_le
  -- `1 / log ↑n → 0`.
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ => 1 / Real.log n) atTop (nhds 0) := by
    have := hlog.inv_tendsto_atTop
    simpa [one_div, Pi.inv_def] using this
  -- Each partial product is nonnegative.
  have hnonneg : ∀ n : ℕ,
      (0 : ℝ) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
    intro n
    apply Finset.prod_nonneg
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp : p.Prime := hp.2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one hppos]; linarith
    linarith
  -- Squeeze between `0` and `1/log n`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall hnonneg) ?_
  filter_upwards [eventually_ge_atTop N] with n hn using hle n hn

end MertensLimits

#print axioms MertensLimits.sum_reciprocal_primes_tendsto_atTop
#print axioms MertensLimits.prod_one_sub_inv_tendsto_zero
