/-
# The Möbius/zeta keystone value `∑' n, μ(n)/n² = 6/π²`

This is the real-tsum form of `1/ζ(2) = 6/π²`, a genuine mathlib gap: mathlib has the
complex L-series identity (`LSeries_convolution'`, `riemannZeta` values) but not this real
`tsum` equality.

The proof is the elementary Dirichlet/Cauchy product, carried out directly over `ℝ`:

* both `a d = μ(d)/d²` and `b e = 1/e²` are absolutely summable (comparison with the
  convergent `p`-series `∑ 1/n²`, using `|μ(d)| ≤ 1`);
* `(∑ a)·(∑ b)` is reindexed by the product map `(d,e) ↦ d·e` (`HasSum.mul` followed by
  `HasSum.tsum_fiberwise`), exactly the device used by mathlib's
  `LSeriesHasSum.convolution`;
* over each fibre `d·e = n ≠ 0` the contribution collapses to
  `(1/n²)·∑_{d ∣ n} μ(d) = (1/n²)·[n = 1]` via the Möbius convolution
  `moebius * ζ = 1` (`moebius_mul_coe_zeta`, `coe_mul_zeta_apply`, `one_apply`);
* summing the indicator gives `(∑ a)·ζ(2) = 1`, and `ζ(2) = π²/6` (`hasSum_zeta_two`)
  yields `∑ a = 6/π²`.
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic

open ArithmeticFunction
open scoped Real

namespace MobiusZetaTwo

/-- **The Möbius/zeta keystone value.**  `∑' n, μ(n)/n² = 6/π²` (i.e. `1/ζ(2)`). -/
theorem tsum_moebius_div_sq :
    ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 = 6 / Real.pi ^ 2 := by
  set a : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 with ha_def
  set b : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hb_def
  -- absolute summability of `a` (comparison with the `p`-series `∑ 1/n²`)
  have hnorm_a : Summable (fun n => ‖a n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    intro n
    simp only [ha_def, Real.norm_eq_abs, abs_div]
    have hden : |(n : ℝ) ^ 2| = (n : ℝ) ^ 2 := abs_of_nonneg (by positivity)
    rw [hden]
    gcongr
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  -- absolute summability of `b`
  have hnorm_b : Summable (fun n => ‖b n‖) := by
    apply (Real.summable_one_div_nat_pow.mpr one_lt_two).congr
    intro n
    simp only [hb_def, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  have hsum_a : Summable a := hnorm_a.of_norm
  have ha : HasSum a (∑' n, a n) := hsum_a.hasSum
  have hb : HasSum b (Real.pi ^ 2 / 6) := by rw [hb_def]; exact hasSum_zeta_two
  -- Cauchy product: `(∑ a)·(∑ b) = ∑_{(d,e)} a d · b e`
  have hfg : Summable (fun x : ℕ × ℕ => a x.1 * b x.2) :=
    summable_mul_of_summable_norm hnorm_a hnorm_b
  have hmul : HasSum (fun x : ℕ × ℕ => a x.1 * b x.2) ((∑' n, a n) * (Real.pi ^ 2 / 6)) :=
    ha.mul hb hfg
  -- reindex the product by the multiplication map `(d,e) ↦ d·e`
  have hfib := hmul.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  -- the fibre over `n` collapses to the Möbius-convolution indicator `[n = 1]`
  have hfun : (fun n : ℕ =>
      ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}), a (p : ℕ × ℕ).1 * b (p : ℕ × ℕ).2)
      = fun n : ℕ => if n = 1 then (1 : ℝ) else 0 := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · -- `n = 0`: every term in the fibre vanishes (`a 0 = 0`, `b 0 = 0`)
      have hz : ∀ p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}),
          a (p : ℕ × ℕ).1 * b (p : ℕ × ℕ).2 = 0 := by
        rintro ⟨⟨d, e⟩, hp⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero] at hp
        rcases hp with rfl | rfl
        · simp [ha_def]
        · simp [hb_def]
      rw [tsum_congr hz, tsum_zero]
      simp
    · -- `n ≠ 0`: the fibre is `n.divisorsAntidiagonal`
      rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
        Finset.tsum_subtype' n.divisorsAntidiagonal fun p => a p.1 * b p.2]
      -- collapse each summand to `μ(p.1)/n²`
      have hterm : ∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2
          = (∑ p ∈ n.divisorsAntidiagonal, (moebius p.1 : ℝ)) / (n : ℝ) ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Nat.mem_divisorsAntidiagonal] at hp
        simp only [ha_def, hb_def]
        rw [← hp.1]
        push_cast
        ring
      rw [hterm]
      -- `∑_{(d,e): de=n} μ(d) = ∑_{d ∣ n} μ(d) = [n = 1]`
      have hreindex : (∑ p ∈ n.divisorsAntidiagonal, (moebius p.1 : ℝ))
          = ∑ d ∈ n.divisors, (moebius d : ℝ) :=
        Nat.sum_divisorsAntidiagonal (fun d _ => (moebius d : ℝ))
      have hconv : (∑ d ∈ n.divisors, moebius d) = if n = 1 then (1 : ℤ) else 0 := by
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
      rw [hreindex]
      have hcast : (∑ d ∈ n.divisors, (moebius d : ℝ)) = ((if n = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := by
        rw [← hconv]; push_cast; ring
      rw [hcast]
      split_ifs with h1
      · subst h1; norm_num
      · simp
  rw [hfun] at hfib
  -- the indicator sums to `1`, hence `(∑ a)·(π²/6) = 1`
  have hone : (∑' n, a n) * (Real.pi ^ 2 / 6) = 1 :=
    hfib.unique (hasSum_ite_eq 1 (1 : ℝ))
  -- solve for `∑ a`
  have hpi2 : Real.pi ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff hpi2]
  linear_combination 6 * hone

end MobiusZetaTwo
