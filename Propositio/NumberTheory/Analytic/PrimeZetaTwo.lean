import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Convergence of the prime zeta function at `2`

The sum of the reciprocals of the squares of the primes converges, and is bounded
above by `ζ(2) = π²/6`.

The prime-indexed family `p ↦ 1/p²` (over the subtype `Nat.Primes`) is the
restriction along the injective coercion `Nat.Primes → ℕ` of the summable,
non-negative family `n ↦ 1/n²` whose total is `π²/6` (`hasSum_zeta_two`).  Hence
it is itself summable, and its `tsum` is `≤ π²/6`.
-/

namespace PrimeZetaTwo

open Filter

/-- The full `ℕ`-indexed family `n ↦ 1/n²` is summable (this is `∑ 1/n² = π²/6`). -/
private lemma summable_nat_inv_sq : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
  hasSum_zeta_two.summable

/-- The coercion `Nat.Primes → ℕ` is injective. -/
private lemma primes_coe_injective : Function.Injective ((↑) : Nat.Primes → ℕ) :=
  Subtype.coe_injective

/-- **Prime zeta at `2` converges.**  The sum of the reciprocals of the squares of
the primes is summable. -/
theorem prime_inv_sq_summable :
    Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ) ^ 2) :=
  summable_nat_inv_sq.comp_injective primes_coe_injective

/-- **The prime zeta value at `2` is bounded by `ζ(2) = π²/6`.** -/
theorem prime_inv_sq_tsum_le :
    ∑' p : Nat.Primes, (1 : ℝ) / (p : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hle :
      ∑' p : Nat.Primes, (1 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
    tsum_comp_le_tsum_of_inj summable_nat_inv_sq (fun n => by positivity)
      primes_coe_injective
  rw [hasSum_zeta_two.tsum_eq] at hle
  exact hle

#print axioms prime_inv_sq_summable
#print axioms prime_inv_sq_tsum_le

end PrimeZetaTwo
