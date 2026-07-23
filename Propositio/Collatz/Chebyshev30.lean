import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Chebyshev's period-30 weight `χ` — the leaf brick of the Chebyshev-30 primorial bound

The lone prize sorry `OSalikhovDenBound.DenIntN_bound_30` needs a primorial bound
`∏_{p ≤ 2n} p ≤ b^{2n}` with base `b < 3.5`, beating mathlib's only (structural, base-4)
`Nat.primorial_le_four_pow`.  The classical route (Chebyshev 1852) uses the weight
`χ(m) = m + ⌊m/30⌋ − ⌊m/2⌋ − ⌊m/3⌋ − ⌊m/5⌋`, the `p`-adic valuation weight of the integer
`M(x) = ⌊x⌋!·⌊x/30⌋! / (⌊x/2⌋!·⌊x/3⌋!·⌊x/5⌋!)`.

**Key simplification.**  In the application we evaluate at `x = 2n` (a *natural* number), and by
Legendre + the nested-floor identity `⌊⌊2n/pᵏ⌋/d⌋ = ⌊2n/(d·pᵏ)⌋`, every term of `v_p(M(2n))` is
`χ` evaluated at the **natural** number `m = ⌊2n/pᵏ⌋`.  So `χ : ℕ → ℤ` with `χ` period `30`, and
`0 ≤ χ(m) ≤ 1` is a finite `decide` over the 30 residues — *no real-analysis periodicity needed*.

This file proves that leaf (`chiW_nonneg`, `chiW_le_one`, and `chiW_eq_one_of_mem_Icc_1_5`, the
`χ = 1` on `1 ≤ m ≤ 5` fact that drives the `θ(x) − θ(x/6)` lower bound).  The downstream bricks
(`M_integral_valuation`, `stirling_M_bound`, `theta_chebyshev30`, `lcm_le_exp_psi`) are queued.
-/

namespace CollatzChebyshev30

/-- Chebyshev's period-30 weight, `χ(m) = m + ⌊m/30⌋ − ⌊m/2⌋ − ⌊m/3⌋ − ⌊m/5⌋` (ℕ-division). -/
def chiW (m : ℕ) : ℤ :=
  (m : ℤ) + ((m / 30 : ℕ) : ℤ) - ((m / 2 : ℕ) : ℤ) - ((m / 3 : ℕ) : ℤ) - ((m / 5 : ℕ) : ℤ)

/-- `χ` has period `30`:  `χ(m + 30) = χ(m)`  (`30 + 1 − 15 − 10 − 6 = 0`). -/
theorem chiW_periodic (m : ℕ) : chiW (m + 30) = chiW m := by
  unfold chiW
  have h30 : (m + 30) / 30 = m / 30 + 1 := by omega
  have h2 : (m + 30) / 2 = m / 2 + 15 := by omega
  have h3 : (m + 30) / 3 = m / 3 + 10 := by omega
  have h5 : (m + 30) / 5 = m / 5 + 6 := by omega
  rw [h30, h2, h3, h5]
  push_cast
  ring

/-- Reduce the argument of `χ` modulo its period. -/
theorem chiW_mod (m : ℕ) : chiW m = chiW (m % 30) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 30 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hlt : m - 30 < m := by omega
      have hrec : chiW (m - 30) = chiW ((m - 30) % 30) := ih _ hlt
      have heq : m = (m - 30) + 30 := by omega
      have e2 : (m - 30) % 30 = m % 30 := by omega
      calc chiW m = chiW ((m - 30) + 30) := by rw [← heq]
        _ = chiW (m - 30) := chiW_periodic _
        _ = chiW ((m - 30) % 30) := hrec
        _ = chiW (m % 30) := by rw [e2]

/-- **`χ ≥ 0` everywhere** (so `M(2n)` is a genuine integer / the factorial ratio is integral). -/
theorem chiW_nonneg (m : ℕ) : 0 ≤ chiW m := by
  rw [chiW_mod]
  have h : m % 30 < 30 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 30) <;> decide

/-- **`χ ≤ 1` everywhere** (so `log M(2n) ≤ ψ(2n)` — the Chebyshev upper bound). -/
theorem chiW_le_one (m : ℕ) : chiW m ≤ 1 := by
  rw [chiW_mod]
  have h : m % 30 < 30 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 30) <;> decide

/-- Packaged two-sided bound `0 ≤ χ(m) ≤ 1`. -/
theorem chiW_mem_zero_one (m : ℕ) : 0 ≤ chiW m ∧ chiW m ≤ 1 :=
  ⟨chiW_nonneg m, chiW_le_one m⟩

/-- **`χ(m) = 1` for `1 ≤ m ≤ 5`.**  This is the engine of the `θ(x) − θ(x/6) ≤ log M(x)` lower
bound: a prime `p` with `2n/6 < p ≤ 2n` has `⌊2n/p⌋ ∈ {1,2,3,4,5}`, contributing `χ = 1` (i.e.
`log p`) to `log M(2n)`. -/
theorem chiW_eq_one_of_mem_Icc_1_5 (m : ℕ) (h1 : 1 ≤ m) (h5 : m ≤ 5) : chiW m = 1 := by
  interval_cases m <;> decide

end CollatzChebyshev30
