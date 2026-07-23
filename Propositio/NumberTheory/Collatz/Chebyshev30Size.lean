import Propositio.NumberTheory.Collatz.Chebyshev30M
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chebyshev-30: factorial-ratio combinatorics for the `M`-size bound

Two reusable, axiom-clean bricks toward the `M`-size bound `log M(N) ≤ A·N` (the upper half of the
per-step inequality `hstep`):

* `choose_le_two_pow_pred` : `C(n+1, k) ≤ 2^n`.
* `M_mul_fact_five` : the **exact two-binomial peel**
  `M(N)·⌊N/5⌋! = C(N,⌊N/2⌋)·C(N−⌊N/2⌋,⌊N/3⌋)·(N−⌊N/2⌋−⌊N/3⌋)!·⌊N/30⌋!`.

CAUTION (recorded for the KB): a *crude* binomial size bound `M(N) ≤ C(N,a)·C(N−a,b)` is **FALSE**
(floor wobble makes the trailing factor `> 1`, e.g. `M(5) = 60 > C(5,2)·C(3,1) = 30`).  Even the
true clean bound `M(N)² ≤ 8^N` (numerically verified `N ≤ 400`) gives only `A = 1.5·log 2 ≈ 1.040`,
i.e. `θ ≤ 1.248x` — which closes only a *looser* `Den ≤ D·36.4ⁿ` (`C = 36.4`), **not** the prize's
`DenIntN_bound_30` (`C = 30`, needs `θ ≤ 1.151x`, i.e. `A ≤ 0.959`).  The prize-grade constant
`A ≈ 0.921` (the period-30 entropy) genuinely needs an explicit two-sided Stirling estimate; the
`M`-size brick remains the analytic long pole.
-/

namespace CollatzChebyshev30

open Nat Finset

/-- **`C(n+1, k) ≤ 2^n`** — every binomial coefficient is at most half its row sum.  Pascal
induction: `C(n+2, j+1) = C(n+1, j) + C(n+1, j+1) ≤ 2^n + 2^n = 2^(n+1)`. -/
theorem choose_le_two_pow_pred : ∀ n k : ℕ, Nat.choose (n + 1) k ≤ 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro k
    match k with
    | 0 => simp
    | 1 => simp
    | (k + 2) => rw [Nat.choose_eq_zero_of_lt (by omega)]; positivity
  | succ n ih =>
    intro k
    match k with
    | 0 => simp only [Nat.choose_zero_right]; exact Nat.one_le_pow _ _ (by norm_num)
    | (j + 1) =>
      rw [Nat.choose_succ_succ]
      calc Nat.choose (n + 1) j + Nat.choose (n + 1) (j + 1)
          ≤ 2 ^ n + 2 ^ n := Nat.add_le_add (ih j) (ih (j + 1))
        _ = 2 ^ (n + 1) := by ring

/-- **The two-binomial peel.**  `M(N) · ⌊N/5⌋! = C(N,a)·C(N−a,b)·(N−a−b)!·⌊N/30⌋!`
with `a = ⌊N/2⌋, b = ⌊N/3⌋`.  Pure factorial algebra from `M_mul_den` and
`choose_mul_factorial_mul_factorial` (applied at `a ≤ N` and `b ≤ N−a`), cancelling `a!·b!`. -/
theorem M_mul_fact_five (N : ℕ) :
    M N * (N / 5)! =
      Nat.choose N (N / 2) * Nat.choose (N - N / 2) (N / 3)
        * (N - N / 2 - N / 3)! * (N / 30)! := by
  have haN : N / 2 ≤ N := Nat.div_le_self _ _
  have hbNa : N / 3 ≤ N - N / 2 := by omega
  have key1 : Nat.choose N (N / 2) * (N / 2)! * (N - N / 2)! = N ! :=
    Nat.choose_mul_factorial_mul_factorial haN
  have key2 : Nat.choose (N - N / 2) (N / 3) * (N / 3)! * (N - N / 2 - N / 3)! = (N - N / 2)! :=
    Nat.choose_mul_factorial_mul_factorial hbNa
  have hmd : M N * ((N / 2)! * (N / 3)! * (N / 5)!) = N ! * (N / 30)! := by
    simpa only [M_den, M_num] using M_mul_den N
  apply Nat.eq_of_mul_eq_mul_right (show 0 < (N / 2)! * (N / 3)! from by positivity)
  calc M N * (N / 5)! * ((N / 2)! * (N / 3)!)
      = M N * ((N / 2)! * (N / 3)! * (N / 5)!) := by ring
    _ = N ! * (N / 30)! := hmd
    _ = Nat.choose N (N / 2) * (N / 2)! * (N - N / 2)! * (N / 30)! := by rw [key1]
    _ = Nat.choose N (N / 2) * (N / 2)!
          * (Nat.choose (N - N / 2) (N / 3) * (N / 3)! * (N - N / 2 - N / 3)!) * (N / 30)! := by
        rw [← key2]
    _ = Nat.choose N (N / 2) * Nat.choose (N - N / 2) (N / 3) * (N - N / 2 - N / 3)! * (N / 30)!
          * ((N / 2)! * (N / 3)!) := by ring

end CollatzChebyshev30
