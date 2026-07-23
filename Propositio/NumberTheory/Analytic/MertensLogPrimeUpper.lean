import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Chebyshev
import Propositio.NumberTheory.Analytic.MertensLogPrimeLower

/-!
# A Mertens-type upper bound `Σ_{p ≤ n} (log p)/p ≤ log n + C`

This is the companion to `MertensLogPrimeLower` (which proves `mertensSum n ≥ (1/4) log n`).
Together they pin `Σ_{p ≤ x} (log p)/p = log x + O(1)`, Mertens' first theorem.

We reuse the *same* `mertensSum` definition from `MertensLogPrimeLower`, so a future capstone
can combine both one-sided bounds.

## Proof outline (the OTHER direction of the `log(n!)` two-ways argument)

1. **Factorization identity.** `log(n!) = Σ_p v_p(n!)·log p` over the prime support of `n!`,
   and that support is *exactly* the primes `≤ n` (`support_eq`).
2. **Legendre lower bound.** `v_p(n!) ≥ ⌊n/p⌋` (just the `j = 1` term of Legendre's formula,
   `div_le_factorization_factorial`), and `⌊n/p⌋ ≥ n/p − 1` in `ℝ`.  Hence termwise
   `v_p(n!)·log p ≥ n·(log p / p) − log p`, giving
   `log(n!) ≥ n·mertensSum n − θ(n)` where `θ(n) = Σ_{p ≤ n} log p` (`log_factorial_ge`).
3. **The Chebyshev link.** `Σ_{p ≤ n} log p = Chebyshev.theta n` (`nθ_eq_theta`), so mathlib's
   `Chebyshev.theta_le_log4_mul_x` gives `θ(n) ≤ log 4 · n`.
4. **Upper bound on `log(n!)`.** `n! ≤ n^n` (`Nat.factorial_le_pow`), so `log(n!) ≤ n·log n`.
5. **Combine.** `n·mertensSum n − θ(n) ≤ log(n!) ≤ n·log n`, hence
   `n·mertensSum n ≤ n·log n + log 4·n`, and dividing by `n > 0`,
   `mertensSum n ≤ log n + log 4`.
-/

open Real Finset

namespace MertensLogPrimeUpper

/-- The natural prime-log sum `Σ_{p ≤ n, p prime} log p`. Equal to `Chebyshev.theta n`. -/
noncomputable def nθ (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p

/-- The prime support of `n!` is **exactly** the primes `≤ n` (every prime `≤ n` divides `n!`). -/
lemma support_eq (n : ℕ) :
    (Nat.factorial n).factorization.support = (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  rw [Nat.support_factorization, Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpp, hdvd, _⟩
    have hpn : p ≤ n := (hpp.dvd_factorial).mp hdvd
    exact ⟨by omega, hpp⟩
  · rintro ⟨hlt, hpp⟩
    exact ⟨hpp, (hpp.dvd_factorial).mpr (by omega), (Nat.factorial_pos n).ne'⟩

/-- **Legendre lower bound (the `j = 1` term).** For a prime `p`, `⌊n/p⌋ ≤ v_p(n!)`. -/
lemma div_le_factorization_factorial (n p : ℕ) (hp : p.Prime) :
    n / p ≤ (Nat.factorial n).factorization p := by
  rcases lt_or_ge n p with hpn | hpn
  · rw [Nat.div_eq_of_lt hpn]; exact Nat.zero_le _
  · -- include the `i = 1` term of Legendre's sum `∑_{i≥1} ⌊n/p^i⌋`
    have hb : Nat.log p n < Nat.log p n + 1 := Nat.lt_succ_self _
    rw [Nat.factorization_factorial hp hb]
    have h1mem : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) := by
      rw [Finset.mem_Ico]
      have : 0 < Nat.log p n := Nat.log_pos hp.one_lt hpn
      omega
    calc n / p = n / p ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i :=
          Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1mem

/-- **Termwise lower bound:** for a prime `p`, `n·(log p / p) − log p ≤ v_p(n!)·log p`. -/
lemma term_bound_lower (n p : ℕ) (hpp : p.Prime) :
    (n : ℝ) * (Real.log p / p) - Real.log p
      ≤ ((Nat.factorial n).factorization p : ℝ) * Real.log p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  -- `⌊n/p⌋ ≤ v_p(n!)`, cast to `ℝ`.
  have hvp := div_le_factorization_factorial n p hpp
  have hcast_vp : ((n / p : ℕ) : ℝ) ≤ ((Nat.factorial n).factorization p : ℝ) := by
    exact_mod_cast hvp
  -- `⌊n/p⌋ ≥ n/p − 1` in `ℝ`, from `n < p·(⌊n/p⌋ + 1)`.
  have hdm : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.div_add_mod n p
  have hmodlt : ((n % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt n hpp.pos
  have h1 : (n : ℝ) < (p : ℝ) * (((n / p : ℕ) : ℝ) + 1) := by nlinarith [hdm, hmodlt]
  have hdivlt : (n : ℝ) / (p : ℝ) ≤ ((n / p : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hppos]; nlinarith [h1]
  have hle : (n : ℝ) / (p : ℝ) - 1 ≤ ((Nat.factorial n).factorization p : ℝ) :=
    le_trans (by linarith [hdivlt]) hcast_vp
  have hmul := mul_le_mul_of_nonneg_right hle hlogp
  calc (n : ℝ) * (Real.log p / (p : ℝ)) - Real.log p
      = ((n : ℝ) / (p : ℝ) - 1) * Real.log p := by ring
    _ ≤ ((Nat.factorial n).factorization p : ℝ) * Real.log p := hmul

/-- **Lower bound via Legendre:** `n·mertensSum n − θ(n) ≤ log(n!)`. -/
theorem log_factorial_ge (n : ℕ) :
    (n : ℝ) * MertensLogPrimeLower.mertensSum n - nθ n ≤ Real.log (Nat.factorial n) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, support_eq]
  unfold MertensLogPrimeLower.mertensSum nθ
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mem_filter] at hp
  exact term_bound_lower n p hp.2

/-- **The Chebyshev link:** `Σ_{p ≤ n} log p = Chebyshev.theta n`. -/
lemma nθ_eq_theta (n : ℕ) : nθ n = Chebyshev.theta n := by
  unfold nθ Chebyshev.theta
  rw [Nat.floor_natCast]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hlt, hpp⟩
    exact ⟨⟨hpp.pos, by omega⟩, hpp⟩
  · rintro ⟨⟨_, hle⟩, hpp⟩
    exact ⟨by omega, hpp⟩

/-- **Upper bound on `log(n!)`:** `log(n!) ≤ n·log n` (from `n! ≤ n^n`). -/
lemma log_factorial_le (n : ℕ) : Real.log (Nat.factorial n) ≤ (n : ℝ) * Real.log n := by
  have h1 : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hpos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (Nat.factorial n) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hpos h1
    _ = (n : ℝ) * Real.log n := by rw [Real.log_pow]

/-- **Mertens-type upper bound.** With `C = log 4` and `N = 1`,
`Σ_{p ≤ n} (log p)/p ≤ log n + log 4` for all `n ≥ 1`. -/
theorem mertensSum_le :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      MertensLogPrimeLower.mertensSum n ≤ Real.log n + C := by
  refine ⟨Real.log 4, 1, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlb := log_factorial_ge n
  have hub := log_factorial_le n
  have hθ : nθ n ≤ Real.log 4 * (n : ℝ) := by
    rw [nθ_eq_theta]; exact Chebyshev.theta_le_log4_mul_x (by positivity)
  -- `n·mertensSum n ≤ n·(log n + log 4)`.
  have hchain :
      (n : ℝ) * MertensLogPrimeLower.mertensSum n
        ≤ (n : ℝ) * (Real.log n + Real.log 4) := by
    have e : (n : ℝ) * (Real.log n + Real.log 4)
        = (n : ℝ) * Real.log n + Real.log 4 * (n : ℝ) := by ring
    rw [e]; linarith [hlb, hub, hθ]
  exact le_of_mul_le_mul_left hchain hnpos

end MertensLogPrimeUpper
