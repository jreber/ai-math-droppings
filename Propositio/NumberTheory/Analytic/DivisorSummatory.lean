/-
# Average order of the divisor function (Dirichlet's divisor problem, leading term)

Let `d(n) = n.divisors.card` be the number of divisors of `n`, and
`D(N) = ∑_{n=1}^{N} d(n)` its summatory function.

We prove the classical **average order** estimate
    `D(N) = N · log N + O(N)`,
with the leading term `N log N` *exact* and an explicit two-sided `O(N)` error.

The engine is the **Dirichlet hyperbola identity** (basic form)
    `∑_{n=1}^{N} d(n) = ∑_{k=1}^{N} ⌊N/k⌋`,
obtained by counting lattice points `{(k,m) : k·m ≤ N}` two ways, plus the
harmonic-number bounds `log(N+1) ≤ H_N ≤ 1 + log N` already in mathlib.

mathlib has the divisor function and the harmonic bounds, but not this Dirichlet
asymptotic; both lemmas below are new and broadly reusable.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace DivisorSummatory

/-- For `1 ≤ n ≤ N`, the divisors of `n` are exactly the elements of `Icc 1 N`
that divide `n`. -/
theorem divisors_eq_filter_Icc {n N : ℕ} (h1 : 1 ≤ n) (hn : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (· ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
      rintro rfl; simp only [Nat.zero_dvd] at hd; omega)
    exact ⟨⟨hdpos, (Nat.le_of_dvd (by omega) hd).trans hn⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

/-- **Dirichlet hyperbola identity (basic form).**
The summatory divisor function equals `∑_{k=1}^{N} ⌊N/k⌋`. -/
theorem sum_divisors_card_eq_sum_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, n.divisors.card = ∑ k ∈ Finset.Icc 1 N, N / k := by
  -- Rewrite each `d(n)` as a filtered count over `Icc 1 N`, then swap the order.
  have hL : ∀ n ∈ Finset.Icc 1 N, n.divisors.card
      = ∑ k ∈ Finset.Icc 1 N, (if k ∣ n then 1 else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [divisors_eq_filter_Icc hn.1 hn.2, Finset.card_filter]
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  -- Now `∑_{k} ∑_{n} [k ∣ n] = ∑_{k} #{n ∈ Icc 1 N : k ∣ n} = ∑_{k} N/k`.
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.card_filter]
  -- `Icc 1 N = Ioc 0 N`, and `#{x ∈ Ioc 0 N : k ∣ x} = N / k`.
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- `∑_{k=1}^{N} 1/k = H_N` over `ℝ`. -/
theorem sum_inv_eq_harmonic (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

/-- **Average order of the divisor function.**
With `D(N) = ∑_{n=1}^{N} d(n)`, we have `D(N) = N·log N + O(N)`, here with the
explicit constant `C = 1` and threshold `N₀ = 1`:
    `|D(N) − N·log N| ≤ N`  for all `N ≥ 1`. -/
theorem divisor_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)) - N * Real.log N| ≤ C * N := by
  refine ⟨1, 1, ?_⟩
  intro N hN
  -- Notation: the summatory function as a real number, via the hyperbola identity.
  have hpos : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  -- D(N) (real) = ∑_{k} ⌊N/k⌋  (cast of the Nat identity)
  have hD : (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ))
      = ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ) := by
    have := sum_divisors_card_eq_sum_floor N
    have := congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at this ⊢
    exact this
  rw [hD]
  -- ∑_{k} (N:ℝ)/k = N · H_N
  have hNH : ∑ k ∈ Finset.Icc 1 N, (N : ℝ) / k = N * (harmonic N : ℝ) := by
    rw [← sum_inv_eq_harmonic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [div_eq_mul_inv]
  -- ∑_{k} 1 = N  (card of Icc 1 N)
  have hcard : ∑ _k ∈ Finset.Icc 1 N, (1 : ℝ) = N := by
    rw [Finset.sum_const, Nat.card_Icc]
    simp
  -- Upper bound: D(N) ≤ ∑ (N:ℝ)/k = N·H_N
  have hub : ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ) ≤ N * (harmonic N : ℝ) := by
    rw [← hNH]
    apply Finset.sum_le_sum
    intro k _
    exact Nat.cast_div_le
  -- Lower bound: ∑ ((N:ℝ)/k − 1) ≤ D(N), i.e. N·H_N − N ≤ D(N)
  have hlb : N * (harmonic N : ℝ) - N ≤ ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ) := by
    have hsum : ∑ k ∈ Finset.Icc 1 N, ((N : ℝ) / k - 1)
        ≤ ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk.1
      -- (N:ℝ)/k < ⌊N/k⌋ + 1  from  N < k·(N/k + 1)
      have hlt : (N : ℝ) / k < ((N / k : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hkpos]
        have hnat : N < k * (N / k + 1) := by
          have h1 : k * (N / k) + N % k = N := Nat.div_add_mod N k
          have h2 : N % k < k := Nat.mod_lt N (by omega)
          calc N = k * (N / k) + N % k := h1.symm
            _ < k * (N / k) + k := by omega
            _ = k * (N / k + 1) := by ring
        have : (N : ℝ) < (k : ℝ) * (((N / k : ℕ) : ℝ) + 1) := by
          have := (Nat.cast_lt (α := ℝ)).mpr hnat
          push_cast at this
          linarith [this]
        linarith [this]
      linarith [hlt]
    have hexpand : ∑ k ∈ Finset.Icc 1 N, ((N : ℝ) / k - 1)
        = N * (harmonic N : ℝ) - N := by
      rw [Finset.sum_sub_distrib, hNH, hcard]
    linarith [hsum, hexpand ▸ hsum]
  -- Harmonic bounds: log N ≤ H_N ≤ 1 + log N
  have hHupper : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have hHlower : Real.log N ≤ (harmonic N : ℝ) := by
    have h := log_add_one_le_harmonic N
    have hmono : Real.log N ≤ Real.log (N + 1) := by
      apply Real.log_le_log hpos
      linarith
    calc Real.log N ≤ Real.log (↑(N + 1)) := by exact_mod_cast hmono
      _ ≤ (harmonic N : ℝ) := h
  -- Assemble:  N log N − N ≤ D(N) ≤ N log N + N
  rw [abs_le]
  constructor
  · -- −(1·N) ≤ D(N) − N log N
    have : N * Real.log N - N ≤ ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ) := by
      have : N * Real.log N - N ≤ N * (harmonic N : ℝ) - N := by
        have := mul_le_mul_of_nonneg_left hHlower (le_of_lt hpos)
        linarith
      linarith [hlb]
    nlinarith [this]
  · -- D(N) − N log N ≤ 1·N
    have : ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ) ≤ N * (1 + Real.log N) := by
      calc ∑ k ∈ Finset.Icc 1 N, ((N / k : ℕ) : ℝ)
          ≤ N * (harmonic N : ℝ) := hub
        _ ≤ N * (1 + Real.log N) := by
            apply mul_le_mul_of_nonneg_left hHupper (le_of_lt hpos)
    nlinarith [this]

end DivisorSummatory
