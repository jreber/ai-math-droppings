/-
# The Möbius–Mertens floor identity and the partial-sum bound `|∑ μ(n)/n| ≤ 1`

Two linked elementary analytic-number-theory facts, neither in mathlib:

* **`sum_moebius_mul_floor`** — the exact identity
    `∑_{n=1}^{N} μ(n)·⌊N/n⌋ = 1`   (for `N ≥ 1`),
  obtained by writing `⌊N/n⌋ = #{m ∈ [1,N] : n ∣ m}`, swapping the order of summation,
  and using the Möbius convolution `∑_{d ∣ m} μ(d) = [m = 1]`
  (`ArithmeticFunction.moebius_mul_coe_zeta` evaluated via `coe_mul_zeta_apply`).

* **`abs_sum_moebius_div_le_one`** — the partial-sum bound
    `|∑_{n=1}^{N} μ(n)/n| ≤ 1`,
  deduced from the floor identity by writing `⌊N/n⌋ = N/n − {N/n}`: the `n = 1`
  fractional part vanishes and the remaining `N−1` fractional parts are each `< 1`, so
  `|N·∑ μ(n)/n| ≤ 1 + (N−1) = N`.

The order-swap engine reuses the Dirichlet-hyperbola reindexing of
`DivisorSummatory.lean` / `OmegaSummatory.lean`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset ArithmeticFunction

namespace MobiusPartialSum

/-- For `1 ≤ m ≤ N`, the divisors of `m` are exactly the elements of `Icc 1 N` dividing `m`. -/
theorem divisors_eq_filter_Icc {m N : ℕ} (h1 : 1 ≤ m) (hm : m ≤ N) :
    m.divisors = (Finset.Icc 1 N).filter (· ∣ m) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
      rintro rfl; simp only [Nat.zero_dvd] at hd; omega)
    exact ⟨⟨hdpos, (Nat.le_of_dvd (by omega) hd).trans hm⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

/-- **The Möbius–Mertens floor identity.**  `∑_{n=1}^{N} μ(n)·⌊N/n⌋ = 1` for `N ≥ 1`. -/
theorem sum_moebius_mul_floor (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℤ) * ((N / n : ℕ) : ℤ)) = 1 := by
  -- `⌊N/n⌋ = #{m ∈ [1,N] : n ∣ m} = ∑_{m ∈ [1,N]} [n ∣ m]`.
  have hfloor : ∀ n ∈ Finset.Icc 1 N, ((N / n : ℕ) : ℤ)
      = ∑ m ∈ Finset.Icc 1 N, (if n ∣ m then (1 : ℤ) else 0) := by
    intro n _
    have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hIcc, ← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]
    push_cast
    rfl
  calc (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℤ) * ((N / n : ℕ) : ℤ))
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℤ) * (if n ∣ m then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hfloor n hn, Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℤ) * (if n ∣ m then 1 else 0) := Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 N, (if m = 1 then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Icc] at hm
        have hinner : ∑ n ∈ Finset.Icc 1 N,
              (ArithmeticFunction.moebius n : ℤ) * (if n ∣ m then 1 else 0)
            = ∑ n ∈ m.divisors, (ArithmeticFunction.moebius n : ℤ) := by
          rw [divisors_eq_filter_Icc hm.1 hm.2, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          by_cases h : n ∣ m <;> simp [h]
        rw [hinner, ← ArithmeticFunction.coe_mul_zeta_apply,
          ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    _ = 1 := by
        rw [Finset.sum_ite_eq']
        simp [Finset.mem_Icc, hN]

/-- **The partial-sum bound.**  `|∑_{n=1}^{N} μ(n)/n| ≤ 1`. -/
theorem abs_sum_moebius_div_le_one (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp
  -- `N ≥ 1`.
  set S := Finset.Icc 1 N with hS
  set L : ℝ := ∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) with hL
  -- The floor identity, cast to `ℝ`.
  have hAreal : (∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_moebius_mul_floor N hN)
    push_cast at h
    rw [hS]; exact h
  -- `N · L = ∑ μ(n)·(N/n)` (real division).
  have hNL : (N : ℝ) * L
      = ∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) * ((N : ℝ) / (n : ℝ)) := by
    rw [hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  -- Split `N/n = ⌊N/n⌋ + {N/n}`.
  set E : ℝ := ∑ n ∈ S,
      (ArithmeticFunction.moebius n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) with hE
  have hsplit : (∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) * ((N : ℝ) / (n : ℝ)))
      = (∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ)) + E := by
    rw [hE, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hNL_eq : (N : ℝ) * L = 1 + E := by rw [hNL, hsplit, hAreal]
  -- Fractional parts: `0 ≤ {N/n} ≤ 1`.
  have hfrac_nonneg : ∀ n ∈ S, 0 ≤ (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) := by
    intro n _
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := n)
    linarith
  have hfrac_le_one : ∀ n ∈ S, (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) ≤ 1 := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hdm : (n : ℝ) * ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N n
    have hmod : ((N % n : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast Nat.mod_lt N (by omega)
    have hle : (N : ℝ) / (n : ℝ) ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn0]; nlinarith [hdm, hmod]
    linarith
  -- Per-term bound: `|μ(n)|·{N/n} ≤ (if n = 1 then 0 else 1)`.
  have hterm : ∀ n ∈ S, |(ArithmeticFunction.moebius n : ℝ)|
      * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) ≤ (if n = 1 then (0 : ℝ) else 1) := by
    intro n hn
    have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    have hf0 := hfrac_nonneg n hn
    have hf1 := hfrac_le_one n hn
    by_cases h1 : n = 1
    · subst h1
      have hz : (N : ℝ) / ((1 : ℕ) : ℝ) - ((N / 1 : ℕ) : ℝ) = 0 := by
        rw [Nat.div_one, Nat.cast_one, div_one]; ring
      rw [hz, mul_zero]
      simp
    · simp only [if_neg h1]
      calc |(ArithmeticFunction.moebius n : ℝ)| * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))
          ≤ 1 * 1 := mul_le_mul hμ hf1 hf0 (by norm_num)
        _ = 1 := by ring
  -- `|E| ≤ ∑ |μ(n)|·{N/n} ≤ ∑ (if n = 1 then 0 else 1) = N − 1`.
  have hEabs : |E| ≤ ∑ n ∈ S, |(ArithmeticFunction.moebius n : ℝ)|
      * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) := by
    rw [hE]
    calc |∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ)
            * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))|
        ≤ ∑ n ∈ S, |(ArithmeticFunction.moebius n : ℝ)
            * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ S, |(ArithmeticFunction.moebius n : ℝ)|
            * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [abs_mul, abs_of_nonneg (hfrac_nonneg n hn)]
  have hbound_sum : ∑ n ∈ S, (if n = 1 then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
    have h1 : (∑ n ∈ S, (if n = 1 then (0 : ℝ) else 1))
        = (∑ n ∈ S, (1 : ℝ)) - (∑ n ∈ S, (if n = 1 then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _; by_cases h : n = 1 <;> simp [h]
    rw [h1]
    have hcard : (∑ n ∈ S, (1 : ℝ)) = (N : ℝ) := by
      rw [Finset.sum_const, hS, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    have hone : (∑ n ∈ S, (if n = 1 then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq', hS, if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)]
    rw [hcard, hone]
  have hEbound : |E| ≤ (N : ℝ) - 1 :=
    le_trans hEabs (le_trans (Finset.sum_le_sum hterm) (le_of_eq hbound_sum))
  -- `|N·L| ≤ N`, hence `|L| ≤ 1`.
  have hNLabs : |(N : ℝ) * L| ≤ (N : ℝ) := by
    rw [hNL_eq]
    calc |(1 : ℝ) + E| ≤ |(1 : ℝ)| + |E| := abs_add_le _ _
      _ ≤ 1 + ((N : ℝ) - 1) := by rw [abs_one]; linarith [hEbound]
      _ = (N : ℝ) := by ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNL2 : (N : ℝ) * |L| ≤ (N : ℝ) * 1 := by
    rw [mul_one]
    calc (N : ℝ) * |L| = |(N : ℝ) * L| := by rw [abs_mul, abs_of_pos hNpos]
      _ ≤ (N : ℝ) := hNLabs
  exact le_of_mul_le_mul_left hNL2 hNpos

end MobiusPartialSum
