import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Chebyshev's lower bound for `ψ` (and `θ`)

mathlib provides Chebyshev's *upper* bound (`Chebyshev.theta_le_log4_mul_x`,
`Chebyshev.psi_le_const_mul_self`) but not the *lower* bound (it is listed as a TODO in
`Mathlib/NumberTheory/Chebyshev.lean`).  This file fills that gap via the classical
central-binomial / Erdős argument.

The engine is `Nat.centralBinom n = (2n).choose n`:

* a **size lower bound** `4^n ≤ 2n · centralBinom n`
  (`Nat.four_pow_le_two_mul_self_mul_centralBinom`), and
* a **prime-power upper bound** `p ^ vₚ(centralBinom n) ≤ 2n`
  (`Nat.pow_factorization_choose_le`),

combined through the von Mangoldt divisor identity
`∑_{d ∣ N} Λ d = log N` (`ArithmeticFunction.vonMangoldt_sum`) to give
`log (centralBinom n) ≤ ψ (2n)`.  Together these yield
`ψ (2n) ≥ n·log 4 − log (2n) = 2n·log 2 − log (2n)`, which transfers to a genuine
linear lower bound `c·x ≤ ψ x` for all real `x ≥ 2`.

## Main results

* `ChebyshevThetaLower.chebyshev_psi_ge` : `∃ c > 0, ∀ x ≥ 2, c·x ≤ ψ x`.
* `ChebyshevThetaLower.chebyshev_theta_ge` : `∃ c > 0, ∃ x₀, ∀ x ≥ x₀, c·x ≤ θ x`.
-/

open Chebyshev Finset Real
open ArithmeticFunction hiding log

namespace ChebyshevThetaLower

/-- **Key link.**  Every prime power in the factorization of the central binomial coefficient
is `≤ 2n`, so `log (centralBinom n)` is dominated by `ψ (2n)`. -/
theorem log_centralBinom_le_psi (n : ℕ) :
    Real.log (Nat.centralBinom n) ≤ ψ ((2 * n : ℕ) : ℝ) := by
  -- `ψ` at a natural argument is the von Mangoldt sum over `Ioc 0 (2n)`.
  have hpsi : ψ ((2 * n : ℕ) : ℝ) = ∑ m ∈ Finset.Ioc 0 (2 * n), Λ m := by
    rw [Chebyshev.psi, Nat.floor_natCast]
  -- The divisor set restricted to prime powers.
  set A := (Nat.centralBinom n).divisors.filter (fun d => IsPrimePow d) with hA
  have hAsub : A ⊆ (Nat.centralBinom n).divisors := Finset.filter_subset _ _
  have hzero : ∀ d ∈ (Nat.centralBinom n).divisors, d ∉ A → Λ d = 0 := by
    intro d hd hnotin
    rw [hA, Finset.mem_filter, not_and] at hnotin
    have hnp : ¬ IsPrimePow d := hnotin hd
    rw [ArithmeticFunction.vonMangoldt_apply]
    simp [hnp]
  rw [hpsi, ← ArithmeticFunction.vonMangoldt_sum (n := Nat.centralBinom n),
      ← Finset.sum_subset hAsub hzero]
  -- Now: ∑_{d ∈ A} Λ d ≤ ∑_{m ∈ Ioc 0 (2n)} Λ m, by `A ⊆ Ioc 0 (2n)` and `Λ ≥ 0`.
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [hA, Finset.mem_filter] at hd
    obtain ⟨hddvd, hpp⟩ := hd
    rw [Nat.mem_divisors] at hddvd
    obtain ⟨hdvd, hne⟩ := hddvd
    rw [Finset.mem_Ioc]
    refine ⟨hpp.pos, ?_⟩
    -- Write `d = p ^ k` with `p` prime, `k ≥ 1`.
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    -- `k ≤ vₚ(centralBinom n)` because `p ^ k ∣ centralBinom n`.
    have hkle : k ≤ (Nat.centralBinom n).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hne]
      exact hdvd
    -- `centralBinom n > 1`, hence `n ≥ 1`.
    have h2 : 2 ≤ p ^ k := by
      have := Nat.one_lt_pow hk.ne' hp.one_lt
      omega
    have hcb1 : 1 < Nat.centralBinom n :=
      lt_of_lt_of_le (by omega : 1 < p ^ k) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd)
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [Nat.centralBinom_zero] at hcb1
      · exact h
    calc p ^ k ≤ p ^ (Nat.centralBinom n).factorization p :=
            Nat.pow_le_pow_right hp.one_le hkle
      _ ≤ 2 * n := by
            rw [Nat.centralBinom_eq_two_mul_choose]
            exact Nat.pow_factorization_choose_le (show 0 < 2 * n by omega)
  · intro d _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- The integer-point Chebyshev lower bound:
`ψ (2n) ≥ n·log 4 − log (2n)`. -/
theorem psi_two_mul_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * (n : ℝ)) ≤ ψ ((2 * n : ℕ) : ℝ) := by
  have h4 : (4 : ℕ) ^ n ≤ 2 * n * Nat.centralBinom n :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hcbpos : 0 < Nat.centralBinom n := Nat.centralBinom_pos n
  have h4r : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h4
  have hl := Real.log_le_log (by positivity) h4r
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at hl
  -- `hl : ↑n * log 4 ≤ log (2 ↑n) + log (centralBinom n)`
  have hle := log_centralBinom_le_psi n
  linarith [hl, hle]

/-- Real-variable Chebyshev lower bound with the elementary main term:
`ψ x ≥ (x − 2)·log 2 − log x` for `x ≥ 2`. -/
theorem psi_ge_real (x : ℝ) (hx : 2 ≤ x) :
    (x - 2) * Real.log 2 - Real.log x ≤ ψ x := by
  have hxpos : 0 < x := by linarith
  have hx2 : (0 : ℝ) ≤ x / 2 := by positivity
  set n := ⌊x / 2⌋₊ with hn_def
  have hn1 : 1 ≤ n := by
    rw [hn_def, Nat.le_floor_iff hx2]; push_cast; linarith
  have hnle : (2 * (n : ℝ)) ≤ x := by
    have := Nat.floor_le hx2
    rw [← hn_def] at this; linarith
  have hngt : x - 2 < 2 * (n : ℝ) := by
    have := Nat.lt_floor_add_one (x / 2)
    rw [← hn_def] at this; linarith
  have h2npos : (0 : ℝ) < 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  -- monotonicity `ψ (2n) ≤ ψ x`
  have hmono : ψ ((2 * n : ℕ) : ℝ) ≤ ψ x := by
    apply Chebyshev.psi_mono
    push_cast; linarith [hnle]
  have hbound := psi_two_mul_ge n hn1
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlogle : Real.log (2 * (n : ℝ)) ≤ Real.log x :=
    Real.log_le_log h2npos (by linarith [hnle])
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlog4] at hbound
  -- `(x-2) log2 ≤ 2n log2`
  have hprod : (x - 2) * Real.log 2 ≤ 2 * (n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hngt]) hlog2pos.le
  nlinarith [hbound, hmono, hlogle, hprod]

/-- Auxiliary: `log x ≤ 2 √x` for `x > 0`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  have hls : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [hls] at hs
  have hsnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

/-- **Chebyshev's lower bound for `ψ`.**  There is an explicit positive constant
`c = (log 2)/64` with `c·x ≤ ψ x` for every real `x ≥ 2`. -/
theorem chebyshev_psi_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * x ≤ Chebyshev.psi x := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 64, by positivity, ?_⟩
  -- `ψ 2 ≥ log 2`, used for the small-`x` range.
  have hpsi2 : Real.log 2 ≤ ψ (2 : ℝ) := by
    rw [Chebyshev.psi, show ⌊(2 : ℝ)⌋₊ = 2 from by norm_num]
    have h2mem : (2 : ℕ) ∈ Finset.Ioc 0 2 := by decide
    have hsum := Finset.single_le_sum
      (f := fun m => Λ m) (fun i _ => ArithmeticFunction.vonMangoldt_nonneg) h2mem
    simp only [] at hsum
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] at hsum
    exact hsum
  intro x hx
  by_cases hx64 : x ≤ 64
  · -- small range: `c·x ≤ c·64 = log 2 ≤ ψ 2 ≤ ψ x`
    calc Real.log 2 / 64 * x
        ≤ Real.log 2 / 64 * 64 := by
          apply mul_le_mul_of_nonneg_left hx64; positivity
      _ = Real.log 2 := by ring
      _ ≤ ψ (2 : ℝ) := hpsi2
      _ ≤ ψ x := Chebyshev.psi_mono hx
  · -- large range: use the analytic bound and `log x ≤ 2√x ≤ x/4`.
    have hx64 : 64 < x := lt_of_not_ge hx64
    have hxpos : 0 < x := by linarith
    have hpgr := psi_ge_real x (by linarith)
    have hlogx := log_le_two_sqrt hxpos
    -- `√x ≤ x/8` for `x ≥ 64`
    have hsqrt_ge : (8 : ℝ) ≤ Real.sqrt x := by
      have : Real.sqrt 64 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
      rwa [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hxsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
    have hsx8 : Real.sqrt x ≤ x / 8 := by nlinarith [hsqrt_ge, hxsq, Real.sqrt_nonneg x]
    have hlb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    -- assemble
    have hkey : (0 : ℝ) ≤ (Real.log 2 - 0.6931471803) * (63 * x / 64 - 2) :=
      mul_nonneg (by linarith [hlb]) (by linarith)
    nlinarith [hpgr, hlogx, hsx8, hlb, hkey]

/-- **Chebyshev's lower bound for `θ`.**  There is an explicit positive constant `c` and a
threshold `x₀` with `c·x ≤ θ x` for all `x ≥ x₀`.  Obtained from the `ψ` bound and
`|ψ x − θ x| ≤ 2 √x · log x`, using `log x ≤ 4 x^{1/4}` to absorb the error term. -/
theorem chebyshev_theta_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ≤ Chebyshev.theta x := by
  obtain ⟨c, hcpos, hpsi⟩ := chebyshev_psi_ge
  refine ⟨c / 2, by positivity, (16 / c) ^ 4 + 2, ?_⟩
  intro x hx
  have hx_ge_pow : (16 / c) ^ 4 ≤ x := by linarith
  have hx2 : 2 ≤ x := by nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 16 / c) 4]
  have hxpos : 0 < x := by linarith
  -- `s = x^{1/4}`
  set s := Real.sqrt (Real.sqrt x) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.sqrt x := Real.mul_self_sqrt (Real.sqrt_nonneg x)
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
  have hs4 : s ^ 4 = x := by
    have : s ^ 4 = (s * s) * (s * s) := by ring
    rw [this, hss, hxx]
  -- `s ≥ 16 / c`
  have h16c_nn : (0 : ℝ) ≤ 16 / c := by positivity
  have hinner : Real.sqrt ((16 / c) ^ 4) = (16 / c) ^ 2 := by
    rw [show ((16 : ℝ) / c) ^ 4 = ((16 / c) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hval : Real.sqrt (Real.sqrt ((16 / c) ^ 4)) = 16 / c := by
    rw [hinner, Real.sqrt_sq h16c_nn]
  have hs_ge : 16 / c ≤ s := by
    rw [hs_def, ← hval]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hx_ge_pow)
  have hcs : (16 : ℝ) ≤ s * c := (div_le_iff₀ hcpos).mp hs_ge
  -- `log x ≤ 4 s`
  have hsx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hlogsqrt : Real.log (Real.sqrt x) ≤ 2 * Real.sqrt (Real.sqrt x) := log_le_two_sqrt hsx_pos
  have hlogx4 : Real.log x ≤ 4 * s := by
    rw [Real.log_sqrt hxpos.le] at hlogsqrt; rw [← hs_def] at hlogsqrt; linarith
  -- error term: `2 √x log x ≤ 8 s³`
  have herr : 2 * Real.sqrt x * Real.log x ≤ 8 * s ^ 3 := by
    rw [← hss]
    calc 2 * (s * s) * Real.log x ≤ 2 * (s * s) * (4 * s) :=
          mul_le_mul_of_nonneg_left hlogx4 (by positivity)
      _ = 8 * s ^ 3 := by ring
  -- `θ x ≥ ψ x − 2 √x log x`
  have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show (1 : ℝ) ≤ x by linarith)
  have hθlower : ψ x - 2 * Real.sqrt x * Real.log x ≤ θ x := by
    have h := (abs_le.mp habs).2
    linarith
  have hpsi_c : c * x ≤ ψ x := hpsi x hx2
  -- assemble: `(c/2) x ≤ c x − 8 s³ ≤ θ x`
  have hcube : (0 : ℝ) ≤ s ^ 3 * (s * c - 16) := mul_nonneg (by positivity) (by linarith)
  nlinarith [hθlower, herr, hpsi_c, hs4, hcube]

end ChebyshevThetaLower
