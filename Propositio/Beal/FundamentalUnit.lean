import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic
import Propositio.Beal.FiveRealSubfieldIso
import Propositio.Beal.GoldenKummerEngine
import Propositio.Beal.GoldenMinPoly
import Propositio.Beal.FundamentalUnitPell
import Propositio.Beal.LambdaCongruence

/-!
# Fundamental unit of `ℚ(√5)` — the golden ratio `φ`

This file assembles the "long pole" of the Kummer `p = 5` attack: properties of the golden ratio
`φ = 1 + ζ + ζ⁴ ∈ ℚ(ζ₅)` that are needed to complete Kummer's lemma.

## What we prove (axiom-clean)

1. **`fib_pos_of_pos`** — `Nat.fib n ≥ 1` for `n ≥ 1`.
2. **`fib_ne_zero_of_pos`** — `Nat.fib n ≠ 0` for `n ≥ 1`.
3. **`five_dvd_fib_mod5`** — `(Nat.fib n : ZMod 5) = 0 ↔ 5 ∣ n`.
4. **`golden_fib_coeff_mod5_zero_iff`** — `(fib(n+1) : ZMod 5) = 0 ↔ 5 ∣ (n+1)`.
5. **`golden_pow_succ_fib_coeff`** — `φ^(n+1) = fib(n) + fib(n+1)·φ`.
6. **`golden_not_algebraMap_rat`** — `φ` is not rational in `K` (minpoly degree 2).
7. **`golden_pow_succ_not_rational`** — `φ^(n+1)` is never rational in CharZero.
8. **`golden_pow_rational_iff_zero`** — `φ^n` is rational iff `n = 0`.
9. **`golden_kummer_five_power`** — If `5 ∣ n` then `φ^n = (φ^(n/5))^5`.

## What remains sorry'd

10. **`dual_snd_eq_fib_mod5`** — `((3+ε)^n).snd = (fib n : ZMod 5)`. Requires periodic
    induction on ZMod 5 (the two functions satisfy different recurrences; the mod-5 agreement
    requires a double induction or Pisano-period argument).

11. **`beal_fundamental_unit_sqrt5_statement`** — Every unit `a + b·φ` of `ℤ[φ]` is `±φⁿ`.
    **PROVED** (commit 8ba944a): transfer from ℝ via `golden_int_repr` + `int_lin_indep_goldenRatio`.

## The Kummer `p = 5` argument chain

1. Descent gives `v = ±φⁿ` with `v ≡ r (mod λ²)`.  [fundamental_unit — sorry'd]
2. `φⁿ ≡ r (mod λ²)` iff `5 ∣ fib n` iff `5 ∣ n`.   [five_dvd_fib_mod5]
3. `v = ±(φ^(n/5))^5` is a 5th power.               [golden_kummer_five_power]
-/

open BealFiveRealSubfieldIso BealGoldenKummerEngine BealGoldenMinPoly
open DualNumber TrivSqZeroExt

set_option linter.unusedSectionVars false

namespace BealFundamentalUnit

/-! ## Tier 1: Fibonacci positivity -/

/-- `Nat.fib n ≥ 1` for all `n ≥ 1`. -/
theorem fib_pos_of_pos {n : ℕ} (hn : n ≥ 1) : Nat.fib n ≥ 1 :=
  Nat.fib_pos.mpr hn

/-- `Nat.fib n ≠ 0` for `n ≥ 1`. -/
theorem fib_ne_zero_of_pos {n : ℕ} (hn : n ≥ 1) : Nat.fib n ≠ 0 := by
  have := Nat.fib_pos.mpr hn; omega

/-! ## Tier 1: Fibonacci mod-5 bridge -/

/-- `(Nat.fib n : ZMod 5) = 0 ↔ 5 ∣ n`. Bridge between the Fibonacci and dual-number
presentations of the Kummer `p = 5` engine. -/
theorem five_dvd_fib_mod5 (n : ℕ) : (Nat.fib n : ZMod 5) = 0 ↔ 5 ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [ZMod.natCast_eq_zero_iff]
  exact five_dvd_fib_iff n

/-- `(Nat.fib (n+1) : ZMod 5) = 0 ↔ 5 ∣ (n+1)`. Successor form. -/
theorem golden_fib_coeff_mod5_zero_iff (n : ℕ) : (Nat.fib (n + 1) : ZMod 5) = 0 ↔ 5 ∣ (n + 1) :=
  five_dvd_fib_mod5 (n + 1)

/-! ## Tier 1: Golden ratio Fibonacci power law -/

variable {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]

/-- `φ^(n+1) = fib(n) + fib(n+1)·φ` for `φ = 1+ζ+ζ⁴`. -/
theorem golden_pow_succ_fib_coeff {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (1 + ζ + ζ ^ 4) ^ (n + 1) =
      (Nat.fib n : K) + (Nat.fib (n + 1) : K) * (1 + ζ + ζ ^ 4) :=
  golden_pow_succ_fib hζ n

/-! ## Tier 2: φ is not rational; φ^(n+1) is never rational in CharZero -/

/-- `φ = 1 + ζ + ζ⁴` is not the image of any `r : ℚ` under `algebraMap ℚ K`.
Proof: `φ` satisfies `φ² − φ − 1 = 0`. If `φ = r ∈ ℚ`, then `r² − r − 1 = 0`, giving
`(2r−1)² = 5 ∈ ℚ²`, which is impossible by `not_isSquare_five_rat`. -/
theorem golden_not_algebraMap_rat {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (r : ℚ) :
    (1 + ζ + ζ ^ 4) ≠ algebraMap ℚ K r := by
  intro hr
  -- φ satisfies X² − X − 1 = 0
  have hphi_eq : (1 + ζ + ζ ^ 4) ^ 2 - (1 + ζ + ζ ^ 4) - 1 = 0 := golden_ratio_eq hζ
  -- Substituting hr: r² − r − 1 = 0 in ℚ
  -- (r : K)² − (r : K) − 1 = 0 by substituting hr into hphi_eq
  have hK_eq : (algebraMap ℚ K r) ^ 2 - algebraMap ℚ K r - 1 = 0 := hr ▸ hphi_eq
  -- Use that algebraMap ℚ K is a ring hom: (algebraMap r)² = algebraMap (r²), etc.
  have hq_eq : (r : ℚ) ^ 2 - r - 1 = 0 := by
    have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
    apply hinj
    push_cast [map_pow, map_sub, map_mul, map_one]
    exact hK_eq
  -- (2r−1)² = 5 ∈ ℚ² — contradicts irrationality of √5
  exact not_isSquare_five_rat (2 * r - 1) (by linear_combination 4 * hq_eq)

/-- `φ^(n+1)` is not rational in `K` for any `n : ℕ`. Proof: `φ^(n+1) = fib(n) + fib(n+1)·φ`;
if rational, then `φ = (r−fib n)/fib(n+1) ∈ ℚ`, contradicting `golden_not_algebraMap_rat`. -/
theorem golden_pow_succ_not_rational {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) (r : ℚ) : (1 + ζ + ζ ^ 4) ^ (n + 1) ≠ algebraMap ℚ K r := by
  intro hr
  rw [golden_pow_succ_fib_coeff hζ n] at hr
  -- fib(n+1) ≠ 0 in K (char 0, fib(n+1) ≥ 1)
  have hfib_pos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos n)
  have hfib_ne : (Nat.fib (n + 1) : K) ≠ 0 := by exact_mod_cast hfib_pos.ne'
  -- fib(n) + fib(n+1)·φ = algebraMap r
  -- So fib(n+1)·φ = algebraMap r − fib(n)
  have heq : (Nat.fib (n + 1) : K) * (1 + ζ + ζ ^ 4) =
      algebraMap ℚ K r - (Nat.fib n : K) := by linear_combination hr
  -- Divide: φ = (r − fib n) / fib(n+1) in K, and this equals algebraMap of a rational
  have hphi_rat : (1 + ζ + ζ ^ 4) = algebraMap ℚ K ((r - Nat.fib n) / Nat.fib (n + 1)) := by
    have hmap : algebraMap ℚ K ((r - ↑(Nat.fib n)) / ↑(Nat.fib (n + 1))) =
        (algebraMap ℚ K r - ↑(Nat.fib n : K)) / ↑(Nat.fib (n + 1) : K) := by
      rw [map_div₀, map_sub, map_natCast, map_natCast]
    rw [hmap]
    -- φ = (algebraMap r − fib n) / fib(n+1) follows from fib(n+1)·φ = algebraMap r − fib n
    rw [eq_div_iff hfib_ne]
    linear_combination heq
  exact golden_not_algebraMap_rat hζ _ hphi_rat

/-- `φ^n` is rational in `K` iff `n = 0`. -/
theorem golden_pow_rational_iff_zero {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (∃ r : ℚ, (1 + ζ + ζ ^ 4) ^ n = algebraMap ℚ K r) ↔ n = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    cases n with
    | zero => rfl
    | succ m => exact absurd hr (golden_pow_succ_not_rational hζ m r)
  · rintro rfl; exact ⟨1, by simp⟩

/-! ## Tier 2: Fifth-power extraction -/

/-- If `5 ∣ n`, write `n = 5m` and exhibit `φ^n = (φ^m)^5`. -/
theorem golden_kummer_five_power {ζ : K} {n : ℕ} (h5 : 5 ∣ n) :
    ∃ w : K, (1 + ζ + ζ ^ 4) ^ n = w ^ 5 := by
  obtain ⟨m, rfl⟩ := h5
  exact ⟨(1 + ζ + ζ ^ 4) ^ m, by rw [← pow_mul, mul_comm]⟩

/-! ## Tier 2: Dual-number ↔ Fibonacci agreement mod 5 (sorry'd) -/

/-- `((3+ε)^n).snd = (Nat.fib n : ZMod 5)` in `𝔽₅[ε] = DualNumber (ZMod 5)`.

Both sides vanish iff `5 ∣ n` (by `golden_dual_rational_iff` and `five_dvd_fib_iff`), and
agree for `n = 0, 1, 2, 3, 4` (by computation). However, proving the EQUALITY (not just the
same zero-set) requires verifying `n · 3^(n−1) ≡ fib n (mod 5)` for all `n`. The cleanest
approach is a periodicity argument (Pisano period for 5 is 20): prove the relation holds for
`n < 20` by `decide`, then show both sides have period 20 in ZMod 5.

This is a secondary quantitative refinement of the engine; the Kummer argument only needs the
ZERO-SET characterization (`five_dvd_fib_mod5`), not the pointwise equality. -/
theorem dual_snd_eq_fib_mod5 (n : ℕ) :
    ((inl (3 : ZMod 5) + ε) ^ n).snd = (Nat.fib n : ZMod 5) := by
  set x : DualNumber (ZMod 5) := inl 3 + ε
  -- x² = x + 1 proved component-wise (TrivSqZeroExt has no DecidableEq for decide)
  have hx_sq : x ^ 2 = x + 1 := by
    simp only [x, sq]
    ext
    · -- fst: 3*3 = 3+1 in ZMod 5 (both = 4)
      simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
            TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_one]
      decide
    · -- snd: 3*1 + 1*3 = 1+0 in ZMod 5 (both = 1); op_smul_eq_smul is @[simp]
      simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
            TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one, smul_eq_mul]
      decide
  have hx_snd : x.snd = 1 := by
    simp [x, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr]
  -- CommRing Fibonacci identity: x^(k+1) = fib(k) + fib(k+1)*x
  have pow_fib : ∀ k : ℕ, x ^ (k + 1) =
      (Nat.fib k : DualNumber (ZMod 5)) + (Nat.fib (k + 1) : DualNumber (ZMod 5)) * x := by
    intro k
    induction k with
    | zero => simp [Nat.fib_zero, Nat.fib_one]
    | succ m ih =>
      -- m+1+1 = m+2; fib_add_two matches syntactically only fib(n+2); cast ℕ→ZMod5→DualNumber
      -- is a double chain norm_cast can't handle directly, so we rewrite manually
      have hfib : (Nat.fib (m + 1 + 1) : DualNumber (ZMod 5)) =
          (Nat.fib m : DualNumber (ZMod 5)) + (Nat.fib (m + 1) : DualNumber (ZMod 5)) := by
        have h2 : m + 1 + 1 = m + 2 := rfl
        have hN : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
        rw [h2, hN, Nat.cast_add]
      rw [pow_succ, ih, hfib]
      push_cast
      linear_combination (↑(Nat.fib (m + 1)) : DualNumber (ZMod 5)) * hx_sq
  -- Extract snd: (x^n).snd = fib(n)
  cases n with
  | zero => simp [Nat.fib_zero, TrivSqZeroExt.snd_one]
  | succ k =>
    rw [pow_fib k, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_natCast, zero_add,
        show (Nat.fib (k + 1) : DualNumber (ZMod 5)) =
             inl (Nat.fib (k + 1) : ZMod 5) from (TrivSqZeroExt.inl_natCast _).symm,
        TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul, hx_snd,
        smul_eq_mul, mul_one]

/-! ## Tier 3: Transfer lemmas for fundamental unit -/

/-- Integer linear independence of `{1, goldenRatio}` over `ℤ` in `ℝ`:
if `(a:ℝ) + b·φ = (c:ℝ) + d·φ` with `a b c d : ℤ`, then `a = c` and `b = d`.
Proof: if `b ≠ d` then `goldenRatio = (c-a)/(b-d) ∈ ℚ`, so `x²-x-1` has a rational root,
giving `5 ∈ ℚ²`, contradicting `not_isSquare_five_rat`. -/
private lemma int_lin_indep_goldenRatio {a b c d : ℤ}
    (h : (a : ℝ) + b * Real.goldenRatio = c + d * Real.goldenRatio) : a = c ∧ b = d := by
  have hgr_sq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    BealFundamentalUnitPell.goldenRatio_sq_eq
  rcases eq_or_ne b d with rfl | hbd
  · exact ⟨by exact_mod_cast (by linarith : (a : ℝ) = c), rfl⟩
  · exfalso
    have heq : ((b : ℝ) - d) * Real.goldenRatio = c - a := by push_cast at h ⊢; linarith
    -- Key: (b-d)²·gr = (c-a)·(b-d), so (c-a)² = (c-a)·(b-d) + (b-d)²
    have hmul : (b - d : ℝ) ^ 2 * Real.goldenRatio = (c - a : ℝ) * (b - d) := by
      rw [sq, mul_assoc, heq]; ring
    have h4 : (c - a : ℝ) ^ 2 - (c - a) * (b - d) - (b - d) ^ 2 = 0 := by
      have h1 : (c - a : ℝ) ^ 2 = (b - d : ℝ) ^ 2 * Real.goldenRatio ^ 2 := by
        rw [← heq]; ring
      rw [hgr_sq, mul_add, mul_one] at h1
      linarith [h1, hmul]
    -- Discriminant: (2·(c-a) - (b-d))² = 5·(b-d)²
    have h5 : (2 * (c - a) - (b - d) : ℤ) ^ 2 = 5 * (b - d : ℤ) ^ 2 := by
      have h4' : (c - a : ℤ) ^ 2 - (c - a) * (b - d) - (b - d) ^ 2 = 0 := by exact_mod_cast h4
      nlinarith [h4', sq_nonneg (2 * (c - a) - (b - d) : ℤ)]
    have hbd_ne_z : b - d ≠ 0 := sub_ne_zero.mpr hbd
    exact (not_isSquare_five_rat (((2 * (c - a) - (b - d) : ℤ) : ℚ) / ((b - d : ℤ) : ℚ))) (by
      rw [div_pow, div_eq_iff (by exact_mod_cast pow_ne_zero 2 hbd_ne_z)]
      exact_mod_cast h5)

/-- For every `n : ℤ`, there exist integers `a_n b_n` such that `goldenRatio^n = a_n + b_n·φ`
in `ℝ` **and** `(1+ζ+ζ⁴)^n = a_n + b_n·(1+ζ+ζ⁴)` in `K` — the same integer pair works
in both rings, since both elements satisfy `x²=x+1` and `x·(x-1)=1`. -/
private lemma golden_int_repr {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℤ) :
    ∃ (a b : ℤ),
      (Real.goldenRatio : ℝ) ^ n = (a : ℝ) + b * Real.goldenRatio ∧
      (1 + ζ + ζ ^ 4 : K) ^ n = (a : K) + b * (1 + ζ + ζ ^ 4) := by
  have hgr_sq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    BealFundamentalUnitPell.goldenRatio_sq_eq
  have hgr_ne : Real.goldenRatio ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one BealFundamentalUnitPell.goldenRatio_gt_one)
  have hgr_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := BealFundamentalUnitPell.phi_inv_eq
  have hφ_sq : (1 + ζ + ζ ^ 4 : K) ^ 2 - (1 + ζ + ζ ^ 4) - 1 = 0 := golden_ratio_eq hζ
  have hφ_ne : (1 + ζ + ζ ^ 4 : K) ≠ 0 := by
    intro heq; have := golden_ratio_mul_inv hζ; simp [heq] at this
  have hφ_inv : (1 + ζ + ζ ^ 4 : K)⁻¹ = (1 + ζ + ζ ^ 4) - 1 := by
    have h2 : (1 + ζ + ζ ^ 4 : K) * ((1 + ζ + ζ ^ 4) - 1) = 1 := by
      linear_combination golden_ratio_mul_inv hζ
    exact (mul_left_cancel₀ hφ_ne (h2.trans (mul_inv_cancel₀ hφ_ne).symm)).symm
  induction n using Int.induction_on with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, hrR, hrK⟩ := ih
    refine ⟨b, a + b, ?_, ?_⟩
    · rw [zpow_add₀ hgr_ne, hrR, zpow_one]; push_cast; linear_combination (b : ℝ) * hgr_sq
    · rw [zpow_add₀ hφ_ne, hrK, zpow_one]; push_cast; linear_combination (b : K) * hφ_sq
  | pred k ih =>
    obtain ⟨a, b, hrR, hrK⟩ := ih
    refine ⟨b - a, a, ?_, ?_⟩
    · rw [show -(k : ℤ) - 1 = -(k : ℤ) + -1 from by ring,
          zpow_add₀ hgr_ne, hrR, zpow_neg_one, hgr_inv]
      push_cast; linear_combination (b : ℝ) * hgr_sq
    · rw [show -(k : ℤ) - 1 = -(k : ℤ) + -1 from by ring,
          zpow_add₀ hφ_ne, hrK, zpow_neg_one, hφ_inv]
      push_cast; linear_combination (b : K) * hφ_sq

/-! ## Tier 3: Fundamental unit theorem -/

/-- Every unit `a + b·φ` of `ℤ[φ] = 𝓞(ℚ(√5))` with norm `a² + ab − b² = ±1` equals `±φⁿ`
for some `n : ℤ`.

**Proof strategy (transfer from ℝ):**
1. Apply `BealFundamentalUnitPell.beal_fundamental_unit_sqrt5` to get `n` from the ℝ version.
2. Use `golden_int_repr` to get integers `a_n, b_n` with `goldenRatio^n = a_n + b_n·goldenRatio`
   AND `(1+ζ+ζ⁴)^n = a_n + b_n·(1+ζ+ζ⁴)` (same pair, different rings, same `x²=x+1`).
3. Apply `int_lin_indep_goldenRatio` to extract `a = ±a_n`, `b = ±b_n` from the ℝ equality.
4. Conclude `a + b·(1+ζ+ζ⁴) = ±(a_n + b_n·(1+ζ+ζ⁴)) = ±(1+ζ+ζ⁴)^n`. -/
theorem beal_fundamental_unit_sqrt5_statement {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ∀ (a b : ℤ),
      (a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1) →
      ∃ n : ℤ, ((a : K) + b * (1 + ζ + ζ ^ 4) = (1 + ζ + ζ ^ 4) ^ n ∨
                (a : K) + b * (1 + ζ + ζ ^ 4) = -((1 + ζ + ζ ^ 4) ^ n)) := by
  intro a b hN
  -- Step 1: get n from the ℝ fundamental unit theorem
  obtain ⟨n, hn⟩ := BealFundamentalUnitPell.beal_fundamental_unit_sqrt5 a b hN
  -- Step 2: integer Fibonacci coords valid in both ℝ and K
  obtain ⟨a_n, b_n, hrR, hrK⟩ := golden_int_repr hζ n
  exact ⟨n, by
    rcases hn with h | h
    · -- h : (a:ℝ) + b*gr = gr^n = a_n + b_n*gr → a = a_n, b = b_n
      obtain ⟨ha, hb⟩ := int_lin_indep_goldenRatio (h.trans hrR)
      left
      conv_lhs => rw [show (a : K) = a_n from by exact_mod_cast ha,
                      show (b : K) = b_n from by exact_mod_cast hb]
      exact hrK.symm
    · -- h : (a:ℝ) + b*gr = -(gr^n) = (-a_n) + (-b_n)*gr → a = -a_n, b = -b_n
      have hneg : -(Real.goldenRatio ^ n) = ((-a_n : ℤ) : ℝ) + (-b_n : ℤ) * Real.goldenRatio := by
        rw [hrR]; push_cast; ring
      obtain ⟨ha, hb⟩ := int_lin_indep_goldenRatio (h.trans hneg)
      right
      conv_lhs => rw [show (a : K) = -a_n from by exact_mod_cast ha,
                      show (b : K) = -b_n from by exact_mod_cast hb]
      rw [hrK]; push_cast; ring⟩

end BealFundamentalUnit

/-! ## Unit congruence: every `ℤ[φ]`-unit is congruent to a rational integer mod λ² -/

namespace BealFundamentalUnit

/-- **Every unit of `ℤ[φ]` is congruent to a rational integer modulo `λ²`.**

For any `a, b : ℤ` with norm `a² + ab - b² = ±1` (i.e., `a + b·φ ∈ (ℤ[φ])ˣ`), there exists
a rational integer `r : ℤ` and `c : K` such that `(a + b·φ) - r = (1-ζ)² · c`.

**Proof**: By `beal_fundamental_unit_sqrt5_statement`, `a + b·φ = ±φⁿ` for some `n : ℤ`.
By `phi_zpow_rat_cong`, `φⁿ ≡ r (mod λ²)` for some `r : ℤ` (with `r = 3ⁿ` if `n ≥ 0`, or
`r = 2^{-n}` if `n < 0`). The sign flip for the `±` produces `±r` as the rational integer. -/
theorem unit_congruence_from_norm {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (a b : ℤ)
    (hN : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1) :
    ∃ (r : ℤ) (c : K), (a : K) + b * (1 + ζ + ζ ^ 4) - r = (1 - ζ) ^ 2 * c := by
  obtain ⟨n, hn⟩ := beal_fundamental_unit_sqrt5_statement hζ a b hN
  obtain ⟨r, c, hrc⟩ := BealLambdaCongruence.phi_zpow_rat_cong hζ n
  rcases hn with h | h
  · -- (a:K)+b*φ = φ^n ≡ r (mod λ²)
    exact ⟨r, c, by rw [h]; exact hrc⟩
  · -- (a:K)+b*φ = -φ^n ≡ -r (mod λ²)
    exact ⟨-r, -c, by rw [h]; push_cast; linear_combination -hrc⟩

end BealFundamentalUnit

-- Axiom check: none of the proved theorems should use sorry
section AxiomCheck
#print axioms BealFundamentalUnit.fib_pos_of_pos
#print axioms BealFundamentalUnit.fib_ne_zero_of_pos
#print axioms BealFundamentalUnit.five_dvd_fib_mod5
#print axioms BealFundamentalUnit.golden_fib_coeff_mod5_zero_iff
#print axioms BealFundamentalUnit.golden_pow_succ_fib_coeff
#print axioms BealFundamentalUnit.golden_not_algebraMap_rat
#print axioms BealFundamentalUnit.golden_pow_succ_not_rational
#print axioms BealFundamentalUnit.golden_pow_rational_iff_zero
#print axioms BealFundamentalUnit.golden_kummer_five_power
#print axioms BealFundamentalUnit.beal_fundamental_unit_sqrt5_statement
end AxiomCheck
