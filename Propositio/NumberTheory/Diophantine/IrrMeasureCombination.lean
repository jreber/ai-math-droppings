import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# From a sequence of small integer linear forms to an irrationality measure

This is the reusable analytic engine that converts an explicit family of good rational
approximations (e.g. produced by a Padé / Legendre-integral construction) into an effective
irrationality measure.  It is construction-agnostic: feed it integer sequences `aₙ, bₙ` with
`aₙθ − bₙ` small and nonzero and `aₙ` of controlled size, and it returns a lower bound
`|θ − p/q| ≥ c/qᵘ`.

The file is organized bottom-up so the elementary atoms are independently useful:
* `three_term_identity` — the algebraic core `a·p − b·q = L·q − a·(q·θ − p)` (`L = aθ − b`).
* `linform_lower_atom` — one nonzero integer form gives `|θ − p/q| ≥ (1 − |L|·q)/(q·|a|)`.
* `consecutive_nonvanishing` — the determinant condition `aₙbₙ₊₁ ≠ aₙ₊₁bₙ` forces at least one
  of two consecutive forms `aₙp − bₙq`, `aₙ₊₁p − bₙ₊₁q` to be nonzero.
-/

namespace IrrMeasureCombination

open Real

/-- **Three-term identity.**  With `L = a·θ − b`, the integer `a·p − b·q` equals
`L·q − a·(q·θ − p)` as a real number. -/
theorem three_term_identity (θ : ℝ) (a b p q : ℤ) :
    ((a * p - b * q : ℤ) : ℝ) = (a * θ - b) * q - a * (q * θ - p) := by
  push_cast
  ring

/-- **One-form lower bound.**  If the integer linear form `a·p − b·q` is nonzero and `a ≠ 0`,
then `|q·θ − p| ≥ (1 − |L|·|q|)/|a|` where `L = a·θ − b`.  (Used with `|L|·|q| < 1`.) -/
theorem linform_lower_atom (θ : ℝ) (a b p q : ℤ)
    (hne : a * p - b * q ≠ 0) :
    (1 : ℝ) - |(a : ℝ) * θ - b| * |(q : ℝ)| ≤ |(a : ℝ)| * |(q : ℝ) * θ - p| := by
  set L : ℝ := (a : ℝ) * θ - b with hL
  -- `a·(q·θ − p) = L·q − (a·p − b·q)`.
  have hid : (a : ℝ) * ((q : ℝ) * θ - p) = L * q - ((a * p - b * q : ℤ) : ℝ) := by
    rw [three_term_identity θ a b p q]; ring
  have hint1 : (1 : ℝ) ≤ |((a * p - b * q : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  have hXY : |(a : ℝ) * ((q : ℝ) * θ - p)| = |L * (q : ℝ) - ((a * p - b * q : ℤ) : ℝ)| := by
    rw [hid]
  calc (1 : ℝ) - |L| * |(q : ℝ)|
      ≤ |((a * p - b * q : ℤ) : ℝ)| - |L * (q : ℝ)| := by
        rw [abs_mul]; linarith [hint1]
    _ ≤ |L * (q : ℝ) - ((a * p - b * q : ℤ) : ℝ)| := by
        have h := abs_sub_abs_le_abs_sub ((a * p - b * q : ℤ) : ℝ) (L * (q : ℝ))
        rw [abs_sub_comm ((a * p - b * q : ℤ) : ℝ) (L * (q : ℝ))] at h
        linarith [h]
    _ = |(a : ℝ) * ((q : ℝ) * θ - p)| := hXY.symm
    _ = |(a : ℝ)| * |(q : ℝ) * θ - p| := by rw [abs_mul]

/-- **Consecutive non-vanishing.**  If `aₙ·bₙ₊₁ ≠ aₙ₊₁·bₙ` (consecutive forms linearly
independent) then for any `p, q` with `q ≠ 0`, the two integer forms `a₀p − b₀q` and
`a₁p − b₁q` cannot both vanish. -/
theorem consecutive_nonvanishing (a₀ b₀ a₁ b₁ p q : ℤ) (hq : q ≠ 0)
    (hdet : a₀ * b₁ ≠ a₁ * b₀)
    (h0 : a₀ * p - b₀ * q = 0) (h1 : a₁ * p - b₁ * q = 0) : False := by
  -- a₀p = b₀q and a₁p = b₁q ⟹ a₀b₁q = a₁b₀q ⟹ (q≠0) a₀b₁ = a₁b₀.
  apply hdet
  have e0 : a₀ * p = b₀ * q := by linarith
  have e1 : a₁ * p = b₁ * q := by linarith
  have hkey : a₀ * (b₁ * q) = a₁ * (b₀ * q) := by rw [← e1, ← e0]; ring
  have hqz : (a₀ * b₁ - a₁ * b₀) * q = 0 := by linear_combination hkey
  rcases mul_eq_zero.mp hqz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hq

/-- **Index selection.**  With `s = log Q / log ρ⁻¹`, for `q` with `2Aq ≥ 1` there is an index
`n` whose form-size `A·ρⁿ` is `≤ 1/(2q)` and whose denominator factor `Qⁿ` is `≤ Q·(2A)ˢ·qˢ`. -/
theorem exists_good_index (A ρ Q : ℝ) (hA : 0 < A) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hQ : 1 < Q) (q : ℝ) (hAq : 1 ≤ 2 * A * q) :
    ∃ n : ℕ, A * ρ ^ n ≤ 1 / (2 * q) ∧
      (Q : ℝ) ^ n ≤ Q * (2 * A) ^ (Real.log Q / Real.log ρ⁻¹)
          * q ^ (Real.log Q / Real.log ρ⁻¹) := by
  have hq0 : 0 < q := by nlinarith [hA]
  have hAq0 : 0 < 2 * A * q := by positivity
  have hinv1 : 1 < ρ⁻¹ := by
    rw [one_lt_inv_iff₀]; exact ⟨hρ0, hρ1⟩
  set L1 : ℝ := Real.log ρ⁻¹ with hL1
  have hL1pos : 0 < L1 := Real.log_pos hinv1
  have hlogρ : Real.log ρ = -L1 := by rw [hL1, Real.log_inv]; ring
  set s : ℝ := Real.log Q / L1 with hs
  have hlogQpos : 0 < Real.log Q := Real.log_pos hQ
  have hspos : 0 < s := by rw [hs]; positivity
  -- x ≥ 0 since 2Aq ≥ 1
  have hlog2Aq : 0 ≤ Real.log (2 * A * q) := Real.log_nonneg hAq
  set x : ℝ := Real.log (2 * A * q) / L1 with hx
  have hxnn : 0 ≤ x := by rw [hx]; positivity
  refine ⟨⌈x⌉₊, ?_, ?_⟩
  · -- A·ρⁿ ≤ 1/(2q)
    have hxle : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hρn : (ρ : ℝ) ^ (⌈x⌉₊ : ℕ) ≤ ρ ^ x := by
      rw [← Real.rpow_natCast ρ ⌈x⌉₊]
      exact Real.rpow_le_rpow_of_exponent_ge hρ0 (le_of_lt hρ1) hxle
    have hρx : (ρ : ℝ) ^ x = (2 * A * q)⁻¹ := by
      rw [Real.rpow_def_of_pos hρ0, hlogρ, hx]
      rw [show -L1 * (Real.log (2 * A * q) / L1) = -(Real.log (2 * A * q)) by
        field_simp]
      rw [Real.exp_neg, Real.exp_log hAq0]
    have : (ρ : ℝ) ^ (⌈x⌉₊ : ℕ) ≤ (2 * A * q)⁻¹ := by rw [← hρx]; exact hρn
    calc A * ρ ^ (⌈x⌉₊ : ℕ) ≤ A * (2 * A * q)⁻¹ := by
          apply mul_le_mul_of_nonneg_left this (le_of_lt hA)
      _ = 1 / (2 * q) := by field_simp
  · -- Qⁿ ≤ Q·(2A)ˢ·qˢ
    have hxlt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxnn
    have hQn : (Q : ℝ) ^ (⌈x⌉₊ : ℕ) ≤ Q ^ (x + 1) := by
      rw [← Real.rpow_natCast Q ⌈x⌉₊]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hQ) (le_of_lt hxlt)
    have hQx : (Q : ℝ) ^ x = (2 * A) ^ s * q ^ s := by
      rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < Q)]
      have : Real.log Q * x = Real.log (2 * A * q) * s := by
        rw [hx, hs]; field_simp
      rw [this, ← Real.rpow_def_of_pos hAq0,
        show (2 * A * q) = (2 * A) * q by ring,
        Real.mul_rpow (by positivity) (le_of_lt hq0)]
    calc (Q : ℝ) ^ (⌈x⌉₊ : ℕ) ≤ Q ^ (x + 1) := hQn
      _ = Q ^ x * Q := by rw [Real.rpow_add (by positivity), Real.rpow_one]
      _ = (2 * A) ^ s * q ^ s * Q := by rw [hQx]
      _ = Q * (2 * A) ^ s * q ^ s := by ring

/-- **The combination criterion.**  Given integer sequences `aₙ > 0`, `bₙ` with the linear
forms `aₙθ − bₙ` small (`≤ A·ρⁿ`, `0<ρ<1`), `aₙ` controlled (`≤ B·Qⁿ`, `Q>1`), and the Padé
determinant condition `aₙbₙ₊₁ ≠ aₙ₊₁bₙ`, the real `θ` has effective irrationality measure
`μ = 1 + log Q / log ρ⁻¹`:  there is `C > 0` with `|θ − p/q| ≥ C / qᵘ` for all `p` and all `q`
large enough that `2Aq ≥ 1`.

This is the construction-agnostic engine: any Padé/Legendre-integral family feeding it the
hypotheses yields a measure with no further analysis. -/
theorem irrationality_measure_le
    (θ : ℝ) (a b : ℕ → ℤ) (A B ρ Q : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hQ : 1 < Q)
    (hsmall : ∀ n, |(a n : ℝ) * θ - b n| ≤ A * ρ ^ n)
    (hapos : ∀ n, 0 < a n)
    (hden : ∀ n, (a n : ℝ) ≤ B * Q ^ n)
    (hdet : ∀ n, a n * b (n + 1) ≠ a (n + 1) * b n) :
    ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
      C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |θ - (p : ℝ) / q| := by
  set s : ℝ := Real.log Q / Real.log ρ⁻¹ with hs
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hspos : 0 < s := by
    rw [hs]
    have hinv1 : 1 < ρ⁻¹ := by rw [one_lt_inv_iff₀]; exact ⟨hρ0, hρ1⟩
    have hlρ : 0 < Real.log ρ⁻¹ := Real.log_pos hinv1
    exact div_pos (Real.log_pos hQ) hlρ
  refine ⟨1 / (2 * B * Q ^ 2 * (2 * A) ^ s), by positivity, ?_⟩
  intro p q hq1 hAq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨n, hi, hii⟩ := exists_good_index A ρ Q hA hρ0 hρ1 hQ q hAq
  set M : ℝ := B * Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s with hM
  have hTs : (0 : ℝ) ≤ (2 * A) ^ s := Real.rpow_nonneg (by positivity) s
  have hUs : (0 : ℝ) ≤ (q : ℝ) ^ s := Real.rpow_nonneg (le_of_lt hq0) s
  -- Core step at a fixed working index `m`.
  have inner : ∀ m : ℕ, |(a m : ℝ) * θ - b m| ≤ 1 / (2 * q) → (a m : ℝ) ≤ M →
      a m * p - b m * q ≠ 0 →
      1 / (2 * B * Q ^ 2 * (2 * A) ^ s) / (q : ℝ) ^ (1 + s) ≤ |θ - (p : ℝ) / q| := by
    intro m hLm haM hne
    have ham_pos : (0 : ℝ) < a m := by exact_mod_cast hapos m
    have hatom := linform_lower_atom θ (a m) (b m) p q hne
    rw [abs_of_pos hq0, abs_of_pos ham_pos] at hatom
    -- `1/2 ≤ a_m · |qθ − p|`
    have hhalf : (1 : ℝ) / 2 ≤ (a m : ℝ) * |(q : ℝ) * θ - p| := by
      have hmul : |(a m : ℝ) * θ - b m| * (q : ℝ) ≤ 1 / (2 * q) * q :=
        mul_le_mul_of_nonneg_right hLm (le_of_lt hq0)
      have hq2 : 1 / (2 * q) * (q : ℝ) = 1 / 2 := by field_simp
      rw [hq2] at hmul; linarith [hatom, hmul]
    -- `|qθ − p| ≥ 1/(2 a_m)`
    have hlf : (1 : ℝ) / (2 * a m) ≤ |(q : ℝ) * θ - p| := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hhalf]
    -- `|θ − p/q| = |qθ − p| / q`
    have heq : θ - (p : ℝ) / q = ((q : ℝ) * θ - p) / q := by field_simp
    rw [heq, abs_div, abs_of_pos hq0]
    -- it remains to bound the target by `(1/(2 a_m))/q`, then use `hlf`.
    have hqs : (q : ℝ) ^ (1 + s) = (q : ℝ) * (q : ℝ) ^ s := by
      rw [Real.rpow_add hq0, Real.rpow_one]
    have hkey : 1 / (2 * B * Q ^ 2 * (2 * A) ^ s) / (q : ℝ) ^ (1 + s)
        ≤ 1 / (2 * a m) / q := by
      rw [div_div, div_div, hqs]
      apply one_div_le_one_div_of_le (by positivity)
      have haMq : (a m : ℝ) * q ≤ M * q := mul_le_mul_of_nonneg_right haM (le_of_lt hq0)
      have hXeq : 2 * B * Q ^ 2 * (2 * A) ^ s * ((q : ℝ) * (q : ℝ) ^ s) = 2 * M * q := by
        rw [hM]; ring
      nlinarith [haMq, hXeq]
    refine le_trans hkey ?_
    exact div_le_div_of_nonneg_right hlf (le_of_lt hq0)
  -- Choose the working index: `n`, or `n+1` if the form vanishes at `n`.
  have hρn_nn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg (le_of_lt hρ0) n
  by_cases h0 : a n * p - b n * q = 0
  · -- forms vanish at `n`; use `n+1`
    have hqne : q ≠ 0 := by omega
    have hne1 : a (n + 1) * p - b (n + 1) * q ≠ 0 := fun h1 =>
      consecutive_nonvanishing (a n) (b n) (a (n + 1)) (b (n + 1)) p q hqne (hdet n) h0 h1
    refine inner (n + 1) ?_ ?_ hne1
    · have hsmle : A * ρ ^ (n + 1) ≤ A * ρ ^ n := by
        rw [pow_succ]; nlinarith [hρn_nn, hA, hρ1, mul_nonneg (le_of_lt hA) hρn_nn]
      linarith [hsmall (n + 1), hsmle, hi]
    · have hpow : (Q : ℝ) ^ (n + 1) ≤ Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s := by
        rw [pow_succ, sq]
        nlinarith [hii, hQ0, hTs, hUs]
      calc (a (n + 1) : ℝ) ≤ B * Q ^ (n + 1) := hden (n + 1)
        _ ≤ B * (Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s) := by nlinarith [hpow, hB]
        _ = M := by rw [hM]; ring
  · -- form nonzero at `n`
    refine inner n ?_ ?_ h0
    · linarith [hsmall n, hi]
    · have hle : (Q : ℝ) ^ n ≤ Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s := by
        have hQsq : (Q : ℝ) ≤ Q ^ 2 := by nlinarith [hQ]
        nlinarith [hii, hQ0, hTs, hUs, hQsq, mul_nonneg hTs hUs]
      calc (a n : ℝ) ≤ B * Q ^ n := hden n
        _ ≤ B * (Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s) := by nlinarith [hle, hB]
        _ = M := by rw [hM]; ring

/-- **Explicit-constant form of `irrationality_measure_le`** (de-existential-ized).  Same hypotheses,
but the constant is exposed as `C = 1/(2·B·Q²·(2A)^s)` with `s = log Q / log ρ⁻¹`, so downstream
normalizations can bound `1/C` and absorb a tiny `C` into a larger exponent.  Proof is identical to
`irrationality_measure_le` minus the `∃`-packaging. -/
theorem irrationality_measure_le_const
    (θ : ℝ) (a b : ℕ → ℤ) (A B ρ Q : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hQ : 1 < Q)
    (hsmall : ∀ n, |(a n : ℝ) * θ - b n| ≤ A * ρ ^ n)
    (hapos : ∀ n, 0 < a n)
    (hden : ∀ n, (a n : ℝ) ≤ B * Q ^ n)
    (hdet : ∀ n, a n * b (n + 1) ≠ a (n + 1) * b n) :
    ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
      1 / (2 * B * Q ^ 2 * (2 * A) ^ (Real.log Q / Real.log ρ⁻¹))
        / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |θ - (p : ℝ) / q| := by
  set s : ℝ := Real.log Q / Real.log ρ⁻¹ with hs
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hspos : 0 < s := by
    rw [hs]
    have hinv1 : 1 < ρ⁻¹ := by rw [one_lt_inv_iff₀]; exact ⟨hρ0, hρ1⟩
    have hlρ : 0 < Real.log ρ⁻¹ := Real.log_pos hinv1
    exact div_pos (Real.log_pos hQ) hlρ
  intro p q hq1 hAq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨n, hi, hii⟩ := exists_good_index A ρ Q hA hρ0 hρ1 hQ q hAq
  set M : ℝ := B * Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s with hM
  have hTs : (0 : ℝ) ≤ (2 * A) ^ s := Real.rpow_nonneg (by positivity) s
  have hUs : (0 : ℝ) ≤ (q : ℝ) ^ s := Real.rpow_nonneg (le_of_lt hq0) s
  have inner : ∀ m : ℕ, |(a m : ℝ) * θ - b m| ≤ 1 / (2 * q) → (a m : ℝ) ≤ M →
      a m * p - b m * q ≠ 0 →
      1 / (2 * B * Q ^ 2 * (2 * A) ^ s) / (q : ℝ) ^ (1 + s) ≤ |θ - (p : ℝ) / q| := by
    intro m hLm haM hne
    have ham_pos : (0 : ℝ) < a m := by exact_mod_cast hapos m
    have hatom := linform_lower_atom θ (a m) (b m) p q hne
    rw [abs_of_pos hq0, abs_of_pos ham_pos] at hatom
    have hhalf : (1 : ℝ) / 2 ≤ (a m : ℝ) * |(q : ℝ) * θ - p| := by
      have hmul : |(a m : ℝ) * θ - b m| * (q : ℝ) ≤ 1 / (2 * q) * q :=
        mul_le_mul_of_nonneg_right hLm (le_of_lt hq0)
      have hq2 : 1 / (2 * q) * (q : ℝ) = 1 / 2 := by field_simp
      rw [hq2] at hmul; linarith [hatom, hmul]
    have hlf : (1 : ℝ) / (2 * a m) ≤ |(q : ℝ) * θ - p| := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hhalf]
    have heq : θ - (p : ℝ) / q = ((q : ℝ) * θ - p) / q := by field_simp
    rw [heq, abs_div, abs_of_pos hq0]
    have hqs : (q : ℝ) ^ (1 + s) = (q : ℝ) * (q : ℝ) ^ s := by
      rw [Real.rpow_add hq0, Real.rpow_one]
    have hkey : 1 / (2 * B * Q ^ 2 * (2 * A) ^ s) / (q : ℝ) ^ (1 + s)
        ≤ 1 / (2 * a m) / q := by
      rw [div_div, div_div, hqs]
      apply one_div_le_one_div_of_le (by positivity)
      have haMq : (a m : ℝ) * q ≤ M * q := mul_le_mul_of_nonneg_right haM (le_of_lt hq0)
      have hXeq : 2 * B * Q ^ 2 * (2 * A) ^ s * ((q : ℝ) * (q : ℝ) ^ s) = 2 * M * q := by
        rw [hM]; ring
      nlinarith [haMq, hXeq]
    refine le_trans hkey ?_
    exact div_le_div_of_nonneg_right hlf (le_of_lt hq0)
  have hρn_nn : (0 : ℝ) ≤ ρ ^ n := pow_nonneg (le_of_lt hρ0) n
  by_cases h0 : a n * p - b n * q = 0
  · have hqne : q ≠ 0 := by omega
    have hne1 : a (n + 1) * p - b (n + 1) * q ≠ 0 := fun h1 =>
      consecutive_nonvanishing (a n) (b n) (a (n + 1)) (b (n + 1)) p q hqne (hdet n) h0 h1
    refine inner (n + 1) ?_ ?_ hne1
    · have hsmle : A * ρ ^ (n + 1) ≤ A * ρ ^ n := by
        rw [pow_succ]; nlinarith [hρn_nn, hA, hρ1, mul_nonneg (le_of_lt hA) hρn_nn]
      linarith [hsmall (n + 1), hsmle, hi]
    · have hpow : (Q : ℝ) ^ (n + 1) ≤ Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s := by
        rw [pow_succ, sq]
        nlinarith [hii, hQ0, hTs, hUs]
      calc (a (n + 1) : ℝ) ≤ B * Q ^ (n + 1) := hden (n + 1)
        _ ≤ B * (Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s) := by nlinarith [hpow, hB]
        _ = M := by rw [hM]; ring
  · refine inner n ?_ ?_ h0
    · linarith [hsmall n, hi]
    · have hle : (Q : ℝ) ^ n ≤ Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s := by
        have hQsq : (Q : ℝ) ≤ Q ^ 2 := by nlinarith [hQ]
        nlinarith [hii, hQ0, hTs, hUs, hQsq, mul_nonneg hTs hUs]
      calc (a n : ℝ) ≤ B * Q ^ n := hden n
        _ ≤ B * (Q ^ 2 * (2 * A) ^ s * (q : ℝ) ^ s) := by nlinarith [hle, hB]
        _ = M := by rw [hM]; ring

/-! ## Specialization to `log₂3`: reducing the wall to the two-log form construction -/

/-- **`log₂3` measure from two-log forms.**  This connects the engine to the *actual* number
behind the Collatz `PowGap` wall.  Feed it a Padé/Hermite family of small integer linear forms
`vₙ·log2 + wₙ·log3` (with `wₙ > 0` controlled and the determinant condition `wₙvₙ₊₁ ≠ wₙ₊₁vₙ`),
and it yields an effective irrationality measure of `log₂3 = Real.logb 2 3`:
`|log₂3 − p/q| ≥ C/qᵘ`, `μ = 1 + log Q / log ρ⁻¹`.

Key observation: `wₙ·log₂3 + vₙ = (vₙ·log2 + wₙ·log3)/log2`, so a small two-log form *is* a good
rational approximation `−vₙ/wₙ` to `log₂3` with denominator `wₙ` — exactly the 1-D input
`irrationality_measure_le` consumes (with `θ = log₂3`, `aₙ = wₙ`, `bₙ = −vₙ`, `A' = A/log2`).

**This is the precise residual frontier of Wall 1:** the *only* missing ingredient is the
construction of such forms (Rhin 1987 / Hermite–Padé simultaneous approximation to `log2, log3`,
giving `μ(log₂3) ≤ 8.616`); `LcmGrowthBound.log_lcmUpto_le_sharp` supplies their integer
denominators.  No further analytic glue is needed. -/
theorem logb23_measure_of_twolog_forms
    (v w : ℕ → ℤ) (A B ρ Q : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hQ : 1 < Q)
    (hsmall : ∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n)
    (hwpos : ∀ n, 0 < w n)
    (hwden : ∀ n, (w n : ℝ) ≤ B * Q ^ n)
    (hdet : ∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) :
    ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * (A / Real.log 2) * q →
      C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.logb 2 3 - (p : ℝ) / q| := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine irrationality_measure_le (Real.logb 2 3) w (fun n => -v n) (A / Real.log 2) B ρ Q
    (div_pos hA hlog2) hB hρ0 hρ1 hQ ?_ hwpos hwden ?_
  · -- small forms: |wₙ·log₂3 − (−vₙ)| = |vₙlog2 + wₙlog3|/log2 ≤ (A/log2)·ρⁿ
    intro n
    have hcast : ((fun m => -v m) n : ℤ) = -v n := rfl
    have heq : (w n : ℝ) * Real.logb 2 3 - (((fun m => -v m) n : ℤ) : ℝ)
        = ((v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3) / Real.log 2 := by
      rw [hcast, Real.logb]; push_cast; field_simp; ring
    rw [heq, abs_div, abs_of_pos hlog2, div_le_iff₀ hlog2]
    have hrhs : A / Real.log 2 * ρ ^ n * Real.log 2 = A * ρ ^ n := by field_simp
    rw [hrhs]; exact hsmall n
  · -- determinant: wₙ·(−vₙ₊₁) ≠ wₙ₊₁·(−vₙ)
    intro n hc
    exact hdet n (by linear_combination -hc)

/-- **Explicit-constant `log₂3` measure from two-log forms** (de-existential-ized
`logb23_measure_of_twolog_forms`).  Exposes `C = 1/(2·B·Q²·(2·(A/log2))^s)`, `s = log Q / log ρ⁻¹`,
so a downstream normalization can certify `1/C ≤ …` and absorb the (tiny) `C` into a larger exponent
en route to the Collatz `PowGap`. -/
theorem logb23_measure_of_twolog_forms_const
    (v w : ℕ → ℤ) (A B ρ Q : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hQ : 1 < Q)
    (hsmall : ∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n)
    (hwpos : ∀ n, 0 < w n)
    (hwden : ∀ n, (w n : ℝ) ≤ B * Q ^ n)
    (hdet : ∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) :
    ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * (A / Real.log 2) * q →
      1 / (2 * B * Q ^ 2 * (2 * (A / Real.log 2)) ^ (Real.log Q / Real.log ρ⁻¹))
        / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.logb 2 3 - (p : ℝ) / q| := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine irrationality_measure_le_const (Real.logb 2 3) w (fun n => -v n) (A / Real.log 2) B ρ Q
    (div_pos hA hlog2) hB hρ0 hρ1 hQ ?_ hwpos hwden ?_
  · intro n
    have hcast : ((fun m => -v m) n : ℤ) = -v n := rfl
    have heq : (w n : ℝ) * Real.logb 2 3 - (((fun m => -v m) n : ℤ) : ℝ)
        = ((v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3) / Real.log 2 := by
      rw [hcast, Real.logb]; push_cast; field_simp; ring
    rw [heq, abs_div, abs_of_pos hlog2, div_le_iff₀ hlog2]
    have hrhs : A / Real.log 2 * ρ ^ n * Real.log 2 = A * ρ ^ n := by field_simp
    rw [hrhs]; exact hsmall n
  · intro n hc
    exact hdet n (by linear_combination -hc)

end IrrMeasureCombination
