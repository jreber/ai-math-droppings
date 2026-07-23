import Propositio.NumberTheory.Collatz.PowGapMu
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Bridge: **any** explicit effective irrationality measure of `log₂3` ⟹ `LinFormGapLog23Mu μ`

`CollatzPowGapBaker.linFormGap_of_irrMeasure` bridges the *hardcoded* measure `IrrMeasureLog23`
(constant `1/40`, exponent `14`) to `LinFormGapLog23`.  But the formalizable `μ(log₂3)`
constructions (`conj-2026-06-23-R04`) emit measures with *different* constants/exponents and two
distinct **output shapes**:

* the 2-D pure-two-log engine (`IrrMeasureCombination.logb23_measure_of_twolog_forms`) and the
  textbook form give `|log₂3 − k/a| ≥ C / a^(m+1)`  (denominator height `a`);
* the 3-D linear-independence engine (`Log23MeasureRhin.log23_measure_of_3d_bound`, fed by the
  `{I,J}` weighted-diagonal system, `μ ≈ 5.76`) gives `|log₂3 − p/q| ≥ C / (q · max(|p|,q)^μ)`
  (height `max(|p|,q)`).

Thread E of the 2026-06-23 prize fan-out identified that **no file converted either shape into**
`CollatzPowGapMu.LinFormGapLog23Mu`, the input of the μ-agnostic `powGap_of_measure_exponent`.
This file supplies both, sharing one elementary core (`gap_core`):

* `linFormGapMu_of_measure`      — from the `C/a^(m+1)` shape;
* `linFormGapMu_of_measure_max`  — from the `C/(q·max(|p|,q)^m)` shape (uses the sub-threshold
  bound `k ≤ 2a` to fold `max(|k|,a) = k ≤ 2a` into the height `a`).

The core is a verbatim generalization of `linFormGap_of_irrMeasure` (`1/40 → C`, `14 → m+1`,
`80 → 2/C`): only `2^x ≥ 1 + x·log 2` (`Real.add_one_le_exp`) and `log 2 ≥ 1/2`
(`Real.one_sub_inv_le_log_of_pos`) — no transcendental constants.  A non-integer measure exponent
`μ` uses `m + 1 = ⌈μ⌉` (weaken `C/q^μ ≥ C/q^⌈μ⌉` since `q ≥ 1`); a tiny `C` uses a larger `m`
(the `2/C ≤ 100` slack is `norm_num`-checkable once `C` is explicit).  Chaining with
`CollatzPowGapMu.powGap_of_measure_exponent` closes the Collatz `PowGap` the instant any finite
measure of `log₂3` is formalized.
-/

namespace CollatzPowGapMeasureBridge

open CollatzPowGapMu

/-- **The elementary core.**  From `hmeas : C/a^(m+1) ≤ |log₂3 − k/a|` (with `a > 100`, `C > 0`,
`2/C ≤ 100`, `3^a < 2^k`), derive `3^a ≤ a^(m+1)·(2^k − 3^a)`. -/
private theorem gap_core' (C : ℝ) (m a k : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (ha : 100 < a) (h3k : 3 ^ a < 2 ^ k)
    (hmeas : C / (a : ℝ) ^ (m + 1) ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    (3 : ℝ) ^ a ≤ (a : ℝ) ^ (m + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hapos : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha100 : (100 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 100 ≤ a)
  have hane : (a : ℝ) ≠ 0 := ne_of_gt hapos
  set θ := Real.logb 2 3 with hθdef
  have hθpow : (2 : ℝ) ^ θ = 3 :=
    Real.rpow_logb h2pos (by norm_num) (by norm_num)
  have e3 : (3 : ℝ) ^ a = (2 : ℝ) ^ (θ * (a : ℝ)) := by
    rw [Real.rpow_mul h2pos.le, hθpow, Real.rpow_natCast]
  have h3apos : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  set x : ℝ := (k : ℝ) - θ * (a : ℝ) with hxdef
  have e2k : (2 : ℝ) ^ k = (3 : ℝ) ^ a * (2 : ℝ) ^ x := by
    have hk : (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ)) := (Real.rpow_natCast 2 k).symm
    rw [hk]
    have hsum : (k : ℝ) = θ * (a : ℝ) + x := by rw [hxdef]; ring
    rw [hsum, Real.rpow_add h2pos, ← e3]
  have hxpos : 0 < x := by
    have h3lt2 : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    rw [e3, ← Real.rpow_natCast 2 k] at h3lt2
    have hlt := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h3lt2
    rw [hxdef]; linarith
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos h2pos
    norm_num at this; linarith
  have hexp : (1 : ℝ) + x * Real.log 2 ≤ (2 : ℝ) ^ x := by
    have hdef : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) := Real.rpow_def_of_pos h2pos x
    rw [hdef]
    have := Real.add_one_le_exp (Real.log 2 * x)
    nlinarith [this]
  have hxa : |θ - (k : ℝ) / (a : ℝ)| = x / (a : ℝ) := by
    have he : θ - (k : ℝ) / (a : ℝ) = -(x / (a : ℝ)) := by
      rw [hxdef]; field_simp; ring
    rw [he, abs_neg, abs_of_pos (by positivity)]
  rw [hxa] at hmeas
  have hxlow : C / (a : ℝ) ^ m ≤ x := by
    have h1 : C / (a : ℝ) ^ (m + 1) * (a : ℝ) ≤ x / (a : ℝ) * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hmeas (le_of_lt hapos)
    have h2 : x / (a : ℝ) * (a : ℝ) = x := by field_simp
    have h3 : C / (a : ℝ) ^ (m + 1) * (a : ℝ) = C / (a : ℝ) ^ m := by
      rw [pow_succ]; field_simp
    rw [h2, h3] at h1; exact h1
  have hxbound : (1 : ℝ) / ((2 / C) * (a : ℝ) ^ m) ≤ (2 : ℝ) ^ x - 1 := by
    have c1 : x * Real.log 2 ≤ (2 : ℝ) ^ x - 1 := by linarith [hexp]
    have c2 : x * (1 / 2 : ℝ) ≤ x * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 (le_of_lt hxpos)
    have c3 : (C / (a : ℝ) ^ m) * (1 / 2) ≤ x * (1 / 2) :=
      mul_le_mul_of_nonneg_right hxlow (by norm_num)
    have c4 : (1 : ℝ) / ((2 / C) * (a : ℝ) ^ m) = (C / (a : ℝ) ^ m) * (1 / 2) := by
      have ham : (a : ℝ) ^ m ≠ 0 := by positivity
      have hCne : C ≠ 0 := ne_of_gt hC
      field_simp
    rw [c4]; linarith [c1, c2, c3]
  have hcpos : (0 : ℝ) < (2 / C) * (a : ℝ) ^ m :=
    mul_pos (div_pos (by norm_num) hC) (by positivity)
  have hbig : (3 : ℝ) ^ a / ((2 / C) * (a : ℝ) ^ m) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have hstep1 : (2 : ℝ) ^ k - (3 : ℝ) ^ a = (3 : ℝ) ^ a * ((2 : ℝ) ^ x - 1) := by
      rw [e2k]; ring
    rw [hstep1]
    have hmul : (3 : ℝ) ^ a * (1 / ((2 / C) * (a : ℝ) ^ m)) ≤ (3 : ℝ) ^ a * ((2 : ℝ) ^ x - 1) :=
      mul_le_mul_of_nonneg_left hxbound (le_of_lt h3apos)
    calc (3 : ℝ) ^ a / ((2 / C) * (a : ℝ) ^ m)
        = (3 : ℝ) ^ a * (1 / ((2 / C) * (a : ℝ) ^ m)) := by ring
      _ ≤ (3 : ℝ) ^ a * ((2 : ℝ) ^ x - 1) := hmul
  have hden : (2 / C) * (a : ℝ) ^ m ≤ (a : ℝ) ^ (m + 1) := by
    rw [pow_succ]
    have hle : (2 / C) ≤ (a : ℝ) := le_trans hCa ha100
    calc (2 / C) * (a : ℝ) ^ m ≤ (a : ℝ) * (a : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (a : ℝ) ^ m * (a : ℝ) := by ring
  have hfrombig : (3 : ℝ) ^ a ≤ (2 / C) * (a : ℝ) ^ m * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) :=
    (div_le_iff₀' hcpos).mp hbig
  have hchain : (2 / C) * (a : ℝ) ^ m * ((2 : ℝ) ^ k - (3 : ℝ) ^ a)
      ≤ (a : ℝ) ^ (m + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) :=
    mul_le_mul_of_nonneg_right hden hnn
  exact le_trans hfrombig hchain

/-- Reduce the rpow exponent `(m:ℝ)+1` to the nat power `m+1`. -/
private theorem rpow_exp_eq (a : ℕ) (m : ℕ) :
    (a : ℝ) ^ ((m : ℝ) + 1) = (a : ℝ) ^ (m + 1) := by
  rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Real.rpow_natCast (a : ℝ) (m + 1)

/-- **Bridge (denominator-height shape): `|log₂3 − k/a| ≥ C/a^(m+1)` ⟹ the bespoke gap.**

From the measure with denominator height `a` (any `C > 0` with `2/C ≤ 100`), derive
`LinFormGapLog23Mu (m+1)`.  This is the shape the 2-D pure-two-log engine and the textbook
irrationality measure emit. -/
theorem linFormGapMu_of_measure (C : ℝ) (m : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (h : ∀ (k a : ℕ), 100 < a →
        C / (a : ℝ) ^ (m + 1) ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    LinFormGapLog23Mu ((m : ℝ) + 1) := by
  intro a k ha h3k _h2k
  rw [rpow_exp_eq a m]
  exact gap_core' C m a k hC hCa ha h3k (h k a ha)

/-- **Bridge (max-height shape): `|log₂3 − p/q| ≥ C/(q·max(|p|,q)^m)` ⟹ the bespoke gap.**

This is the shape the 3-D linear-independence engine emits
(`Log23MeasureRhin.log23_measure_of_3d_bound`, fed by the `{I,J}` weighted-diagonal system).  In
the sub-threshold range `3^a < 2^k ≤ 2·3^a` the test `(p,q) = (k,a)` has `a < k ≤ 2a`, so
`max(|k|,a) = k ≤ 2a`, folding the height into `a` at the cost of a `2^m` in the constant: the
effective measure is `(C/2^m)/a^(m+1)`, requiring `2^(m+1)/C ≤ 100`.  Conclusion:
`LinFormGapLog23Mu (m+1)`. -/
theorem linFormGapMu_of_measure_max (C : ℝ) (m : ℕ) (hC : 0 < C)
    (hCa : (2 : ℝ) ^ (m + 1) / C ≤ 100)
    (h : ∀ (p q : ℤ), 1 ≤ q →
        C / ((q : ℝ) * (((max |p| q : ℤ) : ℝ)) ^ m) ≤ |Real.logb 2 3 - (p : ℝ) / (q : ℝ)|) :
    LinFormGapLog23Mu ((m : ℝ) + 1) := by
  intro a k ha h3k h2k
  rw [rpow_exp_eq a m]
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  -- a < k  (from 2^a ≤ 3^a < 2^k)
  have hak : a < k := by
    by_contra hle; push_neg at hle
    have hkk : (2 : ℕ) ^ k ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hle
    have haa : (2 : ℕ) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
    omega
  -- k ≤ 2a  (from 2^k ≤ 2·3^a < 2·4^a = 2^(2a+1))
  have hk2a : k ≤ 2 * a := by
    by_contra hlt; push_neg at hlt
    have h1 : (2 : ℕ) ^ (2 * a + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e4 : (4 : ℕ) ^ a = 2 ^ (2 * a) := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have h3lt4 : (3 : ℕ) ^ a < 4 ^ a := Nat.pow_lt_pow_left (by norm_num) (by omega)
    have e5 : (2 : ℕ) ^ (2 * a + 1) = 2 * 4 ^ a := by rw [e4, pow_succ]; ring
    omega
  -- the height `max(|k|,a)` collapses to `k`
  have hmaxeq : max |(k : ℤ)| (a : ℤ) = (k : ℤ) := by
    rw [abs_of_nonneg (by positivity)]
    exact max_eq_left (by exact_mod_cast (Nat.le_of_lt hak))
  have h1a : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast (by omega : 1 ≤ a)
  have hm := h (k : ℤ) (a : ℤ) h1a
  rw [hmaxeq] at hm
  push_cast at hm
  -- hm : C / ((a:ℝ) * (k:ℝ)^m) ≤ |log₂3 − k/a|
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hden_pos : (0 : ℝ) < (a : ℝ) * (k : ℝ) ^ m := by positivity
  -- fold k ≤ 2a into the height: (C/2^m)/a^(m+1) ≤ C/(a·k^m)
  have hkm : (k : ℝ) ^ m ≤ 2 ^ m * (a : ℝ) ^ m := by
    have hk2 : (k : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hk2a
    calc (k : ℝ) ^ m ≤ (2 * (a : ℝ)) ^ m := by gcongr
      _ = 2 ^ m * (a : ℝ) ^ m := by rw [mul_pow]
  have hak_m : (a : ℝ) * (k : ℝ) ^ m ≤ 2 ^ m * (a : ℝ) ^ (m + 1) := by
    calc (a : ℝ) * (k : ℝ) ^ m ≤ (a : ℝ) * (2 ^ m * (a : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left hkm (le_of_lt hapos)
      _ = 2 ^ m * (a : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have h2mpos : (0 : ℝ) < 2 ^ m * (a : ℝ) ^ (m + 1) := by positivity
  have hC2den : C / (2 ^ m * (a : ℝ) ^ (m + 1)) ≤ C / ((a : ℝ) * (k : ℝ) ^ m) := by
    gcongr
  have hmeas2 : (C / 2 ^ m) / (a : ℝ) ^ (m + 1)
      ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)| := by
    refine le_trans ?_ (le_trans hC2den hm)
    rw [div_div]
  -- apply the core with the folded constant C/2^m
  have hC2 : 0 < C / 2 ^ m := by positivity
  have hCa2 : 2 / (C / 2 ^ m) ≤ 100 := by
    have he : 2 / (C / 2 ^ m) = (2 : ℝ) ^ (m + 1) / C := by
      rw [div_div_eq_mul_div, pow_succ]; ring
    rw [he]; exact hCa
  exact gap_core' (C / 2 ^ m) m a k hC2 hCa2 ha h3k hmeas2

/-- **`PowGap` from the `C/a^(m+1)` measure** (modulo the per-`μ` finite mid-range `hmidAll`). -/
theorem powGap_of_measure (C : ℝ) (m : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (h : ∀ (k a : ℕ), 100 < a →
        C / (a : ℝ) ^ (m + 1) ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|)
    (hmidAll : ∀ a0 : ℕ, ∀ a k : Nat, 100 < a → a < a0 → 3 ^ a < 2 ^ k →
      2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a) :
    CollatzDescentDichotomy.PowGap :=
  powGap_of_measure_exponent ((m : ℝ) + 1) (linFormGapMu_of_measure C m hC hCa h) hmidAll

/-- **Exponent rounding, denominator-height shape (real `μ` ⟹ Nat `M`).**  The 2-D pure-two-log
engine `IrrMeasureCombination.logb23_measure_of_twolog_forms` emits `C / q^(1 + logQ/log ρ⁻¹)` with a
*real* exponent; `linFormGapMu_of_measure` consumes a *natural* exponent.  Since `a > 100 ≥ 1`,
weakening `μ ⟶ M ≥ μ` only shrinks the bound.  (Used for the oSALIKHOV shared-B route:
two-log form ⟹ 2-D measure ⟹ this ⟹ `linFormGapMu_of_measure` ⟹ `PowGap`.) -/
theorem measure_exp_round (C μ : ℝ) (M : ℕ) (hC : 0 < C) (hμM : μ ≤ (M : ℝ))
    (h : ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ μ ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ M ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)| := by
  intro k a ha
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  have hapos : (0 : ℝ) < (a : ℝ) := by linarith
  have hpow : (a : ℝ) ^ μ ≤ (a : ℝ) ^ M := by
    calc (a : ℝ) ^ μ ≤ (a : ℝ) ^ (M : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hμM
      _ = (a : ℝ) ^ M := Real.rpow_natCast (a : ℝ) M
  have hμpos : (0 : ℝ) < (a : ℝ) ^ μ := Real.rpow_pos_of_pos hapos μ
  calc C / (a : ℝ) ^ M ≤ C / (a : ℝ) ^ μ := by gcongr
    _ ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)| := h k a ha

/-- **Exponent rounding (real `μ` ⟹ Nat `m`).**  `Log23MeasureRhin.log23_measure_of_3d_bound`
emits a measure with a *real* exponent `μ` (an `rpow` `(max|p| q)^μ`), but `linFormGapMu_of_measure_max`
consumes a *natural* exponent `m` (an `npow`).  Since the height `max(|p|,q) ≥ q ≥ 1`, weakening
`μ ⟶ m ≥ μ` only shrinks the bound: `C/(q·M^μ) ≥ C/(q·M^m)`.  This bridges the two shapes. -/
theorem measure_max_exp_round (C μ : ℝ) (m : ℕ) (hC : 0 < C) (hμm : μ ≤ (m : ℝ))
    (h : ∀ (p q : ℤ), 1 ≤ q →
        C / ((q : ℝ) * (((max |p| q : ℤ) : ℝ)) ^ μ) ≤ |Real.logb 2 3 - (p : ℝ) / (q : ℝ)|) :
    ∀ (p q : ℤ), 1 ≤ q →
        C / ((q : ℝ) * (((max |p| q : ℤ) : ℝ)) ^ m) ≤ |Real.logb 2 3 - (p : ℝ) / (q : ℝ)| := by
  intro p q hq
  set M : ℝ := (((max |p| q : ℤ) : ℝ)) with hMdef
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hq)
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]
    have : (1 : ℤ) ≤ max |p| q := le_trans hq (le_max_right _ _)
    exact_mod_cast this
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  -- M^μ ≤ M^m
  have hpow : M ^ μ ≤ M ^ m := by
    calc M ^ μ ≤ M ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hμm
      _ = M ^ m := Real.rpow_natCast M m
  have hμpos : (0 : ℝ) < M ^ μ := Real.rpow_pos_of_pos hMpos μ
  have hmpos : (0 : ℝ) < M ^ m := by positivity
  -- denominators: q·M^μ ≤ q·M^m, so C/(q·M^m) ≤ C/(q·M^μ) ≤ |...|
  have hden : (q : ℝ) * M ^ μ ≤ (q : ℝ) * M ^ m :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt hqpos)
  have hdle : C / ((q : ℝ) * M ^ m) ≤ C / ((q : ℝ) * M ^ μ) := by
    gcongr
  exact le_trans hdle (h p q hq)

/-- **`PowGap` from the 3-D engine's `C/(q·max(|p|,q)^m)` measure** (modulo `hmidAll`).  This is the
direct consumer of `Log23MeasureRhin.log23_measure_of_3d_bound` for the `{I,J}` construction. -/
theorem powGap_of_measure_max (C : ℝ) (m : ℕ) (hC : 0 < C)
    (hCa : (2 : ℝ) ^ (m + 1) / C ≤ 100)
    (h : ∀ (p q : ℤ), 1 ≤ q →
        C / ((q : ℝ) * (((max |p| q : ℤ) : ℝ)) ^ m) ≤ |Real.logb 2 3 - (p : ℝ) / (q : ℝ)|)
    (hmidAll : ∀ a0 : ℕ, ∀ a k : Nat, 100 < a → a < a0 → 3 ^ a < 2 ^ k →
      2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a) :
    CollatzDescentDichotomy.PowGap :=
  powGap_of_measure_exponent ((m : ℝ) + 1) (linFormGapMu_of_measure_max C m hC hCa h) hmidAll

end CollatzPowGapMeasureBridge
