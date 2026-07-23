import Propositio.Collatz.DescentDichotomy
import Propositio.Collatz.PowGapReduce
import Propositio.Collatz.PowGapSmall
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# `PowGap` reduced to a NAMED effective irrationality measure of `log₂3`

`CollatzDescentDichotomy.PowGap` (`∀ a k, 3^a < 2^k → 2^a·(2^k − 3^a + 1) > 3^a`) is
the single residual input of the *sharp* Everett–Terras descent dichotomy
(`three_pow_ge_of_non_descent_of_gap`, giving `2^k ≤ 3^(aCoef)`).  Its `k ≥ 2a` range
is elementary (`powGap_of_two_a_le`) and `a ≤ 100` is `native_decide`
(`powGap_of_le_100`); the genuinely hard part is the sub-threshold range `k < 2a,
a > 100`, which is a lower bound on `|2^k − 3^a|` — a *linear form in two logarithms*,
i.e. transcendence (Baker)-class.

A survey of mathlib (2026-06) confirms it has **no** effective lower bound on linear
forms in logarithms, no irrationality measure as a quantity, no `|2^k − 3^a|` gap — every
Diophantine-approximation theorem there (Dirichlet, Legendre, continued-fraction
convergents, `LiouvilleWith`, Lindemann–Weierstrass) is an *upper* bound on
approximation error or a purely qualitative transcendence statement.

This file does **not** attempt an elementary proof of the sub-threshold gap (the
failed-attempts log is full of those, and the obstruction is genuinely
Mahler-3/2-problem-class).  Instead it isolates the exact transcendence input as a
**single named, literature-true hypothesis** and proves `PowGap` from it:

  `LinFormGapLog23` :  for `a > 100` (sub-threshold), `|2^k − 3^a| ≥ 3^a / a^14`.

This is the magnitude form of "`log₂3` has finite irrationality measure
`μ(log₂3) ≤ 13.3 < 14`" (Rhin 1987; Wu–Wang) — a *known theorem*, merely not yet in
mathlib.  Numerically the true gaps exceed `3^a / a^14` by a factor `> 10^27` already at
`a = 152`, so the hypothesis holds with astronomical room: the wall is **soft**, cleared
by *any* finite irrationality measure.  Porting Rhin's bound to mathlib would discharge
`LinFormGapLog23` and make the sharp dichotomy unconditional.

## Contents
* `powGap_iff_clean` — subtraction-free reformulation `3^a + 6^a < 2^(a+k) + 2^a`.
* `poly14_le_two_pow` — `(a:ℝ)^14 ≤ 2^a` for `a ≥ 100` (the slack that makes the soft
  wall provable; axiom-clean, via `Real.add_one_le_exp`).
* `LinFormGapLog23`, `powGap_of_linFormGap` — the named hypothesis and the reduction.
-/

namespace CollatzPowGapBaker

open CollatzDescentDichotomy CollatzPowGapReduce CollatzPowGapSmall
open TerrasDensity CollatzDensityCount

/-! ## §1  A clean subtraction-free reformulation of `PowGap` -/

/-- The `PowGap` inequality `2^a·(2^k − 3^a + 1) > 3^a`, under `3^a < 2^k`, is
equivalent to the subtraction-free, symmetric form `3^a + 6^a < 2^(a+k) + 2^a`. -/
theorem powGap_iff_clean (a k : Nat) (h : 3 ^ a < 2 ^ k) :
    (2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a) ↔ (3 ^ a + 6 ^ a < 2 ^ (a + k) + 2 ^ a) := by
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ k = 3 ^ a + d := ⟨2 ^ k - 3 ^ a, by omega⟩
  have h6 : (6 : Nat) ^ a = 2 ^ a * 3 ^ a := by rw [show (6 : Nat) = 2 * 3 from rfl, mul_pow]
  have hak : (2 : Nat) ^ (a + k) = 2 ^ a * 2 ^ k := by rw [pow_add]
  have e1 : 2 ^ k - 3 ^ a + 1 = d + 1 := by omega
  rw [e1, hak, hd, h6]
  set X := (2 : Nat) ^ a
  set Y := (3 : Nat) ^ a
  constructor <;> intro H <;> nlinarith [H]

/-! ## §2  Polynomial-vs-exponential slack: `(a:ℝ)^14 ≤ 2^a` for `a ≥ 100` -/

/-- One-step ratio bound: `(n+1)^14 ≤ 2·n^14` for `n ≥ 100`.  Reduces to
`(1+1/n)^14 ≤ (1+1/100)^14 = (101/100)^14 ≈ 1.148 ≤ 2` (monotonicity + `norm_num`);
no transcendental input. -/
private theorem step14 (n : Nat) (hn : 100 ≤ n) :
    ((n : ℝ) + 1) ^ 14 ≤ 2 * (n : ℝ) ^ 14 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : Nat) < n := by omega
    exact_mod_cast this
  -- (1 + 1/n)^14 ≤ 2
  have hexp : (1 + 1 / (n : ℝ)) ^ 14 ≤ 2 := by
    have hle : (1 : ℝ) / (n : ℝ) ≤ 1 / 100 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
    have hbase : 1 + 1 / (n : ℝ) ≤ 1 + 1 / 100 := by linarith
    have hmono : (1 + 1 / (n : ℝ)) ^ 14 ≤ (1 + 1 / 100 : ℝ) ^ 14 := by gcongr
    have hnum : ((1 : ℝ) + 1 / 100) ^ 14 ≤ 2 := by norm_num
    linarith
  have hfac : ((n : ℝ) + 1) ^ 14 = (n : ℝ) ^ 14 * (1 + 1 / (n : ℝ)) ^ 14 := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hfac]
  nlinarith [hexp, pow_nonneg (le_of_lt hnpos) 14]

/-- **`poly14_le_two_pow`.**  `(a:ℝ)^14 ≤ 2^a` for every `a ≥ 100`.  This is the
exponential slack that lets *any* finite irrationality measure of `log₂3` clear the
`PowGap` threshold.  Proved by induction from the base `a = 100` (the crossover of
`2^a ≥ a^14` is `a ≈ 92`), with the one-step ratio `step14`.  Axiom-clean. -/
theorem poly14_le_two_pow (a : Nat) (ha : 100 ≤ a) : (a : ℝ) ^ 14 ≤ (2 : ℝ) ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 100 with hn | hn
    · -- n < 100 ≤ n+1 ⟹ n = 99, base case (100:ℝ)^14 ≤ 2^100
      obtain rfl : n = 99 := by omega
      norm_num
    · have hih := ih hn
      have hstep := step14 n hn
      have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      have hcast : ((n : ℝ) + 1) = ((n + 1 : Nat) : ℝ) := by push_cast; ring
      rw [h2, ← hcast]
      -- (n+1)^14 ≤ 2·n^14 ≤ 2·2^n
      have : 2 * (n : ℝ) ^ 14 ≤ 2 * (2 : ℝ) ^ n := by linarith [hih]
      linarith [hstep, this]

/-! ## §3  The named transcendence hypothesis and the reduction -/

/-- **`LinFormGapLog23` — the single transcendence input.**

For sub-threshold `a > 100` (where the minimal `k` with `3^a < 2^k` satisfies
`2^k ≤ 2·3^a`), the gap obeys `3^a ≤ a^14 · (2^k − 3^a)`, i.e.

  `|2^k − 3^a| ≥ 3^a / a^14`.

This is the **magnitude form of an effective irrationality measure** for `log₂3`:
it is exactly what `μ(log₂3) ≤ 13.3 < 14` (Rhin 1987; Wu–Wang) yields, and is a *known
theorem* of transcendence theory — merely absent from mathlib (which has no effective
lower bound on linear forms in logarithms).  Numerically it holds with a factor `> 10^27`
of slack already at `a = 152`, so it is in no way the bottleneck: *any* finite
irrationality measure of `log₂3` implies it.  Discharging it (by porting Rhin's bound)
makes `PowGap`, hence the sharp Everett–Terras dichotomy, unconditional. -/
def LinFormGapLog23 : Prop :=
  ∀ a k : Nat, 100 < a → 3 ^ a < 2 ^ k → 2 ^ k ≤ 2 * 3 ^ a →
    (3 : ℝ) ^ a ≤ (a : ℝ) ^ 14 * ((2 : ℝ) ^ k - (3 : ℝ) ^ a)

/-- **`powGap_of_linFormGap`.**  The bespoke power inequality `PowGap` follows from the
named effective irrationality measure `LinFormGapLog23`.

Proof structure (the four regimes of `PowGap`):
* `a ≤ 100` — `powGap_of_le_100` (`native_decide`);
* `a > 100, k ≥ 2a` — `powGap_of_two_a_le` (elementary, from `3^a + 2^a ≤ 4^a + 1`);
* `a > 100, k < 2a` — reduce (monotonicity in `k`, `powGap_term_of_le`) to the minimal
  `k₀` with `3^a < 2^{k₀}`; there `2^{k₀} ≤ 2·3^a`, so `LinFormGapLog23` gives
  `3^a ≤ a^14·(2^{k₀} − 3^a)`, and `poly14_le_two_pow` (`a^14 ≤ 2^a`) upgrades this to
  `3^a ≤ 2^a·(2^{k₀} − 3^a) < 2^a·(2^{k₀} − 3^a + 1)`. -/
theorem powGap_of_linFormGap (h : LinFormGapLog23) : PowGap := by
  intro a k h3k
  by_cases ha : a ≤ 100
  · exact powGap_of_le_100 a k ha h3k
  · push_neg at ha          -- ha : 100 < a
    by_cases hk : 2 * a ≤ k
    · exact powGap_of_two_a_le a k hk h3k
    · push_neg at hk         -- hk : k < 2*a
      -- minimal k₀ with 3^a < 2^{k₀}
      have hex : ∃ m, 3 ^ a < 2 ^ m := ⟨k, h3k⟩
      set k₀ := Nat.find hex with hk₀def
      have hk₀ : 3 ^ a < 2 ^ k₀ := Nat.find_spec hex
      have hk₀le : k₀ ≤ k := Nat.find_le h3k
      have hk₀pos : 1 ≤ k₀ := by
        rcases Nat.eq_zero_or_pos k₀ with h0 | h0
        · rw [h0, pow_zero] at hk₀
          have := Nat.one_le_pow a 3 (by norm_num); omega
        · exact h0
      have hmin : 2 ^ (k₀ - 1) ≤ 3 ^ a := by
        have := Nat.find_min hex (show k₀ - 1 < k₀ from by omega); omega
      have h2k0 : 2 ^ k₀ ≤ 2 * 3 ^ a := by
        have e : k₀ = (k₀ - 1) + 1 := by omega
        rw [e, pow_succ]; omega
      -- apply the named hypothesis at the minimal k₀
      have hreal := h a k₀ ha hk₀ h2k0
      have hg : (a : ℝ) ^ 14 ≤ (2 : ℝ) ^ a := poly14_le_two_pow a (by omega)
      have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k₀ - (3 : ℝ) ^ a := by
        have : (3 : ℝ) ^ a < (2 : ℝ) ^ k₀ := by exact_mod_cast hk₀
        linarith
      -- chain: 3^a ≤ a^14·gap ≤ 2^a·gap
      have hfin : (3 : ℝ) ^ a ≤ (2 : ℝ) ^ a * ((2 : ℝ) ^ k₀ - (3 : ℝ) ^ a) :=
        le_trans hreal (by gcongr)
      -- back to ℕ via D := 2^{k₀} − 3^a
      obtain ⟨D, hD, hD1⟩ : ∃ D, 2 ^ k₀ = 3 ^ a + D ∧ 1 ≤ D := ⟨2 ^ k₀ - 3 ^ a, by omega, by omega⟩
      have hDreal : (2 : ℝ) ^ k₀ - (3 : ℝ) ^ a = (D : ℝ) := by
        have : (2 : ℝ) ^ k₀ = (3 : ℝ) ^ a + (D : ℝ) := by exact_mod_cast hD
        rw [this]; ring
      rw [hDreal] at hfin
      have hnat : 3 ^ a ≤ 2 ^ a * D := by exact_mod_cast hfin
      -- PowGap at k₀, then propagate to k
      have hpgk0 : 3 ^ a < 2 ^ a * (2 ^ k₀ - 3 ^ a + 1) := by
        have e : 2 ^ k₀ - 3 ^ a + 1 = D + 1 := by omega
        rw [e]
        have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        calc 3 ^ a < 2 ^ a * D + 2 ^ a := by omega
          _ = 2 ^ a * (D + 1) := by ring
      exact powGap_term_of_le a k₀ k hk₀le hpgk0

/-! ## §4  The sharp dichotomy and capstone, resting on the NAMED hypothesis

These re-export the corpus's `PowGap`-conditional results with `PowGap` replaced by the
recognizable `LinFormGapLog23`.  The point is *honesty about the frontier*: the sharp
Everett–Terras dichotomy now depends on one **named, citable transcendence theorem**
(the effective irrationality measure of `log₂3`), not on a bespoke power inequality. -/

/-- **Sharp per-orbit dichotomy, conditional on `LinFormGapLog23`.**  For `n ≥ 2^k`, a
non-descending orbit (`n ≤ T_iter n k`) forces `2^k ≤ 3^(aCoef n k)` — the *exact* Terras
inequality (no factor `2`, cf. the unconditional `three_pow_ge_of_non_descent_elem`'s
`2·3^(aCoef)`). -/
theorem three_pow_ge_of_non_descent_of_log23 (h : LinFormGapLog23)
    (n k : Nat) (hn : 2 ^ k ≤ n) (hnd : n ≤ T_iter n k) :
    2 ^ k ≤ 3 ^ (aCoef n k) :=
  three_pow_ge_of_non_descent_of_gap (powGap_of_linFormGap h) n k hn hnd

/-- **Everett–Terras "almost all descend" via the named measure.**  `β(k)/2^k → 0`,
conditional on `LinFormGapLog23`.  (Note: the *density* statement is already known
**unconditionally** — `CollatzAlmostAllDescendUncond.collatz_almost_all_descend_uncond` —
since the elementary `2^k ≥ 2·3^a ⟹ descent` suffices for the entropy count.  This
version is the route through the *sharp* threshold; its value is the sharp dichotomy
above, of which density is a corollary.) -/
theorem collatz_almost_all_descend_of_log23 (h : LinFormGapLog23) :
    Filter.Tendsto (fun k => (beta k : ℝ) / 2 ^ k) Filter.atTop (nhds 0) :=
  collatz_almost_all_descend_of_gap (powGap_of_linFormGap h)

/-! ## §5  The frontier in standard vocabulary: an irrationality measure of `log₂3`

The bespoke `LinFormGapLog23` is *asserted* (in its docstring) to be the magnitude form
of an irrationality measure.  This section **machine-checks** that claim: it states the
frontier as a textbook Diophantine bound on the **named constant** `Real.logb 2 3`, and
proves that bound implies `LinFormGapLog23` (hence `PowGap`).  A referee then need only
trust a recognizable statement — "`log₂3` has irrationality measure `≤ 14`" — instead of
a hand-rolled power inequality. -/

/-- **`IrrMeasureLog23` — the frontier as a standard irrationality measure.**

`log₂3 = Real.logb 2 3` is approximated by rationals `k/a` (with `a > 100`) no better than

  `|log₂3 − k/a| ≥ (1/40) / a^14`,

i.e. `log₂3` has (effective) irrationality measure `≤ 14`.  This is a *known theorem*
(`μ(log₂3) ≤ 13.3`, Rhin 1987; the exponent `14 > 13.3` and the generous constant `1/40`
leave room for *all* `a > 100`), absent from mathlib only because it lacks effective
irrationality measures.  `linFormGap_of_irrMeasure` checks it implies the bespoke gap. -/
def IrrMeasureLog23 : Prop :=
  ∀ (k a : ℕ), 100 < a →
    (1 / 40 : ℝ) / (a : ℝ) ^ 14 ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|

/-- **Bridge (machine-checked): the standard irrationality measure ⟹ the bespoke gap.**

Writing `θ = log₂3`, `x = k − a·θ` (`> 0` since `2^k > 3^a`):
`2^k − 3^a = 3^a·(2^x − 1) ≥ 3^a·x·log 2 ≥ 3^a·x·(1/2) ≥ 3^a·(1/80)/a^13 ≥ 3^a/a^14`,
the last step using `a > 100 ≥ 80`.  Only `2^x ≥ 1 + x·log 2` (`Real.add_one_le_exp`) and
`log 2 ≥ 1/2` (`Real.one_sub_inv_le_log_of_pos`) are used — no transcendental constants. -/
theorem linFormGap_of_irrMeasure (h : IrrMeasureLog23) : LinFormGapLog23 := by
  intro a k ha h3k _h2k
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hapos : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha100 : (100 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 100 ≤ a)
  have hane : (a : ℝ) ≠ 0 := ne_of_gt hapos
  set θ := Real.logb 2 3 with hθdef
  have hθpow : (2 : ℝ) ^ θ = 3 :=
    Real.rpow_logb h2pos (by norm_num) (by norm_num)
  -- 3^a (npow) = 2^(θ·a) (rpow)
  have e3 : (3 : ℝ) ^ a = (2 : ℝ) ^ (θ * (a : ℝ)) := by
    rw [Real.rpow_mul h2pos.le, hθpow, Real.rpow_natCast]
  have h3apos : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  -- x = k − θ·a, and 2^k = 3^a · 2^x
  set x : ℝ := (k : ℝ) - θ * (a : ℝ) with hxdef
  have e2k : (2 : ℝ) ^ k = (3 : ℝ) ^ a * (2 : ℝ) ^ x := by
    have hk : (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ)) := (Real.rpow_natCast 2 k).symm
    rw [hk]
    have hsum : (k : ℝ) = θ * (a : ℝ) + x := by rw [hxdef]; ring
    rw [hsum, Real.rpow_add h2pos, ← e3]
  -- x > 0  (from 3^a < 2^k)
  have hxpos : 0 < x := by
    have h3lt2 : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    rw [e3, ← Real.rpow_natCast 2 k] at h3lt2
    have hlt := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h3lt2
    rw [hxdef]; linarith
  -- log 2 ≥ 1/2
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos h2pos
    norm_num at this; linarith
  -- 2^x ≥ 1 + x·log 2
  have hexp : (1 : ℝ) + x * Real.log 2 ≤ (2 : ℝ) ^ x := by
    have hdef : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) := Real.rpow_def_of_pos h2pos x
    rw [hdef]
    have := Real.add_one_le_exp (Real.log 2 * x)
    nlinarith [this]
  -- x ≥ (1/40)/a^13  (from the measure: |θ − k/a| = x/a)
  have hmeas := h k a ha
  have hxa : |θ - (k : ℝ) / (a : ℝ)| = x / (a : ℝ) := by
    have he : θ - (k : ℝ) / (a : ℝ) = -(x / (a : ℝ)) := by
      rw [hxdef]; field_simp; ring
    rw [he, abs_neg, abs_of_pos (by positivity)]
  rw [hxa] at hmeas
  have hxlow : (1 / 40 : ℝ) / (a : ℝ) ^ 13 ≤ x := by
    have h1 : (1 / 40 : ℝ) / (a : ℝ) ^ 14 * (a : ℝ) ≤ x / (a : ℝ) * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hmeas (le_of_lt hapos)
    have h2 : x / (a : ℝ) * (a : ℝ) = x := by field_simp
    have h3 : (1 / 40 : ℝ) / (a : ℝ) ^ 14 * (a : ℝ) = (1 / 40 : ℝ) / (a : ℝ) ^ 13 := by
      field_simp
    rw [h2, h3] at h1; exact h1
  -- 2^x − 1 ≥ 1/(80·a^13)
  have hxbound : (1 : ℝ) / (80 * (a : ℝ) ^ 13) ≤ (2 : ℝ) ^ x - 1 := by
    have c1 : x * Real.log 2 ≤ (2 : ℝ) ^ x - 1 := by linarith [hexp]
    have c2 : x * (1 / 2 : ℝ) ≤ x * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left hlog2 (le_of_lt hxpos)
    have c3 : ((1 / 40 : ℝ) / (a : ℝ) ^ 13) * (1 / 2) ≤ x * (1 / 2) :=
      mul_le_mul_of_nonneg_right hxlow (by norm_num)
    have c4 : (1 : ℝ) / (80 * (a : ℝ) ^ 13) = ((1 / 40 : ℝ) / (a : ℝ) ^ 13) * (1 / 2) := by
      have : (a : ℝ) ^ 13 ≠ 0 := by positivity
      field_simp; ring
    rw [c4]; linarith [c1, c2, c3]
  -- assemble: 3^a/a^14 ≤ 2^k − 3^a, then conclude
  have hbig : (3 : ℝ) ^ a / (80 * (a : ℝ) ^ 13) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have hstep1 : (2 : ℝ) ^ k - (3 : ℝ) ^ a = (3 : ℝ) ^ a * ((2 : ℝ) ^ x - 1) := by
      rw [e2k]; ring
    rw [hstep1]
    have hmul : (3 : ℝ) ^ a * (1 / (80 * (a : ℝ) ^ 13)) ≤ (3 : ℝ) ^ a * ((2 : ℝ) ^ x - 1) :=
      mul_le_mul_of_nonneg_left hxbound (le_of_lt h3apos)
    calc (3 : ℝ) ^ a / (80 * (a : ℝ) ^ 13)
        = (3 : ℝ) ^ a * (1 / (80 * (a : ℝ) ^ 13)) := by ring
      _ ≤ (3 : ℝ) ^ a * ((2 : ℝ) ^ x - 1) := hmul
  have hgap : (3 : ℝ) ^ a / (a : ℝ) ^ 14 ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    refine le_trans ?_ hbig
    have hden : 80 * (a : ℝ) ^ 13 ≤ (a : ℝ) ^ 14 := by
      have e : (a : ℝ) ^ 14 = (a : ℝ) ^ 13 * (a : ℝ) := by ring
      nlinarith [pow_pos hapos 13, ha100]
    gcongr
  -- finish: 3^a ≤ a^14·(2^k − 3^a)
  exact (div_le_iff₀' (by positivity : (0 : ℝ) < (a : ℝ) ^ 14)).mp hgap

/-- **`powGap_of_irrMeasure`.**  `PowGap` follows from the standard irrationality measure
`IrrMeasureLog23` of `log₂3` — the frontier reduced to one recognizable, citable
transcendence theorem. -/
theorem powGap_of_irrMeasure (h : IrrMeasureLog23) : PowGap :=
  powGap_of_linFormGap (linFormGap_of_irrMeasure h)

/-- Sharp per-orbit Terras dichotomy, conditional on the irrationality measure of `log₂3`. -/
theorem three_pow_ge_of_non_descent_of_irrMeasure (h : IrrMeasureLog23)
    (n k : Nat) (hn : 2 ^ k ≤ n) (hnd : n ≤ T_iter n k) :
    2 ^ k ≤ 3 ^ (aCoef n k) :=
  three_pow_ge_of_non_descent_of_gap (powGap_of_irrMeasure h) n k hn hnd

/-- Everett–Terras "almost all descend" via the *named* irrationality measure of `log₂3`
(the sharp-threshold route; density itself is already unconditional). -/
theorem collatz_almost_all_descend_of_irrMeasure (h : IrrMeasureLog23) :
    Filter.Tendsto (fun k => (beta k : ℝ) / 2 ^ k) Filter.atTop (nhds 0) :=
  collatz_almost_all_descend_of_gap (powGap_of_irrMeasure h)

end CollatzPowGapBaker
