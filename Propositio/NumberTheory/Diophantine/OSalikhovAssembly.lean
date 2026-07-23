import Propositio.NumberTheory.Diophantine.OSalikhovHwInterface
import Propositio.NumberTheory.Diophantine.OSalikhovHdetInterface
import Propositio.NumberTheory.Diophantine.OSalikhovHsmallSharper
import Propositio.NumberTheory.Diophantine.OSalikhovTwoLog
import Propositio.Collatz.PowGapCapstone22
import Propositio.Collatz.PowGapMeasureBridge

/-!
# Conditional assembly: the full interface from exactly the two genuine inputs

This file proves `osalikhov_twolog_interface_of_inputs`: that the full
`osalikhov_twolog_interface` conclusion follows once the two genuinely-remaining mathematical
inputs are supplied as explicit hypotheses:

1. **`hDenBound`**: the Apéry/Beukers lcm-clearing denominator satisfies `Den n ≤ D * 21^n`
   (Phase-2 number theory, the Apéry lcm bound with rate `C = 21`).
2. **`hdec1` / `hdec2`**: the integral decomposition `E1 n = A1seq n + Bseq n * log(2/3)` and
   `E2 n = A2seq n - Bseq n * log 2` (Phase-3 partial-fraction / Gosper-certificate step).

All other clauses — `hwpos`, `hwden`, `hdet`, `hsmall`, and the exponent bound `hexp` — are
discharged purely from these two inputs via the proved connectors:

* `hwpos`  ← `OSalikhovHdet.hwpos_connector`
* `hwden`  ← `OSalikhovHdet.hwden_connector` (with C = 21, Q = 94521)
* `hdet`   ← `OSalikhovHdet.hdet_concrete` (sign algebra in ℝ → ℤ contradiction)
* `hsmall` ← `OSalikhovTwoLog.form_decay_sharper` (shifted index, absolute value algebra)
* `hexp`   ← rational inequality `94521 * 567^21 ≤ 1000^21` certified by `norm_num`

**Sign convention**: `w n = wPos Den n = +Den(n+1)·A2seq(n+1) > 0` (positive, the log3 coeff);
`v n` is `vInt n` with `(vInt n : ℝ) = -Den(n+1)·(A1seq+A2seq)(n+1)` (negative in general).
The two-log form `(vInt n)*log2 + (wInt n)*log3 = -Den(n+1)*V(n+1)` where
`V m = (A1+A2)(m)*log2 - A2(m)*log3`, so `|vInt·log2 + wInt·log3| = Den(n+1)*|V(n+1)|`.

**Exponent bound (`hexp`)**:
  `log(94521) / log(1000/567) ≤ 21`
  ⟺ `94521 ≤ (1000/567)^21`
  ⟺ `94521 * 567^21 ≤ 1000^21`  (pure integer, proved by `norm_num`)

The theorem thereby reduces the prize gap to the two stated inputs with no additional sorry.
-/

namespace OSalikhovAssembly

open OSalikhovHdet OSalikhovSequences OSalikhovTwoLog
open CollatzPowGapMeasureBridge CollatzPowGapCapstone22

/-- **Conditional assembly theorem: the full interface from the two genuine inputs.**

Given:
- `Den : ℕ → ℝ` with `Den n > 0` and `Den n ≤ D * 21^n` (Apéry/Beukers lcm bound, C = 21);
- `vInt wInt : ℕ → ℤ` with cast identities `(vInt n : ℝ) = -Den(n+1)·(A1seq+A2seq)(n+1)` and
  `(wInt n : ℝ) = Den(n+1)·A2seq(n+1)`;
- the integral decomposition identities `E1 n = A1seq n + Bseq n * log(2/3)` and
  `E2 n = A2seq n - Bseq n * log 2`;

the conclusion of `osalikhov_twolog_interface` holds with:
  `A = 8*D*(567/1000)`, `B = 10000*D*21*4501`, `ρ = 567/1000`, `Q = 94521`. -/
theorem osalikhov_twolog_interface_of_inputs
    (Den : ℕ → ℝ) (D : ℝ)
    (hDpos   : 0 < D)
    (hDenPos : ∀ n, 0 < Den n)
    (hDenBound : ∀ n, Den n ≤ D * (21 : ℝ) ^ n)
    -- Integer sequences for the cleared coordinates (Phase-2 integrality):
    (vInt wInt : ℕ → ℤ)
    -- Cast identities connecting integer sequences to the real cleared coordinates:
    (hvcast : ∀ n, (vInt n : ℝ) = -(Den (n + 1) * (A1seq (n + 1) + A2seq (n + 1))))
    (hwcast : ∀ n, (wInt n : ℝ) = Den (n + 1) * A2seq (n + 1))
    -- Integral decomposition (Phase-3 content):
    (hdec1 : ∀ n, E1 n = A1seq n + Bseq n * Real.log (2 / 3))
    (hdec2 : ∀ n, E2 n = A2seq n - Bseq n * Real.log 2) :
    ∃ (v w : ℕ → ℤ) (A B ρ Q : ℝ),
      0 < A ∧ 0 < B ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      (∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n) ∧
      (∀ n, 0 < w n) ∧
      (∀ n, (w n : ℝ) ≤ B * Q ^ n) ∧
      (∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 21 := by
  -- Witness the existential with concrete constants (C = 21 fixed):
  --   ρ = 21 * 27/1000 = 567/1000,  Q = 21 * 4501 = 94521
  --   A = 8 * D * ρ  (from the shifted form_decay_sharper bound at n+1)
  --   B = 10000 * D * 21 * 4501  (from hwden_connector)
  refine ⟨vInt, wInt,
          8 * D * (567 / 1000),   -- A
          10000 * D * 21 * 4501,  -- B
          567 / 1000,             -- ρ = 21 * 27/1000
          94521,                  -- Q = 21 * 4501
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·-- 0 < A = 8*D*(567/1000)
   positivity
  ·-- 0 < B = 10000*D*21*4501
   positivity
  ·-- 0 < ρ = 567/1000
   norm_num
  ·-- ρ = 567/1000 < 1
   norm_num
  ·-- 1 < Q = 94521
   norm_num
  ·-- hsmall: |(vInt n : ℝ) * log 2 + (wInt n : ℝ) * log 3| ≤ A * ρ^n
   intro n
   -- |Den(n+1)| = Den(n+1) (since Den > 0)
   have hDenAbsBound : ∀ m, |Den m| ≤ D * (21 : ℝ) ^ m :=
     fun m => (abs_of_pos (hDenPos m)).symm ▸ hDenBound m
   -- Apply form_decay_sharper at index (n+1):
   have hsharp := form_decay_sharper A1seq A2seq Bseq Den D 21
     (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 21)
     hDenAbsBound hdec1 hdec2 (n + 1)
   -- form_decay_sharper (at n+1) gives:
   --   |Den(n+1) * ((A1+A2)(n+1)*log2 - A2(n+1)*log3)| ≤ 8*D*(21*(27/1000))^(n+1)
   -- LHS rewrite: the absolute value equals |(vInt n)*log2 + (wInt n)*log3|
   have hlhs : |Den (n + 1) * ((A1seq (n + 1) + A2seq (n + 1)) * Real.log 2 - A2seq (n + 1) * Real.log 3)|
       = |(vInt n : ℝ) * Real.log 2 + (wInt n : ℝ) * Real.log 3| := by
     rw [hvcast n, hwcast n]
     rw [show -(Den (n+1) * (A1seq (n+1) + A2seq (n+1))) * Real.log 2 +
             Den (n+1) * A2seq (n+1) * Real.log 3
         = -(Den (n+1) * ((A1seq (n+1) + A2seq (n+1)) * Real.log 2 - A2seq (n+1) * Real.log 3))
         by ring]
     rw [abs_neg]
   rw [hlhs] at hsharp
   -- RHS rewrite: 8*D*(21*(27/1000))^(n+1) = 8*D*(567/1000)*(567/1000)^n
   have hrhs : (8 * D) * ((21 : ℝ) * (27 / 1000)) ^ (n + 1) =
       8 * D * (567 / 1000) * (567 / 1000) ^ n := by
     rw [pow_succ]
     norm_num
     ring
   rw [hrhs] at hsharp
   exact hsharp
  ·-- hwpos: 0 < wInt n
   intro n
   have hreal : (0 : ℝ) < (wInt n : ℝ) := by
     rw [hwcast n]
     exact hwpos_connector Den hDenPos n
   exact_mod_cast hreal
  ·-- hwden: (wInt n : ℝ) ≤ B * Q^n
   intro n
   rw [hwcast n]
   -- wPos Den n = Den(n+1) * A2seq(n+1)
   -- hwden_connector gives: wPos Den n ≤ (10000*D*C*4501)*(C*4501)^n with C=21
   -- = (10000*D*21*4501) * (21*4501)^n = (10000*D*21*4501) * 94521^n
   have := hwden_connector Den D 21
     (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 21) hDenPos hDenBound n
   -- hwden_connector: wPos Den n ≤ (10000*D*21*4501)*(21*4501)^n
   simp only [wPos] at this
   convert this using 2
   norm_num
  ·-- hdet: wInt n * vInt (n+1) ≠ wInt (n+1) * vInt n
   intro n
   intro heq
   -- Cast the integer equation to ℝ
   have heqR : (wInt n : ℝ) * (vInt (n + 1) : ℝ) = (wInt (n + 1) : ℝ) * (vInt n : ℝ) := by
     have : ((wInt n * vInt (n + 1) : ℤ) : ℝ) = ((wInt (n + 1) * vInt n : ℤ) : ℝ) :=
       by exact_mod_cast congrArg (Int.cast (R := ℝ)) heq
     push_cast at this
     linarith
   -- Rewrite using cast identities
   rw [hwcast n, hvcast (n + 1), hwcast (n + 1), hvcast n] at heqR
   -- heqR : Den(n+1)*A2(n+1) * (-(Den(n+2)*(A1+A2)(n+2)))
   --      = Den(n+2)*A2(n+2) * (-(Den(n+1)*(A1+A2)(n+1)))
   -- Simplify: -(Den(n+1)*A2(n+1)*Den(n+2)*(A1+A2)(n+2))
   --         = -(Den(n+2)*A2(n+2)*Den(n+1)*(A1+A2)(n+1))
   -- i.e., wCoord Den n * vCoord Den (n+1) = wCoord Den (n+1) * vCoord Den n
   -- which contradicts hdet_concrete
   apply hdet_concrete Den hDenPos n
   simp only [wCoord, vCoord]
   nlinarith [heqR]
  ·-- hexp: log(94521) / log((567/1000)⁻¹) ≤ 21
   -- (567/1000)⁻¹ = 1000/567, so goal is log(94521)/log(1000/567) ≤ 21.
   -- Strategy: 94521 ≤ (1000/567)^21  (rational arithmetic via norm_num)
   --           ⟹ log(94521) ≤ log((1000/567)^21) = 21 * log(1000/567)
   --           ⟹ log(94521)/log(1000/567) ≤ 21.
   have hρinv : ((567 : ℝ) / 1000)⁻¹ = 1000 / 567 := by norm_num
   rw [hρinv]
   have hlog_pos : 0 < Real.log (1000 / 567) := Real.log_pos (by norm_num)
   -- Sufficient: log(94521) ≤ 21 * log(1000/567)
   rw [div_le_iff₀ hlog_pos]
   -- Goal: log(94521) ≤ log(1000/567) * 21
   -- Use: log(1000/567)*21 = log((1000/567)^21) and 94521 ≤ (1000/567)^21
   have hpow_bound : (94521 : ℝ) ≤ (1000 / 567 : ℝ) ^ 21 := by norm_num
   have hlog_ineq : Real.log 94521 ≤ Real.log ((1000 / 567 : ℝ) ^ 21) :=
     Real.log_le_log (by norm_num) hpow_bound
   rw [Real.log_pow] at hlog_ineq
   linarith

/-- **Regeneralized conditional assembly (C = 22, sharp height Cₕ = 1500).**

Same structure as `osalikhov_twolog_interface_of_inputs` but with:
- `hDenBound : ∀ n, Den n ≤ D * 22^n`  (C = 22)
- `ρ = 22 * 27/1000 = 594/1000`
- `Q = 22 * 1500 = 33000`  (sharpened from `22 * 4501 = 99022`)
- `B = 10000 * D * 22 * 1500`

**`hexp` closure**: `log(33000) / log(1000/594) ≤ 21`
⟺ `33000 ≤ (1000/594)^21`  (rational, certified by `norm_num`).
Numerically: `(1000/594)^21 ≈ e^{21·0.521} ≈ 55800 ≥ 33000` ✓ (margin ~1.7×). -/
theorem osalikhov_twolog_interface_of_inputs_c22
    (Den : ℕ → ℝ) (D : ℝ)
    (hDpos   : 0 < D)
    (hDenPos : ∀ n, 0 < Den n)
    (hDenBound : ∀ n, Den n ≤ D * (22 : ℝ) ^ n)
    -- Integer sequences for the cleared coordinates (Phase-2 integrality):
    (vInt wInt : ℕ → ℤ)
    -- Cast identities connecting integer sequences to the real cleared coordinates:
    (hvcast : ∀ n, (vInt n : ℝ) = -(Den (n + 1) * (A1seq (n + 1) + A2seq (n + 1))))
    (hwcast : ∀ n, (wInt n : ℝ) = Den (n + 1) * A2seq (n + 1))
    -- Integral decomposition (Phase-3 content):
    (hdec1 : ∀ n, E1 n = A1seq n + Bseq n * Real.log (2 / 3))
    (hdec2 : ∀ n, E2 n = A2seq n - Bseq n * Real.log 2) :
    ∃ (v w : ℕ → ℤ) (A B ρ Q : ℝ),
      0 < A ∧ 0 < B ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      (∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n) ∧
      (∀ n, 0 < w n) ∧
      (∀ n, (w n : ℝ) ≤ B * Q ^ n) ∧
      (∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 21 := by
  -- Witness with C = 22, Cₕ = 1500:
  --   ρ = 22 * 27/1000 = 594/1000,  Q = 22 * 1500 = 33000
  --   A = 8 * D * ρ  (from form_decay_sharper at n+1)
  --   B = 10000 * D * 22 * 1500  (from hwden_connector_1500 with C=22)
  refine ⟨vInt, wInt,
          8 * D * (594 / 1000),    -- A
          10000 * D * 22 * 1500,   -- B
          594 / 1000,              -- ρ = 22 * 27/1000
          33000,                   -- Q = 22 * 1500
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < A = 8*D*(594/1000)
    positivity
  · -- 0 < B = 10000*D*22*1500
    positivity
  · -- 0 < ρ = 594/1000
    norm_num
  · -- ρ = 594/1000 < 1
    norm_num
  · -- 1 < Q = 33000
    norm_num
  · -- hsmall: |(vInt n : ℝ) * log 2 + (wInt n : ℝ) * log 3| ≤ A * ρ^n
    intro n
    have hDenAbsBound : ∀ m, |Den m| ≤ D * (22 : ℝ) ^ m :=
      fun m => (abs_of_pos (hDenPos m)).symm ▸ hDenBound m
    -- Apply form_decay_sharper at index (n+1) with C = 22:
    have hsharp := form_decay_sharper A1seq A2seq Bseq Den D 22
      (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 22)
      hDenAbsBound hdec1 hdec2 (n + 1)
    -- LHS rewrite: absolute value equals |(vInt n)*log2 + (wInt n)*log3|
    have hlhs : |Den (n + 1) * ((A1seq (n + 1) + A2seq (n + 1)) * Real.log 2 - A2seq (n + 1) * Real.log 3)|
        = |(vInt n : ℝ) * Real.log 2 + (wInt n : ℝ) * Real.log 3| := by
      rw [hvcast n, hwcast n]
      rw [show -(Den (n+1) * (A1seq (n+1) + A2seq (n+1))) * Real.log 2 +
              Den (n+1) * A2seq (n+1) * Real.log 3
          = -(Den (n+1) * ((A1seq (n+1) + A2seq (n+1)) * Real.log 2 - A2seq (n+1) * Real.log 3))
          by ring]
      rw [abs_neg]
    rw [hlhs] at hsharp
    -- RHS rewrite: 8*D*(22*(27/1000))^(n+1) = 8*D*(594/1000)*(594/1000)^n
    have hrhs : (8 * D) * ((22 : ℝ) * (27 / 1000)) ^ (n + 1) =
        8 * D * (594 / 1000) * (594 / 1000) ^ n := by
      rw [pow_succ]; norm_num; ring
    rw [hrhs] at hsharp
    exact hsharp
  · -- hwpos: 0 < wInt n
    intro n
    have hreal : (0 : ℝ) < (wInt n : ℝ) := by
      rw [hwcast n]
      exact hwpos_connector Den hDenPos n
    exact_mod_cast hreal
  · -- hwden: (wInt n : ℝ) ≤ B * Q^n
    intro n
    rw [hwcast n]
    -- hwden_connector_1500 with C = 22:
    -- wPos Den n ≤ (10000*D*22*1500)*(22*1500)^n = (10000*D*22*1500)*33000^n
    have h := hwden_connector_1500 Den D 22
      (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 22) hDenPos hDenBound n
    simp only [wPos] at h
    convert h using 2
    norm_num
  · -- hdet: wInt n * vInt (n+1) ≠ wInt (n+1) * vInt n
    intro n
    intro heq
    have heqR : (wInt n : ℝ) * (vInt (n + 1) : ℝ) = (wInt (n + 1) : ℝ) * (vInt n : ℝ) := by
      have : ((wInt n * vInt (n + 1) : ℤ) : ℝ) = ((wInt (n + 1) * vInt n : ℤ) : ℝ) :=
        by exact_mod_cast congrArg (Int.cast (R := ℝ)) heq
      push_cast at this
      linarith
    rw [hwcast n, hvcast (n + 1), hwcast (n + 1), hvcast n] at heqR
    apply hdet_concrete Den hDenPos n
    simp only [wCoord, vCoord]
    nlinarith [heqR]
  · -- hexp: log(33000) / log((594/1000)⁻¹) ≤ 21
    -- (594/1000)⁻¹ = 1000/594, goal: log(33000)/log(1000/594) ≤ 21.
    -- Strategy: 33000 ≤ (1000/594)^21  (rational, norm_num)
    --           ⟹ log(33000) ≤ 21 * log(1000/594)
    --           ⟹ log(33000)/log(1000/594) ≤ 21.
    have hρinv : ((594 : ℝ) / 1000)⁻¹ = 1000 / 594 := by norm_num
    rw [hρinv]
    have hlog_pos : 0 < Real.log (1000 / 594) := Real.log_pos (by norm_num)
    rw [div_le_iff₀ hlog_pos]
    -- Goal: log(33000) ≤ log(1000/594) * 21
    have hpow_bound : (33000 : ℝ) ≤ (1000 / 594 : ℝ) ^ 21 := by norm_num
    have hlog_ineq : Real.log 33000 ≤ Real.log ((1000 / 594 : ℝ) ^ 21) :=
      Real.log_le_log (by norm_num) hpow_bound
    rw [Real.log_pow] at hlog_ineq
    linarith

/-- **HONEST conditional assembly (C = 30, sharp height Cₕ = 1500).**

This is the version matching the TRUE denominator rate `Den n ≤ D·30ⁿ`
(`OSalikhovDenBound.DenIntN_bound_30`); the `C = 21`/`C = 22` variants above rest on the FALSE
`21ⁿ`/`22ⁿ` rates (`OSalikhovDenStructure`) and are therefore VACUOUS when instantiated. With:
- `hDenBound : ∀ n, Den n ≤ D * 30^n`  (C = 30)
- `ρ = 30 * 27/1000 = 810/1000 = 81/100`
- `Q = 30 * 1500 = 45000`
- `B = 10000 * D * 30 * 1500`

**`hexp` closure** (generous bound `≤ 60`, true value `log(45000)/log(1000/810) ≈ 50.84`):
`45000 ≤ (1000/810)^60` (rational, `norm_num`; `(1000/810)^60 ≈ 309000`, margin ~6.9×).
The downstream capstone is `CollatzPowGapCapstone60` (`M ≤ 60`). -/
theorem osalikhov_twolog_interface_of_inputs_c30
    (Den : ℕ → ℝ) (D : ℝ)
    (hDpos   : 0 < D)
    (hDenPos : ∀ n, 0 < Den n)
    (hDenBound : ∀ n, Den n ≤ D * (30 : ℝ) ^ n)
    (vInt wInt : ℕ → ℤ)
    (hvcast : ∀ n, (vInt n : ℝ) = -(Den (n + 1) * (A1seq (n + 1) + A2seq (n + 1))))
    (hwcast : ∀ n, (wInt n : ℝ) = Den (n + 1) * A2seq (n + 1))
    (hdec1 : ∀ n, E1 n = A1seq n + Bseq n * Real.log (2 / 3))
    (hdec2 : ∀ n, E2 n = A2seq n - Bseq n * Real.log 2) :
    ∃ (v w : ℕ → ℤ) (A B ρ Q : ℝ),
      0 < A ∧ 0 < B ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      (∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n) ∧
      (∀ n, 0 < w n) ∧
      (∀ n, (w n : ℝ) ≤ B * Q ^ n) ∧
      (∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 60 := by
  refine ⟨vInt, wInt,
          8 * D * (810 / 1000),    -- A
          10000 * D * 30 * 1500,   -- B
          810 / 1000,              -- ρ = 30 * 27/1000
          45000,                   -- Q = 30 * 1500
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · norm_num
  · norm_num
  · norm_num
  · -- hsmall
    intro n
    have hDenAbsBound : ∀ m, |Den m| ≤ D * (30 : ℝ) ^ m :=
      fun m => (abs_of_pos (hDenPos m)).symm ▸ hDenBound m
    have hsharp := form_decay_sharper A1seq A2seq Bseq Den D 30
      (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 30)
      hDenAbsBound hdec1 hdec2 (n + 1)
    have hlhs : |Den (n + 1) * ((A1seq (n + 1) + A2seq (n + 1)) * Real.log 2 - A2seq (n + 1) * Real.log 3)|
        = |(vInt n : ℝ) * Real.log 2 + (wInt n : ℝ) * Real.log 3| := by
      rw [hvcast n, hwcast n]
      rw [show -(Den (n+1) * (A1seq (n+1) + A2seq (n+1))) * Real.log 2 +
              Den (n+1) * A2seq (n+1) * Real.log 3
          = -(Den (n+1) * ((A1seq (n+1) + A2seq (n+1)) * Real.log 2 - A2seq (n+1) * Real.log 3))
          by ring]
      rw [abs_neg]
    rw [hlhs] at hsharp
    have hrhs : (8 * D) * ((30 : ℝ) * (27 / 1000)) ^ (n + 1) =
        8 * D * (810 / 1000) * (810 / 1000) ^ n := by
      rw [pow_succ]; norm_num; ring
    rw [hrhs] at hsharp
    exact hsharp
  · -- hwpos
    intro n
    have hreal : (0 : ℝ) < (wInt n : ℝ) := by
      rw [hwcast n]
      exact hwpos_connector Den hDenPos n
    exact_mod_cast hreal
  · -- hwden
    intro n
    rw [hwcast n]
    have h := hwden_connector_1500 Den D 30
      (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 30) hDenPos hDenBound n
    simp only [wPos] at h
    convert h using 2
    norm_num
  · -- hdet
    intro n
    intro heq
    have heqR : (wInt n : ℝ) * (vInt (n + 1) : ℝ) = (wInt (n + 1) : ℝ) * (vInt n : ℝ) := by
      have : ((wInt n * vInt (n + 1) : ℤ) : ℝ) = ((wInt (n + 1) * vInt n : ℤ) : ℝ) :=
        by exact_mod_cast congrArg (Int.cast (R := ℝ)) heq
      push_cast at this
      linarith
    rw [hwcast n, hvcast (n + 1), hwcast (n + 1), hvcast n] at heqR
    apply hdet_concrete Den hDenPos n
    simp only [wCoord, vCoord]
    nlinarith [heqR]
  · -- hexp: log(45000) / log((810/1000)⁻¹) ≤ 60
    have hρinv : ((810 : ℝ) / 1000)⁻¹ = 1000 / 810 := by norm_num
    rw [hρinv]
    have hlog_pos : 0 < Real.log (1000 / 810) := Real.log_pos (by norm_num)
    rw [div_le_iff₀ hlog_pos]
    have hpow_bound : (45000 : ℝ) ≤ (1000 / 810 : ℝ) ^ 60 := by norm_num
    have hlog_ineq : Real.log 45000 ≤ Real.log ((1000 / 810 : ℝ) ^ 60) :=
      Real.log_le_log (by norm_num) hpow_bound
    rw [Real.log_pow] at hlog_ineq
    linarith

/-- **The four interface clauses with CONCRETE witnesses (C = 30).**

Exposes exactly the four "form" clauses (`hsmall`, `hwpos`, `hwden`, `hdet`) used inside
`osalikhov_twolog_interface_of_inputs_c30`, but with the witness constants made explicit so the
downstream numeric certificate can be discharged:
  `A = 8*D*(810/1000)`, `B = 10000*D*30*1500`, `ρ = 810/1000`, `Q = 45000`. -/
theorem interface_clauses_c30
    (Den : ℕ → ℝ) (D : ℝ)
    (hDpos   : 0 < D)
    (hDenPos : ∀ n, 0 < Den n)
    (hDenBound : ∀ n, Den n ≤ D * (30 : ℝ) ^ n)
    (vInt wInt : ℕ → ℤ)
    (hvcast : ∀ n, (vInt n : ℝ) = -(Den (n + 1) * (A1seq (n + 1) + A2seq (n + 1))))
    (hwcast : ∀ n, (wInt n : ℝ) = Den (n + 1) * A2seq (n + 1))
    (hdec1 : ∀ n, E1 n = A1seq n + Bseq n * Real.log (2 / 3))
    (hdec2 : ∀ n, E2 n = A2seq n - Bseq n * Real.log 2) :
    (∀ n, |(vInt n : ℝ) * Real.log 2 + (wInt n : ℝ) * Real.log 3| ≤
        (8 * D * (810 / 1000)) * (810 / 1000) ^ n) ∧
    (∀ n, 0 < wInt n) ∧
    (∀ n, (wInt n : ℝ) ≤ (10000 * D * 30 * 1500) * (45000 : ℝ) ^ n) ∧
    (∀ n, wInt n * vInt (n + 1) ≠ wInt (n + 1) * vInt n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- hsmall
    intro n
    have hDenAbsBound : ∀ m, |Den m| ≤ D * (30 : ℝ) ^ m :=
      fun m => (abs_of_pos (hDenPos m)).symm ▸ hDenBound m
    have hsharp := form_decay_sharper A1seq A2seq Bseq Den D 30
      (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 30)
      hDenAbsBound hdec1 hdec2 (n + 1)
    have hlhs : |Den (n + 1) * ((A1seq (n + 1) + A2seq (n + 1)) * Real.log 2 - A2seq (n + 1) * Real.log 3)|
        = |(vInt n : ℝ) * Real.log 2 + (wInt n : ℝ) * Real.log 3| := by
      rw [hvcast n, hwcast n]
      rw [show -(Den (n+1) * (A1seq (n+1) + A2seq (n+1))) * Real.log 2 +
              Den (n+1) * A2seq (n+1) * Real.log 3
          = -(Den (n+1) * ((A1seq (n+1) + A2seq (n+1)) * Real.log 2 - A2seq (n+1) * Real.log 3))
          by ring]
      rw [abs_neg]
    rw [hlhs] at hsharp
    have hrhs : (8 * D) * ((30 : ℝ) * (27 / 1000)) ^ (n + 1) =
        8 * D * (810 / 1000) * (810 / 1000) ^ n := by
      rw [pow_succ]; norm_num; ring
    rw [hrhs] at hsharp
    exact hsharp
  · -- hwpos
    intro n
    have hreal : (0 : ℝ) < (wInt n : ℝ) := by
      rw [hwcast n]
      exact hwpos_connector Den hDenPos n
    exact_mod_cast hreal
  · -- hwden
    intro n
    rw [hwcast n]
    have h := hwden_connector_1500 Den D 30
      (le_of_lt hDpos) (by norm_num : (1:ℝ) ≤ 30) hDenPos hDenBound n
    simp only [wPos] at h
    convert h using 2
    norm_num
  · -- hdet
    intro n
    intro heq
    have heqR : (wInt n : ℝ) * (vInt (n + 1) : ℝ) = (wInt (n + 1) : ℝ) * (vInt n : ℝ) := by
      have : ((wInt n * vInt (n + 1) : ℤ) : ℝ) = ((wInt (n + 1) * vInt n : ℤ) : ℝ) :=
        by exact_mod_cast congrArg (Int.cast (R := ℝ)) heq
      push_cast at this
      linarith
    rw [hwcast n, hvcast (n + 1), hwcast (n + 1), hvcast n] at heqR
    apply hdet_concrete Den hDenPos n
    simp only [wCoord, vCoord]
    nlinarith [heqR]

end OSalikhovAssembly
