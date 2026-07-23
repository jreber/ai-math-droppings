import Propositio.NumberTheory.Diophantine.OSalikhovHdet

/-!
# `hwpos` and `hwden` interface connectors (consistent `w = Den·A2 > 0` convention)

The prize interface needs `0 < w n` (`hwpos`) and `w n ≤ B·Qⁿ` (`hwden`).  With the one-step-shifted,
sign-correct cleared coordinate `w n = Den(n+1)·A2seq(n+1)` (positive, since `A2seq > 0` on `≥1`),
both follow from the proved recurrence-side facts (`A2seq_pos`, `A2seq_height`) and abstract
properties of the lcm-clearing denominator `Den` (`Den > 0`, `Den ≤ D·Cⁿ` — the Phase-2 inputs).

This completes the "interface-ready" set: every clause of `osalikhov_twolog_interface` is now reduced
to the two Phase-2/3 inputs (the partial-fraction decomposition and the `Den` construction) via an
explicit connector — `hwpos`/`hwden` here, `hdet` via `OSalikhovHdet.hdet_of_casoratian`, `hsmall`
via `OSalikhovTwoLog.form_decay_sharper`.  (Note the sign convention: the final interface uses
`w = +Den·A2`, `v = −Den·(A1+A2)`; the `hdet` determinant is non-vanishing under negating both
coordinates, so `hdet_of_casoratian` applies unchanged.) -/

namespace OSalikhovHdet

open OSalikhovSequences

/-- The sign-correct cleared coordinate `wPos n = Den(n+1)·A2seq(n+1)`. -/
noncomputable def wPos (Den : ℕ → ℝ) (n : ℕ) : ℝ := Den (n + 1) * A2seq (n + 1)

/-- **`hwpos` connector.**  `0 < wPos n` from `A2seq > 0` (on `≥1`) and `Den > 0`. -/
theorem hwpos_connector (Den : ℕ → ℝ) (hDen : ∀ n, 0 < Den n) (n : ℕ) : 0 < wPos Den n := by
  have hA2 : 0 < A2seq (n + 1) := by
    have := A2seq_pos n; rwa [Nat.add_comm 1 n] at this
  exact mul_pos (hDen _) hA2

/-- **`hwden` connector.**  `wPos n ≤ (10000·D·C·4501)·(C·4501)ⁿ` from the height bound
`|A2seq m| ≤ 10000·4501ᵐ` and the lcm bound `Den ≤ D·Cⁿ`. -/
theorem hwden_connector (Den : ℕ → ℝ) (D C : ℝ) (hD : 0 ≤ D) (hC1 : 1 ≤ C)
    (hDenpos : ∀ n, 0 < Den n) (hDen : ∀ n, Den n ≤ D * C ^ n) (n : ℕ) :
    wPos Den n ≤ (10000 * D * C * 4501) * (C * 4501) ^ n := by
  have hA2h : A2seq (n + 1) ≤ 10000 * 4501 ^ (n + 1) :=
    (le_abs_self _).trans (A2seq_height (n + 1))
  have hA2nn : 0 ≤ A2seq (n + 1) := le_of_lt (by
    have := A2seq_pos n; rwa [Nat.add_comm 1 n] at this)
  have hDennn : 0 ≤ Den (n + 1) := le_of_lt (hDenpos _)
  have hDh : Den (n + 1) ≤ D * C ^ (n + 1) := hDen (n + 1)
  calc wPos Den n = Den (n + 1) * A2seq (n + 1) := rfl
    _ ≤ (D * C ^ (n + 1)) * (10000 * 4501 ^ (n + 1)) :=
        mul_le_mul hDh hA2h hA2nn (by positivity)
    _ = (10000 * D * C * 4501) * (C * 4501) ^ n := by
        rw [pow_succ, pow_succ, mul_pow]; ring

/-- **`hwden` connector (sharp, rate 1500).**  `wPos n ≤ (10000·D·C·1500)·(C·1500)ⁿ` using the
sharpened height bound `|A2seq m| ≤ 10000·1500ᵐ` (rate `1500` instead of `4501`).  With `C = 22`
this gives `Q = 22·1500 = 33000` (vs the crude `Q = 21·4501 = 94521`), improving the exponent
`logQ/logρ⁻¹` from `≈20.19` to `≈19.8 ≤ 21`. -/
theorem hwden_connector_1500 (Den : ℕ → ℝ) (D C : ℝ) (hD : 0 ≤ D) (hC1 : 1 ≤ C)
    (hDenpos : ∀ n, 0 < Den n) (hDen : ∀ n, Den n ≤ D * C ^ n) (n : ℕ) :
    wPos Den n ≤ (10000 * D * C * 1500) * (C * 1500) ^ n := by
  have hA2h : A2seq (n + 1) ≤ 10000 * 1500 ^ (n + 1) :=
    (le_abs_self _).trans (A2seq_height_1500 (n + 1))
  have hA2nn : 0 ≤ A2seq (n + 1) := le_of_lt (by
    have := A2seq_pos n; rwa [Nat.add_comm 1 n] at this)
  have hDennn : 0 ≤ Den (n + 1) := le_of_lt (hDenpos _)
  have hDh : Den (n + 1) ≤ D * C ^ (n + 1) := hDen (n + 1)
  calc wPos Den n = Den (n + 1) * A2seq (n + 1) := rfl
    _ ≤ (D * C ^ (n + 1)) * (10000 * 1500 ^ (n + 1)) :=
        mul_le_mul hDh hA2h hA2nn (by positivity)
    _ = (10000 * D * C * 1500) * (C * 1500) ^ n := by
        rw [pow_succ, pow_succ, mul_pow]; ring

end OSalikhovHdet
