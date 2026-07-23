import Mathlib.Tactic

/-!
# Geometric growth bound for linearly-recurrent sequences

A self-contained upper bound: if a real sequence satisfies the sub-multiplicative three-term bound
`|X(n+3)| ≤ K·(|X(n+2)| + |X(n+1)| + |X(n)|)` and the geometric rate `R` is chosen large enough that
`K·(R² + R + 1) ≤ R³` (e.g. `R ≥ 3K+1`), then `|X(n)| ≤ M·Rⁿ` for all `n`, given the base window
`|X 0| ≤ M`, `|X 1| ≤ M·R`, `|X 2| ≤ M·R²`.

This is the tractable "upper half" of Poincaré–Perron for an order-3 recurrence (no asymptotic
constant, just domination).  Applied to the oSALIKHOV sequences `A1, A2, B` — whose coefficient
ratios `|pᵢ(n)/p₃(n)|` are bounded (→ the indicial roots) — it supplies the **height** input `hwden`
of the prize interface.  (The matching *lower* bound on `|B|`, needed for `hsmall`, is the genuinely
hard Poincaré–Perron direction and is not addressed here.)
-/

namespace RecurrenceGrowth

/-- **Geometric domination of a sub-multiplicative order-3 recurrence.** -/
theorem growth_bound (X : ℕ → ℝ) (K R M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hrec : ∀ n, |X (n + 3)| ≤ K * (|X (n + 2)| + |X (n + 1)| + |X n|))
    (hRcond : K * (R ^ 2 + R + 1) ≤ R ^ 3)
    (hb0 : |X 0| ≤ M) (hb1 : |X 1| ≤ M * R) (hb2 : |X 2| ≤ M * R ^ 2) :
    ∀ n, |X n| ≤ M * R ^ n := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  -- carry a 3-window through the induction
  have main : ∀ n, |X n| ≤ M * R ^ n ∧ |X (n + 1)| ≤ M * R ^ (n + 1)
      ∧ |X (n + 2)| ≤ M * R ^ (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using hb0, by simpa using hb1, by simpa using hb2⟩
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hRm : (0 : ℝ) ≤ M * R ^ m := by positivity
      refine ⟨by simpa using h1, by simpa using h2, ?_⟩
      have hstep : |X (m + 3)| ≤ M * R ^ (m + 3) := by
        calc |X (m + 3)| ≤ K * (|X (m + 2)| + |X (m + 1)| + |X m|) := hrec m
          _ ≤ K * (M * R ^ (m + 2) + M * R ^ (m + 1) + M * R ^ m) := by
              apply mul_le_mul_of_nonneg_left _ hK; gcongr
          _ = K * (R ^ 2 + R + 1) * (M * R ^ m) := by ring
          _ ≤ R ^ 3 * (M * R ^ m) := by
              exact mul_le_mul_of_nonneg_right hRcond hRm
          _ = M * R ^ (m + 3) := by ring
      simpa [show m + 1 + 2 = m + 3 from rfl] using hstep
  exact fun n => (main n).1

/-- A convenient choice: `R = 3K+1` (with `K ≥ 0`) satisfies `K(R²+R+1) ≤ R³`. -/
theorem rcond_of_three_K_add_one (K : ℝ) (hK : 0 ≤ K) :
    K * ((3 * K + 1) ^ 2 + (3 * K + 1) + 1) ≤ (3 * K + 1) ^ 3 := by
  nlinarith [sq_nonneg K, mul_nonneg hK (sq_nonneg K), mul_nonneg hK hK]

end RecurrenceGrowth
