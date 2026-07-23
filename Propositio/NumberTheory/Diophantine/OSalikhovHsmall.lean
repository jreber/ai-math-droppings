import Propositio.NumberTheory.Diophantine.OSalikhovDecomp

/-!
# Conditional `hsmall`: the form `Den·V` decays once the connectors are in place

The prize interface's `hsmall` asks that the lcm-cleared two-log form `Den_n·V_n`,
`V_n = (A1+A2)·log2 − A2·log3`, decays geometrically.  Via the shared-B elimination
`B·V = A2·E1 − A1·E2`, this combines the **proved** integral decays `|E1 n| ≤ 3(1/100)ⁿ`,
`|E2 n| ≤ 5(1/32)ⁿ` (`OSalikhovDecomp`) with the recurrence-side growth bounds `|A1|,|A2| ≤ M·1500ⁿ`
(`OSalikhovHeight.solution_upper`), `|B| ≥ c·1100ⁿ` (`solution_lower`-style), and the lcm bound
`Den ≤ D·21ⁿ`.

This file proves the **assembly**: given those four ingredients, `Den·V` decays at rate
`315/352 = (21·1500)/(32·1100) ≈ 0.895 < 1`.  So `hsmall` reduces to exactly (a) the partial-fraction
decomposition `B·V = A2·E1 − A1·E2` and (b) the denominator bound `Den ≤ D·21ⁿ` — both Phase-2 items.
-/

namespace OSalikhovTwoLog

/-- **`hsmall` assembly.**  From the shared-B decomposition, the recurrence growth bounds
`|A1|,|A2| ≤ M·1500ⁿ`, `|B| ≥ c·1100ⁿ`, and the lcm bound `|Den| ≤ D·21ⁿ`, the cleared two-log form
`Den·((A1+A2)log2 − A2log3)` decays at rate `315/352 < 1`. -/
theorem form_decay_of_decomp
    (A1 A2 B Den : ℕ → ℝ) (c M D : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hA1 : ∀ n, |A1 n| ≤ M * 1500 ^ n) (hA2 : ∀ n, |A2 n| ≤ M * 1500 ^ n)
    (hB : ∀ n, c * 1100 ^ n ≤ |B n|) (hDen : ∀ n, |Den n| ≤ D * 21 ^ n)
    (hdecomp : ∀ n, B n * ((A1 n + A2 n) * Real.log 2 - A2 n * Real.log 3)
      = A2 n * E1 n - A1 n * E2 n) :
    ∀ n, |Den n * ((A1 n + A2 n) * Real.log 2 - A2 n * Real.log 3)|
      ≤ (8 * D * M / c) * (315 / 352) ^ n := by
  intro n
  set V : ℝ := (A1 n + A2 n) * Real.log 2 - A2 n * Real.log 3 with hV
  have hBpos : 0 < |B n| := lt_of_lt_of_le (by positivity) (hB n)
  -- both integrals dominated by (1/32)ⁿ
  have hE1 : |E1 n| ≤ 3 * (1 / 32) ^ n := by
    refine (E1_abs_le n).trans ?_
    gcongr <;> norm_num
  have hE2 : |E2 n| ≤ 5 * (1 / 32) ^ n := E2_abs_le_sharp n
  -- |B|·|V| ≤ |A2||E1| + |A1||E2| ≤ M·1500ⁿ·8·(1/32)ⁿ
  have hBV : |B n| * |V| ≤ (M * 1500 ^ n) * (8 * (1 / 32) ^ n) := by
    have hchain : |B n| * |V| ≤ |A2 n| * |E1 n| + |A1 n| * |E2 n| := by
      rw [← abs_mul, hdecomp n]
      calc |A2 n * E1 n - A1 n * E2 n|
          ≤ |A2 n * E1 n| + |A1 n * E2 n| := by
            rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ = |A2 n| * |E1 n| + |A1 n| * |E2 n| := by rw [abs_mul, abs_mul]
    have ht1 : |A2 n| * |E1 n| ≤ (M * 1500 ^ n) * (3 * (1 / 32) ^ n) :=
      mul_le_mul (hA2 n) hE1 (abs_nonneg _) (by positivity)
    have ht2 : |A1 n| * |E2 n| ≤ (M * 1500 ^ n) * (5 * (1 / 32) ^ n) :=
      mul_le_mul (hA1 n) hE2 (abs_nonneg _) (by positivity)
    nlinarith [hchain, ht1, ht2]
  -- |V| ≤ M·1500ⁿ·8·(1/32)ⁿ / |B n|
  have hVbound : |V| ≤ (M * 1500 ^ n) * (8 * (1 / 32) ^ n) / |B n| := by
    rw [le_div_iff₀ hBpos]; nlinarith [hBV]
  -- assemble
  rw [abs_mul]
  have hstep : |Den n| * |V|
      ≤ (D * 21 ^ n) * ((M * 1500 ^ n) * (8 * (1 / 32) ^ n) / |B n|) :=
    mul_le_mul (hDen n) hVbound (abs_nonneg _) (by positivity)
  refine hstep.trans ?_
  -- (D·21ⁿ)·(M·1500ⁿ·8·(1/32)ⁿ / |B n|) ≤ (8DM/c)·(315/352)ⁿ
  have hbig : (M * 1500 ^ n) * (8 * (1 / 32) ^ n) / |B n|
      ≤ (M * 1500 ^ n) * (8 * (1 / 32) ^ n) / (c * 1100 ^ n) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (hB n)
  refine (mul_le_mul_of_nonneg_left hbig (by positivity)).trans ?_
  -- pure power identity
  have hc' : c ≠ 0 := hc.ne'
  have h1100 : (1100 : ℝ) ^ n ≠ 0 := by positivity
  have hbase : (315 / 352 : ℝ) ^ n = 21 ^ n * 1500 ^ n * (1 / 32) ^ n / 1100 ^ n := by
    rw [show (315 / 352 : ℝ) = 21 * 1500 * (1 / 32) / 1100 by norm_num, div_pow, mul_pow, mul_pow]
  have hcollapse : (D * 21 ^ n) * ((M * 1500 ^ n) * (8 * (1 / 32) ^ n) / (c * 1100 ^ n))
      = (8 * D * M / c) * (315 / 352) ^ n := by
    rw [hbase]; field_simp
  rw [hcollapse]

/-- The shared-B identity `B·V = A2·E1 − A1·E2` follows algebraically from the partial-fraction
decomposition `E1 = A1 + B·log(2/3)`, `E2 = A2 − B·log2` — so the `hdecomp` hypothesis of
`form_decay_of_decomp` reduces to the Phase-2 decomposition forms. -/
theorem decomp_identity (A1 A2 B : ℕ → ℝ) (n : ℕ)
    (hE1 : E1 n = A1 n + B n * Real.log (2 / 3))
    (hE2 : E2 n = A2 n - B n * Real.log 2) :
    B n * ((A1 n + A2 n) * Real.log 2 - A2 n * Real.log 3) = A2 n * E1 n - A1 n * E2 n := by
  rw [hE1, hE2, Real.log_div (by norm_num) (by norm_num)]
  ring

end OSalikhovTwoLog
