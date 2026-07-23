import Propositio.NumberTheory.Diophantine.OSalikhovHdet

/-!
# Dominant-ratio bounds `A1, A2 ≤ B` — ELEMENTARY (no Poincaré–Perron)

The `hsmall` analytic crux needs the rationals `A1, A2` to be bounded by the residue `B` (so that
the cleared form `V = (A2·E1 − A1·E2)/B` inherits the integral decay rate rather than blowing up).
An adversarial-recon pass declared this **blocked** — "`A2/B` bounded ⇔ both grow at the common rate
`λ_max`, a Poincaré–Perron fact absent from mathlib."  **That is wrong.**

The difference `Z = K·B − X` (for `X = A1` or `A2`) is **itself a solution** of the oSALIKHOV
recurrence (the recurrence is linear), so positivity of `Z` propagates by the *same* `pos_mono`
argument used for `A2 > 0` — no dominant-root asymptotics.  A positive non-decreasing base window for
`Z` forces `Z(n) > 0`, i.e. `X(n) < K·B(n)`, for all `n`.  Numerically `A2/B ≈ 0.693`,
`A1/B ≈ 0.405`, so **`K = 1` works**: `A1seq ≤ Bseq` and `A2seq ≤ Bseq` for all `n`.

Consequence (recurrence side of `hsmall`): `|V| = |A2·E1 − A1·E2|/B ≤ (A2/B)|E1| + (A1/B)|E2| ≤
|E1| + |E2| ≤ 8·(1/32)ⁿ` — the uncleared two-log form decays at the integral rate `1/32`, so after
lcm-clearing `Den·|V| ≤ 8D·(C/32)ⁿ` with `ρ = C/32 < 1` (given the Apéry `Den ≤ D·Cⁿ` bound — the
one genuinely Phase-2-gated ingredient that remains).  This is far sharper than
`form_decay_of_decomp`'s crude `ρ = 1500·21/(1100·32) = 315/352 ≈ 0.895` and is what brings the
measure exponent down toward the `μ ≤ 22` budget. -/

namespace OSalikhovRatio

set_option linter.unusedSimpArgs false

open OSalikhovHeight OSalikhovSequences OSalikhovHdet OSalikhovCasoratian

/-- **Dominant-ratio bound (generic).**  If `K·B − X` is positive and non-decreasing on a base window
`k, k+1, k+2`, then `X(n) ≤ K·B(n)` for every `n ≥ k`.  Both `X` and `B` are solutions of the
oSALIKHOV `ℝ`-recurrence; the difference `K·B − X` is the solution to which `solution_pos` applies. -/
theorem le_smul_of_diff_pos (X B : ℕ → ℝ) (K : ℝ)
    (hX : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (hB : ∀ n, p3R n * B (n + 3) + p2R n * B (n + 2) + p1R n * B (n + 1) + p0R n * B n = 0)
    (k : ℕ) (h1 : 0 < K * B k - X k)
    (h2 : K * B k - X k ≤ K * B (k + 1) - X (k + 1))
    (h3 : K * B (k + 1) - X (k + 1) ≤ K * B (k + 2) - X (k + 2)) :
    ∀ m, X (k + m) ≤ K * B (k + m) := by
  have hrecZ : ∀ n, p3R n * (K * B (n + 3) - X (n + 3)) + p2R n * (K * B (n + 2) - X (n + 2))
      + p1R n * (K * B (n + 1) - X (n + 1)) + p0R n * (K * B n - X n) = 0 := by
    intro n; linear_combination K * hB n - hX n
  have hpos := OSalikhovHeight.solution_pos (fun n => K * B n - X n) hrecZ k h1 h2 h3
  intro m
  have := hpos m
  simp only at this
  linarith

/-- **`A2seq ≤ Bseq` for all `n`** (`K = 1`; base window `B−A2 = 1/30, 251/60, 515023/120 > 0`,
increasing). -/
theorem A2seq_le_Bseq : ∀ n, A2seq n ≤ Bseq n := by
  have h := le_smul_of_diff_pos A2seq Bseq 1 OSalikhovSequences.A2seq_rec Bseq_rec 0
    (by simp only [A2seq, Bseq, seqR_zero]; norm_num)
    (by simp only [A2seq, Bseq, seqR_zero, seqR_one]; norm_num)
    (by simp only [A2seq, Bseq, seqR_one, seqR_two]; norm_num)
  intro n; have := h n; simpa using this

/-- **`A1seq ≤ Bseq` for all `n`** (`K = 1`; base window `B−A1 = 1/30, 1409/180, 49693343/3240 > 0`,
increasing). -/
theorem A1seq_le_Bseq : ∀ n, A1seq n ≤ Bseq n := by
  have h := le_smul_of_diff_pos A1seq Bseq 1 OSalikhovHdet.A1seq_rec Bseq_rec 0
    (by simp only [A1seq, Bseq, seqR_zero]; norm_num)
    (by simp only [A1seq, Bseq, seqR_zero, seqR_one]; norm_num)
    (by simp only [A1seq, Bseq, seqR_one, seqR_two]; norm_num)
  intro n; have := h n; simpa using this

end OSalikhovRatio
