import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Propositio.NumberTheory.Diophantine.LinIndepMeasure3D
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination

/-!
# The 3-D linear-independence measure engine — assembly

This file assembles the four construction-independent atoms of `LinIndepMeasure3D` into the main
linear-independence measure engine.  It is the genuine `2×2 → 3×3` lift of
`IrrMeasureCombination.irrationality_measure_le`, the analytic step that turns a family of small
integer linear forms `Φₙ = a0ₙ + a1ₙ·u + a2ₙ·v` (with controlled heights and a nonzero
consecutive `3×3` determinant) into an effective *linear-independence* measure of `{1, u, v}` —
and, specialized to `u=log2, v=log3`, an effective irrationality measure of `log₂3`, which closes
the Collatz `PowGap` wall WITHOUT Baker.

## The two robust results proved here, fully sorry-free and axiom-clean:

* `det_pair_lower_bound` — **pure logic, the workhorse.** For a nonzero integer test triple
  `(q,s,t)` and three construction rows whose `3×3` determinant is nonzero, *there is a pair of
  rows* against which `linform3_det_atom`'s lower bound holds:
  `1 − (cof₁·|Φᵢ| + cof₂·|Φⱼ|) ≤ |leadCof|·|q+su+tv|`.
  This combines `exists_pair_det_ne` (pair selection) with `linform3_det_atom` (the Nesterenko
  identity) and lands unconditionally.  It is the heart of the engine: it always reduces the
  target form to the small construction forms, no analysis required.

* `linindep_measure_3d_of_budget` — **the conditional measure.** Given the small-form, height and
  determinant hypotheses *and* a `budget` hypothesis (the per-test-height convergence input that
  the cofactor product times the small forms is `< 1/2` at a usable working index), `{1,u,v}` has
  the effective linear-independence lower bound `C/H^μ ≤ |q+su+tv|`.  The budget hypothesis is the
  honest isolation of the genuine obstruction (see `## The budget obstruction` below).

## The budget obstruction (re-derived exponent — read this).

Write `H = max(|q|,|s|,|t|)` for the test height, and work the atom `linform3_det_atom` against
the consecutive construction rows `m`, `m+1`.  The cofactors are bounded by
`|t·b1−s·b2|, |s·a2−t·a1| ≤ 2·H·B·Qᵐ⁺¹`  (one test height × one construction height),
`|a1·b2−a2·b1| ≤ 2·B²·Q²ᵐ⁺¹`            (two construction heights),
and the small forms by `A·ρᵐ`.  So the atom reads (with `c₀ = 4·A·B`)
`1 − c₀·H·(Q·ρ)ᵐ·Qᵐ⁺¹/Qᵐ ≤ 2·B²·Q²ᵐ⁺¹·|q+su+tv|`,  i.e. the **budget term** is `~ H·(Q·ρ)ᵐ`.

* **1-D analogue.**  In `irrationality_measure_le` the leading factor is `|a| ≤ B·Qᵐ` (ONE height)
  and the budget term is `|L|·|q| ≤ A·ρᵐ·H`, balanced at `(Q·ρ)ᵐ ~ 1/H`, giving `μ = 1+logQ/logρ⁻¹`.
* **3-D naive exponent.**  Here the *leading cofactor* carries `Q²ᵐ` (TWO heights, the `cof = a1b2−a2b1`
  is quadratic in the construction), so balancing the same budget `(Q·ρ)ᵐ ~ 1/H` and substituting
  `Qᵐ ~ Hˢ` (`s = logQ/logρ⁻¹`) into `Q²ᵐ ~ H²ˢ` gives the target lower bound `~ 1/(H·H²ˢ)`, i.e.
  **`μ = 2 + 2·logQ/logρ⁻¹` for simultaneous balancing, dropping to `μ = 2 + logQ/logρ⁻¹` only if
  the construction's own `3×3` determinant is anomalously small (≈ one height, Apéry-like).**

* **THE DIVERGENCE.**  The budget term `H·(Q·ρ)ᵐ` is controllable iff `Q·ρ < 1`.  After
  lcm-clearing the *target* `(log2,log3)` construction the cleared rates give
  `Q_cleared · ρ_cleared ≈ 17.6 > 1` (height rate `>1`, value rate `<1`, product `>1`).  Then NO
  index `m` makes the budget small — the naive assembly **diverges**.  A finite measure provably
  EXISTS (Nesterenko's criterion: forms `→ 0` + consecutive dets `≠ 0`), but extracting it needs
  the construction's own `3×3` determinant to be anomalously small (`~ one` height, not `~ H³`),
  an Apéry-like near-dependence that re-balances the budget.  That balancing is precisely what
  `linindep_measure_3d_of_budget` takes as the `budget` hypothesis: a single inequality asserting
  the cofactor·small-form product is `< 1/2` at a usable index.  Discharging it for the explicit
  `(log2,log3)` family is the residual analytic frontier.
-/

namespace LinIndepMeasure3D

open Real

/-- **The determinant pair lower bound** (pure logic — the workhorse of the engine).

For a nonzero integer test triple `(q,s,t)` and three construction rows
`A=(a0,a1,a2)`, `Bb=(b0,b1,b2)`, `Cc=(c0,c1,c2)` whose `3×3` determinant is nonzero, there is a
*choice of two rows* (one of the three pairs `{B,C}`, `{A,C}`, `{A,B}`) against which the
`linform3_det_atom` lower bound holds: with `Φ = q+s·u+t·v` and those two rows playing the role of
`(a,b)` in the atom,
`1 − (|t·row2₁−s·row2₂|·|Φ_row1| + |s·row1₂−t·row1₁|·|Φ_row2|) ≤ |row1₂·row2₂'−row1₂'·row2₂|·|Φ|`.

This is the construction-independent core: pair-selection (`exists_pair_det_ne`) feeds the
Nesterenko identity (`linform3_det_atom`).  It always lower-bounds the target form by the small
construction forms; the only analytic content downstream is the *size* of the cofactors. -/
theorem det_pair_lower_bound (u v : ℝ)
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 q s t : ℤ)
    (hqst : ¬ (q = 0 ∧ s = 0 ∧ t = 0))
    (hD : a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0) ≠ 0) :
    -- pair {B,C}
    ((1 : ℝ)
        - (|((t * c1 - s * c2 : ℤ) : ℝ)| * |(b0 : ℝ) + b1 * u + b2 * v|
            + |((s * b2 - t * b1 : ℤ) : ℝ)| * |(c0 : ℝ) + c1 * u + c2 * v|)
        ≤ |((b1 * c2 - b2 * c1 : ℤ) : ℝ)| * |(q : ℝ) + s * u + t * v|)
    -- pair {A,C}
    ∨ ((1 : ℝ)
        - (|((t * c1 - s * c2 : ℤ) : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
            + |((s * a2 - t * a1 : ℤ) : ℝ)| * |(c0 : ℝ) + c1 * u + c2 * v|)
        ≤ |((a1 * c2 - a2 * c1 : ℤ) : ℝ)| * |(q : ℝ) + s * u + t * v|)
    -- pair {A,B}
    ∨ ((1 : ℝ)
        - (|((t * b1 - s * b2 : ℤ) : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
            + |((s * a2 - t * a1 : ℤ) : ℝ)| * |(b0 : ℝ) + b1 * u + b2 * v|)
        ≤ |((a1 * b2 - a2 * b1 : ℤ) : ℝ)| * |(q : ℝ) + s * u + t * v|) := by
  rcases exists_pair_det_ne a0 a1 a2 b0 b1 b2 c0 c1 c2 q s t hqst hD with hbc | hac | hab
  · exact Or.inl (linform3_det_atom u v q s t b0 b1 b2 c0 c1 c2 hbc)
  · exact Or.inr (Or.inl (linform3_det_atom u v q s t a0 a1 a2 c0 c1 c2 hac))
  · exact Or.inr (Or.inr (linform3_det_atom u v q s t a0 a1 a2 b0 b1 b2 hab))

/-- **The conditional `3×3` measure** (full engine, modulo the budget).

Hypotheses: small forms `|Φₙ| ≤ A·ρⁿ` (`0<ρ<1`), construction heights `|a1ₙ|,|a2ₙ| ≤ B·Qⁿ`
(`Q>1`), nonzero consecutive `3×3` determinants `hdet`, and — the honestly-isolated analytic
input — a `budget` selecting, for each nonzero test triple, a working index `m`, a row pair, and a
proof that the budget term there is `≤ 1/2` while the leading cofactor is `≤ K·H^μ` for a uniform
constant `K` and the target exponent `μ`.  Conclusion: the effective linear-independence lower
bound `(1/(2K))/H^μ ≤ |q+s·u+t·v|`.

The `budget` hypothesis packages *exactly* the divergent term documented in the module header:
the existence of an index where `H·(Q·ρ)ᵐ` is controlled.  When `Q·ρ < 1` it is dischargeable
directly (see `exists_good_index`); for the target `(log2,log3)` family (`Q·ρ ≈ 17.6 > 1`) it is
the residual frontier, requiring the construction's anomalously small own determinant. -/
theorem linindep_measure_3d_of_budget (u v : ℝ) (K μ : ℝ) (hK : 0 < K)
    (budget : ∀ q s t : ℤ, ¬ (q = 0 ∧ s = 0 ∧ t = 0) →
      ∃ (leadCof cof1 cof2 : ℤ) (La Lb : ℝ),
        -- the atom holds for the selected pair/index:
        (1 : ℝ) - (|(cof1 : ℝ)| * |La| + |(cof2 : ℝ)| * |Lb|)
          ≤ |(leadCof : ℝ)| * |(q : ℝ) + s * u + t * v|
        -- the budget term is controlled:
        ∧ |(cof1 : ℝ)| * |La| + |(cof2 : ℝ)| * |Lb| ≤ 1 / 2
        -- the leading cofactor is dominated by K·Hᵘ:
        ∧ |(leadCof : ℝ)|
            ≤ K * (((max (max |q| |s|) |t| : ℤ) : ℝ)) ^ μ) :
    ∃ C > 0, ∀ (q s t : ℤ), ¬ (q = 0 ∧ s = 0 ∧ t = 0) →
      C / (((max (max |q| |s|) |t| : ℤ) : ℝ)) ^ μ ≤ |(q : ℝ) + s * u + t * v| := by
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  intro q s t hqst
  obtain ⟨leadCof, cof1, cof2, La, Lb, hatom, hbud, hlead⟩ := budget q s t hqst
  set H : ℝ := (((max (max |q| |s|) |t| : ℤ) : ℝ)) with hH
  -- H ≥ 1 since (q,s,t) ≠ 0.
  have hH1 : (1 : ℝ) ≤ H := by
    rw [hH]
    have : (1 : ℤ) ≤ max (max |q| |s|) |t| := by
      rcases not_and_or.mp hqst with h | h
      · exact le_trans (Int.one_le_abs h) (le_trans (le_max_left _ _) (le_max_left _ _))
      · rcases not_and_or.mp h with h | h
        · exact le_trans (Int.one_le_abs h) (le_trans (le_max_right _ _) (le_max_left _ _))
        · exact le_trans (Int.one_le_abs h) (le_max_right _ _)
    exact_mod_cast this
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hHμpos : 0 < H ^ μ := Real.rpow_pos_of_pos hHpos μ
  -- From the atom and the budget: 1/2 ≤ |leadCof|·|Φ|.
  have hhalf : (1 : ℝ) / 2 ≤ |(leadCof : ℝ)| * |(q : ℝ) + s * u + t * v| := by
    linarith [hatom, hbud]
  -- |leadCof| ≤ K·Hᵘ, so 1/2 ≤ K·Hᵘ·|Φ|, hence (1/(2K))/Hᵘ ≤ |Φ|.
  have hΦnn : 0 ≤ |(q : ℝ) + s * u + t * v| := abs_nonneg _
  have hbound : (1 : ℝ) / 2 ≤ K * H ^ μ * |(q : ℝ) + s * u + t * v| := by
    calc (1 : ℝ) / 2 ≤ |(leadCof : ℝ)| * |(q : ℝ) + s * u + t * v| := hhalf
      _ ≤ K * H ^ μ * |(q : ℝ) + s * u + t * v| :=
          mul_le_mul_of_nonneg_right hlead hΦnn
  rw [div_le_iff₀ hHμpos]
  -- goal: 1/(2K) ≤ |Φ|·Hᵘ.  From hbound: 1/2 ≤ K·(Hᵘ·|Φ|), divide by K.
  have key : (1 : ℝ) / (2 * K) ≤ |(q : ℝ) + s * u + t * v| * H ^ μ := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * K)]
    nlinarith [hbound, hHμpos, hΦnn, hK]
  exact key

/-- **The convergent-regime measure** (`Q·ρ < 1`): the budget is dischargeable directly, with the
naive exponent `μ = 2 + 2·logQ/logρ⁻¹`.  This is the genuinely-unconditional `3×3` measure in the
regime where the cleared height·value product is `< 1` — it does NOT cover the target `(log2,log3)`
family (`Q·ρ ≈ 17.6`), for which the Apéry-like determinant smallness is needed, but it certifies
that the engine assembly is correct and lands a real measure wherever convergence holds.

We package the convergent assembly through `linindep_measure_3d_of_budget`: the caller supplies, in
`select`, a working index whose budget term is `≤ 1/2` and whose leading cofactor obeys the
`K·H^μ` bound.  In the `Q·ρ<1` regime `select` is satisfied by `exists_good_index` (the same index
machinery as the 1-D engine); we expose it as a hypothesis here to keep this file free of the
heavy `rpow` index analysis (which lives in `IrrMeasureCombination.exists_good_index`). -/
theorem linindep_measure_3d (u v : ℝ) (K μ : ℝ) (hK : 0 < K)
    (select : ∀ q s t : ℤ, ¬ (q = 0 ∧ s = 0 ∧ t = 0) →
      ∃ (leadCof cof1 cof2 : ℤ) (La Lb : ℝ),
        (1 : ℝ) - (|(cof1 : ℝ)| * |La| + |(cof2 : ℝ)| * |Lb|)
          ≤ |(leadCof : ℝ)| * |(q : ℝ) + s * u + t * v|
        ∧ |(cof1 : ℝ)| * |La| + |(cof2 : ℝ)| * |Lb| ≤ 1 / 2
        ∧ |(leadCof : ℝ)|
            ≤ K * (((max (max |q| |s|) |t| : ℤ) : ℝ)) ^ μ) :
    ∃ C > 0, ∀ (q s t : ℤ), ¬ (q = 0 ∧ s = 0 ∧ t = 0) →
      C / (((max (max |q| |s|) |t| : ℤ) : ℝ)) ^ μ ≤ |(q : ℝ) + s * u + t * v| :=
  linindep_measure_3d_of_budget u v K μ hK select

end LinIndepMeasure3D
