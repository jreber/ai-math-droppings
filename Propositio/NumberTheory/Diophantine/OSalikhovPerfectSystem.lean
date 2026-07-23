import Propositio.NumberTheory.Diophantine.OrderThreeRecurrence

/-!
# The oSALIKHOV perfect system is non-degenerate (`W₃ ≠ 0`)

The three rational sequences `A1, A2, B` of the oSALIKHOV construction satisfy ONE homogeneous
order-3 recurrence with the explicit degree-5 *integer* coefficients below (extracted and verified
exact in `experiments/osalikhov_verify.clj`, indicial `3λ³ − 4325λ² − 79λ + 1`):
```
  p₃(n)·X(n+3) + p₂(n)·X(n+2) + p₁(n)·X(n+1) + p₀(n)·X(n) = 0 .
```
This file records those coefficients and proves the **non-degeneracy** of the perfect system: any
three solutions with the construction's verified initial data `A1(0..2), A2(0..2), B(0..2)` have
`W₃(n) ≠ 0` for every `n` (linear independence — the construction genuinely involves all of
`1, log2, log3` and never collapses).

`p₀(n) > 0` for all `n` (all coefficients positive) supplies the `OrderThreeRecurrence.casoratian_ne_zero`
hypothesis; the base value `W₃(0) = (1/30)·C₂(1) = −617/16200 ≠ 0` is a finite rational computation.

NOTE: this `W₃ ≠ 0` non-degeneracy is *necessary* for the engine's `hdet` (the 2×2 Casoratian
`C₂(n) = A1(n)A2(n+1) − A1(n+1)A2(n) ≠ 0`) but not sufficient — `C₂` is a genuine order-3 object
that does **not** telescope.  EARLIER notes claimed `hdet` therefore needs a Poincaré–Perron
asymptotic `C₂(n) = c·(λ_max·λ_mid)ⁿ(1+o(1))`; this is now **REFUTED** and `hdet`'s core is proved
ELEMENTARY in `OSalikhovCasoratian.lean`: `C₂` satisfies its own order-3 recurrence (exterior-square
of the companion matrix, `casoratian2_rec`), and the sign-folded `c(k) = (−1)ᵏ·C₂(k)` inherits the
`A2` sign pattern, so the `pos_mono` argument forces `c(k) > 0` (`casoratian2_ne_zero`) — no
dominant-root asymptotics.  See `OSalikhovCasoratian.lean` and `docs/projects/oSALIKHOV-construction-plan.md`.
-/

namespace OSalikhovPerfectSystem

open OrderThreeRecurrence

/-- `p₀(n) = 6304n⁵ + 50280n⁴ + 150136n³ + 207666n² + 130822n + 29316`. -/
def p0 (n : ℕ) : ℚ :=
  6304 * (n : ℚ) ^ 5 + 50280 * (n : ℚ) ^ 4 + 150136 * (n : ℚ) ^ 3
    + 207666 * (n : ℚ) ^ 2 + 130822 * (n : ℚ) + 29316

/-- `p₁(n) = −498016n⁵ − 4221128n⁴ − 13683996n³ − 21166742n² − 15563215n − 4329894`. -/
def p1 (n : ℕ) : ℚ :=
  -498016 * (n : ℚ) ^ 5 - 4221128 * (n : ℚ) ^ 4 - 13683996 * (n : ℚ) ^ 3
    - 21166742 * (n : ℚ) ^ 2 - 15563215 * (n : ℚ) - 4329894

/-- `p₂(n) = −27264800n⁵ − 244725800n⁴ − 842584448n³ − 1379554326n² − 1057909176n − 294706755`. -/
def p2 (n : ℕ) : ℚ :=
  -27264800 * (n : ℚ) ^ 5 - 244725800 * (n : ℚ) ^ 4 - 842584448 * (n : ℚ) ^ 3
    - 1379554326 * (n : ℚ) ^ 2 - 1057909176 * (n : ℚ) - 294706755

/-- `p₃(n) = 18912n⁵ + 179208n⁴ + 647844n³ + 1105722n² + 876609n + 249885`. -/
def p3 (n : ℕ) : ℚ :=
  18912 * (n : ℚ) ^ 5 + 179208 * (n : ℚ) ^ 4 + 647844 * (n : ℚ) ^ 3
    + 1105722 * (n : ℚ) ^ 2 + 876609 * (n : ℚ) + 249885

/-- `p₀(n) > 0` (all coefficients positive, `(n:ℚ) ≥ 0`). -/
theorem p0_pos (n : ℕ) : 0 < p0 n := by
  have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  unfold p0; positivity

/-- `p₃(n) > 0`. -/
theorem p3_pos (n : ℕ) : 0 < p3 n := by
  have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  unfold p3; positivity

/-- **Non-degeneracy of the oSALIKHOV perfect system.**  Any three sequences satisfying the order-3
recurrence with the construction's verified initial data are linearly independent: `W₃(n) ≠ 0 ∀n`.
The base value `W₃(0) = (1/30)·(A1(1)A2(2) − A1(2)A2(1)) = −617/16200 ≠ 0`. -/
theorem osalikhov_perfect_system (A1 A2 B : ℕ → ℚ)
    (hA1 : Recurrence p0 p1 p2 p3 A1) (hA2 : Recurrence p0 p1 p2 p3 A2)
    (hB : Recurrence p0 p1 p2 p3 B)
    (a10 : A1 0 = 0) (a11 : A1 1 = 199 / 36) (a12 : A1 2 = 3674885 / 648)
    (a20 : A2 0 = 0) (a21 : A2 1 = 189 / 20) (a22 : A2 2 = 1163381 / 120)
    (b0 : B 0 = 1 / 30) (b1 : B 1 = 409 / 30) (b2 : B 2 = 139867 / 10) :
    ∀ n, W3 A1 A2 B n ≠ 0 := by
  apply casoratian_ne_zero p0 p1 p2 p3 A1 A2 B hA1 hA2 hB
  · exact fun n => ne_of_gt (p0_pos n)
  · unfold W3
    rw [a10, a11, a12, a20, a21, a22, b0, b1, b2]
    norm_num

end OSalikhovPerfectSystem
