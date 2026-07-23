import Mathlib.Tactic

/-!
# Generic order-3 linear recurrence and its 3×3 Casoratian

The oSALIKHOV construction (`OSalikhovTwoLog`) has three rational sequences `A1, A2, B`
that all satisfy ONE homogeneous order-3 linear recurrence
`p₃(n)·X(n+3) + p₂(n)·X(n+2) + p₁(n)·X(n+1) + p₀(n)·X(n) = 0`
with the deg-5 integer polynomial coefficients verified in `experiments/osalikhov_verify.clj`
(indicial `3λ³ − 4325λ² − 79λ + 1`).  This is the *perfect system* underlying the prize.

This file is the order-3 analogue of `PadeRecurrenceGen` (order 2).  The key object is the
**3×3 Casoratian** `W₃(X,Y,Z)(n) = det [rows n,n+1,n+2; cols X,Y,Z]`.  Abel's identity for the
order-3 recurrence telescopes it:
`p₃(n)·W₃(n+1) = −p₀(n)·W₃(n)`,
so if `W₃(0) ≠ 0` and `p₀(n), p₃(n) ≠ 0` for all `n`, then `W₃(n) ≠ 0` for every `n` — i.e. the
three solutions are linearly independent (perfect system).  Coefficients are arbitrary `ℕ → K`
functions, so the machinery is construction-independent.
-/

namespace OrderThreeRecurrence

variable {K : Type*} [Field K]

/-- The homogeneous order-3 recurrence `p₃(n)·X(n+3) + p₂(n)·X(n+2) + p₁(n)·X(n+1) + p₀(n)·X(n) = 0`. -/
def Recurrence (p0 p1 p2 p3 : ℕ → K) (X : ℕ → K) : Prop :=
  ∀ n : ℕ, p3 n * X (n + 3) + p2 n * X (n + 2) + p1 n * X (n + 1) + p0 n * X n = 0

/-- The 3×3 Casoratian `W₃(n) = det [[X n, Y n, Z n], [X(n+1),…], [X(n+2),…]]` (first-row expansion). -/
def W3 (X Y Z : ℕ → K) (n : ℕ) : K :=
  X n * (Y (n + 1) * Z (n + 2) - Y (n + 2) * Z (n + 1))
    - Y n * (X (n + 1) * Z (n + 2) - X (n + 2) * Z (n + 1))
    + Z n * (X (n + 1) * Y (n + 2) - X (n + 2) * Y (n + 1))

set_option linter.unusedSectionVars false

/-- **Abel's identity (cleared form).**  `p₃(n)·W₃(n+1) = −p₀(n)·W₃(n)`.  The `p₂,p₁` parts of the
recurrence are multiples of rows already in the `(n+1)`-window determinant, so they drop out; only
the `p₀·X(n)` part survives, contributing the cyclic-shift `W₃(n)`. -/
theorem casoratian_step (p0 p1 p2 p3 : ℕ → K) (X Y Z : ℕ → K)
    (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y)
    (hZ : Recurrence p0 p1 p2 p3 Z) (n : ℕ) :
    p3 n * W3 X Y Z (n + 1) = - p0 n * W3 X Y Z n := by
  unfold W3
  have hx := hX n
  have hy := hY n
  have hz := hZ n
  linear_combination
    (Y (n + 1) * Z (n + 2) - Y (n + 2) * Z (n + 1)) * hx
    - (X (n + 1) * Z (n + 2) - X (n + 2) * Z (n + 1)) * hy
    + (X (n + 1) * Y (n + 2) - X (n + 2) * Y (n + 1)) * hz

/-- **Non-vanishing propagation.**  If `p₀(n) ≠ 0` and `W₃(n) ≠ 0`, then `W₃(n+1) ≠ 0`.
(Remarkably `p₃(n) ≠ 0` is *not* needed: when `W₃(n+1)=0` the `p₃·W₃(n+1)` term vanishes
regardless of `p₃`, so `p₀(n)·W₃(n)=0` already forces the contradiction.) -/
theorem casoratian_succ_ne_zero (p0 p1 p2 p3 : ℕ → K) (X Y Z : ℕ → K)
    (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y)
    (hZ : Recurrence p0 p1 p2 p3 Z) (n : ℕ)
    (hp0 : p0 n ≠ 0) (hW : W3 X Y Z n ≠ 0) :
    W3 X Y Z (n + 1) ≠ 0 := by
  intro hcontra
  have key := casoratian_step p0 p1 p2 p3 X Y Z hX hY hZ n
  rw [hcontra, mul_zero] at key
  -- 0 = -p0 n * W3 … ⇒ p0 n * W3 = 0 ⇒ contradiction
  have : p0 n * W3 X Y Z n = 0 := by linear_combination key
  rcases mul_eq_zero.mp this with h | h
  · exact hp0 h
  · exact hW h

/-- **Perfect system.**  If the three solutions are independent at `n=0` (`W₃(0) ≠ 0`) and every
`p₀(n), p₃(n) ≠ 0`, then `W₃(n) ≠ 0` for all `n`. -/
theorem casoratian_ne_zero (p0 p1 p2 p3 : ℕ → K) (X Y Z : ℕ → K)
    (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y)
    (hZ : Recurrence p0 p1 p2 p3 Z)
    (hp0 : ∀ n, p0 n ≠ 0) (h0 : W3 X Y Z 0 ≠ 0) :
    ∀ n, W3 X Y Z n ≠ 0 := by
  intro n
  induction n with
  | zero => exact h0
  | succ m ih => exact casoratian_succ_ne_zero p0 p1 p2 p3 X Y Z hX hY hZ m (hp0 m) ih

/-- **Uniqueness.**  Two solutions of the order-3 recurrence (with `p₃` nowhere zero) that agree on
the base window `0,1,2` agree everywhere.  This is the engine behind the integral decomposition
`E1 = A1 + B·log(2/3)`: once `E1` is shown to satisfy the recurrence (Phase 3) and to match
`A1 + B·log(2/3)` at `n=0,1,2`, the two are equal for all `n`. -/
theorem recurrence_unique (p0 p1 p2 p3 : ℕ → K) (X Y : ℕ → K)
    (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y) (hp3 : ∀ n, p3 n ≠ 0)
    (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) (h2 : X 2 = Y 2) :
    ∀ n, X n = Y n := by
  have main : ∀ n, X n = Y n ∧ X (n + 1) = Y (n + 1) ∧ X (n + 2) = Y (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2⟩
    | succ m ih =>
      obtain ⟨e0, e1, e2⟩ := ih
      refine ⟨e1, e2, ?_⟩
      have hx := hX m
      have hy := hY m
      rw [e0, e1, e2] at hx
      have key : p3 m * (X (m + 3) - Y (m + 3)) = 0 := by linear_combination hx - hy
      have hsub : X (m + 3) - Y (m + 3) = 0 := (mul_eq_zero.mp key).resolve_left (hp3 m)
      exact sub_eq_zero.mp hsub
  exact fun n => (main n).1

/-- **Linear combination of solutions is a solution.**  If `X, Y` satisfy the recurrence then so does
`fun n => X n + c · Y n`.  (Used to express `A1 + B·log(2/3)` as a recurrence solution.) -/
theorem Recurrence.add_smul (p0 p1 p2 p3 : ℕ → K) (X Y : ℕ → K) (c : K)
    (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y) :
    Recurrence p0 p1 p2 p3 (fun n => X n + c * Y n) := by
  intro n
  have hx := hX n
  have hy := hY n
  simp only
  linear_combination hx + c * hy

end OrderThreeRecurrence
