import Propositio.NumberTheory.Diophantine.OrderThreeRecurrence

/-!
# The 2×2 sub-Casoratian of an order-3 recurrence satisfies its own order-3 recurrence

For a homogeneous order-3 linear recurrence `p₃(n)X(n+3)+p₂(n)X(n+2)+p₁(n)X(n+1)+p₀(n)X(n)=0`, the
full 3×3 Casoratian of three solutions telescopes (Abel's identity, `OrderThreeRecurrence.W3`).  The
**2×2 sub-Casoratian** `Cas2(X,Y,n) = X(n)Y(n+1) − X(n+1)Y(n)` of two solutions does **not**
telescope — but, like every minor under a linear recurrence, it evolves under the *second compound*
(exterior square) of the companion matrix, and therefore satisfies its **own order-3 recurrence**.

This file proves that recurrence generically (over any field, for arbitrary coefficient functions),
via the two "wedge identities" coupling `Cas2` to the skip-Casoratian `CasD(X,Y,n) = X(n)Y(n+2) −
X(n+2)Y(n)`:
```
(I)   p₃(n)·CasD(n+1) = p₀(n)·Cas2(n) − p₂(n)·Cas2(n+1)
(II)  p₃(n)·Cas2(n+2) = p₀(n)·CasD(n) + p₁(n)·Cas2(n+1)
⟹    p₃(k+1)p₃(k)·Cas2(k+3) = p₁(k+1)p₃(k)·Cas2(k+2) − p₀(k+1)p₂(k)·Cas2(k+1) + p₀(k+1)p₀(k)·Cas2(k).
```
Each identity is a one-line `linear_combination` of the two solution recurrences.  This is the order-3
analogue of `PadeCasoratian` (order-2, where the 2×2 Casoratian itself telescopes by Abel).

**Application.** When the recurrence has sign-definite coefficients and the dominant *product* root
`λ_max·λ_mid` has fixed sign, `Cas2` has constant sign pattern and its non-vanishing follows by an
elementary positivity induction (sign-folding `(−1)ⁿ·Cas2`) — see `OSalikhovCasoratian` for the
oSALIKHOV instance discharging the prize hypothesis `hdet`, without any Poincaré–Perron asymptotics.
-/

namespace OrderThreeRecurrence

variable {K : Type*} [Field K]

/-- The 2×2 sub-Casoratian `Cas2(X,Y,n) = X(n)·Y(n+1) − X(n+1)·Y(n)`. -/
def Cas2 (X Y : ℕ → K) (n : ℕ) : K := X n * Y (n + 1) - X (n + 1) * Y n

/-- The skip-Casoratian `CasD(X,Y,n) = X(n)·Y(n+2) − X(n+2)·Y(n)`. -/
def CasD (X Y : ℕ → K) (n : ℕ) : K := X n * Y (n + 2) - X (n + 2) * Y n

variable {p0 p1 p2 p3 : ℕ → K} {X Y : ℕ → K}

set_option linter.unusedSectionVars false

/-- **Wedge identity (I):** `p₃(n)·CasD(n+1) = p₀(n)·Cas2(n) − p₂(n)·Cas2(n+1)`. -/
theorem cas2_wedge1 (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y) (n : ℕ) :
    p3 n * CasD X Y (n + 1) = p0 n * Cas2 X Y n - p2 n * Cas2 X Y (n + 1) := by
  simp only [Cas2, CasD]
  linear_combination X (n + 1) * hY n - Y (n + 1) * hX n

/-- **Wedge identity (II):** `p₃(n)·Cas2(n+2) = p₀(n)·CasD(n) + p₁(n)·Cas2(n+1)`. -/
theorem cas2_wedge2 (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y) (n : ℕ) :
    p3 n * Cas2 X Y (n + 2) = p0 n * CasD X Y n + p1 n * Cas2 X Y (n + 1) := by
  simp only [Cas2, CasD]
  linear_combination X (n + 2) * hY n - Y (n + 2) * hX n

/-- **The order-3 recurrence for the 2×2 sub-Casoratian** (second compound of the companion matrix):
`p₃(k+1)p₃(k)·Cas2(k+3) = p₁(k+1)p₃(k)·Cas2(k+2) − p₀(k+1)p₂(k)·Cas2(k+1) + p₀(k+1)p₀(k)·Cas2(k)`. -/
theorem cas2_recurrence (hX : Recurrence p0 p1 p2 p3 X) (hY : Recurrence p0 p1 p2 p3 Y) (k : ℕ) :
    p3 (k + 1) * p3 k * Cas2 X Y (k + 3)
      = p1 (k + 1) * p3 k * Cas2 X Y (k + 2) - p0 (k + 1) * p2 k * Cas2 X Y (k + 1)
        + p0 (k + 1) * p0 k * Cas2 X Y k := by
  have A := cas2_wedge2 hX hY (k + 1)
  have B := cas2_wedge1 hX hY k
  linear_combination p3 k * A + p0 (k + 1) * B

/-- `Cas2` is antisymmetric: swapping the two solutions negates it. -/
theorem cas2_swap (X Y : ℕ → K) (n : ℕ) : Cas2 Y X n = -Cas2 X Y n := by
  simp only [Cas2]; ring

end OrderThreeRecurrence
