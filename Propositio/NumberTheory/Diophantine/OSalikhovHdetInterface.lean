import Propositio.NumberTheory.Diophantine.OSalikhovHdet

/-!
# The `hdet` interface connector: cleared-coordinate determinant = `Den·Den·C2`

The prize interface (`logb23_measure_of_twolog_forms`) requires `hdet : ∀ n, w n · v (n+1) ≠
w (n+1) · v n` for the cleared two-log coordinates.  With the (one-step-shifted, to avoid the
degenerate `C2 0 = 0`) coordinates
`v n = Den(n+1)·(A1+A2)(n+1)`, `w n = −Den(n+1)·A2(n+1)`,
the consecutive 2×2 determinant factors exactly as
`w n · v (n+1) − w (n+1) · v n = Den(n+1)·Den(n+2)·C2(A1,A2,(n+1))`,
so it is non-zero whenever `Den > 0` and the Casoratian `C2(A1,A2,·)` is non-zero on `≥ 1` — the
latter is `OSalikhovHdet.casoratian_concrete_ne_zero`.  This connects the proved recurrence-side
`hdet` to the exact form the engine consumes (the `Den` sequence itself is the Phase-2 lcm-clearing
denominator, taken abstractly here). -/

namespace OSalikhovHdet

open OSalikhovCasoratian OSalikhovSequences

variable (A1 A2 Den : ℕ → ℝ)

/-- Shifted cleared coordinates `v n = Den(n+1)·(A1+A2)(n+1)`. -/
def vCoord (n : ℕ) : ℝ := Den (n + 1) * (A1 (n + 1) + A2 (n + 1))
/-- Shifted cleared coordinate `w n = −Den(n+1)·A2(n+1)`. -/
def wCoord (n : ℕ) : ℝ := -(Den (n + 1) * A2 (n + 1))

/-- **The determinant factorisation.**  `w n · v(n+1) − w(n+1) · v n = Den(n+1)·Den(n+2)·C2(A1,A2,n+1)`. -/
theorem det_eq_Den_C2 (n : ℕ) :
    wCoord A2 Den n * vCoord A1 A2 Den (n + 1) - wCoord A2 Den (n + 1) * vCoord A1 A2 Den n
      = Den (n + 1) * Den (n + 2) * C2 A1 A2 (n + 1) := by
  simp only [vCoord, wCoord, C2]
  ring

/-- **`hdet` for the cleared coordinates.**  If `Den > 0` and the Casoratian is non-zero on `≥ 1`,
the consecutive determinant never vanishes. -/
theorem hdet_of_casoratian (hDen : ∀ n, 0 < Den n)
    (hC : ∀ k, 1 ≤ k → C2 A1 A2 k ≠ 0) (n : ℕ) :
    wCoord A2 Den n * vCoord A1 A2 Den (n + 1) ≠ wCoord A2 Den (n + 1) * vCoord A1 A2 Den n := by
  rw [← sub_ne_zero, det_eq_Den_C2]
  have h1 : Den (n + 1) ≠ 0 := (hDen _).ne'
  have h2 : Den (n + 2) ≠ 0 := (hDen _).ne'
  have h3 : C2 A1 A2 (n + 1) ≠ 0 := hC (n + 1) (by omega)
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- **`hdet` (concrete).**  For the oSALIKHOV recurrence sequences `A1seq, A2seq` and any positive
`Den`, the cleared determinant never vanishes. -/
theorem hdet_concrete (Den : ℕ → ℝ) (hDen : ∀ n, 0 < Den n) (n : ℕ) :
    wCoord A2seq Den n * vCoord A1seq A2seq Den (n + 1)
      ≠ wCoord A2seq Den (n + 1) * vCoord A1seq A2seq Den n :=
  hdet_of_casoratian A1seq A2seq Den hDen casoratian_concrete_ne_zero n

end OSalikhovHdet
