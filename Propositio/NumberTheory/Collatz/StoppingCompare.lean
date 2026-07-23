import Propositio.NumberTheory.Collatz.DensityCount
import Propositio.NumberTheory.Collatz.StoppingF3

/-!
# Coefficient stopping time ≤ actual stopping time

Two stopping notions appear in the corpus for the Terras map `T`:
* the **actual** stopping time `σ(n)` — least `j ≥ 1` with `T^j n < n`
  (`CollatzStoppingF3.DescBy n k := ∃ j, 1 ≤ j ∧ j ≤ k ∧ T_iter n j < n`);
* the **coefficient** stopping time `σ̃(n)` — least `j ≥ 1` with `3^(aCoef n j) < 2^j`
  (the "expected multiplicative factor drops below 1"), whose density-1 finiteness is
  proved UNCONDITIONALLY in `CollatzCoeffStopping.coeff_almost_all_descend`.

This file records the easy comparison **`σ̃(n) ≤ σ(n)`**: an actual descent forces a
coefficient descent. From the affine form `2^j · T^j n = 3^(aCoef n j) · n + cCoef n j`
and `cCoef ≥ 0`: `T^j n < n ⟹ 3^(aCoef n j)·n ≤ 2^j·T^j n < 2^j·n ⟹ 3^(aCoef n j) < 2^j`.

The CONVERSE (`σ(n) ≤ σ̃(n)`, i.e. a coefficient descent forces an actual descent) is
exactly the `hpow` gap — the hard half of the Terras descent dichotomy, where the
`cCoef` correction matters — and is the single open hypothesis of the conditional
capstone `CollatzAlmostAllDescend.collatz_almost_all_descend`.
-/

namespace CollatzStoppingCompare

open CollatzDensityCount
open TerrasDensity (T_iter)
open CollatzStoppingF3 (DescBy)

/-- **`coeff_descent_of_descBy` — `σ̃(n) ≤ σ(n)`.** If `n ≥ 1` actually descends within
`k` steps (`DescBy n k`), then it coefficient-descends within `k` steps: there is
`j ∈ [1,k]` with `3^(aCoef n j) < 2^j`. (Easy direction; the converse is `hpow`.) -/
theorem coeff_descent_of_descBy {n k : Nat} (h : DescBy n k) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ 3 ^ (aCoef n j) < 2 ^ j := by
  obtain ⟨j, hj1, hjk, hlt⟩ := h
  refine ⟨j, hj1, hjk, ?_⟩
  -- affine form: 2^j · T_iter n j = 3^(aCoef n j) · n + cCoef n j
  have haf : 2 ^ j * T_iter n j = 3 ^ (aCoef n j) * n + cCoef n j := affine_form n j
  -- T_iter n j < n  ⟹  2^j · T_iter n j < 2^j · n
  have h2pos : 0 < 2 ^ j := by positivity
  have h2 : 2 ^ j * T_iter n j < 2 ^ j * n :=
    Nat.mul_lt_mul_of_pos_left hlt h2pos
  -- hence 3^(aCoef n j) · n + cCoef n j < 2^j · n, so 3^(aCoef n j) · n < 2^j · n.
  rw [haf] at h2
  have h3 : 3 ^ (aCoef n j) * n < 2 ^ j * n := by
    have : 3 ^ (aCoef n j) * n ≤ 3 ^ (aCoef n j) * n + cCoef n j := Nat.le_add_right _ _
    omega
  exact Nat.lt_of_mul_lt_mul_right h3

end CollatzStoppingCompare
