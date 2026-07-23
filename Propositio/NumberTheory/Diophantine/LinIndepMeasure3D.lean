import Mathlib.Tactic

/-!
# The 3-D linear-independence measure engine — core atoms

This file builds the construction-independent core of `linindep_measure_3d`, the 3×3
generalization of `IrrMeasureCombination.irrationality_measure_le`. It is the abstract engine
that turns a sequence of small integer linear forms `Lₙ = a0ₙ + a1ₙ·u + a2ₙ·v` (with a nonzero
consecutive 3×3 determinant) into an effective linear-independence measure of `{1, u, v}` — and,
specialized to `u=log2, v=log3`, an effective irrationality measure of `log₂3` (≈ 5.76 for the
weighted-diagonal `{I, J}` system), which closes the Collatz `PowGap` wall WITHOUT Baker.

Four atoms here, all proved sorry-free and axiom-clean; they are the genuine new mathematics
(the 2×2→3×3 lift). The full engine assembly (index selection + the determinant lower bound) builds
on these plus the reused `IrrMeasureCombination.exists_good_index`.

* `det3_nonvanishing`   — a nonsingular 3×3 integer matrix has trivial integer kernel
  (lift of `consecutive_nonvanishing`; THE determinant-method core). Proved via the three
  adjugate/Cramer identities `D·q = D·s = D·t = 0`.
* `linform3_lower_atom` — the 3-D three-term identity + triangle bound (the *simultaneous*-
  approximation variant: lower-bounds `|q|·|construction form|` via the test errors `qu−s, qv−t`).
* `linform3_det_atom`   — the determinant-target identity `Δ = cof·Φ + (tb₁−sb₂)·Lₐ + (sa₂−ta₁)·L_b`
  + lower bound (the *linear-independence* variant: lower-bounds the target `Φ = q+su+tv` via the
  small construction forms `Lₐ, L_b` — the right atom for `log₂3`).
* `exists_pair_det_ne`  — pair selection: a nonzero test triple has a nonzero `Δ` against some pair
  of the three construction rows, so `linform3_det_atom` applies.
-/

namespace LinIndepMeasure3D

/-- A three-term triangle inequality `|a − b − c| ≤ |a| + |b| + |c|`. -/
private theorem tri3 (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  calc |a - b - c| ≤ |a - b| + |c| := by
        have h := abs_add_le (a - b) (-c); rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ |a| + |b| + |c| := by
        gcongr
        have h := abs_add_le a (-b); rwa [← sub_eq_add_neg, abs_neg] at h

/-- A three-term triangle inequality `|a + b + c| ≤ |a| + |b| + |c|`. -/
private theorem tri3add (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le (a + b) c).trans (by gcongr; exact abs_add_le a b)

/-- **The 3-D determinant-method core.** A `3×3` integer matrix with nonzero determinant has
trivial integer kernel: if `M·(q,s,t)ᵀ = 0` and `det M ≠ 0`, then `(q,s,t) = 0`.  Stated in the
contrapositive form consumed by the engine (a nonzero kernel vector forces `det = 0`).  Proved by
the three Cramer identities `(det M)·q = (det M)·s = (det M)·t = 0`, each a polynomial identity in
the matrix entries with the adjugate cofactors as multipliers. -/
theorem det3_nonvanishing
    (a00 a10 a20 a01 a11 a21 a02 a12 a22 q s t : ℤ)
    (hqst : ¬ (q = 0 ∧ s = 0 ∧ t = 0))
    (hdet : a00 * (a11 * a22 - a21 * a12)
              - a10 * (a01 * a22 - a21 * a02)
              + a20 * (a01 * a12 - a11 * a02) ≠ 0)
    (h0 : a00 * q + a10 * s + a20 * t = 0)
    (h1 : a01 * q + a11 * s + a21 * t = 0)
    (h2 : a02 * q + a12 * s + a22 * t = 0) : False := by
  set D := a00 * (a11 * a22 - a21 * a12) - a10 * (a01 * a22 - a21 * a02)
            + a20 * (a01 * a12 - a11 * a02) with hD
  -- Cramer identity for q (adjugate row 0)
  have hq : D * q = 0 := by
    rw [hD]
    linear_combination (a11 * a22 - a21 * a12) * h0 - (a10 * a22 - a20 * a12) * h1
      + (a10 * a21 - a20 * a11) * h2
  -- Cramer identity for s (adjugate row 1)
  have hs : D * s = 0 := by
    rw [hD]
    linear_combination -(a01 * a22 - a21 * a02) * h0 + (a00 * a22 - a20 * a02) * h1
      - (a00 * a21 - a20 * a01) * h2
  -- Cramer identity for t (adjugate row 2)
  have ht : D * t = 0 := by
    rw [hD]
    linear_combination (a01 * a12 - a11 * a02) * h0 - (a00 * a12 - a10 * a02) * h1
      + (a00 * a11 - a10 * a01) * h2
  -- D ≠ 0 forces q = s = t = 0
  have hq0 : q = 0 := (mul_eq_zero.mp hq).resolve_left hdet
  have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_left hdet
  have ht0 : t = 0 := (mul_eq_zero.mp ht).resolve_left hdet
  exact hqst ⟨hq0, hs0, ht0⟩

/-- **The 3-D three-term identity + lower atom** (lift of `linform_lower_atom`).
For a test triple `(q,s,t)` with the integer combination `a0·q + a1·s + a2·t ≠ 0`, the value
`|q|·|a0 + a1·u + a2·v|` of the construction form (scaled by `q`) is bounded below by
`1 − (|a1|·|q·u − s| + |a2|·|q·v − t|)`, via the identity
`q·(a0 + a1 u + a2 v) = (a0 q + a1 s + a2 t) + a1(q u − s) + a2(q v − t)` and `|integer| ≥ 1`. -/
theorem linform3_lower_atom (u v : ℝ) (a0 a1 a2 q s t : ℤ)
    (hne : a0 * q + a1 * s + a2 * t ≠ 0) :
    (1 : ℝ) - (|(a1 : ℝ)| * |(q : ℝ) * u - s| + |(a2 : ℝ)| * |(q : ℝ) * v - t|)
      ≤ |(q : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v| := by
  -- the integer combination has absolute value ≥ 1
  have hN1 : (1 : ℝ) ≤ |((a0 * q + a1 * s + a2 * t : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |a0 * q + a1 * s + a2 * t| := Int.one_le_abs hne
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ (|a0 * q + a1 * s + a2 * t| : ℝ) := by exact_mod_cast this
      _ = |((a0 * q + a1 * s + a2 * t : ℤ) : ℝ)| := by push_cast [Int.cast_abs]; rfl
  -- the core identity
  have hid : (q : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)
      = ((a0 * q + a1 * s + a2 * t : ℤ) : ℝ)
        + (a1 : ℝ) * ((q : ℝ) * u - s) + (a2 : ℝ) * ((q : ℝ) * v - t) := by
    push_cast; ring
  -- N = q·X − E1 − E2, so |N| ≤ |q·X| + |E1| + |E2| = |q||X| + |a1||qu−s| + |a2||qv−t|
  have hNle : |((a0 * q + a1 * s + a2 * t : ℤ) : ℝ)|
      ≤ |(q : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
        + |(a1 : ℝ)| * |(q : ℝ) * u - s| + |(a2 : ℝ)| * |(q : ℝ) * v - t| := by
    have e : ((a0 * q + a1 * s + a2 * t : ℤ) : ℝ)
        = (q : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)
          - (a1 : ℝ) * ((q : ℝ) * u - s) - (a2 : ℝ) * ((q : ℝ) * v - t) := by
      rw [hid]; ring
    rw [e]
    calc |(q : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)
            - (a1 : ℝ) * ((q : ℝ) * u - s) - (a2 : ℝ) * ((q : ℝ) * v - t)|
        ≤ |(q : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)|
          + |(a1 : ℝ) * ((q : ℝ) * u - s)| + |(a2 : ℝ) * ((q : ℝ) * v - t)| :=
            tri3 _ _ _
      _ = |(q : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
          + |(a1 : ℝ)| * |(q : ℝ) * u - s| + |(a2 : ℝ)| * |(q : ℝ) * v - t| := by
            rw [abs_mul, abs_mul, abs_mul]
  linarith [hN1, hNle]

/-- **The determinant-target identity + lower atom** — the genuine Nesterenko/Siegel core for a
linear-independence measure (the right atom for `log₂3`, where the *target* form `Φ = q + s·u + t·v`
is lower-bounded using the small *construction* forms `Lₐ, L_b`).

For the `3×3` integer determinant `Δ = det[(q,s,t); (a₀,a₁,a₂); (b₀,b₁,b₂)]` and the cofactor
`cof = a₁b₂ − a₂b₁`, the identity `Δ = cof·Φ + (t b₁ − s b₂)·Lₐ + (s a₂ − t a₁)·L_b` holds, where
`Lₐ = a₀+a₁u+a₂v`, `L_b = b₀+b₁u+b₂v`.  When `Δ ≠ 0` (so `|Δ| ≥ 1`) this yields
`1 − (|t b₁ − s b₂|·|Lₐ| + |s a₂ − t a₁|·|L_b|) ≤ |cof|·|Φ|`. -/
theorem linform3_det_atom (u v : ℝ) (q s t a0 a1 a2 b0 b1 b2 : ℤ)
    (hΔ : q * (a1 * b2 - a2 * b1) - s * (a0 * b2 - a2 * b0) + t * (a0 * b1 - a1 * b0) ≠ 0) :
    (1 : ℝ)
      - (|((t * b1 - s * b2 : ℤ) : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
          + |((s * a2 - t * a1 : ℤ) : ℝ)| * |(b0 : ℝ) + b1 * u + b2 * v|)
      ≤ |((a1 * b2 - a2 * b1 : ℤ) : ℝ)| * |(q : ℝ) + s * u + t * v| := by
  -- `|Δ| ≥ 1`
  have hN1 : (1 : ℝ) ≤ |((q * (a1 * b2 - a2 * b1) - s * (a0 * b2 - a2 * b0)
        + t * (a0 * b1 - a1 * b0) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hΔ
  -- the determinant-target identity, as `cof·Φ = Δ − (…)Lₐ − (…)L_b`
  have hid : ((a1 * b2 - a2 * b1 : ℤ) : ℝ) * ((q : ℝ) + s * u + t * v)
      = ((q * (a1 * b2 - a2 * b1) - s * (a0 * b2 - a2 * b0) + t * (a0 * b1 - a1 * b0) : ℤ) : ℝ)
        - ((t * b1 - s * b2 : ℤ) : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)
        - ((s * a2 - t * a1 : ℤ) : ℝ) * ((b0 : ℝ) + b1 * u + b2 * v) := by
    push_cast; ring
  have hNle : |((q * (a1 * b2 - a2 * b1) - s * (a0 * b2 - a2 * b0)
        + t * (a0 * b1 - a1 * b0) : ℤ) : ℝ)|
      ≤ |((a1 * b2 - a2 * b1 : ℤ) : ℝ)| * |(q : ℝ) + s * u + t * v|
        + |((t * b1 - s * b2 : ℤ) : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
        + |((s * a2 - t * a1 : ℤ) : ℝ)| * |(b0 : ℝ) + b1 * u + b2 * v| := by
    have e : ((q * (a1 * b2 - a2 * b1) - s * (a0 * b2 - a2 * b0) + t * (a0 * b1 - a1 * b0) : ℤ) : ℝ)
        = ((a1 * b2 - a2 * b1 : ℤ) : ℝ) * ((q : ℝ) + s * u + t * v)
          + ((t * b1 - s * b2 : ℤ) : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)
          + ((s * a2 - t * a1 : ℤ) : ℝ) * ((b0 : ℝ) + b1 * u + b2 * v) := by
      rw [hid]; ring
    rw [e]
    calc |((a1 * b2 - a2 * b1 : ℤ) : ℝ) * ((q : ℝ) + s * u + t * v)
            + ((t * b1 - s * b2 : ℤ) : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)
            + ((s * a2 - t * a1 : ℤ) : ℝ) * ((b0 : ℝ) + b1 * u + b2 * v)|
        ≤ |((a1 * b2 - a2 * b1 : ℤ) : ℝ) * ((q : ℝ) + s * u + t * v)|
          + |((t * b1 - s * b2 : ℤ) : ℝ) * ((a0 : ℝ) + a1 * u + a2 * v)|
          + |((s * a2 - t * a1 : ℤ) : ℝ) * ((b0 : ℝ) + b1 * u + b2 * v)| := tri3add _ _ _
      _ = |((a1 * b2 - a2 * b1 : ℤ) : ℝ)| * |(q : ℝ) + s * u + t * v|
          + |((t * b1 - s * b2 : ℤ) : ℝ)| * |(a0 : ℝ) + a1 * u + a2 * v|
          + |((s * a2 - t * a1 : ℤ) : ℝ)| * |(b0 : ℝ) + b1 * u + b2 * v| := by
            rw [abs_mul, abs_mul, abs_mul]
  linarith [hN1, hNle]

/-- **Pair selection** for the determinant lower bound: if the three construction rows have
nonzero `3×3` determinant and the integer test triple `(q,s,t)` is nonzero, then at least one of
the three "test-with-a-pair" determinants `Δ_bc, Δ_ca, Δ_ab` (replacing one construction row by
the test triple) is nonzero — so `linform3_det_atom` applies for some pair.  Proved via the same
Cramer identities: the three replacement determinants are the coordinates of `(q,s,t)` in the row
basis (times `D`), so all vanishing forces `(q,s,t)=0`. -/
theorem exists_pair_det_ne
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 q s t : ℤ)
    (hqst : ¬ (q = 0 ∧ s = 0 ∧ t = 0))
    (hD : a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0) ≠ 0) :
    (q * (b1 * c2 - b2 * c1) - s * (b0 * c2 - b2 * c0) + t * (b0 * c1 - b1 * c0) ≠ 0)
    ∨ (q * (a1 * c2 - a2 * c1) - s * (a0 * c2 - a2 * c0) + t * (a0 * c1 - a1 * c0) ≠ 0)
    ∨ (q * (a1 * b2 - a2 * b1) - s * (a0 * b2 - a2 * b0) + t * (a0 * b1 - a1 * b0) ≠ 0) := by
  by_contra h
  rw [not_or, not_or, not_not, not_not, not_not] at h
  obtain ⟨hbc, hac, hab⟩ := h
  -- D·q = q·D, and using the three Δ=0 (Cramer) one shows D·q = D·s = D·t = 0.
  set D := a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0) with hDdef
  have hq : D * q = 0 := by
    rw [hDdef]; linear_combination a0 * hbc - b0 * hac + c0 * hab
  have hs : D * s = 0 := by
    rw [hDdef]; linear_combination a1 * hbc - b1 * hac + c1 * hab
  have ht : D * t = 0 := by
    rw [hDdef]; linear_combination a2 * hbc - b2 * hac + c2 * hab
  exact hqst ⟨(mul_eq_zero.mp hq).resolve_left hD, (mul_eq_zero.mp hs).resolve_left hD,
    (mul_eq_zero.mp ht).resolve_left hD⟩

end LinIndepMeasure3D
