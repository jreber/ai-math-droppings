import Propositio.NumberTheory.Diophantine.OSalikhovHeight

/-!
# `hdet` for the oSALIKHOV prize: the 2×2 Casoratian never vanishes — ELEMENTARY

The prize interface's last "deep" hypothesis was `hdet`: the consecutive 2×2 determinant of the
cleared two-log coordinates `(v,w) = (Den·(A1+A2), −Den·A2)` is non-zero, which reduces to the 2×2
Casoratian
`C2(n) = A1(n)·A2(n+1) − A1(n+1)·A2(n) ≠ 0`
of the two recurrence solutions `A1, A2`.  Earlier notes classified this as needing
Poincaré–Perron dominant-root asymptotics (`C2(n) ~ c·(λ_max·λ_mid)ⁿ`, no telescope).  **It does
not.**  The key facts (verified exact, `experiments/osalikhov_az_certificate.clj` and the wedge
probe):

* The three pairwise wedges of solutions of an order-3 recurrence evolve under the **second
  compound** of the companion matrix.  For `C2` and the "skip" Casoratian
  `D(n) = X(n)·Y(n+2) − X(n+2)·Y(n)` this gives the closed coupled system
  ```
  (I)   p₃(n)·D(n+1) = p₀(n)·C2(n) − p₂(n)·C2(n+1)
  (II)  p₃(n)·C2(n+2) = p₀(n)·D(n) + p₁(n)·C2(n+1)
  ```
  both pure `linear_combination`s of the two recurrences.  Eliminating `D` gives the **order-3
  recurrence for `C2`** (`casoratian2_rec`).
* `C2` has **perfectly alternating sign** `sign C2(n) = (−1)ⁿ` (dominant compound root
  `λ_max·λ_mid ≈ −33.7 < 0`).  Folding the sign, `c(k) = (−1)ᵏ·C2(k)` satisfies an order-3 recurrence
  with the **same sign pattern as `A2`** (`q₃>0, q₂≤0, q₁≤0, q₀≥0`), so the `pos_mono` argument
  (generalised here to `pos_mono_of_signs`) forces `c(k) > 0` for all `k ≥ 1` from a positive
  non-decreasing base window — hence `C2(k) ≠ 0`.  No dominant-root asymptotics.

Everything here is over the oSALIKHOV `ℝ`-recurrence (`OSalikhovHeight.p0R..p3R`); the base window
`0 < c 1 ≤ c 2 ≤ c 3` is a hypothesis, discharged for the concrete construction from the Phase-2
values (`C2(1) = −617/540`, …, verified exact).
-/

namespace OSalikhovCasoratian

open OSalikhovHeight

/-- The raw oSALIKHOV order-3 recurrence predicate (matching `OSalikhovHeight`'s phrasing). -/
def Rec (X : ℕ → ℝ) : Prop :=
  ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0

/-! ## Generic positivity/monotonicity propagation (abstract sign hypotheses) -/

/-- **Generic `pos_mono`.**  Any order-3 recurrence with the sign pattern `q₃>0, q₁≤0, q₀≥0` and the
all-positive combination `q₀ ≤ −q₂ − q₃` propagates a positive non-decreasing base window forever.
(`OSalikhovHeight.pos_mono` is the `p0R..p3R` instance; here the coefficients are arbitrary so the
lemma can also be applied to the *Casoratian* recurrence below.) -/
theorem pos_mono_of_signs (q0 q1 q2 q3 : ℕ → ℝ) (X : ℕ → ℝ)
    (hrec : ∀ n, q3 n * X (n + 3) + q2 n * X (n + 2) + q1 n * X (n + 1) + q0 n * X n = 0)
    (hq3 : ∀ n, 0 < q3 n) (hq1 : ∀ n, q1 n ≤ 0) (hq0 : ∀ n, 0 ≤ q0 n)
    (hcomb : ∀ n, q0 n ≤ -q2 n - q3 n)
    (k : ℕ) (hk1 : 0 < X k) (hk2 : X k ≤ X (k + 1)) (hk3 : X (k + 1) ≤ X (k + 2)) :
    ∀ m, 0 < X (k + m) ∧ X (k + m) ≤ X (k + m + 1) ∧ X (k + m + 1) ≤ X (k + m + 2) := by
  intro m
  induction m with
  | zero => exact ⟨hk1, hk2, hk3⟩
  | succ j ih =>
    obtain ⟨hp, hm1, hm2⟩ := ih
    have hpos1 : 0 < X (k + j + 1) := lt_of_lt_of_le hp hm1
    have hpos2 : 0 < X (k + j + 2) := lt_of_lt_of_le hpos1 hm2
    set N := k + j with hN
    have hp3 : 0 < q3 N := hq3 N
    have hge : X N ≤ X (N + 2) := le_trans hm1 hm2
    have c1 : q0 N ≤ -q2 N - q3 N := hcomb N
    have c2 : 0 ≤ -q1 N := by have := hq1 N; linarith
    have c3 : 0 ≤ q0 N := hq0 N
    have h_a : q0 N * X N ≤ q0 N * X (N + 2) := mul_le_mul_of_nonneg_left hge c3
    have h_b : q0 N * X (N + 2) ≤ (-q2 N - q3 N) * X (N + 2) :=
      mul_le_mul_of_nonneg_right c1 (le_of_lt hpos2)
    have h_c : 0 ≤ (-q1 N) * X (N + 1) := mul_nonneg c2 (le_of_lt hpos1)
    have hstep : X (N + 2) ≤ X (N + 3) := by
      have heq : X (N + 3) - X (N + 2)
          = ((-q2 N - q3 N) * X (N + 2) + (-q1 N) * X (N + 1) - q0 N * X N) / q3 N := by
        rw [eq_div_iff (ne_of_gt hp3)]; linear_combination hrec N
      have : 0 ≤ X (N + 3) - X (N + 2) := by
        rw [heq]; apply div_nonneg _ (le_of_lt hp3); linarith [h_a, h_b, h_c]
      linarith
    exact ⟨hpos1, hm2, hstep⟩

/-- `0 < X(k+m)` for all `m` (the corollary used below). -/
theorem pos_of_signs (q0 q1 q2 q3 : ℕ → ℝ) (X : ℕ → ℝ)
    (hrec : ∀ n, q3 n * X (n + 3) + q2 n * X (n + 2) + q1 n * X (n + 1) + q0 n * X n = 0)
    (hq3 : ∀ n, 0 < q3 n) (hq1 : ∀ n, q1 n ≤ 0) (hq0 : ∀ n, 0 ≤ q0 n)
    (hcomb : ∀ n, q0 n ≤ -q2 n - q3 n)
    (k : ℕ) (hk1 : 0 < X k) (hk2 : X k ≤ X (k + 1)) (hk3 : X (k + 1) ≤ X (k + 2)) :
    ∀ m, 0 < X (k + m) :=
  fun m => (pos_mono_of_signs q0 q1 q2 q3 X hrec hq3 hq1 hq0 hcomb k hk1 hk2 hk3 m).1

/-! ## The 2×2 Casoratian and its order-3 recurrence -/

/-- The 2×2 Casoratian `C2(n) = X(n)·Y(n+1) − X(n+1)·Y(n)`. -/
def C2 (X Y : ℕ → ℝ) (n : ℕ) : ℝ := X n * Y (n + 1) - X (n + 1) * Y n

/-- The "skip" Casoratian `D(n) = X(n)·Y(n+2) − X(n+2)·Y(n)`. -/
def Cd (X Y : ℕ → ℝ) (n : ℕ) : ℝ := X n * Y (n + 2) - X (n + 2) * Y n

variable {X Y : ℕ → ℝ}

/-- **Wedge identity (I):** `p₃(n)·D(n+1) = p₀(n)·C2(n) − p₂(n)·C2(n+1)`. -/
theorem id1 (hX : Rec X) (hY : Rec Y) (n : ℕ) :
    p3R n * Cd X Y (n + 1) = p0R n * C2 X Y n - p2R n * C2 X Y (n + 1) := by
  simp only [C2, Cd]
  linear_combination X (n + 1) * hY n - Y (n + 1) * hX n

/-- **Wedge identity (II):** `p₃(n)·C2(n+2) = p₀(n)·D(n) + p₁(n)·C2(n+1)`. -/
theorem id2 (hX : Rec X) (hY : Rec Y) (n : ℕ) :
    p3R n * C2 X Y (n + 2) = p0R n * Cd X Y n + p1R n * C2 X Y (n + 1) := by
  simp only [C2, Cd]
  linear_combination X (n + 2) * hY n - Y (n + 2) * hX n

/-- **Order-3 recurrence for the Casoratian** (eliminate `D` from (I),(II)):
`p₃(k+1)·p₃(k)·C2(k+3) = p₁(k+1)·p₃(k)·C2(k+2) − p₀(k+1)·p₂(k)·C2(k+1) + p₀(k+1)·p₀(k)·C2(k)`. -/
theorem casoratian2_rec (hX : Rec X) (hY : Rec Y) (k : ℕ) :
    p3R (k + 1) * p3R k * C2 X Y (k + 3)
      = p1R (k + 1) * p3R k * C2 X Y (k + 2) - p0R (k + 1) * p2R k * C2 X Y (k + 1)
        + p0R (k + 1) * p0R k * C2 X Y k := by
  have A := id2 hX hY (k + 1)
  have B := id1 hX hY k
  -- A : p3R(k+1)*C2(k+3) = p0R(k+1)*Cd(k+1) + p1R(k+1)*C2(k+2)
  -- B : p3R k*Cd(k+1) = p0R k*C2(k) - p2R k*C2(k+1)
  linear_combination p3R k * A + p0R (k + 1) * B

/-! ## Sign-folding and the non-vanishing conclusion

Define `c(k) = (−1)ᵏ·C2(k)`.  It satisfies the recurrence with coefficients
`q₃ = p₃(k+1)p₃(k)`, `q₂ = p₁(k+1)p₃(k)`, `q₁ = p₀(k+1)p₂(k)`, `q₀ = p₀(k+1)p₀(k)`, whose signs match
the `A2` pattern. -/

/-- `q₃(k) = p₃(k+1)·p₃(k)`. -/
def q3 (k : ℕ) : ℝ := p3R (k + 1) * p3R k
/-- `q₂(k) = p₁(k+1)·p₃(k)`. -/
def q2 (k : ℕ) : ℝ := p1R (k + 1) * p3R k
/-- `q₁(k) = p₀(k+1)·p₂(k)`. -/
def q1 (k : ℕ) : ℝ := p0R (k + 1) * p2R k
/-- `q₀(k) = p₀(k+1)·p₀(k)`. -/
def q0 (k : ℕ) : ℝ := p0R (k + 1) * p0R k

/-- The sign-folded Casoratian `c(k) = (−1)ᵏ·C2(k)`. -/
def cfold (X Y : ℕ → ℝ) (k : ℕ) : ℝ := (-1) ^ k * C2 X Y k

theorem q3_pos (k : ℕ) : 0 < q3 k := mul_pos (p3R_pos _) (p3R_pos _)

/-- `p₂ ≤ 0` (from `−p₂ − p₃ − p₀ ≥ 0` with `p₃ > 0, p₀ ≥ 0`). -/
theorem p2R_nonpos (n : ℕ) : p2R n ≤ 0 := by
  have h := neg_p2R_sub_p3R_sub_p0R_nonneg n
  have := p3R_pos n; have := p0R_nonneg n; linarith

theorem q1_nonpos (k : ℕ) : q1 k ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (p0R_nonneg _) (p2R_nonpos k)

theorem q0_nonneg (k : ℕ) : 0 ≤ q0 k := mul_nonneg (p0R_nonneg _) (p0R_nonneg _)

/-- Auxiliary deg-5 sign facts. -/
theorem neg_p1R_sub_p3R_sub_p0R_nonneg (n : ℕ) : 0 ≤ -p1R n - p3R n - p0R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold p0R p1R p3R
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

theorem p3R_sub_p0R_nonneg (n : ℕ) : 0 ≤ p3R n - p0R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold p0R p3R
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

/-- The all-positive combination `q₀ ≤ −q₂ − q₃` for the Casoratian recurrence. -/
theorem q_comb (k : ℕ) : q0 k ≤ -q2 k - q3 k := by
  unfold q0 q2 q3
  have hp0k1 : 0 ≤ p0R (k + 1) := p0R_nonneg _
  have hp3k : 0 ≤ p3R k := le_of_lt (p3R_pos k)
  -- p0(k+1) ≤ -p1(k+1) - p3(k+1)
  have L1 : p0R (k + 1) ≤ -p1R (k + 1) - p3R (k + 1) := by
    have := neg_p1R_sub_p3R_sub_p0R_nonneg (k + 1); linarith
  -- p0(k) ≤ p3(k)
  have L2 : p0R k ≤ p3R k := by have := p3R_sub_p0R_nonneg k; linarith
  calc p0R (k + 1) * p0R k
      ≤ p0R (k + 1) * p3R k := mul_le_mul_of_nonneg_left L2 hp0k1
    _ ≤ (-p1R (k + 1) - p3R (k + 1)) * p3R k := mul_le_mul_of_nonneg_right L1 hp3k
    _ = -(p1R (k + 1) * p3R k) - p3R (k + 1) * p3R k := by ring

/-- `cfold` satisfies the order-3 recurrence with the `q` coefficients. -/
theorem cfold_rec (hX : Rec X) (hY : Rec Y) :
    ∀ k, q3 k * cfold X Y (k + 3) + q2 k * cfold X Y (k + 2)
      + q1 k * cfold X Y (k + 1) + q0 k * cfold X Y k = 0 := by
  intro k
  have h := casoratian2_rec hX hY k
  simp only [cfold, q0, q1, q2, q3]
  have e3 : ((-1 : ℝ)) ^ (k + 3) = -((-1) ^ k) := by rw [pow_add]; ring
  have e2 : ((-1 : ℝ)) ^ (k + 2) = (-1) ^ k := by rw [pow_add]; ring
  have e1 : ((-1 : ℝ)) ^ (k + 1) = -((-1) ^ k) := by rw [pow_add]; ring
  rw [e3, e2, e1]
  linear_combination (-((-1 : ℝ) ^ k)) * h

/-- **`hdet` core — the Casoratian never vanishes.**  For two solutions `X, Y` of the oSALIKHOV
recurrence whose sign-folded Casoratian has a positive non-decreasing base window
`0 < c 1 ≤ c 2 ≤ c 3`, the 2×2 Casoratian `C2(X,Y,k) ≠ 0` for every `k ≥ 1`. -/
theorem casoratian2_ne_zero (hX : Rec X) (hY : Rec Y)
    (hb1 : 0 < cfold X Y 1) (hb2 : cfold X Y 1 ≤ cfold X Y 2)
    (hb3 : cfold X Y 2 ≤ cfold X Y 3) :
    ∀ k, 1 ≤ k → C2 X Y k ≠ 0 := by
  have hpos : ∀ m, 0 < cfold X Y (1 + m) :=
    pos_of_signs q0 q1 q2 q3 (cfold X Y) (cfold_rec hX hY) q3_pos q1_nonpos q0_nonneg q_comb
      1 hb1 hb2 hb3
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have := hpos m
  rw [show 1 + m = m + 1 by ring] at this ⊢
  -- cfold = (-1)^(m+1) * C2 ; positive ⇒ C2 ≠ 0
  intro hC
  simp only [cfold, hC, mul_zero] at this
  exact lt_irrefl 0 this
