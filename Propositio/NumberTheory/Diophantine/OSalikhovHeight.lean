import Propositio.NumberTheory.Diophantine.RecurrenceGrowth

/-!
# Height bound for oSALIKHOV recurrence solutions

The oSALIKHOV order-3 recurrence coefficients (over `ℝ`) satisfy `|pᵢ(n)| ≤ 1500·p₃(n)` for
`i = 0,1,2` and all `n` (every coefficient difference `1500·p₃ ∓ pᵢ` has all-positive coefficients;
the sharp ratio is `|p₂|/p₃ → 1441.7 = λ_max`).  Hence any solution obeys the sub-multiplicative
bound `|X(n+3)| ≤ 1500·(|X(n+2)|+|X(n+1)|+|X(n)|)`, and `RecurrenceGrowth.growth_bound` (with
`R = 3·1500+1 = 4501`) gives the geometric **height bound** `|X(n)| ≤ M·4501ⁿ` — the recurrence side
of the prize interface's `hwden`.  (The bound is crude — `4501` vs the true `λ_max ≈ 1442` — but
suffices: only the *rate* `Q` enters the measure exponent, and `μ ≤ 22` has comfortable margin.)
-/

namespace OSalikhovHeight

/-- `p₀` over `ℝ`. -/
def p0R (n : ℕ) : ℝ := 6304 * (n : ℝ) ^ 5 + 50280 * (n : ℝ) ^ 4 + 150136 * (n : ℝ) ^ 3
    + 207666 * (n : ℝ) ^ 2 + 130822 * (n : ℝ) + 29316
/-- `p₁` over `ℝ`. -/
def p1R (n : ℕ) : ℝ := -498016 * (n : ℝ) ^ 5 - 4221128 * (n : ℝ) ^ 4 - 13683996 * (n : ℝ) ^ 3
    - 21166742 * (n : ℝ) ^ 2 - 15563215 * (n : ℝ) - 4329894
/-- `p₂` over `ℝ`. -/
def p2R (n : ℕ) : ℝ := -27264800 * (n : ℝ) ^ 5 - 244725800 * (n : ℝ) ^ 4 - 842584448 * (n : ℝ) ^ 3
    - 1379554326 * (n : ℝ) ^ 2 - 1057909176 * (n : ℝ) - 294706755
/-- `p₃` over `ℝ`. -/
def p3R (n : ℕ) : ℝ := 18912 * (n : ℝ) ^ 5 + 179208 * (n : ℝ) ^ 4 + 647844 * (n : ℝ) ^ 3
    + 1105722 * (n : ℝ) ^ 2 + 876609 * (n : ℝ) + 249885

theorem p3R_pos (n : ℕ) : 0 < p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; unfold p3R; positivity

theorem abs_p0R_le (n : ℕ) : |p0R n| ≤ 1500 * p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_le]; unfold p0R p3R
  constructor <;> nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

theorem abs_p1R_le (n : ℕ) : |p1R n| ≤ 1500 * p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_le]; unfold p1R p3R
  constructor <;> nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

theorem abs_p2R_le (n : ℕ) : |p2R n| ≤ 1500 * p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_le]; unfold p2R p3R
  constructor <;> nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

/-- **Sharp ratio bound** `|p₂(n)| ≤ 1442·p₃(n)`.  The true asymptotic ratio `|p₂|/p₃ → 4325/3 ≈ 1441.7`;
`1442·p₃ + p₂` has all-positive coefficients (leading `6304 = 1442·18912 − 27264800 > 0`), proved by
`positivity`. -/
theorem abs_p2R_le_1442 (n : ℕ) : |p2R n| ≤ 1442 * p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp2neg : p2R n ≤ 0 := by
    unfold p2R
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]
  rw [abs_of_nonpos hp2neg, neg_le]
  have : 0 ≤ 1442 * p3R n + p2R n := by
    unfold p2R p3R
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]
  linarith

/-- **Sharp ratio bound** `|p₁(n)| ≤ 27·p₃(n)`.  The true ratio `|p₁|/p₃ → 79/3 ≈ 26.3`;
`27·p₃ + p₁` has all-positive coefficients (leading `12608 = 27·18912 − 498016 > 0`), proved by
`nlinarith`. -/
theorem abs_p1R_le_27 (n : ℕ) : |p1R n| ≤ 27 * p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp1neg : p1R n ≤ 0 := by
    unfold p1R
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]
  rw [abs_of_nonpos hp1neg, neg_le]
  have : 0 ≤ 27 * p3R n + p1R n := by
    unfold p1R p3R
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]
  linarith

/-- **Sharp ratio bound** `|p₀(n)| ≤ p₃(n)`.  The true ratio `p₀/p₃ → 1/3`;
`p₃ − p₀` has all-positive coefficients (leading `12608 = 18912 − 6304 > 0`), proved by
`nlinarith`. -/
theorem abs_p0R_le_p3 (n : ℕ) : |p0R n| ≤ p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp0nn : 0 ≤ p0R n := by
    unfold p0R; positivity
  rw [abs_of_nonneg hp0nn]
  have : 0 ≤ p3R n - p0R n := by
    unfold p0R p3R
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]
  linarith

/-- **Sharp sub-multiplicative bound** using individual ratio bounds.  Each coefficient is bounded
separately: `|p₂| ≤ 1442·p₃`, `|p₁| ≤ 27·p₃`, `|p₀| ≤ p₃`, giving a per-step ratio
`|p₂|+|p₁|+|p₀| ≤ (1442+27+1)·p₃ = 1470·p₃`, hence `|X(n+3)| ≤ 1470·(|X n+2|+|X n+1|+|X n|)`. -/
theorem submul_sharp (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (n : ℕ) : |X (n + 3)| ≤ 1470 * (|X (n + 2)| + |X (n + 1)| + |X n|) := by
  have hp3 : 0 < p3R n := p3R_pos n
  have hX3 : X (n + 3) = -(p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n) / p3R n := by
    rw [eq_div_iff (ne_of_gt hp3)]; linear_combination hrec n
  rw [hX3, abs_div, abs_of_pos hp3, div_le_iff₀ hp3]
  have h2 : |p2R n| * |X (n + 2)| ≤ 1442 * p3R n * |X (n + 2)| := by
    apply mul_le_mul_of_nonneg_right (abs_p2R_le_1442 n) (abs_nonneg _)
  have h1 : |p1R n| * |X (n + 1)| ≤ 27 * p3R n * |X (n + 1)| := by
    apply mul_le_mul_of_nonneg_right (abs_p1R_le_27 n) (abs_nonneg _)
  have h0 : |p0R n| * |X n| ≤ p3R n * |X n| := by
    apply mul_le_mul_of_nonneg_right (abs_p0R_le_p3 n) (abs_nonneg _)
  calc |-(p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n)|
      = |p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n| := abs_neg _
    _ ≤ |p2R n * X (n + 2)| + |p1R n * X (n + 1)| + |p0R n * X n| := by
        refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ = |p2R n| * |X (n + 2)| + |p1R n| * |X (n + 1)| + |p0R n| * |X n| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ 1442 * p3R n * |X (n + 2)| + 27 * p3R n * |X (n + 1)| + p3R n * |X n| := by
        linarith [h2, h1, h0]
    _ ≤ 1470 * (|X (n + 2)| + |X (n + 1)| + |X n|) * p3R n := by
        have hp3nn : 0 ≤ p3R n := le_of_lt hp3
        nlinarith [abs_nonneg (X (n + 2)), abs_nonneg (X (n + 1)), abs_nonneg (X n)]

/-- **Sub-multiplicative bound** for any solution of the `ℝ`-recurrence. -/
theorem submul (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (n : ℕ) : |X (n + 3)| ≤ 1500 * (|X (n + 2)| + |X (n + 1)| + |X n|) := by
  have hp3 : 0 < p3R n := p3R_pos n
  have hX3 : X (n + 3) = -(p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n) / p3R n := by
    rw [eq_div_iff (ne_of_gt hp3)]; linear_combination hrec n
  rw [hX3, abs_div, abs_of_pos hp3, div_le_iff₀ hp3]
  calc |-(p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n)|
      = |p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n| := abs_neg _
    _ ≤ |p2R n * X (n + 2)| + |p1R n * X (n + 1)| + |p0R n * X n| := by
        refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ = |p2R n| * |X (n + 2)| + |p1R n| * |X (n + 1)| + |p0R n| * |X n| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ 1500 * p3R n * |X (n + 2)| + 1500 * p3R n * |X (n + 1)| + 1500 * p3R n * |X n| := by
        gcongr <;> [exact abs_p2R_le n; exact abs_p1R_le n; exact abs_p0R_le n]
    _ = 1500 * (|X (n + 2)| + |X (n + 1)| + |X n|) * p3R n := by ring

/-- **Height bound.**  Any solution of the oSALIKHOV `ℝ`-recurrence with base window bounded by
`M, M·4501, M·4501²` satisfies `|X(n)| ≤ M·4501ⁿ`. -/
theorem solution_height (X : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (hb0 : |X 0| ≤ M) (hb1 : |X 1| ≤ M * 4501) (hb2 : |X 2| ≤ M * 4501 ^ 2) :
    ∀ n, |X n| ≤ M * 4501 ^ n := by
  exact RecurrenceGrowth.growth_bound X 1500 4501 M (by norm_num) hM (by norm_num)
    (submul X hrec) (by norm_num) hb0 hb1 hb2

/-! ## Positivity & monotonicity (the heart of `hwpos`)

The sign pattern `p₀ ≥ 0`, `p₁ ≤ 0`, `p₂ ≤ 0`, `p₃ > 0` with the all-positive combination
`−p₂ − p₃ − p₀ ≥ 0` (leading `27264800 − 18912 − 6304 > 0`, every coefficient difference positive)
forces any solution that starts positive & non-decreasing to **stay positive & non-decreasing**:
`X(N+3) − X(N+2) = [(−p₂−p₃)X(N+2) + (−p₁)X(N+1) − p₀X(N)]/p₃ ≥ 0`.  Applied to `A2` (with
`A2(1)=189/20 > 0 ≤ A2(2) ≤ A2(3)`) this gives `A2(n) > 0`, hence `w_n = Den_n·A2(n) > 0` — the
prize interface's `hwpos`. -/

theorem p0R_nonneg (n : ℕ) : 0 ≤ p0R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; unfold p0R; positivity

theorem p1R_nonpos (n : ℕ) : p1R n ≤ 0 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold p1R
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

theorem neg_p2R_sub_p3R_sub_p0R_nonneg (n : ℕ) : 0 ≤ -p2R n - p3R n - p0R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold p0R p2R p3R
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

/-- **Positivity & monotonicity propagation** for a solution of the oSALIKHOV `ℝ`-recurrence. -/
theorem pos_mono (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
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
    have hp3 : 0 < p3R N := p3R_pos N
    have hge : X N ≤ X (N + 2) := le_trans hm1 hm2
    have c1 : p0R N ≤ -p2R N - p3R N := by have := neg_p2R_sub_p3R_sub_p0R_nonneg N; linarith
    have c2 : 0 ≤ -p1R N := by have := p1R_nonpos N; linarith
    have c3 : 0 ≤ p0R N := p0R_nonneg N
    have h_a : p0R N * X N ≤ p0R N * X (N + 2) := mul_le_mul_of_nonneg_left hge c3
    have h_b : p0R N * X (N + 2) ≤ (-p2R N - p3R N) * X (N + 2) :=
      mul_le_mul_of_nonneg_right c1 (le_of_lt hpos2)
    have h_c : 0 ≤ (-p1R N) * X (N + 1) := mul_nonneg c2 (le_of_lt hpos1)
    have hstep : X (N + 2) ≤ X (N + 3) := by
      have heq : X (N + 3) - X (N + 2)
          = ((-p2R N - p3R N) * X (N + 2) + (-p1R N) * X (N + 1) - p0R N * X N) / p3R N := by
        rw [eq_div_iff (ne_of_gt hp3)]; linear_combination hrec N
      have : 0 ≤ X (N + 3) - X (N + 2) := by
        rw [heq]; apply div_nonneg _ (le_of_lt hp3); linarith [h_a, h_b, h_c]
      linarith
    exact ⟨hpos1, hm2, hstep⟩

/-- **`hwpos` core**: a solution with positive non-decreasing base window stays positive. -/
theorem solution_pos (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (k : ℕ) (hk1 : 0 < X k) (hk2 : X k ≤ X (k + 1)) (hk3 : X (k + 1) ≤ X (k + 2)) :
    ∀ m, 0 < X (k + m) := fun m => (pos_mono X hrec k hk1 hk2 hk3 m).1

/-! ## Exponential lower bound (toward the B-asymptotic for `hsmall`)

The coefficient combination `−p₂ − p₀ − 1000·p₃` is again all-positive (leading
`27264800 − 6304 − 1000·18912 > 0`; the *sharp* one-step ratio `(|p₂|−p₀)/p₃` has infimum `≈ 1179`
at `n=0` and `→ 1441.4`).  So a positive non-decreasing solution obeys the **one-step** lower ratio
`X(N+3) ≥ 1000·X(N+2)`, giving `X(k+2+m) ≥ 1000ᵐ·X(k+2)`.  Applied to `B` this is a lower bound
`B(n) ≥ c·1000ⁿ`.

This is a *reusable ingredient* for `hsmall`, not a closure: the UNcleared form
`V = (A2·E1 − A1·E2)/B` decays even with crude rates, but `hsmall` needs the **cleared** form
`Den_n·|V| ≤ A·ρⁿ` with `ρ<1`, and `Den_n ~ 21ⁿ` swamps any crude `|V|` bound.  Closing `hsmall`
needs all three of `|A2| ≤ C·λ_maxⁿ`, `B ≥ c·λ_maxⁿ`, `|E2| ≤ C·rₘᵢₙⁿ` *sharp* (so
`|V| ≲ rₘᵢₙⁿ ≈ 0.0265ⁿ` beats `Den`).  The lemma below is the completable half (a lower bound; the
sharp value comes from refining `R → λ_max ≈ 1441`, a Poincaré–Perron statement). -/

theorem neg_p2R_sub_p0R_sub_1000p3R_nonneg (n : ℕ) : 0 ≤ -p2R n - p0R n - 1000 * p3R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold p0R p2R p3R
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

/-- **One-step exponential lower ratio.**  For a positive non-decreasing solution,
`1000·X(N+2) ≤ X(N+3)`. -/
theorem lower_step (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (N : ℕ) (hpN : 0 ≤ X N) (hpN1 : 0 ≤ X (N + 1)) (hle : X N ≤ X (N + 2)) :
    1000 * X (N + 2) ≤ X (N + 3) := by
  have hp3 : 0 < p3R N := p3R_pos N
  have c1 : p0R N ≤ -p2R N - 1000 * p3R N := by
    have := neg_p2R_sub_p0R_sub_1000p3R_nonneg N; linarith
  have c2 : 0 ≤ -p1R N := by have := p1R_nonpos N; linarith
  have c3 : 0 ≤ p0R N := p0R_nonneg N
  have h_a : p0R N * X N ≤ p0R N * X (N + 2) := mul_le_mul_of_nonneg_left hle c3
  have h_b : p0R N * X (N + 2) ≤ (-p2R N - 1000 * p3R N) * X (N + 2) :=
    mul_le_mul_of_nonneg_right c1 (le_trans hpN hle)
  have h_c : 0 ≤ (-p1R N) * X (N + 1) := mul_nonneg c2 hpN1
  have heq : X (N + 3) - 1000 * X (N + 2)
      = ((-p2R N - 1000 * p3R N) * X (N + 2) + (-p1R N) * X (N + 1) - p0R N * X N) / p3R N := by
    rw [eq_div_iff (ne_of_gt hp3)]; linear_combination hrec N
  have : 0 ≤ X (N + 3) - 1000 * X (N + 2) := by
    rw [heq]; apply div_nonneg _ (le_of_lt hp3); linarith [h_a, h_b, h_c]
  linarith

/-- **`hsmall` B-lower-bound input**: `X(k+2+m) ≥ 1000ᵐ · X(k+2)`. -/
theorem solution_lower (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (k : ℕ) (hk1 : 0 < X k) (hk2 : X k ≤ X (k + 1)) (hk3 : X (k + 1) ≤ X (k + 2)) :
    ∀ m, 1000 ^ m * X (k + 2) ≤ X (k + 2 + m) := by
  have W := pos_mono X hrec k hk1 hk2 hk3
  intro m
  induction m with
  | zero => simp
  | succ j ih =>
    obtain ⟨hp, hm1, hm2⟩ := W j
    have step : 1000 * X (k + 2 + j) ≤ X (k + 2 + j + 1) := by
      have e2 : k + j + 2 = k + 2 + j := by ring
      have e3 : k + j + 3 = k + 2 + j + 1 := by ring
      have := lower_step X hrec (k + j) (le_of_lt hp)
        (le_of_lt (lt_of_lt_of_le hp hm1)) (le_trans hm1 hm2)
      rwa [e2, e3] at this
    calc 1000 ^ (j + 1) * X (k + 2) = 1000 * (1000 ^ j * X (k + 2)) := by ring
      _ ≤ 1000 * X (k + 2 + j) := by linarith [ih]
      _ ≤ X (k + 2 + j + 1) := step
      _ = X (k + 2 + (j + 1)) := by ring_nf

/-! ## Sharp one-step UPPER bound (sharper height for `hsmall`)

`1500·p₃ + p₂ + p₁` is all-positive (leading `1500·18912 − 27264800 − 498016 > 0`; the sharp ratio
`(|p₂|+|p₁|)/p₃ → 1468`).  So a positive non-decreasing solution obeys the one-step UPPER ratio
`X(N+3) ≤ 1500·X(N+2)`, giving `X(k+2+m) ≤ 1500ᵐ·X(k+2)` — a height bound with rate `1500` (much
sharper than `solution_height`'s crude `4501`; needed so that, with `B ≥ c·1000ⁿ` and the sharp
integral decays, `|V| = |A2E1−A1E2|/B` decays fast enough to beat the lcm-clearing `Den ~ 21ⁿ` in
`hsmall`). -/

theorem p1500_nonneg (n : ℕ) : 0 ≤ 1500 * p3R n + p2R n + p1R n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold p1R p2R p3R
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5, hn]

/-- **One-step exponential upper ratio.**  For a positive non-decreasing solution,
`X(N+3) ≤ 1500·X(N+2)`. -/
theorem upper_step (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (N : ℕ) (hpN : 0 ≤ X N) (hpN1 : 0 ≤ X (N + 1)) (hle12 : X (N + 1) ≤ X (N + 2)) :
    X (N + 3) ≤ 1500 * X (N + 2) := by
  have hp3 : 0 < p3R N := p3R_pos N
  have c2 : 0 ≤ -p1R N := by have := p1R_nonpos N; linarith
  have cc : -p1R N ≤ 1500 * p3R N + p2R N := by have := p1500_nonneg N; linarith
  have h_a : (-p1R N) * X (N + 1) ≤ (-p1R N) * X (N + 2) := mul_le_mul_of_nonneg_left hle12 c2
  have h_b : (-p1R N) * X (N + 2) ≤ (1500 * p3R N + p2R N) * X (N + 2) :=
    mul_le_mul_of_nonneg_right cc (le_trans hpN1 hle12)
  have h_c : 0 ≤ p0R N * X N := mul_nonneg (p0R_nonneg N) hpN
  have heq : 1500 * X (N + 2) - X (N + 3)
      = ((1500 * p3R N + p2R N) * X (N + 2) - (-p1R N) * X (N + 1) + p0R N * X N) / p3R N := by
    rw [eq_div_iff (ne_of_gt hp3)]; linear_combination -hrec N
  have : 0 ≤ 1500 * X (N + 2) - X (N + 3) := by
    rw [heq]; apply div_nonneg _ (le_of_lt hp3); linarith [h_a, h_b, h_c]
  linarith

/-- **Sharp height** `X(k+2+m) ≤ 1500ᵐ · X(k+2)` (rate `1500`, vs `solution_height`'s `4501`). -/
theorem solution_upper (X : ℕ → ℝ)
    (hrec : ∀ n, p3R n * X (n + 3) + p2R n * X (n + 2) + p1R n * X (n + 1) + p0R n * X n = 0)
    (k : ℕ) (hk1 : 0 < X k) (hk2 : X k ≤ X (k + 1)) (hk3 : X (k + 1) ≤ X (k + 2)) :
    ∀ m, X (k + 2 + m) ≤ 1500 ^ m * X (k + 2) := by
  have W := pos_mono X hrec k hk1 hk2 hk3
  intro m
  induction m with
  | zero => simp
  | succ j ih =>
    obtain ⟨hp, hm1, hm2⟩ := W j
    have step : X (k + 2 + j + 1) ≤ 1500 * X (k + 2 + j) := by
      have e2 : k + j + 2 = k + 2 + j := by ring
      have e3 : k + j + 3 = k + 2 + j + 1 := by ring
      have := upper_step X hrec (k + j) (le_of_lt hp)
        (le_of_lt (lt_of_lt_of_le hp hm1)) hm2
      rwa [e2, e3] at this
    calc X (k + 2 + (j + 1)) = X (k + 2 + j + 1) := by ring_nf
      _ ≤ 1500 * X (k + 2 + j) := step
      _ ≤ 1500 * (1500 ^ j * X (k + 2)) := by linarith [ih]
      _ = 1500 ^ (j + 1) * X (k + 2) := by ring

end OSalikhovHeight
