import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Decomp
import Mathlib.Tactic

/-!
# Integrality of the log-coefficient `α₁(n) = Jα n`

The single-log decomposition `Jₙ = Pₙ + α₁(n)·log(4/3)` has `α₁(n) = Jα n` a rational defined by
the Padé recurrence `(n+2)α₁(n+2) = 7(2n+3)α₁(n+1) − (n+1)α₁(n)`, `α₁(0)=1, α₁(1)=7`.

We prove `Jα n` is in fact a (positive) **integer**.  The integer model is the weighted central
Delannoy / Legendre value
`JαZ n = ∑_{k=0}^n C(n,k)·C(n+k,k)·3^k  =  Pₙ(7)`  (Legendre polynomial at 7).

The crux is that `JαZ` obeys the **same** three-term recurrence — a genuine Zeilberger / creative
telescoping identity.  We prove it with an explicit, verified WZ certificate

  `Hz n k = -2·(2n+3)·k²·C(n+2,k)·C(n+k,k)·3^k`,

via the per-`k` telescoping identity (over `ℤ`)

  `(n+1)(n+2)·[(n+2)·bz(n+2,k) − 7(2n+3)·bz(n+1,k) + (n+1)·bz(n,k)] = Hz n (k+1) − Hz n k`,

where `bz m k = C(m,k)·C(m+k,k)·3^k`.  Summing over `k` telescopes to `0`, which is the recurrence
(after dividing by the nonzero `(n+1)(n+2)`).  A two-step strong induction transfers
`(JαZ n : ℚ) = Jα n`, giving `Jα_int`.
-/

namespace WeightedDiagonalLog43

open Finset

/-- The integer summand `bz(m,k) = C(m,k)·C(m+k,k)·3^k`. -/
def bz (m k : ℕ) : ℤ := (m.choose k : ℤ) * ((m + k).choose k : ℤ) * 3 ^ k

/-- The integer model of `α₁`: `JαZ n = ∑_{k=0}^n C(n,k)·C(n+k,k)·3^k` (Legendre `Pₙ(7)`). -/
def JαZ (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), bz n k

/-- The WZ certificate `Hz n k = -2·(2n+3)·k²·C(n+2,k)·C(n+k,k)·3^k`. -/
def Hz (n k : ℕ) : ℤ :=
  -2 * (2 * (n : ℤ) + 3) * (k : ℤ) ^ 2 * ((n + 2).choose k : ℤ) * ((n + k).choose k : ℤ) * 3 ^ k

/-- The combined summand `Tz n k = (n+2)·bz(n+2,k) − 7(2n+3)·bz(n+1,k) + (n+1)·bz(n,k)`. -/
def Tz (n k : ℕ) : ℤ :=
  ((n : ℤ) + 2) * bz (n + 2) k - 7 * (2 * (n : ℤ) + 3) * bz (n + 1) k + ((n : ℤ) + 1) * bz n k

/-! ### The six binomial ratio relations (cast to `ℤ`), valid for `k ≤ n + 2`. -/

/-- `C(n+1,k)·(n+1-k) = C(n,k)·(n+1)` (valid for `k ≤ n + 2`; at `k = n+2` both choose vanish). -/
theorem rel1 (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 1).choose k : ℤ) * ((n : ℤ) + 1 - k) = (n.choose k : ℤ) * ((n : ℤ) + 1) := by
  rcases le_or_gt k (n + 1) with hk1 | hk1
  · have h := Nat.choose_mul_succ_eq n k
    have hc : ((n + 1 - k : ℕ) : ℤ) = (n : ℤ) + 1 - k := by
      rw [Nat.cast_sub hk1]; push_cast; ring
    have h2 : (n.choose k : ℤ) * ((n : ℤ) + 1) = ((n + 1).choose k : ℤ) * ((n + 1 - k : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [hc] at h2
    linarith [h2]
  · -- k = n + 2: both `(n+1).choose k` and `n.choose k` are zero
    have hz1 : (n + 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz1, hz0]; push_cast; ring

/-- `C(n+2,k)·(n+2-k) = C(n+1,k)·(n+2)`. -/
theorem rel2 (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 2).choose k : ℤ) * ((n : ℤ) + 2 - k) = ((n + 1).choose k : ℤ) * ((n : ℤ) + 2) := by
  have h := Nat.choose_mul_succ_eq (n + 1) k
  have hc : ((n + 1 + 1 - k : ℕ) : ℤ) = (n : ℤ) + 2 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((n + 1).choose k : ℤ) * ((n : ℤ) + 2)
      = ((n + 1 + 1).choose k : ℤ) * ((n + 1 + 1 - k : ℕ) : ℤ) := by
    have := h; push_cast at this ⊢; exact_mod_cast this
  rw [hc] at h2
  have hcast : ((n + 1 + 1).choose k : ℤ) = ((n + 2).choose k : ℤ) := by norm_num
  rw [hcast] at h2
  linarith [h2]

/-- `C(n+1+k,k)·(n+1) = C(n+k,k)·(n+1+k)`. -/
theorem rel3 (n k : ℕ) :
    ((n + 1 + k).choose k : ℤ) * ((n : ℤ) + 1) = ((n + k).choose k : ℤ) * ((n : ℤ) + 1 + k) := by
  have h := Nat.choose_mul_succ_eq (n + k) k
  have hc : ((n + k + 1 - k : ℕ) : ℤ) = (n : ℤ) + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((n + k).choose k : ℤ) * ((n + k + 1 : ℕ) : ℤ)
      = ((n + k + 1).choose k : ℤ) * ((n + k + 1 - k : ℕ) : ℤ) := by exact_mod_cast h
  have htop : ((n + k + 1 : ℕ) : ℤ) = (n : ℤ) + 1 + k := by push_cast; ring
  rw [htop, hc] at h2
  have hcast : ((n + k + 1).choose k : ℤ) = ((n + 1 + k).choose k : ℤ) := by
    have : n + k + 1 = n + 1 + k := by omega
    rw [this]
  rw [hcast] at h2
  linarith [h2]

/-- `C(n+2+k,k)·(n+2) = C(n+1+k,k)·(n+2+k)`. -/
theorem rel4 (n k : ℕ) :
    ((n + 2 + k).choose k : ℤ) * ((n : ℤ) + 2)
      = ((n + 1 + k).choose k : ℤ) * ((n : ℤ) + 2 + k) := by
  have h := Nat.choose_mul_succ_eq (n + 1 + k) k
  have hc : ((n + 1 + k + 1 - k : ℕ) : ℤ) = (n : ℤ) + 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((n + 1 + k).choose k : ℤ) * ((n + 1 + k + 1 : ℕ) : ℤ)
      = ((n + 1 + k + 1).choose k : ℤ) * ((n + 1 + k + 1 - k : ℕ) : ℤ) := by exact_mod_cast h
  have htop : ((n + 1 + k + 1 : ℕ) : ℤ) = (n : ℤ) + 2 + k := by push_cast; ring
  rw [htop, hc] at h2
  have hcast : ((n + 1 + k + 1).choose k : ℤ) = ((n + 2 + k).choose k : ℤ) := by
    have : n + 1 + k + 1 = n + 2 + k := by omega
    rw [this]
  rw [hcast] at h2
  linarith [h2]

/-- `C(n+2,k+1)·(k+1) = C(n+2,k)·(n+2-k)`. -/
theorem rel5 (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 2).choose (k + 1) : ℤ) * ((k : ℤ) + 1) = ((n + 2).choose k : ℤ) * ((n : ℤ) + 2 - k) := by
  have h := Nat.choose_succ_right_eq (n + 2) k
  have hc : ((n + 2 - k : ℕ) : ℤ) = (n : ℤ) + 2 - k := by
    rw [Nat.cast_sub hk]; push_cast; ring
  have h2 : ((n + 2).choose (k + 1) : ℤ) * ((k : ℤ) + 1)
      = ((n + 2).choose k : ℤ) * ((n + 2 - k : ℕ) : ℤ) := by
    have := h; push_cast at this ⊢; exact_mod_cast this
  rw [hc] at h2
  exact h2

/-- `C(n+k+1,k+1)·(k+1) = C(n+k,k)·(n+1+k)`. -/
theorem rel6 (n k : ℕ) :
    ((n + k + 1).choose (k + 1) : ℤ) * ((k : ℤ) + 1)
      = ((n + k).choose k : ℤ) * ((n : ℤ) + 1 + k) := by
  have h := Nat.add_one_mul_choose_eq (n + k) k
  have h2 : ((n + k).choose k : ℤ) * ((n : ℤ) + 1 + k)
      = ((n + k + 1).choose (k + 1) : ℤ) * ((k : ℤ) + 1) := by
    have h3 : ((n + k + 1 : ℕ) : ℤ) * ((n + k).choose k : ℤ)
        = ((n + k + 1).choose (k + 1) : ℤ) * ((k : ℤ) + 1) := by exact_mod_cast h
    have : ((n + k + 1 : ℕ) : ℤ) = (n : ℤ) + 1 + k := by push_cast; ring
    rw [this] at h3
    linarith [h3]
  linarith [h2]

/-! ### The per-`k` WZ telescoping identity. -/

/-- **The WZ creative-telescoping identity** (valid for `k ≤ n + 2`):
`(n+1)(n+2)·Tz n k = Hz n (k+1) − Hz n k`.  This is the heart of the recurrence; it is closed by
the explicit certificate via `linear_combination` over the six binomial ratio relations. -/
theorem Tz_telescope (n k : ℕ) (hk : k ≤ n + 2) :
    ((n : ℤ) + 1) * ((n : ℤ) + 2) * Tz n k = Hz n (k + 1) - Hz n k := by
  -- the six relations
  have R1 := rel1 n k hk
  have R2 := rel2 n k hk
  have R3 := rel3 n k
  have R4 := rel4 n k
  have R5 := rel5 n k hk
  have R6 := rel6 n k
  -- normalize the binomial arguments appearing in `Hz n (k+1)` and `bz` of the shifted indices
  have e1 : n + 2 + k = n + (2 + k) := by ring
  have e2 : n + 1 + k = n + (1 + k) := by ring
  have e3 : n + k + 1 = n + (k + 1) := by ring
  -- abbreviations
  set P : ℤ := (n.choose k : ℤ)
  set P1 : ℤ := ((n + 1).choose k : ℤ)
  set P2 : ℤ := ((n + 2).choose k : ℤ)
  set Q : ℤ := ((n + k).choose k : ℤ)
  set Q1 : ℤ := ((n + 1 + k).choose k : ℤ)
  set Q2 : ℤ := ((n + 2 + k).choose k : ℤ)
  set Pp : ℤ := ((n + 2).choose (k + 1) : ℤ)
  set Qp : ℤ := ((n + k + 1).choose (k + 1) : ℤ)
  set t : ℤ := (3 : ℤ) ^ k with ht
  have hbz_n : bz n k = P * Q * t := by simp only [bz, P, Q, ht]
  have hbz_n1 : bz (n + 1) k = P1 * Q1 * t := by
    simp only [bz, P1, Q1, ht]
  have hbz_n2 : bz (n + 2) k = P2 * Q2 * t := by
    simp only [bz, P2, Q2, ht]
  have hHz_k : Hz n k = -2 * (2 * (n : ℤ) + 3) * (k : ℤ) ^ 2 * P2 * Q * t := by
    simp only [Hz, P2, Q, ht]
  have hHz_k1 : Hz n (k + 1)
      = -2 * (2 * (n : ℤ) + 3) * ((k : ℤ) + 1) ^ 2 * Pp * Qp * (3 * t) := by
    have harg : n + (k + 1) = n + k + 1 := by ring
    simp only [Hz, harg, Pp, Qp, ht]
    push_cast
    ring
  rw [Tz, hbz_n, hbz_n1, hbz_n2, hHz_k, hHz_k1]
  linear_combination
    ((-2) * Q * t + (-3) * (n : ℤ) * Q * t + (-1) * (n : ℤ) * (n : ℤ) * Q * t) * R1
    + ((21) * Q1 * t + (-1) * Q * t + (1) * (k : ℤ) * Q * t + (35) * (n : ℤ) * Q1 * t
        + (-2) * (n : ℤ) * Q * t + (1) * (n : ℤ) * (k : ℤ) * Q * t + (14) * (n : ℤ) * (n : ℤ) * Q1 * t
        + (-1) * (n : ℤ) * (n : ℤ) * Q * t) * R2
    + ((-38) * P2 * t + (23) * (k : ℤ) * P2 * t + (-45) * (n : ℤ) * P2 * t
        + (15) * (n : ℤ) * (k : ℤ) * P2 * t + (-13) * (n : ℤ) * (n : ℤ) * P2 * t) * R3
    + ((2) * P2 * t + (3) * (n : ℤ) * P2 * t + (1) * (n : ℤ) * (n : ℤ) * P2 * t) * R4
    + ((18) * Qp * t + (18) * (k : ℤ) * Qp * t + (12) * (n : ℤ) * Qp * t
        + (12) * (n : ℤ) * (k : ℤ) * Qp * t) * R5
    + ((36) * P2 * t + (-18) * (k : ℤ) * P2 * t + (42) * (n : ℤ) * P2 * t
        + (-12) * (n : ℤ) * (k : ℤ) * P2 * t + (12) * (n : ℤ) * (n : ℤ) * P2 * t) * R6

/-! ### From the telescoping identity to the recurrence. -/

/-- `bz m k = 0` when `k > m` (the binomial `C(m,k)` vanishes). -/
theorem bz_eq_zero_of_lt {m k : ℕ} (h : m < k) : bz m k = 0 := by
  simp only [bz, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]

/-- `Hz n 0 = 0`. -/
theorem Hz_zero (n : ℕ) : Hz n 0 = 0 := by simp [Hz]

/-- `Hz n (n+3) = 0` (the binomial `C(n+2,n+3)` vanishes). -/
theorem Hz_top (n : ℕ) : Hz n (n + 3) = 0 := by
  have : (n + 2).choose (n + 3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [Hz, this, Nat.cast_zero, mul_zero, zero_mul]

/-- The telescoping sum of the certificate differences vanishes over `range (n+3)`. -/
theorem sum_Hz_diff (n : ℕ) :
    ∑ k ∈ range (n + 3), (Hz n (k + 1) - Hz n k) = 0 := by
  rw [Finset.sum_range_sub (fun k => Hz n k) (n + 3)]
  rw [Hz_top, Hz_zero, sub_zero]

/-- **The integer recurrence for `JαZ`** (Legendre `Pₙ(7)` three-term recurrence). -/
theorem JαZ_rec (n : ℕ) :
    ((n : ℤ) + 2) * JαZ (n + 2) = 7 * (2 * (n : ℤ) + 3) * JαZ (n + 1) - ((n : ℤ) + 1) * JαZ n := by
  -- (n+1)(n+2)·∑ Tz = ∑ (Hz(k+1) − Hz(k)) = 0, hence ∑ Tz = 0.
  have hsum_tz : ((n : ℤ) + 1) * ((n : ℤ) + 2) * ∑ k ∈ range (n + 3), Tz n k = 0 := by
    rw [Finset.mul_sum]
    have : ∀ k ∈ range (n + 3),
        ((n : ℤ) + 1) * ((n : ℤ) + 2) * Tz n k = Hz n (k + 1) - Hz n k := by
      intro k hk
      exact Tz_telescope n k (by simp only [Finset.mem_range] at hk; omega)
    rw [Finset.sum_congr rfl this, sum_Hz_diff]
  have hne : ((n : ℤ) + 1) * ((n : ℤ) + 2) ≠ 0 := by positivity
  have hsum0 : ∑ k ∈ range (n + 3), Tz n k = 0 := by
    rcases mul_eq_zero.mp hsum_tz with h | h
    · exact absurd h hne
    · exact h
  -- expand ∑ Tz into the three JαZ sums, dropping vanishing tail terms.
  -- the three component sum identities (over range (n+3)):
  have s2 : ∑ k ∈ range (n + 3), bz (n + 2) k = JαZ (n + 2) := rfl
  have s1 : ∑ k ∈ range (n + 3), bz (n + 1) k = JαZ (n + 1) := by
    unfold JαZ
    rw [Finset.sum_range_succ, show n + 1 + 1 = n + 2 from rfl,
      bz_eq_zero_of_lt (by omega : n + 1 < n + 2), add_zero]
  have s0 : ∑ k ∈ range (n + 3), bz n k = JαZ n := by
    unfold JαZ
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      bz_eq_zero_of_lt (by omega : n < n + 1 + 1),
      bz_eq_zero_of_lt (by omega : n < n + 1), add_zero, add_zero]
  have hTzexp : ∑ k ∈ range (n + 3), Tz n k
      = ((n : ℤ) + 2) * JαZ (n + 2) - 7 * (2 * (n : ℤ) + 3) * JαZ (n + 1)
        + ((n : ℤ) + 1) * JαZ n := by
    simp only [Tz, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [s2, s1, s0]
  rw [hTzexp] at hsum0
  linarith [hsum0]

/-! ### Transfer to `Jα` and integrality. -/

/-- The integer model agrees with the rational `Jα`: `(JαZ n : ℚ) = Jα n`. -/
theorem JαZ_eq_Jα (n : ℕ) : (JαZ n : ℚ) = Jα n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp only [JαZ, Jα]; decide
    | 1 => simp only [JαZ, Jα]; decide
    | (m + 2) =>
      have ihm := ih m (by omega)
      have ihm1 := ih (m + 1) (by omega)
      have hZ := JαZ_rec m
      have hQ := Jα_rec m
      -- cast the integer recurrence to ℚ
      have hZQ : ((m : ℚ) + 2) * (JαZ (m + 2) : ℚ)
          = 7 * (2 * (m : ℚ) + 3) * (JαZ (m + 1) : ℚ) - ((m : ℚ) + 1) * (JαZ m : ℚ) := by
        have := hZ; push_cast at this ⊢; exact_mod_cast this
      have hne : ((m : ℚ) + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [hZQ, ihm, ihm1, hQ]

/-- **Integrality of the log-coefficient.**  `α₁(n) = Jα n` is an integer (`m := JαZ n`). -/
theorem Jα_int (n : ℕ) : ∃ m : ℤ, Jα n = (m : ℚ) :=
  ⟨JαZ n, (JαZ_eq_Jα n).symm⟩

end WeightedDiagonalLog43
