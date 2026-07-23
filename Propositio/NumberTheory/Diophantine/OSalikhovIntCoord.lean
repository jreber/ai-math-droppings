import Propositio.NumberTheory.Diophantine.OSalikhovHdet
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Denominator
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Integer-coordinate layer for the oSALIKHOV two-log interface

This file defines ℚ-valued versions of the oSALIKHOV recurrence sequences (A1seqQ, A2seqQ, BseqQ),
the integer-valued denominator clearing sequence DenIntN, and the integer-coordinate sequences
vInt and wInt that feed into the prize interface.

The key results are:
- `DenIntN_pos`: `0 < DenIntN n`
- `DenInt_pos`: `0 < DenInt n`
- `wInt_cast_DenR`: `(wInt n : ℝ) = DenR (n+1) * A2seq (n+1)`
- `vInt_cast_DenR`: `(vInt n : ℝ) = -(DenR (n+1) * (A1seq (n+1) + A2seq (n+1)))`
-/

namespace OSalikhovIntCoord

open OSalikhovHeight OSalikhovSequences OSalikhovHdet
open WeightedDiagonalLog43 (dvd_clears)

/-! ## ℚ polynomial coefficients -/

private def p0Q (n : ℕ) : ℚ := 6304 * (n : ℚ)^5 + 50280 * (n : ℚ)^4 + 150136 * (n : ℚ)^3
    + 207666 * (n : ℚ)^2 + 130822 * (n : ℚ) + 29316
private def p1Q (n : ℕ) : ℚ := -498016 * (n : ℚ)^5 - 4221128 * (n : ℚ)^4 - 13683996 * (n : ℚ)^3
    - 21166742 * (n : ℚ)^2 - 15563215 * (n : ℚ) - 4329894
private def p2Q (n : ℕ) : ℚ := -27264800 * (n : ℚ)^5 - 244725800 * (n : ℚ)^4 - 842584448 * (n : ℚ)^3
    - 1379554326 * (n : ℚ)^2 - 1057909176 * (n : ℚ) - 294706755
private def p3Q (n : ℕ) : ℚ := 18912 * (n : ℚ)^5 + 179208 * (n : ℚ)^4 + 647844 * (n : ℚ)^3
    + 1105722 * (n : ℚ)^2 + 876609 * (n : ℚ) + 249885

private theorem p3Q_pos (n : ℕ) : 0 < p3Q n := by
  have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; unfold p3Q; positivity

private theorem p0Q_cast (n : ℕ) : (p0Q n : ℝ) = p0R n := by
  simp only [p0Q, p0R]; push_cast; ring
private theorem p1Q_cast (n : ℕ) : (p1Q n : ℝ) = p1R n := by
  simp only [p1Q, p1R]; push_cast; ring
private theorem p2Q_cast (n : ℕ) : (p2Q n : ℝ) = p2R n := by
  simp only [p2Q, p2R]; push_cast; ring
private theorem p3Q_cast (n : ℕ) : (p3Q n : ℝ) = p3R n := by
  simp only [p3Q, p3R]; push_cast; ring

/-! ## ℚ window and sequence -/

def winQ (b0 b1 b2 : ℚ) : ℕ → ℚ × ℚ × ℚ
  | 0 => (b0, b1, b2)
  | (n + 1) =>
      let w := winQ b0 b1 b2 n
      (w.2.1, w.2.2, (-(p2Q n * w.2.2 + p1Q n * w.2.1 + p0Q n * w.1)) / p3Q n)

def seqQ (b0 b1 b2 : ℚ) (n : ℕ) : ℚ := (winQ b0 b1 b2 n).1

@[simp] theorem seqQ_zero (b0 b1 b2 : ℚ) : seqQ b0 b1 b2 0 = b0 := rfl
@[simp] theorem seqQ_one (b0 b1 b2 : ℚ) : seqQ b0 b1 b2 1 = b1 := rfl
@[simp] theorem seqQ_two (b0 b1 b2 : ℚ) : seqQ b0 b1 b2 2 = b2 := rfl

private theorem winQ_cast_eq_win (b0 b1 b2 : ℚ) (n : ℕ) :
    ((winQ b0 b1 b2 n).1 : ℝ) = (win (b0 : ℝ) (b1 : ℝ) (b2 : ℝ) n).1 ∧
    ((winQ b0 b1 b2 n).2.1 : ℝ) = (win (b0 : ℝ) (b1 : ℝ) (b2 : ℝ) n).2.1 ∧
    ((winQ b0 b1 b2 n).2.2 : ℝ) = (win (b0 : ℝ) (b1 : ℝ) (b2 : ℝ) n).2.2 := by
  induction n with
  | zero => simp [winQ, win]
  | succ n ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      simp only [winQ, win, stepR]
      refine ⟨ih2, ih3, ?_⟩
      rw [Rat.cast_div, Rat.cast_neg, Rat.cast_add, Rat.cast_add,
          Rat.cast_mul, Rat.cast_mul, Rat.cast_mul,
          p0Q_cast, p1Q_cast, p2Q_cast, p3Q_cast, ih1, ih2, ih3]

theorem seqQ_cast_eq_seqR (b0 b1 b2 : ℚ) (n : ℕ) :
    (seqQ b0 b1 b2 n : ℝ) = seqR (b0 : ℝ) (b1 : ℝ) (b2 : ℝ) n :=
  (winQ_cast_eq_win b0 b1 b2 n).1

/-! ## Concrete ℚ sequences -/

def A1seqQ : ℕ → ℚ := seqQ 0 (199 / 36) (3674885 / 648)
def A2seqQ : ℕ → ℚ := seqQ 0 (189 / 20) (1163381 / 120)
def BseqQ  : ℕ → ℚ := seqQ (1 / 30) (409 / 30) (139867 / 10)

theorem A1seqQ_cast (n : ℕ) : (A1seqQ n : ℝ) = A1seq n := by
  simp only [A1seqQ, A1seq]
  have h := seqQ_cast_eq_seqR 0 (199 / 36 : ℚ) (3674885 / 648 : ℚ) n
  simp only [Rat.cast_zero] at h; convert h using 2 <;> push_cast <;> norm_num

theorem A2seqQ_cast (n : ℕ) : (A2seqQ n : ℝ) = A2seq n := by
  simp only [A2seqQ, A2seq]
  have h := seqQ_cast_eq_seqR 0 (189 / 20 : ℚ) (1163381 / 120 : ℚ) n
  simp only [Rat.cast_zero] at h; convert h using 2 <;> push_cast <;> norm_num

theorem BseqQ_cast (n : ℕ) : (BseqQ n : ℝ) = Bseq n := by
  simp only [BseqQ, Bseq]
  have h := seqQ_cast_eq_seqR (1 / 30 : ℚ) (409 / 30 : ℚ) (139867 / 10 : ℚ) n
  convert h using 2 <;> push_cast <;> norm_num

/-! ## Denominator clearing sequence -/

def DenIntN (n : ℕ) : ℕ :=
  Nat.lcm (A1seqQ n + A2seqQ n).den (A2seqQ n).den

theorem DenIntN_pos (n : ℕ) : 0 < DenIntN n :=
  Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Rat.den_nz _) (Rat.den_nz _))

def DenInt (n : ℕ) : ℤ := (DenIntN n : ℤ)

theorem DenInt_pos (n : ℕ) : 0 < DenInt n := by
  simp only [DenInt]; exact_mod_cast DenIntN_pos n

private theorem DenIntN_dvd_S_den (n : ℕ) : (A1seqQ n + A2seqQ n).den ∣ DenIntN n :=
  Nat.dvd_lcm_left _ _

private theorem DenIntN_dvd_A2_den (n : ℕ) : (A2seqQ n).den ∣ DenIntN n :=
  Nat.dvd_lcm_right _ _

/-! ## Integer clearing: DenIntN * seqQ values are integers -/

-- `dvd_clears` from WeightedDiagonalLog43Denominator:
-- `theorem dvd_clears {q : ℚ} {N : ℕ} (h : q.den ∣ N) : ∃ m : ℤ, (N : ℚ) * q = (m : ℚ)`

/-- `DenIntN(n) * A2seqQ(n)` is an integer. -/
private theorem DenIntN_mul_A2_int (n : ℕ) :
    ∃ m : ℤ, (DenIntN n : ℚ) * A2seqQ n = (m : ℚ) :=
  dvd_clears (DenIntN_dvd_A2_den n)

/-- `DenIntN(n) * (A1seqQ(n) + A2seqQ(n))` is an integer. -/
private theorem DenIntN_mul_S_int (n : ℕ) :
    ∃ m : ℤ, (DenIntN n : ℚ) * (A1seqQ n + A2seqQ n) = (m : ℚ) :=
  dvd_clears (DenIntN_dvd_S_den n)

/-! ## Integer coordinates -/

-- Use Classical to extract the witness from the existence statement
-- and define wInt / vInt as the unique integer value

/-- The integer `w n = DenIntN(n+1) * A2seqQ(n+1)` (viewed as an element of ℤ). -/
noncomputable def wInt (n : ℕ) : ℤ :=
  (DenIntN_mul_A2_int (n + 1)).choose

/-- `(wInt n : ℚ) = DenIntN(n+1) * A2seqQ(n+1)`. -/
private theorem wInt_rat (n : ℕ) :
    (wInt n : ℚ) = (DenIntN (n + 1) : ℚ) * A2seqQ (n + 1) :=
  (DenIntN_mul_A2_int (n + 1)).choose_spec.symm

/-- The integer `v n = -(DenIntN(n+1) * (A1seqQ+A2seqQ)(n+1))` (viewed as ℤ). -/
noncomputable def vInt (n : ℕ) : ℤ :=
  -((DenIntN_mul_S_int (n + 1)).choose)

/-- `(vInt n : ℚ) = -(DenIntN(n+1) * (A1seqQ+A2seqQ)(n+1))`. -/
private theorem vInt_rat (n : ℕ) :
    (vInt n : ℚ) = -((DenIntN (n + 1) : ℚ) * (A1seqQ (n + 1) + A2seqQ (n + 1))) := by
  simp only [vInt]
  push_cast
  rw [← (DenIntN_mul_S_int (n + 1)).choose_spec]

/-! ## Den as positive real -/

noncomputable def DenR (n : ℕ) : ℝ := (DenIntN n : ℝ)

theorem DenR_pos (n : ℕ) : 0 < DenR n := by
  simp only [DenR]; exact_mod_cast DenIntN_pos n

/-! ## Cast identities for the prize interface -/

/-- **hwcast**: `(wInt n : ℝ) = DenR (n+1) * A2seq (n+1)`. -/
theorem wInt_cast_DenR (n : ℕ) :
    (wInt n : ℝ) = DenR (n + 1) * A2seq (n + 1) := by
  have hQ : (wInt n : ℚ) = (DenIntN (n + 1) : ℚ) * A2seqQ (n + 1) := wInt_rat n
  -- Cast: ℤ →[ℚ] wInt_rat →[ℝ] goal
  -- Use: (wInt n : ℝ) = ((wInt n : ℤ) : ℝ) and the ℤ → ℚ → ℝ chain commutes
  have hR : (wInt n : ℝ) = (DenIntN (n + 1) : ℝ) * (A2seqQ (n + 1) : ℝ) := by
    have : ((wInt n : ℤ) : ℝ) = ((DenIntN (n + 1) : ℕ) : ℝ) * (A2seqQ (n + 1) : ℝ) := by
      have key : ((wInt n : ℤ) : ℝ) = ((((DenIntN (n + 1) : ℕ) : ℚ) * A2seqQ (n + 1) : ℚ) : ℝ) := by
        rw [← hQ]; simp
      rw [key]; push_cast; ring
    exact_mod_cast this
  rw [hR, A2seqQ_cast]; simp [DenR]

/-- **hvcast**: `(vInt n : ℝ) = -(DenR (n+1) * (A1seq (n+1) + A2seq (n+1)))`. -/
theorem vInt_cast_DenR (n : ℕ) :
    (vInt n : ℝ) = -(DenR (n + 1) * (A1seq (n + 1) + A2seq (n + 1))) := by
  have hQ : (vInt n : ℚ) = -((DenIntN (n + 1) : ℚ) * (A1seqQ (n + 1) + A2seqQ (n + 1))) :=
    vInt_rat n
  have hR : (vInt n : ℝ) = -((DenIntN (n + 1) : ℝ) *
      ((A1seqQ (n + 1) : ℝ) + (A2seqQ (n + 1) : ℝ))) := by
    have : ((vInt n : ℤ) : ℝ) = -((DenIntN (n + 1) : ℝ) *
        ((A1seqQ (n + 1) : ℝ) + (A2seqQ (n + 1) : ℝ))) := by
      have key : ((vInt n : ℤ) : ℝ) =
          (((-((DenIntN (n + 1) : ℕ) : ℚ) * (A1seqQ (n + 1) + A2seqQ (n + 1))) : ℚ) : ℝ) := by
        have heq : -((DenIntN (n + 1) : ℕ) : ℚ) * (A1seqQ (n + 1) + A2seqQ (n + 1)) =
                   -((DenIntN (n + 1) : ℕ) : ℚ) * (A1seqQ (n + 1) + A2seqQ (n + 1)) := rfl
        rw [show (-((DenIntN (n + 1) : ℕ) : ℚ)) * (A1seqQ (n + 1) + A2seqQ (n + 1)) =
                -((DenIntN (n + 1) : ℕ) : ℚ) * (A1seqQ (n + 1) + A2seqQ (n + 1)) from rfl]
        simp only [neg_mul]
        rw [← hQ]; simp
      rw [key]; push_cast; ring
    exact_mod_cast this
  rw [hR, A1seqQ_cast, A2seqQ_cast]; simp [DenR]

end OSalikhovIntCoord
