import Propositio.NumberTheory.Diophantine.OSalikhovHeight
import Propositio.NumberTheory.Diophantine.OSalikhovPerfectSystem

/-!
# Concrete oSALIKHOV recurrence sequences and their recurrence-side properties

Defines `seqR b₀ b₁ b₂ : ℕ → ℝ` — the solution of the oSALIKHOV order-3 recurrence with prescribed
base window — via a 3-state window recursion, and proves it satisfies the recurrence (`seqR_rec`).
Instantiating at the verified base values gives the concrete recurrence-side results in one place:
positivity (heart of `hwpos`), height `≤ M·4501ⁿ` (recurrence side of `hwden`), and the lower bound
`≥ 1000ᵐ` (toward `hsmall`).

(These are about the recurrence-*defined* sequences; identifying them with the integral residues
`A1,A2,B` is the Phase-3 Gosper-certificate step, not done here.)
-/

namespace OSalikhovSequences

open OSalikhovHeight

/-- One recurrence step on a window `(X n, X(n+1), X(n+2)) ↦ (X(n+1), X(n+2), X(n+3))`. -/
noncomputable def stepR (n : ℕ) (w : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (w.2.1, w.2.2, (-(p2R n * w.2.2 + p1R n * w.2.1 + p0R n * w.1)) / p3R n)

/-- The window `(seqR n, seqR (n+1), seqR (n+2))`. -/
noncomputable def win (b0 b1 b2 : ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => (b0, b1, b2)
  | (n + 1) => stepR n (win b0 b1 b2 n)

/-- The solution sequence with base window `b0,b1,b2`. -/
noncomputable def seqR (b0 b1 b2 : ℝ) (n : ℕ) : ℝ := (win b0 b1 b2 n).1

variable (b0 b1 b2 : ℝ)

@[simp] theorem seqR_zero : seqR b0 b1 b2 0 = b0 := rfl
@[simp] theorem seqR_one : seqR b0 b1 b2 1 = b1 := rfl
@[simp] theorem seqR_two : seqR b0 b1 b2 2 = b2 := rfl

/-- `seqR (n+1)` is the 2nd window component (definitional). -/
theorem seqR_succ1 (n : ℕ) : seqR b0 b1 b2 (n + 1) = (win b0 b1 b2 n).2.1 := rfl
/-- `seqR (n+2)` is the 3rd window component (definitional). -/
theorem seqR_succ2 (n : ℕ) : seqR b0 b1 b2 (n + 2) = (win b0 b1 b2 n).2.2 := rfl

/-- `seqR` satisfies the oSALIKHOV order-3 recurrence. -/
theorem seqR_rec (n : ℕ) :
    p3R n * seqR b0 b1 b2 (n + 3) + p2R n * seqR b0 b1 b2 (n + 2)
      + p1R n * seqR b0 b1 b2 (n + 1) + p0R n * seqR b0 b1 b2 n = 0 := by
  have hp3 : p3R n ≠ 0 := ne_of_gt (p3R_pos n)
  have key : seqR b0 b1 b2 (n + 3)
      = (-(p2R n * seqR b0 b1 b2 (n + 2) + p1R n * seqR b0 b1 b2 (n + 1)
          + p0R n * seqR b0 b1 b2 n)) / p3R n := by
    rw [seqR_succ2, seqR_succ1, show seqR b0 b1 b2 n = (win b0 b1 b2 n).1 from rfl]
    rfl
  rw [key]; field_simp; ring

/-! ## Concrete sequences `A2seq`, `Bseq` and their recurrence-side properties -/

/-- The residue sequence `B`, recurrence-defined with verified base `B(0..2)=1/30, 409/30, 139867/10`. -/
noncomputable def Bseq : ℕ → ℝ := seqR (1 / 30) (409 / 30) (139867 / 10)
/-- The `A2` sequence, recurrence-defined with base `A2(0..2)=0, 189/20, 1163381/120`. -/
noncomputable def A2seq : ℕ → ℝ := seqR 0 (189 / 20) (1163381 / 120)

theorem Bseq_rec (n : ℕ) :
    p3R n * Bseq (n + 3) + p2R n * Bseq (n + 2) + p1R n * Bseq (n + 1) + p0R n * Bseq n = 0 :=
  seqR_rec _ _ _ n
theorem A2seq_rec (n : ℕ) :
    p3R n * A2seq (n + 3) + p2R n * A2seq (n + 2) + p1R n * A2seq (n + 1) + p0R n * A2seq n = 0 :=
  seqR_rec _ _ _ n

/-- Base window of `A2seq`: `0 < A2(1)=9.45 ≤ A2(2)=9694.8 ≤ A2(3)`. -/
theorem A2seq_base : 0 < A2seq 1 ∧ A2seq 1 ≤ A2seq 2 ∧ A2seq 2 ≤ A2seq 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [A2seq, seqR, win, stepR, p0R, p1R, p2R, p3R] <;> norm_num

/-- **`hwpos` (concrete)**: `A2seq` is strictly positive for `n ≥ 1`. -/
theorem A2seq_pos (m : ℕ) : 0 < A2seq (1 + m) :=
  OSalikhovHeight.solution_pos A2seq A2seq_rec 1 A2seq_base.1 A2seq_base.2.1 A2seq_base.2.2 m

/-- **`hwden` recurrence side (concrete)**: `|A2seq n| ≤ 10000·4501ⁿ`. -/
theorem A2seq_height (n : ℕ) : |A2seq n| ≤ 10000 * 4501 ^ n := by
  refine OSalikhovHeight.solution_height A2seq 10000 (by norm_num) A2seq_rec ?_ ?_ ?_ n <;>
    simp only [A2seq, seqR, win, stepR, p0R, p1R, p2R, p3R] <;> rw [abs_le] <;>
      constructor <;> norm_num

/-- **Sharp `hwden` recurrence side (concrete)**: `|A2seq n| ≤ 10000·1500ⁿ` (rate `1500` vs `4501`).
Uses `solution_upper` (rate `1500` from the `|p₂+p₁|/p₃ ≤ 1500` one-step upper bound) for `n ≥ 3`
and explicit `norm_num` for `n = 0, 1, 2`. -/
theorem A2seq_height_1500 (n : ℕ) : |A2seq n| ≤ 10000 * 1500 ^ n := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · -- n ∈ {0, 1, 2}: explicit norm_num
    interval_cases n
    · simp [A2seq, seqR_zero]
    · simp only [A2seq, seqR_one]; rw [abs_le]; constructor <;> norm_num
    · simp only [A2seq, seqR_two]; rw [abs_le]; constructor <;> norm_num
  · -- n ≥ 3: write n = 3 + m
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m := ⟨n - 3, by omega⟩
    -- A2seq is positive and non-decreasing from index 1
    have hbase := A2seq_base
    -- solution_upper (k=1): A2seq(1+2+m) ≤ 1500^m * A2seq(1+2)
    have hupper := OSalikhovHeight.solution_upper A2seq A2seq_rec 1
      hbase.1 hbase.2.1 hbase.2.2 m
    -- A2seq(3+m) is positive (from A2seq_pos)
    have hpos : 0 < A2seq (3 + m) := by
      have h := A2seq_pos (m + 2)
      have heq2 : 1 + (m + 2) = 3 + m := by ring
      rwa [heq2] at h
    rw [abs_of_pos hpos]
    -- hupper: A2seq(1+2+m) ≤ 1500^m * A2seq(1+2)
    -- i.e., A2seq(3+m) ≤ 1500^m * A2seq 3
    have heq : (1 : ℕ) + 2 + m = 3 + m := by ring
    rw [heq] at hupper
    -- Need: 1500^m * A2seq 3 ≤ 10000 * 1500^(3+m) = 10000 * 1500^3 * 1500^m
    -- Suffices: A2seq 3 ≤ 10000 * 1500^3
    have hA23 : A2seq 3 ≤ 10000 * 1500 ^ 3 := by
      simp only [A2seq, seqR, win, stepR, p0R, p1R, p2R, p3R]; norm_num
    calc A2seq (3 + m) ≤ 1500 ^ m * A2seq 3 := hupper
      _ ≤ 1500 ^ m * (10000 * 1500 ^ 3) := by
          apply mul_le_mul_of_nonneg_left hA23 (pow_nonneg (by norm_num) m)
      _ = 10000 * 1500 ^ (3 + m) := by ring

/-- **toward `hsmall` (concrete)**: `A2seq(3+m) ≥ 1000ᵐ·A2seq 3`. -/
theorem A2seq_lower (m : ℕ) : 1000 ^ m * A2seq 3 ≤ A2seq (3 + m) := by
  have := OSalikhovHeight.solution_lower A2seq A2seq_rec 1
    A2seq_base.1 A2seq_base.2.1 A2seq_base.2.2 m
  simpa using this

/-- Base window of `Bseq`: `0 < B(0)=1/30 ≤ B(1)=13.6 ≤ B(2)=13986.7`. -/
theorem Bseq_base : 0 < Bseq 0 ∧ Bseq 0 ≤ Bseq 1 ∧ Bseq 1 ≤ Bseq 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Bseq, seqR_zero, seqR_one, seqR_two] <;> norm_num

/-- **`Bseq` positive** for all `n` (residue positivity `B(n) > 0`). -/
theorem Bseq_pos (m : ℕ) : 0 < Bseq m := by
  simpa using OSalikhovHeight.solution_pos Bseq Bseq_rec 0 Bseq_base.1 Bseq_base.2.1 Bseq_base.2.2 m

/-- **`Bseq` exponential lower bound** `Bseq(2+m) ≥ 1000ᵐ·Bseq 2` — the concrete `hsmall` B-decay
ingredient (`B(n) ≥ c·1000ⁿ`). -/
theorem Bseq_lower (m : ℕ) : 1000 ^ m * Bseq 2 ≤ Bseq (2 + m) :=
  OSalikhovHeight.solution_lower Bseq Bseq_rec 0 Bseq_base.1 Bseq_base.2.1 Bseq_base.2.2 m

end OSalikhovSequences
