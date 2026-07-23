import Propositio.NumberTheory.Diophantine.OSalikhovDecomp
import Propositio.NumberTheory.Diophantine.OSalikhovSequences
import Propositio.NumberTheory.Diophantine.OSalikhovBaseTwo

/-!
# Grounding the decomposition base cases in the proved integral evaluations

`OSalikhovReduction.E1_decomp_of_rec` reduces `E1 = A1 + B·log(2/3)` to (Phase 3) + the three base
cases `E1(i) = A1(i) + B(i)·log(2/3)`, `i=0,1,2`.  Here we discharge `i=0,1` rigorously by matching
the PROVED integral values (`E1_zero`, `E1_one`, `E2_zero`, `E2_one`) against the recurrence
sequences' base window (`A1seq`, `A2seq`, `Bseq`).  Only `i=2` remains (its integral evaluation
`E1_two`/`E2_two` is memory-limited on this box — see the plan doc).
-/

namespace OSalikhovSequences

open OSalikhovTwoLog

/-- The `A1` sequence, recurrence-defined with base `A1(0..2) = 0, 199/36, 3674885/648`. -/
noncomputable def A1seq : ℕ → ℝ := seqR 0 (199 / 36) (3674885 / 648)

/-- Decomposition base case `i=0` for `E1`: `E1 0 = A1seq 0 + Bseq 0 · log(2/3)`. -/
theorem E1_decomp_base0 : E1 0 = A1seq 0 + Bseq 0 * Real.log (2 / 3) := by
  rw [E1_zero]; simp [A1seq, Bseq]

/-- Decomposition base case `i=1` for `E1`: `E1 1 = A1seq 1 + Bseq 1 · log(2/3)`. -/
theorem E1_decomp_base1 : E1 1 = A1seq 1 + Bseq 1 * Real.log (2 / 3) := by
  rw [E1_one]; simp [A1seq, Bseq]

/-- Decomposition base case `i=0` for `E2`: `E2 0 = A2seq 0 − Bseq 0 · log2`. -/
theorem E2_decomp_base0 : E2 0 = A2seq 0 - Bseq 0 * Real.log 2 := by
  rw [E2_zero]; simp [A2seq, Bseq]

/-- Decomposition base case `i=1` for `E2`: `E2 1 = A2seq 1 − Bseq 1 · log2`. -/
theorem E2_decomp_base1 : E2 1 = A2seq 1 - Bseq 1 * Real.log 2 := by
  rw [E2_one]; simp [A2seq, Bseq]

/-- Decomposition base case `i=2` for `E1`: `E1 2 = A1seq 2 + Bseq 2 · log(2/3)`. -/
theorem E1_decomp_base2 : E1 2 = A1seq 2 + Bseq 2 * Real.log (2 / 3) := by
  rw [E1_two]; simp [A1seq, Bseq]

/-- Decomposition base case `i=2` for `E2`: `E2 2 = A2seq 2 − Bseq 2 · log2`. -/
theorem E2_decomp_base2 : E2 2 = A2seq 2 - Bseq 2 * Real.log 2 := by
  rw [E2_two]; simp [A2seq, Bseq]

end OSalikhovSequences
