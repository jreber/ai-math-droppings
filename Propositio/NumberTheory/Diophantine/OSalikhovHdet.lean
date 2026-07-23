import Propositio.NumberTheory.Diophantine.OSalikhovCasoratian
import Propositio.NumberTheory.Diophantine.OSalikhovSequences

/-!
# `hdet` discharged on the concrete oSALIKHOV recurrence sequences

`OSalikhovCasoratian.casoratian2_ne_zero` is the generic non-vanishing of the 2×2 Casoratian
`C2(X,Y,k) = X(k)·Y(k+1) − X(k+1)·Y(k)` for two solutions of the oSALIKHOV order-3 recurrence with a
positive non-decreasing sign-folded base window.  Here we instantiate it at the concrete
recurrence-defined sequences `A1seq, A2seq` (base values from the verified construction:
`A1(0..2) = 0, 199/36, 3674885/648`, `A2(0..2) = 0, 189/20, 1163381/120`).  The sign-folded base
window is `cfold(1..3) = 617/540, 721649/36450, 359458663/567000` — positive and increasing — so

`C2(A1seq, A2seq, k) ≠ 0` for every `k ≥ 1`,

the **recurrence side of the interface's `hdet`** (the consecutive 2×2 determinant of the cleared
two-log coordinates is `Den·Den·C2`, non-zero for the one-step-shifted `v,w`).  This sits alongside
`A2seq_pos` (`hwpos`), `A2seq_height` (`hwden`), `Bseq_lower` (`hsmall` B-decay) as the
recurrence-side discharge; the integral identification (Phase 3) is the remaining connector — the
same one all four interface clauses share. -/

namespace OSalikhovHdet

open OSalikhovHeight OSalikhovSequences OSalikhovCasoratian

/-- The `A1` sequence, recurrence-defined with base `A1(0..2) = 0, 199/36, 3674885/648`. -/
noncomputable def A1seq : ℕ → ℝ := seqR 0 (199 / 36) (3674885 / 648)

theorem A1seq_rec : Rec A1seq := fun n => seqR_rec _ _ _ n
theorem A2seq_rec : Rec A2seq := fun n => seqR_rec _ _ _ n

/-- The sign-folded Casoratian base window `0 < cfold 1 ≤ cfold 2 ≤ cfold 3`
(`= 617/540, 721649/36450, 359458663/567000`). -/
theorem cfold_base :
    0 < cfold A1seq A2seq 1 ∧ cfold A1seq A2seq 1 ≤ cfold A1seq A2seq 2
      ∧ cfold A1seq A2seq 2 ≤ cfold A1seq A2seq 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cfold, C2, A1seq, A2seq, seqR, win, stepR, p0R, p1R, p2R, p3R] <;> norm_num

/-- **`hdet` (concrete, recurrence side).**  The 2×2 Casoratian of the oSALIKHOV sequences never
vanishes for `k ≥ 1`. -/
theorem casoratian_concrete_ne_zero (k : ℕ) (hk : 1 ≤ k) : C2 A1seq A2seq k ≠ 0 :=
  casoratian2_ne_zero A1seq_rec A2seq_rec cfold_base.1 cfold_base.2.1 cfold_base.2.2 k hk

end OSalikhovHdet
