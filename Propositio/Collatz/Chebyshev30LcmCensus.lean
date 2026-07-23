import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Tactic

/-!
# Chebyshev-30 lcm pin: the finite census `n < 8500`

`CollatzChebyshev30LcmPinSharp.lean` proves the prize denominator target
`30·lcm(1..2n) ≤ 6·10ⁿ` for all `n ≥ 8500` (analytic, axiom-clean).  The target is TRUE for
every `n ≥ 1` (it fails only at `n = 0`, where `30·1 = 30 > 6`), with equality at `n = 1`
(`30·2 = 60 = 6·10`) and ratio `→ 0` thereafter.  This file discharges the remaining finite
window `1 ≤ n < 8500` by a single `native_decide` over a **verified incremental checker**
(`censusAux`) that sweeps `lcm(1..2n)` once — avoiding the `O(N²)` cost of recomputing
`lcm(1..2n)` for each `n`.

Combined with the sharp pin this yields `hlcm` for all `n ≥ 1`, the second of the two
non-transcendence inputs of `OSalikhovDenDvd.DenIntN_bound_30_of_inputs`.
-/

namespace CollatzChebyshev30

open LcmGrowthBound

/-- **lcm monotonicity** (inlined from `WeightedDiagonalLog43Denominator`). -/
theorem lcmUpto_dvd_of_le {m n : ℕ} (hmn : m ≤ n) : lcmUpto m ∣ lcmUpto n := by
  rw [lcmUpto, lcmUpto]
  apply Finset.lcm_dvd
  intro b hb
  simp only [Finset.mem_Icc] at hb
  exact Finset.dvd_lcm (by simp only [Finset.mem_Icc]; omega)

/-- **The lcm recurrence.** `lcm(1..k+1) = lcm(lcm(1..k), k+1)`. -/
theorem lcmUpto_succ (k : ℕ) : lcmUpto (k + 1) = Nat.lcm (lcmUpto k) (k + 1) := by
  apply Nat.dvd_antisymm
  · rw [lcmUpto]
    apply Finset.lcm_dvd
    intro b hb
    simp only [Finset.mem_Icc] at hb
    rcases Nat.lt_or_ge b (k + 1) with h | h
    · exact (dvd_lcmUpto hb.1 (by omega)).trans (Nat.dvd_lcm_left _ _)
    · have hbk : b = k + 1 := by omega
      subst hbk
      exact Nat.dvd_lcm_right _ _
  · apply Nat.lcm_dvd
    · exact lcmUpto_dvd_of_le (by omega)
    · exact dvd_lcmUpto (by omega) (le_refl _)

/-- Small explicit values. -/
theorem lcmUpto_zero : lcmUpto 0 = 1 := by
  rw [lcmUpto]
  rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by rfl]
  simp

theorem lcmUpto_one : lcmUpto 1 = 1 := by
  rw [lcmUpto_succ, lcmUpto_zero]; rfl

theorem lcmUpto_two : lcmUpto 2 = 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, lcmUpto_succ, lcmUpto_one]; rfl

/-- **The incremental census checker.**  `censusAux s n acc ten` is meant to be called with
`acc = lcm(1..2n)` and `ten = 10ⁿ`.  It checks `30·acc ≤ 6·ten` at the current `n` and recurses
for `s` further steps, stepping `acc` to `lcm(1..2(n+1))` (two lcm steps) and `ten` to `10ⁿ⁺¹`. -/
def censusAux : ℕ → ℕ → ℕ → ℕ → Bool
  | 0,     _, _,   _   => true
  | s + 1, n, acc, ten =>
      decide (30 * acc ≤ 6 * ten) &&
        censusAux s (n + 1) (Nat.lcm (Nat.lcm acc (2 * n + 1)) (2 * n + 2)) (10 * ten)

/-- **Soundness of the checker.**  If `censusAux s n (lcm(1..2n)) 10ⁿ = true`, then the target
`30·lcm(1..2(n+j)) ≤ 6·10ⁿ⁺ʲ` holds for every `j < s`. -/
theorem censusAux_sound (s : ℕ) :
    ∀ n acc ten, acc = lcmUpto (2 * n) → ten = 10 ^ n →
      censusAux s n acc ten = true →
      ∀ j, j < s → 30 * lcmUpto (2 * (n + j)) ≤ 6 * 10 ^ (n + j) := by
  induction s with
  | zero => intro n acc ten _ _ _ j hj; omega
  | succ s ih =>
    intro n acc ten hacc hten h j hj
    rw [censusAux, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hbase : 30 * acc ≤ 6 * ten := of_decide_eq_true h1
    match j with
    | 0 =>
      simpa [hacc, hten] using hbase
    | j + 1 =>
      -- step the accumulator and the power of ten
      have hacc' : Nat.lcm (Nat.lcm acc (2 * n + 1)) (2 * n + 2) = lcmUpto (2 * (n + 1)) := by
        rw [hacc]
        have e1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
        have e2 : (2 * n + 1 : ℕ) = (2 * n) + 1 := by ring
        rw [e1, lcmUpto_succ, e2, lcmUpto_succ]
      have hten' : 10 * ten = 10 ^ (n + 1) := by rw [hten, pow_succ]; ring
      have hrec := ih (n + 1) (Nat.lcm (Nat.lcm acc (2 * n + 1)) (2 * n + 2)) (10 * ten)
        hacc' hten' h2 j (by omega)
      have eidx : n + 1 + j = n + (j + 1) := by omega
      rwa [eidx] at hrec

/-- **The finite census.**  `30·lcm(1..2n) ≤ 6·10ⁿ` for every `1 ≤ n < 8500`,
established by one `native_decide` over the incremental checker. -/
theorem census_1_to_8499 (n : ℕ) (h1 : 1 ≤ n) (hn : n < 8500) :
    30 * lcmUpto (2 * n) ≤ 6 * 10 ^ n := by
  have hchk : censusAux 8499 1 2 10 = true := by native_decide
  have hsound := censusAux_sound 8499 1 2 10 (by rw [lcmUpto_two]) (by norm_num) hchk
  obtain ⟨j, rfl⟩ : ∃ j, n = 1 + j := ⟨n - 1, by omega⟩
  exact hsound j (by omega)

#print axioms census_1_to_8499

end CollatzChebyshev30
