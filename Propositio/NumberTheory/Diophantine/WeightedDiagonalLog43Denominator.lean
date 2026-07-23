import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Decomp
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# The 2,3-adic miracle: `lcm(1..n)` clears the denominator of `Pₙ`

The rational part `Pₙ = JP n` of the single-log decomposition `Jₙ = Pₙ + α₁(n)·log(4/3)` obeys the
Padé/Delannoy recurrence `(n+2)·P₍ₙ₊₂₎ = 7(2n+3)·P₍ₙ₊₁₎ − (n+1)·Pₙ`.  For the linear form
`lcm(1..n)·Jₙ = lcm(1..n)·Pₙ + lcm(1..n)·α₁(n)·log(4/3)` to have an **integer** rational part — the
shape required by the effective irrationality-measure construction — one needs

  `den(Pₙ) ∣ lcm(1..n)`     (the **2,3-adic miracle**, verified numerically for `n ≤ 38`).

This file proves the *integer-clearing consequence*

  `JP_den (n) : ∃ m : ℤ, (lcm(1..n) : ℚ) · Pₙ = m`

UNCONDITIONALLY from the denominator divisibility, and proves the denominator divisibility itself by
**strong (two-step) induction** off the recurrence.  All of the induction scaffolding is closed
unconditionally:

* `dvd_clears` — the elementary "`q.den ∣ N ⟹ N·q ∈ ℤ`" clearing reduction;
* `LcmGrowthBound.lcmUpto_dvd_of_le` / `key_dvd` — the lcm monotonicity and
  `lcm(lcm(1..n+1), n+2) ∣ lcm(1..n+2)` divisibility that absorbs the new `(n+2)` factor;
* `JP_den_dvd_lcm_of_step` — the two-step strong induction reducing `den(Pₙ) ∣ lcm(1..n)` to a single
  **per-step denominator bound** `hstep`.

The one irreducible arithmetic input is `hstep`:

  `hstep : ∀ n, (JP (n+2)).den ∣ Nat.lcm (Nat.lcm (JP (n+1)).den (JP n).den) (n+2)`,

i.e. *the division by `(n+2)` in the recurrence enlarges the denominator by at most `(n+2)`*.  This is
the genuine 2,3-adic content: the recurrence is over `ℚ` and dividing by `(n+2)` could in principle
multiply `den` by the full `(n+2)`, but the numerator
`7(2n+3)·P₍ₙ₊₁₎ − (n+1)·Pₙ` always shares enough factors with `(n+2)` that the bound holds (a
`gcd(num, n+2)` cancellation not derivable from generic `Rat.den` arithmetic — the general lemma
`den(a/m) ∣ lcm(den a, m)` is FALSE).  `hstep` is verified numerically for `n ≤ 38` and is left as a
named hypothesis; everything else is `sorry`-free and axiom-clean.
-/

namespace WeightedDiagonalLog43

open scoped Classical

/-- **The elementary clearing reduction.** If a natural number `N` is a multiple of `q.den`, then
`N·q` is an integer. -/
theorem dvd_clears {q : ℚ} {N : ℕ} (h : q.den ∣ N) : ∃ m : ℤ, (N : ℚ) * q = (m : ℚ) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * q.num, ?_⟩
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have key : (q.den : ℚ) * q = q.num := by
    have hqq : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    field_simp at hqq
    linarith [hqq]
  calc (N : ℚ) * q = (c : ℚ) * ((q.den : ℚ) * q) := by rw [hc]; push_cast; ring
    _ = ((c * q.num : ℤ) : ℚ) := by rw [key]; push_cast; ring

end WeightedDiagonalLog43

namespace LcmGrowthBound

/-- **lcm monotonicity.** `m ≤ n ⟹ lcm(1..m) ∣ lcm(1..n)`. -/
theorem lcmUpto_dvd_of_le {m n : ℕ} (hmn : m ≤ n) : lcmUpto m ∣ lcmUpto n := by
  rw [lcmUpto, lcmUpto]
  apply Finset.lcm_dvd
  intro b hb
  simp only [Finset.mem_Icc] at hb
  exact Finset.dvd_lcm (by simp only [Finset.mem_Icc]; omega)

/-- **The absorbing divisibility.** `lcm(lcm(1..n+1), n+2) ∣ lcm(1..n+2)`: the new modulus `(n+2)`
introduced by the recurrence's division is already present in `lcm(1..n+2)`. -/
theorem key_dvd (n : ℕ) :
    Nat.lcm (lcmUpto (n + 1)) (n + 2) ∣ lcmUpto (n + 2) := by
  apply Nat.lcm_dvd
  · exact lcmUpto_dvd_of_le (by omega)
  · exact dvd_lcmUpto (by omega) (by omega)

end LcmGrowthBound

namespace WeightedDiagonalLog43

open LcmGrowthBound

/-- **The denominator divisibility, conditional on the per-step bound.**  Strong (two-step) induction:
given the per-step bound `hstep`, `den(Pₙ) ∣ lcm(1..n)` for every `n`. -/
theorem JP_den_dvd_lcm_of_step
    (hstep : ∀ n, (JP (n + 2)).den ∣ Nat.lcm (Nat.lcm (JP (n + 1)).den (JP n).den) (n + 2))
    (n : ℕ) : (JP n).den ∣ lcmUpto n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp only [JP, lcmUpto]; norm_num
    | 1 => simp only [JP]; exact one_dvd _
    | (m + 2) =>
      have ihm : (JP m).den ∣ lcmUpto m := ih m (by omega)
      have ihm1 : (JP (m + 1)).den ∣ lcmUpto (m + 1) := ih (m + 1) (by omega)
      -- den(JP m) ∣ lcmUpto m ∣ lcmUpto (m+1)
      have ihm' : (JP m).den ∣ lcmUpto (m + 1) :=
        ihm.trans (lcmUpto_dvd_of_le (by omega))
      -- lcm(den(JP(m+1)), den(JP m)) ∣ lcmUpto (m+1)
      have hlcm12 : Nat.lcm (JP (m + 1)).den (JP m).den ∣ lcmUpto (m + 1) :=
        Nat.lcm_dvd ihm1 ihm'
      -- lcm(lcm(den(JP(m+1)),den(JP m)), m+2) ∣ lcm(lcmUpto(m+1), m+2) ∣ lcmUpto(m+2)
      have hbig : Nat.lcm (Nat.lcm (JP (m + 1)).den (JP m).den) (m + 2)
          ∣ lcmUpto (m + 2) := by
        refine (Nat.lcm_dvd ?_ ?_)
        · exact hlcm12.trans (lcmUpto_dvd_of_le (by omega))
        · exact dvd_lcmUpto (by omega) (by omega)
      exact (hstep m).trans hbig

/-- **`lcm(1..n)` clears the denominator of `Pₙ` (conditional on the per-step bound `hstep`).**
The 2,3-adic miracle in its integer-clearing form: `lcm(1..n)·Pₙ ∈ ℤ`. -/
theorem JP_den
    (hstep : ∀ n, (JP (n + 2)).den ∣ Nat.lcm (Nat.lcm (JP (n + 1)).den (JP n).den) (n + 2))
    (n : ℕ) : ∃ m : ℤ, (LcmGrowthBound.lcmUpto n : ℚ) * JP n = (m : ℚ) :=
  dvd_clears (JP_den_dvd_lcm_of_step hstep n)

end WeightedDiagonalLog43
