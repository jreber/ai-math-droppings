/-
  Erdős–Straus residue brick: `n ≡ 529 (mod 552)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  This is the *fifth rung* of the Mordell ladder inside the hard sub-case
  `n ≡ 1 (mod 24)` (n = 24m+1), continuing `ErdosStrausFortyNineMod168.lean`
  (k = 2, numerator 7, `a = 6m+2`), `ErdosStrausElevenMod264.lean` (k = 3,
  numerator 11, `a = 6m+3`), and `ErdosStrausThreeSixtyOneMod456.lean`
  (k = 5, numerator 19, `a = 6m+5`). Rung `k` takes `a = 6m + k` (so
  `4a - n = 4k-1`, i.e. the leftover-fraction numerator is `r = 4k-1`):

    k = 1 : a = 6m+1, numerator 3  — the mod-3 obstruction documented in
            `ErdosStrausFortyNineMod168.lean` (blocked identically for
            every m, since `n ≡ 1 (mod 3)` always but `3 ∣ r` here).
    k = 2 : a = 6m+2, numerator 7  — splits when `7 ∣ n`, giving
            `n ≡ 49 (mod 168)`.
    k = 3 : a = 6m+3, numerator 11 — splits when `11 ∣ n`, giving
            `n ≡ 121 (mod 264)`.
    k = 4 : a = 6m+4, numerator 15 — NOT a viable rung: `gcd(24,15) = 3`,
            the SAME mod-3 obstruction as k = 1.
    k = 5 : a = 6m+5, numerator 19 — splits when `19 ∣ n`, giving
            `n ≡ 361 (mod 456)`.
    k = 6 : a = 6m+6, numerator 23 — prime, `gcd(24,23) = 1`, genuinely
            viable (the mod-3 obstruction hits exactly `k ≡ 1 (mod 3)`,
            i.e. `k = 1, 4, 7, ...`; `k = 6` is safely `≡ 0 (mod 3)`).
            THIS brick.

  Writing `n = 24m+1`, `a = 6m+6`, the leftover is `23/(an)` (since
  `4a - n = 24m+24 - 24m-1 = 23`). This splits into a single unit fraction
  exactly when `23 ∣ n`. Since `n = 4a - 23`, `23 ∣ n ⟺ 23 ∣ a`, and
  `a = 6(m+1)` with `gcd(6,23) = 1`, so `23 ∣ a ⟺ 23 ∣ (m+1) ⟺ m ≡ 22 (mod 23)`,
  i.e. `n ≡ 24·22 + 1 = 529 (mod 552)` (`552 = 24·23`).

  Writing `n = 552u + 529 = 23·(24u+23)` and `a = 138u+138 = 23·(6u+6)`, set
  `n' = 24u+23` (so `n = 23 n'`). Then:

    4/n − 1/a = 23/(a n) = 23/(a · 23 · n') = 1/(a n')

  which splits trivially in half: `1/(a n') = 1/(2 a n') + 1/(2 a n')`. So:

    4/n = 1/a + 1/(2 a n') + 1/(2 a n'),   a = 138u+138,  n' = 24u+23.

  Algebraic check: `4a = 552u + 552` and `23·(n'+1) = 23·(24u+24) =
  552u + 552`, so `4a = 23(n'+1)`, hence `1/a + 1/(a n') = (n'+1)/(a n')
  = 4a/(23 a n') = 4/(23 n') = 4/n` for every `u ≥ 0` — no factorization
  luck required.

  `n = 552u+529 ≡ 1 (mod 24)` and `≡ 1 (mod 3)`, so this class sits inside
  the previously-open gap `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}`
  (`ErdosStrausResidue.nonRep_subset_one_mod_four_not_three_dvd`), disjoint
  from `ErdosStrausThirteenMod24` (which needs `n ≡ 13 (mod 24)`). As with
  the earlier rungs, it is NOT fully disjoint from `ErdosStrausFortyNineMod168`,
  `ErdosStrausElevenMod264`, or `ErdosStrausThreeSixtyOneMod456` mod smaller
  moduli — such overlaps are harmless (a second, different witness) and the
  bulk of instances give genuinely new coverage.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausFiveTwentyNineMod552

/-- **`n ≡ 529 (mod 552)` case**, explicit witness: writing `n = 552*u + 529`,
`a = 138*u + 138`, `n' = 24*u + 23` (so `n = 23*n'` and `4*a = 23*(n'+1)`),
`4/n = 1/a + 1/(2*a*n') + 1/(2*a*n')`. -/
theorem erdos_straus_fiveTwentyNine_mod_552 (u : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (552 * u + 529) = 1 / a + 1 / b + 1 / c := by
  refine ⟨138 * u + 138, 2 * (138 * u + 138) * (24 * u + 23),
    2 * (138 * u + 138) * (24 * u + 23), by omega, by positivity, by positivity, ?_⟩
  have ha : ((138 : ℚ) * u + 138) ≠ 0 := by positivity
  have hn' : ((24 : ℚ) * u + 23) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 529 (mod 552)` case, `HasRep` form. -/
theorem hasRep_of_fiveTwentyNine_mod_552 (u : ℕ) :
    ErdosStrausResidue.HasRep (552 * u + 529) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_fiveTwentyNine_mod_552 u

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 529 = 1 / 138 + 1 / 6348 + 1 / 6348 := by norm_num
example : (4 : ℚ) / 1081 = 1 / 276 + 1 / 25944 + 1 / 25944 := by norm_num
example : (4 : ℚ) / 1633 = 1 / 414 + 1 / 58788 + 1 / 58788 := by norm_num

end ErdosStrausFiveTwentyNineMod552
