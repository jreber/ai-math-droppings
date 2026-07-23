/-
  Erdős–Straus residue brick: `n ≡ 121 (mod 264)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  This is the *third rung* of the Mordell ladder inside the hard sub-case
  `n ≡ 1 (mod 24)` (n = 24m+1), continuing `ErdosStrausFortyNineMod168.lean`
  (numerator 7, `a = 6m+2`). Rung `k` takes `a = 6m + k` (so `4a - n = 4k-1`,
  i.e. the leftover-fraction numerator is `4k-1`):

    k = 1 : a = 6m+1, numerator 3 — the mod-3 obstruction documented in
            `ErdosStrausFortyNineMod168.lean` (blocked identically for every m).
    k = 2 : a = 6m+2, numerator 7 — splits when `7 ∣ n`, giving `n ≡ 49 (mod 168)`.
    k = 3 : a = 6m+3, numerator 11 — splits when `11 ∣ n`, giving THIS brick.

  Writing `n = 24m+1`, `a = 6m+3`, the leftover is `11/(an)` (since
  `4a - n = 24m+12 - 24m-1 = 11`). This splits into a single unit fraction
  exactly when `11 ∣ n`. Since `n = 4a - 11`, `11 ∣ n ⟺ 11 ∣ a`, and (checking
  residues mod 11, using `24 ≡ 2 (mod 11)`) `11 ∣ n ⟺ 2m+1 ≡ 0 (mod 11) ⟺
  m ≡ 5 (mod 11)`, i.e. `n ≡ 121 (mod 264)` (`264 = 24·11`).

  Writing `n = 264t + 121 = 11·(24t+11)` and `a = 66t+33 = 3·(22t+11)`, set
  `n' = 24t+11` (so `n = 11 n'`). Then:

    4/n − 1/a = 11/(a n) = 11/(a · 11 · n') = 1/(a n')

  which splits trivially in half: `1/(a n') = 1/(2 a n') + 1/(2 a n')`. So:

    4/n = 1/a + 1/(2 a n') + 1/(2 a n'),   a = 66t+33,  n' = 24t+11.

  Algebraic check: `4a = 264t + 132` and `11·(n'+1) = 11·(24t+12) = 264t+132`,
  so `4a = 11(n'+1)`, hence `1/a + 1/(a n') = (n'+1)/(a n') = 4a/(11 a n')
  = 4/(11 n') = 4/n` for every `t ≥ 0` — no factorization luck required.

  `n = 264t+121 ≡ 1 (mod 24)` and `≡ 1 (mod 3)`, so this class sits inside
  the previously-open gap `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}`
  (`ErdosStrausResidue.nonRep_subset_one_mod_four_not_three_dvd`), disjoint
  from `ErdosStrausThirteenMod24` (which needs `n ≡ 13 (mod 24)`). It is NOT
  fully disjoint from `ErdosStrausFortyNineMod168`: mod 168 the residue
  `264t+121` cycles through `{121, 49, 145, 73, 1, 97, 25}` as `t` ranges over
  a period of 7, so 1 residue class in 7 (`t ≡ 1 (mod 7)`) coincides with
  `n ≡ 49 (mod 168)`. This is harmless (a second, different witness on the
  overlap) and the remaining 6/7 of instances (e.g. `t = 0, 2, 3, 4, 5, 6`,
  giving `n = 121, 649, 913, 1177, 1441, 1705`) are genuinely new coverage.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausElevenMod264

/-- **`n ≡ 121 (mod 264)` case**, explicit witness: writing `n = 264*t + 121`,
`a = 66*t + 33`, `n' = 24*t + 11` (so `n = 11*n'` and `4*a = 11*(n'+1)`),
`4/n = 1/a + 1/(2*a*n') + 1/(2*a*n')`. -/
theorem erdos_straus_eleven_mod_264 (t : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (264 * t + 121) = 1 / a + 1 / b + 1 / c := by
  refine ⟨66 * t + 33, 2 * (66 * t + 33) * (24 * t + 11),
    2 * (66 * t + 33) * (24 * t + 11), by omega, by positivity, by positivity, ?_⟩
  have ha : ((66 : ℚ) * t + 33) ≠ 0 := by positivity
  have hn' : ((24 : ℚ) * t + 11) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 121 (mod 264)` case, `HasRep` form. -/
theorem hasRep_of_eleven_mod_264 (t : ℕ) :
    ErdosStrausResidue.HasRep (264 * t + 121) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_eleven_mod_264 t

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 121 = 1 / 33 + 1 / 726 + 1 / 726 := by norm_num
example : (4 : ℚ) / 649 = 1 / 165 + 1 / 19470 + 1 / 19470 := by norm_num
example : (4 : ℚ) / 913 = 1 / 231 + 1 / 38346 + 1 / 38346 := by norm_num

end ErdosStrausElevenMod264
