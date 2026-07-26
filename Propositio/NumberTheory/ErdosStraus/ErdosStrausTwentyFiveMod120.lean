/-
  Erdős–Straus residue brick: `n ≡ 25 (mod 120)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  This is the *fourth rung* of the Mordell ladder inside the hard sub-case
  `n ≡ 1 (mod 24)` (n = 24m+1), extending the rungs in
  `ErdosStrausFortyNineMod168.lean` (k=2, numerator 7, `a = 6m+2`) and
  `ErdosStrausElevenMod264.lean` (k=3, numerator 11, `a = 6m+3`). Rung `k`
  takes `a = 6m + k` (so `4a - n = 4k-1`, the leftover-fraction numerator):

    k = 1 : a = 6m+1, numerator 3 — the mod-3 obstruction (blocked for every m).
    k = 2 : a = 6m+2, numerator 7 — splits when `7 ∣ n`, giving `n ≡ 49 (mod 168)`.
    k = 3 : a = 6m+3, numerator 11 — splits when `11 ∣ n`, giving `n ≡ 121 (mod 264)`.
    k = 4 : a = 6m+4, numerator 15 — splits when `5 ∣ n` (composite numerator 15=3*5).

  Writing `n = 24m+1`, `a = 6m+4`, the leftover is `15/(an)`. Checking residues
  mod 3: `6m+4 ≡ 1 (mod 3)` identically, while `24m+1 ≡ 1 (mod 3)` identically,
  so the mod-3 obstruction blocks the direct factorization `15 ∣ n`. However, we
  CAN split on `5 ∣ n` alone. Since `n = 4a - 15`, `5 ∣ n ⟺ 5 ∣ (4a - 15)`.
  Checking mod 5: `6m+4 ≡ m+4 (mod 5)`, so `4a-15 ≡ 4m+16-15 ≡ 4m+1 (mod 5)`.
  This vanishes when `m ≡ 1 (mod 5)`, i.e. `m = 5s+1`, giving `n = 24(5s+1)+1
  = 120s+25` and `a = 6(5s+1)+4 = 30s+10`.

  Writing `n = 120s+25 = 5·(24s+5)` and `a = 30s+10 = 10·(3s+1)` (always even),
  set `n' = 24s+5` (so `n = 5·n'`). The leftover `15/(a·n)` becomes `3/(a·n')`,
  which we split in half via the fact that `a·n'` is always even (since `a` is even):

    3/(a·n') = 1/(a·n') + 2/(a·n') = 1/(a·n') + 1/(a·n'/2)

  This is a *two-step* split, unlike k=2/k=3's single prime-divide-then-halve:
  first we use `5 ∣ n` to reduce 15→3, then we use the mandatory evenness of `a`
  to split 3 in half. So:

    4/n = 1/a + 1/(a·n') + 1/(a·n'/2),   a = 30s+10,  n' = 24s+5.

  Algebraic check: `4a = 120s+40 = 5·(24s+5) + 15 = 5·(n'+3)`, confirming
  `1/a + 3/(a·n') = (n'+3)/(a·n') = 4a/(5·a·n') = 4/(5·n') = 4/n` for every
  `s ≥ 0` — no factorization luck required.

  `n = 120s+25 ≡ 1 (mod 24)` and `≡ 1 (mod 5)`, so this class sits genuinely
  inside the previously-open gap `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}`.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausTwentyFiveMod120

/-- **`n ≡ 25 (mod 120)` case**, explicit witness: writing `n = 120*s + 25`,
`a = 30*s + 10`, `n' = 24*s + 5` (so `n = 5*n'` and `4*a = 5*(n'+3)`),
`4/n = 1/a + 1/(a*n') + 1/(a*n'/2)`. Since `a = 10*(3*s+1)` is always even,
`a*n'/2 = 5*(3*s+1)*(24*s+5)` is a natural number. -/
theorem erdos_straus_twentyfive_mod_120 (s : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (120 * s + 25) = 1 / a + 1 / b + 1 / c := by
  refine ⟨30 * s + 10, (30 * s + 10) * (24 * s + 5),
    5 * (3 * s + 1) * (24 * s + 5), by omega, by positivity, by positivity, ?_⟩
  have ha : ((30 : ℚ) * s + 10) ≠ 0 := by positivity
  have hn' : ((24 : ℚ) * s + 5) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 25 (mod 120)` case, `HasRep` form. -/
theorem hasRep_of_twentyfive_mod_120 (s : ℕ) :
    ErdosStrausResidue.HasRep (120 * s + 25) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_twentyfive_mod_120 s

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 25 = 1 / 10 + 1 / 50 + 1 / 25 := by norm_num
example : (4 : ℚ) / 145 = 1 / 40 + 1 / 1160 + 1 / 580 := by norm_num
example : (4 : ℚ) / 265 = 1 / 70 + 1 / 3710 + 1 / 1855 := by norm_num

end ErdosStrausTwentyFiveMod120
