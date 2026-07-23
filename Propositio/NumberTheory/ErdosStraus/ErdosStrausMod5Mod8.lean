/-
  Erdős–Straus residue brick: `n ≡ 1 (mod 8)` AND `n ≡ 2 (mod 5)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  By CRT, `n ≡ 1 (mod 8) ∧ n ≡ 2 (mod 5) ⟺ n ≡ 17 (mod 40)`:
  writing `n = 8*a + 1`, the condition `n ≡ 2 (mod 5)` becomes
  `8*a + 1 ≡ 2 (mod 5)`, i.e. `3*a ≡ 1 (mod 5)`, i.e. `a ≡ 2 (mod 5)`
  (since `3 * 2 = 6 ≡ 1 (mod 5)`); writing `a = 5*b + 2` gives
  `n = 8*(5*b+2) + 1 = 40*b + 17`.

  This is a self-derived instance of Mordell's classical mod-5 covering
  identity (Mordell, *Diophantine Equations*, 1969, Ch. 30 Sec. 1; the QRs
  mod 5 are `{1,4}`, non-QRs `{2,3}` — this is the `n ≡ 2 (mod 5)` non-QR
  case). Writing `n = 40*m + 17`:

    x1 = (n+3)/4 = 10*m + 5
    Y  = n*(n+3)/2 = 10*n*(2*m+1)
    Z  = n*(n+3)/10 = 2*n*(2*m+1)

  and `4/n = 1/x1 + 1/Y + 1/Z`. Indeed, peeling `x1` first:
  `4*x1 - n = 4*(10*m+5) - (40*m+17) = 3`, so
  `4/n - 1/x1 = (4*x1 - n)/(n*x1) = 3/(n*x1) = 3/(5*n*(2*m+1))`
  (using `x1 = 5*(2*m+1)`). Splitting `3/5 = 1/10 + 1/2`:
  `1/Y + 1/Z = 1/(10*n*(2*m+1)) + 1/(2*n*(2*m+1))
            = (1/10 + 1/2)/(n*(2*m+1)) = (3/5)/(n*(2*m+1))`
  which matches.

  Smallest witness (`m = 0`, `n = 17`): `4/17 = 1/5 + 1/170 + 1/34`.

  This identity requires NO `r ∣ n` divisibility hypothesis (unlike the
  Mordell-ladder family in `ErdosStrausMordellGeneral.lean`). CORRECTION
  (caught by panel review 2026-07-10): the companion conjecture card's claim
  that individual instances of this family (e.g. `n = 17`) are unreachable
  from `erdos_straus_pq_family` is FALSE as stated — `n = 17` IS reachable
  there via `(p,q,t) = (1,6,1)`, giving the different witness triple
  `4/17 = 1/6 + 1/102 + 1/17`. The narrower, still-true claim: THIS SPECIFIC
  witness triple (`x1 = p*q*t` solved for the witnesses `5, 170, 34` above)
  is not a `pq_family` instance (solving forces `t = 4`, `p = 1/2`), and no
  single fixed `(p, q)` reproduces the whole `40*m + 17` family via
  `pq_family` for every `m` (checked: no `p*q ∣ 10` gives an integer `t` for
  all `m`). So this is a genuinely new covering identity as a *family*, even
  though some of its individual output values coincide with `pq_family`
  outputs under different parametrizations.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausMod5Mod8

/-- **`n ≡ 1 (mod 8) ∧ n ≡ 2 (mod 5)` case**, explicit witness: writing
`n = 40*m + 17`, `4/n = 1/(10*m+5) + 1/(10*n*(2*m+1)) + 1/(2*n*(2*m+1))`. -/
theorem erdos_straus_mod5_mod8 (m : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (40 * m + 17) = 1 / a + 1 / b + 1 / c := by
  refine ⟨10 * m + 5, 10 * (40 * m + 17) * (2 * m + 1),
    2 * (40 * m + 17) * (2 * m + 1), by omega, by positivity, by positivity, ?_⟩
  have h1 : ((10 : ℚ) * m + 5) ≠ 0 := by positivity
  have h2 : ((40 : ℚ) * m + 17) ≠ 0 := by positivity
  have h3 : ((2 : ℚ) * m + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 1 (mod 8) ∧ n ≡ 2 (mod 5)` case, `HasRep` form. -/
theorem hasRep_of_mod5_mod8 (m : ℕ) :
    ErdosStrausResidue.HasRep (40 * m + 17) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_mod5_mod8 m

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 17 = 1 / 5 + 1 / 170 + 1 / 34 := by norm_num
example : (4 : ℚ) / 57 = 1 / 15 + 1 / 1710 + 1 / 342 := by norm_num

end ErdosStrausMod5Mod8
