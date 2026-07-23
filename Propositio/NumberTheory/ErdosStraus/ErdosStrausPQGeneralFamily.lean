/-
  Erdős–Straus: the general two-parameter `(p, q, t)` covering-identity family.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  `ErdosStrausFamily168m145.lean` proves ONE instance of a covering identity
  where `a` is divisible by two *fixed* constants (`2` and `21`) by
  construction, not because a factor of `n` forces it — structurally
  different from the Mordell ladder (`ErdosStrausMordellGeneral.lean`, where
  `a` picks up a factor of `n` itself via an `r ∣ n` side condition).

  This file generalizes that single instance into a genuine two-free-parameter
  theorem, exactly the way `ErdosStrausMordellGeneral.erdos_straus_mordell_general`
  generalized the Mordell ladder's numeral rungs `k = 2, 3, 5, 6` into one
  `k`-parametrized theorem.

  **Setup.** For `p q t n : ℕ` with `0 < p`, `0 < q`, `0 < t`, and the linear
  relation `n + p + q = 4*p*q*t` (stated additively to avoid `ℕ`
  truncated-subtraction), set

    `a = p*q*t`,  `b = q*t*n`,  `c = p*t*n`.

  Since `a = p*q*t` is divisible by both `p` (`a/p = q*t`) and `q`
  (`a/q = p*t`) *by construction* — no coprimality or divisibility
  side-condition on `p, q, n` is needed at all:

    `1/b + 1/c = 1/(q*t*n) + 1/(p*t*n) = p/(a*n) + q/(a*n) = (p+q)/(a*n)`

  so

    `1/a + 1/b + 1/c = (n + p + q)/(a*n) = 4*p*q*t/(a*n) = 4*a/(a*n) = 4/n`

  using exactly the defining relation `n + p + q = 4*p*q*t`. This is a
  strictly more general identity than `ErdosStrausFamily168m145` (recovered
  below at `p = 2, q = 21, t = m+1`), and — unlike the Mordell ladder's
  `r ∣ n` requirement — needs *no side condition whatsoever* beyond
  positivity of `p, q, t` and the one defining linear relation.

  **Coverage.** Instantiating `(p, q) = (5, 18)` gives the arithmetic
  progression `n = 360*t - 23` (`t ≥ 1`), and `(p, q) = (3, 20)` gives
  `n = 240*t - 23`. Both are proved unconditionally below (`HasRep` holds for
  *every* `t ≥ 1`, not merely for prime `n`). `360 ≡ 24 (mod 168)`, so the
  `360*t-23` family's residue cycles through `24*t-23 (mod 168)` directly.
  `240 ≡ 72 (mod 168)` (NOT `24` — corrected from an earlier draft), but
  `gcd(72, 168) = 24` and `72 ≡ 3*24 (mod 168)` with `3` invertible mod the
  cycle length `7 = 168/24`, so the `240*t-23` family's residue *also* cycles
  through all seven values of `24*t'-23 (mod 168)`, merely in a different
  order as `t` increases (checked directly: `t=1..7` gives residues
  `49, 121, 25, 97, 1, 73, 145`). Either way, as `t` ranges over `ℕ` each
  family's residue `n mod 168` sweeps through `{145, 1, 25, 49, 73, 97, 121}`
  — the six previously-open sub-residues `{1, 25, 73, 97, 121, 145}` of
  `n ≡ 1 (mod 24)` PLUS `49` (already covered separately by
  `ErdosStrausFortyNineMod168`). So both families here supply representations
  to a sub-progression (mod 360, resp. mod 240) inside each of the six open
  mod-168 classes — not a full closure of any residue class, but a concrete
  unconditional witness family landing in each of them (matching the informal
  claim in the originating conjecture card).
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue
import Propositio.NumberTheory.ErdosStraus.ErdosStrausFamily168m145

namespace ErdosStrausPQGeneralFamily

/-- **Core `(p, q, t)` covering identity.** For `p q t n : ℕ` with
`0 < p`, `0 < q`, `0 < t`, and `n + p + q = 4*p*q*t` (additive form, avoids
`ℕ` truncated subtraction), writing `a = p*q*t`, `b = q*t*n`, `c = p*t*n`,
`4/n = 1/a + 1/b + 1/c`. No coprimality or divisibility side-condition on
`p, q, n` is required. -/
theorem erdos_straus_pq_family (p q t n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ht : 0 < t) (hn : n + p + q = 4 * p * q * t) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  -- `n` is positive: `4*p*q*t ≥ 2*(p+q) > p+q` for `p,q,t ≥ 1`.
  have hpq1 : p ≤ p * q := Nat.le_mul_of_pos_right p hq
  have hpq2 : q ≤ p * q := Nat.le_mul_of_pos_left q hp
  have hpqt : p * q ≤ p * q * t := Nat.le_mul_of_pos_right (p * q) ht
  have hpqpos : 0 < p * q := Nat.mul_pos hp hq
  have h4pqt : 4 * p * q * t = 4 * (p * q * t) := by ring
  have hnpos : 0 < n := by omega
  have hapos : 0 < p * q * t := Nat.mul_pos (Nat.mul_pos hp hq) ht
  have hbpos : 0 < q * t * n := Nat.mul_pos (Nat.mul_pos hq ht) hnpos
  have hcpos : 0 < p * t * n := Nat.mul_pos (Nat.mul_pos hp ht) hnpos
  refine ⟨p * q * t, q * t * n, p * t * n, hapos, hbpos, hcpos, ?_⟩
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have htQ : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have hnQeq : (n : ℚ) + p + q = 4 * p * q * t := by exact_mod_cast hn
  push_cast
  field_simp
  linarith [hnQeq]

/-- `HasRep` form of the core `(p, q, t)` covering identity. -/
theorem hasRep_of_pq_family (p q t n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ht : 0 < t) (hn : n + p + q = 4 * p * q * t) :
    ErdosStrausResidue.HasRep n := by
  unfold ErdosStrausResidue.HasRep
  exact erdos_straus_pq_family p q t n hp hq ht hn

/-! ### Subsumption: `ErdosStrausFamily168m145` as the `p = 2, q = 21` instance -/

/-- `ErdosStrausFamily168m145.hasRep_of_family_168m145` recovered from the
general `(p, q, t)` family at `p = 2, q = 21, t = m + 1`. -/
theorem hasRep_of_family_168m145_via_pq (m : ℕ) :
    ErdosStrausResidue.HasRep (168 * m + 145) := by
  have hn : (168 * m + 145) + 2 + 21 = 4 * 2 * 21 * (m + 1) := by ring
  exact hasRep_of_pq_family 2 21 (m + 1) (168 * m + 145)
    (by norm_num) (by norm_num) (by omega) hn

/-- Cross-check: the corollary above proves the exact same `HasRep`
proposition as the original numeral file's theorem. -/
example (m : ℕ) : ErdosStrausResidue.HasRep (168 * m + 145) :=
  ErdosStrausFamily168m145.hasRep_of_family_168m145 m

/-! ### Two fresh instances hitting previously-untouched mod-168 sub-residues

`(p, q) = (5, 18)` gives `n = 360*t - 23`; `(p, q) = (3, 20)` gives
`n = 240*t - 23`. Both are proved for every `t ≥ 1`, unconditionally (not
merely at prime `n`). -/

/-- **`(p, q) = (5, 18)` instance**: for every `t ≥ 1`, `n = 360*t - 23` has
an Erdős–Straus representation. The smallest instance `t = 1` gives the prime
`n = 337 ≡ 1 (mod 168)`, a fresh sub-residue not hit by
`ErdosStrausFamily168m145` (which only ever lands on `145 mod 168`). -/
theorem hasRep_of_360t_23 (t : ℕ) (ht : 1 ≤ t) :
    ErdosStrausResidue.HasRep (360 * t - 23) := by
  have hn : (360 * t - 23) + 5 + 18 = 4 * 5 * 18 * t := by omega
  exact hasRep_of_pq_family 5 18 t (360 * t - 23)
    (by norm_num) (by norm_num) ht hn

/-- **`(p, q) = (3, 20)` instance**: for every `t ≥ 1`, `n = 240*t - 23` has
an Erdős–Straus representation. -/
theorem hasRep_of_240t_23 (t : ℕ) (ht : 1 ≤ t) :
    ErdosStrausResidue.HasRep (240 * t - 23) := by
  have hn : (240 * t - 23) + 3 + 20 = 4 * 3 * 20 * t := by omega
  exact hasRep_of_pq_family 3 20 t (240 * t - 23)
    (by norm_num) (by norm_num) ht hn

/-- Sanity: explicit numeric instances of the general identity, including the
prime instance `n = 337` (`p = 5, q = 18, t = 1`, the `t = 1` case of
`hasRep_of_360t_23`) and `n = 217` (`p = 3, q = 20, t = 1`). -/
example : (4 : ℚ) / 337 = 1 / 90 + 1 / 6066 + 1 / 1685 := by norm_num
example : (4 : ℚ) / 217 = 1 / 60 + 1 / 4340 + 1 / 651 := by norm_num
example : (4 : ℚ) / 19 = 1 / 6 + 1 / 57 + 1 / 38 := by norm_num

end ErdosStrausPQGeneralFamily
