/-
  Erdős–Straus: the general parametrized Mordell-ladder rung.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  `ErdosStrausFortyNineMod168.lean`, `ErdosStrausElevenMod264.lean`,
  `ErdosStrausThreeSixtyOneMod456.lean`, and `ErdosStrausFiveTwentyNineMod552.lean`
  each prove ONE numeral instance of the same "Mordell ladder" rung: writing
  `n = 24m+1`, `a = 6m+k` for a fixed numeral `k`, the leftover fraction
  `4/n - 1/a` has numerator `r = 4k-1`, and whenever `r ∣ n` it collapses to a
  single unit fraction, split trivially in half. The four files instantiate
  `k = 2, 3, 5, 6` (`r = 7, 11, 19, 23`); `k = 1` gives the `r = 3` mod-3
  obstruction (already covered by `n ≡ 0 (mod 3)` elsewhere), and `k = 4` gives
  `r = 15 = 3·5`, the SAME mod-3 obstruction (any `k ≡ 1 (mod 3)` forces
  `3 ∣ r`, hence `3 ∣ n`, which is redundant with — not wrong, just not new
  relative to — the `3 ∣ n` residue class).

  This file proves the SAME algebraic identity once, parametrized by `k`
  (and the "splitting parameter" `t`, playing the role of `m` reindexed as
  `n = r·(24t+r)`), so every future rung is a corollary by instantiation.

  **Key finding (not assumed, discovered by direct computation): the identity
  itself needs no side condition on `k` beyond `k ≥ 1` (so that `r = 4k-1 ≥ 3`
  is a genuine positive numerator).** It holds *identically* for every
  `k ≥ 1`, including `k ≡ 1 (mod 3)` (where `r` is divisible by 3, e.g.
  `k = 1, 4`); those instances are simply redundant with the `3 ∣ n` case,
  not algebraically broken. The `k mod 3 ≠ 1` restriction quoted in the
  originating conjecture card is about which instances give residue classes
  *disjoint from* `{n | 3 ∣ n}` (i.e. genuinely new coverage), not about
  correctness of the identity — confirmed by direct Python `Fraction`
  arithmetic (792 `(k,t)` pairs, `k = 1..99`, `t ∈ {0,1,2,3,5,10,37,100}`,
  including `k ≡ 1 (mod 3)` instances, zero failures) before this file was
  written.

  Algebraic core (`r` a free variable, `k` linked to it only via
  `r + 1 = 4k` — stated additively to avoid `ℕ` truncated-subtraction
  headaches): writing `a = r·(6t+k)`, `n' = 24t+r`, `n = r·n' = 24rt+r²`,

    4a = 4r(6t+k) = r(24t+4k) = r(24t + (r+1)) = r(n'+1)      [since 4k = r+1]

  hence `1/a + 1/(a n') = (n'+1)/(a n') = 4a/(r a n') = 4/(r n') = 4/n`, and
  the two `1/(2 a n')` halves recombine to `1/(a n')`. No factorization luck
  anywhere — this is the exact same computation carried out numerically in
  each of the four existing files, now done once with `k` (and `r`) as
  variables instead of numerals.

  `erdos_straus_mordell_general` below is the `k`-parametrized form matching
  the conjecture card exactly (hypothesis `1 ≤ k`, numerator written as the
  literal `4*k-1`); `hasRep_of_mordell_general` is its `HasRep` form.
  `hasRep_of_fortyNine_mod_168_via_general` etc. at the bottom recover two of
  the four existing numeral rungs as one-line corollaries, demonstrating the
  subsumption concretely (the existing rung files themselves are untouched).
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue
import Propositio.NumberTheory.ErdosStraus.ErdosStrausFortyNineMod168
import Propositio.NumberTheory.ErdosStraus.ErdosStrausThreeSixtyOneMod456

namespace ErdosStrausMordellGeneral

/-- **Core Mordell-ladder identity**, parametrized by `r`, `k`, `t` with
`r` linked to `k` only via `r + 1 = 4*k` (stated additively so no `ℕ`
truncated-subtraction reasoning is needed): writing `a = r*(6*t+k)`,
`n' = 24*t+r`, `n = 24*r*t + r^2` (so `n = r*n'` and `4*a = r*(n'+1)`),
`4/n = 1/a + 1/(2*a*n') + 1/(2*a*n')`. -/
theorem erdos_straus_mordell_ladder_rung (r k t : ℕ) (hr : r + 1 = 4 * k) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (24 * r * t + r ^ 2) = 1 / a + 1 / b + 1 / c := by
  have hrpos : 0 < r := by omega
  have hkpos : 0 < k := by omega
  have h6tk : 0 < 6 * t + k := by omega
  have hapos : 0 < r * (6 * t + k) := Nat.mul_pos hrpos h6tk
  have hn'pos : 0 < 24 * t + r := by omega
  have hbpos : 0 < 2 * (r * (6 * t + k)) * (24 * t + r) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hapos) hn'pos
  refine ⟨r * (6 * t + k), 2 * (r * (6 * t + k)) * (24 * t + r),
    2 * (r * (6 * t + k)) * (24 * t + r), hapos, hbpos, hbpos, ?_⟩
  have hrQ : (r : ℚ) + 1 = 4 * (k : ℚ) := by exact_mod_cast hr
  have hrne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hrpos.ne'
  have h6tkne : (6 * (t : ℚ) + (k : ℚ)) ≠ 0 := by
    have h1 : (0 : ℚ) ≤ 6 * (t : ℚ) := by positivity
    have h2 : (0 : ℚ) < (k : ℚ) := Nat.cast_pos.mpr hkpos
    have : (0 : ℚ) < 6 * (t : ℚ) + (k : ℚ) := by linarith
    exact this.ne'
  have hn'ne : (24 * (t : ℚ) + (r : ℚ)) ≠ 0 := by
    have h1 : (0 : ℚ) ≤ 24 * (t : ℚ) := by positivity
    have h2 : (0 : ℚ) < (r : ℚ) := Nat.cast_pos.mpr hrpos
    have : (0 : ℚ) < 24 * (t : ℚ) + (r : ℚ) := by linarith
    exact this.ne'
  push_cast
  field_simp
  linear_combination (-2 : ℚ) * hrQ

/-- `HasRep` form of the core identity. -/
theorem hasRep_of_mordell_ladder_rung (r k t : ℕ) (hr : r + 1 = 4 * k) :
    ErdosStrausResidue.HasRep (24 * r * t + r ^ 2) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_mordell_ladder_rung r k t hr

/-- **General Mordell-ladder rung, parametrized directly by `k` (matching the
originating conjecture card)**: for every `k ≥ 1` and every `t`, writing
`r = 4*k-1`, `a = r*(6*t+k)`, `n' = 24*t+r`,
`4/(24*r*t+r^2) = 1/a + 1/(2*a*n') + 1/(2*a*n')`.

Note: no `k mod 3 ≠ 1` hypothesis is needed — see the file docstring; this
is a strict generalization of the conjecture card's stated form. -/
theorem erdos_straus_mordell_general (k t : ℕ) (hk : 1 ≤ k) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (24 * (4 * k - 1) * t + (4 * k - 1) ^ 2)
        = 1 / a + 1 / b + 1 / c := by
  have hr : (4 * k - 1) + 1 = 4 * k := by omega
  have hcast : ((4 * k - 1 : ℕ) : ℚ) = 4 * (k : ℚ) - 1 := by
    have h1 : (1 : ℕ) ≤ 4 * k := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have h := erdos_straus_mordell_ladder_rung (4 * k - 1) k t hr
  rwa [hcast] at h

/-- `HasRep` form of the general `k`-parametrized rung. -/
theorem hasRep_of_mordell_general (k t : ℕ) (hk : 1 ≤ k) :
    ErdosStrausResidue.HasRep (24 * (4 * k - 1) * t + (4 * k - 1) ^ 2) := by
  unfold ErdosStrausResidue.HasRep
  have hcast : ((4 * k - 1 : ℕ) : ℚ) = 4 * (k : ℚ) - 1 := by
    have h1 : (1 : ℕ) ≤ 4 * k := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  push_cast
  rw [hcast]
  exact erdos_straus_mordell_general k t hk

/-! ### Subsumption: two of the four existing numeral rungs as corollaries

`ErdosStrausFortyNineMod168` is `k = 2` (`r = 7`, `n = 168*j+49`) and
`ErdosStrausThreeSixtyOneMod456` is `k = 5` (`r = 19`, `n = 456*s+361`) of
the general ladder above — recovered here with no new algebra, purely by
instantiating `erdos_straus_mordell_ladder_rung` at the fixed numerals
`r = 7, k = 2` and `r = 19, k = 5` and matching witnesses. The existing rung
files are not modified. -/

/-- `ErdosStrausFortyNineMod168.hasRep_of_fortyNine_mod_168` recovered from the
general rung at `k = 2` (`r = 7`). -/
theorem hasRep_of_fortyNine_mod_168_via_general (j : ℕ) :
    ErdosStrausResidue.HasRep (168 * j + 49) := by
  have h := hasRep_of_mordell_ladder_rung 7 2 j (by norm_num)
  have hn : 24 * 7 * j + 7 ^ 2 = 168 * j + 49 := by ring
  rwa [hn] at h

/-- `ErdosStrausThreeSixtyOneMod456.hasRep_of_threeSixtyOne_mod_456` recovered
from the general rung at `k = 5` (`r = 19`). -/
theorem hasRep_of_threeSixtyOne_mod_456_via_general (s : ℕ) :
    ErdosStrausResidue.HasRep (456 * s + 361) := by
  have h := hasRep_of_mordell_ladder_rung 19 5 s (by norm_num)
  have hn : 24 * 19 * s + 19 ^ 2 = 456 * s + 361 := by ring
  rwa [hn] at h

/-- Cross-check: the corollary above proves the exact same `HasRep`
proposition as the original numeral file's theorem (both statements
type-check against each other's target, confirming the subsumption is not
vacuous). -/
example (j : ℕ) : ErdosStrausResidue.HasRep (168 * j + 49) :=
  ErdosStrausFortyNineMod168.hasRep_of_fortyNine_mod_168 j
example (s : ℕ) : ErdosStrausResidue.HasRep (456 * s + 361) :=
  ErdosStrausThreeSixtyOneMod456.hasRep_of_threeSixtyOne_mod_456 s

/-- Sanity: explicit numeric instances of the general identity at the new
witnesses `k = 8` (`r = 31`) and `k = 9` (`r = 35`), `t = 0`. -/
example : (4 : ℚ) / 961 = 1 / 248 + 1 / 15376 + 1 / 15376 := by norm_num
example : (4 : ℚ) / 1225 = 1 / 315 + 1 / 22050 + 1 / 22050 := by norm_num

end ErdosStrausMordellGeneral
