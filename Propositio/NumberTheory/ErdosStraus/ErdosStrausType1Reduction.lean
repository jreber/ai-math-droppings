/-
  Erdős–Straus: the general Type-1 Mordell reduction lemma.

  The Erdős–Straus conjecture: for every `n ≥ 2` there are positive integers
  `a, b, c` with `4/n = 1/a + 1/b + 1/c` (`ErdosStrausResidue.HasRep n`).

  This file extracts, as a single standalone existential lemma, the
  "engineer's machine" that every one of the previously-landed family
  identities (`360t+23`, the `p,q`-general family, the `k`-parametrized
  Mordell-ladder rung, mod-13/24, mod-361/456, mod-5/mod-8, ...) instantiates
  by hand-picking `a` as a function of `n`: NONE of those files actually
  needs a bespoke algebraic derivation past this one reduction.

  **Statement**: for `n a : ℕ` with `n < 4*a`, writing `d = 4*a - n`, if
  `d ∣ n*a` then, setting `k = n*a/d`, `b = k+1`, `c = k*(k+1)`, the triple
  `(a, b, c)` witnesses `4/n = 1/a + 1/b + 1/c`.

  **Algebra**:
  * `1/(k+1) + 1/(k*(k+1)) = 1/k` (the standard telescoping unit-fraction
    split, valid whenever `k ≠ 0`).
  * `1/a + 1/k = 4/n`: from `d ∣ n*a`, write `n*a = d*k`; since
    `d = 4*a - n` (as naturals, using `n < 4*a`), this says `n*a = (4*a-n)*k`,
    i.e. `n*a + n*k = 4*a*k`, i.e. `n*(a+k) = 4*a*k`, which is exactly
    `1/a + 1/k = 4/n` cleared of denominators.
  * Chaining: `1/a + 1/b + 1/c = 1/a + (1/(k+1) + 1/(k*(k+1))) = 1/a + 1/k
    = 4/n`.

  **One hypothesis not spelled out in the literal card statement but needed
  for correctness**: `0 < n`. At `n = 0`, `d = 4*a`, `d ∣ n*a = 0` holds
  vacuously for every `a`, `k = 0*a/(4*a) = 0`, `c = k*(k+1) = 0`, and the
  claimed equation `4/0 = 1/a + 1/1 + 1/0` is `0 = 1/a + 1`, which is false.
  So `n = 0` is a genuine counterexample to the *literal* statement (found by
  direct case-check before writing the proof, not assumed); `0 < n` is added
  as an explicit hypothesis to make the lemma true, matching every actual use
  site (all family files instantiate at `n ≥ 2`). Given `0 < n` and
  `n < 4*a` (which forces `0 < a`), the divisibility hypothesis forces
  `0 < k` as well (`n*a > 0` but `k = 0` would force `n*a = d*0 = 0`), so `b,
  c > 0` and `HasRep n` follows.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausType1Reduction

/-- **Type-1 Mordell reduction lemma** (general infrastructure, existential
witness form): for `n a : ℕ` with `0 < n` and `n < 4*a`, if
`d := 4*a - n` divides `n*a`, then writing `k := n*a/d`, `b := k+1`,
`c := k*(k+1)`, the triple `(a, b, c)` satisfies `0 < b`, `0 < c`, and
`4/n = 1/a + 1/b + 1/c`. -/
theorem erdos_straus_type1_reduction {n a : ℕ} (hn : 0 < n) (hlt : n < 4 * a)
    (hdvd : (4 * a - n) ∣ (n * a)) :
    ∃ b c : ℕ, 0 < b ∧ 0 < c ∧
      b = n * a / (4 * a - n) + 1 ∧
      c = (n * a / (4 * a - n)) * (n * a / (4 * a - n) + 1) ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  set d := 4 * a - n with hd_def
  have ha : 0 < a := by omega
  have hd : 0 < d := by omega
  obtain ⟨k, hk⟩ := hdvd
  -- hk : n * a = d * k
  have hkdiv : n * a / d = k := by
    rw [hk]; exact Nat.mul_div_cancel_left k hd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, Nat.mul_zero] at hk
      exact absurd hk (Nat.mul_pos hn ha).ne'
    · exact h0
  refine ⟨k + 1, k * (k + 1), by omega, by positivity, by rw [hkdiv],
    by rw [hkdiv], ?_⟩
  -- Now the rational identity `4/n = 1/a + 1/(k+1) + 1/(k*(k+1))`.
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have hk1Q : (k : ℚ) + 1 ≠ 0 := by positivity
  have hdsum : d + n = 4 * a := by omega
  have hdsumQ : (d : ℚ) + n = 4 * a := by exact_mod_cast hdsum
  have hkQeq : (n : ℚ) * a = d * k := by exact_mod_cast hk
  -- Eliminate `d` using `hdsumQ`, then finish by clearing denominators.
  have hkey : (n : ℚ) * (a + k) = 4 * a * k := by
    have : (d : ℚ) = 4 * a - n := by linarith
    rw [this] at hkQeq
    linarith [hkQeq]
  push_cast
  field_simp
  linear_combination (-(((k : ℚ) + 1))) * hkey

/-- `HasRep` form of the Type-1 reduction lemma: the existence-only
statement matching `ErdosStrausResidue.HasRep` exactly. -/
theorem hasRep_of_type1_reduction {n a : ℕ} (hn : 0 < n) (hlt : n < 4 * a)
    (hdvd : (4 * a - n) ∣ (n * a)) : ErdosStrausResidue.HasRep n := by
  obtain ⟨b, c, hb, hc, _hbeq, _hceq, heq⟩ :=
    erdos_straus_type1_reduction hn hlt hdvd
  have ha : 0 < a := by omega
  exact ⟨a, b, c, ha, hb, hc, heq⟩

/-- Sanity: an explicit numeric instance. Take `n = 7`, `a = 2`: `d = 1`,
`1 ∣ 14`, `k = 14`, `b = 15`, `c = 14*15 = 210`, and indeed
`4/7 = 1/2 + 1/15 + 1/210`. -/
example : (4 : ℚ) / 7 = 1 / 2 + 1 / 15 + 1 / 210 := by norm_num

example : ErdosStrausResidue.HasRep 7 :=
  hasRep_of_type1_reduction (n := 7) (a := 2) (by norm_num) (by norm_num)
    (by norm_num)

/-- Sanity: `n = 5`, `a = 2`: `d = 3`, `3 ∣ 10`? No — check `n = 5, a = 4`:
`d = 11`, `11 ∣ 20`? No. Try `n = 13, a = 4`: `d = 3`, `3 ∣ 52`? No.
Use `n = 5, a = 3`: `d = 7`, `7 ∣ 15`? No. A clean second instance:
`n = 11, a = 3`: `d = 1`, `1 ∣ 33`, `k = 33`, `b = 34`, `c = 33*34 = 1122`:
`4/11 = 1/3 + 1/34 + 1/1122`. -/
example : (4 : ℚ) / 11 = 1 / 3 + 1 / 34 + 1 / 1122 := by norm_num

example : ErdosStrausResidue.HasRep 11 :=
  hasRep_of_type1_reduction (n := 11) (a := 3) (by norm_num) (by norm_num)
    (by norm_num)

end ErdosStrausType1Reduction
