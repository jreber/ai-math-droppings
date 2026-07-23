/-
# Erdős–Straus conjecture: the elementary, unconditional residue classes

The Erdős–Straus conjecture states that for every `n ≥ 2` the equation
`4/n = 1/a + 1/b + 1/c` has a solution in positive integers `a, b, c`.
The full conjecture is OPEN.

This file proves the standard *explicit* (unconditional) cases, each by exhibiting
a closed-form triple `(a, b, c)` and discharging the exact rational identity:

* `n` even  (`2 ∣ n`, `n = 2m`):     `a = m,   b = 2m,        c = 2m`
* `n ≡ 3 (mod 4)` (`n = 4k+3`):       `a = k+2, b = (k+1)(k+2), c = (k+1)(4k+3)`
* `n ≡ 2 (mod 3)` (`n = 3k+2`):       `a = k+1, b = 3k+2,      c = (k+1)(3k+2)`

Each identity is genuinely true (verified algebraically and numerically before encoding).
A combined corollary covers the union of these classes; the residues left uncovered
(mod 12) are `{1, 9}`, i.e. exactly the hard part of the conjecture remains open.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

namespace ErdosStrausEasyClasses

/-- **Even case.** For `n = 2m`, `4/n = 1/m + 1/n + 1/n`
    (since `1/m = 2/n`). Triple: `a = m, b = n, c = n`. -/
theorem erdosStraus_even (n : ℕ) (hn : 2 ≤ n) (hclass : 2 ∣ n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨m, hm⟩ := hclass
  subst hm
  have hmpos : 0 < m := by omega
  refine ⟨m, 2 * m, 2 * m, hmpos, by omega, by omega, ?_⟩
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  push_cast
  field_simp
  ring

/-- **`n ≡ 3 (mod 4)` case.** For `n = 4k+3`,
    `4/n = 1/(k+2) + 1/((k+1)(k+2)) + 1/((k+1)(4k+3))`.
    (The first two terms collapse to `1/(k+1)`, then `1/(k+1) + 1/((k+1)n) = 4/n`.) -/
theorem erdosStraus_three_mod_four (n : ℕ) (hn : 2 ≤ n) (hclass : n % 4 = 3) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  subst hk
  refine ⟨k + 2, (k + 1) * (k + 2), (k + 1) * (4 * k + 3), by omega, by positivity,
    by positivity, ?_⟩
  have e1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have e2 : ((k : ℚ) + 2) ≠ 0 := by positivity
  have e3 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **`n ≡ 2 (mod 3)` case.** For `n = 3k+2`,
    `4/n = 1/(k+1) + 1/n + 1/((k+1)n)`.
    (Here `1/(k+1) + 1/((k+1)n) = 3/n`, plus `1/n` gives `4/n`.) -/
theorem erdosStraus_two_mod_three (n : ℕ) (hn : 2 ≤ n) (hclass : n % 3 = 2) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  subst hk
  refine ⟨k + 1, 3 * k + 2, (k + 1) * (3 * k + 2), by omega, by omega, by positivity, ?_⟩
  have e1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have e2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Combined corollary.** The explicit Erdős–Straus representation exists for every
    `n ≥ 2` that is even, or `≡ 3 (mod 4)`, or `≡ 2 (mod 3)`. The residues left uncovered
    (mod 12) are `{1, 9}`, where the conjecture remains open. -/
theorem erdosStraus_easy_classes (n : ℕ) (hn : 2 ≤ n)
    (hclass : 2 ∣ n ∨ n % 4 = 3 ∨ n % 3 = 2) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  rcases hclass with h | h | h
  · exact erdosStraus_even n hn h
  · exact erdosStraus_three_mod_four n hn h
  · exact erdosStraus_two_mod_three n hn h

end ErdosStrausEasyClasses
