import Propositio.Collatz.Basic
import Propositio.Collatz.ResidueDescent
import Mathlib.Tactic

/-!
# Guaranteed bounded descent for residue classes mod 128 (Terras structure)

This file extends the residue descent census one level deeper than `CollatzResidueDescent`:
from mod 64 to mod 128. The density of residue classes with guaranteed bounded descent rises
to **115/128** (up from 28/32 = 112/128).

## Background

At mod 32, the 4 "bad" residue classes `{7, 15, 27, 31}` (mod 32) resist short descent.
Each lifts to 4 sub-classes at mod 128. Three of these 16 sub-classes turn out to have
guaranteed descent in **7 Terras steps**:

* `n ≡ 7 (mod 128)`:  T⁷(128j+7)  = 81j+5  < 128j+7  (parity `(1,1,1,0,1,0,0)`)
* `n ≡ 15 (mod 128)`: T⁷(128j+15) = 81j+10 < 128j+15 (parity `(1,1,1,1,0,0,0)`)
* `n ≡ 59 (mod 128)`: T⁷(128j+59) = 81j+38 < 128j+59 (parity `(1,1,0,1,1,0,0)`)

The remaining 13 sub-classes of the 4 bad mod-32 classes do NOT have 7-step guaranteed
descent (the iteration coefficient exceeds 128, so T^k grows for those classes). These
require deeper mod-256 analysis.

## Density count at mod 128

| Source                         | Count |
|--------------------------------|-------|
| Even classes (trivial)         |  64   |
| ≡ 1 mod 4                     |  32   |
| ≡ 3 mod 16 (4-step descent)    |   8   |
| ≡ 11 mod 32 (5-step descent)   |   4   |
| ≡ 23 mod 32 (5-step descent)   |   4   |
| **7 mod 128** (NEW, 7 steps)   |   1   |
| **15 mod 128** (NEW, 7 steps)  |   1   |
| **59 mod 128** (NEW, 7 steps)  |   1   |
| **Total**                      | **115** |

So 115/128 ≈ 89.8% of residue classes at mod 128 have guaranteed bounded descent.

## Key parity vectors

The three new 7-step descents have parity vectors (odd/even) of the first 7 T-steps:
* 7 mod 128:  (O, O, O, E, O, E, E) → coefficient 81/128 < 1 ✓
* 15 mod 128: (O, O, O, O, E, E, E) → coefficient 81/128 < 1 ✓
* 59 mod 128: (O, O, E, O, O, E, E) → coefficient 81/128 < 1 ✓

All three share the same final coefficient 81 (= 3⁴), since they each have exactly
4 odd steps in 7 total (and T odd step multiplies by 3/2, T even step by 1/2,
giving (3/2)⁴ · (1/2)³ = 81/128 < 1).

## Proof method

Each lemma: `obtain ⟨j, rfl⟩` to write n = 128*j + r, then chain 7 explicit
`have hk : T (...)  = ...` steps using `unfold T; split <;> omega`, then close with `omega`.
-/

namespace CollatzResidueDescent128

open TerrasDensity

/-- **`n ≡ 7 (mod 128)` descends in 7 Terras steps.** `T⁷(128j+7) = 81j+5 < 128j+7`.

Parity vector of the 7 steps: `(O,O,O,E,O,E,E)` — 4 odd steps, 3 even steps.
The coefficient 3⁴/2⁷ = 81/128 < 1 ensures descent across the whole class.

Sub-class of the bad mod-32 class `7 mod 32`; this is the "k even" half. The
complementary sub-class `71 mod 128` (the "k odd" half) does NOT descend in 7 steps
(coefficient 243 > 128). -/
theorem descent_seven_mod_128 {n : ℕ} (hn : n % 128 = 7) : T_iter n 7 < n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 128 * j + 7 := ⟨n / 128, by omega⟩
  have h1 : T (128 * j + 7)   = 192 * j + 11  := by unfold T; split <;> omega
  have h2 : T (192 * j + 11)  = 288 * j + 17  := by unfold T; split <;> omega
  have h3 : T (288 * j + 17)  = 432 * j + 26  := by unfold T; split <;> omega
  have h4 : T (432 * j + 26)  = 216 * j + 13  := by unfold T; split <;> omega
  have h5 : T (216 * j + 13)  = 324 * j + 20  := by unfold T; split <;> omega
  have h6 : T (324 * j + 20)  = 162 * j + 10  := by unfold T; split <;> omega
  have h7 : T (162 * j + 10)  = 81  * j + 5   := by unfold T; split <;> omega
  have e  : T_iter (128 * j + 7) 7 =
      T (T (T (T (T (T (T (128 * j + 7))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7]; omega

/-- **`n ≡ 15 (mod 128)` descends in 7 Terras steps.** `T⁷(128j+15) = 81j+10 < 128j+15`.

Parity vector: `(O,O,O,O,E,E,E)` — 4 odd steps, 3 even steps.
Coefficient 81/128 < 1 ensures descent.

Sub-class of the bad mod-32 class `15 mod 32`; this is the "k even" half. The
complementary sub-class `79 mod 128` does NOT descend in 7 steps. -/
theorem descent_fifteen_mod_128 {n : ℕ} (hn : n % 128 = 15) : T_iter n 7 < n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 128 * j + 15 := ⟨n / 128, by omega⟩
  have h1 : T (128 * j + 15)  = 192 * j + 23  := by unfold T; split <;> omega
  have h2 : T (192 * j + 23)  = 288 * j + 35  := by unfold T; split <;> omega
  have h3 : T (288 * j + 35)  = 432 * j + 53  := by unfold T; split <;> omega
  have h4 : T (432 * j + 53)  = 648 * j + 80  := by unfold T; split <;> omega
  have h5 : T (648 * j + 80)  = 324 * j + 40  := by unfold T; split <;> omega
  have h6 : T (324 * j + 40)  = 162 * j + 20  := by unfold T; split <;> omega
  have h7 : T (162 * j + 20)  = 81  * j + 10  := by unfold T; split <;> omega
  have e  : T_iter (128 * j + 15) 7 =
      T (T (T (T (T (T (T (128 * j + 15))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7]; omega

/-- **`n ≡ 59 (mod 128)` descends in 7 Terras steps.** `T⁷(128j+59) = 81j+38 < 128j+59`.

Parity vector: `(O,O,E,O,O,E,E)` — 4 odd steps, 3 even steps.
Coefficient 81/128 < 1 ensures descent.

Sub-class of the bad mod-32 class `27 mod 32` (since 59 ≡ 27 mod 32); this is the
"k even" half. The complementary sub-class `123 mod 128` does NOT descend in 7 steps. -/
theorem descent_fiftynine_mod_128 {n : ℕ} (hn : n % 128 = 59) : T_iter n 7 < n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 128 * j + 59 := ⟨n / 128, by omega⟩
  have h1 : T (128 * j + 59)  = 192 * j + 89  := by unfold T; split <;> omega
  have h2 : T (192 * j + 89)  = 288 * j + 134 := by unfold T; split <;> omega
  have h3 : T (288 * j + 134) = 144 * j + 67  := by unfold T; split <;> omega
  have h4 : T (144 * j + 67)  = 216 * j + 101 := by unfold T; split <;> omega
  have h5 : T (216 * j + 101) = 324 * j + 152 := by unfold T; split <;> omega
  have h6 : T (324 * j + 152) = 162 * j + 76  := by unfold T; split <;> omega
  have h7 : T (162 * j + 76)  = 81  * j + 38  := by unfold T; split <;> omega
  have e  : T_iter (128 * j + 59) 7 =
      T (T (T (T (T (T (T (128 * j + 59))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7]; omega

/-- **Extended coverage capstone (mod 128).** All 9 proved residue classes — the 6 from
`CollatzResidueDescent` plus the 3 new mod-128 classes — have guaranteed bounded descent
within 7 Terras steps.

Together these cover **115/128 ≈ 89.8%** of residue classes, up from 28/32 = 87.5%.
The three new mod-128 classes each require exactly 7 steps (the same coefficient 81/128). -/
theorem descent_within_seven {n : ℕ}
    (h : n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 19 ∨ n % 32 = 23 ∨
         n % 64 = 35 ∨ n % 64 = 43 ∨ n % 64 = 51 ∨
         n % 128 = 7 ∨ n % 128 = 15 ∨ n % 128 = 59) :
    ∃ k, 1 ≤ k ∧ k ≤ 7 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_three_mod_sixteen h⟩
  · exact ⟨5, by norm_num, by norm_num, CollatzResidueDescent.descent_eleven_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_nineteen_mod_thirtytwo h⟩
  · exact ⟨5, by norm_num, by norm_num, CollatzResidueDescent.descent_twentythree_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_thirtyfive_mod_sixtyfour h⟩
  · exact ⟨5, by norm_num, by norm_num, CollatzResidueDescent.descent_fortythree_mod_sixtyfour h⟩
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_fiftyone_mod_sixtyfour h⟩
  · exact ⟨7, by norm_num, by norm_num, descent_seven_mod_128 h⟩
  · exact ⟨7, by norm_num, by norm_num, descent_fifteen_mod_128 h⟩
  · exact ⟨7, by norm_num, by norm_num, descent_fiftynine_mod_128 h⟩

end CollatzResidueDescent128
