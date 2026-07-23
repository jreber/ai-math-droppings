import Propositio.Collatz.Basic
import Propositio.Collatz.ResidueDescent
import Propositio.Collatz.ResidueDescent128
import Mathlib.Tactic

/-!
# Guaranteed bounded descent for residue classes mod 256 (Terras structure)

This file extends the residue descent census from mod 128 to mod 256, adding
**seven new 8-step guaranteed-descent lemmas**.

## Background

At mod 128, the 13 "bad" residue classes `{27,31,39,47,63,71,79,91,95,103,111,123,127}`
(odd ≡ 3 mod 4, not covered by previous lemmas) resist bounded descent in ≤ 7 steps.
Each lifts to 2 sub-classes at mod 256. Seven of these 26 sub-classes turn out to have
guaranteed descent in **8 Terras steps** (all with coefficient 243/256 < 1):

* `n ≡ 39  (mod 256)`: T⁸(256k+39)  = 243k+38  < 256k+39
* `n ≡ 79  (mod 256)`: T⁸(256k+79)  = 243k+76  < 256k+79
* `n ≡ 95  (mod 256)`: T⁸(256k+95)  = 243k+91  < 256k+95
* `n ≡ 123 (mod 256)`: T⁸(256k+123) = 243k+118 < 256k+123
* `n ≡ 175 (mod 256)`: T⁸(256k+175) = 243k+167 < 256k+175
* `n ≡ 199 (mod 256)`: T⁸(256k+199) = 243k+190 < 256k+199
* `n ≡ 219 (mod 256)`: T⁸(256k+219) = 243k+209 < 256k+219

## Parity structure

All seven new classes reach the same coefficient 243 = 3⁵ after 8 steps, meaning
exactly **5 odd steps and 3 even steps**: (3/2)⁵ · (1/2)³ = 243/256 < 1.

Sub-class origins:
* 39  mod 256 ← 39  mod 128 (j even)
* 79  mod 256 ← 79  mod 128 (j even)
* 95  mod 256 ← 95  mod 128 (j even)
* 123 mod 256 ← 123 mod 128 (j even)
* 175 mod 256 ← 47  mod 128 (j odd, 47+128=175)
* 199 mod 256 ← 71  mod 128 (j odd, 71+128=199)
* 219 mod 256 ← 91  mod 128 (j odd, 91+128=219)

## Density count at mod 256

| Source                              | Count |
|-------------------------------------|-------|
| Even classes (trivial, 1 step)      |  128  |
| ≡ 1 mod 4 (2-step descent)          |   64  |
| ≡ 3 mod 16 (4-step descent)         |   16  |
| ≡ 11 mod 32 (5-step descent)        |    8  |
| ≡ 23 mod 32 (5-step descent)        |    8  |
| 7, 15, 59, 135, 143, 187 mod 256*  |    6  |
| **7 new mod-256 classes**           |    7  |
| **Total**                           | **237** |

(*) The mod-128 good classes {7,15,59} each give 2 sub-classes at mod 256 (r and r+128),
all inheriting their 7-step descent bound.

So 237/256 ≈ 92.6% of residue classes at mod 256 have guaranteed bounded descent,
up from 115/128 ≈ 89.8%.

## Proof method

Each of the 8-step lemmas chains 8 explicit `have hk : T (...) = ...` steps using
`unfold T; split <;> omega`, then closes with `omega`.
-/

namespace CollatzResidueDescent256

open TerrasDensity

/-- **`n ≡ 39 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+39) = 243k+38 < 256k+39`.
Parity: `(O,O,O,E,O,O,E,E)` — 5 odd, 3 even. Coefficient 3⁵/2⁸ = 243/256 < 1.
Sub-class of `39 mod 128` (the "k even" half). -/
theorem descent_thirtynine_mod_256 {n : ℕ} (hn : n % 256 = 39) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 39 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 39)   = 384 * k + 59   := by unfold T; split <;> omega
  have h2 : T (384 * k + 59)   = 576 * k + 89   := by unfold T; split <;> omega
  have h3 : T (576 * k + 89)   = 864 * k + 134  := by unfold T; split <;> omega
  have h4 : T (864 * k + 134)  = 432 * k + 67   := by unfold T; split <;> omega
  have h5 : T (432 * k + 67)   = 648 * k + 101  := by unfold T; split <;> omega
  have h6 : T (648 * k + 101)  = 972 * k + 152  := by unfold T; split <;> omega
  have h7 : T (972 * k + 152)  = 486 * k + 76   := by unfold T; split <;> omega
  have h8 : T (486 * k + 76)   = 243 * k + 38   := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 39) 8 =
      T (T (T (T (T (T (T (T (256 * k + 39)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **`n ≡ 79 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+79) = 243k+76 < 256k+79`.
Parity: `(O,O,O,O,E,E,O,E)` — 5 odd, 3 even. Coefficient 243/256 < 1.
Sub-class of `79 mod 128` (the "k even" half). -/
theorem descent_seventynine_mod_256 {n : ℕ} (hn : n % 256 = 79) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 79 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 79)   = 384 * k + 119  := by unfold T; split <;> omega
  have h2 : T (384 * k + 119)  = 576 * k + 179  := by unfold T; split <;> omega
  have h3 : T (576 * k + 179)  = 864 * k + 269  := by unfold T; split <;> omega
  have h4 : T (864 * k + 269)  = 1296 * k + 404 := by unfold T; split <;> omega
  have h5 : T (1296 * k + 404) = 648 * k + 202  := by unfold T; split <;> omega
  have h6 : T (648 * k + 202)  = 324 * k + 101  := by unfold T; split <;> omega
  have h7 : T (324 * k + 101)  = 486 * k + 152  := by unfold T; split <;> omega
  have h8 : T (486 * k + 152)  = 243 * k + 76   := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 79) 8 =
      T (T (T (T (T (T (T (T (256 * k + 79)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **`n ≡ 95 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+95) = 243k+91 < 256k+95`.
Parity: `(O,O,O,O,O,E,E,E)` — 5 odd, 3 even. Coefficient 243/256 < 1.
Sub-class of `95 mod 128` (the "k even" half). -/
theorem descent_ninetyfive_mod_256 {n : ℕ} (hn : n % 256 = 95) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 95 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 95)    = 384 * k + 143  := by unfold T; split <;> omega
  have h2 : T (384 * k + 143)   = 576 * k + 215  := by unfold T; split <;> omega
  have h3 : T (576 * k + 215)   = 864 * k + 323  := by unfold T; split <;> omega
  have h4 : T (864 * k + 323)   = 1296 * k + 485 := by unfold T; split <;> omega
  have h5 : T (1296 * k + 485)  = 1944 * k + 728 := by unfold T; split <;> omega
  have h6 : T (1944 * k + 728)  = 972 * k + 364  := by unfold T; split <;> omega
  have h7 : T (972 * k + 364)   = 486 * k + 182  := by unfold T; split <;> omega
  have h8 : T (486 * k + 182)   = 243 * k + 91   := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 95) 8 =
      T (T (T (T (T (T (T (T (256 * k + 95)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **`n ≡ 123 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+123) = 243k+118 < 256k+123`.
Parity: `(O,O,E,O,O,E,O,E)` — 5 odd, 3 even. Coefficient 243/256 < 1.
Sub-class of `123 mod 128` (the "k even" half). -/
theorem descent_onetwentythree_mod_256 {n : ℕ} (hn : n % 256 = 123) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 123 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 123)  = 384 * k + 185  := by unfold T; split <;> omega
  have h2 : T (384 * k + 185)  = 576 * k + 278  := by unfold T; split <;> omega
  have h3 : T (576 * k + 278)  = 288 * k + 139  := by unfold T; split <;> omega
  have h4 : T (288 * k + 139)  = 432 * k + 209  := by unfold T; split <;> omega
  have h5 : T (432 * k + 209)  = 648 * k + 314  := by unfold T; split <;> omega
  have h6 : T (648 * k + 314)  = 324 * k + 157  := by unfold T; split <;> omega
  have h7 : T (324 * k + 157)  = 486 * k + 236  := by unfold T; split <;> omega
  have h8 : T (486 * k + 236)  = 243 * k + 118  := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 123) 8 =
      T (T (T (T (T (T (T (T (256 * k + 123)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **`n ≡ 175 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+175) = 243k+167 < 256k+175`.
Parity: `(O,O,O,O,E,O,E,E)` — 5 odd, 3 even. Coefficient 243/256 < 1.
Sub-class of `47 mod 128` (the "k odd" half: 47+128=175). -/
theorem descent_onehundredseventyfive_mod_256 {n : ℕ} (hn : n % 256 = 175) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 175 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 175)  = 384 * k + 263  := by unfold T; split <;> omega
  have h2 : T (384 * k + 263)  = 576 * k + 395  := by unfold T; split <;> omega
  have h3 : T (576 * k + 395)  = 864 * k + 593  := by unfold T; split <;> omega
  have h4 : T (864 * k + 593)  = 1296 * k + 890 := by unfold T; split <;> omega
  have h5 : T (1296 * k + 890) = 648 * k + 445  := by unfold T; split <;> omega
  have h6 : T (648 * k + 445)  = 972 * k + 668  := by unfold T; split <;> omega
  have h7 : T (972 * k + 668)  = 486 * k + 334  := by unfold T; split <;> omega
  have h8 : T (486 * k + 334)  = 243 * k + 167  := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 175) 8 =
      T (T (T (T (T (T (T (T (256 * k + 175)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **`n ≡ 199 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+199) = 243k+190 < 256k+199`.
Parity: `(O,O,O,E,O,E,O,E)` — 5 odd, 3 even. Coefficient 243/256 < 1.
Sub-class of `71 mod 128` (the "k odd" half: 71+128=199). -/
theorem descent_oneninety_nine_mod_256 {n : ℕ} (hn : n % 256 = 199) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 199 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 199)  = 384 * k + 299  := by unfold T; split <;> omega
  have h2 : T (384 * k + 299)  = 576 * k + 449  := by unfold T; split <;> omega
  have h3 : T (576 * k + 449)  = 864 * k + 674  := by unfold T; split <;> omega
  have h4 : T (864 * k + 674)  = 432 * k + 337  := by unfold T; split <;> omega
  have h5 : T (432 * k + 337)  = 648 * k + 506  := by unfold T; split <;> omega
  have h6 : T (648 * k + 506)  = 324 * k + 253  := by unfold T; split <;> omega
  have h7 : T (324 * k + 253)  = 486 * k + 380  := by unfold T; split <;> omega
  have h8 : T (486 * k + 380)  = 243 * k + 190  := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 199) 8 =
      T (T (T (T (T (T (T (T (256 * k + 199)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **`n ≡ 219 (mod 256)` descends in 8 Terras steps.**
`T⁸(256k+219) = 243k+209 < 256k+219`.
Parity: `(O,O,E,O,O,O,E,E)` — 5 odd, 3 even. Coefficient 243/256 < 1.
Sub-class of `91 mod 128` (the "k odd" half: 91+128=219). -/
theorem descent_twohundredsixteen_mod_256 {n : ℕ} (hn : n % 256 = 219) : T_iter n 8 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 256 * k + 219 := ⟨n / 256, by omega⟩
  have h1 : T (256 * k + 219)  = 384 * k + 329  := by unfold T; split <;> omega
  have h2 : T (384 * k + 329)  = 576 * k + 494  := by unfold T; split <;> omega
  have h3 : T (576 * k + 494)  = 288 * k + 247  := by unfold T; split <;> omega
  have h4 : T (288 * k + 247)  = 432 * k + 371  := by unfold T; split <;> omega
  have h5 : T (432 * k + 371)  = 648 * k + 557  := by unfold T; split <;> omega
  have h6 : T (648 * k + 557)  = 972 * k + 836  := by unfold T; split <;> omega
  have h7 : T (972 * k + 836)  = 486 * k + 418  := by unfold T; split <;> omega
  have h8 : T (486 * k + 418)  = 243 * k + 209  := by unfold T; split <;> omega
  have e  : T_iter (256 * k + 219) 8 =
      T (T (T (T (T (T (T (T (256 * k + 219)))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8]; omega

/-- **Extended coverage capstone (mod 256).** All 17 proved residue classes have
guaranteed bounded descent within 8 Terras steps: the 10 from `CollatzResidueDescent128`
(which in turn cover the classes from `CollatzResidueDescent`) plus the 7 new mod-256
classes.

Together these cover **237/256 ≈ 92.6%** of residue classes, up from 115/128 ≈ 89.8%.
All seven new classes require exactly 8 steps with the same coefficient 243/256. -/
theorem descent_within_eight {n : ℕ}
    (h : n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 19 ∨ n % 32 = 23 ∨
         n % 64 = 35 ∨ n % 64 = 43 ∨ n % 64 = 51 ∨
         n % 128 = 7 ∨ n % 128 = 15 ∨ n % 128 = 59 ∨
         n % 256 = 39 ∨ n % 256 = 79 ∨ n % 256 = 95 ∨ n % 256 = 123 ∨
         n % 256 = 175 ∨ n % 256 = 199 ∨ n % 256 = 219) :
    ∃ k, 1 ≤ k ∧ k ≤ 8 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_three_mod_sixteen h⟩
  · exact ⟨5, by norm_num, by norm_num, CollatzResidueDescent.descent_eleven_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_nineteen_mod_thirtytwo h⟩
  · exact ⟨5, by norm_num, by norm_num, CollatzResidueDescent.descent_twentythree_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_thirtyfive_mod_sixtyfour h⟩
  · exact ⟨5, by norm_num, by norm_num, CollatzResidueDescent.descent_fortythree_mod_sixtyfour h⟩
  · exact ⟨4, by norm_num, by norm_num, CollatzResidueDescent.descent_fiftyone_mod_sixtyfour h⟩
  · exact ⟨7, by norm_num, by norm_num, CollatzResidueDescent128.descent_seven_mod_128 h⟩
  · exact ⟨7, by norm_num, by norm_num, CollatzResidueDescent128.descent_fifteen_mod_128 h⟩
  · exact ⟨7, by norm_num, by norm_num, CollatzResidueDescent128.descent_fiftynine_mod_128 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_thirtynine_mod_256 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_seventynine_mod_256 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_ninetyfive_mod_256 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_onetwentythree_mod_256 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_onehundredseventyfive_mod_256 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_oneninety_nine_mod_256 h⟩
  · exact ⟨8, by norm_num, by norm_num, descent_twohundredsixteen_mod_256 h⟩

end CollatzResidueDescent256
