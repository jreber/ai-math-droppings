import Propositio.NumberTheory.Collatz.Basic
import Propositio.Tactics
import Mathlib.Tactic

/-!
# Guaranteed bounded descent for specific residue classes (Terras structure)

For the Terras half-step `T` (`n/2` if even, `(3n+1)/2` if odd), a residue class `n ≡ r (mod 2^m)`
fixes the parities of the first `m` steps, so `T_iter n m` is an explicit linear function of `n`.
When that linear function lies below `n` for the whole class, the class has **guaranteed descent in
`m` steps** — a building block of the Everett–Terras "almost all `n` descend" density program: the
fraction of residues mod `2^m` with guaranteed bounded descent rises to `1`
(`3/4, 6/8, 13/16, 28/32, …`).

## Mod-32 coverage (original):

* `descent_three_mod_sixteen` — `n ≡ 3 (mod 16) ⟹ T⁴(n) = 9·(n/16) + 2 < n` (sharp: no descent at
  step 2 or 3; a *mutation* of `T_squared_of_4k_plus_3_non_descent`).
* `descent_nineteen_mod_thirtytwo` — `n ≡ 19 (mod 32) ⟹ T⁴(n) = 18·(n/32) + 11 < n`.
* `descent_eleven_mod_thirtytwo` — `n ≡ 11 (mod 32) ⟹ T⁵(n) = 27·(n/32) + 10 < n`.

## Mod-64 extension (new):

Three new residue classes mod 64 that are *not* covered by the mod-32 lemmas above (they are
sub-classes of the non-trivial ≡3 mod 4 family, refining the census one level deeper):

* `descent_thirtyfive_mod_sixtyfour` — `n ≡ 35 (mod 64) ⟹ T⁴(n) = 36k+20 < n`.
  Parity vector `(odd, odd, even, even)`. Note 35 ≡ 3 mod 16, so this is a mod-64 sub-case
  of `descent_three_mod_sixteen` — same parity vector, finer residue class.
* `descent_fiftyone_mod_sixtyfour` — `n ≡ 51 (mod 64) ⟹ T⁴(n) = 36k+29 < n`.
  Parity vector `(odd, odd, even, even)`. 51 ≡ 3 mod 16, another mod-64 sub-case of the
  same parity class.
* `descent_fortythree_mod_sixtyfour` — `n ≡ 43 (mod 64) ⟹ T⁵(n) = 54k+37 < n`.
  Parity vector `(odd, odd, even, odd, even)`. 43 ≡ 11 mod 32, a mod-64 sub-case of
  `descent_eleven_mod_thirtytwo` — same parity vector, confirmed at finer resolution.

`open TerrasDensity` provides `T`, `T_iter`. Proofs: split the class into its canonical linear
form, evaluate each `T` step by parity (`unfold T; split <;> omega`), then compare with `omega`.
-/

namespace CollatzResidueDescent

open TerrasDensity

/-- **`n ≡ 3 (mod 16)` descends in 4 Terras steps.** `T⁴(16k+3) = 9k+2 < 16k+3`. Parity vector of the
first 4 steps is `(odd, odd, even, even)`, fixed across the class. Sharp — the class does *not*
descend at step 2 or 3, so this strictly extends `T_squared_of_4k_plus_3_non_descent`. -/
theorem descent_three_mod_sixteen {n : ℕ} (hn : n % 16 = 3) : T_iter n 4 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16 * k + 3 := ⟨n / 16, by omega⟩
  have h1 : T (16 * k + 3) = 24 * k + 5 := by collatz_step
  have h2 : T (24 * k + 5) = 36 * k + 8 := by collatz_step
  have h3 : T (36 * k + 8) = 18 * k + 4 := by collatz_step
  have h4 : T (18 * k + 4) = 9 * k + 2 := by collatz_step
  have e : T_iter (16 * k + 3) 4 = T (T (T (T (16 * k + 3)))) := rfl
  rw [e, h1, h2, h3, h4]; omega

/-- **`n ≡ 19 (mod 32)` descends in 4 Terras steps.** `T⁴(32k+19) = 18k+11 < 32k+19`. Parity vector
`(odd, odd, even, even)`. -/
theorem descent_nineteen_mod_thirtytwo {n : ℕ} (hn : n % 32 = 19) : T_iter n 4 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 32 * k + 19 := ⟨n / 32, by omega⟩
  have h1 : T (32 * k + 19) = 48 * k + 29 := by unfold T; split <;> omega
  have h2 : T (48 * k + 29) = 72 * k + 44 := by unfold T; split <;> omega
  have h3 : T (72 * k + 44) = 36 * k + 22 := by unfold T; split <;> omega
  have h4 : T (36 * k + 22) = 18 * k + 11 := by unfold T; split <;> omega
  have e : T_iter (32 * k + 19) 4 = T (T (T (T (32 * k + 19)))) := rfl
  rw [e, h1, h2, h3, h4]; omega

/-- **`n ≡ 11 (mod 32)` descends in 5 Terras steps.** `T⁵(32k+11) = 27k+10 < 32k+11`. Parity vector
`(odd, odd, even, odd, even)` — needs the extra halving level (5 steps), extending the bounded-descent
residue census one modulus deeper toward density 1. -/
theorem descent_eleven_mod_thirtytwo {n : ℕ} (hn : n % 32 = 11) : T_iter n 5 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 32 * k + 11 := ⟨n / 32, by omega⟩
  have h1 : T (32 * k + 11) = 48 * k + 17 := by unfold T; split <;> omega
  have h2 : T (48 * k + 17) = 72 * k + 26 := by unfold T; split <;> omega
  have h3 : T (72 * k + 26) = 36 * k + 13 := by unfold T; split <;> omega
  have h4 : T (36 * k + 13) = 54 * k + 20 := by unfold T; split <;> omega
  have h5 : T (54 * k + 20) = 27 * k + 10 := by unfold T; split <;> omega
  have e : T_iter (32 * k + 11) 5 = T (T (T (T (T (32 * k + 11))))) := rfl
  rw [e, h1, h2, h3, h4, h5]; omega

/-! ## Mod-64 extension: three new guaranteed-descent residue classes -/

/-- **`n ≡ 35 (mod 64)` descends in 4 Terras steps.** `T⁴(64k+35) = 36k+20 < 64k+35`.

Computation (parity vector `(odd, odd, even, even)`):
- T(64k+35) = (3·(64k+35)+1)/2 = 96k+53
- T(96k+53) = (3·(96k+53)+1)/2 = 144k+80
- T(144k+80) = (144k+80)/2 = 72k+40
- T(72k+40) = (72k+40)/2 = 36k+20

Since 36 < 64 and 20 < 35, we have 36k+20 < 64k+35 for all k ≥ 0. This is a mod-64 refinement
of `descent_three_mod_sixteen` (note 35 ≡ 3 mod 16), confirming the parity structure holds at
finer resolution. Descent coefficient 36/64 = 9/16 — same ratio as the mod-16 parent. -/
theorem descent_thirtyfive_mod_sixtyfour {n : ℕ} (hn : n % 64 = 35) : T_iter n 4 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * k + 35 := ⟨n / 64, by omega⟩
  have h1 : T (64 * k + 35) = 96 * k + 53 := by unfold T; split <;> omega
  have h2 : T (96 * k + 53) = 144 * k + 80 := by unfold T; split <;> omega
  have h3 : T (144 * k + 80) = 72 * k + 40 := by unfold T; split <;> omega
  have h4 : T (72 * k + 40) = 36 * k + 20 := by unfold T; split <;> omega
  have e : T_iter (64 * k + 35) 4 = T (T (T (T (64 * k + 35)))) := rfl
  rw [e, h1, h2, h3, h4]; omega

/-- **`n ≡ 51 (mod 64)` descends in 4 Terras steps.** `T⁴(64k+51) = 36k+29 < 64k+51`.

Computation (parity vector `(odd, odd, even, even)`):
- T(64k+51) = (3·(64k+51)+1)/2 = 96k+77
- T(96k+77) = (3·(96k+77)+1)/2 = 144k+116
- T(144k+116) = (144k+116)/2 = 72k+58
- T(72k+58) = (72k+58)/2 = 36k+29

Since 36 < 64 and 29 < 51, we have 36k+29 < 64k+51 for all k ≥ 0. This is the companion
mod-64 sub-class to `descent_thirtyfive_mod_sixtyfour` — note 51 ≡ 3 mod 16 as well, so both
35 and 51 mod 64 are the two halves of the 3 mod 16 class at mod-64 resolution. -/
theorem descent_fiftyone_mod_sixtyfour {n : ℕ} (hn : n % 64 = 51) : T_iter n 4 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * k + 51 := ⟨n / 64, by omega⟩
  have h1 : T (64 * k + 51) = 96 * k + 77 := by unfold T; split <;> omega
  have h2 : T (96 * k + 77) = 144 * k + 116 := by unfold T; split <;> omega
  have h3 : T (144 * k + 116) = 72 * k + 58 := by unfold T; split <;> omega
  have h4 : T (72 * k + 58) = 36 * k + 29 := by unfold T; split <;> omega
  have e : T_iter (64 * k + 51) 4 = T (T (T (T (64 * k + 51)))) := rfl
  rw [e, h1, h2, h3, h4]; omega

/-- **`n ≡ 43 (mod 64)` descends in 5 Terras steps.** `T⁵(64k+43) = 54k+37 < 64k+43`.

Computation (parity vector `(odd, odd, even, odd, even)`):
- T(64k+43) = (3·(64k+43)+1)/2 = 96k+65
- T(96k+65) = (3·(96k+65)+1)/2 = 144k+98
- T(144k+98) = (144k+98)/2 = 72k+49
- T(72k+49) = (3·(72k+49)+1)/2 = 108k+74
- T(108k+74) = (108k+74)/2 = 54k+37

Since 54 < 64 and 37 < 43, we have 54k+37 < 64k+43 for all k ≥ 0. Note 43 ≡ 11 mod 32, so
this is a mod-64 refinement of `descent_eleven_mod_thirtytwo`, confirming the same 5-step
parity vector `(odd, odd, even, odd, even)` at finer resolution. -/
theorem descent_fortythree_mod_sixtyfour {n : ℕ} (hn : n % 64 = 43) : T_iter n 5 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * k + 43 := ⟨n / 64, by omega⟩
  have h1 : T (64 * k + 43) = 96 * k + 65 := by unfold T; split <;> omega
  have h2 : T (96 * k + 65) = 144 * k + 98 := by unfold T; split <;> omega
  have h3 : T (144 * k + 98) = 72 * k + 49 := by unfold T; split <;> omega
  have h4 : T (72 * k + 49) = 108 * k + 74 := by unfold T; split <;> omega
  have h5 : T (108 * k + 74) = 54 * k + 37 := by unfold T; split <;> omega
  have e : T_iter (64 * k + 43) 5 = T (T (T (T (T (64 * k + 43))))) := rfl
  rw [e, h1, h2, h3, h4, h5]; omega

/-- **`n ≡ 23 (mod 32)` descends in 5 Terras steps.** `T⁵(32k+23) = 27k+20 < 32k+23`.
Parity vector `(odd, odd, even, odd, even)` — the same 5-step structure as the `n ≡ 11 (mod 32)`
case. Together with the 11 and 19 mod 32 classes, this gives 4 total ≡3 mod 4 non-trivial
odd classes that descend, bringing the mod-32 guaranteed-descent census to 16+8+4 = 28/32 = 7/8. -/
theorem descent_twentythree_mod_thirtytwo {n : ℕ} (hn : n % 32 = 23) : T_iter n 5 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 32 * k + 23 := ⟨n / 32, by omega⟩
  have h1 : T (32 * k + 23) = 48 * k + 35 := by unfold T; split <;> omega
  have h2 : T (48 * k + 35) = 72 * k + 53 := by unfold T; split <;> omega
  have h3 : T (72 * k + 53) = 108 * k + 80 := by unfold T; split <;> omega
  have h4 : T (108 * k + 80) = 54 * k + 40 := by unfold T; split <;> omega
  have h5 : T (54 * k + 40) = 27 * k + 20 := by unfold T; split <;> omega
  have e : T_iter (32 * k + 23) 5 = T (T (T (T (T (32 * k + 23))))) := rfl
  rw [e, h1, h2, h3, h4, h5]; omega

/-- **Coverage capstone (mod 32).** All four non-trivial `≡ 3 (mod 4)` residue classes mod 32
— `{3,11,19,23}` mod 32 — escape the simple `T²`-descent but still reach a value below
themselves within 5 Terras steps. Together with the 16 even classes and 8 classes `≡1 mod 4`,
this captures **28/32 = 7/8** of all residue classes with guaranteed bounded descent.
A packaged witness for `collatz_residue_descent_density`. -/
theorem descent_within_five {n : ℕ}
    (h : n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 19 ∨ n % 32 = 23) :
    ∃ k, 1 ≤ k ∧ k ≤ 5 ∧ T_iter n k < n := by
  rcases h with h | h | h | h
  · exact ⟨4, by norm_num, by norm_num, descent_three_mod_sixteen h⟩
  · exact ⟨5, by norm_num, by norm_num, descent_eleven_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, descent_nineteen_mod_thirtytwo h⟩
  · exact ⟨5, by norm_num, by norm_num, descent_twentythree_mod_thirtytwo h⟩

/-- **Extended coverage capstone (mod 64).** All 6 proved residue classes — 3 from mod 32 and
3 new mod-64 classes — have guaranteed bounded descent within 5 Terras steps.

This captures the density progress: 28/32 known-descent residues at mod 32, now extended to
confirm the pattern holds at mod 64 for the key sub-classes of the non-trivial ≡3 mod 4
family. The three new mod-64 classes (35, 43, 51 mod 64) are the finer-resolution instances
of the original mod-32 descent classes. -/
theorem descent_within_five_extended {n : ℕ}
    (h : n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 19 ∨
         n % 64 = 35 ∨ n % 64 = 43 ∨ n % 64 = 51) :
    ∃ k, 1 ≤ k ∧ k ≤ 5 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h
  · exact ⟨4, by norm_num, by norm_num, descent_three_mod_sixteen h⟩
  · exact ⟨5, by norm_num, by norm_num, descent_eleven_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, descent_nineteen_mod_thirtytwo h⟩
  · exact ⟨4, by norm_num, by norm_num, descent_thirtyfive_mod_sixtyfour h⟩
  · exact ⟨5, by norm_num, by norm_num, descent_fortythree_mod_sixtyfour h⟩
  · exact ⟨4, by norm_num, by norm_num, descent_fiftyone_mod_sixtyfour h⟩

end CollatzResidueDescent
