import Propositio.NumberTheory.Collatz.Basic
import Propositio.Tactics
import Mathlib.Tactic

/-!
# Exact `T`-iterate value formulas for two residue classes (Terras structure)

For the Terras half-step `T` (`n/2` if even, `(3n+1)/2` if odd), fixing a residue
class `n ≡ r (mod 2^m)` fixes the parities of the first `m` steps, so `T_iter n m`
is an explicit linear function of `n`.  The descent lemmas in `CollatzResidueDescent`
only record the *inequality* `T_iter n m < n`; here we record two exact closed-form
values, the numerically-verified conjecture cards `conj-2026-06-21-002` and
`conj-2026-06-21-003`.

* `T_iter_two_seven_mod_eight`  — `n ≡ 7 (mod 8) ⟹ T²(n) = (9n+5)/4`.
  Parity vector `(odd, odd)`: `T(8k+7)=12k+11`, `T(12k+11)=18k+17`.
* `T_iter_three_three_mod_eight` — `n ≡ 3 (mod 8) ⟹ T³(n) = (9n+5)/8`.
  Parity vector `(odd, odd, even)`: `T(8k+3)=12k+5`, `T(12k+5)=18k+8`, `T(18k+8)=9k+4`.

`open TerrasDensity` provides `T`, `T_iter`; `collatz_step` (from `Tactics`) evaluates
one `T` step by parity (`unfold T; split <;> omega`).
-/

namespace CollatzExactIterate

open TerrasDensity

/-- **`n ≡ 7 (mod 8)` ⟹ `T²(n) = (9n+5)/4`.** With `n = 8k+7`: both first steps are
odd-steps, `T(8k+7)=12k+11` and `T(12k+11)=18k+17`, while `(9(8k+7)+5)/4 = 18k+17`. -/
theorem T_iter_two_seven_mod_eight {n : ℕ} (hn : n % 8 = 7) :
    T_iter n 2 = (9 * n + 5) / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 7 := ⟨n / 8, by omega⟩
  have h1 : T (8 * k + 7) = 12 * k + 11 := by collatz_step
  have h2 : T (12 * k + 11) = 18 * k + 17 := by collatz_step
  have e : T_iter (8 * k + 7) 2 = T (T (8 * k + 7)) := rfl
  rw [e, h1, h2]; omega

/-- **`n ≡ 3 (mod 8)` ⟹ `T³(n) = (9n+5)/8`.** With `n = 8k+3`: parity vector
`(odd, odd, even)`, `T(8k+3)=12k+5`, `T(12k+5)=18k+8`, `T(18k+8)=9k+4`, while
`(9(8k+3)+5)/8 = 9k+4`. -/
theorem T_iter_three_three_mod_eight {n : ℕ} (hn : n % 8 = 3) :
    T_iter n 3 = (9 * n + 5) / 8 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 3 := ⟨n / 8, by omega⟩
  have h1 : T (8 * k + 3) = 12 * k + 5 := by collatz_step
  have h2 : T (12 * k + 5) = 18 * k + 8 := by collatz_step
  have h3 : T (18 * k + 8) = 9 * k + 4 := by collatz_step
  have e : T_iter (8 * k + 3) 3 = T (T (T (8 * k + 3))) := rfl
  rw [e, h1, h2, h3]; omega

/-- **`n ≡ 1 (mod 8)` ⟹ `T²(n) = (3n+1)/4`.** With `n = 8k+1`: `T(8k+1)=12k+2` (even),
`T(12k+2)=6k+1`, and `(3(8k+1)+1)/4 = 6k+1`.  Completes the odd-residue mod-8 family with
`T_iter_three_three_mod_eight`, `T_iter_two_seven_mod_eight`, `T_iter_three_five_mod_eight`. -/
theorem T_iter_two_one_mod_eight {n : ℕ} (hn : n % 8 = 1) :
    T_iter n 2 = (3 * n + 1) / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 1 := ⟨n / 8, by omega⟩
  have h1 : T (8 * k + 1) = 12 * k + 2 := by collatz_step
  have h2 : T (12 * k + 2) = 6 * k + 1 := by collatz_step
  have e : T_iter (8 * k + 1) 2 = T (T (8 * k + 1)) := rfl
  rw [e, h1, h2]; omega

/-- **`n ≡ 5 (mod 8)` ⟹ `T³(n) = (3n+1)/8`.** With `n = 8k+5`: parity vector `(odd, even, even)`,
`T(8k+5)=12k+8`, `T(12k+8)=6k+4`, `T(6k+4)=3k+2`, and `(3(8k+5)+1)/8 = 3k+2`. -/
theorem T_iter_three_five_mod_eight {n : ℕ} (hn : n % 8 = 5) :
    T_iter n 3 = (3 * n + 1) / 8 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  have h1 : T (8 * k + 5) = 12 * k + 8 := by collatz_step
  have h2 : T (12 * k + 8) = 6 * k + 4 := by collatz_step
  have h3 : T (6 * k + 4) = 3 * k + 2 := by collatz_step
  have e : T_iter (8 * k + 5) 3 = T (T (T (8 * k + 5))) := rfl
  rw [e, h1, h2, h3]; omega

end CollatzExactIterate
