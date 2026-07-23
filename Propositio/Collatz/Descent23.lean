import Propositio.Collatz.Basic
import Mathlib.Tactic

/-!
# Guaranteed bounded descent for `n ≡ 23 (mod 32)` (Terras structure)

For the Terras half-step `T` (`n/2` if even, `(3n+1)/2` if odd), the residue class
`n ≡ 23 (mod 32)` fixes the parities of the first five steps, so `T_iter n 5` is an explicit
linear function of `n`. A faithful family member of the bounded-descent residue census in
`CollatzResidueDescent.lean` (cf. `descent_eleven_mod_thirtytwo`).

`T⁵(32k+23) = 27k+20 < 32k+23` for all `k ≥ 0`.

Computation (parity vector `(odd, odd, odd, even, even)`):
- T(32k+23) = (3·(32k+23)+1)/2 = 48k+35
- T(48k+35) = (3·(48k+35)+1)/2 = 72k+53
- T(72k+53) = (3·(72k+53)+1)/2 = 108k+80
- T(108k+80) = (108k+80)/2 = 54k+40
- T(54k+40) = (54k+40)/2 = 27k+20

`open TerrasDensity` provides `T`, `T_iter`.
-/

namespace CollatzDescent23

open TerrasDensity

/-- **`n ≡ 23 (mod 32)` descends in 5 Terras steps.** `T⁵(32k+23) = 27k+20 < 32k+23`. Parity vector
`(odd, odd, odd, even, even)`. Extends the bounded-descent residue census mod 32. -/
theorem descent_twentythree_mod_thirtytwo {n : ℕ} (hn : n % 32 = 23) : T_iter n 5 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 32 * k + 23 := ⟨n / 32, by omega⟩
  have h1 : T (32 * k + 23) = 48 * k + 35 := by unfold T; split <;> omega
  have h2 : T (48 * k + 35) = 72 * k + 53 := by unfold T; split <;> omega
  have h3 : T (72 * k + 53) = 108 * k + 80 := by unfold T; split <;> omega
  have h4 : T (108 * k + 80) = 54 * k + 40 := by unfold T; split <;> omega
  have h5 : T (54 * k + 40) = 27 * k + 20 := by unfold T; split <;> omega
  have e : T_iter (32 * k + 23) 5 = T (T (T (T (T (32 * k + 23))))) := rfl
  rw [e, h1, h2, h3, h4, h5]; omega

end CollatzDescent23
