import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# The 2-adic valuation of `3n + 1` for `n ≡ 3 (mod 4)`

For the Syracuse 3-adic-bias line we need the clean fact that when `n ≡ 3 (mod 4)` the number
`3n + 1` carries exactly one factor of `2`.

Concretely `n = 4k + 3 ⟹ 3n + 1 = 12k + 10 = 2 * (6k + 5)`, and `6k + 5` is odd, so

    padicValNat 2 (3n + 1) = 1 + padicValNat 2 (6k + 5) = 1.

Sorry-free / axiom-clean (no `native_decide`).
-/

/-- `padicValNat 2 (2 * w) = 1` when `w` is odd: the single factor of `2` is the only one.
(Reproduced from the private helper in `SyracuseMaxGrowth.lean`.) -/
private theorem padicValNat_two_two_mul_odd' {w : ℕ} (hw : Odd w) :
    padicValNat 2 (2 * w) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ := hw
  have h1 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  have h2 : padicValNat 2 (2 * m + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  rw [padicValNat.mul (by norm_num) (by omega), h1, h2]

/-- **The 2-adic valuation of `3n + 1` for `n ≡ 3 (mod 4)`.**

When `n ≡ 3 (mod 4)`, `3n + 1` is twice an odd number, so its 2-adic valuation is exactly `1`. -/
theorem padicValNat_two_three_mul_add_one_of_three_mod_four {n : ℕ} (hn : n % 4 = 3) :
    padicValNat 2 (3 * n + 1) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  have heq : 3 * (4 * k + 3) + 1 = 2 * (6 * k + 5) := by ring
  have hw : Odd (6 * k + 5) := ⟨3 * k + 2, by ring⟩
  rw [heq]
  exact padicValNat_two_two_mul_odd' hw
