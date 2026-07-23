/-
Zsygmondy's theorem, general two-variable existence — FULL CAPSTONE.

Assembles the three disjoint pieces of the `(a, b)` plane (partitioned by the gap `a - b`)
that together cover every coprime pair `a > b ≥ 1`:

  * `a - b = 1`, `b = 1` (i.e. `(a, b) = (2, 1)`, the single classical sporadic-exception
    point): `ZsygmondyBaseThree.zsygmondy_base_one_full`, instantiated at `a = 2`.
  * `a - b = 1`, `b ≥ 2` (consecutive integers, general `b`):
    `ZsygmondyExceptionalCapstoneGeneral.primitive_prime_exists_succ_of_b_ge_two`
    (no exceptions).
  * `a - b ≥ 2` (non-consecutive, ALL `b ≥ 1` at once):
    `ZsygmondyGeneralGapTwo.zsygmondy_general_of_gap_two` (this session's new result; only
    the classical `n = 2` carve-out).

into ONE closed statement: for every `n ≥ 2` and coprime integers `a > b ≥ 1`, `a^n - b^n`
has a primitive prime divisor, except the two classical carve-outs (`n = 2` with `a + b` a
power of two; `(n, a, b) = (6, 2, 1)`).
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyBaseThree
import Propositio.NumberTheory.Zsygmondy.ZsygmondyExceptionalCapstoneGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyGeneralGapTwo

namespace ZsygmondyFullExistenceCapstone

/-- **Zsygmondy's theorem, full general two-variable existence.** For every `n ≥ 2`, coprime
integers `a > b ≥ 1`, and the two classical carve-outs — `¬ (n = 2 ∧ a + b` a power of
two`)` and `¬ (n = 6 ∧ a = 2 ∧ b = 1)` — the number `a^n - b^n` has a *primitive* prime
divisor: a prime `p` dividing `a^n - b^n` but none of `a^m - b^m` for `0 < m < n`. -/
theorem zsygmondy_general {n : ℕ} (hn : 1 < n) {a b : ℤ} (hb : 1 ≤ b) (hab : b < a)
    (hcop : IsCoprime a b)
    (hexc2 : ¬ (n = 2 ∧ ∃ t : ℕ, (a + b).natAbs = 2 ^ t))
    (hexc6 : ¬ (n = 6 ∧ a = 2 ∧ b = 1)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - b ^ n ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  by_cases hgap1 : a - b = 1
  · -- consecutive integers
    by_cases hb1 : b = 1
    · -- the single point (a, b) = (2, 1)
      have ha2 : a = 2 := by omega
      subst ha2
      subst hb1
      have hexc2' : ¬ (n = 2 ∧ ∃ t : ℕ, ((2 : ℤ) + 1).natAbs = 2 ^ t) := hexc2
      have hexc6' : ¬ (n = 6 ∧ (2 : ℤ) = 2) := fun ⟨hn6, _⟩ => hexc6 ⟨hn6, rfl, rfl⟩
      have h := ZsygmondyBaseThree.zsygmondy_base_one_full hn (a := (2 : ℤ)) (by norm_num)
        hexc2' hexc6'
      simpa using h
    · -- b ≥ 2, a = b + 1
      have hb2 : 2 ≤ b := by omega
      have hab' : a = b + 1 := by omega
      subst hab'
      exact ZsygmondyExceptionalCapstoneGeneral.primitive_prime_exists_succ_of_b_ge_two hn hb2
  · -- a - b ≥ 2
    have hgap2 : b + 2 ≤ a := by omega
    exact ZsygmondyGeneralGapTwo.zsygmondy_general_of_gap_two hn hb hgap2 hcop hexc2

end ZsygmondyFullExistenceCapstone
