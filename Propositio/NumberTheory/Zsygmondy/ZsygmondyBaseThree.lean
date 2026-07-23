/-
Zsygmondy: the totient-growth estimate `n ≤ 2 ^ φ(n)` for `n ≠ 6`, closing the `a = 3` base
case of `ZsygmondyBaseOneCapstone` (previously excluded — see that file's "Honest scope: why
`a = 3` is excluded" section).

## Status of this file — CLOSED (route (a) from the task brief)

The sharper totient-growth lemma is now proved UNCONDITIONALLY for `n ≠ 6`
(`totient_growth_two_ne_six`), via a `Nat.recOnPrimePow` induction strengthened with a SECOND
companion clause (`totient_growth_two`'s `.2`) that survives peeling BOTH a bare factor of `2`
and a bare factor of `3` — the two primes where the naive per-factor margin
`2 * p ^ k ≤ 2 ^ φ(p^k)` fails (`(p,k) = (2,1)`, `(2,2)`, `(3,1)`).

### Proof sketch

Strong induction on the combined statement `Q(n) : (n ≠ 6 → n ≤ 2^φ(n)) ∧ (Odd n ∧ n ≠ 1 ∧
n ≠ 3 → 2n ≤ 2^φ(n))`, peeling one prime-power factor `n = p^k * a` at a time. The companion
clause (analogous to `ZsygmondyTotientGrowth`'s single `Odd n → 2n ≤ 3^φ(n)` rescue) is now
needed for BOTH `p = 2` (bare factor, `k = 1`: cofactor `a` is automatically odd, and
`ih.2 a` supplies exactly the extra margin) and — less obviously — is what MAKES the `p = 3`
`k = 1` combination step provable via the plain clause `ih.1 a`, since the two exceptional
configurations `(p, k, a) = (2, 1, 3)` and `(3, 1, 2)` are literally the SAME number `n = 6`
approached from two different peeled primes, and both become vacuous once `n ≠ 6` is a
hypothesis. Three further "hard" prime-power margins (`p = 2, k = 2`; `p = 3, k = 1` with
`a ≥ 3`; `p ≥ 5` with cofactor `a ∈ {3, 6}`) are closed by a direct exploitation of the
totient lower bound `a ≥ 3 → φ(a) ≥ 2` (`Nat.totient_eq_one_iff`), not by a per-prime margin
lemma. All other `(p, k)` combinations use the generic `margin_absorb` combinator against one
of three per-prime-power margin facts (`margin_two_ge3`, `margin_three_ge2`, `margin_ge5`),
each proved by its own small induction on `k` sharing the `growth_step` combinatorial core.

The closure into the full `b = 1` Zsygmondy theorem (`zsygmondy_base_one_full`, at the bottom
of this file) plugs `totient_growth_two_ne_six` into `ZsygmondyEvenPrime.
primitive_prime_exists_of_size` as the `hsize` hypothesis for `a = 3`, patches the single
residual `(a, n) = (3, 6)` gap with `ZsygmondyBaseOneCapstone.primitive_prime_exists_three_six`
(already proved there), and assembles this with the pre-existing `a = 2 ∨ a ≥ 4` capstone
(`ZsygmondyBaseOneCapstone.zsygmondy_base_one`) to cover ALL `a ≥ 2` — closing the FULL
`b = 1` Zsygmondy theorem with no base excluded.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.Linarith
import Propositio.NumberTheory.Zsygmondy.ZsygmondyEvenPrime
import Propositio.NumberTheory.Zsygmondy.ZsygmondyBaseOneCapstone

namespace ZsygmondyBaseThree

open Nat

/-! ### Elementary numeric helper lemmas -/

/-- `m ≤ 2 ^ (m - 2)` for all `m ≥ 4` (subtraction-free form: `j + 4 ≤ 2 ^ (j + 2)`). -/
private theorem add_four_le_two_pow_succ_succ (j : ℕ) : j + 4 ≤ 2 ^ (j + 2) := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    have h2 : (2:ℕ) ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by rw [pow_succ]; ring
    omega

/-- General corollary: `m ≤ 2 ^ (m - 2)` for all `m ≥ 4`. -/
private theorem self_le_two_pow_sub_two {m : ℕ} (hm : 4 ≤ m) : m ≤ 2 ^ (m - 2) := by
  obtain ⟨j, hj⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
  have h := add_four_le_two_pow_succ_succ j
  have heq : m - 2 = j + 2 := by omega
  rw [heq, hj]
  omega

/-- `m ≤ 2 ^ (m - 1)` for all `m ≥ 1` (equivalently `m - 1 < 2 ^ (m - 1)`, an instance of
`Nat.lt_two_pow_self`). -/
private theorem self_le_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : m ≤ 2 ^ (m - 1) := by
  have h := Nat.lt_two_pow_self (n := m - 1)
  omega

/-! ### Pure prime powers: the UNCONDITIONAL bound `p ^ k ≤ 2 ^ φ(p ^ k)` -/

/-- **Pure prime power bound, unconditional.** For every prime `p` and `k ≥ 1`,
`p ^ k ≤ 2 ^ φ(p ^ k)`. Unlike the analogous margin bounds used later, this ONE holds with
NO exceptions at all (not even at `p = 2, k = 1` or `p = 3, k = 1`): it is the bare inequality,
without the extra factor of `2` margin needed for the multiplicative combination step. -/
theorem prime_pow_le_two_pow_totient {p : ℕ} (hp : p.Prime) :
    ∀ k, 1 ≤ k → p ^ k ≤ 2 ^ Nat.totient (p ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [pow_one, Nat.totient_prime hp]
    exact self_le_two_pow_sub_one hp.pos
  | succ n hn ih =>
    have hntot : Nat.totient (p ^ n) = p ^ (n - 1) * (p - 1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
    have hnp1 : n + 1 - 1 = n := by omega
    have htarget : Nat.totient (p ^ (n + 1)) = p ^ n * (p - 1) := by
      rw [Nat.totient_prime_pow hp (by omega), hnp1]
    rw [htarget]
    set B : ℕ := 2 ^ (p ^ (n - 1) * (p - 1)) with hBdef
    have hBp : (2:ℕ) ^ (p ^ n * (p - 1)) = B ^ p := by
      rw [hBdef, ← pow_mul]
      congr 1
      have : p ^ n = p ^ (n - 1) * p := by
        rw [← pow_succ]
        congr 1
        omega
      rw [this]
      ring
    rw [hBp]
    have hB_ge : p ≤ B := by
      have h1 : (2:ℕ) ^ (p - 1) ≤ B := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : 1 ≤ p ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne')
        calc p - 1 = 1 * (p - 1) := by ring
          _ ≤ p ^ (n - 1) * (p - 1) := Nat.mul_le_mul_right _ this
      have h2 : p ≤ 2 ^ (p - 1) := self_le_two_pow_sub_one hp.pos
      omega
    have hBeq : B = 2 ^ Nat.totient (p ^ n) := by rw [hBdef, hntot]
    have ihp : p ^ n ≤ B := by rw [hBeq]; exact ih
    have hstep1 : p ^ (n + 1) = p * p ^ n := by rw [pow_succ]; ring
    have hstep2 : p * p ^ n ≤ p * B := Nat.mul_le_mul_left p ihp
    have hstep3 : p * B ≤ B * B := Nat.mul_le_mul_right B hB_ge
    have hstep4 : B * B ≤ B ^ p := by
      calc B * B = B ^ 2 := by ring
        _ ≤ B ^ p := Nat.pow_le_pow_right (by
            have : 1 ≤ B := by
              have := hB_ge; have hppos := hp.pos; omega
            omega) hp.two_le
    calc p ^ (n + 1) = p * p ^ n := hstep1
      _ ≤ p * B := hstep2
      _ ≤ B * B := hstep3
      _ ≤ B ^ p := hstep4

/-! ### Margin-absorption helpers (base `2` analogues of `ZsygmondyTotientGrowth.margin_absorb`) -/

/-- If `2 * c ≤ 2 ^ t` (a per-factor margin bound, base `2`) and `X ≤ 2 ^ e` (`e ≥ 1`), then
`c * X ≤ 2 ^ (t * e)`. -/
private theorem margin_absorb {c t X e : ℕ} (hmargin : 2 * c ≤ 2 ^ t) (ht1 : 1 ≤ t)
    (hXe : X ≤ 2 ^ e) (he1 : 1 ≤ e) : c * X ≤ 2 ^ (t * e) := by
  obtain ⟨q, rfl⟩ : ∃ q, e = q + 1 := ⟨e - 1, by omega⟩
  have hstep1 : c * X ≤ c * 2 ^ (q + 1) := Nat.mul_le_mul_left c hXe
  have hstep2 : c * (2:ℕ) ^ (q + 1) = (2 * c) * 2 ^ q := by
    rw [pow_succ]; ring
  have hstep3 : (2 * c) * 2 ^ q ≤ 2 ^ t * 2 ^ q := Nat.mul_le_mul_right _ hmargin
  have hstep4 : (2:ℕ) ^ t * 2 ^ q ≤ 2 ^ t * (2 ^ t) ^ q := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
  have hstep5 : (2:ℕ) ^ t * (2 ^ t) ^ q = (2 ^ t) ^ (q + 1) := by
    rw [pow_succ]; ring
  have hstep6 : (2:ℕ) ^ t * (2 ^ t) ^ q = 2 ^ (t * (q + 1)) := by
    rw [hstep5, ← pow_mul]
  calc c * X ≤ c * 2 ^ (q + 1) := hstep1
    _ = (2 * c) * 2 ^ q := hstep2
    _ ≤ 2 ^ t * 2 ^ q := hstep3
    _ ≤ 2 ^ t * (2 ^ t) ^ q := hstep4
    _ = 2 ^ (t * (q + 1)) := hstep6

/-! ### Per-prime margin bounds `2 * p ^ k ≤ 2 ^ φ(p ^ k)`

These hold for every `(p, k)` EXCEPT `(2, 1)`, `(2, 2)`, `(3, 1)` — the three configurations
whose rescue is the whole point of this file (via the companion `Odd`-clause, mirroring
`ZsygmondyTotientGrowth`'s single `(2, 1)` rescue). -/

/-- Generic growth step: if `B ≥ p ≥ 2` and `b ≤ B`, then `p * b ≤ B ^ p`. The shared
combinatorial core of every "extend a per-prime bound from `k` to `k+1`" induction below. -/
private theorem growth_step {p b B : ℕ} (hp2 : 2 ≤ p) (hBp : p ≤ B) (hb : b ≤ B) :
    p * b ≤ B ^ p := by
  have hstep2 : p * b ≤ p * B := Nat.mul_le_mul_left p hb
  have hstep3 : p * B ≤ B * B := Nat.mul_le_mul_right B hBp
  have hB1 : 1 ≤ B := by omega
  have hstep4 : B * B ≤ B ^ p := by
    calc B * B = B ^ 2 := by ring
      _ ≤ B ^ p := Nat.pow_le_pow_right hB1 hp2
  omega

/-- **Margin bound, `p = 2`, `k ≥ 3`.** `2 * 2 ^ k ≤ 2 ^ φ(2 ^ k)`. -/
private theorem margin_two_ge3 : ∀ k, 3 ≤ k → 2 * 2 ^ k ≤ 2 ^ Nat.totient (2 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have htn : Nat.totient (2 ^ n) = 2 ^ (n - 1) := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; norm_num
    have htn1 : Nat.totient (2 ^ (n + 1)) = 2 ^ n := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      have : n + 1 - 1 = n := by omega
      rw [this]; norm_num
    rw [htn1]
    set B : ℕ := 2 ^ (2 ^ (n - 1)) with hBdef
    have hBeq : B = 2 ^ Nat.totient (2 ^ n) := by rw [hBdef, htn]
    have hBp2 : (2:ℕ) ≤ B := by
      rw [hBdef]
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ (n - 1)) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    have hgrow : 2 * (2 * 2 ^ n) ≤ B ^ 2 := by
      have hih : 2 * 2 ^ n ≤ B := by rw [hBeq]; exact ih
      have := growth_step (p := 2) (b := 2 * 2 ^ n) (B := B) (by norm_num) hBp2 hih
      simpa using this
    have hB2 : B ^ 2 = 2 ^ (2 ^ n) := by
      rw [hBdef, ← pow_mul]
      congr 1
      have hns : n = (n - 1) + 1 := by omega
      calc 2 ^ (n - 1) * 2 = 2 ^ ((n-1)+1) := by rw [pow_succ]
        _ = 2 ^ n := by rw [← hns]
    have : 2 * 2 ^ (n + 1) = 2 * (2 * 2 ^ n) := by rw [pow_succ]; ring
    rw [this, ← hB2]
    exact hgrow

/-- **Margin bound, `p = 3`, `k ≥ 2`.** `2 * 3 ^ k ≤ 2 ^ φ(3 ^ k)`. -/
private theorem margin_three_ge2 : ∀ k, 2 ≤ k → 2 * 3 ^ k ≤ 2 ^ Nat.totient (3 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have htn : Nat.totient (3 ^ n) = 2 * 3 ^ (n - 1) := by
      rw [Nat.totient_prime_pow Nat.prime_three (by omega)]; ring
    have htn1 : Nat.totient (3 ^ (n + 1)) = 2 * 3 ^ n := by
      rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
      have : n + 1 - 1 = n := by omega
      rw [this]; ring
    rw [htn1]
    set B : ℕ := 2 ^ (2 * 3 ^ (n - 1)) with hBdef
    have hBeq : B = 2 ^ Nat.totient (3 ^ n) := by rw [hBdef, htn]
    have hBge : (3:ℕ) ≤ B := by
      rw [hBdef]
      calc (3:ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * 3 ^ (n - 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have : 1 ≤ 3 ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
          nlinarith
    have hih : 2 * 3 ^ n ≤ B := by rw [hBeq]; exact ih
    have hgrow : 3 * (2 * 3 ^ n) ≤ B ^ 3 :=
      growth_step (p := 3) (b := 2 * 3 ^ n) (B := B) (by norm_num) hBge hih
    have hB3 : B ^ 3 = 2 ^ (2 * 3 ^ n) := by
      rw [hBdef, ← pow_mul]
      congr 1
      have hns : n = (n - 1) + 1 := by omega
      calc 2 * 3 ^ (n - 1) * 3 = 2 * (3 ^ (n - 1) * 3) := by ring
        _ = 2 * 3 ^ ((n-1)+1) := by rw [pow_succ]
        _ = 2 * 3 ^ n := by rw [← hns]
    have heq2 : 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by rw [pow_succ]; ring
    rw [heq2, ← hB3]
    exact hgrow

/-- **Margin bound, primes `p ≥ 5`, any `k ≥ 1`.** `2 * p ^ k ≤ 2 ^ φ(p ^ k)`. Unlike `p = 2`
and `p = 3`, this holds for EVERY `k ≥ 1` including `k = 1` (no exception at the base case). -/
private theorem margin_ge5 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ k, 1 ≤ k → 2 * p ^ k ≤ 2 ^ Nat.totient (p ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [pow_one, Nat.totient_prime hp]
    have h1 : p ≤ 2 ^ (p - 2) := self_le_two_pow_sub_two (by omega)
    have h2 : (2:ℕ) ^ (p - 1) = 2 * 2 ^ (p - 2) := by
      have : p - 1 = (p - 2) + 1 := by omega
      rw [this, pow_succ]; ring
    omega
  | succ n hn ih =>
    have htn : Nat.totient (p ^ n) = p ^ (n - 1) * (p - 1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
    have htn1 : Nat.totient (p ^ (n + 1)) = p ^ n * (p - 1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
      have : n + 1 - 1 = n := by omega
      rw [this]
    rw [htn1]
    set B : ℕ := 2 ^ (p ^ (n - 1) * (p - 1)) with hBdef
    have hBeq : B = 2 ^ Nat.totient (p ^ n) := by rw [hBdef, htn]
    have hBp : p ≤ B := by
      have h1 : (2:ℕ) ^ (p - 1) ≤ B := by
        rw [hBdef]
        apply Nat.pow_le_pow_right (by norm_num)
        have h1n : 1 ≤ p ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne')
        calc p - 1 = 1 * (p - 1) := by ring
          _ ≤ p ^ (n - 1) * (p - 1) := Nat.mul_le_mul_right _ h1n
      have h2 : p ≤ 2 ^ (p - 1) := self_le_two_pow_sub_one hp.pos
      omega
    have hih : 2 * p ^ n ≤ B := by rw [hBeq]; exact ih
    have hgrow : p * (2 * p ^ n) ≤ B ^ p := growth_step (by omega) hBp hih
    have hBpow : B ^ p = 2 ^ (p ^ n * (p - 1)) := by
      rw [hBdef, ← pow_mul]
      congr 1
      have hns : n = (n - 1) + 1 := by omega
      calc p ^ (n - 1) * (p - 1) * p = p ^ (n - 1) * p * (p - 1) := by ring
        _ = p ^ ((n-1)+1) * (p - 1) := by rw [pow_succ]
        _ = p ^ n * (p - 1) := by rw [← hns]
    have heq2 : 2 * p ^ (n + 1) = p * (2 * p ^ n) := by rw [pow_succ]; ring
    rw [heq2, ← hBpow]
    exact hgrow

/-! ### A small totient lower bound -/

/-- For `a ≥ 3`, `φ(a) ≥ 2`. (`φ(a) = 1` only for `a ∈ {1, 2}`, by `Nat.totient_eq_one_iff`.) -/
private theorem totient_ge_two_of_ge_three {a : ℕ} (ha : 3 ≤ a) : 2 ≤ Nat.totient a := by
  have hpos : 0 < Nat.totient a := Nat.totient_pos.mpr (by omega)
  by_contra h
  have h1 : Nat.totient a = 1 := by omega
  rcases Nat.totient_eq_one_iff.mp h1 with h2 | h2 <;> omega

/-! ### The combined main theorem -/

/-- **Totient growth, base `2`, combined form.** For every `n : ℕ`:
`n ≠ 6 → n ≤ 2 ^ φ(n)`, and moreover if `n` is odd and `n ∉ {1, 3}`, `2 * n ≤ 2 ^ φ(n)`.
The companion clause is the reinforcement that survives peeling a bare factor of `2` or `3`
(see the file docstring). -/
theorem totient_growth_two : ∀ n : ℕ,
    (n ≠ 6 → n ≤ 2 ^ Nat.totient n) ∧
    (Odd n ∧ n ≠ 1 ∧ n ≠ 3 → 2 * n ≤ 2 ^ Nat.totient n) := by
  intro n
  induction n using Nat.recOnPrimePow with
  | zero => simp [Nat.totient_zero]
  | one =>
    refine ⟨fun _ => by norm_num, ?_⟩
    rintro ⟨-, h1, -⟩
    exact absurd rfl h1
  | prime_pow_mul a p k hp hpa hk ih =>
    have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
    have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hcop : (p ^ k).Coprime a :=
      (Nat.coprime_pow_left_iff hk p a).mpr (hp.coprime_iff_not_dvd.mpr hpa)
    have htot : Nat.totient (p ^ k * a) = Nat.totient (p ^ k) * Nat.totient a :=
      Nat.totient_mul hcop
    obtain ⟨ihA, ihB⟩ := ih
    by_cases hp2 : p = 2
    · subst hp2
      have haodd : Odd a := by
        rcases Nat.even_or_odd a with he | ho
        · exact absurd (even_iff_two_dvd.mp he) hpa
        · exact ho
      have hn_even : Even (2 ^ k * a) := by
        have h2dvd : (2:ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
        exact even_iff_two_dvd.mpr (Dvd.dvd.mul_right h2dvd a)
      refine ⟨?_, ?_⟩
      · -- clause A
        intro hn6
        rw [htot]
        by_cases ha1 : a = 1
        · subst ha1
          simp only [mul_one]
          simpa using prime_pow_le_two_pow_totient Nat.prime_two k hk
        · by_cases hk1 : k = 1
          · subst hk1
            by_cases ha3 : a = 3
            · exact absurd (by rw [ha3]; norm_num) hn6
            · have hb := ihB ⟨haodd, ha1, ha3⟩
              have ht1 : Nat.totient (2 ^ 1) = 1 := by decide
              rw [ht1, one_mul, pow_one]
              exact hb
          · by_cases hk2 : k = 2
            · subst hk2
              have ha3le : 3 ≤ a := by
                rcases haodd with ⟨m, hm⟩; omega
              have hXa : a ≤ 2 ^ Nat.totient a := ihA (by omega)
              have hX4 : (4:ℕ) ≤ 2 ^ Nat.totient a := by
                calc (4:ℕ) = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ Nat.totient a :=
                    Nat.pow_le_pow_right (by norm_num) (totient_ge_two_of_ge_three ha3le)
              have ht2 : Nat.totient (2 ^ 2) = 2 := by decide
              rw [ht2]
              have heq : (2:ℕ) ^ (2 * Nat.totient a) = (2 ^ Nat.totient a) ^ 2 := by
                rw [mul_comm, pow_mul]
              rw [heq]
              nlinarith [hXa, hX4]
            · have hk3 : 3 ≤ k := by omega
              have hmargin := margin_two_ge3 k hk3
              have hea : 1 ≤ Nat.totient a := Nat.totient_pos.mpr hapos
              have ht1 : 1 ≤ Nat.totient (2 ^ k) := Nat.totient_pos.mpr (pow_pos (by norm_num) k)
              have hXa : a ≤ 2 ^ Nat.totient a := ihA (by
                rintro rfl; exact absurd haodd (by decide))
              exact margin_absorb hmargin ht1 hXa hea
      · -- clause B: vacuous, n is even
        rintro ⟨hodd, -, -⟩
        exact absurd hodd (Nat.not_odd_iff_even.mpr hn_even)
    · by_cases hp3 : p = 3
      · subst hp3
        have h3kodd : Odd ((3:ℕ) ^ k) := Odd.pow (by decide)
        have hniff : Odd (3 ^ k * a) ↔ Odd a := by
          rw [Nat.odd_mul]
          simp [h3kodd]
        refine ⟨?_, ?_⟩
        · -- clause A
          intro hn6
          rw [htot]
          by_cases ha1 : a = 1
          · subst ha1
            simp only [mul_one]
            simpa using prime_pow_le_two_pow_totient Nat.prime_three k hk
          · by_cases hk1 : k = 1
            · subst hk1
              by_cases ha2 : a = 2
              · exact absurd (by rw [ha2]; norm_num) hn6
              · have ha3le : 3 ≤ a := by omega
                have hXa : a ≤ 2 ^ Nat.totient a := ihA (by
                  rintro rfl; exact hpa (by norm_num))
                have hX4 : (4:ℕ) ≤ 2 ^ Nat.totient a := by
                  calc (4:ℕ) = 2 ^ 2 := by norm_num
                    _ ≤ 2 ^ Nat.totient a :=
                      Nat.pow_le_pow_right (by norm_num) (totient_ge_two_of_ge_three ha3le)
                have ht1 : Nat.totient (3 ^ 1) = 2 := by decide
                rw [ht1, pow_one]
                have heq : (2:ℕ) ^ (2 * Nat.totient a) = (2 ^ Nat.totient a) ^ 2 := by
                  rw [mul_comm, pow_mul]
                rw [heq]
                nlinarith [hXa, hX4]
            · have hk2 : 2 ≤ k := by omega
              have hmargin := margin_three_ge2 k hk2
              have hea : 1 ≤ Nat.totient a := Nat.totient_pos.mpr hapos
              have ht1 : 1 ≤ Nat.totient (3 ^ k) := Nat.totient_pos.mpr (pow_pos (by norm_num) k)
              have hXa : a ≤ 2 ^ Nat.totient a := ihA (by
                rintro rfl; exact hpa (by norm_num))
              have h2c : 2 * 3 ^ k ≤ 2 ^ Nat.totient (3 ^ k) := hmargin
              exact margin_absorb h2c ht1 hXa hea
        · -- clause B
          rintro ⟨hoddn, hne1, hne3⟩
          have haodd : Odd a := hniff.mp hoddn
          rw [htot]
          by_cases ha1 : a = 1
          · subst ha1
            simp only [mul_one] at hne1 hne3 ⊢
            by_cases hk1 : k = 1
            · subst hk1; exact absurd rfl hne3
            · have hk2 : 2 ≤ k := by omega
              simpa using margin_three_ge2 k hk2
          · have hb := ihB ⟨haodd, ha1, by
              rintro rfl; exact hpa (by norm_num)⟩
            by_cases hk1 : k = 1
            · subst hk1
              have ha3le : 3 ≤ a := by
                rcases haodd with ⟨m, hm⟩; omega
              have hXa2 : 2 * a ≤ 2 ^ Nat.totient a := hb
              have hX4 : (4:ℕ) ≤ 2 ^ Nat.totient a := by
                calc (4:ℕ) = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ Nat.totient a :=
                    Nat.pow_le_pow_right (by norm_num) (totient_ge_two_of_ge_three ha3le)
              have ht1 : Nat.totient (3 ^ 1) = 2 := by decide
              rw [ht1, pow_one]
              have heq : (2:ℕ) ^ (2 * Nat.totient a) = (2 ^ Nat.totient a) ^ 2 := by
                rw [mul_comm, pow_mul]
              rw [heq]
              have hX3 : 3 ≤ 2 ^ Nat.totient a := by omega
              have hstepA : 3 * (2 * a) ≤ 3 * 2 ^ Nat.totient a := Nat.mul_le_mul_left 3 hXa2
              have hstepB : 3 * 2 ^ Nat.totient a ≤ 2 ^ Nat.totient a * 2 ^ Nat.totient a :=
                Nat.mul_le_mul_right _ hX3
              have heq3 : 2 * (3 * a) = 3 * (2 * a) := by ring
              have heq4 : (2:ℕ) ^ Nat.totient a * 2 ^ Nat.totient a = (2 ^ Nat.totient a) ^ 2 := by
                ring
              omega
            · have hk2 : 2 ≤ k := by omega
              have hmargin := margin_three_ge2 k hk2
              have hea : 1 ≤ Nat.totient a := Nat.totient_pos.mpr hapos
              have ht1 : 1 ≤ Nat.totient (3 ^ k) := Nat.totient_pos.mpr (pow_pos (by norm_num) k)
              have hstep := margin_absorb hmargin ht1 hb hea
              have heq2 : 2 * (3 ^ k * a) = 3 ^ k * (2 * a) := by ring
              rw [heq2]
              exact hstep
      · have hp5 : 5 ≤ p := by
          have h2 := hp.two_le
          obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
          omega
        have hc1 : 1 ≤ p ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne')
        have hcp5 : 5 ≤ p ^ k := le_trans hp5 (Nat.le_self_pow (by omega) p)
        refine ⟨?_, ?_⟩
        · -- clause A
          intro hn6
          rw [htot]
          by_cases ha1 : a = 1
          · subst ha1
            simp only [mul_one]
            simpa using prime_pow_le_two_pow_totient hp k hk
          · by_cases ha6 : a = 6
            · subst ha6
              have hmargin := margin_ge5 hp hp5 k hk
              have ht6 : Nat.totient 6 = 2 := by decide
              rw [ht6]
              have heq : (2:ℕ) ^ (Nat.totient (p ^ k) * 2)
                  = 2 ^ Nat.totient (p ^ k) * 2 ^ Nat.totient (p ^ k) := by
                rw [pow_mul]; ring
              rw [heq]
              have h1 : p ^ k * 6 ≤ p ^ k * (2 * p ^ k) := by
                apply Nat.mul_le_mul_left; omega
              have h2 : p ^ k * (2 * p ^ k) ≤ 2 ^ Nat.totient (p ^ k) * 2 ^ Nat.totient (p ^ k) := by
                calc p ^ k * (2 * p ^ k) = (2 * p ^ k) * p ^ k := by ring
                  _ ≤ (2 * p ^ k) * (2 * p ^ k) := Nat.mul_le_mul_left _ (by omega)
                  _ ≤ 2 ^ Nat.totient (p ^ k) * 2 ^ Nat.totient (p ^ k) :=
                    Nat.mul_le_mul hmargin hmargin
              omega
            · have hea : 1 ≤ Nat.totient a := Nat.totient_pos.mpr hapos
              have ht1 : 1 ≤ Nat.totient (p ^ k) := Nat.totient_pos.mpr (pow_pos hp.pos k)
              have hXa : a ≤ 2 ^ Nat.totient a := ihA ha6
              exact margin_absorb (margin_ge5 hp hp5 k hk) ht1 hXa hea
        · -- clause B
          rintro ⟨hoddn, hne1, hne3⟩
          have haodd : Odd a := (Nat.odd_mul.mp hoddn).2
          rw [htot]
          by_cases ha1 : a = 1
          · subst ha1
            simp only [mul_one, Nat.totient_one] at hne1 hne3 ⊢
            exact margin_ge5 hp hp5 k hk
          · by_cases ha3 : a = 3
            · subst ha3
              have hmargin := margin_ge5 hp hp5 k hk
              have ht3 : Nat.totient 3 = 2 := by decide
              rw [ht3]
              have heq : (2:ℕ) ^ (Nat.totient (p ^ k) * 2)
                  = 2 ^ Nat.totient (p ^ k) * 2 ^ Nat.totient (p ^ k) := by
                rw [pow_mul]; ring
              rw [heq]
              have h1 : 2 * (p ^ k * 3) ≤ p ^ k * (2 * p ^ k) := by
                have : 2 * (p ^ k * 3) = p ^ k * 6 := by ring
                rw [this]
                apply Nat.mul_le_mul_left; omega
              have h2 : p ^ k * (2 * p ^ k) ≤ 2 ^ Nat.totient (p ^ k) * 2 ^ Nat.totient (p ^ k) := by
                calc p ^ k * (2 * p ^ k) = (2 * p ^ k) * p ^ k := by ring
                  _ ≤ (2 * p ^ k) * (2 * p ^ k) := Nat.mul_le_mul_left _ (by omega)
                  _ ≤ 2 ^ Nat.totient (p ^ k) * 2 ^ Nat.totient (p ^ k) :=
                    Nat.mul_le_mul hmargin hmargin
              omega
            · have hb := ihB ⟨haodd, ha1, ha3⟩
              have hea : 1 ≤ Nat.totient a := Nat.totient_pos.mpr hapos
              have ht1 : 1 ≤ Nat.totient (p ^ k) := Nat.totient_pos.mpr (pow_pos hp.pos k)
              have hstep := margin_absorb (margin_ge5 hp hp5 k hk) ht1 hb hea
              have heq2 : 2 * (p ^ k * a) = p ^ k * (2 * a) := by ring
              rw [heq2]
              exact hstep

/-! ### The closure theorem needed by `ZsygmondyBaseOneCapstone` -/

/-- **The sharper totient-growth bound for `a = 3`.** For `n ≠ 6`, `n ≤ 2 ^ φ(n)`. This is
precisely the missing ingredient flagged in `ZsygmondyBaseOneCapstone`'s "Honest scope: why
`a = 3` is excluded" section: plugging this in as `hsize` (via `(a - 1) = 2` at `a = 3`) into
`ZsygmondyEvenPrime.primitive_prime_exists_of_size` closes the base `a = 3` case of Zsygmondy's
`b = 1` theorem, the one gap left in `zsygmondy_base_one`. -/
theorem totient_growth_two_ne_six (n : ℕ) (hn6 : n ≠ 6) : n ≤ 2 ^ Nat.totient n :=
  (totient_growth_two n).1 hn6

/-- **Totient-growth bridge, base `a = 3`.** For `n ≠ 6`, the size hypothesis
`n ≤ (a - 1) ^ φ(n)` holds at `a = 3` (i.e. `n ≤ 2 ^ φ(n)`), the exact analogue of
`ZsygmondyBaseOneCapstone.hsize_of_base_ge_four` for the boundary base `a = 3`. -/
theorem hsize_of_base_three (n : ℕ) (hn6 : n ≠ 6) :
    (n : ℤ) ≤ ((3 : ℤ) - 1) ^ Nat.totient n := by
  have h := totient_growth_two_ne_six n hn6
  have h3 : ((3:ℤ) - 1) = 2 := by norm_num
  rw [h3]
  exact_mod_cast h

/-- **Zsygmondy existence for base `a = 3`, `n ≠ 6`.** No size hypothesis needed: discharged
unconditionally by `hsize_of_base_three`. -/
theorem primitive_prime_exists_of_base_three_ne_six {n : ℕ} (hn : 1 < n) (hn6 : n ≠ 6)
    (hexc : ¬ (n = 2 ∧ ∃ t : ℕ, ((3:ℤ) + 1).natAbs = 2 ^ t)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (3:ℤ) ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ (3:ℤ) ^ m - 1 :=
  primitive_prime_exists_of_size hn (by norm_num) (hsize_of_base_three n hn6) hexc

/-- **Zsygmondy existence for base `a = 3` — FULLY CLOSED, no `n = 6` exclusion.**
For every `n ≥ 2`, `3 ^ n - 1` has a primitive prime divisor, except the single classical
`n = 2` carve-out (`a + 1 = 4` is a power of two). The residual `n = 6` gap flagged in
`ZsygmondyBaseOneCapstone`'s "Honest scope" section is patched here by the explicit witness
`ZsygmondyBaseOneCapstone.primitive_prime_exists_three_six` (`p = 7`). -/
theorem primitive_prime_exists_of_base_three {n : ℕ} (hn : 1 < n)
    (hexc : ¬ (n = 2 ∧ ∃ t : ℕ, ((3:ℤ) + 1).natAbs = 2 ^ t)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (3:ℤ) ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ (3:ℤ) ^ m - 1 := by
  by_cases hn6 : n = 6
  · subst hn6
    exact ZsygmondyBaseOneCapstone.primitive_prime_exists_three_six
  · exact primitive_prime_exists_of_base_three_ne_six hn hn6 hexc

/-- **Zsygmondy's theorem, `b = 1` case — FULLY CLOSED for every base `a ≥ 2`.**
For every integer `a ≥ 2` and every `n ≥ 2`, `a ^ n - 1` has a *primitive* prime divisor,
EXCEPT the two classical exceptional configurations `(n, a) = (2, a)` with `a + 1` a power of
two, and `(n, a) = (6, 2)`. This extends `ZsygmondyBaseOneCapstone.zsygmondy_base_one`
(previously `a = 2 ∨ a ≥ 4` only) to ALL bases `a ≥ 2`, closing the residual `a = 3` gap via
`primitive_prime_exists_of_base_three` above. -/
theorem zsygmondy_base_one_full {n : ℕ} (hn : 1 < n) {a : ℤ} (ha : 2 ≤ a)
    (hexc2 : ¬ (n = 2 ∧ ∃ t : ℕ, (a + 1).natAbs = 2 ^ t))
    (hexc6 : ¬ (n = 6 ∧ a = 2)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 := by
  have htri : a = 2 ∨ a = 3 ∨ 4 ≤ a := by omega
  rcases htri with ha2 | ha3 | ha4
  · exact ZsygmondyBaseOneCapstone.zsygmondy_base_one hn (Or.inl ha2) hexc2 hexc6
  · subst ha3
    exact primitive_prime_exists_of_base_three hn hexc2
  · exact ZsygmondyBaseOneCapstone.primitive_prime_exists_of_base_ge_four hn ha4 hexc2

end ZsygmondyBaseThree
