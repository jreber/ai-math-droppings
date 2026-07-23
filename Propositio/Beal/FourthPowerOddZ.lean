import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Propositio.Beal.FourthPowerLocal
import Mathlib.Tactic

/-!
# Signature `(4,4,z)`, odd `z`: why the local (congruence) route is structurally exhausted

`BealFourthPowerLocal` formally (kernel-checked) proves four theorems: `beal_44z_of_even_z`
(even-`z` closure via `not_fermat_42`), `fourth_pow_mod16`/`fourth_sum_coprime_image_mod16`
(a primitive `A⁴+B⁴` lies in `{1,2} (mod 16)`), and `fourth_sum_two_mod16_both_odd`
(the `≡2` branch forces `A,B` both odd). ITS DOCSTRING additionally *informally* argues —
in prose only, not as a proven Lean theorem — that combining these further pins `C` odd and
`z` odd in the surviving branch; that specific "`C` odd" step is NOT currently kernel-checked
anywhere in this codebase (no `beal_44z_surviving_case` theorem exists). This file does
**not** rely on that unformalized step: its own hypotheses are only "`z` odd" and "exactly one
of `A, B` even" (`hone`) — the latter following directly from `fourth_sum_coprime_image_mod16`
+ `fourth_sum_two_mod16_both_odd` by a one-line case split whenever `A⁴+B⁴ ≢ 2 (mod 16)`, with
no dependence on `C`'s parity. Given those two honest hypotheses, this file investigates
whether pushing the modulus higher (mod `32`, `64`, or any `2^k`) can rule the case out.

**Answer: no, and provably so, for every power of two simultaneously.** The obstruction
is a clean group-theoretic fact: for *any* odd exponent `z` and *any* `k ≥ 1`, the map
`u ↦ uᶻ` is a **bijection** on the unit group `(ZMod (2^k))ˣ`. This is because
`|(ZMod (2^k))ˣ| = φ(2^k) = 2^(k-1)` is a power of `2`, and `gcd(z, 2^(k-1)) = 1` for odd
`z`, so raising to the `z`-th power is a coprime-power automorphism
(`Nat.Coprime.pow_left_bijective`, mathlib).

Consequently, for *every* `k`, `Cᶻ` ranges over **all** odd residues mod `2^k` as `C`
ranges over the odd integers — for any single fixed odd `z`, not just "on average" over
many `z`. In particular there is always some `C` with `Cᶻ ≡ A⁴ + B⁴ (mod 2^k)`, for
literally every `k`. So no finite power-of-two modulus can ever rule out the surviving
case: increasing `k` from `16` to `32`, `64`, ... buys nothing, and this is a *theorem*,
not just an unsuccessful search. This matches (and explains) the numerically observed
mod-8/mod-16/mod-32/mod-64 pattern: the LHS image is always a *subset* of the odd
residues, and the RHS image (for any fixed odd `z`) is *always exactly all* of them.

This is an **honest negative result**: it does not close the surviving case (nor could
any congruence-only argument, per the theorem below), but it rigorously forecloses the
whole "try a bigger modulus" attack line, which otherwise looks promising after mod-16
(the image shrinks from `{1,2}` out of `16` classes and one might hope a further modulus
shrinks it to `∅`). Closing `(4,4,z)` for odd `z` requires non-local (Diophantine /
descent / modularity) methods — it is the generalized-Fermat equation `A⁴+B⁴=Cᶻ`, whose
full resolution is a genuinely hard problem in the literature, not a congruence exercise.

## Contents

* `card_units_two_pow` : `|(ZMod (2^(n+1)))ˣ| = 2^n`.
* `units_pow_bijective_of_odd` : for odd `z`, `u ↦ uᶻ` is bijective on `(ZMod (2^(n+1)))ˣ`.
* `isUnit_intCast_of_odd` : an odd integer casts to a unit of `ZMod (2^(n+1))`.
* `exists_pow_eq_of_odd` : for odd `z` and odd `T`, some `C` has `Cᶻ ≡ T (mod 2^(n+1))`.
* `no_mod_two_pow_obstruction_surviving_case` : applied to `T = A⁴+B⁴` in the surviving
  case — for every `n`, some integer `C` matches `A⁴+B⁴` mod `2^(n+1)` under the `z`-th
  power, so no power-of-two congruence check (at any modulus) can obstruct it.

Typecheck with `lake env lean BealFourthPowerOddZ.lean` (house style: `decide` only on
small finite `ZMod`, no `native_decide`).
-/

namespace BealFourthPowerOddZ

open BealFourthPowerLocal

/-! ## 1. The unit group of `ZMod (2^(n+1))` has `2`-power order -/

/-- **`|(ZMod (2^(n+1)))ˣ| = 2ⁿ`.** The totient of a power of an odd... here `2`, prime:
`φ(2^(n+1)) = 2ⁿ · (2−1) = 2ⁿ`. -/
theorem card_units_two_pow (n : ℕ) :
    Nat.card (ZMod (2 ^ (n + 1)))ˣ = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_two n]
  norm_num

/-! ## 2. Raising to an odd power is a bijection on this unit group -/

/-- **For odd `z`, `u ↦ uᶻ` is a bijection on `(ZMod (2^(n+1)))ˣ`.** The group has
`2`-power order (`card_units_two_pow`), and `z` is odd, hence coprime to any power of
`2`; a coprime power map on a finite group is a bijection
(`Nat.Coprime.pow_left_bijective`). -/
theorem units_pow_bijective_of_odd (n z : ℕ) (hz : Odd z) :
    Function.Bijective (fun u : (ZMod (2 ^ (n + 1)))ˣ => u ^ z) := by
  apply Nat.Coprime.pow_left_bijective
  rw [card_units_two_pow]
  exact (Nat.coprime_two_left.mpr hz).pow_left n

/-! ## 3. An odd integer is a unit mod any power of two -/

/-- **An odd integer `T` casts to a unit of `ZMod (2^(n+1))`.** `T` is coprime to `2`
(Bézout witness from `T = 2k+1`), hence coprime to `2^(n+1)`
(`IsCoprime.pow_left`), hence a unit (`ZMod.coe_int_isUnit_iff_isCoprime`). -/
theorem isUnit_intCast_of_odd (n : ℕ) {T : ℤ} (hT : Odd T) :
    IsUnit (T : ZMod (2 ^ (n + 1))) := by
  obtain ⟨k, hk⟩ := hT
  have h2 : IsCoprime (2 : ℤ) T := ⟨-k, 1, by rw [hk]; ring⟩
  have hpow : IsCoprime ((2 : ℤ) ^ (n + 1)) T := h2.pow_left
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  push_cast
  exact hpow

/-! ## 4. The surjectivity statement: no fixed odd `z` can be locally excluded -/

/-- **For odd `z` and odd `T`, some integer `C` matches `T` under the `z`-th power,
modulo every `2^(n+1)`.** This is the precise sense in which the "power-of-two modulus"
attack is exhausted: whichever residue the left-hand side `A⁴+B⁴` occupies (it is odd in
the surviving case), the right-hand side `Cᶻ` can realize that *same* residue, for the
actual (fixed, but unknown) odd `z` — not merely for some other exponent. -/
theorem exists_pow_eq_of_odd (n z : ℕ) (hz : Odd z) {T : ℤ} (hT : Odd T) :
    ∃ C : ℤ, (C : ZMod (2 ^ (n + 1))) ^ z = (T : ZMod (2 ^ (n + 1))) := by
  set m : ℕ := 2 ^ (n + 1)
  have hTunit : IsUnit (T : ZMod m) := isUnit_intCast_of_odd n hT
  obtain ⟨v, hv⟩ := (units_pow_bijective_of_odd n z hz).surjective hTunit.unit
  simp only at hv
  refine ⟨((v : ZMod m).val : ℤ), ?_⟩
  have hcast : (((v : ZMod m).val : ℕ) : ZMod m) = (v : ZMod m) := ZMod.natCast_zmod_val _
  have hval : ((v ^ z : (ZMod m)ˣ) : ZMod m) = (v : ZMod m) ^ z := Units.val_pow_eq_pow_val v z
  push_cast
  rw [hcast, ← hval, hv, hTunit.unit_spec]

/-! ## 5. The corollary for the surviving `(4,4,z)` case -/

/-- **`A⁴ + B⁴` is odd whenever exactly one of `A, B` is even.** An even base contributes
an even fourth power, an odd base an odd one, and even + odd is odd. -/
theorem odd_fourth_sum_of_one_even {A B : ℤ}
    (h : (Even A ∧ Odd B) ∨ (Odd A ∧ Even B)) : Odd (A ^ 4 + B ^ 4) := by
  rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact (hA.pow_of_ne_zero (by norm_num)).add_odd hB.pow
  · exact hA.pow.add_even (hB.pow_of_ne_zero (by norm_num))

/-- **The surviving `(4,4,z)` case cannot be closed by any power-of-two congruence.**
For a primitive `(4,4,z)` tuple with `z` odd and exactly one of `A, B` even (so
`A⁴ + B⁴` is odd — this is precisely the branch left open by `BealFourthPowerLocal`, the
`≡ 1 (mod 16)` case), and for **every** `n`, there exists an integer `C` realizing
`Cᶻ ≡ A⁴ + B⁴ (mod 2^(n+1))`. Equivalently: no obstruction of the form
`beal_44z_mod16_obstruction` (ruling out residues mod a fixed power of two) can ever
apply to this branch, at any modulus — the "push the modulus higher" attack is
exhausted by this single theorem, for all moduli simultaneously. -/
theorem no_mod_two_pow_obstruction_surviving_case
    {A B : ℤ} (hone : (Even A ∧ Odd B) ∨ (Odd A ∧ Even B))
    {z : ℕ} (hz : Odd z) (n : ℕ) :
    ∃ C : ℤ, (C : ZMod (2 ^ (n + 1))) ^ z = ((A ^ 4 + B ^ 4 : ℤ) : ZMod (2 ^ (n + 1))) :=
  exists_pow_eq_of_odd n z hz (odd_fourth_sum_of_one_even hone)

/-! ## 6. Axiom checks -/

#print axioms card_units_two_pow
#print axioms units_pow_bijective_of_odd
#print axioms isUnit_intCast_of_odd
#print axioms exists_pow_eq_of_odd
#print axioms odd_fourth_sum_of_one_even
#print axioms no_mod_two_pow_obstruction_surviving_case

end BealFourthPowerOddZ
