import Propositio.Beal.FermatLastTheoremFiveCaseOne
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Fermat's Last Theorem for exponent 5, Case I — completed

`FermatLastTheoremFiveCaseOne.lean` assembled the elementary factorization/gcd/coprimality
chain for the classical Case I argument (`5 ∤ ABC`) but stopped short of the final
contradiction, flagging as open: "a genetic/explicit construction of a strictly smaller
Case-I solution ... assembled via strong induction on `|ABC|`".

**That descent turns out not to be necessary.** Case I of Fermat's Last Theorem for `p = 5`
follows from **Sophie Germain's Theorem** applied directly with the auxiliary prime
`q = 11 = 2·5 + 1`, and Germain's own proof of her theorem (as she and Legendre gave it,
1823/1825) is a single finite chain of modular-arithmetic identities — **no infinite descent,
no strong induction on `|ABC|`, no construction of a smaller solution**. This is confirmed by
several independent sources consulted for this file:

* Wikipedia, "Proof of Fermat's Last Theorem for specific exponents": *"Case I for n = 5 can be
  proven immediately by Sophie Germain's theorem (1823) if the auxiliary prime θ = 11."*
* N. Donalds (UC Irvine, Math 180B lecture notes, *"Sophie Germain and Fermat's Last
  Theorem"*), which we follow directly: it proves case 1 of FLT for any *Germain prime* `p`
  (i.e. `q = 2p+1` prime) via one finite modular computation. For `p = 5`, `q = 11` is exactly
  such a prime, and the two hypotheses this proof needs are *precisely* the two facts already
  proved in `FermatLastTheoremFiveCaseOne.lean`: `sophie_germain_dvd_prod` (Germain's
  non-consecutivity conclusion mod 11) and `five_not_fifth_power_mod_eleven` (Germain's
  "`p` is not a `p`-th power mod `q`" condition).
* Laubenbacher–Pengelley, *"Voici ce que j'ai trouvé": Sophie Germain's grand plan to prove
  Fermat's Last Theorem* (2007), confirms the historical attribution and the precise statement
  of Sophie Germain's Theorem (their §1, "Sophie Germain's Theorem").

## What this file proves

`fermat_five_case_one` : for pairwise coprime integers `x, y, z` with `5 ∤ x`, `5 ∤ y`,
`5 ∤ z`, and `x^5 + y^5 = z^5`, we derive `False`. This is the **complete** Case I of FLT-5,
fully general over `ℤ` (no positivity needed beyond what pairwise coprimality already forces).
`fermatLastTheoremFive_caseOne` is the natural-number corollary: no positive pairwise-coprime
`A, B, C` with `5 ∤ ABC` satisfy `A^5 + B^5 = C^5`.

## Proof sketch (following the UC Irvine notes, specialized to `p = 5`, `q = 11`)

Assume `x^5 + y^5 = z^5`, pairwise coprime, `5 ∤ xyz`.

1. **Freshman's-dream trick.** Working mod 5: the Frobenius identity `(a+b)^5 = a^5+b^5`
   (`add_pow_char`) plus Fermat's little theorem `a^5 = a` (`ZMod.pow_card`) give
   `x + y ≡ z (mod 5)`. Since `5 ∤ z`, also `5 ∤ (x+y)` — no case split on `5 ∣ (x+y)` is
   needed.
2. **Coprime factorization** (from `FermatLastTheoremFiveCaseOne`): `x+y = d^5` and the
   quartic cofactor `= e^5`. By the same trick applied to `z^5 + (-y)^5 = x^5` and
   `z^5 + (-x)^5 = y^5` (both immediate rearrangements of the main equation), we similarly get
   `z - y = a^5` (cofactor `= α^5`) and `z - x = b^5`.
3. **The linear identity** `d^5 + a^5 - b^5 = (x+y) + (z-y) - (z-x) = 2x` is a ring identity.
4. Assuming (WLOG, handled by explicit case dispatch below) `11 ∣ x`: reducing step 3 mod 11
   and applying Sophie Germain's non-consecutivity fact (`sophie_germain_dvd_prod`) to
   `d^5 + a^5 + (-b)^5 ≡ 0 (mod 11)` shows `11` divides one of `d, a, b`. Coprimality rules out
   `d` and `b` (each would force `11 ∣ y` or `11 ∣ z`, contradicting pairwise coprimality with
   `x`), leaving `11 ∣ a`, i.e. `z ≡ y (mod 11)`.
5. **Final contradiction.** Reducing the cofactor identities mod 11 with `z ≡ y` and `x ≡ 0`
   gives `α^5 ≡ 5y^4` and `e^5 ≡ y^4` (mod 11). Since `11 ∤ y`, dividing gives
   `(α · e⁻¹)^5 ≡ 5 (mod 11)` — i.e. `5` **is** a fifth-power residue mod 11, directly
   contradicting `five_not_fifth_power_mod_eleven`.

The `11 ∣ y` and `11 ∣ z` branches of the WLOG are closed by re-applying the same core lemma
(`case1_core`) to permuted/negated triples: swapping `x ↔ y` for the `11 ∣ y` case, and
applying it to `(z, -x, y)` (since `z^5 + (-x)^5 = y^5` is the same equation shape with `z` now
playing the "divisible" role) for the `11 ∣ z` case.

**No `sorry`, no project axiom.** All ingredients are either proved in this file (the Frobenius
mod-5 trick and its consequences, the final mod-11 division-ring computation) or imported from
`FermatLastTheoremFiveCaseOne.lean`'s already-real lemmas (the factorization chain,
`sophie_germain_dvd_prod`, `five_not_fifth_power_mod_eleven`).
-/

namespace FermatLastTheoremFiveCaseOne

/-- **Freshman's-dream cast lemma.** `x + y ≡ z (mod 5)` whenever `x^5 + y^5 = z^5`: mod 5,
`(x+y)^5 = x^5+y^5` (Frobenius, `add_pow_char`) `= z^5` (the hypothesis), and Fermat's little
theorem (`ZMod.pow_card`) collapses both sides' fifth powers back to the base. -/
theorem cast_add_eq_cast_of_pow_five_eq {x y z : ℤ} (heq : x ^ 5 + y ^ 5 = z ^ 5) :
    ((x + y : ℤ) : ZMod 5) = (z : ZMod 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcast : (x : ZMod 5) ^ 5 + (y : ZMod 5) ^ 5 = (z : ZMod 5) ^ 5 := by
    have h := congrArg (fun n : ℤ => (n : ZMod 5)) heq
    push_cast at h
    exact h
  have hfrob : ((x : ZMod 5) + (y : ZMod 5)) ^ 5 = (x : ZMod 5) ^ 5 + (y : ZMod 5) ^ 5 :=
    add_pow_char (R := ZMod 5) (x : ZMod 5) (y : ZMod 5) 5
  have h1 : ((x : ZMod 5) + (y : ZMod 5)) ^ 5 = (x : ZMod 5) + (y : ZMod 5) :=
    ZMod.pow_card _
  have h2 : (z : ZMod 5) ^ 5 = (z : ZMod 5) := ZMod.pow_card _
  push_cast
  rw [← h1, hfrob, hcast, h2]

/-- If `x^5+y^5=z^5` and `5 ∤ z`, then `5 ∤ (x+y)`: immediate from
`cast_add_eq_cast_of_pow_five_eq`, avoiding a case split on `5 ∣ (x+y)` vs not. -/
theorem five_not_dvd_add_of_not_dvd_third {x y z : ℤ}
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : ¬ (5 : ℤ) ∣ z) : ¬ (5 : ℤ) ∣ (x + y) := by
  have hcast := cast_add_eq_cast_of_pow_five_eq heq
  intro hdvd
  apply h5z
  have hxy0 : ((x + y : ℤ) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 5).mpr hdvd
  have hz0 : (z : ZMod 5) = 0 := by rw [← hcast]; exact hxy0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mp hz0

/-- **Core Case-I argument** (single branch, `11 ∣ x`): given pairwise coprime `x, y, z` with
`5 ∤ x, y, z`, `x^5+y^5=z^5`, and `11 ∣ x`, derive `False`. This is Sophie Germain's Theorem
(via Legendre, 1823) specialized to `p = 5`, `q = 11`, following the finite modular-arithmetic
proof (no descent). -/
theorem case1_core {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (h5x : ¬ (5 : ℤ) ∣ x) (h5y : ¬ (5 : ℤ) ∣ y) (h5z : ¬ (5 : ℤ) ∣ z)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h11x : (11 : ℤ) ∣ x) : False := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  -- Step 1: 5 ∤ x+y, factor x+y = d^5, quartic(x,y) = e^5.
  have h5xy : ¬ (5 : ℤ) ∣ (x + y) := five_not_dvd_add_of_not_dvd_third heq h5z
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ := quintic_factors_eq_pow_of_coprime hxy h5xy heq
  -- Step 2: z - y factorization (from z^5 + (-y)^5 = x^5).
  have hzy_eq : z ^ 5 + (-y) ^ 5 = x ^ 5 := by linear_combination -heq
  have hcop_zy : IsCoprime z (-y) := hyz.symm.neg_right
  have h5zy : ¬ (5 : ℤ) ∣ (z + -y) := five_not_dvd_add_of_not_dvd_third hzy_eq h5x
  obtain ⟨⟨a, ha⟩, ⟨alpha, halpha⟩⟩ := quintic_factors_eq_pow_of_coprime hcop_zy h5zy hzy_eq
  -- Step 3: z - x factorization (from z^5 + (-x)^5 = y^5).
  have hzx_eq : z ^ 5 + (-x) ^ 5 = y ^ 5 := by linear_combination -heq
  have hcop_zx : IsCoprime z (-x) := hxz.symm.neg_right
  have h5zx : ¬ (5 : ℤ) ∣ (z + -x) := five_not_dvd_add_of_not_dvd_third hzx_eq h5y
  obtain ⟨⟨b, hb⟩, -⟩ := quintic_factors_eq_pow_of_coprime hcop_zx h5zx hzx_eq
  -- Step 4: the ring identity 2x = d^5 + a^5 - b^5.
  have hident : d ^ 5 + a ^ 5 - b ^ 5 = 2 * x := by linear_combination -hd - ha + hb
  -- Step 5: 11 | (d^5 + a^5 + (-b)^5), so (Sophie Germain) 11 divides one of d, a, -b.
  have h11_prod : (11 : ℤ) ∣ (d ^ 5 + a ^ 5 + (-b) ^ 5) := by
    have hnb : (-b) ^ 5 = -(b ^ 5) := Odd.neg_pow (by decide) b
    have heq2 : d ^ 5 + a ^ 5 + (-b) ^ 5 = 2 * x := by rw [hnb]; linear_combination hident
    rw [heq2]
    exact h11x.mul_left 2
  have hdab := sophie_germain_dvd_prod h11_prod
  -- Step 6: 11 ∤ y and 11 ∤ z (pairwise coprimality with x, which 11 divides).
  have h11not_unit : ¬ IsUnit (11 : ℤ) := by rw [Int.isUnit_iff]; norm_num
  have h11y_not : ¬ (11 : ℤ) ∣ y := fun h11y => h11not_unit (hxy.isUnit_of_dvd' h11x h11y)
  have h11z_not : ¬ (11 : ℤ) ∣ z := fun h11z => h11not_unit (hxz.isUnit_of_dvd' h11x h11z)
  -- Step 7: 11 ∤ d and 11 ∤ b, so 11 | a.
  have hd_not : ¬ (11 : ℤ) ∣ d := by
    intro h11d
    have h11d5 : (11 : ℤ) ∣ d ^ 5 := dvd_pow h11d (by norm_num)
    rw [← hd] at h11d5
    have h11y : (11 : ℤ) ∣ y := by
      have h := dvd_sub h11d5 h11x
      rwa [show x + y - x = y by ring] at h
    exact h11y_not h11y
  have hb_not : ¬ (11 : ℤ) ∣ b := by
    intro h11b
    have h11b5 : (11 : ℤ) ∣ b ^ 5 := dvd_pow h11b (by norm_num)
    rw [← hb] at h11b5
    have h11z : (11 : ℤ) ∣ z := by
      have h := dvd_add h11b5 h11x
      rwa [show z + -x + x = z by ring] at h
    exact h11z_not h11z
  have h11a : (11 : ℤ) ∣ a := by
    rcases hdab with h | h | h
    · exact absurd h hd_not
    · exact h
    · exact absurd (dvd_neg.mp h) hb_not
  -- Step 8: 11 | a ⟹ z ≡ y (mod 11).
  have h11zy : (11 : ℤ) ∣ (z - y) := by
    have h11a5 : (11 : ℤ) ∣ a ^ 5 := dvd_pow h11a (by norm_num)
    rw [← ha] at h11a5
    rwa [show z + -y = z - y by ring] at h11a5
  have hzy11 : (z : ZMod 11) = (y : ZMod 11) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - y) 11).mpr h11zy
    push_cast at h
    linear_combination h
  have hx11 : (x : ZMod 11) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x 11).mpr h11x
  -- Step 9: mod 11, alpha^5 = 5*y^4 and e^5 = y^4.
  have halpha11 : (alpha : ZMod 11) ^ 5 = 5 * (y : ZMod 11) ^ 4 := by
    have hc := congrArg (fun n : ℤ => (n : ZMod 11)) halpha
    push_cast at hc
    rw [← hc, hzy11]
    ring
  have he11 : (y : ZMod 11) ^ 4 = (e : ZMod 11) ^ 5 := by
    have hc := congrArg (fun n : ℤ => (n : ZMod 11)) he
    push_cast at hc
    rw [← hc, hx11]
    ring
  -- Step 10: y ≠ 0 mod 11 (from pairwise coprimality), hence e ≠ 0 mod 11.
  have hy11ne : (y : ZMod 11) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h11y_not
  have hy4ne : (y : ZMod 11) ^ 4 ≠ 0 := pow_ne_zero 4 hy11ne
  -- Step 11: w = alpha * e⁻¹ satisfies w^5 = 5 in ZMod 11 — contradicts Sophie Germain's
  -- second condition.
  set w : ZMod 11 := (alpha : ZMod 11) * (e : ZMod 11)⁻¹ with hw_def
  have hw5 : w ^ 5 = 5 := by
    have he5eq : (e : ZMod 11) ^ 5 = (y : ZMod 11) ^ 4 := he11.symm
    rw [hw_def, mul_pow, inv_pow, halpha11, he5eq, mul_assoc, mul_inv_cancel₀ hy4ne, mul_one]
  exact five_not_fifth_power_mod_eleven ⟨w, hw5⟩

/-- **Case I of Fermat's Last Theorem for exponent 5, complete.** For pairwise coprime
integers `x, y, z` with `5 ∤ x`, `5 ∤ y`, `5 ∤ z`, the equation `x^5 + y^5 = z^5` is impossible.
Dispatches on which of `x, y, z` is divisible by the auxiliary prime `11` (guaranteed by
`sophie_germain_dvd_prod`), reducing each branch to `case1_core` by symmetry (`x ↔ y` swap for
the `11 ∣ y` branch; the substitution `(x,y,z) ↦ (z,-x,y)` for the `11 ∣ z` branch, since
`z^5 + (-x)^5 = y^5` is the same equation shape with `z` now playing the "divisible" role). -/
theorem fermat_five_case_one {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (h5x : ¬ (5 : ℤ) ∣ x) (h5y : ¬ (5 : ℤ) ∣ y) (h5z : ¬ (5 : ℤ) ∣ z)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) : False := by
  have h0 : x ^ 5 + y ^ 5 + (-z) ^ 5 = 0 := by linear_combination heq
  have h11 : (11 : ℤ) ∣ x ∨ (11 : ℤ) ∣ y ∨ (11 : ℤ) ∣ (-z) := by
    apply sophie_germain_dvd_prod
    rw [h0]
    exact dvd_zero 11
  rcases h11 with h11x | h11y | h11z'
  · exact case1_core hxy hyz hxz h5x h5y h5z heq h11x
  · have heq' : y ^ 5 + x ^ 5 = z ^ 5 := by linear_combination heq
    exact case1_core hxy.symm hxz hyz h5y h5x h5z heq' h11y
  · have h11z : (11 : ℤ) ∣ z := dvd_neg.mp h11z'
    have heq'' : z ^ 5 + (-x) ^ 5 = y ^ 5 := by linear_combination -heq
    have hcop1 : IsCoprime z (-x) := hxz.symm.neg_right
    have hcop2 : IsCoprime (-x) y := hxy.neg_left
    have hcop3 : IsCoprime z y := hyz.symm
    have h5negx : ¬ (5 : ℤ) ∣ (-x) := by rw [dvd_neg]; exact h5x
    exact case1_core hcop1 hcop2 hcop3 h5z h5negx h5y heq'' h11z

/-- Natural-number form: no positive pairwise-coprime `A, B, C` with `5 ∤ ABC` satisfy
`A^5 + B^5 = C^5`. This is the standard statement of "Case I of FLT-5". -/
theorem fermatLastTheoremFive_caseOne {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hBC : Nat.Coprime B C) (hAC : Nat.Coprime A C)
    (h5A : ¬ 5 ∣ A) (h5B : ¬ 5 ∣ B) (h5C : ¬ 5 ∣ C) :
    A ^ 5 + B ^ 5 ≠ C ^ 5 := by
  intro heq
  have heqZ : (A : ℤ) ^ 5 + (B : ℤ) ^ 5 = (C : ℤ) ^ 5 := by exact_mod_cast heq
  refine fermat_five_case_one hAB.isCoprime hBC.isCoprime hAC.isCoprime ?_ ?_ ?_ heqZ
  · rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]; exact h5A
  · rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]; exact h5B
  · rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]; exact h5C

end FermatLastTheoremFiveCaseOne
