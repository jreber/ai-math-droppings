import Propositio.Beal.FermatLastTheoremFiveCaseTwoDescentRecombination
import Mathlib.Tactic

/-!
# FLT-5 Case II — primitivity of the pinned `γ` (`gcd(γ.a, γ.b) = 1`)

`FermatLastTheoremFiveCaseTwoDescentPin.caseTwoFactorL_eq_pm_sqrt5_mul_fifth` pins the Case-II
factor as `caseTwoFactorL x y = ±(√5·γ⁵)` for some `γ = p + qφ ∈ ℤ[φ]`, and
`FermatLastTheoremFiveCaseTwoDescentRecombination.caseTwo_descent_equation` reads it back to the
integer relation `(x+y)² = ±25·q·Q₄(p,q)`. The remaining descent needs `γ` to be **primitive**:
`IsCoprime γ.a γ.b` (equivalently `gcd(p,q) = 1`). This file supplies exactly that.

## The argument

The `√5`-peeled factor `β` (with `caseTwoFactorL = √5·β`, `β = ±γ⁵`) is coprime to its conjugate:
`caseTwoFactorL_peel_coprime_conj` gives `IsCoprime β (conj β)`. If a rational prime `p` divided
both `γ.a` and `γ.b`, then `ofInt p ∣ γ` in `ℤ[φ]`, hence `ofInt p ∣ γ⁵` and (since
`conj (ofInt p) = ofInt p` — a rational integer is self-conjugate) `ofInt p ∣ conj (γ⁵)`. As
`β = ±γ⁵`, `ofInt p` would then divide both `β` and `conj β`, forcing `IsUnit (ofInt p)`. But
`norm (ofInt p) = p²` and a unit has norm `±1`, while `p ≥ 2` — contradiction. Hence no rational
prime divides both coordinates, i.e. `gcd(γ.a, γ.b) = 1`.

## Main results (all sorry-free, axiom-clean)

* `coprime_a_b_of_pm_pow_conj` — the pure `ℤ[φ]` fact: if `β = ±γ⁵` and `IsCoprime β (conj β)`
  then `IsCoprime γ.a γ.b`.
* `caseTwo_gamma_coprime` — **headline**: for any genuine Case-II solution, the pinned `γ` in
  `caseTwoFactorL x y = ±(√5·γ⁵)` is primitive: `IsCoprime γ.a γ.b`.

**No `sorry`, no project axiom.**
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne GoldenInt

/-! ## `conj` on rational integers and on negatives -/

/-- A rational integer is self-conjugate: `conj (ofInt n) = ofInt n`. -/
theorem conj_ofInt (n : ℤ) : conj (ofInt n) = ofInt n := by
  ext <;> simp

/-- `conj` negates: `conj (-z) = -(conj z)`. -/
theorem conj_neg (z : GoldenInt) : conj (-z) = -(conj z) := by
  ext <;> simp only [a_conj, b_conj, a_neg, b_neg, neg_add]

/-! ## Divisibility of `γ` by a rational prime whose value divides both coordinates -/

/-- If a rational integer `c` divides both coordinates of `γ`, then `ofInt c ∣ γ` in `ℤ[φ]`. -/
theorem ofInt_dvd_of_dvd_coords {γ : GoldenInt} {c : ℤ}
    (ha : c ∣ γ.a) (hb : c ∣ γ.b) : ofInt c ∣ γ := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  refine ⟨⟨s, t⟩, ?_⟩
  ext
  · simp only [a_mul, a_ofInt, b_ofInt]; rw [hs]; ring
  · simp only [b_mul, a_ofInt, b_ofInt]; rw [ht]; ring

/-! ## Primitivity of `γ` from coprimality of `β = ±γ⁵` with its conjugate -/

/-- **The `ℤ[φ]` primitivity fact.** If `β = ±γ⁵` and `β` is coprime to its conjugate, then the
integer coordinates of `γ` are coprime. Any common rational prime `p` of `(γ.a, γ.b)` lifts to
`ofInt p ∣ γ`, hence divides `β = ±γ⁵` and `conj β = ±conj(γ⁵) = ±(conj γ)⁵`; coprimality makes
`ofInt p` a unit, impossible (`norm (ofInt p) = p² ≠ ±1` for `p ≥ 2`). -/
theorem coprime_a_b_of_pm_pow_conj {γ β : GoldenInt}
    (hβγ : β = γ ^ 5 ∨ β = -(γ ^ 5)) (hcop : IsCoprime β (conj β)) :
    IsCoprime γ.a γ.b := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨pn, hpn, hpndvd⟩ := Nat.exists_prime_and_dvd hne
  have hpprime : Prime ((pn : ℤ)) := Nat.prime_iff_prime_int.mp hpn
  -- `p := pn` divides both coordinates of `γ`.
  have hcast : ((pn : ℤ)) ∣ ((Int.gcd γ.a γ.b : ℤ)) := Int.natCast_dvd_natCast.mpr hpndvd
  have hpa : (pn : ℤ) ∣ γ.a := hcast.trans (Int.gcd_dvd_left γ.a γ.b)
  have hpb : (pn : ℤ) ∣ γ.b := hcast.trans (Int.gcd_dvd_right γ.a γ.b)
  -- lift to `ofInt p ∣ γ`.
  have hdvdγ : ofInt (pn : ℤ) ∣ γ := ofInt_dvd_of_dvd_coords hpa hpb
  -- `ofInt p ∣ γ⁵` and `ofInt p ∣ conj(γ⁵)`.
  have hp5 : ofInt (pn : ℤ) ∣ γ ^ 5 := hdvdγ.trans (dvd_pow_self γ (by norm_num : (5 : ℕ) ≠ 0))
  have hconjγ : ofInt (pn : ℤ) ∣ conj γ := by
    obtain ⟨w, hw⟩ := hdvdγ
    exact ⟨conj w, by rw [hw, conj_mul, conj_ofInt]⟩
  have hp5c : ofInt (pn : ℤ) ∣ conj (γ ^ 5) := by
    rw [conj_pow]; exact hconjγ.trans (dvd_pow_self (conj γ) (by norm_num : (5 : ℕ) ≠ 0))
  -- `ofInt p` divides `β` and `conj β`.
  have hpβ : ofInt (pn : ℤ) ∣ β := by
    rcases hβγ with h | h
    · rw [h]; exact hp5
    · rw [h]; exact (dvd_neg).mpr hp5
  have hpcβ : ofInt (pn : ℤ) ∣ conj β := by
    rcases hβγ with h | h
    · rw [h]; exact hp5c
    · rw [h, conj_neg]; exact (dvd_neg).mpr hp5c
  -- coprimality forces `ofInt p` to be a unit — impossible.
  have hunit : IsUnit (ofInt (pn : ℤ)) := hcop.isUnit_of_dvd' hpβ hpcβ
  have hn := (isUnit_iff_norm_eq_one (ofInt (pn : ℤ))).mp hunit
  rw [norm_ofInt] at hn
  have h2 : (2 : ℤ) ≤ (pn : ℤ) := by exact_mod_cast hpn.two_le
  rcases hn with h | h <;> nlinarith [h2]

/-! ## Headline: the pinned `γ` is primitive -/

/-- **`γ` is primitive.** For any genuine Case-II solution (`IsCoprime x y`, `x⁵+y⁵ = z⁵`, `z ≠ 0`,
`5 ∣ z`), there is `γ ∈ ℤ[φ]` with `caseTwoFactorL x y = ±(√5·γ⁵)` **and** `IsCoprime γ.a γ.b`.
Strengthens `caseTwoFactorL_eq_pm_sqrt5_mul_fifth` by exposing primitivity of `γ`, the property the
remaining Legendre descent on `w² = ±q·Q₄(p,q)` consumes. Re-derives the extraction directly (via
`caseTwoFactorL_extraction_strong`, `caseTwoFactorL_K_eq_one`, `caseTwoFactorL_peel_coprime_conj`,
`caseTwoFactorL_beta_b_five_dvd`, `five_dvd_exponent_of_five_dvd_b`) so the coprimality witness
`IsCoprime β (conj β)` — discarded by the bundled capstone — is available for `coprime_a_b_of_pm_pow_conj`. -/
theorem caseTwo_gamma_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ γ : GoldenInt,
      (caseTwoFactorL x y = sqrt5 * γ ^ 5 ∨ caseTwoFactorL x y = -(sqrt5 * γ ^ 5)) ∧
      IsCoprime γ.a γ.b := by
  obtain ⟨K, n, β, d, hβ, hK, hndβ, hndd, hdform⟩ :=
    caseTwoFactorL_extraction_strong hxy hz0 heq h5z
  have hK1 : K = 1 := caseTwoFactorL_K_eq_one hxy heq h5z hβ hK
  subst hK1
  -- coprimality of the peeled factor with its conjugate (uses `hβ : caseTwoFactorL = √5^1·β`).
  have hcop : IsCoprime β (conj β) := caseTwoFactorL_peel_coprime_conj 1 hxy heq h5z hβ hndβ
  rw [pow_one] at hβ
  -- pin the exponent `5 ∣ n`.
  have hbb : (5 : ℤ) ∣ β.b := caseTwoFactorL_beta_b_five_dvd heq h5z hβ
  have h5n : (5 : ℤ) ∣ n := five_dvd_exponent_of_five_dvd_b hndd hdform hbb
  obtain ⟨m, hm⟩ := h5n
  refine ⟨phiZpow m * d, ?_, ?_⟩
  · -- the `±√5·γ⁵` pin.
    have hpow : phiZpow n * d ^ 5 = (phiZpow m * d) ^ 5 := by
      rw [hm, phiZpow_five_mul, ← mul_pow]
    rcases hdform with h | h
    · left; rw [hβ, h, hpow]
    · right; rw [hβ, h, hpow, mul_neg]
  · -- primitivity via `β = ±(phiZpow m * d)⁵`.
    have hpow : phiZpow n * d ^ 5 = (phiZpow m * d) ^ 5 := by
      rw [hm, phiZpow_five_mul, ← mul_pow]
    have hβγ : β = (phiZpow m * d) ^ 5 ∨ β = -((phiZpow m * d) ^ 5) := by
      rw [← hpow]; exact hdform
    exact coprime_a_b_of_pm_pow_conj hβγ hcop

/-! ## Coprimality of `q` and the quartic cofactor `Q₄` -/

/-- **`gcd(q, Q₄) = 1`.** For coprime `p, q`, the second descent coordinate `q` is coprime to the
quartic cofactor `Q₄(p,q) = p⁴+2p³q+4p²q²+3pq³+q⁴`. Since `Q₄ = p⁴ + q·(2p³+4p²q+3pq²+q³) ≡ p⁴
(mod q)` and `IsCoprime p q ⟹ IsCoprime q (p⁴)`. This is the coprimality that (with `w² = ±q·Q₄`)
forces `q` and `Q₄` each to be `±` a square — the next descent step. -/
theorem coprime_q_Q4 {p q : ℤ} (hpq : IsCoprime p q) :
    IsCoprime q (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) := by
  have h1 : IsCoprime q (p ^ 4) := (hpq.symm).pow_right
  have hrw : p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4
      = p ^ 4 + q * (2 * p ^ 3 + 4 * p ^ 2 * q + 3 * p * q ^ 2 + q ^ 3) := by ring
  rw [hrw]
  exact h1.add_mul_left_right _

/-- **Descent equation with `q`–`Q₄` coprimality.** For any genuine Case-II solution, the descent
coordinates `(p, q) = (γ.a, γ.b)` satisfy the integer relation
`(x+y)² = ±25·q·Q₄(p,q)` **and** `IsCoprime q Q₄(p,q)`. Combines the primitivity of `γ`
(`caseTwo_gamma_coprime`), the descent equation (`descent_eq_of_pin_pos`/`neg`) and `coprime_q_Q4`.
This is the exact input the classical "peel the square" step consumes. -/
theorem caseTwo_descent_equation_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (p q : ℤ),
      ((x + y) ^ 2 = 25 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) ∨
       (x + y) ^ 2 =
         -(25 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4))) ∧
      IsCoprime q (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) := by
  obtain ⟨γ, hpin, hcop⟩ := caseTwo_gamma_coprime hxy hz0 heq h5z
  refine ⟨γ.a, γ.b, ?_, coprime_q_Q4 hcop⟩
  rcases hpin with h | h
  · exact Or.inr (descent_eq_of_pin_pos h)
  · exact Or.inl (descent_eq_of_pin_neg h)

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo GoldenInt
#print axioms conj_ofInt
#print axioms conj_neg
#print axioms ofInt_dvd_of_dvd_coords
#print axioms coprime_a_b_of_pm_pow_conj
#print axioms caseTwo_gamma_coprime
#print axioms coprime_q_Q4
#print axioms caseTwo_descent_equation_coprime
end AxiomCheck
