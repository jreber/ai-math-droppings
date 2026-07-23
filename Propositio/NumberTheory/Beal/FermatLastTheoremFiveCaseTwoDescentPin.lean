import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwoUnitPin
import Mathlib.Tactic

/-!
# FLT-5 Case II — wiring the extraction to the unit-exponent pin (`5 ∣ n`)

`FermatLastTheoremFiveCaseTwoExtraction.caseTwoFactorL_extraction` decomposes the concrete
Case-II factor as `caseTwoFactorL x y = √5ᴷ · β` with `β = ±φⁿ · d⁵`, and
`FermatLastTheoremFiveCaseTwoUnitPin.five_dvd_exponent_of_five_dvd_b` pins the exponent: for
`β = ±φⁿ·d⁵` with `√5 ∤ d`, `5 ∣ β.b ⟹ 5 ∣ n`. The prior session left the exact remaining gap
as: (1) `caseTwoFactorL_extraction`'s public statement does not expose `K`, `√5 ∤ β`, or `√5 ∤ d`;
(2) the two branches `K = 1` and `K = 5n+4` need the `5 ∣ β.b` hypothesis supplied from a genuine
solution, "clean only for `K = 1`".

This file closes exactly that gap, with a cleaner-than-expected resolution of the branch problem:

## The branch problem dissolves — `K` is forced to be `1`

The prior scoping worried the `K = 5n+4` branch would need "a different treatment". It does not
arise at all: **for any genuine Case-II solution the extraction exponent `K` must equal `1`.** The
`√5`-antisymmetric ("imaginary") part of the concrete factor is the source:

* `caseTwoFactorL x y − conj (caseTwoFactorL x y) = ofInt (x²+y²) · √5` (`sub_conj`, since the
  `φ`-coordinate of the factor is `x²+y²`), and `5 ∤ (x²+y²)` for a Case-II solution
  (`not_five_dvd_sq_add_sq`: `5 ∣ x+y` with `IsCoprime x y` rules out `5 ∣ x²+y²`). Hence the
  `√5`-valuation of the difference is **exactly `1`** (`√5 ∣` it but `√5² ∤` it).
* From `caseTwoFactorL = √5ᴷ · β` and `conj √5 = −√5`, `√5ᴷ ∣ (caseTwoFactorL − conj caseTwoFactorL)`.
  If `K ≥ 2` this gives `√5² ∣` the difference — contradiction. With `1 ≤ K` (from
  `case2_Phi_eq_five_pow_mul_fifth`), `K = 1`.

So the `K = 5n+4` "branch" is arithmetically impossible: the finer `√5`-adic structure kills it.

## Main results (proved, axiom-clean, no `sorry`)

* `not_five_dvd_sq_add_sq` — `IsCoprime x y`, `5 ∣ x+y ⟹ 5 ∤ x²+y²`.
* `caseTwoFactorL_extraction_strong` — the extraction, strengthened to expose `1 ≤ K`, `√5 ∤ β`
  and `√5 ∤ d` (the data the pin consumes), re-derived on the same public building blocks.
* `caseTwoFactorL_K_eq_one` — **the branch collapse**: `K = 1` for any genuine solution.
* `caseTwoFactorL_beta_b_five_dvd` — in the `K = 1` form `caseTwoFactorL = √5·β`, the trace
  `caseTwoFactorL + conj caseTwoFactorL = ofInt(−(x+y)²)` gives `5·β.b = −(x+y)²`, and `5 ∣ (x+y)`
  makes the RHS divisible by `25`, forcing `5 ∣ β.b`.
* `five_dvd_extraction_exponent` — **the unit-exponent pin, wired to a genuine solution**: for any
  Case-II solution, `caseTwoFactorL x y = √5·β` with `β = ±φⁿ·d⁵`, `√5 ∤ d` and `5 ∣ n`.
* `caseTwoFactorL_eq_pm_sqrt5_mul_fifth` — **capstone**: since `5 ∣ n`, the unit `±φⁿ` is itself
  `±` a fifth power, so `caseTwoFactorL x y = ±(√5 · γ⁵)` for `γ = φ^(n/5)·d ∈ ℤ[φ]` — the concrete
  Case-II factor is `±√5` times a perfect fifth power.

## What this does NOT do (honest scope note)

This fully lands the unit-pin program (both extraction branches resolved) and the `±√5·γ⁵`
factorization of the concrete factor. It does **not** assemble the final infinite descent —
reading a strictly smaller Case-II solution off `caseTwoFactorL = ±√5·γ⁵` (relating `γ`'s
coordinates back to a smaller Fermat-type triple and closing a well-founded recursion) is the
remaining classical content, not attempted here.

**No `sorry`, no project axiom** in what follows.
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne
open GoldenInt

/-! ## `5 ∣ x+y` for a solution, and `5 ∤ x²+y²` -/

/-- **`5 ∣ (x+y)`** for a Case-II solution, via the Frobenius/"freshman's dream" reduction
`x⁵+y⁵ ≡ x+y (mod 5)` and `5 ∣ z`. -/
theorem five_dvd_add_of_solution {x y z : ℤ}
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) : (5 : ℤ) ∣ (x + y) := by
  have hcast := cast_add_eq_cast_of_pow_five_eq heq
  have hz_zero : (z : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mpr h5z
  have hxy0 : ((x + y : ℤ) : ZMod 5) = 0 := by rw [hcast, hz_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 5).mp hxy0

/-- **`5 ∤ (x²+y²)`.** For coprime `x, y` with `5 ∣ x+y`: if `5 ∣ x²+y²` then, since
`2xy = (x+y)² − (x²+y²)`, `5 ∣ 2xy`, so (prime, `5 ∤ 2`) `5 ∣ xy`, so `5 ∣ x` or `5 ∣ y`; either
way `5 ∣ x+y` forces `5` to divide *both*, contradicting coprimality. -/
theorem not_five_dvd_sq_add_sq {x y : ℤ} (hxy : IsCoprime x y) (h5xy : (5 : ℤ) ∣ (x + y)) :
    ¬ (5 : ℤ) ∣ (x ^ 2 + y ^ 2) := by
  intro h5s
  have hp5 : Prime (5 : ℤ) := by norm_num
  have h5xy2 : (5 : ℤ) ∣ (x + y) ^ 2 := by rw [sq]; exact h5xy.mul_right (x + y)
  have h52xy : (5 : ℤ) ∣ 2 * (x * y) := by
    have e : 2 * (x * y) = (x + y) ^ 2 - (x ^ 2 + y ^ 2) := by ring
    rw [e]; exact dvd_sub h5xy2 h5s
  have h5xyprod : (5 : ℤ) ∣ x * y := by
    rcases hp5.dvd_mul.mp h52xy with h2 | h
    · norm_num at h2
    · exact h
  rcases hp5.dvd_mul.mp h5xyprod with h5x | h5y
  · have h5y : (5 : ℤ) ∣ y := by
      have e : y = (x + y) - x := by ring
      rw [e]; exact dvd_sub h5xy h5x
    obtain ⟨u, v, huv⟩ := hxy
    have : (5 : ℤ) ∣ 1 := by rw [← huv]; exact dvd_add (h5x.mul_left u) (h5y.mul_left v)
    norm_num at this
  · have h5x : (5 : ℤ) ∣ x := by
      have e : x = (x + y) - y := by ring
      rw [e]; exact dvd_sub h5xy h5y
    obtain ⟨u, v, huv⟩ := hxy
    have : (5 : ℤ) ∣ 1 := by rw [← huv]; exact dvd_add (h5x.mul_left u) (h5y.mul_left v)
    norm_num at this

/-! ## The extraction, strengthened to expose `1 ≤ K`, `√5 ∤ β`, `√5 ∤ d` -/

/-- **Strengthened extraction.** Identical to `caseTwoFactorL_extraction`, but additionally exposes
`1 ≤ K`, `√5 ∤ β` (the fully `√5`-peeled factor) and `√5 ∤ d` (the fifth-power base) — exactly the
data the branch-collapse and the unit-exponent pin consume. Re-derived on the same public building
blocks (`case2_Phi_eq_five_pow_mul_fifth`, `exists_sqrt5_pow_decomp_of_norm_natAbs`,
`caseTwoFactorL_peel_coprime_conj`, `pm_phiZpow_mul_pow_of_mul_conj_eq_pow`). -/
theorem caseTwoFactorL_extraction_strong {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (K : ℕ) (n : ℤ) (β d : GoldenInt),
      caseTwoFactorL x y = sqrt5 ^ K * β ∧
      1 ≤ K ∧
      ¬ sqrt5 ∣ β ∧
      ¬ sqrt5 ∣ d ∧
      (β = phiZpow n * d ^ 5 ∨ β = -(phiZpow n * d ^ 5)) := by
  obtain ⟨K, e, hK, hPhi, h5e⟩ := case2_Phi_eq_five_pow_mul_fifth hxy hz0 heq h5z
  have hΦne : (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) ≠ 0 := by
    rw [hPhi]
    have hene : e ≠ 0 := fun h => h5e (h ▸ dvd_zero 5)
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hene)
  have hLne : caseTwoFactorL x y ≠ 0 := by
    intro h
    apply hΦne
    have := norm_caseTwoFactorL x y
    rw [h, norm_zero] at this
    linarith [this]
  have hnormL : norm (caseTwoFactorL x y) = -(5 ^ K * e ^ 5) := by
    rw [norm_caseTwoFactorL, hPhi]
  have h5t : ¬ 5 ∣ (e ^ 5).natAbs := by
    rw [Int.natAbs_pow]
    intro h
    have : (5 : ℕ).Prime := by norm_num
    have h5en : 5 ∣ e.natAbs := this.dvd_of_dvd_pow h
    exact h5e (Int.natAbs_dvd_natAbs.mp h5en)
  have hnat : (norm (caseTwoFactorL x y)).natAbs = 5 ^ K * (e ^ 5).natAbs := by
    rw [hnormL, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  obtain ⟨β, hβ, hnd, hnβt⟩ :=
    exists_sqrt5_pow_decomp_of_norm_natAbs hLne h5t hnat
  have hnormβ : norm β = e ^ 5 ∨ norm β = -(e ^ 5) := by
    have : (norm β).natAbs = (e ^ 5).natAbs := hnβt
    exact Int.natAbs_eq_natAbs_iff.mp this
  have hcop : IsCoprime β (conj β) := caseTwoFactorL_peel_coprime_conj K hxy heq h5z hβ hnd
  obtain ⟨n, d, hd⟩ := pm_phiZpow_mul_pow_of_mul_conj_eq_pow (by decide : Odd 5) hcop hnormβ
  -- `√5 ∤ d`: else `√5 ∣ d⁵ ∣ ±(φⁿ·d⁵) = β`, contradicting `√5 ∤ β`.
  have hnd_d : ¬ sqrt5 ∣ d := by
    intro hdvd
    apply hnd
    have h5div : sqrt5 ∣ d ^ 5 := dvd_pow hdvd (by norm_num)
    have hdvdβ : sqrt5 ∣ phiZpow n * d ^ 5 := h5div.mul_left _
    rcases hd with h | h
    · rw [h]; exact hdvdβ
    · rw [h]; exact (dvd_neg).mpr hdvdβ
  exact ⟨K, n, β, d, hβ, hK, hnd, hnd_d, hd⟩

/-! ## The branch collapse: `K = 1` -/

/-- **`K = 1` for any genuine Case-II solution.** The `√5`-antisymmetric part
`caseTwoFactorL − conj caseTwoFactorL = ofInt(x²+y²)·√5` has `√5`-valuation exactly `1`
(`5 ∤ x²+y²`), yet `caseTwoFactorL = √5ᴷ·β` forces `√5ᴷ ∣` that difference; `K ≥ 2` would give
`√5² ∣` it — impossible. With `1 ≤ K`, `K = 1`. This shows the `K = 5n+4` extraction branch is
arithmetically impossible. -/
theorem caseTwoFactorL_K_eq_one {x y z : ℤ}
    (hxy : IsCoprime x y)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z)
    {K : ℕ} {β : GoldenInt}
    (hβ : caseTwoFactorL x y = sqrt5 ^ K * β) (hK : 1 ≤ K) : K = 1 := by
  have h5xy : (5 : ℤ) ∣ (x + y) := five_dvd_add_of_solution heq h5z
  have hns : ¬ (5 : ℤ) ∣ (x ^ 2 + y ^ 2) := not_five_dvd_sq_add_sq hxy h5xy
  -- The `√5`-antisymmetric part.
  have hdiff : caseTwoFactorL x y - conj (caseTwoFactorL x y) = ofInt (x ^ 2 + y ^ 2) * sqrt5 := by
    rw [sub_conj, b_caseTwoFactorL]
  -- `√5ᴷ ∣ caseTwoFactorL` and `√5ᴷ ∣ conj caseTwoFactorL`, hence `√5ᴷ ∣` their difference.
  have hdvdL : sqrt5 ^ K ∣ caseTwoFactorL x y := ⟨β, hβ⟩
  have hcform : conj (caseTwoFactorL x y) = (-sqrt5) ^ K * conj β := by
    rw [hβ, conj_mul, conj_pow, conj_sqrt5]
  have hdvd_neg : sqrt5 ^ K ∣ (-sqrt5) ^ K := by
    rw [neg_pow]; exact dvd_mul_left _ _
  have hdvdcL : sqrt5 ^ K ∣ conj (caseTwoFactorL x y) := by
    rw [hcform]; exact hdvd_neg.mul_right _
  have hdvdK : sqrt5 ^ K ∣ (caseTwoFactorL x y - conj (caseTwoFactorL x y)) := dvd_sub hdvdL hdvdcL
  -- Suppose `K ≠ 1`; then `K ≥ 2`, so `√5² ∣` the difference — contradiction.
  by_contra hKne
  have hK2 : 2 ≤ K := by omega
  have hsq_dvd : sqrt5 * sqrt5 ∣ (caseTwoFactorL x y - conj (caseTwoFactorL x y)) := by
    have h1 : sqrt5 ^ 2 ∣ sqrt5 ^ K := pow_dvd_pow sqrt5 hK2
    rw [sq] at h1
    exact h1.trans hdvdK
  rw [hdiff] at hsq_dvd
  obtain ⟨c, hc⟩ := hsq_dvd
  -- Cancel one `√5`: `ofInt(x²+y²) = √5·c`, so `√5 ∣ ofInt(x²+y²)`.
  have key : sqrt5 * ofInt (x ^ 2 + y ^ 2) = sqrt5 * (sqrt5 * c) := by
    rw [mul_comm sqrt5 (ofInt (x ^ 2 + y ^ 2)), hc]; ring
  have hcancel : ofInt (x ^ 2 + y ^ 2) = sqrt5 * c := mul_left_cancel₀ sqrt5_ne_zero key
  have hsqrt5_dvd : sqrt5 ∣ ofInt (x ^ 2 + y ^ 2) := ⟨c, hcancel⟩
  rw [sqrt5_dvd_iff_five_dvd_norm, norm_ofInt] at hsqrt5_dvd
  exact hns (Int.Prime.dvd_pow' (by norm_num) hsqrt5_dvd)

/-! ## `5 ∣ β.b` in the `K = 1` form -/

/-- **`5 ∣ β.b`** for the `K = 1` decomposition `caseTwoFactorL x y = √5·β`. The trace
`caseTwoFactorL + conj caseTwoFactorL = ofInt(−(x+y)²)` (`caseTwoFactorL_add_conj`) becomes
`√5·β − √5·conj β = √5(β − conj β) = ofInt(5·β.b)` (`conj √5 = −√5`, `sub_conj`, `√5² = 5`); so
`5·β.b = −(x+y)²`, and `5 ∣ (x+y)` makes `25 ∣ (x+y)²`, forcing `5 ∣ β.b`. -/
theorem caseTwoFactorL_beta_b_five_dvd {x y z : ℤ}
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z)
    {β : GoldenInt} (hβ : caseTwoFactorL x y = sqrt5 * β) : (5 : ℤ) ∣ β.b := by
  have h5xy : (5 : ℤ) ∣ (x + y) := five_dvd_add_of_solution heq h5z
  have hcL : conj (caseTwoFactorL x y) = -(sqrt5 * conj β) := by
    rw [hβ, conj_mul, conj_sqrt5]; ring
  have hsum : caseTwoFactorL x y + conj (caseTwoFactorL x y) = ofInt (5 * β.b) := by
    rw [hcL, hβ]
    have step1 : sqrt5 * β + -(sqrt5 * conj β) = sqrt5 * (β - conj β) := by ring
    rw [step1, sub_conj]
    rw [show sqrt5 * (ofInt β.b * sqrt5) = ofInt β.b * (sqrt5 * sqrt5) from by ring,
      sqrt5_sq, ← ofInt_mul]
    congr 1; ring
  have heqInt : 5 * β.b = -(x + y) ^ 2 := by
    have h := caseTwoFactorL_add_conj x y
    rw [hsum] at h
    have h2 := congrArg GoldenInt.a h
    simpa using h2
  -- `25 ∣ (x+y)²`, hence `5·5 ∣ 5·β.b`, hence `5 ∣ β.b`.
  have h25 : (25 : ℤ) ∣ (x + y) ^ 2 := by
    obtain ⟨w, hw⟩ := h5xy
    exact ⟨w ^ 2, by rw [hw]; ring⟩
  have h255 : (25 : ℤ) ∣ 5 * β.b := by rw [heqInt]; exact (dvd_neg).mpr h25
  have hfin : (5 : ℤ) * 5 ∣ 5 * β.b := by
    rwa [show (25 : ℤ) = 5 * 5 from by norm_num] at h255
  exact (mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0)).mp hfin

/-! ## The unit-exponent pin, wired to a genuine solution -/

/-- **The unit-exponent pin.** For any Case-II solution (coprime `x, y`, `x⁵+y⁵ = z⁵`, `z ≠ 0`,
`5 ∣ z`), the concrete factor satisfies `caseTwoFactorL x y = √5·β` with `β = ±φⁿ·d⁵`, `√5 ∤ d`,
and `5 ∣ n`. Assembles the branch collapse (`K = 1`), the trace divisibility `5 ∣ β.b`, and the
decoupled pin `five_dvd_exponent_of_five_dvd_b`. -/
theorem five_dvd_extraction_exponent {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (n : ℤ) (β d : GoldenInt),
      caseTwoFactorL x y = sqrt5 * β ∧
      ¬ sqrt5 ∣ d ∧
      (β = phiZpow n * d ^ 5 ∨ β = -(phiZpow n * d ^ 5)) ∧
      (5 : ℤ) ∣ n := by
  obtain ⟨K, n, β, d, hβ, hK, hndβ, hndd, hdform⟩ :=
    caseTwoFactorL_extraction_strong hxy hz0 heq h5z
  have hK1 : K = 1 := caseTwoFactorL_K_eq_one hxy heq h5z hβ hK
  subst hK1
  rw [pow_one] at hβ
  have hbb : (5 : ℤ) ∣ β.b := caseTwoFactorL_beta_b_five_dvd heq h5z hβ
  have h5n : (5 : ℤ) ∣ n := five_dvd_exponent_of_five_dvd_b hndd hdform hbb
  exact ⟨n, β, d, hβ, hndd, hdform, h5n⟩

/-! ## Capstone: `caseTwoFactorL = ±(√5 · γ⁵)` -/

/-- **`φ^(5m) = (φᵐ)⁵`** in `ℤ[φ]`, for all `m : ℤ`. Transported through the real embedding
(`toReal (φⁿ) = goldenRatio ^ n`, `zpow_mul`) and back via `toReal_injective`. -/
theorem phiZpow_five_mul (m : ℤ) : phiZpow (5 * m) = (phiZpow m) ^ 5 := by
  apply toReal_injective
  rw [toReal_phiZpow, toReal_pow, toReal_phiZpow, mul_comm (5 : ℤ) m, zpow_mul]
  norm_cast

/-- **Capstone — the concrete Case-II factor is `±√5` times a perfect fifth power.** For any
Case-II solution, `caseTwoFactorL x y = √5·γ⁵` or `= −(√5·γ⁵)` for `γ = φ^(n/5)·d ∈ ℤ[φ]`. Immediate
from `five_dvd_extraction_exponent` (`5 ∣ n`, so `φⁿ = (φ^(n/5))⁵` by `phiZpow_five_mul`, hence
`±φⁿ·d⁵ = ±(φ^(n/5)·d)⁵`). This is the full "unit × fifth power" pin the Legendre descent consumes. -/
theorem caseTwoFactorL_eq_pm_sqrt5_mul_fifth {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ γ : GoldenInt,
      caseTwoFactorL x y = sqrt5 * γ ^ 5 ∨ caseTwoFactorL x y = -(sqrt5 * γ ^ 5) := by
  obtain ⟨n, β, d, hβ, hndd, hdform, h5n⟩ := five_dvd_extraction_exponent hxy hz0 heq h5z
  obtain ⟨m, hm⟩ := h5n
  refine ⟨phiZpow m * d, ?_⟩
  have hpow : phiZpow n * d ^ 5 = (phiZpow m * d) ^ 5 := by
    rw [hm, phiZpow_five_mul, ← mul_pow]
  rcases hdform with h | h
  · left; rw [hβ, h, hpow]
  · right; rw [hβ, h, hpow, mul_neg]

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo GoldenInt
#print axioms not_five_dvd_sq_add_sq
#print axioms caseTwoFactorL_extraction_strong
#print axioms caseTwoFactorL_K_eq_one
#print axioms caseTwoFactorL_beta_b_five_dvd
#print axioms five_dvd_extraction_exponent
#print axioms phiZpow_five_mul
#print axioms caseTwoFactorL_eq_pm_sqrt5_mul_fifth
end AxiomCheck
