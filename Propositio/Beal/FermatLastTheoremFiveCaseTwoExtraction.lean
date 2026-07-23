import Propositio.Beal.FermatLastTheoremFiveCaseTwoCofactors
import Propositio.NumberTheory.Diophantine.GoldenIntValuation
import Mathlib.Tactic

/-!
# FLT-5 Case II — item (b): the "unit × fifth power" extraction of the concrete factor

`FermatLastTheoremFiveCaseTwo.case2_core` proves the `5`-adic factorization of Case II over `ℤ`;
`FermatLastTheoremFiveCaseTwoCofactors` exposes the coprime cofactors and the exact `√5`-valuation
of the concrete factor `caseTwoFactorL x y = a₁+b·φ` (`norm = -Φ`); and `GoldenIntValuation`
supplies the reusable `√5`-adic valuation + fifth-power-extraction toolkit. This file assembles
them into **item (b)** of the descent — the step both prior Case-II postmortems flagged as the
last missing brick: pulling the `√5`-peeled residual of `caseTwoFactorL` back to a genuine fifth
power up to a unit, and pinning that unit to `±φⁿ`.

## Main results (proved, axiom-clean, no `sorry`)

* `case2_Phi_eq_five_pow_mul_fifth` — **the fifth-power structure of `Φ`, with the base coprime
  to `5` exposed.** For coprime `x, y` with `x⁵+y⁵ = z⁵`, `z ≠ 0`, `5 ∣ z`, there are `K ≥ 1` and
  `e` with `Φ(x,y) = 5ᴷ · e⁵` and `5 ∤ e`. This is exactly the data hidden inside `case2_core`'s
  existential (it never exposes `5 ∤ e`), re-derived on top of `case2_coprime_cofactors` — and it
  is precisely what the `√5`-adic valuation lift needs to pin the exact `√5`-power of the factor.
* `caseTwoFactorL_peel_coprime_conj` — **coprimality of conjugates (the genuinely new ring
  theory).** If `caseTwoFactorL x y = √5ᴷ · β` with `√5 ∤ β` (the fully `√5`-peeled factor), then
  `β` is coprime to `conj β` in `ℤ[φ]`. Proof: any prime `p ∣ β, conj β` divides both
  `caseTwoFactorL` and `caseTwoFactorR`, hence `ofInt((x+y)²)` (their difference) and `ofInt Φ`
  (their product); primality pushes `p ∣ ofInt(x+y)`, and `caseTwoFactor_common_dvd_sqrt5_sq_of_
  solution` then forces `p ∣ √5²`, so `p ~ √5` — contradicting `√5 ∤ β`.
* `caseTwoFactorL_extraction` — **item (b) headline.** For any Case-II solution, the concrete
  factor factors as `caseTwoFactorL x y = √5ᴷ · (±φⁿ · d⁵)`: a power of the ramified prime `√5`,
  times a unit `±φⁿ`, times an exact fifth power `d⁵`. This is the "unit × fifth power" extraction
  the descent consumes.

## What this does NOT do (honest scope note)

This lands item (b) — the concrete factor is now fully decomposed as `√5ᴷ · unit · fifth power`.
It does **not** assemble the final infinite descent: that further step reads a strictly smaller
solution off the `±φⁿ · d⁵` factorization by pinning the exponent `n` (via a congruence/size
argument on the unit) and recombining coordinates, which is additional work not attempted here.

**No `sorry`, no project axiom** in what follows.
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne
open GoldenInt

/-! ## The fifth-power structure of `Φ`, with `5 ∤ e` exposed -/

/-- **`Φ(x,y) = 5ᴷ · e⁵` with `5 ∤ e` and `K ≥ 1`.** Re-derives, on top of `case2_coprime_cofactors`
(which gives coprime `A, B` with `x+y = 5A`, `Φ = 5B`), the `5`-adic split that `case2_core` performs
internally — but tracks the fact, hidden by `case2_core`'s existential, that the fifth-power base `e`
is coprime to `5`. This is the exact input the `√5`-adic valuation lift needs. -/
theorem case2_Phi_eq_five_pow_mul_fifth {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (K : ℕ) (e : ℤ),
      1 ≤ K ∧
      x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 ^ K * e ^ 5 ∧
      ¬ (5 : ℤ) ∣ e := by
  classical
  obtain ⟨A, B, hcopAB, hxyA, hPhiB⟩ := case2_coprime_cofactors hxy heq h5z
  -- 5 does not divide both A and B (they are coprime).
  have hnot_both : ¬ ((5 : ℤ) ∣ A ∧ (5 : ℤ) ∣ B) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨u, v, huv⟩ := hcopAB
    have h1 : (5 : ℤ) ∣ 1 := by rw [← huv, ha, hb]; exact ⟨u * a + v * b, by ring⟩
    norm_num at h1
  -- exact power of 5 dividing z, as 5^(n+1)
  have hfin : FiniteMultiplicity (5 : ℤ) z := Int.finiteMultiplicity_iff.mpr ⟨by norm_num, hz0⟩
  have hkne : multiplicity (5 : ℤ) z ≠ 0 := multiplicity_ne_zero.mpr h5z
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkne
  obtain ⟨z1, hz_eq, hz1_not5⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hn] at hz_eq
  have hpow_eq : (5 : ℤ) ^ ((n + 1) * 5) = 5 ^ 2 * 5 ^ (5 * n + 3) := by
    rw [← pow_add]; congr 1; ring
  have hz5 : z ^ 5 = 5 ^ 2 * 5 ^ (5 * n + 3) * z1 ^ 5 := by
    rw [hz_eq, mul_pow, ← pow_mul, hpow_eq]
  have hfact : (x + y) * (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) = z ^ 5 := by
    rw [← quintic_sum_factorization]; exact heq
  have hAB25 : 5 * A * (5 * B) = 5 ^ 2 * 5 ^ (5 * n + 3) * z1 ^ 5 := by
    rw [← hxyA, ← hPhiB, hfact, hz5]
  have hAB : A * B = 5 ^ (5 * n + 3) * z1 ^ 5 := by
    have h25 : (25 : ℤ) * (A * B) = 25 * (5 ^ (5 * n + 3) * z1 ^ 5) := by
      have e1 : (5 : ℤ) * A * (5 * B) = 25 * (A * B) := by ring
      have e2 : (5 : ℤ) ^ 2 * 5 ^ (5 * n + 3) * z1 ^ 5 = 25 * (5 ^ (5 * n + 3) * z1 ^ 5) := by ring
      rw [e1, e2] at hAB25; exact hAB25
    exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) h25
  have h5z1 : ¬ (5 : ℤ) ∣ z1 ^ 5 := fun h => hz1_not5 (Int.Prime.dvd_pow' (by norm_num) h)
  rcases not_and_or.mp hnot_both with h5A | h5B
  · -- 5 ∤ A ⟹ all of 5^(5n+3) goes to B; Φ = 5^(5n+4)·e⁵.
    have hcop5A : IsCoprime (5 : ℤ) A := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hdvd5 : Int.gcd (5 : ℤ) A ∣ 5 := by exact_mod_cast Int.gcd_dvd_left (5 : ℤ) A
      have hp5 : Nat.Prime 5 := by norm_num
      rcases hp5.eq_one_or_self_of_dvd _ hdvd5 with h1 | h5
      · exact h1
      · exact absurd (by exact_mod_cast (h5 ▸ Int.gcd_dvd_right (5 : ℤ) A)) h5A
    have hcop5powA : IsCoprime ((5 : ℤ) ^ (5 * n + 3)) A := hcop5A.pow_left
    have hdvdAB : (5 : ℤ) ^ (5 * n + 3) ∣ A * B := ⟨z1 ^ 5, hAB⟩
    have hdvdB : (5 : ℤ) ^ (5 * n + 3) ∣ B := hcop5powA.dvd_of_dvd_mul_left hdvdAB
    obtain ⟨B', hB'⟩ := hdvdB
    have hAB' : A * B' = z1 ^ 5 := by
      have hstep : (5 : ℤ) ^ (5 * n + 3) * (A * B') = 5 ^ (5 * n + 3) * z1 ^ 5 := by
        rw [hB'] at hAB; linear_combination hAB
      exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (5 : ℤ) ≠ 0)) hstep
    have hB'_dvd_B : B' ∣ B := ⟨5 ^ (5 * n + 3), by rw [hB']; ring⟩
    have hcopAB' : IsCoprime A B' := hcopAB.of_isCoprime_of_dvd_right hB'_dvd_B
    obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hcopAB' (by decide : Odd 5) hAB'
    -- 5 ∤ e : e⁵ = B' ∣ A·B' = z1⁵, and 5 ∤ z1⁵.
    have h5B' : ¬ (5 : ℤ) ∣ B' := fun h => h5z1 (h.trans ⟨A, by rw [← hAB']; ring⟩)
    have h5e : ¬ (5 : ℤ) ∣ e := fun h => h5B' (by rw [he]; exact Dvd.dvd.pow h (by norm_num))
    refine ⟨5 * n + 4, e, by omega, ?_, h5e⟩
    have hexp : (5 : ℤ) ^ (5 * n + 4) = 5 ^ (5 * n + 3) * 5 := by
      rw [show 5 * n + 4 = (5 * n + 3) + 1 from by ring, pow_succ]
    rw [hPhiB, hB', he, hexp]; ring
  · -- 5 ∤ B ⟹ B itself is the fifth power; Φ = 5·e⁵.
    have hcop5B : IsCoprime (5 : ℤ) B := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hdvd5 : Int.gcd (5 : ℤ) B ∣ 5 := by exact_mod_cast Int.gcd_dvd_left (5 : ℤ) B
      have hp5 : Nat.Prime 5 := by norm_num
      rcases hp5.eq_one_or_self_of_dvd _ hdvd5 with h1 | h5
      · exact h1
      · exact absurd (by exact_mod_cast (h5 ▸ Int.gcd_dvd_right (5 : ℤ) B)) h5B
    have hcop5powB : IsCoprime ((5 : ℤ) ^ (5 * n + 3)) B := hcop5B.pow_left
    have hdvdAB : (5 : ℤ) ^ (5 * n + 3) ∣ B * A := ⟨z1 ^ 5, by linear_combination hAB⟩
    have hdvdA : (5 : ℤ) ^ (5 * n + 3) ∣ A := hcop5powB.dvd_of_dvd_mul_left hdvdAB
    obtain ⟨A', hA'⟩ := hdvdA
    have hAB' : A' * B = z1 ^ 5 := by
      have hstep : (5 : ℤ) ^ (5 * n + 3) * (A' * B) = 5 ^ (5 * n + 3) * z1 ^ 5 := by
        rw [hA'] at hAB; linear_combination hAB
      exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (5 : ℤ) ≠ 0)) hstep
    have hA'_dvd_A : A' ∣ A := ⟨5 ^ (5 * n + 3), by rw [hA']; ring⟩
    have hcopA'B : IsCoprime A' B := hcopAB.of_isCoprime_of_dvd_left hA'_dvd_A
    obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hcopA'B (by decide : Odd 5) hAB'
    -- 5 ∤ e : e⁵ = B ∣ A'·B = z1⁵.
    have h5Bne : ¬ (5 : ℤ) ∣ B := h5B
    have h5e : ¬ (5 : ℤ) ∣ e := fun h => h5Bne (by rw [he]; exact Dvd.dvd.pow h (by norm_num))
    refine ⟨1, e, le_refl 1, ?_, h5e⟩
    rw [hPhiB, he, pow_one]

/-! ## Coprimality of the `√5`-peeled factor with its conjugate -/

/-- **Coprimality of conjugates.** If the concrete Case-II factor is fully `√5`-peeled,
`caseTwoFactorL x y = √5ᴷ · β` with `√5 ∤ β`, then `β` is coprime to `conj β`. Any common prime `p`
divides `caseTwoFactorL` (via `β ∣ caseTwoFactorL`) and `caseTwoFactorR` (via `conj β ∣ caseTwoFactorR`),
hence their difference `ofInt(-(x+y)²)` and their product `ofInt Φ`; primality gives `p ∣ ofInt(x+y)`,
so `caseTwoFactor_common_dvd_sqrt5_sq_of_solution` forces `p ∣ √5²`, whence `p ~ √5` — contradicting
`√5 ∤ β` via `p ∣ β`. -/
theorem caseTwoFactorL_peel_coprime_conj {x y z : ℤ} (K : ℕ)
    (hxy : IsCoprime x y) (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z)
    {β : GoldenInt} (hβ : caseTwoFactorL x y = sqrt5 ^ K * β) (hnd : ¬ sqrt5 ∣ β) :
    IsCoprime β (conj β) := by
  have hβ0 : β ≠ 0 := fun h => hnd (h ▸ dvd_zero sqrt5)
  apply isCoprime_of_prime_dvd
  · exact fun h => hβ0 h.1
  · intro p hp hpβ hpcβ
    -- p ∣ caseTwoFactorL (via β ∣ caseTwoFactorL)
    have hbLdvd : β ∣ caseTwoFactorL x y := by rw [hβ]; exact dvd_mul_left β (sqrt5 ^ K)
    have hpL : p ∣ caseTwoFactorL x y := hpβ.trans hbLdvd
    -- p ∣ caseTwoFactorR (via conj β ∣ caseTwoFactorR)
    have hcRdvd : conj β ∣ caseTwoFactorR x y := by
      rw [caseTwoFactorR_eq_neg_conj, hβ, conj_mul]
      exact (dvd_neg).mpr (dvd_mul_left (conj β) (conj (sqrt5 ^ K)))
    have hpR : p ∣ caseTwoFactorR x y := hpcβ.trans hcRdvd
    -- p ∣ ofInt((x+y)²) from the difference L - R
    have hpsub : p ∣ ofInt ((x + y) ^ 2) := by
      have hdiff : caseTwoFactorL x y - caseTwoFactorR x y = -ofInt ((x + y) ^ 2) := by
        ext <;> simp [caseTwoFactorL, caseTwoFactorR, ofInt] <;> ring
      have hd : p ∣ (caseTwoFactorL x y - caseTwoFactorR x y) := dvd_sub hpL hpR
      rw [hdiff] at hd
      exact (dvd_neg).mp hd
    -- p ∣ ofInt(x+y) by primality
    have hpxy : p ∣ ofInt (x + y) := by
      rw [ofInt_pow] at hpsub
      exact hp.dvd_of_dvd_pow hpsub
    -- p ∣ ofInt Φ from the product L·R
    have hpPhi : p ∣ ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
      have hLdvd : caseTwoFactorL x y ∣ ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) :=
        ⟨caseTwoFactorR x y, (caseTwoFactor_mul x y).symm⟩
      exact hpL.trans hLdvd
    -- common divisor ⟹ p ∣ √5², hence p ∣ √5
    have hp5sq : p ∣ sqrt5 * sqrt5 :=
      caseTwoFactor_common_dvd_sqrt5_sq_of_solution hxy heq h5z hpxy hpPhi
    have hpsqrt5 : p ∣ sqrt5 := (hp.dvd_or_dvd hp5sq).elim id id
    -- p ~ √5 ⟹ √5 ∣ β, contradiction
    have hassoc : Associated p sqrt5 := hp.irreducible.associated_of_dvd irreducible_sqrt5 hpsqrt5
    exact hnd (hassoc.symm.dvd.trans hpβ)

/-! ## Item (b) headline: the "unit × fifth power" extraction -/

/-- **Item (b) — the concrete Case-II factor is `√5ᴷ · (±φⁿ · d⁵)`.** For any Case-II solution
(coprime `x, y`, `x⁵+y⁵ = z⁵`, `z ≠ 0`, `5 ∣ z`), the concrete factor `caseTwoFactorL x y` (with
`norm = -Φ`) decomposes as a power of the ramified prime `√5`, times a unit `±φⁿ`, times an exact
fifth power `d⁵`. Proof: `case2_Phi_eq_five_pow_mul_fifth` gives `Φ = 5ᴷ·e⁵` with `5 ∤ e`, so
`(norm L).natAbs = |Φ| = 5ᴷ·|e|⁵`; the `√5`-adic lift `exists_sqrt5_pow_decomp_of_norm_natAbs`
peels exactly `√5ᴷ`, leaving `β` with `norm β = ±e⁵`; `caseTwoFactorL_peel_coprime_conj` gives
`IsCoprime β (conj β)`, so `pm_phiZpow_mul_pow_of_mul_conj_eq_pow` extracts `β = ±φⁿ · d⁵`. -/
theorem caseTwoFactorL_extraction {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (K : ℕ) (n : ℤ) (β d : GoldenInt),
      caseTwoFactorL x y = sqrt5 ^ K * β ∧
      (β = phiZpow n * d ^ 5 ∨ β = -(phiZpow n * d ^ 5)) := by
  obtain ⟨K, e, hK, hPhi, h5e⟩ := case2_Phi_eq_five_pow_mul_fifth hxy hz0 heq h5z
  -- L ≠ 0 : norm L = -Φ = -(5ᴷ e⁵) ≠ 0
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
  -- (norm L).natAbs = 5ᴷ · |e|⁵
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
  -- peel exactly √5ᴷ
  obtain ⟨β, hβ, hnd, hnβt⟩ :=
    exists_sqrt5_pow_decomp_of_norm_natAbs hLne h5t hnat
  -- norm β = ±e⁵
  have hnormβ : norm β = e ^ 5 ∨ norm β = -(e ^ 5) := by
    have : (norm β).natAbs = (e ^ 5).natAbs := hnβt
    exact Int.natAbs_eq_natAbs_iff.mp this
  -- coprimality of conjugates + extraction
  have hcop : IsCoprime β (conj β) := caseTwoFactorL_peel_coprime_conj K hxy heq h5z hβ hnd
  obtain ⟨n, d, hd⟩ := pm_phiZpow_mul_pow_of_mul_conj_eq_pow (by decide : Odd 5) hcop hnormβ
  exact ⟨K, n, β, d, hβ, hd⟩

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo
#print axioms case2_Phi_eq_five_pow_mul_fifth
#print axioms caseTwoFactorL_peel_coprime_conj
#print axioms caseTwoFactorL_extraction
end AxiomCheck
