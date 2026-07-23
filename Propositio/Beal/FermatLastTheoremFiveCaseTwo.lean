import Propositio.Beal.FermatLastTheoremFiveCaseOne
import Propositio.Beal.FermatLastTheoremFiveCaseOneDescent
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Fermat's Last Theorem for exponent 5, Case II — the classical `5-adic` factorization step

`FermatLastTheoremFiveCaseOne.lean` / `FermatLastTheoremFiveCaseOneDescent.lean` closed **Case
I** of FLT-5 (`5 ∤ ABC`). This file begins **Case II** (`5 ∣ ABC`), the harder classical
Legendre/Dirichlet completion (1825), which requires descent in the ring of integers of
`ℚ(√5)` (the golden-ratio ring `ℤ[φ]`, whose fundamental-unit theory is already built in
`BealFundamentalUnitPell.lean`).

## What this file proves

Given pairwise coprime `x, y, z` with `x^5 + y^5 = z^5`, `z ≠ 0`, and `5 ∣ z` (the case where
the auxiliary prime `5` divides the term `z`; the fully general "`5` divides one of `x, y, z`"
hypothesis reduces to this normalized form by the same relabeling/sign-substitution trick used
in `FermatLastTheoremFiveCaseOne.fermat_five_case_one`), this file proves the **complete,
explicit `5`-adic factorization** of the classical Case-II argument:

`case2_core` : there exist `n : ℕ` and `d, e : ℤ` such that **either**

* `x + y = 5 · d⁵` and the quartic cofactor `= 5^(5n+4) · e⁵`, **or**
* `x + y = 5^(5n+4) · d⁵` and the quartic cofactor `= 5 · e⁵`.

(Here `5^(n+1)` is the *exact* power of `5` dividing `z`, i.e. `n + 1 = v_5(z)`.)

This is the rigorous form of the classical fact that, once `5 ∣ (x+y)` (forced automatically:
same Frobenius/"freshman's dream" trick as Case I, since `5 ∣ z`), the two factors of
`x^5+y^5 = (x+y)·Φ(x,y)` share the prime `5` to **exactly** the first power as a *common*
divisor (`gcd(x+y, Φ) = 5` exactly, via `quintic_factor_gcd_dvd_five`), so **all** of the
excess `5`-power in `z^5` beyond `5²` must be concentrated in *one* of the two factors — the
classical case split (`Case II(i)` / `Case II(ii)` in Edwards' terminology) — and, once that
power is peeled off, unique factorization (`Int.eq_pow_of_mul_eq_pow_odd`, since the residual
cofactors are then genuinely coprime) forces each residual cofactor to be an exact `5`th power.

## What is NOT proved here (honest scope note)

This is the **factorization/setup step only** — the classical "hard" content of Case II is
the subsequent step, **not attempted in this file**: transplanting the factorization
`x + y = 5·d⁵` (or its mirror) into the ring `ℤ[φ]` via the identity
`4·Φ(x,y) = 5·(x²+y²)² − (x+y)⁴` (equivalently, factoring `Φ` over `ℤ[√5]` as a *norm*), pinning
the resulting unit via `BealFundamentalUnitPell.beal_fundamental_unit_sqrt5`, and using that to
construct a **strictly smaller** Case-II (or Case-I) solution, completing the infinite descent.
That step is genuinely novel 1825-era mathematics (Legendre's contribution) and was not reached
in this session — see the accompanying session report for exactly where the attempt stopped.

**No `sorry`, no project axiom** in what follows.
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne

/-- **Case II core factorization.** For pairwise coprime `x, y, z` with `z ≠ 0`,
`x^5 + y^5 = z^5`, and `5 ∣ z`: writing `5^(n+1)` for the exact power of `5` dividing `z`, one
of the two factors of `x^5+y^5 = (x+y)·Φ(x,y)` is `5` times an exact fifth power, and the other
is `5^(5n+4)` times an exact fifth power. -/
theorem case2_core {x y z : ℤ}
    (hxy : IsCoprime x y) (_hyz : IsCoprime y z) (_hxz : IsCoprime x z)
    (hz0 : z ≠ 0) (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (n : ℕ) (d e : ℤ),
      (x + y = 5 * d ^ 5 ∧
        x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 ^ (5 * n + 4) * e ^ 5) ∨
      (x + y = 5 ^ (5 * n + 4) * d ^ 5 ∧
        x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * e ^ 5) := by
  classical
  -- Step 1: 5 ∣ (x+y), by the Frobenius/"freshman's dream" trick (Case I's cast lemma).
  have h5xy : (5 : ℤ) ∣ (x + y) := by
    have hcast := cast_add_eq_cast_of_pow_five_eq heq
    have hz_zero : (z : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mpr h5z
    have hxy0 : ((x + y : ℤ) : ZMod 5) = 0 := by rw [hcast, hz_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 5).mp hxy0
  -- Step 2: 5 ∣ Φ(x,y), from the cofactor identity Φ = 5x⁴ + (x+y)·(...).
  have h5Phi : (5 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
    have hident := quintic_cofactor_identity x y
    rw [hident]
    exact dvd_add (dvd_mul_right 5 (x ^ 4)) (h5xy.mul_right _)
  -- Step 3: gcd(x+y, Φ) = 5 exactly.
  have hd5 : Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) ∣ 5 := by
    have h := quintic_factor_gcd_dvd_five hxy (Int.gcd_dvd_left (x + y)
      (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4))
      (Int.gcd_dvd_right (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4))
    exact_mod_cast h
  have h5_dvd_gcd : (5 : ℕ) ∣
      Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) :=
    Int.dvd_gcd (c := 5) (by exact_mod_cast h5xy) (by exact_mod_cast h5Phi)
  have hgcd5 : Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) = 5 :=
    Nat.dvd_antisymm hd5 h5_dvd_gcd
  -- Step 4: extract coprime cofactors A, B with x+y = 5A, Φ = 5B.
  have hgcd_pos :
      0 < Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
    rw [hgcd5]; norm_num
  obtain ⟨A, B, hAB1, hxyA, hPhiB⟩ := Int.exists_gcd_one hgcd_pos
  rw [hgcd5] at hxyA hPhiB
  have hcopAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB1
  have hxyA' : x + y = 5 * A := by rw [hxyA]; push_cast; ring
  have hPhiB' : x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * B := by
    rw [hPhiB]; push_cast; ring
  -- Step 5: 5 does not divide both A and B (they are coprime).
  have hnot_both : ¬ ((5 : ℤ) ∣ A ∧ (5 : ℤ) ∣ B) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨u, v, huv⟩ := hcopAB
    have h1 : (5 : ℤ) ∣ 1 := by
      rw [← huv, ha, hb]
      exact ⟨u * a + v * b, by ring⟩
    norm_num at h1
  -- Step 6: the exact power of 5 dividing z, as 5^(n+1).
  have hfin : FiniteMultiplicity (5 : ℤ) z := Int.finiteMultiplicity_iff.mpr ⟨by norm_num, hz0⟩
  have hkne : multiplicity (5 : ℤ) z ≠ 0 := multiplicity_ne_zero.mpr h5z
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkne
  obtain ⟨z1, hz_eq, hz1_not5⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hn] at hz_eq
  -- Step 7: the master 5-adic identity A * B = 5^(5n+3) * z1^5.
  have hpow_eq : (5 : ℤ) ^ ((n + 1) * 5) = 5 ^ 2 * 5 ^ (5 * n + 3) := by
    rw [← pow_add]; congr 1; ring
  have hz5 : z ^ 5 = 5 ^ 2 * 5 ^ (5 * n + 3) * z1 ^ 5 := by
    rw [hz_eq, mul_pow, ← pow_mul, hpow_eq]
  have hfact : (x + y) * (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) = z ^ 5 := by
    rw [← quintic_sum_factorization]; exact heq
  have hAB25 : 5 * A * (5 * B) = 5 ^ 2 * 5 ^ (5 * n + 3) * z1 ^ 5 := by
    rw [← hxyA', ← hPhiB', hfact, hz5]
  have hAB : A * B = 5 ^ (5 * n + 3) * z1 ^ 5 := by
    have h25 : (25 : ℤ) * (A * B) = 25 * (5 ^ (5 * n + 3) * z1 ^ 5) := by
      have e1 : (5 : ℤ) * A * (5 * B) = 25 * (A * B) := by ring
      have e2 : (5 : ℤ) ^ 2 * 5 ^ (5 * n + 3) * z1 ^ 5 = 25 * (5 ^ (5 * n + 3) * z1 ^ 5) := by
        ring
      rw [e1, e2] at hAB25
      exact hAB25
    exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) h25
  -- Step 8: dispatch on which of A, B carries the excess 5-power.
  rcases not_and_or.mp hnot_both with h5A | h5B
  · -- ¬ 5 ∣ A: A is coprime to 5, so all of 5^(5n+3) is forced into B.
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
    obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd hcopAB' (by decide : Odd 5) hAB'
    refine ⟨n, d, e, Or.inl ⟨?_, ?_⟩⟩
    · rw [hxyA', hd]
    · have hexp : (5 : ℤ) ^ (5 * n + 4) = 5 ^ (5 * n + 3) * 5 := by
        rw [show 5 * n + 4 = (5 * n + 3) + 1 from by ring, pow_succ]
      rw [hPhiB', hB', he, hexp]; ring
  · -- ¬ 5 ∣ B: symmetric branch, all of 5^(5n+3) is forced into A.
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
    obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd hcopA'B (by decide : Odd 5) hAB'
    refine ⟨n, d, e, Or.inr ⟨?_, ?_⟩⟩
    · have hexp : (5 : ℤ) ^ (5 * n + 4) = 5 ^ (5 * n + 3) * 5 := by
        rw [show 5 * n + 4 = (5 * n + 3) + 1 from by ring, pow_succ]
      rw [hxyA', hA', hd, hexp]; ring
    · rw [hPhiB', he]

/-- **Case II entry point.** For pairwise coprime nonzero `x, y, z` with `x^5+y^5=z^5` and
`5` dividing at least one of `x, y, z`, the `case2_core` factorization holds for *some*
relabelled pair among `(x,y)`, `(z,-x)`, `(z,-y)` — obtained from the raw hypothesis
`5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z` by the same sign-substitution trick used in
`FermatLastTheoremFiveCaseOne.fermat_five_case_one`'s dispatcher: `x^5+y^5=z^5` has, up to
sign, three equivalent forms `x^5+y^5=z^5`, `z^5+(-x)^5=y^5`, `z^5+(-y)^5=x^5`, each putting a
different one of the three original variables in the "divisible-by-5" (right-hand) slot that
`case2_core` needs. -/
theorem case2_dvd_reduction {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5)
    (h5 : (5 : ℤ) ∣ x ∨ (5 : ℤ) ∣ y ∨ (5 : ℤ) ∣ z) :
    (∃ (n : ℕ) (d e : ℤ),
      (x + y = 5 * d ^ 5 ∧
        x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 ^ (5 * n + 4) * e ^ 5) ∨
      (x + y = 5 ^ (5 * n + 4) * d ^ 5 ∧
        x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * e ^ 5)) ∨
    (∃ (n : ℕ) (d e : ℤ),
      (z + -x = 5 * d ^ 5 ∧
        z ^ 4 - z ^ 3 * (-x) + z ^ 2 * (-x) ^ 2 - z * (-x) ^ 3 + (-x) ^ 4
          = 5 ^ (5 * n + 4) * e ^ 5) ∨
      (z + -x = 5 ^ (5 * n + 4) * d ^ 5 ∧
        z ^ 4 - z ^ 3 * (-x) + z ^ 2 * (-x) ^ 2 - z * (-x) ^ 3 + (-x) ^ 4 = 5 * e ^ 5)) ∨
    (∃ (n : ℕ) (d e : ℤ),
      (z + -y = 5 * d ^ 5 ∧
        z ^ 4 - z ^ 3 * (-y) + z ^ 2 * (-y) ^ 2 - z * (-y) ^ 3 + (-y) ^ 4
          = 5 ^ (5 * n + 4) * e ^ 5) ∨
      (z + -y = 5 ^ (5 * n + 4) * d ^ 5 ∧
        z ^ 4 - z ^ 3 * (-y) + z ^ 2 * (-y) ^ 2 - z * (-y) ^ 3 + (-y) ^ 4 = 5 * e ^ 5)) := by
  rcases h5 with h5x | h5y | h5z
  · -- 5 ∣ x: use z^5 + (-y)^5 = x^5, so the "z-role" is x.
    have heq'' : z ^ 5 + (-y) ^ 5 = x ^ 5 := by linear_combination -heq
    have hcop1 : IsCoprime z (-y) := hyz.symm.neg_right
    have hcop2 : IsCoprime (-y) x := hxy.symm.neg_left
    have hcop3 : IsCoprime z x := hxz.symm
    exact Or.inr (Or.inr (case2_core hcop1 hcop2 hcop3 hx0 heq'' h5x))
  · -- 5 ∣ y: use z^5 + (-x)^5 = y^5, so the "z-role" is y.
    have heq' : z ^ 5 + (-x) ^ 5 = y ^ 5 := by linear_combination -heq
    have hcop1 : IsCoprime z (-x) := hxz.symm.neg_right
    have hcop2 : IsCoprime (-x) y := hxy.neg_left
    have hcop3 : IsCoprime z y := hyz.symm
    exact Or.inr (Or.inl (case2_core hcop1 hcop2 hcop3 hy0 heq' h5y))
  · -- 5 ∣ z: direct.
    exact Or.inl (case2_core hxy hyz hxz hz0 heq h5z)

end FermatLastTheoremFiveCaseTwo
