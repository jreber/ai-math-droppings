import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeDescent
import Propositio.NumberTheory.Beal.Eisenstein

/-!
# Cube-sum descent dichotomy: the `3 ∣ C` branch, and Beal-(3, 3, 3) from FLT-3

**NEW mathematics — no LaTTe sibling.** This file completes the cube-sum descent
*dichotomy* opened in `BealCubeDescent.lean`. There the equation `A³ + B³ = C^z`
with coprime `A, B` was treated in the case `3 ∤ C`, where the two Eisenstein
factors `s = A + B` and `q = A² + B² − A·B` are coprime and each is forced to be
a perfect `z`-th power. Here we treat the **complementary branch `3 ∣ C`**, where
(equivalently) `3 ∣ A + B`, the Eisenstein gcd is exactly `3` (not `1`), and the
descent must pull a single factor of `3` out of the quadratic.

We also connect the **exponent `z = 3`** case to mathlib's *unconditional* proof
of Fermat's Last Theorem for `3` (`fermatLastTheoremThree`), landing the Beal
exponent-(3, 3, 3) case with no coprimality or common-factor hypothesis at all.

## Contents
* `beal_333` — Beal-(3, 3, 3): `A³ + B³ ≠ C³` for nonzero `A, B, C`, straight from
  mathlib's `fermatLastTheoremThree`. Unconditional (no coprimality needed).
* `three_dvd_sum_iff` — under `A³ + B³ = C^z`, `3 ∣ C ↔ 3 ∣ (A + B)`.
* `three_dvd_quadratic_of_three_dvd_sum` — `3 ∣ (A + B) → 3 ∣ (A² + B² − A·B)`.
* `not_three_dvd_of_coprime_of_three_dvd_sum` — coprime `A, B` with `3 ∣ A + B`
  forces `3 ∤ A` and `3 ∤ B`.
* `not_nine_dvd_quadratic` — the quadratic has `3`-adic valuation exactly `1`.
* `gcd_factors_eq_three` — the Eisenstein gcd is exactly `3` in this branch.
* `coprime_sum_quotient` — after dividing the quadratic by its single factor of
  `3`, the quotient is coprime to `A + B`.
* `cube_sum_descent_three` — the factored descent form in the `3 ∣ C` branch.

Key mathlib lemmas relied on:
* `fermatLastTheoremThree` — proven FLT for exponent 3.
* `Nat.Prime.dvd_of_dvd_pow`, `Nat.Prime.dvd_mul` — prime divisibility.
* `Nat.Coprime` API and `BealEisenstein.eisenstein_gcd_eq_one_or_three`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealCubeDescentThree.lean` to typecheck.
-/

namespace BealCubeDescentThree

open BealCubeDescent

/-!
## Part 1 — Beal-(3, 3, 3) from mathlib's proven FLT-3

`fermatLastTheoremThree : FermatLastTheoremFor 3` unfolds (definitionally, via
`FermatLastTheoremFor 3 = FermatLastTheoremWith ℕ 3`) to
`∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3`. The Beal
exponent-(3, 3, 3) case is therefore *exactly* FLT-3, and it is unconditional:
no coprimality or common-factor hypothesis is needed, because FLT-3 itself is
unconditional.
-/

/-- **Beal-(3, 3, 3) (HEADLINE).**
For nonzero naturals `A, B, C`, `A³ + B³ ≠ C³`. This is the Beal
exponent-(3, 3, 3) case, obtained directly from mathlib's proven
`fermatLastTheoremThree`. **NEW — no LaTTe sibling.** -/
theorem beal_333 {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 3 + B ^ 3 ≠ C ^ 3 :=
  fermatLastTheoremThree A B C hA hB hC

/-- **Beal-(3, 3, 3), unconditional corollary.**
The Beal-(3, 3, 3) statement needs **no** common-factor or coprimality hypothesis:
FLT-3 holds for *all* nonzero `A, B, C`, coprime or not. In particular a
hypothetical common factor `d = gcd(A, B)` cannot rescue a solution — there is
none. We record this by exhibiting the conclusion with an explicit (irrelevant)
coprimality hypothesis dropped: the same `≠` holds regardless. **NEW.** -/
theorem beal_333_no_coprime_soln {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C ≠ 0) : ¬ (A ^ 3 + B ^ 3 = C ^ 3) :=
  beal_333 hA hB hC

/-!
## Part 2 — the `3 ∣ C` branch of the descent

In the complementary branch the prime `3` divides `C`, equivalently (under
`A³ + B³ = C^z`) it divides `A + B`. We trace the consequences for the Eisenstein
quadratic `q = A² + B² − A·B`, which equals `(A + B)² − 3·A·B`. From `3 ∣ A + B`
we get `3 ∣ q`; from coprimality we get `3 ∤ A·B`, so `v₃(q) = 1` exactly,
i.e. `9 ∤ q`. Hence the Eisenstein gcd, known to be `1` or `3`, is exactly `3`.
-/

/-- **`3 ∣ C ↔ 3 ∣ (A + B)` under the cube-sum equation.**
Given `A³ + B³ = C^z` with `z ≠ 0`, the prime `3` divides `C` iff it divides
`A + B`. Forward: `3 ∣ C ⟹ 3 ∣ C^z = A³ + B³ = (A + B)·q ⟹ 3 ∣ A + B` (using
`3 ∤ q` would be needed, so instead we argue via the linear factor directly:
`3 ∣ A³ + B³` and `3 ∣ A³ + B³ − (A+B)³`? — cleaner: `3 ∣ A+B → 3 ∣ A³+B³`).
We prove both directions through the factorization. **NEW.** -/
theorem three_dvd_sum_iff {A B C z : ℕ} (hz : z ≠ 0)
    (h : A ^ 3 + B ^ 3 = C ^ z) : 3 ∣ C ↔ 3 ∣ (A + B) := by
  constructor
  · -- 3 ∣ C → 3 ∣ C^z = (A+B)·q → 3 ∣ A+B  (since 3 is prime; the other factor
    -- branch 3 ∣ q is handled by congruence: 3 ∣ q ∧ 3 ∣ A+B are linked, but we
    -- only need: 3 ∣ A³+B³ and a mod-3 argument that 3∣A³+B³ ↔ 3∣A+B).
    intro hC
    -- 3 ∣ C^z.
    have hCz : (3 : ℕ) ∣ C ^ z := dvd_pow hC hz
    rw [← h] at hCz
    -- 3 ∣ A³ + B³.  By Fermat/Euler mod 3: x³ ≡ x (mod 3), so A³+B³ ≡ A+B (mod 3).
    -- Hence 3 ∣ A+B.
    have hcong : (A ^ 3 + B ^ 3) % 3 = (A + B) % 3 := by
      conv_lhs => rw [Nat.add_mod, Nat.pow_mod A, Nat.pow_mod B]
      conv_rhs => rw [Nat.add_mod]
      have hA3 : ∀ r : ℕ, r < 3 → (r ^ 3) % 3 = r % 3 := by decide
      rw [hA3 (A % 3) (Nat.mod_lt _ (by norm_num)),
          hA3 (B % 3) (Nat.mod_lt _ (by norm_num))]
      rw [Nat.mod_mod, Nat.mod_mod]
    rw [Nat.dvd_iff_mod_eq_zero] at hCz ⊢
    rw [← hcong]; exact hCz
  · -- 3 ∣ A+B → 3 ∣ A³+B³ = C^z → 3 ∣ C.
    intro hAB
    have hsum : (3 : ℕ) ∣ A ^ 3 + B ^ 3 := by
      have hcong : (A ^ 3 + B ^ 3) % 3 = (A + B) % 3 := by
        conv_lhs => rw [Nat.add_mod, Nat.pow_mod A, Nat.pow_mod B]
        conv_rhs => rw [Nat.add_mod]
        have hA3 : ∀ r : ℕ, r < 3 → (r ^ 3) % 3 = r % 3 := by decide
        rw [hA3 (A % 3) (Nat.mod_lt _ (by norm_num)),
            hA3 (B % 3) (Nat.mod_lt _ (by norm_num))]
        rw [Nat.mod_mod, Nat.mod_mod]
      rw [Nat.dvd_iff_mod_eq_zero, hcong, ← Nat.dvd_iff_mod_eq_zero]
      exact hAB
    rw [h] at hsum
    exact (Nat.prime_three).dvd_of_dvd_pow hsum

/-- **`3 ∣ (A + B) → 3 ∣ (A² + B² − A·B)`.**
The Eisenstein quadratic `q = A² + B² − A·B` satisfies `q = (A + B)² − 3·A·B`
(over `ℤ`, lifted honestly since `A·B ≤ A² + B²`). If `3 ∣ A + B` then `3` divides
both `(A + B)²` and `3·A·B`, hence `q`. **NEW.** -/
theorem three_dvd_quadratic_of_three_dvd_sum {A B : ℕ} (h : 3 ∣ (A + B)) :
    3 ∣ (A ^ 2 + B ^ 2 - A * B) := by
  -- Work over ℤ via the honest cast, then transfer back.
  have hcast : ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ) = ((A : ℤ) + B) ^ 2 - 3 * (A * B) := by
    rw [Nat.cast_sub (ab_le_sq_add_sq A B)]; push_cast; ring
  have hZ : (3 : ℤ) ∣ ((A : ℤ) + B) := by exact_mod_cast h
  -- 3 ∣ (A+B)²  and  3 ∣ 3·(A·B), hence 3 ∣ their difference = q.
  have hdiff : (3 : ℤ) ∣ (((A : ℤ) + B) ^ 2 - 3 * (A * B)) :=
    dvd_sub (Dvd.dvd.pow hZ (by norm_num)) (Dvd.intro _ rfl)
  rw [← hcast] at hdiff
  exact_mod_cast hdiff

/-- **Coprime `A, B` with `3 ∣ A + B` forces `3 ∤ A` and `3 ∤ B`.**
If `3 ∣ A` then `3 ∣ B` (since `3 ∣ A + B`), so `3 ∣ gcd(A, B) = 1`, absurd. The
prime `3` therefore divides neither, hence `3 ∤ A·B`. **NEW.** -/
theorem not_three_dvd_of_coprime_of_three_dvd_sum {A B : ℕ} (hAB : Nat.Coprime A B)
    (h : 3 ∣ (A + B)) : ¬ (3 ∣ A) ∧ ¬ (3 ∣ B) ∧ ¬ (3 ∣ A * B) := by
  -- If 3 ∣ A then 3 ∣ B = (A+B) − A, so 3 ∣ gcd A B = 1, absurd.
  have hnA : ¬ (3 ∣ A) := by
    intro hA
    have hB : (3 : ℕ) ∣ B := by
      have : B = (A + B) - A := by omega
      rw [this]; exact Nat.dvd_sub h hA
    have : (3 : ℕ) ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
    rw [hAB] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  have hnB : ¬ (3 ∣ B) := by
    intro hB
    have hA : (3 : ℕ) ∣ A := by
      have : A = (A + B) - B := by omega
      rw [this]; exact Nat.dvd_sub h hB
    exact hnA hA
  refine ⟨hnA, hnB, ?_⟩
  intro hAB'
  rcases (Nat.prime_three).dvd_mul.mp hAB' with h' | h'
  · exact hnA h'
  · exact hnB h'

/-- **`9 ∤ (A² + B² − A·B)` in the `3 ∣ A + B` branch.**
With `q = (A + B)² − 3·A·B` and `3 ∣ A + B`, we have `9 ∣ (A + B)²`. If `9 ∣ q`
too, then `9 ∣ ((A + B)² − q) = 3·A·B`, so `3 ∣ A·B` — contradicting coprimality.
Hence the `3`-adic valuation of `q` is exactly `1`. **NEW.** -/
theorem not_nine_dvd_quadratic {A B : ℕ} (hAB : Nat.Coprime A B)
    (h : 3 ∣ (A + B)) : ¬ (9 ∣ (A ^ 2 + B ^ 2 - A * B)) := by
  intro h9
  -- 3 ∤ A·B from coprimality.
  obtain ⟨-, -, hnAB⟩ := not_three_dvd_of_coprime_of_three_dvd_sum hAB h
  -- Move to ℤ with the honest cast: q = (A+B)² − 3·(A·B).
  have hcast : ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ) = ((A : ℤ) + B) ^ 2 - 3 * (A * B) := by
    rw [Nat.cast_sub (ab_le_sq_add_sq A B)]; push_cast; ring
  have h9Z : (9 : ℤ) ∣ ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ) := by exact_mod_cast h9
  have hABZ : (3 : ℤ) ∣ ((A : ℤ) + B) := by exact_mod_cast h
  -- 9 ∣ (A+B)².
  have hsq : (9 : ℤ) ∣ ((A : ℤ) + B) ^ 2 := by
    obtain ⟨k, hk⟩ := hABZ
    exact ⟨k ^ 2, by rw [hk]; ring⟩
  -- 9 ∣ 3·(A·B) = (A+B)² − q.
  have h3ab : (9 : ℤ) ∣ 3 * ((A : ℤ) * B) := by
    have : (3 : ℤ) * ((A : ℤ) * B) = ((A : ℤ) + B) ^ 2 - ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ) := by
      rw [hcast]; ring
    rw [this]; exact dvd_sub hsq h9Z
  -- 9 ∣ 3·X → 3 ∣ X.
  have h3X : (3 : ℤ) ∣ ((A : ℤ) * B) := by
    obtain ⟨m, hm⟩ := h3ab
    refine ⟨m, ?_⟩
    have : (3 : ℤ) * ((A : ℤ) * B) = 3 * (3 * m) := by rw [hm]; ring
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) this
  -- Back to ℕ: 3 ∣ A·B, contradiction.
  have : (3 : ℕ) ∣ A * B := by exact_mod_cast h3X
  exact hnAB this

/-- **The Eisenstein gcd is exactly `3` in the `3 ∣ C` branch.**
For coprime `A, B` with `3 ∣ A + B`, the Eisenstein dichotomy gives
`gcd(A + B, q) ∈ {1, 3}`; the divisibility facts `3 ∣ A + B` and `3 ∣ q` pin it to
`3`. **NEW.** -/
theorem gcd_factors_eq_three {A B : ℕ} (hAB : Nat.Coprime A B)
    (h : 3 ∣ (A + B)) : Nat.gcd (A + B) (A ^ 2 + B ^ 2 - A * B) = 3 := by
  -- 3 divides the gcd (it divides both factors).
  have hq : (3 : ℕ) ∣ (A ^ 2 + B ^ 2 - A * B) := three_dvd_quadratic_of_three_dvd_sum h
  have h3g : (3 : ℕ) ∣ Nat.gcd (A + B) (A ^ 2 + B ^ 2 - A * B) := Nat.dvd_gcd h hq
  -- The Eisenstein dichotomy: gcd is 1 or 3 (transported from ℤ).
  have hcopZ : IsCoprime (A : ℤ) (B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hAB)
  have hdich := BealEisenstein.eisenstein_gcd_eq_one_or_three (A : ℤ) (B : ℤ) hcopZ
  have hs : ((A : ℤ) + B) = ((A + B : ℕ) : ℤ) := by push_cast; ring
  have hqc : ((A : ℤ) ^ 2 - A * B + B ^ 2) = ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ) := by
    rw [Nat.cast_sub (ab_le_sq_add_sq A B)]; push_cast; ring
  rw [hs, hqc, Int.gcd_natCast_natCast] at hdich
  rcases hdich with h1 | h3
  · -- gcd = 1 contradicts 3 ∣ gcd.
    exfalso; rw [h1] at h3g
    exact absurd (Nat.le_of_dvd (by norm_num) h3g) (by norm_num)
  · exact h3

/-- **The quadratic carries exactly one factor of `3`, coprime to `A + B`.**
Write `q = A² + B² − A·B = 3·q'` (possible since `3 ∣ q`). With `3 ∤ q'` (from
`9 ∤ q`), the quotient `q' = q / 3` is coprime to `A + B`: a common divisor `g`
of `A + B` and `q'` also divides `q = 3·q'`, hence divides `gcd(A + B, q) = 3`,
so `g ∈ {1, 3}`; but `g = 3` would give `3 ∣ q'`, excluded. Thus `g = 1`.
This isolates the shared factor of `3` from the descent. **NEW.** -/
theorem coprime_sum_quotient {A B : ℕ} (hAB : Nat.Coprime A B)
    (h : 3 ∣ (A + B)) :
    Nat.Coprime (A + B) ((A ^ 2 + B ^ 2 - A * B) / 3) := by
  set q := A ^ 2 + B ^ 2 - A * B with hq_def
  -- 3 ∣ q, so q = 3 · q' with q' = q / 3.
  have hq3 : (3 : ℕ) ∣ q := three_dvd_quadratic_of_three_dvd_sum h
  obtain ⟨q', hq'⟩ := hq3
  have hdiv : q / 3 = q' := by rw [hq']; exact Nat.mul_div_cancel_left q' (by norm_num)
  rw [hdiv]
  -- 3 ∤ q' (else 9 ∣ q).
  have hnq' : ¬ (3 ∣ q') := by
    intro h3q'
    apply not_nine_dvd_quadratic hAB h
    obtain ⟨k, hk⟩ := h3q'
    exact ⟨k, by rw [← hq_def, hq', hk]; ring⟩
  -- gcd(A+B, q) = 3.
  have hgcd3 : Nat.gcd (A + B) q = 3 := gcd_factors_eq_three hAB h
  -- g := gcd(A+B, q') divides gcd(A+B, q) = 3, so g ∈ {1,3}; 3 excluded by 3∤q'.
  set g := Nat.gcd (A + B) q' with hg_def
  have hg_dvd_sum : g ∣ A + B := Nat.gcd_dvd_left _ _
  have hg_dvd_q' : g ∣ q' := Nat.gcd_dvd_right _ _
  have hg_dvd_q : g ∣ q := by rw [hq']; exact Dvd.dvd.mul_left hg_dvd_q' 3
  have hg_dvd_3 : g ∣ 3 := by rw [← hgcd3]; exact Nat.dvd_gcd hg_dvd_sum hg_dvd_q
  -- g ≠ 3 (would give 3 ∣ q').
  have hg_ne3 : g ≠ 3 := by
    intro hg3
    apply hnq'
    have : (3 : ℕ) ∣ q' := by rw [← hg3]; exact hg_dvd_q'
    exact this
  -- divisors of 3 are 1 or 3; exclude 3.  Bound g ≤ 3 first.
  have hg_le : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg_dvd_3
  show g = 1
  interval_cases g
  · simp at hg_dvd_3      -- g = 0: 0 ∣ 3 false.
  · rfl                    -- g = 1.
  · simp at hg_dvd_3      -- g = 2: 2 ∣ 3 false.
  · exact absurd rfl hg_ne3 -- g = 3 excluded.

/-- **Cube-sum descent, `3 ∣ C` branch (factored form).**
For coprime `A, B` with `3 ∣ A + B` (equivalently `3 ∣ C`) and `z ≠ 0`, a solution
`A³ + B³ = C^z` factors as

  `(A + B) · 3 · q' = C^z`,  with  `q' = (A² + B² − A·B) / 3`,  `Nat.Coprime (A + B) q'`.

This is the honest statement in the shared-`3` branch: the Eisenstein gcd is `3`
(not `1`), so the two factors `A + B` and `q = 3·q'` are **not** coprime, but the
"deflated" factor `q'` is coprime to `A + B`. We record the exact product
identity together with this coprimality; the further per-factor power extraction
is obstructed by the shared `3` and is not asserted here. **NEW.** -/
theorem cube_sum_descent_three {A B C z : ℕ} (hAB : Nat.Coprime A B)
    (h3 : 3 ∣ (A + B)) (_hz : z ≠ 0) (h : A ^ 3 + B ^ 3 = C ^ z) :
    (A + B) * 3 * ((A ^ 2 + B ^ 2 - A * B) / 3) = C ^ z ∧
      Nat.Coprime (A + B) ((A ^ 2 + B ^ 2 - A * B) / 3) := by
  refine ⟨?_, coprime_sum_quotient hAB h3⟩
  -- (A+B) · q = A³ + B³ = C^z, and q = 3 · q'.
  have hfact : (A + B) * (A ^ 2 + B ^ 2 - A * B) = C ^ z := by
    rw [cube_sum_factor_nat, h]
  have hq3 : (3 : ℕ) ∣ (A ^ 2 + B ^ 2 - A * B) := three_dvd_quadratic_of_three_dvd_sum h3
  obtain ⟨q', hq'⟩ := hq3
  have hdiv : (A ^ 2 + B ^ 2 - A * B) / 3 = q' := by
    rw [hq']; exact Nat.mul_div_cancel_left q' (by norm_num)
  rw [hdiv]
  rw [hq'] at hfact
  -- (A+B) · (3 · q') = (A+B)·3·q'.
  rw [← hfact]; ring

end BealCubeDescentThree
