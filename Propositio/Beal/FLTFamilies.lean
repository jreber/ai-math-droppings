import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# Beal `(p,p,z)` for `p ∣ z` — infinite families closed unconditionally via FLT-p

If `A^p + B^p = C^z` with `p ∣ z`, write `z = p·m`; then `C^z = (C^m)^p`, so the
equation is `A^p + B^p = (C^m)^p`, an instance of Fermat's Last Theorem for exponent
`p`. mathlib provides `fermatLastTheoremThree` and `fermatLastTheoremFour`, so the
Beal equation has NO positive solution whenever the equal exponents are `3` (resp. `4`)
and `z` is a multiple of `3` (resp. `4`). These are infinite families of the `(p,p,z)`
case closed unconditionally (no descent, no ABC, no modularity) — complementing the
cyclotomic descent (which handles other `z` only structurally).

`FermatLastTheoremFor n` unfolds to `∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0 → a^n + b^n ≠ c^n`.
-/

namespace BealFLTFamilies

/-- **`beal_of_flt_common_factor` (the general principle).** If `d` is an exponent for
which Fermat's Last Theorem holds (`FermatLastTheoremFor d`) and `d` divides all three
Beal exponents `x, y, z`, then `A^x + B^y = C^z` has no positive solution: the equation
is `(A^{x/d})^d + (B^{y/d})^d = (C^{z/d})^d`. The two concrete families below are the
`d = 3` and `d = 4` instances (the only exponents with FLT in this mathlib pin). Any
future `FermatLastTheoremFor d` plugs straight in. -/
theorem beal_of_flt_common_factor {A B C x y z d : ℕ}
    (hd : FermatLastTheoremFor d)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : d ∣ x) (hy : d ∣ y) (hz : d ∣ z)
    (h : A ^ x + B ^ y = C ^ z) : False := by
  obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy; obtain ⟨k, rfl⟩ := hz
  have hrw : (A ^ i) ^ d + (B ^ j) ^ d = (C ^ k) ^ d := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm i d, Nat.mul_comm j d,
      Nat.mul_comm k d]; exact h
  exact hd (A ^ i) (B ^ j) (C ^ k)
    (pow_ne_zero i hA) (pow_ne_zero j hB) (pow_ne_zero k hC) hrw

/-- **`beal_33z_of_three_dvd_z`.** No positive solution of `A³ + B³ = Cᶻ` when `3 ∣ z`
(reduces to FLT-3 via `Cᶻ = (C^{z/3})³`). An infinite family of the `(3,3,z)` case,
closed unconditionally. -/
theorem beal_33z_of_three_dvd_z {A B C z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hz : 3 ∣ z)
    (h : A ^ 3 + B ^ 3 = C ^ z) : False := by
  obtain ⟨m, rfl⟩ := hz
  have hrw : A ^ 3 + B ^ 3 = (C ^ m) ^ 3 := by
    rw [h, ← pow_mul, Nat.mul_comm]
  exact fermatLastTheoremThree A B (C ^ m) hA hB (pow_ne_zero m hC) hrw

/-- **`beal_44z_of_four_dvd_z`.** No positive solution of `A⁴ + B⁴ = Cᶻ` when `4 ∣ z`
(reduces to FLT-4 via `Cᶻ = (C^{z/4})⁴`). An infinite family of the `(4,4,z)` case,
closed unconditionally. -/
theorem beal_44z_of_four_dvd_z {A B C z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hz : 4 ∣ z)
    (h : A ^ 4 + B ^ 4 = C ^ z) : False := by
  obtain ⟨m, rfl⟩ := hz
  have hrw : A ^ 4 + B ^ 4 = (C ^ m) ^ 4 := by
    rw [h, ← pow_mul, Nat.mul_comm]
  exact fermatLastTheoremFour A B (C ^ m) hA hB (pow_ne_zero m hC) hrw

/-- **`beal_of_three_dvd_exponents` (general).** No positive solution of
`A^x + B^y = C^z` whenever `3 ∣ x`, `3 ∣ y`, `3 ∣ z`: the equation becomes
`(A^{x/3})³ + (B^{y/3})³ = (C^{z/3})³`, an instance of FLT-3. Subsumes
`beal_33z_of_three_dvd_z`. This closes EVERY Beal triple whose three exponents are all
multiples of 3 — an infinite family, unconditional. -/
theorem beal_of_three_dvd_exponents {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 3 ∣ x) (hy : 3 ∣ y) (hz : 3 ∣ z)
    (h : A ^ x + B ^ y = C ^ z) : False := by
  obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy; obtain ⟨k, rfl⟩ := hz
  have hrw : (A ^ i) ^ 3 + (B ^ j) ^ 3 = (C ^ k) ^ 3 := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm i 3, Nat.mul_comm j 3,
      Nat.mul_comm k 3]; exact h
  exact fermatLastTheoremThree (A ^ i) (B ^ j) (C ^ k)
    (pow_ne_zero i hA) (pow_ne_zero j hB) (pow_ne_zero k hC) hrw

/-- **`beal_of_four_dvd_exponents` (general).** No positive solution of
`A^x + B^y = C^z` whenever `4 ∣ x`, `4 ∣ y`, `4 ∣ z` (instance of FLT-4). Subsumes
`beal_44z_of_four_dvd_z`. -/
theorem beal_of_four_dvd_exponents {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 4 ∣ x) (hy : 4 ∣ y) (hz : 4 ∣ z)
    (h : A ^ x + B ^ y = C ^ z) : False := by
  obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy; obtain ⟨k, rfl⟩ := hz
  have hrw : (A ^ i) ^ 4 + (B ^ j) ^ 4 = (C ^ k) ^ 4 := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm i 4, Nat.mul_comm j 4,
      Nat.mul_comm k 4]; exact h
  exact fermatLastTheoremFour (A ^ i) (B ^ j) (C ^ k)
    (pow_ne_zero i hA) (pow_ne_zero j hB) (pow_ne_zero k hC) hrw

/-- Restatement as a non-existence (the Beal conclusion `≠`) for `(3,3,z)`, `3 ∣ z`. -/
theorem beal_33z_ne_of_three_dvd_z {A B C z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hz : 3 ∣ z) :
    A ^ 3 + B ^ 3 ≠ C ^ z :=
  fun h => beal_33z_of_three_dvd_z hA hB hC hz h

/-- Restatement as a non-existence for `(4,4,z)`, `4 ∣ z`. -/
theorem beal_44z_ne_of_four_dvd_z {A B C z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hz : 4 ∣ z) :
    A ^ 4 + B ^ 4 ≠ C ^ z :=
  fun h => beal_44z_of_four_dvd_z hA hB hC hz h

end BealFLTFamilies
