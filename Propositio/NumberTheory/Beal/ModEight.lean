import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Beal local obstruction at `p = 2` — mod-4 and mod-8 classes (Lean 4 mirror)

Lean 4 port of the project-specific Beal **even-even / mod-8 parity-class**
obstruction of the LaTTe development under `src/ai_math/beal/`.

For a putative Beal solution `A^x + B^y = C^z` with `C` even (so `z ≥ 3` forces
`8 ∣ C^z`), the residue of the left-hand side mod 8 is pinned by the parities of
the exponents `x, y` once `A, B` are odd (which holds when `A, B` are coprime —
the Beal setting). The LaTTe sources prove three exponent-parity classes:

* **even/even** (`x = 2i`, `y = 2j`): `A^(2i) + B^(2j) ≡ 2 (mod 8)`, hence
  `8 ∤ A^(2i) + B^(2j)` — a genuine *obstruction* (T8), sharpening the mod-4
  even-even obstruction (sister file `even_even_mod_four.clj`).
* **even/odd** (`x = 2i`, `y = 2j+1`): `A^(2i) + B^(2j+1) ≡ 1 + B (mod 8)` — a
  *transfer*: `8 ∣ LHS ⇒ 8 ∣ (1 + B)`, i.e. `B ≡ 7 (mod 8)` (T9).
* **odd/odd** (`x = 2i+1`, `y = 2j+1`): `A^(2i+1) + B^(2j+1) ≡ A + B (mod 8)` —
  a *transfer*: `8 ∣ LHS ⇒ 8 ∣ (A + B)` (T10).

These are elementary, fully decidable modular facts. The clean Lean route pushes
everything onto `ZMod 8` (resp. `ZMod 4`): for an odd integer `b`, every odd
residue of `ZMod 8` squares to `1`, so `(b : ZMod 8)^2 = 1`; the power, self, and
sum congruences then follow by ring arithmetic on `ZMod 8`. The finite
"odd residue squares to one" facts are discharged by `decide` (NOT
`native_decide`, so no `Lean.ofReduceBool` enters the axiom set).

House style follows `BealEisenstein.lean` / `BealDensity.lean`: a module doc
citing the LaTTe siblings, and each theorem carries a doc-comment ending in a
`LaTTe sibling: src/ai_math/beal/<file>.clj :: <name>` cross-reference.

We state the headline congruences with mathlib's `Int.ModEq` (`a ≡ b [ZMOD n]`),
the faithful analogue of LaTTe's `(congruent a b n)`, and the obstructions with
`¬ (n : ℤ) ∣ S`, the analogue of `(not (divides n S))`. Odd exponents `2j+1`
mirror LaTTe's `(succ (* (two) j))`.

LaTTe siblings:
* `src/ai_math/beal/even_even_mod_four.clj` (the mod-4 even-even obstruction).
* `src/ai_math/beal/mod_eight_classes.clj` (the mod-8 sharpening + class transfers).

Dependency policy: mathlib4 permitted. Typecheck with
`lake env lean BealModEight.lean`.

Key mathlib lemmas relied on:
* `decide` — the finite `ZMod 8` / `ZMod 4` residue computations.
* `pow_mul`, `pow_succ`, `one_pow`, `one_mul` — power bookkeeping over `ZMod n`.
* `ZMod.intCast_eq_intCast_iff` — bridge `(a : ZMod n) = (b : ZMod n) ↔ a ≡ b [ZMOD n]`.
* `ZMod.intCast_zmod_eq_zero_iff_dvd` — bridge `(x : ZMod n) = 0 ↔ (n:ℤ) ∣ x`.
-/

namespace BealModEight

/-! ## 1. Core residue facts on `ZMod 8` for odd integers -/

/-- **Odd square is `1 mod 8`** (mod-8 core; T3).
For any odd integer `A`, `(A : ZMod 8)^2 = 1`. Writing `A = 2m+1` and reducing,
the claim becomes a finite check over the residue `(m : ZMod 8)`, dispatched by
`decide` (every odd residue of `ZMod 8`, namely `1,3,5,7`, squares to `1`).

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`odd-square-cong-one-mod-eight`. -/
theorem odd_sq_zmod8 {A : ℤ} (hA : Odd A) : (A : ZMod 8) ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := hA
  push_cast
  generalize (m : ZMod 8) = x
  revert x
  decide

/-- **Even power is `1 mod 8`** (T4).
For odd `A` and any `i : ℕ`, `(A : ZMod 8)^(2*i) = 1`.

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`odd-pow-even-cong-one-mod-eight`. -/
theorem odd_pow_even_zmod8 {A : ℤ} (hA : Odd A) (i : ℕ) :
    (A : ZMod 8) ^ (2 * i) = 1 := by
  rw [pow_mul, odd_sq_zmod8 hA, one_pow]

/-- **Odd power is self `mod 8`** (T5).
For odd `B` and any `j : ℕ`, `(B : ZMod 8)^(2*j+1) = (B : ZMod 8)`.

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`odd-pow-odd-cong-self-mod-eight`. -/
theorem odd_pow_odd_zmod8 {B : ℤ} (hB : Odd B) (j : ℕ) :
    (B : ZMod 8) ^ (2 * j + 1) = (B : ZMod 8) := by
  rw [pow_succ, odd_pow_even_zmod8 hB, one_mul]

/-! ## 2. The three exponent-parity sum congruences mod 8 -/

/-- **even/even sum ≡ 2 (mod 8)** (T7).
For odd `A, B` and `i, j : ℕ`, `A^(2i) + B^(2j) ≡ 2 [ZMOD 8]`.

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`even-even-sum-cong-two-mod-eight`. -/
theorem even_even_sum_mod8 {A B : ℤ} (hA : Odd A) (hB : Odd B) (i j : ℕ) :
    A ^ (2 * i) + B ^ (2 * j) ≡ 2 [ZMOD 8] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  push_cast
  rw [odd_pow_even_zmod8 hA, odd_pow_even_zmod8 hB]
  decide

/-- **even/odd sum ≡ 1 + B (mod 8)** (T9, transfer).
For odd `A, B` and `i, j : ℕ`, `A^(2i) + B^(2j+1) ≡ 1 + B [ZMOD 8]`.

Beal implication: `8 ∣ A^(2i) + B^(2j+1) ⇒ 8 ∣ (1 + B)` (see
`even_odd_transfer_mod8`).

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`even-odd-sum-cong-one-plus-B-mod-eight`. -/
theorem even_odd_sum_mod8 {A B : ℤ} (hA : Odd A) (hB : Odd B) (i j : ℕ) :
    A ^ (2 * i) + B ^ (2 * j + 1) ≡ 1 + B [ZMOD 8] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  push_cast
  rw [odd_pow_even_zmod8 hA, odd_pow_odd_zmod8 hB]

/-- **odd/odd sum ≡ A + B (mod 8)** (T10, transfer).
For odd `A, B` and `i, j : ℕ`, `A^(2i+1) + B^(2j+1) ≡ A + B [ZMOD 8]`.

Beal implication: `8 ∣ A^(2i+1) + B^(2j+1) ⇒ 8 ∣ (A + B)` (see
`odd_odd_transfer_mod8`).

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`odd-odd-sum-cong-A-plus-B-mod-eight`. -/
theorem odd_odd_sum_mod8 {A B : ℤ} (hA : Odd A) (hB : Odd B) (i j : ℕ) :
    A ^ (2 * i + 1) + B ^ (2 * j + 1) ≡ A + B [ZMOD 8] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  push_cast
  rw [odd_pow_odd_zmod8 hA, odd_pow_odd_zmod8 hB]

/-! ## 3. The even-even obstruction mod 8 (HEADLINE, T8) and its transfers -/

/-- **Even-even mod-8 obstruction (HEADLINE)** (T8).
For odd integers `A, B` and naturals `i, j`, `8 ∤ A^(2i) + B^(2j)`.

Beal interpretation: a solution `A^x + B^y = C^z` with `x, y` both even and
`A, B` odd (e.g. coprime) cannot have `C` even — for even `C` with `z ≥ 3` one
has `8 ∣ C^z`, yet the left-hand side is `≡ 2 (mod 8)`. This is the mod-8
sharpening of the mod-4 even-even obstruction (`even_even_obstruction_mod4`).

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`even-even-obstruction-mod-eight`. -/
theorem even_even_obstruction_mod8 {A B : ℤ} (hA : Odd A) (hB : Odd B)
    (i j : ℕ) : ¬ (8 : ℤ) ∣ (A ^ (2 * i) + B ^ (2 * j)) := by
  intro hdvd
  -- `8 ∣ S` means `S ≡ 0 (mod 8)`; but `S ≡ 2 (mod 8)`, forcing `8 ∣ 2`.
  have h0 : A ^ (2 * i) + B ^ (2 * j) ≡ 0 [ZMOD 8] := Int.modEq_zero_iff_dvd.mpr hdvd
  have h2 : A ^ (2 * i) + B ^ (2 * j) ≡ 2 [ZMOD 8] := even_even_sum_mod8 hA hB i j
  have : (2 : ℤ) ≡ 0 [ZMOD 8] := (h2.symm.trans h0)
  exact absurd (Int.modEq_zero_iff_dvd.mp this) (by decide)

/-- **even/odd transfer** (T9 corollary).
For odd `A, B`, if `8 ∣ A^(2i) + B^(2j+1)` then `8 ∣ (1 + B)` (equivalently
`B ≡ 7 (mod 8)`).

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`even-odd-sum-cong-one-plus-B-mod-eight` (Beal implication). -/
theorem even_odd_transfer_mod8 {A B : ℤ} (hA : Odd A) (hB : Odd B) (i j : ℕ)
    (hdvd : (8 : ℤ) ∣ (A ^ (2 * i) + B ^ (2 * j + 1))) : (8 : ℤ) ∣ (1 + B) := by
  have h0 : A ^ (2 * i) + B ^ (2 * j + 1) ≡ 0 [ZMOD 8] :=
    Int.modEq_zero_iff_dvd.mpr hdvd
  have hsum : A ^ (2 * i) + B ^ (2 * j + 1) ≡ 1 + B [ZMOD 8] := even_odd_sum_mod8 hA hB i j
  exact Int.modEq_zero_iff_dvd.mp (hsum.symm.trans h0)

/-- **odd/odd transfer** (T10 corollary).
For odd `A, B`, if `8 ∣ A^(2i+1) + B^(2j+1)` then `8 ∣ (A + B)`.

LaTTe sibling: `src/ai_math/beal/mod_eight_classes.clj` ::
`odd-odd-sum-cong-A-plus-B-mod-eight` (Beal implication). -/
theorem odd_odd_transfer_mod8 {A B : ℤ} (hA : Odd A) (hB : Odd B) (i j : ℕ)
    (hdvd : (8 : ℤ) ∣ (A ^ (2 * i + 1) + B ^ (2 * j + 1))) : (8 : ℤ) ∣ (A + B) := by
  have h0 : A ^ (2 * i + 1) + B ^ (2 * j + 1) ≡ 0 [ZMOD 8] :=
    Int.modEq_zero_iff_dvd.mpr hdvd
  have hsum : A ^ (2 * i + 1) + B ^ (2 * j + 1) ≡ A + B [ZMOD 8] := odd_odd_sum_mod8 hA hB i j
  exact Int.modEq_zero_iff_dvd.mp (hsum.symm.trans h0)

/-! ## 4. The mod-4 sister obstruction (even-even at `p = 2`)

Mirrors `even_even_mod_four.clj`: for odd `A, B`, `A^(2i) + B^(2j) ≡ 2 (mod 4)`,
hence `4 ∤ A^(2i) + B^(2j)`. (The mod-8 obstruction above is strictly stronger,
but we port the mod-4 statement for faithfulness with the sister file.)
-/

/-- **Odd square is `1 mod 4`** (`odd-square-cong-one-mod-four`).
For odd `A`, `(A : ZMod 4)^2 = 1`.

LaTTe sibling: `src/ai_math/beal/even_even_mod_four.clj` ::
`odd-square-cong-one-mod-four`. -/
theorem odd_sq_zmod4 {A : ℤ} (hA : Odd A) : (A : ZMod 4) ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := hA
  push_cast
  generalize (m : ZMod 4) = x
  revert x
  decide

/-- **Even power is `1 mod 4`** (`cong-one-pow-even` at `m = 4`).
For odd `A` and `i : ℕ`, `(A : ZMod 4)^(2*i) = 1`.

LaTTe sibling: `src/ai_math/beal/even_even_mod_four.clj` :: `cong-one-pow-even`. -/
theorem odd_pow_even_zmod4 {A : ℤ} (hA : Odd A) (i : ℕ) :
    (A : ZMod 4) ^ (2 * i) = 1 := by
  rw [pow_mul, odd_sq_zmod4 hA, one_pow]

/-- **even/even sum ≡ 2 (mod 4)** (`even-even-sum-cong-two-mod-four`).
For odd `A, B` and `i, j : ℕ`, `A^(2i) + B^(2j) ≡ 2 [ZMOD 4]`.

LaTTe sibling: `src/ai_math/beal/even_even_mod_four.clj` ::
`even-even-sum-cong-two-mod-four`. -/
theorem even_even_sum_mod4 {A B : ℤ} (hA : Odd A) (hB : Odd B) (i j : ℕ) :
    A ^ (2 * i) + B ^ (2 * j) ≡ 2 [ZMOD 4] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  push_cast
  rw [odd_pow_even_zmod4 hA, odd_pow_even_zmod4 hB]
  decide

/-- **Even-even mod-4 obstruction** (`even-even-obstruction-mod-four`).
For odd integers `A, B` and naturals `i, j`, `4 ∤ A^(2i) + B^(2j)`.

Beal interpretation: a solution `A^x + B^y = C^z` with `x, y` even and `A, B`
odd forces `C` odd (for even `C`, `z ≥ 2` gives `4 ∣ C^z`, but the LHS is
`≡ 2 (mod 4)`).

LaTTe sibling: `src/ai_math/beal/even_even_mod_four.clj` ::
`even-even-obstruction-mod-four`. -/
theorem even_even_obstruction_mod4 {A B : ℤ} (hA : Odd A) (hB : Odd B)
    (i j : ℕ) : ¬ (4 : ℤ) ∣ (A ^ (2 * i) + B ^ (2 * j)) := by
  intro hdvd
  have h0 : A ^ (2 * i) + B ^ (2 * j) ≡ 0 [ZMOD 4] := Int.modEq_zero_iff_dvd.mpr hdvd
  have h2 : A ^ (2 * i) + B ^ (2 * j) ≡ 2 [ZMOD 4] := even_even_sum_mod4 hA hB i j
  have : (2 : ℤ) ≡ 0 [ZMOD 4] := (h2.symm.trans h0)
  exact absurd (Int.modEq_zero_iff_dvd.mp this) (by decide)

end BealModEight
