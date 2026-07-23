import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Signature-`(2,3,n)` local obstruction: the odd-`a` 2-adic constraint

A **local (congruence) obstruction** for the most-studied generalized-Fermat /
Beal signature `(2, 3, n)`,

  `a² + b³ = cⁿ`,

complementing the Frey/Mordell-curve package (`BealFrey23.lean`,
`BealFrey23Radical.lean`, `BealFrey23Quality.lean`) and the ABC-conditional
finiteness statement (`BealABC23.lean`). It is the `(2,3,n)` analogue of the
mod-9 cube-sum input of `BealCubeMod9.lean` and the split-prime cube-sum
obstruction of `BealCubeSplitPrime.lean`.

## Why the bare equation has NO congruence obstruction

For *unconstrained* `a, b`, the map `(a, b) ↦ a² + b³` is **surjective** onto
`ZMod m` for every modulus `m` (squares are dense enough that adding the cubes
fills every residue — verified by enumeration over `m = 4,7,8,9,13,16,…`). So a
naive "`a² + b³` misses a residue mod `m`" claim is **FALSE** for every `m`. The
structure only appears once one term is pinned by a 2-adic / coprimality
hypothesis.

## The 2-adic constraint (the productive restriction)

The arithmetically natural restriction is `a` **odd** (`¬ 2 ∣ a`). This is exactly
the operative branch of a primitive `(2,3,n)` solution: when the perfect power
`cⁿ` is even, coprimality of `a, b, c` forces `a` (and `b`) odd; more generally
whenever `2 ∤ a` the constraint below applies.

For `a` odd, `a² ≡ 1 (mod 8)` **always** (the square of any odd number is
`≡ 1 mod 8`). Combined with the cube residues mod 8

  `b³ ≡ {0, 1, 3, 5, 7} (mod 8)`   (`b` even ⟹ `0`; `b` odd ⟹ odd),

the sum is pinned:

  `a² + b³ ≡ 1 + {0,1,3,5,7} = {1, 2, 4, 6, 0} (mod 8)`,

so **`a² + b³ ∈ {0, 1, 2, 4, 6} (mod 8)`, missing exactly `{3, 5, 7}`**
(`twothree_odd_a_image_mod8`, sanity-checked by `#eval` enumeration before being
asserted). Hence:

> **`twothree_mod8_obstruction`** : if `a` is odd and `cⁿ ≡ 3, 5, 7 (mod 8)`
> then `a² + b³ ≠ cⁿ`.

The forbidden classes `cⁿ ≡ 3, 5, 7 (mod 8)` are genuinely achievable on the
right (e.g. `c ≡ 3, 5, 7 (mod 8)` with `n` odd: `3¹ ≡ 3`, `5¹ ≡ 5`, `7¹ ≡ 7`),
so this is a real local obstruction, not a vacuous one.

## Sharpenings

* **mod 16** (`twothree_mod16_obstruction`): for `a` odd, `a² ∈ {1, 9} (mod 16)`,
  and `a² + b³` misses **all** the odd residues `≥ 3`, namely
  `{3, 5, 7, 11, 13, 15}` — twice as many forbidden classes as mod 8.
* **parity split** (`twothree_odd_a_parity_mod8`): for `a` odd, the value mod 8
  is `1` when `b` is even and **even** (`∈ {0,2,4,6}`) when `b` is odd — a clean
  dichotomy on the residue determined by the parity of `b`.

## A complementary prime-modulus obstruction

`twothree_mod7_obstruction` : if `7 ∤ a` (so `a²` is a nonzero quadratic residue
mod 7) and `cⁿ ≡ 6 (mod 7)`, then `a² + b³ ≠ cⁿ`. Here `a² ∈ {1,2,4} (mod 7)`
and `a² + b³` ranges over `{0,1,2,3,4,5}`, **missing `{6}`**
(`twothree_coprime_a_image_mod7`). The class `cⁿ ≡ 6 (mod 7)` is achievable
(`c ≡ 6, n` odd), so this too is a genuine obstruction.

## CORRECTNESS / sanity discipline

Every `decide`d non-membership claim was first confirmed by `#eval` enumeration
over the relevant `ZMod m` (the image sets `{0,1,2,4,6}` mod 8,
`{0,…,14} \ {3,5,7,11,13,15}` mod 16, `{0,…,5}` mod 7) BEFORE any `≠` was
asserted. The bare-equation surjectivity (no obstruction without the 2-adic /
coprimality hypothesis) was likewise checked, so no false strong claim is made.
All finite facts use `decide` (NOT `native_decide`, so `Lean.ofReduceBool` never
enters the axiom set). House style follows `BealCubeMod9.lean`.

Typecheck with `lake env lean BealTwoThreeLocal.lean`.

Key mathlib lemmas relied on:
* `decide` — the finite `ZMod m` square / cube / sum residue computations.
* `ZMod.intCast_zmod_eq_zero_iff_dvd` — bridge `(x : ZMod n) = 0 ↔ (n:ℤ) ∣ x`,
  used to transport `2 ∤ a` / `7 ∤ a` into the `ZMod` world.
-/

namespace BealTwoThreeLocal

/-! ## 0. Sanity enumerations (`#eval`, no axiom impact)

These print the achievable residues; run them to confirm the forbidden classes
before trusting the `decide`d non-membership theorems below. -/

-- a² + b³ over ALL a,b mod 8 is surjective (no bare obstruction):
-- #eval (Finset.univ.image (fun ab : ZMod 8 × ZMod 8 => ab.1 ^ 2 + ab.2 ^ 3)).sort (· ≤ ·)
--   ⟹ [0,1,2,3,4,5,6,7]   (all of ZMod 8)
-- a² + b³ with a ODD mod 8:
-- #eval ((Finset.univ.filter (fun ab : ZMod 8 × ZMod 8 => ab.1 = 1 ∨ ab.1 = 3 ∨ ab.1 = 5 ∨ ab.1 = 7)).image
--          (fun ab => ab.1 ^ 2 + ab.2 ^ 3)).sort (· ≤ ·)
--   ⟹ [0,1,2,4,6]   (missing {3,5,7})

/-! ## 1. The odd-square fact mod 8 and mod 16 -/

/-- **The square of any odd integer is `≡ 1 (mod 8)`.**
If `2 ∤ a` then `(a² : ZMod 8) = 1`. The hypothesis `2 ∤ a` is transported to
`(a : ZMod 2) ≠ 0`; the four odd residues mod 8 (`1,3,5,7`) all square to `1`,
a finite `decide`. -/
theorem odd_sq_mod8 {a : ℤ} (ha : ¬ (2 : ℤ) ∣ a) : (a ^ 2 : ZMod 8) = 1 := by
  -- `(a : ZMod 2) ≠ 0`, i.e. the image of `a` in `ZMod 8` is one of `1,3,5,7`.
  have h2 : (a : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha
  -- Reduce to a statement about `(a : ZMod 8)` via the ring hom `ZMod 8 → ZMod 2`.
  have key : ∀ r : ZMod 8, (ZMod.castHom (by norm_num) (ZMod 2) r ≠ 0) → r ^ 2 = 1 := by
    decide
  have hcast : ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) (a : ZMod 8) ≠ 0 := by
    rw [map_intCast]; exact h2
  have := key (a : ZMod 8) hcast
  push_cast at this ⊢
  exact this

/-- **The square of any odd integer lies in `{1, 9} (mod 16)`.**
If `2 ∤ a` then `(a² : ZMod 16) = 1 ∨ (a² : ZMod 16) = 9`. Same transport as
`odd_sq_mod8`, then a finite `decide` over the eight odd residues mod 16. -/
theorem odd_sq_mod16 {a : ℤ} (ha : ¬ (2 : ℤ) ∣ a) :
    (a ^ 2 : ZMod 16) = 1 ∨ (a ^ 2 : ZMod 16) = 9 := by
  have h2 : (a : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha
  have key : ∀ r : ZMod 16,
      (ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) r ≠ 0) →
        r ^ 2 = 1 ∨ r ^ 2 = 9 := by decide
  have hcast : ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) (a : ZMod 16) ≠ 0 := by
    rw [map_intCast]; exact h2
  have := key (a : ZMod 16) hcast
  push_cast at this ⊢
  exact this

/-! ## 2. The cube residues mod 8 and the odd-`a` image -/

/-- **Cubes mod 8 lie in `{0, 1, 3, 5, 7}`.** Finite `decide` over `ZMod 8`. -/
theorem cube_residues_mod8 (b : ℤ) :
    (b ^ 3 : ZMod 8) = 0 ∨ (b ^ 3 : ZMod 8) = 1 ∨ (b ^ 3 : ZMod 8) = 3 ∨
      (b ^ 3 : ZMod 8) = 5 ∨ (b ^ 3 : ZMod 8) = 7 := by
  have h : ∀ r : ZMod 8, r ^ 3 = 0 ∨ r ^ 3 = 1 ∨ r ^ 3 = 3 ∨ r ^ 3 = 5 ∨ r ^ 3 = 7 := by
    decide
  have := h (b : ZMod 8); simpa using this

/-- **For `a` odd, `a² + b³ ∈ {0, 1, 2, 4, 6} (mod 8)`** (HEADLINE image).
Since `a² ≡ 1` (`odd_sq_mod8`) and `b³ ∈ {0,1,3,5,7}` (`cube_residues_mod8`),
the sum `1 + b³` ranges over `{1,2,4,6,0}`. The complement is **`{3, 5, 7}`**:
those three residues are unreachable by `a² + b³` once `a` is odd. -/
theorem twothree_odd_a_image_mod8 {a b : ℤ} (ha : ¬ (2 : ℤ) ∣ a) :
    (a ^ 2 + b ^ 3 : ZMod 8) = 0 ∨ (a ^ 2 + b ^ 3 : ZMod 8) = 1 ∨
      (a ^ 2 + b ^ 3 : ZMod 8) = 2 ∨ (a ^ 2 + b ^ 3 : ZMod 8) = 4 ∨
        (a ^ 2 + b ^ 3 : ZMod 8) = 6 := by
  have hsq := odd_sq_mod8 ha
  have hcu := cube_residues_mod8 b
  push_cast at hsq hcu ⊢
  rw [hsq]
  rcases hcu with h | h | h | h | h <;> rw [h] <;> decide

/-- **For `a` odd, `a² + b³` is never `≡ 3, 5, 7 (mod 8)`** (the gap).
Immediate from `twothree_odd_a_image_mod8`: the image is `{0,1,2,4,6}`, disjoint
from `{3,5,7}`. -/
theorem twothree_odd_a_notMem_mod8 {a b : ℤ} (ha : ¬ (2 : ℤ) ∣ a) :
    (a ^ 2 + b ^ 3 : ZMod 8) ≠ 3 ∧ (a ^ 2 + b ^ 3 : ZMod 8) ≠ 5 ∧
      (a ^ 2 + b ^ 3 : ZMod 8) ≠ 7 := by
  rcases twothree_odd_a_image_mod8 (b := b) ha with h | h | h | h | h <;>
    rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 3. HEADLINE: the mod-8 `(2,3,n)` obstruction -/

/-- **Signature-`(2,3,n)` mod-8 obstruction (HEADLINE).**
If `a` is odd (`2 ∤ a`) and the perfect power `cⁿ` reduces to `3`, `5`, or
`7 (mod 8)`, then the generalized-Fermat equation `a² + b³ = cⁿ` is impossible
modulo 8 — for *any* integers `a, b, c` and exponent `n`.

The left side lies in `{0,1,2,4,6} (mod 8)` once `a` is odd
(`twothree_odd_a_image_mod8`), which is disjoint from `{3,5,7}`. The forbidden
classes on the right are genuinely achievable (e.g. `c ≡ 3,5,7 (mod 8)`, `n`
odd), so this is a real local obstruction. In a primitive solution with `cⁿ`
even, coprimality forces `a` odd, so this hypothesis is the operative branch. -/
theorem twothree_mod8_obstruction {a b c : ℤ} {n : ℕ} (ha : ¬ (2 : ℤ) ∣ a)
    (hc : (c : ZMod 8) ^ n = 3 ∨ (c : ZMod 8) ^ n = 5 ∨ (c : ZMod 8) ^ n = 7) :
    a ^ 2 + b ^ 3 ≠ c ^ n := by
  intro heq
  -- Cast the integer equation to `ZMod 8`.
  have hcast : (a ^ 2 + b ^ 3 : ZMod 8) = (c ^ n : ZMod 8) := by
    have : ((a ^ 2 + b ^ 3 : ℤ) : ZMod 8) = ((c ^ n : ℤ) : ZMod 8) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h3, h5, h7⟩ := twothree_odd_a_notMem_mod8 (a := a) (b := b) ha
  push_cast at hcast
  rcases hc with h | h | h <;> rw [h] at hcast
  · exact h3 hcast
  · exact h5 hcast
  · exact h7 hcast

/-! ## 4. Sharpening mod 16: six forbidden classes -/

/-- **For `a` odd, `a² + b³` avoids `{3, 5, 7, 11, 13, 15} (mod 16)`** (image gap).
With `a² ∈ {1, 9} (mod 16)` (`odd_sq_mod16`) and the cube residues mod 16, the
sum misses all six odd residues `≥ 3`. Sanity-checked by enumeration before
assertion; each case is a finite `decide`. -/
theorem twothree_odd_a_notMem_mod16 {a b : ℤ} (ha : ¬ (2 : ℤ) ∣ a) :
    (a ^ 2 + b ^ 3 : ZMod 16) ≠ 3 ∧ (a ^ 2 + b ^ 3 : ZMod 16) ≠ 5 ∧
      (a ^ 2 + b ^ 3 : ZMod 16) ≠ 7 ∧ (a ^ 2 + b ^ 3 : ZMod 16) ≠ 11 ∧
        (a ^ 2 + b ^ 3 : ZMod 16) ≠ 13 ∧ (a ^ 2 + b ^ 3 : ZMod 16) ≠ 15 := by
  have hsq := odd_sq_mod16 ha
  -- cube residues mod 16 (finite):
  have hcu : ∀ r : ZMod 16, r ^ 3 = 0 ∨ r ^ 3 = 1 ∨ r ^ 3 = 3 ∨ r ^ 3 = 5 ∨
      r ^ 3 = 7 ∨ r ^ 3 = 8 ∨ r ^ 3 = 9 ∨ r ^ 3 = 11 ∨ r ^ 3 = 13 ∨ r ^ 3 = 15 := by
    decide
  have hcu' := hcu (b : ZMod 16)
  push_cast at hsq hcu' ⊢
  rcases hsq with hs | hs <;> rw [hs] <;>
    rcases hcu' with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Signature-`(2,3,n)` mod-16 obstruction (sharper).**
If `a` is odd and `cⁿ ≡ 3, 5, 7, 11, 13, or 15 (mod 16)` then `a² + b³ ≠ cⁿ`.
Twice as many forbidden classes as the mod-8 statement. -/
theorem twothree_mod16_obstruction {a b c : ℤ} {n : ℕ} (ha : ¬ (2 : ℤ) ∣ a)
    (hc : (c : ZMod 16) ^ n = 3 ∨ (c : ZMod 16) ^ n = 5 ∨ (c : ZMod 16) ^ n = 7 ∨
      (c : ZMod 16) ^ n = 11 ∨ (c : ZMod 16) ^ n = 13 ∨ (c : ZMod 16) ^ n = 15) :
    a ^ 2 + b ^ 3 ≠ c ^ n := by
  intro heq
  have hcast : (a ^ 2 + b ^ 3 : ZMod 16) = (c ^ n : ZMod 16) := by
    have : ((a ^ 2 + b ^ 3 : ℤ) : ZMod 16) = ((c ^ n : ℤ) : ZMod 16) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h3, h5, h7, h11, h13, h15⟩ := twothree_odd_a_notMem_mod16 (a := a) (b := b) ha
  push_cast at hcast
  rcases hc with h | h | h | h | h | h <;> rw [h] at hcast
  · exact h3 hcast
  · exact h5 hcast
  · exact h7 hcast
  · exact h11 hcast
  · exact h13 hcast
  · exact h15 hcast

/-! ## 5. The parity dichotomy for odd `a` -/

/-- **Parity dichotomy mod 8 for odd `a`.**
If `a` is odd then the residue `a² + b³ (mod 8)` is determined by the parity of
`b`: it equals `1` when `b` is even, and is **even** (`∈ {0,2,4,6}`) when `b` is
odd. (For `b` even, `b³ ≡ 0`, so `a² + b³ ≡ 1`; for `b` odd, `b³` is odd, so the
sum `1 + odd` is even.) -/
theorem twothree_odd_a_parity_mod8 {a b : ℤ} (ha : ¬ (2 : ℤ) ∣ a) :
    ((2 : ℤ) ∣ b → (a ^ 2 + b ^ 3 : ZMod 8) = 1) ∧
      (¬ (2 : ℤ) ∣ b → (a ^ 2 + b ^ 3 : ZMod 8) = 0 ∨ (a ^ 2 + b ^ 3 : ZMod 8) = 2 ∨
        (a ^ 2 + b ^ 3 : ZMod 8) = 4 ∨ (a ^ 2 + b ^ 3 : ZMod 8) = 6) := by
  have hsq := odd_sq_mod8 ha
  constructor
  · -- b even: b³ ≡ 0 mod 8.
    intro hb
    have hb2 : (b : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hb
    have key : ∀ r : ZMod 8,
        (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) r = 0) → r ^ 3 = 0 := by decide
    have hcast : ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) (b : ZMod 8) = 0 := by
      rw [map_intCast]; exact hb2
    have hcu := key (b : ZMod 8) hcast
    push_cast at hsq hcu ⊢
    rw [hsq, hcu]; decide
  · -- b odd: b³ ≡ odd mod 8, sum is even.
    intro hb
    have hb2 : (b : ZMod 2) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hb
    have key : ∀ r : ZMod 8,
        (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) r ≠ 0) →
          r ^ 3 = 1 ∨ r ^ 3 = 3 ∨ r ^ 3 = 5 ∨ r ^ 3 = 7 := by decide
    have hcast : ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) (b : ZMod 8) ≠ 0 := by
      rw [map_intCast]; exact hb2
    have hcu := key (b : ZMod 8) hcast
    push_cast at hsq hcu ⊢
    rw [hsq]
    rcases hcu with h | h | h | h <;> rw [h] <;> decide

/-! ## 6. A complementary prime-modulus obstruction at `p = 7` -/

/-- **Squares of `7 ∤ a` lie in `{1, 2, 4} (mod 7)`** (the nonzero QRs mod 7).
Transport `7 ∤ a` to `(a : ZMod 7) ≠ 0`, then a finite `decide`. -/
theorem coprime_sq_mod7 {a : ℤ} (ha : ¬ (7 : ℤ) ∣ a) :
    (a ^ 2 : ZMod 7) = 1 ∨ (a ^ 2 : ZMod 7) = 2 ∨ (a ^ 2 : ZMod 7) = 4 := by
  have h7 : (a : ZMod 7) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha
  have key : ∀ r : ZMod 7, r ≠ 0 → r ^ 2 = 1 ∨ r ^ 2 = 2 ∨ r ^ 2 = 4 := by decide
  have := key (a : ZMod 7) h7
  push_cast at this ⊢; exact this

/-- **For `7 ∤ a`, `a² + b³` avoids `6 (mod 7)`** (image gap).
With `a² ∈ {1,2,4}` and `b³ ∈ {0,1,6} (mod 7)`, the sum ranges over
`{0,1,2,3,4,5}`, **missing `{6}`**. Finite `decide` over the cube residues. -/
theorem twothree_coprime_a_notMem_mod7 {a b : ℤ} (ha : ¬ (7 : ℤ) ∣ a) :
    (a ^ 2 + b ^ 3 : ZMod 7) ≠ 6 := by
  have hsq := coprime_sq_mod7 ha
  have hcu : (b ^ 3 : ZMod 7) = 0 ∨ (b ^ 3 : ZMod 7) = 1 ∨ (b ^ 3 : ZMod 7) = 6 := by
    have h : ∀ r : ZMod 7, r ^ 3 = 0 ∨ r ^ 3 = 1 ∨ r ^ 3 = 6 := by decide
    have := h (b : ZMod 7); simpa using this
  push_cast at hsq hcu ⊢
  rcases hsq with hs | hs | hs <;> rcases hcu with h | h | h <;> rw [hs, h] <;> decide

/-- **Signature-`(2,3,n)` mod-7 obstruction (complementary).**
If `7 ∤ a` and `cⁿ ≡ 6 (mod 7)` then `a² + b³ ≠ cⁿ`. The class `cⁿ ≡ 6 (mod 7)`
is achievable (`c ≡ 6 (mod 7)`, `n` odd: `6¹ ≡ 6`), so this is a genuine local
obstruction at the prime `7`. -/
theorem twothree_mod7_obstruction {a b c : ℤ} {n : ℕ} (ha : ¬ (7 : ℤ) ∣ a)
    (hc : (c : ZMod 7) ^ n = 6) : a ^ 2 + b ^ 3 ≠ c ^ n := by
  intro heq
  have hcast : (a ^ 2 + b ^ 3 : ZMod 7) = (c ^ n : ZMod 7) := by
    have : ((a ^ 2 + b ^ 3 : ℤ) : ZMod 7) = ((c ^ n : ℤ) : ZMod 7) := by rw [heq]
    push_cast at this ⊢; exact this
  have hne := twothree_coprime_a_notMem_mod7 (a := a) (b := b) ha
  push_cast at hcast
  rw [hcast, hc] at hne
  exact hne rfl

end BealTwoThreeLocal
