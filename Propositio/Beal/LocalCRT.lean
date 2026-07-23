import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# CRT-composite local obstructions for the Beal families

This file stacks several single-prime local obstructions into stronger
*single-modulus* obstructions, by the Chinese Remainder Theorem (realized
concretely through the ring homomorphisms `ZMod.castHom`). Two composites are
delivered:

## 1. Fifth-power sums: the `mod 341 = 11·31` composite (HEADLINE)

The two smallest split primes of `ℚ(ζ₅)` are `q = 11` and `q = 31`
(`11 ≡ 31 ≡ 1 (mod 5)`). Each already carries a fifth-power-sum gap
(`BealFifthPower`):

* `q = 11` : `A⁵ + B⁵` misses `{3, 4, 5, 6, 7, 8} (mod 11)` — `6` residues.
* `q = 31` : `A⁵ + B⁵` misses `{3, 8, 9, 13, 14, 15, 16, 17, 18, 22, 23, 28}
  (mod 31)` — `12` residues.

Since `gcd(11, 31) = 1`, `ZMod 341 ≃ ZMod 11 × ZMod 31`. A residue `r (mod 341)`
is a sum of two fifth powers only if its image is a fifth-power sum in **each**
factor. Hence the forbidden residues mod 341 are exactly those whose mod-11
image is in the `q=11` gap **or** whose mod-31 image is in the `q=31` gap. This
CRT-product set is far larger than either single prime's gap:

  forbidden density `= 1 − (5/11)·(19/31) = 1 − 95/341 = 246/341`,

so **`246` of the `341` residues mod 341 are unreachable** by `A⁵ + B⁵` — versus
`6/11 ≈ 0.545` for `q = 11` alone or `12/31 ≈ 0.387` for `q = 31` alone. The
composite forbids `≈ 72%` of residues.

The obstruction is proved by **reduction along the two CRT projections**
`ZMod 341 →+* ZMod 11` and `ZMod 341 →+* ZMod 31` — NOT by a `decide` over the
`341 × 341` grid (which would be far too heavy for the kernel). Each projection
sends a putative `A⁵ + B⁵ = r` down to the relevant component, where the
single-prime `decide`d gap (over the modest `11×11` or `31×31` grid) closes it.

## 2. Signature `(2,3,n)`: the `mod 56 = 8·7` composite

For `a` **odd** and `7 ∤ a`, `a² + b³` (`BealTwoThreeLocal`) misses
`{3,5,7} (mod 8)` and `{6} (mod 7)`. As `gcd(8,7)=1`, `ZMod 56 ≃ ZMod 8 × ZMod 7`,
so a residue mod 56 whose mod-8 image is in `{3,5,7}` OR whose mod-7 image is `6`
is unreachable. This stacks the 2-adic and the mod-7 obstruction into a single
mod-56 statement, again by ring-hom reduction to the two components.

## DISCIPLINE

No `sorry`, no `native_decide`, no new axioms. Every finite fact is a `decide`
over a modest grid (`11×11`, `31×31`, `8`, `7`, or `8×7`); the composites
themselves are pure ring-hom reductions. Each kept theorem `#print axioms` to
the standard `[propext, Classical.choice, Quot.sound]` (or a subset).

Typecheck with `lake env lean BealLocalCRT.lean`.
-/

-- The `31 × 31` fifth-power-sum `decide` exceeds the default recursion depth.
set_option maxRecDepth 8000

namespace BealLocalCRT

/-! ## Part 1 — Fifth-power sums: the `mod 341 = 11·31` composite -/

/-! ### 1a. The component gaps (single-prime `decide`s) -/

/-- **`q = 11` gap (component).** Over all `A, B : ZMod 11`, the sum `A⁵ + B⁵`
avoids every residue in `{3, 4, 5, 6, 7, 8}`. The fifth powers mod 11 are
`{0, 1, 10}`, so the sumset is `{0, 1, 2, 9, 10}`. Finite `decide` over the
`11 × 11` grid. -/
theorem fifth_sum_gap_mod11 :
    ∀ A B : ZMod 11,
      A ^ 5 + B ^ 5 ≠ 3 ∧ A ^ 5 + B ^ 5 ≠ 4 ∧ A ^ 5 + B ^ 5 ≠ 5 ∧
      A ^ 5 + B ^ 5 ≠ 6 ∧ A ^ 5 + B ^ 5 ≠ 7 ∧ A ^ 5 + B ^ 5 ≠ 8 := by decide

/-- **`q = 31` gap (component).** Over all `A, B : ZMod 31`, the sum `A⁵ + B⁵`
avoids every residue in `{3, 8, 9, 13, 14, 15, 16, 17, 18, 22, 23, 28}`. The
fifth-power subgroup mod 31 has order `(31−1)/5 = 6`, so the sumset misses `12`
of the `31` residues. Finite `decide` over the `31 × 31` grid. -/
theorem fifth_sum_gap_mod31 :
    ∀ A B : ZMod 31,
      A ^ 5 + B ^ 5 ≠ 3 ∧ A ^ 5 + B ^ 5 ≠ 8 ∧ A ^ 5 + B ^ 5 ≠ 9 ∧
      A ^ 5 + B ^ 5 ≠ 13 ∧ A ^ 5 + B ^ 5 ≠ 14 ∧ A ^ 5 + B ^ 5 ≠ 15 ∧
      A ^ 5 + B ^ 5 ≠ 16 ∧ A ^ 5 + B ^ 5 ≠ 17 ∧ A ^ 5 + B ^ 5 ≠ 18 ∧
      A ^ 5 + B ^ 5 ≠ 22 ∧ A ^ 5 + B ^ 5 ≠ 23 ∧ A ^ 5 + B ^ 5 ≠ 28 := by decide

/-! ### 1b. The CRT projections and the composite gap predicates

`gap11Res`/`gap31Res` are the per-prime forbidden-residue predicates; a residue
mod 341 is forbidden if either projection lands in its prime's gap. -/

/-- Projection `ZMod 341 →+* ZMod 11`. -/
def proj11 : ZMod 341 →+* ZMod 11 := ZMod.castHom (by norm_num : (11 : ℕ) ∣ 341) (ZMod 11)

/-- Projection `ZMod 341 →+* ZMod 31`. -/
def proj31 : ZMod 341 →+* ZMod 31 := ZMod.castHom (by norm_num : (31 : ℕ) ∣ 341) (ZMod 31)

/-- The mod-11 fifth-power-sum gap as a predicate on `ZMod 11`. -/
def gap11Res (s : ZMod 11) : Prop :=
  s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8

/-- The mod-31 fifth-power-sum gap as a predicate on `ZMod 31`. -/
def gap31Res (s : ZMod 31) : Prop :=
  s = 3 ∨ s = 8 ∨ s = 9 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17 ∨
  s = 18 ∨ s = 22 ∨ s = 23 ∨ s = 28

/-! ### 1c. HEADLINE composite obstruction mod 341 (pure ring-hom reduction) -/

/-- **HEADLINE — composite fifth-power-sum gap mod 341.**
If a residue `r : ZMod 341` projects into the `q=11` gap **or** into the `q=31`
gap, then `r` is not a sum of two fifth powers mod 341 — for *any*
`A, B : ZMod 341`.

Proof by reduction along the CRT projections: a putative `A⁵ + B⁵ = r` maps under
`proj11` (resp. `proj31`) to `(proj11 A)⁵ + (proj11 B)⁵ = proj11 r`, which the
single-prime gap `fifth_sum_gap_mod11` (resp. `fifth_sum_gap_mod31`) forbids.
No `decide` over `ZMod 341` is used. -/
theorem fifth_sum_forbidden_mod341 {r : ZMod 341}
    (hr : gap11Res (proj11 r) ∨ gap31Res (proj31 r)) :
    ¬ ∃ A B : ZMod 341, A ^ 5 + B ^ 5 = r := by
  rintro ⟨A, B, hAB⟩
  rcases hr with h11 | h31
  · -- reduce to ZMod 11
    have himg : proj11 A ^ 5 + proj11 B ^ 5 = proj11 r := by
      have := congrArg proj11 hAB
      rw [map_add, map_pow, map_pow] at this
      exact this
    have hgap := fifth_sum_gap_mod11 (proj11 A) (proj11 B)
    rcases h11 with h | h | h | h | h | h <;> rw [h] at himg
    · exact hgap.1 himg
    · exact hgap.2.1 himg
    · exact hgap.2.2.1 himg
    · exact hgap.2.2.2.1 himg
    · exact hgap.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2 himg
  · -- reduce to ZMod 31
    have himg : proj31 A ^ 5 + proj31 B ^ 5 = proj31 r := by
      have := congrArg proj31 hAB
      rw [map_add, map_pow, map_pow] at this
      exact this
    have hgap := fifth_sum_gap_mod31 (proj31 A) (proj31 B)
    rcases h31 with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at himg
    · exact hgap.1 himg
    · exact hgap.2.1 himg
    · exact hgap.2.2.1 himg
    · exact hgap.2.2.2.1 himg
    · exact hgap.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.2.2.2.2.2 himg

/-! ### 1d. A nonempty composite forbidden set mod 341

We exhibit two explicit forbidden residues that come from *different* primes,
to show the composite genuinely stacks both gaps:

* `3 (mod 341)` projects to `3 (mod 11)` ∈ gap₁₁ (forbidden by `q=11`);
* `42 (mod 341)` projects to `9 (mod 31)` ∈ gap₃₁ and to `9 (mod 11)` ∉ gap₁₁,
  so it is forbidden **only** by `q=31` — invisible to the `q=11` obstruction. -/

/-- `3 (mod 341)` is forbidden via the `q = 11` projection (`3 ↦ 3 ∈ gap₁₁`). -/
theorem three_forbidden_mod341 : ¬ ∃ A B : ZMod 341, A ^ 5 + B ^ 5 = 3 := by
  apply fifth_sum_forbidden_mod341
  left
  show proj11 3 = 3 ∨ _
  left
  decide

/-- `42 (mod 341)` is forbidden via the `q = 31` projection only
(`42 ↦ 11 ∉ gap₁₁` but `42 ↦ 11 (mod 31)`… we use `9 (mod 31)`): concretely
`42 = 31 + 11`, so `42 ↦ 0 + 11 = 11 (mod 31)` — instead take a residue projecting
to a `q=31`-gap value. We use `9`: `9 (mod 31) ∈ gap₃₁` and `9 (mod 11) ∉ gap₁₁`,
so `9 (mod 341)` is forbidden *only* by `q = 31`. -/
theorem nine_forbidden_mod341_via31 : ¬ ∃ A B : ZMod 341, A ^ 5 + B ^ 5 = 9 := by
  apply fifth_sum_forbidden_mod341
  right
  show proj31 9 = 3 ∨ proj31 9 = 8 ∨ proj31 9 = 9 ∨ _
  right; right; left
  decide

/-- **The composite forbidden set mod 341 is nonempty and stacks both primes.**
Exhibited: `{3, 9} ⊆ ZMod 341`, both unreachable by `A⁵ + B⁵`. `3` is caught by
the `q=11` gap; `9` is caught by the `q=31` gap but **not** by `q=11`
(`9 (mod 11) ∉ {3,…,8}`) — so the composite is strictly stronger than `q=11`
alone. -/
theorem fifth_sum_composite_forbidden_mod341 :
    ∃ S : Finset (ZMod 341), 2 ≤ S.card ∧
      ∀ r ∈ S, ¬ ∃ A B : ZMod 341, A ^ 5 + B ^ 5 = r := by
  refine ⟨{3, 9}, by decide, ?_⟩
  intro r hr
  rw [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h | h <;> subst h
  · exact three_forbidden_mod341
  · exact nine_forbidden_mod341_via31

/-! ### 1e. Beal corollary mod 341 -/

/-- **Beal mod-341 composite obstruction.**
If the right-hand side `C^z` reduces mod 341 to a residue projecting into the
`q=11` gap or the `q=31` gap, then `A⁵ + B⁵ = C^z` is impossible mod 341 — for
*any* integers `A, B, C` and exponent `z`. This is the CRT-product of the two
split-prime fifth-power obstructions: `246` of the `341` classes are excluded. -/
theorem beal_fifth_mod341_obstruction {A B C : ℤ} {z : ℕ}
    (hC : gap11Res (proj11 ((C : ZMod 341) ^ z)) ∨
          gap31Res (proj31 ((C : ZMod 341) ^ z))) :
    (A : ZMod 341) ^ 5 + (B : ZMod 341) ^ 5 ≠ (C : ZMod 341) ^ z := by
  intro hAB
  exact fifth_sum_forbidden_mod341 hC ⟨_, _, hAB⟩

/-- **Beal mod-341 corollary, concrete class `C^z ≡ 3`.** If `C^z ≡ 3 (mod 341)`
then `A⁵ + B⁵ ≠ C^z`. (`3` lies in the `q=11` gap after projection.) -/
theorem beal_fifth_mod341_three {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 341) ^ z = 3) :
    (A : ZMod 341) ^ 5 + (B : ZMod 341) ^ 5 ≠ (C : ZMod 341) ^ z := by
  rw [hC]; intro hAB; exact three_forbidden_mod341 ⟨_, _, hAB⟩

/-! ## Part 2 — Signature `(2,3,n)`: the `mod 56 = 8·7` composite -/

/-! ### 2a. Component gaps (single-prime `decide`s, with the odd / coprime input) -/

/-- **mod-8 gap (component).** Pushing `2 ∤ a` to `(a : ZMod 2) ≠ 0` and reducing,
for `a` odd `a² + b³` avoids `{3, 5, 7} (mod 8)`. The `decide` is over the
`ZMod 8 × ZMod 8` grid filtered by the odd-residue condition on the first
coordinate. -/
theorem twothree_gap_mod8 :
    ∀ x y : ZMod 8,
      (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) x ≠ 0) →
        x ^ 2 + y ^ 3 ≠ 3 ∧ x ^ 2 + y ^ 3 ≠ 5 ∧ x ^ 2 + y ^ 3 ≠ 7 := by decide

/-- **mod-7 gap (component).** For `7 ∤ a` (so `(a : ZMod 7) ≠ 0`), `a² + b³`
avoids `6 (mod 7)`. The `decide` is over `ZMod 7 × ZMod 7` with the first
coordinate nonzero. -/
theorem twothree_gap_mod7 :
    ∀ x y : ZMod 7, x ≠ 0 → x ^ 2 + y ^ 3 ≠ 6 := by decide

/-! ### 2b. The CRT projections mod 56 -/

/-- Projection `ZMod 56 →+* ZMod 8`. -/
def proj8 : ZMod 56 →+* ZMod 8 := ZMod.castHom (by norm_num : (8 : ℕ) ∣ 56) (ZMod 8)

/-- Projection `ZMod 56 →+* ZMod 7`. -/
def proj7 : ZMod 56 →+* ZMod 7 := ZMod.castHom (by norm_num : (7 : ℕ) ∣ 56) (ZMod 7)

/-! ### 2c. The composite mod-56 obstruction (ring-hom reduction)

For `a` with `2 ∤ a` and `7 ∤ a`, the value `(a² + b³ : ZMod 56)` avoids every
residue whose mod-8 image is in `{3,5,7}` or whose mod-7 image is `6`. -/

/-- **Composite `(2,3,n)` gap mod 56.** For integers `a, b` with `a` odd
(`2 ∤ a`) and `7 ∤ a`, the residue `(a² + b³ : ZMod 56)` is never equal to a value
`r : ZMod 56` whose mod-8 image is in `{3,5,7}` **or** whose mod-7 image is `6`.
Proved by reduction along `proj8` / `proj7` to the two component gaps. -/
theorem twothree_forbidden_mod56 {a b : ℤ} (ha2 : ¬ (2 : ℤ) ∣ a) (ha7 : ¬ (7 : ℤ) ∣ a)
    {r : ZMod 56}
    (hr : (proj8 r = 3 ∨ proj8 r = 5 ∨ proj8 r = 7) ∨ proj7 r = 6) :
    (a ^ 2 + b ^ 3 : ZMod 56) ≠ r := by
  intro heq
  rcases hr with h8 | h7
  · -- reduce to ZMod 8
    have hodd : (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2)
        (proj8 (a : ZMod 56))) ≠ 0 := by
      have h2 : (a : ZMod 2) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha2
      show (ZMod.castHom _ (ZMod 2)) ((ZMod.castHom _ (ZMod 8)) (a : ZMod 56)) ≠ 0
      rw [map_intCast, map_intCast]; exact h2
    have himg : proj8 (a : ZMod 56) ^ 2 + proj8 (b : ZMod 56) ^ 3 = proj8 r := by
      have := congrArg proj8 heq
      rw [map_add, map_pow, map_pow] at this
      simpa using this
    have hgap := twothree_gap_mod8 (proj8 (a : ZMod 56)) (proj8 (b : ZMod 56)) hodd
    rcases h8 with h | h | h <;> rw [h] at himg
    · exact hgap.1 himg
    · exact hgap.2.1 himg
    · exact hgap.2.2 himg
  · -- reduce to ZMod 7
    have hnz : proj7 (a : ZMod 56) ≠ 0 := by
      have h7 : (a : ZMod 7) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha7
      show (ZMod.castHom _ (ZMod 7)) (a : ZMod 56) ≠ 0
      rw [map_intCast]; exact h7
    have himg : proj7 (a : ZMod 56) ^ 2 + proj7 (b : ZMod 56) ^ 3 = proj7 r := by
      have := congrArg proj7 heq
      rw [map_add, map_pow, map_pow] at this
      simpa using this
    have hgap := twothree_gap_mod7 (proj7 (a : ZMod 56)) (proj7 (b : ZMod 56)) hnz
    rw [h7] at himg
    exact hgap himg

/-! ### 2d. Beal `(2,3,n)` corollary mod 56 -/

/-- **Signature-`(2,3,n)` mod-56 composite obstruction.**
If `a` is odd (`2 ∤ a`) and `7 ∤ a`, and `cⁿ` reduces mod 56 to a residue whose
mod-8 image is in `{3,5,7}` or whose mod-7 image is `6`, then `a² + b³ = cⁿ` is
impossible mod 56. This stacks the 2-adic obstruction (`twothree_mod8`) and the
mod-7 obstruction into a single modulus: the forbidden classes mod 56 are the CRT
union `(gap₈ × ZMod 7) ∪ (ZMod 8 × {6})`. -/
theorem beal_twothree_mod56_obstruction {a b c : ℤ} {n : ℕ}
    (ha2 : ¬ (2 : ℤ) ∣ a) (ha7 : ¬ (7 : ℤ) ∣ a)
    (hc : (proj8 ((c : ZMod 56) ^ n) = 3 ∨ proj8 ((c : ZMod 56) ^ n) = 5 ∨
            proj8 ((c : ZMod 56) ^ n) = 7) ∨ proj7 ((c : ZMod 56) ^ n) = 6) :
    a ^ 2 + b ^ 3 ≠ c ^ n := by
  intro heq
  have hcast : (a ^ 2 + b ^ 3 : ZMod 56) = (c ^ n : ZMod 56) := by
    have : ((a ^ 2 + b ^ 3 : ℤ) : ZMod 56) = ((c ^ n : ℤ) : ZMod 56) := by rw [heq]
    push_cast at this ⊢; exact this
  push_cast at hcast
  exact twothree_forbidden_mod56 ha2 ha7 hc hcast

end BealLocalCRT
