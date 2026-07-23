import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Beal fifth-power local obstruction at the RAMIFIED prime-power modulus `q = 25`

The `BealFifthPower` / `BealLocalCRT` / `BealFifthMod41` / `BealFifthMod61` family
attacks **split** primes `q ≡ 1 (mod 5)` (`11, 31, 41, 61`), where `q` splits
completely in `ℚ(ζ₅)`. That split-prime family is now exhausted: every split
prime `q ≥ 71` up to `2000` was checked in Python and found fully surjective
(the fifth-power-sum image covers all of `ZMod q`), so no further split-prime
rung is available.

This file pivots to a **structurally different** modulus: `q = 25 = 5²`, the
square of the RAMIFIED prime `5` of `ℚ(ζ₅)` (`5 = u · λ⁴` there, totally
ramified, not split). Same finite-`decide`-over-a-grid technique, but a
genuinely new sub-family (prime powers of the ramified prime: `25, 125, 625,
…`), distinct in kind from the split-prime ladder.

Fifth powers mod 25 are `{0, 1, 7, 18, 24}` (`5` residues — note `ZMod 25` is
*not* a field, so this is not simply `(25−1)/5 + 1`; the unit group
`(ZMod 25)ˣ` is cyclic of order `φ(25) = 20`, and `5 ∣ 20`, giving `20/5 = 4`
nonzero fifth powers among units, plus `0` and the non-unit non-zero fifth
powers coincide with `0` here since `5 ∤ φ(25)`-adjacent subtleties are
irrelevant to the `decide` — we just compute directly).

The sumset `{A^5 + B^5 (mod 25)}` misses exactly `12` of the `25` residues:
`{3, 4, 5, 9, 10, 12, 13, 15, 16, 20, 21, 22}` — 48% of all residues, a large
obstruction.

Verified independently by exhaustive Python brute force before formalizing:

```python
q = 25
fp = sorted(set(pow(a, 5, q) for a in range(q)))
assert fp == [0, 1, 7, 18, 24]
sumset = set((x + y) % q for x in fp for y in fp)
forbidden = sorted(set(range(q)) - sumset)
assert forbidden == [3, 4, 5, 9, 10, 12, 13, 15, 16, 20, 21, 22]
```

## Non-vacuity of the Beal corollary hypothesis

`8` of the `12` forbidden residues are realizable as `c^z (mod 25)` with
`c = 2` and `z ≥ 3`:
`3 = 2^7`, `4 = 2^22`, `9 = 2^14`, `12 = 2^9`, `13 = 2^19`, `16 = 2^4`,
`21 = 2^12`, `22 = 2^17` (all mod 25).

The remaining `4` forbidden residues — `5, 10, 15, 20`, exactly the nonzero
multiples of `5` mod `25` — are in fact **never** achievable as `C^z (mod 25)`
for *any* integer `C` and exponent `z ≥ 2`: if `5 ∣ C` then `C^z ≡ 0 (mod 25)`
once `z ≥ 2`; if `5 ∤ C` then `C` is a unit mod `25` and `C^z` is coprime to
`5`, hence never a nonzero multiple of `5`. This is itself a nice reflection
of `5` being *ramified* (not split) — the residues `{5,10,15,20}` sit in the
"thickened" ramification locus `5·(ZMod 25)` that ordinary `z`-th powers can
never touch. It does not affect non-vacuity of the corollary below: the
disjunctive hypothesis as a whole is satisfied e.g. by `C = 2, z = 7`
(`C^z ≡ 3 (mod 25)`, forbidden), so `beal_fifth_mod25_obstruction` has
genuine, non-vacuous content.

## DISCIPLINE

No `sorry`, no `native_decide`, no new axioms. The sumset-gap fact is proved
by `decide` over the `25 × 25` grid (strictly smaller than the already-proved
`q = 61` case, `61 × 61`); `ZMod 25` is a finite commutative ring — `decide`
needs only `DecidableEq` + `Fintype`, not field structure, so the non-field,
non-cyclic-multiplicative-on-all-of-`ZMod 25` nature of `q = 25` causes no
issue. The Beal corollary mirrors `BealFifthMod61.beal_fifth_mod61_obstruction`.

Typecheck with `lake env lean BealFifthMod25.lean`.
-/

set_option maxRecDepth 8000

namespace BealFifthMod25

/-! ## 1. Fifth powers mod 25 are `{0, 1, 7, 18, 24}` -/

/-- **Fifth powers mod 25 are `{0, 1, 7, 18, 24}`.** For all `x : ZMod 25`,
`x^5 ∈ {0, 1, 7, 18, 24}`. By `decide`. -/
theorem fifth_powers_mod25 :
    ∀ x : ZMod 25, x ^ 5 = 0 ∨ x ^ 5 = 1 ∨ x ^ 5 = 7 ∨ x ^ 5 = 18 ∨ x ^ 5 = 24 := by
  decide

/-- **`5` distinct fifth powers mod 25.** By `decide`. -/
theorem fifth_residues_card_25 :
    (Finset.univ.image (fun x : ZMod 25 => x ^ 5)).card = 5 := by decide

/-! ## 2. The fifth-power-sum gap mod 25 (HEADLINE) -/

/-- **`q = 25` gap.** Over all `A, B : ZMod 25`, the sum `A^5 + B^5` avoids
every residue in `{3, 4, 5, 9, 10, 12, 13, 15, 16, 20, 21, 22}`. The
fifth-power set mod 25 is `{0, 1, 7, 18, 24}` (5 elements), so the sumset
misses `12` of the `25` residues. Finite `decide` over the `25 × 25` grid. -/
theorem fifth_sum_gap_mod25 :
    ∀ A B : ZMod 25,
      A ^ 5 + B ^ 5 ≠ 3 ∧ A ^ 5 + B ^ 5 ≠ 4 ∧ A ^ 5 + B ^ 5 ≠ 5 ∧
      A ^ 5 + B ^ 5 ≠ 9 ∧ A ^ 5 + B ^ 5 ≠ 10 ∧ A ^ 5 + B ^ 5 ≠ 12 ∧
      A ^ 5 + B ^ 5 ≠ 13 ∧ A ^ 5 + B ^ 5 ≠ 15 ∧ A ^ 5 + B ^ 5 ≠ 16 ∧
      A ^ 5 + B ^ 5 ≠ 20 ∧ A ^ 5 + B ^ 5 ≠ 21 ∧ A ^ 5 + B ^ 5 ≠ 22 := by decide

/-- **`12` residues mod 25 are forbidden**: the fifth-power-sum image misses
`12` of the `25` residues — `{3, 4, 5, 9, 10, 12, 13, 15, 16, 20, 21, 22}`, 48%
of `ZMod 25`. By `decide`. -/
theorem fifth_sum_forbidden_mod25_card :
    (Finset.univ.filter (fun r : ZMod 25 => ¬ ∃ A B : ZMod 25, A ^ 5 + B ^ 5 = r)).card = 12 := by
  decide

/-! ## 3. Beal corollary mod 25 -/

/-- **Beal fifth-power-sum obstruction at `q = 25` (HEADLINE corollary)**.
If the right-hand side `C^z` reduces mod 25 into the forbidden block
`{3, 4, 5, 9, 10, 12, 13, 15, 16, 20, 21, 22}`, then the fifth-power-sum
equation `A^5 + B^5 = C^z` is impossible modulo 25 — for *any* integers
`A, B, C` and exponent `z`. Thus the congruence classes
`C^z ≡ 3, 4, 5, 9, 10, 12, 13, 15, 16, 20, 21, 22 (mod 25)` are local
obstructions to the `(5,5,z)` Beal case.

This is the `q = 25` member of the RAMIFIED-prime-power fifth-power
obstruction family (`5` is totally ramified in `ℚ(ζ₅)`), distinct in kind from
the split-prime family (`q = 11, 31, 41, 61`): the sparsity of fifth powers
mod 25 (`{0,1,7,18,24}`) leaves the block
`{3,4,5,9,10,12,13,15,16,20,21,22}` (`12` of `25` residues) unreachable by
`A^5 + B^5`. Non-vacuous: e.g. `C = 2, z = 7` gives `C^z ≡ 3 (mod 25)`. -/
theorem beal_fifth_mod25_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 25) ^ z = 3 ∨ (C : ZMod 25) ^ z = 4 ∨ (C : ZMod 25) ^ z = 5 ∨
          (C : ZMod 25) ^ z = 9 ∨ (C : ZMod 25) ^ z = 10 ∨ (C : ZMod 25) ^ z = 12 ∨
          (C : ZMod 25) ^ z = 13 ∨ (C : ZMod 25) ^ z = 15 ∨ (C : ZMod 25) ^ z = 16 ∨
          (C : ZMod 25) ^ z = 20 ∨ (C : ZMod 25) ^ z = 21 ∨ (C : ZMod 25) ^ z = 22) :
    (A : ZMod 25) ^ 5 + (B : ZMod 25) ^ 5 ≠ (C : ZMod 25) ^ z := by
  have hgap := fifth_sum_gap_mod25 (A : ZMod 25) (B : ZMod 25)
  rcases hC with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact hgap.1
  · exact hgap.2.1
  · exact hgap.2.2.1
  · exact hgap.2.2.2.1
  · exact hgap.2.2.2.2.1
  · exact hgap.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.2.2.2.2.2

end BealFifthMod25
