import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Beal fifth-power local obstruction at the split prime `q = 61`

The next productive split prime (`q ≡ 1 (mod 5)`) in the `BealFifthPower` /
`BealLocalCRT` / `BealFifthMod41` family, after `q = 11`, `q = 31`, and
`q = 41`.

Fifth powers mod 61 form the index-5 subgroup
`{0, 1, 11, 13, 14, 21, 29, 32, 40, 47, 48, 50, 60}` of order
`(61 − 1)/5 = 12` (nonzero part), since `5 ∣ 60 = |(ZMod 61)ˣ|`. The sumset
`{A^5 + B^5 (mod 61)}` misses exactly `12` of the `61` residues:
`{4, 5, 6, 9, 17, 23, 38, 44, 52, 55, 56, 57}`.

Verified independently by exhaustive Python brute force before formalizing:

```python
q = 61
fp = [pow(a, 5, q) for a in range(q)]
forb = set(range(q)) - set((x + y) % q for x in fp for y in fp)
assert sorted(forb) == [4, 5, 6, 9, 17, 23, 38, 44, 52, 55, 56, 57]
```

Every forbidden residue is realizable as some `c^z (mod 61)` with `z ≥ 3`
(non-vacuity of the hypothesis of the Beal corollary below), e.g.:
`4 = 5^11`, `5 = 4^11`, `6 = 2^7`, `9 = 2^12`, `17 = 26^7`, `23 = 8^19`,
`38 = 7^3`, `44 = 2^17`, `52 = 3^7`, `55 = 7^13`, `56 = 5^16`, `57 = 4^16`.

`q = 71` and further split primes are left for a future file if productive;
sufficiently large split primes make the fifth-power sumset fully
surjective, at which point this particular technique is exhausted.

## DISCIPLINE

No `sorry`, no `native_decide`, no new axioms. The sumset-gap fact is proved
by `decide` over the `61 × 61` grid (mirroring `BealFifthMod41.fifth_sum_gap_mod41`,
which needed `maxRecDepth 8000` for the smaller `41 × 41` grid); the Beal
corollary mirrors `BealFifthMod41.beal_fifth_mod41_obstruction`.

Typecheck with `lake env lean BealFifthMod61.lean`.
-/

-- The `61 × 61` fifth-power-sum `decide` exceeds the default recursion depth.
set_option maxRecDepth 8000

namespace BealFifthMod61

/-! ## 1. The fifth-power-sum gap mod 61 -/

/-- **`q = 61` gap.** Over all `A, B : ZMod 61`, the sum `A^5 + B^5` avoids
every residue in `{4, 5, 6, 9, 17, 23, 38, 44, 52, 55, 56, 57}`. The
fifth-power subgroup mod 61 is
`{0, 1, 11, 13, 14, 21, 29, 32, 40, 47, 48, 50, 60}` (order
`(61−1)/5 + 1 = 13` including `0`), so the sumset misses `12` of the `61`
residues. Finite `decide` over the `61 × 61` grid. -/
theorem fifth_sum_gap_mod61 :
    ∀ A B : ZMod 61,
      A ^ 5 + B ^ 5 ≠ 4 ∧ A ^ 5 + B ^ 5 ≠ 5 ∧ A ^ 5 + B ^ 5 ≠ 6 ∧
      A ^ 5 + B ^ 5 ≠ 9 ∧ A ^ 5 + B ^ 5 ≠ 17 ∧ A ^ 5 + B ^ 5 ≠ 23 ∧
      A ^ 5 + B ^ 5 ≠ 38 ∧ A ^ 5 + B ^ 5 ≠ 44 ∧ A ^ 5 + B ^ 5 ≠ 52 ∧
      A ^ 5 + B ^ 5 ≠ 55 ∧ A ^ 5 + B ^ 5 ≠ 56 ∧ A ^ 5 + B ^ 5 ≠ 57 := by decide

/-- **`12` residues mod 61 are forbidden**: the fifth-power-sum image misses
`12` of the `61` residues —
`{4, 5, 6, 9, 17, 23, 38, 44, 52, 55, 56, 57}`. By `decide`. -/
theorem fifth_sum_forbidden_mod61_card :
    (Finset.univ.filter (fun r : ZMod 61 => ¬ ∃ A B : ZMod 61, A ^ 5 + B ^ 5 = r)).card = 12 := by
  decide

/-! ## 2. Beal corollary mod 61 -/

/-- **Beal fifth-power-sum obstruction at `q = 61` (HEADLINE corollary)**.
If the right-hand side `C^z` reduces mod 61 into the forbidden block
`{4, 5, 6, 9, 17, 23, 38, 44, 52, 55, 56, 57}`, then the fifth-power-sum
equation `A^5 + B^5 = C^z` is impossible modulo 61 — for *any* integers
`A, B, C` and exponent `z`. Thus the congruence classes
`C^z ≡ 4, 5, 6, 9, 17, 23, 38, 44, 52, 55, 56, 57 (mod 61)` are local
obstructions to the `(5,5,z)` Beal case.

This is the `q = 61` member of the split-prime fifth-power obstruction
family (after `q = 11`, `q = 31`, `q = 41`): the sparsity of fifth powers
mod 61 (`{0,1,11,13,14,21,29,32,40,47,48,50,60}`) leaves the block
`{4,5,6,9,17,23,38,44,52,55,56,57}` (`12` of `61` residues) unreachable by
`A^5 + B^5`. -/
theorem beal_fifth_mod61_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 61) ^ z = 4 ∨ (C : ZMod 61) ^ z = 5 ∨ (C : ZMod 61) ^ z = 6 ∨
          (C : ZMod 61) ^ z = 9 ∨ (C : ZMod 61) ^ z = 17 ∨ (C : ZMod 61) ^ z = 23 ∨
          (C : ZMod 61) ^ z = 38 ∨ (C : ZMod 61) ^ z = 44 ∨ (C : ZMod 61) ^ z = 52 ∨
          (C : ZMod 61) ^ z = 55 ∨ (C : ZMod 61) ^ z = 56 ∨ (C : ZMod 61) ^ z = 57) :
    (A : ZMod 61) ^ 5 + (B : ZMod 61) ^ 5 ≠ (C : ZMod 61) ^ z := by
  have hgap := fifth_sum_gap_mod61 (A : ZMod 61) (B : ZMod 61)
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

end BealFifthMod61
