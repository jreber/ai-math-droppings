import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Beal fifth-power local obstruction at the split prime `q = 41`

The next productive split prime (`q ≡ 1 (mod 5)`) in the `BealFifthPower` /
`BealLocalCRT` family, after `q = 11` and `q = 31`.

Fifth powers mod 41 form the index-5 subgroup `{0, 1, 3, 9, 14, 27, 32, 38, 40}`
of order `(41 − 1)/5 = 8` (nonzero part), since `5 ∣ 40 = |(ZMod 41)ˣ|`. The
sumset `{A^5 + B^5 (mod 41)}` misses exactly `8` of the `41` residues:
`{7, 16, 19, 20, 21, 22, 25, 34}`.

Verified independently by exhaustive Python brute force before formalizing:

```python
q = 41
fp = [pow(a, 5, q) for a in range(q)]
forb = set(range(q)) - set((x + y) % q for x in fp for y in fp)
assert sorted(forb) == [7, 16, 19, 20, 21, 22, 25, 34]
```

Every forbidden residue is realizable as some `c^z (mod 41)` with `z ≥ 3`
(e.g. `16 = 2^4`, `19 = 6^9`, `34 = 15^7`, `25 = 2^14`, `7 = 11^13`,
`20 = 2^9`, `21 = 6^14`, `22 = 7^11`), so the hypothesis of the Beal
corollary below is non-vacuous.

`q = 61` (12 forbidden residues) is an equally-valid next member of the
family but is left for a future file; `q ≥ 71` is a dead end for this
technique (the fifth-power sumset becomes fully surjective).

## DISCIPLINE

No `sorry`, no `native_decide`, no new axioms. The sumset-gap fact is proved
by `decide` over the `41 × 41` grid (mirroring `BealLocalCRT.fifth_sum_gap_mod31`,
which needed `maxRecDepth 8000` for the smaller `31 × 31` grid); the Beal
corollary mirrors `BealFifthPower.beal_fifth_mod11_obstruction`.

Typecheck with `lake env lean BealFifthMod41.lean`.
-/

-- The `41 × 41` fifth-power-sum `decide` exceeds the default recursion depth.
set_option maxRecDepth 8000

namespace BealFifthMod41

/-! ## 1. The fifth-power-sum gap mod 41 -/

/-- **`q = 41` gap.** Over all `A, B : ZMod 41`, the sum `A^5 + B^5` avoids
every residue in `{7, 16, 19, 20, 21, 22, 25, 34}`. The fifth-power subgroup
mod 41 is `{0, 1, 3, 9, 14, 27, 32, 38, 40}` (order `(41−1)/5 + 1 = 9`
including `0`), so the sumset misses `8` of the `41` residues. Finite
`decide` over the `41 × 41` grid. -/
theorem fifth_sum_gap_mod41 :
    ∀ A B : ZMod 41,
      A ^ 5 + B ^ 5 ≠ 7 ∧ A ^ 5 + B ^ 5 ≠ 16 ∧ A ^ 5 + B ^ 5 ≠ 19 ∧
      A ^ 5 + B ^ 5 ≠ 20 ∧ A ^ 5 + B ^ 5 ≠ 21 ∧ A ^ 5 + B ^ 5 ≠ 22 ∧
      A ^ 5 + B ^ 5 ≠ 25 ∧ A ^ 5 + B ^ 5 ≠ 34 := by decide

/-- **`8` residues mod 41 are forbidden**: the fifth-power-sum image misses
`8` of the `41` residues — `{7, 16, 19, 20, 21, 22, 25, 34}`. By `decide`. -/
theorem fifth_sum_forbidden_mod41_card :
    (Finset.univ.filter (fun r : ZMod 41 => ¬ ∃ A B : ZMod 41, A ^ 5 + B ^ 5 = r)).card = 8 := by
  decide

/-! ## 2. Beal corollary mod 41 -/

/-- **Beal fifth-power-sum obstruction at `q = 41` (HEADLINE corollary)**.
If the right-hand side `C^z` reduces mod 41 into the forbidden block
`{7, 16, 19, 20, 21, 22, 25, 34}`, then the fifth-power-sum equation
`A^5 + B^5 = C^z` is impossible modulo 41 — for *any* integers `A, B, C` and
exponent `z`. Thus the congruence classes `C^z ≡ 7, 16, 19, 20, 21, 22, 25, 34
(mod 41)` are local obstructions to the `(5,5,z)` Beal case.

This is the `q = 41` member of the split-prime fifth-power obstruction
family (after `q = 11`, `q = 31`): the sparsity of fifth powers mod 41
(`{0,1,3,9,14,27,32,38,40}`) leaves the block `{7,16,19,20,21,22,25,34}`
(`8` of `41` residues) unreachable by `A^5 + B^5`. -/
theorem beal_fifth_mod41_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 41) ^ z = 7 ∨ (C : ZMod 41) ^ z = 16 ∨ (C : ZMod 41) ^ z = 19 ∨
          (C : ZMod 41) ^ z = 20 ∨ (C : ZMod 41) ^ z = 21 ∨ (C : ZMod 41) ^ z = 22 ∨
          (C : ZMod 41) ^ z = 25 ∨ (C : ZMod 41) ^ z = 34) :
    (A : ZMod 41) ^ 5 + (B : ZMod 41) ^ 5 ≠ (C : ZMod 41) ^ z := by
  have hgap := fifth_sum_gap_mod41 (A : ZMod 41) (B : ZMod 41)
  rcases hC with h | h | h | h | h | h | h | h <;> rw [h]
  · exact hgap.1
  · exact hgap.2.1
  · exact hgap.2.2.1
  · exact hgap.2.2.2.1
  · exact hgap.2.2.2.2.1
  · exact hgap.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.1
  · exact hgap.2.2.2.2.2.2.2

end BealFifthMod41
