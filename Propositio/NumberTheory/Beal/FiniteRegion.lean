import Mathlib.Tactic

/-!
# A machine-checked finite-region certificate: no primitive Beal counterexample for small bases

This is the Beal analogue of the Collatz "no cycle of length `≤ L`" results
(`CollatzNineCycle` etc.): a **decidable exhaustive search** over an explicit finite box,
discharged by a single kernel `decide` (no `native_decide`). It is a flavor the Beal
corpus did not previously have — the local-obstruction and descent files constrain
*hypothetical* counterexamples; this one *verifies their absence* in a concrete range.

## The certificate

`noBealInBox N exps` is the `Bool` that is `true` iff there is **no** primitive solution
`A^x + B^y = C^z` with `A, B, C ∈ [1, N]`, exponents `x, y, z ∈ exps`, and
`gcd(gcd(A,B),C) = 1`. `no_beal_in_box` turns `noBealInBox N exps = true` into the
universally-quantified non-existence statement.

The headline instance `no_primitive_beal_bases_le_12` discharges `N = 12`,
`exps = {3,4,5}` by kernel `decide` (≈31 s / ≈4.6 GB; build through `scripts/safe-lean.sh`):

> No coprime triple `A, B, C ≤ 12` and exponents `x, y, z ∈ {3,4,5}` satisfies
> `A^x + B^y = C^z`. Equivalently: any such primitive counterexample has a base `> 12`
> or an exponent outside `{3,4,5}`.

## Honesty about the bound

This is a *method demonstration*, not a record: the known computational verification of
Beal reaches bases in the thousands (with non-kernel arithmetic). The value here is a
fully kernel-checked, axiom-clean certificate (`[propext, Classical.choice, Quot.sound]`,
no `native_decide`/`ofReduceBool`) and a reusable `noBealInBox`/`no_beal_in_box` pair: a
larger region is just a bigger `decide` (memory grows like `N³·|exps|³`), or — to push
further — the same per-parameter partition that broke the Collatz L=9 wall.

Typecheck/​build with `scripts/safe-lean.sh --build BealFiniteRegion`.
-/

namespace BealFiniteRegion

/-- `true` iff no primitive `A^x + B^y = C^z` exists with `A,B,C ∈ [1,N]`, `x,y,z ∈ exps`.
For each tuple, if the configuration is a valid *primitive* candidate (positive bases,
`gcd(gcd(A,B),C) = 1`) we require the equation to *fail*; otherwise the slot is vacuously
`true`. -/
def noBealInBox (N : Nat) (exps : List Nat) : Bool :=
  (List.range (N + 1)).all (fun A =>
   (List.range (N + 1)).all (fun B =>
   (List.range (N + 1)).all (fun C =>
   exps.all (fun x => exps.all (fun y => exps.all (fun z =>
     if 1 ≤ A ∧ 1 ≤ B ∧ 1 ≤ C ∧ Nat.gcd (Nat.gcd A B) C = 1 then
       decide (A ^ x + B ^ y ≠ C ^ z)
     else
       true))))))

/-- **Finite-region non-existence (general).** If `noBealInBox N exps = true`, then no
primitive Beal triple lies in the box: for all `A, B, C ≤ N` with `1 ≤ A, B, C`,
`gcd(gcd(A,B),C) = 1` and exponents `x, y, z ∈ exps`, the equation `A^x + B^y = C^z`
fails. Pure unfolding of the nested `List.all` at the given point. -/
theorem no_beal_in_box {N : Nat} {exps : List Nat} (h : noBealInBox N exps = true)
    {A B C x y z : Nat} (hA : A ≤ N) (hB : B ≤ N) (hC : C ≤ N)
    (hx : x ∈ exps) (hy : y ∈ exps) (hz : z ∈ exps)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hC1 : 1 ≤ C)
    (hcop : Nat.gcd (Nat.gcd A B) C = 1) :
    A ^ x + B ^ y ≠ C ^ z := by
  have hAm : A ∈ List.range (N + 1) := List.mem_range.mpr (by omega)
  have hBm : B ∈ List.range (N + 1) := List.mem_range.mpr (by omega)
  have hCm : C ∈ List.range (N + 1) := List.mem_range.mpr (by omega)
  have h1 := List.all_eq_true.mp h A hAm
  have h2 := List.all_eq_true.mp h1 B hBm
  have h3 := List.all_eq_true.mp h2 C hCm
  have h4 := List.all_eq_true.mp h3 x hx
  have h5 := List.all_eq_true.mp h4 y hy
  have h6 := List.all_eq_true.mp h5 z hz
  rw [if_pos ⟨hA1, hB1, hC1, hcop⟩] at h6
  exact of_decide_eq_true h6

/-- The `N = 12`, `exps = {3,4,5}` certificate value (kernel `decide`). -/
theorem noBealInBox_twelve : noBealInBox 12 [3, 4, 5] = true := by decide

/-- **No primitive Beal counterexample with bases `≤ 12` and exponents in `{3,4,5}`.**
Machine-checked exhaustive search (`noBealInBox_twelve`). Any primitive counterexample
must therefore have a base `> 12` or an exponent outside `{3,4,5}`. -/
theorem no_primitive_beal_bases_le_12
    {A B C x y z : Nat} (hA : A ≤ 12) (hB : B ≤ 12) (hC : C ≤ 12)
    (hx : x = 3 ∨ x = 4 ∨ x = 5) (hy : y = 3 ∨ y = 4 ∨ y = 5) (hz : z = 3 ∨ z = 4 ∨ z = 5)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hC1 : 1 ≤ C)
    (hcop : Nat.gcd (Nat.gcd A B) C = 1) :
    A ^ x + B ^ y ≠ C ^ z := by
  refine no_beal_in_box noBealInBox_twelve hA hB hC ?_ ?_ ?_ hA1 hB1 hC1 hcop
  · rcases hx with rfl | rfl | rfl <;> simp
  · rcases hy with rfl | rfl | rfl <;> simp
  · rcases hz with rfl | rfl | rfl <;> simp

#print axioms no_beal_in_box
#print axioms no_primitive_beal_bases_le_12

end BealFiniteRegion
