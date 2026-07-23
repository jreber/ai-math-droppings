import Propositio.Collatz.CycleDecide

/-!
# A memory-light kernel enumerator for the Steiner divisibility check

`CollatzCycleUniform.cycleExcludedB L` checks, for each admissible total `A`, that no
length-`L` composition `as` of `A` has `(2^A − 3^L) ∣ steinerVal as`. Evaluating that
by a `decide` over the *materialized* list `compositions L A` is what OOMs at `L = 9`
(≈12870-element lists held in the kernel) and stack-overflows past it.

This file gives an equivalent **recursive** checker `noStDvd` that carries the
`steinerVal` foldl accumulator `(s, t)` down the composition tree instead of building
the list. The kernel reduces it depth-first, so the live term is `O(L)` deep rather than
`O(C(A−1, L−1))` wide. Empirically this cuts the `L = 9`, `A = 17` `decide` from
~6.2 GB / 2 min to ~3.6 GB / 1 min, and the same primitive scales the method past `L = 9`.

`noStDvd_top` is the bridge: `noStDvd m L A 0 0 = (compositions L A).all (… steinerVal …)`,
so a `decide` on `noStDvd …` discharges exactly the `cycleExcludedB` body. Both bridge
lemmas are axiom-clean (`noStDvd_eq` / `noStDvd_top` use only `[propext]`).
-/

namespace CollatzCycleEnum

open CollatzCycleDecide (steinerVal compositions)

/-- Recursive "no length-`parts` composition of `total` has `steinerVal` divisible by
`m`" checker. The pair `(s, t)` is the running `steinerVal` foldl accumulator
(`steiner-so-far`, `partial-sum-so-far`); the top-level call uses `(0, 0)`. The list
`compositions parts total` is never materialized — each recursion level only enumerates
the `≤ total` choices of the next part. -/
def noStDvd (m : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0,        total, s, _ => if total = 0 then !decide (m ∣ s) else true
  | parts + 1, total, s, t =>
      (List.range total).all (fun i =>
        noStDvd m parts (total - (i + 1)) (3 * s + 2 ^ t) (t + (i + 1)))

/-- **Bridge (general accumulator).** `noStDvd m parts total s t` equals the
`compositions`-based check whose `steinerVal` foldl starts from `(s, t)`. By induction on
`parts`, mirroring the `compositions` recursion (`List.all_flatMap` / `List.all_map`); the
cons step is definitional `List.foldl` unfolding. -/
theorem noStDvd_eq (m parts : Nat) : ∀ total s t,
    noStDvd m parts total s t
      = (compositions parts total).all
          (fun as => !decide (m ∣ (as.foldl (fun p a => (3 * p.1 + 2 ^ p.2, p.2 + a)) (s, t)).1)) := by
  induction parts with
  | zero =>
    intro total s t
    cases total with
    | zero => simp [noStDvd, compositions]
    | succ n => simp [noStDvd, compositions]
  | succ parts ih =>
    intro total s t
    rw [noStDvd, compositions, List.all_flatMap]
    apply List.all_congr rfl
    intro i
    rw [ih, List.all_map]
    apply List.all_congr rfl
    intro as
    rfl

/-- **Bridge (top level).** With the accumulator started at `(0, 0)`, the foldl is exactly
`steinerVal`, so `noStDvd m parts total 0 0` equals the `cycleExcludedB`-style body. -/
theorem noStDvd_top (m parts total : Nat) :
    noStDvd m parts total 0 0
      = (compositions parts total).all (fun as => !decide (m ∣ steinerVal as)) := by
  rw [noStDvd_eq]; rfl

#print axioms noStDvd_eq
#print axioms noStDvd_top

end CollatzCycleEnum
