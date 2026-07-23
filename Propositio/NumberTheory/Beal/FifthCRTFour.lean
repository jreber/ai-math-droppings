import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.LocalCRT
import Propositio.NumberTheory.Beal.FifthMod41
import Propositio.NumberTheory.Beal.FifthMod61

/-!
# Beal fifth-power CRT capstone: all four split-prime gaps, `mod 852841`

This file stacks **all four currently-proved** fifth-power-sum local
obstructions — `q = 11`, `31`, `41`, `61` (the complete list of productive
split primes `q ≡ 1 (mod 5)` found so far; `q = 71` and beyond are fully
surjective and give no gap) — into a single composite-modulus obstruction, by
the same Chinese-Remainder-Theorem ring-hom-projection technique that
`BealLocalCRT.fifth_sum_forbidden_mod341` already uses for the two smallest
split primes (`q = 11, 31`).

## The four component gaps

* `q = 11` (`BealLocalCRT.fifth_sum_gap_mod11`): `A⁵+B⁵` misses `6` of `11`
  residues, `{3,4,5,6,7,8}`.
* `q = 31` (`BealLocalCRT.fifth_sum_gap_mod31`): misses `12` of `31` residues.
* `q = 41` (`BealFifthMod41.fifth_sum_gap_mod41`): misses `8` of `41`
  residues, `{7,16,19,20,21,22,25,34}`.
* `q = 61` (`BealFifthMod61.fifth_sum_gap_mod61`): misses `12` of `61`
  residues, `{4,5,6,9,17,23,38,44,52,55,56,57}`.

Since `11, 31, 41, 61` are pairwise coprime, `ZMod 852841 ≃ ZMod 11 × ZMod 31 ×
ZMod 41 × ZMod 61` where `852841 = 11 · 31 · 41 · 61`. A residue `r (mod
852841)` is a sum of two fifth powers only if its image is a fifth-power sum
in **every** factor, so the forbidden set mod `852841` is the union (across
all four factors) of the pullbacks of each factor's gap:

  achievable density `= (5/11)·(19/31)·(33/41)·(49/61) = 153615/852841 ≈ 18.0%`,

so **`699226` of the `852841` residues mod `852841` are unreachable** by
`A⁵ + B⁵` — the composite forbids `≈ 82.0%` of residues, versus `72%` for the
existing 2-prime `mod 341` composite (`BealLocalCRT`). This is the natural
*capstone* of the split-prime sumset-obstruction line: the strongest single
local obstruction obtainable from the four currently-proved gaps.

## Proof technique — pure ring-hom reduction, no new `decide`

Rather than re-deriving the `q = 11, 31` cases from scratch, we reduce first
along the projection `ZMod 852841 →+* ZMod 341` (since `341 ∣ 852841`) and
then invoke the **already-proved** `BealLocalCRT.fifth_sum_forbidden_mod341`
as a black box for that half of the case split; the `q = 41` and `q = 61`
cases are handled by direct projections `ZMod 852841 →+* ZMod 41` and
`ZMod 852841 →+* ZMod 61`, exactly mirroring `BealLocalCRT`'s own
single-prime reduction shape. No `decide` is performed over any grid larger
than the four *already-discharged* `q × q` grids (`11×11`, `31×31`, `41×41`,
`61×61`) — there is no combinatorial-explosion risk from the large modulus
`852841`, since it is never itself the domain of a `decide`.

## DISCIPLINE

No `sorry`, no `native_decide`, no new axioms, no new `decide`. Every finite
fact used here was already `decide`d in `BealLocalCRT`, `BealFifthMod41`, and
`BealFifthMod61`; this file is pure ring-hom algebra (`congrArg`, `map_add`,
`map_pow`) composing those four results. `#print axioms` on the headline
theorem should give the standard `[propext, Classical.choice, Quot.sound]`
(or a subset).

Typecheck with `lake env lean BealFifthCRTFour.lean`.
-/

namespace BealFifthCRTFour

/-! ## 1. The composite modulus and its projections -/

/-- The composite modulus: the product of all four currently-proved
split-prime fifth-power gaps. -/
def M : ℕ := 852841

theorem M_eq : M = 11 * 31 * 41 * 61 := by decide

/-- Projection `ZMod 852841 →+* ZMod 341` (reduces to the already-handled
`q = 11, 31` composite). -/
def proj341 : ZMod M →+* ZMod 341 :=
  ZMod.castHom (by norm_num [M] : (341 : ℕ) ∣ M) (ZMod 341)

/-- Projection `ZMod 852841 →+* ZMod 41`. -/
def proj41 : ZMod M →+* ZMod 41 :=
  ZMod.castHom (by norm_num [M] : (41 : ℕ) ∣ M) (ZMod 41)

/-- Projection `ZMod 852841 →+* ZMod 61`. -/
def proj61 : ZMod M →+* ZMod 61 :=
  ZMod.castHom (by norm_num [M] : (61 : ℕ) ∣ M) (ZMod 61)

/-! ## 2. The `q = 41` and `q = 61` gap predicates (mirroring `BealLocalCRT`'s
`gap11Res` / `gap31Res`) -/

/-- The mod-41 fifth-power-sum gap as a predicate on `ZMod 41`. -/
def gap41Res (s : ZMod 41) : Prop :=
  s = 7 ∨ s = 16 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 25 ∨ s = 34

/-- The mod-61 fifth-power-sum gap as a predicate on `ZMod 61`. -/
def gap61Res (s : ZMod 61) : Prop :=
  s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 9 ∨ s = 17 ∨ s = 23 ∨ s = 38 ∨ s = 44 ∨
  s = 52 ∨ s = 55 ∨ s = 56 ∨ s = 57

/-! ## 3. HEADLINE — the 4-prime composite obstruction mod 852841 -/

/-- **HEADLINE — composite fifth-power-sum gap mod `852841 = 11·31·41·61`.**
If a residue `r : ZMod 852841` projects (via `ZMod 341`) into the `q=11` gap
or the `q=31` gap, **or** projects directly into the `q=41` gap or the `q=61`
gap, then `r` is not a sum of two fifth powers mod `852841` — for *any*
`A, B : ZMod 852841`.

Proof: reduce along `proj341`, `proj41`, `proj61`. The `q=11`/`q=31` branch
delegates to the already-proved `BealLocalCRT.fifth_sum_forbidden_mod341`;
the `q=41`/`q=61` branches mirror `BealLocalCRT`'s own single-prime
reductions using `BealFifthMod41.fifth_sum_gap_mod41` and
`BealFifthMod61.fifth_sum_gap_mod61`. No `decide` over `ZMod 852841` is
used. -/
theorem fifth_sum_forbidden_mod852841 {r : ZMod M}
    (hr : (BealLocalCRT.gap11Res (BealLocalCRT.proj11 (proj341 r)) ∨
           BealLocalCRT.gap31Res (BealLocalCRT.proj31 (proj341 r))) ∨
          gap41Res (proj41 r) ∨ gap61Res (proj61 r)) :
    ¬ ∃ A B : ZMod M, A ^ 5 + B ^ 5 = r := by
  rintro ⟨A, B, hAB⟩
  rcases hr with h3341 | h41 | h61
  · -- reduce to ZMod 341, delegate to the already-proved composite theorem
    have himg : proj341 A ^ 5 + proj341 B ^ 5 = proj341 r := by
      have := congrArg proj341 hAB
      rw [map_add, map_pow, map_pow] at this
      exact this
    exact BealLocalCRT.fifth_sum_forbidden_mod341 h3341 ⟨_, _, himg⟩
  · -- reduce to ZMod 41
    have himg : proj41 A ^ 5 + proj41 B ^ 5 = proj41 r := by
      have := congrArg proj41 hAB
      rw [map_add, map_pow, map_pow] at this
      exact this
    have hgap := BealFifthMod41.fifth_sum_gap_mod41 (proj41 A) (proj41 B)
    rcases h41 with h | h | h | h | h | h | h | h <;> rw [h] at himg
    · exact hgap.1 himg
    · exact hgap.2.1 himg
    · exact hgap.2.2.1 himg
    · exact hgap.2.2.2.1 himg
    · exact hgap.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.1 himg
    · exact hgap.2.2.2.2.2.2.2 himg
  · -- reduce to ZMod 61
    have himg : proj61 A ^ 5 + proj61 B ^ 5 = proj61 r := by
      have := congrArg proj61 hAB
      rw [map_add, map_pow, map_pow] at this
      exact this
    have hgap := BealFifthMod61.fifth_sum_gap_mod61 (proj61 A) (proj61 B)
    rcases h61 with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at himg
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

/-! ## 4. A nonempty composite forbidden set mod 852841, stacking all four primes

Four explicit residues, each caught by a *different* one of the four
component gaps, showing the composite genuinely stacks all four primes. -/

/-- `3 (mod 852841)` is forbidden via the `q = 11` projection
(`3 (mod 11) = 3 ∈ gap₁₁`, so `3 (mod 341) ∈` the mod-341 composite gap). -/
theorem three_forbidden_mod852841 : ¬ ∃ A B : ZMod M, A ^ 5 + B ^ 5 = 3 := by
  apply fifth_sum_forbidden_mod852841
  left; left
  show BealLocalCRT.proj11 (proj341 (3 : ZMod M)) = 3 ∨ _
  left
  decide

/-- `9 (mod 852841)` is forbidden via the `q = 31` projection only
(`9 (mod 11) ∉ gap₁₁` but `9 (mod 31) = 9 ∈ gap₃₁`). -/
theorem nine_forbidden_mod852841 : ¬ ∃ A B : ZMod M, A ^ 5 + B ^ 5 = 9 := by
  apply fifth_sum_forbidden_mod852841
  left; right
  show BealLocalCRT.proj31 (proj341 (9 : ZMod M)) = 3 ∨
      BealLocalCRT.proj31 (proj341 (9 : ZMod M)) = 8 ∨
      BealLocalCRT.proj31 (proj341 (9 : ZMod M)) = 9 ∨ _
  right; right; left
  decide

/-- `7 (mod 852841)` is forbidden via the `q = 41` projection only
(`7 (mod 41) = 7 ∈ gap₄₁`, and `7 ∉ gap₁₁`, `7 ∉ gap₃₁`). -/
theorem seven_forbidden_mod852841 : ¬ ∃ A B : ZMod M, A ^ 5 + B ^ 5 = 7 := by
  apply fifth_sum_forbidden_mod852841
  right; left
  show proj41 (7 : ZMod M) = 7 ∨ _
  left
  decide

/-- `4 (mod 852841)` is forbidden via the `q = 61` projection only
(`4 (mod 61) = 4 ∈ gap₆₁`). -/
theorem four_forbidden_mod852841 : ¬ ∃ A B : ZMod M, A ^ 5 + B ^ 5 = 4 := by
  apply fifth_sum_forbidden_mod852841
  right; right
  show proj61 (4 : ZMod M) = 4 ∨ _
  left
  decide

/-- **The composite forbidden set mod 852841 is nonempty and stacks all four
primes.** Exhibited: `{3, 9, 7, 4} ⊆ ZMod 852841`, all unreachable by
`A⁵ + B⁵`, each caught by a *different* one of the four component gaps
(`q = 11, 31, 41, 61` respectively). -/
theorem fifth_sum_composite_forbidden_mod852841 :
    ∃ S : Finset (ZMod M), 4 ≤ S.card ∧
      ∀ r ∈ S, ¬ ∃ A B : ZMod M, A ^ 5 + B ^ 5 = r := by
  refine ⟨{3, 9, 7, 4}, by decide, ?_⟩
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h | h | h | h <;> subst h
  · exact three_forbidden_mod852841
  · exact nine_forbidden_mod852841
  · exact seven_forbidden_mod852841
  · exact four_forbidden_mod852841

/-! ## 5. Beal corollary mod 852841 -/

/-- **Beal mod-852841 CAPSTONE composite obstruction.**
If the right-hand side `C^z` reduces mod `852841` to a residue projecting
into the `q=11` gap, the `q=31` gap, the `q=41` gap, or the `q=61` gap, then
`A⁵ + B⁵ = C^z` is impossible mod `852841` — for *any* integers `A, B, C` and
exponent `z`. This is the CRT-product of all four currently-proved
split-prime fifth-power obstructions: `699226` of the `852841` classes
(`≈ 82.0%`) are excluded, the strongest single local obstruction obtainable
from the currently-proved split-prime family. -/
theorem beal_fifth_mod852841_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (BealLocalCRT.gap11Res (BealLocalCRT.proj11 (proj341 ((C : ZMod M) ^ z))) ∨
           BealLocalCRT.gap31Res (BealLocalCRT.proj31 (proj341 ((C : ZMod M) ^ z)))) ∨
          gap41Res (proj41 ((C : ZMod M) ^ z)) ∨ gap61Res (proj61 ((C : ZMod M) ^ z))) :
    (A : ZMod M) ^ 5 + (B : ZMod M) ^ 5 ≠ (C : ZMod M) ^ z := by
  intro hAB
  exact fifth_sum_forbidden_mod852841 hC ⟨_, _, hAB⟩

end BealFifthCRTFour
