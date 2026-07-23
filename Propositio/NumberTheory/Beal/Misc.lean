import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# Bucket 2 — Beal density-bridge & cancellation ENGINE (Lean 4 mirror)

Lean 4 port of the genuinely-distinct **linear-congruence solvability engine**
of the LaTTe Beal development that the existing Lean mirrors
(`BealDensity`, `BealEisenstein`, `BealExponentImage`, `BealCountingStages`) do
**not** already capture.

## Why these are distinct (gap analysis)

The existing Lean counting layer (`BealDensity`) computes solution-set
*cardinalities* directly as kernel/range sizes of additive homs on `ZMod n`
(`solution_count`, `image_count`, `pair_solution_count`). That machinery makes
the *count* unconditional and never needs to phrase the underlying
**solvability biconditional**

    (∃ j, n ∣ d·j − m)  ⟺  g ∣ m            (g = gcd(d, n), threaded by a Bezout cert)

as a named theorem. But this biconditional is the load-bearing bridge of the
LaTTe `density_bridge.clj` layer (its T2 pair); it is the statement that decides
*whether* a congruence is solvable, which the cardinality view simply assumes
away. So it is distinct content worth a faithful named port.

Likewise the **mod-`n` cancellation** lemma (`cancellation_mod_n.clj` T2,
"L7"): `u·d + v·n = g`, `n = g·n'`, `g ≠ 0`, `n ∣ d·t  ⟹  n' ∣ t`. This is the
arithmetic core that turns "two solutions" into "their indices agree mod `n'`",
and the LaTTe coset-counting bijection rests on it. The Lean kernel-cardinality
proof gets the same conclusion structurally (cosets of the kernel), but never
states this cancellation step as a theorem. Distinct.

Finally the **three-number gcd from input certificates** (`density_bridge.clj`
T3, `gcd-three-from-certs`): given Bezout certs for `(a,b)` and `(g₁,c)`, derive
divisibility of `a`, `b`, `c` by `g₂` *and a combined Bezout cert*. `BealDensity.w_is_gcd_xy_n`
states the *characterisation* of `gcd(gcd x y) n` via `Nat.gcd`, but does **not**
produce a combined Bezout coefficient triple from input certificates — that
certificate-threading is the distinct content here, and we keep the LaTTe shape
(abstract divisors + explicit Bezout witnesses over `ℤ`).

## Faithfulness / modelling notes

We work over `ℤ`, exactly as the LaTTe sources (`latte-integers.int`). gcds are
threaded as *abstract divisors* `g` carrying divisor certificates (`g ∣ d`,
`g ∣ n`) and a Bezout witness (`u·d + v·n = g`), matching the LaTTe statements
one-for-one (LaTTe has no `Int.gcd` rewriting), in the same style already used by
`BealExponentImage.lean`. Each theorem's hypothesis list mirrors its LaTTe
sibling's binder list verbatim.

House style follows `BealDensity.lean` / `BealExponentImage.lean`: each theorem
carries a doc-comment ending in `LaTTe sibling: <clj path> :: <name>`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17).
Typecheck with `lake env lean BealMisc.lean`.

Key mathlib lemmas relied on:
* `dvd_add`, `dvd_sub`, `Dvd.Dvd.mul_left`, `Dvd.Dvd.mul_right` (ℤ divisibility).
* `dvd_trans` — transitivity for the certificate-threaded gcds.
* `mul_left_cancel₀` — the `g ≠ 0` cancellation step of `cancellation-mod-n`.
-/

namespace BealMisc

set_option linter.unusedVariables false

/-! ## 1. Density-bridge T2 — the solvability biconditional

`m` lies in the exponent-image of `d` on `Z/nZ` (i.e. `∃ j, n ∣ d·j − m`) iff
the threaded gcd `g` divides `m`. The two directions are stated as separate
theorems exactly as in `density_bridge.clj`. -/

/-- **Solvability ⟹ gcd divides** (density-bridge T2, forward).

If `g ∣ d`, `g ∣ n`, and there is some `j` with `n ∣ (d·j − m)`, then `g ∣ m`.

This is the "only solvable when `g ∣ m`" half of the linear-congruence
solvability biconditional: `g ∣ d·j` (from `g ∣ d`) and `g ∣ n ∣ (d·j − m)`,
so `g` divides their difference `m`.

LaTTe sibling: `src/ai_math/beal/density_bridge.clj` ::
`exponent-image-hit-implies-gcd-divides`. -/
theorem exponent_image_hit_implies_gcd_divides
    (d n m g u v : ℤ)
    (hgd : g ∣ d) (hgn : g ∣ n)
    (hex : ∃ j : ℤ, n ∣ (d * j - m)) :
    g ∣ m := by
  obtain ⟨j, hj⟩ := hex
  have hg_dj : g ∣ d * j := hgd.mul_right j
  have hg_diff : g ∣ (d * j - m) := dvd_trans hgn hj
  -- g ∣ d·j and g ∣ (d·j − m) ⟹ g ∣ (d·j − (d·j − m)) = m.
  have := dvd_sub hg_dj hg_diff
  simpa using this

/-- **gcd divides ⟹ solvable** (density-bridge T2, backward).

If `u·d + v·n = g` (a Bezout cert for `(d, n)`) and `g ∣ m`, then there is a `j`
with `n ∣ (d·j − m)`.

Write `m = g·t`; take `j = u·t`. Then
`d·(u·t) − m = t·(u·d) − g·t = t·(u·d − g) = t·(−v·n) = n·(−t·v)`.

LaTTe sibling: `src/ai_math/beal/density_bridge.clj` ::
`gcd-divides-implies-exponent-image-hit`. -/
theorem gcd_divides_implies_exponent_image_hit
    (d n m g u v : ℤ)
    (hbez : u * d + v * n = g) (hgm : g ∣ m) :
    ∃ j : ℤ, n ∣ (d * j - m) := by
  obtain ⟨t, ht⟩ := hgm
  refine ⟨u * t, -t * v, ?_⟩
  have hud : u * d = g - v * n := by linarith [hbez]
  rw [ht]
  have hdt : d * (u * t) = (u * d) * t := by ring
  rw [hdt, hud]; ring

/-! ## 2. Density-bridge T3 — three-number gcd from input certificates -/

/-- **Three-number gcd from input certs** (density-bridge T3).

Given a Bezout cert for `(a, b)` (`g₁ ∣ a`, `g₁ ∣ b`, `u₁·a + v₁·b = g₁`) and a
Bezout cert for `(g₁, c)` (`g₂ ∣ g₁`, `g₂ ∣ c`, `x·g₁ + y·c = g₂`), conclude
`g₂ ∣ a`, `g₂ ∣ b`, `g₂ ∣ c`, **and** the combined Bezout cert
`(x·u₁)·a + (x·v₁)·b + y·c = g₂`.

Divisibilities by `dvd_trans` (`g₂ ∣ g₁ ∣ a`, etc.); the combined cert by
substituting `g₁ = u₁·a + v₁·b` into `g₂ = x·g₁ + y·c` and expanding.

LaTTe sibling: `src/ai_math/beal/density_bridge.clj` :: `gcd-three-from-certs`. -/
theorem gcd_three_from_certs
    (a b c g₁ u₁ v₁ g₂ x y : ℤ)
    (hg1a : g₁ ∣ a) (hg1b : g₁ ∣ b) (hbez1 : u₁ * a + v₁ * b = g₁)
    (hg2g1 : g₂ ∣ g₁) (hg2c : g₂ ∣ c) (hbez2 : x * g₁ + y * c = g₂) :
    g₂ ∣ a ∧ g₂ ∣ b ∧ g₂ ∣ c ∧
      (x * u₁) * a + (x * v₁) * b + y * c = g₂ := by
  refine ⟨dvd_trans hg2g1 hg1a, dvd_trans hg2g1 hg1b, hg2c, ?_⟩
  -- g₂ = x·g₁ + y·c = x·(u₁·a + v₁·b) + y·c = (x·u₁)·a + (x·v₁)·b + y·c.
  rw [← hbez2, ← hbez1]; ring

/-! ## 3. cancellation-mod-n (L7) — the mod-`n` cancellation engine -/

/-- **Cancellation mod n** (`cancellation_mod_n.clj` T2, "L7").

If `u·d + v·n = g` (Bezout cert), `n = g·n'`, `g ≠ 0`, and `n ∣ (d·t)`, then
`n' ∣ t`.

Proof. From the cert, `t·g = u·(d·t) + v·(n·t)`. Both `d·t` (hypothesis) and
`n·t` are divisible by `n`, so `n ∣ t·g`; write `t·g = n·k = (g·n')·k`. Then
`g·t = g·(n'·k)`, and cancelling the nonzero `g` gives `t = n'·k`, i.e.
`n' ∣ t`.

LaTTe sibling: `src/ai_math/beal/cancellation_mod_n.clj` :: `cancellation-mod-n`. -/
theorem cancellation_mod_n
    (d n g n' u v t : ℤ)
    (hbez : u * d + v * n = g) (hn_eq : n = g * n') (hg_nz : g ≠ 0)
    (hdt : n ∣ (d * t)) :
    n' ∣ t := by
  -- n ∣ t·g : t·g = u·(d·t) + v·(n·t), and n divides both summands.
  obtain ⟨s, hs⟩ := hdt                 -- d·t = n·s
  have htg : t * g = n * (u * s + v * t) := by
    have : t * g = u * (d * t) + v * (n * t) := by
      rw [← hbez]; ring
    rw [this, hs]; ring
  -- t·g = (g·n')·(u·s + v·t) ⟹ g·t = g·(n'·(u·s+v·t)).
  have hgt : g * t = g * (n' * (u * s + v * t)) := by
    have h1 : t * g = g * t := by ring
    rw [← h1, htg, hn_eq]; ring
  -- cancel g ≠ 0.
  have ht_eq : t = n' * (u * s + v * t) := mul_left_cancel₀ hg_nz hgt
  exact ⟨u * s + v * t, ht_eq⟩

end BealMisc
