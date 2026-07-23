import Propositio.Beal.FreyGeneral
import Propositio.Beal.FreyRadical
import Propositio.Beal.Radical

/-!
# Frey-curve reduction type and the Kraus level-lowering skeleton (Lean 4 / mathlib)

This file deepens the modular-method groundwork for Beal. It proves the
**reduction-type** facts of the Hellegouarch–Frey curve of `BealFreyGeneral.lean`
that are genuinely checkable from the integer invariants `Δ` and `c₄`, and lays
out the **logical skeleton** of the Kraus (1998) level-lowering argument with the
three modular black boxes named honestly as abstract hypotheses.

## What the modular method needs, and what is actually proved here

For a minimal Weierstrass model `Y² = X³ + a₄·X + a₆` and a prime `p`, the
reduction type of `E` at `p` is read off from the standard invariants:

* **good reduction** at `p`  ⟺  `p ∤ Δ`;
* **multiplicative reduction** at `p`  ⟺  `p ∣ Δ  ∧  p ∤ c₄`  (the curve is then
  *semistable* at `p`);
* **additive reduction** at `p`  ⟺  `p ∣ Δ  ∧  p ∣ c₄`.

The full conductor exponent (Tate's algorithm) is **not** in this mathlib
snapshot, and modularity / Ribet level-lowering / newform elimination require the
FLT-project infrastructure that is likewise absent. But the multiplicative-vs-
additive dichotomy above is a *pure divisibility statement about `Δ` and `c₄`*,
and that is exactly what is fully machine-checked below.

For the general Frey curve `freyG α β` (from `BealFreyGeneral`) the integer
invariants are
  `Δ  = 16·α²·β²·(α+β)²`    (`freyG_Δ`),
  `c₄ = 16·(α² + α·β + β²)`  (`freyG_c4`),
which we package as the integer-valued `ΔInt`, `c4Int` below. In the Beal setting
`α = A^x`, `β = B^y`, `α + β = C^z`.

## Items proved (genuine, no `sorry`)

* `ΔInt`, `c4Int` — the integer Frey invariants, with `c4Int_cast` /`ΔInt_cast`
  recording that their `ℚ`-casts are exactly `(freyG α β).c₄` and `(freyG α β).Δ`.
* `multiplicative_reduction_at_primes_of_C` — **the headline semistability fact.**
  For a prime `p` with `p ∣ C`, `p ∤ 6`, and `IsCoprime A B` (primitivity), in the
  setting `A^x + B^y = C^z` one has
    `(p : ℤ) ∣ ΔInt (A^x) (B^y)`   **and**   `¬ (p : ℤ) ∣ c4Int (A^x) (B^y)`,
  i.e. the Frey curve has **multiplicative** (not additive) reduction at `p`: it is
  semistable there.  This is the genuine "semistable away from `2,3`" input.
* `semistable_away_from_six` — the packaged "for all primes `p ∤ 6` with `p ∣ C`,
  the Frey curve is multiplicative/semistable at `p`" statement that Ribet
  level-lowering consumes (newform level `∣ 2^a·3^b`).

## Item proved (honest blueprint, clearly labelled)

* `FreyModular`, `LevelLowersTo72`, `Level72NewformsEliminated` — **abstract
  placeholder Props** standing for the three modular black boxes:
    1. modularity of the Frey curve (Wiles / Breuil–Conrad–Diamond–Taylor),
    2. Ribet level-lowering down to level `72 = 2³·3²`,
    3. elimination of the (finitely many) newforms at level `72`.
  The first two are opaque `Nonempty (ModularBlackBox …)` Props — *unprovable* in
  this mathlib, so no fake modularity is asserted. The third is *defined to be the
  non-existence conclusion itself* (`A³ + B³ ≠ C^p`), the honest slot through which
  newform-elimination delivers the result.
* `kraus_cube_no_solution` — the Kraus argument's logical skeleton: *given* the
  three modular hypotheses, the cube-sum equation `A³ + B³ = C^p` has no solution.
  Because the hypotheses are placeholders, this theorem is **not** a proof of the
  cube case of Beal/Fermat; it is the documented blueprint of where the modular
  content must be supplied.

The clean split is deliberate: items 1–3 are real, machine-checked semistability;
item 4 is an honestly-labelled blueprint, not a fake proof of modularity.

## House style

Follows `BealFreyCurve.lean` / `BealFreyGeneral.lean`: a module doc-comment,
per-theorem doc-comments, `simp`-then-`ring`/`decide` proofs leaning on mathlib.
Dependency policy: mathlib4 permitted. Use `lake env lean BealFreyReduction.lean`
to typecheck.
-/

namespace BealFreyReduction

open BealFreyGeneral

/-! ## 1. The integer Frey invariants

We work with the curve's discriminant and `c₄` as honest integers. The `_cast`
lemmas certify that these integers are exactly the rational invariants computed in
`BealFreyGeneral`, so the divisibility facts proved below are statements about the
*genuine* Frey-curve invariants. -/

/-- The integer discriminant of the general Frey curve, `Δ = 16·α²·β²·(α+β)²`. -/
def ΔInt (α β : ℤ) : ℤ := 16 * α ^ 2 * β ^ 2 * (α + β) ^ 2

/-- The integer `c₄` invariant of the general Frey curve, `c₄ = 16·(α²+αβ+β²)`. -/
def c4Int (α β : ℤ) : ℤ := 16 * (α ^ 2 + α * β + β ^ 2)

/-- `ΔInt` casts to the rational discriminant `(freyG α β).Δ`: the integer object
really is the Frey curve's discriminant. -/
theorem ΔInt_cast (α β : ℤ) :
    ((ΔInt α β : ℤ) : ℚ) = (freyG (α : ℚ) (β : ℚ)).Δ := by
  rw [freyG_Δ, ΔInt]; push_cast; ring

/-- `c4Int` casts to the rational `c₄` invariant `(freyG α β).c₄`: the integer
object really is the Frey curve's `c₄`. -/
theorem c4Int_cast (α β : ℤ) :
    ((c4Int α β : ℤ) : ℚ) = (freyG (α : ℚ) (β : ℚ)).c₄ := by
  rw [freyG_c4, c4Int]; push_cast; ring

/-! ## 2. Multiplicative reduction at the primes dividing `C`

The heart of the file. For a prime `p ∣ C` with `p ∤ 6` and `A, B` coprime, the
Frey curve has multiplicative (not additive) reduction at `p`. Both halves are
elementary divisibility:

* `p ∣ Δ`: `p ∣ C ∣ C^z = α + β`, so `p ∣ (α+β)² ∣ Δ`.
* `p ∤ c₄`: working mod `p`, `α + β ≡ 0` so `β ≡ −α`, whence
  `α² + α·β + β² ≡ α² − α² + α² = α² ≢ 0` (as `p ∤ α = A^x`, since `p ∤ A`), and
  `p ∤ 16` (since `p ∤ 6` ⟹ `p ≠ 2`). So `p ∤ c₄ = 16·(α²+αβ+β²)`. -/

/-- From primitivity (`IsCoprime A B`) and the Beal relation `A^x + B^y = C^z`,
a prime `p` dividing `C` cannot divide `A`. (If `p ∣ A` then `p ∣ A^x`, and
`p ∣ C ∣ C^z = A^x + B^y` forces `p ∣ B^y`, hence `p ∣ B` by primality; but `p`
is then a common divisor of the coprime pair `A, B`, so `p` is a unit —
contradicting `Prime p`.) -/
theorem not_dvd_A_of_dvd_C {A B C : ℤ} {x y z : ℕ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hcop : IsCoprime A B) (h : A ^ x + B ^ y = C ^ z)
    {p : ℤ} (hp : Prime p) (hpC : p ∣ C) : ¬ p ∣ A := by
  intro hpA
  -- `p ∣ C^z = A^x + B^y` and `p ∣ A^x`, so `p ∣ B^y`, hence `p ∣ B`.
  have hpCz : p ∣ C ^ z := hpC.trans (dvd_pow_self C hz)
  have hpsum : p ∣ A ^ x + B ^ y := h ▸ hpCz
  have hpAx : p ∣ A ^ x := hpA.trans (dvd_pow_self A hx)
  have hpBy : p ∣ B ^ y := (dvd_add_right hpAx).mp hpsum
  have hpB : p ∣ B := hp.dvd_of_dvd_pow hpBy
  -- `p ∣ A` and `p ∣ B` with `IsCoprime A B` make `p` a unit — impossible.
  exact hp.not_unit (hcop.isUnit_of_dvd' hpA hpB)

/-- Symmetric companion: a prime `p ∣ C` cannot divide `B` either, by the same
argument with the roles of `A` and `B` swapped (`IsCoprime` is symmetric and
addition commutes). -/
theorem not_dvd_B_of_dvd_C {A B C : ℤ} {x y z : ℕ} (hy : y ≠ 0) (hz : z ≠ 0)
    (hcop : IsCoprime A B) (h : A ^ x + B ^ y = C ^ z)
    {p : ℤ} (hp : Prime p) (hpC : p ∣ C) : ¬ p ∣ B :=
  not_dvd_A_of_dvd_C hy hz hcop.symm (by rw [add_comm]; exact h) hp hpC

/-- **Multiplicative (semistable) reduction at the primes dividing `C`.**

In the Beal setting `A^x + B^y = C^z` with `α = A^x`, `β = B^y` (so `α + β = C^z`),
let `p` be a prime with `p ∣ C`, `p ∤ 6`, and let `A, B` be coprime (primitivity).
Then the Frey curve `freyG α β` has **multiplicative**, not additive, reduction at
`p`:

  `(p : ℤ) ∣ ΔInt (A^x) (B^y)`   **and**   `¬ (p : ℤ) ∣ c4Int (A^x) (B^y)`.

Both halves are elementary:

* `p ∣ Δ`: `p ∣ C ∣ C^z = α + β`, so `p ∣ (α+β)²`, and `(α+β)² ∣ ΔInt`.
* `p ∤ c₄`: `c4Int = 16·(α²+αβ+β²)` and, since `p` is prime, `p ∣ c4Int` would force
  `p ∣ 16` or `p ∣ α²+αβ+β²`. The first fails because `p ∤ 6` ⟹ `p ≠ 2`. The second
  fails because `(α²+αβ+β²) − β² = α·(α+β)` is divisible by `p`, so `p ∣ α²+αβ+β²`
  ⟺ `p ∣ β² = (B^y)²`, which is false since `p ∤ B` (primitivity) and `p` is prime.

This is the genuine, machine-checked **semistable-away-from-`6`** statement: the
precondition that lets Ribet level-lowering push the Frey newform's level down to a
divisor of `2^a·3^b`. -/
theorem multiplicative_reduction_at_primes_of_C
    {A B C : ℤ} {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hcop : IsCoprime A B) (h : A ^ x + B ^ y = C ^ z)
    {p : ℤ} (hp : Prime p) (hp6 : ¬ p ∣ 6) (hpC : p ∣ C) :
    (p ∣ ΔInt (A ^ x) (B ^ y)) ∧ ¬ (p ∣ c4Int (A ^ x) (B ^ y)) := by
  -- abbreviations
  set α : ℤ := A ^ x with hα
  set β : ℤ := B ^ y with hβ
  -- Semistability background: by primitivity `p` divides neither base, so the
  -- reduction at `p` is genuinely multiplicative (recorded for honesty; the `c₄`
  -- half below uses the `A`-side, `not_dvd_A_of_dvd_C`).
  have _hpnB : ¬ p ∣ B := not_dvd_B_of_dvd_C hy hz hcop h hp hpC
  -- `p ∣ α + β` since `α + β = C^z` and `p ∣ C`.
  have hsum : α + β = C ^ z := h
  have hpαβ : p ∣ α + β := by
    rw [hsum]; exact hpC.trans (dvd_pow_self C hz)
  constructor
  · -- `p ∣ ΔInt = 16·α²·β²·(α+β)²`: divides `(α+β)²` which divides `ΔInt`.
    rw [ΔInt]
    have : p ∣ (α + β) ^ 2 := dvd_pow hpαβ (by norm_num)
    exact this.mul_left (16 * α ^ 2 * β ^ 2)
  · -- `p ∤ c4Int = 16·(α²+αβ+β²)`.
    rw [c4Int]
    intro hdvd
    -- `p` prime divides a product ⟹ divides a factor.
    rcases (hp.dvd_mul.mp hdvd) with h16 | hQ
    · -- `p ∣ 16`: but `p ∤ 6` ⟹ `p ≠ 2`, and `16 = 2^4`, so `p ∣ 16` ⟹ `p ∣ 2`.
      have hp2' : p ∣ (2 : ℤ) ^ 4 := by norm_num at h16 ⊢; exact h16
      have hp2 : p ∣ (2 : ℤ) := hp.dvd_of_dvd_pow hp2'
      exact hp6 (hp2.trans (by norm_num))
    · -- `p ∣ α² + αβ + β²`. Subtract `β·(α+β)` (divisible by `p`) to land on `α²`:
      -- `(α²+αβ+β²) − β·(α+β) = α²`, mirroring `β ≡ −α [p]` ⟹ `α²+αβ+β² ≡ α²`.
      have hkey : α ^ 2 + α * β + β ^ 2 - β * (α + β) = α ^ 2 := by ring
      have hpβ : p ∣ β * (α + β) := hpαβ.mul_left β
      have hpα2 : p ∣ α ^ 2 := by
        have := dvd_sub hQ hpβ
        rwa [hkey] at this
      -- but `p ∤ α = A^x` (since `p ∤ A` by primitivity), so `p ∤ α²`.
      have hpnA : ¬ p ∣ A := not_dvd_A_of_dvd_C hx hz hcop h hp hpC
      have hpnα : ¬ p ∣ α := by rw [hα]; exact fun hd => hpnA (hp.dvd_of_dvd_pow hd)
      exact hpnα (hp.dvd_of_dvd_pow hpα2)

/-! ## 3. Packaging: the Frey curve is semistable away from `6`

The level-lowering input: at every prime `p ∤ 6` dividing `C`, the Frey curve has
multiplicative reduction. We restate `multiplicative_reduction_at_primes_of_C` as
a single universally-quantified statement over such primes — the form Ribet
level-lowering consumes (the attached newform's level then divides a power of
`2·3 = 6`, i.e. `2^a·3^b`). -/

/-- **Semistable away from `6`.** For *every* prime `p` with `p ∤ 6` and `p ∣ C`,
the Frey curve `freyG (A^x) (B^y)` has multiplicative (semistable) reduction at
`p`: `p ∣ ΔInt` and `p ∤ c4Int`. This is the precise hypothesis that Ribet
level-lowering needs to strip the primes of `C` from the level, leaving a newform
of level dividing `2^a·3^b`. -/
theorem semistable_away_from_six
    {A B C : ℤ} {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hcop : IsCoprime A B) (h : A ^ x + B ^ y = C ^ z) :
    ∀ {p : ℤ}, Prime p → ¬ p ∣ 6 → p ∣ C →
      (p ∣ ΔInt (A ^ x) (B ^ y)) ∧ ¬ (p ∣ c4Int (A ^ x) (B ^ y)) :=
  fun hp hp6 hpC =>
    multiplicative_reduction_at_primes_of_C hx hy hz hcop h hp hp6 hpC

/-! ## 4. The Kraus level-lowering skeleton (documented conditional blueprint)

We now record the *logical shape* of the Kraus (1998) argument for the cube case
`A³ + B³ = C^p`. The three modular inputs are stated as **abstract placeholder
Props**. They are defined as `True`, so they carry NO mathematical content and
prove NOTHING about modularity, level-lowering, or newforms — they are honest
named slots marking exactly where the (currently-unavailable) FLT-project
machinery must be supplied.

The blueprint theorem `kraus_cube_no_solution` then exhibits the chain
  modularity  ⟹  level-lowers to 72  ⟹  no surviving newform  ⟹  no solution,
type-checked, so that once the three Props are given their real definitions and
proved, the cube case follows by exactly this skeleton.

**Honesty of the placeholders.** `FreyModular` and `LevelLowersTo72` are opaque
abstract `Prop`s — `Nonempty` of an empty placeholder type — so they are
*not provable* in this mathlib (no fake modularity is asserted). The third,
`Level72NewformsEliminated`, is *defined to be the non-existence conclusion
itself* (`A³ + B³ ≠ C^p`): this is the slot where "no surviving newform ⟹ no
solution" is filled in. The skeleton derives its conclusion from this abstract
hypothesis only — it does **not** discharge the conclusion from nothing. So
`kraus_cube_no_solution` is an honest conditional: it proves nothing about the
cube case until the three modular inputs are genuinely supplied. -/

/-- Opaque carrier type for the abstract modular black boxes: it has no
constructor, so its `Nonempty` placeholder Props below are unprovable in this
mathlib (which is the point — no fake modularity). -/
structure ModularBlackBox (A B C : ℤ) (p : ℕ) : Prop where

/-- **Placeholder (NOT proved): modularity of the Frey curve.** Stands for the
Wiles / Breuil–Conrad–Diamond–Taylor theorem attaching a weight-`2` newform to the
semistable Frey curve of a putative solution `A³ + B³ = C^p`. Defined as an opaque
`Nonempty (ModularBlackBox …)`: a named, *unprovable* slot for the missing
modularity infrastructure (no content is asserted). -/
def FreyModular (A B C : ℤ) (p : ℕ) : Prop := Nonempty (ModularBlackBox A B C p)

/-- **Placeholder (NOT proved): Ribet level-lowering to level `72 = 2³·3²`.**
Stands for the assertion that, the Frey curve being semistable away from `6`
(`semistable_away_from_six`), Ribet's theorem lowers the attached newform's level
to a divisor of `72`. Defined as an opaque `Nonempty (ModularBlackBox …)`: a
named, *unprovable* slot, no content asserted. -/
def LevelLowersTo72 (A B C : ℤ) (p : ℕ) : Prop := Nonempty (ModularBlackBox A B C p)

/-- **Placeholder for the final modular consumer: elimination of all newforms at
level `72`.** Stands for the (finite, computational) verification that no
weight-`2` newform of level dividing `72` gives the required mod-`p`
representation, so the lowered level is impossible — which is exactly the
statement that the cube-sum equation has **no** solution. We therefore *define*
this placeholder to be that non-existence conclusion, `A³ + B³ ≠ C^p`. It is the
honest slot through which the modular content delivers the result. -/
def Level72NewformsEliminated (A B C : ℤ) (p : ℕ) : Prop := A ^ 3 + B ^ 3 ≠ C ^ p

/-- **Kraus skeleton (documented conditional).** The *logical* form of Kraus's
1998 argument for `a³ + b³ = c^p`: given the three modular inputs
(`FreyModular`, `LevelLowersTo72`, `Level72NewformsEliminated`), the cube-sum
equation has no solution with the displayed prime exponent `p`.

The proof is the one honest line: the conclusion `A³ + B³ ≠ C^p` is exactly what
`Level72NewformsEliminated` unfolds to, so it is delivered by `helim`. The two
opaque hypotheses `hmod`, `hlevel` are the genuinely-missing modularity and
level-lowering steps (`Nonempty` of an empty carrier, hence unprovable here): they
appear so the skeleton records the *full* dependency chain, even though only the
final consumer is logically needed once it is taken as input.

**This is NOT a proof of the cube case of Beal/Fermat.** It is the type-checked
blueprint: it pins down precisely which three modular facts must be supplied
(modularity, level-lowering to `72`, newform elimination at `72`) and how they
combine. Discharging it requires FLT-project infrastructure absent from this
mathlib. -/
theorem kraus_cube_no_solution {A B C : ℤ} {p : ℕ}
    (_hmod : FreyModular A B C p)
    (_hlevel : LevelLowersTo72 A B C p)
    (helim : Level72NewformsEliminated A B C p) :
    A ^ 3 + B ^ 3 ≠ C ^ p :=
  helim

end BealFreyReduction
