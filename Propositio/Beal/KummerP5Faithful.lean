import Propositio.Beal.RealReductionConcrete
import Mathlib.Tactic

/-!
# Faithful Kummer p=5 capstone — correcting the over-strong `hunit`

`BealKummerP5Assembly.beal_55z_kummer_conditional` states the (5,5,z) Beal reduction
conditional on

  `hunit : ∀ v : (𝓞 K)ˣ, v ∈ realUnits K → ∃ w, v = w ^ z`

i.e. *every* real unit is a `z`-th power.  **This hypothesis is over-strong — in fact
false for `z ≥ 2`**: the fundamental unit `φ = 1 + ζ + ζ⁴` is a real unit but is not a
`z`-th power (it is a generator of the rank-1 unit group modulo torsion).  A conditional
theorem with a false hypothesis is vacuously true and **can never be discharged**, so it
does not represent an honest frontier.

The *faithful* statement quantifies over only the **specific** descent unit `v` that the
reduction `beal_55z_reduced_to_real_unit` actually produces (which already packages the
conditional `(∃ w, v = w^z) → …`).  That conditional is dischargeable: `v = ±φⁿ` (the
fundamental unit theorem, proved as `beal_fundamental_unit_sqrt5_statement`), and `±φⁿ`
is a `z`-th power **iff `z ∣ n`** (for `z` odd, which holds since `gcd(z,10)=1`).

So the honest remaining input for the (5,5,z) family is the single divisibility

  `z ∣ n`   (where `v = ±φⁿ` is the descent unit's golden-ratio exponent),

which is an effective height bound on a linear form in logarithms of the *algebraic* unit
`φ` — genuinely Baker-class, and (unlike the Collatz `PowGap`, which is now reduced to the
*rational* irrationality measure of `log₂3`) it has no clean elementary slack.  The
corpus's "5th-power ⟹ `z`-th-power" step (`BealKummerP5Assembly` Wrapper 3, step 5) is the
**logical error**: in the infinite cyclic group `⟨φ⟩`, `v = w⁵` with `gcd(z,5)=1` does NOT
give `v = u^z` — that needs `z ∣ n`, not `5 ∣ n`.  The `mod λ⁴` analysis delivers only
`5 ∣ n` (necessary, not sufficient).

This file records the faithful capstone and isolates `z ∣ n` as the clean honest input.
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealKummerP5Faithful

/-! ## §1  The honest remaining input, abstractly: `z ∣ n ⟹ xⁿ is a z-th power` -/

/-- **`isPow_z_of_zdvd`.**  In any monoid, if `z ∣ n` then `xⁿ` is a `z`-th power.
This is the (only) direction needed to close the Beal descent: once the Baker-class
divisibility `z ∣ n` is known for the descent unit's exponent, the unit is a `z`-th
power and the reduction's conditional fires. -/
theorem isPow_z_of_zdvd {M : Type*} [Monoid M] (x : M) {n z : ℕ} (hz : z ∣ n) :
    ∃ w : M, x ^ n = w ^ z := by
  obtain ⟨m, rfl⟩ := hz
  exact ⟨x ^ m, by rw [← pow_mul, Nat.mul_comm]⟩

/-- **`zpow_isPow_z_of_zdvd`.**  Integer-exponent version in a group: `z ∣ n → xⁿ` is a
`z`-th power.  (The descent unit's exponent `n` is an integer; `φ` lives in the group
`(𝓞 K)ˣ`.)  The `−φⁿ` branch of the fundamental unit theorem is analogous for **odd** `z`
(which holds since `gcd(z,10)=1 ⟹ z` odd): `−1` is a central involution, so
`(−1)·xⁿ = (−x^{n/z})^z`. -/
theorem zpow_isPow_z_of_zdvd {G : Type*} [Group G] (x : G) {n : ℤ} {z : ℕ}
    (hz : (z : ℤ) ∣ n) : ∃ w : G, x ^ n = w ^ z := by
  obtain ⟨m, rfl⟩ := hz
  refine ⟨x ^ m, ?_⟩
  rw [← zpow_natCast (x ^ m) z, ← zpow_mul, Int.mul_comm]

/-! ## §2  The faithful conditional capstone -/

/-- **`beal_55z_kummer_faithful` — the corrected (5,5,z) capstone.**

Same conclusion as `BealKummerP5Assembly.beal_55z_kummer_conditional`, but conditional on
the **specific** descent unit `v` (exposed in the existential) being a `z`-th power — the
honest, *dischargeable* hypothesis — rather than the false `∀ real unit, is a z-th power`.

1. (Unconditional) `A + B = sᶻ`.
2. (Conditional, faithfully) there is a real unit `v` such that **if that `v`** is a
   `z`-th power then `A + B·ζ = Dᶻ`.

By the fundamental unit theorem `v = ±φⁿ`, so the hypothesis `∃ w, v = wᶻ` is exactly
`z ∣ n` (via §1) — the single Baker-class input.  No false universal. -/
theorem beal_55z_kummer_faithful {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) (hzcop : Nat.Coprime z 10) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧
      ((∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 5) (by norm_num)
  obtain ⟨s, _d, v, hABs, hvreal, himp⟩ :=
    BealRealReductionConcrete.beal_55z_reduced_to_real_unit hζ hAB h5 hz h hzcop
  exact ⟨⟨s, hABs⟩, v, hvreal, himp⟩

end BealKummerP5Faithful
