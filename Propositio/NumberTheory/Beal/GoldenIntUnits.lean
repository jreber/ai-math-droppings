import Propositio.NumberTheory.Beal.GoldenIntEuclidean
import Propositio.NumberTheory.Beal.FundamentalUnitPell
import Mathlib.Tactic

/-!
# `GoldenInt` unit transport — every unit of `ℤ[φ]` is `±φⁿ`

`BealGoldenIntEuclidean.lean` builds `GoldenInt` (the ring `ℤ[φ]`, `φ² = φ + 1`) as its own
type and proves it a full `EuclideanDomain` via the norm `N(a+bφ) = a²+ab-b²`.
`BealFundamentalUnitPell.lean` proves, working with the concrete real-number model
`a + b·φ ∈ ℝ`, that every element of norm `±1` equals `±φⁿ` for some `n : ℤ`
(`beal_fundamental_unit_sqrt5`).

This file is the **first of the three sub-bricks** scoped for FLT-5 Case II unit-pinning
(per the dispatch note and `docs/kb/failed/2026-07-12__fermatLastTheoremFive_caseTwo_descent.
json`): it transports `beal_fundamental_unit_sqrt5`'s unit-pinning fact into `GoldenInt`'s own
algebraic structure, i.e. genuinely working with `IsUnit` in the ring `GoldenInt` rather than
with the ℝ-model's norm-equation hypothesis directly.

## Main results (proved, axiom-clean, no `sorry`)

* `GoldenInt.toRealHom : GoldenInt →+* ℝ` — `toReal` packaged as an actual ring homomorphism
  (additivity + multiplicativity + unit-preservation), reusing `GoldenInt.toReal_mul` from
  `BealGoldenIntEuclidean.lean`.
* `GoldenInt.toReal_injective` — `toRealHom` is injective (via `GoldenInt.toReal_eq_zero_iff`).
* `GoldenInt.isUnit_iff_norm_eq_one` — `IsUnit z ↔ z.norm = 1 ∨ z.norm = -1`, the standard
  Euclidean-domain-with-multiplicative-norm characterization of units, proved directly from
  `GoldenInt.mul_conj_eq_ofInt` and `GoldenInt.norm_mul` (no abstract PID/UFD machinery needed).
* `GoldenInt.phi`, `GoldenInt.phiInv` — the concrete ring elements `φ = 0 + 1·φ` and
  `φ⁻¹ = φ - 1 = -1 + 1·φ`, and `GoldenInt.phi_mul_phiInv : phi * phiInv = 1` (so both are
  units).
* `GoldenInt.phiZpow : ℤ → GoldenInt` — the concrete family `φⁿ` for *all* `n : ℤ` (not just
  `n : ℕ`), defined via `phi ^ n.toNat` / `phiInv ^ (-n).toNat`, together with
  `GoldenInt.toReal_phiZpow : toReal (phiZpow n) = goldenRatio ^ n` (zpow in `ℝ`) tying it to
  the ℝ-model.
* `GoldenInt.unit_eq_pm_phiZpow` — **the transport theorem**: for `z : GoldenInt`, `IsUnit z →
  ∃ n : ℤ, z = phiZpow n ∨ z = -phiZpow n`. Every unit of the ring `GoldenInt` is `±φⁿ`.

## What this does NOT yet do (honest scope note)

This is unit-pinning only. It does **not** attempt to combine this with `case2_core` /
`case2_norm_eq` (`FermatLastTheoremFiveCaseTwo(Transplant).lean`) to build the actual infinite
descent for FLT-5 Case II — that (sub-bricks 2–3 of the scoped plan) needs a further
divisibility/valuation argument peeling the ramified prime `√5 = 2φ-1` off the norm equation
`N(a₁,b) = ∓5^k·e⁵`, which is genuinely new content not attempted here.

**No `sorry`, no project axiom** in what follows.
-/

namespace GoldenInt

open Real BealFundamentalUnitPell

/-! ## `toReal` as a ring homomorphism -/

@[simp] theorem toReal_zero : toReal (0 : GoldenInt) = 0 := by simp [toReal]

@[simp] theorem toReal_one : toReal (1 : GoldenInt) = 1 := by simp [toReal]

theorem toReal_add (z w : GoldenInt) : toReal (z + w) = toReal z + toReal w := by
  simp only [toReal, a_add, b_add]
  push_cast
  ring

theorem toReal_neg (z : GoldenInt) : toReal (-z) = -toReal z := by
  simp only [toReal, a_neg, b_neg]
  push_cast
  ring

/-- `toReal` packaged as a genuine ring homomorphism `GoldenInt →+* ℝ`. -/
noncomputable def toRealHom : GoldenInt →+* ℝ where
  toFun := toReal
  map_one' := toReal_one
  map_mul' := toReal_mul
  map_zero' := toReal_zero
  map_add' := toReal_add

@[simp] theorem toRealHom_apply (z : GoldenInt) : toRealHom z = toReal z := rfl

/-- **`toReal` is injective.** Follows from `toReal_eq_zero_iff` via the standard
"kernel trivial ⟹ injective" argument for an additive map. -/
theorem toReal_injective : Function.Injective toReal := by
  intro z w hzw
  have hsub : toReal (z - w) = 0 := by
    have : toReal z - toReal w = 0 := by rw [hzw]; ring
    calc toReal (z - w) = toReal z - toReal w := by
          show toReal (z + -w) = toReal z - toReal w
          rw [toReal_add, toReal_neg]; ring
      _ = 0 := this
  have : z - w = 0 := (toReal_eq_zero_iff (z - w)).mp hsub
  exact sub_eq_zero.mp this

/-! ## Unit characterization via the norm -/

/-- **`IsUnit z ↔ norm z = ±1`.** The standard Euclidean-domain-with-multiplicative-norm fact,
proved directly: if `z` is a unit, `norm z * norm z⁻¹ = norm 1 = 1` forces `norm z = ±1`
(product of two integers equal to `1`); conversely if `norm z = ±1`, `z * conj z = ofInt (norm z)`
exhibits an explicit inverse (`conj z` or `-conj z`). -/
theorem isUnit_iff_norm_eq_one (z : GoldenInt) : IsUnit z ↔ z.norm = 1 ∨ z.norm = -1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hmul : (↑u : GoldenInt) * ↑u⁻¹ = 1 := Units.mul_inv u
    have hnorm_mul : norm (↑u : GoldenInt) * norm (↑u⁻¹ : GoldenInt) = 1 := by
      rw [← norm_mul, hmul, norm_one]
    exact Int.eq_one_or_neg_one_of_mul_eq_one hnorm_mul
  · rintro (h1 | hm1)
    · refine ⟨⟨z, conj z, ?_, ?_⟩, rfl⟩
      · rw [mul_conj_eq_ofInt, h1]; ext <;> simp [ofInt]
      · rw [mul_comm, mul_conj_eq_ofInt, h1]; ext <;> simp [ofInt]
    · refine ⟨⟨z, -conj z, ?_, ?_⟩, rfl⟩
      · have heq : z * -conj z = -(z * conj z) := by ring
        rw [heq, mul_conj_eq_ofInt, hm1]; ext <;> simp [ofInt]
      · have heq : -conj z * z = -(z * conj z) := by ring
        rw [heq, mul_conj_eq_ofInt, hm1]; ext <;> simp [ofInt]

/-! ## The concrete generators `φ` and `φ⁻¹ = φ - 1` in `GoldenInt` -/

/-- The element `φ = 0 + 1·φ ∈ ℤ[φ]`. -/
def phi : GoldenInt := ⟨0, 1⟩

/-- The element `φ⁻¹ = φ - 1 = -1 + 1·φ ∈ ℤ[φ]`. -/
def phiInv : GoldenInt := ⟨-1, 1⟩

@[simp] theorem a_phi : phi.a = 0 := rfl
@[simp] theorem b_phi : phi.b = 1 := rfl
@[simp] theorem a_phiInv : phiInv.a = -1 := rfl
@[simp] theorem b_phiInv : phiInv.b = 1 := rfl

theorem toReal_phi : toReal phi = goldenRatio := by simp [toReal]

theorem toReal_phiInv : toReal phiInv = goldenRatio - 1 := by
  simp only [toReal, a_phiInv, b_phiInv]
  push_cast
  ring

/-- **`φ · φ⁻¹ = 1` in `GoldenInt`.** Direct computation from the multiplication table. -/
theorem phi_mul_phiInv : phi * phiInv = 1 := by ext <;> simp [phi, phiInv]

theorem phiInv_mul_phi : phiInv * phi = 1 := by ext <;> simp [phi, phiInv]

theorem isUnit_phi : IsUnit (phi : GoldenInt) := ⟨⟨phi, phiInv, phi_mul_phiInv, phiInv_mul_phi⟩, rfl⟩

/-! ## `φⁿ` for all `n : ℤ`, and its transport to `ℝ` -/

/-- The concrete family `φⁿ ∈ GoldenInt` for **all** `n : ℤ` (not just `n : ℕ`): for `n ≥ 0` it
is `phi ^ n.toNat`, and for `n < 0` it is `phiInv ^ (-n).toNat` (using that `phiInv` is a genuine
ring element of `GoldenInt`, since `φ⁻¹ = φ-1 ∈ ℤ[φ]`, so no field/localization is needed). -/
def phiZpow (n : ℤ) : GoldenInt := if 0 ≤ n then phi ^ n.toNat else phiInv ^ (-n).toNat

theorem phiZpow_of_nonneg {n : ℤ} (hn : 0 ≤ n) : phiZpow n = phi ^ n.toNat := by
  simp [phiZpow, hn]

theorem phiZpow_of_neg {n : ℤ} (hn : n < 0) : phiZpow n = phiInv ^ (-n).toNat := by
  simp [phiZpow, not_le.mpr hn]

/-- **`toReal (phiZpow n) = φⁿ`** (`zpow` in `ℝ`), tying the `GoldenInt` family to the
ℝ-model's `goldenRatio ^ n` used by `BealFundamentalUnitPell.beal_fundamental_unit_sqrt5`. -/
theorem toReal_pow (z : GoldenInt) (k : ℕ) : toReal (z ^ k) = (toReal z) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, toReal_mul, ih]

theorem toReal_phiZpow (n : ℤ) : toReal (phiZpow n) = goldenRatio ^ n := by
  by_cases hn : 0 ≤ n
  · rw [phiZpow_of_nonneg hn, toReal_pow, toReal_phi]
    have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have hz : goldenRatio ^ ((n.toNat : ℤ)) = goldenRatio ^ n.toNat := zpow_natCast goldenRatio n.toNat
    rw [hcast] at hz
    exact hz.symm
  · push Not at hn
    rw [phiZpow_of_neg hn, toReal_pow, toReal_phiInv]
    have hcast : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have hphiInv : goldenRatio - 1 = goldenRatio⁻¹ := (BealFundamentalUnitPell.phi_inv_eq).symm
    rw [hphiInv]
    have hz : (goldenRatio⁻¹) ^ (((-n).toNat : ℕ) : ℤ) = (goldenRatio⁻¹) ^ (-n).toNat :=
      zpow_natCast goldenRatio⁻¹ (-n).toNat
    rw [hcast] at hz
    rw [← hz, inv_zpow', neg_neg]

/-! ## The transport theorem -/

/-- **Every unit of `GoldenInt` is `±φⁿ`.** The main transport result: combines
`isUnit_iff_norm_eq_one` (unit ⟹ norm `±1`), `BealFundamentalUnitPell.beal_fundamental_unit_
sqrt5` (norm `±1` in the ℝ-model ⟹ `±φⁿ` in ℝ), `toReal_phiZpow` (bridging `GoldenInt`'s `φⁿ`
family to `ℝ`'s), and `toReal_injective` (transporting the ℝ-equality back to `GoldenInt`). -/
theorem unit_eq_pm_phiZpow {z : GoldenInt} (hz : IsUnit z) :
    ∃ n : ℤ, z = phiZpow n ∨ z = -phiZpow n := by
  have hnorm := (isUnit_iff_norm_eq_one z).mp hz
  have hN : z.a ^ 2 + z.a * z.b - z.b ^ 2 = 1 ∨ z.a ^ 2 + z.a * z.b - z.b ^ 2 = -1 := hnorm
  obtain ⟨n, hn⟩ := BealFundamentalUnitPell.beal_fundamental_unit_sqrt5 z.a z.b hN
  have hzreal : toReal z = (z.a : ℝ) + z.b * goldenRatio := rfl
  refine ⟨n, ?_⟩
  rcases hn with hn | hn
  · left
    apply toReal_injective
    rw [toReal_phiZpow, ← hn, hzreal]
  · right
    apply toReal_injective
    rw [toReal_neg, toReal_phiZpow, ← hn, hzreal]

end GoldenInt

section AxiomCheck
open GoldenInt
#print axioms toReal_add
#print axioms toReal_neg
#print axioms toReal_injective
#print axioms isUnit_iff_norm_eq_one
#print axioms phi_mul_phiInv
#print axioms isUnit_phi
#print axioms toReal_phiZpow
#print axioms unit_eq_pm_phiZpow
end AxiomCheck
