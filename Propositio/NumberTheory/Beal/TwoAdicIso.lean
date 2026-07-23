import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units
import Propositio.NumberTheory.Beal.TwoDensity

/-!
# The 2-adic unit-group product decomposition `(ZMod (2^k))ˣ ≃* C₂ × C_{2^(k-2)}`

For `k ≥ 3`, `(ZMod (2^k))ˣ` is **not** cyclic
(`ZMod.isCyclic_units_two_pow_iff`); it is the internal direct product of
`⟨-1⟩` (order `2`) and `⟨5⟩` (order `2^(k-2)`).  This file builds the explicit
multiplicative isomorphism

  `(ZMod (2^(n+2)))ˣ ≃* (Subgroup.zpowers (-1)) × (Subgroup.zpowers 5)`

and uses `BealTwoDensity.count_of_mulEquiv_prod_cyclic` to close the `p = 2`,
`k ≥ 3` Beal-local pair-count.

Writing `k = n + 2`: for `k ≥ 3` we have `n ≥ 1`, but the iso itself works for
all `n ≥ 0` (for `n = 0`, i.e. `k = 2`, the `⟨5⟩` factor is trivial).

All lemmas are sorry-free and axiom-clean.
-/

open scoped Classical

namespace BealTwoAdicIso

/-! ## Stage 1 — the unit `5` and its order -/

/-- `5` is a unit in `ZMod (2^(n+2))`. -/
theorem isUnit_five (n : ℕ) : IsUnit (5 : ZMod (2 ^ (n + 2))) := by
  rw [show (5 : ZMod (2 ^ (n + 2))) = ((5 : ℕ) : ZMod (2 ^ (n + 2))) by push_cast; ring,
    ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ (by decide)

/-- The unit `5 : (ZMod (2^(n+2)))ˣ`. -/
noncomputable def u5 (n : ℕ) : (ZMod (2 ^ (n + 2)))ˣ := (isUnit_five n).unit

@[simp] theorem u5_coe (n : ℕ) :
    ((u5 n : (ZMod (2 ^ (n + 2)))ˣ) : ZMod (2 ^ (n + 2))) = 5 :=
  (isUnit_five n).unit_spec

/-- **Stage 1.** The unit `5` has order `2^n` in `(ZMod (2^(n+2)))ˣ`. -/
theorem orderOf_u5 (n : ℕ) : orderOf (u5 n) = 2 ^ n := by
  rw [← orderOf_units, u5_coe, ZMod.orderOf_five]

/-! ## Stage 2 — the unit `-1`: order `2`, and not a power of `5` -/

theorem two_lt (n : ℕ) : 2 < 2 ^ (n + 2) := by
  calc 2 < 4 := by norm_num
    _ = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem neg_one_ne_one_units (n : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ 1 := by
  haveI : Fact (2 < 2 ^ (n + 2)) := ⟨two_lt n⟩
  intro h
  rw [← Units.val_eq_one] at h
  simp only [Units.val_neg, Units.val_one] at h
  exact ZMod.neg_one_ne_one h

/-- **Stage 2a.** `-1` has order `2`. -/
theorem orderOf_neg_one (n : ℕ) : orderOf (-1 : (ZMod (2 ^ (n + 2)))ˣ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [neg_one_sq]) (neg_one_ne_one_units n)

theorem four_dvd (n : ℕ) : (4 : ℕ) ∣ 2 ^ (n + 2) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 (by omega)

/-- Reduction `(ZMod (2^(n+2)))ˣ →* (ZMod 4)ˣ`. -/
noncomputable def red (n : ℕ) : (ZMod (2 ^ (n + 2)))ˣ →* (ZMod 4)ˣ :=
  ZMod.unitsMap (four_dvd n)

/-- `5 ≡ 1 mod 4`, so `red` kills `u5`. -/
theorem red_u5 (n : ℕ) : (red n) (u5 n) = 1 := by
  apply Units.ext
  rw [red, ZMod.unitsMap_val, u5_coe, Units.val_one,
    show (5 : ZMod (2 ^ (n + 2))) = ((5 : ℕ) : ZMod (2 ^ (n + 2))) by push_cast; ring,
    ZMod.cast_natCast (four_dvd n)]
  decide

/-- `red` sends `-1` to `-1`. -/
theorem red_neg_one (n : ℕ) : (red n) (-1) = -1 := by
  apply Units.ext
  rw [red, ZMod.unitsMap_val]
  simp only [Units.val_neg, Units.val_one]
  rw [show ((-1 : ZMod (2 ^ (n + 2)))) = (-(1 : ZMod (2 ^ (n + 2)))) by ring,
    ZMod.cast_neg (four_dvd n), ZMod.cast_one (four_dvd n)]

/-- **Stage 2b.** `-1` is not a power of `5`: `-1 ∉ ⟨5⟩`. -/
theorem neg_one_not_mem_zpowers_u5 (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 2)))ˣ) ∉ Subgroup.zpowers (u5 n) := by
  rw [Subgroup.mem_zpowers_iff]
  rintro ⟨z, hz⟩
  apply (show (-1 : (ZMod 4)ˣ) ≠ 1 by decide)
  have := congrArg (red n) hz
  rw [map_zpow, red_u5, one_zpow, red_neg_one] at this
  exact this.symm

/-! ## Cardinalities of the two cyclic factors and of the whole group -/

theorem card_zpowers_neg_one (n : ℕ) :
    Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 := by
  rw [Nat.card_zpowers]; exact orderOf_neg_one n

theorem card_zpowers_u5 (n : ℕ) :
    Nat.card (Subgroup.zpowers (u5 n)) = 2 ^ n := by
  rw [Nat.card_zpowers]; exact orderOf_u5 n

theorem card_units (n : ℕ) : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ (n + 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega), show n + 2 - 1 = n + 1 by omega]
  ring

/-! ## Stages 3 & 4 — the internal direct product MulEquiv -/

/-- The multiplication homomorphism `⟨-1⟩ × ⟨5⟩ →* (ZMod (2^(n+2)))ˣ`,
`(x, y) ↦ x * y`.  (The group is abelian, so this is a `MonoidHom`.) -/
noncomputable def prodHom (n : ℕ) :
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) × (Subgroup.zpowers (u5 n))
      →* (ZMod (2 ^ (n + 2)))ˣ :=
  (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)).subtype.coprod
    (Subgroup.zpowers (u5 n)).subtype

@[simp] theorem prodHom_apply (n : ℕ)
    (x : Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) (y : Subgroup.zpowers (u5 n)) :
    prodHom n (x, y) = (x : (ZMod (2 ^ (n + 2)))ˣ) * (y : (ZMod (2 ^ (n + 2)))ˣ) := by
  simp [prodHom]

/-- **Stage 3 (injectivity).** `⟨-1⟩ ⊓ ⟨5⟩ = ⊥`, so `prodHom` is injective. -/
theorem prodHom_injective (n : ℕ) : Function.Injective (prodHom n) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, y⟩ h
  rw [prodHom_apply] at h
  have hx : (x : (ZMod (2 ^ (n + 2)))ˣ) = ((y : (ZMod (2 ^ (n + 2)))ˣ))⁻¹ :=
    mul_eq_one_iff_eq_inv.mp h
  have hxmem5 : (x : (ZMod (2 ^ (n + 2)))ˣ) ∈ Subgroup.zpowers (u5 n) := by
    rw [hx]; exact (Subgroup.zpowers (u5 n)).inv_mem y.2
  have hxcases : (x : (ZMod (2 ^ (n + 2)))ˣ) = 1 ∨ (x : (ZMod (2 ^ (n + 2)))ˣ) = -1 := by
    have hxmem1 : (x : (ZMod (2 ^ (n + 2)))ˣ)
        ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ) := x.2
    rw [Subgroup.mem_zpowers_iff] at hxmem1
    obtain ⟨z, hz⟩ := hxmem1
    rcases Int.even_or_odd z with he | ho
    · left; rw [← hz]
      exact Even.neg_one_zpow (α := (ZMod (2 ^ (n + 2)))ˣ) he
    · right; rw [← hz]
      obtain ⟨m, rfl⟩ := ho
      rw [zpow_add, zpow_mul]
      simp [zpow_two]
  rcases hxcases with hx1 | hxm1
  · have hxe : x = 1 := by ext; rw [hx1]; rfl
    refine Prod.ext hxe ?_
    have hy1 : ((y : (ZMod (2 ^ (n + 2)))ˣ)) = 1 := by
      have := hx.symm.trans hx1; rwa [inv_eq_one] at this
    ext; rw [hy1]; rfl
  · exact absurd (hxm1 ▸ hxmem5) (neg_one_not_mem_zpowers_u5 n)

/-- **Stage 4.** The internal direct product isomorphism for `k = n + 2`:

  `(ZMod (2^(n+2)))ˣ ≃* ⟨-1⟩ × ⟨5⟩`.

Built from `prodHom` (multiplication of the two cyclic subgroups), which is
injective (Stage 3) and, since domain and codomain have equal cardinality
`2^(n+1)`, bijective. -/
noncomputable def unitsEquiv (n : ℕ) :
    (ZMod (2 ^ (n + 2)))ˣ ≃*
      (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) × (Subgroup.zpowers (u5 n)) := by
  have hcard : Nat.card
      ((Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) × (Subgroup.zpowers (u5 n)))
        = Nat.card (ZMod (2 ^ (n + 2)))ˣ := by
    rw [Nat.card_prod, card_zpowers_neg_one, card_zpowers_u5, card_units, pow_succ]
    ring
  have hbij : Function.Bijective (prodHom n) :=
    (Nat.bijective_iff_injective_and_card (prodHom n)).mpr ⟨prodHom_injective n, hcard⟩
  exact (MulEquiv.ofBijective (prodHom n) hbij).symm

/-! ## Stage 5 — the `k ≥ 3` Beal-local pair-count -/

open BealTwoDensity in
/-- **Stage 5 (HEADLINE).** The `p = 2`, `k ≥ 3` Beal-local pair-count.
For `k = n + 3` (`n ≥ 0`, i.e. `k ≥ 3`),

  `#{ (A,B) : ((ZMod (2^k))ˣ)² // A^x · B^y = 1 }
     = (2 · gcd(2, gcd x y)) · (2^(k-2) · gcd(2^(k-2), gcd x y))`. -/
theorem units_two_pow_count_ge_three (k : ℕ) (hk : 3 ≤ k) (x y : ℕ) :
    Nat.card {p : (ZMod (2 ^ k))ˣ × (ZMod (2 ^ k))ˣ // p.1 ^ x * p.2 ^ y = 1}
      = (2 * Nat.gcd 2 (Nat.gcd x y))
        * (2 ^ (k - 2) * Nat.gcd (2 ^ (k - 2)) (Nat.gcd x y)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  -- the explicit iso, with the two cyclic factors
  have hcount := count_of_mulEquiv_prod_cyclic (unitsEquiv n) x y
  rw [show n + 2 - 2 = n by omega]
  rw [hcount, card_zpowers_neg_one, card_zpowers_u5]

end BealTwoAdicIso
