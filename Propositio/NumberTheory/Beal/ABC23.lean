import Propositio.NumberTheory.Beal.Radical
import Propositio.NumberTheory.Beal.ABCFinite
import Propositio.NumberTheory.Beal.RadicalAPI
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# ABC ⟹ finitely many signature-`(2,3,n)` solutions (the hyperbolic range, Lean 4)

This file extends the **ABC-finiteness route** of `BealABCFinite` /
`BealABCFiniteFull` from the diagonal Beal family `Aˣ + Bʸ = Cᶻ` to the
**signature-`(2,3,n)` generalized-Fermat family**

  `a² + b³ = cⁿ`,    `gcd(a,b) = 1`,

the *most-studied* open generalized-Fermat signature (Poonen–Schaefer–Stoll for
`n = 5`; Bennett–Chen and the Frey–Hellegouarch / modular program for general
`n`).  It is the `(2,3,n)`-family analogue of `BealABCFinite`, and connects
directly to the Frey-curve files `BealFrey23` / `BealFrey23Radical`.

## The hyperbolic range

The Euler-characteristic of the signature `(2,3,n)` is
`χ = 1/2 + 1/3 + 1/n − 1`.  It is *negative* — the **hyperbolic / genus ≥ 2**
range, where Darmon–Granville finiteness and the ABC heuristic apply — exactly
when `1/2 + 1/3 + 1/n < 1`, i.e. `1/n < 1/6`, i.e. `n ≥ 7`.  We work throughout
in this range (our concrete threshold is `N = 16`, comfortably inside it).

## The argument (ABC applied to `(a², b³, cⁿ)`)

For a primitive solution `a² + b³ = cⁿ` with `a, b, c ≥ 2`:

* Both summands are positive, so `a² < cⁿ` and `b³ < cⁿ`.
* From `a² < cⁿ` we get `a < c^(n/2)`, from `b³ < cⁿ` we get `b < c^(n/3)`; with
  `c = c¹` this gives `a·b·c < c^(n/2 + n/3 + 1) = c^(5n/6 + 1)` (`abc23_lt_pow`).
* The radical of the `(2,3,n)` product is exponent-blind:
  `radical(a²·b³·cⁿ) = radical(a·b·c) ≤ a·b·c` (`radical_23_le`).
* ABC at `ε = 1/12` on the coprime triple `(a², b³, cⁿ)` gives
  `cⁿ ≤ K·radical(a²b³cⁿ)^(13/12) ≤ K·(abc)^(13/12) < K·c^((5n/6+1)·13/12)
       = K·c^(65n/72 + 13/12)`.
* Hence `c^(n − 65n/72 − 13/12) = c^(7n/72 − 13/12) < K`.  For `n ≥ 16` the
  exponent `7n/72 − 13/12 ≥ 1/4 > 0` and `c ≥ 2 > 1`, so `c^(1/4) < K`, whence
  `c ≤ K⁴` — an absolute bound (`abc_imp_23_base_bounded`).
* With the base `c` bounded, `a² ≤ cⁿ ≤ ⌊M⌋ⁿ` and `b³ ≤ cⁿ ≤ ⌊M⌋ⁿ` bound `a, b`
  too (crudely `a, b ≤ ⌊M⌋ⁿ`), so the solution set sits in a finite box and is
  finite for each large `n` (`abc_imp_23_finite`).

## Contents
* `radical_23_le`         — `radical(a²·b³·cⁿ) ≤ a·b·c` (exponent-blind radical).
* `abc23_lt_pow`          — `a·b·c < c^(n/2 + n/3 + 1)` (the rpow product bound).
* `abc_imp_23_base_bounded` — **HEADLINE**: ABC ⟹ the base `c` of a `(2,3,n)`
  solution with `n ≥ 16` is bounded by an absolute constant `M = K⁴`.
* `abc_imp_23_finite`     — **HEADLINE 2**: ABC ⟹ for each `n ≥ 16` the set of
  primitive `(2,3,n)` solutions `(a,b,c)` is finite.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17).  Use
`lake env lean BealABC23.lean` to typecheck.
-/

namespace BealABC23

open scoped Real

/-! ## 1. The radical of the `(2,3,n)` product is bounded by `a·b·c` -/

/-- **Radical bound.** For nonzero `a, b, c` and `n ≠ 0`, the radical of the
signature-`(2,3,n)` product collapses to the radical of `a·b·c` (the radical is
exponent-blind, `BealRadical.radical_beal_eq` with `x = 2, y = 3, z = n`), which is
in turn at most `a·b·c` (`BealRadical.radical_le_self`):

  `radical(a²·b³·cⁿ) ≤ a·b·c`. -/
theorem radical_23_le {a b c n : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hn : n ≠ 0) :
    BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) ≤ a * b * c := by
  have hrad_eq : BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n)
      = BealRadical.radical (a * b * c) :=
    BealRadical.radical_beal_eq ha hb hc (by norm_num) (by norm_num) hn
  have habc : 0 < a * b * c := by positivity
  rw [hrad_eq]
  exact BealRadical.radical_le_self habc

/-! ## 2. A base is bounded by a fractional power of `c` -/

/-- **Base bound.** If `1 ≤ k`, `1 ≤ a`, `2 ≤ c`, and `aᵏ < cⁿ`, then over `ℝ`
`a < c^(n/k)`.  (Apply `t ↦ t^(1/k)`, strictly monotone on nonneg reals, to
`aᵏ < cⁿ`.)  This is the generalized cube-root bound, kept parametric in the
exponent `k` so it applies to both `a²` (`k = 2`) and `b³` (`k = 3`). -/
theorem base_lt_rpow {a c k n : ℕ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 2 ≤ c) (hpow : a ^ k < c ^ n) :
    (a : ℝ) < (c : ℝ) ^ ((n : ℝ) / k) := by
  have haR0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hcR0 : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpow' : (a : ℝ) ^ (k : ℝ) < (c : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast hpow
  have hmono := Real.rpow_lt_rpow (z := (1 / k : ℝ)) (by positivity) hpow' (by positivity)
  rw [← Real.rpow_mul haR0, ← Real.rpow_mul hcR0] at hmono
  rw [show (k : ℝ) * (1 / k) = 1 by field_simp, Real.rpow_one] at hmono
  rw [show (n : ℝ) * (1 / k) = (n : ℝ) / k by ring] at hmono
  exact hmono

/-- **Product bound.** For a primitive `(2,3,n)` solution with `a, b ≥ 2`, `c ≥ 2`,
and `a² < cⁿ`, `b³ < cⁿ`, the product of bases satisfies

  `a·b·c < c^(n/2 + n/3 + 1)`

over `ℝ` (strict, from the strict base bounds `a < c^(n/2)`, `b < c^(n/3)`).
Mirrors `BealABCQuality.abc_lt_rpow` specialized to `(x,y) = (2,3)`. -/
theorem abc23_lt_pow {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hAx : a ^ 2 < c ^ n) (hBy : b ^ 3 < c ^ n) :
    (a * b * c : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hbR1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
  have hAlt : (a : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2) :=
    base_lt_rpow (by norm_num) (by omega) hc hAx
  have hBlt : (b : ℝ) < (c : ℝ) ^ ((n : ℝ) / 3) :=
    base_lt_rpow (by norm_num) (by omega) hc hBy
  -- a·b < c^(n/2) · c^(n/3)
  have hAB : (a : ℝ) * (b : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) := by
    calc (a : ℝ) * (b : ℝ)
        < (c : ℝ) ^ ((n : ℝ) / 2) * (b : ℝ) :=
          mul_lt_mul_of_pos_right hAlt (by linarith)
      _ ≤ (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left (le_of_lt hBlt)
            (le_of_lt (Real.rpow_pos_of_pos hcpos _))
  -- Now a·b·c < c^(n/2) · c^(n/3) · c = c^(n/2 + n/3 + 1).
  have hABC : (a : ℝ) * (b : ℝ) * (c : ℝ)
      < (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) * (c : ℝ) :=
    mul_lt_mul_of_pos_right hAB hcpos
  have hrhs : (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) * (c : ℝ)
      = (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) := by
    nth_rewrite 3 [← Real.rpow_one (c : ℝ)]
    rw [← Real.rpow_add hcpos, ← Real.rpow_add hcpos]
  calc (a * b * c : ℝ) = (a : ℝ) * (b : ℝ) * (c : ℝ) := by norm_cast
    _ < (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) * (c : ℝ) := hABC
    _ = (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) := hrhs

/-! ## 3. HEADLINE: ABC ⟹ the base `c` is bounded -/

/-- **HEADLINE (ABC ⟹ `(2,3,n)` base bounded).** Assume the ABC conjecture.  Then
there is an exponent threshold `N` and an absolute constant `M` such that **every**
primitive signature-`(2,3,n)` solution `a² + b³ = cⁿ` with `a, b, c ≥ 2`,
`gcd(a,b) = 1`, and `n ≥ N` has `c ≤ M`.  In particular only finitely many bases
`c` occur for large `n`.

Concretely `N = 16` (comfortably inside the hyperbolic range `n ≥ 7`) and
`M = K⁴`, where `K` is the ABC constant at `ε = 1/12`.

Proof, mirroring `BealABCFinite.beal_base_bounded`: apply
`BealRadical.beal_abc_bounded` at `ε = 1/12` to the triple `(a², b³, cⁿ)` (the
coprimality `gcd(a², b³) = 1` comes from `gcd(a,b) = 1`), obtaining
`cⁿ ≤ K·(abc)^(13/12)`.  Combine with the product bound `abc < c^(5n/6 + 1)`
(`abc23_lt_pow`); the RHS becomes `K·c^(65n/72 + 13/12)`.  Dividing by
`c^(65n/72 + 13/12)` leaves `c^(7n/72 − 13/12) < K`; for `n ≥ 16` the exponent is
`≥ 1/4 > 0`, so `c^(1/4) < K`, whence `c ≤ K⁴`. -/
theorem abc_imp_23_base_bounded (habc : BealRadical.ABCConjecture) :
    ∃ (N : ℕ) (M : ℝ), ∀ a b c n : ℕ,
      2 ≤ a → 2 ≤ b → 2 ≤ c → N ≤ n →
      Nat.Coprime a b → a ^ 2 + b ^ 3 = c ^ n → (c : ℝ) ≤ M := by
  -- ABC at ε = 1/12 gives the value bound for primitive (2,3,n) triples.
  obtain ⟨K, hK, hbound⟩ :=
    BealRadical.beal_abc_bounded habc (ε := (1/12 : ℝ)) (by norm_num)
  refine ⟨16, K ^ 4, ?_⟩
  intro a b c n ha hb hc hn hcop hsum
  -- Basic positivity / coprimality bookkeeping.
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hn16 : 16 ≤ n := hn
  -- Coprimality of the (2,3,n) summands from gcd(a,b) = 1.
  have hcoppow : Nat.Coprime (a ^ 2) (b ^ 3) := Nat.Coprime.pow 2 3 hcop
  -- Each summand is below the value.
  have hAx0 : 0 < a ^ 2 := by positivity
  have hBy0 : 0 < b ^ 3 := by positivity
  have hAx : a ^ 2 < c ^ n := by omega
  have hBy : b ^ 3 < c ^ n := by omega
  -- The value bound: cⁿ ≤ K·(abc)^(13/12).
  have hval := hbound a b c 2 3 n ha0 hb0 hc0 (by norm_num) (by norm_num) hn0 hcoppow hsum
  -- The product bound: abc < c^(5n/6 + 1).
  have hprod : (a * b * c : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) :=
    abc23_lt_pow ha hb hc hAx hBy
  -- Real-side bookkeeping for c.
  have hcR2 : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hABCpos : (0 : ℝ) < (a * b * c : ℝ) := by
    have : (0 : ℕ) < a * b * c := by positivity
    exact_mod_cast this
  -- (abc)^(13/12) < (c^(5n/6+1))^(13/12) = c^((5n/6+1)·13/12) = c^(65n/72 + 13/12).
  have hprod54 : (a * b * c : ℝ) ^ (1 + (1/12 : ℝ))
      < ((c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1)) ^ (1 + (1/12 : ℝ)) := by
    apply Real.rpow_lt_rpow (le_of_lt hABCpos) hprod
    norm_num
  have hrhs_simp : ((c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1)) ^ (1 + (1/12 : ℝ))
      = (c : ℝ) ^ (65 * (n : ℝ) / 72 + 13/12) := by
    rw [← Real.rpow_mul (le_of_lt hcpos)]
    congr 1
    ring
  -- Combine: cⁿ ≤ K·(abc)^(13/12) < K·c^(65n/72 + 13/12).
  have hCz_rpow : (c : ℝ) ^ (n : ℝ) = ((c ^ n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hval' : (c : ℝ) ^ (n : ℝ) ≤ K * (a * b * c : ℝ) ^ (1 + (1/12 : ℝ)) := by
    rw [hCz_rpow]; exact hval
  have hchain : (c : ℝ) ^ (n : ℝ) < K * (c : ℝ) ^ (65 * (n : ℝ) / 72 + 13/12) := by
    calc (c : ℝ) ^ (n : ℝ)
        ≤ K * (a * b * c : ℝ) ^ (1 + (1/12 : ℝ)) := hval'
      _ < K * ((c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1)) ^ (1 + (1/12 : ℝ)) := by
          exact mul_lt_mul_of_pos_left hprod54 hK
      _ = K * (c : ℝ) ^ (65 * (n : ℝ) / 72 + 13/12) := by rw [hrhs_simp]
  -- Divide by c^(65n/72 + 13/12): c^(7n/72 − 13/12) < K.
  have hpowpos : (0 : ℝ) < (c : ℝ) ^ (65 * (n : ℝ) / 72 + 13/12) :=
    Real.rpow_pos_of_pos hcpos _
  have hgap : (c : ℝ) ^ (7 * (n : ℝ) / 72 - 13/12) < K := by
    have hsplit : (c : ℝ) ^ (n : ℝ)
        = (c : ℝ) ^ (7 * (n : ℝ) / 72 - 13/12) * (c : ℝ) ^ (65 * (n : ℝ) / 72 + 13/12) := by
      rw [← Real.rpow_add hcpos]
      congr 1
      ring
    rw [hsplit] at hchain
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hpowpos)
  -- For n ≥ 16 the exponent 7n/72 − 13/12 ≥ 1/4 > 0, and c ≥ 2 > 1.
  have hexp_ge : (1 : ℝ) / 4 ≤ 7 * (n : ℝ) / 72 - 13/12 := by
    have : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn16
    linarith
  have hmono_exp : (c : ℝ) ^ ((1 : ℝ) / 4) ≤ (c : ℝ) ^ (7 * (n : ℝ) / 72 - 13/12) :=
    Real.rpow_le_rpow_of_exponent_le hcR1 hexp_ge
  have h14 : (c : ℝ) ^ ((1 : ℝ) / 4) < K := lt_of_le_of_lt hmono_exp hgap
  -- Raise to the 4th power: c ≤ K⁴.
  have h14pos : (0 : ℝ) ≤ (c : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hcpos) _
  have hraise : ((c : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) ≤ K ^ (4 : ℕ) :=
    pow_le_pow_left₀ h14pos (le_of_lt h14) 4
  have hcsimp : ((c : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = (c : ℝ) := by
    rw [← Real.rpow_natCast ((c : ℝ) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul (le_of_lt hcpos)]
    norm_num
  calc (c : ℝ) = ((c : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hcsimp.symm
    _ ≤ K ^ (4 : ℕ) := hraise

/-! ## 4. HEADLINE 2: ABC ⟹ finitely many `(2,3,n)` solutions per `n` -/

/-- **Component bounds.** In a primitive `(2,3,n)` solution `a² + b³ = cⁿ` with
`a, b ≥ 2` and a base bound `c ≤ D` over `ℕ`, both other components are bounded by
`Dⁿ`: `a ≤ Dⁿ` and `b ≤ Dⁿ`.

Proof (crude, all in `ℕ`): `a ≤ a² ≤ a² + b³ = cⁿ ≤ Dⁿ`, and symmetrically
`b ≤ b³ ≤ cⁿ ≤ Dⁿ`. -/
theorem base_bounds_components {a b c D n : ℕ}
    (_ha : 2 ≤ a) (_hb : 2 ≤ b)
    (hCD : c ≤ D) (hsum : a ^ 2 + b ^ 3 = c ^ n) :
    a ≤ D ^ n ∧ b ≤ D ^ n := by
  have hCz : c ^ n ≤ D ^ n := Nat.pow_le_pow_left hCD n
  have ha2 : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
  have ha2C : a ^ 2 ≤ c ^ n := by omega
  have hb3 : b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
  have hb3C : b ^ 3 ≤ c ^ n := by omega
  exact ⟨le_trans ha2 (le_trans ha2C hCz), le_trans hb3 (le_trans hb3C hCz)⟩

/-- **HEADLINE 2 (ABC ⟹ finitely many `(2,3,n)` solutions per `n`).** Assume the
ABC conjecture.  Then there is an exponent threshold `N` such that for **every**
`n ≥ N`, the set of primitive signature-`(2,3,n)` solutions `(a, b, c)` of
`a² + b³ = cⁿ` with `a, b, c ≥ 2` and `gcd(a,b) = 1` is **finite**.

This is the `(2,3,n)`-family analogue of `BealABCFiniteFull.beal_solutions_finite`,
and the honest finiteness statement behind "ABC ⟹ finitely many `(2,3,n)`
solutions" in the hyperbolic / genus ≥ 2 range `n ≥ 7` (our concrete threshold is
`N = 16`).  This is the most-studied open generalized-Fermat signature (PSS for
`n = 5`, Bennett–Chen / the modular method for general `n`); it connects to the
Frey-curve files `BealFrey23` / `BealFrey23Radical`.

Proof: `abc_imp_23_base_bounded` gives `N` and an absolute `M` with `c ≤ M`, so
`c ≤ ⌊M⌋₊`; then `base_bounds_components` bounds `a, b ≤ ⌊M⌋₊ⁿ`, embedding the
solution set into the finite box `Iic ⌊M⌋₊ⁿ × Iic ⌊M⌋₊ⁿ × Iic ⌊M⌋₊`. -/
theorem abc_imp_23_finite (habc : BealRadical.ABCConjecture) :
    ∃ N, ∀ n, N ≤ n →
      Set.Finite { p : ℕ × ℕ × ℕ |
        2 ≤ p.1 ∧ 2 ≤ p.2.1 ∧ 2 ≤ p.2.2 ∧ Nat.Coprime p.1 p.2.1 ∧
        p.1 ^ 2 + p.2.1 ^ 3 = p.2.2 ^ n } := by
  obtain ⟨N, M, hM⟩ := abc_imp_23_base_bounded habc
  refine ⟨N, ?_⟩
  intro n hn
  set D : ℕ := Nat.floor M with hD
  -- Embed the solution set into the finite box  Iic (Dⁿ) × Iic (Dⁿ) × Iic D.
  apply Set.Finite.subset
    ((Set.finite_Iic (D ^ n)).prod
      ((Set.finite_Iic (D ^ n)).prod (Set.finite_Iic D)))
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hcop, hsum⟩
  -- Base bound: c ≤ M over ℝ, hence c ≤ ⌊M⌋₊.
  have hCM : (c : ℝ) ≤ M := hM a b c n ha hb hc hn hcop hsum
  have hCD : c ≤ D := Nat.le_floor hCM
  -- Component bounds: a, b ≤ Dⁿ.
  obtain ⟨hAD, hBD⟩ := base_bounds_components ha hb hCD hsum
  exact ⟨hAD, hBD, hCD⟩

end BealABC23
