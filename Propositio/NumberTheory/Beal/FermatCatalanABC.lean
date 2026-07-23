import Propositio.NumberTheory.Beal.Radical
import Propositio.NumberTheory.Beal.RadicalAPI
import Propositio.NumberTheory.Beal.ABCFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# ABC ⟹ Fermat–Catalan finiteness, for every hyperbolic signature (Lean 4)

This file proves the **general Granville "ABC ⟹ Fermat–Catalan finiteness"
theorem**, unifying every ABC-finiteness result in the project — Beal
(`BealABCFinite`), signature `(2,3,n)` (`BealABC23`), and Fermat (`BealABCFermat`)
— into a single statement valid for **any** hyperbolic signature.

## Fermat–Catalan

A *Fermat–Catalan* equation is
  `aᵖ + bq = cʳ`,    `gcd(a, b) = 1`,
with fixed exponents `(p, q, r)`.  Its signature is **hyperbolic** (genus ≥ 2,
where Darmon–Granville finiteness and the ABC heuristic apply) exactly when
  `1/p + 1/q + 1/r < 1`,
equivalently — clearing denominators over `ℕ` —
  `q·r + p·r + p·q < p·q·r`.
We work throughout with this `ℕ` inequality form (`hyp`).

## The argument (ABC applied to `(aᵖ, bq, cʳ)`)

For a primitive solution `aᵖ + bq = cʳ` with `a, b, c ≥ 2`:

* Both summands are positive, so `aᵖ < cʳ` and `bq < cʳ`.
* From `aᵖ < cʳ` we get `a < c^(r/p)`, from `bq < cʳ` we get `b < c^(r/q)`; with
  `c = c¹` this gives `a·b·c < c^(r/p + r/q + 1)` (`abc_fc_lt_pow`).
* The radical of the `(p,q,r)` product is exponent-blind:
  `radical(aᵖ·bq·cʳ) = radical(a·b·c) ≤ a·b·c` (`radical_fc_le`).
* Write `S := r/p + r/q + 1` and `δ₀ := r − S`.  The hyperbolic condition gives
  `S < r`, i.e. `δ₀ > 0` (`hyperbolic_gap`).  ABC at a signature-dependent
  `ε = δ₀ / (2S)` gives
  `cʳ ≤ K·radical(aᵖbqcʳ)^(1+ε) ≤ K·(abc)^(1+ε) < K·c^(S·(1+ε))`,
  and `S·(1+ε) = S + δ₀/2 = r − δ₀/2`, so `c^(δ₀/2) < K`, whence `c ≤ K^(2/δ₀)` —
  an absolute bound for the fixed signature (`abc_imp_fermat_catalan_base_bounded`).
* With the base `c` bounded, `aᵖ ≤ cʳ ≤ ⌊M⌋ʳ` and `bq ≤ cʳ ≤ ⌊M⌋ʳ` bound `a, b`
  too, so the solution set sits in a finite box and is finite
  (`abc_imp_fermat_catalan_finite`).

The ε is *chosen from the signature* `(p,q,r)`; since `(p,q,r)` are fixed
parameters this is harmless, but it is the crux of the general proof (the
per-family files could hard-code `ε = 1/4` or `ε = 1/12`).

## Contents
* `hyperbolic_gap`            — `q·r+p·r+p·q < p·q·r` ⟹ `(r:ℝ)/p + r/q + 1 < r`.
* `radical_fc_le`            — `radical(aᵖ·bq·cʳ) ≤ a·b·c` (exponent-blind radical).
* `base_lt_rpow`             — `a < c^(r/p)` from `aᵖ < cʳ` (parametric base bound).
* `abc_fc_lt_pow`            — `a·b·c < c^(r/p + r/q + 1)` (the rpow product bound).
* `abc_imp_fermat_catalan_base_bounded` — **HEADLINE**: ABC ⟹ for each fixed
  hyperbolic `(p,q,r)`, the base `c` is bounded by an absolute constant `M`.
* `abc_imp_fermat_catalan_finite`        — **HEADLINE 2**: ABC ⟹ for each fixed
  hyperbolic `(p,q,r)`, the Fermat–Catalan solution set is finite.
* `beal_diagonal_finite`, `sig_23n_finite`, `fermat_finite` — the three existing
  families recovered as one-line specializations.

The ten known Fermat–Catalan solutions (`1+2³=3²`, `2⁵+7²=3⁴`, …, `33⁸+1549034²=15613³`,
`43⁸+96222³=30042907²`, `9262³+15312283²=113⁷`) all have **min exponent ≤ 3**; the
Fermat–Catalan conjecture (only finitely many in total) is open, but for each
*fixed* hyperbolic signature finiteness is exactly the ABC consequence proved here.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17).  Use
`lake env lean BealFermatCatalanABC.lean` to typecheck.
-/

namespace BealFermatCatalanABC

open scoped Real

/-! ## 1. The hyperbolic gap: `1/p + 1/q + 1/r < 1` ⟹ `r/p + r/q + 1 < r` -/

/-- **Hyperbolic gap.** The genus condition `1/p + 1/q + 1/r < 1`, written over `ℕ`
as `q·r + p·r + p·q < p·q·r`, yields the strict real exponent bound

  `(r:ℝ)/p + (r:ℝ)/q + 1 < (r:ℝ)`.

(Multiply the `ℕ` inequality by `1/(p·q)` over `ℝ`.)  This is the positive
exponent gap `δ₀ := r − (r/p + r/q + 1) > 0` driving the whole argument. -/
theorem hyperbolic_gap {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (h : q * r + p * r + p * q < p * q * r) :
    (r : ℝ) / p + (r : ℝ) / q + 1 < (r : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  -- Cast the ℕ inequality into ℝ.
  have hR : (q : ℝ) * r + (p : ℝ) * r + (p : ℝ) * q < (p : ℝ) * q * r := by
    exact_mod_cast h
  -- Divide through by p·q > 0.
  rw [div_add_div _ _ (ne_of_gt hpR) (ne_of_gt hqR), div_add' _ _ _ (by positivity),
      div_lt_iff₀ (by positivity)]
  ring_nf
  nlinarith [hR, mul_pos hpR hqR]

/-! ## 2. The radical of the `(p,q,r)` product is bounded by `a·b·c` -/

/-- **Radical bound.** For nonzero `a, b, c` and `p, q, r ≠ 0`, the radical of the
signature-`(p,q,r)` product collapses to `radical(a·b·c)` (exponent-blind, via
`BealRadical.radical_beal_eq` with `x,y,z := p,q,r`), which is in turn at most
`a·b·c` (`BealRadical.radical_le_self`):

  `radical(aᵖ·bq·cʳ) ≤ a·b·c`. -/
theorem radical_fc_le {a b c p q r : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    BealRadical.radical (a ^ p * b ^ q * c ^ r) ≤ a * b * c := by
  have hrad_eq : BealRadical.radical (a ^ p * b ^ q * c ^ r)
      = BealRadical.radical (a * b * c) :=
    BealRadical.radical_beal_eq ha hb hc hp hq hr
  have habc : 0 < a * b * c := by positivity
  rw [hrad_eq]
  exact BealRadical.radical_le_self habc

/-! ## 3. A base is bounded by a fractional power of `c` -/

/-- **Base bound.** If `1 ≤ k`, `1 ≤ a`, `2 ≤ c`, and `aᵏ < cʳ`, then over `ℝ`
`a < c^(r/k)`.  (Apply `t ↦ t^(1/k)`, strictly monotone on nonneg reals, to
`aᵏ < cʳ`.)  Kept parametric in the exponent `k` so it applies to both `aᵖ`
(`k = p`) and `bq` (`k = q`).  This is the `BealABC23.base_lt_rpow` idiom with the
value exponent generalized from a fixed `n` to `r`. -/
theorem base_lt_rpow {a c k r : ℕ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 2 ≤ c) (hpow : a ^ k < c ^ r) :
    (a : ℝ) < (c : ℝ) ^ ((r : ℝ) / k) := by
  have haR0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hcR0 : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpow' : (a : ℝ) ^ (k : ℝ) < (c : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast hpow
  have hmono := Real.rpow_lt_rpow (z := (1 / k : ℝ)) (by positivity) hpow' (by positivity)
  rw [← Real.rpow_mul haR0, ← Real.rpow_mul hcR0] at hmono
  rw [show (k : ℝ) * (1 / k) = 1 by field_simp, Real.rpow_one] at hmono
  rw [show (r : ℝ) * (1 / k) = (r : ℝ) / k by ring] at hmono
  exact hmono

/-- **Product bound.** For a primitive `(p,q,r)` solution with `a, b, c ≥ 2`,
`p, q ≥ 1`, and `aᵖ < cʳ`, `bq < cʳ`, the product of bases satisfies

  `a·b·c < c^(r/p + r/q + 1)`

over `ℝ` (strict, from the strict base bounds `a < c^(r/p)`, `b < c^(r/q)`).
Mirrors `BealABC23.abc23_lt_pow` with general value exponent `r`. -/
theorem abc_fc_lt_pow {a b c p q r : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hAx : a ^ p < c ^ r) (hBy : b ^ q < c ^ r) :
    (a * b * c : ℝ) < (c : ℝ) ^ ((r : ℝ) / p + (r : ℝ) / q + 1) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hbR1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
  have hAlt : (a : ℝ) < (c : ℝ) ^ ((r : ℝ) / p) :=
    base_lt_rpow hp (by omega) hc hAx
  have hBlt : (b : ℝ) < (c : ℝ) ^ ((r : ℝ) / q) :=
    base_lt_rpow hq (by omega) hc hBy
  -- a·b < c^(r/p) · c^(r/q)
  have hAB : (a : ℝ) * (b : ℝ) < (c : ℝ) ^ ((r : ℝ) / p) * (c : ℝ) ^ ((r : ℝ) / q) := by
    calc (a : ℝ) * (b : ℝ)
        < (c : ℝ) ^ ((r : ℝ) / p) * (b : ℝ) :=
          mul_lt_mul_of_pos_right hAlt (by linarith)
      _ ≤ (c : ℝ) ^ ((r : ℝ) / p) * (c : ℝ) ^ ((r : ℝ) / q) :=
          mul_le_mul_of_nonneg_left (le_of_lt hBlt)
            (le_of_lt (Real.rpow_pos_of_pos hcpos _))
  -- Now a·b·c < c^(r/p) · c^(r/q) · c = c^(r/p + r/q + 1).
  have hABC : (a : ℝ) * (b : ℝ) * (c : ℝ)
      < (c : ℝ) ^ ((r : ℝ) / p) * (c : ℝ) ^ ((r : ℝ) / q) * (c : ℝ) :=
    mul_lt_mul_of_pos_right hAB hcpos
  have hrhs : (c : ℝ) ^ ((r : ℝ) / p) * (c : ℝ) ^ ((r : ℝ) / q) * (c : ℝ)
      = (c : ℝ) ^ ((r : ℝ) / p + (r : ℝ) / q + 1) := by
    nth_rewrite 3 [← Real.rpow_one (c : ℝ)]
    rw [← Real.rpow_add hcpos, ← Real.rpow_add hcpos]
  calc (a * b * c : ℝ) = (a : ℝ) * (b : ℝ) * (c : ℝ) := by norm_cast
    _ < (c : ℝ) ^ ((r : ℝ) / p) * (c : ℝ) ^ ((r : ℝ) / q) * (c : ℝ) := hABC
    _ = (c : ℝ) ^ ((r : ℝ) / p + (r : ℝ) / q + 1) := hrhs

/-! ## 4. HEADLINE: ABC ⟹ the base `c` is bounded for each hyperbolic signature -/

/-- **HEADLINE (ABC ⟹ Fermat–Catalan base bounded).** Assume the ABC conjecture.
Then for **each fixed hyperbolic signature** `(p, q, r)` (i.e. `p, q, r ≥ 1` with
`q·r + p·r + p·q < p·q·r`, the cleared form of `1/p+1/q+1/r < 1`) there is an
absolute constant `M` such that **every** primitive Fermat–Catalan solution
`aᵖ + bq = cʳ` with `a, b, c ≥ 2` and `gcd(a,b) = 1` has `c ≤ M`.  In particular
only finitely many bases `c` occur for that signature.

The constant `M = K^(2/δ₀)` where `δ₀ := r − (r/p + r/q + 1) > 0` is the hyperbolic
gap (`hyperbolic_gap`) and `K` is the ABC constant at the signature-dependent
`ε = δ₀ / (2S)`, `S := r/p + r/q + 1`.  This choice makes `S·(1+ε) = r − δ₀/2`, so
after combining the ABC value bound with the product bound `abc < c^S` and dividing
by `c^(S·(1+ε))`, one is left with `c^(δ₀/2) < K`, whence `c ≤ K^(2/δ₀)`.  The ε
depending on `(p,q,r)` is harmless — they are fixed parameters of the statement. -/
theorem abc_imp_fermat_catalan_base_bounded (habc : BealRadical.ABCConjecture)
    {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hyp : q * r + p * r + p * q < p * q * r) :
    ∃ M : ℝ, ∀ a b c : ℕ, 2 ≤ a → 2 ≤ b → 2 ≤ c →
      Nat.Coprime a b → a ^ p + b ^ q = c ^ r → (c : ℝ) ≤ M := by
  -- The hyperbolic gap.  S := r/p + r/q + 1, δ₀ := r − S > 0.
  set S : ℝ := (r : ℝ) / p + (r : ℝ) / q + 1 with hS
  have hSlt : S < (r : ℝ) := hyperbolic_gap hp hq hr hyp
  have hSpos : 0 < S := by
    have : (0 : ℝ) ≤ (r : ℝ) / p + (r : ℝ) / q := by positivity
    simp only [hS]; linarith
  set δ₀ : ℝ := (r : ℝ) - S with hδ
  have hδpos : 0 < δ₀ := by simp only [hδ]; linarith
  -- ε := δ₀ / (2S) > 0.  Then S·(1+ε) = S + δ₀/2 = r − δ₀/2.
  set ε : ℝ := δ₀ / (2 * S) with hε
  have hεpos : 0 < ε := by simp only [hε]; positivity
  have hSeps : S * (1 + ε) = (r : ℝ) - δ₀ / 2 := by
    simp only [hε]
    field_simp
    ring_nf
    nlinarith [hSpos, hδ]
  -- ABC at ε gives the value bound for primitive (p,q,r) triples.
  obtain ⟨K, hK, hbound⟩ := BealRadical.beal_abc_bounded habc (ε := ε) hεpos
  refine ⟨K ^ (2 / δ₀), ?_⟩
  intro a b c ha hb hc hcop hsum
  -- Basic positivity / coprimality bookkeeping.
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  have hcoppow : Nat.Coprime (a ^ p) (b ^ q) := Nat.Coprime.pow p q hcop
  -- Each summand is below the value.
  have hAx0 : 0 < a ^ p := by positivity
  have hBy0 : 0 < b ^ q := by positivity
  have hAx : a ^ p < c ^ r := by omega
  have hBy : b ^ q < c ^ r := by omega
  -- The value bound: cʳ ≤ K·(abc)^(1+ε).
  have hval := hbound a b c p q r ha0 hb0 hc0 hp0 hq0 hr0 hcoppow hsum
  -- The product bound: abc < c^S.
  have hprod : (a * b * c : ℝ) < (c : ℝ) ^ S := abc_fc_lt_pow ha hb hc hp hq hAx hBy
  -- Real-side bookkeeping for c.
  have hcR2 : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hABCpos : (0 : ℝ) < (a * b * c : ℝ) := by
    have : (0 : ℕ) < a * b * c := by positivity
    exact_mod_cast this
  -- (abc)^(1+ε) < (c^S)^(1+ε) = c^(S·(1+ε)) = c^(r − δ₀/2).
  have hprod54 : (a * b * c : ℝ) ^ (1 + ε)
      < ((c : ℝ) ^ S) ^ (1 + ε) := by
    apply Real.rpow_lt_rpow (le_of_lt hABCpos) hprod
    linarith
  have hrhs_simp : ((c : ℝ) ^ S) ^ (1 + ε) = (c : ℝ) ^ ((r : ℝ) - δ₀ / 2) := by
    rw [← Real.rpow_mul (le_of_lt hcpos), hSeps]
  -- Combine: cʳ ≤ K·(abc)^(1+ε) < K·c^(r − δ₀/2).
  have hCz_rpow : (c : ℝ) ^ (r : ℝ) = ((c ^ r : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hval' : (c : ℝ) ^ (r : ℝ) ≤ K * (a * b * c : ℝ) ^ (1 + ε) := by
    rw [hCz_rpow]; exact hval
  have hchain : (c : ℝ) ^ (r : ℝ) < K * (c : ℝ) ^ ((r : ℝ) - δ₀ / 2) := by
    calc (c : ℝ) ^ (r : ℝ)
        ≤ K * (a * b * c : ℝ) ^ (1 + ε) := hval'
      _ < K * ((c : ℝ) ^ S) ^ (1 + ε) := mul_lt_mul_of_pos_left hprod54 hK
      _ = K * (c : ℝ) ^ ((r : ℝ) - δ₀ / 2) := by rw [hrhs_simp]
  -- Divide by c^(r − δ₀/2): c^(δ₀/2) < K.
  have hpowpos : (0 : ℝ) < (c : ℝ) ^ ((r : ℝ) - δ₀ / 2) :=
    Real.rpow_pos_of_pos hcpos _
  have hgap : (c : ℝ) ^ (δ₀ / 2) < K := by
    have hsplit : (c : ℝ) ^ (r : ℝ)
        = (c : ℝ) ^ (δ₀ / 2) * (c : ℝ) ^ ((r : ℝ) - δ₀ / 2) := by
      rw [← Real.rpow_add hcpos]
      congr 1
      ring
    rw [hsplit] at hchain
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hpowpos)
  -- Raise to the (2/δ₀) power: c ≤ K^(2/δ₀).
  have hgappos' : (0 : ℝ) ≤ (c : ℝ) ^ (δ₀ / 2) := Real.rpow_nonneg (le_of_lt hcpos) _
  have hraise : ((c : ℝ) ^ (δ₀ / 2)) ^ (2 / δ₀) ≤ K ^ (2 / δ₀) :=
    Real.rpow_le_rpow hgappos' (le_of_lt hgap) (by positivity)
  have hcsimp : ((c : ℝ) ^ (δ₀ / 2)) ^ (2 / δ₀) = (c : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hcpos)]
    rw [show (δ₀ / 2) * (2 / δ₀) = 1 by field_simp]
    exact Real.rpow_one _
  calc (c : ℝ) = ((c : ℝ) ^ (δ₀ / 2)) ^ (2 / δ₀) := hcsimp.symm
    _ ≤ K ^ (2 / δ₀) := hraise

/-! ## 5. HEADLINE 2: ABC ⟹ finitely many solutions per hyperbolic signature -/

/-- **Component bounds.** In a primitive `(p,q,r)` solution `aᵖ + bq = cʳ` with
`a, b ≥ 2`, `p, q ≥ 1`, and a base bound `c ≤ D` over `ℕ`, both other components are
bounded by `Dʳ`: `a ≤ Dʳ` and `b ≤ Dʳ`.

Proof (crude, all in `ℕ`): `a ≤ aᵖ ≤ aᵖ + bq = cʳ ≤ Dʳ`, symmetrically for `b`. -/
theorem base_bounds_components {a b c D p q r : ℕ}
    (_ha : 2 ≤ a) (_hb : 2 ≤ b) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hCD : c ≤ D) (hsum : a ^ p + b ^ q = c ^ r) :
    a ≤ D ^ r ∧ b ≤ D ^ r := by
  have hCz : c ^ r ≤ D ^ r := Nat.pow_le_pow_left hCD r
  have ha2 : a ≤ a ^ p := Nat.le_self_pow (by omega) a
  have ha2C : a ^ p ≤ c ^ r := by omega
  have hb3 : b ≤ b ^ q := Nat.le_self_pow (by omega) b
  have hb3C : b ^ q ≤ c ^ r := by omega
  exact ⟨le_trans ha2 (le_trans ha2C hCz), le_trans hb3 (le_trans hb3C hCz)⟩

/-- **HEADLINE 2 (ABC ⟹ Fermat–Catalan finiteness per signature).** Assume the ABC
conjecture.  Then for **each fixed hyperbolic signature** `(p, q, r)` (i.e.
`p, q, r ≥ 1` with `q·r + p·r + p·q < p·q·r`, the cleared form of `1/p+1/q+1/r<1`)
the set of primitive Fermat–Catalan solutions `(a, b, c)` of `aᵖ + bq = cʳ` with
`a, b, c ≥ 2` and `gcd(a,b) = 1` is **finite**.

This is the general Granville "ABC ⟹ Fermat–Catalan finiteness" theorem; it
unifies `BealABCFinite` (Beal), `BealABC23` (`(2,3,n)`), and `BealABCFermat`
(Fermat), each recovered below by specializing `(p,q,r)`.

Proof: `abc_imp_fermat_catalan_base_bounded` gives an absolute `M` with `c ≤ M`, so
`c ≤ ⌊M⌋₊`; then `base_bounds_components` bounds `a, b ≤ ⌊M⌋₊ʳ`, embedding the
solution set into the finite box `Iic ⌊M⌋₊ʳ × Iic ⌊M⌋₊ʳ × Iic ⌊M⌋₊`. -/
theorem abc_imp_fermat_catalan_finite (habc : BealRadical.ABCConjecture)
    {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hyp : q * r + p * r + p * q < p * q * r) :
    Set.Finite { t : ℕ × ℕ × ℕ |
      2 ≤ t.1 ∧ 2 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 ^ p + t.2.1 ^ q = t.2.2 ^ r } := by
  obtain ⟨M, hM⟩ := abc_imp_fermat_catalan_base_bounded habc hp hq hr hyp
  set D : ℕ := Nat.floor M with hD
  -- Embed the solution set into the finite box  Iic (Dʳ) × Iic (Dʳ) × Iic D.
  apply Set.Finite.subset
    ((Set.finite_Iic (D ^ r)).prod
      ((Set.finite_Iic (D ^ r)).prod (Set.finite_Iic D)))
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hcop, hsum⟩
  -- Base bound: c ≤ M over ℝ, hence c ≤ ⌊M⌋₊.
  have hCM : (c : ℝ) ≤ M := hM a b c ha hb hc hcop hsum
  have hCD : c ≤ D := Nat.le_floor hCM
  -- Component bounds: a, b ≤ Dʳ.
  obtain ⟨hAD, hBD⟩ := base_bounds_components ha hb hp hq hCD hsum
  exact ⟨hAD, hBD, hCD⟩

/-! ## 6. Corollaries: the existing families as one-line specializations

The general theorem `abc_imp_fermat_catalan_finite` subsumes all three previously
proved ABC-finiteness results.  In each case the hyperbolic inequality
`q·r + p·r + p·q < p·q·r` is discharged automatically (`nlinarith`/`omega`) from the
range hypotheses on the exponents. -/

/-- **Beal (diagonal-ish) corollary.** For exponents `p, q, r ≥ 3` (so
`1/p+1/q+1/r ≤ 1/3+1/3+1/3 = 1`, strictly hyperbolic once any exceeds `3`; the
balanced `(3,3,3)` is already on the boundary, but `(3,3,r)` with `r ≥ 4` and all
`(p,q,r) ≥ 3` not all equal to 3 are hyperbolic — we take `min ≥ 3` with at least
one `≥ 4`).  Concretely we use `p, q ≥ 3` and `r ≥ 4`, the Beal regime: the
solution set of `aᵖ + bq = cʳ` is finite.  This recovers `BealABCFinite`'s
finiteness via the general theorem. -/
theorem beal_diagonal_finite (habc : BealRadical.ABCConjecture)
    {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    Set.Finite { t : ℕ × ℕ × ℕ |
      2 ≤ t.1 ∧ 2 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 ^ p + t.2.1 ^ q = t.2.2 ^ r } :=
  abc_imp_fermat_catalan_finite habc (by omega) (by omega) (by omega)
    (by nlinarith [Nat.mul_le_mul hp hq, Nat.mul_le_mul hq hr, Nat.mul_le_mul hp hr,
      Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr])

/-- **Signature `(2,3,n)` corollary.** For `n ≥ 7` the signature `(2,3,n)` is
hyperbolic (`1/2 + 1/3 + 1/n < 1 ⟺ n ≥ 7`); the general theorem gives finiteness of
`a² + b³ = cⁿ` solutions, recovering `BealABC23`. -/
theorem sig_23n_finite (habc : BealRadical.ABCConjecture)
    {n : ℕ} (hn : 7 ≤ n) :
    Set.Finite { t : ℕ × ℕ × ℕ |
      2 ≤ t.1 ∧ 2 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 ^ 2 + t.2.1 ^ 3 = t.2.2 ^ n } :=
  abc_imp_fermat_catalan_finite habc (by omega) (by omega) (by omega) (by nlinarith)


/-- **Fermat corollary.** For `n ≥ 4` the diagonal signature `(n,n,n)` is hyperbolic
(`3/n < 1 ⟺ n ≥ 4`); the general theorem gives finiteness of `aⁿ + bⁿ = cⁿ`
solutions for each such `n`, recovering `BealABCFermat` (asymptotic FLT). -/
theorem fermat_finite (habc : BealRadical.ABCConjecture)
    {n : ℕ} (hn : 4 ≤ n) :
    Set.Finite { t : ℕ × ℕ × ℕ |
      2 ≤ t.1 ∧ 2 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 ^ n + t.2.1 ^ n = t.2.2 ^ n } :=
  abc_imp_fermat_catalan_finite habc (by omega) (by omega) (by omega)
    (by nlinarith [Nat.mul_le_mul hn (le_refl n)])

/-! ## 7. Remark: the general Granville "ABC ⟹ Fermat–Catalan finiteness"

`abc_imp_fermat_catalan_base_bounded` and `abc_imp_fermat_catalan_finite` are the
general conditional theorem: **for any hyperbolic signature** `(p,q,r)` (i.e.
`1/p + 1/q + 1/r < 1`), the ABC conjecture implies that the coprime Fermat–Catalan
equation `aᵖ + bq = cʳ` has only finitely many primitive solutions with bases
`≥ 2`.

This single statement unifies and subsumes the project's three earlier ABC routes:
`BealABCFinite` (the Beal family, recovered as `beal_diagonal_finite`), `BealABC23`
(signature `(2,3,n)`, recovered as `sig_23n_finite`), and `BealABCFermat`
(Fermat / asymptotic FLT, recovered as `fermat_finite`) — each is one application
of the general theorem with the hyperbolic inequality discharged by `nlinarith`.

The Fermat–Catalan *conjecture* (finitely many solutions in **total**, across all
hyperbolic signatures) is open; the ten known solutions
`1+2³=3²`, `2⁵+7²=3⁴`, `7³+13²=2⁹`, `2⁷+17³=71²`, `3⁵+11⁴=122²`, `33⁸+1549034²=15613³`,
`1414³+2213459²=65⁷`, `9262³+15312283²=113⁷`, `17⁷+76271³=21063928²`,
`43⁸+96222³=30042907²` all have **min exponent ≤ 3**, consistent with the heuristic
that the "abundance" of solutions concentrates near the parabolic boundary.  What is
proved here is the per-signature finiteness, which is exactly the ABC consequence. -/

end BealFermatCatalanABC
