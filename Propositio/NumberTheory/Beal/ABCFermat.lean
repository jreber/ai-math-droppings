import Propositio.NumberTheory.Beal.Radical
import Propositio.NumberTheory.Beal.ABCFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# ABC ⟹ Fermat's Last Theorem for all large exponents (Lean 4)

This file proves the **conditional asymptotic FLT** of Granville–Tucker: *assuming
the ABC conjecture, a Fermat counterexample `Aⁿ + Bⁿ = Cⁿ` (coprime, bases `≥ 2`)
with sufficiently large exponent `n` has its base `C` bounded by an absolute
constant — and for each large `n` there are only finitely many counterexamples.*

It is the **diagonal `n = x = y = z` specialization** of the Beal results in
`BealABCFinite.lean`, and is genuinely *simpler*: with a single common exponent,
`Aⁿ < Cⁿ` gives `A < C` **directly** (no cube-root / fractional-power gymnastics),
so `A·B·C < C³` outright (`abc_lt_C_cubed`).  ABC at `ε = 1/4` then forces
`Cⁿ ≤ K·rad(ABC)^(5/4) ≤ K·(ABC)^(5/4) < K·(C³)^(5/4) = K·C^(15/4)`, i.e.
`C^(n − 15/4) < K`.  For `n ≥ 7` the gap `n − 15/4 ≥ 13/4 > 0`, and `C ≥ 2 > 1`,
so `C^(13/4) < K`, whence `C` is bounded by an absolute constant.

This validates that the project's `BealRadical.ABCConjecture` `Prop` is strong
enough to recover **Fermat's Last Theorem for all large exponents** — the classical
"ABC ⟹ asymptotic FLT" corollary.  (Mathlib proves FLT only for `n = 3, 4`
unconditionally; the full theorem is Wiles', not ABC-derived, but ABC yields the
asymptotic form cheaply, as formalized here.)

## The argument

For a counterexample `Aⁿ + Bⁿ = Cⁿ` with `A, B, C ≥ 2` and `n ≥ 7`:

* Both summands are positive, so `Aⁿ < Cⁿ` and `Bⁿ < Cⁿ`, giving `A < C`, `B < C`
  (`fermat_base_lt`); hence `A·B·C < C·C·C = C³` (`abc_lt_C_cubed`).
* ABC at `ε = 1/4` gives `Cⁿ ≤ K·rad(Aⁿ Bⁿ Cⁿ)^(5/4) = K·rad(ABC)^(5/4) ≤
  K·(ABC)^(5/4) < K·(C³)^(5/4) = K·C^(15/4)`.
* Hence `C^(n − 15/4) < K`.  For `n ≥ 7`, `n − 15/4 ≥ 13/4 > 0` and `C ≥ 2 > 1`,
  so `C^(13/4) < K`, whence `C ≤ K^(4/13)` — an absolute bound
  (`abc_imp_fermat_base_bounded`).
* `C` bounded and `A, B < C` ⟹ finitely many counterexamples for each large `n`
  (`abc_imp_fermat_finite`).

## Contents
* `fermat_base_lt` — `A < C` from `Aⁿ < Cⁿ`.
* `abc_lt_C_cubed` — `A·B·C < C³`.
* `abc_imp_fermat_base_bounded` — **HEADLINE**: ABC ⟹ counterexample bases are
  bounded for `n ≥ 7`.
* `abc_imp_fermat_finite` — **HEADLINE 2**: ABC ⟹ for each large `n`, the
  Fermat-`n` counterexample set is finite.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealABCFermat.lean` to typecheck.
-/

namespace BealABCFermat

open scoped Real

/-! ## 1. Strict monotonicity of the base: `Aⁿ < Cⁿ ⟹ A < C`

The whole simplification over the off-diagonal Beal case lives here.  Because the
three exponents coincide, `Aⁿ < Cⁿ` and `Bⁿ < Cⁿ` give `A < C` and `B < C`
**directly** — no fractional power of `C` is needed. -/

/-- **Base strict-monotonicity.** If `1 ≤ n`, `1 ≤ C`, and `Aⁿ < Cⁿ`, then `A < C`.
(Strict monotonicity of `t ↦ tⁿ` on `ℕ`; `lt_of_pow_lt_pow_left'` cancels the
exponent.) -/
theorem fermat_base_lt {A C n : ℕ} (hn : 1 ≤ n) (h : A ^ n < C ^ n) (hC : 1 ≤ C) :
    A < C := by
  have _hn := hn; have _hC := hC
  exact lt_of_pow_lt_pow_left' n h

/-! ## 2. The product of bases is below `C³` -/

/-- **Cube bound.** For a Fermat counterexample `Aⁿ + Bⁿ = Cⁿ` with `A, B, C ≥ 2`
and `n ≥ 1`, the product of bases satisfies `A·B·C < C³`.  Directly from
`fermat_base_lt`: `A < C` and `B < C`, so `A·B·C < C·C·C = C³`. -/
theorem abc_lt_C_cubed {A B C n : ℕ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C) (hn : 1 ≤ n)
    (h : A ^ n + B ^ n = C ^ n) : A * B * C < C ^ 3 := by
  have hBn : 0 < B ^ n := pow_pos (by omega) n
  have hAn : 0 < A ^ n := pow_pos (by omega) n
  have hAlt : A ^ n < C ^ n := by omega
  have hBlt : B ^ n < C ^ n := by omega
  have hAC : A < C := fermat_base_lt hn hAlt (by omega)
  have hBC : B < C := fermat_base_lt hn hBlt (by omega)
  -- A·B·C < C·C·C = C³ over ℕ.
  have : A * B * C < C * C * C := by
    have h1 : A * B < C * C := Nat.mul_lt_mul_of_lt_of_lt hAC hBC
    exact Nat.mul_lt_mul_of_lt_of_le h1 (le_refl C) (by omega)
  simpa [pow_succ, pow_zero, one_mul, mul_assoc] using this

/-! ## 3. HEADLINE: ABC ⟹ Fermat counterexample bases are bounded -/

/-- **HEADLINE (conditional asymptotic FLT, bounded-base form).** Assume the ABC
conjecture.  Then there is an exponent threshold `N` and an absolute constant `M`
such that **every** Fermat counterexample `Aⁿ + Bⁿ = Cⁿ` with `A, B, C ≥ 2`,
`Nat.Coprime A B`, and `n ≥ N` has `C ≤ M`.  In particular only finitely many
bases `C` occur once the exponent is large.

Concretely `N = 7` and `M = K^(4/13)`, where `K` is the ABC constant at `ε = 1/4`.
This is the `n = x = y = z` diagonal of `BealABCFinite.beal_base_bounded`, but with
the sharper `A·B·C < C³` (rather than `C^(2z/3 + 1)`), giving the larger exponent
gap `n − 3(1 + ε) = n − 15/4`. -/
theorem abc_imp_fermat_base_bounded (habc : BealRadical.ABCConjecture) :
    ∃ (N : ℕ) (M : ℝ), ∀ A B C n : ℕ,
      2 ≤ A → 2 ≤ B → 2 ≤ C → N ≤ n →
      Nat.Coprime A B → A ^ n + B ^ n = C ^ n → (C : ℝ) ≤ M := by
  -- ABC at ε = 1/4 gives the value bound for primitive Beal solutions.
  obtain ⟨K, hK, hbound⟩ :=
    BealRadical.beal_abc_bounded habc (ε := (1/4 : ℝ)) (by norm_num)
  refine ⟨7, K ^ ((4 : ℝ) / 13), ?_⟩
  intro A B C n hA hB hC hn hcop hsum
  -- Basic positivity / coprimality bookkeeping.
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  have hC0 : C ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hcoppow : Nat.Coprime (A ^ n) (B ^ n) := Nat.Coprime.pow n n hcop
  -- The value bound (diagonal x = y = z = n): Cⁿ ≤ K·(ABC)^(5/4).
  have hval := hbound A B C n n n hA0 hB0 hC0 hn0 hn0 hn0 hcoppow hsum
  -- The cube bound: A·B·C < C³ (over ℕ, hence over ℝ).
  have hcubeN : A * B * C < C ^ 3 := abc_lt_C_cubed hA hB hC hn1 hsum
  -- Real-side bookkeeping for C.
  have hCR2 : (2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by linarith
  have hCpos : (0 : ℝ) < (C : ℝ) := by linarith
  have hABCpos : (0 : ℝ) < (A * B * C : ℝ) := by
    have : (0 : ℕ) < A * B * C := by positivity
    exact_mod_cast this
  -- A·B·C < C³ over ℝ, presented as an rpow with real exponent 3.
  have hcube : (A * B * C : ℝ) < (C : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hcubeN
  -- (ABC)^(5/4) < (C³)^(5/4) = C^(15/4).
  have hprod54 : (A * B * C : ℝ) ^ (1 + (1/4 : ℝ))
      < ((C : ℝ) ^ (3 : ℝ)) ^ (1 + (1/4 : ℝ)) := by
    apply Real.rpow_lt_rpow (le_of_lt hABCpos) hcube
    norm_num
  have hrhs_simp : ((C : ℝ) ^ (3 : ℝ)) ^ (1 + (1/4 : ℝ))
      = (C : ℝ) ^ (15 / 4 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hCpos)]
    congr 1
    ring
  -- Combine: Cⁿ ≤ K·(ABC)^(5/4) < K·C^(15/4).
  have hCn_rpow : (C : ℝ) ^ (n : ℝ) = ((C ^ n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hval' : (C : ℝ) ^ (n : ℝ) ≤ K * (A * B * C : ℝ) ^ (1 + (1/4 : ℝ)) := by
    rw [hCn_rpow]; exact hval
  have hchain : (C : ℝ) ^ (n : ℝ) < K * (C : ℝ) ^ (15 / 4 : ℝ) := by
    calc (C : ℝ) ^ (n : ℝ)
        ≤ K * (A * B * C : ℝ) ^ (1 + (1/4 : ℝ)) := hval'
      _ < K * ((C : ℝ) ^ (3 : ℝ)) ^ (1 + (1/4 : ℝ)) := by
          exact mul_lt_mul_of_pos_left hprod54 hK
      _ = K * (C : ℝ) ^ (15 / 4 : ℝ) := by rw [hrhs_simp]
  -- Divide by C^(15/4): C^(n − 15/4) < K.
  have hpowpos : (0 : ℝ) < (C : ℝ) ^ (15 / 4 : ℝ) := Real.rpow_pos_of_pos hCpos _
  have hgap : (C : ℝ) ^ ((n : ℝ) - 15/4) < K := by
    have hsplit : (C : ℝ) ^ (n : ℝ)
        = (C : ℝ) ^ ((n : ℝ) - 15/4) * (C : ℝ) ^ (15 / 4 : ℝ) := by
      rw [← Real.rpow_add hCpos]
      congr 1
      ring
    rw [hsplit] at hchain
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hpowpos)
  -- For n ≥ 7 the exponent n − 15/4 ≥ 13/4 > 0, and C ≥ 2 > 1.
  have hexp_ge : (13 : ℝ) / 4 ≤ (n : ℝ) - 15/4 := by
    have : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 7 ≤ n)
    linarith
  -- C^(13/4) ≤ C^(n − 15/4) < K, since C ≥ 1 and exponent increases.
  have hmono_exp : (C : ℝ) ^ ((13 : ℝ) / 4) ≤ (C : ℝ) ^ ((n : ℝ) - 15/4) :=
    Real.rpow_le_rpow_of_exponent_le hCR1 hexp_ge
  have h134 : (C : ℝ) ^ ((13 : ℝ) / 4) < K := lt_of_le_of_lt hmono_exp hgap
  -- Raise to the (4/13) power: C ≤ K^(4/13).  Both sides nonneg, rpow monotone.
  have h134pos : (0 : ℝ) ≤ (C : ℝ) ^ ((13 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hCpos) _
  have hraise : ((C : ℝ) ^ ((13 : ℝ) / 4)) ^ ((4 : ℝ) / 13)
      ≤ K ^ ((4 : ℝ) / 13) :=
    Real.rpow_le_rpow h134pos (le_of_lt h134) (by norm_num)
  have hCsimp : ((C : ℝ) ^ ((13 : ℝ) / 4)) ^ ((4 : ℝ) / 13) = (C : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hCpos)]
    norm_num
  calc (C : ℝ) = ((C : ℝ) ^ ((13 : ℝ) / 4)) ^ ((4 : ℝ) / 13) := hCsimp.symm
    _ ≤ K ^ ((4 : ℝ) / 13) := hraise

/-! ## 4. HEADLINE 2: ABC ⟹ for each large `n`, finitely many counterexamples -/

/-- **HEADLINE 2 (asymptotic FLT, finiteness form).** Assume the ABC conjecture.
Then there is a threshold `N` such that for every exponent `n ≥ N` the set of
Fermat-`n` counterexamples
`{ (A, B, C) | A, B, C ≥ 2, Coprime A B, Aⁿ + Bⁿ = Cⁿ }` is **finite**.

The base `C` is bounded by the absolute constant `M` of
`abc_imp_fermat_base_bounded`, and `A, B < C ≤ M` (no `Cⁿ` blow-up — this is
cleaner than the off-diagonal Beal case).  Hence every counterexample triple lives
inside the finite box `{ (A,B,C) | A ≤ ⌊M⌋₊ ∧ B ≤ ⌊M⌋₊ ∧ C ≤ ⌊M⌋₊ }`. -/
theorem abc_imp_fermat_finite (habc : BealRadical.ABCConjecture) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Set.Finite { p : ℕ × ℕ × ℕ |
        2 ≤ p.1 ∧ 2 ≤ p.2.1 ∧ 2 ≤ p.2.2 ∧ Nat.Coprime p.1 p.2.1 ∧
        p.1 ^ n + p.2.1 ^ n = p.2.2 ^ n } := by
  obtain ⟨N, M, hM⟩ := abc_imp_fermat_base_bounded habc
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  -- Embed the counterexample set into a finite product box of side ⌊M⌋₊.
  set Mf : ℕ := Nat.floor M with hMf
  apply Set.Finite.subset
    (Set.finite_Iic (Mf, Mf, Mf) : Set.Finite { q : ℕ × ℕ × ℕ | q ≤ (Mf, Mf, Mf) })
  intro p hp
  obtain ⟨hA, hB, hC, hcop, hsum⟩ := hp
  obtain ⟨A, B, C⟩ := p
  show A ≤ Mf ∧ B ≤ Mf ∧ C ≤ Mf
  -- Re-state the membership data with the triple-projections reduced to `A, B, C`,
  -- so `omega` can read `A^n`, `B^n`, `C^n` below.
  have hA' : 2 ≤ A := hA
  have hB' : 2 ≤ B := hB
  have hC' : 2 ≤ C := hC
  have hsum' : A ^ n + B ^ n = C ^ n := hsum
  -- C ≤ M, so C ≤ ⌊M⌋₊.
  have hCM : (C : ℝ) ≤ M := hM A B C n hA' hB' hC' hN hcop hsum'
  have hCMf : C ≤ Mf := Nat.le_floor hCM
  -- A, B < C from the Fermat inequality, so A, B ≤ ⌊M⌋₊ too.
  have hBn : 0 < B ^ n := pow_pos (by omega) n
  have hAn : 0 < A ^ n := pow_pos (by omega) n
  have hAC : A < C := fermat_base_lt hn1 (by omega) (by omega)
  have hBC : B < C := fermat_base_lt hn1 (by omega) (by omega)
  -- Package the componentwise bound (A,B,C) ≤ (Mf,Mf,Mf).
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (le_of_lt hAC) hCMf
  · exact le_trans (le_of_lt hBC) hCMf
  · exact hCMf

/-! ## 5. Remark: ABC ⟹ asymptotic FLT (the classical Granville–Tucker corollary)

`abc_imp_fermat_base_bounded` and `abc_imp_fermat_finite` together constitute the
formalized statement that **the ABC conjecture implies Fermat's Last Theorem for
all sufficiently large exponents** (asymptotic FLT, Granville–Tucker).  Beyond a
fixed exponent threshold `N` (here `N = 7`):

* every Fermat counterexample `Aⁿ + Bⁿ = Cⁿ` (coprime, bases `≥ 2`) has its base
  bounded by an absolute constant `M`; and
* for each such `n` there are only **finitely many** counterexamples.

This validates that the project's `BealRadical.ABCConjecture` `Prop` is genuinely
strong enough to recover Fermat for large exponents — recall mathlib proves FLT
unconditionally only for `n = 3, 4` (`fermatLastTheoremThree`, `…Four`), while the
full theorem is Wiles', not ABC-derived.  The ABC route gives the *asymptotic* form
cheaply, mechanized here.

These statements are the **`n = x = y = z` diagonal** of the Beal results in
`BealABCFinite.lean`; the common exponent makes `A, B < C` direct, yielding the
sharper `A·B·C < C³` and the wider exponent gap `n − 15/4`. -/

end BealABCFermat
