/-
Zsygmondy Phi/order bridge — the two-variable cyclotomic-to-`ZMod p` reduction.

Connects the homogeneous bivariate cyclotomic factor `Phi n a b`
(`ZsygmondyHomogeneousCyclotomicFactor.Phi`) to the field-valued cyclotomic evaluation
in `ZMod p`, at the ratio `a * b⁻¹`. This is the single new bridge lemma the general-`b`
port of the `ZsygmondyIntrinsicFactor` / `ZsygmondyPrimitiveOrder` / `ZsygmondyPrimitivePrimeCongr`
dichotomy needs; once it is in hand, the downstream order-of-`(a * b⁻¹)` reasoning is a
direct copy of the `b = 1` proofs with `a` replaced by `a * b⁻¹` throughout.

Statement: for a prime `p`, integers `a b` with `p ∤ b`, and `n : ℕ`:

  `(p : ℤ) ∣ Phi n a b ↔ (cyclotomic n (ZMod p)).IsRoot ((a : ZMod p) * (b : ZMod p)⁻¹)`.

Proof strategy:
1. Cast `Phi n a b` mod `p`: since `Phi n a b = MvPolynomial.eval ![a, b] (P.homogenize d)`
   with `P := cyclotomic n ℤ`, `d := P.natDegree`, naturality of `MvPolynomial.eval` under
   the ring hom `Int.castRingHom (ZMod p)` (via `eval₂_comp` + `eval₂_eq_eval_map`) gives
   `((Phi n a b : ℤ) : ZMod p) = MvPolynomial.eval ![(a : ZMod p), (b : ZMod p)]
     ((P.map (Int.castRingHom (ZMod p))).homogenize d)`.
2. `map_cyclotomic_int` identifies `P.map (Int.castRingHom (ZMod p)) = cyclotomic n (ZMod p)`.
3. `(cyclotomic n (ZMod p)).natDegree = d` since `cyclotomic n ℤ` is monic
   (`Polynomial.Monic.natDegree_map`), so the `Semifield`-section `eval_homogenize` lemma
   applies (`ZMod p` is a field, hence a semifield) with `x 1 = (b : ZMod p) ≠ 0`:
   `MvPolynomial.eval ![a, b] ((cyclotomic n (ZMod p)).homogenize d)
     = (cyclotomic n (ZMod p)).eval (a / b) * b ^ d`.
4. Since `b ≠ 0` in the field `ZMod p`, `b ^ d ≠ 0`, so the LHS vanishes iff the cyclotomic
   evaluation at `a / b = a * b⁻¹` vanishes. Combine with `ZMod.intCast_zmod_eq_zero_iff_dvd`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHomogeneousCyclotomicFactor
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

/-- Naturality of bivariate `MvPolynomial.eval` under `Int.cast`: casting the evaluation
of an integer bivariate polynomial `P` at `x` into a ring `S` equals evaluating the
`S`-cast of `P` at the `S`-cast of `x`. -/
private theorem eval_intCast_eq_eval_map {S : Type*} [CommRing S]
    (x : Fin 2 → ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    ((MvPolynomial.eval x P : ℤ) : S) =
      MvPolynomial.eval (fun i => ((x i : ℤ) : S)) (MvPolynomial.map (Int.castRingHom S) P) := by
  have h : (Int.castRingHom S) (MvPolynomial.eval x P) =
      MvPolynomial.eval ((Int.castRingHom S) ∘ x) (MvPolynomial.map (Int.castRingHom S) P) := by
    rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
  simpa using h

/-- The cast of `Phi n a b` mod `p` equals the bivariate evaluation of the mod-`p`
cyclotomic homogenization at `(a, b)`. -/
private theorem Phi_cast (n p_ : ℕ) [Fact p_.Prime] (a b : ℤ) :
    ((Phi n a b : ℤ) : ZMod p_) =
      MvPolynomial.eval ![(a : ZMod p_), (b : ZMod p_)]
        (((cyclotomic n ℤ).map (Int.castRingHom (ZMod p_))).homogenize
          (cyclotomic n ℤ).natDegree) := by
  unfold Phi
  rw [eval_intCast_eq_eval_map (![a, b] : Fin 2 → ℤ)
    ((cyclotomic n ℤ).homogenize (cyclotomic n ℤ).natDegree),
    Polynomial.homogenize_map]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp

/-- **Zsygmondy Phi/order bridge.** For a prime `p`, integers `a b` with `p ∤ b`, and
`n : ℕ`: `p ∣ Phi n a b` iff `a * b⁻¹` (in `ZMod p`) is a root of the `n`-th cyclotomic
polynomial over `ZMod p`. -/
theorem dvd_Phi_iff_isRoot_cyclotomic {n p : ℕ} [Fact p.Prime] (a b : ℤ)
    (hb : ¬ (p : ℤ) ∣ b) :
    (p : ℤ) ∣ Phi n a b ↔
      (cyclotomic n (ZMod p)).IsRoot ((a : ZMod p) * (b : ZMod p)⁻¹) := by
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hb
  have hmapcyc : (cyclotomic n ℤ).map (Int.castRingHom (ZMod p)) = cyclotomic n (ZMod p) :=
    map_cyclotomic_int n (ZMod p)
  have hdeg : (cyclotomic n (ZMod p)).natDegree = (cyclotomic n ℤ).natDegree := by
    rw [← hmapcyc]
    exact (Polynomial.cyclotomic.monic n ℤ).natDegree_map (Int.castRingHom (ZMod p))
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Phi_cast n p a b, hmapcyc]
  have heval := Polynomial.eval_homogenize (K := ZMod p) (p := cyclotomic n (ZMod p))
    (n := (cyclotomic n ℤ).natDegree) (le_of_eq hdeg)
    (![(a : ZMod p), (b : ZMod p)] : Fin 2 → ZMod p) (by simpa using hb0)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  rw [heval]
  rw [div_eq_mul_inv]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact h1
    · exact absurd h2 (pow_ne_zero _ hb0)
  · intro h
    rw [h]; ring
