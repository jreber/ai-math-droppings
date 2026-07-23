/-
Zsygmondy primitive-prime-order lemma.

If `p` is a prime dividing the value of the `n`-th cyclotomic polynomial at an integer `a`,
and `p` does not divide `n`, then the multiplicative order of `a` modulo `p` equals `n`.

This is the key algebraic fact underlying Zsygmondy's theorem: a prime dividing `Φ_n(a)` but
not `n` must be a genuinely "new" (primitive) prime divisor of `a^n - 1`, because its order
in `(ZMod p)ˣ` is exactly `n`.

Proof strategy:
1. Work in `ZMod p`, a field since `p` is prime.
2. `¬ p ∣ n` gives `NeZero (n : ZMod p)`, the side condition needed by
   `Polynomial.isRoot_cyclotomic_iff : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n`.
3. `IsPrimitiveRoot.eq_orderOf` then reads off `orderOf x = n`.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic

open Polynomial

/-- **Core lemma** (stated directly in `ZMod p`, which is the mathematically faithful and
`Polynomial.isRoot_cyclotomic_iff`-ready form): if `x : ZMod p` is a root of the `n`-th
cyclotomic polynomial over `ZMod p`, and `p` does not divide `n`, then `x` has multiplicative
order exactly `n`. -/
theorem primitive_order_of_isRoot_cyclotomic {n p : ℕ} (_hn : 1 < n) [Fact p.Prime]
    {x : ZMod p} (hx : (cyclotomic n (ZMod p)).IsRoot x) (hpn : ¬ p ∣ n) :
    orderOf x = n := by
  haveI : NeZero (n : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  have hprim : IsPrimitiveRoot x n := isRoot_cyclotomic_iff.mp hx
  exact hprim.eq_orderOf.symm

/-- **Zsygmondy primitive-prime-order lemma**, stated for an integer `a`: if a prime `p`
divides `(cyclotomic n ℤ).eval a` and `p` does not divide `n`, then the order of `a` mod `p`
(computed in `ZMod p`) equals `n`. -/
theorem primitive_order_of_dvd_cyclotomic {n p : ℕ} (_hn : 1 < n) [Fact p.Prime]
    (a : ℤ) (hp : (p : ℤ) ∣ (cyclotomic n ℤ).eval a) (hpn : ¬ p ∣ n) :
    orderOf (a : ZMod p) = n := by
  have hx : (cyclotomic n (ZMod p)).IsRoot (a : ZMod p) := by
    have heval := cyclotomic.eval_apply a n (Int.castRingHom (ZMod p))
    simp only [Int.coe_castRingHom] at heval
    have hzero : (((cyclotomic n ℤ).eval a : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp
    show eval (a : ZMod p) (cyclotomic n (ZMod p)) = 0
    rw [heval, hzero]
  exact primitive_order_of_isRoot_cyclotomic _hn hx hpn
