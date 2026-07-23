/-
Zsygmondy primitive-prime-order lemma — general-`b` port.

The two-variable generalization of `ZsygmondyPrimitiveOrder.primitive_order_of_dvd_cyclotomic`.

If a prime `p` divides `Phi n a b` (the homogeneous bivariate cyclotomic factor at
`(a, b)`), `p` does not divide `n`, and `p` does not divide `b`, then the multiplicative
order of `a * b⁻¹` modulo `p` equals `n`.

Note: the *core* lemma `ZsygmondyPrimitiveOrder.primitive_order_of_isRoot_cyclotomic`
is already stated purely in terms of `x : ZMod p` being a root of `cyclotomic n (ZMod p)`
— it needs no porting at all, since it never mentions `a` as an integer. Only the
integer-`a`-and-`b` wrapper (analogous to `primitive_order_of_dvd_cyclotomic`) is new
here, obtained by composing the core lemma with `dvd_Phi_iff_isRoot_cyclotomic`
(`ZsygmondyPhiOrderBridge`) at `x := a * b⁻¹`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveOrder
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPhiOrderBridge

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

/-- **Zsygmondy primitive-prime-order lemma, general `b`.** For a prime `p`, integers
`a b` with `p ∤ b`, and `n` with `p ∣ Phi n a b` and `p ∤ n`, the order of `a * b⁻¹` mod
`p` equals `n`. -/
theorem primitive_order_of_dvd_Phi_general {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    (a b : ℤ) (hpb : ¬ (p : ℤ) ∣ b) (hp : (p : ℤ) ∣ Phi n a b) (hpn : ¬ p ∣ n) :
    orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  have hx : (cyclotomic n (ZMod p)).IsRoot ((a : ZMod p) * (b : ZMod p)⁻¹) :=
    (dvd_Phi_iff_isRoot_cyclotomic a b hpb).mp hp
  exact primitive_order_of_isRoot_cyclotomic hn hx hpn
