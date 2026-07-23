import Propositio.NumberTheory.Diophantine.OSalikhovDenBoundReduced
import Propositio.NumberTheory.Diophantine.OSalikhovUnconditional

/-!
# `DenIntN n ≤ 6·30ⁿ` — UNCONDITIONAL, closing the lone `OSalikhovDenBound` sorry

`OSalikhovDenBound.DenIntN_bound_30 : ∀ n, DenIntN n ≤ 6·30ⁿ` was proved only for `n < 41`
(`native_decide` over `Fin 41`) with a documented `sorry` for `n ≥ 41`.  That `sorry` was the
last denominator gap of the μ(log₂3) → Collatz-PowGap prize.

The gap is now **fully closed downstream**, sorry-free, in two already-landed pieces:

* `OSalikhovDenDvd.DenIntN_bound_30_of_hdvd` (in `OSalikhovDenBoundReduced`) derives
  `DenIntN n ≤ 6·30ⁿ` for all `n` from the single arithmetic divisibility input
  `hdvd : ∀ m, DenIntN m ∣ 3ᵐ·30·lcm(1..2m)` — its `lcm`/effective-Chebyshev half being
  discharged unconditionally by `CollatzChebyshev30.lcm_two_n_le_target_all`.

* `OSalikhovUnconditional.hdvd_uncond` proves that very `hdvd` **unconditionally and sorry-free**,
  routing around the (deliberately stranded) `OSalikhovPFI.cResQ_one_eq_Bseq` sorry via the
  construction-internal `Irrational (Real.log (2/3))` argument
  (`OSalikhovUnconditional.irrational_log_two_thirds`).

The literal universal statement `DenIntN_bound_30` could not be made sorry-free *in place*:
`OSalikhovUnconditional` transitively imports `OSalikhovDenBound` (via
`CollatzPowGapOfHdvd → OSalikhovDenBoundReduced`), so wiring the two together must happen in a
**new downstream leaf** — this file.  We provide the exact target statement (both the `ℕ` and the
`ℝ`-interface forms) as sorry-free, axiom-clean theorems.
-/

namespace OSalikhovDenBoundUnconditional

open OSalikhovIntCoord

/-- **`DenIntN n ≤ 6·30ⁿ` for ALL `n` — UNCONDITIONAL, sorry-free.**  This is precisely the
statement of `OSalikhovDenBound.DenIntN_bound_30`, whose `n ≥ 41` branch was a `sorry`; here it is
discharged by combining the two landed sorry-free bricks `DenIntN_bound_30_of_hdvd` and
`hdvd_uncond`. -/
theorem DenIntN_bound_30_unconditional (n : ℕ) : DenIntN n ≤ 6 * 30 ^ n :=
  OSalikhovDenDvd.DenIntN_bound_30_of_hdvd OSalikhovUnconditional.hdvd_uncond n

/-- **The ℝ-valued interface form `DenR n ≤ 6·30ⁿ` — UNCONDITIONAL, sorry-free.**  This is the
shape the oSALIKHOV measure engine consumes (cf. `OSalikhovDenBound.DenR_bound_30`, which also
depended on the now-closed gap). -/
theorem DenR_bound_30_unconditional (n : ℕ) : DenR n ≤ (6 : ℝ) * (30 : ℝ) ^ n :=
  OSalikhovDenDvd.DenR_bound_30_of_hdvd OSalikhovUnconditional.hdvd_uncond n

-- Axiom audit: target is the clean base `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
-- no project axiom).  `native_decide`-borne `Lean.ofReduceBool` may appear via the finite
-- Chebyshev census inside `lcm_two_n_le_target_all`, exactly as for the already-audited
-- `OSalikhovUnconditional.collatz_powGap_unconditional`.
#print axioms DenIntN_bound_30_unconditional
#print axioms DenR_bound_30_unconditional

end OSalikhovDenBoundUnconditional
