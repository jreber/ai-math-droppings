import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Tactic

/-!
# Final localization: the real-factor `z`-th-power condition lives in `ℚ(ζ_p)⁺`

The `(p,p,z)` reductions (`BealPrimeRealReductionSharp`, `BealRealReductionConcrete`) reduce the
descent to: *the real unit factor `v` is a `z`-th power in `(𝓞 K)ˣ`*. Since `v` is a **real**
unit it is the image of a unit `vp` of the maximal totally real subfield `K⁺ = ℚ(ζ_p)⁺`
(`mem_realUnits_iff`). This file records that the condition descends to `K⁺`:

> if `vp` is a `z`-th power in `(𝓞 K⁺)ˣ`, then `v` is a `z`-th power in `(𝓞 K)ˣ`.

So the entire remaining input for the `(p,p,z)` family is an honest `z`-th-power /Kummer question
about the unit group of the **totally real field `ℚ(ζ_p)⁺`** — for `p = 5`, the real quadratic
field `ℚ(√5)` and its fundamental unit (golden ratio). This is the precise residual wall.

`lake env lean BealRealSubfieldDescent.lean` to typecheck (SLOW — CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealRealSubfieldDescent

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- **Real-factor condition descends to the real subfield.** If the maximal-real-subfield unit
`vp` underlying a real unit `v` is a `z`-th power in `(𝓞 K⁺)ˣ`, then `v` is a `z`-th power in
`(𝓞 K)ˣ` (apply the inclusion `(𝓞 K⁺)ˣ → (𝓞 K)ˣ`, a monoid hom). -/
theorem real_factor_pow_of_subfield_pow {z : ℕ} {v : (𝓞 K)ˣ} {vp : (𝓞 K⁺)ˣ}
    (hvw : (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom) vp = v)
    (h : ∃ wp : (𝓞 K⁺)ˣ, vp = wp ^ z) :
    ∃ w : (𝓞 K)ˣ, v = w ^ z := by
  obtain ⟨wp, hw⟩ := h
  refine ⟨(Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom) wp, ?_⟩
  rw [← hvw, hw, map_pow]

end BealRealSubfieldDescent
