/-!
# TerrasDensity custom tactics

Macros for proof patterns that recur across TerrasDensity.lean.
Each macro is gated by `lake build` before merging.

Add new macros here when tactic-bank.json shows a sequence with count ≥ 3.
-/

namespace TerrasDensity

/-- Close goals of the form: Odd n hypothesis in context, statement is a
    numeric inequality about n. Extracts witness k, substitutes n = 2*k+1,
    discharges with omega.

    Matches tactic-bank pattern: obtain ⟨k, hk⟩; subst hk; omega
    Applicable when: Odd n is the primary hypothesis and goal is arithmetic.

    Usage: `odd_omega hodd` where `hodd : Odd n` is in context.
-/
macro "odd_omega" id:ident : tactic =>
  `(tactic| (obtain ⟨k, hk⟩ := $id; subst hk; omega))

end TerrasDensity
