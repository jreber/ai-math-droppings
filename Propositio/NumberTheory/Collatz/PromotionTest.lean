import Propositio.NumberTheory.Collatz.Basic
import Mathlib.Tactic

/-! Throwaway synthetic file, exists only to test scripts/promote_to_propositio.py
end-to-end. Not a real result -- safe to delete/promote without affecting anything
else, since nothing imports it. -/

namespace CollatzPromotionTest

open TerrasDensity (cc)

theorem promotion_test_trivial (n : Nat) : cc n = cc n := rfl

end CollatzPromotionTest
