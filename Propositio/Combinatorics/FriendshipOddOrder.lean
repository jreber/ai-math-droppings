/-
# Friendship graphs have an ODD vertex count

A direct corollary of `FriendshipVertexCount.friendship_card_eq`: for a `k`-regular
friendship graph `G` on `n = |V|` vertices, `n = k² − k + 1 = k·(k−1) + 1`. Since
`k·(k−1)` is a product of two consecutive integers, it is even, so `n` is odd.

## Main mathlib API used
* `FriendshipVertexCount.friendship_card_eq` — the vertex-count identity (in `ℤ`)
* `Int.even_mul_pred_self : Even (n * (n - 1))` — product of consecutive integers is even
* `Even.add_one : Even a → Odd (a + 1)`
* `Int.odd_coe_nat : Odd (↑n) ↔ Odd n` — transfer parity from `ℤ` back to `ℕ`
-/
import Propositio.Combinatorics.FriendshipVertexCount

namespace FriendshipOddOrder

open SimpleGraph FriendshipVertexCount FriendshipMatrixEquation

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **A `k`-regular friendship graph has an odd number of vertices.**
Since `n = k² − k + 1 = k(k − 1) + 1` and `k(k − 1)` (a product of consecutive naturals)
is always even, `n` is odd. -/
theorem friendship_card_odd (hfriend : Friendship G) {k : ℕ}
    (hreg : G.IsRegularOfDegree k) [Nonempty V] :
    Odd (Fintype.card V) := by
  have heq := FriendshipVertexCount.friendship_card_eq G hfriend hreg
  rw [← Int.odd_coe_nat, heq]
  have hrw : (k : ℤ) ^ 2 - (k : ℤ) + 1 = (k : ℤ) * ((k : ℤ) - 1) + 1 := by ring
  rw [hrw]
  exact (Int.even_mul_pred_self (k : ℤ)).add_one

-- Non-vacuity: K₃ (= completeGraph (Fin 3)) is a 2-regular friendship graph, giving Odd 3.
-- A permanent machine-checked `example` is a natural follow-up: `IsRegularOfDegree.top`
-- discharges regularity, but `Friendship` (an `∃!` over the vertex Fintype) needs a
-- `Decidable` instance supplied to `decide` (not auto-synthesized here).

end FriendshipOddOrder
