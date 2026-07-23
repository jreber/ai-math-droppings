import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# Mantel's theorem

Mantel's theorem (1907) is the `r = 2` case of Turán's theorem: a triangle-free
simple graph on `n` vertices has at most `⌊n²/4⌋` edges.

Here "triangle-free" is `G.CliqueFree 3` (no `3`-clique). We state the bound in the
division-free form `4 * |E(G)| ≤ n²`, which is equivalent to `|E(G)| ≤ ⌊n²/4⌋`.

The proof is a faithful reduction to mathlib's exact Turán edge-count bound
`SimpleGraph.CliqueFree.card_edgeFinset_le`, specialised to `r = 2`. That bound reads
`|E| ≤ (n² - (n % 2)²) * (2 - 1) / (2 * 2) + (n % 2).choose 2`; here
`(n % 2).choose 2 = 0` (since `n % 2 < 2`), so `|E| ≤ (n² - (n % 2)²) / 4 ≤ n² / 4`.
-/

namespace SimpleGraph

/-- **Mantel's theorem.** A triangle-free (`CliqueFree 3`) simple graph on `n` vertices has
at most `⌊n²/4⌋` edges, stated in the division-free form `4 * |E(G)| ≤ n²`. -/
theorem mantel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  have h := hG.card_edgeFinset_le (r := 2)
  dsimp only at h
  have hc : (Fintype.card V % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [hc] at h
  omega

end SimpleGraph
