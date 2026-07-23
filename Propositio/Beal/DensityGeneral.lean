import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Propositio.Beal.Density

/-!
# Bucket 2+ — CRT-product / multi-variable density (NEW, no LaTTe sibling)

**NEW results extending the LaTTe port (no LaTTe sibling)** — the CRT-product /
multi-variable density that the design memo
(`docs/threads/beal/l4-pair-count-design.md` §6) flagged as future work.

The LaTTe development (mirrored in `BealDensity.lean`) stops at the two-variable,
**single-modulus** pair-solution count
`BealDensity.pair_solution_count`:

  `Nat.card (pairHom n x y).ker = n * gcd(n, gcd(x, y))`.

§6 of the design memo (`## 6. Beyond L4 — Path to Full Density Formula and CRT`)
records the next step as a *CRT product*: assembling the per-modulus counts for
coprime moduli into the count for their product. The memo only sketches this as
"structurally identical [to L4] but at the product level". This file proves it.

## What is new here (versus the LaTTe port)

* `pairHom_ker_chineseRemainder_equiv` — the genuine **CRT bijection**: for
  coprime `m, n` the solution set over `ZMod (m*n)` is in explicit bijection with
  the product of the solution sets over `ZMod m` and `ZMod n`, transported along
  the Chinese-Remainder ring isomorphism `ZMod.chineseRemainder`. This is the
  product-pair bijection §6 asks for, made concrete on the *kernel subtypes*.

* `pair_solution_count_mul` (**HEADLINE**) — multiplicativity of the count, read
  off the bijection: for coprime `m, n > 0`,
  `Nat.card (pairHom (m*n) x y).ker
     = Nat.card (pairHom m x y).ker * Nat.card (pairHom n x y).ker`.

* `pair_solution_count_closed_form_mul` — the corresponding purely-arithmetic
  identity on the closed forms (consistency with `Nat.Coprime.gcd_mul`):
  `(m*n) * gcd(m*n, gcd x y)
     = (m * gcd(m, gcd x y)) * (n * gcd(n, gcd x y))` for coprime `m, n`.

These are genuinely new theorems (no LaTTe sibling exists): the LaTTe corpus
never multiplied two moduli.
-/

namespace BealDensityGeneral

open BealDensity AddMonoidHom

/-!
## 1. The CRT bijection on solution sets

For `Nat.Coprime m n`, `ZMod.chineseRemainder` is a *ring* isomorphism
`e : ZMod (m*n) ≃+* ZMod m × ZMod n`. We package the solution set
`{ p : ZMod N × ZMod N // x • p.1 + y • p.2 = 0 }` (`N` the modulus) and show the
two product copies of `e` carry it bijectively onto the product of the two
single-modulus solution sets.

The condition transfers because `e` is an additive monoid hom, so it commutes
with `nsmul` (`map_nsmul`) and sends `0 ↦ 0` (`map_eq_zero_iff`); evaluated
componentwise this is exactly the pair of single-modulus conditions.
-/

/-- The solution-set subtype attached to `pairHom N x y` — the kernel as a
`Subtype` of the explicit predicate `x • p.1 + y • p.2 = 0`. -/
abbrev SolSet (N x y : ℕ) := { p : ZMod N × ZMod N // x • p.1 + y • p.2 = 0 }

/-- **CRT bijection (NEW).**
For coprime `m, n`, the two-variable solution set over `ZMod (m*n)` is in
explicit bijection with the product of the solution sets over `ZMod m` and
`ZMod n`, via the Chinese-Remainder ring isomorphism. This is the product-pair
bijection that design-memo §6 flags as the CRT step. -/
noncomputable def pairHom_ker_chineseRemainder_equiv
    (m n : ℕ) (h : Nat.Coprime m n) (x y : ℕ) :
    SolSet (m * n) x y ≃ SolSet m x y × SolSet n x y := by
  -- `e : ZMod (m*n) ≃+* ZMod m × ZMod n`, viewed as an additive equiv.
  let e := (ZMod.chineseRemainder h).toAddEquiv
  -- Equiv on the *ambient* pair space:
  --   (ZMod (m*n))²  ≃  (ZMod m × ZMod n)²  ≃  (ZMod m)² × (ZMod n)².
  let E : (ZMod (m * n) × ZMod (m * n)) ≃ (ZMod m × ZMod m) × (ZMod n × ZMod n) :=
    (e.prodCongr e).toEquiv.trans (Equiv.prodProdProdComm (ZMod m) (ZMod n) (ZMod m) (ZMod n))
  -- `subtypeProdEquivProd` packs the product of the two single-modulus solution
  -- sets as a subtype of `(ZMod m × ZMod m) × (ZMod n × ZMod n)` whose predicate
  -- is the conjunction of the two componentwise conditions.
  refine (Equiv.subtypeEquiv E ?_).trans
    (Equiv.subtypeProdEquivProd
      (p := fun p : ZMod m × ZMod m => x • p.1 + y • p.2 = 0)
      (q := fun p : ZMod n × ZMod n => x • p.1 + y • p.2 = 0))
  -- Condition-transfer: `x • a + y • b = 0` over `ZMod (m*n)` ↔ the conjunction
  -- of the two componentwise conditions, read off `E (a,b)`.
  rintro ⟨a, b⟩
  -- LHS predicate, in `ZMod (m*n)`.
  show x • a + y • b = 0 ↔ _
  -- Apply `e` (a ring/additive iso): `c = 0 ↔ e c = 0`, and `e` commutes with `+`, `nsmul`.
  rw [← (ZMod.chineseRemainder h).map_eq_zero_iff]
  -- Push `e` through the sum and the nsmuls.
  rw [map_add, map_nsmul, map_nsmul]
  -- Now both sides live in `ZMod m × ZMod n`; compare componentwise.
  -- `E (a,b)` has fst `((e a).1, (e b).1)` and snd `((e a).2, (e b).2)`.
  show (x • (ZMod.chineseRemainder h) a + y • (ZMod.chineseRemainder h) b = 0) ↔ _
  rw [Prod.ext_iff, Prod.add_def]
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero]
  rfl

/-!
## 2. Headline: multiplicativity of the pair-solution count
-/

/-- **Pair-solution count is multiplicative over coprime moduli (HEADLINE, NEW).**
For coprime `m, n > 0` and any `x, y`, the number of pairs `(a, b)` with
`x • a + y • b = 0` over `ZMod (m*n)` equals the product of the corresponding
counts over `ZMod m` and `ZMod n`.

This is the CRT-product step of design-memo §6, proved by transporting the
solution set along the Chinese-Remainder isomorphism
(`pairHom_ker_chineseRemainder_equiv`) and reading off cardinalities. No LaTTe
sibling: the LaTTe corpus never combined two moduli. -/
theorem pair_solution_count_mul
    (m n : ℕ) [NeZero m] [NeZero n] (h : Nat.Coprime m n) (x y : ℕ) :
    Nat.card (pairHom (m * n) x y).ker
      = Nat.card (pairHom m x y).ker * Nat.card (pairHom n x y).ker := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  -- Rewrite each kernel as its `SolSet` subtype (same predicate, defeq).
  have key : Nat.card (SolSet (m * n) x y)
      = Nat.card (SolSet m x y) * Nat.card (SolSet n x y) := by
    rw [Nat.card_congr (pairHom_ker_chineseRemainder_equiv m n h x y), Nat.card_prod]
  -- Bridge `ker` ↔ `SolSet`: the kernel of `pairHom` is exactly this subtype.
  have hker : ∀ N : ℕ, Nat.card (pairHom N x y).ker = Nat.card (SolSet N x y) := by
    intro N
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro p
    simp [AddMonoidHom.mem_ker, pairHom_apply]
  rw [hker, hker, hker, key]

/-!
## 3. Corollary: closed-form multiplicativity (consistency with `gcd_mul`)
-/

/-- **Closed-form multiplicativity (NEW corollary).**
The closed form `N * gcd(N, gcd x y)` is multiplicative over coprime `m, n`,
matching `pair_solution_count_mul`. Purely arithmetic, via `Nat.Coprime.gcd_mul`.
-/
theorem pair_solution_count_closed_form_mul
    (m n : ℕ) (h : Nat.Coprime m n) (x y : ℕ) :
    (m * n) * Nat.gcd (m * n) (Nat.gcd x y)
      = (m * Nat.gcd m (Nat.gcd x y)) * (n * Nat.gcd n (Nat.gcd x y)) := by
  rw [Nat.gcd_comm (m * n) (Nat.gcd x y), Nat.gcd_comm m (Nat.gcd x y),
    Nat.gcd_comm n (Nat.gcd x y), Nat.Coprime.gcd_mul (Nat.gcd x y) h]
  ring

/-- Sanity: the headline count multiplicativity and the closed-form
multiplicativity agree (both follow, independently, the same product law). -/
theorem pair_solution_count_mul_closed_form
    (m n : ℕ) [NeZero m] [NeZero n] (h : Nat.Coprime m n) (x y : ℕ) :
    Nat.card (pairHom (m * n) x y).ker
      = (m * Nat.gcd m (Nat.gcd x y)) * (n * Nat.gcd n (Nat.gcd x y)) := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [pair_solution_count_mul m n h x y, pair_solution_count, pair_solution_count]

end BealDensityGeneral
