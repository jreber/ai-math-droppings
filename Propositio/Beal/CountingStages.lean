import Propositio.Beal.Density
import Mathlib.Data.Nat.Totient

/-!
# Bucket 2 — Beal counting STAGES: φ(pᵏ) instantiations + named exponent-image count

Lean 4 port completing the *named-theorem* coverage of the LaTTe
density-wall-close (`src/ai_math/beal/density_wall_close.clj`) and
exponent-image-count (`src/ai_math/beal/exponent_image_count.clj`) registries
(test deftests `beal-density-wall-close-theorems-real`,
`beal-exponent-image-count-theorems-real`).

The genuine cardinality content of the single-variable counting layer already
lives in `BealDensity`:

* `BealDensity.solution_count`  — `|ker(x ↦ d•x on ZMod n)| = gcd(n, d)`.
* `BealDensity.image_count`     — `|range(x ↦ d•x on ZMod n)| = n / gcd(n, d)`.

This file adds the **φ(pᵏ) instantiations** of those counts (the
`*-at-phi-pp` theorems), plus a named mirror of the LaTTe `exponent-image-count`
headline. Each is a thin corollary obtained by specialising `n := Nat.totient
(p^k)` and rewriting with `Nat.totient_prime_pow` (`= p^(k-1)·(p-1)`), exactly
as `BealDensity.density_count_at_phi_pp` does for the pair count. That thinness
is expected: the LaTTe `*-at-phi-pp` theorems are themselves single-`qed`
delegations of their generic siblings to `n := phi-pp pk1 p`.

## Faithfulness notes / framing differences

The LaTTe sources, lacking a finite-cardinality library, phrase "how many" as
an explicit **bijection package** (totality + surjectivity + injectivity of the
indexing map `k ↦ k·g` resp. `k ↦ r + k·n'`). mathlib has genuine finite
cardinality (`Nat.card` on a finite cyclic group), so each "the image/solution
set bijects with `[0, …)`" theorem is restated as the literal cardinality it
computes — a single `Nat.card … = …` equation. The Lean equation *is* the
content the LaTTe bijection exhibits (a set of the stated size).

`solution-count-from-solvability` (LaTTe Stage A headline) is **subsumed** — see
the section note below; it is not given a (trivial) alias.

House style follows `BealDensity.lean`: each theorem carries a doc-comment
ending in `LaTTe sibling: <clj path> :: <name>`.

Dependency policy: mathlib4 permitted; reuses the already-built `BealDensity`.
Typecheck with `lake env lean BealCountingStages.lean`.

Key mathlib lemmas relied on:
* `Nat.totient_prime_pow` — `Nat.totient (p^k) = p^(k-1)·(p-1)` for prime `p`,
  `0 < k`.
* `BealDensity.solution_count`, `BealDensity.image_count` (reuse).
-/

namespace BealCountingStages

open BealDensity

/-!
## 1. solution-count-at-phi-pp  (density_wall_close Stage B)

Instantiate the single-variable kernel count at `n = φ(pᵏ)`.

The LaTTe `solution-count-at-phi-pp` packages the full coset *bijection* at
`n := phi-pp pk1 p`. The cardinality that bijection exhibits is `gcd(n, d)`;
here we state that cardinality directly at `n = Nat.totient (p^k)`, then rewrite
`= p^(k-1)·(p-1)` via `Nat.totient_prime_pow`.
-/

/-- **Single-variable solution count at `φ(pᵏ)` (Stage B).**
For `p` prime and `k ≥ 1`, with `n = φ(pᵏ) = p^(k-1)·(p-1)`, the number of
`x ∈ ZMod n` with `d • x = 0` is `gcd(p^(k-1)·(p-1), d)`.

Corollary of `BealDensity.solution_count` at `n := Nat.totient (p^k)`, rewritten
via `Nat.totient_prime_pow`.

LaTTe sibling: `src/ai_math/beal/density_wall_close.clj` ::
`solution-count-at-phi-pp`. -/
theorem solution_count_at_phi_pp
    (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (d : ℕ)
    [NeZero (Nat.totient (p ^ k))] :
    Nat.card (nsmulAddMonoidHom (α := ZMod (Nat.totient (p ^ k))) d).ker
      = Nat.gcd (p ^ (k - 1) * (p - 1)) d := by
  haveI hne : NeZero (p ^ (k - 1) * (p - 1)) := by
    rw [← Nat.totient_prime_pow hp hk]; infer_instance
  rw [Nat.totient_prime_pow hp hk]
  exact solution_count (p ^ (k - 1) * (p - 1)) d

/-!
## 2. exponent-image-count  (exponent_image_count headline)

The LaTTe `exponent-image-count` (Stage C headline) packages the bijection
`k ↦ k·g` between `[0, n')` and the image of `j ↦ d·j` on `Z/nZ`, where
`g = gcd(d, n)` and `n' = n/g`; i.e. the image has exactly `n' = n/gcd(d,n)`
elements.

That cardinality `= n / gcd(n, d)` is *exactly* `BealDensity.image_count`. We
provide a named mirror under the LaTTe name so the registry name is explicitly
covered; the content is identical to (and proved by) `image_count`, so this is a
faithful renaming rather than new mathematics.
-/

/-- **Exponent-image count (Stage C headline).**
In `ZMod n` (`n > 0`), the image of `j ↦ d • j` has exactly `n / gcd(n, d)`
elements — the cardinality exhibited by the LaTTe bijection `k ↦ k·g` between
`[0, n')` and the image (`g = gcd(d, n)`, `n' = n/g`).

This is the literal cardinality content of the LaTTe headline; it coincides
with `BealDensity.image_count` (named mirror under the LaTTe registry name).

LaTTe sibling: `src/ai_math/beal/exponent_image_count.clj` ::
`exponent-image-count`. -/
theorem exponent_image_count (n : ℕ) [NeZero n] (d : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := ZMod n) d).range = n / Nat.gcd n d :=
  image_count n d

/-!
## 3. exponent-image-count-at-phi-pp  (exponent_image_count Stage C at φ(pᵏ))

Instantiate the exponent-image count at `n = φ(pᵏ)`, mirroring
`solution-count-at-phi-pp` for the image-count (exponent) side.
-/

/-- **Exponent-image count at `φ(pᵏ)` (Stage C at phi-pp).**
For `p` prime and `k ≥ 1`, with `n = φ(pᵏ) = p^(k-1)·(p-1)`, the image of
`j ↦ d • j` on `ZMod n` has exactly `(p^(k-1)·(p-1)) / gcd(p^(k-1)·(p-1), d)`
elements.

Corollary of `BealDensity.image_count` at `n := Nat.totient (p^k)`, rewritten
via `Nat.totient_prime_pow`. Mirrors `solution_count_at_phi_pp` for the
image-count side of the density lift.

LaTTe sibling: `src/ai_math/beal/exponent_image_count.clj` ::
`exponent-image-count-at-phi-pp`. -/
theorem exponent_image_count_at_phi_pp
    (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (d : ℕ)
    [NeZero (Nat.totient (p ^ k))] :
    Nat.card (nsmulAddMonoidHom (α := ZMod (Nat.totient (p ^ k))) d).range
      = (p ^ (k - 1) * (p - 1)) / Nat.gcd (p ^ (k - 1) * (p - 1)) d := by
  haveI hne : NeZero (p ^ (k - 1) * (p - 1)) := by
    rw [← Nat.totient_prime_pow hp hk]; infer_instance
  rw [Nat.totient_prime_pow hp hk]
  exact image_count (p ^ (k - 1) * (p - 1)) d

/-!
## 4. solution-count-from-solvability  (density_wall_close Stage A) — SUBSUMED

The LaTTe `solution-count-from-solvability` says: *given solvability*
(`∃ j, n ∣ d·j − m`) of the congruence, the solution set of `d·x ≡ m (mod n)`
bijects with `[0, g)`, `g = gcd(d, n)` — i.e. has exactly `g` solutions.

In the finite-cyclic-group (`ZMod n`) setting this is **subsumed by**
`BealDensity.solution_count`, and the *solvability hypothesis is vacuous* for
the count:

* The homogeneous count `|ker(x ↦ d•x)| = gcd(n, d)` (`solution_count`) holds
  unconditionally — the kernel is never empty (it contains `0`), so no
  "solvability" premise is needed.
* For the inhomogeneous congruence `d·x ≡ m`, the solution set is either empty
  (when `gcd(n,d) ∤ m`) or a *coset* of the kernel, hence of the *same*
  cardinality `gcd(n, d)`. The LaTTe theorem's role is precisely to supply the
  "nonempty ⟹ coset" step that turns solvability into the full count; mathlib's
  group-theoretic `solution_count` already delivers the kernel cardinality that
  every nonempty fibre inherits.

So adding a Lean theorem with a `(∃ j, …)` hypothesis returning
`Nat.card … = gcd(n, d)` would be a strictly weaker restatement of
`solution_count`, not new content. We therefore record it as subsumed rather
than introducing a trivial alias.

LaTTe sibling: `src/ai_math/beal/density_wall_close.clj` ::
`solution-count-from-solvability` (subsumed by `BealDensity.solution_count`).
-/

end BealCountingStages
