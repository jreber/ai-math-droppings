import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# Bucket 2 — Eisenstein cube-sum gcd dichotomy (Lean 4 mirror)

Lean 4 port of the project-specific Beal **Eisenstein factorization / gcd
dichotomy** layer of the LaTTe development under `src/ai_math/beal/`.

The cube `a³ + b³` factors as `(a + b)·(a² − ab + b²)`; the second factor is the
norm form of the Eisenstein integers. The arithmetic heart of "Theorem 2" of
`docs/threads/beal/cube-sum-abc-rigorous.md` is the **gcd dichotomy**: for
coprime `a, b`,

  `gcd(a + b, a² − ab + b²) ∈ {1, 3}`.

The LaTTe development proves this in three layers, all reproduced here:
* the *algebraic core* (`cube_sum_gcd.clj`): a common divisor of `a+b` and the
  quadratic factor divides `3b²`, `3a²`, `3ab`, via the identity
  `q + s·(3b − s) = 3b²` with `s = a+b`, `q = a²−ab+b²`;
* the *unconditional headline* (`division_algorithm.clj ::
  eisenstein-gcd-divides-three-unconditional`): for **coprime** `a, b`, any common
  divisor of `s` and `q` divides `3`;
* the *dichotomy* (`eisenstein_gcd_full.clj`): `d ∣ 3 → d = 1 ∨ d = 3`, hence any
  common nat divisor of `s` and `q` is `1` or `3`.

We work over `ℤ` (the LaTTe sources are over `latte-integers`, and integer
subtraction makes `a² − ab + b²` honest — over `ℕ` truncated subtraction would
distort the quadratic factor). `coprime a b` in LaTTe is
`∀ d, d ∣ a ∧ d ∣ b → d ∣ 1`, which is exactly mathlib's `IsCoprime` over `ℤ`
(Bézout form `∃ u v, u·a + v·b = 1`).

House style follows `BealDensity.lean` / `TerrasDensity.lean`: each theorem
carries a doc-comment ending in a `LaTTe sibling: <clj path> :: <name>`
cross-reference, and proofs lean on mathlib lemmas (`ring`, `linear_combination`,
`IsCoprime.pow_left`/`pow_right`, `dvd_add`, `Dvd.Dvd.mul_left`/`mul_right`)
rather than re-deriving arithmetic.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealEisenstein.lean` to typecheck.

Key mathlib lemmas relied on:
* `ring` / `linear_combination` — the Eisenstein algebraic identities.
* `dvd_add`, `Dvd.Dvd.mul_left`, `Dvd.Dvd.mul_right` — divisibility closure.
* `IsCoprime.pow_left`, `IsCoprime.pow_right` — `coprime a b → coprime a² b²`.
* `Int.isUnit_iff`, `Int.isUnit_eq_one_or` — unit analysis (not needed; we use
  `decide`/`interval_cases` for the `d ∣ 3` dichotomy).
-/

namespace BealEisenstein

/-!
## 1. The cube-sum factorization and its algebraic core

Mirrors `cube_sum_gcd.clj`: the factorization `a³ + b³ = (a+b)(a²−ab+b²)` and the
key identity `q + s·(3b − s) = 3b²` (`eisenstein-sum-identity`), from which a
common divisor of `s = a+b` and `q = a²−ab+b²` is shown to divide `3b²`, `3a²`,
`3ab`.
-/

/-- **Cube-sum factorization.**
`a³ + b³ = (a + b)·(a² − a·b + b²)`. This is the Eisenstein factorization that
opens Theorem 2 of `cube-sum-abc-rigorous.md`.

LaTTe sibling: `src/ai_math/beal/cube_sum_gcd.clj` (the factorization underlying
`eisenstein-sum-identity`). -/
theorem cube_sum_factor (a b : ℤ) :
    a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by ring

/-- **Eisenstein sum identity** (`eisenstein-sum-identity`).
`(a² − a·b + b²) + (a + b)·(3·b − (a + b)) = 3·b²`.

This is the arithmetic pivot: it expresses `3b²` as `q` plus a multiple of the
linear factor `s = a + b`, so any divisor of both `s` and `q` divides `3b²`.

LaTTe sibling: `src/ai_math/beal/cube_sum_gcd.clj` :: `eisenstein-sum-identity`. -/
theorem eisenstein_sum_identity (a b : ℤ) :
    (a ^ 2 - a * b + b ^ 2) + (a + b) * (3 * b - (a + b)) = 3 * b ^ 2 := by ring

/-- **`q` is symmetric** (`q-symmetric`).
`(b² − b·a + a²) = (a² − a·b + b²)`: the Eisenstein quadratic is symmetric in its
two arguments.

LaTTe sibling: `src/ai_math/beal/cube_sum_gcd.clj` :: `q-symmetric`. -/
theorem q_symmetric (a b : ℤ) :
    (b ^ 2 - b * a + a ^ 2) = (a ^ 2 - a * b + b ^ 2) := by ring

/-- **Common divisor of `s, q` divides `3b²`** (`divides-eisenstein-to-3bsq`).
If `d ∣ (a + b)` and `d ∣ (a² − a·b + b²)`, then `d ∣ 3·b²`.

LaTTe sibling: `src/ai_math/beal/cube_sum_gcd.clj` :: `divides-eisenstein-to-3bsq`. -/
theorem divides_eisenstein_to_3bsq (a b d : ℤ)
    (hs : d ∣ a + b) (hq : d ∣ a ^ 2 - a * b + b ^ 2) : d ∣ 3 * b ^ 2 := by
  -- 3b² = q + (a+b)·(3b − (a+b)); divisor of both summands divides the sum.
  rw [← eisenstein_sum_identity a b]
  exact dvd_add hq (hs.mul_right _)

/-- **Common divisor of `s, q` divides `3a²`** (`divides-eisenstein-to-3asq`).
If `d ∣ (a + b)` and `d ∣ (a² − a·b + b²)`, then `d ∣ 3·a²`.

Proved by symmetry: `d ∣ (b + a)` and `d ∣ q(b, a)` via `q_symmetric`, then apply
`divides_eisenstein_to_3bsq` with `a, b` swapped.

LaTTe sibling: `src/ai_math/beal/cube_sum_gcd.clj` :: `divides-eisenstein-to-3asq`. -/
theorem divides_eisenstein_to_3asq (a b d : ℤ)
    (hs : d ∣ a + b) (hq : d ∣ a ^ 2 - a * b + b ^ 2) : d ∣ 3 * a ^ 2 := by
  have hs' : d ∣ b + a := by rwa [add_comm] at hs
  have hq' : d ∣ b ^ 2 - b * a + a ^ 2 := by rwa [q_symmetric a b]
  simpa using divides_eisenstein_to_3bsq b a d hs' hq'

/-- **Common divisor of `s, q` divides `3a·b`** (`divides-eisenstein-to-3ab`).
If `d ∣ (a + b)` and `d ∣ (a² − a·b + b²)`, then `d ∣ 3·(a·b)`.

LaTTe sibling: `src/ai_math/beal/cube_sum_gcd.clj` :: `divides-eisenstein-to-3ab`. -/
theorem divides_eisenstein_to_3ab (a b d : ℤ)
    (hs : d ∣ a + b) (hq : d ∣ a ^ 2 - a * b + b ^ 2) : d ∣ 3 * (a * b) := by
  -- d ∣ (a+b)·(3b) = 3ab + 3b², and d ∣ 3b², so d ∣ the difference 3ab.
  have h3bsq : d ∣ 3 * b ^ 2 := divides_eisenstein_to_3bsq a b d hs hq
  have hprod : d ∣ (a + b) * (3 * b) := hs.mul_right _
  have hkey : (3 : ℤ) * (a * b) = (a + b) * (3 * b) - 3 * b ^ 2 := by ring
  rw [hkey]
  exact dvd_sub hprod h3bsq

/-!
## 2. Unconditional headline — coprime divisor divides 3

Mirrors `division_algorithm.clj :: eisenstein-gcd-divides-three-unconditional`:
for **coprime** `a, b`, any common divisor of `s = a+b` and `q = a²−ab+b²`
divides `3`.

The LaTTe proof goes through Bézout: from `coprime(a,b)` get `coprime(a²,b²)`,
i.e. `∃ u v, u·a² + v·b² = 1`; multiply by `3` to write `3 = u·(3a²) + v·(3b²)`,
and both `3a²`, `3b²` are divisible by `d`. mathlib's `IsCoprime` *is* the Bézout
form, so this is direct.
-/

/-- **Headline (divides 3)** (`eisenstein-gcd-divides-three-unconditional`).
For coprime `a, b`, any common divisor `d` of `a + b` and `a² − a·b + b²` divides
`3`.

Proof: `IsCoprime a b → IsCoprime a² b²`, giving `u·a² + v·b² = 1`. Scaling by
`3`: `3 = u·(3a²) + v·(3b²)`; `d` divides both `3a²` and `3b²`, hence their
combination `3`.

LaTTe sibling: `src/ai_math/beal/division_algorithm.clj` ::
`eisenstein-gcd-divides-three-unconditional`. -/
theorem eisenstein_gcd_divides_three (a b d : ℤ) (hcop : IsCoprime a b)
    (hs : d ∣ a + b) (hq : d ∣ a ^ 2 - a * b + b ^ 2) : d ∣ 3 := by
  have h3a : d ∣ 3 * a ^ 2 := divides_eisenstein_to_3asq a b d hs hq
  have h3b : d ∣ 3 * b ^ 2 := divides_eisenstein_to_3bsq a b d hs hq
  -- coprime a b → coprime a² b²  (Bézout: u·a² + v·b² = 1).
  have hcop2 : IsCoprime (a ^ 2) (b ^ 2) := (hcop.pow_left).pow_right
  obtain ⟨u, v, huv⟩ := hcop2
  -- Scale Bézout by 3: 3 = (3u)·a² + (3v)·b² = u·(3a²) + v·(3b²).
  have e3 : (3 : ℤ) = u * (3 * a ^ 2) + v * (3 * b ^ 2) := by linear_combination (-3) * huv
  rw [e3]
  exact dvd_add (h3a.mul_left u) (h3b.mul_left v)

/-!
## 3. The `d ∣ 3 → d ∈ {1, 3}` dichotomy and the assembled gcd result

Mirrors `eisenstein_gcd_full.clj`: `divides-three-nat-cases` (a *natural* divisor
of 3 is 1 or 3) and `eisenstein-gcd-one-or-three` (the assembled dichotomy).

In Lean we phrase the divisor as a *nonnegative* integer (the natural-number
case) so that the dichotomy is `{1, 3}` exactly — over all of `ℤ` the divisors of
3 are `±1, ±3`, and the LaTTe statement lives in `nat`.
-/

/-- **Divisors of 3 among nonnegatives** (`divides-three-nat-cases`).
A nonnegative integer `d` with `d ∣ 3` equals `1` or `3` (the cases `0` and the
negative divisors `−1, −3` are excluded by `d ∣ 3 ⇒ d ≠ 0` and `0 ≤ d`).

LaTTe sibling: `src/ai_math/beal/eisenstein_gcd_full.clj` :: `divides-three-nat-cases`. -/
theorem divides_three_nat_cases (d : ℤ) (hd : 0 ≤ d) (hdvd : d ∣ 3) :
    d = 1 ∨ d = 3 := by
  -- d ∣ 3 with d ≥ 0 forces d ≤ 3; finite check.
  have hle : d ≤ 3 := Int.le_of_dvd (by norm_num) hdvd
  interval_cases d <;> simp_all

/-- **Eisenstein gcd dichotomy (HEADLINE)** (`eisenstein-gcd-one-or-three`).
For coprime `a, b`, any **nonnegative** common divisor `d` of `a + b` and
`a² − a·b + b²` is `1` or `3`.

This is the faithful `{1, 3}` dichotomy of Theorem 2 of
`cube-sum-abc-rigorous.md`: combine the unconditional `d ∣ 3` headline with the
`d ∣ 3 → d ∈ {1,3}` case split.

LaTTe sibling: `src/ai_math/beal/eisenstein_gcd_full.clj` :: `eisenstein-gcd-one-or-three`. -/
theorem eisenstein_gcd_one_or_three (a b d : ℤ) (hd : 0 ≤ d)
    (hcop : IsCoprime a b)
    (hs : d ∣ a + b) (hq : d ∣ a ^ 2 - a * b + b ^ 2) :
    d = 1 ∨ d = 3 :=
  divides_three_nat_cases d hd (eisenstein_gcd_divides_three a b d hcop hs hq)

/-- **Eisenstein gcd dichotomy, gcd form (HEADLINE).**
For coprime `a, b`, `Int.gcd (a + b) (a² − a·b + b²) = 1 ∨ = 3`.

This restates `eisenstein_gcd_one_or_three` at `d = gcd(s, q)`, the literal gcd
form `gcd(a+b, a²−ab+b²) ∈ {1, 3}` of Theorem 2. `Int.gcd` returns a `ℕ`, so we
read the dichotomy over `ℕ`.

LaTTe sibling: `src/ai_math/beal/eisenstein_gcd_full.clj` :: `eisenstein-gcd-one-or-three`. -/
theorem eisenstein_gcd_eq_one_or_three (a b : ℤ) (hcop : IsCoprime a b) :
    Int.gcd (a + b) (a ^ 2 - a * b + b ^ 2) = 1 ∨
      Int.gcd (a + b) (a ^ 2 - a * b + b ^ 2) = 3 := by
  set s := a + b
  set q := a ^ 2 - a * b + b ^ 2
  -- The gcd, as an integer, is a nonnegative common divisor of s and q.
  have hgnn : (0 : ℤ) ≤ (Int.gcd s q : ℤ) := Int.natCast_nonneg _
  have hgs : (Int.gcd s q : ℤ) ∣ s := Int.gcd_dvd_left s q
  have hgq : (Int.gcd s q : ℤ) ∣ q := Int.gcd_dvd_right s q
  rcases eisenstein_gcd_one_or_three a b (Int.gcd s q : ℤ) hgnn hcop hgs hgq with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

end BealEisenstein
