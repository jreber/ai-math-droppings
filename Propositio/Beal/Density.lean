import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient

/-!
# Bucket 2 — Beal solution-COUNTING / density results (Lean 4 mirror)

Lean 4 port of the project-specific Beal **counting / density** layer of the
LaTTe development under `src/ai_math/beal/`.

The LaTTe sources phrase each cardinality as an explicit *bijection package*
(totality + surjectivity + injectivity of an indexing map `k ↦ r + k·n'`), the
only way to talk about "how many" in a prover without a finite-cardinality
library. mathlib already has the finite-group machinery (`ZMod`,
`AddMonoidHom.ker`, `Nat.card`, cyclic-group kernel counts), so here every
"the solution set bijects with `[0, g)`" theorem is restated as the *actual
cardinality* it computes — a single `Nat.card … = …` equation. This is the
faithful, Lean-idiomatic content of the LaTTe siblings: the LaTTe bijection
exhibits a set of size `g`; the Lean theorem says that size **is** `g`.

House style follows `TerrasDensity.lean`: each theorem carries a doc-comment
ending in a `LaTTe sibling: <clj path> :: <name>` cross-reference, and proofs
lean on mathlib lemmas rather than re-deriving arithmetic.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealDensity.lean` to typecheck.

Key mathlib lemmas relied on:
* `IsAddCyclic.card_nsmulAddMonoidHom_ker` (additive form of
  `IsCyclic.card_powMonoidHom_ker`, `Mathlib.GroupTheory.SpecificGroups.Cyclic`)
  — `Nat.card (nsmulAddMonoidHom d).ker = (Nat.card G).gcd d` in a finite
  additive cyclic group.
* `IsAddCyclic.card_nsmulAddMonoidHom_range` — companion image count
  `Nat.card G / (Nat.card G).gcd d`.
* `ZMod.card`, `ZMod.instIsAddCyclic`, `ZMod.natCast_val`/`ZMod.natCast_zmod_cast`.
* `Nat.totient_prime_pow`, `Nat.gcd_dvd_left`, `Nat.dvd_gcd`.
-/

namespace BealDensity

open AddMonoidHom

/-!
## 1. Single-variable count

Mirrors `count_solution_set.clj` / `exponent_image_size.clj` /
`exponent_image_count.clj`: the solution set of `d · x = 0` in `ZMod n` has
cardinality `gcd(d, n)`, and the image of `x ↦ d · x` has cardinality
`n / gcd(d, n)`.

We phrase multiplication-by-`d` additively as `nsmulAddMonoidHom d`
(`x ↦ d • x`) so that mathlib's cyclic-group kernel/range counts apply directly.
The connection to the ring statement `(d : ZMod n) * x = 0` is recorded
separately in `mul_eq_nsmul_val` / `solution_count_mul`.
-/

/-- **Kernel count (single variable).**
In `ZMod n` (`n > 0`), the number of `x` with `d • x = 0` is `gcd(n, d)`.

This is the cardinality computed by the LaTTe coset bijection
`count-solution-set` (solutions of `d·j ≡ m (mod n)` biject with `[0, g)`,
`g = gcd(d, n)`): here stated as the literal kernel size.

LaTTe sibling: `src/ai_math/beal/count_solution_set.clj` :: `count-solution-set`. -/
theorem solution_count (n : ℕ) [NeZero n] (d : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := ZMod n) d).ker = Nat.gcd n d := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (G := ZMod n) d
  rwa [Nat.card_eq_fintype_card (α := ZMod n), ZMod.card] at h

/-- **Image count (single variable).**
In `ZMod n` (`n > 0`), the image of `x ↦ d • x` has cardinality
`n / gcd(n, d)`.

This is the exponent-image cardinality of `exponent_image_size.clj`
(`|{k·g : 0 ≤ k < n'}| = n'` with `n' = n / g`): stated as the literal range
size.

LaTTe sibling: `src/ai_math/beal/exponent_image_size.clj` ::
`multiples-in-window-count`. -/
theorem image_count (n : ℕ) [NeZero n] (d : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := ZMod n) d).range = n / Nat.gcd n d := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_range (G := ZMod n) d
  rwa [Nat.card_eq_fintype_card (α := ZMod n), ZMod.card] at h

/-- Bridge: in `ZMod n`, ring-multiplication by `(d : ZMod n)` agrees with the
additive `nsmul` by `d.val`, so `(d : ZMod n) * x = d.val • x`. Lets the
kernel/range counts above be read as counts of ring-multiplication solutions. -/
theorem mul_eq_nsmul_val (n : ℕ) [NeZero n] (d x : ZMod n) : d * x = d.val • x := by
  rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

/-- **Ring form of the single-variable count.**
In `ZMod n` (`n > 0`), the number of `x` with `(d : ZMod n) * x = 0` equals
`gcd(n, d.val)`.

LaTTe sibling: `src/ai_math/beal/count_solution_set.clj` :: `count-solution-set`
(ring/`Z/nZ` reading). -/
theorem solution_count_mul (n : ℕ) [NeZero n] (d : ZMod n) :
    Nat.card {x : ZMod n // d * x = 0} = Nat.gcd n d.val := by
  have hcard : Nat.card {x : ZMod n // d * x = 0}
      = Nat.card (nsmulAddMonoidHom (α := ZMod n) d.val).ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun x => ?_)
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← mul_eq_nsmul_val]
  rw [hcard]
  exact solution_count n d.val

/-!
## 2. Pair count (HEADLINE)

Mirrors `pair_solution_count.clj` (`pair-solution-count`) and the capstone
`density-count-at-phi-pp`: the number of pairs `(a, b) ∈ ZMod n × ZMod n` with
`x · a + y · b = 0` equals `n · gcd(gcd(x, y), n)`.

The LaTTe headline assembles this as a fibered bijection (valid-`a` window of
size `n'` × fibers of size `g_y`). In Lean it is the kernel of the additive
hom `(a, b) ↦ x • a + y • b`, counted by `|domain| / |image|`:

  `|ker| = n² / (n / gcd(gcd(x,y), n)) = n · gcd(gcd(x,y), n)`.
-/

/-- The additive hom `ZMod n × ZMod n →+ ZMod n`, `(a, b) ↦ x • a + y • b`. -/
def pairHom (n : ℕ) (x y : ℕ) : (ZMod n × ZMod n) →+ ZMod n :=
  (nsmulAddMonoidHom (α := ZMod n) x).comp (AddMonoidHom.fst _ _) +
    (nsmulAddMonoidHom (α := ZMod n) y).comp (AddMonoidHom.snd _ _)

@[simp] theorem pairHom_apply (n : ℕ) (x y : ℕ) (p : ZMod n × ZMod n) :
    pairHom n x y p = x • p.1 + y • p.2 := by
  simp [pairHom, nsmulAddMonoidHom_apply]

/-- The image of `pairHom` is the same one-dimensional image as the
single-variable map for `g = gcd(x, y)`: namely `gcd(gcd(x,y), n)` multiples,
so its cardinality is `n / gcd(gcd(x,y), n)`. -/
theorem pairHom_range_count (n : ℕ) [NeZero n] (x y : ℕ) :
    Nat.card (pairHom n x y).range = n / Nat.gcd n (Nat.gcd x y) := by
  -- range (pairHom) = range (nsmulAddMonoidHom (gcd x y)) as additive subgroups.
  have hrange : (pairHom n x y).range = (nsmulAddMonoidHom (α := ZMod n) (Nat.gcd x y)).range := by
    apply le_antisymm
    · -- ⊆ : x•a + y•b is a multiple of gcd x y since gcd x y ∣ x and gcd x y ∣ y.
      rintro _ ⟨⟨a, b⟩, rfl⟩
      simp only [pairHom_apply, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
      obtain ⟨px, hpx⟩ := Nat.gcd_dvd_left x y
      obtain ⟨py, hpy⟩ := Nat.gcd_dvd_right x y
      refine ⟨px • a + py • b, ?_⟩
      rw [smul_add, smul_smul, smul_smul, ← hpx, ← hpy]
    · -- ⊇ : gcd x y • c = x • (u • c) + y • (v • c) via integer Bézout (zsmul).
      rintro _ ⟨c, rfl⟩
      simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, pairHom_apply]
      refine ⟨(Nat.gcdA x y • c, Nat.gcdB x y • c), ?_⟩
      -- Work in zsmul: (gcd x y : ℤ) • c = x • (gcdA • c) + y • (gcdB • c).
      have hz : (Nat.gcd x y : ℤ) • c
          = (x : ℤ) • (Nat.gcdA x y • c) + (y : ℤ) • (Nat.gcdB x y • c) := by
        rw [smul_smul, smul_smul, ← add_smul, ← Nat.gcd_eq_gcd_ab]
      have hxz : (x : ℤ) • (Nat.gcdA x y • c) = (x : ℕ) • (Nat.gcdA x y • c) := by
        rw [natCast_zsmul]
      have hyz : (y : ℤ) • (Nat.gcdB x y • c) = (y : ℕ) • (Nat.gcdB x y • c) := by
        rw [natCast_zsmul]
      have hgz : (Nat.gcd x y : ℤ) • c = (Nat.gcd x y : ℕ) • c := by
        rw [natCast_zsmul]
      rw [← hgz, hz, hxz, hyz]
  rw [hrange]
  exact image_count n (Nat.gcd x y)

/-- **Pair count (HEADLINE).**
In `ZMod n` (`n > 0`), the number of pairs `(a, b)` with `x • a + y • b = 0`
equals `n · gcd(gcd(x, y), n)`.

LaTTe sibling: `src/ai_math/beal/pair_solution_count.clj` ::
`pair-solution-count` (and the capstone `density-count-at-phi-pp` count). -/
theorem pair_solution_count (n : ℕ) [NeZero n] (x y : ℕ) :
    Nat.card (pairHom n x y).ker = n * Nat.gcd n (Nat.gcd x y) := by
  -- Lagrange + first iso: |ker| * |range| = |domain| = n².
  -- `card_mul_index` : Nat.card ker * ker.index = Nat.card domain
  -- `index_ker`      : ker.index = Nat.card range
  have hlag : Nat.card (pairHom n x y).ker * Nat.card (pairHom n x y).range
      = Nat.card (ZMod n × ZMod n) := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  -- Domain cardinality is n².
  have hdom : Nat.card (ZMod n × ZMod n) = n * n := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]
  rw [hdom] at hlag
  -- Range cardinality.
  have hrange : Nat.card (pairHom n x y).range = n / Nat.gcd n (Nat.gcd x y) :=
    pairHom_range_count n x y
  -- gcd n g divides n, and n > 0, so n / (n/g) = g·... solve arithmetically.
  have hg_dvd : Nat.gcd n (Nat.gcd x y) ∣ n := Nat.gcd_dvd_left _ _
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set g := Nat.gcd n (Nat.gcd x y) with hg
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hn_pos
  -- From hlag: |ker| * (n / g) = n * n.  Multiply through: since g ∣ n, n = g * (n/g).
  obtain ⟨q, hq⟩ := hg_dvd          -- n = g * q
  have hnq : n / g = q := by
    rw [hq, Nat.mul_div_cancel_left _ hg_pos]
  rw [hrange, hnq] at hlag
  -- hlag : |ker| * q = n * n.  Want |ker| = n * g.  Note n * n = (n * g) * q since n = g*q.
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [h] at hq; omega
    · exact h
  have : n * n = (n * g) * q := by
    rw [hq]; ring
  rw [this] at hlag
  exact Nat.eq_of_mul_eq_mul_right hqpos hlag

/-!
## 3. `w` is the gcd of `(x, y, n)` (T1)

In Lean this is immediate: `Nat.gcd (Nat.gcd x y) n` is *defined* to be a gcd, so
the common-divisor half is `Nat.gcd_dvd_*` and the maximality half is
`Nat.dvd_gcd`.

LaTTe sibling: `src/ai_math/beal/pair_solution_count.clj` :: `w-is-gcd-xy-n`.
-/

/-- **`w = gcd(x, y, n)` characterization (T1).**
`w := gcd(gcd(x, y), n)` divides each of `x`, `y`, `n` and is divisible by every
common divisor `e` of `x`, `y`, `n`.

LaTTe sibling: `src/ai_math/beal/pair_solution_count.clj` :: `w-is-gcd-xy-n`. -/
theorem w_is_gcd_xy_n (x y n : ℕ) :
    (Nat.gcd (Nat.gcd x y) n ∣ x ∧
      Nat.gcd (Nat.gcd x y) n ∣ y ∧
      Nat.gcd (Nat.gcd x y) n ∣ n) ∧
    (∀ e : ℕ, e ∣ x → e ∣ y → e ∣ n → e ∣ Nat.gcd (Nat.gcd x y) n) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left x y)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right x y)
  · exact Nat.gcd_dvd_right _ _
  · intro e hx hy hn
    exact Nat.dvd_gcd (Nat.dvd_gcd hx hy) hn

/-!
## 4. Local density at `n = totient (p^k)` (T2 CAPSTONE)

Specialize the pair count at `n = Nat.totient (p ^ k)` for `p` prime, `k ≥ 1`,
and rewrite with `Nat.totient_prime_pow`.

LaTTe sibling: `src/ai_math/beal/pair_solution_count.clj` ::
`density-count-at-phi-pp`.
-/

/-- **Local density at `φ(pᵏ)` (T2 CAPSTONE).**
For `p` prime and `k ≥ 1`, with `n = φ(pᵏ) = p^(k-1)·(p-1)`, the number of pairs
`(a, b) ∈ ZMod n × ZMod n` with `x • a + y • b = 0` is

  `φ(pᵏ) · gcd(φ(pᵏ), gcd(x, y))  =  p^(k-1)·(p-1) · gcd(p^(k-1)·(p-1), gcd(x, y))`.

LaTTe sibling: `src/ai_math/beal/pair_solution_count.clj` ::
`density-count-at-phi-pp`. -/
theorem density_count_at_phi_pp
    (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (x y : ℕ)
    [NeZero (Nat.totient (p ^ k))] :
    Nat.card (pairHom (Nat.totient (p ^ k)) x y).ker
      = (p ^ (k - 1) * (p - 1)) * Nat.gcd (p ^ (k - 1) * (p - 1)) (Nat.gcd x y) := by
  haveI hne : NeZero (p ^ (k - 1) * (p - 1)) := by
    rw [← Nat.totient_prime_pow hp hk]; infer_instance
  rw [Nat.totient_prime_pow hp hk]
  exact pair_solution_count (p ^ (k - 1) * (p - 1)) x y

end BealDensity
