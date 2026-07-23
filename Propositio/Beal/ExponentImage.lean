import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.Int.Basic

/-!
# Bucket 2 — Beal exponent-image / minus-one / Euler-φ-of-prime-power results

Lean 4 port of the project-specific Beal **exponent-image containment**,
**−1-in-exponent-image**, and **Euler-φ-of-a-prime-power** layers of the LaTTe
development under `src/ai_math/beal/`.

## Modelling notes (faithfulness)

The LaTTe sources work over the integers (`latte-integers.int`) and phrase
"`m` is in the exponent-image of `x`" — i.e. `m ∈ H_x`, the image of
`j ↦ x · j` on `Z/nZ` — as the *solvability of a linear congruence*:

    m ∈ H_x   ⟺   ∃ j, n ∣ (x · j − m).

This file mirrors that **literally** over `ℤ`: every theorem keeps the exact
hypothesis list of its LaTTe sibling, including the explicit Bezout
certificates `u·x + v·n = g` and the gcd-divisor certificates `g ∣ x`, `g ∣ n`
that the LaTTe development carries (LaTTe has no `Int.gcd` rewriting machinery,
so it threads gcds as abstract divisors with a Bezout witness; we keep that
shape rather than silently swapping in `Int.gcd`, so the statements match
one-for-one).

For the Euler-φ layer the LaTTe definition is the *parameterised* prime power
`phi-pp pk1 p = pk1 · (p − 1)` with `pk1 = p^(k−1)` supplied by the caller.
We mirror that `phi_pp` definition over `ℤ` faithfully (so the four LaTTe
theorems transfer verbatim), and *additionally* connect it to mathlib's genuine
`Nat.totient` via `Nat.totient_prime_pow`, which is the mathematical content the
parameterised definition stands in for.

House style follows `BealDensity.lean` / `TerrasDensity.lean`: each theorem
carries a doc-comment ending in `LaTTe sibling: <clj path> :: <name>`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17).
Typecheck with `lake env lean BealExponentImage.lean`.

Key mathlib lemmas relied on:
* `dvd_trans`, `Dvd.dvd.mul_right`, `dvd_sub`, `dvd_add` (ℤ divisibility).
* `Int.emod_emod_of_dvd`, basic ring lemmas via `ring`/`linarith`/`omega`.
* `Nat.totient_prime_pow`, `Nat.totient_pos`, `Nat.totient_even`.
-/

namespace BealExponentImage

open scoped Classical

-- Several theorems carry the *full* LaTTe hypothesis list (gcd-divisor and
-- Bezout certificates) for one-for-one faithfulness even when a particular
-- proof route does not consume every certificate; silence the resulting
-- unused-variable lint rather than weaken the statements.
set_option linter.unusedVariables false

/-! ## L3a — exponent-image containment ↔ gcd divisibility

The exponent-image of `x` (the image of `j ↦ x·j` on `Z/nZ`) is, in the LaTTe
encoding, the set `{ m : ∃ j, n ∣ (x·j − m) }`.  Containment of these images is
governed by divisibility of the gcds.  We thread the gcds as abstract divisors
carrying Bezout certificates, exactly as the LaTTe sources do. -/

/-- **Bezout-self-hit** (helper, T2).

Given a Bezout identity `u·x + v·n = g`, the value `g` lies in the
exponent-image of `x`: concretely `n ∣ (x·u − g)`, with witness `j = u`.

Arithmetic: `x·u − g = x·u − (u·x + v·n) = −(v·n) = n·(−v)`.

LaTTe sibling: `src/ai_math/beal/exponent_image_containment.clj` ::
`bezout-self-hit`. -/
theorem bezout_self_hit (x n g u v : ℤ) (hbez : u * x + v * n = g) :
    n ∣ (x * u - g) := by
  refine ⟨-v, ?_⟩
  rw [← hbez]; ring

/-- **Forward containment** (T1, L3a).

If `gcd(y,n) ∣ gcd(x,n)` (threaded as `g_y ∣ g_x` together with the divisor /
Bezout certificates that pin `g_x`, `g_y` down as the respective gcds), then the
exponent-image of `x` is contained in the exponent-image of `y`:

    (∃ j, n ∣ x·j − m)  →  (∃ j, n ∣ y·j − m).

Chain: `m ∈ H_x ⟹ g_x ∣ m` (since `g_x ∣ x` and `g_x ∣ n`); then
`g_y ∣ g_x ∣ m`; then a Bezout cert for `(y,n)` reconstructs a `j` with
`n ∣ y·j − m`.

LaTTe sibling: `src/ai_math/beal/exponent_image_containment.clj` ::
`exponent-image-containment-forward`. -/
theorem exponent_image_containment_forward
    (x y n m g_x u_x v_x g_y u_y v_y : ℤ)
    (hgx_d : g_x ∣ x) (hgx_n : g_x ∣ n)
    (hgy_d : g_y ∣ y) (hgy_n : g_y ∣ n)
    (hbez_y : u_y * y + v_y * n = g_y)
    (hgyx : g_y ∣ g_x) :
    (∃ j : ℤ, n ∣ (x * j - m)) → (∃ j : ℤ, n ∣ (y * j - m)) := by
  rintro ⟨j, hj⟩
  -- Step 1: g_x ∣ m.  From g_x ∣ n ∣ (x·j − m) and g_x ∣ x·j we get g_x ∣ m.
  have hgx_xj : g_x ∣ x * j := hgx_d.mul_right j
  have hgx_diff : g_x ∣ (x * j - m) := dvd_trans hgx_n hj
  have hgx_m : g_x ∣ m := by
    have := dvd_sub hgx_xj hgx_diff
    simpa using this
  -- Step 2: g_y ∣ m (transitivity g_y ∣ g_x ∣ m).
  have hgy_m : g_y ∣ m := dvd_trans hgyx hgx_m
  -- Step 3: reconstruct j' with n ∣ y·j' − m using the Bezout cert for (y,n).
  -- m = g_y · t, and y·(u_y·t) − m = t·(u_y·y − g_y) = t·(−v_y·n) = n·(−t·v_y).
  obtain ⟨t, ht⟩ := hgy_m
  refine ⟨u_y * t, -t * v_y, ?_⟩
  have : u_y * y = g_y - v_y * n := by linarith [hbez_y]
  rw [ht]
  -- goal: y * (u_y * t) - g_y * t = n * (-t * v_y)
  have hyt : y * (u_y * t) = (u_y * y) * t := by ring
  rw [hyt, this]; ring

/-- **Backward containment** (T3, L3a).

Conversely, if the exponent-image of `x` is contained in that of `y` — it
suffices to know `g_x` itself is carried over, i.e.
`(∃ j, n ∣ x·j − g_x) → (∃ j, n ∣ y·j − g_x)` — then `g_y ∣ g_x`.

Chain: `bezout_self_hit` puts `g_x ∈ H_x`; containment puts `g_x ∈ H_y`;
and `g_x ∈ H_y` forces `g_y ∣ g_x` (since `g_y ∣ y` and `g_y ∣ n`).

LaTTe sibling: `src/ai_math/beal/exponent_image_containment.clj` ::
`exponent-image-containment-backward`. -/
theorem exponent_image_containment_backward
    (x y n g_x u_x v_x g_y u_y v_y : ℤ)
    (hgy_d : g_y ∣ y) (hgy_n : g_y ∣ n)
    (hbez_x : u_x * x + v_x * n = g_x)
    (containment : (∃ j : ℤ, n ∣ (x * j - g_x)) → (∃ j : ℤ, n ∣ (y * j - g_x))) :
    g_y ∣ g_x := by
  -- g_x ∈ H_x via bezout-self-hit (witness j = u_x).
  have hx_hit : ∃ j : ℤ, n ∣ (x * j - g_x) := ⟨u_x, bezout_self_hit x n g_x u_x v_x hbez_x⟩
  -- containment ⟹ g_x ∈ H_y.
  obtain ⟨j, hj⟩ := containment hx_hit
  -- g_y ∣ y·j and g_y ∣ n ∣ (y·j − g_x) ⟹ g_y ∣ g_x.
  have hgy_yj : g_y ∣ y * j := hgy_d.mul_right j
  have hgy_diff : g_y ∣ (y * j - g_x) := dvd_trans hgy_n hj
  have := dvd_sub hgy_yj hgy_diff
  simpa using this

/-! ## L2 — `−1` is in the exponent-image of an odd `x`

Working at `n = φ(p^k)` for an odd prime `p`, `n` is even; write `n = 2·h`.
The residue representing `−1` is `h = n/2`.  For odd `x`, `g = gcd(x,n)` is odd,
hence coprime to `2`, hence `g ∣ 2h ⟹ g ∣ h`, and a Bezout cert reconstructs a
`j` with `n ∣ x·j − h`.  We mirror the four LaTTe steps. -/

/-- **Divisor of an odd is odd** (T1).

If `d ∣ x` and `x` is odd then `d` is odd.

LaTTe sibling: `src/ai_math/beal/minus_one_exponent.clj` ::
`divisor-of-odd-is-odd`. -/
theorem divisor_of_odd_is_odd (d x : ℤ) (hdiv : d ∣ x) (hodd : Odd x) : Odd d := by
  rcases Int.even_or_odd d with he | ho
  · exfalso
    have : Even x := hdiv.even he
    exact (Int.not_even_iff_odd.2 hodd) this
  · exact ho

/-- **Odd ⟹ coprime to 2** (T2).

If `d` is odd then `gcd(d, 2) = 1`.

LaTTe sibling: `src/ai_math/beal/minus_one_exponent.clj` :: `odd-coprime-two`. -/
theorem odd_coprime_two (d : ℤ) (hodd : Odd d) : IsCoprime d (2 : ℤ) := by
  obtain ⟨k, hk⟩ := hodd
  -- d = 2k + 1, so 1·d + (−k)·2 = 1.
  exact ⟨1, -k, by rw [hk]; ring⟩

/-- **Odd gcd divides the half** (T3).

If `x` is odd, `g ∣ x`, and `g ∣ 2·h`, then `g ∣ h`.

LaTTe sibling: `src/ai_math/beal/minus_one_exponent.clj` ::
`odd-gcd-divides-half`. -/
theorem odd_gcd_divides_half (x g h : ℤ) (hodd : Odd x) (hgx : g ∣ x)
    (hg2h : g ∣ 2 * h) : g ∣ h := by
  have hg_odd : Odd g := divisor_of_odd_is_odd g x hgx hodd
  have hcop : IsCoprime g (2 : ℤ) := odd_coprime_two g hg_odd
  -- coprime g 2 ⟹ (g ∣ 2*h ⟹ g ∣ h)
  exact hcop.dvd_of_dvd_mul_left hg2h

/-- **−1 in the exponent-image** (T4, headline L2).

For odd `x` with `g ∣ x`, `g ∣ 2·h` (= `n` for `n = 2h`), and a Bezout cert
`u·x + v·n = g`, the residue `h = n/2` (representing `−1`) lies in the
exponent-image of `x`:  `∃ j, n ∣ (x·j − h)`.

Chain: `odd_gcd_divides_half` gives `g ∣ h`; a Bezout cert for `(x,n)` then
reconstructs the witness exactly as in `bezout_self_hit`, scaled by `m/g`.

LaTTe sibling: `src/ai_math/beal/minus_one_exponent.clj` ::
`minus-one-in-exponent-image`. -/
theorem minus_one_in_exponent_image (x g h n u v : ℤ)
    (hn : n = 2 * h) (hodd : Odd x) (hgx : g ∣ x) (hg2h : g ∣ 2 * h)
    (hbez : u * x + v * n = g) :
    ∃ j : ℤ, n ∣ (x * j - h) := by
  -- g ∣ h.
  have hgh : g ∣ h := odd_gcd_divides_half x g h hodd hgx hg2h
  obtain ⟨t, ht⟩ := hgh
  -- h = g·t; witness j = u·t (same algebra as bezout_self_hit, scaled by t).
  refine ⟨u * t, -t * v, ?_⟩
  have hux : u * x = g - v * n := by linarith [hbez]
  rw [ht]
  have hxt : x * (u * t) = (u * x) * t := by ring
  rw [hxt, hux]; ring

/-! ## Euler-φ of a prime power

Faithful mirror of the parameterised LaTTe definition `phi-pp pk1 p = pk1·(p−1)`
over `ℤ`, with its four theorems; plus the connection to mathlib's
`Nat.totient`. -/

/-- The parameterised Euler-φ of a prime power, `phi_pp pk1 p = pk1 · (p − 1)`,
where `pk1 = p^(k−1)` is supplied by the caller (mirrors the LaTTe `phi-pp`).

LaTTe sibling: `src/ai_math/beal/euler_phi_pp.clj` :: `phi-pp`. -/
def phi_pp (pk1 p : ℤ) : ℤ := pk1 * (p - 1)

/-- **(p−1) ∣ φ(p^k)** (T3).

LaTTe sibling: `src/ai_math/beal/euler_phi_pp.clj` ::
`phi-pp-p-minus-one-divides`. -/
theorem phi_pp_p_minus_one_divides (pk1 p : ℤ) : (p - 1) ∣ phi_pp pk1 p :=
  ⟨pk1, by rw [phi_pp]; ring⟩

/-- **φ(p^k) is a natural** (T4).

Over `ℤ` the LaTTe `nat`-membership claim becomes nonnegativity: if `0 ≤ pk1`
and `0 ≤ p − 1` then `0 ≤ phi_pp pk1 p`.

LaTTe sibling: `src/ai_math/beal/euler_phi_pp.clj` :: `phi-pp-nat`. -/
theorem phi_pp_nat (pk1 p : ℤ) (hpk1 : 0 ≤ pk1) (hpm1 : 0 ≤ p - 1) :
    0 ≤ phi_pp pk1 p :=
  mul_nonneg hpk1 hpm1

/-- **φ(p^k) > 0** (T1).

If `0 < pk1` and `1 < p` then `0 < phi_pp pk1 p`.

LaTTe sibling: `src/ai_math/beal/euler_phi_pp.clj` :: `phi-pp-pos`. -/
theorem phi_pp_pos (pk1 p : ℤ) (hpk1 : 0 < pk1) (hp : 1 < p) :
    0 < phi_pp pk1 p :=
  mul_pos hpk1 (by linarith)

/-- **2 ∣ φ(p^k) for odd p** (T2).

If `p` is odd then `2 ∣ phi_pp pk1 p` (φ of an odd prime power is even).

LaTTe sibling: `src/ai_math/beal/euler_phi_pp.clj` :: `phi-pp-even`. -/
theorem phi_pp_even (pk1 p : ℤ) (hodd : Odd p) : (2 : ℤ) ∣ phi_pp pk1 p := by
  obtain ⟨k, hk⟩ := hodd
  -- p - 1 = 2k, so phi_pp pk1 p = pk1·(2k) = 2·(pk1·k).
  refine ⟨pk1 * k, ?_⟩
  rw [phi_pp, hk]; ring

/-! ### Connection to mathlib `Nat.totient`

The parameterised `phi_pp` stands in for the genuine Euler totient of a prime
power.  These lemmas certify that the standing-in is faithful: mathlib's
`Nat.totient (p^k)` is exactly `p^(k-1)·(p-1)`, is positive, and (for an odd
prime power with `p^k > 2`) is even — the `ℕ`-truth behind the three `phi_pp`
facts above. -/

/-- `Nat.totient (p^k) = p^(k-1)·(p-1)` for a prime `p` and `0 < k` — mathlib's
genuine totient agrees with the `phi_pp` parameterisation (with `pk1 = p^(k-1)`).

LaTTe sibling: the definitional content standing behind
`src/ai_math/beal/euler_phi_pp.clj` :: `phi-pp`. -/
theorem totient_prime_pow_eq_phi_pp {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

/-- mathlib totient of a prime power is positive (companion to `phi_pp_pos`). -/
theorem totient_prime_pow_pos {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    0 < Nat.totient (p ^ k) := by
  rw [Nat.totient_pos]
  exact pow_pos hp.pos k

/-- mathlib totient of an odd prime power `> 2` is even (companion to
`phi_pp_even`). -/
theorem totient_prime_pow_even {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hgt : 2 < p ^ k) : Even (Nat.totient (p ^ k)) :=
  Nat.totient_even hgt

end BealExponentImage
