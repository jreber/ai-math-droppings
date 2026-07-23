/-
Zsygmondy exceptional-case endgame — general-`b` port.

## Task

Per `docs/kb/frontier/_meta.json`'s `_goal_zsygmondy_OPEN_2026_07_05` note (2026-07-10
addendum): the full general-`b` Zsygmondy theorem (coprime `a > b ≥ 1`) now has every
layer ported EXCEPT the exceptional-case endgame — the `a = b + 1` (consecutive integers)
self-bound margin argument that `ZsygmondyBaseTwoEndgame` closed for the special case
`b = 1, a = 2`, needed here for every `b`, not just `b = 1`.

## What THIS FILE proves (real, sorry-free, 10 theorems, axiom-clean
`[propext, Classical.choice, Quot.sound]`)

### Layer 1 — the gearbox, generalized to `Phi n a b`

The two "gearbox" identities that are the mechanical engine of the
`ZsygmondyBaseTwoEndgame` technique — `Φ_n(2) = Φ_{n/p}(2^p)` (exact, when `p² ∣ n`) and
`Φ_q(2^p) = Φ_{qp}(2) · Φ_q(2)` (exact, when `p ∤ q`) — generalized from the univariate
`Φ_n(a) := (cyclotomic n ℤ).eval a` to the homogeneous bivariate
`Phi n a b := ZsygmondyHomogeneousCyclotomicFactor.Phi n a b`:

  * `Phi_expand_eq_of_dvd`: for prime `p`, `p ∣ n'`, `n = n' * p`:
    `Phi n a b = Phi n' (a ^ p) (b ^ p)`.
  * `Phi_expand_eval_eq_mul_of_not_dvd`: for prime `p`, `p ∤ q`:
    `Phi (q * p) a b * Phi q a b = Phi q (a ^ p) (b ^ p)`.

both proved via `Phi_eq_cyclotomic_eval_div_real`, the `K := ℝ` instantiation of the same
`Semifield`-section `Polynomial.eval_homogenize` bridge already validated (at `K := ZMod p`)
in `ZsygmondyPhiOrderBridge` — the "port via division" claim from the 2026-07-09 scoping
note is now hand-verified for an integer-EQUALITY use, not just a ZMod-divisibility one.

### Layer 2 — the height sandwich, generalized to `Phi n a b`

  * `Phi_totient_lower_bound`: `(a - b) ^ φ(n) < Phi n a b`, for `n ≥ 2`, `a > b ≥ 1`.
  * `Phi_totient_upper_bound`: `Phi n a b ≤ (a + b) ^ φ(n)`, for `a > b ≥ 1`.

### Layer 3 — the `k ≥ 2` case, CLOSED for every `b ≥ 1`

  * `no_k_ge_two_general`: for `a = b + 1` (`b ≥ 1`), `n ≥ 2`, `p` prime with `p² ∣ n`:
    `Phi n a b = p` is impossible. This is the exact, complete generalization of
    `ZsygmondyBaseTwoEndgame.no_k_ge_two` to every `b`, via the numeric margin
    `pow_sub_pow_ge_of_succ` (`a^p - b^p ≥ p`, proved by a subtraction-free binomial-margin
    induction, `pow_add_le_succ_pow`) — no `b`-dependence enters this branch at all.

### Layer 4 — the `k = 1` case for `b ≥ 2`, CLOSED, and MORE CHEAPLY than `b = 1`

This is the key finding of the session. The `b = 1` file's `k = 1` margin
(`p_le_four_of_k_eq_one`, needing `p ≥ 5 ⟹ 3p < 2^p` and then a residual case-by-case pin
to `p = 3, n = 6`) does NOT generalize by substitution — but a DIFFERENT, uniform, and in
fact *simpler* argument closes the `k = 1` case completely for every `b ≥ 2`, with no
residual case split at all:

  * `margin_ge_two`: for `b ≥ 2`, `p ≥ 3`: `(2b + 1) · p < (b + 1)^p - b^p`, proved by
    induction on `p` from the EXACT recursion `D(p+1) = (b+1)·D(p) + b^p` (`D_succ_eq`,
    `D(p) := (b+1)^p - b^p`) — uniform in `p ≥ 3`, unlike `b = 1`'s `p ≥ 5` threshold.
  * `k_eq_one_impossible_of_b_ge_two`: for `b ≥ 2`, `q > 1`, `p` prime with `p ∤ q`,
    `p ≥ 3`: `Phi (q*p) (b+1) b = p` is impossible — reached DIRECTLY (no `p ≤ 4` /
    congruence-pin / `n = 6` finite check needed) by combining `margin_ge_two` with the
    height sandwich and `Phi_expand_eval_eq_mul_of_not_dvd`, then canceling the common
    `(a+b)^φ(q)` factor to force `p^φ(q) < p`, impossible since `φ(q) ≥ 1`.

Numerically confirmed (via `decide`, see the git history of this file) that `b = 1` is the
UNIQUE value where the `k = 1` margin fails at the smallest odd prime `p = 3`
(`9 < 7` is false — exactly the `n = 6` exception `(n,a,b) = (6,2,1)`), while already at
`b = 2` the margin holds at `p = 3` (`15 < 19`). Combined with Layer 3 (`b`-independent),
this means: for every `b ≥ 2`, BOTH branches of the "is `n` a non-prime-power with
intrinsic order decomposition `n = e·p^k`" case split are now proved impossible — i.e. this
file's results are consistent with, and give independent structural evidence for, the
classical fact that `(n,a,b) = (6,2,1)` is the ONLY sporadic exception across the entire
`b ≥ 1` family (no analogous exception exists for any `b ≥ 2`).

## What is NOT closed here — the precise remaining assembly gap

The two case-elimination theorems above (Layers 3–4) are the mathematical HEART of the
endgame, but assembling them into the full closed statement `∀ n ≥ 2, n ≠ 6 ∨ b ≠ 1 → Phi n
(b+1) b` has a primitive prime divisor" needs several further general-`b` ports NOT
attempted in this file (each individually looks mechanical given the `ZsygmondyPhiOrderBridge`
pattern already validated twice over in this file, but none is done):

  1. **`Phi`-existence entry point**: the general-`b` analogue of
     `ZsygmondyPrimitiveExists.primitive_prime_exists_of_not_isPrimePow` (currently phrased
     for `(cyclotomic n ℤ).eval a`, i.e. `b = 1` only) — needed to even REACH the "`Phi n a b`
     is a prime power `p^t`" hypothesis that Layers 3–4 assume.
  2. **LTE for `Phi`**: the general-`b` analogue of `padicValInt_cyclotomic_intrinsic_le_one`
     (odd `p`) — needed to pin `t = 1` exactly (i.e. `Phi n a b = p`, not just `p^t`).
     `ZsygmondyOddPrimeLTE.lte_odd_prime` is ALREADY stated for general `a, b` (confirmed by
     grep), so this should be a direct application, not new LTE content — but the assembly
     into a `padicValInt`-of-`Phi` bound was not done here.
  3. **The `n` prime-power case**: the general-`b` analogue of
     `ZsygmondyBaseTwo.cyclotomic_eval_two_gt_of_isPrimePow` (`Φ_n(2) > n` for prime-power
     `n`) — needed for the `e = 1` branch of the intrinsic decomposition (this file only
     handles the `e ≥ 2` branches, `k ≥ 2` and `k = 1`).
  4. **The `p = 2` branch for even `b`**: for `b = 1` (`a = 2` even), `p = 2` is
     automatically excluded (`p ∣ a` would force `p = 2`, but `not_dvd_base` gives `p ∤ a`).
     For general `b`, `a = b + 1` is EVEN iff `b` is ODD — so this shortcut only survives
     for odd `b`. For EVEN `b` (`a` odd), `p = 2` is a live case requiring the general
     even-prime LTE machinery (`ZsygmondyEvenPrime.padicValInt_cyclotomic_intrinsic_two_le`)
     ported to `Phi n a b`, which this file does not attempt. This is flagged as the most
     likely genuinely-new (non-mechanical) remaining piece, since `ZsygmondyEvenPrime`'s own
     proof is the most involved of the LTE files.
  5. The `intrinsic_order_dvd_general` decomposition (`n = e · p^k`, `e = ord_p(a·b⁻¹)`,
     `p ∤ e`) ALREADY EXISTS in `ZsygmondyIntrinsicFactorGeneral` — this piece is done.

Items 1–3 are plausibly short (each is a direct transplant of an existing `b = 1` proof
through the `Phi_eq_cyclotomic_eval_div_real` bridge, exactly as Layers 1–2 of this file
were). Item 4 (`p = 2`, even `b`) is flagged as the one piece most likely to need genuinely
new work, not just transplant, mirroring the difficulty gradient already observed between
`ZsygmondyBaseTwoEndgame` (odd `p` only, easier) and `ZsygmondyEvenPrime` (the `p = 2` LTE,
harder) in the `b = 1` corpus.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHomogeneousCyclotomicFactor
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Nat.Totient

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

namespace ZsygmondyExceptionalEndgameGeneral

/-! ### The real-valued division bridge for `Phi n a b`

This is the `K := ℝ` instantiation of exactly the same `Semifield`-section
`Polynomial.eval_homogenize` bridge already used (at `K := ZMod p`) in
`ZsygmondyPhiOrderBridge.dvd_Phi_iff_isRoot_cyclotomic`. -/

/-- Naturality of bivariate `MvPolynomial.eval` under `Int.cast` into any commutative ring
`S` — the same helper as `ZsygmondyPhiOrderBridge.eval_intCast_eq_eval_map`, restated here
so this file does not need to import that (private) lemma. -/
private theorem eval_intCast_eq_eval_map {S : Type*} [CommRing S]
    (x : Fin 2 → ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    ((MvPolynomial.eval x P : ℤ) : S) =
      MvPolynomial.eval (fun i => ((x i : ℤ) : S)) (MvPolynomial.map (Int.castRingHom S) P) := by
  have h : (Int.castRingHom S) (MvPolynomial.eval x P) =
      MvPolynomial.eval ((Int.castRingHom S) ∘ x) (MvPolynomial.map (Int.castRingHom S) P) := by
    rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
  simpa using h

/-- The cast of `Phi n a b` into `ℝ` equals the bivariate evaluation of the real
cyclotomic homogenization at `(a, b)`. -/
private theorem Phi_castR (n : ℕ) (a b : ℤ) :
    ((Phi n a b : ℤ) : ℝ) =
      MvPolynomial.eval ![(a : ℝ), (b : ℝ)]
        (((cyclotomic n ℤ).map (Int.castRingHom ℝ)).homogenize
          (cyclotomic n ℤ).natDegree) := by
  unfold Phi
  rw [eval_intCast_eq_eval_map (![a, b] : Fin 2 → ℤ)
    ((cyclotomic n ℤ).homogenize (cyclotomic n ℤ).natDegree),
    Polynomial.homogenize_map]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp

/-- **The real division bridge.** For `b ≠ 0`, `Phi n a b` (cast to `ℝ`) equals
`(cyclotomic n ℝ).eval (a / b) * b ^ φ(n)`. -/
theorem Phi_eq_cyclotomic_eval_div_real (n : ℕ) (a b : ℤ) (hb : b ≠ 0) :
    ((Phi n a b : ℤ) : ℝ) =
      (cyclotomic n ℝ).eval ((a : ℝ) / (b : ℝ)) * (b : ℝ) ^ Nat.totient n := by
  have hb0 : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hmapcyc : (cyclotomic n ℤ).map (Int.castRingHom ℝ) = cyclotomic n ℝ :=
    map_cyclotomic_int n ℝ
  have hdeg : (cyclotomic n ℝ).natDegree = (cyclotomic n ℤ).natDegree := by
    rw [← hmapcyc]
    exact (Polynomial.cyclotomic.monic n ℤ).natDegree_map (Int.castRingHom ℝ)
  rw [Phi_castR n a b, hmapcyc]
  have heval := Polynomial.eval_homogenize (K := ℝ) (p := cyclotomic n ℝ)
    (n := (cyclotomic n ℤ).natDegree) (le_of_eq hdeg)
    (![(a : ℝ), (b : ℝ)] : Fin 2 → ℝ) (by simpa using hb0)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  rw [heval]
  have htot : (cyclotomic n ℤ).natDegree = Nat.totient n := natDegree_cyclotomic n ℤ
  rw [htot]

/-! ### The two "gearbox" expand identities, generalized to `Phi n a b` -/

/-- **Expand identity, `p ∣ n'` case.** The bivariate generalization of
`ZsygmondyBaseTwoEndgame`'s use of `cyclotomic_expand_eq_cyclotomic`: for prime `p`,
`p ∣ n'`, `n := n' * p`: `Phi n a b = Phi n' (a ^ p) (b ^ p)` — an EXACT integer identity
(not merely a real-valued one), obtained by proving the real-cast versions agree (via the
division bridge above) and using injectivity of `ℤ → ℝ`. -/
theorem Phi_expand_eq_of_dvd {n' p : ℕ} (hp : p.Prime) (hdvd : p ∣ n') (a b : ℤ) (hb : b ≠ 0) :
    Phi (n' * p) a b = Phi n' (a ^ p) (b ^ p) := by
  have hbp : b ^ p ≠ 0 := pow_ne_zero p hb
  have hL := Phi_eq_cyclotomic_eval_div_real (n' * p) a b hb
  have hR := Phi_eq_cyclotomic_eval_div_real n' (a ^ p) (b ^ p) hbp
  have hexp : expand ℝ p (cyclotomic n' ℝ) = cyclotomic (n' * p) ℝ :=
    cyclotomic_expand_eq_cyclotomic hp hdvd ℝ
  have hevalexp : (cyclotomic n' ℝ).eval (((a : ℝ) / (b : ℝ)) ^ p) =
      (cyclotomic (n' * p) ℝ).eval ((a : ℝ) / (b : ℝ)) := by
    rw [← hexp, expand_eval]
  have hdiv_pow : ((a : ℝ) / (b : ℝ)) ^ p = (a : ℝ) ^ p / (b : ℝ) ^ p := by
    rw [div_pow]
  have htotn : Nat.totient (n' * p) = p * Nat.totient n' := by
    rw [mul_comm n' p]; exact Nat.totient_mul_of_prime_of_dvd hp hdvd
  have hbcast : ((b ^ p : ℤ) : ℝ) = (b : ℝ) ^ p := by push_cast; ring
  have hLR : ((Phi (n' * p) a b : ℤ) : ℝ) = ((Phi n' (a ^ p) (b ^ p) : ℤ) : ℝ) := by
    rw [hL, hR]
    rw [hevalexp.symm, hdiv_pow, htotn]
    rw [show (b:ℝ) ^ (p * Nat.totient n') = ((b:ℝ) ^ p) ^ Nat.totient n' by rw [pow_mul]]
    push_cast
    ring
  exact_mod_cast hLR

/-- **Expand identity, `p ∤ q` case.** The bivariate generalization of
`ZsygmondyBaseTwoEndgame`'s use of `cyclotomic_expand_eq_cyclotomic_mul`: for prime `p`,
`p ∤ q`: `Phi (q * p) a b * Phi q a b = Phi q (a ^ p) (b ^ p)` — an EXACT integer identity.
-/
theorem Phi_expand_eval_eq_mul_of_not_dvd {q p : ℕ} (hp : p.Prime) (hqp : ¬ p ∣ q)
    (a b : ℤ) (hb : b ≠ 0) :
    Phi (q * p) a b * Phi q a b = Phi q (a ^ p) (b ^ p) := by
  have hbp : b ^ p ≠ 0 := pow_ne_zero p hb
  have hL1 := Phi_eq_cyclotomic_eval_div_real (q * p) a b hb
  have hL2 := Phi_eq_cyclotomic_eval_div_real q a b hb
  have hR := Phi_eq_cyclotomic_eval_div_real q (a ^ p) (b ^ p) hbp
  set r : ℝ := (a : ℝ) / (b : ℝ) with hrdef
  have hexp : expand ℝ p (cyclotomic q ℝ) = cyclotomic (q * p) ℝ * cyclotomic q ℝ :=
    cyclotomic_expand_eq_cyclotomic_mul hp hqp ℝ
  have hevalexp : (cyclotomic q ℝ).eval (r ^ p) =
      (cyclotomic (q * p) ℝ).eval r * (cyclotomic q ℝ).eval r := by
    have h := expand_eval p (cyclotomic q ℝ) r
    rw [hexp] at h
    simpa using h.symm
  have hdiv_pow : (a : ℝ) ^ p / (b : ℝ) ^ p = r ^ p := by
    rw [hrdef, div_pow]
  have hcop : q.Coprime p := (hp.coprime_iff_not_dvd.mpr hqp).symm
  have htotqp : Nat.totient (q * p) = Nat.totient q * (p - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]
  have hpow_eq : (b : ℝ) ^ Nat.totient (q * p) * (b : ℝ) ^ Nat.totient q =
      ((b : ℝ) ^ p) ^ Nat.totient q := by
    rw [← pow_add, ← pow_mul]
    congr 1
    rw [htotqp]
    have hp1 : 1 ≤ p := hp.one_le
    have hpe : p - 1 + 1 = p := by omega
    calc Nat.totient q * (p - 1) + Nat.totient q
        = Nat.totient q * (p - 1 + 1) := by ring
      _ = Nat.totient q * p := by rw [hpe]
      _ = p * Nat.totient q := by ring
  have hR' : ((Phi q (a ^ p) (b ^ p) : ℤ) : ℝ) =
      (cyclotomic q ℝ).eval (r ^ p) * ((b : ℝ) ^ p) ^ Nat.totient q := by
    rw [hR]
    have hacast : ((a ^ p : ℤ) : ℝ) = (a : ℝ) ^ p := by push_cast; ring
    have hbcast : ((b ^ p : ℤ) : ℝ) = (b : ℝ) ^ p := by push_cast; ring
    rw [hacast, hbcast, hdiv_pow]
  have hfinal : ((Phi (q * p) a b : ℤ) : ℝ) * ((Phi q a b : ℤ) : ℝ) =
      ((Phi q (a ^ p) (b ^ p) : ℤ) : ℝ) := by
    rw [hL1, hL2, hR', hevalexp, ← hpow_eq]
    ring
  have hL' : ((Phi (q * p) a b : ℤ) : ℝ) * ((Phi q a b : ℤ) : ℝ) =
      ((Phi (q * p) a b * Phi q a b : ℤ) : ℝ) := by push_cast; ring
  rw [hL'] at hfinal
  exact_mod_cast hfinal

/-! ### Height bounds for `Phi n a b`, generalizing `ZsygmondyBaseTwoEndgame`'s
`cyclotomic_eval_totient_lower_bound` / `cyclotomic_eval_totient_upper_bound` from `b = 1`
to general `b`. -/

/-- **Height lower bound, general `b`.** For `n ≥ 2` and integers `a > b ≥ 1`:
`(a - b) ^ φ(n) < Phi n a b`. The bivariate generalization of mathlib's
`Polynomial.sub_one_pow_totient_lt_cyclotomic_eval`, obtained via the division bridge
(evaluate at `q := a / b > 1`, multiply through by `b ^ φ(n)`). -/
theorem Phi_totient_lower_bound {n : ℕ} (hn : 2 ≤ n) {a b : ℤ} (hb : 1 ≤ b) (hab : b < a) :
    (a - b) ^ Nat.totient n < Phi n a b := by
  have hbpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hbne : b ≠ 0 := by omega
  have hq : (1:ℝ) < (a:ℝ) / (b:ℝ) := by
    rw [lt_div_iff₀ hbpos]
    have : (b:ℝ) < (a:ℝ) := by exact_mod_cast hab
    linarith
  have hR := Phi_eq_cyclotomic_eval_div_real n a b hbne
  have hlb : ((a:ℝ)/(b:ℝ) - 1) ^ Nat.totient n < (cyclotomic n ℝ).eval ((a:ℝ)/(b:ℝ)) :=
    sub_one_pow_totient_lt_cyclotomic_eval hn hq
  have hmul : ((a:ℝ)/(b:ℝ) - 1) ^ Nat.totient n * (b:ℝ) ^ Nat.totient n <
      (cyclotomic n ℝ).eval ((a:ℝ)/(b:ℝ)) * (b:ℝ) ^ Nat.totient n := by
    apply mul_lt_mul_of_pos_right hlb
    positivity
  have heq1 : ((a:ℝ)/(b:ℝ) - 1) ^ Nat.totient n * (b:ℝ) ^ Nat.totient n
      = ((a:ℝ) - (b:ℝ)) ^ Nat.totient n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [heq1, ← hR] at hmul
  have hcast : (((a - b) ^ Nat.totient n : ℤ) : ℝ) = ((a:ℝ) - (b:ℝ)) ^ Nat.totient n := by
    push_cast; ring
  rw [← hcast] at hmul
  exact_mod_cast hmul

/-- **Height upper bound, general `b`.** For integers `a, b` with `a ≥ b ≥ 0` and
`a + b ≥ 2` (equivalently `b ≥ 1` suffices given `a > b`, but we only need `b ≥ 1`, `a > 0`):
`Phi n a b ≤ (a + b) ^ φ(n)`. -/
theorem Phi_totient_upper_bound (n : ℕ) {a b : ℤ} (hb : 1 ≤ b) (hab : b < a) :
    Phi n a b ≤ (a + b) ^ Nat.totient n := by
  have hbpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hbne : b ≠ 0 := by omega
  have hq : (1:ℝ) < (a:ℝ) / (b:ℝ) := by
    rw [lt_div_iff₀ hbpos]
    have : (b:ℝ) < (a:ℝ) := by exact_mod_cast hab
    linarith
  have hR := Phi_eq_cyclotomic_eval_div_real n a b hbne
  have hub : (cyclotomic n ℝ).eval ((a:ℝ)/(b:ℝ)) ≤ ((a:ℝ)/(b:ℝ) + 1) ^ Nat.totient n :=
    cyclotomic_eval_le_add_one_pow_totient hq n
  have hmul : (cyclotomic n ℝ).eval ((a:ℝ)/(b:ℝ)) * (b:ℝ) ^ Nat.totient n ≤
      ((a:ℝ)/(b:ℝ) + 1) ^ Nat.totient n * (b:ℝ) ^ Nat.totient n := by
    apply mul_le_mul_of_nonneg_right hub
    positivity
  have heq1 : ((a:ℝ)/(b:ℝ) + 1) ^ Nat.totient n * (b:ℝ) ^ Nat.totient n
      = ((a:ℝ) + (b:ℝ)) ^ Nat.totient n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [heq1, ← hR] at hmul
  have hcast : (((a + b) ^ Nat.totient n : ℤ) : ℝ) = ((a:ℝ) + (b:ℝ)) ^ Nat.totient n := by
    push_cast; ring
  rw [← hcast] at hmul
  exact_mod_cast hmul

/-! ### The `a = b + 1` numeric margin and the `k ≥ 2` elimination step

This is as far as the endgame assembly gets in this session: the ONE numeric margin fact
(`a^p - b^p ≥ p` for `a = b+1`) that is the general-`b` analogue of `2^p - 1 ≥ p`
(`ZsygmondyBaseTwoEndgame`'s `no_k_ge_two` uses `Nat.lt_two_pow_self`), proved directly by
a subtraction-free binomial-margin induction, and its assembly into the general-`b`
analogue of `no_k_ge_two` — the ONE case (`p² ∣ n`) of the case split that generalizes with
NO b-dependence in the numeric threshold (unlike the `k = 1` case; see the file docstring). -/

/-- **Binomial margin, subtraction-free.** For `b ≥ 1` (a real/integer, kept general as `ℤ`
here) and every `p : ℕ`: `b ^ p + p ≤ (b + 1) ^ p`. Proved by induction on `p`; the key step
uses `b ^ p ≥ 1` (since `b ≥ 1`). -/
theorem pow_add_le_succ_pow {b : ℤ} (hb : 1 ≤ b) : ∀ p : ℕ, b ^ p + (p : ℤ) ≤ (b + 1) ^ p := by
  intro p
  induction p with
  | zero => norm_num
  | succ n ih =>
    have hbn1 : (1 : ℤ) ≤ b ^ n := one_le_pow₀ hb
    have hbpos : (0 : ℤ) < b + 1 := by linarith
    have hstep : (b + 1) * (b ^ n + (n : ℤ)) ≤ (b + 1) * (b + 1) ^ n :=
      mul_le_mul_of_nonneg_left ih hbpos.le
    have hexpand : (b + 1) * (b ^ n + (n : ℤ)) = b ^ (n + 1) + b * (n : ℤ) + b ^ n + (n : ℤ) := by
      ring
    have hbnge : (1 : ℤ) ≤ b * (n : ℤ) + b ^ n := by nlinarith [hbn1, Nat.cast_nonneg (α := ℤ) n]
    have hcastsucc : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hexpand] at hstep
    rw [show (b + 1) ^ (n + 1) = (b+1) * (b+1)^n from by rw [pow_succ]; ring] at *
    rw [hcastsucc]
    nlinarith [hstep, hbnge]

/-- **The `a = b + 1` numeric margin.** For `b ≥ 1`, `a = b + 1`, `p : ℕ`:
`(p : ℤ) ≤ a ^ p - b ^ p`. The general-`b` analogue of `2 ^ p - 1 ≥ p` (`a = 2, b = 1`). -/
theorem pow_sub_pow_ge_of_succ {b : ℤ} (hb : 1 ≤ b) (p : ℕ) :
    (p : ℤ) ≤ (b + 1) ^ p - b ^ p := by
  have h := pow_add_le_succ_pow hb p
  linarith

/-- **`k ≥ 2` is impossible, general `b`.** The direct generalization of
`ZsygmondyBaseTwoEndgame.no_k_ge_two`: for `a = b + 1` (`b ≥ 1`), `n ≥ 2`, `p` prime,
`p² ∣ n`: `Phi n a b = p` is impossible. Proved exactly as in the `b = 1` file — write
`n = n' * p` (`p ∣ n'`), apply `Phi_expand_eq_of_dvd` to get the EXACT equality
`Phi n a b = Phi n' (a^p) (b^p)`, sandwich with `Phi_totient_lower_bound` and the numeric
margin `pow_sub_pow_ge_of_succ`. No `b`-dependence enters the numeric threshold at all in
this branch (unlike the `k = 1` branch, per the file docstring). -/
theorem no_k_ge_two_general {n p : ℕ} {b : ℤ} (hb : 1 ≤ b) (hn : 1 < n) (hp : p.Prime)
    (hp2 : p * p ∣ n) (hMeq : Phi n (b + 1) b = (p : ℤ)) : False := by
  set a : ℤ := b + 1 with hadef
  obtain ⟨m, hm⟩ := hp2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · exfalso; rw [h0, Nat.mul_zero] at hm; omega
    · exact h
  set n' : ℕ := p * m with hn'def
  have hnn' : n = n' * p := by rw [hn'def, hm]; ring
  have hpn' : p ∣ n' := ⟨m, hn'def⟩
  have hn'gt1 : 1 < n' := by
    rw [hn'def]
    have hple : p ≤ p * m := Nat.le_mul_of_pos_right p hmpos
    have := hp.one_lt
    omega
  have hbne : b ≠ 0 := by omega
  have heq : Phi n a b = Phi n' (a ^ p) (b ^ p) := by
    rw [hnn']; exact Phi_expand_eq_of_dvd hp hpn' a b hbne
  have hMeq' : Phi n' (a ^ p) (b ^ p) = (p : ℤ) := by rw [← heq, hadef]; exact hMeq
  have hab' : b ^ p < a ^ p := by
    have hab : b < a := by omega
    have hb0 : (0:ℤ) ≤ b := by omega
    exact pow_lt_pow_left₀ hab hb0 hp.ne_zero
  have hb1' : 1 ≤ b ^ p := one_le_pow₀ hb
  have hlb := Phi_totient_lower_bound (n := n') hn'gt1 hb1' hab'
  rw [hMeq'] at hlb
  -- hlb : (a^p - b^p) ^ φ(n') < p
  have hmargin : (p : ℤ) ≤ a ^ p - b ^ p := by
    rw [hadef]; exact pow_sub_pow_ge_of_succ hb p
  have hn'pos : 0 < n' := Nat.zero_lt_one.trans hn'gt1
  have hexpge1 : 1 ≤ Nat.totient n' := Nat.totient_pos.mpr hn'pos
  have hbase_pos : (1 : ℤ) ≤ a ^ p - b ^ p := by omega
  have hpowge : a ^ p - b ^ p ≤ (a ^ p - b ^ p) ^ (Nat.totient n') :=
    le_self_pow₀ hbase_pos (by omega)
  have hfin : (p : ℤ) ≤ (a ^ p - b ^ p) ^ (Nat.totient n') := le_trans hmargin hpowge
  linarith [hlb, hfin]

/-! ### The `b ≥ 2` uniform margin — closing the `k = 1` case WITHOUT a finite check

The key finding of this session: the `k = 1` margin (`ZsygmondyBaseTwoEndgame`'s
`p_le_four_of_k_eq_one`, needing `p ≥ 5 ⟹ 3p < 2^p` and then a case-by-case pin to
`p = 3, n = 6`) does NOT need any threshold or case split at `b ≥ 2` — a single closed-form
inequality `(2b+1)·p < (b+1)^p - b^p`, uniform in `p ≥ 3`, holds for ALL `b ≥ 2` (proved
below by induction on `p` using the exact recursion `D(p+1) = (b+1)·D(p) + b^p` where
`D(p) := (b+1)^p - b^p`), and this ALONE forces a direct contradiction with the height
sandwich — no analogue of the `n = 6` exception survives for any `b ≥ 2`. This matches the
classical exception list (`(n,a,b) = (6,2,1)` is the UNIQUE sporadic exception across all
`b ≥ 1`) and gives a genuinely different (and simpler) proof shape than the `b = 1` file for
this branch. Numerically checked: the margin `9 < 7` FAILS at `(b,p) = (1,3)` (exactly the
`n = 6` exception) but ALREADY HOLDS at `(b,p) = (2,3)` (`15 < 19`), confirming `b = 1` is
the unique hard case. -/

/-- **Exact recursion for `D(p) := (b+1)^p - b^p`.** -/
private theorem D_succ_eq (b : ℤ) (p : ℕ) :
    (b + 1) ^ (p + 1) - b ^ (p + 1) = (b + 1) * ((b + 1) ^ p - b ^ p) + b ^ p := by ring

/-- **Uniform `b ≥ 2` margin.** For `b ≥ 2` and `p ≥ 3`: `(2b+1)·p < (b+1)^p - b^p`. No
threshold on `p` beyond `p ≥ 3` is needed (contrast the `b = 1` case, which needs `p ≥ 5`
and still leaves `p = 3` as a genuine exception). -/
theorem margin_ge_two {b : ℤ} (hb : 2 ≤ b) : ∀ p : ℕ, 3 ≤ p →
    (2 * b + 1) * (p : ℤ) < (b + 1) ^ p - b ^ p := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base =>
    have hD3 : (b + 1) ^ 3 - b ^ 3 = 3 * b ^ 2 + 3 * b + 1 := by ring
    rw [hD3]
    have hkey : (0:ℤ) ≤ b * (b - 2) := mul_nonneg (by linarith) (by linarith)
    have hc3 : ((3:ℕ) : ℤ) = 3 := by norm_num
    rw [hc3]
    nlinarith [hb, hkey]
  | succ n hn ih =>
    have hrec := D_succ_eq b n
    have hbnpos : (0:ℤ) < b ^ n := by positivity
    have hbpos : (0:ℤ) < b + 1 := by linarith
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    rw [hrec]
    have hstep : (b + 1) * ((2 * b + 1) * (n : ℤ)) < (b + 1) * ((b + 1) ^ n - b ^ n) :=
      mul_lt_mul_of_pos_left ih hbpos
    have hn3 : (3:ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have hnb : (6:ℤ) ≤ (n:ℤ) * b :=
      mul_le_mul hn3 hb (by norm_num) (by linarith)
    have hgoal_reduce : (2 * b + 1) * ((n : ℤ) + 1) ≤ (b + 1) * ((2 * b + 1) * (n : ℤ)) := by
      have hfactor : (b + 1) * ((2 * b + 1) * (n : ℤ)) - (2 * b + 1) * ((n : ℤ) + 1)
          = (2 * b + 1) * ((n : ℤ) * b - 1) := by ring
      nlinarith [hfactor, hnb, hb]
    linarith [hstep, hgoal_reduce, hbnpos]

/-- **The `k = 1` case is impossible for `b ≥ 2`.** For `b ≥ 2`, `q > 1`, `p` prime with
`p ∤ q` and `p ≥ 3`: `Phi (q * p) (b+1) b = p` is impossible. This is the `b ≥ 2` analogue
of `ZsygmondyBaseTwoEndgame.p_le_four_of_k_eq_one` — but reaches `False` DIRECTLY (no
residual `p ≤ 4` / congruence-pin / `n = 6` finite check needed), via the uniform margin
`margin_ge_two` combined with the height sandwich (`Phi_totient_lower_bound` /
`Phi_totient_upper_bound`) and the exact gearbox identity `Phi_expand_eval_eq_mul_of_not_dvd`.
-/
theorem k_eq_one_impossible_of_b_ge_two {q p : ℕ} {b : ℤ} (hb : 2 ≤ b) (hq1 : 1 < q)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hqp : ¬ p ∣ q)
    (hMeq : Phi (q * p) (b + 1) b = (p : ℤ)) : False := by
  set a : ℤ := b + 1 with hadef
  have hb1 : (1:ℤ) ≤ b := by omega
  have hbne : b ≠ 0 := by omega
  have hexpand : Phi (q * p) a b * Phi q a b = Phi q (a ^ p) (b ^ p) :=
    Phi_expand_eval_eq_mul_of_not_dvd hp hqp a b hbne
  rw [hMeq] at hexpand
  -- hexpand : (p:ℤ) * Phi q a b = Phi q (a^p) (b^p)
  have hab : b < a := by omega
  have hPhiqab_pos : 0 < Phi q a b := by
    have hlbq := Phi_totient_lower_bound (n := q) hq1 hb1 hab
    have hnn : (0:ℤ) ≤ (a - b) ^ Nat.totient q := pow_nonneg (by omega) (Nat.totient q)
    linarith
  have hubq : Phi q a b ≤ (a + b) ^ Nat.totient q := Phi_totient_upper_bound q hb1 hab
  have hab' : b ^ p < a ^ p := by
    have hb0 : (0:ℤ) ≤ b := by omega
    exact pow_lt_pow_left₀ hab hb0 hp.ne_zero
  have hb1' : (1:ℤ) ≤ b ^ p := one_le_pow₀ hb1
  have hlbqp := Phi_totient_lower_bound (n := q) hq1 hb1' hab'
  rw [← hexpand] at hlbqp
  -- hlbqp : (a^p - b^p) ^ φ(q) < p * Phi q a b
  have hchain : (a ^ p - b ^ p) ^ Nat.totient q < (p:ℤ) * (a + b) ^ Nat.totient q := by
    have hpnn : (0:ℤ) ≤ (p:ℤ) := by positivity
    calc (a ^ p - b ^ p) ^ Nat.totient q < (p:ℤ) * Phi q a b := hlbqp
      _ ≤ (p:ℤ) * (a + b) ^ Nat.totient q := mul_le_mul_of_nonneg_left hubq hpnn
  -- the uniform margin, instantiated at a = b + 1
  have hmargin : (a + b) * (p : ℤ) < a ^ p - b ^ p := by
    have h := margin_ge_two hb p hp3
    rw [hadef]
    have heq2b1 : b + 1 + b = 2 * b + 1 := by ring
    rw [heq2b1]
    exact h
  have hqe1 : Nat.totient q ≠ 0 := (Nat.totient_pos.mpr (by omega)).ne'
  have hab_pos : (0:ℤ) ≤ (a + b) * (p:ℤ) := by
    have : (0:ℤ) < a + b := by omega
    positivity
  have hpowlt : ((a + b) * (p:ℤ)) ^ Nat.totient q < (a ^ p - b ^ p) ^ Nat.totient q :=
    pow_lt_pow_left₀ hmargin hab_pos hqe1
  have hpoweq : ((a + b) * (p:ℤ)) ^ Nat.totient q =
      (a + b) ^ Nat.totient q * (p:ℤ) ^ Nat.totient q := by
    rw [mul_pow]
  rw [hpoweq] at hpowlt
  have hchain2 : (a + b) ^ Nat.totient q * (p:ℤ) ^ Nat.totient q <
      (p:ℤ) * (a + b) ^ Nat.totient q := lt_trans hpowlt hchain
  have habpos : (0:ℤ) < (a + b) ^ Nat.totient q := by
    have : (0:ℤ) < a + b := by omega
    positivity
  have hpcancel : (p:ℤ) ^ Nat.totient q < (p:ℤ) := by
    have hcomm : (p:ℤ) * (a + b) ^ Nat.totient q = (a + b) ^ Nat.totient q * (p:ℤ) := by ring
    rw [hcomm] at hchain2
    exact lt_of_mul_lt_mul_left hchain2 habpos.le
  have hp1lt : (1:ℤ) < (p:ℤ) := by exact_mod_cast hp.one_lt
  have hiff := pow_lt_pow_iff_right₀ (a := (p:ℤ)) (n := Nat.totient q) (m := 1) hp1lt
  rw [pow_one] at hiff
  have hlt1 : Nat.totient q < 1 := hiff.mp hpcancel
  omega

end ZsygmondyExceptionalEndgameGeneral
