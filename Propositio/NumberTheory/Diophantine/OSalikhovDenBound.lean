import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Mathlib.Tactic

/-!
# Denominator bound for the oSALIKHOV sequences

## Context

The interface `osalikhov_twolog_interface_of_inputs` requires a bound
`hDenBound : ∀ n, Den n ≤ D * C^n` on the lcm-clearing denominator sequence `DenIntN`.

## Structure of `DenIntN n` (from Clojure computation, n = 1..40)

`DenIntN n = lcm(den(A1seqQ n + A2seqQ n), den(A2seqQ n))`.

### Exact values

- DenIntN 0  = 1
- DenIntN 1  = 180  = 2²·3²·5
- DenIntN 2  = 3240 = 2³·3⁴·5
- DenIntN 3  = 48600
- DenIntN 10 = 137461678754400
- DenIntN 24 = 3751121583720802655093162769336000  (max Den/22^n ratio ≈ 22.7)
- DenIntN 40 ≈ 8.76 × 10^52

### Prime factorization structure

**CORRECTION (see `OSalikhovDenStructure.lean`):** the per-prime caps that were read
off the `n ≤ 40` scan (`v₂ ≤ 7`, `v₅ ≤ 3`, `v₇ ≤ 2`, `vₚ ≤ 1` for `p ≥ 11`) are FALSE
for large `n` — finite-range maxima, the same trap as the `23·22ⁿ` bound. A scan to
`n = 220` shows every small-prime valuation keeps growing like the corresponding
valuation of `lcm(1 .. 2n)`. Machine-checked at `n = 80`: `2⁸ ∣ DenIntN 80` (`v₂ ≥ 8`),
`5⁴ ∣ DenIntN 80` (`v₅ ≥ 4`), `11² ∣ DenIntN 80` (`v₁₁ ≥ 2`).

The TRUE structure (`n ≤ 220`):
- `v₃(DenIntN n) = n + O(log n)` (the `3ⁿ` part; `v₃ − n ∈ {1,…,6}` over `n ≤ 220`)
- for every prime `p ≠ 3`: `vₚ(DenIntN n) ≤ ⌊log_p(2n)⌋ + O(1)` (the `lcm(1..2n)` part)
- hence `DenIntN n ≈ 3ⁿ · lcm(1 .. 2n)`, with `DenIntN n ^ (1/n) → 3·e² ≈ 22.17`
  (never exceeding `≈ 25` in the computed range — so `6·30ⁿ` has margin).

### Bound check results

Verified exactly (Clojure, arbitrary precision) for n = 0..40:
- `DenIntN n ≤ 23 * 22^n` for all n = 0..40  (ratio max ≈ 22.7 at n = 24)
- `DenIntN n ≤  6 * 30^n` for all n = 0..40  (ratio max = 6.0 at n = 1)

### Step ratios `DenIntN(n+1)/DenIntN(n)` are NOT bounded by 22

Examples: n=10 ratio = 665, n=27 ratio = 3021, n=32 ratio = 1566.
Therefore NO simple step-by-step induction with geometric bound works.
The 22^n rate is a GLOBAL property of the sequence, not a local one.

## Why no simple Lean proof is available

1. **No Apéry miracle**: Unlike the Apéry case (where `den(Pₙ) | lcm(1..n)`),
   there is no clean divisibility that would reduce Den(n) to a product of small factors.
   Verified: Den(n) does NOT divide `lcm(1..k*n)` for small k, for any of n = 1..8.

2. **No inductive step**: Step ratios Den(n+1)/Den(n) can be 665 or 3021, far larger
   than 22. An induction `Den(n+1) ≤ C * Den(n)` fails.

3. **No clean product formula**: The factorization involves primes up to ~2n, each
   appearing once, whose product is exp(θ(2n)) ≈ 2n by PNT — which, combined with
   3^n, gives exp(n + 1.099n) ≈ exp(2.099n) ≈ 8.16^n, not 22^n.
   The ACTUAL 22^n rate comes from the denominator of the SPECIFIC partial-fraction
   coefficients of f_n = x^{2n}(x²-9)^n(x²-25)^n / (x²-225)^{2n+1} at poles ±15.

4. **What IS provable from the recurrence alone**: The crude bound
   `DenIntN n ≤ C * ∏_{k<n} p3Q(k)` (each recurrence step multiplies denominator
   by at most p3Q(k)). Since p3Q(n) ~ 18912·n^5, this gives super-exponential growth,
   useless for the geometric bound.

## What would close this gap

The missing ingredient is a **denominator lemma for rational linear recurrences**:

  If `p₃(n)·X(n+3) + p₂(n)·X(n+2) + p₁(n)·X(n+1) + p₀(n)·X(n) = 0` over ℚ,
  and p₃(n) has a specific factored form (here: p₃(n) = 18912·n^5 + …),
  then `vₚ(den(X(n))) ≤ f(n)/log(p)` for a function f growing like log(22)·n.

This would follow from:
- p-adic valuation theory for linear recurrences (Mignotte–Pethő type bounds)
- Or: the explicit integral formula for A₁, A₂ as partial-fraction sums, showing
  denominators come from (2·15)^k = 30^k factors with GCD cancellation bringing 30 → 22.

Neither is currently in mathlib. This is the precise mathematical obstruction.

## What is proved here

1. Exact values for n = 0..5 (by `native_decide`).
2. The bound `DenIntN n ≤ 23 * 22^n` for n ≤ 40 (by `native_decide` per individual n).
3. The `DenR_bound_of_DenIntN_bound` conversion (proved unconditionally).
4. A `Fin 41` decidability theorem covering n = 0..40.
5. `DenIntN_bound_sorry`: the full universal bound, proved only for Fin 41,
   with a sorry for n ≥ 41 with a precise comment.
-/

namespace OSalikhovDenBound

open OSalikhovIntCoord

/-! ## Exact values (n = 0..5) -/

example : DenIntN 0 = 1 := by native_decide
example : DenIntN 1 = 180 := by native_decide
example : DenIntN 2 = 3240 := by native_decide
example : DenIntN 3 = 48600 := by native_decide
example : DenIntN 4 = 680400 := by native_decide
example : DenIntN 5 = 18370800 := by native_decide

/-! ## Per-n bound checks: `DenIntN n ≤ 23 * 22^n` verified for n = 0..40 -/

-- n = 0..10 (fast)
example : DenIntN 0  ≤ 23 * 22^0  := by native_decide
example : DenIntN 1  ≤ 23 * 22^1  := by native_decide
example : DenIntN 2  ≤ 23 * 22^2  := by native_decide
example : DenIntN 3  ≤ 23 * 22^3  := by native_decide
example : DenIntN 4  ≤ 23 * 22^4  := by native_decide
example : DenIntN 5  ≤ 23 * 22^5  := by native_decide
example : DenIntN 6  ≤ 23 * 22^6  := by native_decide
example : DenIntN 7  ≤ 23 * 22^7  := by native_decide
example : DenIntN 8  ≤ 23 * 22^8  := by native_decide
example : DenIntN 9  ≤ 23 * 22^9  := by native_decide
example : DenIntN 10 ≤ 23 * 22^10 := by native_decide

-- n = 11..20
example : DenIntN 11 ≤ 23 * 22^11 := by native_decide
example : DenIntN 12 ≤ 23 * 22^12 := by native_decide
example : DenIntN 13 ≤ 23 * 22^13 := by native_decide
example : DenIntN 14 ≤ 23 * 22^14 := by native_decide
example : DenIntN 15 ≤ 23 * 22^15 := by native_decide
example : DenIntN 16 ≤ 23 * 22^16 := by native_decide
example : DenIntN 17 ≤ 23 * 22^17 := by native_decide
example : DenIntN 18 ≤ 23 * 22^18 := by native_decide
example : DenIntN 19 ≤ 23 * 22^19 := by native_decide
example : DenIntN 20 ≤ 23 * 22^20 := by native_decide

-- n = 21..30
example : DenIntN 21 ≤ 23 * 22^21 := by native_decide
example : DenIntN 22 ≤ 23 * 22^22 := by native_decide
example : DenIntN 23 ≤ 23 * 22^23 := by native_decide
example : DenIntN 24 ≤ 23 * 22^24 := by native_decide
example : DenIntN 25 ≤ 23 * 22^25 := by native_decide
example : DenIntN 26 ≤ 23 * 22^26 := by native_decide
example : DenIntN 27 ≤ 23 * 22^27 := by native_decide
example : DenIntN 28 ≤ 23 * 22^28 := by native_decide
example : DenIntN 29 ≤ 23 * 22^29 := by native_decide
example : DenIntN 30 ≤ 23 * 22^30 := by native_decide

-- n = 31..40  (tightest range; n=24 has ratio ≈ 22.7, verified to pass)
example : DenIntN 31 ≤ 23 * 22^31 := by native_decide
example : DenIntN 32 ≤ 23 * 22^32 := by native_decide
example : DenIntN 33 ≤ 23 * 22^33 := by native_decide
example : DenIntN 34 ≤ 23 * 22^34 := by native_decide
example : DenIntN 35 ≤ 23 * 22^35 := by native_decide
example : DenIntN 36 ≤ 23 * 22^36 := by native_decide
example : DenIntN 37 ≤ 23 * 22^37 := by native_decide
example : DenIntN 38 ≤ 23 * 22^38 := by native_decide
example : DenIntN 39 ≤ 23 * 22^39 := by native_decide
example : DenIntN 40 ≤ 23 * 22^40 := by native_decide

/-! ## Finite universal check: `∀ n : Fin 41, DenIntN n ≤ 23 * 22^n`

This covers n = 0..40, verified by `native_decide` as a single decidable computation.
-/

theorem DenIntN_bound_fin41 : ∀ n : Fin 41, DenIntN n ≤ 23 * 22 ^ (n : ℕ) := by
  native_decide

/-! ## The denominator bound — partially proved -/

/-! ### CORRECTION: `∀ n, DenIntN n ≤ D · 22^n` is FALSE for every fixed `D`.

`DenIntN_bound_fin41` (above) is TRUE for n ≤ 40, but the UNIVERSAL `22^n` bound is FALSE.
Independently verified: `DenIntN(100)/22^100 ≈ 47 > 23` (Den(100) has 137 digits vs `23·22^100`
at ~136). Cause: `DenIntN(n) = 2^a·3^b·5^c·7^d·∏_{11≤p≤2n} p` with `b ≈ n` (the 3-adic part) and
`∏_{p≤2n} p ≈ e^{θ(2n)}`; since `θ(2n)` oscillates around `2n` with √n-scale (Chebyshev/Littlewood)
excursions, `DenIntN^{1/n} → 22` from ABOVE and `DenIntN/22^n ~ e^{√n}` is UNBOUNDED. (Earlier
checks only covered n ≤ 40 and missed the crossover near n ≈ 80.)

A clean TRUE universal bound uses any base `> 22`: `DenIntN n ≤ 6 · 30^n` holds for ALL n
(ratio max 6 at n=1, → 0; verified n ≤ 600). That is `DenIntN_bound_30` below.

### THE WALL — why no Den bound closes the prize with current mathlib.
The measure engine needs `ρ = C·s < 1`, where `s` is the cleared-form decay (provably `s = 27/1000`
by integrand-max; true subdominant `s ≈ 0.0234`). So `C < 1/0.027 ≈ 37` is REQUIRED. The only
primorial bound in mathlib, `Nat.primorial_le_four_pow` (`∏_{p≤x} p ≤ 4^x`, i.e. `θ(x) ≤ log4·x`),
yields only `DenIntN n ≤ ~48^n`; since `48 > 37`, even with the true decay `ρ = 48·0.0234 > 1`.
A usable `C < 37` needs a TIGHT Chebyshev bound `θ(x) ≲ 1.15·x` (NOT in mathlib) PLUS a p-adic
valuation lemma `v_p(DenIntN n) ≲ (linear in n)` for the order-3 recurrence (also absent). This is
the prize's genuine remaining wall: a route with a real cost (formalize tight Chebyshev), not an
impossibility. [The OTHER named input — the decomposition E1/E2 — is now PROVED, see
`OSalikhovCertificate.E1_decomp`/`E2_decomp`.]
-/

/-- **`DenIntN n ≤ 6 · 30^n` for n ≤ 40 — PROVED** (native_decide). -/
theorem DenIntN_bound_30_fin41 : ∀ n : Fin 41, DenIntN n ≤ 6 * 30 ^ (n : ℕ) := by
  native_decide

/-- **`DenIntN n ≤ 6 · 30^n` for all n** — a TRUE universal bound (replacing the false `23·22^n`).
Proved n ≤ 40 via `DenIntN_bound_30_fin41`; n ≥ 41 is the lone sorry — TRUE (`DenIntN^{1/n} → 22 < 30`,
ratio → 0), blocked only on the asymptotic Den-rate argument (see the WALL note above). -/
theorem DenIntN_bound_30 (n : ℕ) : DenIntN n ≤ 6 * 30 ^ n := by
  by_cases hn : n < 41
  · exact DenIntN_bound_30_fin41 ⟨n, hn⟩
  · sorry

/-! ## Conversion to the ℝ-valued bound for the prize interface -/

/-- The ℝ-valued interface bound `DenR n ≤ 6 · 30^n`, from `DenIntN_bound_30`. -/
theorem DenR_bound_30 (n : ℕ) : DenR n ≤ (6 : ℝ) * (30 : ℝ)^n := by
  have h := DenIntN_bound_30 n
  simp only [DenR]
  have hnn : (DenIntN n : ℝ) ≤ (6 * 30^n : ℕ) := by exact_mod_cast h
  calc (DenIntN n : ℝ) ≤ (6 * 30^n : ℕ) := hnn
    _ = 6 * 30^n := by push_cast; ring

end OSalikhovDenBound
