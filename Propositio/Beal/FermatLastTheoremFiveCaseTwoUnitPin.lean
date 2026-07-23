import Propositio.Beal.FermatLastTheoremFiveCaseTwoExtraction
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic

/-!
# FLT-5 Case II — the conjugation / `√5`-residue module toward pinning the unit exponent

`FermatLastTheoremFiveCaseTwoExtraction.caseTwoFactorL_extraction` decomposes the concrete
Case-II factor as `caseTwoFactorL x y = √5ᴷ · (±φⁿ · d⁵)`. The remaining classical content
(Legendre, 1825) is to **pin the unit exponent `n`** and then recombine into a strictly smaller
solution. Both prior Case-II postmortems
(`docs/kb/failed/2026-07-12__…`, `docs/kb/failed/2026-07-18__…round2`) identify the genuinely
missing piece not as one small lemma but as a **reusable `√5`-adic residue / conjugation module**
for the concrete `⟨a,b⟩ = a+b·φ` model of `ℤ[φ]`. This file builds exactly that module.

The mathematical heart of the pin is the contrast between how fifth powers and how the unit `φ`
behave under the Galois conjugation modulo the ramified prime `√5`:

* **A fifth power is `√5²`-symmetric.** `sqrt5_sq_dvd_pow5_sub_conj` : `√5² ∣ (d⁵ − conj (d⁵))`
  for every `d`, i.e. `d⁵ ≡ conj (d⁵) (mod 5)` — the "fifth power has no `√5`-antisymmetric part
  mod `5`" fact. Concretely `five_dvd_b_pow5` : `5 ∣ (d⁵).b` (the `φ`-coordinate of any fifth
  power is divisible by `5`), and `not_five_dvd_a_pow5` : if `√5 ∤ d` then `5 ∤ (d⁵).a`.
* **The unit `φ` is not.** `phiZpow`'s `φ`-coordinate is the (integer) Fibonacci sequence
  (`phiZpow_b : (φⁿ).b = Int.fib n`), which is `≡ 0 (mod 5)` exactly at multiples of `5`
  (`five_dvd_int_fib_iff : 5 ∣ fib n ↔ 5 ∣ n`) — the sensor that reads the exponent `n mod 5`
  off the `φ`-coordinate.

Combining the two contrasts gives the **unit-exponent pin** `five_dvd_exponent_of_five_dvd_b`:
for `β = ±φⁿ·d⁵` with `√5 ∤ d`, `5 ∣ β.b ⟹ 5 ∣ n`, so the unit `±φⁿ = ±(φ^(n/5))⁵` is itself
`±` a fifth power. The **trace relation** `caseTwoFactorL_add_conj`
(`caseTwoFactorL + conj caseTwoFactorL = ofInt (−(x+y)²)`) is the source of the `5 ∣ β.b`
hypothesis in the productive branch, since `5 ∣ (x+y)` in Case II.

## Main results (proved, axiom-clean, no `sorry`)

Conjugation / residue core in `ℤ[φ]` (all reusable, not FLT-specific):

* `conj_one`, `conj_pow` — `conj` is a ring endomorphism on powers.
* `sub_conj` : `z − conj z = ofInt z.b · √5` (the `√5`-antisymmetric "imaginary part").
* `add_conj` : `z + conj z = ofInt (2·z.a + z.b)` (the trace, a rational integer).
* `sqrt5_sq_dvd_pow5_sub` : `√5 ∣ (u−v) ⟹ √5² ∣ (u⁵−v⁵)` (a fifth power kills a `√5` twice).
* `sqrt5_sq_dvd_pow5_sub_conj` : `√5² ∣ (d⁵ − conj (d⁵))` — fifth powers are `√5²`-symmetric.
* `five_dvd_b_pow5` : `5 ∣ (d⁵).b`.
* `not_five_dvd_a_pow5` : `√5 ∤ d ⟹ 5 ∤ (d⁵).a`.

The Fibonacci sensor:

* `phi_pow_b`, `phiInv_pow_b`, `phiZpow_b` : `(φⁿ).b = Int.fib n` for all `n : ℤ`.
* `five_dvd_int_fib_iff` : `5 ∣ Int.fib n ↔ 5 ∣ n`.

The pin, and its FLT-5 Case II hook:

* `five_dvd_exponent_of_five_dvd_b` — **the unit-exponent pin (decoupled form).** If `√5 ∤ d` and
  `β = ±φⁿ·d⁵`, then `5 ∣ β.b ⟹ 5 ∣ n`.
* `caseTwoFactorL_add_conj` : `caseTwoFactorL x y + conj (caseTwoFactorL x y) = ofInt (−(x+y)²)`.
* `caseTwoFactorL_trace_five_dvd` : for a Case-II solution, `5 ∣ (2·a₁ + b)` where
  `a₁ = (caseTwoFactorL x y).a`, `b = (caseTwoFactorL x y).b` — the trace divisibility the pin
  consumes.

## What this does NOT do (honest scope note)

This module **pins the unit exponent** as a clean, reusable, decoupled theorem
(`five_dvd_exponent_of_five_dvd_b`), built against the real `BealGoldenIntEuclidean.GoldenInt`
(not a mock copy). Two things still separate it from closing FLT-5 Case II:

1. **Wiring the pin to a genuine solution.** `five_dvd_exponent_of_five_dvd_b` consumes the
   hypothesis `5 ∣ β.b` for the `√5`-peeled extracted factor `β` of
   `caseTwoFactorL_extraction`. Supplying that from `caseTwoFactorL_add_conj` requires the
   `√5`-valuation bookkeeping of the `√5ᴷ·β` decomposition (clean in the branch `K = 1`, where
   `caseTwoFactorL = √5·β` and the trace `= ofInt(−(x+y)²)` is `√5`-heavily divisible), which is
   not assembled here — `caseTwoFactorL_extraction` does not expose `K`, the branch, or `√5 ∤ β`
   in its public statement.
2. **The recombination.** Once `5 ∣ n`, so `β = ±(φ^(n/5)·d)⁵` is `±` a fifth power, reading a
   strictly smaller Case-II solution off that factorization and closing the infinite descent is
   additional work, not attempted here.

**No `sorry`, no project axiom** in what follows.
-/

namespace GoldenInt

/-! ## `conj` on `1` and on powers -/

@[simp] theorem conj_one : conj (1 : GoldenInt) = 1 := by ext <;> simp [conj]

/-- `conj` respects powers: `conj (z^k) = (conj z)^k` (it is a ring endomorphism). -/
theorem conj_pow (z : GoldenInt) (k : ℕ) : conj (z ^ k) = (conj z) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, conj_mul, ih]

/-! ## The `√5`-antisymmetric and symmetric parts -/

/-- **The `√5`-antisymmetric part.** `z − conj z = ofInt z.b · √5`: the difference of an element
and its Galois conjugate is `z.b` copies of the ramified prime `√5 = φ − ψ`. -/
theorem sub_conj (z : GoldenInt) : z - conj z = ofInt z.b * sqrt5 := by
  ext <;> simp [conj, ofInt, sqrt5] <;> ring

/-- **The trace.** `z + conj z = ofInt (2·z.a + z.b)`, a rational integer (`ψ = 1 − φ`, so the
`φ`-parts cancel). -/
theorem add_conj (z : GoldenInt) : z + conj z = ofInt (2 * z.a + z.b) := by
  ext <;> simp [conj, ofInt] <;> ring

/-! ## Fifth powers kill `√5` twice -/

/-- **`√5 ∣ (u−v) ⟹ √5² ∣ (u⁵−v⁵)`.** A fifth power difference is divisible by `√5²` whenever
the base difference is divisible by `√5`. Proof: the ring identity
`u⁵−v⁵ = 5·u⁴·(u−v) − (u−v)²·G` with `G = 4u³+3u²v+2uv²+v³`; the first term is divisible by
`√5² = 5` outright, the second by `(u−v)² ` hence by `√5²`. -/
theorem sqrt5_sq_dvd_pow5_sub {u v : GoldenInt} (h : sqrt5 ∣ (u - v)) :
    sqrt5 * sqrt5 ∣ (u ^ 5 - v ^ 5) := by
  obtain ⟨w, hw⟩ := h
  have hfive : (5 : GoldenInt) = sqrt5 * sqrt5 := by rw [sqrt5_sq]; rfl
  have key : u ^ 5 - v ^ 5
      = (5 : GoldenInt) * (u ^ 4 * (u - v))
        - (u - v) ^ 2 * (4 * u ^ 3 + 3 * u ^ 2 * v + 2 * u * v ^ 2 + v ^ 3) := by ring
  rw [key, hfive, hw]
  exact ⟨u ^ 4 * (sqrt5 * w) - w ^ 2 * (4 * u ^ 3 + 3 * u ^ 2 * v + 2 * u * v ^ 2 + v ^ 3),
    by ring⟩

/-- **Fifth powers are `√5²`-symmetric.** `√5² ∣ (d⁵ − conj (d⁵))` for every `d ∈ ℤ[φ]`, i.e.
`d⁵ ≡ conj (d⁵) (mod 5)`: a fifth power has no `√5`-antisymmetric part modulo `5`. Immediate from
`sqrt5_sq_dvd_pow5_sub` with `u = d`, `v = conj d` (and `√5 ∣ d − conj d` by `sub_conj`). -/
theorem sqrt5_sq_dvd_pow5_sub_conj (d : GoldenInt) :
    sqrt5 * sqrt5 ∣ (d ^ 5 - conj (d ^ 5)) := by
  rw [conj_pow]
  apply sqrt5_sq_dvd_pow5_sub
  rw [sub_conj]
  exact dvd_mul_left sqrt5 (ofInt d.b)

/-- **`5 ∣ (d⁵).b`.** The `φ`-coordinate of any fifth power in `ℤ[φ]` is divisible by `5`. (Check:
`φ⁵ = ⟨3, 5⟩`.) Proof: `d⁵ − conj (d⁵) = ofInt ((d⁵).b) · √5` (`sub_conj`) is divisible by
`√5² = ofInt 5` (`sqrt5_sq_dvd_pow5_sub_conj`); taking norms gives `25 ∣ −5·((d⁵).b)²`, so
`5 ∣ ((d⁵).b)²`, so `5 ∣ (d⁵).b`. -/
theorem five_dvd_b_pow5 (d : GoldenInt) : (5 : ℤ) ∣ (d ^ 5).b := by
  have hd : sqrt5 * sqrt5 ∣ (d ^ 5 - conj (d ^ 5)) := sqrt5_sq_dvd_pow5_sub_conj d
  rw [sub_conj, sqrt5_sq] at hd
  obtain ⟨c, hc⟩ := hd
  have hn := congrArg norm hc
  rw [norm_mul, norm_mul, norm_ofInt, norm_ofInt, norm_sqrt5] at hn
  -- hn : (d^5).b ^ 2 * (-5) = 5 ^ 2 * norm c
  have hB2 : (d ^ 5).b ^ 2 = 5 * (- norm c) := by linarith [hn]
  have hdvd : (5 : ℤ) ∣ (d ^ 5).b ^ 2 := ⟨- norm c, hB2⟩
  exact Int.Prime.dvd_pow' (by norm_num) hdvd

/-- **`√5 ∤ d ⟹ 5 ∤ (d⁵).a`.** If `d` is coprime to the ramified prime, the rational-integer
coordinate of `d⁵` is coprime to `5`. Proof: if `5 ∣ (d⁵).a` then (with `5 ∣ (d⁵).b` from
`five_dvd_b_pow5`) both coordinates of `d⁵` are divisible by `5`, so `ofInt 5 = √5² ∣ d⁵`, hence
`√5 ∣ d⁵`, hence `√5 ∣ d` (primality) — contradiction. -/
theorem not_five_dvd_a_pow5 {d : GoldenInt} (hd : ¬ sqrt5 ∣ d) : ¬ (5 : ℤ) ∣ (d ^ 5).a := by
  intro h5a
  apply hd
  have h5b : (5 : ℤ) ∣ (d ^ 5).b := five_dvd_b_pow5 d
  obtain ⟨a', ha'⟩ := h5a
  obtain ⟨b', hb'⟩ := h5b
  have hofInt : d ^ 5 = ofInt 5 * ⟨a', b'⟩ := by
    ext <;> simp [ofInt, ha', hb']
  have hsqrt5 : sqrt5 ∣ d ^ 5 := by
    rw [hofInt, ← sqrt5_sq]
    exact (dvd_mul_right sqrt5 sqrt5).mul_right _
  exact prime_sqrt5.dvd_of_dvd_pow hsqrt5

/-! ## FLT-5 Case II hook: the trace of `caseTwoFactorL` -/

/-- **Trace relation for the concrete Case-II factor.**
`caseTwoFactorL x y + conj (caseTwoFactorL x y) = ofInt (−(x+y)²)`. The `φ`-coordinates cancel
(`add_conj`), leaving `2·a₁ + b = −(x+y)²` with `a₁ = −(x²+xy+y²)`, `b = x²+y²`. -/
theorem caseTwoFactorL_add_conj (x y : ℤ) :
    caseTwoFactorL x y + conj (caseTwoFactorL x y) = ofInt (-(x + y) ^ 2) := by
  rw [add_conj]
  congr 1
  simp only [a_caseTwoFactorL, b_caseTwoFactorL]
  ring

/-- **The trace divisibility the pin consumes.** For a genuine Case-II solution (coprime `x, y`
with `x⁵+y⁵ = z⁵` and `5 ∣ z`), the trace coordinate `2·(caseTwoFactorL x y).a +
(caseTwoFactorL x y).b = −(x+y)²` is divisible by `5`, because `5 ∣ (x+y)` (Frobenius). This is
the concrete input that, combined with the `√5`-adic extraction and the Fibonacci sensor, pins the
unit exponent. -/
theorem caseTwoFactorL_trace_five_dvd {x y z : ℤ}
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    (5 : ℤ) ∣ (2 * (caseTwoFactorL x y).a + (caseTwoFactorL x y).b) := by
  -- 5 ∣ (x+y) by the Frobenius/"freshman's dream" trick.
  have h5xy : (5 : ℤ) ∣ (x + y) := by
    have hcast := FermatLastTheoremFiveCaseOne.cast_add_eq_cast_of_pow_five_eq heq
    have hz_zero : (z : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mpr h5z
    have hxy0 : ((x + y : ℤ) : ZMod 5) = 0 := by rw [hcast, hz_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 5).mp hxy0
  have htrace : 2 * (caseTwoFactorL x y).a + (caseTwoFactorL x y).b = -(x + y) ^ 2 := by
    simp only [a_caseTwoFactorL, b_caseTwoFactorL]; ring
  rw [htrace]
  exact (Dvd.dvd.pow h5xy (by norm_num)).neg_right

/-! ## The Fibonacci sensor: reading the exponent `n mod 5` off the `φ`-coordinate

The `φ`-coordinate of `φⁿ` is the (integer) Fibonacci sequence, and `5 ∣ fib n ↔ 5 ∣ n`. Together
with the `√5`-symmetry facts above, this is what pins the unit exponent. -/

/-- Successor recurrence for the `1`-coordinate of `φᵏ`: `(φ^(k+1)).a = (φᵏ).b`. -/
theorem phi_pow_succ_a (k : ℕ) : (phi ^ (k + 1)).a = (phi ^ k).b := by
  rw [pow_succ]; simp [phi]

/-- Successor recurrence for the `φ`-coordinate of `φᵏ`: `(φ^(k+1)).b = (φᵏ).a + (φᵏ).b`. -/
theorem phi_pow_succ_b (k : ℕ) : (phi ^ (k + 1)).b = (phi ^ k).a + (phi ^ k).b := by
  rw [pow_succ]; simp [phi]

/-- **`φᵏ = ⟨fib(k+1) − fib k, fib k⟩`.** The coordinates of `φᵏ` are consecutive Fibonacci
numbers; in particular the `φ`-coordinate is `fib k`. -/
theorem phi_pow_ab (k : ℕ) :
    (phi ^ k).a = (Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ) ∧ (phi ^ k).b = (Nat.fib k : ℤ) := by
  induction k with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih =>
    obtain ⟨iha, ihb⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [phi_pow_succ_a, ihb]
      have h2 : ((Nat.fib (k + 1 + 1) : ℤ)) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        have := Nat.fib_add_two (n := k); exact_mod_cast this
      rw [h2]; ring
    · rw [phi_pow_succ_b, iha, ihb]; ring

/-- The `φ`-coordinate of `φᵏ` is `fib k` (`k : ℕ`). -/
theorem phi_pow_b (k : ℕ) : (phi ^ k).b = (Nat.fib k : ℤ) := (phi_pow_ab k).2

/-- Successor recurrence for the `1`-coordinate of `(φ⁻¹)ᵏ`. -/
theorem phiInv_pow_succ_a (k : ℕ) :
    (phiInv ^ (k + 1)).a = -(phiInv ^ k).a + (phiInv ^ k).b := by
  rw [pow_succ]; simp [phiInv]

/-- Successor recurrence for the `φ`-coordinate of `(φ⁻¹)ᵏ`. -/
theorem phiInv_pow_succ_b (k : ℕ) : (phiInv ^ (k + 1)).b = (phiInv ^ k).a := by
  rw [pow_succ]; simp [phiInv]

/-- The `φ`-coordinate of `(φ⁻¹)ᵏ` is `(−1)^(k+1)·fib k` (matching `Int.fib (−k)`). -/
theorem phiInv_pow_b (k : ℕ) : (phiInv ^ k).b = (-1) ^ (k + 1) * (Nat.fib k : ℤ) := by
  have key : (phiInv ^ k).a = (-1) ^ k * (Nat.fib (k + 1) : ℤ) ∧
      (phiInv ^ k).b = (-1) ^ (k + 1) * (Nat.fib k : ℤ) := by
    induction k with
    | zero => exact ⟨by simp, by simp⟩
    | succ k ih =>
      obtain ⟨iha, ihb⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [phiInv_pow_succ_a, iha, ihb]
        have h2 : ((Nat.fib (k + 1 + 1) : ℤ)) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
          have := Nat.fib_add_two (n := k); exact_mod_cast this
        rw [h2]; ring
      · rw [phiInv_pow_succ_b, iha]; ring
  exact key.2

/-- **`(φⁿ).b = fib n` for all `n : ℤ`.** The `φ`-coordinate of the unit `φⁿ` (`phiZpow n`,
defined for all integer `n`) is exactly the integer Fibonacci number `Int.fib n`. -/
theorem phiZpow_b (n : ℤ) : (phiZpow n).b = Int.fib n := by
  by_cases hn : 0 ≤ n
  · rw [phiZpow_of_nonneg hn, phi_pow_b, Int.fib_of_nonneg hn]
  · rw [not_le] at hn
    rw [phiZpow_of_neg hn, phiInv_pow_b]
    set m : ℕ := (-n).toNat with hm
    have hnn : n = -(m : ℤ) := by rw [hm, Int.toNat_of_nonneg (by omega)]; ring
    rw [hnn, Int.fib_neg_natCast]

/-- **`5 ∣ fib n ↔ 5 ∣ n`** for `n : ℤ`. Since `fib 5 = 5`, `gcd_fib` gives
`gcd(5, fib n) = fib (gcd 5 n)`; `gcd 5 n ∈ {1, 5}` (as `5` is prime), and `fib` of it is `5` iff
`gcd 5 n = 5`, i.e. iff `5 ∣ n`. The reverse direction is `Int.fib_dvd`. -/
theorem five_dvd_int_fib_iff (n : ℤ) : (5 : ℤ) ∣ Int.fib n ↔ (5 : ℤ) ∣ n := by
  have hfib5 : Int.fib 5 = 5 := by decide
  constructor
  · intro hdvd
    have hgf : Int.gcd (Int.fib 5) (Int.fib n) = Nat.fib (Int.gcd 5 n) := Int.gcd_fib 5 n
    rw [hfib5] at hgf
    have h5g := Int.dvd_gcd (show (5 : ℤ) ∣ 5 from by norm_num) hdvd
    rw [hgf] at h5g
    have h5gN : (5 : ℕ) ∣ Nat.fib (Int.gcd 5 n) := by exact_mod_cast h5g
    have hgdvd5 : Int.gcd (5 : ℤ) n ∣ 5 := by
      have := Int.gcd_dvd_left (5 : ℤ) n; exact_mod_cast this
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ hgdvd5 with h1 | h5
    · rw [h1] at h5gN; norm_num [Nat.fib] at h5gN
    · have hgn : ((Int.gcd (5 : ℤ) n : ℕ) : ℤ) ∣ n := Int.gcd_dvd_right 5 n
      rw [h5] at hgn; exact_mod_cast hgn
  · intro hn
    have hdd : Int.fib 5 ∣ Int.fib n := Int.fib_dvd 5 n hn
    rwa [hfib5] at hdd

/-! ## The pin: `5 ∣ n` for the extracted unit exponent -/

/-- **Unit-exponent pin (decoupled form).** Let `d` be coprime to `√5` (`√5 ∤ d`) and suppose an
element `β` of `ℤ[φ]` is `±φⁿ · d⁵`. If the `φ`-coordinate `β.b` is divisible by `5`, then the
exponent `n` is divisible by `5` — so the unit `±φⁿ = ±(φ^(n/5))⁵` is itself `±` a fifth power.

This is the heart of Legendre's unit-pinning step, in reusable decoupled form. Proof: `β.b`
reduces mod `5` to `(d⁵).a · (φⁿ).b` (the other two terms of the product's `φ`-coordinate carry a
factor `(d⁵).b`, which is `≡ 0 (mod 5)` by `five_dvd_b_pow5`); since `5 ∤ (d⁵).a`
(`not_five_dvd_a_pow5`) and `5` is prime, `5 ∣ (φⁿ).b = fib n` (`phiZpow_b`), hence `5 ∣ n`
(`five_dvd_int_fib_iff`). -/
theorem five_dvd_exponent_of_five_dvd_b {β d : GoldenInt} {n : ℤ}
    (hd : ¬ sqrt5 ∣ d)
    (hβ : β = phiZpow n * d ^ 5 ∨ β = -(phiZpow n * d ^ 5))
    (hb : (5 : ℤ) ∣ β.b) : (5 : ℤ) ∣ n := by
  -- Reduce to `5 ∣ (φⁿ · d⁵).b`.
  have hb' : (5 : ℤ) ∣ (phiZpow n * d ^ 5).b := by
    rcases hβ with h | h
    · rwa [h] at hb
    · rw [h, b_neg, dvd_neg] at hb; exact hb
  -- Expand the `φ`-coordinate of the product.
  have hbmul : (phiZpow n * d ^ 5).b
      = (phiZpow n).a * (d ^ 5).b + (d ^ 5).a * (phiZpow n).b + (phiZpow n).b * (d ^ 5).b := rfl
  rw [hbmul] at hb'
  -- The two terms carrying `(d⁵).b` are `≡ 0 (mod 5)`.
  have h5b : (5 : ℤ) ∣ (d ^ 5).b := five_dvd_b_pow5 d
  have hother : (5 : ℤ) ∣ ((phiZpow n).a * (d ^ 5).b + (phiZpow n).b * (d ^ 5).b) :=
    dvd_add (h5b.mul_left _) (h5b.mul_left _)
  -- Hence `5 ∣ (d⁵).a · (φⁿ).b`.
  have hkey : (5 : ℤ) ∣ (d ^ 5).a * (phiZpow n).b := by
    have hsub := dvd_sub hb' hother
    convert hsub using 1; ring
  -- `5 ∤ (d⁵).a`, so (primality) `5 ∣ (φⁿ).b = fib n`, so `5 ∣ n`.
  have h5a : ¬ (5 : ℤ) ∣ (d ^ 5).a := not_five_dvd_a_pow5 hd
  have hp5 : Prime (5 : ℤ) := by norm_num
  have h5phib : (5 : ℤ) ∣ (phiZpow n).b := (hp5.dvd_mul.mp hkey).resolve_left h5a
  rw [phiZpow_b] at h5phib
  exact (five_dvd_int_fib_iff n).mp h5phib

end GoldenInt

section AxiomCheck
open GoldenInt
#print axioms conj_one
#print axioms conj_pow
#print axioms sub_conj
#print axioms add_conj
#print axioms sqrt5_sq_dvd_pow5_sub
#print axioms sqrt5_sq_dvd_pow5_sub_conj
#print axioms five_dvd_b_pow5
#print axioms not_five_dvd_a_pow5
#print axioms caseTwoFactorL_add_conj
#print axioms caseTwoFactorL_trace_five_dvd
#print axioms phi_pow_b
#print axioms phiInv_pow_b
#print axioms phiZpow_b
#print axioms five_dvd_int_fib_iff
#print axioms five_dvd_exponent_of_five_dvd_b
end AxiomCheck
