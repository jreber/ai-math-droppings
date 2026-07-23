import Mathlib.Tactic

/-!
# Reusable Collatz / Terras tactic macros

Macros distilled from the most-repeated proven tactic sequences in
`docs/kb/tactic-bank.json`. Centralizing them lets the many Collatz descent
files share one spelling instead of re-typing the same combinator chain.

Each macro abstracts a *sequence*, not the objects it acts on: `collatz_step`
calls `unfold T`, so the local `def T` (the Terras half-step
`if n % 2 = 0 then n / 2 else (3 * n + 1) / 2`) must be in scope at the call
site. Every Collatz descent file already `open TerrasDensity`s (or defines its
own `T`), so this holds wherever the macro is used.

Add a macro here when a sequence in `tactic-bank.json` reaches count ≥ 3 and
has a stable, parameter-free shape.

## Hygiene notes

Lean 4's macro system applies hygiene to every identifier that appears literally
in a quasi-quotation body: it appends a fresh macro-scope tag, so `T` becomes
`T✝`, `this` becomes `this✝`, etc.  For names that **reference** something from
the call site (like the local definition `T`, or the anonymous hypothesis `this`),
hygiene would therefore break the lookup.

Two complementary techniques are used here:

* **`Lean.mkIdent`** (in `macro`) — creates an identifier with *no* hygiene
  scope, so it always resolves to exactly the given name at the call site.
  Used for `collatz_step` (referencing `T`) and `push_cast_exact` (referencing
  `this`).  `Lean.mkIdent` bypasses hygiene for *references*; the quasi-quotation
  body still typechecks because the position being spliced into accepts the
  `ident` syntactic category.

* **`MVarId.intro`** (in `elab`) — calls the Lean elaborator API directly to
  introduce hypotheses by a concrete `Name`.  Unlike a quasi-quoted `intro h`,
  this does *not* go through the macro system and so the name is recorded in the
  local context without any hygiene suffix.  Used for `all_range_intro`
  (introducing `i` and `hi`).
-/

/-- **`collatz_step`** — evaluate one Terras half-step `T` on an explicit
    residue-class representative.

    Abstracts the single most-repeated proven sequence (tactic-bank id
    `unfold-split-omega`, count 30): unfold the half-step `T`, case-split the
    `if n % 2 = 0` parity branch, and discharge *both* resulting branches with
    `omega` (the impossible-parity branch closes by arithmetic contradiction,
    the live branch by linear arithmetic).

    `split` produces two goals, hence `<;> omega` rather than a single `omega`.

    Requires a `def T` matching the Terras half-step to be in scope (every
    Collatz descent file `open TerrasDensity`s, which provides it).

    The `T` unfolded here is spliced *unhygienically* (via `Lean.mkIdent`) so
    it resolves to whatever `T` is in scope at the call site — the local /
    `open`ed `def T`, not a macro-private name. (A bare `unfold T` inside the
    macro would be renamed to `T✝` by hygiene and fail to resolve.)

    Usage: `have h : T (16 * k + 3) = 24 * k + 5 := by collatz_step` -/
macro "collatz_step" : tactic =>
  let t := Lean.mkIdent `T
  `(tactic| (unfold $t <;> split <;> omega))

/-- **`all_range_intro`** — open a `List.all _ = true` goal over `List.range n`
    into a per-index obligation.

    Abstracts the stable prologue of tactic-bank sequence `rw-apply-intro`
    (count 95): applies `List.all_eq_true.mpr`, introduces the index and
    membership hypothesis with concrete names, and rewrites the membership
    to a numeric bound.

    After this macro, two names are in scope at the call site:
    - `i : ℕ` — the range index
    - `hi : i < n` — the range membership rewritten from `List.mem_range`

    Both names are introduced via `Lean.MVarId.intro` (the elaborator API,
    not a quasi-quoted `intro`) so they appear in the local context without
    any hygiene suffix and are accessible to subsequent tactics by their exact
    spellings `i` and `hi`.

    The membership rewrite (`i ∈ List.range n → i < n`) is performed with
    `simp only [List.mem_range] at *` rather than `rw ... at hi` to avoid
    Lean 4 quasi-quotation type restrictions on the `locationHyp` position.

    The remaining per-index work (`interval_cases i`, per-branch `decide`,
    etc.) varies per call site and must follow the macro invocation.  The
    surrounding `rw [← noStDvd_top, ...]` setup and per-branch bullets are NOT
    baked in — they differ between call sites.

    Note: all current corpus call sites (count-95 bank) are in heavy
    kernel-decide enumeration files and are therefore not refactored here.  New
    hand-written files should use variable names `i` and `hi` to match what
    this macro introduces.

    Usage (new code):
    ```lean
    -- Goal shape: (List.range n).all f = true
    all_range_intro          -- introduces i : ℕ,  hi : i < n
    interval_cases i
    all_goals decide
    ``` -/
elab "all_range_intro" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply List.all_eq_true.mpr))
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let (_, mvarId) ← mvarId.intro `i
  let (_, mvarId) ← mvarId.intro `hi
  Lean.Elab.Tactic.setGoals [mvarId]
  Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [List.mem_range] at *))

/-- **`push_cast_exact`** — transport a coercion goal through `push_cast` and
    close it by `exact`.

    Abstracts tactic-bank sequence `push_cast-exact` (count 8): after
    establishing `this : (↑a … : R) = (↑b … : R)` via `have := h (↑a) (↑b)`,
    rewrites casts in `this` and the goal to a uniform representation, then
    closes by `exact this`.

    The name `this` is spliced *unhygienically* (via `Lean.mkIdent`) in both
    `push_cast at this ⊢` and `exact this`, so it resolves to the anonymous
    hypothesis introduced by the preceding `have :=` rather than to a
    hygiene-renamed copy `this✝`. (`push_cast at this ⊢` in a plain
    quasi-quotation would expand with a hygienic `this✝` and fail to find the
    hypothesis.)

    Replaces both the one-liner form `push_cast at this ⊢; exact this` and
    the equivalent two-line split form.

    Usage:
    ```lean
    have h : ∀ r s : ZMod p, r ^ m + s ^ n ≠ k := by decide
    have := h (a : ZMod p) (b : ZMod p)
    push_cast_exact            -- closes the coercion-transport subgoal
    ``` -/
macro "push_cast_exact" : tactic =>
  let h := Lean.mkIdent `this
  `(tactic| (push_cast at $h ⊢; exact $h))
