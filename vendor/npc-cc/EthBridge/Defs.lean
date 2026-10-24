import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.Engine

/-! # EthBridge core definitions (Tranche E0)

Formal blocks for the ETH near-robust-to-robust bridge
(`eth-docs/REENTRY_ROBUSTIFICATION_BY_DIRECT_DEFECT_ACCOUNTING.md`).

This file holds the note's §2–§4 primitives:
* `Bdef`        — the Bob-defect envelope `B(p) = (1 + 6/(5p)) ln 2`   (note (4));
* `cExcess`     — the excess-copy quantity `c_a(p) = p - 2^(a-1)`, real-valued
                  (the half-integer value `c_0(p) = p - 1/2` is intentional, note (10));
* `rowThreshold`— the row thresholds `A_a = ⌈m·2^a·x⌉`                 (note §2);
* `colDefect`   — the absolute column defect `Def(K) = ln(n^p/|K|)`    (note §4);
* `stateDefect` / `stateDensity` — the Theorem-1 state predicate in its TWO
                  equivalent forms (defect vs density). The faithfulness judge
                  settles which becomes canonical; both are drafted here.

Every definition is paired with an inhabitability / sanity example in
`EthBridge/UnitTests.lean` (BtL discipline: a def is trusted only once its unit
tests close, hardest field derivable proved first).

DISCIPLINE: these are STATEMENTS only; all downstream proofs are `sorry` until
the faithfulness judge signs off on the statements against the note's literal
text (ceilings, strict vs non-strict, real vs ℕ, density↔defect conversion).
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## Note (4): the Bob-defect envelope `B(p)` -/

/-- `B(p) = (1 + 6/(5p)) ln 2`  (note (4)).

Real-valued function of the copy count `p`. Used only for integer `p ≥ 2`; at
`p = 0` Lean's `6/(5·0) = 0` makes `Bdef 0 = ln 2`, an irrelevant total-function
artifact. Unit tests: `Bdef 2 = (8/5)·ln 2` and `Bdef p > 0` for `p ≥ 2`. -/
noncomputable def Bdef (p : ℕ) : ℝ :=
  (1 + 6 / (5 * (p : ℝ))) * Real.log 2

/-! ## Note (10): the excess-copy quantity `c_a(p)` -/

/-- `c_a(p) = p - 2^(a-1)`, real-valued  (note (10)).

The exponent `a-1` is taken over `ℤ` (via `zpow`), so the value at `a = 0` is
the intentional half-integer `c_0(p) = p - 2^(-1) = p - 1/2` (note (10): "The
half-integer value at `a=0` is intentional. It makes the terminal one-copy
projection strictly better than `exp(-λ)`."). For `a ≥ 1` the power is a genuine
integer `2^(a-1)`. Argument order is `(a, p)` matching `c_a(p)`.
Unit tests: `cExcess 0 1 = 1/2`, `cExcess 2 3 = 1`. -/
noncomputable def cExcess (a p : ℕ) : ℝ :=
  (p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)

/-! ## Note §2: the row thresholds `A_a` -/

/-- `A_a = ⌈m·2^a·x⌉`  (note §2), as a natural number (a retained-row count).

Nat-ceiling `⌈·⌉₊`, matching `NPCC.bracketGE`'s `⌈m·x⌉` row threshold (`A_0`).
Only indices with `2^a·x ≤ 1` are used at call sites (note §2). Unit test:
`rowThreshold m x 0 = ⌈m·x⌉₊`. -/
noncomputable def rowThreshold (m : ℕ) (x : ℝ) (a : ℕ) : ℕ :=
  ⌈(m : ℝ) * (2 : ℝ) ^ a * x⌉₊

/-! ## Note §4: the absolute column defect `Def(K)` -/

/-- `Def(K) = ln(n^p / |K|)`  (note §4), the absolute column defect of a column
set `C` on `p` active copies of an `X × Y` game (`n = Fintype.card Y`,
`n^p = Fintype.card (Fin p → Y)`).

CAUTION (flagged to judge): at `|C| = 0` Lean gives `n^p/0 = 0` and
`Real.log 0 = 0`, so the defect form silently reads `Def = 0`; the density form
below does not have this pathology. See the equivalence lemma in `Arith.lean`. -/
noncomputable def colDefect (Y : Type*) [Fintype Y] (p : ℕ) (C : Finset (Fin p → Y)) : ℝ :=
  Real.log (((Fintype.card Y : ℝ) ^ p) / (C.card : ℝ))

/-! ## The Theorem-1 state predicate — TWO variants (judge settles the canonical one)

A Theorem-1 state is a restriction of `Interlace(W,p)`, recorded (as in
`NPCC.bracketGE`) by its extraction data `(R, C)` — a row subset `R` and a
column subset `C` of the `p`-fold interlace. The two conditions are:

* **rows**: at least `A_a` rows in every active `W` block, i.e. the row set is
  `([p], A_a)`-equipartitioned (`IsEquipartitionedGE R univ (rowThreshold m x a)`);
* **columns**: `Def(C) ≤ c_a(p)·λ`, equivalently `|C| ≥ n^p · exp(-c_a(p)·λ)`.

VARIANT CHOICE (note plan step 2 / ledger `eth:def-state`): the defect form is
literal to the note; the density form `|C| ≥ n^p·e^{-c_a(p)λ}` is the
`Real.log`-free equivalent that avoids the `|C| = 0` pathology of `colDefect`.
The judge decides which is canonical; `Arith.state_defect_iff_density` records
their equivalence (under `0 < |C|`, `0 < n`). Both are drafted; downstream
statements (E1–E3) reference `stateDensity` provisionally. -/

/-- Theorem-1 state family, **defect form** (note §4, literal):
row-equipartition at threshold `A_a` and `Def(C) ≤ c_a(p)·λ`. -/
noncomputable def stateDefect (X Y : Type*) [Fintype X] [Fintype Y]
    (p a : ℕ) (x lam : ℝ) :
    Set (Finset (Fin p × X) × Finset (Fin p → Y)) :=
  { RC | IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin p))
           (rowThreshold (Fintype.card X) x a)
         ∧ colDefect Y p RC.2 ≤ cExcess a p * lam }

/-- Theorem-1 state family, **density form** (the `Real.log`-free equivalent):
row-equipartition at threshold `A_a` and `|C| ≥ n^p · exp(-c_a(p)·λ)`.
Faithful even at `|C| = 0` (LHS `> 0`, so empty column sets are excluded,
matching the note's positive-target states). -/
noncomputable def stateDensity (X Y : Type*) [Fintype X] [Fintype Y]
    (p a : ℕ) (x lam : ℝ) :
    Set (Finset (Fin p × X) × Finset (Fin p → Y)) :=
  { RC | IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin p))
           (rowThreshold (Fintype.card X) x a)
         ∧ ((Fintype.card Y : ℝ) ^ p) * Real.exp (-(cExcess a p * lam)) ≤ (RC.2.card : ℝ) }

/-- The complexity conclusion `comp(state) ≥ C + a` of Theorem 1, as a reusable
abbreviation: `Dfamily` is the *min* over members, so `C + a ≤ Dfamily …` says
every restriction in the state has communication complexity `≥ C + a` (note (11)).
Provided as scaffolding for E3; not itself an E0 obligation. -/
noncomputable def stateComp (X Y : Type*) [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (p a : ℕ) (x lam : ℝ) : ℕ :=
  Dfamily (interlaceFun W p) (stateDensity X Y p a x lam)

end EthBridge
