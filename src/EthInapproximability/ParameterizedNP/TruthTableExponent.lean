import EthInapproximability.ParameterizedNP.CommonPadding

/-!
# Parameterized NP route: the common truth-table exponent (`step:I-12`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`CLOCK-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 134),
"Total computable nondecreasing unbounded slow diagonal tied to the same
machine/compiler, with final-only padding and **subexponential table size**",
recorded there as human **proved** / Lean **partially landed**.  The `cc-t1u`
cell of that row closes with the explicit remainder "**`step:I-12` beyond
`frozenPaddedEntryCount`** -- `expi:E-12-log` and `log_2 T_n = o(n)` are not
landed".  This module is exactly that remainder.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchors (proof source).**
  * `step:I-12` *Common truth-table exponent*,
    `sections/13-iteration-assembly.tex`, label line 886, body lines
    886--913.  Its headline, lines 886--888, is "The common truth-table
    exponent and its subexponential bound contain no suppressed floor or
    ceiling term."
  * Lines 889--894: "The padded matrix is a Boolean function on two `e(n)`-bit
    inputs.  Its side length and number of entries are exactly
    `S_n = 2^{e(n)}`, `T_n = S_n^2 = (2^{e(n)})^2 = 2^{2e(n)}`."
  * `expi:E-12-log` (label line 900, display lines 896--901):
    `log_2 T_n = 2 e(n) = 2 g(n) + 2 ceil(log_2(n+2))`.
  * Lines 902--907, "The ceiling contributes less than one extra unit:
    `log_2(n+2) <= ceil(log_2(n+2)) < log_2(n+2) + 1`".
  * Lines 908--909: "Since `g(n) = o(n)`, `log_2(n+2) = o(n)`, and `1 = o(n)`,
    dividing `expi:E-12-log` by `n` proves `log_2 T_n = o(n)`."
  * Lines 909--911: "Finally, `2^{ceil(log_2(n+2))} >= n + 2`, so
    `S_n >= n + 2` and `T_n >= (n+2)^2`."
  * Lines 911--913, the closing scope sentence: "The common-square exponent,
    the truth-table length, and the padding transport are therefore all fixed
    before the promise case is analysed."
  * `eq:common-size` in `sections/12-iteration-specification.tex` (label line
    628, display lines 621--629) supplies `e`, `S_n`, `T_n`, and
    `eq:uniform-size-majorant` (label line 597) supplies `g`.
  * `conv:finite-slots` in `sections/02-mechanical-contract.tex` fixes the
    zero-based reading of `[S_n]`, already transcribed in `FiniteSlots.lean`
    and used through the banked `CommonPadding` statements.

* **Banked endpoints, all grep-verified present in
  `src/EthInapproximability/ParameterizedNP/` before use.**
  *Actually consumed:*
  * from `CommonPadding.lean` (tranche `cc-t1u`): **`frozenPaddedEntryCount`**
    (in `paddedTruthTableLength`) and **`carrierFitsCommonSquare_of_zhat`**
    (in `carrierEntriesFitTruthTable`), together with the pinned
    `CommonPadding.witnessClock` battery -- `witnessClock_gMaj` -- used only
    in Part 7's consistency witness;
  * from `PaddingAndClock.lean` (tranche `cc-t1t-r1`): `commonSizeParameters`
    (in `truthTable_pow`), `gMaj_spec` (in `truthTableExponent_monotone`),
    `SlowClockGateSet` with `witnessClock` and `witnessClock_gates`, `Tk`,
    `tk_ge`, `slowIndex`, `zhat`, `zSeed`, `qSeed_le`, `aSeed_bounds`, and the
    definitions `gMaj`, `eCommon`, `sCommon`, `tCommon`;
  * from `IterationAssembly.lean`: `ellN`, `ellN_exists`, `envE`, `depthB`.

  *Verified present but deliberately **not** consumed:* `zhat_sublinear` and
  `slowClock_sublinear`.  Both bound the **pointwise** majorant `zhat V n` at
  the single clock index; `expi:E-12-log` is stated at the **prefix maximum**
  `g(n)`, and `zhat V n <= gMaj V n` runs the wrong way, so routing the
  subexponential clause through them would be a fabricated dependence rather
  than a trace.  The frozen input really is `g(n) = o(n)` of lines 796--807,
  which `CLOCK-001` leaves GAP-EXPOSED, so it enters here as a named
  hypothesis (GAP-EXPOSED 2 below).

* **Imports.**  `EthInapproximability.ParameterizedNP.CommonPadding` and,
  through it, `PaddingAndClock`, `SizePropagation`, `IterationAssembly` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported, so the
  cited AGHP balanced-family axiom stays outside this module's closure and no
  ledger note for it is needed.  No new import is added: `Real.logb` is
  already reachable through the existing Mathlib surface (`SizePropagation`
  already works over `ℝ`).

* **Proof status.**  Every declaration below is **new**.  Nothing is inherited,
  nothing is ported, and nothing is transcribed from `C:/lean/npc-cc/EthProof`,
  which traced the older fixed-width manuscript and is not a trace or style
  source here.

## What this module lands

1. **The exponent itself** (frozen lines 891--894, 896--901).
   `truthTableExponent V n` is the frozen middle term `2 e(n)` of
   `expi:E-12-log`; `truthTableExponent_eq` is its right-hand term
   `2 g(n) + 2 ceil(log_2(n+2))`; `truthTable_pow` is
   `T_n = 2^{log_2 T_n}`.
2. **The headline, "no suppressed floor or ceiling term"** (frozen lines
   886--888).  `truthTableExponent_no_rounding` proves that the **floor**
   logarithm and the **ceiling** logarithm of `T_n` are *both* equal to
   `truthTableExponent V n`, so no rounding convention is being suppressed;
   `truthTableExponent_logb` proves that the **real** logarithm is the same
   number, on the nose.  `floorAndCeilingDisagreeInGeneral` records in the
   kernel that this agreement is a real claim and not a tautology.
3. **The `e(n)`-bit reading** (frozen line 889).  `sideIsBitStrings` and
   `truthTablePairIsBitStrings` say that one side of the padded square is the
   set of `e(n)`-bit strings and that the index set of the truth table has
   exactly `2^{log_2 T_n}` elements; `paddedTruthTableLength` transports the
   banked `frozenPaddedEntryCount` to the new name, and
   `carrierEntriesFitTruthTable` shows the *unpadded* entry count fits inside
   it through the banked `carrierFitsCommonSquare_of_zhat`.
4. **The ceiling estimate** (frozen lines 902--907), twice:
   `ceilingPowerSandwich` in the exponentiated integer form, and
   `ceilingSandwich` as the literal real display.
5. **The subexponential clause** (frozen lines 908--909), as
   `truthTableExponent_sublinear`: the frozen "dividing by `n`" step, in the
   **finite multiplicative form at a single index** that `CLOCK-001` and
   `SIZE-001` established, with the two frozen `o(n)` inputs as **named
   hypotheses**.  No `Filter.Tendsto` and no asymptotic order relation appears
   anywhere in this module.
6. **The lower bounds** (frozen lines 909--911), as `commonSquare_ge`
   (`S_n >= n + 2`) and `truthTable_ge` (`T_n >= (n+2)^2`), with the growth
   consequences the reader uses at `06-eth.tex:351` and `:360`.
7. **Non-vacuity of the conditional deliverable** (Part 7).  The hypothesis
   bundle of `truthTableExponent_sublinear` is inhabited at a **legal
   gate-satisfying clock** -- `PaddingAndClock.witnessClock`, whose four
   frozen gates are banked as `witnessClock_gates` -- at the source size
   `n = 2^63` and the nondegenerate multiplier `m = 2`, and the conclusion it
   yields there is not the trivial `0 <= n`
   (`truthTableExponent_positive` is proved alongside it).

## Reader counterparts

The reader counterparts are in
`routes/parameterized-np/reader-facing/sections/06-eth.tex`.  **That file was
opened first-hand this tranche and every cited item read to confirm it states
the same fact.**  `CLOCK-001` already claims lines 281, 283, 284, 288,
298--302, 304, 317, 318, 319, 322, 325--329, 330, 332--333, 333--334,
`eq:paper-padding-invariance` (label 338) and the clause "every branch has the
same truth-table length `T_n`" of lines 340--341.  The items below are
disjoint from those, and **no item below is assigned to two declarations**.

* line 340, the **first** clause of that sentence -- "The padded matrix is a
  Boolean function on two `e(n)`-bit inputs" -- to `sideIsBitStrings`.  Its
  second clause, "every branch has the same truth-table length `T_n`", is
  `CommonPadding.frozenPaddedEntryCount`'s item and is **not** re-claimed
  here; `paddedTruthTableLength` therefore claims no reader item, being that
  banked statement rewritten at the new exponent name.
* `eq:paper-table-subexponential` (label line 344, display line 343) reads
  `log T_n = 2 g(n) + 2 ceil(log(n+2)) = o(n)` and is **split by clause**:
  the **equality** `log T_n = 2 g(n) + 2 ceil(log(n+2))` to
  `truthTableExponent_eq`, and the **`= o(n)` clause** to
  `truthTableExponent_sublinear`.  No third declaration touches it.
* line 351, "The sequence `T_n` is nondecreasing and tends to infinity", is
  **split by clause**: *nondecreasing* to `truthTable_monotone` and *tends to
  infinity* to `truthTable_unbounded`.
* line 360, "The search for `p(T)` terminates because `T_n >= (n+2)^2`" -- to
  `truthTable_ge`.

`eq:paper-g-little-o` (label line 312) remains **unclaimed**, as it was in the
`cc-t1t-r1` and `cc-t1u` cells: it is the limit statement `g(n) = o(n)` whose
proof is the prefix-maximum argument of frozen lines 796--807, and this module
takes that statement as a hypothesis rather than landing it (GAP-EXPOSED 2).

**Claiming no reader item** (autoformalization-only content -- the reader
prints neither the exponent as an object, nor the rounding agreement, nor the
ceiling estimate, nor `S_n >= n + 2` as a separate display):
`truthTableExponent`, `truthTable_pow`, `truthTableExponent_no_rounding`,
`truthTableExponent_logb`, `truthTablePairIsBitStrings`,
`paddedTruthTableLength`, `carrierEntriesFitTruthTable`,
`ceilingPowerSandwich`, `ceilingSandwich`, `sublinearSum`, `commonSquare_ge`,
`truthTableExponent_monotone`, `truthTableExponent_unbounded`,
`truthTableExponent_positive`, and every declaration of Parts 7 and 8.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: **this module introduces no structure at all**, so no constructor
  can carry a conclusion.  The one conditional deliverable,
  `truthTableExponent_sublinear`, takes its two frozen inputs as **explicit
  binders**, never as a premise bundle, and neither binder restates a derived
  telescope: `4 m g(n) <= n` and `4 m ceil(log_2(n+2)) <= n` are logically
  independent (the first is not landed anywhere in the route, the second is a
  numerical fact about `n` alone).
* `M7`: no carrier is introduced here, and the nonemptiness facts of
  `step:I-11` are consumed only through the banked `CommonPadding` statements,
  which carry them as fields.
* `M9`: the frozen ceiling is `Nat.clog`, never `Nat.log`.  The floor spelling
  is refuted for this role in the kernel by the banked
  `PaddingAndClock.floorLogarithm_breaks_the_ceiling_sandwich`, and
  `floorAndCeilingDisagreeInGeneral` records here that the two really are
  different functions.
* Zero-based slots (`conv:finite-slots`) are untouched: every index type below
  is `Fin S` or `Fin (e(n)) → Bool`.
* Both interlace widths `q` and `Q` are untouched: `step:I-12` runs strictly
  after the last level, so no interlace appears in this module and none is
  renamed or re-derived.

## GAP-EXPOSED (what this module deliberately does not claim)

1. **The machine layer is out of scope, explicitly.**  Nothing here models the
   canonical environment `M_*`, `A_cert`, `A_raw`, `tau_k`,
   `thm:effective-materialization`, `cor:realized-effective-prefix`, or
   `eq:total-construction-time`.  In particular the reader's next sentence,
   `06-eth.tex:346--347` ("constructing every intermediate level and writing
   the `T_n` output bits takes `2^{o(n)}` time"), is **not** claimed, and no
   computability or runtime claim is made about `e`, `S`, `T` or the emitted
   truth table.
2. **`g(n) = o(n)` is not landed, and is not silently assumed either.**  The
   frozen proof of `log_2 T_n = o(n)` consumes three inputs at line 908; the
   second (`log_2(n+2) = o(n)`) and the third (`1 = o(n)`) are elementary and
   appear below in finite form, but the first is the prefix-maximum limit
   argument of frozen lines 796--807, which `CLOCK-001` records as **not
   landed**.  It is therefore the explicit binder `hg` of
   `truthTableExponent_sublinear`, never an axiom, never a structure field and
   never a hidden `simp` fact.  The **limit form** of the frozen conclusion --
   `log_2 T_n = o(n)` as a statement about a filter -- is correspondingly
   **GAP-EXPOSED**: what is landed is the frozen finite multiplicative
   inequality at a single index, exactly as `slowClock_sublinear` and
   `zhat_sublinear` are.
3. **The matrix is still arbitrary.**  As in `CommonPadding`, nothing below
   asserts that the padded matrix is the level-`L(n)` output `R_k(I)`; the
   carrier bounds of frozen lines 815--818 remain named hypotheses.
4. **Nothing is claimed about the promise case.**  Frozen lines 911--913 say
   only that these numbers are fixed *before* the promise case is analysed;
   the analysis itself is `sec:final-consequence` and is untouched.
5. **The approximation allowance is not landed.**  `eq:paper-alpha`
   (`06-eth.tex`, label line 358) and the function `p(T)` are `ALPHA`-side
   content; only the frozen fact that makes its search terminate,
   `T_n >= (n+2)^2`, is landed here, and no `p` or `alpha` is defined.
6. **No route completion is claimed.**  `step:I-12` is one mechanical step of
   Section 13; the headline theorem of the route is not in Lean.

## Reading notes

* **N1 (why `log_2 T_n` is an integer at all).**  The frozen text writes
  `log_2 T_n` with no rounding decoration because `T_n = 2^{2e(n)}` is an
  exact power of two.  That is the whole content of the headline "no
  suppressed floor or ceiling term", and it is why the exponent is landed as a
  `ℕ` and the two integer logarithms are *proved* to agree with it rather than
  one of them being chosen by fiat.
* **N2 (the ceiling estimate is a finite sandwich, not an asymptotic).**
  Frozen lines 903--907 are a two-sided bound at a single `n`.  It is landed
  twice, once over `ℕ` (`ceilingPowerSandwich`, the form every other statement
  in the route consumes) and once over `ℝ` (`ceilingSandwich`, the literal
  frozen display).  The `ℝ` version uses `Real.logb` for the *bound only*; it
  is not used to define anything, and no limit is taken.
* **N3 (the multiplier `m` is the frozen "dividing by `n`").**  Frozen line 908
  divides `expi:E-12-log` by `n`.  Over `ℕ` that is transcribed
  multiplicatively -- `natDivision_is_not_the_frozen_conclusion` in
  `PaddingAndClock` already refutes the truncated-division spelling for the
  sibling estimate -- so "`log_2 T_n / n` is eventually below `1/m`" becomes
  `m * log_2 T_n <= n`, and the two hypotheses are the same reading of the two
  summands at the same `m`.  The constant `4` is exactly the two factors of
  `2` in `expi:E-12-log` times the two summands, and nothing is rounded.

## Candidate encodings and ranking (NOVEL-concept protocol)

Two encodings of the truth-table exponent were written and run against the
same aux-lemma battery before landing.

* **Candidate A (landed).**  `truthTableExponent V n : ℕ := 2 * eCommon V n`
  -- the frozen middle term of `expi:E-12-log`, valued in `ℕ`.
* **Candidate B (rejected).**  `Real.logb 2 (tCommon V n) : ℝ` -- the literal
  real logarithm as the *definition*.

Ranking.  Battery (the five general lemmas marked **Aux 1**--**Aux 5** below):
A proved 5/5.  B proved 3/5: it cannot state **Aux 3** (the rounding
agreement, which is a statement about `Nat.log` and `Nat.clog` and has no
`ℝ`-valued shadow -- see `floorAndCeilingDisagreeInGeneral`), and it cannot
state **Aux 5** in the route's finite multiplicative `ℕ` form without a cast
at every use site, so every banked consumer (`frozenPaddedEntryCount`,
`carrierFitsCommonSquare_of_zhat`, `commonSizeParameters`) would have to be
re-cast.  Faithfulness: `Real.logb` is junk-valued off the frozen regime --
`logbCandidate_is_junk_off_the_frozen_regime` records
`logb 2 0 = logb 2 1 = 0` in the kernel -- so B's definition alone does not
determine the table length, whereas A's does
(`truthTableExponent_determines_length`).  Length: A needs no cast anywhere;
B needs one per statement.  Candidate A wins on all three axes and is landed,
and B's single genuine content -- that the real logarithm is this same number
-- survives as the *theorem* `truthTableExponent_logb`, so nothing B could say
correctly is lost.

## Statement poles

* `truthTable_unbounded` and `truthTableExponent_unbounded` are the only
  existential deliverables.  The trivial witness fails them: no *fixed* index
  works, because `unboundedness_has_no_uniform_witness` exhibits, for every
  `n`, a bound `B` that `tCommon V n` does not reach.  The existential is
  therefore genuinely over the index, which is what "tends to infinity" means
  at `06-eth.tex:351`.
* `truthTableExponent_sublinear` is a conditional, and its pole is vacuity:
  `sublinear_hypotheses_consistent` inhabits its whole binder list at a legal
  gate-satisfying clock with a multiplier `m = 2 > 0` and a conclusion
  `2 * log_2 T_{2^63} <= 2^63` whose left side is proved positive, so the
  bundle is consistent and the conclusion is not `0 <= n` in disguise.
-/

namespace EthInapproximability.ParameterizedNP.TruthTableExponent

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.PaddingAndClock

/-! ## Part 1: the common truth-table exponent (`expi:E-12-log`) -/

/-- **The common truth-table exponent `log_2 T_n`** -- the middle term of
`expi:E-12-log` (`13-iteration-assembly.tex`, label line 900, display lines
896--901): `log_2 T_n = 2 e(n)`.

Valued in `ℕ`, with no rounding decoration, because `T_n = 2^{2 e(n)}` is an
exact power of two (reading note N1).  `truthTableExponent_no_rounding` and
`truthTableExponent_logb` are what make that a claim rather than a convention.

Claims no reader item: the reader prints the exponent only inside
`eq:paper-table-subexponential`, whose two clauses go to
`truthTableExponent_eq` and `truthTableExponent_sublinear`. -/
noncomputable def truthTableExponent (V : ℕ → ℕ) (n : ℕ) : ℕ := 2 * eCommon V n

/-- **The right-hand equality of `expi:E-12-log`**
(`13-iteration-assembly.tex:896--901`):
`log_2 T_n = 2 g(n) + 2 ceil(log_2(n+2))`.

Both frozen coefficients are the literal `2`, and the ceiling is `Nat.clog`,
which is the frozen `ceil(log_2 .)` of `eq:common-size`
(`12-iteration-specification.tex`, label line 628).  General in the clock and
the source size.

Reader counterpart: the **equality** clause of `eq:paper-table-subexponential`
(`06-eth.tex`, label line 344, display line 343),
`log T_n = 2 g(n) + 2 ceil(log(n+2))`.  Its `= o(n)` clause is claimed
separately by `truthTableExponent_sublinear` and by nothing else. -/
theorem truthTableExponent_eq (V : ℕ → ℕ) (n : ℕ) :
    truthTableExponent V n = 2 * gMaj V n + 2 * Nat.clog 2 (n + 2) := by
  simp [truthTableExponent, eCommon, Nat.mul_add]

/-- **`T_n = 2^{log_2 T_n}`** -- frozen lines 891--894,
`T_n = S_n^2 = (2^{e(n)})^2 = 2^{2 e(n)}`, read at the new exponent name.

This consumes the banked `PaddingAndClock.commonSizeParameters` (the third
conjunct `T_n = 2^{2 e(n)}`) and adds nothing to it; every statement below
that mentions `tCommon` goes through this rewrite.  General in the clock and
the source size.  Claims no reader item -- `06-eth.tex:319`'s second equality
is `commonSizeParameters`'s item. -/
theorem truthTable_pow (V : ℕ → ℕ) (n : ℕ) :
    tCommon V n = 2 ^ truthTableExponent V n := by
  simpa [truthTableExponent] using (commonSizeParameters V n).2.2

/-- **Aux 3 (the headline: no suppressed floor or ceiling term).**

Frozen lines 886--888: "The common truth-table exponent and its subexponential
bound contain no suppressed floor or ceiling term."  The exact content of that
sentence, at the truth-table length, is that the **floor** logarithm and the
**ceiling** logarithm of `T_n` are the *same* number, and that this number is
the frozen `2 e(n)`.  Neither rounding convention is chosen: both are proved.

That this is a claim and not a tautology is recorded in the kernel by
`floorAndCeilingDisagreeInGeneral`.  General in the clock and the source size.
Claims no reader item. -/
theorem truthTableExponent_no_rounding (V : ℕ → ℕ) (n : ℕ) :
    Nat.log 2 (tCommon V n) = truthTableExponent V n ∧
      Nat.clog 2 (tCommon V n) = truthTableExponent V n := by
  rw [truthTable_pow]
  exact ⟨Nat.log_pow (by norm_num) _, Nat.clog_pow 2 _ (by norm_num)⟩

/-- **The real logarithm is the same number** -- the literal reading of the
symbol `log_2 T_n` in `expi:E-12-log`.

This is the one thing Candidate B (a real-valued *definition*) could have said
correctly, kept here as a theorem about the pinned `ℕ`-valued construction, so
nothing is lost by rejecting that encoding.  `Real.logb` is used for the value
only; nothing is defined by it and no limit is taken.  General in the clock and
the source size.  Claims no reader item. -/
theorem truthTableExponent_logb (V : ℕ → ℕ) (n : ℕ) :
    Real.logb 2 (tCommon V n : ℝ) = (truthTableExponent V n : ℝ) := by
  rw [truthTable_pow]
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  ring

/-! ## Part 2: the `e(n)`-bit reading, and the banked padded matrix -/

/-- **"a Boolean function on two `e(n)`-bit inputs"**, the side half --
frozen line 889.

One side of the padded square is the set of `e(n)`-bit strings, and it has
exactly `S_n` elements.  General in the clock and the source size.

Reader counterpart: the **first** clause of `06-eth.tex:340`, "The padded
matrix is a Boolean function on two `e(n)`-bit inputs".  The second clause of
that sentence belongs to `CommonPadding.frozenPaddedEntryCount` and is not
re-claimed. -/
theorem sideIsBitStrings (V : ℕ → ℕ) (n : ℕ) :
    Fintype.card (Fin (eCommon V n) → Bool) = sCommon V n := by
  simp [sCommon]

/-- **"a Boolean function on two `e(n)`-bit inputs"**, the pair half --
frozen lines 889--894.

The index set of the truth table is a pair of `e(n)`-bit strings, and it has
exactly `2^{log_2 T_n}` elements.  General in the clock and the source size.
Claims no reader item. -/
theorem truthTablePairIsBitStrings (V : ℕ → ℕ) (n : ℕ) :
    Fintype.card ((Fin (eCommon V n) → Bool) × (Fin (eCommon V n) → Bool))
      = 2 ^ truthTableExponent V n := by
  simp [truthTableExponent, ← pow_add, two_mul]

/-- **The banked padded entry count, at the new exponent name** -- frozen lines
889--894 together with `step:I-11`.

`CommonPadding.frozenPaddedEntryCount` states that the padded matrix has
`tCommon V n` entries; `truthTable_pow` turns that into `2^{log_2 T_n}`.  This
declaration adds no mathematics -- it is the rewrite that lets `step:I-12`
consume `step:I-11` -- and therefore claims **no** reader item: the sentence
"every branch has the same truth-table length `T_n`" (`06-eth.tex:340--341`)
is the banked theorem's item.  General in the clock and the source size. -/
theorem paddedTruthTableLength (V : ℕ → ℕ) (n : ℕ) :
    Fintype.card (Fin (sCommon V n) × Fin (sCommon V n))
      = 2 ^ truthTableExponent V n := by
  rw [CommonPadding.frozenPaddedEntryCount V n, truthTable_pow]

/-- **The unpadded entry count fits inside the truth table** -- frozen lines
815--818 and 889--894, through `step:I-11`.

The frozen carrier bounds `|X| <= 2^{g(n)}` are **named hypotheses**, exactly
as they are in `CommonPadding`, because `step:I-07` is not landed here; the
form used is the pointwise one at `zhat V n`, so the banked
`CommonPadding.carrierFitsCommonSquare_of_zhat` (with its live `1 <= n` fold
guard) is what does the lifting to the prefix maximum and then to the common
square.  General in the clock, the source size `n >= 1` and both carriers.
Claims no reader item. -/
theorem carrierEntriesFitTruthTable {X Y : Type*} [Fintype X] [Fintype Y]
    (V : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hX : Fintype.card X ≤ 2 ^ zhat V n) (hY : Fintype.card Y ≤ 2 ^ zhat V n) :
    Fintype.card X * Fintype.card Y ≤ 2 ^ truthTableExponent V n := by
  have hx := CommonPadding.carrierFitsCommonSquare_of_zhat (X := X) V n hn hX
  have hy := CommonPadding.carrierFitsCommonSquare_of_zhat (X := Y) V n hn hY
  have hprod : Fintype.card X * Fintype.card Y ≤ sCommon V n * sCommon V n :=
    Nat.mul_le_mul hx hy
  have hsq : sCommon V n * sCommon V n = tCommon V n := by
    simp [tCommon, pow_two]
  rw [← truthTable_pow, ← hsq]
  exact hprod

/-! ## Part 3: the ceiling estimate (frozen lines 902--907) -/

/-- **Aux 4 (the ceiling sandwich, exponentiated).**

The integer content of frozen lines 903--907,
`log_2(n+2) <= ceil(log_2(n+2)) < log_2(n+2) + 1`: the ceiling is at least
`1`, and `n + 2` sits strictly above the previous power of two and at or below
its own.  Stated over `ℕ` because that is the form every other statement in
the route consumes; the literal real display is `ceilingSandwich`.

General in `n`, including `n = 0`, where `n + 2 = 2` and the ceiling is `1`.
Claims no reader item. -/
theorem ceilingPowerSandwich (n : ℕ) :
    1 ≤ Nat.clog 2 (n + 2) ∧ 2 ^ (Nat.clog 2 (n + 2) - 1) < n + 2 ∧
      n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := by
  refine ⟨Nat.clog_pos (by norm_num) (by omega), ?_,
    Nat.le_pow_clog (by norm_num) _⟩
  simpa [Nat.pred_eq_sub_one] using
    Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n + 2) (by omega)

/-- **The ceiling estimate as the literal frozen display** -- frozen lines
902--907, "The ceiling contributes less than one extra unit:
`log_2(n+2) <= ceil(log_2(n+2)) < log_2(n+2) + 1`."

A two-sided bound at a single `n` (reading note N2).  `Real.logb` appears here
only as the value being bounded; no limit is taken and nothing is defined by
it.  General in `n`.  Claims no reader item -- the reader does not print this
estimate. -/
theorem ceilingSandwich (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 2) ≤ (Nat.clog 2 (n + 2) : ℝ) ∧
      (Nat.clog 2 (n + 2) : ℝ) < Real.logb 2 ((n : ℝ) + 2) + 1 := by
  obtain ⟨hpos, hlt, hle⟩ := ceilingPowerSandwich n
  have hb : (1 : ℝ) < 2 := by norm_num
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  constructor
  · have hcast : ((n : ℝ) + 2) ≤ (2 : ℝ) ^ Nat.clog 2 (n + 2) := by
      have h := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at h
      exact h
    have h := Real.logb_le_logb_of_le hb hxpos hcast
    rwa [Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at h
  · have hcast : (2 : ℝ) ^ (Nat.clog 2 (n + 2) - 1) < (n : ℝ) + 2 := by
      have h := (Nat.cast_lt (α := ℝ)).2 hlt
      push_cast at h
      exact h
    have hp : (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 (n + 2) - 1) := by positivity
    have h := Real.logb_lt_logb hb hp hcast
    rw [Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at h
    have hsub : ((Nat.clog 2 (n + 2) - 1 : ℕ) : ℝ)
        = (Nat.clog 2 (n + 2) : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ Nat.clog 2 (n + 2) := hpos
      push_cast [Nat.cast_sub h1]
      ring
    rw [hsub] at h
    linarith

/-! ## Part 4: the subexponential clause (frozen lines 908--909) -/

/-- **Aux 5 (the frozen division step, as pure arithmetic).**

Frozen line 908 divides `expi:E-12-log` by `n`.  Over `ℕ` that is transcribed
multiplicatively (reading note N3): if each of the two summands is below
`n/(4m)`, then the whole exponent `2 g + 2 c` is below `n/m`.  The constant `4`
is the two coefficients `2` of `expi:E-12-log` times the two summands; nothing
is rounded and nothing is estimated.

General in all four arguments, including the degenerate `m = 0`.  Its
hypothesis pair is consistent at nondegenerate values -- `m = 2`, `g = 3`,
`c = 1`, `n = 32` satisfies both and yields the nontrivial `16 <= 32`.  Claims
no reader item. -/
theorem sublinearSum (m g c n : ℕ) (hg : 4 * m * g ≤ n) (hc : 4 * m * c ≤ n) :
    m * (2 * g + 2 * c) ≤ n := by
  have hdouble : 2 * (m * (2 * g + 2 * c)) ≤ 2 * n := by
    have hrw : 2 * (m * (2 * g + 2 * c)) = 4 * m * g + 4 * m * c := by ring
    rw [hrw]
    calc 4 * m * g + 4 * m * c ≤ n + n := Nat.add_le_add hg hc
      _ = 2 * n := by ring
  exact Nat.le_of_mul_le_mul_left hdouble (by norm_num)

/-- **`log_2 T_n = o(n)`, in the frozen finite multiplicative form at a single
index** -- frozen lines 908--909, "Since `g(n) = o(n)`, `log_2(n+2) = o(n)`,
and `1 = o(n)`, dividing `expi:E-12-log` by `n` proves `log_2 T_n = o(n)`."

The two frozen inputs are **explicit binders**, not a premise bundle and not a
structure:

* `hg` is the frozen `g(n) = o(n)` of line 908, whose proof is the
  prefix-maximum limit argument of lines 796--807.  `CLOCK-001` records that
  argument as **not landed**, so it is a hypothesis here rather than a derived
  fact (GAP-EXPOSED 2).  It is *not* the banked `zhat_sublinear`, which bounds
  the pointwise majorant and runs the wrong way against `zhat V n <= g(n)`.
* `hc` is the frozen `log_2(n+2) = o(n)` of line 908, in the same finite form.

The third input `1 = o(n)` is absorbed: `expi:E-12-log` has no additive
constant, so the frozen "and `1 = o(n)`" is the slack already carried by the
ceiling, which `ceilingSandwich` bounds by one unit.

Kept in the frozen **finite-inequality** form, at a single index `m`, with no
`Filter.Tendsto` and no asymptotic order relation anywhere -- exactly as
`slowClock_sublinear` and `zhat_sublinear` are (`CLOCK-001` GAP-EXPOSED 4, and
the `SIZE-001` precedent).  The **limit form** of the frozen conclusion is
correspondingly GAP-EXPOSED.  General in the clock, the multiplier and the
source size; the binder list is inhabited nondegenerately at a legal
gate-satisfying clock by `sublinear_hypotheses_consistent`.

Reader counterpart: the **`= o(n)` clause** of `eq:paper-table-subexponential`
(`06-eth.tex`, label line 344, display line 343).  Its equality clause is
`truthTableExponent_eq`'s item and is not re-claimed. -/
theorem truthTableExponent_sublinear (V : ℕ → ℕ) (m n : ℕ)
    (hg : 4 * m * gMaj V n ≤ n)
    (hc : 4 * m * Nat.clog 2 (n + 2) ≤ n) :
    m * truthTableExponent V n ≤ n := by
  rw [truthTableExponent_eq]
  exact sublinearSum m (gMaj V n) (Nat.clog 2 (n + 2)) n hg hc

/-! ## Part 5: the lower bounds (frozen lines 909--911) -/

/-- **`S_n >= n + 2`** -- frozen lines 909--911, "Finally,
`2^{ceil(log_2(n+2))} >= n + 2`, so `S_n >= n + 2`".

The frozen implication uses only `g(n) >= 0`, so it holds for every clock.
General in the clock and the source size.  Claims no reader item: the reader
prints only the squared consequence, at line 360. -/
theorem commonSquare_ge (V : ℕ → ℕ) (n : ℕ) : n + 2 ≤ sCommon V n := by
  have h1 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) _
  have hexp : Nat.clog 2 (n + 2) ≤ eCommon V n := by
    simp [eCommon]
  have h2 : (2 : ℕ) ^ Nat.clog 2 (n + 2) ≤ 2 ^ eCommon V n :=
    Nat.pow_le_pow_right (by norm_num) hexp
  simpa [sCommon] using le_trans h1 h2

/-- **`T_n >= (n+2)^2`** -- frozen lines 910--911, "so `S_n >= n + 2` and
`T_n >= (n+2)^2`".

General in the clock and the source size.

Reader counterpart: `06-eth.tex:360`, "The search for `p(T)` terminates
because `T_n >= (n+2)^2`."  The reader states it as the termination reason for
`p`; `p` itself is not defined here (GAP-EXPOSED 5). -/
theorem truthTable_ge (V : ℕ → ℕ) (n : ℕ) : (n + 2) ^ 2 ≤ tCommon V n := by
  have h := commonSquare_ge V n
  simpa [tCommon] using Nat.pow_le_pow_left h 2

/-! ## Part 6: growth (the aux battery's monotonicity and unboundedness) -/

/-- **Aux 2 (the exponent is nondecreasing).**

Both summands of `expi:E-12-log` are nondecreasing in `n`: the prefix maximum
by the banked `gMaj_spec`, and the ceiling by monotonicity of `Nat.clog`.
General in the clock and the source size.  Claims no reader item. -/
theorem truthTableExponent_monotone (V : ℕ → ℕ) (n : ℕ) :
    truthTableExponent V n ≤ truthTableExponent V (n + 1) := by
  have h1 : gMaj V n ≤ gMaj V (n + 1) := (gMaj_spec V).2 n
  have h2 : Nat.clog 2 (n + 2) ≤ Nat.clog 2 (n + 1 + 2) :=
    Nat.clog_mono_right 2 (by omega)
  rw [truthTableExponent_eq, truthTableExponent_eq]
  omega

/-- **`T_n` is nondecreasing** -- the growth-exercising half of the reader's
sentence at `06-eth.tex:351`, "The sequence `T_n` is nondecreasing and tends to
infinity".

General in the clock and the source size.  Reader counterpart: the
*nondecreasing* clause of line 351; its *tends to infinity* clause is
`truthTable_unbounded`'s item and is not re-claimed. -/
theorem truthTable_monotone (V : ℕ → ℕ) (n : ℕ) :
    tCommon V n ≤ tCommon V (n + 1) := by
  rw [truthTable_pow, truthTable_pow]
  exact Nat.pow_le_pow_right (by norm_num) (truthTableExponent_monotone V n)

/-- **`T_n` tends to infinity** -- the second clause of `06-eth.tex:351`,
exercised through the frozen `T_n >= (n+2)^2` of lines 910--911.

Statement pole: no *fixed* index witnesses this.
`unboundedness_has_no_uniform_witness` exhibits, for every `n`, a bound the
value at `n` fails, so the existential is genuinely over the index.  General in
the clock and the bound. -/
theorem truthTable_unbounded (V : ℕ → ℕ) (B : ℕ) : ∃ n, B ≤ tCommon V n := by
  refine ⟨B, le_trans ?_ (truthTable_ge V B)⟩
  calc B ≤ B + 2 := by omega
    _ ≤ (B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _

/-- **The exponent tends to infinity too** -- the same growth read through
`truthTable_pow`, so the *exponent* and not merely the length is unbounded.

This is what makes the subexponential clause a real constraint: an exponent
that stayed bounded would satisfy `truthTableExponent_sublinear` for trivial
reasons at every large `n`.  General in the clock and the bound.  Claims no
reader item. -/
theorem truthTableExponent_unbounded (V : ℕ → ℕ) (B : ℕ) :
    ∃ n, B ≤ truthTableExponent V n := by
  refine ⟨2 ^ B, ?_⟩
  have h1 : (2 : ℕ) ^ B + 2 ≤ sCommon V (2 ^ B) := commonSquare_ge V (2 ^ B)
  have h2 : sCommon V (2 ^ B) = 2 ^ eCommon V (2 ^ B) := rfl
  have h3 : (2 : ℕ) ^ B < 2 ^ eCommon V (2 ^ B) := by omega
  have h4 : B < eCommon V (2 ^ B) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  rw [truthTableExponent]
  omega

/-- **The exponent is never zero.**

`e(n) >= ceil(log_2(n+2)) >= 1` for every `n`, so the truth table always has at
least four entries and the conclusion of `truthTableExponent_sublinear` is
never the trivial `0 <= n`.  General in the clock and the source size.  Claims
no reader item. -/
theorem truthTableExponent_positive (V : ℕ → ℕ) (n : ℕ) :
    1 ≤ truthTableExponent V n := by
  have hpos : 0 < Nat.clog 2 (n + 2) :=
    Nat.clog_pos (by norm_num) (by omega)
  rw [truthTableExponent_eq]
  omega

/-! ## Part 7: non-vacuity and hypothesis consistency -/

/-- **Aux 1 (a uniform pointwise bound dominates the prefix maximum).**

The converse direction of the banked `gMaj_spec`: `g(n) = max_{1 <= m <= n}
zhat(m)` (`eq:uniform-size-majorant`,
`12-iteration-specification.tex:596`) is below `B` as soon as every term in the
frozen index range is.  The lower guard `1 <= m` is the frozen index range and
is live: `gMaj V 0 = 0` needs no hypothesis at all.

General in the clock, the source size and the bound.  Claims no reader item. -/
theorem gMaj_le_of_forall (V : ℕ → ℕ) (n B : ℕ)
    (h : ∀ m, 1 ≤ m → m ≤ n → zhat V m ≤ B) : gMaj V n ≤ B := by
  induction n with
  | zero => simp [gMaj]
  | succ p ih =>
    have hp : gMaj V p ≤ B := ih (fun m h1 h2 => h m h1 (by omega))
    have hz : zhat V (p + 1) ≤ B := h (p + 1) (by omega) le_rfl
    simp only [gMaj, max_le_iff]
    exact ⟨hp, hz⟩

/-- **The prefix maximum at `n = 1` is the pointwise majorant there.**

An immediate consequence of the frozen fold range `1 <= m <= n`, used to reuse
the banked `CommonPadding.witnessClock_gMaj` as a bound on `zhat`.  General in
the clock.  Claims no reader item. -/
theorem gMaj_one (V : ℕ → ℕ) : gMaj V 1 = zhat V 1 := by simp [gMaj]

/-- **Every gate-satisfying clock has index `0` below `2^64`.**

Frozen line 675 gates the clock by `V_k >= 2^{2^{T_k}}` for `k >= 1`, and the
banked `tk_ge` gives `T_k >= 124`, so `V_k >= 2^{2^{124}} >= 2^{64}` for every
positive `k`.  Hence no positive index is feasible at any source size below
`2^64`, and the frozen maximum `L(n) = max({0} ∪ {k <= n : V_k <= n})` is `0`
there.

This is not a statement about one pinned clock: it holds for **every** clock
satisfying `SlowClockGateSet`, and `witnessClock_gates` inhabits that
structure.  General in the clock, the cutoff function and the source size.
Claims no reader item. -/
theorem slowIndex_eq_zero_of_lt {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    (m : ℕ) (hm : m < 2 ^ 64) : slowIndex V m = 0 := by
  simp only [slowIndex]
  refine Nat.findGreatest_eq_zero_iff.2 ?_
  intro k hk _ hle
  have h1 : (64 : ℕ) ≤ 2 ^ Tk k := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ Tk k := Nat.pow_le_pow_right (by norm_num) (by
          have := tk_ge k hk
          omega)
  have h2 : (2 : ℕ) ^ 64 ≤ 2 ^ 2 ^ Tk k := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 2 ^ 2 ^ Tk k ≤ V k := hg.threshold_gate k hk
  have : m < V k := lt_of_lt_of_le hm (le_trans h2 h3)
  omega

/-- **The envelope index is at most `6` below `2^63`.**

`l(n)` is the least `r >= 2` with `n + 16 <= 2^{2^r}`
(`13-iteration-assembly.tex:248--249`), so `r = 6` is already feasible at every
`n <= 2^63`, since `2^{2^6} = 2^{64}`.  General in `n` under that bound.
Claims no reader item. -/
theorem ellN_le_six (m : ℕ) (hm : m ≤ 2 ^ 63) : ellN m ≤ 6 := by
  have hp : 2 ≤ 6 ∧ m + 16 ≤ 2 ^ 2 ^ 6 := by
    refine ⟨by norm_num, ?_⟩
    have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
    have h64 : (2 : ℕ) ^ 2 ^ 6 = 18446744073709551616 := by norm_num
    omega
  simpa [ellN] using Nat.find_le (h := ellN_exists m) hp

/-- **The seed majorant is uniformly bounded below `2^63`.**

`z_seed(m) = q_seed(m) + a_seed(m)` (`13-iteration-assembly.tex:763`) with the
banked `qSeed_le` (`q_seed(m) <= 128 B(m) + 128`) and `aSeed_bounds`
(`a_seed(m) <= B(m)`), and `B(m) = E_2(m) = 2^{l(m)^2} <= 2^{36}` by
`ellN_le_six`.  General in `1 <= m <= 2^63`.  Claims no reader item. -/
theorem seedMajorant_le (m : ℕ) (h1 : 1 ≤ m) (hm : m ≤ 2 ^ 63) :
    zSeed m ≤ 129 * 2 ^ 36 + 128 := by
  have hell : ellN m ≤ 6 := ellN_le_six m hm
  have hsq : ellN m ^ 2 ≤ 36 := by nlinarith
  have hdepth : depthB m ≤ 2 ^ 36 := by
    simpa [depthB, envE] using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hsq
  have hq := qSeed_le m h1
  have ha := (aSeed_bounds m h1).2
  have h36 : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
  simp only [zSeed]
  omega

/-- **The uniform size majorant of every gate-satisfying clock is small at
`n = 2^63`.**

Combining `gMaj_le_of_forall`, `slowIndex_eq_zero_of_lt` (so `zhat` takes its
frozen seed branch throughout the fold range) and `seedMajorant_le`.  General
in the clock and the cutoff function.  Claims no reader item. -/
theorem gMaj_le_of_gates {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) :
    gMaj V (2 ^ 63) ≤ 129 * 2 ^ 36 + 128 := by
  refine gMaj_le_of_forall V (2 ^ 63) _ (fun m h1 h2 => ?_)
  have hlt : m < 2 ^ 64 := by
    have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
    have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    omega
  have h0 : slowIndex V m = 0 := slowIndex_eq_zero_of_lt hg m hlt
  have hz : zhat V m = zSeed m := by simp [zhat, h0]
  rw [hz]
  exact seedMajorant_le m h1 h2

/-- **Hypothesis consistency for `truthTableExponent_sublinear`, at a legal
gate-satisfying clock** (LANE-GATE 3, and the `cc-t1p` lesson that every gate
can pass while the principal deliverable is vacuous).

`PaddingAndClock.witnessClock` satisfies all four frozen gates of
`13-iteration-assembly.tex:653--676` -- that is the banked `witnessClock_gates`
-- so it is a **legal** clock, not a toy.  At the source size `n = 2^63` and
the multiplier `m = 2` both binders of `truthTableExponent_sublinear` hold
simultaneously, so no `False` follows from the pair, and the conclusion it
yields there is genuinely nontrivial: the fifth conjunct proves the left-hand
side positive, so the conclusion is not `0 <= n` in disguise.

The multiplier is `2` and not `1` deliberately: a bundle satisfiable only at
`m = 0` would be degenerate, and the frozen "dividing by `n`" reading is
vacuous at `m = 0`.  General in the cutoff function. -/
theorem sublinear_hypotheses_consistent (nstep : ℕ → ℕ) :
    SlowClockGateSet (witnessClock nstep) nstep ∧
      4 * 2 * gMaj (witnessClock nstep) (2 ^ 63) ≤ 2 ^ 63 ∧
      4 * 2 * Nat.clog 2 (2 ^ 63 + 2) ≤ 2 ^ 63 ∧
      2 * truthTableExponent (witnessClock nstep) (2 ^ 63) ≤ 2 ^ 63 ∧
      1 ≤ truthTableExponent (witnessClock nstep) (2 ^ 63) := by
  have hgates := witnessClock_gates nstep
  have h36 : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
  have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have hg : 4 * 2 * gMaj (witnessClock nstep) (2 ^ 63) ≤ 2 ^ 63 := by
    have h := gMaj_le_of_gates hgates
    omega
  have hc : 4 * 2 * Nat.clog 2 (2 ^ 63 + 2) ≤ 2 ^ 63 := by
    have h : Nat.clog 2 (2 ^ 63 + 2) ≤ 64 := by
      refine Nat.clog_le_of_le_pow ?_
      have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
      omega
    omega
  exact ⟨hgates, hg, hc,
    truthTableExponent_sublinear (witnessClock nstep) 2 (2 ^ 63) hg hc,
    truthTableExponent_positive _ _⟩

/-- **Hypothesis consistency for `carrierEntriesFitTruthTable`, at a banked
route object.**

The Part-2 binder list -- `1 <= n` together with both frozen carrier bounds at
`zhat V n` -- is inhabited at the clock the `cc-t1u` tranche already pinned for
exactly this purpose, at `n = 1`, with carriers of **four** elements each.  The
banked `CommonPadding.witnessClock_gMaj` gives `g(1) >= 67`, and `gMaj_one`
turns that into a bound on `zhat` at the same index, so both carrier bounds
hold with room to spare.

Nondegenerate in the sense that matters: the carriers have more than one
element, so the product bound is not `1 <= 2^k`.  Claims no reader item. -/
theorem carrierEntries_hypotheses_consistent :
    67 ≤ zhat CommonPadding.witnessClock 1 ∧
      Fintype.card (Fin 4) * Fintype.card (Fin 4)
        ≤ 2 ^ truthTableExponent CommonPadding.witnessClock 1 ∧
      1 < Fintype.card (Fin 4) := by
  have hz : 67 ≤ zhat CommonPadding.witnessClock 1 := by
    have h := CommonPadding.witnessClock_gMaj
    rwa [gMaj_one] at h
  refine ⟨hz, ?_, by simp⟩
  have hfit : Fintype.card (Fin 4) ≤ 2 ^ zhat CommonPadding.witnessClock 1 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    have hmono : (2 : ℕ) ^ 2 ≤ 2 ^ zhat CommonPadding.witnessClock 1 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [h4] using hmono
  exact carrierEntriesFitTruthTable (X := Fin 4) (Y := Fin 4)
    CommonPadding.witnessClock 1 le_rfl hfit hfit

/-! ## Part 8: statement poles and the refuted candidate -/

/-- **Statement pole: the rounding agreement of `truthTableExponent_no_rounding`
is a real claim.**

The floor and ceiling logarithms are genuinely different functions -- at
`t = 6` they return `2` and `3` -- so proving that they agree at `T_n` is
content, not a tautology.  It is exactly the frozen headline "no suppressed
floor or ceiling term" of lines 886--888, and it holds at `T_n` only because
`T_n` is an exact power of two.  Recorded in the kernel rather than in prose,
because an over-strong or empty claim typechecks perfectly. -/
theorem floorAndCeilingDisagreeInGeneral : Nat.log 2 6 ≠ Nat.clog 2 6 := by
  norm_num [Nat.log, Nat.clog]

/-- **The exponent determines the truth-table length.**

If `T_n` is any power of two, the exponent is forced to be the landed one.
This is the property Candidate B lacks: a real-valued definition would not pin
the length, because `Real.logb` is junk-valued off the frozen regime.  General
in the clock, the source size and the exponent.  Claims no reader item. -/
theorem truthTableExponent_determines_length (V : ℕ → ℕ) (n k : ℕ)
    (h : tCommon V n = 2 ^ k) : k = truthTableExponent V n := by
  have h2 : (2 : ℕ) ^ k = 2 ^ truthTableExponent V n := by
    rw [← h, truthTable_pow]
  exact Nat.pow_right_injective (le_refl 2) h2

/-- **Candidate B refuted: the real-valued definition is junk off the frozen
regime.**

Candidate B defines the exponent as `Real.logb 2 T_n`.  That function assigns
the *same* value `0` to a table with no entries and to a table with one entry,
so the definition alone does not determine the table length; Candidate A's does
(`truthTableExponent_determines_length`).  Kept in the kernel so the reading
cannot return unnoticed. -/
theorem logbCandidate_is_junk_off_the_frozen_regime :
    Real.logb 2 0 = 0 ∧ Real.logb 2 1 = 0 := by
  constructor <;> simp

/-- **Statement pole: no fixed index witnesses unboundedness.**

`truthTable_unbounded` is an existential over the source size, and it has to
be: for every fixed `n` there is a bound the value at `n` fails.  Without this
the existential could have been discharged by a single index, which is not what
"tends to infinity" means at `06-eth.tex:351`.  General in the clock and the
source size. -/
theorem unboundedness_has_no_uniform_witness (V : ℕ → ℕ) (n : ℕ) :
    ∃ B, ¬ (B ≤ tCommon V n) := ⟨tCommon V n + 1, by omega⟩

end EthInapproximability.ParameterizedNP.TruthTableExponent
