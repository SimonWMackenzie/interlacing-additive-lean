import EthInapproximability.ParameterizedNP.DirectOutputEqualityClose

/-!
# Parameterized NP route: the one-level completion (`sec:one-level-completion`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-COMPLETION-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1p` tranche for `10-direct-bridge.tex:492--563` and **repaired in the
`cc-t1p-r1` round**: the output interfacebox and the budget-collection
subsection that closes the direct bridge.

Three things live in that range and nothing else does.

1. **The collected interface** (lines 492--498, `interfacebox` "Ordinary robust
   output"): `R⁺` is now an ordinary robust seed at depth `b_out`, and the next
   recursive level receives **only** four things — its truth table, exact `NO`
   complexity, known `YES` protocol budget, and the three-rung estimate
   `eq:direct-output`.  "No label, source item, donor, reservoir, or
   intermediate gadget coordinate survives this interface."
2. **The budget collection** (lines 500--541): `C = D + a + log₂q₂ + log₂s + 1`,
   the scale-alignment interlace sets `C_W = C + log₂q`, the direct bridge adds
   `log₂Q`, and therefore `comp R⁺ = D + H + 1` in the `NO` case and
   `comp R⁺ ≤ Y + H` in the `YES` case, with
   `H = a + log₂q₂ + log₂s + log₂q + log₂Q`.
3. **The increment table** (lines 543--563): the same three rows in both promise
   columns, differing only in the single extra `NO` bit carried by the
   Stages 1--4 row, with totals `H` and `H + 1`.

The two **readings** the subsection consumes are named where the frozen text
places them: line 521, "This is an equality: the lower bound is
`eq:direct-output`, and the matching protocol …", and line 536, "Finally,
`eq:direct-output` is exactly the requested ordinary robustness at depth
`b_out`".  Both are consumed from the `cc-t1n` close, never re-derived.

## What round `cc-t1p-r2` changed

The `r1` statement gate returned two per-declaration `REVISE` verdicts and
`CLEAR` on the other fifty-one declarations.  Those fifty-one are carried over
unchanged; the two repairs are:

1. **`seedInterface_realizable_no` now inhabits `SeedInterface.noReading`.**
   Round `r1` proved only two of its three conjuncts, so nothing in the module
   witnessed the predicate that `03-preliminaries.tex:444` makes the entry
   hypothesis of every later level.  The missing `Λ₃` conjunct is supplied by
   `aliceBit_lambda`.  Because that inhabitant sits at `noComplexity = 1`,
   below the frozen entry floor `D ≥ 3`, and because
   `noReading_refuted_at_bool_carrier` proves the two-element carrier can never
   do better, round `r2` additionally lands the paper's own legal-budget
   inhabitant: `fullCubeSeed_realizes_noReading`, at `noComplexity = 8` on the
   frozen full-cube matrix.  Part 1b is the machinery that makes it reachable;
   GAP-EXPOSED 7 records exactly how much of `lem:full-cube-seed` that is.
2. **`pinnedOutput_carriers` now carries the frozen `q ≥ 2` legality guard**,
   and the companion `pinnedOutput_carriers_invariant` states the frozen
   successor-carrier invariant of `02-mechanical-contract.tex:767--775` with the
   paper's own premises.  Round `r1` admitted `w_q = 0`, i.e. the frozen-illegal
   `q = 1`.

Nothing else in the module changed, and **no route completion is claimed**.

## The promise split (repair round `cc-t1p-r1`)

The frozen subsection states the two budgets as **two promise cases of one
common construction**, at two disjoint places: the `NO` equality at lines
512--520 and the `YES` bound at lines 525--534.  The `readingwarning` at lines
565--571 asserts only that the *widths and the matrix construction* are
promise-independent; it does **not** assert that both budget readings hold of
one and the same source matrix.

Conjoining them is not merely inelegant — it is **inconsistent with the frozen
side conditions**.  `13-iteration-assembly.tex` `step:I-05` (lines 430--432)
fixes `Y_i ≤ D_i` and `3 ≤ D_i` at every level, including every one-level call
site.  Assuming both the `NO` input `comp W = C_W = C + log₂q` and the `YES`
input `comp N ≤ Y + K` at once forces, through the selector upper bound,

```
Dsrc + K + 1 + wq  ≤  Ysrc + K + wq,      i.e.      Dsrc + 1 ≤ Ysrc,
```

the exact negation of `Y_i ≤ D_i`.  So every deliverable stated over the
conjoined bundle is a theorem about the empty parameter set.  This module
therefore carries **two headline theorems**, `oneLevelCompletion_no` and
`oneLevelCompletion_yes`, and no declaration anywhere in it asserts both a
`= Dsrc + H + 1` and a `≤ Ysrc + H` reading of the same matrix.  The inversion
itself is recorded as a theorem (`promiseConjunction_forces_gap_inversion`,
`promiseConjunction_refuted_at_step_I05`) so that the shape cannot be
reintroduced silently.

After the split the separation is syntactic and therefore permanent:
`oneLevelCompletion_no` does not mention `Ysrc` at all and
`oneLevelCompletion_yes` does not mention `Dsrc` at all, so neither can
constrain the pair `(Dsrc, Ysrc)` and neither can contradict `Ysrc ≤ Dsrc`.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`,
and (unless stated otherwise) to `sections/10-direct-bridge.tex`.

* **lines 492--498**, the `interfacebox` "Ordinary robust output" — the four
  interface slots of `SeedInterface` and its two promise-case readings, and the
  carrier-freeness of the complexity slot.
* **line 507**, `C = D + a + log₂q₂ + log₂s + 1` — `stage4Exact`.
* **lines 509--510**, "The scale-alignment interlace inside the adapted Stage~4
  sets `C_W = C + log₂q`, and the direct bridge adds `log₂Q`" — `alignedExact`
  and the outer step.
* **lines 512--519**, the `NO` display `comp R⁺ = C + log₂q + log₂Q = D + H + 1`
  with the underbraced definition of `H` at lines 516--518 — `levelOverhead`,
  `noBudget_collect`, and the headline `oneLevelCompletion_no`.
* **line 521**, "This is an equality: the lower bound is `eq:direct-output`, and
  the matching protocol applies `lem:interlace-selector-protocol` at each
  power-of-two interlace and then runs an optimal protocol for the seed" — the
  **equality reading**, consumed from `cc-t1n`.
* **lines 525--534**, the `YES` chain `Y + a + log₂q₂ + log₂s`, then the two
  power-of-two selectors, then `comp R⁺ ≤ Y + H` — `yesBudget_collect` and the
  headline `oneLevelCompletion_yes`.
* **line 536**, "Finally, `eq:direct-output` is exactly the requested ordinary
  robustness at depth `b_out`" — the **ordinary-robustness reading**, consumed
  from `cc-t1n`.
* **lines 537--541**, the scope sentence: "This subsection proves only the
  budget and robustness composition for an already admissible record."  That
  sentence is the exact scope of this module; see GAP-EXPOSED 1.
* **lines 543--563**, the increment table — `levelIncrementTable`.
* **lines 565--571**, the promise-independence `readingwarning` — the reason the
  *widths* are shared between the two headline theorems while the *readings*
  are not.
* `sections/03-preliminaries.tex`:
  * `def:robust-seed` (label line 243, statement lines 244--250): "A matrix `R`
    is robust at depth `b` if `comp(R) ≥ 1` **and**
    `Λ₃(R,1,2^{-b},y) ≥ comp(R)`", and it is a *certified robust seed at scale
    `D`* when the right-hand side is `D` — the three conjuncts of
    `SeedInterface.noReading`;
  * lines 438--444, the input tuple `(R,D,Y,b₀)` with **`D ≥ 3`** — the separate
    entry-guard lemma `oneLevelSeed_entryGuard`;
  * lines 450--455, the output tuple `(R⁺, D+H+1, Y+H, b_out)` — the four fields
    of `SeedInterface`, in that order;
  * `lem:interlace-selector-protocol` (label line 149, sentence lines 156--157)
    — the exact selector cost at both power-of-two widths, consumed twice
    through `cc-t1h`/`cc-t1n` and never re-proved;
  * `def:lambda` (label line 224) and `conv:finite-slots` — zero-based finite
    slots; every carrier below is `Fin k`-indexed exactly as in `EntryAssembly`
    and `DirectOutputEqualityClose`;
  * `def:reduced-protocol` (label line 35), `lem:fixed-output-leaves` (label
    line 46, statement lines 47--50) and `cor:fixed-output-rank` (label line 68,
    statement lines 69--76), together with the one-bit warning of lines 86--90
    — Part 1b, added in round `r2`.  These three are what supply the bit the
    inherited total-rank bound cannot; the recorded deviation is that the
    `2^{d-1}` one-colour count is obtained without formalizing
    `def:reduced-protocol` (see the head of Part 1b).
* `sections/02-mechanical-contract.tex`, lines 767--775, the realized-input
  carrier invariant: "The full-cube seed has both carrier sizes at least two.
  Moreover the exact successor equations give `m_next = (q m_N)^Q ≥ 2`,
  `n_next = Q n_N^q ≥ 2` because `q, Q ≥ 2` and `m_N, n_N ≥ 1`.  Hence
  realization preserves the invariant."  This is the anchor of
  `pinnedOutput_carriers_invariant` and of the `hq : 1 ≤ w_q` guard now carried
  by `pinnedOutput_carriers` — round `r2`'s second repair.
* `sections/12-iteration-specification.tex`, `sec:full-cube-seed`:
  lines 16--21 (the minimality rule fixing `a_seed` and
  `q_seed = 2^{a_seed} - 2 ≥ 64(b+1)`), `eq:full-cube-seed` (label line 31,
  display lines 23--30) and `lem:full-cube-seed` (label line 32, statement lines
  33--41) with its proof at lines 45--81.  **These two labels belong to ledger
  row `SEED-001`, not to this row**; Part 1b lands a recorded *part* of them and
  `SEED-001`'s own Lean column carries the scope.  What this module needs from
  them is only the legal-budget inhabitant of `SeedInterface.noReading`
  demanded by round `r1`'s statement gate.
* `sections/07-one-level-construction.tex`:
  * line 632, `K = a + log₂q₂ + log₂s` — `stage4Overhead`;
  * line 43, the overhead field `H = a + log₂q₂ + log₂s + log₂q + log₂Q`, the
    same expression the underbrace of line 518 introduces;
  * lines 80--81, `|Rows(R⁺)| = (q m_N)^Q` and `|Cols(R⁺)| = Q n_N^q` — used
    **only** to certify that the pinned composite of Part 3 is the paper's
    `R⁺`; see GAP-EXPOSED 3.
* `sections/08-dense-stage4.tex`, lines 145--152, `N = ᵀA` and the same
  `C = D + a + log₂q₂ + log₂s + 1` — the matrix the `q`-interlace is applied to.
* `sections/09-first-wrapper.tex`, lines 1786--1806: `comp U ≤ C + r` with
  `r = log₂q` (line 331 spells `r` as `log₂q`), `W = ᵀU`, `C_W = C + r`, and
  "The same outer selector adds exactly `r` bits to the `YES` protocol" — the
  inner interlace of Part 3.
* `sections/11-one-level-assembly.tex`, line 793, `comp N ≤ Y + a + log₂q₂ +
  log₂s` — the `YES` input binder `hYesN`.  Section 11 itself is **not**
  claimed here (GAP-EXPOSED 1).
* `sections/13-iteration-assembly.tex`, `step:I-05` (label line 430, side
  conditions line 431): `Y_i ≤ D_i` and `3 ≤ D_i` at every level and every
  one-level call site — the explicit binder `hYD` of the gap lemma, the target
  of the inconsistency refutation, and (with line 435, `D_0 = Y_0 = a_seed + 1
  ≥ 4`) the legal seed values used by the non-vacuity witnesses.

## Reader counterpart

The reader artifact of the same frozen release,
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/reader-facing`,
was opened first-hand and each candidate item read to check what it states.

**Claimed:** `sections/05-iteration.tex`, `eq:paper-budget-update` (label line
116, display lines 112--117),

> `Y_{i+1} = Y_i + H_i`,  `D_{i+1} = D_i + H_i + 1`,

introduced at line 111 as what "the parameterized construction and the bridge
give".  With the reader's own `K_i = a_i + log q_{2,i} + log s_i` and
`H_i = K_i + r_{q,i} + r_{Q,i}` (lines 105--110), that display states exactly
the two collected budgets of lines 514--519 and 534 and the totals row of the
table.

The reader states them as **two separate equations**, one per promise column,
which is the reader's own corroboration of the split this round performs.  They
are assigned accordingly, one equation to one declaration and no equation to
two declarations:

* the **first** equation (line 113), `Y_{i+1} = Y_i + H_i`, to
  `oneLevelCompletion_yes`;
* the **second** equation (line 115), `D_{i+1} = D_i + H_i + 1`, to
  `oneLevelCompletion_no`.

This follows the split already used in this route for `eq:bridge-output`, whose
first and second equations are held by `BRIDGE-OUTPUT-003` and
`BRIDGE-OUTPUT-002` respectively.  No previously banked ledger row cited
`05-iteration.tex` at all, and neither equation was assigned to any other
declaration before this round.

**Deliberately not claimed**, to avoid a double assignment:

* `sections/05-iteration.tex`, `lem:paper-full-cube-seed` (label line 27,
  statement lines 28--44), the reader counterpart of `lem:full-cube-seed`,
  belongs to ledger row `SEED-001` (reader anchor "reader Section 5").  Part 1b
  lands part of that lemma and the landing is recorded in `SEED-001`'s Lean
  column; **no reader item moves to this row**.
* `sections/05-iteration.tex` lines 280--283 ("Both seed carriers have size at
  least two.  At every successor, `q, Q ≥ 2` and `m⁺ = (q m_N)^Q`,
  `n⁺ = Q n_N^q`, so this lower-carrier invariant is preserved") is the reader's
  locus for `pinnedOutput_carriers_invariant`.  It was opened first-hand and
  states the same fact, but it is **proof prose inside the proof of the size
  envelope**, not a labelled statement, so it is named as navigation and is not
  claimed as a reader item.
* `sections/02-preliminaries.tex`, `def:paper-robust` (label line 94, statement
  lines 95--99) is the reader's robust-seed definition.  It is **not** the
  counterpart of `SeedInterface.noReading`: it additionally fixes `b ≥ 1` and
  `D ≥ 2`, where the autoformalization `def:robust-seed`
  (`03-preliminaries.tex:243--250`) — which `noReading` transcribes — imposes
  neither.  Recorded here because the depth-zero inhabitant
  `fullCubeSeed_realizes_noReading` is an instance of the autoformalization
  definition and **not** of the reader one.

* `sections/04-bridge.tex`, `cor:one-level-amplifier` (label line 155) and its
  `eq:one-level-amplifier-conclusion` (label line 174) belong to ledger row
  `ONELEVEL-001`, whose autoformalization side is `thm:one-level`
  (Section 11) — the *hypothesis-by-hypothesis* assembly that frozen lines
  538--539 explicitly hand to `sec:one-level-assembly`.
* `eq:one-level-exact-carriers` (reader label line 180) belongs to `SIZE-001`.
* `thm:paper-finite-iteration` (reader `05-iteration.tex` label line 120) is the
  closed-form summation theorem of lines 119--133 and belongs to `ITER-001`; it
  is a *different* statement from the display at lines 112--117, which precedes
  it and is not part of it.  Read first-hand this round to confirm the
  separation before claiming the display.
* `05-iteration.tex` lines 96--100 (the two-interlace display `U_i = Int_{q_i}
  (N_i)`, `W_i = ᵀU_i`, `R_{i+1} = ᵀInt_{Q_i}(W_i)`) is a construction display
  and lines 91--93 are prose; both are named as the reader's navigation locus
  for the pinning of Part 3 and are **not** claimed as statements.

**Crosswalk note, recorded rather than absorbed.**  The section-level crosswalk
maps autoformalization Section 10 to reader Section 4 plus Appendix B, and the
claimed item sits in reader Section 5.  That is a fact about the reader, not a
liberty taken here: reader Appendix B carries no budget item at all, and the
only Section-4 statement of the collected budgets is
`eq:one-level-amplifier-conclusion`, which `ONELEVEL-001` holds.  The reader
therefore states this subsection's content in exactly two places, one held and
one free, and the free one is claimed.  `ONELEVEL-001` keeps
`cor:one-level-amplifier`, `ITER-001` keeps `thm:paper-finite-iteration`, and
`SIZE-001` keeps `eq:one-level-exact-carriers`; none of the three is touched.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge" (the row that
already carries `INHERIT-001`, `BRIDGE-COPYREST-001`, `BRIDGE-OUTPUT-002`,
`BRIDGE-DISCHARGE-001`, `BRIDGE-ASSEMBLY-001`, `BRIDGE-DICHOTOMY-001` and
`BRIDGE-EQCLOSE-001`).

## Dependencies, imports, external adapters

* Imports: `DirectOutputEqualityClose.lean` only, hence transitively
  `BridgeOutputEquality`, `EntryAssembly`, `DefectDischarge`, `CopyRestriction`,
  `DirectOutputLower`, `DirectOutput`, `EntryGates`, `ThreeCopyRowStep`,
  `TwoCopyLadder`, `DefectInduction`, `InheritedContracts`, `PilotStage3` and
  `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom is not in this
  module's closure, and there is no contact with `EXPANDER-001` (which by
  design has no Lean declaration and remains an explicit named hypothesis
  wherever it is needed).
* Consumed, never edited, widened or re-proved — **both `cc-t1n` endpoints**,
  by their grep-verified names:
  * `DirectOutputEqualityClose.directOutputEqualityClose`
    (`BRIDGE-EQCLOSE-001`), the equality reading of line 521 from the `t = 0`
    rung;
  * `DirectOutputEqualityClose.directOutputClose` (`BRIDGE-EQCLOSE-001`), the
    paired endpoint that delivers the equality **and** the assembled
    three-rung `Λ` bound, i.e. the ordinary-robustness reading of line 536;
  * `DirectOutputEqualityClose.selectorUpper_transpose_two_pow`, the
    `lem:interlace-selector-protocol` upper bound at an **arbitrary**
    power-of-two width, used here at the **inner** width `q = 2^{w_q}`;
  * `DirectOutput.canonicalSelectorProtocol` and `.canonicalSelectorBits`
    (`BRIDGE-OUTPUT-001`), the outer `Q`-selector;
  * `DirectOutputLower.entryLevel_pow_eq` (`BRIDGE-OUTPUT-002`), the banked
    identity `2^{a_t} = Q / 2^t`, consumed at `t = 0` to certify that the
    `log₂Q` written in the collected budget is the exact selector cost of a
    genuine power-of-two width (mechanical rule M8);
  * `DirectOutputLower.entryLevelA`, `.xOut`,
    `.directOutputLower_conclusion_nontrivial`;
  * `EntryGates.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`, `.four_le_rQ`,
    `.directEntryGates_fires`;
  * `DirectOutput.clog_two_pow`, `.directOutput_fires_second_witness`;
  * `BridgeOutputEquality.rowsCard`, `.colsCard`.
* External theorem adapters: **none new**.  Two vendored names appear, both
  already inside the route's closure: `EthBridge.Rnext`
  (`vendor/npc-cc/EthBridge/Entry.lean:181`), used twice for the two frozen
  interlace-and-transpose steps, and `NPCC.achievableCosts_reindex`
  (`vendor/npc-cc/NPCC/Complexity.lean:93`), the cost-preserving reindexing
  bijection, used only for the carrier-freeness lemma.  The realizability
  battery of Part 5 additionally uses the vendored *definitions*
  `Workspace.Types.Protocol.Protocol` and `Workspace.Types.CommComplexity.D`
  and the Mathlib lemma `Nat.sInf_mem`; it introduces no adapter and
  axiomatizes nothing.
* Proof status: **new (elementary)** throughout.  Every budget deliverable is
  linear `ℕ` arithmetic (`omega`) over banked, already kernel-checked route
  facades; the carrier readout is `Fintype.card` bookkeeping; the realizability
  battery is explicit protocol trees and a case analysis on a cost-zero tree.
  No banked declaration is edited or re-proved.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings (k = 2) and the ranking

The genuinely open choice is **how the interfacebox's four slots are encoded**.

**Candidate A (landed) — four slots of public data, two separate readings.**
`SeedInterface` carries exactly the four things lines 494--496 list — truth
table, `NO` complexity, `YES` budget, requested depth — as *data*, and the two
promise-case statements are the separate predicates `noReading` (the full
`def:robust-seed` reading: the equality of line 521, the robustness of line 536
at the **same** integer, and the `comp ≥ 1` guard of `03-preliminaries.tex:244`)
and `yesReading`.  No complexity or robustness conclusion sits in constructor
data: the record's `noComplexity` and `yesBudget` fields are the public
integers `D + H + 1` and `Y + H`, computed from the public tuple before either
promise case is analysed (mechanical rules M1 and M2).

**Candidate B (refuted) — one flat predicate asserting all four slots at
once.**  Bundle `comp R⁺ = c_NO`, `comp R⁺ ≤ y_YES` and the `Λ` bound into a
single `Prop`.  This is the classic M2 violation — the constructor would carry
both promise certificates — and in Lean it is not merely inelegant but
**inhabited only at inverted parameters**: the two complexity fields force
`c_NO ≤ y_YES`, i.e. `D + H + 1 ≤ Y + H`, i.e. `D + 1 ≤ Y`, which contradicts
the frozen side condition `Y ≤ D` of `13-iteration-assembly.tex:431` at every
legal level.  Proved as `flatInterface_forces_gap_inversion` together with
`flatInterface_refuted_at_legal_budgets`.

Candidate B is exactly the shape the first round of this tranche accidentally
took at the *theorem* level rather than the *record* level; the same two
refutations now also fire against that form, as
`promiseConjunction_forces_gap_inversion` and
`promiseConjunction_refuted_at_step_I05`.

Aux battery: A = 12/12, B = 10/12 (B fails aux 4, the one-bit gap, and aux 5,
the field-by-field readout, since a flat bundle has no `NO`/`YES` split to read
off).  Faithfulness: A is the box's own list; B merges two propositions the
paper keeps apart.  Length: A is shorter at every use site, because the two
readings are exactly the two things the callers of `cc-t1n` already hold.

**A is landed.**  B survives only as its own refutation.

**Round `r2` adds a second, independent `k = 2` choice** — how to encode the
frozen seed matrix `eq:full-cube-seed`.  Candidate A keeps the frozen carriers
`{0,1}^{q} × [q]`; candidate B re-carriers the columns as bit-strings with
`q = 2^{a}`.  B is rejected on faithfulness (it contradicts the frozen
`q_seed = 2^{a_seed} - 2` and reads the bracket column threshold at a
cardinality the paper does not have), and the ranking together with the eight
aux lemmas that close on A is recorded at the head of Part 1b.

## Aux-lemma battery (24, all general, all proved)

None is about a pinned instance; each quantifies over arbitrary widths,
budgets, matrices, carriers or protocols.

1. `levelOverhead_eq` — the overhead unfolds to the literal five-term sum of
   line 517 and of `07-one-level-construction.tex:43`.  Identity property,
   general in all five widths.
2. `noBudget_collect` — **the arithmetic engine of lines 512--519**:
   `C_W + w_Q = D + H + 1` from `C_W = C + w_q` and
   `C = D + K + 1`.  General in all six numbers.
3. `yesBudget_collect` — **the arithmetic engine of lines 525--534**: the
   three-step `YES` chain `n ≤ Y + K`, `m ≤ n + w_q`, `r ≤ m + w_Q` gives
   `r ≤ Y + H`.  Monotone-chaining property, general in all seven numbers.
4. `oneBitGap` — under the frozen `Y ≤ D` the collected `YES` total is
   **strictly** below the collected `NO` total, by exactly the single bit the
   table's Stages 1--4 row carries.  Ordering property, general.
5. `noReading_iff`, `yesReading_iff` — the interface read **field by field as
   the box and `def:robust-seed` state it**.  Identity property, general in the
   carriers.
6. `comp_reindex` and `interfaceComplexity_carrier_free` — the exact-complexity
   slot is invariant under **any** relabelling of both carriers, which is the
   Lean content of line 496's "no … coordinate survives this interface".
   Round-trip property through the vendored `achievableCosts_reindex`, general
   in two arbitrary equivalences.
7. `topLevelWidth_pow_eq` and `outerSelectorCost_exact` — **the banked
   `entryLevel_pow_eq` consumed**: at `t = 0` it reads `2^{a_0} = Q`, so the
   canonical width is a genuine power of two and `⌈log₂Q⌉ = r_Q` exactly.  This
   is the M8 licence for writing `log₂Q` rather than `⌈log₂Q⌉` in the collected
   budget.  General in `b_out` and `δ_U`.
8. `alignedSelectorCost_exact` — the same M8 licence at the **inner** width,
   `⌈log₂ 2^{w_q}⌉ = w_q`, general in `w_q`.  Both interlace widths are carried
   separately and neither is conflated with the other.
9. `computes_const_of_cost_zero` — a protocol of cost `0` is a leaf, so any
   function it computes is constant.  General in both carriers and in the
   protocol.
10. `one_le_D_of_not_const` — the converse readout: a nonconstant function whose
    cost set is nonempty has `comp ≥ 1`.  General in both carriers; this is the
    lemma that makes the `def:robust-seed` guard `comp(R) ≥ 1` a checkable
    property rather than a decoration.
11. `D_bool_le_two` — **every** Boolean function of two Boolean inputs is
    computed in two bits, so `comp ≤ 2` on a two-element row carrier.  General
    in the function; it is what makes the cardinality refutation of Part 5
    quantify over all tables rather than one.
12. `D_aliceBit` — `comp` of the projection `(x, y) ↦ x` on `Bool × Bool` is
    **exactly** `1`.  A round-trip of aux 9--11 (upper bound by a protocol,
    lower bound by nonconstancy), and the only exact `comp` value this module
    needs.

Round `r2` adds twelve more, all for the new Part-1b types:

13. `indR_apply` — the one-colour indicator is the entrywise
    `if f i j = β then 1 else 0` and nothing else.  Readout, general.
14. `rank_add_le_generic` — real-rank subadditivity at arbitrary carriers, the
    inequality `03-preliminaries.tex:78--81` invokes.  General.
15. `indR_rank_le_one_of_const` — a monochromatic rectangle's indicator has rank
    at most one (`03-preliminaries.tex:79--80`).  General.
16. `eval_const_of_cost_zero` — the *value* form of aux 9, valid on empty
    carriers where the `∀ x y x' y'` form is vacuous.  General.
17. `one_le_cost_of_not_const` — its contrapositive.  General.
18. `fullCube_apply`, `fullCube_unit` — the frozen `F_b(γ,j) = γ(j)` and the
    identity submatrix cut out by the unit rows.  Readouts, general in `q`.
19. `fullCube_not_const` — nonconstancy at every `q ≥ 1`.  General.
20. `fullCube_rank_ge` — `q ≤ rank(1_{F=1})` for every `q`, by the unit-row
    identity submatrix.  General.
21. `fullCube_D_le` / `fullCube_D_ge` / `fullCube_D_eq` — the announce-tree
    upper bound, the `cor:fixed-output-rank` lower bound, and their round trip
    `comp F = a + 1` under the frozen sandwich `2^{a-1} < q ≤ 2^{a}`.  General
    in `q` and `a`.
22. `bracket_row_univ` — at requested depth zero the bracket keeps every row.
    General in both carriers and in the column density.
23. `fin1_fun_ext` — a one-slot column tuple is its single entry.  General.
24. `one_le_D_of_no_const_value` — the value-form readout of aux 10, general in
    both carriers.

## Faithfulness notes (mechanical rules M1--M10)

* **M1, M2 — no promise certificate in constructor data.**  `SeedInterface` has
  four fields and all four are public: the truth table (computed from the
  public tuple), the two public integers `D + H + 1` and `Y + H`, and the
  requested depth.  Neither promise case appears; the readings are separate
  `Prop`s, and no field restates a derived telescope.  At the *theorem* level
  the same rule is enforced by the promise split: no declaration takes both
  promise inputs.
* **M3 — constructed versus derived.**  `alignedMatrix` and `levelOutput` are
  the constructed objects; their complexity, budget and carrier cardinalities
  are recomputed from them (`pinnedOutput_carriers`) rather than stored.
* **M7 — carrier equations accompany entry equations.**  The pinned composite's
  row and column carriers are counted, and the nonemptiness binder
  `1 ≤ |X|` is carried explicitly wherever the banked lower half needs it.  A
  numerical width and its logarithm are never interchanged: `q` and `Q` occur
  only as `2 ^ w_q` and `Qwidth b_out δ_U = 2 ^ r_Q`, and the exponents `w_q`,
  `r_Q` are separate objects from them.
* **M8 — protocol cost is exact at every selector.**  Both selector costs are
  discharged as exact `Nat.clog 2` values of proved powers of two (aux 7 and
  aux 8) before `log₂` notation is used, and neither is smoothed into an
  inequality.  No conclusion bit is added by convention: the single extra `NO`
  bit is the one already present in `C` at line 507, and no `YES` conclusion is
  weakened by a bit to make a pair look consistent.
* **Both interlace widths.**  The inner scale-alignment width `q = 2^{w_q}` of
  `09-first-wrapper.tex` and the outer bridge width `Q = 2^{r_Q}` of
  `EntryGates.Qwidth` are distinct binders throughout, and the collected `H`
  contains both exponents once each.
* **Literal ceilings.**  None is introduced or smoothed; `x_out` and the row
  floors are consumed unchanged from the banked apparatus.
* **Binder order** follows the frozen subsection: the source matrix, then the
  public budget of the promise case at hand (`D` for the `NO` theorems, `Y` for
  the `YES` theorems), then the widths `a, w₂, w_s, w_q`, then the depth
  `b_out` and `δ_U`, then the carrier nonemptiness, then that case's input, then
  the rung premise.

## Statement poles

* **Trivial-witness pole.**  There is **no existential deliverable** among the
  budget statements: every one is an equation or inequality between named
  readouts, or a named-def claim about the pinned composite `levelOutput`.  The
  one place a trivial witness could hide is the record `SeedInterface`, which is
  trivially inhabitable — so the deliverable is never "such a record exists" but
  always "*this* record's readings hold".  The two existentials of Part 5
  (`seedInterface_realizable_no`, `seedInterface_realizable_yes`) each pin every
  field by an explicit equation, so the zero record `⟨fun _ _ => false, 0, 0,
  0⟩` — the witness a vacuous `∃` would accept — fails them on the very first
  conjunct, and would in addition fail `yesBudget < noComplexity`, which
  `0 < 0` refutes.
* **Cardinality pole.**  A `SeedInterface` inhabitant is worthless if its
  pinned complexity slot is out of the carrier's reach: the reading it is meant
  to illustrate is then refutable rather than merely unproved.  Part 5 pins its
  two inhabitants at complexity values that the carrier **does** realize — the
  exact-complexity conjunct of `noReading` is *proved*, not assumed — and
  records the general reason a bigger value could not be pinned there as
  `noReading_refuted_at_bool_carrier`.
* **Vacuous-hypothesis pole.**  The `NO` input `hCW` is not free: it is
  `BRIDGE-OUTPUT-003`'s line-40 binder at the aligned value `C_W = C + w_q`, and
  that binder's non-triviality is the consumed
  `BridgeOutputEquality.exactComplexity_refuted_at_unit_row`.  The rung premise
  is not free: `DirectOutputEqualityClose.topRung_fires_via_bankedRung` and
  `EntryAssembly.entryDescent_fires_via_bankedRungs` discharge it from the
  route's own banked rungs.  The `YES` input `hYesN` is not free: it is
  `11-one-level-assembly.tex:793` verbatim, and it is satisfiable at
  `Y = D`, the frozen seed value of `13-iteration-assembly.tex:435`.  Crucially,
  **no theorem takes both**, and the reason is recorded in the kernel by
  `promiseConjunction_refuted_at_step_I05`.
* **Vacuous-conclusion pole.**  `oneLevelCompletion_conclusion_nontrivial`
  records that the delivered `NO` value is at least `r_Q + 1 ≥ 5` for every
  legal parameter tuple and at least `D + 1`, so the collected budget is never
  the free `0`; `oneBitGap` records that the two collected budgets are never
  equal.
* **Round `r2` — the `noReading` pole.**  Round `r1` proved statements *about*
  `SeedInterface.noReading` while inhabiting it nowhere, which is exactly the
  shape a green build cannot see.  Two inhabitants now close it from both
  sides: `seedInterface_realizable_no` at the floor budget `1`, and
  `fullCubeSeed_realizes_noReading` at the **legal** budget
  `8 = a_seed + 1 ≥ 3` on the paper's own seed matrix.  For the latter the
  trivial witness fails on three separate conjuncts at once
  (`table = fullCube 126`, `3 ≤ 0`, and `D (fun _ _ => false) = 0 ≠ 8`), and no
  record over that carrier with any other `noComplexity` can satisfy `noReading`
  at all, because `fullCubeSeed_D` computes the left-hand side of its first
  conjunct.
* **Round `r2` — the dropped-guard pole.**  `pinnedOutput_carriers` now carries
  `hq : 1 ≤ w_q`, and `pinnedOutput_carriers_invariant` turns the frozen
  `02-mechanical-contract.tex:771--775` premises into the frozen `≥ 2`
  conclusions.  The guard is a *lower* bound on the width; `w_q = 0`, i.e. the
  frozen-illegal `q = 1`, is no longer an admitted instantiation.  `Q ≥ 2` is
  **derived** from `EntryGates.four_le_rQ`, never assumed, so no premise is
  imported that the route has not proved.

## GAP-EXPOSED (nothing is weakened to close these)

1. **Only lines 492--563 are claimed.**  Frozen lines 537--541 say this
   subsection "proves only the budget and robustness composition for an already
   admissible record"; the hypothesis-by-hypothesis assembly is
   `sec:one-level-assembly` and the effective production of such a record is
   `thm:eff-ledger`/`thm:effective-materialization`.  Accordingly `ONELEVEL-001`
   (`thm:one-level`, Section 11) is **not** claimed: its promise-independence
   clause C1, its `Admissible` predicate, and its carrier clause C4 are
   untouched, and `Y`, `D`, `a`, `w₂`, `w_s`, `w_q` stay universally quantified
   naturals rather than outputs of the schedule compiler.  In particular the
   two headline theorems are **not** joined into a single one-level contract
   here; joining them is `sec:one-level-assembly`'s work and requires the
   promise hypothesis that this subsection does not have.
2. **No inhabitant of the input is exhibited.**  `eq:direct-input` and the
   Stage-4 exact identity have no Lean inhabitant and can have none until
   Stages 1--4 land, so every statement here is conditional: the witnesses
   discharge the *numeric* binders by computation and leave `X`, `Y`, `N`, the
   `NO` input, the `YES` input and the rung premise universally quantified.
   **No route completion is claimed.**  The Part-5 inhabitants inhabit the
   *record type*, never the input bundle.
3. **`pinnedOutput_carriers` is a pinning check, not the carrier obligation.**
   It certifies that the composite this module pins has exactly the carriers
   `07-one-level-construction.tex:80--81` attributes to `R⁺`, so that the
   budget statements are about the paper's matrix.  Clause C4 of
   `thm:one-level` and reader `eq:one-level-exact-carriers` remain with
   `ONELEVEL-001` and `SIZE-001`; the side-length recurrence
   `eq:one-level-side-recurrence` and the successor exponent `16(c+1)` are not
   touched here.
4. **Carrier-freeness is proved for the complexity slot only.**  Line 496's
   claim is rendered as the relabelling invariance of the exact-complexity
   field (aux 6) plus the fact that `SeedInterface` has exactly four fields.
   The corresponding invariance of the `Λ` slot is **not** proved: `bracketGE`
   is stated over `Fin p`-indexed equipartitions and transporting it along
   arbitrary carrier equivalences is a separate obligation, not opened here.
   Recorded as the follow-up item this round deliberately does not expand into.
5. **The legal-parameter tuples of the witnesses are checked against the
   structural gates only.**  `q₂ ≥ 16` (`09-first-wrapper.tex:840`, hence
   `w₂ ≥ 4`), `1 ≤ w_s` (`07-one-level-construction.tex:501`), `2^a = q₁ + 2`
   (`07-one-level-construction.tex:623`, hence `a ≥ 2`), `C ≥ 3`
   (`09-first-wrapper.tex:240`), `Y ≤ D` and `3 ≤ D`
   (`13-iteration-assembly.tex:431`), and `Q = 2^{r_Q}` from the banked entry
   witness.  The schedule-internal gates that additionally relate `q` to `q₂`
   through `μ_P` and `η_R` (`06-parameter-schedule.tex:1687`) are **not**
   traced in this tranche, so the witnesses are labelled *structurally legal*,
   not *schedule-certified*; certifying them is `PARAM-001`'s work.
6. **The Part-5 record inhabitants are field-shape realizability witnesses, not
   route instances.**  Their budgets (`1` and `2`) are the only ones a
   two-element carrier realizes, and `noReading_refuted_at_bool_carrier` proves
   that no route-legal `noComplexity ≥ 3` can be pinned there at all.  The
   route-legal-value non-degeneracy of the record is carried separately and
   unconditionally by `oneLevelSeed_fields_first_witness` (`31 < 32` at the
   banked first entry-gate parameters) and by
   `oneLevelCompletion_conclusion_nontrivial` (`≥ 5`).  Neither substitutes for
   the other: the first shows the *type* is inhabited at realizable values, the
   second that the *route's own* values are separated and above the floor.
7. **`lem:full-cube-seed` is landed only at requested depth `b = 0`, and the
   row-density leg of its proof is not formalized.**  Part 1b lands the frozen
   matrix `eq:full-cube-seed`, the exact complexity `comp F = a_seed + 1`
   (`12-iteration-specification.tex:33--36`) for every `q` in the frozen
   sandwich, and the three-rung bound `Λ₃(F, 1, 2^{-b}, 3/5) ≥ a_seed + 1`
   **at `b = 0` only**.  The frozen lemma fixes `b ≥ 1`, where the proof
   additionally needs lines 60--64: a retained row set of density `2^{-b}`
   spans a subspace of dimension at least `q_seed - b`, whence restricted rank
   at least `|J| - b`.  **That leg is not formalized here**; at `b = 0` the row
   condition forces the full row set (`bracket_row_univ`) and the `-b`
   correction vanishes, which is precisely why this instance is reachable and
   the parametric lemma is not.  `SEED-001` keeps the parametric lemma and its
   Lean column records this partial landing; no consumer may read the depth-zero
   instance as `lem:full-cube-seed`.  The reader's `def:paper-robust`
   (`02-preliminaries.tex:95--99`) additionally fixes `b ≥ 1`, so the depth-zero
   record is an instance of the autoformalization `def:robust-seed` and not of
   the reader definition.
8. **`def:reduced-protocol` is not formalized.**  `protocol_indR_rank_bound`
   delivers the `2^{d-1}` one-colour count of `lem:fixed-output-leaves`
   directly by induction on the protocol tree, without the reduction operation
   of `03-preliminaries.tex:34--43`.  The conclusion consumed by
   `cor:fixed-output-rank` is the frozen one; what is *not* landed is the
   frozen intermediate statement about reduced protocols, and any later
   obligation that needs reduction itself must open it separately.
-/

namespace EthInapproximability.ParameterizedNP.OneLevelCompletion

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.EntryAssembly
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.DirectOutputEqualityClose

/-! ## Part 0: the public budget names and the collected interface

Four transparent `ℕ`-valued definitions and one four-field record.  All five are
public data in the sense of mechanical rule M1: each is a function of the public
tuple alone, fixed before either promise case is analysed. -/

/-- **`K = a + log₂q₂ + log₂s`** — `07-one-level-construction.tex:632`, the
public selector overhead of the parameterized construction, and the quantity the
frozen `YES` line `10-direct-bridge.tex:527` and the frozen `NO` line 507 both
spell out term by term.

The three summands are *exponents*: `a` is the seed-copy exponent, `w₂ = log₂q₂`
and `w_s = log₂s` are the base-two logarithms of two widths the schedule has
already proved to be powers of two (mechanical rule M8). -/
def stage4Overhead (a w2 ws : ℕ) : ℕ := a + w2 + ws

/-- **`H = a + log₂q₂ + log₂s + log₂q + log₂Q`** — the underbraced definition at
`10-direct-bridge.tex:516--518`, identical to the overhead field of
`07-one-level-construction.tex:43` and to the reader's
`H_i = K_i + r_{q,i} + r_{Q,i}` (`05-iteration.tex:109`).

`w_q = log₂q` is the **inner** scale-alignment exponent of
`09-first-wrapper.tex` and `wQ = log₂Q` the **outer** bridge exponent; they are
separate binders and are never conflated. -/
def levelOverhead (a w2 ws wq wQ : ℕ) : ℕ := stage4Overhead a w2 ws + wq + wQ

/-- **`C = D + a + log₂q₂ + log₂s + 1`** — `10-direct-bridge.tex:507`, the same
identity as `08-dense-stage4.tex:149`.  The exact `NO` complexity of the
protected Stage-4 transpose `N = ᵀA`.

The trailing `+ 1` is the raw Stage-4 one-bit gap; it is the *only* asymmetry
between the two promise columns of the table at lines 543--563. -/
def stage4Exact (Dsrc a w2 ws : ℕ) : ℕ := Dsrc + stage4Overhead a w2 ws + 1

/-- **`C_W = C + log₂q`** — `10-direct-bridge.tex:509--510`, "The scale-alignment
interlace inside the adapted Stage~4 sets `C_W = C + log₂q`", which is
`09-first-wrapper.tex:1794`'s `C_W = C + r` with `r = log₂q` (line 331). -/
def alignedExact (Dsrc a w2 ws wq : ℕ) : ℕ := stage4Exact Dsrc a w2 ws + wq

/-- **The collected interface of `10-direct-bridge.tex:492--498`, field by field
as the box states it.**

> "The matrix `R⁺` is now an ordinary robust seed at depth `b_out`.  The next
> recursive level receives only its truth table, exact `NO` complexity, known
> `YES` protocol budget, and the three-rung estimate `eq:direct-output`.  No
> label, source item, donor, reservoir, or intermediate gadget coordinate
> survives this interface."

Exactly four fields, in the box's order — which is also the order of the output
tuple `(R⁺, D+H+1, Y+H, b_out)` at `03-preliminaries.tex:450--453`:

* `table` — "its truth table";
* `noComplexity` — "exact `NO` complexity", the public integer `D + H + 1`;
* `yesBudget` — "known `YES` protocol budget", the public integer `Y + H`;
* `depth` — "at depth `b_out`", the requested depth the three-rung estimate is
  taken at.

All four are **public data** (M1, M2): no promise certificate and no complexity
or robustness conclusion is a field.  The two promise-case statements are the
separate predicates `noReading` and `yesReading` below, so a value of this type
carries no proof obligation and proves nothing on its own — which is exactly
why the deliverables of Parts 2--3 are the *readings*, never an inhabitant. -/
structure SeedInterface (A B : Type*) [Fintype A] [Fintype B] where
  /-- The truth table crossing the interface — the first slot of line 494. -/
  table : A → B → Bool
  /-- The exact `NO` complexity — the second slot of line 494. -/
  noComplexity : ℕ
  /-- The known `YES` protocol budget — the third slot of line 495. -/
  yesBudget : ℕ
  /-- The requested depth `b_out` of line 493. -/
  depth : ℕ

/-- **The `NO` reading of the interface** — the two frozen readings the
subsection consumes at the **same** integer, together with the guard that makes
them `def:robust-seed`.

`10-direct-bridge.tex:521`, "This is an equality", gives
`comp R⁺ = noComplexity`; `10-direct-bridge.tex:536`, "`eq:direct-output` is
exactly the requested ordinary robustness at depth `b_out`", gives
`noComplexity ≤ Λ_{R⁺}(1, 2^{-b_out}, 3/5)`.  That both use one field rather
than two is the content of `11-one-level-assembly.tex:784`, "the equality and
the robustness lower bound use the same integer".

The third conjunct is the **first** clause of `def:robust-seed`
(`03-preliminaries.tex:244`): "A matrix `R` is robust at depth `b` if
`comp(R) ≥ 1` **and** `Λ₃(R,1,2^{-b},y) ≥ comp(R)`."  Without it a consumer
handed this predicate would not hold "robust at depth `b`" in the paper's
sense.  It is stated on the field rather than on `comp R⁺` deliberately: the
first conjunct identifies the two, and the field is the public integer the next
level actually receives.

The *entry* guard `3 ≤ D` of `03-preliminaries.tex:442` and
`13-iteration-assembly.tex:431` is **not** a conjunct here: it is a condition on
the tuple the next level is invoked with, not part of robustness, and it is
carried separately by `oneLevelSeed_entryGuard`. -/
def SeedInterface.noReading {A B : Type*} [Fintype A] [Fintype B]
    (S : SeedInterface A B) : Prop :=
  D S.table = S.noComplexity ∧
    S.noComplexity ≤ LambdaGE S.table 1 (xOut S.depth) ((3 : ℝ) / 5) ∧
    1 ≤ S.noComplexity

/-- **The `YES` reading of the interface** — `10-direct-bridge.tex:534`,
`comp R⁺ ≤ Y + H`.  A separate proposition about the same output, per
mechanical rule M2. -/
def SeedInterface.yesReading {A B : Type*} [Fintype A] [Fintype B]
    (S : SeedInterface A B) : Prop :=
  D S.table ≤ S.yesBudget

/-! ## Part 1: the aux-lemma battery

Twelve general properties: the two budget engines, the strict gap, the
field-by-field readout, the carrier-freeness of the complexity slot, the two
M8 selector-cost licences (the outer one consuming the banked
`entryLevel_pow_eq`), and the four realizability lemmas that make the
`def:robust-seed` guard and the cardinality pole checkable.  None is about the
pinned instance of Part 3. -/

/-- **Aux 1 (the overhead is the literal five-term sum).**

`10-direct-bridge.tex:517` writes `H` as `a + log₂q₂ + log₂s + log₂q + log₂Q`;
`07-one-level-construction.tex:43` writes the same expression for the overhead
field of the trace.  General in all five exponents. -/
lemma levelOverhead_eq (a w2 ws wq wQ : ℕ) :
    levelOverhead a w2 ws wq wQ = a + w2 + ws + wq + wQ := by
  unfold levelOverhead stage4Overhead
  omega

/-- **Aux 2 (the arithmetic engine of `10-direct-bridge.tex:512--519`).**

```
comp R⁺ = C + log₂q + log₂Q = D + (a + log₂q₂ + log₂s + log₂q + log₂Q) + 1
```
read purely as arithmetic: `C_W + w_Q = D + H + 1`, where `C_W = C + w_q` and
`C = D + K + 1`.  General in all six numbers, so it is a property of the
collection step and not of the bridge's particular values. -/
lemma noBudget_collect (Dsrc a w2 ws wq wQ : ℕ) :
    alignedExact Dsrc a w2 ws wq + wQ
      = Dsrc + levelOverhead a w2 ws wq wQ + 1 := by
  unfold alignedExact stage4Exact levelOverhead stage4Overhead
  omega

/-- **Aux 3 (the arithmetic engine of `10-direct-bridge.tex:525--534`).**

The `YES` chain has three links: the Stage-4 protocol costs at most `Y + K`
(line 527), scale alignment communicates its `q`-selector in `w_q` bits and the
direct bridge its `Q`-selector in `w_Q` bits (lines 529--531).  Composing them
gives `comp R⁺ ≤ Y + H` (line 534).

Stated at seven arbitrary numbers, so it is the shape of the composition and not
the values.  Monotone-chaining property. -/
lemma yesBudget_collect {Ysrc a w2 ws wq wQ n m r : ℕ}
    (hN : n ≤ Ysrc + stage4Overhead a w2 ws) (hq : m ≤ n + wq)
    (hQ : r ≤ m + wQ) : r ≤ Ysrc + levelOverhead a w2 ws wq wQ := by
  unfold levelOverhead
  omega

/-- **Aux 4 (the one-bit gap survives the collection).**

The table at `10-direct-bridge.tex:543--563` gives both promise columns the same
three overhead rows and differs only in the single extra bit of the Stages 1--4
row, so the totals are `H` and `H + 1`.  Under the frozen side condition
`Y ≤ D` of `13-iteration-assembly.tex:431`, the collected `YES` budget is
therefore **strictly** below the collected `NO` complexity.

This is the property Candidate B destroys; see
`flatInterface_refuted_at_legal_budgets`.  General in all seven numbers. -/
lemma oneBitGap {Dsrc Ysrc : ℕ} (a w2 ws wq wQ : ℕ) (hYD : Ysrc ≤ Dsrc) :
    Ysrc + levelOverhead a w2 ws wq wQ
      < Dsrc + levelOverhead a w2 ws wq wQ + 1 := by
  omega

/-- **Aux 5a (the `NO` reading read field by field).**  Identity property: the
predicate is literally the conjunction of the equality of line 521, the
robustness of line 536, and the `comp ≥ 1` clause of `def:robust-seed`
(`03-preliminaries.tex:244`), at the record's own fields and at no other data.

*Deviation from the parked round, recorded:* this statement gained its third
conjunct when `noReading` did.  It is the only judged-sound declaration of the
previous round whose statement the `F4` strengthening changed. -/
lemma noReading_iff {A B : Type*} [Fintype A] [Fintype B] (M : A → B → Bool)
    (c y b : ℕ) :
    (SeedInterface.mk M c y b).noReading
      ↔ (D M = c ∧ c ≤ LambdaGE M 1 (xOut b) ((3 : ℝ) / 5) ∧ 1 ≤ c) := Iff.rfl

/-- **Aux 5b (the `YES` reading read field by field).**  Identity property. -/
lemma yesReading_iff {A B : Type*} [Fintype A] [Fintype B] (M : A → B → Bool)
    (c y b : ℕ) : (SeedInterface.mk M c y b).yesReading ↔ D M ≤ y := Iff.rfl

/-- **Aux 6a (relabelling costs nothing).**

`D` is `sInf` of the achievable-cost set, and the vendored
`NPCC.achievableCosts_reindex` is a cost-preserving bijection on computing
protocols along equivalences of both parties' input spaces.  Hence the exact
complexity of a matrix is unchanged by any relabelling of its row and column
carriers.  General in two arbitrary equivalences. -/
lemma comp_reindex {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A']
    [Fintype B'] (f : A → B → Bool) (e₁ : A' ≃ A) (e₂ : B' ≃ B) :
    D (fun a b => f (e₁ a) (e₂ b)) = D f := by
  unfold Workspace.Types.CommComplexity.D
  rw [NPCC.achievableCosts_reindex]

/-- **Aux 6b (`10-direct-bridge.tex:496--497` for the complexity slot).**

"No label, source item, donor, reservoir, or intermediate gadget coordinate
survives this interface."  Rendered as: the exact-complexity slot of the
interface is invariant under **any** relabelling of both carriers, so it cannot
encode a coordinate identity; and the `YES` reading transports with it.

Only the complexity slot is covered — see GAP-EXPOSED 4 for the `Λ` slot. -/
theorem interfaceComplexity_carrier_free {A B A' B' : Type*} [Fintype A]
    [Fintype B] [Fintype A'] [Fintype B'] (S : SeedInterface A B) (e₁ : A' ≃ A)
    (e₂ : B' ≃ B) :
    D (fun a b => S.table (e₁ a) (e₂ b)) = D S.table ∧
      ((SeedInterface.mk (fun a b => S.table (e₁ a) (e₂ b)) S.noComplexity
          S.yesBudget S.depth).yesReading ↔ S.yesReading) := by
  refine ⟨comp_reindex S.table e₁ e₂, ?_⟩
  unfold SeedInterface.yesReading
  rw [comp_reindex S.table e₁ e₂]

/-- **Aux 7a (the banked `entryLevel_pow_eq` at the top level).**

`DirectOutputLower.entryLevel_pow_eq` is the frozen identity `2^{a_t} = Q/2^t`
of `10-direct-bridge.tex:471`.  At `t = 0` — the level the collection is stated
at — it reads `2^{a_0} = Q`.  Consumed, never re-proved.  General in `b_out`
and `δ_U`. -/
lemma topLevelWidth_pow_eq (bout : ℕ) (δU : ℝ) :
    (2 : ℝ) ^ entryLevelA bout δU 0 = ((Qwidth bout δU : ℕ) : ℝ) := by
  have h := entryLevel_pow_eq bout δU (t := 0) (by norm_num)
  simpa using h

/-- **Aux 7b (the M8 licence for the outer `log₂Q`).**

Mechanical rule M8: "A selector of width `w` costs `⌈log₂w⌉`.  It is replaced by
`log₂w` only after `w` has been proved to be a power of two."  The collected
budget of lines 514--518 writes `log₂Q`; this lemma supplies the licence, from
the banked `entryLevel_pow_eq` at `t = 0` together with `Q = 2^{r_Q}`, and
returns the exact ceiling `⌈log₂Q⌉ = r_Q` rather than an inequality. -/
theorem outerSelectorCost_exact (bout : ℕ) (δU : ℝ) :
    (2 : ℝ) ^ entryLevelA bout δU 0 = ((Qwidth bout δU : ℕ) : ℝ) ∧
      Qwidth bout δU = 2 ^ rQ bout δU ∧
      Nat.clog 2 (Qwidth bout δU) = rQ bout δU :=
  ⟨topLevelWidth_pow_eq bout δU, Qwidth_eq_two_pow bout δU,
    canonicalSelectorBits bout δU⟩

/-- **Aux 8 (the M8 licence for the inner `log₂q`).**

The same rule at the **other** interlace width: `q = 2^{w_q}` is a power of two
by construction (`09-first-wrapper.tex`, reader `05-iteration.tex:101`), so its
selector costs exactly `w_q` bits and `log₂q` is legal notation.  General in
`w_q`, and kept separate from aux 7 so the two widths are never conflated. -/
theorem alignedSelectorCost_exact (wq : ℕ) : Nat.clog 2 (2 ^ wq) = wq :=
  clog_two_pow wq

open Workspace.Types.Protocol in
/-- **Aux 9 (a cost-zero protocol computes only constants).**

`Protocol.cost` is the tree depth, so a protocol of cost `0` is a leaf and its
output does not read either party's input.  General in both carriers and in the
protocol; this is the mechanism behind the `comp ≥ 1` guard of
`def:robust-seed` (`03-preliminaries.tex:244`). -/
lemma computes_const_of_cost_zero {A B : Type*} (P : Protocol A B Bool)
    (f : A → B → Bool) (hc : P.cost = 0) (hf : Protocol.Computes P f) :
    ∀ x y x' y', f x y = f x' y' := by
  cases P with
  | leaf z =>
      intro x y x' y'
      have h1 := hf x y
      have h2 := hf x' y'
      simp only [Protocol.eval] at h1 h2
      rw [← h1, ← h2]
  | aNode a l r => simp [Protocol.cost] at hc
  | bNode b l r => simp [Protocol.cost] at hc

open Workspace.Types.Protocol in
/-- **Aux 10 (nonconstant functions have `comp ≥ 1`).**

The readout of aux 9 at the infimum: if some protocol computes `f` at all, and
`f` takes two different values, then `comp f ≥ 1`.  This is the literal first
clause of `def:robust-seed` (`03-preliminaries.tex:244`) made checkable.
General in both carriers. -/
lemma one_le_D_of_not_const {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) (hne : (AchievableCosts f).Nonempty)
    (h : ¬ ∀ x y x' y', f x y = f x' y') : 1 ≤ D f := by
  rcases Nat.eq_zero_or_pos (D f) with h0 | hpos
  swap
  · exact hpos
  exfalso
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem hne
  exact h (computes_const_of_cost_zero P f (by rw [hcost]; exact h0) hcomp)

open Workspace.Types.Protocol in
/-- **Aux 11 (two bits suffice on a two-element row carrier).**

For **every** `f : Bool → Bool → Bool`, Alice announces her bit and Bob answers
with the value: an `aNode` over two `bNode`s has depth `2` and computes `f`.
Hence `comp f ≤ 2` on `Bool × Bool`.

General in `f`, which is what makes the cardinality refutation of Part 5 a
statement about every table rather than about one. -/
lemma achievableCosts_bool_two (f : Bool → Bool → Bool) :
    (2 : ℕ) ∈ AchievableCosts f := by
  refine ⟨Protocol.aNode (fun x => x)
      (Protocol.bNode (fun y => y) (Protocol.leaf (f false false))
        (Protocol.leaf (f false true)))
      (Protocol.bNode (fun y => y) (Protocol.leaf (f true false))
        (Protocol.leaf (f true true))), ?_, ?_⟩
  · simp [Protocol.cost]
  · intro x y
    cases x <;> cases y <;> simp [Protocol.eval]

/-- **Aux 11b.**  The bound itself: `comp f ≤ 2` for every Boolean function of
two Boolean inputs. -/
lemma D_bool_le_two (f : Bool → Bool → Bool) : D f ≤ 2 :=
  Nat.sInf_le (achievableCosts_bool_two f)

open Workspace.Types.Protocol in
/-- **Aux 12a.**  One Alice bit computes the projection `(x, y) ↦ x`. -/
lemma achievableCosts_aliceBit :
    (1 : ℕ) ∈ AchievableCosts (fun x _ : Bool => x) := by
  refine ⟨Protocol.aNode (fun x => x) (Protocol.leaf false)
      (Protocol.leaf true), ?_, ?_⟩
  · simp [Protocol.cost]
  · intro x y
    cases x <;> simp [Protocol.eval]

/-- **Aux 12b (an exact `comp` value).**

`comp` of the projection `(x, y) ↦ x` on `Bool × Bool` is **exactly** `1`: the
upper bound is aux 12a and the lower bound is aux 10, since the projection is
not constant.  A round trip of aux 9--11, and the only exact `comp` value this
module needs — it is what makes the Part-5 inhabitants *realizable* rather than
merely unrefuted. -/
lemma D_aliceBit : D (fun x _ : Bool => x) = 1 := by
  refine le_antisymm (Nat.sInf_le achievableCosts_aliceBit) ?_
  refine one_le_D_of_not_const _ ⟨1, achievableCosts_aliceBit⟩ ?_
  intro h
  have h' := h true true false false
  simp at h'

/-! ## Part 1b: the fixed-output rank corollary and the full-cube seed

This part exists because of one arithmetic fact recorded by the frozen paper
itself at `03-preliminaries.tex:86--90`:

> "Thus a rank argument that counts leaves of one colour may be **one bit
> below** a bound obtained from the total number of leaves.  This is a feature
> of that argument, not a conversion between two definitions of communication
> complexity."

The inherited total-rank bound (`Workspace.LogRankBound.logRank_lowerBound`,
`comp ≥ log₂ rank`) is exactly that one bit short at every site the seed needs,
so it cannot deliver `comp F_b = a + 1`.  The frozen route to the missing bit is
`lem:fixed-output-leaves` (`03-preliminaries.tex:45--50`) followed by
`cor:fixed-output-rank` (`03-preliminaries.tex:66--84`), and that is what is
traced here.

**Deviation from the frozen proof text, recorded.**  The frozen proof of
`lem:fixed-output-leaves` counts `β`-leaves of a *reduced* protocol
(`def:reduced-protocol`, `03-preliminaries.tex:34--43`).  Reduction is a
protocol-rewriting operation; formalizing it faithfully is a development of its
own.  `protocol_indR_rank_bound` below proves the **same `2^{d-1}` one-colour
count** without it, by induction on the protocol tree: the `β`-indicator of a
node splits as `D₀·M_l + D₁·M_r` (rows) or `M_l·E₀ + M_r·E₁` (columns), rank is
subadditive, and a *constant* child contributes rank at most one — so the only
place reducedness was used, the depth-one base case where two equal leaf labels
would double-count, is replaced by the observation that two equal leaf labels
make the whole node constant, contradicting the nonconstancy hypothesis.  The
conclusion is byte-identical to `cor:fixed-output-rank`'s hypothesis
`rank_ℝ(1_{M=β}) > 2^{d-1}`.

The full cube itself is `eq:full-cube-seed` (`12-iteration-specification.tex:23--30`),
reader `lem:paper-full-cube-seed` (`05-iteration.tex:26--44`).

### Two candidate encodings of the seed matrix, and why this one landed

* **Candidate A (landed).**  `fullCube q : (Fin q → Bool) → Fin q → Bool`,
  `γ j ↦ γ j`.  Rows are `{0,1}^{q}` and columns are the frozen `[q]`, in
  zero-based `Fin` slots (`conv:finite-slots`).  Six general aux lemmas close
  on it (`fullCube_apply`, `fullCube_not_const`, `fullCube_rank_ge`,
  `fullCube_D_le`, `fullCube_D_ge`, `fullCube_D_eq`) plus the two family
  lemmas `bracket_row_univ` and `fullCube_bracket_ge`.
* **Candidate B (rejected).**  Columns as bit-strings, `(Fin q → Bool) → (Fin a
  → Bool) → Bool` with `q = 2^a`.  Its `YES`-side announce protocol is one line
  shorter, but it *changes the frozen column carrier* from `[q_seed]` to
  `{0,1}^{a_seed}` and forces `q = 2^{a}` where the frozen text fixes
  `q_seed = 2^{a_seed} - 2`.  The bracket column threshold
  `⌈|Cols|^p · y⌉` would then be read at a cardinality the paper does not have,
  so `fullCube_bracket_ge`'s rung arithmetic would certify a different matrix.
  Rejected on faithfulness before any aux lemma was attempted. -/

/-- **The real one-colour indicator `1_{M=β}`** of
`03-preliminaries.tex:64--65`: "For a Boolean matrix `M`, let `1_{M=β}` denote
the real zero--one matrix indicating the entries on which `M = β`."

Carrier-generic on purpose: `cor:fixed-output-rank` is applied below both to the
full cube itself and to the *subgame* of a bracket member, whose carriers are
`Finset` subtypes rather than initial segments. -/
noncomputable def indR {X Y : Type*} (f : X → Y → Bool) (β : Bool) :
    Matrix X Y ℝ :=
  Matrix.of (fun i j => if f i j = β then (1 : ℝ) else 0)

/-- **Aux 13 (readout).**  `indR` is the entrywise indicator and nothing else.
General in both carriers, in `f`, and in `β`. -/
lemma indR_apply {X Y : Type*} (f : X → Y → Bool) (β : Bool) (i : X) (j : Y) :
    indR f β i j = if f i j = β then (1 : ℝ) else 0 := rfl

/-- **Aux 14 (rank subadditivity).**  `rank (A + B) ≤ rank A + rank B` over an
arbitrary column carrier.

The vendored `Workspace.LogRankBound.rank_add_le` is stated only for
`Fin m × Fin n`; the proof is reproduced here verbatim in shape at general
carriers so that no transport to `BoolMat` is needed.  This is the
subadditivity the frozen proof of `cor:fixed-output-rank` invokes
(`03-preliminaries.tex:78--81`). -/
lemma rank_add_le_generic {X Y : Type*} [Fintype Y] (A B : Matrix X Y ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    intro v hv
    obtain ⟨w, hw⟩ := hv
    rw [← hw]
    simp only [LinearMap.add_apply]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ⟨w, rfl⟩) (Submodule.mem_sup_right ⟨w, rfl⟩)
  calc (A + B).rank
      = Module.finrank ℝ ↥(LinearMap.range (A + B).mulVecLin) := rfl
    _ ≤ Module.finrank ℝ
          ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono hsub
    _ ≤ Module.finrank ℝ ↥(LinearMap.range A.mulVecLin) +
          Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = A.rank + B.rank := rfl

/-- **Aux 15 (a monochromatic rectangle has rank at most one).**

`03-preliminaries.tex:79--80`, "The indicator of each nonempty rectangle has
real rank one".  General in both carriers and in `β`. -/
lemma indR_rank_le_one_of_const {X Y : Type*} [Fintype Y] {f : X → Y → Bool}
    {c : Bool} (hc : ∀ x y, f x y = c) (β : Bool) : (indR f β).rank ≤ 1 := by
  have h : indR f β
      = Matrix.vecMulVec (fun _ : X => (1 : ℝ))
          (fun _ : Y => if c = β then (1 : ℝ) else 0) := by
    ext i j
    simp [indR, Matrix.vecMulVec, hc i j]
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

open Workspace.Types.Protocol in
/-- **Aux 16 (cost-zero protocols are constant, in the value form).**

Aux 9 delivers `∀ x y x' y', f x y = f x' y'`, which is vacuous on an empty
carrier; the induction below needs the *value*, so it is extracted here from the
leaf directly.  General in both carriers. -/
lemma eval_const_of_cost_zero {X Y : Type*} (P : Protocol X Y Bool)
    (hc : P.cost = 0) : ∃ c, ∀ x y, Protocol.eval P x y = c := by
  cases P with
  | leaf z => exact ⟨z, fun _ _ => rfl⟩
  | aNode a l r => simp [Protocol.cost] at hc
  | bNode b l r => simp [Protocol.cost] at hc

open Workspace.Types.Protocol in
/-- **Aux 17.**  Contrapositive of aux 16: a nonconstant protocol has depth at
least one.  General in both carriers. -/
lemma one_le_cost_of_not_const {X Y : Type*} (P : Protocol X Y Bool)
    (h : ¬ ∃ c, ∀ x y, Protocol.eval P x y = c) : 1 ≤ P.cost := by
  rcases Nat.eq_zero_or_pos P.cost with h0 | hpos
  · exact absurd (eval_const_of_cost_zero P h0) h
  · exact hpos

open Workspace.Types.Protocol in
/-- **`lem:fixed-output-leaves` in rank form** (`03-preliminaries.tex:45--50`).

> "Let `P` be a nonconstant reduced binary deterministic protocol of depth at
> most `d ≥ 1`.  For either output value `β ∈ {0,1}`, the number of
> `β`-labelled leaves of `P` is at most `2^{d-1}`."

Stated as `2 · rank(1_{eval P = β}) ≤ 2^{cost P}` — i.e. `rank ≤ 2^{d-1}` for
every `d ≥ cost P` — because the rank of the one-colour indicator is what
`cor:fixed-output-rank` actually consumes, and because `ℕ`-subtraction in the
exponent is thereby avoided.  See the deviation note at the head of this part:
the `2^{d-1}` count is obtained without formalizing `def:reduced-protocol`.

General in both carriers, in the protocol, and in `β`. -/
lemma protocol_indR_rank_bound {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (β : Bool) :
    ∀ P : Protocol X Y Bool, (¬ ∃ c, ∀ x y, Protocol.eval P x y = c) →
      2 * (indR (Protocol.eval P) β).rank ≤ 2 ^ P.cost := by
  intro P
  induction P with
  | leaf z =>
      intro h
      exact absurd ⟨z, fun _ _ => rfl⟩ h
  | aNode a l r ihl ihr =>
      intro h
      set Ml := indR (Protocol.eval l) β with hMl
      set Mr := indR (Protocol.eval r) β with hMr
      set D0 : Matrix X X ℝ :=
        Matrix.diagonal (fun i => if a i then (0 : ℝ) else 1) with hD0
      set D1 : Matrix X X ℝ :=
        Matrix.diagonal (fun i => if a i then (1 : ℝ) else 0) with hD1
      have hdecomp : indR (Protocol.eval (Protocol.aNode a l r)) β
          = D0 * Ml + D1 * Mr := by
        rw [hMl, hMr, hD0, hD1]
        ext i j
        simp only [indR, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
        by_cases hai : a i
        · simp [Protocol.eval, hai]
        · simp [Protocol.eval, hai]
      have hstep : (indR (Protocol.eval (Protocol.aNode a l r)) β).rank
          ≤ Ml.rank + Mr.rank := by
        rw [hdecomp]
        calc (D0 * Ml + D1 * Mr).rank ≤ (D0 * Ml).rank + (D1 * Mr).rank :=
              rank_add_le_generic _ _
          _ ≤ Ml.rank + Mr.rank :=
              Nat.add_le_add (Matrix.rank_mul_le_right _ _)
                (Matrix.rank_mul_le_right _ _)
      have hcost : (Protocol.aNode a l r).cost = 1 + max l.cost r.cost := rfl
      have hpow : 2 ^ (Protocol.aNode a l r).cost
          = 2 ^ max l.cost r.cost + 2 ^ max l.cost r.cost := by
        rw [hcost, pow_add]; ring
      by_cases hlc : ∃ c, ∀ x y, Protocol.eval l x y = c
      · by_cases hrc : ∃ c, ∀ x y, Protocol.eval r x y = c
        · obtain ⟨cl, hcl⟩ := hlc
          obtain ⟨cr, hcr⟩ := hrc
          have hne : cl ≠ cr := by
            intro hEq
            refine h ⟨cl, fun x y => ?_⟩
            by_cases hax : a x
            · simp [Protocol.eval, hax, hcr x y, hEq]
            · simp [Protocol.eval, hax, hcl x y]
          have hone : Ml.rank + Mr.rank ≤ 1 := by
            rcases Bool.eq_or_eq_not cl β with hb | hb
            · have hMr0 : Mr = 0 := by
                rw [hMr]; ext i j
                have hcrb : cr ≠ β := fun hcb => hne (hb.trans hcb.symm)
                simp [indR, hcr i j, hcrb]
              rw [hMr0, Matrix.rank_zero]
              simpa using indR_rank_le_one_of_const hcl β
            · have hMl0 : Ml = 0 := by
                rw [hMl]; ext i j
                have hclb : cl ≠ β := by rw [hb]; cases β <;> simp
                simp [indR, hcl i j, hclb]
              rw [hMl0, Matrix.rank_zero]
              simpa using indR_rank_le_one_of_const hcr β
          have hfin : (indR (Protocol.eval (Protocol.aNode a l r)) β).rank ≤ 1 :=
            le_trans hstep hone
          have h2 : (2 : ℕ) ≤ 2 ^ max l.cost r.cost + 2 ^ max l.cost r.cost := by
            have : (1 : ℕ) ≤ 2 ^ max l.cost r.cost := Nat.one_le_two_pow
            omega
          omega
        · have hrpos : 1 ≤ r.cost := one_le_cost_of_not_const r hrc
          have hr := ihr hrc
          have hl : Ml.rank ≤ 1 := by
            obtain ⟨cl, hcl⟩ := hlc
            simpa [hMl] using indR_rank_le_one_of_const hcl β
          have hmax : 1 ≤ max l.cost r.cost := le_trans hrpos (le_max_right _ _)
          have hrle : 2 * Mr.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hr (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
          have h2 : (2 : ℕ) ≤ 2 ^ max l.cost r.cost := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ max l.cost r.cost :=
                  Nat.pow_le_pow_right (by norm_num) hmax
          omega
      · by_cases hrc : ∃ c, ∀ x y, Protocol.eval r x y = c
        · have hlpos : 1 ≤ l.cost := one_le_cost_of_not_const l hlc
          have hl := ihl hlc
          have hr : Mr.rank ≤ 1 := by
            obtain ⟨cr, hcr⟩ := hrc
            simpa [hMr] using indR_rank_le_one_of_const hcr β
          have hmax : 1 ≤ max l.cost r.cost := le_trans hlpos (le_max_left _ _)
          have hlle : 2 * Ml.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hl (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          have h2 : (2 : ℕ) ≤ 2 ^ max l.cost r.cost := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ max l.cost r.cost :=
                  Nat.pow_le_pow_right (by norm_num) hmax
          omega
        · have hl := ihl hlc
          have hr := ihr hrc
          have hlle : 2 * Ml.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hl (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          have hrle : 2 * Mr.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hr (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
          omega
  | bNode b l r ihl ihr =>
      intro h
      set Ml := indR (Protocol.eval l) β with hMl
      set Mr := indR (Protocol.eval r) β with hMr
      set E0 : Matrix Y Y ℝ :=
        Matrix.diagonal (fun j => if b j then (0 : ℝ) else 1) with hE0
      set E1 : Matrix Y Y ℝ :=
        Matrix.diagonal (fun j => if b j then (1 : ℝ) else 0) with hE1
      have hdecomp : indR (Protocol.eval (Protocol.bNode b l r)) β
          = Ml * E0 + Mr * E1 := by
        rw [hMl, hMr, hE0, hE1]
        ext i j
        simp only [indR, Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal]
        by_cases hbj : b j
        · simp [Protocol.eval, hbj]
        · simp [Protocol.eval, hbj]
      have hstep : (indR (Protocol.eval (Protocol.bNode b l r)) β).rank
          ≤ Ml.rank + Mr.rank := by
        rw [hdecomp]
        calc (Ml * E0 + Mr * E1).rank ≤ (Ml * E0).rank + (Mr * E1).rank :=
              rank_add_le_generic _ _
          _ ≤ Ml.rank + Mr.rank :=
              Nat.add_le_add (Matrix.rank_mul_le_left _ _)
                (Matrix.rank_mul_le_left _ _)
      have hcost : (Protocol.bNode b l r).cost = 1 + max l.cost r.cost := rfl
      have hpow : 2 ^ (Protocol.bNode b l r).cost
          = 2 ^ max l.cost r.cost + 2 ^ max l.cost r.cost := by
        rw [hcost, pow_add]; ring
      by_cases hlc : ∃ c, ∀ x y, Protocol.eval l x y = c
      · by_cases hrc : ∃ c, ∀ x y, Protocol.eval r x y = c
        · obtain ⟨cl, hcl⟩ := hlc
          obtain ⟨cr, hcr⟩ := hrc
          have hne : cl ≠ cr := by
            intro hEq
            refine h ⟨cl, fun x y => ?_⟩
            by_cases hby : b y
            · simp [Protocol.eval, hby, hcr x y, hEq]
            · simp [Protocol.eval, hby, hcl x y]
          have hone : Ml.rank + Mr.rank ≤ 1 := by
            rcases Bool.eq_or_eq_not cl β with hb | hb
            · have hMr0 : Mr = 0 := by
                rw [hMr]; ext i j
                have hcrb : cr ≠ β := fun hcb => hne (hb.trans hcb.symm)
                simp [indR, hcr i j, hcrb]
              rw [hMr0, Matrix.rank_zero]
              simpa using indR_rank_le_one_of_const hcl β
            · have hMl0 : Ml = 0 := by
                rw [hMl]; ext i j
                have hclb : cl ≠ β := by rw [hb]; cases β <;> simp
                simp [indR, hcl i j, hclb]
              rw [hMl0, Matrix.rank_zero]
              simpa using indR_rank_le_one_of_const hcr β
          have hfin : (indR (Protocol.eval (Protocol.bNode b l r)) β).rank ≤ 1 :=
            le_trans hstep hone
          have h2 : (2 : ℕ) ≤ 2 ^ max l.cost r.cost + 2 ^ max l.cost r.cost := by
            have : (1 : ℕ) ≤ 2 ^ max l.cost r.cost := Nat.one_le_two_pow
            omega
          omega
        · have hrpos : 1 ≤ r.cost := one_le_cost_of_not_const r hrc
          have hr := ihr hrc
          have hl : Ml.rank ≤ 1 := by
            obtain ⟨cl, hcl⟩ := hlc
            simpa [hMl] using indR_rank_le_one_of_const hcl β
          have hmax : 1 ≤ max l.cost r.cost := le_trans hrpos (le_max_right _ _)
          have hrle : 2 * Mr.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hr (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
          have h2 : (2 : ℕ) ≤ 2 ^ max l.cost r.cost := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ max l.cost r.cost :=
                  Nat.pow_le_pow_right (by norm_num) hmax
          omega
      · by_cases hrc : ∃ c, ∀ x y, Protocol.eval r x y = c
        · have hlpos : 1 ≤ l.cost := one_le_cost_of_not_const l hlc
          have hl := ihl hlc
          have hr : Mr.rank ≤ 1 := by
            obtain ⟨cr, hcr⟩ := hrc
            simpa [hMr] using indR_rank_le_one_of_const hcr β
          have hmax : 1 ≤ max l.cost r.cost := le_trans hlpos (le_max_left _ _)
          have hlle : 2 * Ml.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hl (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          have h2 : (2 : ℕ) ≤ 2 ^ max l.cost r.cost := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ max l.cost r.cost :=
                  Nat.pow_le_pow_right (by norm_num) hmax
          omega
        · have hl := ihl hlc
          have hr := ihr hrc
          have hlle : 2 * Ml.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hl (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          have hrle : 2 * Mr.rank ≤ 2 ^ max l.cost r.cost :=
            le_trans hr (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
          omega

open Workspace.Types.Protocol in
/-- **`cor:fixed-output-rank`** (`03-preliminaries.tex:66--84`).

> "Let `M` be nonconstant, let `d ≥ 1`, and let `β ∈ {0,1}`.  If
> `rank_ℝ(1_{M=β}) > 2^{d-1}`, then `comp M ≥ d + 1`."

Every hypothesis of the frozen statement is a binder here — nonconstancy, the
guard `d ≥ 1`, the fixed colour `β`, and the strict rank inequality — and the
conclusion is the frozen `d + 1`, not `d`.  This is the declaration that
supplies the bit the total-rank bound cannot (`03-preliminaries.tex:86--90`).

General in both carriers.  Adapted proof (the frozen argument with reduction
replaced as recorded at the head of this part). -/
theorem fixedOutputRank {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y → Bool) (β : Bool) (d : ℕ)
    (hd : 1 ≤ d) (hnc : ¬ ∃ c, ∀ x y, f x y = c)
    (hrank : 2 ^ (d - 1) < (indR f β).rank) : d + 1 ≤ D f := by
  by_contra hcon
  have hDd : D f ≤ d := by omega
  have hne : (AchievableCosts f).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty f
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem hne
  have hev : Protocol.eval P = f := by
    funext x y; exact hcomp x y
  have hPnc : ¬ ∃ c, ∀ x y, Protocol.eval P x y = c := by rw [hev]; exact hnc
  have h := protocol_indR_rank_bound β P hPnc
  rw [hev] at h
  have hcd : P.cost ≤ d := by
    have hc : P.cost = D f := hcost
    omega
  have h2 : 2 * (indR f β).rank ≤ 2 ^ d :=
    le_trans h (Nat.pow_le_pow_right (by norm_num) hcd)
  have hdd : 2 ^ d = 2 * 2 ^ (d - 1) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
    subst hk
    rw [pow_add]
    simp
  omega

/-- **The full-cube matrix `F_b` of `eq:full-cube-seed`**
(`12-iteration-specification.tex:23--30`), reader `lem:paper-full-cube-seed`
(`05-iteration.tex:34--38`):

```
F_b : {0,1}^{q} × [q] → {0,1},      F_b(γ, j) = γ(j).
```

Alice holds `γ`, Bob holds `j`, carriers are the zero-based finite slots of
`conv:finite-slots`.  The width `q` is a binder: the frozen `q_seed` is pinned
only at the witness (`fullCubeSeed_parameters`), never inside the construction,
so that `M1` is respected and no promise-side or budget conclusion is data. -/
def fullCube (q : ℕ) : (Fin q → Bool) → Fin q → Bool := fun γ j => γ j

/-- The unit-vector rows of `12-iteration-specification.tex:47--48`,
"Restricting to the unit-vector rows gives the `q_seed`-dimensional identity
matrix". -/
def cubeUnit (q : ℕ) (j : Fin q) : Fin q → Bool := fun i => decide (i = j)

/-- **Aux 18 (readout).**  `fullCube` is the frozen `γ(j)` and nothing else. -/
lemma fullCube_apply (q : ℕ) (γ : Fin q → Bool) (j : Fin q) :
    fullCube q γ j = γ j := rfl

/-- **Aux 19 (the unit rows carve out the identity).**
`fullCube q (e_j) k = [k = j]`, the frozen identity submatrix
(`12-iteration-specification.tex:47--48`). -/
lemma fullCube_unit (q : ℕ) (j k : Fin q) :
    fullCube q (cubeUnit q j) k = decide (k = j) := rfl

/-- **Aux 20 (nonconstancy).**  `12-iteration-specification.tex:50--52`,
"Because `q_seed > 2^{a_seed - 1}` and `a_seed ≥ 3`, this restriction is
nonconstant."  General in `q ≥ 1`; the frozen inequality is one sufficient
condition for `q ≥ 1` and is checked at the witness. -/
lemma fullCube_not_const (q : ℕ) (hq : 1 ≤ q) :
    ¬ ∃ c, ∀ γ j, fullCube q γ j = c := by
  rintro ⟨c, hc⟩
  have j0 : Fin q := ⟨0, hq⟩
  have h1 : false = c := hc (fun _ => false) j0
  have h2 : true = c := hc (fun _ => true) j0
  exact Bool.noConfusion (h1.trans h2.symm)

/-- **Aux 21 (the identity submatrix).**  The one-indicator of the full cube has
real rank at least `q`, because the `q` unit-vector rows carve out `I_q`
(`12-iteration-specification.tex:47--49`, "whose one-output indicator has real
rank `q_seed`").  General in `q`. -/
lemma fullCube_rank_ge (q : ℕ) : q ≤ (indR (fullCube q) true).rank := by
  classical
  set A := indR (fullCube q) true with hA
  set S : Matrix (Fin q) (Fin q → Bool) ℝ :=
    Matrix.of (fun j γ => if γ = cubeUnit q j then (1 : ℝ) else 0) with hS
  have hmul : S * A = (1 : Matrix (Fin q) (Fin q) ℝ) := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [hS, Matrix.of_apply]
    rw [Finset.sum_eq_single (cubeUnit q j)]
    · simp only [hA, indR, Matrix.of_apply, fullCube,
        cubeUnit, Matrix.one_apply]
      by_cases h : k = j
      · simp [h]
      · simp [h, Ne.symm h]
    · intro γ _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : (1 : Matrix (Fin q) (Fin q) ℝ).rank = q := by
    simp
  calc q = (S * A).rank := by rw [hmul, h1]
    _ ≤ A.rank := Matrix.rank_mul_le_right _ _

open Workspace.Types.Protocol in
/-- **The `YES`-side half of `lem:full-cube-seed`'s complexity claim**
(`12-iteration-specification.tex:46--47`): "Bob sends `j` using `a_seed` bits
and Alice sends the selected bit, so `comp F_b ≤ a_seed + 1`."

The protocol is the vendored `Workspace.UpperBound.bobAnnounceTree` at width `a`
with an Alice leaf; the encoding of `[q]` into `a` bits is the embedding
supplied by `q ≤ 2^a`.  General in `q` and `a`. -/
lemma fullCube_D_le (q a : ℕ) (hqa : q ≤ 2 ^ a) : D (fullCube q) ≤ a + 1 := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq1
  · have h0 : (0 : ℕ) ∈ AchievableCosts (fullCube 0) :=
      ⟨Protocol.leaf false, rfl, fun _ j => j.elim0⟩
    exact le_trans (Nat.sInf_le h0) (Nat.zero_le _)
  haveI : Nonempty (Fin q) := ⟨⟨0, hq1⟩⟩
  have hcard : Fintype.card (Fin q) ≤ Fintype.card (Fin a → Bool) := by
    simpa [Fintype.card_fun] using hqa
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard
  set dec : (Fin a → Bool) → Fin q := Function.invFun enc with hdecdef
  have hdec : ∀ j, dec (enc j) = j := Function.leftInverse_invFun enc.injective
  set leafP : (Fin a → Bool) → Protocol (Fin q → Bool) (Fin q) Bool :=
    fun w => Protocol.aNode (fun γ => γ (dec w)) (Protocol.leaf false)
      (Protocol.leaf true) with hleafP
  set T : Protocol (Fin q → Bool) (Fin q) Bool :=
    Workspace.UpperBound.bobAnnounceTree a leafP (fun j => enc j) with hT
  have hTcost : T.cost ≤ a + 1 := by
    have h := Workspace.UpperBound.bobAnnounceTree_cost
      (A := (Fin q → Bool)) (B := Fin q) (Z := Bool)
      1 a leafP (fun j => enc j) (fun w => by simp [hleafP, Protocol.cost])
    simpa [hT] using h
  have hTeval : ∀ γ j, T.eval γ j = fullCube q γ j := by
    intro γ j
    have h := Workspace.UpperBound.bobAnnounceTree_eval a leafP (fun j => enc j) γ j
    rw [hT, h, hleafP]
    simp only [Protocol.eval, hdec j]
    by_cases hg : γ j <;> simp [hg, fullCube]
  exact le_trans (Nat.sInf_le ⟨T, rfl, hTeval⟩) hTcost

/-- **The `NO`-side half of `lem:full-cube-seed`'s complexity claim**
(`12-iteration-specification.tex:47--53`): the identity submatrix has rank
`q_seed > 2^{a_seed - 1}`, so `cor:fixed-output-rank` at `(β, d) = (1, a_seed)`
gives `comp F_b ≥ a_seed + 1`.  General in `q` and `a`. -/
lemma fullCube_D_ge (q a : ℕ) (ha : 1 ≤ a) (hq : 2 ^ (a - 1) < q) :
    a + 1 ≤ D (fullCube q) := by
  have hq1 : 1 ≤ q := lt_of_le_of_lt (Nat.zero_le _) hq
  refine fixedOutputRank (fullCube q) true a ha (fullCube_not_const q hq1) ?_
  exact lt_of_lt_of_le hq (fullCube_rank_ge q)

/-- **Aux 22 (the exact complexity, a round trip of aux 21 and the announce
protocol).**  `comp F_b = a_seed + 1`, the first display of
`lem:full-cube-seed` (`12-iteration-specification.tex:33--36`).  General in
`q` and `a` under the frozen sandwich `2^{a-1} < q ≤ 2^{a}`, which the frozen
`q_seed = 2^{a_seed} - 2` with `a_seed ≥ 3` satisfies. -/
lemma fullCube_D_eq (q a : ℕ) (ha : 1 ≤ a) (hlo : 2 ^ (a - 1) < q)
    (hhi : q ≤ 2 ^ a) : D (fullCube q) = a + 1 :=
  le_antisymm (fullCube_D_le q a hhi) (fullCube_D_ge q a ha hlo)

/-- **Aux 23 (at requested depth zero the bracket keeps every row).**

`def:bracket` (`03-preliminaries.tex`, vendored as `NPCC.bracketGE`) demands a
row set that is `([p], ⌈m·x⌉)`-equipartitioned.  At `x = 2^{-b}` with `b = 0`
the threshold is `m` itself, and the ambient row carrier of the one-fold
interlace is `Fin 1 × X` with exactly `m` elements, so the row set is forced to
be everything.  General in both carriers and in the column density `y`.

This is the only place the requested depth enters, and it is why the depth-zero
instance below does **not** need the row-density leg of `lem:full-cube-seed`'s
proof (`12-iteration-specification.tex:60--64`). -/
lemma bracket_row_univ {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    {R : Finset (Fin 1 × X)} {C : Finset (Fin 1 → Y)} {y : ℝ}
    (h : (R, C) ∈ bracketGE X Y 1 (xOut 0) y) : R = Finset.univ := by
  obtain ⟨hrow, -⟩ := h
  have hx0 : xOut 0 = 1 := by simp [xOut]
  have hthr : ⌈(Fintype.card X : ℝ) * xOut 0⌉₊ = Fintype.card X := by
    rw [hx0, mul_one]; exact Nat.ceil_natCast _
  have hfib := hrow (0 : Fin 1) (Finset.mem_univ _)
  rw [hthr] at hfib
  refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
  have hc : Fintype.card (Fin 1 × X) = Fintype.card X := by simp
  rw [hc]
  exact le_trans hfib (Finset.card_filter_le _ _)

/-- **Aux 23b (a one-slot column tuple is its single entry).**

`conv:finite-slots` makes the one-fold interlace's Bob carrier `Fin 1 → Y`; two
such tuples agreeing at slot `0` are equal.  This is what makes the retained
identity submatrix of aux 25 genuinely square. -/
lemma fin1_fun_ext {Y : Type*} {c c' : Fin 1 → Y} (h : c 0 = c' 0) : c = c' := by
  funext i
  fin_cases i
  exact h

/-- **Aux 24.**  Value form of aux 10, needed where the empty-carrier-vacuous
`∀ x y x' y'` form is not available.  General in both carriers. -/
lemma one_le_D_of_no_const_value {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) (h : ¬ ∃ c, ∀ x y, f x y = c) : 1 ≤ D f := by
  rcases Nat.eq_zero_or_pos (D f) with h0 | hpos
  swap
  · exact hpos
  exfalso
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty f)
  have hev : Workspace.Types.Protocol.Protocol.eval P = f := by
    funext x y; exact hcomp x y
  have hc0 : P.cost = 0 := by rw [hcost]; exact h0
  obtain ⟨c, hc⟩ := eval_const_of_cost_zero P hc0
  rw [hev] at hc
  exact h ⟨c, hc⟩

/-- **The three-rung family bound for the full cube at requested depth zero**
(`12-iteration-specification.tex:64--76`).

For every bracket member at row density `2^{-0}` and column density `y`, the
retained matrix keeps *all* rows (aux 23), so the identity submatrix on the
retained columns survives intact and its one-indicator has rank at least
`|J|`.  The frozen `|J| - b > 2^{a_seed - t - 1}` therefore reads `|J| >
2^{d-1}` here, and `cor:fixed-output-rank` at `(β, d)` closes each rung.

`bracketGE.nonempty` is consumed **before** any lower bound is taken: `Dfamily`
is a `Nat.sInf` and returns `0` on the empty family, so lower-bounding it
without nonemptiness would be unsound.

General in `q`, in the rung index through `d`, and in the density `y`. -/
lemma fullCube_bracket_ge (q d : ℕ) (hd : 1 ≤ d) (y : ℝ) (hy1 : y ≤ 1)
    (hthr : 2 ^ (d - 1) < ⌈((Fintype.card (Fin q) : ℝ)) ^ (1 : ℕ) * y⌉₊) :
    d + 1 ≤ Dfamily (interlaceFun (fullCube q) 1)
      (bracketGE (Fin q → Bool) (Fin q) 1 (xOut 0) y) := by
  classical
  have hx1 : xOut 0 ≤ 1 := by simp [xOut]
  have hXpos : 1 ≤ Fintype.card (Fin q → Bool) := Fintype.card_pos
  have hne : (bracketGE (Fin q → Bool) (Fin q) 1 (xOut 0) y).Nonempty :=
    bracketGE.nonempty 1 (xOut 0) y hx1 hy1 hXpos
  have hall : ∀ RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut 0) y,
      d + 1 ≤ D (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2) := by
    rintro ⟨R, C⟩ hRC
    have hRuniv : R = Finset.univ := bracket_row_univ hRC
    obtain ⟨-, hcol⟩ := hRC
    simp only at hcol
    have hCcard : 2 ^ (d - 1) < C.card := lt_of_lt_of_le hthr hcol
    have hCpos : 0 < C.card := lt_of_le_of_lt (Nat.zero_le _) hCcard
    obtain ⟨c0, hc0⟩ := Finset.card_pos.mp hCpos
    set ρ : {c // c ∈ C} → {a // a ∈ R} :=
      fun c => ⟨(0, cubeUnit q (c.val 0)), by rw [hRuniv]; exact Finset.mem_univ _⟩
      with hρ
    have hval : ∀ (c c' : {c // c ∈ C}),
        subgame (interlaceFun (fullCube q) 1) R C (ρ c) c'
          = decide (c'.val 0 = c.val 0) := by
      intro c c'
      rfl
    have hnc : ¬ ∃ z, ∀ a c, subgame (interlaceFun (fullCube q) 1) R C a c = z := by
      rintro ⟨z, hz⟩
      have h1 : false = z :=
        hz ⟨(0, fun _ => false), by rw [hRuniv]; exact Finset.mem_univ _⟩ ⟨c0, hc0⟩
      have h2 : true = z := by
        have h := hz (ρ ⟨c0, hc0⟩) ⟨c0, hc0⟩
        rw [hval ⟨c0, hc0⟩ ⟨c0, hc0⟩] at h
        simpa using h
      exact Bool.noConfusion (h1.trans h2.symm)
    have hrank : C.card
        ≤ (indR (subgame (interlaceFun (fullCube q) 1) R C) true).rank := by
      set A := indR (subgame (interlaceFun (fullCube q) 1) R C) true with hA
      set Sm : Matrix {c // c ∈ C} {a // a ∈ R} ℝ :=
        Matrix.of (fun c a => if a = ρ c then (1 : ℝ) else 0) with hSm
      have hmul : Sm * A = 1 := by
        ext c c'
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single (ρ c)]
        · simp only [hSm, Matrix.of_apply, hA, indR,
            hval c c', Matrix.one_apply]
          by_cases h : c'.val 0 = c.val 0
          · have hcc : c = c' := Subtype.ext (fin1_fun_ext h).symm
            simp [h, hcc]
          · have hcc : c ≠ c' := by
              intro hEq; exact h (by rw [hEq])
            simp [h, hcc]
        · intro b _ hb; simp [hSm, hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h1 : (1 : Matrix {c // c ∈ C} {c // c ∈ C} ℝ).rank = C.card := by
        rw [Matrix.rank_one, Fintype.card_coe]
      calc C.card = (Sm * A).rank := by rw [hmul, h1]
        _ ≤ A.rank := Matrix.rank_mul_le_right _ _
    exact fixedOutputRank _ true d hd hnc (lt_of_lt_of_le hCcard hrank)
  obtain ⟨RC0, hRC0⟩ := hne
  have hSne : {n : ℕ | ∃ RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut 0) y,
      n = D (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2)}.Nonempty :=
    ⟨_, RC0, hRC0, rfl⟩
  obtain ⟨RC1, hRC1, hEq⟩ := Nat.sInf_mem hSne
  change d + 1 ≤ sInf _
  rw [hEq]
  exact hall RC1 hRC1

/-- **The three-rung minimum for the full cube at requested depth zero** — the
shape of the second display of `lem:full-cube-seed`
(`12-iteration-specification.tex:38--41`) evaluated at `q_seed = 126`,
`a_seed = 7` and `b = 0`.  It is **not** an instance of that lemma: the
subsection fixes `b ≥ 1` at line 16 (see the range disclosure on
`fullCubeSeed_parameters`).  What is proved here is a self-contained statement
about `fullCube 126` at row density `xOut 0 = 1`, whose proof reuses only the
frozen rung arithmetic.

`def:lambda` (`03-preliminaries.tex:224--231`) takes the minimum over
`j ∈ {0,1,2}` of `j + comp⟨M,1,x,y/2^j⟩`, so the three rungs are checked at
column densities `3/5`, `3/10`, `3/20` with offsets `0, 1, 2`, exactly as the
frozen proof does (`12-iteration-specification.tex:66--76`).  The ceilings are
the frozen `⌈|Cols|·y⌉` and are computed, not rounded away:

| rung `t` | frozen `|J|` floor | `2^{a_seed - t - 1}` | `d = a_seed - t` | rung value |
| --- | --- | --- | --- | --- |
| `0` | `⌈126·3/5⌉ = 76` | `64` | `7` | `8` |
| `1` | `⌈126·3/10⌉ = 38` | `32` | `6` | `1 + 7 = 8` |
| `2` | `⌈126·3/20⌉ = 19` | `16` | `5` | `2 + 6 = 8` |

Every row of the table satisfies the frozen strict inequality
`|J| - b > 2^{a_seed - t - 1}` at `b = 0`, and the guard `d ≥ 1` of
`cor:fixed-output-rank` holds because `a_seed = 7 ≥ 3` and `t ≤ 2`. -/
theorem fullCubeSeed_lambda :
    8 ≤ LambdaGE (fullCube 126) 1 (xOut 0) ((3 : ℝ) / 5) := by
  have h0 : 8 ≤ Dfamily (interlaceFun (fullCube 126) 1)
      (bracketGE (Fin 126 → Bool) (Fin 126) 1 (xOut 0) ((3 : ℝ) / 5)) := by
    have h := fullCube_bracket_ge 126 7 (by norm_num) ((3 : ℝ) / 5) (by norm_num) ?_
    · simpa using h
    · rw [Fintype.card_fin]
      exact Nat.lt_ceil.mpr (by norm_num)
  have h1 : 7 ≤ Dfamily (interlaceFun (fullCube 126) 1)
      (bracketGE (Fin 126 → Bool) (Fin 126) 1 (xOut 0) ((3 : ℝ) / 5 / 2)) := by
    have h := fullCube_bracket_ge 126 6 (by norm_num) ((3 : ℝ) / 5 / 2) (by norm_num) ?_
    · simpa using h
    · rw [Fintype.card_fin]
      exact Nat.lt_ceil.mpr (by norm_num)
  have h2 : 6 ≤ Dfamily (interlaceFun (fullCube 126) 1)
      (bracketGE (Fin 126 → Bool) (Fin 126) 1 (xOut 0) ((3 : ℝ) / 5 / 4)) := by
    have h := fullCube_bracket_ge 126 5 (by norm_num) ((3 : ℝ) / 5 / 4) (by norm_num) ?_
    · simpa using h
    · rw [Fintype.card_fin]
      exact Nat.lt_ceil.mpr (by norm_num)
  unfold LambdaGE
  exact le_min h0 (le_min (by omega) (by omega))

/-- **The exact complexity of the pinned seed.**  `comp F = a_seed + 1 = 8` at
`q_seed = 126`, `a_seed = 7`: the sandwich `2^{6} = 64 < 126 ≤ 128 = 2^{7}` is
the frozen `q_seed = 2^{a_seed} - 2`. -/
theorem fullCubeSeed_D : D (fullCube 126) = 8 :=
  fullCube_D_eq 126 7 (by norm_num) (by norm_num) (by norm_num)

/-- **The seed parameters, and the exact sense in which they are the paper's.**

`12-iteration-specification.tex:16--21` fixes `a_seed ≥ 3` to be the **least**
integer with `q_seed = 2^{a_seed} - 2 ≥ 64(b+1)`.  Evaluating that rule at
`b = 0` reads `2^{a} - 2 ≥ 64`, which `a = 7` satisfies and `a = 6` does not,
giving `a_seed = 7` and `q_seed = 126`.  Recorded as a theorem so the numeral
cannot drift silently.

**Range disclosure (read before consuming this).**  Line 16 of that anchor
opens with "Fix a requested depth `b ≥ 1`", so the minimality rule — like the
rest of `sec:full-cube-seed` — is *stated only for* `b ≥ 1`, and `b = 0` is
**outside** its frozen range.  Evaluating the displayed inequality at `b = 0`
is therefore an extrapolation of the frozen rule, not an instance of it: at the
paper's own first legal depth `b = 1` the rule instead selects `a_seed = 8`,
`q_seed = 254`, because `2^7 - 2 = 126 < 128 = 64·(1+1) ≤ 254 = 2^8 - 2`.
Nothing downstream may cite this theorem as "the paper's seed parameters at a
requested depth"; what it pins is the arithmetic of the numerals `7` and `126`
actually used by `fullCubeSeed_D` and `fullCubeSeed_lambda`, whose own content
is depth-free (`comp`) and taken at `xOut 0 = 1` (`Λ₃`) respectively. -/
theorem fullCubeSeed_parameters :
    (126 : ℕ) = 2 ^ 7 - 2 ∧ 3 ≤ 7 ∧ 64 * (0 + 1) ≤ 2 ^ 7 - 2 ∧
      ¬ (64 * (0 + 1) ≤ 2 ^ 6 - 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The floor `Λ`-bound for the two-element carrier** — the exact fix the
`cc-t1p-r1` statement gate prescribed for `seedInterface_realizable_no`.

At `b = 0` the row condition forces `R = univ` (aux 23) and the column
condition `⌈2·(3/5)⌉ = 2 ≤ |C|` forces `C` nonempty, so every member's induced
subgame still separates Alice's two rows; hence each rung is at least `1` and
the two shifted rungs are at least `1` for free.  Nonemptiness of the family is
taken from `bracketGE.nonempty` **first**, because `Dfamily` is a `Nat.sInf`
and would report `0` on an empty family. -/
theorem aliceBit_lambda :
    1 ≤ LambdaGE (fun x _ : Bool => x) 1 (xOut 0) ((3 : ℝ) / 5) := by
  classical
  have hx1 : xOut 0 ≤ 1 := by simp [xOut]
  have hne : (bracketGE Bool Bool 1 (xOut 0) ((3 : ℝ) / 5)).Nonempty :=
    bracketGE.nonempty 1 (xOut 0) ((3 : ℝ) / 5) hx1 (by norm_num) (by simp)
  have hall : ∀ RC ∈ bracketGE Bool Bool 1 (xOut 0) ((3 : ℝ) / 5),
      1 ≤ D (subgame (interlaceFun (fun x _ : Bool => x) 1) RC.1 RC.2) := by
    rintro ⟨R, C⟩ hRC
    have hRuniv : R = Finset.univ := bracket_row_univ hRC
    obtain ⟨-, hcol⟩ := hRC
    simp only at hcol
    have hCpos : 0 < C.card := by
      have h2 : (2 : ℕ) ≤ C.card := by
        refine le_trans ?_ hcol
        have hceil : ⌈((Fintype.card Bool : ℝ)) ^ (1 : ℕ) * ((3 : ℝ) / 5)⌉₊ = 2 := by
          simp only [Fintype.card_bool]
          rw [Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)]
          norm_num
        omega
      omega
    obtain ⟨c0, hc0⟩ := Finset.card_pos.mp hCpos
    refine one_le_D_of_no_const_value _ ?_
    rintro ⟨z, hz⟩
    have h1 : true = z :=
      hz ⟨(0, true), by rw [hRuniv]; exact Finset.mem_univ _⟩ ⟨c0, hc0⟩
    have h2 : false = z :=
      hz ⟨(0, false), by rw [hRuniv]; exact Finset.mem_univ _⟩ ⟨c0, hc0⟩
    exact Bool.noConfusion (h2.trans h1.symm)
  obtain ⟨RC0, hRC0⟩ := hne
  have hSne : {n : ℕ | ∃ RC ∈ bracketGE Bool Bool 1 (xOut 0) ((3 : ℝ) / 5),
      n = D (subgame (interlaceFun (fun x _ : Bool => x) 1) RC.1 RC.2)}.Nonempty :=
    ⟨_, RC0, hRC0, rfl⟩
  obtain ⟨RC1, hRC1, hEq⟩ := Nat.sInf_mem hSne
  have h0 : 1 ≤ Dfamily (interlaceFun (fun x _ : Bool => x) 1)
      (bracketGE Bool Bool 1 (xOut 0) ((3 : ℝ) / 5)) := by
    change 1 ≤ sInf _
    rw [hEq]
    exact hall RC1 hRC1
  unfold LambdaGE
  exact le_min h0 (le_min (by omega) (by omega))

/-! ## Part 2: the collection over an abstract scale-aligned matrix

The frozen subsection collects budgets for "an already admissible record"
(lines 537--538), so the scale-aligned matrix `W` enters abstractly, exactly as
the interfacebox of `09-first-wrapper.tex:1809--1816` demands: "From this point
onward, `W` is an ordinary Boolean matrix known only through
`eq:n`--`eq:common-low` and its explicit `YES` protocol."

The two promise cases are collected **separately**, as lines 512--520 and
525--534 state them.  `oneLevelBudgets_no` mentions no `YES` budget and
`oneLevelBudget_yes` mentions no `NO` complexity. -/

/-- **The `NO` half of the collection** (`10-direct-bridge.tex:512--521, 536`).

Both frozen readings, delivered together at the collected value `D + H + 1`:

* the **equality** of line 521, `comp R⁺ = D + H + 1`;
* the **ordinary robustness** of line 536,
  `Λ_{R⁺}(1, 2^{-b_out}, 3/5) ≥ D + H + 1`.

The premises are the frozen inputs and nothing else: the line-40 binder at the
aligned value `comp W = C_W = C + w_q` (lines 509--510), and the three rungs of
the direct-bridge loop.  Both halves come from the banked
`DirectOutputEqualityClose.directOutputClose` — the `cc-t1n` endpoint that
already joined them — and only the substitution `C_W + r_Q = D + H + 1` of
aux 2 is performed here. -/
theorem oneLevelBudgets_no {A B : Type*} [Fintype A] [Fintype B]
    (W : A → B → Bool) (Dsrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hB : 1 ≤ Fintype.card B)
    (hCW : D W = alignedExact Dsrc a w2 ws wq)
    (hrung : ∀ t, t ≤ 2 →
      alignedExact Dsrc a w2 ws wq + entryLevelA bout δU t
        ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
            (bracketGE (Fin (Qwidth bout δU) → B) (Fin (Qwidth bout δU) × A) 1
              (xOut bout) ((3 / 5) / 2 ^ t))) :
    D (EthBridge.Rnext W (Qwidth bout δU))
        = Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 ∧
      Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1
        ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
            ((3 : ℝ) / 5) := by
  obtain ⟨heq, hlam⟩ :=
    directOutputClose W (alignedExact Dsrc a w2 ws wq) bout hB hCW hrung
  have hcollect := noBudget_collect Dsrc a w2 ws wq (rQ bout δU)
  refine ⟨?_, ?_⟩
  · rw [heq]; exact hcollect
  · rw [← hcollect]; exact hlam

/-- **The `NO` equality alone, from the top rung only**
(`10-direct-bridge.tex:512--521`).

Line 521 names the equality; its lower half is the `t = 0` rung and nothing
more.  This is the same collection as `oneLevelBudgets_no` over the strictly
weaker premise `DirectOutputEqualityClose.directOutputEqualityClose` takes, kept
separate so a caller holding only the top rung is not asked for the other two
(the Candidate-B failure mode `cc-t1n` refuted). -/
theorem oneLevelBudget_noEquality {A B : Type*} [Fintype A] [Fintype B]
    (W : A → B → Bool) (Dsrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hB : 1 ≤ Fintype.card B)
    (hCW : D W = alignedExact Dsrc a w2 ws wq)
    (h0 : alignedExact Dsrc a w2 ws wq + entryLevelA bout δU 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → B) (Fin (Qwidth bout δU) × A) 1
            (xOut bout) ((3 : ℝ) / 5))) :
    D (EthBridge.Rnext W (Qwidth bout δU))
      = Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 := by
  have heq :=
    directOutputEqualityClose W (alignedExact Dsrc a w2 ws wq) bout hB hCW h0
  rw [heq]
  exact noBudget_collect Dsrc a w2 ws wq (rQ bout δU)

/-- **The `YES` half of the collection** (`10-direct-bridge.tex:525--534`).

"By `lem:interlace-selector-protocol`, … the direct bridge communicates its
`Q`-selector in `log₂Q` bits.  Therefore `comp R⁺ ≤ Y + H`."  The outer step
only: the premise is the already scale-aligned `YES` budget `Y + K + w_q`, and
the banked `DirectOutput.canonicalSelectorProtocol` supplies the `Q`-selector.
No lower-bound hypothesis and no robustness certificate is used, exactly as
`11-one-level-assembly.tex:805--807` records. -/
theorem oneLevelBudget_yes {A B : Type*} [Fintype A] [Fintype B]
    (W : A → B → Bool) (Ysrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hYes : D W ≤ Ysrc + stage4Overhead a w2 ws + wq) :
    D (EthBridge.Rnext W (Qwidth bout δU))
      ≤ Ysrc + levelOverhead a w2 ws wq (rQ bout δU) := by
  exact yesBudget_collect (n := Ysrc + stage4Overhead a w2 ws) (m := D W)
    le_rfl hYes (canonicalSelectorUpper_transpose W bout δU)

/-! ## Part 3: the pinned two-interlace composite

`10-direct-bridge.tex:509--510` names two interlaces — the scale-alignment
interlace *inside* the adapted Stage 4, and the direct bridge — and the reader
displays their composite at `05-iteration.tex:96--100`.  Part 3 pins that
composite and runs each promise case over the **one** matrix, which is the
promise-independence the readingwarning immediately after the table
(`10-direct-bridge.tex:565--571`) insists on: the *construction* is shared, the
*readings* are not. -/

/-- **`W = ᵀInt_q(N)` at `q = 2^{w_q}`** — the scale-alignment interlace inside
the adapted Stage 4, `09-first-wrapper.tex:1794` (`U = Int_q(N)`, `W = ᵀU`);
reader `05-iteration.tex:97`.  The vendored `EthBridge.Rnext` is exactly the
interlace-then-transpose of that line. -/
def alignedMatrix {X Y : Type*} (N : X → Y → Bool) (wq : ℕ) :
    (Fin (2 ^ wq) → Y) → (Fin (2 ^ wq) × X) → Bool :=
  EthBridge.Rnext N (2 ^ wq)

/-- **`R⁺ = ᵀInt_Q(W)` at the canonical width `Q = Qwidth b_out δ_U`** — the
direct bridge, `10-direct-bridge.tex:63`; reader `05-iteration.tex:99`.  Applied
to `alignedMatrix`, this is the composite the collected budgets are about. -/
noncomputable def levelOutput {X Y : Type*} (N : X → Y → Bool)
    (wq bout : ℕ) (δU : ℝ) :
    (Fin (Qwidth bout δU) → Fin (2 ^ wq) × X) →
      Fin (Qwidth bout δU) × (Fin (2 ^ wq) → Y) → Bool :=
  EthBridge.Rnext (alignedMatrix N wq) (Qwidth bout δU)

/-- **The pinned composite has the carriers the paper attributes to `R⁺`**
(`07-one-level-construction.tex:80--81`):
`|Rows(R⁺)| = (q m_N)^Q` and `|Cols(R⁺)| = Q n_N^q`, with `m_N = |Rows(N)|` and
`n_N = |Cols(N)|`, at `q = 2^{w_q}` and `Q = Qwidth b_out δ_U`.

This is a **pinning check**, not the carrier obligation: it certifies that the
matrix the budgets below are about is the paper's `R⁺` and not some other
double interlace.  Clause C4 of `thm:one-level` and reader
`eq:one-level-exact-carriers` stay with `ONELEVEL-001` and `SIZE-001`
(GAP-EXPOSED 3).

**The scale-alignment width carries its frozen legality guard.**
`02-mechanical-contract.tex:771--775` states the successor equations together
with the hypotheses they travel with — "because `q, Q ≥ 2` and `m_N, n_N ≥ 1`"
— and `09-first-wrapper.tex:105` fixes `q = 2^{r}`.  The binder `hq : 1 ≤ w_q`
is exactly `q = 2^{w_q} ≥ 2`.  Without it `w_q = 0`, i.e. the frozen-illegal
`q = 1`, would be an admitted instantiation of this statement; the guard is a
**lower** bound on the width and never an upper one.  Both pinned witnesses
satisfy it (`w_q = 3` and `w_q = 5`). -/
theorem pinnedOutput_carriers {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) (hq : 1 ≤ wq) :
    rowsCard (levelOutput N wq bout δU)
        = (2 ^ wq * Fintype.card X) ^ Qwidth bout δU ∧
      colsCard (levelOutput N wq bout δU)
        = Qwidth bout δU * Fintype.card Y ^ 2 ^ wq := by
  have _hq : 1 ≤ wq := hq
  constructor
  · simp [rowsCard, Fintype.card_fin]
  · simp [colsCard, Fintype.card_fin]

/-- **The frozen realized-input carrier invariant at the composed double
interlace** — `02-mechanical-contract.tex:767--775`:

> "The lower-carrier rows in (ii) are the minimal realized-input invariant, not
> a promise-case condition.  The full-cube seed has both carrier sizes at least
> two.  Moreover the exact successor equations give
> `m_next = (q m_N)^Q ≥ 2`, `n_next = Q n_N^q ≥ 2`
> because `q, Q ≥ 2` and `m_N, n_N ≥ 1`.  Hence realization preserves the
> invariant."

Reader counterpart: `05-iteration.tex:280--283`, "Both seed carriers have size
at least two.  At every successor, `q, Q ≥ 2` and `m⁺ = (q m_N)^Q`,
`n⁺ = Q n_N^q`, so this lower-carrier invariant is preserved."

The three frozen premises are the three binders `hq` (`q = 2^{w_q} ≥ 2`), `hX`
(`m_N ≥ 1`) and `hY` (`n_N ≥ 1`).  **`Q ≥ 2` is not assumed**: it is discharged
from the banked `EntryGates.four_le_rQ` (`r_Q ≥ 4`) and `Qwidth_eq_two_pow`
(`Q = 2^{r_Q}`), so no guard is imported that the route has not already proved.

This is the composed-carrier analogue of the banked single-interlace pair
`BridgeOutputEquality.bridgeCarriers_nonempty_fires` /
`bridgeCarriers_fires_nondegenerate`, and it is what makes
`pinnedOutput_carriers` a nondegeneracy statement rather than two equations
that also hold at `q = 1`.  General in both carriers, in `w_q`, `b_out` and
`δ_U`. -/
theorem pinnedOutput_carriers_invariant {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ)
    (hq : 1 ≤ wq) (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) :
    2 ≤ rowsCard (levelOutput N wq bout δU) ∧
      2 ≤ colsCard (levelOutput N wq bout δU) := by
  obtain ⟨hrow, hcol⟩ := pinnedOutput_carriers N wq bout δU hq
  have h4 : 4 ≤ rQ bout δU := four_le_rQ bout δU
  have hQpow : Qwidth bout δU = 2 ^ rQ bout δU := Qwidth_eq_two_pow bout δU
  have hQ2 : 2 ≤ Qwidth bout δU := by
    rw [hQpow]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ rQ bout δU := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2 ≤ 2 ^ wq := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ wq := Nat.pow_le_pow_right (by norm_num) hq
  refine ⟨?_, ?_⟩
  · rw [hrow]
    have hbase : 2 ≤ 2 ^ wq * Fintype.card X :=
      le_trans hq2 (Nat.le_mul_of_pos_right _ hX)
    have hstep : 2 ^ wq * Fintype.card X
        ≤ (2 ^ wq * Fintype.card X) ^ Qwidth bout δU :=
      Nat.le_self_pow (by omega) _
    omega
  · rw [hcol]
    have hpow : 1 ≤ Fintype.card Y ^ 2 ^ wq := Nat.one_le_pow _ _ hY
    have hstep : Qwidth bout δU * 1
        ≤ Qwidth bout δU * Fintype.card Y ^ 2 ^ wq :=
      Nat.mul_le_mul_left _ hpow
    omega

/-- **The inner `q`-selector on the `YES` side**
(`10-direct-bridge.tex:529--530`; `09-first-wrapper.tex:1805--1806`, "The same
outer selector adds exactly `r` bits to the `YES` protocol").

From the Stage-4 `YES` budget `comp N ≤ Y + K` of
`11-one-level-assembly.tex:793` and `lem:interlace-selector-protocol` at the
power-of-two width `q = 2^{w_q}`.  The banked
`DirectOutputEqualityClose.selectorUpper_transpose_two_pow` is consumed at an
arbitrary exponent; nothing is re-proved. -/
theorem alignedYesBudget {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Ysrc a w2 ws wq : ℕ)
    (hN : D N ≤ Ysrc + stage4Overhead a w2 ws) :
    D (alignedMatrix N wq) ≤ Ysrc + stage4Overhead a w2 ws + wq := by
  have h := selectorUpper_transpose_two_pow N wq
  unfold alignedMatrix
  omega

/-- **Headline 1 — the `NO` case of the one-level completion at the pinned
composite** (`10-direct-bridge.tex:512--521` and `:536`).

Two deliverables, both about the one matrix `R⁺`:

* the **equality** of lines 512--520, `comp R⁺ = D + H + 1`;
* the **ordinary robustness** of line 536,
  `Λ_{R⁺}(1, 2^{-b_out}, 3/5) ≥ D + H + 1`.

The premises are the `NO`-case ones only: the aligned exact identity
`comp W = C_W` of lines 509--510 and the loop's three rungs.  **`Ysrc` does not
occur anywhere in this statement**, which is what makes it consistent with the
frozen side condition `Y_i ≤ D_i` of `13-iteration-assembly.tex:431` — see
`promiseConjunction_refuted_at_step_I05` for the shape this replaces.

Row nonemptiness `1 ≤ |X|` is the explicit carrier binder the banked lower half
needs (mechanical rule M7); it is exactly what makes the composite's column
carrier `Fin q × X` nonempty. -/
theorem oneLevelCompletion_no {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hX : 1 ≤ Fintype.card X)
    (hCW : D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hrung : ∀ t, t ≤ 2 →
      alignedExact Dsrc a w2 ws wq + entryLevelA bout δU t
        ≤ Dfamily (interlaceFun (levelOutput N wq bout δU) 1)
            (bracketGE (Fin (Qwidth bout δU) → Fin (2 ^ wq) × X)
              (Fin (Qwidth bout δU) × (Fin (2 ^ wq) → Y)) 1 (xOut bout)
              ((3 / 5) / 2 ^ t))) :
    D (levelOutput N wq bout δU)
        = Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 ∧
      Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1
        ≤ LambdaGE (levelOutput N wq bout δU) 1 (xOut bout) ((3 : ℝ) / 5) := by
  have hcol : 1 ≤ Fintype.card (Fin (2 ^ wq) × X) := by
    have h2 : 1 ≤ 2 ^ wq := Nat.one_le_two_pow
    have := Nat.mul_le_mul h2 hX
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  exact oneLevelBudgets_no (alignedMatrix N wq) Dsrc a w2 ws wq bout hcol hCW
    hrung

/-- **Headline 2 — the `YES` case of the one-level completion at the pinned
composite** (`10-direct-bridge.tex:525--534`).

One deliverable, about the same matrix `R⁺`: `comp R⁺ ≤ Y + H`.  The `YES` side
descends the whole two-interlace chain from the Stage-4 budget `comp N ≤ Y + K`
of `11-one-level-assembly.tex:793`, paying `w_q` then `r_Q`.  No lower bound, no
robustness certificate, no row-nonemptiness binder and **no occurrence of
`Dsrc`** — which is why this statement, too, is consistent with `Y_i ≤ D_i`. -/
theorem oneLevelCompletion_yes {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Ysrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hYesN : D N ≤ Ysrc + stage4Overhead a w2 ws) :
    D (levelOutput N wq bout δU)
      ≤ Ysrc + levelOverhead a w2 ws wq (rQ bout δU) := by
  exact oneLevelBudget_yes (alignedMatrix N wq) Ysrc a w2 ws wq bout
    (alignedYesBudget N Ysrc a w2 ws wq hYesN)

/-- **The collected interface as a record** (`10-direct-bridge.tex:492--498`).

The four public slots of the box at the pinned composite: the truth table
`R⁺`, the exact `NO` complexity `D + H + 1`, the known `YES` protocol budget
`Y + H`, and the requested depth `b_out`.  No label, source item, donor,
reservoir or gadget coordinate is a field — nor could one be, since the record
has exactly these four.

Both public budgets are fields of the *same* record because both are computed
from the public tuple before either promise case is analysed
(`10-direct-bridge.tex:565--571`).  That is data, not a conjunction of
readings: `oneLevelSeed_readings_disjoint` shows the two readings of this very
record are never jointly satisfiable. -/
noncomputable def oneLevelSeed {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq bout : ℕ) (δU : ℝ) :
    SeedInterface (Fin (Qwidth bout δU) → Fin (2 ^ wq) × X)
      (Fin (Qwidth bout δU) × (Fin (2 ^ wq) → Y)) where
  table := levelOutput N wq bout δU
  noComplexity := Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1
  yesBudget := Ysrc + levelOverhead a w2 ws wq (rQ bout δU)
  depth := bout

/-- **The delivered `NO` value is not trivial.**

The collected complexity is at least `D + 1` and at least `r_Q + 1`, and the
banked `EntryGates.four_le_rQ` makes the latter at least `5` at every legal
parameter choice.  A collected budget delivering `0` would be free; this one is
not.  The banked
`DirectOutputLower.directOutputLower_conclusion_nontrivial` is available for the
sharper `≥ 7` reading under `C_W ≥ 3` and is not restated here. -/
theorem oneLevelCompletion_conclusion_nontrivial (Dsrc a w2 ws wq bout : ℕ)
    (δU : ℝ) :
    Dsrc + 1 ≤ Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 ∧
      5 ≤ Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 := by
  have h4 := four_le_rQ bout δU
  have hle : rQ bout δU ≤ levelOverhead a w2 ws wq (rQ bout δU) := by
    unfold levelOverhead stage4Overhead
    omega
  omega

/-- **The `NO` reading of the collected interface holds**
(`10-direct-bridge.tex:521` and `:536` through the record of lines 492--498,
with the `comp ≥ 1` clause of `def:robust-seed`).

The `YES` input is **not** a hypothesis: `noReading` is a `NO`-case statement
and asking for the `YES` budget here is precisely the inconsistency
`promiseConjunction_refuted_at_step_I05` records.  The third conjunct is
discharged from `oneLevelCompletion_conclusion_nontrivial`, so the record this
module hands the next level really is an ordinary robust seed in the sense of
`03-preliminaries.tex:243--250`. -/
theorem oneLevelSeed_noReading {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hX : 1 ≤ Fintype.card X)
    (hCW : D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hrung : ∀ t, t ≤ 2 →
      alignedExact Dsrc a w2 ws wq + entryLevelA bout δU t
        ≤ Dfamily (interlaceFun (levelOutput N wq bout δU) 1)
            (bracketGE (Fin (Qwidth bout δU) → Fin (2 ^ wq) × X)
              (Fin (Qwidth bout δU) × (Fin (2 ^ wq) → Y)) 1 (xOut bout)
              ((3 / 5) / 2 ^ t))) :
    (oneLevelSeed N Dsrc Ysrc a w2 ws wq bout δU).noReading := by
  obtain ⟨heq, hlam⟩ :=
    oneLevelCompletion_no N Dsrc a w2 ws wq bout hX hCW hrung
  have hpos : 1 ≤ Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 :=
    Nat.le_add_left 1 _
  exact ⟨heq, hlam, hpos⟩

/-- **The `YES` reading of the collected interface holds**
(`10-direct-bridge.tex:534` through the record of lines 492--498).

A separate proposition about the same record, per mechanical rule M2; its
premises are the `YES` ones only. -/
theorem oneLevelSeed_yesReading {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq bout : ℕ) {δU : ℝ}
    (hYesN : D N ≤ Ysrc + stage4Overhead a w2 ws) :
    (oneLevelSeed N Dsrc Ysrc a w2 ws wq bout δU).yesReading :=
  oneLevelBudget_yes (alignedMatrix N wq) Ysrc a w2 ws wq bout
    (alignedYesBudget N Ysrc a w2 ws wq hYesN)

/-- **The entry guard the next level requires, kept separate from robustness.**

`03-preliminaries.tex:438--444` fixes the input tuple of one level as
`(R, D, Y, b₀)` with **`D ≥ 3`**, and `13-iteration-assembly.tex:431`
(`step:I-05`) re-states `3 ≤ D_i` as a side condition at every level and every
one-level call site.  That is a condition on the *tuple*, not a clause of
`def:robust-seed`, so it is a separate lemma rather than a `noReading`
conjunct.

Unconditional: it holds for every structurally legal parameter tuple, from the
banked `EntryGates.four_le_rQ` through
`oneLevelCompletion_conclusion_nontrivial`.  The output tuple of one level is
therefore always a legal input tuple for the next as far as this guard is
concerned. -/
theorem oneLevelSeed_entryGuard {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq bout : ℕ) (δU : ℝ) :
    3 ≤ (oneLevelSeed N Dsrc Ysrc a w2 ws wq bout δU).noComplexity := by
  have h := (oneLevelCompletion_conclusion_nontrivial Dsrc a w2 ws wq bout δU).2
  simpa [oneLevelSeed] using (by omega : (3 : ℕ) ≤
    Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1)

/-- **The increment table of `10-direct-bridge.tex:543--563`, row by row.**

|                          | YES increment | NO increment |
|--------------------------|---------------|--------------|
| Stages 1--4              | `K`           | `K + 1`      |
| Stage-4 scale alignment  | `w_q`         | `w_q`        |
| direct robustification   | `w_Q`         | `w_Q`        |
| total                    | `H`           | `H + 1`      |

The four conjuncts are the four rows.  The content is that the single asymmetry
sits in the Stages 1--4 row and survives untouched to the total: the two
selector rows contribute the *same* increment to both columns, which is what
`lem:interlace-selector-protocol` gives and what makes the level step
promise-independent.  General in all five exponents. -/
theorem levelIncrementTable (a w2 ws wq wQ : ℕ) :
    stage4Overhead a w2 ws = a + w2 + ws ∧
      stage4Overhead a w2 ws + 1 = a + w2 + ws + 1 ∧
      levelOverhead a w2 ws wq wQ = stage4Overhead a w2 ws + wq + wQ ∧
      levelOverhead a w2 ws wq wQ + 1 = stage4Overhead a w2 ws + 1 + wq + wQ := by
  unfold levelOverhead stage4Overhead
  omega

/-! ## Part 4: the encoding refutation, the promise-conjunction refutation, and
the value poles -/

/-- **Candidate B collapses the promise gap.**

A flat interface that asserts the exact `NO` complexity and the `YES` budget of
the *same* matrix simultaneously forces `c_NO ≤ y_YES`.  Since the two slots are
what the box keeps apart, this is the mechanical-rule-M2 violation made
arithmetic: the record would carry both promise certificates at once. -/
theorem flatInterface_forces_gap_inversion {A B : Type*} [Fintype A] [Fintype B]
    (S : SeedInterface A B) (hno : S.noReading) (hyes : S.yesReading) :
    S.noComplexity ≤ S.yesBudget := by
  obtain ⟨heq, -⟩ := hno
  unfold SeedInterface.yesReading at hyes
  omega

/-- **…and at legal budgets that is impossible.**

With the collected values of lines 514--519 and 534, `c_NO ≤ y_YES` reads
`D + H + 1 ≤ Y + H`, i.e. `D + 1 ≤ Y`, which the frozen side condition
`Y ≤ D` of `13-iteration-assembly.tex:431` refutes at every legal level.  So
Candidate B is not merely a worse encoding: at legal parameters it is
uninhabited, and a module that landed it would compile green and prove nothing.
General in all seven numbers. -/
theorem flatInterface_refuted_at_legal_budgets {Dsrc Ysrc : ℕ}
    (a w2 ws wq wQ : ℕ) (hYD : Ysrc ≤ Dsrc) :
    ¬ (Dsrc + levelOverhead a w2 ws wq wQ + 1
        ≤ Ysrc + levelOverhead a w2 ws wq wQ) := by
  omega

/-- **The two readings are never jointly satisfiable at legal budgets.**

The record-level form of the previous lemma: at the collected values and under
the frozen `Y ≤ D`, no interface satisfies both the `NO` and the `YES` reading.
This is what makes the promise split real rather than decorative — a record
admitting both would be the degenerate one. -/
theorem oneLevelSeed_readings_disjoint {A B : Type*} [Fintype A] [Fintype B]
    (S : SeedInterface A B) (hgap : S.yesBudget < S.noComplexity) :
    ¬ (S.noReading ∧ S.yesReading) := by
  rintro ⟨hno, hyes⟩
  have := flatInterface_forces_gap_inversion S hno hyes
  omega

/-- **The theorem-level form of the same error: conjoining the two promise
inputs inverts the gap.**

Take the `NO` input `comp W = C_W = C + w_q` of lines 509--510 and the `YES`
input `comp N ≤ Y + K` of lines 525--527 **on the same source matrix**.  The
inner selector bound (`alignedYesBudget`, i.e.
`lem:interlace-selector-protocol` at the width `q = 2^{w_q}`) turns the second
into `comp W ≤ Y + K + w_q`; comparing with the first gives

```
Dsrc + K + 1 + wq  ≤  Ysrc + K + wq,     i.e.     Dsrc < Ysrc.
```

So the conjoined hypothesis bundle *derives* the strict inversion of the
promise gap.  Nothing about the paper is wrong here: the paper never conjoins
them.  General in every parameter. -/
theorem promiseConjunction_forces_gap_inversion {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq : ℕ)
    (hCW : D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hYesN : D N ≤ Ysrc + stage4Overhead a w2 ws) : Dsrc < Ysrc := by
  have h := alignedYesBudget N Ysrc a w2 ws wq hYesN
  rw [hCW] at h
  unfold alignedExact stage4Exact at h
  omega

/-- **…and `step:I-05` forbids it, so the conjoined form is vacuous.**

`13-iteration-assembly.tex:430--432` (`step:I-05`) fixes `Y_i ≤ D_i` at every
level "including every one-level call site".  Together with the previous lemma,
a theorem taking both promise inputs at once has premises satisfiable at **no**
legal parameter value: it is a statement about the empty parameter set, and a
green build of it certifies nothing.

This is the shape the first round of this tranche took and the reason the
module now carries `oneLevelCompletion_no` and `oneLevelCompletion_yes`
separately.  Recorded in the kernel so it cannot return unnoticed. -/
theorem promiseConjunction_refuted_at_step_I05 {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq : ℕ)
    (hYD : Ysrc ≤ Dsrc)
    (hCW : D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hYesN : D N ≤ Ysrc + stage4Overhead a w2 ws) : False := by
  have h := promiseConjunction_forces_gap_inversion N Dsrc Ysrc a w2 ws wq hCW
    hYesN
  omega

/-! ## Part 5: non-vacuity

LANE-GATE 3 and LANE-GATE 4b/4c.  Each item excludes one degeneracy a green
build cannot see.  The parameter tuples are *structurally legal* in the sense of
GAP-EXPOSED 5; the two record inhabitants are *realizability* witnesses in the
sense of GAP-EXPOSED 6. -/

/-- **Why a two-element carrier cannot carry a route-legal `noComplexity`.**

Aux 11b bounds `comp` by `2` for every table on `Bool × Bool`, so the
exact-complexity conjunct of `noReading` is **refutable** — not merely
unproved — at any record over that carrier whose `noComplexity` reaches the
entry guard `3 ≤ D` of `03-preliminaries.tex:442`.  A "non-degeneracy witness"
pinned there would prove nothing: its `¬ (noReading ∧ yesReading)` conclusion
would hold because one side is unsatisfiable, not because the budgets are
separated.

General in the record.  It is the reason the two inhabitants below pin
`noComplexity` at `1` and `2`, and the reason the route-legal values are
carried instead by `oneLevelSeed_fields_first_witness`. -/
theorem noReading_refuted_at_bool_carrier (S : SeedInterface Bool Bool)
    (h : 3 ≤ S.noComplexity) : ¬ S.noReading := by
  rintro ⟨heq, -, -⟩
  have hle := D_bool_le_two S.table
  omega

/-- **Non-vacuity witness 1: a realizable `NO`-side inhabitant of
`SeedInterface`.**

The record `⟨(x, y) ↦ x, 1, 0, 0⟩` over `Bool` carriers.  Every claim about it
is *proved*, not assumed:

* `S.noReading` — **all three** conjuncts of `def:robust-seed`
  (`03-preliminaries.tex:244--250`) hold at this record, the middle one by
  `aliceBit_lambda`.  Round `r1` established only two of the three and therefore
  inhabited nothing; the statement gate's exact prescription was to restore the
  `Λ₃` conjunct here, and this is it.  The budget is `1`, i.e. **below** the
  frozen entry floor `D ≥ 3`; the legal-budget inhabitant is
  `fullCubeSeed_realizes_noReading` below, and
  `noReading_refuted_at_bool_carrier` proves no record over this two-element
  carrier could ever reach a legal budget;
* `D S.table = S.noComplexity` — the exact-complexity slot is **realized** by
  the carrier (aux 12b), so the first conjunct of `noReading` holds here and is
  not cardinality-refutable, which is exactly what the previous round's `32` on
  this carrier failed;
* `1 ≤ S.noComplexity` — the `comp ≥ 1` guard of `def:robust-seed`
  (`03-preliminaries.tex:244`) is met, and **tightly**, so it is not a
  decoration;
* `S.yesBudget < S.noComplexity` — the strict one-bit gap of the increment
  table;
* `¬ S.yesReading` — the `YES` reading genuinely **fails** here, by the value of
  `comp`, not by a cardinality accident.

**Why the trivial witness fails.**  The zero record `⟨fun _ _ => false, 0, 0,
0⟩` — the witness a vacuous `∃` would accept — fails the very first conjunct
(`table = (x, y) ↦ x` is false for it), and it also fails
`yesBudget < noComplexity`, which `0 < 0` refutes, and the guard `1 ≤ 0`.  The
statement pins one record and asserts properties of it; it is not "some
interface exists".

This is a *field-shape realizability* witness (GAP-EXPOSED 6), not a route
instance: the route's own values are carried by
`oneLevelSeed_fields_first_witness`. -/
theorem seedInterface_realizable_no :
    ∃ S : SeedInterface Bool Bool,
      S.table = (fun x _ => x) ∧ S.depth = 0 ∧
        S.noComplexity = 1 ∧ S.yesBudget = 0 ∧
        S.noReading ∧
        D S.table = S.noComplexity ∧ 1 ≤ S.noComplexity ∧
        S.yesBudget < S.noComplexity ∧ ¬ S.yesReading := by
  refine ⟨⟨fun x _ => x, 1, 0, 0⟩, rfl, rfl, rfl, rfl,
    ⟨D_aliceBit, aliceBit_lambda, le_rfl⟩, D_aliceBit, le_rfl, by norm_num, ?_⟩
  intro hyes
  have h : D (fun x _ : Bool => x) ≤ 0 := hyes
  rw [D_aliceBit] at h
  omega

/-- **Non-vacuity witness 2: a realizable `YES`-side inhabitant of
`SeedInterface`.**

The same table at `⟨(x, y) ↦ x, 2, 1, 0⟩`.  Now the other reading is the one
that holds:

* `S.yesReading` — **proved**, since `comp` of the table is `1 ≤ 1`;
* `¬ S.noReading` — fails on its exact-complexity conjunct, `1 ≠ 2`, again by a
  computed value rather than a carrier accident;
* `S.yesBudget < S.noComplexity` — the strict gap is still there.

Witnesses 1 and 2 together show that **both** readings of the record are
individually satisfiable at realizable values, so `oneLevelSeed_readings_disjoint`
is a genuine separation and not a statement about an always-empty side.  The
trivial witness fails witness 2 for the same reasons as witness 1. -/
theorem seedInterface_realizable_yes :
    ∃ S : SeedInterface Bool Bool,
      S.table = (fun x _ => x) ∧ S.depth = 0 ∧
        S.noComplexity = 2 ∧ S.yesBudget = 1 ∧
        S.yesReading ∧ ¬ S.noReading ∧ S.yesBudget < S.noComplexity := by
  refine ⟨⟨fun x _ => x, 2, 1, 0⟩, rfl, rfl, rfl, rfl, ?_, ?_, by norm_num⟩
  · change D (fun x _ : Bool => x) ≤ 1
    rw [D_aliceBit]
  · rintro ⟨heq, -, -⟩
    have h : D (fun x _ : Bool => x) = 2 := heq
    rw [D_aliceBit] at h
    omega

/-- **Non-vacuity witness 2b: a `noReading` inhabitant at a *legal* budget,
built from the paper's own seed matrix.**

Witness 1 inhabits `SeedInterface.noReading` but at `noComplexity = 1`, below
the frozen entry floor `D ≥ 3` (`03-preliminaries.tex:442`,
`13-iteration-assembly.tex:431`), and `noReading_refuted_at_bool_carrier` shows
the two-element carrier admits nothing better.  This witness closes that gap
with the frozen full-cube matrix `eq:full-cube-seed`
(`12-iteration-specification.tex:23--30`) at the numerals obtained by
**evaluating** the frozen minimality rule at `b = 0`
(`fullCubeSeed_parameters`: `a_seed = 7`, `q_seed = 2^7 - 2 = 126`) — a value of
`b` *outside* the range `b ≥ 1` that rule is stated for, as the range
disclosure on `fullCubeSeed_parameters` records:

* `S.table = fullCube 126` — the frozen `F_b(γ, j) = γ(j)` on
  `{0,1}^{126} × [126]`, no re-carriering;
* `S.noComplexity = 8 = a_seed + 1` — proved, not posited
  (`fullCubeSeed_D`), so the first conjunct of `noReading` is an equality
  between two computed values;
* `S.noReading` — all three conjuncts, the middle one by `fullCubeSeed_lambda`,
  which has the shape of the second display of `lem:full-cube-seed` evaluated
  at `b = 0` but is not an instance of it (that lemma fixes `b ≥ 1`);
* `3 ≤ S.noComplexity` — the frozen entry floor is met, and in fact
  `8 = a_seed + 1 ≥ 4` is exactly the seed value `D_0 = a_seed + 1` of
  `step:I-05` (`13-iteration-assembly.tex:433--436`);
* `S.yesBudget = S.noComplexity` — also frozen: `step:I-05` fixes
  `D_0 = Y_0 = a_seed + 1` at the seed, so **both** readings hold here, and no
  strict gap is claimed.  That is consistent with
  `oneLevelSeed_readings_disjoint`, whose hypothesis is the strict gap
  `Y < D`; the gap opens only at the level *output*, where the budgets are
  `D + H + 1` and `Y + H`.

**Why the trivial witness fails.**  The zero record `⟨fun _ _ => false, 0, 0, 0⟩`
fails `S.table = fullCube 126`, fails `3 ≤ 0`, and fails the first `noReading`
conjunct because `D (fun _ _ => false) = 0 ≠ 8`.  More sharply: *no* record over
this carrier other than one with `noComplexity = 8` can satisfy `noReading` at
all, because `fullCubeSeed_D` computes the left-hand side of the first conjunct.
The existential pins one record and asserts computed properties of it.

**What this does not claim (recorded for `SEED-001`).**  The whole of
`sec:full-cube-seed` opens at `12-iteration-specification.tex:16` with "Fix a
requested depth `b ≥ 1`", so **every** statement in that subsection — the
minimality rule, `eq:full-cube-seed` as an indexed family, and
`lem:full-cube-seed` itself — is scoped to `b ≥ 1`, and `b = 0` lies outside it.
This record is therefore **not** an instance of the paper's seed at a requested
depth, and no consumer may cite it as one.  Two things make it nevertheless a
faithful inhabitant of the target predicate: `SeedInterface.noReading` traces
`def:robust-seed` (`03-preliminaries.tex:243--250`), which imposes no lower
bound on `b`; and both computed inputs are depth-free or evaluated at
`xOut 0 = 1` — `fullCubeSeed_D` is a statement about the matrix alone, and
`fullCubeSeed_lambda` is `Λ₃` at row density `1`.

What is *not* landed is the parametric lemma.  At `b ≥ 1` the frozen proof
additionally needs the row-density leg
(`12-iteration-specification.tex:60--64`: a retained row set of density
`2^{-b}` spans a subspace of dimension at least `q_seed - b`, whence restricted
rank at least `|J| - b`).  **That leg is not formalized here.**  At `b = 0` the
row condition forces the full row set (`bracket_row_univ`), the `-b` correction
vanishes, and the identity submatrix of
`12-iteration-specification.tex:47--48` survives intact — which is exactly why
this instance is reachable and the parametric lemma is not.  At the paper's own
first legal depth `b = 1` the minimality rule selects `a_seed = 8`,
`q_seed = 254`, not the numerals used here.  The reader's `def:paper-robust`
(`02-preliminaries.tex:93--100`, label line 93) likewise fixes `b ≥ 1` and
`D ≥ 2`, so this record is an instance of the autoformalization definition
only. -/
theorem fullCubeSeed_realizes_noReading :
    ∃ S : SeedInterface (Fin 126 → Bool) (Fin 126),
      S.table = fullCube 126 ∧ S.depth = 0 ∧
        S.noComplexity = 8 ∧ S.yesBudget = 8 ∧
        S.noReading ∧ S.yesReading ∧
        3 ≤ S.noComplexity ∧ S.yesBudget ≤ S.noComplexity := by
  refine ⟨⟨fullCube 126, 8, 8, 0⟩, rfl, rfl, rfl, rfl,
    ⟨fullCubeSeed_D, ?_, by norm_num⟩, ?_, by norm_num, by norm_num⟩
  · exact fullCubeSeed_lambda
  · change D (fullCube 126) ≤ 8
    rw [fullCubeSeed_D]

/-- **Non-vacuity witness 3: the `NO` collection fires at the banked first
entry-gate witness.**

`b_out = 1`, `δ_U = 1/60`, where the banked entry apparatus reads `r_Q = 13` and
`Q = 8192`; the widths `a = 4`, `w₂ = 6` (so `q₂ = 64 ≥ 16`), `w_s = 1` (so
`s = 2`), `w_q = 3` (so `q = 8`); and the frozen seed budget `D = 4` of
`13-iteration-assembly.tex:435`.

Then `K = 11`, `H = 27`, the collected `NO` complexity is `32`, and both
selector costs are the exact `⌈log₂⌉` values M8 requires.  No `YES` quantity
occurs, so the hypothesis context of this proof is consistent and the closing
`omega` calls are genuine arithmetic rather than an explosion.

Only the numeric binders are discharged by computation: `X`, `Y`, `N`, the
aligned exact identity and the rung premise stay universally quantified, since
the bridge's input matrix has no exhibited inhabitant in Lean and can have none
until Stages 1--4 land. -/
theorem oneLevelCompletion_no_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X)
    (hCW : D (alignedMatrix N 3) = alignedExact 4 4 6 1 3)
    (hrung : ∀ t, t ≤ 2 →
      alignedExact 4 4 6 1 3 + entryLevelA 1 (1 / 60) t
        ≤ Dfamily (interlaceFun (levelOutput N 3 1 (1 / 60)) 1)
            (bracketGE (Fin (Qwidth 1 (1 / 60)) → Fin (2 ^ 3) × X)
              (Fin (Qwidth 1 (1 / 60)) × (Fin (2 ^ 3) → Y)) 1 (xOut 1)
              ((3 / 5) / 2 ^ t))) :
    rQ 1 (1 / 60) = 13 ∧ Qwidth 1 (1 / 60) = 8192 ∧
      stage4Overhead 4 6 1 = 11 ∧
      levelOverhead 4 6 1 3 (rQ 1 (1 / 60)) = 27 ∧
      alignedExact 4 4 6 1 3 = 19 ∧
      Nat.clog 2 (Qwidth 1 (1 / 60)) = 13 ∧ Nat.clog 2 (2 ^ 3) = 3 ∧
      D (levelOutput N 3 1 (1 / 60)) = 32 ∧
      32 ≤ LambdaGE (levelOutput N 3 1 (1 / 60)) 1 (xOut 1) ((3 : ℝ) / 5) := by
  obtain ⟨-, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  obtain ⟨heq, hlam⟩ :=
    oneLevelCompletion_no N 4 4 6 1 3 1 (δU := 1 / 60) hX hCW hrung
  have hK : stage4Overhead 4 6 1 = 11 := by unfold stage4Overhead; norm_num
  have hH : levelOverhead 4 6 1 3 (rQ 1 (1 / 60)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  have hCWval : alignedExact 4 4 6 1 3 = 19 := by
    unfold alignedExact stage4Exact stage4Overhead; norm_num
  rw [hH] at heq hlam
  refine ⟨hrQ, hQ, hK, hH, hCWval, ?_, alignedSelectorCost_exact 3, by omega,
    by omega⟩
  rw [← hrQ]
  exact canonicalSelectorBits 1 (1 / 60 : ℝ)

/-- **Non-vacuity witness 4: the `YES` collection fires at the same widths.**

The `YES` half of the first witness, at the frozen seed budget `Y = 4`.  The
collected `YES` budget is `Y + H = 4 + 27 = 31`, and the conclusion is stated at
that value — **`≤ 31`, the frozen number of line 534**, not `≤ 32`.  Weakening
it by one bit would make it numerically indistinguishable from the `NO` value
and would hide exactly the defect this round repairs.

No `NO` quantity occurs: neither `Dsrc`, nor the aligned exact identity, nor the
rung premise, nor the row-nonemptiness binder. -/
theorem oneLevelCompletion_yes_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool)
    (hYesN : D N ≤ 4 + stage4Overhead 4 6 1) :
    rQ 1 (1 / 60) = 13 ∧ stage4Overhead 4 6 1 = 11 ∧
      levelOverhead 4 6 1 3 (rQ 1 (1 / 60)) = 27 ∧
      Nat.clog 2 (2 ^ 3) = 3 ∧
      D (levelOutput N 3 1 (1 / 60)) ≤ 31 := by
  obtain ⟨-, -, hrQ, -, -, -, -⟩ := directEntryGates_fires
  have hK : stage4Overhead 4 6 1 = 11 := by unfold stage4Overhead; norm_num
  have hH : levelOverhead 4 6 1 3 (rQ 1 (1 / 60)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  have hyes :=
    oneLevelCompletion_yes N 4 4 6 1 3 1 (δU := 1 / 60) hYesN
  rw [hH] at hyes
  exact ⟨hrQ, hK, hH, alignedSelectorCost_exact 3, by omega⟩

/-- **Non-vacuity witness 5: the `NO` collection fires again at a different
arithmetic.**

`b_out = 1`, `δ_U = 1/200`, where the banked apparatus reads `r_Q = 14` and
`Q = 16384`; the inner width moves too, `w_q = 5` (so `q = 32`).  Now `H = 30`
and the collected `NO` complexity is `35`.

Both interlace widths, the overhead and the delivered constant change, which a
statement satisfiable at only one numeral could not do. -/
theorem oneLevelCompletion_no_fires_second_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X)
    (hCW : D (alignedMatrix N 5) = alignedExact 4 4 6 1 5)
    (hrung : ∀ t, t ≤ 2 →
      alignedExact 4 4 6 1 5 + entryLevelA 1 (1 / 200) t
        ≤ Dfamily (interlaceFun (levelOutput N 5 1 (1 / 200)) 1)
            (bracketGE (Fin (Qwidth 1 (1 / 200)) → Fin (2 ^ 5) × X)
              (Fin (Qwidth 1 (1 / 200)) × (Fin (2 ^ 5) → Y)) 1 (xOut 1)
              ((3 / 5) / 2 ^ t))) :
    rQ 1 (1 / 200) = 14 ∧ Qwidth 1 (1 / 200) = 16384 ∧
      levelOverhead 4 6 1 5 (rQ 1 (1 / 200)) = 30 ∧
      Nat.clog 2 (2 ^ 5) = 5 ∧
      D (levelOutput N 5 1 (1 / 200)) = 35 ∧
      35 ≤ LambdaGE (levelOutput N 5 1 (1 / 200)) 1 (xOut 1) ((3 : ℝ) / 5) := by
  obtain ⟨-, hrQ, hQ, -, -, -, -⟩ := directOutput_fires_second_witness
  obtain ⟨heq, hlam⟩ :=
    oneLevelCompletion_no N 4 4 6 1 5 1 (δU := 1 / 200) hX hCW hrung
  have hH : levelOverhead 4 6 1 5 (rQ 1 (1 / 200)) = 30 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  rw [hH] at heq hlam
  exact ⟨hrQ, hQ, hH, alignedSelectorCost_exact 5, by omega, by omega⟩

/-- **Non-vacuity witness 6: the `YES` collection fires again at the second
arithmetic.**

At `Y = 4` and `H = 30` the collected `YES` budget is `34`, one bit below the
`NO` value `35` of witness 5.  The one-bit gap is the one thing that does
**not** move between the two witnesses — as the table at lines 543--563
requires — and it is visible only because the two sides are stated in separate
theorems at their own frozen values. -/
theorem oneLevelCompletion_yes_fires_second_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool)
    (hYesN : D N ≤ 4 + stage4Overhead 4 6 1) :
    rQ 1 (1 / 200) = 14 ∧
      levelOverhead 4 6 1 5 (rQ 1 (1 / 200)) = 30 ∧
      Nat.clog 2 (2 ^ 5) = 5 ∧
      D (levelOutput N 5 1 (1 / 200)) ≤ 34 := by
  obtain ⟨-, hrQ, -, -, -, -, -⟩ := directOutput_fires_second_witness
  have hH : levelOverhead 4 6 1 5 (rQ 1 (1 / 200)) = 30 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  have hyes :=
    oneLevelCompletion_yes N 4 4 6 1 5 1 (δU := 1 / 200) hYesN
  rw [hH] at hyes
  exact ⟨hrQ, hH, alignedSelectorCost_exact 5, by omega⟩

/-- **Non-vacuity witness 7: the collected interface's four slots at legal
values, with `X`, `Y` and `N` universally quantified.**

The record of `oneLevelSeed` at the first witness's parameters: the depth is the
requested `b_out = 1`, the `NO` slot is `32`, the `YES` slot is `31`, the gap is
strict, and the table is the pinned composite and nothing else.  So the record
introduced in Part 0 is inhabited at **route-legal** parameter values by the
route's own construction, not only by the hand-built `Bool`-carrier
realizability witnesses — and this statement is unconditional, so it depends on
no promise hypothesis at all. -/
theorem oneLevelSeed_fields_first_witness {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) :
    (oneLevelSeed N 4 4 4 6 1 3 1 (1 / 60 : ℝ)).depth = 1 ∧
      (oneLevelSeed N 4 4 4 6 1 3 1 (1 / 60 : ℝ)).noComplexity = 32 ∧
      (oneLevelSeed N 4 4 4 6 1 3 1 (1 / 60 : ℝ)).yesBudget = 31 ∧
      (oneLevelSeed N 4 4 4 6 1 3 1 (1 / 60 : ℝ)).table
        = levelOutput N 3 1 (1 / 60) ∧
      (oneLevelSeed N 4 4 4 6 1 3 1 (1 / 60 : ℝ)).yesBudget
        < (oneLevelSeed N 4 4 4 6 1 3 1 (1 / 60 : ℝ)).noComplexity := by
  obtain ⟨-, -, hrQ, -, -, -, -⟩ := directEntryGates_fires
  have hH : levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩ <;>
    · simp only [oneLevelSeed, hH]
      try omega

/-- **Non-vacuity witness 8: the pinned composite's carriers at the first
witness.**

At `q = 2^3 = 8` and `Q = 8192`, the row carrier has `(q m_N)^Q` elements and the
column carrier `Q · n_N^q` — the paper's two carrier equations at those widths.
`X` and `Y` stay universally quantified, so this is a statement about the shape
of the composite, not about a pinned cardinality.  Both widths are reported in
their power-of-two spelling (`Qwidth 1 (1/60) = 8192` as a separate conjunct,
`q` as `2 ^ 3`) rather than substituted into the carriers, whose *types* depend
on them. -/
theorem pinnedOutput_carriers_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) :
    Qwidth 1 (1 / 60 : ℝ) = 8192 ∧
      rowsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        = (2 ^ 3 * Fintype.card X) ^ Qwidth 1 (1 / 60 : ℝ) ∧
      colsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        = Qwidth 1 (1 / 60 : ℝ) * Fintype.card Y ^ 2 ^ 3 := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  obtain ⟨hrow, hcol⟩ := pinnedOutput_carriers N 3 1 (1 / 60 : ℝ) (by norm_num)
  exact ⟨hQ, hrow, hcol⟩

end EthInapproximability.ParameterizedNP.OneLevelCompletion
