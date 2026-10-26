import EthInapproximability.ParameterizedNP.BridgeOutputEquality
import EthInapproximability.ParameterizedNP.EntryAssembly

/-!
# Parameterized NP route: the line-488 close of the direct-output equality

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-EQCLOSE-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1n` tranche for the closing sentence of the proof of
`thm:direct-robustification`, `10-direct-bridge.tex:488--490`:

> "The `t = 0` case gives `comp(R⁺) ≥ C_W + r_Q`, while
> `\Cref{lem:interlace-selector-protocol}` gives the matching upper bound.
> This proves `eq:direct-output`."

That one sentence is the whole content of this module.  It is the paper's own
close, and it is traced exactly: the lower half is read off the **`t = 0` rung
of the loop** — which is what the frozen sentence names — and the upper half is
`lem:interlace-selector-protocol`, at the canonical width, in the `R⁺`
orientation.

This **retires the banked `EntryAssembly.entryComplexityDescent` endpoint.**
`BRIDGE-ASSEMBLY-001` landed line 488's *lower half* as an endpoint with no
consumer and recorded, in its GAP-EXPOSED 4, that
"`lem:interlace-selector-protocol` is not invoked: line 488's matching upper
bound belongs to `BRIDGE-OUTPUT-001`".  Here the two halves are joined, so that
endpoint stops being an open end of the route: it is consumed, unchanged and
never re-proved, by `directOutputEqualityClose` below.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`,
and (unless stated otherwise) to `sections/10-direct-bridge.tex`.

* **lines 488--490**, the close itself — the whole of this module.  Both halves
  of that sentence and its consequence "This proves `eq:direct-output`".
* `thm:direct-robustification` (label line 35, statement lines 34--75):
  * line 40, "let `W` satisfy `comp W = C_W ≥ 3`" — the **first** conjunct is
    the explicit binder `hCWeq` every close below carries; it is exactly the
    binder `BRIDGE-OUTPUT-003` added, consumed here in the same spelling;
  * line 51, `Q = 2^{r_Q}` the least power of two at least `Q_0` — the banked
    `EntryGates.Qwidth`, `.rQ`, consumed and never redefined;
  * line 63, `R⁺ = Int_Q(W)^T` — the vendored `EthBridge.Rnext`, the matrix
    both halves of line 488 are about;
  * `eq:direct-output` (label line 71, display lines 66--72), **first
    equation** `comp R⁺ = C_W + r_Q`, which line 490 says this sentence proves;
  * lines 73--74, the selector sentence, banked as
    `BRIDGE-OUTPUT-001`'s `DirectOutput.canonicalSelectorUpper_transpose` and
    `.canonicalSelectorBits`, consumed.
* `sec:direct-entry` (label line 390), lines 421--426 (the level schedule
  `a_t = r_Q - t`, whose top value `a_0 = r_Q` is the banked
  `DirectOutputLower.entryLevelA_zero`) and lines 452--455 (the rung family
  `B(R⁺; 1, x_out, y/2^t)`, whose `t = 0` member is the premise of the close).
* `sections/03-preliminaries.tex`, `lem:interlace-selector-protocol` (label
  line 149, `eq:interlace-selector-upper` label line 154, and the sentence at
  lines 156--157, "if `p = 2^w`, the displayed protocol uses exactly `w`
  selector bits before running a protocol for `M`") — the frozen source of the
  matching upper bound of line 488.  It is the checked interface
  `powerOfTwoInterlace_upper`, consumed through `BRIDGE-OUTPUT-001`.
* `sections/03-preliminaries.tex`, `def:lambda` (label line 224, unfolding at
  lines 234--240) — the three-rung readout, used **only** to justify why the
  close does *not* take `Λ` as its input; see Choice 1 below.
* `conv:finite-slots` (`sections/03-preliminaries.tex`) — zero-based finite
  slots; the coordinate carriers are `Fin (Qwidth b_out δ_U)`, exactly as in
  `EntryAssembly.lean` and `DirectOutputLower.lean`.

## Reader counterpart

The reader artifact of the same frozen release,
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/reader-facing`,
was opened first-hand before this section was written, and each candidate item
was read to check what it states.

**No reader item is claimed by this module**, and that is deliberate: every
labelled reader item that states any part of the closed equality is already
assigned to another declaration, and assigning one twice is forbidden.

* `sections/04-bridge.tex`, `eq:bridge-output` (label line 110, display lines
  106--111), **first equation** `comp R^+ = C_W + r_Q`, is already assigned to
  `BridgeOutputEquality.directOutputEquality` by `BRIDGE-OUTPUT-003`, and its
  **second** equation to `DirectOutputLower.directOutputLower` by
  `BRIDGE-OUTPUT-002`.  Neither is reassigned here.
* `04-bridge.tex` lines 112--113, "If `W` has a protocol of cost at most `U`,
  then `R^+` has a protocol of cost at most `U + r_Q`", is already assigned to
  `DirectOutput.canonicalSelectorProtocol` by `BRIDGE-OUTPUT-001`.  It is
  *consumed* here, never restated.
* The reader's own account of this very sentence — `04-bridge.tex` lines
  147--150, "The top rung lower-bounds the whole matrix.  Conversely, the
  player holding the selector sends its `r_Q` bits and the parties run a
  protocol for `W^T`, proving equality and the YES upper bound." — is **proof
  prose inside a proof environment**, which `BRIDGE-OUTPUT-002`,
  `BRIDGE-ASSEMBLY-001` and `BRIDGE-DICHOTOMY-001` all recorded as prose that
  is not cited as a statement.  The same discipline applies here: lines
  147--150 are named as the reader's navigation locus for what this module
  proves, and are **not** claimed as a reader counterpart.  The parallel
  appendix prose, `B-bridge-details.tex` lines 233--237 ("This proves all three
  output rungs. ...  The selector protocol and the carrier calculation are
  those in `thm:near-to-robust`."), is likewise navigation only.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge" (the row that
already carries `INHERIT-001`, `BRIDGE-COPYREST-001`, `BRIDGE-OUTPUT-002`,
`BRIDGE-DISCHARGE-001`, `BRIDGE-ASSEMBLY-001` and `BRIDGE-DICHOTOMY-001`).

## Dependencies, imports, external adapters

* Imports: `BridgeOutputEquality.lean` and `EntryAssembly.lean` only, hence
  transitively `DefectDischarge`, `CopyRestriction`, `DirectOutputLower`,
  `DirectOutput`, `EntryGates`, `ThreeCopyRowStep`, `TwoCopyLadder`,
  `DefectInduction`, `InheritedContracts`, `PilotStage3` and
  `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom is not in this
  module's closure, and there is no contact with `EXPANDER-001` (which by
  design has no Lean declaration and remains an explicit named hypothesis
  wherever it is needed).
* Consumed, never edited, widened or re-proved:
  * `EntryAssembly.entryComplexityDescent` (`BRIDGE-ASSEMBLY-001`), line 488's
    lower half from the `t = 0` rung — the endpoint this module retires;
  * `EntryAssembly.entryDescent` and `.entryRungFamily_nonempty`, the loop and
    its family inhabitation;
  * `DirectOutput.selectorUpper_two_pow`,
    `.canonicalSelectorUpper_transpose`, `.canonicalSelectorBits`,
    `.canonicalSelectorProtocol` (`BRIDGE-OUTPUT-001`), the upper half of line
    488 and the two frozen readings of the selector cost;
  * `DirectOutputLower.entryLevelA`, `.entryLevelA_zero`, `.xOut`,
    `.directOutputRung`, `.directOutputLower_conclusion_nontrivial`
    (`BRIDGE-OUTPUT-002`);
  * `TwoCopyLadder.le_LambdaGE_iff` (`BRIDGE-TWOCOPY-001`), the unfolding of
    `def:lambda` used only in the direction "`Λ` bound gives the top rung";
  * `BridgeOutputEquality.directOutput_needs_exact_complexity` and
    `.theta_le_one_of_entryGate` (`BRIDGE-OUTPUT-003`);
  * `EntryGates.rQ`, `.Qwidth`, `.Q0`, `.deltaFixed`, `.lambdaU`,
    `.four_le_rQ`, `.Q0_eq_route`, `.secondEntryGate_of_deltaU_small`,
    `.directEntryGates_fires` (`BRIDGE-ENTRY-001`).
* External theorem adapters: **none new**.  Two vendored names appear, both
  already inside the route's closure: `EthBridge.Rnext`
  (`vendor/npc-cc/EthBridge/Entry.lean:181`), the `R⁺` orientation of line 63,
  which is plumbing rather than mathematics, and `NPCC.comp_transpose`, the
  frozen "transposition costs nothing" of `03-preliminaries.tex:100`, which
  `BRIDGE-OUTPUT-001` already consumes.  Nothing here is axiomatized.
* Proof status: **new (elementary)** throughout — every deliverable is
  `le_antisymm` in `ℕ` (discharged by `omega`) over banked, already
  kernel-checked route facades.  No definition is introduced, and no banked
  declaration is edited or re-proved.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings (k = 2) and the ranking

The genuinely open choice is **what the close takes as its lower input**.  Line
488 names one specific object — "the `t = 0` case" — and there are two ways to
read that in a route that has both the rung and the assembled `Λ` banked.

**Candidate A (landed) — the `t = 0` rung is the premise.**  The close takes
the top rung of the loop, `C_W + a_0 ≤ comp⟨R⁺, 1, x_out, y⟩`, as an explicit
binder, together with the line-40 binder `comp W = C_W`, and delivers the
equality.  This is line 488 read literally: `a_0 = r_Q` is the banked
`entryLevelA_zero`, and the premise is exactly the object the frozen sentence
names.

**Candidate B (rejected as the encoding of line 488) — the three-rung readout
is the premise.**  Take `Λ_{R⁺}(1, x_out, y) ≥ C_W + r_Q`, the conclusion of
lines 483--487, as the lower input.  By `def:lambda` (`03-preliminaries.tex`
lines 234--240) `Λ` is a **minimum over three rungs**, so B's premise
additionally demands the `t = 1` and `t = 2` rungs, which line 488 never
mentions.  A caller holding only the top rung — all that frozen line 488
supposes — cannot invoke B.  That is the "structure demanding more than the
paper" failure mode, and it is refuted in Lean rather than in prose by
`closeInput_candidateB_demands_more`, in the exact arithmetic shape
`le_LambdaGE_iff` gives the three rungs.

Aux battery: A = 6/6, B = 5/6 (B fails aux 4's round trip *in the direction it
needs*: `Λ` gives the top rung, but the top rung does not give `Λ`).
Faithfulness: A is the frozen sentence, B is a strictly stronger premise.
Length: A is shorter at every use site, since `entryComplexityDescent` already
takes the rung.

**A is landed.**  B survives only as the derived caller-side convenience
`directOutputEquality_ofLambdaGE`, which is *implied by* A through aux 4 and is
offered for callers who happen to hold the assembled `Λ` — it is a corollary,
never the statement of line 488.

## Aux-lemma battery (6, all general, all proved)

None is about a pinned instance; each quantifies over an arbitrary matrix,
width, or parameter tuple.

1. `natClose_of_bounds` — **the arithmetic engine of line 488**: from
   `n ≤ d + r`, `c + r ≤ n` and `d = c` conclude `n = c + r`.  General in all
   four numbers.  Identity property.
2. `selectorUpper_transpose_two_pow` — **the upper half at an arbitrary
   power-of-two width**, in the `R⁺` orientation:
   `comp(Int_{2^w}(W)^T) ≤ comp W + w`.  Round trip to
   `lem:interlace-selector-protocol` through the banked
   `selectorUpper_two_pow` and `NPCC.comp_transpose`.
3. `selectorUpper_transpose_of_exact` — the same after the line-40 rewrite:
   `comp W = C_W` gives `comp(Int_{2^w}(W)^T) ≤ C_W + w`.  Identity property,
   and the exact shape the close consumes.
4. `topRung_of_LambdaGE` — **`Λ` gives the top rung**, fully general in the
   game, copy count, both density parameters and the target.  This is the one
   direction of `def:lambda` that Candidate B would need, and it is what makes
   B a corollary of A rather than an alternative to it.
5. `topRungFamily_nonempty` — **inhabitation with the hardest field**: the
   bracket family the close's premise quantifies over is nonempty at the
   globally fixed `y = 3/5`, so `Dfamily`'s `sInf` is not the empty-family `0`
   and the premise is not free.  Consumes the banked
   `EntryAssembly.entryRungFamily_nonempty` at `t = 0`.
6. `close_recovers_both_halves` — **round trip**: the delivered equality gives
   back *both* frozen halves of line 488, the lower bound `C_W + r_Q ≤ comp R⁺`
   and the selector upper bound `comp R⁺ ≤ comp W + r_Q`.  Nothing is lost by
   stating the close as one equation.

## Faithfulness notes (mechanical rules M1--M10)

* **No new definition, no structure, no premise bundle.**  Every hypothesis is
  an explicit binder, in the frozen order.  Since there is no constructor
  anywhere in the module, no complexity or robustness conclusion can sit in
  constructor data, and no field can restate a derived telescope.
* **Nothing is weakened, nothing is re-proved.**  The conclusion of
  `directOutputEqualityClose` is byte-identical to the conclusion of
  `BridgeOutputEquality.directOutputEquality`; the difference is entirely on
  the premise side, where the frozen gate list is replaced by the abstract top
  rung that line 488 names, and which the banked rung discharges (witness 1).
  `directOutputEquality` itself is untouched and is not re-derived anywhere
  here.
* **Selector costs preserved.**  Line 74's *exactly* `r_Q` is carried as the
  banked `Nat.clog 2 Q = r_Q`, never as an inequality; the additive upper bound
  is separate.  The width `Q = 2^{r_Q}` is never recomputed.
* **Both interlace widths.**  Only the outer width `Q = Qwidth b_out δ_U`
  occurs.  The scale-alignment width `q` does not appear and is not conflated
  with it.
* **Literal ceilings.**  None is introduced or smoothed; `x_out` and the row
  floors are consumed unchanged.
* **Finite carriers and nonemptiness.**  `Fin (Qwidth b_out δ_U) → Y` and
  `Fin (Qwidth b_out δ_U) × X`, zero-based per `conv:finite-slots`;
  `1 ≤ |Y|` stays an explicit binder wherever the banked lower half needs it,
  and aux 5 records that the family it quantifies over is inhabited.
* **Binder order** follows the frozen sentence: the matrix, then `C_W` and
  `b_out`, then the carrier nonemptiness, then line 40's `comp W = C_W`, then
  the rung the sentence names.

## Statement poles

* **Trivial-witness pole.**  There is **no existential deliverable** in this
  module: every claim is an equation between named readouts, a bound on a named
  readout, or a named-def claim about the pinned `R⁺ = Rnext W Q`.  The
  substitute check the pipeline asks for is Choice 1's Candidate-B refutation
  together with the consumed
  `BridgeOutputEquality.directOutput_needs_exact_complexity`: the weakest
  reading a trivial close could deliver — the two directions left side by side,
  with no line-40 binder — provably does *not* determine `comp R⁺`.
* **Vacuous-hypothesis pole.**  The rung premise is not free: aux 5 shows the
  family it bounds is nonempty, so `Dfamily` is not the empty-family `0` there,
  and witness 1 discharges it from the route's own banked rung rather than
  assuming it.  The line-40 binder is not free either — `BRIDGE-OUTPUT-003`'s
  `exactComplexity_refuted_at_unit_row` shows it fails at `C_W ≥ 3` for the
  one-row matrix; that refutation is consumed, not restated.
* **Vacuous-conclusion pole.**  `directOutputEqualityClose_conclusion_nontrivial`
  records that the delivered equality reads at least `7`, from the frozen
  `C_W ≥ 3` of line 40 and the banked `r_Q ≥ 4`.  An equality delivering `0`
  would be free; this one is not.

## GAP-EXPOSED (nothing is weakened to close these)

1. **Only line 488 is claimed.**  The `t = 0` rung itself is *not* discharged
   here: it stays an explicit binder, and witness 1 supplies it from the banked
   `DirectOutputLower.directOutputRung`, which is where the good-copy
   dichotomy, the projection and the defect induction actually live.  This
   module adds no rung, no counting step and no defect argument.
2. **`eq:direct-input` still has no exhibited inhabitant** in Lean and can have
   none until Stages 1--4 land.  Every statement here is conditional; the
   witnesses discharge every *numeric* binder by computation and leave `X`,
   `Y`, `W`, `comp W = C_W` and the two input clauses universally quantified.
   **No route completion is claimed.**
3. **The rest of `thm:direct-robustification` is untouched.**  `eq:bridge-carriers`
   stays with `BRIDGE-OUTPUT-003`, `lem:copy-restriction` with
   `BRIDGE-COPYREST-001`, the projection of lines 465--469 with
   `BRIDGE-COPYREST-001`, and the budget collection of `sec:one-level-completion`
   (lines 500--563) with nobody.
-/

namespace EthInapproximability.ParameterizedNP.DirectOutputEqualityClose

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.TwoCopyLadder
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.EntryAssembly
open EthInapproximability.ParameterizedNP.BridgeOutputEquality

/-! ## Part 1: the aux-lemma battery

Six general properties: the arithmetic engine of line 488, the upper half at an
arbitrary power-of-two width and in its line-40 form, the one direction of
`def:lambda` that Candidate B would need, inhabitation of the family the
premise bounds, and the round trip back to the two frozen halves.  None is
about the pinned instance of Part 4. -/

/-- **Aux 1 (the arithmetic engine of `10-direct-bridge.tex:488`).**

"The `t = 0` case gives `comp(R⁺) ≥ C_W + r_Q`, while
`lem:interlace-selector-protocol` gives the matching upper bound."

In `ℕ`: an upper bound `n ≤ d + r`, a lower bound `c + r ≤ n`, and the frozen
line-40 identification `d = c` close into the equality `n = c + r`.  Stated at
four arbitrary numbers, so it is a property of the closing step and not of the
bridge's particular values. -/
lemma natClose_of_bounds {n d c r : ℕ} (hup : n ≤ d + r) (hlow : c + r ≤ n)
    (hd : d = c) : n = c + r := by
  omega

/-- **Aux 2 (the upper half at an arbitrary power-of-two width).**

`lem:interlace-selector-protocol` (`03-preliminaries.tex:148--158`) in the
`R⁺` orientation of `10-direct-bridge.tex:63`:
`comp(Int_{2^w}(W)^T) ≤ comp W + w`.

The banked `DirectOutput.selectorUpper_two_pow` is consumed for the interlace
and `NPCC.comp_transpose` — the frozen "transposition costs nothing" of
`03-preliminaries.tex:100` — transports it across the transpose.  The exponent
is arbitrary, so this is not a property of the canonical width. -/
lemma selectorUpper_transpose_two_pow {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (w : ℕ) :
    D (EthBridge.Rnext W (2 ^ w)) ≤ D W + w := by
  have hswap : D (EthBridge.Rnext W (2 ^ w)) = D (interlaceFun W (2 ^ w)) :=
    NPCC.comp_transpose (interlaceFun W (2 ^ w))
  rw [hswap]
  exact selectorUpper_two_pow W w

/-- **Aux 3 (the upper half in its line-40 form).**

`10-direct-bridge.tex:40`, "let `W` satisfy `comp W = C_W`", applied to aux 2:
`comp(Int_{2^w}(W)^T) ≤ C_W + w`.  This is the exact shape the close consumes,
and it is what makes the two halves of line 488 meet at the *same* value —
without line 40 they do not, as the consumed
`BridgeOutputEquality.directOutput_needs_exact_complexity` shows. -/
lemma selectorUpper_transpose_of_exact {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW w : ℕ} (hCWeq : D W = CW) :
    D (EthBridge.Rnext W (2 ^ w)) ≤ CW + w := by
  have h := selectorUpper_transpose_two_pow W w
  rw [hCWeq] at h
  exact h

/-- **Aux 4 (`Λ` gives the top rung).**

`def:lambda` (`03-preliminaries.tex:224`, unfolding at lines 234--240) is a
minimum over exactly three rungs, and its **first** rung is the one line 488
uses.  So a caller holding the assembled `Λ` bound of lines 483--487 holds, in
particular, the `t = 0` rung.

Stated at an arbitrary game, copy count, both density parameters and an
arbitrary target, over the banked `TwoCopyLadder.le_LambdaGE_iff`.  Only this
direction is available: the converse is exactly what
`closeInput_candidateB_demands_more` refutes. -/
lemma topRung_of_LambdaGE {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) (n : ℕ) (h : n ≤ LambdaGE f p x z) :
    n ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x z) :=
  ((le_LambdaGE_iff f p x z n).mp h).1

/-- **Aux 5 (inhabitation of the family the premise bounds).**

The rung family of `10-direct-bridge.tex:452--455` at `t = 0` — the one line
488's premise is a bound on — is nonempty at the globally fixed `y = 3/5`.
This is the banked `EntryAssembly.entryRungFamily_nonempty` at `t = 0`, with
the frozen density `y / 2^0` read as `y`.

It matters because `Dfamily` is an `sInf` over `ℕ`, which is `0` on the empty
family: without it the close's premise would be satisfiable for the empty
reason.  Stated for arbitrary `b_out` and `δ_U`. -/
lemma topRungFamily_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (bout : ℕ) (δU : ℝ) (hY : 1 ≤ Fintype.card Y) :
    (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
      (xOut bout) ((3 : ℝ) / 5)).Nonempty := by
  have h := entryRungFamily_nonempty (X := X) (Y := Y) bout δU hY 0
  simpa using h

/-- **Aux 6 (round trip: the equality gives back both frozen halves).**

From `comp R⁺ = C_W + r_Q` and the line-40 binder one recovers exactly the two
statements line 488 joins: the lower bound `C_W + r_Q ≤ comp R⁺` (its `t = 0`
half) and the selector upper bound `comp R⁺ ≤ comp W + r_Q` (its
`lem:interlace-selector-protocol` half).  So stating the close as a single
equation loses nothing, which is the encoding-correctness test for reading line
490's "This proves `eq:direct-output`" as one equality. -/
lemma close_recovers_both_halves {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW bout : ℕ} {δU : ℝ} (hCWeq : D W = CW)
    (heq : D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU) :
    CW + rQ bout δU ≤ D (EthBridge.Rnext W (Qwidth bout δU)) ∧
      D (EthBridge.Rnext W (Qwidth bout δU)) ≤ D W + rQ bout δU := by
  rw [hCWeq]
  omega

/-! ## Part 2: the close of `10-direct-bridge.tex:488--490` -/

/-- **Line 488, both halves joined** (`10-direct-bridge.tex:488--490`):

"The `t = 0` case gives `comp(R⁺) ≥ C_W + r_Q`, while
`lem:interlace-selector-protocol` gives the matching upper bound.  This proves
`eq:direct-output`."

Candidate A of the header.  The premise is the **`t = 0` rung** — the object
the frozen sentence names, at the top level `a_0 = r_Q` of the banked schedule
— together with the frozen line-40 binder `comp W = C_W`.  The lower half is
the banked `EntryAssembly.entryComplexityDescent`, consumed unchanged; the
upper half is the banked
`DirectOutput.canonicalSelectorUpper_transpose`, rewritten along line 40; and
the two meet by aux 1.

This is where the `BRIDGE-ASSEMBLY-001` endpoint is retired: that row's
GAP-EXPOSED 4 recorded that `lem:interlace-selector-protocol` was not invoked
and that only the lower half of line 488 was read off the loop.  Here it is
invoked, and the sentence is complete.

The conclusion is byte-identical to that of
`BridgeOutputEquality.directOutputEquality`; the difference is entirely on the
premise side, and that banked theorem is neither edited nor re-proved. -/
theorem directOutputEqualityClose {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ} (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW)
    (h0 : CW + entryLevelA bout δU 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 : ℝ) / 5))) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU := by
  have hlow := entryComplexityDescent W CW bout hY h0
  have hup := canonicalSelectorUpper_transpose W bout δU
  exact natClose_of_bounds hup hlow hCWeq

/-- **The close for a caller holding the assembled `Λ`** — Candidate B of the
header, retained as a **derived corollary only**.

Lines 483--487 assemble the three rungs into
`Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q`; aux 4 extracts from it the `t = 0` rung
that line 488 actually uses, and the close then applies.  So every banked
`Λ`-endpoint of the route — `EntryAssembly.entryDescent`,
`.entryAssembly_ofSelection`, `.entryAssembly_ofVSideSelection`,
`DirectOutputLower.directOutputLower` — reaches the equality without any new
mathematics.

This is **not** the encoding of line 488: its premise demands the `t = 1` and
`t = 2` rungs as well, which the frozen sentence never mentions.  See
`closeInput_candidateB_demands_more`. -/
theorem directOutputEquality_ofLambdaGE {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ} (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW)
    (hLam : CW + rQ bout δU
      ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
          ((3 : ℝ) / 5)) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU := by
  have h0 := topRung_of_LambdaGE
    (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) ((3 : ℝ) / 5)
    (CW + rQ bout δU) hLam
  rw [← entryLevelA_zero bout δU] at h0
  exact directOutputEqualityClose W CW bout hY hCWeq h0

/-- **`eq:direct-output` as one statement, closed from the loop's own rungs**
(`10-direct-bridge.tex:483--490`).

The loop premise of `BRIDGE-ASSEMBLY-001` — the three rungs `t = 0, 1, 2` at
densities `y / 2^t` — now yields *both* halves of `eq:direct-output`: the
robustness bound is the banked `EntryAssembly.entryDescent`, consumed
unchanged, and the exact complexity is the close above, applied to the same
premise at `t = 0` after the frozen density `y / 2^0` is read as `y`.

This is the sentence of line 490, "This proves `eq:direct-output`", performed
over the route's own loop rather than over the vendored entry term. -/
theorem directOutputClose {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ} (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW)
    (hrung : ∀ t, t ≤ 2 →
      CW + entryLevelA bout δU t
        ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
            (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
              (xOut bout) ((3 / 5) / 2 ^ t))) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU ∧
      CW + rQ bout δU
        ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
            ((3 : ℝ) / 5) := by
  have h0 := hrung 0 (by norm_num)
  have e0 : ((3 : ℝ) / 5) / 2 ^ (0 : ℕ) = (3 : ℝ) / 5 := by norm_num
  rw [e0] at h0
  exact ⟨directOutputEqualityClose W CW bout hY hCWeq h0,
    entryDescent W CW bout hrung⟩

/-- **The close read out in both frozen readings of the selector sentence**
(`10-direct-bridge.tex:488--490` together with lines 73--74).

The same premise as `directOutputEqualityClose`, with the conclusion stating
the equality, the *exact* selector count `⌈log₂ Q⌉ = r_Q` of line 74 (an
equation, never an inequality), and the reader's protocol form at an arbitrary
budget `U`.  The last two are the banked
`DirectOutput.canonicalSelectorBits` and `.canonicalSelectorProtocol`,
consumed; nothing about them is restated or re-proved. -/
theorem directOutputEqualityClose_readouts {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ} (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW)
    (h0 : CW + entryLevelA bout δU 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 : ℝ) / 5))) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU ∧
      Nat.clog 2 (Qwidth bout δU) = rQ bout δU ∧
      (∀ U : ℕ, D W ≤ U →
        D (EthBridge.Rnext W (Qwidth bout δU)) ≤ U + rQ bout δU) :=
  ⟨directOutputEqualityClose W CW bout hY hCWeq h0,
    canonicalSelectorBits bout δU,
    fun U hU => canonicalSelectorProtocol W bout δU U hU⟩

/-! ## Part 3: the encoding refutation and the value pole -/

/-- **Candidate B demands strictly more than line 488.**

`le_LambdaGE_iff` unfolds `n ≤ Λ_M(p, x, z)` into the **three** conjuncts
`n ≤ D(z)`, `n ≤ 1 + D(z/2)`, `n ≤ 2 + D(z/4)`.  The frozen sentence at line
488 supposes only the first.  In that exact shape, the first conjunct does not
imply the other two: at `n = 5`, `d₀ = 5`, `d₁ = d₂ = 0` the top rung holds and
the second rung fails.

So an encoding of line 488 whose premise is the assembled `Λ` bound would ask a
caller for two rungs the frozen sentence never mentions.  That is why Candidate
A takes the `t = 0` rung and `directOutputEquality_ofLambdaGE` is kept only as
a corollary of it, never as the statement. -/
theorem closeInput_candidateB_demands_more :
    ¬ ∀ n d₀ d₁ d₂ : ℕ, n ≤ d₀ → (n ≤ d₀ ∧ n ≤ 1 + d₁ ∧ n ≤ 2 + d₂) := by
  intro h
  have hbad := (h 5 5 0 0 (by norm_num)).2.1
  omega

/-- **The delivered equality is not trivial.**

`C_W ≥ 3` (frozen line 40) and the banked `EntryGates.four_le_rQ` force
`comp R⁺ = C_W + r_Q ≥ 7` at every legal parameter choice.  An equality
delivering `0` would be free; this one is not.  The banked
`DirectOutputLower.directOutputLower_conclusion_nontrivial` supplies the
arithmetic and is consumed, not restated. -/
theorem directOutputEqualityClose_conclusion_nontrivial {X Y : Type*}
    [Fintype X] [Fintype Y] (W : X → Y → Bool) {CW bout : ℕ} {δU : ℝ}
    (hCW : 3 ≤ CW)
    (heq : D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU) :
    7 ≤ D (EthBridge.Rnext W (Qwidth bout δU)) := by
  have h7 : 7 ≤ CW + rQ bout δU :=
    directOutputLower_conclusion_nontrivial (bout := bout) (δU := δU) hCW
  omega

/-! ## Part 4: non-vacuity

LANE-GATE 3 and LANE-GATE 4b/4c.  Each item excludes one degeneracy a green
build cannot see. -/

/-- **Non-vacuity witness 1: the close's premise is satisfiable with real
content.**

The abstract `t = 0` rung is discharged by the banked
`DirectOutputLower.directOutputRung` under exactly the frozen
`eq:direct-input` binders, with the frozen density `y / 2^0` read as `y`.  So
the premise of the close is not an empty container: it is the route's own top
rung.

`X`, `Y`, `W` stay universally quantified and both input clauses stay
hypotheses, since `eq:direct-input` has no exhibited inhabitant in Lean
(GAP-EXPOSED 2). -/
theorem topRung_fires_via_bankedRung {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    CW + entryLevelA bout δU 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 : ℝ) / 5)) := by
  have h0 := directOutputRung W CW bout (t := 0) (by norm_num) hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput
  have e0 : ((3 : ℝ) / 5) / 2 ^ (0 : ℕ) = (3 : ℝ) / 5 := by norm_num
  rw [e0] at h0
  exact h0

/-- **Non-vacuity witness 2: the close fires at the banked first entry-gate
witness, and the two frozen halves are exhibited at a pinned value.**

`b_out = 1`, `δ_U = 1/60`, `C_W = 3` — the boundary of line 40 — where the
banked entry apparatus reads `r_Q = 13` and `Q = 8192`.  The equality then
reads `comp R⁺ = 16`, the value is above the general floor `7`, the exact
selector count is `13` bits, and the round trip of aux 6 returns both frozen
halves of line 488 at those numbers.

Only the numeric binders are discharged by computation: `X`, `Y`, `W`, the
line-40 binder and the `t = 0` rung stay universally quantified, since the
bridge's input matrix has no exhibited inhabitant in Lean and can have none
until Stages 1--4 land. -/
theorem directOutputEqualityClose_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = 3)
    (h0 : (3 : ℕ) + entryLevelA 1 (1 / 60) 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth 1 (1 / 60))) 1)
          (bracketGE (Fin (Qwidth 1 (1 / 60)) → Y)
            (Fin (Qwidth 1 (1 / 60)) × X) 1 (xOut 1) ((3 : ℝ) / 5))) :
    rQ 1 (1 / 60) = 13 ∧ Qwidth 1 (1 / 60) = 8192 ∧
      D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) = 16 ∧
      7 ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) ∧
      Nat.clog 2 (Qwidth 1 (1 / 60)) = 13 ∧
      (16 : ℕ) ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) ∧
      D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) ≤ D W + 13 := by
  obtain ⟨-, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  have heq := directOutputEqualityClose W 3 1 (δU := 1 / 60) hY hCWeq h0
  have h7 : 7 ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) :=
    directOutputEqualityClose_conclusion_nontrivial W (CW := 3) (by norm_num) heq
  have hbits := canonicalSelectorBits 1 (1 / 60 : ℝ)
  obtain ⟨hlow, hup⟩ :=
    close_recovers_both_halves W (bout := 1) (δU := 1 / 60) hCWeq heq
  rw [hrQ] at heq hlow hup hbits
  exact ⟨hrQ, hQ, by omega, h7, hbits, by omega, hup⟩

/-- **Non-vacuity witness 3: the close fires again at the banked second
witness, at a different arithmetic.**

`b_out = 1`, `δ_U = 1/200`, `C_W = 3`, where the banked apparatus reads
`Q_0 = 16000`, `r_Q = 14` and `Q = 16384`.  The width, the canonical exponent,
the selector cost and the delivered constant all move — the equality now reads
`comp R⁺ = 17` — which a statement satisfiable at only one numeral could not
do. -/
theorem directOutputEqualityClose_fires_second_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = 3)
    (h0 : (3 : ℕ) + entryLevelA 1 (1 / 200) 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth 1 (1 / 200))) 1)
          (bracketGE (Fin (Qwidth 1 (1 / 200)) → Y)
            (Fin (Qwidth 1 (1 / 200)) × X) 1 (xOut 1) ((3 : ℝ) / 5))) :
    rQ 1 (1 / 200) = 14 ∧ Qwidth 1 (1 / 200) = 16384 ∧
      D (EthBridge.Rnext W (Qwidth 1 (1 / 200))) = 17 ∧
      7 ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 200))) ∧
      Nat.clog 2 (Qwidth 1 (1 / 200)) = 14 := by
  obtain ⟨-, hrQ, hQ, -, -, -, -⟩ := directOutput_fires_second_witness
  have heq := directOutputEqualityClose W 3 1 (δU := 1 / 200) hY hCWeq h0
  have h7 : 7 ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 200))) :=
    directOutputEqualityClose_conclusion_nontrivial W (CW := 3) (by norm_num) heq
  have hbits := canonicalSelectorBits 1 (1 / 200 : ℝ)
  rw [hrQ] at heq hbits
  exact ⟨hrQ, hQ, by omega, h7, hbits⟩

/-- **Non-vacuity witness 4: the `Λ`-side corollary fires from the banked
loop.**

`EntryAssembly.entryDescent_fires_via_bankedRungs` delivers the assembled
`Λ` bound of lines 483--487 under the frozen `eq:direct-input` binders; aux 4
extracts its top rung and the close turns it into the equality.  So the
Candidate-B corollary is not an empty shell either — it is reachable from the
route's own loop.

The frozen range `θ ≤ 1` of line 39 is *not* assumed: it is delivered by the
consumed `BridgeOutputEquality.theta_le_one_of_entryGate` from the first entry
gate, recorded here as the second conjunct so that the hypothesis list is
visibly no stronger than the paper's. -/
theorem directOutputEquality_ofLambdaGE_fires {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU ∧ θ ≤ 1 := by
  have hLam := entryDescent_fires_via_bankedRungs W CW bout hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput
  exact ⟨directOutputEquality_ofLambdaGE W CW bout hY hCWeq hLam,
    theta_le_one_of_entryGate (bout := bout) (δU := δU) hθ0 hgate⟩

/-- **Non-vacuity witness 5: the family the premise bounds is inhabited at the
canonical width.**

Aux 5 at the banked first entry-gate witness, where `Q = 8192`: the `t = 0`
rung family of `10-direct-bridge.tex:452--455` is nonempty, so the close's
premise is a bound on a genuine `sInf` and not on the empty-family `0`.  `X`
stays universally quantified; `Y` is pinned to `Bool` only because a carrier
must be exhibited. -/
theorem topRungFamily_nonempty_fires_first_witness {X : Type*} [Fintype X] :
    Qwidth 1 (1 / 60) = 8192 ∧
      (bracketGE (Fin (Qwidth 1 (1 / 60)) → Bool)
        (Fin (Qwidth 1 (1 / 60)) × X) 1 (xOut 1) ((3 : ℝ) / 5)).Nonempty := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  exact ⟨hQ, topRungFamily_nonempty (X := X) (Y := Bool) 1 (1 / 60) (by decide)⟩

end EthInapproximability.ParameterizedNP.DirectOutputEqualityClose
