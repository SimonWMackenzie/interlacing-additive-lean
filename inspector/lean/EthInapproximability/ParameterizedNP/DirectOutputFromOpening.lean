import EthInapproximability.ParameterizedNP.BridgeOutputEquality
import EthInapproximability.ParameterizedNP.DirectBridgeOpening

/-!
# Parameterized NP route: `thm:direct-robustification`'s conclusions, from the landed opening

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-OUTPUT-004`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t3f` tranche to close **GAP-EXPOSED G1 of `BRIDGE-OPENING-001`**.

## Placement note (read first)

The tranche argument named `DirectOutput.lean` as the target file.  That file is
**not writable for this content**: it is the landed `BRIDGE-OUTPUT-001` module
and is imported by `DirectOutputLower.lean`, hence by `BridgeOutputEquality.lean`.
This module must consume `BridgeOutputEquality.directRobustification` *and*
`DirectBridgeOpening.directBridgeOpening`, so placing it in `DirectOutput.lean`
would make the import graph cyclic (`DirectOutput -> BridgeOutputEquality ->
DirectOutputLower -> DirectOutput`) and no build could succeed.  The content is
therefore landed in this new sibling module under the same route directory, the
`BRIDGE-OUTPUT-001` body is left untouched (SHARED-FILE RULE), and the deviation
is recorded here and in the ledger row.

## What this module is

`BRIDGE-OPENING-001` stops at `thm:direct-robustification`'s binder list and
records, as its **G1**, that the theorem's own conclusions -- the orientation
`R^+ = transpose(Int_Q(W))` of `10:63`, the two clauses of `eq:direct-output`
(`10:66--72`), and the `r_Q`-bit selector sentence (`10:73--74`) -- are not
stated there.  `BRIDGE-OUTPUT-003` states exactly those conclusions, but takes
the theorem's *input* as three free hypotheses `hCWeq`, `hNear`, `hInput`.

This module joins the two ends.  It takes the input as the **banked Section-9
interface** `FirstWrapperClose.CommonThreshold` at the globally fixed
`y = yFixed = 3/5`, passes it through `DirectBridgeOpening.directBridgeOpening`
and `DirectBridgeOpening.directInput_at_fixed_y` -- both **by pin**, neither
restated nor re-proved -- and returns `thm:direct-robustification`'s conclusions
verbatim from the banked `BridgeOutputEquality.directRobustification`.  That is
the whole content: **no new mathematics, and no conclusion of any consumed row is
weakened, widened, or re-derived.**

`directInput_at_fixed_y` was landed with no consumer; this module is its first,
which is what "closing its wiring" means here.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
`autoformalization`.

* `sections/10-direct-bridge.tex` (SHA-256
  `ae0defbd6dd93950fc67db70584da3d0e68061a060b04cae78b1d4584358c984`),
  `thm:direct-robustification` (label line 35):
  * lines **36--37**, the globally fixed `delta = 1/10` and
    `y = 1/2 + delta = 3/5`, consumed as `EntryGates.deltaFixed` and
    `DirectBridgeOpening.yFixed`;
  * line **38**, `0 < delta_U < 1`; line **39**, `0 < theta <= 1`; line **40**,
    `comp W = C_W >= 3`; line **41**, `b_out >= 1`;
  * lines **43--51**, `lambda`, `Q_0`, and `Q = 2^{r_Q}` the least power of two
    at least `Q_0` -- the banked `EntryGates.lambdaU`, `.Q0`, `.rQ`, `.Qwidth`;
  * `eq:direct-entry-gates` (label line **56**), the banked
    `EntryGates.directEntryGates` at `y = 3/5`;
  * line **63**, `R^+ = transpose(Int_Q(W))` -- the vendored `EthBridge.Rnext`,
    whose defining equation `Rnext W Q c r = interlaceFun W Q r c`
    (`vendor/npc-cc/EthBridge/Entry.lean:181--195`) is this orientation;
  * **`eq:direct-output`** (label line **71**, display lines **66--72**), both
    clauses: `comp R^+ = C_W + r_Q` and
    `Lambda_3(R^+, 1, 2^{-b_out}, y) >= C_W + r_Q`;
  * lines **73--74**, the selector sentence, in both frozen readings.
  * lines **4--12**, `eq:direct-input`, taken here through the Section-9
    interface rather than as free hypotheses.
* `sections/09-first-wrapper.tex`, the `interfacebox` **`09:1809--1816`** and the
  Section-9 output `W = transpose(U)` at `C_W = C + r` (**`09:1794--1795`**) --
  the paper's own entry object, used for canonical inhabitation below.
* `sections/06-parameter-schedule.tex` (SHA-256
  `46a9aa59695357e5e2a42fa08537939a70f0d8421eb9cf1365ab42f8125b5fb9`), for the
  two quantities `sec:parameters` **defines** and this module's witnesses must
  therefore evaluate rather than assign:
  * **`eq:q-deltaU`** (label line **518**, display lines **514--519**),
    `delta_U = eta_R/(16 q)` -- the banked `ParameterSchedule.deltaU`;
  * **`eq:Q-theta-choice`** (label line **537**, display lines **525--538**),
    `theta = c_theta/(2Q) = delta/(16Q)` at the very `Q` of `10:47--51` -- the
    banked `ParameterSchedule.theta`;
  * **`eq:direct-theta-gates`** (label line **545**, display lines
    **541--546**), second row `4 Q_0 theta <= delta/4 < delta` -- the banked
    `ParameterSchedule.four_Q0_theta_le`, which discharges the *first* half of
    `eq:direct-entry-gates` at the schedule's own `theta`;
  * line **547**, the finite gate `delta_U <= 1/200` -- discharged at the
    scheduled point by `ParameterSchedule.deltaU_le_gates`, and the boundary
    value the BEYOND-PAPER AUDIT witness pins.
* `sections/03-preliminaries.tex`, `def:interlace` (label line **112**, display
  lines **113--118**) for the interlace carriers, and lines **215--219** for the
  fixed constants.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex` (SHA-256
`5ab193329268d18aa9940d3f7cce12c35cd25b453d6329d29f083bd8576fe8ec`).  The file
was opened and the cited item checked, first-hand, to state the same fact.

**Exactly one** reader item is claimed, and it is one that **no other
declaration in `src/` claims**:

* the unlabelled orientation display inside `thm:near-to-robust`, lines
  **101--104**, "Then `R^+ = Int_Q(W)^T`" -- claimed by
  `directOutputMatrix_transpose`, and by that declaration alone.  It states the
  same fact as the frozen `10:63`.  A repository-wide check of every
  `04-bridge.tex` citation in `src/` confirmed the item was previously
  unassigned: `BRIDGE-OUTPUT-001` cites lines 112--113, `BRIDGE-OUTPUT-002`
  lines 108--109, `BRIDGE-OUTPUT-003` lines 107 and 113--118, and none cites the
  orientation display.

**Deliberately given no reader counterpart**, to avoid a double assignment:

* `directRobustification_of_opening` and everything downstream of it.  Every
  component of its closed statement already has an assigned reader item -- the
  first equation of `eq:bridge-output` (line 107) belongs to
  `BRIDGE-OUTPUT-003`'s `directOutputEquality`, the second (line 109) to
  `BRIDGE-OUTPUT-002`'s `directOutputLower`, the selector sentence (lines
  112--113) to `BRIDGE-OUTPUT-001`'s `canonicalSelectorProtocol`,
  `eq:bridge-common-input` (label line 15) to `BRIDGE-OPENING-001`'s
  `directInput_at_fixed_y`, and the four entry items to `BRIDGE-ENTRY-001`.
  Claiming `thm:near-to-robust` as a whole would reassign items already
  assigned, so nothing fresh is claimed for the assembly.
* `eq:bridge-carriers` (label line 117) stays with `BRIDGE-OUTPUT-003`'s
  `bridgeCarriers` and is neither restated nor re-proved here.
* the width lemmas and the statement poles are interface properties, not
  transcriptions of reader statements.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **new (elementary) wiring, relative to landed inputs.**  Every
  deliverable is an application of banked, already kernel-checked route facades.
  Nothing banked is edited, widened, or re-proved.
* Consumed strictly **by pin**, never restated:
  * `DirectBridgeOpening.directBridgeOpening`, `.directInput_at_fixed_y`,
    `.yFixed`, `.yFixed_eq`, `.yFixed_mem`, and the statement pole
    `.opening_rejects_the_wrapper_close_probe` (`BRIDGE-OPENING-001`);
  * `BridgeOutputEquality.directRobustification` (`BRIDGE-OUTPUT-003`), and
    through it `BRIDGE-OUTPUT-001` and `BRIDGE-OUTPUT-002`.  Its two statement
    poles `.directRobustification_conclusion_nontrivial` and
    `.directOutput_needs_exact_complexity` are **cited by name** in Part 6 and
    deliberately **not** re-stated: both are already phrased at this module's
    own binders, so a local twin would be a duplicate declaration and a
    stale-twin hazard;
  * `FirstWrapperClose.CommonThreshold`, `.DenseRung`,
    `.commonThreshold_of_firstWrapperClose` (`FIRST-WRAPPER-CLOSE-001`);
  * `EntryGates.deltaFixed`, `.Q0`, `.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`,
    `.four_le_rQ`, `.directEntryGates`, `.secondEntryGate_of_deltaU_small`
    (`BRIDGE-ENTRY-001`);
  * `ParameterSchedule.deltaU`, `.deltaU_pos`, `.deltaU_lt_one`, `.etaR`,
    `.etaR_pos`, `.theta`, `.four_Q0_theta_le`, `.schedule_theta_in_range`,
    `.schedule_fires_directEntryGates` (`SCHEDULE-001`) -- the reifications of
    `eq:q-deltaU` and `eq:Q-theta-choice`, so that the two *defined* quantities
    of `sec:parameters` are **evaluated**, never assigned;
  * `DirectOutput.directOutput_fires_second_witness` (`BRIDGE-OUTPUT-001`) and
    `DirectOutputLower.xOut` (`BRIDGE-OUTPUT-002`);
  * `ScaleAlignOpening.wrapperW`, `.wrapperU`, `.scaleAlignWidth`,
    `.scaleAlignWidth_def` (`SCALEALIGN-001`);
  * the vendored `EthBridge.Rnext`, `EthBridge.Rnext_apply` and
    `NPCC.comp_transpose`.
* Imports: `BridgeOutputEquality.lean` and `DirectBridgeOpening.lean` only,
  hence `DirectOutputLower.lean`, `DirectOutput.lean`, `EntryGates.lean`,
  `PilotStage3.lean`, `FirstWrapperClose.lean` and its chain -- which is where
  `ParameterSchedule.lean` enters, so `SCHEDULE-001` is reached without a new
  import line -- `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom is not in scope, and
  there is no contact with `EXPANDER-001` (which by design has no Lean
  declaration and would have to stay an explicit named hypothesis).
* External adapters: none.  Nothing here is axiomatized; no opaque certificate,
  no unproved placeholder of either kind the release gate scans for.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Conditional statuses of the consumed chain, disclosed exactly

The ledger statuses of every consumed row travel unchanged; this module improves
none of them, and each conditionality below is inherited, not introduced.

1. **`FIRST-WRAPPER-CLOSE-001`** supplies `CommonThreshold`.  Its
   `firstWrapperClose` runs under the **named, undischarged** binder
   `FirstWrapperClose.DenseRung` (`eq:wrapper-u-dense`, `09:262--263`), so its
   `commonThreshold_of_firstWrapperClose` is **conditional** -- and therefore so
   is `directOutput_at_the_paper_instance` here, in exactly the same way and to
   exactly the same degree.
2. Through that row travel, unchanged: `TERMINAL-TWO-STREAM-001` (headline
   `lem:terminal-two-stream` landed as a **stated** claim, not a proved theorem,
   and **not invoked** anywhere below), `DENSE-WRAPPER-FRONTIER-001` and
   `WRAPPER-PROTECTED-EARLY-001` (landed, GAP-EXPOSED items intact), and
   `WRAPPER-MASS-REDISTRIBUTION-001` (landed with four GAP-EXPOSED items and its
   own deferred canonical-inhabitation obligation on record).
3. **`BRIDGE-OUTPUT-002`** supplies the lower clause of `eq:direct-output`; its
   own GAP-EXPOSED items, and the `lem:copy-restriction` interface it consumes
   inside the vendored term, are untouched.
4. **`BRIDGE-OUTPUT-003`** supplies the equality and the closed theorem, with
   its GAP-EXPOSED item 1 (`eq:direct-input` has no exhibited unconditional
   inhabitant in Lean) intact.
5. **`BRIDGE-ENTRY-001`** supplies `lambda`, `Q_0`, `r_Q`, `Q` and the gate
   pair.  No numeral is assigned to any of them here.
6. **`SCHEDULE-001`** *is* consumed, and it is what makes the parameter
   witnesses of Part 7 legal.  `sec:parameters` **defines** both `delta_U`
   (`eq:q-deltaU`, `06:517`) and `theta` (`eq:Q-theta-choice`, `06:533`), so
   neither may be given a numeral in a witness; the values are obtained by
   evaluating the definitional chain through the banked
   `ParameterSchedule.deltaU` and `ParameterSchedule.theta`, and the two entry
   binders are then discharged rather than assumed, by
   `ParameterSchedule.four_Q0_theta_le` (`eq:direct-theta-gates` second row,
   `06:544`) and `ParameterSchedule.schedule_theta_in_range` (`10:39`).  The
   row's own status travels unchanged and is not improved here.

## Both interlace widths, kept distinct

Two widths meet at the paper's entry object and are never identified:

* the **scale-alignment** width `q = 2^r`
  (`ScaleAlignOpening.scaleAlignWidth`), internal to the Section-9 wrapper
  `W = transpose(U)`, whose carriers are `Fin (2^r) -> Cl` and `Fin (2^r) x Rw`;
* the **outer** bridge width `Q = 2^{r_Q}` (`EntryGates.Qwidth`), which is what
  `R^+ = transpose(Int_Q(W))` interlaces over.

`widths_ne_of_exponents_ne` and `scaleAlignWidth_ne_Qwidth_of_lt_four` record
the separation as checked theorems rather than as a comment, and
`directOutput_at_the_paper_instance` is the one declaration in which both occur
simultaneously.  **No numeral is assigned to `r` or to `q = 2^r` anywhere.**
The frozen schedule fixes them -- `q = 2^{A_wrap L_P^2}` at `eq:q-deltaU`
(`06:515`) -- and although this module now consumes `SCHEDULE-001` for
`delta_U` and `theta`, it consumes the wrapper width only as the *free binder*
`q` that `eq:q-deltaU` itself quantifies over in
`ParameterSchedule.deltaU`.  Every width statement is therefore general in `r`
(equivalently in `q`) or hypothesis-guarded, and the outer `Q` is never
substituted for it.

## Faithfulness notes (mechanical rules M1--M10)

* **No structure, no premise bundle, and no new definition.**  Every deliverable
  takes its hypotheses as **explicit binders**; the only bundled hypotheses are
  the paper's own `EntryGates.directEntryGates` (display `eq:direct-entry-gates`)
  and the banked `FirstWrapperClose.CommonThreshold` (the `interfacebox`
  `09:1809--1816`), both consumed by pin.  No conclusion of `eq:direct-output`
  sits in constructor data.
* **Binder order** follows the frozen theorem, lines 38--56: `C_W >= 3`, then
  `0 < delta_U < 1`, then `0 < theta <= 1`, then `b_out >= 1`, then the
  carriers, then the gate pair, then the input record.
* **Selector costs preserved.**  Line 74's *exactly* `r_Q` is carried as the
  equation `Nat.clog 2 Q = r_Q`, never as an inequality; the protocol form keeps
  `U` an explicit binder as the reader writes it.
* **Literal ceilings.**  None is introduced or rewritten; `A_a` is not mentioned.
* **Finite carriers and nonemptiness.**  `1 <= |X|` and `1 <= |Y|` are explicit
  binders as `10:102` and reader line 83 require, and at the paper instance both
  are *derived* from `1 <= |Rw|`, `1 <= |Cl|` rather than assumed.
* **Defined versus free.**  `delta_U` and `theta` are **defined** by
  `sec:parameters`, not free, so no witness in this module assigns them a
  numeral: they are evaluated through `ParameterSchedule.deltaU` and
  `ParameterSchedule.theta`.  The one exception is explicitly labelled
  **BEYOND-PAPER AUDIT** and claims no legality beyond the paper's own finite
  gate `06:547`; see Part 7.
* **Trivial-witness pole.**  There is **no existential deliverable** in this
  module: every claim is an equation between named readouts, a bound on a named
  readout, or a named-def claim about the pinned `EthBridge.Rnext W (Qwidth ...)`.
  The pipeline's substitute check is the banked
  `BridgeOutputEquality.directOutput_needs_exact_complexity`, which shows that
  dropping the interface's `exact` field leaves the two banked directions unable
  to determine `comp R^+`; it is cited, not restated.

## Statement poles

* **Vacuous-conclusion pole.**  The banked
  `BridgeOutputEquality.directRobustification_conclusion_nontrivial` records
  `comp R^+ = C_W + r_Q >= 7` at every legal parameter, from the frozen
  `C_W >= 3` (line 40) and the banked `r_Q >= 4`.  It is stated at exactly this
  module's binders, so it is cited by name rather than duplicated.
* **Vacuous-hypothesis pole.**  The input record is not free: consumed from
  `BRIDGE-OPENING-001`, any inhabitant at `C_W >= 2` forces
  `|Rows(W)| * theta > 1`, hence `|Rows(W)| > 640` under the frozen first gate.
  The banked `DirectBridgeOpening.opening_rejects_the_wrapper_close_probe`
  refutes the Section-9 NON-FIDELITY probe as a supplier of this input for
  **every** `y`, hence verbatim at this module's `y = yFixed`; it is cited by
  name in Part 6 and deliberately not specialized here.
* **Hypothesis consistency.**  The hypothesis bundle is the conjunction of
  `BRIDGE-OPENING-001`'s (which is satisfiable at legal parameters, and is
  inhabited by the paper's object conditionally) with `BRIDGE-OUTPUT-003`'s gate
  pair; both were separately checked consistent at the frozen `y = 3/5`.  In
  this module the check is sharper than a numeral probe:
  `directOutput_from_opening_at_the_scheduled_point` **derives** the whole gate
  pair, together with `0 < delta_U < 1` and `0 < theta <= 1/4`, from the frozen
  schedule at symbolic `s`, `delta_v(G)`, `zeta`, `q`, `b_out` -- so the bundle
  is consistent on a whole family of legal points, not at one arithmetic --
  and `directOutput_from_opening_fires_at_the_gate_boundary` moves the width,
  the canonical exponent and the selector cost, which a bundle satisfiable at a
  single arithmetic could not do.

## DEFERRED CANONICAL INHABITATION (registered, open)

The paper constructs exactly one object that enters this bridge: the Section-9
output `W = transpose(U)` at `C_W = C + r` (`09:1794--1795`).  That instance --
not a synthetic one -- is the required witness, and it is landed here as
`directOutput_at_the_paper_instance`, **conditionally** on
`FirstWrapperClose.DenseRung` and the low-rung inputs, exactly as its supplier
is.  The unconditional form is **not** claimed; it is discharged precisely when
`DenseRung` is proved, i.e. when the routed certificate system of GAP-EXPOSED M1
of `WRAPPER-MASS-REDISTRIBUTION-001` lands in Lean.  **No synthetic stand-in is
offered, and that is forced rather than chosen** -- see the banked
`DirectBridgeOpening.opening_rejects_the_wrapper_close_probe` (cited in Part 6)
and `DirectBridgeOpening.bridgeEntry_forces_large_row_carrier`.  The two
Part-7 theorems are **parameter** witnesses only: they leave `X`, `Y`, `W`
universally quantified and the input record a hypothesis, and they are not, and
do not pretend to be, inhabitations.  Of the two,
`directOutput_from_opening_at_the_scheduled_point` is the paper-derived one (no
numeral at any defined quantity) and
`directOutput_from_opening_fires_at_the_gate_boundary` is an explicitly
labelled **BEYOND-PAPER AUDIT** instance of our encoding at a point the frozen
source never visits -- strictly weaker evidence, and never a substitute.

## GAP-EXPOSED

* **G1 of `BRIDGE-OPENING-001` is closed** in the stated sense only: the
  theorem's conclusions are now available *from the Section-9 interface*.  They
  are not proved afresh -- they are the banked `BRIDGE-OUTPUT-001..003`
  conclusions, which retain their own GAP-EXPOSED items.
* **G3 of `BRIDGE-OPENING-001` remains open**: an unconditional inhabitant of the
  entry point at the route's own `W` is still not exhibited, because `DenseRung`
  is undischarged upstream.  Every conclusion of this module about the paper's
  object therefore remains conditional.
* `lem:copy-restriction` (`10:132`), the column-defect apparatus of
  `10:76--571`, the budget collection of `sec:one-level-completion`, and the
  Stage-4 carrier substitution of `05-public-records.tex:834--836` are untouched
  and belong to other rows.

**No route completion is claimed anywhere in this module.**
-/

namespace EthInapproximability.ParameterizedNP.DirectOutputFromOpening

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.DirectBridgeOpening
open EthInapproximability.ParameterizedNP.FirstWrapperClose

/-! ## Part 1  The orientation `R^+ = transpose(Int_Q(W))` (`10:63`) -/

/-- **`R^+ = transpose(Int_Q(W))`** -- `10-direct-bridge.tex:63`.

*Reader counterpart:* the unlabelled display inside `thm:near-to-robust`,
`04-bridge.tex:101--104`, "Then `R^+ = Int_Q(W)^T`".  This is the one reader
item this module claims, and it is claimed by this declaration alone.

Stated entrywise, which is what a matrix equality between two Boolean matrices
means: the `(c, r)` entry of `R^+` is the `(r, c)` entry of the `Q`-fold
interlace.  The vendored `EthBridge.Rnext` is the frozen `R^+` and its defining
equation `EthBridge.Rnext_apply` is consumed; nothing is redefined.  General in
the carriers, the matrix, and the width. -/
theorem directOutputMatrix_transpose {X Y : Type*} (W : X → Y → Bool) (Q : ℕ)
    (c : Fin Q → Y) (r : Fin Q × X) :
    EthBridge.Rnext W Q c r = interlaceFun W Q r c :=
  EthBridge.Rnext_apply W Q c r

/-- **Aux 1 (round trip): transposing `R^+` back recovers the interlace.**

Transposition is an involution on Boolean matrices, so reading `10:63` in the
other direction returns `Int_Q(W)` on the nose.  Recorded because the lower
clause of `eq:direct-output` is proved by transposing an arbitrary bracket
member, and that step is only legal if the round trip is exact.  General. -/
theorem directOutputMatrix_transpose_involutive {X Y : Type*}
    (W : X → Y → Bool) (Q : ℕ) :
    (fun (r : Fin Q × X) (c : Fin Q → Y) => EthBridge.Rnext W Q c r)
      = interlaceFun W Q := rfl

/-- **Aux 2 (transposition costs nothing).**  `comp R^+ = comp Int_Q(W)`, the
vendored `NPCC.comp_transpose` at the frozen orientation of `10:63`.

This is the general fact behind the selector clause of lines 73--74: the
selector protocol is stated for the interlace, and line 63 transposes it.
General in the carriers, the matrix, and the width. -/
theorem D_directOutputMatrix {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (Q : ℕ) :
    D (EthBridge.Rnext W Q) = D (interlaceFun W Q) :=
  NPCC.comp_transpose (interlaceFun W Q)

/-! ## Part 2  The two interlace widths, kept distinct

`q = 2^r` is the scale-alignment width internal to the Section-9 wrapper;
`Q = 2^{r_Q}` is the outer width of `10:51` that `R^+` interlaces over.  No
numeral is assigned to `r`, which the frozen schedule fixes. -/

/-- **Aux 3 (the widths separate whenever their exponents do).**

`q = 2^r` and `Q = 2^{r_Q}` are equal only if `r = r_Q`, because doubling is
injective on exponents.  This is the general form of "both interlace widths are
kept distinct": nothing in the route forces the two exponents together, and the
bridge never substitutes one width for the other.  General in `r`, `b_out` and
`delta_U`. -/
theorem widths_ne_of_exponents_ne {r bout : ℕ} {δU : ℝ} (h : r ≠ rQ bout δU) :
    ScaleAlignOpening.scaleAlignWidth r ≠ Qwidth bout δU := by
  rw [ScaleAlignOpening.scaleAlignWidth_def, Qwidth_eq_two_pow]
  exact fun hc => h (Nat.pow_right_injective (le_refl 2) hc)

/-- **Aux 4 (a quantitative separation, with no numeral for `r`).**

Every small scale-alignment width is strictly below the bridge's canonical
width: `q = 2^r <= 8` for `r < 4`, while `Q = 2^{r_Q} >= 16` always, by the
banked `EntryGates.four_le_rQ`.  So the two widths cannot be conflated on the
whole low range of `r` at *any* legal `b_out` and `delta_U`, without ever
assigning `r` a value the frozen schedule owns. -/
theorem scaleAlignWidth_ne_Qwidth_of_lt_four {r : ℕ} (bout : ℕ) (δU : ℝ)
    (hr : r < 4) : ScaleAlignOpening.scaleAlignWidth r ≠ Qwidth bout δU := by
  have h16 : 16 ≤ Qwidth bout δU := by
    have h4 := four_le_rQ bout δU
    have hpow : (2 : ℕ) ^ 4 ≤ 2 ^ rQ bout δU :=
      Nat.pow_le_pow_right (by norm_num) h4
    rw [Qwidth_eq_two_pow]
    simpa using hpow
  have h8 : ScaleAlignOpening.scaleAlignWidth r ≤ 8 := by
    have hpow : (2 : ℕ) ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ScaleAlignOpening.scaleAlignWidth_def]
    simpa using hpow
  omega

/-! ## Part 3  The input, taken through the landed opening -/

/-- **Aux 5 (identity): the input record at `yFixed` is the record at `3/5`.**

`yFixed` is the *defining display* `y = 1/2 + delta` of `10:36--37`, and
`DirectBridgeOpening.yFixed_eq` evaluates that chain to the printed `3/5`.  So
writing the interface at `yFixed` -- which is what makes
`directInput_at_fixed_y` applicable -- costs nothing and loses nothing: the two
readings are the same proposition.  Recorded so that the substitution below is a
checked step rather than a silent one.  General. -/
theorem commonThreshold_at_yFixed_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) (θ δU : ℝ) :
    CommonThreshold W CW θ δU yFixed ↔ CommonThreshold W CW θ δU (3 / 5) := by
  rw [yFixed_eq]

/-- **Disclosure: the opening supplies exactly the binder `BRIDGE-OUTPUT-003`
demands.**

`BridgeOutputEquality.directRobustification` takes `comp W = C_W` (`10:40`) as a
free hypothesis `hCWeq`.  `DirectBridgeOpening.directBridgeOpening`'s **first**
conclusion is that same equation, delivered from the Section-9 interface.  This
theorem states the identification in the kernel, so that the wiring below is a
checked application of the landed opening and not an appeal to the interface's
field by another route.  All of the opening's binders are carried, exactly as it
states them. -/
theorem opening_supplies_exactComplexity {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {θ δU : ℝ}
    (hCW : 3 ≤ CW) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hbout : 1 ≤ bout)
    (hX : 1 ≤ Fintype.card X)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (h : CommonThreshold W CW θ δU yFixed) :
    D W = CW :=
  (directBridgeOpening W CW bout hCW hδ0 hδ1 hθ0 hθ1 hbout yFixed_mem.1
    yFixed_mem.2 hX hgate h).1

/-! ## Part 4  `thm:direct-robustification`'s conclusions, from the opening -/

/-- **`thm:direct-robustification` (`10-direct-bridge.tex`, label line 35), with
its input taken through the landed opening.**

Hypotheses, in the frozen order of lines 38--56 (the constants `delta = 1/10`
and `y = 1/2 + delta = 3/5` of lines 36--37 are substituted through
`DirectBridgeOpening.yFixed`, not quantified):

* `hCW : 3 <= C_W` (line 40, second half);
* `hδ0`, `hδ1` : `0 < delta_U < 1` (line 38);
* `hθ0`, `hθ1` : `0 < theta <= 1` (line 39);
* `hbout : 1 <= b_out` (line 41);
* `hX`, `hY` : nonempty carriers (`10:102`, reader line 83);
* `hgates` : `eq:direct-entry-gates` (label line 56) as the banked frozen pair at
  the globally fixed `y = 3/5`;
* `h` : the **input**, as the banked Section-9 interface
  `FirstWrapperClose.CommonThreshold` at `yFixed` -- `W`, `C_W`, and the two
  common-threshold lower bounds of `eq:direct-input`, and nothing else.

The first half of line 40, `comp W = C_W`, is **not** a separate binder here: it
is supplied by `DirectBridgeOpening.directBridgeOpening`'s first conclusion, and
the two clauses of `eq:direct-input` are supplied by
`DirectBridgeOpening.directInput_at_fixed_y`.  Both are consumed **by pin**.

Conclusions, in the frozen print order of lines 63--74:

1. the orientation `R^+ = transpose(Int_Q(W))` of line 63, entrywise;
2. `comp R^+ = C_W + r_Q`, the first clause of `eq:direct-output` (line 67);
3. `Lambda_3(R^+, 1, 2^{-b_out}, 3/5) >= C_W + r_Q`, the second clause (lines
   69--70), with `2^{-b_out}` the banked `DirectOutputLower.xOut`;
4. the selector sentence of line 74 in its exact reading, `ceil(log_2 Q) = r_Q`
   -- an equation, not an inequality;
5. the selector sentence of line 73 in its protocol reading, with `U` an
   explicit binder as the reader writes it.

Clauses 2--5 are the banked `BridgeOutputEquality.directRobustification`,
consumed unchanged; clause 1 is `directOutputMatrix_transpose`.  **Nothing is
re-proved and nothing is strengthened.**  Nothing is claimed about the existence
of an input satisfying the hypotheses, and **no route completion is claimed**. -/
theorem directRobustification_of_opening {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {θ δU : ℝ}
    (hCW : 3 ≤ CW) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hbout : 1 ≤ bout)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hgates : directEntryGates bout δU θ (3 / 5))
    (h : CommonThreshold W CW θ δU yFixed) :
    (∀ (c : Fin (Qwidth bout δU) → Y) (r : Fin (Qwidth bout δU) × X),
        EthBridge.Rnext W (Qwidth bout δU) c r
          = interlaceFun W (Qwidth bout δU) r c)
      ∧ D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU
      ∧ CW + rQ bout δU
          ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) (3 / 5)
      ∧ Nat.clog 2 (Qwidth bout δU) = rQ bout δU
      ∧ (∀ U : ℕ, D W ≤ U →
          D (EthBridge.Rnext W (Qwidth bout δU)) ≤ U + rQ bout δU) := by
  have hgate : 4 * Q0 bout δU * θ ≤ deltaFixed := hgates.1
  have hCWeq : D W = CW :=
    opening_supplies_exactComplexity W CW bout hCW hδ0 hδ1 hθ0 hθ1 hbout hX
      hgate h
  obtain ⟨hNear, hInput⟩ := directInput_at_fixed_y h
  obtain ⟨heq, hrob, hbits, hprot⟩ :=
    directRobustification W CW bout hδ0 hδ1 hθ0 hθ1 hX hY hCWeq hCW hNear hInput
      hbout hgates
  exact ⟨directOutputMatrix_transpose W (Qwidth bout δU), heq, hrob, hbits, hprot⟩

/-! ## Part 5  General properties of the delivered conclusions -/

/-- **Aux 6 (monotone in the protocol budget).**

The selector clause of line 73 is stated for *some* cost bound `U` on `W`; it
therefore survives relaxing that bound.  Recorded as a general property of the
delivered clause rather than of any pinned parameter: the route compares two
canonical widths and two budgets, and the comparison is this monotonicity.
General. -/
theorem directOutput_selector_mono {X Y : Type*} [Fintype X] [Fintype Y]
    {W : X → Y → Bool} {bout : ℕ} {δU : ℝ} {U U' : ℕ} (hUU : U ≤ U')
    (hsel : ∀ U : ℕ, D W ≤ U →
      D (EthBridge.Rnext W (Qwidth bout δU)) ≤ U + rQ bout δU)
    (hU : D W ≤ U) :
    D (EthBridge.Rnext W (Qwidth bout δU)) ≤ U' + rQ bout δU :=
  hsel U' (le_trans hU hUU)

/-- **Aux 7 (round trip along an entrywise identification).**

`10:4` says all construction-specific information is discarded, so the bridge's
output equality is a statement about the entry function alone and transports
along a pointwise equality of matrices.  Stated at the *conclusion*, so that it
is a fact about this module's deliverable and not a restatement of any banked
congruence.  General. -/
theorem directOutput_congr {X Y : Type*} [Fintype X] [Fintype Y]
    {W₁ W₂ : X → Y → Bool} {CW bout : ℕ} {δU : ℝ} (hW : ∀ a b, W₁ a b = W₂ a b)
    (h : D (EthBridge.Rnext W₁ (Qwidth bout δU)) = CW + rQ bout δU) :
    D (EthBridge.Rnext W₂ (Qwidth bout δU)) = CW + rQ bout δU := by
  have hfun : W₁ = W₂ := funext fun a => funext fun b => hW a b
  subst hfun
  exact h

/-! ## Part 6  Statement poles

**All three** poles this module needs are **already banked declarations**, and
are therefore cited by name rather than restated (fixed-interface discipline; a
local twin of any of them would be a duplicate declaration and a stale-twin
hazard):

* the **vacuous-conclusion pole** is
  `BridgeOutputEquality.directRobustification_conclusion_nontrivial`, which
  reads `comp R^+ = C_W + r_Q >= 7` at every legal parameter from the frozen
  `C_W >= 3` (`10:40`) and the banked `EntryGates.four_le_rQ`.  Its statement
  is already exactly this module's conclusion at this module's binders --
  `W`, `C_W`, `b_out`, `delta_U` are the same universally quantified symbols --
  so nothing here would be added by repeating it;
* the **trivial-witness pole** is
  `BridgeOutputEquality.directOutput_needs_exact_complexity`: the two banked
  directions alone read in `ℕ` as `n <= d + r` and `c + r <= n` and do **not**
  determine `n`, so the interface's `exact` field -- which
  `DirectBridgeOpening.directBridgeOpening`'s first conclusion returns, and
  which `opening_supplies_exactComplexity` above identifies in the kernel -- is
  load-bearing, and a version of this module consuming only
  `directInput_at_fixed_y` would be strictly weaker than `eq:direct-output`;
* the **vacuous-hypothesis pole** is
  `DirectBridgeOpening.opening_rejects_the_wrapper_close_probe`, which refutes
  `CommonThreshold FirstWrapperClose.probeW C_W theta delta_U y` whenever
  `3 <= C_W` (`10:40`), because `FirstWrapperClose.probeW_D` pins the Section-9
  NON-FIDELITY probe's complexity at exactly `2`.  It is stated **general in
  `y`**, so it applies verbatim at this module's `y = yFixed` and at this
  module's own `3 <= C_W` binder; nothing about the exclusion is local here.

**`cc-t3f-r2` correction of record.**  The parked `cc-t3f-r1` text asserted that
a third pole was "genuinely local, because it is stated at *this* module's
hypothesis list rather than at `BRIDGE-OUTPUT-003`'s", and carried a local
`directOutput_from_opening_rejects_the_probe` on that basis.  The justification
was **false as written**: the banked pole above is stated at a strictly *more
general* hypothesis list (general in `y`, of which `yFixed` is one value), it
lives in `BRIDGE-OPENING-001` rather than in `BRIDGE-OUTPUT-003`, and this
module already imports its supplier -- so the local declaration was a verbatim
specialization with a byte-identical proof.  It was **deleted**, and no pole is
lost: all three are banked, kernel-checked, and cited above. -/

/-! ## Part 7  Parameter witnesses (no inhabitation claimed)

Both `delta_U` and `theta` are **source-defined**, not free: `eq:q-deltaU`
(`06-parameter-schedule.tex:514--519`, display line **517**) fixes
`delta_U = eta_R/(16 q)`, and
`eq:Q-theta-choice` (`06:525--538`, display line **533**) fixes
`theta = c_theta/(2Q) = delta/(16Q)` at the very `Q` of `10:47--51`.  Neither
may be given a numeral in a witness: their values are obtained by **evaluating
the defining chain**, which the banked `SCHEDULE-001` module reifies as
`ParameterSchedule.deltaU` and `ParameterSchedule.theta`.  Consequently both
entry binders of `directRobustification_of_opening` are *discharged* here rather
than assumed:

* the first gate is `eq:direct-theta-gates`, second row (`06:544`), banked as
  `ParameterSchedule.four_Q0_theta_le`;
* the frozen range `0 < theta <= 1` of `10:39` is banked as
  `ParameterSchedule.schedule_theta_in_range`, which in fact returns the
  stronger reader range `theta <= 1/4`.

The first witness below is the paper's own scheduled point and assigns **no**
numeral at all.  The second is an explicitly labelled **BEYOND-PAPER AUDIT**
instance: it pins `delta_U` at the boundary `1/200` of the paper's own finite
gate (`06:547`) purely to move the arithmetic, and audits our encoding at a
point the paper itself never instantiates.  It is strictly weaker evidence than
the first and never a substitute for it.  Neither is an inhabitation: `X`, `Y`,
`W` stay universally quantified and the input record stays a hypothesis, since
the bridge's input has no exhibited unconditional inhabitant and can have none
until `DenseRung` is discharged. -/

/-- **Non-vacuity (i): the wiring fires at the paper's own scheduled point, with
no numeral assigned to any defined quantity.**

`delta_U` and `theta` are pinned here by their **defining displays**, not by
values: `hδU` is `eq:q-deltaU` (`06:517`) and `hθ` is `eq:Q-theta-choice`
(`06:533`), each reified by the banked `SCHEDULE-001` module and each evaluated
in dependency order (`eta_C -> eta_R -> delta_U -> Q_0 -> Q -> theta`).  The
only free inputs are the ones `06:4--8` names as the public tuple and the
source graph -- the source scale `s`, the source-side scalars `delta_v(G)` and
`zeta`, the first-wrapper width `q`, and the requested depth `b_out` -- and they
stay universally quantified under their frozen legality.

Both entry binders of `directRobustification_of_opening` are then **derived**:
the gate pair from `ParameterSchedule.schedule_fires_directEntryGates`
(`eq:direct-theta-gates` second row for the first half, and the finite gate
`06:547` discharged through `ParameterSchedule.deltaU_le_gates` for the second),
and `0 < theta <= 1` from `ParameterSchedule.schedule_theta_in_range`.  The
legality `0 < delta_U < 1` is likewise read off the chain rather than assumed.
They are returned in the conclusion so that the discharge is visible, not merely
internal.

`C_W` stays a binder at the frozen floor `3 <= C_W` of `10:40`, since the
Section-9 output fixes it as `C + r` and no value may be chosen for it here.
This is a **parameter** witness, not an inhabitation. -/
theorem directOutput_from_opening_at_the_scheduled_point {X Y : Type*}
    [Fintype X] [Fintype Y] (W : X → Y → Bool) (CW bout s q : ℕ)
    {dv zeta δU θ : ℝ}
    (hCW : 3 ≤ CW) (hbout : 1 ≤ bout)
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q)
    (hδU : δU = ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) q)
    (hθ : θ = ParameterSchedule.theta (Qwidth bout δU))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (h : CommonThreshold W CW θ δU yFixed) :
    (0 < δU ∧ δU < 1) ∧ (0 < θ ∧ θ ≤ 1 / 4) ∧
      directEntryGates bout δU θ (3 / 5) ∧
      D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU ∧
      CW + rQ bout δU
          ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) (3 / 5) ∧
      Nat.clog 2 (Qwidth bout δU) = rQ bout δU := by
  subst hδU
  subst hθ
  have hδ0 : 0 < ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) q :=
    ParameterSchedule.deltaU_pos (ParameterSchedule.etaR_pos hs hdv hz) hq
  have hδ1 : ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) q < 1 :=
    ParameterSchedule.deltaU_lt_one hq
  obtain ⟨hθ0, hθ4⟩ :=
    ParameterSchedule.schedule_theta_in_range bout
      (ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) q)
  have hgates := ParameterSchedule.schedule_fires_directEntryGates
    (bout := bout) hs hdv hz hq
  obtain ⟨-, heq, hrob, hbits, -⟩ :=
    directRobustification_of_opening W CW bout hCW hδ0 hδ1 hθ0 (by linarith)
      hbout hX hY hgates h
  exact ⟨⟨hδ0, hδ1⟩, ⟨hθ0, hθ4⟩, hgates, heq, hrob, hbits⟩

/-- **Non-vacuity (ii), BEYOND-PAPER AUDIT: the wiring fires again at a
different arithmetic, with `theta` still taken from its defining display.**

**This instance is not a point the paper instantiates.**  `delta_U` is
*defined* by `eq:q-deltaU`, and pinning it at `1/200` is an assignment to a
defined quantity; the value chosen is the boundary of the paper's own finite
gate `delta_U <= 1/200` (`06:547`), so the instance is legal, but it audits
**our encoding** at a point the frozen source never visits.  It is therefore
strictly weaker evidence than
`directOutput_from_opening_at_the_scheduled_point` above and is never a
substitute for it.

`theta` is **not** given a numeral even here: it is
`ParameterSchedule.theta (Qwidth 1 (1/200))`, the defining display `06:533`
evaluated at the banked width.  At this `delta_U` the banked entry apparatus
reads `Q_0 = 16000`, `r_Q = 14`, `Q = 16384`, so the width, the canonical
exponent, the selector cost and the delivered constant all move relative to the
scheduled point -- which a hypothesis bundle satisfiable at a single arithmetic
could not do, and which is this module's consistency check on that bundle.
`C_W` stays a binder; the input record stays a hypothesis. -/
theorem directOutput_from_opening_fires_at_the_gate_boundary {X Y : Type*}
    [Fintype X] [Fintype Y] (W : X → Y → Bool) (CW : ℕ) (hCW : 3 ≤ CW)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (h : CommonThreshold W CW (ParameterSchedule.theta (Qwidth 1 (1 / 200)))
      (1 / 200) yFixed) :
    Qwidth 1 (1 / 200) = 16384 ∧ rQ 1 (1 / 200) = 14 ∧
      D (EthBridge.Rnext W (Qwidth 1 (1 / 200))) = CW + 14 ∧
      CW + 14 ≤ LambdaGE (EthBridge.Rnext W (Qwidth 1 (1 / 200))) 1
        (xOut 1) (3 / 5) ∧
      Nat.clog 2 (Qwidth 1 (1 / 200)) = 14 := by
  obtain ⟨-, hrQ, hQ, -, -, -, -⟩ := DirectOutput.directOutput_fires_second_witness
  obtain ⟨hgate4, hquarter⟩ := ParameterSchedule.four_Q0_theta_le 1 (1 / 200)
  have hgate : 4 * Q0 1 (1 / 200) *
      ParameterSchedule.theta (Qwidth 1 (1 / 200)) ≤ deltaFixed := by
    linarith
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 200) (by norm_num : (1 / 200 : ℝ) ≤ 1 / 60)
  obtain ⟨hθ0, hθ4⟩ := ParameterSchedule.schedule_theta_in_range 1 (1 / 200)
  obtain ⟨-, heq, hrob, hbits, -⟩ :=
    directRobustification_of_opening W CW 1
      (θ := ParameterSchedule.theta (Qwidth 1 (1 / 200))) (δU := 1 / 200)
      hCW (by norm_num) (by norm_num) hθ0 (by linarith) (le_refl 1)
      hX hY ⟨hgate, hmargin⟩ h
  rw [hrQ] at heq hrob hbits
  exact ⟨hQ, hrQ, heq, hrob, hbits⟩

/-! ## Part 8  Canonical inhabitation of the input, deferred

Read the module header's registered obligation before consuming this section.
The paper's own instance is the required witness, and it is delivered here
**conditionally**, exactly as its supplier delivers it. -/

/-- **Canonical inhabitation: `thm:direct-robustification` at the paper's own
entry object (`09:1794--1795` into `10:4--74`).**

The only object the paper ever hands to this bridge is the Section-9 output
`W = transpose(U)` at `C_W = C + r`.  This theorem runs the *whole* of
`thm:direct-robustification` on that object: its hypotheses are exactly the
banked `FirstWrapperClose.commonThreshold_of_firstWrapperClose`'s, plus the
Section-10 binders (`b_out >= 1` and the frozen gate pair at `y = 3/5`), and its
conclusion is `directRobustification_of_opening`'s at
`ScaleAlignOpening.wrapperW Nmat r` and `C + r`.

**Both interlace widths occur here, and they are not identified.**  The
scale-alignment width `q = 2^r` is internal to `W`, whose carriers are
`Fin (2^r) -> Cl` and `Fin (2^r) x Rw`; the outer bridge width is
`Q = Qwidth b_out delta_U = 2^{r_Q}`, and `R^+` interlaces over that.  The
carrier nonemptiness facts `1 <= |Fin (2^r) -> Cl|` and `1 <= |Fin (2^r) x Rw|`
are **derived** from `1 <= |Cl|` and `1 <= |Rw|` rather than assumed.

**Conditional, and registered as such.**  `hDense` is the named, undischarged
`FirstWrapperClose.DenseRung` (`eq:wrapper-u-dense`, `09:262--263`), and `hne`,
`hmem` are the low-rung inputs of `09:274--334`.  The unconditional form is
GAP-EXPOSED G3 of `BRIDGE-OPENING-001` and is discharged only when `DenseRung`
is proved.  Nothing here weakens, discharges, or reorients that binder, and
**no route completion is claimed**. -/
theorem directOutput_at_the_paper_instance {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Nmat : Rw → Cl → Bool) (r C bout : ℕ) {δU θ : ℝ}
    (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hbout : 1 ≤ bout)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hgates : directEntryGates bout δU θ (3 / 5))
    (hDense : FirstWrapperClose.DenseRung Nmat r C δU θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (yFixed / 2 ^ j)
        θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (yFixed / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame
          (interlaceFun (ScaleAlignOpening.wrapperU Nmat r) 1) RC.1 RC.2)) :
    D (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r) (Qwidth bout δU))
        = C + r + rQ bout δU
      ∧ C + r + rQ bout δU
          ≤ LambdaGE (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
              (Qwidth bout δU)) 1 (xOut bout) (3 / 5)
      ∧ Nat.clog 2 (Qwidth bout δU) = rQ bout δU := by
  classical
  have hIn : CommonThreshold (ScaleAlignOpening.wrapperW Nmat r) (C + r) θ δU
      yFixed :=
    FirstWrapperClose.commonThreshold_of_firstWrapperClose Nmat r C hC hN hθ0
      hθ1 (by linarith) (by linarith) yFixed_mem.1 yFixed_mem.2 hRw hCl hDense
      hne hmem
  have hClne : Nonempty Cl := Fintype.card_pos_iff.mp (by omega)
  have hRwne : Nonempty Rw := Fintype.card_pos_iff.mp (by omega)
  have hX : 1 ≤ Fintype.card (Fin (2 ^ r) → Cl) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Classical.choice hClne⟩
  have hY : 1 ≤ Fintype.card (Fin (2 ^ r) × Rw) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, Nat.one_le_two_pow⟩, Classical.choice hRwne)⟩
  obtain ⟨-, heq, hrob, hbits, -⟩ :=
    directRobustification_of_opening (ScaleAlignOpening.wrapperW Nmat r) (C + r)
      bout (by omega) hδ0 hδ1 hθ0 hθ1 hbout hX hY hgates hIn
  exact ⟨heq, hrob, hbits⟩

end EthInapproximability.ParameterizedNP.DirectOutputFromOpening
