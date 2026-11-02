import EthInapproximability.ParameterizedNP.DoubleInterlaceRecurrence
import EthInapproximability.ParameterizedNP.IteratedCanonicalChaining

/-!
# Parameterized NP route: `thm:one-level` clauses C1--C3 on the frozen trace

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ONELEVEL-THEOREM-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`).

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## What this module is, and what it is not

`ONELEVEL-001` (`OneLevelAssembly.lean`) landed clauses C1--C4 of
`thm:one-level` about the *free* term
`OneLevelCompletion.levelOutput N w_q b_out delta_U`, with abstract `Prop`
promise binders and with the four `step:L-10` bridge inputs
(`hCW`, `hNear`, `hInput`, and the entry floor) taken as **guarded binders**.

This module restates nothing of that.  It lands C1--C3 in the *frozen shape* of
`07-one-level-construction.tex:36--68`:

* the object is the frozen trace record
  `T = LevelStep(Public, Pi)` destructured exactly as
  `eq:one-level-trace-destructuring` (label line 27) prints it -- the banked
  `PublicRecords.LevelTrace` -- so `R+` is the trace field `T.Rnext` and the
  overhead is the trace field `T.H`, never a free application;
* the promise is the frozen `def:level-certificates` pair
  `PublicRecords.YesCert P` / `PublicRecords.NoCert P`, never an abstract
  `Prop`;
* the `NO` clause C3 is obtained by **consuming
  `DoubleInterlaceRecurrence.doubleInterlaceRecurrence` and
  `.doubleInterlaceRecurrence_budget` by pin**, so the four `step:L-10` bridge
  inputs are no longer assumed here: they are produced inside the Section-10
  hub, and the one input that survives is the *named* dense-rung hypothesis.

Concretely, the hypothesis surface of C3 moves from
"`comp W = C_W`, `comp[W]_{1,theta,1-delta_U} >= C_W`,
`Lambda_3(W,1,theta,3/5) >= C_W - 1` assumed" (`ONELEVEL-001`)
to "`FirstWrapperClose.DenseRung` and the two low-rung inputs assumed"
(`FIRST-WRAPPER-CLOSE-001`).  Nothing is discharged; the conditionality is
relocated to the row that owns it and is disclosed in full below.

**No route completion is claimed.**  The construction layer (Stages 1--4) and
the machine layer are unlanded; C4 is not restated here at all.

## The two **double-interlace** declarations of `ONELEVEL-OVERHEAD-001`,
consumed by pin

**Naming caution, and it is the whole point of this heading.**  Two disjoint
pairs of declarations are in play in this module and an earlier round of this
tranche described them with the same words, which is a defect this round
repairs.  The pair named *here* is
`DoubleInterlaceRecurrence.doubleInterlaceRecurrence` and
`.doubleInterlaceRecurrence_budget`; it supplies clause C3.  The **other** pair
is `IteratedCanonicalChaining.chainingStep_from_oneLevel` and
`CanonicalChain.chain_apply` of `ITERATED-CANONICAL-CHAINING-001`; it is the
Section-12 chaining, it supplies nothing to C1--C3, and it is consumed only in
Part 6 below, where the clauses are converted into the banked per-level
difference forms.  Neither pair is a spelling of the other, no declaration
belongs to both, and no sentence below may be read as claiming that consuming
one discharges the other.

Both declarations of the pair named here live in
`DoubleInterlaceRecurrence.lean` (`ONELEVEL-OVERHEAD-001`), whose
GAP-EXPOSED 3 names `ONELEVEL-001` and `STAGE4-ALIGN-001` as the owners of the
chain each of them leaves as a binder:

1. `DoubleInterlaceRecurrence.doubleInterlaceRecurrence` -- `step:L-01`
   composed with `step:L-11` (`exp:E-11-exact`, label line 763) and `step:L-14`,
   on one term: `comp R+ = C + r + r_Q`,
   `Lambda_3(R+,1,x_out,3/5) >= C + r + r_Q`, `ceil(log_2 Q) = r_Q`, and the two
   carrier equations;
2. `DoubleInterlaceRecurrence.doubleInterlaceRecurrence_budget` -- `step:L-12`
   lines 769--783, the substitution `C_W + r_Q = D + H + 1` at the banked
   `OneLevelCompletion.levelOverhead`.

**The banked C4 carrier half is cited, never restated.**  Conjuncts 4 and 5 of
`doubleInterlaceRecurrence` -- `|Rows(R+)| = (q m_N)^Q` and
`|Cols(R+)| = Q n_N^q` -- are exactly the banked
`OneLevelAssembly.oneLevelAssembly_carriers` /
`.doubleInterlaceCarriers` (`ONELEVEL-001`) and
`PublicRecords.LevelTrace.levelTrace_carrier_recurrence`, and the integer side
bounds are `OneLevelAssembly.oneLevelAssembly_sideBound`.  This module discards
those conjuncts at the point of consumption and states **no** carrier equation,
**no** `z_N`, and **no** `z+`.

## The dense estimate enters as the named `DenseRung` hypothesis

Every dense-estimate application below enters as
`FirstWrapperClose.DenseRung Nmat r C delta_U theta`
(`eq:wrapper-u-dense`, `09:262--263`), the *same named predicate* the banked
close `FirstWrapperClose.firstWrapperClose` and the banked
`DoubleInterlaceRecurrence.doubleInterlaceRecurrence` carry, with the same
argument order and the same low-rung companions `hne`, `hmem` of `09:274--334`.
Nothing is strengthened, weakened, reoriented, or discharged.

**One difference from the banked close, and it is forced.**  The banked close
has no `YES` clause, so it may carry `hN : comp N = C` and `DenseRung` as
*unguarded* binders.  This module states C2 and C3 together, and the frozen
theorem states them as two implications out of the two certificates
(`def:level-certificates`).  Carrying the `NO`-side inputs unguarded beside the
`YES` input would make C2 vacuous at every legal parameter: at the frozen
`Y <= D` of `13-iteration-assembly.tex:431` the pair
`comp N = D + K + 1` and `comp N <= Y + K` derives `False`.  That is a theorem
here, not a remark -- `denseInputs_unguarded_refute_the_yes_clause` -- and it is
why each `NO`-side input is written `NoCert P -> ...`, exactly as the banked
`OneLevelAssembly.oneLevelAssembly_no` writes its four.

## Every schedule quantity goes through the banked definitions

No new integer, width, threshold or overhead is defined in this module.  The
schedule quantities are consumed as:

* `OneLevelCompletion.levelOverhead` (`H`), `.stage4Overhead` (`K`),
  `.stage4Exact` (`C`), `.alignedExact` (`C_W`), `.noBudget_collect`,
  `.levelOutput` (`R+`), `.alignedMatrix` (`W`);
* `EntryGates.rQ` (`r_Q`), `.Qwidth` (`Q = 2^{r_Q}`), `.directEntryGates`,
  `.Qwidth_eq_two_pow`, `.directEntryGates_fires`;
* `DirectOutputLower.xOut` (`x_out = 2^{-b_out}`);
* `DirectBridgeOpening.yFixed` (`y = 3/5` at its defining chain);
* `ScaleAlignOpening.wrapperU`, `.wrapperW` (`U`, `W`);
* `GuardedSourceSlab.q2` (`q_2`), through the trace's own `H_eq` field;
* the trace's own fields `T.H`, `T.mnext`, `T.nnext` for the `T6` quantities.

The only arithmetic performed is `Nat.log_pow` at the two power-of-two widths
(the frozen "Admissibility makes `q` and `Q` positive powers of two, so their
base-two logarithms below are integers", `07:85--86`) and `omega` on linear
`Nat` goals, together with the closed-form real arithmetic of Part 5, which runs
entirely through the banked `ParameterSchedule` definitions.

## Autoformalization anchors

* `sections/07-one-level-construction.tex`, `thm:one-level` (label line 37):
  * `eq:one-level-trace-destructuring` (label line 27, display lines 18--28) --
    the 23-field destructuring, consumed as the banked `PublicRecords.LevelTrace`;
  * lines 29--31, "Assume the single predicate `Admissible(Public,Pi,T)` of
    `def:admissible-parameters`" -- the hypothesis Part 5 exhibits a legal point
    of;
  * line 43, the overhead field
    `H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`;
  * **C1**, lines 46--53 (promise independence, determinacy sentence at lines
    48--51, "Thus both implications below refer to this same matrix `R+`");
  * **C2**, lines 55--58 (`YesCert(Public) => comp R+ <= Y + H`);
  * **C3**, lines 60--67 (`NoCert(Public) => comp R+ = D + H + 1` and
    `Lambda_3(R+,1,2^{-b_out},3/5) >= D + H + 1`);
  * **C4**, lines 69--106 -- **not claimed here**, cited only.
* `sections/05-public-records.tex`: `def:level-public-input` (label line 13),
  `def:level-certificates` (label line 54, statement lines 55--73),
  `def:level-trace` (label line 220), `def:admissible-parameters` and its
  **Direct** group at lines 509--534 (the clauses `0 < delta_U <= 1/200`,
  `lambda_def = -ln(1-delta_U)`, `eq:direct-theta-gates` and
  `eq:direct-numeric-gate`, together with the explicit arithmetic implication of
  lines 519--533 whose antecedent contains `delta_U <= 1/200` and
  `4 Q_0 theta <= delta/4`), and the four-proposition proof ledger of
  lines 798--850 with its discipline sentence at line 849.
* `sections/06-parameter-schedule.tex`: `eq:q-deltaU` (label line 518, display
  lines 514--519, prose lead-in at 513) fixing `q = 2^{A_wrap L_P^2}` at line 515
  and `delta_U = eta_R/(16 q)` at line 517;
  `eq:Q-theta-choice` (label line 537, display lines 525--538, prose lead-in at
  524) fixing `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}` at lines
  529--531, `Q` = the least power of two at least `Q_0` at line 532, and
  `theta = c_theta/(2Q) = delta/(16 Q)` at line 533;
  `eq:direct-theta-gates` (label line 545, display lines 541--546, prose lead-in
  at 540) deriving `Q theta = delta/16 < delta/2` at line 542 and
  `4 Q_0 theta <= delta/4 < delta` at line 544; and the
  finite gate `delta_U <= 1/200` at line 547.
* `sections/12-iteration-specification.tex`: `eq:iterated-canonical-chaining`
  (label line 229, display lines 222--230) and the conversion paragraph at lines
  335--350 -- "The promise-independence clause C1 ... keeps the trace fixed, and
  clause C2 gives `comp R_i^+ <= Y_i + H_i = Y_{i+1}`.  Canonical-reindexing
  invariance and `eq:iterated-canonical-chaining` give the same inequality for
  `R_{i+1}`", and the `NO` sentence "The NO clause C3 gives both the exact
  equality and the depth-`b_{i+1}` certificate for `R_i^+`" with its transport.
* `sections/11-one-level-assembly.tex`: `step:L-01` (label line 20),
  `step:L-12` (label line 766, "the equality and the robustness lower bound use
  the same integer, as required in clause C3", line 784), `step:L-13`
  (label line 789, line 793 and lines 800--807).
* `sections/09-first-wrapper.tex`: `eq:wrapper-u-dense` (`09:262--263`) and the
  low-rung block `09:274--334`.
* `sections/13-iteration-assembly.tex`, `step:I-05` (label line 430, side
  conditions line 431) -- `Y_i <= D_i` and `3 <= D_i`, the legal-budget regime
  the refutation is read at.
* `sections/02-mechanical-contract.tex` lines 767--775 -- the frozen legality
  `q, Q >= 2`, carried as `hwq : 1 <= w_q`.

## Reader counterpart

**No reader item is newly claimed, and this is a disclosure rather than an
omission.**  The reader locus of C1--C3 is `cor:one-level-amplifier`
(`routes/parameterized-np/reader-facing/sections/04-bridge.tex`, label line 155,
statement lines 154--182), which was opened first-hand this tranche.  Its lines
are already partitioned, without remainder, among `ONELEVEL-001`'s four
declarations: 154--167 to `oneLevelAssembly_promiseIndependent`, line 170 to
`oneLevelAssembly_yes`, lines 171--172 to `oneLevelAssembly_no`, and the
corollary read as one aggregation to `oneLevelAssembly`; lines 177--181
(`eq:one-level-exact-carriers`) belong to `SIZE-001`.  Re-citing any of them
here would assign one reader item to two declarations, which the crosswalk
forbids, so every declaration below records `cor:one-level-amplifier` as a
**navigation locus only** and claims no reader line.  The reader's
`eq:paper-common-threshold-profile`
(`03-parameterized-construction.tex`, the three-display conclusion of clause 2
of `thm:parameterized-one-bit`) stays with `FIRST-WRAPPER-CLOSE-001`, whose
`CommonThreshold` record is its transcription; it is reached here only through
the pinned chaining declarations and is not restated.

Crosswalk row: `READER_CROSSWALK.md`, row 11 "Mechanical one-level assembly",
extended with this module as a second Lean locus carrying no additional reader
line.

## Dependencies, imports, external adapters

* Imports `DoubleInterlaceRecurrence.lean` and
  `IteratedCanonicalChaining.lean`, hence transitively `PublicRecords`,
  `OneLevelAssembly`, `OneLevelCompletion`,
  `DirectOutputFromOpening`, `DirectBridgeOpening`, `FirstWrapperClose`,
  `ScaleAlignOpening`, `ParameterSchedule`, `GuardedSourceSlab`, `EntryGates`,
  `DirectOutputLower`, `BridgeOutputEquality`, and -- through the second import
  -- `FinalOnlyDuplication`, `DepthThread`, `CommonPadding`,
  `BudgetThreadWiring`, `SizeThreadWiring`, `FixedLevelCarriers`,
  `IterationAssembly`, and `EthInapproximability.Prelude`,
  and through it `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
* `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP balanced-family
  axiom is outside this module's closure and **no opt-in ledger note is owed**.
  There is no contact with `EXPANDER-001`, which by design has no Lean
  declaration and stays an explicit named hypothesis or cited-fact field
  wherever it is needed.
* Consumed strictly **by pin**, never restated, widened or re-proved:
  * `DoubleInterlaceRecurrence.doubleInterlaceRecurrence`,
    `.doubleInterlaceRecurrence_budget`, `.levelOutput_eq_bridge_of_wrapperW`;
  * `PublicRecords.LevelTrace.levelTrace_Rnext_eq_double`,
    `.levelTrace_H_eq_levelOverhead`, `.levelTrace_tail_determined`,
    `.levelTrace_promise_free`, and `PublicRecords.LevelTrace.traceOfCase`,
    `.YesCert`, `.NoCert`, `.yesCert_not_noCert`, `.LevelPublicInput`,
    `.LevelParams`, `.LevelTrace`, `.K3`, `.paramsWitness`, `.witnessA`,
    `.witnessBase`;
  * `OneLevelCompletion.oneLevelCompletion_yes`, `.noBudget_collect`,
    `.levelOverhead`, `.stage4Overhead`, `.stage4Exact`, `.alignedExact`,
    `.levelOutput`, `.oneLevelCompletion_conclusion_nontrivial`;
  * `OneLevelAssembly.PromiseCase`,
    `.unguardedJoin_refuted_at_legal_budgets`, `.promiseFreedom_not_automatic`;
  * `FirstWrapperClose.DenseRung`, `.denseRung_not_automatic`;
  * `EntryGates.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`, `.directEntryGates`,
    `.directEntryGates_fires`, `.Q0`, `.deltaFixed`, `.deltaFixed_eq`,
    `.secondEntryGate_of_deltaU_small`;
  * `ParameterSchedule.etaR`, `.etaR_pos`, `.qWrap`, `.qWrap_pos`,
    `.qWrap_eq_two_pow`, `.deltaU`, `.deltaU_pos`, `.deltaU_le_gates`,
    `.deltaU_lt_one`, `.theta`, `.four_Q0_theta_le`,
    `.schedule_theta_in_range`;
    **overlap disclosed, not consumed:** `.schedule_fires_directEntryGates`
    (`ParameterSchedule.lean:1678--1688`) already proves the fifth conjunct of
    `admissibleDirectGroup_at_the_schedule_point` -- `directEntryGates b_out
    (deltaU (etaR s d_V zeta) q) (theta (Qwidth b_out .)) (3/5)` -- from
    `3 < s`, `0 < d_V`, `0 < zeta`, `0 < q`, by the same two banked steps
    (`secondEntryGate_of_deltaU_small` and `four_Q0_theta_le`) used here.  At
    `q := qWrap A_wrap L_P` that is exactly conjunct 5, which Part 5 re-derives
    through `directEntryGates_of_admissibleDirect` instead of consuming.  The
    redundancy is recorded rather than removed: routing the proof through the
    banked twin would be a proof change, and none is authorized in a repair
    round.  The other four conjuncts are new, and
    `directEntryGates_of_admissibleDirect` is new frozen content (the general
    form of the `05:519--533` coverage map), so nothing here restates a banked
    theorem.  The banked consistency probe `.scheduledPoint_hypotheses_consistent`
    (`:1752--1767`) is the on-tree analogue of Part 5's non-vacuity check;
  * `IteratedCanonicalChaining.CanonicalChain`, `.chain_apply`,
    `.chainingStep_from_oneLevel`, `.Can`, `.canonEquiv`, `.reindex`,
    `.reindex_complexity`, and `FixedLevelCarriers.LevelCarrierSpec` with its
    accessors `qExp`, `bout`, `dU`, `mN`, `nN`, `rowCarrier`, `colCarrier`;
  * `DirectOutputLower.xOut`; `DirectBridgeOpening.yFixed`;
  * `ScaleAlignOpening.wrapperU`; `GuardedSourceSlab.q2`, `.slotEmbed`;
  * the vendored `EthBridge.Rnext`, reached only through the banked lemmas.
* External theorem adapters: **none new**.
* Proof status: **new (elementary)** throughout -- guarded application of
  banked kernel-checked route facades plus linear `Nat` arithmetic.  Nothing is
  axiomatized; there is no opaque certificate and no unproved placeholder of
  either kind the release gate scans for.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Conditional statuses of the consumed chain, disclosed exactly

Every conditionality below is **inherited**; this module introduces none and
improves none.

1. **`FIRST-WRAPPER-CLOSE-001`.**  C3 runs under the named, undischarged
   `FirstWrapperClose.DenseRung` (`eq:wrapper-u-dense`, `09:262--263`), exactly
   as its supplier `DoubleInterlaceRecurrence.doubleInterlaceRecurrence` does
   and to exactly the same degree.  The unconditional form is GAP-EXPOSED G3 of
   `BRIDGE-OPENING-001`.
2. **The low-rung inputs.**  `hne`, `hmem` of `09:274--334`, which
   `FirstWrapperClose.commonThreshold_of_firstWrapperClose` takes as explicit
   binders rather than proving, travel verbatim.
3. **`TERMINAL-TWO-STREAM-001`** is landed as a **stated** claim, not a proved
   theorem, and is not invoked anywhere below; it reaches this module only as
   part of the `FIRST-WRAPPER-CLOSE-001` chain's recorded status.  Likewise
   `DENSE-WRAPPER-FRONTIER-001`, `WRAPPER-PROTECTED-EARLY-001` and
   `WRAPPER-MASS-REDISTRIBUTION-001` (the last with four GAP-EXPOSED items and
   its own deferred canonical-inhabitation obligation on record).
4. **`BRIDGE-OUTPUT-002`/`-003`/`-004`** keep their own GAP-EXPOSED items,
   including `-003`'s item 1 (`eq:direct-input` has no exhibited unconditional
   inhabitant in Lean).
5. **`ONELEVEL-001`, `ONELEVEL-OVERHEAD-001`, `SIZE-001`** keep theirs; in
   particular the uniform majorant `exp:E-14-raw` (label line 850) is not
   proved anywhere here.
6. **`PublicRecords`' own disclosure travels unchanged**: the `NO` certificate's
   complexity half is the route's robust-seed reading, still Lean pending, and
   `NoCert P` is therefore stated faithfully and **never witnessed** below.
7. **C2 carries its own undischarged input, and it is disclosed here rather than
   only in a docstring.**  `hYesInput : YesCert P -> comp N <= Y + K` is the
   frozen Stage-4 `YES` line `11-one-level-assembly.tex:793`; no declaration in
   this repository derives it, so C2 -- and every corollary of C2 below,
   including `oneLevelTheorem_C2_fires_at_the_probe` and the two Part-6
   wirings -- is conditional on it to exactly the degree C3 is conditional on
   `hStage4`.  It is GAP-EXPOSED 1 together with `hStage4`, and its owner is the
   same unlanded Stage-1--4 chain.
8. **`ITERATED-CANONICAL-CHAINING-001`** keeps its GAP-EXPOSED 1 (the bracket
   half of `lem:canonical-reindexing-invariance`, `12:146--165`), 2 (the
   recursive canonical orders), 3 (canonical inhabitation of `CanonicalChain`),
   5 and 6 unchanged.  Only its GAP-EXPOSED **4** -- "turning the frozen
   certificate-guarded clauses into those differences needs `thm:one-level`
   C1--C3 in Lean" -- is addressed, by Part 6, and it is addressed as a
   *conversion*, not as a discharge: the difference forms Part 6 delivers inherit
   every guard C2 and C3 carry.

## GAP-EXPOSED

1. **Both Stage-4 promise inputs are guarded binders, not derivations.**  C3
   takes `hStage4 : NoCert P -> comp N = stage4Exact D a (log_2 q_2) (log_2 s)`
   and C2 takes `hYesInput : YesCert P -> comp N <= Y + stage4Overhead a
   (log_2 q_2) (log_2 s)`, the frozen `YES` line
   `11-one-level-assembly.tex:793`.  **Neither** is derived anywhere in this
   repository, and the two are named together here so that no reader of this
   list takes C2 to be unconditional.  The chain producing them from the promise
   certificates through Stages 1--4 is `ONELEVEL-001`, `STAGE4-RAW-001`,
   `STAGE4-PROTECTED-001` and `STAGE4-ALIGN-001`, none of which is discharged
   here.  The **deferred range**
   is `08-dense-stage4.tex:1--256` together with `09-first-wrapper.tex:1--273`.
2. **The dense rung is a guarded binder.**  As in conditional status 1; the
   **deferred range** is `09-first-wrapper.tex:262--334`
   (`eq:wrapper-u-dense` and `sec:wrapper-low-rungs`).
3. **C1's congruence half is stated at the trace, not at a Lean `LevelStep`
   function.**  The frozen sentence "the trace `T` ... is determined by
   `(Public, Pi)` alone" is transcribed as: two traces over the same protected
   duplicate at the same widths have the same `R+`, `H`, `m_next` and `n_next`.
   A total Lean constructor `LevelStep(Public, Pi)` would need the whole
   construction layer; that is `PARAM-001`'s
   `06-parameter-schedule.tex:1--2273`, and the **deferred range** is that
   section in full.  Nothing below asserts the existence of such a constructor.
4. **Canonical inhabitation of C3's guarded bundle is deferred and REGISTERED.**
   The paper's own trace at the route's own Stage-4 output cannot be exhibited
   until GAP-EXPOSED 1 and 2 land.  What is landed instead is
   `bridgeWidthTrace`, an explicitly labelled **NON-FIDELITY** probe: a
   nondegenerate `LevelTrace` at the frozen-legal widths `q = 2^1` and
   `Q = Qwidth b_out delta_U`, which shows the *unguarded* width constraints of
   C2 and C3 are jointly satisfiable by a real trace and nothing more.  It never
   satisfies, and is never used to satisfy, the guarded inputs.  The deferred
   canonical-inhabitation obligation is recorded in the ledger row and is
   discharged only when the construction layer lands.
5. **The chain that Part 6 converts along is a binder, not a construction.**
   `chainedLevel_differenceForms` takes a `CanonicalChain S` and the two
   equivalences identifying its level-`i` output carriers with the trace's; it
   does **not** build the chain whose `out i` is the route's own level output.
   That construction is `ITERATED-CANONICAL-CHAINING-001`'s own GAP-EXPOSED 3
   (canonical inhabitation of `CanonicalChain`, REGISTERED as deferred there),
   which needs Stages 1--4; the **deferred range** is
   `12-iteration-specification.tex:222--230` read at the route's own instance.
   Nothing in Part 6 exhibits such a chain, and `chainedSuccessor_differenceForms`
   is the strictly weaker statement that avoids the binder by working at the
   canonical successor `Can(R+)` directly, where the two cardinality proofs are
   supplied by the banked `chainingStep_from_oneLevel` rather than assumed.

## What round `r1` adds, and what it does not

Part 5 and Part 6 are new; Parts 0--4 are the judged round-`r0` content,
unchanged in statement and proof, with citation repairs in docstrings only.

* **Part 5** answers the question round `r0` left open: `thm:one-level` assumes
  `Admissible(Public,Pi,T)` (`07:29--31`), whose **Direct** group is printed at
  `05:509--534`, and the only parameter point round `r0` exhibited --
  `EntryGates.directEntryGates_fires`' `(b_out, delta_U, theta) = (1, 1/60,
  1/192000)` -- satisfies `eq:direct-entry-gates` but **violates** that group on
  both of its arithmetic clauses.  `entryGatePoint_is_not_admissible` records
  that violation in the kernel rather than in prose, and
  `admissibleDirectGroup_at_the_schedule_point` exhibits a point that *does*
  satisfy the group, obtained by **evaluating the frozen definitional chain**
  `eq:q-deltaU` -> `eq:Q-theta-choice` -> `eq:direct-theta-gates` in dependency
  order through the banked `ParameterSchedule` definitions.  No numeral is
  assigned to any quantity the frozen source defines: `q` is `qWrap A_wrap L_P`,
  `delta_U` is `deltaU (etaR s dv zeta) q`, `theta` is `theta (Qwidth b_out
  delta_U)`, and the three gate facts are the banked `deltaU_le_gates`,
  `schedule_theta_in_range` and `four_Q0_theta_le` consumed by pin.
* **Part 6** converts the certificate-guarded clauses into the *banked
  difference forms* the Section-12 folds consume, which is exactly
  `ITERATED-CANONICAL-CHAINING-001`'s GAP-EXPOSED 4.  It consumes
  `IteratedCanonicalChaining.chainingStep_from_oneLevel` and
  `CanonicalChain.chain_apply` **by pin**, in proof terms, and re-proves neither.
* **Not added:** no clause C4, no carrier equation, no bracket statement, no
  discharge of any guard, and no route completion.  Every conditionality listed
  above travels into Parts 5 and 6 unchanged.
-/

set_option linter.unusedVariables false

namespace EthInapproximability.ParameterizedNP.OneLevelTheorem

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.PublicRecords

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

section Trace

variable {G : EndpointGraph V E} {s : ℕ} {X₁ : Type*}
  {Pr : LevelParams X₁ (q2 G s)}
  {C₁ RB CB RA CA : Type*}
  [Fintype X₁] [Fintype C₁]
  [Fintype RB] [Fintype CB] [Fintype RA] [Fintype CA]

/-! ## Part 0: the aux-lemma battery

Aux 1--5, the five general properties Parts 1--4 are proved through.  The
module's aux battery is **8/8**: Aux 6 (`qWrap_exponent_legal`) and Aux 7
(`directEntryGates_of_admissibleDirect`) are stated in Part 5 and Aux 8
(`chainedLevel_separates_of_output_separates`) in Part 6, each beside the
declaration it serves.

None is about a pinned instance: each quantifies over
an arbitrary trace, arbitrary carriers, and arbitrary exponents.  Aux 2 and
aux 3 are the two identifications every clause below is proved through, so an
unprovable one would immediately disqualify the encoding. -/

/-- **Aux 1 (the entry floor survives Stage 4).**

`P4` of `def:level-public-input` fixes `D >= 3`
(`05-public-records.tex`, and `step:I-05`'s side condition
`13-iteration-assembly.tex:431`), and the chaining declaration below needs
`3 <= C` at the Stage-4 exact value `C = D + K + 1` of `10-direct-bridge.tex:507`.
Monotonicity/floor property, general in all four numbers; no trace, no carrier
and no promise occurs.

Reader locus: none (this is an arithmetic property of the banked
`OneLevelCompletion.stage4Exact`, not a transcription of a reader statement). -/
theorem three_le_stage4Exact {Dsrc a w2 ws : ℕ} (hD : 3 ≤ Dsrc) :
    3 ≤ stage4Exact Dsrc a w2 ws := by
  unfold stage4Exact stage4Overhead
  omega

/-- **Aux 2 (the trace's `R+` is the banked level output).**

`step:L-01` (`11-one-level-assembly.tex`, label line 20) and `T3` of
`def:level-trace`: `U = Int_q(N)`, `W = U^T`, `R+ = Int_Q(W)^T`.  At the
frozen-legal widths `q = 2^{w_q}` and `Q = Qwidth b_out delta_U` the trace field
`T.Rnext` **is** the banked `OneLevelCompletion.levelOutput` at the trace's own
protected transpose `T.N`.

Round-trip identity into the banked bridge layer, general in the trace, the nine
carriers, `a`, `w_q`, `b_out` and `delta_U`.  Purely the banked
`PublicRecords.LevelTrace.levelTrace_Rnext_eq_double`; nothing is re-proved.

Reader locus (navigation only, not claimed): `cor:one-level-amplifier`
`04-bridge.tex:163--166`, carried by `ONELEVEL-001`. -/
theorem traceOutput_eq_levelOutput {a wq bout : ℕ} {δU : ℝ}
    (T : LevelTrace G s Pr C₁ RB CB RA CA a (2 ^ wq)
      (Qwidth bout δU)) :
    T.Rnext = levelOutput T.N wq bout δU := by
  rw [LevelTrace.levelTrace_Rnext_eq_double]
  rfl

/-- **Aux 3 (the trace's overhead field is the banked `levelOverhead`).**

`T6` of `def:level-trace` stores `H = a + log_2 q_2 + log_2 s + log_2 q +
log_2 Q`, which is line 43 of `thm:one-level`.  At the frozen-legal widths the
two interlace logarithms are exact -- "Admissibility makes `q` and `Q` positive
powers of two, so their base-two logarithms below are integers"
(`07-one-level-construction.tex:85--86`) -- so `T.H` is the banked
`OneLevelCompletion.levelOverhead` at the five exponents, with `log_2 q = w_q`
and `log_2 Q = r_Q` in **distinct** summands.

Identity property, general in the trace and all five exponents.  Consumes the
banked `PublicRecords.LevelTrace.levelTrace_H_eq_levelOverhead` and
`EntryGates.Qwidth_eq_two_pow` by pin.

Reader locus (navigation only, not claimed): the `H` display of
`cor:one-level-amplifier`, `04-bridge.tex:156--161`, carried by
`ONELEVEL-001`. -/
theorem traceOverhead_eq {a wq bout : ℕ} {δU : ℝ}
    (T : LevelTrace G s Pr C₁ RB CB RA CA a (2 ^ wq)
      (Qwidth bout δU)) :
    T.H = levelOverhead a (Nat.log 2 (q2 G s)) (Nat.log 2 s) wq (rQ bout δU) := by
  rw [LevelTrace.levelTrace_H_eq_levelOverhead, Qwidth_eq_two_pow,
    Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]

/-- **Aux 4 (a supplied promise branch leaves the output and the overhead
alone).**

The "in particular" sentence of C1 (`07-one-level-construction.tex:50--53`;
`05-public-records.tex:809--811`) read at the two fields the other two clauses
speak about, and then identified with the banked level output of aux 2.  General
in the trace, the branch labels and all four numeric parameters.

What makes this content rather than notation is the banked
`OneLevelAssembly.promiseFreedom_not_automatic`: a function of `PromiseCase`
need **not** be constant.

Reader locus (navigation only, not claimed): `04-bridge.tex:162--167`, carried
by `ONELEVEL-001`. -/
theorem traceOutput_promise_free {a wq bout : ℕ} {δU : ℝ}
    (T : LevelTrace G s Pr C₁ RB CB RA CA a (2 ^ wq)
      (Qwidth bout δU)) (c c' : OneLevelAssembly.PromiseCase) :
    (LevelTrace.traceOfCase T c).Rnext = levelOutput T.N wq bout δU ∧
      (LevelTrace.traceOfCase T c).H = (LevelTrace.traceOfCase T c').H := by
  refine ⟨?_, ?_⟩
  · rw [show LevelTrace.traceOfCase T c = T from LevelTrace.levelTrace_promise_free T c c]
    exact traceOutput_eq_levelOutput T
  · rw [LevelTrace.levelTrace_promise_free T c c']

/-- **Aux 5 (the one-bit gap between the two clauses, at one trace).**

`10-direct-bridge.tex:543--563` and `step:L-12`/`step:L-13`: the `YES` budget
`Y + H` and the `NO` value `D + H + 1` differ, and under the frozen
`Y <= D` of `13-iteration-assembly.tex:431` the `YES` budget is **strictly**
smaller.  Ordering property, general in the trace and in `Y`, `D`.

This is what stops C2 and C3 from being two spellings of one inequality: they
are separated by exactly the single bit the increment table carries.

Reader locus (navigation only, not claimed): `eq:one-level-amplifier-conclusion`,
`04-bridge.tex:168--175`, carried by `ONELEVEL-001`. -/
theorem oneLevelBudgets_one_bit_gap {a q Q : ℕ}
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (P : LevelPublicInput V E) (hYD : P.Y ≤ P.D) :
    P.Y + T.H < P.D + T.H + 1 := by omega

/-! ## Part 1: clauses C1--C3 of `thm:one-level`, in the frozen shape

Three separate declarations, as `05-public-records.tex:801--802` prints them
("the proof ledger contains the following four separate propositions about that
one output"), aggregated in Part 2 per line 849.  **C4 is absent by design**:
the carrier equations and the integer side bounds are the banked
`OneLevelAssembly.oneLevelAssembly_carriers` / `.oneLevelAssembly_sideBound` and
`PublicRecords.LevelTrace.levelTrace_carrier_recurrence`, cited above and never
restated. -/

/-- **C1 -- promise independence, at the frozen trace**
(`07-one-level-construction.tex:46--53`; `05-public-records.tex:804--811`;
`step:L-01`, label line 20).

Both halves of the frozen clause, at the trace record:

* the determinacy half of lines 47--50, "The trace `T`, including `R+`, its row
  and column carriers, and every auxiliary matrix and map displayed in
  `eq:one-level-trace-destructuring`, is determined by `(Public, Pi)` alone":
  transcribed as -- two traces at the same widths over the same protected
  duplicate `A` agree on `R+`, on the overhead field `H`, and on **both**
  carrier counts `m_next`, `n_next`.  The tail equality is the banked
  `PublicRecords.LevelTrace.levelTrace_tail_determined`, consumed by pin; what
  is new is that it propagates to the three `T6` fields.  See GAP-EXPOSED 3 for
  why this is the trace-level and not a `LevelStep`-level statement;
* the "in particular" half of lines 50--53: a supplied promise branch changes
  nothing, so "both implications below refer to this same matrix `R+`".

`m_next = |Rows(R+)|` and `n_next = |Cols(R+)|` are the `T6` field equations,
**not** clause C4: no `(q m_N)^Q`, no `Q n_N^q`, no `z_N` and no `z+` occurs.

Reader locus (navigation only, not claimed): `04-bridge.tex:154--167`, carried
by `OneLevelAssembly.oneLevelAssembly_promiseIndependent`. -/
theorem oneLevelTheorem_C1 {a q Q : ℕ}
    (T T' : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (hA : T.A = T'.A) :
    (T.Rnext = T'.Rnext ∧ T.H = T'.H ∧ T.mnext = T'.mnext ∧
        T.nnext = T'.nnext) ∧
      ∀ c c' : OneLevelAssembly.PromiseCase,
        LevelTrace.traceOfCase T c = LevelTrace.traceOfCase T c' := by
  obtain ⟨-, -, -, hR⟩ := LevelTrace.levelTrace_tail_determined T T' hA
  refine ⟨⟨hR, ?_, ?_, ?_⟩, fun c c' => LevelTrace.levelTrace_promise_free T c c'⟩
  · rw [T.H_eq, T'.H_eq]
  · rw [T.mnext_eq, T'.mnext_eq, hR]
  · rw [T.nnext_eq, T'.nnext_eq, hR]

end Trace

/-! ## Part 1b: the two promise clauses, at a trace over the public input's own
guarded source

`thm:one-level` reads `T = LevelStep(Public, Pi)`, so the trace's guarded source
is built from `Public`'s own ordered multigraph.  From here on the trace is
therefore typed at `P.G`, and the two Stage-4 exponents `log_2 q_2` and
`log_2 s` in the overhead are read at that same graph.  Nothing else changes. -/

section AtPublicInput

variable (P : LevelPublicInput V E)

variable {s : ℕ} {X₁ : Type*}
  {Pr : LevelParams X₁ (q2 P.G s)}
  {C₁ RB CB RA CA : Type*}
  [Fintype X₁] [Fintype C₁]
  [Fintype RB] [Fintype CB] [Fintype RA] [Fintype CA]

/-- **C2 -- the `YES` upper bound, at the frozen trace**
(`07-one-level-construction.tex:55--58`; `05-public-records.tex:812--813`;
`step:L-13`, label line 789).

`YesCert(Public) => comp R+ <= Y + H`, with `R+ = T.Rnext` and `H = T.H` the
trace's own fields and `Y = P.Y` the public input's own `P4` budget.

The single guarded input is the frozen Stage-4 `YES` line 793,
`comp N <= Y + a + log_2 q_2 + log_2 s`, i.e. the banked
`OneLevelCompletion.stage4Overhead` at the trace's own exponents.  Lines 800--807
record that the `YES` argument "uses only `comp R <= Y` and source feasibility;
it does not use an exact value for `comp R` or any robustness certificate", so
**no** lower-bound binder, **no** robustness binder, **no** dense rung and **no**
carrier binder appears here, and `P.D` does not occur -- which is why this
statement cannot constrain the pair `(D, Y)` and cannot contradict `Y <= D`.

Proved by pin from `OneLevelCompletion.oneLevelCompletion_yes` after the two
identifications of aux 2 and aux 3.  `w_q` is free: the frozen legality
`q = 2^{w_q} >= 2` is not needed for the `YES` direction and is therefore not
demanded.

Reader locus (navigation only, not claimed): `04-bridge.tex:170`, carried by
`OneLevelAssembly.oneLevelAssembly_yes`. -/
theorem oneLevelTheorem_C2 {a q Q wq : ℕ} {δU : ℝ}
    (T : LevelTrace P.G s Pr C₁ RB CB RA CA a q Q)
    (hqpow : q = 2 ^ wq) (hQpow : Q = Qwidth P.bout δU)
    (hYesInput : YesCert P →
      D T.N ≤ P.Y + stage4Overhead a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s)) :
    YesCert P → D T.Rnext ≤ P.Y + T.H := by
  subst hqpow
  subst hQpow
  intro hc
  rw [traceOutput_eq_levelOutput T, traceOverhead_eq T]
  exact oneLevelCompletion_yes T.N P.Y a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) wq
    P.bout (hYesInput hc)

/-- **C3 -- exact `NO` bound and robust re-entry, at the frozen trace, through
the two `ONELEVEL`-wired chaining declarations**
(`07-one-level-construction.tex:60--67`; `05-public-records.tex:814--822`;
`step:L-12`, label line 766).

`NoCert(Public) => (comp R+ = D + H + 1 and
Lambda_3(R+, 1, 2^{-b_out}, 3/5) >= D + H + 1)`, at the **one** integer
`D + H + 1` -- the content of line 784, "the equality and the robustness lower
bound use the same integer, as required in clause C3".  Both conclusions are
about the same trace field `T.Rnext` and the same trace field `T.H`.

**What is consumed, and what is therefore no longer assumed.**  The `NO`
budget and the regenerated robustness certificate come from
`DoubleInterlaceRecurrence.doubleInterlaceRecurrence` and
`.doubleInterlaceRecurrence_budget`, applied once, in that order.  Consequently
the four `step:L-10` bridge inputs that `OneLevelAssembly.oneLevelAssembly_no`
takes as binders (`comp W = C_W`, the near-family bound, the `Lambda` input, and
the entry floor) are **not** hypotheses here: the first three are produced
inside the Section-10 hub and the fourth is derived from `P4`'s `D >= 3` by
aux 1.  Conjuncts 4 and 5 of the chaining declaration -- the C4 carrier
equations -- are **discarded at the point of consumption** and nothing about
carriers is stated.

**The guarded inputs, and why they are guarded.**  All four `NO`-side inputs
carry the frozen certificate as a guard:

* `hStage4` -- the Stage-4 exact value `comp N = C = D + K + 1`
  (`10-direct-bridge.tex:507`, `08-dense-stage4.tex:149`), GAP-EXPOSED 1;
* `hDense` -- the **named** `FirstWrapperClose.DenseRung`
  (`eq:wrapper-u-dense`, `09:262--263`) at the same argument order the banked
  close carries it in, GAP-EXPOSED 2;
* `hne`, `hmem` -- the low-rung inputs of `09:274--334`, verbatim.

Guarding is forced, not stylistic: `denseInputs_unguarded_refute_the_yes_clause`
shows that carrying `hStage4` unguarded beside C2's `YES` input derives `False`
at the frozen `Y <= D`.  The unguarded binders are the structural legality facts
of `thm:direct-robustification` (`10-direct-bridge.tex:38--41,53--56`) plus the
frozen inner-width legality `hwq : 1 <= w_q`
(`02-mechanical-contract.tex:771--775`), all of which are promise-free public
data; `P.Y` does not occur.

Reader locus (navigation only, not claimed): `04-bridge.tex:171--172`, carried
by `OneLevelAssembly.oneLevelAssembly_no`. -/
theorem oneLevelTheorem_C3 {a q Q wq : ℕ} {δU θ : ℝ}
    (T : LevelTrace P.G s Pr C₁ RB CB RA CA a q Q)
    (hqpow : q = 2 ^ wq) (hQpow : Q = Qwidth P.bout δU) (hwq : 1 ≤ wq)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hCA : 1 ≤ Fintype.card CA) (hRA : 1 ≤ Fintype.card RA)
    (hgates : directEntryGates P.bout δU θ (3 / 5))
    (hStage4 : NoCert P →
      D T.N = stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s))
    (hDense : NoCert P →
      FirstWrapperClose.DenseRung T.N wq
        (stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s)) δU θ)
    (hne : NoCert P → ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ wq) × CA) (Fin (2 ^ wq) → RA) 1
        (DirectBridgeOpening.yFixed / 2 ^ j) θ).Nonempty)
    (hmem : NoCert P → ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ wq) × CA) (Fin (2 ^ wq) → RA) 1
        (DirectBridgeOpening.yFixed / 2 ^ j) θ,
        stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) + wq
          ≤ j + 1 + D (subgame
              (interlaceFun (ScaleAlignOpening.wrapperU T.N wq) 1) RC.1 RC.2)) :
    NoCert P →
      D T.Rnext = P.D + T.H + 1 ∧
        P.D + T.H + 1 ≤ LambdaGE T.Rnext 1 (xOut P.bout) ((3 : ℝ) / 5) := by
  subst hqpow
  subst hQpow
  intro hc
  have hC : 3 ≤ stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) :=
    three_le_stage4Exact P.Dge
  obtain ⟨heq, hrob, -, -, -⟩ :=
    DoubleInterlaceRecurrence.doubleInterlaceRecurrence T.N wq
      (stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s)) P.bout hwq hC
      (hStage4 hc) hθ0 hθ1 hδ0 hδ1 P.boutpos hCA hRA hgates (hDense hc)
      (hne hc) (hmem hc)
  have hbudget :=
    DoubleInterlaceRecurrence.doubleInterlaceRecurrence_budget
      (Nmat := T.N) (r := wq)
      (C := stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s))
      (bout := P.bout) (δU := δU) P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s)
      rfl heq
  have hcollect :=
    noBudget_collect P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) wq (rQ P.bout δU)
  have haligned : alignedExact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) wq
      = stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) + wq := rfl
  have hsame : stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) + wq
      + rQ P.bout δU
      = P.D + levelOverhead a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) wq
          (rQ P.bout δU) + 1 := by
    omega
  rw [traceOutput_eq_levelOutput T, traceOverhead_eq T]
  refine ⟨hbudget, ?_⟩
  rw [← hsame]
  exact hrob

/-! ## Part 2: the aggregated clauses C1--C3 about one trace -/

/-- **`thm:one-level`, clauses C1--C3, aggregated at one trace**
(`07-one-level-construction.tex`, label line 37; the proof-ledger discipline of
`05-public-records.tex:849`, "Only after C1--C4 have been proved for the same
output is the aggregated one-level theorem invoked").

The three conclusions are C1's "in particular" sentence, C2 and C3, **all about
the single trace `T`, its single output field `T.Rnext`, and its single overhead
field `T.H`** -- which is the formal content of "the same output".

**This is the C1--C3 aggregate and is explicitly not the frozen aggregate.**
Line 849 licenses the aggregated one-level theorem only after **C1--C4**; C4 is
banked separately (`OneLevelAssembly.oneLevelAssembly_carriers`,
`.oneLevelAssembly_sideBound`, `PublicRecords.LevelTrace
.levelTrace_carrier_recurrence`) and is cited, not restated, so this declaration
is named for what it contains.  **No route completion is claimed.**

**The promise is the only join.**  The `YES` input is guarded by `YesCert P` and
the four `NO` inputs by `NoCert P`, so no hypothesis asserts both cases; the
banked `PublicRecords.yesCert_not_noCert` records that they are never
simultaneously satisfiable, and
`denseInputs_unguarded_refute_the_yes_clause` records that dropping the `NO`
guard collapses C2.

Reader locus (navigation only, not claimed): `cor:one-level-amplifier` read as
one aggregation, `04-bridge.tex:154--182`, carried by
`OneLevelAssembly.oneLevelAssembly`. -/
theorem oneLevelTheorem_C1_C3 {a q Q wq : ℕ} {δU θ : ℝ}
    (T : LevelTrace P.G s Pr C₁ RB CB RA CA a q Q)
    (hqpow : q = 2 ^ wq) (hQpow : Q = Qwidth P.bout δU) (hwq : 1 ≤ wq)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hCA : 1 ≤ Fintype.card CA) (hRA : 1 ≤ Fintype.card RA)
    (hgates : directEntryGates P.bout δU θ (3 / 5))
    (hYesInput : YesCert P →
      D T.N ≤ P.Y + stage4Overhead a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s))
    (hStage4 : NoCert P →
      D T.N = stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s))
    (hDense : NoCert P →
      FirstWrapperClose.DenseRung T.N wq
        (stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s)) δU θ)
    (hne : NoCert P → ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ wq) × CA) (Fin (2 ^ wq) → RA) 1
        (DirectBridgeOpening.yFixed / 2 ^ j) θ).Nonempty)
    (hmem : NoCert P → ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ wq) × CA) (Fin (2 ^ wq) → RA) 1
        (DirectBridgeOpening.yFixed / 2 ^ j) θ,
        stage4Exact P.D a (Nat.log 2 (q2 P.G s)) (Nat.log 2 s) + wq
          ≤ j + 1 + D (subgame
              (interlaceFun (ScaleAlignOpening.wrapperU T.N wq) 1) RC.1 RC.2)) :
    (∀ c c' : OneLevelAssembly.PromiseCase,
        LevelTrace.traceOfCase T c = LevelTrace.traceOfCase T c') ∧
      (YesCert P → D T.Rnext ≤ P.Y + T.H) ∧
      (NoCert P → D T.Rnext = P.D + T.H + 1 ∧
        P.D + T.H + 1 ≤ LambdaGE T.Rnext 1 (xOut P.bout) ((3 : ℝ) / 5)) :=
  ⟨fun c c' => LevelTrace.levelTrace_promise_free T c c',
    oneLevelTheorem_C2 P T hqpow hQpow hYesInput,
    oneLevelTheorem_C3 P T hqpow hQpow hwq hθ0 hθ1 hδ0 hδ1 hCA hRA hgates
      hStage4 hDense hne hmem⟩

end AtPublicInput

/-! ## Part 3: statement poles

One new pole, and two banked ones cited by name rather than restated (a local
twin would be a duplicate declaration and a stale-twin hazard):

* the **vacuous-conclusion pole** is
  `OneLevelCompletion.oneLevelCompletion_conclusion_nontrivial`, which reads the
  delivered `NO` value as at least `D + 1` and at least `5` at every legal
  parameter tuple, so C3's conclusion is never the free `0`;
* the **unguarded-conclusion pole** is
  `OneLevelAssembly.unguardedJoin_refuted_at_legal_budgets`, which refutes the
  two *conclusions* taken unguarded at `Y <= D`.

The new pole below is about the *input* layer instead, which is what this module
changed, and it is what forces every `NO`-side binder of Part 1 to be
guarded. -/

/-- **Pole: the `NO`-side inputs cannot be carried unguarded beside C2.**

The banked close `FirstWrapperClose.firstWrapperClose` and the banked
`DoubleInterlaceRecurrence.doubleInterlaceRecurrence` carry `comp N = C` and
`DenseRung` as unguarded binders, and may do so because neither states a `YES`
clause.  Part 1 states C2 and C3 together, and this theorem is why the `NO`-side
binders must then be guarded by `NoCert P`.

Taking the Stage-4 exact value `comp N = D + K + 1`
(`10-direct-bridge.tex:507`) and the Stage-4 `YES` input `comp N <= Y + K`
(`11-one-level-assembly.tex:793`) on the same matrix at once, at the frozen side
condition `Y <= D` of `13-iteration-assembly.tex:431` (`step:I-05`), derives
`False`.  So an unguarded transcription would make C2 a theorem about the empty
parameter set while every gate stayed green.

General in the matrix, both carriers and all five integers; the `+ 1` that
carries the contradiction is the raw Stage-4 one-bit gap and nothing else.

Reader locus: none -- this is an interface refutation, not a transcription of a
reader statement. -/
theorem denseInputs_unguarded_refute_the_yes_clause {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) {Dsrc Ysrc a w2 ws : ℕ}
    (hYD : Ysrc ≤ Dsrc)
    (hStage4 : D N = stage4Exact Dsrc a w2 ws)
    (hYesInput : D N ≤ Ysrc + stage4Overhead a w2 ws) : False := by
  rw [hStage4] at hYesInput
  unfold stage4Exact at hYesInput
  omega

/-! ## Part 4: non-vacuity

Part 1 introduces **no new structure and no premise bundle**: every hypothesis
is an explicit binder, and the only record used is the banked
`PublicRecords.LevelTrace`.  What still has to be shown is that the *unguarded*
half of those binders is jointly satisfiable at legal parameter values, and that
is what the two declarations below do.

The **guarded** half is not witnessed and must not be: `NoCert P`'s complexity
clause is the route's robust-seed reading, still Lean pending
(`PublicRecords.noCert_iff_reading`), and the Stage-4 and dense-rung inputs are
GAP-EXPOSED 1 and 2.  The canonical-inhabitation obligation for C3's full bundle
is deferred and REGISTERED in the ledger row; it is discharged when the
construction layer lands, never by anything here. -/

/-- **The unguarded parameter bundle of C2 and C3 fires, at the banked
entry-gate legality point of `thm:direct-robustification`.**

Every unguarded real and integer binder of Part 1 at the banked application
point `b_out = 1`, `delta_U = 1/60`, `theta = 1/192000`, `y = 3/5`, which is the
tuple `EntryGates.directEntryGates_fires` exhibits and which
`OneLevelAssembly.oneLevelAssembly_fires_no_witness` already runs the assembly
at.  The inner exponent `w_q = 3` is the same banked witness's value, so no
number here is self-chosen.

**This is the entry-gate legality point, NOT a point of the frozen Direct
admissibility group, and the distinction is material.**  Part 1's binders are
the `thm:direct-robustification` ranges (`10-direct-bridge.tex:38--41,53--56`)
plus `02-mechanical-contract.tex:774`'s `q >= 2`, and this tuple meets those.
It does **not** meet `def:admissible-parameters`' **Direct** group of
`05-public-records.tex:509--534`: there `delta_U <= 1/200` while here
`delta_U = 1/60`, and there `4 Q_0 theta <= delta/4` while here
`4 Q_0 theta = 4 * 4800 * (1/192000) = 1/10 = delta`, four times the admissible
bound.  Both failures are proved in the kernel by
`entryGatePoint_is_not_admissible` below rather than asserted here, and a point
that *does* satisfy the group is exhibited by
`admissibleDirectGroup_at_the_schedule_point`.  Since `thm:one-level` assumes
admissibility (`07:29--31`), **this tuple is not a point at which the
frozen theorem is in force**; what it witnesses is that Part 1's own -- weaker
-- hypothesis set is inhabited, which is all a non-vacuity check of Part 1
needs.

Why the trivial witness fails: `w_q = 0` satisfies every other conjunct and
fails `1 <= w_q`, which is the frozen legality `q = 2^{w_q} >= 2` of
`02-mechanical-contract.tex:771--775`; and `theta` cannot be taken `0`, since
`0 < theta` is demanded and the gate `4 Q_0 theta <= delta` is what bounds it
from above, so the admissible window is a genuine interval and not a point.

Reader locus: none -- a parameter-legality witness, not a reader statement. -/
theorem oneLevelTheorem_unguarded_bundle_fires :
    ∃ wq : ℕ, 1 ≤ wq ∧ (2 : ℕ) ^ wq = 8 ∧
      Qwidth 1 (1 / 60 : ℝ) = 8192 ∧ rQ 1 (1 / 60 : ℝ) = 13 ∧
      (0 : ℝ) < 1 / 192000 ∧ (1 / 192000 : ℝ) ≤ 1 ∧
      (0 : ℝ) < 1 / 60 ∧ (1 / 60 : ℝ) < 1 ∧
      directEntryGates 1 (1 / 60 : ℝ) (1 / 192000 : ℝ) (3 / 5) := by
  obtain ⟨hgates, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  exact ⟨3, by norm_num, by norm_num, hQ, hrQ, by norm_num, by norm_num,
    by norm_num, by norm_num, hgates⟩

/-- **A nondegenerate trace at the frozen-legal widths, including the bridge's
canonical outer width.**

**Explicitly labelled NON-FIDELITY.**  This is *not* the paper's own trace: the
route's `LevelStep(Public, Pi)` needs Stages 1--4, which are GAP-EXPOSED 1 and 2.
What it does establish is that the two unguarded width constraints of Part 1,
`q = 2^{w_q}` with `1 <= w_q` and `Q = Qwidth b_out delta_U`, are jointly
satisfiable by a genuine `LevelTrace` -- so those constraints are a real
restriction rather than a cardinality contradiction, and Part 1 is not a family
of statements about an uninhabited index.

It is also **not a restatement of `PublicRecords.traceWitness`**: that banked
witness is pinned at the outer width `Q = 2` and therefore cannot satisfy
`hQpow` at the bridge's canonical width `Qwidth b_out delta_U = 8192`.  The
construction is the banked one taken at the new outer width; no statement of
`PublicRecords` is repeated, and the guarded inputs of C3 are neither satisfied
nor approached here.

The protected duplication is proper -- `A` has twice the rows of `B`, and the
label-forgetting map is not injective -- so the record is not inhabited at the
degenerate `A = B`; both facts are recorded below.

Reader locus: none -- a probe, not a reader statement. -/
noncomputable def bridgeWidthTrace :
    LevelTrace K3 4 (paramsWitness (q2 K3 4)) Bool Bool Bool
      (Fin 2 × Bool) Bool 6 (2 ^ 1) (Qwidth 1 (1 / 60 : ℝ)) where
  S := guardedRow K3 4
  C₂ := (paramsWitness (q2 K3 4)).c₂
  π := slotEmbed K3 (by norm_num)
  M₁ := witnessBase
  M₂ := witnessM₂
  M₃ := interlaceFun (fun y x => witnessM₂ x y) 4
  B := witnessBase
  A := witnessA
  N := fun y x => witnessA x y
  U := interlaceFun (fun y x => witnessA x y) (2 ^ 1)
  W := fun y x => interlaceFun (fun y' x' => witnessA x' y') (2 ^ 1) x y
  Rnext := fun c r =>
    interlaceFun (fun y x => interlaceFun
      (fun y' x' => witnessA x' y') (2 ^ 1) x y) (Qwidth 1 (1 / 60 : ℝ)) r c
  fArow := Prod.snd
  rArow := fun b => (0, b)
  fAcol := id
  rAcol := id
  pUrow := Prod.fst
  pUcol := fun p => p.1 p.2
  pQrow := Prod.fst
  pQcol := fun p => p.1 p.2
  H := 6 + Nat.log 2 (q2 K3 4) + Nat.log 2 4 + Nat.log 2 (2 ^ 1)
    + Nat.log 2 (Qwidth 1 (1 / 60 : ℝ))
  mnext := rowsCard (fun (c : Fin (Qwidth 1 (1 / 60 : ℝ)) → Fin (2 ^ 1) × Bool)
    (r : Fin (Qwidth 1 (1 / 60 : ℝ)) × (Fin (2 ^ 1) → Fin 2 × Bool)) =>
      interlaceFun (fun y x => interlaceFun
        (fun y' x' => witnessA x' y') (2 ^ 1) x y)
        (Qwidth 1 (1 / 60 : ℝ)) r c)
  nnext := colsCard (fun (c : Fin (Qwidth 1 (1 / 60 : ℝ)) → Fin (2 ^ 1) × Bool)
    (r : Fin (Qwidth 1 (1 / 60 : ℝ)) × (Fin (2 ^ 1) → Fin 2 × Bool)) =>
      interlaceFun (fun y x => interlaceFun
        (fun y' x' => witnessA x' y') (2 ^ 1) x y)
        (Qwidth 1 (1 / 60 : ℝ)) r c)
  S_eq := rfl
  C₂_eq := rfl
  π_eq := fun _ _ => rfl
  M₂_eq := rfl
  M₃_eq := rfl
  N_eq := rfl
  U_eq := rfl
  W_eq := rfl
  Rnext_eq := rfl
  fArow_rArow := fun _ => rfl
  fAcol_rAcol := fun _ => rfl
  pUrow_eq := fun _ _ => rfl
  pUcol_eq := fun _ _ => rfl
  pQrow_eq := fun _ _ => rfl
  pQcol_eq := fun _ _ => rfl
  H_eq := rfl
  mnext_eq := rfl
  nnext_eq := rfl

/-- **The probe is nondegenerate.**  The protected duplication doubles the rows
and the label-forgetting map is not injective, so the trace does not inhabit
`T4` at the degenerate `A = B`; and the base matrix is two-valued, so no field
is satisfied by a constant.  NON-FIDELITY probe, as its definition records. -/
theorem bridgeWidthTrace_nondegenerate :
    rowsCard bridgeWidthTrace.A = 2 * rowsCard bridgeWidthTrace.B ∧
      ¬ Function.Injective bridgeWidthTrace.fArow ∧
      bridgeWidthTrace.B true true ≠ bridgeWidthTrace.B true false := by
  refine ⟨by decide, ?_, witnessBase_nonconstant⟩
  intro h
  have := h (a₁ := (0, true)) (a₂ := (1, true)) rfl
  exact absurd this (by decide)

/-- **The probe sits at the widths Part 1 demands.**  Its inner width is
`q = 2^1` with `1 <= 1`, and its outer width is the bridge's canonical
`Qwidth b_out delta_U`, which at the banked scheduled point is `8192` -- not the
`Q = 2` of the banked `PublicRecords.traceWitness`.  Both identifications are
`rfl` at the trace's own type parameters; the numeral comes from
`EntryGates.directEntryGates_fires`. -/
theorem bridgeWidthTrace_widths :
    (1 : ℕ) ≤ 1 ∧ (2 : ℕ) ^ 1 = 2 ∧ Qwidth 1 (1 / 60 : ℝ) = 8192 := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  exact ⟨le_refl 1, by norm_num, hQ⟩

/-- **C2 fires at a fully concrete legal pair, with the certificate inhabited.**

The banked public input `PublicRecords.publicInputConst` is the one whose `YES`
certificate is inhabited **in full** (`publicInputConst_yesCert`: the source half
is `k3_sourceYES` and the complexity half is `comp R = 0 <= 0 = Y`), and its
guarded source is `K_3`, the same ordered multigraph the probe trace is built
over, at the same `b_out = 1`.  So `oneLevelTheorem_C2` applies at the concrete
pair `(P, T) = (publicInputConst, bridgeWidthTrace)` with `w_q = 1`,
`delta_U = 1/60`, and its guard actually *fires* rather than being discharged
vacuously -- which is the shape a green build cannot otherwise see.

`hYesInput` stays a binder, exactly as
`OneLevelAssembly.oneLevelAssembly_fires_second_witness` keeps its `hYesN`: it is
the frozen Stage-4 `YES` line `11-one-level-assembly.tex:793`, which is
GAP-EXPOSED 1 and is not derived anywhere in this repository yet.

**NON-FIDELITY on the trace side**, as `bridgeWidthTrace` records: the public
input, its certificate and the width legality are the banked route objects, but
the trace is the probe rather than `LevelStep(Public, Pi)`.  This is evidence
that C2's statement shape is applicable and its guard satisfiable; it is not
evidence about the route's own trace. -/
theorem oneLevelTheorem_C2_fires_at_the_probe
    (hYesInput : YesCert publicInputConst →
      D bridgeWidthTrace.N ≤ publicInputConst.Y
        + stage4Overhead 6 (Nat.log 2 (q2 K3 4)) (Nat.log 2 4)) :
    D bridgeWidthTrace.Rnext ≤ publicInputConst.Y + bridgeWidthTrace.H :=
  oneLevelTheorem_C2 publicInputConst bridgeWidthTrace (wq := 1) (δU := 1 / 60)
    rfl rfl hYesInput publicInputConst_yesCert

/-! ## Part 5: the frozen **Direct** admissibility group, at the schedule's own
point

`thm:one-level` opens "Assume the single predicate `Admissible(Public,Pi,T)` of
`def:admissible-parameters`" (`07-one-level-construction.tex:29--31`) and
repeats the assumption inside the theorem statement (lines 40--41: line 40 ends
"... `eq:one-level-trace-destructuring`.  Assume" and the predicate itself is on
line 41).  The **Direct**
group of that predicate is printed at `05-public-records.tex:509--534`: the
clauses `0 < delta_U <= 1/200` and `lambda_def = -ln(1-delta_U)`, then
`eq:direct-theta-gates` and `eq:direct-numeric-gate`, then the explicit
arithmetic implication of lines 519--533 whose antecedent contains
`delta_U <= 1/200` and `4 Q_0 theta <= delta/4` and whose consequent is the
coverage map into `eq:direct-entry-gates`.

Part 1's own binders are strictly **weaker** than that group -- they are the
`thm:direct-robustification` ranges (`10-direct-bridge.tex:38--41,53--56`) plus
`02-mechanical-contract.tex:774`'s `q >= 2` -- so Part 1's theorems hold on a
strictly larger parameter set than the frozen clauses are stated on.  That is a
virtue for the theorems and a hazard for the *witnesses*: a tuple can satisfy
every binder of Part 1 and still fail the predicate `thm:one-level` assumes, in
which case it witnesses nothing about the frozen theorem.  Part 4's tuple is
exactly such a point, and this part settles the matter in the kernel in both
directions -- `entryGatePoint_is_not_admissible` proves the failure, and
`admissibleDirectGroup_at_the_schedule_point` exhibits a point that does satisfy
the group.

**Every quantity here is DEFINED by the frozen schedule, so none is assigned a
numeral.**  `eq:q-deltaU` (`06-parameter-schedule.tex:513--518`, label line 518)
fixes `q = 2^{A_wrap L_P^2}` and `delta_U = eta_R/(16 q)`; `eq:Q-theta-choice`
(`06:524--538`, label line 537) fixes
`Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`, then `Q` as the least power
of two at least `Q_0`, then `theta = c_theta/(2Q) = delta/(16 Q)`; and
`eq:direct-theta-gates` (`06:540--545`) together with the finite gate at
`06:547` is the paper's own verification that this point clears the Direct
group.  The values below are obtained by **evaluating that chain in dependency
order** through the banked `ParameterSchedule.qWrap`, `.etaR`, `.deltaU` and
`.theta` and the banked `EntryGates.Q0` / `.Qwidth`; the three gate facts are
the banked `deltaU_le_gates`, `schedule_theta_in_range` and `four_Q0_theta_le`,
consumed by pin and never re-derived.

`A_wrap`, `L_P`, `s`, `d_V`, `zeta` and `b_out` stay binders: `06:520--522`,
`06:471` and Section 6's source block fix them by searches this module does not
run, and assigning any of them a numeral would replace a schedule degree of
freedom by an invented constant (`M3`). -/

/-- **Aux 6 (the schedule's inner exponent is legal, and the width is two to
it).**

`eq:q-deltaU` (`06-parameter-schedule.tex:515`) sets `q = 2^{A_wrap L_P^2}`, and
`02-mechanical-contract.tex:771--775` demands `q >= 2`, i.e. `1 <= log_2 q`.
Both halves at once for the banked `ParameterSchedule.qWrap`: the exponent is at
least one whenever the two frozen schedule integers are, and the width is
literally two to that exponent -- which is the shape Part 1's `hqpow` binder
asks for.

Monotonicity/floor property, general in `A_wrap` and `L_P`; no trace, carrier,
promise or real parameter occurs.  The banked `.qWrap_eq_two_pow` is consumed by
pin, not restated: what is new is only the exponent bound beside it.

**The hypotheses are surrogates, not the frozen floors, and the name must not be
read as claiming otherwise.**  The frozen source fixes `A_wrap > c_seed = 100`
(`06:1671`, `06:578`) and `L_P = clog_2(P_0) >= 4` (`06:467--471`), banked as
`ParameterSchedule.hundredOne_le_of_cSeed_lt` and `.four_le_LPwidth`.  `1 <=
A_wrap` and `1 <= L_P` are strictly weaker, which makes this statement stronger;
but `A_wrap = L_P = 1` is **not** a legal schedule point, and "legal" in the
declaration name refers to the conclusion `q >= 2` it establishes, not to the
hypotheses it establishes it from.

Reader locus: none -- a schedule legality readout, not a reader statement. -/
theorem qWrap_exponent_legal {Awrap LP : ℕ} (hA : 1 ≤ Awrap) (hL : 1 ≤ LP) :
    1 ≤ Awrap * LP ^ 2 ∧
      ParameterSchedule.qWrap Awrap LP = 2 ^ (Awrap * LP ^ 2) := by
  refine ⟨?_, ParameterSchedule.qWrap_eq_two_pow Awrap LP⟩
  have h1 : 1 ≤ LP ^ 2 := Nat.one_le_pow _ _ (by omega)
  simpa using Nat.mul_le_mul hA h1

/-- **Aux 7 (the frozen coverage map of the Direct group).**

`05-public-records.tex:519--533` prints the implication whose antecedent is
`delta_U <= 1/200`, `lambda_def = -ln(1-delta_U)`, `4 Q_0 theta <= delta/4` and
`eq:direct-numeric-gate`, and whose consequent is `4 Q_0 theta <= delta`
together with `3 lambda_def + (7/5) ln 2 <= -2 ln(3/5)` -- i.e. exactly
`EntryGates.directEntryGates` at the frozen `y = 3/5`.

Landed in the form the schedule supplies it: the second consequent is the banked
`EntryGates.secondEntryGate_of_deltaU_small`, which needs the weaker
`delta_U <= 1/60` that the frozen `1/200` implies, and the first follows from
`delta/4 < delta` at `delta = 1/10`.

Ordering property, general in `b_out`, `delta_U` and `theta`.  Nothing is
assumed about how the tuple was produced, so this is reusable at any admissible
point and is **not** a statement about the schedule's own point; the schedule
enters only in the next declaration.

Reader locus: none -- the coverage map is autoformalization-only content. -/
theorem directEntryGates_of_admissibleDirect (bout : ℕ) {δU θ : ℝ}
    (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 60)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed / 4) :
    directEntryGates bout δU θ (3 / 5) := by
  refine ⟨?_, secondEntryGate_of_deltaU_small hδ0 hδ⟩
  have hpos : (0 : ℝ) < deltaFixed := by rw [deltaFixed_eq]; norm_num
  linarith

/-- **The Direct admissibility group of `def:admissible-parameters` holds at the
schedule's own point.**

The point is the frozen schedule's, evaluated rather than chosen:
`q = qWrap A_wrap L_P` (`eq:q-deltaU`, `06:515`),
`delta_U = deltaU (etaR s d_V zeta) q` (`eq:q-deltaU`, `06:517`), and
`theta = theta (Qwidth b_out delta_U)` (`eq:Q-theta-choice`, `06:533`, at `Q`
and **not** at `Q_0` -- that difference is the whole of finding F3, since
`theta = delta/(16 Q)` with `Q >= Q_0` is exactly what makes `4 Q_0 theta` come
out at `delta/4` rather than at `delta`).

**What is delivered, and where each part actually comes from.**  The statement
has **five** top-level conjuncts; the second bundles two independent facts, so
the provenance list below has six entries.  They are *not* all clauses of the
`05:509--534` Direct group, and saying so would misattribute three of them:

1. `1 <= A_wrap L_P^2` with `qWrap = 2^{A_wrap L_P^2}` -- **not a Direct clause
   at all**.  It is the frozen legality `q >= 2` of
   `02-mechanical-contract.tex:771--775`, read as `1 <= log_2 q`, which is what
   Part 1's `hqpow` binder asks for.
2. `0 < delta_U < 1` -- the frozen range of `thm:direct-robustification`
   (`10-direct-bridge.tex:38`, repeated at `11-one-level-assembly.tex:666`),
   **not** printed in the `05:509--534` window.
3. `delta_U <= 1/200` -- **is** the Direct group's own clause (`05:512`), and
   also the finite gate imposed at `06:547`.  Here it is *discharged* rather
   than assumed: the banked `ParameterSchedule.deltaU_le_gates` derives it from
   the definitional chain, which is strictly stronger than imposing it.
4. `0 < theta <= 1` -- the frozen `theta` range of `thm:direct-robustification`
   (`10-direct-bridge.tex:38--41`); the Direct group constrains `theta` only
   through `eq:direct-theta-gates`.
5. `4 Q_0 theta <= delta/4 < delta` -- the **second** row of
   `eq:direct-theta-gates` (`06:544`), which the Direct group cites at `05:515`.
6. `directEntryGates b_out delta_U theta (3/5)` -- the consequent of the Direct
   group's own coverage map (`05:519--533`, consequent at `05:530--531`).

**Not delivered in the kernel here, and why that is not a gap.**  The *first*
row of `eq:direct-theta-gates`, `Q theta = delta/16 < delta/2` (`06:542`), is
inside the group's cited `\eqref{eq:direct-theta-gates}` but is **not** a
conjunct below.  It is true at this point -- it is the banked
`ParameterSchedule.Q_mul_theta` -- so its absence is record incompleteness, not
a mathematical gap.  Two further Direct clauses are handled definitionally
rather than as conjuncts: `lambda_def = -ln(1-delta_U)` (`05:513`) is the
*definition* `EntryGates.lambdaU`, so it is not an assumable clause at all, and
`eq:direct-numeric-gate` (`06:551`, label 552) is discharged inside the banked
`EntryGates.secondEntryGate_of_deltaU_small`.  Both are strengthenings.

Together these are every unguarded real and integer binder Part 1
carries, **plus** the two arithmetic clauses of the Direct group that Part 4's
tuple fails -- so this is a point at which `thm:one-level` is genuinely in
force, and Part 1 is a family of statements about a nonempty admissible
parameter set.

Why the trivial witness fails: `theta = 0` is excluded by `0 < theta`, and
`delta_U = 0` by `0 < delta_U`, so the group is not satisfiable by collapsing
either scale; and the pair cannot be met by shrinking `theta` alone while
keeping Part 4's `delta_U = 1/60`, because `delta_U <= 1/200` is a separate
clause that no choice of `theta` repairs.  Both are *forced* here rather than
arranged: they come out of `deltaU_pos`, `theta_pos` and `deltaU_le_gates` at
the schedule's own definitions.

**Hypothesis provenance, stated exactly.**  `3 < s`, `0 < d_V` and `0 < zeta`
are the frozen positivity conditions `eta_R` is formed under.  `1 <= A_wrap` and
`1 <= L_P`, however, are **positivity surrogates strictly weaker than the frozen
floors**, and are deliberately not presented as the frozen conditions: the
frozen source fixes `A_wrap > c_seed` with `c_seed = 100` (`06:1671` and
`06:578`), i.e. `A_wrap >= 101`, banked as
`ParameterSchedule.hundredOne_le_of_cSeed_lt`, and `L_P = clog_2(P_0)` with
`P_0 >= 16` (`06:467--471`), i.e. `L_P >= 4`, banked as
`ParameterSchedule.four_le_LPwidth`.  Assuming less makes this theorem
**stronger**, and nothing false is asserted; but `1 <= A_wrap` and `1 <= L_P`
must not be cited anywhere as the frozen legality, and the companion name
`qWrap_exponent_legal` is a Lean name, not a claim that `A_wrap = L_P = 1` is a
legal schedule point -- it is not.

**Non-vacuity, on tree.**  The bundle is inhabited at the frozen floors
themselves: the banked `ParameterSchedule.scheduledPoint_hypotheses_consistent`
(`:1752--1767`) is the same-shape consistency probe at the *evaluated* scheduled
point, discharging `4 <= L_P` through `four_le_LPwidth_sched` and `101 <=
A_wrap` through `hundredOne_le_of_cSeed_lt`, and returning
`schedule_fires_directEntryGates` there.  So the hypotheses below are satisfied
at a point at or above both frozen floors, and the theorem is not vacuous.

There is no promise, certificate, trace or matrix anywhere in the statement --
so no case of the construction is conjoined with another and the bundle cannot
be inconsistent.

Reader locus: none -- an admissibility-legality witness, not a reader
statement. -/
theorem admissibleDirectGroup_at_the_schedule_point
    {s Awrap LP bout : ℕ} {dv zeta δU θ : ℝ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta)
    (hA : 1 ≤ Awrap) (hL : 1 ≤ LP)
    (hδU : δU = ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta)
      (ParameterSchedule.qWrap Awrap LP))
    (hθ : θ = ParameterSchedule.theta (Qwidth bout δU)) :
    (1 ≤ Awrap * LP ^ 2 ∧
        ParameterSchedule.qWrap Awrap LP = 2 ^ (Awrap * LP ^ 2)) ∧
      (0 < δU ∧ δU < 1 ∧ δU ≤ 1 / 200) ∧
      (0 < θ ∧ θ ≤ 1) ∧
      (4 * Q0 bout δU * θ ≤ deltaFixed / 4 ∧ deltaFixed / 4 < deltaFixed) ∧
      directEntryGates bout δU θ (3 / 5) := by
  have hq : 0 < ParameterSchedule.qWrap Awrap LP :=
    ParameterSchedule.qWrap_pos Awrap LP
  have hbounds :=
    ParameterSchedule.deltaU_le_gates (s := s) (dv := dv) (zeta := zeta) hq
  have hδ0 : 0 < δU := by
    rw [hδU]
    exact ParameterSchedule.deltaU_pos (ParameterSchedule.etaR_pos hs hdv hz) hq
  have hδ200 : δU ≤ 1 / 200 := by rw [hδU]; exact hbounds.1
  have hδ60 : δU ≤ 1 / 60 := by rw [hδU]; exact hbounds.2
  have hδ1 : δU < 1 := by
    rw [hδU]
    exact ParameterSchedule.deltaU_lt_one (s := s) (dv := dv) (zeta := zeta) hq
  have hrange := ParameterSchedule.schedule_theta_in_range bout δU
  have hθ0 : 0 < θ := by rw [hθ]; exact hrange.1
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith [hrange.2]
  have hfour := ParameterSchedule.four_Q0_theta_le bout δU
  have hgate : 4 * Q0 bout δU * θ ≤ deltaFixed / 4 := by rw [hθ]; exact hfour.1
  exact ⟨qWrap_exponent_legal hA hL, ⟨hδ0, hδ1, hδ200⟩, ⟨hθ0, hθ1⟩,
    ⟨hgate, hfour.2⟩, directEntryGates_of_admissibleDirect bout hδ0 hδ60 hgate⟩

/-- **Pole: the banked entry-gate point is NOT a point of the Direct
admissibility group.**

`EntryGates.directEntryGates_fires` exhibits `(b_out, delta_U, theta, y) =
(1, 1/60, 1/192000, 3/5)` and proves `eq:direct-entry-gates` there; Part 4 uses
it, correctly, as a witness that Part 1's own binders are inhabited.  It is
**not** a witness for `thm:one-level`, and this declaration is why.

At that tuple the banked `Q_0` evaluates to `4800`, so

```
4 Q_0 theta = 4 * 4800 * (1/192000) = 1/10 = delta,
```

which is four times the Direct group's `4 Q_0 theta <= delta/4`
(`05-public-records.tex:520--525`, via `eq:direct-theta-gates`); and
`delta_U = 1/60 > 1/200` fails the group's other arithmetic clause and the
finite gate of `06:547` as well.  Both failures are proved, not asserted.

The gap is **inherited, not created here**: it belongs to the banked witness of
`ENTRY-GATES-001`, whose `theta` is calibrated at `Q_0` rather than at the
schedule's `Q >= Q_0`.  What closes it is
`admissibleDirectGroup_at_the_schedule_point`, which calibrates `theta` at `Q`
exactly as `eq:Q-theta-choice` does.

This is a statement pole and not a defect report: it is the one-line reason the
previous witness does not establish non-vacuity of the *frozen* theorem, made
checkable so that no later round can re-describe that tuple as the route's
scheduled point.

Reader locus: none -- an interface separation, not a transcription. -/
theorem entryGatePoint_is_not_admissible :
    directEntryGates 1 (1 / 60 : ℝ) (1 / 192000 : ℝ) (3 / 5) ∧
      Q0 1 (1 / 60 : ℝ) = 4800 ∧
      ¬ ((1 / 60 : ℝ) ≤ 1 / 200) ∧
      4 * Q0 1 (1 / 60 : ℝ) * (1 / 192000 : ℝ) = deltaFixed ∧
      ¬ (4 * Q0 1 (1 / 60 : ℝ) * (1 / 192000 : ℝ) ≤ deltaFixed / 4) := by
  obtain ⟨hgates, hQ0, -, -, -, -, -⟩ := directEntryGates_fires
  refine ⟨hgates, hQ0, by norm_num, ?_, ?_⟩
  · rw [hQ0, deltaFixed_eq]; norm_num
  · rw [hQ0, deltaFixed_eq]; norm_num

/-! ## Part 6: converting the certificate-guarded clauses into the banked
per-level difference forms

This is `ITERATED-CANONICAL-CHAINING-001`'s **GAP-EXPOSED 4**, verbatim:

> The per-level clause shape is the banked one, and it is not the frozen clause
> C2/C3 shape.  Frozen lines 336--345 obtain the per-level updates as
> implications out of `YesCert(Public_i)` / `NoCert(Public_i)`; the banked
> `ITER-001` inductions take the *difference* form `cc (i+1) <= cc i + H i` and
> `cc (i+1) = cc i + H i + 1` ...  Turning the frozen certificate-guarded
> clauses into those differences needs `thm:one-level` C1--C3 in Lean.

The frozen conversion is `12-iteration-specification.tex:335--350`.  On the
`YES` side: "The promise-independence clause C1 of `thm:one-level` keeps the
trace fixed, and clause C2 gives `comp R_i^+ <= Y_i + H_i = Y_{i+1}`.
Canonical-reindexing invariance and `eq:iterated-canonical-chaining` give the
same inequality for `R_{i+1}`."  On the `NO` side: "The NO clause C3 gives both
the exact equality and the depth-`b_{i+1}` certificate for `R_i^+`", transported
the same way.

Two declarations, consuming the two Section-12 pins **by pin and in proof
terms**, never restating them:

* `chainedSuccessor_differenceForms` consumes
  `IteratedCanonicalChaining.chainingStep_from_oneLevel`, which supplies the two
  cardinality proofs from the banked one-level carrier equations, and states the
  clauses at the canonical successor `Can(R+)` on the schedule's own carriers.
  No chain object is needed and none is assumed.
* `chainedLevel_differenceForms` consumes
  `IteratedCanonicalChaining.CanonicalChain.chain_apply`, the frozen pointwise
  chaining equation, and states the clauses at `R_{i+1} = Ch.lev (i+1)` of an
  actual chain.

**Scope, kept exact.**  Only the complexity half is transported.  The frozen
`NO` clause also regenerates the depth-`b_{i+1}` bracket certificate, whose
transport is `eq:canonical-bracket-invariance` (`12:146--165`) --
`ITERATED-CANONICAL-CHAINING-001`'s own GAP-EXPOSED 1, asserted nowhere, and
**not** delivered here.  Nothing below mentions a bracket, a retained density or
`Lambda_3`.

**Nothing is discharged.**  Both declarations take C2 and C3 as guarded
hypotheses -- in practice `oneLevelTheorem_C2` and `oneLevelTheorem_C3` applied
at the level's own trace -- so every guard of Part 1, and with it GAP-EXPOSED 1
and 2, travels into the difference forms unchanged.

**The two shapes are kept apart deliberately.**  The frozen `YES` induction
hypothesis is the *inequality* `comp R_i <= Y_i` (`12:336`), not an equality, so
the frozen transport delivers the **budget** form `comp R_{i+1} <= Y_i + H_i`;
the banked `chainYesFold` instead consumes the **difference** form
`cc (i+1) <= cc i + H i`, which is the same statement only where the induction
is tight.  The budget forms below are therefore stated unconditionally, and each
difference form is stated under an explicit inner implication naming the
tightness it needs.  Conflating them would be exactly the over-strong hypothesis
a green build cannot see. -/

section ChainConversion

variable (P : LevelPublicInput V E) {s : ℕ} {X₁ : Type*}
  {Pr : LevelParams X₁ (q2 P.G s)}
  {C₁ RB CB : Type*} {RA CA : Type}
  [Fintype X₁] [Fintype C₁]
  [Fintype RB] [Fintype CB] [Fintype RA] [Fintype CA]

/-- **Aux 8 (the chaining transports separation, entrywise).**

`eq:iterated-canonical-chaining`'s third equation read pointwise
(`CanonicalChain.chain_apply`, itself `def:canonical-reindexing`'s display at
`12:115`, whose `\label{eq:canonical-reindexing}` is on `12:116`): every entry
of `R_{i+1}` is an entry of `R_i^+`, and the two
canonical equivalences are bijections, so any two entries of the level output
that differ are *witnessed* by two entries of the relabelled matrix that differ.

Round-trip/nondegeneracy property, general in the specification, the chain, the
level and the four points.  It is what stops the difference forms below from
being statements about a matrix that the relabelling could have flattened: the
canonical reindexing is a relabelling, not a projection, and this is the kernel
form of that.

Reader locus: none -- a chaining property, not a transcription. -/
theorem chainedLevel_separates_of_output_separates
    {Spec : FixedLevelCarriers.LevelCarrierSpec}
    (Ch : IteratedCanonicalChaining.CanonicalChain Spec) (i : ℕ)
    {x x' : Ch.Row i} {y y' : Ch.Col i}
    (h : Ch.out i x y ≠ Ch.out i x' y') :
    ∃ u u' : Fin (Spec.rowCarrier (i + 1)),
      ∃ v v' : Fin (Spec.colCarrier (i + 1)),
        Ch.lev (i + 1) u v ≠ Ch.lev (i + 1) u' v' := by
  refine ⟨(IteratedCanonicalChaining.canonEquiv (Ch.Row i) (Ch.rowCard i)).symm x,
    (IteratedCanonicalChaining.canonEquiv (Ch.Row i) (Ch.rowCard i)).symm x',
    (IteratedCanonicalChaining.canonEquiv (Ch.Col i) (Ch.colCard i)).symm y,
    (IteratedCanonicalChaining.canonEquiv (Ch.Col i) (Ch.colCard i)).symm y', ?_⟩
  simp only [Ch.chain_apply i, Equiv.apply_symm_apply]
  exact h

/-- **The clauses at the canonical successor, through
`chainingStep_from_oneLevel`**
(`12-iteration-specification.tex:222--230` and the conversion paragraph
`:335--350`; `07-one-level-construction.tex:55--58` and `:60--67`).

`eq:iterated-canonical-chaining` demands two cardinality equalities before the
relabelling `R_{i+1} = Can_{m_{i+1},n_{i+1}}(R_i^+)` even typechecks, and frozen
lines 257--258 attribute them to clause C4 of `thm:one-level`.  The banked
`IteratedCanonicalChaining.chainingStep_from_oneLevel` is exactly that
attribution, so both proofs are **supplied, not assumed**, and with them the
complexity invariance `comp(Can(M)) = comp(M)`.  Composing that with C2 and C3
at the level's own trace gives the two clauses at the successor matrix on the
schedule's own carriers `m_{i+1}`, `n_{i+1}`.

The trace is typed at the specification's own widths -- inner `q = 2^{q_exp i}`
(`eq:q-deltaU`) and outer `Q = Qwidth (b_out i) (delta_U i)`
(`eq:Q-theta-choice`) -- so neither width is a free numeral (`M3`), and the two
are in their frozen **exchanged** roles throughout: `q` is the scale-alignment
interlace width and `Q` the outer selector width, never the reverse.

**No carrier equation is stated.**  The two cardinalities appear only as the
proof arguments `hrow`, `hcol` that `Can` needs; the closed forms
`(q m_N)^Q` and `Q n_N^q` stay with `ONELEVEL-001` and `SIZE-001` and are not
restated, exactly as Parts 1--2 already avoid them.

On the existential: `hrow` and `hcol` are proofs of cardinality equations, so
the existential quantifies over `Prop`s and carries no data; the content is
entirely in the conjunction, and the trivial reading -- discarding the
conjunction and claiming only that the cardinalities match -- is the banked
`FixedLevelCarriers.fixedLevelCarriers_realized`, which is consumed here rather
than re-proved.

**Both guards travel.**  `hC2` and `hC3` are the conclusions of
`oneLevelTheorem_C2` and `oneLevelTheorem_C3`, each already guarded by its
certificate, so nothing here is unguarded and nothing is discharged.  General in
the public input, the seven trace carriers, the specification, the level and the
trace.

Reader locus: none -- the reader has no canonical-reindexing statement outside
the proof of `thm:paper-finite-iteration`, and proof-internal prose is never
cited as a statement. -/
theorem chainedSuccessor_differenceForms {a : ℕ}
    (Spec : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ)
    (T : LevelTrace P.G s Pr C₁ RB CB RA CA a
      (2 ^ Spec.qExp i) (Qwidth (Spec.bout i) (Spec.dU i)))
    (hm : rowsCard T.N = Spec.mN i) (hn : colsCard T.N = Spec.nN i)
    [LinearOrder (Fin (Qwidth (Spec.bout i) (Spec.dU i)) →
      Fin (2 ^ Spec.qExp i) × CA)]
    [LinearOrder (Fin (Qwidth (Spec.bout i) (Spec.dU i)) ×
      (Fin (2 ^ Spec.qExp i) → RA))]
    (hC2 : YesCert P → D T.Rnext ≤ P.Y + T.H)
    (hC3 : NoCert P → D T.Rnext = P.D + T.H + 1) :
    ∃ (hrow : Fintype.card (Fin (Qwidth (Spec.bout i) (Spec.dU i)) →
          Fin (2 ^ Spec.qExp i) × CA) = Spec.rowCarrier (i + 1))
      (hcol : Fintype.card (Fin (Qwidth (Spec.bout i) (Spec.dU i)) ×
          (Fin (2 ^ Spec.qExp i) → RA)) = Spec.colCarrier (i + 1)),
      (YesCert P →
          D (IteratedCanonicalChaining.Can hrow hcol T.Rnext) ≤ P.Y + T.H) ∧
        (NoCert P →
          D (IteratedCanonicalChaining.Can hrow hcol T.Rnext)
            = P.D + T.H + 1) := by
  have hR : T.Rnext
      = levelOutput T.N (Spec.qExp i) (Spec.bout i) (Spec.dU i) :=
    traceOutput_eq_levelOutput T
  obtain ⟨hrow, hcol, -, hD⟩ :=
    IteratedCanonicalChaining.chainingStep_from_oneLevel Spec i T.N hm hn
  refine ⟨hrow, hcol, fun hc => ?_, fun hc => ?_⟩
  · rw [hR, hD, ← hR]; exact hC2 hc
  · rw [hR, hD, ← hR]; exact hC3 hc

/-- **The clauses at the chain's own successor level, through `chain_apply`**
(`12-iteration-specification.tex:339--341` and `:345--349`).

The frozen sentence transported here is "Canonical-reindexing invariance and
`eq:iterated-canonical-chaining` give the same inequality for `R_{i+1}`", and
its `NO` twin.  `Ch.lev (i+1)` is the chain's own level matrix, and the link to
the trace is the frozen one: the chain's level-`i` output *is* `R_i^+`, up to
the two carrier equivalences, which is `hout` with `eRow`, `eCol`.  From
`CanonicalChain.chain_apply` -- the pointwise chaining equation, consumed by pin
-- the level matrix is a reindexing of `T.Rnext` along one composite equivalence
per side, so `IteratedCanonicalChaining.reindex_complexity` transports the
complexity, and C2 and C3 read at `Ch.lev (i+1)`.

Four conclusions, and the split is deliberate:

* the two **budget** forms, `comp R_{i+1} <= Y + H` and
  `comp R_{i+1} = D + H + 1`, which are the frozen transports verbatim and hold
  with no further hypothesis;
* the two **difference** forms, `comp R_{i+1} <= comp R_i + H` and
  `comp R_{i+1} = comp R_i + H + 1`, which are the shapes the banked folds
  `IteratedCanonicalChaining.chainYesFold` / `.chainNoFold` consume, each under
  an explicit inner implication naming the level identification it needs.  On
  the `NO` side that identification is frozen (`12:342`, "the equality
  `comp R_i = D_i`"); on the `YES` side the frozen hypothesis is the
  *inequality* `comp R_i <= Y_i` (`12:336`), so the difference form is delivered
  at the tight level only and is **not** claimed unconditionally.  Writing the
  `YES` difference form without that guard would be an over-strong reading of
  the frozen induction.

The `D (Ch.out i)` variants the folds also accept are one banked rewrite away
through `CanonicalChain.chain_complexity` and are deliberately not restated
here.

**Nothing is discharged, and the chain is a binder.**  `Ch` is assumed, not
built: constructing the chain whose `out i` is the route's own level output is
`ITERATED-CANONICAL-CHAINING-001`'s GAP-EXPOSED 3, registered as deferred there
(see GAP-EXPOSED 5 above).  `hC2` and `hC3` carry their certificates, so no
hypothesis asserts both promise cases and the bundle cannot collapse.

General in the public input, the seven trace carriers, the two exponents, the
specification, the chain, the level and the two equivalences.

Reader locus: none, for the reason recorded on the previous declaration. -/
theorem chainedLevel_differenceForms {a wq bout : ℕ} {δU : ℝ}
    (T : LevelTrace P.G s Pr C₁ RB CB RA CA a (2 ^ wq)
      (Qwidth bout δU))
    {Spec : FixedLevelCarriers.LevelCarrierSpec}
    (Ch : IteratedCanonicalChaining.CanonicalChain Spec) (i : ℕ)
    (eRow : Ch.Row i ≃ (Fin (Qwidth bout δU) → Fin (2 ^ wq) × CA))
    (eCol : Ch.Col i ≃ (Fin (Qwidth bout δU) × (Fin (2 ^ wq) → RA)))
    (hout : ∀ x y, Ch.out i x y = T.Rnext (eRow x) (eCol y))
    (hC2 : YesCert P → D T.Rnext ≤ P.Y + T.H)
    (hC3 : NoCert P → D T.Rnext = P.D + T.H + 1) :
    (YesCert P → D (Ch.lev (i + 1)) ≤ P.Y + T.H) ∧
      (NoCert P → D (Ch.lev (i + 1)) = P.D + T.H + 1) ∧
      (YesCert P → D (Ch.lev i) = P.Y →
        D (Ch.lev (i + 1)) ≤ D (Ch.lev i) + T.H) ∧
      (NoCert P → D (Ch.lev i) = P.D →
        D (Ch.lev (i + 1)) = D (Ch.lev i) + T.H + 1) := by
  have key : Ch.lev (i + 1) = IteratedCanonicalChaining.reindex
      ((IteratedCanonicalChaining.canonEquiv (Ch.Row i)
        (Ch.rowCard i)).trans eRow)
      ((IteratedCanonicalChaining.canonEquiv (Ch.Col i)
        (Ch.colCard i)).trans eCol) T.Rnext := by
    funext u v
    rw [Ch.chain_apply i u v, hout]
    rfl
  have hD : D (Ch.lev (i + 1)) = D T.Rnext := by
    rw [key]
    exact IteratedCanonicalChaining.reindex_complexity _ _ _
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc hlev => ?_, fun hc hlev => ?_⟩
  · rw [hD]; exact hC2 hc
  · rw [hD]; exact hC3 hc
  · rw [hD, hlev]; exact hC2 hc
  · rw [hD, hlev]; exact hC3 hc

end ChainConversion

end EthInapproximability.ParameterizedNP.OneLevelTheorem
