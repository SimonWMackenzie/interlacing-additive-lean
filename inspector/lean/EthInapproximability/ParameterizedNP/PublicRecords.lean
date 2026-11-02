import EthInapproximability.ParameterizedNP.GuardedSourceSlab
import EthInapproximability.ParameterizedNP.OneLevelAssembly

/-!
# Parameterized NP route: the Section-5 typed record layer

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `sec:level-records`, *Public
  records and the one-level constructor*, in the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/05-public-records.tex`, **lines 13--318**.  The
  anchors traced here are
  * `def:level-public-input` (label line 13, body lines 12--51), clauses
    `P1`--`P5` and the closing promise-freedom sentence of lines 45--50;
  * `def:level-certificates` (label line 54, body lines 53--74), the two
    separate propositions `YesCert(Public)` and `NoCert(Public)`;
  * `def:level-configuration` (label line 92, body lines 91--102);
  * `def:level-parameters` (label line 173, body lines 172--190);
  * `def:level-trace` (label line 220, body lines 219--316), clauses
    `T1`--`T6`, including `eq:trace-interlace-coordinate-carriers` (label line
    284), `eq:trace-interlace-coordinate-types` (label line 294) and
    `eq:trace-interlace-coordinate-equations` (label line 304);
  * for the Stage-2 field `M_2` -- which `T3` (05:253--254) delegates by the
    same reference -- the delegated display `eq:stage2-relaxed-value` of
    `sections/07-one-level-construction.tex` (display lines 221--229, label line
    228) in **all three** of its lines: `Rows(M_2) = [q_2] x C_1` at `07:223`
    (reprinted as `J_2 = Rows(M_2) = [q_2] x C_1` at `07:528` inside
    `eq:raw-stage4-universes`), `Cols(M_2) = L_2` at `07:224`, and the value
    clause `M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)` at
    `07:225--226`, with the typed-evaluation sentence `07:230--231`; together
    with `def:level-parameters`'s own `L_2 = [N_2]` at `05:178`,
    `conv:finite-slots` for the zero-based reading of `[q_2]` and `[N_2]`, and
    the framing sentence `07:217--220` ("Stage 2 is a relaxed interlace of
    `M_1^T`", with `c^{(l)} : [q_2] -> Rows(M_1)`) that names the vendored
    `NPCC.relaxedInterlace` of `def:relaxed-interlace` as the constructor;
  * for the Stage-3 field `M_3` -- which `T3` (05:253--254) delegates by
    reference, "`M_1, M_2, M_3, B` have exactly the carriers and entry maps in
    `sec:one-level`" -- the delegated displays themselves, in
    `sections/07-one-level-construction.tex`: `M_3 = Int_s(M_2^T)` at line 450
    (inside `lem:stage3-exact-scale`) and again as the construction's own
    display at line 497, together with `S_2 = M_2^T` of
    `sections/08-dense-stage4.tex` lines 262--263 and `def:interlace` of
    `sections/03-preliminaries.tex` lines 112--119 -- the range that carries the
    **complete** definition: the row set `[p] x X` at line 114, the column set
    `Y^p` at line 115, and the value `M(x, y(i))` at lines 116--119 (the
    narrower `03:112--114` cited elsewhere in this repository reaches the row
    set only, and is correct exactly where only the row set is claimed).  The
    consuming site `07:539--541`
    (`eq:raw-stage4-universes`) prints the same carrier, `[s] x Cols(M_2)`, as
    the template summand of `Rows(B)`;
  * the destructuring `eq:one-level-trace-destructuring` of
    `sections/07-one-level-construction.tex` (display lines 18--28, label line
    27), which the field order of `LevelTrace` reproduces letter-exactly.

  Lines 318 onwards -- `proc:level-step`, `inv:construction-identity` and the
  nine admissibility gate groups of `def:admissibility-groups` -- are **out of
  scope for this module** and nothing here states them.  Lines 780--850 of the
  same frozen section are already banked in `OneLevelAssembly.lean`
  (`ASSEMBLY-001`) and are consumed by pin, never restated.

* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`
  `03-parameterized-construction.tex`, `thm:paper-parameterized-one-bit`), one
  reader item per declaration, no **item** claimed twice here or in any earlier
  row.  The reader loci used are all previously unclaimed; the only two
  previously claimed loci in this reader file are line 59 (`a >= 6`) and line
  142, both held by `SIZE-001`, and neither is touched.  The list:
  * lines 53--54, "Let `R : X x Y -> {0,1}` be a public Boolean matrix with
    nonempty carriers, and let `Y_0, D, b_0` be public integers, with
    `D >= 3`" -> `LevelPublicInput` clauses `P3`, `P4`, `P5`;
  * lines 55--58, "Let `Delta >= 1` be an integer and let `gamma in Q` satisfy
    `0 < gamma <= 1`.  Let `G = (V,E)` be a finite ordered loopless multigraph
    with nonempty `V,E`, no isolated vertices, and maximum degree at most
    `Delta`" -> `LevelPublicInput` clauses `P1`, `P2`.  The graph record and
    the degree/density content are the banked `EndpointGraph` and
    `SourceCommon` and are **not** reclaimed here (row `SOURCE-GRAPH-001`
    already holds reader lines 16--18 and the `SourceCommon` content); what is
    claimed at lines 55--58 is exactly the *public-input tuple* clause, the
    frozen `P2` bundle `(gamma, Delta, SourceCommon)` sitting in one record;
  * lines 100--101, "If `G` is three-colourable and `CC(R) <= Y_0`"
    -> `YesCert`;
  * lines 105--107, "If the source satisfies its `NO` promise, `CC(R) = D`,
    and `R` has a robust certificate at depth `b_0`" -> `NoCert`;
  * `eq:paper-W-definition` (label line 88), display line 87,
    `W = Int_q(N)^T` -> the trace field equation `W_eq` together with `U_eq`,
    read off as `levelTrace_W_eq_bridge` (`:1536--1539`);
  * `eq:paper-W-carriers` (label line 124), display lines 121--123,
    `|Rows(W)| = n_N^q` and `|Cols(W)| = q m_N` ->
    `PublicRecords.levelTrace_W_carriers` (`:1590`).

  **Reader items deliberately declined, with the reason recorded** (the
  precedent is `CLOCK-001`/`cc-t1x` and `SOURCE-SLAB-001`/`cc-t2b`):
  * `LevelConfig` has **no** reader counterpart.  The reader never displays the
    six universal integers `(C_0, c_seed, A_wrap, B_s, c_b, C_in)`; it defers
    all of them to `thm:paper-effective-level`, whose displayed successor bound
    is already claimed by `SIZE-001` (`effectiveParameterSchedule`, reader
    lines 221--226).  So `LevelConfig` claims no reader item.
  * `LevelParams` claims **no** reader item.  The nearest reader sentence,
    lines 75--77 ("suppose that the one physical family `C_2` is indexed
    `(q_2,t_2,eps_2)`-balanced"), states *balancedness*, which the frozen
    `def:level-parameters` explicitly refuses to make a field ("The
    balancedness formula remains a post-construction admissibility
    proposition; it is not a proof field of `Pi`", 05:186--189).  Citing it
    here would assign the record a property it does not carry, so it is
    declined; `levelParams_admits_unbalanced_family` records in the kernel why.
  * `LevelTrace`'s remaining fields (`S`, `C_2`, the rank injections, `M_1`,
    `M_3`, `B`, `A`, `N`, the four duplication maps, the four
    coordinate maps, `H`, `m_next`, `n_next`) have no reader display: the
    reader states only `eq:paper-W-definition` and `eq:paper-W-carriers` for
    this layer and describes the rest as prose ("All carriers, forgetful maps,
    least-representative sections, and entry cases are explicitly ordered and
    computable", line 126--127), and prose is never cited as a statement.
  * `M_2` is the one exception, and it is declined for the **other** reason.
    The reader *does* display it, at `eq:paper-M2-definition`
    (`03-parameterized-construction.tex`, label line 297, display lines
    290--297), so "no reader display" would be false of it.  That locus is
    **already held** by `StageTwoRelaxed.stageTwo` under `STAGE2-MODULE-001`
    (whose own header, line 124, claims label line 297 with `stageTwo_apply`
    as its value equation and `stageTwo_rows_card`/`stageTwo_cols_card` as its
    two carriers).  Citing it again here would be the double assignment the
    reader-counterpart rule forbids, so the `M_2` field, its equation field
    `M₂_eq`, the receipts `levelTrace_M₂_apply`, `levelTrace_M₂_rowCarrier`,
    `levelTrace_M₂_rows`, `levelTrace_M₂_colCarrier`, `levelTrace_M₂_cols` and
    `Section5Admissibility.stepMTwo` all claim **no** reader item.
  * The rank injection `pi_alpha` of `T2` corresponds to no reader display
    either; the reader's only source-support statement,
    `eq:paper-source-support`, is the bound `|{i : v_i(alpha) = 1}| <= s`,
    which is **already assigned** to `GuardedSourceGraph.card_activeRows_le`
    by row `SOURCE-GRAPH-001` and to its slabbed refinement
    `GuardedSourceSlab.card_activeSlot_le` (declined there for the same
    reason).  No reader line is assigned twice, so `slotRank`, `slotEmbed` and
    the `pi` field claim none.

## Dependencies, imports, adapters

* `EthInapproximability.ParameterizedNP.GuardedSourceSlab` (banked, consumed by
  pin) and `EthInapproximability.ParameterizedNP.OneLevelAssembly` (banked,
  consumed by pin), the latter for `rowsCard`, `colsCard`, `bridgeCarriers`,
  `doubleInterlaceCarriers`, `levelOverhead`, `SeedInterface` and the promise
  label, plus Mathlib and the vendored `Workspace` / `NPCC` / `EthBridge`
  facades reached through `EthInapproximability.Prelude`.
* Imports reach `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`
  only.  `LegacyNPCC.Stage12` is **not** imported anywhere in this chain, so
  the cited AGHP balanced-family axiom is **not** in the closure of any
  declaration here.
* The banked modules supply, and this module never restates: `EndpointGraph`,
  `Inc`, `Row`, `Coord`, `SourceCommon`, `SourceYES`, `SourceNO`,
  `sourceYES_not_sourceNO`, `SlabRow`, `SlabCoord`, `guardedRow`, `q2`,
  `q2_pos`, `activeSlot`, `card_activeSlot_le`, `rankIn`, `K3`, `K4`,
  `k3_sourceYES`, `k4_sourceNO`, `k4_not_sourceYES`, `rowsCard`, `colsCard`,
  `bridgeCarriers`, `doubleInterlaceCarriers`, `levelOverhead`,
  `levelOverhead_eq`, `SeedInterface`, `SeedInterface.noReading`,
  `SeedInterface.yesReading`, `xOut`, `PromiseCase`,
  `Workspace.Types.Interlace.interlaceFun`, `Workspace.Types.CommComplexity.D`
  and `NPCC.LambdaGE`.
* External theorem adapters: **none are taken as axioms**, and none is needed;
  every declaration below is a record, an accessor, or an elementary fact about
  one.
* Proof status of every declaration: **new** (first transcription of
  `sec:level-records`, lines 13--318).

## Accessors carried as parameters, disclosed

`def:level-parameters` and `def:level-trace` are stated for a fixed
`(Public, K)` whose *derived accessors* -- `a`, `s`, `q`, `Q` and the Stage-1
matrix `M_1` -- are the deterministic straight-line program of
`sec:parameters` (frozen section 06), which is **not yet transcribed**.  This
module therefore carries `a`, `s`, `q`, `Q` and the remaining free carriers
as explicit parameters rather than computing them.  (Since `cc-t6z` the Stage-3
pair is **not** among them: `M_3`'s two carriers are forced by
`M_3 = Int_s(M_2^T)` and are no longer type parameters.  Since the `C₂c` round
the Stage-2 **column** carrier is not among them either: `07:224` sets
`Cols(M_2) = L_2` and `05:178` sets `L_2 = [N_2]`, so the field is typed at
`Fin Pr.N₂`, read off the record `Pi` the trace is already indexed by.  Since
the `cc-t7b` round the Stage-2 **row** carrier has gone the same way: `07:223`
sets `Rows(M_2) = [q_2] x C_1`, so the field is typed at
`Fin (q2 G s) x C₁` -- the banked guarded-source width `T1` and `T2` are already
stated at, times `M_1`'s own column carrier -- and `M_2` itself is no longer free
data but the value clause `07:225--226` evaluated at `M_1` and the stored family.
The five carriers that remain free are `C₁, RB, CB, RA, CA`.)  That is strictly
weaker than
the frozen text and never stronger: no declaration here asserts a value for any
of them, and no consumer may read a parameter schedule out of this module.  The
one accessor that *is* pinned is `q_2`, because the banked
`GuardedSourceSlab.q2` computes it from `(G,s)` alone; `def:level-parameters`
and `T1`/`T2` are therefore stated at the literal `q2 G s`, exactly as
`05:330--332` demands ("there is no stored value to compare against it").

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M1`/`M2`/`M4`: **no complexity, robustness, promise, colouring, packing,
  protocol or lower-bound field appears in any record here.**
  `LevelPublicInput` carries only the frozen `P1`--`P5` data together with the
  *promise-independent* predicate `SourceCommon`, which `05:29--35` explicitly
  makes a field; `YesCert` and `NoCert` are two **separate** `Prop`s outside
  the record, never conjoined (`yesCert_not_noCert` proves that conjoining them
  is inconsistent); `LevelConfig` holds six integers and their three
  inequalities; `LevelParams` holds `(K, N_2, c_2)` and the positivity of `N_2`
  that `05:183--186` calls structural, and no width, tolerance, multiplicity,
  capacity, ceiling or output-size field; `LevelTrace` holds the 23 components
  of `eq:one-level-trace-destructuring` and their defining equations, and
  `05:315` -- "No complexity, robustness, YES, or NO proposition is a field of
  the trace" -- is checkable as `levelTrace_promise_free`.
* `M3`: `slotRank`, `slotEmbed`, `rowKey`, `noSeed` are derived accessors; none
  restates a derived telescope as a bundle field.  In particular the trace does
  **not** carry `Rows(U)`, `Cols(U)`, `Rows(Int_Q(W))` or `Cols(Int_Q(W))` as
  data: `eq:trace-interlace-coordinate-carriers` holds **definitionally** here
  (`levelTrace_interlace_carriers`, closed by `rfl`), which is the strongest
  possible reading of "the literal carrier identifications".  The same applies
  to `Rows(M_3)` and `Cols(M_3)` since `cc-t6z`, to `Cols(M_2)` since the
  `C₂c` round, and to `Rows(M_2)` since `cc-t7b`: they are not type parameters
  but the forced `[s] x [N_2]`, `Fin s → ([q_2] x C_1)`, `[N_2]` and
  `[q_2] x C_1`, so `levelTrace_M₃_rowCarrier`, `levelTrace_M₂_colCarrier` and
  `levelTrace_M₂_rowCarrier` all close by `rfl`.
* `M5`/`M8`: both interlace widths are kept apart throughout -- `q` is the
  inner scale-alignment width and `Q` the outer bridge width, they appear in
  the four coordinate maps at their own carriers, and the overhead field `H`
  carries `log_2 q` and `log_2 Q` as separate summands.
* `M7`: nonemptiness is preserved -- `LevelPublicInput` carries the frozen
  `m_R > 0` and `n_R > 0` as the fields `mRpos`, `nRpos` (whence
  `publicInput_rows_nonempty`), `EndpointGraph` carries the two graph
  nonemptiness facts, and `LevelParams` carries `0 < N_2`.
* `M9`: the two promise branches are exhaustive-by-name and never merged; the
  frozen `T2` dichotomy real/padding coordinate is not re-derived here but
  consumed from the banked `card_activeSlot_le`.
* `M10`: every count is a `Finset.card` or a `Fintype.card` of a tagged
  carrier; `slotRank` counts inside the induced order on `I_alpha` and nowhere
  identifies two equal row vectors.

## Candidate encodings of `def:level-trace`

Two encodings of the 23-component record were built and raced.

* **Candidate A (landed).**  The derived matrices `M_3, N, U, W, R+` are fields
  typed at their **forced** carriers -- `N : Cols(A) -> Rows(A) -> Bool`,
  `U : ([q] x Cols(A)) -> ([q] -> Rows(A)) -> Bool`, and so on -- with the
  frozen equations `N = A^T`, `U = Int_q(N)`, `W = U^T`,
  `R+ = Int_Q(W)^T` as separate proof fields.
* **Candidate B (rejected).**  A bundled carrier record
  `BoolMatrix = (Row, Col, entry)` with `N, U, W, R+` as `BoolMatrix` fields
  and the equations as equalities of bundles.

Both compile.  Candidate B is shorter in the signature (four type parameters
instead of ten), but it **fails the discriminating battery item**: under B the
displayed identifications `Rows(U) = [q] x Rows(N)` and
`Cols(U) = Cols(N)^{[q]}` of `eq:trace-interlace-coordinate-carriers` are only
available after rewriting along the stored equation `U_eq`, so the four
coordinate fields of `eq:trace-interlace-coordinate-types` cannot even be
*typed* as the frozen display types them without a transport; under A they hold
by `rfl` (`levelTrace_interlace_carriers`) and the four coordinate fields are
typed letter-exactly.  Ranking (aux lemmas proved, faithfulness, length): A
wins the first two decisively and loses only on signature length.  The
candidate-B file is kept as scratch evidence at
`scratch/PublicRecordsCandidateB.lean` (gitignored), where the discriminating
item is left as the explicit unproved `Prop` `B_frozen_coordinate_types`.

## The Stage-3 equation field (`cc-t6z`) and its consumer sweep

Residue 1 of ledger row `S5-M3-ROWS-AUDIT-001` had two halves.  This round
closes the **first**: `M_3` was a bare field `R₃ → C₃ → Bool` over two
unconstrained carriers with no defining equation, so `rowsCard T.M₃` reduced to
`Fintype.card R₃` -- an arbitrary natural wearing an accessor's name, which is
what let a banked call site read `m_3` off it.  `M_3` now carries the frozen
`M₃_eq : M₃ = Int_s(M_2^T)` (`07:450`, `07:497`) at the forced carrier
`[s] x Rows(S_2) = [s] x Cols(M_2)` (`08:262--263` with `03:112--114`),
following the structure's own `U_eq`/`W_eq`/`Rnext_eq` pattern exactly: an
equation field on a type-forced matrix, no positivity side condition (the frozen
`p >= 1` of `def:interlace` is carried by the schedule, not by the record --
`U_eq` and `Rnext_eq` carry none either, and adding one here would demand more
than the paper).  The **second** half -- `C₂c = L_2 = [N_2]` -- is closed by the
`C₂c` round recorded in the next section.

The two type parameters `R₃, C₃` therefore leave `LevelTrace`.  The consumer
sweep was run over `src/` **before** the edit, in both polarities, and every
consumer is restated inside this round:

* *type-argument polarity* (`LevelTrace ... R₃ C₃ ...` in a signature):
  `PublicRecords` itself (the structure, its `LevelTrace`-namespace `variable`
  block, `traceWitness`); `OneLevelTheorem` (three `variable` blocks, ten
  applications, `bridgeWidthTrace`); `Section5Admissibility`
  (`partialTailAssembler` and its `AssemblerFacts` block with four call sites,
  `WFTraceCarriers`, `wfTraceCarriers_output_pos`, `wfTraceCarriers_at_assembler`,
  `WFGroupPartialAtTrace`, `AdmissiblePartialAtTrace` and its `AdmissibleFacts`
  block, `scheduleContextProbe_bundle_refuted`);
  `ExtensionCallInhabitation` (`fourPaperCalls_at_admissiblePartial`);
  `IterationDifferenceWiring` (`AdmissibleLevel`'s two carrier fields and their
  two `Fintype` fields, the `attribute [instance]` list, its `T` field,
  `probeTrace`, `probeAdmissibleLevel`).
* *value polarity* (a declaration supplying or reading `M₃`):
  `Section5Admissibility.partialTailAssembler`'s `M₃` input, which becomes the
  computed `stepMThree M₂ (sOf C)` in the `stepN`/`stepU`/`stepW`/`stepRnext`
  family, and its two downstream binders; the `0 < rowsCard T.M₃` and
  `0 < colsCard T.M₃` clauses of `WFTraceCarriers` (`05:425--434`), which keep
  their frozen wording and are now discharged at the derived carriers; and the
  three trace inhabitants `PublicRecords.traceWitness`,
  `OneLevelTheorem.bridgeWidthTrace`, `IterationDifferenceWiring.probeTrace`,
  each of which now supplies the interlace and closes `M₃_eq` by `rfl`.

The boundary is five modules and did not explode, so no PARK report is filed.
No banked *statement* is weakened: every migrated declaration keeps its
conclusion, and the three `WF` positivity clauses are unchanged text.

## The `C₂c` identification and its consumer sweep

This round closes the **second** half of Residue 1 of `S5-M3-ROWS-AUDIT-001`.
`M_2`'s column carrier was the free type parameter `C₂c`, so `colsCard T.M₂`
reduced to `Fintype.card C₂c` -- again an arbitrary natural wearing an
accessor's name (`Section5Admissibility.rowsCard_of_fin_carrier` shows such a
readout realizes every natural), and consequently `levelTrace_M₃_rows` could
only say `s |Cols(M_2)|` rather than the paper's `s N_2`.

The frozen text fixes that carrier outright, in two displays that live in
**different sections**: `eq:stage2-relaxed-value` prints
`Cols(M_2) = L_2` at `07:224`, and `def:level-parameters` prints `L_2 = [N_2]`
at `05:178`.  The trace is already indexed by the record `Pi` that carries
`N_2`, so the identification is available as a **carrier forcing**, not as an
equation field: `M₂ : R₂ → Fin Pr.N₂ → Bool`, with `[N_2]` read zero-based per
`conv:finite-slots`.

**Why forcing rather than an equation field.**  Both were considered, as the
`U_eq`-pattern fallback the charter names.  An equation field would have to say
`C₂c ≃ Fin Pr.N₂` (a stored equivalence) or `Fintype.card C₂c = Pr.N₂` (a
stored count).  A stored *count* is strictly weaker than the frozen display --
it says the carrier has the right size, not that it **is** `L_2`, so the four
Stage-2 slot indices of `eq:stage2-relaxed-value`'s value clause would still
have to be transported.  A stored *equivalence* would be a bundle field
restating a derived telescope, and would additionally make
`levelTrace_M₂_colCarrier` fail to close by `rfl`.  The consumer sweep found no
declaration that needs `C₂c` to be anything other than `[N_2]`, so forcing is in
licence and is what landed: `Fintype.card C₂c = Pr.N₂` is now the **theorem**
`levelTrace_M₂_cols`, with the `rfl` receipt `levelTrace_M₂_colCarrier` beside
it, and `levelTrace_M₃_rows` upgrades from `s |Cols(M_2)|` to the paper's
`s N_2`.

The type parameter `C₂c` and its `Fintype` instance therefore leave
`LevelTrace`.  The consumer sweep was run over `src/` **before** the edit, in
both polarities, and every consumer is restated inside this round:

* *type-argument polarity* (`LevelTrace ... C₂c ...` in a signature, or a
  `C₂c` binder feeding one): `PublicRecords` itself (the structure, its
  `LevelTrace`-namespace `variable` block, `levelTrace_M₃_apply`,
  `levelTrace_M₃_rowCarrier`, `traceWitness`); `OneLevelTheorem` (three
  `variable` blocks, ten applications, `bridgeWidthTrace`);
  `Section5Admissibility` (`stepMThree`, `partialTailAssembler` and its
  `AssemblerFacts` block with four call sites, `WFTraceCarriers`,
  `wfTraceCarriers_output_pos`, `wfTraceCarriers_at_assembler`,
  `WFGroupPartialAtTrace`, `AdmissiblePartialAtTrace` and its `AdmissibleFacts`
  block, `rowsCard_stageThree_of_stageTwo`, `stageThreeRows_ne_mThree`,
  `scheduleContextProbe_bundle_refuted`); `ExtensionCallInhabitation`
  (`fourPaperCalls_at_admissiblePartial`); `IterationDifferenceWiring`
  (`AdmissibleLevel`'s `C₂c` field and its `Fintype` field, the
  `attribute [instance]` list, its `T` field, `probeTrace`,
  `probeAdmissibleLevel`).
* *value polarity* (a declaration supplying or reading `M₂`, or reading
  `Fintype.card C₂c`): `Section5Admissibility.partialTailAssembler`'s `M₂`
  input and the two downstream binder blocks that mirror it; the five
  `Fintype.card C₂c` readings inside `AdmissiblePartialAtTrace`,
  `admissiblePartial_stage3`, `admissiblePartial_iff`,
  `admissiblePartial_gap_reduces_to_eight` and (in the `cc-t7a` r0 bytes only)
  `admissiblePartial_forces_colsM2_pos`, which become the one term `Pr.N₂` --
  the same term the other four `m_3`/`N_2` positions of the conjunction already
  carry; the `0 < colsCard T.M₂` clause of `WFTraceCarriers` (`05:425--434`),
  which keeps its frozen wording and is now discharged at the forced carrier;
  and the three trace inhabitants `PublicRecords.traceWitness`,
  `OneLevelTheorem.bridgeWidthTrace`,
  `IterationDifferenceWiring.probeTrace`, whose `M₂` slot moves from
  `witnessBase : Bool → Bool → Bool` to `witnessM₂ : Bool → Fin 2 → Bool` at
  `paramsWitness`'s own `N_2 = 2`.

**Claim Check, itemized** (the `cc-t7a` r0 wording of this paragraph was
FALSE -- it said every non-listed declaration was byte-identical "modulo the
deleted `C₂c` token", which under-reports a *term* substitution inside four
statements; `cc-t7a-r1` repairs it, Sol finding `F3`):

1. **Two conclusions re-typed at the forced carrier, neither weakened.**
   `levelTrace_M₃_rows` (`s |Cols(M_2)| -> s Pr.N₂`, an upgrade to the paper's
   own parameter, the two being equal by `levelTrace_M₂_cols`) and the
   rejection probe `stageThree_equation_is_a_restriction` (re-typed at
   `Fin 4 x Fin 2`, claiming no legality either way).
2. **Four statements substitute one *term* for another** -- the term
   `Fintype.card C₂c` becomes the term `Pr.N₂` -- which is a substitution
   licensed by the forcing, **not** the deletion of a type token:
   `Section5Admissibility.AdmissiblePartialAtTrace`, `admissiblePartial_stage3`,
   `admissiblePartial_iff` and `admissiblePartial_gap_reduces_to_eight`.  The
   two terms are provably equal (`levelTrace_M₂_cols`), so no statement is
   weakened; but the edit is a rewrite of the statement, and this paragraph now
   says so.  A fifth declaration,
   `Section5Admissibility.admissiblePartial_forces_colsM2_pos`, carried the same
   substitution in the r0 bytes and is **deleted** at `cc-t7a-r1` (item 4).
3. **One hypothesis dropped, conclusion unchanged.**
   `Section5Admissibility.wfTraceCarriers_at_assembler` loses `[Nonempty C₂c]`,
   because `Fin Pr.N₂` is nonempty by the structural `Pr.N₂pos` (`05:183--186`).
   A dropped hypothesis is a strengthening, never a weakening.
4. **One declaration deleted and replaced** at `cc-t7a-r1`:
   `admissiblePartial_forces_colsM2_pos` (a trace-specialized restatement of
   `Pr.N₂pos`, whose hypothesis was inessential) gives way to the general
   `Section5Admissibility.stage3Group_forces_colsM2_pos`, which states the
   surviving gate content where the width is genuinely free.
5. **Everything else** keeps its statement byte-identical modulo the deleted
   `C₂c` binder token.

The boundary is five modules and did not explode, so no PARK report is filed.

## The `M_2` value clause (`cc-t7b`) and its consumer sweep

The `C₂c` round closed `Cols(M_2)`; this round closes the rest of
`eq:stage2-relaxed-value`.  `M_2` was still a bare field over an unconstrained
row carrier `R₂` with **no defining equation**, so `rowsCard T.M₂` reduced to
`Fintype.card R₂` -- the same defect shape `cc-t6z` removed from `M_3` -- and,
worse, every *entry* of `M_2` was free: a trace could name any Boolean table at
those carriers and satisfy `T3`, so no consumer could read the frozen
`M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)` off the record at all.

The frozen display fixes all three lines at once (`07:221--229`).  Two of them
are carrier identifications and one is a value clause, and they are landed in the
two different ways the charter distinguishes:

* `Rows(M_2) = [q_2] x C_1` (`07:223`, reprinted at `07:528`) is a **carrier
  forcing**, for exactly the reasons the `C₂c` round recorded for the column
  side: a stored equivalence would be a bundle field restating a derived
  telescope and would make `levelTrace_M₂_rowCarrier` fail to close by `rfl`,
  and a stored *count* would say the carrier has the right size rather than that
  it **is** `[q_2] x C_1`, leaving the value clause's two slot indices to be
  transported.  Both factors are already available to the record: `[q_2]` is the
  banked `Fin (q2 G s)` that `T1`, `T2` and the stored family are stated at, and
  `C_1` is `M_1`'s own column carrier, a type parameter the record already
  carries.
* `M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)` (`07:225--226`) is an
  **equation field** `M₂_eq`, following the structure's own
  `U_eq`/`W_eq`/`Rnext_eq`/`M₃_eq` pattern exactly: an equation on a type-forced
  matrix, no side condition (the frozen balancedness of `C_2` is carried by the
  admissibility predicate, not by the record -- `05:186--189` is explicit that it
  "is not a proof field of `Pi`", and adding it here would demand more than the
  paper).  The right-hand side is the vendored `NPCC.relaxedInterlace` of
  `def:relaxed-interlace` applied to `M_1^T` and the trace's own `C_2`, which is
  the frozen sentence `07:217` read literally; nothing is restated and no fresh
  constructor is written.

So the type parameter `R₂` and its `Fintype` instance leave `LevelTrace`, and the
Stage-2 matrix ceases to be *unconstrained* data: `M₂` remains a data field, at a
now-forced carrier pair, but `M₂_eq` pins every one of its entries, exactly as
`M₃_eq` does for `M₃`.  The acceptance probe is
`levelTrace_M₂_apply`: `T.M₂ (alpha, gamma) l` reduces through the equation to
`T.M₁ (Pr.c₂ l alpha) gamma`, i.e. to the `M_1` composition, with `Pi`'s stored
family reached through `C₂_eq` and nothing else.

The consumer sweep was run over `src/` **before** the edit, in both polarities,
and every consumer is restated inside this round:

* *type-argument polarity* (`LevelTrace ... R₂ ...` in a signature, or an `R₂`
  binder feeding one): `PublicRecords` itself (the structure, its
  `LevelTrace`-namespace `variable` block, `levelTrace_M₃_apply`, `traceWitness`);
  `OneLevelTheorem` (three `variable` blocks, ten applications,
  `bridgeWidthTrace`); `Section5Admissibility` (`partialTailAssembler` and its
  `AssemblerFacts` block with four call sites, `WFTraceCarriers`,
  `wfTraceCarriers_output_pos`, `wfTraceCarriers_at_assembler`,
  `WFGroupPartialAtTrace`, `AdmissiblePartialAtTrace` and its `AdmissibleFacts`
  block, `scheduleContextProbe_bundle_refuted`); `ExtensionCallInhabitation`
  (`fourPaperCalls_at_admissiblePartial`); `IterationDifferenceWiring`
  (`AdmissibleLevel`'s `R₂` field and its `Fintype` field, the
  `attribute [instance]` list, its `T` field, `probeTrace`,
  `probeAdmissibleLevel`).  The two general helpers
  `Section5Admissibility.rowsCard_stageThree_of_stageTwo` and
  `.stageThreeRows_ne_mThree` bind their **own** `R₂ C₂c` and are *not*
  consumers; they are untouched.
* *value polarity* (a declaration supplying or reading `M₂`):
  `Section5Admissibility.partialTailAssembler`'s `M₂` input, which becomes the
  computed `stepMTwo M₁ Pr.c₂` in the same `stepMThree`/`stepN`/`stepU` family
  (and feeds `stepMThree` in turn), together with its two downstream binder
  blocks; the `0 < rowsCard T.M₂` clause of `WFTraceCarriers` (`05:425--434`),
  which keeps its frozen wording and is now discharged at the forced carrier;
  and the three trace inhabitants `PublicRecords.traceWitness`,
  `OneLevelTheorem.bridgeWidthTrace`, `IterationDifferenceWiring.probeTrace`,
  whose `M₂` slot moves from the chosen table `witnessM₂ : Bool → Fin 2 → Bool`
  to the **computed** `witnessM₂ = relaxedInterlace witnessBase^T c_2` at the
  forced carriers, closing `M₂_eq` by `rfl`.

**Claim Check, itemized.**

1. **One conclusion re-typed at the forced carriers, not weakened.**  The
   rejection probe `stageThree_equation_is_a_restriction` moves its column
   carrier from `Fin 4 → Bool` to `Fin 4 → Fin (q2 K3 4) × Bool` and its
   falsifying point accordingly, because the field it probes now lives at the
   forced `Rows(M_2)^{[s]}`.  It claims no legality either way.
2. **One hypothesis dropped, conclusion unchanged.**
   `Section5Admissibility.wfTraceCarriers_at_assembler` loses `[Nonempty R₂]`,
   because `Fin (q2 G s) × C₁` is nonempty by the banked `q2_pos` together with
   the `[Nonempty C₁]` the same declaration already assumes.  A dropped
   hypothesis is a strengthening, never a weakening.
3. **One input removed from a constructor, output unchanged.**
   `partialTailAssembler` no longer takes `M₂`; it computes it, exactly as
   `cc-t6z` made it compute `M₃`.  Its output type and all four `AssemblerFacts`
   conclusions are unchanged.
4. **One probe input retyped and recomputed.**  `witnessM₂` moves from the
   *chosen* table `Bool → Fin 2 → Bool` to the *computed*
   `Fin (q2 K3 4) × Bool → Fin 2 → Bool`, defined as the relaxed interlace of
   `witnessBase^T` by `paramsWitness`'s own `c_2`.  It is an input to the three
   probes, never a claim; the change replaces a self-chosen table by the frozen
   display evaluated at objects the round already banked.
5. **One nondegeneracy restated, strictly more general.**
   `witnessM₂_nonconstant` moves from the two points `(true, 1)`/`(true, 0)` of
   the old table to `(α, true) 0`/`(α, false) 0` **universally quantified over
   `α`**, because the row carrier gained the `[q_2]` factor.  Universal `α` is a
   strengthening: the old statement was one instance, the new one is all of
   them, and the probe no longer has to pick a source coordinate.
6. **Everything else** keeps its statement byte-identical modulo the deleted
   `R₂` binder token and, at the three probes, the deleted `M₂` argument.

The boundary is five modules and did not explode, so no PARK report is filed.

## Aux-lemma battery

Every battery item below is proved; nothing is stated and left open.

* `A1` the induced order on the slabbed row carrier (4): `vertexKey_injective`,
  `rowKey0_injective`, `rowKey_injective`, `rowKey_lt_trichotomy`.
* `A2` the frozen zero-based rank injection of `T2` (5):
  `slotRank_strictMono`, `slotRank_injOn`, `slotRank_lt_card`, `slotRank_lt`,
  `slotEmbed_injective`.
* `A3` the public input and its two certificates (6): `yesCert_iff_reading`,
  `noCert_iff_reading`, `yesCert_not_noCert`, `publicInput_one_le_D`,
  `publicInput_card_vertex_le`, `publicInput_rows_nonempty`.
* `A4` the universal configuration (3): `levelConfig_cb_pos`,
  `levelConfig_cb_ne_five`, `levelConfig_Cin_unconstrained`.
* `A5` the parameter record (3): `levelParams_card_family`,
  `levelParams_ext_c2`, `levelParams_index_nonempty`.
* `A6` the trace's derived-matrix tail (5): `levelTrace_W_eq_bridge`,
  `levelTrace_Rnext_eq_bridge`, `levelTrace_Rnext_eq_double`,
  `levelTrace_interlace_carriers`, `levelTrace_coordinate_equations`.
* `A7` the trace's public integers and duplication maps (5):
  `levelTrace_W_carriers`, `levelTrace_carrier_recurrence`,
  `levelTrace_H_eq_levelOverhead`, `levelTrace_rA_injective`,
  `levelTrace_fA_surjective`.
* `A8` the pinned width `q_2` inside `H` (2): `log_q2`, `overhead_at_powers`.
* `A9` the Stage-3 scale-alignment field, new at `cc-t6z` (5):
  `levelTrace_M₃_apply`, `levelTrace_M₃_rowCarrier`, `levelTrace_M₃_rows`,
  `levelTrace_M₃_cols`, `levelTrace_M₃_determined`.
* `A10` the forced Stage-2 column carrier, new at the `C₂c` round (2):
  `levelTrace_M₂_colCarrier` (the `rfl` receipt), `levelTrace_M₂_cols` (the
  numeric identification `|Cols(M_2)| = N_2`).
* `A11` the Stage-2 value clause and its row carrier, new at `cc-t7b` (5):
  `levelTrace_M₂_apply` (the acceptance probe: `T.M₂` reduces through the
  equation to the `M_1` composition), `levelTrace_M₂_rowCarrier` (the `rfl`
  receipt), `levelTrace_M₂_rows` (`|Rows(M_2)| = q_2 |C_1|`),
  `levelTrace_M₂_determined` and `levelTrace_M₃_reduces_to_stageOne` (the two
  Stage equations composed down to `M_1`).

That is **45/45 proved** across eleven groups, with `0` unproved.  The battery is
accompanied by the module's non-vacuity, statement-pole and pinning theorems,
which include the three `cc-t6z` additions `traceWitness_M₃_rows`,
`traceWitness_mThree_eq_N₂` and `stageThree_equation_is_a_restriction`, the
`C₂c` round's `witnessM₂_nonconstant`, and `cc-t7b`'s
`stageTwo_value_clause_is_a_restriction` and `traceWitness_M₂_rows`.

## Non-vacuity and statement poles

* `LevelPublicInput` is inhabited **twice at legal, nondegenerate values**, on
  the two promise branches separately and never conjoined:
  `publicInputYes` (`K_3`, `gamma = 1/6`, `Delta = 3`, `D = 3`, `Y = 0`,
  `b_0 = bout = 1`, `R` a genuinely two-valued `2 x 2` matrix) and
  `publicInputNo` (`K_4`, same legal constants).  Both discharge the hardest
  field, `SourceCommon`, at real degree data rather than at an empty graph.
* `YesCert` is inhabited **in full** -- both conjuncts -- by
  `publicInputConst_yesCert`: the source half is `k3_sourceYES` and the
  complexity half is the kernel-checked `D (fun _ _ => false) = 0` at the legal
  budget `Y = 0`.  So the `YES` certificate is not an empty predicate.
* `NoCert` is **not** inhabited outright, and the gap is disclosed rather than
  papered over.  Its source half is inhabited (`publicInputNo_sourceNO`,
  `K_4`), and `noCert_not_automatic` shows it is not a tautology, but its two
  complexity conjuncts are exactly the banked `SeedInterface.noReading` --
  `noCert_iff_reading` proves that identification in the kernel -- whose
  witness is the route's Stage-1 hard seed, still **Lean pending**.
  `noCert_of_reading` localizes the deferral to exactly that obligation, and
  `noCert_complexity_conjuncts_consistent` checks in the kernel that the two
  complexity conjuncts are **jointly satisfiable** -- at the banked full-cube
  seed, `comp R = 8 >= 3` and `8 <= Lambda_3(R,1,2^{-0},3/5)` -- so `NoCert` is
  not a hidden contradiction.  What blocks promoting that pair to a full
  `NoCert` inhabitant is disclosed: the banked `Lambda` bound is proved at
  requested depth `0`, while `P5` demands `b_0 > 0`, and the banked module
  carries the same range restriction for its own seed.  Fabricating an
  inhabitant would mean asserting an exact deterministic complexity and a
  `Lambda_3` lower bound this repository has not proved, so the honest record
  is: `NoCert` is a faithful transcription whose realizability at a legal
  positive depth is deferred, and **no** consumer may read a `NO` certificate
  out of this module.
* `LevelConfig` is inhabited at the frozen **boundary** (`levelConfigMin`,
  `c_b = 6` exactly, `C_in = 0`) and at nondegenerate interior values
  (`levelConfigWitness`).  `levelConfig_cb_ne_five` records that the `c_b >= 6`
  guard genuinely bites.
* `LevelParams` is inhabited by `paramsWitness` at `N_2 = 2` with a family that
  is **not constant** (`paramsWitness_c2_nonconstant`), and
  `levelParams_admits_unbalanced_family` exhibits a legal `Pi` whose family is
  constant, hence maximally unbalanced -- the kernel-checked form of the frozen
  sentence "the balancedness formula ... is not a proof field of `Pi`".  A
  record that secretly forced balancedness would make that inhabitant
  impossible.
* `LevelTrace` is inhabited by `traceWitness` at values legal **for the bare
  trace record** -- and, since `cc-t6z`, explicitly **NON-FIDELITY** for the
  frozen schedule: `06:975` requires `64 | s` (hence `s >= 64`) and
  `06:966--967` requires `N_2 >= 2s`, while the witness runs at `s = 4` and
  `N_2 = 2`.  Canonical scheduled inhabitation therefore stays **deferred** and
  registered, not discharged, exactly as for the other NON-FIDELITY probes in
  this campaign; what the witness does establish is that the record's own field
  and clause system is satisfiable and nondegenerate.  At those values
  (`G = K_3`, `s = 4`, `a = 6`, `q = Q = 2`) it has a **genuinely proper** protected
  duplication: `traceWitness_A_rows` gives `|Rows(A)| = 2|Rows(B)|` and
  `traceWitness_fArow_not_injective` shows the label-forgetting map really
  forgets, so the record is not inhabited only at the degenerate `A = B`.  The
  base matrices are two-valued (`traceWitness_B_nonconstant`, and
  `witnessM₂_nonconstant` for the Stage-2 slot at its forced carrier), so no
  field is satisfied by a constant, and `traceWitness_carriers` pins the two
  output cardinalities at their exact frozen values `16` and `32`.
  Since the `C₂c` round the witness's `N_2 = 2` is doing real work: it is the
  size of the Stage-2 column carrier as well as the length of the family, and
  `traceWitness_mThree_eq_N₂` is that identity evaluated here.
* **Statement pole for `T2`.**  The trivial witness for "a typed injection
  `I_alpha -> [s]`" is a constant map; `slotRank_not_constant` proves it fails
  the frozen equation `pi_alpha(i) = |{h in I_alpha : h < i}|` whenever
  `|I_alpha| >= 2`.  So `T2` is a constraint, not a naming convention.
* **Statement pole for `T3`'s Stage-3 field.**  The trivial candidate for a
  matrix at `M_3`'s carriers is a constant; `stageThree_equation_is_a_restriction`
  exhibits one that fails `M₃_eq` at a single point (its `4` is the banked
  witness's own `s` and its `2` the banked `N_2`, and it claims no legality --
  it is a rejection probe), and
  `levelTrace_M₃_determined` shows the equation pins `M_3` from `M_2` alone.  So
  the field is a constraint rather than a naming convention, and
  `traceWitness_M₃_rows` pins the witness's row count at the frozen
  `s N_2 = 8` rather than at a free carrier's cardinality.
* **Statement pole for `T3`'s Stage-2 value clause.**  The trivial candidate for
  a matrix at `M_2`'s carriers is a constant;
  `stageTwo_value_clause_is_a_restriction` exhibits one that fails `M₂_eq` at a
  single point (its carriers are the banked witness's own, and it claims no
  legality -- it is a rejection probe), and `levelTrace_M₂_determined` shows the
  equation pins `M_2` from `M_1` alone.  So the field is a constraint rather than
  a naming convention, and no trace may name an arbitrary Stage-2 table:
  `levelTrace_M₂_apply` reads every entry of `M_2` back as an entry of `M_1`.
* **Statement pole for `T3`'s Stage-2 column carrier.**  A record whose
  `Cols(M_2)` were free would let `|Cols(M_2)|` be any natural at all
  (`Section5Admissibility.rowsCard_of_fin_carrier`), so no consumer could read
  the frozen `m_3 = N_2` off the trace.  With the carrier forced, the trivial
  reading is impossible: `levelTrace_M₂_cols` proves `|Cols(M_2)| = N_2` for
  **every** trace, and there is no trace at all whose Stage-2 column count
  differs from its own record's `N_2`.  That is a statement no equation-free
  encoding of this field can make.
* **Statement pole for `T3`--`T5`.**  A record whose derived tail were
  unconstrained would be satisfied by arbitrary matrices;
  `levelTrace_tail_determined` proves that two traces over the same `A` at the
  same widths have equal `N, U, W, R+`, i.e. the four equations pin the tail
  uniquely.
* **Statement pole for `T1`.**  `levelTrace_S_pinned` proves the guarded-source
  field is the banked `guardedRow G s` on the nose, so no trace may substitute
  a promise-specific source; `levelTrace_C2_pinned` does the same for the
  Stage-2 family, which is the frozen "`LevelStep` never chooses a
  replacement".
* **Promise-freedom.**  `levelTrace_promise_free` supplies a `PromiseCase`
  argument to a trace and gets the same trace back, and the banked
  `promiseFreedom_not_automatic` records that a function of `PromiseCase` need
  not be constant, so the discard is content rather than notation.
-/

namespace EthInapproximability.ParameterizedNP.PublicRecords

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open NPCC

/-! ## Part 1: the induced order on the guarded-source rows

`T2` reads `I_alpha = {i in I(S) : v_i(alpha) = 1}`, *"in its induced order"*,
and then defines `pi_alpha(i) = |{h in I_alpha : h < i}|`.  The banked slab
module already supplies `I_alpha` as `activeSlot G s alpha` and the bound
`|I_alpha| <= s`; what is missing there is the order on the **row** carrier
`I(G,s) = [4s] x (V u [s-3])`, since the banked lexicographic keys order the
*coordinate* carrier.  The three keys below are the row-side mirror of the
banked `edgeKey`/`coordKey`/`realKey`, built from the same `rankIn` and the
same tagged-sum convention (left summand first), and `zero`-based throughout
per `conv:finite-slots`. -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The zero-based rank of a vertex in `G`'s own linear order on `V`. -/
def vertexKey (G : EndpointGraph V E) (u : V) : ℕ := rankIn G.orderV u

/-- **Aux `A1.1`.**  The vertex key is injective; general in `G`. -/
theorem vertexKey_injective (G : EndpointGraph V E) :
    Function.Injective (vertexKey G) :=
  rankIn_injective G.orderV

/-- The lexicographic key of an unslabbed row of `I_0(G,s) = V u [s-3]`: the
tagged sum is ordered with `V` first, matching the banked `Coord` convention. -/
def rowKey0 (G : EndpointGraph V E) (s : ℕ) : Row V s → ℕ ×ₗ ℕ
  | Sum.inl u => toLex (0, vertexKey G u)
  | Sum.inr k => toLex (1, (k : ℕ))

/-- **Aux `A1.2`.**  The unslabbed row key is injective; general in `G` and
`s`. -/
theorem rowKey0_injective (G : EndpointGraph V E) (s : ℕ) :
    Function.Injective (rowKey0 G s) := by
  rintro (u | k) (u' | k') h <;>
    simp only [rowKey0, toLex_inj, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (vertexKey_injective G h.2)
  · exact absurd h.1 (by norm_num)
  · exact absurd h.1 (by norm_num)
  · exact congrArg Sum.inr (Fin.ext h.2)

/-- The displayed lexicographic key of a slabbed row `(r,i) in [4s] x I_0`. -/
def rowKey (G : EndpointGraph V E) (s : ℕ) (x : SlabRow V s) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex ((x.1 : ℕ), rowKey0 G s x.2)

/-- **Aux `A1.3`.**  The slabbed row key is injective, so it induces a linear
order on `I(G,s)`; general in `G` and `s`. -/
theorem rowKey_injective (G : EndpointGraph V E) (s : ℕ) :
    Function.Injective (rowKey G s) := by
  rintro ⟨r, i⟩ ⟨r', i'⟩ h
  simp only [rowKey, toLex_inj, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (rowKey0_injective G s h.2)

/-- **Aux `A1.4`.**  The induced order is a genuine linear order: any two rows
are comparable, and equal keys mean equal rows.  General in `G` and `s`. -/
theorem rowKey_lt_trichotomy (G : EndpointGraph V E) (s : ℕ)
    (x y : SlabRow V s) :
    rowKey G s x < rowKey G s y ∨ x = y ∨ rowKey G s y < rowKey G s x := by
  rcases lt_trichotomy (rowKey G s x) (rowKey G s y) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (rowKey_injective G s h))
  · exact Or.inr (Or.inr h)

/-- **The frozen zero-based rank of `T2`**, `pi_alpha(i) = |{h in I_alpha :
h < i}|` (05:246--248), taken in the induced order on `I_alpha`. -/
def slotRank (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s))
    (i : SlabRow V s) : ℕ :=
  ((activeSlot G s α).filter fun h => rowKey G s h < rowKey G s i).card

/-- **Aux `A2.1`.**  The rank is strictly monotone on `I_alpha`. -/
theorem slotRank_strictMono (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s))
    {i j : SlabRow V s} (hi : i ∈ activeSlot G s α)
    (hij : rowKey G s i < rowKey G s j) :
    slotRank G s α i < slotRank G s α j := by
  classical
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro h hh
    rw [Finset.mem_filter] at hh ⊢
    exact ⟨hh.1, lt_trans hh.2 hij⟩
  · intro hsub
    have hmem : i ∈ (activeSlot G s α).filter fun h => rowKey G s h < rowKey G s j :=
      Finset.mem_filter.mpr ⟨hi, hij⟩
    have := hsub hmem
    rw [Finset.mem_filter] at this
    exact absurd this.2 (lt_irrefl _)

/-- **Aux `A2.2`.**  The rank is injective on `I_alpha`, so `pi_alpha` really
is an injection and not merely a map. -/
theorem slotRank_injOn (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s))
    {i j : SlabRow V s} (hi : i ∈ activeSlot G s α) (hj : j ∈ activeSlot G s α)
    (h : slotRank G s α i = slotRank G s α j) : i = j := by
  rcases rowKey_lt_trichotomy G s i j with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (slotRank_strictMono G s α hi hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (slotRank_strictMono G s α hj hgt))

/-- **Aux `A2.3`.**  The rank of a member of `I_alpha` is below `|I_alpha|`:
this is the "rank equivalence `I_alpha = [|I_alpha|]`" half of 05:249--251. -/
theorem slotRank_lt_card (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s))
    {i : SlabRow V s} (hi : i ∈ activeSlot G s α) :
    slotRank G s α i < (activeSlot G s α).card := by
  classical
  have hsub :
      ((activeSlot G s α).filter fun h => rowKey G s h < rowKey G s i)
        ⊆ (activeSlot G s α).erase i := by
    intro h hh
    rw [Finset.mem_filter] at hh
    refine Finset.mem_erase.mpr ⟨fun hc => ?_, hh.1⟩
    exact absurd (hc ▸ hh.2) (lt_irrefl _)
  have h1 := Finset.card_le_card hsub
  have h2 : ((activeSlot G s α).erase i).card = (activeSlot G s α).card - 1 :=
    Finset.card_erase_of_mem hi
  have h3 : 0 < (activeSlot G s α).card := Finset.card_pos.mpr ⟨i, hi⟩
  rw [slotRank]
  omega

/-- **Aux `A2.4`.**  Composed with the banked `lem:guarded-source-active-slot`,
the rank lands in `[s]`: this is the "followed by the initial-segment inclusion
`[|I_alpha|] -> [s]`" half of 05:249--251.  The banked bound is *consumed*,
never restated. -/
theorem slotRank_lt (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) {i : SlabRow V s} (hi : i ∈ activeSlot G s α) :
    slotRank G s α i < s :=
  lt_of_lt_of_le (slotRank_lt_card G s α hi) (card_activeSlot_le G hs α)

/-- **The typed rank injection `pi_alpha : I_alpha -> [s]` of `T2`.**  It stores
no arbitrary injection witness: the value is the frozen rank formula and the
target bound is the banked active-slot lemma. -/
def slotEmbed (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s) (α : Fin (q2 G s))
    (i : {i : SlabRow V s // i ∈ activeSlot G s α}) : Fin s :=
  ⟨slotRank G s α i.1, slotRank_lt G hs α i.2⟩

@[simp] theorem slotEmbed_val (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) (i : {i : SlabRow V s // i ∈ activeSlot G s α}) :
    (slotEmbed G hs α i : ℕ) = slotRank G s α i.1 := rfl

/-- **Aux `A2.5`.**  `pi_alpha` is injective. -/
theorem slotEmbed_injective (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) : Function.Injective (slotEmbed G hs α) := by
  intro i j h
  have hval : slotRank G s α i.1 = slotRank G s α j.1 := congrArg Fin.val h
  exact Subtype.ext (slotRank_injOn G s α i.2 j.2 hval)

/-- **Statement pole for `T2`.**  The trivial witness for "some typed injection
`I_alpha -> [s]`" is a constant map.  It fails the frozen rank equation as soon
as `I_alpha` has two elements, so `T2` constrains the trace rather than naming
a choice. -/
theorem slotRank_not_constant (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s))
    (h2 : 2 ≤ (activeSlot G s α).card) :
    ¬ ∃ c : ℕ, ∀ i ∈ activeSlot G s α, slotRank G s α i = c := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
  exact hij (slotRank_injOn G s α hi hj ((hc i hi).trans (hc j hj).symm))

/-! ## Part 2: the one-level public input

`def:level-public-input`, 05:12--51.  Clauses `P1`--`P5` and nothing else: the
closing sentence 05:45--46, "No promise bit, colouring, packing, protocol,
lower-bound proof, or robustness proof is a field of `Public`", is what makes
`YesCert` and `NoCert` separate definitions in Part 3 rather than fields.
`GuardedSource(G,s)` is deliberately absent (05:47--50), and indeed no field
below mentions `s`. -/

/-- **A one-level public input** (`def:level-public-input`, label line 13).

Reader counterpart: `03-parameterized-construction.tex:53--58`, the public data
of `thm:paper-parameterized-one-bit`.

The frozen tuple is
`Public = (N_V, N_E, bd_0, bd_1, m_R, n_R, R, gamma, Delta, D, Y, b_0, bout)`.
Clause `P1` -- the two carriers, their nonemptiness, the two endpoint maps, and
looplessness -- is exactly the banked `EndpointGraph`, which also carries the
two canonical orders `05:42--44` requires, and is **consumed by pin**; clause
`P2` is the triple `(gamma, Delta, SourceCommon)`, whose predicate is the
banked promise-independent one; clause `P3` is `(m_R, n_R, R)` at the frozen
zero-based carriers `X_R = [m_R]`, `Y_R = [n_R]` with `m_R, n_R > 0`, so the
two matrix dimensions are stored as the tuple components the frozen display
lists and no order on them has to be carried separately
(`conv:finite-slots`); clause `P4` is `(D, Y)` with
`D >= 3` and `Y <= D`; clause `P5` is the two positive robustness depths. -/
structure LevelPublicInput (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  /-- `P1`: the ordered endpoint graph `G = (V,E,bd_0,bd_1)`. -/
  G : EndpointGraph V E
  /-- `P2`: `gamma in Q`. -/
  γ : ℚ
  /-- `P2`: `Delta in N_{>0}`. -/
  Δ : ℕ
  /-- `P2`: `Delta > 0`. -/
  Δpos : 0 < Δ
  /-- `P2`: `0 < gamma`. -/
  γpos : 0 < γ
  /-- `P2`: `gamma <= 1`. -/
  γle : γ ≤ 1
  /-- `P2`: the promise-independent predicate `SourceCommon(G;gamma,Delta)`. -/
  common : G.SourceCommon γ Δ
  /-- `P3`: `m_R in N`, so that `X_R = [m_R]`. -/
  mR : ℕ
  /-- `P3`: `n_R in N`, so that `Y_R = [n_R]`. -/
  nR : ℕ
  /-- `P3`: `m_R > 0`. -/
  mRpos : 0 < mR
  /-- `P3`: `n_R > 0`. -/
  nRpos : 0 < nR
  /-- `P3`: `R : X_R x Y_R -> {0,1}`, at the frozen zero-based carriers
  `X_R = [m_R]` and `Y_R = [n_R]` of `conv:finite-slots`. -/
  R : Fin mR → Fin nR → Bool
  /-- `P4`: the exact `NO` complexity target `D`. -/
  D : ℕ
  /-- `P4`: the `YES` budget `Y`. -/
  Y : ℕ
  /-- `P4`: `D >= 3`. -/
  Dge : 3 ≤ D
  /-- `P4`: `Y <= D`. -/
  YleD : Y ≤ D
  /-- `P5`: the incoming robustness depth `b_0`. -/
  b₀ : ℕ
  /-- `P5`: the requested outgoing robustness depth `bout`. -/
  bout : ℕ
  /-- `P5`: `b_0 > 0`. -/
  b₀pos : 0 < b₀
  /-- `P5`: `bout > 0`. -/
  boutpos : 0 < bout

/-- **Aux `A3.4`.**  `D >= 3` gives the `def:robust-seed` guard `1 <= D` that
the banked `SeedInterface.noReading` asks for.  General in the input. -/
theorem publicInput_one_le_D (P : LevelPublicInput V E) : 1 ≤ P.D :=
  le_trans (by norm_num) P.Dge

/-- **Aux `A3.5`.**  The density half of `P2` is available on every public
input, by pin from the banked graph layer.  General in the input. -/
theorem publicInput_card_vertex_le (P : LevelPublicInput V E) :
    Fintype.card V ≤ 2 * Fintype.card E :=
  P.G.card_vertex_le_two_mul_card_edge fun u => (P.common.2 u).1

/-- **Aux `A3.6`.**  The frozen `m_R, n_R > 0` of `P3` is exactly the
nonemptiness of the two matrix carriers `X_R = [m_R]` and `Y_R = [n_R]`, which
is what mechanical rule `M7` preserves.  General in the input. -/
theorem publicInput_rows_nonempty (P : LevelPublicInput V E) :
    Nonempty (Fin P.mR) ∧ Nonempty (Fin P.nR) :=
  ⟨⟨⟨0, P.mRpos⟩⟩, ⟨⟨0, P.nRpos⟩⟩⟩

/-! ## Part 3: the two separate promise certificates

`def:level-certificates`, 05:53--74.  Two propositions *about the same*
`Public`, never a field of it and never conjoined.  The banked
`SeedInterface` of `10-direct-bridge.tex` already fixes the exact shape the
two complexity clauses are consumed in downstream; `noSeed` presents a public
input in that shape so that the identification can be proved rather than
asserted. -/

/-- The public input's own `(R, D, Y, b_0)` presented as the banked interface
record.  This is an accessor, not new data: every field is a projection. -/
def noSeed (P : LevelPublicInput V E) : SeedInterface (Fin P.mR) (Fin P.nR) where
  table := P.R
  noComplexity := P.D
  yesBudget := P.Y
  depth := P.b₀

/-- **`YesCert(Public)`** (`def:level-certificates`, 05:56--61):
`SourceYES(G)` and `comp R <= Y`.

Reader counterpart: `03-parameterized-construction.tex:100--101`, "If `G` is
three-colourable and `CC(R) <= Y_0`". -/
def YesCert (P : LevelPublicInput V E) : Prop :=
  P.G.SourceYES ∧ D P.R ≤ P.Y

/-- **`NoCert(Public)`** (`def:level-certificates`, 05:66--69):
`SourceNO(G;gamma)`, `comp R = D`, and `Lambda_3(R,1,2^{-b_0},3/5) >= D`.

Reader counterpart: `03-parameterized-construction.tex:105--107`, "If the
source satisfies its `NO` promise, `CC(R) = D`, and `R` has a robust
certificate at depth `b_0`". -/
def NoCert (P : LevelPublicInput V E) : Prop :=
  P.G.SourceNO P.γ ∧ D P.R = P.D ∧
    P.D ≤ LambdaGE P.R 1 (xOut P.b₀) ((3 : ℝ) / 5)

/-- **Aux `A3.1`.**  The `YES` certificate's complexity half is *exactly* the
banked `SeedInterface.yesReading`, at the public input's own budget.  General
in the input; consumes the banked interface by pin. -/
theorem yesCert_iff_reading (P : LevelPublicInput V E) :
    YesCert P ↔ P.G.SourceYES ∧ (noSeed P).yesReading := Iff.rfl

/-- **Aux `A3.2`.**  The `NO` certificate's two complexity clauses are
*exactly* the banked `SeedInterface.noReading`, whose third conjunct
`1 <= noComplexity` is supplied by `P4`'s `D >= 3` and is therefore not an
extra demand.  General in the input.

This is the disclosure of where the `NO` branch's realizability lives: the
right-hand side is the route's robust-seed reading, still Lean pending, so this
module states the certificate faithfully and claims **no** witness for it. -/
theorem noCert_iff_reading (P : LevelPublicInput V E) :
    NoCert P ↔ P.G.SourceNO P.γ ∧ (noSeed P).noReading := by
  constructor
  · rintro ⟨hno, heq, hrob⟩
    exact ⟨hno, heq, hrob, publicInput_one_le_D P⟩
  · rintro ⟨hno, heq, hrob, -⟩
    exact ⟨hno, heq, hrob⟩

/-- **Aux `A3.3`, and the hypothesis-consistency check for this layer.**  The
two certificates are never simultaneously satisfiable: conjoining them derives
`False` from the banked mutual exclusivity of the two source predicates.

The frozen text states them as two propositions about one `Public` precisely
because they are the two **cases** of one construction; accordingly no
statement anywhere in this module takes both as hypotheses. -/
theorem yesCert_not_noCert (P : LevelPublicInput V E) :
    YesCert P → NoCert P → False := by
  rintro ⟨hyes, -⟩ ⟨hno, -, -⟩
  exact EndpointGraph.sourceYES_not_sourceNO P.G P.γpos hyes hno

/-! ## Part 4: the universal level configuration

`def:level-configuration`, 05:91--102.  Six integers, four positivity clauses,
one `c_b >= 6` guard, and `C_in in N` with no constraint at all.  The record
takes **no** parameters: universality ("it does not depend on `Public`, on a
promise certificate, on a protocol, or on a transcript") is the absence of a
parameter, not an axiom. -/

/-- **A universal level configuration** `K = (C_0, c_seed, A_wrap, B_s, c_b,
C_in)` (`def:level-configuration`, label line 92).

Reader counterpart: **none** (see the module header). -/
structure LevelConfig where
  /-- `C_0`, a positive integer. -/
  C₀ : ℕ
  /-- `c_seed`, a positive integer. -/
  cseed : ℕ
  /-- `A_wrap`, a positive integer. -/
  Awrap : ℕ
  /-- `B_s`, a positive integer. -/
  Bs : ℕ
  /-- `c_b`, an integer with `c_b >= 6`. -/
  cb : ℕ
  /-- `C_in in N`; the frozen text imposes nothing further on it. -/
  Cin : ℕ
  /-- `C_0 > 0`. -/
  C₀pos : 0 < C₀
  /-- `c_seed > 0`. -/
  cseedpos : 0 < cseed
  /-- `A_wrap > 0`. -/
  Awrappos : 0 < Awrap
  /-- `B_s > 0`. -/
  Bspos : 0 < Bs
  /-- `c_b >= 6`. -/
  cbge : 6 ≤ cb

/-- **Aux `A4.1`.**  `c_b` is positive.  General in the configuration. -/
theorem levelConfig_cb_pos (K : LevelConfig) : 0 < K.cb :=
  lt_of_lt_of_le (by norm_num) K.cbge

/-- **Aux `A4.2`, and the pole for the `c_b` guard.**  The frozen bound really
bites: no configuration has `c_b = 5`.  Without this the field could be a
decoration. -/
theorem levelConfig_cb_ne_five (K : LevelConfig) : K.cb ≠ 5 := by
  have := K.cbge; omega

/-- **Aux `A4.3`.**  `C_in` is genuinely unconstrained: every natural number
occurs as the `C_in` of some configuration.  This is the frozen
`C_in in N` (as against the four positive entries), made checkable. -/
theorem levelConfig_Cin_unconstrained (n : ℕ) : ∃ K : LevelConfig, K.Cin = n :=
  ⟨{ C₀ := 1, cseed := 1, Awrap := 1, Bs := 1, cb := 6, Cin := n,
     C₀pos := by norm_num, cseedpos := by norm_num, Awrappos := by norm_num,
     Bspos := by norm_num, cbge := by norm_num }, rfl⟩

/-- Non-vacuity: the configuration at the frozen **boundary** values, `c_b = 6`
exactly and `C_in = 0`. -/
def levelConfigMin : LevelConfig where
  C₀ := 1; cseed := 1; Awrap := 1; Bs := 1; cb := 6; Cin := 0
  C₀pos := by norm_num
  cseedpos := by norm_num
  Awrappos := by norm_num
  Bspos := by norm_num
  cbge := by norm_num

/-- Non-vacuity: a configuration at nondegenerate interior values, so that the
record is not inhabited only at its boundary. -/
def levelConfigWitness : LevelConfig where
  C₀ := 3; cseed := 5; Awrap := 7; Bs := 2; cb := 11; Cin := 4
  C₀pos := by norm_num
  cseedpos := by norm_num
  Awrappos := by norm_num
  Bspos := by norm_num
  cbge := by norm_num

/-! ## Part 5: the typed one-level parameter record

`def:level-parameters`, 05:172--190.  `Pi = (K, N_2, c_2)` and nothing else:
`0 < N_2` is structural data because `LevelStep` must return nonempty carriers
and total least-representative maps *before* admissibility is checked, and
balancedness is a post-construction proposition, not a field.

The family lands in `Rows(M_1(Public,K))^{q_2}`.  `M_1`'s row carrier is a
Section-6/7 accessor, so it is the type parameter `X₁` here and the width is
the pinned banked `q_2`; every use site below instantiates `X₁` at the actual
`Rows(M_1)` of the trace. -/

/-- **A one-level parameter record** `Pi = (K, N_2, c_2)`
(`def:level-parameters`, label line 173), at row carrier `X₁ = Rows(M_1)` and
width `w = q_2`.

Reader counterpart: **none** (see the module header: the nearest reader
sentence states balancedness, which is deliberately not a field). -/
structure LevelParams (X₁ : Type*) (w : ℕ) where
  /-- The universal configuration. -/
  K : LevelConfig
  /-- `N_2 in N_{>0}`, so that `L_2 = [N_2]`. -/
  N₂ : ℕ
  /-- `N_2 > 0`: structural, per 05:183--186. -/
  N₂pos : 0 < N₂
  /-- `c_2 : L_2 -> Rows(M_1)^{q_2}`, the single indexed family. -/
  c₂ : Fin N₂ → Fin w → X₁

/-- **Aux `A5.1`.**  `L_2 = [N_2]` really has `N_2` elements.  General. -/
theorem levelParams_card_family {X₁ : Type*} {w : ℕ} (Pr : LevelParams X₁ w) :
    Fintype.card (Fin Pr.N₂) = Pr.N₂ := Fintype.card_fin _

/-- **Aux `A5.2`.**  Two parameter records with the same configuration and the
same `N_2` are equal exactly when their families agree: the family is genuine
data, not a derived accessor.  General. -/
theorem levelParams_ext_c2 {X₁ : Type*} {w : ℕ} {Pr Pr' : LevelParams X₁ w}
    (hK : Pr.K = Pr'.K) (hN : Pr.N₂ = Pr'.N₂) (hc : HEq Pr.c₂ Pr'.c₂) : Pr = Pr' := by
  cases Pr; cases Pr'
  cases hK
  subst hN
  cases hc
  rfl

/-- **Aux `A5.3`.**  `L_2` is nonempty, which is what `0 < N_2` is carried
for.  General. -/
theorem levelParams_index_nonempty {X₁ : Type*} {w : ℕ} (Pr : LevelParams X₁ w) :
    Nonempty (Fin Pr.N₂) := ⟨⟨0, Pr.N₂pos⟩⟩

/-- **Statement pole: balancedness is not a field.**  A constant family is a
perfectly legal `Pi`, and its coordinate restriction takes the two extreme
counts `N_2` and `0` at a two-element row carrier -- the furthest possible from
the two-sided balancedness bound.  A record that secretly forced balancedness
could not be inhabited this way, so 05:186--189 is checkable rather than
prose. -/
theorem levelParams_admits_unbalanced_family (w : ℕ) (hw : 0 < w) :
    ∃ Pr : LevelParams Bool w,
      (∀ ℓ ℓ' : Fin Pr.N₂, Pr.c₂ ℓ = Pr.c₂ ℓ') ∧
        ((Finset.univ.filter fun ℓ : Fin Pr.N₂ =>
            Pr.c₂ ℓ ⟨0, hw⟩ = false).card = Pr.N₂) ∧
        ((Finset.univ.filter fun ℓ : Fin Pr.N₂ =>
            Pr.c₂ ℓ ⟨0, hw⟩ = true).card = 0) := by
  refine ⟨{ K := levelConfigMin, N₂ := 2, N₂pos := by norm_num,
            c₂ := fun _ _ => false }, fun _ _ => rfl, ?_, ?_⟩
  · simp
  · simp

/-- Non-vacuity: a parameter record at `N_2 = 2` whose family is **not**
constant, so the record is not inhabited only at degenerate families. -/
def paramsWitness (w : ℕ) : LevelParams Bool w where
  K := levelConfigWitness
  N₂ := 2
  N₂pos := by norm_num
  c₂ := fun ℓ j => decide ((ℓ : ℕ) ≤ (j : ℕ))

theorem paramsWitness_c2_nonconstant (w : ℕ) (hw : 0 < w) :
    (paramsWitness w).c₂ ⟨0, (paramsWitness w).N₂pos⟩
      ≠ (paramsWitness w).c₂ ⟨1, by change (1 : ℕ) < 2; norm_num⟩ := by
  intro h
  have := congrFun h (⟨0, hw⟩ : Fin w)
  simp [paramsWitness] at this

/-! ## Part 6: the one-level trace

`def:level-trace`, 05:219--316, with the field order of
`eq:one-level-trace-destructuring` (07:18--28) reproduced letter-exactly: the
23 data fields below appear in the frozen order

```
S, C_2, (pi_alpha), M_1, M_2, M_3, B, A, N, U, W, R+,
f_A^row, r_A^row, f_A^col, r_A^col,
p_U^row, p_U^col, p_Q^row, p_Q^col,
H, m_next, n_next
```

and the clauses `T1`--`T6` follow as a separate block of proof fields.  The
carriers of `M_1, B, A` are type parameters, since their entry equations live in
Sections 7--8.  Four carriers are **not** parameters.  `M_2`'s column carrier is
the frozen `L_2 = [N_2]` (`07:224` with `05:178`), read off the record `Pi` the
trace is already indexed by, so the field is typed at `Fin Pr.N₂`; its **row**
carrier is the frozen `[q_2] x C_1` (`07:223`, reprinted at `07:528`), typed at
`Fin (q2 G s) × C₁`, and since `cc-t7b` the field itself carries the value clause
`M₂_eq` of `07:225--226`.  `M_3`'s pair is forced in turn --
`07:450`/`07:497` fix `M_3 = Int_s(M_2^T)`, so `def:interlace` forces
`Rows(M_3) = [s] x Cols(M_2) = [s] x [N_2]` and `Cols(M_3) = Rows(M_2)^{[s]}`,
and the field is typed there with `M₃_eq` alongside `U_eq`/`W_eq`/`Rnext_eq`;
the tail
`N, U, W, R+` is typed at its
**forced** carriers so that `eq:trace-interlace-coordinate-carriers` holds
definitionally and the four coordinate fields can be typed exactly as
`eq:trace-interlace-coordinate-types` displays them. -/

/-- **A one-level trace** `LevelTrace(Public, Pi)` (`def:level-trace`, label
line 220), destructured exactly as `eq:one-level-trace-destructuring`.

Reader counterparts: `eq:paper-W-definition` (`03-parameterized-construction`
`.tex:87`) for the `U`/`W` equations and `eq:paper-W-carriers` (line 124) for
the readout `levelTrace_W_carriers`; the remaining fields have no reader
display **except `M_2`**, which the reader does display at
`eq:paper-M2-definition` (label line 297) but whose locus is already held by
`StageTwoRelaxed.stageTwo` under `STAGE2-MODULE-001`, so it is declined as a
double assignment rather than for absence (see the module header).

Nothing in this record is a complexity, robustness, `YES` or `NO` proposition
(05:315), and nothing depends on a promise branch. -/
structure LevelTrace (G : EndpointGraph V E) (s : ℕ)
    {X₁ : Type*} (Pr : LevelParams X₁ (q2 G s))
    (C₁ RB CB RA CA : Type*)
    [Fintype X₁] [Fintype C₁]
    [Fintype RB] [Fintype CB] [Fintype RA] [Fintype CA]
    (a q Q : ℕ) where
  /-- `T1`: the guarded source `S = GuardedSource(G,s)`. -/
  S : SlabRow V s → Fin (q2 G s) → Bool
  /-- `T1`: the indexed family `C_2 = (c_2(l))_{l in L_2}`. -/
  C₂ : Fin Pr.N₂ → Fin (q2 G s) → X₁
  /-- `T2`: the typed zero-based rank injections `pi_alpha : I_alpha -> [s]`. -/
  π : ∀ α : Fin (q2 G s), {i : SlabRow V s // i ∈ activeSlot G s α} → Fin s
  /-- `T3`: Stage 1. -/
  M₁ : X₁ → C₁ → Bool
  /-- `T3`: Stage 2, at **both** of its forced carriers.
  `eq:stage2-relaxed-value` (`07:221--229`) sets `Rows(M_2) = [q_2] x C_1` at
  line 223 and `Cols(M_2) = L_2` at line 224, and `def:level-parameters` sets
  `L_2 = [N_2]` at `05:178`.  So neither carrier is a free type: the row carrier
  is the frozen product of the guarded-source coordinate set `[q_2]` -- the same
  banked `Fin (q2 G s)` `T1` and `T2` are stated at -- with `M_1`'s own column
  carrier `C_1`, and the column carrier is the zero-based index set `[N_2]` of
  `conv:finite-slots`, i.e. `Fin Pr.N₂`, read off the record `Pi` the trace is
  already indexed by.  `07:528` prints the same row carrier a second time, as
  `J_2 = Rows(M_2) = [q_2] x C_1` inside `eq:raw-stage4-universes`. -/
  M₂ : Fin (q2 G s) × C₁ → Fin Pr.N₂ → Bool
  /-- `T3`: Stage 3, at its **forced** carriers.  `07:450` and `07:497` fix
  `M_3 = Int_s(M_2^T)`, `08:262--263` names `S_2 = M_2^T`, and `def:interlace`
  (`03:112--119`: row set at line 114, column set at line 115, value at lines
  116--119) gives the `s`-fold classical interlace of a matrix with row
  set `X` the row set `[s] x X` and the column set `Y^{[s]}`.  Hence
  `Rows(M_3) = [s] x Rows(S_2) = [s] x Cols(M_2) = [s] x [N_2]` and
  `Cols(M_3) = Cols(S_2)^{[s]} = Rows(M_2)^{[s]} = ([q_2] x C_1)^{[s]}`, exactly
  as typed here.  The
  same forcing is what `Rows(B)`'s template summand `[s] x Cols(M_2)` of
  `eq:raw-stage4-universes` (`07:539--541`) reads. -/
  M₃ : Fin s × Fin Pr.N₂ → (Fin s → Fin (q2 G s) × C₁) → Bool
  /-- `T3`: the raw Stage-4 matrix. -/
  B : RB → CB → Bool
  /-- `T3`: the labelled protected duplicate. -/
  A : RA → CA → Bool
  /-- `T3`: `N = A^T`. -/
  N : CA → RA → Bool
  /-- `T3`: `U = Int_q(N)`. -/
  U : Fin q × CA → (Fin q → RA) → Bool
  /-- `T3`: `W = U^T`. -/
  W : (Fin q → RA) → Fin q × CA → Bool
  /-- `T3`: `R+ = Int_Q(W)^T`. -/
  Rnext : (Fin Q → Fin q × CA) → Fin Q × (Fin q → RA) → Bool
  /-- `T4`: the row label-forgetting map. -/
  fArow : RA → RB
  /-- `T4`: the row least-representative map. -/
  rArow : RB → RA
  /-- `T4`: the column label-forgetting map. -/
  fAcol : CA → CB
  /-- `T4`: the column least-representative map. -/
  rAcol : CB → CA
  /-- `T5`: the inner interlace row coordinate. -/
  pUrow : Fin q × CA → Fin q
  /-- `T5`: the inner interlace column coordinate. -/
  pUcol : (Fin q → RA) × Fin q → RA
  /-- `T5`: the outer interlace row coordinate. -/
  pQrow : Fin Q × (Fin q → RA) → Fin Q
  /-- `T5`: the outer interlace column coordinate. -/
  pQcol : (Fin Q → Fin q × CA) × Fin Q → Fin q × CA
  /-- `T6`: the public overhead integer. -/
  H : ℕ
  /-- `T6`: the output row count. -/
  mnext : ℕ
  /-- `T6`: the output column count. -/
  nnext : ℕ
  /-- `T1`: `S = GuardedSource(G,s)`, the banked constructor on the nose. -/
  S_eq : S = guardedRow G s
  /-- `T1`: `C_2` is exactly the family stored in `Pi`. -/
  C₂_eq : C₂ = Pr.c₂
  /-- `T2`: `pi_alpha(i) = |{h in I_alpha : h < i}|`. -/
  π_eq : ∀ (α : Fin (q2 G s)) (i : {i : SlabRow V s // i ∈ activeSlot G s α}),
    ((π α i : Fin s) : ℕ) = slotRank G s α i.1
  /-- `T3`: `M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)` -- the Stage-2
  **value clause**, the third line of `eq:stage2-relaxed-value` (`07:225--226`),
  at the two carriers the same display fixes on `07:223--224`.  Both operands are
  the trace's own fields: `M_1` is the Stage-1 matrix of `T3` and `c^{(l)}` is
  the stored family `C_2` of `T1`, whose own equation `C₂_eq` pins it to `Pi`'s
  `c_2` -- so nothing here restates the parameter record.  The typed evaluation
  `c^{(l)}(alpha)` is `07:230--231`'s `c_alpha^{(l)}`, applied in the frozen
  binder order `(family index, coordinate)`.

  The right-hand side is the **vendored** `NPCC.relaxedInterlace` of
  `def:relaxed-interlace` applied to `M_1^T`, consumed by pin and never
  restated: `07:217` says "Stage 2 is a relaxed interlace of `M_1^T`", and the
  vendored constructor's own value clause `f(x, S(j)(i))` at row `(i,x)` and
  column `j` is the frozen `M_1(c^{(l)}(alpha), gamma)` on the nose.  The inline
  transpose `fun gamma x => M_1(x, gamma)` is the same idiom the trace's `N_eq`
  and `W_eq` already use.

  **Reader counterpart: none, declined with the reason recorded.**  Unlike the
  other `LevelTrace` fields, `M_2` *is* displayed by the reader, at
  `eq:paper-M2-definition` (`03-parameterized-construction.tex`, label line 297,
  value clause on lines 294--295); so the header's "no reader display" reason
  does not apply to it.  It is declined for the other reason instead: that locus
  is **already held** by `StageTwoRelaxed.stageTwo` under `STAGE2-MODULE-001`,
  and citing it twice is the double assignment the reader-counterpart rule
  forbids.  The same disposition covers `Section5Admissibility.stepMTwo`. -/
  M₂_eq : M₂ = relaxedInterlace (fun γ x => M₁ x γ) C₂
  /-- `T3`: `M_3 = Int_s(M_2^T)` -- the Stage-3 scale-alignment equation, stated
  at `07:450` inside `lem:stage3-exact-scale` and again as the construction's own
  display at `07:497`, with `S_2 = M_2^T` of `08:262--263`.  This is the same
  `interlaceFun` the trace's `U_eq` uses at the inner width `q`; here the width
  is the frozen `s`, and the two are never interchanged. -/
  M₃_eq : M₃ = interlaceFun (fun y x => M₂ x y) s
  /-- `T3`: `N = A^T`. -/
  N_eq : N = fun y x => A x y
  /-- `T3`: `U = Int_q(N)`. -/
  U_eq : U = interlaceFun N q
  /-- `T3`: `W = U^T`. -/
  W_eq : W = fun y x => U x y
  /-- `T3`: `R+ = Int_Q(W)^T`. -/
  Rnext_eq : Rnext = fun c r => interlaceFun W Q r c
  /-- `T4`: `f_A^row . r_A^row` is the identity on `Rows(B)`. -/
  fArow_rArow : ∀ b : RB, fArow (rArow b) = b
  /-- `T4`: `f_A^col . r_A^col` is the identity on `Cols(B)`. -/
  fAcol_rAcol : ∀ b : CB, fAcol (rAcol b) = b
  /-- `T5`: `p_U^row(i,x) = i`. -/
  pUrow_eq : ∀ (i : Fin q) (x : CA), pUrow (i, x) = i
  /-- `T5`: `p_U^col(y,i) = y(i)`. -/
  pUcol_eq : ∀ (y : Fin q → RA) (i : Fin q), pUcol (y, i) = y i
  /-- `T5`: `p_Q^row(j,x) = j`. -/
  pQrow_eq : ∀ (j : Fin Q) (x : Fin q → RA), pQrow (j, x) = j
  /-- `T5`: `p_Q^col(z,j) = z(j)`. -/
  pQcol_eq : ∀ (z : Fin Q → Fin q × CA) (j : Fin Q), pQcol (z, j) = z j
  /-- `T6`: `H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`. -/
  H_eq : H = a + Nat.log 2 (q2 G s) + Nat.log 2 s + Nat.log 2 q + Nat.log 2 Q
  /-- `T6`: `m_next = |Rows(R+)|`. -/
  mnext_eq : mnext = rowsCard Rnext
  /-- `T6`: `n_next = |Cols(R+)|`. -/
  nnext_eq : nnext = colsCard Rnext

namespace LevelTrace

variable {G : EndpointGraph V E} {s : ℕ} {X₁ : Type*}
  {Pr : LevelParams X₁ (q2 G s)}
  {C₁ RB CB RA CA : Type*}
  [Fintype X₁] [Fintype C₁]
  [Fintype RB] [Fintype CB] [Fintype RA] [Fintype CA]
  {a q Q : ℕ}

/-- **`T1` pole.**  The guarded-source field is pinned to the banked
constructor, so no trace may substitute a promise-specific source. -/
theorem levelTrace_S_pinned
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (i : SlabRow V s) (j : Fin (q2 G s)) : T.S i j = guardedRow G s i j := by
  rw [T.S_eq]

/-- **`T1` pole.**  The Stage-2 family is pinned to the one stored in `Pi`:
this is the frozen "`LevelStep` never chooses a replacement" (05:338--340). -/
theorem levelTrace_C2_pinned
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (ℓ : Fin Pr.N₂) : T.C₂ ℓ = Pr.c₂ ℓ := by rw [T.C₂_eq]

/-- **`T2`.**  Each `pi_alpha` is injective, by the frozen rank equation and
`slotRank_injOn`.  General in the trace. -/
theorem levelTrace_π_injective
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (α : Fin (q2 G s)) : Function.Injective (T.π α) := by
  intro i j h
  refine Subtype.ext (slotRank_injOn G s α i.2 j.2 ?_)
  rw [← T.π_eq α i, ← T.π_eq α j, h]

/-- **Aux `A9.1`.**  The frozen Stage-3 entry equation, read off the field
equation: `M_3((i,y), x) = M_2(x(i), y)`.  This is `def:interlace`'s value
clause (`03:116--119`) at `S_2 = M_2^T` (`08:262--263`), i.e. `07:497` unfolded
one step.  General in the trace. -/
theorem levelTrace_M₃_apply
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (i : Fin s) (y : Fin Pr.N₂) (x : Fin s → Fin (q2 G s) × C₁) :
    T.M₃ (i, y) x = T.M₂ (x i) y := by rw [T.M₃_eq]; rfl

/-- **Aux `A9.2`.**  `Rows(M_3)` is the frozen
`[s] x Rows(S_2) = [s] x Cols(M_2) = [s] x [N_2]` **definitionally**: the
identity below closes by `rfl`, so `rowsCard T.M₃` is no longer `Fintype.card`
of a free carrier.  Before the `M₃`/`M₃_eq` pair landed, `M₃ : R₃ → C₃ → Bool`
stood over an unconstrained `R₃` and `rowsCard T.M₃` reduced to
`Fintype.card R₃`, which `Section5Admissibility.rowsCard_of_fin_carrier` shows
realizes every natural.  General in the trace. -/
theorem levelTrace_M₃_rowCarrier
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    rowsCard T.M₃ = Fintype.card (Fin s × Fin Pr.N₂) := rfl

/-- **Aux `A10.1`, and the acceptance `rfl` receipt of the `C₂c` round.**  The
Stage-2 column carrier **is** the frozen `L_2 = [N_2]`, definitionally: the
identity below closes by `rfl`, so `colsCard T.M₂` is no longer `Fintype.card`
of a free type.  Before the carrier was forced, `M₂ : R₂ → C₂c → Bool` stood
over an unconstrained `C₂c`, and `Section5Admissibility.rowsCard_of_fin_carrier`
shows that such a readout realizes every natural.

**Reader counterpart: none, declined with the reason recorded** -- see the
numeric sibling `levelTrace_M₂_cols` below, where the sweep is written out:
the reader's two statements of this fact (`eq:paper-M2-definition` line 293 and
`03-parameterized-construction.tex:477--485`) are already held by
`StageTwoRelaxed` and by `SchedulePhysicalResidue`/`PARAM-001` respectively, so
neither half of this receipt claims a reader item.  General in the trace. -/
theorem levelTrace_M₂_colCarrier
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    colsCard T.M₂ = Fintype.card (Fin Pr.N₂) := rfl

/-- **Aux `A10.2`, the numeric half of the same receipt.**  `|Cols(M_2)| = N_2`.

**Attribution.**  `eq:stage2-relaxed-value` fixes `Cols(M_2) = L_2` at `07:224`
and `def:level-parameters` fixes `L_2 = [N_2]` at `05:178`; `conv:finite-slots`
makes `[N_2]` the zero-based `Fin N_2`.  The two project pins owed are then the
sibling `rfl` receipt `levelTrace_M₂_colCarrier` (the carrier half: `colsCard
T.M₂` **is** `Fintype.card (Fin N_2)`) and the banked `A5.1` item
`levelParams_card_family` (the count half: `Fintype.card (Fin N_2) = N_2`,
`:1087--1088`); the proof is their composite and nothing else.  Mathlib's
`Fintype.card_fin` is **not** re-invoked here -- it is already the proof term
*inside* `levelParams_card_family`, and re-deriving it around both banked
receipts would be the duplicate-upstream-proof pattern parked at `cc-t5d-r1`,
`cc-t5m`, `cc-t6s-r4` and `cc-t6s-r5`.  This is the identification that was OPEN
as Residue 1's second half of `S5-M3-ROWS-AUDIT-001`; it is a **theorem** here
rather than a hypothesis, because the carrier is forced by the record's own
`Pi`.

**Reader counterpart: none, and the reason is recorded** (the module's standing
convention, whose in-file precedent is the rank injection `pi_alpha` above --
declined there because its only reader display was *already assigned*).  The
reader does state this fact, twice, and **both loci are already held**:
`eq:paper-M2-definition` (`03-parameterized-construction.tex`, label line 297,
display 290--297, whose line 293 reads `Cols(M_2)=L_2`) is claimed by
`StageTwoRelaxed.stageTwo` / `stageTwo_cols_card`, and
`03-parameterized-construction.tex:477--485` ("Write `N_2=|L_2|` ...") is
claimed by `SchedulePhysicalResidue`'s Stage-3 carrier group under `PARAM-001`,
`READER_CROSSWALK.md` row 6.  A sweep of the whole reader file for `L_2`, `N_2`
and `Cols` returns no third locus.  Citing either would be the double
assignment the reader-counterpart rule forbids, so this declaration and its
`rfl` sibling claim **no** reader item.  General in the trace. -/
theorem levelTrace_M₂_cols
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    colsCard T.M₂ = Pr.N₂ :=
  (levelTrace_M₂_colCarrier T).trans (levelParams_card_family Pr)

/-- **Aux `A11.1`, and the acceptance probe of the `cc-t7b` round.**  The frozen
Stage-2 **value clause** `M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)`
(`07:225--226`), read off the field equation at the record's own stored family.

This is the reduction the round was for: `T.M₂` is no longer an arbitrary
`Bool`-matrix at the right carriers -- every entry of it *is* an entry of `T.M₁`
at the coordinate the family `c_2` names.  Both pins are the trace's own
equations, `M₂_eq` and `C₂_eq`, so the right-hand side mentions `Pi`'s stored
`c_2` and nothing else; the vendored `NPCC.relaxedInterlace` is consumed, never
unfolded by hand.

**Reader counterpart: none, declined with the reason recorded.**  The reader
states this clause at `eq:paper-M2-definition`
(`03-parameterized-construction.tex`, label line 297, value clause on lines
294--295), and that display is **already held** by `StageTwoRelaxed.stageTwo`
(`STAGE2-MODULE-001`, whose own header claims label line 297).  Citing it here
would be the double assignment the reader-counterpart rule forbids, exactly as
for the sibling receipts `levelTrace_M₂_colCarrier` and `levelTrace_M₂_cols`
above.  General in the trace. -/
theorem levelTrace_M₂_apply
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (α : Fin (q2 G s)) (γ : C₁) (ℓ : Fin Pr.N₂) :
    T.M₂ (α, γ) ℓ = T.M₁ (Pr.c₂ ℓ α) γ := by
  rw [T.M₂_eq, T.C₂_eq]
  rfl

/-- **Aux `A11.2`, the `rfl` receipt of the forced Stage-2 row carrier.**
`Rows(M_2)` **is** the frozen `[q_2] x C_1` of `07:223` definitionally, so
`rowsCard T.M₂` is no longer `Fintype.card` of a free type.  Before the carrier
was forced, `M₂ : R₂ → Fin Pr.N₂ → Bool` stood over an unconstrained `R₂`, and
`Section5Admissibility.rowsCard_of_fin_carrier` shows such a readout realizes
every natural.  General in the trace. -/
theorem levelTrace_M₂_rowCarrier
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    rowsCard T.M₂ = Fintype.card (Fin (q2 G s) × C₁) := rfl

/-- **Aux `A11.3`, the numeric half of the same receipt.**
`|Rows(M_2)| = q_2 |C_1|`.

**Attribution.**  `eq:stage2-relaxed-value` fixes `Rows(M_2) = [q_2] x C_1` at
`07:223` (and `eq:raw-stage4-universes` reprints it as `J_2` at `07:528`);
`conv:finite-slots` makes `[q_2]` the zero-based `Fin (q2 G s)`, the banked
guarded-source width `T1` and `T2` are already stated at.  The proof is the
sibling `rfl` receipt composed with the product and `Fin` counts; no frozen
display is quoted for the product itself.  General in the trace. -/
theorem levelTrace_M₂_rows
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    rowsCard T.M₂ = q2 G s * Fintype.card C₁ :=
  (levelTrace_M₂_rowCarrier T).trans
    (by rw [Fintype.card_prod, Fintype.card_fin])

/-- **Aux `A11.4`, and the statement pole for the value clause.**  The equation
field pins `M_2` from `M_1` alone: two traces over the same Stage-1 matrix have
the same Stage-2 matrix.  A record whose `M_2` were unconstrained would be
satisfied by an arbitrary matrix at those carriers, and this is the property it
could not have.  (The stored family needs no hypothesis: `C₂_eq` already pins it
to the `Pi` both traces are indexed by.)  General in the two traces. -/
theorem levelTrace_M₂_determined
    (T T' : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (hM : T.M₁ = T'.M₁) : T.M₂ = T'.M₂ := by
  rw [T.M₂_eq, T'.M₂_eq, T.C₂_eq, T'.C₂_eq, hM]

/-- **Aux `A11.5`.**  The two Stage equations compose: every entry of `M_3` is an
entry of `M_1`, at the coordinate the stored family names.  This is `07:497`
followed by `07:225--226`, and it is what makes the Stage-3 row carrier a
*derived* object all the way down to Stage 1 rather than two forced carriers over
a free matrix.  Consumes `levelTrace_M₃_apply` and the two field equations by
pin.  General in the trace. -/
theorem levelTrace_M₃_reduces_to_stageOne
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (i : Fin s) (ℓ : Fin Pr.N₂) (x : Fin s → Fin (q2 G s) × C₁) :
    T.M₃ (i, ℓ) x = T.M₁ (Pr.c₂ ℓ (x i).1) (x i).2 := by
  rw [levelTrace_M₃_apply, T.M₂_eq, T.C₂_eq]
  rfl

/-- **Aux `A9.3`.**  `|Rows(M_3)| = s N_2`.

**Attribution, split by source.**  `08:262--263` supplies `S_2 = M_2^T` and the
name `m_3 = |Rows(S_2)|`, i.e. the `|Cols(M_2)|` factor -- and *only* that; the
outer factor `s` is **not** in those lines.  It comes from the Stage-3 equation
`M_3 = Int_s(M_2^T)` (`07:450`, `07:497`) together with `def:interlace`'s row
set `[p] x X` (`03:114`).  The inner factor is then the frozen
`|Cols(M_2)| = L_2 = [N_2]` (`07:224` with `05:178`), i.e. `levelTrace_M₂_cols`,
which is why the right-hand side is the paper's own parameter `N_2` and not a
free carrier's cardinality.  The product `s m_3` is derived here, not quoted
from a single frozen display.

Both interlace steps are consumed by pin from the banked `rowsCard_interlace`
and `rowsCard_transpose`; neither is restated.  General in the trace. -/
theorem levelTrace_M₃_rows
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    rowsCard T.M₃ = s * Pr.N₂ := by
  rw [T.M₃_eq, rowsCard_interlace, rowsCard_transpose, levelTrace_M₂_cols]

/-- **Aux `A9.4`.**  `|Cols(M_3)| = |Rows(M_2)|^s`, the column half of the same
display, by pin from `colsCard_interlace` and `colsCard_transpose`.  General in
the trace. -/
theorem levelTrace_M₃_cols
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    colsCard T.M₃ = rowsCard T.M₂ ^ s := by
  rw [T.M₃_eq, colsCard_interlace, colsCard_transpose]

/-- **Statement pole for the Stage-3 field.**  A record whose `M_3` were
unconstrained would be satisfied by an arbitrary matrix at those carriers; the
equation field pins it, so two traces over the same `M_2` at the same `s` have
the same `M_3`.  This is the `M_3` analogue of `levelTrace_tail_determined`, and
it is the property the bare field could not have. -/
theorem levelTrace_M₃_determined
    (T T' : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (hM : T.M₂ = T'.M₂) : T.M₃ = T'.M₃ := by
  rw [T.M₃_eq, T'.M₃_eq, hM]

/-- **Aux `A6.1`.**  `W = U^T = Int_q(N)^T` is definitionally the banked
`EthBridge.Rnext N q`, which is how the whole bridge layer names it.  This is
the round-trip to the banked interface; nothing is re-proved. -/
theorem levelTrace_W_eq_bridge
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    T.W = EthBridge.Rnext T.N q := by
  rw [T.W_eq, T.U_eq]; rfl

/-- **Aux `A6.2`.**  `R+ = Int_Q(W)^T` is the banked `EthBridge.Rnext W Q`. -/
theorem levelTrace_Rnext_eq_bridge
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    T.Rnext = EthBridge.Rnext T.W Q := by
  rw [T.Rnext_eq]; rfl

/-- **Aux `A6.3`.**  Composing the two, `R+` is the double interlace of `N` at
the two **separate** widths `q` and `Q`, in that order.  This is the form the
banked size layer consumes. -/
theorem levelTrace_Rnext_eq_double
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    T.Rnext = EthBridge.Rnext (EthBridge.Rnext T.N q) Q := by
  rw [levelTrace_Rnext_eq_bridge, levelTrace_W_eq_bridge]

/-- **Aux `A6.4`.**  The four literal carrier identifications of
`eq:trace-interlace-coordinate-carriers` (05:276--285), read as cardinalities:
`|Rows(U)| = q|Rows(N)|`, `|Cols(U)| = |Cols(N)|^q`,
`|Rows(Int_Q(W))| = Q|Rows(W)|`, `|Cols(Int_Q(W))| = |Cols(W)|^Q`.

The *typed* half of the same display -- that the four coordinate fields can be
declared at exactly the types `eq:trace-interlace-coordinate-types` prints -- is
what the encoding race turned on: under the landed encoding those types are the
field types verbatim, so `levelTrace_coordinate_equations` typechecks without a
transport, whereas the rejected bundled encoding needs a rewrite along the
stored equation `U_eq` before the coordinate maps can even be stated. -/
theorem levelTrace_interlace_carriers
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    rowsCard T.U = q * rowsCard T.N ∧ colsCard T.U = colsCard T.N ^ q ∧
      rowsCard (interlaceFun T.W Q) = Q * rowsCard T.W ∧
      colsCard (interlaceFun T.W Q) = colsCard T.W ^ Q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [rowsCard, colsCard, Fintype.card_prod, Fintype.card_fin]

/-- **Aux `A6.5`.**  The four defining equations of
`eq:trace-interlace-coordinate-equations` (05:297--305), collected, at the
literal types of `eq:trace-interlace-coordinate-types`. -/
theorem levelTrace_coordinate_equations
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    (∀ (i : Fin q) (x : CA), T.pUrow (i, x) = i) ∧
      (∀ (y : Fin q → RA) (i : Fin q), T.pUcol (y, i) = y i) ∧
      (∀ (j : Fin Q) (x : Fin q → RA), T.pQrow (j, x) = j) ∧
      (∀ (z : Fin Q → Fin q × CA) (j : Fin Q), T.pQcol (z, j) = z j) :=
  ⟨T.pUrow_eq, T.pUcol_eq, T.pQrow_eq, T.pQcol_eq⟩

/-- **Aux `A7.1`.**  The carriers of the scale-alignment output.

Reader counterpart: `eq:paper-W-carriers`
(`03-parameterized-construction.tex:121--123`), `|Rows(W)| = n_N^q` and
`|Cols(W)| = q m_N`.  Obtained from the banked `bridgeCarriers` by pin. -/
theorem levelTrace_W_carriers
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    rowsCard T.W = colsCard T.N ^ q ∧ colsCard T.W = q * rowsCard T.N := by
  rw [levelTrace_W_eq_bridge]
  exact bridgeCarriers T.N q

/-- **Aux `A7.2`.**  The two output cardinalities are the frozen exact carrier
growth `|Rows(R+)| = (q m_N)^Q` and `|Cols(R+)| = Q n_N^q`, obtained from the
banked `doubleInterlaceCarriers` by pin.  Both interlace widths are kept in
their own positions. -/
theorem levelTrace_carrier_recurrence
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    T.mnext = (q * rowsCard T.N) ^ Q ∧ T.nnext = Q * colsCard T.N ^ q := by
  obtain ⟨hr, hc⟩ := doubleInterlaceCarriers T.N q Q
  rw [T.mnext_eq, T.nnext_eq, levelTrace_Rnext_eq_double]
  exact ⟨hr, hc⟩

/-- **Aux `A7.3`.**  The overhead field is the banked `levelOverhead` at the
five frozen exponents; the two interlace exponents `log_2 q` and `log_2 Q`
stay in distinct summands. -/
theorem levelTrace_H_eq_levelOverhead
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    T.H = levelOverhead a (Nat.log 2 (q2 G s)) (Nat.log 2 s)
            (Nat.log 2 q) (Nat.log 2 Q) := by
  rw [T.H_eq, levelOverhead_eq]

/-- **Aux `A7.4`.**  The least-representative maps are injective -- the content
of `T4`'s round-trip identity on the `B` side. -/
theorem levelTrace_rA_injective
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    Function.Injective T.rArow ∧ Function.Injective T.rAcol := by
  refine ⟨fun x y h => ?_, fun x y h => ?_⟩
  · rw [← T.fArow_rArow x, ← T.fArow_rArow y, h]
  · rw [← T.fAcol_rAcol x, ← T.fAcol_rAcol y, h]

/-- **Aux `A7.5`.**  The label-forgetting maps are surjective: every row and
column of the raw Stage-4 matrix is hit by the protected duplicate. -/
theorem levelTrace_fA_surjective
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q) :
    Function.Surjective T.fArow ∧ Function.Surjective T.fAcol :=
  ⟨fun b => ⟨T.rArow b, T.fArow_rArow b⟩,
   fun b => ⟨T.rAcol b, T.fAcol_rAcol b⟩⟩

/-- **Statement pole for `T3`.**  The four tail equations pin the tail
uniquely: two traces over the same `A` at the same widths have the same
`N, U, W, R+`.  Without them the derived tail would be free data and the trace
would assert nothing about the construction. -/
theorem levelTrace_tail_determined
    (T T' : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (hA : T.A = T'.A) :
    T.N = T'.N ∧ T.U = T'.U ∧ T.W = T'.W ∧ T.Rnext = T'.Rnext := by
  have hN : T.N = T'.N := by rw [T.N_eq, T'.N_eq, hA]
  have hU : T.U = T'.U := by rw [T.U_eq, T'.U_eq, hN]
  have hW : T.W = T'.W := by rw [T.W_eq, T'.W_eq, hU]
  refine ⟨hN, hU, hW, ?_⟩
  rw [T.Rnext_eq, T'.Rnext_eq, hW]

/-- **Promise freedom** (05:315, and `C1` of `thm:one-level` as it applies to
this layer).  Supplying a promise branch to a trace returns the same trace.

What makes this content rather than notation is the banked
`OneLevelAssembly.promiseFreedom_not_automatic`: a function of `PromiseCase`
need **not** be constant. -/
def traceOfCase (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (_c : PromiseCase) : LevelTrace G s Pr C₁ RB CB RA CA a q Q := T

theorem levelTrace_promise_free
    (T : LevelTrace G s Pr C₁ RB CB RA CA a q Q)
    (c c' : PromiseCase) : traceOfCase T c = traceOfCase T c' := rfl

end LevelTrace

/-! ## Part 7: the pinned width inside the overhead

`H` carries `log_2 q_2`, and `q_2` is the banked accessor `2^{clog_2(12 s m)}`.
The two lemmas below make the overhead completely explicit without introducing
any new constant. -/

/-- **Aux `A8.1`.**  `log_2 q_2 = clog_2(12 s |E|)`: the frozen width is a power
of two, so its binary logarithm is exact and no floor is suppressed.  General in
`G` and `s`. -/
theorem log_q2 (G : EndpointGraph V E) (s : ℕ) :
    Nat.log 2 (q2 G s) = Nat.clog 2 (12 * s * Fintype.card E) := by
  rw [q2, Nat.log_pow (by norm_num)]

/-- **Aux `A8.2`.**  At dyadic `s = 2^{w_s}`, `q = 2^{w_q}`, `Q = 2^{w_Q}` --
the regime the admissibility group `WF` demands -- the overhead is the literal
five-term sum of exponents.  General in all four exponents. -/
theorem overhead_at_powers (G : EndpointGraph V E) (a ws wq wQ : ℕ) :
    a + Nat.log 2 (q2 G (2 ^ ws)) + Nat.log 2 (2 ^ ws) + Nat.log 2 (2 ^ wq)
        + Nat.log 2 (2 ^ wQ)
      = a + Nat.clog 2 (12 * 2 ^ ws * Fintype.card E) + ws + wq + wQ := by
  rw [log_q2, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num),
    Nat.log_pow (by norm_num)]

/-! ## Part 8: non-vacuity -- nondegenerate inhabitants at legal values

Every structure introduced above is inhabited here.  The public input is
inhabited **separately** on the two promise branches, never conjoined; the
`YES` certificate is inhabited in full; the `NO` certificate's source half is
inhabited and its complexity half is disclosed as the banked, still pending,
robust-seed reading. -/

/-- `K_3` satisfies the promise-independent graph hypotheses at `Delta = 3`. -/
theorem k3_sourceCommon : K3.SourceCommon (1 / 6) 3 := by
  refine ⟨by simp, fun u => ?_⟩
  rw [k3_degree u]; omega

/-- `K_4` satisfies the promise-independent graph hypotheses at `Delta = 3`. -/
theorem k4_sourceCommon : K4.SourceCommon (1 / 6) 3 := by
  refine ⟨by simp, fun u => ?_⟩
  rw [k4_degree u]; omega

/-- The two-valued `2 x 2` seed used by the public-input witnesses: equality on
`Fin 2`, which is genuinely not constant. -/
def witnessR : Fin 2 → Fin 2 → Bool := fun x y => decide (x = y)

theorem witnessR_nonconstant : witnessR 0 0 ≠ witnessR 0 1 := by decide

/-- Non-vacuity: a public input on the `YES` branch, at legal nondegenerate
values (`K_3`, `gamma = 1/6`, `Delta = 3`, `D = 3`, `Y = 0`, `b_0 = bout = 1`).
The hardest field, `SourceCommon`, is discharged at real degree data. -/
def publicInputYes : LevelPublicInput (Fin 3) (Fin 3) where
  G := K3
  γ := 1 / 6
  Δ := 3
  Δpos := by norm_num
  γpos := by norm_num
  γle := by norm_num
  common := k3_sourceCommon
  mR := 2
  nR := 2
  mRpos := by norm_num
  nRpos := by norm_num
  R := witnessR
  D := 3
  Y := 0
  Dge := by norm_num
  YleD := by norm_num
  b₀ := 1
  bout := 1
  b₀pos := by norm_num
  boutpos := by norm_num

/-- Non-vacuity: a public input on the `NO` branch, at the same legal
constants but on `K_4`, which has no proper `3`-colouring. -/
def publicInputNo : LevelPublicInput (Fin 4) (Fin 6) where
  G := K4
  γ := 1 / 6
  Δ := 3
  Δpos := by norm_num
  γpos := by norm_num
  γle := by norm_num
  common := k4_sourceCommon
  mR := 2
  nR := 2
  mRpos := by norm_num
  nRpos := by norm_num
  R := witnessR
  D := 3
  Y := 0
  Dge := by norm_num
  YleD := by norm_num
  b₀ := 1
  bout := 1
  b₀pos := by norm_num
  boutpos := by norm_num

/-- The `NO` branch's source half is genuinely occupied. -/
theorem publicInputNo_sourceNO : publicInputNo.G.SourceNO publicInputNo.γ :=
  k4_sourceNO

/-- The `NO` witness is not secretly a `YES` witness. -/
theorem publicInputNo_not_sourceYES : ¬ publicInputNo.G.SourceYES :=
  k4_not_sourceYES

/-- The deterministic communication complexity of a constant matrix is zero:
the one-leaf protocol computes it at cost `0`.  General in the carriers and the
constant. -/
theorem D_const {X Y : Type*} [Fintype X] [Fintype Y] (b : Bool) :
    D (fun (_ : X) (_ : Y) => b) = 0 :=
  Nat.le_antisymm
    (Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.leaf b, rfl, fun _ _ => rfl⟩)
    (Nat.zero_le _)

/-- A public input on the `YES` branch whose matrix is constant, so that the
`YES` certificate can be inhabited **in full**. -/
def publicInputConst : LevelPublicInput (Fin 3) (Fin 3) :=
  { publicInputYes with R := fun _ _ => false }

/-- **Full inhabitation of `YesCert`.**  Both conjuncts hold: the source half is
`k3_sourceYES` and the complexity half is `D R = 0 <= 0 = Y`. -/
theorem publicInputConst_yesCert : YesCert publicInputConst :=
  ⟨k3_sourceYES, le_of_eq (D_const false)⟩

/-- **`NoCert` is not automatic.**  On the `YES` witness the source half
already fails, so the certificate is a real constraint. -/
theorem noCert_not_automatic : ¬ NoCert publicInputConst := by
  rintro ⟨hno, -, -⟩
  exact EndpointGraph.sourceYES_not_sourceNO publicInputConst.G
    publicInputConst.γpos k3_sourceYES hno

/-- **`YesCert` is not automatic** either: on the `NO` witness the source half
fails. -/
theorem yesCert_not_automatic : ¬ YesCert publicInputNo := by
  rintro ⟨hyes, -⟩
  exact k4_not_sourceYES hyes

/-- **Relative inhabitation of `NoCert`.**  Given the source promise and the
banked robust-seed reading at the input's own `(R, D, b_0)`, the `NO`
certificate holds.  This is where the deferral is localized: the right-hand
side is `SEED-001`'s obligation, not a new one. -/
theorem noCert_of_reading (P : LevelPublicInput V E)
    (hno : P.G.SourceNO P.γ) (h : (noSeed P).noReading) : NoCert P :=
  (noCert_iff_reading P).mpr ⟨hno, h⟩

/-- **Hypothesis-consistency probe for `NoCert`'s complexity half.**

The two complexity conjuncts of `NoCert` -- `comp R = D` at `D >= 3`, and
`D <= Lambda_3(R,1,2^{-b},3/5)` -- are **jointly satisfiable**, so conjoining
them is not a hidden contradiction.  The witness is the banked full-cube seed
at `D = 8`, consumed by pin from `OneLevelCompletion`.

What keeps this from being a full `NoCert` inhabitant is disclosed, not hidden:
the banked `Lambda` bound is proved at requested depth `0`
(`xOut 0 = 1`), while `P5` of `def:level-public-input` demands `b_0 > 0`, and
the banked module records that same range restriction for its own seed.  A
`NoCert` witness at a legal positive `b_0` therefore needs the route's Stage-1
hard seed, which remains Lean pending; nothing here manufactures one. -/
theorem noCert_complexity_conjuncts_consistent :
    3 ≤ 8 ∧ D (fullCube 126) = 8 ∧
      (8 : ℕ) ≤ LambdaGE (fullCube 126) 1 (xOut 0) ((3 : ℝ) / 5) :=
  ⟨by norm_num, fullCubeSeed_D, fullCubeSeed_lambda⟩

/-! ### The trace witness

`G = K_3`, `s = 4` (`3 <= s`, a power of two), `a = 6`, `q = Q = 2`.  The
protected duplication is **proper**: `Rows(A) = [2] x Rows(B)` with the label
genuinely forgotten, so the record is not inhabited only at `A = B`. -/

/-- The base matrix shared by the four pre-duplication slots of the witness:
equality on `Bool`, which is two-valued. -/
def witnessBase : Bool → Bool → Bool := fun x y => decide (x = y)

theorem witnessBase_nonconstant : witnessBase true true ≠ witnessBase true false := by
  decide

/-- The protected duplicate of `witnessBase`: two labelled copies of every row,
with the label forgotten by the entry map. -/
def witnessA : Fin 2 × Bool → Bool → Bool := fun p y => witnessBase p.2 y

/-- The Stage-2 slot of the trace probes, at **both** forced carriers and
**computed**, not chosen.

Since the `cc-t7b` round the Stage-2 matrix is not a free field at all: the value
clause `M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)` (`07:225--226`)
determines it from the probes' own Stage-1 matrix `witnessBase` and the banked
`paramsWitness`'s own stored family `c_2`.  So this definition is the *evaluation*
of the frozen display at those two banked objects -- the vendored
`NPCC.relaxedInterlace` applied to `witnessBase^T` -- and every probe below
supplies it with `M₂_eq := rfl`.  Its row carrier is the frozen
`[q_2] x C_1 = Fin (q2 K3 4) x Bool` (`07:223`) and its column carrier the frozen
`L_2 = [N_2] = Fin 2` (`07:224` with `05:178`) at `paramsWitness`'s own `N_2 = 2`.

**Reader counterpart: none** -- see the module header: the reader's
`eq:paper-M2-definition` is already held by `StageTwoRelaxed.stageTwo`.

**Numeral provenance, itemized over the signature.**  The *body* selects
nothing: it is `relaxedInterlace` applied to two banked objects, so no numeral
occurs in it.  Two numerals occur in the **type**, and neither is chosen here:
* the `4` inside `q2 K3 4` is the banked `traceWitness`'s own scale, carried
  over verbatim.  It is a **NON-FIDELITY** value and is labelled as such at
  `traceWitness`: `s = 4` violates the schedule's `64 | s` (`06:975--976`), so
  this is a probe scale, never the paper's application point;
* the `2` in `Fin 2` is `paramsWitness`'s own `N₂` (`N₂ := 2`), read off the
  banked record rather than picked, via `L_2 = [N_2]` at `05:178`.  It is
  NON-FIDELITY for the same reason: `eq:stage3-carrier-lower-bound` forces
  `N_2 >= 2s` (`06:965--969`, the chain ending `\ge 2s` on line 967). -/
def witnessM₂ : Fin (q2 K3 4) × Bool → Fin 2 → Bool :=
  relaxedInterlace (fun γ x => witnessBase x γ) (paramsWitness (q2 K3 4)).c₂

/-- The computed Stage-2 matrix is still two-valued, so no field of a probe is
satisfied by a constant.  The two points differ only in the `C_1` coordinate
`gamma`, and the frozen value clause reads that coordinate through `M_1`, so this
is nondegeneracy of the *composite* rather than of a chosen table.  General in
the source coordinate `alpha`, which the probe therefore does not have to pick.

**Numeral provenance.**  The only numerals in statement position are the two
column indices `0`, and both are the same one: the canonical **zero-based first
slot** of `[N_2] = Fin 2` under `conv:finite-slots` (`02:14`), at
`paramsWitness`'s own `N_2 = 2` via `L_2 = [N_2]` (`05:178`).  No column is
searched for -- the first slot is the canonical choice, and the statement is
already universal in the row coordinate `alpha`. -/
theorem witnessM₂_nonconstant (α : Fin (q2 K3 4)) :
    witnessM₂ (α, true) 0 ≠ witnessM₂ (α, false) 0 := by
  simp [witnessM₂, witnessBase, paramsWitness, relaxedInterlace]

/-- Non-vacuity: a one-level trace at values legal **for the bare trace
record** -- every field type is inhabited, every clause holds, and the
positive-width interlace operation is applied at `s = 4 > 0`.

**NON-FIDELITY.**  These values are *not* schedule-admissible: the frozen
schedule requires `64 | s` (`06:975`, hence `s >= 64`) and
`N_2 >= 2s` (`06:966--967`), while this witness runs at `s = 4` and `N_2 = 2`.
It is therefore a satisfiability and nondegeneracy probe for `LevelTrace`
itself, never a discharge of canonical inhabitation, which needs
`LevelStep(Public, Pi)` and stays registered and deferred.  The evaluated
consequence `rowsCard M_3 = s N_2 = 8` of `traceWitness_M₃_rows` is
unaffected: it is read off this witness's own values, not claimed of the
schedule. -/
def traceWitness :
    LevelTrace K3 4 (paramsWitness (q2 K3 4)) Bool Bool Bool
      (Fin 2 × Bool) Bool 6 2 2 where
  S := guardedRow K3 4
  C₂ := (paramsWitness (q2 K3 4)).c₂
  π := slotEmbed K3 (by norm_num)
  M₁ := witnessBase
  M₂ := witnessM₂
  M₃ := interlaceFun (fun y x => witnessM₂ x y) 4
  B := witnessBase
  A := witnessA
  N := fun y x => witnessA x y
  U := interlaceFun (fun y x => witnessA x y) 2
  W := fun y x => interlaceFun (fun y' x' => witnessA x' y') 2 x y
  Rnext := fun c r =>
    interlaceFun (fun y x => interlaceFun
      (fun y' x' => witnessA x' y') 2 x y) 2 r c
  fArow := Prod.snd
  rArow := fun b => (0, b)
  fAcol := id
  rAcol := id
  pUrow := Prod.fst
  pUcol := fun p => p.1 p.2
  pQrow := Prod.fst
  pQcol := fun p => p.1 p.2
  H := 6 + Nat.log 2 (q2 K3 4) + Nat.log 2 4 + Nat.log 2 2 + Nat.log 2 2
  mnext := rowsCard (fun (c : Fin 2 → Fin 2 × Bool)
    (r : Fin 2 × (Fin 2 → Fin 2 × Bool)) =>
      interlaceFun (fun y x => interlaceFun
        (fun y' x' => witnessA x' y') 2 x y) 2 r c)
  nnext := colsCard (fun (c : Fin 2 → Fin 2 × Bool)
    (r : Fin 2 × (Fin 2 → Fin 2 × Bool)) =>
      interlaceFun (fun y x => interlaceFun
        (fun y' x' => witnessA x' y') 2 x y) 2 r c)
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

/-- The protected duplication in the witness is **proper**: `A` has twice as
many rows as `B`. -/
theorem traceWitness_A_rows :
    rowsCard traceWitness.A = 2 * rowsCard traceWitness.B := by decide

/-- The label-forgetting map really forgets: it is not injective.  Without this
the witness would inhabit `T4` at the degenerate `A = B`. -/
theorem traceWitness_fArow_not_injective :
    ¬ Function.Injective traceWitness.fArow := by
  intro h
  have := h (a₁ := (0, true)) (a₂ := (1, true)) rfl
  exact absurd this (by decide)

/-- The base matrices of the witness are two-valued, so no field is satisfied by
a constant. -/
theorem traceWitness_B_nonconstant :
    traceWitness.B true true ≠ traceWitness.B true false := witnessBase_nonconstant

/-- The two output cardinalities of the witness at their exact values,
`|Rows(R+)| = (q m_N)^Q = (2 * 2)^2 = 16` and
`|Cols(R+)| = Q n_N^q = 2 * 4^2 = 32`. -/
theorem traceWitness_carriers :
    traceWitness.mnext = 16 ∧ traceWitness.nnext = 32 := by
  constructor <;> decide

/-- The witness's Stage-3 row count is the frozen `s N_2` at its own
`s = 4` and its own `N_2 = 2`, i.e. `8` -- **not** the
two it would have been read as before the equation field landed.  The frozen
`m_3` is `|Cols(M_2)| = N_2 = 2` here, so the witness exhibits the `s`-fold gap
`08:262--263` names.

**Numeral provenance.**  The `8` is **EVALUATED**, not chosen: it is
`s * N_2` computed through `levelTrace_M₃_rows` (whose defining chain is
`07:450`/`07:497` with `03:112--114`, closed at the inner factor by `07:224`
with `05:178`) at the banked `traceWitness`'s own
`s = 4` and `paramsWitness`'s own `N_2 = 2`.  Nothing here selects a row
count. -/
theorem traceWitness_M₃_rows : rowsCard traceWitness.M₃ = 8 := by
  rw [LevelTrace.levelTrace_M₃_rows]; decide

/-- **Name is conceptual shorthand.**  The declaration is named for the frozen
`m_3 = N_2` it is *consistent with*; the statement it actually proves mentions
no `m_3` at all.  Read it as the **`M_2`-column / `N_2` equality at the
one banked witness**: `colsCard traceWitness.M₂ = paramsWitness.N₂`.  Nothing
below identifies `colsCard M_2` with `m_3` in general, and no consumer may read
this name as if it did.

At the witness the frozen `m_3 = N_2` of `06:966`/`06:979` holds on the
nose: `|Cols(M_2)| = N_2 = 2`.  Since the `C₂c` round it is the *evaluation at
one witness* of the general `levelTrace_M₂_cols`, no longer a consistency check
standing in for an open identification: `Cols(M_2) = L_2 = [N_2]` is now forced
by the record itself.

**Numeral provenance.**  The only numeral in the statement is the `4` inside
`q2 K3 4`, the banked `traceWitness`/`paramsWitness` scale `s = 4` carried over
verbatim from those declarations; this theorem selects no value. -/
theorem traceWitness_mThree_eq_N₂ :
    colsCard traceWitness.M₂ = (paramsWitness (q2 K3 4)).N₂ := by decide

/-- **Statement pole for `M₃_eq`.**  The equation field is a genuine
restriction, not a typing convention: at the witness's own carriers there is a
matrix of exactly the field's type that is **not** the `s`-fold interlace of
`M_2^T`, so a trace cannot satisfy `T3` by naming an arbitrary Stage-3 matrix.
The constant-`false` matrix is the trivial candidate and it fails at the single
point `((0, 0), (fun _ => (alpha_0, true)))`, where `alpha_0` is the first slot
of `[q_2]`; there the interlace returns `witnessM₂ (alpha_0, true) 0 = true`.

**Re-typed twice, never weakened.**  At the `C₂c` round the probe's Stage-3
*row* carrier moved from `Fin 4 x Bool` to `Fin 4 x Fin 2`, because
`Rows(M_3) = [s] x [N_2]` became forced.  At `cc-t7b` its **column** carrier
moved in turn, from `Fin 4 → Bool` to `Fin 4 → Fin (q2 K3 4) × Bool`, because
`Cols(M_3) = Rows(M_2)^{[s]}` and `Rows(M_2) = [q_2] x C_1` is now forced too
(`07:223`); the candidate correspondingly moved from constant-`true` to
constant-`false` and the falsifying point from `((0, 1), fun _ => false)` to the
one above, since `witnessM₂` is no longer a chosen table but the computed
relaxed interlace.  The claim -- that the field type admits a non-solution of
`M₃_eq` at the banked witness's own carriers -- is unchanged both times; only
the carriers it is stated at moved to the ones the paper fixes.

**Numeral provenance, and the claim this makes.**  This is a **rejection
probe**: it claims no legality for any object, only that the field's type admits
a non-solution of `M₃_eq`.  The `4` is the banked `traceWitness`'s own `s`, the
`2` is `paramsWitness`'s own `N_2`, the two `0`s are canonical zero-based first
slots (`conv:finite-slots`), and the source coordinate `⟨0, q2_pos K3 4⟩` is the
first slot of `[q_2]` at the banked unconditional `q2_pos`.  Nothing here is
self-chosen. -/
theorem stageThree_equation_is_a_restriction :
    ∃ M : Fin 4 × Fin 2 → (Fin 4 → Fin (q2 K3 4) × Bool) → Bool,
      M ≠ interlaceFun (fun y x => witnessM₂ x y) 4 := by
  refine ⟨fun _ _ => false, fun h => ?_⟩
  have hpt := congrFun (congrFun h (0, 0))
    (fun _ => (⟨0, q2_pos K3 4⟩, true))
  exact absurd hpt
    (by simp [interlaceFun, witnessM₂, witnessBase, paramsWitness,
      relaxedInterlace])

/-- **Statement pole for `M₂_eq`.**  The Stage-2 equation field is a genuine
restriction too, not a typing convention: at the witness's own carriers there is
a matrix of exactly the field's type that is **not** the relaxed interlace of
`M_1^T` by the stored family, so a trace cannot satisfy `T3` by naming an
arbitrary Stage-2 matrix.  The constant-`false` matrix is the trivial candidate
and it fails at the single point `((alpha_0, true), 0)`, where the frozen value
clause returns `M_1(c^{(0)}(alpha_0), true) = true`.

**Numeral provenance, and the claim this makes.**  This is a **rejection
probe**: it claims no legality for any object, only that the field's type admits
a non-solution of `M₂_eq`.  The `4` inside `q2 K3 4` is the banked
`traceWitness`'s own `s`, the `2` in `Fin 2` is `paramsWitness`'s own `N_2`, and
the source coordinate is the frozen zero-based first slot of `[q_2]`
(`conv:finite-slots`), whose legality is the banked `q2_pos`; nothing is
self-chosen. -/
theorem stageTwo_value_clause_is_a_restriction :
    ∃ M : Fin (q2 K3 4) × Bool → Fin 2 → Bool, M ≠ witnessM₂ := by
  refine ⟨fun _ _ => false, fun h => ?_⟩
  have hpt := congrFun (congrFun h (⟨0, q2_pos K3 4⟩, true)) 0
  exact absurd hpt
    (by simp [witnessM₂, witnessBase, paramsWitness, relaxedInterlace])

/-- The witness's Stage-2 row count is the frozen `q_2 |C_1|` at its own guarded
width and its own `C_1 = Bool`.

**Numeral provenance.**  The `2` is **EVALUATED**, not chosen: it is
`Fintype.card Bool` at the banked `traceWitness`'s own Stage-1 column carrier,
reached through `levelTrace_M₂_rows`, whose defining chain is `07:223` with
`conv:finite-slots`.  The `4` inside `q2 K3 4` is the banked witness's own `s`.
Nothing here selects a row count, and the guarded width is left as the banked
accessor rather than evaluated to a numeral. -/
theorem traceWitness_M₂_rows :
    rowsCard traceWitness.M₂ = q2 K3 4 * 2 := by
  rw [LevelTrace.levelTrace_M₂_rows]
  simp

end EthInapproximability.ParameterizedNP.PublicRecords
