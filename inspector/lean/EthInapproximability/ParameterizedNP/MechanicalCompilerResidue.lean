import EthInapproximability.ParameterizedNP.ScheduleMajorantResidue
import EthInapproximability.ParameterizedNP.ScheduleTemplateResidue
import EthInapproximability.ParameterizedNP.SchedulePhysicalResidue
import EthInapproximability.ParameterizedNP.HardSeedFacade
import EthInapproximability.ParameterizedNP.PublicRecords
import EthInapproximability.ParameterizedNP.PilotPCut
import EthInapproximability.ParameterizedNP.DenseBranchSelection
import EthInapproximability.ParameterizedNP.StageTwoRelaxed
import EthInapproximability.ParameterizedNP.BridgeOutputEquality
import EthInapproximability.ParameterizedNP.TerminalTwoStream
import EthInapproximability.ParameterizedNP.MassRedistributionTail
import EthInapproximability.ParameterizedNP.Section5Admissibility

/-!
# Parameterized NP route: the Section-2 mechanical compiler residue

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: opened under **`PARAM-001`** (the schedule-compiler thread), wiring
into `SCHEDULE-MAJORANT-RESIDUE-001` (`ScheduleMajorantResidue`),
`PILOT-PCUT-001` (`PilotPCut`) and `ENVELOPE-REALIZATION-001`.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.
Every anchor below was opened first-hand in that source this tranche; the
41-page reader artifact, the ledger, the crosswalk and every summary are
navigation only.  Unqualified `NN:mmm` line citations are
`sections/02-mechanical-contract.tex`.

## THE `cc-t6x` / `-r1` / `-r2` MIGRATION, stated first because it is this round

**Round marker.**  `cc-t6x` (`r0`) was PARKED at `fe40b1b`, gate REVISE, **0 of
11** delta declarations CLEAR: it replaced the free *width record* correctly and
then left the *Stage-1 matrix* free, which is the same class of defect one level
down.  `cc-t6x-r1` was PARKED at `b22e752`, gate REVISE, **2 of 18** CLEAR: it
pinned the matrix correctly and then routed its exponent `a` through a banked
accessor whose own chain reads a *stored width field*, which is the same class of
defect one level further down again.  `cc-t6x-r2` restores those bytes and
applies the `r1` repair charter; the `r2` seam repair is stated immediately
below, then the `r1` findings, then the unchanged `r0` material.

### `cc-t6x-r2`: the `a` seam, closed on the derived width

**The defect the `r1` gate found.**  `stage1BindingAt`'s exponent was
`Section5Admissibility.aExpOf C`.  That accessor evaluates the right display --
`a = C_0 (log_2 A_*)^2`, `eq:stage1-scales`, `06:314` -- but the `A_*` threshold
it runs through reads the `log_2 q_2` branch of `eq:Astar-choice` as
`Section5Admissibility.lq2Of C = C.W.r_2` (`Section5Admissibility.lean:541`), a
**stored** field of the context's width record, and
`ScheduleTemplateResidue.astarThreshold` genuinely consumes that argument
(`:1002`, a nested `max`, not a discarded slot).  Neither
`DerivedWidths.WidthGateCore` (`Section5Admissibility.lean:3789`) nor
`DerivedWidths.WidthsCoherent` (`:3842`) mentions `C.W` in any conjunct, so no
hypothesis carried anywhere in this module constrained it.  Consequently `a`,
hence `q_1 = 2^a - 2`, hence `m_1 = |Rows(M_1)|`, hence every family-size and
pre-builder statement resting on `m_1`, varied with data the frozen record does
not carry: `05-public-records.tex:188--189` reads "There are no stored width,
tolerance, multiplicity, capacity, ceiling, or output-size fields", and
`05:104--108` prints the field inventory "to make clear which symbols are
accessors rather than stored data".

**The repair.**  A four-step derived chain -- `astarThresholdAt`, `lgAstarAt`,
`aExpAt`, `q1At` -- re-runs `eq:Astar-choice` (`06:298--304`) and
`eq:stage1-scales` (`06:314--315`) with the **derived** `log_2 q_2` of the banked
`Section5Admissibility.DerivedWidths.r2At` (`Section5Admissibility.lean:3604`,
banked at `cc-t6s-r6`) in the branch `06:301` writes `\log_2q_2`.
`stage1BindingAt.a` is that chain's `aExpAt C`, its `three_le_a` is rederived
from `sixteen_le_aExpAt`, and `stageOneAt`, `rowsCard_stageOneAt` and the ten
downstream declarations follow the corrected subject.  **No banked byte is
changed**: the chain is declared here, over the banked pieces, because
`Section5Admissibility` is BYTE-FROZEN under `S5-M3-ROWS-AUDIT-001`.

**What is no longer true of this module, stated exactly so the record does not
lag the code.**  After this round the Stage-1 chain, `stageOneAt`, and all ten
downstream declarations reach neither `Section5Admissibility.lq2Of` nor `C.W.r_2`
in any code position, directly or through a chain.  The banked accessor family
survives in exactly **eight identifier occurrences across two declarations**
module-wide (`astarThresholdOf` x2, `aExpOf` x3, `q1Of` x2, `lgAstarOf` x1); the
accessor `lq2Of` itself occurs **zero** times -- the string `lq2Of` at `:2122`
belongs to the distinct banked bridge-lemma identifier
`DerivedWidths.lq2Of_eq_r2At_of_coherent`, which merely contains it as a
substring.  [COUNT CORRECTED at `cc-t6x-r2` by the verify seat: the `r1` bytes
said "two code positions"; Sol's `r2` FINDING 2 prescribed "nine occurrences",
which double-counted that substring; Sol accepted the eight-occurrence
correction at the verify gate.]  All eight sit inside the conservativity
corollaries `astarThresholdAt_eq_banked_of_coherent` and
`aExpAt_eq_banked_of_coherent`, which name the banked chain **on purpose** in
order to say the two readings agree, and which carry
`StageTwoRelaxed.DerivedWidthCoherent` as an explicit hypothesis for exactly that
reason.  Those two are statements *about* the stored/derived seam, not consumers
of it; no other declaration, and in particular no gate-free one, depends on them.
The disclosure the `r1` gate asked for is therefore not carried forward as a live
caveat about the construction; the paragraph above is its historical record.

### `cc-t6x-r1`: the four confirmed findings and their repairs

**Finding 1 -- a DEFINED quantity re-admitted as a free binder.**  All ten
delta declarations that carried the Stage-1 matrix took it as
`{X₁ Y₁ : Type*} [Fintype X₁] [Fintype Y₁] (M₁ : X₁ → Y₁ → Bool)`.  But
`05-public-records.tex:167--170` says `M_1(Public, K)` "is already determined by
these accessors and the equations in `\Cref{sec:one-level}`", and
`05-public-records.tex:336--337` (step `L2` of `proc:level-step`) gives the
constructor call: "Construct Stage 1, `M_1`, from `R, a, q_1, s` by the carrier
and entry equations".  So `M_1` is DEFINED, and the `r0` migration -- whose whole
point was to stop reading source-defined quantities off free objects -- re-freed
one exactly one level below the width record it had just pinned.

*Repair.*  The Stage-1 matrix is reified as `stageOneAt C`, evaluated through
the definitional chain in dependency order: `a = aExpAt C` (`06:314`; the
`r1` bytes read `aExpOf C` here and cited `06:317`, which is the `b_1` line --
both corrected at `cc-t6x-r2`), `s = sOf C` (`06:118`), `q_1 = 2^a - 2` derived
by the banked
`Stage1SlotBinding.q₁` (receipted equal to `q1At C`), `R = C.P.R` (`P3`,
`05:13--52`), and the carrier/entry equations the banked
`StageOneInterlace.stageOne` already holds
(`eq:stage1-universes-and-value`, `07:141--148`).  Three `rfl` accessor probes
(`stage1BindingAt_a`, `_s`, `_q₁`) put the three input pins in the kernel.  The
binder, the two carriers and their `Fintype` instances are deleted from all ten
declarations, and `m_1` is read as
`BridgeOutputEquality.rowsCard (stageOneAt C)` throughout.

**Finding 2 -- a derived carrier nonemptiness discharged from an assumption.**
`preBuilderScalarPostconditionsHold` proved the frozen `m_1 = |Rows(M_1)| > 0`
of `02:1151` from an assumed `[Nonempty X₁]` instance.  The paper assumes
nothing of the kind: `Rows(M_1) = [q_1] x Rows(R)`, `q_1 > 0` follows from
`a >= 3`, and `m_R > 0` is `P3`'s own guard, so positivity is a **theorem** about
the constructed carrier.

*Repair.*  The instance is deleted.  `rowsCard_stageOneAt` computes
`m_1 = q_1 * m_R` and `rowsCard_stageOneAt_pos` derives `m_1 > 0` from
`Stage1SlotBinding.q₁_pos` and `LevelPublicInput.mRpos`, both consumed by pin.

**Finding 3 -- a gate-independent fact made gate-conditional.**  The `r0` bytes
put `hgate` in the *body* of `SuccessorRow.FamilySizeGuard`, reading the two
widths at `toStoredAt.{0} hgate`, and then recorded the resulting
conditionality of `successorRowFamilySizeGuardAtMajorant` as an honest cost of
the migration.  It was not: the widths that identity lands on are `q2At C` and
`t2At C`, which need no gate, and `bBal_pos` is general.  The round paid the
OPEN `S5-LEVEL-STEP` row for nothing on this endpoint.

*Repair.*  The guard's body is stated **gate-free** at the derived accessors.

**CENSUS CORRECTED at `cc-t6x-r2`** (per Sol's `r2` FINDING 3, re-verified by the
verify seat with a mechanical binder screen over the delta text; the earlier
5/4/1 figure was wrong).  The ten restatements split **4 gate-free / 5 `hgate` /
1 `hcoh`**:

* gate-free (4): `SuccessorRow.FamilySizeGuard`,
  `successorRowFamilySizeGuardAtMajorant`,
  `successorRowFamilySizeGuardRejectsZero`, `familySizeGuardDownwardClosed`;
* `hgate`-carrying (5): `familySizeGuardAtBridgeWidths`,
  `PreBuilderScalarPostconditions`, `preBuilderScalarPostconditionsHold`,
  `preBuilderLegalBuilderInput`, `preBuilderLegalBuilderInputAtDerivedWidths`;
* `hcoh`-carrying (1): `familySizeGuardMajorantAtCoherentWidths`.

`PreBuilderScalarPostconditions` keeps `hgate`, because two of its four clauses
are gate conjuncts -- that one is a real cost and stays recorded; the earlier
census had wrongly classed this `def` gate-free, and had wrongly listed
`familySizeGuardMajorantAtCoherentWidths` (which binds `WidthsCoherent`) among
the gate-free.  The bridge form is recovered as the gated corollary
`familySizeGuardAtBridgeWidths`.

**Finding 4 -- a rejection pole that a gate makes vacuous, plus an over-claim.**
`preBuilderScalarPostconditionsRejectEmptyRowCarrier` was
`forall C hgate, ¬ PreBuilderScalarPostconditions C hgate (empty matrix)`.  A
`forall`-over-`hgate` statement is **vacuously true** while `WidthGateCore`
inhabitation is the OPEN `S5-LEVEL-STEP` row, so as a statement pole it
established nothing -- and its docstring's sentence that it "loses nothing to the
gate" was an over-claim.

*Repair.*  The over-claim sentence is **deleted**.  The pole is replaced by
`rowPositivityRejectsEmptyRowCarrier`, a **gate-free, context-free, closed**
statement about the `02:1151` positivity clause itself: `0 < rowsCard` fails at
a matrix over an empty row carrier.  It carries no universal quantifier, so no
instantiation can make it vacuous, and it is labelled **BEYOND-PAPER AUDIT** in
every value -- `Fin 0` / `Fin 1` are ours, `P3` fixes `m_R, n_R > 0`, and the
paper never visits this point.  It claims no legality.

### `cc-t6x-r1`: LIVENESS notes -- what is landed but UNWIRED

Recorded because a green build witnesses none of it:

* **`stageOneAt` is not a formalized `LevelStep`.**  It is the `L2` call
  (`05:336--337`) evaluated at the context's own accessors.  No `LevelTrace`
  field is wired to it here, and `proc:level-step` as a whole remains the
  REGISTERED, OPEN ledger row `S5-LEVEL-STEP`.  This def does not discharge that
  row and is not offered toward it.
* **Zero downstream consumers.**  A first-hand grep of `src/**/*.lean` for
  `FamilySizeGuard`, `PreBuilderScalarPostconditions`,
  `preBuilderLegalBuilderInput`, `successorRowFamilySizeGuard...` and
  `familySizeGuard...` returns **this module only**.  Nothing downstream would
  break if a migrated statement had the wrong shape, so the build is not
  evidence that these statements are usable at a call site;
  `preBuilderLegalBuilderInputAtDerivedWidths` and
  `familySizeGuardAtBridgeWidths` exist to make the two shapes a consumer would
  want available in advance, and both are currently unused.
* **`WidthGateCore` is still uninhabited on this route.**  So
  `preBuilderScalarPostconditionsHold`, `preBuilderLegalBuilderInput`,
  `preBuilderLegalBuilderInputAtDerivedWidths` and
  `familySizeGuardAtBridgeWidths` have **no instance** yet.  The gate-free
  family-size statements do have instances at any `ScheduleContext`; the only
  `ScheduleContext` this repository builds is
  `ScheduleCompilerExistential.auditContext`, which is downstream, labelled
  NON-FIDELITY at its own declaration, and neither imported nor cited here.
* **`rowsCard_stageOneAt` is not the carrier recurrence of `Rnext`.**  It is the
  Stage-1 row count only.  The frozen `|Rows(R+)| = (q m_N)^Q` recurrence is
  elsewhere and is untouched by this round.

### `cc-t6x-r1`: every touched declaration, judged

`M` = migrated at `r0` and kept, `R` = repaired at `r1`, `N` = new at `r1`,
`D` = deleted, `X` = replaced, `C` = corrected subject at `r2`, `N2` = new
at `r2`.

| decl | verdict | judgement |
|---|---|---|
| `astarThresholdAt` | `N2` | `eq:Astar-choice` at the DERIVED `log_2 q_2` (`06:298--304`) |
| `lgAstarAt` | `N2` | `log_2 A_*` (`06:314`) on the corrected threshold |
| `aExpAt` | `N2` | `a = C_0(log_2 A_*)^2` (`06:314`) on the corrected chain |
| `q1At` | `N2` | `q_1 = 2^a - 2` (`06:315`); one copy of the display |
| `astarThresholdAt_reads_derived_r2At` | `N2` | `rfl` seam receipt: `log_2 q_2` slot is `r2At C` |
| `sixteen_le_aExpAt` | `N2` | `a >= 16` on the corrected exponent (`06:481`) |
| `q1At_add_two_eq` | `N2` | `q_1 + 2 = 2^a` on the corrected chain (`05:418`) |
| `astarThresholdAt_eq_banked_of_coherent` | `N2` | round trip vs the banked threshold |
| `aExpAt_eq_banked_of_coherent` | `N2` | the same, carried to `a` and `q_1` |
| `stage1BindingAt` | `C` | `(a, s)` of `05:336`; `a` now `aExpAt C`; guards derived |
| `stage1BindingAt_a` | `C` | `rfl` receipt, `a = aExpAt C` |
| `stage1BindingAt_s` | `N` | `rfl` receipt, `s = sOf C` (CLEAR at `r1`, byte-pinned) |
| `stage1BindingAt_q₁` | `C` | `rfl` receipt, `q_1 = q1At C`; one copy of `2^a-2` |
| `stageOneAt` | `C` | the `L2` call `05:336--337` at the corrected binding |
| `rowsCard_stageOneAt` | `C` | `m_1 = q1At C * m_R` from `07:144` |
| `rowsCard_stageOneAt_pos` | `C` | finding 2's repair: `m_1 > 0` DERIVED |
| `SuccessorRow.FamilySizeGuard` | `C` | `M₁` dropped, gate-free; `m_1` corrected |
| `successorRowFamilySizeGuardAtMajorant` | `C` | unconditional; corrected `m_1` |
| `successorRowFamilySizeGuardRejectsZero` | `C` | corrected guard, still gate-free |
| `familySizeGuardAtBridgeWidths` | `C` | gated corollary; corrected `m_1` both sides |
| `familySizeGuardDownwardClosed` | `C` | monotonicity of the corrected ceiling |
| `familySizeGuardMajorantAtCoherentWidths` | `C` | corrected `m_1`, both majorants |
| `PreBuilderScalarPostconditions` | `C` | 4th clause at the corrected `m_1`; keeps `hgate` |
| `preBuilderScalarPostconditionsHold` | `C` | `[Nonempty X₁]` gone; corrected 4th clause |
| `preBuilderLegalBuilderInput` | `C` | legal triple at the context, corrected `m_1` |
| `preBuilderLegalBuilderInputAtDerivedWidths` | `C` | consumer form, corrected `m_1` |
| `rowPositivityRejectsEmptyRowCarrier` | `X` | not vacuous (CLEAR at `r1`, byte-pinned) |
| `preBuilderScalarPostconditionsAtBankedWidths` | `D` | renamed duplicate of `...Hold` |
| `CoeffPassChecked` + `tree` + `P2-S2` note + Tie 4 | `M` | `R-8`, record-only, kept |
| `Cert.HasSuccessorRootCount` + its constant-manifest theorem | `M` | `R-9`, record-only, kept |

**READER COUNTERPART DISPOSITION for the five new `r2` auxiliaries** (added at
`cc-t6x-r2` per Sol's `r2` FINDING 6; the per-declaration reader-attribution rule
requires an explicit disposition, and silence is not one):

| decl | reader counterpart |
|---|---|
| `astarThresholdAt_reads_derived_r2At` | **NONE claimable**: migration-only |
| `sixteen_le_aExpAt` | **NONE claimable**: migration-only lower bound |
| `astarThresholdAt_eq_banked_of_coherent` | **NONE claimable**: migration-only |
| `aExpAt_eq_banked_of_coherent` | **NONE claimable**: migration-only |
| `q1At_add_two_eq` | reader `03:142` (`q_1:=2^a-2`) |

The four `NONE claimable` rows are migration-only results -- a `rfl` seam
receipt, a re-derived lower bound, and two conditional round trips -- and the
41-page reader artifact prints no stored/derived seam for them to answer to.

`stageOneAt`'s mention of `eq:paper-M1-definition` (reader `03:153`, label line
`03:156`) is a **CROSS-REFERENCE** to the item already owned by the ledger row
`STAGE1-MODULE-001` (`StageOneInterlace.lean:90`), **not** a counterpart claim by
this module -- so the crosswalk invariant "no reader item is assigned twice"
holds.  [Classification added at `cc-t6x-r2`; Sol concurred at the verify gate.]

The module pin moves again for `r2`; the ledger row carries the recomputed
SHA-256 and the `r2` disposition in the same change.  The
`STAGE2-DERIVED-WIDTH-001` **migration count moves 3 -> 4 on bank** -- while this
round was authored the count stood at 3, because a migration is not banked until
the verify seat commits it; the verify seat of `cc-t6x-r2` did commit, so the
ledger row now reads 4.

This module is the **fourth consumer migration** of the route-ledger row
`STAGE2-DERIVED-WIDTH-001` -- after `WrapperTerminalBlockSupply` (`cc-t6t-r2`),
`ExtensionCallInhabitation` (`cc-t6v`) and `SchedulePhysicalResidue`
(`cc-t6w-r3`) -- whose plan reads "later rounds move consumers across one module
at a time" and "`StageTwoWidths` deletes **last**".

**The recount, first-hand, because the row's count for this module drifted
twice.**  The census below is comment-stripped (nesting-aware block comments,
line comments, string literals preserved), attribute-aware (a count that starts
at a bare `theorem`/`def` head misses every `@[simp] theorem`), and run on both
polarities of the identifier -- the qualified `StageTwoRelaxed.StageTwoWidths`
and a bare `StageTwoWidths`.  The module's only `open` is
`open EthInapproximability.ParameterizedNP`, and it is the module's **sole**
`open` declaration, not
`open ... StageTwoRelaxed`, so the bare spelling is not even in scope here; it
was searched for anyway, and it does not occur.  The result before this round:

| # | line | declaration | binder |
|---|---|---|---|
| 1 | `:1415` | `SuccessorRow.FamilySizeGuard` | `(W : StageTwoWidths)` |
| 2 | `:1425` | `successorRowFamilySizeGuardAtMajorant` | `(W : StageTwoWidths)` |
| 3 | `:1434` | `successorRowFamilySizeGuardRejectsZero` | `(W : StageTwoWidths)` |
| 4 | `:3180` | `PreBuilderScalarPostconditions` | `(W : StageTwoWidths)` |
| 5 | `:3195` | `preBuilderScalarPostconditionsHold` | `(W : StageTwoWidths)` |
| 6 | `:3219` | `preBuilderLegalBuilderInput` | `{W : StageTwoWidths}` |

**Six**, as the ledger row's second count says.  Two further code lines
mentioned the *record namespace* without a binder --
`preBuilderScalarPostconditionsAtBankedWidths` (`:3239`) and
`preBuilderScalarPostconditionsRejectEmptyRowCarrier` (`:3250`), both reading
the banked constant `StageTwoRelaxed.widthsWitness` -- and one read
`StageTwoRelaxed.epsTwo W` (`:3182`) inside occurrence 4.  Those three are
consequences of the six, not extra occurrences, and all three move with them;
they are itemized here so that "six" is a statement about *binders* and not an
undercount of touched lines.  The remaining hits in the file are prose.

**Import-cycle freedom, verified in both directions over the whole `src/`
import graph, and one stale ledger sentence corrected.**  Computed first-hand
by transitive closure of every `import` line under `src/`:

* `Section5Admissibility`'s closure (114 modules) does **not** contain
  `MechanicalCompilerResidue`.  That is the direction cycle-freeness needs, and
  it is the direction the `cc-t6u` BLOCK found violated for
  `MassRedistributionTail`.
* `MechanicalCompilerResidue`'s closure (128 modules) **already contained**
  `Section5Admissibility` before this round, through
  `MechanicalCompilerResidue -> SchedulePhysicalResidue -> Section5Admissibility`
  -- the edge `cc-t6w` itself added.  **The `STAGE2-DERIVED-WIDTH-001` sentence
  "Both are INDEPENDENT of `Section5Admissibility` -- neither imports it and it
  imports neither" was true when written and is now stale for this module**;
  `cc-t6w` made the accessor surface an ancestor of this one.  The correction is
  recorded here and owed to that row.

So the accessor-surface import was **not** absent from the closure, and the
`import` line added at the top of this file is a *directness* change, not a
graph change: it makes the dependency this module now states in its own
statements explicit rather than inherited.  No probe-and-revert was needed for
the cycle question -- the closure computation decides it -- and the build is the
witness that the direct edge elaborates.

**The byte-freeze, lifted deliberately.**  `MECHANICAL-COMPILER-RESIDUE-001`
recorded this module `BANKED ... BYTE-FROZEN` at `cc-t6n-r6` with pin
`159E0D6713665E09E3E4FA7B605C00412610A43D9B2C50F0891CFC779083E67C`, 3309 lines,
169514 bytes, 185 declarations (96 `theorem` + 61 `def` + 8 `structure` +
20 `inductive`).  That pin was **recomputed and re-verified first-hand at the
start of this round on the working-tree bytes and matched exactly**, and the
declaration census was re-run attribute-aware and returned the same 185.  The
freeze is lifted **only** for the migration described here, under the
`STAGE2-DERIVED-WIDTH-001` plan that names this module as a target; the ledger
row is updated with the new pin and the disposition in the same change.  A
byte-freeze certifies a module unchanged, never correct, and lifting one is an
act that has to be recorded rather than a permission that follows from a plan.

**What changes, counted exactly (final `r1` figures).**  Eight existing
declarations are touched -- the six binder-carrying ones of the table, plus the
`r0`-era `preBuilderScalarPostconditionsRejectEmptyRowCarrier` (replaced at `r1`
by `rowPositivityRejectsEmptyRowCarrier`; see finding 4) and
`preBuilderScalarPostconditionsAtBankedWidths` (deleted; see below).  Eleven are
added: the seven-declaration Stage-1 reification `stage1BindingAt`,
`stage1BindingAt_a`, `stage1BindingAt_s`, `stage1BindingAt_q₁`, `stageOneAt`,
`rowsCard_stageOneAt`, `rowsCard_stageOneAt_pos`, and the four migration lemmas
`familySizeGuardAtBridgeWidths`, `familySizeGuardDownwardClosed`,
`familySizeGuardMajorantAtCoherentWidths`,
`preBuilderLegalBuilderInputAtDerivedWidths`.  The module therefore moves from
**185** declarations to **195** -- 104 `theorem` + 63 `def` + 8 `structure` +
20 `inductive`, counted comment-stripped and attribute-aware, and matched 1:1
against `tools/AxiomAudit.lean` (195 rows, no name in one set and not the
other, no duplicate row).  Every other byte of the module is prose.

Each of the six binders above is replaced by

```text
(C : Section5Admissibility.ScheduleContext V E)
(hgate : Section5Admissibility.DerivedWidths.WidthGateCore.{0} C)
```

and every width is read through the banked bridge
`Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate`:

| was | is | defining display |
|---|---|---|
| `W` (the record) | `DerivedWidths.toStoredAt.{0} hgate` | the migration bridge |
| `W.q₂` | `(toStoredAt hgate).q₂` = `q2At C` | `04:386--391`, via `06:122--125` |
| `W.t₂` | `(toStoredAt hgate).t₂` = `t2At C` | `eq:t2-search`, `06:763--772` |
| `W.k₂` | `(toStoredAt hgate).k₂` = `k2At C` | `eq:t2-search`, `06:766--770` |
| `epsTwo W` | `epsTwo (toStoredAt hgate)` | `eq:epsilon-product`, `06:851--857` |

The migrated statements are **instances** of their predecessors -- the old
statement at `W := toStoredAt.{0} hgate` -- so nothing is weakened, no
conclusion is strengthened, and the proof terms are otherwise unchanged.  The
narrowing is the one-way implication old `=>` new; the converse is not claimed,
because `C` is a new universally quantified input.

**The universe, pinned to `0` and not left to inference.**  `WidthGateCore` and
`toStoredAt` carry three universe parameters `[u, u_1, u_2]`, of which the first
is the `HardSeedFacade.mHS` universe (`WidthGateCore`'s first conjunct is
`5 <= m_HS`) and the other two are the carriers `V`, `E`.  This module's
standing rule -- stated at the `K1` note below and forced by `02:799--806`,
"[`m_HS`] is selected once and hardwired into the finite code of `A_cert`" -- is
that the threshold is read at the **one** universe this route's carriers inhabit
(`conv:finite-slots`), never as a universe-indexed family.  Leaving the level to
inference would have auto-bound a fresh universe on each migrated declaration
and reintroduced exactly that family, so every occurrence here writes
`.{0}` and the two carrier levels stay inferred from the `V E : Type*` binders.
This is the same value the `K1` block below already reads, at
`HardSeedFacade.mHS.{0}` in `tLeastExists`, `tLeastSpec`, `tLeastMinimal` and
`k1HardSeedFloor`.

**The one-scale rule, and the `r0` reading of it that was wrong.**  The `cc-t6t`
`D07` / `cc-t6w-r0` defect is a *free* scale `s` standing beside a quantity
already determined through `Section5Admissibility.sOf C`.  No declaration
touched by this round binds `s`, `q`, `b_T`, `m_3` or any other schedule scale
*directly*: the statements mention exactly `q_2`, `t_2`, `eps_2`,
`m_1 = |Rows(M_1)|`, `B_bal` and the stored family size `N_2`.

The `r0` bytes then wrote, of `m_1`, that it "was already pinned to
`BridgeOutputEquality.rowsCard M₁` of the actual Stage-1 matrix".  **That
sentence was false and is withdrawn.**  `rowsCard M₁` pins `m_1` to *whatever
matrix is supplied*, and `M₁` was a free binder over free finite carriers, so
the quantity was not pinned at all -- and `a` and `s` re-entered through the back
door as the free carriers' unconstrained shape.  At `r1` the matrix itself is
reified (`stageOneAt C`), so `m_1 = |Rows(stageOneAt C)| = q_1 * m_R` is
evaluated from the context, and `a`/`s`/`q_1` are pinned with it.

Of the six quantities: `q_2`, `t_2` and `eps_2` are pinned through the derived
accessors / the bridge; `m_1` is pinned through `stageOneAt C`; `B_bal` is the
banked `ScheduleMajorantResidue.bBal`; and `N_2` is **genuinely free at its own
frozen site**, because `02:519--520` makes the successor row *conditional on
what the compiler literally stored* and `02:1142--1143` says in as many words
"do not choose `N_2` or `c_2`".  Zero source-defined quantities remain as free
binders in these statements.

**One declaration deleted, and the deletion is judged rather than silent.**
`preBuilderScalarPostconditionsAtBankedWidths` (`:3237--3240`) said "the helper
is inhabited at the banked `StageTwoRelaxed.widthsWitness`".  Under the
migration the helper's width argument is no longer a record but the context's
own bridge, so that statement becomes
`forall C hgate, PreBuilderScalarPostconditions C hgate` -- which is
**literally** `preBuilderScalarPostconditionsHold`, argument for argument.
Keeping it would bank a renamed duplicate, which this campaign has paid for
five times.  It is deleted; its `#print axioms` row goes with it; and the
honest consequence is recorded in the next paragraph rather than hidden by the
deletion.

**The cost, recorded and not hidden: ONE endpoint becomes CONDITIONAL
(`r0` said two; `r1` corrects the count downward).**
Before this migration `preBuilderScalarPostconditionsHold` and
`successorRowFamilySizeGuardAtMajorant` held at *every* `StageTwoWidths`, and
`StageTwoRelaxed.widthsWitness` was an unconditional inhabitant of the displayed
scalar region.

After it, `preBuilderScalarPostconditionsHold` carries
`hgate : WidthGateCore.{0} C`, whose canonical inhabitation is the paper's own
`proc:level-step` call (`05:318--364`) and therefore the **already REGISTERED
and OPEN** ledger row `S5-LEVEL-STEP`.  That cost is real and irreducible: two
of its four clauses, `4 t_2 <= q_2` and `16 <= t_2`, *are* gate conjuncts.

`successorRowFamilySizeGuardAtMajorant` does **not** pay it, and the `r0` claim
that it did was a defect of that round's shape, not a fact about the migration
-- see finding 3 below.  Its statement is unconditional again, now at the
derived widths.

This round inherits the `S5-LEVEL-STEP` deferral, enlarges it by nothing, and
**manufactures no probe for it**: no synthetic `ScheduleContext` is built here,
and `ScheduleCompilerExistential.auditContext` -- which is downstream of this
module and labelled NON-FIDELITY at its own declaration -- is neither imported
nor cited as evidence.  What is gained in exchange is that the widths and the
Stage-1 matrix these statements speak about are the ones a schedule actually
produces, instead of every record a constructor admits and every Boolean matrix
over every pair of finite types; that is the whole point of
`STAGE2-DERIVED-WIDTH-001`, and it is a trade, not a free improvement.

**The two registered record-defects `R-8` and `R-9` are DISCHARGED here, because
this is the tranche their registration named.**  `MECHANICAL-COMPILER-RESIDUE-001`
recorded them as "deliberately unrepaired, because any comment edit would move
the frozen pin ... owed to a future tranche that re-opens this module".  The pin
moves in this round anyway, so the excuse expires with it:

* **`R-8`** (Sol, `cc-t6n-r4`): `SuccessorRow.CoeffPassChecked` overstated
  "complete checked proof tree".  Repaired at four sites -- the `tree` field's
  own docstring, the `CoeffPassChecked` docstring, the `P2-S2` note and Tie 4 of
  `PartialLedgerInterfaces` -- each now saying that the frozen phrase names the
  *slot* and that the checker verifies three local conditions
  (root-headedness, parent range, ledger resolution), completeness being the
  unbuilt `CoeffPassDerivation` evaluator, REGISTERED.
* **`R-9`** (Sol, `cc-t6n-r4`): the duplicate-rejection prose was too strong --
  it claimed the length test was "all that is expressible", where in fact a
  local `Nodup` on the stored successor root IDs is expressible without the
  untranscribed registry and would already break
  `partialSchemaScreenAdmitsAConstantSuccessorManifest`; only canonical *order*
  needs the appendix table.  The overstatement is **withdrawn** at both sites
  (`Cert.HasSuccessorRootCount` and that theorem), and the `Nodup` clause is
  deliberately **not** added, because adding a screen clause changes
  `PartialLedgerInterfaces`' surface and is not a migration round's business.

Both repairs are record-only: no statement, hypothesis, conclusion or proof term
moves for either.

**No new structure, no new premise bundle, no new axiom.**  `WidthGateCore` is
banked and consumed by pin; `toStoredAt`, `toStoredAt_fields`, `WidthsCoherent`,
`DerivedWidthCoherent`, `q2At`, `t2At`, `k2At`, `t2At_eq_two_pow_k2At`, `bBal`,
`bBal_pos`, `rowsCard`, `epsTwo` and `StageTwoWidths.five_le_k₂` /
`.four_t₂_le_q₂` are all consumed with their arguments never re-run.  The
`cc-t6x-r1` reification adds only *consumption*: `FiniteSlots.Stage1SlotBinding`
(banked structure, applied -- not redeclared), `Stage1SlotBinding.q₁` /
`.q₁_pos`, `StageOneInterlace.stageOne` / `.Stage1Rows` / `.Stage1Cols`,
`Section5Admissibility.sOf` / `.sOf_floor` / `.BpubOf` / `.zROf` / `.clU0Of`,
`Section5Admissibility.DerivedWidths.r2At` / `.lq2Of_eq_r2At_of_coherent`,
`ScheduleTemplateResidue.astarThreshold` / `.astarExp` / `.q1Stage1` /
`.sixteen_le_astarThreshold` / `.four_le_astarExp`,
`MassRedistributionTail.aStage1`, and
`PublicRecords.LevelPublicInput.R` / `.mR` / `.mRpos`.  (`cc-t6x-r2` withdraws
the consumption of `Section5Admissibility.aExpOf` / `.q1Of` /
`.sixteen_le_aExpOf` from the construction: the first two survive only inside the
two conservativity corollaries, and the third is not consumed at all.)  No
structure, inductive or class is declared by this round or the last; the new
`def`s are banked-function applications and one banked-structure application.
`LegacyNPCC.Stage12` is still not reached by any declaration of this module, so
no opt-in ledger note is owed for the AGHP axiom.

## Scope

This module addresses the **eleven open Section-2 items** of
`sec:mechanical-contract` that the banked schedule modules left unstated.

| # | frozen anchor (`02-mechanical-contract.tex`) | declaration |
| --- | --- | --- |
| 1 | `def:effective-schedule-certificate`, label 177, body 176--554 |
  `CoreSort` .. `Cert` (including the typed alphabets `TailClass`, `NodeLeaf`,
  `NodeOp`, `ElabObligation`), `preIndicesDependencyClosed`,
  `terminalCodeToValue` |
| 2 | `eq:balanced-family-envelope`, label 187, display 183--188 |
  *(none -- consumed by pin from `ScheduleMajorantResidue.bBal`)* |
| 3 | `eq:balanced-family-log-envelope`, label 193, display 189--194 |
  `balancedFamilyLogEnvelope` |
| 4 | `eq:balanced-family-binary-length-envelope`, label 300, display 293--301 |
  *(none -- consumed by pin from `ScheduleMajorantResidue.n2ExplicitCodeEnvelope`;
  the new composite is `balancedFamilyCodeEnvelopeTerminal`)* |
| 5 | `thm:eff-ledger`, label 570, statement 569--650, quantifier prefix 630--649 |
  `PartialLedgerInterfaces`, `EffLedgerSchemaHyp`, `EffLedgerPartialSchema`,
  `effLedgerPartialSchemaSingleState` -- an **auxiliary** shape over an
  explicitly **partial** screen, not the theorem and not `SchemaChecked` |
| 6 | the nine-block manifest `G1--G9`, 663--707 | `ManifestBlock`,
  `ExtSchema`, `ExtensionCoverageClosed`, `ManifestRowKind` |
| 7 | the universal constants `K1--K4`, 798--903 | `KStep`, `Czero`,
  `cBconst`, `czeroMeetsStage1C0Gate`, `tLeast`, `jZero`, `cIn`, `k4M`
  *(`K2` lands no declaration here -- consumed by pin from
  `ParameterSchedule.kref_j49_candidate` and `.jrefStar_le_j49`, so `L_P` never
  occurs in this module)* |
| 8 | the compiler `C1--C8`, 905--1120 | `CompilerStep`,
  `CutoffPendingTarget`, `dcOf`, `ecOf`, `pcutTriple`
  *(`lambda_0` itself is consumed by pin from `DenseBranchSelection.lambdaZero`)* |
| 9 | the static rows `S1--S5`, 1228--1300 | `StaticLemma`, `s2*`, `s4*` |
| 10 | `eq:pre-input-envelope`, label 757, display 741--758 |
  `InputEnvelopePre` and its three companions |
| 11 | `clm:eff-ledger-prebuilder`, label 1141, claim 1140--1161 |
  `PreBuilderScalarPostconditions` and its companions -- a **helper**, not the
  claim (the claim's hypotheses and its "halts and returns" conclusion are
  GAP-EXPOSED 1) -- and `PreBuilderSearch`
  *(the `K2` record's `K_0`, `Z`, `k_2^*` of `02:1194--1197`
  are consumed by pin from `ParameterSchedule.k2Floor`, `.zEndpoint`, `.k2Star`
  and land no declaration here)* |

## What is consumed by pin and never restated

* `X_bal`, `B_bal` and the literal binary-length envelope --
  `ScheduleMajorantResidue.xBal`, `.bBal`, `.two_le_xBal`, `.bBal_pos`,
  `.n2ExplicitCodeEnvelope`.  Items 2 and 4 of the table above therefore land
  **no declaration of their own**: `02:183--188` is `bBal` and `02:293--301`
  is `n2ExplicitCodeEnvelope` with the binders renamed, and the fixed-interface
  discipline forbids a second copy.
* `l(n) = max{2, ceil(log_2 log_2(n+16))}`, `E_d(n) = 2^{l(n)^d}` and
  `B(n) = E_2(n)` (`02:164--171`) -- `IterationAssembly.ellN`, `.envE`,
  `.depthB`, `.ellN_spec`, and the elementary `M^2+2M+4 <= 2^M` of `02:892`
  is `IterationAssembly.sq_le_two_pow`.
* `j_49` and its two eliminators (`02:826--827`, `02:1218--1222`) --
  `ParameterSchedule.j49`, `.j49_max`, `.j49_le`, and the predicate itself is
  `RawLowProfileBody.J49Feasible`.
* `c_seed = 100` (`02:808`) -- `ParameterSchedule.cSeed`; `k_ref^* = 100 L_P^2`
  (`02:1200`) -- `ParameterSchedule.krefStar`; `L_P = clog_2 P_0` and the
  displayed `P_0` maximum -- `ParameterSchedule.LPwidth`, `.P0sched`,
  `.sScale`, `.leastPowTwoExp`, with `U_0` and `eta_R` from
  `ScheduleTemplateResidue.U0sched` and `ParameterSchedule.etaR`.
* `m_HS = min{r : HSThreshold(r)}` (`02:800--803`, Appendix D) --
  `HardSeedFacade.mHS`.  No numeral is assigned to it anywhere below.
* `K_* = (C_0, c_seed, A_wrap, B_s, c_b, C_in)` as a record (`02:899--902`,
  `def:level-configuration`) -- `PublicRecords.LevelConfig`.  This module
  declares **no** second configuration record; it lands only the two literal
  constants `C_0` and `c_b` that `02:808` prints and `LevelConfig` leaves as
  fields.
* `A_wrap`'s search nonemptiness (`02:878--893`) --
  `IterationAssembly.awrap_search_nonempty`, `.awrap`,
  `.coefficientPass_awrap`.
* the shifted `PCut` absorption of `02:1100--1105` --
  `PCutPred`, `pCut_shifted_certificate` (namespace
  `EthInapproximability.ParameterizedNP`).
* the tested-endpoint termination witnesses of `02:1205--1208`,
  `x <= 2^x` and `u/v <= u <= 2^u` --
  `SchedulePhysicalResidue.natTerminationWitness`, `.ratTerminationWitness`,
  `.abs_le_natAbs_num`.
* `n^2 <= 2^n` for `n >= 4` -- `ScheduleTemplateResidue.sq_le_two_pow`.
* `eq:stage1-C0-gate` itself (`06:306--311`) -- `MassRedistributionTail.stage1C0Gate`,
  a predicate of the configuration field `C_0`.  This module only checks it at
  the frozen `C_0 = 152` (`czeroMeetsStage1C0Gate`); it declares no second copy.
* the `eq:epsilon-product` conclusion `eps_prod < 1/50` (`06:851--857`,
  `02:1252--1253`) -- `TerminalTwoStream.epsProd_lt_fiftieth`.
* the `j_49` feasible-set endpoints of `02:1218--1222` --
  `RawLowProfileBody.J49Feasible.zero` and `.le_index`.
* the Stage-2 dyadic widths `q_2 = 2^{r_2}`, `t_2 = 2^{k_2}` and their frozen
  gates -- **since `cc-t6x`** the banked derived accessors
  `Section5Admissibility.DerivedWidths.q2At` / `.t2At` / `.k2At`, reached
  through the banked bridge `.toStoredAt` from
  `Section5Admissibility.DerivedWidths.WidthGateCore`, whose presentation
  carries the banked `StageTwoRelaxed.StageTwoWidths` theorems `four_t₂_le_q₂`
  and `five_le_k₂`; `eps_2 = 1/(100 t_2)` -- `StageTwoRelaxed.epsTwo` at that
  same bridge record; `m_1 = |Rows(M_1)|` -- `BridgeOutputEquality.rowsCard`
  applied, **since `cc-t6x-r1`**, to this module's own `stageOneAt C` rather
  than to a free matrix.
  The migration identity `epsTwo (toStoredAt hgate) = 1/(100 t2At C)` is the
  banked `SchedulePhysicalResidue.migratedEpsTwo_at_derived_t₂` and is not
  restated here.
* `A_pre` and `u` of `eq:s-choice` (`06:111--117`) --
  `ParameterSchedule.Apre` and `.uAux`.
* the two `K2` comparisons of `02:855--859` --
  `ParameterSchedule.kref_j49_candidate` (`06:615--621`) and
  `.jrefStar_le_j49` (`06:622--624`), consumed by pin; this module lands no
  `K2` declaration of its own (see the note before `K3`).
* the public record `Public` itself -- `PublicRecords.LevelPublicInput`, whose
  fields `InputEnvelopePre` reads; and the `r`-copy source family of
  `04:196--204` -- `GuardedSourceGraph.K3`, `.k3_degree`,
  `EndpointGraph.copies`, `.degree_copies`.

## DEFINED-vs-FREE

Every symbol of the eleven items was classified against the frozen source
before it was written; a **DEFINED** one is reified here only when no banked
reification exists, and each new reification cites its own defining display.

* `bl(x) = clog2N(x+1)` with `clog2N(x) = min{r : x <= 2^r}` (`02:279--283`).
  As in `ScheduleMajorantResidue`, this gets **no** Lean definition on this
  route: every statement below that needs it writes the inline
  `Nat.clog 2 (x + 1)`, which is the frozen display verbatim.
* `C_0 = 152`, `c_b = 6` (`02:808`) -- `Czero`, `cBconst`.  `c_seed = 100` of
  the same display is the banked `ParameterSchedule.cSeed` and is not copied.
* `T` = the least integer with `T >= 64` and `9T^2 - 2 >= m_HS`
  (`02:815--817`), and `B_s = T^2` (`02:819`) -- `tLeast`, `bsSched`, over the
  banked `HardSeedFacade.mHS`.  Both are **single naturals**: `02:799--806`
  hardwires one `m_HS`, so neither declaration carries a universe binder.
* `c_eps = c_D + 2` (`14:1455`) -- `cEpsOf`, over the fixed exponent `c_D` of
  the cited Dinur adapter (`thm:dinur-adapter`, `14:689--698`).  It is a
  DEFINED quantity and is never a binder.
* `j_0(v) = max{0, floor(49v/100) - 1}` (`02:821`) -- `jZero`.  Natural
  truncated subtraction *is* the frozen outer maximum with zero, by the
  semantics `subN(x,y) = max{x-y,0}` of `02:280`.
* `L_P` at its full defining chain `L_P = clog_2 P_0`, `P_0` the maximum of
  `06:467--470`, `U_0 = max{2, b_out/eta_R}` of `06:295--297`, `s = 2^{ceil(B_s
  u^2)}` and `u = clog_2(clog_2(A_pre+16))` of `eq:s-choice` (`06:111--118`) --
  **no declaration of its own here, and no occurrence at all**.  The only rows
  of this module that ever mentioned `L_P` were the two `K2` restatements, both
  deleted (see the note before `K3`); `02:855--859` is consumed by pin from
  `ParameterSchedule.kref_j49_candidate` and `.jrefStar_le_j49`, which are
  general in `L_P`.  No statement below binds `L_P`, `P_0`, `s`, `U_0`,
  `eta_R`, `B_s` or `u` freely.
* `C_in` = the maximum of zero and the emitted additive binary-loss constants
  (`02:869--871`) -- `cIn`.  Its argument is the emitted list, which is
  compiler output and therefore genuinely free.
* `d_c = 8(c+1)`, `e_c = 16(c+1)` and the absorbed triple
  `(2^{d_c} C_u, d_c, e_c)` (`02:1031--1035`, `02:1096--1099`) -- `dcOf`,
  `ecOf`, `pcutTriple`.
* `lambda_0 = q_2 2^{1-b_1}` (`02:1084`) -- **consumed by pin** from the banked
  `DenseBranchSelection.lambdaZero`, which reifies the *same* quantity at
  `08:796` in the equal frozen form `lambda_0 = 2 q_2 2^{-b_1}`.  This module
  lands no `lambda_0` of its own; it only records, in
  `lambdaZeroSignedExponentPole`, that the banked quotient form is the reading
  `02:400--403` demands and not natural truncated subtraction.
* `K_0 = max{4, 2^19, m_HS}`, `Z = max{16, K_0, clog_2(H_max+1)}`,
  `k_2^* = K_0 + 10000 Z^2` (`02:1194--1197`) -- **consumed by pin** from the
  banked `ParameterSchedule.k2Floor`, `.zEndpoint`, `.k2Star`.  This module
  declares no reification of its own for them.
* `eps_2 = 1/(100 t_2)` (`02:1150`) and `m_1 = |Rows(M_1)|` (`02:1151`) --
  **consumed by pin** from `StageTwoRelaxed.epsTwo` and
  `BridgeOutputEquality.rowsCard`.  Neither is a binder anywhere below.
  Since `cc-t6x-r1` the *matrix* `M_1` is not a binder either: it is
  `stageOneAt C`, the `05:336--337` constructor call at the context's own
  accessors (`05:167--170`).
* the four tail classes of `eq:four-tail-errors` (`06:1712--1717`) --
  `TailClass`, a closed four-constructor type, because `02:475--476` restricts
  `e_r` to exactly those four.
* the typed operation alphabet `(Op)`--`(SearchOp)` (`02:222--271`,
  `02:327--332`) -- `NodeOp`; the leaf productions of `02:224` -- `NodeLeaf`;
  the three lowering obligations of `02:389--393` -- `ElabObligation`.

The quantities that stay **FREE in the frozen source itself**, and are
therefore binders, are exactly: the source size `n`; the fixed source constants
`Delta_eps`, `gamma_eps`, `Delta_v`, `zeta` and the cited-adapter exponent
`c_D`, whose existence `thm:dinur-adapter` (`14:689--692`) asserts without
printing a value -- **`c_eps` is not among them**, because `14:1455` defines it
as `c_D + 2`, and `InputEnvelopePre` accordingly takes `c_D` and evaluates
`cEpsOf`; the incoming exponent
`c`; the numerical source width `q_2` and its logarithm outside the Stage-2
width record; `C_cert`, `z_R`, `B_pub`, `H_max`, `clog_2(|E|+2)`; the level's
remaining dyadic widths `q_1`, `q`, `Q`; the compiler's own emitted rows
(binary-loss constants, `C_exc^0`, `B_exc^0`, `C_u`), which `06:1628--1631`
forbids a formalizer to supply; and the abstract `Config`, `Machine` and
`Context` carriers of `PartialLedgerInterfaces`, together with the evaluation
`val` that `GateRow.TiedTo` takes as an explicit named argument because the
interpreter of `02:459--462` is GAP-EXPOSED 1.  Each is licensed at the anchor cited
in its declaration.  The public data `N_V`, `N_E`, `m_R`, `n_R`, `D`, `Y`,
`b_0`, `b_out`, `Delta`, `gamma` are **no longer binders**: they are read from
`PublicRecords.LevelPublicInput`, which is what `02:763--764` requires.

Every quantity the frozen source **defines** is pinned rather than bound: `T`
and `B_s` through `tLeast`/`bsSched`, `m_HS` through `HardSeedFacade.mHS` read
at the one universe of `conv:finite-slots` carriers, `c_eps` through `cEpsOf`
(`14:1455`), `L_P` and its whole `P_0`/`U_0`/`eta_R`/`s`/`u` chain by having no
occurrence in this module at all,
`l(n)` through `IterationAssembly.ellN`, `B(n)` through `.depthB`, `E_c(n)`
through `.envE`, `c_seed` through `ParameterSchedule.cSeed`, `k_ref^*` through
`.krefStar`, `j_49` through `.j49`, `K_0`/`Z`/`k_2^*` through
`.k2Floor`/`.zEndpoint`/`.k2Star`, `M` through `k4M`, `t_2`/`q_2`/`eps_2`
through `Section5Admissibility.DerivedWidths.t2At`/`.q2At` and
`StageTwoRelaxed.epsTwo`, both reached from the context by the banked bridge
`.toStoredAt` (**`cc-t6x`**; before that round they were read off a free stored
width record), `m_1` through `BridgeOutputEquality.rowsCard (stageOneAt C)`
(**`cc-t6x-r1`**; before that round it was read off a free matrix binder, which
pinned nothing -- see finding 1), and the tested value `v = Tu` of K1 through
`k1ScheduledComparisons`.  The only source-defined symbols left as universally
quantified variables are the ones the frozen text itself quantifies at that
display: `v` in the three K1 comparisons (proved for every `v` above the frozen
floor, and applied only at the pinned `tLeast * u`) and `t` in `S2`
(`02:1240`, "For `t = t_2 >= 1`").

## GAP-EXPOSED

1. **The recursive interpreter, not the node fields.**  `02:454--461` gives
   each node of `Nodes_c` a sort, a *name*, a *literal-or-primitive-symbol
   leaf*, a *typed operation* from `(Op)`--`(SearchOp)` (`02:222--271`,
   `02:327--332`), ordered parents, its *expected-sort elaboration
   obligations* (`02:389--393`), a coefficient, a degree and a phase tag.
   `NodeRow` now carries **all nine**.  What is unbuilt is the recursive
   interpretation `sembracket{u}_Xi` of `02:460--462` -- a *function* on the
   record, needing `val_Xi` and `LevelStep(Public, Pi)` (`02:425--444`).  No
   predicate below evaluates a node, and nothing claims that interpreter.
2. **`SchemaChecked`, `NumChecked`, `Successor_16` are not implemented, and
   nothing here occupies `SchemaChecked`'s slot.**  They enter
   `EffLedgerPartialSchema` only as *interface fields* of
   `PartialLedgerInterfaces`.  The field standing where the frozen
   `SchemaChecked` would stand is named `partialSchemaScreen`, because it is
   strictly weaker: it is constrained to imply only the phase rule
   (`02:527--528`), the in-range pointer condition (`02:527`), the
   successor-root count (`02:529`, `02:1086`) and the coefficient-pass check
   (`02:1045--1046`).  Everything else `02:526--540` demands -- registry
   equality in canonical order, the pinned registry hash and generated counts,
   one coverage pointer per target, topological earliness, resolution of every
   reference, exactly the four registered Extension roots, and no pending
   compiler tag -- is absent, and
   `partialSchemaScreenAdmitsAConstantSuccessorManifest` proves in the kernel
   how far that reaches: a manifest of `173` identical rows passes the screen.
   `Cert.HasSuccessorRootCount` is likewise named a count precisely because the
   registry equality of `02:530--532` needs the appendix registry table that
   this route has not transcribed.

   What the module *does* now carry, which the `r2` form did not, is the
   `CoeffPassDerivation` content of `02:1042--1046`: `SuccessorRow` stores the
   exact root expression and a proof tree in the adjacency form of
   `CoeffPassStep` alongside the root, `C_u` and `d_c` (**`R-8`, `cc-t6x`:** the
   frozen sentence's word "complete" names the slot and is not delivered by this
   encoding -- see the field's own docstring), and
   `SuccessorRow.CoeffPassChecked` performs the frozen rejections -- missing
   tree, root/expression/coefficient mismatch, unresolved ledger citation.
   Storing and checking that tree is still not *evaluating* the graph: no
   declaration here rebuilds the withdrawn coefficient-pass **evaluator**, and
   no 29-row persistent tail registry or registry-shape predicate is declared.
3. **`thm:eff-ledger` itself is neither stated nor proved.**  What is landed is
   `EffLedgerPartialSchema`, the *shape* of `02:630--649` at an arbitrary
   interface **and over the weakened first conjunct**; the frozen theorem is
   that shape at the canonical interface whose three checkers are the
   executable predicates of `02:526--550`, and building those needs the whole
   compiler `C1--C8` together with GAP-EXPOSED 1 and 2.  The two poles below
   show the shape is neither trivially true nor trivially false, which is all
   an auxiliary landing may claim.
4. **`G1--G9`, `C1--C8` row contents.**  The nine manifest blocks, the eight
   compiler steps, the four constant-fixing steps and the five static rows are
   landed as *complete named rosters with their frozen content in the
   constructor docstrings*, together with the arithmetic each of them proves
   that is expressible without the node graph.  What is **not** landed is the
   expansion of a block into its atomic clauses, because `02:658--660`
   defines that expansion by splitting `def:admissibility-groups`, whose
   displays live in `sections/06-parameter-schedule.tex` and are the province
   of the banked schedule modules.
5. **`S1`, `S3`, `S5`.**  Their conclusions are analytic consequences of
   `eq:j49-window`, `eq:tref-search`, `eq:t2-search`,
   `eq:all-extension-gates` and the four Localized-Extension legal-domain
   predicates, all of which are Section-6 and Appendix-D surfaces owned by
   other rows.  They are landed as roster entries with their frozen content
   in docstrings; `S2` and `S4`, whose proofs `02:1240--1252` and
   `02:1264--1287` print in full and which need no Section-6 display, are
   **proved**.

## Non-vacuity and canonical inhabitation

* `Cert` carries the paper's `Cert_c` fields.  The paper constructs exactly one
  inhabitant, `Compile(c)` (`02:905--1120`), and that construction needs
  GAP-EXPOSED 1, 2 and 4.  The canonical-inhabitation obligation is therefore
  **ledger-REGISTERED and deferred** (`MECHANICAL-COMPILER-RESIDUE-001` in
  `routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), discharged
  only when `Compile` lands.  `probeCert` is the interim smoke inhabitant and is
  explicitly **NON-FIDELITY**: `probeCertIsNotThePaperCertificate` proves in the
  kernel that it fails even the `173`-row count of `02:1086`, so it can never be
  mistaken for the paper's object.
* `InputEnvelopePre` is inhabited by a **general** family at an actual public
  record: `sourcePublicInput` builds `r` disjoint `K_3` copies through the
  banked `EndpointGraph.copies`, and `inputEnvelopePreNondegenerate` inhabits
  the envelope at every copy count `r >= 1`, every legal incoming exponent and
  every legal pair of fixed source constants, with `m_R = n_R = 2` and
  `D = Y = 3` taken from the frozen floors `02:749` and `02:760`, not chosen.
  Its companion `inputEnvelopePreForcesTwoLeC` proves the legality side
  condition `c >= 2` is *forced* by conjuncts 9 and 16 of the frozen list rather
  than assumed, which is this module's hypothesis-consistency receipt.
* `PreBuilderScalarPostconditions` is a **helper**, and its name no longer
  claims the claim: it is not a constraint on free scalars (all four of its
  clauses are *proved*, of the context's own derived widths and its own Stage-1
  matrix, by `preBuilderScalarPostconditionsHold`; and its fourth clause has
  teeth, the empty row carrier refuting it at
  `rowPositivityRejectsEmptyRowCarrier`), but it represents **none** of
  `clm:eff-ledger-prebuilder`'s
  operative content -- not its three hypotheses, and not "exact evaluation of
  the `pre` slice halts and returns".  That whole claim is GAP-EXPOSED 1 and
  stays registered; nothing here is offered as evidence for it.
* `EffLedgerPartialSchema`'s two poles are
  `effLedgerPartialSchemaIsNotTriviallyTrue` (a refuting instantiation) and
  `effLedgerPartialSchemaHoldsAtAnAuditInterface` (an explicitly
  **BEYOND-PAPER** satisfiability audit at an interface the paper never visits,
  whose certificate `auditCert` must actually meet the four expressible clauses
  of `02:526--540` and `02:1042--1046`).  Neither is offered as evidence about
  the paper's instance, and
  `partialSchemaScreenAdmitsAConstantSuccessorManifest` measures, in the
  kernel, exactly how weak the audit interface's screen is.
* `SuccessorRow.CoeffPassChecked` carries its own three general rejection
  lemmas (`successorRowCoeffPassRejectsMissingTree`,
  `...RejectsCoefficientMismatch`, `...RejectsUnresolvedLedgerRef`) and is
  satisfied by `auditSuccessorRow` at `probeNodes`, so it is neither vacuous
  nor unsatisfiable.  It is **NON-FIDELITY** at that witness: the paper's own
  successor rows come from `Compile(c)`.
* `ExtensionCoverageClosed` is inhabited (`extensionCoverageProbeIsClosed`) and
  guarded on both sides (`extensionCoverageRejectsAMistaggedPointer`,
  `extensionCoverageRejectsASharedRow`).
* `SearchRow` and `SuccessorRow.FamilySizeGuard` carry their own general
  facts (`searchRowReturnedUnique`, `searchRowDecidesEverywhere`,
  `successorRowFamilySizeGuardAtMajorant`,
  `successorRowFamilySizeGuardRejectsZero`, and since `cc-t6x` the three
  migration lemmas `familySizeGuardAtBridgeWidths`,
  `familySizeGuardDownwardClosed`, `familySizeGuardMajorantAtCoherentWidths`).
  The satisfiability fact `successorRowFamilySizeGuardAtMajorant` is
  **unconditional**, at the context's own derived widths: `cc-t6x` made it
  conditional on `WidthGateCore` and `cc-t6x-r1` withdrew that, the guard's body
  being gate-free.  Only `familySizeGuardAtBridgeWidths` carries the gate, and
  only because it names the bridge record.  See finding 3 in the `cc-t6x-r1`
  block at the top of this header.
* The Stage-1 reification of `cc-t6x-r1` carries its own five-lemma battery:
  the three `rfl` accessor probes `stage1BindingAt_a` / `_s` / `_q₁`, the
  carrier count `rowsCard_stageOneAt`, and the derived positivity
  `rowsCard_stageOneAt_pos`.  Its canonical inhabitation -- a `ScheduleContext`
  produced by `proc:level-step` -- is the OPEN, REGISTERED `S5-LEVEL-STEP` row,
  and no probe is manufactured for it here.

## Reader counterpart

This module claims **no** reader item, and the reason is the reader's own
content.  The 41-page artifact prints none of the mechanical proof discipline,
the certificate record, the manifest, the constant-fixing searches, the
compiler steps or the static rows.  Its only neighbouring material is:

* `C-effectivity-details.tex:82--84` and `:86--88`, already assigned to
  `EnvelopeRealization`;
* `eq:paper-balanced-family-size` (`C-effectivity-details.tex`, label 41),
  already claimed by `ScheduleMajorantResidue.bBal`, so the log envelope of
  `02:189--194` has no unassigned reader statement left;
* `C-effectivity-details.tex:79--80`, "The parameter compiler in
  `thm:paper-effective-level` produces a finite certificate for each incoming
  envelope exponent `c`", which is prose naming `thm:paper-effective-level` --
  the reader item of `PARAM-001` -- and the reader-counterpart rule forbids
  citing prose as a statement.

Each interval above was opened first-hand this tranche, and a sweep of
`C-effectivity-details.tex` citations across this route's Lean modules
confirmed the two existing assignments.

## Round `r3` audit block (this module only)

Round `r3` of tranche `cc-t6n` works the whole `r2` judged backlog for this
module: the `29` per-declaration `REVISE` entries, in the gate's own six
classes `P2-S1 .. P2-S6`.  The `149` declarations the `r2` gate marked `CLEAR`
keep byte-identical statements except where a type repair forced a change, and
every such change is itemized below.  Nothing outside
`src/EthInapproximability/ParameterizedNP/MechanicalCompilerResidue.lean`, this
module's own block of `tools/AxiomAudit.lean`, this module's single import line
in `src/EthInapproximability.lean`, and its own ledger row was edited.  The
sibling `Section5Admissibility` module is another lane's file and is untouched;
this module no longer imports it.

**`P2-S1` (2 decls) -- prescribed fix.**  `GateRow.TiedTo` now certifies
positivity of the **evaluated** denominator: it takes the interpretation
`val : ℕ → ℚ` of `02:459--462` as an explicit named argument (that interpreter
is GAP-EXPOSED 1, so it is supplied, never axiomatized) and requires
`0 < val d` at each recorded denominator index, in place of the `r2` clause
`0 < nd.coeff`, which certified the node's *integer coefficient* of
`02:458--459` -- a different field of a different display.
`gateRowTiedToIsAConstraint` gains a third component proving the new clause
fires: a row whose recorded denominator evaluates to zero is rejected.

**`P2-S2` (9 decls) -- both prescribed branches taken.**
*(a) The frozen `CoeffPassDerivation` content is now carried and checked.*
`SuccessorRow` gains `rootExpr` (the exact root expression, `02:1043`) and
`tree` (the slot `02:1044--1045` calls the complete checked parent/ledger proof
tree, in the adjacency form of the new `CoeffPassStep`; **`R-8`, `cc-t6x`:**
completeness is named, not delivered), and the new
`SuccessorRow.CoeffPassChecked` performs the frozen rejections of
`02:1045--1046` with three general rejection lemmas.
*(b) The interface is renamed explicitly partial and vacates the source
predicate's slot.*  `LedgerInterfaces` -> `PartialLedgerInterfaces`,
`schemaChecked` -> `partialSchemaScreen`, the three ties renamed to match and a
fourth added for the coefficient pass, `EffLedgerSchema` ->
`EffLedgerPartialSchema` with its four consumers renamed.  The gate's sharpest
observation -- *a `173`-fold junk successor list passes every check the
interface expresses* -- is no longer prose: the new
`partialSchemaScreenAdmitsAConstantSuccessorManifest` proves it in the kernel
at `auditCert`.

**`P2-S3` (3 decls) -- prescribed fix.**  `14:1455` defines `c_eps = c_D + 2`.
The new `cEpsOf` reifies that display; `InputEnvelopePre` takes the cited
adapter's exponent `c_D` (`thm:dinur-adapter`, `14:689--692`) and evaluates
`cEpsOf cD` in conjuncts 3 and 4, and both companions follow.  `c_eps` is no
longer a binder anywhere.

**`P2-S4` (8 decls) -- prescribed fix, first branch.**  `02:799--806` fixes
`m_HS` once and hardwires it, so `T` and `B_s` are single naturals.  The eight
declarations drop their `.{w}` universe binders and read
`HardSeedFacade.mHS.{0}`, the one universe this route's `conv:finite-slots`
carriers inhabit.  Universe invariance of `HSThreshold` is **not** claimed; it
is never needed, because the value is never read at a second universe.

**`P2-S5` (2 decls) -- honest itemized deletion.**  `k2KrefCandidateFeasible`
and `k2J49KrefGe` are deleted.  The repaired schedule the gate prescribes is
another lane's surface, and both rows were in any case duplicate reifications:
`02:855--858` is the banked `ParameterSchedule.kref_j49_candidate`
(`06:615--621`) and `02:858--859` is `.jrefStar_le_j49` (`06:622--624`), both
general in `L_P` and consumed by pin.  With them goes the module's only
occurrence of `L_P` and its only sibling-tranche import.

**`P2-S6` (5 decls) -- prescribed fix, second branch.**
`PreBuilderReturnedScalars` -> `PreBuilderScalarPostconditions`, with
`preBuilderScalarPostconditionsHold`, `...AtBankedWidths` (which `cc-t6x` later
deleted as a renamed duplicate -- see its own note at the declaration site) and
`...RejectEmptyRowCarrier` (which `cc-t6x-r1` replaced by the gate-free
`rowPositivityRejectsEmptyRowCarrier` -- see finding 4);
`preBuilderLegalBuilderInput` keeps its name and
gains a docstring saying which half of `02:1158--1160` it draws.  Every
docstring now states plainly that the declaration represents none of
`clm:eff-ledger-prebuilder`'s hypotheses and none of its "halts and returns"
conclusion.

**Record-only repairs the `r2` gate itemized for this module (six).**  The
binder table's `FREE` ruling on `cEps` (now `DEFINED`, `14:1455`); `B_s = T^2`
cited at `815--818`, corrected to `819`, in both the header and `bsSched`;
`j_0` cited at `825`, corrected to `821`, in both the header and `jZero`; the
first K1 comparison cited at `826--828`, corrected to `821--824`; and the
`GateRow.TiedTo` prose, rewritten to describe what the statement now proves.
Four further citations were re-read at the same time and corrected:
`k1JZeroGe` (`828--829` -> `827--828`, and `816`/`822--823` -> `817`/`819`),
`k1TwoPowJZeroGtSq` (`829--831` -> `828--831`), `k1ScheduledComparisons`
(`822--831` -> `819--831`), `k1HardSeedFloor` (`833--835` -> `832--834`), and
`nineSqLtTwoPow`'s floor citation (`824` -> `821`).

**Forced changes to declarations the `r2` gate had marked `CLEAR`, recorded
loudly rather than silently.**  Three, all forced by a type repair, none
weakening a claim:

1. `Cert` -- its `successor` field type is unchanged in name but `SuccessorRow`
   gained two subfields, so every `Cert` literal changes.  The record's six
   frozen fields and their order are byte-identical.
2. `EffLedgerSchemaHyp` -- its `I` binder changes type from `LedgerInterfaces`
   to `PartialLedgerInterfaces`.  Its five conjuncts and their frozen print
   order are byte-identical.
3. `probeCert`, `auditCert`, `auditCertMeetsExpressibleSchemaClauses` -- their
   *bodies* gain the new `SuccessorRow` subfields (and `auditCert`'s row is
   factored out as the named `auditSuccessorRow`);
   `auditCertMeetsExpressibleSchemaClauses` additionally gains a fourth
   conjunct, the coefficient-pass check, which strengthens rather than weakens
   it.  `probeCertFieldsNonempty`, `probeNodesPhaseSeparated` and
   `probeCertIsNotThePaperCertificate` keep byte-identical statements.

**Declaration count.**  `178` (r2) `- 2` (the two deleted `K2` rows) `+ 9`
(`CoeffPassStep`, `SuccessorRow.CoeffPassChecked`, its three rejection lemmas,
`auditSuccessorRow`, `partialSchemaScreenAdmitsAConstantSuccessorManifest`,
`cEpsOf`, `cEpsOf_eq_and_ge`) `= 185`.

**Registered deferrals this round did not and could not discharge.**  All three
`r2` deferrals stand: (a) the recursive interpreter `val_Xi` of `02:425--444`,
hence `SchemaChecked`/`NumChecked`/`Successor_16` and the canonical `Compile(c)`
inhabitant of `Cert`; (b) the immutable certificate registry of
`app:certificate-registry`, hence the registry-order equality; (c) the
hypotheses and halting conclusion of `clm:eff-ledger-prebuilder`.  A fourth is
added by this round's own repair: (d) the `CoeffPassDerivation` **evaluator**,
since `SuccessorRow.CoeffPassChecked` checks stored data and does not compute
`C_u` from the expression.  Each is recorded in the ledger row
`MECHANICAL-COMPILER-RESIDUE-001`; none is silently satisfied by a probe.

-/

namespace EthInapproximability.ParameterizedNP.MechanicalCompilerResidue

open EthInapproximability.ParameterizedNP

/-! ## Section 1  The closed alphabets of `def:effective-schedule-certificate`

`02:210--220` fixes four sorts and their value sets; `02:456--461` fixes the
node fields and the phase tag; `02:463--484` fixes the gate atom tags and the
three disjoint evidence tags; `02:500--505` fixes the four coverage pointers.
Each of these alphabets is printed *exhaustively* in the frozen source, so each
is transcribed as a closed inductive with its roster. -/

/-- **The four core sorts** -- `02:210--213`,
"Each symbol has one of the sorts `Nat`, `PosNat`, `Int`, `Rat`", in the
frozen print order. -/
inductive CoreSort where
  /-- `Nat`. -/
  | natS
  /-- `PosNat`. -/
  | posS
  /-- `Int`. -/
  | intS
  /-- `Rat`. -/
  | ratS
  deriving DecidableEq, Repr

/-- **The value set `V_sigma`** -- `02:218--220`, "write `V_sigma` for,
respectively, `N`, `N_{>0}`, `Z`, `Q`".  `PosNat` is a genuinely different
carrier from `Nat`; `coreSortPosIsPositive` records that it is not a
decoration. -/
def CoreSort.carrier : CoreSort → Type
  | CoreSort.natS => ℕ
  | CoreSort.posS => {n : ℕ // 0 < n}
  | CoreSort.intS => ℤ
  | CoreSort.ratS => ℚ

/-- The sort roster in the frozen print order of `02:210--213`. -/
def coreSorts : List CoreSort :=
  [CoreSort.natS, CoreSort.posS, CoreSort.intS, CoreSort.ratS]

/-- **Aux C1 (the sort roster is the complete frozen list).**  Four entries, no
repetition, and every sort occurs.  General. -/
theorem coreSortsIsTheCompleteRoster :
    coreSorts.length = 4 ∧ coreSorts.Nodup ∧ ∀ s : CoreSort, s ∈ coreSorts := by
  refine ⟨rfl, by decide, ?_⟩
  intro s; cases s <;> decide

/-- **Aux C2 (`PosNat` is not `Nat`).**  Every inhabitant of the `PosNat`
carrier is positive, so the second sort is a real restriction and the
`asPos(-, h_{>0})` cast of `02:382` has content.  General. -/
theorem coreSortPosIsPositive (x : CoreSort.posS.carrier) : 0 < x.val := x.2

/-- **The phase tag** -- `02:459--460`, "a phase tag in `{pre, post}`", with
the assignment rule at `02:783--796`. -/
inductive Phase where
  /-- `pre`: the dependency closure mentions only `n`, `Public`, `K_*`, the
  scalar accessors through `q_2, t_2, eps_2`, and `M_1` (`02:786--789`). -/
  | pre
  /-- `post`: everything else (`02:789`). -/
  | post
  deriving DecidableEq, Repr

/-- **The parent join** -- `02:783--784`, "a row inherits the maximum phase of
its parent nodes", and C2 at `02:929--930`, "Give each derived node the maximum
phase of its parents". -/
def Phase.join : Phase → Phase → Phase
  | Phase.post, _ => Phase.post
  | _, Phase.post => Phase.post
  | Phase.pre, Phase.pre => Phase.pre

/-- The maximum phase of an ordered parent list, `pre` on the empty list. -/
def Phase.maxOf (l : List Phase) : Phase := l.foldr Phase.join Phase.pre

/-- **Aux P1 (`pre` is the join identity).**  A parent list of `pre` nodes
never promotes its child.  General. -/
theorem Phase.joinPreLeft (p : Phase) : Phase.join Phase.pre p = p := by
  cases p <;> rfl

/-- **Aux P2 (the join is commutative).**  The frozen rule is a maximum, so it
does not depend on the order in which the parents are visited.  General. -/
theorem Phase.joinComm (p q : Phase) : Phase.join p q = Phase.join q p := by
  cases p <;> cases q <;> rfl

/-- **Aux P3 (`post` absorbs).**  A single `post` parent promotes the child
whatever the other parents are, which is the "maximum" of `02:783--784`.
General. -/
theorem Phase.joinPostLeft (p : Phase) : Phase.join Phase.post p = Phase.post := rfl

/-- **Aux P4 (a leaf row is `pre`).**  `Phase.maxOf [] = pre`.  General. -/
theorem Phase.maxOfNil : Phase.maxOf ([] : List Phase) = Phase.pre := rfl

/-- **Aux P5 (the maximum is `post` exactly when a parent is).**  This is the
whole content of `02:783--784` made checkable, and it is what makes the
`pre` slice dependency closed below.  General in the parent list. -/
theorem Phase.maxOfEqPostIff (l : List Phase) :
    Phase.maxOf l = Phase.post ↔ Phase.post ∈ l := by
  induction l with
  | nil => simp [Phase.maxOf]
  | cons a l ih =>
      cases a with
      | pre =>
          simp only [Phase.maxOf, List.foldr_cons] at *
          rw [Phase.joinPreLeft]
          simp [ih]
      | post =>
          simp only [Phase.maxOf, List.foldr_cons, Phase.joinPostLeft]
          simp

/-- **The gate atom tags** -- `02:465--468`, "Its atom tag is one of `Eq`,
`Le`, `Lt`, `Divides`", in the frozen print order.  `02:463--464` restricts
`NumGates_c` to "decidable atoms over exact integers and rationals". -/
inductive AtomTag where
  /-- `Eq`. -/
  | eqA
  /-- `Le`. -/
  | leA
  /-- `Lt`. -/
  | ltA
  /-- `Divides`. -/
  | dividesA
  deriving DecidableEq, Repr

/-- The exact integer semantics of an atom tag (`02:463--468`). -/
def AtomTag.holds : AtomTag → ℤ → ℤ → Prop
  | AtomTag.eqA, a, b => a = b
  | AtomTag.leA, a, b => a ≤ b
  | AtomTag.ltA, a, b => a < b
  | AtomTag.dividesA, a, b => a ∣ b

/-- The atom-tag roster in the frozen print order of `02:465--468`. -/
def atomTags : List AtomTag :=
  [AtomTag.eqA, AtomTag.leA, AtomTag.ltA, AtomTag.dividesA]

/-- **Aux A1 (the atom roster is the complete frozen list).**  General. -/
theorem atomTagsIsTheCompleteRoster :
    atomTags.length = 4 ∧ atomTags.Nodup ∧ ∀ t : AtomTag, t ∈ atomTags := by
  refine ⟨rfl, by decide, ?_⟩
  intro t; cases t <;> decide

/-- **Aux A2 (`Eq` refines `Le`).**  A row compiled to the equality atom is
never weaker than the same row compiled to the comparison atom, which is what
lets C3 (`02:940--944`) compile a divisibility "as the exact equation `b = ak`"
without loss.  General. -/
theorem atomTagEqImpliesLe {a b : ℤ} (h : AtomTag.eqA.holds a b) :
    AtomTag.leA.holds a b := le_of_eq h

/-- **The three persistence classes** -- `02:478`,
"`Cutoff(u, ECut/PCut/DCut)`", with their persistence proofs at
`02:1302--1314`.  `02:1014` records that "No tail class uses `DCut`". -/
inductive CutKind where
  /-- `ECut`. -/
  | ecut
  /-- `PCut`; the only class the successor rows use (`02:1026--1035`). -/
  | pcut
  /-- `DCut`. -/
  | dcut
  deriving DecidableEq, Repr

/-- The persistence-class roster in the frozen print order of `02:478`. -/
def cutKinds : List CutKind := [CutKind.ecut, CutKind.pcut, CutKind.dcut]

/-- **Aux K1 (the persistence roster is the complete frozen list).**
General. -/
theorem cutKindsIsTheCompleteRoster :
    cutKinds.length = 3 ∧ cutKinds.Nodup ∧ ∀ k : CutKind, k ∈ cutKinds := by
  refine ⟨rfl, by decide, ?_⟩
  intro k; cases k <;> decide

/-- **The four tail classes** -- `eq:four-tail-errors`,
`06-parameter-schedule.tex:1712--1717` (the display `\label`led at `06:1717`
inside `sec:effective-cutoff`), which is exactly what `02:475--476` points at:
"tail classes `e_r` from the four classes in `\Cref{sec:effective-cutoff}`".
The four adverse-term majorants are printed in the frozen order

```
W(L)/q_2,   2^{C_size L^8 - b_T},   2^{C_size A_*^2 - b_1},   2^{C_exc L_P^2}/q.
```

`06:1719--1724` fixes the reading: "The first controls source-width and
ordinary ceiling losses.  The second controls every `x_T` loss, the third every
`2^{-b_1}` loss, and the fourth every reference-routing and exceptional
terminal loss", and it explicitly rules out a fifth class ("The fixed estimates
`eps_2 <= 1/100` and `eps_prod < 1/50` ... do not form a fifth asymptotic
error").

This is a **typed** class index, not a natural number: `02:475--476` restricts
`e_r` to the four registered classes, and a bare `ℕ` index admitted a fifth. -/
inductive TailClass where
  /-- `W(L)/q_2` -- "source-width and ordinary ceiling losses"
  (`06:1713`, `06:1719--1720`). -/
  | sourceWidth
  /-- `2^{C_size L^8 - b_T}` -- "every `x_T` loss" (`06:1714`, `06:1720`). -/
  | sizeDepth
  /-- `2^{C_size A_*^2 - b_1}` -- "every `2^{-b_1}` loss"
  (`06:1715`, `06:1720--1721`). -/
  | seedDepth
  /-- `2^{C_exc L_P^2}/q` -- "every reference-routing and exceptional terminal
  loss" (`06:1716`, `06:1721--1722`). -/
  | exceptionalRouting
  deriving DecidableEq, Repr

/-- The tail-class roster in the frozen print order of `06:1713--1716`. -/
def tailClasses : List TailClass :=
  [TailClass.sourceWidth, TailClass.sizeDepth, TailClass.seedDepth,
    TailClass.exceptionalRouting]

/-- **Aux T1 (the tail-class roster is the complete frozen list).**  Exactly
four entries, no repetition, every class present -- which is what
`02:475--476` ("the four classes") and `06:1722--1724` ("do not form a fifth
asymptotic error") jointly require.  General. -/
theorem tailClassesIsTheCompleteRoster :
    tailClasses.length = 4 ∧ tailClasses.Nodup ∧ ∀ e : TailClass, e ∈ tailClasses := by
  refine ⟨rfl, by decide, ?_⟩
  intro e; cases e <;> decide

/-- **Aux T2 (the four classes are pairwise distinct).**  `06:1719--1722`
assigns each class a different loss family, so the four-element roster is not
four names for one class.  General. -/
theorem tailClassesPairwiseDistinct :
    TailClass.sourceWidth ≠ TailClass.sizeDepth ∧
      TailClass.sourceWidth ≠ TailClass.seedDepth ∧
      TailClass.sourceWidth ≠ TailClass.exceptionalRouting ∧
      TailClass.sizeDepth ≠ TailClass.seedDepth ∧
      TailClass.sizeDepth ≠ TailClass.exceptionalRouting ∧
      TailClass.seedDepth ≠ TailClass.exceptionalRouting := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Aux T3 (there is no fifth class).**  Any tail class the roster does not
already list is equal to one of the four, so `06:1722--1724`'s "do not form a
fifth asymptotic error" is a kernel fact about the type rather than a comment.
General. -/
theorem tailClassHasNoFifthMember (e : TailClass) :
    e = TailClass.sourceWidth ∨ e = TailClass.sizeDepth ∨
      e = TailClass.seedDepth ∨ e = TailClass.exceptionalRouting := by
  cases e
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- **The three disjoint evidence tags** -- `02:470--483`, "Each row contains
its manuscript label, parent nodes, and one of three disjoint evidence tags". -/
inductive Evidence where
  /-- `Exact`: "checked directly and has no asymptotic-error fields"
  (`02:471--472`). -/
  | exactE
  /-- `TailBundle(sigma; [(u_r, m_r, e_r)]_{r<k})`: "a positive rational slack
  `sigma` and a nonempty ordered list of distinct auxiliary tail IDs `u_r`,
  positive multipliers `m_r`, and tail classes `e_r` from the four classes in
  `\Cref{sec:effective-cutoff}`" (`02:473--477`).  The tail class is the
  **typed** `TailClass` of `06:1712--1717`, so "from the four classes" is a
  typing constraint and not a side condition that could be forgotten;
  `02:476--477` ("Different terms of one target may have different classes") is
  why the class sits inside the term and not on the bundle.  **No**
  coefficient-derivation record and **no** registry-shape predicate is carried
  (GAP-EXPOSED 2). -/
  | tailBundle (sigma : ℚ) (terms : List (ℕ × ℕ × TailClass))
  /-- `Cutoff(u, ECut/PCut/DCut)`: "points to an earlier auxiliary comparison
  and its persistent search record" (`02:478--479`). -/
  | cutoffE (u : ℕ) (kind : CutKind)
  deriving DecidableEq, Repr

/-- The ordered tail-term list of an evidence tag; empty on the two
non-tail tags, which is `02:471--472`'s "no asymptotic-error fields". -/
def Evidence.tailTerms : Evidence → List (ℕ × ℕ × TailClass)
  | Evidence.exactE => []
  | Evidence.tailBundle _ ts => ts
  | Evidence.cutoffE _ _ => []

/-- The frozen well-formedness of an evidence tag: `02:473--477`'s positive
slack, nonempty list, distinct auxiliary IDs and positive multipliers.  The
fourth frozen restriction, "tail classes `e_r` from the four classes", is
carried by the `TailClass` type of the third component and therefore needs no
clause here; `tailBundleClassesAreRegistered` records that it holds.  The two
non-tail tags carry no such obligation. -/
def Evidence.WellFormed : Evidence → Prop
  | Evidence.exactE => True
  | Evidence.tailBundle sigma ts =>
      0 < sigma ∧ ts ≠ [] ∧ (ts.map Prod.fst).Nodup ∧ ∀ x ∈ ts, 0 < x.2.1
  | Evidence.cutoffE _ _ => True

/-- **Aux E0 (every stored tail class is one of the four registered classes).**
`02:475--476`.  With the typed third component this is a kernel fact about
*every* bundle rather than a clause a checker could omit, which is exactly the
strengthening the untyped `ℕ` index could not express.  General. -/
theorem tailBundleClassesAreRegistered (ev : Evidence) :
    ∀ x ∈ ev.tailTerms, x.2.2 ∈ tailClasses := by
  intro x _
  exact (tailClassesIsTheCompleteRoster.2.2) x.2.2

/-- **Aux E1 (the three tags really are disjoint).**  `02:470` calls them
"three disjoint evidence tags"; here that is a kernel fact rather than a
naming convention.  General. -/
theorem evidenceTagsPairwiseDistinct (sigma : ℚ) (ts : List (ℕ × ℕ × TailClass))
    (u : ℕ) (k : CutKind) :
    Evidence.exactE ≠ Evidence.tailBundle sigma ts ∧
      Evidence.exactE ≠ Evidence.cutoffE u k ∧
      Evidence.tailBundle sigma ts ≠ Evidence.cutoffE u k :=
  ⟨by simp, by simp, by simp⟩

/-- **Aux E2 (`Exact` carries no tail error).**  `02:471--472` and `02:975`,
"Exact and cutoff-pending rows do not enter the tail-error sum".  General. -/
theorem exactHasNoTailTerms :
    Evidence.exactE.tailTerms = [] ∧ ∀ u k, (Evidence.cutoffE u k).tailTerms = [] :=
  ⟨rfl, fun _ _ => rfl⟩

/-- **Aux E3 (the tail well-formedness is exactly the frozen four clauses).**
General. -/
theorem wellFormedTailBundleIff (sigma : ℚ) (ts : List (ℕ × ℕ × TailClass)) :
    (Evidence.tailBundle sigma ts).WellFormed ↔
      (0 < sigma ∧ ts ≠ [] ∧ (ts.map Prod.fst).Nodup ∧ ∀ x ∈ ts, 0 < x.2.1) :=
  Iff.rfl

/-- **Statement pole for `Evidence` (`02:474`, "a nonempty ordered list").**
The empty bundle is rejected, so the nonemptiness clause is not a decoration:
without it every target could be marked `TailBundle` with no tail at all.
**BEYOND-PAPER AUDIT** at `sigma = 1`: a rejection probe claiming no legality,
exhibited only to show that the guard fires. -/
theorem wellFormedRejectsEmptyBundle :
    ¬ (Evidence.tailBundle 1 []).WellFormed := by
  simp [Evidence.WellFormed]

/-- **The four immutable manifest row tags** -- `02:714--719` (`type`,
`assumption`) and `02:766` ("Every remaining row is tagged `numerical` or
`static`"). -/
inductive RowTag where
  /-- A `type` row: a record, function, carrier or accessor equation
  (`02:714--717`). -/
  | typeRow
  /-- An `assumption` row: one of the four classes of `02:720--738`. -/
  | assumptionRow
  /-- A `numerical` row (`02:766`). -/
  | numericalRow
  /-- A `static` row (`02:766`). -/
  | staticRow
  deriving DecidableEq, Repr

/-- The row-tag roster in the frozen print order. -/
def rowTags : List RowTag :=
  [RowTag.typeRow, RowTag.assumptionRow, RowTag.numericalRow, RowTag.staticRow]

/-- **Aux R1 (the row-tag roster is the complete frozen list).**  General. -/
theorem rowTagsIsTheCompleteRoster :
    rowTags.length = 4 ∧ rowTags.Nodup ∧ ∀ t : RowTag, t ∈ rowTags := by
  refine ⟨rfl, by decide, ?_⟩
  intro t; cases t <;> decide

/-- **The four coverage pointers** -- `02:500--505`,
"Every pointer in `Coverage_c` has exactly one of four constructors:
`ByNum(r)`, `ByStatic(r)`, `ByType(r)`, `ByAssumption(r)`", in the frozen print
order. -/
inductive Pointer where
  /-- `ByNum(r)`, pointing at a numerical gate (`02:963`). -/
  | byNum (r : ℕ)
  /-- `ByStatic(r)`, pointing at a static row (`02:963--964`). -/
  | byStatic (r : ℕ)
  /-- `ByType(r)`; `02:506--507` restricts it to "a named member of
  `TypeFacts(Xi)`". -/
  | byType (r : ℕ)
  /-- `ByAssumption(r)`; `02:507--509` restricts it to "the explicitly
  displayed source-size, incoming-envelope, or balanced-family hypotheses". -/
  | byAssumption (r : ℕ)
  deriving DecidableEq, Repr

/-- The row index a pointer names. -/
def Pointer.row : Pointer → ℕ
  | Pointer.byNum r => r
  | Pointer.byStatic r => r
  | Pointer.byType r => r
  | Pointer.byAssumption r => r

/-- The manifest row tag a pointer is permitted to cite -- C4, `02:961--967`:
"Type rows point only to the matching named member of `TypeFacts(Xi)`;
assumption rows point only to one of the four assumption classes listed above;
exact rows point to their numerical gate; and analytic rows point to their
static row." -/
def Pointer.sourceTag : Pointer → RowTag
  | Pointer.byNum _ => RowTag.numericalRow
  | Pointer.byStatic _ => RowTag.staticRow
  | Pointer.byType _ => RowTag.typeRow
  | Pointer.byAssumption _ => RowTag.assumptionRow

/-- **Aux Pt1 (every row tag has its pointer).**  The four constructors cover
the four immutable tags, so no manifest row is left without a legal pointer
kind.  General. -/
theorem pointerSourceTagSurjective (t : RowTag) : ∃ p : Pointer, p.sourceTag = t := by
  cases t
  · exact ⟨Pointer.byType 0, rfl⟩
  · exact ⟨Pointer.byAssumption 0, rfl⟩
  · exact ⟨Pointer.byNum 0, rfl⟩
  · exact ⟨Pointer.byStatic 0, rfl⟩

/-- **Statement pole for `Pointer` (C4, `02:966--967`, "Reject any attempted
pointer with a different source tag").**  The tag map separates the four
constructors, so a pointer cannot be re-tagged: this is what makes the
rejection in C4 have content.  General in the row indices. -/
theorem pointerTagSeparatesConstructors (r s : ℕ) :
    (Pointer.byNum r).sourceTag ≠ (Pointer.byStatic s).sourceTag ∧
      (Pointer.byNum r).sourceTag ≠ (Pointer.byType s).sourceTag ∧
      (Pointer.byNum r).sourceTag ≠ (Pointer.byAssumption s).sourceTag ∧
      (Pointer.byStatic r).sourceTag ≠ (Pointer.byType s).sourceTag ∧
      (Pointer.byStatic r).sourceTag ≠ (Pointer.byAssumption s).sourceTag ∧
      (Pointer.byType r).sourceTag ≠ (Pointer.byAssumption s).sourceTag := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Pointer.sourceTag]

/-- **The four assumption classes** -- `02:720--738`, items (i)--(iv), in the
frozen print order.  `02:509` restricts `ByAssumption` to exactly these. -/
inductive AssumptionClass where
  /-- (i) the source clauses `n >= 1`, `n <= N_E`,
  `N_V, N_E <= n(log_2(n+2))^{c_eps}`, `Delta = Delta_eps`,
  `gamma = gamma_eps` (`02:721--727`). -/
  | sourceClauses
  /-- (ii) the incoming-envelope block (`02:728--734`). -/
  | incomingEnvelope
  /-- (iii) the displayed indexed-balancedness hypothesis (`02:735`). -/
  | indexedBalancedness
  /-- (iv) `0 < N_2 <= B_bal(q_2, t_2, |Rows(M_1)|)` (`02:736--737`). -/
  | familyBound
  deriving DecidableEq, Repr

/-- The assumption-class roster in the frozen print order of `02:720--738`. -/
def assumptionClasses : List AssumptionClass :=
  [AssumptionClass.sourceClauses, AssumptionClass.incomingEnvelope,
    AssumptionClass.indexedBalancedness, AssumptionClass.familyBound]

/-- **Aux As1 (the assumption roster is the complete frozen list).**  Exactly
four classes, which is what `02:509` and C4 (`02:963`) rely on.  General. -/
theorem assumptionClassesIsTheCompleteRoster :
    assumptionClasses.length = 4 ∧ assumptionClasses.Nodup ∧
      ∀ a : AssumptionClass, a ∈ assumptionClasses := by
  refine ⟨rfl, by decide, ?_⟩
  intro a; cases a <;> decide

/-! ## Section 2  The six-field certificate record

`02:446--453`:
`Cert_c = (Nodes_c, NumGates_c, Searches_c, Static_c, Coverage_c, Successor_c)`,
"the finite, deterministically ordered record".  The six fields are transcribed
in the frozen order, and each row type carries **every** subfield the frozen
enumeration `02:454--524` prints.  What remains unbuilt on this route is the
recursive *interpreter* `eval_Xi` / `val_Xi` of `02:425--444` -- a function, not
a field -- which is GAP-EXPOSED 1. -/

/-- **The typed leaf of a core scalar expression** -- `02:224`,
`e_sigma ::= Lit_sigma(v) | Ref_sigma(a)`.  A node is a leaf exactly when it
carries one of these two; every other production of `(Op)` has parents. -/
inductive NodeLeaf where
  /-- `Lit_sigma(v)`: a literal of the declared sort, stored by its canonical
  code (`02:224`). -/
  | lit (sort : CoreSort) (code : ℕ)
  /-- `Ref_sigma(a)`: a primitive symbol reference at the declared sort
  (`02:224`); `02:348--349` makes the identifier family-qualified, so the
  reference is the registry atom ID. -/
  | ref (sort : CoreSort) (atomId : ℕ)
  deriving DecidableEq, Repr

/-- **The typed operation alphabet `(Op)`--`(SearchOp)`** -- the two frozen
grammar displays `02:222--271` (tagged `(Op)` at `02:270`) and `02:327--332`
(tagged `(SearchOp)` at `02:331`), transcribed exhaustively in the frozen print
order, family by family.

`02:272--274` fixes the argument conventions ("`*` means a length-prefixed
finite list, `+` a nonempty such list, `F` a previously encoded finite carrier,
`P` an encoded decidable predicate"); those are properties of a node's parent
list, not extra constructors, so the alphabet below has exactly one constructor
per printed production. -/
inductive NodeOp where
  /-- `Lit_sigma(v)` (`02:224`). -/
  | lit
  /-- `Ref_sigma(a)` (`02:224`). -/
  | ref
  /-- `asPos(e_Nat, h_{>0})` (`02:226`). -/
  | asPos
  /-- `powTwo(e_Nat)` (`02:227`). -/
  | powTwo
  /-- `leastPowTwoN(e_Nat, h)` (`02:228`); also a `(SearchOp)` at `02:330`. -/
  | leastPowTwoN
  /-- `leastPowTwoQ(e_Rat, h_{>=0}, h)` (`02:229`); also `(SearchOp)`. -/
  | leastPowTwoQ
  /-- `posToNat(e_PosNat)` (`02:231`). -/
  | posToNat
  /-- `addN(e_Nat^*)` (`02:232`). -/
  | addN
  /-- `mulN(e_Nat^*)` (`02:233`). -/
  | mulN
  /-- `subN(e_Nat, e_Nat)` (`02:234`), the frozen `max{x-y,0}` of `02:280`. -/
  | subN
  /-- `exactDivN(e_Nat, e_PosNat, h_|)` (`02:235`). -/
  | exactDivN
  /-- `minN(e_Nat^+)` (`02:236`). -/
  | minN
  /-- `maxN(e_Nat^+)` (`02:237`). -/
  | maxN
  /-- `powN(e_Nat, e_Nat)` (`02:238`). -/
  | powN
  /-- `exactLog2(e_PosNat, h_{2^.})` (`02:239`). -/
  | exactLog2
  /-- `clog2N(e_Nat)` (`02:240`). -/
  | clog2N
  /-- `clog2Q(e_Rat, h_{>=0})` (`02:241`). -/
  | clog2Q
  /-- `ceilQ(e_Rat, h_{>=0})` (`02:242`). -/
  | ceilQ
  /-- `bl(e_Nat)` (`02:243`), the binary length of `02:279--283`. -/
  | bl
  /-- `absNum(e_Rat)` (`02:244`). -/
  | absNum
  /-- `den(e_Rat)` (`02:245`). -/
  | den
  /-- `card(F)` (`02:246`). -/
  | card
  /-- `count(F, P)` (`02:247`). -/
  | count
  /-- `natToInt(e_Nat)` (`02:249`). -/
  | natToInt
  /-- `num(e_Rat)` (`02:250`). -/
  | num
  /-- `negI(e_Int)` (`02:251`). -/
  | negI
  /-- `addI(e_Int^*)` (`02:252`). -/
  | addI
  /-- `mulI(e_Int^*)` (`02:253`). -/
  | mulI
  /-- `subI(e_Int, e_Int)` (`02:254`). -/
  | subI
  /-- `natToRat(e_Nat)` (`02:256`). -/
  | natToRat
  /-- `intToRat(e_Int)` (`02:257`). -/
  | intToRat
  /-- `rat(p, q, h_q)` (`02:258`). -/
  | ratMk
  /-- `addQ(e_Rat^*)` (`02:259`). -/
  | addQ
  /-- `mulQ(e_Rat^*)` (`02:260`). -/
  | mulQ
  /-- `subQ(e_Rat, e_Rat)` (`02:261`). -/
  | subQ
  /-- `minQ(e_Rat^+)` (`02:262`). -/
  | minQ
  /-- `maxQ(e_Rat^+)` (`02:263`). -/
  | maxQ
  /-- `negQ(e_Rat)` (`02:264`). -/
  | negQ
  /-- `halfQ(e_Rat)` (`02:265`). -/
  | halfQ
  /-- `divQ(e_Rat, e_Rat, h_{/=0})` (`02:266`). -/
  | divQ
  /-- `powQN(e_Rat, e_Nat)` (`02:267`). -/
  | powQN
  /-- `powQZ(e_Rat, e_Int, h^-_{/=0})` (`02:268`). -/
  | powQZ
  /-- `leastNat(x, P, h_exists)` (`02:328`), "returns the least natural
  satisfying `P`" (`02:333--334`). -/
  | leastNat
  /-- `greatestNat(x, P, b, h_bd, h_exists)` (`02:329`), whose "proof field
  supplies a tested bound `b` with `P(r)` false for `r > b`, as well as a
  satisfying witness" (`02:334--336`). -/
  | greatestNat
  deriving DecidableEq, Repr

/-- The operation alphabet in the frozen print order of `02:224--268` followed
by the two search instructions of `02:328--329`.  The two power-of-two searches
appear once, at their `(Op)` position `02:228--229`, because `02:330` reprints
the *same* two instructions in `(SearchOp)`. -/
def nodeOps : List NodeOp :=
  [NodeOp.lit, NodeOp.ref,
    NodeOp.asPos, NodeOp.powTwo, NodeOp.leastPowTwoN, NodeOp.leastPowTwoQ,
    NodeOp.posToNat, NodeOp.addN, NodeOp.mulN, NodeOp.subN, NodeOp.exactDivN,
    NodeOp.minN, NodeOp.maxN, NodeOp.powN, NodeOp.exactLog2, NodeOp.clog2N,
    NodeOp.clog2Q, NodeOp.ceilQ, NodeOp.bl, NodeOp.absNum, NodeOp.den,
    NodeOp.card, NodeOp.count,
    NodeOp.natToInt, NodeOp.num, NodeOp.negI, NodeOp.addI, NodeOp.mulI,
    NodeOp.subI,
    NodeOp.natToRat, NodeOp.intToRat, NodeOp.ratMk, NodeOp.addQ, NodeOp.mulQ,
    NodeOp.subQ, NodeOp.minQ, NodeOp.maxQ, NodeOp.negQ, NodeOp.halfQ,
    NodeOp.divQ, NodeOp.powQN, NodeOp.powQZ,
    NodeOp.leastNat, NodeOp.greatestNat]

/-- **Aux Op1 (the operation alphabet is the complete frozen list).**  The two
frozen grammar displays print `2 + 4 + 17 + 6 + 13` productions and two further
search instructions, so the closed alphabet has `44` entries, no repetition,
and every operation occurs.  General. -/
theorem nodeOpsIsTheCompleteRoster :
    nodeOps.length = 44 ∧ nodeOps.Nodup ∧ ∀ o : NodeOp, o ∈ nodeOps := by
  refine ⟨rfl, by decide, ?_⟩
  intro o; cases o <;> decide

/-- **Aux Op2 (the two leaf productions are exactly `Lit` and `Ref`).**
`02:224` is the only line of the grammar without a recursive argument, so
"literal or primitive-symbol leaf" identifies precisely two operations.
General. -/
def NodeOp.IsLeafOp : NodeOp → Prop
  | NodeOp.lit => True
  | NodeOp.ref => True
  | _ => False

/-- **Aux Op3 (leafhood is decidable and hits exactly two operations).**
General. -/
theorem nodeOpLeafOpsAreTheTwoOfLine224 :
    (nodeOps.filter (fun o => decide (o = NodeOp.lit ∨ o = NodeOp.ref))).length = 2 := by
  decide

/-- **The three elaboration obligations** -- `02:389--393`: "The certificate
stores, for every mixed-family atom, its expected sort and the ordered list of
`CheckedPositive`, `CheckedDenominator`, and `CheckedDivides` obligations
created by this lowering.  The schema checker reconstructs that list from the
surface AST and rejects an omitted, extra, or failed check." -/
inductive ElabObligation where
  /-- `CheckedPositive`, the `h_{>0}` program of `02:382--384`. -/
  | checkedPositive
  /-- `CheckedDenominator`, the positive-denominator record of `02:367--369`
  and `02:469--470`. -/
  | checkedDenominator
  /-- `CheckedDivides`, the checked-divisibility program of `02:361--362`. -/
  | checkedDivides
  deriving DecidableEq, Repr

/-- The obligation roster in the frozen print order of `02:390--391`. -/
def elabObligations : List ElabObligation :=
  [ElabObligation.checkedPositive, ElabObligation.checkedDenominator,
    ElabObligation.checkedDivides]

/-- **Aux El1 (the obligation roster is the complete frozen list).**  General. -/
theorem elabObligationsIsTheCompleteRoster :
    elabObligations.length = 3 ∧ elabObligations.Nodup ∧
      ∀ e : ElabObligation, e ∈ elabObligations := by
  refine ⟨rfl, by decide, ?_⟩
  intro e; cases e <;> decide

/-- **A row of `Nodes_c`** -- `02:454--461`, with **all nine** printed
subfields: "Each node records its sort, name, literal or primitive-symbol leaf,
typed operation from `(Op)`--`(SearchOp)`, ordered parent nodes, its
expected-sort elaboration obligations, integer coefficient, binary-length
degree, and a phase tag in `{pre, post}`", in that frozen order.

What is **not** landed here is the recursive interpretation
`sembracket{u}_Xi` of `02:460--462` -- a function on this record, not a field of
it; it needs `val_Xi` and `LevelStep(Public, Pi)` (`02:425--444`), which are
GAP-EXPOSED 1.  No predicate in this module evaluates a node. -/
structure NodeRow where
  /-- The declared sort of the node (`02:456`). -/
  coreSort : CoreSort
  /-- The node's name (`02:456`); `02:348--349` makes it family-qualified, so
  it is the literal registry identifier. -/
  name : String
  /-- The literal or primitive-symbol leaf (`02:456`), absent on a derived
  node.  `nodeRowLeafIffLeafOp` ties this to the operation. -/
  leaf : Option NodeLeaf
  /-- The typed operation from `(Op)`--`(SearchOp)` (`02:456--457`). -/
  op : NodeOp
  /-- The ordered parent node indices (`02:457--458`). -/
  parents : List ℕ
  /-- The expected sort of `02:389--390`, which selects the overload
  (`02:350--353`). -/
  expectedSort : CoreSort
  /-- The ordered elaboration-obligation list of `02:390--392`. -/
  elabObligations : List ElabObligation
  /-- The integer coefficient (`02:458--459`). -/
  coeff : ℕ
  /-- The binary-length degree (`02:459`). -/
  blDegree : ℕ
  /-- The phase tag (`02:459--460`). -/
  phase : Phase
  deriving DecidableEq, Repr

/-- **The leaf/operation agreement of `02:224` and `02:456`.**  A node stores a
leaf exactly when its operation is one of the two leaf productions.  This is
the syntactic half of `02:462`, "ill-sorted operations are rejected", that is
expressible without the interpreter. -/
def NodeRow.LeafConsistent (nd : NodeRow) : Prop :=
  nd.leaf.isSome ↔ (nd.op = NodeOp.lit ∨ nd.op = NodeOp.ref)

/-- **Aux N1 (leaf consistency is decidable, and it separates the two
families).**  A derived node with a stored leaf, or a `Lit`/`Ref` node without
one, is rejected -- so the leaf field is not decoration.  General. -/
theorem nodeRowLeafIffLeafOp (nd : NodeRow) :
    nd.LeafConsistent ↔ (nd.leaf.isSome ↔ (nd.op = NodeOp.lit ∨ nd.op = NodeOp.ref)) :=
  Iff.rfl

/-- **A row of `NumGates_c`** -- `02:463--484`: its manuscript label, its atom
tag, its parent nodes, its certified-positive denominator records, and one of
the three disjoint evidence tags.  `02:469--470`: "a rational atom also records
certified-positive denominators before it is cross-multiplied".
`02:483--484`: "No row contains a communication-complexity, robustness, `YES`,
or `NO` proposition" -- accordingly this record has no such field. -/
structure GateRow where
  /-- The manuscript label, as its registry index (`02:470`). -/
  label : ℕ
  /-- The atom tag (`02:464--468`). -/
  tag : AtomTag
  /-- The parent nodes (`02:470`). -/
  parents : List ℕ
  /-- The certified-positive denominator records a rational atom stores before
  cross-multiplication (`02:469--470`), as the node indices carrying them. -/
  denominators : List ℕ
  /-- The evidence tag (`02:470--483`). -/
  evidence : Evidence
  deriving DecidableEq, Repr

/-- **The gate row is tied to the typed node graph and to the evaluated
denominators** -- `02:470` (the parent nodes) together with `02:527--528`
("every pointer is in range and of the advertised kind ... every expression
parent ... must be topologically earlier") and `02:469--470`, "a rational atom
also records certified-positive denominators before it is cross-multiplied".

The third clause is the frozen certification, read where the frozen text reads
it: at the **value of the denominator expression**, not at any stored field.
`02:541--544` is explicit that this evaluation is `NumChecked`, "recursive exact
integer and rational evaluation under `val_Xi`", so the interpretation
`sembracket{u}_Xi` of `02:459--462` is what has to be positive.  That
interpreter is unbuilt on this route (GAP-EXPOSED 1), so it is supplied as an
**explicit named argument** `val` -- the same discipline the route uses for
every cited-but-unformalized interface, and never a silent axiom.

The `r2` form of this predicate instead required `0 < nd.coeff` at the node the
denominator index names.  `02:458--459` makes `coeff` the node's *integer
coefficient*, a different field of a different display from the denominator
value of `02:469`; that clause certified the wrong quantity and is replaced.

The *manuscript label* is deliberately **not** constrained here.  `02:530--532`
ties it to "the immutable registry of `\Cref{app:certificate-registry}` in
exactly its canonical order", and that registry table is not transcribed on this
route (GAP-EXPOSED 2); binding its size as a free natural would put a
source-defined quantity in a binder, which is why the clause is omitted rather
than approximated. -/
def GateRow.TiedTo (g : GateRow) (ns : List NodeRow) (val : ℕ → ℚ) : Prop :=
  (∀ j ∈ g.parents, j < ns.length) ∧
    (∀ d ∈ g.denominators, d < ns.length) ∧
    (∀ d ∈ g.denominators, 0 < val d)

/-- **Aux Ga1 (the tie is a three-sided constraint).**  A gate row with no
parents and no denominator records is tied to every node list under every
evaluation; a row citing a parent index beyond the stored graph is tied under
none; and a row whose recorded denominator *evaluates to zero* is rejected --
which is the clause `02:469--470` asks for, and the clause the `r2` form could
not express.  So `TiedTo` is neither always true nor always false.

The third component's evaluation is the constant `0`, a **BEYOND-PAPER AUDIT**
rejection probe: it claims no legality and exists only to fire the guard.
General in the node list and in the evaluation. -/
theorem gateRowTiedToIsAConstraint (ns : List NodeRow) (val : ℕ → ℚ) :
    GateRow.TiedTo { label := 0, tag := AtomTag.leA, parents := [],
                     denominators := [], evidence := Evidence.exactE } ns val ∧
    ¬ GateRow.TiedTo { label := 0, tag := AtomTag.leA, parents := [ns.length],
                       denominators := [], evidence := Evidence.exactE } ns val ∧
    ¬ GateRow.TiedTo { label := 0, tag := AtomTag.leA, parents := [],
                       denominators := [0], evidence := Evidence.exactE } ns
        (fun _ => 0) := by
  refine ⟨⟨by simp, by simp, by simp⟩, ?_, ?_⟩
  · rintro ⟨hpar, -, -⟩
    exact absurd (hpar ns.length (by simp)) (lt_irrefl _)
  · rintro ⟨-, -, hden⟩
    exact absurd (hden 0 (by simp)) (lt_irrefl 0)

/-- **A row of `Searches_c`** -- `02:485--487`: "its exact integer predicate,
its least returned integer, and an integer proof that the predicate persists at
all larger integers".

All three are carried as data: the predicate itself, the returned integer, and
the two proof fields (`least` for "least returned", `persists` for the integer
persistence proof).  `02:341--342` -- "Every executed search stores its
nonemptiness, tested endpoint, and termination proof" -- is why `satisfied` is
a field as well.  A `CutKind` tag is *not* a persistence certificate and is
kept only as the cutoff class of `02:478`. -/
structure SearchRow where
  /-- The exact integer predicate (`02:485--486`). -/
  predicate : ℕ → Prop
  /-- The least returned integer (`02:486`). -/
  returned : ℕ
  /-- The cutoff class of `02:478`, `ECut/PCut/DCut`. -/
  kind : CutKind
  /-- The stored nonemptiness witness (`02:341--342`): the returned integer
  satisfies the predicate. -/
  satisfied : predicate returned
  /-- "its least returned integer" (`02:486`): nothing below it satisfies the
  predicate. -/
  least : ∀ k, k < returned → ¬ predicate k
  /-- "an integer proof that the predicate persists at all larger integers"
  (`02:486--487`). -/
  persists : ∀ k, returned ≤ k → predicate k

/-- **Aux Se1 (the stored search record determines its answer).**  Two search
rows with the same exact integer predicate return the same integer: leastness
and satisfaction pin it.  This is the content of "its *least* returned integer"
and is why the record cannot silently drift.  General in the two rows. -/
theorem searchRowReturnedUnique (s t : SearchRow) (h : s.predicate = t.predicate) :
    s.returned = t.returned := by
  rcases lt_trichotomy s.returned t.returned with hlt | heq | hgt
  · exact absurd (h ▸ s.satisfied) (t.least s.returned hlt)
  · exact heq
  · exact absurd (h ▸ t.satisfied : s.predicate t.returned) (s.least t.returned hgt)

/-- **Aux Se2 (the persistence proof really is a persistence proof).**  The
stored record decides the predicate above and below the returned integer, so
`02:486--487` is checkable rather than asserted.  General. -/
theorem searchRowDecidesEverywhere (s : SearchRow) (k : ℕ) :
    (k < s.returned → ¬ s.predicate k) ∧ (s.returned ≤ k → s.predicate k) :=
  ⟨s.least k, s.persists k⟩

/-- **A row of `Static_c`** -- `02:488--499`, the frozen triple `(C, Q, l)` with
**all three** components: the ordered `ContextRefs` vector `C`, the analytic
conclusion `Q(Xi)`, and the name `l` of the separately proved theorem.

`02:494--499`: "The conclusion `Q(Xi)` is an analytic proposition used by
admissibility, and `l` is the name of a separately proved theorem which, after
the data records in `C` are instantiated, derives `Q(Xi)` from the proof-valued
atoms in `C`. ... the executable checker does not evaluate them."  The
conclusion is therefore carried as a `Context`-indexed proposition -- the
checker never evaluates it, and neither does anything here. -/
structure StaticCtxRow (Context : Type*) where
  /-- `C`: the ordered `ContextRefs` vector of topologically earlier registered
  IDs (`02:488--490`). -/
  contextRefs : List ℕ
  /-- `Q`: the analytic conclusion `Q(Xi)` (`02:494--495`). -/
  conclusion : Context → Prop
  /-- `l`: the name of the separately proved theorem (`02:495--498`). -/
  lemmaId : ℕ

/-- **One edge of a `CoeffPassDerivation` proof tree** -- `02:1042--1045`,
"Each successor coefficient tree is a concrete runtime `CoeffPassDerivation`,
not a normalizer name: its row stores ... complete checked parent/ledger proof
tree."

A proof tree over a typed expression graph is recorded here in the graph's own
adjacency form: one step per derived node, naming the node, the ordered parent
nodes the step consumes, and the coefficient-ledger row that justifies it.  The
ordering of `02:534--535` ("every expression parent, data-context reference, and
proof-valued context atom must be topologically earlier") is what makes the
adjacency list a tree rather than an unordered bag. -/
structure CoeffPassStep where
  /-- The node this step derives, as its index into `Nodes_c`. -/
  nodeId : ℕ
  /-- The ordered parent nodes the step consumes (`02:1091--1092`). -/
  parentIds : List ℕ
  /-- The coefficient-ledger row justifying the step (`02:531--536`). -/
  ledgerRef : ℕ
  deriving DecidableEq, Repr

/-- **A row of `Successor_c`** -- `02:517--524` with the literal C7 content of
`02:1091--1099`, carrying **all five** subfields the frozen
`CoeffPassDerivation` sentence of `02:1042--1045` prints: "its row stores the
root ID, exact root expression, returned literal integer `C_u`, degree `d_c`,
and complete checked parent/ledger proof tree".  `02:1106--1107` rejects a
degree annotation without the raw-coefficient row, which is why both are
fields.

The `r2` form stored only the root ID, its flat parents, flat ledger references,
`C_u` and `d_c`: the *exact root expression* and the *proof tree itself* were
absent, so `02:1045--1046` ("Reject a missing tree or a
root/expression/coefficient mismatch") had nothing to reject.  Both are now
stored, and `SuccessorRow.CoeffPassChecked` below performs exactly that
rejection.  Storing and checking the tree is *not* evaluating the graph:
`NumChecked` still needs the interpreter (GAP-EXPOSED 1). -/
structure SuccessorRow where
  /-- The named root, as its index into `Nodes_c` (`02:529`, `02:1091--1092`). -/
  root : ℕ
  /-- The **exact root expression** (`02:1043`), stored as its own typed node
  list with the named root first, rather than referred to by name. -/
  rootExpr : List NodeRow
  /-- The ordered parent nodes of the root expression (`02:1091--1092`). -/
  parents : List ℕ
  /-- The coefficient-ledger references the checked proof tree resolves
  (`02:531--536`). -/
  ledgerRefs : List ℕ
  /-- The independently computed integer coefficient `C_u` (`02:1092`). -/
  coeff : ℕ
  /-- The degree `d_c` (`02:1044`). -/
  degree : ℕ
  /-- The slot the frozen sentence calls the "complete checked parent/ledger
  proof tree" (`02:1044--1045`), stored in the adjacency form of
  `CoeffPassStep`.

  **RECORD REPAIR `R-8` (`cc-t6x`; Sol's `cc-t6n-r4` finding, registered then
  and unrepairable until this round re-opened the module).**  The frozen phrase
  is quoted here as the *name of the slot*, not as a property this encoding
  delivers: nothing types this field as complete or as checked.  What
  `SuccessorRow.CoeffPassChecked` verifies of it is exactly three local
  conditions -- non-emptiness with the head step at `root`, every consumed
  parent in range of the stored node list, and every cited ledger row among the
  row's own `ledgerRefs`.  Completeness of the derivation, i.e. that the tree
  actually derives `coeff` for `rootExpr`, is the unbuilt `CoeffPassDerivation`
  EVALUATOR and is REGISTERED as a deferred obligation on this module's ledger
  row. -/
  tree : List CoeffPassStep
  deriving DecidableEq, Repr

/-- **`02:1045--1046`: "Reject a missing tree or a root/expression/coefficient
mismatch."**  The three rejections, in the frozen order, plus the resolution
clause of `02:531--536`:

* the named root resolves in `Nodes_c`, the stored exact root expression begins
  at *that* node, and the row's `C_u` is that node's coefficient -- one
  existential covering the root, expression and coefficient matches;
* the proof tree is present and rooted at the row's root -- so a *missing* tree
  is rejected;
* every parent the tree consumes is a stored node, and every ledger row the tree
  cites is one of the row's own coefficient-ledger references.

This is a *checker on stored data*.  It does not evaluate the graph and makes no
claim to be `NumChecked` (`02:541--544`, GAP-EXPOSED 1).

**RECORD REPAIR `R-8` (`cc-t6x`), stated once more where it bites.**  The three
clauses above are the whole of what this predicate checks about `tree`.  It does
**not** check that the tree is *complete* -- that every step needed to derive
`coeff` from `rootExpr` is present -- because that is the unbuilt
`CoeffPassDerivation` evaluator (REGISTERED, deferred).  A tree consisting of a
single well-formed root step satisfies this predicate. -/
def SuccessorRow.CoeffPassChecked (r : SuccessorRow) (ns : List NodeRow) : Prop :=
  (∃ nd : NodeRow, ns[r.root]? = some nd ∧ r.rootExpr.head? = some nd ∧
      nd.coeff = r.coeff) ∧
    (∃ s : CoeffPassStep, r.tree.head? = some s ∧ s.nodeId = r.root) ∧
    (∀ s ∈ r.tree, ∀ p ∈ s.parentIds, p < ns.length) ∧
    (∀ s ∈ r.tree, s.ledgerRef ∈ r.ledgerRefs)

/-- **Aux Su3 (a missing tree is rejected).**  `02:1045`, "Reject a missing
tree".  General in the row and the node list. -/
theorem successorRowCoeffPassRejectsMissingTree {r : SuccessorRow}
    {ns : List NodeRow} (h : r.tree = []) : ¬ r.CoeffPassChecked ns := by
  rintro ⟨-, ⟨s, hs, -⟩, -, -⟩
  rw [h] at hs
  exact absurd hs (by simp)

/-- **Aux Su4 (a coefficient mismatch is rejected).**  `02:1045--1046`, "Reject
... a root/expression/coefficient mismatch": if the node the row names carries a
coefficient other than the row's `C_u`, the row fails.  This is the clause that
makes `coeff` a checked field rather than an annotation.  General. -/
theorem successorRowCoeffPassRejectsCoefficientMismatch {r : SuccessorRow}
    {ns : List NodeRow} {nd : NodeRow} (hnd : ns[r.root]? = some nd)
    (hne : nd.coeff ≠ r.coeff) : ¬ r.CoeffPassChecked ns := by
  rintro ⟨⟨nd', hnd', -, hcoeff⟩, -, -, -⟩
  rw [hnd] at hnd'
  exact hne (by rw [Option.some.injEq] at hnd'; rw [hnd']; exact hcoeff)

/-- **Aux Su5 (an unregistered ledger citation is rejected).**  `02:531--536`,
"every static context, tail-term, cutoff-search, and successor reference must
resolve": a proof-tree step citing a ledger row the successor row does not carry
fails the check.  General. -/
theorem successorRowCoeffPassRejectsUnresolvedLedgerRef {r : SuccessorRow}
    {ns : List NodeRow} {s : CoeffPassStep} (hs : s ∈ r.tree)
    (hne : s.ledgerRef ∉ r.ledgerRefs) : ¬ r.CoeffPassChecked ns := by
  rintro ⟨-, -, -, hres⟩
  exact hne (hres s hs)

/-! #### The Stage-1 matrix at the context (`cc-t6x-r1`)

**Why this exists, and why the `cc-t6x` bytes were wrong without it.**  The
`r0` form of every declaration below took the Stage-1 matrix as a free binder
`M₁ : X₁ → Y₁ → Bool` over arbitrary finite carriers.  The frozen source does
not leave `M_1` open once the public record and the parameter record are fixed:

* `05-public-records.tex:167--170`: "In particular, the Stage-1 matrix
  `M_1(Public, K)` **is already determined by these accessors and the equations
  in `sec:one-level`**; it is available when the type of the balanced family is
  formed."  The sentence closes the accessor enumeration of `05:139--165` and is
  printed *for exactly the purpose these declarations need it* -- the type of
  the balanced family is `Rows(M_1(Public, K))^{q_2}` of
  `def:level-parameters` (`05:176--181`), the very family whose size `N_2` the
  `02:519--524` guard bounds.
* `05-public-records.tex:336--337`, step `L2` of `proc:level-step`: "Construct
  Stage 1, `M_1`, from `R, a, q_1, s` by the carrier and entry equations in
  `\Cref{sec:one-level}`."  That is the constructor call, with its four inputs
  named.

So `M_1` is a **DEFINED** quantity, and under the definitional-chain rule it is
reified by evaluating the source's own chain in dependency order rather than
taken as a binder.  The three inputs `L2` names are all accessors of
the schedule context -- `a = aExpAt C` (`eq:stage1-scales`, `06:314`; the
`r2` derived chain, see the block below), `s = sOf C` (`eq:s-choice`, `06:118`,
banked), `R = C.P.R` (`P3` of
`def:level-public-input`, `05:13--52`) -- and the fourth, `q_1`, is *derived
from `a`* by the banked `Stage1SlotBinding.q₁ = 2^a - 2`, so it is not a fifth
input and does not enter as a binder either (`stage1BindingAt_q₁` puts that
identity in the kernel).  The carrier and entry equations of `sec:one-level`
are the banked `StageOneInterlace.stageOne`, consumed by pin.

**What is still open, stated rather than absorbed (LIVENESS, UNWIRED).**  This
def is the `L2` call evaluated at the context's accessors; it is **not** a
formalized `LevelStep`, and no `LevelTrace` field is wired to it here.  The
canonical inhabitation of the surrounding procedure remains the REGISTERED,
OPEN ledger row `S5-LEVEL-STEP`. -/

/-! #### The derived Stage-1 exponent chain (`cc-t6x-r2`)

**Why four local accessors, and why here.**  `eq:Astar-choice` (`06:298--304`)
sets `A_*` to "the least power of two at least
`max{16, B_pub, z_R, log_2 q_2, s, ceil(log_2 U_0)}`", and `eq:stage1-scales`
(`06:314--315`) then defines `a = C_0 (log_2 A_*)^2` and `q_1 = 2^a - 2`.  The
banked `Section5Admissibility` chain (`astarThresholdOf` `:545`, `lgAstarOf`
`:555`, `aExpOf` `:560`, `q1Of` `:571`) evaluates exactly these displays, but
reads the fourth branch of the threshold as `lq2Of C = C.W.r_2`
(`Section5Admissibility.lean:541`) -- a **stored** width field, which
`05-public-records.tex:188--189` says the record does not have.  The derived
reading of that branch is the banked width-arc accessor
`Section5Admissibility.DerivedWidths.r2At` (`:3604`, `r_2 = log_2 q_2` at the
scheduled intake), landed at `cc-t6s-r6` for precisely this migration.

The four declarations below are the banked chain with that one argument
replaced.  They live **here** and not in `Section5Admissibility` because that
module is BYTE-FROZEN under `S5-M3-ROWS-AUDIT-001` and this round lifts no
freeze; the `At`/`Of` naming keeps them distinct from the banked accessors in
every scope (no homonym shadowing of the `cc-t6s-r3` class), and each one
consumes banked ingredients by pin rather than re-expanding a display:
`ScheduleTemplateResidue.astarThreshold` (`:1002`), `.astarExp` (`:1011`),
`.q1Stage1` (`:882`) and `MassRedistributionTail.aStage1` (`:3216`).

**Reader counterpart: none exists, and that is checked rather than assumed.**
The 41-page reader artifact never prints `A_*`, the threshold of
`eq:Astar-choice`, or the equation `a = C_0(log_2 A_*)^2`: its Stage-1
subsection takes `a` as given and writes only `q_1 := 2^a - 2`
(`03-parameterized-construction.tex:142`), which is `q1At`'s counterpart and is
claimed by no other declaration on this route.  `astarThresholdAt`, `lgAstarAt`
and `aExpAt` therefore claim **no** reader item. -/

/-- **The `A_*` threshold at the schedule context, read at the DERIVED
`log_2 q_2`** -- `eq:Astar-choice` (`06:298--304`): "let `A_*` be the least power
of two at least `max{16, B_pub, z_R, log_2 q_2, s, ceil(log_2 U_0)}`".

Argument for argument this is the banked `Section5Admissibility.astarThresholdOf`
(`:545--547`) with its third argument -- the branch `06:301` writes `\log_2q_2`
-- replaced by the derived `DerivedWidths.r2At C` in place of the stored
`lq2Of C = C.W.r_2`.  The other four branches are unchanged banked accessors of
`C.P` and `C.K`, and the `max` itself is the banked
`ScheduleTemplateResidue.astarThreshold`, consumed by pin and not re-expanded.

No reader counterpart (see the block docstring above). -/
noncomputable def astarThresholdAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ScheduleTemplateResidue.astarThreshold (Section5Admissibility.BpubOf C)
    (Section5Admissibility.zROf C)
    (Section5Admissibility.DerivedWidths.r2At C)
    (Section5Admissibility.sOf C)
    (Section5Admissibility.clU0Of C)

/-- **`log_2 A_*` at the schedule context** (`06:314`), evaluated as the exponent
of the least power of two above the corrected threshold.  The exponent function
is the banked `ScheduleTemplateResidue.astarExp` (`:1011`), consumed by pin.

No reader counterpart (see the block docstring above). -/
noncomputable def lgAstarAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ScheduleTemplateResidue.astarExp (astarThresholdAt C)

/-- **`a = C_0 (log_2 A_*)^2` at the schedule context** -- `eq:stage1-scales`,
`06:314`, evaluated through the banked `MassRedistributionTail.aStage1`
(`:3216`) at the context's own `C_0` and the corrected `log_2 A_*`.

`06:314` is the `a` line of the `gathered` block; `06:315` is `q_1`, `06:316` is
`t_1` and `06:317` is `b_1`.  (The `r1` bytes cited `06:317` for `a` in three
places; all three are corrected this round.)

No reader counterpart (see the block docstring above). -/
noncomputable def aExpAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  MassRedistributionTail.aStage1 C.K.C₀ (lgAstarAt C)

/-- **`q_1 = 2^a - 2` at the schedule context** -- `eq:stage1-scales`, `06:315`,
evaluated through the banked `ScheduleTemplateResidue.q1Stage1` (`:882`) at the
corrected exponent.  The route carries one copy of the display `2^a - 2`, not
two: this accessor only *applies* the banked reification.

The `- 2` is the paper's own, not a convenience: `06:315` prints `q_1 = 2^a - 2`
and not `2^a`, which is the `q`-vs-`Q` trap this campaign screens for.

Reader counterpart: `03-parameterized-construction.tex:142`,
`q_1:=2^a-2`. -/
noncomputable def q1At {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ScheduleTemplateResidue.q1Stage1 (aExpAt C)

/-- **Seam receipt (the chain reads the DERIVED `log_2 q_2`).**  The one slot
that distinguishes this chain from the banked one holds
`DerivedWidths.r2At C`, definitionally -- so the `r1` defect ("`aExpOf C`
consumes the stored `C.W.r_2`") cannot recur silently under a later edit to
these bytes.  General in the two carriers and the context.  PROVED by `rfl`. -/
theorem astarThresholdAt_reads_derived_r2At {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) :
    astarThresholdAt C
      = ScheduleTemplateResidue.astarThreshold (Section5Admissibility.BpubOf C)
        (Section5Admissibility.zROf C)
        (Section5Admissibility.DerivedWidths.r2At C)
        (Section5Admissibility.sOf C)
        (Section5Admissibility.clU0Of C) := rfl

/-- **Aux A.1 (the corrected exponent clears the frozen Stage-1 floor).**
`06:481`: "`A_*` is a power of two, and `A_* >= 16`", so `log_2 A_* >= 4`
through the banked `ScheduleTemplateResidue.four_le_astarExp` at the frozen
first branch `16` of `eq:Astar-choice`; with `C_0 >= 1` a `LevelConfig` field,
`a = C_0 (log_2 A_*)^2 >= 16`.

This is what makes `stage1BindingAt.three_le_a` derivable at the corrected
exponent rather than assumed, and it is proved on `aExpAt` -- the banked
`Section5Admissibility.sixteen_le_aExpOf` (`:977`) is the same statement about
the *other* subject and is not a substitute for it.  General in the two carriers
and the context.  PROVED. -/
theorem sixteen_le_aExpAt {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    16 ≤ aExpAt C := by
  have h16 : 16 ≤ astarThresholdAt C :=
    ScheduleTemplateResidue.sixteen_le_astarThreshold _ _ _ _ _
  have h4 : 4 ≤ lgAstarAt C := ScheduleTemplateResidue.four_le_astarExp h16
  have hC : 1 ≤ C.K.C₀ := C.K.C₀pos
  have hsq : 16 ≤ lgAstarAt C ^ 2 := by nlinarith
  have hmul : lgAstarAt C ^ 2 ≤ C.K.C₀ * lgAstarAt C ^ 2 :=
    Nat.le_mul_of_pos_left _ hC
  have heq : aExpAt C = C.K.C₀ * lgAstarAt C ^ 2 := rfl
  omega

/-- **Aux A.2 (`eq:stage1-scales` closes at the corrected exponent).**
`q_1 + 2 = 2^a`, which `05:418` prints as a `WF` accessor clause (the `r1` bytes
cited `05:419`, which is only the opening `\[` of the following display;
corrected at `cc-t6x-r2` per Sol's FINDING 1).  With `q_1`
evaluated as `2^a - 2` this is a theorem of the corrected chain at every
context, not a gate on a stored copy.  General in the two carriers and the
context.  PROVED. -/
theorem q1At_add_two_eq {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    q1At C + 2 = 2 ^ aExpAt C := by
  have h16 := sixteen_le_aExpAt C
  have hge : 2 ≤ (2 : ℕ) ^ aExpAt C := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ aExpAt C := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold q1At ScheduleTemplateResidue.q1Stage1
  omega

/-- **Aux A.3 (round trip: the correction is conservative on coherent records).**

The banked chain is not refuted by this round, only freed of a hypothesis it
never declared.  On a context whose **stored** width record is coherent with its
own intake -- the upstream `StageTwoRelaxed.DerivedWidthCoherent`, whose width
clause is exactly `C.W.q_2 = q_2(G, s)` -- the corrected threshold and the banked
`Section5Admissibility.astarThresholdOf` are equal, because the banked
`DerivedWidths.lq2Of_eq_r2At_of_coherent` (`Section5Admissibility.lean:3692`)
identifies the two readings of `log_2 q_2`.

That lemma is the one the banked module says exists so the seam "cannot be
assumed silently" (`Section5Admissibility.lean:3676--3681`); this is its first
consumption on the Stage-1 side.  Note the direction: coherence is used *here*,
in a corollary about agreement, and **not** in the chain -- the corrected
accessors are unconditional, which is what makes the ten downstream statements
gate-free where they were gate-free before.  General in the two carriers, the
context and the coherence proof.

**The honest cost, stated rather than absorbed.**  This corollary and its
successor are the **only** two declarations of this module that are conditional
on coherence, and a context exhibiting it needs a `StageTwoWidths` built at the
derived width -- which is the OPEN, REGISTERED `S5-LEVEL-STEP` row.  So these two
are agreement statements whose canonical instance is deferred, exactly like every
`hgate`-carrying statement here.  Nothing downstream rests on them: the four
chain accessors, the binding, `stageOneAt`, both row-count lemmas, and the
gate-free family-size declarations are all unconditional and do not cite them.
PROVED. -/
theorem astarThresholdAt_eq_banked_of_coherent {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    {C : Section5Admissibility.ScheduleContext V E}
    (h : StageTwoRelaxed.DerivedWidthCoherent C.W C.P.G
      (Section5Admissibility.sOf C)) :
    astarThresholdAt C = Section5Admissibility.astarThresholdOf C := by
  unfold astarThresholdAt Section5Admissibility.astarThresholdOf
  rw [Section5Admissibility.DerivedWidths.lq2Of_eq_r2At_of_coherent h]

/-- **Aux A.4 (the round trip, carried to `a` and to `q_1`).**  The corrected
Stage-1 exponent and width agree with the banked ones on every coherent record,
so no value a scheduled record could have carried is changed by the correction;
what the correction removes is the freedom of `C.W.r_2` at records no schedule
produces.  General in the two carriers, the context and the coherence proof.
PROVED. -/
theorem aExpAt_eq_banked_of_coherent {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {C : Section5Admissibility.ScheduleContext V E}
    (h : StageTwoRelaxed.DerivedWidthCoherent C.W C.P.G
      (Section5Admissibility.sOf C)) :
    aExpAt C = Section5Admissibility.aExpOf C ∧
      q1At C = Section5Admissibility.q1Of C := by
  have ha : aExpAt C = Section5Admissibility.aExpOf C := by
    unfold aExpAt Section5Admissibility.aExpOf lgAstarAt
      Section5Admissibility.lgAstarOf
    rw [astarThresholdAt_eq_banked_of_coherent h]
  exact ⟨ha, by unfold q1At Section5Admissibility.q1Of; rw [ha]⟩

/-- **The Stage-1 slot binding at the schedule context** -- the `(a, s)` pair
that `05:336--337` hands to the Stage-1 constructor, evaluated at the context's
own defining displays rather than chosen.

`a := aExpAt C` is `eq:stage1-scales` (`06:314`) evaluated **through the derived
`log_2 q_2`**; `s := Section5Admissibility.sOf C` is `eq:s-choice` (`06:118`)
evaluated.  The two legality guards of the banked
`FiniteSlots.Stage1SlotBinding` are **derived**, not assumed: `3 <= a` from
`sixteen_le_aExpAt` above, and `0 < s` from the banked
`Section5Admissibility.sOf_floor` (whose first clause is `3 < s`).  No numeral
of ours enters this binding.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The `r1` bytes set `a` to the banked
`Section5Admissibility.aExpOf C`, whose `A_*` threshold reads the stored
`lq2Of C = C.W.r_2`; the exponent therefore varied with a field
`05-public-records.tex:188--189` says the record does not have.  The statement
shape is unchanged -- same binder, same structure, same two guards -- and only
the subject is corrected, which is what the `r1` gate prescribed.  `s` is
untouched: its chain reads only `C.P` and `C.K`, which is why
`stage1BindingAt_s` was already CLEAR and is byte-identical to the `r1` bytes.

Contrast `StageOneInterlace.stage1Legal`, whose own docstring says
`(a, s) = (7, 64)` is *not* the pair the schedule computes and that "no
parameter schedule may be read out of" it: that is the banked slot-layer
smoke binding, and this is the scheduled one. -/
noncomputable def stage1BindingAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) :
    FiniteSlots.Stage1SlotBinding where
  a := aExpAt C
  s := Section5Admissibility.sOf C
  three_le_a := le_trans (by norm_num) (sixteen_le_aExpAt C)
  s_pos := lt_trans (by norm_num) (Section5Admissibility.sOf_floor C).1

/-- **Accessor-probe receipt 1 (`a`).**  The binding's Stage-1 exponent is the
context's evaluated `a` of `06:314`, routed through the derived `log_2 q_2`, and
nothing else, definitionally.  Composed with
`astarThresholdAt_reads_derived_r2At` this is the kernel receipt that the
binding's exponent never reads `C.W.r_2`.  PROVED by `rfl`. -/
theorem stage1BindingAt_a {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    (stage1BindingAt C).a = aExpAt C := rfl

/-- **Accessor-probe receipt 2 (`s`).**  The binding's bin width is the
context's evaluated `s` and nothing else, definitionally.  This is the same
one-scale seam the `cc-t6t`/`cc-t6w` rounds closed for the other consumers.
PROVED by `rfl`. -/
theorem stage1BindingAt_s {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    (stage1BindingAt C).s = Section5Admissibility.sOf C := rfl

/-- **Accessor-probe receipt 3 (`q_1`, the input `05:336` names third).**  The
binding's derived `q_1 = 2^a - 2` is the context accessor `q1At C` of `06:315`,
definitionally -- so the route carries **one** copy of the ambient Stage-1 width,
and `q_1` is not a free input of the constructor call.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The `r1` receipt landed on
`Section5Admissibility.q1Of C`, which propagates the stored-`r_2` dependence of
`aExpOf`; deriving `q_1` from `a` was never the defect (`06:315` requires it),
and the receipt survives the repair unchanged apart from its subject.  PROVED by
`rfl`. -/
theorem stage1BindingAt_q₁ {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    (stage1BindingAt C).q₁ = q1At C := rfl

/-- **The Stage-1 matrix `M_1(Public, K)` at the schedule context** --
`05:167--170` ("already determined by these accessors and the equations in
`sec:one-level`") realized through the constructor call of `05:336--337`
("Construct Stage 1, `M_1`, from `R, a, q_1, s` by the carrier and entry
equations in `\Cref{sec:one-level}`").

The body is the banked `StageOneInterlace.stageOne` -- the carrier and entry
equations of `eq:stage1-universes-and-value`
(`07-one-level-construction.tex:141--148`), consumed by pin and not restated --
applied to the reified binding and to the public record's own source matrix
`R : X_R -> Y_R -> {0,1}` at the frozen zero-based carriers `X_R = [m_R]`,
`Y_R = [n_R]` of `P3` (`05:13--52`, `conv:finite-slots`).

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The constructor body and both carriers are
unchanged; what changed is the binding it is applied to, whose `a` -- hence
`q_1`, hence `Rows(M_1)` -- is now the derived chain of `astarThresholdAt` ..
`q1At` rather than the banked chain through the stored `C.W.r_2`.  So this is
`05:167--170`'s "already determined by these accessors" at the accessors the
paper actually has.

Reader counterpart: `03-parameterized-construction.tex`,
`eq:paper-M1-definition` (label line 156; the entry equation itself is at 153,
which is what the `r1` bytes cited for the label). -/
noncomputable def stageOneAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) :
    StageOneInterlace.Stage1Rows (stage1BindingAt C) (Fin C.P.mR) →
      StageOneInterlace.Stage1Cols (stage1BindingAt C) (Fin C.P.nR) → Bool :=
  StageOneInterlace.stageOne (stage1BindingAt C) C.P.R

/-- **Aux M1.1 (the frozen row-carrier count).**  `Rows(M_1) = [q_1] x Rows(R)`
(`eq:stage1-universes-and-value`, `07:143--145`; the row line is `07:144`), so
`m_1 = |Rows(M_1)| = q_1 * m_R` at the context's own two accessors.  The
multiplier is `C.P.mR = |Rows(R)|` of the public source matrix, not `m_G`.  This
is the value `02:1151` and `02:521--523` write `|Rows(M_1)|` for, computed rather
than assumed.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The cardinality computation is unchanged;
the result is now stated at the derived `q1At C`, because the `r1` right-hand
side `Section5Admissibility.q1Of C` carried the stored-`r_2` dependence of the
banked exponent chain.  General in the two carriers and the context.  PROVED. -/
theorem rowsCard_stageOneAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    BridgeOutputEquality.rowsCard (stageOneAt C)
      = q1At C * C.P.mR := by
  have h : BridgeOutputEquality.rowsCard (stageOneAt C)
      = Fintype.card (FiniteSlots.Slot (stage1BindingAt C).q₁ × Fin C.P.mR) := rfl
  rw [h, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, stage1BindingAt_q₁]

/-- **Aux M1.2 (`m_1 > 0` is DERIVED, not assumed).**  `02:1151` displays
`m_1 = |Rows(M_1)|` and the pre-builder returns it positive.  On the constructed
carrier that positivity is a *theorem*: `q_1 > 0` is the banked
`Stage1SlotBinding.q₁_pos` at the reified binding (through `a >= 3`), and
`m_R > 0` is `P3`'s own frozen guard `LevelPublicInput.mRpos` (`05:13--52`).

**This is the `cc-t6x` `[Nonempty X₁]` repair.**  The `r0` bytes discharged the
same clause from an *assumed* `[Nonempty X₁]` instance on a free row carrier,
which is an assumption the paper does not make and does not need.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The positivity argument is unchanged --
`q_1 > 0` from the reified binding's own `q₁_pos`, `m_R > 0` from `P3` -- but its
subject is now the corrected Stage-1 matrix, whose `q_1` is `q1At C`.  General in
the two carriers and the context.  PROVED. -/
theorem rowsCard_stageOneAt_pos {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (C : Section5Admissibility.ScheduleContext V E) :
    0 < BridgeOutputEquality.rowsCard (stageOneAt C) := by
  rw [rowsCard_stageOneAt]
  exact Nat.mul_pos
    (FiniteSlots.Stage1SlotBinding.q₁_pos (stage1BindingAt C)) C.P.mRpos

/-! #### The derived wrapper-width chain (`cc-t7c-r1`)

**Why seven more local accessors, and why here.**  `cc-t6x-r2` closed the
Stage-1 seam: `aExpAt` reads the `log_2 q_2` branch of `eq:Astar-choice`
through the **derived** `Section5Admissibility.DerivedWidths.r2At`, not through
the stored `lq2Of C = C.W.r_2`.  The `cc-t7c` gate found the same seam still
open one level along, on the *wrapper* side, and the finding was re-verified
first-hand this round against the frozen release source:

* `Section5Admissibility.qOf C = qWrap C.K.A_wrap (LPOf C)` (`:738`),
  `LPOf C = LPwidth (P0Of C)` (`:735`),
  `P0Of C = P0sched (CcertOf C) (sOf C) (lq2Of C) (clU0Of C) (zROf C)`
  (`:731--732`),
  `CcertOf C = Ccert (bCapOf C) (lq2Of C) (lsOf C)` (`:726--727`), and
  `bCapOf C = bCap C.P.D (aExpOf C)` (`:722`).  So `q` reads the **stored**
  `C.W.r_2` in *three* places -- twice directly through `lq2Of`, once more
  through `aExpOf`'s own `A_*` threshold.
* `QOf C = Qwidth C.P.b_out (deltaUOf C)` (`:750--751`) and
  `deltaUOf C = deltaU (etaROf C) (qOf C)` (`:745--746`), so `Q` inherits all
  three.

(Record repair **R19**, executed at `cc-t7c-r2`: the `r1` bytes cited only the
declaration-header line of each accessor.  Every span above is the complete
banked definition, header plus continuation lines, and each was re-read
first-hand this round; `qOf`, `LPOf` and `bCapOf` are one-line definitions, so
their single line already is the complete span.)

`05-public-records.tex:188--189` states that the parameter record "has no
stored width, tolerance, multiplicity, capacity, ceiling, or output-size
fields", and `05:143--156` lists `P_0, L_P, q, delta_U, Q_0, Q` among the
**Wrappers accessors**, whose defining displays it names as
`eq:q-deltaU` and `eq:Q-theta-choice`.  Both are therefore DEFINED quantities
of `(Public, K)` and are reified here by evaluating the source's own chain in
dependency order, exactly as the Stage-1 block above does.

The seven declarations below are the banked chain with the two `lq2Of`
arguments replaced by `DerivedWidths.r2At` and the one `aExpOf` argument
replaced by `aExpAt`.  Nothing else moves: `sOf`, `lsOf`, `clU0Of`, `zROf`,
`etaROf`, `C.P.D` and `C.P.b_out` are unchanged banked accessors, and every
display is consumed **by pin** from its banked reification
(`StageOneInterlace.bCap` `:653`, `ScheduleTemplateResidue.Ccert` `:1028`,
`ParameterSchedule.P0sched` `:834--835`, `.LPwidth` `:839`, `.qWrap` `:758`,
`.deltaU` `:783`, `EntryGates.Qwidth` `:249`), never re-expanded.  (Record
repair **R19** again: `P0sched` is the only two-line reification of the seven,
and the `r1` bytes cited its header line alone.)

They live **here**, beside `aExpAt`, and not in `Section5Admissibility`, for
the reason the Stage-1 block already records: that module is byte-frozen for
this arc, the `At`/`Of` split keeps the two chains distinct in every scope, and
placing the wrapper chain anywhere else would separate it from the Stage-1
chain it consumes.

**Reader counterpart: none exists, and that is checked rather than assumed.**
The 41-page reader artifact prints no wrapper-width schedule at all: its
Section-3 construction takes `q` and `Q` as given interlace widths
(`03-parameterized-construction.tex:84--89`, `:120--125`, both of which are
already assigned to `PublicRecords.LevelTrace` and to
`PublicRecords.levelTrace_W_carriers` (`PublicRecords.lean:1589`; the `r1`
bytes wrote `LevelTrace.levelTrace_W_carriers`, which names no declaration --
the same phantom-citation family as record repair **R22**, found first-hand
this round in this module's own `r1` delta and corrected here), and it never
displays `P_0`, `L_P`,
`C_cert`, `B_cap`, `delta_U` or `Q_0`.  None of the seven claims a reader
item. -/

/-- **`B_cap = D + a` at the schedule context**, `07-one-level-construction.tex`
`:154--157` -- the complete sentence and its display: `07:154` "We denote this
public certified scale by", `07:155` the opening `\[`, `07:156`
`\Bcap\defeq D+a.` and `07:157` the closing `\]` (record repair **R20**,
executed at `cc-t7c-r2`: the `r1` bytes attributed the naming sentence to the
equation line `:156` alone).  Evaluated at the public record's own `D` and the
**derived** Stage-1 exponent `aExpAt C`.

Argument for argument this is the banked `Section5Admissibility.bCapOf`
(`:722`) with its second argument -- the Stage-1 exponent -- replaced by the
derived `aExpAt C` in place of `Section5Admissibility.aExpOf C`, whose `A_*`
threshold reads the stored `lq2Of C = C.W.r_2`.  The `+` is the banked
`StageOneInterlace.bCap` (`:653`), consumed by pin.

No reader counterpart (see the block docstring above). -/
noncomputable def bCapAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  StageOneInterlace.bCap C.P.D (aExpAt C)

/-- **`C_cert = B_cap + log_2 q_2 + log_2 s + 1` at the schedule context** --
`eq:Ccert`, display `06:431--432`, label `06:433` -- evaluated through the
banked `ScheduleTemplateResidue.Ccert` (`:1028`).

Both corrected slots occur here: `B_cap` is `bCapAt C` above, and the
`log_2 q_2` summand is the derived `DerivedWidths.r2At C` in place of the
stored `lq2Of C = C.W.r_2`.  The third summand `log_2 s` is the unchanged
banked `Section5Admissibility.lsOf` (`06:432` prints `\log_2s`; `06:122` makes
`s` a power of two, so the integer logarithm is exact), and the trailing `+ 1`
is the display's own.

No reader counterpart (see the block docstring above). -/
noncomputable def CcertAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ScheduleTemplateResidue.Ccert (bCapAt C)
    (Section5Admissibility.DerivedWidths.r2At C) (Section5Admissibility.lsOf C)

/-- **`P_0 = max{16, C_cert, s, log_2 q_2, ceil(log_2 U_0), z_R}` at the
schedule context** -- the display `06:467--470` opening
`\Cref{sec:parameter-wrappers}` -- evaluated through the banked
`ParameterSchedule.P0sched` (`:834`), which is that six-branch maximum and is
consumed by pin rather than re-expanded.

Two of the six branches are corrected: `C_cert` is `CcertAt C` above, and the
fourth branch `log_2 q_2` is the derived `DerivedWidths.r2At C`.  The remaining
four -- the frozen `16`, `sOf C`, `clU0Of C` and `zROf C` -- are unchanged
banked accessors of `C.P` and `C.K`.  The numeral `16` is the display's own
first branch and is inside the banked `P0sched`, not written here.

No reader counterpart (see the block docstring above). -/
noncomputable def P0At {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ParameterSchedule.P0sched (CcertAt C) (Section5Admissibility.sOf C)
    (Section5Admissibility.DerivedWidths.r2At C) (Section5Admissibility.clU0Of C)
    (Section5Admissibility.zROf C)

/-- **`L_P = clog_2(P_0)` at the schedule context** -- the second half of the
same display, `06:471` -- evaluated through the banked
`ParameterSchedule.LPwidth` (`:839`), consumed by pin.

No reader counterpart (see the block docstring above). -/
noncomputable def LPAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ParameterSchedule.LPwidth (P0At C)

/-- **`q = 2^{A_wrap L_P^2}`, the first-wrapper width, at the schedule
context** -- `eq:q-deltaU`, display line `06:515`, label `06:518`
("Choose the first-wrapper width", `06:513`) -- evaluated through the banked
`ParameterSchedule.qWrap` (`:758`) at the configuration's own `A_wrap` and the
corrected `L_P`.

The exponent is `A_wrap L_P^2` and not `A_wrap L_P`: `06:515` prints
`q=2^{A_{\mathrm{wrap}}L_P^2}`, and the square is inside the banked `qWrap`.

No reader counterpart (see the block docstring above). -/
noncomputable def qAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  ParameterSchedule.qWrap C.K.Awrap (LPAt C)

/-- **`delta_U = eta_R/(16 q)` at the schedule context** -- `eq:q-deltaU`,
display line `06:517` (the banked `Section5Admissibility.deltaUOf` cites
`06:519`, which is that equation's `\end{equation}`; the quotient is on
`06:517`) -- evaluated through the banked `ParameterSchedule.deltaU` (`:783`)
at the unchanged banked `etaROf` and the corrected `q`.

No reader counterpart (see the block docstring above). -/
noncomputable def deltaUAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℝ :=
  ParameterSchedule.deltaU (Section5Admissibility.etaROf C) (qAt C)

/-- **`Q`, the outer bridge width, at the schedule context** --
`eq:Q-theta-choice`: `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}` on
`06:529--531` and "`Q =` the least power of two at least `Q_0`" on `06:532`,
label `06:537` -- evaluated through the banked `EntryGates.Qwidth` (`:249`),
which is that least power of two and is consumed by pin.

Its only argument beyond the public `b_out` is `delta_U`, so the whole
correction reaches `Q` through `deltaUAt` and nothing else has to move.

No reader counterpart (see the block docstring above). -/
noncomputable def QAt {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  EntryGates.Qwidth C.P.bout (deltaUAt C)

/-- **Seam receipt 1 (the wrapper chain reads the DERIVED `log_2 q_2` in both
of its slots).**  `P_0`'s fourth branch and `C_cert`'s second summand both hold
`DerivedWidths.r2At C`, definitionally -- so the `cc-t7c` defect
("`qOf C -> LPOf -> P0Of -> lq2Of := C.W.r_2`") cannot recur silently under a
later edit to these bytes.  This is the wrapper-side twin of
`astarThresholdAt_reads_derived_r2At`.  General in the two carriers and the
context.  PROVED by `rfl`. -/
theorem P0At_reads_derived_r2At {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) :
    P0At C
      = ParameterSchedule.P0sched
        (ScheduleTemplateResidue.Ccert (bCapAt C)
          (Section5Admissibility.DerivedWidths.r2At C)
          (Section5Admissibility.lsOf C))
        (Section5Admissibility.sOf C)
        (Section5Admissibility.DerivedWidths.r2At C)
        (Section5Admissibility.clU0Of C)
        (Section5Admissibility.zROf C) := rfl

/-- **Seam receipt 2 (no stored width field is reachable from the corrected
chain).**  This is the kernel statement the `cc-t7c` park could not make.  At a
fixed public record `P` and configuration `K`, the Stage-1 exponent, the
first-wrapper width and the outer bridge width are **the same values** at every
stored Stage-2 width record: the schedule context's `W` component is not read.

That is exactly `05-public-records.tex:188--189` ("There are no stored width
... fields") made checkable, and it is what makes `05:104--106` ("For fixed
`(Public, K)`, the equations of `sec:parameters` are a deterministic
straight-line program up to the balanced-family choice") true of this
formalization rather than merely asserted about it.

The statement is universally quantified over **two arbitrary** stored records,
so it needs no legal `StageTwoWidths` inhabitant and makes no legality claim;
`S5-BUNDLE-INHABITATION` is untouched.  General in the two carriers, the public
record, the configuration and both stored records.  PROVED by `rfl`. -/
theorem derivedWidths_indep_stored {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (P : PublicRecords.LevelPublicInput V E) (K : PublicRecords.LevelConfig)
    (W W' : StageTwoRelaxed.StageTwoWidths) :
    aExpAt (⟨P, K, W⟩ : Section5Admissibility.ScheduleContext V E)
        = aExpAt (⟨P, K, W'⟩ : Section5Admissibility.ScheduleContext V E) ∧
      qAt (⟨P, K, W⟩ : Section5Admissibility.ScheduleContext V E)
        = qAt (⟨P, K, W'⟩ : Section5Admissibility.ScheduleContext V E) ∧
      QAt (⟨P, K, W⟩ : Section5Admissibility.ScheduleContext V E)
        = QAt (⟨P, K, W'⟩ : Section5Admissibility.ScheduleContext V E) :=
  ⟨rfl, rfl, rfl⟩

/-- **Round trip (the correction is conservative on coherent records).**  The
banked wrapper chain is not refuted, only freed of a hypothesis it never
declared: on a context whose stored width record is coherent with its own
intake -- the upstream `StageTwoRelaxed.DerivedWidthCoherent`, whose width
clause is `C.W.q_2 = q_2(G, s)` -- the corrected `q` and `Q` equal the banked
`Section5Admissibility.qOf` and `.QOf`.

Direction, as in the Stage-1 block: coherence is used **here**, in a corollary
about agreement, and not in the chain -- `bCapAt`, `CcertAt`, `P0At`, `LPAt`,
`qAt`, `deltaUAt`, `QAt` are all unconditional.  A context exhibiting coherence
needs a `StageTwoWidths` built at the derived width, which is the OPEN,
REGISTERED `S5-LEVEL-STEP` row, so this corollary's canonical instance is
deferred exactly like the two Stage-1 ones.  Nothing downstream rests on it.
General in the two carriers, the context and the coherence proof.  PROVED. -/
theorem qAt_QAt_eq_banked_of_coherent {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {C : Section5Admissibility.ScheduleContext V E}
    (h : StageTwoRelaxed.DerivedWidthCoherent C.W C.P.G
      (Section5Admissibility.sOf C)) :
    qAt C = Section5Admissibility.qOf C ∧ QAt C = Section5Admissibility.QOf C := by
  have ha : aExpAt C = Section5Admissibility.aExpOf C :=
    (aExpAt_eq_banked_of_coherent h).1
  have hq : qAt C = Section5Admissibility.qOf C := by
    unfold qAt LPAt P0At CcertAt bCapAt Section5Admissibility.qOf
      Section5Admissibility.LPOf Section5Admissibility.P0Of
      Section5Admissibility.CcertOf Section5Admissibility.bCapOf
    rw [ha, Section5Admissibility.DerivedWidths.lq2Of_eq_r2At_of_coherent h]
  refine ⟨hq, ?_⟩
  unfold QAt deltaUAt Section5Admissibility.QOf Section5Admissibility.deltaUOf
  rw [hq]

/-- **The family-size side condition of `02:519--524`**: "Its family-size rows
are conditional on the literal stored family satisfying
`0 < N_2 <= B_bal(q_2, t_2, |Rows(M_1)|)`."

`B_bal` is the banked `ScheduleMajorantResidue.bBal`; `q_2` and `t_2` are the
banked derived accessors `DerivedWidths.q2At C` and `.t2At C`, evaluated from
the context's own intake; and `|Rows(M_1)|` is
`BridgeOutputEquality.rowsCard (stageOneAt C)`, the row count of the Stage-1
matrix the context itself determines.  None of the three enters as a free
binder.  The stored family size `N_2` is genuinely free: `02:519--520` makes the
row *conditional* on what the compiler literally stored, and `02:1142--1143`
says "do not choose `N_2` or `c_2`".

**MIGRATED (`cc-t6x`), and the body is GATE-FREE (`cc-t6x-r1`).**  Before the
migration `q_2` and `t_2` were read from a *free* stored
`StageTwoRelaxed.StageTwoWidths` binder, hence ranged over every record the
constructor admits -- including records whose stored `q_2 = 2^{r_2}` bears no
relation to `def:guarded-source-constructor`'s display
`q_2 = min{2^r : 12 s |E| <= 2^r}` (`04:391`).  The `r0` repair replaced that
binder by `(C, hgate)` and read the widths through
`DerivedWidths.toStoredAt.{0} hgate`; but the widths that identity lands on are
`q2At C` and `t2At C`, which need **no** gate proof, so carrying `hgate` in the
body made every family-size statement conditional on the OPEN `S5-LEVEL-STEP`
row for nothing.  The body is therefore stated directly at the derived
accessors, and the bridge form is recovered as the corollary
`familySizeGuardAtBridgeWidths` below -- that corollary is the one gated
statement of this block, and it is gated because it mentions the bridge record,
not because the guard needs a gate.

**CORRECTED SUBJECT (`cc-t6x-r2`), and it applies to this guard and its five
consumers below -- six of the ten declarations the `r1` gate sent back on this
count, the other four being the pre-builder block.**  `|Rows(M_1)|` is spelled
`BridgeOutputEquality.rowsCard (stageOneAt C)` exactly as `02:522--523` spells
it, and that spelling is unchanged; what changed is `stageOneAt C` itself, whose
`q_1` now comes from the derived `q1At` chain instead of the banked chain through
the stored `C.W.r_2`.  At the gate-free declarations here the context's `C.W` was
entirely unconstrained -- neither `WidthGateCore` nor `WidthsCoherent` mentions
it -- so before the correction `m_1` genuinely varied with a field the frozen
record does not have.  That is closed, and **no hypothesis was added to close
it**: the correction is in the subject, not in the premises, so every statement
that was gate-free stays gate-free. -/
def SuccessorRow.FamilySizeGuard {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N2 : ℕ)
    (C : Section5Admissibility.ScheduleContext V E) : Prop :=
  0 < N2 ∧
    N2 ≤ ScheduleMajorantResidue.bBal
      (Section5Admissibility.DerivedWidths.q2At C)
      (Section5Admissibility.DerivedWidths.t2At.{0} C)
      (BridgeOutputEquality.rowsCard (stageOneAt C))

/-- **Aux Su1 (the family-size guard predicate is satisfiable at its own
majorant).**  **NON-FIDELITY** (labelled at `cc-t6x-r2` per Sol's `r2` FINDING 5,
re-verified by the verify seat).  The frozen upper endpoint
`N_2 = B_bal(q_2, t_2, m_1)` meets the guard, because
`ScheduleMajorantResidue.bBal_pos` makes the majorant positive.  General in the
two carriers and the context.

**What this does and does not establish.**  It shows only that the **numerical
guard predicate is satisfiable** at the source-defined closed-form upper
endpoint.  It is a synthetic scalar satisfiability probe, **not** the paper's
literal balanced family: `02:520` makes the rows conditional on *the literal
stored family* satisfying the bound, and no such family is built here.  The
earlier claim that "the conditional rows of `02:519--524` are not vacuous" was
therefore too strong and is **withdrawn**; canonical inhabitation remains the
OPEN, REGISTERED `S5-LEVEL-STEP` row.

**GATE-FREE (`cc-t6x-r1`).**  The `r0` bytes carried `hgate` here and recorded
the resulting conditionality as an honest cost of the migration.  It was not a
cost of the migration but of stating the body at the bridge record: the majorant
endpoint is a fact about `bBal (q2At C) (t2At C) m_1`, and `bBal_pos` is general
in all three arguments.  The statement is unconditional again, at the *derived*
widths rather than at an arbitrary stored record -- which is strictly better than
the pre-migration form, not a restoration of it.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The majorant endpoint is the banked
`ScheduleMajorantResidue.bBal` at the same three arguments, never restated; its
third argument is now the corrected derived row count.  `bBal_pos` is general in
all three, so the proof is unchanged. -/
theorem successorRowFamilySizeGuardAtMajorant {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) :
    SuccessorRow.FamilySizeGuard
      (ScheduleMajorantResidue.bBal
        (Section5Admissibility.DerivedWidths.q2At C)
        (Section5Admissibility.DerivedWidths.t2At.{0} C)
        (BridgeOutputEquality.rowsCard (stageOneAt C)))
      C :=
  ⟨ScheduleMajorantResidue.bBal_pos _ _ _, le_refl _⟩

/-- **Aux Su2 (the guard rejects the empty family).**  `02:522` reads
`0 < N_2`, so a stored family of size zero is refused.  General in the two
carriers and the context, and gate-free.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The proof uses only the guard's first
conjunct `0 < N_2` and touches no width or row count, but the statement is about
the guard, so it is restated on the corrected guard.  It remains gate-free. -/
theorem successorRowFamilySizeGuardRejectsZero {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E) :
    ¬ SuccessorRow.FamilySizeGuard 0 C := fun h => absurd h.1 (lt_irrefl 0)

/-! #### Aux battery for the migrated family-size surface (`cc-t6x`, `-r1`)

Two general properties of the surface `FamilySizeGuard` now runs on -- a
monotonicity and a round trip -- plus the one gated corollary that reconnects it
to the banked bridge record.  Each is PROVED, and none is a restatement of
anything banked.  The banked ingredients `DerivedWidths.toStoredAt`,
`.toStoredAt_fields`, `.t2At_eq_two_pow_k2At`, `.WidthsCoherent`,
`StageTwoRelaxed.DerivedWidthCoherent` and `ScheduleMajorantResidue.bBal_pos`
are consumed **by pin**, with their arguments never re-run.
`SchedulePhysicalResidue`'s own migration battery
(`migratedEpsTwo_at_derived_t₂`, `epsTwo_at_coherent_eq_migrated`,
`migratedEpsTwo_pos_and_lt_hundredth`) *is* in this module's import closure and
none of its three is duplicated here. -/

/-- **Aux X.2 (the guard is downward closed above zero).**  `02:521--523` is a
*ceiling* on the stored family size, so any smaller positive stored family also
clears it.  This is what makes `B_bal` a majorant rather than a target, and it
is general in every argument and gate-free.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The order argument transports whatever
ceiling the guard carries, so it is unchanged; the ceiling it now transports is
the corrected one.  PROVED. -/
theorem familySizeGuardDownwardClosed {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {N2 N2' : ℕ}
    {C : Section5Admissibility.ScheduleContext V E} (hpos : 0 < N2')
    (hle : N2' ≤ N2) (h : SuccessorRow.FamilySizeGuard N2 C) :
    SuccessorRow.FamilySizeGuard N2' C :=
  ⟨hpos, le_trans hle h.2⟩

/-- **Aux X.1 (the gated corollary: the guard, read at the bridge record).**

This is the one gated statement of the family-size block, and the only place
`WidthGateCore` is needed for it: a context that clears the gate presents its
derived widths as a `StageTwoWidths` through the banked bridge
`DerivedWidths.toStoredAt.{0} hgate`, and the guard's two width slots are
exactly that record's `q₂` and `t₂`.  So a banked consumer still phrased over a
stored record sees the same side condition.

`q_2 = q2At C` is `toStoredAt_fields`' fifth clause, which the banked bridge
proves through `q₂_eq_two_pow_r₂` and **not** by `rfl` -- the pin runs through a
proved identity of the definitional chain, not through an accessor applied to a
free carrier.  `t_2 = t2At C` is the banked `t2At_eq_two_pow_k2At` at the
bridge's own `k₂` field.

Direction, and why it is stated this way round: the *body* is gate-free and the
*bridge form* is the corollary, which is the opposite of the `r0` bytes.  See
the `FamilySizeGuard` docstring.  General in the two carriers, the context, the
gate proof and the family size.

**CORRECTED SUBJECT (`cc-t6x-r2`), on BOTH sides.**  `hgate` identifies the
bridge record's `q_2` and `t_2` and says nothing about `C.W.r_2`, so it never
repaired the row count; the corrected row count now stands on both sides of the
equivalence, and the two width identities are untouched.  PROVED. -/
theorem familySizeGuardAtBridgeWidths {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N2 : ℕ)
    (C : Section5Admissibility.ScheduleContext V E)
    (hgate : Section5Admissibility.DerivedWidths.WidthGateCore.{0} C) :
    SuccessorRow.FamilySizeGuard N2 C ↔
      (0 < N2 ∧ N2 ≤ ScheduleMajorantResidue.bBal
        (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂
        (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂
        (BridgeOutputEquality.rowsCard (stageOneAt C))) := by
  have hq : (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂
      = Section5Admissibility.DerivedWidths.q2At C :=
    (Section5Admissibility.DerivedWidths.toStoredAt_fields.{0} hgate).2.2.2.2
  have ht : (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂
      = Section5Admissibility.DerivedWidths.t2At.{0} C := by
    rw [Section5Admissibility.DerivedWidths.t2At_eq_two_pow_k2At,
      StageTwoRelaxed.StageTwoWidths.t₂,
      (Section5Admissibility.DerivedWidths.toStoredAt_fields.{0} hgate).1]
  rw [SuccessorRow.FamilySizeGuard, hq, ht]

/-- **Aux X.3 (round trip: the migration is conservative on coherent records).**

A stored record coherent with the context -- `DerivedWidths.WidthsCoherent`,
whose load-bearing clause is that its stored width equals the derived one --
gives the **same** majorant as the context's own derived widths.  So the
migration changes no value a scheduled record could have carried; it removes
exactly the records no schedule produces.

`Ws` is a binder but **not a free width record**: `hcoh` pins it to the context,
exactly as `ExtensionCallInhabitation.coherentWidths_eq_bridge`'s and
`SchedulePhysicalResidue.epsTwo_at_coherent_eq_migrated`'s do.  The `q_2` clause
is `hcoh`'s fourth conjunct, the banked upstream
`StageTwoRelaxed.DerivedWidthCoherent` at this context's own intake; the `t_2`
clause is `hcoh`'s first conjunct through the record's own `t₂` display.

**GATE-FREE (`cc-t6x-r1`).**  The `r0` form took `hgate` only to name the
bridge record on the right-hand side.  With the guard's body at the derived
accessors the gate proof is not needed at all: coherence alone identifies the
two majorants.  General in the two carriers, the context and the record.

**CORRECTED SUBJECT (`cc-t6x-r2`), on BOTH majorants.**  `WidthsCoherent Ws C`
constrains the binder `Ws`, not the separate field `C.W` the `r1` exponent chain
consumed, so it never repaired the row count either; the corrected row count is
now the third argument of both majorants.  `hcoh` still pins `Ws` -- it is a
binder, not a free width record -- and neither `Ws` nor the coherence proof
enters the corrected chain.  PROVED. -/
theorem familySizeGuardMajorantAtCoherentWidths {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    {C : Section5Admissibility.ScheduleContext V E}
    {Ws : StageTwoRelaxed.StageTwoWidths}
    (hcoh : Section5Admissibility.DerivedWidths.WidthsCoherent.{0} Ws C) :
    ScheduleMajorantResidue.bBal Ws.q₂ Ws.t₂
        (BridgeOutputEquality.rowsCard (stageOneAt C))
      = ScheduleMajorantResidue.bBal
          (Section5Admissibility.DerivedWidths.q2At C)
          (Section5Admissibility.DerivedWidths.t2At.{0} C)
          (BridgeOutputEquality.rowsCard (stageOneAt C)) := by
  have hq : Ws.q₂ = Section5Admissibility.DerivedWidths.q2At C := hcoh.2.2.2
  have ht : Ws.t₂ = Section5Admissibility.DerivedWidths.t2At.{0} C := by
    simp only [StageTwoRelaxed.StageTwoWidths.t₂, hcoh.1,
      Section5Admissibility.DerivedWidths.t2At_eq_two_pow_k2At]
  rw [hq, ht]

/-- **The effective numerical schedule certificate**, `02:446--453`, as its six
frozen fields in the frozen order, over the candidate-context type `Xi` ranges
over.

Every subfield the frozen enumeration `02:454--524` prints is carried by the
six row types above.  The canonical inhabitant is `Compile(c)`
(`02:905--1120`); its construction needs the interpreter of `02:425--444`
(GAP-EXPOSED 1) and the withdrawn coefficient-pass checker (GAP-EXPOSED 2), so
the canonical-inhabitation obligation is ledger-REGISTERED and deferred (see the
module header).  `probeCert` is the interim **NON-FIDELITY** smoke inhabitant
and never discharges it. -/
structure Cert (Context : Type*) where
  /-- `Nodes_c`, "a finite acyclic typed expression graph" (`02:454--455`). -/
  nodes : List NodeRow
  /-- `NumGates_c` (`02:463`). -/
  numGates : List GateRow
  /-- `Searches_c`, "lists every cutoff search" (`02:485`). -/
  searches : List SearchRow
  /-- `Static_c` (`02:488`). -/
  staticRows : List (StaticCtxRow Context)
  /-- `Coverage_c` (`02:500`). -/
  coverage : List Pointer
  /-- `Successor_c` (`02:517`). -/
  successor : List SuccessorRow

/-- The node at index `i` carries the `pre` tag. -/
def PreNode (ns : List NodeRow) (i : ℕ) : Prop :=
  (ns[i]?.map NodeRow.phase) = some Phase.pre

/-- **The `pre`-builder slice** -- `02:930--933`, "The *pre-builder slice* is
the induced subgraph on the `pre` nodes; it need not be a contiguous list
prefix." -/
def preIndices (ns : List NodeRow) : List ℕ :=
  (List.range ns.length).filter
    (fun i => decide ((ns[i]?.map NodeRow.phase) = some Phase.pre))

/-- **Aux S1 (membership in the slice).**  General in the node list. -/
theorem memPreIndicesIff (ns : List NodeRow) (i : ℕ) :
    i ∈ preIndices ns ↔ i < ns.length ∧ PreNode ns i := by
  simp [preIndices, PreNode, List.mem_filter, List.mem_range]

/-- **The phase rule** -- `02:794--796`, "No `pre` node is permitted to have a
parent mentioning `N_2, c_2, C_2`, or a trace field constructed after `M_1`",
i.e. no `pre` node has a `post` parent; together with C8's in-range check
(`02:1108--1112`). -/
def PhaseSeparated (ns : List NodeRow) : Prop :=
  ∀ (i : ℕ) (nd : NodeRow), ns[i]? = some nd → nd.phase = Phase.pre →
    ∀ j ∈ nd.parents, j < ns.length ∧ PreNode ns j

/-- A set of node indices is closed under taking parents. -/
def DependencyClosed (ns : List NodeRow) (S : List ℕ) : Prop :=
  ∀ i ∈ S, ∀ nd : NodeRow, ns[i]? = some nd → ∀ j ∈ nd.parents, j ∈ S

/-- **`02:933--934`: "Because no such node has a `post` parent, this slice is
dependency closed."**  Proved, in exactly that direction: the phase rule of
`02:794--796` implies dependency closure of the `pre` slice.  This is the
structural fact `clm:eff-ledger-prebuilder` (`02:1164--1166`) rests on.
General in the node list. -/
theorem preIndicesDependencyClosed {ns : List NodeRow} (h : PhaseSeparated ns) :
    DependencyClosed ns (preIndices ns) := by
  intro i hi nd hnd j hj
  have hmem := (memPreIndicesIff ns i).1 hi
  have hpre : nd.phase = Phase.pre := by
    have := hmem.2
    rw [PreNode, hnd] at this
    simpa using this
  obtain ⟨hjlt, hjpre⟩ := h i nd hnd hpre j hj
  exact (memPreIndicesIff ns j).2 ⟨hjlt, hjpre⟩

/-- **The frozen successor-root count** -- `02:1086`, "does not enlarge the
173-root successor manifest".  A `CANONICAL-FORM` count printed by the source
itself. -/
def successorRootCount : ℕ := 173

/-- A certificate stores exactly `173` successor rows.

**This is a count, not a completeness predicate**, and the name says so.
`02:526--540` requires far more of the real manifest: "the decoded target,
auxiliary, static, tail, and successor IDs must equal the immutable registry of
`\Cref{app:certificate-registry}` in exactly its canonical order".  That
equality needs the immutable registry itself, which is an appendix table this
route has not transcribed, so the *registry-order equality* is not expressible
here and this declaration is registered under that honest name.  The frozen
count is `02:1086`, "does not enlarge the 173-root successor manifest".

**RECORD REPAIR `R-9` (`cc-t6x`; Sol's `cc-t6n-r4` finding, registered then and
unrepairable until this round re-opened the module).**  The `r3` bytes said "the
length test is all that is expressible", which is **too strong and is
withdrawn**.  What is not expressible is equality with the untranscribed
registry *in its canonical order*.  A strictly weaker, purely local check --
distinctness of the stored successor root IDs,
`(K.successor.map SuccessorRow.root).Nodup` -- **is** expressible without the
registry, and would already refute the constant manifest of
`partialSchemaScreenAdmitsAConstantSuccessorManifest`.  It is deliberately
**not** landed here: adding a screen clause is a change to the partial
interface, which is `PartialLedgerInterfaces`' surface and belongs to the round
that strengthens it, not to a migration round.  The gap is therefore recorded
with its true boundary rather than overstated. -/
def Cert.HasSuccessorRootCount {Context : Type*} (K : Cert Context) : Prop :=
  K.successor.length = successorRootCount

/-- The `pre` leaf of the interim smoke inhabitant.  **NON-FIDELITY**, and
**BEYOND-PAPER AUDIT** in every field value: the paper never prints a node. -/
def probeNodeZero : NodeRow where
  coreSort := CoreSort.natS
  name := "PROBE.LEAF.0"
  leaf := some (NodeLeaf.lit CoreSort.natS 1)
  op := NodeOp.lit
  parents := []
  expectedSort := CoreSort.natS
  elabObligations := []
  coeff := 1
  blDegree := 0
  phase := Phase.pre

/-- A `pre` node above the leaf.  **NON-FIDELITY**, and **BEYOND-PAPER AUDIT**
in every field value. -/
def probeNodeOne : NodeRow where
  coreSort := CoreSort.posS
  name := "PROBE.ASPOS.1"
  leaf := none
  op := NodeOp.asPos
  parents := [0]
  expectedSort := CoreSort.posS
  elabObligations := [ElabObligation.checkedPositive]
  coeff := 1
  blDegree := 1
  phase := Phase.pre

/-- A `post` node above both, exercising the phase join of `02:783--784`.
**NON-FIDELITY**, and **BEYOND-PAPER AUDIT** in every field value. -/
def probeNodeTwo : NodeRow where
  coreSort := CoreSort.ratS
  name := "PROBE.DIVQ.2"
  leaf := none
  op := NodeOp.divQ
  parents := [0, 1]
  expectedSort := CoreSort.ratS
  elabObligations := [ElabObligation.checkedDenominator]
  coeff := 1
  blDegree := 1
  phase := Phase.post

/-- **Aux Ce0 (the three probe nodes satisfy the leaf/operation agreement).**
The leaf node carries a leaf and the two derived nodes do not, so the probe is
consistent with `02:224` and `02:456` even though it is NON-FIDELITY in every
value. -/
theorem probeNodesLeafConsistent :
    probeNodeZero.LeafConsistent ∧ probeNodeOne.LeafConsistent ∧
      probeNodeTwo.LeafConsistent := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [NodeRow.LeafConsistent, probeNodeZero, probeNodeOne, probeNodeTwo]

/-- The three nodes of the interim smoke inhabitant: a `pre` leaf, a `pre` node
above it, and a `post` node above both.  **NON-FIDELITY** (see the header). -/
def probeNodes : List NodeRow := [probeNodeZero, probeNodeOne, probeNodeTwo]

/-- **NON-FIDELITY smoke inhabitant of `Cert`.**  The paper's own inhabitant is
`Compile(c)` (`02:905--1120`), which needs GAP-EXPOSED 1, 2 and 4; the
canonical-inhabitation obligation for `Cert` is ledger-REGISTERED and deferred,
and this probe never discharges it.  `probeCertIsNotThePaperCertificate` proves
in the kernel that it is not the paper's object.  Every field value below is
**BEYOND-PAPER AUDIT**: it claims no legality and names no schedule quantity. -/
def probeCert : Cert Unit where
  nodes := probeNodes
  numGates := [{ label := 0, tag := AtomTag.leA, parents := [0], denominators := [],
                 evidence := Evidence.exactE }]
  searches := [{ predicate := fun k => 2 ≤ k, returned := 2, kind := CutKind.pcut,
                 satisfied := le_refl 2, least := fun _ hk => by omega,
                 persists := fun _ hk => hk }]
  staticRows := [{ contextRefs := [0], conclusion := fun _ => True, lemmaId := 0 }]
  coverage := [Pointer.byNum 0]
  successor :=
    [{ root := 0, rootExpr := [probeNodeZero], parents := [], ledgerRefs := [0],
       coeff := 1, degree := 8,
       tree := [{ nodeId := 0, parentIds := [], ledgerRef := 0 }] }]

/-- **Aux Ce1 (the probe satisfies the phase rule).**  Its single `post` node
is a child, never a parent of a `pre` node, so `02:794--796` holds of it. -/
theorem probeNodesPhaseSeparated : PhaseSeparated probeNodes := by
  intro i nd hnd hpre j hj
  rcases i with _ | _ | _ | i
  · have h0 : nd = probeNodeZero := by simpa [probeNodes] using hnd.symm
    subst h0
    simp [probeNodeZero] at hj
  · have h1 : nd = probeNodeOne := by simpa [probeNodes] using hnd.symm
    subst h1
    have hj0 : j = 0 := by simpa [probeNodeOne] using hj
    subst hj0
    exact ⟨by simp [probeNodes], by simp [PreNode, probeNodes, probeNodeZero]⟩
  · have h2 : nd = probeNodeTwo := by simpa [probeNodes] using hnd.symm
    subst h2
    exact absurd hpre (by decide)
  · simp [probeNodes] at hnd

/-- **Aux Ce2 (the probe is not degenerate).**  All six frozen fields are
nonempty, so it exercises every field of the record rather than collapsing to
the empty certificate. -/
theorem probeCertFieldsNonempty :
    probeCert.nodes ≠ [] ∧ probeCert.numGates ≠ [] ∧ probeCert.searches ≠ [] ∧
      probeCert.staticRows ≠ [] ∧ probeCert.coverage ≠ [] ∧
      probeCert.successor ≠ [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [probeCert, probeNodes]

/-- **NON-FIDELITY pole.**  The probe fails even the `173`-row count of the
frozen successor manifest (`02:1086`), let alone the registry equality of
`02:530--532`, so no reader of this module can mistake it for the paper's
`Cert_c`.  This is the whole point of labelling it a probe. -/
theorem probeCertIsNotThePaperCertificate : ¬ probeCert.HasSuccessorRootCount := by
  simp [Cert.HasSuccessorRootCount, probeCert, successorRootCount]

/-- **The terminal conversion from codes back to values** -- `02:318--321`,
"`bl(x) <= B` implies `x < 2^B` for a natural or absolute integer terminal".
`02:322--324` records that the rule is terminal: it may not be composed through
a power node.  Accordingly this is a standalone lemma with no companion that
iterates it.  General. -/
theorem terminalCodeToValue {x B : ℕ} (h : Nat.clog 2 (x + 1) ≤ B) : x < 2 ^ B := by
  have h1 : x + 1 ≤ 2 ^ Nat.clog 2 (x + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : (2 : ℕ) ^ Nat.clog 2 (x + 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- **The rational half of the terminal rule** -- `02:320--321`, "for a reduced
rational `p/q` with `q >= 1`, `bl(|p|) <= B` implies `|p/q| <= |p| < 2^B`".
The first inequality is the banked
`SchedulePhysicalResidue.abs_le_natAbs_num`, consumed by pin.  `02:321--322`
keeps denominator-code bounds separate, and none is asserted here.  General. -/
theorem terminalCodeToValueRat {r : ℚ} {B : ℕ}
    (h : Nat.clog 2 (r.num.natAbs + 1) ≤ B) : |r| < (2 : ℚ) ^ B := by
  have h1 : |r| ≤ ((r.num.natAbs : ℕ) : ℚ) :=
    SchedulePhysicalResidue.abs_le_natAbs_num r
  have h2 : r.num.natAbs < 2 ^ B := terminalCodeToValue h
  have h3 : ((r.num.natAbs : ℕ) : ℚ) < (2 : ℚ) ^ B := by exact_mod_cast h2
  linarith

/-! ## Section 3  The three balanced-family envelopes

`eq:balanced-family-envelope` (`02:183--188`) and
`eq:balanced-family-binary-length-envelope` (`02:293--301`) are **consumed by
pin** from `ScheduleMajorantResidue` and are not restated; only the real
logarithmic envelope of `02:189--194`, which no banked module carries, is new
here, together with the composite that feeds the code envelope into the
terminal rule of `02:318--321`. -/

/-- **`eq:balanced-family-log-envelope`** (`02-mechanical-contract.tex`, label
line 193, display lines 189--194):

```
 log_2 B_bal(q,t,m) <= t (1 + log_2 max{q, 1000 m t^2, 2}).
```

The two quantities on the left and inside the right-hand logarithm are the
banked `ScheduleMajorantResidue.bBal` and `.xBal`, consumed by pin.  This is
the one display of the certificate definition that is genuinely real-valued:
`02:496--499` sends such expressions to a `Static_c` conclusion rather than to
a node, so this lemma is the analytic surrogate that the `Static_c` row of
`02:1002--1004` ("the indexed-family size is handled only by
`eq:balanced-family-log-envelope`") names.

Proved as an identity and weakened to the frozen `<=`; `02:179` fixes the
positivity of the base through `X_bal >= 2`, so no side condition is assumed.
General in `q`, `t`, `m`. -/
theorem balancedFamilyLogEnvelope (q t m : ℕ) :
    Real.logb 2 (ScheduleMajorantResidue.bBal q t m)
      ≤ (t : ℝ) * (1 + Real.logb 2 (ScheduleMajorantResidue.xBal q t m)) := by
  have hX : (2 : ℝ) ≤ ((ScheduleMajorantResidue.xBal q t m : ℕ) : ℝ) := by
    exact_mod_cast ScheduleMajorantResidue.two_le_xBal q t m
  have hXpos : (0 : ℝ) < ((ScheduleMajorantResidue.xBal q t m : ℕ) : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((ScheduleMajorantResidue.bBal q t m : ℕ) : ℝ)
      = (2 * ((ScheduleMajorantResidue.xBal q t m : ℕ) : ℝ)) ^ t := by
    rw [ScheduleMajorantResidue.bBal]; push_cast; ring
  have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  apply le_of_eq
  rw [hcast]
  simp only [Real.logb]
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hXpos)]
  rw [show (1 : ℝ) + Real.log ((ScheduleMajorantResidue.xBal q t m : ℕ) : ℝ) / Real.log 2
      = (Real.log 2 + Real.log ((ScheduleMajorantResidue.xBal q t m : ℕ) : ℝ)) / Real.log 2 by
    field_simp]
  rw [mul_div_assoc]

/-- **The code envelope composed with the terminal conversion.**  This is the
one place where the two banked halves meet: the literal binary-length envelope
`eq:balanced-family-binary-length-envelope` (`02:293--301`), consumed by pin as
`ScheduleMajorantResidue.n2ExplicitCodeEnvelope`, followed by the terminal
code-to-value rule of `02:318--321`.  `02:322--324` forbids composing that rule
through a power node, and this statement composes it exactly once, at the
terminal.

The frozen positivity side condition `0 < N` of `02:293` is restored here even
though the banked envelope does not need it, so the hypothesis list is the
frozen one.  General in `N`, `q`, `t`, `m`, `B`. -/
theorem balancedFamilyCodeEnvelopeTerminal {N q t m B : ℕ} (_hpos : 0 < N)
    (hle : N ≤ ScheduleMajorantResidue.bBal q t m)
    (hB : 1 + t * (1 + max (max (Nat.clog 2 (q + 1))
        (Nat.clog 2 (1000 + 1) + Nat.clog 2 (m + 1) + 2 * Nat.clog 2 (t + 1))) 1) ≤ B) :
    N < 2 ^ B :=
  terminalCodeToValue
    (le_trans (ScheduleMajorantResidue.n2ExplicitCodeEnvelope hle) hB)

/-! ## Section 4  The state-locked ledger schema of `thm:eff-ledger`

`02:630--649` prints the state-locked quantifier prefix and its principal
conclusion, and says why: "Thus the state does not silently vary between the
schema, numerical, successor, and soundness claims."  That lock is the content
transcribed here.

**This section lands an AUXILIARY parametric schema over an explicitly PARTIAL
screen, not `thm:eff-ledger` and not `SchemaChecked`.**  The frozen theorem
asserts the existence of a *particular* configuration, compiler, machine and
step function whose `SchemaChecked`, `NumChecked` and `Successor_16` are the
executable checkers of `02:526--550`.  Those three checkers evaluate the node
graph under `val_Xi` and are unbuilt on this route (GAP-EXPOSED 1--2), so they
remain **interface fields**.  Accordingly the declarations below are named
`...PartialSchema`: no declaration here claims `thm:eff-ledger`, and the
canonical instantiation is a registered deferred obligation (module header).

**The screen does not occupy `SchemaChecked`'s slot, and its name says so.**
`02:526--540` requires far more than this module can express: registry equality
in canonical order, the pinned registry hash and generated counts, one coverage
pointer per target and none for an unregistered target, topological earliness of
every expression parent and context atom, resolution of every static, tail,
cutoff and successor reference, exactly the four registered Extension roots, and
no pending compiler tag.  The `r2` form of this interface called its field
`schemaChecked` while expressing only the phase rule, selected pointer ranges
and a row count -- so, as the `r2` gate observed, *a `173`-fold junk successor
list passed every check it expressed*.  The field is therefore renamed
`partialSchemaScreen`, every consumer is renamed to match, and
`partialSchemaScreenAdmitsAConstantSuccessorManifest` below proves that junk
observation **in the kernel** rather than leaving it as prose.

What the screen *does* pin, rather than leave abstract, is the certificate
type: the interface is parameterized by the module's own `Cert Context`, and
four fields force `partialSchemaScreen` to imply the parts of `02:526--540` and
`02:1042--1046` that are expressible without the interpreter -- the phase rule
of `02:527--528`, the in-range/advertised-kind pointer condition of `02:527`,
the successor-root count of `02:529` and `02:1086`, and the coefficient-pass
check of `02:1045--1046`.  A `partialSchemaScreen` that is identically `True`
therefore no longer inhabits the interface.

The `Static_c`/soundness items of `02:619--628` are among the components
`02:630--631` explicitly suppresses when it prints the locked prefix ("the
already fixed source constants and the four static/soundness components just
enumerated"), so they are not fields either. -/

/-- The interfaces the partial ledger schema quantifies over.  Every field is
named after the frozen predicate it stands for, **except** the screen, which is
named after what it actually is.

The certificate type is **not** abstract: it is this module's `Cert Context`,
and the four `partialSchemaScreen_*` fields tie the abstract screen to the
certificate semantics that are expressible here.  The remaining predicates are
the frozen checkers, which stay unimplemented (GAP-EXPOSED 2). -/
structure PartialLedgerInterfaces (Config Machine Context : Type*) where
  /-- The `K1--K4` searches returned an admissible universal configuration
  (`02:899--903`). -/
  configAdmissible : Config → Prop
  /-- `Compile` at a configuration and an incoming exponent (`02:905--907`). -/
  builtFrom : Config → ℕ → Cert Context
  /-- **A partial screen, strictly weaker than `SchemaChecked` of
  `02:526--540`.**  It is *not* that predicate and does not stand in its place;
  the frozen checker needs the registry of `app:certificate-registry` and the
  interpreter of `02:425--444`, neither of which exists on this route. -/
  partialSchemaScreen : Cert Context → Prop
  /-- Tie 1 to the certificate semantics: `02:527--528`, "no pre-builder node
  has a post-builder parent". -/
  partialSchemaScreen_phase : ∀ K, partialSchemaScreen K → PhaseSeparated K.nodes
  /-- Tie 2: `02:527`, "every pointer is in range and of the advertised kind",
  read at the two row lists this module carries. -/
  partialSchemaScreen_pointers : ∀ K, partialSchemaScreen K → ∀ p ∈ K.coverage,
    (p.sourceTag = RowTag.numericalRow → p.row < K.numGates.length) ∧
      (p.sourceTag = RowTag.staticRow → p.row < K.staticRows.length)
  /-- Tie 3: `02:529` ("every successor root is named") at the frozen `173`-row
  manifest count of `02:1086`. -/
  partialSchemaScreen_successorRootCount :
    ∀ K, partialSchemaScreen K → K.HasSuccessorRootCount
  /-- Tie 4: `02:1042--1046`, every successor row carries its exact root
  expression and its proof-tree slot, and no row has a missing tree or a
  root/expression/coefficient mismatch.  (**`R-8`, `cc-t6x`:** the tie is
  exactly `CoeffPassChecked`, which does not check that the tree is
  *complete*.) -/
  partialSchemaScreen_coeffPass : ∀ K, partialSchemaScreen K →
    ∀ r ∈ K.successor, r.CoeffPassChecked K.nodes
  /-- `NumChecked(Cert_c, Xi)` (`02:541--544`). -/
  numChecked : Cert Context → Context → Prop
  /-- `Successor_16(Cert_c, Xi, n)` (`02:544--550`). -/
  successor16 : Cert Context → Context → ℕ → Prop
  /-- The maximum of the finite ordered list `ExecutedRoots(Cert_c)` of
  `02:589--591`, **without** the fixed `2`: the frozen `R(c)` of `02:585--586`
  is `max({2} u ExecutedRoots(Cert_c))`, and the schema below is where that
  outer `max 2` is applied, exactly once. -/
  executedRootsMax : Cert Context → ℕ
  /-- The output of the designated total byte machine `A_cert` on the canonical
  encoding of `c` (`02:591--595`). -/
  certOutput : Machine → ℕ → Cert Context
  /-- "on every byte string that is not a canonical natural-number encoding it
  returns the fixed `Reject` code and halts" (`02:594--595`). -/
  rejectsNonCanonical : Machine → Prop
  /-- `TypeFacts(Xi)` (`02:429--433`). -/
  typeFacts : Context → Prop
  /-- `InputEnvelope^pre_c(n, Public)` (`02:603`, `eq:pre-input-envelope`). -/
  inputEnvelopePre : ℕ → ℕ → Context → Prop
  /-- "`c_2 : [N_2] -> Rows(M_1)^{q_2}` is indexed `(q_2, t_2, 1/(100 t_2))`
  balanced" (`02:604--605`). -/
  indexedBalanced : Context → Prop
  /-- `0 < N_2 <= B_bal(q_2, t_2, |Rows(M_1)|)` (`02:606`). -/
  familyBound : Context → Prop

/-- **`H(c, n, Xi)`** -- `02:599--607` and `02:645--646`, "exactly the displayed
conjunction in item (c), including `n >= n_step(c)`".  The five conjuncts are
carried in the frozen print order. -/
def EffLedgerSchemaHyp {Config Machine Context : Type*}
    (I : PartialLedgerInterfaces Config Machine Context)
    (nstep : ℕ → ℕ) (c n : ℕ) (Xi : Context) : Prop :=
  nstep c ≤ n ∧ I.typeFacts Xi ∧ I.inputEnvelopePre c n Xi ∧
    I.indexedBalanced Xi ∧ I.familyBound Xi

/-- **The state-locked schema shape of `02:630--649`, over the partial
screen**:

```
 exists K_* exists Cert exists A_cert exists R exists n_step
   [ forall c  PartialSchemaScreen(Cert_c) ]
   and [ forall c forall n forall Xi
           ( H(c,n,Xi) => NumChecked(Cert_c,Xi) and Successor_16(Cert_c,Xi,n) ) ].
```

Everything that makes the lock a lock is present: `R` and `n_step` carry their
defining equations of `02:585--587`, `A_cert` carries its output equation and
its rejection clause of `02:591--595`, and the same `cert` function serves both
conjuncts.  `02:646--647` is the reason: "Thus the state does not silently vary
between the schema, numerical, successor, and soundness claims."

**This is not `thm:eff-ledger`** (GAP-EXPOSED 3), and it is weaker than the
frozen shape in a second, named way: the frozen first conjunct is
`SchemaChecked(Cert_c)` and this one is the explicitly partial screen.  So the
declaration is the *shape* at an arbitrary interface with a *weakened* first
conjunct, twice removed from the frozen theorem, and its name records both.  The
two poles below show the shape is neither trivially true nor trivially false;
`partialSchemaScreenAdmitsAConstantSuccessorManifest` records how far the
weakening reaches. -/
def EffLedgerPartialSchema {Config Machine Context : Type*}
    (I : PartialLedgerInterfaces Config Machine Context) : Prop :=
  ∃ K : Config, ∃ cert : ℕ → Cert Context, ∃ A : Machine, ∃ R nstep : ℕ → ℕ,
    I.configAdmissible K ∧
    (∀ c, cert c = I.builtFrom K c) ∧
    (∀ c, I.certOutput A c = cert c) ∧
    I.rejectsNonCanonical A ∧
    (∀ c, R c = max 2 (I.executedRootsMax (cert c))) ∧
    (∀ c, nstep c = 2 ^ 2 ^ (R c + 2)) ∧
    (∀ c, I.partialSchemaScreen (cert c)) ∧
    (∀ c n (Xi : Context), EffLedgerSchemaHyp I nstep c n Xi →
      I.numChecked (cert c) Xi ∧ I.successor16 (cert c) Xi n)

/-- **Aux L1 (the state really is locked).**  `02:646--647`.  From the shape
one recovers a *single* certificate family that simultaneously satisfies the
screen claim and, at the *derived* step function
`n_step(c) = 2^{2^{R(c)+2}}` computed from that same family's executed roots,
the numerical and successor claims.  No second existential is introduced in
between, which is exactly what "the state does not silently vary" forbids.
General in the interfaces. -/
theorem effLedgerPartialSchemaSingleState {Config Machine Context : Type*}
    {I : PartialLedgerInterfaces Config Machine Context}
    (h : EffLedgerPartialSchema I) :
    ∃ cert : ℕ → Cert Context,
      (∀ c, I.partialSchemaScreen (cert c)) ∧
      ∀ c n (Xi : Context),
        2 ^ 2 ^ (max 2 (I.executedRootsMax (cert c)) + 2) ≤ n →
        I.typeFacts Xi → I.inputEnvelopePre c n Xi → I.indexedBalanced Xi →
        I.familyBound Xi →
        I.numChecked (cert c) Xi ∧ I.successor16 (cert c) Xi n := by
  obtain ⟨_K, cert, _A, R, nstep, _hK, _hbuilt, _hout, _hrej, hR, hstep, hschema, hnum⟩ := h
  refine ⟨cert, hschema, ?_⟩
  intro c n Xi hn htf henv hbal hfam
  refine hnum c n Xi ⟨?_, htf, henv, hbal, hfam⟩
  rw [hstep c, hR c]
  exact hn

/-- **Aux L2 (the semantic ties reach the shape's conclusion).**  Whatever
interface satisfies the shape, its certificate family satisfies the expressible
clauses of `02:526--540` and `02:1042--1046` at every incoming exponent.  This
is what the four `partialSchemaScreen_*` fields buy: the shape can no longer be
satisfied by an interface whose screen is empty of content.  It remains *only*
those clauses -- that is precisely the partiality the name announces.  General
in the interfaces. -/
theorem effLedgerPartialSchemaForcesCertificateSemantics
    {Config Machine Context : Type*}
    {I : PartialLedgerInterfaces Config Machine Context}
    (h : EffLedgerPartialSchema I) :
    ∃ cert : ℕ → Cert Context, ∀ c,
      PhaseSeparated (cert c).nodes ∧ (cert c).HasSuccessorRootCount ∧
        ∀ r ∈ (cert c).successor, r.CoeffPassChecked (cert c).nodes := by
  obtain ⟨_K, cert, _A, _R, _nstep, _hK, _hbuilt, _hout, _hrej, _hR, _hstep, hschema, _⟩ := h
  exact ⟨cert, fun c => ⟨I.partialSchemaScreen_phase _ (hschema c),
    I.partialSchemaScreen_successorRootCount _ (hschema c),
    I.partialSchemaScreen_coeffPass _ (hschema c)⟩⟩

/-- The single successor row `auditCert` repeats `173` times.  Every value is
**BEYOND-PAPER AUDIT**; it names no schedule quantity and claims no legality.
It is built to *pass* the partial screen, which is the whole point of
`partialSchemaScreenAdmitsAConstantSuccessorManifest` below. -/
def auditSuccessorRow : SuccessorRow where
  root := 0
  rootExpr := [probeNodeZero]
  parents := []
  ledgerRefs := [0]
  coeff := 1
  degree := 8
  tree := [{ nodeId := 0, parentIds := [], ledgerRef := 0 }]

/-- A certificate meeting the four expressible clauses of `02:526--540` and
`02:1042--1046`: `probeNodes` satisfies the phase rule, the coverage list is
empty, the successor list has exactly the frozen `173` rows, and every row
passes `CoeffPassChecked`.

**NON-FIDELITY**, and **BEYOND-PAPER AUDIT** in every value: this is the
satisfiability witness of the shape pole below, and nothing else.  Only its
`173`-row count is source-anchored (`02:1086`); the row content is not the
paper's, and all `173` rows are literally the same row. -/
def auditCert : Cert Unit where
  nodes := probeNodes
  numGates := []
  searches := []
  staticRows := []
  coverage := []
  successor := List.replicate successorRootCount auditSuccessorRow

/-- **Aux L3 (the audit certificate meets the expressible screen clauses).**
`02:527--529` and `02:1045--1046` at the parts this route can express.
**NON-FIDELITY.** -/
theorem auditCertMeetsExpressibleSchemaClauses :
    PhaseSeparated auditCert.nodes ∧ auditCert.HasSuccessorRootCount ∧
      auditCert.coverage = [] ∧
      ∀ r ∈ auditCert.successor, r.CoeffPassChecked auditCert.nodes := by
  refine ⟨probeNodesPhaseSeparated, ?_, rfl, ?_⟩
  · simp [Cert.HasSuccessorRootCount, auditCert]
  · intro r hr
    have hrr : r = auditSuccessorRow := List.eq_of_mem_replicate hr
    subst hrr
    refine ⟨⟨probeNodeZero, ?_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, ?_⟩
    · simp [auditCert, probeNodes, auditSuccessorRow]
    · intro s hs p hp
      have : s = { nodeId := 0, parentIds := [], ledgerRef := 0 } := by
        simpa [auditSuccessorRow] using hs
      subst this
      simp at hp
    · intro s hs
      have : s = { nodeId := 0, parentIds := [], ledgerRef := 0 } := by
        simpa [auditSuccessorRow] using hs
      subst this
      simp [auditSuccessorRow]

/-- The interface used by both poles below.  `partialSchemaScreen` is the
singleton predicate `K = auditCert`, so the four semantic ties are discharged
from `auditCertMeetsExpressibleSchemaClauses` rather than assumed.

**BEYOND-PAPER AUDIT** at the one-point carriers: it audits our encoding at a
point the paper never visits and claims no legality. -/
def auditInterfaces : PartialLedgerInterfaces Unit Unit Unit where
  configAdmissible := fun _ => True
  builtFrom := fun _ _ => auditCert
  partialSchemaScreen := fun K => K = auditCert
  partialSchemaScreen_phase := by rintro K rfl; exact probeNodesPhaseSeparated
  partialSchemaScreen_pointers := by rintro K rfl p hp; simp [auditCert] at hp
  partialSchemaScreen_successorRootCount := by
    rintro K rfl; simp [Cert.HasSuccessorRootCount, auditCert]
  partialSchemaScreen_coeffPass := by
    rintro K rfl; exact auditCertMeetsExpressibleSchemaClauses.2.2.2
  numChecked := fun _ _ => True
  successor16 := fun _ _ _ => True
  executedRootsMax := fun _ => 0
  certOutput := fun _ _ => auditCert
  rejectsNonCanonical := fun _ => True
  typeFacts := fun _ => True
  inputEnvelopePre := fun _ _ _ => True
  indexedBalanced := fun _ => True
  familyBound := fun _ => True

/-- **The `r2` gate's sharpest observation, now kernel-checked.**  A successor
manifest consisting of `173` copies of one and the same row passes the partial
screen.  `02:530--532` requires the decoded successor IDs to "equal the immutable
registry of `\Cref{app:certificate-registry}` in exactly its canonical order",
which a constant list plainly is not; the screen as currently written cannot see
the difference, because the registry table is not transcribed on this route
(GAP-EXPOSED 2).

This theorem exists so that the gap is a *proved fact about our encoding*
rather than a caveat in prose, and so that any later strengthening of the screen
has a concrete statement to break.  **BEYOND-PAPER AUDIT** in every value.

**RECORD REPAIR `R-9` (`cc-t6x`), the same withdrawal as at
`Cert.HasSuccessorRootCount`.**  "The screen cannot see the difference" is a
fact about *this* screen, not a limit of what is expressible without the
registry: a local `Nodup` on the stored root IDs would break this very theorem
and needs no appendix table.  What genuinely needs the registry is canonical
*order*.  The clause is not added here for the reason given at that
declaration. -/
theorem partialSchemaScreenAdmitsAConstantSuccessorManifest :
    auditInterfaces.partialSchemaScreen auditCert ∧
      auditCert.successor.length = successorRootCount ∧
      ∀ r ∈ auditCert.successor, r = auditSuccessorRow := by
  refine ⟨rfl, ?_, ?_⟩
  · show (List.replicate successorRootCount auditSuccessorRow).length = successorRootCount
    exact List.length_replicate ..
  · intro r hr
    exact List.eq_of_mem_replicate hr

/-- **Statement pole 1: the shape is not trivially true.**  The trivial
witness fails it -- at an interface whose screen is the empty predicate the whole
conjunction is refutable, so `EffLedgerPartialSchema` is a real constraint on
its interfaces and not a tautology.

**BEYOND-PAPER AUDIT** at the one-point carriers: this instantiation audits our
encoding at a point the paper never visits and claims no legality. -/
theorem effLedgerPartialSchemaIsNotTriviallyTrue :
    ∃ I : PartialLedgerInterfaces Unit Unit Unit, ¬ EffLedgerPartialSchema I := by
  refine ⟨{ auditInterfaces with
            partialSchemaScreen := fun _ => False
            partialSchemaScreen_phase := fun _ h => absurd h not_false
            partialSchemaScreen_pointers := fun _ h => absurd h not_false
            partialSchemaScreen_successorRootCount := fun _ h => absurd h not_false
            partialSchemaScreen_coeffPass := fun _ h => absurd h not_false }, ?_⟩
  rintro ⟨_, cert, _, _, _, _, _, _, _, _, _, hschema, _⟩
  exact hschema 0

/-- **Statement pole 2: the shape is not trivially false.**  It is satisfiable,
so a future proof of the paper's instance is not blocked by a shape defect in
the transcription -- and, unlike the r0/r1 form of this pole, the witness must
now exhibit a certificate that actually satisfies the four expressible clauses
of `02:526--540` and `02:1042--1046`, not an interface whose predicates are all
`True`.

**BEYOND-PAPER AUDIT** at the one-point carriers: this audits our encoding at a
point the paper never visits, claims no legality, and is strictly weaker
evidence than the paper's own instantiation, which remains GAP-EXPOSED 3. -/
theorem effLedgerPartialSchemaHoldsAtAnAuditInterface :
    EffLedgerPartialSchema auditInterfaces := by
  refine ⟨(), fun _ => auditCert, (), fun _ => 2, fun _ => 2 ^ 2 ^ 4, trivial,
    fun _ => rfl, fun _ => rfl, trivial, fun _ => rfl, fun _ => by norm_num,
    fun _ => rfl, ?_⟩
  intro _ _ _ _
  exact ⟨trivial, trivial⟩

/-! ## Section 5  The fixed manifest `G1--G9`

`02:657--701`: "Split every displayed conjunction in `def:admissibility-groups`
into atomic clauses, preserve the order in which the clauses are printed, and
expand each three-entry family in the order `j = 0, 1, 2`.  The resulting
manifest `G` has the following nine blocks."  All nine are landed as a closed
roster with the frozen content of each in its constructor docstring; see
GAP-EXPOSED 4 for what the expansion into atomic clauses would need. -/

/-- **The nine manifest blocks** -- `02:663--701`, in the frozen print order. -/
inductive ManifestBlock where
  /-- **G1 `WF`**: "the public-, configuration-, accessor-, carrier-,
  power-of-two-, divisibility-, positivity-, and balanced-family clauses
  printed under `WF`" (`02:664--666`). -/
  | wf
  /-- **G2 `Source`**: "the least-power-of-two definition of `q_2`,
  `eq:template-source-ratio`, and `eq:eta-choice`" (`02:667--668`). -/
  | source
  /-- **G3 `Stage1`**: `eq:input-depth-request`, `eq:stage1-C0-gate`,
  `eq:stage1-hard-seed-threshold`--`eq:stage1-projection-ceilings`, "and the
  three instances of every indexed row" (`02:669--673`). -/
  | stage1
  /-- **G4 `Stage2`**: `eq:stage2-two-depth-comparisons`,
  `eq:stage2-structural-gates`--`eq:epsilon-product`,
  `eq:physical-stage4-gates`, `eq:all-extension-gates` (`02:674--677`). -/
  | stage2
  /-- **G5 `Stage3`**: `eq:hard-seed-width-gates` and
  `eq:stage3-separation-gates` (`02:678--679`). -/
  | stage3
  /-- **G6 `Dense`**: `eq:raw-low-gates`, `eq:dense-separation-gates`,
  `eq:dense-source-row-gate`, `eq:source-protection-gate`,
  `eq:dense-defect-gates`, `eq:routing-slack` (`02:680--683`). -/
  | dense
  /-- **G7 `Wrapper`**: `eq:q-deltaU`, `eq:wrapper-template-gates`,
  `eq:tref-search`--`eq:terminal-wrapper-gates`,
  `eq:parameter-wrapper-survival-gates`, `eq:reference-profile-gates`,
  `eq:wrapper-low-rung-gates`, `eq:wrapper-owner-gates` (`02:684--690`). -/
  | wrapper
  /-- **G8 `Direct`**: `0 < delta_U <= 1/200`, the defining identity for
  `lambda_def`, `eq:direct-theta-gates`, `eq:direct-numeric-gate`, and the
  displayed implication to `eq:direct-entry-gates` (`02:691--694`). -/
  | direct
  /-- **G9 `ExtensionCoverage`**: "exactly `ExtDense`, `ExtTwo`, `ExtEarly`,
  and `ExtTerminal` ...  It contains no reached call, support set, capacity,
  equipartition, or retained rectangle" (`02:695--700`). -/
  | extensionCoverage
  deriving DecidableEq, Repr

/-- The nine-block manifest in the frozen print order of `02:663--701`. -/
def manifestBlocks : List ManifestBlock :=
  [ManifestBlock.wf, ManifestBlock.source, ManifestBlock.stage1,
    ManifestBlock.stage2, ManifestBlock.stage3, ManifestBlock.dense,
    ManifestBlock.wrapper, ManifestBlock.direct,
    ManifestBlock.extensionCoverage]

/-- **Aux G1 (the manifest is the complete frozen nine-block list).**  Nine
entries, no repetition, and every block occurs -- "no clause dropped" at the
block level.  General. -/
theorem manifestBlocksIsTheCompleteRoster :
    manifestBlocks.length = 9 ∧ manifestBlocks.Nodup ∧
      ∀ b : ManifestBlock, b ∈ manifestBlocks := by
  refine ⟨rfl, by decide, ?_⟩
  intro b; cases b <;> decide

/-- **The four closed Localized-Extension schemas** -- `02:510--513` and
`02:696--698`, `eq:extension-coverage-closed`. -/
inductive ExtSchema where
  /-- `ExtDense`. -/
  | extDense
  /-- `ExtTwo`. -/
  | extTwo
  /-- `ExtEarly`. -/
  | extEarly
  /-- `ExtTerminal`. -/
  | extTerminal
  deriving DecidableEq, Repr

/-- The four schemas in the frozen print order. -/
def extSchemas : List ExtSchema :=
  [ExtSchema.extDense, ExtSchema.extTwo, ExtSchema.extEarly,
    ExtSchema.extTerminal]

/-- **Aux G2 (the extension roster is the complete frozen list).**  Exactly
four, which is what `02:536--538` ("exactly the four registered Extension
roots") and C4 (`02:965--966`) check.  General. -/
theorem extSchemasIsTheCompleteRoster :
    extSchemas.length = 4 ∧ extSchemas.Nodup ∧ ∀ e : ExtSchema, e ∈ extSchemas := by
  refine ⟨rfl, by decide, ?_⟩
  intro e; cases e <;> decide

/-- **The ninth block's coverage condition** -- C4, `02:965--966`: "For the
ninth block append exactly four pointers, one to each closed schema in
`eq:extension-coverage-closed`", together with `02:536--538`, "exactly the four
registered Extension roots must occur".  `02:1288--1297` proves those four
implications as `S5`, so each pointer is a `ByStatic` pointer.

The pointers are **keyed by `ExtSchema`**, not stored as an anonymous list: a
total function out of the four-element schema type is exactly "one pointer to
each closed schema", and the two clauses then say that each one is correctly
tagged and that no two schemas are covered by the same static row.  A list of
four distinct `ByStatic` rows does *not* express this -- it never mentions
`ExtDense`, `ExtTwo`, `ExtEarly` or `ExtTerminal`. -/
def ExtensionCoverageClosed (ptrs : ExtSchema → Pointer) : Prop :=
  (∀ e : ExtSchema, (ptrs e).sourceTag = RowTag.staticRow) ∧
    ∀ e f : ExtSchema, (ptrs e).row = (ptrs f).row → e = f

/-- The canonical keying of the ninth block: one `ByStatic` pointer per schema,
at the four `S5` rows of `02:1288--1297`, in the frozen roster order of
`02:510--513`.  The four row indices are registry positions, not schedule
quantities; they are **BEYOND-PAPER AUDIT** values used only to exhibit the
guard. -/
def extensionCoverageProbe : ExtSchema → Pointer
  | ExtSchema.extDense => Pointer.byStatic 0
  | ExtSchema.extTwo => Pointer.byStatic 1
  | ExtSchema.extEarly => Pointer.byStatic 2
  | ExtSchema.extTerminal => Pointer.byStatic 3

/-- **Aux G3 (the keyed condition is inhabited).**  Four distinct `ByStatic`
rows, one per schema, satisfy it -- so the two clauses are not jointly
unsatisfiable.  **BEYOND-PAPER AUDIT** in the four row indices. -/
theorem extensionCoverageProbeIsClosed :
    ExtensionCoverageClosed extensionCoverageProbe := by
  constructor
  · intro e; cases e <;> rfl
  · intro e f h; cases e <;> cases f <;> first | rfl | (exact absurd h (by decide))

/-- **Statement pole 1 for `ExtensionCoverageClosed`: a mistagged pointer is
rejected.**  C4 (`02:966--967`) says "Reject any attempted pointer with a
different source tag", and `02:1288--1297` makes the four Extension pointers
analytic, hence `ByStatic`.  Re-tagging `ExtDense` as `ByNum` breaks the
condition.

**BEYOND-PAPER AUDIT** in the row indices: a rejection probe claiming no
legality, exhibited only to show that the tag guard fires. -/
theorem extensionCoverageRejectsAMistaggedPointer :
    ¬ ExtensionCoverageClosed
        (fun e => match e with
          | ExtSchema.extDense => Pointer.byNum 0
          | e' => extensionCoverageProbe e') := by
  intro h
  exact absurd (h.1 ExtSchema.extDense) (by decide)

/-- **Statement pole 2 for `ExtensionCoverageClosed`: two schemas may not share
one row.**  `02:533` requires "exactly one coverage pointer per target and no
pointer for an unregistered target"; a single static row standing for both
`ExtDense` and `ExtTwo` would cover four targets with three rows.

**BEYOND-PAPER AUDIT** in the row indices: a rejection probe claiming no
legality, exhibited only to show that the injectivity guard fires. -/
theorem extensionCoverageRejectsASharedRow :
    ¬ ExtensionCoverageClosed
        (fun e => match e with
          | ExtSchema.extTwo => Pointer.byStatic 0
          | e' => extensionCoverageProbe e') := by
  intro h
  have := h.2 ExtSchema.extDense ExtSchema.extTwo rfl
  exact absurd this (by decide)

/-- **The target/AUX distinction** -- `02:702--707`: "The three sufficient
rational rows in `eq:raw-low-rung-gates` are registered auxiliary proof rows,
not additional Dense targets. ...  This target/AUX distinction is part of the
immutable registry." -/
inductive ManifestRowKind where
  /-- A registered admissibility target. -/
  | target
  /-- A registered auxiliary proof row. -/
  | aux
  deriving DecidableEq, Repr

/-- The three sufficient rational rows of `eq:raw-low-rung-gates`, each
registered `aux` (`02:702--707`). -/
def rawLowRungRows : List ManifestRowKind :=
  [ManifestRowKind.aux, ManifestRowKind.aux, ManifestRowKind.aux]

/-- **Aux G3 (`02:702--704`).**  The three raw-low-rung rows are auxiliary
rows, never Dense targets, and there are exactly three of them.  `02:1346--1349`
repeats the point in the soundness induction: they "are not smuggled in as
Dense targets".  General. -/
theorem rawLowRungRowsAreAux :
    rawLowRungRows.length = 3 ∧ ∀ r ∈ rawLowRungRows, r = ManifestRowKind.aux := by
  refine ⟨rfl, ?_⟩
  intro r hr
  simp only [rawLowRungRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h <;> exact h

/-! ## Section 6  Fixing the universal constants, `K1--K4`

`02:798--903`.  The tuple `K_* = (C_0, c_seed, A_wrap, B_s, c_b, C_in)` is the
banked `PublicRecords.LevelConfig` and is not redeclared; what this section
lands is the two literal constants of `02:808`, the frozen gate they satisfy,
and the arithmetic each of the four steps proves. -/

/-- **The four constant-fixing steps** -- `02:814--898`. -/
inductive KStep where
  /-- **K1** (`02:815--839`): the terminating search for `T` with `T >= 64` and
  `9T^2 - 2 >= m_HS`, `B_s = T^2`, and the three integer comparisons for
  `j_0(v) = max{0, floor(49v/100) - 1}` at `v = Tu`, `u >= 3`. -/
  | k1
  /-- **K2** (`02:840--868`): the formal-variable pass that makes
  `c_seed` independent of `A_wrap`, and the candidate `k^* = 100 L_P^2` with
  `10000(4L_P)^2 <= 2401 k^*`, giving `j_49(k^*) >= 4 L_P`. -/
  | k2
  /-- **K3** (`02:869--873`): `C_in` is the maximum of zero and the emitted
  additive binary-loss constants of the Stage-1 row-extraction ceilings. -/
  | k3
  /-- **K4** (`02:874--897`): with `C_in` fixed, the first coefficient pass
  computes `C_exc^0, B_exc^0`, and `A_wrap` is the least integer above
  `c_seed` satisfying `eq:Awrap-coefficient-search`; the search is nonempty by
  the tested witness `A = 2^M`, `M = C_exc^0 + B_exc^0 + c_seed + 8`. -/
  | k4
  deriving DecidableEq, Repr

/-- The four constant-fixing steps in the frozen print order. -/
def kSteps : List KStep := [KStep.k1, KStep.k2, KStep.k3, KStep.k4]

/-- **Aux K1 (the constant-fixing roster is the complete frozen list).**
General. -/
theorem kStepsIsTheCompleteRoster :
    kSteps.length = 4 ∧ kSteps.Nodup ∧ ∀ k : KStep, k ∈ kSteps := by
  refine ⟨rfl, by decide, ?_⟩
  intro k; cases k <;> decide

/-- **`C_0 = 152`** -- `02:808--809`, "Set `C_0 = 152`, `c_b = 6`,
`c_seed = 100`".  The third constant of that display is the banked
`ParameterSchedule.cSeed` and is not copied here. -/
def Czero : ℕ := 152

/-- **`c_b = 6`** -- `02:808--809`.  `PublicRecords.LevelConfig.cbge` is the
frozen `c_b >= 6` guard this literal choice meets exactly. -/
def cBconst : ℕ := 6

/-- **`eq:stage1-C0-gate` at the frozen choice** -- `02:809--811`, "the first
identity satisfies `eq:stage1-C0-gate` because `2401 * 150 = 360150 > 360000`".

The gate itself is **not** restated here: it is the banked
`MassRedistributionTail.stage1C0Gate`, which reifies `06:306--311`
(`2401(C_0 - 2) > 360000`, "the exact integer form of `0.49 sqrt(C_0-2) > 6`")
as a predicate of the configuration field `C_0`.  This declaration only checks
it in the kernel at the frozen `C_0 = 152` of `02:808`. -/
theorem czeroMeetsStage1C0Gate : MassRedistributionTail.stage1C0Gate Czero := by
  simp only [MassRedistributionTail.stage1C0Gate, Czero]
  norm_num

/-- **Aux K2 (`c_b = 6` meets the frozen configuration guard).**  `02:808`
picks the boundary value of `def:level-configuration`'s `c_b >= 6`
(`PublicRecords.LevelConfig.cbge`), so the choice is legal and extremal. -/
theorem cBconstMeetsConfigGuard : 6 ≤ cBconst := le_refl 6

/-- **`j_0(v) = max{0, floor(49v/100) - 1}`** -- `02:821`.  Natural truncated
subtraction *is* the frozen outer maximum with zero: `02:280` fixes
`subN(x,y) = max{x-y,0}` as the core semantics. -/
def jZero (v : ℕ) : ℕ := 49 * v / 100 - 1

/-- **K1, first comparison** -- `02:821--824`: "Since `v >= 192`, direct
expansion gives `10000 j_0(v)^2 <= 2401(v^2 - 2)`".  Proved here under the
weaker hypothesis `v >= 2`, which is never stronger than the frozen one.
General in `v`. -/
theorem k1J49FeasibleBound {v : ℕ} (hv : 2 ≤ v) :
    10000 * jZero v ^ 2 ≤ 2401 * (v ^ 2 - 2) := by
  rcases Nat.eq_zero_or_pos (49 * v / 100) with h0 | hpos
  · have hz : jZero v = 0 := by simp only [jZero, h0]
    simp [hz]
  · have h100 : 100 * jZero v + 100 ≤ 49 * v := by simp only [jZero]; omega
    have hsq : (100 * jZero v + 100) * (100 * jZero v + 100) ≤ 49 * v * (49 * v) :=
      Nat.mul_le_mul h100 h100
    have hv2 : 4 ≤ v ^ 2 := by nlinarith
    have key : 10000 * jZero v ^ 2 + 4802 ≤ 2401 * v ^ 2 := by nlinarith [hsq]
    omega

/-! ### The hard-seed threshold is read at **one** universe, never as a family

`02:799--806` fixes `m_HS` **once**: "Here `m_HS` is the least natural
satisfying the full uniform predicate `HSThreshold` defined with the inherited
contract ... It is selected once and hardwired into the finite code of
`A_cert`".  One hardwired `m_HS` gives one `T` and one `B_s`.

The banked `HardSeedFacade.mHS.{u}` is universe polymorphic exactly as its
inherited declaration is (`D:495--515`), so writing `mHS.{w}` under a fresh
universe binder would expose a *family* of naturals `{m_HS.{w}}` where the
frozen paragraph fixes a single value -- and no universe-invariance theorem for
`HSThreshold` is available on this route to collapse that family.  Accordingly
the five declarations below read the threshold at the **one** universe this
route's carriers inhabit, `Type` (`conv:finite-slots`), and carry **no universe
binder at all**: `T`, `B_s` and the K1 comparisons are single naturals, as
`02:803` requires.  Universe invariance of `HSThreshold` is *not* claimed here;
it is simply never needed, because the value is never read anywhere else. -/

/-- **K1's terminating search for `T`** -- `02:815--819`, "Let `T` be the least
integer with `T >= 64`, `9T^2 - 2 >= m_HS`" (`02:815--817`), "and set
`B_s = T^2`.  This is a terminating search" (`02:819`).  The threshold is the
banked `HardSeedFacade.mHS` read at the single universe `Type` (see the note
above), and the frozen `9T^2 - 2 >= m_HS` is written `m_HS + 2 <= 9T^2` so that
no natural truncated subtraction is introduced. -/
theorem tLeastExists :
    ∃ T : ℕ, 64 ≤ T ∧ HardSeedFacade.mHS.{0} + 2 ≤ 9 * T ^ 2 := by
  refine ⟨HardSeedFacade.mHS.{0} + 64, by omega, ?_⟩
  nlinarith [Nat.zero_le HardSeedFacade.mHS.{0}]

/-- **`T`** -- the least integer of `02:815--817`.  One natural, not a
universe-indexed family. -/
noncomputable def tLeast : ℕ := Nat.find tLeastExists

/-- **`B_s = T^2`** -- `02:819`.  One natural, not a universe-indexed family. -/
noncomputable def bsSched : ℕ := tLeast ^ 2

/-- **Aux K4 (`T` satisfies both defining clauses).**  General. -/
theorem tLeastSpec :
    64 ≤ tLeast ∧ HardSeedFacade.mHS.{0} + 2 ≤ 9 * tLeast ^ 2 :=
  Nat.find_spec tLeastExists

/-- **Aux K5 (`T` is least).**  Nothing below `T` satisfies the two clauses, so
`02:815`'s "least" is carried and not weakened.  General. -/
theorem tLeastMinimal {T : ℕ} (h : T < tLeast) :
    ¬ (64 ≤ T ∧ HardSeedFacade.mHS.{0} + 2 ≤ 9 * T ^ 2) :=
  Nat.find_min tLeastExists h

/-- **K1, second comparison** -- `02:827--828`: "The same integer comparison
gives `j_0(v) >= 20u + 2`", at `v = Tu` with `T >= 64` (`02:817`) and `u >= 3`
(`02:819`).  General in `u`, at the single pinned `T`. -/
theorem k1JZeroGe {u : ℕ} (hu : 3 ≤ u) :
    20 * u + 2 ≤ jZero (tLeast * u) := by
  have hT : 64 ≤ tLeast := tLeastSpec.1
  have hP : 64 * u ≤ tLeast * u := Nat.mul_le_mul hT (le_refl u)
  simp only [jZero]
  omega

/-- **Aux K3 (an exponential-versus-quadratic step).**  `9k^2 < 2^k` for
`k >= 93`, proved from the banked `ScheduleTemplateResidue.sq_le_two_pow`
applied at `k/2`.  This is the arithmetic engine of K1's third comparison, and
both of its numerals are **evaluated**, not chosen: `93 = j_0(192)` is `jZero`
read at the frozen floor `v >= 192` of `02:821`, and the factor `9` is the
square of the `v <= 3 j_0(v)` slope that the same evaluation returns there.
General in `k`. -/
theorem nineSqLtTwoPow {k : ℕ} (hk : 93 ≤ k) : 9 * k ^ 2 < 2 ^ k := by
  have hh5 : 5 ≤ k / 2 := by omega
  have hsq : (k / 2) ^ 2 ≤ 2 ^ (k / 2) :=
    ScheduleTemplateResidue.sq_le_two_pow (by omega)
  have hlin : 4 * (k / 2) + 1 ≤ (k / 2) ^ 2 := by nlinarith
  have hk2 : k ≤ 2 * (k / 2) + 1 := by omega
  have hk2' : k ^ 2 ≤ 4 * (k / 2) ^ 2 + 4 * (k / 2) + 1 := by nlinarith
  have h64 : (2 : ℕ) ^ (k / 2 + 6) = 64 * 2 ^ (k / 2) := by
    rw [pow_add]; ring
  have hlt : (2 : ℕ) ^ (k / 2 + 6) < 2 ^ k :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- **K1, third comparison** -- `02:828--831`: "Finally `2^{j_0(v)} > v^2`".
The frozen proof checks the three residues `v = 192, 193, 194` and then
increases `v` by three; the closed-form route here is the same inequality at
every `v >= 192` and is never weaker.  General in `v`. -/
theorem k1TwoPowJZeroGtSq {v : ℕ} (hv : 192 ≤ v) : v ^ 2 < 2 ^ jZero v := by
  have hk : 93 ≤ jZero v := by simp only [jZero]; omega
  have hv3 : v ≤ 3 * jZero v := by simp only [jZero]; omega
  have h9 := nineSqLtTwoPow hk
  have hsq : v ^ 2 ≤ 9 * jZero v ^ 2 := by nlinarith
  omega

/-- **K1's conclusion about the schedule search** -- `02:826--827`, "so the
definition of `j_49` gives `j_49(T^2 u^2 - 2) >= j_0(v)`".  This is the frozen
maximality eliminator `ParameterSchedule.j49_max` applied to the first
comparison, over the banked `RawLowProfileBody.J49Feasible`; no lower bound on
`j_49` is asserted from an asymptotic claim (`02:1221--1223`).  General. -/
theorem k1J49GeJZero {v : ℕ} (hv : 2 ≤ v) :
    jZero v ≤ ParameterSchedule.j49 (v ^ 2 - 2) :=
  ParameterSchedule.j49_max (k1J49FeasibleBound hv)

/-- **K1 at the paper's own application point** -- `02:819--831`, "For `u >= 3`,
put `v = Tu`", with every source-defined quantity pinned: `T` is the reified
least integer `tLeast`, `j_0` is `jZero`, and `j_49` is the banked
`ParameterSchedule.j49`.  All three displayed comparisons of the frozen
paragraph, read at that point.  General in the frozen free input `u`. -/
theorem k1ScheduledComparisons {u : ℕ} (hu : 3 ≤ u) :
    20 * u + 2 ≤ jZero (tLeast * u) ∧
      (tLeast * u) ^ 2 < 2 ^ jZero (tLeast * u) ∧
      jZero (tLeast * u)
        ≤ ParameterSchedule.j49 ((tLeast * u) ^ 2 - 2) := by
  have hT : 64 ≤ tLeast := tLeastSpec.1
  have hv : 192 ≤ tLeast * u := by
    have := Nat.mul_le_mul hT hu
    omega
  exact ⟨k1JZeroGe hu, k1TwoPowJZeroGtSq hv, k1J49GeJZero (by omega)⟩

/-- **K1's hard-seed floor** -- `02:832--834`, "Hence, for every admissible
`u`, `k_T = T^2 u^2 - 2 >= m_HS`".  Written without truncated subtraction, and
proved from `u >= 3` (`02:819`) together with the defining clause of `T`.
General in `u`, at the single pinned threshold. -/
theorem k1HardSeedFloor {u : ℕ} (hu : 3 ≤ u) :
    HardSeedFacade.mHS.{0} + 2 ≤ bsSched * u ^ 2 := by
  have hspec := tLeastSpec
  have h9 : 9 ≤ u ^ 2 := by nlinarith
  have hstep : 9 * tLeast ^ 2 ≤ tLeast ^ 2 * u ^ 2 := by nlinarith
  simp only [bsSched]
  omega

/-! ### `K2` and `L_P` are consumed by pin -- this module lands **no** `K2` row

**CROSS-MODULE PIN RECONCILIATION.**  `02:855--859` needs `L_P` with no free
binder standing for a source-defined intermediate.  An earlier authoring pass of
this module met that need with a local composite `scheduledLP`, spelling out
`06:471` (`L_P = clog_2 P_0`), `06:467--470` (the six-branch `P_0`) and
`06:295--297` (`U_0 = max{2, b_out/eta_R}`) a second time; that duplicate
reification was deleted in `r2`.  Its replacement -- two `K2` rows stated at the
sibling module's evaluated `ScheduleContext` -- is deleted here, for two
independent reasons, and the module now imports no sibling-tranche schedule
surface at all.

1. **Duplication.**  Both frozen `K2` sentences are already banked verbatim in
   the schedule module and are consumed by pin, not restated:
   `02:855--858` ("for the candidate `k^* = 100 L_P^2`, the exact comparison
   `10000(4L_P)^2 = 160000 L_P^2 <= 240100 L_P^2 = 2401 k^*`") is
   `ParameterSchedule.kref_j49_candidate` at `eq:kref-j49-candidate`
   (`06:615--621`), and `02:858--859` ("gives `j_49(k^*) >= 4 L_P`") is
   `ParameterSchedule.jrefStar_le_j49` at `06:622--624`, proved through the
   same maximality eliminator `j49_max` and never from an asymptotic claim
   (`02:1221--1223`).  Both are general in `L_P`, hence hold at whatever
   evaluated value the schedule chain returns; restating them here added no
   frozen content.
2. **A defective carrier.**  The restatements read `L_P` off the sibling
   module's `ScheduleContext`, whose Stage-1 roots are carried as free record
   fields although `06:239--241`, `06:298--303` and `06:314--316` define them.
   A row consuming a defective interface inherits its defect, so no repair of
   the two rows inside *this* module was available: they are deleted rather
   than re-pinned onto an unrepaired carrier.

Nothing frozen is lost: `L_P`, `P_0`, `U_0`, `eta_R`, `s` and `u` appear in no
statement of this module, free or bound, and `k_ref^*`/`j_49` are read only
through the banked `ParameterSchedule.krefStar` and `.j49`.

The `B_s` used by the schedule chain is the `LevelConfig` field `C.K.Bs`, which
is the discipline this section already states for `K_*` (`02:798--813`): the
tuple is the banked `PublicRecords.LevelConfig` and is not redeclared.  `K1`'s
own closed form for that field, `B_s = T^2` at `02:819`, stays landed above as
`bsSched` and is *not* a second `L_P`; `k1HardSeedFloor` is where it is used. -/

/-- **K3's `C_in`** -- `02:869--871`: "Normalize the finitely many Stage-1
row-extraction ceilings and let `C_in` be the maximum of zero and their emitted
additive binary-loss constants."  The argument is the emitted list, which is
compiler output (`06:1628--1631`, `PARAM-001`) and therefore a free binder. -/
def cIn (losses : List ℕ) : ℕ := losses.foldr max 0

/-- **Aux K6 (the frozen "maximum of zero").**  On no emitted constants,
`C_in = 0`; `def:level-configuration` imposes nothing further on the field
(`PublicRecords.levelConfig_Cin_unconstrained`).  General. -/
theorem cInNil : cIn [] = 0 := rfl

/-- **Aux K7 (`C_in` dominates every emitted constant).**  This is what
`02:871--873` uses: "Consequently `eq:input-depth-request` implies every such
ceiling row".  General in the emitted list. -/
theorem cInGeOfMem : ∀ (losses : List ℕ) (x : ℕ), x ∈ losses → x ≤ cIn losses := by
  intro losses
  induction losses with
  | nil => intro x h; cases h
  | cons a l ih =>
      intro x h
      rcases List.mem_cons.1 h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (ih x h') (le_max_right _ _)

/-- **K4's tested witness exponent** -- `02:881--883`,
`M = C_exc^0 + B_exc^0 + c_seed + 8`, over the banked
`ParameterSchedule.cSeed`.  The two coefficients are first-pass compiler output
and are therefore free binders. -/
def k4M (Cexc0 Bexc0 : ℕ) : ℕ := Cexc0 + Bexc0 + ParameterSchedule.cSeed + 8

/-- **Aux K8 (`02:892--893`, "here `M >= c_seed + 8 = 108`").**  General. -/
theorem k4MGe (Cexc0 Bexc0 : ℕ) : 108 ≤ k4M Cexc0 Bexc0 := by
  simp only [k4M, ParameterSchedule.cSeed]; omega

/-- **K4's nonemptiness comparison** -- `02:887--890`:

```
 C_exc^0 + B_exc^0 (M+1) + 4 <= M + M(M+1) + 4 <= 2^M = A.
```

"The last inequality follows by the elementary induction `M^2 + 2M + 4 <= 2^M`
for `M >= 8`" -- that induction is the banked
`IterationAssembly.sq_le_two_pow`, consumed by pin.  The banked
`IterationAssembly.awrap_search_nonempty` is the search-level statement; this
row is the displayed comparison itself.  General in the two coefficients. -/
theorem k4WitnessBound (Cexc0 Bexc0 : ℕ) :
    Cexc0 + Bexc0 * (k4M Cexc0 Bexc0 + 1) + 4 ≤ 2 ^ k4M Cexc0 Bexc0 := by
  have hM8 : 8 ≤ k4M Cexc0 Bexc0 := le_trans (by norm_num) (k4MGe Cexc0 Bexc0)
  have hC : Cexc0 ≤ k4M Cexc0 Bexc0 := by
    simp only [k4M, ParameterSchedule.cSeed]; omega
  have hB : Bexc0 ≤ k4M Cexc0 Bexc0 := by
    simp only [k4M, ParameterSchedule.cSeed]; omega
  have hstep : Bexc0 * (k4M Cexc0 Bexc0 + 1)
      ≤ k4M Cexc0 Bexc0 * (k4M Cexc0 Bexc0 + 1) := Nat.mul_le_mul hB (le_refl _)
  have hpow : k4M Cexc0 Bexc0 ^ 2 + 2 * k4M Cexc0 Bexc0 + 4 ≤ 2 ^ k4M Cexc0 Bexc0 :=
    IterationAssembly.sq_le_two_pow _ hM8
  calc Cexc0 + Bexc0 * (k4M Cexc0 Bexc0 + 1) + 4
      ≤ k4M Cexc0 Bexc0 + k4M Cexc0 Bexc0 * (k4M Cexc0 Bexc0 + 1) + 4 :=
        Nat.add_le_add (Nat.add_le_add hC hstep) (le_refl 4)
    _ = k4M Cexc0 Bexc0 ^ 2 + 2 * k4M Cexc0 Bexc0 + 4 := by ring
    _ ≤ 2 ^ k4M Cexc0 Bexc0 := hpow

/-- **K4's code-length half** -- `02:886--887`, "one has
`clog_2(A + 2) <= M + 1`" at the tested witness `A = 2^M`.  General in `M`. -/
theorem k4ClogWitness (Cexc0 Bexc0 : ℕ) :
    Nat.clog 2 (2 ^ k4M Cexc0 Bexc0 + 2) ≤ k4M Cexc0 Bexc0 + 1 := by
  have hM : 1 ≤ k4M Cexc0 Bexc0 := le_trans (by norm_num) (k4MGe Cexc0 Bexc0)
  refine Nat.clog_le_of_le_pow ?_
  have h1 : (2 : ℕ) ^ 1 ≤ 2 ^ k4M Cexc0 Bexc0 :=
    Nat.pow_le_pow_right (by norm_num) hM
  have h2 : (2 : ℕ) ^ (k4M Cexc0 Bexc0 + 1) = 2 * 2 ^ k4M Cexc0 Bexc0 := by
    rw [pow_succ]; ring
  simp only [pow_one] at h1
  omega

/-! ## Section 7  The compiler `C1--C8`

`02:905--1120`: "On input `c in N`, execute the following finite program
`Compile(c)`."  All eight steps are landed as a closed roster with the frozen
content of each in its constructor docstring, together with the arithmetic each
step fixes that is expressible without the node graph (GAP-EXPOSED 1, 4). -/

/-- **The eight compiler steps** -- `02:908--1120`, in the frozen print
order. -/
inductive CompilerStep where
  /-- **C1** (`02:909--917`): write the primitive leaves in the inventory order
  `n`, `Public`, `Pi`, the literal trace accessors; append `c`, `K_*` and the
  source constants; tag phases.  "List position does not determine phase." -/
  | c1
  /-- **C2** (`02:918--935`): follow `fig:parameter-order`, append each
  displayed defining expression after all its parents, exclude every real
  logarithm, square root and noninteger real power, share equal exact
  expressions, and give each derived node the maximum phase of its parents. -/
  | c2
  /-- **C3** (`02:936--960`): visit `G` in block and row order and compile each
  comparison to its literal `Eq`/`Le`/`Lt` atom or `Divides` atom; mark exactly
  three target rows `CutoffPending`. -/
  | c3
  /-- **C4** (`02:961--967`): build `Coverage_c` at the same visit, four
  pointers for the ninth block, and "Reject any attempted pointer with a
  different source tag." -/
  | c4
  /-- **C5** (`02:968--1006`): apply the binary-length rules, build and
  validate the leaf/search-endpoint majorant ledger, read each literal
  `TailRuleSpec`, and replace each pending mark by its ordered
  `TailBundle`. -/
  | c5
  /-- **C6** (`02:1007--1046`): normalize each registered `TailTerm`
  auxiliary, emit the `ECut`/`PCut` records, run only the compiler-executed
  `c`-dependent least searches, and emit every successor root with its
  normalized `PCut` argument triple `(2^{d_c} C_u, d_c, e_c)`. -/
  | c6
  /-- **C7** (`02:1047--1107`): form `ScalarOut_c` and `Successor_c` with their
  roots in the frozen order, exclude the raw source and family cardinalities
  and the internal helper `lambda_0`, and store for each root its coefficient,
  normalized inequality and executed `PCut` record. -/
  | c7
  /-- **C8** (`02:1108--1119`): run the mathematical schema checker and output
  the six fields in the frozen order, length-prefixed and canonically coded. -/
  | c8
  deriving DecidableEq, Repr

/-- The eight compiler steps in the frozen print order. -/
def compilerSteps : List CompilerStep :=
  [CompilerStep.c1, CompilerStep.c2, CompilerStep.c3, CompilerStep.c4,
    CompilerStep.c5, CompilerStep.c6, CompilerStep.c7, CompilerStep.c8]

/-- **Aux C3 (the compiler roster is the complete frozen list).**  Eight steps,
no repetition, all present -- "no clause dropped" at the step level.  The
"cannot reject" induction of `02:1130--1138` runs over exactly `C1--C7`.
General. -/
theorem compilerStepsIsTheCompleteRoster :
    compilerSteps.length = 8 ∧ compilerSteps.Nodup ∧
      ∀ s : CompilerStep, s ∈ compilerSteps := by
  refine ⟨rfl, by decide, ?_⟩
  intro s; cases s <;> decide

/-- **The complete cutoff-pending target list** -- C3, `02:946--950`: "Exactly
three target rows are marked `CutoffPending`", repeated at `02:480--482` and
closed at `02:953--954` ("This is the complete target cutoff list"). -/
inductive CutoffPendingTarget where
  /-- The input-depth request, `eq:input-depth-request` (`02:947`). -/
  | inputDepthRequest
  /-- `delta_min |Cols(M_1)| >= 8` (`02:949`). -/
  | stage2DeltaMinCols
  /-- `delta_term |Cols(M_1)| >= 8` (`02:950`). -/
  | stage2DeltaTermCols
  deriving DecidableEq, Repr

/-- The three cutoff-pending targets in the frozen print order. -/
def cutoffPendingTargets : List CutoffPendingTarget :=
  [CutoffPendingTarget.inputDepthRequest, CutoffPendingTarget.stage2DeltaMinCols,
    CutoffPendingTarget.stage2DeltaTermCols]

/-- **Aux C4 (`02:946--954`).**  Exactly three, all distinct, and no fourth --
`02:950--953` adds that the Stage-3 `b_2`-ceiling loss is discharged by a
static implication instead, and that successor comparisons "are not
admissibility targets".  General. -/
theorem cutoffPendingTargetsIsTheCompleteRoster :
    cutoffPendingTargets.length = 3 ∧ cutoffPendingTargets.Nodup ∧
      ∀ t : CutoffPendingTarget, t ∈ cutoffPendingTargets := by
  refine ⟨rfl, by decide, ?_⟩
  intro t; cases t <;> decide

/-- **`d_c = 8(c+1)`** -- `02:1031`, the successor degree. -/
def dcOf (c : ℕ) : ℕ := 8 * (c + 1)

/-- **`e_c = 16(c+1)`** -- `02:1031`, the successor exponent; the same
`16(c+1)` as the `E_{16(c+1)}(n)` target of `02:548--550`. -/
def ecOf (c : ℕ) : ℕ := 16 * (c + 1)

/-- **Aux C5 (the `PCut` persistence premise).**  `02:1308--1309`: "In
`PCut(A,d,e)`, the predicate is `A <= (r+2)^{e-d}`, whose right side is
nondecreasing and unbounded because `e > d`."  Here that strict inequality is
checked at every incoming exponent, so the successor class is never emitted
with a degenerate `e = d`.  General in `c`. -/
theorem dcLtEc (c : ℕ) : dcOf c < ecOf c := by
  simp only [dcOf, ecOf]; omega

/-- **The absorbed successor triple** -- `02:1033--1035` and `02:1096--1099`,
`PCut(2^{d_c} C_u, d_c, e_c)`.  `02:1106--1107` rejects "a degree annotation
without the raw-coefficient row, absorbed cutoff tuple, offset, guard, and
checked conclusion", which is why the coefficient is a component here. -/
def pcutTriple (c Cu : ℕ) : ℕ × ℕ × ℕ := (2 ^ dcOf c * Cu, dcOf c, ecOf c)

/-- **The C6/C7 successor conclusion** -- `02:1100--1105`: "the record is
instantiated at the exact natural index `l(n) - 2`, and
`lem:shifted-pcut-absorption` proves `C_u (l(n)+2)^{8(c+1)} <= l(n)^{16(c+1)}`."
The absorption lemma is the banked `pCut_shifted_certificate`, consumed by pin;
this row is the frozen triple feeding it, with the guard `l(n) >= 4` of
`02:1038--1039` carried as an explicit hypothesis.  General. -/
theorem pcutTripleAbsorbs {c Cu n : ℕ}
    (hell : 4 ≤ IterationAssembly.ellN n)
    (hcut : PCutPred (pcutTriple c Cu).1 (dcOf c) (ecOf c)
      (IterationAssembly.ellN n - 2)) :
    Cu * (IterationAssembly.ellN n + 2) ^ dcOf c
      ≤ IterationAssembly.ellN n ^ ecOf c := by
  refine pCut_shifted_certificate hell ?_
  simpa [pcutTriple, mul_comm] using hcut

/-! ### `lambda_0` is consumed by pin, not reified here

`02:1083--1086` names "the internal rational helper `lambda_0 = q_2 2^{1-b_1}`
...  a typed exact node used only by tail normalization; it is not a public
pre-trace accessor and does not enlarge the 173-root successor manifest."  That
is the *same* quantity the banked `DenseBranchSelection.lambdaZero` already
reifies from `08:796`, `lambda_0 = 2 q_2 2^{-b_1}`, written there as a quotient
with a natural exponent; the two frozen displays are equal term for term, so
this module lands no second `lambda_0` and speaks only about the banked one.
What Section 2 adds is the *reading* discipline of `02:400--403` -- the registry
"never uses natural `Sub`, whose meaning is truncated subtraction" -- and that
is recorded below as a pole about the banked declaration. -/

/-- **Aux C6 (`lambda_0` is positive on a positive source width).**  Stated of
the banked `DenseBranchSelection.lambdaZero`, consumed by pin.  General. -/
theorem lambdaZeroPos {q2 : ℕ} (h : 0 < q2) (b1 : ℕ) :
    0 < DenseBranchSelection.lambdaZero q2 b1 := by
  have hq : (0 : ℝ) < (q2 : ℝ) := by exact_mod_cast h
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b1 := pow_pos (by norm_num) _
  simp only [DenseBranchSelection.lambdaZero]
  positivity

/-- **Statement pole for the pinned `lambda_0` (`02:400--403`).**  The frozen
exponent is not interchangeable with natural truncated subtraction: at
`b_1 = 3` the banked quotient form gives `1/4`, while reading `2^{1-b_1}` with
natural `Sub` gives `2^0 = 1` and hence `q_2`.  This is exactly the confusion
`02:401--403` forbids, exhibited in the kernel against the banked declaration
rather than against a second copy of it.

**BEYOND-PAPER AUDIT** at `(q_2, b_1) = (1, 3)`: a rejection probe claiming no
legality, exhibited only to separate the two readings. -/
theorem lambdaZeroSignedExponentPole :
    DenseBranchSelection.lambdaZero 1 3 = 1 / 4 ∧
      ((1 : ℝ) * (2 : ℝ) ^ ((1 : ℕ) - 3) = 1) := by
  constructor
  · norm_num [DenseBranchSelection.lambdaZero]
  · norm_num

/-! ## Section 8  The static rows `S1--S5`

`02:1228--1300`: "There are no unnamed static lemmas.  The rows in `Static_c`
are instances of the following finite list."  All five are landed as a closed
roster; `S2` and `S4`, whose proofs the frozen source prints in full and which
need no Section-6 display, are **proved**.  See GAP-EXPOSED 5 for `S1`, `S3`
and `S5`. -/

/-- **The five static rows** -- `02:1231--1298`, in the frozen print order. -/
inductive StaticLemma where
  /-- **S1** (`02:1232--1235`): the defining maximality of `j_49` gives
  `eq:j49-window`; monotonicity of `2^x` gives the Stage-1 and hard-seed
  real-power consequences; the block-count and projection consequences are the
  rational calculation following `eq:stage1-projection-ceilings`.
  GAP-EXPOSED 5. -/
  | s1
  /-- **S2** (`02:1236--1253`): the three cover searches, the template,
  protected-mass, low-rung and owner rows, and the product-error row -- the
  Bernoulli and binomial calculation that puts the maximum of
  `eq:epsilon-product` strictly below `1/50`.  Proved below. -/
  | s2
  /-- **S3** (`02:1254--1261`): `eq:tref-search` implies the
  certified-reference logarithmic and real-power rows; `eq:t2-search` implies
  `eq:all-extension-gates`.  GAP-EXPOSED 5. -/
  | s3
  /-- **S4** (`02:1262--1287`): the fixed logarithmic comparison
  `eq:direct-numeric-gate`, with its rational proof from the exponential
  series, and the integration bound `-ln(1-z) <= z/(1-z) <= 1/199`.  Proved
  below. -/
  | s4
  /-- **S5** (`02:1288--1297`): the four implications `ExtDense`, `ExtTwo`,
  `ExtEarly`, `ExtTerminal`, proved uniformly under their universal
  call-domain binders.  GAP-EXPOSED 5. -/
  | s5
  deriving DecidableEq, Repr

/-- The five static rows in the frozen print order. -/
def staticLemmas : List StaticLemma :=
  [StaticLemma.s1, StaticLemma.s2, StaticLemma.s3, StaticLemma.s4,
    StaticLemma.s5]

/-- **Aux S2 (the static roster is the complete frozen list).**  Five rows, no
repetition, all present: `02:1299--1300`, "These cases exhaust the real-valued
clauses of `G`; all other rows are exact integer or rational comparisons."
General. -/
theorem staticLemmasIsTheCompleteRoster :
    staticLemmas.length = 5 ∧ staticLemmas.Nodup ∧
      ∀ s : StaticLemma, s ∈ staticLemmas := by
  refine ⟨rfl, by decide, ?_⟩
  intro s; cases s <;> decide

/-- **S2, lower half of the product-error row** -- `02:1240--1243`: "For
`t = t_2 >= 1` and `x = 1/(100t)`, Bernoulli's inequality gives
`1 - (1-x)^t <= tx = 1/100 < 1/50`."  General in `t`. -/
theorem s2LowerProductError {t : ℕ} (ht : 1 ≤ t) :
    1 - (1 - (1 : ℝ) / (100 * (t : ℝ))) ^ t ≤ 1 / 100 := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htne : (t : ℝ) ≠ 0 := ne_of_gt htpos
  have hxle : (1 : ℝ) / (100 * (t : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hx0 : (0 : ℝ) < 1 / (100 * (t : ℝ)) := by positivity
  have hb := one_add_mul_le_pow (a := -((1 : ℝ) / (100 * (t : ℝ)))) (by linarith) t
  have h100t : (0 : ℝ) < 100 * (t : ℝ) := by linarith
  have hval : (1 : ℝ) + (t : ℝ) * -((1 : ℝ) / (100 * (t : ℝ))) = 1 - 1 / 100 := by
    have hkey : (t : ℝ) / (100 * (t : ℝ)) = 1 / 100 := by
      rw [div_eq_iff (ne_of_gt h100t)]
      ring
    rw [mul_neg, mul_one_div, hkey]
    ring
  have heq : (1 : ℝ) + -((1 : ℝ) / (100 * (t : ℝ)))
      = 1 - (1 : ℝ) / (100 * (t : ℝ)) := by ring
  rw [heq] at hb
  linarith [hb, hval]

/-- **S2, upper half of the product-error row** -- `02:1244--1252`:
"`(1+x)^t - 1 <= sum_{k=1}^t (1/100)^k < sum_{k=1}^inf (1/100)^k = 1/99 <
1/50`."  The frozen bound is transcribed exactly; the proof route here runs
through `(1+x)^t (1-x)^t = (1-x^2)^t < 1` and the Bernoulli half above, which
gives the same strict `1/99` without a series manipulation.  General in `t`. -/
theorem s2UpperProductError {t : ℕ} (ht : 1 ≤ t) :
    (1 + (1 : ℝ) / (100 * (t : ℝ))) ^ t - 1 < 1 / 99 := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  set x : ℝ := 1 / (100 * (t : ℝ)) with hxdef
  have hx0 : (0 : ℝ) < x := by rw [hxdef]; positivity
  have hxle : x ≤ 1 / 100 := by
    rw [hxdef, div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (t : ℝ))]
    nlinarith
  have hlow : (99 : ℝ) / 100 ≤ (1 - x) ^ t := by
    have hs := s2LowerProductError ht
    rw [← hxdef] at hs
    linarith
  have hposp : (0 : ℝ) ≤ (1 + x) ^ t := by positivity
  have hprod : (1 + x) ^ t * (1 - x) ^ t = (1 - x ^ 2) ^ t := by
    rw [← mul_pow]; congr 1; ring
  have hpowlt : ∀ (n : ℕ), 1 ≤ n → ∀ a : ℝ, 0 ≤ a → a < 1 → a ^ n < 1 := by
    intro n
    induction n with
    | zero => intro h; exact absurd h (by norm_num)
    | succ n ih =>
        intro _ a h0 h1
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using h1
        · have hprev := ih hn a h0 h1
          rw [pow_succ]
          nlinarith [pow_nonneg h0 n]
  have hlt1 : (1 - x ^ 2) ^ t < 1 := hpowlt t ht _ (by nlinarith) (by nlinarith)
  have hstep : (1 + x) ^ t * ((99 : ℝ) / 100) < 1 := by
    calc (1 + x) ^ t * ((99 : ℝ) / 100) ≤ (1 + x) ^ t * (1 - x) ^ t :=
          mul_le_mul_of_nonneg_left hlow hposp
      _ = (1 - x ^ 2) ^ t := hprod
      _ < 1 := hlt1
  nlinarith [hstep, hposp]

/-! **S2's conclusion** -- `02:1252--1253`, "Thus the maximum in
`eq:epsilon-product` is strictly below `1/50` without using that inequality as a
premise" -- lands **no declaration here**.  It is the banked
`TerminalTwoStream.epsProd_lt_fiftieth` (`eq:epsilon-product`, `06:851--857`),
proved for every positive width, and the fixed-interface discipline forbids a
second copy: the two `s2` bounds above are the frozen `02:1240--1252` half-steps
that this module owns, and the conclusion is consumed by pin. -/

/-- **S4, first rational bound** -- `02:1264--1269`: "the positive-term
exponential series gives `e^{7/10} > 12013/6000 > 2`, hence `ln 2 < 7/10`." -/
theorem s4LogTwoLt : Real.log 2 < 7 / 10 :=
  lt_trans Real.log_two_lt_d9 (by norm_num)

/-- **S4, second rational bound** -- `02:1269--1276`: "`e^{1/2} < 2849/1728 <
5/3`, and `ln(5/3) > 1/2`." -/
theorem s4LogFiveThirdsGt : (1 : ℝ) / 2 < Real.log (5 / 3) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith [he, h1, hpos]

/-- **S4's fixed comparison** -- `02:1276--1281`: "Since `3/199 < 1/50`, it
follows that `3/199 + (7/5) ln 2 < 1/50 + 49/50 = 1 < 2 ln(5/3) = -2 ln(3/5)`.
" -/
theorem s4FixedComparison :
    (3 : ℝ) / 199 + (7 / 5) * Real.log 2 < 1 ∧ (1 : ℝ) < 2 * Real.log (5 / 3) :=
  ⟨by linarith [s4LogTwoLt], by linarith [s4LogFiveThirdsGt]⟩

/-- **S4's integration bound** -- `02:1281--1285`: "For `0 <= z <= 1/200`,
integrating `1/(1-t) <= 1/(1-z)` on `[0,z]` gives `-ln(1-z) <= z/(1-z) <=
1/199`."  General in `z`. -/
theorem s4NegLogOneSubLe {z : ℝ} (_hz0 : 0 ≤ z) (hz : z ≤ 1 / 200) :
    -Real.log (1 - z) ≤ 1 / 199 := by
  have hz1 : (0 : ℝ) < 1 - z := by linarith
  have hne : (1 : ℝ) - z ≠ 0 := ne_of_gt hz1
  have hinvpos : (0 : ℝ) < (1 - z)⁻¹ := inv_pos.mpr hz1
  have h3 : Real.log (1 - z)⁻¹ ≤ (1 - z)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_inv] at h3
  have hkey : (1 : ℝ) ≤ (1 - z) * (200 / 199) := by nlinarith
  have hinv : (1 - z)⁻¹ ≤ 200 / 199 := by
    calc (1 - z)⁻¹ = 1 * (1 - z)⁻¹ := by ring
      _ ≤ ((1 - z) * (200 / 199)) * (1 - z)⁻¹ :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hinvpos)
      _ = 200 / 199 := by field_simp
  linarith

/-! ## Section 9  `eq:pre-input-envelope`

`02:741--758` prints the "literal ordered conjunction" in full and `02:761--762`
closes it: "Equation `eq:pre-input-envelope`, equivalently items (i)--(ii) in
their literal conjunction order, is the promised complete definition."  All
seventeen conjuncts are carried, in the frozen order, with no clause
dropped. -/

/-- **`c_eps = c_D + 2`** -- `eq:literal-source-size-constants`
(`14-final-consequence.tex`, display `14:1453--1457`, the middle identity at
`14:1455`): "Set `A_size = A_0 + 3bc + 2`, `c_eps = c_D + 2`,
`n_eps = 2^{2A_size}`", and `14:1462--1464` names these "the promised literal
values of `c_eps, Delta_eps, gamma_eps, n_eps`".

The argument `c_D` is the fixed exponent of the **cited** Dinur short-PCP
adapter, `thm:dinur-adapter` (`14:689--698`): "There are fixed integers
`A_D, d_D, C_D, c_D, r_D >= 1` ... `size(H) <= C_D L (log_2(L+2))^{c_D}`".  The
frozen source asserts that those integers exist and never prints a value, so
`c_D` is a cited external interface: it enters as an explicit named argument,
exactly as the cited expander family does elsewhere on this route, and this
module declares no axiom for it.  `c_eps` itself is **not** free anywhere
below. -/
def cEpsOf (cD : ℕ) : ℕ := cD + 2

/-- **Aux I0 (the defining identity, and the floor it inherits).**  `14:1455`
read back, together with `c_D >= 1` of `14:692` giving `c_eps >= 3`; so the
evaluated exponent is never the degenerate `0` a free binder would allow.
General in `c_D`. -/
theorem cEpsOf_eq_and_ge {cD : ℕ} (h : 1 ≤ cD) : cEpsOf cD = cD + 2 ∧ 3 ≤ cEpsOf cD :=
  ⟨rfl, by simp only [cEpsOf]; omega⟩

/-- **`InputEnvelope^pre_c(n, Public)`** -- `eq:pre-input-envelope`
(`02-mechanical-contract.tex`, label line 757, display lines 741--758), the
literal ordered conjunction, verbatim and complete.

`B(n)` is the banked `IterationAssembly.depthB`, pinned rather than bound,
because `02:170` defines it (`B(n) = E_2(n)`); the frozen conjunct
`B(n) = E_2(n)` is nevertheless kept in place so that no clause is dropped, and
`inputEnvelopePreClause11IsDischarged` records that our reification discharges
it.  `02:759--762` is respected: looplessness, non-isolation, degree bounds,
nonempty carriers, `D >= 3` and `Y <= D` come from the public-input type and
are **not** repeated here.  `02:762--764`: "No branch assertion, protocol fact,
or desired lower bound occurs in this list" -- and none does.

**`02:763--764` is the reason the predicate takes the record and not a scalar
tuple**: "It depends only on `n` and `Public`".  `N_V` and `N_E` are the two
carrier cardinalities of the public input's endpoint graph, and `m_R`, `n_R`,
`D`, `Y`, `b_0`, `bout`, `Delta`, `gamma` are its own fields; the r0/r1 form of
this predicate accepted them as ten unrelated naturals and two unrelated
rationals, which is the defect repaired in `r2`.

**`c_eps` is evaluated, never bound** (the `r3` repair).  The `r2` form took
`cEps` as a free natural; `14:1454--1456` *defines* it,
`c_eps = c_D + 2`, so this predicate takes the cited adapter's exponent `c_D`
and reads `cEpsOf cD` in conjuncts 3 and 4.  Only `c`, `n`, `c_D`, `Delta_eps`
and `gamma_eps` remain binders: the incoming exponent, the source size, the
cited-adapter exponent of `thm:dinur-adapter` (`14:689--692`), and the two
remaining fixed source constants of `thm:encoded-source-package`
(`02:571--573`). -/
def InputEnvelopePre {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (c n cD : ℕ) (P : PublicRecords.LevelPublicInput V E)
    (Deltaeps : ℕ) (gammaeps : ℚ) : Prop :=
  1 ≤ n ∧
  n ≤ Fintype.card E ∧
  (Fintype.card V : ℝ) ≤ (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ cEpsOf cD ∧
  (Fintype.card E : ℝ) ≤ (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ cEpsOf cD ∧
  P.Δ = Deltaeps ∧
  P.γ = gammaeps ∧
  2 ≤ P.mR ∧
  2 ≤ P.nR ∧
  P.b₀ = IterationAssembly.depthB n ∧
  P.bout = IterationAssembly.depthB n ∧
  IterationAssembly.depthB n = IterationAssembly.envE 2 n ∧
  Nat.clog 2 P.mR ≤ IterationAssembly.envE c n ∧
  Nat.clog 2 P.nR ≤ IterationAssembly.envE c n ∧
  P.D ≤ IterationAssembly.envE c n ∧
  P.Y ≤ IterationAssembly.envE c n ∧
  P.b₀ ≤ IterationAssembly.envE c n ∧
  P.bout ≤ IterationAssembly.envE c n

/-- **Aux I1 (the eleventh conjunct is discharged, not assumed).**  `02:750`
prints `B(n) = E_2(n)`; pinning `B` to the banked `IterationAssembly.depthB`
makes that conjunct hold by the banked definition, so keeping it in the list
costs nothing and drops no clause.  General in `n`. -/
theorem inputEnvelopePreClause11IsDischarged (n : ℕ) :
    IterationAssembly.depthB n = IterationAssembly.envE 2 n := rfl

/-- **Hypothesis-consistency receipt: `c >= 2` is forced, never chosen.**

Conjunct 9 (`b_0 = B(n)`, `02:750`) and conjunct 16 (`b_0 <= E_c(n)`,
`02:755`) together force `E_2(n) <= E_c(n)`, and at `l(n) >= 3`
(`IterationAssembly.ellN_spec`, `step:I-10`) that forces `c >= 2`.  So the
frozen envelope is not satisfiable at `c <= 1` for any positive source size:
the non-vacuity instance below does not assume a convenient exponent, it
inherits the one the frozen list already fixes.  General in `c` and `n`. -/
theorem inputEnvelopePreForcesTwoLeC {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {c n cD : ℕ} {P : PublicRecords.LevelPublicInput V E}
    {Deltaeps : ℕ} {gammaeps : ℚ}
    (h : InputEnvelopePre c n cD P Deltaeps gammaeps) : 2 ≤ c := by
  obtain ⟨hn, -, -, -, -, -, -, -, hb0, -, -, -, -, -, -, hb0le, -⟩ := h
  have hell : 3 ≤ IterationAssembly.ellN n := (IterationAssembly.ellN_spec n hn).2.2
  by_contra hc
  have hcle : c ≤ 1 := by omega
  have hstep : IterationAssembly.ellN n ^ c < IterationAssembly.ellN n ^ 2 := by
    calc IterationAssembly.ellN n ^ c ≤ IterationAssembly.ellN n ^ 1 :=
          Nat.pow_le_pow_right (by omega) hcle
      _ < IterationAssembly.ellN n ^ 2 :=
          Nat.pow_lt_pow_right (by omega) (by omega)
  have hlt : IterationAssembly.envE c n < IterationAssembly.depthB n := by
    simp only [IterationAssembly.envE, IterationAssembly.depthB]
    exact Nat.pow_lt_pow_right (by norm_num) hstep
  rw [hb0] at hb0le
  omega

/-- **An actual public input at every source size** -- `r` disjoint copies of
the triangle `K_3`, taken through the banked `EndpointGraph.copies` of
`04:196--204`, which is the same `r`-copies family the banked
`GuardedSourceGraph` non-vacuity section uses.

**What this is not.**  The frozen source adapter of `04:195--206` outputs `r`
copies of `G^+ = G_0 + K_2` at its own `r = max{1, ceil(n/(m_0+1))}`; this
declaration does **not** claim to be that output, and nothing below reads a
promise branch off it.  It is a legal `LevelPublicInput` exhibited so that
`InputEnvelopePre` is inhabited at a genuine public record rather than at a
scalar tuple -- the fidelity question for `eq:pre-input-envelope`, whose own
text (`02:763--764`) says the predicate "depends only on `n` and `Public`".

Every field value is the paper's own floor, not ours: `m_R = n_R = 2` is the
frozen minimum of `02:749` (and `02:768--769`, "The full-cube seed has both
carrier sizes at least two"); `D = 3` is the frozen `D >= 3` of `02:760` and
`Y = D = 3` its `Y <= D`; `b_0 = bout = B(n)` is conjuncts 9--10 of
`eq:pre-input-envelope` read at the banked `IterationAssembly.depthB`; and the
degree bound `2 <= Delta_eps` is the source's own bounded-degree constant, which
`P2`'s `SourceCommon` requires and `K_3` meets exactly.

The source relation `R` is the constantly-`false` matrix: `eq:pre-input-envelope`
mentions no clause about `R`, so a choice here claims nothing.  That single
field is **BEYOND-PAPER AUDIT**; every other field is source-anchored above. -/
def sourcePublicInput (r : ℕ) (hr : 0 < r) (Deltaeps : ℕ) (hΔ : 2 ≤ Deltaeps)
    (gammaeps : ℚ) (hγ0 : 0 < gammaeps) (hγ1 : gammaeps ≤ 1) :
    PublicRecords.LevelPublicInput (Fin r × Fin 3) (Fin r × Fin 3) where
  G := GuardedSourceGraph.K3.copies r hr
  γ := gammaeps
  Δ := Deltaeps
  Δpos := by omega
  γpos := hγ0
  γle := hγ1
  common := by
    refine ⟨by omega, ?_⟩
    rintro ⟨cc, v⟩
    rw [GuardedSourceGraph.EndpointGraph.degree_copies,
      GuardedSourceGraph.k3_degree v]
    exact ⟨by norm_num, hΔ⟩
  mR := 2
  nR := 2
  mRpos := by norm_num
  nRpos := by norm_num
  R := fun _ _ => false
  D := 3
  Y := 3
  Dge := le_refl 3
  YleD := le_refl 3
  b₀ := IterationAssembly.depthB (r * 3)
  bout := IterationAssembly.depthB (r * 3)
  b₀pos := by
    simp only [IterationAssembly.depthB, IterationAssembly.envE]
    positivity
  boutpos := by
    simp only [IterationAssembly.depthB, IterationAssembly.envE]
    positivity

/-- **Non-vacuity of `InputEnvelopePre` at an actual public input.**

This is a **general family**, not a single probe: for every copy count
`r >= 1` it inhabits the envelope at the source size `n = 3r`, at every legal
incoming exponent `c >= 2`, and at every legal pair of fixed source constants.
The exponent hypothesis `2 <= c` is the one `inputEnvelopePreForcesTwoLeC` shows
the frozen list already forces.  `c_eps` is **not** a binder here: the family is
indexed by the cited-adapter exponent `c_D` of `14:689--692`, and the envelope
reads the evaluated `cEpsOf c_D = c_D + 2` of `14:1455`.  So the instance is
legal at every `c_D` the cited adapter can supply, including the frozen floor
`c_D = 1`, and nothing in it is a value of ours.

Because the predicate now reads its data out of `LevelPublicInput`, this is
legality at a genuine public record: `N_V` and `N_E` are the *carrier
cardinalities of that record's graph*, not two naturals chosen to satisfy the
displayed inequalities. -/
theorem inputEnvelopePreNondegenerate {c cD r : ℕ} (hc : 2 ≤ c) (hr : 0 < r)
    {Deltaeps : ℕ} (hΔ : 2 ≤ Deltaeps) {gammaeps : ℚ} (hγ0 : 0 < gammaeps)
    (hγ1 : gammaeps ≤ 1) :
    InputEnvelopePre c (r * 3) cD
      (sourcePublicInput r hr Deltaeps hΔ gammaeps hγ0 hγ1) Deltaeps gammaeps := by
  set n := r * 3 with hn_def
  have hn : 1 ≤ n := by omega
  have hcardV : Fintype.card (Fin r × Fin 3) = n := by
    simp [hn_def, Fintype.card_prod]
  have hell : 3 ≤ IterationAssembly.ellN n := (IterationAssembly.ellN_spec n hn).2.2
  have hexp : 2 ≤ IterationAssembly.ellN n ^ c := by
    have h1 : (3 : ℕ) ^ 2 ≤ (3 : ℕ) ^ c := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : (3 : ℕ) ^ c ≤ IterationAssembly.ellN n ^ c := Nat.pow_le_pow_left hell c
    have h3 : (3 : ℕ) ^ 2 = 9 := by norm_num
    omega
  have hbig : 4 ≤ IterationAssembly.envE c n := by
    have h : (2 : ℕ) ^ 2 ≤ 2 ^ (IterationAssembly.ellN n ^ c) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    simpa [IterationAssembly.envE] using h
  have hdep : IterationAssembly.depthB n ≤ IterationAssembly.envE c n := by
    simp only [IterationAssembly.depthB, IterationAssembly.envE]
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by omega) hc)
  have hclog : Nat.clog 2 2 = 1 := by norm_num
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmono : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogb : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
    rw [Real.logb, le_div_iff₀ hlog2pos]
    linarith
  have honepow : ∀ (k : ℕ) (a : ℝ), 1 ≤ a → 1 ≤ a ^ k := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
        intro a ha
        rw [pow_succ]
        nlinarith [ih a ha]
  have hpow : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) ^ cEpsOf cD :=
    honepow (cEpsOf cD) _ hlogb
  have hsrc : (n : ℝ) ≤ (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ cEpsOf cD := by
    nlinarith
  refine ⟨hn, by rw [hcardV], ?_, ?_, rfl, rfl, le_refl 2, le_refl 2, rfl, rfl,
    rfl, ?_, ?_, ?_, ?_, hdep, hdep⟩
  · rw [hcardV]; exact hsrc
  · rw [hcardV]; exact hsrc
  · change Nat.clog 2 2 ≤ _
    rw [hclog]; omega
  · change Nat.clog 2 2 ≤ _
    rw [hclog]; omega
  · change (3 : ℕ) ≤ _
    omega
  · change (3 : ℕ) ≤ _
    omega

/-! ## Section 10  `clm:eff-ledger-prebuilder`

`02:1140--1161`: "Fix `c, n`, the public input, and `K_*`, but do not choose
`N_2` or `c_2`. ...  exact evaluation of the `pre` slice halts and returns
`q_2 >= 4 t_2`, `t_2 >= 16`, `eps_2 = 1/(100 t_2)`, `m_1 = |Rows(M_1)| > 0`,
together with the positive integer `B_bal(q_2, t_2, m_1)`."  The evaluation
itself needs the node interpreter (GAP-EXPOSED 1); what is landed here is the
claim's conclusion bundle, its legality consequence, and the closed
pre-builder search table of `02:1178--1203`. -/

/-- **A scalar-postcondition helper -- NOT `clm:eff-ledger-prebuilder`.**

`02:1142--1160` states an *implication about an evaluation*: "If
`TypeFacts^pre(n, Public, K_*)`, `InputEnvelope^pre_c(n, Public)`, and
`n >= n_step(c)` hold, **exact evaluation of the `pre` slice halts and
returns**" the four displayed scalars together with `B_bal(q_2, t_2, m_1)`.
This declaration represents **none** of that operative content: it has no
hypothesis, no evaluation relation, and no halting statement.  It is only the
displayed *postcondition conjunction* read off already-constructed objects, and
its name says so (the `r2` name `PreBuilderReturnedScalars` claimed the
returning, which is the defect repaired here).

The four clauses are `02:1148--1152` in the frozen print order, read **at the
objects the claim displays them for** rather than at four unrelated numbers.

`q_2` and `t_2` are the two Stage-2 dyadic widths (`eq:stage2-balance-ceilings`),
`eps_2` is the banked `StageTwoRelaxed.epsTwo` (`eq:epsilon-product`), and `m_1`
is `|Rows(M_1)|` of the actual Stage-1 matrix, read through the banked
`BridgeOutputEquality.rowsCard`.  The r0/r1 form of this predicate accepted
`q_2, t_2, m_1, eps_2` as free scalars satisfying the returned inequalities;
`02:1150` **defines** `eps_2 = 1/(100 t_2)` and `02:1151` **defines**
`m_1 = |Rows(M_1)|`, so neither may be a free binder, and the two width
inequalities are properties of the widths rather than hypotheses on numbers.

**MIGRATED (`cc-t6x`).**  Until this round `q_2` and `t_2` were read off a
*free* `StageTwoRelaxed.StageTwoWidths` binder -- which closed the
free-*scalar* defect the r2 rename repaired, but left the whole predicate
quantified over stored records no schedule produces.  The binder is replaced by
`(C, hgate)` and all three width-derived clauses are read at the banked bridge
`DerivedWidths.toStoredAt.{0} hgate`, whose `q₂` and `t₂` are the derived
accessors `DerivedWidths.q2At C` and `.t2At C` evaluated from `C`'s own intake.
The fourth `WidthGateCore` conjunct is *not* imported into this predicate -- the
bundle is still exactly the four displayed facts of `02:1148--1152`, no more.

**`m_1` PINNED (`cc-t6x-r1`).**  The `r0` bytes still read `m_1` off a free
matrix binder `M₁ : X₁ → Y₁ → Bool` over arbitrary finite carriers, which is
precisely what `05:167--170` forbids ("already determined by these accessors and
the equations in `sec:one-level`") and what `05:336--337` supplies a constructor
call for.  The binder, its two carriers and their `Fintype` instances are gone;
the fourth clause now reads `0 < rowsCard (stageOneAt C)`, the row count of the
Stage-1 matrix this context determines.  Unlike the three width clauses this one
is **gate-free** on its own -- see `rowsCard_stageOneAt_pos` -- and it stays in
this bundle only because `02:1148--1152` prints it as one of the four returned
facts.

*Why this predicate keeps `hgate` while `FamilySizeGuard` does not.*  Two of the
four clauses, `4 t_2 <= q_2` and `16 <= t_2` (through `5 <= k_2`), are literally
two of `WidthGateCore`'s own conjuncts as facts about the presented record;
there is no gate-free reading of them at `q2At C` / `t2At C`.  The family-size
guard, by contrast, only *names* the two widths, so its body needs no gate.

**CORRECTED SUBJECT (`cc-t6x-r2`), fourth conjunct.**  `hgate` constrains only
derived accessors and never `C.W`, so it did not repair the stored-`r_2`
dependence inside the `r1` `stageOneAt C`; the fourth conjunct now asserts
positivity of the **corrected** derived Stage-1 matrix's row count.  The three
width clauses are untouched, the bundle is still exactly the four displayed facts
of `02:1148--1152`, and no clause was added or weakened.

**GAP-EXPOSED (the whole claim).**  What is *not* landed is the claim itself --
its three hypotheses `TypeFacts^pre`, `InputEnvelope^pre_c` and
`n >= n_step(c)` (`02:1144--1146`), and its operative conclusion "exact
evaluation of the `pre` slice halts and returns" (`02:1146--1147`) -- which
needs the node interpreter of `02:425--444` (GAP-EXPOSED 1).  That obligation
is registered and deferred; nothing below is offered as evidence for it, and
`preBuilderScalarPostconditionsHold` proves only that the displayed scalar
facts hold of the banked objects. -/
def PreBuilderScalarPostconditions {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E)
    (hgate : Section5Admissibility.DerivedWidths.WidthGateCore.{0} C) : Prop :=
  4 * (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂
      ≤ (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂ ∧
    16 ≤ (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂ ∧
    StageTwoRelaxed.epsTwo
        (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate)
      = 1 / (100
        * ((Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂ : ℝ)) ∧
    0 < BridgeOutputEquality.rowsCard (stageOneAt C)

/-- **The four displayed scalar facts hold at every level** -- `02:1148--1152`.

Three of them are *theorems about the banked objects*, not hypotheses:
`4 t_2 <= q_2` is the width record's own `four_t₂_le_q₂`, `16 <= t_2` follows
from `5 <= k_2` (through `m_HS >= 5`), and `eps_2 = 1/(100 t_2)` is the banked
definition.  The only residue is `m_1 > 0`, which is exactly the nonemptiness of
the Stage-1 row carrier that `02:1151` asserts.  This says nothing about
evaluation or halting.

**MIGRATED (`cc-t6x`).**  "The banked objects" are now the context's own derived
widths: the three width facts are the banked `StageTwoWidths` theorems
`four_t₂_le_q₂` and `five_le_k₂` and the banked `epsTwo` definition, all read at
`DerivedWidths.toStoredAt.{0} hgate`, with their arguments not re-run.

**The `[Nonempty X₁]` repair (`cc-t6x-r1`).**  The `r0` bytes discharged the
fourth clause from an *assumed* `[Nonempty X₁]` instance on a free row carrier.
That is an assumption the paper does not make: `02:1151` displays `m_1` as
`|Rows(M_1)|` of the matrix the constructor produced, and its positivity is
derived from `q_1 > 0` and `m_R > 0` (`P3`).  The instance, the carriers and the
matrix binder are gone; the clause is now discharged by
`rowsCard_stageOneAt_pos`, consumed by pin.

**The honest cost, unchanged and not concealed.**  The pre-migration form held
at *every* `StageTwoWidths`, so `StageTwoRelaxed.widthsWitness` inhabited the
displayed scalar region unconditionally; this one is conditional on `hgate`,
whose canonical inhabitation is the OPEN, REGISTERED `S5-LEVEL-STEP` row.
Nothing here manufactures a context.  (`successorRowFamilySizeGuardAtMajorant`
no longer shares this cost -- see its `cc-t6x-r1` note.)

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The fourth conjunct is still discharged by
`rowsCard_stageOneAt_pos`, consumed by pin; that lemma now concerns the corrected
derived Stage-1 matrix, so the proof text is unchanged and the fact proved is the
paper's.  The three width proofs are untouched.

General in the two carriers, the context and the gate proof. -/
theorem preBuilderScalarPostconditionsHold {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (C : Section5Admissibility.ScheduleContext V E)
    (hgate : Section5Admissibility.DerivedWidths.WidthGateCore.{0} C) :
    PreBuilderScalarPostconditions C hgate := by
  refine ⟨(Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).four_t₂_le_q₂,
    ?_, rfl, rowsCard_stageOneAt_pos C⟩
  have hk : 5 ≤ (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).k₂ :=
    (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).five_le_k₂
  calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).k₂ :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂ := rfl

/-- **The builder-legality consequence of the scalar postconditions** --
`02:1158--1160`, "In particular `(q_2, t_2, m_1)` is a legal input to the
builder in `eq:effective-balanced-builder`; this conclusion has no
balanced-family hypothesis."

The legality of a builder input is exactly positivity of the three arguments
(`02:179`, "For positive integers `q, t, m`"), and the last displayed quantity
of the claim, `B_bal(q_2, t_2, m_1)`, is positive by the banked
`ScheduleMajorantResidue.bBal_pos`, consumed by pin.  No balanced-family
hypothesis is used, exactly as the frozen sentence insists.

This is the frozen sentence's *arithmetic* content only: the frozen "In
particular" is drawn from the evaluation conclusion, which is GAP-EXPOSED 1, so
this lemma draws it instead from the scalar-postcondition helper.

**MIGRATED (`cc-t6x`), `m_1` PINNED (`cc-t6x-r1`).**  The legal triple is now
the context's own `(q_2, t_2, m_1)` -- the two widths read at
`DerivedWidths.toStoredAt.{0} hgate`, `m_1` at the context's own Stage-1 matrix
-- rather than two read off a free stored record and one off a free matrix.  `C`
and `hgate` stay implicit for exactly the reason `W` was: the hypothesis `h`
determines both.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The logical extraction from the scalar
conjunction is unchanged; the `m_1` it extracts and the `B_bal` endpoint it
builds now carry the corrected derived Stage-1 row count, so the frozen
`02:1158--1160` triple `(q_2, t_2, m_1)` is the paper's at every context.  No
balanced-family hypothesis is used, as the frozen sentence insists.

General. -/
theorem preBuilderLegalBuilderInput {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {C : Section5Admissibility.ScheduleContext V E}
    {hgate : Section5Admissibility.DerivedWidths.WidthGateCore.{0} C}
    (h : PreBuilderScalarPostconditions C hgate) :
    0 < (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂ ∧
      0 < (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂ ∧
      0 < BridgeOutputEquality.rowsCard (stageOneAt C) ∧
      0 < ScheduleMajorantResidue.bBal
        (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂
        (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂
        (BridgeOutputEquality.rowsCard (stageOneAt C)) := by
  obtain ⟨hq, ht, -, hm⟩ := h
  exact ⟨by omega, by omega, hm,
    ScheduleMajorantResidue.bBal_pos
      (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂
      (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂
      (BridgeOutputEquality.rowsCard (stageOneAt C))⟩

/-! **`preBuilderScalarPostconditionsAtBankedWidths`: DELETED at `cc-t6x`, and
the deletion is judged rather than silent.**

The predecessor read "the displayed scalar region is nonempty on this route:
`StageTwoRelaxed.widthsWitness` is the banked Stage-2 width record, and any
Stage-1 matrix over a nonempty row carrier completes it", and its proof was
`preBuilderScalarPostconditionsHold _ _`.

Under the `cc-t6x` migration the helper's width argument is no longer a record
but the context's own bridge, so the migrated statement would read
`forall C hgate, PreBuilderScalarPostconditions C hgate` -- which is
`preBuilderScalarPostconditionsHold`, argument for argument, with a different
name.  Banking it would bank a renamed duplicate; the campaign has paid for that
shape five times (`cc-t5i`, `cc-t5j`, `cc-t5m`, `cc-t5x`, `cc-t5z`).  It is
**deleted**, and its `#print axioms` row is deleted with it.

What is lost is stated rather than absorbed: the predecessor's inhabitant was
*unconditional*, and no unconditional inhabitant of the migrated helper exists
until a context clears `WidthGateCore` (the OPEN, REGISTERED `S5-LEVEL-STEP`
row).  Deleting the declaration does not create that gap -- the migration does --
and keeping a renamed duplicate would not have closed it. -/

/-- **Statement pole for the `02:1151` positivity clause.**  `02:1151` displays
`m_1 = |Rows(M_1)| > 0` and not merely `m_1 >= 0`, so the clause has teeth: a
matrix over an *empty* row carrier refutes it.  This is what a trivial witness
would have to defeat, and it is the reason `rowsCard_stageOneAt_pos` is a
theorem with content rather than a restatement.

**BEYOND-PAPER AUDIT** in every value.  `Fin 0` and `Fin 1` are **ours**, not the
paper's: `P3` (`05:13--52`) fixes `m_R > 0` and `n_R > 0`, so `Rows(M_1)` is
never empty at any legal input, and the paper never visits this point.  The
declaration therefore claims **no legality** -- it is a rejection probe showing
that the guard fires on illegal input, which is strictly weaker evidence than
the paper's own application site and never a substitute for it.

**REPLACED (`cc-t6x-r1`), and the over-claim withdrawn.**  The `r0` form was
`forall C hgate, ¬ PreBuilderScalarPostconditions C hgate (empty matrix)`, whose
docstring said it "loses nothing to the gate".  That sentence was wrong and is
**deleted**: a `forall`-over-`hgate` statement is vacuously true while
`WidthGateCore` inhabitation is the OPEN `S5-LEVEL-STEP` row, so as a *pole* it
established nothing.  Worse, after `m_1` is pinned to `stageOneAt C` the empty
row carrier is not even expressible inside the bundle -- the bundle no longer
has a matrix slot.  The pole is therefore restated where its content actually
lives: gate-free, context-free, and about the `02:1151` clause itself.  It is a
closed statement with no universal quantifier, so no instantiation can make it
vacuous. -/
theorem rowPositivityRejectsEmptyRowCarrier :
    ¬ (0 < BridgeOutputEquality.rowsCard
        (fun (_ : Fin 0) (_ : Fin 1) => false)) := by
  simp [BridgeOutputEquality.rowsCard]

/-- **Aux X.4 (the migrated legality, at the derived accessors).**

`02:1158--1160`'s legal triple, spelled at `DerivedWidths.q2At C` and
`.t2At C` rather than at the bridge record's fields.  This is the form a
downstream schedule consumer needs -- it mentions no `StageTwoWidths` at all --
and it is what makes the migration usable rather than merely correct.

The two field identities are the banked `toStoredAt_fields` (fifth clause, itself
proved through `q₂_eq_two_pow_r₂` and not by `rfl`) and the banked
`t2At_eq_two_pow_k2At` at the bridge's own `k₂`; the legality itself is
`preBuilderLegalBuilderInput`, consumed by pin and not re-derived.

**CORRECTED SUBJECT (`cc-t6x-r2`).**  The `q2At`/`t2At` transport was already
right; what it transports is now the corrected `m_1`, so every Stage-1
row-count occurrence in the transported triple is the derived one.  Both width
identities are untouched.

General in the two carriers, the context and the gate proof.  PROVED. -/
theorem preBuilderLegalBuilderInputAtDerivedWidths {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    {C : Section5Admissibility.ScheduleContext V E}
    {hgate : Section5Admissibility.DerivedWidths.WidthGateCore.{0} C}
    (h : PreBuilderScalarPostconditions C hgate) :
    0 < Section5Admissibility.DerivedWidths.q2At C ∧
      0 < Section5Admissibility.DerivedWidths.t2At.{0} C ∧
      0 < BridgeOutputEquality.rowsCard (stageOneAt C) ∧
      0 < ScheduleMajorantResidue.bBal
        (Section5Admissibility.DerivedWidths.q2At C)
        (Section5Admissibility.DerivedWidths.t2At.{0} C)
        (BridgeOutputEquality.rowsCard (stageOneAt C)) := by
  have hq : (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).q₂
      = Section5Admissibility.DerivedWidths.q2At C :=
    (Section5Admissibility.DerivedWidths.toStoredAt_fields.{0} hgate).2.2.2.2
  have ht : (Section5Admissibility.DerivedWidths.toStoredAt.{0} hgate).t₂
      = Section5Admissibility.DerivedWidths.t2At.{0} C := by
    rw [Section5Admissibility.DerivedWidths.t2At_eq_two_pow_k2At,
      StageTwoRelaxed.StageTwoWidths.t₂,
      (Section5Admissibility.DerivedWidths.toStoredAt_fields.{0} hgate).1]
  have hlegal := preBuilderLegalBuilderInput h
  rw [hq, ht] at hlegal
  exact hlegal

/-- **The nine pre-builder instance records** -- `02:1178--1187`: "the symbolic
pre-builder search table is closed explicitly.  It has exactly nine instance
records", in the frozen registry order. -/
inductive PreBuilderSearch where
  /-- `BREF`, defining `B_ref`. -/
  | bref
  /-- `BSING`, defining `B_sing`. -/
  | bsing
  /-- `BPAIR`, defining `B_pair`. -/
  | bpair
  /-- `K2`, defining `k_2`. -/
  | k2
  /-- `KREF`, defining `k_ref`. -/
  | kref
  /-- `Q2`, defining `q_2`. -/
  | q2
  /-- `ASTAR`, defining `A_*`. -/
  | astar
  /-- `QDIRECT`, defining `Q`. -/
  | qdirect
  /-- `UTERM`, defining `u_term`. -/
  | uterm
  deriving DecidableEq, Repr

/-- The nine pre-builder searches in the frozen registry order of
`02:1180--1187`. -/
def preBuilderSearches : List PreBuilderSearch :=
  [PreBuilderSearch.bref, PreBuilderSearch.bsing, PreBuilderSearch.bpair,
    PreBuilderSearch.k2, PreBuilderSearch.kref, PreBuilderSearch.q2,
    PreBuilderSearch.astar, PreBuilderSearch.qdirect, PreBuilderSearch.uterm]

/-- **Aux Pb1 (`02:1187--1189`).**  Exactly nine records, all distinct, all
present: "Thus all nine, rather than only the five non-power-of-two searches,
carry an endpoint record and a coefficient-ledger row."  General. -/
theorem preBuilderSearchesIsTheCompleteRoster :
    preBuilderSearches.length = 9 ∧ preBuilderSearches.Nodup ∧
      ∀ s : PreBuilderSearch, s ∈ preBuilderSearches := by
  refine ⟨rfl, by decide, ?_⟩
  intro s; cases s <;> decide

/-! The `K2` instance record's three inline quantities of `02:1194--1197` --
`K_0 = max{4, 2^19, m_HS}`, `Z = max{16, K_0, clog_2(H_max+1)}` and
`k_2^* = K_0 + 10000 Z^2` -- are the **banked** `ParameterSchedule.k2Floor`,
`.zEndpoint` and `.k2Star` (`eq:k2-tested-endpoint`, `06:766--778`), together
with their displayed feasible candidate `.j2Star` and its eliminator
`.j2Star_le_j49`.  They are consumed by pin and are **not** restated here. -/

/-! **The `j_49` tested upper bound** -- `02:1218--1222`, "For fixed `k`, the
`j_49(k)` feasible set contains zero and has the tested upper bound `j <= k`,
because `j > k` contradicts `10000 j^2 <= 2401 k`" -- lands **no declaration
here**.  Both halves are the banked `RawLowProfileBody.J49Feasible.zero` and
`.le_index`, consumed by pin; the contrapositive wrapper this module used to
carry restated `.le_index` and is deleted. -/

end EthInapproximability.ParameterizedNP.MechanicalCompilerResidue
