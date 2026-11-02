import EthInapproximability.ParameterizedNP.MechanicalCompilerResidue

/-!
# Parameterized NP route: the one-level constructor `LevelStep`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `proc:level-step`, *One-level
  construction* `LevelStep`, in the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/05-public-records.tex`, **lines 318--364**
  (`\begin{procedure}` at `05:318`, label at `05:319`, `\end{procedure}` at
  `05:364`).  The nine steps are `L1` at `05:329--335`, `L2` at `05:336--337`,
  `L3` at `05:338--340`, `L4` at `05:341`, `L5` at `05:342--344`, `L6` at
  `05:345--347`, `L7` at `05:348`, `L8` at `05:349` and `L9` at `05:350--354`;
  the `Precondition` is `05:320--322`, the `Mutation` clause `05:324--326`, the
  `Postcondition` `05:357--363`.  Every one of those lines was opened
  first-hand in the frozen file this round.  Secondary anchors, each likewise
  opened first-hand this round:

  1. `def:level-trace` (label `05:220`, body `05:219--316`), whose 23 data
     fields and clause block `T1`--`T6` the output record must have exactly;
  2. `def:level-parameters` (label `05:173`, body `05:172--190`): the record is
     `Pi = (K, N_2, c_2)` at `05:176`, with `c_2 : L_2 -> Rows(M_1(Public,K))^{q_2}`
     at `05:180--181`, `N_2 > 0` structural at `05:183--186`, and "There are no
     stored width, tolerance, multiplicity, capacity, ceiling, or output-size
     fields" at `05:188--189`;
  3. `05:104--106` ("For fixed `(Public, K)`, the equations of
     `\Cref{sec:parameters}` are a deterministic straight-line program up to the
     balanced-family choice") and the accessor inventory it introduces,
     including the **Wrappers** paragraph `05:143--156` which lists
     `P_0, L_P, q, delta_U, Q_0, Q` as accessors with defining displays
     `eq:q-deltaU` and `eq:Q-theta-choice`;
  4. `eq:stage1-universes-and-value` (`07:141--148`) for `L2`, and `05:167--170`
     ("the Stage-1 matrix `M_1(Public, K)` is already determined by these
     accessors");
  5. `eq:stage2-relaxed-value` (`07:221--229`) for `L3`, with `05:178`'s
     `L_2 = [N_2]`;
  6. `07:495--497` for `L4` ("Stage 3 uses `s`, rather than four, classical
     copies", `M_3 = Int_s(M_2^T)` on `07:497`), reprinted inside
     `lem:stage3-exact-scale` at `07:450`;
  7. the rank-injection block `07:516--523` and the `K_R`/`J_2`/`iota_s`/`nu_s`
     block `07:524--535` for the inputs of `L5`, with
     `eq:raw-stage4-universes` itself at `07:537--545`;
  8. `08:17--31` (the three column and four row reservoirs), the least seed
     value `y_0` of `08:33--38` with its constructor-data sentence at
     `08:39--40`, `eq:protected-labelled-carriers` (`08:80--95`) and
     `eq:protected-multiplicities` (`08:98--109`) for `L6`;
  9. `eq:s-choice` (`06:111--118`), the frozen guard `04:389` (`s >= 4`), and
     the wrapper displays `eq:Ccert` (`06:431--432`), `P_0`/`L_P`
     (`06:467--471`), `eq:q-deltaU` (`06:515`, `06:517`) and
     `eq:Q-theta-choice` (`06:529--532`) for the schedule quantities the
     constructor evaluates rather than binds.

* **Reader counterpart: none, deliberately, and the reason is the reader's own
  content.**  For this layer the 41-page artifact states only
  `eq:paper-W-definition` (`03-parameterized-construction.tex`, display
  `03:84--89`, label line 88) and `eq:paper-W-carriers` (display `03:120--125`,
  label line 124), and **both are already assigned** -- the first to the trace
  field equations `W_eq`/`U_eq`, read off as
  `PublicRecords.levelTrace_W_eq_bridge` (`PublicRecords.lean:1535--1538`), and
  the second to `PublicRecords.levelTrace_W_carriers`; both assignments are
  recorded in that module's own header (`PublicRecords.lean:86--91`), and
  neither belongs to the `LevelTrace` structure generically.  Everything else
  this module builds the reader describes as prose, "All carriers, forgetful
  maps, least-representative sections, and entry cases are explicitly ordered
  and computable" (`03:126--127`), and `RECORD-LAYER-001` already declined that
  sentence on the standing ground that prose is never cited as a statement
  (`PublicRecords.lean:79--85`).  No reader line is assigned twice by this
  module, and no declaration below claims one.

  (**Record repair RF1, executed this round.**  The `cc-t7c-r2` bytes carried a
  self-referential residue of an earlier phantom-name repair at their own line
  75, which made the surrounding "all three sites are corrected" claim false
  while the residue stood.  The whole paragraph is rewritten: the theorem that
  carries `eq:paper-W-definition` is `PublicRecords.levelTrace_W_eq_bridge`,
  that is the only name this module uses for it, and no retired name is quoted
  anywhere in these bytes.  The substantive claim -- the reader display is
  already assigned and may not be claimed twice -- is unchanged.)

## What this module is

`proc:level-step` is a **composition**, not a new construction: its nine steps
invoke objects that are banked on this route, and the module performs that
composition, fixes the one input record the procedure takes at a fixed public
input, and -- since `cc-t8b`, banked at `cc-t8c` -- supplies the one *ambient*
datum the composition's own carriers are required to carry: the canonical order
of `12:93--98` on `Rows(M_1)` (Part 8).  Nothing else.

| step | frozen text | banked object consumed by pin |
| --- | --- | --- |
| `L1` | `05:329--335` | `GuardedSourceSlab.guardedRow` |
| `T2` | `05:241--252` | `PublicRecords.slotEmbed` |
| `L2` | `05:336--337` | `StageOneInterlace.stageOne` |
| `L3` | `05:338--340` | `Section5Admissibility.stepMTwo` |
| `L4` | `05:341` | `Section5Admissibility.stepMThree` |
| `L5` | `05:342--344` | `RawStageFour.rawStageFourGuarded` |
| `L6` | `05:345` | `DenseStageFourOpening.protectedAFrozen` |
| `L6` | `05:346` | `Section5Admissibility.stepN` (the `N = A^T` clause) |
| `L6` | `05:346--347` | `.rowForget`, `.rowSection`, `.colForget`, `.colSection` |
| `L7` | `05:348` | `Section5Admissibility.stepU`, `.stepW` |
| `L8` | `05:349` | `Section5Admissibility.stepRnext` |
| `L9` | `05:350--354` | `BridgeOutputEquality.rowsCard`, `.colsCard` |

**Nothing below restates a banked definition**, and the module introduces no
new mathematical object.  Precisely:

* the six carrier abbreviations are banked carriers with this module's own
  `(Public, K)`-evaluated arguments supplied;
* the twenty-five schedule accessors of Part 1 are the banked reifications of
  `sec:parameters` **applied to the paper's own two inputs** rather than to a
  three-field context record; each carries a kernel receipt that it is the
  banked context accessor at *every* stored width record (Part 1c);
* four of the eight step definitions -- `levelStepB`, `levelStepA`,
  `levelStepFAcol`, `levelStepRAcol` -- are single applications of the
  constructors in that table; `levelStepFArow` is a single application of the
  banked `rowForget` to **three** banked reservoir inclusions; and
  `levelStepRArow` and `levelStepRAcol` are each a single application whose one
  positivity side condition is discharged by a banked lemma (`uBaseF_pos`,
  `wBaseF_pos` respectively);
* `stepSeedValue` is **not** a constructor application: it evaluates the
  paper's own least element `y_0` of `08:33--38` at the zero-based carrier of
  `conv:finite-slots`;
* `levelStep` is **not** a constructor application either: it is the record
  assembly of `def:level-trace` whose 23 data fields are the objects above;
* `CanonicalRowOrder.stepRowsOneOrder` (Part 8, `cc-t8b`/`cc-t8c`) is **not** a
  new mathematical object either: it is the recursive canonical order that
  `12:93--98`, `14:166--168` and `04:393` already fix for every `LevelStep`
  carrier, reified at this module's own product carrier `Rows(M_1)`.  It is a
  `def`, promoted to an instance nowhere in this module, and no declaration of
  Parts 1--7 mentions it.

## The `cc-t7c-r3` repair: an honest substrate under the two-input signature

The `cc-t7c-r2` gate certified the *visible* shape of the constructor -- the
dependent record `LevelParamsFor P` owning its own `K`, and
`levelStep (P) (Pi)` with exactly the two inputs of `05:320` and no hypothesis
binder -- and returned `REVISE` on the substrate underneath it.  Its ruling,
quoted from the reply: "the paper-facing constructor still uses a proof-only,
self-chosen BEYOND-PAPER width witness as definitional construction data", and
its `R1`: "Delete `erasedWidths` and stop using `ctxFor` in paper-facing types
and definitions.  Provide genuine `(P, Pi.K)` accessors -- such as `sFor`,
`aExpFor`, `qFor`, `QFor`, `stage1BindingFor`, and `stageOneFor` -- whose
unfolding contains no `StageTwoWidths`."

That finding was re-verified first-hand against the frozen release before any
byte moved: `02-mechanical-contract.tex:97--99` reads "Proof-only existential
witnesses are not reused as construction data", inside item `M5` **Every finite
choice is deterministic**.  The `r2` bytes' defence of `erasedWidths` is
withdrawn as refuted (record repair **RF2**): `Nonempty.some` *is* a choice,
and opacity is not provenance.

**R1 is executed in full.**

* `erasedWidths` and `ctxFor` are **deleted**.  No `Classical.choice` term and
  no existential witness of any kind occurs in the **construction data** of any
  declaration below.

  (**Record repair RF11, executed this round**, on the `cc-t7c-r3` gate's
  record finding 7b.  The `r3` bytes wrote "in the data of any declaration
  below" and, in `levelStep_carriers_nonempty`, "none is chosen"; both
  over-claimed by omitting a disclosure.  Two occurrences of
  `P.G.vertexNonempty.some` do remain in this module -- one in `levelStepRArow`
  and one inside the proof of `levelStep_carriers_nonempty` -- and each is
  supplied only to the banked `uBaseF_pos`, whose result is the proposition
  `0 < u_0`.  By proof irrelevance neither reaches construction data: the row
  representative that `levelStepRArow` builds is the base-labelled copy at
  multiplicity index `0`, and neither its carrier coordinate nor its entry
  depends on the vertex.  The accurate claim, which is what these bytes assert,
  is therefore: **no construction datum of this module depends on a choice; one
  proof-only vertex witness discharges a positivity side condition.**  The gate
  ruled both sites `CLEAR` on exactly that ground.)
* Part 1 supplies the twenty-five `(Public, K)`-direct schedule accessors,
  ending in `sFor`, `aExpFor`, `qFor`, `QFor`, `q2For`, `stage1BindingFor` and
  `stageOneFor`.  Every one is a banked reification of `sec:parameters`
  applied to `P` and `K`; **no `StageTwoWidths` occurs in any of their
  unfoldings**, which is not asserted but proved, once per accessor, by the
  twenty-five receipts of Part 1c: each says the direct accessor equals the
  banked context accessor at `ctxAt P K W` for an *arbitrary* `W`, by `rfl`.
  Quantifying the receipt over `W` is exactly the sentence `05:104--106` makes
  available ("For fixed `(Public, K)`, the equations of `sec:parameters` are a
  deterministic straight-line program up to the balanced-family choice") and
  exactly what `05:188--189` demands ("There are no stored width ... fields").
* The eleven dependents the gate named -- `LevelParamsFor`,
  `LevelParamsFor.toParams`, `levelStepB`, `levelStepA`, `levelStepFArow`,
  `levelStepRArow`, `levelStep`, `levelStep_steps_are_banked`,
  `levelStep_M₃_resolves_to_source`, `levelStep_A_entry_is_B_entry`,
  `levelStep_H_at_derived_exponent` -- are retyped over that surface.
  **Reported deviation:** eight further declarations the `r2` gate marked
  `CLEAR` as "general internal context helpers" are retyped as well, because
  the constructor *consumes* them and they would otherwise reintroduce a
  context, hence a width record, into `levelStep`: the six carriers
  `StepRowsOne`, `StepColsOne`, `StepRowsB`, `StepColsB`, `StepRowsA`,
  `StepColsA`, and the two column maps `levelStepFAcol`, `levelStepRAcol`.
  `four_le_stepScale` and `stepSeedValue` move for the same reason; the latter
  now takes only `P`, since `05:36--37`'s `n_R` is all it ever read.  In every
  one of these the statement, the body and the proof are unchanged and only
  the binders move -- which is the disposition the `r1` gate already ruled on
  ("A later retyping is mechanical").

**R2 is executed by the deletion option the gate offered.**  Its text: "remove
D24/D26 once the constructor uses only direct `(P, Pi.K)` accessors".  The
alternative -- a uniform explicit-`W` assembly -- is *not available* once `R1`
is executed, because it would require a second copy of every step definition at
an explicit `W` alongside the `(P, Pi.K)` copies the same gate demands, and
this route does not carry two copies of a construction.  `levelTraceAt` and
`levelStep_eq_levelTraceAt` are therefore deleted, and with them the seven
vacuous field comparisons the gate identified (record repair **RF4**: the `r2`
prose claiming every field of that assembly was formed at the explicit `W` was
false, and is gone with the declaration it described).  What the deleted
receipt asserted is not lost -- it is *strengthened* into structure: with no
`W` anywhere on the paper path there is nothing to erase, and the twenty-five
receipts of Part 1c prove the same independence one display at a time.

**R3 is executed.**  `levelParamsFor_toParams_covers`, with its ambient
`hK : Pr.K = K`, is deleted and replaced by `LevelParamsFor.equivFibre`: an
actual `Equiv` between `LevelParamsFor P` and the dependent sigma
`Σ K, {p : LevelParams (StepRowsOne P K) (q2For P K) // p.K = K}`.  No
hypothesis remains at the theorem boundary; the coherence that used to be
`hK` is the subtype clause on the fibred side, where it belongs, and both
round trips are `rfl` after a `subst`.

**RF3 is executed**: this header no longer claims that `F2` and `F3` are
executed.  `F2`'s *signature* half was certified at `r2` and is unchanged;
`F2`'s substrate half is what this round performs, and `F3` -- the erasure
receipt -- is withdrawn rather than executed, because after `R1` there is no
adapter on the paper path for it to be about.

## The `cc-t7c-r4` cleanup: the fixed-interface rule, executed

The `cc-t7c-r3` gate returned `TRANCHE_VERDICT: REVISE` at 76 `CLEAR` /
4 `REVISE` / 0 `BLOCK` over eighty declarations.  The substrate above was
certified; the controlling defect was the **fixed-interface rule**, and it
named four declarations.  Its own words: "D36 makes `sFor P K` definitionally
the same as `sOf (ctxAt P K W)` for every `W`; D45 does the same for `aExpFor`
and `aExpAt`.  Consequently D24 and D25 do not establish facts about genuinely
different mathematical subjects."  Its exact repair -- delete D24 and D25,
place the primitive derivations directly in D26's two proof fields, derive D56
inline from `sScale_floor`, and **add no replacement wrapper theorems** -- is
what this round performs, and it performs nothing else.

* `sFor_floor` (D24) and `sixteen_le_aExpFor` (D25) are **deleted**, with no
  successor of any name.  The `r3` bytes defended them as "a new statement
  about a new subject"; that defence is **withdrawn as refuted** by the
  module's own receipts `sFor_eq_sOf` (D36) and `aExpFor_eq_aExpAt` (D45),
  which make the subjects the same term.  The verify seat recorded one partial
  disagreement (D24's *body* is a fresh application of `sScale_floor` and
  `three_le_uAux`, not a copy of `sOf_floor`'s proof); that observation is
  preserved here and does not alter the disposition, because the fixed-
  interface rule is about the *statement's subject*, not about the proof text,
  and the gate is the authority of record.
* `stage1BindingFor` (D26) keeps its two data fields byte-for-byte and
  discharges `three_le_a` and `s_pos` **inline from the banked primitives**
  (`ScheduleTemplateResidue.sixteen_le_astarThreshold`, `.four_le_astarExp`,
  `ParameterSchedule.three_le_uAux`, `.sScale_floor`), exactly the derivations
  the deleted pair carried.  Record repair **RF5**.
* `four_le_stepScale` (D56) keeps its statement byte-for-byte and is proved
  inline from `ParameterSchedule.sScale_floor`.  Record repair **RF6**; the
  Part-2 block's "derived above" is corrected in **RF7**.
* `stage1BindingFor_eq_stage1BindingAt` (D54) stays `rfl`: the two `Prop`
  fields differ only by proof irrelevance, so replacing their proof terms does
  not move the term.  The gate said so in advance, and the kernel confirms it.

**Nothing else in the mathematics moves.**  The seventy-six `CLEAR`
declarations keep their statements and their proof bodies byte-identical; what
changes outside the four is record prose only, in the eight repairs `RF5`
through `RF12`.  The module now carries **78** declarations, and this round
introduces **zero** new ones.

The gate's two record-only findings are `RF9`/`RF10` (the `StageTwoWidths`
description) and `RF11`/`RF12` (the two `P.G.vertexNonempty.some` disclosures);
`RF8` is this section.

## What survives of the internal adapter

Two declarations of the `r2` adapter block survive, both `CLEAR` at `r2` and
both now confined to Part 1c:

* `stageTwoWidthsNonempty` -- kept exactly as the gate permitted it, "only as
  an explicitly BEYOND-PAPER audit theorem".  It is consumed by **nothing**:
  no definition, no carrier, no proof field, and no theorem below mentions it.
  It records that the banked `StageTwoWidths` type is not empty, so that the
  universally quantified receipts of Part 1c are not vacuous;
* `ctxAt` -- the three-field retyping `(P, K, W) |-> ScheduleContext`, with `W`
  an **explicit binder**.  It occurs only inside the receipts of Part 1c and
  in no definition on the paper path.

**What `StageTwoWidths` is, and is not (record repair RF9, executed this
round).**  `StageTwoRelaxed.StageTwoWidths` is a **legacy Lean audit encoding**
banked by this route's own earlier tranches.  It is *not* the paper's record
and carries **zero canonical credit**: `def:level-parameters` says in terms
that the one-level parameter record has "no stored width, tolerance,
multiplicity, capacity, ceiling, or output-size fields" (`05:188--189`), so
there is no frozen object for it to be a formalization of.  Wherever the `r3`
bytes called it "the paper's stored record", or attributed it to a frozen
Stage-2 display, that attribution was false and is corrected here and at
`stageTwoWidthsNonempty` below (`RF10`).  Its only role in this module is as
the universally quantified dummy of the Part-1c receipts, whose whole content
is that **no** schedule quantity depends on it.

## Two candidate encodings, and why this one

**Candidate A (landed).**  Build the record of `def:level-trace` directly at
the schedule's own **derived** quantities, evaluated from `(Public, K)` --
`aExpFor`, `qFor`, `QFor` -- consuming the banked derived-tail steps
`stepMTwo`, `stepMThree`, `stepN`, `stepU`, `stepW`, `stepRnext` by pin.
`M_1` is *computed* (`stageOneFor`), not accepted.

**Candidate B (rejected, and the reason is a defect, not a preference).**
Apply the banked `Section5Admissibility.partialTailAssembler` at
`M_1 := stageOneFor`.  It typechecks, and it is wrong: the assembler's result
type is indexed by `Section5Admissibility.aExpOf`, whose `A_*` threshold
reads `lq2Of C = C.W.r_2` -- a **stored** width field -- while the Stage-1
matrix `stageOneFor` lives on carriers built from `aExpFor`, the same exponent
evaluated through the *derived* `log_2 q_2`.  The resulting record would carry
`M_1` at one exponent and the public integer `H` of `05:352` at another.  That
is exactly the seam `cc-t6x-r2` closed, one level up, so the assembler is
**not applicable here** and this module does not duplicate it.

**Candidate C (refuted upstream, recorded so it is not retried).**  Carry the
identification `C.W.q_2 = q2 G s` as an explicit hypothesis and rebuild the
stored width record from it.  This is the shape the `cc-t6r` park took, and it
is unsatisfiable at every `ScheduleContext` in the tree: `05:329--332` says
`q_2` "is the derived accessor equal to the least power of two at least
`12 s |E|`; there is no stored value to compare against it", and
`05:186--189` says the parameter record "has no stored width ... fields".  No
hypothesis of that shape appears below; `levelStep` has **no** hypothesis
beyond its two data arguments.

**Candidate D (rejected at `cc-t7c`, that gate's own prescription).**  Carry
`Pr.K = C.K` as a hypothesis of `levelStep`, or carry a coherence proof for
`C.W`.  Both are the forbidden fix: a constructor the paper states as total, on
two data inputs, would acquire a proof input that `05:320--322` explicitly
excludes ("No admissibility proof is an input").  The typing carries the
identification instead -- and after `F1` there is nothing left to identify,
because `K` is a field of the record and the accessors read that field.

**Candidate E (rejected at `cc-t7c-r1`).**  Keep the fibred `LevelParamsAt C`
and rest on extensional independence of `C.W`.  That gate: "Extensional
independence from `W` is valuable but does not make the signatures identical."
`LevelParamsAt` and its four lemmas were deleted at `r2` and are not revived.

**Candidate F (rejected at `cc-t7c-r2`, the current gate's ruling).**  Keep a
context adapter on the paper path and supply its width component from a
proof-only witness, relying on a full-trace erasure equation to certify that
the witness is not read.  This is the shape this round deletes; the gate's
words are quoted in the repair block above, and the frozen prohibition is
`02:97--99`.

## GAP register (what is *not* claimed)

1. **`inv:construction-identity` (`05:366--374`) is NOT stated here, and stays
   OPEN.**  The invariant is a claim about the `YES` analysis, the `NO`
   analysis, the robustness proof and the size proof -- that each of them
   denotes *this* object.  None of those four consumers is formalized, so the
   only Lean statement available would be that `levelStep P Pi` is a function
   of its arguments, which is proof irrelevance plus `rfl` and certifies
   nothing.  `S5-CONSTRUCTION-IDENTITY` therefore remains an HONEST-PARTIAL
   with its successor registered: it is discharged when the first of the four
   consumers is built, not here.
2. **The banked `StageTwoWidths` encoding is not a paper field, and is now
   structurally unreachable from this module's paper path.**  `05:188--189`
   says the parameter record has no stored width field at all, so nothing in
   the frozen text corresponds to that Lean type (`RF9`); the twenty-five
   receipts of Part 1c are the kernel evidence that every schedule quantity
   this constructor evaluates is a function of `(Public, K)` alone, and the
   banked `MechanicalCompilerResidue.derivedWidths_indep_stored` is the same
   fact for `a`, `q` and `Q` on the banked context presentation.  No clause
   identifies a stored record with anything.
3. **No gate is proved here and none is an input.**  `05:320--322`: "No
   admissibility proof is an input.  In particular, gates involving physical
   cardinalities are checked only after this total constructor returns its
   trace."  The nine groups stay in `Section5Admissibility`.
4. **`S5-BUNDLE-INHABITATION` is untouched.**  Nothing below inhabits any of
   the nine gate groups, and no declaration claims a nondegenerate *legal*
   `ScheduleContext`.  What lands here is the **constructor**, which is total
   and therefore needs no context inhabitant to be stated or to be the
   canonical witness of `PublicRecords.LevelTrace`.  Evaluating it at a legal
   public input stays registered under `S5-BUNDLE-INHABITATION`, and so does
   the canonical inhabitation of `LevelParamsFor`: the paper's own `Pi` is a
   `(q_2, t_2, eps_2)`-balanced family (`07:218--220`), whose existence
   argument is unbuilt, so `levelParamsFor_exists` below is a **general**
   nonemptiness statement about our encoding and is NOT offered as the paper's
   instance.
5. **No complexity, robustness, `YES` or `NO` proposition enters constructor
   data** (`05:315`, `05:324--326`).  No such proposition occurs below at all,
   not even as a derived readout.

## Dependencies, imports, adapters

* `EthInapproximability.ParameterizedNP.MechanicalCompilerResidue` (banked,
  consumed by pin) -- and through it, transitively and all consumed by pin,
  `FiniteSlots`, `GuardedSourceGraph`, `GuardedSourceSlab`, `PublicRecords`,
  `StageOneInterlace`, `RawStageFour`, `DenseStageFourOpening`,
  `BridgeOutputEquality`, `ParameterSchedule`, `ScheduleTemplateResidue`,
  `MassRedistributionTail`, `EntryGates`, `Section5Admissibility`,
  `StageTwoRelaxed`.
* External adapters: **none**.  No axiom is introduced, and
  `LegacyNPCC.Stage12` is **not** imported, so the AGHP axiom is not reachable
  from this module.
* Proof status: **new** (the composition, the `(Public, K)`-direct accessor
  chain, the dependent parameter record and the two-input constructor); every
  component **inherited** by pin from the banked constructors in the table
  above.
-/

namespace EthInapproximability.ParameterizedNP.LevelStepConstruction

open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.RawStageFour
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.Section5Admissibility
open EthInapproximability.ParameterizedNP.MechanicalCompilerResidue

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Part 1: the schedule at the paper's own two inputs `(Public, K)`

`05:104--106`: "For fixed `(Public, K)`, the equations of
`\Cref{sec:parameters}` are a deterministic straight-line program up to the
balanced-family choice.  The following list is the field inventory of that
program.  It is included to make clear which symbols are accessors rather than
stored data."  `05:143--156` then lists `P_0, L_P, q, delta_U, Q_0, Q` inside
that inventory, with defining displays `eq:q-deltaU` and `eq:Q-theta-choice`.

The banked evaluations of those displays -- `Section5Admissibility.sOf`,
`MechanicalCompilerResidue.aExpAt`, `.qAt`, `.QAt` and the chain between them
-- are stated over `Section5Admissibility.ScheduleContext`, a **three**-field
record `(P, K, W)` whose third component is the banked `StageTwoWidths`, a
**legacy Lean audit encoding of this route's own earlier tranches with zero
canonical credit** -- not a frozen object, since `05:188--189` says the
parameter record has no stored width field at all (record repair `RF9`,
executed this round; the `r3` bytes attributed the type to a Stage-2 display).
`def:level-parameters` forbids any such third component
(`05:188--189`), and `proc:level-step` has exactly two inputs (`05:320`), so
the paper's own straight-line program has to be available at `(Public, K)`
alone.  Part 1a and Part 1b make it so; Part 1c proves, one accessor at a
time, that the two presentations are the same term.

**Nothing here is a new display.**  Every body below is a banked reification --
`ParameterSchedule.Apre`, `.uAux`, `.sScale`, `.etaR`, `.leastPowTwoExp`,
`.P0sched`, `.LPwidth`, `.qWrap`, `.deltaU`; `ScheduleTemplateResidue.Bpub`,
`.zRpub`, `.U0sched`, `.astarThreshold`, `.astarExp`, `.Ccert`;
`MassRedistributionTail.aStage1`; `StageOneInterlace.bCap`, `.stageOne`;
`GuardedSourceSlab.q2`; `StageTwoRelaxed.r₂Of`; `EntryGates.Qwidth` --
consumed by pin and *applied* to `P` and `K`.  The route carries one copy of
each display; what Part 1 adds is a second **presentation** of the same
composition, on the paper's domain, and Part 1c is the kernel proof that the
two presentations agree at every stored record.  This is the `At`/`Of` split
the banked `MechanicalCompilerResidue` already uses, carried one step further
to the domain `05:320` actually names.

**No reader counterpart exists for any accessor of Part 1**, and that is
checked rather than assumed: the 41-page reader artifact prints no wrapper-width
schedule at all -- it takes `q` and `Q` as given interlace widths in
`03-parameterized-construction.tex:84--89` and `:120--125`, both of which are
already claimed by `PublicRecords`, and it never displays `P_0`, `L_P`,
`C_cert`, `B_cap`, `delta_U`, `Q_0`, `A_pre`, `u`, `s`, `A_*`, `eta_R` or
`U_0`.  None of the declarations of Part 1 claims a reader item.

### Part 1a: the source scale `s` and the Stage-1 exponent `a` -/

/-- **`B_pub = max{D, Y}`** (`06:49`) at the public record, consumed by pin
from the banked `ScheduleTemplateResidue.Bpub`.  The banked context
presentation is `Section5Admissibility.BpubOf`.  No reader counterpart (see
the Part-1 block docstring). -/
def BpubFor (P : LevelPublicInput V E) : ℕ :=
  ScheduleTemplateResidue.Bpub P.D P.Y

/-- **`z_R = max{clog_2 m_R, clog_2 n_R}`** (`06:51--54`) at the public
record, consumed by pin from the banked `ScheduleTemplateResidue.zRpub`.
Banked context presentation: `Section5Admissibility.zROf`.  No reader
counterpart. -/
def zRFor (P : LevelPublicInput V E) : ℕ :=
  ScheduleTemplateResidue.zRpub P.mR P.nR

/-- **`clog_2(|E| + 2)`** (`06:114`), the fifth branch of `A_pre`, at the
public edge carrier.  `Nat.clog 2` is the exact integer primitive
`clog_2(z) = min{j >= 0 : z <= 2^j}` of `06:75--76`; the summand `2` is the
display's own.  Banked context presentation: `Section5Admissibility.clEOf`,
which likewise ignores its context argument.  The public record is taken as an
argument only to keep the chain's shape uniform.  No reader counterpart. -/
def clEFor (_P : LevelPublicInput V E) : ℕ := Nat.clog 2 (Fintype.card E + 2)

/-- **`A_pre`** (`eq:s-choice`, `06:111--115`) at `(Public, K)`, consumed by
pin from the banked `ParameterSchedule.Apre` -- the five-branch maximum whose
frozen first branch `16` lives inside that reification and is not written
here.  Banked context presentation: `Section5Admissibility.ApreOf`.  No reader
counterpart. -/
def ApreFor (P : LevelPublicInput V E) : ℕ :=
  ParameterSchedule.Apre P.bout (BpubFor P) (zRFor P) (clEFor P)

/-- **`u = clog_2(clog_2(A_pre + 16))`** (`eq:s-choice`, `06:116--117`) at
`(Public, K)`, consumed by pin from the banked `ParameterSchedule.uAux`; the
frozen `+ 16` is inside that reification.  Banked context presentation:
`Section5Admissibility.uAuxOf`.  No reader counterpart. -/
def uAuxFor (P : LevelPublicInput V E) : ℕ :=
  ParameterSchedule.uAux (ApreFor P)

/-- **`s = 2^{ceil(B_s u^2)}`** (`eq:s-choice`, `06:118`) at the paper's own
two inputs: the configuration's `B_s` (`06:56--69`) and the public record's
own `u`.  Consumed by pin from the banked `ParameterSchedule.sScale`, whose
docstring records that the frozen ceiling is kept rather than dropped.
`06:122`: "Thus `s` is a public power of two."

This is the first of the six accessors the `cc-t7c-r2` gate's `R1` names.
Banked context presentation: `Section5Admissibility.sOf`; receipt
`sFor_eq_sOf`.  No reader counterpart. -/
noncomputable def sFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.sScale K.Bs (uAuxFor P)

/-- **`delta_v(G) = gamma |E| / (2 Delta |V|)`** (`04:311--320`) at the public
record's own graph and its two fixed fields.  `04:321--323`: "we use the
abbreviation `delta_v(G)`; it does not suppress a choice."  Banked context
presentation: `Section5Admissibility.dvOf`.  No reader counterpart. -/
noncomputable def dvFor (P : LevelPublicInput V E) : ℝ :=
  ((P.G.deltaV P.γ P.Δ : ℚ) : ℝ)

/-- **`zeta = gamma/24`** (`04:509`, reprinted at `05:117`) at the public
record's own `gamma`.  The `24` is the frozen display's own denominator.
Banked context presentation: `Section5Admissibility.zetaOf`.  No reader
counterpart. -/
noncomputable def zetaFor (P : LevelPublicInput V E) : ℝ :=
  ((P.γ : ℚ) : ℝ) / 24

/-- **`eta_R`** (`eq:eta-choice`, second line, `06:212--217`) at `(Public, K)`,
consumed by pin from the banked `ParameterSchedule.etaR`.  Banked context
presentation: `Section5Admissibility.etaROf`.  No reader counterpart. -/
noncomputable def etaRFor (P : LevelPublicInput V E) (K : LevelConfig) : ℝ :=
  ParameterSchedule.etaR (sFor P K) (dvFor P) (zetaFor P)

/-- **`ceil(log_2 U_0)`**, the fifth branch of `P_0` (`06:470`) and the sixth
of the `A_*` threshold (`06:302`), at `(Public, K)`.  `06:295--297` defines
`U_0 = max{2, b_out/eta_R}`, banked as `ScheduleTemplateResidue.U0sched`, and
`ceil(log_2 . )` is the banked `ParameterSchedule.leastPowTwoExp`.  Banked
context presentation: `Section5Admissibility.clU0Of`.  No reader
counterpart. -/
noncomputable def clU0For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.leastPowTwoExp
    (ScheduleTemplateResidue.U0sched P.bout (etaRFor P K))

/-- **`q_2`**, the ambient guarded-source width
(`def:guarded-source-constructor`, `04:386--391`; restated at `06:122--125`
and inside `def:admissibility-groups` at `05:450--452`; and named again in
`L1` at `05:329--332` as "the derived accessor equal to the least power of two
at least `12 s |E|`; there is no stored value to compare against it"),
consumed by pin from the banked `GuardedSourceSlab.q2` at the public record's
own graph and this schedule's evaluated `s`.  Banked context presentation:
`Section5Admissibility.DerivedWidths.q2At`.  No reader counterpart. -/
noncomputable def q2For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  q2 P.G (sFor P K)

/-- **`r_2 = log_2 q_2`** (`07:387--390`, the frozen selector sentence of
`lem:stage2-one-depth`: "Since `q_2 = 2^{r_2}`, apply
`lem:indexed-selector-protocol` ... It sends exactly `r_2 = log_2 q_2` bits"),
consumed by pin from the banked `StageTwoRelaxed.r₂Of` -- the `q_2`-only view
of the width, not a second copy of `Nat.log 2 (q2 ...)`.  Banked context
presentation: `Section5Admissibility.DerivedWidths.r2At`.  No reader
counterpart. -/
noncomputable def r2For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  StageTwoRelaxed.r₂Of P.G (sFor P K)

/-- **The threshold of `eq:Astar-choice`** (`06:299--305`),
`max{16, B_pub, z_R, log_2 q_2, s, ceil(log_2 U_0)}` at `(Public, K)`,
consumed by pin from the banked `ScheduleTemplateResidue.astarThreshold`
(whose frozen first branch `16` is inside that reification).  The `log_2 q_2`
slot holds the **derived** `r2For`, which is the seam `cc-t6x-r2` closed on
the banked context presentation.  Banked context presentation:
`MechanicalCompilerResidue.astarThresholdAt`.  No reader counterpart. -/
noncomputable def astarThresholdFor (P : LevelPublicInput V E)
    (K : LevelConfig) : ℕ :=
  ScheduleTemplateResidue.astarThreshold (BpubFor P) (zRFor P) (r2For P K)
    (sFor P K) (clU0For P K)

/-- **`log_2 A_*`** (`06:314`) at `(Public, K)`, the exponent of the least
power of two at least the threshold above, consumed by pin from the banked
`ScheduleTemplateResidue.astarExp`.  Banked context presentation:
`MechanicalCompilerResidue.lgAstarAt`.  No reader counterpart. -/
noncomputable def lgAstarFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ScheduleTemplateResidue.astarExp (astarThresholdFor P K)

/-- **`a = C_0 (log_2 A_*)^2`** (`eq:stage1-scales`, `06:314` -- the `a` line
of that `gathered` block, `06:315` being `q_1`, `06:316` `t_1` and `06:317`
`b_1`) at `(Public, K)`, consumed by pin from the banked
`MassRedistributionTail.aStage1` at the configuration's own `C_0`.

This is the second of the six accessors the `R1` list names.  Banked context
presentation: `MechanicalCompilerResidue.aExpAt`; receipt `aExpFor_eq_aExpAt`.
No reader counterpart. -/
noncomputable def aExpFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  MassRedistributionTail.aStage1 K.C₀ (lgAstarFor P K)

/-! ### Part 1b: the wrapper widths `q` and `Q`, and the Stage-1 objects -/

/-- **`log_2 s`**, the third summand of `eq:Ccert` (`06:432` prints
`\log_2s`; `06:122` makes `s` a public power of two, so the integer logarithm
is exact).  Banked context presentation: `Section5Admissibility.lsOf`.  No
reader counterpart. -/
noncomputable def lsFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  Nat.log 2 (sFor P K)

/-- **`B_cap = D + a`** (`07-one-level-construction.tex:154--157`: `07:154`
"We denote this public certified scale by", `07:155` the opening `\[`,
`07:156` the display `\Bcap\defeq D+a.`, `07:157` the closing `\]`) at
`(Public, K)`, consumed by pin from the banked `StageOneInterlace.bCap` at the
public record's own `D` and the derived Stage-1 exponent.  Banked context
presentation: `MechanicalCompilerResidue.bCapAt`.  No reader counterpart. -/
noncomputable def bCapFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  StageOneInterlace.bCap P.D (aExpFor P K)

/-- **`C_cert = B_cap + log_2 q_2 + log_2 s + 1`** (`eq:Ccert`, display
`06:431--432`, label `06:433`) at `(Public, K)`, consumed by pin from the
banked `ScheduleTemplateResidue.Ccert`; the trailing `+ 1` is the display's
own and lives inside that reification.  Banked context presentation:
`MechanicalCompilerResidue.CcertAt`.  No reader counterpart. -/
noncomputable def CcertFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ScheduleTemplateResidue.Ccert (bCapFor P K) (r2For P K) (lsFor P K)

/-- **`P_0 = max{16, C_cert, s, log_2 q_2, ceil(log_2 U_0), z_R}`** -- the
display `06:467--470` opening `\Cref{sec:parameter-wrappers}` -- at
`(Public, K)`, consumed by pin from the banked `ParameterSchedule.P0sched`,
which is that six-branch maximum; its frozen first branch `16` is inside that
reification.  Banked context presentation: `MechanicalCompilerResidue.P0At`.
No reader counterpart. -/
noncomputable def P0For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.P0sched (CcertFor P K) (sFor P K) (r2For P K)
    (clU0For P K) (zRFor P)

/-- **`L_P = clog_2(P_0)`** -- the second half of the same display, `06:471` --
at `(Public, K)`, consumed by pin from the banked
`ParameterSchedule.LPwidth`.  Banked context presentation:
`MechanicalCompilerResidue.LPAt`.  No reader counterpart. -/
noncomputable def LPFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.LPwidth (P0For P K)

/-- **`q = 2^{A_wrap L_P^2}`, the first-wrapper width** -- `eq:q-deltaU`,
display line `06:515`, label `06:518` ("Choose the first-wrapper width",
`06:513`) -- at `(Public, K)`, consumed by pin from the banked
`ParameterSchedule.qWrap` at the configuration's own `A_wrap`.  The exponent
is `A_wrap L_P^2` and not `A_wrap L_P`: `06:515` prints
`q=2^{A_{\mathrm{wrap}}L_P^2}`, and the square is inside `qWrap`.

This is the third of the six accessors the `R1` list names.  Banked context
presentation: `MechanicalCompilerResidue.qAt`; receipt `qFor_eq_qAt`.  No
reader counterpart. -/
noncomputable def qFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.qWrap K.Awrap (LPFor P K)

/-- **`delta_U = eta_R/(16 q)`** -- `eq:q-deltaU`, display line `06:517` --
at `(Public, K)`, consumed by pin from the banked
`ParameterSchedule.deltaU`; the frozen `16` is inside that reification.
Banked context presentation: `MechanicalCompilerResidue.deltaUAt`.  No reader
counterpart. -/
noncomputable def deltaUFor (P : LevelPublicInput V E) (K : LevelConfig) : ℝ :=
  ParameterSchedule.deltaU (etaRFor P K) (qFor P K)

/-- **`Q`, the outer bridge width** -- `eq:Q-theta-choice`:
`Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}` on `06:529--531` and
"`Q =` the least power of two at least `Q_0`" on `06:532`, label `06:537` --
at `(Public, K)`, consumed by pin from the banked `EntryGates.Qwidth`, which
is that least power of two and carries all three frozen branches.

This is the fourth of the six accessors the `R1` list names.  Banked context
presentation: `MechanicalCompilerResidue.QAt`; receipt `QFor_eq_QAt`.  No
reader counterpart. -/
noncomputable def QFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  EntryGates.Qwidth P.bout (deltaUFor P K)

/-- **The Stage-1 slot binding at `(Public, K)`** -- the `(a, s)` pair that
`05:336--337` hands to the Stage-1 constructor ("Construct Stage 1, `M_1`,
from `R, a, q_1, s`"), evaluated at the paper's own two inputs.

`a := aExpFor P K` is `eq:stage1-scales` (`06:314`) evaluated through the
derived `log_2 q_2`; `s := sFor P K` is `eq:s-choice` (`06:118`) evaluated.
The two legality guards of the banked `FiniteSlots.Stage1SlotBinding` are
**derived**, not assumed, and -- record repair **RF5**, executed this round --
they are discharged **inline from the banked primitives**, with no local
restatement standing between the primitives and this record:

* `three_le_a`: the frozen first branch `16` of `eq:Astar-choice`
  (`06:299--305`) is `ScheduleTemplateResidue.sixteen_le_astarThreshold`;
  `06:480--481` ("Since `D <= B_pub`, `A_*` is a power of two, and
  `A_* >= 16`,") is
  `ScheduleTemplateResidue.four_le_astarExp`, giving `log_2 A_* >= 4`; and
  `eq:stage1-scales` (`06:314`) is `a = C_0 (log_2 A_*)^2`, so the
  `LevelConfig` field `C_0 >= 1` yields `a >= 16 >= 3`;
* `s_pos`: `06:116--117` is `ParameterSchedule.three_le_uAux`, giving
  `3 <= u`, and `eq:s-choice` (`06:118`) at the `LevelConfig` field
  `1 <= B_s` is `ParameterSchedule.sScale_floor`, whose first clause is the
  frozen floor `3 < s` of `04:389` ("Let `s >= 4` be a power of two").

Those are exactly the derivations the `cc-t7c-r3` bytes carried in the two
local theorems `sFor_floor` and `sixteen_le_aExpFor`; the `cc-t7c-r3` gate
ruled both to be renamed restatements of the banked `sOf_floor` and
`sixteen_le_aExpAt` -- definitionally identified by this module's own receipts
`sFor_eq_sOf` and `aExpFor_eq_aExpAt` -- and prescribed deletion with **no
replacement wrapper**.  Both are deleted; only the proof terms moved here.
No numeral of ours enters this binding, and no `StageTwoWidths` occurs in its
unfolding.

This is the fifth of the six accessors the `R1` list names.  Banked context
presentation: `MechanicalCompilerResidue.stage1BindingAt`; receipt
`stage1BindingFor_eq_stage1BindingAt`, which stays `rfl` because the two
`Prop` fields differ only by proof irrelevance.  No reader counterpart. -/
noncomputable def stage1BindingFor (P : LevelPublicInput V E)
    (K : LevelConfig) : FiniteSlots.Stage1SlotBinding where
  a := aExpFor P K
  s := sFor P K
  three_le_a := by
    have h16 : 16 ≤ astarThresholdFor P K :=
      ScheduleTemplateResidue.sixteen_le_astarThreshold _ _ _ _ _
    have h4 : 4 ≤ lgAstarFor P K := ScheduleTemplateResidue.four_le_astarExp h16
    have hC : 1 ≤ K.C₀ := K.C₀pos
    have hsq : 16 ≤ lgAstarFor P K ^ 2 := by nlinarith
    have hmul : lgAstarFor P K ^ 2 ≤ K.C₀ * lgAstarFor P K ^ 2 :=
      Nat.le_mul_of_pos_left _ hC
    have heq : aExpFor P K = K.C₀ * lgAstarFor P K ^ 2 := rfl
    omega
  s_pos :=
    lt_trans (by norm_num)
      (ParameterSchedule.sScale_floor K.Bspos
        (ParameterSchedule.three_le_uAux P.bout (BpubFor P) (zRFor P)
          (clEFor P))).1

/-- **The Stage-1 matrix `M_1(Public, K)` at the paper's own two inputs** --
`05:167--170` ("already determined by these accessors and the equations in
`sec:one-level`") realized through the constructor call of `05:336--337`.

The body is the banked `StageOneInterlace.stageOne` -- the carrier and entry
equations of `eq:stage1-universes-and-value` (`07:141--148`), consumed by pin
and not restated -- applied to the binding above and to the public record's own
source matrix `R : X_R -> Y_R -> {0,1}` at the frozen zero-based carriers
`X_R = [m_R]`, `Y_R = [n_R]` of `P3` (`05:36--37`, `conv:finite-slots`).

This is the sixth of the six accessors the `R1` list names.  Banked context
presentation: `MechanicalCompilerResidue.stageOneAt`; receipt
`stageOneFor_eq_stageOneAt`.

Reader counterpart: **none** -- the reader's `eq:paper-M1-definition`
(`03-parameterized-construction.tex`, label line 156) is already claimed by
the banked `MechanicalCompilerResidue.stageOneAt`, and the reader-counterpart
rule forbids assigning one reader item twice. -/
noncomputable def stageOneFor (P : LevelPublicInput V E) (K : LevelConfig) :
    Stage1Rows (stage1BindingFor P K) (Fin P.mR) →
      Stage1Cols (stage1BindingFor P K) (Fin P.nR) → Bool :=
  StageOneInterlace.stageOne (stage1BindingFor P K) P.R

/-- **`0 < q_2` at `(Public, K)`**, the banked `GuardedSourceSlab.q2_pos` read
at this schedule's evaluated source scale.  Consumed by the two Section-8
column carriers below; PROVED by pin.  General in the two carriers, the public
record and the configuration. -/
theorem q2For_pos (P : LevelPublicInput V E) (K : LevelConfig) :
    0 < q2For P K :=
  q2_pos P.G (sFor P K)

/-! ### Part 1c: the receipts -- no `StageTwoWidths` in any unfolding

The `cc-t7c-r2` gate's `R1` asks for accessors "whose unfolding contains no
`StageTwoWidths`".  That is a property of the twenty-five definitions above,
and it is *visible* in their bodies; what the twenty-five theorems below add is
the kernel statement of the same fact from the other side -- each direct
accessor **is** the banked context accessor, at an arbitrary stored width
record `W`.  Because `W` is universally quantified and appears on the right
only, each receipt says precisely that the banked chain's value at that
display does not depend on `W`, i.e. that the display is a function of
`(Public, K)` alone.  Composed across the twenty-five, that is
`05:104--106`'s straight-line program and `05:188--189`'s "There are no stored
width ... fields", made checkable rather than asserted.

Two internal declarations serve this block and nothing else.  Neither claims a
frozen statement, and neither occurs in any definition on the paper path. -/

/-- **INTERNAL adapter: the schedule context at `(Public, K)` and an explicit
stored width record.**  The banked chain's three-field record, formed from the
paper's two inputs together with a width record supplied as an **explicit
binder**.  It is a retyping and nothing else; `05:104--106` is the sentence
that makes it legitimate.

It occurs **only** in the receipts below.  No definition on the paper path
mentions it, and no value of `W` is ever chosen: every occurrence is under a
universal quantifier.  The `cc-t7c-r2` gate ruled this declaration `CLEAR`
("Proper explicit internal adapter; field order is `P,K,W`"). -/
def ctxAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) : ScheduleContext V E :=
  ⟨P, K, W⟩

/-- **BEYOND-PAPER AUDIT, and consumed by nothing.**  The banked
`StageTwoRelaxed.StageTwoWidths` type is not empty.

**What that type is (record repair RF10, executed this round).**
`StageTwoWidths` is a **legacy Lean audit encoding** banked by this route's own
earlier tranches, and it carries **zero canonical credit**.  It is *not* "the
paper's stored record" and is not the formalization of any frozen Stage-2
display: `def:level-parameters` says in terms that the one-level parameter
record has "no stored width, tolerance, multiplicity, capacity, ceiling, or
output-size fields" (`05:188--189`), so there is no frozen object for it to
encode.  The `cc-t7c-r3` bytes described it as the paper's record; the
`cc-t7c-r3` gate returned that as a record-only defect, and the description is
corrected here and in the module header (`RF9`).

This is *not* a claim about the schedule, and it is *not* used anywhere in
this module: no definition, no carrier, no structure field, no proof field and
no other theorem below mentions it.  It is retained on exactly the footing the
`cc-t7c-r2` gate permitted -- "D08 may remain only as an explicitly
BEYOND-PAPER audit theorem" -- and it earns its place by showing that the
receipts of this block are not vacuously universally quantified.

Its single input is the banked **BEYOND-PAPER AUDIT** witness
`Section5Admissibility.DerivedWidths.widthGate_shape_satisfiable`, whose own
docstring says it "claims nothing about the schedule and nothing about any
context"; that label is inherited verbatim.  The four numeric fields
`k_2, r_2, b_1, m_HS` come from that banked existential, so no numeral of this
module is assigned to any of them, and the two order clauses `4 t_2 <= q_2`
and `q_2 2^{-b_1} <= 1/131072` are the banked witness's own
`4 * 2^k <= q <= 2^r` and `17 + r <= b`, transported.  The `131072` is the
frozen balancing constant and `17` is a proof-position evaluation of
`131072 = 2^17`.

A *scheduled* inhabitant of this legacy encoding -- one whose fields agree with
the derived widths at a legal public input -- is a different and strictly
stronger object; producing it is the OPEN, REGISTERED
`S5-BUNDLE-INHABITATION` row and is not attempted, needed, or claimed here,
and neither it nor this theorem is a paper obligation (`RF10`).  PROVED. -/
theorem stageTwoWidthsNonempty : Nonempty StageTwoRelaxed.StageTwoWidths := by
  obtain ⟨k, b, m, q, r, hm, hmk, _hk, hq, hqr, hrb, _hqb⟩ :=
    DerivedWidths.widthGate_shape_satisfiable
  have hdepth : 131072 * 2 ^ r ≤ 2 ^ b := by
    calc (131072 : ℕ) * 2 ^ r = 2 ^ 17 * 2 ^ r := by norm_num
      _ = 2 ^ (17 + r) := (pow_add 2 17 r).symm
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hrb
  exact ⟨{ k₂ := k
           r₂ := r
           b₁ := b
           mHS := m
           five_le_mHS := hm
           mHS_le_k₂ := hmk
           four_t₂_le_q₂ := le_trans hq hqr
           depth_gate := hdepth }⟩

/-- Receipt 1/25 (`B_pub`, `06:49`): the direct accessor is the banked context
accessor at every stored width record.  PROVED by `rfl`. -/
theorem BpubFor_eq_BpubOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    BpubFor P = BpubOf (ctxAt P K W) := rfl

/-- Receipt 2/25 (`z_R`, `06:51--54`).  PROVED by `rfl`. -/
theorem zRFor_eq_zROf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    zRFor P = zROf (ctxAt P K W) := rfl

/-- Receipt 3/25 (`clog_2(|E|+2)`, `06:114`).  PROVED by `rfl`. -/
theorem clEFor_eq_clEOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    clEFor P = clEOf (ctxAt P K W) := rfl

/-- Receipt 4/25 (`A_pre`, `06:111--115`).  PROVED by `rfl`. -/
theorem ApreFor_eq_ApreOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    ApreFor P = ApreOf (ctxAt P K W) := rfl

/-- Receipt 5/25 (`u`, `06:116--117`).  PROVED by `rfl`. -/
theorem uAuxFor_eq_uAuxOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    uAuxFor P = uAuxOf (ctxAt P K W) := rfl

/-- Receipt 6/25 (`s`, `eq:s-choice`, `06:118`) -- the first accessor of the
gate's `R1` list.  PROVED by `rfl`. -/
theorem sFor_eq_sOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    sFor P K = sOf (ctxAt P K W) := rfl

/-- Receipt 7/25 (`delta_v(G)`, `04:311--320`).  PROVED by `rfl`. -/
theorem dvFor_eq_dvOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    dvFor P = dvOf (ctxAt P K W) := rfl

/-- Receipt 8/25 (`zeta`, `04:509`).  PROVED by `rfl`. -/
theorem zetaFor_eq_zetaOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    zetaFor P = zetaOf (ctxAt P K W) := rfl

/-- Receipt 9/25 (`eta_R`, `06:212--217`).  PROVED by `rfl`. -/
theorem etaRFor_eq_etaROf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    etaRFor P K = etaROf (ctxAt P K W) := rfl

/-- Receipt 10/25 (`ceil(log_2 U_0)`, `06:295--297` / `06:470`).  PROVED by
`rfl`. -/
theorem clU0For_eq_clU0Of (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    clU0For P K = clU0Of (ctxAt P K W) := rfl

/-- Receipt 11/25 (`q_2`, `04:386--391` / `05:329--332`).  PROVED by
`rfl`. -/
theorem q2For_eq_q2At (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    q2For P K = DerivedWidths.q2At (ctxAt P K W) := rfl

/-- Receipt 12/25 (`r_2 = log_2 q_2`, `07:387--390`).  PROVED by `rfl`. -/
theorem r2For_eq_r2At (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    r2For P K = DerivedWidths.r2At (ctxAt P K W) := rfl

/-- Receipt 13/25 (the `A_*` threshold, `06:299--305`).  PROVED by `rfl`. -/
theorem astarThresholdFor_eq_astarThresholdAt (P : LevelPublicInput V E)
    (K : LevelConfig) (W : StageTwoRelaxed.StageTwoWidths) :
    astarThresholdFor P K = astarThresholdAt (ctxAt P K W) := rfl

/-- Receipt 14/25 (`log_2 A_*`, `06:314`).  PROVED by `rfl`. -/
theorem lgAstarFor_eq_lgAstarAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    lgAstarFor P K = lgAstarAt (ctxAt P K W) := rfl

/-- Receipt 15/25 (`a`, `eq:stage1-scales`, `06:314`) -- the second accessor of
the gate's `R1` list.  PROVED by `rfl`. -/
theorem aExpFor_eq_aExpAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    aExpFor P K = aExpAt (ctxAt P K W) := rfl

/-- Receipt 16/25 (`log_2 s`, `06:432`).  PROVED by `rfl`. -/
theorem lsFor_eq_lsOf (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    lsFor P K = lsOf (ctxAt P K W) := rfl

/-- Receipt 17/25 (`B_cap`, `07:154--157`).  PROVED by `rfl`. -/
theorem bCapFor_eq_bCapAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    bCapFor P K = bCapAt (ctxAt P K W) := rfl

/-- Receipt 18/25 (`C_cert`, `eq:Ccert`, `06:431--432`).  PROVED by `rfl`. -/
theorem CcertFor_eq_CcertAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    CcertFor P K = CcertAt (ctxAt P K W) := rfl

/-- Receipt 19/25 (`P_0`, `06:467--470`).  PROVED by `rfl`. -/
theorem P0For_eq_P0At (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    P0For P K = P0At (ctxAt P K W) := rfl

/-- Receipt 20/25 (`L_P`, `06:471`).  PROVED by `rfl`. -/
theorem LPFor_eq_LPAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    LPFor P K = LPAt (ctxAt P K W) := rfl

/-- Receipt 21/25 (`q`, `eq:q-deltaU`, `06:515`) -- the third accessor of the
gate's `R1` list.  PROVED by `rfl`. -/
theorem qFor_eq_qAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    qFor P K = qAt (ctxAt P K W) := rfl

/-- Receipt 22/25 (`delta_U`, `eq:q-deltaU`, `06:517`).  PROVED by `rfl`. -/
theorem deltaUFor_eq_deltaUAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    deltaUFor P K = deltaUAt (ctxAt P K W) := rfl

/-- Receipt 23/25 (`Q`, `eq:Q-theta-choice`, `06:529--532`) -- the fourth
accessor of the gate's `R1` list.  PROVED by `rfl`. -/
theorem QFor_eq_QAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    QFor P K = QAt (ctxAt P K W) := rfl

/-- Receipt 24/25 (the Stage-1 slot binding, `05:336--337`) -- the fifth
accessor of the gate's `R1` list.  The two `Prop` fields differ only by proof
irrelevance, so the two bindings are the same term.  PROVED by `rfl`. -/
theorem stage1BindingFor_eq_stage1BindingAt (P : LevelPublicInput V E)
    (K : LevelConfig) (W : StageTwoRelaxed.StageTwoWidths) :
    stage1BindingFor P K = stage1BindingAt (ctxAt P K W) := rfl

/-- Receipt 25/25 (`M_1`, `05:167--170` / `05:336--337`) -- the sixth accessor
of the gate's `R1` list, and the one that carries the whole Stage-1 carrier
tower with it.  PROVED by `rfl`. -/
theorem stageOneFor_eq_stageOneAt (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    stageOneFor P K = stageOneAt (ctxAt P K W) := rfl

/-! ## Part 2: the frozen bin-count floor, at the binding the constructor uses

`proc:level-step` names no numeral.  The one numeric fact its Section-7 and
Section-8 callees demand is the frozen bin-count floor, and it is **derived
inline from the banked `ParameterSchedule.sScale_floor`** (record repair
**RF7**, executed this round: the `cc-t7c-r3` bytes said "derived above",
pointing at the local `sFor_floor` that the `cc-t7c-r3` gate has since ordered
deleted as a renamed restatement; there is no such local theorem now, and the
derivation is the primitive's).  The single declaration below is that floor
read at the field the callees index by. -/

/-- The frozen bin-count floor at the scheduled Stage-1 binding:
`4 <= s`, stated at `(stage1BindingFor P K).s`, which **is** `sFor P K` by
construction.

**Proved inline from the banked primitive** (record repair **RF6**, executed
this round): `ParameterSchedule.three_le_uAux` supplies `3 <= u` from
`06:116--117`, and `ParameterSchedule.sScale_floor` at the `LevelConfig` field
`1 <= B_s` returns `3 < s`, which **is** `4 <= s` on `Nat`.  The `cc-t7c-r3`
gate's ruling on this declaration was "Keep the statement, but prove it inline
from `sScale_floor`; do not introduce a replacement `sFor_floor`", and that is
what these bytes do: the statement is byte-identical to the `r3` bytes and only
the proof term moved.

**The floor's frozen source is `04:389`** -- `def:guarded-source-constructor`,
"Let `s >= 4` be a power of two" -- which is the hypothesis every Stage-4
consumer inherits.  (`eq:s-choice` at `06:118` *defines* `s = 2^{ceil(B_s u^2)}`
and does not itself print the bound; the previous bytes cited only `06:118`,
which the `cc-t7c` gate's record finding R15 rejected.)

Consumed twice below, and by nothing else: `RawStageFour.rawStageFourGuarded`
asks for `3 <= F.s` (the rank injections of `07:516--523` land in `[s]`), and
`DenseStageFourOpening.section8_row_counts_pos` asks for `4 <= F.s` because the
blocker reservoir `W_B = I_B x Rows(R)` of `08:24` is indexed by
`I_B = [4s] x [s-3]` -- the frozen item carrier `I(G,s) = [4s] x I_0(G,s)` of
`04:396`, whose blocker branch is ranged at `04:491--492` ("`r in [4s]`,
`k in [s-3]`") and whose cardinality `08:566--567` reads off as
`|I_B| = 4s(s-3)` -- which is empty at `s <= 3`.  The numeral `4` is the
frozen floor's own, not a choice of this module.

**Retyped at `cc-t7c-r3`** from a `ScheduleContext` binder to the paper's own
pair, for the reason recorded in the header: it is consumed by the constructor,
so leaving it on a context would reintroduce a stored width record into
`levelStep`.  General in the public record and the configuration.  PROVED. -/
theorem four_le_stepScale (P : LevelPublicInput V E) (K : LevelConfig) :
    4 ≤ (stage1BindingFor P K).s :=
  (ParameterSchedule.sScale_floor K.Bspos
    (ParameterSchedule.three_le_uAux P.bout (BpubFor P) (zRFor P)
      (clEFor P))).1

/-! ## Part 3: the six carriers of the composition

Every type below is a **banked** carrier with this module's own
`(Public, K)`-evaluated arguments supplied.  Naming them keeps the
fourteen-argument `LevelTrace` application readable and lets the nonemptiness
battery of Part 7 be stated once; no new type is introduced and no banked name
is renamed (each abbreviation is a banked abbreviation *applied*, never an
alias for it).

**Retyped at `cc-t7c-r3`** from a `ScheduleContext` binder to `(P, K)`: the six
were `CLEAR` at `r2` as internal helpers, but they are the carriers of the
constructor's own output type, so on a context they would put a stored width
record into the type of `levelStep`.  The bodies are unchanged. -/

/-- `Rows(M_1) = [q_1] x Rows(R)` (`eq:stage1-universes-and-value`, `07:144`)
at the schedule of `(Public, K)`.  This is the `X_1` the parameter record's
family `c_2 : L_2 -> Rows(M_1)^{q_2}` of `05:180--181` lands in, so the record
`Pi` below is typed at it rather than at a free carrier. -/
abbrev StepRowsOne (P : LevelPublicInput V E) (K : LevelConfig) : Type _ :=
  Stage1Rows (stage1BindingFor P K) (Fin P.mR)

/-- `C_1 = Cols(R)^{L_1}` (`eq:stage1-universes-and-value`, `07:143`) at the
schedule of `(Public, K)`.  This is the trace's `C_1` type argument. -/
abbrev StepColsOne (P : LevelPublicInput V E) (K : LevelConfig) : Type _ :=
  Stage1Cols (stage1BindingFor P K) (Fin P.nR)

/-- `Rows(B) = ([s] x Cols(M_2)) u (I x Rows(R))` (`eq:raw-stage4-universes`,
`07:539--541`) at the guarded item carrier, i.e. the banked
`DenseStageFourOpening.RowsB` at the schedule of `(Public, K)`, with the frozen
`Cols(M_2) = L_2 = [N_2]` of `07:224` / `05:178`. -/
abbrev StepRowsB (P : LevelPublicInput V E) (K : LevelConfig) (N₂ : ℕ) :
    Type _ :=
  RowsB (stage1BindingFor P K) V (Fin P.mR) (Fin N₂)

/-- `Omega = Cols(B) = K_R x J_2^s` (`eq:raw-stage4-universes`, `07:542`,
reprinted at `08:20`), i.e. the banked `DenseStageFourOpening.Omega` at the
**derived** ambient width `q_2 = q2 G s` of `05:329--332`. -/
abbrev StepColsB (P : LevelPublicInput V E) (K : LevelConfig) : Type _ :=
  Omega (stage1BindingFor P K) (q2For P K) (Fin P.nR)

/-- `Rows(A)` of `eq:protected-labelled-carriers` (`08:88--92`) at the frozen
multiplicities of `eq:protected-multiplicities` (`08:103--106`, the four *row*
multiplicities `u_0, u_temp, u_V, u_B`), i.e. the banked
`DenseStageFourOpening.ProtRowsFrozen`.  Not one of the multiplicities is
written out here: they are the banked `uBaseF`, `uTempF`, `uVertF`, `uBlockF`
inside that abbreviation. -/
abbrev StepRowsA (P : LevelPublicInput V E) (K : LevelConfig) (N₂ : ℕ) :
    Type _ :=
  ProtRowsFrozen (stage1BindingFor P K) V (Fin P.mR) (Fin N₂)

/-- `Cols(A)` of `eq:protected-labelled-carriers` (`08:83--87`) at the frozen
*column* multiplicities `w_0, w_Sigma, w_D` (`08:100--102`), i.e. the banked
`DenseStageFourOpening.ProtColsFrozen`. -/
abbrev StepColsA (P : LevelPublicInput V E) (K : LevelConfig) : Type _ :=
  ProtColsFrozen (stage1BindingFor P K) (q2For P K) (Fin P.nR)

/-! ## Part 4: `Pi = (K, N_2, c_2)`, the one-level parameter record

`def:level-parameters` (`05:172--190`).  The record is `Pi = (K, N_2, c_2)`
(`05:176`) at a fixed `Public` (`05:174`), the family lands in
`Rows(M_1(Public, K))^{q_2}` (`05:180--181`) -- so its codomain is a function
of the record's own `K` -- `N_2 > 0` is structural (`05:183--186`), and there
are **no** further fields (`05:188--189`).

`K` is the record's first field, the codomain of `c_2` is computed from that
field, and the record's signature mentions no width record and no context.  The
banked `PublicRecords.LevelParams X_1 w` remains the *fibre* of this record
over an already-supplied carrier and width; `toParams` is the exact
correspondence, and `equivFibre` is the equivalence in both directions. -/

/-- **`Pi = (K, N_2, c_2)` at a fixed public record** (`def:level-parameters`,
`05:172--190`), the paper-facing dependent parameter record.

Field provenance, one row per field:

* `K` -- GENUINELY FREE, `05:176` (`Pi = (K, N_2, c_2)`) and `05:320` (`Pi` is
  an input of the procedure).  It is a **field**, not an ambient datum: the
  codomain of `c_2` is computed from it, which is the frozen dependency
  `Rows(M_1(Public, K))^{q_2}` of `05:180--181`.
* `N_2` -- GENUINELY FREE, `05:177` (`N_2 in N_{>0}`) and `05:320`.  The paper
  fixes no value; `02:1142--1143` says "do not choose `N_2` or `c_2`".
* `N_2pos` -- the frozen structural clause `05:183--186`, verbatim: positivity
  "is part of the type because `LevelStep` must return nonempty communication
  carriers and total least-representative maps before admissibility is
  checked".  It is not a premise bundle and not a derived telescope.
* `c_2` -- GENUINELY FREE, `05:180--181`, at the frozen codomain
  `Rows(M_1(Public, K))^{q_2}`: the row carrier is `StepRowsOne P K`, i.e.
  `M_1(Public, K)`'s own rows at this record's own `K`, and the width is the
  derived `q_2 = q2For P K` of `05:329--332`.  Balancedness (`07:218--220`) is
  **not** a field: `05:186--188` says it "remains a post-construction
  admissibility proposition; it is not a proof field of `Pi`".

No stored width, tolerance, multiplicity, capacity, ceiling or output-size
field appears, per `05:188--189`, and the type `LevelPublicInput V E -> Type`
names no `StageTwoWidths` and no `ScheduleContext`.

**Retyped at `cc-t7c-r3`** (gate item `#12`, `R1`): the four visible fields are
unchanged and were certified extensionally correct at `r2`; what moves is the
substrate under `c_2`'s type, from the deleted `ctxFor` to the direct
accessors of Part 1.

Reader counterpart: **none** (the reader never displays `Pi`; the nearest
sentence states balancedness, which is deliberately not a field -- the same
disposition `PublicRecords.LevelParams` records). -/
structure LevelParamsFor (P : LevelPublicInput V E) where
  /-- `K`, the six universal integer choices, as a **field** of `Pi`
  (`05:176`). -/
  K : LevelConfig
  /-- `N_2 in N_{>0}`, so that `L_2 = [N_2]` (`05:177--178`). -/
  N₂ : ℕ
  /-- `N_2 > 0`: structural, `05:183--186`. -/
  N₂pos : 0 < N₂
  /-- `c_2 : L_2 -> Rows(M_1(Public, K))^{q_2}` (`05:180--181`), the single
  indexed family, at the carrier and width computed from this record's own
  `K`. -/
  c₂ : Fin N₂ → Fin (q2For P K) → StepRowsOne P K

/-- **The banked fibre view of `Pi`.**  The same triple, presented as the
banked `PublicRecords.LevelParams` over the carrier and width this record's own
`K` determines.  Nothing is inserted: the `K` component is `Pi.K`, the record's
own field.

**Retyped at `cc-t7c-r3`** (gate item `#13`, `R1`): body and shape unchanged,
substrate moved to the direct accessors. -/
noncomputable def LevelParamsFor.toParams {P : LevelPublicInput V E}
    (Pr : LevelParamsFor P) :
    LevelParams (StepRowsOne P Pr.K) (q2For P Pr.K) where
  K := Pr.K
  N₂ := Pr.N₂
  N₂pos := Pr.N₂pos
  c₂ := Pr.c₂

/-- **Receipt (one configuration, and it is the record's own).**  The fibre
view's `K` component is `Pi.K`, definitionally -- not an ambient configuration
that happens to agree with it.  General in the public record and the parameter
record.  PROVED by `rfl`. -/
theorem levelParamsFor_toParams_K (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) : (Pr.toParams).K = Pr.K := rfl

/-- **The dependent-record equivalence (gate repair `R3`).**  `LevelParamsFor P`
is *equivalent*, not merely mapped, to the dependent sigma of the banked fibres
over the configuration, each cut down to the fibre's own coherent elements:

  `LevelParamsFor P  ≃  Σ K, {p : LevelParams (StepRowsOne P K) (q2For P K) // p.K = K}`.

The `cc-t7c-r2` gate's `R3` reads: "Replace it with an actual `Equiv` between
`LevelParamsFor P` and the appropriate dependent sigma/subtype representation;
no external `hK` hypothesis should remain at the theorem boundary."  There is
none: the coherence that the `r2` predecessor carried as an ambient
`hK : Pr.K = K` is the subtype clause on the fibred side, where it is part of
the object rather than a premise about it.

Both directions are exact.  Forward, a record goes to its own `K` together with
`toParams` and the `rfl` proof that the fibre element's configuration is that
same `K`; backward, a coherent fibre element over `K` becomes the record with
`K` as its field and the element's `N_2`, positivity and `c_2` unchanged.
Neither direction inserts, drops or transports anything -- the forward map's
target index *is* `Pi.K`, so no `cast` occurs at all.

This is the statement the fibre form cannot express, and it is what shows the
dependent record neither adds nor loses information relative to the banked one.
General in the public record.  PROVED. -/
noncomputable def LevelParamsFor.equivFibre (P : LevelPublicInput V E) :
    LevelParamsFor P ≃
      Σ K : LevelConfig,
        {p : LevelParams (StepRowsOne P K) (q2For P K) // p.K = K} where
  toFun Pr := ⟨Pr.K, ⟨Pr.toParams, rfl⟩⟩
  invFun x :=
    { K := x.1, N₂ := x.2.1.N₂, N₂pos := x.2.1.N₂pos, c₂ := x.2.1.c₂ }
  left_inv := by rintro ⟨K, N₂, hN₂, c₂⟩; rfl
  right_inv := by
    rintro ⟨K, ⟨K', N₂, hN₂, c₂⟩, hK⟩
    replace hK : K' = K := hK
    subst hK
    rfl

/-- **Non-vacuity (LANE-GATE 3), stated as generally as it is true.**  At every
public record, every configuration and every positive family size the parameter
record is inhabited **with that configuration and that family size**, so the
type is not inhabited only at a degenerate `N_2`, not only at some special
configuration, and not only at public records of some special shape.

The structural ingredients are paper-derived: `q_1 > 0` is the banked
`Stage1SlotBinding.q₁_pos` (from `a >= 3`), `m_R > 0` is `P3`'s own frozen
field (`05:36--37`), and `N_2 > 0` is the hypothesis.

**NON-FIDELITY, and registered as such.**  The least-row constant family is a
synthetic NON-FIDELITY inhabitant; it is not the paper's balanced-family
construction.  The paper's `Pi` carries a `(q_2, t_2, eps_2)`-balanced family
(`07:218--220`), whose existence argument is unbuilt, so the canonical
inhabitation stays the OPEN, REGISTERED `S5-BUNDLE-INHABITATION` row and is not
discharged here.  General in the public record, the configuration and the
family size.  PROVED. -/
theorem levelParamsFor_exists (P : LevelPublicInput V E) (K : LevelConfig)
    (N₂ : ℕ) (hN₂ : 0 < N₂) :
    ∃ Pr : LevelParamsFor P, Pr.K = K ∧ Pr.N₂ = N₂ :=
  ⟨{ K := K, N₂ := N₂, N₂pos := hN₂,
     c₂ := fun _ _ =>
       (⟨0, (stage1BindingFor P K).q₁_pos⟩, ⟨0, P.mRpos⟩) }, rfl, rfl⟩

/-! ## Part 5: the construction, step by step

Each definition is one frozen step, and each is a single application of a
banked constructor at the schedule's own evaluated data, except where the
header's inventory says otherwise.  Every one is bound to the paper's own pair
`(Public, Pi)` or, where the step does not read the family, to `(Public, K)`;
none is left on a context. -/

/-- **`y_0`, the least element of `Y_R = [n_R]`** (`08:33--38`): "Because
`Y_R = [n_R]` is nonempty, let `y_0` be its least element" and
`k_0(r) = y_0`.  `08:39--40` then rules that "`k_0` is the lexicographically
least selector value; it is constructor data derived from the public order, not
a proof-time choice" -- that sentence is on `08:39--40`, not inside the display
block `08:33--38`, which is the `cc-t7c` gate's record finding R9.

At the frozen zero-based carrier of `conv:finite-slots` the least element is
slot `0`, and `n_R > 0` is the `P3` field `LevelPublicInput.nRpos`
(`05:36--37`) that makes it exist.  The numeral `0` is `conv:finite-slots`' own
name for that least element, not a chosen value.

**Retyped at `cc-t7c-r3`** to the public record alone: `05:36--37`'s `n_R` and
`n_R > 0` are all this step ever read, so the configuration and the width
record both drop out of its binder list. -/
def stepSeedValue (P : LevelPublicInput V E) : Fin P.nR := ⟨0, P.nRpos⟩

/-- **`L5`** (`05:342--344`): "Construct the raw Stage-4 matrix `B` using the
guarded-source item vectors and the order-preserving rank injections
`pi_alpha` from `T2`."  The banked `RawStageFour.rawStageFourGuarded`, in which
both source-side objects are already pinned -- the item vectors to
`GuardedSourceSlab.guardedRow` and the injections to
`RawStageFour.rankInjection`, which is the `T2` rank `PublicRecords.slotEmbed`
retyped.  Its Stage-2 argument is the `L3` step `Section5Admissibility.stepMTwo`
at the `L2` matrix `stageOneFor` and the family stored in `Pi`, so no free
Stage-2 table can enter `B` here.

**Binder provenance (gate item `#18`, `R1`).**  `P` and `Pi` are the
procedure's own two inputs (`05:320`), and every schedule accessor is the
direct `(Public, K)` accessor of Part 1 at `K = Pi.K`, the record's own field.
The `r2` bytes routed the same body through the deleted `ctxFor`; the body is
unchanged and only the substrate moves. -/
noncomputable def levelStepB (P : LevelPublicInput V E) (Pr : LevelParamsFor P) :
    StepRowsB P Pr.K Pr.N₂ → StepColsB P Pr.K → Bool :=
  rawStageFourGuarded P.G (stage1BindingFor P Pr.K)
    (Nat.le_of_succ_le (four_le_stepScale P Pr.K)) P.R
    (stepMTwo (stageOneFor P Pr.K) Pr.c₂)

/-- **`L6`, first half** (`05:345`): "Apply the labelled protected duplication
to obtain `A`."  The banked `DenseStageFourOpening.protectedAFrozen`, which is
already the duplication at the three column and four row reservoirs of
`08:17--31`, at their banked inclusions, and at the frozen multiplicities of
`eq:protected-multiplicities`.  The frozen sentence "The value of `A` ignores
the reservoir label and multiplicity index and is the corresponding entry of
`B`" (`08:96--97`) is that banked definition and is not restated; it is read
back out at `levelStep_A_entry_is_B_entry` below.

**Binder provenance (gate item `#19`, `R1`).**  As for `levelStepB`, whose
corrected raw matrix this is rebased on. -/
noncomputable def levelStepA (P : LevelPublicInput V E) (Pr : LevelParamsFor P) :
    StepRowsA P Pr.K Pr.N₂ → StepColsA P Pr.K → Bool :=
  protectedAFrozen (levelStepB P Pr) (stepSeedValue P)

/-- **`L6`, stored map 1 of 4** (`05:346--347`, "Store the four explicit
forgetful and least-representative maps"): the row label-forgetting map
`f_A^row : Rows(A) -> Rows(B)`, the banked `DenseStageFourOpening.rowForget`
applied to the **three** banked row-reservoir inclusions `tempIncl`, `vertIncl`
and `blockIncl` that `protectedAFrozen` itself uses.

**Binder provenance (gate item `#20`, `R1`).**  `(P, Pi)` and nothing else: the
family size is read as `Pi.N_2` rather than bound freely, so this map cannot be
formed at a size the parameter record does not carry, and the configuration is
the record's own `Pi.K`. -/
noncomputable def levelStepFArow (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) :
    StepRowsA P Pr.K Pr.N₂ → StepRowsB P Pr.K Pr.N₂ :=
  rowForget (tempIncl (stage1BindingFor P Pr.K) V (Fin P.mR) (Fin Pr.N₂))
    (vertIncl (stage1BindingFor P Pr.K) V (Fin P.mR) (Fin Pr.N₂))
    (blockIncl (stage1BindingFor P Pr.K) V (Fin P.mR) (Fin Pr.N₂))

/-- **`L6`, stored map 2 of 4**: the row least-representative map
`r_A^row : Rows(B) -> Rows(A)`, the banked `DenseStageFourOpening.rowSection` --
`08:139`'s "selecting one representative of every underlying row" -- at the
base reservoir's zeroth multiplicity index.  Its side condition `0 < u_0` is
**derived**, not assumed: the banked `uBaseF_pos` computes it from
`eq:protected-multiplicities` and the four reservoir counts, whose
nonemptiness comes from `P1`'s `Nonempty V` (`05:21`, "`N_V, N_E in N_{>0}`,
`V = [N_V]`"), `P3`'s `m_R > 0` (`05:36--37`), the type of `Pi`
(`N_2 > 0`, `05:183--186`) and the frozen bin floor `4 <= s` (`04:389`).

**Binder provenance (gate item `#21`, `R1`).**  Same as `levelStepFArow`; the
map formula and its derived positivity proof are unchanged.

**Disclosure (record repair RF12, executed this round).**  The proof term
below contains `P.G.vertexNonempty.some`.  It is supplied **only** to the
banked `uBaseF_pos`, whose result is the proposition `0 < u_0`, and that
proposition is the `Prop` argument certifying that multiplicity index `0` is
legal.  The representative this map returns is always the base-labelled copy
at index `0`; neither its carrier coordinate nor its entry depends on the
vertex, so by proof irrelevance the witness is **not** construction data and
`02:95--99` ("Proof-only existential witnesses are not reused as construction
data") is respected.  The `cc-t7c-r3` gate ruled this declaration `CLEAR` on
exactly that reasoning and asked only that the module say so out loud. -/
noncomputable def levelStepRArow (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) :
    StepRowsB P Pr.K Pr.N₂ → StepRowsA P Pr.K Pr.N₂ :=
  rowSection (uBaseF_pos (stage1BindingFor P Pr.K)
    (four_le_stepScale P Pr.K)
    P.G.vertexNonempty.some (⟨0, P.mRpos⟩ : Fin P.mR)
    (⟨0, Pr.N₂pos⟩ : Fin Pr.N₂))

/-- **`L6`, stored map 3 of 4**: the column label-forgetting map
`f_A^col : Cols(A) -> Cols(B)`, the banked `DenseStageFourOpening.colForget` at
the same two banked column-reservoir inclusions `protectedAFrozen` uses --
`selIncl` at the frozen least selector value `k_0 = const y_0` of `08:33--38`,
and `diagIncl`.

**Retyped at `cc-t7c-r3`** from a `ScheduleContext` binder to `(P, K)`: the
`r2` gate ruled this declaration `CLEAR` as a general internal helper, but the
constructor consumes it, so on a context it would put a stored width record
into `levelStep`.  The body is unchanged. -/
noncomputable def levelStepFAcol (P : LevelPublicInput V E) (K : LevelConfig) :
    StepColsA P K → StepColsB P K :=
  colForget (selIncl (stage1BindingFor P K) (stepSeedValue P))
    (diagIncl (stage1BindingFor P K))

/-- **`L6`, stored map 4 of 4**: the column least-representative map
`r_A^col : Cols(B) -> Cols(A)`, the banked
`DenseStageFourOpening.colSection`.  Its side condition `0 < w_0` is likewise
**derived** by the banked `wBaseF_pos` from `w_0 = 182 S_0 D_0` and the
positivity of the derived ambient width `q_2` (`GuardedSourceSlab.q2_pos`, read
here as `q2For_pos`).

**Retyped at `cc-t7c-r3`** for the same reason as `levelStepFAcol`; the body
and its derived positivity proof are unchanged. -/
noncomputable def levelStepRAcol (P : LevelPublicInput V E) (K : LevelConfig) :
    StepColsB P K → StepColsA P K :=
  colSection (wBaseF_pos (stage1BindingFor P K) (q := q2For P K)
    (q2For_pos P K) (stepSeedValue P))

/-! ## Part 6: `T = LevelStep(Public, Pi)`

The `Postcondition` (`05:357--363`) is
`LevelOutput(Public, Pi) = LevelTrace(Public, Pi)`, "with exactly the fields of
`def:level-trace`.  There is no unnamed auxiliary-data component."  That record
is the banked `PublicRecords.LevelTrace`, and the assembly below fills every
one of its 23 data fields and every clause of `T1`--`T6`.

The assembly is stated **once**, in the declaration that claims
`proc:level-step`, at the direct accessors of Part 1.  The `r2` bytes stated it
in an internal adapter over an explicit stored width record and instantiated
that adapter at a chosen witness; both the adapter assembly and the erasure
receipt over it are deleted this round under the gate's own `R2` option. -/

/-- **`LevelStep(Public, Pi)`** (`proc:level-step`, `05:318--364`), the total
one-level constructor, delivered at the two frozen binding sites `05:385--386`
("Fix `Public`, `Pi = (K, N_2, c_2)`, and `T = LevelStep(Public, Pi)`") and
`05:721` ("With `T = LevelStep(Public, Pi)`").

*Precondition* (`05:320--322`): "A public input `Public` and a typed parameter
record `Pi`.  No admissibility proof is an input."  **The domain is exactly
that pair.**  There is no third argument: no configuration outside `Pi`, no
stored width record, no gate, no promise certificate, no width identification,
no coherence proof and no admissibility conjunct appears in the binder list.

*Where the schedule comes from* (gate item `#25`, `R1`).  Every accessor is the
direct `(Public, K)` accessor of Part 1 at `K = Pi.K`, the configuration
**field** of `Pi`.  No `StageTwoWidths` occurs in the unfolding of any of them,
which the twenty-five receipts of Part 1c certify in the kernel; this is
`05:104--106`'s straight-line program of `(Public, K)`, and it is what the `r2`
bytes claimed but did not have.

*Step by step.*  `L1` sets `S` to the banked guarded source and `C_2` to the
family stored in `Pi` -- "`LevelStep` never chooses a replacement"
(`05:338--340`); `T2` sets `pi_alpha` to the banked rank injection; `L2`
computes `M_1` at the schedule's own `(R, a, q_1, s)`; `L3` computes `M_2` by
the frozen value clause `07:225--226`; `L4` sets `M_3 = Int_s(M_2^T)`; `L5`
computes `B`; `L6` computes `A`, sets `N = A^T` (`05:346`) and stores the four
maps (`05:346--347`); `L7` sets `U = Int_q(N)` and `W = U^T` (`05:348`); `L8`
sets `R+ = Int_Q(W)^T` (`05:349`); `L9` computes `H` and both exact output
cardinalities.

*Widths, all evaluated and none stored.*  `a` is `aExpFor` (`eq:stage1-scales`,
`06:314`, through the **derived** `log_2 q_2`), `q` is `qFor` (`eq:q-deltaU`,
`06:515`) and `Q` is `QFor` (`eq:Q-theta-choice`, `06:529--532`); the ambient
`q_2` is `q2For`, the derived accessor of `05:329--332`, and `s` is `sFor` of
`06:118`.  No width is a free binder, and none is read from a stored field --
which is now structural rather than argued: no stored width record occurs in
this declaration's unfolding at all.

*Mutation* (`05:324--326`): the construction allocates fresh finite carriers
and Boolean matrices; it does not modify `G, R, D, Y, b_0, bout`, the fixed
orders, or `Pi`, and it never inspects a `YES` or `NO` certificate.  In Lean
this is structural: every argument is used only by being passed to a banked
constructor, and no promise-case object occurs in the definition. -/
noncomputable def levelStep (P : LevelPublicInput V E) (Pr : LevelParamsFor P) :
    LevelTrace P.G (sFor P Pr.K) Pr.toParams
      (StepColsOne P Pr.K) (StepRowsB P Pr.K Pr.N₂)
      (StepColsB P Pr.K) (StepRowsA P Pr.K Pr.N₂)
      (StepColsA P Pr.K)
      (aExpFor P Pr.K) (qFor P Pr.K) (QFor P Pr.K) where
  S := guardedRow P.G (sFor P Pr.K)
  C₂ := Pr.c₂
  π := slotEmbed P.G (Nat.le_of_succ_le (four_le_stepScale P Pr.K))
  M₁ := stageOneFor P Pr.K
  M₂ := stepMTwo (stageOneFor P Pr.K) Pr.c₂
  M₃ := stepMThree (stepMTwo (stageOneFor P Pr.K) Pr.c₂) (sFor P Pr.K)
  B := levelStepB P Pr
  A := levelStepA P Pr
  N := stepN (levelStepA P Pr)
  U := stepU (levelStepA P Pr) (qFor P Pr.K)
  W := stepW (levelStepA P Pr) (qFor P Pr.K)
  Rnext := stepRnext (levelStepA P Pr) (qFor P Pr.K) (QFor P Pr.K)
  fArow := levelStepFArow P Pr
  rArow := levelStepRArow P Pr
  fAcol := levelStepFAcol P Pr.K
  rAcol := levelStepRAcol P Pr.K
  pUrow := fun p => p.1
  pUcol := fun p => p.1 p.2
  pQrow := fun p => p.1
  pQcol := fun p => p.1 p.2
  H := aExpFor P Pr.K + Nat.log 2 (q2For P Pr.K) +
    Nat.log 2 (sFor P Pr.K) + Nat.log 2 (qFor P Pr.K) +
    Nat.log 2 (QFor P Pr.K)
  mnext := rowsCard (stepRnext (levelStepA P Pr) (qFor P Pr.K) (QFor P Pr.K))
  nnext := colsCard (stepRnext (levelStepA P Pr) (qFor P Pr.K) (QFor P Pr.K))
  S_eq := rfl
  C₂_eq := rfl
  π_eq := fun α i =>
    slotEmbed_val P.G (Nat.le_of_succ_le (four_le_stepScale P Pr.K)) α i
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

/-! ## Part 7: the aux-lemma battery

Five general properties of the constructor, all proved, all general in the
public record and the parameter record.  Aux 1 is the composition claim; Aux 2
and Aux 3 are the two statements that are **only** true of this composition and
are false of a free `LevelTrace`; Aux 4 is the derived-seam readout; Aux 5 is
non-vacuity of every carrier the constructor returns.  Three further proved
properties of the parameter record sit in Part 4
(`levelParamsFor_toParams_K`, `LevelParamsFor.equivFibre`,
`levelParamsFor_exists`), and the twenty-five substrate receipts sit in Part
1c.

**Statement pole.**  No declaration in this module is an existential
deliverable except `levelParamsFor_exists`, whose non-triviality is that it
delivers a record at a **prescribed** configuration and a **prescribed** `N_2`,
so no single fixed inhabitant supplies it.  `levelStep` is a named constructor
and every theorem below is an equation or a nonemptiness fact about it, so
there is no witness a trivial inhabitant could supply.  The nearest thing to a
trivial competitor is Aux 5's "some carrier is nonempty", which is why Aux 5 is
stated for **all six** carriers at once, including the two labelled Section-8
carriers whose nonemptiness needs the frozen `4 <= s`. -/

/-- **Aux 1 (the eight constructed objects are the banked constructors, on the
nose).**  Every object `proc:level-step` names in `L1`--`L6` and `T2` is the
banked constructor at the paper's own arguments: nothing is re-derived, nothing
is replaced, and no step accepts an arbitrary matrix.  This is the composition
claim of the whole module, in the kernel.

**Retyped at `cc-t7c-r3`** (gate item `#27`, `R1`): the eight conjuncts are
unchanged and only their substrate moves to the direct accessors.  General in
the public record and the parameter record.  PROVED by `rfl`. -/
theorem levelStep_steps_are_banked (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) :
    (levelStep P Pr).S = guardedRow P.G (sFor P Pr.K) ∧
      (levelStep P Pr).C₂ = Pr.c₂ ∧
      (levelStep P Pr).π =
        slotEmbed P.G (Nat.le_of_succ_le (four_le_stepScale P Pr.K)) ∧
      (levelStep P Pr).M₁ = stageOneFor P Pr.K ∧
      (levelStep P Pr).M₂ = stepMTwo (stageOneFor P Pr.K) Pr.c₂ ∧
      (levelStep P Pr).M₃ =
        stepMThree (stepMTwo (stageOneFor P Pr.K) Pr.c₂) (sFor P Pr.K) ∧
      (levelStep P Pr).B = levelStepB P Pr ∧
      (levelStep P Pr).A = levelStepA P Pr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Aux 2 (`L2`--`L4` resolve all the way down to the public seed matrix).**
The Stage-3 entry of the constructed trace is an entry of the public record's
own `R`, at the coordinate the stored family and the Stage-1 slot inclusion
name -- and at no free object whatsoever.

Reading the chain: `M_3((i,l), x) = M_2(x(i), l)` is `def:interlace`'s value
clause at `S_2 = M_2^T` (`07:497`, `08:262`); `M_2((alpha,gamma), l) =
M_1(c^{(l)}(alpha), gamma)` is `eq:stage2-relaxed-value`'s third line
(`07:225--226`); and `M_1((j,y), gamma) = R(y, gamma(iota_1(j)))` is
`eq:stage1-universes-and-value`'s third line (`07:145`).  Composing them at
`x(i) = (alpha, gamma)` gives the displayed right-hand side.

This is the statement that is **false of a free trace**: in
`PublicRecords.LevelTrace` the field `M_1` is an arbitrary `Bool`-matrix on a
free carrier, so no equation can express its entries through `P.R`.  It becomes
provable exactly because `L2` is computed rather than accepted.

**Retyped at `cc-t7c-r3`** (gate item `#28`, `R1`); the equation is unchanged.
General in the public record, the parameter record, and the three indices.
PROVED by `rfl`. -/
theorem levelStep_M₃_resolves_to_source (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) (i : Fin (sFor P Pr.K)) (ℓ : Fin Pr.N₂)
    (x : Fin (sFor P Pr.K) → Fin (q2For P Pr.K) × StepColsOne P Pr.K) :
    (levelStep P Pr).M₃ (i, ℓ) x =
      P.R (Pr.c₂ ℓ (x i).1).2
        ((x i).2 ((stage1BindingFor P Pr.K).iota₁ (Pr.c₂ ℓ (x i).1).1)) :=
  rfl

/-- **Aux 3 (`08:96--97` at the constructed objects: `A`'s value ignores the
reservoir label and the multiplicity index).**  Every entry of the labelled
duplicate is the entry of the raw Stage-4 matrix at the two *stored* forgetful
maps of `L6` -- so the trace's `A`, `B`, `f_A^row` and `f_A^col` fields are
four views of one object rather than four independent data.

This too is **false of a free trace**: `def:level-trace` types `B`, `A`,
`f_A^row` and `f_A^col` at unrelated carriers and imposes only the two
retraction clauses `T4`, which say nothing about entries.

**Retyped at `cc-t7c-r3`** (gate item `#29`, `R1`); the equation is unchanged.
General in the public record, the parameter record, and the two indices.
PROVED by `rfl`. -/
theorem levelStep_A_entry_is_B_entry (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) (r : StepRowsA P Pr.K Pr.N₂)
    (c : StepColsA P Pr.K) :
    (levelStep P Pr).A r c =
      (levelStep P Pr).B ((levelStep P Pr).fArow r) ((levelStep P Pr).fAcol c) :=
  rfl

/-- **Aux 4 (the public integer is at the derived seam, in all five
summands).**  `L9`'s `H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`
(`05:352`) at this schedule's own evaluated quantities, with **every** schedule
width taken from the `(Public, K)`-direct chain: `a` is `aExpFor` (the `06:314`
chain routed through the derived `log_2 q_2` of `05:329--332`), `q` is `qFor`
and `Q` is `QFor` (the `06:431--432` / `06:467--471` / `06:515` / `06:529--532`
chain routed through the same derived accessor).

The `cc-t7c` bytes stated this lemma with `qOf` and `QOf`, which reach
`C.W.r_2` through `LPOf -> P0Of -> lq2Of`; that is the defect the `cc-t7c` gate
returned, and the `cc-t7c-r1` gate certified the corrected display and its five
summands as mathematically correct.  **Retyped at `cc-t7c-r3`** (gate item
`#30`, `R1`); the display is unchanged.  General in the public record and the
parameter record.  PROVED by `rfl`. -/
theorem levelStep_H_at_derived_exponent (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) :
    (levelStep P Pr).H =
      aExpFor P Pr.K + Nat.log 2 (q2For P Pr.K) +
        Nat.log 2 (sFor P Pr.K) + Nat.log 2 (qFor P Pr.K) +
        Nat.log 2 (QFor P Pr.K) :=
  rfl

/-- **Aux 5 (non-vacuity: the constructor never returns an empty matrix).**
All six carriers of the constructed trace are inhabited, at every public record
and every parameter record -- so no step of `proc:level-step` produces a matrix
with no rows or no columns, and the retractions `r_A^row`, `r_A^col` of `T4`
are sections of nonempty carriers rather than of empty ones.

Every inhabitant exhibited below is **paper-derived**: `q_1 > 0` is the banked
`Stage1SlotBinding.q₁_pos` (from `a >= 3`), `m_R > 0` and `n_R > 0` are `P3`'s
own fields (`05:36--37`), `N_2 > 0` is part of the type of `Pi`
(`05:183--186`), `0 < s` and `4 <= s` are the frozen floor (`04:389`), the
seed value is the frozen least element `y_0` of `08:33--38`, every other
coordinate is the least element `0` of a positive zero-based carrier
(`conv:finite-slots`), and `0 < q_2` is the banked `q2_pos` at the derived
width of `05:329--332`.  The two labelled carriers additionally need the frozen
`4 <= s`, because the blocker reservoir of `08:24` is indexed by
`I_B = [4s] x [s-3]` (`04:396` with the blocker ranges `r in [4s]`,
`k in [s-3]` of `04:491--492`; `08:566--567` gives `|I_B| = 4s(s-3)`).

**Disclosure (record repair RF12, executed this round).**  The `cc-t7c-r3`
bytes wrote "and none is chosen", which over-claimed.  The proof below does use
`P.G.vertexNonempty.some`, from `P1`'s `Nonempty V`, in the single place the
banked `uBaseF_pos` needs a vertex; its result is the proposition
`0 < u_0`, so by proof irrelevance the witness reaches no exhibited
inhabitant.  The accurate claim is: **no inhabitant exhibited here depends on a
choice; one proof-only vertex witness discharges a positivity side condition.**
The `cc-t7c-r3` gate ruled this declaration `CLEAR` on exactly that ground and
asked only for the disclosure.

**Retyped at `cc-t7c-r3`**, which the `cc-t7c-r1` gate marked `CLEAR` with the
note "A later retyping is mechanical": the statement, the six conjuncts and
every inhabitant are unchanged, and only the schedule's source moved.  General
in the public record and the parameter record.  PROVED. -/
theorem levelStep_carriers_nonempty (P : LevelPublicInput V E)
    (Pr : LevelParamsFor P) :
    Nonempty (StepRowsOne P Pr.K) ∧
      Nonempty (StepColsOne P Pr.K) ∧
      Nonempty (StepRowsB P Pr.K Pr.N₂) ∧
      Nonempty (StepColsB P Pr.K) ∧
      Nonempty (StepRowsA P Pr.K Pr.N₂) ∧
      Nonempty (StepColsA P Pr.K) := by
  have hq : 0 < q2For P Pr.K := q2For_pos P Pr.K
  have hu : 0 < uBaseF (stage1BindingFor P Pr.K) V (Fin P.mR) (Fin Pr.N₂) :=
    uBaseF_pos (stage1BindingFor P Pr.K) (four_le_stepScale P Pr.K)
      P.G.vertexNonempty.some (⟨0, P.mRpos⟩ : Fin P.mR)
      (⟨0, Pr.N₂pos⟩ : Fin Pr.N₂)
  have hw : 0 < wBaseF (stage1BindingFor P Pr.K) (q2For P Pr.K) (Fin P.nR) :=
    wBaseF_pos (stage1BindingFor P Pr.K) hq (stepSeedValue P)
  refine ⟨⟨(⟨0, (stage1BindingFor P Pr.K).q₁_pos⟩, ⟨0, P.mRpos⟩)⟩,
    ⟨fun _ => stepSeedValue P⟩,
    ⟨Sum.inl (⟨0, (stage1BindingFor P Pr.K).s_pos⟩, ⟨0, Pr.N₂pos⟩)⟩,
    ⟨(fun _ => stepSeedValue P,
      fun _ => (⟨0, hq⟩, fun _ => stepSeedValue P))⟩,
    ⟨Sum.inl (Sum.inl (⟨0, (stage1BindingFor P Pr.K).s_pos⟩,
      ⟨0, Pr.N₂pos⟩), ⟨0, hu⟩)⟩,
    ⟨Sum.inl ((fun _ => stepSeedValue P,
      fun _ => (⟨0, hq⟩, fun _ => stepSeedValue P)), ⟨0, hw⟩)⟩⟩

/-! ## Part 8: the canonical order on `Rows(M_1)` (`12:93--98`), the missing
input of the increasing equivalence `e_i` of `14:1626`

**Round marker (true lineage), added this round as finding `F7` requires.**
Part 8 was **authored at `cc-t8b`**, ruled `CLEAR` on all seven declarations by
that tranche's gate, and **parked** with the tranche under its `BLOCK` verdict
(which fell on other lanes and on Part 13, never on these seven).  It is
**repaired and banked at `cc-t8c`**.  The delta between the two rounds is
exactly this marker (`F7`: no round marker was present at all) and the
corrected opt-in paragraph below (`F8`).  **No statement, type, body or proof
term of the seven declarations changes**, and no line number, quotation or
anchor below is inherited: every frozen line cited in this part was re-opened
first-hand at the bytes this round.

### The frozen convention, read first-hand this round

`sec:canonical-reindexing` (`12:85--104`) fixes the order every `LevelStep`
carrier carries: "Every carrier constructed by `LevelStep` has the recursive
canonical order fixed in `def:level-public-input`, `def:level-trace`: initial
segments use their natural order, tagged sums are ordered first by tag and then
within a tag, **products use lexicographic order**, finite function spaces use
lexicographic order in increasing coordinate order, and subtypes use the
induced order" (`12:93--98`).  `14:166--168` states the same rule for the
descriptor carriers ("initial segments have increasing order, sums use tag
order, products and function spaces use lexicographic order"), and `04:393`
repeats it inside `def:guarded-source-constructor` ("order every product and
disjoint union lexicographically").  Three independent frozen sites, one rule.

`12:98--104` is what the rule buys: "if `X` is one of these nonempty carriers,
there is a unique increasing equivalence `e_X : [|X|] -> X`.  This equivalence
is determined by the carrier itself; it is not an additional choice and cannot
depend on a YES or NO certificate."

### Why this belongs here and what it unblocks

`Rows(M_1) = [q_1] x Rows(R)` (`eq:stage1-universes-and-value`, `07:144`) is a
**product**, so the rule applies to it verbatim: the primary key is the Stage-1
slot `[q_1]` and the secondary key is `Rows(R) = [m_R]`, each an initial segment
in its natural order under `conv:finite-slots` (`02:14--18`).  The banked
`IteratedCanonicalChaining.canonOrderEquiv` / `.canonEquiv` take that order as
an ambient `LinearOrder` instance -- their own header records the omission as
`GAP-EXPOSED 2` -- and `StepRowsOne`, this module's own name for `Rows(M_1)`,
carried no such instance.  Supplying it is the one missing input of `e_i` at
`14:1626`, so it is authored by the module that owns the carrier rather than by
a consumer.

**Opt-in, deliberately, and the reason is a measured one.**  The order is a
plain `def` in the nested namespace `CanonicalRowOrder`, and **this part
performs no instance promotion whatsoever**.

  (**Record repair `F8`, executed this round.**  The `cc-t8b` bytes wrote that
  the order is "promoted to an instance only by a section-scoped
  `attribute [local instance]` here and by the same one-line opt-in at each
  consumer".  The first half was false and is withdrawn: no `attribute`
  command occurs in this part, and none occurs anywhere in this module.  The
  accurate statement, which is what these bytes assert, is the one below.)

Nothing in this module promotes `stepRowsOneOrder`, and nothing exports it.  A
consumer that wants the order opts in **locally**, inside its own `section`,
with its own one-line `attribute [local instance]`; the only consumer on the
route today is `BalancedFamilyBuilder`'s Part 13, whose promotion is confined
to that module's own `section LevelStepStorage` and reaches no third module.

The reason for that discipline is a measurement, re-run at the bytes this
round: Mathlib already puts the *pointwise* product order on `X x Y`, so with
`stepRowsOneOrder` inactive `x <= y` at `StepRowsOne P K` elaborates against
Mathlib's `Prod` instance to the pointwise relation `x.1 <= y.1 ∧ x.2 <= y.2`,
which is not total.  A globally exported lexicographic instance would silently
change the meaning of `<=` for every product of finite slot types on the route.
`stepRowsOneOrder_le_iff` below is the kernel guard that inside the opt-in the
relation really is the frozen lexicographic one and not the pointwise one: the
two right-hand sides differ, so the `iff` cannot typecheck against the wrong
instance.

**Nothing about the parameter record changes.**  No balanced-family clause, no
Stage-2 structural gate, no admissibility proposition is stated, implied or
assumed here; this part is the carrier's order and nothing else.  In
particular this part authors no `A_bal` call, no stored family and no `Pi`
record, and it does not weaken the module header's disposition on
`levelParamsFor_exists`.

Reader counterpart: **none claimed.**  The frozen reader's only sentence at this
layer is `reader-facing/sections/C-effectivity-details.tex:7--8` ("Every carrier
is ordered, so quotient--remainder decoding and least representatives are
canonical"), opened first-hand this round in the **pinned release copy** -- and
appendix-preamble prose is never cited as a statement on this route
(`PublicRecords.lean:79--85`).  No reader item is assigned to any declaration
below. -/

namespace CanonicalRowOrder

/-- **The canonical order on `Rows(M_1) = [q_1] x Rows(R)`** (`12:96`,
`14:167`, `04:393`): the lexicographic order of the two frozen keys, transported
onto the product by Mathlib's `Prod.Lex` linear order along `toLex`.

Field-free and choice-free: the order is a function of the carrier's own
descriptor (`[q_1]` then `[m_R]`, both initial segments in the natural order of
`conv:finite-slots`), which is exactly what `12:103--104` demands of the data
`e_X` is computed from.  The two keys are the schedule's own: `q_1` is the
banked `Stage1SlotBinding.q₁` at `stage1BindingFor P K` and `m_R` is `P3`'s own
field (`05:36--37`); neither is a value chosen here.

A `def` and not an exported instance, for the diamond reason recorded in the
Part-8 block docstring; this part promotes it nowhere.  `@[reducible]` is the
Mathlib convention for a class-valued `def` that consumers promote to an
instance locally (the "reducible non-instance" note); without it Lean warns at
the declaration and the local promotion is unsound as an instance.  General in
the public record and the configuration. -/
@[reducible] noncomputable def stepRowsOneOrder (P : LevelPublicInput V E)
    (K : LevelConfig) : LinearOrder (StepRowsOne P K) :=
  LinearOrder.lift'
    (fun x => (toLex x : Lex (Slot (stage1BindingFor P K).q₁ × Fin P.mR)))
    (Equiv.injective toLex)

/-- **The order relation of `stepRowsOneOrder`, spelled without notation.**

`<=` notation is deliberately *not* used for this relation anywhere on the
route: with the canonical order inactive, `x <= y` at `StepRowsOne P K`
elaborates to Mathlib's *pointwise* product order, and that silent substitution
is exactly the failure mode this part exists to close.  Naming the projection
chain makes every statement below say which order it is about.  Not a second
order: this is `stepRowsOneOrder`'s own `LE` field, reached by the generated
parent projections. -/
abbrev stepRowsOneLe (P : LevelPublicInput V E) (K : LevelConfig)
    (x y : StepRowsOne P K) : Prop :=
  @LE.le _ (stepRowsOneOrder P K).toPartialOrder.toPreorder.toLE x y

/-- **The strict order relation of `stepRowsOneOrder`**, spelled the same way. -/
abbrev stepRowsOneLt (P : LevelPublicInput V E) (K : LevelConfig)
    (x y : StepRowsOne P K) : Prop :=
  @LT.lt _ (stepRowsOneOrder P K).toPartialOrder.toPreorder.toLT x y

/-- **Aux 1 (fidelity: the order IS the frozen one).**  The canonical `<=` on
`Rows(M_1)` is the lexicographic clause of `12:96` read literally -- strictly
smaller Stage-1 slot, or equal Stage-1 slot and `<=` in `Rows(R)`.

This is the statement pole of the whole part.  Mathlib's default *pointwise*
product order would make the right-hand side `x.1 <= y.1 ∧ x.2 <= y.2`, a
different relation (not even total), so this `iff` fails outright if
`stepRowsOneOrder` is not the lexicographic one.  General in the public record,
the configuration and the two rows.  PROVED. -/
theorem stepRowsOneOrder_le_iff (P : LevelPublicInput V E) (K : LevelConfig)
    (x y : StepRowsOne P K) :
    stepRowsOneLe P K x y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2) :=
  Prod.Lex.toLex_le_toLex

/-- **Aux 2 (the strict form).**  The same readback for `<`, which is the
relation the word *increasing* in `12:99` quantifies over.  General.  PROVED. -/
theorem stepRowsOneOrder_lt_iff (P : LevelPublicInput V E) (K : LevelConfig)
    (x y : StepRowsOne P K) :
    stepRowsOneLt P K x y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) :=
  Prod.Lex.toLex_lt_toLex

/-- **Aux 3 (monotonicity in the primary key).**  The Stage-1 slot is the
primary key: it can never decrease along the order.  General in the public
record, the configuration and the two rows.  PROVED. -/
theorem stepRowsOneOrder_fst_mono (P : LevelPublicInput V E) (K : LevelConfig)
    {x y : StepRowsOne P K} (h : stepRowsOneLe P K x y) : x.1 ≤ y.1 := by
  rcases (stepRowsOneOrder_le_iff P K x y).mp h with h₁ | ⟨h₁, _⟩
  · exact le_of_lt h₁
  · exact le_of_eq h₁

/-- **Aux 4 (the least element is the zero-based origin).**  `Rows(M_1)` has a
bottom, and it is the pair of zero slots of `conv:finite-slots` (`02:14--18`) --
the same zero-based origin `levelStep_carriers_nonempty` exhibits for this
carrier.  Consequently the increasing equivalence `e_i` of `14:1626` sends
`0 in [m_{1,i}]` to `(0,0)`, so the storage step's reindexing has a computed
base point rather than a chosen one.

Non-degenerate: both components are inhabited for *derived* reasons --
`Stage1SlotBinding.q₁_pos` and `P3`'s own `m_R > 0` (`05:36--37`) -- so this is
not a statement about an empty carrier.  General.  PROVED. -/
theorem stepRowsOne_origin_le (P : LevelPublicInput V E) (K : LevelConfig)
    (x : StepRowsOne P K) :
    stepRowsOneLe P K
      ((⟨0, (stage1BindingFor P K).q₁_pos⟩, ⟨0, P.mRpos⟩) : StepRowsOne P K) x := by
  rw [stepRowsOneOrder_le_iff]
  by_cases h : (x.1 : ℕ) = 0
  · refine Or.inr ⟨Fin.ext h.symm, ?_⟩
    simp [Fin.le_def]
  · left
    simp only [Fin.lt_def]
    omega

end CanonicalRowOrder

end EthInapproximability.ParameterizedNP.LevelStepConstruction
