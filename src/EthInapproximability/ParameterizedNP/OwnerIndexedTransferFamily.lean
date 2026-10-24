import EthInapproximability.ParameterizedNP.OwnerMassTransfer

/-!
# Parameterized NP route: the outer-copy indexing layer and the owner-indexed
transfer family

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche).  Every anchor below was opened
  first-hand in that file for this tranche.

  This module is **round 4** of the mass-redistribution segment and lands the
  three items the predecessor `OwnerMassTransfer` (`OWNER-MASS-TRANSFER-001`)
  registered as GAP-EXPOSED 1, 4 and as the parked judge finding **F3**.  It
  introduces **no new frozen display**: every statement below is one of the
  predecessor's own conclusions re-derived with a binder removed.

  The anchors traced here, in the order the frozen text prints them:

  * **`09:105--108`**, the outer-copy indexing layer: "Let `q = 2^r` be the
    scale-alignment width and set `U = Int_q(N)`."  Both the width and the
    matrix are already banked -- `ScaleAlignOpening.scaleAlignWidth` (`09:105`)
    and `ScaleAlignOpening.wrapperU` (`09:107`) -- and are consumed **by pin**;
    this module defines no second interlace and no second width.  What is new is
    that the wrapper's donor index is read *through* that interlace: the outer
    coordinate of a routed certificate is a `Slot (scaleAlignWidth r)`, i.e. an
    outer copy of `U`, and the game the residual comparison compares against is
    `subgame (wrapperU N r)` rather than a free `interlaceFun`.
  * **`09:1238--1239`**, "At remaining selector capacity `2^k`, a certificate consists
    of at least `A_k` reference rows **in one outer coordinate**" -- the frozen
    sentence that makes `RoutedCertificate.coord` the donor's outer copy, hence
    makes `donorCoord` a **derived** map and not the free binder `crd` the
    predecessor carried.
  * **`09:1235--1236`**, "Start one clean reference certificate in every coordinate
    outside `E_0`, each with weight one", read against **`09:1519`**, "Let
    `J_clean` be the `c` **outer coordinates** whose clean reference
    certificates reach final Alice nodes" -- the frozen text indexes clean
    donors *by outer coordinate*.  In this development the donor index `iota`
    and the coordinate carrier are separate types, and **the full
    identification is not encoded as a hypothesis of any declaration below**
    (record repair R1 of the r0 statement gate, narrowed by R9 of the r1 gate):
    `Function.Injective (donorCoord S)` occurs only as the local hypothesis
    `hinj` of the general cardinality readout
    `donorCoord_card_le_of_injective`.  What §4b *does* carry, per index, is the
    strictly weaker **pairwise** slice at the fixed donor `j`: the binder
    `hOuter`, saying `donorCoord S i != donorCoord S j` for every `i` in
    `(goodDonors S Pv etaR).erase j`.  That is a visible, frozen-grounded
    hypothesis (`09:1643--1644`, `09:1653--1655`), satisfied at the paper's own
    instance, and it does **not** give injectivity.  §5's
    `coordUnique_is_vacuous_on_distinct_clean_donors` proves that the banked
    `RoutedSystem.coordUnique` cannot supply the full identification either, so
    the frozen indexing survives as GAP item 2 and not as a carried binder.
  * **`09:1550--1552`**, "Every clean reference certificate has a unique final
    node, its *owner*" -- the source of the derived `hv`, `hcol` and residual
    budget of §2.
  * **`09:1643--1679`**, the transfer trigger, the terminal-state
    identification and the transfer bound, consumed **by pin** through the
    banked `OwnerMassTransfer.ownerTerminalState` and
    `OwnerMassTransfer.ownerTransfer_lt_engine`.
  * **`09:1670--1671`**, "the structural gates give `q_2 >= 16` and
    `lambda_0 <= 1/8`" -- the frozen sentence that supplies `hq_2` at the call
    site (banked as `WrapperMassRedistribution.structuralReadout`), which is
    exactly the **F3 route**.
  * **`09:1690--1699`**, `eq:wrapper-good-to-good`, and **`09:1700--1701`**, the
    combination with `eq:wrapper-mass-leaves-owner`, both consumed by pin from
    the predecessor and restated nowhere.

* **Cross-anchors opened first-hand for this tranche:** `09:1250--1252` (the two
  stopping rules, the banked `RoutedSystem.node_isAlicePath` and
  `final_residual_budget`); `09:1330--1331` ("no Bob query has occurred on the
  route to this node"), which is what makes the column half of the owner
  rectangle derivable; `09:1339` (the frozen floor `C >= 3`);
  `09:1519--1520`, `09:1548`, `09:1553`; `09:1618--1625`
  (`eq:wrapper-owner-threshold`); `09:658--704`
  (`lem:terminal-state-realization`); `09:1777--1778` (the budget identity
  behind `TerminalTwoStream.terminalTarget`); `06:1213--1218` and `09:256--258`
  (where `eq:wrapper-owner-gates` is discharged and assumed respectively).

## What this module adds, item by item

The predecessor's own GAP list is the specification.  Three of its items move.

1. **GAP 1 (M1), the outer-copy indexing, is now a layer and not a binder.**
   `crd : iota -> Slot q` was a free function; it is replaced by
   `donorCoord S i = (S.cert i).coord`, *derived* from the routed certificate
   system, and the width is pinned to the frozen `q = scaleAlignWidth r` of
   `09:105` so that a donor coordinate is literally an outer copy of the banked
   `wrapperU`.  The owner rectangle's **column** section obligation and the
   frontier facts around it are derived as well (§2): `hv`
   (`owner_not_firstBob`), the residual budget (`owner_residual_budget`), and
   `hcol` (`ownerCols_derived`) all follow from `09:1250--1252` and
   `09:1550--1552`.  What genuinely does **not** derive is recorded, not
   papered over: the row sections `iotaA` and the games `hgame` stay explicit
   binders, while the coordinate injectivity of `09:1235--1236` is **not encoded
   at all** (R1) -- §5 proves it is *not* implied by the banked `coordUnique`,
   so it stays an open GAP item rather than becoming a hypothesis.
2. **GAP 4, the per-owner transfer family, is derived and no longer supplied.**
   `goodToGood_engine_derived` reaches `eq:wrapper-good-to-good` **without an
   `htrans` hypothesis**: the whole family
   `Pv (own i) j < 2 mu_P delta_i  (i in J_good \ {j})` is produced inside the
   proof by quantifying the banked `ownerTransfer_lt_engine` over
   `i in J_good \ {j}` (`ownerTransfer_family`).  The predecessor's prescription
   for this round was exactly "quantify `ownerTransfer_lt_engine` over
   `i in J_good` once the outer-copy indexing lands", and item 1 is what makes
   it possible: the frozen `eps_i` of the family is read at the *derived*
   coordinate `donorCoord S i`.
3. **The §4 -> §5 seam is closed in actual proof terms, and F3 with it.**
   `ownerStateOf` builds the predecessor's `hstateOf` binder by *calling*
   `ownerTerminalState`, with `hq_2` obtained at the call site from the banked
   `WrapperMassRedistribution.structuralReadout` (`09:1670--1671`) and
   `hEpsLtOne` obtained from the banked `ordinaryDeficit_lt_one`.  This is the
   **F3 route**: the parked finding asked for `hq_2 : 0 < W.q_2` to stop being a
   binder, and it is discharged here **without opening**
   `ownerTerminalState` -- the banked declaration is untouched, byte for byte,
   and the discharge happens in the consumer.  `ownerTransfer_lt_of_realization`
   then composes the produced `hstateOf` into `ownerTransfer_lt_engine`, so the
   two sections demonstrably compose rather than merely coexisting.

## Repair round r1: what changed against the parked generation

The r0 statement gate returned REVISE on two of twenty-nine declarations,
`ownerStateOf` and `ownerTransfer_lt_of_realization`, on finding **F1**, and
recorded eight record findings.  This generation is the parked generation with
exactly the following changes; every other declaration's statement and proof is
byte-stable.

1. **F1 (mathematics).**  Both declarations bound a *single* natural `dFor`
   outside the `forall Rf` of `hRegF`, so the premise bundle demanded
   `d_Sigma = d_D` at the fixed bin `pFor`.  `RegularOn` is an **exact** fibre
   count, and the frozen `09:725--732` prints
   `d_G = w_0 |K_R| |J_2|^{s-1}`, `d_Sigma = w_Sigma |J_2|^{s-1}`, `d_D = w_D`,
   with `08:100--102` fixing `w_Sigma = M_0 D_0` and `w_D = M_0 S_0`; those are
   equal only if `D_0 |J_2|^{s-1} = S_0`, which no frozen gate imposes.  The
   degree is therefore the reservoir-indexed `dF : Finset Rw -> N`, with both the
   regularity and the positivity quantified over the reservoir.  The banked
   `OwnerMassTransfer.ownerTerminalState` takes `{Rf}` and `{dFor}` implicit, so
   `(hRegF Rf hProt)` and `(hdF Rf hProt)` unify it per branch at `dF Rf`; the
   banked declaration is untouched.  §5 proves both halves of the finding as
   theorems: `singleForeignDegree_collapses_the_two_reservoirs` and
   `foreignDegrees_may_differ`.
2. **R6 (scope).**  `ownerTransfer_lt_of_realization` was consumed by nothing,
   because the endpoints ran through `ownerTransfer_family`, which re-introduces
   `hstateOf` as a per-index binder.  §4b adds
   `ownerTransfer_family_of_realization`, `goodToGood_engine_of_realization` and
   `goodDonor_mass_to_exceptional_of_realization`, which take the per-index
   realization data and call `ownerStateOf` once per index -- so the §4 -> §5 seam
   now travels in actual proof terms all the way to `09:1701`, carrying the F1
   repair with it.  The parked binder-form declarations are kept unchanged as
   the weaker interface.
3. **R7 (width identification).**  The two new endpoints take `09:105`,
   `09:1250` and `09:1264` at the one width the frozen paper identifies.
4. **R1--R5 (record only).**  Header, GAP list, axiom-surface list and four
   docstrings corrected; no statement and no proof was touched by these.  The
   line-number citation of the fibre degrees is `09:725--732` throughout (R3).

## What this module deliberately is not

* **No new frozen mathematics.**  Every conclusion below is a conclusion of
  `OwnerMassTransfer`, `WrapperMassRedistribution`, `MassRedistributionCounting`
  or `RoutedCertificateSystem`, reached with fewer hypotheses.  No display of
  the frozen paper is transcribed here for the first time, and no constant,
  carrier or gate is redefined.
* **`lem:terminal-two-stream` stays BINDER-ONLY.**  The banked
  `TerminalTwoStream.TerminalTwoStream` is *stated and not proved*
  (`TERMINAL-TWO-STREAM-001`); it enters the family as the indexed hypothesis
  `hTTS` and nothing here upgrades it.  The frozen conditional shape -- *if* the
  transfer is large, *then* the owner is hard -- is preserved at every index;
  §5's `ownerFamily_unconditional_hardness_is_contradictory` shows that
  flattening it at any single index already makes the bundle inconsistent.
* **`hDenseRung` is neither discharged nor fed by this module.**  `DenseRung`
  (the `eq:wrapper-u-dense` endpoint) falls only at the genuine end of the
  mass-redistribution segment; nothing below mentions it, `eq:wrapper-u-dense`
  is concluded nowhere, and **no route completion is claimed**.  Steps 7--9 of
  the segment (`09:1702--1781`) are untouched: the `e_T = 0` contradiction of
  `09:1702`, the pigeonhole and `eq:wrapper-terminal-density` of
  `09:1704--1713`, the schedule layer of `09:1715--1744` and the final
  Extension call of `09:1746--1781` are all outside this tranche.
* **`R5` is not leaned on.**  The predecessor's R5 audit instance
  (`r5_seven_binders_live`, `r5_eighth_binder_fails_here`) is a **NON-FIDELITY /
  BEYOND-PAPER** probe whose eighth item is provably false at that point; no
  declaration below consumes it, mentions it, or treats the seven exhibited
  items as an inhabitant of anything.

## GAP-EXPOSED, carried forward

1. **The row sections and games stay binders.**  `iotaA`, `hgame` (and the
   computed function `gamb`) are the frozen reading of the owner's copy of `N`
   inside the wrapper's carriers; the transcript-level construction that would
   produce them is unbuilt.  The **column** half is now derived, and that is the
   whole of what `09:1330--1331` supplies.
2. **`09:1235--1236`'s "one certificate per coordinate" is NOT ENCODED (R1,
   narrowed by R9).**  The frozen indexing of `09:1235--1236`/`09:1519` is *not*
   derivable from the banked `RoutedSystem.coordUnique`: §5 proves that field is
   vacuous on distinct clean donors, because they sit at distinct places.  Nor
   is the *full* identification carried as a hypothesis anywhere below --
   `Function.Injective (donorCoord S)` occurs only as the local hypothesis
   `hinj` of the general readout `donorCoord_card_le_of_injective`.  §4b does
   carry its **pairwise** `j`-slice as the per-index binder `hOuter` (see the
   anchor list above), which is strictly weaker and frozen-grounded.  Closing
   the full identification needs the routing dynamics of
   `ROUTED-CERTIFICATE-SYSTEM-001`'s own GAP item 1, i.e. a certificate carrier
   indexed by initial coordinate.
3. **M3 (the two reservoir types) still enters only by counting.**  `hsplit` is
   the frozen `09:1643--1645` sentence, indexed by the donor, and is carried.
4. **`P_v` is still the doubly-indexed binder** `MASS-REDISTRIBUTION-COUNTING-001`
   registered; this module only aggregates it through the predecessor.
5. **`hdense` at a legal `C >= 3` remains the Stage-4 lower bound itself**, so
   the terminal hardness at an owner is an interface and not a theorem here.

## Reader counterpart

**This module claims no reader item, deliberately rather than by omission**, and
the precedent is its own predecessor plus `MassLeavesOwner`,
`MassRedistributionCounting`, `WrapperMassRedistribution`,
`TerminalResidualComparison` and `DenseWrapperFrontier`.
`routes/parameterized-np/reader-facing/sections/` was swept first-hand for this
tranche (`interlace`, `scale-alignment`, `owner`, `donor`, `coordinate`,
`outer copy`, `threshold`):

* `A-stage4-details.tex:296--301` ("Let `q = 2^{r_q}` be the dyadic
  scale-alignment width chosen by the parameter compiler, and define
  `U = Int_q(N)`, `W = U^T`") is the reader's account of `09:105--108`, opened
  first-hand: it is **unnumbered prose with an unlabelled display**, and citing
  prose as a statement is barred.
* `def:paper-adapted-stage4` (`A-stage4-details.tex:324--332`) is a numbered
  item, but it states the *transposed* output `W = Int_q(N)^T` together with the
  evaluator, not the outer-copy indexing of `U`; it is already carried by the
  crosswalk row "Scale-aligned adapted Stage 4" against `SCALE-ALIGN-OPENING-001`,
  which is the module that owns `wrapperU` and `wrapperW`.  A reader item may not
  be assigned twice.
* `A-stage4-details.tex:373--378` and `:396--399` are unnumbered proof prose
  inside the proof of `thm:paper-adapted-stage4-interface` and are already
  recorded as unclaimed by `WrapperProjectionCovers`, `MassRedistributionCounting`,
  `MassLeavesOwner` and `OwnerMassTransfer`.
* `:387--391` is already assigned to `TERMINAL-TWO-STREAM-001`, and the one
  display in range, `:393--395`, is `eq:wrapper-u-dense` itself -- which this
  module does **not** close and therefore must not claim.

`READER_CROSSWALK.md` is therefore not modified by this tranche.

## Axiom surface

No new `axiom`, no proof-suppression token, no opaque certificate.  Every
external contact is an explicit binder: the terminal lemma family `hTTS`, the
frozen reservoir split `hsplit`, the schedule gates `hgates`, the deficit-sum
majorant `hdeficit`, the per-reservoir foreign fibre degree `dF` with its
regularity and positivity (F1), the pairwise outer-copy separation `hOuter`
(`09:1643--1644`, `09:1653--1655`; R9), and the owner rectangle's row sections
and games.  `EXPANDER-001` occurs in no hypothesis of
this module and has no Lean declaration by design.  `LegacyNPCC.Stage12` --
whose closure reaches the cited AGHP balanced-family axiom -- is **not** in the
import closure: the single import is `OwnerMassTransfer`, whose ledger row
records the same exclusion.  Every declaration below is `Classical`-only.

## Non-vacuity and canonical inhabitation

**CANONICAL INHABITATION -- REGISTERED and DEFERRED, inherited unchanged.**  The
paper's own instance of this block is the owner rectangle of a good donor in the
routed certificate system of the *alleged shallow protocol*, at the matrix `N` of
the frozen construction.  Neither that routing, nor the protected-reservoir mass
`P_v`, nor the transcript-level row sections is formalized, and `hdense` is the
Stage-4 lower bound itself, so **no paper instance exists to exhibit**.  The
obligation is discharged only when the wrapper's transcript-level construction
lands -- never by a probe, and never by the predecessor's NON-FIDELITY R5 audit
point.

This module introduces **no new structure and no new premise bundle**, precisely
so that no bundle inhabitation is owed: `donorCoord` is the only new definition
and it is a projection of banked data.  The non-vacuity load is carried by §5:
the outer-copy layer is shown to **degenerate at the illegal width `r = 0`**
(where every donor coordinate collapses and the realization's `hOuter` is
unsatisfiable), the derived cardinality relation `card iota <= card Coord` is
exhibited as pointing the same way as the frozen counting rather than as a
contradiction, the erased index `j` is shown to be genuinely excluded from the
family, the unconditional reading of the terminal hardness is refuted at every
index, and -- new in r1 -- the F1 hypothesis shape is shown to be the only one
the frozen degrees allow: a single scalar provably forces the two foreign
reservoirs to share an exact fibre degree, while the reservoir-indexed `dF` is
inhabited at unequal positive degrees.
-/

namespace EthInapproximability.ParameterizedNP.OwnerIndexedTransferFamily

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.TwoStreamState
open EthInapproximability.ParameterizedNP.TerminalStateRealization
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.OwnerMassTransfer

/-! ## §1  `09:105--108` and `09:1238--1239`: the outer-copy indexing layer

"Let `q = 2^r` be the scale-alignment width and set `U = Int_q(N)`"
(`09:105--108`), and "a certificate consists of at least `A_k` reference rows in
one **outer coordinate**" (`09:1238--1239`).

Both halves of the first sentence are already banked --
`ScaleAlignOpening.scaleAlignWidth` and `ScaleAlignOpening.wrapperU` -- and are
consumed by pin: no second width and no second interlace is defined.  What this
section adds is the *indexing*: the outer coordinate of a routed certificate is
a slot of `U`, so the predecessor's free `crd : iota -> Slot q` becomes the
derived `donorCoord`. -/

section OuterCopies

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}

/-- **`09:1238--1239`, the donor's outer coordinate, DERIVED.**

"At remaining selector capacity `2^k`, a certificate consists of at least `A_k`
reference rows in one outer coordinate."  The coordinate is the banked
`RoutedCertificate.coord` field of the certificate the routed system places for
the donor, so the map the predecessor carried as the free binder
`crd : iota -> Slot q` is a projection of banked data and nothing is chosen.

Kept general in `Coord`; `donorCoord_is_an_outer_copy_index` below is the
instance at the frozen `Coord = Slot (scaleAlignWidth r)` of `09:105--108`. -/
def donorCoord (S : RoutedSystem P Coord ι V r A0) (i : ι) : Coord :=
  (S.cert i).coord

/-- **Aux 1 (identity).**  `donorCoord` is the certificate's own coordinate
field: the derivation is a projection and not a re-encoding.  General. -/
@[simp] theorem donorCoord_eq (S : RoutedSystem P Coord ι V r A0) (i : ι) :
    donorCoord S i = (S.cert i).coord := rfl

/-- **Aux 2 (`09:1279--1280` in the donor-coordinate reading).**  Two donors that
stop at the same node and carry the same outer coordinate are the same donor.
This is the banked `RoutedSystem.coordUnique` read through `donorCoord`, and it
is *all* the banked structure supplies -- §5 shows why it is not enough for the
family.  General. -/
theorem donorCoord_injOn_of_place_eq (S : RoutedSystem P Coord ι V r A0) {i j : ι}
    (hplace : S.place i = S.place j) (hcoord : donorCoord S i = donorCoord S j) :
    i = j :=
  S.coordUnique i j hplace hcoord

/-- **Aux 3 (round trip to the owner).**  The same fact at the owner map, which
is the frozen `own(.)` of `09:1568`: `owner` is `place` by definition, so two
good donors with a common owner and a common outer coordinate coincide.
General. -/
theorem donorCoord_injOn_of_owner_eq (S : RoutedSystem P Coord ι V r A0) {i j : ι}
    (howner : S.owner i = S.owner j) (hcoord : donorCoord S i = donorCoord S j) :
    i = j :=
  donorCoord_injOn_of_place_eq S howner hcoord

/-- **Aux 4 (the cardinality readout of `09:1235--1236`).**  If the frozen indexing
"one clean reference certificate in every coordinate" holds, the donor index is
no larger than the coordinate carrier.

R4, corrected: `09:1559` prints `e_T <= q-c+e_B`, an *exceptional-count* bound
and not a cardinality relation; the frozen `c <= q` is the inference the paper
records at `09:1564` ("Here we used `K_B+n_T <= q`").  And `iota` here indexes
*all* routed certificates, not the clean set `J_clean` of `09:1519`.  So this
lemma says only that the hypothesis `hinj` -- the sole occurrence in this module
of the coordinate injectivity of `09:1235--1236` (R1: it is bound nowhere else)
-- points the same way as the frozen counting and is not a cardinality trap.
General. -/
theorem donorCoord_card_le_of_injective [Fintype ι] [Fintype Coord]
    (S : RoutedSystem P Coord ι V r A0) (hinj : Function.Injective (donorCoord S)) :
    Fintype.card ι ≤ Fintype.card Coord :=
  Fintype.card_le_of_injective _ hinj

/-- **Aux 5 (the outer copies of `U` never collide).**  Two donors at distinct
outer coordinates have physically disjoint row streams, whatever the reservoirs
are: the banked `TwoStreamState.streamRows_disjoint` at the derived coordinates.
This is the structural content of "one outer coordinate" (`09:1238--1239`) inside the
interlace `U` of `09:107`.  General. -/
theorem donorStreams_disjoint {Rw : Type*} [DecidableEq Rw] {q : ℕ}
    (S : RoutedSystem P (Slot q) ι V r A0) {i j : ι}
    (hij : donorCoord S i ≠ donorCoord S j) (XZ : Finset (Slot q × Rw))
    (R R' : Finset Rw) :
    Disjoint (streamRows XZ (donorCoord S i) R) (streamRows XZ (donorCoord S j) R') :=
  streamRows_disjoint hij R R'

end OuterCopies

section Interlace

variable {Rw Cl : Type*}

/-- **Aux 6 (`09:107`, the defining readout of `U`).**  Stated without the
routed system, so that the outer-copy layer is available before any donor is
fixed.  General. -/
@[simp] theorem wrapperU_apply (Nmat : Rw → Cl → Bool) (rq : ℕ)
    (p : Slot (scaleAlignWidth rq) × Rw) (y : Slot (scaleAlignWidth rq) → Cl) :
    wrapperU Nmat rq p y = Nmat p.2 (y p.1) := rfl

/-- **Aux 7 (the outer copy reads only its own coordinate).**  Two Bob tuples
agreeing at the row's own outer coordinate give the same entry of `U`.  This is
the property that makes "outer copy" a genuine indexing rather than a
relabelling, and it is what lets the frozen argument treat one donor's copy in
isolation.  General. -/
theorem wrapperU_congr_at_slot (Nmat : Rw → Cl → Bool) (rq : ℕ)
    (p : Slot (scaleAlignWidth rq) × Rw) {y y' : Slot (scaleAlignWidth rq) → Cl}
    (h : y p.1 = y' p.1) :
    wrapperU Nmat rq p y = wrapperU Nmat rq p y' := by
  simp only [wrapperU_apply, h]

/-- **Aux 8 (the bridge the residual comparison needs).**  The game the banked
`OwnerMassTransfer.ownerTransfer_lt_engine` compares against at the frozen width
`q = 2^r` **is** the subgame of the banked `U`; by `rfl`, so no relabelling is
inserted between `09:107` and the wrapper's `hgame`.  General. -/
theorem subgame_wrapperU (Nmat : Rw → Cl → Bool) (rq : ℕ)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl)) :
    subgame (wrapperU Nmat rq) XZ YZ
      = subgame (interlaceFun Nmat (scaleAlignWidth rq)) XZ YZ := rfl

/-- **Aux 9 (`09:107` with `09:1238--1239`): a donor's outer copy of `U` is a copy of
`N`.**  Reading `U` at the row `(donorCoord S i, x)` evaluates `N` at `x` against
Bob's entry in *that* donor's coordinate.  This is the sentence "a certificate
consists of ... reference rows in one outer coordinate" made a computation, and
it is the whole content of calling `donorCoord` an outer-copy index.  General. -/
theorem wrapperU_at_donorCoord {X Y Z ι V : Type*} {P : Protocol X Y Z} {rr A0 : ℕ}
    (Nmat : Rw → Cl → Bool) (rq : ℕ)
    (S : RoutedSystem P (Slot (scaleAlignWidth rq)) ι V rr A0) (i : ι) (x : Rw)
    (y : Slot (scaleAlignWidth rq) → Cl) :
    wrapperU Nmat rq (donorCoord S i, x) y = Nmat x (y (donorCoord S i)) := rfl

/-- **Aux 10 (monotonicity at the derived index).**  The frozen `eps_i` of
`09:1618--1619`, read at the *derived* donor coordinate, is antitone in the
surviving rectangle: shrinking the rectangle can only raise the missing
fraction.  This is the banked `OwnerMassTransfer.ordinaryDeficit_mono` transported
to the outer-copy indexing, and it is the property the per-owner gluing note of
`OWNER-MASS-TRANSFER-001` relies on.  General. -/
theorem ordinaryDeficit_at_donorCoord_mono [DecidableEq Rw]
    {X Y Z ι V : Type*} {P : Protocol X Y Z} {rr A0 : ℕ} {rq : ℕ}
    (S : RoutedSystem P (Slot (scaleAlignWidth rq)) ι V rr A0) (i : ι)
    {XZ XZ' : Finset (Slot (scaleAlignWidth rq) × Rw)} (RG : Finset Rw)
    (hsub : XZ ⊆ XZ') :
    ordinaryDeficit XZ' (donorCoord S i) RG ≤ ordinaryDeficit XZ (donorCoord S i) RG :=
  ordinaryDeficit_mono (donorCoord S i) RG hsub

end Interlace

/-! ## §2  `09:1250--1252` and `09:1550--1552`: the owner-side facts that are
genuinely derivable

The predecessor took `hv : S.firstBob v = false` at a free node `v`, and its
consumers took the residual budget and the column sections at that node.  Once
the node is the *owner* of a clean donor, all three follow from banked facts:
membership in `cleanFinal` carries the stopping rule, `09:1250--1252` makes the
address an Alice-only route, and `09:1330--1331` makes Bob's columns untouched
there. -/

section OwnerFacts

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype ι]

/-- **`09:1550`, the stopping rule at an owner, DERIVED.**  "Every clean
reference certificate has a unique final node, its owner": membership in the
banked `RoutedSystem.cleanFinal` *is* the conjunction "clean, and stopped by the
final-Alice rule", so the predecessor's `hv` is a projection at every owner.
General. -/
theorem owner_not_firstBob (S : RoutedSystem P Coord ι V r A0) {i : ι}
    (hi : i ∈ S.cleanFinal) : S.firstBob (S.owner i) = false := by
  simp only [RoutedSystem.cleanFinal, Finset.mem_filter] at hi
  exact hi.2.2

/-- **`09:1548` with `09:1550`, at a good donor.**  Good donors are clean donors
(the banked `goodDonors_subset`), so their owners are final Alice nodes too.
General. -/
theorem goodDonor_owner_not_firstBob [Fintype V] [DecidableEq ι]
    (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (etaR : ℝ) {i : ι} (hi : i ∈ goodDonors S Pv etaR) :
    S.firstBob (S.owner i) = false :=
  owner_not_firstBob S (goodDonors_subset S Pv etaR hi)

/-- **`09:1341--1343` at an owner, DERIVED.**  The suffix below the owner of a
clean donor keeps at most `C-1` bits in the alleged `(C+r-1)`-bit protocol.  The
banked `RoutedSystem.final_residual_budget` fed by the derived stopping rule.
General. -/
theorem owner_residual_budget {C : ℕ} (S : RoutedSystem P Coord ι V r A0) {i : ι}
    (hi : i ∈ S.cleanFinal) (hcost : P.cost ≤ C + r - 1) :
    (descend P (S.node (S.owner i))).cost + r ≤ C + r - 1 :=
  S.final_residual_budget (owner_not_firstBob S hi) hcost

omit [Fintype ι] in
/-- **`09:1330--1331` at an owner, DERIVED -- the column half of the owner
rectangle.**  "No Bob query has occurred on the route to this node": every
frontier address is an Alice-only route, so *every* Bob section satisfies
`RouteCols` there.  This is the one half of the owner rectangle's sections that
the frozen text supplies outright, and it is why only `iotaA`/`hgame` remain
binders.  General in the section. -/
theorem ownerCols_derived (S : RoutedSystem P Coord ι V r A0) (i : ι)
    {B : Type*} (iotaB : B → Y) :
    ∀ b : B, RouteCols P (S.node (S.owner i)) (iotaB b) := fun b =>
  routeCols_of_isAlicePath (S.node_isAlicePath (S.owner i)) (iotaB b)

/-- **`09:1550--1552` and `09:1612`, the erased index is genuinely absent.**

The frozen leakage sum of `eq:wrapper-mass-leaves-owner` runs over
`T != own(j)`, and `eq:wrapper-good-to-good` bounds its good-owner part by
summing over the *other* good donors.  With owners injective on clean donors
(the banked `RoutedSystem.owner_injOn`), `own(j)` is not the owner of any other
good donor -- so erasing `j` from the index set really does erase the node
`own(j)` from the sum, and the frozen exclusion is not a convention.
General. -/
theorem owner_self_not_mem_erase_image [DecidableEq V] [DecidableEq ι] [Fintype V]
    (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ) (etaR : ℝ)
    (huniq : ∀ v : V, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    {j : ι} (hj : j ∈ goodDonors S Pv etaR) :
    S.owner j ∉ ((goodDonors S Pv etaR).erase j).image S.owner := by
  intro hmem
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  exact (Finset.mem_erase.mp hi).1
    (S.owner_injOn huniq i (goodDonors_subset S Pv etaR (Finset.mem_of_mem_erase hi)) j
      (goodDonors_subset S Pv etaR hj) heq)

end OwnerFacts

/-! ## §3  The §4 -> §5 seam: `hstateOf` produced, and `hq_2` discharged at the
call site (the **F3 route**)

`09:1661--1669` calls `lem:terminal-state-realization` and `09:1670--1671`
immediately reads the structural gates off the schedule: "Since
`delta_i = lambda_0 + 5 eps_i + 2/q_2`, the structural gates give `q_2 >= 16`
and `lambda_0 <= 1/8`."  The banked
`WrapperMassRedistribution.structuralReadout` is exactly that sentence, so the
positivity `0 < q_2` the realization needs is available *at the call site* and
never has to be a binder of the consumer.

The parked judge finding **F3** on `OWNER-MASS-TRANSFER-001` asked for precisely
this and was deferred because removing the binder from `ownerTerminalState`
would have changed a banked signature.  It is discharged here **without opening
that declaration**: `ownerTerminalState` is consumed byte-for-byte as banked,
and `hq_2` is supplied from `structuralReadout` by the caller. -/

section Seam

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]

/-- **`09:1648--1669` composed into the shape `09:1670--1679` consumes.**

This is the predecessor's `hstateOf` binder, *produced*.  Given the realization
data of `09:1661--1669` it returns, for **either** arriving reservoir type of the
frozen dichotomy `09:1644--1645` and any arrival meeting the owner threshold, the
banked `TwoStreamState` at exactly the frozen pair
`(eps_i, delta_i) = (ordinaryDeficit, ownerThreshold ...)`.

Two hypotheses of the banked `ownerTerminalState` are **discharged rather than
passed**:

* `hq_2 : 0 < W.q_2` comes from `WrapperMassRedistribution.structuralReadout`
  (`09:1670--1671`), the **F3 route**;
* `hEpsLtOne` comes from the banked `ordinaryDeficit_lt_one` fed by the two
  frozen nonemptiness facts -- the owner retains *some* of its ordinary baseline
  (`09:1648--1649`) and the baseline itself is nonempty (`09:109--117`, where
  `R_G` is the base-column reservoir of `A`).

**F1 repair (r1): the foreign fibre degree is INDEXED BY THE RESERVOIR.**  The
frozen display at `09:725--732` gives the three physical reservoirs *different*
exact fibre degrees at one fixed bin `p`, namely
`d_G = w_0 |K_R| |J_2|^{s-1}` (`09:728`), `d_Sigma = w_Sigma |J_2|^{s-1}`
(`09:730`) and `d_D = w_D` (`09:732`), and `08:100--102` fixes
`w_Sigma = M_0 D_0` and `w_D = M_0 S_0`.  Since `RegularOn` is an **exact**
fibre count, a single scalar degree quantified outside the `forall Rf` would
demand `d_Sigma = d_D`, i.e. `D_0 |J_2|^{s-1} = S_0`, which no frozen gate
imposes; the bundle would then fail to be inhabited at the paper's own instance.
The degree is therefore the function `dF : Finset Rw -> N`, with regularity
(`hRegF`) and positivity (`hdF`) both quantified over the reservoir.  The banked
`ownerTerminalState` takes `{Rf}` and `{dFor}` implicit, so `(hRegF Rf hProt)`
and `(hdF Rf hProt)` unify the degree per branch at `dF Rf` and the banked
declaration stays untouched.  `dOrd` remains a separate scalar: it is the third,
base-reservoir degree `d_G`.  The banked
`TerminalStateRealization.terminalStateRealization_fires_in_diagonal_branch` is
the recorded reason a shared tuple-level form would empty one branch.
General in all six carriers.

Recorded as a `noncomputable def` and not a `theorem` for the same reason
`ownerTerminalState` is: the banked `TwoStreamState` is a **structure**, so the
produced object is data and its type is not a `Prop`.  Nothing about it is
choice-laden beyond the banked realization it calls. -/
noncomputable def ownerStateOf (W : StageTwoRelaxed.StageTwoWidths)
    {q s mT dT dOrd : ℕ}
    {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
    {cFam : Ltwo → Slot W.q₂ → Rone}
    {Stwo : Ltwo → Slot W.q₂ × Cone → Bool}
    {RG RSig RD : Finset Rw} {omg : Rw → Om} {tup : Om → Slot s → Slot W.q₂ × Cone}
    {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
    {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
    {eps2 xT : ℝ}
    (dF : Finset Rw → ℕ)
    (oi oj : Slot q) (pOrd pFor : Slot s) (Pstar : Finset (Cl × Cl))
    (Rbin : Slot s → Finset Ltwo) (selRow : Slot s × Ltwo → (Slot q → Cl))
    (hOuter : oi ≠ oj)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : (streamRows XZ oi RG).Nonempty) (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ yp ∈ Pstar, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ yp ∈ Pstar, ∃ w ∈ YZ, w oi = yp.1 ∧ w oj = yp.2)
    (hPairDensity : aMin rhoPair (templateDensity YT) ≤ (Pstar.card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ p : Slot s,
      ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin p).card)
    (hSelRowMem : ∀ p : Slot s, ∀ l ∈ Rbin p, selRow (p, l) ∈ YZ)
    (hSelRowTyped : ∀ p : Slot s, ∀ l ∈ Rbin p,
      selRow (p, l) oi ∈ YT p ∧ zeta p (selRow (p, l) oi) = l)
    (hSelDist : ∀ l ∈ Rbin pOrd, ∃ yp ∈ Pstar, selRow (pOrd, l) oi = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2) :
    ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ oi RG)
        ≤ ((streamRows XZ oj Rf).card : ℝ) / (Rf.card : ℝ) →
      TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD omg
        (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT
        (ordinaryDeficit XZ oi RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ oi RG)) := by
  intro Rf hProt harr
  exact ownerTerminalState W oi oj pOrd pFor Pstar Rbin selRow hOuter hbins
    htemplate_card htemplate_regular hStwo hNval hProt
    (lt_of_lt_of_le (by norm_num) (structuralReadout W).1)
    (ordinaryDeficit_lt_one hOrdNe hRGpos) harr hRegG hdOrd (hRegF Rf hProt)
    (hdF Rf hProt)
    hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist
    hEps2 hxT hSelectorGate

end Seam

/-! ## §4  The owner-indexed transfer family (`09:1643--1699`), with `htrans`
derived

The predecessor's `goodToGood_engine` *received* the family

  `Pv (own i) j < 2 mu_P delta_i`   for `i in J_good \ {j}`

as the hypothesis `htrans`, and recorded as GAP item 4 that wiring §5 into §7
uniformly needed the owner-indexed family of realizations.  §1 supplies the
missing index: the frozen `eps_i` of donor `i` is read at the *derived*
coordinate `donorCoord S i`, and the whole family is now produced by quantifying
the banked `ownerTransfer_lt_engine` over `i in J_good \ {j}`.

Three of that theorem's inputs become derived at each index: the node is the
owner `own(i)` (`09:1568`), its stopping rule is `owner_not_firstBob`
(`09:1550`), and the column half of the rectangle is `ownerCols_derived`
(`09:1330--1331`).  What stays indexed-and-explicit is exactly what the frozen
text supplies per owner: the terminal lemma `hTTS` (BINDER-ONLY,
`TERMINAL-TWO-STREAM-001`), the produced state `hstateOf` (which §3 builds), the
reservoir split `hsplit` (M3), and the row sections `iotaA`/`hgame` (M1
residue). -/

section Family

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
  [Fintype Rone] [DecidableEq Rone]

/-- **`09:1643--1679` with the §4 -> §5 seam closed in proof terms.**

The predecessor's `ownerTransfer_lt_engine` with its `hstateOf` binder
**removed**: the produced state comes from `ownerStateOf`, i.e. from the frozen
realization call of `09:1661--1669`, and `hq_2` is discharged inside it from
`09:1670--1671`.  Nothing else changes -- the terminal lemma is still the binder
`hTTS`, the reservoir split is still `hsplit`, and the conclusion is byte-for-byte
the frozen "every such transfer is strictly below `2 mu_P delta_i`".

This is the declaration that makes §3 and §4 *compose* rather than merely
coexist.  R6, corrected: the quantified form of **this** declaration is §4b's
`ownerTransfer_family_of_realization`, which is what the module's endpoints now
run through; the earlier `ownerTransfer_family` quantifies the banked
`ownerTransfer_lt_engine` instead and re-introduces `hstateOf` as a per-index
binder, so it is the weaker interface and is kept only as such.  General. -/
theorem ownerTransfer_lt_of_realization
    {Xa Yb : Type*} {Coord ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    (W : StageTwoRelaxed.StageTwoWidths)
    (q s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot q × Rw)) (YZ : Finset (Slot q → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ) (oi oj : Slot q)
    (pOrd pFor : Slot s) (Pstar : Finset (Cl × Cl))
    (Rbin : Slot s → Finset Ltwo) (selRow : Slot s × Ltwo → (Slot q → Cl))
    (hOuter : oi ≠ oj)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : (streamRows XZ oi RG).Nonempty) (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ yp ∈ Pstar, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ yp ∈ Pstar, ∃ w ∈ YZ, w oi = yp.1 ∧ w oj = yp.2)
    (hPairDensity : aMin rhoPair (templateDensity YT) ≤ (Pstar.card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ p : Slot s,
      ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin p).card)
    (hSelRowMem : ∀ p : Slot s, ∀ l ∈ Rbin p, selRow (p, l) ∈ YZ)
    (hSelRowTyped : ∀ p : Slot s, ∀ l ∈ Rbin p,
      selRow (p, l) oi ∈ YT p ∧ zeta p (selRow (p, l) oi) = l)
    (hSelDist : ∀ l ∈ Rbin pOrd, ∃ yp ∈ Pstar, selRow (pOrd, l) oi = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : TerminalTwoStream.TerminalTwoStream W q s mT dT bcap r₃ bT Lh vmax Nmat
      Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
      (templateDensity YT) eps2 epsProd xT yy (ordinaryDeficit XZ oi RG)
      (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ oi RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (S : RoutedSystem Pr Coord ιc Vn rw' A0) {v : Vn} (hv : S.firstBob v = false)
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : {a // a ∈ XZ} → Xa) (iotaB : {b // b ∈ YZ} → Yb)
    (hrow : ∀ a, RouteRows Pr (S.node v) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat q) XZ YZ a b = gamb (iotaA a) (iotaB b))
    {transfer : ℝ}
    (hsplit : 2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ oi RG) ≤ transfer →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ oi RG)
        ≤ muP * (((streamRows XZ oj RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ oj RD).card : ℝ) / (RD.card : ℝ))) :
    transfer < 2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ oi RG) :=
  ownerTransfer_lt_engine W q s mT dT bcap r₃ bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD
    omg tup YT zeta XZ YZ eps2 epsProd xT yy oi oj
    (ownerStateOf W dF oi oj pOrd pFor Pstar Rbin selRow hOuter hbins htemplate_card
      htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd hRegF hdF hPstarTyped
      hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist hEps2 hxT
      hSelectorGate)
    hTTS hs hxTd hyy hseed hfixed hcalls S hv hC hcost hcomp iotaA iotaB hrow hgame hsplit

/-- **`09:1677--1679`, quantified over `J_good \ {j}` -- GAP 4 discharged.**

"Therefore every such transfer is strictly below `2 mu_P delta_i`", now as a
*family* over the good donors other than `j`, at the frozen width
`q = 2^r` of `09:105` and the derived donor coordinates of `09:1238--1239`.

The game is the banked `ScaleAlignOpening.wrapperU` (`09:107`) rather than a free
interlace, which is what pins the outer-copy indexing: Alice's carrier is
`Slot (scaleAlignWidth rq) x Rw`, i.e. an outer copy of `U` paired with a row of
`N`, and the donor coordinates are slots of that interlace.

`hv` and the column sections are **not** binders: they are derived from
`09:1550` and `09:1330--1331` at each owner.  Nothing here upgrades
`lem:terminal-two-stream`, which enters as the indexed binder `hTTS`.
General. -/
theorem ownerTransfer_family
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    [Fintype Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (eps2 epsProd xT yy : ℝ)
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) (etaR : ℝ) {j : ιc}
    (hstateOf : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ Rf : Finset Rw,
      (Rf = RSig ∨ Rf = RD) →
      ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ ((streamRows XZ (donorCoord S j) Rf).card : ℝ) / (Rf.card : ℝ) →
      TwoStreamState (scaleAlignWidth rq) s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
        omg (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ))) :
    ∀ i ∈ (goodDonors S Pv etaR).erase j,
      Pv (S.owner i) j
        < 2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG) := by
  intro i hi
  have hgood : i ∈ goodDonors S Pv etaR := Finset.mem_of_mem_erase hi
  exact ownerTransfer_lt_engine W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh vmax Nmat
    Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ eps2 epsProd xT yy
    (donorCoord S i) (donorCoord S j) (hstateOf i hi) (hTTS i hi) hs hxTd hyy hseed
    hfixed hcalls S (goodDonor_owner_not_firstBob S Pv etaR hgood) hC hcost hcomp
    (iotaA i) (iotaB i) (hrow i hi) (hgame i hi) (hsplit i hi)

/-- **`eq:wrapper-good-to-good` (`09:1690--1699`) with `htrans` DERIVED.**

The predecessor's `goodToGood_engine` with its per-owner transfer hypothesis
removed: the family is produced by `ownerTransfer_family` inside the proof.  The
arithmetic remains the banked `WrapperMassRedistribution.wrapperGoodToGood` and
`sum_ownerThreshold_le`, consumed by pin through the predecessor; the frozen
constant `3 eta_R/16` and the strict gap to `eta_R/4` are not restated.

`crd` is the derived `donorCoord`, so the frozen `eps_i` of the deficit sum and
the frozen `eps_i` of the transfer family are read at the **same** coordinate by
construction -- which is what the predecessor's modelling note asked the
outer-copy layer to supply.  General. -/
theorem goodToGood_engine_derived
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT bcap r₃ bT Lh vmax qw : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (eps2 epsProd xT yy : ℝ)
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} {j : ιc}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors S Pv etaR) (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates qw W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ (qw : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR, ordinaryDeficit XZ (donorCoord S i) RG
      ≤ etaR / (8 * g))
    (hstateOf : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ Rf : Finset Rw,
      (Rf = RSig ∨ Rf = RD) →
      ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ ((streamRows XZ (donorCoord S j) Rf).card : ℝ) / (Rf.card : ℝ) →
      TwoStreamState (scaleAlignWidth rq) s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
        omg (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ))) :
    goodOwnerMass S Pv etaR j ≤ 3 * etaR / 16 ∧ 3 * etaR / 16 < etaR / 4 :=
  goodToGood_engine W S Pv XZ RG (donorCoord S) huniq hj hetaR hg hgates hcard hdeficit
    (ownerTransfer_family W rq s mT dT bcap r₃ bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD
      omg tup YT zeta XZ YZ eps2 epsProd xT yy S Pv etaR hstateOf hTTS hs hxTd hyy hseed
      hfixed hcalls hC hcost hcomp iotaA iotaB hrow hgame hsplit)

/-- **`09:1700--1701` with the family derived -- the segment's steps 5--6, closed
one level lower than the predecessor closed them.**

"Together with `eq:wrapper-mass-leaves-owner`, this says that every good donor
sends more than `eta_R/4` protected mass to exceptional final nodes."

Identical conclusion to the banked
`OwnerMassTransfer.goodDonor_mass_to_exceptional`, with the per-owner transfer
hypothesis `htrans` **removed**: it is produced inside from the owner-indexed
realization family.  `hleaves` is still the banked
`MassLeavesOwner.massLeavesOwner_engine` endpoint, and the arithmetic is still
the banked `goodDonor_to_exceptional_gt`.  Nothing beyond `09:1701` is claimed.
General. -/
theorem goodDonor_mass_to_exceptional_derived
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT bcap r₃ bT Lh vmax qw : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (eps2 epsProd xT yy : ℝ)
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} {j : ιc}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors S Pv etaR) (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates qw W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ (qw : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR, ordinaryDeficit XZ (donorCoord S i) RG
      ≤ etaR / (8 * g))
    (hstateOf : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ Rf : Finset Rw,
      (Rf = RSig ∨ Rf = RD) →
      ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ ((streamRows XZ (donorCoord S j) Rf).card : ℝ) / (Rf.card : ℝ) →
      TwoStreamState (scaleAlignWidth rq) s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
        omg (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ)))
    (hleaves : etaR / 2 < ownerLeakage S Pv j) :
    etaR / 4 < exceptionalMass S Pv etaR j :=
  goodDonor_to_exceptional_engine S Pv hj hetaR hleaves
    (goodToGood_engine_derived W rq s mT dT bcap r₃ bT Lh vmax qw Nmat Mmat cFam Stwo
      RG RSig RD omg tup YT zeta XZ YZ eps2 epsProd xT yy S Pv huniq hj hetaR hg hgates
      hcard hdeficit hstateOf hTTS hs hxTd hyy hseed hfixed hcalls hC hcost hcomp iotaA
      iotaB hrow hgame hsplit).1

/-! ### §4b  The seam TRAVELLED (R6), at the one frozen width (R7)

The three declarations above stop short in one respect the r0 statement gate
recorded as **R6**: `ownerTransfer_lt_of_realization` was consumed by nothing,
because `ownerTransfer_family` re-introduces `hstateOf` as a *per-index binder*.
The seam of §3 was therefore **stated** and not **travelled** -- the module's own
endpoints never ran through the produced state.

This block closes that.  `ownerTransfer_family_of_realization` takes the
per-index realization data of `09:1661--1669`, read at the derived owner
coordinate `donorCoord S i` and the derived donor coordinate `donorCoord S j`
(`09:1238--1239`), and produces the whole family of `09:1677--1679` by calling
`ownerTransfer_lt_of_realization` -- hence `ownerStateOf`, hence the banked
`ownerTerminalState` -- once per index.  **No `hstateOf` binder occurs anywhere
in this block**, so the §4 -> §5 seam travels in actual proof terms, and the F1
repair (the reservoir-indexed degree `dF`) travels with it: the two foreign
reservoirs of `09:725--732` may carry their different exact fibre degrees at
every index.

The two endpoints are rebuilt on it, and `09:105`, `09:1250` and `09:1264` are
read as the **one** width the frozen paper says they are (**R7**): the
coordinate carrier `Slot (scaleAlignWidth rq)` of `09:105` ("Let `q = 2^r` be
the scale-alignment width"), the routed system's Alice budget of `09:1250`
("Stop each routed branch at its first Bob query, or after `r` Alice queries"),
and the width `q` of `sum_v kappa_v <= q` at `09:1264` are all taken at the same
`rq`.  The banked `goodToGood_engine` keeps the three nominally independent;
that inherited generality is sound and the frozen paper's point is exactly the
diagonal instance, which is what these two endpoints take.  Nothing beyond
`09:1701` is claimed, and `hDenseRung` is still neither discharged nor fed. -/

/-- **`09:1677--1679` as a family, produced from the realization data -- R6.**

The per-index form of `ownerTransfer_lt_of_realization`: no `hstateOf`
hypothesis, only the frozen realization inputs of `09:1661--1669` at each good
donor `i != j`.  `hv` is derived at every index from `09:1550`
(`goodDonor_owner_not_firstBob`), and the column half of the owner rectangle is
derived inside the banked engine from `09:1330--1331`.

`dF : Finset Rw -> N` is the F1 shape: the exact fibre degree of the *arriving*
reservoir at the fixed bin `pFor`, indexed by that reservoir, because
`09:725--732` gives `d_Sigma = w_Sigma |J_2|^{s-1}` and `d_D = w_D` with
`08:100--102` fixing `w_Sigma = M_0 D_0`, `w_D = M_0 S_0`.  The base-reservoir
degree `d_G` is the separate scalar `dOrd`.

The realization witnesses `Pstar`, `Rbin`, `selRow` and the row/column sections
`iotaA`, `iotaB` are indexed by the donor, since `09:1661--1669` is applied once
per owner rectangle.  `hTTS` remains the BINDER-ONLY terminal lemma
(`TERMINAL-TWO-STREAM-001`) at every index.  General. -/
theorem ownerTransfer_family_of_realization
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    [Fintype Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ)
    (pOrd pFor : Slot s) (Pstar : ιc → Finset (Cl × Cl))
    (Rbin : ιc → Slot s → Finset Ltwo)
    (selRow : ιc → Slot s × Ltwo → (Slot (scaleAlignWidth rq) → Cl))
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) (etaR : ℝ) {j : ιc}
    (hOuter : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      donorCoord S i ≠ donorCoord S j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      (streamRows XZ (donorCoord S i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ yp ∈ Pstar i,
      ∃ w ∈ YZ, w (donorCoord S i) = yp.1 ∧ w (donorCoord S j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ∀ l ∈ Rbin i p, selRow i (p, l) (donorCoord S i) ∈ YT p
        ∧ zeta p (selRow i (p, l) (donorCoord S i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ l ∈ Rbin i pOrd,
      ∃ yp ∈ Pstar i, selRow i (pOrd, l) (donorCoord S i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ))) :
    ∀ i ∈ (goodDonors S Pv etaR).erase j,
      Pv (S.owner i) j
        < 2 * muP * ownerThreshold W.q₂ W.b₁
            (ordinaryDeficit XZ (donorCoord S i) RG) := by
  intro i hi
  exact ownerTransfer_lt_of_realization W (scaleAlignWidth rq) s mT dT dOrd bcap r₃ bT Lh
    vmax Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy
    (donorCoord S i) (donorCoord S j) pOrd pFor (Pstar i) (Rbin i) (selRow i)
    (hOuter i hi) hbins htemplate_card htemplate_regular hStwo hNval (hOrdNe i hi) hRGpos
    hRegG hdOrd hRegF hdF (hPstarTyped i hi) (hPstarProj i hi) (hPairDensity i hi)
    (hRbinCard i hi) (hSelRowMem i hi) (hSelRowTyped i hi) (hSelDist i hi) hEps2 hxT
    hSelectorGate (hTTS i hi) hs hxTd hyy hseed hfixed hcalls S
    (goodDonor_owner_not_firstBob S Pv etaR (Finset.mem_of_mem_erase hi)) hC hcost hcomp
    (iotaA i) (iotaB i) (hrow i hi) (hgame i hi) (hsplit i hi)

/-- **`eq:wrapper-good-to-good` (`09:1690--1699`) from the realization data --
R6 travelled to the endpoint, R7 taken.**

Identical conclusion to `goodToGood_engine_derived`, with **both** the `htrans`
family *and* the per-index `hstateOf` removed: the family comes from
`ownerTransfer_family_of_realization`, so every good owner's two-stream state is
built here by the frozen realization call of `09:1661--1669`.

R7: the three nominally independent naturals of the banked engine are taken at
the single frozen width.  The routed system's Alice budget is `rq` (`09:1250`),
its coordinate carrier is `Slot (scaleAlignWidth rq)` (`09:105`), and the width
in `eq:wrapper-owner-gates` and in the donor count is `scaleAlignWidth rq`
(`09:1264`).  The arithmetic is still the banked `wrapperGoodToGood` and
`sum_ownerThreshold_le`, consumed by pin; the frozen `3 eta_R/16` and the strict
gap to `eta_R/4` are not restated.  General in the six carriers. -/
theorem goodToGood_engine_of_realization
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ)
    (pOrd pFor : Slot s) (Pstar : ιc → Finset (Cl × Cl))
    (Rbin : ιc → Slot s → Finset Ltwo)
    (selRow : ιc → Slot s × Ltwo → (Slot (scaleAlignWidth rq) → Cl))
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rq A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} {j : ιc}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors S Pv etaR) (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth rq) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ ((scaleAlignWidth rq : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR, ordinaryDeficit XZ (donorCoord S i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      donorCoord S i ≠ donorCoord S j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      (streamRows XZ (donorCoord S i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ yp ∈ Pstar i,
      ∃ w ∈ YZ, w (donorCoord S i) = yp.1 ∧ w (donorCoord S j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ∀ l ∈ Rbin i p, selRow i (p, l) (donorCoord S i) ∈ YT p
        ∧ zeta p (selRow i (p, l) (donorCoord S i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ l ∈ Rbin i pOrd,
      ∃ yp ∈ Pstar i, selRow i (pOrd, l) (donorCoord S i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rq - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ))) :
    goodOwnerMass S Pv etaR j ≤ 3 * etaR / 16 ∧ 3 * etaR / 16 < etaR / 4 :=
  goodToGood_engine W S Pv XZ RG (donorCoord S) huniq hj hetaR hg hgates hcard hdeficit
    (ownerTransfer_family_of_realization W rq s mT dT dOrd bcap r₃ bT Lh vmax Nmat Mmat
      cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd pFor Pstar
      Rbin selRow S Pv etaR hOuter hbins htemplate_card htemplate_regular hStwo hNval
      hOrdNe hRGpos hRegG hdOrd hRegF hdF hPstarTyped hPstarProj hPairDensity hRbinCard
      hSelRowMem hSelRowTyped hSelDist hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed
      hfixed hcalls hC hcost hcomp iotaA iotaB hrow hgame hsplit)

/-- **`09:1700--1701` from the realization data -- the segment's steps 5--6 with
the seam travelled all the way to the endpoint.**

"Together with `eq:wrapper-mass-leaves-owner`, this says that every good donor
sends more than `eta_R/4` protected mass to exceptional final nodes."

Identical conclusion to `goodDonor_mass_to_exceptional_derived`, now with the
per-index `hstateOf` removed as well: the good-to-good half comes from
`goodToGood_engine_of_realization`, so the banked `ownerTerminalState` is called
inside this proof term at every good owner.  `hleaves` is still the banked
`MassLeavesOwner.massLeavesOwner_engine` endpoint, and the arithmetic is still
the banked `goodDonor_to_exceptional_gt`.  Nothing beyond `09:1701` is claimed
and `eq:wrapper-u-dense` is concluded nowhere.  General. -/
theorem goodDonor_mass_to_exceptional_of_realization
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ)
    (pOrd pFor : Slot s) (Pstar : ιc → Finset (Cl × Cl))
    (Rbin : ιc → Slot s → Finset Ltwo)
    (selRow : ιc → Slot s × Ltwo → (Slot (scaleAlignWidth rq) → Cl))
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rq A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} {j : ιc}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors S Pv etaR) (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth rq) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ ((scaleAlignWidth rq : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR, ordinaryDeficit XZ (donorCoord S i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      donorCoord S i ≠ donorCoord S j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      (streamRows XZ (donorCoord S i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ yp ∈ Pstar i,
      ∃ w ∈ YZ, w (donorCoord S i) = yp.1 ∧ w (donorCoord S j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ p : Slot s,
      ∀ l ∈ Rbin i p, selRow i (p, l) (donorCoord S i) ∈ YT p
        ∧ zeta p (selRow i (p, l) (donorCoord S i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ l ∈ Rbin i pOrd,
      ∃ yp ∈ Pstar i, selRow i (pOrd, l) (donorCoord S i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rq - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ)))
    (hleaves : etaR / 2 < ownerLeakage S Pv j) :
    etaR / 4 < exceptionalMass S Pv etaR j :=
  goodDonor_to_exceptional_engine S Pv hj hetaR hleaves
    (goodToGood_engine_of_realization W rq s mT dT dOrd bcap r₃ bT Lh vmax Nmat Mmat
      cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd pFor Pstar
      Rbin selRow S Pv huniq hj hetaR hg hgates hcard hdeficit hOuter hbins
      htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd hRegF hdF
      hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist
      hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls hC hcost hcomp iotaA
      iotaB hrow hgame hsplit).1

end Family

/-! ## §5  Statement poles, derived-not-assumed readouts, and hypothesis
consistency

A green build sees none of this.  Each item shows either that a hypothesis kept
above is genuinely not derivable, or that a hypothesis removed above was really
removed, or that the bundle is not degenerate. -/

section Poles

/-- **Pole 1: the outer-copy indexing degenerates at the illegal width `r = 0`.**

`09:105` fixes `q = 2^r` and the realization of `09:1661--1669` demands
`hOuter : oi != oj` -- the owner and the donor sit in *different* outer copies.
At `r = 0` the frozen width is `q = 1`, every donor coordinate collapses to the
single slot, and `hOuter` becomes unsatisfiable, so the whole owner--donor
transfer step is empty there.  The outer-copy layer is therefore load-bearing
and not bookkeeping.

**Self-chosen value, NO legality claimed.**  `r = 0` is not a paper quantity and
is not offered as one: this is a *rejection* probe showing the guard fires at a
width the schedule never selects. -/
theorem outerIndexing_degenerates_at_width_zero :
    ∀ i j : Slot (scaleAlignWidth 0), i = j := by
  intro i j
  exact Subsingleton.elim (α := Fin 1) i j

/-- **Pole 2: the frozen coordinate indexing of `09:1235--1236` is NOT derivable from
the banked `coordUnique`.**

`RoutedSystem.coordUnique` separates two certificates only when they stopped at
the *same* node.  Distinct clean donors have **distinct** owners
(`09:1550--1552`, the banked `RoutedSystem.owner_injOn`), and `owner` is `place`,
so its hypothesis is never satisfiable for the pairs the family ranges over: the
field is vacuous exactly where the frozen coordinate indexing is needed.

This is why `Function.Injective (donorCoord S)` cannot be derived here, and it is
the precise statement of GAP item 2.  R1: the module binds no such hypothesis --
the frozen indexing is recorded as open, not carried.  General. -/
theorem coordUnique_is_vacuous_on_distinct_clean_donors
    {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
    [Fintype ι] [DecidableEq V] (S : RoutedSystem P Coord ι V r A0)
    (huniq : ∀ v : V, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    {i j : ι} (hi : i ∈ S.cleanFinal) (hj : j ∈ S.cleanFinal) (hne : i ≠ j) :
    S.place i ≠ S.place j := fun hplace =>
  hne (S.owner_injOn huniq i hi j hj hplace)

/-- **Pole 3: the erased index is genuinely erased.**

`eq:wrapper-good-to-good` sums over the good donors *other than* `j`, and the
family above is quantified over `(goodDonors).erase j` for that reason.  If the
erasure were dropped, the sum would pick up the term at `i = j`, i.e. the mass
`Pv (own j) j` a donor sends to its **own** owner -- the very term
`eq:wrapper-mass-leaves-owner` excludes on `09:1612`.  Concretely, over a
one-element index the erased sum is empty while the unerased one is not. -/
theorem family_index_must_erase_the_donor :
    (({0} : Finset ℕ).erase 0) ≠ ({0} : Finset ℕ) := by
  decide

/-- **Pole 4: the terminal hardness may not enter unconditionally, at any index
of the family.**

The family threads `lem:terminal-two-stream` through the per-index `hstateOf`,
which fires only after the transfer trigger has produced an arrival.  Were the
hardness `C <= B` available unconditionally at an owner of the alleged shallow
protocol, the derived residual budget of `09:1341--1343` would already
contradict it -- this is the banked
`DenseWrapperFrontier.finalNode_budget_contradiction`, reached here through the
*derived* budget `owner_residual_budget` rather than through an assumed one.

**No new mathematics.**  This is the banked contradiction in negated form; it is
recorded because the vacuity route it rules out is invisible in a green build.
General. -/
theorem ownerFamily_unconditional_hardness_is_contradictory
    {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ} {C : ℕ}
    [Fintype ι] (S : RoutedSystem P Coord ι V r A0) {i : ι} (hi : i ∈ S.cleanFinal)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1) :
    ¬ (C ≤ (descend P (S.node (S.owner i))).cost) := fun hlow =>
  finalNode_budget_contradiction hC (owner_residual_budget S hi hcost) hlow

/-- **Derived-not-assumed readout 1: `hq_2` really is discharged.**

The seam theorem `ownerStateOf` takes no `0 < W.q_2` binder, because
`09:1670--1671` supplies it: the structural gates give `q_2 >= 16` at every legal
Stage-2 width record.  This is the closed form of the **F3 route**, exhibited so
that the discharge is visible without reading the proof term. -/
theorem structural_gates_discharge_q2 (W : StageTwoRelaxed.StageTwoWidths) :
    0 < W.q₂ :=
  lt_of_lt_of_le (by norm_num) (structuralReadout W).1

/-- **Derived-not-assumed readout 2: the owner threshold stays legal after the
seam.**

The pair `(eps_i, delta_i)` the seam hands to `lem:terminal-two-stream` is
positive and at most `1` at **the banked probe widths**
`TerminalTwoStream.probeWidths`.  R5, corrected: those are the *dyadic*
widths `q_2 = 128`, `b_1 = 24` that
`TerminalTwoStream.probeWidths_dyadic_readout` records (renamed at `cc-t7p`
from `probeWidths_are_legal`, which over-suggested schedule legality: the
record fails the `eq:t2-search` floor `06:766`) -- **not** minima; the frozen
structural minimum is `q_2 >= 16` (`09:1671`).  The `eps = 0` appearing on the
right is inherited from the banked
`TerminalTwoStream.probeEntry_holds`, which states `eq:terminal-entry` at
`eps = 0`, `delta' = 1`.  The width positivity now comes from
`structural_gates_discharge_q2` rather than from a binder, so closing the seam
did not make the transferred hypothesis bundle inconsistent. -/
theorem seam_preserves_threshold_legality :
    0 < ownerThreshold TerminalTwoStream.probeWidths.q₂
        TerminalTwoStream.probeWidths.b₁ 0
      ∧ ownerThreshold TerminalTwoStream.probeWidths.q₂
        TerminalTwoStream.probeWidths.b₁ 0 ≤ 1 :=
  ⟨ownerThreshold_pos (structural_gates_discharge_q2 TerminalTwoStream.probeWidths) le_rfl,
    TerminalTwoStream.probeEntry_holds.2.2⟩

/-- **Hypothesis consistency at the COORDINATE type only.**

R2, corrected scope: this statement is about the coordinate carrier, not about a
donor family.  At the smallest width admitting two distinct outer copies --
`r = 1`, so `q = 2^1 = 2` by `09:105` -- it exhibits that the carrier has exactly
two elements, that an injective self-map of it exists, and that the
realization's `hOuter : oi != oj` is satisfiable there.  It constructs **no**
`RoutedSystem` and **no** donor index, so it does *not* show
`Function.Injective (donorCoord S)` consistent with a plural donor family; that
would need the unbuilt routing dynamics of GAP item 2.

What it does rule out is the cardinality trap the frozen indexing would raise if
it were ever added as a hypothesis: an injection `iota -> Slot q` forces
`|iota| <= q`, and the frozen counting runs the same way (`c <= q`, the
inference the paper records at `09:1564`), so the two are compatible in
direction rather than contradictory.

**Self-chosen value, NO legality claimed.**  `r = 1` is the smallest width at
which `hOuter` can be met; it is an audit point for this encoding, not a
schedule value the paper selects. -/
theorem crdInj_is_consistent_with_two_donors :
    Fintype.card (Slot (scaleAlignWidth 1)) = 2
      ∧ Function.Injective (id : Slot (scaleAlignWidth 1) → Slot (scaleAlignWidth 1))
      ∧ ∃ i j : Slot (scaleAlignWidth 1), i ≠ j := by
  refine ⟨rfl, fun a b h => h, ?_⟩
  exact (⟨0, 1, by decide⟩ : ∃ i j : Fin 2, i ≠ j)

/-- **Hypothesis consistency for the derived good-to-good step: the schedule
side of the family is jointly satisfiable, and the frozen strict gap survives.**

`goodToGood_engine_derived` conjoins `0 < eta_R`, `0 < g`, the three clauses of
`eq:wrapper-owner-gates` and the deficit majorant of
`eq:wrapper-baseline-deficit-sum`.  The derive-`False` attempt on that bundle
fails, and the reason is banked: `WrapperMassRedistribution.ownerGates_nonvacuous`
exhibits legal `q_2`, `b_1` for **any** width and any `eta_R` inside the frozen
window, and the frozen conclusion's strict gap `3 eta_R/16 < eta_R/4` then holds
outright.  No numeral is chosen here: `eta_R` and `g` are the caller's, subject
only to the two frozen legality conditions the banked lemma names, and `q_2`,
`b_1` come from the paper's own least-power-of-two accessors inside it. -/
theorem goodToGood_schedule_side_is_satisfiable {q : ℕ} {etaR g : ℝ}
    (hq : 0 < q) (hetaR0 : 0 < etaR) (hetaR : etaR ≤ 1 / 36800)
    (hg : muP ≤ g / 20) :
    ∃ q₂ b₁ : ℕ, 16 ≤ q₂ ∧ 16 * q₂ ≤ 2 ^ b₁
      ∧ wrapperOwnerGates q q₂ etaR g b₁ ∧ 3 * etaR / 16 < etaR / 4 := by
  obtain ⟨q₂, b₁, h16, hpow, hgates⟩ := ownerGates_nonvacuous hq hetaR0 hetaR hg
  exact ⟨q₂, b₁, h16, hpow, hgates, by linarith⟩

/-! ### §5b  The F1 battery: why the fibre degree must be indexed by the
reservoir, and why the identified width is legal

These five are the r1 aux-lemma battery.  All are GENERAL properties of the
banked `RegularOn` and of the frozen width, and all are proved.  Together they
turn the r0 gate's finding F1 from a review remark into a theorem: a single
scalar foreign degree *provably* collapses the two reservoirs of `09:1644--1645`,
and the frozen `09:725--732` degrees are not equal, so the collapsed bundle is
not inhabited at the paper's instance. -/

/-- **Aux 11 (identity/uniqueness for the exact fibre degree).**  `RegularOn` is
an exact count (`TerminalStateRealization.RegularOn`), so a reservoir determines
its degree: two degrees witnessing regularity of the same set along the same map
are equal, as soon as there is a bin to count into.  General. -/
theorem regularOn_degree_unique {A B : Type*} [DecidableEq B] [Nonempty B]
    {R : Finset A} {φ : A → B} {d d' : ℕ}
    (h : RegularOn R φ d) (h' : RegularOn R φ d') : d = d' :=
  (h (Classical.arbitrary B)).symm.trans (h' (Classical.arbitrary B))

/-- **Aux 12 (round trip: the exact degree recovers the reservoir's size).**  A
regular reservoir has `|R| = d * |B|`: the fibres partition it and each has
exactly `d` elements.  This is the sense in which the degree is data about the
reservoir and not a free parameter -- and it is why two reservoirs of different
sizes over a common bin carrier cannot share one degree.  General. -/
theorem card_eq_degree_mul_card_of_regularOn {A B : Type*} [DecidableEq B]
    [Fintype B] {R : Finset A} {φ : A → B} {d : ℕ} (h : RegularOn R φ d) :
    R.card = d * Fintype.card B := by
  have hsum : R.card = ∑ b : B, (R.filter fun a => φ a = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  rw [hsum, Finset.sum_congr rfl (fun b _ => h b), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.mul_comm]

/-- **Pole 5 (the F1 defect, as a theorem).**

The parked generation bound a single natural `dFor` *outside* the `forall Rf` of
`hRegF`.  This lemma is what that shape says: given regularity of both foreign
reservoirs of `09:1644--1645` at one common degree, their own exact degrees
coincide.  The frozen `09:725--732` gives `d_Sigma = w_Sigma |J_2|^{s-1}` and
`d_D = w_D`, with `08:100--102` fixing `w_Sigma = M_0 D_0`, `w_D = M_0 S_0`;
these are equal only if `D_0 |J_2|^{s-1} = S_0`, which no frozen gate imposes.
So the collapsed premise bundle is not inhabited at the paper's own instance,
which is exactly why `ownerStateOf` and `ownerTransfer_lt_of_realization` now
carry `dF : Finset Rw -> N`.  General. -/
theorem singleForeignDegree_collapses_the_two_reservoirs
    {A B : Type*} [DecidableEq B] [Nonempty B]
    {RSig RD : Finset A} {φ : A → B} {dFor dSig dD : ℕ}
    (hsingle : ∀ Rf : Finset A, (Rf = RSig ∨ Rf = RD) → RegularOn Rf φ dFor)
    (hSig : RegularOn RSig φ dSig) (hD : RegularOn RD φ dD) :
    dSig = dD :=
  (regularOn_degree_unique hSig (hsingle RSig (Or.inl rfl))).trans
    (regularOn_degree_unique (hsingle RD (Or.inr rfl)) hD)

/-- **Pole 6 (the repaired shape is inhabited where the parked one is not).**

Two distinct reservoirs, both regular along one map into a common bin carrier,
at **different** positive degrees -- so the reservoir-indexed hypothesis pair
`hRegF`/`hdF` of `ownerStateOf` is satisfiable exactly where the single-scalar
pair of the parked generation is refuted by Pole 5.

**BEYOND-PAPER audit instance, NO legality claimed.**  The carriers `Fin 3` and
`Fin 1` and the reservoirs `{0,1}`, `{2}` are chosen by this development to
audit *our encoding* of the hypothesis shape at a point the frozen paper never
visits; they are not the paper's `R_Sigma`, `R_D`, `J_2`, and nothing here
claims the frozen degrees.  The paper's own instance of the shape is the pair
`d_Sigma = w_Sigma |J_2|^{s-1}`, `d_D = w_D` of `09:725--732`, whose
construction is unbuilt and stays registered as the deferred canonical
inhabitation. -/
theorem foreignDegrees_may_differ :
    ∃ (RSig RD : Finset (Fin 3)) (φ : Fin 3 → Fin 1) (dF : Finset (Fin 3) → ℕ),
      RSig ≠ RD
        ∧ (∀ Rf : Finset (Fin 3), (Rf = RSig ∨ Rf = RD) → RegularOn Rf φ (dF Rf))
        ∧ (∀ Rf : Finset (Fin 3), (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
        ∧ dF RSig ≠ dF RD := by
  refine ⟨{0, 1}, {2}, fun _ => 0, fun R => R.card, by decide, ?_, ?_, by decide⟩
  · rintro Rf (rfl | rfl) <;> intro b <;> fin_cases b <;> decide
  · rintro Rf (rfl | rfl)
    · decide
    · decide

/-- **Derived-not-assumed readout 3 (R7): the identified width is legal.**

`09:105` fixes the scale-alignment width `q = 2^r`, `09:1250` stops each routed
branch "after `r` Alice queries", and `09:1264` bounds the frontier by the same
`q`.  `goodToGood_engine_of_realization` and
`goodDonor_mass_to_exceptional_of_realization` take all three at one `rq`.  This
readout records that the identification is nondegenerate at **every** exponent:
the width is positive and the coordinate carrier has exactly that many outer
copies, so pinning `rr = rq` and `qw = scaleAlignWidth rq` never empties the
carrier.  (Pole 1 is the complementary fact that `rq = 0` kills `hOuter`.)
General. -/
theorem identified_width_is_nondegenerate (rq : ℕ) :
    0 < scaleAlignWidth rq
      ∧ Fintype.card (Slot (scaleAlignWidth rq)) = scaleAlignWidth rq :=
  ⟨scaleAlignWidth_pos rq, Fintype.card_fin _⟩

end Poles

end EthInapproximability.ParameterizedNP.OwnerIndexedTransferFamily
