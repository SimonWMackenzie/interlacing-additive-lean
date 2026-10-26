import EthInapproximability.ParameterizedNP.WrapperLossTable
import EthInapproximability.ParameterizedNP.RetentionSupply

/-!
# Parameterized NP route: the owners and loss-table layer on the CONSTRUCTION PATH

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche), **lines `09:1535--1781`**.  Every
  anchor named below was opened first-hand in that file for this tranche.

  The frozen items this module carries onto the construction path, in print
  order:

  1. `09:1535--1540`, the Bob-heavy test -- "Call a clean donor `j` *Bob-heavy*
     if `sum_{v: first-Bob frontier node} P_v({j}) > eta_R/4`, where mass is
     normalized by `m`" -- and `eq:wrapper-bob-heavy-count` (display
     `09:1542--1547`, label `09:1546`);
  2. `09:1548`, "Let `J_good` be the other clean donors", and `09:1550--1553`,
     the owner sentence with the exceptional classification ("Every clean
     reference certificate has a unique final node, its *owner*.  Distinct clean
     donors have distinct owners because a final node contains at most one clean
     certificate.  Let `n_T` be the total number of final nodes.  All final
     nodes not owned by `J_good` are called exceptional");
  3. `eq:wrapper-exceptional-count` (display `09:1555--1563`, label `09:1562`)
     with its frozen justification `09:1564`, "Here we used `K_B + n_T <= q` and
     `eq:wrapper-clean-count`";
  4. `09:1566--1584`, the `m_{j,T}`/`own(i)` conventions, the four-disjoint-
     categories sentence `09:1569--1570`, and the **table** `09:1571--1584`
     itself with its four rows -- "initially deleted rows, at most `eta_R m/16`"
     (`09:1574--1575`), "base rows lost along the unique clean route, less than
     `eta_R m/16`" (`09:1576--1577`), "protected rows stopped at first-Bob nodes,
     at most `eta_R m/4`" (`09:1578--1579`), "protected rows sent to other final
     nodes, the remaining loss" (`09:1580--1581`);
  5. `09:1600--1610`, the retention/hardness step, and
     `eq:wrapper-mass-leaves-owner` (display `09:1611--1615`, label `09:1614`);
  6. `09:1702`, "If `e_T = 0`, this is already a contradiction", with `09:1704`'s
     "Assume then that `e_T > 0`".

* **The construction chain this module fires them at** -- the second frozen
  strand, opened first-hand for this tranche:
  * `09:1187--1193`, the contradiction frame: "Fix an arbitrary retained matrix
    `U'` in `[U]_{1,1-delta_U,theta}` and suppose for contradiction that a
    protocol `P` of cost at most `C+r-1` computes `U'`."  The protocol is
    **arbitrary**; nothing about completion is supposed;
  * `09:1195--1215`, `lem:wrapper-no-bob-completion` and the substitution step,
    banked as `RoutedCertificateConstruction.completeNoBob`,
    `completedNoBob_completeNoBob`, `completeNoBob_cost_le_frame`,
    `completeNoBob_computes` and `completedSystem`;
  * `09:1217--1236`, the retention `A_r <= |R i|`, banked as
    `RetentionSupply.retentionSupply` and, at the paper's own
    `A_0 = ceil(2 x_T m_G)` (`09:1219` with `08:166`),
    `RetentionSupply.retentionSupply_at_paper_A0`;
  * `09:1250--1259` and `09:1264`, the two stopping rules and `sum_v kappa_v <= q`,
    banked as `FrontierIndexing.canonicalSystem` and consumed here only through
    `completedSystem`.

* **Cross-anchors opened first-hand for this tranche:** `09:1519--1520` (`c` as
  `|J_clean|`), `09:1526--1534` (`eq:wrapper-total-early-mass`, the `htot` slot),
  `09:1315--1344` (`lem:final-reference-uniqueness` -- statement `09:1315--1319`,
  proof `09:1321--1344` -- the ladder behind `huniq`),
  `09:1352--1357` (the `eq:wrapper-clean-count` display itself, the `hclean` slot;
  its three node classes and the variable `c` are introduced at `09:1346--1351`),
  `09:1585--1598`
  (the three frozen table-row justifications, `delta_U q <= eta_R/16`,
  `q A_0 <= eta_R m/16`, and "the definition of not being Bob-heavy"),
  `09:1603--1604` (the frozen `1/16+1/16+1/4+1/2` arithmetic), and
  `06:204--219`/`06:228` (`eq:eta-choice` and the frozen chain
  `0 < eta_R <= eta_C/2 < tau < x_N`) in `06-parameter-schedule.tex` (SHA-256
  `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
  recomputed first-hand this tranche).

* **Reader counterpart: NONE claimable.**  `routes/parameterized-np/reader-facing/`
  `sections/` was searched first-hand for this tranche.  The only passage
  covering this material is running prose in the proof of
  `thm:paper-adapted-stage4-interface`: `A-stage4-details.tex:376` ("restriction
  or one terminal owner receives enough protected mass from a ...") and
  `A-stage4-details.tex:396` ("The complete owner--donor count is finite: it uses
  only the fixed reservoir ...").  Neither is a numbered item, and the
  READER-COUNTERPART rule forbids citing prose and forbids reusing another
  declaration's item.  The predecessor tranches `WrapperLossTable` and
  `RoutedCertificateConstruction` recorded the same absence; it is inherited, not
  newly asserted.

* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively, by either of the two imports.
* **Proof status:** new wiring; no mathematics is added.

## What this tranche lands, and what it deliberately is not

Every banked module of `sec:wrapper-mass-redistribution` states its counting,
ownership and loss-table results **over a routed system whose protocol is already
assumed completed** -- the binder `hcomp : CompletedNoBob P r` -- and over a
retention `hR` that is likewise assumed.  The construction chain
(`RoutedCertificateConstruction`, `RetentionSupply`) produces both from the
frozen `09:1187--1193` frame, but nothing had yet carried the owners and
loss-table layer across that seam.

This module carries it.  Every declaration of Sections 2--5 below is stated at
`RoutedCertificateConstruction.completedSystem P hR` for an **arbitrary** alleged
protocol `P`, with

* `hcomp` **discharged** by `completedNoBob_completeNoBob`;
* the completed protocol's cost bound **derived** from the *original* protocol's
  `09:1192` bound by `completeNoBob_cost_le_frame`;
* the completed protocol's `Computes` obligation **derived** from the original's
  by `completeNoBob_computes` (`09:1205--1206`);
* and, in Section 6, the retention `hR` itself **produced** from the retained
  matrix's bracket membership by `RetentionSupply.retentionSupply`.

**Census of the name-matching predecessor modules.**
All **eleven name-matching predecessor modules** are delineated here, including
modules this tranche does not consume and the unrelated `DenseSourceOwners` name
match, so that no reader has to guess which side of the seam a statement lives
on.  Everything this module *does* consume, it consumes **by pin**, never
restated:

* `WrapperMassRedistribution` **owns** the pure arithmetic of `09:1526--1781`
  (`earlyMassCoeff`, `BobHeavy`, `wrapperBobHeavyCount`,
  `wrapperExceptionalCount`, `wrapperMassLeavesOwner`, `ownerThreshold`,
  `deltaZero`, `wrapperTerminalDonorGate`).  **Consumed here** only
  transitively, through the engines below: no declaration of this module names
  it.
* `BobHeavyDonorCount` **owns** `eq:wrapper-bob-heavy-count` at the canonical
  system and the schedule bridge `e_B <= E_B`.  **Not re-fired here:** Section 2
  fires the *engine*, so no schedule quantity enters this path at all.
* `WrapperExceptionalCount` **owns** `eq:wrapper-exceptional-count` at the
  canonical system, `ownerUniqueness_of_ladder`, and `|J_good| >= q - E_T`.
  **Consumed here:** `ownerUniqueness_of_ladder` (Section 3).
* `WrapperLossTable` **owns** the loss table read as the owner leakage, `09:1702`
  in both forms, and the terminal donor gate.  **Consumed here:**
  `ownerLeakage_gt_of_fourCategories`, `eT_zero_is_contradictory`,
  `not_finalNodes_subset_goodOwners` (Sections 4--5).
* `MassRedistributionCounting` **owns** the frozen index sets `bobHeavyDonors`,
  `goodDonors`, `exceptionalFinal` and their two counting engines.  **Consumed
  here:** the two engines (Sections 2--3); the sets are used *by name*, never
  redefined.
* `MassLeavesOwner` **owns** `rowDensity`, `ownerRect`, the retention identity
  and `massLeavesOwner_of_fourCategories`.  **Consumed here:** `rowDensity` and
  the four-category endpoint (Section 4).
* `MassRedistributionEntry` **owns** the *earlier* entry wiring into this
  subsection (`firstBob_earlyMass_lt_of_closure`, `earlyMass_lt_of_cleanCount`),
  i.e. `eq:wrapper-total-early-mass` reached through the construction path.
  **Not consumed here:** Section 2 takes `htot` as an explicit binder.
* `OwnerMassTransfer` **owns** the direct owner-mass definitions -- the
  owner-threshold system, `streamRows` and the owner transfer bound of
  `09:1617--1699`.  **Not consumed here:** that range is GAP-EXPOSED item 1.
* `OwnerIndexedTransferFamily` **owns** the outer-copy indexing layer and the
  owner-indexed transfer family (`donorCoord` and its injectivity).  **Not
  consumed here:** this is the untravelled transfer *realization* whose carriers
  are matrix-side (GAP-EXPOSED item 1).
* `OwnerFamilyToPigeonhole` **owns** the downstream pigeonhole layer that wires
  the owner family into the terminal pigeonhole of `09:1704--1781`.  **Not
  consumed here:** that range is GAP-EXPOSED item 3.
* `DenseSourceOwners` is the **unrelated earlier** dense-source ownership layer of
  the Stage-4 lemma battery (`08-dense-stage4.tex`), not part of
  `sec:wrapper-mass-redistribution` at all.  It is listed only because its name
  matches; **nothing here consumes it**.

**One new type, and why.**  `LossTable` (Section 1) is the frozen tabular display
`09:1571--1584` itself: five row sets, the cover and pairwise disjointness of
`09:1569--1570` ("fall into four disjoint categories"), and the three budgets the
table prints.  It is the paper's own object -- a single display -- and not a
premise bundle assembled for convenience: the fourth row carries **no** field,
because `09:1581` gives it none ("the remaining loss"), and no field restates a
derived telescope (the retention is the *consequence*
`LossTable.rowDensity_retained`, derived from the four-category partition
`09:1569--1584`, not a field).  `09:1600--1601` is that consequence's frozen
**consumer** -- the conditional sentence "If the last line were at most
`eta_R m/2`, then the owner would retain more than" -- not the display of the
identity itself.  Its ten frozen clauses were previously ten loose binders
repeated at every consumer.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:262--263`,
`09:1780--1781`) is neither stated nor implied.

## GAP-EXPOSED (named ranges, with the next-round prescription)

1. **`09:1617--1699` is not travelled on the construction path.**  The
   owner-to-owner transfer family, `eq:wrapper-owner-threshold`,
   `eq:wrapper-baseline-deficit-sum`, `eq:wrapper-owner-gates` and
   `eq:wrapper-good-to-good` are banked at an abstract routed system
   (`OwnerIndexedTransferFamily`, `WrapperLossTable` Section 2) and are **not**
   re-fired at `completedSystem` here: doing so needs the realization telescope
   `hstateOf`/`hTTS`/`hsplit`/`iotaA`/`iotaB`/`hrow`/`hgame`, whose carriers are
   matrix-side and are GAP-EXPOSED item 2 of `RoutedCertificateConstruction`.
   Section 5 therefore takes the `09:1700--1701` endpoint as its explicit
   hypothesis `hexc` rather than deriving it.  *Next round:* transport the
   telescope along `completedSystem` once the protected reservoirs exist.
2. **`Pv` is still a binder** (`09:1367--1384`, `09:1418--1531`).  The two
   protected row reservoirs and the mass `P_v(J_0)` are matrix-side objects; no
   declaration below constructs them, exactly as in the predecessor.
3. **`09:1704--1781` is untouched.**  The pigeonhole, `delta_0`, `u_don`, the
   projection cover, the block supply and the row-(iv) Extension call are not
   reached from anything below.
4. **The retention seam of Section 6 is index-typed.**  `retentionSupply`
   produces `hR` over `Fin (2^r)`; the canonical firings of
   `BobHeavyDonorCount`/`WrapperExceptionalCount` are stated over
   `StartedCoord E_0`.  Section 6 is therefore stated at the `Fin (2^r)`
   coordinate type the supply produces, and the transport to `StartedCoord E_0`
   (i.e. `09:1235--1236`'s "every coordinate **outside `E_0`**") is **not**
   performed.  *Next round:* the coordinate-restriction map, which is the
   "outside `E_0`" construction of `09:1233--1236` read against the **definition**
   of `E_0` at `09:447--450` ("Let `E_0` be the union of all singleton, pair, and
   small-copy covers, and put `e_0 = |E_0|`").  `09:452--453` is only the
   deterministic bound `e_0 <= e_0^max`, not the definition.

## Canonical inhabitation

`LossTable` is the paper's own display, and the paper's own instance of it is the
four-category decomposition at `own(j)` for a good donor `j` of the alleged
shallow protocol of `09:1187--1193` -- a protocol whose non-existence is the
conclusion of the subsection, so the frozen paper exhibits no such table by
construction.  The canonical-inhabitation obligation is therefore **REGISTERED
and DEFERRED**: it is discharged when the matrix-side reservoirs and the retained
matrix `U'` of `09:1188--1191` land, never by the probe.  The probe of Section 7 is
explicitly **NON-FIDELITY**: its row carrier is `Fin n`, not `Rows(N)`, and its
width is chosen by *us* from the gate `16 < eta_R n`; it claims only that our
encoding of the frozen table is inhabited with every category carrying strictly
positive mass, at a tolerance `eta_R` taken from the schedule's **defining**
display `ParameterSchedule.etaR` rather than from a numeral.

`completedSystem`'s own inhabitation obligation is inherited from
`canonicalSystem` and was recorded by the predecessor; nothing here reopens it.
-/

namespace EthInapproximability.ParameterizedNP.MassRedistributionOwners

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.MassLeavesOwner
open EthInapproximability.ParameterizedNP.OwnerMassTransfer

/-! ## §1  The frozen four-category table, as the display it is
(`09:1569--1584`)

"The rows of a good donor missing from its owner fall into four disjoint
categories:" followed by the tabular display with its four rows.

The fields below are, in order, the display's own clauses and nothing else:
the five row sets, the cover and pairwise disjointness of the sentence
`09:1569--1570`, and the three budgets the table prints.  The fourth row carries
**no** field: `09:1581` prints "the remaining loss", i.e. it constrains nothing,
and inventing a bound for it would be a structure demanding more than the paper.

The retention is *not* a field either -- it is derived (`rowDensity_retained`
below) from the cover and disjointness of `09:1569--1584`, which is exactly how
the frozen text obtains it.  `09:1600--1601` is where the frozen text then
*consumes* that retention ("If the last line were at most `eta_R m/2`, then the
owner would retain more than"); it is a conditional sentence, not the identity. -/

section Table

/-- **`09:1569--1584`, the four-category loss table at one owner.**

`Rw` is the row carrier of the owner's copy of `N`, so `Fintype.card Rw = m` and
`MassLeavesOwner.rowDensity` is the frozen normalization "by `m`" of `09:1567`
and `09:1540`.  The four categories are the table's four rows:

* `deleted` -- `09:1574--1575`, "initially deleted rows ... at most `eta_R m/16`";
* `routeLoss` -- `09:1576--1577`, "base rows lost along the unique clean route ...
  less than `eta_R m/16`" (**strict**, as printed, and as `09:1595`'s
  `(q-1)A_0 < q A_0` produces it);
* `earlyStopped` -- `09:1578--1579`, "protected rows stopped at first-Bob nodes ...
  at most `eta_R m/4`", which `09:1598` calls "the definition of not being
  Bob-heavy";
* `sentElsewhere` -- `09:1580--1581`, "protected rows sent to other final nodes ...
  the remaining loss", **unconstrained** here.

`retained` is the complement the frozen sentence speaks of: `09:1569` says the
rows *missing from its owner* fall into the four categories, so the cover field
is an equation on `univ \ retained`. -/
structure LossTable (Rw : Type*) [Fintype Rw] [DecidableEq Rw] (etaR : ℝ) where
  /-- The rows of the good donor retained at its owner: the complement of the
  four categories of `09:1569--1584`, whose density `09:1600--1601` consumes. -/
  retained : Finset Rw
  /-- Table row 1 (`09:1574`): initially deleted rows. -/
  deleted : Finset Rw
  /-- Table row 2 (`09:1576`): base rows lost along the unique clean route. -/
  routeLoss : Finset Rw
  /-- Table row 3 (`09:1578`): protected rows stopped at first-Bob nodes. -/
  earlyStopped : Finset Rw
  /-- Table row 4 (`09:1580`): protected rows sent to other final nodes. -/
  sentElsewhere : Finset Rw
  /-- `09:1569`: the missing rows are exactly the four categories. -/
  cover : (Finset.univ : Finset Rw) \ retained
    = deleted ∪ routeLoss ∪ earlyStopped ∪ sentElsewhere
  /-- `09:1569`, "disjoint". -/
  disjoint₁₂ : Disjoint deleted routeLoss
  /-- `09:1569`, "disjoint". -/
  disjoint₁₃ : Disjoint deleted earlyStopped
  /-- `09:1569`, "disjoint". -/
  disjoint₁₄ : Disjoint deleted sentElsewhere
  /-- `09:1569`, "disjoint". -/
  disjoint₂₃ : Disjoint routeLoss earlyStopped
  /-- `09:1569`, "disjoint". -/
  disjoint₂₄ : Disjoint routeLoss sentElsewhere
  /-- `09:1569`, "disjoint". -/
  disjoint₃₄ : Disjoint earlyStopped sentElsewhere
  /-- `09:1575`: "at most `eta_R m/16`". -/
  deleted_le : rowDensity deleted ≤ etaR / 16
  /-- `09:1577`: "less than `eta_R m/16`". -/
  routeLoss_lt : rowDensity routeLoss < etaR / 16
  /-- `09:1579`: "at most `eta_R m/4`". -/
  earlyStopped_le : rowDensity earlyStopped ≤ etaR / 4

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw] {etaR : ℝ}

/-- **Aux T1 (identity).**  `09:1569--1570` as a count: the retained rows and the
four categories exhaust the owner's copy of `N`.  Stated additively, so no
natural-number truncation occurs.  General in the row carrier and the
tolerance. -/
theorem LossTable.card_partition (T : LossTable Rw etaR) :
    T.retained.card
        + (T.deleted.card + T.routeLoss.card + T.earlyStopped.card
            + T.sentElsewhere.card)
      = Fintype.card Rw :=
  card_retained_add_card_categories T.cover T.disjoint₁₂ T.disjoint₁₃ T.disjoint₁₄
    T.disjoint₂₃ T.disjoint₂₄ T.disjoint₃₄

/-- **Aux T2 (round trip: counts to densities).**  The density identity derived
from the four-category partition `09:1569--1584`.  The frozen text does not print
this identity anywhere; it *consumes* it at `09:1600--1601` ("If the last line
were at most `eta_R m/2`, then the owner would retain more than"), so that
conditional sentence is this lemma's consumer, not its source.  This is what
makes the retention a *derived* consequence of the table rather than a field of
it.  General. -/
theorem LossTable.rowDensity_retained (T : LossTable Rw etaR)
    (hRw : 0 < Fintype.card Rw) :
    rowDensity T.retained
      = 1 - (rowDensity T.deleted + rowDensity T.routeLoss + rowDensity T.earlyStopped
          + rowDensity T.sentElsewhere) :=
  rowDensity_retained_eq hRw T.cover T.disjoint₁₂ T.disjoint₁₃ T.disjoint₁₄
    T.disjoint₂₃ T.disjoint₂₄ T.disjoint₃₄

/-- **Aux T3 (the frozen `1/16 + 1/16 + 1/4` head).**

`09:1603` prints the four coefficients `1/16 + 1/16 + 1/4 + 1/2`; the first three
are the table's own budgets and sum to `3/8`, strictly, because the second row is
strict.  This is the arithmetic `09:1604--1605` then turns into `1 - 7 eta_R/8 >
1 - eta_R`; the banked `WrapperMassRedistribution.fourCategory_coefficients` owns
that final comparison and is not restated.  General. -/
theorem LossTable.head_rows_lt (T : LossTable Rw etaR) :
    rowDensity T.deleted + rowDensity T.routeLoss + rowDensity T.earlyStopped
      < 3 * etaR / 8 := by
  have h₁ := T.deleted_le
  have h₂ := T.routeLoss_lt
  have h₃ := T.earlyStopped_le
  linarith

/-- **Aux T4 (monotonicity in the tolerance).**  A loss table at `eta_R` is a
loss table at any larger tolerance, with the *same* five row sets: the three
budgets are upper bounds and the cover and disjointness do not mention `eta_R`.
This is the sanity check that `eta_R` enters the display only through its three
budgets.  General. -/
def LossTable.mono (T : LossTable Rw etaR) {etaR' : ℝ} (h : etaR ≤ etaR') :
    LossTable Rw etaR' where
  retained := T.retained
  deleted := T.deleted
  routeLoss := T.routeLoss
  earlyStopped := T.earlyStopped
  sentElsewhere := T.sentElsewhere
  cover := T.cover
  disjoint₁₂ := T.disjoint₁₂
  disjoint₁₃ := T.disjoint₁₃
  disjoint₁₄ := T.disjoint₁₄
  disjoint₂₃ := T.disjoint₂₃
  disjoint₂₄ := T.disjoint₂₄
  disjoint₃₄ := T.disjoint₃₄
  deleted_le := le_trans T.deleted_le (by linarith)
  routeLoss_lt := lt_of_lt_of_le T.routeLoss_lt (by linarith)
  earlyStopped_le := le_trans T.earlyStopped_le (by linarith)

/-- **Aux T5 (the deliverable is not satisfied by the empty fourth row).**

`eq:wrapper-mass-leaves-owner` says the fourth category carries more than
`eta_R/2`.  At a positive tolerance that forces the category to be inhabited, so
the frozen conclusion is a genuine constraint on the table and not a bookkeeping
identity.  General. -/
theorem LossTable.sentElsewhere_nonempty_of_massLeaves (T : LossTable Rw etaR)
    (hetaR : 0 < etaR) (h : etaR / 2 < rowDensity T.sentElsewhere) :
    T.sentElsewhere.Nonempty := by
  rcases Finset.eq_empty_or_nonempty T.sentElsewhere with hE | hN
  · rw [hE, rowDensity_empty] at h; linarith
  · exact hN

end Table

/-! ## §2  Bob-heaviness on the construction path (`09:1535--1547`)

The frozen Bob-heavy test and `eq:wrapper-bob-heavy-count`, at the routed system
the construction chain builds from an **arbitrary** alleged protocol.  The set
`bobHeavyDonors` is the banked one of `MassRedistributionCounting` used by name;
nothing is redefined. -/

section BobHeavy

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

omit [DecidableEq Coord] in
/-- **`eq:wrapper-bob-heavy-count` (`09:1542--1547`) with `hcomp` DISCHARGED.**

"Call a clean donor `j` *Bob-heavy* if `sum_{v: first-Bob frontier node} P_v({j})
> eta_R/4` ...  Their number `e_B` satisfies
`e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)`."

Stated at `RoutedCertificateConstruction.completedSystem P hR`, i.e. at the walked
system of the **completion** of the arbitrary protocol `P` of `09:1192--1193`.
No `CompletedNoBob` hypothesis appears anywhere: `completedSystem` supplies it
from `completedNoBob_completeNoBob`.  The counting itself is the banked
`MassRedistributionCounting.wrapperBobHeavyCount_engine` (and behind it
`WrapperMassRedistribution.wrapperBobHeavyCount`), consumed by pin and restated
nowhere.

*What is still a binder.*  `Pv` (GAP-EXPOSED item 2), its nonnegativity `hnonneg`
at the clean donors, and `htot` -- `eq:wrapper-total-early-mass` (`09:1526--1534`)
read at `J_0 = J_clean`.  The retention `hR` is a binder here and is *produced*
in Section 6.  **No hypothesis is added to the banked engine and none is
weakened.**

*Why the trivial witness fails.*  The conclusion is an inequality between two
fixed reals, not an existential; and it is not vacuous, since the right-hand side
is the frozen expression whose ceiling defines `E_B` at `e_0^max` (`06:720--722`).

General in the Alice carrier, both other carriers, the coordinate type, and every
width and tolerance. -/
theorem constructionPath_wrapperBobHeavyCount
    (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {θ : ℝ} {q s : ℕ} {e0 etaR : ℝ}
    (hetaR : 0 < etaR)
    (hnonneg : ∀ j ∈ (completedSystem P hR).cleanFinal,
      0 ≤ firstBobMass (completedSystem P hR) Pv j)
    (htot : earlyMass (completedSystem P hR) Pv (completedSystem P hR).cleanFinal
      ≤ earlyMassCoeff θ q s * (e0 / (1 - vartheta))) :
    ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ≤ 512 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * e0
          / ((1 - vartheta) * etaR) :=
  wrapperBobHeavyCount_engine (completedSystem P hR) Pv hetaR hnonneg htot

/-- **`09:1535` and `09:1548` on the construction path, as a split.**

"Call a clean donor `j` Bob-heavy ...  Let `J_good` be the other clean donors":
at the walked system of an arbitrary alleged protocol, the two frozen classes
partition `J_clean` exactly.  The banked
`MassRedistributionCounting.card_goodDonors_add_card_bobHeavy` is the identity;
what is new is that it holds with no completion hypothesis.  General. -/
theorem constructionPath_donor_split
    (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ) (etaR : ℝ) :
    (goodDonors (completedSystem P hR) Pv etaR).card
        + (bobHeavyDonors (completedSystem P hR) Pv etaR).card
      = (completedSystem P hR).cleanFinal.card :=
  card_goodDonors_add_card_bobHeavy (completedSystem P hR) Pv etaR

end BobHeavy

/-! ## §3  Owners and the exceptional count on the construction path
(`09:1548--1564`)

`09:1550--1552`'s owner uniqueness is fired at the walked system with the ladder's
cost budget taken from the **original** protocol of `09:1192`, which is the only
form of the budget the frozen frame supplies; `completeNoBob_cost_le_frame` is
what makes that legal, and it is `09:1207--1213`'s own cost display. -/

section Owners

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

omit [DecidableEq Coord] in
/-- **`09:1550--1552` at the walked system of an arbitrary alleged protocol.**

"Every clean reference certificate has a unique final node, its *owner*.  Distinct
clean donors have distinct owners because a final node contains at most one clean
certificate."

The banked `WrapperExceptionalCount.ownerUniqueness_of_ladder` states this at a
routed system whose protocol already meets the frozen cost bound.  Here the bound
is the **original** protocol's, `09:1192`'s `P.cost <= C + r - 1`, transported to
the completion by `completeNoBob_cost_le_frame` with `1 <= C` from `hC` --
exactly the frozen justification of `09:1207--1212` ("Hence the completed protocol
has cost at most `max{cost(P), r} <= C+r-1`, because `C >= 1`").

*What is still a binder.*  `residual`/`hresidual` and `hladder`, the
`lem:certified-row-ladder` call of `09:1334--1338`, inherited verbatim.

*Why the trivial witness fails.*  The bound is `<= 1`, not `<= |J_clean|`; it
fails outright for a map sending two clean donors to one node, which is the
configuration `hladder` refutes.  General. -/
theorem constructionPath_ownerUniqueness
    {C : ℕ} (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (residual : CertIndex (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℕ)
    (hresidual : ∀ i j, residual i j
      ≤ (descend (completeNoBob r P)
          ((completedSystem P hR).node ((completedSystem P hR).owner i))).cost)
    (hladder : ∀ i ∈ (completedSystem P hR).cleanFinal,
      ∀ j ∈ (completedSystem P hR).cleanFinal,
      (completedSystem P hR).owner i = (completedSystem P hR).owner j →
      ((completedSystem P hR).cert i).coord ≠ ((completedSystem P hR).cert j).coord →
      C ≤ residual i j) :
    ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1 :=
  WrapperExceptionalCount.ownerUniqueness_of_ladder (C := C) (completedSystem P hR) hC
    (completeNoBob_cost_le_frame (le_trans (by norm_num) hC) hcost) residual hresidual
    hladder

/-- **`eq:wrapper-exceptional-count` (`09:1555--1564`) with `hcomp` DISCHARGED.**

"All final nodes not owned by `J_good` are called exceptional; their number is
`e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`.  Here we used
`K_B + n_T <= q` and `eq:wrapper-clean-count`."

At the walked system of the completion of an arbitrary alleged protocol.  Both
frozen inputs of `09:1564` stay inside the banked
`MassRedistributionCounting.wrapperExceptionalCount_engine`: `K_B + n_T <= q` is
its Kraft step and `|J_good| = c - e_B` its split.  The only binders are `huniq`
-- which Section 3's first theorem *supplies* on this path -- and the first clause
of `eq:wrapper-clean-count` at `J_clean`.

*Why the trivial witness fails.*  The conclusion is a conjunction of two
inequalities between fixed reals, not an existential, and the banked
`WrapperExceptionalCount` records a routed instance with `e_T = 1`, `n_T = 2`,
`c = 2`, `e_B = 1`, so neither clause is checked only against zero.

General in every carrier, width and tolerance. -/
theorem constructionPath_wrapperExceptionalCount
    (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ) (etaR : ℝ)
    (huniq : ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1)
    {q e0 : ℝ} (hq : q = (2 : ℝ) ^ r)
    (hclean : q - e0 / (1 - vartheta) ≤ ((completedSystem P hR).cleanFinal.card : ℝ)) :
    ((exceptionalFinal (completedSystem P hR) Pv etaR).card : ℝ)
        ≤ q - ((completedSystem P hR).cleanFinal.card : ℝ)
            + ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ∧ q - ((completedSystem P hR).cleanFinal.card : ℝ)
            + ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ)
        ≤ e0 / (1 - vartheta)
            + ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ) :=
  wrapperExceptionalCount_engine (completedSystem P hR) Pv etaR huniq hq hclean

/-- **`09:1550--1564` in one proof term on the construction path.**

The seam test for Section 3: from the ladder alone -- with the cost budget of the
*original* alleged protocol, and no completion hypothesis anywhere --
`eq:wrapper-exceptional-count` holds at the walked system.  `huniq` is not
re-introduced as a binder on the way; it is produced inside the proof term by the
first theorem of this section.  General. -/
theorem constructionPath_exceptionalCount_of_ladder
    {C : ℕ} (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ) (etaR : ℝ)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (residual : CertIndex (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℕ)
    (hresidual : ∀ i j, residual i j
      ≤ (descend (completeNoBob r P)
          ((completedSystem P hR).node ((completedSystem P hR).owner i))).cost)
    (hladder : ∀ i ∈ (completedSystem P hR).cleanFinal,
      ∀ j ∈ (completedSystem P hR).cleanFinal,
      (completedSystem P hR).owner i = (completedSystem P hR).owner j →
      ((completedSystem P hR).cert i).coord ≠ ((completedSystem P hR).cert j).coord →
      C ≤ residual i j)
    {q e0 : ℝ} (hq : q = (2 : ℝ) ^ r)
    (hclean : q - e0 / (1 - vartheta) ≤ ((completedSystem P hR).cleanFinal.card : ℝ)) :
    ((exceptionalFinal (completedSystem P hR) Pv etaR).card : ℝ)
        ≤ q - ((completedSystem P hR).cleanFinal.card : ℝ)
            + ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ∧ q - ((completedSystem P hR).cleanFinal.card : ℝ)
            + ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ)
        ≤ e0 / (1 - vartheta)
            + ((bobHeavyDonors (completedSystem P hR) Pv etaR).card : ℝ) :=
  constructionPath_wrapperExceptionalCount P hR Pv etaR
    (constructionPath_ownerUniqueness P hR hC hcost residual hresidual hladder) hq hclean

end Owners

/-! ## §4  The loss table and `eq:wrapper-mass-leaves-owner` on the construction
path (`09:1566--1615`)

The frozen table of Section 1 fired at the walked system of an arbitrary alleged
protocol.  Three obligations of the banked endpoint are **discharged** here that
no banked module could discharge:

* `hcomp : CompletedNoBob` -- by `completedSystem` itself;
* the completed protocol's cost bound -- from `09:1192`'s bound on the original,
  by `completeNoBob_cost_le_frame`;
* the completed protocol's `Computes` obligation -- from `09:1205--1206`'s
  "they do not change ... the computed matrix", i.e. `completeNoBob_computes`,
  applied to the original protocol's computation of the retained matrix `U'`. -/

section LossTableOnPath

variable {X Y : Type*} [Fintype X] [DecidableEq X]
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

omit [DecidableEq Coord] in
/-- **`eq:wrapper-mass-leaves-owner` (`09:1600--1615`) on the construction path.**

"If the last line were at most `eta_R m/2`, then the owner would retain more than
`1 - 7 eta_R/8 > 1 - eta_R` of all rows of its copy of `N` ...  The
deletion-stable Stage-4 theorem would make the owner `C`-hard, impossible under
the alleged shallow protocol.  We have proved `sum_{T != own(j)} m_{j,T} >
eta_R/2`."

Stated at a final Alice node `v` of `completedSystem P hR`, with the four
categories supplied as the single frozen display `LossTable` of Section 1 rather
than as ten loose binders.  The arithmetic and the hardness step are the banked
`MassLeavesOwner.massLeavesOwner_of_fourCategories`, consumed by pin.

*What this adds.*  `halleged` is the **original** protocol's computation of the
retained matrix (`09:1188--1193`), and `hcost` the **original** protocol's cost
bound; both are transported across the completion inside the proof term.  No
caller has to know that a completion happened.

*What is still a binder.*  `hdense` (the deletion-stable Stage-4 conclusion at
the owner's copy of `N`, `08:317`), the column density `hcols` (`09:1607--1608`),
and the rectangle sections `iotaA`/`iotaB`/`hrow`/`hgame` -- GAP-EXPOSED item 2
of `RoutedCertificateConstruction`, inherited verbatim.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
two fixed reals, not an existential, and the table alone does **not** imply it:
`lossTable_alone_does_not_give_massLeavesOwner` in Section 7 exhibits a legal
loss table whose fourth row is far below `eta_R/2`, so the hardness step is
load-bearing.

General in the row and column carriers of the owner's copy of `N`, in the three
protocol carriers, in the coordinate type, and in both tolerances. -/
theorem constructionPath_massLeavesOwner
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] [DecidableEq Rw]
    {C : ℕ} (P : Protocol X Y Bool) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    {v : FrontierNode (completeNoBob r P) R A0 r}
    (hv : (completedSystem P hR).firstBob v = false)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (Nmat : Rw → Cl → Bool) {ηR ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    (T : LossTable Rw ηR) {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC C)
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaA : {a // a ∈ (ownerRect T.retained cols).1} → X)
    (iotaB : {c // c ∈ (ownerRect T.retained cols).2} → Y)
    (hrow : ∀ a, RouteRows (completeNoBob r P) ((completedSystem P hR).node v) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect T.retained cols).1
      (ownerRect T.retained cols).2 a b = gamb (iotaA a) (iotaB b))
    (hηR : 0 < ηR) :
    ηR / 2 < rowDensity T.sentElsewhere :=
  massLeavesOwner_of_fourCategories (completedSystem P hR) hC
    (completeNoBob_cost_le_frame (le_trans (by norm_num) hC) hcost) hv
    (completeNoBob_computes halleged r) Nmat hRw hdense hcols iotaA iotaB hrow hgame
    T.cover T.disjoint₁₂ T.disjoint₁₃ T.disjoint₁₄ T.disjoint₂₃ T.disjoint₂₄
    T.disjoint₃₄ hηR T.deleted_le T.routeLoss_lt T.earlyStopped_le

/-- **`09:1566--1615` in the shape `09:1700--1701` consumes, on the construction
path.**

The same conclusion read on the *leakage* `sum_{T != own(j)} m_{j,T}` of
`09:1612` rather than on the fourth category's density, at the owner of a good
donor `j` of the walked system.  The banked
`WrapperLossTable.ownerLeakage_gt_of_fourCategories` owns this reading; what is
new is that the owner's stopping rule, the cost budget and the computation
obligation all come from the arbitrary protocol of `09:1192--1193`.

`hfourth` is the frozen reading of `09:1580--1581` against `09:1566--1568` -- that
the fourth category *is* the leakage.  The paper states it in prose, so it stays
the explicit binder it is and is never derived from the encoding.  General. -/
theorem constructionPath_ownerLeakage_gt
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] [DecidableEq Rw]
    {C : ℕ} (P : Protocol X Y Bool) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {ηR : ℝ} {j : CertIndex (completeNoBob r P) R A0 r}
    (hj : j ∈ goodDonors (completedSystem P hR) Pv ηR)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (Nmat : Rw → Cl → Bool) {ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    (T : LossTable Rw ηR) {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC C)
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaA : {a // a ∈ (ownerRect T.retained cols).1} → X)
    (iotaB : {c // c ∈ (ownerRect T.retained cols).2} → Y)
    (hrow : ∀ a, RouteRows (completeNoBob r P)
      ((completedSystem P hR).node ((completedSystem P hR).owner j)) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect T.retained cols).1
      (ownerRect T.retained cols).2 a b = gamb (iotaA a) (iotaB b))
    (hηR : 0 < ηR)
    (hfourth : rowDensity T.sentElsewhere = ownerLeakage (completedSystem P hR) Pv j) :
    ηR / 2 < ownerLeakage (completedSystem P hR) Pv j :=
  WrapperLossTable.ownerLeakage_gt_of_fourCategories (C := C) (completedSystem P hR) Pv hj
    hC (completeNoBob_cost_le_frame (le_trans (by norm_num) hC) hcost)
    (completeNoBob_computes halleged r) Nmat hRw hdense hcols iotaA iotaB hrow hgame
    T.cover T.disjoint₁₂ T.disjoint₁₃ T.disjoint₁₄ T.disjoint₂₃ T.disjoint₂₄
    T.disjoint₃₄ hηR T.deleted_le T.routeLoss_lt T.earlyStopped_le hfourth

end LossTableOnPath

/-! ## §5  `09:1702` on the construction path

"If `e_T = 0`, this is already a contradiction."  Both frozen forms, at the walked
system of an arbitrary alleged protocol.  The `09:1700--1701` endpoint itself is
the explicit hypothesis `hexc` -- GAP-EXPOSED item 1: the owner-to-owner transfer
family of `09:1617--1699` is not travelled on this path in this tranche. -/

section VanishingCase

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- **`09:1702` in the counting form, on the construction path.**

The frozen sentence as the contradiction it is: `e_T = 0` and the `09:1701`
endpoint at one good donor are jointly inconsistent, at the walked system of the
completion of an arbitrary alleged protocol.  The banked
`WrapperLossTable.eT_zero_is_contradictory` is consumed by pin.  General. -/
theorem constructionPath_eT_zero_is_contradictory
    (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR : ℝ} {j : CertIndex (completeNoBob r P) R A0 r} (hetaR : 0 < etaR)
    (hexc : etaR / 4 < exceptionalMass (completedSystem P hR) Pv etaR j)
    (heT : (exceptionalFinal (completedSystem P hR) Pv etaR).card = 0) : False :=
  WrapperLossTable.eT_zero_is_contradictory (completedSystem P hR) Pv hetaR hexc heT

/-- **`09:1702` in the ownership form of `09:1553`, on the construction path.**

"All final nodes not owned by `J_good` are called exceptional": the frozen
vanishing case says it is *not* the case that every final node of the walked
system is owned by a good donor.  General. -/
theorem constructionPath_not_finalNodes_subset_goodOwners
    (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR : ℝ} {j : CertIndex (completeNoBob r P) R A0 r} (hetaR : 0 < etaR)
    (hexc : etaR / 4 < exceptionalMass (completedSystem P hR) Pv etaR j) :
    ¬ ((completedSystem P hR).toWrapperFrontier.finalNodes
        ⊆ (goodDonors (completedSystem P hR) Pv etaR).image (completedSystem P hR).owner) :=
  WrapperLossTable.not_finalNodes_subset_goodOwners (completedSystem P hR) Pv hetaR hexc

end VanishingCase

/-! ## §6  The retention `hR` produced, not assumed (`09:1217--1236`)

`RetentionSupply` produces the frozen retention from the retained matrix's own
bracket membership together with the second survival gate.  Section 2's Bob-heavy
count therefore holds at the frozen frame `09:1188--1193` with **no** retention
hypothesis and **no** completion hypothesis: the two binders every banked module
of this subsection carries are both gone.

The coordinate type here is the `Fin (2^r)` the supply produces; the transport to
`StartedCoord E_0` is GAP-EXPOSED item 4 and is not performed. -/

section RetentionFree

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw]

/-- **`eq:wrapper-bob-heavy-count` at the frozen frame, with both binders gone.**

`09:1188--1193` fixes a retained matrix `U'` in the bracket family and an
arbitrary alleged protocol `P` for it of cost at most `C+r-1`.  At that frame --
and with `A_0` at the value its own defining display fixes, `A_0 = ceil(2 x_T
m_G)` of `09:1219` with `x_T = 2^{-b_T}` of `08:166`, evaluated through the banked
`initialRefRows`/`xTdepth` chain rather than assigned -- the frozen Bob-heavy
count holds.

Neither `CompletedNoBob` nor the retention appears: the first is
`completedNoBob_completeNoBob` inside `completedSystem`, the second is
`RetentionSupply.retentionSupply_at_paper_A0` fired at the bracket membership
`hRC` and the second survival gate `hgate` (`09:1228`).

*What is still a binder.*  `Pv` (GAP-EXPOSED item 2), `hnonneg`, and `htot` --
`eq:wrapper-total-early-mass` at `J_0 = J_clean`.  **No hypothesis is added to the
banked engine and none is weakened; full-bundle satisfiability is not claimed.**

General in the row carrier, the column carrier, and every width and tolerance. -/
theorem retentionFree_wrapperBobHeavyCount {Cl : Type*} [Fintype Cl]
    {r bT : ℕ} {δU θ' : ℝ}
    {RC : Finset (Fin 1 × (Fin (2 ^ r) × Rw)) × Finset (Fin 1 → (Fin (2 ^ r) → Cl))}
    (RG : Finset Rw)
    (hRC : RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ')
    (hgate : ((2 ^ r : ℕ) : ℝ) * ((initialRefRows (xTdepth bT) RG.card : ℕ) : ℝ)
        + δU * ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) ≤ ((RG.card : ℕ) : ℝ))
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (Pv : FrontierNode (completeNoBob r P) (RetentionSupply.retainedRefRows RC.1 RG)
        (initialRefRows (xTdepth bT) RG.card) r →
      CertIndex (completeNoBob r P) (RetentionSupply.retainedRefRows RC.1 RG)
        (initialRefRows (xTdepth bT) RG.card) r → ℝ)
    {θ : ℝ} {q s : ℕ} {e0 etaR : ℝ}
    (hetaR : 0 < etaR)
    (hnonneg : ∀ j ∈ (completedSystem P
        (RetentionSupply.retentionSupply_at_paper_A0 RG hRC hgate)).cleanFinal,
      0 ≤ firstBobMass (completedSystem P
        (RetentionSupply.retentionSupply_at_paper_A0 RG hRC hgate)) Pv j)
    (htot : earlyMass (completedSystem P
          (RetentionSupply.retentionSupply_at_paper_A0 RG hRC hgate)) Pv
        (completedSystem P
          (RetentionSupply.retentionSupply_at_paper_A0 RG hRC hgate)).cleanFinal
      ≤ earlyMassCoeff θ q s * (e0 / (1 - vartheta))) :
    ((bobHeavyDonors (completedSystem P
        (RetentionSupply.retentionSupply_at_paper_A0 RG hRC hgate)) Pv etaR).card : ℝ)
      ≤ 512 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * e0
          / ((1 - vartheta) * etaR) :=
  constructionPath_wrapperBobHeavyCount P
    (RetentionSupply.retentionSupply_at_paper_A0 RG hRC hgate) Pv hetaR hnonneg htot

end RetentionFree

/-! ## §7  Canonical inhabitation: REGISTERED, DEFERRED, and a NON-FIDELITY probe

The paper's own loss table lives at `own(j)` for a good donor of the alleged
shallow protocol of `09:1187--1193`, whose non-existence is the conclusion of the
subsection; the frozen text therefore exhibits no such table by construction, and
the matrix-side data it would be built from (`09:1188--1191`'s retained `U'`, the
protected reservoirs of `09:1367--1384`) is not in Lean.  The canonical
inhabitation obligation is **registered and deferred**, and nothing below
discharges it.

What follows claims only that our encoding of the frozen display is inhabited,
with every category carrying strictly positive mass, at a tolerance taken from
the schedule's **defining** display and at a width read off the gate rather than
picked.  It is **NON-FIDELITY**: the row carrier is `Fin n`, not `Rows(N)`. -/

section Probe

/-- The probe's ambient row count.  `n` is not a numeral chosen by inspection: the
**tightest** of the three budget rows of `09:1575`/`09:1577`/`09:1579` is the
strict `09:1577`, which at a singleton category reads `1/n < eta_R/16`, so a legal
width must be a natural strictly above `16/eta_R`.  This accessor is **a uniform
sufficient closed-form width, one above the ceiling** -- the same closed-form
style the schedule uses for its own least-power-of-two quantities.  It is *not*
claimed to be the smallest such natural: when `16/eta_R` is non-integral,
`ceil(16/eta_R)` already exceeds it, and the `+1` is then slack.  Uniform
sufficiency is all the probe needs.  **NON-FIDELITY**: the paper's row count is
`m = |Rows(N)|`, fixed by `09:109` ("Write `m = |Rows(N)|`") for the matrix
`N = transpose(A)` of `08:145--147`, not this. -/
noncomputable def probeWidth (etaR : ℝ) : ℕ := ⌈16 / etaR⌉₊ + 1

/-- **Probe gate.**  The accessor really clears the table's three budgets: at
`n = probeWidth eta_R` a singleton category has density strictly below
`eta_R/16`.  General in `eta_R > 0`. -/
theorem probeWidth_gate {etaR : ℝ} (hetaR : 0 < etaR) :
    16 < etaR * ((probeWidth etaR : ℕ) : ℝ) := by
  have hle : (16 : ℝ) / etaR ≤ ((⌈(16 : ℝ) / etaR⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hlt : (16 : ℝ) / etaR < ((probeWidth etaR : ℕ) : ℝ) := by
    rw [probeWidth]
    push_cast
    linarith
  rw [div_lt_iff₀ hetaR] at hlt
  linarith

/-- **Probe width admits four distinct loss slots and still leaves a retained
row.**  The conclusion is `5 <= probeWidth eta_R`, not `4 <=`: four slots go to
the four categories and the fifth is what `probeLossTable` retains, so the
nondegeneracy claim `T.retained.Nonempty` has room.  At any tolerance below `1`
-- and `06:228`'s frozen chain forces `eta_R < x_N = 1/16`, far below `1` -- the
accessor already reaches `5`.  General. -/
theorem five_le_probeWidth {etaR : ℝ} (hetaR : 0 < etaR) (hle : etaR ≤ 1) :
    5 ≤ probeWidth etaR := by
  have h16 : (16 : ℝ) ≤ 16 / etaR := by
    rw [le_div_iff₀ hetaR]; nlinarith
  have hceil : (16 : ℕ) ≤ ⌈(16 : ℝ) / etaR⌉₊ := by
    have h1 : (16 : ℝ) / etaR ≤ ((⌈(16 : ℝ) / etaR⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((16 : ℕ) : ℝ) ≤ ((⌈(16 : ℝ) / etaR⌉₊ : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  rw [probeWidth]
  omega

variable {n : ℕ} {etaR : ℝ}

/-- The four probe rows, at four distinct slots of the ambient carrier. -/
def probeLossRow (h5 : 5 ≤ n) (k : Fin 4) : Fin n := ⟨k.val, by omega⟩

/-- **Aux P0.**  The four probe slots are distinct.  General. -/
theorem probeLossRow_injective (h5 : 5 ≤ n) {k l : Fin 4}
    (h : probeLossRow h5 k = probeLossRow h5 l) :
    k = l := by
  have hv : (probeLossRow h5 k).val = (probeLossRow h5 l).val := by rw [h]
  simp only [probeLossRow] at hv
  exact Fin.ext hv

/-- **Aux P1.**  A singleton category of the probe carrier has density `1/n`.
General. -/
theorem rowDensity_singleton_fin (x : Fin n) :
    rowDensity ({x} : Finset (Fin n)) = 1 / (n : ℝ) := by
  unfold MassLeavesOwner.rowDensity
  rw [Finset.card_singleton, Fintype.card_fin]
  norm_num

/-- **NON-FIDELITY smoke probe: our encoding of the frozen table is inhabited.**

Four distinct singleton categories and everything else retained.  Every budget is
cleared by the gate `16 < eta_R n`, which is what `probeWidth` supplies.  This is
**not** the paper's instance and must never be recorded as one: the paper's table
is the four-category decomposition at `own(j)` in the refutation of `09:1187--1193`,
and its canonical-inhabitation obligation stays open. -/
def probeLossTable (h5 : 5 ≤ n) (hgate : 16 < etaR * (n : ℝ)) : LossTable (Fin n) etaR := by
  classical
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hden : (1 : ℝ) / (n : ℝ) < etaR / 16 := by
    rw [div_lt_div_iff₀ hn (by norm_num)]
    linarith
  refine
    { retained := (Finset.univ : Finset (Fin n)) \
        ({probeLossRow h5 0} ∪ {probeLossRow h5 1} ∪ {probeLossRow h5 2} ∪ {probeLossRow h5 3})
      deleted := {probeLossRow h5 0}
      routeLoss := {probeLossRow h5 1}
      earlyStopped := {probeLossRow h5 2}
      sentElsewhere := {probeLossRow h5 3}
      cover := ?_
      disjoint₁₂ := ?_
      disjoint₁₃ := ?_
      disjoint₁₄ := ?_
      disjoint₂₃ := ?_
      disjoint₂₄ := ?_
      disjoint₃₄ := ?_
      deleted_le := ?_
      routeLoss_lt := ?_
      earlyStopped_le := ?_ }
  · exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
  all_goals
    first
      | (refine Finset.disjoint_singleton.mpr ?_
         intro h
         exact absurd (probeLossRow_injective h5 h) (by decide))
      | (rw [rowDensity_singleton_fin]
         first
           | linarith
           | (have : etaR / 16 ≤ etaR / 4 := by nlinarith
              linarith))

/-- **The probe is nondegenerate.**  Every one of the four categories carries
strictly positive mass and the retained set is inhabited -- so this is not the
empty table, and the cover, disjointness and budget fields are all checked
against non-zero quantities.  Still **NON-FIDELITY**. -/
theorem probeLossTable_nondegenerate (h5 : 5 ≤ n) (hgate : 16 < etaR * (n : ℝ)) :
    0 < rowDensity (probeLossTable h5 hgate).deleted
      ∧ 0 < rowDensity (probeLossTable h5 hgate).routeLoss
      ∧ 0 < rowDensity (probeLossTable h5 hgate).earlyStopped
      ∧ 0 < rowDensity (probeLossTable h5 hgate).sentElsewhere
      ∧ (probeLossTable h5 hgate).retained.Nonempty := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hpos : ∀ k : Fin 4, 0 < rowDensity ({probeLossRow h5 k} : Finset (Fin n)) := by
    intro k
    rw [rowDensity_singleton_fin]
    positivity
  refine ⟨hpos 0, hpos 1, hpos 2, hpos 3, ⟨⟨4, by omega⟩, ?_⟩⟩
  simp only [probeLossTable, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  intro h
  rcases h with ((h | h) | h) | h <;>
    exact absurd (congrArg Fin.val h) (by simp [probeLossRow])

/-- **The probe at the schedule's own tolerance.**

`eta_R` is a **defined** quantity: `ParameterSchedule.etaR` traces its defining
display, and `ParameterSchedule.etaR_pos` / `etaR_le_bound` are the banked
readouts of that chain.  No numeral is assigned to it here; the probe width is
then the accessor of `probeWidth`, evaluated through the chain.

Still **NON-FIDELITY** on the carrier axis, and the legality it records is that of
`eta_R` alone -- the frozen chain `06:228` is a statement about the schedule, not
about `Fin n`. -/
theorem probe_at_schedule_etaR {s : ℕ} {dv zeta : ℝ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) :
    ∃ T : LossTable (Fin (probeWidth (ParameterSchedule.etaR s dv zeta)))
        (ParameterSchedule.etaR s dv zeta),
      0 < rowDensity T.deleted ∧ 0 < rowDensity T.routeLoss
        ∧ 0 < rowDensity T.earlyStopped ∧ 0 < rowDensity T.sentElsewhere
        ∧ T.retained.Nonempty := by
  have hpos : 0 < ParameterSchedule.etaR s dv zeta := ParameterSchedule.etaR_pos hs hdv hz
  have hle : ParameterSchedule.etaR s dv zeta ≤ 1 :=
    le_trans (ParameterSchedule.etaR_le_bound s dv zeta) (by norm_num)
  have h5 : 5 ≤ probeWidth (ParameterSchedule.etaR s dv zeta) := five_le_probeWidth hpos hle
  exact ⟨probeLossTable h5 (probeWidth_gate hpos),
    probeLossTable_nondegenerate h5 (probeWidth_gate hpos)⟩

end Probe

/-! ## §8  Statement poles

A green build sees none of this.  Each item shows that a hypothesis of a
statement above really bites, or that a conclusion is not delivered by its
trivial witness. -/

section Poles

/-- **Pole 1: the four-category table alone does NOT give
`eq:wrapper-mass-leaves-owner`.**

The frozen conclusion `sum_{T != own(j)} m_{j,T} > eta_R/2` is *not* an
arithmetic consequence of the table's three budgets: the fourth row is
unconstrained, so a table whose fourth category is a single row of a wide carrier
is perfectly legal and its density is far below `eta_R/2`.  Hence the hardness
step of `09:1600--1610` -- `hdense`, `hcols`, the rectangle sections and the final
node's residual budget -- is load-bearing in
`constructionPath_massLeavesOwner`, and that theorem is not a repackaging of
`LossTable.head_rows_lt`. -/
theorem lossTable_alone_does_not_give_massLeavesOwner {n : ℕ} {etaR : ℝ}
    (h5 : 5 ≤ n) (hgate : 16 < etaR * (n : ℝ)) (hetaR : 0 < etaR) :
    ¬ (etaR / 2 < rowDensity (probeLossTable h5 hgate).sentElsewhere) := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hval : rowDensity (probeLossTable h5 hgate).sentElsewhere = 1 / (n : ℝ) :=
    rowDensity_singleton_fin _
  rw [hval]
  have : (1 : ℝ) / (n : ℝ) < etaR / 16 := by
    rw [div_lt_div_iff₀ hn (by norm_num)]; linarith
  intro hcon
  linarith

/-- **Pole 2: the fourth row carries no field, and must not.**

`09:1581` prints "the remaining loss", i.e. no bound.  If the display had been
encoded with a fourth budget in the style of the first three, the *frozen
conclusion* `eta_R/2 < rowDensity D_4` would contradict it: at a positive
tolerance no real can be both at most `eta_R/16` and more than `eta_R/2`.  So the
missing field is fidelity, not an omission. -/
theorem fourth_row_budget_would_be_contradictory {etaR d : ℝ} (hetaR : 0 < etaR)
    (hbudget : d ≤ etaR / 16) : ¬ (etaR / 2 < d) := by
  intro hcon
  linarith

/-- **Pole 3: `09:1569`'s "disjoint" is load-bearing in `LossTable`.**

Not a repackaging of `Finset.card_sdiff_add_card_eq_card`: dropping disjointness
lets the four categories over-count.  Here `Rw = Fin 2`, `retained` is empty and
`D_1 = D_2 = univ`, so the cover equation still holds while the five counts miss
the carrier's size -- the banked
`MassLeavesOwner.categories_need_disjointness` is the witness and is consumed by
pin. -/
theorem lossTable_cover_alone_is_not_the_partition :
    ((Finset.univ : Finset (Fin 2)) \ (∅ : Finset (Fin 2))
        = (Finset.univ : Finset (Fin 2)) ∪ (Finset.univ : Finset (Fin 2))
            ∪ (∅ : Finset (Fin 2)) ∪ (∅ : Finset (Fin 2)))
      ∧ (∅ : Finset (Fin 2)).card
          + ((Finset.univ : Finset (Fin 2)).card + (Finset.univ : Finset (Fin 2)).card
              + (∅ : Finset (Fin 2)).card + (∅ : Finset (Fin 2)).card)
        ≠ Fintype.card (Fin 2) :=
  MassLeavesOwner.categories_need_disjointness

/-- **Pole 4: the construction path is not the identity on the frame.**

`09:1195--1200` has content: `Protocol.leaf z` fails the completion frame
condition at width `1`, and its completion satisfies it.  So the discharge of
`hcomp` performed throughout Sections 2--6 is a real step and not a change of
notation.  Consumed by pin from the banked
`RoutedCertificateConstruction.leafProtocol_not_completed`. -/
theorem construction_path_discharges_a_real_binder (z : Bool) :
    ¬ CompletedNoBob (Protocol.leaf z : Protocol Bool Bool Bool) 1
      ∧ CompletedNoBob (completeNoBob 1 (Protocol.leaf z : Protocol Bool Bool Bool)) 1 :=
  leafProtocol_not_completed z

/-- **Pole 5: `09:1207--1212`'s `C >= 1` is load-bearing on this path.**

Every theorem of Sections 3--4 transports the *original* protocol's cost bound to
the completion through `completeNoBob_cost_le_frame`, whose frozen justification
is "because `C >= 1`".  At `C = 0` the transport fails outright: the banked
`RoutedCertificateConstruction.completeNoBob_cost_needs_C_ge_one` is the witness,
and it is why `3 <= C` -- not merely a cost hypothesis -- is carried in
`constructionPath_ownerUniqueness` and `constructionPath_massLeavesOwner`.
**Claims no legality: `C = 0` is outside the frozen range `09:1302`'s `C >= 3`.** -/
theorem cost_transport_needs_C_ge_one :
    (Protocol.leaf true : Protocol Bool Bool Bool).cost ≤ 0 + 1 - 1
      ∧ ¬ (completeNoBob 1 (Protocol.leaf true : Protocol Bool Bool Bool)).cost ≤ 0 + 1 - 1 :=
  completeNoBob_cost_needs_C_ge_one

/-- **Pole 6: the two NEW binders of this tranche are jointly satisfiable.**

Sections 3--4 replace the banked modules' `hcomp : CompletedNoBob P r` by the pair
that `09:1188--1193` actually supplies -- the original protocol's cost bound and
its computation of the retained matrix.  This exhibits a protocol meeting **both**
at the frozen `C >= 3`, together with the fact that it is *not* already completed:
so the pair is consistent, and the completion step of Sections 3--4 is not
vacuously available.

**Claims no legality:** the carriers and the game are the probe's own, and the
retained matrix `U'` of `09:1188` is not exhibited.  This is a consistency check
on the two replaced binders, not an instance of the frozen frame. -/
theorem constructionPath_binders_are_jointly_satisfiable :
    (Protocol.leaf true : Protocol Bool Bool Bool).cost ≤ 3 + 1 - 1
      ∧ Protocol.Computes (Protocol.leaf true : Protocol Bool Bool Bool)
          (fun _ _ : Bool => true)
      ∧ ¬ CompletedNoBob (Protocol.leaf true : Protocol Bool Bool Bool) 1 :=
  ⟨by simp [Protocol.cost], fun _ _ => rfl, (leafProtocol_not_completed true).1⟩

end Poles

end EthInapproximability.ParameterizedNP.MassRedistributionOwners
