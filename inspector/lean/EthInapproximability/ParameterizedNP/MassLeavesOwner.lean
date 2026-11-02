import EthInapproximability.ParameterizedNP.MassRedistributionCounting
import EthInapproximability.ParameterizedNP.TerminalResidualComparison

/-!
# Parameterized NP route: the fourth loss-table line and `eq:wrapper-mass-leaves-owner`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche), **lines `09:1566--1615`**: the frozen
  four-category loss table and the display `eq:wrapper-mass-leaves-owner`.
  Every anchor below was opened first-hand in that file for this tranche.

  The anchors traced here, in the order the frozen block prints them:

  * `09:1566--1568`, the frozen `m_{j,T}` and `own(i)` conventions: "For a donor
    `j` and final node `T`, let `m_{j,T}` be the protected mass from `j` reaching
    `T`, normalized by `m`.  Write `own(i)` for the owner of `i in J_good`";
  * `09:1569--1570`, **the sentence this module formalizes as a partition**: "The
    rows of a good donor missing from its owner fall into four disjoint
    categories";
  * `09:1571--1584`, the table itself, whose four rows are `09:1574--1575`
    (initially deleted rows, at most `eta_R m/16`), `09:1576--1577` (base rows
    lost along the unique clean route, less than `eta_R m/16`), `09:1578--1579`
    (protected rows stopped at first-Bob nodes, at most `eta_R m/4`) and
    `09:1580--1581` (protected rows sent to other final nodes, "the remaining
    loss");
  * `09:1600--1607`, the retention arithmetic: "If the last line were at most
    `eta_R m/2`, then the owner would retain more than
    `1 - (1/16 + 1/16 + 1/4 + 1/2) eta_R = 1 - 7 eta_R/8 > 1 - eta_R` of all rows
    of its copy of `N`" -- the display closes at `09:1606` and the sentence's
    final clause "of all rows of its copy of `N`." is the first half of
    `09:1607`, which is why the range ends at `1607` and the column reading
    below starts mid-line at the same `1607` (record repair **R1**);
  * `09:1607--1608`, the column reading: "Its coordinate lies outside the
    singleton cover, so its outer column projection has density at least
    `1 - eta_C`";
  * `09:1609--1610`, **the hardness step**: "The deletion-stable Stage-4 theorem
    would make the owner `C`-hard, impossible under the alleged shallow
    protocol";
  * `eq:wrapper-mass-leaves-owner` (label `09:1614`, display `09:1611--1615`):
    `sum_{T != own(j)} m_{j,T} > eta_R/2` for `j in J_good`.

* **Cross-anchors opened first-hand for this tranche:**
  * `thm:dense-stage4` (statement `08:298--319`), whose frozen conclusion
    `comp<N, 1, 1 - eta_R, 1 - eta_C> >= C` is the "deletion-stable Stage-4
    theorem" of `09:1609`; it is banked as
    `DenseStageFourOpening.DenseStageFourConclusion` / `denseStageFour` and is
    consumed here **by pin**, never re-derived;
  * `08:154--156`, the orientation rule that reads `eta_R` on rows of `N`
    (= columns of `A`) and `eta_C` on its columns -- which is why the retention
    of `09:1600--1607` feeds the *row* clause of the bracket family and the
    projection of `09:1608` feeds the *column* clause;
  * `09:407` (`rho_* = max{rho_sing, 1 - eta_C}`) and `06:697--701` (the
    materialized evaluation `rho_* = 1 - eta_C`, with its derivation
    `06:702--709`), which is the **defining display** of the `1 - eta_C` that
    `09:1608` writes; the banked `WrapperProjectionCovers.rhoStar` and
    `rhoStar_eq_one_sub_etaC` carry it, and `ownerRect_mem_bracketGE_at_rhoStar`
    below enters the frozen threshold through that chain rather than through a
    numeral;
  * `09:448--451`, `E_0` as the union of all singleton, pair and small-copy
    covers with `e_0 = |E_0|`, and `09:683--686`, the frozen consequence of a
    coordinate lying outside the singleton projection cover -- the two anchors
    that make `09:1607--1608` a *cover-avoidance* reading;
  * `09:1250--1252`, the two frozen stopping rules, and `09:1341--1343`, "the
    suffix below a node reached after `r` Alice bits in the alleged
    `(C+r-1)`-bit protocol has depth at most `C-1`", which is the "impossible
    under the alleged shallow protocol" of `09:1610`; both are banked
    (`RoutedCertificateSystem.RoutedSystem.final_residual_budget`,
    `DenseWrapperFrontier.finalNode_budget_contradiction`);
  * `09:1339--1340`, **the frozen floor `C >= 3` itself** -- "The hypotheses are
    supplied by `lem:wrapper-reference`, `C >= 3`, and `2 x_T <= t_ref x_T <= 1`"
    -- which is a *different* anchor from `09:1341--1343`: the latter is the
    suffix-depth sentence, and carries no `C >= 3`.  The floor itself is on
    `09:1339`, which ends at "`C >= 3`, and"; the trailing clause
    `2 x_T <= t_ref x_T <= 1` runs onto `09:1340`, so the *quotation* spans
    `09:1339--1340` while the *floor* is cited as `09:1339` (record repair
    **R2**, range corrected by verify-seat record finding **F3**);
  * `09:1330--1331`, "no Bob query has occurred on the route to this node",
    which is why the *column* half of the owner rectangle needs **no**
    hypothesis here: it is discharged from the frontier's own stopping rule.

## What this module is, and what it deliberately is not

`WrapperMassRedistribution` banked this block's **arithmetic** over abstract
reals -- `fourCategory_coefficients` (the frozen coefficient sum and the strict
margin) and `wrapperMassLeavesOwner` (the frozen contrapositive with the
hardness step carried as an implication).  Both are consumed here **by pin** and
neither is restated.

`MassRedistributionCounting` banked the **counting head** of the same segment
(`09:1512--1598`) at the routed certificate system, and left the fourth table
line as its GAP-EXPOSED item 1 with an explicit prescription: *supply the engine
retention `1 - (L1+L2+L3+L4) <= retained` at the owner rectangle of the routed
system and feed `wrapperMassLeavesOwner` with the banked deletion-stable
endpoint.*  This module executes exactly that prescription, and it is the first
step of the mass-redistribution segment whose justification runs through
**hardness** rather than counting.

What is added, in four layers:

* **The partition (`09:1569--1570`).**  "Four disjoint categories" is a
  statement about a finite row set, not a bookkeeping convention, so
  `card_retained_add_card_categories` **proves** the retention count from
  disjointness and coverage, and `rowDensity_retained_eq` turns it into the
  normalized identity `retained = 1 - (L1+L2+L3+L4)`.  The banked
  `wrapperMassLeavesOwner` takes that as an inequality binder; here it is an
  equality, derived.
* **The bracket membership (`09:1600--1608`).**  The two frozen density
  readings -- more than `1 - eta_R` of the rows of the owner's copy of `N`, and
  outer column projection density at least `1 - eta_C` -- are exactly the two
  clauses of `NPCC.bracketGE Rw Cl 1 (1-eta_R) (1-eta_C)` at the one-fold
  interlace, so `ownerRect_mem_bracketGE` **proves** that the owner rectangle is
  a member of the family `thm:dense-stage4` lower-bounds.
* **The hardness readout (`09:1609`).**  `ownerHard_of_denseStageFour` composes
  the banked `DenseStageFourConclusion` with the vendored
  `EthBridge.Dfamily_le_member`: a family bound plus a membership is a bound on
  that member.  Nothing of `08:330--1346` is re-derived; the frozen theorem
  enters as the named endpoint it is.
* **The impossibility (`09:1610`) and the deliverable.**  `ownerRetention_le`
  runs the frozen contradiction at a **final Alice node of the routed system of
  the alleged protocol**: the owner's residual complexity is at least `C` by the
  three layers above, at most the suffix depth by the banked residual comparison
  `TerminalResidualComparison.D_le_cost_descend_of_computes`, and the suffix
  depth is at most `C-1` by the banked `final_residual_budget`.  Its conclusion
  is precisely the `hHard` binder of `wrapperMassLeavesOwner`, so
  `massLeavesOwner_engine` and `massLeavesOwner_of_fourCategories` close
  `eq:wrapper-mass-leaves-owner` at the engine.

**One frozen hypothesis is discharged rather than assumed.**  The column half of
the residual comparison (`hcol`) is *not* a binder of `ownerRetention_le`: every
frontier address is an Alice-only route (`09:1250--1252`), so
`TerminalResidualComparison.routeCols_of_isAlicePath` applied to
`RoutedSystem.node_isAlicePath` supplies it.  That is `09:1330--1331` ("no Bob
query has occurred on the route to this node") turned into a proof.

**M3 (reservoirs).**  The frozen reservoir sentence is `09:1370--1373`, "Each
outer coordinate contains two protected row reservoirs, each of mass
`mu_P = 1/184`" -- the prose opens on `09:1370`, the display `mu_P = 1/184`
occupies `09:1371--1373` (`\[` / `\mu_P=\frac1{184}` / `\]`), and the sentence's
final clause "relative to the `m` rows of one copy of `N`." is the first half of
`09:1374`.  (`09:1367--1368` is the subsection heading
`sec:wrapper-protected-early` and its label, not the sentence; record repair
**R4**, whose exclusion of the heading is right but whose range stopped one
display short -- corrected by verify-seat record finding **F2**.)  Those two
reservoirs are re-modelled nowhere here.  The third table line enters only as
the real number `L3` at its frozen budget, exactly as the banked
`MassRedistributionCounting.goodDonor_firstBobMass_le` produces it.

**M4 (fixed member, fixed protocol).**  Every statement below is about one fixed
`RoutedSystem` on one fixed `Protocol` and one fixed matrix `N`; no protocol
family is quantified over, and no member of the bracket family is selected --
the member is *constructed* as `ownerRect`.

**`hDenseRung` is neither discharged nor fed by this module.**  `DenseRung` (the
`eq:wrapper-u-dense` endpoint) falls only at the genuine end of the
mass-redistribution segment; nothing below mentions it, `eq:wrapper-u-dense` is
concluded nowhere, and **no route completion is claimed**.  Steps 5--9 of the
segment (`09:1617--1781`) are untouched.

## Repair round `r1` (tranche `cc-t4r-r1`)

The `cc-t4r` statement gate returned REVISE at 39/40 declarations CLEAR.  This
generation restores those 39 declarations byte-for-byte from the parked bytes
(SHA-256 `32FB5C590EAEF92B0075FBB277ED4424615DD3F28D08B6B0C5A87525803A71AB`) and
applies exactly the prescribed repairs -- nothing else:

* **Blocking (judge decl 25), a statement change.**  The third conjunct of
  `impossibility_needs_C_ge_three` was written `(0 + 1 <= 0 + 1 - 1 + 1)`, which
  parses as `1 <= 1` and is trivially true; it was **not** a clause of the banked
  `DenseWrapperFrontier.finalNode_budget_contradiction`, and at the values the
  docstring advertised (`B = 0`, `r = 1`) that lemma's real `hbudget` reads
  `1 <= 0` and is false, while its companion `hlower : C <= B` was not exhibited
  at all.  The conjunct is replaced by the genuine two-clause witness at
  `C = 0`, `B = 0`, `r = 0`, and the docstring's advertised values are corrected
  with the `r >= 1` and `C in {1,2}` exclusions stated.  See §5.
* **Records R1--R6, all comment-side except R6.**  R1: the retention range is
  `09:1600--1607`, not `1600--1606`.  R2: the frozen floor `C >= 3` lives at
  `09:1339`, not `09:1341--1343` (which is the suffix-depth sentence).  R3: §7's
  "cannot be fired" prose is withdrawn and restated accurately.  R4: the
  reservoir sentence is `09:1370--1371`, not `09:1367--1371`.  R5: §7's coverage
  residue (`iotaA`, `iotaB`, `hrow`, `hgame`, and also `hcomp`, `hRw`, `hcols`,
  `hdense`) is named with an explicit no-leaning caution, here and at the
  lemma.  R6: the style-linter `show` at the fibre readout becomes `change`.

R6 touches one tactic token inside `ownerRect_fiber_card`, whose **statement** is
unchanged; no other CLEAR declaration's statement or proof term is altered.

### Verify-seat record repairs (F1--F5), applied after the CLEAR verdict

The `cc-t4r-r1` statement gate returned **CLEAR at 40/40** with five *record*
findings -- citations and prose only, no statement, hypothesis, conclusion or
proof term.  The verify seat re-derived each one first-hand against the frozen
source before applying it, and applied exactly these:

* **F1** -- GAP-EXPOSED item 2 cited `09:1188--1213` for "the outer-copy
  indexing".  That range is the `eq:wrapper-u-dense` contradiction opening plus
  `lem:wrapper-no-bob-completion`, and contains no outer-copy indexing; the
  structure `U = interlace(N, q)` is `09:105--108`.  Repointed, with the
  protocol-carrier setup cited separately.
* **F2** -- §M3's reservoir range `09:1370--1371` stopped one display short of
  the `mu_P = 1/184` it quotes (the display is `09:1371--1373`).  Corrected to
  `09:1370--1373`; R4's exclusion of the heading `09:1367--1368` stands.
* **F3** -- the cross-anchor bullet quoted through `2 x_T <= t_ref x_T <= 1`
  while citing `09:1339` alone; that clause is on `09:1340`.  The quotation now
  cites `09:1339--1340`, the floor itself still `09:1339`.
* **F4** -- `eta_R <= 1/36800` was attributed to `06:228`'s chain, which alone
  gives only `eta_R < tau = 1/92`.  Re-attributed to `eq:eta-choice`'s first
  `eta_R` term, `mu_Sigma/200`.  The value was always correct.
* **F5** -- Pole 5's title read as a tightness claim for the frozen `3`.  In the
  banked `Nat`-valued lemma `1 <= C` already suffices, so the title is restated
  and the docstring now says what the pole does and does not establish.

**No statement, hypothesis, conclusion or proof term was touched by F1--F5**;
the 40 declarations are byte-identical in their code to the judged generation.

## GAP-EXPOSED, with the next-round prescription

1. **The four categories are not *constructed* from the routing.**  `09:1569`
   asserts that the missing rows *fall into* the four categories; this module
   takes the four Finsets, their disjointness and their coverage as explicit
   binders and proves what follows from them.  Producing `D1` from the initial
   deletion, `D2` from the clean route, `D3` from the first-Bob stop and `D4`
   from the transfers needs the protected-reservoir routing, which is the same
   object `MassRedistributionCounting` registers as its GAP item 3 (`P_v`).
   *Next round:* build the four categories from the routing and replace
   `hcover`/the six disjointness binders by theorems.
2. **The owner's copy of `N` is not identified inside the ambient carrier.**
   The sections `iotaA`, `iotaB` and the game identification `hgame` are the
   "read the owner's copy of `N` into the wrapper's carriers" of `09:1600--1607`,
   and they are explicit binders here.  The frozen construction fixes them
   through the outer-copy structure `U = interlace(N, q)` with `q = 2^r` the
   scale-alignment width, set up at **`09:105--108`** ("Let `q = 2^r` be the
   scale-alignment width and set", with the display `U = interlace(N, q)` at
   `09:107`; the pipeline figure node is `09:36`); that
   structure is not formalized here.  The ambient carrier of the *alleged
   protocol* is a separate setup at `09:1188--1193` (the `eq:wrapper-u-dense`
   contradiction opening, followed by `lem:wrapper-no-bob-completion` at
   `09:1195--1213`), which carries no outer-copy indexing.  (Verify-seat record
   finding **F1**: the parked and judged generations cited `09:1188--1213` for
   the indexing; a whole-file search for "outer copy"/"outer copies" in
   `09-first-wrapper.tex` returns nothing, and the outer-copy structure is
   `09:107`.)  *Next round:* derive the sections from the wrapper's outer-copy
   structure once it lands.
3. **`hcols`, the outer projection density, is a binder.**  `09:1607--1608`
   derives it from the owner coordinate lying outside the singleton cover
   (`09:448--451`, `09:683--686`), i.e. from the cover apparatus of
   `sec:wrapper-projection-covers`.  The *threshold* is not free -- it is the
   banked `rhoStar` evaluated by `06:697--701`, and
   `ownerRect_mem_bracketGE_at_rhoStar` enters it through that definitional
   chain -- but the *fact* that the owner attains it is not derived.
   *Next round:* discharge `hcols` from the banked
   `WrapperProjectionCovers.singleton_bin_retention` at the owner coordinate.
4. **`hdense`, the deletion-stable endpoint, is the banked statement and not a
   banked proof.**  `DenseStageFourOpening.denseStageFour` reduces the family
   bound to the per-member contradiction and names the whole of `08:330--1346`
   as its hypothesis `hnoProtocol`.  Consuming its *conclusion* here therefore
   inherits that status exactly; nothing in this module makes the Stage-4 lower
   bound any more proved than it already was.

## Unexercised joints

* `ownerRetention_le` is **not** fired at a live instance.  The precise claim,
  stated without overreach (record repair **R3**): firing it at the frozen floor
  `3 <= C` (`09:1339`) requires supplying `hdense`, i.e. exhibiting the Stage-4
  family lower bound at a concrete matrix and a concrete `C >= 3`, which is item
  4 above and is unbuilt in this repository.  It is *not* the case that `hdense`
  is unsatisfiable or that any firing would amount to a proof of
  `thm:dense-stage4` in general: §5's
  `denseBinder_is_realizable_but_below_the_frozen_floor` discharges `hdense` at
  `C = 1` on the banked two-element witness, which is below the floor and so
  cannot feed `ownerRetention_le`.  The gap is a **construction** gap at legal
  parameters, not an inconsistency.
* **R5, the coverage residue of §7, named and not leaned on.**  §7 exhibits
  exactly three items -- `hv`, `hcost`, and the column half `hcol` (which is a
  theorem here, not a binder).  It exhibits **none** of `iotaA`, `iotaB`, `hrow`,
  `hgame`, and none of `hcomp`, `hRw`, `hcols`, `hdense`.  So §7 must **not** be
  read as evidence that the rest of `ownerRetention_le`'s bundle is satisfiable
  at the live system: `iotaA`/`iotaB`/`hrow`/`hgame` are precisely the
  owner's-copy identification of GAP-EXPOSED item 2, and whether they can be
  supplied at any concrete system is exactly what is unformalized.  §7 is a
  three-binder smoke check and carries no weight beyond those three.
* The four-category partition and the bracket membership *are* fired, at a
  nondegenerate point where all four categories are inhabited.

## Reader counterpart

**This module claims no reader item, deliberately rather than by omission.**
`routes/parameterized-np/reader-facing/sections/` was swept first-hand for this
tranche (`owner`, `retain`, `deletion-stable`, `donor`, `singleton`,
`protected mass`, `near-full`).

* `A-stage4-details.tex:384--386` -- "The deletion-stable theorem
  `eq:paper-protected-dense` rules out the complementary near-full single-owner
  obstruction" -- is the reader's *exact* sentence for `09:1609--1610`, and it is
  **unnumbered proof prose** inside the proof of
  `thm:paper-adapted-stage4-interface`.  The reader-counterpart rule bars citing
  prose as a statement, so it is **declined** and recorded here instead.
* The display it points at, `eq:paper-protected-dense`
  (`A-stage4-details.tex:222`), is the reader counterpart of `thm:dense-stage4`
  itself and is **already assigned** to `DenseStageFourOpening` through the
  crosswalk row "Protected Stage 4 | Appendix A".  A reader item may not be
  assigned twice.
* `A-stage4-details.tex:373--377` and `396--399` are the reader's only other
  accounts of the owner--donor count; both are unnumbered proof prose and both
  are already recorded as unclaimed by `WrapperProjectionCovers` and
  `MassRedistributionCounting`.  The one display in range,
  `A-stage4-details.tex:393--395`, is `eq:wrapper-u-dense`, which this module
  does **not** close and therefore must not claim -- and it carries no `\label`.

The precedent for claiming none is `MassRedistributionCounting`,
`WrapperMassRedistribution`, `TerminalResidualComparison`,
`DenseRoutingInvariant` and `DenseWrapperFrontier`.  `READER_CROSSWALK.md` is
therefore not modified by this tranche.

## Axiom surface

No new `axiom`, no proof-suppression token, no opaque certificate.  Every
external contact is an explicit binder: the deletion-stable endpoint `hdense`,
the outer projection density `hcols`, the four categories with their coverage
and disjointness, and the owner-rectangle sections.  `EXPANDER-001` occurs in no
hypothesis of this module and has no Lean declaration by design.
`LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
axiom -- is **not** in the import closure: the two imports are
`MassRedistributionCounting` and `TerminalResidualComparison`, whose ledger rows
record the same exclusion.  The only vendored declarations consumed are
`NPCC.bracketGE`, `NPCC.subgame`, `NPCC.Dfamily`, `NPCC.IsEquipartitionedGE`,
`Workspace.Types.Interlace.interlaceFun`, `Workspace.Types.CommComplexity.D` and
`EthBridge.Dfamily_le_member`.

## Non-vacuity and canonical inhabitation

**CANONICAL INHABITATION -- REGISTERED and DEFERRED.**  The paper's own instance
of this block is the owner rectangle of a good donor in the routed certificate
system of the *alleged shallow protocol*, at the matrix `N` of the frozen
construction.  Neither the alleged protocol's routing nor the protected-reservoir
mass `P_v` is formalized (GAP items 1--2 above), and `hdense` is the Stage-4
lower bound itself (item 4), so **no paper instance exists to exhibit** and the
obligation is discharged only when the wrapper's transcript-level construction
lands -- never by a probe.

§7's probes are therefore labelled **NON-FIDELITY** in situ.  They are
nevertheless **nondegenerate**: the four-category partition is fired at a point
where all four categories are inhabited and the retained set is a proper
nonempty subset, and the bracket membership is fired with its row clause tight
(equality), so no clause below is satisfied by an empty or slack case.  The
tolerances used there are **ours** and are labelled **BEYOND-PAPER AUDIT**;
`eta_R` is DEFINED by `eq:eta-choice` (`06:206--217`), whose first `eta_R` term
`(1/2) * mu_Sigma/100 = mu_Sigma/200` with the frozen `mu_Sigma = 1/184` of
`eq:fixed-protected-masses` (`06:133`) forces `eta_R <= 1/36800`, at which no
decidable carrier is available.  (The chain `0 < eta_R <= eta_C/2 < tau < x_N`
of `06:228` alone yields only `eta_R < tau = 1/92`; the `1/36800` comes from
`eq:eta-choice` -- verify-seat record finding **F4**.)
-/

namespace EthInapproximability.ParameterizedNP.MassLeavesOwner

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.TerminalResidualComparison

/-! ## §1  The four disjoint categories (`09:1569--1584`)

"The rows of a good donor missing from its owner fall into four disjoint
categories."  At the engine this is a partition of the finite row set of the
owner's copy of `N`, and the retention of `09:1600--1601` is its arithmetic
consequence rather than a separate assumption. -/

section Categories

variable {Rw : Type*} [Fintype Rw]

/-- **`09:1567` and `09:1540`, the frozen normalization.**  "normalized by `m`":
a row set of the owner's copy of `N`, read as a fraction of *all* rows of that
copy.  `m = |Rows(N)| = Fintype.card Rw`.  General. -/
noncomputable def rowDensity (D : Finset Rw) : ℝ :=
  (D.card : ℝ) / (Fintype.card Rw : ℝ)

/-- **Aux 1 (identity).**  The empty category contributes no loss.  General. -/
@[simp] theorem rowDensity_empty : rowDensity (∅ : Finset Rw) = 0 := by
  simp [rowDensity]

/-- **Aux 2 (identity).**  Retaining every row is retention `1` -- the frozen
"of all rows of its copy of `N`" read at the full set.  General. -/
theorem rowDensity_univ (h : 0 < Fintype.card Rw) :
    rowDensity (Finset.univ : Finset Rw) = 1 := by
  have hc : (0 : ℝ) < (Fintype.card Rw : ℝ) := by exact_mod_cast h
  unfold rowDensity
  rw [Finset.card_univ]
  exact div_self hc.ne'

/-- **Aux 3.**  A density is nonnegative.  General. -/
theorem rowDensity_nonneg (D : Finset Rw) : 0 ≤ rowDensity D := by
  unfold rowDensity
  positivity

/-- **Aux 4 (monotonicity).**  A larger category is a larger loss.  General. -/
theorem rowDensity_mono {D D' : Finset Rw} (h : D ⊆ D') :
    rowDensity D ≤ rowDensity D' := by
  have hcard : (D.card : ℝ) ≤ (D'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h
  have hc : (0 : ℝ) ≤ (Fintype.card Rw : ℝ) := Nat.cast_nonneg _
  unfold rowDensity
  gcongr

/-- **Aux 5 (the round trip between the density and the count).**  The frozen
retention comparison `1 - eta_R < retained` and the bracket family's row clause
`|Rows(N)| (1 - eta_R) <= |retained|` are the same statement, up to strictness.
This is the identity `ownerRetention_le` turns on.  General. -/
theorem lt_rowDensity_iff {D : Finset Rw} (h : 0 < Fintype.card Rw) (t : ℝ) :
    t < rowDensity D ↔ (Fintype.card Rw : ℝ) * t < (D.card : ℝ) := by
  have hc : (0 : ℝ) < (Fintype.card Rw : ℝ) := by exact_mod_cast h
  unfold rowDensity
  rw [lt_div_iff₀ hc]
  constructor
  · intro hlt; nlinarith
  · intro hlt; nlinarith

section Partition

variable [DecidableEq Rw]

/-- **`09:1569--1570`, the four disjoint categories, as a count.**

"The rows of a good donor missing from its owner fall into four disjoint
categories."  Coverage (`hcover`) says the missing rows are exactly the union;
the six `Disjoint` binders say "disjoint".  The conclusion is the frozen
bookkeeping of `09:1600--1601`: the retained rows plus the four losses are all
rows of the copy.  Stated additively, so no natural-number truncation occurs.
General in the row carrier and in all five sets. -/
theorem card_retained_add_card_categories {retained D₁ D₂ D₃ D₄ : Finset Rw}
    (hcover : (Finset.univ : Finset Rw) \ retained = D₁ ∪ D₂ ∪ D₃ ∪ D₄)
    (h₁₂ : Disjoint D₁ D₂) (h₁₃ : Disjoint D₁ D₃) (h₁₄ : Disjoint D₁ D₄)
    (h₂₃ : Disjoint D₂ D₃) (h₂₄ : Disjoint D₂ D₄) (h₃₄ : Disjoint D₃ D₄) :
    retained.card + (D₁.card + D₂.card + D₃.card + D₄.card) = Fintype.card Rw := by
  have hbase := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ retained)
  rw [hcover, Finset.card_univ] at hbase
  have hd₃ : Disjoint (D₁ ∪ D₂) D₃ := Finset.disjoint_union_left.mpr ⟨h₁₃, h₂₃⟩
  have hd₄ : Disjoint (D₁ ∪ D₂ ∪ D₃) D₄ :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h₁₄, h₂₄⟩, h₃₄⟩
  rw [Finset.card_union_of_disjoint hd₄, Finset.card_union_of_disjoint hd₃,
    Finset.card_union_of_disjoint h₁₂] at hbase
  omega

/-- **`09:1600--1601`, the retention, PROVED.**

"the owner would retain more than `1 - (...) eta_R` of all rows of its copy of
`N`": at the engine the retained fraction *equals* one minus the four
normalized losses.  The banked `WrapperMassRedistribution.wrapperMassLeavesOwner`
consumes this as the inequality binder `hret`; here it is an identity, derived
from the frozen partition.  General. -/
theorem rowDensity_retained_eq (h : 0 < Fintype.card Rw)
    {retained D₁ D₂ D₃ D₄ : Finset Rw}
    (hcover : (Finset.univ : Finset Rw) \ retained = D₁ ∪ D₂ ∪ D₃ ∪ D₄)
    (h₁₂ : Disjoint D₁ D₂) (h₁₃ : Disjoint D₁ D₃) (h₁₄ : Disjoint D₁ D₄)
    (h₂₃ : Disjoint D₂ D₃) (h₂₄ : Disjoint D₂ D₄) (h₃₄ : Disjoint D₃ D₄) :
    rowDensity retained
      = 1 - (rowDensity D₁ + rowDensity D₂ + rowDensity D₃ + rowDensity D₄) := by
  have hc : (0 : ℝ) < (Fintype.card Rw : ℝ) := by exact_mod_cast h
  have hcard := card_retained_add_card_categories hcover h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  have hR : (retained.card : ℝ)
      + ((D₁.card : ℝ) + (D₂.card : ℝ) + (D₃.card : ℝ) + (D₄.card : ℝ))
      = (Fintype.card Rw : ℝ) := by exact_mod_cast hcard
  unfold rowDensity
  field_simp
  linarith

end Partition

end Categories

/-! ## §2  The owner rectangle as a member of the bracket family
(`09:1600--1608`)

The frozen sentence reads two densities at the owner and then invokes
`thm:dense-stage4`.  Its conclusion (`08:317`) is a bound on
`comp<N, 1, 1 - eta_R, 1 - eta_C>`, i.e. on the **minimum** over the members of
`bracketGE Rw Cl 1 (1-eta_R) (1-eta_C)`.  So the two frozen densities are not
decoration: they are exactly the two clauses that put the owner rectangle *in*
that family, which is what turns a family lower bound into a bound on the
owner. -/

section Bracket

section Rect

variable {Rw Cl : Type*}

/-- **`09:1600--1608`, the owner rectangle.**

The extraction data of the member of `bracketGE Rw Cl 1 (...)` that the frozen
sentence points at: the retained rows of the owner's copy of `N`, taken in the
one-fold interlace (whose rows are `Fin 1 x Rw`, `conv:finite-slots`), together
with the outer column projection (whose ambient carrier is `Fin 1 -> Cl`).

Nothing about complexity or robustness is part of this datum (M4): it is a pair
of finite sets. -/
def ownerRect (retained : Finset Rw) (cols : Finset (Fin 1 → Cl)) :
    Finset (Fin 1 × Rw) × Finset (Fin 1 → Cl) :=
  ((Finset.univ : Finset (Fin 1)) ×ˢ retained, cols)

@[simp] theorem ownerRect_fst (retained : Finset Rw) (cols : Finset (Fin 1 → Cl)) :
    (ownerRect retained cols).1 = (Finset.univ : Finset (Fin 1)) ×ˢ retained := rfl

@[simp] theorem ownerRect_snd (retained : Finset Rw) (cols : Finset (Fin 1 → Cl)) :
    (ownerRect retained cols).2 = cols := rfl

/-- **Aux 6 (round trip: the fibre readout).**  At `p = 1` the interlace has one
slot, so the fibre of the owner rectangle over that slot is the retained row set
itself.  This is what makes the bracket family's `IsEquipartitionedGE` clause a
statement about `|retained|` and not about a genuinely partitioned row set.
General. -/
theorem ownerRect_fiber_card (retained : Finset Rw) (cols : Finset (Fin 1 → Cl))
    (i : Fin 1) :
    (((ownerRect retained cols).1).filter (fun p => p.1 = i)).card = retained.card := by
  have hfilter : ((Finset.univ : Finset (Fin 1)) ×ˢ retained).filter (fun p => p.1 = i)
      = (Finset.univ : Finset (Fin 1)) ×ˢ retained := by
    refine Finset.filter_true_of_mem ?_
    intro p _
    rw [Fin.fin_one_eq_zero p.1, Fin.fin_one_eq_zero i]
  change (((Finset.univ : Finset (Fin 1)) ×ˢ retained).filter (fun p => p.1 = i)).card
      = retained.card
  rw [hfilter, Finset.card_product, Finset.card_univ, Fintype.card_fin, one_mul]

end Rect

variable {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]

/-- **`09:1600--1608`, membership in the deletion-stable bracket family, PROVED.**

`hrows` is `09:1600--1607` ("the owner would retain more than `1 - eta_R` of all
rows of its copy of `N`", here in its non-strict count form) and `hcols` is
`09:1607--1608` ("its outer column projection has density at least `1 - eta_C`").
The two ceilings are the frozen `def:bracket`'s own, taken from the vendored
`NPCC.bracketGE` by pin; neither is re-rounded here.  General. -/
theorem ownerRect_mem_bracketGE {ηR ηC : ℝ} {retained : Finset Rw}
    {cols : Finset (Fin 1 → Cl)}
    (hrows : (Fintype.card Rw : ℝ) * (1 - ηR) ≤ (retained.card : ℝ))
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ)) :
    ownerRect retained cols ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC) := by
  refine ⟨?_, ?_⟩
  · intro i _
    rw [ownerRect_fiber_card retained cols i]
    exact Nat.ceil_le.mpr hrows
  · exact Nat.ceil_le.mpr hcols

/-- **Aux 7 (monotonicity of the membership).**  Both bracket clauses are
`>=`-thresholds, so enlarging either side of the owner rectangle preserves
membership.  This is the sanity property the frozen "retains **more than**
`1 - eta_R`" and "density **at least** `1 - eta_C`" readings demand: the family
is upward closed in the rectangle, and the frozen sentence never has to exhibit
the exact retained set.  General. -/
theorem ownerRect_mem_bracketGE_mono {ηR ηC : ℝ} {retained retained' : Finset Rw}
    {cols cols' : Finset (Fin 1 → Cl)} (hr : retained ⊆ retained') (hc : cols ⊆ cols')
    (h : ownerRect retained cols ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC)) :
    ownerRect retained' cols' ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC) := by
  refine ⟨?_, ?_⟩
  · intro i _
    have hi := h.1 i (Finset.mem_univ i)
    rw [ownerRect_fiber_card retained cols i] at hi
    rw [ownerRect_fiber_card retained' cols' i]
    exact le_trans hi (Finset.card_le_card hr)
  · exact le_trans h.2 (Finset.card_le_card hc)

/-- **`09:1608` entered through its defining display, not through a numeral.**

The `1 - eta_C` of `09:1608` is the singleton cover's contraction factor: `09:407`
defines `rho_* = max{rho_sing, 1 - eta_C}` and `06:697--701` evaluates it to
`1 - eta_C` once the physical Stage-4 matrix is materialized.  This is the
membership lemma stated at the *defined* quantity, with the evaluation supplied
by the banked `WrapperProjectionCovers.rhoStar_eq_one_sub_etaC` (consumed by pin;
its own hypothesis `rho_sing <= 1 - eta_C` is `06:702--709`'s and is not claimed
here).  General in the two cover widths and the route allowance. -/
theorem ownerRect_mem_bracketGE_at_rhoStar {ηR ηC : ℝ} {n mT : ℕ} {τ₀ : ℝ}
    {retained : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hsing : rhoSing n mT τ₀ ≤ 1 - ηC)
    (hrows : (Fintype.card Rw : ℝ) * (1 - ηR) ≤ (retained.card : ℝ))
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * rhoStar n mT τ₀ ηC ≤ (cols.card : ℝ)) :
    ownerRect retained cols ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC) := by
  rw [rhoStar_eq_one_sub_etaC hsing] at hcols
  exact ownerRect_mem_bracketGE hrows hcols

/-- **`09:1609`, the deletion-stable Stage-4 theorem read at the owner.**

"The deletion-stable Stage-4 theorem would make the owner `C`-hard."  The
frozen theorem bounds the family *minimum* (`08:317`); a member bound follows
because `Dfamily` is an infimum over members -- the vendored
`EthBridge.Dfamily_le_member`
-- and the owner rectangle is a member by §2.  `thm:dense-stage4` itself is consumed
by pin as `DenseStageFourOpening.DenseStageFourConclusion`; none of
`08:330--1346` is re-derived, and this declaration makes it no more proved than
it already was.  General. -/
theorem ownerHard_of_denseStageFour (Nmat : Rw → Cl → Bool) {ηR ηC : ℝ} {Cval : ℕ}
    {retained : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC Cval)
    (hmem : ownerRect retained cols ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC)) :
    Cval ≤ D (subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2) :=
  le_trans hdense
    (EthBridge.Dfamily_le_member (interlaceFun Nmat 1)
      (bracketGE Rw Cl 1 (1 - ηR) (1 - ηC)) (ownerRect retained cols) hmem)

/-- **`09:1600--1609` composed.**  The frozen chain from the two densities to the
owner's hardness, with no intermediate object named.  General. -/
theorem ownerHard_of_densities (Nmat : Rw → Cl → Bool) {ηR ηC : ℝ} {Cval : ℕ}
    {retained : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC Cval)
    (hrows : (Fintype.card Rw : ℝ) * (1 - ηR) ≤ (retained.card : ℝ))
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ)) :
    Cval ≤ D (subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2) :=
  ownerHard_of_denseStageFour Nmat hdense (ownerRect_mem_bracketGE hrows hcols)

end Bracket

/-! ## §3  "Impossible under the alleged shallow protocol" (`09:1609--1610`)

The owner is a **final Alice-frontier node** of the routed certificate system of
the alleged `(C+r-1)`-bit protocol.  Three banked facts meet there:

* its residual subtree has depth at most `C-1` (`09:1341--1343`, the banked
  `RoutedSystem.final_residual_budget`);
* the complexity of any rectangle at a node is at most that residual depth (the
  banked `TerminalResidualComparison.D_le_cost_descend_of_computes`);
* the owner rectangle has complexity at least `C` (§2).

Their conjunction is the frozen contradiction, and the banked
`DenseWrapperFrontier.finalNode_budget_contradiction` is exactly it. -/

section Owner

variable {X Y Coord ι V : Type*} {P : Protocol X Y Bool} {r A0 : ℕ}

/-- **`09:1609--1610`, the frozen impossibility, PROVED -- the deliverable of
this module's hardness layer.**

"The deletion-stable Stage-4 theorem would make the owner `C`-hard, impossible
under the alleged shallow protocol."  Read as what it is: at a final Alice node
of the routed system, the owner **cannot** retain more than `1 - eta_R` of the
rows of its copy of `N`.  That conclusion is precisely the `hHard` binder the
banked `WrapperMassRedistribution.wrapperMassLeavesOwner` consumes.

The column half of the residual rectangle is **discharged, not assumed**: every
frontier address is an Alice-only route (`09:1250--1252`,
`RoutedSystem.node_isAlicePath`), so `routeCols_of_isAlicePath` supplies it --
this is `09:1330--1331` turned into a proof.  The row half `hrow` and the
sections `iotaA`, `iotaB`, `hgame` are the frozen reading of the owner's copy of
`N` inside the wrapper's carriers, carried as the binders they are
(GAP-EXPOSED item 2).

General in the five carriers, in the protocol, in the frontier index, in the
matrix and in both tolerances. -/
theorem ownerRetention_le {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {C : ℕ} (S : RoutedSystem P Coord ι V r A0) (hC : 3 ≤ C)
    (hcost : P.cost ≤ C + r - 1) {v : V} (hv : S.firstBob v = false)
    {gamb : X → Y → Bool} (hcomp : Protocol.Computes P gamb)
    (Nmat : Rw → Cl → Bool) {ηR ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    {retained : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC C)
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaA : {a // a ∈ (ownerRect retained cols).1} → X)
    (iotaB : {c // c ∈ (ownerRect retained cols).2} → Y)
    (hrow : ∀ a, RouteRows P (S.node v) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2 a b = gamb (iotaA a) (iotaB b)) :
    ¬ (1 - ηR < rowDensity retained) := by
  intro hret
  have hrows : (Fintype.card Rw : ℝ) * (1 - ηR) ≤ (retained.card : ℝ) :=
    le_of_lt ((lt_rowDensity_iff hRw (1 - ηR)).mp hret)
  have hhard := ownerHard_of_densities Nmat hdense hrows hcols
  have hcol : ∀ b, RouteCols P (S.node v) (iotaB b) := fun b =>
    routeCols_of_isAlicePath (S.node_isAlicePath v) (iotaB b)
  have hres := D_le_cost_descend_of_computes (P := P) (p := S.node v) hcomp iotaA iotaB
    hrow hcol hgame
  have hbudget := S.final_residual_budget (C := C) hv hcost
  exact finalNode_budget_contradiction (C := C) (r := r)
    (B := (descend P (S.node v)).cost) hC hbudget (le_trans hhard hres)

/-! ## §4  `eq:wrapper-mass-leaves-owner` (`09:1611--1615`) at the engine -/

/-- **`eq:wrapper-mass-leaves-owner` (`09:1600--1615`), at the routed system.**

"If the last line were at most `eta_R m/2`, then the owner would retain more
than `1 - 7 eta_R/8 > 1 - eta_R` ... impossible under the alleged shallow
protocol.  We have proved `sum_{T != own(j)} m_{j,T} > eta_R/2`."

`L₁`, `L₂`, `L₃` are the first three table rows at their frozen budgets
(`09:1575`, `09:1577`, `09:1579`), which the banked
`MassRedistributionCounting.initiallyDeleted_le_budget`, `cleanRouteLoss_engine`
and `goodDonor_firstBobMass_le` produce.  `L₄` is the fourth row, the frozen
`sum_{T != own(j)} m_{j,T}`.  The arithmetic is the banked
`WrapperMassRedistribution.wrapperMassLeavesOwner`, consumed by pin; what this
declaration adds is that its `hHard` binder is **discharged** by §3 rather than
assumed.  General. -/
theorem massLeavesOwner_engine {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {C : ℕ} (S : RoutedSystem P Coord ι V r A0) (hC : 3 ≤ C)
    (hcost : P.cost ≤ C + r - 1) {v : V} (hv : S.firstBob v = false)
    {gamb : X → Y → Bool} (hcomp : Protocol.Computes P gamb)
    (Nmat : Rw → Cl → Bool) {ηR ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    {retained : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC C)
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaA : {a // a ∈ (ownerRect retained cols).1} → X)
    (iotaB : {c // c ∈ (ownerRect retained cols).2} → Y)
    (hrow : ∀ a, RouteRows P (S.node v) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2 a b = gamb (iotaA a) (iotaB b))
    {L₁ L₂ L₃ L₄ : ℝ} (hηR : 0 < ηR)
    (h₁ : L₁ ≤ ηR / 16) (h₂ : L₂ < ηR / 16) (h₃ : L₃ ≤ ηR / 4)
    (hret : 1 - (L₁ + L₂ + L₃ + L₄) ≤ rowDensity retained) :
    ηR / 2 < L₄ :=
  wrapperMassLeavesOwner hηR h₁ h₂ h₃ hret
    (ownerRetention_le S hC hcost hv hcomp Nmat hRw hdense hcols iotaA iotaB hrow hgame)

/-- **The whole frozen block `09:1566--1615`, assembled.**

The four table rows enter as the four **categories** of `09:1569--1570` rather
than as four abstract reals: `D₁` the initially deleted rows (`09:1574--1575`),
`D₂` the base rows lost along the unique clean route (`09:1576--1577`), `D₃` the
protected rows stopped at first-Bob nodes (`09:1578--1579`), `D₄` the protected
rows sent to other final nodes (`09:1580--1581`).  Their disjointness and
coverage are the frozen sentence; the retention is then §1's identity, and the
conclusion is `eq:wrapper-mass-leaves-owner` on the fourth category,
`rowDensity D₄ = sum_{T != own(j)} m_{j,T}`.  General. -/
theorem massLeavesOwner_of_fourCategories {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    [DecidableEq Rw]
    {C : ℕ} (S : RoutedSystem P Coord ι V r A0) (hC : 3 ≤ C)
    (hcost : P.cost ≤ C + r - 1) {v : V} (hv : S.firstBob v = false)
    {gamb : X → Y → Bool} (hcomp : Protocol.Computes P gamb)
    (Nmat : Rw → Cl → Bool) {ηR ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    {retained D₁ D₂ D₃ D₄ : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat ηR ηC C)
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaA : {a // a ∈ (ownerRect retained cols).1} → X)
    (iotaB : {c // c ∈ (ownerRect retained cols).2} → Y)
    (hrow : ∀ a, RouteRows P (S.node v) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2 a b = gamb (iotaA a) (iotaB b))
    (hcover : (Finset.univ : Finset Rw) \ retained = D₁ ∪ D₂ ∪ D₃ ∪ D₄)
    (h₁₂ : Disjoint D₁ D₂) (h₁₃ : Disjoint D₁ D₃) (h₁₄ : Disjoint D₁ D₄)
    (h₂₃ : Disjoint D₂ D₃) (h₂₄ : Disjoint D₂ D₄) (h₃₄ : Disjoint D₃ D₄)
    (hηR : 0 < ηR)
    (h₁ : rowDensity D₁ ≤ ηR / 16) (h₂ : rowDensity D₂ < ηR / 16)
    (h₃ : rowDensity D₃ ≤ ηR / 4) :
    ηR / 2 < rowDensity D₄ := by
  refine massLeavesOwner_engine S hC hcost hv hcomp Nmat hRw hdense hcols iotaA iotaB
    hrow hgame hηR h₁ h₂ h₃ ?_
  exact le_of_eq
    (rowDensity_retained_eq hRw hcover h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄).symm

end Owner

/-! ## §5  Statement poles

A green build sees none of this.  Each item shows that a hypothesis of a
statement above is load-bearing, or that a conclusion is not satisfied by its
trivial witness. -/

section Poles

/-- **Pole 1: `09:1569`'s "disjoint" is load-bearing.**

Without disjointness the frozen bookkeeping over-counts.  Here `Rw = Fin 2`, the
retained set is empty, and `D₁ = D₂ = univ` with `D₃ = D₄` empty: the union is
still the whole missing set, so `hcover` holds, yet the four counts add to `4`
against `|Rw| = 2`.  So `card_retained_add_card_categories` is not a
repackaging of `Finset.card_sdiff_add_card_eq_card`. -/
theorem categories_need_disjointness :
    ((Finset.univ : Finset (Fin 2)) \ (∅ : Finset (Fin 2))
        = (Finset.univ : Finset (Fin 2)) ∪ (Finset.univ : Finset (Fin 2))
            ∪ (∅ : Finset (Fin 2)) ∪ (∅ : Finset (Fin 2)))
      ∧ (∅ : Finset (Fin 2)).card
          + ((Finset.univ : Finset (Fin 2)).card + (Finset.univ : Finset (Fin 2)).card
              + (∅ : Finset (Fin 2)).card + (∅ : Finset (Fin 2)).card)
        ≠ Fintype.card (Fin 2) := by
  constructor
  · decide
  · decide

/-- **Pole 2: the bracket's row clause is a genuine constraint.**

`ownerRect_mem_bracketGE` is not automatic: a rectangle whose retained row set is
too small is **not** a member, so the retention of `09:1600--1607` is doing work
and the membership is not a tautology about the one-fold interlace.

Self-chosen values are legitimate here and only here: this is a rejection probe
claiming **no** legality at any paper parameter. -/
theorem ownerRect_needs_the_row_density :
    ownerRect ({0} : Finset (Fin 8)) (Finset.univ : Finset (Fin 1 → Fin 4))
      ∉ bracketGE (Fin 8) (Fin 4) 1 (1 / 2) (3 / 4) := by
  intro h
  have hfib := h.1 0 (Finset.mem_univ _)
  rw [ownerRect_fiber_card ({0} : Finset (Fin 8))
    (Finset.univ : Finset (Fin 1 → Fin 4)) 0] at hfib
  have hcard : ((Fintype.card (Fin 8) : ℝ) * (1 / 2)) = 4 := by
    rw [Fintype.card_fin]; norm_num
  rw [hcard] at hfib
  have hone : ({0} : Finset (Fin 8)).card = 1 := by decide
  rw [hone] at hfib
  norm_num at hfib

/-- **Pole 3: the hardness step of `09:1609--1610` is load-bearing.**

`eq:wrapper-mass-leaves-owner` does **not** follow from the first three table
rows alone.  At `eta_R = 1/2` with all four losses zero, the three budget
hypotheses `h₁`, `h₂`, `h₃` of `wrapperMassLeavesOwner` hold, the retention
binder `hret` holds at retention `1`, and yet the frozen conclusion
`eta_R/2 < L₄` fails.  What fails in that configuration is exactly `hHard`:
`1 - eta_R = 1/2 < 1`, i.e. the owner *does* retain more than `1 - eta_R`.  So
the deletion-stable Stage-4 theorem is the whole content of the step, and
`ownerRetention_le` is not decoration. -/
theorem massLeavesOwner_needs_the_hardness_step :
    ((0 : ℝ) ≤ (1 / 2 : ℝ) / 16) ∧ ((0 : ℝ) < (1 / 2 : ℝ) / 16)
      ∧ ((0 : ℝ) ≤ (1 / 2 : ℝ) / 4)
      ∧ ((1 : ℝ) - (0 + 0 + 0 + 0) ≤ 1)
      ∧ ((1 : ℝ) - (1 / 2 : ℝ) < 1)
      ∧ ¬ ((1 / 2 : ℝ) / 2 < 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Pole 4: `ownerRetention_le`'s conclusion is not vacuous.**

The negated statement it forbids is satisfiable a priori: at the full retained
set the retention is `1`, which strictly exceeds `1 - eta_R` for every positive
`eta_R`.  So the theorem rules out a genuinely available state rather than one
that arithmetic already excluded.  General in the row carrier. -/
theorem ownerRetention_conclusion_is_not_vacuous {Rw : Type*} [Fintype Rw]
    (h : 0 < Fintype.card Rw) {ηR : ℝ} (hηR : 0 < ηR) :
    1 - ηR < rowDensity (Finset.univ : Finset Rw) := by
  rw [rowDensity_univ h]
  linarith

/-- **Pole 5: some lower bound on `C` is what makes `09:1610` a contradiction --
`hC` cannot be dropped.**

The banked `DenseWrapperFrontier.finalNode_budget_contradiction` has signature
`(hC : 3 <= C) (hbudget : B + r <= C + r - 1) (hlower : C <= B) : False`.  Drop
`hC` and the remaining two clauses are simultaneously satisfiable: **take
`C = 0`, `B = 0`, `r = 0`**, where `hbudget` reads `0 + 0 <= 0 + 0 - 1` and
`hlower` reads `0 <= 0`.  Both conjuncts below are those two clauses at those
values, so the pole exhibits the *actual* premises of the banked lemma rather
than a rearrangement of them.

Three cautions are part of the claim, not footnotes to it.

* **The corner is a natural-number truncation corner.**  `0 + 0 <= 0 + 0 - 1`
  holds in `Nat` only because `0 - 1 = 0`; over `ZZ` the clause would read
  `0 <= -1` and fail.  The pole therefore witnesses that `hC` is load-bearing
  **in the banked `Nat`-valued statement**, which is the statement the frozen
  argument is transcribed into, and claims nothing about a hypothetical
  integer-valued variant.
* **`r = 0`, not `r = 1` (this is the repair).**  For every `r >= 1` the budget
  at `C = 0` reads `r <= r - 1`, which is false, so no witness exists there; and
  for `C = 1` and `C = 2` the two clauses are contradictory at every `r`.  The
  `r = 0` corner is the only one, which is why it is the one exhibited.
* **The dense endpoint is separately free at `C = 0`** --
  `DenseStageFourOpening.DenseStageFourConclusion Nmat etaR etaC Cval` unfolds to
  `Cval <= Dfamily (interlaceFun Nmat 1) (bracketGE ...)` over `Nat`, and
  `0 <= _` always holds there -- so no clause of `ownerRetention_le`'s bundle
  re-imposes the floor behind `hC`'s back.

**This pole is NOT a tightness claim for the frozen `3`** (verify-seat record
finding **F5**).  What it establishes is that `hC` cannot be dropped *entirely*.
In the banked `Nat`-valued statement the weaker `1 <= C` already suffices: from
`hlower : C <= B` and `hbudget : B + r <= C + r - 1`, for `C >= 1` one has
`C + r - 1 = (C - 1) + r`, hence `B <= C - 1 < C <= B`, i.e. `False`.  So `3` is
not the minimal floor *for this arithmetic lemma*; the frozen `C >= 3` of
`09:1339` is imposed by the ladder call's own hypothesis list
(`lem:wrapper-reference` and `2 x_T <= t_ref x_T <= 1`), not by the budget
contradiction, and this pole speaks only to the latter.  Consistently with that,
the three cautions above isolate `(C, B, r) = (0, 0, 0)` as the *unique* corner
at which both clauses survive.

General in the matrix and in both tolerances. -/
theorem impossibility_needs_C_ge_three {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (ηR ηC : ℝ) :
    DenseStageFourConclusion Nmat ηR ηC 0 ∧ ¬ (3 ≤ 0)
      ∧ (((0 : ℕ) + 0 ≤ 0 + 0 - 1) ∧ ((0 : ℕ) ≤ 0)) := by
  refine ⟨Nat.zero_le _, by norm_num, ?_⟩
  exact ⟨by omega, by omega⟩

/-- **Hypothesis consistency for `ownerRetention_le`, as far as it can honestly be
exhibited -- and the exact reason it cannot be exhibited further.**

Attempting to derive `False` from `ownerRetention_le`'s full bundle fails, and the shape
of that failure is the point.  The bundle constrains the owner rectangle
only through the conclusion: `hdense` bounds the family *minimum* from below,
while the budget chain bounds *every* rectangle routing to the node from above by
`C-1`; the two coexist exactly when the owner rectangle is **not** a member, i.e.
when the retention fails.  Nothing forces the retention, so no contradiction
arises and the theorem is not vacuous.

What cannot be exhibited is a *live* instance, and the obstruction is named
precisely: `hdense` at a legal `C >= 3` is the Stage-4 lower bound itself
(GAP-EXPOSED item 4).  The banked
`DenseStageFourOpening.denseStageFour_hypotheses_consistent` -- consumed here by
pin, not restated -- shows the dense endpoint is a **realizable** binder rather
than a contradictory one, at `C = 1` on the banked two-element witness; the
frozen floor `3 <= C` of **`09:1339`** (the hypothesis list of the ladder call,
*not* `09:1341--1343`, which is the suffix-depth sentence; record repair **R2**)
is what puts that instance out of range, and closing the gap is a construction
obligation, not a repair of this statement. -/
theorem denseBinder_is_realizable_but_below_the_frozen_floor :
    DenseStageFourConclusion StageTwoRelaxed.bobBit (1 / 4) (1 / 4) 1 ∧ ¬ (3 ≤ 1) :=
  ⟨denseStageFour_hypotheses_consistent, by norm_num⟩

end Poles

/-! ## §6  Non-vacuity: the frozen partition and the bracket membership, fired

**NON-FIDELITY.**  The paper's own instance of this block -- the owner rectangle
of a good donor in the routed system of the *alleged shallow protocol*, at the
frozen matrix `N` -- is not available: its routing, its protected-reservoir mass
and the Stage-4 lower bound `hdense` are all unbuilt, and the
canonical-inhabitation obligation for it is **registered** in the header and in
the ledger row, to be discharged only when the construction lands.

What follows is a smoke probe chosen so that **every clause is nondegenerate**:
all four categories are inhabited, the retained set is a proper nonempty subset,
and the bracket family's row clause is attained at **equality**.

**Self-chosen quantities, named explicitly.**  `Rw = Fin 8`, `Cl = Fin 4`,
`eta_R = 1/2` and `eta_C = 1/4` are **ours** and are **BEYOND-PAPER AUDIT**
values: they audit *our* encoding at a point the paper never visits.  They are
illegal by a wide margin -- `eta_R` is DEFINED by `eq:eta-choice`
(`06:206--217`), whose **first `eta_R` term** `(1/2) * mu_Sigma/100 =
mu_Sigma/200`, with the frozen `mu_Sigma = 1/184` of
`eq:fixed-protected-masses` (`06:133`), forces `eta_R <= mu_Sigma/200 =
1/36800`.  (`06:228`'s chain `0 < eta_R <= eta_C/2 < tau < x_N` with the frozen
`tau = 1/92`, `x_N = 1/16` is a *weaker* bound, `eta_R < 1/92`; the `1/36800`
is the `eq:eta-choice` term -- verify-seat record finding **F4**.)  At any
legal tolerance the frozen row threshold `ceil(m_N (1 - eta_R))` forces
`retained = univ` on a carrier this small, which would make every category
empty; the honest choice is therefore an explicitly illegal tolerance on a
nondegenerate carrier rather than a legal tolerance on a degenerate one. -/

section Probe

/-- The retained rows of the probe owner: a proper nonempty subset. -/
def probeRetained : Finset (Fin 8) := {0, 1, 2, 3}

/-- Initially deleted rows (`09:1574`), inhabited. -/
def probeD₁ : Finset (Fin 8) := {4}

/-- Base rows lost along the unique clean route (`09:1576`), inhabited. -/
def probeD₂ : Finset (Fin 8) := {5}

/-- Protected rows stopped at first-Bob nodes (`09:1578`), inhabited. -/
def probeD₃ : Finset (Fin 8) := {6}

/-- Protected rows sent to other final nodes (`09:1580`), inhabited -- the
category `eq:wrapper-mass-leaves-owner` bounds from below. -/
def probeD₄ : Finset (Fin 8) := {7}

/-- **The probe is nondegenerate.**  All four frozen categories are inhabited and
the retained set is a proper nonempty subset, so no clause of §1 is satisfied by
an empty case. -/
theorem probe_categories_nonempty :
    probeRetained.Nonempty ∧ probeD₁.Nonempty ∧ probeD₂.Nonempty
      ∧ probeD₃.Nonempty ∧ probeD₄.Nonempty ∧ probeRetained ≠ Finset.univ := by
  refine ⟨⟨0, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩,
    ⟨7, by decide⟩, by decide⟩

theorem probe_cover :
    (Finset.univ : Finset (Fin 8)) \ probeRetained
      = probeD₁ ∪ probeD₂ ∪ probeD₃ ∪ probeD₄ := by decide

theorem probe_disjoint :
    Disjoint probeD₁ probeD₂ ∧ Disjoint probeD₁ probeD₃ ∧ Disjoint probeD₁ probeD₄
      ∧ Disjoint probeD₂ probeD₃ ∧ Disjoint probeD₂ probeD₄ ∧ Disjoint probeD₃ probeD₄ := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem probe_cards :
    probeRetained.card = 4 ∧ probeD₁.card = 1 ∧ probeD₂.card = 1
      ∧ probeD₃.card = 1 ∧ probeD₄.card = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **§1 fired.**  The frozen partition of `09:1569--1570` produces the retention
count of `09:1600--1601` at the probe: `4 + (1+1+1+1) = 8`. -/
theorem probe_card_identity :
    probeRetained.card + (probeD₁.card + probeD₂.card + probeD₃.card + probeD₄.card)
      = Fintype.card (Fin 8) :=
  card_retained_add_card_categories probe_cover probe_disjoint.1 probe_disjoint.2.1
    probe_disjoint.2.2.1 probe_disjoint.2.2.2.1 probe_disjoint.2.2.2.2.1
    probe_disjoint.2.2.2.2.2

/-- **The normalized retention at the probe.**  `retained = 1/2` and each loss is
`1/8`, so the frozen identity `retained = 1 - (L₁+L₂+L₃+L₄)` reads
`1/2 = 1 - 4/8`.  Every summand is nonzero. -/
theorem probe_rowDensity :
    rowDensity probeRetained = 1 / 2 ∧ rowDensity probeD₁ = 1 / 8
      ∧ rowDensity probeRetained
          = 1 - (rowDensity probeD₁ + rowDensity probeD₂ + rowDensity probeD₃
              + rowDensity probeD₄) := by
  have hid := rowDensity_retained_eq (Rw := Fin 8) (by simp) probe_cover
    probe_disjoint.1 probe_disjoint.2.1 probe_disjoint.2.2.1 probe_disjoint.2.2.2.1
    probe_disjoint.2.2.2.2.1 probe_disjoint.2.2.2.2.2
  refine ⟨?_, ?_, hid⟩
  · unfold rowDensity
    rw [probe_cards.1, Fintype.card_fin]
    norm_num
  · unfold rowDensity
    rw [probe_cards.2.1, Fintype.card_fin]
    norm_num

/-- **§2 fired, with the row clause TIGHT.**  At `eta_R = 1/2` the frozen row
threshold is `ceil(8 * 1/2) = 4`, attained exactly by the four retained rows; at
`eta_C = 1/4` the column threshold is `ceil(4 * 3/4) = 3` against the four
available outer columns.  Both are **BEYOND-PAPER AUDIT** values (see the section
header); the point of the instance is that the membership clauses are satisfiable
without slack in the row coordinate, so `ownerRect_mem_bracketGE` is not entered
on a vacuously generous bundle. -/
theorem probe_mem_bracketGE :
    ownerRect probeRetained (Finset.univ : Finset (Fin 1 → Fin 4))
      ∈ bracketGE (Fin 8) (Fin 4) 1 (1 - 1 / 2) (1 - 1 / 4) := by
  refine ownerRect_mem_bracketGE ?_ ?_
  · rw [probe_cards.1, Fintype.card_fin]
    norm_num
  · have hc : (Finset.univ : Finset (Fin 1 → Fin 4)).card = 4 := by decide
    rw [hc, Fintype.card_fin]
    norm_num

end Probe

/-! ## §7  Three of `ownerRetention_le`'s binders, live -- and the residue

**What this section does not say (record repair R3).**  Earlier prose here read
"`ownerRetention_le` cannot be fired ... a live firing would be a proof of
`thm:dense-stage4`".  Both halves were overstated and are withdrawn.  The
accurate statement: `ownerRetention_le` is not fired here because `hdense` at a
legal `C >= 3` (`09:1339`) would have to be exhibited at a concrete matrix, and
no such exhibit exists in this repository (GAP-EXPOSED item 4).  That is a
construction gap, not an impossibility -- `hdense` is a *realizable* binder, as
§5's `denseBinder_is_realizable_but_below_the_frozen_floor` shows at `C = 1` --
and supplying it at one concrete matrix would not be a proof of
`thm:dense-stage4`, which quantifies over the frozen construction.

**The coverage residue, named (record repair R5), with its no-leaning caution.**
What follows exhibits exactly three items at the banked live system: `hv`,
`hcost`, and the column half `hcol` (a theorem here, not a binder).  It exhibits
**none** of `iotaA`, `iotaB`, `hrow`, `hgame`, and none of `hcomp`, `hRw`,
`hcols`, `hdense`.  Nothing below may be leaned on as evidence that the rest of
`ownerRetention_le`'s bundle is jointly satisfiable at any system: the four
unexhibited sections are exactly the owner's-copy identification of GAP-EXPOSED
item 2, and their availability is the open question, not a corollary of these
three.

**NON-FIDELITY** throughout: `FirstBobFrontierInstance.liveSystem` carries that
module's own BEYOND-PAPER label for its alphabet and predicates, and `C = 3` here
is the frozen floor of `09:1339`, not a schedule value. -/

section LiveBinders

open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.FrontierIndexing

/-- **Three of `ownerRetention_le`'s binders, live -- and only three.**

At the banked live routed system and its final Alice node `[false, false]`:
`hv` (the node is final, not first-Bob), `hcost` (the alleged protocol is shallow
at `C = 3`, `r = 2`), and the column half of the residual rectangle -- which is
**not** a binder of `ownerRetention_le` at all but a theorem, and is exhibited
here to show that the discharge of `09:1330--1331` fires at a real node rather
than only in principle.

**Residue (R5), not to be leaned on:** `iotaA`, `iotaB`, `hrow` and `hgame` are
*not* exhibited at this system, nor are `hcomp`, `hRw`, `hcols`, `hdense`.  This
lemma is a three-item smoke check; it is not evidence about the remainder. -/
theorem live_owner_binders :
    liveSystem.firstBob liveFinalNodeZero = false
      ∧ liveProtocol.cost ≤ 3 + 2 - 1
      ∧ ∀ y : Bool, RouteCols liveProtocol (liveSystem.node liveFinalNodeZero) y := by
  refine ⟨by decide, by decide, ?_⟩
  intro y
  exact routeCols_of_isAlicePath (liveSystem.node_isAlicePath liveFinalNodeZero) y

/-- **The live final node's residual budget, live.**  `09:1341--1343` at the same
node: the suffix below it has depth at most `C - 1 = 2`.  This is the second half
of the frozen contradiction, available without any hardness input. -/
theorem live_owner_budget :
    (descend liveProtocol (liveSystem.node liveFinalNodeZero)).cost + 2 ≤ 3 + 2 - 1 :=
  liveSystem.final_residual_budget (C := 3) live_owner_binders.1 live_owner_binders.2.1

end LiveBinders

end EthInapproximability.ParameterizedNP.MassLeavesOwner
