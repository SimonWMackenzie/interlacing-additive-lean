import EthInapproximability.ParameterizedNP.FirstBobFrontierInstance

/-!
# Parameterized NP route: the split first-Bob instance, and the routing side of
`eq:wrapper-first-bob-light`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`),
  the **frontier layer** of the per-member shallow-protocol refutation engine.
* **The exact frozen lines traced here**, in print order:
  * `09:105`, "Let `q = 2^r` be the scale-alignment width", the width/exponent
    identification behind every `q`-vs-`2^r` substitution.
  * `09:434--441`, the defining display of the small-capacity cover data:
    `rho = 2y^2 = 18/25`, `u_2 = 2`, `u_kappa = kappa/2 + 1` for
    `4 <= kappa < t_ref`.  This is the **defining** display of `u_kappa`; the
    consuming block at `09:1283` only *uses* it.  Reified already, and consumed
    here by pin, as `WrapperProjectionCovers.smallCopyWidth`.
  * `09:1217--1221`, `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0` -- the defining
    display of the row floor, consumed by pin as `DenseWrapperFrontier.refRowFloor`.
  * `09:1233--1236`, the retention `A_r = q A_0` and the initial placement,
    "Start one clean reference certificate in every coordinate outside `E_0`,
    each with weight one".
  * `09:1238--1248`, the routing rule, **including the branching clause**
    "route it to both children if both qualify" and the kind transition "When a
    clean certificate splits, both descendants become low certificates of weight
    `1/2`".  This is the clause the live instance of §3 exercises.
  * `09:1250--1259`, the two stopping rules, `d_v`, `kappa_v = 2^{r-d_v}`,
    `W_v`, and "Every first-Bob node has `kappa_v >= 2`".
  * `09:1268`, "Put `vartheta = 9/16`.  We first close any first-Bob node
    satisfying `W_v >= vartheta kappa_v`."
  * `09:1277--1284`, the small-capacity readout: "Every certificate has weight
    `1` or `1/2`, and at a fixed node there is at most one descendant of each
    initial outer coordinate.  Hence the number of represented coordinates is at
    least `ceil(W_v)`, and `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`."
  * `09:1285--1290`, the frozen case split `kappa_v = 2,4,8` versus
    `kappa_v >= 16`, and the projection density `rho = 2y^2` with the denser Bob
    child retaining `y^2`.
  * `09:1292--1306`, the ladder call: `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G`,
    the trim to row density `kappa_v x_T`, and
    `Cref{lem:certified-row-ladder}` at `M = G`, `H = C-1`, `x = x_T`, `z = y`,
    `ell = ell_v`, with `C >= 3` giving `H >= 2` and
    `kappa_v x_T <= t_ref x_T <= 1` giving legality.
  * `09:1306--1313`, "Its lower bound is one more bit than the remaining child
    budget in the alleged protocol.  Therefore `W_v < vartheta kappa_v` at every
    first-Bob node `v`" (`eq:wrapper-first-bob-light`).
  * `09:1315--1319`, `lem:final-reference-uniqueness`, whose conclusion the live
    instance of §3 **respects**: every final Alice node here carries exactly one
    certificate.
  * `09:1346--1350` and `09:1352--1357`, the final-node classification, the
    frozen `c` and `ell` columns, and `eq:wrapper-clean-count`.
* **Cross-anchors opened first-hand for this tranche:** `09:1188--1213` (the
  contradiction frame and `lem:wrapper-no-bob-completion`), `09:1320--1344` (the
  proof of `lem:final-reference-uniqueness`), `09:327` with `A:117--118` (the
  `q/4 >= t_ref` exponent gate `k + 2 <= r` and the endpoint row legality), and
  `06:558--572` (`eq:tref-search`, `t_ref = 2^{k_ref}`) in
  `sections/06-parameter-schedule.tex` (SHA-256
  `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the only import is
  `FirstBobFrontierInstance`, whose ledger row records the same exclusion.
* **Proof status.**  Every declaration has exactly one of **three** shapes:
  1. a **general** property of the banked `FrontierIndexing.frontierWeight` and
     the banked `DenseWrapperFrontier` closure machinery (§1, §2);
  2. a **BEYOND-PAPER audit instance** of the banked
     `FrontierIndexing.canonicalSystem`, explicitly labelled as such (§3, §4);
  3. a **BEYOND-PAPER hypothesis-consistency check** at self-chosen numerals
     substituted for source-DEFINED quantities -- `smallCapacity_binders_consistent`
     alone, which is *not* an instance of `canonicalSystem` and therefore is not
     covered by §3's blanket label; it carries its own label in its docstring.
  **No mathematics is added**, and no conclusion of `eq:wrapper-u-dense` is
  asserted anywhere.

## What this tranche closes in the predecessor module

`FirstBobFrontierInstance.lean` (SHA-256
`D4E2F123C2D457CAB6B1EEC10F625DA0D6940B3B898F62D3F1921E979DB2C77F`, which pins
`FrontierIndexing.lean` at SHA-256
`057A0B39EDB5BA909AEC4A0061598BE3D38E8CCC781F3343D659089099F42F4B`) recorded two
**new** GAP-EXPOSED items, (12) and (13).  This module discharges (13) in full,
advances (12) partially and honestly, and touches no other item.

* **Item (13), the split branch never reached a first-Bob node, discharged.**
  The banked record read, verbatim: "no certificate splits along any route of
  `liveProtocol`, so every derived kind is `clean`, the frozen `ell` of
  `09:1349--1350` is `0` ... A live instance in which a *split* certificate's
  half-weight descendant reaches an exposed first-Bob node -- exercising
  `09:1244`'s branching clause and the light bound at the same node -- is the
  next-round obligation."  §3 below is that instance.  It is
  `FrontierIndexing.canonicalSystem` at the *same* protocol object `liveProtocol`
  the predecessor used -- reused by pin, because `CompletedNoBob` does not
  mention the reference rows -- with a **different frozen initial placement**:
  the coordinate `splitRows 0` straddles the root Alice predicate, so
  `09:1244`'s "route it to both children if both qualify" fires
  (`split_splitsAt_root`), the two descendants become `low` by `09:1245--1246`, one of
  them stops at the exposed Bob query of depth `1` and the other at a final Alice
  node of depth `2`.  Consequently: the exposed first-Bob node carries a
  **half-weight** certificate (`W_v = 1/2`, `split_frontierWeight_bobNode`) and
  `eq:wrapper-first-bob-light` is exercised there
  (`split_halfWeight_reaches_firstBob`); and the frozen `ell` column of
  `09:1349--1350` is **nonempty**, `ell = 1` (`split_splitNodes_card`,
  `split_splitNodes_nonempty`), where the predecessor had `ell = 0`.
* **Item (12), `eq:wrapper-first-bob-light` is supplied, not derived: advanced,
  NOT discharged.**  The banked record read: "no declaration derives
  `W_v < vartheta kappa_v` at an arbitrary first-Bob node from the routing".
  §1--§2 below begin that derivation and stop at a named remainder.
  * `ceil_frontierWeight_le_card_representedCoords` is `09:1280--1281` -- "the
    number of represented coordinates is at least `ceil(W_v)`" -- **proved from
    the routing**, by the ceiling of the predecessor's Aux A5
    (`frontierWeight_le_card_reaching`), which is itself the frozen
    `09:1278--1280` coordinate uniqueness.
  * `heavy_firstBob_smallCopyWidth_le` is the whole chain of `09:1283`,
    `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`, at a first-Bob node of the
    canonical system: it consumes the predecessor's Aux A6
    (`firstBob_capacity_dyadic`, which puts `kappa_v` in the dyadic form
    `09:1285--1287`'s case split needs) and the banked
    `DenseWrapperFrontier.smallCopyWidth_le_ceil_weight`.
  * `canonical_firstBobLight_of_closure` then produces
    `eq:wrapper-first-bob-light` **at the canonical system's own weight and
    capacity**: `W_v` is the derived `frontierWeight`, `ell_v = r - d_v` is the
    node's derived depth, and the closure of `09:1269--1306` enters as one named
    binder stated at its **cover-entry condition** -- `u_{kappa_v}` represented
    coordinates -- which is what `09:1287--1296` actually consumes, rather than
    at the raw weight condition of the banked abstract `wrapperFirstBobLight`.
  * `canonical_firstBobLight_smallCapacity` discharges the small-capacity branch
    of that binder against the banked, already-proved
    `smallCapacity_child_bound` (`09:1296--1306`) and `capacity_row_density_legal`
    (`09:1302--1304`), leaving exactly one named binder: `hselect`, the step
    `09:1287--1296` that selects `u_{kappa_v}` of the represented coordinates,
    reads off the parent projection density `rho = 2y^2`, follows the denser Bob
    child to `y^2` and identifies the trimmed restriction inside that child.
* **What remains open in item (12), named.**  `hselect` above is the column
  projection at a protocol node, which is not modelled (the banked
  `ROUTED-CERTIFICATE-SYSTEM-001` GAP-EXPOSED item 2/3 territory), and the
  **large-capacity branch** `09:1269--1276` -- `kappa_v >= t_ref`, the certified-
  scale reference stopping lemma at `r' = kappa_v/t_ref`, `a^sharp = 1` -- is
  **not** entered here at all.  Until both land, `hlight` stays a binder of
  `canonical_cleanCount` everywhere it is used, and citing this module as
  evidence that `eq:wrapper-first-bob-light` is discharged would be a misreading.

## Predecessor modules consumed **by pin**, never restated

* `Workspace.Types.Protocol` (through `LegacyNPCC.Core`, project-axiom-free):
  `Protocol`, `Protocol.aNode`, `Protocol.bNode`, `Protocol.leaf`.
* `EthInapproximability.ParameterizedNP.WrapperProjectionCovers`:
  `smallCopyWidth` (the frozen `u_kappa` of `09:436--441`).
* `EthInapproximability.ParameterizedNP.WrapperLowRungs`:
  `wrapperLowRungGates_legal_instance` (the banked legal `x_T` witness).
* `EthInapproximability.ParameterizedNP.DenseWrapperFrontier`: `refRowFloor`,
  `CertKind`, `WrapperFrontier` with `capacity`, `bobNodes`, `finalNodes`,
  `bobCapacity`, `cleanNodes`, `splitNodes`, `finalWeight`, `vartheta`,
  `smallCopyWidth_le_ceil_weight`, `capacity_row_density_legal`,
  `smallCapacity_child_bound`, `wrapperFirstBobLight`.
* `EthInapproximability.ParameterizedNP.RoutedCertificateSystem`:
  `IsFirstBobNode`, `RoutedSystem`, `toWrapperFrontier`.
* `EthInapproximability.ParameterizedNP.RoutingDynamics`: `kindAlong`,
  `splitsAt`, `CompletedNoBob`.
* `EthInapproximability.ParameterizedNP.FrontierIndexing`: `descendants`,
  `coordRoutes`, `frontierRoutes`, `FrontierNode`, `CertIndex`,
  `canonicalSystem`, `frontierWeight`, `canonical_cleanCount`.
* `EthInapproximability.ParameterizedNP.FirstBobFrontierInstance`:
  `frontierWeight_eq_weight_of_unique_coord`, `frontierWeight_le_card_reaching`,
  `frontierWeight_pos`, `firstBob_capacity_dyadic`, and the protocol object
  `liveProtocol` with its frame condition `live_hcomp`.

## Canonical inhabitation

* **No new `structure` and no new `inductive` is introduced**, so this module
  opens **no** canonical-inhabitation obligation: the `RoutedSystem` obligation
  stays discharged at the paper's own construction by
  `FrontierIndexing.canonicalSystem`, and `representedCoords` is a `Finset`-valued
  readout of the routing, not a carrier of data.
* **`splitSystem` is `canonicalSystem` itself**, at the two frozen inputs
  `live_hcomp` (the conclusion of `lem:wrapper-no-bob-completion`,
  `09:1195--1200`) and `split_hR` (the retention `A_r <= |R i|` of
  `09:1233--1235`).  Nothing about the routed system, the frontier, the kinds or
  the weights is chosen: the frontier `{[false,false], [false,true], [true]}`,
  the split at the root, both `low` kinds and all three weights are **computed
  outputs** (`split_descendants_zero`, `split_descendants_one`,
  `split_frontierRoutes`, `split_splitsAt_root`, `split_*_kind`).
* **BEYOND-PAPER AUDIT label (mandatory, and not a legality claim).**  `r` is
  DEFINED by the schedule -- `06:515` `q = 2^{A_wrap L_P^2}` with `09:105`
  `q = 2^r`, so `r = A_wrap L_P^2` -- `A_0` is DEFINED by `09:1219`
  `A_0 = ceil(2 x_T m_G)`, and `e_0 = |E_0|` is fixed by the exceptional-set
  bookkeeping of `09:448--451`.  Putting the numerals `r = 2`, `A_0 = 1`,
  `e_0 = 2` at those three places, and reusing the predecessor's self-chosen
  alphabet `Fin 12` and its two Alice predicates and Bob predicate, is **ours**:
  this instance audits *our encoding* at a point the paper never visits, and is
  strictly weaker evidence than the paper's own application point.  `q = 4` is
  **not** chosen but *derived*, by evaluating `09:105`'s `q = 2^r` at `r = 2`;
  the row floor `A_r = 4` is derived through the banked `refRowFloor` from
  `09:1221`; `kappa_v = 2` is derived through the banked `stoppingCapacity` from
  `09:1255`; and `u_2 = 2` is derived through the banked `smallCopyWidth` from
  `09:438`.  The parametric legality statement, valid at *every* legal
  `(r, A_0)` including the schedule's, remains
  `FrontierIndexing.canonicalSystem_legal_instance`.
* **Why `e_0 = 2` here, and what it costs -- recorded, not hidden.**  At `r = 2`
  a frontier carrying an exposed first-Bob node has at most three addresses
  (`[b]` and the two depth-`2` addresses below the other root child), so
  `lem:final-reference-uniqueness` (`09:1315--1319`) caps the two final nodes at
  one certificate each.  A half-weight certificate at the first-Bob node forces
  its coordinate to split at the root, hence to occupy one of the two final
  addresses as well; the remaining budget admits exactly one further started
  coordinate, so `card Coord = 2` and the frozen `hcoord` of `09:1235--1236`
  forces `e_0 >= q - 2 = 2`.
  **The uniqueness lemma alone does not close this**, and the missing step is
  recorded rather than elided: `lem:final-reference-uniqueness` constrains only
  *final Alice* nodes, so it does not by itself exclude a third started
  coordinate that routes entirely into the `true` subtree and stops at the
  exposed Bob node `[true]`, occupying no final address at all.  What excludes
  that coordinate is the **light bound**: it would arrive clean, adding weight
  `1` to the split's `1/2`, so `W_[true] = 3/2 > 9/8 = vartheta kappa_v`, which
  contradicts `split_hlight` -- i.e. `eq:wrapper-first-bob-light` at that very
  node.  With that step the count `card Coord = 2` is closed, and the Lean pole
  `split_cleanCount_tradeoff_is_forced` formalizes only the arithmetic side of
  the trade-off, so nothing in the development below depends on this paragraph.
  The predecessor's own pole
  `FirstBobFrontierInstance.live_cleanCount_first_conjunct_is_live` records that
  at `e_0 = 2` the **first** conjunct of `eq:wrapper-clean-count` reads
  `-4/7 <= c` and constrains nothing.  So this instance makes the **second**
  conjunct live and the half-weight column nonempty, at the price of the first --
  the exact converse of the predecessor's instance, and
  `split_cleanCount_tradeoff_is_forced` states the trade-off arithmetically
  rather than leaving it implicit.  Neither instance is a substitute for the
  paper's own application point.

## Aux-lemma battery and statement poles

Five **general** properties of the new `representedCoords` readout, all proved:
`mem_representedCoords` (membership identity), `representedCoords_nonempty`
(every frontier node has a donor), `card_representedCoords_le_card_coord`
(bound), `ceil_frontierWeight_le_card_representedCoords` (the frozen
`09:1280--1281` ceiling step) and `card_representedCoords_eq_one_of_unique`
(the specialization the frozen counting uses).  Plus the general
`heavy_firstBob_smallCopyWidth_le` and the two general closure theorems of §2.

Four **statement poles**: `split_hlight_is_exercised_at_half_weight` (the light
bound is checked at a node carrying a half-weight descendant of a split, not at
a clean one), `firstBobLight_closure_antecedent_is_not_automatic` (at the live
instance the cover-entry condition `u_2 <= #represented` **fails**, so the
closure binder of §2 is not discharged by an antecedent that always holds),
`split_cleanCount_second_conjunct_constrains_ell` (a larger `ell` would break the
frozen bound, so the second conjunct says something) and
`split_cleanCount_tradeoff_is_forced` (the first conjunct is live only for
`e_0 < 7/4`, which `card Coord = 2` excludes).

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for
this tranche (`first-Bob`, `first Bob`, `split`, `half-weight`, `represented`,
`cover`, `u_`, `kappa`).  Every hit was opened and none states what any
declaration below states; in particular the predecessor's finding is
re-confirmed and not re-used for a second declaration.

* `01-introduction.tex:101` and `02-preliminaries.tex:564` ("a weighted
  frontier", "the weighted frontier") are the **Stage-4 quotient-support**
  weighted frontier, a different mechanism from the wrapper's first-Bob frontier.
* `02-preliminaries.tex:301` ("not stable under the first Bob bit") is a remark
  about rectangle stability, not about a frontier node.
* `A-stage4-details.tex:263--271` is the **same Stage-4 quotient-support**
  stopping count, whose `kappa_v` is a residual copy capacity conserving a
  template/witness mass rather than the certificate weight `W_v` of `09:1257`;
  it is also unnumbered prose.
* `A-stage4-details.tex:318--319`, `371--373` and `387` ("terminal frontier")
  are the direct-bridge / two-stream terminal frontier, with `371--373` already
  recorded as unclaimed prose by `WRAPPER-PROJECTION-COVERS-001`.
* `A-stage4-details.tex:389--391` is the **closest** reader sentence to §2 --
  "Its small-capacity and final-node closures use the certified row ladder
  `Cref{lem:paper-certified-row-ladder}`; they do not require a new odd-copy
  theorem", which is the reader's one-sentence echo of `09:1306--1307` ("This
  argument, not the ordinary robustness-based odd-copy theorem, is the
  small-capacity fallback").  It is **not claimed**, for two independent
  reasons: it is unnumbered prose inside a paragraph about the two-stream
  lemma, not a statement; and it is already assigned to
  `TERMINAL-TWO-STREAM-001`, so claiming it here would give one reader item two
  declarations.
* `03-parameterized-construction.tex:567` ("`q_1+2 = 2^a` represented copies of
  `R`") and `C-effectivity-details.tex:74` ("their represented") use
  "represented" in unrelated senses -- Stage-1 copy multiplicity and encoded
  input indices -- not the represented *outer coordinates* of `09:1280`.

**No reader item is claimed**, and the absence is a finding about the reader
artifact rather than an omission here.  In particular the reader artifact
contains no statement of `eq:wrapper-first-bob-light`, no `vartheta`, no
`u_kappa`, and no first-Bob frontier weight at all.

## What is *not* claimed

`hDenseRung` is **neither discharged nor fed**; `eq:wrapper-u-dense` is asserted
nowhere below; `sec:wrapper-mass-redistribution` (`09:1512--1781`) stays
**DEFERRED in full** under `WRAPPER-MASS-REDISTRIBUTION-001` and nothing of it is
formalized, cited or implied; GAP-EXPOSED items 3, 4, 5 and 6 of
`ROUTED-CERTIFICATE-SYSTEM-001` are untouched; `lem:final-reference-uniqueness`
remains the named binder `hfinal` of the banked `canonical_cleanCount` -- this
tranche *supplies* it at one audit instance, respecting its conclusion, and
**does not discharge it in general**; and **no route completion is claimed.**

**GAP-EXPOSED, recorded rather than papered over, with a next-round
prescription:**

14. **The large-capacity branch of `09:1269--1276` is not entered.**  The frozen
    closure has two branches, and only `kappa_v < t_ref` is assembled here
    (`canonical_firstBobLight_smallCapacity`).  The branch `kappa_v >= t_ref`
    invokes the certified-scale reference stopping lemma on `G` at
    `r' = kappa_v/t_ref`, `a^sharp = 1`, with the other parameters those of
    `sec:wrapper-low-rungs`; its banked neighbours are in `WrapperLowRungs`, but
    no declaration composes them into the `hclosure` binder of
    `canonical_firstBobLight_of_closure` at `kappa_v >= t_ref`.  Next round owes
    that composition, after which the two branches can be joined by the frozen
    dichotomy on `kappa_v` versus `t_ref`.
15. **`hselect` -- the projection/selection step `09:1287--1296` -- is a named
    binder, not a theorem.**  "Every represented coordinate is outside `E_0`, so
    the parent projection to any selected `u_{kappa_v}` of them has density at
    least `rho = 2y^2`.  The denser Bob child retains density at least `y^2`.
    Each selected certificate has at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v
    x_T m_G` reference rows, so trim it to the row density `kappa_v x_T`."  The
    banked `denserChild_density_frozen` is the density halving in isolation, but
    the column projection *at a protocol node* is not modelled, so nothing
    identifies the ladder's certified restriction inside the selected Bob child.
    Until that lands, `canonical_firstBobLight_smallCapacity` reduces the
    small-capacity branch to exactly one unproved step and no further.
16. **`e_0 = 1` and a nonempty half-weight column cannot coexist at `r = 2`.**
    §3's instance pays for the nonempty `ell` column with `e_0 = 2`, where the
    first conjunct of `eq:wrapper-clean-count` is uninformative, and
    `split_cleanCount_tradeoff_is_forced` shows the *informativeness threshold*
    `e_0 < 7/4` is arithmetic, not an artefact of the chosen rows (its first
    clause; see item 17 for what that pole does **not** formalize).  An audit
    instance that makes **both**
    conjuncts live simultaneously needs `r >= 3`, hence a frontier with at least
    four addresses; that is the next-round shape, and it is a strictly larger
    `decide` than anything landed so far.
17. **`split_cleanCount_tradeoff_is_forced`'s middle clause is weaker than its
    own prose.**  The pole's argument is "`e_0 <= 1` forces
    `card Coord >= q - e_0 >= 3`, while the instance has `card Coord = 2`", but
    the formalized middle clause is `(4 : R) - 2 < 3`, i.e. `2 < 3` at the
    instance's own `e_0 = 2` -- the instance's coordinate demand, not the
    quantified demand the argument needs.  The clause is true and proved, and
    nothing else in the module consumes it, so this is a shortfall in what the
    pole certifies rather than an unsound statement.  Next round owes the
    quantified replacement `forall e0 : R, e0 < 7/4 -> (card Coord : R) < 4 - e0`
    (equivalently `(4 : R) - 1 > 2`).  This is a **statement** change, so it was
    deliberately *not* applied as a record repair at the verify seat.
-/

namespace EthInapproximability.ParameterizedNP.SplitFirstBobInstance

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance

/-! ## §1  The represented coordinates at a frontier node (`09:1277--1281`)

"Every certificate has weight `1` or `1/2`, and at a fixed node there is at most
one descendant of each initial outer coordinate.  Hence the number of
represented coordinates is at least `ceil(W_v)`."

The frozen sentence names a *set* -- the outer coordinates represented at `v` --
and then counts it.  The set is a readout of the routing (`coordRoutes`), never
constructor data, and the count is what the small-capacity fallback of
`09:1283--1290` consumes.  Everything in this section is **general** in the
protocol, the coordinate type, the reference rows and the two frozen numerals. -/

section General

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1280`, "the represented coordinates" at a frontier node.**

The outer coordinates whose routed branch reaches `v`.  By the frozen
`09:1278--1280` -- "at a fixed node there is at most one descendant of each
initial outer coordinate", which the banked `descendants_nodup` licenses -- each
such coordinate contributes exactly one certificate at `v`, so this `Finset` is
also the certificate census at `v`.

**Deliberately carries no weight, kind or bound:** all three are frozen
*consequences* of the route, and carrying them would put a conclusion into
constructor data (mechanical rules M1--M10). -/
def representedCoords (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : Finset Coord :=
  Finset.univ.filter fun i : Coord => v.val ∈ coordRoutes P R A0 r i

/-- **Aux B1.**  Membership readout.  General. -/
@[simp] theorem mem_representedCoords (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) (i : Coord) :
    i ∈ representedCoords P R A0 r v ↔ v.val ∈ coordRoutes P R A0 r i := by
  simp [representedCoords]

/-- **Aux B2 (every frontier node has a donor).**  A node is on the frontier
because some coordinate's routed branch stopped there, so the represented set is
never empty.  General. -/
theorem representedCoords_nonempty (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : (representedCoords P R A0 r v).Nonempty := by
  obtain ⟨i, hi⟩ := exists_coord_of_mem_frontierRoutes v.property
  exact ⟨i, (mem_representedCoords P R A0 r v i).mpr hi⟩

/-- **Aux B3 (the census is bounded by the started coordinates).**  No node can
represent more coordinates than were started (`09:1235--1236`).  General. -/
theorem card_representedCoords_le_card_coord (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode P R A0 r) :
    (representedCoords P R A0 r v).card ≤ Fintype.card Coord := by
  simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ
    (representedCoords P R A0 r v))

/-- **`09:1280--1281`, PROVED from the routing.**

"Hence the number of represented coordinates is at least `ceil(W_v)`."

The estimate itself is the predecessor's Aux A5
(`FirstBobFrontierInstance.frontierWeight_le_card_reaching`), which is the frozen
`09:1277--1280` -- every certificate weighs at most the clean `1`, and each
coordinate contributes at most one certificate at `v`.  What is new here is the
frozen *ceiling*: the count is a natural number, so it dominates `ceil(W_v)` and
not merely `W_v`.  General. -/
theorem ceil_frontierWeight_le_card_representedCoords (P : Protocol X Y Z)
    (R : Coord → Finset X) (A0 r : ℕ) (v : FrontierNode P R A0 r) :
    ⌈frontierWeight P R A0 r v⌉₊ ≤ (representedCoords P R A0 r v).card :=
  Nat.ceil_le.mpr (frontierWeight_le_card_reaching P R A0 r v)

/-- **Aux B4 (the specialization the frozen counting uses).**  When exactly one
outer coordinate reaches `v`, the represented set is a singleton.  General; this
is the census form of the predecessor's `frontierWeight_eq_weight_of_unique_coord`
hypothesis. -/
theorem card_representedCoords_eq_one_of_unique (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode P R A0 r) {i₀ : Coord}
    (h : ∀ i : Coord, v.val ∈ coordRoutes P R A0 r i ↔ i = i₀) :
    (representedCoords P R A0 r v).card = 1 := by
  classical
  have hset : representedCoords P R A0 r v = {i₀} := by
    ext i
    rw [mem_representedCoords, Finset.mem_singleton]
    exact h i
  rw [hset, Finset.card_singleton]

/-- **`09:1283`, the frozen chain, at a first-Bob node of the canonical system.**

"`ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`."

Three pins and no new mathematics: the predecessor's Aux A6
(`firstBob_capacity_dyadic`) puts `kappa_v` in the dyadic form `2^{ell}`,
`ell >= 1`, which is the form `09:1285--1287`'s case split needs; the banked
`DenseWrapperFrontier.smallCopyWidth_le_ceil_weight` is that case split, carrying
`09:1285--1286`'s three immediate cases and `09:1287`'s
`9 kappa_v/16 >= kappa_v/2 + 1` at once against the banked `smallCopyWidth`
(the frozen `u_kappa` of `09:436--441`); and `09:1280--1281` is the theorem
above.  General in `P`, `Coord`, `R`, `A_0`, `r`.

**Deliberate widening past the frozen branch condition, recorded.**  The paper
states `09:1277--1283` inside the branch `2 <= kappa_v < t_ref`; this statement
omits `kappa_v < t_ref` and therefore covers every dyadic `kappa_v >= 2`.  That
is sound and cannot weaken anything: the banked `smallCopyWidth` is a total
function `kappa |-> kappa/2 + 1` agreeing with `09:438--440` on the frozen
domain, and the banked `smallCopyWidth_le_ceil_weight` carries **no** `t_ref`
hypothesis, because `9 kappa/16 >= kappa/2 + 1` holds for every dyadic
`kappa >= 2`.  Dropping a hypothesis only strengthens the conclusion's
availability; no frozen guard is being relaxed on the consuming side, where
`canonical_firstBobLight_smallCapacity` still carries its own `hsmall`. -/
theorem heavy_firstBob_smallCopyWidth_le {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r}
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hheavy : vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)
      ≤ frontierWeight P R A0 r v) :
    smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
      ≤ (representedCoords P R A0 r v).card := by
  obtain ⟨l, hl, hcap⟩ := firstBob_capacity_dyadic (canonicalSystem hcomp hR) hv
  rw [hcap] at hheavy ⊢
  have hcast : (((2 : ℕ) ^ l : ℕ) : ℝ) = (2 : ℝ) ^ l := by push_cast; ring
  rw [hcast] at hheavy
  exact le_trans (smallCopyWidth_le_ceil_weight hl hheavy)
    (ceil_frontierWeight_le_card_representedCoords P R A0 r v)

end General

/-! ## §2  `eq:wrapper-first-bob-light` at the canonical system (`09:1268--1313`)

"Put `vartheta = 9/16`.  We first close any first-Bob node satisfying
`W_v >= vartheta kappa_v` ... Its lower bound is one more bit than the remaining
child budget in the alleged protocol.  Therefore `W_v < vartheta kappa_v` at
every first-Bob node `v`."

The banked `DenseWrapperFrontier.wrapperFirstBobLight` is the frozen
contradiction in the abstract: it takes `W`, `ell` and the closure as free data.
This section instantiates it **at the routing** -- `W_v` is the derived
`frontierWeight`, `ell_v = r - d_v` is the node's derived depth, `kappa_v` is the
derived capacity -- and moves the closure binder from the raw weight condition to
the frozen **cover-entry condition** of `09:1287--1289`, which §1 supplies. -/

section Closure

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) at the canonical routed
system, with the closure named.**

At a first-Bob node of `FrontierIndexing.canonicalSystem` the frozen conclusion
`W_v < vartheta kappa_v` follows from two frozen inputs and nothing else:

* `hbudget` is `09:1306--1308`, the alleged `(C+r-1)`-bit protocol's remaining
  budget below the selected Bob child of a node reached after `d_v` Alice
  queries, stated subtraction-free;
* `hclosure` is the closure of `09:1269--1306`, carried at its **entry
  condition**: once `u_{kappa_v}` outer coordinates are represented at `v`, the
  selected Bob child has complexity at least `C + log_2 kappa_v - 1`.  The
  small-capacity ladder of `09:1296--1306` delivers exactly that; whether the
  large-capacity endpoint call of `09:1269--1276` can be re-expressed at the
  cover-entry condition, or needs `hclosure` stated branch-wise (heavy-
  conditioned for `kappa_v >= t_ref`), is part of GAP-EXPOSED 14.  The frozen
  large branch runs from the heavy condition `W_v >= vartheta kappa_v` directly
  through the certified-scale stopping lemma and mentions neither represented
  coordinates nor `u_kappa`, so it is **not** claimed here to deliver the
  cover-entry form.  Neither branch is proved here (GAP-EXPOSED 14, 15).

What is **not** assumed is the heavy-node hypothesis itself: `09:1283`'s chain
from `W_v >= vartheta kappa_v` to the cover-entry condition is the *proved*
`heavy_firstBob_smallCopyWidth_le`, so the derivation now starts at the routing
rather than at an assumed weight bound.  General in `P`, `Coord`, `R`, `A_0`,
`r`, `C` and the residual budget. -/
theorem canonical_firstBobLight_of_closure {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B : ℕ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hclosure : smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card → C + (r - v.val.length) - 1 ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  have hcap : (canonicalSystem hcomp hR).toWrapperFrontier.capacity v
      = 2 ^ (r - v.val.length) := rfl
  have hcast : (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) = (2 : ℝ) ^ (r - v.val.length) := by
    push_cast; ring
  rw [hcap, hcast]
  refine wrapperFirstBobLight (C := C) (r := r) (d := v.val.length)
    (ℓ := r - v.val.length) (B := B) hC (by omega) (by omega) hbudget ?_
  intro hheavy
  refine hclosure (heavy_firstBob_smallCopyWidth_le hcomp hR hv ?_)
  rw [hcap, hcast]
  exact hheavy

/-- **`eq:wrapper-first-bob-light` on the small-capacity branch
(`09:1277--1313`), assembled.**

At a first-Bob node with `kappa_v < t_ref` -- in exponent form
`ell_v <= k` with `t_ref = 2^k` (`06:569`) -- the closure binder of the
preceding statement is discharged against the banked, already-proved
transcriptions:

* `capacity_row_density_legal` is `09:1302--1304`, "`kappa_v x_T <= t_ref x_T <= 1`
  verifies legality", from the frozen exponent gate `k + 2 <= r`
  (`09:327`, `q/4 >= t_ref`) and `eq:wrapper-low-simple-gate`;
* `smallCapacity_child_bound` is `09:1296--1306`, the
  `Cref{lem:certified-row-ladder}` call at `M = G`, `H = C-1`, `x = x_T`,
  `z = y`, `ell = ell_v`, with `hbase` the second clause of `lem:wrapper-reference`
  (`09:1302`) and `C >= 3` supplying `H >= 2`.

The single remaining binder is `hselect`: the frozen `09:1287--1296` step that
selects `u_{kappa_v}` of the represented coordinates, reads the parent projection
density `rho = 2y^2`, follows the denser Bob child to `y^2`, trims each selected
certificate to row density `kappa_v x_T`, and thereby exhibits the ladder's
certified restriction *inside* the selected Bob child -- so that the child's own
complexity `B` dominates the ladder value.  The column projection at a protocol
node is not modelled, so this step is stated, never proved (GAP-EXPOSED 15).
General in the source carriers, `C`, `k`, `x_T`, `y` and the residual budget.

**Deliberate widening at the branch boundary, recorded.**  `hsmall` is the
non-strict `ell_v <= k`, so it admits `kappa_v = 2^k = t_ref`, which `09:1269`
routes to the *large*-capacity branch.  This cannot weaken the conclusion: the
banked `capacity_row_density_legal` permits `ell = k` and yields
`t_ref x_T <= 1`, which is exactly the legality `09:1304` asserts at the
boundary, and covering one extra capacity only **enlarges** the burden carried
by `hselect`.  The frozen dichotomy is therefore still available to a later
round, which owes the `kappa_v >= t_ref` branch in any case (GAP-EXPOSED 14). -/
theorem canonical_firstBobLight_smallCapacity {Xg Yg : Type*} [Fintype Xg] [Fintype Yg]
    (Gmat : Xg → Yg → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k : ℕ} {xT y : ℝ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hXg : 1 ≤ Fintype.card Xg) (hYg : 1 ≤ Fintype.card Yg) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (hsmall : r - v.val.length ≤ k) (hq4 : k + 2 ≤ r)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hselect : smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card →
        LambdaGE Gmat (2 ^ (r - v.val.length - 1) + 1)
          ((2 : ℝ) ^ (r - v.val.length) * xT) (y ^ 2) ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  refine canonical_firstBobLight_of_closure hcomp hR hv hC hbudget ?_
  intro hcover
  have hlegal : ((2 : ℝ) ^ (r - v.val.length)) * xT ≤ 1 :=
    capacity_row_density_legal (le_of_lt hxT0) hsmall hq4 hgate
  have hladder := smallCapacity_child_bound Gmat (ℓ := r - v.val.length) hXg hYg hC hxT0 hy0 hy1
    hbase (by omega) hlegal
  exact le_trans hladder (hselect hcover)

/-- **Hypothesis consistency for `canonical_firstBobLight_smallCapacity`: the
arithmetic and gate binders are jointly satisfiable, and the closure fires.**

**BEYOND-PAPER AUDIT**, per the module header, and this declaration is **not**
covered by §3's blanket label -- it sits in §2 and carries its own.  `r` is
DEFINED by `06:515` (`q = 2^{A_wrap L_P^2}`) with `09:105` (`q = 2^r`), `k` is
DEFINED as `k_ref` by `06:558--569` (`t_ref = 2^{k_ref}`, the least integer
meeting `eq:tref-search`), and `C` is DEFINED by the wrapper schedule.  The
numerals `r = 6`, `k = 4`, `C = 3`, `B = 5`, `d_v = 2` are **ours**: they audit
*our encoding* of the gate interaction at a point the paper never visits, and are
strictly weaker evidence than the paper's own application point.  Nothing here
claims those numerals are legal values of the schedule.

**Coverage, stated precisely.**  What is checked below is the **arithmetic and
gate** binders -- `hxT0`, `hgate`, `hsmall`, `hq4`, `hbudget`, `1 <= ell_v` --
which are jointly satisfiable at those numerals, with `x_T` taken as the banked
closed-form accessor `WrapperLowRungs.wrapperLowRungGates_legal_instance` at
`(k, r) = (4, 6)` rather than as a numeral.  The **analytic** binders `hbase`,
`hy0`, `hy1`, `hXg`, `hYg` are inherited unchanged from the banked
`smallCapacity_child_bound`'s own legal instance and are **not** instantiated
jointly with the arithmetic ones here, even though `hbase` shares `x_T`, `y` and
`C` with them: no `Gmat` is exhibited at the pinned `x_T` satisfying
`C - 1 <= LambdaGE Gmat 1 x_T y`.  So full-bundle satisfiability is *inferred
from the two groups*, not exhibited; a joint instance would additionally need the
unmodelled `hselect` (GAP-EXPOSED 15).

The arithmetic bundle is consistent -- every clause below holds -- and it is
**not** consistent
with the closure's own output: `C + ell_v - 1 = 6 > 5 = B`, so the frozen
contradiction of `09:1306--1308` genuinely fires once `hselect`'s antecedent is
met.  Note also that the gates force `d_v >= 2`: `ell_v <= k` and `k + 2 <= r`
give `ell_v <= r - 2`, so the small-capacity branch never applies at the shallow
first-Bob nodes of §3's `r = 2` instance -- which is why §3 audits
`canonical_firstBobLight_of_closure` and not this theorem. -/
theorem smallCapacity_binders_consistent :
    (0 : ℝ) < 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ ((2 : ℝ) ^ 6) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025
      ∧ (6 - 2 : ℕ) ≤ 4
      ∧ (4 : ℕ) + 2 ≤ 6
      ∧ (5 : ℕ) + (2 + 1) ≤ 3 + 6 - 1
      ∧ 1 ≤ (6 - 2 : ℕ)
      ∧ ¬ ((3 : ℕ) + (6 - 2) - 1 ≤ 5) := by
  obtain ⟨-, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  refine ⟨hpos, ?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [hval]
  norm_num

end Closure

/-! ## §3  The live split first-Bob instance (BEYOND-PAPER AUDIT, `r = 2`)

Everything in this section is an audit of *our encoding* at self-chosen numerals.
See the module header for the mandatory BEYOND-PAPER label, for which quantities
are DEFINED by the frozen source (`r`, `A_0`, `e_0`) and therefore not
legitimately assigned, and for why `e_0 = 2` is forced here. -/

section SplitInstance

/-- **The frozen initial placement of `09:1233--1236` at the audit instance.**

Two started outer coordinates, each holding all
`A_r = refRowFloor A_0 r = 2^2 . 1 = 4` retained reference rows demanded by
`09:1234--1235` ("that coordinate would therefore retain at least `A_r = q A_0`
reference rows").  Four is not a chosen number: it is `09:1221`'s `A_k = 2^k A_0`
evaluated through the banked `refRowFloor`.

Coordinate `0` **straddles** the predecessor's root Alice predicate
`FirstBobFrontierInstance.rootPred` (`8 <= x`): two of its rows fall on each
side, so `09:1244`'s "route it to both children if both qualify" fires.
Coordinate `1` lies entirely below both predicates and routes uniquely.

**BEYOND-PAPER label.**  Which rows each coordinate holds is ours; the frozen
text fixes no alphabet and no placement beyond the cardinality floor. -/
def splitRows : Fin 2 → Finset (Fin 12) :=
  ![Finset.univ.filter (fun x => 6 ≤ x.val ∧ x.val < 10),
    Finset.univ.filter (fun x => x.val < 4)]

/-- **`09:1233--1235` at the audit instance.**  Both started coordinates hold all
`A_r = 2^2 . 1 = 4` retained reference rows, so the frozen retention holds with
equality.  Stated through the banked `refRowFloor`, so the numeral `4` appears in
no hypothesis. -/
theorem split_hR : ∀ i : Fin 2, refRowFloor 1 2 ≤ (splitRows i).card := by decide

/-- **The canonical routed certificate system at the audit instance.**

This is `FrontierIndexing.canonicalSystem` itself, at its own two frozen inputs:
`FirstBobFrontierInstance.live_hcomp`, the frame condition of
`lem:wrapper-no-bob-completion` (`09:1195--1200`), reused **by pin** because
`CompletedNoBob` does not mention the reference rows; and `split_hR`, the
retention of `09:1233--1235`.  Nothing about the system is chosen here. -/
abbrev splitSystem :
    RoutedSystem liveProtocol (Fin 2) (CertIndex liveProtocol splitRows 1 2)
      (FrontierNode liveProtocol splitRows 1 2) 2 1 :=
  canonicalSystem live_hcomp split_hR

/-! ### The routing, computed

Each started coordinate is routed by the frozen rule of `09:1238--1248`, and
where it stops is a **computed output**. -/

/-- **`09:1244` fires at the root: the frozen branching clause, live.**

"route it to both children if both qualify": at the root, coordinate `0` holds
two rows on each side of the Alice predicate, and the qualification threshold
there is `childFloor A_0 r [] = A_{r-1} = 2`, met by both.  This is the clause the
predecessor's instance never exercised. -/
theorem split_splitsAt_root :
    splitsAt liveProtocol (splitRows 0) 1 2 ([] : List Bool) = true := by decide

/-- **`09:1238--1252` at coordinate `0`.**  The split sends one half down the
`false` side, where it is routed uniquely to the final Alice node `[false, true]`,
and the other half down the `true` side, where the *first* frozen stopping rule
stops it at the exposed Bob query of depth `1`. -/
theorem split_descendants_zero :
    descendants liveProtocol (splitRows 0) 1 2 2 ([] : List Bool) = [[false, true], [true]] := by
  decide

/-- **`09:1238--1252` at coordinate `1`.**  A unique route to the final Alice node
`[false, false]`; no qualification is ever two-sided along it. -/
theorem split_descendants_one :
    descendants liveProtocol (splitRows 1) 1 2 2 ([] : List Bool) = [[false, false]] := by decide

/-- **The frontier of the audit instance, computed.**  Three nodes: two final
Alice nodes at depth `2` and one exposed first-Bob node at depth `1`. -/
theorem split_frontierRoutes :
    frontierRoutes liveProtocol splitRows 1 2
      = ({[false, false], [false, true], [true]} : Finset (List Bool)) := by decide

/-- The exposed first-Bob node of the audit instance (`09:1250--1251`), reached by
the `true` half of the split certificate. -/
def splitBobNode : FrontierNode liveProtocol splitRows 1 2 := ⟨[true], by decide⟩

/-- The final Alice node reached by the `false` half of the split certificate
(`09:1252`); this is the node that populates the frozen `ell` column. -/
def splitLowFinalNode : FrontierNode liveProtocol splitRows 1 2 := ⟨[false, true], by decide⟩

/-- The final Alice node reached by the unsplit coordinate `1` (`09:1252`); this
is the node that populates the frozen `c` column. -/
def splitCleanFinalNode : FrontierNode liveProtocol splitRows 1 2 := ⟨[false, false], by decide⟩

/-- **`09:1250--1251`, live.**  The first-Bob set is the singleton `{[true]}`. -/
theorem split_bobNodes : splitSystem.toWrapperFrontier.bobNodes = {splitBobNode} := by decide

/-- **`09:1252`, live.**  The final Alice nodes are the two depth-`2` addresses. -/
theorem split_finalNodes :
    splitSystem.toWrapperFrontier.finalNodes = {splitCleanFinalNode, splitLowFinalNode} := by
  decide

/-- **`09:1255` evaluated, `09:1259` ATTAINED.**  `kappa_v = 2^{2-1} = 2`, so the
frozen floor "Every first-Bob node has `kappa_v >= 2`" holds with equality. -/
theorem split_kappa_attained : splitSystem.toWrapperFrontier.capacity splitBobNode = 2 := by
  decide

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), attained.**
`sum_v kappa_v = 2 + 1 + 1 = 4 = q`: Kraft is met with **equality**, so the audit
instance sits on the frozen boundary rather than in a slack corner. -/
theorem split_kraft_tight :
    ∑ v : FrontierNode liveProtocol splitRows 1 2,
        splitSystem.toWrapperFrontier.capacity v = 2 ^ 2 := by decide

/-! ### The kinds and the weights, computed

Coordinate `0` splits at the root, so by `09:1245--1246` **both** its descendants
are `low` of weight `1/2`; coordinate `1` never splits, so by `09:1244--1245` its
descendant stays `clean` of weight `1`.  Each `W_v` is obtained by *evaluating*
`frontierWeight` through the predecessor's Aux A2, never assigned. -/

/-- **`09:1278--1280` at the live first-Bob node.**  Exactly one coordinate
reaches it. -/
theorem split_bobNode_unique_coord :
    ∀ i : Fin 2, splitBobNode.val ∈ coordRoutes liveProtocol splitRows 1 2 i ↔ i = 0 := by decide

/-- **`09:1278--1280` at the half-weight final node.** -/
theorem split_lowFinalNode_unique_coord :
    ∀ i : Fin 2, splitLowFinalNode.val ∈ coordRoutes liveProtocol splitRows 1 2 i ↔ i = 0 := by
  decide

/-- **`09:1278--1280` at the clean final node.** -/
theorem split_cleanFinalNode_unique_coord :
    ∀ i : Fin 2, splitCleanFinalNode.val ∈ coordRoutes liveProtocol splitRows 1 2 i ↔ i = 1 := by
  decide

/-- **`09:1245--1246` at the live first-Bob node.**  "When a clean certificate splits,
both descendants become low certificates of weight `1/2`": the derived kind at
the exposed Bob query is `low`. -/
theorem split_bobNode_kind :
    kindAlong liveProtocol (splitRows 0) 1 2 splitBobNode.val = CertKind.low := by decide

/-- **`09:1246--1247` at the half-weight final node.**  "A low certificate keeps
weight `1/2`": the other half of the same split is still `low` two levels down. -/
theorem split_lowFinalNode_kind :
    kindAlong liveProtocol (splitRows 0) 1 2 splitLowFinalNode.val = CertKind.low := by decide

/-- **`09:1244--1245` at the clean final node.**  "A clean certificate routed uniquely
stays clean with weight one." -/
theorem split_cleanFinalNode_kind :
    kindAlong liveProtocol (splitRows 1) 1 2 splitCleanFinalNode.val = CertKind.clean := by decide

/-- **`09:1257` evaluated at the live first-Bob node.**  `W_v = 1/2` -- a
**half-weight** descendant of a split certificate, where the predecessor's
instance had a clean `W_v = 1`. -/
theorem split_frontierWeight_bobNode :
    frontierWeight liveProtocol splitRows 1 2 splitBobNode = 1 / 2 := by
  rw [frontierWeight_eq_weight_of_unique_coord liveProtocol splitRows 1 2 splitBobNode
      split_bobNode_unique_coord, split_bobNode_kind]
  norm_num [CertKind.weight]

/-- **`09:1257` evaluated at the half-weight final node.**  `W_v = 1/2`. -/
theorem split_frontierWeight_lowFinalNode :
    frontierWeight liveProtocol splitRows 1 2 splitLowFinalNode = 1 / 2 := by
  rw [frontierWeight_eq_weight_of_unique_coord liveProtocol splitRows 1 2 splitLowFinalNode
      split_lowFinalNode_unique_coord, split_lowFinalNode_kind]
  norm_num [CertKind.weight]

/-- **`09:1257` evaluated at the clean final node.**  `W_v = 1`. -/
theorem split_frontierWeight_cleanFinalNode :
    frontierWeight liveProtocol splitRows 1 2 splitCleanFinalNode = 1 := by
  rw [frontierWeight_eq_weight_of_unique_coord liveProtocol splitRows 1 2 splitCleanFinalNode
      split_cleanFinalNode_unique_coord, split_cleanFinalNode_kind]
  norm_num [CertKind.weight]

/-! ### The final-node classification of `09:1346--1350`, supplied live -/

/-- **`09:1346--1350`, the frozen trichotomy read off the computed routing.**

"Thus every final Alice node contains either one clean certificate, one
half-weight descendant of a split certificate, or none."  Each address of the
computed frontier is labelled by the kind the routing actually put there;
`splitCertOpt_matches_kinds` verifies the labelling against `kindAlong` at all
three nodes, so this is a *readout* of the routing rather than an assignment. -/
def splitCertLabel : List Bool → Option CertKind
  | [false, false] => some CertKind.clean
  | [false, true] => some CertKind.low
  | [true] => some CertKind.low
  | _ => none

/-- The frozen `09:1346--1350` classification as the banked
`canonical_cleanCount` consumes it. -/
def splitCertOpt (v : FrontierNode liveProtocol splitRows 1 2) : Option CertKind :=
  splitCertLabel v.val

/-- **The classification is the routing's own output.**  At each of the three
frontier nodes the label agrees with the derived `kindAlong` of the unique
coordinate that reaches it, so no kind is assigned by hand. -/
theorem splitCertOpt_matches_kinds :
    splitCertOpt splitCleanFinalNode
        = some (kindAlong liveProtocol (splitRows 1) 1 2 splitCleanFinalNode.val)
      ∧ splitCertOpt splitLowFinalNode
        = some (kindAlong liveProtocol (splitRows 0) 1 2 splitLowFinalNode.val)
      ∧ splitCertOpt splitBobNode
        = some (kindAlong liveProtocol (splitRows 0) 1 2 splitBobNode.val) := by decide

/-- **`lem:final-reference-uniqueness` (`09:1315--1319`) is RESPECTED here.**

"Every final Alice-frontier node ... contains at most one reference certificate,
whether clean or split."  Each final node of the audit instance is reached by
exactly one outer coordinate, so it carries exactly one certificate; the
instance therefore exhibits a shape the frozen lemma permits, rather than one it
refutes.  (The lemma itself is **not** discharged here; this is the check that
the audit instance is not built against it.) -/
theorem split_finalNodes_single_certificate :
    (representedCoords liveProtocol splitRows 1 2 splitCleanFinalNode).card = 1
      ∧ (representedCoords liveProtocol splitRows 1 2 splitLowFinalNode).card = 1 :=
  ⟨card_representedCoords_eq_one_of_unique liveProtocol splitRows 1 2 splitCleanFinalNode
      split_cleanFinalNode_unique_coord,
    card_representedCoords_eq_one_of_unique liveProtocol splitRows 1 2 splitLowFinalNode
      split_lowFinalNode_unique_coord⟩

/-! ### The two binders of `canonical_cleanCount`, supplied live -/

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) at the audit instance,
exercised on a HALF-WEIGHT descendant.**

`W_v = 1/2 <= vartheta . kappa_v = (9/16) . 2 = 9/8` at the single first-Bob
node, which is reached by the `true` half of the certificate that split at the
root.  This is what the predecessor's GAP item (13) asked for: `09:1244`'s
branching clause and the light bound exercised **at the same node**.

**On the relation `<=` versus `<`.**  The frozen display is the strict
`W_v < vartheta kappa_v`; the banked `wrapperCleanCount`, and with it
`canonical_cleanCount`, consumes the weaker non-strict binder, which is what this
statement matches at that interface.  The strict frozen form holds here too and
is recorded separately by `split_hlight_is_exercised_at_half_weight`.

**This supplies the binder at one audit instance; it does not discharge
`eq:wrapper-first-bob-light` in general** -- for that, see §2. -/
theorem split_hlight :
    ∀ v ∈ splitSystem.toWrapperFrontier.bobNodes,
      frontierWeight liveProtocol splitRows 1 2 v
        ≤ vartheta * ((splitSystem.toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  intro v hv
  rw [split_bobNodes, Finset.mem_singleton] at hv
  subst hv
  rw [split_frontierWeight_bobNode, split_kappa_attained]
  norm_num [vartheta]

/-- **The final-node classification of `09:1346--1350` at the audit instance.**

Both final Alice nodes carry exactly one certificate, and the classification
records its computed kind, so `W_v = finalWeight (certOpt v)` holds with
**equality** at both: `1 = finalWeight (some clean)` at the clean node and
`1/2 = finalWeight (some low)` at the half-weight node.

**This supplies the binder at one audit instance; it does not discharge
`lem:final-reference-uniqueness` in general.** -/
theorem split_hfinal :
    ∀ v ∈ splitSystem.toWrapperFrontier.finalNodes,
      frontierWeight liveProtocol splitRows 1 2 v ≤ finalWeight (splitCertOpt v) := by
  intro v hv
  rw [split_finalNodes] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · rw [split_frontierWeight_cleanFinalNode]
    norm_num [splitCertOpt, splitCertLabel, splitCleanFinalNode, finalWeight, CertKind.weight]
  · rw [split_frontierWeight_lowFinalNode]
    norm_num [splitCertOpt, splitCertLabel, splitLowFinalNode, finalWeight, CertKind.weight]

/-! ### `eq:wrapper-clean-count` re-run at the split instance -/

/-- **`09:1347--1348`, `K_B`, at the audit instance.**  `K_B = kappa_v = 2`. -/
theorem split_bobCapacity : splitSystem.toWrapperFrontier.bobCapacity = 2 := by
  rw [WrapperFrontier.bobCapacity, split_bobNodes, Finset.sum_singleton, split_kappa_attained]
  norm_num

/-- **`09:1348--1349`, `c`, at the audit instance.** -/
theorem split_cleanNodes_card :
    (splitSystem.toWrapperFrontier.cleanNodes splitCertOpt).card = 1 := by decide

/-- **`09:1349--1350`, `ell`, at the audit instance: the half-weight column is
NONEMPTY.**

`ell = 1`, where the predecessor's instance had `ell = 0`
(`FirstBobFrontierInstance.live_splitNodes_card`).  This is the second half of
what GAP item (13) asked for. -/
theorem split_splitNodes_card :
    (splitSystem.toWrapperFrontier.splitNodes splitCertOpt).card = 1 := by decide

/-- **The frozen `ell` column of `09:1349--1350` is inhabited.** -/
theorem split_splitNodes_nonempty :
    (splitSystem.toWrapperFrontier.splitNodes splitCertOpt).Nonempty := by
  rw [← Finset.card_pos, split_splitNodes_card]
  norm_num

/-- **`eq:wrapper-clean-count` (`09:1352--1357`) re-run at the split instance.**

The banked `FrontierIndexing.canonical_cleanCount` -- itself the banked
`DenseWrapperFrontier.wrapperCleanCount` with the conservation binder already
retired -- applied verbatim at its own interface, with `q = 4` **derived** from
`09:105` at `r = 2` and with the forced `e_0 = 2` (see the module header).  Both
remaining binders are supplied live, `hlight` at a first-Bob node carrying a
half-weight descendant and `hfinal` at two verified final nodes; the frozen
coordinate count `hcoord` of `09:1235--1236` holds with equality,
`q - e_0 = 2 = card(Coord)`.

**BEYOND-PAPER AUDIT**, per the module header.  At `e_0 = 2` the first conjunct
is the degenerate one the predecessor's pole already identified; the **second**
conjunct is the live one here, and it is the conjunct the half-weight column
feeds. -/
theorem split_cleanCount :
    (4 : ℝ) - 2 / (1 - vartheta)
        ≤ ((splitSystem.toWrapperFrontier.cleanNodes splitCertOpt).card : ℝ)
      ∧ splitSystem.toWrapperFrontier.bobCapacity
          + ((splitSystem.toWrapperFrontier.splitNodes splitCertOpt).card : ℝ)
        ≤ 2 / (1 - vartheta) :=
  canonical_cleanCount live_hcomp split_hR splitCertOpt
    (q := 4) (e0 := 2) (by norm_num) (by norm_num [Fintype.card_fin]) split_hlight split_hfinal

/-- **The second conjunct of `eq:wrapper-clean-count` is LIVE at the split
instance, and the half-weight column is what enters it.**

`K_B + ell = 2 + 1 = 3 <= e_0/(1-vartheta) = 32/7`, with `K_B = 2 > 0` because the
first-Bob set is nonempty and `ell = 1 > 0` because the half-weight column is.
Both summands are strictly positive, so the frozen bound is checked against a
genuine quantity rather than against zero. -/
theorem split_cleanCount_second_conjunct_is_live :
    (0 : ℝ) < splitSystem.toWrapperFrontier.bobCapacity
      ∧ (0 : ℝ) < ((splitSystem.toWrapperFrontier.splitNodes splitCertOpt).card : ℝ)
      ∧ splitSystem.toWrapperFrontier.bobCapacity
          + ((splitSystem.toWrapperFrontier.splitNodes splitCertOpt).card : ℝ)
        ≤ 2 / (1 - vartheta) := by
  refine ⟨?_, ?_, split_cleanCount.2⟩
  · rw [split_bobCapacity]; norm_num
  · rw [split_splitNodes_card]; norm_num

/-- **The frozen headline of this tranche: a SPLIT certificate's half-weight
descendant reaches an exposed first-Bob node, and the light bound is exercised
there.**

All six clauses are computed from the frozen rule, not chosen: the root
qualification is two-sided (`09:1244`), the first-Bob address is reached by the
splitting coordinate, its derived kind is `low` (`09:1245--1246`), it really is an
exposed first-Bob node in the frozen sense (`09:1250--1251`), its weight is the
half-weight `1/2` (`09:1257`), and `eq:wrapper-first-bob-light` holds there in its
**strict** frozen form.

**BEYOND-PAPER AUDIT**, per the module header. -/
theorem split_halfWeight_reaches_firstBob :
    splitsAt liveProtocol (splitRows 0) 1 2 ([] : List Bool) = true
      ∧ splitBobNode.val ∈ coordRoutes liveProtocol splitRows 1 2 0
      ∧ kindAlong liveProtocol (splitRows 0) 1 2 splitBobNode.val = CertKind.low
      ∧ IsFirstBobNode liveProtocol 2 splitBobNode.val
      ∧ frontierWeight liveProtocol splitRows 1 2 splitBobNode = 1 / 2
      ∧ frontierWeight liveProtocol splitRows 1 2 splitBobNode
          < vartheta * ((splitSystem.toWrapperFrontier.capacity splitBobNode : ℕ) : ℝ) := by
  refine ⟨split_splitsAt_root, (split_bobNode_unique_coord 0).mpr rfl, split_bobNode_kind,
    splitSystem.firstBob_spec splitBobNode (by decide), split_frontierWeight_bobNode, ?_⟩
  rw [split_frontierWeight_bobNode, split_kappa_attained]
  norm_num [vartheta]

/-- **Hypothesis consistency for `canonical_firstBobLight_of_closure` at the
split instance.**

The §2 theorem's full binder bundle -- the two frozen construction inputs, the
first-Bob flag, `C >= 3`, the remaining child budget of `09:1306--1308`, and the
closure of `09:1269--1306` at its cover-entry condition -- is **jointly
satisfiable, and the conclusion follows rather than `False`**, at the live split
instance with the frozen minimum `C = 3` and a residual budget `B = 0`.

`hclosure` holds because its antecedent **fails** here: the node is light, one
coordinate is represented, and `u_2 = 2 > 1`.  That is the honest reading -- the
closure is not invoked at a light node -- and it is precisely why
`firstBobLight_closure_antecedent_is_not_automatic` is recorded below.

**BEYOND-PAPER AUDIT**, per the module header. -/
theorem split_firstBobLight_from_closure :
    frontierWeight liveProtocol splitRows 1 2 splitBobNode
      < vartheta * ((splitSystem.toWrapperFrontier.capacity splitBobNode : ℕ) : ℝ) :=
  canonical_firstBobLight_of_closure live_hcomp split_hR (C := 3) (B := 0)
    (by decide) (by norm_num) (by decide) (fun h => absurd h (by decide))

end SplitInstance

/-! ## §4  Statement poles

A green build sees none of this. -/

section Poles

/-- **Statement pole: the light bound is exercised at a half-weight descendant,
not at a clean certificate.**

The predecessor checked `eq:wrapper-first-bob-light` at a node carrying a *clean*
certificate (`W_v = 1`); here the same bound is checked at a node carrying the
`true` half of a split (`W_v = 1/2`, derived kind `low`), with `kappa_v` attaining
the frozen floor `2`.  The three facts together are what GAP item (13) asked for,
and the strict frozen form of `09:1310` is what holds. -/
theorem split_hlight_is_exercised_at_half_weight :
    kindAlong liveProtocol (splitRows 0) 1 2 splitBobNode.val = CertKind.low
      ∧ frontierWeight liveProtocol splitRows 1 2 splitBobNode = 1 / 2
      ∧ splitSystem.toWrapperFrontier.capacity splitBobNode = 2
      ∧ frontierWeight liveProtocol splitRows 1 2 splitBobNode
          < vartheta * ((splitSystem.toWrapperFrontier.capacity splitBobNode : ℕ) : ℝ) := by
  refine ⟨split_bobNode_kind, split_frontierWeight_bobNode, split_kappa_attained, ?_⟩
  rw [split_frontierWeight_bobNode, split_kappa_attained]
  norm_num [vartheta]

/-- **Statement pole: the closure binder of §2 is not discharged by a vacuous
antecedent.**

`canonical_firstBobLight_of_closure` would be worthless if its cover-entry
condition `u_{kappa_v} <= #represented` always held, because then `hclosure`
would carry the whole conclusion.  At the live instance the antecedent **fails**:
`u_2 = 2` is the frozen small-copy width of `09:438`, one coordinate is
represented at the first-Bob node, and `2 > 1`.  So the entry condition is a real
gate, and the frozen `09:1283` chain that produces it from `W_v >= vartheta
kappa_v` is doing work rather than restating the hypothesis. -/
theorem firstBobLight_closure_antecedent_is_not_automatic :
    smallCopyWidth 2 = 2
      ∧ (representedCoords liveProtocol splitRows 1 2 splitBobNode).card = 1
      ∧ ¬ (smallCopyWidth (splitSystem.toWrapperFrontier.capacity splitBobNode)
            ≤ (representedCoords liveProtocol splitRows 1 2 splitBobNode).card) := by
  refine ⟨smallCopyWidth_two, ?_, by decide⟩
  exact card_representedCoords_eq_one_of_unique liveProtocol splitRows 1 2 splitBobNode
    split_bobNode_unique_coord

/-- **Statement pole: the second conjunct of `eq:wrapper-clean-count` genuinely
constrains the half-weight column.**

At the audit instance `K_B + ell = 3 <= e_0/(1-vartheta) = 32/7`.  Had the same
frontier carried `ell = 3` half-weight final nodes, the frozen bound would read
`5 <= 32/7` and **fail**.  So the conclusion the nonempty `ell` column feeds is
not automatically true, and exhibiting `ell > 0` is not exhibiting slack. -/
theorem split_cleanCount_second_conjunct_constrains_ell :
    (2 : ℝ) + 1 ≤ 2 / (1 - vartheta) ∧ ¬ ((2 : ℝ) + 3 ≤ 2 / (1 - vartheta)) := by
  constructor <;> norm_num [vartheta]

/-- **Statement pole: the `e_0 = 2` cost of a nonempty half-weight column is
arithmetic, not a choice of rows.**

The first conjunct of `eq:wrapper-clean-count` is informative only when its
left-hand side is positive, i.e. `q - e_0/(1-vartheta) > 0`, which at `q = 4`
means `e_0 < 7/4` and hence `e_0 <= 1`.  The frozen coordinate count `hcoord` of
`09:1235--1236` then demands `card Coord >= q - e_0 >= 3` started coordinates,
while the audit instance has `card Coord = 2` -- forced, as the module header
records, by `lem:final-reference-uniqueness` together with the light bound at
the exposed Bob node.  So at `r = 2` one may have the first conjunct live
(the predecessor's instance, `ell = 0`) or the half-weight column nonempty (this
one), never both; the trade-off is recorded rather than hidden.

**Exactly what the three clauses below prove, stated without over-claim.**  Only
the **first** clause carries the argument above: it is the implication
`0 < 4 - e_0/(1-vartheta) -> e_0 < 7/4`, i.e. the informativeness threshold,
proved for *every* real `e_0`.  The second and third clauses record the audit
instance's **own** numbers -- its coordinate demand `q - e_0 = 4 - 2 = 2` and its
actual `card Coord = 2`, both strictly below the `3` that an informative first
conjunct would require.  They do **not** formalize the quantified step
"`e_0 <= 1` forces `card Coord >= 4 - e_0 >= 3 > 2`"; that step is argued in this
docstring and is *not* discharged by the middle clause, which is the arithmetic
`2 < 3` at the instance's own `e_0 = 2`.  Strengthening the middle clause to the
quantified form -- e.g. `forall e0 : R, e0 < 7/4 -> (card Coord : R) < 4 - e0` --
is a **statement** change and therefore belongs to a fresh judged round, not to a
record repair; it is registered as GAP-EXPOSED 17.  Nothing else in the module
consumes this pole, so the shortfall is confined to this declaration. -/
theorem split_cleanCount_tradeoff_is_forced :
    (∀ e0 : ℝ, 0 < 4 - e0 / (1 - vartheta) → e0 < 7 / 4)
      ∧ (4 : ℝ) - 2 < 3
      ∧ Fintype.card (Fin 2) = 2 := by
  refine ⟨fun e0 h => ?_, by norm_num, by norm_num⟩
  rw [one_sub_vartheta] at h
  linarith

end Poles

end EthInapproximability.ParameterizedNP.SplitFirstBobInstance
