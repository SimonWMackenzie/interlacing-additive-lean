import EthInapproximability.ParameterizedNP.TerminalStageThreeLift
import EthInapproximability.ParameterizedNP.RoutingDynamics

/-!
# Parameterized NP route: the protocol-side routing of the terminal proof

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  72,008 bytes, recomputed first-hand this round).  The tranche traces the
  **protocol-side** sentences of `lem:terminal-two-stream`'s proof, which the two
  predecessor modules record as *not declared*:
  * `09:928--935` -- the Stage-2 support ladder display and the split-or-route
    rule: "An unattached token follows a child retaining at least half of its
    support.  For an attached pair, choose a heavier child separately for its two
    labelled fibres.  If the choices agree, route the pair together.  If they
    differ, split it into two ordinary tokens in incomparable children.  Every
    descendant therefore has support at least `lambda_{d+1}`."
  * `09:937--951` -- the Stage-2 stopping rule and coordinate isolation: "Put
    `r_2 = log_2 q_2`.  Stop a token at the first Alice query or when its Stage-2
    coordinate is isolated", the ladder floor `lambda_d >= lambda_{r_2} =
    2^{1-b_1}`, the two residual certificates ("one-copy robustness gives
    residual complexity `B_cap`"; "an unsplit attached pair there has residual
    complexity `B_cap + 1` by the inherited top two-copy rung"), and "no routed
    token can end at a protocol leaf at a depth at most `r_2`".
  * `09:953--965` -- the isolation node, `kappa_v = 2^{r_2-d_v}`, and the frozen
    capacity-one exclusion ("if `kappa_v = 1`, then `d_v = r_2`, while `P_2` has
    at most `D_2 - r_2 = B_cap` bits remaining, contradicting the pair's residual
    complexity `B_cap + 1`").
  * `09:1004--1019` -- the Alice child selection ("Following the denser Alice
    child leaves typed density at least `49/128 > 9/25`") and the **Localized
    Extension invocation**: "If `kappa_v >= t_2`, select `9 kappa_v/16` ordinary
    coordinates, trim each to support `kappa_v 2^{-b_1}`, and invoke Localized
    Extension at the fixed physical width `t_2`.  This is exactly call (ii) in
    `sec:extension-call-ledger`."
  * `09:1023--1028` -- "In every case one Alice child has complexity at least
    `B_cap + log_2 kappa_v`, which exceeds `eq:terminal-stage2-budget`."
  * `09:1055--1067` -- the **Stage-3** split-or-route rule, including the
    routing-validity sentence: "If, say, `P_0` has density below `tau_{d+1}`,
    route the whole object to child one using `P setminus P_0`.  This is a valid
    support in child one because every parent pair absent from `P_1` belongs to
    `P_0`."
  * `09:1068--1073` -- "an attached object that remains unsplit loses strictly
    less than `sum_{d >= 0} tau_{d+1} = tau_0` of its typed physical support."
  * `09:1084--1095` -- the Stage-3 stopping rule ("Stop each routed object
    immediately before its first Bob query or when its Stage-3 outer block is
    isolated"), the column density `1 - eps > 4/5 > 3/5`, the row floor
    `tau_d >= tau_{r_3} = 2 x_T`, and "no ordinary object can stop at a protocol
    leaf by depth `r_3`".
  * `09:1107--1110` -- the Stage-3 premature-depth exclusion.
  * `09:1125--1128` -- the **Bob child selection**: "Bob's query does not change
    the row supports.  Follow a child whose quotient projection of
    `K_{ord}` has at least half its current size", with
    `eq:terminal-bob-child-density` at `09:1129--1132`.
* **Cross-anchors opened first-hand for this tranche:** `09:916--927` (the
  transposed fixed-bin frame, the party assignment and the token placement),
  `09:967--978` (the Stage-2 premature-leaf exclusion), `09:980--1002`
  (`eq:terminal-first-alice` and `eq:terminal-stage2-budget`), `09:1035--1054`
  (the Stage-3 frame, the baseline bins and the `tau_d` display), `08:946--1012`
  (`lem:dense-no-leaf` and `eq:isolation-capacity`, the abstract lemmas the
  terminal paragraphs instantiate), and `08:880--935` (the Stage-4 routing rule
  whose `BobRouting` transcription is consumed here by pin).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively; the two imports are `TerminalStageThreeLift`
  and `RoutingDynamics`, whose ledger rows record the same exclusion.  No axiom,
  no opaque conclusion-bearing certificate, and no compiler-trusted decision
  procedure: every closed evaluation below goes through the kernel.

## What this tranche closes, and in which banked row

`TerminalFixedBin.lean`'s **GAP-EXPOSED 2** ("the protocol-side routing") and
`TerminalStageThreeLift.lean`'s **GAP-EXPOSED 3** ("the Stage-3 protocol-side
routing ... is not modelled") name the same object from the two phases.  This
module lands it, and the arithmetic and counting phases both rows already banked
are consumed by pin and never restated.

**Landed.**

1. **The heavier child (`09:931`, `09:1055--1058`).**  The frozen "follows a
   child retaining at least half of its support" is a *derived* selector
   `heavierChild` on the banked `DenseRoutingInvariant.BobRouting`, not an
   existential: `card_le_two_mul_heavierChild` proves the frozen retention from
   the record's own `assigns` field ("their union contains the parent support, so
   such a child always exists"), and `heavierChild_floor_step` is the frozen
   "every descendant therefore has support at least `lambda_{d+1}`" through the
   banked `routingFloor_succ_le_of_two_mul`.
2. **The attached-pair rule (`09:932--935`), derived into the banked arrival
   type.**  `pairArrival` computes, from the two labelled fibres' own heavier
   bits, exactly the banked `DenseFrontierConservation.FrontierArrival` the
   weighted counting consumes: `unsplit` when the choices agree, `split` when they
   differ.  `pairArrival_split_addresses_ne` **discharges** the banked
   `FrontierArrival.hContrib_le_one` premise `hpair`, which
   `DenseFrontierConservation` deliberately left as a named hypothesis
   ("the frozen 'two incomparable children' of `08:934--935` is deliberately not a
   field ... carried as the named hypothesis `hpair`"), and
   `pair_split_addresses_incomparable` is the frozen *incomparability* itself,
   from the banked `routeChildren_incomparable`.
3. **The Stage-2 stopping rule (`09:937--951`, `09:967--978`).**
   `stage2_routed_token_frontier` instantiates the banked `lem:dense-no-leaf` at
   the terminal Stage-2 budget `D_2 = B_cap + log_2 q_2`, with the frozen
   one-copy residual certificate gated on the routing floor at the node and at
   the length-`(r_2+1)` prefix -- the two mutually exclusive gates the banked
   lemma states, never conjoined.
4. **The residual certificate of an unsplit attached pair (`09:948--965`),
   protocol-side.**  `stage2_unsplit_pair_depth_lt` derives, from the frozen
   `B_cap + 1` rung and the alleged protocol's own budget, that such a pair
   cannot sit at the Stage-2 frontier depth; `stage2_unsplit_pair_capacity_two`
   turns that into `kappa_v >= 2`, so the `htwo` premise of the banked
   `eq:isolation-capacity` is **derived from protocol data** rather than assumed,
   and `stage2_isolation_capacity_from_protocol` is the frozen
   `h_v + z_v <= kappa_v`.
5. **The Alice child selection and the Localized Extension invocation
   (`09:1004--1028`).**  `stage2_extension_branch_fires` composes the banked
   call-(ii) binder, the banked block-count exactness and the banked selection
   count at the reached capacity, and adds the frozen post-query column density
   comparison; `stage2_alice_child_budget_contradiction` is the frozen closing
   sentence "which exceeds `eq:terminal-stage2-budget`" **on the protocol
   object** -- the `d_v + 1` bits spent plus the `B_cap + log_2 kappa_v` the child
   demands do not fit, so the alleged `P_2` cannot exist.
6. **The Stage-3 split-or-route rule (`09:1055--1073`).**
   `routeWhole_valid_support` proves the frozen validity sentence exactly as the
   paper argues it; `stage3_split_or_route` is the frozen dichotomy at the
   threshold `tau_{d+1}`; and `routeWhole_loss_le` bounds one step's loss by the
   discarded child's density.
7. **The bridge to the refreshed certificate: `routedSupport_of_stepwise_losses`.**
   The frozen `09:1068--1073` says the surviving support of an unsplit attached
   object loses strictly less than `sum_{d >= 0} tau_{d+1} = tau_0` in total.
   This theorem proves that a chain of Stage-3 routing steps, each losing less
   than its own `tau_{d+1}`, produces a support satisfying the banked
   `TerminalStageThreeLift.RoutedSupport` -- i.e. **the protocol-side routing
   lands inside the quantifier of `RefreshedFixedBinBound`**, which is the exact
   shape the predecessor module's GAP-EXPOSED 2 asked for.
   `refreshedFixedBinBound_at_routed_chain` then reads the refreshed certificate
   off at the routed support, which is the frozen "we use this refreshed
   certificate ... at every selector isolation node".
8. **The Stage-3 stopping rule and the premature-depth exclusion
   (`09:1084--1095`, `09:1107--1110`), protocol-side.**  `stage3_object_depth_le`
   and `stage3_object_not_leaf` are the two frozen exclusions on the alleged
   `P_3`, at the banked scale guard `D_2 >= 2`.
9. **The Bob child selection (`09:1125--1132`).**
   `bob_query_preserves_aliceCols` / `bob_query_preserves_rowsAt` are the frozen
   "Bob's query does not change the row supports" (with the helper
   `aliceCols_append`, new here); `stage3_bob_child_density_at_terminal` is
   `eq:terminal-bob-child-density`, and it carries the frozen halving of
   `09:1126` **inside** its proof, through the banked
   `RoutingDynamics.exists_denser_bob_child_density` and
   `TerminalTwoStream.bob_child_density`.  There is deliberately no standalone
   halving declaration; the aux battery `G` below lists the four names this item
   actually lands.

**Deliberately open (GAP-EXPOSED).**

1. **Neither `eq:terminal-fixed-bin` nor `StageThreeLift` is proved here.**  The
   two named claims stay exactly as their own modules landed them, stated only.
   This module supplies the routing layer they were waiting on; what remains for
   phase 1 are the *certificate* inputs -- the one-copy and top two-copy residual
   readings at a node, and the conclusion `eq:certified-E3` of the Localized
   Extension corollary -- which are carried here as **explicit binders** at every
   theorem that consumes them and are asserted nowhere.
2. **The Localized Extension corollary's conclusion is not asserted.**
   `extensionCallTwo` is consumed by pin (`ExtensionCallTwoFixedWidth` is *not*
   referenced here, and the sentence no longer claims it is); `eq:certified-E3`
   appears in no conclusion, exactly as all three predecessor modules record.
   Two further preconditions the frozen call sentence states are likewise **not
   modelled**, and nothing below assumes them: the ordinary-token support floor
   `2 kappa_v 2^{-b_1}` of `09:1005--1006`, and the trimming step "trim each to
   support `kappa_v 2^{-b_1}`" of `09:1015`.  This is under-modelling, not an
   over-claim -- the same class as the row-floor omission `A:139--140` that
   `LargeCapacityBranch` records -- and it is named here so the ledger row
   carries it beside `eq:certified-E3`.
3. **Coordinate isolation is a named predicate, not a construction.**  The frozen
   "when its Stage-2 coordinate is isolated" (`09:937--938`) and "when its Stage-3
   outer block is isolated" (`09:1084--1085`) are carried through the banked
   `DenseWeightedCount.StopEvent.isolation` and the banked `isolationNodes`
   predicate.  This module does not build the isolation *test*; it proves the
   budget facts that hold at such a node.
4. **The simultaneous frontier of all tokens is not rebuilt.**  Each theorem
   below is about one routed object or one protocol node; the frontier-wide
   indexing is the banked `FrontierIndexing`, consumed by pin, and no new
   conservation identity is claimed.
5. **`sec:wrapper-projection-covers` is untouched.**  This block **feeds**
   `hDenseRung` and neither discharges nor narrows it; the ranges `09:1184--1366`,
   `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly as
   `ScaleAlignOpening` records them, and **no route completion is claimed**.

## Consumed by pin (never restated)

This list is a **fixed-interface record and is exact in both directions**: every
name below occurs in the code of this module, and every banked name the code
references occurs below.  (Re-derived first-hand this round off the
comment-stripped source; the seven never-consumed entries and the two consumed
but unlisted pins of the judged draft are corrected here, together with an eighth
never-consumed entry, `routeChildren_ne`, found in the same pass.)

* `DenseRoutingInvariant`: `BobRouting` with its fields `left`, `right`,
  `left_subset`, `right_subset`, `card_parent_le` and its `symm`,
  `BobRouting.symm_left`, `BobRouting.symm_right`; `canonicalRouting`;
  `routingFloor`, `routingFloor_succ_le_of_two_mul`; `routeLeft`,
  `routeLeft_length`, `routeRight`, `routeRight_length`,
  `routeChildren_incomparable`.
* `DenseBranchSelection`: `Dtwo`, `quotientSupport`, `mem_quotientSupport`.
* `DenseWeightedCount`: `descend`, `descend_cons`, `descendStep`, `IsQueryNode`,
  `IsQueryPath`, `IsBobNode`, `cost_descend_add_length_le`,
  `cost_descendStep_succ_le`, `node_not_leaf`, `StoppedToken` with its fields
  `route` and `event`, `StopEvent.isolation`, `StopEvent.beforeAlice`,
  `denseNoLeaf`, `seedFloor`,
  `trim_to_seed_floor`, `stoppingCapacity`, `two_le_stoppingCapacity_of_lt`,
  `isolationNode_capacity_at_depth`.
* `DenseFrontierConservation`: `FrontierArrival` with its constructors `unsplit`
  and `split`, its field `isWitness`, its `hContrib`, and
  `FrontierArrival.hContrib_le_one`.
* `RoutedCertificateSystem`: `IsAlicePath`,
  `cost_descend_add_length_le_of_isAlicePath`, `aliceCols`, `aliceConstraint`,
  `aliceCols_cons`, `nodeProjection`.
* `RoutingDynamics`: `rowsAt`, `exists_denser_bob_child_density`.
* `StageTwoRelaxed`: `StageTwoWidths` with its fields `q₂`, `r₂`, `t₂`.
* `TerminalTwoStream`: `tauAt`, `tauAt_partial_loss_lt`, `tauAt_stage3_frontier`,
  `scale_guard`, `bob_child_density`, `ordinary_column_density`,
  `post_alice_density_gt`, `extensionCallTwo`, `probeWidths` with its `r₂` and
  `t₂`.
* `TerminalFixedBin`: `fixedBinTarget`, `fixedBinRows`, `fixedBinCols`,
  `stage2_selection_count`, `stage2_extension_call_fires`,
  `stage2_capacity_trichotomy`.
* `TerminalStageThreeLift`: `stageThreeBudget`, `RoutedSupport`,
  `RefreshedFixedBinBound`, `tauAt_antitone`.
* `TwoStreamState`: the record `TwoStreamState` with the fields this module
  projects (`Pstar`, `sigmaStar`, `pOrd`, `pFor`, `iOrd`, `iFor`, `iotaOrd`,
  `iotaFor`, `Rfor`); `ProbeCl`, `probeState`, `probePstar`, `probePstar_card`,
  `probe_tauZero`.
* `WrapperProjectionCovers`: `tauZero`.
* `NPCC`: `subgame`.  `Workspace.Types.Interlace`: `interlaceFun`.  Both occur
  only inside the carrier expression of `refreshedFixedBinBound_at_routed_chain`,
  copied field-for-field from the banked `RefreshedFixedBinBound`.

## Canonical inhabitation

The frozen argument is an **adversary argument against an arbitrary protocol**:
`09:918--919` and `09:1037` both say "suppose for contradiction that ... has a
protocol", and the paper constructs no protocol tree anywhere.  Every
protocol-side declaration below is therefore *universally quantified over the
alleged protocol*, and the paper's object is covered by construction rather than
by exhibition -- which is strictly stronger than any synthetic inhabitant.

No new structure is introduced by this module: `heavierChild`, `heavierRoute`,
`pairArrival` and `pairDensity` are **defs over banked carriers**, and
`PairAgrees` is a predicate on two banked `BobRouting` records.  The banked
`FrontierArrival` and `BobRouting` keep their own inhabitation records.

The **deferred canonical-inhabitation obligation** this tranche inherits is
unchanged and is *not* discharged here: it is the one `TERMINAL-STAGE3-LIFT-001`
registered on `RefreshedFixedBinBound`, discharged only when phase 1 becomes
provable.  What this module adds is the missing *input* to that discharge --
`routedSupport_of_stepwise_losses` shows the routing produces supports inside the
refreshed quantifier -- not the discharge itself.

Five concrete readouts are labelled **NON-FIDELITY**
(`stage2_dispatch_is_reached` in §4, `heavierChild_needs_the_right_side` and
`pairArrival_split_is_reachable` in §8, `routeWhole_can_be_proper` and
`routedSupport_is_not_free` in §9) and one is a **rejection probe**
(`probe_single_pair_drop_is_not_one_routing_step`, §9).  They evaluate our
encoding at points the frozen paper never visits and are never evidence that the
terminal regime is inhabited.  `heavierChild_needs_the_right_side` shares the
self-chosen degenerate carrier of `pairArrival_split_is_reachable` and now
carries the same label.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex` (SHA-256
`5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`, recomputed
first-hand this round), opened for this tranche.

**No declaration below claims a reader item.**  The reader's entire account of
the protocol-side routing is the unnumbered prose at lines **370--373** ("For the
near-full rung, inspect an arbitrary protocol for the retained interlace.  Before
its terminal frontier, the all-column reference follows every Bob query and its
one-bit-down certificate prevents an early cheap termination"), which
`WRAPPER-PROJECTION-COVERS-001` already records as unclaimed prose, plus lines
**387--390** and **319--322**, recorded as unclaimed prose by `TERMINAL-FIXED-BIN-001`
and `TERMINAL-STAGE3-LIFT-001` respectively.  Searched first-hand across all nine
reader section files for "split", "route", "heavier child", "stopping rule",
"isolation node", `tau_d`, `lambda_d`, `49/128`, `9/16` in the terminal sense:
none occurs as a numbered statement.  The reader-counterpart discipline bars
citing prose as a statement counterpart, so nothing is claimed and no reader item
is assigned twice; line **391** stays with `TerminalTwoStream`'s certified-row-ladder
group and **361--368** stays with `WrapperLowRungs.wrapperLowRungs`.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the heavier child, general (5): `heavierChild_mem_children`,
  `heavierChild_subset`, `card_le_two_mul_heavierChild`,
  `heavierChild_floor_step`, `heavierRoute_length`.
* `B` the attached pair, general (6): `heavierRoute_eq_of_agree`,
  `pair_split_addresses_incomparable`, `pairArrival_split_addresses_ne`,
  `pairArrival_hContrib_le_one`, `pairArrival_isWitness`,
  `pair_descendants_meet_floor`.
* `C` the Stage-2 stopping rule and residual certificates, general (4):
  `stage2_routed_token_frontier`, `stage2_unsplit_pair_depth_lt`,
  `stage2_unsplit_pair_capacity_two`, `stage2_isolation_capacity_from_protocol`.
* `D` the Alice child and the Extension call, general (2):
  `stage2_alice_child_budget_contradiction`, `stage2_extension_branch_fires`.
* `E` the Stage-3 split-or-route rule and the routed support, general (6):
  `routeWhole_valid_support`, `routeWhole_loss_le`, `stage3_split_or_route`,
  `pairDensity_sdiff`, `routedSupport_of_stepwise_losses`,
  `refreshedFixedBinBound_at_routed_chain`.
* `F` the Stage-3 stopping rule, general (3): `stage3_object_depth_le`,
  `stage3_object_not_leaf`, `stage3_stop_certificate_inputs`.
* `G` the Bob child, general (4): `aliceCols_append`,
  `bob_query_preserves_aliceCols`, `bob_query_preserves_rowsAt`,
  `stage3_bob_child_density_at_terminal`.

That is **30 general battery entries proved**, with `0` unproved, alongside
**three statement poles** (`heavierChild_needs_the_right_side`,
`stage2_budget_comparison_never_fits`, `routedSupport_is_not_free`), **three
non-vacuity readouts** (`stage2_dispatch_is_reached`,
`pairArrival_split_is_reachable`, `routeWhole_can_be_proper`), **one rejection
probe** (`probe_single_pair_drop_is_not_one_routing_step`) and the probe helper
`poleRep_quotientSupport`.  The module has **48 declarations** in total: 38
theorems, 9 `def`s and 1 `instance`.

## HYPOTHESIS-CONSISTENCY note

Every theorem below is an implication whose antecedents are either banked
predicates or protocol-level budget facts, and none of them conjoins two cases of
one frozen construction: the Stage-2 node gate `d <= r_2` and the deep gate
`r_2 + 1 <= d` are passed to the banked `denseNoLeaf` in exactly the mutually
exclusive form that module states, and the Stage-3 dichotomy of `09:1061--1067` is
landed as a disjunction, never as a conjunction of both branches.

The two bundles that could be vacuous are exhibited satisfied:
`pairArrival_split_is_reachable` builds two banked `BobRouting` records at one
query whose heavier bits genuinely differ, so the `split` branch of `pairArrival`
is reached; and `stage2_dispatch_is_reached` exhibits the frozen three-case
dispatch at the banked **balance-minimum** width record
`TerminalTwoStream.probeWidths` -- legal for the four proof fields of
`StageTwoRelaxed.StageTwoWidths` and **not** a legal schedule width record, its
`k_2 = 5` failing the `eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}`
(`06:766`) -- with the
call-(ii) branch live at the root capacity.  `routedSupport_is_not_free` shows the
conclusion of `routedSupport_of_stepwise_losses` is not automatic: the empty
support is **not** a routed support at the banked probe state.

**Disclosure on `stage2_routed_token_frontier`.**  Its four-hypothesis bundle
(`hnodeFloor`, `hdeepFloor`, `honeCopy`, `hresidual`) is **not** exhibited
satisfied by an in-module instance.  Every one of the four is an *implication*,
and the banked core the theorem instantiates is itself probed
(`DenseWeightedCount.denseNoLeaf_hypotheses_consistent`, `denseNoLeaf_at_probe`),
so the bundle is satisfiable and the theorem is not vacuous -- but the
composition is not independently probed here, and the ledger row should not be
read as claiming that it is.
-/

namespace EthInapproximability.ParameterizedNP.Stage3ProtocolRouting

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.FiniteSlots

/-! ## §1  The heavier child of one query (`09:931`, `09:1055--1058`)

"An unattached token follows a child retaining at least half of its support."
(`09:931`)  In the Stage-3 orientation the same sentence reads "An unattached
ordinary object follows a child whose quotient row support has at least half the
size of its current support.  The two child projections may overlap, but their
union contains the parent support, so such a child always exists."
(`09:1055--1058`)

The banked `DenseRoutingInvariant.BobRouting` already carries the union clause as
its `assigns` field, so "such a child always exists" is not re-proved; what is new
is that the frozen rule names **a** child, i.e. a *choice*, and the choice is
made here by a derived selector rather than by an existential. -/

section HeavierChild

variable {Phys Coord Γ : Type*} [DecidableEq Coord] [DecidableEq Γ]
variable {rep : Phys → Coord × Γ} {S₀ S₁ : Finset Phys} {α β : Coord} {T Tf : Finset Γ}

/-- The bit naming the heavier of the two children of one query: `true` selects
the right child.  The frozen rule of `09:931` fixes the child only up to "at
least half", so the tie is broken to the left; `heavierChild_needs_the_right_side`
records that the choice is nevertheless genuine. -/
def heavierBit (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T) : Bool :=
  decide (r.left.card < r.right.card)

/-- **`09:931`, `09:1055--1057`.**  The child the frozen rule follows. -/
def heavierChild (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T) : Finset Γ :=
  if heavierBit r then r.right else r.left

/-- The address of that child below the current node, in the banked suffix-address
convention of `DenseRoutingInvariant.routeLeft` / `.routeRight`. -/
def heavierRoute (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T)
    (p : List Bool) : List Bool :=
  if heavierBit r then DenseRoutingInvariant.routeRight p else DenseRoutingInvariant.routeLeft p

/-- **Aux A1.**  The selected child is one of the two children the banked record
assigns; the selector invents no set.  General. -/
theorem heavierChild_mem_children (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T) :
    heavierChild r = r.left ∨ heavierChild r = r.right := by
  unfold heavierChild
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Aux A2.**  The selected child is a subset of the parent support: the routing
never invents mass.  General. -/
theorem heavierChild_subset (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T) :
    heavierChild r ⊆ T := by
  rcases heavierChild_mem_children r with h | h
  · rw [h]; exact r.left_subset
  · rw [h]; exact r.right_subset

/-- **Aux A3 (`09:931`, `09:1055--1058`).**  "a child retaining at least half of
its support" -- proved from the record's own `assigns` clause ("their union
contains the parent support"), so the frozen existence sentence is a theorem and
not a hypothesis.  General. -/
theorem card_le_two_mul_heavierChild (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T) :
    T.card ≤ 2 * (heavierChild r).card := by
  have h := r.card_parent_le
  unfold heavierChild heavierBit
  split_ifs with hb
  · simp only [decide_eq_true_eq] at hb
    omega
  · simp only [decide_eq_true_eq] at hb
    omega

/-- **Aux A4 (`09:934--935`, the unattached case).**  "Every descendant therefore
has support at least `lambda_{d+1}`", read at the banked integral floor
`L_d = ceil(lambda_d |C_1|)`: if the parent meets the floor at suffix depth `d`,
the selected child meets it at `d + 1`.  The step itself is the banked
`routingFloor_succ_le_of_two_mul`, consumed by pin.  General. -/
theorem heavierChild_floor_step [Fintype Γ]
    (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T) (q₂ b₁ d : ℕ)
    (hT : DenseRoutingInvariant.routingFloor Γ q₂ b₁ d ≤ T.card) :
    DenseRoutingInvariant.routingFloor Γ q₂ b₁ (d + 1) ≤ (heavierChild r).card :=
  DenseRoutingInvariant.routingFloor_succ_le_of_two_mul Γ hT (card_le_two_mul_heavierChild r)

/-- **Aux A5.**  Following a child spends exactly one suffix bit, so the frozen
depth bookkeeping of `09:938` is the address length.  General. -/
theorem heavierRoute_length (r : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T)
    (p : List Bool) : (heavierRoute r p).length = p.length + 1 := by
  unfold heavierRoute
  split_ifs
  · exact DenseRoutingInvariant.routeRight_length p
  · exact DenseRoutingInvariant.routeLeft_length p

/-! ## §2  The attached pair (`09:932--935`)

"For an attached pair, choose a heavier child separately for its two labelled
fibres.  If the choices agree, route the pair together.  If they differ, split it
into two ordinary tokens in incomparable children."

The outcome type is **not** new: it is the banked
`DenseFrontierConservation.FrontierArrival`, whose `unsplit` and `split`
constructors are exactly the frozen two cases.  What is new is that the outcome is
*computed* from the two fibres' own heavier bits rather than supplied as
constructor data. -/

/-- The frozen "the choices agree" of `09:933`. -/
def PairAgrees (ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T)
    (rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf) : Prop :=
  heavierBit ro = heavierBit rf

instance decidablePairAgrees (ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T)
    (rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf) :
    Decidable (PairAgrees ro rf) := by
  unfold PairAgrees
  infer_instance

/-- **`09:932--935`, the routing outcome of one attached pair**, as the banked
frontier-arrival kind.  Agreement routes the pair together and it reaches the
frontier whole (`unsplit`); disagreement splits it into two ordinary tokens at the
two children (`split`). -/
def pairArrival (ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T)
    (rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf) (p : List Bool) :
    DenseFrontierConservation.FrontierArrival (List Bool) :=
  if heavierBit ro = heavierBit rf then
    DenseFrontierConservation.FrontierArrival.unsplit (heavierRoute ro p)
  else
    DenseFrontierConservation.FrontierArrival.split (heavierRoute ro p) (heavierRoute rf p)

/-- **Aux B1 (`09:933`, "route the pair together").**  When the two labelled
fibres choose the same child, the two components have the same address, so the
pair is a single routed object.  General. -/
theorem heavierRoute_eq_of_agree {ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T}
    {rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf} (h : PairAgrees ro rf)
    (p : List Bool) : heavierRoute ro p = heavierRoute rf p := by
  unfold heavierRoute
  rw [show heavierBit ro = heavierBit rf from h]

/-- **Aux B2 (`09:933--934`, "two ordinary tokens in incomparable children").**
When the choices differ, the two descendants sit at addresses neither of which is
a prefix of the other.  The incomparability is the banked
`routeChildren_incomparable`, consumed by pin.  General. -/
theorem pair_split_addresses_incomparable
    {ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T}
    {rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf} (h : ¬ PairAgrees ro rf)
    (p : List Bool) :
    ¬ (heavierRoute ro p <+: heavierRoute rf p)
      ∧ ¬ (heavierRoute rf p <+: heavierRoute ro p) := by
  unfold PairAgrees at h
  unfold heavierRoute
  cases hbo : heavierBit ro <;> cases hbf : heavierBit rf <;>
    simp only [hbo, hbf] at h ⊢
  · exact absurd trivial h
  · exact DenseRoutingInvariant.routeChildren_incomparable p
  · exact ⟨(DenseRoutingInvariant.routeChildren_incomparable p).2,
      (DenseRoutingInvariant.routeChildren_incomparable p).1⟩
  · exact absurd trivial h

/-- **Aux B3 (`09:934`), the premise the banked counting module left open.**
`DenseFrontierConservation` records that "the frozen 'two incomparable children'
of `08:934--935` is deliberately not a field ... carried as the named hypothesis
`hpair`".  For the terminal routing that hypothesis is now a **theorem**: a split
pair's two addresses are distinct.  General. -/
theorem pairArrival_split_addresses_ne
    {ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T}
    {rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf} (p : List Bool) :
    ∀ v w : List Bool, pairArrival ro rf p =
      DenseFrontierConservation.FrontierArrival.split v w → v ≠ w := by
  intro v w hsplit
  unfold pairArrival at hsplit
  by_cases hagree : heavierBit ro = heavierBit rf
  · rw [if_pos hagree] at hsplit
    cases hsplit
  · rw [if_neg hagree] at hsplit
    obtain ⟨hv, hw⟩ : heavierRoute ro p = v ∧ heavierRoute rf p = w := by
      constructor
      · injection hsplit with h1 _
      · injection hsplit with _ h2
    subst hv
    subst hw
    have hne := pair_split_addresses_incomparable (ro := ro) (rf := rf) hagree p
    intro hcon
    exact hne.1 (by rw [hcon])

/-- **Aux B4.**  Consequently the banked pointwise bound `h_v <= 1` per arrival
applies to the terminal pair with **no** named hypothesis: the coverage limit the
banked module recorded is discharged for this routing.  General. -/
theorem pairArrival_hContrib_le_one
    {ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T}
    {rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf} (p u : List Bool) :
    (pairArrival ro rf p).hContrib u ≤ 1 :=
  DenseFrontierConservation.FrontierArrival.hContrib_le_one
    (pairArrival_split_addresses_ne (ro := ro) (rf := rf) p)

/-- **Aux B5 (`09:924--925`).**  "attach one additional foreign token to each
coordinate of `Z`": an attached pair is a witness coordinate in the banked
counting, whichever branch of the frozen rule fires.  General. -/
theorem pairArrival_isWitness
    {ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T}
    {rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf} (p : List Bool) :
    (pairArrival ro rf p).isWitness = true := by
  unfold pairArrival
  split_ifs <;> rfl

/-- **Aux B6 (`09:934--935`, the attached case).**  "Every descendant therefore has
support at least `lambda_{d+1}`" for **both** labelled fibres, in either branch of
the frozen rule: the two heavier children are chosen separately and each satisfies
the unattached step.  General. -/
theorem pair_descendants_meet_floor [Fintype Γ]
    (ro : DenseRoutingInvariant.BobRouting rep S₀ S₁ α T)
    (rf : DenseRoutingInvariant.BobRouting rep S₀ S₁ β Tf) (q₂ b₁ d : ℕ)
    (hTo : DenseRoutingInvariant.routingFloor Γ q₂ b₁ d ≤ T.card)
    (hTf : DenseRoutingInvariant.routingFloor Γ q₂ b₁ d ≤ Tf.card) :
    DenseRoutingInvariant.routingFloor Γ q₂ b₁ (d + 1) ≤ (heavierChild ro).card
      ∧ DenseRoutingInvariant.routingFloor Γ q₂ b₁ (d + 1) ≤ (heavierChild rf).card :=
  ⟨heavierChild_floor_step ro q₂ b₁ d hTo, heavierChild_floor_step rf q₂ b₁ d hTf⟩

end HeavierChild

/-! ## §3  The Stage-2 stopping rule and the two residual certificates
(`09:937--978`)

"Put `r_2 = log_2 q_2`.  Stop a token at the first Alice query or when its
Stage-2 coordinate is isolated. ... one-copy robustness gives residual complexity
`B_cap`.  If the coordinate is isolated, this is exactly the surviving local
block; an unsplit attached pair there has residual complexity `B_cap + 1` by the
inherited top two-copy rung.  In particular, no routed token can end at a protocol
leaf at a depth at most `r_2`." -/

section StageTwoStopping

variable {X Y Z Coord Γ : Type*} [Fintype Γ]

/-- **`09:937--951` and `09:967--978`, the Stage-2 frontier.**  The banked
`lem:dense-no-leaf` at the *terminal* Stage-2 budget `D_2 = B_cap + log_2 q_2` and
the frozen dyadic width `q_2 = 2^{r_2}`.

The frozen one-copy certificate is supplied through the banked trimming step: a
token whose support meets the routing floor at the node can be trimmed to the seed
density `2^{-b_1}`, and `honeCopy` is then the frozen "both have the thresholds in
`eq:stage1-robust-certificate`, so one-copy robustness gives residual complexity
`B_cap`" -- carried as an explicit binder because this module builds no rectangle
apparatus.  The two gates are the mutually exclusive `d <= r_2` (`09:943--951`)
and `r_2 + 1 <= d` (`09:967--978`) the frozen proof states, never conjoined.
General. -/
theorem stage2_routed_token_frontier {A B : List Bool → Type*}
    [∀ p, Fintype (A p)] [∀ p, Fintype (B p)] {Pstar : Protocol X Y Z}
    (g : ∀ p : List Bool, A p → B p → Bool)
    (t : DenseWeightedCount.StoppedToken Pstar Coord)
    (supp : List Bool → Finset Γ) {bcap r₂ b₁ : ℕ}
    (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hnodeFloor : t.route.length ≤ r₂ →
      DenseRoutingInvariant.routingFloor Γ (2 ^ r₂) b₁ t.route.length ≤ (supp t.route).card)
    (hdeepFloor : r₂ + 1 ≤ t.route.length →
      DenseRoutingInvariant.routingFloor Γ (2 ^ r₂) b₁ (r₂ + 1)
        ≤ (supp (t.route.take (r₂ + 1))).card)
    (honeCopy : ∀ p : List Bool,
      DenseWeightedCount.seedFloor Γ b₁ ≤ (supp p).card → bcap ≤ D (g p))
    (hresidual : ∀ p : List Bool, D (g p) ≤ (DenseWeightedCount.descend Pstar p).cost) :
    (t.event = DenseWeightedCount.StopEvent.isolation
        ∨ t.event = DenseWeightedCount.StopEvent.beforeAlice)
      ∧ t.route.length ≤ r₂ :=
  DenseWeightedCount.denseNoLeaf g t hbcap hbudget
    (fun h => honeCopy _ (DenseWeightedCount.trim_to_seed_floor (hnodeFloor h) (by omega)))
    (fun _ => hresidual _)
    (fun h => honeCopy _ (DenseWeightedCount.trim_to_seed_floor (hdeepFloor h) le_rfl))
    (fun _ => hresidual _)

end StageTwoStopping

section StageTwoBudget

variable {X Y Z : Type*}

/-- **`09:948--965`, the unsplit attached pair, protocol-side.**  "an unsplit
attached pair there has residual complexity `B_cap + 1` by the inherited top
two-copy rung ... if `kappa_v = 1`, then `d_v = r_2`, while `P_2` has at most
`D_2 - r_2 = B_cap` bits remaining, contradicting the pair's residual complexity
`B_cap + 1`."

Read additively on the alleged protocol: the `d` bits already spent plus the
`B_cap + 1` the pair demands do not fit inside `D_2`, so the pair's node is
strictly above the Stage-2 frontier depth.  The `B_cap + 1` rung is the inherited
top two-copy certificate, carried as the explicit binder `hpair`; this module
neither proves nor assumes it anywhere else.  General. -/
theorem stage2_unsplit_pair_depth_lt {A B : Type*} [Fintype A] [Fintype B]
    {gpair : A → B → Bool} {Pstar : Protocol X Y Z} {p : List Bool} {bcap r₂ : ℕ}
    (hpath : DenseWeightedCount.IsQueryPath Pstar p)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hpair : bcap + 1 ≤ D gpair)
    (hres : D gpair ≤ (DenseWeightedCount.descend Pstar p).cost) :
    p.length < r₂ := by
  have hspent := DenseWeightedCount.cost_descend_add_length_le (P := Pstar) hpath
  simp only [DenseBranchSelection.Dtwo] at hbudget
  omega

/-- **`09:956--958`, the frozen capacity clause, derived.**  "An unsplit attached
pair contributes two tokens and can occur only when `kappa_v >= 2`."  The banked
`eq:isolation-capacity` takes exactly this as its named premise `htwo`; here it is
**derived** from the alleged protocol's own budget through the previous theorem.
General. -/
theorem stage2_unsplit_pair_capacity_two {A B : Type*} [Fintype A] [Fintype B]
    {gpair : A → B → Bool} {Pstar : Protocol X Y Z} {p : List Bool} {bcap r₂ : ℕ}
    (hpath : DenseWeightedCount.IsQueryPath Pstar p)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hpair : bcap + 1 ≤ D gpair)
    (hres : D gpair ≤ (DenseWeightedCount.descend Pstar p).cost) :
    2 ≤ DenseWeightedCount.stoppingCapacity r₂ p.length :=
  DenseWeightedCount.two_le_stoppingCapacity_of_lt
    (stage2_unsplit_pair_depth_lt hpath hbudget hpair hres)

/-- **`09:953--965`, `h_v + z_v <= kappa_v` at a Stage-2 isolation node.**
"Coordinatewise uniqueness leaves at most one routed object there.  An ordinary
object contributes one token, hence at most `kappa_v` ... Thus
`h_v + z_v <= kappa_v` at every isolation node, as required by the weighted
frontier."

The counting is the banked `isolationNode_capacity_at_depth`; what this adds is
that its `htwo` premise is discharged from protocol data whenever a bonus
component is present, so the frozen sentence needs no capacity hypothesis of its
own.  `huniq` is the frozen coordinatewise-uniqueness clause and `hz` the banked
`z_v <= h_v`, both named as the banked module states them.  General. -/
theorem stage2_isolation_capacity_from_protocol {A B : Type*} [Fintype A] [Fintype B]
    {gpair : A → B → Bool} {Pstar : Protocol X Y Z} {p : List Bool} {bcap r₂ h z : ℕ}
    (huniq : h ≤ 1) (hz : z ≤ h)
    (hpath : DenseWeightedCount.IsQueryPath Pstar p)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hpair : 0 < z → bcap + 1 ≤ D gpair)
    (hres : 0 < z → D gpair ≤ (DenseWeightedCount.descend Pstar p).cost) :
    h + z ≤ DenseWeightedCount.stoppingCapacity r₂ p.length :=
  DenseWeightedCount.isolationNode_capacity_at_depth huniq hz
    (fun hzpos => stage2_unsplit_pair_capacity_two hpath hbudget (hpair hzpos) (hres hzpos))

/-! ## §4  The Alice child and the Localized Extension invocation
(`09:1004--1028`) -/

/-- **`09:1023--1028`, the closing contradiction of phase 1, on the protocol
object.**

"In every case one Alice child has complexity at least `B_cap + log_2 kappa_v`,
which exceeds `eq:terminal-stage2-budget`."  At `log_2 kappa_v = r_2 - d_v` the
frozen comparison is: the `d_v` bits spent reaching the first-Alice node, the one
bit of the Alice query itself, and the `B_cap + (r_2 - d_v)` the selected child
still demands, together exceed the alleged `P_2`'s total depth `D_2`.

`hchild` is the frozen "one Alice child has complexity at least
`B_cap + log_2 kappa_v`", the endpoint of the three-case dispatch; it is an
explicit binder, and the dispatch that produces it -- in particular
`eq:certified-E3` -- is asserted nowhere in this module.

**The frozen depth clause is deliberately not a hypothesis here.**  `09:951`
places the node at depth at most `r_2`, and that clause is what makes the
*certificate* `hchild` available at all; the budget comparison itself does not
need it, because the truncated `r_2 - d` only makes a deeper node worse.  Adding
`d <= r_2` would therefore be a hypothesis that restates a derived telescope, and
`stage2_budget_comparison_never_fits` records the exact arithmetic.  General. -/
theorem stage2_alice_child_budget_contradiction {Pstar : Protocol X Y Z} {p : List Bool}
    {bcap r₂ : ℕ} {b : Bool}
    (hpath : DenseWeightedCount.IsQueryPath Pstar p)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hnode : DenseWeightedCount.IsQueryNode (DenseWeightedCount.descend Pstar p))
    (hchild : bcap + (r₂ - p.length)
      ≤ (DenseWeightedCount.descendStep (DenseWeightedCount.descend Pstar p) b).cost) :
    False := by
  have hspent := DenseWeightedCount.cost_descend_add_length_le (P := Pstar) hpath
  have hstep := DenseWeightedCount.cost_descendStep_succ_le hnode b
  simp only [DenseBranchSelection.Dtwo] at hbudget
  omega

/-- **Statement pole 3 (which frozen clause is load-bearing where).**

`09:1023--1028` compares the spent `d_v + 1` bits plus the demanded
`B_cap + log_2 kappa_v` against the alleged `P_2`'s total `D_2`, and the frozen
sentence sits at a node of depth at most `r_2` (`09:951`).  It would be easy to
carry that depth clause into the Lean comparison as a hypothesis; this readout
shows why that would be wrong.  In the additive, truncation-free encoding the
comparison `d + 1 + (B_cap + (r_2 - d)) <= B_cap + r_2` fails at **every** depth:
below the frontier because `r_2 + 1 > r_2`, and above it because the truncated
`r_2 - d` is `0` while `d + 1 > r_2`.  So the depth clause is load-bearing for
the *certificate* `hchild` -- the frozen residual reading is only claimed at
depth at most `r_2` -- and carries no weight in the budget arithmetic, which is
exactly how the previous theorem binds it. -/
theorem stage2_budget_comparison_never_fits (bcap r₂ d : ℕ) :
    ¬ (d + 1 + (bcap + (r₂ - d)) ≤ bcap + r₂) := by
  omega

end StageTwoBudget

section ExtensionCall

/-- **`09:1004--1019`, the Localized Extension invocation at a reached
capacity.**

"Each ordinary token there has support at least `2 kappa_v 2^{-b_1}` ...  Following
the denser Alice child leaves typed density at least `49/128 > 9/25`.  If
`kappa_v >= t_2`, select `9 kappa_v/16` ordinary coordinates, trim each to support
`kappa_v 2^{-b_1}`, and invoke Localized Extension at the fixed physical width
`t_2`.  This is exactly call (ii) in `sec:extension-call-ledger`."

The three banked pieces are composed at the frozen guard and nothing is added:
the reached-capacity binder yields `extensionCallTwo` and, with the width record's
`16 | t_2`, the frozen selected-block count `9 kappa_v/16`; the first-Alice verdict
`3 kappa_v <= 4 h_v` leaves the `9 kappa_v/16` ordinary coordinates the call
consumes; and the frozen post-query column density `49/128` clears the capacity
guard `9/25`.  **The call's conclusion `eq:certified-E3` is not asserted.**
General in the width record and the depth. -/
theorem stage2_extension_branch_fires (W : StageTwoRelaxed.StageTwoWidths) {d h : ℕ}
    (hd : d ≤ W.r₂)
    (hbind : ∀ e : ℕ, e ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ e →
        TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
          (DenseWeightedCount.stoppingCapacity W.r₂ e))
    (hguard : W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d)
    (hforced : 3 * DenseWeightedCount.stoppingCapacity W.r₂ d ≤ 4 * h) :
    TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d)
      ∧ (DenseWeightedCount.stoppingCapacity W.r₂ d / W.t₂) * (9 * W.t₂ / 16)
        = 9 * DenseWeightedCount.stoppingCapacity W.r₂ d / 16
      ∧ 9 * DenseWeightedCount.stoppingCapacity W.r₂ d ≤ 16 * h
      ∧ (9 : ℝ) / 25 < 49 / 128 := by
  obtain ⟨hcall, hcount⟩ := TerminalFixedBin.stage2_extension_call_fires W hd hbind hguard
  exact ⟨hcall, hcount, TerminalFixedBin.stage2_selection_count hforced,
    TerminalTwoStream.post_alice_density_gt⟩

/-- **Non-vacuity / consistency for §4 (`09:1014--1023` reached at both ends) --
NON-FIDELITY.**  At the banked **balance-minimum** width record
`TerminalTwoStream.probeWidths` -- **not** a legal schedule width record, per the
`eq:t2-search` paragraph below --
(`k_2 = 5`, `r_2 = 7`, `b_1 = 24`, hence `q_2 = 128`, `t_2 = 32`) the frozen
three-case dispatch is reached at **both ends**: the call-(ii) branch fires at
the root capacity `2^7 = 128 >= 32`, and the capacity-one branch is reached at the
frontier depth.

**Exactly which branches this exhibits.**  `09:1014--1023` dispatches on *three*
cases -- `kappa_v >= t_2` (`09:1014`), `2 <= kappa_v < t_2` (`09:1020`) and
`kappa_v = 1` (`09:1021`) -- and this readout exhibits the first and the third.
The middle case is *not* exhibited here, though it is reachable at the same
banked record (`stoppingCapacity probeWidths.r_2 6 = 2^{7-6} = 2 < 32`); the
third conjunct below carries it only as the banked trichotomy's own disjunct.

The banked record `probeWidths` is legal for the four proof fields of
`StageTwoRelaxed.StageTwoWidths` and **not** for the schedule -- `eq:t2-search`
fixes `k_2 >= max{4, 2^{19}, m_HS}` at `06:766` and `probeWidths.k₂ = 5` -- and
its widths sit outside the **gate-firing** regime (`TerminalTwoStream` records
that `eq:all-extension-gates` fails there).  So this is machine evidence about
our encoding, not a witness at the paper's parameter values.  (Terminology and
the unqualified legality reading repaired at `cc-t7p`, ledger item `(b11)`; the
predecessor "certified regime" is WITHDRAWN, and the record that defined that
term, `TerminalTwoStream.extProbeWidths`, fails the same `06:766` floor.) -/
theorem stage2_dispatch_is_reached :
    TerminalTwoStream.probeWidths.t₂
        ≤ DenseWeightedCount.stoppingCapacity TerminalTwoStream.probeWidths.r₂ 0
      ∧ DenseWeightedCount.stoppingCapacity TerminalTwoStream.probeWidths.r₂
          TerminalTwoStream.probeWidths.r₂ = 1
      ∧ (TerminalTwoStream.probeWidths.t₂
            ≤ DenseWeightedCount.stoppingCapacity TerminalTwoStream.probeWidths.r₂ 0
          ∨ (2 ≤ DenseWeightedCount.stoppingCapacity TerminalTwoStream.probeWidths.r₂ 0
              ∧ DenseWeightedCount.stoppingCapacity TerminalTwoStream.probeWidths.r₂ 0
                < TerminalTwoStream.probeWidths.t₂)
          ∨ DenseWeightedCount.stoppingCapacity TerminalTwoStream.probeWidths.r₂ 0 = 1) :=
  ⟨by decide, by decide,
    TerminalFixedBin.stage2_capacity_trichotomy _ _ (by decide)⟩

end ExtensionCall

/-! ## §5  The Stage-3 split-or-route rule and the routed support
(`09:1055--1073`)

"For the attached object, let `P` be its current typed support and let `P_0,P_1`
be the two child projections induced by an Alice query.  If both have relative
density at least `tau_{d+1}`, split the object and put one ordinary object in each
child; both use the first, ordinary-coordinate projection of the corresponding
`P_i`.  If, say, `P_0` has density below `tau_{d+1}`, route the whole object to
child one using `P setminus P_0`.  This is a valid support in child one because
every parent pair absent from `P_1` belongs to `P_0`." -/

section PairSupport

variable {σ : Type*} [DecidableEq σ]

/-- The typed physical density of a support inside a template bin pair,
`|P| / m_T^2` -- the exact normalization the banked
`TerminalStageThreeLift.RoutedSupport` and the record's
`eq:terminal-physical-pair-density` use, so no new denominator is introduced. -/
noncomputable def pairDensity (mT : ℕ) (P : Finset σ) : ℝ := (P.card : ℝ) / (mT : ℝ) ^ 2

/-- **`09:1066--1067`, the routing-validity sentence, proved.**  "This is a valid
support in child one because every parent pair absent from `P_1` belongs to
`P_0`."  Given that the two child projections cover the parent support, the set
`P \ P_0` the frozen rule routes really does live in child one.  General. -/
theorem routeWhole_valid_support {P P₀ P₁ : Finset σ} (hcover : P ⊆ P₀ ∪ P₁) :
    P \ P₀ ⊆ P₁ := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  rcases Finset.mem_union.1 (hcover hx.1) with h | h
  · exact absurd h hx.2
  · exact h

/-- **Aux E2 (`09:1065--1069`).**  The whole-object route loses at most the
discarded child's own density, so the frozen "below `tau_{d+1}`" clause bounds one
step's loss by `tau_{d+1}`.  General; no positivity of `m_T` is needed because the
inequality is between three quotients with one denominator. -/
theorem routeWhole_loss_le (mT : ℕ) (P P₀ : Finset σ) :
    pairDensity mT P - pairDensity mT (P \ P₀) ≤ pairDensity mT P₀ := by
  have hsub : P ⊆ (P \ P₀) ∪ P₀ := by
    intro x hx
    by_cases hx0 : x ∈ P₀
    · exact Finset.mem_union_right _ hx0
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hx0⟩)
  have hcard : P.card ≤ (P \ P₀).card + P₀.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hcardR : (P.card : ℝ) ≤ ((P \ P₀).card : ℝ) + (P₀.card : ℝ) := by exact_mod_cast hcard
  have hden : (0 : ℝ) ≤ (mT : ℝ) ^ 2 := by positivity
  simp only [pairDensity, div_sub_div_same]
  rcases hden.eq_or_lt with hz | hpos
  · rw [← hz]
    simp
  · rw [div_le_div_iff_of_pos_right hpos]
    linarith

/-- **`09:1061--1067`, the frozen dichotomy.**  At an Alice query either both
child projections keep relative density at least `tau_{d+1}` -- the frozen split
branch -- or one of them is below it, and the whole object routes into the *other*
child with a valid support whose loss is strictly below `tau_{d+1}`.  Landed as a
disjunction, never as a conjunction of the two frozen branches.

**The routed sets are named, not existentially quantified.**  The frozen rule
routes using `P setminus P_0` specifically, and an existential `exists Q ⊆ P_1`
would be satisfied by the trivial `Q = ∅` at any sparse parent; naming the frozen
sets removes that reading and keeps the statement a claim about the paper's own
construction.  General. -/
theorem stage3_split_or_route {mT : ℕ} {P P₀ P₁ : Finset σ} (hcover : P ⊆ P₀ ∪ P₁)
    (τ : ℝ) :
    (τ ≤ pairDensity mT P₀ ∧ τ ≤ pairDensity mT P₁)
      ∨ (P \ P₀ ⊆ P₁ ∧ pairDensity mT P - pairDensity mT (P \ P₀) < τ)
      ∨ (P \ P₁ ⊆ P₀ ∧ pairDensity mT P - pairDensity mT (P \ P₁) < τ) := by
  by_cases h₀ : τ ≤ pairDensity mT P₀
  · by_cases h₁ : τ ≤ pairDensity mT P₁
    · exact Or.inl ⟨h₀, h₁⟩
    · refine Or.inr (Or.inr ⟨routeWhole_valid_support ?_, ?_⟩)
      · rw [Finset.union_comm]
        exact hcover
      · exact lt_of_le_of_lt (routeWhole_loss_le mT P P₁) (not_le.1 h₁)
  · refine Or.inr (Or.inl ⟨routeWhole_valid_support hcover, ?_⟩)
    exact lt_of_le_of_lt (routeWhole_loss_le mT P P₀) (not_le.1 h₀)

/-- **Aux E4.**  The density of a difference splits, because the subtrahend is a
subset.  General. -/
theorem pairDensity_sdiff (mT : ℕ) {P Q : Finset σ} (h : Q ⊆ P) :
    pairDensity mT (P \ Q) = pairDensity mT P - pairDensity mT Q := by
  have hcard : ((P \ Q).card : ℝ) = (P.card : ℝ) - (Q.card : ℝ) := by
    have h1 : (P \ Q).card + Q.card = P.card := Finset.card_sdiff_add_card_eq_card h
    have h2 : ((P \ Q).card : ℝ) + (Q.card : ℝ) = (P.card : ℝ) := by exact_mod_cast h1
    linarith
  simp only [pairDensity, hcard, sub_div]

end PairSupport

/-! ### The routed support produced by a Stage-3 routing chain

`09:1068--1073`: "an attached object that remains unsplit loses strictly less than
`sum_{d >= 0} tau_{d+1} = tau_0` of its typed physical support."  The banked
`TerminalTwoStream.tauAt_partial_loss_lt` is that geometric bound; what this
section adds is that the frozen conclusion is exactly membership in the banked
`TerminalStageThreeLift.RoutedSupport`, i.e. the routing lands **inside** the
quantifier of `RefreshedFixedBinBound`. -/

section RoutedChain

variable {Rw Cl Om Cone Ltwo : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
variable {q s q₂ mT dT : ℕ} {Nmat : Rw → Cl → Bool}
variable {lamT eps2 xT ε δ' : ℝ}

/-- **`09:1068--1073`, the frozen total-loss conclusion, as membership in the
banked refreshed quantifier.**

A Stage-3 routing chain is a decreasing family of typed supports starting at the
record's own `P_*`, each step losing strictly less than its own threshold
`tau_{d+1}` -- exactly the two branches of `09:1061--1067` produce.  The frozen
sentence bounds the *total* loss by `sum_{d >= 0} tau_{d+1} = tau_0`, and that is
precisely the antecedent of clause (v) of `def:two-stream-state`, i.e. the banked
`TerminalStageThreeLift.RoutedSupport`.

This is the object the predecessor module's GAP-EXPOSED 2 named: the protocol-side
routing now provably produces supports the refreshed certificate speaks about.
General in the state, the chain and its length. -/
theorem routedSupport_of_stepwise_losses
    {Rone : Type*}
    {Mmat' : Cone → Rone → Bool} {cFam : Ltwo → Slot q₂ → Rone}
    {Stwo : Ltwo → Slot q₂ × Cone → Bool} {RG RSig RD : Finset Rw} {omg : Rw → Om}
    {rho : Slot s → Om → Slot q₂ × Cone} {YT : Slot s → Finset Cl}
    {zeta : Slot s → Cl → Ltwo} {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat' cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (Ps : ℕ → Finset (Cl × Cl)) (n : ℕ)
    (h0 : Ps 0 = st.Pstar)
    (hchain : ∀ d, Ps (d + 1) ⊆ Ps d)
    (hpos : 0 < WrapperProjectionCovers.tauZero s xT)
    (hstep : ∀ d ∈ Finset.range n,
      pairDensity mT (Ps d) - pairDensity mT (Ps (d + 1)) < TerminalTwoStream.tauAt s xT (d + 1)) :
    TerminalStageThreeLift.RoutedSupport st (Ps n) := by
  have hmono : ∀ m, Ps m ⊆ Ps 0 := by
    intro m
    induction m with
    | zero => exact Finset.Subset.refl _
    | succ k ih => exact subset_trans (hchain k) ih
  have hsubn : Ps n ⊆ st.Pstar := by
    have := hmono n
    rwa [h0] at this
  refine ⟨hsubn, ?_⟩
  have htel : pairDensity mT (Ps 0) - pairDensity mT (Ps n)
      = ∑ d ∈ Finset.range n,
          (pairDensity mT (Ps d) - pairDensity mT (Ps (d + 1))) :=
    (Finset.sum_range_sub' (fun d => pairDensity mT (Ps d)) n).symm
  have hsumlt : ∑ d ∈ Finset.range n,
        (pairDensity mT (Ps d) - pairDensity mT (Ps (d + 1)))
      < WrapperProjectionCovers.tauZero s xT := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using hpos
    · have hne : (Finset.range n).Nonempty := by
        exact Finset.nonempty_range_iff.2 (by omega)
      have h1 : ∑ d ∈ Finset.range n,
            (pairDensity mT (Ps d) - pairDensity mT (Ps (d + 1)))
          < ∑ d ∈ Finset.range n, TerminalTwoStream.tauAt s xT (d + 1) :=
        Finset.sum_lt_sum_of_nonempty hne hstep
      have h2 := (TerminalTwoStream.tauAt_partial_loss_lt hpos n).2
      linarith
  have hsdiff : pairDensity mT (st.Pstar \ Ps n)
      = pairDensity mT (Ps 0) - pairDensity mT (Ps n) := by
    rw [pairDensity_sdiff mT hsubn, h0]
  have hgoal : pairDensity mT (st.Pstar \ Ps n) < WrapperProjectionCovers.tauZero s xT := by
    rw [hsdiff, htel]
    exact hsumlt
  simpa [pairDensity] using hgoal

/-- **`09:1078--1082` consumed at the routing's own output.**  "We use this
refreshed certificate, rather than restriction monotonicity, at every selector
isolation node and in the capacity-one case below."

Given the banked refreshed certificate as a binder -- it is *not* proved, and this
module does not pretend otherwise -- the support the Stage-3 routing produces
carries the phase-1 bound `D_2 + 1`.  This is the composition the frozen sentence
performs, with the routing supplied by the previous theorem instead of assumed.
General. -/
theorem refreshedFixedBinBound_at_routed_chain
    {Rone : Type*}
    {Mmat' : Cone → Rone → Bool} {cFam : Ltwo → Slot q₂ → Rone}
    {Stwo : Ltwo → Slot q₂ × Cone → Bool} {RG RSig RD : Finset Rw} {omg : Rw → Om}
    {rho : Slot s → Om → Slot q₂ × Cone} {YT : Slot s → Finset Cl}
    {zeta : Slot s → Cl → Ltwo} {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat' cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {bcap r₂ : ℕ} (hrefresh : TerminalStageThreeLift.RefreshedFixedBinBound st bcap r₂)
    (Ps : ℕ → Finset (Cl × Cl)) (n : ℕ)
    (h0 : Ps 0 = st.Pstar)
    (hchain : ∀ d, Ps (d + 1) ⊆ Ps d)
    (hpos : 0 < WrapperProjectionCovers.tauZero s xT)
    (hstep : ∀ d ∈ Finset.range n,
      pairDensity mT (Ps d) - pairDensity mT (Ps (d + 1)) < TerminalTwoStream.tauAt s xT (d + 1)) :
    TerminalFixedBin.fixedBinTarget bcap r₂
      ≤ D (NPCC.subgame (Workspace.Types.Interlace.interlaceFun Nmat q)
            (TerminalFixedBin.fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG
              st.Rfor st.iotaOrd st.iotaFor)
            (TerminalFixedBin.fixedBinCols (Ps n) st.sigmaStar)) :=
  hrefresh (Ps n) (routedSupport_of_stepwise_losses st Ps n h0 hchain hpos hstep)

end RoutedChain

/-! ## §6  The Stage-3 stopping rule, protocol-side (`09:1084--1095`,
`09:1107--1110`)

"Stop each routed object immediately before its first Bob query or when its
Stage-3 outer block is isolated. ...  After trimming the row support to `x_T`,
`eq:terminal-seed-inputs` gives residual complexity at least `D_2`.  Thus no
ordinary object can stop at a protocol leaf by depth `r_3`. ...  Nor can an
ordinary object first reach depth `r_3 + 1`."

Both exclusions are budget counts against the alleged `P_3` of total depth
`C - 1 = D_2 + r_3`, which is the banked
`TerminalStageThreeLift.stageThreeBudget`. -/

section StageThreeStopping

variable {X Y Z : Type*}

/-- **`09:1107--1110`, the Stage-3 premature-depth exclusion, protocol-side.**
"Nor can an ordinary object first reach depth `r_3 + 1`: it would retain row
density at least `x_T` and column density greater than `3/5`, so its residual
complexity would be `D_2`, while only `D_2 - 1` bits would remain."

An object routed through Alice queries to a node whose residual subtree must still
solve a `D_2`-hard game cannot be deeper than `r_3`.  `hhard` is the frozen
seed-inputs certificate at the trimmed support, an explicit binder.  General. -/
theorem stage3_object_depth_le {Pstar : Protocol X Y Z} {p : List Bool} {bcap r₂ r₃ : ℕ}
    (hpath : RoutedCertificateSystem.IsAlicePath Pstar p)
    (hbudget : Pstar.cost ≤ TerminalStageThreeLift.stageThreeBudget bcap r₂ r₃)
    (hhard : DenseBranchSelection.Dtwo bcap r₂ ≤ (DenseWeightedCount.descend Pstar p).cost) :
    p.length ≤ r₃ := by
  have h := RoutedCertificateSystem.cost_descend_add_length_le_of_isAlicePath hpath
  simp only [TerminalStageThreeLift.stageThreeBudget] at hbudget
  omega

/-- **`09:1093--1095`, the Stage-3 no-leaf exclusion.**  "After trimming the row
support to `x_T`, `eq:terminal-seed-inputs` gives residual complexity at least
`D_2`.  Thus no ordinary object can stop at a protocol leaf by depth `r_3`."

The banked `scale_guard` (`09:1148--1149`) makes `D_2 >= 2` at the frozen
`q_2 >= 16`, so the node's game is not constant and the node is not a leaf.
General. -/
theorem stage3_object_not_leaf {A B : Type*} [Fintype A] [Fintype B]
    {gnode : A → B → Bool} {Pstar : Protocol X Y Z} {p : List Bool} {bcap r₂ : ℕ}
    (hq : 16 ≤ 2 ^ r₂)
    (hhard : DenseBranchSelection.Dtwo bcap r₂ ≤ D gnode)
    (hres : D gnode ≤ (DenseWeightedCount.descend Pstar p).cost) (z : Z) :
    DenseWeightedCount.descend Pstar p ≠ Protocol.leaf z := by
  have hpos : 0 < DenseBranchSelection.Dtwo bcap r₂ := by
    have := TerminalTwoStream.scale_guard bcap r₂ hq
    omega
  exact DenseWeightedCount.node_not_leaf hpos hhard hres z

/-- **`09:1086--1092`, the two inputs of the Stage-3 stop certificate.**  "Since
`delta' <= 1` and `eq:terminal-entry` imply `eps < 1/5`, specified-coordinate
projection gives every ordinary object column density at least
`1 - eps > 4/5 > 3/5`.  For `d <= r_3`, its row support is at least
`tau_d >= tau_{r_3} = 2 x_T`."

Both readouts are banked (`ordinary_column_density`, `tauAt_antitone`,
`tauAt_stage3_frontier`); this exhibits them together at the frozen dyadic width
`s = 2^{r_3}` and at any depth up to the Stage-3 frontier, which is the pair the
frozen trimming step consumes.  General. -/
theorem stage3_stop_certificate_inputs {r₃ d : ℕ} {xT ε : ℝ} (hd : d ≤ r₃)
    (hxT : 0 ≤ xT) (hε : ε < 1 / 5) :
    (3 : ℝ) / 5 < 1 - ε
      ∧ 2 * xT ≤ TerminalTwoStream.tauAt (2 ^ r₃) xT d := by
  have hcol := TerminalTwoStream.ordinary_column_density hε
  refine ⟨by linarith [hcol.1, hcol.2], ?_⟩
  have hτ0 : 0 ≤ WrapperProjectionCovers.tauZero (2 ^ r₃) xT := by
    rw [WrapperProjectionCovers.tauZero]
    positivity
  have hanti := TerminalStageThreeLift.tauAt_antitone (s := 2 ^ r₃) (xT := xT) hτ0 hd
  rw [TerminalTwoStream.tauAt_stage3_frontier] at hanti
  exact hanti

end StageThreeStopping

/-! ## §7  The Bob child (`09:1125--1132`)

"Bob's query does not change the row supports.  Follow a child whose quotient
projection of `K_{ord}` has at least half its current size.  After projection to
any selected collection of ordinary bins, this child has column density at least
`(1 - eps)/2 > 2/5 > 9/25`." -/

section BobChild

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [Fintype Y] [DecidableEq Y] in
/-- **Aux G1 (a helper the banked module does not carry).**  Alice's surviving row
set decomposes along any split of the address.  General. -/
theorem aliceCols_append : ∀ {P : Protocol X Y Z} (p r : List Bool),
    RoutedCertificateSystem.aliceCols P (p ++ r)
      = RoutedCertificateSystem.aliceCols P p
        ∩ RoutedCertificateSystem.aliceCols (DenseWeightedCount.descend P p) r := by
  intro P p
  induction p generalizing P with
  | nil =>
      intro r
      simp [DenseWeightedCount.descend]
  | cons b p ih =>
      intro r
      rw [List.cons_append, RoutedCertificateSystem.aliceCols_cons, ih,
        RoutedCertificateSystem.aliceCols_cons, DenseWeightedCount.descend_cons,
        Finset.inter_assoc]

omit [Fintype Y] [DecidableEq Y] in
/-- **`09:1125`, "Bob's query does not change the row supports."**  At a Bob query
Alice's surviving row set is untouched by the answer bit.  General. -/
theorem bob_query_preserves_aliceCols {P : Protocol X Y Z} {p : List Bool}
    (h : DenseWeightedCount.IsBobNode (DenseWeightedCount.descend P p)) (b : Bool) :
    RoutedCertificateSystem.aliceCols P (p ++ [b])
      = RoutedCertificateSystem.aliceCols P p := by
  rw [aliceCols_append p [b], RoutedCertificateSystem.aliceCols_cons]
  have hc : RoutedCertificateSystem.aliceConstraint
      (DenseWeightedCount.descend P p) b = Finset.univ := by
    cases hP : DenseWeightedCount.descend P p with
    | leaf z => rfl
    | aNode a l r =>
        rw [hP] at h
        exact absurd h (by simp [DenseWeightedCount.IsBobNode])
    | bNode f l r => rfl
  rw [hc]
  simp

omit [Fintype Y] [DecidableEq Y] in
/-- **`09:1125` on the routed row set.**  Consequently the banked `rowsAt` -- the
rows a routed object still owns at a node -- is unchanged across a Bob query, which
is exactly what lets the frozen argument keep the row density `tau_d = 2 kappa x_T`
while it spends the query on the column side.  General. -/
theorem bob_query_preserves_rowsAt {P : Protocol X Y Z} {p : List Bool}
    (h : DenseWeightedCount.IsBobNode (DenseWeightedCount.descend P p))
    (R : Finset X) (b : Bool) :
    RoutingDynamics.rowsAt P R (p ++ [b]) = RoutingDynamics.rowsAt P R p := by
  simp only [RoutingDynamics.rowsAt, bob_query_preserves_aliceCols h b]

end BobChild

section BobChildDensity

variable {q : ℕ} {X Yc Z : Type*} [DecidableEq Yc] [Fintype Yc]

/-- **`09:1125--1132`, `eq:terminal-bob-child-density`.**  "Follow a child whose
quotient projection of `K_{ord}` has at least half its current size.  After
projection to any selected collection of ordinary bins, this child has column
density at least `(1 - eps)/2 > 2/5 > 9/25`."

The halving is the banked `exists_denser_bob_child_density`; the constant chase is
the banked `bob_child_density` at the frozen `eps < 1/5`.  Nothing is re-derived:
`1 - eps` in, a child of density strictly above the capacity guard `9/25` out.
General; the alphabet is nonempty, which is what makes the strict comparison
survive multiplication by the projection denominator.

**On the existential.**  The `exists b` is a genuine choice, not a disguised
constant: the banked `RoutingDynamics.projection_denserChild_needs_the_right_bit`
exhibits a Bob query at which the `false` child's projection is empty while the
parent's is not, so no fixed bit is a witness.  That is the frozen "*a* child
whose quotient projection ... has at least half its current size". -/
theorem stage3_bob_child_density_at_terminal {P : Protocol X (Slot q → Yc) Z}
    {p : List Bool} {ε : ℝ} (hε : ε < 1 / 5) (hYc : 0 < Fintype.card Yc)
    (h : DenseWeightedCount.IsBobNode (DenseWeightedCount.descend P p))
    (S : Finset (Slot q → Yc)) (J : Finset (Slot q))
    (hdens : (1 - ε) * (Fintype.card Yc : ℝ) ^ J.card
      ≤ ((RoutedCertificateSystem.nodeProjection P S J p).card : ℝ)) :
    ∃ b : Bool, (9 : ℝ) / 25 * (Fintype.card Yc : ℝ) ^ J.card
      < ((RoutedCertificateSystem.nodeProjection P S J (p ++ [b])).card : ℝ) := by
  obtain ⟨b, hb⟩ :=
    RoutingDynamics.exists_denser_bob_child_density (ρ := 1 - ε) h S J hdens
  refine ⟨b, ?_⟩
  have hcard : (0 : ℝ) < (Fintype.card Yc : ℝ) := by exact_mod_cast hYc
  have hpow : (0 : ℝ) < (Fintype.card Yc : ℝ) ^ J.card := by positivity
  have hd := TerminalTwoStream.bob_child_density hε
  have hlt : (9 : ℝ) / 25 < (1 - ε) / 2 := by linarith [hd.1, hd.2]
  have := mul_lt_mul_of_pos_right hlt hpow
  linarith

end BobChildDensity

/-! ## §8  Statement poles

A green build sees neither of the two failure modes below, so both are landed as
machine-checked facts. -/

/-- The physical carrier of the pole probe: two columns, one Stage-2 coordinate. -/
def poleRep : Slot 2 → Slot 1 × Slot 2 := fun i => (0, i)

/-- **Aux (the probe's quotient support is the whole fibre).** -/
theorem poleRep_quotientSupport :
    DenseBranchSelection.quotientSupport poleRep Finset.univ 0
      = (Finset.univ : Finset (Slot 2)) := by
  ext γ
  simp only [Finset.mem_univ, iff_true]
  exact DenseBranchSelection.mem_quotientSupport.2 ⟨γ, Finset.mem_univ _, rfl⟩

/-- The left-heavy routing of the pole probe: the canonical assignment sends every
duplicated value to the left child, so its right child is empty. -/
noncomputable def poleLeft :
    DenseRoutingInvariant.BobRouting poleRep Finset.univ Finset.univ 0
      (DenseBranchSelection.quotientSupport poleRep Finset.univ 0) :=
  DenseRoutingInvariant.canonicalRouting poleRep (S := Finset.univ)
    (Finset.union_self _) 0 _ (Finset.Subset.refl _)

/-- The right-heavy routing of the pole probe: the same assignment with the two
physical children swapped, through the banked `BobRouting.symm`. -/
noncomputable def poleRight :
    DenseRoutingInvariant.BobRouting poleRep Finset.univ Finset.univ 0
      (DenseBranchSelection.quotientSupport poleRep Finset.univ 0) :=
  poleLeft.symm

/-- **Statement pole 1 (the frozen "a heavier child" names a genuine choice).**
The routing rule of `09:931` cannot be replaced by a fixed side: at the probe the
canonical assignment puts everything in the left child, so the *right* child
retains nothing and the frozen retention clause fails there, while the derived
`heavierChild` selects correctly.  Hence `card_le_two_mul_heavierChild` is not a
statement about a constant function of the routing.

The carrier is self-chosen and degenerate on purpose (`canonicalRouting` is
applied with `S_0 = S_1 = univ`, so the two physical children coincide), and the
pole claims **no** legality: it exhibits the *failure* of the frozen retention
clause for a fixed side.  Like its sibling `pairArrival_split_is_reachable` on
the identical carrier, it is **NON-FIDELITY** -- machine evidence about our
encoding at a point the frozen paper never visits. -/
theorem heavierChild_needs_the_right_side :
    heavierChild poleLeft = poleLeft.left
      ∧ poleLeft.right = (∅ : Finset (Slot 2))
      ∧ ¬ ((DenseBranchSelection.quotientSupport poleRep Finset.univ 0).card
            ≤ 2 * poleLeft.right.card) := by
  have hqs : DenseBranchSelection.quotientSupport poleRep Finset.univ 0
      = (Finset.univ : Finset (Slot 2)) := poleRep_quotientSupport
  have hright : poleLeft.right = (∅ : Finset (Slot 2)) := by
    change (DenseBranchSelection.quotientSupport poleRep Finset.univ 0) \
      DenseBranchSelection.quotientSupport poleRep Finset.univ 0 = ∅
    simp
  have hleft : poleLeft.left = (Finset.univ : Finset (Slot 2)) := by
    change (DenseBranchSelection.quotientSupport poleRep Finset.univ 0) ∩
      DenseBranchSelection.quotientSupport poleRep Finset.univ 0 = Finset.univ
    rw [Finset.inter_self, hqs]
  refine ⟨?_, hright, ?_⟩
  · unfold heavierChild heavierBit
    rw [if_neg]
    simp only [decide_eq_true_eq, not_lt, hright, hleft]
    exact Nat.zero_le _
  · rw [hright, hqs]
    simp

/-- **Non-vacuity 1 (the `split` branch of the frozen pair rule is reached).**
The two probe routings choose *different* children -- one is left-heavy, the other
right-heavy -- so `pairArrival` really does produce the frozen `split` outcome,
with two distinct incomparable addresses.  Without this the whole attached-pair
dichotomy of `09:932--935` would be landed with one branch empty.

This is machine evidence about **our encoding** on a two-element fibre, at a point
the frozen paper never visits: **NON-FIDELITY**.  The fidelity statements are the
general lemmas of §2, which hold at every `BobRouting`. -/
theorem pairArrival_split_is_reachable :
    ¬ PairAgrees poleLeft poleRight
      ∧ pairArrival poleLeft poleRight []
        = DenseFrontierConservation.FrontierArrival.split
            (heavierRoute poleLeft []) (heavierRoute poleRight []) := by
  have hqs : DenseBranchSelection.quotientSupport poleRep Finset.univ 0
      = (Finset.univ : Finset (Slot 2)) := poleRep_quotientSupport
  have hleft : poleLeft.left = (Finset.univ : Finset (Slot 2)) := by
    change (DenseBranchSelection.quotientSupport poleRep Finset.univ 0) ∩
      DenseBranchSelection.quotientSupport poleRep Finset.univ 0 = Finset.univ
    rw [Finset.inter_self, hqs]
  have hright : poleLeft.right = (∅ : Finset (Slot 2)) := by
    change (DenseBranchSelection.quotientSupport poleRep Finset.univ 0) \
      DenseBranchSelection.quotientSupport poleRep Finset.univ 0 = ∅
    simp
  have hcard : (Finset.univ : Finset (Slot 2)).card = 2 := by simp
  have hbl : heavierBit poleLeft = false := by
    unfold heavierBit
    rw [hleft, hright]
    simp
  have hbr : heavierBit poleRight = true := by
    unfold heavierBit poleRight
    rw [DenseRoutingInvariant.BobRouting.symm_left, DenseRoutingInvariant.BobRouting.symm_right,
      hleft, hright]
    simp [hcard]
  have hne : ¬ PairAgrees poleLeft poleRight := by
    unfold PairAgrees
    rw [hbl, hbr]
    simp
  refine ⟨hne, ?_⟩
  unfold pairArrival
  rw [if_neg]
  rw [hbl, hbr]
  simp

/-! ## §9  Non-vacuity readouts on the Stage-3 support rule -/

/-- **Non-vacuity 2 (the whole-object route can be proper).**  On a two-element
support the frozen `P setminus P_0` really loses mass: the rule is not a disguised
identity, so `routeWhole_valid_support` is not vacuous.  A concrete arithmetic
readout about our encoding -- **NON-FIDELITY** -- whose fidelity counterparts are
the general lemmas of §5. -/
theorem routeWhole_can_be_proper :
    ({0, 1} : Finset (Slot 2)) \ ({0} : Finset (Slot 2)) = ({1} : Finset (Slot 2))
      ∧ ({0, 1} : Finset (Slot 2)) \ ({0} : Finset (Slot 2)) ≠ ({0, 1} : Finset (Slot 2)) := by
  constructor
  · decide
  · decide

/-- **Rejection probe (the Stage-3 step guard fires) -- no legality claimed.**

At the banked probe state the template bin pair has `m_T = 12`, so
`tau_0 = 2 s x_T = 1/100` and the first Stage-3 threshold is
`tau_1 = tau_0/2 = 1/200`, while deleting a *single* typed pair costs
`1/m_T^2 = 1/144`.  Since `1/144 > 1/200`, a one-pair deletion is **not** a legal
single Stage-3 routing step at those carriers, even though the banked
`routedSupport_at_probe_proper_subset` shows it is a legal *total* loss against
`tau_0`.

So the step guard of `routedSupport_of_stepwise_losses` has real content, and the
probe's granularity -- not the theorem -- is why a one-step chain cannot reproduce
that banked witness.  The values are the banked probe's own; nothing here claims
legality of any parameter choice. -/
theorem probe_single_pair_drop_is_not_one_routing_step :
    ¬ ((1 : ℝ) / 144 < TerminalTwoStream.tauAt 1 (1 / 200 : ℝ) 1)
      ∧ (1 : ℝ) / 144 < WrapperProjectionCovers.tauZero 1 (1 / 200 : ℝ) := by
  have hτ : WrapperProjectionCovers.tauZero 1 (1 / 200 : ℝ) = 1 / 100 :=
    TwoStreamState.probe_tauZero
  constructor
  · rw [TerminalTwoStream.tauAt, hτ]
    norm_num
  · rw [hτ]
    norm_num

/-- **Statement pole 2 (`RoutedSupport` is not free).**  The conclusion of
`routedSupport_of_stepwise_losses` is a real constraint: at the banked probe state
the *empty* support is not a routed support, because its loss `143/144` exceeds
`tau_0 = 1/100`.  A routing chain therefore cannot end anywhere, and the theorem's
step hypotheses are doing work.

Machine evidence about our encoding at the banked probe -- **NON-FIDELITY**, since
that probe sits at `q_2 = 2` and hence outside `eq:terminal-entry`. -/
theorem routedSupport_is_not_free :
    ¬ TerminalStageThreeLift.RoutedSupport TwoStreamState.probeState
        (∅ : Finset (TwoStreamState.ProbeCl × TwoStreamState.ProbeCl)) := by
  rintro ⟨-, hloss⟩
  have hPs : TwoStreamState.probeState.Pstar = TwoStreamState.probePstar := rfl
  rw [hPs] at hloss
  rw [Finset.sdiff_empty, TwoStreamState.probePstar_card, TwoStreamState.probe_tauZero] at hloss
  norm_num at hloss

end EthInapproximability.ParameterizedNP.Stage3ProtocolRouting
