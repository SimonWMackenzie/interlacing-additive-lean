import EthInapproximability.ParameterizedNP.TerminalFixedBin

/-!
# Parameterized NP route: the Stage-3 selector lift (terminal phase 2)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand this round), **lines 1035--1173** -- the **second** of
  the two phases the frozen proof of `lem:terminal-two-stream` announces at
  `09:867--868`:

  > "We first prove a lower bound one bit above `D_2` inside a fixed Stage-3
  > bin, and then lift that bit through the Stage-3 selector."

  Phase 1 is the predecessor module `TerminalFixedBin` (`09:862--1033`); this
  module is phase 2, opening at the frozen italic heading *Lifting the extra bit
  through Stage 3* (`09:1035--1036`) and stopping at `09:1173`, the frozen
  "Therefore no protocol of depth `C - 1` computes `Z`, and `comp Z >= C`, as
  claimed."  The anchors traced, in the order the frozen block prints them:
  * `09:1037--1038`, the Stage-3 frame: "suppose for contradiction that `Z` has
    a protocol `P_3` of depth at most `C - 1 = D_2 + log_2 s`, and put
    `r_3 = log_2 s`", with `09:1038--1039` "Every remaining-budget reference in
    this second part is to the suffix depth in `P_3`."
  * `09:1039--1044`, the transposition to the Stage-3 selector orientation and
    the party assignment that "determines the stopping rule below: the
    row-support ladder is routed through Alice queries, and the ordinary column
    set remains unchanged until the first Bob query."
  * `09:1046--1054`, the baseline-bin start, the distinguished-bin attachment
    ("This is one object of weight two"), and the Alice row ladder
    `tau_d = 2 s x_T 2^{-d}` -- the ladder itself consumed **by pin** from the
    banked `TerminalTwoStream.tauAt` and never restated.
  * `09:1055--1067`, the split-or-route support rule.
  * `09:1068--1076`, "an attached object that remains unsplit loses strictly
    less than `sum_{d >= 0} tau_{d+1} = tau_0` of its typed physical support.
    Clause (v) and `eq:terminal-selector-data` then leave transferred typed
    density at least `49/64`."
  * **`09:1076--1082`**, the sentence this module's central section formalizes:
    "Until the first Bob query, these Alice restrictions do not change the
    ordinary and foreign fibre sets `O_alpha, F_alpha`, so the averages
    `eq:terminal-averages` are unchanged.  The Stage-2 calculation above
    therefore applies verbatim to the routed fixed-bin restriction and again
    gives residual complexity at least `D_2 + 1`.  **We use this refreshed
    certificate, rather than restriction monotonicity**, at every selector
    isolation node and in the capacity-one case below."
  * `09:1084--1095`, the stopping rule, the column density `1 - eps > 4/5 > 3/5`,
    the row floor `tau_d >= tau_{r_3} = 2 x_T`, and "no ordinary object can stop
    at a protocol leaf by depth `r_3`".
  * `09:1097--1106`, the isolation capacity `kappa_v = 2^{r_3-d_v}`, the
    capacity-one exclusion ("then `d_v = r_3`, only `D_2` protocol bits remain,
    and `eq:terminal-fixed-bin` requires `D_2 + 1`"), and `h_v + z_v <= kappa_v`.
  * `09:1107--1110`, the premature-leaf exclusion at depth `r_3 + 1`.
  * `09:1112--1123`, the first-Bob frontier substitution: "The stopping nodes
    therefore satisfy the hypotheses of `lem:dense-weighted-frontier` with the
    names of Alice and Bob interchanged.  Here all `s` ordinary bins are
    present, there is one attached bonus component, and there is no defective
    bin.  Equivalently, the weighted count has `b = 0` and `w = 1.`", yielding
    `eq:terminal-first-bob` (label `09:1122`, display `09:1118--1123`).
  * `09:1125--1132`, the Bob child and `eq:terminal-bob-child-density`.
  * `09:1133--1150`, the certified-scale row ladder at `M = S_2`, `H = D_2`,
    `x = x_T`, `z = y = 3/5`, its `ell = 1` and `ell = log_2 kappa` instances
    (`eq:terminal-stage3-two-copy`, `eq:terminal-stage3-odd-copy`), the scale
    guard `H >= 2` and the legality `kappa <= s < 2^{b_T}` -- all **banked** in
    `TerminalTwoStream` and consumed here by pin.
  * `09:1152--1161`, the three-case dispatch on `kappa`.
  * `eq:terminal-stage3-budget` (label `09:1170`, display `09:1167--1171`) and
    the closing contradiction `09:1172--1173`.
* **Cross-anchors opened first-hand for this tranche:** `09:482--656`
  (`def:two-stream-state`, in particular clause (i)'s two averages `09:539--546`
  and clause (v)'s universal transfer `09:633--652` with
  `eq:terminal-selector-data`), `09:658--832` (`lem:terminal-state-realization`,
  whose proof's closing `09:828--831` records that "the selector argument spends
  `tau_0` only when it replaces `P_*` by its routed subset"), `09:834--860`
  (`lem:terminal-two-stream`'s statement, whose binder set this phase inherits),
  `09:862--1033` (phase 1, to fix exactly what `eq:terminal-fixed-bin` says and
  what the predecessor module leaves open), and `08:946--1134`
  (`sec:dense-weighted-count` and `lem:dense-weighted-frontier`, the abstract
  lemma `09:1112--1116` substitutes into with `b = 0`, `w = 1`).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively; the sole import is `TerminalFixedBin`,
  whose ledger row records the same exclusion.  No axiom, no opaque
  conclusion-bearing certificate, and no `Stage12` reachability is introduced.

## Consumed by pin (never restated)

* `EthInapproximability.ParameterizedNP.TerminalTwoStream`: `terminalTarget`,
  `terminalTarget_sub_one`, `terminalEntry`, `terminalSeedInputs`,
  `ExtensionCallTwoFixedWidth`, `extensionCallTwo`, `tauAt` and its four
  readouts (`tauAt_zero`, `tauAt_succ`, `tauAt_stage3_frontier`,
  `tauAt_partial_loss_lt`), `ordinary_column_density`, `bob_child_density`,
  the certified-scale Stage-3 instances (`stage3_two_copy_of_seedInputs`,
  `stage3_odd_copy_of_seedInputs`, `scale_guard`, `row_density_legal`,
  `row_density_legal_at_capacity`, `two_xT_le_one`), `odd_copy_selection`,
  `stage3_budget`, `stage3_contradiction`, `probeWidths`,
  `probeEntry_is_nondegenerate`, and the headline claim `TerminalTwoStream`.
  **None of these is redefined here.**  The Stage-3 arithmetic that module
  already banked is *used*, and the new content is exactly the phase-2 steps its
  GAP-EXPOSED 2 lists as not declared.
* `EthInapproximability.ParameterizedNP.TerminalFixedBin`: `fixedBinTarget`,
  `fixedBinRows`, `fixedBinCols`, `fixedBinRows_nonempty`,
  `fixedBinCols_nonempty`, `fixedBinRows_subset`, `fixedBinCols_subset`,
  `fixedBin_le_state`, `FixedBinLowerBound`,
  `fixedBin_bound_is_strictly_weaker_than_C`, `stage2_capacity_one_excess`
  (the frozen `09:1156--1161` capacity-one dichotomy is *the same statement* as
  `09:1021--1023` and is therefore consumed, not restated), and the Stage-2
  isolation machinery `stage2_isolation_capacity`.
* `EthInapproximability.ParameterizedNP.TwoStreamState`: the record
  `TwoStreamState` with its clause-(i) averages `ordinary_density`,
  `foreign_density`, its clause-(ii) `physical_pair_density`, and its clause-(v)
  fields `uniform_transfer` and `selector_gate`; `probeState`, `probePstar`,
  `probe_tauZero`, `fixedBin_of_uniform`.  `def:two-stream-state` is **never**
  restated: the routed support below is a *predicate on the banked record*.
* `WrapperProjectionCovers.tauZero` (`09:376`), `.aMin` / `.rhoPair`
  (`09:380--383`); `DenseBranchSelection.Dtwo` (`08:152`);
  `DenseWeightedCount.stoppingCapacity` (`08:986--989`),
  `.two_le_stoppingCapacity_of_lt`, `.isolationNode_capacity_at_depth`,
  `.aliceNodes`, `.isolationNodes`, `.PrefixFreeFrontier`;
  `DenseFrontierConservation.FrontierArrival`, `.hMass`, `.zMass`,
  `.witnessCount`; `DenseWeightedFrontier.denseWeightedFrontier`
  (`lem:dense-weighted-frontier`, applied never restated);
  `DenseStageFourOpening.xTdepth` (the frozen `x_T = 2^{-b_T}` pin);
  `NPCC.D_subgame_mono`, `Workspace.Types.CommComplexity.D`, `NPCC.subgame`,
  `Workspace.Types.Interlace.interlaceFun` -- the vendored, project-axiom-free
  complexity interface reached through `LegacyNPCC.Core`.

## What is new here, and what is deliberately still open

**New (the phase-2 steps the two predecessor modules list as not declared).**

1. The Stage-3 frame of `09:1037--1038` as `stageThreeBudget`, with the exact
   two-phase arithmetic `stageThreeBudget + 1 = fixedBinTarget + r_3` and the
   residual identity at every depth `d <= r_3`.
2. **The refreshed fixed-bin certificate of `09:1076--1082`.**  `RoutedSupport`
   is the frozen clause-(v) hypothesis "`P' subseteq P_*` losing less than
   `tau_0` of `m_T^2`" as a predicate on the banked record;
   `routed_transfer_density` **proves**, from `uniform_transfer` and
   `selector_gate`, that every routed support still transfers typed density
   `49/64`; `routed_averages_are_column_free` records the *structural half* of
   `09:1076--1078` -- the two clause-(i) averages are functions of the row stream
   data alone, so the routed support cannot disturb their statements -- and
   **not** the frozen invariance of the fibre sets `O_alpha, F_alpha`, which is
   GAP-EXPOSED 7; and `stage2_inputs_at_routed_support` bundles the two, which is
   the frozen "the Stage-2 calculation above therefore applies verbatim to the
   routed fixed-bin restriction" read at exactly that strength.
   `RefreshedFixedBinBound` is the resulting named claim, quantified over
   **every** routed support.
3. `refreshedFixedBinBound_gives_fixedBin`: taking `P' = P_*` recovers
   `eq:terminal-fixed-bin`'s conclusion, so the refreshed certificate is a
   genuine **strengthening** of phase 1 and never a weakening of it.
4. `monotonicity_runs_the_wrong_way`: the machine-checked reason the frozen text
   says "rather than restriction monotonicity".  `D_subgame_mono` on the routed
   column carrier points from the routed restriction *up* to the full fixed-bin
   restriction, i.e. away from what the selector argument needs, so no amount of
   monotonicity turns phase 1's single bound into the refreshed one.
5. The Stage-3 row ladder at a reached capacity: `tauAt_antitone` (the frozen
   `tau_d >= tau_{r_3}`), `tauAt_eq_two_mul_capacity` (the frozen
   `tau_d = 2 kappa x_T` of `09:1134`), its consistency with the banked frontier
   evaluation, and its strict positivity.
6. The three Stage-3 budget facts of `09:1097--1110` in **additive** form: the
   capacity-one exclusion against `eq:terminal-fixed-bin`, its contrapositive
   supplying the frontier's `htwo` premise, the isolation-capacity bound
   `h_v + z_v <= kappa_v`, and the premature-leaf exclusion at depth `r_3 + 1`.
7. **The frozen first-Bob frontier substitution `09:1112--1123`**:
   `terminal_first_bob` applies the banked `lem:dense-weighted-frontier` at
   `Coord = [s]`, `r = r_3`, `b = 0` and `w = 1`, discharging its width
   hypothesis from `s = 2^{r_3}` and its **gap** hypothesis outright from
   `b = 0` ("there is no defective bin").  This is a *derivation* of
   `eq:terminal-first-bob`, not an assumption of it.
8. The three-case dispatch of `09:1152--1161` at the Stage-3 capacities
   (`stage3_capacity_trichotomy`, `stage3_selection_at_capacity`,
   `stage3_selection_at_capacity_two`) and the closing budget comparison
   `stage3_bob_child_exceeds` (`eq:terminal-stage3-budget`).
9. `StageThreeLift` itself, as the named phase-2 claim about the pinned
   construction, and `terminalTwoStream_of_phases`, the binder-bookkeeping
   readout showing that phase 2 plus the refreshed phase-1 certificate compose
   to the frozen headline with nothing added.

**Deliberately open (GAP-EXPOSED).**

1. **`StageThreeLift` is not proved.**  It is landed as a named claim, letter
   exact against `09:1035--1173`, and *stated only*.  No declaration below has
   it as a conclusion, and in particular there is **no** theorem deriving it
   from an assumed first-Bob verdict: an "assume `eq:terminal-first-bob` and
   conclude `C`" shell would typecheck and establish nothing, which is exactly
   the statement pole this module refuses.  `terminal_first_bob` runs the other
   way -- it *produces* the frontier verdict from the counting.
2. **`eq:terminal-fixed-bin` is still not proved, and this module does not
   pretend to prove it.**  `TerminalFixedBin.FixedBinLowerBound` remains
   stated-only, and its refreshed form `RefreshedFixedBinBound` enters phase 2
   as an **explicit binder**, never as a conclusion.  The gating dependency is
   disclosed rather than absorbed: it is the predecessor module's
   **GAP-EXPOSED 2, the protocol-side routing** -- the split-or-route support
   rule, the stopping rule and coordinate isolation, the one-copy and top
   two-copy residual certificates, the Alice child selection and the Localized
   Extension invocation.  Until those land, phase 1 is unprovable and therefore
   the refreshed certificate is unprovable; this module states exactly which
   object it is waiting for and proves everything on this side of it.
3. **The Stage-3 protocol-side routing is likewise not modelled.**  The
   split-or-route rule of `09:1055--1067`, the stopping rule of `09:1084--1095`,
   the Bob child selection of `09:1125--1128`, and the coordinate isolation are
   **not** declared.  What is landed is every arithmetic, counting and
   density-transfer phase those steps consume or produce, at the frozen
   constants.
4. **`sec:wrapper-projection-covers` is untouched.**  This block **feeds**
   `hDenseRung` and neither discharges nor narrows it; the ranges
   `09:1184--1366`, `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly as
   `ScaleAlignOpening` records them, and **no route completion is claimed**.
5. **The headline `lem:terminal-two-stream` is not concluded here.**
   `terminalTwoStream_of_phases` is an implication whose antecedents are two
   *unproved* named claims; it proves no mathematics, and
   `stageThreeLift_conclusion_is_not_the_binder` records, as a machine-checked
   fact, that the phase-2 conclusion is exactly `r_3` bits above the certificate
   it consumes, so nothing here can be mistaken for the headline.
6. **The Localized Extension corollary's conclusion is not asserted**, exactly
   as both predecessor modules record: `extensionCallTwo` and
   `ExtensionCallTwoFixedWidth` are consumed by pin, and `eq:certified-E3` is
   asserted nowhere.
7. **The fibre-set invariance of `09:1076--1078` is not transcribed** (recorded
   by repair F-3).  The frozen sentence claims that the Alice restrictions "do
   not change the ordinary and foreign fibre sets `O_alpha, F_alpha`"; this
   module builds no model of those sets under a restriction, so that claim is
   **not** a theorem here.  `routed_averages_are_column_free` carries only its
   structural consequence -- the two clause-(i) averages never mention the column
   support -- and its name now says so.

### Successor record (comment-only; nothing above is restated or weakened)

**GAP-EXPOSED 3 is discharged except for coordinate isolation, which passes to
`Stage3ProtocolRouting`'s own GAP-EXPOSED 3.**  GAP-EXPOSED 3 above names four
items; `EthInapproximability.ParameterizedNP.Stage3ProtocolRouting` (tranche
`cc-t4k`) lands three of them -- the split-or-route rule (`09:931--935`,
`09:1055--1067`), the two stopping rules (`09:937--951`, `09:1084--1095`), and
the Bob child selection (`09:1125--1132`) -- together with the residual
certificates as explicit binders and the Alice child and Localized Extension
composition (`09:1004--1028`).  **Coordinate isolation is not discharged**: that
module records, in its own GAP-EXPOSED 3, that it builds no isolation *test* and
only proves the budget facts holding at such a node.  Two further points of that
module bear on how the text above should be read, and neither edits it:

* Its `routedSupport_of_stepwise_losses` proves that a chain of Stage-3 routing
  steps produces a support satisfying `RoutedSupport` above, so the routing
  provably lands **inside** the quantifier of `RefreshedFixedBinBound`.  That is
  the *input* to GAP-EXPOSED 2's discharge, not the discharge: phase 1 still
  needs its certificate readings, and `RefreshedFixedBinBound` remains a binder.
* The deferred canonical-inhabitation obligation registered on
  `RefreshedFixedBinBound` is **unchanged** and is not discharged there.

## Canonical inhabitation

`RoutedSupport` and `RefreshedFixedBinBound` are predicates on the banked
`TwoStreamState` record, so the paper's own instance -- the state produced by
`lem:terminal-state-realization` (`09:658--832`) -- is the object they speak
about by construction, and every general lemma below
(`routed_transfer_density`, `routed_averages_are_column_free`,
`routedSupport_nonempty`, `routedFixedBinCols_nonempty`,
`refreshedFixedBinBound_gives_fixedBin`, `monotonicity_runs_the_wrong_way`) is
proved **at every state**, hence at the paper's.  That is strictly stronger than
a synthetic inhabitant.

The concrete readouts `routedSupport_at_probe_proper_subset` and
`routed_carrier_nonempty_at_probe` evaluate the new predicate at the banked
`TwoStreamState.probeState` and are labelled **NON-FIDELITY**: that probe sits
at `q_2 = 2` and therefore outside `eq:terminal-entry` (the banked
`TerminalTwoStream.bankedProbeWidth_is_not_a_terminal_entry_width` records
exactly this), so they are machine evidence about *our encoding*, never a
witness that the frozen terminal regime is inhabited.  What they *do* establish
is that `RoutedSupport` is not satisfied only at `P' = P_*`: the probe's loss
budget `tau_0 m_T^2 = 144/100 > 1` permits a **proper** routed subset, so the
predicate is not a disguised equality.

`StageThreeLift` is a claim, not a carrier: it has no inhabitation obligation of
its own, and its discharge is the arc's later assembly round.  The **deferred
canonical-inhabitation obligation** registered by this tranche is therefore the
one on `RefreshedFixedBinBound`: it is discharged only when the protocol-side
routing lands and phase 1 becomes provable, never by the probe readouts above.

## Reader counterparts

Frozen release, `reader-facing/`, opened first-hand for this round
(`sections/A-stage4-details.tex`, SHA-256
`5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`,
recomputed this round).

**No declaration below claims a reader item, and that is a finding about the
reader artifact rather than an omission here.**  Searched first-hand across all
nine reader section files for the phase-2 vocabulary: `r_3`, `tau_d`, `tau_0`,
"first Bob", "bonus", `49/64`, `3/5` in the terminal sense, the Stage-3
capacities and both budget displays `eq:terminal-stage3-budget` /
`eq:terminal-first-bob` occur **nowhere**.  The reader compresses the entire
Stage-3 lift into two prose sentences -- `A-stage4-details.tex` **lines
387--390** ("At the frontier, the two-stream lemma combines the ordinary `M_1`
robustness, the auxiliary `M_2` robustness, the product-family transfer, and the
Stage--3 selector to contribute the missing bit") and **lines 319--322** ("There
the terminal two-stream argument combines the protected structure with the
inherited Stage--1 and Stage--2 robustness and the Stage--3 selector to recover
the missing bit") -- and then says at **396--399** that the count "is expanded
line by line in the ultra-explicit companion", which is exactly the frozen
`09:1035--1173` traced here.  Both sentences are **prose**, and the
reader-counterpart discipline bars citing prose as a statement counterpart;
`387--390` was already recorded as unclaimed prose by `TerminalFixedBin` and is
**not** reclaimed, and `319--322` is recorded here as navigation only.  Reader
line **391** stays assigned to `TerminalTwoStream`'s certified-row-ladder group,
`374` and `396--399` stay the unclaimed prose `WrapperProjectionCovers`
recorded, and `361--368` stays assigned to `WrapperLowRungs.wrapperLowRungs`.
No reader item is assigned twice.

## Aux-lemma battery

Every battery item is **proved**; nothing is stated and left open.

* `A` the Stage-3 frame, general (5): `stageThreeBudget_eq_terminalTarget_sub_one`,
  `stageThreeBudget_succ`, `stageThreeBudget_eq_fixedBin_add`,
  `stage3_residual_at_depth`, `stage3_depth_lt_budget`.
* `B` the routed selector support and the refreshed certificate, general in the
  state (7): `stage3_width_pos`, `aMin_sub_tauZero_pos`,
  `routedSupport_card_gt`, `routedSupport_nonempty`,
  `routedFixedBinCols_subset`, `routedFixedBinCols_subset_state`,
  `routedFixedBinCols_nonempty`.
* `C` the frozen re-derivation of `09:1074--1082`, general in the state (4):
  `routed_transfer_density`, `routed_averages_are_column_free`,
  `stage2_inputs_at_routed_support`, `refreshedFixedBinBound_gives_fixedBin`.
* `D` the Stage-3 Alice row ladder, general (4): `tauAt_antitone`,
  `tauAt_eq_two_mul_capacity`, `tauAt_capacity_at_frontier`, `tauAt_pos`.
* `E` the Stage-3 exclusions and the isolation capacity, general (4):
  `stage3_capacity_one_exclusion`, `stage3_unsplit_forces_capacity_two`,
  `stage3_isolation_capacity`, `stage3_premature_leaf_exclusion`.
* `F` the first-Bob frontier substitution, general (1): `terminal_first_bob`.
* `G` the Stage-3 dispatch and the closing budget, general (4):
  `stage3_capacity_trichotomy`, `stage3_selection_at_capacity`,
  `stage3_selection_at_capacity_two`, `stage3_bob_child_exceeds`.

That is **29 general battery entries proved**, with `0` unproved, alongside
**three statement poles** (`monotonicity_runs_the_wrong_way`,
`first_bob_needs_the_bonus_component`,
`stageThreeLift_conclusion_is_not_the_binder`), one composition readout
(`terminalTwoStream_of_phases`) and **three non-vacuity readouts**
(`routedSupport_at_probe_proper_subset`, `routed_carrier_nonempty_at_probe`,
`stageThreeLift_arith_hypotheses_consistent`).

## Statement-level repairs applied in tranche `cc-t4k`

The four findings this row carried forward unrepaired -- each recorded as needing
a statement edit or a rename and a fresh judged round -- are applied here.  No
declaration is added or removed, no statement is weakened, and the two renames are
mechanical (every call site and the axiom audit move with them).

* **F-3.**  `routed_averages_unchanged` was named for the whole frozen sentence
  `09:1076--1078` while proving only its structural consequence.  Renamed to
  `routed_averages_are_column_free`, with a docstring that states exactly what is
  and is not established, and the untranscribed fibre-set invariance recorded as
  the new **GAP-EXPOSED 7**.  The bundling readout
  `stage2_inputs_at_routed_support` now records the asymmetry between its two
  conjuncts.
* **F-4.**  `stage3_no_ordinary_leaf` was named for the protocol-leaf sentence of
  `09:1093--1095` while its content is the arithmetic `d < stageThreeBudget`.
  Renamed to `stage3_depth_lt_budget`; the protocol-semantic half is
  `Stage3ProtocolRouting.stage3_object_not_leaf`.
* **F-5.**  `stageThreeLift_arith_hypotheses_consistent` wrote the bare numeral
  `3` for the Stage-3 exponent where the banked pin `TerminalTwoStream.probeR₃`
  exists.  Every occurrence now goes through the pin.
* **F-6.**  The fourth conjunct of `first_bob_needs_the_bonus_component` was
  `¬ (4 * 0 < 0)` -- the gap hypothesis at the unsubstituted `w = 0` -- while its
  docstring described the hypothesis `terminal_first_bob` actually discharges,
  `hgap : 4 * 0 < 1`.  The conjunct now states the latter, which **holds** at the
  probe, so the pole's substance is visibly located in the `hbonus` and conclusion
  conjuncts.

F-1, F-2, F-7 and F-8 were already repaired under the record-only boundary and are
untouched.

## HYPOTHESIS-CONSISTENCY note on `StageThreeLift`

The claim's binder set is `TerminalTwoStream`'s **plus one**: the refreshed
fixed-bin certificate.  Adding a hypothesis can only make the claim weaker than
the frozen headline, which is the correct direction for a phase the later
assembly must combine with phase 1; `terminalTwoStream_of_phases` records the
combination.  Nothing is dropped: the width record, the dyadic convention
`s = 2^{r_3}`, both checked-identity pins `x_T = 2^{-b_T}` and `y = 3/5`,
`eq:terminal-entry`, `eq:terminal-seed-inputs`, the call-(ii) fixed-width binder
and the `forall`-form reached-capacity Extension binder are token-identical with
the headline's.

Consistency is inherited and extended.  The arithmetic sub-bundle is exhibited
by `stageThreeLift_arith_hypotheses_consistent` simultaneously at the banked
**balance-minimum** width record `TerminalTwoStream.probeWidths` -- legal for the
four proof fields of `StageTwoRelaxed.StageTwoWidths` and **not** a legal
schedule width record, its `k_2 = 5` failing the `eq:t2-search` floor
`k_2 >= max{4, 2^{19}, m_HS}` (`06:766`) -- at `r_2 = 7`,
`b_1 = 24`, so `q_2 = 128`, `t_2 = 32`, a nondegenerate `B_cap = 5`, a
nondegenerate Stage-3 exponent `r_3 = 3`, and a nondegenerate
`eps = 1/100`, `delta' = 1/10`: `eq:terminal-entry` holds, the three Stage-3
targets are the nondegenerate `15`, `16`, `13`, **both** Stage-3 exclusions fire,
and the capacity trichotomy is reached at both ends (`kappa = 8 >= 4` at the
root, `kappa = 1` at the frontier), so neither the odd-copy branch nor the
capacity-one branch is vacuous.  (The middle `kappa = 2` branch is *not*
exhibited by that readout.)  The added binder is consistent with the rest for a
structural reason,
not by inspection: `refreshedFixedBinBound_gives_fixedBin` shows it implies the
phase-1 conclusion, whose own consistency the predecessor module already
recorded, and `routedSupport_at_probe_proper_subset` shows its quantifier ranges
over more than the trivial support.  A satisfiable collection cannot yield
`False`, so no derivation of `False` from these binders can go through.

What is *not* established, exactly as both predecessor modules record: this
module does **not** exhibit a `TwoStreamState` record sitting inside the terminal
regime, and does not claim the two `Lambda` clauses of `eq:terminal-seed-inputs`
simultaneously realizable -- they are two inherited certificates about two
different matrices, carried separately and never conjoined as cases of one
construction.  Note also that `probeWidths` -- legal for the four proof fields
of `StageTwoRelaxed.StageTwoWidths`, not for the schedule -- sits **outside the
gate-firing regime**; the gate-firing consistency readout is
`TerminalTwoStream.terminalTwoStream_r2_hypotheses_consistent` at
`extProbeWidths`, itself a BEYOND-PAPER record below the `eq:t2-search` floor
(`06:766`).  (Terminology and legality reading repaired at `cc-t7p`, ledger item
`(b11)`; "certified regime" and the unqualified "legal width record" are
WITHDRAWN.)
-/

namespace EthInapproximability.ParameterizedNP.TerminalStageThreeLift

open Finset
open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.TwoStreamState
open EthInapproximability.ParameterizedNP.TerminalTwoStream
open EthInapproximability.ParameterizedNP.TerminalFixedBin

/-! ## Section 1  The Stage-3 frame (`09:1037--1038`)

"suppose for contradiction that `Z` has a protocol `P_3` of depth at most
`C - 1 = D_2 + log_2 s`, and put `r_3 = log_2 s`."  `D_2` is the banked
`DenseBranchSelection.Dtwo` and `C` the banked `TerminalTwoStream.terminalTarget`;
neither is redefined, and `r_3` is carried as the exponent itself so that no
`Nat.log` enters where the frozen text writes a width. -/

/-- **`09:1037--1038`.**  `C - 1 = D_2 + log_2 s`, the alleged Stage-3 protocol
depth that the frozen contradiction spends.  Written additively at the frozen
exponent `r_3`, so that the `- 1` of the frozen display never becomes a
truncated natural subtraction.  General in the three exponents. -/
def stageThreeBudget (bcap r₂ r₃ : ℕ) : ℕ := DenseBranchSelection.Dtwo bcap r₂ + r₃

/-- **Aux A1 (`09:1038` against the banked target).**  The additive form agrees
with the banked truncated one.  General. -/
theorem stageThreeBudget_eq_terminalTarget_sub_one (bcap r₂ r₃ : ℕ) :
    terminalTarget bcap r₂ r₃ - 1 = stageThreeBudget bcap r₂ r₃ :=
  terminalTarget_sub_one bcap r₂ r₃

/-- **Aux A2.**  One more bit than the alleged protocol is exactly the frozen
target `C`, which is what the closing contradiction of `09:1172--1173` converts
the refuted protocol into.  General. -/
theorem stageThreeBudget_succ (bcap r₂ r₃ : ℕ) :
    stageThreeBudget bcap r₂ r₃ + 1 = terminalTarget bcap r₂ r₃ := by
  simp only [stageThreeBudget, terminalTarget]

/-- **Aux A3 (`09:867--868` made exact at the phase boundary).**  The frozen
two-phase split, read at the Stage-3 budget: the bit phase 1 proves plus the
`log_2 s` bits phase 2 lifts is precisely `C`.  This is the arithmetic that says
the two modules together cover the frozen proof and neither overlaps the other.
General. -/
theorem stageThreeBudget_eq_fixedBin_add (bcap r₂ r₃ : ℕ) :
    stageThreeBudget bcap r₂ r₃ + 1 = fixedBinTarget bcap r₂ + r₃ := by
  simp only [stageThreeBudget, fixedBinTarget, DenseBranchSelection.Dtwo]
  omega

/-- **Aux A4 (`09:1038--1039`, the suffix-depth convention).**  "Every
remaining-budget reference in this second part is to the suffix depth in `P_3`."
At suffix depth `d <= r_3` the alleged protocol has spent `d` bits and retains
`D_2 + (r_3 - d) = D_2 + log_2 kappa_v` of them, at the reached capacity
`kappa_v = 2^{r_3 - d}`.  Stated as an identity so that no natural subtraction
enters.  General. -/
theorem stage3_residual_at_depth (bcap r₂ r₃ d : ℕ) (hd : d ≤ r₃) :
    stageThreeBudget bcap r₂ r₃ = d + (DenseBranchSelection.Dtwo bcap r₂ + (r₃ - d)) := by
  simp only [stageThreeBudget]
  omega

/-- **Aux A5 (`09:1093--1095`, the *budget* half; renamed by repair F-4).**

The frozen sentence is "no ordinary object can stop at a protocol leaf by depth
`r_3`", and it has a protocol-semantic half (a leaf has cost `0`, so a node whose
residual game is `D_2`-hard is not a leaf) and an arithmetic half (at depth
`d <= r_3` the alleged protocol has not yet exhausted its budget).  **Only the
arithmetic half is this theorem**, and the name now states its content: the
suffix depth is strictly below the Stage-3 budget.  The scale guard
`09:1148--1149` supplies `D_2 >= 2` at the frozen `q_2 >= 16`.

The protocol-semantic half is `Stage3ProtocolRouting.stage3_object_not_leaf`,
which is where the frozen no-leaf sentence is actually discharged.  General. -/
theorem stage3_depth_lt_budget {r₂ : ℕ} (bcap r₃ d : ℕ) (hd : d ≤ r₃)
    (hq : 16 ≤ 2 ^ r₂) : d < stageThreeBudget bcap r₂ r₃ := by
  have h2 := scale_guard bcap r₂ hq
  simp only [stageThreeBudget]
  omega

/-! ## Section 2  The routed selector support (`09:1060--1073`, `09:633--652`)

The Stage-3 route replaces the clause-(ii) support `P_*` by a routed subset `P'`:
`09:1065--1067` routes an object to a child using `P setminus P_0`, and
`09:1068--1073` bounds the *total* loss of an unsplit attached object by
`sum_{d >= 0} tau_{d+1} = tau_0`.  Clause (v) of `def:two-stream-state`
(`09:633--652`) is stated for exactly that hypothesis, and its closing sentence
records the reason: "the later Stage-3 route charges the loss `tau_0` exactly
once."

`RoutedSupport` is therefore not a new structure -- it is the clause-(v)
hypothesis, named, as a predicate on the banked record. -/

section AtState

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
variable {q s q₂ mT dT : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
  {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
  {RG RSig RD : Finset Rw} {omg : Rw → Om} {rho : Slot s → Om → Slot q₂ × Cone}
  {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
  {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)} {lamT eps2 xT ε δ' : ℝ}

/-- **`09:633--637` named.**  A *routed selector support* for a two-stream
terminal state is a subset `P'` of the clause-(ii) support `P_*` whose loss is
strictly below the frozen selector budget `tau_0 = 2 s x_T`.  This is verbatim
the antecedent of the record's `uniform_transfer` field; nothing is added and
nothing is weakened.  General in the state. -/
def RoutedSupport
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (P' : Finset (Cl × Cl)) : Prop :=
  P' ⊆ st.Pstar ∧
    ((st.Pstar \ P').card : ℝ) / (mT : ℝ) ^ 2 < WrapperProjectionCovers.tauZero s xT

/-- **Aux B1 (the Stage-3 width is positive at every state).**  The record
stores a selected template bin `p_o : [s]`, so `s >= 1` with no extra binder.
This is what stops `tau_0 = 2 s x_T` from degenerating.  General in the state. -/
theorem stage3_width_pos
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    0 < s :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) st.pOrd.isLt

/-- **Aux B2 (`eq:terminal-selector-data` forces a positive routing margin).**
The record's `selector_gate` field, `49/64 <= (a_min - tau_0)/(1 + eps_2)^2`,
already forces `a_min > tau_0` -- with no positivity hypothesis on `eps_2`,
because a vanishing denominator would make the quotient `0` and refute the gate.
This is the estimate every routed statement below runs on.  General in the
state. -/
theorem aMin_sub_tauZero_pos
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    0 < WrapperProjectionCovers.aMin WrapperProjectionCovers.rhoPair lamT
      - WrapperProjectionCovers.tauZero s xT := by
  have hgate := st.selector_gate
  have hden : (0 : ℝ) < (1 + eps2) ^ 2 := by
    rcases (sq_nonneg (1 + eps2)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, div_zero] at hgate
      linarith
  have hmul := (le_div_iff₀ hden).mp hgate
  nlinarith

/-- **Aux B3 (`09:1068--1073` in density form).**  A routed support keeps
strictly more than `a_min - tau_0` of the two template bins: the clause-(ii)
density `|P_*|/m_T^2 >= a_min` minus a loss strictly below `tau_0`.  This is the
frozen "loses strictly less than `tau_0` of its typed physical support", read as
a lower bound on what survives.  General in the state. -/
theorem routedSupport_card_gt
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (hP : RoutedSupport st P') :
    WrapperProjectionCovers.aMin WrapperProjectionCovers.rhoPair lamT
        - WrapperProjectionCovers.tauZero s xT
      < (P'.card : ℝ) / (mT : ℝ) ^ 2 := by
  obtain ⟨hsub, hloss⟩ := hP
  have hcard : (st.Pstar \ P').card + P'.card = st.Pstar.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hcastR : ((st.Pstar \ P').card : ℝ) + (P'.card : ℝ) = (st.Pstar.card : ℝ) := by
    exact_mod_cast hcard
  have hsplit : ((st.Pstar \ P').card : ℝ) / (mT : ℝ) ^ 2 + (P'.card : ℝ) / (mT : ℝ) ^ 2
      = (st.Pstar.card : ℝ) / (mT : ℝ) ^ 2 := by
    rw [← add_div, hcastR]
  have hdens := st.physical_pair_density
  linarith

/-- **Aux B4 (a routed support is never empty).**  Combining Aux B2 and Aux B3,
the surviving density is strictly positive, so `P'` is nonempty at **every**
state and every routed support.  Without this the Stage-3 route could pass
through an empty Alice carrier, at which the refreshed certificate would be a
bound on an empty matrix.  General in the state. -/
theorem routedSupport_nonempty
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (hP : RoutedSupport st P') :
    P'.Nonempty := by
  have hpos : (0 : ℝ) < (P'.card : ℝ) / (mT : ℝ) ^ 2 :=
    lt_trans (aMin_sub_tauZero_pos st) (routedSupport_card_gt hP)
  rcases Finset.eq_empty_or_nonempty P' with he | hne
  · rw [he] at hpos
    simp at hpos
  · exact hne

omit [Fintype Cl] in
/-- **Aux B5 (the routed Alice carrier sits inside the fixed-bin one).**  The
banked column carrier `fixedBinCols` is already general in the support it images,
so the routed carrier needs no new definition: it is `fixedBinCols P' sigma_*`.
General. -/
theorem routedFixedBinCols_subset {P' Pstar : Finset (Cl × Cl)} (hsub : P' ⊆ Pstar)
    (sigmaStar : Cl × Cl → (Slot q → Cl)) :
    fixedBinCols P' sigmaStar ⊆ fixedBinCols Pstar sigmaStar :=
  Finset.image_subset_image hsub

/-- **Aux B6 (the routed Alice carrier consists of columns of `Z`).**  Composing
Aux B5 with the banked `fixedBinCols_subset`, a routed restriction is still a
genuine rectangular restriction of the state.  General in the state. -/
theorem routedFixedBinCols_subset_state
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (hP : RoutedSupport st P') :
    fixedBinCols P' st.sigmaStar ⊆ YZ :=
  subset_trans (routedFixedBinCols_subset hP.1 st.sigmaStar) (fixedBinCols_subset st)

/-- **Aux B7 (the routed Alice carrier is nonempty at every state).**  Aux B4
plus the image.  General in the state. -/
theorem routedFixedBinCols_nonempty
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (hP : RoutedSupport st P') :
    (fixedBinCols P' st.sigmaStar).Nonempty :=
  (routedSupport_nonempty hP).image _

/-! ## Section 3  The refreshed fixed-bin certificate (`09:1074--1082`)

"Clause (v) and `eq:terminal-selector-data` then leave transferred typed density
at least `49/64`.  Until the first Bob query, these Alice restrictions do not
change the ordinary and foreign fibre sets `O_alpha, F_alpha`, so the averages
`eq:terminal-averages` are unchanged.  The Stage-2 calculation above therefore
applies verbatim to the routed fixed-bin restriction and again gives residual
complexity at least `D_2 + 1`.  We use this refreshed certificate, rather than
restriction monotonicity, at every selector isolation node and in the
capacity-one case below."

The frozen sentence names **two** inputs of the Stage-2 calculation and asserts
that the route preserves both.  Both are proved below at every state; the
conclusion the frozen text then draws is phase 1's, which stays a binder. -/

/-- **`09:1074--1076`, proved.**  "Clause (v) and `eq:terminal-selector-data`
then leave transferred typed density at least `49/64`."  At a routed support the
record's universal clause (v) returns an actual classical two-copy restriction
whose family-index preimages lie in `P'`, and `selector_gate` upgrades its
density bound `(a_min - tau_0)/(1 + eps_2)^2` to the frozen `49/64`.  General in
the state and the routed support. -/
theorem routed_transfer_density
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (hP : RoutedSupport st P') :
    ∃ Q : Finset (Ltwo × Ltwo),
      (∀ z ∈ Q, ∃ y ∈ P', zeta st.pOrd y.1 = z.1 ∧ zeta st.pFor y.2 = z.2) ∧
      49 / 64 ≤ (Q.card : ℝ) / (Fintype.card Ltwo : ℝ) ^ 2 := by
  obtain ⟨Q, hQ, hden⟩ := st.uniform_transfer P' hP.1 hP.2
  exact ⟨Q, hQ, le_trans st.selector_gate hden⟩

/-- **`09:1076--1078`, the *structural half only* (repair F-3).**

The frozen sentence is "Until the first Bob query, these Alice restrictions do
not change the ordinary and foreign fibre sets `O_alpha, F_alpha`, so the
averages `eq:terminal-averages` are unchanged", and it has two halves: an
invariance claim about the fibre sets, and the consequence for the two averages.

**What this theorem establishes is only the second half, and only structurally:**
the two clause-(i) averages are computed from the *row* stream data
`(omega, rho, p, X_Z, i, R)` alone -- the column support `P'` never occurs in
either expression -- so they are available at every routed support as literally
the record's own fields.  The `RoutedSupport` argument is therefore inert here,
and the name says so.

**What it does not establish**, and must never be cited for: that the Alice
restrictions leave `O_alpha, F_alpha` themselves unchanged.  This module builds
no model of those fibre sets under an Alice restriction, so the frozen invariance
claim is **not** transcribed and is recorded as GAP-EXPOSED 7 below.  General in
the state and the routed support. -/
theorem routed_averages_are_column_free
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (_hP : RoutedSupport st P') :
    1 - ε ≤ meanFibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG) ∧
      δ' ≤ meanFibreDensity (streamImage omg rho st.pFor XZ st.iFor st.Rfor) :=
  ⟨st.ordinary_density, st.foreign_density⟩

/-- **`09:1078--1080`, the two inputs bundled.**  "The Stage-2 calculation above
therefore applies verbatim to the routed fixed-bin restriction."

The Stage-2 calculation of `09:871--1033` consumes exactly two things from the
state: the two averages of `eq:terminal-averages`, and the transferred typed
density of clause (ii).  This readout exhibits both **at the routed support**,
which is the precise content of the frozen "applies verbatim".  What it does not
do -- and must not do -- is run that calculation: the calculation is phase 1, and
phase 1 is gated on the protocol-side routing (GAP-EXPOSED 2).

Note the asymmetry between the two conjuncts, sharpened by repair F-3: the typed
density is genuinely re-derived **at `P'`** (`routed_transfer_density` uses the
record's universal clause (v)), whereas the two averages are carried by
`routed_averages_are_column_free`, which is only the structural half of
`09:1076--1078` and asserts nothing about the fibre sets `O_alpha, F_alpha`.
General in the state and the routed support. -/
theorem stage2_inputs_at_routed_support
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {P' : Finset (Cl × Cl)} (hP : RoutedSupport st P') :
    (1 - ε ≤ meanFibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG) ∧
        δ' ≤ meanFibreDensity (streamImage omg rho st.pFor XZ st.iFor st.Rfor)) ∧
      (∃ Q : Finset (Ltwo × Ltwo),
        (∀ z ∈ Q, ∃ y ∈ P', zeta st.pOrd y.1 = z.1 ∧ zeta st.pFor y.2 = z.2) ∧
        49 / 64 ≤ (Q.card : ℝ) / (Fintype.card Ltwo : ℝ) ^ 2) ∧
      (fixedBinCols P' st.sigmaStar).Nonempty :=
  ⟨routed_averages_are_column_free hP, routed_transfer_density hP,
    routedFixedBinCols_nonempty hP⟩

/-- **`09:1078--1082`, the refreshed certificate, transcribed as a named
claim.**

"The Stage-2 calculation above therefore applies verbatim to the routed
fixed-bin restriction and again gives residual complexity at least `D_2 + 1`.
We use this refreshed certificate, rather than restriction monotonicity, at
every selector isolation node and in the capacity-one case below."

The claim is the phase-1 bound `eq:terminal-fixed-bin`, quantified over **every**
routed selector support rather than asserted once at `P_*`.  That quantifier is
the whole content of the frozen word "refreshed", and
`monotonicity_runs_the_wrong_way` below is the machine-checked reason it cannot
be replaced by the single instance plus `D_subgame_mono`.

**Status.**  Stated only.  No declaration in this module has it as a conclusion.
Its discharge is `TerminalFixedBin.FixedBinLowerBound` at the routed support,
which is itself gated on that module's GAP-EXPOSED 2 (the protocol-side
routing); the dependency is disclosed here, not absorbed.  General in the state
and both exponents. -/
def RefreshedFixedBinBound
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (bcap r₂ : ℕ) : Prop :=
  ∀ P' : Finset (Cl × Cl), RoutedSupport st P' →
    fixedBinTarget bcap r₂
      ≤ D (subgame (interlaceFun Nmat q)
            (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor
              st.iotaOrd st.iotaFor)
            (fixedBinCols P' st.sigmaStar))

/-- **Aux C4 (`09:650`, the refreshed certificate really is a strengthening).**
"Taking `P' = P_*` gives the fixed-bin restriction in clause (ii)."  The full
support is a routed support -- its loss is exactly `0`, and `tau_0 > 0` at the
frozen positive row scale -- so the refreshed claim implies the phase-1
conclusion `eq:terminal-fixed-bin` verbatim.  Hence phase 2's added binder is
never weaker than what phase 1 delivers, and the arc cannot be closed by
weakening the certificate.  General in the state, at the frozen positivity of
`x_T`. -/
theorem refreshedFixedBinBound_gives_fixedBin
    {st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ'}
    {bcap r₂ : ℕ} (h : RefreshedFixedBinBound st bcap r₂) (hxT : 0 < xT) :
    fixedBinTarget bcap r₂
      ≤ D (subgame (interlaceFun Nmat q)
            (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor
              st.iotaOrd st.iotaFor)
            (fixedBinCols st.Pstar st.sigmaStar)) := by
  refine h st.Pstar ⟨Finset.Subset.refl _, ?_⟩
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast stage3_width_pos st
  have hτ : (0 : ℝ) < WrapperProjectionCovers.tauZero s xT := by
    rw [WrapperProjectionCovers.tauZero]
    have h2 : (0 : ℝ) < 2 * (s : ℝ) := by linarith
    exact mul_pos h2 hxT
  simpa using hτ

/-- **Statement pole 1 (`09:1080--1082`: monotonicity runs the wrong way).**

The frozen text is explicit that the refreshed certificate is used "rather than
restriction monotonicity", and this is the machine-checked reason.  The routed
Alice carrier is a **subset** of the fixed-bin one, so the vendored
`D_subgame_mono` compares the two complexities in the direction shown -- the
routed restriction is the *cheaper* game.  A single instance of
`eq:terminal-fixed-bin` at `P_*` therefore transports to **no** lower bound at a
routed `P'`, and `RefreshedFixedBinBound` cannot be replaced by its
`P' = P_*` instance.

Contrast `refreshedFixedBinBound_gives_fixedBin`, which travels the *available*
direction.  Together the two declarations pin the implication as strict.  General
in the state and the routed support. -/
theorem monotonicity_runs_the_wrong_way
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    {P' : Finset (Cl × Cl)} (hsub : P' ⊆ st.Pstar) :
    D (subgame (interlaceFun Nmat q)
        (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor
          st.iotaOrd st.iotaFor)
        (fixedBinCols P' st.sigmaStar))
      ≤ D (subgame (interlaceFun Nmat q)
            (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor
              st.iotaOrd st.iotaFor)
            (fixedBinCols st.Pstar st.sigmaStar)) :=
  D_subgame_mono _ (Finset.Subset.refl _) (routedFixedBinCols_subset hsub st.sigmaStar)

end AtState

/-! ## Section 4  The Stage-3 Alice row ladder (`09:1051--1095`, `09:1133--1134`)

`tau_d = 2 s x_T 2^{-d}` is the banked `TerminalTwoStream.tauAt` and is not
redefined.  What this section adds is the ladder's behaviour at a **reached
capacity**, which is what `09:1089--1092` and `09:1133--1134` read off it. -/

/-- **Aux D1 (`09:1089--1092`).**  "For `d <= r_3`, its row support is at least
`tau_d >= tau_{r_3} = 2 x_T`."  The ladder is antitone as soon as its root is
nonnegative, which is the only property of `tau_0` this step uses.  General. -/
theorem tauAt_antitone {s : ℕ} {xT : ℝ}
    (hτ : 0 ≤ WrapperProjectionCovers.tauZero s xT) {d d' : ℕ} (hdd : d ≤ d') :
    tauAt s xT d' ≤ tauAt s xT d := by
  unfold tauAt
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hle : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ d' := by
    have hnat : (2 : ℕ) ^ d ≤ 2 ^ d' := Nat.pow_le_pow_right (by norm_num) hdd
    exact_mod_cast hnat
  exact div_le_div_of_nonneg_left hτ hpow hle

/-- **Aux D2 (`09:1133--1134`).**  "Every ordinary object at the parent has row
density at least `tau_d = 2 kappa x_T`."  At the frozen dyadic width
`s = 2^{r_3}` this is an *identity* between the banked ladder and the banked
stopping capacity, not an estimate -- the Stage-3 counterpart of the predecessor
module's `lambdaAt_eq_two_mul_capacity_xSeed`.  General in the exponents, at any
suffix depth at most the Stage-3 frontier. -/
theorem tauAt_eq_two_mul_capacity {r₃ d : ℕ} (xT : ℝ) (hd : d ≤ r₃) :
    tauAt (2 ^ r₃) xT d
      = 2 * (DenseWeightedCount.stoppingCapacity r₃ d : ℝ) * xT := by
  rw [tauAt, WrapperProjectionCovers.tauZero, DenseWeightedCount.stoppingCapacity_eq]
  have hcast : (((2 : ℕ) ^ r₃ : ℕ) : ℝ) = (2 : ℝ) ^ r₃ := by push_cast; ring
  have hcast' : (((2 : ℕ) ^ (r₃ - d) : ℕ) : ℝ) = (2 : ℝ) ^ (r₃ - d) := by push_cast; ring
  rw [hcast, hcast']
  have hsplit : (2 : ℝ) ^ r₃ = (2 : ℝ) ^ (r₃ - d) * 2 ^ d := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  have hne : ((2 : ℝ) ^ d) ≠ 0 := by positivity
  field_simp

/-- **Aux D3 (consistency with the banked frontier evaluation).**  At the
Stage-3 frontier depth the reached capacity is `1`, and Aux D2 reproduces the
banked `tauAt_stage3_frontier` value `2 x_T` exactly.  A drift between the two
frozen readings of `tau_{r_3}` would show up here.  General. -/
theorem tauAt_capacity_at_frontier (r₃ : ℕ) (xT : ℝ) :
    2 * (DenseWeightedCount.stoppingCapacity r₃ r₃ : ℝ) * xT = 2 * xT := by
  rw [← tauAt_eq_two_mul_capacity xT (le_refl r₃)]
  exact tauAt_stage3_frontier r₃ xT

/-- **Aux D4 (the frozen row floor is not the degenerate `0`).**  At every depth
the Stage-3 row support the frozen text quotes is strictly positive, so none of
the row guards `09:1089--1095` reads off it can be met vacuously.  General, at
the frozen positive width and row scale. -/
theorem tauAt_pos {s d : ℕ} {xT : ℝ} (hs : 0 < s) (hxT : 0 < xT) :
    0 < tauAt s xT d := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  rw [tauAt, WrapperProjectionCovers.tauZero]
  have hnum : (0 : ℝ) < 2 * (s : ℝ) * xT := by positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  exact div_pos hnum hden

/-! ## Section 5  The two Stage-3 exclusions and the isolation capacity
(`09:1097--1110`)

Both frozen exclusions are budget counts against the alleged protocol `P_3` of
total depth `C - 1 = D_2 + r_3`.  They are stated **additively** -- "spent plus
demanded exceeds the total" -- so that no natural subtraction enters and no
`B_cap = 0` corner can make them vacuous. -/

/-- **Aux E1 (`09:1101--1103`, the capacity-one exclusion).**  "An unsplit
attached object at capacity one is impossible: then `d_v = r_3`, only `D_2`
protocol bits remain, and `eq:terminal-fixed-bin` requires `D_2 + 1`."
Additively: at the frontier depth `r_3` the object would need
`r_3 + (D_2 + 1)` bits, which exceeds the Stage-3 budget.

This is the point at which the frozen proof consumes the **refreshed**
certificate rather than a transported one: the object at the isolation node
carries a routed fixed-bin restriction, and the number it demands is the
refreshed `D_2 + 1`.  General. -/
theorem stage3_capacity_one_exclusion (bcap r₂ r₃ : ℕ) :
    stageThreeBudget bcap r₂ r₃ < r₃ + fixedBinTarget bcap r₂ := by
  simp only [stageThreeBudget, fixedBinTarget, DenseBranchSelection.Dtwo]
  omega

/-- **Aux E2 (`09:1101--1103`, contrapositive).**  If an unsplit attached object
*does* survive at suffix depth `d` -- i.e. its refreshed `D_2 + 1` certificate
still fits the Stage-3 budget after `d` bits have been spent -- then the reached
capacity is at least `2`.  This is exactly the frozen `htwo` premise of the
banked `eq:isolation-capacity`, derived rather than assumed.  General. -/
theorem stage3_unsplit_forces_capacity_two {bcap r₂ r₃ d : ℕ}
    (hres : d + fixedBinTarget bcap r₂ ≤ stageThreeBudget bcap r₂ r₃) :
    2 ≤ DenseWeightedCount.stoppingCapacity r₃ d := by
  have hlt : d < r₃ := by
    simp only [stageThreeBudget, fixedBinTarget, DenseBranchSelection.Dtwo] at hres
    omega
  exact DenseWeightedCount.two_le_stoppingCapacity_of_lt hlt

/-- **Aux E3 (`09:1098--1106`, the isolation-capacity bound).**  "The routing has
at most one ordinary object from each baseline bin at a node, and an isolation
node has only one surviving baseline bin.  An unsplit attached object at capacity
one is impossible ...  Hence `h_v + z_v <= kappa_v`."  The banked
`isolationNode_capacity_at_depth` supplies the counting; what this adds is that
its `htwo` premise is discharged by Aux E2 from the Stage-3 budget rather than
assumed.  `huniq` (the frozen one-object-per-node clause, `09:1099--1101`) and
`hz` (`z_v <= h_v`) stay named hypotheses, honouring the banked
`DenseRoutingInvariant`'s coverage limit.  General. -/
theorem stage3_isolation_capacity {bcap r₂ r₃ d h z : ℕ}
    (huniq : h ≤ 1) (hz : z ≤ h)
    (hres : 0 < z → d + fixedBinTarget bcap r₂ ≤ stageThreeBudget bcap r₂ r₃) :
    h + z ≤ DenseWeightedCount.stoppingCapacity r₃ d :=
  DenseWeightedCount.isolationNode_capacity_at_depth huniq hz
    (fun hzpos => stage3_unsplit_forces_capacity_two (hres hzpos))

/-- **Aux E4 (`09:1107--1110`, the premature-leaf exclusion).**  "Nor can an
ordinary object first reach depth `r_3 + 1`: it would retain row density at least
`x_T` and column density greater than `3/5`, so its residual complexity would be
`D_2`, while only `D_2 - 1` bits would remain."  Additively: `(r_3 + 1) + D_2`
exceeds the Stage-3 budget.  General. -/
theorem stage3_premature_leaf_exclusion (bcap r₂ r₃ : ℕ) :
    stageThreeBudget bcap r₂ r₃ < (r₃ + 1) + DenseBranchSelection.Dtwo bcap r₂ := by
  simp only [stageThreeBudget]
  omega

/-! ## Section 6  The first-Bob frontier substitution (`09:1112--1123`)

"The stopping nodes therefore satisfy the hypotheses of
`lem:dense-weighted-frontier` with the names of Alice and Bob interchanged.
Here all `s` ordinary bins are present, there is one attached bonus component,
and there is no defective bin.  Equivalently, the weighted count has `b = 0` and
`w = 1`.  It yields a first-Bob node `v` such that ..."

The banked lemma is **applied**, never restated.  Its width hypothesis is
discharged from the frozen `s = 2^{r_3}` and its gap hypothesis outright from
`b = 0`; the routing data and the two properties the banked module left as
coverage limits stay explicit binders. -/

/-- **`eq:terminal-first-bob` (label `09:1122`, display `09:1118--1123`),
derived.**

The banked `lem:dense-weighted-frontier` is applied at `Coord = [s]`, at the
Stage-3 exponent `r = r_3`, with the frozen substitution `b = 0` ("there is no
defective bin") and `w = 1` ("there is one attached bonus component").  Two of
its four counting hypotheses are **discharged** here:

* `hselected : 2^{r_3} <= |Coord| + 0` from the frozen dyadic width
  `s = 2^{r_3}` (`09:1038`), since `|[s]| = s`;
* `hgap : 4 * 0 < 1`, which is the frozen "`b = 0` and `w = 1`" -- so the
  Stage-3 substitution needs no counting phase at all, in contrast with the
  Stage-2 one where `eq:terminal-excess` had to supply the gap.

The remaining two stay named binders, exactly as the banked module states them:
`hbonus` (the routed arrivals really carry the one attached bonus component,
`09:1114--1116`) and `hisocap` (`eq:isolation-capacity`, whose Stage-3
derivation is Aux E3).  Prefix-freeness and the depth bound are the banked `hpf`
and `hdepth`.

**On the party names.**  The banked frontier lemma classifies its nodes into
`isolationNodes` and `aliceNodes`; the latter is simply the non-isolation class,
named after the Stage-2 orientation in which it was banked.  `09:1112--1113`
applies that lemma "with the names of Alice and Bob interchanged", so in this
Stage-3 orientation the same class *is* the frozen first-Bob class.  The banked
name is kept rather than duplicated, exactly as the fixed-interface discipline
requires; nothing about the classification changes.

General in the Stage-3 width and exponent, the node type, the routing and the
isolation predicate. -/
theorem terminal_first_bob {ι : Type*} [Fintype ι] [DecidableEq ι] {s r₃ : ℕ}
    (hwidth : s = 2 ^ r₃)
    (arr : Slot s → DenseFrontierConservation.FrontierArrival ι)
    (route : ι → List Bool) (iso : ι → Prop) [DecidablePred iso]
    (hpf : DenseWeightedCount.PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r₃)
    (hbonus : 1 ≤ DenseFrontierConservation.witnessCount arr)
    (hisocap : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      DenseFrontierConservation.hMass arr v + DenseFrontierConservation.zMass arr v
        ≤ DenseWeightedCount.stoppingCapacity r₃ (route v).length) :
    ∃ v ∈ DenseWeightedCount.aliceNodes iso,
      3 * DenseWeightedCount.stoppingCapacity r₃ (route v).length
          ≤ 4 * DenseFrontierConservation.hMass arr v ∧
        DenseWeightedCount.stoppingCapacity r₃ (route v).length
          < DenseFrontierConservation.hMass arr v
            + DenseFrontierConservation.zMass arr v := by
  classical
  have hcard : Fintype.card (Slot s) = s := Fintype.card_fin s
  have hselected : 2 ^ r₃ ≤ Fintype.card (Slot s) + 0 := by omega
  exact DenseWeightedFrontier.denseWeightedFrontier (b := 0) (w := 1) arr route iso
    hpf hdepth hselected (by omega) (by norm_num) hisocap

/-! ### The probe behind statement pole 2 -/

/-- The one-node Stage-3 frontier at `r_3 = 0`: a single baseline bin carrying an
**ordinary** object, hence no attached bonus component. -/
def poleArr : Slot 1 → DenseFrontierConservation.FrontierArrival (Fin 1) :=
  fun _ => DenseFrontierConservation.FrontierArrival.ordinary 0

/-- The route function of the pole probe: the single node is the root. -/
def poleRoute : Fin 1 → List Bool := fun _ => []

/-- The isolation predicate of the pole probe: no node is an isolation node, so
every node is an Alice node in the banked classification. -/
def poleIso : Fin 1 → Prop := fun _ => False

instance decidablePoleIso : DecidablePred poleIso :=
  fun _ => Decidable.isFalse (fun h => h)

/-- **Statement pole 2 (the existential deliverable is not automatic: the frozen
"one attached bonus component" is load-bearing).**

`eq:terminal-first-bob` is an existential, so the discipline demands one line
showing the trivial witness fails.  Because the Stage-3 substitution sets
`b = 0`, the gap hypothesis `4b < w` is automatic -- which is exactly why the
*other* frozen counting sentence, "there is one attached bonus component"
(`09:1114--1116`), carries the weight there.

The witness is the one-node frontier at the Stage-3 exponent `r_3 = 0` with a
single baseline bin holding an **ordinary** object.  At it every hypothesis of
`terminal_first_bob` except `hbonus` holds -- prefix-freeness and the depth bound
trivially, `hselected : 2^0 <= 1 + 0`, `hgap : 4 * 0 < 1`, and `hisocap` because
`h_v + z_v = 1 + 0 = 1 = kappa_v` -- while `hbonus` fails (`witnessCount = 0`)
and the conclusion fails too: the single Alice node has `h_v = 1`, `z_v = 0` and
`kappa_v = 1`, so the strict excess `kappa_v < h_v + z_v` is `1 < 1`.

Consequently the frozen sentence at `09:1114--1116` is not decoration, and
`terminal_first_bob` is not provable from `b = 0` alone.

**Repair F-6.**  The fourth conjunct previously read `¬ (4 * 0 < 0)`, which is
the gap hypothesis at the *unsubstituted* `w = 0` and therefore not the
hypothesis `terminal_first_bob` discharges.  `terminal_first_bob` applies the
banked frontier lemma at the frozen substitution `b = 0`, `w = 1`, so its gap
hypothesis is `4 * 0 < 1`, which **holds** at this probe -- and that is precisely
why the pole's substance sits in the `hbonus` and conclusion conjuncts.  The
conjunct now matches the docstring. -/
theorem first_bob_needs_the_bonus_component :
    (DenseWeightedCount.PrefixFreeFrontier poleRoute)
      ∧ (∀ v : Fin 1, (poleRoute v).length ≤ 0)
      ∧ 2 ^ 0 ≤ Fintype.card (Slot 1) + 0
      ∧ (4 * 0 < 1)
      ∧ (∀ v ∈ DenseWeightedCount.isolationNodes poleIso,
          DenseFrontierConservation.hMass poleArr v
              + DenseFrontierConservation.zMass poleArr v
            ≤ DenseWeightedCount.stoppingCapacity 0 (poleRoute v).length)
      ∧ ¬ (1 ≤ DenseFrontierConservation.witnessCount poleArr)
      ∧ ¬ ∃ v ∈ DenseWeightedCount.aliceNodes poleIso,
          3 * DenseWeightedCount.stoppingCapacity 0 (poleRoute v).length
              ≤ 4 * DenseFrontierConservation.hMass poleArr v ∧
            DenseWeightedCount.stoppingCapacity 0 (poleRoute v).length
              < DenseFrontierConservation.hMass poleArr v
                + DenseFrontierConservation.zMass poleArr v := by
  classical
  have hmass : ∀ v : Fin 1, DenseFrontierConservation.hMass poleArr v = 1 := by
    intro v
    simp [DenseFrontierConservation.hMass, poleArr,
      DenseFrontierConservation.FrontierArrival.hContrib, Subsingleton.elim (0 : Fin 1) v]
  have hzero : ∀ v : Fin 1, DenseFrontierConservation.zMass poleArr v = 0 := by
    intro v
    simp [DenseFrontierConservation.zMass, poleArr,
      DenseFrontierConservation.FrontierArrival.zContrib]
  have hwit : DenseFrontierConservation.witnessCount poleArr = 0 := by
    simp [DenseFrontierConservation.witnessCount, DenseFrontierConservation.witnesses,
      poleArr, DenseFrontierConservation.FrontierArrival.isWitness]
  refine ⟨?_, fun _ => le_rfl, by simp, by norm_num, ?_, by omega, ?_⟩
  · intro v w hvw
    exact absurd (Subsingleton.elim v w) hvw
  · intro v _
    rw [hmass v, hzero v]
    simp [DenseWeightedCount.stoppingCapacity]
  · rintro ⟨v, -, -, hlt⟩
    rw [hmass v, hzero v] at hlt
    simp [DenseWeightedCount.stoppingCapacity] at hlt

/-! ## Section 7  The Stage-3 dispatch and the closing budget (`09:1125--1173`)

`eq:terminal-bob-child-density` and both certified-scale ladder instances are
banked (`TerminalTwoStream.bob_child_density`,
`stage3_two_copy_of_seedInputs`, `stage3_odd_copy_of_seedInputs`); what this
section adds is the frozen three-case dispatch **at the reached Stage-3
capacities** and the closing comparison, again additively. -/

/-- **Aux G1 (`09:1152--1161`, the frozen three-case dispatch).**  At any reached
Stage-3 capacity exactly one of the frozen branches applies: `kappa >= 4`
(select `3 kappa/4 >= kappa/2 + 1` ordinary objects and apply
`eq:terminal-stage3-odd-copy`), `kappa = 2` (integrality plus
`eq:terminal-stage3-two-copy`), or `kappa = 1` (the positive excess).  Unlike the
Stage-2 dispatch -- whose branches are cut by the *free* width `t_2` and are
therefore only exhaustive -- the Stage-3 branches are cut by the dyadic capacity
itself, so this disjunction is genuinely exhaustive at **every** depth with no
side condition.  General in the exponent and the depth. -/
theorem stage3_capacity_trichotomy (r₃ d : ℕ) :
    4 ≤ DenseWeightedCount.stoppingCapacity r₃ d
      ∨ DenseWeightedCount.stoppingCapacity r₃ d = 2
      ∨ DenseWeightedCount.stoppingCapacity r₃ d = 1 := by
  rw [DenseWeightedCount.stoppingCapacity_eq]
  rcases Nat.lt_or_ge (r₃ - d) 2 with hlt | hge
  · have hcase : r₃ - d = 0 ∨ r₃ - d = 1 := by omega
    rcases hcase with h0 | h1
    · exact Or.inr (Or.inr (by rw [h0]; norm_num))
    · exact Or.inr (Or.inl (by rw [h1]; norm_num))
  · refine Or.inl ?_
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r₃ - d) := Nat.pow_le_pow_right (by norm_num) hge

/-- **Aux G2 (`09:1152--1155`, the `kappa >= 4` branch).**  "If `kappa >= 4`,
then `h_v >= 3 kappa/4 >= kappa/2 + 1`; select that many ordinary objects, trim
their supports to `kappa x_T`, and apply `eq:terminal-stage3-odd-copy`."  The
copy count `kappa/2 + 1` is exactly the one the banked odd-copy instance
consumes, so this shows the frozen selection is available and is not an extra
demand.  General, at any depth at least two below the Stage-3 frontier. -/
theorem stage3_selection_at_capacity {r₃ d h : ℕ} (hcap : 2 ≤ r₃ - d)
    (hforced : 3 * DenseWeightedCount.stoppingCapacity r₃ d ≤ 4 * h) :
    DenseWeightedCount.stoppingCapacity r₃ d / 2 + 1 ≤ h := by
  obtain ⟨k, hk⟩ : ∃ k, r₃ - d = k + 1 := ⟨r₃ - d - 1, by omega⟩
  have hk2 : 1 ≤ k := by omega
  have hcapeq : DenseWeightedCount.stoppingCapacity r₃ d = 2 * 2 ^ k := by
    rw [DenseWeightedCount.stoppingCapacity_eq, hk, pow_succ]
    ring
  have hm : 2 ≤ 2 ^ k := by
    have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    simpa using hpow
  have hdiv : DenseWeightedCount.stoppingCapacity r₃ d / 2 = 2 ^ k := by
    rw [hcapeq]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hdiv]
  rw [hcapeq] at hforced
  exact odd_copy_selection hm hforced

/-- **Aux G3 (`09:1155--1156`, the `kappa = 2` branch).**  "If `kappa = 2`,
integrality gives `h_v >= 2`, and `eq:terminal-stage3-two-copy` applies."  The
frozen appeal to integrality is `3 * 2 <= 4 h => h >= 2`, which is false over the
rationals for `h = 3/2`; landing it at the reached capacity keeps it a statement
about the Stage-3 ladder rather than a detached inequality.  General. -/
theorem stage3_selection_at_capacity_two {r₃ d h : ℕ} (hcap : r₃ - d = 1)
    (hforced : 3 * DenseWeightedCount.stoppingCapacity r₃ d ≤ 4 * h) :
    2 ≤ h := by
  rw [DenseWeightedCount.stoppingCapacity_eq, hcap] at hforced
  omega

/-- **Aux G4 (`eq:terminal-stage3-budget`, `09:1161--1173`, the closing
comparison).**  "in every remaining case, the selected Bob child has complexity
at least `D_2 + log_2 kappa`.  The suffix of `P_3` below that child has depth at
most `(C - 1) - d - 1 = D_2 + log_2 kappa - 1`, a contradiction."  At
`log_2 kappa = r_3 - d` this says: the `d + 1` bits already spent, plus the
`D_2 + (r_3 - d)` the child still demands, exceed the alleged Stage-3 budget.
Stated additively so that the frozen `- 1` never becomes a truncated natural
subtraction.  General, at any suffix depth at most the Stage-3 frontier. -/
theorem stage3_bob_child_exceeds {r₃ d : ℕ} (bcap r₂ : ℕ) (hd : d ≤ r₃) :
    stageThreeBudget bcap r₂ r₃ < (d + 1) + (DenseBranchSelection.Dtwo bcap r₂ + (r₃ - d)) := by
  simp only [stageThreeBudget]
  omega

/-! ## Section 8  `lem:terminal-two-stream`, phase 2 (`09:1035--1173`), stated

The frozen phase-2 conclusion is transcribed as a named claim about the pinned
construction.  It is **not proved** in this tranche -- see GAP-EXPOSED 1--3 --
and no declaration below derives it. -/

/-- **The Stage-3 lift (`09:1035--1173`), transcribed.**

"Now suppose for contradiction that `Z` has a protocol `P_3` of depth at most
`C - 1 = D_2 + log_2 s` ...  Therefore no protocol of depth `C - 1` computes
`Z`, and `comp Z >= C`, as claimed."

**Binder set.**  Every binder of the frozen headline `lem:terminal-two-stream` is
carried token-identically -- the banked Stage-2 width record, the dyadic
convention `s = 2^{r_3}`, the two checked-identity pins `x_T = 2^{-b_T}` and
`y = 3/5`, the banked `TwoStreamState` record, `eq:terminal-entry`,
`eq:terminal-seed-inputs`, the call-(ii) fixed-width binder and the `forall`-form
reached-capacity Extension binder -- **plus one**: the refreshed fixed-bin
certificate of `09:1076--1082`.

That extra binder is the honest shape of a *phase*.  The frozen proof's second
part opens by using a result its first part established; a phase-2 statement that
did not carry it would be claiming the whole lemma.  Adding it weakens this claim
relative to the headline, which is the correct direction, and
`terminalTwoStream_of_phases` records that the two phases recombine with nothing
added.  It is carried in its **refreshed** form, quantified over every routed
selector support, because `09:1080--1082` says in as many words that restriction
monotonicity is not what the selector argument uses -- and
`monotonicity_runs_the_wrong_way` proves that the frozen text is right about the
direction.

**Status.**  Stated only.  No declaration in this module has it as a conclusion,
and in particular there is no theorem deriving it from an assumed first-Bob
verdict: `terminal_first_bob` runs the other way, *producing*
`eq:terminal-first-bob` from the substitution.  The conclusion is `comp Z >= C`
at `Z = extract(U, X_Z, Y_Z)`, `U = Interlace(N, q)`, in the vendored,
project-axiom-free complexity interface. -/
def StageThreeLift {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo]
    [DecidableEq Ltwo] [Fintype Rone] [DecidableEq Rone]
    (W : StageTwoRelaxed.StageTwoWidths)
    (q s mT dT bcap r₃ bT Lh vmax : ℕ) (Nmat : Rw → Cl → Bool)
    (Mmat : Cone → Rone → Bool) (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (rho : Slot s → Om → Slot W.q₂ × Cone) (YT : Slot s → Finset Cl)
    (zeta : Slot s → Cl → Ltwo) (XZ : Finset (Slot q × Rw))
    (YZ : Finset (Slot q → Cl)) (lamT eps2 epsProd xT y ε δ' : ℝ) : Prop :=
  s = 2 ^ r₃ →
    xT = DenseStageFourOpening.xTdepth bT →
    y = 3 / 5 →
    ∀ st : TwoStreamState.TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ',
      terminalEntry W.q₂ W.b₁ ε δ' →
      terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT y →
      ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd →
      (∀ d : ℕ, d ≤ W.r₂ → W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
        extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ d)) →
      RefreshedFixedBinBound st bcap W.r₂ →
      terminalTarget bcap W.r₂ r₃ ≤ D (subgame (interlaceFun Nmat q) XZ YZ)

/-- **Composition readout (the two phases recombine with nothing added).**

**Read the name with its scope.**  This theorem proves **no mathematics**: both
antecedents are unproved named claims, and the body is the modus ponens that
feeds the refreshed certificate into the phase-2 binder.  What it establishes is
a *bookkeeping* fact the arc needs -- that `StageThreeLift`'s binder set is the
headline's binder set plus exactly the refreshed certificate, in the same binder
positions, so no hypothesis has silently drifted between the two statements and
no third obligation has appeared.

The refreshed certificate is required at every state **at these parameters** --
the antecedent `hrefresh` carries no `eq:terminal-entry`,
`eq:terminal-seed-inputs` or Extension guard of its own, since all of those are
parameter-level in the headline and so are already fixed before `st` is bound.
That is the honest reading of `09:1078--1082`: the frozen proof re-derives the
certificate at each selector isolation node, so a single instance would not do.
General in every parameter. -/
theorem terminalTwoStream_of_phases {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw]
    [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone]
    [Fintype Ltwo] [DecidableEq Ltwo] [Fintype Rone] [DecidableEq Rone]
    {W : StageTwoRelaxed.StageTwoWidths}
    {q s mT dT bcap r₃ bT Lh vmax : ℕ} {Nmat : Rw → Cl → Bool}
    {Mmat : Cone → Rone → Bool} {cFam : Ltwo → Slot W.q₂ → Rone}
    {Stwo : Ltwo → Slot W.q₂ × Cone → Bool} {RG RSig RD : Finset Rw} {omg : Rw → Om}
    {rho : Slot s → Om → Slot W.q₂ × Cone} {YT : Slot s → Finset Cl}
    {zeta : Slot s → Cl → Ltwo} {XZ : Finset (Slot q × Rw)}
    {YZ : Finset (Slot q → Cl)} {lamT eps2 epsProd xT y ε δ' : ℝ}
    (hlift : StageThreeLift W q s mT dT bcap r₃ bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 epsProd xT y ε δ')
    (hrefresh : ∀ st : TwoStreamState.TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo
        RG RSig RD omg rho YT zeta XZ YZ lamT eps2 xT ε δ',
      RefreshedFixedBinBound st bcap W.r₂) :
    TerminalTwoStream W q s mT dT bcap r₃ bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 epsProd xT y ε δ' := by
  intro hs hxT hy st hentry hseed hfw hcall
  exact hlift hs hxT hy st hentry hseed hfw hcall (hrefresh st)

/-- **Statement pole 3 (phase 2 cannot be mistaken for its own binder).**  The
refreshed certificate the phase consumes bounds the fixed-bin restriction by
`D_2 + 1`; the phase's conclusion bounds `Z` by `C = D_2 + log_2 s + 1`.  The
deficit is exactly `log_2 s` bits, and it is strictly positive as soon as there
is more than one baseline bin.  So no rearrangement of the binder yields the
conclusion, and the entire Stage-3 selector argument of `09:1035--1173` is
load-bearing.  General. -/
theorem stageThreeLift_conclusion_is_not_the_binder {r₃ : ℕ} (bcap r₂ : ℕ) (hr : 0 < r₃) :
    stageThreeBudget bcap r₂ r₃ < terminalTarget bcap r₂ r₃
      ∧ fixedBinTarget bcap r₂ + r₃ = terminalTarget bcap r₂ r₃
      ∧ ¬ (terminalTarget bcap r₂ r₃ ≤ fixedBinTarget bcap r₂) := by
  refine ⟨?_, ?_, (fixedBin_bound_is_strictly_weaker_than_C (r₃ := r₃) bcap r₂ hr).2⟩
  · rw [← stageThreeBudget_succ bcap r₂ r₃]
    omega
  · rw [← stageThreeBudget_eq_fixedBin_add, stageThreeBudget_succ]

/-! ## Section 9  Non-vacuity readouts

The new predicate is inhabited at a **proper** routed subset of the banked
probe's support, and the claim's arithmetic sub-bundle is exhibited at the banked
**balance-minimum** width record `TerminalTwoStream.probeWidths` -- **not** at
legal schedule values.  The predecessor wording "exhibited at legal schedule
values" is WITHDRAWN: it was false.  `probeWidths` is legal for the four proof
fields of `StageTwoRelaxed.StageTwoWidths` only; its `k_2 = 5` fails the
`eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}` (`06:766`,
`2^{19} = 524288`), which is why
`Section5Admissibility.stage2Group_refuted_at_balance_minimum` refutes the fourth
admissibility group at it outright.  (Repaired at `cc-t7q`, ledger item
`(b14)`.) -/

/-- **Non-vacuity 1 (`RoutedSupport` is not a disguised equality) --
NON-FIDELITY.**  The banked probe's loss budget is `tau_0 m_T^2 = 144/100 > 1`,
so a routed support may drop a pair and still qualify: `P' = P_* \ {one pair}`
satisfies `RoutedSupport` and is **strictly** inside `P_*`.  Without this the
whole quantifier of `RefreshedFixedBinBound` would collapse to its
`P' = P_*` instance and the module would have re-landed phase 1 under a new
name.

This is machine evidence about *our* encoding at a point the frozen paper never
visits: the banked probe sits at `q_2 = 2`, hence outside `eq:terminal-entry`
(`TerminalTwoStream.bankedProbeWidth_is_not_a_terminal_entry_width`), so it is
**not** a witness that the terminal regime is inhabited.  The fidelity statements
are the general lemmas of Sections 2--3, which hold at every state including the
paper's. -/
theorem routedSupport_at_probe_proper_subset :
    ∃ P' : Finset (TwoStreamState.ProbeCl × TwoStreamState.ProbeCl),
      RoutedSupport TwoStreamState.probeState P' ∧
        P' ≠ TwoStreamState.probeState.Pstar := by
  classical
  set e : TwoStreamState.ProbeCl × TwoStreamState.ProbeCl :=
    ((0, (true, 0)), (0, (true, 0))) with he
  have heP : e ∈ TwoStreamState.probePstar :=
    Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩
  refine ⟨TwoStreamState.probePstar.erase e,
    ⟨Finset.erase_subset _ _, ?_⟩, ?_⟩
  · have hPs : TwoStreamState.probeState.Pstar = TwoStreamState.probePstar := rfl
    have hsd : (TwoStreamState.probePstar \ TwoStreamState.probePstar.erase e).card = 1 := by
      rw [Finset.sdiff_erase heP]
      simp
    rw [hPs, hsd, TwoStreamState.probe_tauZero]
    norm_num
  · intro hcon
    have hmem : e ∈ TwoStreamState.probePstar.erase e := hcon ▸ heP
    exact absurd (Finset.mem_erase.mp hmem).1 (fun h => h rfl)

/-- **Non-vacuity 2 (the routed Alice carrier survives the routing) --
NON-FIDELITY.**  At the proper routed subset of Non-vacuity 1 the routed column
carrier is still nonempty, so the refreshed certificate is never a bound on an
empty matrix at that point.  Same NON-FIDELITY caveat as Non-vacuity 1; the
fidelity statement is `routedFixedBinCols_nonempty`, proved at every state. -/
theorem routed_carrier_nonempty_at_probe :
    ∃ P' : Finset (TwoStreamState.ProbeCl × TwoStreamState.ProbeCl),
      RoutedSupport TwoStreamState.probeState P' ∧
        (fixedBinCols P' TwoStreamState.probeState.sigmaStar).Nonempty := by
  obtain ⟨P', hP, -⟩ := routedSupport_at_probe_proper_subset
  exact ⟨P', hP, routedFixedBinCols_nonempty hP⟩

/-- **Non-vacuity 3 (HYPOTHESIS-CONSISTENCY for the phase-2 arithmetic).**

**Exact coverage.**  This readout exhibits the *arithmetic* conjuncts of
`StageThreeLift`'s binder set and the Stage-3 dispatch, and no others.  It does
**not** exhibit `ExtensionCallTwoFixedWidth`, the banked `TwoStreamState` record,
the two pins `x_T = 2^{-b_T}` and `y = 3/5`, the two `Lambda` certificates, or
the refreshed certificate.  The fixed-width binder is discharged in full by
`TerminalTwoStream.terminalTwoStream_r2_hypotheses_consistent` at
`extProbeWidths`; the two pins are satisfiable by construction; and the refreshed
certificate's consistency is structural rather than numeric -- it implies the
phase-1 conclusion (`refreshedFixedBinBound_gives_fixedBin`), whose own
consistency the predecessor module recorded, and its quantifier is inhabited at
a proper subset (Non-vacuity 1).  Note that `probeWidths` -- legal for the four
proof fields of `StageTwoRelaxed.StageTwoWidths` only -- has widths **outside
the gate-firing regime** (`cc-t7p`, ledger item `(b11)`).

At the banked record `TerminalTwoStream.probeWidths` (`k_2 = 5`, `r_2 = 7`,
`b_1 = 24`, so `q_2 = 128`, `t_2 = 32`), a nondegenerate `B_cap = 5` and a
nondegenerate Stage-3 exponent `r_3 = 3`, the following hold
**simultaneously**:

* `eq:terminal-entry` at a nondegenerate `eps = 1/100`, `delta' = 1/10`;
* the three Stage-3 targets are the nondegenerate `C - 1 = 15`, `C = 16` and
  `D_2 + 1 = 13`, and the two-phase identity `15 + 1 = 13 + 3` holds;
* both Stage-3 exclusions of `09:1097--1110` fire;
* the closing budget comparison of `eq:terminal-stage3-budget` fires at the root
  depth; and
* the capacity trichotomy is reached at **both** ends -- `kappa = 8 >= 4` at the
  root and `kappa = 1` at the frontier -- so neither the odd-copy branch nor the
  capacity-one branch is vacuous.

A satisfiable collection cannot yield `False`, so no derivation of `False` from
the arithmetic sub-bundle can go through.

**Repair F-5.**  The Stage-3 exponent is now written as the banked pin
`TerminalTwoStream.probeR₃`, not as the bare numeral `3`.  `probeR₃` is the value
the banked probe fixes (`probeWidths`-side `8 = 2 ^ probeR₃`, `probeR₃ < probeBT`),
so the readout and the banked probe now speak about one object and a change to the
pin cannot leave this readout silently pinned to an old numeral. -/
theorem stageThreeLift_arith_hypotheses_consistent :
    terminalEntry probeWidths.q₂ probeWidths.b₁ (1 / 100) (1 / 10)
      ∧ stageThreeBudget 5 probeWidths.r₂ probeR₃ = 15
      ∧ terminalTarget 5 probeWidths.r₂ probeR₃ = 16
      ∧ fixedBinTarget 5 probeWidths.r₂ = 13
      ∧ stageThreeBudget 5 probeWidths.r₂ probeR₃ + 1
          = fixedBinTarget 5 probeWidths.r₂ + probeR₃
      ∧ stageThreeBudget 5 probeWidths.r₂ probeR₃
          < probeR₃ + fixedBinTarget 5 probeWidths.r₂
      ∧ stageThreeBudget 5 probeWidths.r₂ probeR₃
          < (probeR₃ + 1) + DenseBranchSelection.Dtwo 5 probeWidths.r₂
      ∧ stageThreeBudget 5 probeWidths.r₂ probeR₃
          < (0 + 1) + (DenseBranchSelection.Dtwo 5 probeWidths.r₂ + (probeR₃ - 0))
      ∧ 4 ≤ DenseWeightedCount.stoppingCapacity probeR₃ 0
      ∧ DenseWeightedCount.stoppingCapacity probeR₃ probeR₃ = 1 :=
  ⟨probeEntry_is_nondegenerate.1, by decide, by decide, by decide,
    stageThreeBudget_eq_fixedBin_add 5 probeWidths.r₂ probeR₃,
    stage3_capacity_one_exclusion 5 probeWidths.r₂ probeR₃,
    stage3_premature_leaf_exclusion 5 probeWidths.r₂ probeR₃,
    stage3_bob_child_exceeds (r₃ := probeR₃) (d := 0) 5 probeWidths.r₂ (by norm_num),
    by decide, by decide⟩

end EthInapproximability.ParameterizedNP.TerminalStageThreeLift
