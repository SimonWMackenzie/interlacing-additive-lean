import EthInapproximability.ParameterizedNP.TerminalTwoStream

/-!
# Parameterized NP route: the fixed-Stage-3-bin lower bound (terminal phase 1)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`),
  **lines 862--1033** -- the **first** of the two phases the frozen proof of
  `lem:terminal-two-stream` announces at `09:867--868`:

  > "We first prove a lower bound one bit above `D_2` inside a fixed Stage-3
  > bin, and then lift that bit through the Stage-3 selector."

  This module is that first phase and stops at `eq:terminal-fixed-bin`
  (`09:1030--1033`); the Stage-3 lift `09:1035--1173` is the arc's later round
  and nothing here anticipates it.  The anchors traced, in the order the frozen
  block prints them:
  * `09:867--868`, the two-phase announcement, and `D_2 = B_cap + log_2 q_2` at
    `09:864--866`, `D_2` consumed by pin from `DenseBranchSelection.Dtwo`.
  * `09:916--923`, the fixed-bin frame: "Fix the pair of Stage-3 template bins
    in clause (ii) of `def:two-stream-state` and work inside one of them.
    Transpose this fixed-bin state, and suppose for contradiction that the
    resulting matrix has a protocol `P_2` of depth at most `D_2`.  Until
    `eq:terminal-fixed-bin`, every remaining-budget reference is to the suffix
    depth in `P_2`.  Bob's columns are then the disjoint tagged ordinary and
    foreign `C_1`-fibres, while Alice's rows are the retained typed subset of
    `C_2 x C_2`."
  * `09:923--925`, the token placement: "Give each coordinate of `H` one
    ordinary token and attach one additional foreign token to each coordinate of
    `Z`."
  * `09:928--930`, the Bob support threshold `lambda_d = lambda_0 2^{-d}`,
    consumed **by pin** from `DenseRoutingThresholds.lambdaAt` (`08:812--816`).
  * `09:953--965`, the isolation-node bookkeeping: `kappa_v = 2^{r_2-d_v}`, the
    ordinary and unsplit-bonus counts `h_v, z_v`, the capacity-one exclusion
    ("if `kappa_v = 1`, then `d_v = r_2`, while `P_2` has at most
    `D_2 - r_2 = B_cap` bits remaining, contradicting the pair's residual
    complexity `B_cap + 1`"), and the conclusion `h_v + z_v <= kappa_v`.
  * `09:967--978`, the premature-leaf exclusion at depth `r_2 + 1`.
  * `09:980--994`, the appeal to `lem:dense-weighted-frontier`: "Substituting
    witness count `|Z|` and bad count `b`, and then using
    `eq:terminal-excess`, shows that some first-Alice node satisfies
    `eq:terminal-first-alice`."
  * `eq:terminal-stage2-budget` (label `09:1001`, display `09:998--1002`).
  * `09:1005--1006`, "Each ordinary token there has support at least
    `2 kappa_v 2^{-b_1}`".
  * `09:1006--1012`, the labelled `C_2 x C_2` coordinates and the post-query
    typed density `49/128 > 9/25`.
  * `09:1014--1028`, the three-case Extension dispatch: `kappa_v >= t_2`
    (select `9 kappa_v/16` ordinary coordinates and invoke call (ii)),
    `2 <= kappa_v < t_2` (inherited two-copy and odd-copy bounds), `kappa_v = 1`
    (the positive excess supplies an unsplit attached pair or two ordinary
    coordinates), and "In every case one Alice child has complexity at least
    `B_cap + log_2 kappa_v`, which exceeds `eq:terminal-stage2-budget`."
  * `eq:terminal-fixed-bin` (label `09:1032`, display `09:1030--1033`),
    "Consequently the fixed-bin state has complexity at least `D_2 + 1`".
* **Cross-anchors opened first-hand for this tranche:** `09:834--860`
  (`lem:terminal-two-stream`'s statement, whose binders this claim inherits),
  `09:482--656` (`def:two-stream-state`, in particular clauses (i)--(iii) which
  supply the fixed-bin carriers), `09:658--832` (`lem:terminal-state-realization`
  and its proof, which fixes the two template bins `p_o, p_f` and the sections
  `iota_o, iota_f, sigma_*` this module restricts through), `09:1035--1173` (the
  Stage-3 lift, read only to confirm that `eq:terminal-fixed-bin` is consumed
  there and re-derived rather than assumed -- `09:1101--1103`), `06:1103--1167`
  (`sec:extension-call-ledger`, row (ii)) and `08:946--1134`
  (`sec:dense-weighted-count` and `lem:dense-weighted-frontier`, whose abstract
  statement is the one `09:983` substitutes into).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively; the sole import is `TerminalTwoStream`,
  whose ledger row records the same exclusion.

## Repair record (round r1)

This is the r1 generation.  The r0 generation was gated REVISE on one
declaration and carried twelve record defects; nothing else changed.

* **Statement repair (declaration `FixedBinLowerBound`).**  The frozen row-scale
  pin `x_T = 2^{-b_T}` -- `xT = DenseStageFourOpening.xTdepth bT`, with `bT` a
  parameter, exactly as the banked headline binds it at
  `TerminalTwoStream.lean:2131` and in the same binder position -- has been
  **restored** to the claim, and the r0 header sentence asserting that phase 1
  never reads `x_T` has been corrected.  That sentence was false: this module's
  own `fixedBinCols_nonempty` reads `x_T` through the clause-(ii) selector gate.
  Without the pin the claim was not a strengthening of the frozen phase but a
  claim whose Alice carrier could be empty; see the extended note on
  `FixedBinLowerBound` and the scratch probes recorded below.
* **Record repairs (comments only, R1--R12).**  Corrected frozen line spans:
  the two-phase announcement is `09:867--868` (with `09:864--866` for `D_2`);
  the fixed-bin frame `09:916--923`; the row-carrier sentence `09:921--922`;
  the token placement `09:923--925`; coordinatewise uniqueness `09:955--956`;
  the capacity-one exclusion `09:957--963` everywhere (the r0 module cited it two
  different ways); the ordinary-token support `09:1005--1006`; the closing
  comparison `09:1023--1028`; and the Extension dispatch spans beginning at
  `09:1014`, not the blank `09:1013`.  Prose repairs: `stage2_capacity_trichotomy`
  no longer claims exclusivity it does not prove;
  `fixedBinLowerBound_arith_hypotheses_consistent` now states which conjuncts it
  actually exhibits and which it does not, and that `probeWidths` lies outside
  the gate-firing regime (the term was "certified regime" until the `cc-t7p`
  sweep renamed it -- see `TerminalTwoStream.extProbeWidths`); and
  `fixedBinLowerBound_hypotheses_from_terminal` now
  says in its first line that it proves one conjunct, not an implication between
  binder sets.

## Verify-seat record repair (round r1, post-gate)

The r1 statement gate returned `TRANCHE_VERDICT: CLEAR` on all 43 declarations
and itemized twelve further **record** defects (RD-1..RD-12) -- wrong or
imprecise frozen line spans attached to mathematics it certified.  Each was
re-verified against the frozen sections first-hand and corrected here; **no
statement, hypothesis, conclusion or proof term was touched**, and the
comment-stripped module is byte-identical to the gated bytes.  The corrections:

* `lem:terminal-two-stream`'s proof block is `09:862--1033` (`09:860` is
  `\end{lemma}`; `\begin{proof}` opens at `862`) -- RD-11, two occurrences.
* `lem:terminal-state-realization` is `09:658--832` (`09:756` is a mid-proof
  `\]`) -- RD-5, two occurrences.
* The Stage-3 lift's consumption of `eq:terminal-fixed-bin` is `09:1101--1103`,
  not `09:1082--1085` -- RD-6.
* The residual `09:915--*` spans now open at `916` (`09:915` is blank; the frame
  opens `Fix the pair of Stage-3 template bins ...`) -- RD-3.
* The transposition is `09:917--918`, not `09:916` -- RD-4, two occurrences.
* The fixed-bin row/column carrier sentence is `09:921--923`, not `09:919--920`
  (which is the contradiction hypothesis and the budget-scoping sentence)
  -- RD-1 and RD-2.
* The witness-count substitution behind `hwitness` is `09:986--988`, not
  `09:981--983` -- RD-12.
* `stoppingCapacity` is `08:986--989` (the display `kappa_v = 2^{r-d_v}` sits at
  `08:988`), matching the banked predecessor's own citation, not `08:1113`
  (a `\]`) -- RD-7.
* `eq:isolation-capacity` is labelled at `08:1011`; `08:1130` only `\eqref`s it
  -- RD-8.
* `lem:dense-weighted-frontier` is labelled at `08:1092`, so the span is
  `08:1092--1134` -- RD-10.
* `rho_pair = 99/100` sits at `09:380`, so the `.aMin` / `.rhoPair` citation is
  `09:380--383` -- RD-9.

The 42 declarations the r0 gate found CLEAR are otherwise unchanged.

## Predecessor modules consumed **by pin**, never restated

* `EthInapproximability.ParameterizedNP.TerminalTwoStream` (SHA-256
  `9B9FF040527416FB0042EE5E40EBD220DBDD0283A150699227245423C7A67A89`):
  `terminalEntry`, `terminalSeedInputs`, `terminalTarget`, the three counting
  sets `highSet`, `zoneSet`, `badSet` with the whole Stage-2 counting battery up
  to `stage2_zone_excess`, the Stage-2 ladder evaluations
  `lambdaAt_stage2_frontier` / `lambdaAt_stage2_beyond`, the budget identities
  `stage2_residual_budget` / `stage2_premature_budget` / `stage2_budget`, the
  capacity equivalence `stage2_capacity_one_iff`, the post-Alice density
  comparison `post_alice_density_gt`, the Extension row `extensionCallTwo` with
  `extensionCallTwo_block_count` and `extensionCallTwo_of_widths`, the
  call-(ii) fixed-width binder `ExtensionCallTwoFixedWidth`, and the headline
  claim `TerminalTwoStream` itself.  **None of these is redefined here**; the
  new content is exactly the phase-1 steps that module's GAP-EXPOSED 2 lists as
  not declared.
* `EthInapproximability.ParameterizedNP.TwoStreamState` (SHA-256
  `1DD7EAF859765FEC9D99FCBFED3841E581EA41E09E5150FD0E9B2B08BA378530`):
  the record `TwoStreamState` and its derived readouts `streamRows`,
  `streamImage`, `colFibre`, `fibreDensity`, `meanFibreDensity`,
  `streamImage_nonempty_of_mean_pos`, `foreign_stream_nonempty`.
  `def:two-stream-state` is **never restated**: the fixed-bin carriers below are
  *definitions on the banked record*, exactly as `09:916--917` restricts the
  banked state rather than redefining it.
* `DenseBranchSelection.Dtwo` (`08:152`, `08:769`), `.lambdaZero` (`08:796`),
  `.selectedGood` (`08:730`) and `.selectedWitness` (`08:731`) -- the terminal
  token device of `09:923--925` is the **banked** device at the terminal sets,
  which `terminal_selectedGood` / `terminal_selectedWitness` prove, so
  `DenseRoutingThresholds.tokenWeight` (`08:819--823`) and its total mass
  `sum_tokenWeight` are consumed by pin and never restated.
* `DenseRoutingThresholds.lambdaAt` (`08:812--816`) and
  `StageOneInterlace.xSeed` (`09:477`) -- `lambda_d` and `x = 2^{-b_1}`.
* `DenseWeightedCount.stoppingCapacity` (`08:986--989`),
  `.two_le_stoppingCapacity_of_lt` and `.isolationNode_capacity_at_depth`
  (`eq:isolation-capacity`, `08:1011`) -- `kappa_v = 2^{r_2-d_v}` and the
  isolation-capacity bound, at the Stage-2 exponent `r_2`.
* `DenseFrontierConservation.FrontierArrival`, `.hMass`, `.zMass`,
  `.witnessCount` and `DenseWeightedCount.aliceNodes` / `.isolationNodes` /
  `.PrefixFreeFrontier` -- the frontier bookkeeping carriers.
* `DenseWeightedFrontier.denseWeightedFrontier` (`lem:dense-weighted-frontier`,
  `08:1092--1134`) -- the abstract lemma `09:983` substitutes into.  It is
  **applied**, not restated, and its `hgap` is *discharged* from
  `TerminalTwoStream.stage2_zone_excess`, which is the whole content of
  `09:989--994`.
* `WrapperProjectionCovers.tauZero` (`09:376`) and `.aMin` / `.rhoPair`
  (`09:380--383`) -- read only inside `fixedBinCols_nonempty`.
* `NPCC.D_subgame_mono`, `Workspace.Types.CommComplexity.D`, `NPCC.subgame`,
  `Workspace.Types.Interlace.interlaceFun` -- the vendored, project-axiom-free
  complexity interface reached through `LegacyNPCC.Core`.

## What is new here, and what is deliberately still open

**New (the phase-1 steps the predecessor module lists as not declared).**

1. The two-phase decomposition of the frozen target, `C = (D_2 + 1) + log_2 s`
   (`09:864--866` against `09:1038`), as `fixedBinTarget` and
   `terminalTarget_eq_fixedBinTarget_add`.
2. The fixed-bin carriers of `09:916--923` as `fixedBinRows` / `fixedBinCols`,
   with their containment in the banked rectangle, their nonemptiness at
   **every** two-stream state, and restriction monotonicity into the state.
3. The token placement of `09:923--925`, identified with the banked
   `08:819--823` device (`terminal_selectedGood`, `terminal_selectedWitness`,
   `terminal_sum_tokenWeight`), together with the two counting facts the
   frontier consumes: `|Z| <= |H|` and `|H| + b = q_2`.
4. The exact ordinary-token support at a reached capacity,
   `lambda_{d} = 2 kappa_v 2^{-b_1}` (`09:1005--1006`).
5. The two premature-stop exclusions of `09:957--963` and `09:967--978`, and
   the isolation-capacity bound `h_v + z_v <= kappa_v` of `09:964--965`,
   all in **additive** form (no natural subtraction), and the derivation
   `0 < z_v -> kappa_v >= 2` that the banked `isolationNode_capacity_at_depth`
   takes as its named `htwo`.
6. **The frozen frontier substitution `09:980--994`**: `terminal_first_alice`
   applies the banked `lem:dense-weighted-frontier` at `Coord = [q_2]`,
   `r = r_2`, witness count `|Z|` and bad count `b`, discharging its width
   hypothesis from `q_2 = 2^{r_2}` and its gap hypothesis `4b < w` from
   `eq:terminal-excess`.  This is a *derivation* of `eq:terminal-first-alice`,
   not an assumption of it.
7. The three-case Extension dispatch of `09:1014--1028`: the selection count
   `9 kappa_v/16 <= h_v`, the capacity trichotomy, the capacity-one excess
   dichotomy, and the closing "exceeds `eq:terminal-stage2-budget`" step.
8. `eq:terminal-fixed-bin` itself, as the named claim `FixedBinLowerBound`
   about the pinned construction.

**Deliberately open (GAP-EXPOSED).**

1. **`eq:terminal-fixed-bin` is not proved.**  `FixedBinLowerBound` is landed as
   a named claim, letter exact against `09:1030--1033`, and *stated only*.  No
   declaration below has it as a conclusion, and in particular there is **no**
   theorem deriving it from an assumed frontier verdict: an "assume
   `eq:terminal-first-alice` and conclude `D_2 + 1`" shell would typecheck and
   establish nothing, which is exactly the statement pole this module refuses.
   `terminal_first_alice` runs the other way -- it *produces* the frontier
   verdict from the counting.
2. **The protocol-side routing is not modelled.**  The split-or-route support
   rule (`09:930--935`), the stopping rule and coordinate isolation
   (`09:937--952`), the one-copy and top two-copy residual certificates
   (`09:943--952`), the Alice child selection (`09:1007--1012`), and the
   Localized Extension invocation itself (`09:1014--1019`) are **not** declared.
   What is landed is every arithmetic and counting phase those steps consume or
   produce, at the frozen constants.
3. **The Localized Extension corollary's conclusion is not asserted**, exactly
   as the predecessor module records: `extensionCallTwo` and
   `ExtensionCallTwoFixedWidth` are consumed by pin, and `eq:certified-E3` is
   asserted nowhere.
4. **`sec:wrapper-projection-covers` is untouched.**  This block **feeds**
   `hDenseRung` and neither discharges nor narrows it; the ranges
   `09:1184--1366`, `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly as
   `ScaleAlignOpening` records them, and **no route completion is claimed**.
5. **The headline `lem:terminal-two-stream` is not concluded here.**  This is
   round 1 of the terminal arc; the headline is concluded only at the arc's
   genuine assembly round.  `fixedBinTarget_lt_terminalTarget` records, as a
   machine-checked fact, that the phase-1 target is *strictly smaller* than `C`
   whenever `log_2 s >= 1`, so nothing in this module can be mistaken for the
   headline.

## Canonical inhabitation

`fixedBinRows` and `fixedBinCols` are total functions of the banked
`TwoStreamState` record, so the paper's own instance -- the state produced by
`lem:terminal-state-realization` (`09:658--832`) -- inhabits them by
construction, and the nonemptiness lemmas `fixedBinRows_nonempty` /
`fixedBinCols_nonempty` are proved **at every state**, hence at the paper's.
That is strictly stronger than a synthetic inhabitant.  The concrete readout
`fixedBin_carriers_nonempty_at_probe` evaluates them at the banked
`TwoStreamState.probeState` and is labelled **NON-FIDELITY**: that probe sits at
`q_2 = 2` and therefore outside `eq:terminal-entry` (the banked
`TerminalTwoStream.bankedProbeWidth_is_not_a_terminal_entry_width` records
exactly this), so it is machine evidence about *our encoding*, never a witness
that the frozen regime is inhabited.

`FixedBinLowerBound` is a claim, not a carrier: it has no inhabitation
obligation of its own, and its discharge is the arc's later assembly round.

## Reader counterparts

Frozen release, `reader-facing/`, opened first-hand for this round
(`sections/A-stage4-details.tex`, SHA-256
`5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`).

**No declaration below claims a reader item, and that is a finding about the
reader artifact rather than an omission here.**  Searched first-hand across all
nine reader section files: `D_2`, `49/128`, `9/25`, "fixed bin", "one bit
above", `kappa_v`, and the two budget displays `eq:terminal-stage2-budget` /
`eq:terminal-fixed-bin` occur **nowhere**; the reader compresses the entire
Stage-2 calculation into the single sentence at `A-stage4-details.tex` **lines
387--390** ("At the frontier, the two-stream lemma combines the ordinary `M_1`
robustness, the auxiliary `M_2` robustness, the product-family transfer, and
the Stage--3 selector to contribute the missing bit"), and then says at **lines
396--399** that the count "is expanded line by line in the ultra-explicit
companion" -- which is exactly the frozen `09:862--1033` traced here.  Line
**379** ("After selecting one template bin for each stream ...") is the nearest
reader sentence to `09:916--917` and is recorded here as **navigation only**:
it is prose, and the reader-counterpart discipline bars citing prose as a
statement counterpart.  Reader line **391** stays assigned to
`TerminalTwoStream`'s certified-row-ladder group, `396--399` and `374` stay the
unclaimed prose `WrapperProjectionCovers` recorded, and `361--368` stays
assigned to `WrapperLowRungs.wrapperLowRungs`.  No reader item is assigned
twice.

## Aux-lemma battery

Every battery item is **proved**; nothing is stated and left open.

* `A` the two-phase target, general (5): `fixedBinTarget_eq`,
  `fixedBinTarget_pos`, `terminalTarget_eq_fixedBinTarget_add`,
  `fixedBinTarget_le_terminalTarget`, `fixedBinTarget_lt_terminalTarget`.
* `B` the fixed-bin carriers, general (8): `mem_fixedBinRows`,
  `mem_fixedBinCols`, `fixedBinRows_subset`, `fixedBinCols_subset`,
  `ordinary_stream_image_nonempty`, `fixedBinRows_nonempty`,
  `fixedBinCols_nonempty`, `fixedBin_le_state`.
* `C` the token placement, general (6): `badSet_eq_compl`,
  `terminal_selectedGood`, `zoneSet_subset_highSet`,
  `terminal_selectedWitness`, `terminal_sum_tokenWeight`,
  `terminal_card_highSet_add_badSet`.
* `D` the Stage-2 support ladder at a reached capacity, general (3):
  `lambdaAt_eq_two_mul_capacity_xSeed`, `lambdaAt_capacity_at_frontier`,
  `ordinary_token_support_pos`.
* `E` the exclusions and the isolation capacity, general (4):
  `stage2_capacity_one_exclusion`, `stage2_premature_leaf_exclusion`,
  `stage2_unsplit_pair_forces_capacity_two`, `stage2_isolation_capacity`.
* `F` the frontier substitution, general (2): `stage2_gap_of_excess`,
  `terminal_first_alice`.
* `G` the Extension dispatch and the closing budget, general (5):
  `stage2_selection_count`, `stage2_capacity_trichotomy`,
  `stage2_capacity_one_excess`, `stage2_alice_child_exceeds`,
  `stage2_extension_call_fires`.

That is **33 general battery entries proved**, with `0` unproved, alongside
**three statement poles** (`fixedBinLowerBound_is_not_trivial`,
`fixedBin_bound_is_strictly_weaker_than_C`,
`first_alice_needs_the_counting_gap`), one composition readout
(`fixedBinLowerBound_hypotheses_from_terminal`) and **two non-vacuity readouts**
(`fixedBin_carriers_nonempty_at_probe`,
`fixedBinLowerBound_arith_hypotheses_consistent`).

## HYPOTHESIS-CONSISTENCY note on `FixedBinLowerBound`

The claim's binder set is a **sub-bundle** of `TerminalTwoStream`'s: the banked
width record, the banked `TwoStreamState`, `eq:terminal-entry`, the *first*
clause of `eq:terminal-seed-inputs` (the only one `09:943--952` consumes -- the
second and third are Stage-3 inputs used at `09:1091--1094` and `09:1149--1150`
respectively), the frozen row-scale pin `x_T = 2^{-b_T}`, the checked-identity
pin `y = 3/5`, the call-(ii) fixed-width binder, and the `forall`-form
reached-capacity Extension binder.  Dropping the two Stage-3 clauses and
`s = 2^{r_3}` makes this claim **stronger** than the corresponding restriction
of the headline, which is the correct direction for a phase the later assembly
must supply.  The `x_T` pin is **not** dropped, and repair r1 restored it: it is
the one binder of the headline that phase 1 genuinely reads (through the
clause-(ii) selector gate consumed by `fixedBinCols_nonempty`), so dropping it
would have admitted `x_T <= 0`, at which the Alice carrier is empty and the
conclusion false -- see the extended discussion on `FixedBinLowerBound` itself.
`fixedBinLowerBound_hypotheses_from_terminal` proves that the headline's binder
set supplies the one non-literal binder, so the two compose.

Consistency is inherited: `fixedBinLowerBound_arith_hypotheses_consistent`
exhibits, simultaneously at the banked **balance-minimum** record
`TerminalTwoStream.probeWidths` -- **not** a legal schedule width record, its
`k_2 = 5` failing the `eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}`
(`06:766`), as the closing note of this block records -- and a nondegenerate `eps = 1/100`,
`delta' = 1/10`, exactly these conjuncts of the binder set -- `eq:terminal-entry`,
the `forall`-form reached-capacity Extension binder, that binder's guard both
firing and failing, the phase-1 target, and both premature-stop exclusions at a
concrete nondegenerate `B_cap`.  It does **not** exhibit
`ExtensionCallTwoFixedWidth`, the banked `TwoStreamState` record, the `x_T` and
`y` pins, or the `Lambda` certificate.  That is not a gap in the consistency
argument: the predecessor's `terminalTwoStream_r2_hypotheses_consistent`
discharges the fixed-width binder in full at `extProbeWidths`, and the two pins
are satisfiable by construction (take `xT := DenseStageFourOpening.xTdepth bT`
and `y := 3/5`).  Note also that `probeWidths` -- legal for the four proof
fields of `StageTwoRelaxed.StageTwoWidths`, and **not** for the schedule, whose
`eq:t2-search` floor `06:766` it fails -- sits **outside the gate-firing
regime**: `TerminalTwoStream.extensionGatesFixedWidth_fails_at_balance_minimum`
refutes `eq:all-extension-gates` there outright, and it is `extProbeWidths`, a
BEYOND-PAPER record that fails the same `06:766` floor, that carries the
gate-firing consistency readout.  (Terminology and both legality readings
repaired at `cc-t7p`, ledger item `(b11)`; the predecessor "certified regime"
and the unqualified "legal width record" are WITHDRAWN.)  So this readout is
arithmetic
consistency evidence about the phase-1 conjuncts, never a realizability claim
for the terminal construction.

Machine evidence, recorded by this generation (`scratch/TerminalFixedBinProbes.lean`,
disposable, one `example` expected to fail): the attempted derivation of `False`
from the full arithmetic bundle -- the width record, **both** pins
`x_T = 2^{-b_T}` and `y = 3/5`, `eq:terminal-entry`, the `09:499` parameter
guards `0 <= eps < 1`, `0 < delta' <= 1` carried by `def:two-stream-state`, the
call-(ii) fixed-width binder and the `forall`-form Extension binder -- **fails**,
with `eps < 1/5`, `16 <= q_2`, `lambda_0 <= 1/8`, both exclusions, the target
identity, the inhabited Extension domain at `d = 0`, `0 <= eps_prod < 1/50` and
`0 < x_T` all already in context.  So restoring the pin did not create an
unsatisfiable binder pair.

The same scratch file records the **positive** half of the r1 repair, as four
probes that *do* prove: the pin forces `0 < x_T`; `st.pOrd : Slot s` forces
`0 < s` with no extra binder; hence `fixedBinCols` is nonempty at **every** state
the repaired binder set admits; and the two pins are jointly satisfiable.  That
closes the r0 countermodel -- at `x_T <= 0` the r0 binder set admitted a state
with `P_* = emptyset`, an empty Alice carrier, `D = 0`, and therefore a false
conclusion against `fixedBinTarget_pos`.

What is *not* established, exactly as the predecessor module records: this
module does **not** exhibit a `TwoStreamState` record sitting inside the
terminal regime.  `TerminalTwoStream.bankedProbeWidth_is_not_a_terminal_entry_width`
shows the only banked inhabitant sits at `q_2 = 2` and so fails
`eq:terminal-entry`, and the inherited `Lambda` certificate of `09:847` is not
claimed simultaneously realizable either: it is a Stage-1 hardness input about
`M_1^T`, carried as a certificate and never conjoined with a construction case.
-/

namespace EthInapproximability.ParameterizedNP.TerminalFixedBin

open Finset
open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.TwoStreamState
open EthInapproximability.ParameterizedNP.TerminalTwoStream

/-! ## Section 1  The two-phase target (`09:864--868`, `eq:terminal-fixed-bin`)

`09:864--866` fixes `D_2 = B_cap + log_2 q_2` and `09:867--868` announces the
split: phase 1 proves `D_2 + 1` inside a fixed
Stage-3 bin, phase 2 lifts that bit through the selector to `C`.  `D_2` is the
banked `DenseBranchSelection.Dtwo` and `C` the banked
`TerminalTwoStream.terminalTarget`; neither is redefined. -/

/-- **`eq:terminal-fixed-bin` (label `09:1032`, display `09:1030--1033`).**
"Consequently the fixed-bin state has complexity at least `D_2 + 1`", at the
banked `D_2 = B_cap + log_2 q_2`.  General in the two exponents. -/
def fixedBinTarget (bcap r₂ : ℕ) : ℕ := DenseBranchSelection.Dtwo bcap r₂ + 1

/-- **Aux A1.**  The frozen target expanded: `D_2 + 1 = B_cap + log_2 q_2 + 1`.
General. -/
theorem fixedBinTarget_eq (bcap r₂ : ℕ) : fixedBinTarget bcap r₂ = bcap + r₂ + 1 := by
  simp [fixedBinTarget, DenseBranchSelection.Dtwo]

/-- **Aux A2.**  The phase-1 target is positive, so `eq:terminal-fixed-bin` is
never the empty bound `comp >= 0`.  General. -/
theorem fixedBinTarget_pos (bcap r₂ : ℕ) : 0 < fixedBinTarget bcap r₂ := by
  simp [fixedBinTarget]

/-- **Aux A3 (`09:864--866` against `09:1038`).**  The frozen two-phase
decomposition of the terminal target: `C = (D_2 + 1) + log_2 s`.  This is the
exact sense in which phase 1 proves "a lower bound one bit above `D_2`" and
phase 2 "lifts that bit through the Stage-3 selector".  General. -/
theorem terminalTarget_eq_fixedBinTarget_add (bcap r₂ r₃ : ℕ) :
    terminalTarget bcap r₂ r₃ = fixedBinTarget bcap r₂ + r₃ := by
  simp [terminalTarget, fixedBinTarget, DenseBranchSelection.Dtwo]
  omega

/-- **Aux A4.**  Phase 1 never overshoots the headline target.  General. -/
theorem fixedBinTarget_le_terminalTarget (bcap r₂ r₃ : ℕ) :
    fixedBinTarget bcap r₂ ≤ terminalTarget bcap r₂ r₃ := by
  rw [terminalTarget_eq_fixedBinTarget_add]
  omega

/-- **Aux A5 (phase 2 is not redundant).**  As soon as the Stage-3 exponent is
positive -- i.e. as soon as there is more than one baseline bin -- the phase-1
target is **strictly** below `C`.  So no rearrangement of this module can be
mistaken for `lem:terminal-two-stream`: the missing `log_2 s` bits are exactly
what the selector lift of `09:1035--1173` supplies.  General. -/
theorem fixedBinTarget_lt_terminalTarget {r₃ : ℕ} (bcap r₂ : ℕ) (h : 0 < r₃) :
    fixedBinTarget bcap r₂ < terminalTarget bcap r₂ r₃ := by
  rw [terminalTarget_eq_fixedBinTarget_add]
  omega

/-! ## Section 2  The fixed-bin carriers (`09:916--923`)

"Fix the pair of Stage-3 template bins in clause (ii) of
`def:two-stream-state` and work inside one of them. ...  Bob's columns are then
the disjoint tagged ordinary and foreign `C_1`-fibres, while Alice's rows are
the retained typed subset of `C_2 x C_2`."

The transposition of `09:917--918` decides which party queries first and is internal
to the frozen proof; the *object* whose complexity `eq:terminal-fixed-bin`
bounds is the fixed-bin state itself, so the carriers below are stated on the
untransposed restriction of `Z`.  Both are **definitions on the banked record**,
never a new structure: `def:two-stream-state` already stores the two sections
`iota_o, iota_f` and the section `sigma_*` of clause (ii). -/

variable {Rw Cl Om Cone Ltwo Rone : Type*}

/-- **`09:921--922`.**  The fixed-bin row carrier: the union of the two tagged
`C_1`-fibre streams, i.e. the images of `E_o` and `E_f` under the banked least
sections `iota_o, iota_f` of `09:528--533`.  General in the carriers, the three
widths and the routed data. -/
def fixedBinRows [DecidableEq Rw] [DecidableEq Cone] {q s q₂ : ℕ}
    (omg : Rw → Om) (rho : Slot s → Om → Slot q₂ × Cone) (pOrd pFor : Slot s)
    (XZ : Finset (Slot q × Rw)) (iOrd iFor : Slot q) (RG Rfor : Finset Rw)
    (iotaOrd iotaFor : Slot q₂ × Cone → Slot q × Rw) : Finset (Slot q × Rw) :=
  (streamImage omg rho pOrd XZ iOrd RG).image iotaOrd
    ∪ (streamImage omg rho pFor XZ iFor Rfor).image iotaFor

/-- **`09:921--923` with `09:550--558`.**  The fixed-bin column carrier: the
retained typed subset of `C_2 x C_2`, i.e. the image of the clause-(ii) support
`P_*` under the banked least section `sigma_*`.  General. -/
def fixedBinCols [DecidableEq Cl] {q : ℕ} (Pstar : Finset (Cl × Cl))
    (sigmaStar : Cl × Cl → (Slot q → Cl)) : Finset (Slot q → Cl) :=
  Pstar.image sigmaStar

/-- **Aux B1 (round trip, rows).**  Membership in the fixed-bin row carrier is
"is the chosen representative of an ordinary or of a foreign fibre element".
General. -/
theorem mem_fixedBinRows [DecidableEq Rw] [DecidableEq Cone] {q s q₂ : ℕ}
    {omg : Rw → Om} {rho : Slot s → Om → Slot q₂ × Cone} {pOrd pFor : Slot s}
    {XZ : Finset (Slot q × Rw)} {iOrd iFor : Slot q} {RG Rfor : Finset Rw}
    {iotaOrd iotaFor : Slot q₂ × Cone → Slot q × Rw} {x : Slot q × Rw} :
    x ∈ fixedBinRows omg rho pOrd pFor XZ iOrd iFor RG Rfor iotaOrd iotaFor ↔
      (∃ e ∈ streamImage omg rho pOrd XZ iOrd RG, iotaOrd e = x) ∨
        (∃ e ∈ streamImage omg rho pFor XZ iFor Rfor, iotaFor e = x) := by
  simp [fixedBinRows, Finset.mem_union, Finset.mem_image]

/-- **Aux B2 (round trip, columns).**  General. -/
theorem mem_fixedBinCols [DecidableEq Cl] {q : ℕ} {Pstar : Finset (Cl × Cl)}
    {sigmaStar : Cl × Cl → (Slot q → Cl)} {y : Slot q → Cl} :
    y ∈ fixedBinCols Pstar sigmaStar ↔ ∃ p ∈ Pstar, sigmaStar p = y := by
  simp [fixedBinCols, Finset.mem_image]

section AtState

variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
variable {q s q₂ mT dT : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
  {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
  {RG RSig RD : Finset Rw} {omg : Rw → Om} {rho : Slot s → Om → Slot q₂ × Cone}
  {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
  {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)} {lamT eps2 xT ε δ' : ℝ}

/-- **Aux B3 (`09:921--923`: the fixed-bin rows are rows of `Z`).**  The two
`iota` sections of `def:two-stream-state` land in `X_Z`, so the fixed-bin row
carrier is a genuine restriction of the banked rectangle and not a larger
carrier smuggled in.  General in the state. -/
theorem fixedBinRows_subset
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor st.iotaOrd
        st.iotaFor ⊆ XZ := by
  intro x hx
  rcases mem_fixedBinRows.mp hx with ⟨e, he, hx'⟩ | ⟨e, he, hx'⟩
  · have := st.iotaOrd_mem e he
    rw [hx'] at this
    exact (mem_streamRows.mp this).1
  · have := st.iotaFor_mem e he
    rw [hx'] at this
    exact (mem_streamRows.mp this).1

/-- **Aux B4 (`09:921--923`: the fixed-bin columns are columns of `Z`).**  The
clause-(ii) section `sigma_*` lands in `Y_Z`.  General in the state. -/
theorem fixedBinCols_subset
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    fixedBinCols st.Pstar st.sigmaStar ⊆ YZ := by
  intro y hy
  obtain ⟨p, hp, hy'⟩ := mem_fixedBinCols.mp hy
  exact hy' ▸ st.sigmaStar_mem p hp

/-- **Aux B5 (the ordinary stream is really there).**  `eps < 1` and the
clause-(i) ordinary density `1 - eps <= (1/q_2) sum r_alpha` force `E_o` to be
nonempty.  This is the ordinary-side companion of the banked
`foreign_stream_nonempty`, and it is what stops the "two streams" of
`09:921--923` from degenerating to none.  General in the state. -/
theorem ordinary_stream_image_nonempty
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    (streamImage omg rho st.pOrd XZ st.iOrd RG).Nonempty := by
  refine streamImage_nonempty_of_mean_pos ?_
  have h1 : (0 : ℝ) < 1 - ε := by linarith [st.eps_lt_one]
  exact lt_of_lt_of_le h1 st.ordinary_density

/-- **Aux B6 (the fixed-bin row carrier is nonempty at *every* state).**  Both
tagged streams contribute, so `eq:terminal-fixed-bin` is never a bound on an
empty matrix.  Proved at every `TwoStreamState`, hence in particular at the one
`lem:terminal-state-realization` produces -- see the canonical-inhabitation note
in the module header.  General in the state. -/
theorem fixedBinRows_nonempty
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor st.iotaOrd
      st.iotaFor).Nonempty := by
  obtain ⟨e, he⟩ := ordinary_stream_image_nonempty st
  exact ⟨st.iotaOrd e, mem_fixedBinRows.mpr (Or.inl ⟨e, he, rfl⟩)⟩

/-- **Aux B7 (the fixed-bin column carrier is nonempty at *every* state).**  The
clause-(ii) support `P_*` cannot be empty: `eq:terminal-selector-data` forces
`a_min > tau_0 > 0` at any positive `s` and `x_T`, and
`eq:terminal-physical-pair-density` then forces `|P_*| > 0`.  So the retained
typed subset of `C_2 x C_2` is a genuine Alice carrier.  General in the state,
at the frozen positivity of the Stage-3 width and the row scale. -/
theorem fixedBinCols_nonempty
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hs : 0 < s) (hxT : 0 < xT) :
    (fixedBinCols st.Pstar st.sigmaStar).Nonempty := by
  have hgate := st.selector_gate
  have hden : (0 : ℝ) < (1 + eps2) ^ 2 := by
    rcases (sq_nonneg (1 + eps2)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, div_zero] at hgate
      linarith
  have hnum : (0 : ℝ) < WrapperProjectionCovers.aMin WrapperProjectionCovers.rhoPair lamT
      - WrapperProjectionCovers.tauZero s xT := by
    have hmul := (le_div_iff₀ hden).mp hgate
    nlinarith
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have htau : (0 : ℝ) < WrapperProjectionCovers.tauZero s xT := by
    rw [WrapperProjectionCovers.tauZero]
    have : (0 : ℝ) < 2 * (s : ℝ) := by linarith
    exact mul_pos this hxT
  have hamin : (0 : ℝ) < WrapperProjectionCovers.aMin WrapperProjectionCovers.rhoPair lamT := by
    linarith
  have hpd : (0 : ℝ) < (st.Pstar.card : ℝ) / (mT : ℝ) ^ 2 :=
    lt_of_lt_of_le hamin st.physical_pair_density
  have hne : st.Pstar.Nonempty := by
    rcases Finset.eq_empty_or_nonempty st.Pstar with he | hne
    · rw [he] at hpd
      simp at hpd
    · exact hne
  exact hne.image _

/-- **Aux B8 (the fixed-bin bound is a genuine intermediate).**  The fixed-bin
state is a restriction of `Z`, so restriction monotonicity in the vendored
interface gives `comp(fixed bin) <= comp Z`.  Hence proving
`eq:terminal-fixed-bin` yields `D_2 + 1 <= comp Z` -- **strictly less** than the
frozen `C` whenever `log_2 s >= 1` (Aux A5), which is precisely why
`09:1035--1173` exists.  General in the state. -/
theorem fixedBin_le_state
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    D (subgame (interlaceFun Nmat q)
        (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor
          st.iotaOrd st.iotaFor)
        (fixedBinCols st.Pstar st.sigmaStar))
      ≤ D (subgame (interlaceFun Nmat q) XZ YZ) :=
  D_subgame_mono _ (fixedBinRows_subset st) (fixedBinCols_subset st)

end AtState

/-! ## Section 3  The token placement (`09:923--925`)

"Give each coordinate of `H` one ordinary token and attach one additional
foreign token to each coordinate of `Z`."

This is the **banked** device of `08:819--823` at the terminal sets: the
identities below show that the frozen `H` is `selectedGood b` and the frozen `Z`
is `selectedWitness Z b`, so `DenseRoutingThresholds.tokenWeight` and its total
mass `sum_tokenWeight` apply verbatim and are consumed by pin, never restated. -/

/-- **Aux C1.**  `b = q_2 - |H|` is the complement of `H`, which is what
`badSet` already is.  General. -/
theorem badSet_eq_compl {q₂ : ℕ} (r : Slot q₂ → ℝ) (lam : ℝ) :
    badSet r lam = (highSet r lam)ᶜ := by
  classical
  simp [badSet, Finset.compl_eq_univ_sdiff]

/-- **Aux C2 (the frozen good set is the banked one).**  `H` of `09:883` is
`selectedGood` of `08:730` at the terminal bad set.  General. -/
theorem terminal_selectedGood {q₂ : ℕ} (r : Slot q₂ → ℝ) (lam : ℝ) :
    DenseBranchSelection.selectedGood (badSet r lam) = highSet r lam := by
  classical
  rw [DenseBranchSelection.selectedGood, badSet_eq_compl, compl_compl]

/-- **Aux C3 (`09:885--887`: the bonus tokens sit on ordinary tokens).**
`Z = H cap F subseteq H`.  This is the terminal analogue of the banked
`selectedWitness_subset_selectedGood`, and it is what supplies the
`0 <= z_v <= h_v` hypothesis of `lem:dense-weighted-frontier` at the root.
General. -/
theorem zoneSet_subset_highSet {q₂ : ℕ} (r f : Slot q₂ → ℝ) (lam : ℝ) :
    zoneSet r f lam ⊆ highSet r lam := by
  classical
  intro α hα
  exact (Finset.mem_inter.mp hα).1

/-- **Aux C4 (the frozen witness set is the banked one).**  `Z` of `09:885--886`
is `selectedWitness` of `08:731` at the terminal pair, because `Z` is disjoint
from the bad set.  General. -/
theorem terminal_selectedWitness {q₂ : ℕ} (r f : Slot q₂ → ℝ) (lam : ℝ) :
    DenseBranchSelection.selectedWitness (zoneSet r f lam) (badSet r lam)
      = zoneSet r f lam := by
  classical
  rw [DenseBranchSelection.selectedWitness]
  refine Finset.sdiff_eq_self_of_disjoint ?_
  refine Finset.disjoint_left.mpr ?_
  intro α hα hbad
  rw [badSet_eq_compl, Finset.mem_compl] at hbad
  exact hbad (zoneSet_subset_highSet r f lam hα)

/-- **Aux C5 (`09:923--925`, the frozen total token mass).**  One ordinary token
per coordinate of `H` and one additional foreign token per coordinate of `Z`
carry total weight `|H| + |Z|`.  The device is the banked
`DenseRoutingThresholds.tokenWeight`; nothing about it is redefined here, only
instantiated at the terminal sets.  General in the two density vectors. -/
theorem terminal_sum_tokenWeight {q₂ : ℕ} (r f : Slot q₂ → ℝ) (lam : ℝ) :
    ∑ α ∈ highSet r lam,
        DenseRoutingThresholds.tokenWeight (zoneSet r f lam) (badSet r lam) α
      = (highSet r lam).card + (zoneSet r f lam).card := by
  classical
  have h := DenseRoutingThresholds.sum_tokenWeight (zoneSet r f lam) (badSet r lam)
  rw [terminal_selectedGood, terminal_selectedWitness] at h
  exact h

/-- **Aux C6 (`09:886`, `eq:selected-mass` at the terminal sets).**
`|H| + b = q_2`.  General. -/
theorem terminal_card_highSet_add_badSet {q₂ : ℕ} (r : Slot q₂ → ℝ) (lam : ℝ) :
    (highSet r lam).card + (badSet r lam).card = q₂ := by
  classical
  have h := DenseBranchSelection.card_selectedGood (badSet r lam)
  rw [terminal_selectedGood] at h
  simpa using h

/-! ## Section 4  The ordinary-token support at a reached capacity
(`09:1005--1006`)

"Each ordinary token there has support at least `2 kappa_v 2^{-b_1}`."  At the
frozen dyadic width `q_2 = 2^{r_2}` this is an *identity* for the banked
threshold ladder, not an estimate: `lambda_d = lambda_0 2^{-d}` and
`lambda_0 = 2 q_2 2^{-b_1}` give `lambda_d = 2 kappa_v 2^{-b_1}` at
`kappa_v = 2^{r_2 - d}`. -/

/-- **Aux D1 (`09:1005--1006`).**  The frozen ordinary-token support at a
reached isolation capacity, as an identity between the banked routing threshold
and the banked stopping capacity.  General in the exponents, at any depth at
most the Stage-2 frontier. -/
theorem lambdaAt_eq_two_mul_capacity_xSeed {r₂ d : ℕ} (b₁ : ℕ) (hd : d ≤ r₂) :
    DenseRoutingThresholds.lambdaAt (2 ^ r₂) b₁ d
      = 2 * (DenseWeightedCount.stoppingCapacity r₂ d : ℝ)
          * StageOneInterlace.xSeed b₁ := by
  rw [DenseRoutingThresholds.lambdaAt, DenseBranchSelection.lambdaZero,
    DenseRoutingThresholds.xSeed_eq_inv_pow, DenseWeightedCount.stoppingCapacity_eq]
  have hcast : (((2 : ℕ) ^ r₂ : ℕ) : ℝ) = (2 : ℝ) ^ r₂ := by push_cast; ring
  have hcast' : (((2 : ℕ) ^ (r₂ - d) : ℕ) : ℝ) = (2 : ℝ) ^ (r₂ - d) := by
    push_cast; ring
  rw [hcast, hcast']
  have hsplit : (2 : ℝ) ^ r₂ = (2 : ℝ) ^ (r₂ - d) * 2 ^ d := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  have hb : ((2 : ℝ) ^ b₁) ≠ 0 := by positivity
  have hd' : ((2 : ℝ) ^ d) ≠ 0 := by positivity
  field_simp

/-- **Aux D2 (consistency with the banked frontier evaluation).**  At the
Stage-2 frontier depth the reached capacity is `1`, and Aux D1 reproduces the
banked `lambdaAt_stage2_frontier` value `2^{1-b_1}` exactly.  A drift between
the two frozen readings of `lambda_{r_2}` would show up here.  General. -/
theorem lambdaAt_capacity_at_frontier (r₂ b₁ : ℕ) :
    2 * (DenseWeightedCount.stoppingCapacity r₂ r₂ : ℝ) * StageOneInterlace.xSeed b₁
      = 2 / 2 ^ b₁ := by
  rw [← lambdaAt_eq_two_mul_capacity_xSeed b₁ (le_refl r₂)]
  exact lambdaAt_stage2_frontier r₂ b₁

/-- **Aux D3 (the frozen support floor is not the degenerate `0`).**  At every
depth the ordinary-token support the frozen text quotes is strictly positive, so
none of the support guards `09:943--952` reads off it can be met vacuously.
General. -/
theorem ordinary_token_support_pos (r₂ d b₁ : ℕ) :
    (0 : ℝ) < 2 * (DenseWeightedCount.stoppingCapacity r₂ d : ℝ)
      * StageOneInterlace.xSeed b₁ := by
  have hκ : (0 : ℝ) < (DenseWeightedCount.stoppingCapacity r₂ d : ℝ) := by
    exact_mod_cast DenseWeightedCount.one_le_stoppingCapacity r₂ d
  have hx : (0 : ℝ) < StageOneInterlace.xSeed b₁ := by
    rw [DenseRoutingThresholds.xSeed_eq_inv_pow]
    positivity
  positivity

/-! ## Section 5  The two premature-stop exclusions and the isolation capacity
(`09:953--978`)

Both frozen exclusions are budget counts: the alleged protocol `P_2` has total
depth `D_2`, an object stopped at suffix depth `d` has already spent `d` bits,
and the certificate it still carries demands more than what remains.  They are
stated **additively** -- "spent plus demanded exceeds the total" -- so that no
natural subtraction enters and no `B_cap = 0` corner can make them vacuous. -/

/-- **Aux E1 (`09:957--963`, the capacity-one exclusion).**  "An unsplit
attached pair ... can occur only when `kappa_v >= 2`: if `kappa_v = 1`, then
`d_v = r_2`, while `P_2` has at most `D_2 - r_2 = B_cap` bits remaining,
contradicting the pair's residual complexity `B_cap + 1`."  Additively: at the
frontier depth `r_2` the pair would need `r_2 + (B_cap + 1)` bits, which exceeds
`D_2`.  General. -/
theorem stage2_capacity_one_exclusion (bcap r₂ : ℕ) :
    DenseBranchSelection.Dtwo bcap r₂ < r₂ + (bcap + 1) := by
  simp [DenseBranchSelection.Dtwo]
  omega

/-- **Aux E2 (`09:967--978`, the premature-leaf exclusion).**  "Nor can a token
first reach depth `r_2 + 1`.  Its support would still have density at least
`lambda_{r_2+1} = 2^{-b_1}`, so the one-copy residual would have complexity at
least `B_cap`, whereas the alleged protocol `P_2` would leave at most
`D_2 - (r_2+1) = B_cap - 1` further bits."  Additively: `(r_2 + 1) + B_cap`
exceeds `D_2`.  General. -/
theorem stage2_premature_leaf_exclusion (bcap r₂ : ℕ) :
    DenseBranchSelection.Dtwo bcap r₂ < (r₂ + 1) + bcap := by
  simp [DenseBranchSelection.Dtwo]
  omega

/-- **Aux E3 (`09:957--963`, contrapositive).**  If an unsplit attached pair
*does* survive at suffix depth `d` -- i.e. its `B_cap + 1` certificate still
fits the budget `D_2` after `d` bits have been spent -- then the reached
capacity is at least `2`.  This is exactly the frozen `htwo` premise of the
banked `eq:isolation-capacity`, derived rather than assumed.  General. -/
theorem stage2_unsplit_pair_forces_capacity_two {bcap r₂ d : ℕ}
    (hres : d + (bcap + 1) ≤ DenseBranchSelection.Dtwo bcap r₂) :
    2 ≤ DenseWeightedCount.stoppingCapacity r₂ d := by
  have hlt : d < r₂ := by
    simp only [DenseBranchSelection.Dtwo] at hres
    omega
  exact DenseWeightedCount.two_le_stoppingCapacity_of_lt hlt

/-- **Aux E4 (`09:953--965`, the isolation-capacity bound).**
"Coordinatewise uniqueness leaves at most one routed object there.  An ordinary
object contributes one token, hence at most `kappa_v`.  An unsplit attached pair
contributes two tokens and can occur only when `kappa_v >= 2` ... Thus
`h_v + z_v <= kappa_v` at every isolation node, as required by the weighted
frontier."  The banked `isolationNode_capacity_at_depth` supplies the counting;
what this adds is that its `htwo` premise is discharged by Aux E3 from the
budget rather than assumed.  `huniq` (coordinatewise uniqueness, `09:955--956`)
and `hz` (`z_v <= h_v`) stay named hypotheses, honouring the banked
`DenseRoutingInvariant`'s coverage limit.  General. -/
theorem stage2_isolation_capacity {bcap r₂ d h z : ℕ}
    (huniq : h ≤ 1) (hz : z ≤ h)
    (hres : 0 < z → d + (bcap + 1) ≤ DenseBranchSelection.Dtwo bcap r₂) :
    h + z ≤ DenseWeightedCount.stoppingCapacity r₂ d :=
  DenseWeightedCount.isolationNode_capacity_at_depth huniq hz
    (fun hzpos => stage2_unsplit_pair_forces_capacity_two (hres hzpos))

/-! ## Section 6  The frozen frontier substitution (`09:980--994`)

"The proof of `lem:dense-weighted-frontier` uses only one ordinary component per
good coordinate, one attached bonus component per witness coordinate, the
split-or-route support rule above, and the exclusion of premature leaves.  All
four properties hold for the present labelled fibres.  Substituting witness
count `|Z|` and bad count `b`, and then using `eq:terminal-excess`, shows that
some first-Alice node satisfies `eq:terminal-first-alice`."

The banked lemma is **applied**, never restated.  Its width hypothesis is
discharged from the frozen `q_2 = 2^{r_2}` and its gap hypothesis from
`eq:terminal-excess`; the routing data (`arr`, `route`, `iso`) and the two
properties the banked module left as coverage limits stay explicit binders. -/

/-- **Aux F1 (`eq:terminal-excess` to the frontier's gap hypothesis).**  The
frozen real excess `|Z| - 4b > 2` implies the natural-number gap `4b < |Z|` that
`lem:dense-weighted-frontier` binds.  General in the two counts. -/
theorem stage2_gap_of_excess {z b : ℕ} (h : 2 < (z : ℝ) - 4 * (b : ℝ)) :
    4 * b < z := by
  have : ((4 * b : ℕ) : ℝ) < ((z : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- **`eq:terminal-first-alice` (label `09:993`, display `09:989--994`),
derived.**

"Substituting witness count `|Z|` and bad count `b`, and then using
`eq:terminal-excess`, shows that some first-Alice node satisfies
`h_v >= 3 kappa_v/4`, `h_v + z_v > kappa_v`."

The banked `lem:dense-weighted-frontier` is applied at `Coord = [q_2]`, at the
Stage-2 exponent `r = r_2`, with bad count `b = |b|` and witness count `w = |Z|`
in the frozen substitution.  Two of its four hypotheses are **discharged** here:

* `hselected : 2^{r_2} <= |Coord| + b` from the frozen dyadic width
  `q_2 = 2^{r_2}` (`09:937`), since `|[q_2]| = q_2`;
* `hgap : 4b < w` from `TerminalTwoStream.stage2_zone_excess`, i.e. from
  `eq:terminal-excess` at the banked fibre-density vectors -- this is the
  substitution the frozen sentence performs, and it is the reason this lemma is
  a derivation rather than an assumption of the frontier verdict.

The remaining two stay named binders, exactly as the banked module states them:
`hwitness` (the routed arrivals really carry the `|Z|` witness coordinates,
`09:986--988`) and `hisocap` (`eq:isolation-capacity`, whose terminal
derivation is Aux E4).  The prefix-freeness and depth bounds of the frontier are
the banked `hpf` and `hdepth`.  General in the state, the node type, the routing
and the isolation predicate. -/
theorem terminal_first_alice {Rw Cl Om Cone Ltwo Rone ι : Type*}
    [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] [Fintype Cone]
    [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo] [Fintype ι] [DecidableEq ι]
    {q s q₂ mT dT b₁ r₂ : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
    {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
    {RG RSig RD : Finset Rw} {omg : Rw → Om} {rho : Slot s → Om → Slot q₂ × Cone}
    {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
    {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)} {lamT eps2 xT ε δ' : ℝ}
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hentry : terminalEntry q₂ b₁ ε δ') (hwidth : q₂ = 2 ^ r₂)
    (arr : Slot q₂ → DenseFrontierConservation.FrontierArrival ι)
    (route : ι → List Bool) (iso : ι → Prop) [DecidablePred iso]
    (hpf : DenseWeightedCount.PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r₂)
    (hwitness :
      (zoneSet (fibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG))
          (fibreDensity (streamImage omg rho st.pFor XZ st.iFor st.Rfor))
          (DenseBranchSelection.lambdaZero q₂ b₁)).card
        ≤ DenseFrontierConservation.witnessCount arr
          + (badSet (fibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG))
              (DenseBranchSelection.lambdaZero q₂ b₁)).card)
    (hisocap : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      DenseFrontierConservation.hMass arr v + DenseFrontierConservation.zMass arr v
        ≤ DenseWeightedCount.stoppingCapacity r₂ (route v).length) :
    ∃ v ∈ DenseWeightedCount.aliceNodes iso,
      3 * DenseWeightedCount.stoppingCapacity r₂ (route v).length
          ≤ 4 * DenseFrontierConservation.hMass arr v ∧
        DenseWeightedCount.stoppingCapacity r₂ (route v).length
          < DenseFrontierConservation.hMass arr v
            + DenseFrontierConservation.zMass arr v := by
  classical
  have hselected : 2 ^ r₂ ≤ Fintype.card (Slot q₂)
      + (badSet (fibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG))
          (DenseBranchSelection.lambdaZero q₂ b₁)).card := by
    have hcard : Fintype.card (Slot q₂) = q₂ := Fintype.card_fin q₂
    calc 2 ^ r₂ = q₂ := hwidth.symm
      _ = Fintype.card (Slot q₂) := hcard.symm
      _ ≤ Fintype.card (Slot q₂) + _ := Nat.le_add_right _ _
  have hgap := stage2_gap_of_excess (stage2_zone_excess st hentry)
  exact DenseWeightedFrontier.denseWeightedFrontier arr route iso hpf hdepth
    hselected hwitness hgap hisocap

/-! ## Section 7  The Extension dispatch and the closing budget
(`09:996--1028`)

`eq:terminal-stage2-budget` is banked (`TerminalTwoStream.stage2_budget`); what
this section adds is the frozen three-case dispatch on `kappa_v` and the closing
comparison, again additively. -/

/-- **Aux G1 (`09:1014`).**  "select `9 kappa_v/16` ordinary coordinates".  The
first-Alice conclusion `h_v >= 3 kappa_v/4 = 12 kappa_v/16` leaves at least the
`9 kappa_v/16` ordinary coordinates the Extension call consumes, so the frozen
selection is available and is not an extra demand.  General. -/
theorem stage2_selection_count {κ h : ℕ} (hforced : 3 * κ ≤ 4 * h) : 9 * κ ≤ 16 * h := by
  omega

/-- **Aux G2 (`09:1014--1023`, the frozen three-case dispatch).**  At any reached
capacity **at least one** of the frozen branches applies: `kappa_v >= t_2`
(call (ii) fires), `2 <= kappa_v < t_2` (the inherited two-copy and odd-copy
bounds), or `kappa_v = 1` (the positive excess).  The statement is a
**non-exclusive** disjunction and is deliberately not strengthened to
exclusivity: at the degenerate `t_2 <= 1` the first and third disjuncts hold
together.  Exhaustiveness is all the frozen dispatch needs -- every case reaches
the same target -- and it is the only reading that stays true at every width;
the frozen legality `16 | t_2` of `StageTwoWidths` puts the intended regime at
`t_2 >= 16`, where the three branches are in fact disjoint.  General in the two
widths. -/
theorem stage2_capacity_trichotomy (t₂ κ : ℕ) (hκ : 1 ≤ κ) :
    t₂ ≤ κ ∨ (2 ≤ κ ∧ κ < t₂) ∨ κ = 1 := by
  omega

/-- **Aux G3 (`09:1021--1023`).**  "If `kappa_v = 1`, the positive excess in
`eq:terminal-first-alice` supplies either an unsplit attached pair or two
ordinary coordinates."  At capacity one the frozen strict excess
`h_v + z_v > kappa_v` is exactly this dichotomy.  General. -/
theorem stage2_capacity_one_excess {h z : ℕ} (hexcess : 1 < h + z) : 2 ≤ h ∨ 1 ≤ z := by
  omega

/-- **Aux G4 (`09:1023--1028`, the closing comparison).**  "In every case one
Alice child has complexity at least `B_cap + log_2 kappa_v`, which exceeds
`eq:terminal-stage2-budget`."  At `log_2 kappa_v = r_2 - d_v` this says: the
`d_v + 1` bits already spent, plus the `B_cap + (r_2 - d_v)` the child still
demands, exceed the total budget `D_2`.  Stated additively so that the frozen
`- 1` of `eq:terminal-stage2-budget` never becomes a truncated natural
subtraction.  General, at any suffix depth at most the Stage-2 frontier. -/
theorem stage2_alice_child_exceeds {r₂ d : ℕ} (bcap : ℕ) (hd : d ≤ r₂) :
    DenseBranchSelection.Dtwo bcap r₂ < (d + 1) + (bcap + (r₂ - d)) := by
  simp only [DenseBranchSelection.Dtwo]
  omega

/-- **Aux G5 (`09:1014--1019`, the call-(ii) branch fires with its exact block
count).**  In the frozen branch `kappa_v >= t_2` the headline's reached-capacity
Extension binder yields `extensionCallTwo` at that capacity, and the banked
exactness `06:1126--1130` then gives the frozen selected-block count
`9 kappa_v/16`.  This composes the two banked pieces at the frozen guard and
adds no mathematics.  General in the width record and the depth. -/
theorem stage2_extension_call_fires (W : StageTwoRelaxed.StageTwoWidths) {d : ℕ}
    (hd : d ≤ W.r₂)
    (hbind : ∀ e : ℕ, e ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ e →
        extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ e))
    (hguard : W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d) :
    extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ d)
      ∧ (DenseWeightedCount.stoppingCapacity W.r₂ d / W.t₂) * (9 * W.t₂ / 16)
        = 9 * DenseWeightedCount.stoppingCapacity W.r₂ d / 16 := by
  have hcall := hbind d hd hguard
  exact ⟨hcall, extensionCallTwo_block_count W.t₂_pos W.sixteen_dvd_t₂ hcall⟩

/-! ## Section 8  `eq:terminal-fixed-bin` (`09:1030--1033`), stated

The frozen phase-1 conclusion is transcribed as a named claim about the pinned
construction.  It is **not proved** in this tranche -- see GAP-EXPOSED 1 and 2
-- and no declaration below derives it. -/

/-- **`eq:terminal-fixed-bin` (label `09:1032`, display `09:1030--1033`),
transcribed.**

"Consequently the fixed-bin state has complexity at least `D_2 + 1`."

The *fixed-bin state* is `09:916--923`'s object: the restriction of
`Z = extract(Interlace(N,q), X_Z, Y_Z)` to the two tagged `C_1`-fibre streams
(rows) and the retained typed subset of `C_2 x C_2` (columns), i.e.
`fixedBinRows` and `fixedBinCols` at the banked record.  The transposition of
`09:917--918` fixes which party queries first inside the frozen proof and does not
change the object whose complexity is bounded, so the claim is stated on the
untransposed restriction.

**Binders.**  This is a phase *inside* the proof of `lem:terminal-two-stream`,
so its binders are that lemma's, minus the two clauses of
`eq:terminal-seed-inputs` that only the Stage-3 lift consumes:

* the banked `StageTwoRelaxed.StageTwoWidths` record -- all seven frozen width
  conditions of `07:277--281` plus the balancing gate, exactly as the headline
  takes them, and in particular `4 t_2 <= q_2`, without which the Extension
  binder below is satisfied vacuously;
* the banked `TwoStreamState` record, consumed by pin and never restated;
* `eq:terminal-entry` (`09:838--844`);
* the **first** clause of `eq:terminal-seed-inputs` (`09:847`),
  `Lambda_{M_1^T}(1, 2^{-b_1}, y) >= B_cap`, which is the inherited Stage-1
  one-copy certificate `09:943--948` reads at every ordinary token.  The second
  clause is the Stage-3 certificate used at `09:1091--1094` and the third is the
  row-density legality of `09:1149--1150`; neither enters phase 1, and carrying
  them here would make this claim gratuitously weaker than the frozen phase.
* the frozen row-scale pin `x_T = 2^{-b_T}`, i.e.
  `xT = DenseStageFourOpening.xTdepth bT`, taken **exactly as the banked headline
  binds it** (`TerminalTwoStream.lean:2131`), and in the same binder position;
* the checked-identity pin `y = 3/5` (`05:542`, `09:1137`), which is the column
  threshold the Stage-1 certificate is stated at;
* the call-(ii) fixed-width binder `ExtensionCallTwoFixedWidth`
  (`09:856--858`), including its two `06:1116--1123` balancedness clauses about
  this statement's own `cFam`; and
* the `forall`-form reached-capacity Extension binder of `09:1014`.

`x_T` **is** pinned here, and the pin is load-bearing rather than inherited
decoration: phase 1 reads `x_T` through the clause-(ii) selector gate of
`def:two-stream-state` that `fixedBinCols_nonempty` consumes, since
`eq:terminal-selector-data` is stated at
`WrapperProjectionCovers.tauZero s x_T = 2 s x_T`.  At `x_T <= 0` that gate is
*easier*, so it can be met with a negative `a_min`,
`eq:terminal-physical-pair-density` is then satisfied by `P_* = emptyset`, the
Alice carrier `fixedBinCols` is empty, the subgame has empty domain and its `D`
is `0`, and the conclusion fails against `fixedBinTarget_pos`.  Dropping the pin
would therefore not strengthen the phase toward what the later assembly must
supply; it would make the claim false at parameter values the remaining binders
still permit.  (Repair r1: the r0 generation asserted that phase 1 never reads
`x_T`, which this module's own `fixedBinCols_nonempty` contradicts.)

What this claim still does *not* mention is `s = 2^{r_3}` or the Stage-3
exponent `r_3`, which is the precise sense in which it is the fixed-bin phase
and not the headline; `b_T` enters only as the depth at which the frozen row
scale is read. -/
def FixedBinLowerBound {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo]
    [DecidableEq Ltwo] [Fintype Rone] [DecidableEq Rone]
    (W : StageTwoRelaxed.StageTwoWidths)
    (q s mT dT bcap bT Lh vmax : ℕ) (Nmat : Rw → Cl → Bool)
    (Mmat : Cone → Rone → Bool) (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (rho : Slot s → Om → Slot W.q₂ × Cone) (YT : Slot s → Finset Cl)
    (zeta : Slot s → Cl → Ltwo) (XZ : Finset (Slot q × Rw))
    (YZ : Finset (Slot q → Cl)) (lamT eps2 epsProd xT y ε δ' : ℝ) : Prop :=
  xT = DenseStageFourOpening.xTdepth bT →
    y = 3 / 5 →
    ∀ st : TwoStreamState.TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ',
      terminalEntry W.q₂ W.b₁ ε δ' →
      bcap ≤ LambdaGE Mmat 1 (StageOneInterlace.xSeed W.b₁) y →
      ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd →
      (∀ d : ℕ, d ≤ W.r₂ → W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
        extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ d)) →
      fixedBinTarget bcap W.r₂
        ≤ D (subgame (interlaceFun Nmat q)
            (fixedBinRows omg rho st.pOrd st.pFor XZ st.iOrd st.iFor RG st.Rfor
              st.iotaOrd st.iotaFor)
            (fixedBinCols st.Pstar st.sigmaStar))

/-- **Composition readout (the one non-literal binder).**

**Read the name with its scope.**  Despite reading like a full implication
between binder sets, this theorem proves exactly **one** conjunct: the Stage-1
`Lambda` certificate.  The rest of the composition is *literal* and needs no
theorem -- the pins `x_T = 2^{-b_T}` and `y = 3/5` are two of the headline's
three leading equations and appear here verbatim, and the banked
`TwoStreamState` record, `eq:terminal-entry`, `ExtensionCallTwoFixedWidth` and
the `forall`-form reached-capacity binder are token-identical in the two binder
lists.  What is *not* literal is the Stage-1 certificate: the headline carries
it bundled inside `terminalSeedInputs` together with two Stage-3 clauses, while
`FixedBinLowerBound` isolates it, and this theorem is the projection that shows
the isolated form is available from the bundled one.

So the arc's later assembly round can feed this phase from exactly the
hypotheses the frozen lemma states, with nothing added.  General. -/
theorem fixedBinLowerBound_hypotheses_from_terminal {Cone Rone Ltwo Jtwo : Type*}
    [Fintype Cone] [Fintype Rone] [Fintype Ltwo] [Fintype Jtwo]
    {M1T : Cone → Rone → Bool} {S2 : Ltwo → Jtwo → Bool} {b₁ bcap r₂ r₃ bT : ℕ}
    {xT y : ℝ} (h : terminalSeedInputs M1T S2 b₁ bcap r₂ r₃ bT xT y) :
    bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) y := h.1

/-! ## Section 9  Statement poles

A green build sees none of the three failure modes these record. -/

/-- **Statement pole 1 (the frozen conclusion is not automatic).**  The phase-1
deliverable has no existential, so its pole is the trivial bound: `D_2 + 1 >= 1`
while `comp` of a constant subgame is `0`, so the conclusion fails on a constant
matrix and is not a consequence of the ambient shape.  Any restatement that
weakened the target to `0` would be exactly this triviality. -/
theorem fixedBinLowerBound_is_not_trivial (bcap r₂ : ℕ) :
    ¬ (fixedBinTarget bcap r₂
        ≤ D (subgame (fun _ _ : Unit => false) (Finset.univ : Finset Unit)
              (Finset.univ : Finset Unit))) := by
  have hzero : D (subgame (fun _ _ : Unit => false) (Finset.univ : Finset Unit)
      (Finset.univ : Finset Unit)) = 0 := by
    apply Nat.le_antisymm _ (Nat.zero_le _)
    exact Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.leaf false, rfl,
      by intro a b; rfl⟩
  rw [hzero]
  have := fixedBinTarget_pos bcap r₂
  omega

/-- **Statement pole 2 (this module cannot be mistaken for the headline).**
Restriction monotonicity carries the phase-1 bound into `Z` (`fixedBin_le_state`),
but the number it carries is `D_2 + 1`, and `terminalTarget` is `log_2 s` bits
larger whenever `log_2 s >= 1`.  So even granting `eq:terminal-fixed-bin` in
full, `lem:terminal-two-stream` does **not** follow, and the Stage-3 lift of
`09:1035--1173` is load-bearing.  General. -/
theorem fixedBin_bound_is_strictly_weaker_than_C {r₃ : ℕ} (bcap r₂ : ℕ) (h : 0 < r₃) :
    fixedBinTarget bcap r₂ < terminalTarget bcap r₂ r₃ ∧
      ¬ (terminalTarget bcap r₂ r₃ ≤ fixedBinTarget bcap r₂) := by
  have hlt := fixedBinTarget_lt_terminalTarget (r₃ := r₃) bcap r₂ h
  exact ⟨hlt, by omega⟩

/-- **Statement pole 3 (the frontier substitution genuinely consumes
`eq:terminal-excess`).**  `lem:dense-weighted-frontier`'s gap hypothesis `4b < w`
is not decorative, so `terminal_first_alice` could not have been obtained by
dropping the counting phase.

The witness is the one-node frontier with an **empty** coordinate set, at the
Stage-2 exponent `r_2 = 0`, bad count `b = 1` and witness count `w = 1`, with
every node classified as an Alice node.  At it **every hypothesis of the banked
frontier lemma except the gap holds** -- prefix-freeness and the depth bound
vacuously, `hselected : 2^0 <= 0 + 1`, `hwitness : 1 <= 0 + 1`, and `hisocap`
vacuously because there are no isolation nodes -- while the gap `4 * 1 < 1`
fails and the conclusion fails too: the single Alice node carries
`h_v = z_v = 0`, so `kappa_v < h_v + z_v` is `1 < 0`.

Consequently the frozen sentence "and then using `eq:terminal-excess`"
(`09:983`) is load-bearing: it is exactly what `stage2_zone_excess` supplies in
`terminal_first_alice`. -/
theorem first_alice_needs_the_counting_gap :
    (DenseWeightedCount.PrefixFreeFrontier (fun _ : Fin 1 => ([] : List Bool)))
      ∧ (∀ v : Fin 1, ((fun _ : Fin 1 => ([] : List Bool)) v).length ≤ 0)
      ∧ 2 ^ 0 ≤ Fintype.card Empty + 1
      ∧ (1 : ℕ) ≤ DenseFrontierConservation.witnessCount
          (fun e : Empty => (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) + 1
      ∧ (∀ v ∈ DenseWeightedCount.isolationNodes (fun _ : Fin 1 => False),
          DenseFrontierConservation.hMass
              (fun e : Empty => (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v
            + DenseFrontierConservation.zMass
              (fun e : Empty => (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v
            ≤ DenseWeightedCount.stoppingCapacity 0
                ((fun _ : Fin 1 => ([] : List Bool)) v).length)
      ∧ ¬ (4 * 1 < 1)
      ∧ ¬ ∃ v ∈ DenseWeightedCount.aliceNodes (fun _ : Fin 1 => False),
          3 * DenseWeightedCount.stoppingCapacity 0
                ((fun _ : Fin 1 => ([] : List Bool)) v).length
              ≤ 4 * DenseFrontierConservation.hMass
                (fun e : Empty =>
                  (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v ∧
            DenseWeightedCount.stoppingCapacity 0
                ((fun _ : Fin 1 => ([] : List Bool)) v).length
              < DenseFrontierConservation.hMass
                  (fun e : Empty =>
                    (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v
                + DenseFrontierConservation.zMass
                  (fun e : Empty =>
                    (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v := by
  classical
  have hmass : ∀ v : Fin 1,
      DenseFrontierConservation.hMass
          (fun e : Empty => (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v = 0 :=
    fun v => by simp [DenseFrontierConservation.hMass]
  have hzero : ∀ v : Fin 1,
      DenseFrontierConservation.zMass
          (fun e : Empty => (e.elim : DenseFrontierConservation.FrontierArrival (Fin 1))) v = 0 :=
    fun v => by simp [DenseFrontierConservation.zMass]
  refine ⟨?_, fun _ => le_rfl, by simp, by simp, ?_, by norm_num, ?_⟩
  · intro v w hvw
    exact absurd (Subsingleton.elim v w) hvw
  · intro v _
    rw [hmass v, hzero v]
    exact Nat.zero_le _
  · rintro ⟨v, -, -, hlt⟩
    rw [hmass v, hzero v] at hlt
    simp [DenseWeightedCount.stoppingCapacity] at hlt

/-! ## Section 10  Non-vacuity readouts

The new carriers are inhabited at the banked probe, and the claim's arithmetic
sub-bundle is exhibited at the banked **balance-minimum** width record
`TerminalTwoStream.probeWidths` -- **not** at legal schedule values.  The
predecessor wording "exhibited at legal schedule values" is WITHDRAWN: it was
false.  `probeWidths` is legal for the four proof fields of
`StageTwoRelaxed.StageTwoWidths` only; its `k_2 = 5` fails the `eq:t2-search`
floor `k_2 >= max{4, 2^{19}, m_HS}` (`06:766`, `2^{19} = 524288`), which is why
`Section5Admissibility.stage2Group_refuted_at_balance_minimum` refutes the fourth
admissibility group at it outright.  (Repaired at `cc-t7q`, ledger item
`(b14)`.) -/

/-- **Non-vacuity 1 (the fixed-bin carriers at the banked probe) --
NON-FIDELITY.**  Both carriers are nonempty at `TwoStreamState.probeState`,
whose Stage-3 width `s = 1` and row scale `x_T = 1/200` meet the positivity the
column lemma asks for.  This is machine evidence about *our* encoding at a point
the frozen paper never visits: the banked probe sits at `q_2 = 2`, hence outside
`eq:terminal-entry` (`TerminalTwoStream.bankedProbeWidth_is_not_a_terminal_entry_width`),
so it is **not** a witness that the terminal regime is inhabited.  The fidelity
statement is the pair of general lemmas `fixedBinRows_nonempty` /
`fixedBinCols_nonempty`, which hold at every state including the paper's. -/
theorem fixedBin_carriers_nonempty_at_probe :
    (fixedBinRows TwoStreamState.probeOmg TwoStreamState.probeRho
        TwoStreamState.probeState.pOrd TwoStreamState.probeState.pFor
        TwoStreamState.probeXZ TwoStreamState.probeState.iOrd
        TwoStreamState.probeState.iFor TwoStreamState.probeRG
        TwoStreamState.probeState.Rfor TwoStreamState.probeState.iotaOrd
        TwoStreamState.probeState.iotaFor).Nonempty
      ∧ (fixedBinCols TwoStreamState.probeState.Pstar
          TwoStreamState.probeState.sigmaStar).Nonempty :=
  ⟨fixedBinRows_nonempty TwoStreamState.probeState,
    fixedBinCols_nonempty TwoStreamState.probeState (by norm_num) (by norm_num)⟩

/-- **Non-vacuity 2 (HYPOTHESIS-CONSISTENCY for the phase-1 arithmetic).**

**Exact coverage (repair r1).**  This readout exhibits the *arithmetic*
conjuncts of `FixedBinLowerBound`'s binder set and no others.  It does **not**
exhibit `ExtensionCallTwoFixedWidth`, the banked `TwoStreamState` record, the
two pins `x_T = 2^{-b_T}` and `y = 3/5`, or the `Lambda` certificate.  The
fixed-width binder is discharged in full -- both balancedness fields at the
exact full product -- by the predecessor's
`TerminalTwoStream.terminalTwoStream_r2_hypotheses_consistent` at
`extProbeWidths`, and `FixedBinLowerBound`'s binder set is a sub-bundle of the
one that readout covers; the two pins are satisfiable by construction.  Note
also that `probeWidths` -- legal for the four proof fields of
`StageTwoRelaxed.StageTwoWidths` only, not for the schedule -- has widths
**outside the gate-firing regime** (the note above
`TerminalTwoStream.extProbeWidths`), so what is recorded here is arithmetic
consistency, not realizability.  (Terminology repaired at `cc-t7p`, ledger item
`(b11)`.)

At the banked record `TerminalTwoStream.probeWidths` (`k_2 = 5`,
`r_2 = 7`, `b_1 = 24`, so `q_2 = 128` and `t_2 = 32` -- the minima of those four
proof fields, **not** the frozen schedule's minima, which `06:766` puts at
`k_2 >= 2^{19}`) and a
nondegenerate `B_cap = 5`, the following hold **simultaneously**:

* `eq:terminal-entry` at a nondegenerate `eps = 1/100`, `delta' = 1/10`;
* the `forall`-form reached-capacity Extension binder, in the shape
  `FixedBinLowerBound` binds it;
* the Extension guard genuinely fires somewhere (`d = 2`, capacity `32 >= t_2`)
  and genuinely fails elsewhere (`d = 3`, capacity `16 < t_2`), so the binder is
  neither vacuous nor total, and the frozen middle branch `2 <= kappa_v < t_2`
  is really reached;
* the phase-1 target is the nondegenerate `D_2 + 1 = 13`; and
* both premature-stop exclusions fire at those values.

As in the predecessor module, the inherited `Lambda` certificate of `09:847` is
deliberately **not** claimed simultaneously realizable: it is a Stage-1 hardness
input about `M_1^T`, not an arithmetic side condition.  A satisfiable collection
cannot yield `False`, so no derivation of `False` from the arithmetic sub-bundle
can go through. -/
theorem fixedBinLowerBound_arith_hypotheses_consistent :
    terminalEntry probeWidths.q₂ probeWidths.b₁ (1 / 100) (1 / 10)
      ∧ (∀ d : ℕ, d ≤ probeWidths.r₂ →
          probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ d →
          extensionCallTwo probeWidths.q₂ probeWidths.t₂
            (DenseWeightedCount.stoppingCapacity probeWidths.r₂ d))
      ∧ probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ 2
      ∧ ¬ probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ 3
      ∧ fixedBinTarget 5 probeWidths.r₂ = 13
      ∧ DenseBranchSelection.Dtwo 5 probeWidths.r₂ < probeWidths.r₂ + (5 + 1)
      ∧ DenseBranchSelection.Dtwo 5 probeWidths.r₂ < (probeWidths.r₂ + 1) + 5 := by
  refine ⟨probeEntry_is_nondegenerate.1, probeExtensionCallTwo, by decide, by decide,
    by decide, stage2_capacity_one_exclusion 5 probeWidths.r₂,
    stage2_premature_leaf_exclusion 5 probeWidths.r₂⟩

end EthInapproximability.ParameterizedNP.TerminalFixedBin
