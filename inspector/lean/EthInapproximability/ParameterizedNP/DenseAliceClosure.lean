import EthInapproximability.ParameterizedNP.DenseWeightedFrontier

/-!
# Parameterized NP route: closing the forced Alice node (the ninth dense block)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 1136--1346** --
  `sec:dense-alice-closure`, the Completion of `thm:dense-stage4`, and
  `cor:exact-protected-stage4`.  The anchors traced here, in the order the frozen
  block prints them:
  * the forced-node preamble (`08:1139--1162`): "Fix the Alice frontier node `v`
    supplied by `lem:dense-weighted-frontier`, and abbreviate
    `kappa = kappa_v = 2^{r - d_v}`.  By `lem:dense-routing`, every represented
    coordinate has quotient support at least" `eq:alice-entering-support`
    (`08:1146--1150`), i.e. `lambda_{d_v} = 2 kappa 2^{-b_1}`; "The template rows
    reaching `v` come from one common subset of the indexed family `C_2`, shared by
    all represented coordinates.  Alice's query partitions this common set.  Choose
    the child retaining at least half of it.  Its relaxed template density is at
    least `x_dom/2`, simultaneously on every represented coordinate.  After
    relaxed-to-classical transfer, the corresponding classical density is at least"
    `eq:alice-child-density` (`08:1158--1162`), i.e.
    `(x_dom/2)/(1 + eps_2) >= 49/100 > 9/25`;
  * `lem:dense-extension-closure` (label `08:1168`, statement `08:1167--1173`):
    "If `kappa >= t_2`, the selected Alice child has complexity at least
    `B_cap + log_2 kappa`";
  * its frozen proof (`08:1175--1233`): "Write `r' = kappa/t_2`.  All of
    `q_2, t_2, kappa` are powers of two, so `r'` is a positive power of two and
    `r' <= q_2/t_2`.  Since `h_v >= 3 kappa/4`, we may select exactly
    `r' 9t_2/16 = 9 kappa/16` of the represented coordinates" (`08:1176--1186`);
    "The selected child is a restriction of `S_2 = M_2^T`.  Transpose that child,
    apply the inherited Localized Extension corollary to the corresponding
    restriction of `M_2`, and transpose the conclusion back.  Communication
    complexity is unchanged.  The binder substitution is" the **thirteen-row table**
    of `08:1194--1210`
    (`M := M_1^T`, `\widehat M := M_2`, `H := B_cap`, `x := 2^{-b_1}`, `y := 3/5`,
    `t := t_2`, `q := q_2`, `r := q_2/t_2`, `r' := kappa/t_2`, `eps := eps_2`,
    `p_seed := 9t_2/16`, `h := x_dom`, `a^sharp := 1`);
    "Its per-selected-coordinate support threshold is
    `ceil(r' t_2 2^{-b_1} |C_1|) = ceil(kappa 2^{-b_1} |C_1|)`.  Equation
    `eq:alice-entering-support` supplies twice this density, so every selected
    coordinate may be trimmed to the required integer size.  The stronger gate
    `2 q_2 2^{-b_1} <= 1/8`, together with `kappa <= q_2`, makes every requested
    density legal" (`08:1212--1220`); "The chosen Alice child has relaxed density
    `x_dom/2`.  The same physical Stage-2 family was certified at auxiliary density
    `2^{-b_T} <= x_dom`; the Extension column-loss and seed comparisons are monotone
    in the entering density.  The explicit inequalities verified in
    `sec:parameters`, together with `eq:alice-child-density`, therefore discharge
    the remaining hypotheses of Localized Extension.  Its conclusion is
    `B_cap + log_2 t_2 + log_2 r' = B_cap + log_2 kappa`" (`08:1222--1232`);
  * `lem:dense-small-closure` (label `08:1236`, statement `08:1235--1243`): "If
    `1 <= kappa < t_2`, either the parent already contains a `B_cap + 1`-hard
    unsplit witness at capacity one, or the selected Alice child has complexity at
    least `B_cap + log_2 kappa`";
  * its frozen proof (`08:1245--1296`): "Put `x = 2^{-b_1}`.  Since `kappa` and
    `t_2` are powers of two and `kappa < t_2`, the schedule gives"
    `eq:small-capacity-legal` (`08:1248--1251`), `2 kappa <= t_2 <= 2^{b_1}`; "Thus
    the entering support `2 kappa x` in `eq:alice-entering-support` is at most one
    and can be trimmed to every threshold used below.  The inherited two-copy and
    odd-copy consequences of the Stage-1 robust seed state that"
    `eq:small-two-copy` (`08:1257--1258`) and `eq:small-odd-copy`
    (`08:1259--1263`); "The column requirement `9/25` is met by
    `eq:alice-child-density`.  Four cases exhaust the possible capacities"
    (`08:1265--1292`); "The number of selected coordinates is at most `t_2`, so
    every relaxed-to-classical transfer above lies within the balanced family's
    independence width" (`08:1293--1295`);
  * the **Completion of `thm:dense-stage4`** (`08:1298--1324`): "At suffix depth
    `d_v`, the remaining protocol budget before Alice's query is at most
    `B_cap + r - d_v = B_cap + log_2 kappa`.  After that query, either
    `lem:dense-extension-closure` or `lem:dense-small-closure` gives a child of
    complexity at least this quantity, while only `B_cap + log_2 kappa - 1` further
    bits remain.  The exceptional capacity-one witness case is already harder than
    the parent budget.  Every case is therefore impossible.  It follows that no
    suffix protocol of cost at most `D_2 = B_cap + log_2 q_2` computes the selected
    residual rectangle, contradicting `eq:selected-upper-budget`.  Hence the
    original protocol `P` has cost at least `C`";
  * `cor:exact-protected-stage4` (label `08:1327`, statement `08:1326--1332`): "In
    the `NO` case, `comp N = comp A = comp B = C`", with the frozen proof
    (`08:1334--1339`) "Take the full row and column sets in `thm:dense-stage4`.
    This gives `comp N >= C`.  The labelled duplication and transposition preserve
    complexity, while the direct protocol `eq:stage4-no-upper` gives
    `comp B <= C`.  Hence every inequality is an equality."
* **Predecessor anchors (the banked pins consumed here, never restated):**
  * `EthInapproximability.ParameterizedNP.DenseWeightedFrontier.denseWeightedFrontier`
    -- the forced Alice node of `lem:dense-weighted-frontier`, whose two
    conclusions `3 kappa_v <= 4 h_v` and `kappa_v < h_v + z_v` enter every closure
    statement below as the binders `hforced` and `hexcess`.  All four
    weighted-frontier entry points (`denseWeightedFrontier`,
    `denseWeightedFrontier_real`, `denseWeightedFrontier_of_uniqueness`,
    `denseWeightedFrontier_at_selected_branch`) are the supply side of this block
    and are cited, never re-proved;
  * `EthInapproximability.ParameterizedNP.DenseRoutingInvariant` --
    `lem:dense-routing`, whose endpoint is the banked integral floor
    `routingFloor Gamma (2^r) b_1 d_v`; `eq:alice-entering-support` is proved here
    to be exactly `2 kappa 2^{-b_1}` at that floor's threshold, so the frozen
    "supplies twice this density" becomes the theorem
    `capacityFloor_le_routingFloor`.  Also `routingBound`, `lambdaAt` and the
    routing slack, all consumed by pin;
  * `EthInapproximability.ParameterizedNP.DenseRoutingThresholds` --
    `lem:dense-local-certificates` inside `GAP-EXPOSED(4)`: `denseLocalCertificates`
    and its two halves supply the `B_cap` ordinary certificate and the `B_cap + 1`
    unsplit-witness certificate that case 1 of `lem:dense-small-closure` spends;
    they enter as the binder `hwit`, never as an axiom.  `omegaRoute_gt_capacity_density`
    and `denseFibre_estimate` are the frozen-constant arithmetic this block reuses;
  * `EthInapproximability.ParameterizedNP.DenseBranchSelection` -- `eq:selected-mass`
    (`selectedMass`, `card_selectedGood`, `card_selectedWitness_ge`) and the whole
    `eq:selected-upper-budget` chain (`Dtwo`, `Dtwo_eq`, `selectedResidual_cost_le`),
    which is what the Completion contradicts at `08:1314--1316`.  `xSeed`,
    `xSeed_eq_inv_pow`, `pRoot`, `lambdaZero` and `RoutingSlack` likewise;
  * `EthInapproximability.ParameterizedNP.DenseWeightedCount` -- the weighted-count
    partition: `stoppingCapacity` (the frozen `kappa_v = 2^{r - d_v}`),
    `one_le_stoppingCapacity`, `stoppingCapacity_le_width`, `seedFloor` and
    `trim_to_seed_floor`, plus the frontier classification `aliceNodes` /
    `isolationNodes`;
  * `EthInapproximability.ParameterizedNP.DenseStageFourOpening` -- the opening
    shells: `DenseStageFourConclusion`, `denseStageFour` (the statement shell whose
    single named hypothesis `hnoProtocol` this block supplies at the licensed
    level), `denseFamily_nonempty`, `member_bound_of_no_cheap_protocol`,
    `denseSeparationGates`, `xDom`, `xTdepth`, `transposeN`, `D_transposeN`,
    `protectedDup`, `D_protectedDup`, `cBlock`, `cBlock_pred`.
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**
  * `EXPANDER-001`, the cited `(q_2, t_2, eps_2)`-balanced family of
    `lem:cited-expander-family`, has **no** Lean declaration by design and appears
    in no hypothesis below;
  * the **inherited Localized Extension corollary**
    (`thm:certified-localized-extension`, `A-certified-stopping.tex:110--147`) is
    the named binder `hLocEx` of `denseExtensionClosure`, in the exact implication
    shape the frozen theorem has -- three restriction clauses in, the conclusion
    `H + log_2(r' t)` out.  This is the standing `cc-t2e` discipline: Localized
    Extension endpoints stay named binders and are never re-proved, never assumed
    unconditionally, and never turned into an axiom;
  * the **inherited two-copy and odd-copy consequences of the Stage-1 robust seed**
    (`eq:small-two-copy`, `eq:small-odd-copy`) are the named binders `htwo` and
    `hodd` of `denseSmallClosure`, at their frozen contract anchors: the odd-copy
    lower bound is the still-open binder of `eq:contract-stage1-output`
    (`D-inherited-contracts.tex:872`), whose required reboot facade
    `EthInapproximability.reboot_stage1_certificate` has no inherited declaration
    with that type (`D:882--884`).  Both are gated on exactly the frozen
    preconditions the four-case dispatch establishes before spending them;
  * `Admissible`, `NoCert` and `LevelStep` remain propositional binders, exactly as
    the banked opening shell carries them.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency graph.
* **New work.**  `eq:alice-entering-support` proved as the identity
  `lambda_{d_v} = 2 kappa 2^{-b_1}` at the banked capacity weight; the frozen
  per-selected-coordinate threshold `ceil(kappa 2^{-b_1}|C_1|)` as the definition
  `capacityFloor`, with the frozen "supplies twice this density" proved as an
  inequality against the banked routing floor; the half-retaining child of
  `08:1153--1155`; `eq:alice-child-density` with its frozen-constant arithmetic;
  the thirteen-row binder substitution of `08:1194--1210` discharged clause by
  clause; `eq:small-capacity-legal` and the four-case capacity dispatch; the
  Completion's budget contradiction and its two exceptional readings; and
  `cor:exact-protected-stage4` as a sandwich over the banked complexity-preservation
  pins.
* Proof status: **new** for everything in SS1--SS5 below; **inherited by pin** for
  the capacity weight, the routing floor, the seed density, the separation gates,
  the opening shell, `eq:selected-upper-budget` and both complexity-preservation
  identities.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no unproved
  placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, the proof outline of
`thm:paper-protected-stage4`.  The banked `DenseWeightedFrontier` row claims lines
266--271 and stops there; the remainder of that outline is claimed here, each clause
**once**:

* **lines 272--274**, "The retained template/source and selector/diagonal reservoirs
  close the resulting stopping cases.  Every premature stop leaves either the
  inherited Stage--2 hard subgame or a source witness" -- the closure dichotomy,
  `denseSmallClosure` (the small range) and `denseExtensionClosure` (the Extension
  range);
* **lines 274--277**, "The latter contains the `q_1` template copies, two active
  source copies, and one neutral copy, so `eq:paper-local-capacity` requires
  `D + a + 1` residual bits" -- the capacity-one unsplit-witness branch,
  `denseStageFour_completion_witness_step`;
* **lines 277--279**, "This contradicts the alleged budget and proves the first
  inequality in `eq:paper-protected-dense`" --
  `denseStageFour_completion_step` and `denseStageFour_completion_dichotomy`,
  with `denseStageFour_residual_cost_lower` and `denseStageFourCompletion` the
  passage back to the banked shell;
* **lines 279--281**, "The direct NO protocol for `B`, together with
  `eq:paper-protected-complexity-preservation`, supplies the matching upper bound
  and hence `comp N = C`" -- `exactProtectedStageFour` and
  `exactProtectedStageFour_at_protectedDup`.

The reader's `eq:paper-protected-complexity-preservation` (line 207) is `comp A =
comp B`; it is *cited* by the corollary and is the banked `D_protectedDup`, not a
new claim of this module.  Reader line 240--253 ("The proof is the companion
no-waste proof ...") is a description of method, not an assertion, and is **not**
cited as a statement by anything below.  Lines 283 onwards
(`eq:paper-protected-low`, the reference profile) belong to `sec:raw-low-profile`
and are **not** claimed here.

## Candidate encodings of the per-selected-coordinate threshold (`k = 2`, raced)

The novel object of this tranche is the frozen threshold
`ceil(r' t_2 2^{-b_1} |C_1|) = ceil(kappa 2^{-b_1} |C_1|)` of `08:1212--1216`: the
integer size to which every selected coordinate's quotient support is trimmed.

**Candidate A (landed, SS1).**  A *derived* `Nat.ceil` of the banked seed density,
`capacityFloor Gamma kappa b_1 = ceil(kappa * xSeed b_1 * |Gamma|)`, carrying no
certificate and no node.  It is a function of the banked data alone, so it cannot
disagree with the routing floor: `capacityFloor_two_mul_eq_routingFloor` proves
`capacityFloor Gamma (2 kappa) b_1 = routingFloor Gamma (2^r) b_1 d_v` **on the
nose** at every legal depth, which is exactly the frozen "supplies twice this
density".  Five aux lemmas proved on it, including the round trip to the banked
`seedFloor` at capacity one.

**Candidate B (rejected, SS6).**  Package the threshold with the object it is a
threshold *for*: a record `TrimmedSelection` carrying the selected coordinate set,
its surviving support, the capacity, the depth and the trim inequality.  4 aux
lemmas proved, and it loses on three counts.  First,
`trimmedSelection_floor_is_derived` shows the stored `floor` field restates a
telescope -- it is forced to be `capacityFloor` by the other fields, so a record
that stores it can store a *wrong* one.  Second, `trimmedSelection_capacity_floats`
exhibits two inhabitants with identical support, depth and width but different
recorded capacity, so the record forgets what the frozen datum knows (`kappa` is
`2^{r - d_v}`, determined by the depth).  Third,
`trimmedSelection_is_a_repackaging` proves the record-form trim from Candidate A by
projection, so it adds no mathematics.  The race is decided on faithfulness.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the frozen entering support (`eq:alice-entering-support`), general (2):
  `aliceEnteringSupport`, `aliceEnteringSupport_le_one`.
* `A2` the threshold `capacityFloor`, general (5): `capacityFloor_le`,
  `capacityFloor_mono`, `capacityFloor_zero`, `capacityFloor_one_eq_seedFloor`,
  `capacityFloor_two_mul_eq_routingFloor`.
* `A3` the trim of `08:1216--1218`, general (2): `capacityFloor_le_routingFloor`,
  `trim_to_capacity_floor`.
* `A4` the half-retaining child of `08:1153--1155`, general (2):
  `exists_half_retaining_child`, `halfRetaining_density`.
* `A5` `eq:alice-child-density` (`08:1158--1162`), general (1): `aliceChildDensity`.
* `A6` the frozen table's arithmetic rows (`08:1176--1220`), general (4):
  `extensionRatio_pow`, `extensionSelectionCount`, `extensionSelectedBlocks`,
  `extensionCapacityLegal`.
* `A7` `lem:dense-extension-closure` (`08:1167--1233`), general (1):
  `denseExtensionClosure`.
* `A8` `eq:small-capacity-legal` and the four-case arithmetic (`08:1245--1295`),
  general (5): `smallCapacityLegal`, `smallCase_two_of_capacity_one`,
  `smallCase_two_of_capacity_two`, `smallCase_odd_select`,
  `smallCase_selected_le_width`.
* `A9` the bracket-member step, general (1): `bracketMember_bound`.
* `A10` `lem:dense-small-closure` (`08:1235--1296`), general (1):
  `denseSmallClosure`.
* `A11` the Completion of `thm:dense-stage4` (`08:1298--1324`), general (5):
  `stoppingCapacity_log`, `denseStageFour_completion_step`,
  `denseStageFour_completion_witness_step`, `denseStageFour_completion_dichotomy`,
  `denseStageFour_residual_cost_lower`.
* `A12` the passage back to the banked shell, general (1):
  `denseStageFourCompletion`.
* `A13` `cor:exact-protected-stage4` (`08:1326--1339`), general (2):
  `exactProtectedStageFour`, `exactProtectedStageFour_at_protectedDup`.
* Candidate B's own battery (4): `trimmedSelection_nonempty`,
  `trimmedSelection_floor_is_derived`, `trimmedSelection_capacity_floats`,
  `trimmedSelection_is_a_repackaging`.

That is **32 battery entries proved for the landed candidate plus 4 for the
rejected one**, with `0` unproved, alongside **four statement poles**
(`denseExtensionClosure_pole_needs_endpoint`,
`smallClosure_pole_needs_inherited_bounds`,
`completion_pole_needs_the_child_bound`, `exactProtectedStageFour_pole_needs_upper`)
and **four non-vacuity / consistency readouts**
(`denseExtensionClosure_legal_instance`, `denseSmallClosure_at_capacity_one`,
`denseSmallClosure_dispatch_readout`, `denseSmallClosure_hypotheses_consistent`),
plus `routingFloor_le_card` as the shared legality helper.

The module has **47** source declarations in all: 1 definition (`capacityFloor`),
1 type (`TrimmedSelection`) and 45 proved results; with the structure's constructor
and its 6 field projections that is **54** audited names.  `#print axioms` was run on
all 44 named results outside the structure API and reports `propext`,
`Classical.choice`, `Quot.sound` only.

## Why the deliverables are not satisfied by a trivial witness

Neither closure lemma is existential in a witness: both are **named-def claims about
the pinned construction** -- a lower bound on the complexity of the *selected* Alice
child, at the capacity the banked frontier lemma forces.  The trivial reading to
refute is therefore "the bound holds for free".  It does not:
`denseExtensionClosure_pole_needs_endpoint` exhibits the entire frozen data at legal
values with the conclusion **false** at a child of cost `0`, so the inherited
Localized Extension endpoint is load-bearing; and
`smallClosure_pole_needs_inherited_bounds` exhibits a legal bracket member of a
constant matrix whose subgame has complexity `0`, so `eq:small-two-copy` is genuine
content and not a restatement of its own hypothesis.  The Completion's contradiction
is likewise not vacuous: `completion_pole_needs_the_child_bound` exhibits a budget
assignment satisfying every other clause in which no contradiction follows, so the
child bound is exactly what closes the case.

The one existential in this module is `exists_half_retaining_child`.  Its trivial
witness would be the empty child; it fails because the conclusion demands
`|S| <= 2 |T|` with `T` one of the two *specified* parts, and `S` may be nonempty.

## Three-tier witness legality

* **Tier 1 -- symbolic in the frozen parameters.**  Every result of SS1--SS5 is
  general in the carriers, in `r`, `d_v`, `b_1`, `k_2`, `rho`, `rho'`, `B_cap`,
  `h_v`, `z_v`, in the matrices and in the child object, and takes no schedule
  hypothesis whatever.  Nothing is evaluated, so the frozen widths
  `q_2 = 2^r >= 6144` forced by `eq:stage2-structural-gates` (`06:832--847`) are
  inside the range of every statement.
* **Tier 2 -- fully instantiated legal instances of the block's regime.**
  `denseExtensionClosure_legal_instance` discharges the entire premise bundle of
  `lem:dense-extension-closure` at `r = 6` (`q_2 = 64`), `k_2 = 4` (`t_2 = 16`),
  `rho = 2`, `rho' = 1` (so `kappa = 32 >= t_2`, `r' = 2`), `d_v = 1`, `b_1 = 10`,
  `B_cap = 3`, `h_v = 24`, on `|C_1| = 16`, at the banked
  `denseSeparationGates_satisfiable` values `(s, b_T, m_3, eps_2) = (4, 16, 2^20,
  1/100)` -- with the frozen gate `2 q_2 2^{-b_1} <= 1/8` **attained with
  equality**, `3 kappa <= 4 h_v` **attained with equality**, and the endpoint's
  conclusion `B_cap + log_2 kappa = 8` attained.  `denseSmallClosure_at_capacity_one`
  does the same for the small range at `kappa = 1` with a live unsplit witness.
  Neither is a **schedule** instance: neither satisfies the full
  `eq:stage2-structural-gates`, which forces `q_2 >= 6144`, and no parameter value
  may be read out of either.  Neither needs to: every statement they instantiate is
  tier 1.
* **Tier 3 -- separating probes at deliberately small carriers.**  The four
  statement poles, `denseSmallClosure_dispatch_readout`,
  `denseSmallClosure_hypotheses_consistent` and Candidate B's four readouts are
  probes of one named hypothesis or one field at a minimal carrier.  They are
  neither schedule instances nor legal instances and are cited only for what they
  separate.

## Honest scope and recorded coverage limits

1. **The Localized Extension endpoint is not discharged, and this module does not
   build the transposed restriction of `M_2`.**  `08:1188--1191` ("Transpose that
   child, apply the inherited Localized Extension corollary ... and transpose the
   conclusion back") is *stated* by `hLocEx`'s shape, not carried out: the child is
   an abstract object with an abstract cost, and what is proved is that the frozen
   data discharge all three restriction clauses at the frozen substituted values.
   No consumer may read this module as having applied
   `thm:certified-localized-extension`.
2. **`eq:small-two-copy` and `eq:small-odd-copy` are not inhabited at a concrete
   matrix.**  They are the binders `htwo` and `hodd`;
   `smallClosure_pole_needs_inherited_bounds` records why the constant matrices
   cannot serve.  The odd-copy bound in particular is the still-open binder of
   `eq:contract-stage1-output` (`D:872`), and nothing here upgrades that bar.
3. **The bracket memberships of the selected children stay binders.**  `hsel2` and
   `hselodd` say that once the frozen preconditions hold (`h_v >= 2`, resp.
   `4 <= kappa` and `kappa/2 + 1 <= h_v`, together with the trimmed support) the
   selected rectangle *is* a member of the frozen bracket family.  They are gated
   on exactly those preconditions, so nothing is assumed at points where the frozen
   hypothesis fails; the rectangles themselves are not constructed here.
4. **No routing, no frontier and no protocol tree is constructed.**  As in every
   banked predecessor, the arrival data, the routes and the isolation predicate are
   *given*.  The Completion's per-protocol contradiction is arithmetic over the
   banked `eq:selected-upper-budget` chain; `denseStageFourCompletion` reaches the
   banked shell only through the named hypothesis `hclosure`.
5. **`cor:exact-protected-stage4` does not evaluate the direct NO protocol.**
   `eq:stage4-no-upper` (`07:645`) is the binder `hupper`, and "Take the full row
   and column sets in `thm:dense-stage4`" is the binder `hlower`: extracting the
   full-carrier member from the bracket family is a membership computation this
   module does not perform.
6. **Nothing after `08:1346` is claimed**, and the frozen reading warning of
   `08:1341--1346` ("The argument synchronises only the first `log_2 s` actual
   queries") is respected: no declaration below asserts a Bob-only segment.
7. **`r`, `b_1`, `B_cap`, the carriers and the counts are binders, not values.**  No
   parameter schedule may be read out of any witness below; the tier labelling above
   is binding on consumers.
8. **Candidate B is race evidence with a recorded disposition.**  `TrimmedSelection`
   is consumed by nothing and may not be used to re-encode the threshold of
   `08:1212--1216` without a fresh judged tranche.
9. **Route completion is not claimed.**  The construction and machine layers are
   unlanded; this module lands `sec:dense-alice-closure` as statements plus their
   arithmetic, and the two closure lemmas remain conditional on binders 1--3 above.
-/

namespace EthInapproximability.ParameterizedNP.DenseAliceClosure

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseBranchSelection
open EthInapproximability.ParameterizedNP.DenseRoutingThresholds
open EthInapproximability.ParameterizedNP.DenseRoutingInvariant
open EthInapproximability.ParameterizedNP.DenseWeightedCount

/-! ## §1  The forced-Alice-node preamble (`08:1136--1162`)

"Fix the Alice frontier node `v` supplied by `lem:dense-weighted-frontier`, and
abbreviate `kappa = kappa_v = 2^{r - d_v}`."  The abbreviation is the banked
`stoppingCapacity r d_v`, consumed by pin; what is new here is the arithmetic that
turns `lem:dense-routing`'s threshold into the frozen entering support, the frozen
per-selected-coordinate trim target, the half-retaining child, and the frozen
constant chain of `eq:alice-child-density`. -/

/-- **`eq:alice-entering-support` (`08:1146--1150`).**  "By `lem:dense-routing`,
every represented coordinate has quotient support at least
`lambda_{d_v} = 2 kappa 2^{-b_1}`."

At the frozen width `q_2 = 2^r` (`08:949`) the banked routing threshold `lambda_d`
*is* twice the residual capacity times the seed density.  This is an identity, not
an estimate, and it is the reason the frozen proof can say at `08:1217` that the
entering support "supplies twice" the trim target.  General in `r`, `b_1` and the
suffix depth below the frozen width. -/
theorem aliceEnteringSupport {r b₁ dv : ℕ} (hd : dv ≤ r) :
    lambdaAt (2 ^ r) b₁ dv = 2 * (stoppingCapacity r dv : ℝ) * xSeed b₁ := by
  have hsplit : (r - dv) + dv = r := Nat.sub_add_cancel hd
  have hcap : ((stoppingCapacity r dv : ℕ) : ℝ) = (2 : ℝ) ^ (r - dv) := by
    simp [stoppingCapacity]
  have hpow : (((2 : ℕ) ^ r : ℕ) : ℝ) = (2 : ℝ) ^ (r - dv) * 2 ^ dv := by
    push_cast
    rw [← pow_add, hsplit]
  have hb : ((2 : ℝ) ^ b₁) ≠ 0 := by positivity
  have hdvne : ((2 : ℝ) ^ dv) ≠ 0 := by positivity
  unfold lambdaAt lambdaZero
  rw [xSeed_eq_inv_pow, hcap, hpow]
  field_simp

/-- **Aux 1b (the entering support is a density).**  Under the frozen stronger gate
`2 q_2 2^{-b_1} <= 1/8` of `08:1219` the entering support is at most one, so the
banked routing floor never exceeds the whole quotient carrier.  General. -/
theorem aliceEnteringSupport_le_one {r b₁ dv : ℕ} (hd : dv ≤ r)
    (hgate : 2 * (((2 : ℕ) ^ r : ℕ) : ℝ) * xSeed b₁ ≤ 1 / 8) :
    lambdaAt (2 ^ r) b₁ dv ≤ 1 := by
  have hx : (0 : ℝ) ≤ xSeed b₁ := by rw [xSeed_eq_inv_pow]; positivity
  have hle : ((stoppingCapacity r dv : ℕ) : ℝ) ≤ (((2 : ℕ) ^ r : ℕ) : ℝ) := by
    exact_mod_cast stoppingCapacity_le_width r dv
  have hmul : 2 * ((stoppingCapacity r dv : ℕ) : ℝ) * xSeed b₁
      ≤ 2 * (((2 : ℕ) ^ r : ℕ) : ℝ) * xSeed b₁ := by nlinarith
  rw [aliceEnteringSupport hd]
  linarith

/-- **Aux 2 (a legality helper).**  A threshold that is at most one rounds up to at
most the whole carrier, so the banked routing floor is a legal support size.
General. -/
theorem routingFloor_le_card (Γ : Type*) [Fintype Γ] {q₂ b₁ d : ℕ}
    (h : lambdaAt q₂ b₁ d ≤ 1) : routingFloor Γ q₂ b₁ d ≤ Fintype.card Γ := by
  unfold routingFloor
  refine Nat.ceil_le.2 ?_
  exact mul_le_of_le_one_left (Nat.cast_nonneg _) h

/-- **The frozen per-selected-coordinate support threshold** of `08:1212--1216`,
`ceil(kappa 2^{-b_1} |C_1|)`.

Candidate A: a derived `Nat.ceil` of the banked seed density `xSeed b_1`, carrying
no certificate, no node and no coordinate.  The frozen identity
`ceil(r' t_2 2^{-b_1}|C_1|) = ceil(kappa 2^{-b_1}|C_1|)` is then literally a
rewrite along `kappa = r' t_2`, which is why nothing about the split is stored. -/
noncomputable def capacityFloor (Γ : Type*) [Fintype Γ] (κ b₁ : ℕ) : ℕ :=
  ⌈(κ : ℝ) * xSeed b₁ * (Fintype.card Γ : ℝ)⌉₊

/-- **Aux 3 (the trim target dominates the real density it rounds).**  General. -/
theorem capacityFloor_le (Γ : Type*) [Fintype Γ] (κ b₁ : ℕ) :
    (κ : ℝ) * xSeed b₁ * (Fintype.card Γ : ℝ) ≤ (capacityFloor Γ κ b₁ : ℝ) :=
  Nat.le_ceil _

/-- **Aux 4 (monotone in the capacity).**  A larger residual capacity asks for a
larger trimmed support.  General. -/
theorem capacityFloor_mono (Γ : Type*) [Fintype Γ] {κ κ' b₁ : ℕ} (h : κ ≤ κ') :
    capacityFloor Γ κ b₁ ≤ capacityFloor Γ κ' b₁ := by
  have hx : (0 : ℝ) ≤ xSeed b₁ := by rw [xSeed_eq_inv_pow]; positivity
  have hκ : (κ : ℝ) ≤ (κ' : ℝ) := by exact_mod_cast h
  have hn : (0 : ℝ) ≤ (Fintype.card Γ : ℝ) := Nat.cast_nonneg _
  unfold capacityFloor
  exact Nat.ceil_le_ceil
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hx) hn)

/-- **Aux 5 (degenerate end).**  Zero residual capacity asks for nothing.  General. -/
@[simp] theorem capacityFloor_zero (Γ : Type*) [Fintype Γ] (b₁ : ℕ) :
    capacityFloor Γ 0 b₁ = 0 := by
  unfold capacityFloor
  norm_num

/-- **Aux 6 (round trip to the banked seed floor).**  At capacity one the frozen
threshold *is* the banked `seedFloor` of `08:966`, so the two trims of the block --
the one `lem:dense-routing` performs and the one the Alice closure performs -- speak
about one object.  General. -/
theorem capacityFloor_one_eq_seedFloor (Γ : Type*) [Fintype Γ] (b₁ : ℕ) :
    capacityFloor Γ 1 b₁ = seedFloor Γ b₁ := by
  unfold capacityFloor seedFloor
  congr 1
  push_cast
  ring

/-- **`08:1217`, "supplies twice this density", as an identity.**  Twice the frozen
trim target is *exactly* the banked routing floor at the node's suffix depth.
General below the frozen width. -/
theorem capacityFloor_two_mul_eq_routingFloor (Γ : Type*) [Fintype Γ]
    {r b₁ dv : ℕ} (hd : dv ≤ r) :
    capacityFloor Γ (2 * stoppingCapacity r dv) b₁ = routingFloor Γ (2 ^ r) b₁ dv := by
  unfold capacityFloor routingFloor
  congr 1
  rw [aliceEnteringSupport hd]
  push_cast
  ring

/-- **`08:1216--1218`, the frozen trim.**  "Equation `eq:alice-entering-support`
supplies twice this density, so every selected coordinate may be trimmed to the
required integer size."  General. -/
theorem capacityFloor_le_routingFloor (Γ : Type*) [Fintype Γ] {r b₁ dv : ℕ}
    (hd : dv ≤ r) :
    capacityFloor Γ (stoppingCapacity r dv) b₁ ≤ routingFloor Γ (2 ^ r) b₁ dv := by
  rw [← capacityFloor_two_mul_eq_routingFloor Γ (b₁ := b₁) hd]
  exact capacityFloor_mono Γ (by omega)

/-- **The trim, consumed at a node.**  A routed object meeting the banked routing
floor at suffix depth `d_v` can be trimmed to the frozen threshold
`ceil(kappa 2^{-b_1}|C_1|)`.  The routing-floor hypothesis is the endpoint of
`lem:dense-routing`, consumed **by pin**; nothing here re-proves it.  General. -/
theorem trim_to_capacity_floor {Γ : Type*} [Fintype Γ] {r b₁ dv : ℕ} {T : Finset Γ}
    (hinv : routingFloor Γ (2 ^ r) b₁ dv ≤ T.card) (hd : dv ≤ r) :
    capacityFloor Γ (stoppingCapacity r dv) b₁ ≤ T.card :=
  le_trans (capacityFloor_le_routingFloor Γ hd) hinv

/-- **`08:1151--1154`, the half-retaining child.**  "The template rows reaching `v`
come from one common subset of the indexed family `C_2`, shared by all represented
coordinates.  Alice's query partitions this common set.  Choose the child retaining
at least half of it."

Alice's query is a two-way partition of the physical columns, so the common subset
`S` is covered by the two children `S_0, S_1`; disjointness is *not* needed and is
therefore not demanded.  The conclusion names which child was chosen, records that
it is a subset of the common set, and gives the frozen "at least half" in the
subtraction-free form `|S| <= 2 |T|`.

*Why the trivial witness fails.*  The empty child does not work: `T` is required to
be one of the two specified parts, and `|S| <= 2|T|` fails at `T = empty` whenever
`S` is nonempty. -/
theorem exists_half_retaining_child {L : Type*} [DecidableEq L]
    (S S₀ S₁ : Finset L) (hcover : S ⊆ S₀ ∪ S₁) :
    ∃ T : Finset L, (T = S ∩ S₀ ∨ T = S ∩ S₁) ∧ T ⊆ S ∧ S.card ≤ 2 * T.card := by
  have hunion : S ∩ S₀ ∪ S ∩ S₁ = S := by
    rw [← Finset.inter_union_distrib_left]
    exact Finset.inter_eq_left.2 hcover
  have hcard : S.card ≤ (S ∩ S₀).card + (S ∩ S₁).card := by
    calc S.card = (S ∩ S₀ ∪ S ∩ S₁).card := by rw [hunion]
      _ ≤ (S ∩ S₀).card + (S ∩ S₁).card := Finset.card_union_le _ _
  by_cases h : (S ∩ S₁).card ≤ (S ∩ S₀).card
  · exact ⟨S ∩ S₀, Or.inl rfl, Finset.inter_subset_left, by omega⟩
  · exact ⟨S ∩ S₁, Or.inr rfl, Finset.inter_subset_left, by omega⟩

/-- **`08:1154--1155`, the density of the retained child.**  "Its relaxed template
density is at least `x_dom/2`, simultaneously on every represented coordinate."
Halving the count halves the density, at every carrier size.  General. -/
theorem halfRetaining_density {L : Type*} {S T : Finset L} {x m : ℝ}
    (hS : x * m ≤ (S.card : ℝ)) (hhalf : S.card ≤ 2 * T.card) :
    x / 2 * m ≤ (T.card : ℝ) := by
  have h2 : ((S.card : ℝ)) ≤ 2 * (T.card : ℝ) := by exact_mod_cast hhalf
  linarith

/-- **`eq:alice-child-density` (`08:1156--1162`).**  "After relaxed-to-classical
transfer, the corresponding classical density is at least
`(x_dom/2)/(1 + eps_2) >= 49/100 > 9/25`."

The first inequality is the fifth clause of the banked `eq:dense-separation-gates`,
consumed by pin; the second is the frozen constant comparison `49/100 > 36/100`,
which is what makes the column requirement of the odd-copy bracket
(`eq:local-capacity-gap`, column density `9/25`) available at the selected child.
General in `s`, `b_T`, `m_3` and `eps_2`. -/
theorem aliceChildDensity {s bT m₃ : ℕ} {ε₂ : ℝ}
    (hg : denseSeparationGates s bT m₃ ε₂) :
    (49 : ℝ) / 100 ≤ xDom s bT m₃ / 2 / (1 + ε₂)
      ∧ (9 : ℝ) / 25 < xDom s bT m₃ / 2 / (1 + ε₂) := by
  have h := hg.2.2.2.2
  exact ⟨h, by linarith⟩

/-! ## §2  `lem:dense-extension-closure` (`08:1167--1233`)

"If `kappa >= t_2`, the selected Alice child has complexity at least
`B_cap + log_2 kappa`."

The frozen proof is one call of the inherited Localized Extension corollary at the
thirteen-row binder substitution of `08:1194--1210`.  Following the standing `cc-t2e`
discipline, **the endpoint is a named binder**: the content landed here is that the
frozen data discharge each of its restriction clauses at the substituted values, and
that its conclusion `H + log_2(r' t)` is the frozen `B_cap + log_2 kappa`.

The exponent binders are named, never recovered by `Nat.log` from the widths, exactly
as `eq:contract-extension-exponents` demands (`D:747--757`): `t_2 = 2^{k_2}`,
`q_2 = 2^{rho + k_2}`, `kappa = 2^{rho' + k_2}` with `rho' <= rho`.  In that shape the
frozen case hypothesis `kappa >= t_2` and the frozen `r' <= q_2/t_2` are *consequences*
rather than extra assumptions, which is the point of naming the exponents. -/

/-- **`08:1176--1181`, the ratio row of the table.**  "Write `r' = kappa/t_2`.  All of
`q_2, t_2, kappa` are powers of two, so `r'` is a positive power of two and
`r' <= q_2/t_2`."  In exponent form: `kappa = 2^{rho'} t_2`, the quotient is positive,
it is dominated by `q_2/t_2`, and both `t_2 <= kappa` and `kappa <= q_2` follow.
General. -/
theorem extensionRatio_pow {k₂ ρ ρ' : ℕ} (hρ : ρ' ≤ ρ) :
    (2 : ℕ) ^ (ρ' + k₂) = 2 ^ ρ' * 2 ^ k₂ ∧ 1 ≤ (2 : ℕ) ^ ρ'
      ∧ (2 : ℕ) ^ ρ' ≤ 2 ^ ρ
      ∧ (2 : ℕ) ^ k₂ ≤ 2 ^ (ρ' + k₂)
      ∧ (2 : ℕ) ^ (ρ' + k₂) ≤ 2 ^ (ρ + k₂) := by
  refine ⟨pow_add 2 ρ' k₂, Nat.one_le_pow _ _ (by norm_num), ?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by norm_num) hρ
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`08:1182--1186`, the selection row.**  "Since `h_v >= 3 kappa/4`, we may select
exactly `r' 9t_2/16 = 9 kappa/16` of the represented coordinates."  Cleared of
denominators, that is `9 kappa <= 16 h_v`, which is the shape the represented-block
clause of the inherited endpoint is stated in.  General and subtraction-free. -/
theorem extensionSelectionCount {κ h : ℕ} (hforced : 3 * κ ≤ 4 * h) :
    9 * κ ≤ 16 * h := by omega

/-- **`08:1184`, the seed-count identity of the table.**  `r' p_seed = r' (9 t_2/16)`
is `9 kappa/16` exactly, with no rounding, because the frozen `t` of
`thm:certified-localized-extension` is "a power of two divisible by `16`"
(`A:120--121`) -- which is the hypothesis `4 <= k_2`.  General. -/
theorem extensionSelectedBlocks {ρ' k₂ : ℕ} (hk : 4 ≤ k₂) :
    2 ^ ρ' * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (ρ' + k₂) / 16 := by
  obtain ⟨j, rfl⟩ : ∃ j, k₂ = j + 4 := ⟨k₂ - 4, by omega⟩
  have hA : (2 : ℕ) ^ (j + 4) = 2 ^ j * 16 := by
    rw [pow_add]; norm_num
  have hB : (2 : ℕ) ^ (ρ' + (j + 4)) = 2 ^ (ρ' + j) * 16 := by
    rw [show ρ' + (j + 4) = (ρ' + j) + 4 by omega, pow_add]; norm_num
  have hC : (9 : ℕ) * (2 ^ j * 16) / 16 = 9 * 2 ^ j := by omega
  have hD : (9 : ℕ) * (2 ^ (ρ' + j) * 16) / 16 = 9 * 2 ^ (ρ' + j) := by omega
  rw [hA, hB, hC, hD, pow_add]
  ring

/-- **`08:1219--1220`, the legality row.**  "The stronger gate `2 q_2 2^{-b_1} <= 1/8`,
together with `kappa <= q_2`, makes every requested density legal."  Three readouts
are needed downstream: the selected-coordinate density `kappa 2^{-b_1} <= 1/16`, the
inherited guard `t x <= 1` of `thm:certified-localized-extension` (`A:122`), and the
entering density `2 kappa 2^{-b_1} <= 1`.  General. -/
theorem extensionCapacityLegal {q₂ κ t₂ b₁ : ℕ}
    (hgate : 2 * (q₂ : ℝ) * xSeed b₁ ≤ 1 / 8)
    (hκq : κ ≤ q₂) (htκ : t₂ ≤ κ) :
    (κ : ℝ) * xSeed b₁ ≤ 1 / 16 ∧ (t₂ : ℝ) * xSeed b₁ ≤ 1
      ∧ 2 * (κ : ℝ) * xSeed b₁ ≤ 1 := by
  have hx : (0 : ℝ) ≤ xSeed b₁ := by rw [xSeed_eq_inv_pow]; positivity
  have h1 : (κ : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hκq
  have h2 : (t₂ : ℝ) ≤ (κ : ℝ) := by exact_mod_cast htκ
  have hk : (κ : ℝ) * xSeed b₁ ≤ (q₂ : ℝ) * xSeed b₁ := by nlinarith
  have ht : (t₂ : ℝ) * xSeed b₁ ≤ (κ : ℝ) * xSeed b₁ := by nlinarith
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **`lem:dense-extension-closure` (`08:1167--1233`).**

"If `kappa >= t_2`, the selected Alice child has complexity at least
`B_cap + log_2 kappa`."

*The thirteen-row binder substitution of `08:1194--1210*, carried as explicit named
binders and never as a bundle:

| theorem parameter | present value | how it appears below |
| --- | --- | --- |
| `M` | `M_1^T` | the seed matrix of `hLocEx`, left abstract in the endpoint |
| `\widehat M` | `M_2` | the ambient of the selected child, abstract as `child` |
| `H` | `B_cap` | the binder `bcap` |
| `x` | `2^{-b_1}` | the banked `xSeed b₁` |
| `y` | `3/5` | the banked column floor, inside `hLocEx` |
| `t` | `t_2` | `2 ^ k₂`, exponent named (`D:747--757`) |
| `q` | `q_2` | `2 ^ r`, with `hwidth : 2 ^ r = 2 ^ (ρ + k₂)` |
| `r` | `q_2/t_2` | `2 ^ ρ` |
| `r'` | `kappa/t_2` | `2 ^ ρ'`, with `hρ : ρ' ≤ ρ` |
| `eps` | `eps_2` | the binder `ε₂`, with `hε : 0 ≤ ε₂` |
| `p_seed` | `9 t_2/16` | `extensionSelectedBlocks`, needing `4 ≤ k₂` |
| `h` | `x_dom` | the banked `xDom s bT m₃` |
| `a^sharp` | `1` | the column clause `h 2^{-a#} = x_dom/2` |

The **inherited Localized Extension corollary is the named binder `hLocEx`**, in the
exact implication shape `thm:certified-localized-extension` has: its three
restriction clauses in (`08:1184` represented blocks, `08:1212--1216` rows per
represented block, `08:1222--1228` column density), its guard `t x <= 1` in, and its
conclusion `H + log_2(r' t)` out.  What is *proved* here is that the frozen data
discharge each antecedent: `hforced` (the banked forced-node bound of
`lem:dense-weighted-frontier`) gives the block count, the banked routing floor gives
the row floor through `trim_to_capacity_floor`, the frozen gate gives the guard, and
`eq:alice-child-density` gives the column density.  The final rewrite
`B_cap + log_2 t_2 + log_2 r' = B_cap + log_2 kappa` (`08:1230--1232`) is the
injectivity of `n |-> 2^n`, so nothing is recovered by `Nat.log`.

Note that the frozen case hypothesis `kappa >= t_2` is *not* an extra binder: in the
exponent shape it is `rho' >= 0`, and `extensionRatio_pow` derives it.

General in the quotient carrier, in the child object and its cost, in `r`, `d_v`,
`b_1`, `k_2`, `rho`, `rho'`, `B_cap`, `h_v`, and in the schedule data `s, b_T, m_3,
eps_2`; no schedule hypothesis beyond the block's own gates appears.

*Why the conclusion is not free.*  `denseExtensionClosure_pole_needs_endpoint`
exhibits the whole frozen data at legal values with the conclusion **false** at a
child of cost `0`, so `hLocEx` carries the bound. -/
theorem denseExtensionClosure {Γ : Type*} [Fintype Γ] {Child : Type*}
    (childCost : Child → ℕ) (child : Child)
    {r dv b₁ k₂ ρ ρ' bcap hv s bT m₃ : ℕ} {ε₂ dens : ℝ} {T : Finset Γ}
    (hdepth : dv ≤ r)
    (hwidth : (2 : ℕ) ^ r = 2 ^ (ρ + k₂))
    (hcap : stoppingCapacity r dv = 2 ^ (ρ' + k₂))
    (hρ : ρ' ≤ ρ) (hk : 4 ≤ k₂)
    (hforced : 3 * stoppingCapacity r dv ≤ 4 * hv)
    (hinv : routingFloor Γ (2 ^ r) b₁ dv ≤ T.card)
    (hgate : 2 * (((2 : ℕ) ^ r : ℕ) : ℝ) * xSeed b₁ ≤ 1 / 8)
    (hsep : denseSeparationGates s bT m₃ ε₂) (hε : 0 ≤ ε₂)
    (hchild : xDom s bT m₃ / 2 ≤ dens)
    (hLocEx :
      9 * stoppingCapacity r dv ≤ 16 * hv →
      2 ^ ρ' * (9 * 2 ^ k₂ / 16) = 9 * stoppingCapacity r dv / 16 →
      capacityFloor Γ (stoppingCapacity r dv) b₁ ≤ T.card →
      (((2 : ℕ) ^ k₂ : ℕ) : ℝ) * xSeed b₁ ≤ 1 →
      (9 : ℝ) / 25 < dens / (1 + ε₂) →
      bcap + (ρ' + k₂) ≤ childCost child) :
    bcap + (r - dv) ≤ childCost child := by
  have hexp : r - dv = ρ' + k₂ :=
    Nat.pow_right_injective (le_refl 2) (by simpa [stoppingCapacity] using hcap)
  -- the frozen block count
  have hblocks : 9 * stoppingCapacity r dv ≤ 16 * hv := extensionSelectionCount hforced
  -- the frozen seed-count identity
  have hseed : 2 ^ ρ' * (9 * 2 ^ k₂ / 16) = 9 * stoppingCapacity r dv / 16 := by
    rw [hcap]; exact extensionSelectedBlocks hk
  -- the frozen trim
  have hrows : capacityFloor Γ (stoppingCapacity r dv) b₁ ≤ T.card :=
    trim_to_capacity_floor hinv hdepth
  -- the frozen legality guard
  have htκ : (2 : ℕ) ^ k₂ ≤ stoppingCapacity r dv := by
    rw [hcap]; exact (extensionRatio_pow (k₂ := k₂) hρ).2.2.2.1
  have hκq : stoppingCapacity r dv ≤ (2 : ℕ) ^ r := by
    rw [hcap, hwidth]; exact (extensionRatio_pow (k₂ := k₂) hρ).2.2.2.2
  have hguard : (((2 : ℕ) ^ k₂ : ℕ) : ℝ) * xSeed b₁ ≤ 1 :=
    (extensionCapacityLegal hgate hκq htκ).2.1
  -- the frozen column density
  have hpos : (0 : ℝ) < 1 + ε₂ := by linarith
  have hcol : (9 : ℝ) / 25 < dens / (1 + ε₂) := by
    have hbase := (aliceChildDensity hsep).2
    have hmono : xDom s bT m₃ / 2 / (1 + ε₂) ≤ dens / (1 + ε₂) := by gcongr
    linarith
  have := hLocEx hblocks hseed hrows hguard hcol
  omega

/-! ## §3  `lem:dense-small-closure` (`08:1235--1296`)

"If `1 <= kappa < t_2`, either the parent already contains a `B_cap + 1`-hard unsplit
witness at capacity one, or the selected Alice child has complexity at least
`B_cap + log_2 kappa`."

The inherited two-copy and odd-copy consequences of the Stage-1 robust seed
(`eq:small-two-copy`, `eq:small-odd-copy`) stay named hypotheses at their frozen
contract anchors, and each is **gated on exactly the precondition the frozen
four-case dispatch establishes before spending it** -- `h_v >= 2` for the two-copy
consequence (cases 2 and 3), `kappa >= 4` for the odd-copy one (case 4).  Gating them
is strictly weaker in hypothesis than the frozen unconditional printing, hence
strictly stronger as a theorem. -/

/-- **`eq:small-capacity-legal` (`08:1246--1253`).**  "Since `kappa` and `t_2` are
powers of two and `kappa < t_2`, the schedule gives `2 kappa <= t_2 <= 2^{b_1}`.
Thus the entering support `2 kappa x` in `eq:alice-entering-support` is at most one
and can be trimmed to every threshold used below."

The schedule half `t_2 <= 2^{b_1}` is the banked width record's
`t₂_le_two_pow_b₁`, carried here as the binder `hsched` at named exponents.
General. -/
theorem smallCapacityLegal {e k₂ b₁ : ℕ} (hlt : e < k₂)
    (hsched : (2 : ℕ) ^ k₂ ≤ 2 ^ b₁) :
    2 * (2 : ℕ) ^ e ≤ 2 ^ k₂ ∧ 2 * (((2 : ℕ) ^ e : ℕ) : ℝ) * xSeed b₁ ≤ 1 := by
  have hstep : (2 : ℕ) ^ (e + 1) ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsucc : (2 : ℕ) ^ (e + 1) = 2 ^ e * 2 := pow_succ 2 e
  have hnat : 2 * (2 : ℕ) ^ e ≤ 2 ^ k₂ := by omega
  refine ⟨hnat, ?_⟩
  have hcast : ((2 * (2 : ℕ) ^ e : ℕ) : ℝ) ≤ (((2 : ℕ) ^ b₁ : ℕ) : ℝ) := by
    exact_mod_cast le_trans hnat hsched
  have hp : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  rw [xSeed_eq_inv_pow]
  push_cast at hcast ⊢
  rw [mul_one_div, div_le_one hp]
  linarith

/-- **Case 2 of the dispatch (`08:1275--1277`).**  "Suppose `kappa = 1` and no
unsplit witness is present.  Positive excess gives `h_v >= 2`."  With no unsplit
witness the routed witness mass is zero, so the banked positive excess
`kappa_v < h_v + z_v` is carried entirely by the template mass.  General. -/
theorem smallCase_two_of_capacity_one {h z : ℕ} (hz : z = 0) (hexcess : 1 < h + z) :
    2 ≤ h := by omega

/-- **Case 3 of the dispatch (`08:1280--1281`).**  "Suppose `kappa = 2`.  High
template mass gives `h_v >= 2`."  This is the banked forced-node bound
`3 kappa <= 4 h_v` at `kappa = 2`.  General. -/
theorem smallCase_two_of_capacity_two {h : ℕ} (hforced : 3 * 2 ≤ 4 * h) : 2 ≤ h := by
  omega

/-- **Case 4 of the dispatch (`08:1285--1289`).**  "Suppose `kappa >= 4`.  Since
`h_v >= 3 kappa/4 >= kappa/2 + 1`, select `kappa/2 + 1` ordinary coordinates."
General and subtraction-free. -/
theorem smallCase_odd_select {κ h : ℕ} (hκ : 4 ≤ κ) (hforced : 3 * κ ≤ 4 * h) :
    κ / 2 + 1 ≤ h := by omega

/-- **`08:1293--1295`, the independence-width check.**  "The number of selected
coordinates is at most `t_2`, so every relaxed-to-classical transfer above lies
within the balanced family's independence width."  Both selection sizes the dispatch
uses -- two, and `kappa/2 + 1` -- clear the frozen `2 kappa <= t_2` of
`eq:small-capacity-legal`.  General. -/
theorem smallCase_selected_le_width {κ t₂ : ℕ} (hκ : 1 ≤ κ) (h2 : 2 * κ ≤ t₂) :
    2 ≤ t₂ ∧ (4 ≤ κ → κ / 2 + 1 ≤ t₂) := by
  exact ⟨by omega, fun _ => by omega⟩

/-- **The bracket-member step.**  A lower bound on the family complexity
`comp<M, p, x, y>` bounds **every** member of the bracket family, because `Dfamily`
is a `Nat.sInf` over the members.  This is the step by which the two inherited
consequences of `08:1256--1264` are spent at the *selected* rectangle.  General in
the matrix, the copy count and both densities.

The dual caution is the banked `stage1Certificate_family_nonempty`: a family lower
bound taken over an empty family would be unsound, which is why the frozen text always
exhibits the selected rectangle first. -/
theorem bracketMember_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) {p : ℕ} {x y : ℝ} {c : ℕ}
    (hfam : c ≤ Dfamily (interlaceFun M p) (bracketGE X Y p x y))
    {RC : Finset (Fin p × X) × Finset (Fin p → Y)} (hRC : RC ∈ bracketGE X Y p x y) :
    c ≤ D (subgame (interlaceFun M p) RC.1 RC.2) :=
  le_trans hfam (Nat.sInf_le ⟨RC, hRC, rfl⟩)

/-- **`lem:dense-small-closure` (`08:1235--1296`).**

"If `1 <= kappa < t_2`, either the parent already contains a `B_cap + 1`-hard unsplit
witness at capacity one, or the selected Alice child has complexity at least
`B_cap + log_2 kappa`."

The capacity is written at its named exponent, `kappa = 2^e`, and the frozen case
hypothesis `kappa < t_2` is `e < k_2` (`hsmall`); `hsched` is the schedule's
`t_2 <= 2^{b_1}`.  The conclusion carries both halves the frozen proof states: the
legality readout of `eq:small-capacity-legal`, and the four-case dichotomy.

*The inherited consequences, as named binders at their frozen contract anchors.*
`htwo` is `eq:small-two-copy` -- `comp<M_1^T, 2, 2x, 9/25> >= B_cap + 1` -- gated on
the frozen `h_v >= 2` that cases 2 and 3 establish first.  `hodd` is
`eq:small-odd-copy` -- `comp<M_1^T, kappa/2 + 1, kappa x, 9/25> >= B_cap + log_2
kappa` for `kappa >= 4` -- gated on that same frozen side condition; it is the still
open binder of `eq:contract-stage1-output` (`D:872`), whose required reboot facade
has no inherited declaration with that type (`D:882--884`), and nothing here upgrades
that bar.  `hwit` is the capacity-one unsplit witness's `B_cap + 1` certificate from
`lem:dense-local-certificates` and `lem:dense-routing` (`08:1269--1273`), inside
`GAP-EXPOSED(4)` and consumed by pin, never re-proved.  `hsel2` and `hselodd` are the
two selections of `08:1276--1277` and `08:1289--1290`, gated on exactly the frozen
preconditions; the rectangles they name are not constructed here.

`hnowit` is the frozen reading of "no unsplit witness is present": the routed witness
mass at the node is then zero.

The trimming side conditions are discharged from the banked routing floor:
`capacityFloor Γ 2 b₁` (the `2x` threshold of `eq:small-two-copy`) and
`capacityFloor Γ kappa b₁` (the `kappa x` threshold of `eq:small-odd-copy`) are both
below `capacityFloor Γ (2 kappa) b₁`, which *is* the banked routing floor by
`capacityFloor_two_mul_eq_routingFloor`.

General in the seed matrix, the quotient carrier, `r`, `d_v`, `b_1`, `e`, `k_2`,
`B_cap`, `h_v`, `z_v`, both rectangles and the unsplit-witness predicate. -/
theorem denseSmallClosure {X Y : Type*} [Fintype X] [Fintype Y] (M1T : X → Y → Bool)
    {Γ : Type*} [Fintype Γ]
    {r dv b₁ e k₂ bcap hv zv witCost : ℕ} {T : Finset Γ}
    (UnsplitWitness : Prop)
    (RC2 : Finset (Fin 2 × X) × Finset (Fin 2 → Y))
    (RCodd : Finset (Fin (stoppingCapacity r dv / 2 + 1) × X)
      × Finset (Fin (stoppingCapacity r dv / 2 + 1) → Y))
    (hdepth : dv ≤ r)
    (hcap : stoppingCapacity r dv = 2 ^ e)
    (hsmall : e < k₂) (hsched : (2 : ℕ) ^ k₂ ≤ 2 ^ b₁)
    (hforced : 3 * stoppingCapacity r dv ≤ 4 * hv)
    (hexcess : stoppingCapacity r dv < hv + zv)
    (hinv : routingFloor Γ (2 ^ r) b₁ dv ≤ T.card)
    (hnowit : ¬ UnsplitWitness → zv = 0)
    (hwit : UnsplitWitness → bcap + 1 ≤ witCost)
    (htwo : 2 ≤ hv →
      bcap + 1 ≤ Dfamily (interlaceFun M1T 2)
        (bracketGE X Y 2 (2 * xSeed b₁) (9 / 25)))
    (hodd : 4 ≤ stoppingCapacity r dv →
      bcap + e ≤ Dfamily (interlaceFun M1T (stoppingCapacity r dv / 2 + 1))
        (bracketGE X Y (stoppingCapacity r dv / 2 + 1)
          ((stoppingCapacity r dv : ℝ) * xSeed b₁) (9 / 25)))
    (hsel2 : 2 ≤ hv → capacityFloor Γ 2 b₁ ≤ T.card →
      RC2 ∈ bracketGE X Y 2 (2 * xSeed b₁) (9 / 25))
    (hselodd : 4 ≤ stoppingCapacity r dv → stoppingCapacity r dv / 2 + 1 ≤ hv →
      capacityFloor Γ (stoppingCapacity r dv) b₁ ≤ T.card →
      RCodd ∈ bracketGE X Y (stoppingCapacity r dv / 2 + 1)
        ((stoppingCapacity r dv : ℝ) * xSeed b₁) (9 / 25)) :
    (2 * ((stoppingCapacity r dv : ℕ) : ℝ) * xSeed b₁ ≤ 1
        ∧ 2 * stoppingCapacity r dv ≤ 2 ^ k₂)
      ∧ ((UnsplitWitness ∧ e = 0 ∧ bcap + 1 ≤ witCost)
          ∨ bcap + e ≤ D (subgame (interlaceFun M1T 2) RC2.1 RC2.2)
          ∨ bcap + e ≤ D (subgame (interlaceFun M1T (stoppingCapacity r dv / 2 + 1))
              RCodd.1 RCodd.2)) := by
  classical
  -- `eq:small-capacity-legal`
  obtain ⟨hlegalNat, hlegalReal⟩ := smallCapacityLegal (e := e) (b₁ := b₁) hsmall hsched
  have hlegal : 2 * ((stoppingCapacity r dv : ℕ) : ℝ) * xSeed b₁ ≤ 1 := by
    rw [hcap]; exact hlegalReal
  have hlegal' : 2 * stoppingCapacity r dv ≤ 2 ^ k₂ := by rw [hcap]; exact hlegalNat
  refine ⟨⟨hlegal, hlegal'⟩, ?_⟩
  -- the two trimmed thresholds, from the banked routing floor
  have hone : 1 ≤ stoppingCapacity r dv := one_le_stoppingCapacity r dv
  have hroute : capacityFloor Γ (2 * stoppingCapacity r dv) b₁ ≤ T.card := by
    rw [capacityFloor_two_mul_eq_routingFloor Γ (b₁ := b₁) hdepth]; exact hinv
  have htrim2 : capacityFloor Γ 2 b₁ ≤ T.card :=
    le_trans (capacityFloor_mono Γ (by omega)) hroute
  have htrimκ : capacityFloor Γ (stoppingCapacity r dv) b₁ ≤ T.card :=
    le_trans (capacityFloor_mono Γ (by omega)) hroute
  -- the four-case dispatch of `08:1268--1292`
  rcases Nat.lt_or_ge e 2 with hlow | hhigh
  · -- `kappa in {1, 2}`: the two-copy consequence
    interval_cases e
    · -- case 1 and case 2: `kappa = 1`
      have hκ1 : stoppingCapacity r dv = 1 := by simpa using hcap
      by_cases hw : UnsplitWitness
      · exact Or.inl ⟨hw, rfl, hwit hw⟩
      · have hz : zv = 0 := hnowit hw
        have hhv : 2 ≤ hv := by
          refine smallCase_two_of_capacity_one hz ?_
          omega
        refine Or.inr (Or.inl ?_)
        have := bracketMember_bound M1T (htwo hhv) (hsel2 hhv htrim2)
        omega
    · -- case 3: `kappa = 2`
      have hκ2 : stoppingCapacity r dv = 2 := by simpa using hcap
      have hhv : 2 ≤ hv := by
        refine smallCase_two_of_capacity_two ?_
        omega
      refine Or.inr (Or.inl ?_)
      have := bracketMember_bound M1T (htwo hhv) (hsel2 hhv htrim2)
      omega
  · -- case 4: `kappa >= 4`
    have hκ4 : 4 ≤ stoppingCapacity r dv := by
      rw [hcap]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hhigh
    have hsel : stoppingCapacity r dv / 2 + 1 ≤ hv := smallCase_odd_select hκ4 hforced
    exact Or.inr (Or.inr
      (bracketMember_bound M1T (hodd hκ4) (hselodd hκ4 hsel htrimκ)))

/-! ## §4  Completion of `thm:dense-stage4` (`08:1298--1324`)

"At suffix depth `d_v`, the remaining protocol budget before Alice's query is at most
`B_cap + r - d_v = B_cap + log_2 kappa`.  After that query, either
`lem:dense-extension-closure` or `lem:dense-small-closure` gives a child of complexity
at least this quantity, while only `B_cap + log_2 kappa - 1` further bits remain.  The
exceptional capacity-one witness case is already harder than the parent budget.  Every
case is therefore impossible."

Every step below is subtraction-free: the frozen `B_cap + log_2 kappa - 1` appears as
`childBudget + 1 <= parentBudget`, so no truncated difference is used. -/

/-- **`08:1302`, the two frozen readings of the parent budget agree.**
`log_2 kappa = log_2 2^{r - d_v} = r - d_v`, so `B_cap + r - d_v` and
`B_cap + log_2 kappa` are the same number.  General. -/
@[simp] theorem stoppingCapacity_log (r dv : ℕ) :
    Nat.log 2 (stoppingCapacity r dv) = r - dv := by
  simp [stoppingCapacity]

/-- **`08:1304--1312`, the main contradiction.**  A child that the closure lemmas make
`B_cap + log_2 kappa`-hard cannot be computed inside a budget one bit below the
parent's, when the parent's own budget is at most `B_cap + log_2 kappa`.  General and
subtraction-free. -/
theorem denseStageFour_completion_step {bcap lκ parentBudget childBudget childCost : ℕ}
    (hparent : parentBudget ≤ bcap + lκ)
    (hquery : childBudget + 1 ≤ parentBudget)
    (hcheap : childCost ≤ childBudget)
    (hhard : bcap + lκ ≤ childCost) : False := by omega

/-- **`08:1311--1312`, the exceptional case.**  "The exceptional capacity-one witness
case is already harder than the parent budget."  At capacity one the parent budget is
`B_cap + log_2 1 = B_cap`, while the unsplit witness is `B_cap + 1`-hard.  General. -/
theorem denseStageFour_completion_witness_step {bcap parentBudget witCost : ℕ}
    (hparent : parentBudget ≤ bcap)
    (hwit : bcap + 1 ≤ witCost)
    (hcheap : witCost ≤ parentBudget) : False := by omega

/-- **`08:1304--1312`, both branches together.**  The dichotomy delivered by
`lem:dense-extension-closure` and `lem:dense-small-closure` closes every case at the
frozen budgets.  The capacity-one branch is stated at `e = 0`, where the parent budget
is `B_cap`, exactly as the frozen sentence reads it.  General. -/
theorem denseStageFour_completion_dichotomy
    {bcap e parentBudget childBudget witCost childCost : ℕ}
    (hparent : parentBudget ≤ bcap + e)
    (hquery : childBudget + 1 ≤ parentBudget)
    (hclosure :
      (e = 0 ∧ witCost ≤ parentBudget ∧ bcap + 1 ≤ witCost)
        ∨ (childCost ≤ childBudget ∧ bcap + e ≤ childCost)) : False := by
  rcases hclosure with ⟨he, hcheap, hwit⟩ | ⟨hcheap, hhard⟩
  · exact denseStageFour_completion_witness_step (bcap := bcap) (by omega) hwit hcheap
  · exact denseStageFour_completion_step (bcap := bcap) (lκ := e) hparent hquery hcheap hhard

/-- **`08:1314--1317`, back to `eq:selected-upper-budget`.**  "It follows that no
suffix protocol of cost at most `D_2 = B_cap + log_2 q_2` computes the selected
residual rectangle, contradicting `eq:selected-upper-budget`.  Hence the original
protocol `P` has cost at least `C`."

The banked `DenseBranchSelection.selectedResidual_cost_le` is
`eq:selected-upper-budget` itself, consumed **by pin**: this is its contrapositive,
which is exactly the `cost(P) > C - 1 = log_2 s + D_2` the opening shell's
`hnoProtocol` asks for.  General in the protocol, the row and both exponents. -/
theorem denseStageFour_residual_cost_lower {X Y Z : Type*} {P : Protocol X Y Z}
    {ls bcap lq₂ : ℕ} {x : X}
    (hpre : IsAlicePrefixAt P ls x)
    (hresidual : Dtwo bcap lq₂ < (aliceResidual x ls P).cost) :
    ls + Dtwo bcap lq₂ < P.cost := by
  rcases Nat.lt_or_ge (ls + Dtwo bcap lq₂) P.cost with h | h
  · exact h
  · exact absurd (selectedResidual_cost_le hpre h) (by omega)

/-- **The Completion at the banked-shell-licensed level.**

`DenseStageFourOpening.denseStageFour` is the banked statement shell of
`thm:dense-stage4` (`08:298--328`); its single named hypothesis `hnoProtocol` is "for
every retained member and every alleged protocol of cost at most `C - 1`,
contradiction".  This theorem supplies it from the Completion's accounting: what is
still a binder is `hclosure`, the statement that every alleged protocol has an Alice
prefix of the frozen length at some row whose residual exceeds `D_2` -- which is
precisely what the forced Alice node plus the two closure lemmas deliver, and which
this module does not construct (coverage limit 4).

`hCval` is the frozen `C = log_2 s + D_2 + 1` of `08:149--152`, the banked `cBlock`
reading, so `C - 1` is exact.  General. -/
theorem denseStageFourCompletion {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (ηR ηC : ℝ) (Cval ls bcap lq₂ : ℕ)
    (Admissible NoCert : Prop) (hAdm : Admissible) (hNo : NoCert)
    (hηR : 0 < ηR) (hηC : 0 < ηC) (hcard : 1 ≤ Fintype.card Rw)
    (hCval : Cval = ls + Dtwo bcap lq₂ + 1)
    (hclosure : Admissible → NoCert →
      ∀ RC ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC),
        ∀ P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool,
          Protocol.Computes P (subgame (interlaceFun Nmat 1) RC.1 RC.2) →
            ∃ x, IsAlicePrefixAt P ls x
              ∧ Dtwo bcap lq₂ < (aliceResidual x ls P).cost) :
    DenseStageFourConclusion Nmat ηR ηC Cval := by
  refine denseStageFour Nmat ηR ηC Cval Admissible NoCert hAdm hNo hηR hηC hcard
    (by omega) ?_
  intro hA hN RC hRC P hP
  obtain ⟨x, hpre, hres⟩ := hclosure hA hN RC hRC P hP
  have h := denseStageFour_residual_cost_lower hpre hres
  omega

/-! ## §5  `cor:exact-protected-stage4` (`08:1326--1339`)

"In the `NO` case, `comp N = comp A = comp B = C`."

"Take the full row and column sets in `thm:dense-stage4`.  This gives `comp N >= C`.
The labelled duplication and transposition preserve complexity, while the direct
protocol `eq:stage4-no-upper` gives `comp B <= C`.  Hence every inequality is an
equality." -/

/-- **`cor:exact-protected-stage4` (`08:1326--1339`), as a sandwich.**

`hchain` is the frozen `comp A = comp B` of `08:143` (the labelled duplication),
`hlower` is "Take the full row and column sets in `thm:dense-stage4`", and `hupper`
is `eq:stage4-no-upper` (`07:645`).  The transposition step `comp N = comp A` is the
banked `D_transposeN`, consumed by pin.  All three equalities follow.  General in both
matrices and in `C`. -/
theorem exactProtectedStageFour {Rw Cl Rb Cb : Type*} [Fintype Rw] [Fintype Cl]
    [Fintype Rb] [Fintype Cb] (Amat : Rw → Cl → Bool) (Bmat : Rb → Cb → Bool)
    {Cval : ℕ}
    (hchain : D Amat = D Bmat)
    (hlower : Cval ≤ D (transposeN Amat))
    (hupper : D Bmat ≤ Cval) :
    D (transposeN Amat) = Cval ∧ D Amat = Cval ∧ D Bmat = Cval := by
  have ht := D_transposeN Amat
  exact ⟨by omega, by omega, by omega⟩

/-- **`cor:exact-protected-stage4` with the duplication discharged by pin.**  The
frozen "The labelled duplication ... preserve[s] complexity" is the banked
`DenseStageFourOpening.D_protectedDup` at the block's protected carriers, so `hchain`
is not a hypothesis at the actual construction.  Only `hlower` (the full-carrier
member of `thm:dense-stage4`) and `hupper` (`eq:stage4-no-upper`) remain binders.
General in every carrier, inclusion and multiplicity with positive base
multiplicities. -/
theorem exactProtectedStageFour_at_protectedDup {Xr Tm Wv Wb Om Sg Dg : Type*}
    {u₀ uT uV uB w₀ wSg wD : ℕ} [Fintype Xr] [Fintype Tm] [Fintype Wv] [Fintype Wb]
    [Fintype Om] [Fintype Sg] [Fintype Dg]
    (Bmat : Xr → Om → Bool) (iT : Tm → Xr) (iV : Wv → Xr) (iB : Wb → Xr)
    (iSg : Sg → Om) (iD : Dg → Om) (hu : 0 < u₀) (hw : 0 < w₀) {Cval : ℕ}
    (hlower : Cval ≤ D (transposeN (protectedDup (u₀ := u₀) (uT := uT) (uV := uV)
      (uB := uB) (w₀ := w₀) (wSg := wSg) (wD := wD) Bmat iT iV iB iSg iD)))
    (hupper : D Bmat ≤ Cval) :
    D (transposeN (protectedDup (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB)
        (w₀ := w₀) (wSg := wSg) (wD := wD) Bmat iT iV iB iSg iD)) = Cval
      ∧ D (protectedDup (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) (w₀ := w₀)
          (wSg := wSg) (wD := wD) Bmat iT iV iB iSg iD) = Cval
      ∧ D Bmat = Cval :=
  exactProtectedStageFour _ Bmat
    (D_protectedDup Bmat iT iV iB iSg iD hu hw).2.2 hlower hupper

/-! ## §6  Non-vacuity, statement poles and consistency probes (LANE-GATE 3/4)

Every statement above is a conditional whose premise bundle a green build cannot
check.  Each is therefore inhabited at legal values, and each is probed against its
trivial reading.  No parameter schedule may be read out of any witness below. -/

/-- **Tier 2 -- `lem:dense-extension-closure` at a fully instantiated legal
instance.**

Every hypothesis of `denseExtensionClosure` is discharged at
`r = 6` (`q_2 = 64`), `k_2 = 4` (`t_2 = 16`), `rho = 2`, `rho' = 1` (so
`kappa = 32 >= t_2` and `r' = 2`), `d_v = 1`, `b_1 = 10`, `B_cap = 3`, `h_v = 24`,
`|C_1| = 16`, and the banked `denseSeparationGates_satisfiable` values
`(s, b_T, m_3, eps_2) = (4, 16, 2^20, 1/100)`.

The instance is **nondegenerate and tight in three places at once**: the frozen gate
`2 q_2 2^{-b_1} <= 1/8` is attained with equality (`128/1024 = 1/8`), the banked
forced-node bound `3 kappa <= 4 h_v` is attained with equality (`96 = 96`), and the
endpoint's conclusion `B_cap + log_2 kappa = 8` is attained by the child's cost.  So
no `False` follows from the bundle and the lemma is asserted at a real point.

It is **not** a schedule instance: it does not satisfy the full
`eq:stage2-structural-gates`, which forces `q_2 >= 6144`. -/
theorem denseExtensionClosure_legal_instance :
    (3 : ℕ) + (6 - 1) ≤ (fun _ : Unit => 8) () := by
  have hgate : 2 * (((2 : ℕ) ^ 6 : ℕ) : ℝ) * xSeed 10 ≤ 1 / 8 := by
    rw [xSeed_eq_inv_pow]; norm_num
  have hfloor : routingFloor (Fin 16) (2 ^ 6) 10 1
      ≤ (Finset.univ : Finset (Fin 16)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact routingFloor_le_card (Fin 16)
      (aliceEnteringSupport_le_one (r := 6) (b₁ := 10) (dv := 1) (by norm_num) hgate)
  exact denseExtensionClosure (Γ := Fin 16) (T := (Finset.univ : Finset (Fin 16)))
    (fun _ : Unit => 8) () (r := 6) (dv := 1) (b₁ := 10) (k₂ := 4) (ρ := 2) (ρ' := 1)
    (bcap := 3) (hv := 24) (s := 4) (bT := 16) (m₃ := 1048576) (ε₂ := 1 / 100)
    (dens := xDom 4 16 1048576 / 2)
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by decide) hfloor hgate denseSeparationGates_satisfiable (by norm_num)
    (le_refl _) (fun _ _ _ _ _ => by norm_num)

/-- **Statement pole for `lem:dense-extension-closure`: the inherited endpoint is
load-bearing.**

Every frozen datum of `denseExtensionClosure` holds at the legal instance above, yet
the conclusion is **false** at a child of cost `0`.  A proof that never used `hLocEx`
would therefore be wrong, and the lemma's content is exactly the discharge of
`thm:certified-localized-extension`'s three restriction clauses -- not an arithmetic
identity. -/
theorem denseExtensionClosure_pole_needs_endpoint :
    (1 : ℕ) ≤ 6 ∧ (2 : ℕ) ^ 6 = 2 ^ (2 + 4)
      ∧ stoppingCapacity 6 1 = 2 ^ (1 + 4)
      ∧ (1 : ℕ) ≤ 2 ∧ (4 : ℕ) ≤ 4
      ∧ 3 * stoppingCapacity 6 1 ≤ 4 * 24
      ∧ routingFloor (Fin 16) (2 ^ 6) 10 1 ≤ (Finset.univ : Finset (Fin 16)).card
      ∧ 2 * (((2 : ℕ) ^ 6 : ℕ) : ℝ) * xSeed 10 ≤ 1 / 8
      ∧ denseSeparationGates 4 16 1048576 (1 / 100)
      ∧ ¬ ((3 : ℕ) + (6 - 1) ≤ 0) := by
  have hgate : 2 * (((2 : ℕ) ^ 6 : ℕ) : ℝ) * xSeed 10 ≤ 1 / 8 := by
    rw [xSeed_eq_inv_pow]; norm_num
  have hfloor : routingFloor (Fin 16) (2 ^ 6) 10 1
      ≤ (Finset.univ : Finset (Fin 16)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact routingFloor_le_card (Fin 16)
      (aliceEnteringSupport_le_one (r := 6) (b₁ := 10) (dv := 1) (by norm_num) hgate)
  exact ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, by decide,
    hfloor, hgate, denseSeparationGates_satisfiable, by norm_num⟩

/-- **Tier 2 -- `lem:dense-small-closure` applied at capacity one with a live unsplit
witness (case 1 of `08:1268--1273`).**

The whole premise bundle is discharged at `r = d_v = 4` (so `kappa = 1`, `e = 0`),
`k_2 = 4`, `b_1 = 4`, `B_cap = 3`, `h_v = 1`, `z_v = 1`, `|C_1| = 8`, with the
unsplit-witness predicate `True` and its `B_cap + 1 = 4` certificate.  The banked
forced-node bounds are attained tightly (`3 * 1 <= 4 * 1` and `1 < 1 + 1`), the frozen
`eq:small-capacity-legal` chain `2 kappa = 2 <= t_2 = 16 <= 2^{b_1} = 16` holds, and
the conclusion is the frozen exceptional branch.

Case 1 is the branch that spends **no** inherited bracket bound, which is exactly why
it is the branch that can be inhabited without inhabiting `eq:small-two-copy` or
`eq:small-odd-copy` at a concrete matrix (coverage limit 2). -/
theorem denseSmallClosure_at_capacity_one :
    (2 * ((stoppingCapacity 4 4 : ℕ) : ℝ) * xSeed 4 ≤ 1
        ∧ 2 * stoppingCapacity 4 4 ≤ 2 ^ 4)
      ∧ ((True ∧ (0 : ℕ) = 0 ∧ (3 : ℕ) + 1 ≤ 4)
          ∨ (3 : ℕ) + 0 ≤ D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 2)
              (∅ : Finset (Fin 2 × Bool)) (∅ : Finset (Fin 2 → Bool)))
          ∨ (3 : ℕ) + 0 ≤ D (subgame
              (interlaceFun (fun (_ : Bool) (_ : Bool) => false)
                (stoppingCapacity 4 4 / 2 + 1))
              (∅ : Finset (Fin (stoppingCapacity 4 4 / 2 + 1) × Bool))
              (∅ : Finset (Fin (stoppingCapacity 4 4 / 2 + 1) → Bool)))) := by
  refine denseSmallClosure (Γ := Fin 8) (T := (Finset.univ : Finset (Fin 8)))
    (fun (_ : Bool) (_ : Bool) => false) True (∅, ∅) (∅, ∅)
    (r := 4) (dv := 4) (b₁ := 4) (e := 0) (k₂ := 4) (bcap := 3) (hv := 1) (zv := 1)
    (witCost := 4)
    (le_refl 4) (by decide) (by norm_num) (by norm_num) (by decide) (by decide) ?_
    (fun h => absurd trivial h) (fun _ => by norm_num)
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by decide))
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by decide))
  · rw [Finset.card_univ, Fintype.card_fin]
    refine routingFloor_le_card (Fin 8) ?_
    rw [aliceEnteringSupport (r := 4) (b₁ := 4) (dv := 4) (le_refl 4), xSeed_eq_inv_pow]
    norm_num [stoppingCapacity]

/-- **Tier 3 -- the four-case dispatch, applied at all four frozen capacities.**

The arithmetic core of `08:1268--1292` is exercised at `kappa = 1` (case 2, no
witness), `kappa = 2` (case 3), `kappa = 4` and `kappa = 8` (case 4), together with
the frozen independence-width check of `08:1293--1295` at `t_2 = 16`.  Each row is the
*conclusion* the frozen case draws, so a dispatch that silently dropped a case would
fail here.  This is a probe of the arithmetic at small values and is **not** a legal
instance of the block's regime. -/
theorem denseSmallClosure_dispatch_readout :
    (2 : ℕ) ≤ 2 ∧ (2 : ℕ) ≤ 2 ∧ (4 : ℕ) / 2 + 1 ≤ 3 ∧ (8 : ℕ) / 2 + 1 ≤ 6
      ∧ ((2 : ℕ) ≤ 16 ∧ ((4 : ℕ) ≤ 4 → (4 : ℕ) / 2 + 1 ≤ 16))
      ∧ ((2 : ℕ) ≤ 16 ∧ ((4 : ℕ) ≤ 8 → (8 : ℕ) / 2 + 1 ≤ 16)) := by
  refine ⟨smallCase_two_of_capacity_one (h := 2) (z := 0) rfl (by norm_num),
    smallCase_two_of_capacity_two (h := 2) (by norm_num),
    smallCase_odd_select (κ := 4) (h := 3) (by norm_num) (by norm_num),
    smallCase_odd_select (κ := 8) (h := 6) (by norm_num) (by norm_num),
    smallCase_selected_le_width (κ := 4) (t₂ := 16) (by norm_num) (by norm_num),
    smallCase_selected_le_width (κ := 8) (t₂ := 16) (by norm_num) (by norm_num)⟩

/-- **Hypothesis consistency for `lem:dense-small-closure`, at the numeric shape.**

The lemma conjoins the two inherited consequences of the Stage-1 robust seed with the
banked forced-node bounds.  They are the two consequences `08:1254--1264` names side
by side for the two selection widths -- not two cases of a promise split -- so
conjoining them is legitimate; and their numeric shape is simultaneously satisfiable
with every conclusion the dispatch draws, at every `B_cap` above the frozen floor
`B_cap >= 3` (`07:501`) and at every capacity exponent.  Hence no contradiction
follows from the bundle.

This is the same shape of consistency probe the banked
`DenseRoutingThresholds.denseLocalCertificates_hypotheses_consistent` records, and it
carries the same coverage limit: neither inherited consequence is inhabited here at a
concrete matrix (`smallClosure_pole_needs_inherited_bounds` records why the constant
matrices cannot serve). -/
theorem denseSmallClosure_hypotheses_consistent (bcap e : ℕ) (h3 : 3 ≤ bcap) :
    ∃ dtwo dodd dwit hv zv : ℕ,
      3 ≤ bcap ∧ bcap + 1 ≤ dtwo ∧ bcap + e ≤ dodd ∧ bcap + 1 ≤ dwit
        ∧ 3 * 2 ^ e ≤ 4 * hv ∧ 2 ^ e < hv + zv
        ∧ (2 ≤ hv) ∧ (e ≤ 1 → bcap + e ≤ dtwo) := by
  have hone : (1 : ℕ) ≤ 2 ^ e := Nat.one_le_pow _ _ (by norm_num)
  exact ⟨bcap + 1, bcap + e, bcap + 1, 2 ^ e + 1, 1, h3, by omega, by omega, by omega,
    by omega, by omega, by omega, fun _ => by omega⟩


/-- **Statement pole for the inherited bracket bounds.**

`eq:small-two-copy` is genuine content.  At the legal constant seed the two-copy
bracket family at row density `2 * 2^{-b_1} <= 1` and column density `9/25` is
nonempty, and every member's subgame is constant, hence of complexity `0`; so the
family bound `comp<M_1^T, 2, 2x, 9/25> >= B_cap + 1` fails at every positive `B_cap`.
A proof of `denseSmallClosure` that never used `htwo` would be wrong.

This also records coverage limit 2 honestly: the module does **not** inhabit `htwo` or
`hodd` at a concrete matrix, and this pole is the reason -- the only matrices whose
bracket complexity is computable here are the constant ones, which refute them. -/
theorem smallClosure_pole_needs_inherited_bounds {b₁ : ℕ} (hb : 2 * xSeed b₁ ≤ 1) :
    ∃ RC : Finset (Fin 2 × Bool) × Finset (Fin 2 → Bool),
      RC ∈ bracketGE Bool Bool 2 (2 * xSeed b₁) (9 / 25) ∧
      D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 2) RC.1 RC.2) = 0 ∧
      ¬ (1 ≤ D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 2)
            RC.1 RC.2)) := by
  obtain ⟨RC, hRC⟩ :=
    bracketGE.nonempty (X := Bool) (Y := Bool) 2 (2 * xSeed b₁) (9 / 25)
      hb (by norm_num) (by simp)
  have hconst :
      subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 2) RC.1 RC.2
        = fun (_ : {x // x ∈ RC.1}) (_ : {y // y ∈ RC.2}) => false := rfl
  have hzero : D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 2)
      RC.1 RC.2) = 0 := by
    rw [hconst]; exact PublicRecords.D_const false
  exact ⟨RC, hRC, hzero, by rw [hzero]; norm_num⟩

/-- **Statement pole for the Completion.**  The child bound is what closes the case.
Dropping it leaves a perfectly consistent budget assignment: a parent budget of
`B_cap + log_2 kappa`, a child budget one bit below, and a child the alleged protocol
computes inside that budget.  So `denseStageFour_completion_step` is not an arithmetic
tautology about the budgets alone -- the closure lemmas' conclusion is load-bearing. -/
theorem completion_pole_needs_the_child_bound (bcap lκ : ℕ) (hl : 1 ≤ lκ) :
    (bcap + lκ ≤ bcap + lκ) ∧ ((bcap + lκ - 1) + 1 ≤ bcap + lκ)
      ∧ (bcap + lκ - 1 ≤ bcap + lκ - 1)
      ∧ ¬ (bcap + lκ ≤ bcap + lκ - 1) := by
  refine ⟨le_refl _, by omega, le_refl _, by omega⟩

/-- **Statement pole for `cor:exact-protected-stage4`.**  `eq:stage4-no-upper` is
load-bearing: without the direct `NO` protocol's upper bound the sandwich does not
close, and the corollary's equality would be false.  At the frozen shape a lower bound
alone permits `comp B` strictly above `C`. -/
theorem exactProtectedStageFour_pole_needs_upper (Cval : ℕ) :
    ∃ dA dB : ℕ, dA = dB ∧ Cval ≤ dA ∧ ¬ (dA = Cval) := by
  exact ⟨Cval + 1, Cval + 1, rfl, by omega, by omega⟩

/-! ## §7  Candidate B (rejected): the threshold as a record about its selection

Recorded as race evidence with the disposition of coverage limit 8. -/

/-- **Candidate B (rejected).**  The frozen threshold of `08:1212--1216` packaged with
the object it is a threshold for: the selected coordinate set, the surviving support,
the residual capacity, the suffix depth and the trim inequality.

Rejected: `floor` restates a telescope the other fields force, the record forgets that
`kappa` is `2^{r - d_v}`, and the record-form trim is a projection of Candidate A. -/
structure TrimmedSelection (Γ : Type*) [Fintype Γ] where
  /-- The surviving quotient support at the node. -/
  support : Finset Γ
  /-- The alleged residual capacity `kappa_v`. -/
  cap : ℕ
  /-- The frozen Stage-1 robustness depth `b_1`. -/
  depth : ℕ
  /-- The alleged trim target -- the redundant field. -/
  floor : ℕ
  /-- The alleged trim target really is the frozen ceiling. -/
  floor_eq : floor = ⌈(cap : ℝ) * xSeed depth * (Fintype.card Γ : ℝ)⌉₊
  /-- The trim is legal at the node. -/
  trim : floor ≤ support.card

/-- **Candidate B battery 1 (inhabitation with the hardest field).**  The record is
inhabited at a nondegenerate point: a nonempty support, positive capacity, and the
trim inequality actually satisfied rather than vacuous. -/
theorem trimmedSelection_nonempty : Nonempty (TrimmedSelection (Fin 8)) := by
  refine ⟨⟨Finset.univ, 1, 4, capacityFloor (Fin 8) 1 4, rfl, ?_⟩⟩
  rw [Finset.card_univ, Fintype.card_fin]
  unfold capacityFloor
  rw [Fintype.card_fin, xSeed_eq_inv_pow]
  refine Nat.ceil_le.2 ?_
  norm_num

/-- **Candidate B battery 2 (the stored floor is derived).**  The `floor` field is
forced by `cap`, `depth` and the carrier, so it restates a telescope: it is the banked
`capacityFloor` on the nose.  A field that can only ever hold one value is not data. -/
theorem trimmedSelection_floor_is_derived {Γ : Type*} [Fintype Γ]
    (t : TrimmedSelection Γ) : t.floor = capacityFloor Γ t.cap t.depth :=
  t.floor_eq

/-- **Candidate B battery 3 (the record forgets the frozen capacity law).**  Two
inhabitants with identical support and depth but different recorded capacity: the
record does not know that the frozen `kappa_v` is `2^{r - d_v}`, determined by the
node's suffix depth (`08:1142`).  The frozen datum knows this; the record does not. -/
theorem trimmedSelection_capacity_floats :
    ∃ t t' : TrimmedSelection (Fin 8),
      t.support = t'.support ∧ t.depth = t'.depth ∧ t.cap ≠ t'.cap := by
  have h1 : capacityFloor (Fin 8) 1 4 ≤ 8 := by
    unfold capacityFloor
    rw [Fintype.card_fin, xSeed_eq_inv_pow]
    refine Nat.ceil_le.2 ?_
    norm_num
  have h2 : capacityFloor (Fin 8) 2 4 ≤ 8 := by
    unfold capacityFloor
    rw [Fintype.card_fin, xSeed_eq_inv_pow]
    refine Nat.ceil_le.2 ?_
    norm_num
  refine ⟨⟨Finset.univ, 1, 4, capacityFloor (Fin 8) 1 4, rfl, ?_⟩,
    ⟨Finset.univ, 2, 4, capacityFloor (Fin 8) 2 4, rfl, ?_⟩, rfl, rfl, by norm_num⟩
  · rw [Finset.card_univ, Fintype.card_fin]; exact h1
  · rw [Finset.card_univ, Fintype.card_fin]; exact h2

/-- **Candidate B battery 4 (the record adds no mathematics).**  The record-form trim
is a projection of Candidate A: the landed `trim_to_capacity_floor` produces the
record's own inequality, so the record is a strictly lossier spelling of the same
statement. -/
theorem trimmedSelection_is_a_repackaging {Γ : Type*} [Fintype Γ] {r b₁ dv : ℕ}
    {T : Finset Γ} (hinv : routingFloor Γ (2 ^ r) b₁ dv ≤ T.card) (hd : dv ≤ r) :
    ∃ t : TrimmedSelection Γ,
      t.support = T ∧ t.cap = stoppingCapacity r dv ∧ t.depth = b₁ :=
  ⟨⟨T, stoppingCapacity r dv, b₁, capacityFloor Γ (stoppingCapacity r dv) b₁, rfl,
      trim_to_capacity_floor hinv hd⟩, rfl, rfl, rfl⟩

end EthInapproximability.ParameterizedNP.DenseAliceClosure
