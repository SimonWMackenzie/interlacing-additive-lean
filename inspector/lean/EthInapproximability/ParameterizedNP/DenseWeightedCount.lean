import EthInapproximability.ParameterizedNP.DenseRoutingInvariant

/-!
# Parameterized NP route: the sixth block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 946--1012** --
  `sec:dense-weighted-count`, the weighted stopping count, with `lem:dense-no-leaf`
  and its frozen proof.  The anchors traced here, in the order the block prints
  them:
  * `08:949--951`, the frozen width and the positive token: "Write `q_2 = 2^r`.
    A *positive token* means one unit-weight component: either an ordinary token
    or the bonus component of a witness object.  Follow every positive token
    below the root of `P_*`";
  * `08:952--953`, the stopping rule: "Stop it when its Stage-2 coordinate is
    isolated, immediately before the first Alice query on its path, or
    provisionally at a protocol leaf";
  * `lem:dense-no-leaf` (label 956, statement 955--959): "Every positive token
    stops at coordinate isolation or before its first Alice query, and it does so
    at suffix depth at most `r`";
  * 962--965, the support readout inside the proof: "Before the first Alice
    query, the template row set is unchanged.  At depth `d <= r`,
    `lem:dense-routing` gives ordinary support at least
    `lambda_d >= lambda_r = 2^{1-b_1}`";
  * 966--972, the trimming and the local certificate: "Trim this support to
    density `2^{-b_1}`.  Relaxed-to-classical transfer and
    `x_dom/(1+eps_2) >= 3/5` give a one-copy restriction of `M_1^T` with
    complexity at least `B_cap`.  In particular the node is not monochromatic";
  * 974--978, the budget clash one level deeper: "Nor can a positive token first
    reach depth `r+1`.  Its support there is still at least `2^{-b_1}`, so the
    same one-copy lower bound applies, while the total suffix budget
    `B_cap + r` leaves at most `B_cap - 1` further bits.  This contradiction rules
    out both a premature leaf and first stopping depth greater than `r`";
  * 981--989, the frontier and its capacity weight: "The stopping nodes form a
    prefix-free frontier.  An Alice stopping node stops every token that reaches
    it.  At a coordinate-isolation node, every other coordinate fibre is empty.
    If both descriptions hold at the same protocol node, classify it as a
    coordinate-isolation node; the two frontier classes are therefore disjoint and
    exhaustive.  For a frontier node `v` at suffix depth `d_v`, put
    `kappa_v = 2^{r - d_v}`";
  * 990--992, the two masses: "Let `h_v` be the number of ordinary components at
    `v`, counting the ordinary component of an unsplit witness, and let `z_v` be
    the number of unsplit bonus components.  Thus `0 <= z_v <= h_v`";
  * 1004--1012, `eq:isolation-capacity`: "By the coordinatewise uniqueness in
    `lem:dense-routing`, an isolation node contains at most one routed object.  It
    therefore contains either one ordinary token, which requires `kappa_v >= 1`,
    or one unsplit witness, whose `B_cap + 1` certificate requires
    `kappa_v >= 2`.  Therefore `h_v + z_v <= kappa_v` at every isolation node";
  * `eq:selected-upper-budget` (`08:768--771`), the residual budget
    `cost(P_*) <= D_2 = B_cap + log_2 q_2` that the depth clause spends, consumed
    through the banked `DenseBranchSelection.Dtwo`.
* **Deliberately NOT claimed (the next block's territory).**  `eq:frontier-conservation`
  (`08:995--1002`) has **no** declaration here: neither conservation equality, nor
  the Kraft bound `sum_v kappa_v <= q_2`, nor the split count `S` appears in any
  statement below, and no predicate bundling them is defined.
  `lem:abstract-weighted-frontier` (`08:1014--1089`) is the banked
  `EthInapproximability.ParameterizedNP.weightedFrontier` pilot and is neither
  restated nor applied, and `lem:dense-weighted-frontier` (`08:1091--1134`), the
  closure lemmas of `sec:dense-alice-closure` (`08:1136--1324`) and
  `cor:exact-protected-stage4` have no declaration here.  Where a later block
  needs the counting facts of this block it must cite the named results below;
  where it needs conservation or Kraft, those remain its own obligations.
* **Predecessor anchors (the handoffs consumed by pin):**
  * `08:878--944` through the banked
    `EthInapproximability.ParameterizedNP.DenseRoutingInvariant`, which supplies
    `routingFloor` (the frozen integral floor `L_d = ceil(lambda_d |C_1|)`) with
    `routingFloor_le`, `routingFloor_antitone`, and `supportDensity`.  The frozen
    sentence `08:963--964` -- "`lem:dense-routing` gives ordinary support at least
    `lambda_d`" -- enters every statement below **only** as the banked
    `routingFloor Gamma (2^r) b_1 d <= (quotientSupport rep S alpha).card`, never
    re-proved;
  * `08:811--876` through the banked `DenseRoutingThresholds`, which supplies
    `lambdaAt` with `lambdaAt_succ`, `lambdaAt_antitone` and
    `lambdaAt_at_depth_log` (the frozen `lambda_r = 2^{1-b_1}` at `q_2 = 2^r`),
    and `xSeed_eq_inv_pow`;
  * `08:766--789` through the banked `DenseBranchSelection`, which supplies
    `Dtwo` (the frozen `D_2 = B_cap + log_2 q_2`) and `quotientSupport`;
  * `08:427--428` through the banked `DenseSynchronisation.IsANode`, reused
    unchanged as "the node reached is an Alice node";
  * `StageOneInterlace.xSeed`, the frozen seed density `2^{-b_1}`.
  **None of those handoffs is restated here.**
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design and appears in
  no hypothesis below.  The three deep inputs of the frozen proof are named
  hypotheses at the exact gates the frozen text states them:
  * the one-copy certificate of `08:966--971` -- "relaxed-to-classical transfer and
    `x_dom/(1+eps_2) >= 3/5` give a one-copy restriction of `M_1^T` with complexity
    at least `B_cap`" -- is `honeCopy`, **gated on the trimmed support** reaching
    the frozen seed floor `ceil(2^{-b_1}|C_1|)`, so nothing is assumed at nodes
    where the frozen hypothesis fails;
  * the protocol-semantic reading of a node -- its residual subtree solves the
    node's own game -- is `hresidual : D (gnode) <= (descend P p).cost`, the only
    form in which the frozen budget sentence `08:975--976` can be spent;
  * the coordinatewise uniqueness clause `08:1004--1005` is `huniq : h <= 1`, a
    **named hypothesis**, because the banked `DenseRoutingInvariant` records (its
    coverage limit 3) that it did not prove the routing preserves the
    one-object-per-coordinate representation across a query; nothing here upgrades
    that bar.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency graph.
* **New vendored-gap work.**  The suffix-depth walk.  The vendored protocol type
  exposes only the Alice walk (`DenseSynchronisation.aliceStep`,
  `aliceResidual`), which stops at a Bob node and is therefore useless for a
  token routed **through** Bob queries.  `descendStep` / `descend` / `IsQueryPath`
  / `IsBobPath` are the two-sided walk the frozen "suffix depth" needs, and
  `cost_descend_add_length_le` is the budget accounting `08:975--976` spends.  No
  vendored file is touched.
* Proof status: **new** for the suffix-depth walk, the stopping device, the
  no-leaf lemma, the capacity weight, the frontier classification and the
  isolation-capacity inequality; **inherited by pin** for the routing floor, the
  thresholds, the seed density and the residual budget.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no unproved
  placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, the proof outline of
`thm:paper-protected-stage4`, **lines 259--265**:

* "the weighted stopping count records coordinate isolation, the first Alice
  query, and premature leaves" (259--261) is the stopping device of SS4
  (`StopEvent`, `TokenKind`, `StoppedToken`) together with `denseNoLeaf`;
* "Classify each stopping node as either an Alice node or a coordinate-isolation
  node, giving priority to isolation if both descriptions apply" (261--263) is
  `frontierClass` with `frontierClass_isolation_of_both`, `frontier_disjoint` and
  `frontier_union`;
* "If `kappa_v` is its residual copy capacity and `h_v,z_v` are its routed
  template and witness masses, isolation gives `h_v+z_v <= kappa_v`" (263--265) is
  `stoppingCapacity` with `isolationNode_capacity`.

Each of the three is claimed **once**, and none was claimed by an earlier tranche:
the banked `DenseRoutingInvariant` records that reader line 259 up to "Quotient-support
routing follows every Bob query" was assigned to `DenseBranchSelection` in tranche
`cc-t2k`, and that "the remainder of line 259 onwards" -- exactly the three clauses
above -- was left to this block.  The reader sentences after line 265
("Conservation gives ...", "Thus some Alice node satisfies ...") are the next
block's and are **not** claimed here.  No reader prose is cited as a statement:
each of the three clauses above is an assertion, not a description of method.

## Candidate encodings of the stopped positive token (`k = 2`, raced)

The novel object of this tranche is the positive token together with the frozen
stopping rule of `08:949--953`.

**Candidate A (landed, SS4).**  Make the novelty the *stop record*: a
`StoppedToken Pstar Coord` carries the token's Stage-2 coordinate, its kind
(`ordinary` or `bonus`, the two frozen unit-weight components), the route it
followed below the root of `P_*` as a `List Bool`, and which of the three frozen
events stopped it -- plus exactly the **well-formedness laws of the frozen rule**:
every node strictly before the stopping node is a Bob query (`route_bob`, the
frozen "before the first Alice query on its path", which is also why `08:962` may
say the template row set is unchanged), the provisional stop happens at a protocol
leaf (`atLeaf_at_leaf`), and the Alice stop happens at an Alice node
(`beforeAlice_at_alice`, the banked `IsANode`).  The suffix depth is the
**derived** `route.length`, not a field.  Nothing is stored that the frozen lemma
concludes: neither `event <> atLeaf` nor `route.length <= r` is a field, and
`stoppedToken_leaf_stop_is_inhabited` exhibits a legal token with
`event = atLeaf`, so the no-leaf lemma is not available by projection.  4 aux
lemmas proved on the record itself (`A7`), and it is inhabited at a concrete
protocol three times over (SS10).

**Candidate B (rejected, SS8).**  Take the stopped token as a record carrying its
own guarantee: a depth, an event, and the two fields `event <> atLeaf` and
`depth <= r`.  3 aux lemmas proved, and it loses decisively on two counts.
First, it puts the frozen *conclusion* of `lem:dense-no-leaf` (`08:957--959`) into
constructor data, which the mechanical contract's no-conclusion-in-constructor-data
rule forbids outright -- and it is the exact shape that makes the no-leaf theorem a
projection.  Second, it is unfaithful even as data: `countedToken_needs_no_protocol`
exhibits an inhabitant at a protocol in which its route walks off a leaf, so the
record describes a token stopped in no protocol at all.  The race is decided on
faithfulness, not length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the frozen capacity weight `kappa_v = 2^{r-d_v}` (`08:985--989`), general (7):
  `stoppingCapacity_eq`, `one_le_stoppingCapacity`, `stoppingCapacity_at_root`,
  `stoppingCapacity_at_depth`, `stoppingCapacity_le_width`,
  `stoppingCapacity_antitone`, `two_mul_stoppingCapacity_succ`.
* `A2` the threshold readouts at the frozen width `q_2 = 2^r` (`08:963--965`,
  `08:975`), general (5): `lambdaAt_at_depth_succ_log`, `xSeed_eq_lambdaAt_succ`,
  `xSeed_le_lambdaAt_of_le_succ`, `two_mul_xSeed_le_lambdaAt_of_le`,
  `two_le_stoppingCapacity_of_lt`.
* `A3` the trimming to seed density (`08:966`), general (3): `seedFloor_le`,
  `seedFloor_le_routingFloor`, `trim_to_seed_floor`.
* `A4` the suffix-depth walk, general (11): `descend_nil`, `descend_cons`,
  `descend_leaf`, `descend_append`, `cost_descendStep_le`, `cost_descend_le`,
  `not_isQueryNode_leaf`, `isQueryNode_of_isBobNode`, `isQueryPath_of_isBobPath`,
  `isQueryPath_take`, `cost_descendStep_succ_le`.
* `A5` the budget accounting (`08:975--976`), general (2):
  `cost_descend_add_length_le`, `length_le_cost_of_isQueryPath`.
* `A6` the node readouts (`08:971--972`), general (3): `one_le_D_of_ne`,
  `node_not_monochromatic`, `node_not_leaf`.
* `A7` the stop record (`08:946--953`), general (4): `StoppedToken.depth_eq`,
  `StoppedToken.event_cases`, `StoppedToken.route_isQueryPath`,
  `StoppedToken.take_isQueryPath`.
* `A8` the frozen lemma (4): `oneCopy_hard_at_node`, `denseNoLeaf_depth_le`,
  `denseNoLeaf_event_ne_atLeaf`, `denseNoLeaf`.
* `A9` the frontier (`08:981--992`, `08:1004--1012`), general (8):
  `frontierClass_isolation_iff`, `frontierClass_alice_iff`,
  `frontierClass_isolation_of_both`, `frontier_disjoint`, `frontier_union`,
  `prefixFreeFrontier_injective`, `isolationNode_capacity`,
  `isolationNode_capacity_at_depth`.
* `A10` the probe protocol and the probe node game the readouts of SS10 are built
  from (8): `probeProtocol_cost`, `probeProtocol_descend_true`,
  `probeProtocol_descend_false`, `probeProtocol_bobPath_true`,
  `probeProtocol_bobPath_false`, `probeGame_D_le_one`, `probeGame_one_le_D`,
  `probeGame_D_eq_one`.
* Candidate B's own battery (3): `countedToken_nonempty`,
  `countedToken_depth_le`, `countedToken_needs_no_protocol`.

That is **55 battery entries proved plus 3 for the rejected candidate**, with `0`
unproved, alongside **three statement poles** (`seedFloor_pole_beyond_succ_width`,
`cost_descend_pole_needs_query_path`, `stoppedToken_leaf_stop_is_inhabited`) and
**five non-vacuity / consistency readouts** -- one for every definition group, one
for the headline's premise bundle, and one applying the headline at that bundle.
The module has **87** source declarations in all: 21 definitions
(`stoppingCapacity`, `seedFloor`, `descendStep`, `descend`, `IsQueryNode`,
`IsBobNode`, `IsQueryPath`, `IsBobPath`, `TokenKind`, `StopEvent`, `StoppedToken`,
`StoppedToken.depth`, `FrontierClass`, `frontierClass`, `isolationNodes`,
`aliceNodes`, `PrefixFreeFrontier`, `probeProtocol`, `probeToken`, `probeGame`,
`CountedToken`) and 66 proved results (55 battery entries, 3 poles, 5 readouts,
3 for the rejected candidate):

* `stoppingCapacity_nondegenerate`, the capacity weight inhabited **symbolically in
  `r`**: for every `r` and every `d <= r` it is a positive power of two that halves
  with depth, equals `q_2 = 2^r` at the root and `1` at depth `r`, so nothing is
  evaluated and the frozen widths `q_2 >= 6144` are reached;
* `seedFloor_nondegenerate`, the trimming layer inhabited at a
  **routing-slack-legal** parameter pair -- legality is `RoutingSlack (2^1) 5`, the
  frozen `eq:routing-slack` (`08:805--810`) itself, proved **on the face of the
  statement** as its first conjunct, so the probe is legal for the frozen routing
  gate and not merely by `lambda_0 <= 1`.  It does **not** satisfy the full
  `eq:stage2-structural-gates` (`06:832--847`), which forces
  `q_2 >= 64 s q_1 / zeta >= 6144`; the probe does not need it, because
  `seedFloor_le_routingFloor` is general in `r`, `b_1` and `d` and takes no schedule
  hypothesis -- where the seed floor is a **strictly** smaller
  integer than the routing floor at every depth `d <= r`, so the trimming step is a
  real trim rather than an identity, and where the frozen stopping depth `d = r + 1`
  is exhibited as the exact depth at which the two floors **coincide**;
* `stoppedToken_nondegenerate`, the stop record inhabited **twice** over one
  protocol with different kinds and different events at the same route, so
  `StoppedToken` is not a subsingleton determined by `(Pstar, coord, route)` and the
  frozen three-way stopping rule has content;
* `denseNoLeaf_at_probe`, the headline **applied** at that witness, so the frozen
  conclusion is produced by the lemma itself at a real point rather than only in the
  abstract, and no `False` follows from the bundle;
* `denseNoLeaf_hypotheses_consistent`, the **joint** readout: the headline's entire
  premise bundle inhabited at legal values (`r = 1`, `B_cap = 1`,
  `cost(P_*) = 2 = D_2`, a token stopping at suffix depth `1 = r` before a genuine
  Alice query) at which **both** gated hypotheses that can fire do fire -- the node
  game has `D = 1 = B_cap` and the node's residual subtree has cost exactly `1`, so
  the budget and the certificate are simultaneously tight -- and the frozen
  conclusion is obtained with `route.length = r`, not with room to spare.  Without
  it the lemma could be quantified over a bundle its own premises force empty while
  the module compiled green.

## Honest scope and recorded coverage limits

1. **The two gates of the frozen proof are kept apart, and neither is widened.**
   The local certificate is stated by the paper "at depth `d <= r`" and the budget
   clash "at depth `r+1`"; `denseNoLeaf` therefore takes its four deep inputs as
   **two gated pairs**, `route.length <= r` for the stopping node and
   `r + 1 <= route.length` for the length-`(r+1)` prefix.  Assuming the one-copy
   certificate at the stopping node **ungated** would be strictly stronger than the
   paper: past depth `r+1` the routing threshold `lambda_d` falls below the seed
   density `2^{-b_1}` and the trimming step is illegal, which
   `seedFloor_pole_beyond_succ_width` exhibits at a carrier whose parameter pair
   carries `RoutingSlack (2^1) 5` -- the frozen `eq:routing-slack` (`08:805--810`)
   -- on the face of its own statement, so the pole is not an artefact of a pair
   violating `eq:routing-slack`.  The
   two gates are mutually exclusive, so the bundle never conjoins two cases of one
   construction.
2. **No protocol is constructed, and no protocol is evaluated.**  `descend` reads
   a given tree; `IsQueryPath` and `IsBobPath` are properties of a given tree; the
   frozen `cost(P_*) <= D_2` is the banked `Dtwo` bound and enters as the binder
   `hbudget`.  Nothing here builds `P_*`, restricts a rectangle, or asserts that
   the residual protocol below the selected branch has any particular shape.
3. **"The node is not monochromatic" is proved, and the link to the node's game is
   named.**  `node_not_monochromatic` proves the frozen sentence `08:972` outright:
   a game of positive complexity is computed by no leaf protocol.  That the node's
   *residual subtree* solves the node's *own* game -- the protocol semantics the
   frozen proof uses without naming -- is the hypothesis `hresidual`, never an
   axiom and never derived from a rectangle apparatus this block does not build.
4. **The isolation stop has no structure field.**  `08:983--984` ("At a
   coordinate-isolation node, every other coordinate fibre is empty") is a property
   of the routed family at the node, and the banked `DenseRoutingInvariant`
   (coverage limit 3) did not prove that the routing preserves that family across a
   query.  So the isolation predicate is carried **abstractly** in SS7
   (`frontierClass` over an arbitrary decidable `iso`), and the uniqueness
   consequence `08:1004--1005` is the named hypothesis `huniq` of
   `isolationNode_capacity`.  A later tranche may not cite this module as having
   supplied either.
5. **`eq:frontier-conservation` is untouched, and Kraft's inequality is not
   proved.**  `PrefixFreeFrontier` records the frozen sentence `08:981` as a
   property of a family of routes and proves only that it forces distinct routes;
   the counting consequence `sum_v kappa_v <= q_2` (`08:1000`) is **not** proved
   here and must not be cited from here.
6. **`b_1`, `r`, `B_cap` and the depth are binders, not values.**  `stoppingCapacity`
   and `seedFloor` take them as explicit naturals and the carrier as an explicit
   type; no parameter schedule may be read out of any witness below.  The
   consistency readouts and the three poles are separating probes at deliberately
   small carriers and are **not** schedule instances.
7. **Candidate B is race evidence with a recorded disposition.**  `CountedToken` is
   consumed by nothing and may not be used to re-encode the stopped token of
   `08:946--959` without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseWeightedCount

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseBranchSelection
open EthInapproximability.ParameterizedNP.DenseRoutingThresholds
open EthInapproximability.ParameterizedNP.DenseRoutingInvariant

/-! ## §1  The frozen width and the residual capacity `kappa_v` (`08:949`, `08:985--989`)

"Write `q_2 = 2^r`."  "For a frontier node `v` at suffix depth `d_v`, put
`kappa_v = 2^{r - d_v}`."  The frozen `r` is `log_2 q_2`, so the width itself is the
capacity of the root and every frontier node's capacity is what remains of it. -/

/-- The residual copy capacity `kappa_v = 2^{r - d_v}` of a frontier node at suffix
depth `d_v` (`08:986--989`).  The subtraction is the frozen one: the block applies
it only at depths `d_v <= r`, which `lem:dense-no-leaf` is what supplies. -/
def stoppingCapacity (r d : ℕ) : ℕ := 2 ^ (r - d)

/-- **Aux 1.**  The frozen definition, unfolded.  General. -/
@[simp] theorem stoppingCapacity_eq (r d : ℕ) : stoppingCapacity r d = 2 ^ (r - d) := rfl

/-- **Aux 2 (`08:1115`, "`d_v <= r` gives `1 <= kappa_v`").**  Every capacity is at
least one.  General. -/
theorem one_le_stoppingCapacity (r d : ℕ) : 1 ≤ stoppingCapacity r d :=
  Nat.one_le_two_pow

/-- **Aux 3.**  At the root the capacity is the frozen width `q_2 = 2^r`.
General. -/
theorem stoppingCapacity_at_root (r : ℕ) : stoppingCapacity r 0 = 2 ^ r := by
  simp [stoppingCapacity]

/-- **Aux 4.**  At the deepest legal suffix depth the capacity is exhausted.
General. -/
theorem stoppingCapacity_at_depth (r : ℕ) : stoppingCapacity r r = 1 := by
  simp [stoppingCapacity]

/-- **Aux 5.**  No capacity exceeds the frozen width.  General. -/
theorem stoppingCapacity_le_width (r d : ℕ) : stoppingCapacity r d ≤ 2 ^ r :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le r d)

/-- **Aux 6.**  Capacity decreases with suffix depth.  General. -/
theorem stoppingCapacity_antitone (r : ℕ) {d d' : ℕ} (h : d ≤ d') :
    stoppingCapacity r d' ≤ stoppingCapacity r d :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left h r)

/-- **Aux 7 (the halving step).**  Descending one level halves the residual
capacity, which is the arithmetic behind `kappa_v = 2^{r - d_v}`.  General below the
frozen depth. -/
theorem two_mul_stoppingCapacity_succ {r d : ℕ} (h : d < r) :
    2 * stoppingCapacity r (d + 1) = stoppingCapacity r d := by
  have hsub : r - d = (r - (d + 1)) + 1 := by omega
  simp only [stoppingCapacity, hsub, pow_succ]
  ring

/-! ## §2  The threshold readouts at the frozen width (`08:963--965`, `08:975`)

"At depth `d <= r`, `lem:dense-routing` gives ordinary support at least
`lambda_d >= lambda_r = 2^{1-b_1}`"; and at depth `r+1` "its support there is still
at least `2^{-b_1}`".  Both are arithmetic of the banked `lambdaAt` at `q_2 = 2^r`. -/

/-- **Aux 8 (`08:975`).**  One level below the frozen depth the threshold is exactly
the seed density: `lambda_{r+1} = 2^{-b_1}`.  General in `r` and `b_1`. -/
theorem lambdaAt_at_depth_succ_log (r b₁ : ℕ) :
    lambdaAt (2 ^ r) b₁ (r + 1) = 1 / 2 ^ b₁ := by
  rw [lambdaAt_succ, lambdaAt_at_depth_log]
  ring

/-- **Aux 9.**  The banked seed density `x_seed = 2^{-b_1}` is the threshold at depth
`r+1`.  General. -/
theorem xSeed_eq_lambdaAt_succ (r b₁ : ℕ) :
    xSeed b₁ = lambdaAt (2 ^ r) b₁ (r + 1) := by
  rw [xSeed_eq_inv_pow, lambdaAt_at_depth_succ_log]

/-- **`08:975`, the support still available at depth `r+1`.**  For every suffix depth
`d <= r + 1` the routing threshold is at least the seed density `2^{-b_1}`, so the
trimming of `08:966` is legal there.  General.

Past `r + 1` this fails, which is why the frozen proof stops one level below the
width: `seedFloor_pole_beyond_succ_width` exhibits the failure at a concrete
carrier. -/
theorem xSeed_le_lambdaAt_of_le_succ {r b₁ d : ℕ} (hd : d ≤ r + 1) :
    xSeed b₁ ≤ lambdaAt (2 ^ r) b₁ d := by
  rw [xSeed_eq_lambdaAt_succ r b₁]
  exact lambdaAt_antitone (2 ^ r) b₁ hd

/-- **`08:963--965`, the displayed inequality `lambda_d >= lambda_r = 2^{1-b_1}`.**
At every suffix depth `d <= r` the routing threshold is at least twice the seed
density.  General. -/
theorem two_mul_xSeed_le_lambdaAt_of_le {r b₁ d : ℕ} (hd : d ≤ r) :
    2 * xSeed b₁ ≤ lambdaAt (2 ^ r) b₁ d := by
  have hval : lambdaAt (2 ^ r) b₁ r = 2 / 2 ^ b₁ := lambdaAt_at_depth_log r b₁
  have hmono : lambdaAt (2 ^ r) b₁ r ≤ lambdaAt (2 ^ r) b₁ d :=
    lambdaAt_antitone (2 ^ r) b₁ hd
  have hseed : xSeed b₁ = 1 / 2 ^ b₁ := xSeed_eq_inv_pow b₁
  rw [hseed]
  rw [hval] at hmono
  have h2 : (2 : ℝ) * (1 / 2 ^ b₁) = 2 / 2 ^ b₁ := by ring
  rw [h2]
  exact hmono

/-- **Aux 10.**  Strictly above the frozen depth the residual capacity is at least
two, the frozen "`B_cap + 1` certificate requires `kappa_v >= 2`" arithmetic in the
form the isolation clause spends.  General. -/
theorem two_le_stoppingCapacity_of_lt {r d : ℕ} (h : d < r) :
    2 ≤ stoppingCapacity r d := by
  have hstep := two_mul_stoppingCapacity_succ h
  have hone := one_le_stoppingCapacity r (d + 1)
  omega

/-! ## §3  Trimming to the seed density (`08:966`)

"Trim this support to density `2^{-b_1}`."  The frozen trim is an integer
requirement on the surviving quotient columns, so the target is the ceiling
`ceil(2^{-b_1}|C_1|)`, exactly as the banked `routingFloor` records the frozen
`L_d = ceil(lambda_d |C_1|)`. -/

/-- The integer target of the frozen trim, `ceil(2^{-b_1}|C_1|)` (`08:966`). -/
noncomputable def seedFloor (Γ : Type*) [Fintype Γ] (b₁ : ℕ) : ℕ :=
  ⌈xSeed b₁ * (Fintype.card Γ : ℝ)⌉₊

/-- **Aux 11.**  The trim target dominates the real density it rounds.  General. -/
theorem seedFloor_le (Γ : Type*) [Fintype Γ] (b₁ : ℕ) :
    xSeed b₁ * (Fintype.card Γ : ℝ) ≤ (seedFloor Γ b₁ : ℝ) :=
  Nat.le_ceil _

/-- **Aux 12 (the trim is legal at every depth the frozen proof uses).**  For
`d <= r + 1` the seed floor is at most the banked routing floor
`L_d = ceil(lambda_d |C_1|)`.  General. -/
theorem seedFloor_le_routingFloor (Γ : Type*) [Fintype Γ] {r b₁ d : ℕ}
    (hd : d ≤ r + 1) : seedFloor Γ b₁ ≤ routingFloor Γ (2 ^ r) b₁ d := by
  unfold seedFloor routingFloor
  exact Nat.ceil_le_ceil
    (mul_le_mul_of_nonneg_right (xSeed_le_lambdaAt_of_le_succ hd) (by positivity))

/-- **`08:963--966`, the trimming step.**  A routed object whose support meets the
banked routing floor at suffix depth `d <= r + 1` can be trimmed to the frozen seed
density `2^{-b_1}`: its support already meets the integer target.

The routing floor hypothesis is the endpoint of `lem:dense-routing`, consumed **by
pin** from the banked `DenseRoutingInvariant`; nothing here re-proves it.
General. -/
theorem trim_to_seed_floor {Γ : Type*} [Fintype Γ] {r b₁ d : ℕ} {T : Finset Γ}
    (hinv : routingFloor Γ (2 ^ r) b₁ d ≤ T.card) (hd : d ≤ r + 1) :
    seedFloor Γ b₁ ≤ T.card :=
  le_trans (seedFloor_le_routingFloor Γ hd) hinv

/-! ## §4  Suffix depth in the residual protocol

The frozen "suffix depth" of `08:952--959` is the number of queries a token has
passed below the root of `P_*`.  The banked Alice walk stops at a Bob node by
design, so it cannot follow a token that is routed *through* Bob queries; this
section is the two-sided walk that can, together with the budget accounting the
frozen proof spends at `08:975--976`. -/

section Walk

variable {X Y Z : Type*}

/-- One step of the walk: descend along the edge named by the bit, at a node of
either player.  At a leaf the walk is stationary. -/
def descendStep : Protocol X Y Z → Bool → Protocol X Y Z
  | Protocol.leaf z, _ => Protocol.leaf z
  | Protocol.aNode _ l r, b => if b then r else l
  | Protocol.bNode _ l r, b => if b then r else l

/-- The node reached by following the bits of `p` below `P`. -/
def descend : Protocol X Y Z → List Bool → Protocol X Y Z
  | P, [] => P
  | P, b :: p => descend (descendStep P b) p

/-- "The node is a query node", i.e. not a protocol leaf. -/
def IsQueryNode : Protocol X Y Z → Prop
  | Protocol.leaf _ => False
  | Protocol.aNode _ _ _ => True
  | Protocol.bNode _ _ _ => True

/-- "The node is a Bob query", the only kind a positive token is routed through
(`08:880`, `08:952--953`). -/
def IsBobNode : Protocol X Y Z → Prop
  | Protocol.leaf _ => False
  | Protocol.aNode _ _ _ => False
  | Protocol.bNode _ _ _ => True

/-- Every node strictly along `p` is a query node.  The node `p` itself reaches is
unconstrained: it is where the token stops. -/
def IsQueryPath : Protocol X Y Z → List Bool → Prop
  | _, [] => True
  | P, b :: p => IsQueryNode P ∧ IsQueryPath (descendStep P b) p

/-- Every node strictly along `p` is a Bob query -- the frozen "before the first
Alice query on its path" (`08:952--953`), which is also what lets `08:962` say the
template row set is unchanged. -/
def IsBobPath : Protocol X Y Z → List Bool → Prop
  | _, [] => True
  | P, b :: p => IsBobNode P ∧ IsBobPath (descendStep P b) p

/-- **Aux 13.**  The empty route reaches the root.  General. -/
@[simp] theorem descend_nil (P : Protocol X Y Z) : descend P [] = P := rfl

/-- **Aux 14.**  The walk commutes with its first step.  General. -/
theorem descend_cons (P : Protocol X Y Z) (b : Bool) (p : List Bool) :
    descend P (b :: p) = descend (descendStep P b) p := rfl

/-- **Aux 15 (stationarity).**  Past a leaf the walk stands still.  General. -/
theorem descend_leaf (z : Z) (p : List Bool) :
    descend (Protocol.leaf z : Protocol X Y Z) p = Protocol.leaf z := by
  induction p with
  | nil => rfl
  | cons b p ih => simpa [descend_cons, descendStep] using ih

/-- **Aux 16 (composition).**  Walking `p` then `q` is walking `p ++ q`.  General. -/
theorem descend_append (P : Protocol X Y Z) (p q : List Bool) :
    descend P (p ++ q) = descend (descend P p) q := by
  induction p generalizing P with
  | nil => simp
  | cons b p ih => simpa [descend_cons] using ih (descendStep P b)

/-- **Aux 17.**  A step never increases the cost.  General. -/
theorem cost_descendStep_le (P : Protocol X Y Z) (b : Bool) :
    (descendStep P b).cost ≤ P.cost := by
  cases P with
  | leaf z => cases b <;> simp [descendStep]
  | aNode a l r =>
      have hchild : (descendStep (Protocol.aNode a l r) b).cost ≤ max l.cost r.cost := by
        cases b <;> simp [descendStep]
      simp only [Protocol.cost]
      omega
  | bNode b' l r =>
      have hchild : (descendStep (Protocol.bNode b' l r) b).cost ≤ max l.cost r.cost := by
        cases b <;> simp [descendStep]
      simp only [Protocol.cost]
      omega

/-- **Aux 18.**  The walk never increases the cost.  General. -/
theorem cost_descend_le (P : Protocol X Y Z) (p : List Bool) :
    (descend P p).cost ≤ P.cost := by
  induction p generalizing P with
  | nil => simp
  | cons b p ih =>
      exact le_trans (by simpa [descend_cons] using ih (P := descendStep P b))
        (cost_descendStep_le P b)

/-- **Aux 19.**  A leaf is not a query node.  General. -/
theorem not_isQueryNode_leaf (z : Z) :
    ¬ IsQueryNode (Protocol.leaf z : Protocol X Y Z) := by
  simp [IsQueryNode]

/-- **Aux 20.**  A Bob query is a query.  General. -/
theorem isQueryNode_of_isBobNode {P : Protocol X Y Z} (h : IsBobNode P) :
    IsQueryNode P := by
  cases P with
  | leaf z => exact absurd h (by simp [IsBobNode])
  | aNode a l r => exact absurd h (by simp [IsBobNode])
  | bNode b l r => trivial

/-- **Aux 21.**  A Bob-only route is a query route -- the form the budget accounting
consumes.  General. -/
theorem isQueryPath_of_isBobPath : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsBobPath P p → IsQueryPath P p := by
  intro P p
  induction p generalizing P with
  | nil => intro _; trivial
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩
      exact ⟨isQueryNode_of_isBobNode hnode, ih hrest⟩

/-- **Aux 22 (prefix closure).**  Every prefix of a query route is a query route.
General; this is what lets the frozen proof look at the length-`(r+1)` prefix of a
longer route. -/
theorem isQueryPath_take : ∀ (n : ℕ) {P : Protocol X Y Z} {p : List Bool},
    IsQueryPath P p → IsQueryPath P (p.take n) := by
  intro n
  induction n with
  | zero => intro P p _; simp only [List.take_zero]; trivial
  | succ n ih =>
      intro P p h
      cases p with
      | nil => simpa using h
      | cons b p =>
          obtain ⟨hnode, hrest⟩ := h
          exact ⟨hnode, ih hrest⟩

/-- **Aux 23 (one query costs one bit).**  At a query node, the child's cost plus the
bit spent is at most the parent's cost.  General. -/
theorem cost_descendStep_succ_le {P : Protocol X Y Z} (h : IsQueryNode P) (b : Bool) :
    (descendStep P b).cost + 1 ≤ P.cost := by
  cases P with
  | leaf z => exact absurd h (not_isQueryNode_leaf z)
  | aNode a l r =>
      have hchild : (descendStep (Protocol.aNode a l r) b).cost ≤ max l.cost r.cost := by
        cases b <;> simp [descendStep]
      simp only [Protocol.cost]
      omega
  | bNode b' l r =>
      have hchild : (descendStep (Protocol.bNode b' l r) b).cost ≤ max l.cost r.cost := by
        cases b <;> simp [descendStep]
      simp only [Protocol.cost]
      omega

/-! ## §5  The budget accounting (`08:975--976`)

"the total suffix budget `B_cap + r` leaves at most `B_cap - 1` further bits".  The
frozen sentence is the statement that a node at suffix depth `d` has already spent
`d` of the residual budget. -/

/-- **`08:975--976`, the suffix budget.**  A node reached by a query route of length
`d` keeps at most `cost(P_*) - d` further bits.  General.

*Why the hypothesis is load-bearing.*  Without `IsQueryPath` the statement is false:
`cost_descend_pole_needs_query_path` exhibits a protocol and a route walking off a
leaf whose length exceeds the whole budget. -/
theorem cost_descend_add_length_le {p : List Bool} :
    ∀ {P : Protocol X Y Z}, IsQueryPath P p → (descend P p).cost + p.length ≤ P.cost := by
  induction p with
  | nil => intro P _; simp
  | cons b p ih =>
      intro P h
      obtain ⟨hnode, hrest⟩ := h
      have h1 := ih (P := descendStep P b) hrest
      have h2 := cost_descendStep_succ_le hnode b
      simp only [descend_cons, List.length_cons]
      omega

/-- **Aux 24.**  In particular no query route is longer than the budget.  General. -/
theorem length_le_cost_of_isQueryPath {P : Protocol X Y Z} {p : List Bool}
    (h : IsQueryPath P p) : p.length ≤ P.cost := by
  have := cost_descend_add_length_le (P := P) h
  omega

end Walk

/-! ## §6  What a node of positive complexity is not (`08:971--972`)

"In particular the node is not monochromatic." -/

section NodeReadouts

variable {A B : Type*} [Fintype A] [Fintype B]

/-- **Aux 25.**  A game taking two distinct values has positive complexity: no
cost-`0` protocol computes it.  Nonemptiness of the achievable-cost set is a
hypothesis rather than an appeal, because `D` is an `sInf` and returns `0` on the
empty set.  General. -/
theorem one_le_D_of_ne {gnode : A → B → Bool} {a₁ a₂ : A} {b₁ b₂ : B}
    (hne : gnode a₁ b₁ ≠ gnode a₂ b₂)
    (hach : (AchievableCosts gnode).Nonempty) : 1 ≤ D gnode := by
  by_contra hlt
  have h0 : D gnode = 0 := by omega
  have hmem : (0 : ℕ) ∈ AchievableCosts gnode := by
    have hmem' := Nat.sInf_mem hach
    have : sInf (AchievableCosts gnode) = 0 := h0
    rwa [this] at hmem'
  obtain ⟨P, hcost, hcomp⟩ := hmem
  cases P with
  | leaf z =>
      have h1 := hcomp a₁ b₁
      have h2 := hcomp a₂ b₂
      simp only [Protocol.eval] at h1 h2
      exact hne (by rw [← h1, ← h2])
  | aNode a l r => simp only [Protocol.cost] at hcost; omega
  | bNode b l r => simp only [Protocol.cost] at hcost; omega

/-- **`08:972`, "In particular the node is not monochromatic".**  A game of positive
complexity is computed by no leaf protocol, i.e. it is not constant.  General. -/
theorem node_not_monochromatic {gnode : A → B → Bool} (hpos : 0 < D gnode) (z : Bool) :
    ¬ Protocol.Computes (Protocol.leaf z : Protocol A B Bool) gnode := by
  intro hcomp
  have hmem : (0 : ℕ) ∈ AchievableCosts gnode := ⟨Protocol.leaf z, rfl, hcomp⟩
  have hle : D gnode ≤ 0 := Nat.sInf_le hmem
  omega

end NodeReadouts

/-- **`08:972`, the protocol-side reading.**  If the node's game is `B_cap`-hard with
`B_cap >= 1`, and the node's residual subtree solves that game, then the node is not
a protocol leaf.

`hresidual` is the named protocol-semantic hypothesis of coverage limit 3: this
block builds no rectangle apparatus and so never derives it.  General. -/
theorem node_not_leaf {X Y Z A B : Type*} [Fintype A] [Fintype B]
    {gnode : A → B → Bool} {P : Protocol X Y Z} {p : List Bool} {bcap : ℕ}
    (hbcap : 0 < bcap) (hhard : bcap ≤ D gnode)
    (hresidual : D gnode ≤ (descend P p).cost) (z : Z) :
    descend P p ≠ Protocol.leaf z := by
  intro hleaf
  rw [hleaf] at hresidual
  simp only [Protocol.cost] at hresidual
  omega

/-! ## §7  The positive token and the frozen stopping rule (`08:946--953`)

"A *positive token* means one unit-weight component: either an ordinary token or the
bonus component of a witness object.  Follow every positive token below the root of
`P_*`.  Stop it when its Stage-2 coordinate is isolated, immediately before the first
Alice query on its path, or provisionally at a protocol leaf." -/

/-- The two frozen unit-weight components of `08:949--951`. -/
inductive TokenKind
  | ordinary
  | bonus
  deriving DecidableEq, Repr

/-- The three frozen stopping events of `08:952--953`. -/
inductive StopEvent
  | isolation
  | beforeAlice
  | atLeaf
  deriving DecidableEq, Repr

/-- **The stop record of a positive token (Candidate A).**  The token's Stage-2
coordinate, its kind, the route it followed below the root of `P_*`, and which of the
three frozen events stopped it -- together with the well-formedness laws of the
frozen rule, and nothing else.  The suffix depth is the derived `route.length`; no
field records what `lem:dense-no-leaf` concludes. -/
structure StoppedToken {X Y Z : Type*} (Pstar : Protocol X Y Z) (Coord : Type*) where
  /-- The Stage-2 coordinate the token carries. -/
  coord : Coord
  /-- Which unit-weight component it is (`08:949--950`). -/
  kind : TokenKind
  /-- The route followed below the root of `P_*` (`08:951`). -/
  route : List Bool
  /-- Which frozen event stopped it (`08:952--953`). -/
  event : StopEvent
  /-- Every node strictly before the stopping node is a Bob query: the token is
  routed through Bob queries and stops before the first Alice query on its path
  (`08:880`, `08:952--953`). -/
  route_bob : IsBobPath Pstar route
  /-- The provisional stop happens at a protocol leaf (`08:953`). -/
  atLeaf_at_leaf : event = StopEvent.atLeaf → ∃ z : Z, descend Pstar route = Protocol.leaf z
  /-- The Alice stop happens immediately before an Alice query (`08:952--953`,
  `08:981--982`); `IsANode` is the banked `DenseSynchronisation` predicate. -/
  beforeAlice_at_alice : event = StopEvent.beforeAlice → IsANode (descend Pstar route)

namespace StoppedToken

variable {X Y Z Coord : Type*} {Pstar : Protocol X Y Z}

/-- The suffix depth at which the token stopped (`08:958`), a derived quantity. -/
def depth (t : StoppedToken Pstar Coord) : ℕ := t.route.length

/-- **Aux 26.**  The suffix depth is the length of the route.  General. -/
@[simp] theorem depth_eq (t : StoppedToken Pstar Coord) : t.depth = t.route.length := rfl

/-- **Aux 27.**  The three frozen events are exhaustive.  General. -/
theorem event_cases (t : StoppedToken Pstar Coord) :
    t.event = StopEvent.isolation ∨ t.event = StopEvent.beforeAlice
      ∨ t.event = StopEvent.atLeaf := by
  cases h : t.event with
  | isolation => exact Or.inl rfl
  | beforeAlice => exact Or.inr (Or.inl rfl)
  | atLeaf => exact Or.inr (Or.inr rfl)

/-- **Aux 28.**  A token's route is a query route, so the budget accounting applies to
it.  General. -/
theorem route_isQueryPath (t : StoppedToken Pstar Coord) : IsQueryPath Pstar t.route :=
  isQueryPath_of_isBobPath t.route_bob

/-- **Aux 29.**  Every prefix of a token's route is a query route -- the frozen proof
looks at the length-`(r+1)` one.  General. -/
theorem take_isQueryPath (t : StoppedToken Pstar Coord) (n : ℕ) :
    IsQueryPath Pstar (t.route.take n) :=
  isQueryPath_take n t.route_isQueryPath

end StoppedToken

/-! ## §8  `lem:dense-no-leaf` (`08:955--979`)

"Every positive token stops at coordinate isolation or before its first Alice query,
and it does so at suffix depth at most `r`." -/

/-- **`08:963--971`, the one-copy lower bound at a node.**  A routed object whose
support meets the banked routing floor at suffix depth `d <= r + 1` can be trimmed to
the seed density `2^{-b_1}`, and the relaxed-to-classical transfer then makes the
node's game `B_cap`-hard.

The transfer itself -- "relaxed-to-classical transfer and `x_dom/(1+eps_2) >= 3/5`
give a one-copy restriction of `M_1^T` with complexity at least `B_cap`" -- is the
named hypothesis `honeCopy`, **gated on the trimmed support**, so nothing is assumed
at a node where the frozen hypothesis fails.  The routing floor hypothesis is the
endpoint of `lem:dense-routing`, consumed by pin.  General. -/
theorem oneCopy_hard_at_node {Phys Coord Γ A B : Type*} [Fintype Γ] [DecidableEq Coord]
    [DecidableEq Γ] [Fintype A] [Fintype B] (gnode : A → B → Bool)
    (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord) {r b₁ d bcap : ℕ}
    (honeCopy : seedFloor Γ b₁ ≤ (quotientSupport rep S α).card → bcap ≤ D gnode)
    (hinv : routingFloor Γ (2 ^ r) b₁ d ≤ (quotientSupport rep S α).card)
    (hd : d ≤ r + 1) : bcap ≤ D gnode :=
  honeCopy (trim_to_seed_floor hinv hd)

/-- **`08:974--978`, the depth clause.**  "Nor can a positive token first reach depth
`r+1`.  Its support there is still at least `2^{-b_1}`, so the same one-copy lower
bound applies, while the total suffix budget `B_cap + r` leaves at most `B_cap - 1`
further bits."

Stated at the length-`(r+1)` prefix of the token's route, exactly as the frozen proof
argues: the token would have to *pass through* that node, and the certificate there
already exceeds what the budget leaves. -/
theorem denseNoLeaf_depth_le {X Y Z Coord : Type*}
    {A B : List Bool → Type*} [∀ p, Fintype (A p)] [∀ p, Fintype (B p)]
    {Pstar : Protocol X Y Z} (g : ∀ p : List Bool, A p → B p → Bool)
    (t : StoppedToken Pstar Coord) {r bcap : ℕ}
    (hbudget : Pstar.cost ≤ Dtwo bcap r)
    (hdeepHard : r + 1 ≤ t.route.length → bcap ≤ D (g (t.route.take (r + 1))))
    (hdeepResidual : r + 1 ≤ t.route.length →
      D (g (t.route.take (r + 1))) ≤ (descend Pstar (t.route.take (r + 1))).cost) :
    t.route.length ≤ r := by
  by_contra hlong
  have hge : r + 1 ≤ t.route.length := by omega
  have hpath : IsQueryPath Pstar (t.route.take (r + 1)) := t.take_isQueryPath (r + 1)
  have hlen : (t.route.take (r + 1)).length = r + 1 := by
    rw [List.length_take]
    omega
  have hspent := cost_descend_add_length_le (P := Pstar) hpath
  rw [hlen] at hspent
  have hhard := hdeepHard hge
  have hres := hdeepResidual hge
  rw [Dtwo_eq] at hbudget
  omega

/-- **`08:961--972`, the no-premature-leaf clause.**  At a stopping node of suffix
depth at most `r` the node's game is `B_cap`-hard, so with `B_cap >= 1` the node is
not a protocol leaf and the provisional stop of `08:953` cannot have fired. -/
theorem denseNoLeaf_event_ne_atLeaf {X Y Z Coord : Type*}
    {A B : List Bool → Type*} [∀ p, Fintype (A p)] [∀ p, Fintype (B p)]
    {Pstar : Protocol X Y Z} (g : ∀ p : List Bool, A p → B p → Bool)
    (t : StoppedToken Pstar Coord) {r bcap : ℕ}
    (hbcap : 0 < bcap) (hshallow : t.route.length ≤ r)
    (hnodeHard : t.route.length ≤ r → bcap ≤ D (g t.route))
    (hnodeResidual : t.route.length ≤ r →
      D (g t.route) ≤ (descend Pstar t.route).cost) :
    t.event ≠ StopEvent.atLeaf := by
  intro hev
  obtain ⟨z, hleaf⟩ := t.atLeaf_at_leaf hev
  exact node_not_leaf hbcap (hnodeHard hshallow) (hnodeResidual hshallow) z hleaf

/-- **`lem:dense-no-leaf` (`08:955--959`).**  "Every positive token stops at
coordinate isolation or before its first Alice query, and it does so at suffix depth
at most `r`."

The four deep inputs are **two gated pairs**, at exactly the depths the frozen proof
states them: the local one-copy certificate and the node's residual reading are gated
on `route.length <= r` (`08:962--972`), and the same pair at the length-`(r+1)`
prefix is gated on `r + 1 <= route.length` (`08:974--978`).  The two gates are
mutually exclusive, so the bundle never conjoins two cases of one construction; and
neither is assumed past depth `r + 1`, where the frozen trimming step becomes illegal
(`seedFloor_pole_beyond_succ_width`).

`hbudget` is `eq:selected-upper-budget` at the banked `Dtwo = B_cap + log_2 q_2`,
with the frozen `q_2 = 2^r`.

*Why neither conclusion is automatic.*  `StoppedToken` is inhabited with
`event = atLeaf` (`stoppedToken_leaf_stop_is_inhabited`) and with routes of every
length, so both clauses fail for a token whose node is monochromatic or whose budget
is larger; and `denseNoLeaf_hypotheses_consistent` exhibits the whole bundle at legal
values where both firing hypotheses are **tight** and the depth bound is attained. -/
theorem denseNoLeaf {X Y Z Coord : Type*}
    {A B : List Bool → Type*} [∀ p, Fintype (A p)] [∀ p, Fintype (B p)]
    {Pstar : Protocol X Y Z} (g : ∀ p : List Bool, A p → B p → Bool)
    (t : StoppedToken Pstar Coord) {r bcap : ℕ}
    (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ Dtwo bcap r)
    (hnodeHard : t.route.length ≤ r → bcap ≤ D (g t.route))
    (hnodeResidual : t.route.length ≤ r →
      D (g t.route) ≤ (descend Pstar t.route).cost)
    (hdeepHard : r + 1 ≤ t.route.length → bcap ≤ D (g (t.route.take (r + 1))))
    (hdeepResidual : r + 1 ≤ t.route.length →
      D (g (t.route.take (r + 1))) ≤ (descend Pstar (t.route.take (r + 1))).cost) :
    (t.event = StopEvent.isolation ∨ t.event = StopEvent.beforeAlice)
      ∧ t.route.length ≤ r := by
  have hshallow : t.route.length ≤ r :=
    denseNoLeaf_depth_le g t hbudget hdeepHard hdeepResidual
  have hne : t.event ≠ StopEvent.atLeaf :=
    denseNoLeaf_event_ne_atLeaf g t hbcap hshallow hnodeHard hnodeResidual
  refine ⟨?_, hshallow⟩
  rcases t.event_cases with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hne

/-! ## §9  The stopping frontier and `eq:isolation-capacity` (`08:981--1012`)

"The stopping nodes form a prefix-free frontier. ...  If both descriptions hold at the
same protocol node, classify it as a coordinate-isolation node; the two frontier
classes are therefore disjoint and exhaustive." -/

/-- The two frontier classes of `08:984--985`. -/
inductive FrontierClass
  | isolation
  | alice
  deriving DecidableEq, Repr

section Frontier

variable {ι : Type*}

/-- The frozen classification with its tie-break (`08:983--985`): a node is an
isolation node when the isolation description applies, and an Alice node otherwise.
Priority to isolation is what makes the two classes disjoint. -/
def frontierClass (iso : ι → Prop) [DecidablePred iso] (v : ι) : FrontierClass :=
  if iso v then FrontierClass.isolation else FrontierClass.alice

variable (iso : ι → Prop) [DecidablePred iso]

/-- **Aux 30.**  General. -/
theorem frontierClass_isolation_iff (v : ι) :
    frontierClass iso v = FrontierClass.isolation ↔ iso v := by
  unfold frontierClass
  by_cases h : iso v <;> simp [h]

/-- **Aux 31.**  General. -/
theorem frontierClass_alice_iff (v : ι) :
    frontierClass iso v = FrontierClass.alice ↔ ¬ iso v := by
  unfold frontierClass
  by_cases h : iso v <;> simp [h]

/-- **`08:983--984`, the tie-break.**  "If both descriptions hold at the same protocol
node, classify it as a coordinate-isolation node."  The Alice description is carried
as an arbitrary predicate to make the priority explicit: it does not enter the
classification at all.  General. -/
theorem frontierClass_isolation_of_both (alice : ι → Prop) (v : ι)
    (hiso : iso v) (_halice : alice v) :
    frontierClass iso v = FrontierClass.isolation :=
  (frontierClass_isolation_iff iso v).2 hiso

variable [Fintype ι] [DecidableEq ι]

/-- The isolation class of the frontier (`08:984--985`). -/
def isolationNodes : Finset ι :=
  Finset.univ.filter (fun v => frontierClass iso v = FrontierClass.isolation)

/-- The Alice class of the frontier (`08:984--985`). -/
def aliceNodes : Finset ι :=
  Finset.univ.filter (fun v => frontierClass iso v = FrontierClass.alice)

omit [DecidableEq ι] in
/-- **`08:984--985`, disjointness.**  General. -/
theorem frontier_disjoint : Disjoint (isolationNodes iso) (aliceNodes iso) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [isolationNodes, Finset.mem_filter] at hv
  rw [aliceNodes, Finset.mem_filter] at hv'
  rw [hv.2] at hv'
  exact absurd hv'.2 (by simp)

/-- **`08:984--985`, exhaustiveness.**  General. -/
theorem frontier_union : isolationNodes iso ∪ aliceNodes iso = Finset.univ := by
  ext v
  simp only [Finset.mem_union, isolationNodes, aliceNodes, Finset.mem_filter,
    Finset.mem_univ, true_and, iff_true]
  cases h : frontierClass iso v with
  | isolation => exact Or.inl rfl
  | alice => exact Or.inr rfl

end Frontier

/-- "The stopping nodes form a prefix-free frontier" (`08:981`), as a property of the
family of routes indexed by the frontier.  The counting consequence
`sum_v kappa_v <= q_2` (`08:1000`) is **not** proved here -- see coverage limit 5. -/
def PrefixFreeFrontier {ι : Type*} (route : ι → List Bool) : Prop :=
  ∀ v w : ι, v ≠ w → ¬ (route v).IsPrefix (route w)

/-- **Aux 32.**  A prefix-free frontier has distinct routes: a node is a prefix of
itself, so two frontier nodes with one route would be one node.  General. -/
theorem prefixFreeFrontier_injective {ι : Type*} {route : ι → List Bool}
    (h : PrefixFreeFrontier route) {v w : ι} (hvw : route v = route w) : v = w := by
  by_contra hne
  exact h v w hne (by rw [hvw])

/-- **`eq:isolation-capacity` (`08:1004--1012`).**  "By the coordinatewise uniqueness
in `lem:dense-routing`, an isolation node contains at most one routed object.  It
therefore contains either one ordinary token, which requires `kappa_v >= 1`, or one
unsplit witness, whose `B_cap + 1` certificate requires `kappa_v >= 2`.  Therefore
`h_v + z_v <= kappa_v` at every isolation node."

The uniqueness clause is the **named hypothesis** `huniq : h <= 1`, honouring the
banked `DenseRoutingInvariant`'s coverage limit 3 (it did not prove that the routing
preserves the one-object-per-coordinate representation across a query).  The two
capacity requirements are the named `hone` and `htwo`; `hz` is the frozen
`0 <= z_v <= h_v` of `08:990--992`, which the paper derives rather than assumes and
which is therefore a binder here, not a field of any bundle.  General. -/
theorem isolationNode_capacity {h z κ : ℕ}
    (huniq : h ≤ 1) (hz : z ≤ h) (hone : 1 ≤ κ) (htwo : 0 < z → 2 ≤ κ) :
    h + z ≤ κ := by
  rcases Nat.eq_zero_or_pos z with hz0 | hzpos
  · omega
  · have := htwo hzpos
    omega

/-- **`eq:isolation-capacity` at the frozen capacity weight.**  At an isolation node of
suffix depth `d_v` -- any depth, since `kappa_v = 2^{r-d_v} >= 1` holds outright -- the
routed masses fit in the residual capacity.  General. -/
theorem isolationNode_capacity_at_depth {r d h z : ℕ}
    (huniq : h ≤ 1) (hz : z ≤ h) (htwo : 0 < z → 2 ≤ stoppingCapacity r d) :
    h + z ≤ stoppingCapacity r d :=
  isolationNode_capacity huniq hz (one_le_stoppingCapacity r d) htwo

/-! ## §10  Non-vacuity, statement poles and consistency probes

Every definition above is a carrier a later tranche will read, and the headline is a
universally quantified implication.  A degenerate carrier or an unsatisfiable premise
bundle would make every consumer vacuous while compiling green, so each is probed
here.  No parameter schedule may be read out of any witness below. -/

/-- **Non-vacuity of the capacity weight, symbolic in the frozen width.**  For every
`r` and every suffix depth `d <= r` the residual capacity is a genuine positive power
of two that halves with depth, equals the frozen width `q_2 = 2^r` at the root and is
exhausted at depth `r`.  Nothing is evaluated, so this reaches the frozen widths
`q_2 >= 6144` that no literal reaches. -/
theorem stoppingCapacity_nondegenerate (r : ℕ) :
    stoppingCapacity r 0 = 2 ^ r ∧ stoppingCapacity r r = 1 ∧
      (∀ d, 1 ≤ stoppingCapacity r d ∧ stoppingCapacity r d ≤ 2 ^ r) ∧
      (∀ d, d < r → 2 * stoppingCapacity r (d + 1) = stoppingCapacity r d
        ∧ 2 ≤ stoppingCapacity r d) := by
  refine ⟨stoppingCapacity_at_root r, stoppingCapacity_at_depth r,
    fun d => ⟨one_le_stoppingCapacity r d, stoppingCapacity_le_width r d⟩, fun d hd => ?_⟩
  exact ⟨two_mul_stoppingCapacity_succ hd, two_le_stoppingCapacity_of_lt hd⟩

/-- **Non-vacuity of the trimming layer, at a routing-slack-legal parameter pair.**
The carrier is `|C_1| = 1024` with `b_1 = 5` and `r = 1`, so the frozen width is
`q_2 = 2^r = 2`.  Legality is proved **on the face of the statement**: the first
conjunct is `RoutingSlack (2^1) 5`, the frozen `eq:routing-slack` (`08:805--810`) at
this very pair, i.e. `lambda_0 = 2 q_2 2^{-b_1} = 1/8 <= p_root = 3/4` **and**
`p_root - lambda_0 = 5/8 > omega = 1/2`.

The pair discharges the frozen `eq:routing-slack` (`08:805--810`) -- the only
schedule consequence Section 8's routing and trimming argument consumes -- and the
schedule line `2 q_2 2^{-b_1} <= 1/8` (`06:838`) at equality.  It does **not**
satisfy the full `eq:stage2-structural-gates` (`06:832--847`), which forces
`q_2 >= 64 s q_1 / zeta >= 6144` and hence `r >= 13`; the probe does not need it,
because `seedFloor_le_routingFloor` is general in `r`, `b_1` and `d` and takes no
schedule hypothesis.  The pair `(q_2, b_1) = (2, 5)` is the banked
`DenseRoutingInvariant`'s own gate-legal pair, so the two modules probe the
trimming layer at one point; the carrier is widened to `1024` because the
strict separations below need `2^{-b_1}|C_1|` to be a large integer.

At that pair the seed floor `ceil(2^{-b_1}|C_1|) = 32` is a **strictly** smaller
integer than the routing floor at every depth `d <= r` -- `128` at the root and `64`
at depth `1` -- so the frozen "Trim this support to density `2^{-b_1}`" (`08:967`) is
a real trim and not an identity.  At depth `d = r + 1 = 2` the two floors are
**equal**, and that identity is exhibited as its own conjunct: the pinned inequality
`seedFloor_le_routingFloor` is tight exactly at the depth where the frozen proof
stops (`08:974--975`). -/
theorem seedFloor_nondegenerate :
    RoutingSlack (2 ^ 1) 5
      ∧ seedFloor (Fin 1024) 5 = 32
      ∧ routingFloor (Fin 1024) (2 ^ 1) 5 0 = 128
      ∧ routingFloor (Fin 1024) (2 ^ 1) 5 1 = 64
      ∧ routingFloor (Fin 1024) (2 ^ 1) 5 2 = 32
      ∧ seedFloor (Fin 1024) 5 < routingFloor (Fin 1024) (2 ^ 1) 5 0
      ∧ seedFloor (Fin 1024) 5 < routingFloor (Fin 1024) (2 ^ 1) 5 1
      ∧ seedFloor (Fin 1024) 5 = routingFloor (Fin 1024) (2 ^ 1) 5 2 := by
  have hslack : RoutingSlack (2 ^ 1) 5 := by
    unfold RoutingSlack lambdaZero
    rw [pRoot_eq, omegaRoute_eq]
    norm_num
  have h1 : seedFloor (Fin 1024) 5 = 32 := by
    unfold seedFloor
    rw [xSeed_eq_inv_pow]
    norm_num
  have h2 : routingFloor (Fin 1024) (2 ^ 1) 5 0 = 128 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  have h3 : routingFloor (Fin 1024) (2 ^ 1) 5 1 = 64 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  have h4 : routingFloor (Fin 1024) (2 ^ 1) 5 2 = 32 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  exact ⟨hslack, h1, h2, h3, h4, by omega, by omega, by omega⟩

/-- **Statement pole (the trim gate is load-bearing), at the same
routing-slack-legal pair.**  Past depth `r + 1` the frozen trimming step is illegal,
and the first conjunct is again `RoutingSlack (2^1) 5`, the frozen
`eq:routing-slack` (`08:805--810`), so the pole is not an artefact of a pair
violating `eq:routing-slack`.  (As above, the pair does not satisfy the full
`eq:stage2-structural-gates` (`06:832--847`), and does not need to: the pinned
`seedFloor_le_routingFloor` is general in `r`, `b_1` and `d`.)  At
`|C_1| = 1024`, `b_1 = 5`, `r = 1` the routing floor at depth `3 = r + 2` is `16`,
strictly below the seed floor `32`, so an ungated one-copy hypothesis at the stopping
node would assume strictly more than the paper states. -/
theorem seedFloor_pole_beyond_succ_width :
    RoutingSlack (2 ^ 1) 5
      ∧ routingFloor (Fin 1024) (2 ^ 1) 5 3 < seedFloor (Fin 1024) 5 := by
  have hslack : RoutingSlack (2 ^ 1) 5 := by
    unfold RoutingSlack lambdaZero
    rw [pRoot_eq, omegaRoute_eq]
    norm_num
  have h1 : seedFloor (Fin 1024) 5 = 32 := by
    unfold seedFloor
    rw [xSeed_eq_inv_pow]
    norm_num
  have h2 : routingFloor (Fin 1024) (2 ^ 1) 5 3 = 16 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  exact ⟨hslack, by omega⟩

/-- **Statement pole (the budget accounting needs its query route).**  Without
`IsQueryPath` the frozen suffix accounting fails outright: a route walking off a leaf
has any length at all while the protocol has spent nothing. -/
theorem cost_descend_pole_needs_query_path :
    ∃ (P : Protocol Bool Bool Bool) (p : List Bool),
      ¬ IsQueryPath P p ∧ P.cost < (descend P p).cost + p.length := by
  refine ⟨Protocol.leaf true, [true, true], ?_, ?_⟩
  · rintro ⟨h, -⟩
    exact not_isQueryNode_leaf true h
  · rw [descend_leaf]
    simp only [Protocol.cost, List.length_cons, List.length_nil]
    omega

/-! ### The witness protocol for the stop-record probes

`Pstar` is a Bob query whose right child is a genuine Alice query and whose left child
is a leaf.  It is a probe of the definitions at a deliberately small carrier, not a
schedule instance. -/

/-- The probe protocol: `cost = 2`, one Bob query above one Alice query. -/
def probeProtocol : Protocol Bool Bool Bool :=
  Protocol.bNode (fun y => y)
    (Protocol.leaf false)
    (Protocol.aNode (fun x => x) (Protocol.leaf false) (Protocol.leaf true))

/-- **Aux 33.**  The probe protocol costs exactly two bits.  General for the probe. -/
theorem probeProtocol_cost : probeProtocol.cost = 2 := by
  simp [probeProtocol, Protocol.cost]

/-- **Aux 34.**  Its right child, reached by the route `[true]`, is the Alice query. -/
theorem probeProtocol_descend_true :
    descend probeProtocol [true]
      = Protocol.aNode (fun x => x) (Protocol.leaf false) (Protocol.leaf true) := by
  rfl

/-- **Aux 35.**  Its left child, reached by the route `[false]`, is a leaf. -/
theorem probeProtocol_descend_false :
    descend probeProtocol [false] = Protocol.leaf false := by
  rfl

/-- **Aux 36.**  The route `[true]` is a Bob route in the probe protocol. -/
theorem probeProtocol_bobPath_true : IsBobPath probeProtocol [true] :=
  ⟨trivial, trivial⟩

/-- **Aux 37.**  The route `[false]` is a Bob route in the probe protocol. -/
theorem probeProtocol_bobPath_false : IsBobPath probeProtocol [false] :=
  ⟨trivial, trivial⟩

/-- The probe token: an ordinary token stopping at suffix depth `1`, immediately
before the probe protocol's Alice query. -/
def probeToken : StoppedToken probeProtocol (Fin 2) where
  coord := 0
  kind := TokenKind.ordinary
  route := [true]
  event := StopEvent.beforeAlice
  route_bob := probeProtocol_bobPath_true
  atLeaf_at_leaf := by intro h; exact absurd h (by decide)
  beforeAlice_at_alice := by
    intro _
    exact ⟨fun x => x, Protocol.leaf false, Protocol.leaf true, probeProtocol_descend_true⟩

/-- **Non-vacuity of the stop record.**  The record is inhabited **twice** over one
protocol at one route with different kinds and different events, so `StoppedToken` is
not a subsingleton determined by `(Pstar, coord, route)` and the frozen three-way
stopping rule has content: the bonus component of a witness object is a legal positive
token (`08:949--951`), and an isolation stop is legal at the same node as an Alice
stop (`08:983--985`). -/
theorem stoppedToken_nondegenerate :
    ∃ t t' : StoppedToken probeProtocol (Fin 2),
      t.route = t'.route ∧ t.kind ≠ t'.kind ∧ t.event ≠ t'.event
        ∧ t.depth = 1 := by
  refine ⟨probeToken,
    { coord := 0
      kind := TokenKind.bonus
      route := [true]
      event := StopEvent.isolation
      route_bob := probeProtocol_bobPath_true
      atLeaf_at_leaf := by intro h; exact absurd h (by decide)
      beforeAlice_at_alice := by intro h; exact absurd h (by decide) },
    rfl, by decide, by decide, rfl⟩

/-- **Statement pole (the no-leaf clause is not automatic).**  `StoppedToken` is
inhabited with `event = atLeaf`: the probe protocol's left child *is* a leaf, and a
token routed there stops provisionally.  So `denseNoLeaf`'s first conclusion is not a
property of the record -- it is bought by the `B_cap`-hardness of the node, and fails
without it. -/
theorem stoppedToken_leaf_stop_is_inhabited :
    ∃ t : StoppedToken probeProtocol (Fin 2), t.event = StopEvent.atLeaf := by
  refine ⟨{ coord := 0
            kind := TokenKind.ordinary
            route := [false]
            event := StopEvent.atLeaf
            route_bob := probeProtocol_bobPath_false
            atLeaf_at_leaf := by
              intro _
              exact ⟨false, probeProtocol_descend_false⟩
            beforeAlice_at_alice := by intro h; exact absurd h (by decide) }, rfl⟩

/-- The probe node game: a nonconstant game that Bob alone decides, so its complexity
is exactly one bit. -/
def probeGame (_p : List Bool) : Bool → Bool → Bool := fun _ b => b

/-- **Aux 38.**  A one-bit Bob protocol computes the probe game, so `D <= 1` and the
achievable-cost set is nonempty. -/
theorem probeGame_D_le_one (p : List Bool) : D (probeGame p) ≤ 1 := by
  refine Nat.sInf_le ⟨Protocol.bNode (fun y => y) (Protocol.leaf false)
    (Protocol.leaf true), ?_, ?_⟩
  · simp [Protocol.cost]
  · intro x y
    cases y <;> rfl

/-- **Aux 39.**  The probe game is nonconstant, so `1 <= D`. -/
theorem probeGame_one_le_D (p : List Bool) : 1 ≤ D (probeGame p) := by
  refine one_le_D_of_ne (a₁ := true) (a₂ := true) (b₁ := true) (b₂ := false)
    (by simp [probeGame]) ?_
  exact ⟨1, Protocol.bNode (fun y => y) (Protocol.leaf false) (Protocol.leaf true),
    by simp [Protocol.cost], by intro x y; cases y <;> rfl⟩

/-- **Aux 40.**  Hence the probe game has complexity exactly one. -/
theorem probeGame_D_eq_one (p : List Bool) : D (probeGame p) = 1 :=
  le_antisymm (probeGame_D_le_one p) (probeGame_one_le_D p)

/-- **Joint consistency of the headline's premise bundle.**  Every hypothesis of
`denseNoLeaf` holds simultaneously at legal values -- `r = 1`, `B_cap = 1`,
`cost(P_*) = 2 = D_2 = B_cap + log_2 q_2` with the frozen `q_2 = 2^r = 2`, and a token
stopping at suffix depth `1 = r` immediately before a genuine Alice query -- and both
gated hypotheses that can fire do fire, **tightly**: the node's game has `D = 1 = B_cap`
and the node's residual subtree costs exactly `1`.  The frozen conclusion is obtained
with `route.length = r`, so the depth bound is attained rather than slack.

Without this readout the lemma could be quantified over a bundle its own premises
force empty while the module compiled green. -/
theorem denseNoLeaf_hypotheses_consistent :
    (probeProtocol.cost ≤ Dtwo 1 1)
      ∧ (probeToken.route.length ≤ 1 → 1 ≤ D (probeGame probeToken.route))
      ∧ (probeToken.route.length ≤ 1 →
          D (probeGame probeToken.route) ≤ (descend probeProtocol probeToken.route).cost)
      ∧ (1 + 1 ≤ probeToken.route.length →
          1 ≤ D (probeGame (probeToken.route.take (1 + 1))))
      ∧ (1 + 1 ≤ probeToken.route.length →
          D (probeGame (probeToken.route.take (1 + 1)))
            ≤ (descend probeProtocol (probeToken.route.take (1 + 1))).cost)
      ∧ ((probeToken.event = StopEvent.isolation
            ∨ probeToken.event = StopEvent.beforeAlice)
          ∧ probeToken.route.length = 1) := by
  have hroute : probeToken.route = [true] := rfl
  have hcost : (descend probeProtocol [true]).cost = 1 := by
    rw [probeProtocol_descend_true]
    simp [Protocol.cost]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [probeProtocol_cost, Dtwo_eq]
  · intro _
    rw [hroute]
    exact probeGame_one_le_D [true]
  · intro _
    rw [hroute, hcost, probeGame_D_eq_one]
  · intro h
    rw [hroute] at h
    simp at h
  · intro h
    rw [hroute] at h
    simp at h
  · exact ⟨Or.inr rfl, rfl⟩

/-- **The headline applied at the consistency witness.**  The frozen conclusion is
produced by `denseNoLeaf` itself at the witness above, so the lemma is asserted at a
real point and not only in the abstract. -/
theorem denseNoLeaf_at_probe :
    (probeToken.event = StopEvent.isolation
        ∨ probeToken.event = StopEvent.beforeAlice)
      ∧ probeToken.route.length ≤ 1 := by
  have hroute : probeToken.route = [true] := rfl
  refine denseNoLeaf (r := 1) (bcap := 1) probeGame probeToken (by norm_num) ?_ ?_ ?_ ?_ ?_
  · rw [probeProtocol_cost, Dtwo_eq]
  · intro _
    exact probeGame_one_le_D probeToken.route
  · intro _
    have hcost : (descend probeProtocol probeToken.route).cost = 1 := by
      rw [hroute, probeProtocol_descend_true]
      simp [Protocol.cost]
    rw [hcost, probeGame_D_eq_one]
  · intro h
    rw [hroute] at h
    simp at h
  · intro h
    rw [hroute] at h
    simp at h

/-! ## §11  Candidate B (rejected): the token carrying its own guarantee

Race evidence only.  `CountedToken` is consumed by nothing below and may not be used
to re-encode the stopped token of `08:946--959` without a fresh judged tranche. -/

/-- Candidate B: a stopped token that stores what `lem:dense-no-leaf` concludes. -/
structure CountedToken (r : ℕ) where
  /-- The suffix depth at which it stopped. -/
  depth : ℕ
  /-- Which event stopped it. -/
  event : StopEvent
  /-- The frozen *conclusion* of `08:957--958`, stored. -/
  not_leaf_stop : event ≠ StopEvent.atLeaf
  /-- The frozen *conclusion* of `08:958--959`, stored. -/
  depth_le : depth ≤ r

/-- **Candidate-B aux 1.**  The record is inhabited. -/
theorem countedToken_nonempty : Nonempty (CountedToken 3) :=
  ⟨{ depth := 2, event := StopEvent.isolation, not_leaf_stop := by decide,
     depth_le := by norm_num }⟩

/-- **Candidate-B aux 2.**  Its guarantee is available by projection, which is exactly
why it is rejected: the frozen lemma would be a field lookup. -/
theorem countedToken_depth_le {r : ℕ} (t : CountedToken r) : t.depth ≤ r := t.depth_le

/-- **Candidate-B aux 3 (the disqualifying probe).**  The record mentions no protocol,
so an inhabitant can carry a suffix depth at which the probe protocol has no node at
all: its route would have walked off a leaf.  The stored guarantee therefore describes
a token stopped in no protocol. -/
theorem countedToken_needs_no_protocol :
    ∃ t : CountedToken 5, probeProtocol.cost < t.depth := by
  refine ⟨{ depth := 5, event := StopEvent.isolation, not_leaf_stop := by decide,
            depth_le := by norm_num }, ?_⟩
  rw [probeProtocol_cost]
  norm_num

end EthInapproximability.ParameterizedNP.DenseWeightedCount
