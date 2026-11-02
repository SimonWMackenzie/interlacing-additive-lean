import EthInapproximability.ParameterizedNP.ClosureSelectSupply

/-!
# Parameterized NP route: the frontier-sum assembly (`09:1259--1266` against `09:1309--1313`)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand this tranche).
* **The exact frozen lines traced here**, in print order:
  * **`09:447--451`**, "Let `E_0` be the union of all singleton, pair, and
    small-copy covers, and put `e_0 = |E_0|`" -- the display at `09:450`, which
    makes `e_0` a **DEFINED** quantity and not a free parameter;
  * **`09:1235--1236`**, "Start one clean reference certificate in every
    coordinate outside `E_0`, each with weight one";
  * **`09:1250--1252`**, the stopping/exposure rule;
  * **`09:1253--1257`**, `d_v`, `kappa_v = 2^{r-d_v}` (`09:1255`) and
    `W_v = ` total certificate weight at `v` (`09:1257`);
  * **`09:1259--1266`, `eq:wrapper-frontier-conservation`**, display
    `09:1261--1266`, label `09:1265`: "Every first-Bob node has `kappa_v >= 2`.
    Prefix-freeness and conservation give `sum_v W_v >= q - e_0`,
    `sum_v kappa_v <= q`";
  * **`09:1268`**, `vartheta = 9/16`;
  * **`09:1309--1313`, `eq:wrapper-first-bob-light`**, display `09:1310`, label
    `09:1312`: "`W_v < vartheta kappa_v` at every first-Bob node `v`";
  * **`09:1346--1350`**, the final-node classification and the frozen names
    `K_B`, `c`, `ell`;
  * **`09:1352--1357`, `eq:wrapper-clean-count`**, with the two-line derivation
    at `09:1358--1365`.
* **Cross-anchors opened first-hand this tranche:** `09:1187--1193` (the alleged
  `(C+r-1)`-bit protocol and `09:1190`'s bracket member), `09:1219` (`A_0`),
  `09:1367--1534` (the protected-mass subsection whose `eq:wrapper-total-early-mass`
  consumes `K_B <= e_0/(1-vartheta)`), `09:1564` ("Here we used `K_B + n_T <= q`"),
  `09:1780--1781` ("We have proved `eq:wrapper-u-dense`"), and `09:260--267`
  (the `eq:wrapper-u-dense` display itself, inside `thm:first-wrapper`).
* **Reader counterpart:** none is claimed.  **Every reader coordinate in this
  record is cited against a PINNED RELEASE directory and never against the live
  worktree**, and each span names the release it actually resolves in, with that
  file's SHA-256 recomputed first-hand at these bytes.  The live tree
  `routes/parameterized-np/reader-facing/` is *not* the citation target: a
  concurrent session is editing it right now (it has already deleted
  `sections/B-bridge-details.tex` and `sections/C-effectivity-details.tex`
  there), so its line numbers are unstable, while a `versions/` directory is
  immutable by the repository contract.  This is the discipline
  `MassRedistributionTail.lean`'s §R3c applies to its own reader coordinates.
  * **Release R1 = the route's `CURRENT_VERSION`**,
    `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
    `reader-facing/sections/A-stage4-details.tex`, SHA-256
    `5b6e9ba0e271d67bf2b0525bd6d59d90c150a8170bdce29dc74da55ab39019c6`.
    `R1:370--399` is the only passage covering this material and it is running
    prose ("The complete owner--donor count is finite ... It is expanded line by
    line in the ultra-explicit companion"), with `R1:394` --
    `D_U(1; 1-delta_U, theta) >= C + r_q` -- carrying the `eq:wrapper-u-dense`
    endpoint (`09:260--267`) in the reader's own letters, rather than either
    display assembled below.  The READER-COUNTERPART rule forbids citing prose
    and forbids reusing another declaration's item, so none is cited rather than
    one invented.
  * **Release R2 = the reader-only minimal release**,
    `routes/parameterized-np/versions/2026-08-22-reader-minimal-v3/source/`
    `reader-facing/sections/A-stage4-details.tex`, SHA-256
    `77bb9f846937fc6d3b89daee2fd47f3fe6dc346ded9e5764aad6473601ea937c`.
    **Re-searched first-hand this tranche for §4a-0's new material**
    (`two-coordinate`, `final-reference`, `uniqueness`) across `R2`'s
    `reader-facing/sections/`: the single hit is `R2:828--835`, "an unsplit pair
    at capacity one is excluded as follows.  Apply the same specified-`J` clause
    to its two tagged coordinates.  It gives classical density greater than
    `9/25`, while both row supports have density at least `2^{1-b_1}`; the
    two-copy row-ladder bound is `H_*+1`."  That is the same argument in the
    reader's own Stage-4 letters, but it is **running prose inside a proof** and
    carries no number and no label, so it may not be cited as a statement.
  **The two spans live in two DIFFERENT releases, and that is the point of the
  repair.**  Up to and including the `r4` bytes this record pinned all three
  coordinates under `R2`'s hash alone.  Re-verified first-hand here, `R1:370--399`
  and `R1:394` do **not** resolve in `R2` at all -- the minimal reader cut that
  passage, and `R2` contains no occurrence of "ultra-explicit companion" -- while
  `R2:828--835` does not resolve in `R1` (`R1` contains no occurrence of "unsplit
  pair at").  The single-hash pin was therefore wrong for two of its three spans
  even though the hash itself was correct, and the live worktree copy happening
  to agree with `R2` today concealed it.  Both spans are now cited where they are
  actually readable.
  **No declaration of this module claims a reader counterpart.**

## Census first: what this tranche is allowed to conclude

The seat's target is `eq:wrapper-u-dense`.  Before writing anything the frozen
route from `09:1259` to that endpoint was censused line by line, and it is
**not** short:

* `09:1259--1266` -- `sum_v W_v >= q - e_0` and `sum_v kappa_v <= q`.  PROVED
  (`FrontierIndexing.frontier_conservation`,
  `DenseWrapperFrontier.sum_capacity_le_width`).
* `09:1268--1313` -- `W_v < vartheta kappa_v` at each first-Bob node.  PROVED per
  node, conditional on `hLocEx` (`ClosureSelectSupply`, tranche `cc-t5n`).
* `09:1315--1344` -- `lem:final-reference-uniqueness`.  PROVED as
  `DenseWrapperFrontier.wrapperFinalReferenceUniqueness`, with its `hladder`
  binder.  **Wired into this module at §4a**: consumed by pin, with all three of
  its slots discharged -- `hdistinct` (`09:1322--1324`) from the routed system's
  own `coordUnique`, `hsuffix` (`09:1341--1343`) from `hcost` through
  `RoutedCertificateSystem.RoutedSystem.final_residual_budget`, and `hladder`
  (`09:1334--1338`) from the banked
  `DenseWrapperFrontier.finalNode_twoCopy_bound` at the DEFINED ladder quantity
  `Lambda_G(2, 2x_T, y^2)`.
* `09:1325--1343` -- the proof of `lem:final-reference-uniqueness`.  **BUILT at
  §4a-0/§4a-0b** and **wired at §4a-1/§4a-2**: the `u_2 = 2` pair, the
  two-coordinate column projection at a protocol node, its `rho = 2y^2 >= y^2`
  density, the `A_0` row supply **per certificate**, the `ell = 1` ladder call's
  legality, and the budget contradiction.  `09:1334--1341`'s realization of the
  two-copy restriction inside the suffix is **derived** inside
  `certsAtNode_card_le_one_of_construction_supply` -- through the **banked**
  `SelectDischarge.bracketMember_of_blocks_and_columns` and
  `SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member`, applied to each
  other by pin inside that proof, and the **banked** `SELECT-EMBED-001` owner
  `SelectEmbedComposition.interlaceFun_reference_copy` -- and is carried by no
  binder.  **The `09:1320` pair is constructed inside that proof and appears in
  no premise of this module**; see "The structural ban on pair-shaped premises".
* `09:1346--1365` -- `eq:wrapper-clean-count`.  Banked with `hlight` and
  `hfinal` as binders; **both are now retired** (§2 and §4a-2 respectively),
  neither at the price of a premise in the shape of the conclusion nor of a
  premise quantified over a pair, and the certificate assignment is derived
  (`canonicalFinalCert`) rather than free.
* `09:1367--1510` -- `lem:early-protected-closure` and its threshold.  Partially
  banked (`WrapperMassRedistribution`, `MassRedistributionCounting`).
* `09:1512--1564` -- `eq:wrapper-total-early-mass`,
  `eq:wrapper-bob-heavy-count`, `eq:wrapper-exceptional-count`.  Banked as
  engines, each with binders.
* `09:1566--1615` -- the four-category table and
  `eq:wrapper-mass-leaves-owner`.  Banked (`MassLeavesOwner`).
* `09:1617--1699` -- `eq:wrapper-owner-threshold` through
  `eq:wrapper-good-to-good`.  Banked (`OwnerMassTransfer`,
  `OwnerIndexedTransferFamily`).
* `09:1700--1781` -- the terminal pigeonhole, call (iv), and the final
  contradiction.  **OPEN.**

**So `eq:wrapper-u-dense` is NOT asserted here, and no declaration below implies
it.**  What this tranche lands is the honest partial the seat's own instruction
names: the frontier-sum assembly proper -- `09:1259--1266`'s conservation display
set against `09:1309--1313`'s per-node light bound -- and the
`eq:wrapper-clean-count` consequence, with `hlight` retired.  The remainder
(`09:1367--1781`) is **GAP-EXPOSED** and is enumerated in the census above; the
single missing *summation* link between what is banked and `eq:wrapper-u-dense`
is `09:1700--1781`, and it is named, not assumed away.

There is no missing summation link *inside* `09:1259--1365`: every sum the frozen
derivation performs (`09:1360--1362`'s three-term comparison and `09:1364`'s
Kraft line) is discharged below or by the banked lemmas cited, and nothing in
this range is carried as an arithmetic binder.

## What this tranche does

`ClosureSelectSupply.closure_and_projected_density_of_reference_construction`
(tranche `cc-t5n`) is `09:1310`'s display **at one first-Bob node**, with the
selection binder `hselect` discharged and no capacity guard.  Its remaining
inputs are the reference construction of `09:105--123` as data, the frozen
numeric guards, and the single analytic binder `hLocEx`.  It also needs a
coordinate `i` and a route witness `hroute` placing the node on `i`'s route.

This module fires that deliverable **across the whole first-Bob column**:

* **Section 2** retires the coordinate binder.  Every frontier address is some
  started coordinate's stopping address (`FrontierIndexing.exists_coord_of_mem_frontierRoutes`),
  so `i` and `hroute` are *obtained*, never assumed, and the conclusion is the
  universally quantified `hlight` slot that the banked counting spine consumes.
* **Section 3** is the frontier-sum assembly itself: `09:1262`'s
  `sum_v W_v >= q - e_0` -- already unconditional at the canonical system through
  `FrontierIndexing.frontier_conservation` -- set against Section 2, giving
  `09:1360--1361`'s first comparison with its first-Bob column evaluated.  No
  certificate classification is needed for it, so it carries neither `cert` nor
  `hfinal`.
* **Section 4** is `eq:wrapper-clean-count` at the canonical system with
  **`hlight` retired**: `FrontierIndexing.canonical_cleanCount` fired at Section 2.
* **Section 4a-0** builds `09:1325--1343`, the proof of
  `lem:final-reference-uniqueness`: the two-coordinate column projection at a
  protocol node, its density, the `A_0` row supply, and the `ell = 1` ladder
  call against the suffix budget.
* **Section 4a-0b** is the STRUCTURAL repair of this round: the two
  **single-certificate** supplies the frozen proof actually consumes --
  `09:1325--1328`'s `A_0` floor at *one* certificate and `09:105--123`'s
  reference-copy identity at *one* coordinate per copy.  See "The structural ban
  on pair-shaped premises" below.
* **Section 4a** reads the `09:1346--1347` trichotomy off the routing as
  `canonicalKindsAt`/`canonicalFinalCert` rather than supplying it, and turns the
  uniqueness count into the weight bound the counting spine consumes.
* **Section 4a-1** is `lem:final-reference-uniqueness` (`09:1315--1344`) at a
  final node of an arbitrary routed system, with
  `DenseWrapperFrontier.wrapperFinalReferenceUniqueness` consumed by pin: its
  `hdistinct` slot proved from the routed system's `coordUnique`, its `hladder`
  slot from the banked ladder bound, and its `hsuffix` slot from `hcost` together
  with §4a-0's ladder contradiction fired at the two-copy bracket member the
  proof **assembles** from §4a-0b's two supplies.  It carries **no** premise
  quantified over certificates in pairs.
* **Section 4a-2** supplies §4a-1's construction data **from the canonical
  construction** -- the per-certificate block family, its placement, the
  per-coordinate reference-copy identity, and the node-level cover -- so the
  `hfinal` slot is obtained with no premise in the shape of the conclusion and no
  premise quantified over a pair.

### The structural ban on pair-shaped premises

`lem:final-reference-uniqueness` argues by contradiction *from a pair*, and three
successive rounds tried to state the inputs its proof consumes as premises
quantified over pairs of certificates at one node: a free `residual` family, then
`hrealize` (`Lambda_G(2, 2x_T, y^2) <= cost(subtree at v)`), then a pair-local
existential `hpair` producing the `09:1325--1332` bracket member.  All three are
dead for one reason that is independent of what they say.
`pair_premise_is_vacuous_at_a_thin_node` (Battery 10) proves that the conclusion
`(certsAtNode S v).card <= 1` implies **every** premise of that shape, for every
predicate without exception; and a pair premise strong enough to close the
two-certificate case supplies the converse.  So the whole class is
conclusion-equivalent, and exhibiting an inhabitant for a member of it certifies
nothing, because Battery 10 exhibits one for all of them simultaneously.

**Therefore no declaration of this module carries a premise quantified over two
certificates or over certificate pairs.**  What the frozen proof consumes enters
as §4a-0b's two single-certificate supplies plus node-level data, and the pair is
*constructed inside* `certsAtNode_card_le_one_of_construction_supply`, exactly
where `09:1320` puts it.
* **Section 4b** is `eq:wrapper-clean-count` with **`hfinal` retired too**, at
  the derived classification, carrying only the construction's own final-node
  block family (`09:1325--1328`) in its place.

### The two-kappa trap

`kappa_v` takes exactly two kinds of value on the frozen frontier, and the whole
assembly turns on keeping them apart.  At a first-Bob node `09:1259` gives
`kappa_v >= 2`, so `vartheta kappa_v >= 9/8 > 1` and a weight-one clean
certificate can sit under the light bound.  At a **final** Alice node
`09:1250--1252` forces `d_v = r` and hence `kappa_v = 1`, where
`vartheta kappa_v = 9/16 < 1`: the very same display would then *forbid* the
clean certificate that `09:1346--1347` puts there, and `09:1262`'s conservation
would collapse.  Quantifying `hlight` over the whole frontier instead of over
`bobNodes` is therefore not a harmless strengthening -- it is inconsistent with
the frozen final-node classification.  Section 5's
`two_kappa_trap_at_the_final_nodes` is the check, and Section 2's conclusion is
quantified over `bobNodes` and no wider.

### The `vartheta` twins

`vartheta = 9/16` is declared twice in this development, from two different
frozen displays: `DenseWrapperFrontier.vartheta` (`09:1268`, the frontier weight
threshold, which is the one `09:1310` and `09:1353` use) and
`ParameterSchedule.vartheta` (`eq:terminal-uniform-bounds`, `06:718`, a schedule
constant).  Everything below consumes the **`09:1268` twin**, inherited through
`ClosureSelectSupply` and `FrontierIndexing`; `vartheta_twins_agree` records
that the two are numerically the same real, so a later tranche cannot silently
substitute one for the other and cannot claim they disagree.

### `e_0` is evaluated, never assigned

`09:450` **defines** `e_0 = |E_0|`.  The banked
`FrontierIndexing.frontier_conservation` takes the frozen count as the binder
`hcoord : q - e_0 <= |Coord|`; at the started carrier
`SelectEmbedComposition.StartedCoord E_0` of `09:1235--1236` that binder is a
*theorem*, because `SelectEmbedComposition.card_startedCoord` evaluates
`|StartedCoord E_0| = q - |E_0|`.  So every statement below writes `e_0` as
`(E_0.card : ℝ)` -- the definitional chain evaluated -- and `hcoord` is
discharged rather than carried.  No numeral is chosen for `e_0`, for `vartheta`,
for `u_kappa`, for `rho` or for `A_0`; all arrive through the banked chain.

### What is NOT discharged

* **`hLocEx`** -- `thm:certified-localized-extension` (`A:109--146`), the place
  **EXPANDER-001** would enter -- survives as the single explicit named analytic
  binder, now quantified over the first-Bob nodes it is applied at, and
  otherwise byte-identical in re-association to `ClosureSelectSupply`'s.  It is
  never an `axiom`, never a premise-bundle field, never an opaque certificate.
  `hE1`, `hE2` and `htcert` likewise survive, as do `halleged` and `hcost`.
* The final-node **block family** `Bfin` of `09:1325--1328` -- one G-row block per
  routed certificate, with `hBfin` saying it realizes that certificate's own
  reference-row count and `hblockFin` placing it inside `RoutingDynamics.rowsAt`
  under the **existing** `plc` -- is the whole of what §4a-2 and §4b carry in place
  of the former `hfinal`.  It is construction data of exactly the kind Section 2
  already demands of the first-Bob column (`B`, `hB`, `plc`, `hblock`, `hplace`),
  it mentions no cost, complexity, density or weight, **it is quantified over one
  certificate at a time**, and `09:1325--1328` is what floors it:
  `finalNode_cert_rows_ge_initialRefRows` reads `A_0` off the routed system at
  `d_v = r` and `finalNode_block_meets_twoCopy_floor` puts it in the bracket's
  units.  Its joint, nondegenerate satisfiability at legal parameters is Battery
  11c over Battery 11b, composed and **written down at the construction point**
  by Battery 11d (LANE-GATE 3); its *canonical* inhabitation is the
  inherited REGISTERED and DEFERRED obligation and is not claimed.
* **`cidx`, `hcidx`, `hE0`** in §4a-1 -- the outer coordinate a certificate
  descends from, injectively and outside `E_0`.  At the canonical system all
  three are **theorems** (`SelectEmbedComposition.startedIdx_injective`,
  `startedIdx_notMem_E0`, the `09:1235--1236` start rule), so nothing survives
  there; they are binders only at the generality of an arbitrary routed system.
* **What is no longer carried.**  `09:1334--1341`'s realization of the two-copy
  restriction inside the suffix is **derived**, not assumed: §4a-2's own proof
  builds the bracket member from §4a-0's supplies through the banked
  `SelectDischarge.bracketMember_of_blocks_and_columns` and fires the banked
  `SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member` at it, both by pin
  and with **no declaration of this module between them**.  That composition's
  `iotaA`/`iotaB`/`hgame` inputs are supplied at §4a-2 by the banked
  column section `SelectEmbedComposition.ambientColumn` and the banked
  **`SELECT-EMBED-001`** owner
  `SelectEmbedComposition.interlaceFun_reference_copy` (`09:105--123`) -- that
  owner is a **proved theorem of the banked module, not a live STOP**, and the
  first-Bob side already consumes it at
  `SelectEmbedComposition.hselect_of_reference_construction`.  Both the
  predecessor round's free `residual` family and its successor `hrealize` --
  each of which was equivalent to the conclusion under the final-node budget --
  are **gone**; the corresponding caveat on the banked
  `RoutedCertificateSystem.RoutedSystem.owner_injOn_of_ladder` is untouched by
  this tranche and stays as that module records it.
* **`hfinal`** itself is RETIRED at §4b.  It survives only as an explicit
  parameter of the older, more general
  `canonical_cleanCount_of_reference_construction`, which is kept for consumers
  that bound the final-node weight by other means.
* Everything in `09:1367--1781`, per the header census.

## Statement-content and dependency notes

* **Widths.** `q` is FREE throughout: `09:105`'s `q = 2^r` enters only where the
  banked `canonical_cleanCount` demands it, as its own binder `hq`.  The second
  interlace width `Q` does not occur.
* **Carriers.** `Coord := StartedCoord E_0` (`09:1235--1236`); `m_G` is read at
  `Fintype.card X` (`09:113--116`); `A_0` is
  `initialRefRows (xTdepth bT) (Fintype.card X)`, the reified `09:1219`.
* **Node-indexed data.** `09:1291--1296` trims each selected certificate "to the
  row density `kappa_v x_T`", a threshold that depends on the node, so the trims
  `B` and the placement `plc` are supplied as **families over the frontier
  node**.  Collapsing them to one node-free choice would be an over-strong
  hypothesis: no single trim can meet the floor at every capacity.
* **Imports.** The sole import is `ClosureSelectSupply`, whose transitive closure
  already contains `FrontierIndexing`, `DenseWrapperFrontier`,
  `RoutedCertificateSystem`, `SelectDischarge`, `SelectEmbedComposition`,
  `TerminalResidualComparison`, `TranscriptLevelSuccessors`,
  `WrapperProjectionCovers` and `ParameterSchedule`.
  **Import direction, verified first-hand this tranche:** this module is the
  importer and every name pinned below sits upstream of it --
  `FrontierSumAssembly.lean:1` imports `ClosureSelectSupply`, whose chain
  `ClosureSelectSupply.lean:1 -> FirstBobLightClosure.lean:1 ->
  AliceOnlyHdensSupply.lean:1 -> FrontierProjectionSupply.lean:1 ->
  FrontierBundleConstruction.lean:1 -> SelectEmbedComposition.lean:1 ->
  SelectDischarge.lean:1` reaches `SelectDischarge`, and continues through
  `FirstBobLightDichotomy.lean:1 -> ... -> TerminalTwoStream.lean:1 ->
  TerminalStateRealization.lean:1 -> TwoStreamState.lean:1` to
  `WrapperProjectionCovers`.  No banked module is edited and no downstream name
  is pinned from upstream.
  `LegacyNPCC.Stage12` is **not** in that closure, so the cited AGHP
  balanced-family axiom is unreachable from every declaration here.  No `axiom`,
  no opaque certificate, no premise bundle, no new structure, `abbrev` or
  `instance`.  **§4a-0 declares no `def` at all**: `09:1331`'s two-coordinate
  column projection is the banked `RoutedCertificateSystem.nodeProjection` at the
  frozen pair `{i,j}`, consumed by pin, and no alias or canonical specialization
  of it is introduced.  The three `def`s in the module are the inherited ones,
  all *carriers of frozen content rather than new hypotheses*: `certsAtNode` (the
  `09:1315--1319` certificate set at a node), `canonicalKindsAt` (the derived
  kinds there), and `canonicalFinalCert` (the `09:1346--1347` trichotomy read off
  the routing).  None of them takes a complexity, density or robustness
  conclusion as data.

## Canonical inhabitation, and full-bundle satisfiability

**Canonical inhabitation: REGISTERED and DEFERRED, inherited unchanged.**  This
module declares no new type, so it opens no new inhabitation obligation.  The
inherited one cannot be discharged: the paper's own instance of every statement
below is a function of the **alleged** protocol of `09:1187--1193`, whose
non-existence is the conclusion of the whole argument, so the frozen paper
exhibits no routed instance and no probe here claims to supply one.

**Full-bundle satisfiability IS now claimed, and only in the weaker
NON-FIDELITY sense LANE-GATE 3 asks for.**  Battery 11c
(`finalBlock_bundle_joint_inhabitant`) exhibits a single choice of `Gmat`,
`iota_R`, `g`, `plc` and `Bfin` satisfying `hsub`, `hBfin`, `hblockFin` and
`hplace` **together**, over the coordinate slab `R` of `09:1235--1236`, with `q`,
`r`, `A_0`, `E_0` and both carriers left free -- so the bundle is not inhabited
only at degenerate or cardinality-contradictory values.  Its witness is
nondegenerate by construction and the statement pins that: `Bfin` is the
certificate's **own** routed row set (not `Finset.univ`, the weak Battery 11a
choice) and `plc` is pinned outright to `09:1235--1236`'s re-tagging
`plc v j a = (startedIdx j, a.2)`.

**That re-tagging is NOT claimed to differ from the identity on the slab.**
`hslab` forces `a.1 = startedIdx j` for every row of `R j`, so on exactly the
rows `hblockFin` is exercised at, `plc v j a = a`.  What the last conjunct buys
is the *pin* -- a would-be trivial witness has no freedom at all in that
component -- not a nonidentity claim; off the slab the re-tagging is what carries
a row into the started coordinate's copy.

Battery 11b (`finalBlock_bundle_inputs_are_legal`) supplies the **slab family**
that receipt runs over, at legal nondegenerate parameters: its exact `|W|` row
count, the `09:1233--1235` retention `A_r <= |R j|`, and the `09:1235--1236`
tagging `x.1 = startedIdx j`.  It does **not** restate the `CompletedNoBob`
frame: `lem:wrapper-no-bob-completion` (`09:1195--1213`, with the completed
Alice ladder constructed at `09:1203--1207`) is the banked
`RoutingDynamics.completedNoBob_aliceLadder`, and every consumer invokes that
owner **directly by pin** rather than through a republished conjunct.

Battery 11d (`finalBlock_bundle_joint_inhabitant_at_the_construction_point`) is
the one that **composes** them: it applies the banked frame owner and 11b's slab
family, feeds both to 11c, substitutes `q = 2^r` (`09:105`) and `A_0` in its
evaluated closed form `initialRefRows (xTdepth bT) |W|` (`09:1219`), and adds the
four nondegeneracy conjuncts 11b does not establish on its own (`1 <= A_0`,
`StartedCoord E_0` inhabited, each slab nonempty, each slab a proper subset).
Without it the composition would be *available* and *unwritten*, which is not a
LANE-GATE 3 receipt.
Neither battery is the paper's own instance, and none discharges the deferred
canonical-inhabitation obligation.  Sections 1 and 5's checks are general and
evaluate no schedule parameter.
-/

namespace EthInapproximability.ParameterizedNP.FrontierSumAssembly

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply
open EthInapproximability.ParameterizedNP.SelectEmbedComposition
open EthInapproximability.ParameterizedNP.FirstBobLightClosure
open EthInapproximability.ParameterizedNP.ClosureSelectSupply

/-! ## §1  The started-carrier census (`09:450` with `09:1235--1236`)

`e_0` is a DEFINED quantity and the frozen conservation count is a theorem of the
started carrier, not a binder.  Hoisted ahead of the assembly because Sections 3
and 4 consume it; it is a general check in its own right and is counted with the
battery. -/

section Census

/-- **Battery 1 / `e_0` is evaluated, never assigned.**

`09:450` **defines** `e_0 = |E_0|`, and `09:1235--1236` starts one certificate in
every coordinate outside `E_0`.  At the started carrier those two frozen lines
force the conservation count exactly: `|StartedCoord E_0| = q - |E_0|`, as a real
equation rather than an inequality.

This is what lets Sections 3 and 4 discharge the banked
`FrontierIndexing.frontier_conservation`'s `hcoord` binder instead of carrying
it.  The natural-number subtraction of
`SelectEmbedComposition.card_startedCoord` is genuinely converted here: the
conversion needs `|E_0| <= q`, which is a theorem of `E_0 : Finset (Fin q)` and
not an assumption.

General in `q` and `E_0`; nothing is chosen. -/
theorem startedCoord_census_evaluates_e_zero {q : ℕ} (E0 : Finset (Fin q)) :
    (q : ℝ) - (E0.card : ℝ) = ((Fintype.card (StartedCoord E0) : ℕ) : ℝ) := by
  have hle : E0.card ≤ q := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ E0
  rw [card_startedCoord E0, Nat.cast_sub hle]

end Census

/-! ## §2  `eq:wrapper-first-bob-light` across the whole first-Bob column

`09:1310`'s display fired at every first-Bob node of the canonical routed
system, with the per-node coordinate binder retired. -/

section LightColumn

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) at EVERY first-Bob node.**

The banked per-node supply
`ClosureSelectSupply.closure_and_projected_density_of_reference_construction`
needs a started coordinate `i` and a route witness placing the node on `i`'s
stopping set.  Neither is available uniformly in a quantified statement, and
neither has to be: `FrontierIndexing.exists_coord_of_mem_frontierRoutes` says
every frontier address *is* some coordinate's stopping address, so both are
**obtained** inside the proof.  What comes out is exactly the `hlight` slot of
the banked counting spine (`DenseWrapperFrontier.wrapperCleanCount`,
`FrontierIndexing.canonical_cleanCount`,
`MassRedistributionCounting.bobCapacity_le_of_cleanCount`): the frozen display
at `vartheta` times the frontier capacity, quantified over `bobNodes`.

**Quantified over `bobNodes` and no wider.**  See
`two_kappa_trap_at_the_final_nodes`: at a final Alice node `kappa_v = 1` and the
same inequality would forbid the weight-one clean certificate `09:1346--1347`
puts there.  The frozen guard `hv` in the banked per-node supply is what keeps
the two node kinds apart, and it is preserved.

**The trims and the placement are node-indexed** because `09:1293--1296`'s floor
is `ceil(m_G . kappa_v x_T)`, a per-node threshold.  `hplace` is quantified over
the node only because `plc` is a family: the entry identity it records is
`09:105--123`'s, a property of the construction rather than of the node.
`hcover` is node-free outright, `09:442--444`'s covers likewise being a property
of the construction.

*Why the trivial witness fails.*  The conclusion is not existential, so the
question is whether it is tight and whether it can fail at all.  It is tight:
the banked `TranscriptLevelJoin.splitAudit_is_not_light` exhibits a routed
system with a first-Bob node at `W_v = 9 = vartheta . 16`, i.e. exactly on the
boundary, so no smaller multiple of `kappa_v` would do and this is not a slack
estimate.  That same instance falsifies the **strict** frozen display of
`09:1310`, which is why the banked per-node supply's hypotheses must exclude it
rather than hold everywhere; and `W_v` is not bounded by `vartheta kappa_v` as a
matter of arithmetic, since the banked `FrontierIndexing.frontierWeight_le_card`
is the only unconditional bound available and it is the certificate count, not
the capacity.  So no arithmetic tautology is being recorded.

**The frozen display is strict; this slot is not.**  `09:1310` prints
`W_v < vartheta kappa_v` and the banked per-node supply proves exactly that; the
non-strict form here is the weakening the banked counting spine's `hlight` slot
takes, and nothing downstream uses the strictness.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet
`Yc`, the Alice carrier `X`, in `q`, `r`, `b_T`, `k_ref`, `C`, `t_cert`, `E_0`,
the bracket member, the retained column set, the trim and placement families,
and the real parameters `x_U` and `theta`. -/
theorem canonical_firstBob_light_of_reference_construction {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ C - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [c])).cost)
    {Scol : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (B : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → Finset X)
    (hB : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B v j).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblock : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B v j, plc v j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c) :
    ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ vartheta
          * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  classical
  intro v hv
  have hvb : (canonicalSystem hcomp hR).firstBob v = true := by
    simpa [WrapperFrontier.bobNodes, RoutedSystem.toWrapperFrontier] using hv
  obtain ⟨i, hroute⟩ := exists_coord_of_mem_frontierRoutes v.property
  have h := (closure_and_projected_density_of_reference_construction Nmat Gmat ιR hsub
    halleged hcomp hR v hvb i hroute hmem hk hq4 hX hYc hθ0 hθ1 hC hgate hbase htcert
    hE1 hE2 hcost (hLocEx v hvb) hcover (B v) (hB v) (plc v) (hblock v) (hplace v)).1
  exact le_of_lt h

end LightColumn

/-! ## §3  The frontier-sum assembly (`09:1259--1266` against `09:1309--1313`)

`09:1262`'s conservation set against the first-Bob column of Section 2: the
frozen comparison of `09:1360--1361`, with its `vartheta K_B` term produced
rather than assumed. -/

section FrontierSum

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`09:1359--1361`'s first comparison, at the canonical routed system.**

`q - e_0 <= vartheta K_B + sum over final Alice nodes of W_v`.

This is the frontier-sum assembly the seat names.  Both of its inputs are
discharged, not assumed:

* the left-hand side is `eq:wrapper-frontier-conservation`'s first clause
  (`09:1262`), unconditional at the canonical system through
  `FrontierIndexing.frontier_conservation`, whose frozen count binder is
  evaluated here by `SelectEmbedComposition.card_startedCoord` -- `e_0` is
  `09:450`'s DEFINED `|E_0|`, so the binder is a theorem of the started carrier
  and not a hypothesis;
* the first-Bob column is Section 2, i.e. `eq:wrapper-first-bob-light`
  (`09:1310`) fired at every first-Bob node, whose only surviving analytic input
  is `hLocEx`.

**No certificate classification enters.**  The frozen derivation replaces the
final-node sum by `c + ell/2` using `09:1346--1350`, which needs
`lem:final-reference-uniqueness`; that replacement is Section 4's business.
This statement is deliberately upstream of it, so it carries no `cert`
assignment and no `hfinal`, and is therefore available to any consumer that
bounds the final-node weight differently.

*Why the trivial witness fails.*  Not existential; and not vacuous either way.
With no first-Bob node the right-hand side is the bare final-node sum and the
statement still has content (it is then `09:1262` itself); with no started
coordinate the left-hand side is `q - e_0 <= 0`, and the banked
`FrontierIndexing.conservation_needs_the_coordinate_count` shows that is exactly
where the frozen count is load-bearing.

General in the same data as Section 2. -/
theorem canonical_frontierSum_against_the_light_bound {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ C - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [c])).cost)
    {Scol : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (B : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → Finset X)
    (hB : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B v j).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblock : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B v j, plc v j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c) :
    (q : ℝ) - (E0.card : ℝ)
      ≤ vartheta * (canonicalSystem hcomp hR).toWrapperFrontier.bobCapacity
        + ∑ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
            frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v := by
  classical
  have hcoord := startedCoord_census_evaluates_e_zero (q := q) E0
  have hcons := frontier_conservation P R (initialRefRows (xTdepth bT) (Fintype.card X)) r
    (q := (q : ℝ)) (e0 := (E0.card : ℝ)) hcoord.le
  have hsplit := (canonicalSystem hcomp hR).toWrapperFrontier.sum_bobNodes_add_sum_finalNodes
    (frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
  have hbob : ∑ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ vartheta * (canonicalSystem hcomp hR).toWrapperFrontier.bobCapacity := by
    rw [WrapperFrontier.bobCapacity, Finset.mul_sum]
    exact Finset.sum_le_sum
      (canonical_firstBob_light_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR
        hmem hk hq4 hX hYc hθ0 hθ1 hC hgate hbase htcert hE1 hE2 hcost hLocEx hcover
        B hB plc hblock hplace)
  linarith [hcons, hsplit, hbob]

end FrontierSum

/-! ## §4a  `lem:final-reference-uniqueness` wired: the `hfinal` slot supplied
(`09:1315--1344` into `09:1346--1350`)

The frozen text does not *assume* the final-node classification; it **derives** it.
`lem:final-reference-uniqueness` (`09:1315--1319`) says a final Alice-frontier node
"contains at most one reference certificate, whether clean or split", and the
sentence at `09:1346--1347` reads that count off as the trichotomy "one clean
certificate, one half-weight descendant of a split certificate, or none".  Section
4's `hfinal` binder is exactly that trichotomy in weight form, and this section
supplies it.

**What is consumed by pin.**  `DenseWrapperFrontier.wrapperFinalReferenceUniqueness`
(`DenseWrapperFrontier.lean:1312`, `09:1315--1344`) is applied verbatim at its own
interface, and re-proved nowhere; so is
`RoutedCertificateSystem.RoutedSystem.final_residual_budget`
(`RoutedCertificateSystem.lean:1005`, `09:1341--1343` on the protocol object), which
turns the banked lemma's `hsuffix` slot into a consequence of `hcost`.

**What becomes a theorem.**  The banked lemma's `hdistinct` slot -- `09:1322--1324`,
"a fixed protocol node receives at most one descendant of any initial certificate" --
is the `coordUnique` field of every `RoutedSystem`, so `certsAtNode_coord_ne` proves
it rather than assuming it.

**What becomes a theorem in §4a-0, and is the point of this tranche.**  The frozen
`09:1329--1340` is now *built*, not assumed:

* `09:1329--1330`, "the pair `{i,j}` avoids the `u_2 = 2` small-copy cover":
  `pair_card_eq_smallCopyWidth_two` identifies a two-element coordinate set with the
  frozen width `u_2 = smallCopyWidth (2^1)` of `09:438`, and the two coordinates are
  outside `E_0` by `09:1235--1236`'s start rule;
* `09:1330--1331`, "no Bob query has occurred on the route to this node": the
  banked `RoutedCertificateSystem.nodeProjection_of_isAlicePath` at the frontier
  address, consumed inside
  `SelectDischarge.parent_projection_dense_at_frontier_node` and restated nowhere;
* `09:1331--1332`, "its two-coordinate column projection consequently still has
  density at least `rho = 2y^2`, and hence at least `y^2`":
  `twoCoordPair_projection_retains_y_sq`, which calls the banked
  `SelectDischarge.parent_projection_dense_at_frontier_node` directly at `l = 1`
  (no specialization of it is declared) and adds only the frozen weakening, from
  `WrapperProjectionCovers.rhoSmall_eq_two_y_sq` (`rho = 2y^2 = 18/25`, `09:436`);
* `09:1334--1338`, the `lem:certified-row-ladder` call at
  `(M,H,x,z,ell) = (G, C-1, x_T, y, 1)`: the banked
  `DenseWrapperFrontier.finalNode_twoCopy_bound`, consumed by pin, whose hypotheses
  are `09:1339`'s `lem:wrapper-reference` base (`hbase`) and `C >= 3`, and whose
  legality `2 x_T <= t_ref x_T <= 1` (`09:1340`) is
  `twoCopy_row_legality_of_gate` from the schedule gate;
* `09:1325--1328`, "at a final node `d_v = r`, so each certificate contains at least
  `A_0 = ceil(2 x_T m_G)` rows of its copy of `G`":
  `finalNode_cert_rows_ge_initialRefRows` from the routed certificate's own
  `rows_floor`, with `initialRefRows_is_the_twoCopy_block_floor` identifying `A_0`
  with the two-copy bracket's per-block row floor at row density `2 x_T`;
* `09:1341--1343`, the budget contradiction: `finalPair_ladder_contradiction`.

**What survives as a binder, and it is no longer the conclusion's shape.**  Nothing
about the *realization* survives.  The three localization inputs `iotaA`, `iotaB`
and `hgame` that the banked
`SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member` demands are supplied
at §4a-2, inside the proof that fires it, from the canonical construction:
`iotaB` and its `hcol` by the banked column section
`SelectEmbedComposition.ambientColumn`/`routeCols_ambientColumn`, `iotaA` and its
`hrow` by the construction's placement `plc` composed with
`SelectDischarge.routeRows_of_mem_rowsAt`, and `hgame` by the **banked**
`SELECT-EMBED-001` owner `SelectEmbedComposition.interlaceFun_reference_copy`
(`09:105--123`), which is a proved theorem and **not a live STOP** -- the first-Bob
side consumes the same owner at
`SelectEmbedComposition.hselect_of_reference_construction`.  What §4a-2 does carry
is the final-node block family of `09:1325--1328` (`Bfin`, `hBfin`, `hblockFin`),
construction data of the same kind Section 2 already demands.

This is the repair of **three** successive defects, and the third repair is
structural rather than another attempt at wording.  The first predecessor round
stated `hladder` over a **free** `residual` family capped by the node's own suffix
cost, so it carried no ladder call at all.  The second replaced it by `hrealize`,
`Lambda_G(2, 2x_T, y^2) <= cost(subtree at v)` per distinct-coordinate pair -- which
under the same declaration's `hcost` and the banked ladder bound is **false at every
such pair**, hence equivalent to the conclusion it was meant to establish.  The
third replaced *that* by `hpair`, a pair-local **existential** producing the
`09:1325--1332` bracket member, and it died the same death for a reason that has
nothing to do with what it said: by `pair_premise_is_vacuous_at_a_thin_node` the
conclusion `(certsAtNode S v).card <= 1` implies **every** premise quantified over
distinct-coordinate pairs of certificates at `v`, while any such premise strong
enough to close the two-certificate case implies the conclusion.  So the class is
uniformly conclusion-equivalent and no member of it can ever be admitted.

**The structural ban, and what replaced the class.**  No declaration of this
module carries a premise quantified over two certificates or over certificate
pairs.  The frozen proof's inputs enter as the two SINGLE-certificate supplies of
§4a-0b -- `finalNode_block_meets_twoCopy_floor` (`09:1325--1328`, one certificate)
and `twoCopy_hgame_of_perCoordinate_placement` (`09:105--123`, one coordinate per
copy) -- together with node-level data (`Scol`, `hcover`) and per-certificate
placement (`plc`, `hrowloc`/`hblockFin`).
`certsAtNode_card_le_one_of_construction_supply` instantiates the supplies
**twice inside its own proof**, which is where `09:1320`'s "Suppose a final node
contained two certificates" puts the pair.  Here the residual quantity is the
**DEFINED** `Lambda_G(2, 2x_T, y^2)` -- the `ell = 1` ladder output of `A:158` at
the frozen substitution of `09:1336--1337` -- `C <= Lambda_G(2, 2x_T, y^2)` is a
*theorem* (`finalNode_twoCopy_bound`), and no hypothesis about a cost is carried
anywhere.

**Consistency (LANE-GATE 3).**  Every surviving premise is a total statement
about the construction, so `pair_premise_is_vacuous_at_a_thin_node` has nothing to
act on.  The bundle is not merely field-by-field inhabited: Battery 11c
(`finalBlock_bundle_joint_inhabitant`) exhibits one choice of `Gmat`, `iota_R`,
`g`, `plc` and `Bfin` satisfying `hsub`, `hBfin`, `hblockFin` and `hplace`
**jointly** and **nondegenerately** -- `Bfin` the certificate's own routed row set
rather than `Finset.univ`, `plc` pinned to `09:1235--1236`'s re-tagging (which
coincides with the identity on the slab, and is a pin rather than a nonidentity
claim) -- with every schedule parameter left free, and Battery 11b
(`finalBlock_bundle_inputs_are_legal`) exhibits the `09:1235--1236` slab family
and its `09:1233--1235` retention that receipt runs over.  Battery 11d
(`finalBlock_bundle_joint_inhabitant_at_the_construction_point`) composes the two
at the construction point, at `q = 2^r` and the evaluated `A_0`, and rules out
the degeneracies.  The `CompletedNoBob` frame of `lem:wrapper-no-bob-completion`
(`09:1195--1213`) is not republished there: it is the banked
`RoutingDynamics.completedNoBob_aliceLadder`, consumed by pin.
Battery 11a (`Bfin := fun _ => Finset.univ`) is retained as the explicitly WEAK
half and is no longer offered as a consistency receipt for anything. -/

/-! ### §4a-0  The two-coordinate column projection at a protocol node
(`09:1325--1343`)

`lem:final-reference-uniqueness`'s proof works at a **pair** of initial outer
coordinates.  The carrier is the banked
`RoutedCertificateSystem.nodeProjection` -- the projection of a node's retained
column set to a coordinate set -- consumed by pin and re-authored nowhere; what this
subsection adds is the frozen `u_2 = 2` instance of it and the density the frozen
argument reads off, then the `ell = 1` ladder call and the budget contradiction the
frozen proof closes with. -/

section TwoCoordinateProjection

variable {q : ℕ}

/-- **`09:1330` with `09:438`: a two-element coordinate set is a small-copy cover
width.**

"The pair `{i,j}` avoids the `u_2 = 2` small-copy cover."  `u_2` is the banked
`WrapperProjectionCovers.smallCopyWidth 2 = smallCopyWidth (2^1)`, and this records
that the frozen *pair* is exactly a set of that width -- which is what lets the
`l = 1` member of `09:442--445`'s cover family be cited at `{i,j}`.  The frozen
width is consumed, never re-derived from `09:438`.  General in `q` and the pair. -/
theorem pair_card_eq_smallCopyWidth_two {i j : Fin q} (hij : i ≠ j) :
    ({i, j} : Finset (Fin q)).card = smallCopyWidth (2 ^ 1) := by
  rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  rfl

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {X Z : Type*}

/-! **The carrier is banked, and is consumed by pin.**  `09:1331`'s "its
two-coordinate column projection" is the banked
`RoutedCertificateSystem.nodeProjection P S J p` -- the projection of a node's
retained column set to a coordinate set -- at the frozen pair `J = {i,j}`.  That
module's atlas card records that "the per-node column set has exactly one
definition here", so **no alias, wrapper or specialization of it is declared
below**: every statement of this subsection is written directly over
`nodeProjection P S {i, j} (Sys.node v)`, and `09:1330--1331`'s "no Bob query has
occurred on the route to this node" is the banked `nodeProjection_of_isAlicePath`,
invoked *inside* the banked `SelectDischarge.parent_projection_dense_at_frontier_node`
rather than restated here.  What this subsection adds is the frozen *content* at
that pair: the `u_2 = 2` legality, the two densities, the `A_0` row supply, the
`ell = 1` ladder call's legality and the budget contradiction. -/


/-- **`09:1329--1332` in full, PROVED: the two-coordinate projection retains `y^2`.**

"The pair `{i,j}` avoids the `u_2 = 2` small-copy cover, and no Bob query has
occurred on the route to this node.  Its two-coordinate column projection
consequently still has density at least `rho = 2y^2`, and hence at least `y^2`."

**The `rho` half is not restated.**  The banked
`SelectDischarge.parent_projection_dense_at_frontier_node` (`09:1287--1289`, the
parent half of the projection-at-a-node lemma) is called **directly** at its `l = 1`
member, where `pair_card_eq_smallCopyWidth_two` identifies the frozen width
`smallCopyWidth (2^1) = u_2 = 2` of `09:438`; that banked lemma already discharges
`09:1330--1331`'s "no Bob query has occurred on the route to this node" internally,
through `RoutedCertificateSystem.nodeProjection_of_isAlicePath`.  No specialization
of it is declared here.  The two coordinates avoid `E_0` because `09:1235--1236`
starts certificates only outside it, which is why `hi` and `hj` are supplied by the
started carrier at every call site and never assumed of arbitrary coordinates.
`rhoSmall` is the banked `09:436` constant and is neither evaluated nor restated.

**What is fresh here is only the frozen weakening** `rho = 2y^2 >= y^2` at the
DEFINED `y = 3/5` of `09:436`.  At a **final** node this is where the frozen
argument stops: unlike the first-Bob branch of `09:1290`, no Bob child is taken,
because `09:1330` records that no Bob query has occurred.  So the banked
`RoutingDynamics.denserBobChild_retains_y_sq` is deliberately *not* invoked here,
and the factor two is spent on the weakening rather than on a halving.  `y = 3/5`
is not a chosen numeral: `09:436`'s display `rho = 2y^2 = 18/25` fixes it, and
`FirstBobLightDichotomy.wrapper_y_is_pinned_by_rho` proves the uniqueness direction
on the nonnegative reals; `WrapperProjectionCovers.rhoSmall_eq_two_y_sq` supplies
the evaluation and is consumed, not restated.

*Why this is not vacuous.*  The conclusion is an inequality on a real density and it
fails without `hi`/`hj`: a pair meeting the cover may be poor, which is exactly what
`PoorProjection` says and what `09:447--451`'s `E_0` is for.

General in the routed system, the node, the retained set, `E_0`, the cover index and
the pair. -/
theorem twoCoordPair_projection_retains_y_sq {Coord ι V : Type*}
    {P : Protocol X (Fin q → Yc) Z} {r A0 : ℕ}
    (Sys : RoutedSystem P Coord ι V r A0) (v : V) (S : Finset (Fin q → Yc))
    {E0 : Finset (Fin q)} {k : ℕ} {i j : Fin q}
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (hk : 2 ≤ k) (hij : i ≠ j) (hi : i ∉ E0) (hj : j ∉ E0) :
    ((3 : ℝ) / 5) ^ 2 * (Fintype.card Yc : ℝ) ^ (2 : ℕ)
      ≤ ((nodeProjection P S {i, j} (Sys.node v)).card : ℝ) := by
  have hcard : ({i, j} : Finset (Fin q)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  have hrho := SelectDischarge.parent_projection_dense_at_frontier_node Sys v S hcover
    (l := 1) (Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩)
    (pair_card_eq_smallCopyWidth_two hij)
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ hi
      · exact (Finset.mem_singleton.mp h) ▸ hj)
  rw [hcard] at hrho
  have hval : (2 : ℝ) * ((3 : ℝ) / 5) ^ 2 = rhoSmall := rhoSmall_eq_two_y_sq
  have hpow : (0 : ℝ) ≤ (Fintype.card Yc : ℝ) ^ (2 : ℕ) := by positivity
  nlinarith [hrho, hpow]

/-- **Battery B (the two-coordinate density is a genuine weakening).**

`rho = 18/25` is strictly above `y^2 = 9/25`, so `09:1332`'s "and hence at least
`y^2`" is a real step down with room to spare and not an equality dressed as an
inequality.  Recorded on the frozen constants themselves; nothing is chosen. -/
theorem twoCoord_rho_exceeds_y_sq :
    ((3 : ℝ) / 5) ^ 2 < rhoSmall ∧ rhoSmall = 2 * ((3 : ℝ) / 5) ^ 2 := by
  refine ⟨by norm_num [rhoSmall], (rhoSmall_eq_two_y_sq).symm⟩

/-- **`09:1331--1332` in the bracket family's own units.**

`def:bracket`'s column clause is stated over `Fin pc -> Cl`; the projection lives
over the pair `{i,j} -> Yc`.  The two are the same object in the frozen
construction -- `09:445--447` fixes `u_2 = 2^{1-1} + 1 = 2 = pc` and `09:121--123`
(`eq:reference-all-columns`, `Cols(G) = Cols(N)`) says the reference copies use the
ambient outer alphabet -- and those two identifications are the equivalences `eIdx`
and `eCol`, carried here as explicit binders so that the statement stays general in
the bracket alphabet.  **They are not a STOP.**  At the endpoint
`canonical_hfinal_of_reference_construction` both are *supplied*: `eIdx` from the
frozen pair's own `Finset.equivFin` at `|{i,j}| = 2`, and `eCol` as
`Equiv.refl Yc`, which is exactly what `eq:reference-all-columns` licenses.  What is
proved here is that once they are given the density transports with no loss, by pin
from the banked `SelectDischarge.nodeProjection_transport_density`.

General in the bracket alphabet and in everything the previous theorem is general
in. -/
theorem twoCoordPair_supplies_the_bracket_column_clause {Cl : Type*} [Fintype Cl]
    [DecidableEq Cl] {Coord ι V : Type*}
    {P : Protocol X (Fin q → Yc) Z} {r A0 : ℕ}
    (Sys : RoutedSystem P Coord ι V r A0) (v : V) (S : Finset (Fin q → Yc))
    {E0 : Finset (Fin q)} {k : ℕ} {i j : Fin q}
    (eIdx : Fin 2 ≃ {x // x ∈ ({i, j} : Finset (Fin q))}) (eCol : Cl ≃ Yc)
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (hk : 2 ≤ k) (hij : i ≠ j) (hi : i ∉ E0) (hj : j ∉ E0) :
    ((3 : ℝ) / 5) ^ 2 * (Fintype.card Cl : ℝ) ^ (2 : ℕ)
      ≤ (((nodeProjection P S {i, j} (Sys.node v)).image
          fun f => fun m : Fin 2 => eCol.symm (f (eIdx m))).card : ℝ) := by
  have hcard : ({i, j} : Finset (Fin q)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  have hdens : ((3 : ℝ) / 5) ^ 2 * (Fintype.card Yc : ℝ)
      ^ ({i, j} : Finset (Fin q)).card
      ≤ ((nodeProjection P S {i, j} (Sys.node v)).card : ℝ) := by
    rw [hcard]
    exact twoCoordPair_projection_retains_y_sq Sys v S hcover hk hij hi hj
  exact SelectDischarge.nodeProjection_transport_density eIdx eCol hdens

end TwoCoordinateProjection

section TwoCopyRowSupply

/-- **`09:1326--1328` as the two-copy bracket's per-block row floor.**

"...each certificate contains at least `A_0 = ceil(2 x_T m_G)` rows of its copy of
`G`."  The banked `DenseWrapperFrontier.initialRefRows` **is** that ceiling; what is
recorded here is that it is literally the row floor `def:bracket` demands of each of
the `ell = 1` ladder call's two copies at row density `2 x_T` (`09:1336--1337`'s
`x = x_T`, `A:158`'s `2^ell x`).  So no separate trim is needed at a final node:
`09:1296`'s "trim it to the row density `kappa_v x_T`" reads at `kappa_v = 1` and
`ell_v = 1` as the frozen `A_0` itself.  General in `x_T` and `m_G`. -/
theorem initialRefRows_is_the_twoCopy_block_floor (xT : ℝ) (mG : ℕ) :
    ⌈(mG : ℝ) * (2 * xT)⌉₊ = initialRefRows xT mG := by
  unfold initialRefRows
  congr 1
  ring

/-- **`09:1325--1328`, PROVED of every routed system.**

"At a final node `d_v = r`, so each certificate contains at least `A_0` rows of its
copy of `G`."  Both halves are theorems rather than assumptions: `d_v = r` is the
`final_spec` field's `IsFinalAliceNode` clause, and the row count is the routed
certificate's own `rows_floor` at the resulting capacity exponent `r - r = 0`, where
`refRowFloor A_0 0 = A_0`.  General in every parameter. -/
theorem finalNode_cert_rows_ge_initialRefRows {X Y Z : Type*}
    {P : Protocol X Y Z} {Coord ι V : Type*} {r A0 : ℕ}
    (S : RoutedSystem P Coord ι V r A0) {v : V} (hv : S.firstBob v = false)
    {i : ι} (hi : S.place i = v) :
    A0 ≤ (S.cert i).rows := by
  have hlen : (S.cert i).route.length = r := by
    rw [S.cert_at i, hi]
    exact (S.final_spec v hv).2
  have h := (S.cert i).rows_floor
  rw [hlen] at h
  simpa [refRowFloor] using h

/-- **`09:1340`, the ladder call's legality guard, DERIVED from the schedule gate.**

"`2 x_T <= t_ref x_T <= 1` verifies legality."  `lem:certified-row-ladder` (`A:155--156`)
asks `2^ell x <= 1`, which at `ell = 1` and `x = x_T` is `2 x_T <= 1`.  The frozen
chain runs through `t_ref`, but `eq:wrapper-low-simple-gate`'s `q x_T <= 4/25025`
(`09:304--307`; also `06:927--934`) at `q = 2^r` dominates it for `r >= 1`; `x_T` is
positive (the banked `TranscriptLevelSuccessors.xTdepth_pos`).  So the guard is
evaluated from the schedule rather than assumed.  General in `r >= 1` and `b_T`. -/
theorem twoCopy_row_legality_of_gate {r bT : ℕ} (hr : 1 ≤ r)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025) :
    2 * xTdepth bT ≤ 1 := by
  have hx : 0 < xTdepth bT := TranscriptLevelSuccessors.xTdepth_pos bT
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  nlinarith [hgate, hx, hpow]

/-- **`09:1334--1343`, the frozen contradiction, PROVED.**

"The resulting two-copy restriction has complexity at least `C`.  But the suffix
below a node reached after `r` Alice bits in the alleged `(C+r-1)`-bit protocol has
depth at most `C-1`, a contradiction."

The upper leg is `hreal`, the realization of the two-copy restriction inside the
suffix; the lower leg is the banked `DenseWrapperFrontier.finalNode_twoCopy_bound`,
the `ell = 1` ladder call of `09:1334--1338` at
`(M,H,x,z,ell) = (G, C-1, x_T, y, 1)` with `09:1339`'s `lem:wrapper-reference` base
and `C >= 3`; the collision is the banked
`DenseWrapperFrontier.finalNode_budget_contradiction`.  Nothing is re-derived.

*Why this is not a triviality about the shape of the hypotheses.*  The frozen margin
is exactly one bit -- `finalPair_margin_is_exactly_one_bit` -- so a residual bound of
`C-1` would leave the budget consistent and no contradiction would follow.

General in the two carriers, `C`, `r`, the residual cost and `x_T`. -/
theorem finalPair_ladder_contradiction {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {C r cost : ℕ} {xT : ℝ}
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hC : 3 ≤ C) (hxT0 : 0 < xT) (hlegal : 2 * xT ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (hreal : LambdaGE Gmat 2 (2 * xT) (((3 : ℝ) / 5) ^ 2) ≤ cost)
    (hbudget : cost + r ≤ C + r - 1) : False := by
  have hlad := finalNode_twoCopy_bound Gmat hRw hCl hC hxT0 (by norm_num) (by norm_num)
    hbase hlegal
  exact finalNode_budget_contradiction hC hbudget (le_trans hlad hreal)

/-- **Battery C (statement pole): the frozen margin is exactly one bit.**

**Generalized over `C` and `r` under the paper's own floor**, so that no value is
chosen: the only hypothesis is `09:1302`'s `C >= 3`, and the statement then holds at
*every* width exponent `r`.  A residual cost of `C - 1` -- the depth
`09:1341--1343` allows the suffix below a final node -- satisfies the frozen budget
`cost + r <= C + r - 1`, while the `ell = 1` ladder's own output `C`
(`finalNode_twoCopy_bound`) does not.  So `finalPair_ladder_contradiction` draws its
strength from the ladder's extra bit and not from an over-tight budget hypothesis;
had the `ell = 1` call delivered only `C - 1`, the two constraints would be
consistent and `lem:final-reference-uniqueness` would not follow.  The companion pole
on the first-Bob side is the banked
`DenseWrapperFrontier.firstBobLight_needs_the_extra_bit`.

The predecessor round stated this at the two self-chosen instances `C = 3`, `r = 6`;
`r = 6` was not a frozen value but the equality case of `k_ref + 2 <= r` at
`k_ref = 4`, so it is gone.  Both surviving numerals are frozen: `3` is `09:1302`'s
floor and `1` is `09:1341--1343`'s `C-1` margin. -/
theorem finalPair_margin_is_exactly_one_bit {C r : ℕ} (hC : 3 ≤ C) :
    (C - 1) + r ≤ C + r - 1 ∧ ¬ (C + r ≤ C + r - 1) := by
  omega

/-! ### §4a-0b  The two SINGLE-CERTIFICATE supplies (`09:1325--1328`, `09:105--123`)

`lem:final-reference-uniqueness` is proved by contradiction *from a pair*, but
nothing the frozen proof **consumes** is pair-shaped: `09:1326--1328` supplies
`A_0` rows to *each* certificate separately, and `09:105--123` places *each*
selected outer coordinate's reference copy separately.  The two lemmas below are
those two supplies, each quantified over **one** certificate (resp. one
coordinate); the pair enters only where the frozen proof puts it, inside the
uniqueness argument, which instantiates them twice.

This is the structural repair of the predecessor round.  A premise quantified
over pairs of certificates at one node is, by
`pair_premise_is_vacuous_at_a_thin_node`, implied by the conclusion
`(certsAtNode S v).card <= 1`; and any such premise strong enough to close the
two-certificate case implies that conclusion.  So **every** pair-shaped premise
at a final node is conclusion-equivalent, whatever it says, and no wording can
rescue one.  The remedy is not a better pair premise but none at all. -/

/-- **`09:1325--1328` in the two-copy bracket's units, at ONE certificate.**

"At a final node `d_v = r`, so each certificate contains at least
`A_0 = ceil(2 x_T m_G)` rows of its copy of `G`."  Given a block family `Bfin`
realizing each certificate's own reference-row count, the block of a **single**
certificate sitting at a final node meets the per-block row floor `def:bracket`
demands of the `ell = 1` ladder call at row density `2 x_T`.

Nothing here is quantified over two certificates: `i` is one certificate, `hi`
places it at `v`, and the conclusion is a statement about its own block.  The
`A_0` floor is read off the routed system by
`finalNode_cert_rows_ge_initialRefRows` (the certificate's own `rows_floor` at
capacity exponent `r - r = 0`), and `hA0` is the identification
`initialRefRows_is_the_twoCopy_block_floor` supplies at the frozen
`A_0 = initialRefRows x_T m_G` of `09:1219`.

*Why the trivial witness fails.*  Not existential; and the conclusion is false
for a block family that ignores the certificate (`Bfin := fun _ => emptyset`
falsifies it whenever the floor is positive), so `hBfin` is doing work.

General in the carriers, the coordinate and index types, the protocol, `r`, `A_0`
and `x_T`. -/
theorem finalNode_block_meets_twoCopy_floor {X Y Z : Type*} [Fintype X]
    {P : Protocol X Y Z} {Coord ι V : Type*} {r A0 : ℕ} {xT : ℝ}
    (S : RoutedSystem P Coord ι V r A0) {v : V} (hv : S.firstBob v = false)
    (hA0 : ⌈(Fintype.card X : ℝ) * (2 * xT)⌉₊ ≤ A0)
    (Bfin : ι → Finset X) (hBfin : ∀ x : ι, (S.cert x).rows ≤ (Bfin x).card)
    {i : ι} (hi : S.place i = v) :
    ⌈(Fintype.card X : ℝ) * (2 * xT)⌉₊ ≤ (Bfin i).card := by
  have h1 : A0 ≤ (S.cert i).rows := finalNode_cert_rows_ge_initialRefRows S hv hi
  have h2 := hBfin i
  omega

/-- **`09:105--123` at ONE outer coordinate per copy: the bracket's `hgame`,
supplied.**

`SELECT-EMBED-001` -- the **banked**
`SelectEmbedComposition.interlaceFun_reference_copy` -- is consumed by pin here
and re-proved nowhere.  What this lemma adds is the composition with the
construction's **single-coordinate** placement identity

  `hplace : g (plc j a) c = interlaceFun N q (cidx j, iota_R a) c`,

which is `09:113--116` at one started coordinate `j` and one reference row `a`,
and is exactly the datum Section 2's first-Bob column already carries.  Given a
choice `own : Fin pc -> Coord` naming which coordinate carries which copy of the
bracket, the `pc`-fold interlace identity `def:bracket` demands follows copy by
copy.

**No premise here mentions two certificates.**  `hplace` is quantified over one
coordinate; `own` is a *function*, supplied by the caller from the certificates
it already holds, never a hypothesis about pairs.

*Why the trivial witness fails.*  Not existential; and the conclusion is false
without `hagree` -- the banked
`SelectEmbedComposition.reference_copy_needs_the_selected_agreement` exhibits a
matrix, a selection and a disagreeing column tuple where the two sides differ.

General in the three carriers, in `q`, in `pc`, in the coordinate type, the
selection, the placement and both column tuples. -/
theorem twoCopy_hgame_of_perCoordinate_placement {X RwN Yc Coord : Type*} {q pc : ℕ}
    {Nmat : RwN → Yc → Bool} {Gmat : X → Yc → Bool} {ιR : X → RwN}
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {g : X → (Fin q → Yc) → Bool} {plc : Coord → X → X} {cidx : Coord → Fin q}
    {Scol : Finset (Fin q → Yc)}
    (hplace : ∀ (j : Coord) (a : X), ∀ c ∈ Scol,
      g (plc j a) c = interlaceFun Nmat q (cidx j, ιR a) c)
    (own : Fin pc → Coord) (y : Fin q → Yc) (hy : y ∈ Scol) (cJ : Fin pc → Yc)
    (hagree : ∀ m, y (cidx (own m)) = cJ m) (a : Fin pc × X) :
    interlaceFun Gmat pc a cJ = g (plc (own a.1) a.2) y := by
  rw [SelectEmbedComposition.interlaceFun_reference_copy Nmat Gmat ιR hsub
    (fun m => cidx (own m)) y cJ hagree a]
  exact (hplace (own a.1) a.2 y hy).symm

end TwoCopyRowSupply

section FinalClassification

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}

/-- **`09:1315--1319`, "the certificates a final node contains", as a `Finset`.**

The certificates of a routed system that stopped at the address `v`.  This is the
`certs` argument the banked `wrapperFinalReferenceUniqueness` quantifies over, made
concrete at the system's own placement map; it is not new mathematics but the
carrier the frozen lemma's count is a count *of*.

Deliberately **not** restricted to clean certificates: `09:1317` says "whether clean
or split", and the banked `RoutedSystem.cleanFinal` (the `09:1519--1520` donor set)
is the clean-only object, a different one. -/
def certsAtNode [Fintype ι] [DecidableEq V] (S : RoutedSystem P Coord ι V r A0) (v : V) :
    Finset ι :=
  Finset.univ.filter fun i => S.place i = v

/-- **Battery 6 (membership readout).**  A certificate is at `v` exactly when the
system places it there.  General in every parameter; nothing is evaluated. -/
@[simp] theorem mem_certsAtNode [Fintype ι] [DecidableEq V]
    (S : RoutedSystem P Coord ι V r A0) (v : V) (i : ι) :
    i ∈ certsAtNode S v ↔ S.place i = v := by
  simp [certsAtNode]

/-- **Battery 7 (every certificate sits at exactly one node).**

`sum_v |certs at v| = |certificates|`.  The frontier addresses partition the
certificate set, which is the bookkeeping `09:1257`'s `W_v` and `09:1262`'s
conservation both rest on: no certificate is counted twice and none is lost.
General in every parameter. -/
theorem sum_card_certsAtNode [Fintype ι] [Fintype V] [DecidableEq V]
    (S : RoutedSystem P Coord ι V r A0) :
    ∑ v, (certsAtNode S v).card = Fintype.card ι := by
  classical
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise
    (f := S.place) (fun i _ => Finset.mem_univ (S.place i))).symm

/-- **`09:1322--1324` -- a theorem of every routed system, not a binder.**

"They descend from distinct initial outer coordinates `i, j notin E_0`, because a
fixed protocol node receives at most one descendant of any initial certificate."

That sentence is the `coordUnique` field of `RoutedSystem` (`09:1278--1280`,
`09:1323--1324`), so the `hdistinct` slot of the banked
`wrapperFinalReferenceUniqueness` is *proved* here rather than assumed: two distinct
certificates sharing an address must carry distinct outer coordinates.

General in the system and the node. -/
theorem certsAtNode_coord_ne [Fintype ι] [DecidableEq V]
    (S : RoutedSystem P Coord ι V r A0) (v : V) {i j : ι}
    (hi : i ∈ certsAtNode S v) (hj : j ∈ certsAtNode S v) (hne : i ≠ j) :
    (S.cert i).coord ≠ (S.cert j).coord := by
  intro hc
  refine hne (S.coordUnique i j ?_ hc)
  rw [(mem_certsAtNode S v i).mp hi, (mem_certsAtNode S v j).mp hj]

/-- **Battery 10 (the STRUCTURAL BAN, kernel-visible): EVERY per-pair premise at
a final node is conclusion-equivalent, so none may appear anywhere.**

`lem:final-reference-uniqueness` is proved by contradiction *from a pair*, so it
is tempting to state the inputs its proof consumes at `09:1329--1343` as premises
quantified over pairs of certificates at one node carrying **distinct** outer
coordinates.  This records why that is never legitimate: for an *arbitrary*
per-pair predicate `Q`, at a node whose certificate set has at most one element
the premise never fires and is satisfied outright.

**One direction of an equivalence, and the other is free.**  This lemma is
`conclusion -> premise`, for *every* `Q` without exception.  Any pair premise
strong enough to close the two-certificate case supplies `premise -> conclusion`
by construction.  Hence every such premise is *equivalent to the conclusion*, and
a declaration carrying one proves nothing whatever it says.  Three successive
rounds died on this: a free `residual` family, then `hrealize`
(`Lambda_G(2, 2x_T, y^2) <= cost(subtree at v)`), then a pair-local existential
`hpair` handing over the two-copy bracket member.  Exhibiting an inhabitant
cannot rescue any of them, because this lemma exhibits one for all of them at
once.

**The ban this module now enforces.**  No declaration below carries a premise
quantified over two certificates or over certificate pairs.  The frozen proof's
inputs enter as the two SINGLE-certificate supplies of §4a-0b
(`finalNode_block_meets_twoCopy_floor`, `twoCopy_hgame_of_perCoordinate_placement`)
together with node-level construction data, and
`certsAtNode_card_le_one_of_construction_supply` instantiates them **twice**
inside its own proof, which is where the frozen text puts "suppose a final node
contained two certificates".

What this lemma still records honestly is that no `False` is derived anywhere in
this module from the shape of a per-pair quantifier alone.

General in the system, the node and the predicate. -/
theorem pair_premise_is_vacuous_at_a_thin_node [Fintype ι] [DecidableEq V]
    (S : RoutedSystem P Coord ι V r A0) (v : V)
    (hthin : (certsAtNode S v).card ≤ 1) {Q : ι → ι → Prop} :
    ∀ i ∈ certsAtNode S v, ∀ j ∈ certsAtNode S v,
      (S.cert i).coord ≠ (S.cert j).coord → Q i j := by
  intro i hi j hj hne
  exact absurd (congrArg (fun x => (S.cert x).coord)
    (Finset.card_le_one.mp hthin i hi j hj)) hne

end FinalClassification

/-! ### §4a-1  `lem:final-reference-uniqueness` with the frozen proof's inputs
supplied ONE CERTIFICATE AT A TIME (`09:1315--1343`)

The composition of §4a-0's derived facts and §4a-0b's two single-certificate
supplies with §4a's uniqueness count.  **No premise of this subsection is
quantified over two certificates or over certificate pairs** -- the ban
`pair_premise_is_vacuous_at_a_thin_node` forces (see Battery 10).  The pair
appears only inside the proof, exactly where `09:1320` puts it ("Suppose a final
node contained two certificates"), and the supplies are instantiated twice
there. -/

section LocalizedFinalUniqueness

variable {Coord ι V : Type*} {r A0 : ℕ}

/-- **`lem:final-reference-uniqueness` (`09:1315--1344`) at a final node, with
every slot of the banked lemma discharged and NO PAIR-SHAPED PREMISE AT ALL.**

`DenseWrapperFrontier.wrapperFinalReferenceUniqueness` is consumed **by pin, at
its own interface**, and its three slots are supplied as follows:

* `hdistinct` -- `certsAtNode_coord_ne`, i.e. the system's own `coordUnique`
  (`09:1322--1324`).  Discharged.
* `hladder` -- `09:1334--1338`, the `ell = 1` ladder call.  Discharged: the
  residual quantity is the DEFINED `Lambda_G(2, 2x_T, y^2)` -- `A:158`'s ladder
  output at the frozen substitution `(M,H,x,z,ell) = (G, C-1, x_T, y, 1)` of
  `09:1336--1337` -- and `C <= Lambda_G(2, 2x_T, y^2)` is the banked
  `DenseWrapperFrontier.finalNode_twoCopy_bound`, consumed by pin.
* `hsuffix` -- `09:1341--1343`, "the suffix below a node reached after `r` Alice
  bits in the alleged `(C+r-1)`-bit protocol has depth at most `C-1`".
  Discharged from `hcost` through the banked
  `RoutedCertificateSystem.RoutedSystem.final_residual_budget` off the pairs, and
  at a genuine distinct-coordinate pair by `finalPair_ladder_contradiction`
  (`09:1334--1343`), whose upper leg is the banked
  `SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member` fired at the
  two-copy bracket member **assembled inside the proof** from the
  single-certificate supplies by the banked
  `SelectDischarge.bracketMember_of_blocks_and_columns`.

**What replaced the predecessor round's `hpair`, and why nothing of that shape
may return.**  Battery 10 is one direction of an equivalence: at a node
satisfying the conclusion, *every* premise quantified over distinct-coordinate
pairs of certificates at that node holds vacuously.  A pair premise strong enough
to close the two-certificate case supplies the other direction.  So a pair
premise -- a free `residual` family, `hrealize`, or an existential `hpair`
handing over the bracket member -- is *equivalent to the conclusion*, and
exhibiting an inhabitant for it proves nothing, because Battery 10 exhibits one
for every such premise simultaneously.  **This declaration therefore carries
none.**  What it carries instead is the construction's own data, in the shape the
frozen text supplies it:

* `Bfin` and `hBfin` -- one G-row block per certificate realizing that
  certificate's own reference-row count.  `09:1325--1328` then floors it
  **per certificate** through `finalNode_block_meets_twoCopy_floor`.
* `plc` and `hrowloc` -- the placement of one certificate's block inside the
  rows the routing retains at `v` (`09:1291--1296` read at `kappa_v = 1`).
  Quantified over one certificate.
* `hplace` -- `09:113--116`, the reference-copy placement identity at **one**
  started coordinate and one row; §4a-0b's
  `twoCopy_hgame_of_perCoordinate_placement` turns it into the bracket's `hgame`
  by consuming the banked `SELECT-EMBED-001` owner
  `SelectEmbedComposition.interlaceFun_reference_copy`.
* `Scol`, `hcover`, `hk` -- the retained column set and the `09:442--445` cover
  family.  Node-level, mentioning no certificate at all; §4a-0's
  `twoCoordPair_supplies_the_bracket_column_clause` reads `09:1331--1332`'s
  `y^2` density off them.
* `cidx`, `hcidx`, `hE0` -- the outer coordinate a certificate descends from,
  injectively (`09:1322--1323`, "They descend from distinct initial outer
  coordinates `i,j` not in `E_0`") and outside
  `E_0` (`09:1235--1236`'s start rule).  All three are theorems at the canonical
  system and binders only at this generality.

None of these mentions a cost, a complexity, a density on the suffix, or a
certificate count, and each is a *total* statement about the construction, so
the conclusion does not imply any of them and Battery 10 does not apply to a
single one.  The pair `{i,j}` is *constructed* inside the proof from the two
certificates the contradiction hypothesis produces.

**The frozen guards, each at its anchor** (all inherited unchanged from the
predecessor statement and none of them pair-shaped): `halleged`
(`Protocol.Computes P g`) and `hcost` (`P.cost <= C + r - 1`) are the alleged
protocol of `09:1187--1193`, carried as named hypotheses and never as an
`axiom`; `hC : 3 <= C` is `09:1302` ("`C >= 3` verifies `H >= 2`"); `hbase` is
`09:1339`'s `lem:wrapper-reference` base certificate at the `ell = 1`
substitution of `09:1336--1337`; `hlegal : 2 x_T <= 1` is `09:1340`'s legality
line (`twoCopy_row_legality_of_gate` derives it from `eq:wrapper-low-simple-gate`,
`09:304--307`, at every call site, so it is not assumed there); `hxT0` is the
positivity of `x_T = 2^{-b_T}` (banked `TranscriptLevelSuccessors.xTdepth_pos`);
`hA0` is `09:1219`'s `A_0 = ceil(2 x_T m_G)` in the bracket's units
(`initialRefRows_is_the_twoCopy_block_floor` supplies it by equality); `hX` and
`hYc` are the carrier nonemptiness the banked
`DenseWrapperFrontier.finalNode_twoCopy_bound` demands; `hk : 2 <= k_ref` is
what `09:442--445`'s cover family needs to contain its `l = 1` member, and is
`by omega` from `09`'s `k_ref >= 4` at every call site.

**Full-bundle satisfiability is NOT claimed for this declaration and must not
be**: the bundle contains `halleged` and `hcost`, i.e. the alleged protocol of
`09:1187--1193`, whose non-existence is the conclusion of the whole argument.
What LANE-GATE 3 asks for, and what Batteries 11b/11c/11d deliver, is joint
satisfiability of the *new* construction bundle `(hsub, hBfin, hblockFin/hrowloc,
hplace)` at legal parameters.

*Why the trivial witness fails.*  Not existential; and the conclusion is false at
a node holding two certificates of distinct coordinates, which nothing in
`RoutedSystem` forbids.

*Consistency of the hypothesis bundle.*  `finalBlock_bundle_joint_inhabitant`
(Section 5) exhibits `Gmat`, `iota_R`, `g`, `plc` and `Bfin` satisfying `hsub`,
`hBfin`, the placement clause and `hplace` **jointly**, at the coordinate slab
`R` of `09:1235--1236` and at any legal `(q, r, A_0)`;
`finalBlock_bundle_inputs_are_legal` supplies the `09:1235--1236` slab family
and its `09:1233--1235` retention for that bundle.  The protocol frame is not
republished there: `lem:wrapper-no-bob-completion` (`09:1195--1213`, ladder
constructed at `09:1203--1207`) is the banked
`RoutingDynamics.completedNoBob_aliceLadder`, consumed by pin.

The carriers are the frozen ones and not a specialization of convenience:
`Rw = X` because `09:113--116` makes Alice's reference rows the rows of `G`, and
`Cl = Yc` because `09:121--123` (`eq:reference-all-columns`) makes the reference
copies use the ambient outer alphabet.  Generality in a *separate* bracket
alphabet would be generality the frozen construction does not have.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet `Yc`,
the Alice carrier `X`, the coordinate, index and node types, the protocol, `q`,
`r`, `A_0`, `C`, `k_ref`, `E_0`, `x_T`, the retained column set, and the block and
placement families. -/
theorem certsAtNode_card_le_one_of_construction_supply
    {X : Type*} [Fintype X] {Yc : Type*} [Fintype Yc] [DecidableEq Yc]
    {RwN : Type*} {q C kref : ℕ} {xT : ℝ} {E0 : Finset (Fin q)}
    [Fintype ι] [DecidableEq V]
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    (halleged : Protocol.Computes P g)
    (S : RoutedSystem P Coord ι V r A0)
    (cidx : Coord → Fin q) (hcidx : Function.Injective cidx)
    (hE0 : ∀ j : Coord, cidx j ∉ E0)
    {v : V} (hv : S.firstBob v = false)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (hxT0 : 0 < xT) (hlegal : 2 * xT ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (hA0 : ⌈(Fintype.card X : ℝ) * (2 * xT)⌉₊ ≤ A0)
    {Scol : Finset (Fin q → Yc)} (hk : 2 ≤ kref)
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (Bfin : ι → Finset X) (plc : Coord → X → X)
    (hBfin : ∀ x : ι, (S.cert x).rows ≤ (Bfin x).card)
    (hrowloc : ∀ x : ι, S.place x = v → ∀ a ∈ Bfin x,
      TerminalResidualComparison.RouteRows P (S.node v) (plc (S.cert x).coord a))
    (hplace : ∀ (j : Coord) (a : X), ∀ c ∈ Scol,
      g (plc j a) c = interlaceFun Nmat q (cidx j, ιR a) c) :
    (certsAtNode S v).card ≤ 1 := by
  classical
  have hbudget : (descend P (S.node v)).cost + r ≤ C + r - 1 :=
    S.final_residual_budget hv hcost
  have hlad : C ≤ LambdaGE Gmat 2 (2 * xT) (((3 : ℝ) / 5) ^ 2) :=
    finalNode_twoCopy_bound Gmat hX hYc hC hxT0 (by norm_num) (by norm_num) hbase hlegal
  set L : ℕ := LambdaGE Gmat 2 (2 * xT) (((3 : ℝ) / 5) ^ 2) with hL
  refine wrapperFinalReferenceUniqueness (C := C) (r := r) (certsAtNode S v)
    (fun i => (S.cert i).coord)
    (fun i j => if i ∈ certsAtNode S v ∧ j ∈ certsAtNode S v
        ∧ (S.cert i).coord ≠ (S.cert j).coord then L else 0)
    hC (fun i hi j hj hne => certsAtNode_coord_ne S v hi hj hne) ?_ ?_
  · intro i hi j hj hne
    dsimp only
    rw [if_pos (⟨hi, hj, hne⟩ : i ∈ certsAtNode S v ∧ j ∈ certsAtNode S v
      ∧ (S.cert i).coord ≠ (S.cert j).coord)]
    exact hlad
  · intro i j
    dsimp only
    by_cases h : i ∈ certsAtNode S v ∧ j ∈ certsAtNode S v
        ∧ (S.cert i).coord ≠ (S.cert j).coord
    · -- `09:1320--1343`, the hypothetical two-certificate case, closed HERE from
      -- the single-certificate supplies rather than from a pair premise.
      exfalso
      obtain ⟨hi, hj, hcne⟩ := h
      have hiv : S.place i = v := (mem_certsAtNode S v i).mp hi
      have hjv : S.place j = v := (mem_certsAtNode S v j).mp hj
      -- `09:1322--1324`: the two certificates carry distinct outer coordinates.
      have hij : cidx (S.cert i).coord ≠ cidx (S.cert j).coord := fun hh => hcne (hcidx hh)
      -- `09:1329--1330`: the frozen pair `{i,j}`, of the frozen width `u_2 = 2`.
      have hJcard :
          ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
      have eIdx : Fin 2 ≃
          {z // z ∈ ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))} :=
        ((Finset.equivFin _).trans (finCongr hJcard)).symm
      have hsel : ∀ m : Fin 2,
          (eIdx m).val = cidx (S.cert i).coord ∨ (eIdx m).val = cidx (S.cert j).coord := by
        intro m
        rcases Finset.mem_insert.mp (eIdx m).2 with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Finset.mem_singleton.mp h')
      obtain ⟨pick, hpickdef⟩ :
          ∃ pick : Fin 2 → ι,
            ∀ m, pick m = if (eIdx m).val = cidx (S.cert i).coord then i else j :=
        ⟨_, fun _ => rfl⟩
      have hpickIdx : ∀ m, cidx (S.cert (pick m)).coord = (eIdx m).val := by
        intro m
        rw [hpickdef m]
        by_cases h' : (eIdx m).val = cidx (S.cert i).coord
        · rw [if_pos h']; exact h'.symm
        · rw [if_neg h']
          rcases hsel m with h'' | h''
          · exact absurd h'' h'
          · exact h''.symm
      have hpickv : ∀ m, S.place (pick m) = v := by
        intro m
        rw [hpickdef m]
        by_cases h' : (eIdx m).val = cidx (S.cert i).coord
        · rw [if_pos h']; exact hiv
        · rw [if_neg h']; exact hjv
      -- `09:1325--1328`, the FIRST single-certificate supply, instantiated twice.
      have hAfloor : ∀ m, ⌈(Fintype.card X : ℝ) * (2 * xT)⌉₊ ≤ (Bfin (pick m)).card :=
        fun m => finalNode_block_meets_twoCopy_floor S hv hA0 Bfin hBfin (hpickv m)
      -- `09:1331--1332`, the two-coordinate column clause, a THEOREM of §4a-0.
      have hCd : ((3 : ℝ) / 5) ^ 2 * (Fintype.card Yc : ℝ) ^ (2 : ℕ)
          ≤ (((SelectEmbedComposition.transportedProj P Scol
                ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))
                (S.node v) eIdx (Equiv.refl Yc)).card : ℕ) : ℝ) :=
        twoCoordPair_supplies_the_bracket_column_clause (Cl := Yc) S v Scol eIdx
          (Equiv.refl Yc) hcover hk hij (hE0 _) (hE0 _)
      -- the row localization, per certificate
      have hrow : ∀ a : {a // a ∈ SelectDischarge.blockRows (fun m => Bfin (pick m))},
          TerminalResidualComparison.RouteRows P (S.node v)
            (plc (S.cert (pick a.1.1)).coord a.1.2) := by
        intro a
        exact hrowloc (pick a.1.1) (hpickv a.1.1) a.1.2
          ((SelectDischarge.mem_blockRows (fun m => Bfin (pick m)) a.1).mp a.2)
      -- the column localization, from the banked section
      have hcolloc : ∀ c, TerminalResidualComparison.RouteCols P (S.node v)
          (SelectEmbedComposition.ambientColumn P Scol
            ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))
            (S.node v) eIdx (Equiv.refl Yc) c) :=
        fun c => SelectEmbedComposition.routeCols_ambientColumn c
      -- `09:105--123`, the SECOND single-certificate supply, one coordinate per copy.
      have hgame : ∀ (a : {a // a ∈ SelectDischarge.blockRows (fun m => Bfin (pick m))})
          (c : {c // c ∈ SelectEmbedComposition.transportedProj P Scol
                ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))
                (S.node v) eIdx (Equiv.refl Yc)}),
          interlaceFun Gmat 2 a.1 c.1
            = g (plc (S.cert (pick a.1.1)).coord a.1.2)
                (SelectEmbedComposition.ambientColumn P Scol
                  ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))
                  (S.node v) eIdx (Equiv.refl Yc) c) := by
        intro a c
        have hyagree : ∀ m : Fin 2,
            SelectEmbedComposition.ambientColumn P Scol
                ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))
                (S.node v) eIdx (Equiv.refl Yc) c (cidx (S.cert (pick m)).coord)
              = c.val m := by
          intro m
          rw [hpickIdx m]
          simpa using SelectEmbedComposition.ambientColumn_apply
            (P := P) (S := Scol)
            (J := ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q)))
            (p := S.node v) (eIdx := eIdx) (eCol := Equiv.refl Yc) c m
        have hmemS : SelectEmbedComposition.ambientColumn P Scol
            ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q))
            (S.node v) eIdx (Equiv.refl Yc) c ∈ Scol :=
          (Finset.mem_inter.mp (SelectEmbedComposition.ambientColumn_mem
            (P := P) (S := Scol)
            (J := ({cidx (S.cert i).coord, cidx (S.cert j).coord} : Finset (Fin q)))
            (p := S.node v) (eIdx := eIdx) (eCol := Equiv.refl Yc) c)).1
        exact twoCopy_hgame_of_perCoordinate_placement hsub hplace
          (fun m => (S.cert (pick m)).coord) _ hmemS c.1 hyagree a.1
      -- `09:1334--1343`, the frozen contradiction.  The upper leg is TWO banked
      -- owners applied to each other directly, by pin, with no declaration of this
      -- module between them: `bracketMember_of_blocks_and_columns` assembles
      -- `def:bracket`'s member from the two single-certificate supplies `hAfloor`
      -- (`09:1325--1328`) and `hCd` (`09:1331--1332`), and
      -- `lambdaGE_le_cost_descend_of_bracket_member` reads the `ell = 1` ladder
      -- output `Lambda_G(2, 2x_T, y^2)` (`09:1336--1337`) off it at the node's own
      -- address, which is legitimate because `09:1330` records that no Bob query
      -- has occurred on the route to this node.
      exact finalPair_ladder_contradiction Gmat hX hYc hC hxT0 hlegal hbase
        (SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member Gmat halleged
          (S.node v) (SelectDischarge.blockRows (fun m => Bfin (pick m))) _
          (SelectDischarge.bracketMember_of_blocks_and_columns
            (fun m => Bfin (pick m)) _ hAfloor hCd)
          _ _ hrow hcolloc hgame) hbudget
    · rw [if_neg h]
      omega

end LocalizedFinalUniqueness

section CanonicalFinalClassification

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **The kinds carried at a frontier node of the canonical routed system.**

Each certificate's kind is the **derived** `RoutingDynamics.kindAlong` of its route
(`09:1244--1248`), never constructor data, so this `Finset` is computed from the
routing and nothing about it is chosen. -/
def canonicalKindsAt {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) : Finset CertKind :=
  (certsAtNode (canonicalSystem hcomp hR) v).image
    fun x => kindAlong P (R x.1) A0 r x.2.val

/-- **`09:1346--1347`, the final-node classification, DERIVED.**

"Thus every final Alice node contains either one clean certificate, one half-weight
descendant of a split certificate, or none."

The trichotomy read off the certificates actually sitting at `v`: clean if a clean
certificate is there, otherwise low if a split descendant is, otherwise none.  This
is the `certOpt` slot the banked counting spine takes -- but *computed* from the
routing rather than supplied, which is the whole point of this section.  At a final
node the three cases are exclusive because
`certsAtNode_card_le_one_of_construction_supply` caps the count at one; the
definition is total regardless, so no legality claim is hidden inside it. -/
def canonicalFinalCert {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) : Option CertKind :=
  if CertKind.clean ∈ canonicalKindsAt hcomp hR v then some CertKind.clean
  else if CertKind.low ∈ canonicalKindsAt hcomp hR v then some CertKind.low
  else none

/-- **Aux.**  At the canonical system a certificate sits at `v` exactly when its
address *is* `v`'s address: the placement map of `FrontierIndexing.canonicalSystem`
is the inclusion of stopping addresses into the frontier.  General. -/
theorem mem_certsAtNode_canonical {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) (x : CertIndex P R A0 r) :
    x ∈ certsAtNode (canonicalSystem hcomp hR) v ↔ x.2.val = v.val := by
  rw [mem_certsAtNode]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- **`09:1257` re-indexed: `W_v` is the total weight of the certificates at `v`.**

`FrontierIndexing.frontierWeight` sums the derived weight over *all* certificate
indices with an address test; this is the same sum taken over the certificates that
are there.  General. -/
theorem frontierWeight_eq_sum_certsAtNode {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) :
    frontierWeight P R A0 r v
      = ∑ x ∈ certsAtNode (canonicalSystem hcomp hR) v,
          (kindAlong P (R x.1) A0 r x.2.val).weight := by
  classical
  unfold frontierWeight certsAtNode
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x.2.val = v.val
  · rw [if_pos h, if_pos (Subtype.ext h : (canonicalSystem hcomp hR).place x = v)]
  · rw [if_neg h, if_neg (fun hc => h (congrArg Subtype.val hc))]

/-- **Battery 8 (the classification is `none` exactly on the empty nodes).**

A round-trip between the derived classification and the certificate set it is read
off: `canonicalFinalCert` returns `none` precisely when no certificate sits at the
node.  This is what makes the third case of `09:1346--1347` ("or none") the honest
reading of an *empty* node rather than a default value, and it holds at every
frontier node, with no uniqueness input.  General. -/
theorem canonicalFinalCert_eq_none_iff {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) :
    canonicalFinalCert hcomp hR v = none
      ↔ certsAtNode (canonicalSystem hcomp hR) v = ∅ := by
  classical
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hmem : kindAlong P (R x.1) A0 r x.2.val ∈ canonicalKindsAt hcomp hR v :=
      Finset.mem_image_of_mem _ hx
    unfold canonicalFinalCert at h
    split_ifs at h with h1 h2
    · cases hk : kindAlong P (R x.1) A0 r x.2.val
      · exact h1 (hk ▸ hmem)
      · exact h2 (hk ▸ hmem)
  · intro h
    have hk : canonicalKindsAt hcomp hR v = ∅ := by
      simp [canonicalKindsAt, h]
    simp [canonicalFinalCert, hk]

/-- **`09:1346--1350` in weight form: the `hfinal` shape at one node.**

Given the uniqueness count of `lem:final-reference-uniqueness`, the node's total
certificate weight `W_v` (`09:1257`) is at most the weight of its single certificate
-- `1` for a clean one, `1/2` for a split descendant, `0` for none -- which is
exactly `DenseWrapperFrontier.finalWeight` of the derived classification.  In fact
equality holds; the inequality is the shape the banked counting spine consumes.

The uniqueness input is genuinely load-bearing and is not smuggled in: without it
two clean certificates at one node give `W_v = 1 + 1 = 2`, and the banked
`DenseWrapperFrontier.finalWeight_clean`, `finalWeight_low` and `finalWeight_none`
evaluate the three classification values to `1`, `1/2` and `0`, none of which bounds
`2`.  Those three banked evaluations are the whole of that observation and are
consumed rather than restated as a conjunction here.

General in the carriers, the protocol, the reference rows, `A_0`, `r` and the
node. -/
theorem canonical_frontierWeight_le_finalWeight_of_card_le_one {P : Protocol X Y Z}
    {R : Coord → Finset X} {A0 r : ℕ} (hcomp : CompletedNoBob P r)
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) {v : FrontierNode P R A0 r}
    (hcard : (certsAtNode (canonicalSystem hcomp hR) v).card ≤ 1) :
    frontierWeight P R A0 r v ≤ finalWeight (canonicalFinalCert hcomp hR v) := by
  classical
  rw [frontierWeight_eq_sum_certsAtNode hcomp hR v]
  rcases Finset.eq_empty_or_nonempty (certsAtNode (canonicalSystem hcomp hR) v) with hE | hN
  · have hnone : canonicalFinalCert hcomp hR v = none :=
      (canonicalFinalCert_eq_none_iff hcomp hR v).mpr hE
    rw [hE, Finset.sum_empty, hnone, finalWeight_none]
  · obtain ⟨x, hx⟩ :=
      Finset.card_eq_one.mp (le_antisymm hcard (Finset.one_le_card.mpr hN))
    have hk : canonicalKindsAt hcomp hR v = {kindAlong P (R x.1) A0 r x.2.val} := by
      simp [canonicalKindsAt, hx]
    rw [hx, Finset.sum_singleton]
    cases hkind : kindAlong P (R x.1) A0 r x.2.val with
    | clean =>
        have hc : canonicalFinalCert hcomp hR v = some CertKind.clean := by
          simp [canonicalFinalCert, hk, hkind]
        rw [hc, finalWeight_clean]
        simp [CertKind.weight]
    | low =>
        have hc : canonicalFinalCert hcomp hR v = some CertKind.low := by
          simp [canonicalFinalCert, hk, hkind]
        rw [hc, finalWeight_low]
        simp [CertKind.weight]

end CanonicalFinalClassification

/-! ### §4a-2  The `hfinal` slot supplied from the canonical construction
(`09:1315--1350`)

`certsAtNode_card_le_one_of_construction_supply` fired at
`FrontierIndexing.canonicalSystem`.  Every input it takes is construction data
of the canonical system -- the per-certificate block family, its placement, the
per-coordinate reference-copy identity, and the node-level cover -- and **not
one of them is quantified over a pair of certificates**.  The frozen proof's
pair enters only inside that declaration's own body. -/

section CanonicalFinalRealization

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **The `hfinal` slot at the canonical routed system, SUPPLIED (`09:1315--1350`),
with NO PAIR-SHAPED PREMISE.**

Every final Alice-frontier node of `FrontierIndexing.canonicalSystem` satisfies the
frozen classification bound `W_v <= finalWeight(cert v)` at the **derived**
classification `canonicalFinalCert`.  This is precisely the `hfinal` argument that
Section 4 carried as a binder, now obtained from `lem:final-reference-uniqueness`
-- consumed by pin as `DenseWrapperFrontier.wrapperFinalReferenceUniqueness`
inside `certsAtNode_card_le_one_of_construction_supply`.  The certificate
assignment is no longer a free function either: `certOpt` was an arbitrary
parameter in Section 4, and here it is `canonicalFinalCert`, read off the routing.

**Every input of `09:1325--1340` is discharged here, not assumed.**

* the **per-certificate block rows** are `09:1325--1328`'s
  `A_0 = ceil(2 x_T m_G)`: `finalNode_cert_rows_ge_initialRefRows` reads the floor
  off the routed system at `d_v = r`, `initialRefRows_is_the_twoCopy_block_floor`
  identifies it with the two-copy bracket's per-block floor at row density
  `2 x_T`, and `finalNode_block_meets_twoCopy_floor` composes the two **at one
  certificate**;
* the **two-coordinate column clause** is `09:1329--1332`, a theorem of §4a-0
  (`twoCoordPair_supplies_the_bracket_column_clause`, hence the banked
  `SelectDischarge.parent_projection_dense_at_frontier_node` and
  `SelectDischarge.nodeProjection_transport_density`), fired inside the uniqueness
  proof at the pair the contradiction hypothesis produces, whose members avoid
  `E_0` by `SelectEmbedComposition.startedIdx_notMem_E0` -- the `09:1235--1236`
  start rule, not an assumption;
* the **route localizations** are free: the column section is the banked
  `SelectEmbedComposition.ambientColumn` with its own `routeCols_ambientColumn`,
  and the row side is `SelectDischarge.routeRows_of_mem_rowsAt` applied to
  `hblockFin`, one certificate at a time.  No Bob child is taken, because
  `09:1330` records that no Bob query has occurred on the route to a final node;
* the **reference-copy embedding** is the **banked** `SELECT-EMBED-001` owner
  `SelectEmbedComposition.interlaceFun_reference_copy` (`09:105--123` with
  `eq:reference-all-columns`), consumed by pin through §4a-0b's
  `twoCopy_hgame_of_perCoordinate_placement`, which takes the construction's
  `hplace` at **one** coordinate.

**What survives as construction data, and why Battery 10 cannot touch it.**
`Bfin` is the G-row block of each certificate's own copy of `G`, `hBfin` says it
realizes that certificate's reference-row count, and `hblockFin` places it inside
`RoutingDynamics.rowsAt` at the certificate's address.  Together with `plc` and
`hplace` -- carried unchanged from Section 2, where the first-Bob column already
demands them -- that is exactly the trims-and-placement datum of `09:1291--1296`
read at `kappa_v = 1`, where `09:1325--1328` supplies `A_0` instead of a trim.
None of these mentions a cost, a complexity or a weight, and **none is quantified
over two certificates**, so Battery 10's `conclusion -> premise` direction does
not apply to any of them and none can be a disguised restatement of the
conclusion.  Contrast the two dead predecessors: `hrealize`, an inequality on
`cost(subtree at v)` per distinct-coordinate pair, and its successor `hpair`, a
pair-local existential producing the bracket member -- both pair-shaped, hence
both conclusion-equivalent by Battery 10 regardless of content.

*Why the trivial witness fails.*  Not existential.  The conclusion is a bound at
every final node simultaneously, and it is false without the uniqueness count: two
clean certificates at one node give `W_v = 2` while the banked `finalWeight_clean`,
`finalWeight_low` and `finalWeight_none` evaluate the three classification values to
`1`, `1/2` and `0`.  The trivial classification `fun _ => none` would make the
right-hand side `0` and the statement false at any node carrying a certificate
(`canonicalFinalCert_eq_none_iff`).

*Why the hypothesis bundle is consistent.*  `finalBlock_bundle_joint_inhabitant`
(Section 5) exhibits `Gmat`, `iota_R`, `g`, `plc` and `Bfin` satisfying `hsub`,
`hBfin`, `hblockFin` and `hplace` **jointly and nondegenerately** -- `Bfin` the
certificate's own routed row set rather than `Finset.univ`, `plc` pinned to
`09:1235--1236`'s re-tagging (a pin, not a nonidentity claim: it agrees with the
identity on the slab) -- over the coordinate slab `R` of `09:1235--1236`;
`finalBlock_bundle_inputs_are_legal` supplies that slab family and its
`hR` retention.  `hcomp` is **not** republished there: it is the banked
`RoutingDynamics.completedNoBob_aliceLadder` (`lem:wrapper-no-bob-completion`,
`09:1195--1213`), consumed by pin at the call site.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet `Yc`, the
Alice carrier `X`, in `q`, `r`, `b_T`, `k_ref`, `C`, `E_0`, the retained column set,
and the block and placement families. -/
theorem canonical_hfinal_of_reference_construction {RwN : Type*}
    {r bT kref C : ℕ} {E0 : Finset (Fin q)}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (hcost : P.cost ≤ C + r - 1)
    {Scol : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (Bfin : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Finset X)
    (hBfin : ∀ x, ((canonicalSystem hcomp hR).cert x).rows ≤ (Bfin x).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblockFin : ∀ (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
      (x : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r),
      x.2.val = v.val → ∀ a ∈ Bfin x, plc v x.1 a ∈ rowsAt P (R x.1) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c) :
    ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ finalWeight (canonicalFinalCert hcomp hR v) := by
  classical
  intro v hv
  have hfb : (canonicalSystem hcomp hR).firstBob v = false := by
    simpa [WrapperFrontier.finalNodes, RoutedSystem.toWrapperFrontier] using hv
  refine canonical_frontierWeight_le_finalWeight_of_card_le_one hcomp hR ?_
  refine certsAtNode_card_le_one_of_construction_supply Nmat Gmat ιR hsub halleged
    (canonicalSystem hcomp hR) startedIdx startedIdx_injective startedIdx_notMem_E0
    hfb hX hYc hC hcost (TranscriptLevelSuccessors.xTdepth_pos bT)
    (twoCopy_row_legality_of_gate (by omega) hgate) hbase
    (le_of_eq (initialRefRows_is_the_twoCopy_block_floor (xTdepth bT) (Fintype.card X)))
    (by omega) hcover Bfin (plc v) hBfin ?_ (hplace v)
  -- the row localization, one certificate at a time (`09:1291--1296` at `kappa_v = 1`)
  intro x hxv a ha
  exact SelectDischarge.routeRows_of_mem_rowsAt
    (hblockFin v x (congrArg Subtype.val hxv) a ha)

end CanonicalFinalRealization

/-! ## §4  `eq:wrapper-clean-count` with `hlight` retired (`09:1346--1365`) -/

section CleanCount

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-clean-count` (`09:1352--1357`) at the canonical system, with
`hlight` retired.**

`c >= q - e_0/(1-vartheta)` and `K_B + ell <= e_0/(1-vartheta)`.

`FrontierIndexing.canonical_cleanCount` is consumed **verbatim, at its own
interface**; what changes is that its `hlight` argument is now supplied by
Section 2 instead of assumed, and its `hcoord` argument is evaluated from
`09:450`'s definition of `e_0` rather than assumed.  The banked statement is
untouched -- a binder can only be retired where it is consumed, and this is that
site.

**What still enters as a binder, and why.**

* `hq : (q : ℝ) = 2^r` is `09:105`'s width identification, "Let `q = 2^r` be the
  scale-alignment width".  It is the banked theorem's own binder and is passed
  through unchanged; `q` is otherwise FREE in this module.
* `hfinal` is the final-node classification of `09:1346--1350` --
  "every final Alice node contains either one clean certificate, one half-weight
  descendant of a split certificate, or none".  What licenses it is
  `lem:final-reference-uniqueness` (`09:1315--1344`), banked as
  `DenseWrapperFrontier.wrapperFinalReferenceUniqueness` with its own `hladder`
  binder.  **That arc is now wired** (§4a): this general form keeps `hfinal` and
  a free `certOpt`, so a consumer that bounds the final-node weight by other
  means can still use it, while
  `canonical_cleanCount_of_reference_construction_and_twoCopy` below is the same
  conclusion with `hfinal` retired and `certOpt` derived.
* `hLocEx` (`A:109--146`), where **EXPANDER-001** would enter, survives exactly
  as in Section 2.

**No route completion is claimed.**  `eq:wrapper-u-dense` needs `09:1367--1781`
in addition; see the header census.  What this conclusion supplies downstream is
the `hKB` slot of `MassRedistributionCounting.wrapperTotalEarlyMass_engine`
(`09:1526--1534`'s replacement of `K_B` by `e_0/(1-vartheta)`), obtained from the
second conjunct by `cleanCount_supplies_the_earlyMass_slot`.

*Why the trivial witness fails.*  Neither conjunct is existential.  The first is
not a formal truth: the banked `DenseWrapperFrontier.cleanCount_needs_kraft`
exhibits data satisfying the conservation comparison where
`c >= q - e_0/(1-vartheta)` fails outright, so `09:1364`'s Kraft line -- supplied
here, not assumed -- is load-bearing.  The second is not vacuous either: the
banked `SplitFirstBobInstance.split_cleanCount_second_conjunct_is_live` carries a
routed instance at which `K_B > 0` and `ell > 0`, so the frozen ceiling is
checked against a genuine positive quantity rather than against zero.

General in the same data as Section 2, plus the certificate assignment. -/
theorem canonical_cleanCount_of_reference_construction {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ C - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [c])).cost)
    {Scol : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (B : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → Finset X)
    (hB : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B v j).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblock : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B v j, plc v j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
    (hfinal : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ finalWeight (certOpt v)) :
    (q : ℝ) - (E0.card : ℝ) / (1 - vartheta)
        ≤ (((canonicalSystem hcomp hR).toWrapperFrontier.cleanNodes certOpt).card : ℝ)
      ∧ (canonicalSystem hcomp hR).toWrapperFrontier.bobCapacity
          + (((canonicalSystem hcomp hR).toWrapperFrontier.splitNodes certOpt).card : ℝ)
        ≤ (E0.card : ℝ) / (1 - vartheta) :=
  canonical_cleanCount hcomp hR certOpt hq
    (startedCoord_census_evaluates_e_zero (q := q) E0).le
    (canonical_firstBob_light_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR
      hmem hk hq4 hX hYc hθ0 hθ1 hC hgate hbase htcert hE1 hE2 hcost hLocEx hcover
      B hB plc hblock hplace)
    hfinal

/-! ### §4b  `eq:wrapper-clean-count` with **`hfinal` retired as well**
(`09:1315--1365`) -/

/-- **`eq:wrapper-clean-count` (`09:1352--1357`) at the canonical system, with
BOTH `hlight` and `hfinal` retired, and the certificate assignment derived.**

`c >= q - e_0/(1-vartheta)` and `K_B + ell <= e_0/(1-vartheta)`.

This is `canonical_cleanCount_of_reference_construction` with its last two free
inputs removed:

* the certificate assignment is no longer a parameter -- it is
  `canonicalFinalCert`, the `09:1346--1347` trichotomy **read off the routing**
  (§4a), so `c` and `ell` now count the nodes the construction actually puts a
  clean or a split certificate at, not the nodes an arbitrary labelling names;
* `hfinal` is no longer assumed -- it is
  `canonical_hfinal_of_reference_construction`, i.e.
  `lem:final-reference-uniqueness` (`09:1315--1344`) consumed by pin as
  `DenseWrapperFrontier.wrapperFinalReferenceUniqueness`, with its `hdistinct`
  slot discharged by the routed system's own `coordUnique` (`09:1322--1324`), its
  `hsuffix` slot discharged from `hcost` by
  `RoutedCertificateSystem.RoutedSystem.final_residual_budget`
  (`09:1341--1343`) and by `finalPair_ladder_contradiction` at a genuine pair, and
  its `hladder` slot discharged by the banked
  `DenseWrapperFrontier.finalNode_twoCopy_bound` -- the `ell = 1` call of
  `09:1334--1338` at `(M,H,x,z,ell) = (G, C-1, x_T, y, 1)`.

**What enters in exchange, and exactly how strong it is.**  Three further pieces of
**construction data**, and no inequality on a cost: `Bfin`, the G-row block of each
certificate's own copy of `G`; `hBfin`, that it realizes that certificate's
reference-row count (which `finalNode_cert_rows_ge_initialRefRows` then floors at
`09:1325--1328`'s `A_0`); and `hblockFin`, that its placement under the **existing**
`plc` lands in `RoutingDynamics.rowsAt` at the certificate's own address.  `hfinal`
was a binder in the *shape of the conclusion* -- it asserted the very weight bound
the counting spine needs at every final node, at a certificate labelling that was
itself a free parameter -- and the predecessor round's replacement `hrealize`
(`Lambda_G(2, 2x_T, y^2) <= cost(subtree at v)` per distinct-coordinate pair) was no
better: under this declaration's own `hcost` and the banked ladder bound it is false
at every such pair, so it merely renamed the conclusion.  **It is gone.**  What
remains mentions no cost, complexity, density or weight at all; the two-coordinate
column clause of `09:1331--1332`, the route localizations, and the reference-copy
embedding of `09:105--123` are all **derived** at
`canonical_hfinal_of_reference_construction`, the last of them by consuming the
**banked** `SELECT-EMBED-001` owner
`SelectEmbedComposition.interlaceFun_reference_copy`, which is a proved theorem and
not a live STOP.

**Consistency (LANE-GATE 3).**  Nothing in the final-node bundle quantifies over
a pair of certificates, so Battery 10's `conclusion -> premise` direction has
nothing to act on.  Satisfiability is claimed **jointly**, not field by field:
Battery 11c (`finalBlock_bundle_joint_inhabitant`) exhibits one choice of `Gmat`,
`iota_R`, `g`, `plc` and `Bfin` meeting `hsub`, `hBfin`, `hblockFin` and `hplace`
at once, nondegenerately (`Bfin` the certificate's own routed row set, `plc` the
genuine coordinate placement), with every schedule parameter free; Battery 11b
supplies the `09:1235--1236` slab family, its `09:1233--1235` retention and its
coordinate tagging -- **not** the protocol and **not** the frame, which is the
banked `RoutingDynamics.completedNoBob_aliceLadder` consumed by pin.  Battery 11d
composes 11b with 11c at `q = 2^r` and the evaluated `A_0`, with the degeneracies
excluded, so the joint instance is exhibited and not merely available.  Battery
11a's `Bfin := fun _ => Finset.univ` settles `hBfin` in isolation and is
explicitly the WEAK half.

**What is still not claimed.**  `eq:wrapper-u-dense`: the header census marks
`09:1700--1781` OPEN and this statement does not touch it.  `hLocEx`
(`A:109--146`, where **EXPANDER-001** would enter), `hE1`, `hE2`, `htcert`,
`halleged` and `hcost` survive exactly as in Section 2.

*Why the trivial witness fails.*  Neither conjunct is existential, and both
inherit the poles of `canonical_cleanCount_of_reference_construction`: the first
is not a formal truth (`DenseWrapperFrontier.cleanCount_needs_kraft`), and the
second is not vacuous (`SplitFirstBobInstance.split_cleanCount_second_conjunct_is_live`).
For the newly derived classification specifically, the trivial choice
`fun _ => none` would falsify the `hfinal` bound at any node carrying a
certificate (the banked `DenseWrapperFrontier.finalWeight_none` against
`canonicalFinalCert_eq_none_iff`), so `canonicalFinalCert` is not a placeholder.

General in the same data as Section 2, plus the final-node block family
`09:1325--1328` supplies. -/
theorem canonical_cleanCount_of_reference_construction_and_twoCopy {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ C - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [c])).cost)
    {Scol : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (B : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → Finset X)
    (hB : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B v j).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblock : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B v j, plc v j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
    (Bfin : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Finset X)
    (hBfin : ∀ x, ((canonicalSystem hcomp hR).cert x).rows ≤ (Bfin x).card)
    (hblockFin : ∀ (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
      (x : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r),
      x.2.val = v.val → ∀ a ∈ Bfin x, plc v x.1 a ∈ rowsAt P (R x.1) v.val) :
    (q : ℝ) - (E0.card : ℝ) / (1 - vartheta)
        ≤ (((canonicalSystem hcomp hR).toWrapperFrontier.cleanNodes
              (canonicalFinalCert hcomp hR)).card : ℝ)
      ∧ (canonicalSystem hcomp hR).toWrapperFrontier.bobCapacity
          + (((canonicalSystem hcomp hR).toWrapperFrontier.splitNodes
                (canonicalFinalCert hcomp hR)).card : ℝ)
        ≤ (E0.card : ℝ) / (1 - vartheta) := by
  refine canonical_cleanCount_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR
    (canonicalFinalCert hcomp hR) hq hmem hk hq4 hX hYc hθ0 hθ1 hC hgate hbase htcert
    hE1 hE2 hcost hLocEx hcover B hB plc hblock hplace ?_
  exact canonical_hfinal_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR
    hk hq4 hX hYc hC hgate hbase hcost hcover Bfin hBfin plc hblockFin hplace

end CleanCount

/-! ## §5  Aux-lemma battery

Six further general checks on the assembly, after §1's census, §4a-0's two
(`twoCoord_rho_exceeds_y_sq`, `finalPair_margin_is_exactly_one_bit`) and §4a's
four (`mem_certsAtNode`, `sum_card_certsAtNode`, `canonicalFinalCert_eq_none_iff`,
`pair_premise_is_vacuous_at_a_thin_node`, the last of which states the
**structural ban** the module now enforces: every premise quantified over a pair
of certificates at a final node is implied by the conclusion, hence
conclusion-equivalent, hence forbidden -- it is not, and may not be used as, a
consistency receipt for anything).

Batteries 11b, 11c and 11d are this round's LANE-GATE 3 receipts for the
final-node block bundle: 11b exhibits the `09:1235--1236` slab family with its
exact row count, its `09:1233--1235` retention and its coordinate tagging; 11c
exhibits a **joint** inhabitant of `(hsub, hBfin, hblockFin, hplace)` over an
arbitrary such family; and **11d writes the composition down** at the
construction point, with `q = 2^r` substituted and `A_0` in its evaluated closed
form, so the receipt is an exhibited instance rather than an available one.  The
`CompletedNoBob` frame those receipts run under is **not** restated by any of
them: `lem:wrapper-no-bob-completion` (`09:1195--1213`) is the banked
`RoutingDynamics.completedNoBob_aliceLadder` and is consumed **by pin** inside
11d, never as a conjunct.
Battery 11a is the retained WEAK half (`hBfin` alone, at
`Bfin := fun _ => Finset.univ`) and is labelled as such.

Canonical inhabitation remains INHERITED, REGISTERED and DEFERRED per the header:
the paper's own instance of every statement above is a function of the **alleged**
protocol of `09:1187--1193`, which does not exist, so no paper instance can be
exhibited and **no battery below discharges that obligation** -- 11b, 11c and 11d
are NON-FIDELITY probes in the precise sense that they show satisfiability at
legal parameters, never that the bundle holds of the frozen object.  Every
battery below is generic in the schedule except **11d**, which is the one that
performs the construction-specific substitutions the receipt requires -- `q = 2^r`
(`09:105`) and `A_0 = initialRefRows (xTdepth bT) |W|` (`09:1219` at `06:243`'s
`x_T = 2^{-b_T}`) -- and does so by writing the DEFINED terms, never a numeral. -/

section Battery

/-- **Battery 11a (`hBfin` alone is inhabited, and this is the WEAK half).**

`canonical_hfinal_of_reference_construction` and
`canonical_cleanCount_of_reference_construction_and_twoCopy` carry the
`09:1325--1328` block family through the binder
`hBfin : forall x, ((canonicalSystem ...).cert x).rows <= (Bfin x).card`.  That
binder alone is satisfied outright by the total choice `Bfin := fun _ => Finset.univ`,
and this proves it: a routed certificate's `rows` field is the *cardinality* of the
`Finset X` the routing cuts (`RoutingDynamics.RoutedRowCertificate.toRoutedCertificate`,
`09:1238--1239`), so it never exceeds `|X|`.

**This receipt settles one field of a four-field bundle and is not, on its own,
a non-vacuity receipt for that bundle.**  `Bfin := fun _ => Finset.univ` says
nothing about `hblockFin` (the block is genuinely *placed* inside the
certificate's retained rows) or about `hplace` (it carries the reference copy of
`09:105--123`), and a bundle can have each field separately inhabited while no
single choice satisfies them together.  The JOINT receipt is
`finalBlock_bundle_joint_inhabitant` below, whose witness is nondegenerate --
`Bfin` the certificate's own routed row set rather than `Finset.univ`, `plc`
pinned to `09:1235--1236`'s re-tagging rather than left free -- and whose slab
inputs `R`, `hR` and `hslab` are themselves exhibited at legal values by
`finalBlock_bundle_inputs_are_legal`.  Those two are **composed, at the
construction point and with the degeneracies excluded**, by
`finalBlock_bundle_joint_inhabitant_at_the_construction_point`, whose `P` and
`hcomp` are the banked `RoutingDynamics.completedNoBob_aliceLadder`
(`lem:wrapper-no-bob-completion`, `09:1195--1213`) consumed **by pin**, not a
republished conjunct of any battery.

Canonical inhabitation -- the paper's **own** instance rather than any instance --
remains the inherited REGISTERED and DEFERRED obligation of the header, and
neither receipt discharges it: the frozen instance is a function of the alleged
protocol of `09:1187--1193`, which does not exist.

General in the carriers, the coordinate type, the protocol, `A_0`, `r` and the
certificate index; nothing is evaluated. -/
theorem finalBlock_supply_is_inhabited {X Y Z : Type*} [Fintype X] [DecidableEq X]
    {Coord : Type} [Fintype Coord] {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r)
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) (x : CertIndex P R A0 r) :
    ((canonicalSystem hcomp hR).cert x).rows ≤ (Finset.univ : Finset X).card :=
  Finset.card_le_card (Finset.subset_univ _)

/-- **Battery 11b (LANE-GATE 3: the final-node bundle's SLAB inputs are legal).**

`finalBlock_bundle_joint_inhabitant` runs over a protocol, a `CompletedNoBob`
frame and a coordinate-slab reference family.  This exhibits the **slab family**
at legal, nondegenerate parameters, so that receipt is not a statement about an
empty hypothesis set.

**The protocol frame is deliberately NOT a conjunct here.**
`lem:wrapper-no-bob-completion` (`09:1195--1213`, with the completed Alice ladder
constructed at `09:1203--1207`) is owned by the banked
`RoutingDynamics.completedNoBob_aliceLadder` at
`aliceLadder (X := Fin q x W) (Y := Fin q -> Yc) aq z r` -- general in the leaf
output label `z`, which `09:1204` **retains** rather than fixes -- and a consumer that
needs the frame invokes **that owner directly by pin**.  Bundling it in as a
conjunct here would republish a banked owner's statement at a specialization
under a new name, which the fixed-interface rule forbids however fresh the
remaining conjuncts are.  The three conjuncts below are the genuinely fresh
content:

* the reference family is `09:1235--1236`'s own placement read literally: the
  certificate started in coordinate `j` holds reference rows of the copy of `G`
  that sits **at coordinate `j`**, i.e. the slab `{startedIdx j} x W` of the
  interlaced Alice alphabet `Fin q x W` (`09:105--116`), and that slab has
  **exactly** `|W|` rows.  That count is all the first conjunct claims: the sole
  hypothesis is `hW : refRowFloor A_0 r <= |W|`, which at `A_0 = 0` is vacuous,
  so **this declaration does not establish that the slab is nonempty, that
  `StartedCoord E_0` is nonempty, or that the slab is a proper subset of
  `Fin q x W`** -- the first two would need `0 < |W|` resp. an inhabitant of
  `StartedCoord E_0`, and the third `2 <= q`.  Those guards are supplied where
  they are needed, at the construction point, by
  `finalBlock_bundle_joint_inhabitant_at_the_construction_point`;
* the retention `A_r <= |R j|` of `09:1233--1235` then holds as soon as the row
  carrier is large enough, which is the single hypothesis `hW`;
* every row of the slab carries the started coordinate's tag, which is the
  `hslab` input `09:1235--1236` forces and which
  `finalBlock_bundle_joint_inhabitant` consumes.

Nothing is evaluated: `r`, `A_0`, `q`, `E_0` and `W` stay free, so the receipt is
available at every legal schedule point (in particular at `k_ref = 4`,
`k_ref + 2 <= r` and `q = 2^r`) and not only at some convenient one.

General in the row carrier, `q`, `r`, `A_0` and `E_0`. -/
theorem finalBlock_bundle_inputs_are_legal {W : Type*} [Fintype W] [DecidableEq W]
    {q r A0 : ℕ} {E0 : Finset (Fin q)}
    (hW : refRowFloor A0 r ≤ Fintype.card W) :
    (∀ j : StartedCoord E0,
        ((Finset.univ : Finset W).image fun w => ((startedIdx j, w) : Fin q × W)).card
          = Fintype.card W)
    ∧ (∀ j : StartedCoord E0,
        refRowFloor A0 r
          ≤ ((Finset.univ : Finset W).image fun w => ((startedIdx j, w) : Fin q × W)).card)
    ∧ (∀ (j : StartedCoord E0) (x : Fin q × W),
        x ∈ (Finset.univ : Finset W).image (fun w => ((startedIdx j, w) : Fin q × W)) →
          x.1 = startedIdx j) := by
  have hcard : ∀ j : StartedCoord E0,
      ((Finset.univ : Finset W).image fun w => ((startedIdx j, w) : Fin q × W)).card
        = Fintype.card W := by
    intro j
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2)]
    exact Finset.card_univ
  refine ⟨hcard, fun j => (hcard j).symm ▸ hW, ?_⟩
  intro j x hx
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hx
  exact (congrArg Prod.fst hw).symm ▸ rfl

/-- **Battery 11c (LANE-GATE 3: a NONDEGENERATE JOINT inhabitant of the whole
final-node bundle `(Bfin, hBfin, hblockFin, hplace)`).**

`canonical_hfinal_of_reference_construction` and
`canonical_cleanCount_of_reference_construction_and_twoCopy` carry four pieces of
construction data together -- `hsub` (the reference copy is a row-submatrix of the
ambient matrix, `09:113--116`), `hBfin`, `hblockFin` and `hplace`.  Battery 11a
settles `hBfin` in isolation, which proves nothing about the bundle.  This
exhibits **one** choice of `Gmat`, `iota_R`, `g`, `plc` and `Bfin` satisfying all
four **simultaneously**, over the coordinate slab `R` of `09:1235--1236` (Battery
11b exhibits one, with its retention and its coordinate tagging) and over any
protocol at all with the `09:1195--1213` frame -- for which the banked
`RoutingDynamics.completedNoBob_aliceLadder` is the owner, consumed **by pin** at
the call site rather than restated by any battery of this module.  **That call
site is Battery 11d** (`finalBlock_bundle_joint_inhabitant_at_the_construction_point`),
which is where this receipt and 11b are actually composed, at `q = 2^r` and the
evaluated `A_0`, with the degeneracies excluded.

The witness is read off `09:105--123` rather than invented:

* Alice's alphabet is the interlaced one, `Fin q x W` -- a *(coordinate, row)*
  pair, which is exactly what `interlaceFun` takes;
* `iota_R := Prod.snd` and `Gmat := N` on the row component, so `hsub` is
  `09:113--116` at equality: the reference copy of `G` at each coordinate *is* the
  ambient matrix on those rows;
* `g` is the `q`-fold interlace itself (`09:107`), so `hplace` is `09:113--116`
  read forwards;
* `plc v j a` places a row into the copy that sits at coordinate `startedIdx j`,
  which is `09:1235--1236`'s "start one clean reference certificate in every
  coordinate outside `E_0`";
* `Bfin x` is the certificate's **own routed row set** `RoutingDynamics.rowsAt`
  at its own address (`09:1238--1239`), so `hBfin` holds with equality.

*Why the trivial witness fails.*  This IS existential, so the pole matters: the
last two conjuncts **pin** `Bfin` and `plc` outright, so a would-be trivial
witness has no freedom at all in those two components -- `Bfin := fun _ =>
Finset.univ` (Battery 11a's weak choice) is excluded by the fifth conjunct, and
`plc := fun _ _ a => a` is excluded by the sixth unless every reference row
already sits at its own coordinate.  With `Bfin` and `plc` pinned, the third
conjunct (`hblockFin`) is a real constraint on `R` and is what `hslab` pays for,
and the fourth (`hplace`) is a real constraint on `g` and is what forces `g` to
be `09:107`'s interlace rather than an arbitrary function.

**Nondegeneracy is therefore pinned in the statement, not asserted in prose**, and
every parameter (`q`, `r`, `A_0`, `E_0`, the carriers, the protocol, the retained
column set) is left free, so the receipt is available at legal schedule points
rather than at one convenient instance.

**What this is NOT.**  It is not canonical inhabitation: the paper's own instance
is a function of the alleged protocol of `09:1187--1193`, and that obligation
stays REGISTERED and DEFERRED per the header.  This receipt is a NON-FIDELITY
probe in that precise sense -- it shows the bundle is jointly satisfiable at
legal parameters, never that it holds of the frozen object.

**AND IT IS AN OPEN TARGET on a second, independent leg.**  Firing this battery
at a *closed* public input would need one, and `def:level-public-input`
(`05:13--14`) is instantiated **nowhere** in the frozen release (zero matches for
any closed instance across the whole frozen source).  A project-created tuple
cannot stand in: under the DEFINED-VS-FREE witness rule its self-chosen fields
confine it to declarations claiming no legality.  So the closed external firing
of this row is a **target**, the legality leg is a REGISTERED DEFERRAL recorded
with anchors in `FrontierScheduleReceipt`'s header, and every downstream firing
that does exist is universally quantified in the record.  No sentence in this
module may report that discharge as achieved.

General in the row carrier, the per-coordinate alphabet, `q`, `r`, `A_0`, `E_0`,
the protocol and the retained column set. -/
theorem finalBlock_bundle_joint_inhabitant {W : Type*} [Fintype W] [DecidableEq W]
    {Yc : Type*} {q r A0 : ℕ} {E0 : Finset (Fin q)}
    (Nmat : W → Yc → Bool)
    {P : Protocol (Fin q × W) (Fin q → Yc) Bool} (hcomp : CompletedNoBob P r)
    {R : StartedCoord E0 → Finset (Fin q × W)}
    (hR : ∀ j, refRowFloor A0 r ≤ (R j).card)
    (hslab : ∀ (j : StartedCoord E0) (x : Fin q × W), x ∈ R j → x.1 = startedIdx j)
    (Scol : Finset (Fin q → Yc)) :
    ∃ (Gmat : (Fin q × W) → Yc → Bool) (ιR : (Fin q × W) → W)
      (g : (Fin q × W) → (Fin q → Yc) → Bool)
      (plc : FrontierNode P R A0 r → StartedCoord E0 → (Fin q × W) → (Fin q × W))
      (Bfin : CertIndex P R A0 r → Finset (Fin q × W)),
      (∀ a c, Gmat a c = Nmat (ιR a) c)
      ∧ (∀ x, ((canonicalSystem hcomp hR).cert x).rows ≤ (Bfin x).card)
      ∧ (∀ (v : FrontierNode P R A0 r) (x : CertIndex P R A0 r), x.2.val = v.val →
          ∀ a ∈ Bfin x, plc v x.1 a ∈ rowsAt P (R x.1) v.val)
      ∧ (∀ (v : FrontierNode P R A0 r) (j : StartedCoord E0) (a : Fin q × W),
          ∀ c ∈ Scol, g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
      ∧ (∀ x : CertIndex P R A0 r, Bfin x = rowsAt P (R x.1) x.2.val)
      ∧ (∀ (v : FrontierNode P R A0 r) (j : StartedCoord E0) (a : Fin q × W),
          plc v j a = (startedIdx j, a.2)) := by
  classical
  refine ⟨fun x c => Nmat x.2 c, Prod.snd, fun x c => Nmat x.2 (c x.1),
    fun _ j a => (startedIdx j, a.2), fun x => rowsAt P (R x.1) x.2.val,
    fun _ _ => rfl, fun _ => le_refl _, ?_, fun _ _ _ _ _ => rfl,
    fun _ => rfl, fun _ _ _ => rfl⟩
  intro v x hxv a ha
  have hmem : a ∈ R x.1 := (Finset.mem_inter.mp ha).1
  have ha1 : startedIdx x.1 = a.1 := (hslab x.1 a hmem).symm
  dsimp only
  rw [ha1, ← hxv]
  exact ha

/-- **Battery 11d (LANE-GATE 3: the joint inhabitant WRITTEN DOWN at the
construction point -- a NON-FIDELITY receipt).**

Batteries 11b and 11c are each conditional: 11b exhibits the slab family at a
free `q`, `r`, `A_0` and `E_0`, and 11c exhibits the bundle over *any* protocol
carrying the `09:1195--1213` frame and *any* retaining slab family.  Their
composition was therefore available but **unwritten**, and an available
composition is not a receipt: LANE-GATE 3 asks for the joint nondegenerate
instance to be exhibited **in the tranche**.  This is that instance.

**Three things are consumed BY PIN and none is restated:**

* the protocol frame is the banked
  `RoutingDynamics.completedNoBob_aliceLadder` at
  `aliceLadder (Y := Fin (2^r) -> Yc) aq z r`, i.e.
  `lem:wrapper-no-bob-completion` (`09:1195--1213`, the ladder constructed at
  `09:1203--1207`).  It is applied, never republished: **`CompletedNoBob` is not
  a conjunct of the statement below**, and the only place the owner appears is
  as an argument of `canonicalSystem` inside the `hBfin` conjunct, where the
  routed system it indexes is what is being spoken about;

**The leaf output label `z` is a BINDER, because `09:1204` retains it.**  The
completion proof reads "append `r-d` fixed Alice messages and **retain the
original output label** at the new leaf" (`09:1203--1205`); the frozen text
therefore fixes the *shape* of the completed prefix and explicitly declines to
fix its output.  A previous form of this statement wrote `aq false r` at all ten
sites below, which pins the retained label to `false` at every completed leaf --
an over-specialization the frozen sentence contradicts, and the STATEMENT POLES
class in which an over-strong hypothesis typechecks perfectly.  The banked owners
`RoutedCertificateSystem.aliceLadder (a) (z)` and
`RoutingDynamics.completedNoBob_aliceLadder (a) (z) (r)` are already general in
`z`, so the receipt is stated for **every** retained label and nothing is paid
for the generality.  `z` is a universal binder here, never existentially chosen;
* the slab family and its two properties are Battery 11b
  (`finalBlock_bundle_inputs_are_legal`), applied at the instantiation below;
* the bundle itself is Battery 11c (`finalBlock_bundle_joint_inhabitant`),
  applied to those two.

**The construction-specific instantiations are performed, not left free.**
`q = 2^r` of `09:105` is substituted -- the width binder is gone and the outer
coordinate type is literally `Fin (2^r)` -- and `A_0` is written in its evaluated
closed form `initialRefRows (xTdepth bT) |W|`, which is `09:1219`'s
`A_0 = ceil(2 x_T m_G)` at `x_T = 2^{-b_T}` (`06:243`) and at the reference
matrix's own row count `m_G = |W|` (`09:113--116`).  Neither quantity is a free
binder here, and neither is replaced by a numeral.

**The Stage-3 depth `b_T` is PINNED to its `06:241` defining display, not chosen.**
`06:237--243` fixes the auxiliary depth in one aligned display:
`k_T = log_2(s/4)` (`06:239`), `b_T = 2^{j_49(k_T)}` (`06:241`),
`x_T = 2^{-b_T}` (`06:243`), on top of `s = 2^{ceil(B_s u^2)}`
(`06:118`, `eq:s-choice`) with `06:122` "Thus `s` is a public power of two".
`b_T` is therefore a **DEFINED** quantity, and a numeral standing in its place
(`b_T = 3`, `b_T = 19`) is an authoring defect even when every visible gate
passes.  The three hypotheses `hkT`, `hbT`, `hgate` write that chain out:

* `hu : u = uAux (Apre b_out B_pub z_R clE)` is the second line of `eq:s-choice`,
  `u = clog_2(clog_2(A_pre + 16))` (`06:116--117`) over `A_pre` of `06:111--115`,
  through the banked `ParameterSchedule.uAux` / `.Apre`.  `u` is a DEFINED
  quantity too, so it may not enter as a free binder either;
* `hkT : sScale B_s u / 4 = 2^{k_T}` is `06:239` in the exponent form `06:122`
  licenses, over the banked `ParameterSchedule.sScale` (`eq:s-choice`, `06:118`);
* `hbT : b_T = 2^{j_49(k_T)}` is `06:241` itself, over the banked
  `ParameterSchedule.j49` (`06:77--78`), which is **not** redefined here;
* `hgate : B_s u^2 < b_T` is the third row of `eq:hard-seed-width-gates`
  (`06:267`, "`log_2 s < b_T`"), read through `sScale_eq_pow`'s
  `log_2 s = B_s u^2`.

**`B_s` IS A SOURCE-DEFINED QUANTITY, and it is a binder here only because its
owner is downstream.**  An earlier form of this paragraph read `06:263` ("the
finite search fixing `B_s`") as leaving `B_s` free.  That reading is
**WITHDRAWN**: `06:263` is a USE site referring back to `02:815--819`, which
*defines* `B_s` -- "Let `T` be the least integer with `T >= 64`,
`9T^2 - 2 >= m_HS` ... and set `B_s = T^2`.  This is a terminating search" --
and that display has a banked owner, `MechanicalCompilerResidue.bsSched`
(`:3742`) over `.tLeast` (`:3739`).  Reading a use site as a definition is the
USE-AS-DEFINITION class outright, and it is what let a numeral (`B_s = 112`,
not a square) stand at an instantiation in the withdrawn `cc-t8h` receipt.

That owner's home is **downstream of this module**
(`MechanicalCompilerResidue.lean:11` -> `MassRedistributionTail.lean:3` ->
`ProtectedRowReservoirs.lean:2` -> `ProtectedEarlyClosure.lean:1` -> here), so
naming it here would close an import cycle and re-authoring it here would
duplicate a banked owner.  Accordingly `B_s` stays an **explicit binder of this
statement**, exactly as `k_T` and `b_T`'s links do, and the instantiation at the
paper's own value is performed **externally**, in the module downstream of both:
`FrontierScheduleReceipt.paperSchedulePins_hold_at_the_derived_point` supplies
all four pins at `B_s = MechanicalCompilerResidue.bsSched` together with **all
three** rows of `eq:hard-seed-width-gates` (`06:264--269`), which `02:838--839`
says K1 proves rather than assumes, and
`FrontierScheduleReceipt.finalBlock_receipt_fires_at_the_derived_point` fires
this battery there.  Those are forward record pointers to a downstream consumer,
never pins of this module.

**THIS DECLARATION IS AN OPEN TARGET, not a discharged one.**  Stated as a
target rather than as an accomplishment, because a forward pointer to an
unbanked consumer is a forecast and forecasts are not premises:

* what the downstream module **does** close is the *schedule* leg -- `B_s`,
  `u`, `s`, `k_T`, `b_T`, `x_T` at the K1 values, and all three gate rows;
* what nothing closes, here or downstream, is the *legality* leg.
  `def:level-public-input` (`05:13--14`) defines a thirteen-component tuple and
  the frozen release **instantiates it nowhere** -- a search of the whole frozen
  source for a closed instance returns zero matches -- so no closed external
  firing of this battery carries a paper-legality claim, and none is asserted.
  That leg is a REGISTERED DEFERRAL, recorded with its anchors in
  `FrontierScheduleReceipt`'s header and transcribed to the route
  `OBLIGATION_LEDGER` at bank time;
* consequently the downstream firing is universally quantified in the public
  record, and the target for this row is: fire it at the frozen source's own
  closed public input, once such an input exists.

Genuinely free at this site are only the four public-record sizes `b_out`,
`B_pub`, `z_R`, `clE = clog_2(|E|+2)` that `06:111--115` feeds into `A_pre`,
which are properties of the input instance; at the external firing they are the
downstream accessors applied to a universally quantified record, never numerals
and never a manufactured tuple.  `u`, `k_T` and `b_T` are **not** free: `hu` and
`hbT` are their defining displays outright, and `hkT` determines `k_T` because
`m |-> 2^m` is injective on the naturals.

**Nondegeneracy is proved, not asserted.**  The four conjuncts before the bundle
are exactly the degeneracies Battery 11b does *not* rule out and whose absence
from its prose was the record defect of the preceding round: `1 <= A_0` (so the
row floor is a real constraint and `hblockFin` is not vacuous), `StartedCoord
E_0` inhabited (so the two `forall j` conjuncts and the bundle's own `plc`/
`hplace` quantifications are not vacuously true), `R j` nonempty at every started
coordinate (so the slab carries rows), and `R j` a **proper** subset of
`Fin (2^r) x W` (so the "slab" is not all of Alice's alphabet).  They are paid
for by `hr : 1 <= r`, `hW0 : 0 < |W|` and the started coordinate `j0`, the last
being `09:1235--1236`'s "start one clean reference certificate in every
coordinate outside `E_0`" read as a nonvacuity requirement rather than assumed
silently.

**NON-FIDELITY, and precisely so.**  This shows the bundle is jointly satisfiable
at a legal, nondegenerate schedule point.  It does **not** show that the bundle
holds of the frozen object: the paper's own instance is a function of the alleged
protocol of `09:1187--1193`, whose non-existence is the conclusion of the
argument, so canonical inhabitation stays REGISTERED and DEFERRED per the header
and no battery of this module discharges it.  The protocol used here is the
completed Alice ladder, which is a legal frame and is **not** the alleged
protocol.

General in the reference row carrier `W`, the per-coordinate alphabet `Yc`, the
depth `r`, the exceptional set `E_0`, the reference matrix, the ladder's Alice
predicate, **the retained leaf output label `z` (`09:1204`)**, the retained
column set, and the genuinely free source-scale inputs `B_s`, `b_out`, `B_pub`,
`z_R`, `clE`.  The auxiliary quantities `u`, `k_T` and `b_T` are **not** general:
they are pinned to `06:116--117`, `06:239` and `06:241` by `hu`, `hkT` and
`hbT`. -/
theorem finalBlock_bundle_joint_inhabitant_at_the_construction_point
    {W : Type*} [Fintype W] [DecidableEq W] {Yc : Type*} {r bT kT Bs u : ℕ}
    {bout Bpub zR clE : ℕ}
    {E0 : Finset (Fin (2 ^ r))} (j0 : StartedCoord E0)
    (Nmat : W → Yc → Bool) (aq : (Fin (2 ^ r) × W) → Bool) (z : Bool)
    (hr : 1 ≤ r) (hW0 : 0 < Fintype.card W)
    (hu : u = ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE))
    (hkT : ParameterSchedule.sScale Bs u / 4 = 2 ^ kT)
    (hbT : bT = 2 ^ ParameterSchedule.j49 kT)
    (hgate : Bs * u ^ 2 < bT)
    (hW : refRowFloor (initialRefRows (xTdepth bT) (Fintype.card W)) r
      ≤ Fintype.card W)
    (Scol : Finset (Fin (2 ^ r) → Yc)) :
    ∃ (R : StartedCoord E0 → Finset (Fin (2 ^ r) × W))
      (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card W)) r
        ≤ (R j).card),
      1 ≤ initialRefRows (xTdepth bT) (Fintype.card W)
      ∧ Nonempty (StartedCoord E0)
      ∧ (∀ j, (R j).Nonempty)
      ∧ (∀ j, R j ≠ (Finset.univ : Finset (Fin (2 ^ r) × W)))
      ∧ ∃ (Gmat : (Fin (2 ^ r) × W) → Yc → Bool) (ιR : (Fin (2 ^ r) × W) → W)
          (g : (Fin (2 ^ r) × W) → (Fin (2 ^ r) → Yc) → Bool)
          (plc : FrontierNode
              (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
              (initialRefRows (xTdepth bT) (Fintype.card W)) r →
            StartedCoord E0 → (Fin (2 ^ r) × W) → (Fin (2 ^ r) × W))
          (Bfin : CertIndex
              (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
              (initialRefRows (xTdepth bT) (Fintype.card W)) r →
            Finset (Fin (2 ^ r) × W)),
          (∀ a c, Gmat a c = Nmat (ιR a) c)
          ∧ (∀ x, ((canonicalSystem
                (RoutingDynamics.completedNoBob_aliceLadder
                  (Y := Fin (2 ^ r) → Yc) aq z r) hR).cert x).rows
              ≤ (Bfin x).card)
          ∧ (∀ (v : FrontierNode
                (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
                (initialRefRows (xTdepth bT) (Fintype.card W)) r)
              (x : CertIndex
                (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
                (initialRefRows (xTdepth bT) (Fintype.card W)) r),
              x.2.val = v.val → ∀ a ∈ Bfin x,
                plc v x.1 a ∈ rowsAt
                  (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) (R x.1) v.val)
          ∧ (∀ (v : FrontierNode
                (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
                (initialRefRows (xTdepth bT) (Fintype.card W)) r)
              (j : StartedCoord E0) (a : Fin (2 ^ r) × W), ∀ c ∈ Scol,
              g (plc v j a) c = interlaceFun Nmat (2 ^ r) (startedIdx j, ιR a) c)
          ∧ (∀ x : CertIndex
                (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
                (initialRefRows (xTdepth bT) (Fintype.card W)) r,
              Bfin x = rowsAt
                (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) (R x.1) x.2.val)
          ∧ (∀ (v : FrontierNode
                (aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r) R
                (initialRefRows (xTdepth bT) (Fintype.card W)) r)
              (j : StartedCoord E0) (a : Fin (2 ^ r) × W),
              plc v j a = (startedIdx j, a.2)) := by
  classical
  -- The three schedule pins are CARRIED, not consumed: they fix **which** `b_T`
  -- this receipt speaks about (`06:239`, `06:241`, `06:267`), while the bundle
  -- itself is built from the row geometry alone.  The downstream
  -- `FrontierScheduleReceipt` is where they are discharged at the paper's own
  -- `B_s = T^2`, together with all three rows of `eq:hard-seed-width-gates`.
  have _schedulePins :
      u = ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE)
        ∧ ParameterSchedule.sScale Bs u / 4 = 2 ^ kT
        ∧ bT = 2 ^ ParameterSchedule.j49 kT
        ∧ Bs * u ^ 2 < bT :=
    ⟨hu, hkT, hbT, hgate⟩
  obtain ⟨hcard, hret, hslab⟩ :=
    finalBlock_bundle_inputs_are_legal (W := W) (q := 2 ^ r) (r := r)
      (A0 := initialRefRows (xTdepth bT) (Fintype.card W)) (E0 := E0) hW
  refine ⟨_, hret, ?_, ⟨j0⟩, ?_, ?_,
    finalBlock_bundle_joint_inhabitant Nmat
      (RoutingDynamics.completedNoBob_aliceLadder (Y := Fin (2 ^ r) → Yc) aq z r)
      hret hslab Scol⟩
  · -- `1 <= A_0` at the EVALUATED `09:1219` point, from the banked positivity of
    -- `x_T = 2^{-b_T}` and `0 < |W|`.
    have hx : (0 : ℝ) < xTdepth bT := TranscriptLevelSuccessors.xTdepth_pos bT
    have hw : (0 : ℝ) < ((Fintype.card W : ℕ) : ℝ) := by exact_mod_cast hW0
    have hpos : (0 : ℝ) < 2 * xTdepth bT * ((Fintype.card W : ℕ) : ℝ) := by positivity
    have hceil := Nat.ceil_pos.mpr hpos
    unfold initialRefRows
    omega
  · -- every slab carries rows: its cardinality is `|W|`
    intro j
    refine Finset.card_pos.mp ?_
    rw [hcard j]
    exact hW0
  · -- and it is a PROPER subset of `Fin (2^r) x W`, because `2^r >= 2`
    intro j hj
    have h1 := hcard j
    rw [hj] at h1
    have h2 : (Finset.univ : Finset (Fin (2 ^ r) × W)).card
        = 2 ^ r * Fintype.card W := by
      simp [Finset.card_univ, Fintype.card_prod]
    rw [h2] at h1
    have h3 : 2 ^ r * Fintype.card W = 1 * Fintype.card W := by omega
    have h4 : (2 : ℕ) ^ r = 1 := Nat.eq_of_mul_eq_mul_right hW0 h3
    have h5 : 1 < (2 : ℕ) ^ r := Nat.one_lt_two_pow (by omega)
    omega

/-! ### §4c  The `06:237--243` schedule chain -- RE-SITED, not deleted

The five declarations that stood here (`sScale_quarter_eq_two_pow`,
`kT_pin_determines_kT`, `xTdepth_le_quarter_of_gate`,
`paperSchedulePins_are_jointly_satisfiable`,
`finalBlock_receipt_fires_at_the_pinned_schedule_point`) are **withdrawn from
this module** and their content is re-sited to the new
`EthInapproximability.ParameterizedNP.FrontierScheduleReceipt`, which imports
this module.  The reason is structural, not stylistic, and it is recorded here
so a later reader does not re-mint them.

**The defect they died of.**  `06:263` -- "the finite search fixing `B_s`" --
was read as leaving `B_s` free.  It is a USE site referring back to
`02:815--819`, which *defines* it: "Let `T` be the least integer with `T >= 64`,
`9T^2 - 2 >= m_HS` ... and set `B_s = T^2`.  This is a terminating search."
Under that misreading the joint-satisfiability receipt assigned `B_s = 112`, a
value no `T` yields, and it established only one of the three rows of
`eq:hard-seed-width-gates` although `02:838--839` says K1 proves all three.

**Why the repair could not be made here.**  The banked owner of `02:819` is
`MechanicalCompilerResidue.bsSched` (`:3742`), over `.tLeast` (`:3739`), and its
home is *downstream* of this module:

    MechanicalCompilerResidue.lean:11   imports MassRedistributionTail
    MassRedistributionTail.lean:3       imports ProtectedRowReservoirs
    ProtectedRowReservoirs.lean:2       imports ProtectedEarlyClosure
    ProtectedEarlyClosure.lean:1        imports FrontierSumAssembly

so pinning it here closes an import cycle, and re-authoring `tLeast`/`bsSched`
here duplicates a banked owner.  Both routes are closed by the IMPORT-DIRECTION
RULE; the remedy is a module downstream of both, and that is where the receipt
now lives.  The same wall was already recorded for `k_T` and `b_T`, whose banked
owners `ScheduleTemplateResidue.kT` (`:742`) and `.bT` (`:746`) sit on the same
downstream side; **Battery 11d's `hkT`, `hbT`, `hgate` and `hu` slots therefore
stay explicit equational hypotheses of this module**, naming their defining
displays, and are discharged externally.

**Where each withdrawn statement now lives** (forward record pointers to a
downstream consumer, never pins of this module):

* `sScale_quarter_eq_two_pow` -- superseded outright.  The banked
  `ScheduleTemplateResidue.kT_at_pow_two` (`:781`) is that arithmetic and is
  reachable from the new module, so the local restatement is not re-authored
  anywhere; the new module consumes the banked owner directly.
* `kT_pin_determines_kT` -- superseded by
  `FrontierScheduleReceipt.derivedKT_eq`, which proves the stronger fact that
  `06:239`'s `k_T = log_2(s/4)` and `02:834`'s closed form `k_T = T^2u^2 - 2`
  agree at the derived scale, instead of assuming a pin equivalent to its own
  conclusion.
* `xTdepth_le_quarter_of_gate` -- superseded by
  `FrontierScheduleReceipt.derivedXT_le_quarter`, at the **pinned** `b_T` rather
  than a free one.
* `paperSchedulePins_are_jointly_satisfiable` -- superseded by
  `FrontierScheduleReceipt.paperSchedulePins_hold_at_the_derived_point`, which
  carries no existential over the schedule at all: it is universally quantified
  over the public record, at `B_s = bsSched`, and it establishes all three gate
  rows.
* `finalBlock_receipt_fires_at_the_pinned_schedule_point` -- superseded by
  `FrontierScheduleReceipt.finalBlock_receipt_fires_at_the_derived_point` and
  `.finalBlock_receipt_fires_over_the_audit_carriers`, **both universally
  quantified in the public record**.  No closed public instance is formed there
  and none is formed here: `def:level-public-input` (`05:13--14`) is
  instantiated nowhere in the frozen release, so that leg is a REGISTERED
  DEFERRAL and this row stays an open target on it.

**CONSUMED BY PIN by that module, never re-authored here or there:**
`ParameterSchedule.sScale`/`.sScale_eq_pow`/`.uAux`/`.Apre`/`.three_le_uAux`/
`.j49`/`.j49_max`, `ScheduleTemplateResidue.kT`/`.bT`/`.kT_at_pow_two`/
`.hardSeedWidthGates`/`.hardSeedWidthGates_at_scheduled_scale`/
`.sScale_divisibility_row`, `MechanicalCompilerResidue.tLeast`/`.bsSched`/
`.tLeastSpec`/`.k1ScheduledComparisons`/`.k1HardSeedFloor`,
`HardSeedFacade.mHS`, `DenseStageFourOpening.xTdepth` with
`TranscriptLevelSuccessors.xTdepth_pos`/`.xTdepth_antitone`, and
`LevelStepConstruction.uAuxFor`/`.BpubFor`/`.zRFor`/`.clEFor`. -/

/-- **Battery 2 (the two-kappa trap).**

`kappa_v` takes two kinds of value on the frozen frontier, and conflating them
breaks the assembly.  At a first-Bob node `09:1259` gives `kappa_v >= 2`, so the
light threshold `vartheta kappa_v` is at least `9/8` and a weight-one clean
certificate fits under it.  At a final Alice node `09:1250--1252` forces
`d_v = r`, hence `kappa_v = 1` and `vartheta kappa_v = 9/16 < 1`, so the very
same display would *forbid* the clean certificate `09:1346--1347` places there.

Hence Section 2's conclusion is quantified over `bobNodes` and no wider: a
frontier-wide `hlight` is not a harmless strengthening but a contradiction with
the frozen final-node classification, and it would make the whole assembly
vacuous while every gate still passed.

General in the frontier and the node; nothing is evaluated. -/
theorem two_kappa_trap_at_the_final_nodes {r : ℕ} {V : Type*} (F : WrapperFrontier r V)
    {v w : V} (hv : F.firstBob v = true) (hw : F.firstBob w = false) :
    (1 : ℝ) < vartheta * ((F.capacity v : ℕ) : ℝ)
      ∧ vartheta * ((F.capacity w : ℕ) : ℝ) < 1
      ∧ ¬ (finalWeight (some CertKind.clean) ≤ vartheta * ((F.capacity w : ℕ) : ℝ)) := by
  have h2 : (2 : ℝ) ≤ ((F.capacity v : ℕ) : ℝ) := by
    exact_mod_cast F.two_le_capacity_firstBob hv
  have h1 : ((F.capacity w : ℕ) : ℝ) = 1 := by
    rw [F.capacity_final_eq_one hw]; norm_num
  refine ⟨by rw [vartheta_val]; linarith, ?_, ?_⟩
  · rw [h1, vartheta_val]; norm_num
  · rw [h1, vartheta_val, finalWeight_clean]
    norm_num

/-- **Battery 3 (the `vartheta` twins).**

`vartheta = 9/16` is declared twice in this development, from two different
frozen displays: `DenseWrapperFrontier.vartheta` is `09:1268`'s frontier weight
threshold -- the one `09:1310` and `eq:wrapper-clean-count` use, and the one
every statement above consumes -- while `ParameterSchedule.vartheta` is the
schedule constant of `eq:terminal-uniform-bounds` (`06:718`).

They are the same real number, and this records it.  The point is not the
arithmetic but the pin: a later tranche cannot silently swap the two names, and
cannot claim the assembly's threshold differs from the schedule's.

Nothing is evaluated here that the frozen source does not fix: both sides are
defined constants, and the lemma is their comparison. -/
theorem vartheta_twins_agree :
    DenseWrapperFrontier.vartheta = ParameterSchedule.vartheta := by
  rw [DenseWrapperFrontier.vartheta, ParameterSchedule.vartheta]

/-- **Battery 4 (the second conjunct supplies the early-mass slot).**

`09:1526--1534` replaces `K_B` by `e_0/(1-vartheta)` inside
`eq:wrapper-total-early-mass`, and the banked
`MassRedistributionCounting.wrapperTotalEarlyMass_engine` takes that replacement
as its `hKB` slot in the bare shape `K_B <= e_0/(1-vartheta)`.  Section 4's
second conjunct carries the split tally `ell` as well, so this is the drop that
matches the two interfaces -- the one step by which the assembly feeds the
protected-mass subsection.

It is stated generally on the abstract frontier, not at the canonical system, so
it commits to nothing about which routed system the consumer uses.

General in the frontier, the certificate assignment and the two reals. -/
theorem cleanCount_supplies_the_earlyMass_slot {r : ℕ} {V : Type*} [Fintype V]
    (F : WrapperFrontier r V) (cert : V → Option CertKind) {e0 : ℝ}
    (h : F.bobCapacity + ((F.splitNodes cert).card : ℝ) ≤ e0 / (1 - vartheta)) :
    F.bobCapacity ≤ e0 / (1 - vartheta) := by
  have hsplit : (0 : ℝ) ≤ ((F.splitNodes cert).card : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Battery 5 (both conclusions are monotone in the exceptional count).**

`e_0` enters `eq:wrapper-clean-count` only through `e_0/(1-vartheta)`, and
`09:452--453` records that the construction supplies an upper bound
`e_0 <= e_0^max` rather than the exact value.  A consumer that knows only the
bound must be able to weaken both conclusions to it, and this is that weakening:
enlarging `e_0` weakens the clean-count floor and relaxes the `K_B + ell`
ceiling, in the same direction.

Positivity of `1 - vartheta` is what makes the direction well defined, and it is
the banked `DenseWrapperFrontier.vartheta_lt_one` -- the second of the two facts
about `vartheta` the frozen derivation consumes (the first being
`half_le_vartheta`, used at `09:1361--1362`).

General in all five reals; nothing is evaluated. -/
theorem cleanCount_conclusions_are_monotone_in_e0 {q e0 e0' c KB l : ℝ}
    (hmono : e0 ≤ e0')
    (hfirst : q - e0 / (1 - vartheta) ≤ c)
    (hsecond : KB + l ≤ e0 / (1 - vartheta)) :
    q - e0' / (1 - vartheta) ≤ c ∧ KB + l ≤ e0' / (1 - vartheta) := by
  have hpos : (0 : ℝ) < 1 - vartheta := by
    have := vartheta_lt_one
    linarith
  have hdiv : e0 / (1 - vartheta) ≤ e0' / (1 - vartheta) := by
    gcongr
  exact ⟨by linarith, by linarith⟩

end Battery

/-! ## §6  WIRING (`cc-t8j` lane 3): banked endpoint theorems substituted at
binder-only consumer sites of this module

**What a "wiring" is here, and what it is not.**  Nothing below restates a
banked statement under a new name, and nothing below is a new mathematical
claim -- if a wiring's supplier were deleted, the wiring would not typecheck,
which is the operational test that it is a substitution and not a restatement.
Each wiring retires at least one binder of a consumer site by pinning a banked
owner that proves it.

**The blanket form of that sentence was FALSE and is withdrawn** (`cc-t8j` gate,
finding F-5, ruled CLEAR-with-itemization).  Through `r0` this preamble read
"Every declaration of this section has the SAME conclusion as a declaration this
module (or an upstream banked module) already carries, and STRICTLY FEWER
hypotheses".  That holds for **W-2** and **W-3**, whose conclusions are their
consumer sites' verbatim and whose binder lists are strictly shorter.  It does
**not** hold for **W-1**, on either half, and W-1's own docstring says so while
this preamble did not:

* its conclusion is *existentially strengthened* -- W-1 concludes
  `∃ E0, E0.card ≤ e0Max … ∧ ∀ i j, …`, while the consumer
  `twoCoordPair_projection_retains_y_sq` (`:935`) concludes only the body at a
  fixed `E0, i, j`;
* its hypotheses are *exchanged, not reduced* -- W-1 adds `hYc`, `hr0`, `hr1`,
  `hth`, `hS` in return for retiring `hcover`, `hi`, `hj` and the `E0` binder.

Both changes are deliberate and are exactly what `09:404--459` licenses, but they
are an exchange; the accurate general statement of this section is the one in the
paragraph above, and no stronger claim is made for W-1 anywhere below.

**Import direction, verified first-hand this tranche and printed, not asserted**
(IMPORT-DIRECTION RULE).  Both suppliers sit UPSTREAM of this module, so this
module is the importer at every pin below:

* `FrontierSumAssembly.lean:1 -> ClosureSelectSupply`;
  `ClosureSelectSupply.lean:1 -> FirstBobLightClosure`;
  `FirstBobLightClosure.lean:1 -> AliceOnlyHdensSupply`;
  `AliceOnlyHdensSupply.lean:1 -> FrontierProjectionSupply`;
  `FrontierProjectionSupply.lean:1 -> FrontierBundleConstruction`;
  `FrontierBundleConstruction.lean:1 -> SelectEmbedComposition`;
  `SelectEmbedComposition.lean:1 -> SelectDischarge`;
  `SelectDischarge.lean:1 -> FirstBobLightDichotomy`;
  `FirstBobLightDichotomy.lean:1 -> TranscriptLevelJoin`;
  `TranscriptLevelJoin.lean:1 -> TranscriptLevelSuccessors`;
  `TranscriptLevelSuccessors.lean:1 -> TranscriptLevelConstruction`;
  `TranscriptLevelConstruction.lean:1 -> WrapperDenseFrontierWiring`;
  `WrapperDenseFrontierWiring.lean:1 -> WrapperReferenceConstruction`;
  `WrapperReferenceConstruction.lean:1 -> WrapperLowRungAssembly`;
  `WrapperLowRungAssembly.lean:1 -> CertifiedLocalizedExtension`;
  `CertifiedLocalizedExtension.lean:1 -> TerminalFixedBinAssembly`;
  `TerminalFixedBinAssembly.lean:1 -> TerminalResidualComparison`;
  `TerminalResidualComparison.lean:1 -> TerminalCertificateInputs`;
  `TerminalCertificateInputs.lean:1 -> Stage3ProtocolRouting`;
  `Stage3ProtocolRouting.lean:1 -> TerminalStageThreeLift`;
  `TerminalStageThreeLift.lean:1 -> TerminalFixedBin`;
  `TerminalFixedBin.lean:1 -> TerminalTwoStream`;
  `TerminalTwoStream.lean:1 -> TerminalStateRealization`;
  `TerminalStateRealization.lean:1 -> TwoStreamState`;
  `TwoStreamState.lean:1 -> WrapperProjectionCovers`.  **W-1's supplier.**
* the same chain to `TranscriptLevelConstruction`, then
  `TranscriptLevelConstruction.lean:1 -> WrapperDenseFrontierWiring`;
  `WrapperDenseFrontierWiring.lean:2 -> FirstWrapperAssembly`;
  `FirstWrapperAssembly.lean:1 -> LargeCapacityBranch`;
  `LargeCapacityBranch.lean:1 -> SplitFirstBobInstance`;
  `SplitFirstBobInstance.lean:1 -> FirstBobFrontierInstance`;
  `FirstBobFrontierInstance.lean:1 -> FrontierIndexing`;
  `FrontierIndexing.lean:1 -> RoutingDynamics`;
  `RoutingDynamics.lean:1 -> RoutedCertificateSystem`;
  `RoutedCertificateSystem.lean:1 -> WrapperMassRedistribution`.
  **W-2's and W-3's supplier.**

**Sites SKIPPED this round, with the reason recorded rather than the site
silently omitted.**

* **`hcover` at the `09:1346--1365` clean-count endpoints**
  (`canonical_firstBob_light_of_reference_construction`,
  `canonical_frontierSum_against_the_light_bound`,
  `canonical_cleanCount_of_reference_construction`,
  `canonical_cleanCount_of_reference_construction_and_twoCopy`,
  `canonical_hfinal_of_reference_construction`).  The supplier
  `WrapperProjectionCovers.exists_initial_exceptional_set` is existential in
  `E_0`, while those five statements carry `E_0` in the CARRIER
  `StartedCoord E0` and in `R : StartedCoord E0 -> Finset X`.  Wiring them means
  moving thirty binders inside an `exists E_0`, which is a statement-shape change
  at five endpoints, not a substitution.  W-1 wires the site where `E_0` occurs
  only in hypotheses (`09:1329--1332`), which is the substitution the frozen text
  actually licenses; the five carrier-level sites are recorded OPEN.
* **`hLocEx` (`A:109--146`) at every site that carries it.**  Its owner is the
  cited expander family **EXPANDER-001**, which has no Lean declaration by
  design and must stay an explicit named hypothesis.  No supplier exists and
  none may be manufactured.
* **`halleged`, `hcost` (`09:1187--1193`, `09:1192--1193`).**  These are the
  *contradiction hypotheses* of the whole subsection: the alleged
  `(C+r-1)`-bit protocol, whose non-existence is the conclusion.  A supplier for
  them would be a proof that the object the argument refutes exists.  Not
  wireable, ever.
* **`hE1`, `hE2`, `htcert`, `hmem`, `hgate`, `hbase`, `hq`.**  Their defining
  displays (`06:239--243`, `02:815--819`, `09:105`, `06:927--934` /`09:304--307`)
  have banked owners whose homes -- `MechanicalCompilerResidue`,
  `ScheduleTemplateResidue`, `Section5Admissibility`,
  `FrontierScheduleReceipt` -- **import this module transitively or are
  incomparable to it**.  Pinning them here would be a downstream pin from
  upstream, which the IMPORT-DIRECTION RULE forbids; the `cc-t8h r7` gate already
  ruled that exact repair a REPAIR-STOP and the remedy is the downstream module
  `FrontierScheduleReceipt` (see L11 of the screen report below).  Recorded as an
  UNOWNED-INPUT skip, not as a gap in the mathematics.
* **`FrontierScheduleReceipt.finalBlock_receipt_fires_at_the_derived_point` at
  this module's `hfinal` disposition.**  Verified first-hand:
  `FrontierScheduleReceipt.lean:1` reads
  `import EthInapproximability.ParameterizedNP.FrontierSumAssembly`, so the
  named supplier is DOWNSTREAM of the named consumer and the pin is impossible in
  this direction.  **REPAIR-STOP, surfaced rather than worked around**: the
  remedy is a module downstream of both, never a rewrite of either, and never a
  free-binder substitute here.
* **`MassRedistributionCounting.wrapperTotalEarlyMass_engine` at
  `cleanCount_supplies_the_earlyMass_slot`.**  `MassRedistributionCounting` is
  **not** in this module's transitive import closure (checked first-hand), so
  that named engine cannot be pinned here.  W-2 wires the same frozen display
  `eq:wrapper-total-early-mass` through the owner that IS upstream,
  `WrapperMassRedistribution.wrapperTotalEarlyMass_frozen`; the
  `MassRedistributionCounting` restatement of the engine stays unwired from here.
* **`MassRedistributionTail`'s telescope entries and
  `TerminalFixedBinAssembly`'s A9-adjacent consumers.**  Not this lane's file
  (PARALLEL-LANE SURFACE RULE: a prove lane edits only its own obligation's
  file), and in the second case `TerminalFixedBinAssembly` is UPSTREAM of this
  module while `TerminalFixedBinProof` is INCOMPARABLE to it, so neither is
  reachable from these bytes in any case.

**Canonical inhabitation.**  This section declares no `structure`, `inductive`,
`abbrev`, `instance` or `def` -- only theorems about objects that already exist
-- so it opens NO new inhabitation obligation.  The module's inherited one stays
REGISTERED and DEFERRED under `FRONTIER-SUM-ASSEMBLY-001` for the reason the
header gives: the paper's own instance is a function of the alleged protocol of
`09:1187--1193`, which the argument refutes. -/

section CoverWiring

variable {q : ℕ} {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {X Z : Type*}

/-- **W-1.  `09:1331--1332`'s two-coordinate density with `hcover` RETIRED.**

*Consumer site.*  `twoCoordPair_projection_retains_y_sq` (`:935`) carries the
small-copy cover clause of `09:442--448` as the binder `hcover` and the two
avoidance facts `hi`, `hj` as binders over an assumed `E_0`.

*Supplier, by pin.*  `WrapperProjectionCovers.exists_initial_exceptional_set` --
the assembled deliverable of `sec:wrapper-projection-covers`, frozen
`09:404--459`, whose fourth conjunct is the `hcover` clause **at exactly this
shape** and whose cardinality clause is `09:452--453`'s "the construction
records an explicit deterministic upper bound `e_0 <= e_0^max`" at the
`eq:cover-bounds` value (`06:647--651`, reified as
`WrapperProjectionCovers.e0Max`).  That owner had **zero external consumers**
before this declaration; it is consumed here verbatim at its own interface and
is not restated.

*What is preserved and what is exchanged.*  The conclusion is **byte-identical**
to the consumer's, at the same `Sys`, `v`, `S`, `i`, `j`.  What enters in
exchange for `hcover` is `09:404`'s own hypothesis -- "For a retained outer
column set of density at least `theta`" -- as `hS`, plus the frozen
`rho_*`-legality binders `hr0`, `hr1` of `09:405--411`.  `E_0` is no longer
assumed: it is **produced**, together with its `09:452--453` bound.

**`rho_*` is NOT a free binder here, and that is deliberate.**  `09:407` DEFINES
`rho_* = max{rho_sing, 1 - eta_C}`, so a free `rstar` would be a source-defined
quantity entering as a binder.  The banked reification
`WrapperProjectionCovers.rhoStar` is pinned instead and its arguments are
evaluated down the frozen chain in dependency order: `n = |Y|` is `09:364`'s
one-coordinate outer column alphabet, here `Fintype.card Yc`; `tau_0` is
`09:376`'s `2 s x_T` through the banked `WrapperProjectionCovers.tauZero` at the
banked `DenseStageFourOpening.xTdepth` (`06:243`, `x_T = 2^{-b_T}`); and `eta_C`
is `eq:eta-choice`'s three-term minimum (`06:206--211`) through the banked
`ParameterSchedule.etaC`.  What remains free after that evaluation is exactly
four quantities, and each is free for a stated reason: `m_T` is `09:364--372`'s
readout `|Y_{T,p}| = m_T` of a template part this declaration does not build;
`delta_v(G)` is read off the guarded source, which `06:206--211` states as an
explicit binder rather than a formula; and `s` (`06:118`) and `b_T` (`06:241`)
are source-defined with banked owners whose homes -- `MechanicalCompilerResidue`,
`ScheduleTemplateResidue` -- import this module transitively, so they are
IMPORT-DIRECTION-FORCED binders of the standing disclosed class, discharged
downstream at `FrontierScheduleReceipt` and never pinned from upstream here.
`hr0` and `hr1` are then legality side conditions on the DEFINED value, not on a
substitute for it.

**`theta_cov` is a SEPARATE binder from the bracket parameter `theta` of
Sections 2--4, deliberately.**  `09:404`'s `theta` is the retained *outer column*
density; `def:bracket`'s `theta` is the bracket column parameter.  The frozen
text does not identify them at this site, so no identification is made here: two
independent binders is the weaker and honest reading, and conflating them would
be an over-strong hypothesis that typechecks perfectly.

*Why the trivial witness fails.*  The deliverable is existential, so this must be
answered.  `E_0 := Finset.univ` empties the universally quantified body (no `i`
is outside it) -- and it is barred by the cardinality clause exactly when
`e_0^max < q`, which is the schedule regime the construction runs in; Battery
W-B4 records that bar as a theorem rather than as a remark, and `E_0 := empty`
does **not** work, because then `hi`, `hj` are free and the density conclusion is
false at a genuinely poor pair (which is what `PoorProjection` says and what
`09:447--451`'s `E_0` exists to remove).  So neither degenerate choice is
available and the clause is load-bearing.

General in the routed system, the node, the retained column set, the cover index
`k`, the four residually free schedule readouts named above and the column
density; `rho_*`, `tau_0`, `x_T` and `eta_C` are evaluated through their banked
reifications rather than bound. -/
theorem twoCoordPair_projection_at_a_supplied_cover {Coord ι V : Type*}
    {P : Protocol X (Fin q → Yc) Z} {r A0 : ℕ}
    (Sys : RoutedSystem P Coord ι V r A0) (v : V) (S : Finset (Fin q → Yc))
    {k mT s bT : ℕ} {dv θcov : ℝ}
    (hYc : 0 < Fintype.card Yc) (hk : 2 ≤ k)
    (hr0 : 0 < rhoStar (Fintype.card Yc) mT (tauZero s (xTdepth bT))
      (ParameterSchedule.etaC s dv))
    (hr1 : rhoStar (Fintype.card Yc) mT (tauZero s (xTdepth bT))
      (ParameterSchedule.etaC s dv) < 1)
    (hth : 0 < θcov)
    (hS : θcov * (Fintype.card Yc : ℝ) ^ q ≤ (S.card : ℝ)) :
    ∃ E0 : Finset (Fin q),
      E0.card ≤ e0Max (coverExponent rhoSmall θcov)
          (coverExponent (rhoStar (Fintype.card Yc) mT (tauZero s (xTdepth bT))
            (ParameterSchedule.etaC s dv)) θcov)
          (coverExponent rhoPair θcov) k
        ∧ ∀ i j : Fin q, i ≠ j → i ∉ E0 → j ∉ E0 →
            ((3 : ℝ) / 5) ^ 2 * (Fintype.card Yc : ℝ) ^ (2 : ℕ)
              ≤ ((nodeProjection P S {i, j} (Sys.node v)).card : ℝ) := by
  obtain ⟨E, hcard, -, -, hsmall⟩ :=
    exists_initial_exceptional_set (Y := Yc) (q := q) (k := k) S hYc (by omega)
      hr0 hr1 hth hS
  exact ⟨E, hcard, fun i j hij hi hj =>
    twoCoordPair_projection_retains_y_sq Sys v S hsmall hk hij hi hj⟩

end CoverWiring

section EarlyMassWiring

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **W-2.  `eq:wrapper-total-early-mass` (`09:1526--1534`) with its `hKB` slot
RETIRED, on an arbitrary wrapper frontier.**

*Consumer site.*  `WrapperMassRedistribution.wrapperTotalEarlyMass_frozen`
carries `09:1529--1531`'s replacement of `K_B` by `e_0/(1-vartheta)` as the
binder `hKB : sum over B of kappa_v <= e_0/(1-vartheta)`, at a free node family
`B` and a free capacity family `kappa_v`.

*Supplier, by pin.*  This module's own `eq:wrapper-clean-count` output: the
second conjunct of `09:1352--1357`, dropped into the bare shape by
`cleanCount_supplies_the_earlyMass_slot` (`:2811`).  The node family and the
capacity family are no longer free -- they are `F.bobNodes` and `F.capacity`,
the frozen `09:1259` first-Bob column and `09:1255`'s `kappa_v = 2^{r-d_v}` --
and Battery W-B1 records that `K_B` is then literally
`DenseWrapperFrontier.WrapperFrontier.bobCapacity`, i.e. `09:1347--1348`'s own
`K_B`, so the instantiation is a pin and not a choice.

*What is preserved.*  The conclusion is the frozen display's second line
verbatim, at the frozen coefficient `earlyMassCoeff theta q s =
128 mu_P B_theta L_q s` (`09:1526--1529`), consumed from its banked owner and
re-rolled nowhere.

*The strictness binder is NOT decoration, and its pole is consumed by pin.*
`09:1526--1534` is a STRICT inequality, and at an empty first-Bob set both sides
are zero.  `WrapperMassRedistribution.totalEarlyMass_needs_a_first_bob_node` is
the banked pole for exactly that corner; it is cited here and **not**
re-authored, so `hne` is carried deliberately.

*Why the trivial witness fails.*  Not existential.  The conclusion is a strict
bound on a sum, and it is false at `F.bobNodes = empty` together with `e_0 = 0`
(both sides zero) -- which is precisely why `hne` is a binder.  Nor is it a
formal truth in the other direction: `hlt` is the per-node strict bound
`09:1519--1525` obtains from the contrapositive of `lem:early-protected-closure`,
and without it the sum bound fails at any node whose mass meets its threshold.

*`theta_E` is again a SEPARATE binder* from Sections 2--4's bracket `theta`, for
the reason W-1 gives: `B_theta = coverExponent rho_0 theta` reads the retained
outer column density, and the frozen text makes no identification at this site.

General in the frontier, the node carrier, the certificate assignment, the mass
family, the coefficient's schedule inputs and `e_0`; nothing is evaluated. -/
theorem earlyMass_at_the_supplied_cleanCount {r : ℕ} {V : Type*} [Fintype V]
    (F : WrapperFrontier r V) (cert : V → Option CertKind) (Pv : V → ℝ)
    {θE : ℝ} {s : ℕ} {e0 : ℝ}
    (hθE : 0 < θE) (hs : 1 ≤ s) (hne : F.bobNodes.Nonempty)
    (hlt : ∀ v ∈ F.bobNodes,
      Pv v < WrapperMassRedistribution.earlyMassCoeff θE q s
        * ((F.capacity v : ℕ) : ℝ))
    (hclean : F.bobCapacity + ((F.splitNodes cert).card : ℝ)
      ≤ e0 / (1 - vartheta)) :
    ∑ v ∈ F.bobNodes, Pv v
      < WrapperMassRedistribution.earlyMassCoeff θE q s * (e0 / (1 - vartheta)) := by
  refine WrapperMassRedistribution.wrapperTotalEarlyMass_frozen F.bobNodes Pv
    (fun v => ((F.capacity v : ℕ) : ℝ)) hθE hs hne hlt ?_
  have hKB := cleanCount_supplies_the_earlyMass_slot F cert hclean
  rwa [WrapperFrontier.bobCapacity] at hKB

/-- **W-3.  `eq:wrapper-total-early-mass` at the canonical routed system, with
`hlight`, `hfinal` AND `hKB` all retired.**

*Consumer site.*  W-2, whose remaining clean-count binder `hclean` is the
`eq:wrapper-clean-count` second conjunct at an arbitrary frontier.

*Supplier, by pin.*  `canonical_cleanCount_of_reference_construction_and_twoCopy`
(`:2089`) -- this module's `09:1352--1357` endpoint at the canonical system,
where `hlight` is already `canonical_firstBob_light_of_reference_construction`
and `hfinal` is already `canonical_hfinal_of_reference_construction`.  Its
statement is consumed **verbatim at its own interface**: the binder list below is
byte-identical to that declaration's, in the same order, with only the early-mass
inputs `Pv`, `theta_E`, `s`, `hne`, `hlt` appended.

*What this buys, stated exactly.*  `e_0` in the conclusion is `(E0.card : R)` --
`09:450`'s definition evaluated, never a parameter -- so the frozen display's
second line now reads at the construction's own exceptional count rather than at
a free real.  This is the FIRST link of the `09:1367--1781` block the header
census marks OPEN, wired to the assembly.  **It does not narrow that census**:
`eq:wrapper-u-dense` still needs `09:1535--1781`, and nothing here touches it.

*Why the trivial witness fails.*  Not existential; the poles are W-2's, inherited
unchanged, and the supplier's own (`DenseWrapperFrontier.cleanCount_needs_kraft`
for the first conjunct, `SplitFirstBobInstance.split_cleanCount_second_conjunct_is_live`
for the second).

*Hypothesis consistency.*  Nothing is conjoined that the frozen text states as
separate cases: `hlt` is quantified over the first-Bob column and the clean-count
supplier's `hfinal` over the final column, which are disjoint by
`DenseWrapperFrontier.WrapperFrontier.bobNodes_disjoint_finalNodes` -- the
`two_kappa_trap_at_the_final_nodes` separation, respected rather than collapsed.

*The added hypothesis `hne`, REGISTERED as an open non-vacuity residue.*  W-3
carries one binder its supplier
`canonical_cleanCount_of_reference_construction_and_twoCopy` does not:
`hne : (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes.Nonempty`.  It is
inherited from W-2, where it is the strictness pole of `09:1526--1534`, and it is
**not discharged at the canonical system by anything in this repository** --
grepped first-hand across `src/` at these bytes.  The earlier reading here, that
`09:1259`'s `kappa_v >= 2` "presupposes" inhabitation, is **withdrawn**: a
statement about every first-Bob node is vacuously true at an empty column and so
presupposes nothing, and the `cc-t8j` gate itemized that reasoning as a
non-derivation (finding F-10).  W-B5's receipt is at the **synthetic**
`DenseWrapperFrontier.wrapperFrontierProbe` and is explicitly NON-FIDELITY, so it
is evidence that the bundle is inhabited *somewhere*, never that it is inhabited
at `canonicalSystem`.  The residue is registered in the route obligation ledger
(`FRONTIER-SUM-ASSEMBLY-002`) and is **not** claimed discharged here; retiring it
instead would need the frozen construction to produce a first-Bob node at the
canonical system, which no banked module does.

What is checked and does hold is that `hne` conflicts with nothing:
`hlt` is quantified over the first-Bob column and the clean-count supplier's
`hfinal` over the final column, which are disjoint by
`DenseWrapperFrontier.WrapperFrontier.bobNodes_disjoint_finalNodes`, so the
final-node classification does not contradict inhabitation of the first-Bob one.

General in the same data as
`canonical_cleanCount_of_reference_construction_and_twoCopy`, plus the mass
family and the coefficient's schedule inputs. -/
theorem canonical_earlyMass_of_reference_construction {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ C - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [c])).cost)
    {Scol : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scol → (E0 ∩ K).Nonempty)
    (B : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → Finset X)
    (hB : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B v j).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblock : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B v j, plc v j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
    (Bfin : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Finset X)
    (hBfin : ∀ x, ((canonicalSystem hcomp hR).cert x).rows ≤ (Bfin x).card)
    (hblockFin : ∀ (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
      (x : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r),
      x.2.val = v.val → ∀ a ∈ Bfin x, plc v x.1 a ∈ rowsAt P (R x.1) v.val)
    (Pv : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    {θE : ℝ} {s : ℕ} (hθE : 0 < θE) (hs : 1 ≤ s)
    (hne : (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes.Nonempty)
    (hlt : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      Pv v < WrapperMassRedistribution.earlyMassCoeff θE q s
        * ((((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ))) :
    ∑ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes, Pv v
      < WrapperMassRedistribution.earlyMassCoeff θE q s
          * ((E0.card : ℝ) / (1 - vartheta)) := by
  refine earlyMass_at_the_supplied_cleanCount
    ((canonicalSystem hcomp hR).toWrapperFrontier) (canonicalFinalCert hcomp hR) Pv
    hθE hs hne hlt ?_
  exact (canonical_cleanCount_of_reference_construction_and_twoCopy Nmat Gmat ιR hsub
    halleged hcomp hR hq hmem hk hq4 hX hYc hθ0 hθ1 hC hgate hbase htcert hE1 hE2 hcost
    hLocEx hcover B hB plc hblock hplace Bfin hBfin hblockFin).2

end EarlyMassWiring

/-! ### §6a  Aux-lemma battery for the wiring

Four GENERAL checks.  **Canonical inhabitation comes first by rule, and there is
nothing new to inhabit**: §6 declares no type, so the module's inherited
obligation (REGISTERED and DEFERRED under `FRONTIER-SUM-ASSEMBLY-001`) is
unchanged and no probe below claims to discharge it.  W-2's strictness pole is
the banked `WrapperMassRedistribution.totalEarlyMass_needs_a_first_bob_node`,
consumed by citation and deliberately **not** re-authored here. -/

section WiringBattery

/-- **Battery W-B1 (the wired capacity family is a PIN, not a choice).**

`WrapperMassRedistribution.wrapperTotalEarlyMass_frozen` is general in the
capacity family `kappa_v`.  W-2 instantiates it at `F.capacity`, and this records
that the resulting sum is literally `09:1347--1348`'s `K_B`, the banked
`DenseWrapperFrontier.WrapperFrontier.bobCapacity` -- so the instantiation cannot
be a convenient choice of family, and a later tranche cannot substitute a
different one without the identity failing.

General in the frontier and its node carrier; nothing is evaluated. -/
theorem wiring_capacity_family_is_bobCapacity {r : ℕ} {V : Type*} [Fintype V]
    (F : WrapperFrontier r V) :
    ∑ v ∈ F.bobNodes, ((F.capacity v : ℕ) : ℝ) = F.bobCapacity := by
  rw [WrapperFrontier.bobCapacity]

/-- **Battery W-B2 (the wired early-mass bound weakens along `e_0 <= e_0^max`).**

`09:452--453` gives the construction an upper bound on `e_0` rather than its
exact value, so a consumer that knows only the bound must be able to weaken
W-2's conclusion to it.  This is that weakening, in the same direction as
`cleanCount_conclusions_are_monotone_in_e0` (`:2833`) and for the same reason:
`1 - vartheta > 0` is the banked `DenseWrapperFrontier.vartheta_lt_one`.

General in all four reals; nothing is evaluated. -/
theorem earlyMass_conclusion_is_monotone_in_e0 {cf e0 e0' T : ℝ}
    (hcf : 0 ≤ cf) (hmono : e0 ≤ e0')
    (h : T < cf * (e0 / (1 - vartheta))) :
    T < cf * (e0' / (1 - vartheta)) := by
  have hpos : (0 : ℝ) < 1 - vartheta := by
    have := vartheta_lt_one
    linarith
  have hdiv : e0 / (1 - vartheta) ≤ e0' / (1 - vartheta) := by
    gcongr
  nlinarith [h, hdiv, hcf]

/-- **Battery W-B3 (and along the coefficient).**

`earlyMassCoeff theta q s = 128 mu_P B_theta L_q s` (`09:1526--1529`) is
monotone in each of `B_theta`, `L_q` and `s`, so a consumer holding a coarser
coefficient inherits the bound.  Stated on the coefficient abstractly, because
the monotonicity is of the *conclusion shape*, not of the constant: it needs only
that the quantity being scaled is nonnegative, which `e_0 >= 0` and
`1 - vartheta > 0` supply.

General in all four reals; nothing is evaluated. -/
theorem earlyMass_conclusion_is_monotone_in_the_coefficient {cf cf' e0 T : ℝ}
    (hle : cf ≤ cf') (he0 : 0 ≤ e0)
    (h : T < cf * (e0 / (1 - vartheta))) :
    T < cf' * (e0 / (1 - vartheta)) := by
  have hpos : (0 : ℝ) < 1 - vartheta := by
    have := vartheta_lt_one
    linarith
  have hd : (0 : ℝ) ≤ e0 / (1 - vartheta) := div_nonneg he0 (le_of_lt hpos)
  nlinarith [h, hd, hle]

/-- **Battery W-B4 (W-1's cardinality clause bars the trivial cover).**

W-1 is existential in `E_0`, and the STATEMENT-POLES rule demands one line
showing the trivial witness fails.  `E_0 := Finset.univ` would empty W-1's
universally quantified body; this proves that `09:452--453`'s bound
`e_0 <= e_0^max` **excludes** that witness as soon as the schedule budget is
below the width, and moreover produces a coordinate outside `E_0`, which is what
W-1's body is quantified over.

The hypothesis `e_0^max < q` is not manufactured: it is the regime
`sec:wrapper-projection-covers` runs in, where `e_0 = O((s + t_ref) log(1/theta))`
(`09:454--456`) sits far below the outer width `q = 2^r`.  Stated as an explicit
binder rather than assumed, so the check is honest about what it needs.

General in `q`, the three cover exponents and the cover index; nothing is
evaluated. -/
theorem suppliedCover_is_not_everything {q Bref Bsing Bpair k : ℕ}
    {E0 : Finset (Fin q)}
    (hbudget : e0Max Bref Bsing Bpair k < q)
    (hcard : E0.card ≤ e0Max Bref Bsing Bpair k) :
    E0 ≠ (Finset.univ : Finset (Fin q)) ∧ ∃ i : Fin q, i ∉ E0 := by
  classical
  have hlt : E0.card < q := lt_of_le_of_lt hcard hbudget
  have hne : E0 ≠ (Finset.univ : Finset (Fin q)) := by
    intro hEq
    rw [hEq, Finset.card_univ, Fintype.card_fin] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hne, ?_⟩
  by_contra hall
  push_neg at hall
  exact hne (Finset.eq_univ_of_forall hall)

/-- **Battery W-B5 (HYPOTHESIS CONSISTENCY: W-2's bundle is jointly satisfiable,
and W-2 actually FIRES on it).**

The HYPOTHESIS-CONSISTENCY rule asks whether `False` follows from a new headline's
full bundle.  For W-2 the question has one real edge: `hne` demands a first-Bob
node while the clean-count supplier's `hfinal` runs over the final column, and
`two_kappa_trap_at_the_final_nodes` shows the two columns obey *opposite*
`vartheta kappa_v` inequalities.  If the frozen frame forced the first-Bob column
empty, W-2 would be vacuous with every gate green.

It does not, and this is the receipt: the **banked**
`DenseWrapperFrontier.wrapperFrontierProbe` has `bobNodes = {0}` with
`kappa_0 = 2` -- `09:1259`'s "every first-Bob node has `kappa_v >= 2`" met
strictly -- and the **banked** `DenseWrapperFrontier.wrapperCleanCount_legal_instance`
discharges `hclean` there at that probe's own `e_0 = 1`.  Both are consumed **by
pin**; neither is restated, and the probe frontier is not re-declared here.

**`theta_E` and `s` stay FREE**, so nothing about the schedule is chosen: the only
pinned numerals are the probe's own `q = 2^2 = 4` and `e_0 = 1`, read off the
banked instance rather than selected.  `P_v = 0` is the mass family the free
coefficient forces (a strict per-node bound against an unevaluated `cf` admits no
positive constant), so what this receipt establishes is exactly that the bundle
is inhabited and the conclusion is produced -- not that the mass side is
nondegenerate.  Stated plainly rather than overclaimed.

**This is a NON-FIDELITY probe** in the module's standing sense: the probe
frontier is not the paper's own routed instance, whose existence is what
`09:1187--1193` refutes, so it does **not** touch the inherited REGISTERED and
DEFERRED canonical-inhabitation obligation. -/
theorem earlyMass_wiring_fires_at_the_banked_probe {θE : ℝ} {s : ℕ}
    (hθE : 0 < θE) (hs : 1 ≤ s) :
    ∑ _v ∈ wrapperFrontierProbe.bobNodes, (0 : ℝ)
      < WrapperMassRedistribution.earlyMassCoeff θE 4 s * ((1 : ℝ) / (1 - vartheta)) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hclean⟩ := wrapperCleanCount_legal_instance
  refine earlyMass_at_the_supplied_cleanCount (q := 4) wrapperFrontierProbe probeCert
    (fun _ => (0 : ℝ)) hθE hs ?_ ?_ hclean
  · exact ⟨0, by decide⟩
  · intro v _
    have hcf : 0 < WrapperMassRedistribution.earlyMassCoeff θE 4 s :=
      WrapperMassRedistribution.earlyMassCoeff_pos hθE hs
    have hcap : (1 : ℝ) ≤ ((wrapperFrontierProbe.capacity v : ℕ) : ℝ) := by
      exact_mod_cast wrapperFrontierProbe.one_le_capacity v
    nlinarith

end WiringBattery

/-! ## LANE-1 SCREEN REPORT (`cc-t8i` bytes, `FrontierSumAssembly`)

**This block is the authoring lane's own contract-complete report**, required by the
SCREEN-GRANULARITY CONTRACT and prescribed at r0, r1 and r2.  At `r2` the lane shipped no
report at all and the tranche was ruled INCOMPLETE-BY-CONTRACT; at `r3` the report existed
and matched the gate's independent extraction occurrence for occurrence, but invented a
fourth numeral class for 39% of its rows and was ruled incomplete by contract again.  It
is written here, in-module, so it cannot go stale in `scratch/` or vanish between rounds.
The gate seat's independent tables are not treated as a substitute for it.

**That non-staleness sentence FAILED once, and the failure is recorded rather than
quietly repaired.**  `cc-t8j` lane 3 appended 8 declarations to this module and extended
none of L1--L6 to them, so at `r0` the report's 1:1-cover claim and this very sentence
were false about the module they describe — the `cc-t8j` gate ruled it
INCOMPLETE-BY-CONTRACT (finding F-9).  **L12 below is the repair**: it carries the
numeral screen, the binder-provenance table, the roster receipt, the dedup sweeps, the
shadow check and the atlas cross-check for those 8, and the L0 counts and the L3 header
are corrected in place to the post-delta figures.  L1--L6 above remain the `cc-t8i`
surface, unchanged; L12 is the `cc-t8j` surface; together they cover the module 1:1.

**Recomputation record, stated exactly** (the `r7` gate itemized the previous version of
this sentence as a record defect, because it said "recomputed on the `r4` bytes" over
rows that were in fact `r6` rows).  The tables were first computed on the `r4` bytes;
`r5` opened comment and citation rows only; `r6` added the five §4c declarations and
their rows; **`cc-t8i` deletes those five declarations and their rows, and moves no
statement or proof byte of any surviving declaration**.  What `cc-t8i` did move is
`D29`'s docstring, which lengthened by 22 lines, so every `D29` coordinate below was
shifted by exactly `+22` and then re-verified against the final bytes -- head `:2520`
-> `:2542`, span end `:2578` -> `:2600` -- rather than shifted on trust.  All other
coordinates are unchanged because every edit of this round lies at or below `D29`'s
docstring.

### L0.  Method, stated so the counts are reproducible

* **Statement span.**  For each declaration the span runs from its head line to the
  first `:=` at bracket depth zero.  Named-argument `:=` inside a term sits at positive
  depth and does not close the span; docstrings are excluded because the span starts at
  the head line.
* **Numeral occurrence.**  A maximal digit run whose neighbours are not identifier
  characters.  So `A0`, `E0`, `hE1`, `hq4` and `Yc` are NAMES and are not counted, while
  the `2` of `2 * xT`, the `1` of `C - 1` and the `.1` of `a.1` are counted -- the last
  as a structure projection index, classified CANONICAL-FORM rather than silently
  dropped.  **One artefact of that rule is reported rather than hidden:** the test only
  knows ASCII identifier characters, so the trailing digits of `hθ0` and `hθ1` -- whose
  preceding character is the non-ASCII `θ` -- ARE counted.  They are name digits, not
  quantities; every such row is classified CANONICAL-FORM under role `N29`, which says
  so, and there are 8 of them.
* **Classes.**  The taxonomy is CLOSED at three: EVALUATED = an evaluation of a frozen
  display through the definitional chain; CANONICAL-FORM = structural (positivity,
  arity, projection index, name digit) with no frozen value behind it; BEYOND-PAPER = a
  numeral the frozen source does not fix.  **Every occurrence receives one of those
  three.**  Provenance -- that an occurrence was also screened inside a banked block --
  is an annotation below the table, never a fourth class; the preceding round's
  `INHERITED` class is withdrawn and its 81 rows are classified individually.
* **Roster.**  The module holds **45** declarations (42 `theorem` + 3 `def`) on these
  bytes: **37** at the `cc-t8i` bytes this section's tables were computed on (34
  `theorem` + 3 `def`) -- of which 29 are that tranche's surface and 8 are
  byte-identical to the baseline `9c17653` and not gated -- plus the **8** `cc-t8j`
  lane-3 declarations appended at `:2847`ff., whose own tables are **L12**.  The `r7`
  gate's census correction is applied:
  `mem_certsAtNode` at `D13` carries `@[simp]` and is invisible to a `^theorem`-anchored
  sweep, so a bare head sweep under-reports by one.  (The `r7`-era figure of **42** was
  the count *before* this round deleted `D30`--`D34`; `42 - 5 = 37`.)

**Headline counts for the `cc-t8i` surface these tables cover: 29 gated declarations,
230 statement-position numeral occurrences, 0 BEYOND-PAPER, 0 unclassified, 0 outside
the three classes.**  The `cc-t8i` delta against the `r6` bytes is **-5 declarations**
(the §4c schedule batteries `D30`--`D34`, re-sited to `FrontierScheduleReceipt` -- see
§4c) and **-46 statement occurrences** (`276 - 46 = 230`), of which 18 were that
surface's entire BEYOND-PAPER population.  No statement byte of any surviving `cc-t8i`
declaration moved.

**Module-wide headline counts on these final bytes, `cc-t8i` surface plus `cc-t8j`
delta: 45 declarations, 345 statement-position numeral occurrences (`230 + 115`),
3 BEYOND-PAPER, 0 unclassified, 0 outside the three classes.**  The BEYOND-PAPER class
is **not** empty module-wide: W-B5's three synthetic-probe numerals repopulate it, and
the earlier "that class is now empty here" reading is **withdrawn** as a module-wide
claim and kept only as the statement about the `cc-t8i` surface that it accurately is.
The per-occurrence rows behind the `+115` are L12.1.

### L1.  STATEMENT-NUMERAL SCREEN -- ONE ROW PER OCCURRENCE

Columns: gated index | `file:line` | the numeral | class | what it evaluates.

Role legend (the fifth column of every row below):

  N01  `09:438`/`09:446` small-copy width `u_{2^l}`, base `2` and its `l = 1` member
  N02  `09:442` cover family lower index (`l` runs from `1`)
  N03  `09:442--445` the cover family needs its `l = 1` member, i.e. `2 <= k_ref`
  N04  `06:1110` `y = 3/5`
  N05  `06:1110` `y = 3/5`, denominator
  N06  `09:1332` `y^2`, the squared density the two-coordinate projection retains
  N07  `09:1331--1332` the two-coordinate column exponent
  N08  `09:436` `rho = 2 y^2`
  N09  arity of a frozen index type (`Fin 2` = `u_2` of `09:438`; `Fin 1` = the `l = 1`
       bracket)
  N10  `09:1340` two-copy row density `2 x_T`
  N11  depth floor `1 <= r` for the gate's `2^r`
  N12  `09:105` `q = 2^r` / the gate's `2^r`
  N13  `09:304--307` `eq:wrapper-low-simple-gate` `q x_T <= 4/25025` (also `06:927--934`)
  N14  `09:1340` legality ceiling `2 x_T <= 1`
  N15  carrier nonemptiness, no frozen value
  N16  `09:1302` `C >= 3`
  N17  positivity of a carrier cardinality / of `x_T`; a nonemptiness side condition, no frozen
       value
  N18  `09:1336` `H = C - 1`
  N19  `09:1336--1337` ladder copy index (`1` = `lem:wrapper-reference` base, `2` = the two-
       copy call)
  N20  `09:1192--1193` alleged cost `C + r - 1`
  N22  structure projection index (`.1`/`.2` field selector), not a quantity
  N23  `09:1317--1318` the conclusion `at most one reference certificate`
  N24  `09`'s `k_ref >= 4`
  N25  `09`'s gate `k_ref + 2 <= r`
  N27  `09:1353--1357` `eq:wrapper-clean-count`'s `e_0/(1 - vartheta)`
  N28  nondegeneracy floor `1 <= A_0` of Battery 11d; a nonvacuity side condition of
       the receipt, no frozen value
  N29  binder-NAME digit: the run belongs to the identifier `hθ0` / `hθ1`, whose
       non-ASCII prefix defeats L0's ASCII identifier test, so the extractor counts
       it.  It is a name, not a quantity (see L0's artefact note)
  N30  normalization of a free density parameter (`θ <= 1`, `x_T <= 1`); structural,
       no frozen value
  N31  `06:566--568` `t_ref = 2^{k_ref}` -- the selector-capacity base `2` of
       `09:1238`'s `2^k`; the search itself is `eq:tref-search` (`06:558--572`)
  N32  `09:1190`'s `p = 1` bracket family, its copy count
  N33  `A:130--136` (`eq:certified-E1` / `eq:certified-E2`): the dyadic factors
       `2^{-(H + log_2 q)}` and `2^{-(H + log_2 t)}` at `H = C-1`, `log_2 q = r`,
       `log_2 t = k_ref`; discharged in `06` by `eq:tref-search` (`06:574--578`)
  N34  `09:1255` `kappa_v = 2^{r-d_v}` and the capacity arithmetic `A:138--140`
       needs of it (`2^{(r-d_v)-k_ref} . 2^{k_ref} = 2^{r-d_v}`, `ceil(r' t x m)`)
  N35  structural side conditions of that capacity arithmetic: its positivity
       `0 < 2^{(r-d_v)-k_ref}`, and the vacuous placeholder `(0 : R) = 0` that
       `A:109--146` prints in antecedent position
  N36  `A:128--129`'s `a^sharp in {0,1}` fixed at `1`, with `A:140--141`'s
       column-density clause `h . 2^{-a^sharp}` (here `theta / 2^1`)
  N37  `vartheta = 9/16` (`09:1268`), in numerator/denominator form, and `A:120`'s
       `p_t = 9t/16` it is read from
  N38  `A:111--112`'s `H >= 2` at `H = C - 1`, i.e. `09:1302`'s `C >= 3` written in
       the printed antecedent's own form
  N39  `06:118` `eq:s-choice` `s = 2^{ceil(B_s u^2)}`: its base `2`, the exponent `2`
       of `u^2`, and the quarter divisor `4` of `06:239`'s `k_T = log_2(s/4)` -- the
       display written in the exponent form `06:122` ("Thus `s` is a public power of
       two") licenses.  Evaluated through the banked `ParameterSchedule.sScale`
  N40  `06:241` `b_T = 2^{j_49(k_T)}`: the base `2`, over the banked
       `ParameterSchedule.j49` (`06:77--78`).  Never a numeral for `b_T` itself
  N41  `06:263--267` `eq:hard-seed-width-gates` third row `log_2 s < b_T`, read
       through `sScale_eq_pow`'s `log_2 s = B_s u^2`; the `2` is `u^2`'s exponent
  (`N42` and `N43` were the roles of the deleted `D30`--`D34` rows and are retired
   with them; no row below carries either code, and **no BEYOND-PAPER occurrence
   survives anywhere in this module**.)

  -- D01  pair_card_eq_smallCopyWidth_two
  D01 :879   [2    ] EVALUATED      N01
  D01 :879   [1    ] EVALUATED      N01
  -- D02  twoCoordPair_projection_retains_y_sq
  D02 :939   [1    ] EVALUATED      N02
  D02 :940   [2    ] EVALUATED      N01
  D02 :941   [2    ] EVALUATED      N03
  D02 :942   [3    ] EVALUATED      N04
  D02 :942   [5    ] EVALUATED      N05
  D02 :942   [2    ] EVALUATED      N06
  D02 :942   [2    ] EVALUATED      N07
  -- D03  twoCoord_rho_exceeds_y_sq
  D03 :965   [3    ] EVALUATED      N04
  D03 :965   [5    ] EVALUATED      N05
  D03 :965   [2    ] EVALUATED      N06
  D03 :965   [2    ] EVALUATED      N08
  D03 :965   [3    ] EVALUATED      N04
  D03 :965   [5    ] EVALUATED      N05
  D03 :965   [2    ] EVALUATED      N06
  -- D04  twoCoordPair_supplies_the_bracket_column_clause
  D04 :990   [2    ] CANONICAL-FORM N09
  D04 :991   [1    ] EVALUATED      N02
  D04 :992   [2    ] EVALUATED      N01
  D04 :993   [2    ] EVALUATED      N03
  D04 :994   [3    ] EVALUATED      N04
  D04 :994   [5    ] EVALUATED      N05
  D04 :994   [2    ] EVALUATED      N06
  D04 :994   [2    ] EVALUATED      N07
  D04 :996   [2    ] CANONICAL-FORM N09
  -- D05  initialRefRows_is_the_twoCopy_block_floor
  D05 :1020  [2    ] EVALUATED      N10
  -- D07  twoCopy_row_legality_of_gate
  D07 :1052  [1    ] CANONICAL-FORM N11
  D07 :1053  [2    ] EVALUATED      N12
  D07 :1053  [4    ] EVALUATED      N13
  D07 :1053  [25025] EVALUATED      N13
  D07 :1054  [2    ] EVALUATED      N10
  D07 :1054  [1    ] EVALUATED      N14
  -- D08  finalPair_ladder_contradiction
  D08 :1081  [1    ] CANONICAL-FORM N15
  D08 :1081  [1    ] CANONICAL-FORM N15
  D08 :1082  [3    ] EVALUATED      N16
  D08 :1082  [0    ] CANONICAL-FORM N17
  D08 :1082  [2    ] EVALUATED      N10
  D08 :1082  [1    ] EVALUATED      N14
  D08 :1083  [1    ] EVALUATED      N18
  D08 :1083  [1    ] EVALUATED      N19
  D08 :1083  [3    ] EVALUATED      N04
  D08 :1083  [5    ] EVALUATED      N05
  D08 :1084  [2    ] EVALUATED      N19
  D08 :1084  [2    ] EVALUATED      N10
  D08 :1084  [3    ] EVALUATED      N04
  D08 :1084  [5    ] EVALUATED      N05
  D08 :1084  [2    ] EVALUATED      N06
  D08 :1085  [1    ] EVALUATED      N20
  -- D09  finalPair_margin_is_exactly_one_bit
  D09 :1108  [3    ] EVALUATED      N16
  D09 :1109  [1    ] EVALUATED      N18
  D09 :1109  [1    ] EVALUATED      N20
  D09 :1109  [1    ] EVALUATED      N20
  -- D10  finalNode_block_meets_twoCopy_floor
  D10 :1155  [2    ] EVALUATED      N10
  D10 :1158  [2    ] EVALUATED      N10
  -- D11  twoCopy_hgame_of_perCoordinate_placement
  D11 :1199  [1    ] CANONICAL-FORM N22
  D11 :1199  [2    ] CANONICAL-FORM N22
  -- D16  pair_premise_is_vacuous_at_a_thin_node
  D16 :1300  [1    ] EVALUATED      N23
  -- D17  certsAtNode_card_le_one_of_construction_supply
  D17 :1447  [0    ] CANONICAL-FORM N17
  D17 :1447  [0    ] CANONICAL-FORM N17
  D17 :1448  [3    ] EVALUATED      N16
  D17 :1448  [1    ] EVALUATED      N20
  D17 :1449  [0    ] CANONICAL-FORM N17
  D17 :1449  [2    ] EVALUATED      N10
  D17 :1449  [1    ] EVALUATED      N14
  D17 :1450  [1    ] EVALUATED      N18
  D17 :1450  [1    ] EVALUATED      N19
  D17 :1450  [3    ] EVALUATED      N04
  D17 :1450  [5    ] EVALUATED      N05
  D17 :1451  [2    ] EVALUATED      N10
  D17 :1452  [2    ] EVALUATED      N03
  D17 :1453  [1    ] EVALUATED      N02
  D17 :1454  [2    ] EVALUATED      N01
  D17 :1461  [1    ] EVALUATED      N23
  -- D20  mem_certsAtNode_canonical
  D20 :1636  [2    ] CANONICAL-FORM N22
  -- D21  frontierWeight_eq_sum_certsAtNode
  D21 :1650  [1    ] CANONICAL-FORM N22
  D21 :1650  [2    ] CANONICAL-FORM N22
  -- D23  canonical_frontierWeight_le_finalWeight_of_card_le_one
  D23 :1708  [1    ] EVALUATED      N23
  -- D24  canonical_hfinal_of_reference_construction
  D24 :1833  [4    ] EVALUATED      N24
  D24 :1833  [2    ] EVALUATED      N25
  D24 :1834  [0    ] CANONICAL-FORM N17
  D24 :1834  [0    ] CANONICAL-FORM N17
  D24 :1834  [3    ] EVALUATED      N16
  D24 :1835  [2    ] EVALUATED      N12
  D24 :1835  [4    ] EVALUATED      N13
  D24 :1835  [25025] EVALUATED      N13
  D24 :1836  [1    ] EVALUATED      N18
  D24 :1836  [1    ] EVALUATED      N19
  D24 :1836  [3    ] EVALUATED      N04
  D24 :1836  [5    ] EVALUATED      N05
  D24 :1837  [1    ] EVALUATED      N20
  D24 :1839  [1    ] EVALUATED      N02
  D24 :1840  [2    ] EVALUATED      N01
  D24 :1847  [2    ] CANONICAL-FORM N22
  D24 :1847  [1    ] CANONICAL-FORM N22
  D24 :1847  [1    ] CANONICAL-FORM N22
  -- D25  canonical_cleanCount_of_reference_construction_and_twoCopy
  D25 :2097  [2    ] EVALUATED      N12
  D25 :2098  [1    ] CANONICAL-FORM N09
  D25 :2098  [1    ] CANONICAL-FORM N09
  D25 :2099  [1    ] EVALUATED      N32
  D25 :2100  [4    ] EVALUATED      N24
  D25 :2100  [2    ] EVALUATED      N25
  D25 :2101  [0    ] CANONICAL-FORM N17
  D25 :2101  [0    ] CANONICAL-FORM N17
  D25 :2102  [0    ] CANONICAL-FORM N29
  D25 :2102  [0    ] CANONICAL-FORM N17
  D25 :2102  [1    ] CANONICAL-FORM N29
  D25 :2102  [1    ] CANONICAL-FORM N30
  D25 :2102  [3    ] EVALUATED      N16
  D25 :2103  [2    ] EVALUATED      N12
  D25 :2103  [4    ] EVALUATED      N13
  D25 :2103  [25025] EVALUATED      N13
  D25 :2104  [1    ] EVALUATED      N18
  D25 :2104  [1    ] EVALUATED      N19
  D25 :2104  [3    ] EVALUATED      N04
  D25 :2104  [5    ] EVALUATED      N05
  D25 :2105  [2    ] EVALUATED      N31
  D25 :2106  [3    ] EVALUATED      N04
  D25 :2106  [5    ] EVALUATED      N05
  D25 :2106  [2    ] EVALUATED      N31
  D25 :2106  [2    ] EVALUATED      N33
  D25 :2106  [1    ] EVALUATED      N18
  D25 :2108  [2    ] EVALUATED      N33
  D25 :2108  [1    ] EVALUATED      N18
  D25 :2109  [1    ] EVALUATED      N20
  D25 :2114  [1    ] EVALUATED      N36
  D25 :2115  [2    ] CANONICAL-FORM N22
  D25 :2116  [1    ] CANONICAL-FORM N17
  D25 :2117  [2    ] EVALUATED      N38
  D25 :2117  [1    ] EVALUATED      N18
  D25 :2118  [0    ] CANONICAL-FORM N17
  D25 :2118  [1    ] CANONICAL-FORM N30
  D25 :2119  [1    ] EVALUATED      N18
  D25 :2119  [1    ] EVALUATED      N19
  D25 :2119  [3    ] EVALUATED      N04
  D25 :2119  [5    ] EVALUATED      N05
  D25 :2120  [2    ] EVALUATED      N31
  D25 :2121  [4    ] EVALUATED      N24
  D25 :2122  [2    ] EVALUATED      N31
  D25 :2122  [1    ] EVALUATED      N14
  D25 :2123  [0    ] CANONICAL-FORM N35
  D25 :2123  [2    ] EVALUATED      N34
  D25 :2124  [2    ] EVALUATED      N34
  D25 :2124  [2    ] EVALUATED      N34
  D25 :2125  [2    ] EVALUATED      N34
  D25 :2125  [2    ] EVALUATED      N34
  D25 :2125  [2    ] EVALUATED      N34
  D25 :2126  [0    ] CANONICAL-FORM N35
  D25 :2126  [0    ] CANONICAL-FORM N35
  D25 :2127  [0    ] CANONICAL-FORM N17
  D25 :2127  [1    ] CANONICAL-FORM N30
  D25 :2128  [2    ] EVALUATED      N36
  D25 :2128  [1    ] EVALUATED      N36
  D25 :2128  [0    ] CANONICAL-FORM N29
  D25 :2128  [1    ] CANONICAL-FORM N29
  D25 :2129  [3    ] EVALUATED      N04
  D25 :2129  [5    ] EVALUATED      N05
  D25 :2129  [2    ] EVALUATED      N31
  D25 :2129  [2    ] EVALUATED      N33
  D25 :2129  [1    ] EVALUATED      N18
  D25 :2131  [2    ] EVALUATED      N33
  D25 :2131  [1    ] EVALUATED      N18
  D25 :2132  [2    ] EVALUATED      N34
  D25 :2132  [9    ] EVALUATED      N37
  D25 :2132  [2    ] EVALUATED      N31
  D25 :2132  [16   ] EVALUATED      N37
  D25 :2133  [9    ] EVALUATED      N37
  D25 :2133  [2    ] EVALUATED      N34
  D25 :2133  [16   ] EVALUATED      N37
  D25 :2134  [9    ] EVALUATED      N37
  D25 :2134  [2    ] EVALUATED      N34
  D25 :2134  [16   ] EVALUATED      N37
  D25 :2135  [0    ] CANONICAL-FORM N29
  D25 :2135  [1    ] CANONICAL-FORM N29
  D25 :2136  [2    ] EVALUATED      N34
  D25 :2137  [0    ] CANONICAL-FORM N29
  D25 :2137  [1    ] CANONICAL-FORM N29
  D25 :2138  [1    ] EVALUATED      N18
  D25 :2140  [1    ] EVALUATED      N02
  D25 :2141  [2    ] EVALUATED      N01
  D25 :2162  [2    ] CANONICAL-FORM N22
  D25 :2162  [1    ] CANONICAL-FORM N22
  D25 :2162  [1    ] CANONICAL-FORM N22
  D25 :2163  [1    ] EVALUATED      N27
  D25 :2169  [1    ] EVALUATED      N27
  -- D27  finalBlock_bundle_inputs_are_legal
  D27 :2311  [1    ] CANONICAL-FORM N22
  -- D28  finalBlock_bundle_joint_inhabitant
  D28 :2385  [1    ] CANONICAL-FORM N22
  D28 :2393  [2    ] CANONICAL-FORM N22
  D28 :2394  [1    ] CANONICAL-FORM N22
  D28 :2394  [1    ] CANONICAL-FORM N22
  D28 :2397  [1    ] CANONICAL-FORM N22
  D28 :2397  [2    ] CANONICAL-FORM N22
  D28 :2399  [2    ] CANONICAL-FORM N22
  -- D29  finalBlock_bundle_joint_inhabitant_at_the_construction_point
  D29 :2545  [2 c24 ] EVALUATED      N12
  D29 :2546  [2 c40 ] EVALUATED      N12
  D29 :2547  [1 c11 ] CANONICAL-FORM N11
  D29 :2547  [0 c25 ] CANONICAL-FORM N17
  D29 :2549  [4 c44 ] EVALUATED      N39
  D29 :2549  [2 c48 ] EVALUATED      N39
  D29 :2550  [2 c17 ] EVALUATED      N40
  D29 :2551  [2 c23 ] EVALUATED      N41
  D29 :2554  [2 c26 ] EVALUATED      N12
  D29 :2555  [2 c43 ] EVALUATED      N12
  D29 :2558  [1 c7  ] CANONICAL-FORM N28
  D29 :2561  [2 c49 ] EVALUATED      N12
  D29 :2562  [2 c25 ] EVALUATED      N12
  D29 :2562  [2 c62 ] EVALUATED      N12
  D29 :2563  [2 c22 ] EVALUATED      N12
  D29 :2563  [2 c42 ] EVALUATED      N12
  D29 :2565  [2 c39 ] EVALUATED      N12
  D29 :2567  [2 c37 ] EVALUATED      N12
  D29 :2567  [2 c57 ] EVALUATED      N12
  D29 :2569  [2 c39 ] EVALUATED      N12
  D29 :2571  [2 c26 ] EVALUATED      N12
  D29 :2575  [2 c30 ] EVALUATED      N12
  D29 :2578  [2 c41 ] EVALUATED      N12
  D29 :2581  [2 c41 ] EVALUATED      N12
  D29 :2583  [2 c17 ] CANONICAL-FORM N22
  D29 :2584  [1 c25 ] CANONICAL-FORM N22
  D29 :2585  [2 c43 ] EVALUATED      N12
  D29 :2585  [1 c69 ] CANONICAL-FORM N22
  D29 :2587  [2 c41 ] EVALUATED      N12
  D29 :2589  [2 c47 ] EVALUATED      N12
  D29 :2590  [2 c52 ] EVALUATED      N12
  D29 :2592  [2 c41 ] EVALUATED      N12
  D29 :2595  [2 c41 ] EVALUATED      N12
  D29 :2595  [1 c67 ] CANONICAL-FORM N22
  D29 :2595  [2 c72 ] CANONICAL-FORM N22
  D29 :2597  [2 c41 ] EVALUATED      N12
  D29 :2599  [2 c47 ] EVALUATED      N12
  D29 :2600  [2 c44 ] CANONICAL-FORM N22

Class totals: CANONICAL-FORM 62, EVALUATED 168, BEYOND-PAPER 0; TOTAL 230.
(`r6` bytes: 63 / 195 / 18 = 276.  The `cc-t8i` deletion of `D30`--`D34` removed
1 CANONICAL-FORM, 27 EVALUATED and all 18 BEYOND-PAPER rows = 46.)
**Unclassified: 0.  Rows outside the three prescribed classes: 0.**

**The taxonomy is CLOSED at three classes, and the previous round's fourth class is
withdrawn.**  The preceding round classified the 81 occurrences of D25's guard
telescope and `hLocEx` slot (`:2098--:2138` on these bytes) as `INHERITED`, which is
not one of the three standing classes.  Every one of those 81 rows above now carries
EVALUATED or CANONICAL-FORM on its own merits, against the frozen display named in its
role code (`N29`--`N38` were added for exactly this block), and inherited provenance is
recorded here as an annotation rather than as a class:

* **provenance, annotation only.**  The block is the guard telescope of the banked
  `ClosureSelectSupply.closure_and_projected_density_of_reference_construction`.
  `FrontierSumAssembly.lean:2098--2109` against `ClosureSelectSupply.lean:307--318`,
  and `FrontierSumAssembly.lean:2116--2138` against `ClosureSelectSupply.lean:323--345`,
  are identical modulo leading indentation (SHA-256 of the de-indented text,
  `822333cec485e99d8216330b643ec53e96db7c6189f06e17658e5003936957d1` and
  `9ab33969e3cb8d63250f950c9d808bbce0e608397b17d58653ca421a669692e8`), so those
  numerals were also screened where they were banked.
* **the previous round's byte-identity claim was too wide, and is corrected here.**
  The guard-plus-`hLocEx` block is **not** byte-identical to
  `ClosureSelectSupply.lean:307--345` taken whole: D25 adds a node quantifier and a
  `firstBob` guard, at `:2110--2111` on these bytes
  (`(hLocEx : ∀ v : FrontierNode ...` and `(canonicalSystem hcomp hR).firstBob v = true →`),
  which **strengthens** the hypothesis relative to the banked shape.  Those two added
  lines contain **no digit run at all**, so no row of the table above lands on either
  of them and the numeral screen is unaffected; the two numeral-bearing subblocks
  named in the previous bullet really are identical.

### L2.  BINDER-PROVENANCE TABLE (source-DEFINED quantities, one row per declaration)

The question this table answers is the DEFINED-vs-FREE rule's: does any quantity the
frozen source **defines** enter a statement as a free binder?  Columns: gated index |
quantity with its anchor | how it enters.

How-it-enters legend (the third column of every row below):

  B01  EVALUATED via `smallCopyWidth (2 ^ l)`
  B02  FREE width `{q : ℕ}`; `09:105` enters only where a consumer demands it
  B03  carrier `E0 : Finset (Fin q)`, free; `e_0` itself never a binder
  B04  EVALUATED, the defined `rhoSmall`
  B05  FREE at the GENERIC layer (`{A0 : ℕ}` of `RoutedSystem`/`CertIndex`); floored by `hA0`
       where used
  B06  EVALUATED, written `3 / 5` / `((3 : ℝ) / 5)`; never a binder
  B07  FREE `{k : ℕ}`, CONSTRAINED by `hk : 2 ≤ k`
  B08  EVALUATED as `initialRefRows (xTdepth bT) (Fintype.card X)` -- at D29, at
       the reference matrix's own row carrier, `initialRefRows (xTdepth bT) (Fintype.card W)`
  B09  FREE at the GENERIC layer (`{xT : ℝ}`), guarded by `hxT0`/`hlegal`
  B10  FREE `(mG : ℕ)` at this generality
  B11  EVALUATED as `xTdepth bT`
  B12  FREE `{C : ℕ}`, CONSTRAINED not assigned (`hC : 3 ≤ C` = 09:1302)
  B14  EVALUATED as `Fintype.card X`
  B15  FREE `{kref : ℕ}`, CONSTRAINED by `hk`
  B16  EVALUATED as `(E0.card : ℝ)`
  B17  EVALUATED, the defined constant `DenseWrapperFrontier.vartheta`
  B18  EVALUATED, carried by `hq : (q : ℝ) = (2 : ℝ) ^ r`
  B19  EVALUATED via `kappaAt`
  B20  EVALUATED as `Fintype.card W`, the reference matrix `Nmat : W -> Yc -> Bool`'s
       own row carrier
  B21  SUBSTITUTED: `09:105`'s width is written into the types -- the `{q : ℕ}` binder
       is gone and the outer coordinate type is literally `Fin (2 ^ r)`
  B22  PINNED to `06:116--117` (`u = clog_2(clog_2(A_pre + 16))`) by the `hu` hypothesis,
       over the banked `ParameterSchedule.uAux` and `.Apre`.  NOT a free binder
  B23  PINNED to `06:239` (`k_T = log_2(s/4)`) by the `hkT` hypothesis in the exponent
       form `06:122` licenses, over the banked `ParameterSchedule.sScale`.  NOT free:
       the pin forces `k_T = B_s u^2 - 2` because `m |-> 2^m` is injective, and
       `FrontierScheduleReceipt.derivedKT_eq` proves that downstream
  B24  PINNED to `06:241` (`b_T = 2^{j_49(k_T)}`) by the `hbT` hypothesis, over the
       banked `ParameterSchedule.j49`.  NOT a free binder, and never a numeral
  B25  SOURCE-DEFINED@`02:815--819` (`B_s = T^2`, least `T` with `T >= 64` and
       `9T^2 - 2 >= m_HS`), carried as a binder here ONLY because its banked owner
       `MechanicalCompilerResidue.bsSched` is downstream of this module.  The
       earlier GENUINELY-FREE@`06:263` reading is **WITHDRAWN**: `06:263` is a USE
       site.  Discharged externally at `FrontierScheduleReceipt`
  B26  GENUINELY-FREE public-record size of the input instance -- `b_out`, `B_pub`,
       `z_R`, `clE = clog_2(|E|+2)`, the four inputs `06:111--115` feeds into `A_pre`.
       The frozen text prints no numeral for any of them.  (`B_pub` and `z_R` are
       themselves DEFINED at `06:49--54` off the public record; at this generality no
       record is in scope, and the external instantiation supplies them as the
       downstream accessors at a UNIVERSALLY QUANTIFIED record rather than as
       numerals -- no closed public input is formed, `05:13--14` exhibiting none)
  (`B27` was the role of the deleted `D30`--`D34` rows and is retired with them.)

  -- D01  pair_card_eq_smallCopyWidth_two
  D01 u_2 = 2 (09:438)                 B01
  D01 q = 2^r (09:105)                 B02
  -- D02  twoCoordPair_projection_retains_y_sq
  D02 e_0  = |E_0| (09:450)            B03
  D02 u_2 = 2 (09:438)                 B01
  D02 rho = 2y^2 (09:436)              B04
  D02 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  D02 y = 3/5 (06:1110)                B06
  D02 q = 2^r (09:105)                 B02
  D02 k_ref (09:442--445)              B07
  -- D03  twoCoord_rho_exceeds_y_sq
  D03 rho = 2y^2 (09:436)              B04
  D03 y = 3/5 (06:1110)                B06
  -- D04  twoCoordPair_supplies_the_bracket_column_clause
  D04 e_0  = |E_0| (09:450)            B03
  D04 u_2 = 2 (09:438)                 B01
  D04 rho = 2y^2 (09:436)              B04
  D04 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  D04 y = 3/5 (06:1110)                B06
  D04 q = 2^r (09:105)                 B02
  D04 k_ref (09:442--445)              B07
  -- D05  initialRefRows_is_the_twoCopy_block_floor
  D05 A_0 = ceil(2 x_T m_G) (09:1219)  B08
  D05 x_T = 2^{-b_T} (06:243)         B09
  D05 m_G = |Rows(G)| (09:113--116)    B10
  -- D06  finalNode_cert_rows_ge_initialRefRows
  D06 A_0 = ceil(2 x_T m_G) (09:1219)  B08
  -- D07  twoCopy_row_legality_of_gate
  D07 x_T = 2^{-b_T} (06:243)         B11
  -- D08  finalPair_ladder_contradiction
  D08 x_T = 2^{-b_T} (06:243)         B09
  D08 y = 3/5 (06:1110)                B06
  D08 C  (target cost, 09:1192)        B12
  -- D09  finalPair_margin_is_exactly_one_bit
  D09 C  (target cost, 09:1192)        B12
  -- D10  finalNode_block_meets_twoCopy_floor
  D10 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  D10 x_T = 2^{-b_T} (06:243)         B09
  D10 m_G = |Rows(G)| (09:113--116)    B14
  -- D11  twoCopy_hgame_of_perCoordinate_placement
  D11 q = 2^r (09:105)                 B02
  -- D12  certsAtNode
  D12 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D13  mem_certsAtNode
  D13 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D14  sum_card_certsAtNode
  D14 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D15  certsAtNode_coord_ne
  D15 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D16  pair_premise_is_vacuous_at_a_thin_node
  D16 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D17  certsAtNode_card_le_one_of_construction_supply
  D17 e_0  = |E_0| (09:450)            B03
  D17 u_2 = 2 (09:438)                 B01
  D17 rho = 2y^2 (09:436)              B04
  D17 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  D17 x_T = 2^{-b_T} (06:243)         B09
  D17 y = 3/5 (06:1110)                B06
  D17 q = 2^r (09:105)                 B02
  D17 m_G = |Rows(G)| (09:113--116)    B14
  D17 C  (target cost, 09:1192)        B12
  D17 k_ref (09:442--445)              B15
  -- D18  canonicalKindsAt
  D18 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D19  canonicalFinalCert
  D19 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D20  mem_certsAtNode_canonical
  D20 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D21  frontierWeight_eq_sum_certsAtNode
  D21 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D22  canonicalFinalCert_eq_none_iff
  D22 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D23  canonical_frontierWeight_le_finalWeight_of_card_le_one
  D23 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D24  canonical_hfinal_of_reference_construction
  D24 e_0  = |E_0| (09:450)            B03
  D24 u_2 = 2 (09:438)                 B01
  D24 rho = 2y^2 (09:436)              B04
  D24 A_0 = ceil(2 x_T m_G) (09:1219)  B08
  D24 x_T = 2^{-b_T} (06:243)         B11
  D24 y = 3/5 (06:1110)                B06
  D24 q = 2^r (09:105)                 B02
  D24 m_G = |Rows(G)| (09:113--116)    B14
  D24 C  (target cost, 09:1192)        B12
  D24 k_ref (09:442--445)              B15
  -- D25  canonical_cleanCount_of_reference_construction_and_twoCopy
  D25 e_0  = |E_0| (09:450)            B16
  D25 vartheta = 9/16 (09:1268)        B17
  D25 u_2 = 2 (09:438)                 B01
  D25 rho = 2y^2 (09:436)              B04
  D25 A_0 = ceil(2 x_T m_G) (09:1219)  B08
  D25 x_T = 2^{-b_T} (06:243)         B11
  D25 y = 3/5 (06:1110)                B06
  D25 q = 2^r (09:105)                 B18
  D25 m_G = |Rows(G)| (09:113--116)    B14
  D25 kappa_v = 2^{r-d_v} (09:1255)    B19
  D25 C  (target cost, 09:1192)        B12
  D25 k_ref (09:442--445)              B15
  -- D26  finalBlock_supply_is_inhabited
  D26 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  -- D27  finalBlock_bundle_inputs_are_legal
  D27 e_0  = |E_0| (09:450)            B03
  D27 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  D27 q = 2^r (09:105)                 B02
  -- D28  finalBlock_bundle_joint_inhabitant
  D28 e_0  = |E_0| (09:450)            B03
  D28 A_0 = ceil(2 x_T m_G) (09:1219)  B05
  D28 q = 2^r (09:105)                 B02
  -- D29  finalBlock_bundle_joint_inhabitant_at_the_construction_point
  D29 e_0  = |E_0| (09:450)            B03
  D29 A_0 = ceil(2 x_T m_G) (09:1219)  B08
  D29 x_T = 2^{-b_T} (06:243)         B11
  D29 m_G = |Rows(G)| (09:113--116)    B20
  D29 q = 2^r (09:105)                 B21

**The `r6` delta, at the contract's granularity: ONE ROW PER FREE BINDER, with the
exact `file:line` of the binder.**  All lines are in this file.  The module declares no
`structure`, so there is no field row to write; every row below is a `theorem` binder.

  decl  binder  line   source status
  ----  ------  -----  -------------------------------------------------------------
  D29   W       :2543  GENUINELY-FREE carrier (09:113--116 fixes no cardinality)
  D29   Yc      :2543  GENUINELY-FREE carrier (09:105--116 fixes no alphabet)
  D29   r       :2543  GENUINELY-FREE, CONSTRAINED by `hr : 1 <= r`; 09:105 ties
                       `q = 2^r` to it and the frozen text constrains, never assigns
  D29   bT      :2543  SOURCE-DEFINED@06:241 -- PINNED by `hbT`            B24
  D29   kT      :2543  SOURCE-DEFINED@06:239 -- PINNED by `hkT`            B23
  D29   Bs      :2543  SOURCE-DEFINED@02:815--819 -- binder here ONLY because its
                       banked owner is downstream; discharged externally      B25
  D29   u       :2543  SOURCE-DEFINED@06:116--117 -- PINNED by `hu`        B22
  D29   bout    :2544  GENUINELY-FREE@06:111--115                          B26
  D29   Bpub    :2544  GENUINELY-FREE@06:111--115                          B26
  D29   zR      :2544  GENUINELY-FREE@06:111--115                          B26
  D29   clE     :2544  GENUINELY-FREE@06:111--115                          B26
  D29   E0      :2545  GENUINELY-FREE carrier (09:447--451 fixes no cover set)
  D29   Nmat    :2546  GENUINELY-FREE reference matrix (09:113--116)
  D29   aq      :2546  GENUINELY-FREE ladder Alice predicate (09:1203--1207)
  D29   z       :2546  GENUINELY-FREE@09:1204 -- the RETAINED output label; the
                       frozen sentence retains it and declines to fix it, which is
                       exactly why pinning it to `false` was the r5 REVISE
  D29   Scol    :2554  GENUINELY-FREE retained column set (09:1275)

**Source-DEFINED quantities entering as FREE binders in statement position: ONE, and
it is the one the IMPORT-DIRECTION RULE forces.**  This replaces the `r6` report's
claim of zero, which the `cc-t8h` `r7` gate ruled **FALSE** and which is withdrawn
here rather than softened.

* `B_s` at `D29 :2543` is **SOURCE-DEFINED@02:815--819** (`B_s = T^2` for the least
  `T` with `T >= 64`, `9T^2 - 2 >= m_HS`), not GENUINELY-FREE@`06:263`.  `06:263`
  is a USE site referring back to that display -- the USE-AS-DEFINITION class.  Its
  banked owner `MechanicalCompilerResidue.bsSched` is **downstream** of this module
  (import chain printed in §4c), so it cannot be pinned here; it therefore remains
  an explicit binder of D29, and the instantiation at the paper's own value happens
  in `FrontierScheduleReceipt` (`paperSchedulePins_hold_at_the_derived_point`).
  **Disclosed, not claimed away**: a downstream consumer discharges it, and no
  declaration of this module asserts anything about `B_s`'s value.
* `u`, `k_T`, `b_T` are source-defined and are **PINNED** by `hu`, `hkT`, `hbT`,
  never free.  `r5`'s bytes had `b_T` free and no `u` or `k_T` at all, which is what
  let the withdrawn audit point assign `b_T = 3`.
* The five `r6` declarations whose free `u` and `b_T` the `r7` gate also flagged
  (`D30`--`D34`) are **deleted from this module** (§4c); their re-sited successors
  pin both through the defining chain.

**Reading of the table.**  `x_T`, `A_0`, `m_G` and the interlace width are free binders
at the GENERIC layer only -- the layer at which a statement is about an arbitrary
`RoutedSystem`, where the frozen construction has not yet been named.  At the three
construction-specific endpoints D24, D25 and D29 every one of them is the evaluated form
(`initialRefRows (xTdepth bT) (Fintype.card X)` resp. `... (Fintype.card W)`,
`xTdepth bT`, `Fintype.card X` resp. `Fintype.card W`), D29 additionally SUBSTITUTES
`q = 2^r` into the types so that `09:105`'s width is not a binder there at all, and
D24's proof discharges the generic `hA0` slot by
`le_of_eq (initialRefRows_is_the_twoCopy_block_floor ...)` and its `hk` slot by `omega`
from `4 ≤ kref`, rather than carrying them.  `e_0`, `vartheta`, `rho`, `u_2`, `y` and
`kappa_v` are **never** binders anywhere in the module: each is written as its defined
term.  `C` and `k_ref` are free but CONSTRAINED (`3 ≤ C` at `09:1302`, `4 ≤ k_ref`), which
is what the frozen text does with them -- it constrains them, it does not assign them.

**Source-DEFINED quantities entering as free binders in statement position at a
construction-specific endpoint: 0.**

### L3.  ROSTER RECEIPT (29 rows, `file:line`) -- the `cc-t8i` surface only

The 8 `cc-t8j` lane-3 declarations appended at `:2847`ff. are **not** in this roster;
their roster receipt is **L12.3**.  The two rosters plus the 8 non-gated baseline rows
named at the foot of this section partition the module's 45 declarations.

Columns: gated index | kind | name | head line | last line of the statement | numerals.
All lines are in `src/EthInapproximability/ParameterizedNP/FrontierSumAssembly.lean`.

  D01 theorem pair_card_eq_smallCopyWidth_two                          :878   -> :879   num 2
  D02 theorem twoCoordPair_projection_retains_y_sq                     :935   -> :943   num 7
  D03 theorem twoCoord_rho_exceeds_y_sq                                :964   -> :965   num 7
  D04 theorem twoCoordPair_supplies_the_bracket_column_clause          :985   -> :996   num 9
  D05 theorem initialRefRows_is_the_twoCopy_block_floor                :1019  -> :1020  num 1
  D06 theorem finalNode_cert_rows_ge_initialRefRows                    :1032  -> :1036  num 0
  D07 theorem twoCopy_row_legality_of_gate                             :1052  -> :1054  num 6
  D08 theorem finalPair_ladder_contradiction                           :1079  -> :1085  num 16
  D09 theorem finalPair_margin_is_exactly_one_bit                      :1108  -> :1109  num 4
  D10 theorem finalNode_block_meets_twoCopy_floor                      :1152  -> :1158  num 2
  D11 theorem twoCopy_hgame_of_perCoordinate_placement                 :1190  -> :1199  num 2
  D12 def     certsAtNode                                              :1220  -> :1221  num 0
  D13 theorem mem_certsAtNode                                          :1226  -> :1228  num 0
  D14 theorem sum_card_certsAtNode                                     :1237  -> :1239  num 0
  D15 theorem certsAtNode_coord_ne                                     :1256  -> :1259  num 0
  D16 theorem pair_premise_is_vacuous_at_a_thin_node                   :1298  -> :1302  num 1
  D17 theorem certsAtNode_card_le_one_of_construction_supply           :1435  -> :1461  num 16
  D18 def     canonicalKindsAt                                         :1605  -> :1607  num 0
  D19 def     canonicalFinalCert                                       :1623  -> :1625  num 0
  D20 theorem mem_certsAtNode_canonical                                :1633  -> :1636  num 1
  D21 theorem frontierWeight_eq_sum_certsAtNode                        :1645  -> :1650  num 2
  D22 theorem canonicalFinalCert_eq_none_iff                           :1666  -> :1670  num 0
  D23 theorem canonical_frontierWeight_le_finalWeight_of_card_le_one   :1705  -> :1709  num 1
  D24 theorem canonical_hfinal_of_reference_construction               :1825  -> :1853  num 18
  D25 theorem canonical_cleanCount_of_reference_construction_and_twoCopy :2089  -> :2169  num 89
  D26 theorem finalBlock_supply_is_inhabited                           :2251  -> :2255  num 0
  D27 theorem finalBlock_bundle_inputs_are_legal                       :2300  -> :2311  num 1
  D28 theorem finalBlock_bundle_joint_inhabitant                       :2379  -> :2399  num 7
  D29 theorem finalBlock_bundle_joint_inhabitant_at_the_construction_point :2542  -> :2600  num 38

The five `r6` rows `D30`--`D34` are **deleted from this roster and from every table
above**, and their content is re-sited to `FrontierScheduleReceipt` (§4c).  Residue
check run in BOTH polarities on these bytes: none of the five short names heads a
declaration anywhere in `src/` or `vendor/`, and every surviving textual occurrence of
any of them is prose in §4c or in this report -- the record of the deletion, never a
re-mint.

The 8 non-gated declarations, byte-identical to `9c17653` and therefore outside this
tranche's surface: `startedCoord_census_evaluates_e_zero`,
`canonical_firstBob_light_of_reference_construction`,
`canonical_frontierSum_against_the_light_bound`,
`canonical_cleanCount_of_reference_construction`, `two_kappa_trap_at_the_final_nodes`,
`vartheta_twins_agree`, `cleanCount_supplies_the_earlyMass_slot`,
`cleanCount_conclusions_are_monotone_in_e0`.

### L4.  DEDUP SWEEPS, RE-RUN ON THESE BYTES

**Corpus.**  All 237 `.lean` files under `src/` and `vendor/` -- a strict superset of this
module's transitive closure and of its `open` list -- comment-stripped with line structure
preserved (nesting-aware, so doc comments, module comments and nested block comments are
all removed), parsed for
`theorem`/`def`/`lemma`/`abbrev`/`instance`/`structure`/`inductive` heads including
`noncomputable`, `private`, `protected`, `nonrec` and `@[...]` attribute prefixes.
**8698 declarations parsed, 8398 distinct short names.**  (The r3 report's 8704/8525 came
from a parse that also swept docstring lines beginning with `instance`/`def` into the head
set; the stricter comment strip removes them.  The delta is parser hygiene, not a change
in the tree.)

**(a) Whole-statement sweep.**  Statement spans normalized (comments stripped, whitespace
collapsed, namespace prefixes dropped) and scored against every corpus declaration outside
the gated set by token-set Jaccard, reporting at `>= 0.82`.  **5 pairs cleared the
threshold, every one of them a D25 shared-telescope artefact, and no other gated
declaration appears at any threshold:**

  0.890  D25  vs  `FrontierSumAssembly.canonical_frontierSum_against_the_light_bound` (:647)
  0.887  D25  vs  `FrontierSumAssembly.canonical_cleanCount_of_reference_construction` (:1925)
  0.884  D25  vs  `FrontierSumAssembly.canonical_firstBob_light_of_reference_construction` (:520)
  0.868  D25  vs  `ClosureSelectSupply`
         `.closure_and_projected_density_of_reference_construction` (:295)
  0.868  D25  vs  `ProtectedEarlyClosure.canonical_bobCapacity_le_earlyMassSlot` (:553)

All five are the same phenomenon and it is adjudicated, not waved through.  D25 carries
the reference-construction guard telescope, and so does every declaration that consumes or
supplies that construction; the tokens therefore agree while the **conclusions** share
nothing.  The first three are this module's own **baseline** declarations, byte-identical
to `9c17653` and outside the gated set -- D25 is the `hfinal`-discharged sibling of the
second and is *proved by calling it*, which is consumption, not republication.  The fourth
is the banked supply whose guard block D25 carries (L1's provenance annotation); its
conclusion is the per-node closure/density statement, D25's is `eq:wrapper-clean-count`'s
two-sided count.  The fifth sits **downstream** (`ProtectedEarlyClosure` imports this
module) and carries the telescope in order to consume it; its conclusion is the single
`bobCapacity` bound, i.e. the Battery-4 drop of D25's *second* conjunct.

**(b) Intra-module sweep** (gated against gated).  **1 pair at `>= 0.82`:**

  0.914  `canonicalKindsAt`  vs  `canonicalFinalCert`

Both are `def`s reading the `09:1346--1347` trichotomy off the same routing at the same
node, so their binder lists coincide; their bodies and return types differ
(`Finset`-valued kinds against `Option CertKind`).  This is the pair the gate seat has
adjudicated as a shared-telescope artefact in each preceding round.

**(c) UP-TO-SPECIALIZATION sweep -- the one that decides this round.**  For every
top-level conjunct of every gated conclusion, a head-symbol skeleton is computed:
**explicit named arguments `(X := ...)` are deleted first** -- they are presentation, and
leaving them in is exactly what lets a republished owner look fresh -- then the
declaration's own binder names and every locally quantified name are removed, and only
identifiers of length `>= 3` that are declared names of the corpus are retained, so
instantiating a type, a `Fin q`, or a literal cannot defeat the match.  Skeletons are then
looked up in the table of all banked conclusions' skeletons.  A one-symbol skeleton is
shared *vocabulary*, not a shared statement shape, and is reported as noise rather than as
a hit: **18 one-symbol coincidences** (`rowsAt`, `startedIdx`, `refRowFloor`, `CertKind`,
and the like).  **3 matches at skeleton length `>= 2`:**

  D04  `('nodeProjection', 'symm')`
       vs `SelectDischarge.nodeProjection_transport_density` (:674)
  D15  `('coord', 'coord')`  vs `RoutingDynamics.twinSystem_live_pair` (:1462)
  D16  `('coord', 'coord')`  vs `RoutingDynamics.twinSystem_live_pair` (:1462)

**The test.**  A conjunct is a PROHIBITED specialization-level duplicate when the banked
owner, at that specialization, proves it **with no further hypothesis** -- the gated
declaration then adds nothing and merely republishes the owner under a new name.  It is
LEGITIMATE CONSUMPTION when the gated declaration **discharges** at least one of the
owner's own premises, *and that discharge itself contributes fresh construction
mathematics*; a banked lemma applied to another banked lemma with nothing gated in between
is NOT legitimate.  That sharpening is the r3 gate's, adopted verbatim.

* **D04 is legitimate.**  It discharges the owner's `hdens` slot: the projection density
  is not assumed but derived from `09:442--445`'s cover family **through the gated D02**,
  and `pc := 2`, `J := {i,j}`, `y := (3/5)^2` are the frozen `09:1330--1332` instance.
* **D15 and D16 are not duplicates, and the hit is an artefact of the two-symbol
  threshold**: both symbols of `('coord','coord')` are the same field projection.  The
  banked `twinSystem_live_pair` is an **existential non-vacuity probe at one fixed twin
  system** (`exists i in cleanFinal, exists j in cleanFinal, i != j and owner i = owner j
  and coord i != coord j`).  D15 is a **universal** uniqueness fact of an *arbitrary*
  routed system (distinct certificates at one node carry distinct coordinates), and D16 is
  Battery 10's vacuity implication.  The quantifier direction is opposite and the banked
  owner proves neither, so nothing is republished.  Reported rather than suppressed
  because the threshold produced it.
* **The r3 REVISE is gone from this list.**  `finalPair_lambdaGE_le_suffix_cost` -- the
  banked-to-banked wrapper whose conclusion was
  `LambdaGE Gmat 2 (2 * xT) (((3 : R) / 5) ^ 2) <= (descend P p).cost`, matching
  `SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member` (:506) -- **is deleted**,
  and its two banked applications now sit directly in D17's proof with no declaration of
  this module between them.
* **The new D29 produces no match at any length `>= 2`**, and in particular no conjunct of
  it has the `CompletedNoBob` skeleton.

**Screen-power test (a null result from a screen that never fires is worthless).**  The
conjunct the r3 round deleted was re-fed to the same sweep on these bytes:

  probe    `CompletedNoBob (aliceLadder (X := Fin q x W) (Y := Fin q -> Yc) aq false r) r`
  skeleton `('CompletedNoBob', 'aliceLadder')`
  MATCHES  `FrontierIndexing.canonicalSystem_legal_instance` (:1159),
           `RoutingDynamics.completedNoBob_aliceLadder` (:1181)

So the sweep still fires on the exact defect that parked `r2`, and it fires on it
**because the named arguments are stripped first** -- with them left in, the same probe
returns NONE.  On these bytes no gated conjunct produces that skeleton.  Independently:
`CompletedNoBob` occurs in statement position in this module exactly 13 times (`:526`,
`:653`, `:1606`, `:1624`, `:1634`, `:1646`, `:1667`, `:1706`, `:1831`, `:1931`, `:2095`,
`:2253`, `:2382`), and **every one is an `hcomp : CompletedNoBob P r` binder taken from
the caller** -- none is a conclusion or a conjunct of one, and **D29 adds none**: it names
the owner as the lower-case term `completedNoBob_aliceLadder`, applied.  `aliceLadder`
occurs in statement position only inside
D29, and only as the **protocol index of a type** (`FrontierNode (aliceLadder ...) R A_0 r`,
`CertIndex (aliceLadder ...) ...`, `rowsAt (aliceLadder ...) ...`) and as the argument of
`canonicalSystem` in the `hBfin` conjunct -- never as the subject of a `CompletedNoBob`
claim.  That is exactly the shape the r3 verdict's prescription 2 requires: the owner is
*applied*, not restated.

### L5.  CROSS-MODULE SHADOW CHECK

The 29 gated short names intersected against the distinct short names of the corpus of
all `.lean` files under `src/` and `vendor/` (covering `def`/`abbrev`/`instance`/
`structure` as well as theorems):

  SHADOW INTERSECTION: {}      total collisions: 0

**The five `r6` §4c names are BARRED from `cc-t8i` on.**  `sScale_quarter_eq_two_pow`,
`kT_pin_determines_kT`, `xTdepth_le_quarter_of_gate`,
`paperSchedulePins_are_jointly_satisfiable` and
`finalBlock_receipt_fires_at_the_pinned_schedule_point` head **no** declaration anywhere
in `src/` or `vendor/`, and occur in no statement, proof or tactic.  Their surviving
textual occurrences are prose -- §4c's re-site record, this section, and the L3 note --
which is the record of the deletion, not a re-mint; that is stated rather than letting an
`rg` hit look like a survival.  Their re-sited successors carry **different names** in a
different module (`FrontierScheduleReceipt.derivedKT_eq`, `.derivedXT_le_quarter`,
`.paperSchedulePins_hold_at_the_derived_point`,
`.finalBlock_receipt_fires_at_the_derived_point`), so no homonym is minted on either
side, and `sScale_quarter_eq_two_pow` has no successor at all -- the banked
`ScheduleTemplateResidue.kT_at_pow_two` is that arithmetic and is consumed by pin.

The empty intersection is the positive token that the check ran.  D29's name
`finalBlock_bundle_joint_inhabitant_at_the_construction_point` is fresh in the corpus,
and `finalPair_lambdaGE_le_suffix_cost` remains a barred name on the same footing.

### L6.  ATLAS CROSS-CHECK ("Do not re-author" rows, read at these bytes)

* `docs/atlas/RoutingDynamics.md:80` lists `completedNoBob_aliceLadder` /
  `aliceLadder_stopAt_final` among that module's **non-vacuity probes**.  A non-vacuity
  probe is owned where it is banked; no declaration here republishes it, and D29 -- the
  only declaration that needs the frame -- invokes the owner **by pin**, as a term, and
  concludes only the fresh bundle.  **This is the row the r4 repair complies with.**
* `docs/BANKED_SURFACE_INDEX.md:3521` registers the anchor span **`09:1195--1213`** for
  `RoutingDynamics.completedNoBob_aliceLadder` (with `RoutedCertificateSystem.aliceLadder`
  at `:1119`).  Every citation of it in this module reads `09:1195--1213`, with the ladder
  construction at `09:1203--1207`.
* `docs/atlas/SelectDischarge.md`: the certified row ladder "is consumed only through the
  banked `TerminalTwoStream.certifiedRowLadder_of_base`".  The ladder enters D17 only
  through `DenseWrapperFrontier.finalNode_twoCopy_bound`.  **The r4 delta touches that
  card's other owners directly**: `lambdaGE_le_cost_descend_of_bracket_member` and
  `bracketMember_of_blocks_and_columns` are now applied inside D17's proof rather than
  through a module-local wrapper, which is consumption by pin and is what the card asks
  for.
* `docs/atlas/SelectEmbedComposition.md`: "`interlaceFun_reference_copy` owns the
  reference-copy identity -- do not re-assume `hgame`."  D11 **consumes** that owner by pin
  and composes it with the construction's single-coordinate `hplace`; its conclusion's
  right-hand side is `g (plc (own a.1) a.2) y`, not `interlaceFun Nmat ...`.
* `docs/atlas/FrontierSumAssembly.md`.  Its **mechanical** header is at the banked state
  and describes 8 declarations, not 37; that block is regenerated by the card generator at
  bank and is untouched here.  Its **curated** block, however, asserted two things that are
  false of these bytes -- that the `hfinal` arc is unwired, and that full-bundle
  satisfiability is unclaimed.  At `r4` this lane read that as accurate-until-bank and left
  it; `r5` corrects it under an explicit round instruction, labelling both corrections
  **in-flight and unbanked** rather than as banked fact.  See L9(4).
  **No card row assigns an owner to** the joint final-node bundle at the construction
  point, which is what D29 exhibits; the empty relevant-owner result is the positive token
  that the check ran.


### L7.  THE r4 REPAIR DELTA, PRESCRIPTION BY PRESCRIPTION

The r3 verdict listed six prescriptions.  All six are applied on these bytes; nothing else
was touched.

1. **The banked-to-banked wrapper is DELETED.**  `finalPair_lambdaGE_le_suffix_cost` -- an
   entire proof of the form `bankedOwner (bankedLemma hB hC) ...` with no gated content in
   between -- is gone, together with its docstring.  Its **single** Lean consumer was
   inside D17's proof, and the two banked applications now sit there directly:
   `SelectDischarge.lambdaGE_le_cost_descend_of_bracket_member` applied to
   `SelectDischarge.bracketMember_of_blocks_and_columns (fun m => Bfin (pick m)) _ hAfloor
   hCd`, both by pin.  **D17's statement does not change**; only its proof does, and it
   still typechecks against the same conclusion.  The four prose mentions of the deleted
   name were rewritten to name the two banked owners instead, and the name occurs nowhere
   in `src/` or `vendor/` any more (L5).
2. **The LANE-GATE 3 composition is WRITTEN DOWN**, as the new D29
   `finalBlock_bundle_joint_inhabitant_at_the_construction_point` (Battery 11d).  It
   applies `RoutingDynamics.completedNoBob_aliceLadder` **by pin**, applies D27's slab
   result **by pin**, feeds both to D28, and concludes **only** the fresh joint bundle --
   `CompletedNoBob` is not a conjunct of it (L4(c)).  The construction-specific
   instantiations are performed rather than left free: `q = 2^r` is substituted into the
   types (the width binder is gone) and `A_0` is written as the evaluated
   `initialRefRows (xTdepth bT) (Fintype.card W)`.  Four nondegeneracy conjuncts are proved
   alongside the bundle -- `1 <= A_0`, `StartedCoord E_0` inhabited, every slab nonempty,
   every slab a **proper** subset of `Fin (2^r) x W` -- so the receipt is not a statement
   about an empty or degenerate hypothesis set.  It is labelled **NON-FIDELITY** in its own
   docstring and in the section header: it shows joint satisfiability at a legal schedule
   point, never that the bundle holds of the frozen object.
3. **The fourth numeral class is WITHDRAWN.**  All 81 rows the r3 report classified
   `INHERITED` now carry EVALUATED or CANONICAL-FORM against a named frozen display; the
   role legend gained `N28`--`N38` for exactly that block, and provenance survives as an
   annotation under the table, never as a class.  The r3 role text `N26` claimed the whole
   guard-plus-`hLocEx` block was byte-identical to `ClosureSelectSupply.lean:307--345`;
   **that claim was false and is corrected** in the annotation: D25 adds a node quantifier
   and a `firstBob` guard at `:2110--2111`, which strengthens the hypothesis, and those two
   lines carry **no digit run at all**, so the numeral screen is unaffected.  Class totals
   on these bytes: CANONICAL-FORM 62, EVALUATED 164, BEYOND-PAPER 0, TOTAL 226.
4. **D27's nonemptiness prose is corrected.**  The claim that the slab "is not empty and
   not all of `Fin q x W`" is withdrawn: the sole hypothesis `hW : refRowFloor A_0 r <=
   |W|` is vacuous at `A_0 = 0`, so D27 establishes the **cardinality** and nothing more.
   The docstring now says so, names the three guards that would be needed (`0 < |W|`, an
   inhabitant of `StartedCoord E_0`, `2 <= q`), and points at D29, which supplies them.
5. At `r4` `docs/atlas/FrontierSumAssembly.md` and `docs/ARCS_TO_DONE.md` were left
   **untouched**, on the reading that the record-only boundary opens on an all-CLEAR
   round.  **`r5` changes that for the atlas card only**, under an explicit round
   instruction; see L9(4).  `docs/ARCS_TO_DONE.md` is still untouched by this lane.
6. The whole surface is re-presented for gating: **29 gated declarations** (28 carried,
   1 deleted, 1 new), 37 in the module, 8 baseline.  Every carried statement is
   byte-identical to the bytes ruled on at r3 -- only D17's *proof* changed -- which the
   L1 table's positional match against the r3 table confirms occurrence by occurrence.

**Carried forward from the r3 repair, unchanged and re-verified here.**  D27 states only
its three fresh conjuncts; this report exists in-module at contract granularity; D17's
docstring attributes "distinct initial outer coordinates" to `09:1322--1323`;
`09:1207--1212` reads `09:1195--1213` everywhere with the ladder construction at
`09:1203--1207`; and the `plc` "not the identity" claim stays withdrawn.  The reader pin
was **rebuilt** at `r5` rather than carried; see L9(2).


### L8.  WHAT THIS REPORT DOES NOT CLAIM

It certifies the provenance and the reproducibility of the screens, and nothing else.  It
does not claim `eq:wrapper-u-dense`: the header census stands, `09:1700--1781` is OPEN,
and no declaration above implies the endpoint.  It does not claim canonical inhabitation:
the paper's own instance of every statement here is a function of the alleged protocol of
`09:1187--1193`, whose non-existence is the conclusion of the argument, so that obligation
stays REGISTERED and DEFERRED and Batteries 11b/11c/11d remain NON-FIDELITY probes -- 11d
in particular exhibits the bundle over the **completed Alice ladder**, a legal frame that
is not the alleged protocol, and says so.  It does
not bank anything: the ledger row, the crosswalk, the atlas cards and
`docs/BANKED_SURFACE_INDEX.md` are the verify seat's bank-time duties, and the tranche
verdict is the gate's to give.
### L9.  THE r5 MECHANICAL PRE-GATE DELTA

`r5` is the gate round on the `r4` bytes.  The lane's licence was **comment, citation and
audit-row lines only**, and that is measured rather than asserted: stripping every comment
and doc-comment from this module leaves **982 non-comment lines**, and those 982 lines are
**byte-identical** to the `r4` park's (joint SHA-256 `882e5070...`), so no statement byte
and no proof byte of any of the 37 declarations moved.  The L1/L3 tables below re-confirm
it positionally -- every carried row keeps its numeral multiset and its class.  Five items.

1. **The durable auditor now covers this surface one-to-one.**  Through `r4`,
   `tools/AxiomAudit.lean` carried `#print axioms` rows for the **8 baseline** declarations
   only, and the `r2` gate had to obtain its 48-line audit from a throwaway probe file,
   which certifies nothing durable.  `r5` adds **29 rows** for exactly the gated roster
   below -- 26 `theorem`s and the 3 `def`s `certsAtNode`, `canonicalKindsAt`,
   `canonicalFinalCert` -- so this module's block was a 1:1 cover of all 37 declarations
   **as of `r5`**.  **That sentence is superseded and must not be read in the present
   tense**: `cc-t8j` lane 3 appended 8 declarations, so a 1:1 cover of the module now
   needs 8 further `#print axioms` rows.  Adding them is the verify seat's action on a
   shared surface, and this lane does not edit `tools/AxiomAudit.lean`; L12.3 lists
   exactly which 8 rows are owed.
   (Lane 2's 19 rows were added to the same file in the same pass, giving 48 = the whole
   tranche surface.)  The `def`s are rowed deliberately: a `def` can still reach
   `Classical.choice` through its decidability instances, so leaving them unrowed left a
   real hole in the audit rather than a stylistic one.
2. **The reader pin is rebuilt, and it was WRONG, not merely unpinned.**  The finding
   prescribed at `r0`, `r1` and `r2` was that the reader citation named the **live**
   `routes/parameterized-np/reader-facing/` tree, which a concurrent session is editing.
   Re-citing it against a pinned release exposed a second, worse defect that four rounds
   had not seen: the header cited **three** spans under **one** release's hash, and the
   spans live in **two different releases**.  `A-stage4-details.tex:370--399` and `:394`
   resolve in the route's `CURRENT_VERSION` release
   (`versions/2026-08-02-iteration-cexc-repair`, SHA-256 `5b6e9ba0...19c6`) and do **not**
   resolve in `versions/2026-08-22-reader-minimal-v3` at all -- the minimal reader cut that
   passage, and contains no occurrence of "ultra-explicit companion".  `:828--835` resolves
   in the minimal release (SHA-256 `77bb9f84...937c`) and not in the `CURRENT_VERSION` one,
   which contains no occurrence of "unsplit pair at".  Both hashes were recomputed
   first-hand at these bytes and both spans were re-read where they are cited.  The live
   worktree copy happens to agree with the minimal release today, which is precisely what
   concealed the defect.  **Still no reader counterpart is claimed for any declaration.**
3. **Every in-module coordinate in this report is re-anchored and re-verified, not
   shifted on trust.**  Item 2 lengthened the header, so all report coordinates moved.  The
   L1 rows, the L3 roster, the `CompletedNoBob` statement-position list, the D25 telescope
   spans and the barred-name occurrence list were all re-anchored and then **checked
   against these bytes**: L1 **226 rows checked, 226 agree, 0 mismatches** (each row's digit
   run `tok` must occur on the line the row names); L3 **29 rows checked, 29 agree** (each
   row's head line must begin that declaration); the 13 `CompletedNoBob` lines each contain
   `CompletedNoBob`; and the two de-indented telescope segments reproduce the *unchanged*
   SHA-256 values `822333ce...57d1` (`:2098--2109`) and `9ab33969...92e8` (`:2116--2138`)
   under the report's own normalization -- which is a stronger receipt than the shift, since
   an off-by-one would break the hash.  This is the check `r0` skipped, and it is the same
   class of defect that finding `S-6` still has open in `docs/ARCS_TO_DONE.md`.
4. **The atlas card is repaired** (`docs/atlas/FrontierSumAssembly.md`, FINDING 7, held by
   the `r2` gate for the next licensed round).  Its curated block claimed the `hfinal` arc
   was unwired and that full-bundle satisfiability was unclaimed; both are false of these
   bytes.  The repair states each correction **as in-flight and unbanked**, per the
   "forecasts are not premises" rule, and leaves the mechanical header (SHA, size, roster)
   alone because the generator rebuilds it at bank.  It also carries item 2's two-release
   correction into the card's own reader sentence.
5. **Two anchor defects the gate found while running item 3, repaired in place, both
   comment-only and both line-count neutral so no coordinate moved again.**
   (a) *The legality gate was anchored to the wrong passage, in three places.*  D07
   `twoCopy_row_legality_of_gate` consumes `q x_T <= 4/25025`; its docstring, the guard
   census at §4a-1, and role code `N13` all attributed that display to `09:1187--1193`,
   which is the **alleged-protocol** passage and contains no such display.  Re-read
   first-hand in the frozen release: the display is `eq:wrapper-low-simple-gate` at
   `09:304--307` (display `09:305`, label `09:306`), and it is also the last clause of
   `eq:wrapper-low-rung-gates` at `06:927--934` (the clause on `06:932`).  All three
   citations now read that.  The Lean is unaffected -- `hgate` already carried the
   display in `09:105`'s `q = 2^r` form -- so this is a record repair, not a
   mathematics change, and it is the USE-AS-DEFINITION class: a gate cited where it is
   *used* rather than where it is *displayed*.
   (b) *The alleged protocol was cited under two different spans in one module*:
   `09:1187--1193` at five sites (including the header cross-anchor census and the
   `FRONTIER-SUM-ASSEMBLY-001` ledger row) and `09:1188--1193` at seven.  Both cover the
   passage; the split is the defect.  Normalized to `09:1187--1193`, the sentence-head
   span, which is also the ledger's, so module and ledger now agree.  `N20` keeps the
   tighter `09:1192--1193` for the alleged **cost**, which is where that numeral is.

**The joint-inhabitant pedigree, recorded per the ACTUAL `r5` verdict.**  The paragraph
that stood here at `r5` pre-recorded a gate ruling in the authoring lane's favour, and the
gate reached the opposite conclusion on the half that mattered.  It is replaced, not
softened; recording a verdict before the gate returns it is the "forecasts are not
premises" defect, and banking that paragraph would have inherited it as fact.

*What the `r5` gate actually returned* (`handoffs/cc-formalize/judge-cc-t8h-r5-projection-gate.md`,
verdict of record: `TRANCHE_VERDICT: REVISE`, 46 CLEAR / 2 REVISE of 48): **D28 and D29 were
the two REVISEs.**  Two defects were named.  **No advance clearance is recorded for either.**
The `r7` gate itemized the sentence that stood here -- "both are now repaired here" -- as a
second advance-clearance claim and rejected it; the previous round's own D28--D34 were all
returned REVISE.  What follows is therefore a statement of what was **moved**, with no
prediction of how any gate will rule on it.  The first item was subsequently confirmed
applied by the `r7` verdict (`ANSWER Q3`); the second was **not**, and its repair is the
`cc-t8i` re-site recorded in §4c.

1. **D29 pinned the retained leaf output label to `false`** at all ten sites of its
   statement span.  `09:1203--1205` reads "append `r-d` fixed Alice messages and **retain
   the original output label** at the new leaf" -- the frozen text retains the label, it
   does not fix it.  D29 now binds `(z : Bool)` universally and the banked owners
   `aliceLadder (a) (z)` / `completedNoBob_aliceLadder (a) (z) (r)`, which were already
   general in `z`, are consumed at that generality.
2. **The `r5` audit point put a numeral where the schedule defines a quantity.**  That
   probe ran at `r = 1`, **`b_T = 3`**, `W = Fin 4`, `E_0 = empty`; `06:241` defines
   `b_T = 2^{j_49(k_T)}`, so `b_T = 3` is a manufactured point in exactly the sense the
   DEFINITIONAL-CHAIN rule names -- and no more legal than the `b_T = 19` rejected at `r4`.
   **That probe is withdrawn**, and `scratch/t8h_r5_gate_hypcheck.lean` is superseded.
   D29 carries the chain as four explicit pins (`hu` = `06:116--117`, `hkT` = `06:239`
   over the banked `sScale`, `hbT` = `06:241` over the banked `j49`,
   `hgate` = `06:267`).  The `r6` attempt to discharge them **inside this module** was
   itself returned REVISE at `r7` -- it assigned `B_s = 112` where `02:819` defines
   `B_s = T^2` -- and is deleted at `cc-t8i`; the discharge now happens downstream, at
   `FrontierScheduleReceipt.paperSchedulePins_hold_at_the_derived_point`, with all
   three rows of `eq:hard-seed-width-gates` proved from the banked K1 chain.

*What is unchanged, and was never in dispute.*  Canonical inhabitation stays REGISTERED and
DEFERRED under `FRONTIER-SUM-ASSEMBLY-001`: the paper-legal instance of D29 would be a
routed system over the alleged `(C+r-1)`-bit protocol of `09:1187--1193`, and the whole
subsection exists to show that protocol does not exist, so the frozen paper exhibits no
instance to demand.  D29 remains a **NON-FIDELITY** receipt over the completed Alice
ladder -- a legal frame that is not the alleged protocol.  **The claim that "`B_s` and
`u` are ours" is WITHDRAWN**: `02:815--819` defines `B_s = T^2` and `06:116--117`
defines `u`, and `06:263` is a use site, not a definition.

*The surface question raised here has been ANSWERED, by the module downstream.*  Three
links of the `02:815--819` / `06:237--243` chain (`MechanicalCompilerResidue.bsSched`,
`ScheduleTemplateResidue.kT`, `.bT`, and the `Section5Admissibility.*Of` accessors) have
banked owners this module cannot pin, because their homes import it transitively; the
import paths are printed in §4c.  The links carry as equational hypotheses on their
defining displays, nothing banked was rewritten, and the remedy -- a module downstream of
both -- is now built: `EthInapproximability.ParameterizedNP.FrontierScheduleReceipt`.

### L10.  THE r6 DELTA, ITEM BY ITEM

The `r5` verdict of record returned `TRANCHE_VERDICT: REVISE` with exactly two
per-declaration REVISEs, D28 and D29.  This is what `r6` moved.

1. **D29 binds `(z : Bool)`** and all **ten** statement occurrences of `aq false r` in
   its span became `aq z r`, plus the one proof-side occurrence.  Frozen warrant
   `09:1203--1205`.  The binder is UNIVERSAL, never `exists z`: the receipt now holds
   for *every* retained label, which is a strengthening of the statement, not a
   weakening of it.  Residue check on these bytes, run in BOTH polarities: `aq false`
   occurs **0** times in any statement or proof term, and its four surviving occurrences
   are all prose -- D29's own docstring saying what was repaired (`:2437`), L4's
   historical screen-power probe string (`:3605`), and the two sentences you are reading
   (`:3887`, `:3891`).  `aq z r` occurs **15** times on the `cc-t8i` bytes: the ten
   statement sites (`:2565`, `:2569`, `:2575`, `:2578`, `:2581`, `:2585`, `:2587`,
   `:2592`, `:2595`, `:2597`), the one proof site (`:2618`), and four prose descriptions
   of the pin (`:2269`, `:2426`, `:3888`, `:3895`).  The ten statement coordinates are
   the `r6` list shifted by the round's `+22` docstring offset and then re-verified by
   `rg`, not shifted on trust.
2. **D29's Stage-3 depth is pinned to `06:237--243`** by `hu`, `hkT`, `hbT` and the
   `06:267` gate `hgate`.  `b_T` was a free binder at `r5` and is not one now; `u` and
   `k_T` are new and are pinned from the start.  Nothing about the conclusion changed.
3. **The withdrawn `b_T = 3` point.**  `scratch/t8h_r5_gate_hypcheck.lean` is marked
   SUPERSEDED at its head, with both of its defects named (the manufactured `b_T` and
   the `06:1110` misattribution).  Its replacement is in `src/`, as D33/D34.
4. **Five new declarations, D30--D34** (§4c), all `theorem`, no new `def`, `abbrev`,
   `structure`, `instance` or `axiom`.  D30--D32 are general facts about the chain;
   D33 is the HYPOTHESIS-CONSISTENCY receipt; D34 fires D29 at it.  `#print axioms`
   rows for all five were added to `tools/AxiomAudit.lean`, and each returns exactly
   `[propext, Classical.choice, Quot.sound]`.
5. **`u` is at its DERIVED value in D33, not a convenient one.**  The first draft of the
   witness used `u = 1`, which the banked `ParameterSchedule.three_le_uAux` (`3 <= u`,
   from `06:111--117`) makes **illegal**; the banked lemma was consulted and the witness
   is now `u = uAux (Apre 0 0 0 0) = 3`.  Recorded because it is the same defect class
   as the `b_T` numeral, caught one level further down the same chain.
6. **`xTdepth_antitone` was NOT authored.**  It already exists at
   `TranscriptLevelSuccessors.lean:507`, upstream of this module, and is consumed by pin
   inside D32.  The `r6` dedup sweep over all 237 files found **0** occurrences of any of
   the five new names outside this module (L5).
7. **Record repairs carried this round** (all comment-only, no statement byte moved by
   them): the ten `x_T = 2^{-b_T}` citations re-anchored from `06:1110` to `06:243`,
   with the **nine** `y = 3/5` citations to `06:1110` deliberately LEFT ALONE because
   frozen `06:1108--1110` reads `x = 2^{-b_1}, y = 3/5` and only the `x` half is
   misattributed; `tools/AxiomAudit.lean`'s `09:1188--1193` normalized to
   `09:1187--1193`; and the pre-recorded gate ruling replaced by the actual verdict.
8. **Not touched by this lane**, deliberately: `docs/atlas/FrontierSumAssembly.md`,
   `docs/ARCS_TO_DONE.md`, the `OBLIGATION_LEDGER`, `MassRedistributionTail.lean`, and
   every banked module.  The `vartheta_twins_agree` ledger row (`S-6`) remains a
   bank-round action and is carried, not executed here.

**Items 4, 5 and 6 of this list are SUPERSEDED**: the five declarations they describe
were returned REVISE at `r7` and are deleted at `cc-t8i` (L11).  The list is kept as the
record of what `r6` did, not as a claim about these bytes.

### L11.  THE `cc-t8i` DELTA, ITEM BY ITEM

The `r7` verdict of record (`handoffs/cc-formalize/judge-cc-t8h-r7-inhabitant-gate.md`)
returned `TRANCHE_VERDICT: REVISE`, 46 CLEAR / 7 REVISE over 53, with all seven REVISEs
on `D28`--`D34`, and ruled the repair a **REPAIR-STOP** under the IMPORT-DIRECTION RULE:
a construction obligation for a new module downstream of both `FrontierSumAssembly` and
`MechanicalCompilerResidue`, not an in-round edit.  This round executes that order.

1. **`D30`--`D34` deleted** (§4c).  No statement or proof byte of any surviving
   declaration moved.  The re-sited content is
   `EthInapproximability.ParameterizedNP.FrontierScheduleReceipt`, a new module
   importing this one, which proves **all three** rows of `eq:hard-seed-width-gates` at
   `B_s = MechanicalCompilerResidue.bsSched` (`02:819`) rather than at a chosen numeral.
   Residue check run in BOTH polarities (L5): the five short names head nothing anywhere
   in `src/` or `vendor/`, and every survivor is prose.
2. **`D29`'s `B_s` paragraph corrected.**  The GENUINELY-FREE@`06:263` reading is
   withdrawn as USE-AS-DEFINITION; `B_s` is SOURCE-DEFINED@`02:815--819` and is a binder
   here only because its banked owner is downstream.  The statement is **byte-identical**
   -- only the docstring changed, by `+22` lines.
3. **The L2 binder table's zero-claim corrected.**  The `r6` claim "Source-DEFINED
   quantities entering as FREE binders anywhere in the `r6` delta: 0" was ruled FALSE at
   `r7`.  It is replaced by a positive count of one, with the disclosure that the one is
   forced by the import direction and is discharged downstream.
4. **The advance-clearance sentence at L9 removed**, per the `r7` itemization; no gate
   ruling is pre-recorded anywhere in this module.
5. **The recomputation sentence at the head of this report corrected**: it said the
   tables were recomputed on the `r4` bytes over rows that were `r6` rows.  It now states
   the round-by-round provenance exactly, including this round's `+22` shift.
6. **Tables recomputed on these bytes**: L1 `276 -> 230` occurrences (`62`
   CANONICAL-FORM / `168` EVALUATED / **`0` BEYOND-PAPER**), L3 `34 -> 29` rows, L5
   re-run with the five names barred.  Every `D29` coordinate re-verified by `rg` after
   the shift.
7. **`tools/AxiomAudit.lean`**: the five `#print axioms` rows for `D30`--`D34` are
   removed and rows for the new module's declarations are added there.  That file is a
   shared surface; this is the only edit made to it.
8. **Still not touched by this lane**: `docs/atlas/FrontierSumAssembly.md` (whose revert
   the `r7` verdict rules a verify-seat action), `docs/ARCS_TO_DONE.md`, the
   `OBLIGATION_LEDGER`, `MassRedistributionTail.lean`, `vendor/`, `reference/`, every
   `routes/parameterized-np/versions/` directory, and every other banked module.

### L12.  THE `cc-t8j` LANE-3 DELTA — every screen extended to the 8 appended declarations

`cc-t8j` lane 3 appended **8** declarations at `:2847`ff. (§6 and §6a) and, at `r0`,
extended **none** of L1--L6 to them.  The `cc-t8j` gate ruled that INCOMPLETE-BY-CONTRACT
(finding F-9) and recorded that the report's own non-staleness sentence and its
1:1-cover claim had become false.  This section is the repair: every screen above is
re-run on the 8 new declarations and its rows are written here.  **The counts in L0 and
the roster header in L3 are corrected in place to the post-delta figures; the L1--L6
tables above are the `cc-t8i` surface and are unchanged, so the two sets partition the
module.**

The 8, with their in-section names and their statement spans (head line -> first `:=` at
bracket depth zero, L0's rule):

  W-1  theorem twoCoordPair_projection_at_a_supplied_cover          :3051 -> :3069  num 9
  W-2  theorem earlyMass_at_the_supplied_cleanCount                 :3124 -> :3134  num 4
  W-3  theorem canonical_earlyMass_of_reference_construction        :3199 -> :3281  num 90
  W-B1 theorem wiring_capacity_family_is_bobCapacity                :3312 -> :3314  num 0
  W-B2 theorem earlyMass_conclusion_is_monotone_in_e0               :3326 -> :3329  num 3
  W-B3 theorem earlyMass_conclusion_is_monotone_in_the_coefficient  :3347 -> :3350  num 3
  W-B4 theorem suppliedCover_is_not_everything                      :3373 -> :3377  num 0
  W-B5 theorem earlyMass_wiring_fires_at_the_banked_probe           :3418 -> :3421  num 6

**L12.3 ROSTER RECEIPT — 8 rows, above.**  All 8 are `theorem`s; the delta declares no
`def`, no `structure`, no `instance`, no `abbrev` and no `axiom`, so it opens no new
canonical-inhabitation obligation (§6a repeats this).  Post-delta the module holds
**45** declarations (42 `theorem` + 3 `def`): the 29 `cc-t8i`-gated rows `D01`--`D29`,
the 8 non-gated baseline rows listed at the foot of L3, and these 8.

**L12.1 STATEMENT-NUMERAL SCREEN — one row per occurrence, 115 rows.**

*W-3's 87 inherited rows, separated first so the remaining rows can be read.*  W-3's
lines `:3200--3272` are **byte-identical** to `D25`'s `:2090--2162` — re-verified by
line-by-line diff on these final bytes: 72 of the 73 lines match exactly, and the one
that differs (`:3272` against `:2162`) differs **only** in the trailing ` :` that opens
`D25`'s conclusion where W-3's binder list continues.  Those 73 lines carry **87** of
W-3's 90 numeral occurrences, and each carries `D25`'s existing L1 row and class
unchanged; they are counted here and not re-classified, because re-classifying a
byte-identical binder list would be a second opinion about the same bytes.  W-3's own
lines are `:3273--3281`, with **3** occurrences, classified individually below.

Columns: `file:line` | numeral | class | role.

  W-1
    :3055   0   CANONICAL-FORM  N17  positivity of a carrier cardinality, no frozen value
    :3055   2   EVALUATED       N03  `09:442--445` the cover family needs its `l = 1` member
    :3056   0   CANONICAL-FORM  N17  positivity side condition on the DEFINED `rho_*`
    :3059   1   CANONICAL-FORM  N30  legality ceiling on the DEFINED `rho_*` (`09:405--411`)
    :3060   0   CANONICAL-FORM  N17  positivity of the free retained-column density
    :3068   3   EVALUATED       N04  `06:1110` `y = 3/5`
    :3068   5   EVALUATED       N05  `06:1110` `y = 3/5`, denominator
    :3068   2   EVALUATED       N06  `09:1332` `y^2`, the retained squared density
    :3068   2   EVALUATED       N07  `09:1331--1332` the two-coordinate column exponent
  W-2
    :3127   0   CANONICAL-FORM  N17  positivity of the free outer-column density `theta_E`
    :3127   1   CANONICAL-FORM  N36  nondegeneracy floor `1 <= s` of `earlyMassCoeff`
    :3132   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
    :3134   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
  W-3
    :3200--:3272  87 occurrences  INHERITED FROM `D25` BYTE-IDENTICALLY (see above);
                  classes and roles are `D25`'s L1 rows `:2090--2162`, unchanged
    :3274   0   CANONICAL-FORM  N17  positivity of the free `theta_E`
    :3274   1   CANONICAL-FORM  N36  nondegeneracy floor `1 <= s` of `earlyMassCoeff`
    :3281   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
  W-B1
    (no numeral occurrence in the statement span)
  W-B2
    :3327   0   CANONICAL-FORM  N17  nonnegativity of the abstract coefficient
    :3328   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
    :3329   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
  W-B3
    :3348   0   CANONICAL-FORM  N17  nonnegativity of the scaled quantity `e_0`
    :3349   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
    :3350   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`
  W-B4
    (no numeral occurrence in the statement span)
  W-B5
    :3419   0   CANONICAL-FORM  N17  positivity of the free `theta_E`
    :3419   1   CANONICAL-FORM  N36  nondegeneracy floor `1 <= s` of `earlyMassCoeff`
    :3420   0   BEYOND-PAPER    N37  the probe's own mass family `P_v = 0`
    :3421   4   BEYOND-PAPER    N37  the probe's own outer width `q = 2^2 = 4`
    :3421   1   BEYOND-PAPER    N37  the probe's own exceptional count `e_0 = 1`
    :3421   1   EVALUATED       N27  `09:1353--1357` `e_0/(1 - vartheta)`

Two role codes are new and are added to L1's closed legend rather than invented as a
fourth class:

  N36  nondegeneracy floor `1 <= s` of `earlyMassCoeff` (`09:1526--1529`); a positivity
       side condition on a free schedule input, no frozen value
  N37  a numeral of the **synthetic** banked probe `DenseWrapperFrontier.wrapperFrontierProbe`
       and of `wrapperCleanCount_legal_instance`: read off the banked instance rather
       than chosen, but the frozen source fixes no such value, so BEYOND-PAPER

**Class totals for the delta.**  115 occurrences: 87 inherited byte-identically from
`D25` (classes unchanged), and **28** classified here — 13 EVALUATED, 12 CANONICAL-FORM,
**3 BEYOND-PAPER**.  0 unclassified, 0 outside the three classes.

**Correction to L0, stated rather than silently patched.**  L0's headline says "0
BEYOND-PAPER ... so that class is now **empty** here".  That was true on the `cc-t8i`
bytes and is **false** after this delta: W-B5's three probe numerals repopulate the
class.  L0's headline is corrected in place, and the module-wide figures are now
**45 declarations, 345 statement-position numeral occurrences (230 + 115), 3
BEYOND-PAPER, 0 unclassified**.

**L12.2 BINDER-PROVENANCE TABLE — one row per declaration, 8 rows.**  The question each
row answers is the standing one: does a *source-DEFINED* quantity enter as a free binder?

  W-1   **NO defined quantity is bound.**  `rho_*` is `09:407`'s DEFINED
        `max{rho_sing, 1 - eta_C}` and is **pinned** as `WrapperProjectionCovers.rhoStar`,
        with its arguments evaluated down the chain: `n = |Y|` (`09:364`) as
        `Fintype.card Yc`, `tau_0` (`09:376`, `2 s x_T`) through `tauZero` at
        `DenseStageFourOpening.xTdepth`, `eta_C` (`06:206--211`) through
        `ParameterSchedule.etaC`.  `e0Max` and `coverExponent` are likewise pinned.
        Residually free, each for a stated reason: `m_T` (`09:364--372`, a template
        readout this declaration does not build), `dv` = `delta_v(G)` (`06:206--211`
        states it as an explicit binder, not a formula), `s` (`06:118`) and `bT`
        (`06:241`) — IMPORT-DIRECTION-FORCED binders of the standing disclosed class,
        their owners' homes importing this module transitively.  `theta_cov` is `09:404`'s
        retained OUTER column density and is deliberately a **separate** binder from
        `def:bracket`'s `theta`; `k` is the cover index.  `hr0`/`hr1` are legality side
        conditions on the DEFINED value, not substitutes for it.
  W-2   **NO defined quantity is bound.**  The coefficient is the pinned
        `WrapperMassRedistribution.earlyMassCoeff` and is never re-rolled; `vartheta` is
        the banked `9/16` constant, pinned.  Free: the frontier `F`, the certificate
        assignment `cert`, the mass family `Pv`, `e0`, and the coefficient's own schedule
        inputs `theta_E` and `s` — all of which the frozen display leaves as inputs at
        this site.  `theta_E` is again separate from the bracket `theta`, for W-1's reason.
  W-3   **NO defined quantity is bound**, and one that W-2 leaves free is EVALUATED:
        `e_0` in the conclusion is `(E0.card : R)`, `09:450`'s definition read at the
        construction's own exceptional set, never a parameter.  The binder list is
        `D25`'s verbatim (diff above), so `D25`'s L2 row transfers unchanged; the five
        appended binders are `Pv`, `theta_E`, `s`, `hne`, `hlt`, of which the first three
        are W-2's free inputs and the last two are W-2's poles.  `hne` is an **added**
        hypothesis with no supplier at the canonical system — REGISTERED as
        `FRONTIER-SUM-ASSEMBLY-002` (W-3's docstring; `cc-t8j` gate finding F-10), not
        claimed discharged.
  W-B1  **NO defined quantity is bound.**  `bobCapacity` and `capacity` are the banked
        `DenseWrapperFrontier` readouts, pinned; the frontier and its carrier are free.
  W-B2  **NO defined quantity is bound.**  Stated on four abstract reals; `vartheta` is
        pinned.  The coefficient is deliberately abstract (`cf`) because the monotonicity
        is of the conclusion SHAPE, not of the constant.
  W-B3  As W-B2, in the coefficient argument.
  W-B4  **NO defined quantity is bound.**  `e0Max` is the pinned cover budget and the
        three cover exponents `Bref`/`Bsing`/`Bpair` and the index `k` are free naturals;
        `hbudget : e0Max … < q` is an explicit binder, the regime
        `sec:wrapper-projection-covers` runs in, stated rather than assumed.
  W-B5  **NO defined quantity is bound**, and `theta_E` and `s` stay FREE so nothing about
        the schedule is chosen.  The two numerals that are fixed (`q = 4`, `e_0 = 1`) are
        **read off** the banked `DenseWrapperFrontier.wrapperCleanCount_legal_instance`
        and `wrapperFrontierProbe`, not selected — and they are BEYOND-PAPER (N37), which
        is why this declaration is labelled NON-FIDELITY.

**L12.4 DEDUP SWEEPS, RUN ON THESE BYTES.**  Corpus re-parsed at these final bytes by the
same method as L4: **242** `.lean` files under `src/` and `vendor/`, comment-stripped
nesting-aware, `theorem`/`lemma`/`def`/`abbrev`/`instance`/`structure`/`inductive` heads
including attribute and modifier prefixes — **8799** declaration heads, **8693** distinct
short names.  (L4's `cc-t8i` figures 237/8698/8398 predate this tranche's three new
modules and used a slightly different head regex; the delta is corpus growth plus parser
hygiene, not a change in the tree.  Both figures are reported rather than reconciled by
fiat.)

*(a) Whole-statement sweep*, statement spans normalized (comments stripped, whitespace
collapsed, namespace prefixes dropped, explicit named arguments `(X := …)` deleted),
token-set Jaccard against every corpus declaration outside these 8, reporting at
`>= 0.82`.  **4 pairs cleared the threshold, all of them W-3, and no other of the 8
appears at any threshold:**

  0.889  W-3  vs  `FrontierSumAssembly`
         `.canonical_cleanCount_of_reference_construction_and_twoCopy` (:2089)
  0.873  W-3  vs  `FrontierSumAssembly.canonical_firstBob_light_of_reference_construction` (:520)
  0.856  W-3  vs  `FrontierSumAssembly.canonical_frontierSum_against_the_light_bound` (:647)
  0.830  W-3  vs  `ProtectedEarlyClosure.canonical_bobCapacity_le_earlyMassSlot` (:553)

All four are the **reference-construction guard telescope** artefact that L4 already
adjudicates for `D25`, and the adjudication transfers because W-3's binder list *is*
`D25`'s: every declaration that consumes or supplies that construction carries the same
72 lines, so the tokens agree while the CONCLUSIONS share nothing.  The first is W-3's own
declared supplier, consumed by pin and proved by calling it — consumption, not
republication.  The second and third are this module's baseline declarations, byte-identical
to `9c17653` and outside every gated set; their conclusions are the light bound and the
conservation comparison, W-3's is the early-mass sum bound.  The fourth sits **downstream**
(`ProtectedEarlyClosure` imports this module) and carries the telescope in order to consume
it.  No pair is a duplicate.

*(b) Intra-set sweep* (the 8 against each other, same threshold): **EMPTY.**

*(c) UP-TO-SPECIALIZATION sweep.*  For each of the 8, a head-symbol skeleton of the
conclusion is computed (explicit named arguments deleted first) and scored against every
corpus conclusion outside the 8; nothing reaches `0.90`, and the nearest neighbour of each
is printed so the margin is visible rather than asserted:

  W-1   0.786  `twoCoordPair_projection_retains_y_sq` (FrontierSumAssembly.lean:935)
  W-2   0.583  `wrapperTotalEarlyMass_frozen` (WrapperMassRedistribution.lean:533)
  W-3   0.500  `canonical_wrapperTotalEarlyMass` (ProtectedEarlyClosure.lean:857)
  W-B1  0.600  `two_le_capacity_firstBob` (DenseWrapperFrontier.lean:909)
  W-B2  0.250  `wrapperTotalEarlyMass` (WrapperMassRedistribution.lean:515)
  W-B3  0.333  `cleanCount_supplies_the_earlyMass_slot` (FrontierSumAssembly.lean:2811)
  W-B4  0.600  `startedIdx` (SelectEmbedComposition.lean:314)
  W-B5  0.231  `wrapperTotalEarlyMass_frozen` (WrapperMassRedistribution.lean:533)

The two that matter are read, not just scored.  W-1's nearest neighbour is its own declared
**consumer site**: W-1's conclusion is existentially strengthened over it (`∃ E0, …`) and
its hypotheses are exchanged, not reduced — which is exactly what the corrected §6 preamble
now says, and which is why W-1 is not a specialization of it in either direction.  W-2's is
its own declared **supplier**, instantiated at `F.bobNodes`/`F.capacity` with `hKB` retired,
i.e. strictly fewer binders at a pinned family (W-B1 records that the family is a pin, not a
choice); a specialization that *retires* a binder by pinning a banked owner is the
substitution this section is for, and it is not a republication because deleting the
supplier breaks the typecheck.  W-3's nearest neighbour is **downstream** of this module and
so cannot be an owner it should have consumed.

*(d) Barred names.*  No name deleted by any preceding round of this module (`D30`--`D34`,
the `r6` §4c batteries) is re-minted by any of the 8; checked in both polarities on these
bytes.

**L12.5 CROSS-MODULE SHADOW CHECK.**  Each of the 8 short names intersected against every
declaration head in the 242-file corpus: **EMPTY** — no short name of any of the 8 is
declared in any other file, and none shadows a banked name.

**L12.6 ATLAS CROSS-CHECK ("Do not re-author" rows, read at these bytes).**

* `docs/atlas/FrontierSumAssembly.md` (this module's own card) — "the interface adapter
  into the protected-mass subsection is `cleanCount_supplies_the_earlyMass_slot`, and the
  `e_0` weakening is `cleanCount_conclusions_are_monotone_in_e0`".  W-2 **consumes** the
  adapter by pin (`:2811`) and does not restate it.  W-B2 is a **second** `e_0`-weakening,
  at a different conclusion shape — the early-mass strict bound, not the clean-count
  bound — and is stated on abstract reals; it neither replaces nor re-proves
  `cleanCount_conclusions_are_monotone_in_e0`, which stays the clean-count owner.  Noted,
  **no hit**.  The same card's "The `e_0` evaluation is `startedCoord_census_evaluates_e_zero`;
  do not reintroduce `e_0` as a free parameter" is respected by W-3, whose conclusion reads
  `e_0` as `(E0.card : R)`; W-2 does carry a free `e0`, deliberately, because it is stated
  at an **arbitrary** frontier where no census exists — and W-3 is the declaration that
  removes that freedom at the canonical system.
* `docs/atlas/WrapperProjectionCovers.md` — "The cover budget is `e0Max` with
  `e0_le_e0Max`, and the assembled deliverable is `exists_initial_exceptional_set`."  W-1
  consumes `exists_initial_exceptional_set` by pin (it had **zero** external consumers
  before) and W-B4 reasons *about* `e0Max` without redefining it or introducing separate
  `B_*` constants.  **No hit.**
* `docs/atlas/WrapperMassRedistribution.md` — "Every frozen display of `09:1512--1781` is
  reified exactly once here — `wrapperTotalEarlyMass` … — and none may be rebuilt inline";
  "`earlyMassCoeff` … are the module's reified quantities."  W-2 and W-3 **fire**
  `wrapperTotalEarlyMass_frozen` and consume `earlyMassCoeff` by pin; W-B2/W-B3 state
  monotonicity of the **conclusion shape** on abstract reals and re-roll no display.
  **No hit.**
* `docs/atlas/DenseWrapperFrontier.md` — "the counting readouts
  `bobNodes`/`finalNodes`/`cleanNodes`/`splitNodes`/`bobCapacity` … are the consumption
  surface"; "The probe (`probeRoute`, `probeFirstBob`, `wrapperFrontierProbe`, `probeCert`,
  …) already inhabits the frontier nondegenerately … reuse it rather than building another."
  W-B1 records `∑ capacity = bobCapacity` at the banked readouts and defines nothing; W-B5
  **reuses** the banked probe and `wrapperCleanCount_legal_instance` rather than building a
  frontier, exactly as instructed.  **No hit.**

**L12.7 WHAT L12 DOES NOT CLAIM.**  It certifies the provenance and reproducibility of the
screens over the 8 appended declarations, and nothing else.  It does not narrow the header
census: `09:1367--1781` stays OPEN and `eq:wrapper-u-dense` is not approached.  It does not
discharge canonical inhabitation, which stays REGISTERED and DEFERRED under
`FRONTIER-SUM-ASSEMBLY-001`.  It does not discharge W-3's `hne`, which is REGISTERED as
`FRONTIER-SUM-ASSEMBLY-002` and remains open.  And it does not bank anything: the ledger
row, the crosswalk, the atlas cards and `docs/BANKED_SURFACE_INDEX.md` are the verify seat's
bank-time duties, and the tranche verdict is the gate's to give.

-/
end EthInapproximability.ParameterizedNP.FrontierSumAssembly
