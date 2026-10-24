import EthInapproximability.ParameterizedNP.TerminalTwoStream

/-!
# Parameterized NP route: the dense scale-alignment frontier

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8a54aaa6f0e60eaeb31ac1719cd696b169d5a845381fbd810a18a86c6b2a24e5`),
  **lines 1184--1366** -- the subsubsection `sec:dense-wrapper-frontier`, opening
  at `09:1184--1185` ("The dense scale-alignment frontier") and closing at
  `09:1366`, immediately before `sec:wrapper-protected-early` at `09:1367`.  The
  anchors traced here, in the order the frozen block prints them:
  * `09:1187--1193`, the contradiction frame: "We now prove the remaining
    full-strength estimate `eq:wrapper-u-dense`.  Fix an arbitrary retained
    matrix `U' in [U]_{1, 1-delta_U, theta}` and suppose for contradiction that a
    protocol `P` of cost at most `C+r-1` computes `U'`."
  * `lem:wrapper-no-bob-completion` (label `09:1196`, statement `09:1195--1200`,
    proof `09:1202--1213`), with its three frozen clauses -- the appended
    `r-d` fixed Alice messages, the new depth "exactly `r`", and the cost bound
    `max{cost(P), r} <= C+r-1` "because `C >= 1`" -- and the closing
    "No path containing a Bob query is modified."  The statement's quantifier is
    "**every** root-to-leaf path containing no Bob query", with no depth
    restriction; "their new depth is exactly `r`" (`09:1206`) is a remark about
    the formerly short paths inside the *proof*, and is carried here as the
    separately guarded `wrapperNoBobCompletion_exact_on_short`, never as a
    hypothesis of the lemma.
  * `09:1217--1222`, the reference-row geometry `A_0 = ceil(2 x_T m_G)`,
    `A_k = 2^k A_0`;
  * `eq:wrapper-initial-survival` (label `09:1231`, display `09:1224--1232`),
    the three row-survival gates `q A_0/m <= eta_R/16`,
    `q A_0 + delta_U q m <= m_G`, `q(q-1)A_0/m_G <= eta_R/(16 g)`;
  * `09:1233--1236`, "Even if every deleted row of `U` were concentrated in one
    nonexceptional outer coordinate, that coordinate would therefore retain at
    least `A_r = q A_0` reference rows.  Start one clean reference certificate in
    every coordinate outside `E_0`, each with weight one";
  * `09:1238--1248`, the routing rule and the certificate weights: "At remaining
    selector capacity `2^k`, a certificate consists of at least `A_k` reference
    rows in one outer coordinate.  At an Alice query, route it to a child
    containing at least `ceil(A_k/2) >= A_{k-1}` of those rows; route it to both
    children if both qualify.  A clean certificate routed uniquely stays clean
    with weight one.  When a clean certificate splits, both descendants become
    low certificates of weight `1/2`.  A low certificate keeps weight `1/2`,
    whether it has one or two qualifying children.  Thus total certificate weight
    never decreases";
  * `09:1250--1258`, the frontier: "Stop each routed branch at its first Bob
    query, or after `r` Alice queries.  A Bob query that occurs only after all
    `r` Alice queries is not exposed; its state is a final Alice-frontier node.
    If `v` is a frontier node, let `d_v` be the number of preceding Alice queries
    and set `kappa_v = 2^{r-d_v}`, `W_v = total certificate weight at v`";
  * `09:1259`, "Every first-Bob node has `kappa_v >= 2`.  Prefix-freeness and
    conservation give";
  * `eq:wrapper-frontier-conservation` (label `09:1265`, display `09:1261--1266`),
    `sum_v W_v >= q - e_0` and `sum_v kappa_v <= q`;
  * `09:1268--1276`, `vartheta = 9/16` and the large-capacity branch: "We first
    close any first-Bob node satisfying `W_v >= vartheta kappa_v`.  When
    `kappa_v >= t_ref`, follow the denser Bob child and invoke the
    certified-scale reference stopping lemma on `G` with `r' = kappa_v/t_ref`,
    `a^sharp = 1`.  The other parameters are those of `sec:wrapper-low-rungs`.
    This gives residual complexity at least `C + log_2 kappa_v - 1`";
  * `09:1276--1305`, the small-capacity branch: `ell_v = log_2 kappa_v`,
    `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}` with "the cases
    `kappa_v = 2,4,8` ... immediate, and for `kappa_v >= 16` it follows from
    `9 kappa_v/16 >= kappa_v/2 + 1`", the parent density `rho = 2y^2`, the
    denser Bob child density `y^2`, `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
    m_G`, the trim to row density `kappa_v x_T`, and the
    `lem:certified-row-ladder` invocation at `M = G`, `H = C-1`, `x = x_T`,
    `z = y`, `ell = ell_v`, whose guards are `lem:wrapper-reference`, `C >= 3`
    (giving `H >= 2`) and `kappa_v x_T <= t_ref x_T <= 1`;
  * `09:1306--1308`, "Its lower bound is one more bit than the remaining child
    budget in the alleged protocol";
  * `eq:wrapper-first-bob-light` (label `09:1312`, display `09:1309--1313`),
    the **strict** `W_v < vartheta kappa_v` at every first-Bob node;
  * `lem:final-reference-uniqueness` (label `09:1316`, statement `09:1315--1319`,
    proof `09:1321--1344`), including the distinctness of the two source
    coordinates, the avoidance of the `u_2 = 2` cover, the `ell = 1` ladder
    invocation and the closing budget contradiction `C` against `C-1`;
  * `09:1346--1350`, "Thus every final Alice node contains either one clean
    certificate, one half-weight descendant of a split certificate, or none.
    Let `K_B` be the sum of `kappa_v` over first-Bob nodes, let `c` be the number
    of final nodes with one clean certificate, and let `ell` be the number with
    one split certificate";
  * `eq:wrapper-clean-count` (label `09:1356`, display `09:1352--1357`) and its
    derivation `09:1358--1365`, `q - e_0 <= vartheta K_B + c + ell/2 <=
    vartheta(q-c) + c` and `K_B + c + ell <= q`.
* **Predecessor anchors for the external calls the block makes.**
  `09:1270` invokes "the certified-scale reference stopping lemma", identified at
  `09:313--314` as `thm:certified-localized-extension` (`A:109--146`);
  `09:1297--1301` and `09:1334--1338` invoke `lem:certified-row-ladder`
  (`A:148--162`); `09:1302` and `09:1339` name `lem:wrapper-reference`
  (`09:151--162`) as the base certificate; `09:1275` defers "the other
  parameters" to `sec:wrapper-low-rungs` (`09:274--333`); the `u_2 = 2` and
  `u_kappa = kappa/2 + 1` covers and `rho = 2y^2` are `09:434--447`.
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q,t,eps)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design and appears
  in no hypothesis below: the large-capacity branch's endpoint call is not
  transcribed here (see GAP-EXPOSED 3), so its balanced-family-or-exact-product
  branch (`A:126--128`) is never reached.  `LegacyNPCC.Stage12` -- whose closure
  reaches the cited AGHP balanced-family axiom -- is **not** imported, and no
  declaration here is in its dependency graph.
* **The terminal lemma is cited conditionally and never applied.**
  `lem:terminal-two-stream` (`09:834--860`) is banked as a *stated* claim, not a
  proved theorem (`TERMINAL-TWO-STREAM-001`).  Inside `09:1184--1366` the frozen
  text never `\Cref`s it at all -- its only Section-9 citations are `09:1177`
  (the `readingwarning` box preceding this block) and `09:1676` (a later range).
  Accordingly **no declaration below mentions
  `TerminalTwoStream.TerminalTwoStream` or any of its conclusions**, and none is
  derived from it; the import is present only because the banked
  `certifiedRowLadder_of_base` -- a *proved* theorem of that module -- lives
  there and is consumed by pin.
* **New work.**  The completion arithmetic of `lem:wrapper-no-bob-completion`;
  the `A_k` geometry with its exact halving identity; the three survival gates as
  a transcribed predicate with its retention consequence; the certificate weight
  algebra with the frozen "never decreases" clause proved; the frontier record
  with `kappa_v >= 2` at first-Bob nodes and `kappa_v = 1` at final nodes; the
  dyadic estimate `ceil(9 kappa/16) >= u_kappa`; both budget contradictions
  (`eq:wrapper-first-bob-light` and `lem:final-reference-uniqueness`); and
  `eq:wrapper-clean-count`, proved outright from the aggregated conservation
  inequality and Kraft.
* Proof status: **new** for everything named in the previous item; **inherited by
  pin** for Kraft (`DenseFrontierConservation.sum_stoppingCapacity_le_width`),
  the capacity weight and prefix-freeness (`DenseWeightedCount`), the
  small-copy widths and the `2y^2` density (`WrapperProjectionCovers`), the
  `t_ref` row legality (`WrapperLowRungs`), and the certified row ladder
  (`TerminalTwoStream.certifiedRowLadder_of_base`).
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Predecessor modules consumed **by pin**, never restated

* `EthInapproximability.ParameterizedNP.DenseWeightedCount`:
  `stoppingCapacity` (the frozen `kappa_v = 2^{r-d_v}`, `08:1113`, which
  `09:1254--1256` reintroduces at the wrapper width and this module does not
  restate), `one_le_stoppingCapacity`, and `PrefixFreeFrontier` (`08:981`),
  which is exactly the "Prefix-freeness" of `09:1259`.
* `EthInapproximability.ParameterizedNP.DenseFrontierConservation`:
  `sum_stoppingCapacity_le_width` -- Kraft's inequality for a prefix-free
  frontier, `sum_v kappa_v <= 2^r`.  This **is** the second clause of
  `eq:wrapper-frontier-conservation` (`09:1264`) at the wrapper width `q = 2^r`;
  it is consumed, never re-proved.
* `EthInapproximability.ParameterizedNP.WrapperProjectionCovers`:
  `smallCopyWidth` (the frozen `u_kappa = kappa/2 + 1` and `u_2 = 2` of
  `09:438--440`), `smallCopyWidth_dyadic`, `smallCopyWidth_two`, and `rhoSmall`
  with `rhoSmall_eq_two_y_sq` (the frozen `rho = 2y^2 = 18/25` of `09:436`).
* `EthInapproximability.ParameterizedNP.WrapperLowRungs`:
  `simple_gate_forces_tRef_row_legality` (`09:327` plus `A:118`), which supplies
  `t_ref x_T <= 1`, the outer guard of the frozen legality chain
  `kappa_v x_T <= t_ref x_T <= 1` at `09:1303--1304`; and `kappaLow`, the
  wrapper capacity in exponent form.
* `EthInapproximability.ParameterizedNP.TerminalTwoStream`:
  `certifiedRowLadder_of_base` and the predicate `CertifiedRowLadder`
  (`lem:certified-row-ladder`, `A:148--162`), **proved** in that module from the
  three checked inherited contracts.  The two ladder invocations of
  `09:1297--1301` (`ell = ell_v`) and `09:1334--1338` (`ell = 1`) are that pin at
  two exponents; the lemma is not restated and not re-proved.
* `EthInapproximability.ParameterizedNP.ScaleAlignOpening`: `xTdepth`
  (`x_T = 2^{-b_T}`, `08:166`) for the legality probe only.
* `NPCC.LambdaGE`, `Workspace.Types.CommComplexity.D` -- the vendored,
  project-axiom-free complexity interface reached through `LegacyNPCC.Core`.

## GAP-EXPOSED (what this module deliberately does not claim)

1. **`eq:wrapper-u-dense` is not closed.**  The frame at `09:1187--1193` opens a
   contradiction that the frozen text completes only in `09:1367--1511`
   (`sec:wrapper-protected-early`) and `09:1512--1781`.  Those two ranges stay
   GAP-EXPOSED exactly as `SCALE-ALIGN-OPENING-001` and
   `TERMINAL-TWO-STREAM-001` record them, `hDenseRung` is **fed and not
   discharged**, and **no route completion is claimed**.  No declaration below
   has `comp <U, 1, 1-delta_U, theta> >= C + r` as a conclusion.
2. **The protocol side is not modelled.**  The certificate routing itself (which
   rows land in which child), the choice of the denser Bob child, the selection
   of `u_{kappa_v}` represented coordinates, the trimming of a certificate to row
   density `kappa_v x_T`, and the passage from a frontier node to an actual
   protocol subtree are **not** declared.  What is landed is every *arithmetic
   and counting* phase those steps consume or produce, at the frozen constants,
   plus the two budget contradictions, which are pure natural-number arithmetic
   on the frozen depths.
3. **`thm:certified-localized-extension` is not transcribed here.**  The
   large-capacity branch of `09:1269--1276` invokes it at `r' = kappa_v/t_ref`,
   `a^sharp = 1`; its Lean interface is the named binder `hLocEx` of the banked
   `WrapperLowRungs.wrapperLowExtension` (at `a^sharp = 0`), and re-siting that
   binder at `a^sharp = 1` is a separate obligation.  What is landed for that
   branch is only the arithmetic it produces -- the residual bound
   `C + log_2 kappa_v - 1` measured against the remaining child budget -- carried
   as the named hypothesis `hclosure`.  The corollary's conclusion
   `eq:certified-E3` is asserted nowhere.
4. **`eq:wrapper-frontier-conservation`'s first clause is a hypothesis.**
   `sum_v W_v >= q - e_0` (`09:1262`) follows from the routing dynamics of
   `09:1238--1248` together with the initial placement "one clean reference
   certificate in every coordinate outside `E_0`"; the routing dynamics are not
   modelled (item 2), so the clause enters `wrapperCleanCount` as the explicit
   binder `hcons`.  What *is* proved outright is the weight algebra it rests on
   (`weight_le_totalRouteWeight`, `sum_weight_le_sum_routeWeight`) and the second
   clause (Kraft, by pin).
5. **`e_0 <= e_0^max` is not asserted.**  `09:452--453` records that "the
   construction records an explicit deterministic upper bound"; the value is the
   schedule's, and the banked `WrapperProjectionCovers.e0Max` / `e0_le_e0Max`
   own it.  `e_0` is a free nonnegative real in every statement below.
6. **The three survival gates are transcribed, not derived.**
   `eq:wrapper-initial-survival` is stated as a predicate and asserted nowhere;
   `06`'s `eq:parameter-wrapper-survival-gates` is where the schedule discharges
   it, and that discharge is not claimed here.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, opened first-hand
for this tranche.  **No reader item is claimed by any declaration in this
module**, and that is a finding about the reader artifact rather than an omission
here.

The reader's near-full rung outline is lines `370--399`, and every sentence of it
sits *inside the proof* of `thm:paper-adapted-stage4-interface`, so it is prose,
not a numbered or displayed statement; the reader-counterpart discipline bars
citing prose as a statement.  Concretely:

* line `371--373`, "Before its terminal frontier, the all-column reference
  follows every Bob query and its one-bit-down certificate prevents an early
  cheap termination" -- the nearest reader sentence to this block, and prose;
* lines `390--391`, "Its small-capacity and final-node closures use the certified
  row ladder `lem:paper-certified-row-ladder`" -- **already assigned** to
  `TerminalTwoStream` (its header records reader line `391` as claimed there),
  and no reader item may carry two assignments, so it is not reclaimed;
* the display at line `394`, `D_U(1; 1-delta_U, theta) >= C + r_q`, is precisely
  `eq:wrapper-u-dense`, which this block **does not close** (GAP-EXPOSED 1);
  claiming it here would be false.  Its transposed form at reader line `342`
  (`eq:paper-adapted-stage4-interface`, second clause) is in any case already
  assigned to `ScaleAlignOpening.commonThreshold_of_wrapper`.

Searched first-hand across the whole reader artifact: `A_0`, `A_k`, `eta_R`,
`vartheta`, `9/16` as a frontier threshold, `K_B`, `e_0` and the phrase "no Bob"
occur **nowhere**.  The reader's own sentence at `396--399` -- the owner--donor
count "is expanded line by line in the ultra-explicit companion" -- names exactly
the frozen `09:1184--1781` of which this module traces the first subsubsection.
Every declaration below therefore carries its autoformalization anchor alone.
The neighbouring reader rung display at lines `361--368` is already assigned to
`WrapperLowRungs.wrapperLowRungs` and is not reclaimed.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the completion map `completeRoute`, general (5): `completeRoute_length`,
  `completeRoute_of_not_bobFree`, `completeRoute_prefix`, `completeRoute_idem`,
  `completeRoute_length_le_max`; plus `completeRoute_r_le_length`, the frozen
  `09:1198--1200` conclusion `r <= length` on **every** no-Bob path, which is what
  makes the lemma's second clause available without any depth restriction.
* `B` the row-count geometry `refRowFloor`, general (5): `refRowFloor_zero`,
  `refRowFloor_succ`, `refRowFloor_mono`, `refRowFloor_add`,
  `refRowFloor_ceil_half`.
* `C` the certificate kinds `CertKind`, general (5): `weight_pos`,
  `weight_le_one`, `weight_ne_of_ne`, `weight_le_totalRouteWeight`,
  `totalRouteWeight_append`.
* `D` the frontier record `WrapperFrontier`, general (5): `one_le_capacity`,
  `capacity_le_width`, `two_le_capacity_firstBob`, `capacity_final_eq_one`,
  `route_injective`.
* `E` the counting readouts, general (5): `sum_capacity_le_width`,
  `sum_bobNodes_add_sum_finalNodes`, `card_cleanNodes_add_card_splitNodes_le`,
  `sum_finalWeight_eq`, `kraftSplit`.

## Non-vacuity and statement poles

* `wrapperInitialSurvival_tier2_instance` exhibits the three survival gates
  jointly satisfied at the **frozen identities and over the whole legal range of
  the schedule's free masses**: the width is the frozen `q = 2^r` (`09:105`),
  `delta_U` is `eq:q-deltaU`'s `eta_R/(16 q)` (`06:514--518`) as an identity and
  not a numeral, and `A_0` is `initialRefRows x_T m_G`, i.e. the frozen
  `A_0 = ceil(2 x_T m_G)` of `09:1219` evaluated at the witness's own `x_T` and
  `m_G`.  `eta_R` and `g` stay free binders -- `06:228` fixes no numeral for
  `eta_R` -- and only the ratio `x_T m_G = 1` (giving `A_0 = 2`) and the two
  derived widths `survivalWidth`, `survivalRefWidth` are fixed.  Nondegenerate:
  `r >= 1` forces `q >= 2 > 1`, so the third gate's `q(q-1)` factor is positive.
  `wrapperInitialSurvival_not_automatic` refutes the reading that the gates hold
  for free.  No claim is made about `ScaleAlignOpening.scheduleDeltaU_guards`,
  whose `delta_U <= 1/200` is that lemma's own hypothesis and not a schedule
  theorem.
* `wrapperFrontierProbe` inhabits `WrapperFrontier` at `r = 2` with a first-Bob
  node **and** two final nodes, so no field is satisfied vacuously; Kraft is
  attained there (`sum_v kappa_v = 4 = q`).
* `wrapperCleanCount_legal_instance` discharges the *entire* hypothesis bundle of
  the headline at that probe, with `e_0 = 1`, and produces both conclusions with
  the clean count `c = 2` strictly above the bound `4 - 16/7`.  So the bundle is
  jointly satisfiable, not merely unrefuted, and `False` does not follow from it.
* `cleanCount_needs_kraft` is the statement pole for the headline: at
  `q = 16, e_0 = 0, K_B = 32, c = 0, l = 0` the conservation inequality holds and
  the conclusion **fails**, so Kraft is load-bearing and the theorem is not a
  triviality about its conclusion's shape.
* `noBobCompletion_needs_C_pos` is the pole for the completion cost bound: at
  `C = 0`, `r = 1`, `cost = 0` the frozen conclusion is false, which is exactly
  why `09:1212` writes "because `C >= 1`".
* `firstBobLight_needs_the_extra_bit` shows the budget contradiction is by one
  bit and no more: at a residual bound of `C + ell - 2` the same hypotheses are
  consistent.
* `wrapperNoBobCompletion_legal_instance` / `wrapperNoBobCompletion_fires_at_probe`
  discharge the completion lemma's bundle on a leaf family containing **both** a
  Bob-free path and a Bob-carrying path, so neither of its two clauses is
  exercised only vacuously; and `wrapperNoBobCompletion_fires_on_long_path` fires
  it on a Bob-free path of depth `3 > r = 2`, where the depth restriction the
  frozen statement does not carry would have been **unsatisfiable**.  That is the
  pole showing the restored quantifier is load-bearing rather than cosmetic.
* `finalReferenceUniqueness_legal_instance` /
  `finalReferenceUniqueness_fires_at_probe` discharge
  `lem:final-reference-uniqueness`'s bundle at a **nonempty** certificate set.
  The same bundle at two certificates on distinct coordinates is inconsistent --
  which is the frozen contradiction itself (`finalNode_budget_contradiction`),
  not a defect of the statement.
* `wrapperFrontier_needs_prefixFree` is the pole for the frontier record: without
  prefix-freeness three nodes at depth `1` below `r = 2` would carry total
  capacity `6 > 4 = q` and `kraftSplit` would be false.

## Machine evidence (this generation)

`scratch/CCT2ZProbes.lean` (disposable, five `example`s each expected to fail):
`False` from the full hypothesis bundle of `wrapperCleanCount` (at `q = 2^r`,
`e_0 >= 0`, with Kraft and the capacity nonnegativity already in context), of
`wrapperFirstBobLight` (at `d + ell = r`, `ell >= 1`, `C >= 3` and the alleged
budget), of the **repaired** `wrapperNoBobCompletion` (now without any depth
restriction on the leaves), of `wrapperFinalReferenceUniqueness` at a nonempty
certificate set, and of `wrapperInitialSurvival_tier2_instance`'s bundle at
`r >= 1`, `0 < eta_R <= 1`, `0 < g` -- **all five fail**, with every consequence
of the bundle already derived.  Axiom audit: all 110 named declarations of this
module report `propext`, `Classical.choice`, `Quot.sound` and nothing else, and
each is registered individually in `tools/AxiomAudit.lean`.
-/

namespace EthInapproximability.ParameterizedNP.DenseWrapperFrontier

open Finset
open NPCC
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseFrontierConservation
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.TerminalTwoStream

/-! ## §1  `lem:wrapper-no-bob-completion` (`09:1195--1213`)

"The protocol may be chosen, without increasing its cost beyond `C+r-1` or
changing any first-Bob node, so that every root-to-leaf path containing no Bob
query contains at least `r` Alice queries."

A root-to-leaf path is its transcript, a `List Bool`; `bobFree p` records the
frozen side condition "containing no Bob query", carried as a parameter rather
than reconstructed, since which nodes are Bob nodes is protocol data this block
does not model.  On a Bob-free path every transmitted bit is an Alice message, so
the number of Alice queries on such a path **is** its length, and `false` is the
frozen "fixed Alice message" appended by the completion. -/

/-- **`09:1203--1205`.**  "At every leaf reached after `d < r` Alice queries and
no Bob query, append `r-d` fixed Alice messages and retain the original output
label at the new leaf."

The `ℕ`-subtraction `r - p.length` is exact under the frozen guard `d < r`
(`completeRoute_appended`), and is `0` -- so the map is the identity -- on the
longer Bob-free paths, which the frozen text leaves alone. -/
def completeRoute (r : ℕ) (bobFree : List Bool → Bool) (p : List Bool) : List Bool :=
  if bobFree p then p ++ List.replicate (r - p.length) false else p

/-- **Aux A1 (`09:1212`, "No path containing a Bob query is modified").**
General in `r`, in the Bob-free predicate and in the path. -/
@[simp] theorem completeRoute_of_not_bobFree {r : ℕ} {bobFree : List Bool → Bool}
    {p : List Bool} (h : bobFree p = false) : completeRoute r bobFree p = p := by
  simp [completeRoute, h]

/-- **Aux A2 (the completed depth is `max{d, r}`).**  This is what makes the
frozen cost bound `max{cost(P), r}` of `09:1210` the right one.  General. -/
theorem completeRoute_length {r : ℕ} {bobFree : List Bool → Bool} {p : List Bool}
    (h : bobFree p = true) : (completeRoute r bobFree p).length = max p.length r := by
  simp only [completeRoute, h, if_true, List.length_append, List.length_replicate]
  omega

/-- **Aux A3 (the completion only extends).**  The original path is a prefix of
its completion, which is the precise sense in which "no first-Bob node" moves:
every node of the original protocol survives at its original position.  General. -/
theorem completeRoute_prefix {r : ℕ} {bobFree : List Bool → Bool} {p : List Bool} :
    p <+: completeRoute r bobFree p := by
  unfold completeRoute
  by_cases h : bobFree p = true
  · simp only [h, if_true]
    exact List.prefix_append _ _
  · simp only [Bool.not_eq_true] at h
    simp [h]

/-- **Aux A3b (the completion in closed form).**  General. -/
theorem completeRoute_eq_of_bobFree {r : ℕ} {bobFree : List Bool → Bool} {p : List Bool}
    (h : bobFree p = true) :
    completeRoute r bobFree p = p ++ List.replicate (r - p.length) false := by
  simp [completeRoute, h]

/-- **Aux A4 (the completion is idempotent).**  Completing a completed path
changes nothing, because the completed depth already meets `r`.  The Bob-free
predicate is evaluated at the completed path, so the hypothesis is that the
completion does not create a Bob query -- which it does not, since it appends
Alice messages only.  General. -/
theorem completeRoute_idem {r : ℕ} {bobFree : List Bool → Bool} {p : List Bool}
    (hstable : bobFree (completeRoute r bobFree p) = bobFree p) :
    completeRoute r bobFree (completeRoute r bobFree p) = completeRoute r bobFree p := by
  by_cases h : bobFree p = true
  · have hlen := completeRoute_length (r := r) (bobFree := bobFree) (p := p) h
    have h' : bobFree (completeRoute r bobFree p) = true := by rw [hstable]; exact h
    have hz : r - (completeRoute r bobFree p).length = 0 := by omega
    rw [completeRoute_eq_of_bobFree h', hz, List.replicate_zero, List.append_nil]
  · simp only [Bool.not_eq_true] at h
    simp [completeRoute_of_not_bobFree h]

/-- **Aux A5 (the completed depth never exceeds `max{d, r}`).**  General, with no
side condition on the Bob-free predicate; this is the form the cost bound
consumes. -/
theorem completeRoute_length_le_max {r : ℕ} {bobFree : List Bool → Bool}
    {p : List Bool} : (completeRoute r bobFree p).length ≤ max p.length r := by
  by_cases h : bobFree p = true
  · rw [completeRoute_length h]
  · simp only [Bool.not_eq_true] at h
    rw [completeRoute_of_not_bobFree h]
    exact le_max_left _ _

/-- **`09:1203--1204`, the appended count.**  "append `r-d` fixed Alice
messages": under the frozen guard `d < r` the natural subtraction is exact and
the new depth is `d + (r-d) = r`.  General. -/
theorem completeRoute_appended {r d : ℕ} (h : d < r) : d + (r - d) = r := by omega

/-- **`09:1206`, "their new depth is exactly `r`".**  On a Bob-free path of depth
at most `r`, the completion has depth exactly `r`; since every bit of a Bob-free
path is an Alice message, that is the frozen conclusion "contains at least `r`
Alice queries", with equality on the short paths.  General. -/
theorem completeRoute_length_eq {r : ℕ} {bobFree : List Bool → Bool} {p : List Bool}
    (h : bobFree p = true) (hd : p.length ≤ r) :
    (completeRoute r bobFree p).length = r := by
  rw [completeRoute_length h]; omega

/-- **Aux A6 (`09:1198--1200`, the frozen conclusion, unconditionally).**

"every root-to-leaf path containing no Bob query contains at least `r` Alice
queries."  Since every transmitted bit of a Bob-free path is an Alice message,
the number of Alice queries on such a path is its length, and
`completeRoute_length` gives that length as `max{d, r} >= r` with **no** depth
restriction: the frozen lemma quantifies over every no-Bob path of the cost-`C+r-1`
protocol, and such paths may already exceed depth `r`.  General. -/
theorem completeRoute_r_le_length {r : ℕ} {bobFree : List Bool → Bool} {p : List Bool}
    (h : bobFree p = true) : r ≤ (completeRoute r bobFree p).length := by
  rw [completeRoute_length h]
  exact le_max_right _ _

/-- **`09:1208--1212`, the cost bound.**  "Hence the completed protocol has cost
at most `max{cost(P), r} <= C+r-1`, because `C >= 1`."

The `ℕ`-subtraction `C + r - 1` is exact under `1 <= C`.  General in `C`, `r` and
the original cost. -/
theorem noBobCompletion_cost_le {C r cost : ℕ} (hC : 1 ≤ C)
    (hcost : cost ≤ C + r - 1) : max cost r ≤ C + r - 1 := by
  omega

/-- **Statement pole for `noBobCompletion_cost_le`: `C >= 1` is load-bearing.**

`09:1212` says the cost bound holds "because `C >= 1`".  At `C = 0` the frozen
conclusion is false, so the clause is not decoration: the trivial witness
`cost = 0`, `r = 1` satisfies the cost hypothesis and refutes the conclusion. -/
theorem noBobCompletion_needs_C_pos :
    (0 : ℕ) ≤ 0 + 1 - 1 ∧ ¬ (max (0 : ℕ) 1 ≤ 0 + 1 - 1) := by
  refine ⟨by norm_num, by norm_num⟩

/-- **`lem:wrapper-no-bob-completion` (`09:1195--1200`), all three clauses.**

For a finite family of root-to-leaf paths of a protocol of cost at most `C+r-1`,
the completion of `09:1203--1207`

1. leaves every path containing a Bob query untouched (`09:1212`);
2. gives **every** Bob-free path at least `r` Alice queries (`09:1198--1200`);
   and
3. has cost at most `max{cost(P), r} <= C+r-1` (`09:1208--1212`).

The frozen lemma quantifies over every root-to-leaf path containing no Bob query,
with **no** depth restriction: a Bob-free path of the cost-`C+r-1` protocol may
already exceed depth `r`, and the completion fixes it.  Accordingly the second
clause is the frozen `r <= length`, available unconditionally from
`completeRoute_length` (`length = max{d, r}`); the sharper "their new depth is
exactly `r`" of `09:1206` is a statement about the *formerly short* paths only
and is carried separately by `wrapperNoBobCompletion_exact_on_short` under its own
guard.

`hlen` is the frozen "protocol `P` of cost at most `C+r-1`" of `09:1192--1193`
read off at the leaves.  General in the leaf family, the Bob-free predicate, `C`
and `r`. -/
theorem wrapperNoBobCompletion {C r cost : ℕ} {bobFree : List Bool → Bool}
    (leaves : Finset (List Bool)) (hC : 1 ≤ C) (hcost : cost ≤ C + r - 1)
    (hlen : ∀ p ∈ leaves, p.length ≤ cost) :
    (∀ p ∈ leaves, bobFree p = false → completeRoute r bobFree p = p)
      ∧ (∀ p ∈ leaves, bobFree p = true → r ≤ (completeRoute r bobFree p).length)
      ∧ (∀ p ∈ leaves, (completeRoute r bobFree p).length ≤ C + r - 1) := by
  refine ⟨fun p _ h => completeRoute_of_not_bobFree h,
    fun _ _ h => completeRoute_r_le_length h, fun p hp => ?_⟩
  refine le_trans completeRoute_length_le_max ?_
  exact le_trans (max_le_max (hlen p hp) (le_refl r)) (noBobCompletion_cost_le hC hcost)

/-- **`09:1206`, the optional sharpening, under its own guard.**

"Only the formerly short paths are enlarged, and their new depth is exactly `r`."
On the leaves reached after `d <= r` Alice queries -- the ones the completion
actually enlarges -- the completed depth is exactly `r`.  This is a *strictly
weaker-quantified* companion to `wrapperNoBobCompletion`'s second clause, never a
replacement for it: `hshort` is the guard `09:1203` places on the completion's
domain, and it must not migrate into the lemma statement, whose conclusion
`09:1198--1200` ranges over every no-Bob path.  General. -/
theorem wrapperNoBobCompletion_exact_on_short {r : ℕ} {bobFree : List Bool → Bool}
    (leaves : Finset (List Bool)) (hshort : ∀ p ∈ leaves, p.length ≤ r) :
    ∀ p ∈ leaves, bobFree p = true → (completeRoute r bobFree p).length = r :=
  fun p hp h => completeRoute_length_eq h (hshort p hp)

/-! ## §2  The reference-row geometry (`09:1217--1222`, `09:1238--1243`)

"For `k = 0, ..., r`, put `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0`." -/

/-- **`09:1219`.**  `A_0 = ceil(2 x_T m_G)`, the initial reference-row demand.
The ceiling is kept, never rounded away. -/
noncomputable def initialRefRows (xT : ℝ) (mG : ℕ) : ℕ := ⌈2 * xT * (mG : ℝ)⌉₊

/-- **`09:1221`.**  `A_k = 2^k A_0`. -/
def refRowFloor (A0 k : ℕ) : ℕ := 2 ^ k * A0

/-- **Aux B1.**  `A_0` is the base of the geometry.  General. -/
@[simp] theorem refRowFloor_zero (A0 : ℕ) : refRowFloor A0 0 = A0 := by
  simp [refRowFloor]

/-- **Aux B2.**  `A_{k+1} = 2 A_k`.  General. -/
theorem refRowFloor_succ (A0 k : ℕ) : refRowFloor A0 (k + 1) = 2 * refRowFloor A0 k := by
  simp [refRowFloor, pow_succ]; ring

/-- **Aux B3.**  `A_k` is monotone in the remaining selector capacity exponent.
General. -/
theorem refRowFloor_mono (A0 : ℕ) {j k : ℕ} (h : j ≤ k) :
    refRowFloor A0 j ≤ refRowFloor A0 k :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)

/-- **Aux B4.**  `A_{j+k} = 2^j A_k`.  General. -/
theorem refRowFloor_add (A0 j k : ℕ) :
    refRowFloor A0 (j + k) = 2 ^ j * refRowFloor A0 k := by
  simp [refRowFloor, pow_add]; ring

/-- **Aux B5 (`09:1242`: `ceil(A_k/2) >= A_{k-1}`), with equality.**

The frozen inequality is in fact an identity, because `A_k = 2 A_{k-1}` is even:
in `ℕ`, `ceil(n/2) = (n+1)/2`, and `(2A+1)/2 = A`.  Recording the equality is
what shows the routing rule loses nothing.  General in `A_0` and in `k >= 1`. -/
theorem refRowFloor_ceil_half {A0 k : ℕ} (hk : 1 ≤ k) :
    (refRowFloor A0 k + 1) / 2 = refRowFloor A0 (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [refRowFloor_succ]
  simp only [Nat.add_sub_cancel]
  omega

/-- **`09:1240--1243`, the routing rule's row bookkeeping.**

"At remaining selector capacity `2^k`, a certificate consists of at least `A_k`
reference rows in one outer coordinate.  At an Alice query, route it to a child
containing at least `ceil(A_k/2) >= A_{k-1}` of those rows."

So the invariant "at least `A_k` rows at capacity `2^k`" is restored one level
down.  General. -/
theorem routedChild_rows_ge {A0 k rows child : ℕ} (hk : 1 ≤ k)
    (hrows : refRowFloor A0 k ≤ rows) (hchild : (rows + 1) / 2 ≤ child) :
    refRowFloor A0 (k - 1) ≤ child := by
  rw [← refRowFloor_ceil_half (A0 := A0) hk]
  exact le_trans (Nat.div_le_div_right (by omega)) hchild

/-- **Aux B6 (`09:1219`, the ceiling is a genuine lower bound).**
`2 x_T m_G <= A_0`.  General in `x_T` and `m_G`. -/
theorem initialRefRows_ge (xT : ℝ) (mG : ℕ) :
    2 * xT * (mG : ℝ) ≤ (initialRefRows xT mG : ℝ) :=
  Nat.le_ceil _

/-- **`09:1293--1295`, the row demand at a small-capacity node.**

"Each selected certificate has at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
m_G` reference rows, so trim it to the row density `kappa_v x_T`."

Both halves: the identity `A_ell = 2^ell A_0` at `kappa = 2^ell`, and the
comparison against the frozen row demand `2 kappa x_T m_G`.  General in `ell`,
`x_T` and `m_G`. -/
theorem refRowFloor_meets_row_demand (ℓ mG : ℕ) (xT : ℝ) :
    2 * ((2 : ℝ) ^ ℓ) * xT * (mG : ℝ)
      ≤ ((refRowFloor (initialRefRows xT mG) ℓ : ℕ) : ℝ) := by
  have hbase := initialRefRows_ge xT mG
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have hcast : ((refRowFloor (initialRefRows xT mG) ℓ : ℕ) : ℝ)
      = (2 : ℝ) ^ ℓ * ((initialRefRows xT mG : ℕ) : ℝ) := by
    simp [refRowFloor]
  rw [hcast]
  nlinarith [hbase, hpow]

/-- **`09:1233--1235`, the retained reference rows at the width.**

"Even if every deleted row of `U` were concentrated in one nonexceptional outer
coordinate, that coordinate would therefore retain at least `A_r = q A_0`
reference rows."  At the wrapper width `q = 2^r` the frozen identity `A_r = q A_0`
is `refRowFloor A_0 r = 2^r A_0`, which is definitional; what is proved here is
the retention itself, from the second survival gate.  General. -/
theorem retainedRefRows_ge {q m mG : ℕ} {A0 : ℕ} {deltaU deleted : ℝ}
    (hgate : (q : ℝ) * A0 + deltaU * q * m ≤ mG)
    (hdel : deleted ≤ deltaU * q * m) :
    (q : ℝ) * A0 ≤ (mG : ℝ) - deleted := by
  linarith

/-! ## §3  `eq:wrapper-initial-survival` (`09:1224--1232`)

"The three row-survival gates are `q A_0/m <= eta_R/16`,
`q A_0 + delta_U q m <= m_G`, `q(q-1)A_0/m_G <= eta_R/(16 g)`."

Transcribed as a predicate and asserted nowhere; the schedule discharges it in
`06` (GAP-EXPOSED 6). -/

/-- **`eq:wrapper-initial-survival` (`09:1224--1232`), verbatim, all three
clauses.**  The comparisons are in `ℝ`, so the frozen rationals are exact and no
natural division truncates.  `q - 1` is the real difference, legal because the
wrapper width is at least one. -/
def wrapperInitialSurvival (q m mG A0 : ℕ) (etaR deltaU g : ℝ) : Prop :=
  (q : ℝ) * A0 / m ≤ etaR / 16
    ∧ (q : ℝ) * A0 + deltaU * q * m ≤ mG
    ∧ (q : ℝ) * ((q : ℝ) - 1) * A0 / mG ≤ etaR / (16 * g)

/-- The row width the gates force at wrapper exponent `r` and reference mass
`eta_R`: the least natural clearing the first gate `q A_0/m <= eta_R/16` at
`A_0 = 2`.  A *derived* quantity of the witness below, not a pinned numeral. -/
noncomputable def survivalWidth (r : ℕ) (etaR : ℝ) : ℕ := ⌈32 * (2 : ℝ) ^ r / etaR⌉₊

/-- The reference row count the gates force at wrapper exponent `r`, reference
mass `eta_R` and row mass `g`: large enough for the second gate against
`survivalWidth` and for the third gate's `q(q-1)` term at once.  Derived, not
pinned. -/
noncomputable def survivalRefWidth (r : ℕ) (etaR g : ℝ) : ℕ :=
  2 ^ (r + 2) + 1 + ⌈32 * g * (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) / etaR⌉₊

theorem survivalRefWidth_pos (r : ℕ) (etaR g : ℝ) : 0 < survivalRefWidth r etaR g := by
  have : 0 < 2 ^ (r + 2) := Nat.two_pow_pos _
  unfold survivalRefWidth
  omega

/-- **Non-vacuity (tier 2): the three survival gates hold jointly, at the frozen
identities and over the whole legal range of the schedule's free masses.**

Nothing is pinned that the frozen text does not pin.  The wrapper width is the
frozen `q = 2^r` (`09:105`); `delta_U` is the frozen `eq:q-deltaU` (`06:514--518`)
`delta_U = eta_R/(16 q)` **as an identity**, not a numeral; `A_0` is the frozen
`A_0 = ceil(2 x_T m_G)` (`09:1219`), evaluated through `initialRefRows` at the
witness's own `x_T` and `m_G` and coming out as the honest `A_0 = 2`.  The
reference mass `eta_R` and the row mass `g` stay **free** in their frozen ranges
(`06:228` fixes only `0 < eta_R`, and `g` is a density), exactly as
`WrapperLowRungs.wrapperLowRungGates_legal_instance` leaves `k`, `r` and `x_T`
free: no numeral is an admissible value of either for every instance, so pinning
one would assert a schedule point no instance need realise.

What the witness fixes is the single ratio the gates constrain -- `x_T m_G = 1`,
i.e. `A_0 = 2` -- and the two derived widths `m = survivalWidth r eta_R` and
`m_G = survivalRefWidth r eta_R g` that the three gates then force.

Nondegeneracy: `r >= 1` gives `q = 2^r >= 2 > 1`, so the third gate's factor
`q(q-1) > 0` and the clause is a real constraint rather than a vacuous `0 <= .`;
`A_0 = 2 > 0`; `m > 0` and `m_G > 0`; and `delta_U > 0`. -/
theorem wrapperInitialSurvival_tier2_instance (r : ℕ) (hr : 1 ≤ r) {etaR g : ℝ}
    (hetaR : 0 < etaR) (hetaR1 : etaR ≤ 1) (hg : 0 < g) :
    wrapperInitialSurvival (2 ^ r) (survivalWidth r etaR) (survivalRefWidth r etaR g)
        (initialRefRows (1 / (survivalRefWidth r etaR g : ℝ)) (survivalRefWidth r etaR g))
        etaR (etaR / (16 * (2 : ℝ) ^ r)) g
      ∧ initialRefRows (1 / (survivalRefWidth r etaR g : ℝ)) (survivalRefWidth r etaR g) = 2
      ∧ (1 : ℕ) < 2 ^ r
      ∧ 0 < survivalWidth r etaR
      ∧ 0 < etaR / (16 * (2 : ℝ) ^ r) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hmG0 : 0 < survivalRefWidth r etaR g := survivalRefWidth_pos r etaR g
  have hmGR : (0 : ℝ) < (survivalRefWidth r etaR g : ℝ) := by exact_mod_cast hmG0
  -- `A_0 = ceil(2 x_T m_G) = 2` at `x_T = 1/m_G`.
  have hA0 : initialRefRows (1 / (survivalRefWidth r etaR g : ℝ))
      (survivalRefWidth r etaR g) = 2 := by
    unfold initialRefRows
    have : 2 * (1 / (survivalRefWidth r etaR g : ℝ)) * (survivalRefWidth r etaR g : ℝ)
        = (2 : ℝ) := by field_simp
    rw [this]
    simp
  -- The first gate's width bound.
  have hm : 32 * (2 : ℝ) ^ r / etaR ≤ (survivalWidth r etaR : ℝ) := Nat.le_ceil _
  have hmlt : (survivalWidth r etaR : ℝ) < 32 * (2 : ℝ) ^ r / etaR + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hm0 : 0 < survivalWidth r etaR := by
    have : (0 : ℝ) < 32 * (2 : ℝ) ^ r / etaR := by positivity
    have := lt_of_lt_of_le this hm
    exact_mod_cast this
  have hmR : (0 : ℝ) < (survivalWidth r etaR : ℝ) := by exact_mod_cast hm0
  have hm' : 32 * (2 : ℝ) ^ r ≤ etaR * (survivalWidth r etaR : ℝ) := by
    rw [div_le_iff₀ hetaR] at hm; linarith
  have hm'' : etaR * (survivalWidth r etaR : ℝ) < 32 * (2 : ℝ) ^ r + etaR := by
    have hstep : etaR * (survivalWidth r etaR : ℝ)
        < etaR * (32 * (2 : ℝ) ^ r / etaR + 1) := by
      exact mul_lt_mul_of_pos_left hmlt hetaR
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hetaR)] at hstep
    linarith
  -- The third gate's reference-row bound.
  have h3 : 32 * g * (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) / etaR
      ≤ (⌈32 * g * (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) / etaR⌉₊ : ℝ) := Nat.le_ceil _
  have hcastG : (survivalRefWidth r etaR g : ℝ)
      = (2 : ℝ) ^ (r + 2) + 1 + (⌈32 * g * (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) / etaR⌉₊ : ℝ) := by
    unfold survivalRefWidth; push_cast; ring
  have hpow2 : (2 : ℝ) ^ (r + 2) = 4 * (2 : ℝ) ^ r := by rw [pow_add]; ring
  refine ⟨⟨?_, ?_, ?_⟩, hA0, ?_, hm0, by positivity⟩
  · -- `q A_0 / m <= eta_R/16`
    rw [hA0]
    rw [div_le_div_iff₀ hmR (by norm_num)]
    push_cast
    nlinarith [hm']
  · -- `q A_0 + delta_U q m <= m_G`
    rw [hA0]
    have hdu : etaR / (16 * (2 : ℝ) ^ r) * (2 : ℝ) ^ r * (survivalWidth r etaR : ℝ)
        = etaR * (survivalWidth r etaR : ℝ) / 16 := by
      field_simp
    push_cast
    rw [hdu, hcastG, hpow2]
    have hceil0 : (0 : ℝ) ≤ (⌈32 * g * (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) / etaR⌉₊ : ℝ) := by
      positivity
    nlinarith [hm'', hetaR1]
  · -- `q(q-1) A_0 / m_G <= eta_R/(16 g)`
    rw [hA0]
    rw [div_le_div_iff₀ hmGR (by positivity)]
    push_cast
    rw [hcastG, hpow2] at *
    rw [div_le_iff₀ hetaR] at h3
    nlinarith [h3, hpow1, hpow, hg.le, sq_nonneg ((2 : ℝ) ^ r - 1)]
  · exact Nat.one_lt_two_pow_iff.mpr (by omega)

/-- **Statement pole: the survival gates are not automatic.**

At `q = 4` (so `r = 2`), `m = 4096`, `m_G = 65536`, `eta_R = 1/2` and the frozen
`delta_U = eta_R/(16 q) = 1/128` of `eq:q-deltaU`, raising the reference-row
demand to `A_0 = 4096` breaks the first gate, so `wrapperInitialSurvival` is a
real constraint on the schedule and not a predicate every tier satisfies.
Without this, `wrapperInitialSurvival_tier2_instance` would establish nothing. -/
theorem wrapperInitialSurvival_not_automatic :
    ¬ wrapperInitialSurvival 4 4096 65536 4096 (1 / 2) (1 / 128) (91 / 92) := by
  rintro ⟨h1, -, -⟩
  norm_num at h1

/-! ## §4  Certificate weights (`09:1236`, `09:1244--1248`)

"Start one clean reference certificate in every coordinate outside `E_0`, each
with weight one. ...  A clean certificate routed uniquely stays clean with weight
one.  When a clean certificate splits, both descendants become low certificates
of weight `1/2`.  A low certificate keeps weight `1/2`, whether it has one or two
qualifying children.  Thus total certificate weight never decreases." -/

/-- **`09:1236`, `09:1245--1247`.**  The two frozen certificate kinds.  A clean
certificate carries weight one; a low certificate -- a descendant of a split --
carries weight `1/2`.  No complexity or robustness conclusion is constructor
data. -/
inductive CertKind
  | clean
  | low
  deriving DecidableEq, Repr

namespace CertKind

/-- **`09:1236`, `09:1246`.**  The frozen weights: `1` for clean, `1/2` for low. -/
noncomputable def weight : CertKind → ℝ
  | .clean => 1
  | .low => 1 / 2

/-- **Aux C1.**  Every certificate carries strictly positive weight.  General. -/
theorem weight_pos (k : CertKind) : 0 < k.weight := by cases k <;> norm_num [weight]

/-- **Aux C2.**  No certificate carries more than the clean weight.  General. -/
theorem weight_le_one (k : CertKind) : k.weight ≤ 1 := by
  cases k <;> norm_num [weight]

/-- **Aux C3 (the two kinds are separated by their weight).**  The weight map is
injective, so "clean" and "low" are not interchangeable labels: the frozen
bookkeeping of `09:1347--1350` counts them separately for a reason.  General. -/
theorem weight_ne_of_ne {j k : CertKind} (h : j ≠ k) : j.weight ≠ k.weight := by
  cases j <;> cases k <;> simp_all [weight]

/-- **`09:1245--1248`, the routing outcome.**  The kinds of the descendants of one
certificate at one Alice query: a clean certificate routed uniquely stays clean;
a clean certificate that splits yields two low descendants; a low certificate
yields one low descendant, or two when both children qualify. -/
def routeOut : CertKind → Bool → List CertKind
  | .clean, false => [CertKind.clean]
  | .clean, true => [CertKind.low, CertKind.low]
  | .low, false => [CertKind.low]
  | .low, true => [CertKind.low, CertKind.low]

/-- The total weight carried by a list of certificates. -/
noncomputable def totalRouteWeight (l : List CertKind) : ℝ := (l.map weight).sum

/-- **Aux C4 (`09:1248`: "total certificate weight never decreases"), one
step.**  For every kind and every split decision, the weight of the descendants
is at least the weight of the parent -- with equality except when a low
certificate qualifies at both children, where it strictly increases.  General. -/
theorem weight_le_totalRouteWeight (k : CertKind) (b : Bool) :
    k.weight ≤ totalRouteWeight (routeOut k b) := by
  cases k <;> cases b <;> norm_num [weight, routeOut, totalRouteWeight]

/-- **Aux C5.**  `totalRouteWeight` is additive on concatenation, which is what
lets the one-step estimate be summed over a frontier.  General. -/
theorem totalRouteWeight_append (l₁ l₂ : List CertKind) :
    totalRouteWeight (l₁ ++ l₂) = totalRouteWeight l₁ + totalRouteWeight l₂ := by
  simp [totalRouteWeight]

/-- **Statement pole (`09:1246`): a split never restores a clean certificate.**

Both descendants of a split clean certificate are low, which is exactly why the
final-node classification of `09:1346--1347` has three cases and not two.  If
`routeOut` could return a clean descendant of a split, the half-weight column of
`eq:wrapper-clean-count` would be empty and the theorem would say nothing. -/
theorem routeOut_split_not_clean (k : CertKind) :
    CertKind.clean ∉ routeOut k true := by
  cases k <;> simp [routeOut]

end CertKind

/-- **`09:1248`, summed.**  "Thus total certificate weight never decreases": over
any finite family of certificates with any split decisions, the total descendant
weight is at least the total parent weight.  General in the index type. -/
theorem sum_weight_le_sum_routeWeight {ι : Type*} [Fintype ι]
    (k : ι → CertKind) (b : ι → Bool) :
    ∑ i, (k i).weight ≤ ∑ i, CertKind.totalRouteWeight (CertKind.routeOut (k i) (b i)) :=
  Finset.sum_le_sum fun i _ => CertKind.weight_le_totalRouteWeight (k i) (b i)

/-- **`09:1346--1347`.**  "Thus every final Alice node contains either one clean
certificate, one half-weight descendant of a split certificate, or none."  The
weight a final node carries, as a function of that trichotomy. -/
noncomputable def finalWeight : Option CertKind → ℝ
  | none => 0
  | some k => k.weight

@[simp] theorem finalWeight_none : finalWeight none = 0 := rfl

@[simp] theorem finalWeight_clean : finalWeight (some CertKind.clean) = 1 := rfl

@[simp] theorem finalWeight_low : finalWeight (some CertKind.low) = 1 / 2 := rfl

/-- **Aux (the final-node weight is a probability-like scalar).**  General. -/
theorem finalWeight_mem_Icc (o : Option CertKind) : 0 ≤ finalWeight o ∧ finalWeight o ≤ 1 := by
  cases o with
  | none => simp
  | some k => exact ⟨le_of_lt (CertKind.weight_pos k), CertKind.weight_le_one k⟩

/-! ## §5  The frontier (`09:1250--1266`)

"Stop each routed branch at its first Bob query, or after `r` Alice queries.  A
Bob query that occurs only after all `r` Alice queries is not exposed; its state
is a final Alice-frontier node.  If `v` is a frontier node, let `d_v` be the
number of preceding Alice queries and set `kappa_v = 2^{r-d_v}`, `W_v = total
certificate weight at `v`.  Every first-Bob node has `kappa_v >= 2`."

`kappa_v` is the banked `DenseWeightedCount.stoppingCapacity`, consumed by pin at
the wrapper exponent `r`; the frozen text repeats the definition, this module
does not. -/

/-- **`09:1250--1259`, the routed frontier.**

The two frozen stopping rules -- at the first Bob query, or after `r` Alice
queries -- and the two frozen structural facts they force: prefix-freeness
(`09:1259`) and the exposure rule, i.e. a first-Bob node has strictly fewer than
`r` preceding Alice queries while a final Alice node has exactly `r`.

Carrying no weight function and no certificate assignment is deliberate: `W_v`
and the per-node certificate are the *routing's* output, supplied at the use
sites as explicit binders, and folding either into the record would make this
record demand more than `09:1250--1258` states. -/
structure WrapperFrontier (r : ℕ) (V : Type*) where
  /-- The route from the root to the frontier node; its length is `d_v`. -/
  route : V → List Bool
  /-- `09:1259`, "Prefix-freeness". -/
  prefixFree : PrefixFreeFrontier route
  /-- Every branch stops at or before `r` Alice queries (`09:1250--1251`). -/
  depth_le : ∀ v, (route v).length ≤ r
  /-- Whether the node is a first-Bob node or a final Alice-frontier node. -/
  firstBob : V → Bool
  /-- `09:1251--1252`, the exposure rule: a Bob query after all `r` Alice queries
  "is not exposed", so an exposed first-Bob node has `d_v < r`. -/
  firstBob_depth_lt : ∀ v, firstBob v = true → (route v).length < r
  /-- `09:1250--1252`, a final Alice-frontier node is reached after exactly `r`
  Alice queries. -/
  final_depth_eq : ∀ v, firstBob v = false → (route v).length = r

namespace WrapperFrontier

variable {r : ℕ} {V : Type*}

/-- **`09:1255`.**  `kappa_v = 2^{r-d_v}`, the banked `stoppingCapacity` at the
wrapper exponent.  Consumed by pin, never restated. -/
def capacity (F : WrapperFrontier r V) (v : V) : ℕ :=
  stoppingCapacity r (F.route v).length

/-- **Aux D1.**  Every frontier node has positive capacity.  General. -/
theorem one_le_capacity (F : WrapperFrontier r V) (v : V) : 1 ≤ F.capacity v :=
  one_le_stoppingCapacity _ _

/-- **Aux D2.**  No node's capacity exceeds the wrapper width `q = 2^r`.
General. -/
theorem capacity_le_width (F : WrapperFrontier r V) (v : V) : F.capacity v ≤ 2 ^ r := by
  unfold capacity stoppingCapacity
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Aux D3 (`09:1259`: "Every first-Bob node has `kappa_v >= 2`").**  General. -/
theorem two_le_capacity_firstBob (F : WrapperFrontier r V) {v : V}
    (h : F.firstBob v = true) : 2 ≤ F.capacity v := by
  have hlt := F.firstBob_depth_lt v h
  have h1 : 1 ≤ r - (F.route v).length := by omega
  unfold capacity stoppingCapacity
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (r - (F.route v).length) := Nat.pow_le_pow_right (by norm_num) h1

/-- **Aux D4 (`09:1250--1252`: a final Alice node has capacity one).**  General. -/
theorem capacity_final_eq_one (F : WrapperFrontier r V) {v : V}
    (h : F.firstBob v = false) : F.capacity v = 1 := by
  unfold capacity stoppingCapacity
  rw [F.final_depth_eq v h]
  simp

/-- **Aux D5.**  Prefix-freeness makes the frontier's routes distinct, so nodes
are determined by their routes.  Consumed from the banked
`prefixFreeFrontier_injective`.  General. -/
theorem route_injective (F : WrapperFrontier r V) {v w : V} (h : F.route v = F.route w) :
    v = w :=
  prefixFreeFrontier_injective F.prefixFree h

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), by pin.**

"Prefix-freeness and conservation give ... `sum_v kappa_v <= q`", at the wrapper
width `q = 2^r`.  This *is* the banked
`DenseFrontierConservation.sum_stoppingCapacity_le_width`; the same Kraft device
at the same capacity weight, invoked here at the wrapper exponent, and re-proved
nowhere. -/
theorem sum_capacity_le_width [Fintype V] (F : WrapperFrontier r V) :
    ∑ v, F.capacity v ≤ 2 ^ r :=
  sum_stoppingCapacity_le_width F.route F.prefixFree F.depth_le

section Counting

variable [Fintype V]

/-- The first-Bob nodes of the frontier (`09:1259`). -/
def bobNodes (F : WrapperFrontier r V) : Finset V :=
  Finset.univ.filter fun v => F.firstBob v = true

/-- The final Alice-frontier nodes (`09:1252`). -/
def finalNodes (F : WrapperFrontier r V) : Finset V :=
  Finset.univ.filter fun v => F.firstBob v = false

/-- **`09:1347--1348`.**  `K_B`, "the sum of `kappa_v` over first-Bob nodes". -/
noncomputable def bobCapacity (F : WrapperFrontier r V) : ℝ :=
  ∑ v ∈ F.bobNodes, (F.capacity v : ℝ)

/-- **`09:1348--1349`.**  The final nodes carrying one clean certificate; `c` is
this set's cardinality. -/
def cleanNodes (F : WrapperFrontier r V) (cert : V → Option CertKind) : Finset V :=
  F.finalNodes.filter fun v => cert v = some CertKind.clean

/-- **`09:1349--1350`.**  The final nodes carrying one split (half-weight)
certificate; the frozen `ell` is this set's cardinality.  The name deliberately
avoids the ladder exponent `ell_v` of `09:1278`, a different symbol. -/
def splitNodes (F : WrapperFrontier r V) (cert : V → Option CertKind) : Finset V :=
  F.finalNodes.filter fun v => cert v = some CertKind.low

theorem bobNodes_disjoint_finalNodes (F : WrapperFrontier r V) :
    Disjoint F.bobNodes F.finalNodes := by
  refine Finset.disjoint_left.mpr fun v hv hv' => ?_
  simp only [bobNodes, finalNodes, Finset.mem_filter] at hv hv'
  rw [hv.2] at hv'
  exact Bool.noConfusion hv'.2

theorem finalNodes_eq_filter_not (F : WrapperFrontier r V) :
    (Finset.univ.filter fun v => ¬ (F.firstBob v = true)) = F.finalNodes := by
  ext v
  simp [finalNodes]

/-- **Aux (the frontier is the disjoint union of its two node kinds).**  Every
frontier node is either a first-Bob node or a final Alice node (`09:1250--1252`),
so any sum over the frontier splits into the two frozen groups.  General in the
value monoid. -/
theorem sum_bobNodes_add_sum_finalNodes {M : Type*} [AddCommMonoid M]
    (F : WrapperFrontier r V) (f : V → M) :
    ∑ v ∈ F.bobNodes, f v + ∑ v ∈ F.finalNodes, f v = ∑ v, f v := by
  classical
  rw [← F.finalNodes_eq_filter_not]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem bobCapacity_nonneg (F : WrapperFrontier r V) : 0 ≤ F.bobCapacity :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem cleanNodes_disjoint_splitNodes (F : WrapperFrontier r V)
    (cert : V → Option CertKind) : Disjoint (F.cleanNodes cert) (F.splitNodes cert) := by
  refine Finset.disjoint_left.mpr fun v hv hv' => ?_
  simp only [cleanNodes, splitNodes, Finset.mem_filter] at hv hv'
  rw [hv.2] at hv'
  exact absurd (Option.some.inj hv'.2) (by decide)

theorem cleanNodes_subset (F : WrapperFrontier r V) (cert : V → Option CertKind) :
    F.cleanNodes cert ⊆ F.finalNodes := Finset.filter_subset _ _

theorem splitNodes_subset (F : WrapperFrontier r V) (cert : V → Option CertKind) :
    F.splitNodes cert ⊆ F.finalNodes := Finset.filter_subset _ _

/-- **`09:1346--1347`, the final-node classification as a count.**  "every final
Alice node contains either one clean certificate, one half-weight descendant of a
split certificate, or none": the clean and split tallies are disjoint groups of
final nodes, so `c + ell <= |final nodes|`.  General. -/
theorem card_cleanNodes_add_card_splitNodes_le (F : WrapperFrontier r V)
    (cert : V → Option CertKind) :
    (F.cleanNodes cert).card + (F.splitNodes cert).card ≤ F.finalNodes.card := by
  classical
  have hsub : F.splitNodes cert
      ⊆ F.finalNodes.filter fun v => ¬ (cert v = some CertKind.clean) := by
    intro v hv
    simp only [splitNodes, Finset.mem_filter] at hv
    simp only [Finset.mem_filter]
    refine ⟨hv.1, ?_⟩
    rw [hv.2]
    exact fun h => absurd (Option.some.inj h) (by decide)
  have hcount := Finset.card_filter_add_card_filter_not
    (s := F.finalNodes) (p := fun v => cert v = some CertKind.clean)
  calc (F.cleanNodes cert).card + (F.splitNodes cert).card
      ≤ (F.finalNodes.filter fun v => cert v = some CertKind.clean).card
        + (F.finalNodes.filter fun v => ¬ (cert v = some CertKind.clean)).card :=
        Nat.add_le_add_left (Finset.card_le_card hsub) _
    _ = F.finalNodes.card := hcount

/-- **Aux E1 (`09:1346--1350`, the final-node weight tally).**

`sum over final nodes of finalWeight = c + ell/2`: the clean nodes contribute `1`
each, the split nodes `1/2` each, and the certificate-free nodes nothing.
General in the node type, the frontier and the certificate assignment. -/
theorem sum_finalWeight_eq (F : WrapperFrontier r V) (cert : V → Option CertKind) :
    ∑ v ∈ F.finalNodes, finalWeight (cert v)
      = ((F.cleanNodes cert).card : ℝ) + ((F.splitNodes cert).card : ℝ) / 2 := by
  classical
  have hpt : ∀ v : V, finalWeight (cert v)
      = (if cert v = some CertKind.clean then (1 : ℝ) else 0)
        + (1 / 2) * (if cert v = some CertKind.low then (1 : ℝ) else 0) := by
    intro v
    cases h : cert v with
    | none => simp [finalWeight]
    | some k => cases k <;> simp [finalWeight, CertKind.weight]
  rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole]
  simp only [cleanNodes, splitNodes]
  ring

/-- **`eq:wrapper-clean-count`'s Kraft input (`09:1364`): `K_B + c + ell <= q`.**

From the banked Kraft bound `sum_v kappa_v <= 2^r`, since the clean and split
final nodes are disjoint subsets of the final nodes and every final node has
capacity exactly one (`09:1252`).  General. -/
theorem kraftSplit (F : WrapperFrontier r V) (cert : V → Option CertKind) :
    F.bobCapacity + ((F.cleanNodes cert).card : ℝ) + ((F.splitNodes cert).card : ℝ)
      ≤ ((2 : ℝ) ^ r) := by
  classical
  have hfinal : ∑ v ∈ F.finalNodes, F.capacity v = F.finalNodes.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_one]
    simp only [finalNodes, Finset.mem_filter] at hv
    exact F.capacity_final_eq_one hv.2
  have htotal := F.sum_bobNodes_add_sum_finalNodes F.capacity
  have hkraft := F.sum_capacity_le_width
  have hcard := F.card_cleanNodes_add_card_splitNodes_le cert
  have hnat : ∑ v ∈ F.bobNodes, F.capacity v + (F.cleanNodes cert).card
      + (F.splitNodes cert).card ≤ 2 ^ r := by omega
  have hcast : F.bobCapacity = ((∑ v ∈ F.bobNodes, F.capacity v : ℕ) : ℝ) := by
    simp [bobCapacity]
  rw [hcast]
  exact_mod_cast hnat

end Counting

end WrapperFrontier

/-! ## §6  `vartheta = 9/16` and the closure of heavy first-Bob nodes
(`09:1268--1313`) -/

/-- **`09:1268`.**  `vartheta = 9/16`, the frontier weight threshold. -/
noncomputable def vartheta : ℝ := 9 / 16

@[simp] theorem vartheta_val : vartheta = 9 / 16 := rfl

theorem vartheta_pos : 0 < vartheta := by norm_num [vartheta]

theorem vartheta_lt_one : vartheta < 1 := by norm_num [vartheta]

/-- **`09:1353`, `09:1355`.**  `1 - vartheta = 7/16`, the denominator of
`eq:wrapper-clean-count`. -/
theorem one_sub_vartheta : 1 - vartheta = 7 / 16 := by norm_num [vartheta]

/-- **`09:1361--1362`, the coefficient comparison.**  A split certificate's
weight `1/2` is below the threshold `vartheta`, which is exactly what turns
`vartheta K_B + c + ell/2` into `vartheta(K_B + ell) + c`. -/
theorem half_le_vartheta : (1 : ℝ) / 2 ≤ vartheta := by norm_num [vartheta]

/-- **`09:1287`, the frozen large-capacity inequality.**

"for `kappa_v >= 16` it follows from `9 kappa_v/16 >= kappa_v/2 + 1`."  General
in the real capacity. -/
theorem nine_sixteenths_ge_halfPlusOne {κ : ℝ} (h : 16 ≤ κ) : κ / 2 + 1 ≤ 9 * κ / 16 := by
  linarith

/-- **`09:1285--1286`, the three immediate cases.**

"the cases `kappa_v = 2,4,8` are immediate": `ceil(9 . 2/16) = 2 = u_2`,
`ceil(9 . 4/16) = 3 = u_4`, `ceil(9 . 8/16) = 5 = u_8`, against the banked
`WrapperProjectionCovers.smallCopyWidth`. -/
theorem ceil_nine_sixteenths_small_cases :
    ⌈(9 : ℝ) * 2 / 16⌉₊ = smallCopyWidth 2
      ∧ ⌈(9 : ℝ) * 4 / 16⌉₊ = smallCopyWidth 4
      ∧ ⌈(9 : ℝ) * 8 / 16⌉₊ = smallCopyWidth 8 := by
  have h2 : smallCopyWidth 2 = 2 := rfl
  have h4 : smallCopyWidth 4 = 3 := rfl
  have h8 : smallCopyWidth 8 = 5 := rfl
  rw [h2, h4, h8]
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [Nat.ceil_eq_iff (by norm_num)]
      norm_num

/-- **`09:1280--1287`, the represented-coordinate count at a heavy node.**

"Every certificate has weight `1` or `1/2`, and at a fixed node there is at most
one descendant of each initial outer coordinate.  Hence the number of represented
coordinates is at least `ceil(W_v)`, and `ceil(W_v) >= ceil(9 kappa_v/16) >=
u_{kappa_v}`."

Proved uniformly on the dyadic capacities `kappa = 2^ell` with `ell >= 1`, which
covers the frozen cases `kappa = 2, 4, 8` and `kappa >= 16` at once: the banked
`smallCopyWidth_dyadic` reads `u_{2^ell} = 2^{ell-1} + 1`, and
`2^{ell-1} < 9 . 2^ell/16` is the single inequality behind all of them.
`ceil_nine_sixteenths_small_cases` and `nine_sixteenths_ge_halfPlusOne` record the
frozen case split itself.  General in `ell >= 1` and in the weight `W`. -/
theorem smallCopyWidth_le_ceil_weight {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {W : ℝ}
    (hW : vartheta * ((2 : ℝ) ^ ℓ) ≤ W) : smallCopyWidth (2 ^ ℓ) ≤ ⌈W⌉₊ := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  rw [smallCopyWidth_dyadic hℓ]
  simp only [Nat.add_sub_cancel]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hstrict : ((2 ^ n : ℕ) : ℝ) < W := by
    have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    rw [hcast]
    have : vartheta * ((2 : ℝ) ^ (n + 1)) = 9 / 8 * (2 : ℝ) ^ n := by
      rw [vartheta_val, pow_succ]; ring
    rw [this] at hW
    linarith
  have := Nat.lt_ceil.mpr hstrict
  omega

/-- **`09:1288--1290`, the denser Bob child.**

"Every represented coordinate is outside `E_0`, so the parent projection to any
selected `u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob
child retains density at least `y^2`."

The two Bob children partition the parent's columns, so their densities sum to at
least the parent's; the denser of the two is therefore at least half of `2y^2`.
General in `y` and in the two child densities. -/
theorem denserChild_density {d₀ d₁ y : ℝ} (h : 2 * y ^ 2 ≤ d₀ + d₁) :
    y ^ 2 ≤ max d₀ d₁ := by
  rcases le_total d₀ d₁ with hle | hle
  · rw [max_eq_right hle]; linarith
  · rw [max_eq_left hle]; linarith

/-- **`09:1290` at the frozen numbers, by pin.**

`rho = 2y^2 = 18/25` at the frozen `y = 3/5` is the banked
`WrapperProjectionCovers.rhoSmall`; the denser child retains `y^2 = 9/25`. -/
theorem denserChild_density_frozen {d₀ d₁ : ℝ} (h : rhoSmall ≤ d₀ + d₁) :
    (9 : ℝ) / 25 ≤ max d₀ d₁ := by
  have hy : (2 : ℝ) * ((3 : ℝ) / 5) ^ 2 = rhoSmall := rhoSmall_eq_two_y_sq
  have : (9 : ℝ) / 25 = ((3 : ℝ) / 5) ^ 2 := by norm_num
  rw [this]
  exact denserChild_density (by rw [hy]; exact h)

/-- **`09:1302--1304`, the row-density legality chain.**

"`kappa_v x_T <= t_ref x_T <= 1` verifies legality."  The outer guard is the
banked `WrapperLowRungs.simple_gate_forces_tRef_row_legality`, consumed by pin
from `eq:wrapper-low-simple-gate`; the inner one is monotonicity in the exponent
at the small-capacity range `kappa_v < t_ref`, i.e. `ell_v <= k`.  General. -/
theorem capacity_row_density_legal {ℓ k r : ℕ} {xT : ℝ} (hxT0 : 0 ≤ xT)
    (hℓk : ℓ ≤ k) (hq4 : k + 2 ≤ r) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025) :
    ((2 : ℝ) ^ ℓ) * xT ≤ 1 := by
  have htref : ((2 : ℝ) ^ k) * xT ≤ 1 :=
    simple_gate_forces_tRef_row_legality hq4 hxT0 hgate
  have hmono : (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hℓk
  nlinarith

/-- **`09:1296--1306`, the small-capacity ladder call.**

"Apply `lem:certified-row-ladder` with `M = G`, `H = C-1`, `x = x_T`, `z = y`,
`ell = ell_v`.  The base certificate is `lem:wrapper-reference`; `C >= 3` verifies
`H >= 2`, and `kappa_v x_T <= t_ref x_T <= 1` verifies legality.  The selected Bob
child therefore has complexity at least `C + log_2 kappa_v - 1`."

The ladder itself is the banked, **proved**
`TerminalTwoStream.certifiedRowLadder_of_base`, consumed by pin and re-proved
nowhere; what is new here is the substitution `H = C-1` with its `C >= 3` guard
and the arithmetic reading `(C-1) + ell = C + ell - 1`.  `hbase` is the second
clause of the banked `lem:wrapper-reference` (`09:1302`), carried as a binder.
General in the carriers, `C`, `ell_v`, `x_T` and `y`. -/
theorem smallCapacity_child_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (Gmat : X → Y → Bool) {C ℓ : ℕ} {xT y : ℝ}
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (hℓ : 1 ≤ ℓ) (hlegal : ((2 : ℝ) ^ ℓ) * xT ≤ 1) :
    C + ℓ - 1 ≤ LambdaGE Gmat (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ℓ * xT) (y ^ 2) := by
  have hladder := certifiedRowLadder_of_base Gmat hX hY (H := C - 1) (by omega) hxT0 hy0 hy1
    hbase ℓ hℓ hlegal
  omega

/-- **`09:1306--1308`, "one more bit than the remaining child budget".**

At a first-Bob node `v` reached after `d_v` Alice queries, with
`ell_v = log_2 kappa_v = r - d_v`, the suffix below the selected Bob child of the
alleged `(C+r-1)`-bit protocol has depth at most `C + ell_v - 2`, while both
closure branches give the child complexity at least `C + ell_v - 1`.  The gap is
exactly one bit.

The depth relation is stated subtraction-free as `d + ell = r`.  General. -/
theorem firstBob_budget_contradiction {C r d ℓ B : ℕ} (hC : 3 ≤ C) (hdℓ : d + ℓ = r)
    (hℓ : 1 ≤ ℓ) (hbudget : B + (d + 1) ≤ C + r - 1) (hlower : C + ℓ - 1 ≤ B) : False := by
  omega

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`).**

"Therefore `W_v < vartheta kappa_v` at every first-Bob node `v`."

The frozen argument is by contradiction: a node with `W_v >= vartheta kappa_v`
would be *closed*, its selected Bob child carrying complexity at least
`C + log_2 kappa_v - 1`, one bit more than the remaining budget.  The closure
itself is the branch-dependent hypothesis `hclosure` -- the large-capacity
endpoint call of `09:1269--1276` (GAP-EXPOSED 3) or the small-capacity ladder of
`09:1296--1306` (`smallCapacity_child_bound`) -- and the strictness of the
conclusion is what this theorem produces.  General in `C`, `r`, `d`, `ell_v`, the
residual budget and the weight. -/
theorem wrapperFirstBobLight {C r d ℓ B : ℕ} {W : ℝ} (hC : 3 ≤ C) (hdℓ : d + ℓ = r)
    (hℓ : 1 ≤ ℓ) (hbudget : B + (d + 1) ≤ C + r - 1)
    (hclosure : vartheta * ((2 : ℝ) ^ ℓ) ≤ W → C + ℓ - 1 ≤ B) :
    W < vartheta * ((2 : ℝ) ^ ℓ) := by
  by_contra hcon
  exact firstBob_budget_contradiction hC hdℓ hℓ hbudget (hclosure (not_lt.mp hcon))

/-- **Statement pole for `wrapperFirstBobLight`: the margin is exactly one bit.**

`09:1308` says the closure's lower bound "is one more bit than the remaining
child budget".  Were the residual bound only `C + ell_v - 2`, the two constraints
would be consistent and no contradiction would follow -- here at
`C = 3, r = 3, d = 1, ell = 2, B = 3`, where `B + (d+1) = 5 = C + r - 1` and
`B = C + ell - 2`.  So the theorem's strength comes from the extra bit and not
from an over-tight budget hypothesis. -/
theorem firstBobLight_needs_the_extra_bit :
    (3 : ℕ) + (1 + 1) ≤ 3 + 3 - 1 ∧ (3 : ℕ) = 3 + 2 - 2 ∧ ¬ ((3 : ℕ) + 2 - 1 ≤ 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## §7  `lem:final-reference-uniqueness` (`09:1315--1344`)

"Every final Alice-frontier node in the routed certificate system above contains
at most one reference certificate, whether clean or split." -/

/-- **`09:1341--1343`, the final-node budget contradiction.**

"The resulting two-copy restriction has complexity at least `C`.  But the suffix
below a node reached after `r` Alice bits in the alleged `(C+r-1)`-bit protocol
has depth at most `C-1`, a contradiction."  General. -/
theorem finalNode_budget_contradiction {C r B : ℕ} (hC : 3 ≤ C) (hbudget : B + r ≤ C + r - 1)
    (hlower : C ≤ B) : False := by omega

/-- **`09:1334--1340`, the `ell = 1` ladder call at a final node.**

"Invoke `lem:certified-row-ladder` with `M = G`, `H = C-1`, `x = x_T`, `z = y`,
`ell = 1`.  The hypotheses are supplied by `lem:wrapper-reference`, `C >= 3`, and
`2 x_T <= t_ref x_T <= 1`.  The resulting two-copy restriction has complexity at
least `C`."

This is `smallCapacity_child_bound` at `ell = 1`, where `2^{ell-1} + 1 = 2` is
the frozen two-copy restriction and `C + 1 - 1 = C` the frozen output.  General. -/
theorem finalNode_twoCopy_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (Gmat : X → Y → Bool) {C : ℕ} {xT y : ℝ}
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y) (hlegal : 2 * xT ≤ 1) :
    C ≤ LambdaGE Gmat 2 (2 * xT) (y ^ 2) := by
  have h := smallCapacity_child_bound Gmat (ℓ := 1) hX hY hC hxT0 hy0 hy1 hbase
    (le_refl 1) (by simpa using hlegal)
  simpa using h

/-- **`lem:final-reference-uniqueness` (`09:1315--1319`).**

"Every final Alice-frontier node in the routed certificate system above contains
at most one reference certificate, whether clean or split."

The frozen proof is by contradiction from a pair: two certificates at one final
node descend from **distinct** initial outer coordinates `i, j` (a fixed protocol
node receives at most one descendant of any initial certificate, `09:1322--1324`),
the pair avoids the `u_2 = 2` small-copy cover, so its two-coordinate column
projection retains density at least `rho = 2y^2` and hence `y^2`
(`09:1329--1332`), and the `ell = 1` ladder then gives complexity at least `C`
against a suffix depth of at most `C-1`.

`hdistinct` is the frozen `09:1322--1324`; `hladder` is the composite of
`09:1329--1340` -- the cover avoidance, the surviving density and
`finalNode_twoCopy_bound` -- carried as the named hypothesis it is, since the
column projection at a protocol node is not modelled (GAP-EXPOSED 2); `hsuffix`
is `09:1341--1343`.  General in the certificate index type. -/
theorem wrapperFinalReferenceUniqueness {ι Coord : Type*}
    {C r : ℕ} (certs : Finset ι) (coord : ι → Coord) (residual : ι → ι → ℕ)
    (hC : 3 ≤ C)
    (hdistinct : ∀ i ∈ certs, ∀ j ∈ certs, i ≠ j → coord i ≠ coord j)
    (hladder : ∀ i ∈ certs, ∀ j ∈ certs, coord i ≠ coord j → C ≤ residual i j)
    (hsuffix : ∀ i j, residual i j + r ≤ C + r - 1) :
    certs.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun i hi j hj => ?_
  by_contra hij
  exact finalNode_budget_contradiction hC (hsuffix i j)
    (hladder i hi j hj (hdistinct i hi j hj hij))

/-! ## §8  `eq:wrapper-clean-count` (`09:1346--1365`)

"Let `K_B` be the sum of `kappa_v` over first-Bob nodes, let `c` be the number of
final nodes with one clean certificate, and let `ell` be the number with one
split certificate.  From `eq:wrapper-frontier-conservation`,
`eq:wrapper-first-bob-light`, and Kraft's inequality,
`c >= q - e_0/(1-vartheta)`, `K_B + ell <= e_0/(1-vartheta)`.  Indeed,
`q - e_0 <= vartheta K_B + c + ell/2 <= vartheta(q-c) + c`, which gives the first
inequality, while `K_B + c + ell <= q` gives the second." -/

/-- **`eq:wrapper-clean-count` (`09:1352--1357`), the arithmetic core.**

Exactly the frozen derivation of `09:1358--1365`: from the aggregated
conservation inequality `q - e_0 <= vartheta K_B + c + ell/2` and Kraft's
`K_B + c + ell <= q`, both conclusions follow, using `1/2 <= vartheta`
(`half_le_vartheta`) to absorb the half-weight column and `1 - vartheta = 7/16`
to clear the denominator.  General in all five reals. -/
theorem cleanCount_arithmetic {q e0 KB c l : ℝ}
    (hcons : q - e0 ≤ vartheta * KB + c + l / 2) (hkraft : KB + c + l ≤ q)
    (hl : 0 ≤ l) :
    q - e0 / (1 - vartheta) ≤ c ∧ KB + l ≤ e0 / (1 - vartheta) := by
  have hden : e0 / (1 - vartheta) = 16 * e0 / 7 := by
    rw [one_sub_vartheta]; ring
  rw [hden, vartheta_val] at *
  constructor <;> linarith

/-- **Statement pole for `cleanCount_arithmetic`: Kraft is load-bearing.**

At `q = 16`, `e_0 = 0`, `K_B = 32`, `c = 0`, `l = 0` the conservation inequality
`q - e_0 <= vartheta K_B + c + l/2` holds (`16 <= 18`) and the first conclusion
`c >= q - e_0/(1-vartheta) = 16` **fails**.  So `09:1364`'s `K_B + c + ell <= q`
is not decoration, and the theorem is not a triviality about the shape of its
conclusion. -/
theorem cleanCount_needs_kraft :
    (16 : ℝ) - 0 ≤ vartheta * 32 + 0 + 0 / 2
      ∧ ¬ ((32 : ℝ) + 0 + 0 ≤ 16)
      ∧ ¬ ((16 : ℝ) - 0 / (1 - vartheta) ≤ 0) := by
  refine ⟨by norm_num [vartheta], by norm_num, by norm_num [vartheta]⟩

/-- **`eq:wrapper-clean-count` (`09:1352--1357`), at the routed frontier.**

The frozen statement, assembled from this module's own results and pins:

* `hcons` is `eq:wrapper-frontier-conservation`'s first clause `sum_v W_v >= q -
  e_0` (`09:1262`), a named hypothesis because the routing dynamics that produce
  it are not modelled (GAP-EXPOSED 4);
* `hlight` is `eq:wrapper-first-bob-light` (`09:1312`), whose per-node strict form
  is `wrapperFirstBobLight`;
* `hfinal` is the final-node classification of `09:1346--1347`, which
  `wrapperFinalReferenceUniqueness` is what licenses;
* Kraft's inequality is the banked `sum_stoppingCapacity_le_width`, applied
  through `kraftSplit`.

The conclusion is the frozen pair `c >= q - e_0/(1-vartheta)` and
`K_B + ell <= e_0/(1-vartheta)`, at `q = 2^r`.  General in the frontier's node
type, in `r`, in the certificate assignment, in the weight function and in
`e_0`. -/
theorem wrapperCleanCount {V : Type*} [Fintype V] {r : ℕ}
    (F : WrapperFrontier r V) (cert : V → Option CertKind) (W : V → ℝ) {q e0 : ℝ}
    (hq : q = (2 : ℝ) ^ r)
    (hlight : ∀ v ∈ F.bobNodes, W v ≤ vartheta * (F.capacity v : ℝ))
    (hfinal : ∀ v ∈ F.finalNodes, W v ≤ finalWeight (cert v))
    (hcons : q - e0 ≤ ∑ v, W v) :
    q - e0 / (1 - vartheta) ≤ ((F.cleanNodes cert).card : ℝ)
      ∧ F.bobCapacity + ((F.splitNodes cert).card : ℝ) ≤ e0 / (1 - vartheta) := by
  classical
  have hsplit := F.sum_bobNodes_add_sum_finalNodes W
  have hbob : ∑ v ∈ F.bobNodes, W v ≤ vartheta * F.bobCapacity := by
    rw [WrapperFrontier.bobCapacity, Finset.mul_sum]
    exact Finset.sum_le_sum hlight
  have hfin : ∑ v ∈ F.finalNodes, W v
      ≤ ((F.cleanNodes cert).card : ℝ) + ((F.splitNodes cert).card : ℝ) / 2 := by
    rw [← F.sum_finalWeight_eq cert]
    exact Finset.sum_le_sum hfinal
  have hagg : q - e0 ≤ vartheta * F.bobCapacity + ((F.cleanNodes cert).card : ℝ)
      + ((F.splitNodes cert).card : ℝ) / 2 := by
    calc q - e0 ≤ ∑ v, W v := hcons
      _ = ∑ v ∈ F.bobNodes, W v + ∑ v ∈ F.finalNodes, W v := hsplit.symm
      _ ≤ vartheta * F.bobCapacity
          + (((F.cleanNodes cert).card : ℝ) + ((F.splitNodes cert).card : ℝ) / 2) := by
          exact add_le_add hbob hfin
      _ = vartheta * F.bobCapacity + ((F.cleanNodes cert).card : ℝ)
          + ((F.splitNodes cert).card : ℝ) / 2 := by ring
  have hkraft : F.bobCapacity + ((F.cleanNodes cert).card : ℝ)
      + ((F.splitNodes cert).card : ℝ) ≤ q := by
    rw [hq]; exact F.kraftSplit cert
  exact cleanCount_arithmetic hagg hkraft (by positivity)

/-! ## §9  Non-vacuity: the probe frontier and the full hypothesis bundle -/

/-- A three-node routed frontier at `r = 2`, so `q = 4`: one first-Bob node at
suffix depth `1` (capacity `2`) and two final Alice nodes at depth `2` (capacity
`1` each).  Both kinds of node occur, so no field of `WrapperFrontier` is
satisfied by an empty case, and Kraft is **attained**:
`sum_v kappa_v = 2 + 1 + 1 = 4 = q`. -/
def probeRoute : Fin 3 → List Bool := ![[true], [false, false], [false, true]]

def probeFirstBob : Fin 3 → Bool := ![true, false, false]

theorem probeRoute_prefixFree : PrefixFreeFrontier probeRoute := by
  intro v w hvw hpre
  obtain ⟨t, ht⟩ := hpre
  fin_cases v <;> fin_cases w <;> simp [probeRoute] at ht hvw

/-- **Non-vacuity (tier 2): `WrapperFrontier` has a nondegenerate inhabitant.**

Every field is discharged at genuinely mixed data -- a first-Bob node with
`kappa_v = 2 >= 2` and two final nodes with `kappa_v = 1` -- so neither the
exposure rule nor the final-depth rule is satisfied vacuously.  Tier 2: the
frozen schedule forces far larger `r`, and every statement above is general in
`r` and in the node type. -/
def wrapperFrontierProbe : WrapperFrontier 2 (Fin 3) where
  route := probeRoute
  prefixFree := probeRoute_prefixFree
  depth_le := by decide
  firstBob := probeFirstBob
  firstBob_depth_lt := by decide
  final_depth_eq := by decide

/-- **The probe frontier realizes both node kinds and attains Kraft.**

`kappa = 2, 1, 1` summing to `4 = 2^r`, with the first-Bob node genuinely above
capacity one.  This is what makes `wrapperFrontierProbe` a nondegenerate
inhabitant rather than a formal one. -/
theorem wrapperFrontierProbe_nondegenerate :
    wrapperFrontierProbe.capacity 0 = 2
      ∧ wrapperFrontierProbe.capacity 1 = 1
      ∧ wrapperFrontierProbe.capacity 2 = 1
      ∧ ∑ v, wrapperFrontierProbe.capacity v = 2 ^ 2
      ∧ wrapperFrontierProbe.firstBob 0 = true
      ∧ wrapperFrontierProbe.firstBob 1 = false := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  decide

/-- The probe certificate assignment: the first-Bob node carries none, and both
final nodes carry one clean certificate, so `c = 2` and `ell = 0`. -/
def probeCert : Fin 3 → Option CertKind :=
  fun v => if v = 0 then none else some CertKind.clean

/-- The probe weights: `W = 1` at every node.  At the first-Bob node this is
below `vartheta kappa_v = 9/8`, as `eq:wrapper-first-bob-light` demands, and at
each final node it is exactly the clean weight. -/
noncomputable def probeWeight : Fin 3 → ℝ := fun _ => 1

/-- **HYPOTHESIS CONSISTENCY (tier 2): the headline's entire bundle is jointly
satisfiable, and its conclusions are nondegenerate.**

Every hypothesis of `wrapperCleanCount` is discharged at the probe frontier with
`q = 4` and `e_0 = 1`:

* `hq`, `q = 2^r = 4`;
* `hlight`, `W_v = 1 <= vartheta . 2 = 9/8` at the single first-Bob node --
  strictly below, so the light bound is not met with equality by accident;
* `hfinal`, `W_v = 1 = finalWeight(clean)` at both final nodes;
* `hcons`, `q - e_0 = 3 <= 3 = sum_v W_v`.

and both conclusions come out with room: the clean count is `c = 2`, strictly
above the frozen bound `q - e_0/(1-vartheta) = 4 - 16/7 = 12/7`, and
`K_B + ell = 2 + 0 = 2 <= 16/7`.  Kraft is attained (`K_B + c + ell = 4 = q`), so
the bundle sits exactly on the frozen boundary rather than in a slack corner, and
no `False` follows from it. -/
theorem wrapperCleanCount_legal_instance :
    (4 : ℝ) = (2 : ℝ) ^ 2
      ∧ (∀ v ∈ wrapperFrontierProbe.bobNodes,
          probeWeight v ≤ vartheta * (wrapperFrontierProbe.capacity v : ℝ))
      ∧ (∀ v ∈ wrapperFrontierProbe.finalNodes,
          probeWeight v ≤ finalWeight (probeCert v))
      ∧ ((4 : ℝ) - 1 ≤ ∑ v, probeWeight v)
      ∧ (wrapperFrontierProbe.cleanNodes probeCert).card = 2
      ∧ (wrapperFrontierProbe.splitNodes probeCert).card = 0
      ∧ (4 : ℝ) - 1 / (1 - vartheta) ≤ ((wrapperFrontierProbe.cleanNodes probeCert).card : ℝ)
      ∧ wrapperFrontierProbe.bobCapacity
          + ((wrapperFrontierProbe.splitNodes probeCert).card : ℝ) ≤ 1 / (1 - vartheta) := by
  classical
  have hbob : wrapperFrontierProbe.bobNodes = {0} := by decide
  have hfinal : wrapperFrontierProbe.finalNodes = {1, 2} := by decide
  have hclean : (wrapperFrontierProbe.cleanNodes probeCert).card = 2 := by decide
  have hsplit : (wrapperFrontierProbe.splitNodes probeCert).card = 0 := by decide
  have hcap0 : wrapperFrontierProbe.capacity 0 = 2 := rfl
  have hcap : wrapperFrontierProbe.bobCapacity = 2 := by
    rw [WrapperFrontier.bobCapacity, hbob, Finset.sum_singleton, hcap0]
    norm_num
  refine ⟨by norm_num, ?_, ?_, ?_, hclean, hsplit, ?_, ?_⟩
  · intro v hv
    rw [hbob] at hv
    simp only [Finset.mem_singleton] at hv
    subst hv
    rw [hcap0]
    norm_num [probeWeight, vartheta]
  · intro v hv
    rw [hfinal] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    have hc : probeCert v = some CertKind.clean := by
      rcases hv with rfl | rfl <;> rfl
    rw [hc]
    norm_num [probeWeight]
  · simp [probeWeight]
    norm_num
  · rw [hclean]; norm_num [vartheta]
  · rw [hcap, hsplit]; norm_num [vartheta]

/-- **The headline fires at the probe.**  `wrapperCleanCount` applied to the
discharged bundle, so the theorem is not merely stated over a satisfiable
hypothesis set but actually produces its two conclusions there. -/
theorem wrapperCleanCount_fires_at_probe :
    (4 : ℝ) - 1 / (1 - vartheta) ≤ ((wrapperFrontierProbe.cleanNodes probeCert).card : ℝ)
      ∧ wrapperFrontierProbe.bobCapacity
          + ((wrapperFrontierProbe.splitNodes probeCert).card : ℝ) ≤ 1 / (1 - vartheta) := by
  obtain ⟨hq, hlight, hfinal, hcons, -, -, -, -⟩ := wrapperCleanCount_legal_instance
  exact wrapperCleanCount wrapperFrontierProbe probeCert probeWeight hq hlight hfinal hcons

/-- The probe's Bob-free predicate: a path is Bob-free when it carries no `true`
bit.  Only a local encoding for the probe -- the library statements take the
predicate as a parameter, since which nodes are Bob nodes is protocol data. -/
def probeBobFree : List Bool → Bool := fun p => !(p.any id)

/-- Two probe leaves, one Bob-free and one not, so both clauses of
`wrapperNoBobCompletion` are exercised. -/
def probeLeaves : Finset (List Bool) := {[false], [true]}

/-- A leaf family in which the Bob-free path is **longer** than `r = 2`: three
bits, none of them a Bob query.  Its purpose is to exercise the frozen quantifier
of `09:1198--1200`, which ranges over every no-Bob path and not only the short
ones, so `wrapperNoBobCompletion` must fire here too. -/
def probeLongLeaves : Finset (List Bool) := {[false, false, false], [true]}

/-- **Non-vacuity (tier 2) for `lem:wrapper-no-bob-completion`.**

The bundle is discharged at `C = 3`, `r = 2`, `cost = 1` on a leaf family
containing **both** a Bob-free path (`[false]`, enlarged to depth `2`) and a
Bob-carrying path (`[true]`, left untouched), so neither of the lemma's two
clauses is satisfied by an empty case.  The completed cost `max{1, 2} = 2` is
within the frozen budget `C + r - 1 = 4`.

`hshort` is recorded as a *separate* readout, not as a hypothesis of the lemma:
it is the guard of the optional `09:1206` sharpening only. -/
theorem wrapperNoBobCompletion_legal_instance :
    (∀ p ∈ probeLeaves, p.length ≤ 1) ∧ (∀ p ∈ probeLeaves, p.length ≤ 2)
      ∧ probeBobFree [false] = true ∧ probeBobFree [true] = false
      ∧ completeRoute 2 probeBobFree [true] = [true]
      ∧ (completeRoute 2 probeBobFree [false]).length = 2 := by
  refine ⟨?_, ?_, by decide, by decide, ?_, ?_⟩
  · decide
  · decide
  · exact completeRoute_of_not_bobFree (by decide)
  · exact completeRoute_length_eq (by decide) (by decide)

/-- **`wrapperNoBobCompletion` fires at the probe.**  All three frozen clauses
are produced from the discharged bundle -- with the frozen second clause
`r <= length` and no depth restriction on the leaves. -/
theorem wrapperNoBobCompletion_fires_at_probe :
    (∀ p ∈ probeLeaves, probeBobFree p = false → completeRoute 2 probeBobFree p = p)
      ∧ (∀ p ∈ probeLeaves, probeBobFree p = true →
          2 ≤ (completeRoute 2 probeBobFree p).length)
      ∧ (∀ p ∈ probeLeaves, (completeRoute 2 probeBobFree p).length ≤ 3 + 2 - 1) := by
  obtain ⟨hlen, -, -, -, -, -⟩ := wrapperNoBobCompletion_legal_instance
  exact wrapperNoBobCompletion (C := 3) (r := 2) (cost := 1) (bobFree := probeBobFree)
    probeLeaves (by norm_num) (by norm_num) hlen

/-- **The restored quantifier is load-bearing: the lemma fires on an
over-length no-Bob path.**

At `C = 3`, `r = 2`, `cost = 3` the family `probeLongLeaves` contains the Bob-free
path `[false, false, false]` of depth `3 > r`.  The former `hshort` hypothesis
would have been **unsatisfiable** here, so the narrowed statement could not have
been applied at all; the frozen statement produces all three clauses, with the
over-length path fixed by the completion (`3 = max{3, 2}`) and still meeting
`r <= length`. -/
theorem wrapperNoBobCompletion_fires_on_long_path :
    ¬ (∀ p ∈ probeLongLeaves, p.length ≤ 2)
      ∧ completeRoute 2 probeBobFree [false, false, false] = [false, false, false]
      ∧ (∀ p ∈ probeLongLeaves, probeBobFree p = true →
          2 ≤ (completeRoute 2 probeBobFree p).length)
      ∧ (∀ p ∈ probeLongLeaves, (completeRoute 2 probeBobFree p).length ≤ 3 + 2 - 1) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [completeRoute_eq_of_bobFree (by decide)]
    norm_num
  · obtain ⟨-, h2, h3⟩ := wrapperNoBobCompletion (C := 3) (r := 2) (cost := 3)
      (bobFree := probeBobFree) probeLongLeaves (by norm_num) (by norm_num) (by decide)
    exact ⟨h2, h3⟩

/-- **Non-vacuity (tier 2) for `lem:final-reference-uniqueness`.**

The bundle is jointly satisfiable with a **nonempty** certificate set: at
`C = 3`, `r = 1`, one certificate at coordinate `0`, and a residual budget of
`2 = C - 1`, every hypothesis holds and the conclusion `card <= 1` is produced.
So the lemma is not green-because-its-hypotheses-are-empty.

What is *not* satisfiable is the same bundle with two certificates at distinct
coordinates -- and that is the frozen contradiction itself
(`finalNode_budget_contradiction`), not a defect: `hladder` would then demand
`3 <= 2`. -/
theorem finalReferenceUniqueness_legal_instance :
    ((({0} : Finset (Fin 2))).card = 1)
      ∧ (∀ i ∈ ({0} : Finset (Fin 2)), ∀ j ∈ ({0} : Finset (Fin 2)), i ≠ j →
          (id i : Fin 2) ≠ id j)
      ∧ (∀ i ∈ ({0} : Finset (Fin 2)), ∀ j ∈ ({0} : Finset (Fin 2)),
          (id i : Fin 2) ≠ id j → (3 : ℕ) ≤ 2)
      ∧ (∀ _i _j : Fin 2, (2 : ℕ) + 1 ≤ 3 + 1 - 1) := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  intro i hi j hj hne
  simp only [Finset.mem_singleton] at hi hj
  subst hi; subst hj
  exact absurd rfl hne

/-- **`wrapperFinalReferenceUniqueness` fires at the probe.** -/
theorem finalReferenceUniqueness_fires_at_probe :
    (({0} : Finset (Fin 2))).card ≤ 1 := by
  obtain ⟨-, hdist, hlad, hsuf⟩ := finalReferenceUniqueness_legal_instance
  exact wrapperFinalReferenceUniqueness (C := 3) (r := 1) ({0} : Finset (Fin 2)) id
    (fun _ _ => 2) (by norm_num) hdist hlad hsuf

/-- **Statement pole: prefix-freeness is what makes Kraft available.**

Dropping it, three nodes at depths `1, 1, 1` below `r = 2` would carry total
capacity `6 > 4 = q`, and `kraftSplit` -- hence the second half of
`eq:wrapper-clean-count` -- would be false.  Recorded on the raw capacity weight,
so no `WrapperFrontier` is constructed from illegal data. -/
theorem wrapperFrontier_needs_prefixFree :
    ¬ (∑ _v : Fin 3, stoppingCapacity 2 1 ≤ 2 ^ 2) := by decide

end EthInapproximability.ParameterizedNP.DenseWrapperFrontier
