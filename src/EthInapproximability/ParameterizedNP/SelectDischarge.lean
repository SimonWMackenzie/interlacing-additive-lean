import EthInapproximability.ParameterizedNP.FirstBobLightDichotomy

/-!
# Parameterized NP route: the `hselect` discharge (`09:1287--1296`)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand this tranche), with
  `sections/A-certified-stopping.tex`
  (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`)
  and `sections/02-mechanical-contract.tex`
  (SHA-256 `019209B4EDF21015507148310EFBED757A83FD7709CF3880E178A4C535097A3D`).
* **The exact frozen lines traced here**, in print order:
  * `09:105`, `q = 2^r`, and `09:107`, `U = <N>^q` -- why the ambient column
    carrier of the alleged protocol is a `q`-tuple type `Fin q -> Yc`;
  * `09:113--116`, `R_G` and `G = N[R_G, Cols(N)]` with `m_G = |Rows(G)|`, and
    `09:121--123` (`eq:reference-all-columns`), `Cols(G) = Cols(N)` -- why the
    reference copies share the ambient column alphabet;
  * `09:434--441`, the small-capacity display: `09:436`, `rho = 2y^2 = 18/25`;
    `09:438`, `u_2 = 2`; and `09:440`, `u_kappa = kappa/2 + 1` for
    `4 <= kappa < t_ref`;
  * `09:442--445`, "For every dyadic `2 <= kappa < t_ref`, take one
    maximal-matching cover of the coordinate sets of size `u_kappa` whose
    projection density is below `rho`" -- the cover clause this module consumes;
  * `09:1235--1236`, "Start one clean reference certificate in every coordinate
    outside `E_0`" -- the frozen start rule, carried as the named binder `hstart`;
  * `09:1250--1252`, the two stopping rules, and `09:1253--1257`, `d_v`,
    `kappa_v` and `W_v`;
  * **`09:1287--1290`**, "Every represented coordinate is outside `E_0`, so the
    parent projection to any selected `u_{kappa_v}` of them has density at least
    `rho = 2y^2`.  The denser Bob child retains density at least `y^2`" -- leg (1)
    of this tranche;
  * `09:1291--1296`, "Each selected certificate has at least
    `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows, so trim it to
    the row density `kappa_v x_T`" -- the row supply of the bracket member;
  * `09:1296--1306`, the `lem:certified-row-ladder` call at
    `M = G, H = C-1, x = x_T, z = y, ell = ell_v`, whose conclusion quantity is
    the `LambdaGE` on the left of `hselect` -- leg (2)'s target;
  * `A:150--160`, `lem:certified-row-ladder` itself, consumed **only** through
    the banked `TerminalTwoStream.certifiedRowLadder_of_base` at its call sites,
    and not re-derived here.
* **Cross-anchors opened first-hand this tranche:** `09:1188--1194` (the
  **alleged** `(C+r-1)`-bit protocol computing a member of
  `<U,1,1-delta_U,theta>`), `09:1219` (`A_0 = ceil(2 x_T m_G)`), `09:1302--1304`
  (`C >= 3` and the legality chain), `09:1309--1313`
  (`eq:wrapper-first-bob-light`), `02:definition of the bracket family` as the
  frozen `def:bracket`/`def:equipartition` pair reached through the vendored
  `NPCC.bracketGE` and `NPCC.IsEquipartitionedGE`.

## What this tranche does: the two legs, and what remains

`hselect` -- the named binder carried unchanged through
`SplitFirstBobInstance` (GAP-EXPOSED item 15), `LargeCapacityBranch`,
`TranscriptLevelJoin` and `FirstBobLightDichotomy` -- is the implication

```text
u_{kappa_v} <= |represented coordinates at v|
  ->  Lambda_G(2^{ell_v - 1} + 1, kappa_v x_T, y^2) <= cost(subtree at v ++ [b]).
```

The frozen text reaches it in two steps, and **both are proved here**:

* **Leg (1), `09:1287--1290`, the projection-at-a-node lemma.**
  `parent_projection_dense_at_frontier_node` proves the *parent* half: at a
  frontier node of any `RoutedCertificateSystem.RoutedSystem` the node's route is
  Alice-only (the banked `RoutedSystem.node_isAlicePath`), so the banked
  `nodeProjection_of_isAlicePath` identifies the node's column projection with the
  ambient one, and a selection of `u_{kappa_v}` coordinates that avoids `E_0`
  cannot be poor -- so its projection density is at least `rho`.  The frozen
  reason it avoids `E_0` is `09:1235--1236`, the start rule, which enters as the
  explicit binder `hstart` and is turned into the frozen sentence by
  `representedCoords_image_avoids_E0`.  `projection_at_a_node` then adds the
  *child* half by pin -- the banked `RoutingDynamics.denserBobChild_retains_y_sq`
  -- at the value `y = 3/5` that `09:436` **defines** (see the DEFINED-vs-FREE
  paragraph below).
* **Leg (2), the `LambdaGE`-to-subtree-cost bridge.**
  `lambdaGE_le_cost_descend_of_bracket_member` proves that a bracket member
  **localized at a node** -- a row set, a column set, and two sections of the
  ambient carriers whose images reach the node -- bounds the node's residual
  cost from below by `Lambda_G` at the member's own parameters.  Its three
  ingredients are consumed by pin and re-derived nowhere: `LambdaGE` is a minimum
  over its first rung (`min_le_left`), `Dfamily` is an infimum over members
  (`EthBridge.Dfamily_le_member`), and the residual comparison is the banked
  `TerminalResidualComparison.D_le_cost_descend_of_computes`.

The two legs are then joined at the paper's own quantities.  The copy count of
the ladder call is `2^{ell_v - 1} + 1`, and the width of the selected coordinate
set is `u_{kappa_v} = kappa_v/2 + 1`; at `kappa_v = 2^{ell_v}` **these are the
same number**, which is why the selected outer coordinates *are* the interlace's
copies.  Section 3b's `nodeProjection_transport_density` carries leg (1)'s
estimate from the outer alphabet to the reference matrix's column type with no
loss, `bracket_column_clause_of_projection_density` turns the resulting real
density into the bracket family's own ceiling clause, and
`bracketMember_of_blocks_and_columns` assembles the member from `09:1291--1296`'s
per-certificate trims and that clause.

Sections 2 and 3 also supply the two *routing* hypotheses the bridge needs, which
were previously unavailable because the node's column set
(`RoutedCertificateSystem.bobCols`, the object leg (1) projects) and the routing
predicate (`TerminalResidualComparison.RouteCols`, the object the residual
comparison consumes) had never been linked: `mem_bobCols_iff_routeCols` and
`mem_aliceCols_iff_routeRows` prove they are two readings of the one frozen
rectangle of `09:1039--1044`, and `routeRows_of_mem_rowsAt` reads the row side off
a certificate's own rows at the node.

### STOP-AND-REPORT: the one input that is not derivable here

**What remains after both legs is exactly one datum, and it is not derivable from
the banked substrate: the reference-copy embedding at the node.**  Concretely,
`lambdaGE_le_cost_descend_of_bracket_member` needs

```text
hgame : interlaceFun G p a c = g (iotaA a) (iotaB c)
```

-- the statement that the ambient matrix the alleged protocol computes, read at
the selected rows and columns, **is** the `p`-fold interlace of `G`.  In the
frozen paper this is supplied by the construction: `09:107` builds
`U = <N>^q`, `09:113--116` cuts `G` out of `N` on the base reservoir, and
`09:121--123` (`eq:reference-all-columns`) records `Cols(G) = Cols(N)`, so the
`u_{kappa_v}` selected outer coordinates carry literal copies of `G`.  In the
Lean development that construction is present **only numerically**: the banked
`lem:wrapper-reference` enters every consumer as the binder
`hbase : C - 1 <= LambdaGE Gmat 1 xT (3/5)`, and a numeric `Lambda` bound cannot
produce an embedding of carriers.  There is no theorem, and no honest way to
manufacture one, that converts `hbase` into `hgame`.

So this tranche **stops there and reports it**, rather than assuming it: the
embedding enters as explicit named binders (`iotaA`, `iotaB`, `hgame`), never as
an `axiom`, never as a premise bundle, and never as an opaque certificate.  The
successor obligation is named `SELECT-EMBED-001` in the module summary below:
build the reference-copy embedding of `<G>^{u_kappa}` into `U` at a first-Bob
node from `09:105--123`, at which point `hselect` becomes unconditional.  What
*is* achieved is a strict narrowing: `hselect` was an assumption about the
alleged protocol's residual **cost**; what is left is a statement about the
**construction**, with the cost side and the density side both proved.

### DEFINED-vs-FREE, and the `vartheta` twin

* `y` is **DEFINED**: `09:436` prints `rho = 2y^2 = 18/25`, and the banked
  `FirstBobLightDichotomy.wrapper_y_is_pinned_by_rho` proves `3/5` is its only
  nonnegative solution.  Every occurrence of `3/5` and `9/25` below is an
  evaluation of that chain, never a chosen numeral; `rhoSmall` and
  `rhoSmall_eq_two_y_sq` are consumed by pin and restated nowhere.
* `u_kappa` is **DEFINED** by `09:438` (`u_2 = 2`) and `09:440`
  (`u_kappa = kappa/2 + 1`), reified as the banked
  `WrapperProjectionCovers.smallCopyWidth`; `kappa_v` is **DEFINED** by
  `09:1255`, reified as the banked `TranscriptLevelConstruction.kappaAt`; `A_0`
  by `09:1219`, reified as the banked `initialRefRows`.  None is re-reified here.
* **The `vartheta` twin, named at every use.**  Two declarations spell
  `vartheta`: `DenseWrapperFrontier.vartheta` and `ParameterSchedule.vartheta`.
  This module `open`s **`DenseWrapperFrontier`** and not `ParameterSchedule`, so
  every occurrence of `vartheta` below -- it occurs only in the two re-fired
  dichotomy statements of section 5, inherited verbatim from
  `FirstBobLightDichotomy` -- is `DenseWrapperFrontier.vartheta`, the `9/16` of
  `09:1268`.  No declaration of this module defines, restates or evaluates
  either twin.

## Reader counterpart: NONE claimable, re-verified first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was searched again this round
for `projection`, `denser`, `Bob child`, `represented` and `exceptional`.  The
hits are: `02-preliminaries.tex:119--140` (`prop:paper-projection-facts`, the
*inherited* bracket projection/monotonicity facts, already the property of the
inherited-contract modules and about `CC` of bracket families, not about a
protocol node); `05-iteration.tex:61--73` (the rank argument inside the
iteration's power-of-two lower bound, a different mechanism at a different
stage); `B-bridge-details.tex:146` and `:163` ("If Bob speaks, keep a denser
child", "the denser child has ...") which are the *bridge* induction's denser
child, not the wrapper frontier's; and `C-effectivity-details.tex:74`
("represented" of encoded indices).  None states `09:1287--1296`.  The reader
artifact contains no statement of the projection-at-a-node step and no statement
of a `Lambda`-to-subtree-cost comparison, so **no declaration of this module
claims a reader counterpart**, and the absence is recorded once, here.

## Canonical inhabitation

This module defines exactly one `def` (`blockRows`, a finite row-block union) and
**no `structure` and no `inductive`**, so it opens no new canonical-inhabitation
obligation of its own.  `blockRows` is instantiated at a nondegenerate legal
tuple in section 6 (`blockRows_bracket_member_is_inhabited`), and that instance
is labelled **NON-FIDELITY / BEYOND-PAPER**: the paper's own instance of the
bracket member at a first-Bob node is a function of the **alleged** protocol of
`09:1188--1194`, whose non-existence is the conclusion of the whole argument, so
there is no paper object to exhibit.  The inherited deferred canonical-inhabitation
registration is therefore carried unchanged, and nothing below discharges it.

## Residues this module does NOT close (named, not implied)

* **`SELECT-EMBED-001`, the reference-copy embedding**, is the documented STOP
  above.  Until it lands, `hselect` is *narrowed*, not removed: sections 4 and 5
  carry `iotaA`, `iotaB` and `hgame` as explicit binders.
* **`L1-F6`** (retire the redundant `hone` binder of `WrapperDenseFrontierWiring`,
  an *extra* hypothesis relative to `09:1291--1296`) is **carried, unedited**; it
  is an edit to another module and therefore its own tranche.  It reappears below
  only where the re-fired schedule-indexed dichotomy inherits it verbatim.
* **`L1-F7`** (the docstring of `TranscriptLevelSuccessors` attributes `m_G` to
  `09:1270`, which defines nothing; the correct anchor is `09:113--116`) is
  **carried, unedited**, as a record-only repair of that module.  This module
  cites `09:113--116` for `m_G` and `G` throughout, which is the correct anchor.
* `hLocEx` (branch (i)'s certified-scale endpoint `A:109--146`, the place
  `EXPANDER-001` would enter) is untouched and is inherited as a named binder by
  the re-fired dichotomies; `EXPANDER-001` occurs in no hypothesis here.
* `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-u-dense` is not approached; `hDenseRung` is neither discharged nor
  fed; `thm:first-wrapper` is **not** proved; **no route completion is claimed,
  and none may be inferred.**
* `TranscriptLevelJoin.select_bound_mono` stays **unwired**, as in the
  predecessor: nothing here weakens a budget.

## Unwired census of this module's own declarations

Of the twenty-eight declarations below (one `def`, twenty-seven theorems),
fifteen are consumed by another proof term here; the thirteen that are not are
endpoints by design rather than oversight:

* `projection_at_a_node` (leg (1)), `nodeProjection_transport_density` (the join),
  `hselect_of_trims_and_projection` (the second entry point of the discharge), and
  the two re-fired dichotomies of section 5 are **deliverables**.  Their consumers
  are the assembly of `thm:first-wrapper` and, for the first three, a call site
  that must supply the equivalences of `SELECT-EMBED-001`; neither exists yet.
* `representedCoords_image_avoids_E0`, `mem_bobCols_iff_routeCols` and
  `routeRows_of_mem_rowsAt` are **hypothesis suppliers**: they produce `hout`,
  `hcol` and `hrow` at a call site, and are deliberately not wired into the
  discharge's term, which states those three as binders so that a consumer may
  supply them from whichever banked object it has.
* `blockRows_mono` is an aux-battery monotonicity check;
  `blockRows_bracket_member_is_inhabited`, `bridge_hypotheses_are_consistent`,
  `bracket_column_clause_is_not_free` and `equipartition_clause_is_not_free` are
  measurement endpoints (**NON-FIDELITY / BEYOND-PAPER**), consumed by nothing by
  construction.

## Axioms and imports

The sole import is `FirstBobLightDichotomy`, whose transitive closure carries
every banked module consumed below.  `LegacyNPCC.Stage12` is **not** in that
closure, so the cited AGHP balanced-family axiom is unreachable from every
declaration here.  No `axiom`, no opaque certificate, no premise bundle; the
external interfaces consumed (`Dfamily_le_member`, `D_le_cost_descend_of_computes`,
`denserBobChild_retains_y_sq`, `nodeProjection_of_isAlicePath`,
`rhoSmall_eq_two_y_sq`, `smallCopyWidth`) are all proved declarations reached by
pin.

`#print axioms` was run on **all twenty-eight** declarations (they are added to
`tools/AxiomAudit.lean` in this tranche): **twenty-three** depend only on
`[propext, Classical.choice, Quot.sound]`, and the remaining **five** --
`mem_bobConstraint_iff`, `mem_aliceConstraint_iff`, `mem_bobCols_iff_routeCols`,
`mem_aliceCols_iff_routeRows` and `routeRows_of_mem_rowsAt` -- depend only on
`[propext, Quot.sound]`.  Zero `sorryAx`, zero project axioms, and zero
occurrences of `NPCC.aghp_balanced_family_exists`.
-/

namespace EthInapproximability.ParameterizedNP.SelectDischarge

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction

/-! ## §1  Leg (1): the projection-at-a-node lemma (`09:1287--1290`)

Everything in this section is **general**: in the outer alphabet, in `q`, in the
protocol, in the routed system, in the node, and in the cover data. -/

section Projection

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **Aux P1 (the cover clause, contrapositive).**

`09:442--445` supplies, for each dyadic capacity, a cover that *meets every poor
`u`-set*.  A `u`-set that meets the cover nowhere is therefore not poor, i.e. its
projection density is at least `rho`.  This is the one counting step the frozen
sentence `09:1287--1289` performs, isolated: it is inlined at two banked call
sites (`WrapperProtectedEarly.exists_dense_uset_in_class` and
`WrapperDenseFrontierWiring.exists_dense_donor_subset`), both of which *find* their
`u`-set by a counting argument, whereas `09:1287` *selects* it from the represented
coordinates.  General in `rho`, `S`, the cover, the selection and `u`. -/
theorem notPoor_of_avoids_cover {ρ : ℝ} {S : Finset (Fin q → Yc)} {E J : Finset (Fin q)}
    {u : ℕ}
    (hmeet : ∀ K : Finset (Fin q), K.card = u → PoorProjection ρ K S → (E ∩ K).Nonempty)
    (hJ : J.card = u) (hout : ∀ i ∈ J, i ∉ E) :
    ρ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((projSet J S).card : ℝ) := by
  have hnot : ¬ PoorProjection ρ J S := by
    intro hpoor
    obtain ⟨i, hi⟩ := hmeet J hJ hpoor
    rw [Finset.mem_inter] at hi
    exact hout i hi.2 hi.1
  exact not_lt.mp hnot

omit [Fintype Yc] [DecidableEq Yc] in
/-- **`09:1287`, "Every represented coordinate is outside `E_0`", derived.**

The frozen sentence is *not* an assumption about the frontier: it is a
consequence of the start rule `09:1235--1236`, "Start one clean reference
certificate in every coordinate outside `E_0`".  In the Lean model the started
coordinates are exactly the elements of `Coord`, addressed in `[q]` by the
placement `idx`, so the start rule is the binder `hstart`, and the frozen
sentence is its image along `idx`.  Carrying `hstart` explicitly rather than
identifying `Coord` with `[q] \ E_0` keeps the frozen exclusion visible instead of
hiding it in a carrier.  General. -/
theorem representedCoords_image_avoids_E0 {X Z : Type*} [Fintype X] [DecidableEq X]
    {Coord : Type} [Fintype Coord]
    {P : Protocol X (Fin q → Yc) Z} {R : Coord → Finset X} {A0 r : ℕ}
    (v : FrontierNode P R A0 r) {E0 : Finset (Fin q)} (idx : Coord → Fin q)
    (hstart : ∀ i : Coord, idx i ∉ E0) :
    ∀ i ∈ (representedCoords P R A0 r v).image idx, i ∉ E0 := by
  intro i hi
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
  exact hj ▸ hstart j

/-- **`09:1287--1289`, the parent half of the projection-at-a-node lemma.**

"Every represented coordinate is outside `E_0`, so the parent projection to any
selected `u_{kappa_v}` of them has density at least `rho = 2y^2`."

Two frozen facts make the *root* cover of `09:442--445` usable at a *node*, and
both are consumed by pin: a frontier address is Alice-only
(`RoutedSystem.node_isAlicePath`, from `09:1250--1252`), and along an Alice-only
route the node's column projection is literally the ambient one
(`RoutingDynamics.nodeProjection_of_isAlicePath`, `09:1330--1331`).  So no density
is lost between the root, where `E_0` is built, and the first-Bob node, where the
selection is made -- which is exactly why the frozen argument may cite a cover
built once at `09:404--453`.

*Why this is not vacuous.*  The conclusion is an inequality on a real density,
and it fails without `hout`: a `u`-set meeting the cover may be poor, which is
what `PoorProjection` says and what the cover's existence is for.

General in the routed system, the node, the ambient retained set `S`, the
exceptional set, the selection, and the dyadic index. -/
theorem parent_projection_dense_at_frontier_node {X Z : Type*}
    {Coord ι V : Type*} {P : Protocol X (Fin q → Yc) Z} {r A0 : ℕ}
    (Sys : RoutedSystem P Coord ι V r A0) (v : V)
    (S : Finset (Fin q → Yc)) {E0 J : Finset (Fin q)} {l k : ℕ}
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (hl : l ∈ Finset.Ico 1 k) (hJ : J.card = smallCopyWidth (2 ^ l))
    (hout : ∀ i ∈ J, i ∉ E0) :
    rhoSmall * (Fintype.card Yc : ℝ) ^ J.card
      ≤ ((nodeProjection P S J (Sys.node v)).card : ℝ) := by
  have halice : IsAlicePath P (Sys.node v) := Sys.node_isAlicePath v
  rw [nodeProjection_of_isAlicePath (S := S) (J := J) halice]
  exact notPoor_of_avoids_cover (hcover l hl) hJ hout

/-- **`09:1287--1290`, the projection-at-a-node lemma, complete.**

"Every represented coordinate is outside `E_0`, so the parent projection to any
selected `u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob
child retains density at least `y^2`."

The parent half is the previous theorem; the child half is the banked
`RoutingDynamics.denserBobChild_retains_y_sq`, consumed by pin at the **DEFINED**
value `y = 3/5` of `09:436` -- the substitution `rho = 2y^2` in, `y^2` out, with
`WrapperProjectionCovers.rhoSmall_eq_two_y_sq` supplying the evaluation and
nothing restated.

*Why the trivial witness fails.*  The deliverable is existential in the child
bit, and no fixed bit works: the banked
`RoutingDynamics.projection_denserChild_needs_the_right_bit` exhibits a Bob query
whose predicate sends every column to the `true` child, so the bound at `false`
fails outright.  The frozen "*the* denser Bob child" names a genuine choice.

General in everything the previous theorem is general in, plus the Bob query. -/
theorem projection_at_a_node {X Z : Type*}
    {Coord ι V : Type*} {P : Protocol X (Fin q → Yc) Z} {r A0 : ℕ}
    (Sys : RoutedSystem P Coord ι V r A0) (v : V)
    (S : Finset (Fin q → Yc)) {E0 J : Finset (Fin q)} {l k : ℕ}
    (hbob : IsBobNode (descend P (Sys.node v)))
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (hl : l ∈ Finset.Ico 1 k) (hJ : J.card = smallCopyWidth (2 ^ l))
    (hout : ∀ i ∈ J, i ∉ E0) :
    ∃ b : Bool, ((3 : ℝ) / 5) ^ 2 * (Fintype.card Yc : ℝ) ^ J.card
      ≤ ((nodeProjection P S J (Sys.node v ++ [b])).card : ℝ) := by
  have hpar := parent_projection_dense_at_frontier_node Sys v S hcover hl hJ hout
  refine denserBobChild_retains_y_sq (y := (3 : ℝ) / 5) hbob S J ?_
  have hval : (2 : ℝ) * ((3 : ℝ) / 5) ^ 2 = rhoSmall := rhoSmall_eq_two_y_sq
  rw [hval]
  exact hpar

end Projection

/-! ## §2  The rectangle glue, and leg (2): the `LambdaGE`-to-subtree-cost bridge

The node's column set (`RoutedCertificateSystem.bobCols`, the object leg (1)
projects) and the routing predicate (`TerminalResidualComparison.RouteCols`, the
object leg (2)'s residual comparison consumes) are two banked readings of one
frozen rectangle (`09:1039--1044`).  Nothing linked them; the two membership
lemmas below do, and they are what lets leg (1)'s output feed leg (2)'s
hypothesis. -/

section Glue

/-- **Aux G1.**  One step of Bob's cut, as a predicate.  General. -/
theorem mem_bobConstraint_iff {X Y Z : Type*} [Fintype Y]
    (P : Protocol X Y Z) (b : Bool) (y : Y) :
    y ∈ bobConstraint P b ↔ bobStepConsistent P b y := by
  cases P <;> simp [bobConstraint, bobStepConsistent]

/-- **Aux G2.**  One step of Alice's cut, as a predicate.  General. -/
theorem mem_aliceConstraint_iff {X Y Z : Type*} [Fintype X]
    (P : Protocol X Y Z) (b : Bool) (x : X) :
    x ∈ aliceConstraint P b ↔ aliceStepConsistent P b x := by
  cases P <;> simp [aliceConstraint, aliceStepConsistent]

/-- **The column half of the rectangle, in its two banked readings.**

`bobCols P p` is the node's column *set* (`09:1287--1290`'s projection target);
`RouteCols P p y` is the node's column *predicate* (the residual comparison's
hypothesis).  They agree.  General in the carriers, the protocol and the
address. -/
theorem mem_bobCols_iff_routeCols {X Y Z : Type*} [Fintype Y] [DecidableEq Y] :
    ∀ (P : Protocol X Y Z) (p : List Bool) (y : Y), y ∈ bobCols P p ↔ RouteCols P p y := by
  intro P p
  induction p generalizing P with
  | nil => intro y; simp [RouteCols]
  | cons b p ih =>
      intro y
      rw [bobCols_cons, Finset.mem_inter, mem_bobConstraint_iff, routeCols_cons,
        ih (descendStep P b) y]

/-- **The row half of the rectangle, in its two banked readings.**  The dual of
`mem_bobCols_iff_routeCols`; `RoutingDynamics.rowsAt` cuts a certificate's
reference rows by exactly this set, so a certificate's rows at a node are rows
that reach the node.  General. -/
theorem mem_aliceCols_iff_routeRows {X Y Z : Type*} [Fintype X] [DecidableEq X] :
    ∀ (P : Protocol X Y Z) (p : List Bool) (x : X), x ∈ aliceCols P p ↔ RouteRows P p x := by
  intro P p
  induction p generalizing P with
  | nil => intro x; simp [RouteRows]
  | cons b p ih =>
      intro x
      rw [aliceCols_cons, Finset.mem_inter, mem_aliceConstraint_iff, routeRows_cons,
        ih (descendStep P b) x]

/-- **Aux G3 (the form the certificate rows are supplied in).**  A row a
certificate holds at a node reaches that node: `rowsAt` is the reference rows cut
by `aliceCols`, and `aliceCols` is the routing predicate.  General. -/
theorem routeRows_of_mem_rowsAt {X Y Z : Type*} [Fintype X] [DecidableEq X]
    {P : Protocol X Y Z} {R : Finset X} {p : List Bool} {x : X}
    (h : x ∈ rowsAt P R p) : RouteRows P p x :=
  (mem_aliceCols_iff_routeRows P p x).mp (Finset.mem_inter.mp h).2

end Glue

section Bridge

/-- **Leg (2): the `LambdaGE`-to-subtree-cost bridge.**

Let `P` be the alleged protocol of `09:1188--1194`, computing the ambient game
`g`, and let `p` address a node of it.  Suppose the `p`-fold interlace of `G`
appears at that node: a bracket member `(Rset, Cset)` of `<G, pc, x, y>` together
with sections `iotaA`, `iotaB` of the ambient carriers whose images reach the
node, on which the interlace agrees with `g`.  Then

```text
Lambda_G(pc, x, y) <= cost(subtree at p).
```

This is the comparison the frozen `09:1305--1306` performs -- "The selected Bob
child therefore has complexity at least `C + log_2 kappa_v - 1`" -- with the
ladder's output quantity on the left; the ladder itself
(`lem:certified-row-ladder`, `A:150--160`) is *not* re-derived here and enters
only at the call sites through the banked
`TerminalTwoStream.certifiedRowLadder_of_base`.

The proof is three pins and no new mathematics: `LambdaGE` is a minimum whose
first rung is the family complexity (`min_le_left`); a family complexity is an
infimum, hence at most the complexity of any member
(`EthBridge.Dfamily_le_member`); and a node's local game costs at most the node's
residual subtree (`TerminalResidualComparison.D_le_cost_descend_of_computes`).

**STOP-AND-REPORT.**  `hgame` is the reference-copy embedding named
`SELECT-EMBED-001` in the module header: it is supplied by `09:105--123` in the
frozen construction and is **not derivable** from the numeric binder `hbase` the
Lean development carries for `lem:wrapper-reference`.  It is an explicit named
binder here, never an `axiom`.

*Why this is not vacuous.*  The conclusion is a `<=` between two named
quantities, so there is nothing to witness trivially; and it is false without the
routing hypotheses -- the banked
`TerminalResidualComparison.residual_needs_the_rectangle` exhibits a protocol, an
address and a game where the local complexity is `1` while the suffix depth is
`0`.

General in all four carriers, in the protocol, the address, the copy count and
both real parameters. -/
theorem lambdaGE_le_cost_descend_of_bracket_member {X Y : Type*} {Rw Cl : Type*}
    [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool) {P : Protocol X Y Bool}
    {g : X → Y → Bool} (hcomp : Protocol.Computes P g) (p : List Bool) {pc : ℕ} {x y : ℝ}
    (Rset : Finset (Fin pc × Rw)) (Cset : Finset (Fin pc → Cl))
    (hmem : (Rset, Cset) ∈ bracketGE Rw Cl pc x y)
    (iotaA : {a // a ∈ Rset} → X) (iotaB : {c // c ∈ Cset} → Y)
    (hrow : ∀ a, RouteRows P p (iotaA a)) (hcol : ∀ c, RouteCols P p (iotaB c))
    (hgame : ∀ a c, interlaceFun Gmat pc a.1 c.1 = g (iotaA a) (iotaB c)) :
    LambdaGE Gmat pc x y ≤ (descend P p).cost := by
  have hfam : Dfamily (interlaceFun Gmat pc) (bracketGE Rw Cl pc x y)
      ≤ D (subgame (interlaceFun Gmat pc) Rset Cset) :=
    EthBridge.Dfamily_le_member (interlaceFun Gmat pc) (bracketGE Rw Cl pc x y)
      (Rset, Cset) hmem
  have hres : D (subgame (interlaceFun Gmat pc) Rset Cset) ≤ (descend P p).cost :=
    D_le_cost_descend_of_computes hcomp iotaA iotaB hrow hcol (fun a c => hgame a c)
  have hmin : LambdaGE Gmat pc x y
      ≤ Dfamily (interlaceFun Gmat pc) (bracketGE Rw Cl pc x y) := by
    unfold LambdaGE
    exact min_le_left _ _
  omega

end Bridge

/-! ## §3  The bracket member at the paper's own quantities (`09:1291--1296`)

"Each selected certificate has at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
m_G` reference rows, so trim it to the row density `kappa_v x_T`."

The frozen trim supplies one row block per *selected coordinate*, and leg (1)
supplies the column density.  This section turns those two supplies into a member
of the frozen bracket family `def:bracket`, consumed through the vendored
`NPCC.bracketGE`. -/

section Member

variable {Rw : Type*} [DecidableEq Rw] {pc : ℕ}

/-- **`09:1291--1296`, the row side as an interlace row set.**

The union, over the `pc` selected coordinates, of that coordinate's trimmed
reference rows, tagged by the coordinate.  This is the only `def` of the module:
it carries a row block per copy and **no** floor, density or complexity claim --
all of those are frozen consequences and stay out of constructor data (mechanical
rules M1--M10). -/
def blockRows (B : Fin pc → Finset Rw) : Finset (Fin pc × Rw) :=
  Finset.univ.biUnion fun j => (B j).image fun a => (j, a)

/-- **Aux M1a (the membership readout).**  A tagged pair lies in the row set
exactly when its second component lies in the block its tag names.  General. -/
theorem mem_blockRows (B : Fin pc → Finset Rw) (p : Fin pc × Rw) :
    p ∈ blockRows B ↔ p.2 ∈ B p.1 := by
  obtain ⟨i, a⟩ := p
  simp only [blockRows, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨j, a', ha', hj, ha⟩
    subst hj
    subst ha
    exact ha'
  · intro h
    exact ⟨i, a, h, rfl, rfl⟩

/-- **Aux M1b (the fibre readout).**  The fibre of `blockRows B` over the copy `j`
is that copy's own block, tagged.  General. -/
theorem blockRows_fibre (B : Fin pc → Finset Rw) (j : Fin pc) :
    (blockRows B).filter (fun p => p.1 = j) = (B j).image fun a => (j, a) := by
  ext p
  obtain ⟨i, a⟩ := p
  constructor
  · intro h
    rw [Finset.mem_filter] at h
    obtain ⟨h1, h2⟩ := h
    simp only at h2
    subst h2
    exact Finset.mem_image.mpr ⟨a, (mem_blockRows B (i, a)).mp h1, rfl⟩
  · intro h
    obtain ⟨a', ha', hp⟩ := Finset.mem_image.mp h
    rw [← hp]
    exact Finset.mem_filter.mpr ⟨(mem_blockRows B (j, a')).mpr ha', rfl⟩

/-- **Aux M2 (the fibre count).**  Tagging is injective, so the fibre has exactly
the block's cardinality.  General. -/
theorem card_blockRows_fibre (B : Fin pc → Finset Rw) (j : Fin pc) :
    ((blockRows B).filter (fun p => p.1 = j)).card = (B j).card := by
  rw [blockRows_fibre]
  exact Finset.card_image_of_injective _ (fun a a' h => by simpa using h)

/-- **`def:equipartition` at the frozen trim.**  A row set built from per-copy
blocks is `([pc], T)`-equipartitioned as soon as every block meets the floor `T`
-- which is what `09:1291--1296` provides, one trim per selected certificate.
General in the floor. -/
theorem isEquipartitionedGE_blockRows {T : ℕ} (B : Fin pc → Finset Rw)
    (hB : ∀ j, T ≤ (B j).card) :
    IsEquipartitionedGE (blockRows B) (Finset.univ : Finset (Fin pc)) T := by
  intro j _
  rw [card_blockRows_fibre]
  exact hB j

/-- **Leg (1)'s output, in the bracket family's own units.**

Leg (1) delivers a *real* density, `y . |Cl|^{pc} <= |Cset|`; `def:bracket`
demands the *ceiling* clause `ceil(|Cl|^{pc} . y) <= |Cset|`.  They are the same
statement, because the right-hand side is a natural number.  This is the join
between the two legs, and it is where the identity `u_{kappa_v} = 2^{ell_v-1}+1 =
pc` of `09:436` and `09:1297--1300` does its work: the selected coordinate set and
the interlace copy set have the same width, so leg (1)'s denominator
`|Yc|^{|J|}` is the bracket's `|Cl|^{pc}`.  General. -/
theorem bracket_column_clause_of_projection_density {Cl : Type*} [Fintype Cl] {y : ℝ}
    {Cset : Finset (Fin pc → Cl)}
    (hC : y * (Fintype.card Cl : ℝ) ^ pc ≤ (Cset.card : ℝ)) :
    ⌈((Fintype.card Cl : ℝ) ^ pc) * y⌉₊ ≤ Cset.card :=
  Nat.ceil_le.mpr (by linarith [hC])

/-- **`def:bracket` at the paper's own two supplies.**

The member of `<G, pc, x, y>` whose rows are `09:1291--1296`'s per-certificate
trims and whose columns are leg (1)'s dense projection.  Nothing here is chosen:
both clauses are the frozen definition's, and both inputs are frozen outputs.

*Why the trivial witness fails.*  The empty column set is excluded outright: at
`Cset = empty` the hypothesis forces `y . |Cl|^{pc} <= 0`, which the frozen
`y = 3/5 > 0` and a nonempty column alphabet refute.  The empty row family is
excluded by the floor whenever the floor is positive, which
`09:1291--1296`'s `A_{ell_v} >= 2 kappa_v x_T m_G` makes it.

General in the carriers, the copy count and both real parameters. -/
theorem bracketMember_of_blocks_and_columns {Cl : Type*} [Fintype Rw] [Fintype Cl] {x y : ℝ}
    (B : Fin pc → Finset Rw) (Cset : Finset (Fin pc → Cl))
    (hB : ∀ j, ⌈(Fintype.card Rw : ℝ) * x⌉₊ ≤ (B j).card)
    (hC : y * (Fintype.card Cl : ℝ) ^ pc ≤ (Cset.card : ℝ)) :
    (blockRows B, Cset) ∈ bracketGE Rw Cl pc x y :=
  ⟨isEquipartitionedGE_blockRows B hB, bracket_column_clause_of_projection_density hC⟩

end Member

/-! ### §3b  The join: leg (1)'s node projection carried to the bracket's column type

Leg (1) delivers a dense set of *outer* tuples restricted to the selected
coordinates, `projSet J (retained columns at the child)`, a `Finset (J -> Yc)`.
`def:bracket` wants a `Finset (Fin pc -> Cl)`.  The frozen construction makes the
two the same object: `09:438--440` fixes the selected width at `u_{kappa_v}`, and
the copy count is `2^{ell_v-1}+1` -- the interlace parameter of **`A:158`**
(`\LambdaThree{M}{2^{\ell-1}+1}{2^\ell x}{z^2}`), at the `ell = ell_v` fixed by
`09:1297--1300`.  The two are equal at `kappa_v = 2^{ell_v}`, which is the
identity `u_kappa = 2^{ell-1}+1` asserted at `09:445--447`; and `09:121--123`
(`eq:reference-all-columns`, `Cols(G) = Cols(N)`) says the reference copies use
the ambient outer alphabet.  Those two identifications are the equivalences
`eIdx` and `eCol` below -- part of the construction, hence part of the documented
STOP `SELECT-EMBED-001`, and carried as explicit binders.  What is *proved* here
is that once they are given, the density transports with no loss: leg (1)'s
estimate **is** the bracket's column clause. -/

section Join

/-- **The column clause of `def:bracket`, supplied by leg (1).**

Transporting `projSet J S'` along `eIdx` and `eCol` is injective, so it preserves
cardinality, and the two density denominators agree
(`|Cl|^{pc} = |Yc|^{|J|}` because the equivalences are bijections).  Hence a node
projection of density at least `y` becomes a bracket column set of density at
least `y`.

**This is where the two legs meet**: with
`bracket_column_clause_of_projection_density` after it, and
`projection_at_a_node` before it, the whole column side of `hmem` is a frozen
output rather than an assumption.

General in the alphabets, in `q`, in the node, in the selection and in `y`. -/
theorem nodeProjection_transport_density {Yc : Type*} [Fintype Yc] [DecidableEq Yc]
    {q : ℕ} {X Z : Type*} {Cl : Type*} [Fintype Cl] [DecidableEq Cl] {pc : ℕ}
    {P : Protocol X (Fin q → Yc) Z} {S : Finset (Fin q → Yc)} {J : Finset (Fin q)}
    {p : List Bool} {y : ℝ} (eIdx : Fin pc ≃ {i // i ∈ J}) (eCol : Cl ≃ Yc)
    (hdens : y * (Fintype.card Yc : ℝ) ^ J.card
      ≤ ((nodeProjection P S J p).card : ℝ)) :
    y * (Fintype.card Cl : ℝ) ^ pc
      ≤ (((nodeProjection P S J p).image
          fun f => fun j : Fin pc => eCol.symm (f (eIdx j))).card : ℝ) := by
  classical
  have hinj : Function.Injective
      (fun f : {i // i ∈ J} → Yc => fun j : Fin pc => eCol.symm (f (eIdx j))) := by
    intro f₁ f₂ hf
    funext i
    have hj := congrFun hf (eIdx.symm i)
    simp only [Equiv.apply_symm_apply] at hj
    exact eCol.symm.injective hj
  have hcard : ((nodeProjection P S J p).image
      fun f => fun j : Fin pc => eCol.symm (f (eIdx j))).card
      = (nodeProjection P S J p).card :=
    Finset.card_image_of_injective _ hinj
  have hJ : J.card = pc := by
    have h1 : Fintype.card {i // i ∈ J} = J.card := Fintype.card_coe J
    have h2 : Fintype.card (Fin pc) = Fintype.card {i // i ∈ J} := Fintype.card_congr eIdx
    simp only [Fintype.card_fin] at h2
    omega
  have hAlph : Fintype.card Cl = Fintype.card Yc := Fintype.card_congr eCol
  rw [hcard, hAlph, ← hJ]
  exact hdens

end Join

/-! ## §4  The discharge (`09:1287--1306`)

`hselect` proved, from the two legs plus the one documented residual datum. -/

section Discharge

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} {Coord : Type} [Fintype Coord]

/-- **`hselect` discharged from a node-localized bracket member.**

This is the exact statement carried as the binder `hselect` through
`SplitFirstBobInstance`, `LargeCapacityBranch`, `TranscriptLevelJoin` and
`FirstBobLightDichotomy`, **proved** -- with the copy count, the row density and
the column density at the paper's own values: `pc = 2^{ell_v-1}+1` from `A:158`
at the `ell = ell_v` of `09:1297--1300`, `x = kappa_v x_T` from `09:1296`, and
`y = (3/5)^2` from `09:436`'s DEFINED `y`.

**Where each hypothesis comes from, and what remains.**

* `hmem` is `09:1291--1296` (rows) joined with `09:1287--1290` (columns): section
  3's `bracketMember_of_blocks_and_columns` builds it from the frozen trims and
  leg (1)'s density, so neither clause is assumed here.
* `hrow` and `hcol` are the routing readings of the node's rectangle: section 2's
  `routeRows_of_mem_rowsAt` supplies the first from a certificate's own rows at
  the node, and `mem_bobCols_iff_routeCols` the second from the node's column set
  -- the very set leg (1) projects.
* `hgame` is the **documented STOP**, `SELECT-EMBED-001`: the reference copies of
  `G` sitting at the selected outer coordinates (`09:105--123`).  It is an
  explicit named binder.

**On the antecedent.**  `hselect`'s antecedent is `09:1283`'s count,
`u_{kappa_v} <= |represented coordinates|`.  Its frozen role is to license the
*selection* of `u_{kappa_v}` represented coordinates, and it is therefore consumed
in leg (1) -- it is what produces the set `J` whose projection density feeds
`hmem`.  It is not consumed a second time by the bridge, which is why it is
discarded here; the statement keeps it because `hselect`'s shape is fixed by its
consumers and this theorem must match it byte for byte.

General in the carriers, the coordinate type, the protocol, the reference rows,
`A_0`, `r`, the node, the child bit and `x_T`. -/
theorem hselect_of_localized_reference_copies {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Bool} {g : X → Y → Bool}
    (hcomp : Protocol.Computes P g) {R : Coord → Finset X} {A0 r : ℕ}
    (v : FrontierNode P R A0 r) (b : Bool) {xT : ℝ}
    (Rset : Finset (Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) × Rw))
    (Cset : Finset (Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) → Cl))
    (hmem : (Rset, Cset) ∈ bracketGE Rw Cl (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
      (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) ((3 / 5 : ℝ) ^ 2))
    (iotaA : {a // a ∈ Rset} → X) (iotaB : {c // c ∈ Cset} → Y)
    (hrow : ∀ a, RouteRows P (v.val ++ [b]) (iotaA a))
    (hcol : ∀ c, RouteCols P (v.val ++ [b]) (iotaB c))
    (hgame : ∀ a c,
      interlaceFun Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) a.1 c.1
        = g (iotaA a) (iotaB c)) :
    smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card →
      LambdaGE Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
          (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) ((3 / 5 : ℝ) ^ 2)
        ≤ (descend P (v.val ++ [b])).cost :=
  fun _ =>
    lambdaGE_le_cost_descend_of_bracket_member Gmat hcomp (v.val ++ [b]) Rset Cset hmem
      iotaA iotaB hrow hcol hgame

/-- **The same discharge, taken straight from the paper's two supplies.**

The previous theorem with `hmem` replaced by the frozen inputs it is built from:
`hB` is `09:1291--1296`'s per-certificate trim floor at the row density
`kappa_v x_T`, and `hC` is leg (1)'s output at `09:1290`'s `y^2`, in the real
density form `projection_at_a_node` delivers it.  So the only inputs that are not
frozen outputs are the three of the documented STOP.

General in everything the previous theorem is general in. -/
theorem hselect_of_trims_and_projection {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    [DecidableEq Rw] (Gmat : Rw → Cl → Bool) {P : Protocol X Y Bool} {g : X → Y → Bool}
    (hcomp : Protocol.Computes P g) {R : Coord → Finset X} {A0 r : ℕ}
    (v : FrontierNode P R A0 r) (b : Bool) {xT : ℝ}
    (B : Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) → Finset Rw)
    (Cset : Finset (Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) → Cl))
    (hB : ∀ j, ⌈(Fintype.card Rw : ℝ) * (((kappaAt P R A0 r v : ℕ) : ℝ) * xT)⌉₊ ≤ (B j).card)
    (hC : ((3 / 5 : ℝ) ^ 2) * (Fintype.card Cl : ℝ)
        ^ (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) ≤ (Cset.card : ℝ))
    (iotaA : {a // a ∈ blockRows B} → X) (iotaB : {c // c ∈ Cset} → Y)
    (hrow : ∀ a, RouteRows P (v.val ++ [b]) (iotaA a))
    (hcol : ∀ c, RouteCols P (v.val ++ [b]) (iotaB c))
    (hgame : ∀ a c,
      interlaceFun Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) a.1 c.1
        = g (iotaA a) (iotaB c)) :
    smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card →
      LambdaGE Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
          (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) ((3 / 5 : ℝ) ^ 2)
        ≤ (descend P (v.val ++ [b])).cost :=
  hselect_of_localized_reference_copies Gmat hcomp v b (blockRows B) Cset
    (bracketMember_of_blocks_and_columns B Cset hB hC) iotaA iotaB hrow hcol hgame

end Discharge

/-! ## §5  The two `cc-t5e` deliverables re-fired through the discharge

The predecessor's unwired census recorded that
`canonical_firstBobLight_dichotomy` and
`canonical_firstBobLight_dichotomy_at_paper_schedule` "have no consumer yet ...
until `hselect` is discharged by successor `L1-F8`".  This is that successor, and
the two statements are re-fired here with `hselect` replaced by the localization
datum -- **not** weakened in any other respect: every other binder, including
`hLocEx`, the two budget readings and (in the schedule-indexed form) the inherited
`hone` of the open `L1-F6`, is passed through verbatim.

`vartheta` in both conclusions is `DenseWrapperFrontier.vartheta` (the `9/16` of
`09:1268`), never `ParameterSchedule.vartheta`; the twin is named here once for
both statements, and neither is restated or evaluated. -/

section Refire

open EthInapproximability.ParameterizedNP.FirstBobLightDichotomy

variable {X Y : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`), the dichotomy with `hselect`
discharged.**

The predecessor's `canonical_firstBobLight_dichotomy` re-fired with its
`hselect` binder replaced by the localization datum of section 4.  Nothing else
changes: `hLocEx` (branch (i)'s certified-scale endpoint `A:109--146`, the place
`EXPANDER-001` would enter), both budget readings of `09:1306--1308`, and every
schedule binder are passed through verbatim, and the conclusion is the frozen
`W_v < vartheta kappa_v` -- `vartheta` here being
`DenseWrapperFrontier.vartheta`, the `9/16` of `09:1268`, never
`ParameterSchedule.vartheta`.

The ambient output type is `Bool` because the alleged protocol of
`09:1188--1194` computes a Boolean matrix; the predecessor is general in that
output type, so this is a specialization to the frozen setting and not a
weakening.

**What is genuinely better than the predecessor.**  `hselect` was an assumption
about the alleged protocol's residual *cost*.  What replaces it -- `hmem`,
`iotaA`, `iotaB`, `hrow`, `hcol`, `hgame` -- is a statement about the
*construction*, of which the quantitative halves (`hmem`'s two clauses, and the
routing of the images) are frozen outputs proved in sections 1--3; only the
identification `hgame` remains, and it is the documented STOP
`SELECT-EMBED-001`.

*Why no full-bundle pole is fired here.*  The predecessor established that none
is available, and why: `hk : 4 <= k_ref` with `hq4 : k_ref + 2 <= r` forces
`6 <= r`, so the smallest firable instance has `r = 6` and hence `k_ref = 4`, and
at `k_ref = 4` branch (i)'s `hE2` is false outright for every `theta <= 1`
(`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`).
A `False` derived at any decidable instance would therefore measure `hE2` rather
than this statement.  This tranche adds only the localization datum, whose own
satisfiability is checked separately in section 6 by
`bridge_hypotheses_are_consistent`, so the inherited obstruction is unchanged and
**no pole is landed**.

General in the carriers, the coordinate type, the node, and every schedule
parameter. -/
theorem canonical_firstBobLight_dichotomy_of_localized_copies {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Gmat : Rw → Cl → Bool) {P : Protocol X Y Bool} {g : X → Y → Bool}
    {R : Coord → Finset X} {A0 r : ℕ}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k tcert : ℕ} {xT θ colDens : ℝ} (b : Bool)
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw) (hCne : 1 ≤ Fintype.card Cl)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcolDens : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) →
      (C - 1) + (r - v.val.length) ≤ B)
    (Rset : Finset (Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) × Rw))
    (Cset : Finset (Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) → Cl))
    (hmem : (Rset, Cset) ∈ bracketGE Rw Cl (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
      (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) ((3 / 5 : ℝ) ^ 2))
    (iotaA : {a // a ∈ Rset} → X) (iotaB : {c // c ∈ Cset} → Y)
    (hrow : ∀ a, RouteRows P (v.val ++ [b]) (iotaA a))
    (hcolRoute : ∀ c, RouteCols P (v.val ++ [b]) (iotaB c))
    (hgame : ∀ a c,
      interlaceFun Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) a.1 c.1
        = g (iotaA a) (iotaB c)) :
    frontierWeight P R A0 r v < vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) :=
  canonical_firstBobLight_dichotomy Gmat hcomp hR b hv hC hk hq4 hxT0 hxT1 hθ0 hθ1 hGne hCne
    hgate hbase htcert hE1 hE2 hcolDens hbudget hcost hLocEx
    (hselect_of_localized_reference_copies Gmat halleged v b Rset Cset hmem iotaA iotaB
      hrow hcolRoute hgame)

/-- **The schedule-indexed dichotomy with `hselect` discharged.**

The second `cc-t5e` deliverable, re-fired the same way: `A_0` pinned to
`09:1219`'s `ceil(2 x_T m_G)` through the banked `initialRefRows`, the node on
coordinate `i`'s route, and the second conjunct `09:1291--1296` executed.

`hone` is inherited verbatim and **not** retired here: it is an *extra*
hypothesis relative to `09:1291--1296`, and retiring it is the open **`L1-F6`**,
an edit to `WrapperDenseFrontierWiring` and therefore its own tranche.

*Why the trivial witness fails.*  `T = empty` is refuted by the `Nonempty`
conjunct, exactly as in the predecessor; the light conjunct is refutable at the
banked `TranscriptLevelJoin.interiorAudit_is_not_light`.

General in the carriers, the coordinate type, the node, the coordinate, the
child bit and every schedule parameter. -/
theorem canonical_firstBobLight_dichotomy_at_paper_schedule_of_localized_copies
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool)
    {P : Protocol X Y Bool} {g : X → Y → Bool} {R : Coord → Finset X} {r : ℕ} {xT : ℝ}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ i, refRowFloor (initialRefRows xT (Fintype.card X)) r ≤ (R i).card)
    {v : FrontierNode P R (initialRefRows xT (Fintype.card X)) r}
    {C B k tcert : ℕ} {θ colDens : ℝ} (i : Coord) (b : Bool)
    (hp : v.val ∈ coordRoutes P R (initialRefRows xT (Fintype.card X)) r i)
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw) (hCne : 1 ≤ Fintype.card Cl)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcolDens : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hcost : P.cost ≤ C + r - 1)
    (hone : 1 ≤ ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
      * ((Fintype.card X : ℕ) : ℝ))
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R (initialRefRows xT (Fintype.card X)) r v).card : ℕ) : ℝ) →
      (C - 1) + (r - v.val.length) ≤ B)
    (Rset : Finset (Fin (2 ^ (Nat.log 2
        (kappaAt P R (initialRefRows xT (Fintype.card X)) r v) - 1) + 1) × Rw))
    (Cset : Finset (Fin (2 ^ (Nat.log 2
        (kappaAt P R (initialRefRows xT (Fintype.card X)) r v) - 1) + 1) → Cl))
    (hmem : (Rset, Cset) ∈ bracketGE Rw Cl
      (2 ^ (Nat.log 2 (kappaAt P R (initialRefRows xT (Fintype.card X)) r v) - 1) + 1)
      (((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT)
      ((3 / 5 : ℝ) ^ 2))
    (iotaA : {a // a ∈ Rset} → X) (iotaB : {c // c ∈ Cset} → Y)
    (hrow : ∀ a, RouteRows P (v.val ++ [b]) (iotaA a))
    (hcolRoute : ∀ c, RouteCols P (v.val ++ [b]) (iotaB c))
    (hgame : ∀ a c,
      interlaceFun Gmat
          (2 ^ (Nat.log 2 (kappaAt P R (initialRefRows xT (Fintype.card X)) r v) - 1) + 1)
          a.1 c.1
        = g (iotaA a) (iotaB c)) :
    frontierWeight P R (initialRefRows xT (Fintype.card X)) r v
        < vartheta
          * ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ)
      ∧ ∃ T ⊆ rowsAt P (R i) v.val,
          T.card = ⌈((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
              * ((Fintype.card X : ℕ) : ℝ)⌉₊
            ∧ T.Nonempty :=
  canonical_firstBobLight_dichotomy_at_paper_schedule Gmat hcomp hR i b hp hv hC hk hq4
    hxT0 hxT1 hθ0 hθ1 hGne hCne hgate hbase htcert hE1 hE2 hcolDens hbudget hcost hone hLocEx
    (hselect_of_localized_reference_copies Gmat halleged v b Rset Cset hmem iotaA iotaB
      hrow hcolRoute hgame)

end Refire

/-! ## §6  Aux-lemma battery, non-vacuity, and the statement poles

**NON-FIDELITY / BEYOND-PAPER** throughout this section: the paper's own bracket
member at a first-Bob node is a function of the **alleged** protocol of
`09:1188--1194`, so there is no paper instance to exhibit and nothing here
discharges the deferred canonical-inhabitation registration. -/

section Battery

/-- **Aux B1 (identity).**  A one-copy block family has exactly its block as row
set, up to the tag.  The round-trip check on `blockRows`: the construction adds
the copy index and nothing else.  General. -/
theorem card_blockRows {Rw : Type*} [DecidableEq Rw] {pc : ℕ} (B : Fin pc → Finset Rw) :
    (blockRows B).card = ∑ j : Fin pc, (B j).card := by
  classical
  rw [blockRows, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun j _ =>
      Finset.card_image_of_injective _ (fun a a' h => by simpa using h)
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨k, a⟩ hi hj
    obtain ⟨a₁, -, hk⟩ := Finset.mem_image.mp hi
    obtain ⟨a₂, -, hk'⟩ := Finset.mem_image.mp hj
    have hik : i = k := congrArg Prod.fst hk
    have hjk : j = k := congrArg Prod.fst hk'
    exact hij (hik.trans hjk.symm)

/-- **Aux B2 (monotonicity).**  Enlarging every block enlarges the row set.
General. -/
theorem blockRows_mono {Rw : Type*} [DecidableEq Rw] {pc : ℕ} {B B' : Fin pc → Finset Rw}
    (h : ∀ j, B j ⊆ B' j) : blockRows B ⊆ blockRows B' := by
  intro p hp
  simp only [blockRows, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image] at hp ⊢
  obtain ⟨j, a, ha, hpa⟩ := hp
  exact ⟨j, a, h j ha, hpa⟩

/-- **Aux B3 (non-vacuity of the assembled bracket member, LANE-GATE 3).**

`bracketMember_of_blocks_and_columns` would prove nothing if its conclusion were
only ever reachable at a degenerate tuple, and a green build cannot see the
difference.  Here it is fired at a tuple that is **nondegenerate on both sides**:
the row set has four rows spread over two copies, and the column set is nonempty.

**Which values are the paper's and which are not.**  The copy count `pc = 2` is
`09:438`'s own `u_2 = 2` at the smallest capacity a first-Bob node can have
(`09:1259`, "Every first-Bob node has `kappa_v >= 2`"), and the column density
`(3/5)^2` is `09:436`'s DEFINED `y^2`.  The carriers `Fin 2` and the row density
`1/2` are **BEYOND-PAPER AUDIT** values: the paper's `x = kappa_v x_T` is fixed by
a schedule whose `x_T` is far below anything a decidable instance can carry
(`eq:tref-search`, `06:558--571`), so no finite check can reach it.

**NON-FIDELITY.**  This is not the paper's instance and discharges nothing.  The
paper's own bracket member at a first-Bob node is a function of the **alleged**
protocol of `09:1188--1194`, whose non-existence is the conclusion of the whole
argument, so no paper instance exists to exhibit; the canonical-inhabitation
obligation stays REGISTERED and DEFERRED. -/
theorem blockRows_bracket_member_is_inhabited :
    ((blockRows fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))),
        (Finset.univ : Finset (Fin 2 → Fin 2)))
        ∈ bracketGE (Fin 2) (Fin 2) 2 (1 / 2) ((3 / 5 : ℝ) ^ 2)
      ∧ (blockRows fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))).card = 4
      ∧ (Finset.univ : Finset (Fin 2 → Fin 2)).Nonempty := by
  have hcols : (Finset.univ : Finset (Fin 2 → Fin 2)).card = 4 := by decide
  refine ⟨bracketMember_of_blocks_and_columns _ _ ?_ ?_, ?_, ?_⟩
  · intro j
    have hx : ((Fintype.card (Fin 2) : ℝ)) * (1 / 2 : ℝ) = 1 := by
      simp only [Fintype.card_fin]; norm_num
    rw [hx, Nat.ceil_one]
    simp
  · rw [hcols]
    simp only [Fintype.card_fin]
    norm_num
  · rw [card_blockRows]
    simp
  · exact Finset.univ_nonempty

/-- **Aux B4 (the bridge's hypothesis bundle is consistent, HYPOTHESIS-CONSISTENCY).**

A conditional theorem whose hypotheses cannot all hold at once proves nothing,
and a green build cannot see that either.  Leg (2) is fired here at a tuple where
**every** one of its hypotheses holds simultaneously -- an alleged protocol that
really computes its game, a genuine bracket member, sections whose images really
reach the addressed node, and a real interlace identification -- so the bundle is
satisfiable and the bridge is not vacuously true.

This is a **consistency** check and deliberately not a non-vacuity witness: at
this tuple both sides are `0`.  The operative constraint is proof availability,
not matrix constancy: `LambdaGE` is `Dfamily`-valued, hence an `sInf` over the
`bracketGE` family, and is `noncomputable` at **every** matrix, so no instance --
constant or not -- is reachable by kernel evaluation; a nonconstant one is
unbuilt here, not excluded in principle.  The bridge's *content* pole is the
banked `TerminalResidualComparison.residual_needs_the_rectangle`, which shows the
comparison fails without the routing hypotheses.

**NON-FIDELITY / BEYOND-PAPER AUDIT** in every value. -/
theorem bridge_hypotheses_are_consistent :
    LambdaGE (fun _ _ : Fin 1 => false) 1 1 1
      ≤ (descend (Protocol.leaf (X := Unit) (Y := Unit) false) []).cost := by
  have hceil : ⌈(1 : ℝ)⌉₊ = 1 := Nat.ceil_one
  refine lambdaGE_le_cost_descend_of_bracket_member (fun _ _ : Fin 1 => false)
    (P := Protocol.leaf false) (g := fun _ _ => false) (fun _ _ => rfl) []
    (Finset.univ) (Finset.univ) ?_ (fun _ => ()) (fun _ => ())
    (fun _ => trivial) (fun _ => trivial) (fun _ _ => rfl)
  refine ⟨?_, ?_⟩
  · intro j _
    have hx : ((Fintype.card (Fin 1) : ℝ)) * (1 : ℝ) = 1 := by
      simp only [Fintype.card_fin]; norm_num
    rw [hx, hceil]
    have : (Finset.univ : Finset (Fin 1 × Fin 1)).filter (fun p => p.1 = j) = {(j, 0)} := by
      ext p
      obtain ⟨a, c⟩ := p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Prod.mk.injEq]
      exact ⟨fun h => ⟨h, Subsingleton.elim _ _⟩, fun h => h.1⟩
    rw [this, Finset.card_singleton]
  · have hy : ((Fintype.card (Fin 1) : ℝ)) ^ 1 * (1 : ℝ) = 1 := by
      simp only [Fintype.card_fin]; norm_num
    rw [hy, hceil, Finset.card_univ]
    simp

/-- **Statement pole 1: the column clause of `def:bracket` is not free.**

At the empty column set the clause forces `y . |Cl|^{pc} <= 0`, which the frozen
`y = (3/5)^2 > 0` refutes.  So leg (1)'s density is doing work in
`bracketMember_of_blocks_and_columns`, and is not a clause that any set would
satisfy.  **BEYOND-PAPER AUDIT** in the carriers; the density is the paper's. -/
theorem bracket_column_clause_is_not_free :
    ¬ ((3 / 5 : ℝ) ^ 2 * (Fintype.card (Fin 2) : ℝ) ^ 2
        ≤ (((∅ : Finset (Fin 2 → Fin 2)).card : ℕ) : ℝ)) := by
  simp only [Fintype.card_fin, Finset.card_empty, Nat.cast_zero]
  norm_num

/-- **Statement pole 2: the equipartition clause of `def:bracket` is not free.**

`09:1291--1296` trims **every** selected certificate, and the equipartition
demand is per copy, not in aggregate.  A block family that puts everything in one
copy fails it: at two copies with the second block empty, the floor `T = 1` is
missed at that copy even though the total row count is large.  So
`isEquipartitionedGE_blockRows`'s hypothesis is load-bearing.  **BEYOND-PAPER
AUDIT** in the carriers and the floor. -/
theorem equipartition_clause_is_not_free :
    ¬ IsEquipartitionedGE
        (blockRows fun j : Fin 2 => if j = 0 then (Finset.univ : Finset (Fin 2)) else ∅)
        (Finset.univ : Finset (Fin 2)) 1 := by
  intro h
  have h1 := h 1 (Finset.mem_univ 1)
  rw [card_blockRows_fibre] at h1
  simp at h1

end Battery

end EthInapproximability.ParameterizedNP.SelectDischarge
