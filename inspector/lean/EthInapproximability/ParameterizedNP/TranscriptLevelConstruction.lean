import EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring

/-!
# Parameterized NP route: the transcript-level construction of `09:1268--1300`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:105`** ("Let `q = 2^r` be the scale-alignment width"), the width
      identification every capacity readout below is stated against.
    * **`09:277--283`**, the *low-rung* index `kappa_j = q/2^j` with
      `j in {0,1,2}` -- cited here **only** to keep it apart from the frontier
      capacity; it is the banked `WrapperLowRungs.kappaLow` and is never
      consumed as `kappa_v`.
    * **`09:313--323`**, the low-rung substitution display (`r' = kappa_j/t_ref`,
      `t = t_ref`, `a^sharp = 0`), consumed by pin from
      `WrapperReferenceConstruction`; the frontier substitution below is its
      `a^sharp = 1` sibling and is built here, not copied from it.
    * **`09:436--441`**, `rho = 2y^2 = 18/25`, `u_2 = 2`,
      `u_kappa = kappa/2 + 1`; the banked `WrapperProjectionCovers.rhoSmall` and
      `smallCopyWidth`.
    * **`09:1195--1213`** (`lem:wrapper-no-bob-completion`) as the *frame
      condition* only: the banked `RoutingDynamics.CompletedNoBob`.  The
      completion **construction** of `09:1203--1207` (append `r-d` fixed Alice
      messages) is **not** built here; see the residue list.
    * **`09:1217--1222`**, `A_0 = ceil(2 x_T m_G)` and `A_k = 2^k A_0`; the
      banked `DenseWrapperFrontier.initialRefRows` and `refRowFloor`.
    * **`09:1233--1236`**, the initial retention `A_r = q A_0` and "Start one
      clean reference certificate in every coordinate outside `E_0`".
    * **`09:1238--1248`**, the routing rule and the weight bookkeeping; the
      banked `RoutingDynamics` dynamics.
    * **`09:1250--1252`**, the two stopping rules and the exposure rule.
    * **`09:1253--1258`**, `d_v`, and the display **`09:1255`**,
      `kappa_v = 2^{r-d_v}`, with `W_v` at `09:1257`.  **This is the
      prerequisite `WDFW-F10` executes.**
    * **`eq:wrapper-frontier-conservation`, `09:1261--1266`.**
    * **`09:1268`**, `vartheta = 9/16`; the banked
      `DenseWrapperFrontier.vartheta`.
    * **`09:1268--1275`, branch (i)**: "When `kappa_v >= t_{ref}`, follow the
      denser Bob child and invoke the certified-scale reference stopping lemma
      on `G` with `r' = kappa_v/t_{ref}`, `a^sharp = 1`.  The other parameters
      are those of `sec:wrapper-low-rungs`."  **This is the index tuple the
      headline theorem is stated at.**
    * **`09:1276--1290`, branch (ii)**: `2 <= kappa_v < t_ref`,
      `ell_v = log_2 kappa_v`, `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`.
      `09:1287--1290` remains **GAP-EXPOSED** (the projection form), exactly as
      the predecessor records; nothing here narrows it.
    * **`09:1291--1296`**: "Each selected certificate has at least
      `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows, so trim it
      to the row density `kappa_v x_T`."  **This is the row side, and it is
      derived here rather than assumed.**
    * **`09:1297--1300`**, the `lem:certified-row-ladder` call closing branch
      (ii); **not** invoked here.
    * **`09:1310--1313`** (`eq:wrapper-first-bob-light`) and **`09:1315--1344`**
      (`lem:final-reference-uniqueness`): the boundary this module does **not**
      reach.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`):
    `08:166` (`x_T = 2^{-b_T}`, the banked `DenseStageFourOpening.xTdepth`) and
    `08:986--989`, the frozen `kappa_v = 2^{r-d_v}` of the *dense* frontier,
    which is the banked `DenseWeightedCount.stoppingCapacity` the wrapper
    display `09:1255` is pinned to below.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    `A:117--118` and `A:120` (`t` a power of two divisible by `16`,
    `p_t = 9t/16`), `A:125` (`q = r t`), and `A:138--141`, which states
    **three** supply demands -- `r' p_t` represented outer blocks, at least
    `ceil(r' t x m)` rows in each represented block, and column density at least
    `h 2^{-a^sharp}`.  (The banked `RoutedTriple` carries a *fourth* clause,
    `T.Nonempty`; that clause is `WrapperDenseFrontierWiring`'s own record fix
    F4 and is **not** a reading of `A:138--141`.)  `A:26` fixes the cutoff value
    `t_cert = 2^{2^20}` that `A:117`'s `t >= t_cert` refers to.
    `A:285--329` is the endpoint's own proof and is **not** invoked.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `eq:tref-search` (`06:561--567`), the defining display of `k_ref`, consumed
    only through the banked `WrapperReferenceConstruction.tRef`; and
    **`06:237--243`**, "define the auxiliary Stage-3 depth by
    `k_T = log_2(s/4)`, `b_T = 2^{j_49(k_T)}`, `x_T = 2^{-b_T}`" -- the display
    that makes `b_T` a **DEFINED** quantity of the schedule rather than a free
    input (see the DEFINED-VS-FREE ledger below).
* **Reader counterpart (module level, claimed by no single declaration).**
  `routes/parameterized-np/reader-facing/sections/A-stage4-details.tex:315--319`
  -- "Near the full row set, ordinary reference copies control the protocol
  until a terminal frontier; labelled protected copies from other outer
  coordinates are routed to that frontier."  That is the reader's *only* trace
  of the routed certificate system, and it is unnumbered connective prose, not a
  numbered statement.  It is therefore recorded here once, at module level, and
  **no declaration below claims it as its reader counterpart** -- assigning
  prose to a theorem, or the same prose to several theorems, is exactly what the
  reader-counterpart rule forbids.

## What this module is

`WRAPPER-DENSE-FRONTIER-WIRING-001` registered three deferred
canonical-inhabitation obligations and two successors.  This tranche executes
the prerequisite **`WDFW-F10`** and then as much of residue **L1** (the
transcript-level construction of `09:1268--1300`) as the frozen text supports
without the unbuilt certified stopping lemma.

## This generation: `WDFW-F13`, the `hone` retirement reaches this module

The one change over the banked generation, and it is confined to Section 4's row
side: `exists_frontier_routedTriple_at_paper_indices` carried the retired
`hone : kappa_v x_T m_G >= 1` and weakened it at the call after `L1-F6` retired
the same binder from the banked supply (tranche `cc-t5h`).  That residue is the
successor `WDFW-F13` registered by `WrapperDenseFrontierWiring`, and it is
**DISCHARGED here**: the binder is now `hpos : 0 < kappa_v x_T m_G`, in the same
binder position, with the conclusion byte-identical and the theorem therefore
strictly stronger.  Nothing else in this module changes, no anchor is re-cited,
no deferral is discharged, and no obligation is transferred.  Two consequential
edits follow it and are named here so they are not mistaken for scope creep:
`heavy_frontier_bundle_is_jointly_satisfiable` keeps the retired, strictly
stronger clause and weakens it at the call (retiring a binder must not weaken
the evidence that the bundle is inhabited), and statement pole 2 gains the
conjunct that poles the *replacement* binder at the same `x = 0`, its docstring
having claimed a binder that no longer exists.  In round `r1` that pole is also
**renamed**, `trim_nonemptiness_needs_hone` ->
`trim_nonemptiness_needs_a_row_density_clause`: after the retirement the old name
pointed at a binder no statement in `src/` carries, and a past-tense docstring is
the mitigation `WDFW-F14` was registered to reject.  The declaration is consumed
by nothing, so no proof term moves, the old name is not kept as an alias, and
**no statement byte changes**.  The module's declaration count is unchanged at
`56`.

**Section 1 executes `WDFW-F10`.**  The frontier capacity `kappa_v = 2^{r-d_v}`
of `09:1255` is reified as `kappaFrontier`, **by pin** on the banked
`DenseWeightedCount.stoppingCapacity` (the same display at `08:986--989`), and
then as `kappaAt`, *indexed by a frontier node of a routed certificate system*
rather than by a numeral.  The indexing is the whole point.  As bare arithmetic
`kappa_v = 2^{r-d_v}` and the low-rung `kappa_j = q/2^j` are the **same
function** -- `kappaFrontier_and_kappaLow_are_numerically_identical` proves this
outright, by `rfl` -- so nothing but the *provenance of the index* separates
them, and a numeral-level encoding would silently permit the conflation.
`kappaAt` takes a node; `kappaLow` takes a rung index `j <= 2`; and
`kappaFrontier_depth_can_leave_the_rung_range` exhibits a legal frontier depth
whose capacity **no** legal rung index produces.  That is why the predecessor
was right to refuse the conflation, and it is now a machine-checked refusal
rather than a comment.

**Section 2 builds the paper's own index tuple at the frontier.**  `09:1272`
fixes `r' = kappa_v/t_ref` and `t = t_ref`; `frontierCopies` is that quotient in
the exponent form the banked `refRungCopies` uses at the low rungs, and
`frontierBlockCount_eq_certifiedPt_kappa` **evaluates** the substitution:
`r' p_t = p_{kappa_v}`, i.e. the frozen `9 kappa_v/16` of `09:1280--1283`.
Nothing is assigned; the count is obtained from `A:117--120` through the banked
`sixteen_mul_certifiedPt`, exactly as `refBlockCount_eq_certifiedPt_kappa` does
one section earlier.  `tRef_le_kappaFrontier_iff` turns `09:1269`'s branch
condition into its exponent form.

**Section 3 derives the row side.**  This is the substantive new mathematics of
the tranche.  `09:1291--1296` demands that each selected certificate carry at
least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows.  Read
through the banked schedule, `A_{ell_v}` is literally
`refRowFloor A_0 (r - d_v) = kappa_v A_0`
(`refRowFloor_eq_kappaFrontier_mul`, by `rfl`), and the routing invariant
`FrontierIndexing.coordRoutes_rows_floor` already delivers exactly that many
rows at every frontier address.  So at the paper's own `A_0`
(`initialRefRows x_T m_G`, `09:1219`) the trim hypothesis of
`WrapperDenseFrontierWiring.exists_trimmed_reference_rows` is
**dischargeable** rather than irreducibly assumed: `certificate_rows_meet_trim_demand`
is the theorem about the routing that supplies it.  **Stated precisely, so the
claim is not read as more than it is:** the composition is *available* -- take
`p := v.val`, `m_G := Fintype.card X`, `A_0 := initialRefRows x_T (Fintype.card X)`,
`Arows := rowsAt P (R i) v.val`, with the node on coordinate `i`'s route -- but it
is **not exhibited** in this tranche.  Section 4 still carries `hA` as a binder,
and does so deliberately, to keep the headline general in `A_0`; the audit
instance discharges `hA` by direct evaluation, not through Section 3.  The
composed corollary at the paper's schedule (with `m_G` pinned to the carrier) is
named successor **L1-F1** below.  The frozen factor `2` is where it always
was -- in `A_0`'s own ceiling -- and it is consumed, not re-supplied.

**Section 4 is the headline.**  `exists_frontier_routedTriple_at_paper_indices`
produces the routed triple `(S,T,K)` at
`r' = kappa_v/t_ref`, `t = t_ref`, `a^sharp = 1` -- the paper's own index tuple
of `09:1272--1273` -- with the block-count hypothesis `hblocks` **discharged**
from Section 2 rather than carried.  `paperFrontierRestriction` is the
`RestrictionDatum` built from it, and `paperFrontierRestriction_selCard` reads
back the frozen `p_{kappa_v} = 9 kappa_v/16`.

**Section 5 states the frozen dichotomy at a node**: `09:1269` versus `09:1277`,
exhaustive and disjoint with the boundary `kappa_v = t_ref` assigned to branch
(i), `ell_v = log_2 kappa_v` (`09:1278`) evaluated, and `09:1283`'s cover-entry
consequence restated at `kappaAt` by pin on the banked
`SplitFirstBobInstance.heavy_firstBob_smallCopyWidth_le`.

**Section 6 is a general transcript family**, and Section 7 is the audit
instance built on it.

## CANONICAL INHABITATION -- what this tranche discharges and what it does not

**DISCHARGED: obligation (i) of `WRAPPER-DENSE-FRONTIER-WIRING-001`** -- the
routed triple *at the paper's own index tuple*.  The predecessor deferred it for
one stated reason: "`kappa_v = 2^{r-d_v}` (`09:1255`) has no reification in
`src/`".  Section 1 supplies it and Section 2 evaluates `09:1272` through it, so
`exists_frontier_routedTriple_at_paper_indices` is stated at
`r' = frontierCopies r d_v k_ref`, `t = tRef k_ref`, `a^sharp = 1` -- no free
`r'`, no free `t`, no assigned numeral, and the block count obtained by
evaluating the definitional chain.

**STILL DEFERRED: obligation (ii)** -- the five-clause frontier bundle at the
*paper's own instance*.  The paper's instance is the routing of an **alleged**
`(C+r-1)`-bit protocol computing a member of `<U,1,1-delta_U,theta>`
(`09:1188--1193`).  No such protocol exists -- that is the conclusion of the
argument -- so the paper's object at `09:1268` is a *function of the assumed
protocol*, and the honest Lean form is exactly the implication this module
states.  What was open, and is now closed, is whether the implication's
hypothesis bundle is **vacuous**: `heavy_frontier_bundle_is_jointly_satisfiable`
exhibits a routed certificate system in which all six clauses hold **at once**,
every one of them tight.  Together with the predecessor's
`live_firstBob_node_is_not_heavy` (a routing where `hheavy` fails) the heavy
premise is now known to be neither automatic nor unsatisfiable.  That instance
is nevertheless labelled **NON-FIDELITY / BEYOND-PAPER** and does **not**
discharge (ii): `k_ref = 4` meets every gate this module carries, but `A:117`
forces `t_ref >= t_cert = 2^{2^20}`, so the instance visits a point the paper
never does.

**STILL DEFERRED: obligation (iii)**, `ReferenceStoppingEndpoint`, untouched.

## THE R5 REACH, RECORDED PER TRUTH

The `cc-t5a-r1` judge's finding R5 was that a statement pole had been
*re-derived* where it should have been *consumed by pin*.  The reach of that
finding here, stated per truth rather than per habit:

* Everything the predecessor already proved is consumed by pin and **not**
  restated: `RoutedTriple` and its readout battery, `exists_selected_blocks_at_heavy_node`,
  `exists_trimmed_reference_rows`, `exists_denser_child_colFloor`,
  `exists_frontier_routedTriple`, `frontierRoutedRestriction`,
  `heavy_blockCount_le_card_representedCoords`,
  `heavy_firstBob_smallCopyWidth_le`, `initialRefRows_ge`, `refRowFloor`,
  `vartheta`, `stoppingCapacity`, `tRef`, `certifiedPt`.
* The three poles below are **new** claims about **new** objects
  (`kappaFrontier`, `frontierCopies`, the trim demand at the paper's `A_0`);
  none of them re-derives a banked pole.  In particular the empty-selection pole
  of `frontier_blockCount_needs_the_heavy_node` is **not** repeated: the pole
  here is the strictly different statement that the demanded count is positive
  *at the paper's index tuple*, which the predecessor could not state.
* One banked fact is **restated deliberately and labelled as such**:
  `kappaAt_eq_capacity` is `rfl` and exists solely to record, in the kernel,
  that the new node-indexed name is the banked capacity and not a second
  reification.  It is a pin assertion, not a re-derivation.

## Residues this module does NOT close (named, not implied)

* **L1a, the completion construction.**  `lem:wrapper-no-bob-completion`'s proof
  (`09:1203--1207`) builds a padded protocol; only its *frame condition*
  `CompletedNoBob` is used here, as the banked binder.  The padding transformer
  and its cost bound `max{cost(P), r} <= C+r-1` are unbuilt.
* **L1b, the initial-survival gates.**  `eq:wrapper-initial-survival`
  (`09:1224--1232`) and the retention "at least `A_r = q A_0` reference rows"
  (`09:1233--1235`) enter as the banked `hR` binder; the three gates are not
  derived from the schedule here.
* **`09:1287--1290` stays GAP-EXPOSED** in its projection form, verbatim as the
  predecessor left it; the column side is supplied only in the column-set form.
* **`eq:wrapper-first-bob-light` (`09:1310--1313`) is not proved**, because its
  proof runs through `thm:certified-localized-extension` and
  `lem:certified-row-ladder`.  Neither is invoked.
* **`lem:final-reference-uniqueness` (`09:1315--1344`) is untouched.**
* `hDenseRung` is neither discharged nor fed; `eq:wrapper-u-dense`
  (`09:1780--1781`) is not approached; `thm:first-wrapper` is not proved; **no
  route completion is claimed.**

## Named successors this module registers (each needs its own judged tranche)

These are evidence and composition gaps, not defects in any statement below.
Each requires a **new declaration**, so none of them is repaired here.

* **`L1-F1` -- the composed `hA` discharge.**  State the corollary that composes
  `certificate_rows_meet_trim_demand` into the headline at the paper's schedule,
  pinning `m_G := Fintype.card X` at the point of consumption.  This closes the
  gap named in the Section 3 paragraph above and simultaneously removes the one
  place in this module where a schedule quantity floats free of its carrier:
  `certificate_rows_meet_trim_demand` quantifies over `m_G : ℕ` with the row
  carrier `X` separate, so although the statement is universally quantified (and
  therefore *includes* the paper's `m_G = |X|` of `09:1294`, coherently in both
  hypothesis and conclusion, hence not vacuous), it degenerates at `m_G = 0`.
  The banked layer deliberately reads `m` at the carrier for exactly this
  reason.
* **`L1-F2` -- a live-fire for `hone` at a *legal* `x_T`.**  Statement pole 2
  (`trim_nonemptiness_needs_a_row_density_clause`) fires at `x = 0`, but `x_T = 2^{-b_T}`
  (`08:166`) is strictly positive for every `b_T`, so `x = 0` is a point the
  schedule can never reach.  The probe therefore shows `hone` load-bearing only
  outside the legal range.  Re-fire it at positive `x` with a small carrier,
  where `hone` can still genuinely fail.
* **`L1-F3` -- a rejection probe for `4 <= k_ref`.**  Of the headline's two new
  binders only `hcap` is probed (`frontierCopies_needs_the_branch_guard`); `hk`
  is unprobed although it is load-bearing.  The witness is available: at
  `r = 4`, `d_v = 0`, `k_ref = 3` one has `r' . p_{t_ref} = 2 . 4 = 8` while
  `p_{kappa_v} = certifiedPt 16 = 9`, so
  `frontierBlockCount_eq_certifiedPt_kappa` fails without `4 <= k_ref`.  Land it
  labelled as claiming no legality.
* **`L1-F4` -- a joint-satisfiability witness at `d_v > 0`.**  The audit instance
  below sits at a depth-`1` protocol with `d_v = 0`, so no Alice query is ever
  routed, no certificate ever splits, and the weight bookkeeping of
  `09:1244--1248` is never exercised (this is disclosed at the instance itself).
  A witness at `d_v > 0` with an actual split would exercise what `09:1259`'s
  `kappa_v >= 2` and the halving of `09:1239--1243` are about, and is strictly
  stronger evidence.

## Axioms and imports

The only import is `WrapperDenseFrontierWiring`, so there is no
`LegacyNPCC.Stage12` in the transitive closure and no contact with the AGHP
balanced-family axiom.  `EXPANDER-001` occurs in no hypothesis of any
declaration below.  No `axiom`, no opaque certificate, no unproved obligation
marker.

## DEFINED-VS-FREE ledger for this tranche

| quantity | status | how it is obtained here |
| --- | --- | --- |
| `kappa_v` | DEFINED, `09:1255` | `kappaFrontier`, pinned to the banked `stoppingCapacity` |
| `r'` at `09:1272` | DEFINED | `frontierCopies`, the quotient in exponent form |
| `t` at `09:1272` | DEFINED, `eq:tref-search` | the banked `tRef k_ref`, at a `4 <= k_ref` binder |
| `a^sharp` at `09:1273` | DEFINED | the literal `1` of the display |
| `p_t` | DEFINED, `A:120` | the banked `certifiedPt`, evaluated |
| `A_0` | DEFINED, `09:1219` | the banked `initialRefRows x_T m_G`, evaluated |
| `A_{ell_v}` | DEFINED, `09:1221` | the banked `refRowFloor`, evaluated |
| `vartheta` | DEFINED, `09:1268` | the banked `vartheta` |
| `rho` | DEFINED, `09:436` | the banked `rhoSmall` |
| `x_T` | DEFINED, `08:166` with `06:243` | the banked `xTdepth` at `b_T` |
| `b_T` | **DEFINED**, `06:239--241` | see the `b_T` note directly below |
| `k_ref`, `r`, `C` | binders | never assigned outside the labelled audit instance |

**The `b_T` note.**  `b_T` is **not** a free input.  `06:237--243` defines the
auxiliary Stage-3 depth by `k_T = log_2(s/4)`, `b_T = 2^{j_49(k_T)}`, and then
`x_T = 2^{-b_T}`; so `b_T` is obtained by evaluating `j_49` at `k_T`, which is
itself derived from `s`.  In this module `b_T` is a *Lean binder*, and it is
assigned exactly once -- to `5`, inside the Section 7 instance that carries the
BEYOND-PAPER label and claims no legality, where self-chosen values are
admissible.  **A successor that claims legality must evaluate `06:239--241`, not
assign.**

Every numeral in Sections 1--6 is a frozen literal of a cited display (`2`, `9`,
`16`, `1`) or an evaluation.  Self-chosen values occur **only** in Section 7,
which claims no legality and says so in its own docstring.
-/

namespace EthInapproximability.ParameterizedNP.TranscriptLevelConstruction

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.LargeCapacityBranch
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring

/-! ## §1  `WDFW-F10`: the frontier capacity `kappa_v = 2^{r-d_v}` (`09:1255`)

"If `v` is a frontier node, let `d_v` be the number of preceding Alice queries
and set `kappa_v = 2^{r-d_v}`, `W_v = total certificate weight at v`."

The display is the wrapper's own, but the *function* it names is the banked
`DenseWeightedCount.stoppingCapacity` of `08:986--989`.  It is therefore pinned,
not restated -- and then given a node-indexed form, which is the reification the
predecessor's `WDFW-F10` asked for. -/

section Capacity

/-- **`09:1255`, reified.**  `kappa_v = 2^{r-d_v}` at the wrapper exponent,
**by pin** on the banked `stoppingCapacity` (the same display at `08:986--989`).

This is a name, not a second definition: `kappaFrontier_eq` records that it
unfolds to the frozen `2^{r-d}` and nothing else. -/
def kappaFrontier (r d : ℕ) : ℕ := stoppingCapacity r d

/-- **Aux F1.**  The frozen display, unfolded.  General. -/
@[simp] theorem kappaFrontier_eq (r d : ℕ) : kappaFrontier r d = 2 ^ (r - d) := rfl

/-- **Aux F2 (`09:1255` at `d_v = 0`).**  At the root the capacity is the full
scale-alignment width `q = 2^r` of `09:105`.  General. -/
@[simp] theorem kappaFrontier_zero (r : ℕ) : kappaFrontier r 0 = 2 ^ r := by
  simp [kappaFrontier, stoppingCapacity]

/-- **Aux F3.**  Every capacity is positive.  Consumed from the banked
`one_le_stoppingCapacity`.  General. -/
theorem one_le_kappaFrontier (r d : ℕ) : 1 ≤ kappaFrontier r d :=
  one_le_stoppingCapacity r d

/-- **Aux F4 (`09:1264`'s right-hand side bounds every summand).**  No node's
capacity exceeds the width `q = 2^r`.  General. -/
theorem kappaFrontier_le_width (r d : ℕ) : kappaFrontier r d ≤ 2 ^ r :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Aux F5 (`09:1239--1243` and `09:1255` together).**  One further Alice query
halves the capacity, so the frozen exponent really is a *depth* counter.
General, at any depth strictly below `r`. -/
theorem two_mul_kappaFrontier_succ {r d : ℕ} (h : d < r) :
    2 * kappaFrontier r (d + 1) = kappaFrontier r d := by
  simp only [kappaFrontier, stoppingCapacity]
  rw [show r - d = (r - (d + 1)) + 1 by omega, pow_succ]
  ring

/-- **The frontier capacity of a node of a routed certificate system.**

`kappa_v` as `09:1253--1255` writes it: a function of the *node*, whose `d_v` is
"the number of preceding Alice queries", i.e. the length of the node's address.
This is the reification `WDFW-F10` records as missing, and the indexing is its
content -- see `kappaFrontier_and_kappaLow_are_numerically_identical` below for
why a numeral-level name would not have sufficed.  General in `P`, `Coord`, `R`,
`A_0`, `r` and the node. -/
def kappaAt {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]
    (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : ℕ :=
  kappaFrontier r v.val.length

section Node

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **Pin assertion (deliberate restatement, see the R5 paragraph).**

The node-indexed name **is** the banked frontier capacity of
`RoutedCertificateSystem.toWrapperFrontier`, by `rfl`.  Its only purpose is to
make it impossible for a later tranche to treat `kappaAt` as a second, competing
reification of `09:1255`.  General. -/
theorem kappaAt_eq_capacity {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) :
    kappaAt P R A0 r v = (canonicalSystem hcomp hR).toWrapperFrontier.capacity v := rfl

/-- **Aux F6.**  Positivity at a node.  General. -/
theorem one_le_kappaAt (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : 1 ≤ kappaAt P R A0 r v :=
  one_le_kappaFrontier _ _

/-- **Aux F7.**  `kappa_v <= q` at a node (`09:1264`'s summand bound).
General. -/
theorem kappaAt_le_width (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : kappaAt P R A0 r v ≤ 2 ^ r :=
  kappaFrontier_le_width _ _

/-- **`09:1259`, "Every first-Bob node has `kappa_v >= 2`", at a node.**

Proved from the frozen exposure rule alone, through the banked
`two_le_stoppingCapacity_firstBob`.  General. -/
theorem two_le_kappaAt_of_firstBob {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true) :
    2 ≤ kappaAt P R A0 r v :=
  two_le_stoppingCapacity_firstBob ((canonicalSystem hcomp hR).firstBob_spec v hv)

/-- **`09:1250--1252` at a final Alice node**: `d_v = r`, so `kappa_v = 1`.
General. -/
theorem kappaAt_final_eq_one {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = false) :
    kappaAt P R A0 r v = 1 :=
  stoppingCapacity_final_eq_one ((canonicalSystem hcomp hR).final_spec v hv)

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), at the
node-indexed capacity.**  `sum_v kappa_v <= q`, by pin on the banked
`canonicalSystem_sum_capacity_le_width`; not re-proved.  General. -/
theorem sum_kappaAt_le_width {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) :
    ∑ v : FrontierNode P R A0 r, kappaAt P R A0 r v ≤ 2 ^ r :=
  canonicalSystem_sum_capacity_le_width hcomp hR

end Node

/-! ### Why `kappa_v` and `kappa_j` must not be conflated

The predecessor refused to identify the frontier capacity `kappa_v` (`09:1255`)
with the low-rung index `kappa_j = q/2^j` (`09:280`).  The two theorems below are
the machine-checked form of that refusal, and they are stated in this order on
purpose: the first shows that no *arithmetic* distinguishes them, and the second
shows that the *index ranges* do. -/

/-- **The conflation trap, exhibited.**

As bare arithmetic the two frozen displays are the **same function**: `09:1255`'s
`2^{r-d_v}` and `09:280`'s `q/2^j = 2^{r-j}` agree at every common argument, by
`rfl` against the banked `WrapperLowRungs.kappaLow`.  So no value check, no
`norm_num`, and no green build can catch a conflation of the two -- only the
provenance of the index can.  This is precisely why `kappaAt` is indexed by a
*frontier node* and `kappaLow` by a *rung*.  General. -/
theorem kappaFrontier_and_kappaLow_are_numerically_identical (r i : ℕ) :
    kappaFrontier r i = kappaLow r i := rfl

/-- **Statement pole: the index ranges are genuinely different.**

`09:278` fixes the rung index to `j in {0,1,2}`, while `09:1253` lets `d_v` run
over every Alice depth `0 <= d_v <= r`.  At `r = 5` and `d_v = 3` the frontier
capacity is `4`, and **no** legal rung index produces it: `kappa_0 = 32`,
`kappa_1 = 16`, `kappa_2 = 8`.  So the two symbols are not interchangeable even
extensionally over their frozen domains, and any tranche that substituted
`kappaLow` for `kappa_v` would be making a substitution the frozen text does not
license.  Concrete numerals here are a **refutation witness**, not an
instantiation: this statement claims no legality. -/
theorem kappaFrontier_depth_can_leave_the_rung_range :
    ∃ r d : ℕ, d ≤ r ∧ ∀ j : ℕ, j ≤ 2 → kappaLow r j ≠ kappaFrontier r d := by
  refine ⟨5, 3, by norm_num, ?_⟩
  intro j hj
  interval_cases j <;> simp [kappaLow, kappaFrontier, stoppingCapacity]

end Capacity

/-! ## §2  The paper's own index tuple at the frontier (`09:1269--1274`)

"When `kappa_v >= t_{ref}`, follow the denser Bob child and invoke the
certified-scale reference stopping lemma on `G` with `r' = kappa_v/t_{ref}`,
`a^sharp = 1`.  The other parameters are those of `sec:wrapper-low-rungs`."

`t = t_ref` and `x = x_T`, `h = theta`, `M = G` come from `09:313--323` through
that last sentence.  What is new is `r'`, and it is a *quotient of the frontier
capacity* -- so it could not be written down before Section 1. -/

section PaperIndices

/-- **`r' = kappa_v/t_ref` (`09:1272`), reified.**

At `kappa_v = 2^{r-d_v}` and `t_ref = 2^{k_ref}` the frozen quotient is the
exponent difference, in exactly the form the banked
`WrapperReferenceConstruction.refRungCopies` takes at the low rungs.  The natural
subtraction is exact under the branch condition `t_ref <= kappa_v` of `09:1269`,
which is where every consumer below fires it. -/
def frontierCopies (r d kref : ℕ) : ℕ := 2 ^ (r - d - kref)

@[simp] theorem frontierCopies_eq (r d kref : ℕ) :
    frontierCopies r d kref = 2 ^ (r - d - kref) := rfl

/-- **Aux G1.**  `r'` is a positive natural, which is what `A:125`'s `q = r t`
needs.  General. -/
theorem frontierCopies_pos (r d kref : ℕ) : 0 < frontierCopies r d kref :=
  pow_pos (by norm_num) _

/-- **`09:1269`'s branch condition in exponent form.**

`t_ref <= kappa_v` iff `k_ref <= r - d_v`.  This is the guard that makes the
`09:1272` quotient exact, and it is the guard `09:1269` states.  General. -/
theorem tRef_le_kappaFrontier_iff (r d kref : ℕ) :
    tRef kref ≤ kappaFrontier r d ↔ kref ≤ r - d := by
  simp only [tRef_eq, kappaFrontier_eq]
  exact Nat.pow_le_pow_iff_right (by norm_num)

/-- **`A:125` (`q = r t`) at the `09:1272` substitution, PROVED.**

`r' t_ref = kappa_v` identically, not approximately: the two exponents add back
under the branch guard.  General at the frozen guard. -/
theorem frontierCopies_mul_tRef {r d kref : ℕ} (hcap : kref ≤ r - d) :
    frontierCopies r d kref * tRef kref = kappaFrontier r d := by
  simp only [frontierCopies_eq, tRef_eq, kappaFrontier_eq, ← pow_add]
  congr 1
  omega

/-- **`09:1272` with `A:138--139` and `09:1280--1283`, EVALUATED.**

`A:138` demands `r' p_t` represented outer blocks.  At the paper's own index
tuple that count is not chosen: substituting `r' = kappa_v/t_ref`, `t = t_ref`
and evaluating `A:120`'s `p_t = 9t/16` through the banked
`sixteen_mul_certifiedPt` gives exactly `p_{kappa_v}`, which is the frozen
`9 kappa_v/16` the census of `09:1280--1283` supplies.

This is the frontier sibling of the banked
`WrapperReferenceConstruction.refBlockCount_eq_certifiedPt_kappa`, which does the
same evaluation at the low-rung index `kappa_j`; the two are stated separately
because their indices are (see Section 1) different objects.  The divisibility
`16 | t` of `A:117--118` is supplied at both ends by `k_ref >= 4` and by
`k_ref <= r - d_v`.

**Branch attribution (the banked record fix F2, restated where a reader meets
it).**  The census `09:1280--1283` is printed inside branch (ii)'s paragraph
(`2 <= kappa_v < t_ref`, `09:1277`), while the tuple evaluated here is branch
(i)'s (`09:1272`, `kappa_v >= t_ref`).  Using it here is sound because the count
depends only on `09:1268`'s heavy condition `W_v >= vartheta kappa_v`, which is
stated *before* the branch split and holds on both sides; the caveat travels
with the banked theorem being consumed and is repeated here so it is not
rediscovered.  General at the frozen guards. -/
theorem frontierBlockCount_eq_certifiedPt_kappa {r d kref : ℕ} (hk : 4 ≤ kref)
    (hcap : kref ≤ r - d) :
    frontierCopies r d kref * RestrictionDatum.certifiedPt (tRef kref)
      = RestrictionDatum.certifiedPt (kappaFrontier r d) := by
  have hPt : RestrictionDatum.certifiedPt ((2 : ℕ) ^ kref) = 9 * 2 ^ (kref - 4) := by
    have hP : 16 * RestrictionDatum.certifiedPt ((2 : ℕ) ^ kref) = 9 * 2 ^ kref :=
      RestrictionDatum.sixteen_mul_certifiedPt (RestrictionDatum.sixteen_dvd_two_pow hk)
    have hsplit : (2 : ℕ) ^ kref = 16 * 2 ^ (kref - 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  have hPtK : RestrictionDatum.certifiedPt (kappaFrontier r d) = 9 * 2 ^ (r - d - 4) := by
    have hP : 16 * RestrictionDatum.certifiedPt (kappaFrontier r d) = 9 * 2 ^ (r - d) := by
      rw [kappaFrontier_eq]
      exact RestrictionDatum.sixteen_mul_certifiedPt
        (RestrictionDatum.sixteen_dvd_two_pow (by omega))
    have hsplit : (2 : ℕ) ^ (r - d) = 16 * 2 ^ (r - d - 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  rw [frontierCopies_eq, tRef_eq, hPt, hPtK]
  rw [← mul_assoc, mul_comm (2 ^ (r - d - kref)) 9, mul_assoc, ← pow_add]
  congr 2
  omega

/-- **`09:1268--1269` with `09:1280--1283`: the block demand is met by the heavy
census, at the paper's index tuple.**

The natural division in `A:120` only ever floors, so the block count demanded at
`09:1272` is at most the frozen `9 kappa_v/16` that
`heavy_blockCount_le_card_representedCoords` delivers.  This is the hypothesis
`hblocks` of the banked `exists_frontier_routedTriple`, and it is a **theorem**
at the paper's own indices rather than a binder.  General at the frozen
guards. -/
theorem frontierBlockCount_le_heavy_ceiling {r d kref : ℕ} (hk : 4 ≤ kref)
    (hcap : kref ≤ r - d) :
    ((frontierCopies r d kref * RestrictionDatum.certifiedPt (tRef kref) : ℕ) : ℝ)
      ≤ 9 * ((kappaFrontier r d : ℕ) : ℝ) / 16 := by
  rw [frontierBlockCount_eq_certifiedPt_kappa hk hcap]
  have h16 : 16 * RestrictionDatum.certifiedPt (kappaFrontier r d) ≤ 9 * kappaFrontier r d := by
    rw [RestrictionDatum.certifiedPt, mul_comm]
    exact Nat.div_mul_le_self _ _
  have h16R : 16 * ((RestrictionDatum.certifiedPt (kappaFrontier r d) : ℕ) : ℝ)
      ≤ 9 * ((kappaFrontier r d : ℕ) : ℝ) := by exact_mod_cast h16
  linarith

end PaperIndices

/-! ## §3  The row side of `09:1291--1296`, DERIVED

"Each selected certificate has at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
m_G` reference rows, so trim it to the row density `kappa_v x_T`."

Two frozen identities and one banked routing invariant close this: `A_{ell_v}` is
the schedule value `refRowFloor A_0 (r - d_v)`, that value *is* `kappa_v A_0`,
and the routing already guarantees it at every frontier address. -/

section RowSide

/-- **`09:1221` at the frontier exponent, `09:1255` substituted -- an identity.**

`A_{ell_v} = 2^{ell_v} A_0` with `ell_v = r - d_v` is literally `kappa_v A_0`.
Both sides are the banked names; nothing is recomputed.  General. -/
theorem refRowFloor_eq_kappaFrontier_mul (A0 r d : ℕ) :
    refRowFloor A0 (r - d) = kappaFrontier r d * A0 := rfl

/-- **`09:1291--1295`, the frozen factor two, PROVED at the paper's own `A_0`.**

"`A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G`."  The banked
`initialRefRows_ge` says `A_0 >= 2 x_T m_G` (`09:1219`'s ceiling), and the
inequality survives multiplication by the nonnegative capacity.  This is where
the frozen factor `2` lives, and it is consumed here rather than re-supplied.
General in `kappa`, `m_G` and `x_T`. -/
theorem kappa_mul_initialRefRows_ge_trim_demand (κ mG : ℕ) (xT : ℝ) :
    2 * ((κ : ℝ) * xT * (mG : ℝ)) ≤ ((κ * initialRefRows xT mG : ℕ) : ℝ) := by
  have hbase : 2 * xT * (mG : ℝ) ≤ ((initialRefRows xT mG : ℕ) : ℝ) :=
    initialRefRows_ge xT mG
  have hκ : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

section Routing

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

omit [Fintype Coord] in
/-- **`09:1238--1239` with `09:1291--1295`: the trim demand is a THEOREM about the
routing.**

At the paper's own `A_0 = ceil(2 x_T m_G)` (`09:1219`), the routed descendant of
coordinate `i` sitting at a frontier address `p` holds at least
`A_{r-|p|} = kappa_v A_0` reference rows -- that is the banked routing invariant
`FrontierIndexing.coordRoutes_rows_floor`, not a new assumption -- and
`kappa_mul_initialRefRows_ge_trim_demand` turns that into the frozen
`>= 2 kappa_v x_T m_G` of `09:1293--1295`.

So `hA`, which the banked `exists_trimmed_reference_rows` and
`exists_frontier_routedTriple` carry as a hypothesis, is discharged at the
paper's schedule.  General in `P`, `Coord`, `R`, `r`, the coordinate, the
address, `m_G` and `x_T`. -/
theorem certificate_rows_meet_trim_demand {P : Protocol X Y Z} {R : Coord → Finset X}
    {r mG : ℕ} {xT : ℝ} {i : Coord}
    (hR : refRowFloor (initialRefRows xT mG) r ≤ (R i).card)
    {p : List Bool} (hp : p ∈ coordRoutes P R (initialRefRows xT mG) r i) :
    2 * (((kappaFrontier r p.length : ℕ) : ℝ) * xT * (mG : ℝ))
      ≤ ((rowsAt P (R i) p).card : ℝ) := by
  have hfloor := coordRoutes_rows_floor hR hp
  rw [refRowFloor_eq_kappaFrontier_mul] at hfloor
  have hcast : ((kappaFrontier r p.length * initialRefRows xT mG : ℕ) : ℝ)
      ≤ ((rowsAt P (R i) p).card : ℝ) := by exact_mod_cast hfloor
  exact le_trans (kappa_mul_initialRefRows_ge_trim_demand _ mG xT) hcast

end Routing

end RowSide

/-! ## §4  The routed triple at the paper's own index tuple (`09:1272--1273`)

The predecessor's `exists_frontier_routedTriple` is general in `r'` and `t`, and
recorded that generality as the reason the paper's own instance stayed deferred.
With Sections 1--3 in place the tuple can be written down, and the block-count
hypothesis discharged. -/

section PaperTriple

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord]

/-- **`09:1268--1296` at the frozen index tuple `r' = kappa_v/t_ref`,
`t = t_ref`, `a^sharp = 1` -- the tranche's headline.**

The routed triple of the dense frontier, produced at the substitution `09:1272`
prints, rather than at free indices.  Compared with the banked
`exists_frontier_routedTriple` three things change, and all three are
strengthenings:

* `r'` and `t` are no longer free.  They are `frontierCopies r d_v k_ref` and
  `tRef k_ref`, i.e. the paper's `kappa_v/t_ref` and `t_ref`, obtained by
  evaluating `09:1255` and `eq:tref-search`.
* the block-count hypothesis `hblocks` is **discharged**, by
  `frontierBlockCount_le_heavy_ceiling`; the caller no longer supplies it.
* the branch guard `t_ref <= kappa_v` of `09:1269` is carried explicitly, in the
  exponent form `k_ref <= r - d_v`, so the natural quotient is exact.

**`WDFW-F13`, DISCHARGED here: the paper-shaped `hone` is retired from this
statement too.**  The banked `exists_trimmed_reference_rows` gave up
`hone : kappa_v x_T m_G >= 1` in tranche `cc-t5h` (`L1-F6`) and kept only the
positivity it actually consumes; this caller went on carrying the retired binder
and weakening it at the call, and `WrapperDenseFrontierWiring` registered
removing that residue as successor `WDFW-F13`.  It is taken here: the binder is
now `hpos : 0 < kappa_v x_T m_G`, in the same binder position, with the
conclusion **byte-identical**.  Nothing in the frozen text is given up --
`09:1291--1296` states only the row count `A_{ell_v} = kappa_v A_0 >= 2 kappa_v
x_T m_G`, never a `>= 1` display -- and the replacement is weaker
(`retired_hone_binder_is_strictly_stronger`), so the theorem is strictly stronger
and every model of the old bundle is a model of the new one.  It is also
**better supplied**: `08:166`'s `x_T = 2^{-b_T}` is positive and `A:111`'s row
carrier is nonempty, so the replacement holds wherever the schedule is read,
whereas `TranscriptLevelSuccessors.hone_can_fail_at_legal_positive_xT` exhibits
legal schedule values at which the retired binder is false.  (Turning that supply
into a declaration of its own is registered as successor `L1-F10` of
`TRANSCRIPT-LEVEL-SUCCESSORS-001` and is taken by no tranche yet.)

What remains a binder is exactly what the frozen text leaves as the branch's own
entry data: `hbob` (the node is a Bob query), `hheavy` (`09:1268--1269`), `hpos`
(the positivity that makes the trimmed set nonempty), `hA` (the certificate's row
count -- discharged at the paper's schedule by
`certificate_rows_meet_trim_demand`, and left as a binder here only so that the
theorem stays general in `A_0`), and `hdens` (the parent column density).
`heavy_frontier_bundle_is_jointly_satisfiable` shows the bundle is not vacuous;
it deliberately keeps the **retired** clause `1 <= kappa_v x_T m_G`, which is
strictly stronger than `hpos`, so that the witness evidence does not weaken
along with the interface, and weakens it at the call.

*Why the trivial witness fails.*  `S = empty` has card `0`, while the demanded
count `r' p_t` is **positive** at the paper's index tuple
(`paper_blockCount_is_positive`); and `T = empty` is refuted by `hpos` through
the banked `exists_trimmed_reference_rows`, whose nonemptiness clause forces the
row floor `ceil(r' t x m)` to be at least `1`
(`certifiedRowFloor_pos_iff_trim_positive`).  Neither degenerate choice satisfies
the conclusion.

General in the three protocol carriers, in `Coord`, in the routed system, in the
node, in `k_ref`, `x_T` and `theta`. -/
theorem exists_frontier_routedTriple_at_paper_indices (P : Protocol X Y Z)
    (R : Coord → Finset X) (A0 r : ℕ) (v : FrontierNode P R A0 r)
    (Sc : Finset Y) (Arows : Finset X) {kref : ℕ} {xT θ : ℝ}
    (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length)
    (hY : 0 < Fintype.card Y)
    (hbob : IsBobNode (descend P v.val))
    (hheavy : vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) ≤ frontierWeight P R A0 r v)
    (hpos : 0 < ((kappaAt P R A0 r v : ℕ) : ℝ) * xT * ((Fintype.card X : ℕ) : ℝ))
    (hA : 2 * (((kappaAt P R A0 r v : ℕ) : ℝ) * xT * ((Fintype.card X : ℕ) : ℝ))
      ≤ (Arows.card : ℝ))
    (hdens : θ ≤ ((retainedCols P Sc v.val).card : ℝ) / (Fintype.card Y : ℝ)) :
    ∃ (S : Finset Coord) (T : Finset X) (b : Bool),
      S ⊆ representedCoords P R A0 r v ∧ T ⊆ Arows ∧
        RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
          (frontierCopies r v.val.length kref) (tRef kref) 1 xT θ S T
          (retainedCols P Sc (v.val ++ [b])) := by
  have hmul : frontierCopies r v.val.length kref * tRef kref = kappaAt P R A0 r v :=
    frontierCopies_mul_tRef hcap
  refine exists_frontier_routedTriple P R A0 r v Sc Arows hY hbob hheavy ?_ ?_ ?_ hdens
  · exact frontierBlockCount_le_heavy_ceiling hk hcap
  · -- `WDFW-F13`: the binder is now the positivity the banked supply asks for.
    rw [hmul]; exact hpos
  · rw [hmul]; exact hA

/-- **The `09:1270--1274` restriction at the paper's own index tuple, BUILT.**

The banked `frontierRoutedRestriction` fired at a triple carried by the paper's
own indices.  General in the carriers, in `k_ref`, `x_T` and `theta`. -/
def paperFrontierRestriction [DecidableEq Coord] {r d kref : ℕ} {xT θ : ℝ}
    {S : Finset Coord} {T : Finset X} {K : Finset Y}
    (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
      (frontierCopies r d kref) (tRef kref) 1 xT θ S T K)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    RestrictionDatum.RestrictionDatum Coord X Y
      (frontierCopies r d kref) (tRef kref) 1 xT θ :=
  frontierRoutedRestriction htr hθ0 hθ1

omit [DecidableEq X] [DecidableEq Y] [Fintype Coord] in
/-- **`A:138`'s census at the paper's index tuple reads back `9 kappa_v/16`.**

The built restriction's block count is `r' p_t`, and Section 2 evaluates that to
`p_{kappa_v}` -- the frozen count of `09:1280--1283`.  So the object really is
indexed by the capacity the frontier derives, not by a free width.  General at
the frozen guards. -/
theorem paperFrontierRestriction_selCard [DecidableEq Coord] {r d kref : ℕ} {xT θ : ℝ}
    {S : Finset Coord} {T : Finset X} {K : Finset Y}
    (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
      (frontierCopies r d kref) (tRef kref) 1 xT θ S T K)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hk : 4 ≤ kref) (hcap : kref ≤ r - d) :
    (paperFrontierRestriction htr hθ0 hθ1).selCard
      = RestrictionDatum.certifiedPt (kappaFrontier r d) := by
  rw [paperFrontierRestriction, frontierRoutedRestriction,
    routedRestriction_selCard htr hθ0 hθ1 (le_refl 1)]
  exact frontierBlockCount_eq_certifiedPt_kappa hk hcap

end PaperTriple

/-! ## §5  The frozen dichotomy at a frontier node (`09:1269`, `09:1277--1283`) -/

section Dichotomy

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1269` versus `09:1277`, at a first-Bob node of the canonical system.**

"When `kappa_v >= t_{ref}` ..." and "When `2 <= kappa_v < t_{ref}` ...": the two
branches are exhaustive and disjoint, and the boundary `kappa_v = t_ref` belongs
to the **large** branch, exactly as `09:1269`'s non-strict inequality assigns it.
The lower bound `2 <= kappa_v` of the small branch is not assumed: it is
`09:1259`, already proved for every first-Bob node.  General. -/
theorem frontier_branch_dichotomy {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (kref : ℕ) :
    (tRef kref ≤ kappaAt P R A0 r v ∧ ¬ kappaAt P R A0 r v < tRef kref)
      ∨ (2 ≤ kappaAt P R A0 r v ∧ kappaAt P R A0 r v < tRef kref
          ∧ ¬ tRef kref ≤ kappaAt P R A0 r v) := by
  have htwo := two_le_kappaAt_of_firstBob hcomp hR hv
  by_cases h : tRef kref ≤ kappaAt P R A0 r v
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr ⟨htwo, by omega, h⟩

/-- **`09:1278`, `ell_v = log_2 kappa_v`, EVALUATED.**

"write `ell_v = log_2 kappa_v`."  At `kappa_v = 2^{r-d_v}` the frozen logarithm is
the capacity exponent `r - d_v`, so `ell_v` is a derived quantity of the node and
never an independent parameter.  General. -/
theorem log_kappaAt_eq_capacity_exponent (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode P R A0 r) :
    Nat.log 2 (kappaAt P R A0 r v) = r - v.val.length := by
  simp [kappaAt, kappaFrontier, stoppingCapacity]

/-- **`09:1283`'s cover-entry consequence, restated at the node-indexed
capacity.**

"`ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`."  Consumed by pin from the
banked `SplitFirstBobInstance.heavy_firstBob_smallCopyWidth_le`; the only content
added is that its `kappa_v` is the `kappaAt` of Section 1, which is `rfl`.

**Domain note (the statement is deliberately broader than the display).**
`09:440` defines `u_kappa = kappa/2 + 1` only on `4 <= kappa < t_ref`, and
`09:1283` is printed inside branch (ii)'s paragraph `2 <= kappa_v < t_ref`
(`09:1277`).  This declaration carries **no** upper guard -- it inherits the
banked theorem's generality -- so it asserts the cover-entry bound also at
`kappa_v >= t_ref`, where the frozen text does not define `u_kappa`.  That is a
*strengthening*, not a weakening, and it is true for the paper's own reason
(`09:1285--1287`: the cases `kappa_v = 2,4,8` directly, and `kappa_v >= 16` from
`9 kappa_v/16 >= kappa_v/2 + 1`).  The name's "smallBranch" records where the
display lives, **not** a guard the statement carries; a consumer needing the
branch restriction must add `kappaAt ... < tRef kref` itself.  General. -/
theorem smallBranch_coverEntry_at_kappaAt {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hheavy : vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) ≤ frontierWeight P R A0 r v) :
    smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card :=
  heavy_firstBob_smallCopyWidth_le hcomp hR hv hheavy

end Dichotomy

/-! ## §6  A general transcript family whose whole frontier is one first-Bob node

`09:1250` stops every routed branch "at its first Bob query".  A protocol whose
**root** is a Bob query is therefore the extreme legal case: every branch stops
at depth `0`, every started certificate is clean (`09:1236`), the frontier is the
single address `[]`, and `kappa_v = q` is maximal -- which puts the node squarely
inside branch (i)'s regime `kappa_v >= t_ref`.

Nothing here is an audit instance: the family is general in the carriers, the
Bob predicate, the leaf value, the coordinate type, `A_0` and `r`.  Section 7
instantiates it. -/

section BobRoot

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **A transcript whose root is a Bob query.**  The smallest protocol shape at
which `09:1250`'s first stopping rule fires immediately. -/
def bobRootTranscript (f : Y → Bool) (z : Z) : Protocol X Y Z :=
  Protocol.bNode f (Protocol.leaf z) (Protocol.leaf z)

omit [Fintype X] [DecidableEq X] in
/-- **Aux H1.**  Its root is a Bob node -- the `hbob` clause of the frontier
supply, at the root address.  General. -/
theorem bobRootTranscript_isBobNode (f : Y → Bool) (z : Z) :
    IsBobNode (descend (bobRootTranscript f z : Protocol X Y Z) ([] : List Bool)) :=
  trivial

omit [Fintype X] [DecidableEq X] in
/-- **Aux H2.**  Its root is not an Alice node, so the frozen routing rule
consumes no query.  General. -/
theorem bobRootTranscript_not_isANodeB (f : Y → Bool) (z : Z) :
    isANodeB (descend (bobRootTranscript f z : Protocol X Y Z) ([] : List Bool)) = false :=
  rfl

omit [Fintype X] [DecidableEq X] in
/-- **`09:1195--1200` at this family.**  The frame condition of
`lem:wrapper-no-bob-completion` holds for **every** `r`, by the two cases of the
banked `CompletedNoBob P r = forall p, IsAlicePath P p -> p.length < r ->
IsQueryNode (descend P p)`.  Only one of them is vacuous, and the docstring says
which: at `p = []` the condition is **discharged, not vacuous** -- the root is a
Bob query, hence a query node, which is exactly the conclusion demanded; at
`p = b :: q` the *hypothesis* is vacuous, since a protocol whose root is a Bob
query admits no Alice path of positive length.  General. -/
theorem bobRootTranscript_completedNoBob (f : Y → Bool) (z : Z) (r : ℕ) :
    CompletedNoBob (bobRootTranscript f z : Protocol X Y Z) r := by
  intro p hp _
  cases p with
  | nil => trivial
  | cons b q =>
      obtain ⟨⟨a, l, rr, hP⟩, -⟩ := hp
      simp [bobRootTranscript] at hP

omit [Fintype Coord] in
/-- **`09:1250` at this family.**  Every certificate stops at the root, so each
coordinate's stopping-address set is the singleton `{[]}`.  General in `R`, `A_0`
and `r`. -/
theorem bobRootTranscript_coordRoutes (f : Y → Bool) (z : Z) (R : Coord → Finset X)
    (A0 r : ℕ) (i : Coord) :
    coordRoutes (bobRootTranscript f z) R A0 r i = {([] : List Bool)} := by
  have hdesc : descendants (bobRootTranscript f z) (R i) A0 r r ([] : List Bool)
      = [([] : List Bool)] := by
    cases r with
    | zero => rfl
    | succ n =>
        refine descendants_of_stopped ?_
        rintro ⟨hcon, -⟩
        rw [bobRootTranscript_not_isANodeB] at hcon
        exact Bool.noConfusion hcon
  rw [coordRoutes, hdesc]
  simp

/-- **Aux H3.**  The root address is on the frontier as soon as one coordinate is
started.  General. -/
theorem bobRootTranscript_mem_frontierRoutes (f : Y → Bool) (z : Z) (R : Coord → Finset X)
    (A0 r : ℕ) (i : Coord) :
    ([] : List Bool) ∈ frontierRoutes (bobRootTranscript f z) R A0 r :=
  mem_frontierRoutes_of_mem_coordRoutes (i := i)
    (by rw [bobRootTranscript_coordRoutes]; exact Finset.mem_singleton_self _)

/-- **`09:1235--1236` with `09:1257`, EVALUATED at this family.**

"Start one clean reference certificate in every coordinate outside `E_0`", and
`W_v` is the total certificate weight at `v`.  Here every started coordinate
contributes exactly one clean certificate at the root, so `W_root` is the number
of started coordinates -- the frozen conservation `sum_v W_v >= q - e_0` attained
with equality at a single node.  Obtained by *evaluating* the banked
`frontierWeight_eq_sum_reaching` and `kindAlong_nil`; no weight is assigned.
General. -/
theorem bobRootTranscript_frontierWeight (f : Y → Bool) (z : Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode (bobRootTranscript f z) R A0 r) (hv : v.val = []) :
    frontierWeight (bobRootTranscript f z) R A0 r v = (Fintype.card Coord : ℝ) := by
  classical
  rw [frontierWeight_eq_sum_reaching]
  have hterm : ∀ i : Coord,
      (if v.val ∈ coordRoutes (bobRootTranscript f z) R A0 r i
        then (kindAlong (bobRootTranscript f z) (R i) A0 r v.val).weight else 0) = (1 : ℝ) := by
    intro i
    rw [if_pos (by rw [hv, bobRootTranscript_coordRoutes]; exact Finset.mem_singleton_self _)]
    rw [hv, kindAlong_nil]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp [Finset.card_univ]

omit [Fintype X] [DecidableEq X] in
/-- **`09:1250--1251` at this family.**  The root address is an exposed first-Bob
node for every positive `r`; in particular the `firstBob` flag of the canonical
system is `true` there.  General. -/
theorem bobRootTranscript_root_isFirstBob (f : Y → Bool) (z : Z) {r : ℕ} (hr : 0 < r) :
    IsFirstBobNode (bobRootTranscript f z : Protocol X Y Z) r ([] : List Bool) :=
  ⟨trivial, bobRootTranscript_isBobNode f z, by simpa using hr⟩

end BobRoot

/-! ## §7  Statement poles, and the joint-satisfiability audit instance

The three poles are about the **new** objects of Sections 1--3 and re-derive no
banked pole (see the R5 paragraph in the header). -/

section Poles

/-- **Statement pole 1 (`A:138`'s demand is positive at the paper's indices).**

The block count `r' p_t` demanded at `09:1272` is strictly positive throughout
the frozen guard range, so the trivial selection `S = empty` is refuted outright
at the paper's own index tuple -- which the predecessor could only state at free
indices.  General at `4 <= k_ref <= r - d_v`. -/
theorem paper_blockCount_is_positive {r d kref : ℕ} (hk : 4 ≤ kref) (hcap : kref ≤ r - d) :
    0 < frontierCopies r d kref * RestrictionDatum.certifiedPt (tRef kref) := by
  rw [frontierBlockCount_eq_certifiedPt_kappa hk hcap, RestrictionDatum.certifiedPt,
    kappaFrontier_eq]
  have hsplit : (2 : ℕ) ^ (r - d) = 16 * 2 ^ (r - d - 4) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    congr 1
    omega
  have hpos : 0 < (2 : ℕ) ^ (r - d - 4) := pow_pos (by norm_num) _
  rw [hsplit]
  omega

/-- **Statement pole 2 (a row-density clause is load-bearing at `x = 0`, whichever
form it takes).**

`09:1296` trims "to the row density `kappa_v x_T`", and the trimmed set must be
nonempty for `A:138`'s census to see the block at all.  At `x_T = 0` the frozen
row floor `ceil(r' t x m)` collapses to `0`, so *some* row-density clause is
needed in the frontier supply: without one the produced `T` may be empty and the
first clause of `RoutedTriple` is unobtainable.

**Renamed in tranche `cc-t5i`, round `r1`.**  The banked name was
`trim_nonemptiness_needs_hone`.  When it was chosen the clause was the
paper-shaped `hone : kappa_v x_T m_G >= 1`; `L1-F6` (tranche `cc-t5h`) replaced
it in the banked supply, and `WDFW-F13` replaced it here, by
`hpos : 0 < r' t x m`, so the old name pointed at a binder no statement in `src/`
carries any more.  A docstring instructing the reader to read a name in the past
tense is exactly the mitigation `WDFW-F14` was registered to reject, so the name
moves instead; the old name is **not** kept as an alias, which is safe because
the declaration is a statement pole consumed by nothing.  **No statement byte
moves.**

The pole itself survives the replacement intact, and the third conjunct below
says so: at `x = 0` the *current* binder fails as well.  What the retirement
removed was the gap between the two, not the pole -- see
`TranscriptLevelSuccessors.hone_can_fail_at_legal_positive_xT` for a *legal*
point separating them.  General. -/
theorem trim_nonemptiness_needs_a_row_density_clause (r' t m : ℕ) :
    RestrictionDatum.certifiedRowFloor r' t 0 m = 0
      ∧ ¬ (1 : ℝ) ≤ ((r' * t : ℕ) : ℝ) * 0 * (m : ℝ)
      ∧ ¬ (0 : ℝ) < ((r' * t : ℕ) : ℝ) * 0 * (m : ℝ) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp [RestrictionDatum.certifiedRowFloor]

/-- **Statement pole 3 (`09:1269`'s guard is load-bearing for the quotient).**

Below the branch condition the natural quotient `kappa_v/t_ref` is **not** the
paper's `r'`: at `r - d_v = 2` and `k_ref = 4` the exponent form gives
`frontierCopies = 1` while `r' t_ref = 16 > 4 = kappa_v`, so the `A:125` identity
`r' t = kappa_v` fails.  This is why `hcap` is carried explicitly in the headline
rather than inferred.  Concrete numerals here are a **refutation witness**; this
statement claims no legality. -/
theorem frontierCopies_needs_the_branch_guard :
    ∃ r d kref : ℕ, ¬ kref ≤ r - d
      ∧ frontierCopies r d kref * tRef kref ≠ kappaFrontier r d := by
  refine ⟨2, 0, 4, by norm_num, ?_⟩
  norm_num [frontierCopies, tRef, kappaFrontier, stoppingCapacity]

/-- **Non-vacuity of the paper's index tuple at legal widths.**

At any `4 <= k_ref <= r - d_v` the tuple `09:1272` prints is nondegenerate: `r'`
is positive, the branch condition `t_ref <= kappa_v` of `09:1269` holds, the
`A:125` identity `r' t_ref = kappa_v` is exact, and the demanded block count is
positive.  No numeral is assigned -- `k_ref`, `r` and `d_v` stay binders.
General. -/
theorem paper_indices_nondegenerate_at_legal_widths {r d kref : ℕ} (hk : 4 ≤ kref)
    (hcap : kref ≤ r - d) :
    0 < frontierCopies r d kref
      ∧ tRef kref ≤ kappaFrontier r d
      ∧ frontierCopies r d kref * tRef kref = kappaFrontier r d
      ∧ 0 < frontierCopies r d kref * RestrictionDatum.certifiedPt (tRef kref) :=
  ⟨frontierCopies_pos r d kref, (tRef_le_kappaFrontier_iff r d kref).mpr hcap,
    frontierCopies_mul_tRef hcap, paper_blockCount_is_positive hk hcap⟩

end Poles

/-! ### The joint-satisfiability audit instance

**NON-FIDELITY / BEYOND-PAPER.**  Everything in this subsection audits *our*
encoding at a point the frozen paper never visits, and it claims no legality:

* `k_ref = 4` satisfies every gate this module carries (`A:117--118`'s
  `16 | t_ref`), but `A:117` also forces `t_ref >= t_cert`, whose **value** is
  fixed at **`A:26`** as `t_cert = 2^{2^20}`, so the paper's own `k_ref` is
  astronomically larger.  This is the one clause that makes the instance an
  audit rather than the paper's instance.
* the instance sits at `d_v = 0` (the root is the whole frontier), so **no Alice
  query is routed and no certificate splits**: the weight bookkeeping of
  `09:1244--1248` and the halving of `09:1239--1243` are never exercised here.
  The bundle is shown satisfiable at the extreme legal shape, not at a shape
  where the frontier machinery does work; the stronger witness is named
  successor `L1-F4`.
* the alphabet `Fin 16`, the column alphabet `Bool`, the Bob predicate, the leaf
  value, the coordinate count `9`, the wrapper exponent `r = 4` and the depth
  `b_T = 5` are **ours**; the frozen text fixes none of them.

What is **not** ours, and is evaluated rather than assigned:

* `x_T = 2^{-b_T}` is the banked `xTdepth` (`08:166`) -- the paper's closed form,
  at our `b_T`;
* `A_0 = ceil(2 x_T m_G)` is the banked `initialRefRows` (`09:1219`) evaluated at
  those values, and `audit_A0_is_evaluated` proves the evaluation;
* `theta = rho = 18/25` is the banked `rhoSmall` (`09:436`);
* `kappa_v = 2^{r-d_v} = 16`, `r' = kappa_v/t_ref = 1` and `p_t = 9` are
  evaluations of Sections 1--2;
* `W_root = 9` is an evaluation of `frontierWeight`, by §6.

The point of the instance is a single fact the predecessor could not establish:
the heavy branch's premise bundle is **jointly satisfiable**.  Every clause below
is tight -- `W_v = vartheta kappa_v` exactly, `r' p_t = 9 kappa_v/16` exactly, and
the trim demand equals the certificate's row count exactly -- so the instance sits
on the frozen boundary rather than in a slack corner. -/

section Audit

/-- The audit transcript: a Bob query at the root (`09:1250`'s first stopping
rule, fired immediately).  **Ours**, per the BEYOND-PAPER label. -/
def auditProtocol : Protocol (Fin 16) Bool Bool :=
  bobRootTranscript (fun y => y) true

/-- The nine started outer coordinates and their reference rows.  Nine is not a
free choice: it is `p_{t_ref} = 9 t_ref/16` at `t_ref = 16`, i.e. `A:120`
evaluated, which is exactly the census `A:138` demands at this node. -/
def auditRows : Fin 9 → Finset (Fin 16) := fun _ => Finset.univ

/-- `x_T = 2^{-b_T}` (`08:166`) at our `b_T = 5`, through the banked `xTdepth`:
the paper's closed form, never a numeral shortcut of it. -/
noncomputable def auditXT : ℝ := xTdepth 5

/-- `A_0 = ceil(2 x_T m_G)` (`09:1219`) through the banked `initialRefRows`, at
`m_G = |Fin 16| = 16`.  Its value is computed, not assigned -- see
`audit_A0_is_evaluated`. -/
noncomputable def auditA0 : ℕ := initialRefRows auditXT 16

/-- **`09:1219` EVALUATED at the audit values.**  `A_0 = ceil(2 . 2^{-5} . 16) = 1`.
The numeral is an output of the frozen display, not an input. -/
theorem audit_A0_is_evaluated : auditA0 = 1 := by
  have h : (2 : ℝ) * auditXT * ((16 : ℕ) : ℝ) = 1 := by
    norm_num [auditXT, xTdepth]
  rw [auditA0, initialRefRows, h]
  simp

/-- **`09:1233--1235` at the audit instance.**  Every started coordinate retains
all `A_r = 2^4 A_0 = 16` reference rows, so the frozen retention holds with
equality. -/
theorem audit_hR : ∀ i : Fin 9, refRowFloor auditA0 4 ≤ (auditRows i).card := by
  intro i
  rw [audit_A0_is_evaluated, refRowFloor]
  simp [auditRows]

/-- **`09:1195--1200` at the audit instance**, from the general §6 family. -/
theorem audit_hcomp : CompletedNoBob auditProtocol 4 :=
  bobRootTranscript_completedNoBob _ _ 4

/-- The single frontier node of the audit instance: the root, an exposed
first-Bob node of depth `d_v = 0`. -/
def auditNode : FrontierNode auditProtocol auditRows auditA0 4 :=
  ⟨[], bobRootTranscript_mem_frontierRoutes _ _ auditRows auditA0 4 0⟩

/-- **Aux (the audit node's address).**  `d_v = 0`: the routing stops at the
root. -/
@[simp] theorem audit_node_val : auditNode.val = ([] : List Bool) := rfl

/-- **`09:1255` EVALUATED at the audit node.**  `kappa_v = 2^{4-0} = 16`, which is
the full width `q` of `09:105` -- the maximal legal capacity, and in particular
`>= t_ref = 16`, so the node lies in branch (i)'s regime with equality. -/
theorem audit_kappa : kappaAt auditProtocol auditRows auditA0 4 auditNode = 16 := by
  rfl

/-- **`09:1257` EVALUATED at the audit node.**  `W_root = 9`: nine clean
certificates of weight `1` each, by §6. -/
theorem audit_frontierWeight :
    frontierWeight auditProtocol auditRows auditA0 4 auditNode = 9 := by
  have h := bobRootTranscript_frontierWeight (X := Fin 16) (Y := Bool) (Z := Bool)
    (fun y => y) true auditRows auditA0 4 auditNode rfl
  exact h.trans (by simp)

/-- **The heavy premise bundle of `09:1268--1296` is JOINTLY SATISFIABLE.**

All six clauses of `exists_frontier_routedTriple_at_paper_indices` hold at once
at the audit instance, each of them **tight**:

* `4 <= k_ref` and `k_ref <= r - d_v` both hold with equality at `k_ref = 4`,
  `r - d_v = 4`; equivalently `t_ref = kappa_v = 16`, the boundary `09:1269`
  assigns to branch (i);
* `hbob`: the root is a Bob query;
* `hheavy`: `vartheta kappa_v = (9/16) . 16 = 9 = W_v`, satisfied with equality;
* the row-density clause: `kappa_v x_T m_G = 16 . 2^{-5} . 16 = 8`.  Since
  `WDFW-F13` the headline's own binder there is only `hpos : 0 < kappa_v x_T m_G`,
  and this witness deliberately keeps the **retired** and strictly stronger
  `1 <= kappa_v x_T m_G`, weakening it at the call in
  `audit_yields_paper_indexed_triple`.  Retiring a binder must not quietly
  weaken the evidence that the bundle is inhabited, so the clause is left at the
  stronger form it was verified at;
* `hA`: `2 kappa_v x_T m_G = 16 = |Arows|`, satisfied with equality;
* `hdens`: `theta = rho = 18/25 <= 1`, the root's retained column density.

This is the fact the predecessor's `live_firstBob_node_is_not_heavy` left open in
the other direction: the heavy condition is neither automatic nor unsatisfiable.
**It does not discharge the canonical-inhabitation obligation** -- see the
BEYOND-PAPER label above. -/
theorem heavy_frontier_bundle_is_jointly_satisfiable :
    (4 : ℕ) ≤ 4 ∧ (4 : ℕ) ≤ 4 - auditNode.val.length
      ∧ 0 < Fintype.card Bool
      ∧ IsBobNode (descend auditProtocol auditNode.val)
      ∧ vartheta * ((kappaAt auditProtocol auditRows auditA0 4 auditNode : ℕ) : ℝ)
          ≤ frontierWeight auditProtocol auditRows auditA0 4 auditNode
      ∧ 1 ≤ ((kappaAt auditProtocol auditRows auditA0 4 auditNode : ℕ) : ℝ) * auditXT
          * ((Fintype.card (Fin 16) : ℕ) : ℝ)
      ∧ 2 * (((kappaAt auditProtocol auditRows auditA0 4 auditNode : ℕ) : ℝ) * auditXT
          * ((Fintype.card (Fin 16) : ℕ) : ℝ))
          ≤ ((Finset.univ : Finset (Fin 16)).card : ℝ)
      ∧ rhoSmall ≤ ((retainedCols auditProtocol (Finset.univ : Finset Bool)
          auditNode.val).card : ℝ) / (Fintype.card Bool : ℝ) := by
  refine ⟨le_refl 4, by simp, by norm_num, bobRootTranscript_isBobNode _ _, ?_, ?_, ?_, ?_⟩
  · rw [audit_kappa, audit_frontierWeight, vartheta_val]; norm_num
  · rw [audit_kappa]; norm_num [auditXT, xTdepth]
  · rw [audit_kappa]; norm_num [auditXT, xTdepth]
  · rw [audit_node_val, retainedCols_nil]; norm_num [rhoSmall]

/-- **The audit instance produces an actual routed triple at the paper's index
tuple.**

The headline theorem fired at the satisfiable bundle: a genuine `(S,T,K)` with
`S` selected inside the node's own census, `T` inside the certificate's own rows,
and the triple indexed by `r' = kappa_v/t_ref = 1`, `t = t_ref = 16`,
`a^sharp = 1`.  **NON-FIDELITY**, per the BEYOND-PAPER label: it audits our
encoding, and does not exhibit the paper's object. -/
theorem audit_yields_paper_indexed_triple :
    ∃ (S : Finset (Fin 9)) (T : Finset (Fin 16)) (b : Bool),
      S ⊆ representedCoords auditProtocol auditRows auditA0 4 auditNode
        ∧ T ⊆ (Finset.univ : Finset (Fin 16))
        ∧ RoutedTriple (Blk := Fin 9) (Row := Fin 16) (Col := Bool)
            (frontierCopies 4 auditNode.val.length 4) (tRef 4) 1 auditXT rhoSmall S T
            (retainedCols auditProtocol (Finset.univ : Finset Bool)
              (auditNode.val ++ [b])) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := heavy_frontier_bundle_is_jointly_satisfiable
  exact exists_frontier_routedTriple_at_paper_indices auditProtocol auditRows auditA0 4
    auditNode Finset.univ Finset.univ h1 h2 h3 h4 h5 (lt_of_lt_of_le zero_lt_one h6) h7 h8

end Audit

end EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
