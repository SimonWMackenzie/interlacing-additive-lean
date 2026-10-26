import EthInapproximability.ParameterizedNP.TranscriptLevelJoin

/-!
# Parameterized NP route: the frozen branch dichotomy of `eq:wrapper-first-bob-light`

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
  and `sections/06-parameter-schedule.tex`
  (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`).
* **The exact frozen lines traced here**, in print order:
  * `09:1253--1257`, `d_v`, `kappa_v = 2^{r-d_v}` (`09:1255`) and `W_v`
    (`09:1257`);
  * `09:1259`, "Every first-Bob node has `kappa_v >= 2`";
  * `09:1268`, "Put `vartheta = 9/16`", with the shared heavy condition at
    `09:1269`, "We first close any first-Bob node satisfying
    `W_v >= vartheta kappa_v`";
  * **`09:1269`, the split itself** -- "When `kappa_v >= t_{ref}` ..." -- read at
    its printed **non-strict** inequality, so the boundary `kappa_v = t_ref`
    belongs to branch (i);
  * `09:1269--1276`, branch (i), consumed **by pin** as the banked
    `LargeCapacityBranch.canonical_firstBobLight_largeCapacity`;
  * `09:1277--1306`, branch (ii), consumed **by pin** as the banked
    `TranscriptLevelJoin.branchTwo_firstBobLight_join` and
    `..._at_paper_schedule`;
  * `09:1290` with `09:436` (`rho = 2y^2 = 18/25`), the display that makes the
    section's `y` a **DEFINED** quantity, `y = 3/5`, and therefore lets the two
    banked branches be joined at one value of `y` rather than at two;
  * `09:1291--1296`, the trim, carried through the schedule-indexed form;
  * `09:1307--1308`, "Its lower bound is one more bit than the remaining child
    budget in the alleged protocol" (the sentence begins at `09:1307`; the
    enclosing residual-budget clause runs `09:1306--1308`);
  * **`09:1309--1313`, `eq:wrapper-first-bob-light`**, `W_v < vartheta kappa_v`
    at every first-Bob node -- the dichotomy's target, reached here at the
    honest extent described below.
* **Cross-anchors opened first-hand this tranche:** `09:105` (`q = 2^r`),
  `09:113--116` (`m_G = |Rows(G)|`), `09:305--306`
  (`eq:wrapper-low-simple-gate`), `09:314--315` (the endpoint's fixed
  `y_* = 3/5`), `09:436` (`rho = 2y^2 = 18/25`), `09:1137` (`z = y = 3/5`, the
  same value read at the terminal Stage-3 lift), `09:1188--1194` (the **alleged**
  `(C+r-1)`-bit protocol), `09:1219` (`A_0 = ceil(2 x_T m_G)`), `09:1302--1304`
  (`C >= 3`; the legality chain), `A:117--118` (`16 | t`, exponent form
  `4 <= k`), `A:125`, `A:138--141`, and `eq:tref-search` `06:558--571`
  (`t_ref = 2^{k_ref}` with `k_ref >= 2^19`).

## What this tranche does, and the exact extent of it

`TRANSCRIPT-LEVEL-JOIN-001` registered, in its own unwired census, that
`branchTwo_firstBobLight_join_at_paper_schedule` "is wired when the branch
dichotomy lands (`canonical_firstBobLight_largeCapacity` joined with branch (ii)
into an unconditional `eq:wrapper-first-bob-light`, which additionally requires
`hselect`)".  That join is this module, and the parenthesis is respected
literally.

`canonical_firstBobLight_dichotomy` **performs the split of `09:1269`** at a
first-Bob node of `FrontierIndexing.canonicalSystem`: the banked
`TranscriptLevelConstruction.frontier_branch_dichotomy` exhausts the two cases,
branch (i) discharges the case `t_ref <= kappa_v` and branch (ii) the case
`kappa_v <= t_ref`, and the conclusion `W_v < vartheta kappa_v` carries **no
branch guard**.  What it does carry is every hypothesis the two banked branches
carry, inherited **explicitly and by name**:

* **`hselect`** -- branch (ii)'s projection/selection step `09:1287--1296` -- is
  a named explicit binder, exactly as in the predecessor.  It is **still
  GAP-EXPOSED**: `09:1287--1290` is narrowed by nothing here, and the
  projection-at-a-node discharge (a node-level projection lemma plus a
  restriction-to-subtree bridge relating `NPCC.LambdaGE` to `(descend P _).cost`)
  is held as a **successor**, not attempted.
* **`hLocEx`** -- branch (i)'s certified-scale endpoint `A:109--146`, the place
  `EXPANDER-001` would enter -- is a named explicit binder, never an `axiom` and
  never a premise-bundle field.
* The residual-budget clause of `09:1306--1308` is inherited **twice**, once in
  each banked branch's own shape: `hbudget` against branch (i)'s abstract
  residual budget `B`, and `hcost` against the alleged protocol's own cost on
  branch (ii).  They are not two independent assumptions -- `A3`
  (`paper_residual_budget_is_one_bit_short`) proves they are the paper's single
  budget read twice, and that the endpoint output then exceeds it by **exactly
  one bit**.

So "unconditional" here means *unconditional in the capacity split*, and in
nothing else.  The dichotomy is not a route completion, does not prove
`thm:first-wrapper`, and does not narrow any certificate residue.

### The tranche's one deflationary finding

A conditional theorem earns its keep only if its bundle excludes something, and
the predecessor measured that by firing its join at a routed system where the
conclusion is false.  **The same measurement is not available to the dichotomy,
and the reason is arithmetic.**  `hk : 4 <= k_ref` with `hq4 : k_ref + 2 <= r`
forces `6 <= r`, so the smallest instance the joined statement can be fired at
has `r = 6` and hence `k_ref = 4`; and at `k_ref = 4` branch (i)'s `hE2` is
**false outright** for every `theta <= 1`, since
`h_{t} = 2^{-2^{49/50}} > 2^{-6}`.  A `False` derived there would be a fact about
`hE2`, not a measurement of the join -- precisely the defect the predecessor's
`r1` round was parked on.  So no such pole is landed; instead
`branchOne_analytic_binder_fails_below_the_tref_floor` proves the obstruction
itself in the kernel, and `dichotomy_split_is_two_sided` supplies what *can*
honestly be shown -- that the capacity split bifurcates on both sides at one
schedule tuple.  Full-bundle satisfiability is **not** exhibited and is **not**
claimed; `eq:tref-search`'s `k_ref >= 2^19` puts the inhabited regime beyond any
finite check, which is exactly why `k` is universally quantified here.

### The one interface decision, and why it is forced (DEFINED-vs-FREE)

The two banked branches disagree, on their face, about the density parameter of
the base certificate: branch (i) is stated at the literal `3/5`, branch (ii) at a
free real `y` with `0 < y <= 1`.  Joining them requires knowing whether `y` is
ours to choose.  It is **not**: `09:436` prints `rho = 2y^2 = 18/25`, which
**defines** `y` on the nonnegative reals, and the same value is printed again at
`09:314--315` (`y_* = 3/5`) and at `09:1137` (`z = y = 3/5`).  `A1`
(`wrapper_y_is_pinned_by_rho`) proves the uniqueness direction outright -- the
banked `WrapperProjectionCovers.rhoSmall_eq_two_y_sq` is the *existence*
direction and is consumed, not restated -- so instantiating branch (ii) at
`y = 3/5` is an **evaluation of the frozen definitional chain**, not a chosen
numeral.  Nothing else in the join has a free input: `kappa_v`, `ell_v`, `t_ref`,
`vartheta`, `A_0`, `x_T`, `m_G`, `r` and `k_ref` are all DEFINED and enter as
universally quantified binders or as banked reifications, and `C` -- the one
genuinely free input -- appears only under `09:1302`'s own floor `C >= 3`.

## Reader counterpart: NONE claimable, re-verified first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was searched again, this
round, for `vartheta`, `first Bob`, `first-Bob`, `firstBob` and `9/16`.  The
search returns **one** hit in the whole artifact, `02-preliminaries.tex:301`,
"not stable under the first Bob bit" -- motivating prose for
`thm:paper-density-amplification`, about a *bundled density statement*, not
about the routed certificate weight of a frontier node.  The only other trace of
this frozen block is the unnumbered connective prose at
`A-stage4-details.tex:385--392`, opened again and confirmed verbatim; prose
inside a proof may not be cited as a statement, and the one numbered item it
points at, `lem:paper-certified-row-ladder`, is **already claimed by
`TerminalTwoStream`**.  `eq:wrapper-first-bob-light` has no reader counterpart
and neither does the capacity dichotomy, so **no declaration of this module
claims one** and the trace is recorded once, here.

## Canonical inhabitation

This module defines **no `structure` and no `inductive`**, so it opens no new
canonical-inhabitation obligation.  The inherited one is **REGISTERED and
DEFERRED**, unchanged: the paper's own instance at `09:1268` is a function of the
**alleged** `(C+r-1)`-bit protocol of `09:1188--1194` computing a member of
`<U,1,1-delta_U,theta>`, an object whose non-existence *is* the conclusion of the
whole argument.  There is therefore no paper instance to exhibit, the honest Lean
form is the implication each theorem below states, and every numeric readout in
Section 3 is labelled **NON-FIDELITY / BEYOND-PAPER** and discharges **nothing**.

## Residues this module does NOT close (named, not implied)

* **`09:1287--1290` stays GAP-EXPOSED.**  `hselect` is carried, not discharged;
  the projection-at-a-node lemma and the `LambdaGE`-to-subtree-cost bridge are a
  registered **successor**.
* **`L1-F6`** (retire the redundant `hone` binder from `WrapperDenseFrontierWiring`)
  is carried, unedited: `hone` is an *extra* hypothesis relative to `09:1291--1296`
  and is inherited from the banked `exists_branchTwo_trimmed_rows`.
* **`L1-F7`** (the predecessor's docstring attributes `m_G` to `09:1270`, which
  defines nothing; the correct anchor is `09:113--116`) is carried as a
  record-only repair of `TranscriptLevelSuccessors`, untouched here.
* `thm:certified-localized-extension` (`A:285--329`), `lem:certified-row-ladder`'s
  own proof and `ReferenceStoppingEndpoint` are consumed by pin, neither
  re-derived nor discharged; `A:139--140`'s per-block row floor remains inside
  `hLocEx`'s restriction data.
* Residues **L1a** (`09:1203--1207`) and **L1b** (`09:1224--1235`) enter only as
  the banked binders `CompletedNoBob` and the retention floor.
* `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-u-dense` is not approached; `hDenseRung` is neither discharged nor
  fed; `thm:first-wrapper` is **not** proved; **no route completion is claimed,
  and none may be inferred.**
* `TranscriptLevelJoin.select_bound_mono` stays **unwired**.  It converts a
  selection bound stated against a smaller budget into one against a larger
  budget; the dichotomy states each branch's budget clause in that branch's own
  banked shape and performs no budget weakening, so wiring it here would be
  decoration.  Recorded rather than silently left.

## Unwired census of this module's own declarations

Of the seven declarations below, exactly **one** -- `A2`
(`branchOne_guard_closes_branchTwo_entry`) -- is consumed by another proof term
in this module; it is called by both Section-2 theorems and by
`dichotomy_split_is_two_sided`.  The other **six are consumed by no proof term**,
and each is an endpoint by design rather than an oversight:

* `A1` (`wrapper_y_is_pinned_by_rho`) and `A3`
  (`paper_residual_budget_is_one_bit_short`) are **justification lemmas**: they
  make this module's two interface readings checkable in the kernel instead of
  asserted in prose -- `A1` that `y = 3/5` is an evaluation of `09:436` and not a
  chosen numeral, `A3` that the two inherited budget binders are `09:1307--1308`'s
  single budget with an exact one-bit margin.  Neither is *invoked* by the
  dichotomy's term (branch (ii) is instantiated at the literal `3/5`, whose side
  conditions close by `norm_num`), and that is deliberate: they certify the
  reading, they do not participate in it.  Wiring either one into the term would
  not strengthen anything.
* `canonical_firstBobLight_dichotomy` and
  `canonical_firstBobLight_dichotomy_at_paper_schedule` are this tranche's
  **deliverables** and have no consumer yet.  Their wiring target is the assembly
  of `thm:first-wrapper`, which cannot consume them until `hselect` is discharged
  by successor **`L1-F8`**; until then any consumer would only propagate the same
  two named binders.
* `dichotomy_split_is_two_sided` and
  `branchOne_analytic_binder_fails_below_the_tref_floor` are **measurement
  endpoints** (`NON-FIDELITY / BEYOND-PAPER`), consumed by nothing by
  construction.

## Axioms and imports

The sole import is `TranscriptLevelJoin`, whose transitive closure already
carries `LargeCapacityBranch` (it is `open`ed by `TranscriptLevelConstruction`).
`LegacyNPCC.Stage12` is **not** in that closure, so the cited AGHP balanced-family
axiom is unreachable from every declaration here, and **`EXPANDER-001` occurs in
no hypothesis**: where the frozen paper uses the balanced family it is the named
binder `hLocEx`.  No `axiom`, no opaque certificate, no premise bundle.
-/

namespace EthInapproximability.ParameterizedNP.FirstBobLightDichotomy

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.LargeCapacityBranch
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors
open EthInapproximability.ParameterizedNP.TranscriptLevelJoin

/-! ## §1  The three general facts the join needs

Everything in this section is **general**: in the reals, in `C`, `r`, `d_v` and
`k_ref`.  Nothing is evaluated and no instance is chosen. -/

section Aux

/-- **`A1` (`09:436`): the section's `y` is DEFINED, and `3/5` is the only value
it can take.**

"`rho = 2y^2 = 18/25`."  The banked `WrapperProjectionCovers.rhoSmall_eq_two_y_sq`
records the *existence* direction, `2 (3/5)^2 = rho_small`, and is consumed here
rather than restated.  What the join needs is the **uniqueness** direction: on
the nonnegative reals the frozen display has exactly one solution, so the value
`y = 3/5` at which branch (ii) is instantiated below is an evaluation of the
frozen definitional chain and not a chosen numeral.  (Nonnegativity is not an
extra assumption smuggled in: `y` is a density, and branch (ii)'s own binder
`hy0 : 0 < y` is stronger.)

The corroborating displays are `09:314--315`, the endpoint's fixed `y_* = 3/5`,
and `09:1137`, `z = y = 3/5` at the terminal Stage-3 lift; all three print the
same constant.  General in `y`. -/
theorem wrapper_y_is_pinned_by_rho {y : ℝ} (hy : 0 ≤ y) (hrho : 2 * y ^ 2 = rhoSmall) :
    y = 3 / 5 := by
  have h : (y - 3 / 5) * (y + 3 / 5) = 0 := by
    have : 2 * y ^ 2 = 18 / 25 := by rw [hrho]; unfold rhoSmall; norm_num
    nlinarith [this]
  rcases mul_eq_zero.mp h with h₁ | h₂
  · linarith
  · linarith

/-- **`A2` (`09:1269` read at its printed non-strict inequality): the boundary
belongs to branch (i), and branch (i)'s guard closes branch (ii)'s entry.**

"When `kappa_v >= t_{ref}` ..." is printed with `>=`, so the boundary
`kappa_v = t_ref` is branch (i)'s.  In exponent form (`t_ref = 2^{k_ref}`,
`06:558--569`; `kappa_v = 2^{r-d_v}`, `09:1255`) that is `k <= r - d_v`, and the
consequence the join actually consumes is the **negative** one: under branch
(i)'s guard the entry condition of branch (i)'s own small-capacity binder,
`r - d_v < k`, cannot hold.  This is what lets the banked
`canonical_firstBobLight_largeCapacity` be fired on the large side with its
`hsmall` binder discharged vacuously, rather than being supplied with a second
closure it does not need.

Clause 3 is the boundary case itself, stated separately so that the non-strict
reading is recorded and not merely used: at `t_ref = kappa_v` the split lands on
branch (i).

Obtained by *calling* the banked `tRef_le_kappaFrontier_iff`, not by re-deriving
the exponent comparison.  General in `r`, `d` and `k`. -/
theorem branchOne_guard_closes_branchTwo_entry (r d k : ℕ) (h : tRef k ≤ kappaFrontier r d) :
    k ≤ r - d ∧ ¬ (r - d < k) ∧ (tRef k = kappaFrontier r d → k ≤ r - d) := by
  have hk : k ≤ r - d := (tRef_le_kappaFrontier_iff r d k).mp h
  exact ⟨hk, by omega, fun _ => hk⟩

/-- **`A3` (`09:1306--1308`): the paper's single budget, read as branch (i)'s
abstract `B`, and the exact one-bit margin.**

"Its lower bound is one more bit than the remaining child budget in the alleged
protocol."  The dichotomy inherits the budget clause twice -- `hbudget` against
branch (i)'s abstract residual budget and `hcost` against the alleged protocol's
own cost -- and this records that the two are the *same* frozen budget: at the
node's own residual value `B = (C+r-1) - (d_v+1)`, branch (i)'s `hbudget` holds,
and the endpoint output `(C-1) + (r-d_v)` of `09:1276` is then `B + 1` **exactly**.

So the frozen contradiction is a one-bit margin and not a slack inequality: if
the margin were two or more bits the argument would still run, but if it were
zero it would not, and clause 2 pins which of those the frozen text has.
General in `C`, `r` and `d` at the frozen `C >= 3` (`09:1302`) and the exposure
rule `d_v < r` (`09:1251--1252`). -/
theorem paper_residual_budget_is_one_bit_short {C r d : ℕ} (hC : 3 ≤ C) (hd : d < r) :
    (C + r - 1 - (d + 1)) + (d + 1) ≤ C + r - 1
      ∧ (C - 1) + (r - d) = (C + r - 1 - (d + 1)) + 1 := by
  refine ⟨by omega, by omega⟩

end Aux

/-! ## §2  The dichotomy (`09:1268--1313`)

The frozen split of `09:1269` performed at a first-Bob node of
`FrontierIndexing.canonicalSystem`, joining the two banked branches into
`eq:wrapper-first-bob-light` with **no branch guard** in the statement. -/

section Dichotomy

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`), the branch dichotomy of
`09:1268--1313` performed.**

"Therefore `W_v < vartheta kappa_v` at every first-Bob node `v`."

At a first-Bob node of `FrontierIndexing.canonicalSystem` the conclusion is
reached with **no capacity guard**: `frontier_branch_dichotomy` exhausts
`09:1269`'s split at its printed non-strict inequality, and

* on `t_ref <= kappa_v` the banked
  `LargeCapacityBranch.canonical_firstBobLight_largeCapacity` closes the node --
  its own `hsmall` binder is discharged **vacuously** by `A2`, because branch
  (i)'s guard forbids that binder's entry condition, so no second closure is
  invented for the large side;
* on `kappa_v <= t_ref` the banked
  `TranscriptLevelJoin.branchTwo_firstBobLight_join` closes it, instantiated at
  `y = 3/5` -- which `A1` proves is the *only* value `09:436` permits, so the
  two banked branches are joined at one evaluated `y` and not at two free ones.

Both branches are consumed **by pin**; nothing they prove is re-derived, and
neither statement is weakened.  The boundary `kappa_v = t_ref` goes to branch
(i), exactly as `09:1269` assigns it.

**What is inherited, and stays visible.**  `hLocEx` is branch (i)'s certified-scale
endpoint (`A:109--146`), the place `EXPANDER-001` would enter; `hselect` is branch
(ii)'s projection/selection step (`09:1287--1296`), which is **GAP-EXPOSED item
15** of `SPLIT-FIRST-BOB-INSTANCE-001` and is narrowed by nothing here.  Both are
explicit named binders -- never an `axiom`, never a premise-bundle field.  The
budget of `09:1306--1308` is inherited in each branch's own shape (`hbudget` with
branch (i)'s abstract `B`, `hcost` with the alleged protocol's cost); `A3` shows
these are the paper's single budget read twice, with the frozen one-bit margin.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
two named quantities of the routed system, not an existential, so the question is
whether it can fail at all -- and it can: the banked
`TranscriptLevelJoin.interiorAudit_is_not_light` exhibits a routed system whose
first-Bob node meets the heavy threshold with **equality**, `W_v = 9/2 =
vartheta . 8`, so `eq:wrapper-first-bob-light` is false there and is not an
arithmetic tautology.  That refutation is **not** fired against this theorem's
full bundle, and §3's `branchOne_analytic_binder_fails_below_the_tref_floor`
proves why no honest firing is available: every instance small enough to compute
with already refutes branch (i)'s `hE2` on its own, so the resulting `False`
would measure `hE2` rather than the join.  The banked
`interiorAudit_forces_a_join_hypothesis_to_fail` remains the measurement of
branch (ii)'s side, where it localises the exclusion to `hbase` and `hselect`.

General in the matrix carriers, in the three protocol carriers, in `Coord`, `P`,
`R`, `A_0`, `r`, the node, `C`, the residual budget `B`, `k_ref`, `t_cert`, and
the real parameters `x_T`, `theta` and the column density. -/
theorem canonical_firstBobLight_dichotomy {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
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
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
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
    (hselect : smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card →
      LambdaGE Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
          (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) ((3 / 5 : ℝ) ^ 2)
        ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R A0 r v < vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) := by
  rcases frontier_branch_dichotomy hcomp hR hv k with ⟨hge, -⟩ | ⟨-, hlt, -⟩
  · obtain ⟨hexp, hnot, -⟩ := branchOne_guard_closes_branchTwo_entry r v.val.length k hge
    rw [kappaAt_eq_capacity hcomp hR v]
    exact canonical_firstBobLight_largeCapacity Gmat hcomp hR hv hC hk hq4 hxT0 hxT1 hθ0 hθ1
      hGne hgate hbase htcert hE1 hE2 hcol hbudget hLocEx (fun hb _ => absurd hb hnot)
  · exact branchTwo_firstBobLight_join (y := 3 / 5) Gmat hcomp hR b hv hcost hC hGne hCne
      hxT0 (by norm_num) (by norm_num) hbase (le_of_lt hlt) hq4 hgate hselect

/-- **The dichotomy at the paper's own row schedule, carrying the executed
trim.**

Same split, with `A_0` pinned to `09:1219`'s `ceil(2 x_T m_G)` through the banked
`initialRefRows` (`m_G` read at the row carrier, `A:111` with `09:113--116`) and
the node sitting on coordinate `i`'s route.  The second conjunct is
`09:1291--1296` **executed**: the certificate's own rows at that address, trimmed
to the frozen floor `ceil(kappa_v x_T m_G)`, nonempty.

This is the declaration `TRANSCRIPT-LEVEL-JOIN-001`'s unwired census named:
`branchTwo_firstBobLight_join_at_paper_schedule` "is wired when the branch
dichotomy lands", and it is wired here -- on branch (ii) the schedule-indexed
join is called whole, so its trim conjunct comes from the join itself; on branch
(i), where that join does not apply, the same trim is supplied by the banked
`exists_branchTwo_trimmed_rows` it is built from.  The trim is a fact of the
routing and the retention floor, not of the capacity branch, which is why it
survives the split.

`hone` is inherited, not introduced: it is an **extra** hypothesis relative to
`09:1291--1296` -- the frozen trim demands no such clause -- and retiring it is
the open **`L1-F6`**, an edit to `WrapperDenseFrontierWiring` and therefore its
own tranche.

*Why the trivial witness fails.*  `T = empty` is refuted by the `Nonempty`
conjunct, which `hone` forces through the frozen floor; and the light conjunct is
refutable exactly as in the predecessor statement.

General in the carriers, `P`, `R`, `r`, the node, the coordinate, `C`, `B`,
`k_ref`, `t_cert`, `x_T`, `theta`, the column density and the selected bit. -/
theorem canonical_firstBobLight_dichotomy_at_paper_schedule {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X}
    {r : ℕ} {xT : ℝ}
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
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
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
    (hselect :
      smallCopyWidth (kappaAt P R (initialRefRows xT (Fintype.card X)) r v)
          ≤ (representedCoords P R (initialRefRows xT (Fintype.card X)) r v).card →
      LambdaGE Gmat
          (2 ^ (Nat.log 2 (kappaAt P R (initialRefRows xT (Fintype.card X)) r v) - 1) + 1)
          (((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT)
          ((3 / 5 : ℝ) ^ 2)
        ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R (initialRefRows xT (Fintype.card X)) r v
        < vartheta
          * ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ)
      ∧ ∃ T ⊆ rowsAt P (R i) v.val,
          T.card = ⌈((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
              * ((Fintype.card X : ℕ) : ℝ)⌉₊
            ∧ T.Nonempty := by
  rcases frontier_branch_dichotomy hcomp hR hv k with ⟨hge, -⟩ | ⟨-, hlt, -⟩
  · obtain ⟨hexp, hnot, -⟩ := branchOne_guard_closes_branchTwo_entry r v.val.length k hge
    refine ⟨?_, exists_branchTwo_trimmed_rows (hR i) hp hone⟩
    rw [kappaAt_eq_capacity hcomp hR v]
    exact canonical_firstBobLight_largeCapacity Gmat hcomp hR hv hC hk hq4 hxT0 hxT1 hθ0 hθ1
      hGne hgate hbase htcert hE1 hE2 hcol hbudget hLocEx (fun hb _ => absurd hb hnot)
  · exact branchTwo_firstBobLight_join_at_paper_schedule (y := 3 / 5) Gmat hcomp hR i b hp hv
      hcost hC hGne hCne hxT0 (by norm_num) (by norm_num) hbase (le_of_lt hlt) hq4 hgate hone
      hselect

end Dichotomy

/-! ## §3  What the dichotomy costs, measured

Two things a green build cannot see: whether the **split** is degenerate (one
branch never taken), and how much of the joined bundle any finite check can
reach.  Both are settled here -- the first affirmatively, the second by a
kernel-visible obstruction rather than by a pole that would measure nothing.

**NON-FIDELITY / BEYOND-PAPER** throughout.  The tuple `(r, k_ref, C) = (6, 4, 3)`
is the banked probes' -- `06:561--563` alone forces `k_ref >= 2^19` and `A:117`
with `A:26` forces `t_ref >= t_cert = 2^{2^20}`.  Nothing here is the paper's
instance and nothing here discharges canonical inhabitation. -/

section Measurement

/-- **The split of `09:1269` is TWO-SIDED: both branches are entered at one and
the same schedule tuple.**

A dichotomy whose second case never occurs is a theorem with a decorative case
split, and a green build cannot tell the difference.  At the single tuple
`r = 6`, `k_ref = 4`, `C = 3` with `x_T` the banked closed-form gate accessor,
**both** guards of `09:1269` are live, distinguished only by the node's depth:

* clauses 1--2: at `d_v = 2` the capacity is `2^4 = 16 = t_ref`, so branch (i)'s
  guard holds -- at the **boundary**, which `09:1269`'s non-strict inequality
  assigns to branch (i) -- and branch (i)'s small-capacity entry condition
  correspondingly fails, by `A2`;
* clauses 3--4: at `d_v = 3` the capacity is `2^3 = 8 < 16`, so branch (ii)'s
  guard holds and `09:1277`'s upper guard is **strict**, i.e. the node is in the
  interior of branch (ii) rather than on the boundary;
* clause 5: both depths are legal frontier depths at `r = 6` (`d_v < r`,
  `09:1251--1252`);
* clause 6: the shared gate `eq:wrapper-low-simple-gate` holds at the **one**
  `x_T` used on both sides, obtained by calling
  `WrapperLowRungs.wrapperLowRungGates_legal_instance 4 6` rather than by
  writing the numeral `2^{-22}`.

So neither branch of the dichotomy is vacuous, and the two banked branch
theorems are being joined across a split that genuinely bifurcates without any
schedule parameter having to change.

**Scope, stated precisely.**  What is inhabited here is the **capacity and gate**
group -- the two branch guards, the depth legality of `09:1251--1252` and
`eq:wrapper-low-simple-gate`.  Branch (i)'s *analytic* binders `hE1`, `hE2` and
`hLocEx` are **not** inhabited at this tuple and cannot be: the next declaration
proves `hE2` is outright false at `k_ref = 4`, which is the only exponent
`hk` and `hq4` permit at `r = 6`.  Full-bundle satisfiability is therefore **not**
exhibited and is not claimed; two-sidedness of the *split* is.

**BEYOND-PAPER AUDIT** in `(r, d_v, k_ref) = (6, 2, 4)` and `(6, 3, 4)`; `C = 3`
is `09:1302`'s own floor. -/
theorem dichotomy_split_is_two_sided :
    tRef 4 ≤ kappaFrontier 6 2
      ∧ ¬ (6 - 2 < 4)
      ∧ kappaFrontier 6 3 < tRef 4
      ∧ kappaFrontier 6 3 ≤ tRef 4
      ∧ (2 < 6 ∧ 3 < 6)
      ∧ ((2 : ℝ) ^ (6 : ℕ)) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025 := by
  obtain ⟨-, -, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  have hbig : tRef 4 ≤ kappaFrontier 6 2 := by
    norm_num [tRef, kappaFrontier, stoppingCapacity]
  obtain ⟨-, hnot, -⟩ := branchOne_guard_closes_branchTwo_entry 6 2 4 hbig
  refine ⟨hbig, hnot, ?_, ?_, ⟨by norm_num, by norm_num⟩, by rw [hval]; norm_num⟩
  · norm_num [tRef, kappaFrontier, stoppingCapacity]
  · norm_num [tRef, kappaFrontier, stoppingCapacity]

/-- **Why the dichotomy's joined bundle admits NO probe: branch (i)'s analytic
binder fails at every exponent a decidable instance can reach.**

The natural pole for a conditional theorem is a routed system where the
conclusion is false, fired against the full bundle.  For the **join** that pole
exists and is banked (`TranscriptLevelJoin.interiorAudit_forces_a_join_hypothesis_to_fail`,
at `interiorAudit`, where the exclusion localises to `hbase` and `hselect`).
For the **dichotomy** it does not, and the reason is arithmetic rather than
missing effort, so it is recorded in the kernel instead of asserted in prose.

* Clause 1: the two schedule binders `hk : 4 <= k_ref` (`A:117--118`, `16 | t`
  in exponent form) and `hq4 : k_ref + 2 <= r` (`09:327`) force `6 <= r`.  So the
  smallest instance the dichotomy can be fired at has `r = 6`, and there
  `k_ref = 4` is the only permitted exponent.
* Clause 2: at `k_ref = 4` branch (i)'s `hE2` -- `eq:certified-E2` (`A:135--136`,
  the second line of the `align` block `A:130--137`, whose first line `A:134`
  carries `eq:certified-E1`) with the inherited `h_t` pinned to
  `HardSeedFacade.hardSeedColumnDensity` (`D:484`) -- is **false for every**
  `theta <= 1`, at `09:1302`'s own `C = 3`.
  Concretely `h_{t} = 2^{-2^{0.49 sqrt 4}} = 2^{-2^{49/50}} > 2^{-6}`, because
  `2^{49/50} < 2 < 6`; the demand `h_t <= theta . 2^{-(C-1+k)}` is off by more
  than four binary orders of magnitude (`2^{49/50} = 1.9724...`, so the ratio is
  `2^{4.027...}`).

Together these say: **any** instance small enough for `decide` already refutes a
branch-(i) hypothesis on its own, so a `False` derived there would be a fact
about `hE2` and not a measurement of the joined statement.  Landing such a
"pole" would repeat exactly the defect the predecessor's `r1` round was parked
on -- a pole placed where two binders are incompatible by themselves.  None is
landed here.

This is not a defect of the dichotomy; it is `eq:tref-search` doing its work.
`06:558--571` forces `k_ref >= 2^19`, and at that scale `2^{0.49 sqrt k}` dwarfs
`C - 1 + k`, so `hE2` holds with enormous room.  The honest consequence is that
branch (i)'s analytic bundle is inhabited only at exponents no finite check can
enumerate, which is why `k` is universally quantified everywhere in this route
and why the canonical-inhabitation obligation is REGISTERED and DEFERRED rather
than probed.

**BEYOND-PAPER AUDIT** in `C = 3` and `k_ref = 4`: both are *rejection* values
here, claimed illegal rather than legal, which is the one place the discipline
permits values that are not the paper's. -/
theorem branchOne_analytic_binder_fails_below_the_tref_floor :
    (∀ k r : ℕ, 4 ≤ k → k + 2 ≤ r → 6 ≤ r)
      ∧ ∀ θ : ℝ, θ ≤ 1 →
          ¬ (HardSeedFacade.hardSeedColumnDensity 4
              ≤ θ * (2 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 1 + ((4 : ℕ) : ℝ)))) := by
  refine ⟨fun k r hk hq => by omega, ?_⟩
  intro θ hθ hle
  have hsqrt : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show (((4 : ℕ) : ℝ)) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hexp : (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((4 : ℕ) : ℝ)) < 6 := by
    rw [hsqrt]
    have h1 : (2 : ℝ) ^ ((49 / 100 : ℝ) * 2) < (2 : ℝ) ^ (1 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by norm_num)
    rw [Real.rpow_one] at h1
    linarith
  have hpow : (2 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 1 + ((4 : ℕ) : ℝ)))
      < HardSeedFacade.hardSeedColumnDensity 4 := by
    unfold HardSeedFacade.hardSeedColumnDensity
    refine (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr ?_
    push_cast
    linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 1 + ((4 : ℕ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : θ * (2 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 1 + ((4 : ℕ) : ℝ)))
      ≤ (2 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 1 + ((4 : ℕ) : ℝ))) :=
    mul_le_of_le_one_left hpos.le hθ
  linarith

end Measurement

end EthInapproximability.ParameterizedNP.FirstBobLightDichotomy
