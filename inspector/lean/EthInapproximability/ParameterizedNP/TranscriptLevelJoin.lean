import EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors

/-!
# Parameterized NP route: the `L1-F5` branch-(ii) join

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche, after the last edit to the file it pins.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:1250--1252`**, the two stopping rules and the exposure rule.
    * **`09:1253--1257`**, `d_v`, `kappa_v = 2^{r-d_v}` (`09:1255`), `W_v`.
    * **`09:1259`**, "Every first-Bob node has `kappa_v >= 2`".
    * **`09:1268`**, `Put \vartheta=9/16`.  The heavy condition itself,
      `W_v >= vartheta kappa_v`, displays on the **next** line, **`09:1269`**
      (sentence-start convention; both anchors are cited wherever the condition
      is used).  It is the condition this module *refutes* at a first-Bob node,
      which is what `eq:wrapper-first-bob-light` says.
    * **`09:1238--1244`**, the routing rule: "At an Alice query, route it to a
      child containing at least `ceil(A_k/2) >= A_{k-1}` of those rows; route it
      to both children if both qualify."
    * **`09:1244--1248`**, the kinds: a clean certificate routed uniquely stays
      clean with weight `1`; when it splits both descendants become **low**
      certificates of weight `1/2`; a low certificate keeps weight `1/2`
      "whether it has one or two qualifying children".
    * **`09:1276--1277`, branch (ii)'s own guard**: `2 <= kappa_v < t_ref`.  The
      **strict** upper guard is what Section 2 exhibits; the boundary
      `kappa_v = t_ref` belongs to branch (i) by `09:1269`.
    * **`09:1280--1283`**, the census chain
      `|represented| >= ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`, with the
      case split of `09:1285--1287`.
    * **`09:1287--1290`**, the projection sentence.  **GAP-EXPOSED.**  See the
      STOP-AND-REPORT section below: it is neither proved nor assumed silently
      here; it enters as the single named binder `hselect`.
    * **`09:1291--1296`**, `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G`, "so
      trim it to the row density `kappa_v x_T`".
    * **`09:1296--1301`**, the `lem:certified-row-ladder` call with `M = G`,
      `H = C-1`, `x = x_T`, `z = y`, `ell = ell_v`.
    * **`09:1302--1304`**, "`C >= 3` verifies `H >= 2`, and
      `kappa_v x_T <= t_ref x_T <= 1` verifies legality".
    * **`09:1304--1308`**, the closure output `C + log_2 kappa_v - 1` and "Its
      lower bound is one more bit than the remaining child budget in the alleged
      protocol.  Therefore".
    * **`09:1309--1313`** (`eq:wrapper-first-bob-light`), `W_v < vartheta
      kappa_v` at every first-Bob node: **the conclusion this module reaches**,
      conditionally on `hselect` and on the alleged protocol's budget.
    * **`09:1219`**, `A_0 = ceil(2 x_T m_G)`; **`09:1233--1235`**, the retention.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`):
    `08:166`, `x_T = 2^{-b_T}` (the banked `DenseStageFourOpening.xTdepth`).
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    `A:26` (`t_cert = 2^{2^20}`), `A:117--118` (`t` a power of two divisible by
    `16`, `t >= t_cert`), `A:111` (`m` is the matrix's row count).
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `eq:tref-search` (`06:558--571`), consumed only through the banked
    `WrapperReferenceConstruction.tRef`; `06:237--243` (`b_T`, `x_T`), the
    display that makes `b_T` a **DEFINED** quantity.
* **Reader counterpart (module level; claimed by no declaration below).**
  `routes/parameterized-np/reader-facing/sections/A-stage4-details.tex:390--392`
  -- "Its small-capacity and final-node closures use the certified row ladder
  ...; they do not require a new odd-copy theorem."  Opened and read verbatim
  this tranche.  It is unnumbered connective prose inside a proof, and the
  reader-counterpart rule forbids citing prose as a statement; the one numbered
  reader item it points at, `lem:paper-certified-row-ladder`
  (`reader 02:244--256`), is **already claimed** by `TerminalTwoStream`, and the
  rule forbids assigning one reader item to two declarations.  A search of the
  whole reader artifact for the first-Bob light bound returns nothing numbered:
  `eq:wrapper-first-bob-light` has **no** reader counterpart.  The same search,
  repeated this tranche for the routed-certificate material Section 5 audits
  (`09:1238--1257`: the routing rule, the kinds and weights, `kappa_v`, `W_v`),
  again returns nothing numbered -- `reader A-stage4-details.tex:263--271` is
  unnumbered prose about a *different* count (Alice-node excess against
  deficit), not the certificate-weight routing.  The trace is therefore recorded
  once, here, at module level, and is claimed by no declaration below.

## What this module is

`TRANSCRIPT-LEVEL-SUCCESSORS-001` registered successor **`L1-F5`**: "assemble
branch (ii) into `W_v < vartheta kappa_v`; needs `hselect` (`09:1287--1296`)
discharged at the routed census".  This tranche executes the join and reports
honestly on `hselect`.  Three things land.

**Section 1 executes the trim at the predecessor's own audit instance.**  The
predecessor proved `exists_branchTwo_trimmed_rows` in general and never fired
it; Section 1 fires it at the `splitAudit` instance of its Section 4, where the
frozen regime clause holds with **equality** (`kappa_v x_T m_G = 16 . 2^{-9} . 32
= 1`) and the frozen trim floor `ceil(kappa_v x_T m_G)` therefore **evaluates to
`1`**: the branch-(ii) trim selects exactly one reference row there.  It is a
**NON-FIDELITY / BEYOND-PAPER** firing, inheriting the label of the instance it
uses.

**Section 2 moves the legality audit off the branch boundary.**  The
predecessor's `branchTwo_legality_binders_consistent` sits at `r = 6`, `d_v = 2`,
where `kappa_v = 16 = t_ref`: the boundary `09:1269` assigns to branch **(i)**,
at which the first conjunct of the legality chain is an *equality* and branch
(ii)'s own guard `09:1277` fails.  `branchTwo_legality_at_interior_capacity`
fires one Alice query deeper, at `r = 6`, `d_v = 3`, `kappa_v = 2^3 = 8 < 16`:
now `09:1277`'s guard `2 <= kappa_v < t_ref` holds **strictly**, and the first
conjunct of the legality chain is a **strict** inequality.  The row density is
still taken from the banked closed-form accessor
`WrapperLowRungs.wrapperLowRungGates_legal_instance`, never as a numeral.

**Section 4 is the join.**  `branchTwo_firstBobLight_join` derives the frozen
`W_v < vartheta kappa_v` at a first-Bob node of the canonical routed system, by
contradiction exactly as `09:1268--1313` argues it: assume the node heavy, get
the cover from the census chain, feed `hselect`, compose with the ladder call,
and hit the child budget.  Five banked inputs are consumed and none is
re-derived:

1. `TranscriptLevelSuccessors.branchTwo_census_chain` (`09:1280--1283`) supplies
   the cover `u_{kappa_v} <= |represented|` -- the antecedent of `hselect`;
2. `TranscriptLevelSuccessors.branchTwo_row_density_legality` (`09:1302--1304`)
   supplies `kappa_v x_T <= 1`;
3. `TranscriptLevelSuccessors.branchTwo_ladder_call_at_node` (`09:1296--1306`)
   supplies the closure output `C + ell_v - 1`;
4. `TranscriptLevelSuccessors.branchTwo_closure_contradicts_child_budget`
   (`09:1304--1308`) fires the one-bit contradiction;
5. `TranscriptLevelSuccessors.exists_branchTwo_trimmed_rows` (`09:1291--1296`)
   is consumed by `branchTwo_firstBobLight_join_at_paper_schedule`, whose
   conclusion carries the **executed** trim alongside the light bound, so the
   row side of the frozen paragraph is not orphaned by the join.

What is new against the banked `FirstWrapperAssembly.firstBobLight_assembled` is
the *indexing*: that theorem's residual budget `B` is an abstract natural
constrained by `hbudget`, and its branch dichotomy is done at the exponent.
Here `B` is the **actual** cost of the selected Bob child,
`(descend P (v.val ++ [b])).cost`, `hbudget` is derived from the routed address
rather than supplied, and `ell_v` is `Nat.log 2 kappa_v` read at the node.  The
join is therefore an instance of the banked one, never a strengthening of it.

## STOP-AND-REPORT: `hselect` is NOT discharged, and here is the exact stop

The prescription for this tranche was a genuine banked-material discharge of
`hselect` **or** a documented stop.  The stop is documented, with the search
that produced it.

`hselect` is the frozen sentence `09:1287--1296` in the form the ladder consumes:

> if `u_{kappa_v}` represented coordinates are covered, then the certified
> restriction living inside the **selected Bob child** has complexity at most
> that child's protocol cost.

What is banked, and was read first-hand this tranche:

* `WrapperDenseFrontierWiring.exists_denser_child_colFloor` proves the
  **column-set** halving: at a Bob query the two children split the retained
  column set exactly, so one child meets `certifiedColFloor theta 1 = theta/2`.
  Its own docstring records that this is *not* `09:1287--1290`, whose subject is
  the **projection** `WrapperProjectionCovers.projSet J` of that column set.
* `DenseWrapperFrontier.denserChild_density_frozen` is the same halving as pure
  arithmetic at `rho = 2y^2`, and the predecessor's
  `TranscriptLevelSuccessors.denserChild_colFloor_eq_y_sq` evaluates it to the
  frozen `y^2 = 9/25`.
* `WrapperProjectionCovers.productProjectionCover` and
  `density_le_pow_of_disjoint_poor` are the projection-cover machinery, but they
  are stated for an ambient column family `S : Finset (Fin q -> Y)`, not for the
  retained column set at a *protocol node*.

What is missing is not a step of arithmetic.  Two objects are unrelated in
`src/`:

* the certified restriction's complexity `NPCC.LambdaGE Gmat ...`, and
* the protocol subtree cost `(descend P (v.val ++ [b])).cost`.

A grep of `src/` for a statement mentioning both `LambdaGE` and `cost`, run
first-hand this tranche, returns **nothing** outside this file -- and inside this
file the only occurrences are the `hselect` binders of Section 4, i.e. the
hypothesis itself.  There is no simulation or embedding lemma identifying the
certified restriction of `G` with what the alleged protocol does below the
selected child, and the projection form of `09:1287--1290` -- which is what
would produce that identification -- is exactly GAP-EXPOSED item 15 of
`SPLIT-FIRST-BOB-INSTANCE-001` and item (iii) of
`WRAPPER-DENSE-FRONTIER-WIRING-001`.  Discharging `hselect` therefore needs new
Lean mathematics (a node-level projection lemma plus the restriction-to-subtree
bridge), not a recombination of banked material.

Accordingly `hselect` is a **named explicit binder** of every theorem in
Section 4, never an `axiom`, never a bundle field, and never silently assumed;
`09:1287--1290` stays GAP-EXPOSED verbatim as all three predecessors left it,
and this tranche narrows it by **nothing**.

## Residues this module does NOT close (named, not implied)

* **`09:1287--1290` is not narrowed.**  See the stop above.
* **`eq:wrapper-first-bob-light` is not unconditional.**  Section 4 reaches it
  *given* `hselect` and the alleged protocol's budget relation; the banked
  `FirstWrapperAssembly.firstBobLight_assembled` remains the branch-joined
  statement and is unchanged by this tranche.
* **Branch (i) (`09:1269--1276`) is not entered**, and the branch dichotomy is
  not performed: Section 4 carries branch (ii)'s guard `kappa_v <= t_ref` as a
  hypothesis.  Joining the two branches is the banked
  `canonical_firstBobLight_largeCapacity`'s job and is untouched.
* **`L1a`** (`09:1203--1207`) and **`L1b`** (`09:1224--1235`) are untouched;
  `CompletedNoBob` and the retention floor enter as the banked binders.
* **The certified-lemma residues are not narrowed.**
  `thm:certified-localized-extension` (`A:285--329`),
  `lem:certified-row-ladder`'s own proof, and `ReferenceStoppingEndpoint` are
  consumed by pin where they are consumed at all.
* **`lem:final-reference-uniqueness` (`09:1315--1344`) is untouched**;
  `eq:wrapper-u-dense` is not approached; `thm:first-wrapper` is not proved;
  **no route completion is claimed, and none may be inferred.**
* **`L1-F6`** (retire the redundant `hone` binder from the banked frontier
  supply) is still open: it is an edit to `WrapperDenseFrontierWiring` and
  therefore its own tranche.  Nothing here edits it.  Recorded once more, since
  it is easy to mistake for a defect of this module: the `hone` binder of
  `branchTwo_firstBobLight_join_at_paper_schedule` is an **extra hypothesis
  relative to `09:1291--1296`** -- the frozen trim demands no such clause -- and
  it is inherited from the banked `exists_branchTwo_trimmed_rows`, not
  introduced here.

## CANONICAL INHABITATION -- registered, not discharged

The paper's own instance at `09:1268` is the routing of an **alleged**
`(C+r-1)`-bit protocol computing a member of `<U,1,1-delta_U,theta>`
(`09:1188--1194`).  No such protocol exists -- that is the conclusion of the
whole argument -- so the paper's object is a *function of the assumed protocol*
and the honest Lean form is the implication each theorem of Section 4 states.
The canonical-inhabitation obligation is **REGISTERED and DEFERRED**, exactly as
`WRAPPER-DENSE-FRONTIER-WIRING-001` obligation (ii),
`TRANSCRIPT-LEVEL-CONSTRUCTION-001` and `TRANSCRIPT-LEVEL-SUCCESSORS-001` record
it; it is discharged when the schedule-level construction lands, and **never** by
a probe here.  Sections 1 and 5 are labelled **NON-FIDELITY / BEYOND-PAPER** and
discharge nothing.

## Section 5: what the join costs, measured

A green build cannot see whether a conditional theorem is worth anything, so
Section 5 measures the join against concrete routed systems, from both sides.

*The conclusion is refutable.*  `splitAudit_completedNoBob` and
`splitAudit_firstBob_true` put the predecessor's audit node inside
`FrontierIndexing.canonicalSystem`, and `splitAudit_is_not_light` records that
its weight meets the heavy threshold of `09:1268--1269` with **equality**
(`W_v = 9 = vartheta . 16`), so the join's *conclusion* is false there:
`eq:wrapper-first-bob-light` is not an arithmetic tautology.

*The hypotheses are not vacuous.*  `splitAudit_cover_antecedent_holds` shows the
antecedent of `hselect` is **reachable** -- at the audit node the cover of
`09:1280--1283` holds, so `hselect` there is not an empty implication but the
bare unmodelled inequality -- and `join_gate_group_jointly_satisfiable` inhabits
the whole arithmetic/schedule group at once inside branch (ii), at `C = 3`
(`09:1302`'s floor) and the frozen `y = 3/5` (`09:314--315`), with `x_T` taken
from the banked closed-form gate accessor.

*The hypotheses exclude something, at a point where they can jointly hold.*
This is the repair this generation of the module carries, and the reason
Section 5 owns a second routed system.  The pole must be placed where the join's
premise bundle is **inhabited**, or it measures nothing: at `splitAudit` the two
schedule binders `hbranch : kappa_v <= t_ref` and `hq4 : k_ref + 2 <= r` read
`4 <= k_ref` and `k_ref <= 3` (because `r = 5` and `d_v = 1` force
`kappa_v = 16`), so they are incompatible *by themselves*, with `hcost`, `hbase`
and `hselect` playing no part.  Solving the two guards together gives
`r - d_v <= k_ref <= r - 2`, hence `d_v >= 2`.  `interiorAudit` is therefore a
routed system with a first-Bob node at `d_v = 3` under `r = 6`, i.e. at exactly
the compatible interior point `(r, d_v, k_ref) = (6, 3, 4)` that
`branchTwo_legality_at_interior_capacity` and
`join_gate_group_jointly_satisfiable` already inhabit.  There
`interiorAudit_pole_binders_inhabited_except_certificates` proves that every
hypothesis of the pole **except `hbase` and `hselect`** holds at one concrete
tuple at that node, and `interiorAudit_forces_a_join_hypothesis_to_fail` then
shows they cannot all hold: at the exhibited tuple the excluded pair is exactly
`hbase` and `hselect` -- the two certificate clauses -- rather than schedule
arithmetic.  `hcost` participates in the derivation but is *separately
inhabited* there (`interiorAudit.cost = 4 <= C + r - 1 = 8`), and is in fact
implied by `hC` at this instance, so it is never the culprit.

Together these are the LANE-GATE 3 discharge for everything except `hbase` and
`hselect`, whose joint inhabitation *is* the REGISTERED and DEFERRED canonical
obligation.  No probe below discharges it.

## Axioms and imports

Computed first-hand this tranche rather than argued from the one-line import:
the transitive import closure of this module is 119 local modules -- 67
`ParameterizedNP` modules counting this one, `EthInapproximability.Prelude`, the
`LegacyNPCC.Core` and `LegacyNPCC.Bridge` facades, and their Stage12-free
closure of 20 `NPCC.*` modules (`NPCC.Engine`, `NPCC.Relaxed`, `NPCC.Upper`
among them), 21 `Workspace.*` modules and 8 `EthBridge.*` modules -- together
with `Mathlib*`.  There is **no** `import LegacyNPCC.Stage12`
anywhere in that closure, so the cited AGHP balanced-family axiom is not reached
by an import path; and the fixed-width family `NPCC.Lift`, `NPCC.Gap`,
`NPCC.Wrapper` appears nowhere in it.  `EXPANDER-001` occurs in no hypothesis of
any declaration below.  No `axiom`, no opaque certificate, no unproved
obligation marker, no `structure`, no `inductive`.

## DEFINED-VS-FREE ledger for this tranche

| quantity | status | how it is obtained here |
| --- | --- | --- |
The status column carries the frozen **DEFINED/FREE** classification.  It is
about the *paper*, not about Lean: every quantity below except the labelled
audit points is represented here by a universally quantified Lean binder, which
is a strengthening of the paper's statement and never an assignment.

| quantity | status | how it is obtained here |
| --- | --- | --- |
| `kappa_v` | DEFINED, `09:1255` | the banked `kappaFrontier` / `kappaAt` |
| `ell_v` | DEFINED, `09:1278` | `Nat.log 2 kappa_v`, evaluated to `r - d_v` |
| `t_ref` | DEFINED, `06:558--569` | the banked `tRef`, never a numeral |
| `vartheta` | DEFINED, `09:1268` | the banked `vartheta` |
| `A_0` | DEFINED, `09:1219` | `initialRefRows xT (Fintype.card X)`, evaluated |
| `x_T` | DEFINED, `08:166` with `06:243` | the banked `xTdepth`, or the banked gate accessor |
| `b_T` | DEFINED, `06:239--241` | a Lean binder, except in the labelled sections |
| `m_G` | DEFINED, `A:111` with `09:113--116` | `Fintype.card X`, read at the carrier |
| `r` | DEFINED, `06:515` with `09:105` | a Lean binder, except in the labelled sections |
| `k_ref` | DEFINED, `06:558--569` | a Lean binder, except in the labelled sections |
| `y` | DEFINED, `09:314--315` (`y_* = 3/5`) | a Lean binder; `3/5` only where cited |
| `C` | **FREE** (genuine binder) | a Lean binder; `C = 3` only as `09:1302`'s floor |

`x_T`'s "how" column names two banked routes, and **both occur in §5, at
different values** -- `2^{-7}` inside `interiorAuditA0` and `2^{-22}` in the
pole's own clauses.  The §5 header states why that is sound and why it is ours.

`C` is the one genuinely free input of the group: the frozen text leaves the
alleged protocol's cost parameter open and only floors it, `C >= 3` at
`09:1302`, so wherever `C = 3` appears below it is that floor and not a choice.

`06:515` defines the width `q = 2^{A_wrap L_P^2}`; `r` is fixed from it by
`09:105`, "Let `q = 2^r` be the scale-alignment width".  Both anchors are
required and both are cited wherever `r`'s status is asserted.

**Self-chosen values occur in exactly two places, both labelled.**  The tuple
`(r, d_v, k_ref) = (6, 3, 4)` of Section 2 and of Section 5's `interiorAudit`,
and the whole of Sections 1 and 5, which inherit the predecessor's `splitAudit`
**BEYOND-PAPER** label -- earned twice over, because `06:561--563` alone forces
`k_ref >= 2^19` and `A:117` with `A:26` forces `t_ref >= t_cert = 2^{2^20}`,
while the instances use `k_ref = 4`.  Every other numeral is a frozen literal of
a cited display (`1`, `2`, `9`, `16`) or the output of an evaluation.
-/

namespace EthInapproximability.ParameterizedNP.TranscriptLevelJoin

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors

/-! ## §1  Judge `F4`: the branch-(ii) trim, FIRED at the predecessor's instance

`TranscriptLevelSuccessors.exists_branchTwo_trimmed_rows` executes the trim of
`09:1291--1296` in general and was never fired.  It is fired here at the
`splitAudit` instance of that module's Section 4 -- the only routed system this
development owns -- where the frozen regime clause holds with equality.

**NON-FIDELITY / BEYOND-PAPER**, inherited verbatim from the instance: `A:117`
with `A:26` forces `t_ref >= t_cert = 2^{2^20}` while the instance uses
`k_ref = 4`, and the alphabet, coordinate count, `r = 5` and `b_T = 9` are the
predecessor's own choices.  Nothing here discharges canonical inhabitation. -/

section AuditTrim

/-- **`09:1291--1296`'s regime clause EVALUATED at the audit node.**

`kappa_v x_T m_G = 16 . 2^{-9} . 32 = 1`, with equality: `kappa_v` is the banked
`kappaFrontier` at the node's own depth `d_v = 1` (`09:1255`), `x_T` is the
banked `xTdepth` at the instance's `b_T = 9` (`08:166`), and `m_G` is read at the
row carrier (`A:111` with `09:113--116`).  No numeral is assigned to any of the
three. -/
theorem splitAudit_branchTwo_hone :
    1 ≤ ((kappaFrontier 5 splitAuditNode.val.length : ℕ) : ℝ) * splitAuditXT
      * ((Fintype.card (Fin 32) : ℕ) : ℝ) := by
  have hcard : (Fintype.card (Fin 32) : ℕ) = 32 := by simp
  rw [splitAudit_node_val, hcard]
  norm_num [kappaFrontier, stoppingCapacity, splitAuditXT, xTdepth]

/-- **Aux (the branch-(ii) trim floor at the audit node, EVALUATED).**

`ceil(kappa_v x_T m_G) = ceil(1) = 1`: at this instance the frozen trim of
`09:1296` keeps exactly one reference row.  The numeral is an output of the
frozen display, not an input. -/
theorem splitAudit_branchTwo_trimFloor :
    ⌈((kappaFrontier 5 splitAuditNode.val.length : ℕ) : ℝ) * splitAuditXT
      * ((Fintype.card (Fin 32) : ℕ) : ℝ)⌉₊ = 1 := by
  have hcard : (Fintype.card (Fin 32) : ℕ) = 32 := by simp
  have h : ((kappaFrontier 5 splitAuditNode.val.length : ℕ) : ℝ) * splitAuditXT
      * ((Fintype.card (Fin 32) : ℕ) : ℝ) = 1 := by
    rw [splitAudit_node_val, hcard]
    norm_num [kappaFrontier, stoppingCapacity, splitAuditXT, xTdepth]
  rw [h]
  simp

/-- **Judge `F4`: `exists_branchTwo_trimmed_rows` INHABITED from the `splitAudit`
instance.**

The predecessor's general trim, fired at its own audit node: a subset of
coordinate `0`'s **actual** certificate rows at the address `[false]`, of card
exactly the frozen floor `ceil(kappa_v x_T m_G)`, nonempty.  Every input is a
theorem of the predecessor -- the retention `splitAudit_hR` (`09:1233--1235`),
the routing `splitAudit_node_mem_coordRoutes` (`09:1250--1252`), and the regime
clause above -- so nothing is supplied by hand.

**NON-FIDELITY / BEYOND-PAPER**, per the section label. -/
theorem splitAudit_branchTwo_trimmed_rows :
    ∃ T ⊆ rowsAt splitAudit (splitAuditRows 0) splitAuditNode.val,
      T.card = ⌈((kappaFrontier 5 splitAuditNode.val.length : ℕ) : ℝ) * splitAuditXT
          * ((Fintype.card (Fin 32) : ℕ) : ℝ)⌉₊
        ∧ T.Nonempty :=
  exists_branchTwo_trimmed_rows (P := splitAudit) (R := splitAuditRows) (r := 5)
    (xT := splitAuditXT) (i := 0) (splitAudit_hR 0) (splitAudit_node_mem_coordRoutes 0)
    splitAudit_branchTwo_hone

/-- **The same firing with the floor evaluated: the trim keeps exactly one row.**

Stated separately from `splitAudit_branchTwo_trimmed_rows` so that the frozen
expression and its value are both on record; a reader who wants the display keeps
the former, a reader who wants the audit number gets this. -/
theorem splitAudit_branchTwo_trims_to_one_row :
    ∃ T ⊆ rowsAt splitAudit (splitAuditRows 0) splitAuditNode.val,
      T.card = 1 ∧ T.Nonempty := by
  obtain ⟨T, hT, hcard, hne⟩ := splitAudit_branchTwo_trimmed_rows
  exact ⟨T, hT, by rw [hcard, splitAudit_branchTwo_trimFloor], hne⟩

end AuditTrim

/-! ## §2  Judge `F5`: the legality chain at an INTERIOR branch-(ii) capacity

`09:1277` opens branch (ii) with `2 <= kappa_v < t_ref`, strictly.  The
predecessor's consistency audit for the legality chain sat at `r = 6`, `d_v = 2`,
where `kappa_v = 2^4 = 16 = t_ref`: the boundary, which `09:1269` (non-strict)
assigns to branch **(i)**, and at which the chain's first comparison degenerates
to an equality.  One Alice query deeper the point is genuinely interior. -/

section InteriorPoint

/-- **Aux (strict monotonicity of the row density in the capacity).**

The step `09:1302--1304`'s first comparison makes when the branch guard of
`09:1277` is strict rather than boundary.  General in the two capacities and in
the density. -/
theorem capacity_row_density_strict_mono {κ t : ℕ} {x : ℝ} (hx : 0 < x) (h : κ < t) :
    ((κ : ℕ) : ℝ) * x < ((t : ℕ) : ℝ) * x := by
  have hcast : ((κ : ℕ) : ℝ) < ((t : ℕ) : ℝ) := by exact_mod_cast h
  exact mul_lt_mul_of_pos_right hcast hx

/-- **Judge `F5`: branch (ii)'s guard and the legality chain at an interior
point, with the first conjunct STRICT.**

At `r = 6`, `d_v = 3` the capacity is `kappa_v = 2^{6-3} = 8`, so `09:1277`'s own
guard `2 <= kappa_v < t_ref` holds with a **strict** upper comparison at
`t_ref = 2^4 = 16` -- unlike the predecessor's `d_v = 2` audit, which sat on the
boundary `kappa_v = t_ref` that `09:1269` gives to branch (i).  The first
conjunct of `TranscriptLevelSuccessors.branchTwo_row_density_legality`
(declaration 11 of that module) is literally non-strict,
`kappa_v x_T <= t_ref x_T`; what is true here is that the underlying comparison
**can be strengthened to strict, and is** -- as conjunct 4 of this statement,
proved by `capacity_row_density_strict_mono` -- while declaration 11 supplies
conjuncts 5 and 6 unchanged, by *calling* it rather than by re-deriving them.

The row density is the banked closed-form accessor
`WrapperLowRungs.wrapperLowRungGates_legal_instance 4 6`, i.e. that accessor's
closed-form witness `1/(2^r . 65536)` for the gate ratio `q x_T`, at `r = 6`,
evaluated -- never a numeral shortcut of it.  It is **not** the paper's own
expression for `x_T`: the accessor's own docstring records that the paper's
`x_T` is `2^{-b_T}` with `b_T` fixed by `06:238--242`, and that what the witness
fixes is the single ratio `q x_T` the gate constrains, and nothing else.  Its
value `2^{-22}` is disclosed rather than hidden, because the arguments are
BEYOND-PAPER.

**BEYOND-PAPER.**  `r = 6`, `k_ref = 4` and `d_v = 3` are **ours** -- `06:515`
with `09:105` DEFINES `r`, `06:558--569` DEFINES `k_ref` (and `06:561--563` alone
forces `k_ref >= 2^19`), and `A:117` with `A:26` forces
`t_ref >= 2^{2^20}` -- and no legality is claimed for them.  What the statement
does claim is that the binder group of declaration 11 is jointly satisfiable
*inside* branch (ii), which the boundary instance could not show. -/
theorem branchTwo_legality_at_interior_capacity :
    2 ≤ kappaFrontier 6 3
      ∧ kappaFrontier 6 3 < tRef 4
      ∧ (0 : ℝ) < 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ ((kappaFrontier 6 3 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536))
          < ((tRef 4 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536))
      ∧ ((kappaFrontier 6 3 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536))
          ≤ ((tRef 4 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536))
      ∧ ((tRef 4 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 1 := by
  obtain ⟨-, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  have hstrict : kappaFrontier 6 3 < tRef 4 := by
    norm_num [kappaFrontier, stoppingCapacity, tRef]
  have hchain := branchTwo_row_density_legality (r := 6) (d := 3) (kref := 4)
    (le_of_lt hpos) (le_of_lt hstrict) (by norm_num) (by rw [hval]; norm_num)
  exact ⟨by norm_num [kappaFrontier, stoppingCapacity], hstrict, hpos,
    capacity_row_density_strict_mono hpos hstrict, hchain.1, hchain.2⟩

end InteriorPoint

/-! ## §3  Aux battery: the general steps the join runs on

Five general properties, each proved.  Four of them -- `cover_of_heavy`,
`one_le_log_kappaAt_of_firstBob`, `capacity_row_density_legal_at_capacity` and
`light_iff_not_heavy` -- are consumed by Section 4; `select_bound_mono` is
**unwired**, a recorded ordering fact kept for the branch-(i) join that is not
this tranche's.  A green build sees none of them. -/

section Aux

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **Aux 1 (`09:1280--1283` composed: the cover the selection is counted
against).**

The frozen census chain has three links; what `09:1288--1289`'s selection of
`u_{kappa_v}` coordinates actually needs is their composition,
`u_{kappa_v} <= |represented|`.  Consumed from the predecessor's
`branchTwo_census_chain` by pin, not re-derived.

General in `P`, `Coord`, `R`, `A_0`, `r` and the node. -/
theorem cover_of_heavy {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hheavy : vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) ≤ frontierWeight P R A0 r v) :
    smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card := by
  obtain ⟨h₁, h₂, h₃⟩ := branchTwo_census_chain hcomp hR hv hheavy
  exact le_trans h₁ (le_trans h₂ h₃)

/-- **Aux 2 (`09:1259` with `09:1278`: the ladder's exponent is at least one at
every first-Bob node).**

"Every first-Bob node has `kappa_v >= 2`", so `ell_v = log_2 kappa_v >= 1`.  This
is the ladder call's `hℓ`, derived from the frozen exposure rule of
`09:1251--1252` rather than assumed.  General. -/
theorem one_le_log_kappaAt_of_firstBob {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true) :
    1 ≤ Nat.log 2 (kappaAt P R A0 r v) := by
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  rw [log_kappaAt_eq_capacity_exponent]
  omega

/-- **Aux 3 (`09:1302--1304` composed at a node's capacity).**

"`kappa_v x_T <= t_ref x_T <= 1` verifies legality" is a chain of two
comparisons; the ladder consumes only its composite `kappa_v x_T <= 1`.  Obtained
by calling the predecessor's `branchTwo_row_density_legality` and transiting it,
so the two reasons stay separable at the call site.  General in `r`, `d_v`,
`k_ref` and `x_T`. -/
theorem capacity_row_density_legal_at_capacity {r d kref : ℕ} {xT : ℝ} (hxT0 : 0 ≤ xT)
    (hbranch : kappaFrontier r d ≤ tRef kref) (hq4 : kref + 2 ≤ r)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025) :
    ((kappaFrontier r d : ℕ) : ℝ) * xT ≤ 1 := by
  obtain ⟨h₁, h₂⟩ := branchTwo_row_density_legality hxT0 hbranch hq4 hgate
  exact le_trans h₁ h₂

/-- **Aux 4 (`hselect` is upward closed in the budget it bounds).**

The banked `FirstWrapperAssembly.firstBobLight_assembled` states `hselect`
against an abstract residual budget `B`; Section 4 states it against the
**actual** child cost.  This records that the two are ordered the safe way: a
selection bound against a smaller budget implies one against any larger budget,
so instantiating `B` at the child's own cost is the strongest form of the
hypothesis and never a strengthening obtained by accident.  General. -/
theorem select_bound_mono {α : Prop} {z B B' : ℕ} (h : α → z ≤ B) (hB : B ≤ B') :
    α → z ≤ B' := fun ha => le_trans (h ha) hB

/-- **Aux 5 (`09:1268`'s two sides are exact complements).**

The heavy condition of `09:1268` and the light conclusion of
`eq:wrapper-first-bob-light` partition the possibilities at a node, so the
join's proof by contradiction loses nothing: refuting heaviness *is* proving
`W_v < vartheta kappa_v`.  General. -/
theorem light_iff_not_heavy {W κ : ℝ} : W < vartheta * κ ↔ ¬ (vartheta * κ ≤ W) :=
  (not_le).symm

end Aux

/-! ## §4  `L1-F5`: the branch-(ii) join

`09:1268--1313`, at a first-Bob node of `FrontierIndexing.canonicalSystem`, with
`hselect` the single named binder the STOP-AND-REPORT section documents. -/

section Join

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) on branch (ii), joined at the
routed node.**

"Therefore `W_v < vartheta kappa_v` at every first-Bob node `v`."

The frozen argument, executed in its own order.  Suppose the node were heavy.
Then `09:1280--1283` gives `u_{kappa_v} <= |represented|` (`cover_of_heavy`),
which is precisely the antecedent `09:1288--1289` needs; `hselect` carries the
selection, the projection and the trim of `09:1287--1296` to the certified
restriction inside the selected Bob child; `09:1296--1306`'s ladder call at
`ell = ell_v = log_2 kappa_v` (`branchTwo_ladder_call_at_node`, legality from
`capacity_row_density_legal_at_capacity`) gives that child complexity at least
`C + ell_v - 1`; and `09:1306--1308` says that is one bit more than the child can
have in an alleged `(C+r-1)`-bit protocol
(`branchTwo_closure_contradicts_child_budget`).  Contradiction, so the node is
light.

**`hselect` is NOT proved and NOT assumed away.**  It is the frozen sentence
`09:1287--1296` in the form the ladder consumes, it is GAP-EXPOSED item 15 of
`SPLIT-FIRST-BOB-INSTANCE-001`, and the module header documents first-hand why
banked material cannot discharge it: nothing in `src/` relates `LambdaGE` to a
protocol subtree's `cost`.  It appears here as an explicit binder, never an
`axiom` and never a field of a premise bundle.

**Branch (ii) only.**  `hbranch : kappa_v <= t_ref` is `09:1277`'s guard,
weakened to non-strict exactly as the banked small-capacity theorem reads it
(the boundary is handled by branch (i), `09:1269`).  This theorem does **not**
perform the frozen dichotomy and does **not** enter branch (i).

*Why the trivial witness fails.*  The conclusion is a strict inequality about
two named quantities of the routed system, not an existential, so the pole is
whether it can fail at all: `splitAudit_is_not_light` exhibits a routed system
with a first-Bob node at which `W_v = vartheta kappa_v` exactly, i.e. at which the
conclusion is **false**.  The hypotheses therefore exclude something we can
exhibit -- see `interiorAudit_forces_a_join_hypothesis_to_fail`, which places
that exclusion at a point where the whole schedule sub-bundle can hold at once.

General in the matrix carriers, in the three protocol carriers, in `Coord`, `P`,
`R`, `A_0`, `r`, the node, `C`, `k_ref`, `x_T`, `y` and the selected bit. -/
theorem branchTwo_firstBobLight_join {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C kref : ℕ} {xT y : ℝ} (b : Bool)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hcost : P.cost ≤ C + r - 1) (hC : 3 ≤ C)
    (hX : 1 ≤ Fintype.card Rw) (hY : 1 ≤ Fintype.card Cl)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (hbranch : kappaAt P R A0 r v ≤ tRef kref) (hq4 : kref + 2 ≤ r)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hselect : smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card →
      LambdaGE Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
          (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) (y ^ 2)
        ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R A0 r v < vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) := by
  rw [light_iff_not_heavy]
  intro hheavy
  have hcover := cover_of_heavy hcomp hR hv hheavy
  have hℓ := one_le_log_kappaAt_of_firstBob hcomp hR hv
  have hlegal : ((kappaAt P R A0 r v : ℕ) : ℝ) * xT ≤ 1 :=
    capacity_row_density_legal_at_capacity (r := r) (d := v.val.length) (kref := kref)
      (le_of_lt hxT0) hbranch hq4 hgate
  have hladder := branchTwo_ladder_call_at_node Gmat v hX hY hC hxT0 hy0 hy1 hbase hℓ hlegal
  have hlower : C + (r - v.val.length) - 1 ≤ (descend P (v.val ++ [b])).cost := by
    have hcomposed := le_trans hladder (hselect hcover)
    rwa [log_kappaAt_eq_capacity_exponent] at hcomposed
  exact branchTwo_closure_contradicts_child_budget
    ((canonicalSystem hcomp hR).firstBob_spec v hv) hcost hC b hlower

/-- **The join at the paper's own row schedule, carrying the executed trim.**

Same conclusion as `branchTwo_firstBobLight_join`, with `A_0` pinned to the
paper's `ceil(2 x_T m_G)` (`09:1219`, `m_G` read at the row carrier per `A:111`
with `09:113--116`) and the node sitting on coordinate `i`'s route.  The extra
conjunct is `09:1291--1296` **executed**: the certificate's own rows at that
address, trimmed to the frozen floor `ceil(kappa_v x_T m_G)`, nonempty.

This is why the join is stated twice.  In the frozen paragraph the trim is what
makes the ladder's row demand legitimate; in Lean the banked ladder takes the
row density as a real parameter, so the trim would otherwise be consumed by
nothing and the fifth banked input would be orphaned by the join.  Here it is
part of the join's own deliverable.

*Why the trivial witness fails.*  `T = empty` is refuted by `hone`, which forces
the floor to be at least `1`; and the light bound is refutable, see the
predecessor statement's pole.

General in the carriers, `P`, `R`, `r`, the node, the coordinate, `C`, `k_ref`,
`x_T`, `y` and the bit. -/
theorem branchTwo_firstBobLight_join_at_paper_schedule {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X}
    {r : ℕ} {xT : ℝ}
    (hcomp : CompletedNoBob P r)
    (hR : ∀ i, refRowFloor (initialRefRows xT (Fintype.card X)) r ≤ (R i).card)
    {v : FrontierNode P R (initialRefRows xT (Fintype.card X)) r} {C kref : ℕ} {y : ℝ}
    (i : Coord) (b : Bool)
    (hp : v.val ∈ coordRoutes P R (initialRefRows xT (Fintype.card X)) r i)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hcost : P.cost ≤ C + r - 1) (hC : 3 ≤ C)
    (hX : 1 ≤ Fintype.card Rw) (hY : 1 ≤ Fintype.card Cl)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (hbranch : kappaAt P R (initialRefRows xT (Fintype.card X)) r v ≤ tRef kref)
    (hq4 : kref + 2 ≤ r) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hone : 1 ≤ ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
      * ((Fintype.card X : ℕ) : ℝ))
    (hselect :
      smallCopyWidth (kappaAt P R (initialRefRows xT (Fintype.card X)) r v)
          ≤ (representedCoords P R (initialRefRows xT (Fintype.card X)) r v).card →
      LambdaGE Gmat
          (2 ^ (Nat.log 2 (kappaAt P R (initialRefRows xT (Fintype.card X)) r v) - 1) + 1)
          (((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT) (y ^ 2)
        ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R (initialRefRows xT (Fintype.card X)) r v
        < vartheta * ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ)
      ∧ ∃ T ⊆ rowsAt P (R i) v.val,
          T.card = ⌈((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
              * ((Fintype.card X : ℕ) : ℝ)⌉₊
            ∧ T.Nonempty :=
  ⟨branchTwo_firstBobLight_join Gmat hcomp hR b hv hcost hC hX hY hxT0 hy0 hy1 hbase
      hbranch hq4 hgate hselect,
    exists_branchTwo_trimmed_rows (hR i) hp hone⟩

end Join

/-! ## §5  What the join costs, measured at routed systems we own

**NON-FIDELITY / BEYOND-PAPER** throughout.  The `splitAudit` instance is
inherited from `TranscriptLevelSuccessors`'s Section 4 and uses `k_ref = 4`
where `06:561--563` alone forces `k_ref >= 2^19` and `A:117` with `A:26` forces
`t_ref >= t_cert = 2^{2^20}`; its alphabet, coordinate count, `r = 5` and
`b_T = 9` are the predecessor's choices.  The `interiorAudit` instance below is
ours, at the same `k_ref = 4` and with `r = 6`, `b_T = 7`, nine coordinates and
alphabet `Fin 64`.  Nothing here is the paper's instance, and nothing here
discharges canonical inhabitation.

Three further scope facts about this section, stated rather than gestured at,
since the section enumerates its violations rather than waving at them.

* **`b_T` is not a legal value here.**  `06:239--241` DEFINES
  `b_T = 2^{j_{49}(k_T)}`, a power of two; `b_T = 7` (`interiorAuditA0`) and the
  predecessor's `b_T = 9` are neither.  Covered by the label above; no legality
  is claimed for either.
* **This section carries two values of `x_T`, deliberately.**
  `interiorAuditA0` is built from `xTdepth 7`, i.e. `x_T = 2^{-7}`, while every
  `x_T` clause of `interiorAudit_pole_binders_inhabited_except_certificates` and
  `join_gate_group_jointly_satisfiable` uses the banked gate accessor's
  `1/(2^6 . 65536) = 2^{-22}`.  This is sound because `A_0` and `x_T` are
  *independent binders* of `branchTwo_firstBobLight_join` -- and `A_0` evaluates
  to `1` at both values, so the routed system is literally unchanged -- but the
  paper ties the two roles together at `09:1219`, so the split is ours and is
  named here rather than left to be discovered.
* **The row-side regime is outside the group that is inhabited.**  At the pole's
  toy sizes `kappa_v = 8` and `m_G = 64`, `09:1294`'s regime `kappa_v x_T m_G >= 1`
  forces `x_T >= 2^{-9}`, while `eq:wrapper-low-simple-gate` at `r = 6` forces
  `x_T <= 4/1601600 < 2^{-18}`; no `x_T` meets both.  So no extension of this
  probe inhabits the trim clause `hone` together with the gate clause.  This
  costs the statements nothing -- `hone` is not a binder of the pole, and the
  two theorems above scope their claims to the group they do inhabit -- and it
  is an artifact of `m_G = 64`; the frozen `m_G = |Rows(G)|` (`09:116`, with
  `g = m_G/m = 91/92` at `09:117`) is astronomically larger, which makes the
  regime clause easy.

What Section 5 *is* good for: the join is a conditional theorem, and a green
build cannot tell a conditional theorem with load-bearing hypotheses from one
whose hypotheses are jointly unsatisfiable at every legal point.  Two facts are
needed and neither implies the other.

* **The conclusion can fail.**  `splitAudit` is a routed system whose first-Bob
  node is heavy **exactly**, so `eq:wrapper-first-bob-light` is false there and
  is not an arithmetic tautology.
* **The premise bundle is inhabited where the exclusion is claimed.**  A pole is
  evidence only if the hypotheses it excludes *could* have held together.  At
  `splitAudit` they could not: `r = 5` with `d_v = 1` forces `kappa_v = 16`, so
  the join's two schedule binders `hbranch : kappa_v <= t_ref` and
  `hq4 : k_ref + 2 <= r` read `4 <= k_ref` and `k_ref <= 3` and are incompatible
  by themselves, with `hcost`, `hbase` and `hselect` playing no part.  Solving
  the two guards together gives `r - d_v <= k_ref <= r - 2`, hence `d_v >= 2`,
  which `splitAudit` cannot reach.  So the pole is placed instead at
  `interiorAudit`, a routed system whose first-Bob node sits at `d_v = 3` under
  `r = 6`: there `kappa_v = 8 < 16 = t_ref` is strictly inside `09:1277`, the
  whole arithmetic/schedule group is jointly satisfiable
  (`join_gate_group_jointly_satisfiable`, at the same tuple), and the exclusion
  is therefore attributable to `hcost`, `hbase` and `hselect`. -/

section AuditPole

/-- **`lem:wrapper-no-bob-completion`'s frame condition at the audit instance.**

`CompletedNoBob splitAudit 5`: every Alice route strictly shorter than `r = 5`
arrives at a query node.  The root is an Alice query and its two children are Bob
queries, so the only Alice routes are `[]`, `[false]` and `[true]`; a route of
length two or more would need its second node to be an Alice query, and both are
`bobRootTranscript`s.  Proved, not assumed. -/
theorem splitAudit_completedNoBob : CompletedNoBob splitAudit 5 := by
  intro p hp _
  match p with
  | [] => exact trivial
  | [c] => cases c <;> exact trivial
  | c :: d :: q =>
      obtain ⟨-, hrest⟩ := hp
      obtain ⟨a, l, r', hEq⟩ := hrest.1
      cases c <;> exact absurd hEq (by simp [splitAudit, bobRootTranscript, descendStep])

/-- **The audit node is a first-Bob node of the canonical routed system.**

`FrontierIndexing.canonicalSystem`'s `firstBob` is the frozen exposure rule
`09:1251--1252` -- `d_v < r` -- and the audit node has `d_v = 1 < 5`. -/
theorem splitAudit_firstBob_true :
    (canonicalSystem splitAudit_completedNoBob splitAudit_hR).firstBob splitAuditNode
      = true := by
  decide

/-- **`hselect`'s antecedent is REACHABLE, so `hselect` is not vacuously true
where it is used.**

An implication hypothesis is worthless if its antecedent can never hold: the
join would then be an elaborate way of assuming nothing.  At the audit node the
cover of `09:1280--1283` **holds** -- `u_{kappa_v} = smallCopyWidth 16 = 9` against
the eighteen coordinates that route there -- and it is obtained by firing
`cover_of_heavy` at the node's own heaviness (`W_v = 9 = vartheta . 16`, with
equality), not asserted.

So at this node `hselect` is not an empty promise: it reduces to the bare
inequality `LambdaGE G ... <= (descend P ([false] ++ [b])).cost`, which is exactly
the unmodelled identification the STOP-AND-REPORT section names. -/
theorem splitAudit_cover_antecedent_holds :
    smallCopyWidth (kappaAt splitAudit splitAuditRows splitAuditA0 5 splitAuditNode)
      ≤ (representedCoords splitAudit splitAuditRows splitAuditA0 5 splitAuditNode).card :=
  cover_of_heavy splitAudit_completedNoBob splitAudit_hR splitAudit_firstBob_true
    (by rw [splitAudit_kappa, splitAudit_frontierWeight, vartheta_val]; norm_num)

/-- **The join's conclusion is FALSE at the audit node.**

`09:1268`'s heavy threshold is met with **equality** there:
`vartheta kappa_v = (9/16) . 16 = 9 = W_v`, both sides evaluations of the
predecessor's `splitAudit_kappa` and `splitAudit_frontierWeight`.  So
`eq:wrapper-first-bob-light` genuinely says something -- it is not a bound that
holds for arithmetic reasons at every routed system. -/
theorem splitAudit_is_not_light :
    ¬ (frontierWeight splitAudit splitAuditRows splitAuditA0 5 splitAuditNode
        < vartheta
          * ((kappaAt splitAudit splitAuditRows splitAuditA0 5 splitAuditNode : ℕ) : ℝ)) := by
  rw [splitAudit_kappa, splitAudit_frontierWeight, vartheta_val]
  norm_num

/-! ### The pole, placed where the join's premise bundle is INHABITED

`splitAudit` cannot carry the pole.  Its only frontier depth is `d_v = 1` under
`r = 5`, so `kappa_v = 2^{5-1} = 16`, and the join's two schedule binders read
`hbranch : 16 <= 2^{k_ref}` and `hq4 : k_ref + 2 <= 5`, i.e. `4 <= k_ref` and
`k_ref <= 3`.  Those two are incompatible **by themselves**, at every `G`, `C`,
`x_T`, `y` and selected bit; a contradiction derived there is a fact about two
scalars of the schedule and measures nothing about `hcost`, `hbase` or
`hselect`.  A pole is evidence only when the hypotheses it excludes could have
held together.

Solving the two guards jointly, `2^{r-d_v} <= 2^{k_ref}` with `k_ref <= r-2`
gives `r - d_v <= k_ref <= r - 2`, hence `d_v >= 2`: the pole needs a first-Bob
node at least two Alice queries deep, which `splitAudit` does not have.  Among
the capacities `09:1255` can produce, `kappa_v = 8` is the smallest at which the
heavy threshold `vartheta kappa_v = 9/2` of `09:1268--1269` is itself a sum of
the frozen certificate weights of `09:1246` (`k . (1/2) >= 9/2` iff `k >= 9`),
and `kappa_v = 8` together with `d_v >= 2` and a **strict** `09:1277` upper
guard first occurs at `r = 6`, `d_v = 3`, `k_ref = 4` -- the tuple Section 2's
`branchTwo_legality_at_interior_capacity` and
`join_gate_group_jointly_satisfiable` already use.

`interiorAudit` is a routed system with a first-Bob node exactly there.

**NON-FIDELITY / BEYOND-PAPER**, per the section label: it audits *our* encoding
at a point the frozen paper never visits, and discharges nothing. -/

/-- The pole's routed transcript: three Alice queries capped by a Bob query,
built from the banked `RoutedCertificateSystem.bobCappedLadder`, which is the
shape `09:1250`'s first stopping rule produces at depth `3`.

Alice's query splits the row carrier into halves, so `09:1240--1244`'s "route it
to both children if both qualify" fires at the root, and its unique-routing
clause fires at depths `1` and `2` (the ladder asks the *same* question again,
so only one child of a depth-`1` or depth-`2` node is nonempty).  Both clauses of
the frozen routing rule are therefore exercised, and by `09:1244--1248` every
descendant of the root split is a **low** certificate of weight `1/2`.

The carrier is `Fin 64` because the retention floor of `09:1233--1235` at
`r = 6` is `A_6 = 2^6 A_0 = 64` and `A_0 = 1` here: `64` is the smallest row
count that meets it, and it is met with equality.  **Ours**, per the section
label. -/
def interiorAudit : Protocol (Fin 64) Bool Bool :=
  bobCappedLadder (fun x => decide (32 ≤ x.val)) (fun y => y) true 3

/-- The nine started outer coordinates and their reference rows.  Nine is not
free: it is the smallest count for which nine **low** certificates of the frozen
weight `1/2` (`09:1246`) meet the heavy threshold `vartheta kappa_v = 9/2` of
`09:1268--1269` at `kappa_v = 8`. -/
def interiorAuditRows : Fin 9 → Finset (Fin 64) := fun _ => Finset.univ

/-- `A_0 = ceil(2 x_T m_G)` (`09:1219`) through the banked `initialRefRows`, with
`x_T = 2^{-b_T}` the banked `xTdepth` (`08:166`) at our `b_T = 7` -- `06:239--241`
DEFINES `b_T`, and `7` is ours -- and `m_G` read at the row carrier (`A:111` with
`09:113--116`).  Its value is computed, not assigned; see
`interiorAudit_A0_is_evaluated`. -/
noncomputable def interiorAuditA0 : ℕ :=
  initialRefRows (xTdepth 7) (Fintype.card (Fin 64))

/-- **`09:1219` EVALUATED at the pole's values.**
`A_0 = ceil(2 . 2^{-7} . 64) = ceil(1) = 1`.  The numeral is an output of the
frozen display, not an input. -/
theorem interiorAudit_A0_is_evaluated : interiorAuditA0 = 1 := by
  have hcard : (Fintype.card (Fin 64) : ℕ) = 64 := by simp
  have h : (2 : ℝ) * xTdepth 7 * ((Fintype.card (Fin 64) : ℕ) : ℝ) = 1 := by
    rw [hcard]
    norm_num [xTdepth]
  rw [interiorAuditA0, initialRefRows, h]
  simp

/-- **`09:1233--1235` at the pole's instance.**  Every started coordinate retains
all `A_r = 2^6 A_0 = 64` reference rows, so the frozen retention holds with
equality. -/
theorem interiorAudit_hR (i : Fin 9) :
    refRowFloor interiorAuditA0 6 ≤ (interiorAuditRows i).card := by
  rw [interiorAudit_A0_is_evaluated, refRowFloor]
  simp [interiorAuditRows]

/-- **`09:1195--1200` at the pole's instance**, by the banked
`RoutingDynamics.completedNoBob_bobCappedLadder` (`RoutingDynamics.lean:1236`,
itself `09:1195--1213` on the Bob-capped shape), consumed by pin and not
re-proved here: `CompletedNoBob interiorAudit 6`.  Proved, not assumed. -/
theorem interiorAudit_completedNoBob : CompletedNoBob interiorAudit 6 :=
  RoutingDynamics.completedNoBob_bobCappedLadder _ _ _

set_option maxRecDepth 10000 in
/-- **`09:1240--1252` EVALUATED at the pole's instance.**

The certificate started in each coordinate splits at the root -- both children
hold `32 >= ceil(A_6/2) = A_5 = 32` of the `64` reference rows, so `09:1244`
fires -- and is then routed uniquely at depths `1` and `2`, because the ladder
repeats the same Alice question and the off-branch child holds `0` rows against
the floors `A_4 = 16` and `A_3 = 8`.  Each branch stops at its first Bob query
(`09:1250`), at depth `3`.  Nothing is asserted: every decision is the computed
`splitsAt` / `routeBit` of the banked routing dynamics. -/
theorem interiorAudit_coordRoutes (i : Fin 9) :
    coordRoutes interiorAudit interiorAuditRows interiorAuditA0 6 i
      = {([false, false, false] : List Bool), ([true, true, true] : List Bool)} := by
  rw [interiorAudit_A0_is_evaluated]
  change (descendants interiorAudit (Finset.univ : Finset (Fin 64)) 1 6 6
      ([] : List Bool)).toFinset = _
  decide

/-- The pole's frontier node: the all-`false` branch, an exposed first-Bob
address of depth `d_v = 3`. -/
def interiorAuditNode : FrontierNode interiorAudit interiorAuditRows interiorAuditA0 6 :=
  ⟨[false, false, false], mem_frontierRoutes_of_mem_coordRoutes (i := (0 : Fin 9))
    (by rw [interiorAudit_coordRoutes]; simp)⟩

/-- **Aux (the pole node's address).**  `d_v = 3`: three Alice queries were
routed before the branch stopped, which is what `hbranch` and `hq4` need in
order to be jointly satisfiable at all. -/
@[simp] theorem interiorAudit_node_val :
    interiorAuditNode.val = ([false, false, false] : List Bool) := rfl

/-- **`09:1255` EVALUATED at the pole node.**  `kappa_v = 2^{6-3} = 8`, strictly
below `t_ref = 2^4 = 16`: the interior of branch (ii)'s guard `09:1277`, not the
boundary `09:1269` assigns to branch (i). -/
theorem interiorAudit_kappa :
    kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode = 8 := rfl

/-- **Aux (the pole node lies on every coordinate's route).**  All nine started
coordinates reach it, which is what makes its weight the frozen `9/2`. -/
theorem interiorAudit_node_mem_coordRoutes (i : Fin 9) :
    interiorAuditNode.val ∈ coordRoutes interiorAudit interiorAuditRows interiorAuditA0 6 i := by
  rw [interiorAudit_node_val, interiorAudit_coordRoutes]
  simp

/-- **`09:1244--1248` EVALUATED at the pole node.**  The certificate split at the
root, so every descendant is a **low** certificate; its weight is the frozen
`1/2`, and it stays `1/2` through the two unique routings of depths `1` and `2`
("A low certificate keeps weight `1/2`, whether it has one or two qualifying
children"). -/
theorem interiorAudit_kindAlong (i : Fin 9) :
    kindAlong interiorAudit (interiorAuditRows i) interiorAuditA0 6
        ([false, false, false] : List Bool) = CertKind.low := by
  have hsplit : splitsAt interiorAudit (interiorAuditRows i) interiorAuditA0 6
      ([] : List Bool) = true := by
    rw [interiorAudit_A0_is_evaluated]
    change splitsAt interiorAudit (Finset.univ : Finset (Fin 64)) 1 6 ([] : List Bool) = true
    decide
  have hsb : splitBefore interiorAudit (interiorAuditRows i) interiorAuditA0 6
      ([false, false, false] : List Bool) = true := by
    rw [splitBefore]
    simp only [List.length_cons, List.length_nil]
    refine List.any_eq_true.mpr ⟨0, by simp, ?_⟩
    simpa using hsplit
  simp [kindAlong, hsb]

/-- **`09:1257` EVALUATED at the pole node.**  `W_v = 9/2`: nine **low**
certificates of the frozen weight `1/2` each.  Every summand is the derived
`kindAlong` weight of the routing, never assigned. -/
theorem interiorAudit_frontierWeight :
    frontierWeight interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
      = 9 / 2 := by
  classical
  rw [FirstBobFrontierInstance.frontierWeight_eq_sum_reaching]
  have hterm : ∀ i : Fin 9,
      (if interiorAuditNode.val
          ∈ coordRoutes interiorAudit interiorAuditRows interiorAuditA0 6 i
        then (kindAlong interiorAudit (interiorAuditRows i) interiorAuditA0 6
          interiorAuditNode.val).weight else 0) = (1 / 2 : ℝ) := by
    intro i
    rw [if_pos (interiorAudit_node_mem_coordRoutes i)]
    rw [interiorAudit_node_val, interiorAudit_kindAlong i]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp [Finset.card_univ]
  norm_num

/-- **The pole node is a first-Bob node of the canonical routed system.**

`FrontierIndexing.canonicalSystem`'s `firstBob` is the frozen exposure rule
`09:1251--1252` -- `d_v < r` -- and the pole node has `d_v = 3 < 6`. -/
theorem interiorAudit_firstBob_true :
    (canonicalSystem interiorAudit_completedNoBob interiorAudit_hR).firstBob
      interiorAuditNode = true := by
  decide

/-- **The join's conclusion is FALSE at the pole node.**

The heavy threshold of `09:1268--1269` is met with **equality** there:
`vartheta kappa_v = (9/16) . 8 = 9/2 = W_v`, both sides evaluations of
`interiorAudit_kappa` and `interiorAudit_frontierWeight`.  So
`eq:wrapper-first-bob-light` is refutable at a node **inside** branch (ii)'s
strict guard, not only at `splitAudit`'s boundary node. -/
theorem interiorAudit_is_not_light :
    ¬ (frontierWeight interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
        < vartheta
          * ((kappaAt interiorAudit interiorAuditRows interiorAuditA0 6
              interiorAuditNode : ℕ) : ℝ)) := by
  rw [interiorAudit_kappa, interiorAudit_frontierWeight, vartheta_val]
  norm_num

/-- **The pole's OWN premise bundle, minus the two certificate clauses, is
INHABITED at the pole instance.**

This is the fact that makes the pole below a measurement.  Every hypothesis of
`interiorAudit_forces_a_join_hypothesis_to_fail` except `hbase` and `hselect` is
listed here and proved at one concrete tuple, *at the pole's own node*: the
alleged protocol's budget clause `hcost` (`interiorAudit` has cost `4` against
the budget `C + r - 1 = 8`), `hC` at `09:1302`'s own floor `C = 3`, the two
carrier nonemptiness clauses of `A:111`, branch (ii)'s guard `hbranch` read at
`kappaAt` (`8 <= 16`), the schedule clause `hq4` at `k_ref = 4`, the positivity
and range clauses of the frozen `y_* = 3/5` (`09:314--315`), and
`eq:wrapper-low-simple-gate`'s `hgate` at the banked closed-form row density
`WrapperLowRungs.wrapperLowRungGates_legal_instance 4 6`.

Contrast `splitAudit`, where `hbranch` and `hq4` alone are already
contradictory: there no such list can exist, which is exactly why the pole moved.

**BEYOND-PAPER** in `(r, d_v, k_ref) = (6, 3, 4)`, as everywhere in this
section; `C = 3` and `y = 3/5` are the paper's, and `x_T` is the banked
accessor's closed form, never a numeral shortcut of it. -/
theorem interiorAudit_pole_binders_inhabited_except_certificates :
    interiorAudit.cost ≤ 3 + 6 - 1
      ∧ (3 : ℕ) ≤ 3
      ∧ 1 ≤ Fintype.card (Fin 1)
      ∧ 1 ≤ Fintype.card Bool
      ∧ (0 : ℝ) < 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ (0 : ℝ) < 3 / 5
      ∧ (3 : ℝ) / 5 ≤ 1
      ∧ kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
          ≤ tRef 4
      ∧ (4 : ℕ) + 2 ≤ 6
      ∧ ((2 : ℝ) ^ (6 : ℕ)) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025 := by
  obtain ⟨-, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  refine ⟨by decide, le_refl 3, by simp, by simp, hpos, by norm_num, by norm_num, ?_,
    by norm_num, by rw [hval]; norm_num⟩
  rw [interiorAudit_kappa]
  norm_num [tRef]

/-- **The join's hypothesis bundle is load-bearing, at a point where its
schedule sub-bundle is jointly satisfiable.**

Contrapositive of `branchTwo_firstBobLight_join` at the pole node, whose
conclusion `interiorAudit_is_not_light` refutes.  Whatever `G`, `C`, `k_ref`,
`x_T`, `y` and selected bit are chosen, the join's remaining hypotheses --
the alleged protocol's budget `hcost`, the base certificate `hbase`, the gates
and `hselect` -- **cannot all hold** at this instance.

*What makes this a measurement rather than an arithmetic accident.*  Here
`kappa_v = 8` and `r = 6`, so `hbranch : 8 <= 2^{k_ref}` and
`hq4 : k_ref + 2 <= 6` read `3 <= k_ref <= 4` and hold **together**.
`interiorAudit_pole_binders_inhabited_except_certificates` proves the point
outright: every hypothesis below except `hbase` and `hselect` holds at one
concrete tuple at this very node.  So the excluded conjunction is not two
scalars of the schedule contradicting each other -- what the contradiction
attributes to is `hbase` and `hselect` against the routed weight.  `hcost` is
*separately inhabited* at that tuple (and is implied by `hC` here), so it is
not part of the excluded pair.

It is **not** a canonical inhabitation and discharges nothing: `hbase` and
`hselect` are properties of the certified restriction and of the alleged
protocol, and their joint inhabitation is the REGISTERED and DEFERRED
obligation the header names. -/
theorem interiorAudit_forces_a_join_hypothesis_to_fail {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Gmat : Rw → Cl → Bool) {C kref : ℕ} {xT y : ℝ} (b : Bool)
    (hcost : interiorAudit.cost ≤ C + 6 - 1) (hC : 3 ≤ C)
    (hX : 1 ≤ Fintype.card Rw) (hY : 1 ≤ Fintype.card Cl)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (hbranch : kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
      ≤ tRef kref)
    (hq4 : kref + 2 ≤ 6) (hgate : ((2 : ℝ) ^ (6 : ℕ)) * xT ≤ 4 / 25025)
    (hselect :
      smallCopyWidth
          (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode)
          ≤ (representedCoords interiorAudit interiorAuditRows interiorAuditA0 6
              interiorAuditNode).card →
      LambdaGE Gmat
          (2 ^ (Nat.log 2
            (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6
              interiorAuditNode) - 1) + 1)
          (((kappaAt interiorAudit interiorAuditRows interiorAuditA0 6
              interiorAuditNode : ℕ) : ℝ) * xT)
          (y ^ 2)
        ≤ (descend interiorAudit (interiorAuditNode.val ++ [b])).cost) :
    False :=
  interiorAudit_is_not_light
    (branchTwo_firstBobLight_join Gmat interiorAudit_completedNoBob interiorAudit_hR b
      interiorAudit_firstBob_true hcost hC hX hY hxT0 hy0 hy1 hbase hbranch hq4 hgate hselect)

/-- **The join's arithmetic and schedule group is JOINTLY SATISFIABLE, inside
branch (ii).**

The part of the join's bundle that can conflict is the arithmetic one, and it
pulls in three directions at once: `eq:wrapper-low-simple-gate`'s
`2^r x_T <= 4/25025` wants `x_T` small, `09:1277` wants the capacity strictly
below `t_ref`, and `09:1290`'s `rho = 2y^2` fixes `y = 3/5`, which must still
satisfy `0 < y <= 1`.  All of them hold at once at `r = 6`, `d_v = 3`, `k_ref = 4`
and `C = 3` (`09:1302`'s minimum), with `x_T` the banked closed-form accessor's
value and the legality clause obtained by *calling*
`capacity_row_density_legal_at_capacity` rather than by re-deriving it.

`y = 3/5` is **not** ours: it is the frozen `y_*` of `09:314--315`, the same value
`WrapperProjectionCovers.rhoSmall_eq_two_y_sq` records as `rho = 2y^2 = 18/25`.
`C = 3` is `09:1302`'s own floor.

**BEYOND-PAPER** in `(r, d_v, k_ref) = (6, 3, 4)`, exactly as
`branchTwo_legality_at_interior_capacity`: `A:117` with `A:26` forces
`t_ref >= 2^{2^20}`.  What is claimed is joint satisfiability of the group, not
legality of the tuple; the remaining hypotheses of the join -- `hcost`, `hbase`
and `hselect` -- are properties of the alleged protocol and of the certified
restriction, and their inhabitation is the REGISTERED and DEFERRED canonical
obligation, not something a numeric probe can supply. -/
theorem join_gate_group_jointly_satisfiable :
    (3 : ℕ) ≤ 3
      ∧ kappaFrontier 6 3 ≤ tRef 4
      ∧ (4 : ℕ) + 2 ≤ 6
      ∧ (0 : ℝ) < 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ (0 : ℝ) < 3 / 5
      ∧ (3 : ℝ) / 5 ≤ 1
      ∧ ((2 : ℝ) ^ (6 : ℕ)) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025
      ∧ ((kappaFrontier 6 3 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 1 := by
  obtain ⟨-, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  refine ⟨le_refl 3, by norm_num [kappaFrontier, stoppingCapacity, tRef], by norm_num,
    hpos, by norm_num, by norm_num, by rw [hval]; norm_num, ?_⟩
  exact capacity_row_density_legal_at_capacity (r := 6) (d := 3) (kref := 4) (le_of_lt hpos)
    (by norm_num [kappaFrontier, stoppingCapacity, tRef]) (by norm_num)
    (by rw [hval]; norm_num)

end AuditPole

end EthInapproximability.ParameterizedNP.TranscriptLevelJoin
