import EthInapproximability.ParameterizedNP.TranscriptLevelConstruction

/-!
# Parameterized NP route: the `L1` successors of the transcript-level construction

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche, after the last edit to the file it pins.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:105`**, `q = 2^r`, the scale-alignment width.
    * **`09:113--116`**, the defining display of the reference matrix:
      `R_G = {base} x Omega x [w_0]` inside `Rows(N)`, `G = extract N R_G
      Cols(N)`, and **`m_G = abs(Rows(G))`** (`09:116`).  This is the *defining*
      display of `m_G`, and the only one: in `09-first-wrapper.tex` the symbol
      occurs at `116`, `117`, `1219`, `1228--1229`, `1294`, `1327` and `1637`,
      and every occurrence after `117` is a **use**.  In particular `09:1270`
      (the certified-scale invocation on `G`) does not mention `m_G` at all, so
      it can never be its anchor -- the record repair carried as `L1-F7`.
    * **`09:1219`**, `A_0 = ceil(2 x_T m_G)`; **`09:1221`**, `A_k = 2^k A_0`.
    * **`09:1238--1248`**, the routing rule, the frozen halving
      `ceil(A_k/2) >= A_{k-1}`, and the weight bookkeeping (clean weight `1`,
      split descendants low with weight `1/2`).
    * **`09:1250--1252`**, the two stopping rules and the exposure rule.
    * **`09:1253--1257`**, `d_v`, `kappa_v = 2^{r-d_v}` (`09:1255`), `W_v`.
    * **`09:1259`**, "Every first-Bob node has `kappa_v >= 2`".
    * **`09:1268`**, `vartheta = 9/16`, and the heavy condition
      `W_v >= vartheta kappa_v`.
    * **`09:1269--1275`, branch (i)**: `r' = kappa_v/t_ref`, `a^sharp = 1`.
    * **`09:1276--1296`, branch (ii)**: `2 <= kappa_v < t_ref`,
      `ell_v = log_2 kappa_v` (`09:1277--1278`); the census chain
      `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}` (`09:1280--1283`) with the
      case split of `09:1285--1287`; the projection sentence `09:1287--1290`
      (`rho = 2y^2`, denser Bob child retains `y^2`); and the row side
      `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G`, "so trim it to the row
      density `kappa_v x_T`" (`09:1291--1296`).  **This is the paragraph
      Section 5 traces.**
    * **`09:1296--1301`**, the `lem:certified-row-ladder` call with
      `M = G`, `H = C-1`, `x = x_T`, `z = y`, `ell = ell_v`.
    * **`09:1302--1304`**, "`C >= 3` verifies `H >= 2`, and
      `kappa_v x_T <= t_ref x_T <= 1` verifies legality".
    * **`09:1304--1308`**, "The selected Bob child therefore has complexity at
      least `C + log_2 kappa_v - 1` ...  Its lower bound is one more bit than the
      remaining child budget in the alleged protocol."
    * **`09:1309--1313`** (`eq:wrapper-first-bob-light`), `W_v < vartheta
      kappa_v`: the statement this module moves **toward** and does **not**
      prove; see the residue list.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`):
    `08:166`, `x_T = 2^{-b_T}` (the banked `DenseStageFourOpening.xTdepth`), and
    `08:986--989`, the dense frontier's `kappa_v = 2^{r-d_v}`.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    `A:117--118` (`t` a power of two divisible by `16`, `t >= t_cert`), `A:120`
    (`p_t = 9t/16`), `A:125` (`q = r t`), `A:138--141` (the three supply
    demands), and `A:26` (`t_cert = 2^{2^20}`).
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `eq:tref-search` (`06:558--571`; the search body is `06:561--569`, whose last
    line is the defining `t_ref = 2^{k_ref}`), the defining display of `k_ref`, consumed
    only through the banked `WrapperReferenceConstruction.tRef`; and
    `06:237--243`, `k_T = log_2(s/4)`, `b_T = 2^{j_49(k_T)}`, `x_T = 2^{-b_T}`,
    the display that makes `b_T` a **DEFINED** quantity.
* **Reader counterpart (module level; claimed by no declaration below).**
  `routes/parameterized-np/reader-facing/sections/A-stage4-details.tex:390--392`
  -- "Its small-capacity and final-node closures use the certified row ladder
  ...; they do not require a new odd-copy theorem."  That is the reader's only
  trace of branch (ii), and it is unnumbered connective prose inside a proof,
  not a numbered statement; the reader-counterpart rule forbids citing prose as
  a statement.  The one numbered reader item it points at,
  `lem:paper-certified-row-ladder` (`reader 02:244--256`), is **already claimed**
  by `TerminalTwoStream`, and the rule forbids assigning one reader item to two
  declarations.  The trace is therefore recorded once, here, at module level.

## What this module is

`TRANSCRIPT-LEVEL-CONSTRUCTION-001` registered four named successors
(`L1-F1`--`L1-F4`) and left residue `L1` branch (ii) open.  This tranche
executes all four successors and traces branch (ii) as far as the frozen text
supports without the unbuilt certified stopping/ladder endpoints.

**Section 1 is `L1-F1`.**  The predecessor's headline carried `hA` (the
certificate's row count) as a binder "only so that the theorem stays general in
`A_0`", and named the composition as a gap.  `exists_frontier_routedTriple_at_paper_schedule`
closes it: at the paper's own `A_0 = ceil(2 x_T m_G)` (`09:1219`) with `m_G`
**pinned to the row carrier** `Fintype.card X` -- `09:113--116` defines `m_G` as
the row count of the reference matrix `G`, and here those rows sit on `X` -- and
at a node sitting on coordinate `i`'s route, `hA` is discharged by the
predecessor's
`certificate_rows_meet_trim_demand` and the row set is the certificate's own
`rowsAt P (R i) v.val` rather than a free `Finset`.  The one place where a
schedule quantity floated free of its carrier is gone.

**Section 2 is `L1-F3`.**  The predecessor probed only `hcap` of its two new
binders.  `frontierBlockCount_needs_the_kref_floor` fires the missing one at the
witness the predecessor computed: at `r = 4`, `d_v = 0`, `k_ref = 3` the branch
guard `hcap` **holds** while `hk` fails, and the census identity
`r' p_{t_ref} = p_{kappa_v}` fails with it -- `2 . 4 = 8` against
`p_{16} = 9`.  So `hk` is load-bearing independently of `hcap`, and the
`16 | t` demand of `A:117--118` is not decoration.

**Section 3 was `L1-F2`, and it carried the tranche's one deflationary finding.**
The predecessor's pole 2 fired `hone` at `x = 0`, a point `08:166` can never
reach.  Re-fired inside the legal range, `hone` turned out to be
**dischargeable**: the banked trimming conclusion follows from `hA` alone
whenever `x > 0`, `m > 0` and the two widths are positive, because then
`z = r' t x m > 0` already, which was the only use the **then-banked**
`exists_trimmed_reference_rows` made of `hone`.  So `hone` was load-bearing
**only** at `x = 0`.  `L1-F6` acted on that in tranche `cc-t5h` -- the banked
lemma now carries `hpos` and no `hone` -- and `L1-F9`'s deduplication half then
**deleted** the finding's own declaration here as a duplicate of the interface it
produced (see "This generation").  What remains in Section 3 is the part that is
not a duplicate: `hone_can_fail_at_legal_positive_xT`, exhibiting a legal
positive `x_T = xTdepth b_T` and a carrier at which `1 <= kappa_v x_T m_G` is
false, so the retirement is a strict weakening and not a rename.  Section 3
therefore states the trim **nowhere at all**; the one-step recovery of the
deleted unbundling from the four positivity facts is a *new* statement, which no
registered successor licenses, and it is carried as successor `L1-F10` rather
than declared here.

**Section 4 is `L1-F4`.**  The predecessor's audit instance sat at `d_v = 0`
where no Alice query is routed and no certificate splits.  Section 4 builds an
instance at `d_v = 1` whose root **is** an Alice query and at which the frozen
split of `09:1244` genuinely fires (both children qualify, so
`splitsAt = true`), every certificate becomes `low` with the frozen weight
`1/2` (`09:1246`), and the six-clause heavy bundle still holds -- now with `hA`
**discharged through Section 1** rather than supplied.  The weight bookkeeping of
`09:1244--1248` and the halving of `09:1239--1243` are exercised, which is
exactly what `L1-F4` asked for.

**Section 5 is residue `L1` branch (ii)**, `09:1276--1296`, traced toward
`eq:wrapper-first-bob-light` at its honest extent -- see the residue list for
what that extent excludes.

## This generation: `L1-F9`'s deduplication half + `WDFW-F13`'s consumers

Two registered successors, in tranche `cc-t5i` (statement gate REVISE at round
`r0`, repaired in round `r1`), taken together because the second is what makes
the first's residue visible.  **No new mathematics is claimed, no residue is
narrowed, and no declaration is added**; one duplicate leaves `src/` and one
retired binder stops being carried.  The module's declaration count moves
`40 -> 39`, and that is the whole of its arithmetic.

* **`L1-F9`, deduplication half.**  `exists_trimmed_reference_rows_in_the_positive_regime`
  is **deleted**.  Since `L1-F6` it has been logically equivalent to the banked
  `WrapperDenseFrontierWiring.exists_trimmed_reference_rows` -- by
  `trim_positivity_iff_factors_positive` its four unbundled positivity binders
  and that lemma's single `hpos` are the same hypothesis -- so it was a second
  name for a banked interface, which is the defect `cc-t5d-r2` removed from the
  join.  The consumer census was taken first-hand over `src/` **before** the
  deletion and found exactly one proof consumer,
  `positive_regime_trim_holds_where_hone_fails`; it now fires the banked lemma
  **directly**, with its three conjuncts byte-identical, converting its four
  positivity facts at the call site through
  `trim_positivity_iff_factors_positive.mpr`.  Round `r0` instead re-declared the
  deleted *type* under the name `trim_of_unbundled_positivity`, which renames a
  duplicate rather than removing one; round `r1` deletes that too, so **no
  statement of the trim survives anywhere in this module**.
* **`WDFW-F13`, the consumer side.**  The banked supply gave up the paper-shaped
  `hone : kappa_v x_T m_G >= 1` in `cc-t5h`, but
  `TranscriptLevelConstruction.exists_frontier_routedTriple_at_paper_indices` and
  this module's `exists_frontier_routedTriple_at_paper_schedule` went on carrying
  it and weakening it at the call.  Both now carry `hpos` in the same binder
  position with their conclusions byte-identical, so both are strictly stronger.
  The two audit witnesses (`heavy_bundle_jointly_satisfiable_at_positive_depth`
  here, `heavy_frontier_bundle_is_jointly_satisfiable` in the predecessor)
  deliberately keep the **retired, stronger** clause and weaken it at the call:
  retiring a binder must not quietly weaken the evidence that the bundle is
  inhabited.
* **What the retirement bought, and what this tranche may say about it.**
  `hone_can_fail_at_legal_positive_xT` -- unchanged, and the only surviving
  member of Section 3 -- exhibits legal schedule values at which the retired
  binder is false, while the replacement is a positivity the schedule always
  supplies (`08:166`'s `x_T = 2^{-b_T} > 0` over a nonempty row carrier: `A:111`,
  read at `m_G = abs(Rows(G))`, `09:113--116`).  Turning that supply into its own
  declaration is a **new theorem**, which neither `L1-F9` nor `WDFW-F13`
  licenses; it is registered as successor `L1-F10` and deliberately not taken.
* **Scope.**  No anchor is re-cited, no deferral is discharged, no residue below
  is narrowed, the canonical-inhabitation deferral stands unchanged, and
  `L1-F5` is untouched.  `L1-F9` is spent in full (its rename half landed in the
  same tranche, in a disjoint body); `WDFW-F13` is spent.

## CANONICAL INHABITATION -- registered, not discharged

The paper's own instance at `09:1268` is the routing of an **alleged**
`(C+r-1)`-bit protocol computing a member of `<U,1,1-delta_U,theta>`
(`09:1188--1193`).  No such protocol exists -- that is the conclusion of the
argument -- so the paper's object is a *function of the assumed protocol*, and
the honest Lean form is the implication each theorem below states.  The
canonical-inhabitation obligation is therefore **REGISTERED and DEFERRED**,
exactly as `WRAPPER-DENSE-FRONTIER-WIRING-001` obligation (ii) and
`TRANSCRIPT-LEVEL-CONSTRUCTION-001` record it; it is discharged when the
schedule-level construction lands, and **never** by a probe here.  Section 4's
instance is labelled **NON-FIDELITY / BEYOND-PAPER** and discharges nothing.

## Residues this module does NOT close (named, not implied)

* **`eq:wrapper-first-bob-light` (`09:1309--1313`) is NOT proved.**  What lands
  is the *comparison* of `09:1304--1308`: at a first-Bob node of an alleged
  `(C+r-1)`-bit protocol the **selected Bob child**'s residual budget is at most
  `C + ell_v - 2`, so the branch's own output `C + ell_v - 1` is impossible.  The
  output bound itself is the unbuilt `lem:certified-row-ladder` call composed
  with the unbuilt `hselect` of `09:1287--1296`; both stay hypotheses.  The
  assembled light bound remains the banked, still-conditional
  `FirstWrapperAssembly.firstBobLight_assembled`, unchanged by this tranche.
* **`09:1287--1290` stays GAP-EXPOSED** in its projection form, verbatim as both
  predecessors left it.  Section 5 supplies only the *evaluation*
  `certifiedColFloor rho 1 = y^2` at the frozen `rho = 2y^2` -- the arithmetic of
  "the denser Bob child retains density at least `y^2`", not the projection
  statement.
* **`L1a`, the completion construction** (`09:1203--1207`), and **`L1b`, the
  initial-survival gates** (`09:1224--1235`), are untouched: `CompletedNoBob` and
  the retention floor enter as the banked binders, exactly as before.
* **The certified-lemma residues are not narrowed.**  `thm:certified-localized-extension`
  (`A:285--329`), `lem:certified-row-ladder`'s own proof, and
  `ReferenceStoppingEndpoint` are consumed by pin where they are consumed at all,
  and are neither re-derived nor discharged.
* **`lem:final-reference-uniqueness` (`09:1315--1344`) is untouched**;
  `eq:wrapper-u-dense` is not approached; `thm:first-wrapper` is not proved;
  **no route completion is claimed.**

## Successors this module registers

* **`L1-F5` -- the branch-(ii) closure, assembled at the node.**  Section 5
  lands the ladder call at `ell = ell_v` and the budget comparison separately.
  Joining them into `W_v < vartheta kappa_v` needs `hselect` (`09:1287--1296`,
  GAP-EXPOSED item 15 of `SPLIT-FIRST-BOB-INSTANCE-001`) discharged at the routed
  census, which no tranche has attempted.
* **`L1-F6` -- the `hone` binder should be retired from the frontier supply.
  DISCHARGED in tranche `cc-t5h`.**  Section 3 proved it dischargeable in the
  legal regime.  Retiring it meant restating
  `WrapperDenseFrontierWiring.exists_trimmed_reference_rows` and
  `exists_frontier_routedTriple` at the weaker hypothesis, which is an edit to a
  banked module and therefore its own tranche -- that tranche is `cc-t5h`, which
  did exactly this.  Both now carry `hpos : r' t x m > 0` in the same binder
  position with the conclusions byte-identical, so both are strictly stronger.
  Nothing in *this* module edits them; the sentences below written against the
  pre-retirement interface are marked as such.
  * **Consequence, registered as successor `L1-F9`** (`L1-F8` is already spent,
    on `SELECT-DISCHARGE-001`)**.**  With `L1-F6` taken,
    `exists_trimmed_reference_rows_in_the_positive_regime` (§3) and the banked
    `exists_trimmed_reference_rows` are **logically equivalent** -- by
    `WrapperDenseFrontierWiring.trim_positivity_iff_factors_positive`, this
    module's four positivity binders and that module's single `hpos` are the same
    hypothesis.  §3 is therefore now a redundant unbundling of the banked
    interface.  Deduplicating it, and renaming
    `positive_regime_trim_is_strictly_stronger` (which after `L1-F6` no longer
    describes a strict strengthening -- see its own docstring), are interface
    changes and so their own tranche.
    * **`L1-F9`'s RENAME half, DISCHARGED in tranche `cc-t5i`.**  The stale name
      is gone: the theorem is now
      `positive_regime_trim_holds_where_hone_fails`, which is exactly what its
      three conjuncts assert at the BEYOND-PAPER point (`hone` fails there, the
      row supply `hA` holds, and the trim is still delivered).  The old name is
      **not** retained as an alias -- the declaration is consumed by nothing, so
      no proof term moves -- and **not one statement byte changes**: the three
      conjuncts are byte-identical to the banked ones, as the docstring's own
      "true exactly as stated" sentence already recorded.
    * **`L1-F9`'s DEDUPLICATION half, DISCHARGED in tranche `cc-t5i`** (see "This
      generation" below).  `exists_trimmed_reference_rows_in_the_positive_regime`
      is **deleted**; its one `src/` consumer, the renamed non-vacuity witness
      above, fires the banked lemma directly with its three conjuncts unchanged.
      No declaration of the same type is left behind under another name, which is
      what round `r0` of the tranche attempted and the statement gate rejected.
      `L1-F9` is therefore spent in full.
* **`L1-F10` -- the retirement's supply side, REGISTERED and NOT taken.**  The
  four licensed items of tranche `cc-t5i` are `L1-F9` (a deletion and a rename),
  `WDFW-F13` (a binder retirement with consumer updates), `WDFW-F14` (a rename)
  and `WDFW-F15` (a one-token tactic edit).  **None of them licenses a new
  theorem.**  Round `r0` nevertheless added five, and round `r1` drops all five
  and registers them here instead: the one-step recovery of the deleted
  unbundling from the four positivity facts; the discharge of the replacement
  binder at `08:166`'s `x_T = 2^{-b_T}` over a nonempty row carrier (`A:111` read
  at `09:113--116`); the node-level reading of that binder as *exactly* positive
  density over a nonempty carrier; the schedule specialisation of the banked
  `certifiedRowFloor_pos_iff_trim_positive`; and the `x = 0` pole for the
  existential deliverable.  They are to be re-landed against residue `L1`
  **together with their consumers**, so that each is load-bearing rather than an
  unwired endpoint; the round-`r0` bytes are preserved on the parked commit named
  in the `TRANSCRIPT-LEVEL-SUCCESSORS-001` ledger row.  Until then this module
  states none of them.

## Axioms and imports

The only import is `TranscriptLevelConstruction`, whose own only import is
`WrapperDenseFrontierWiring`; so there is no `LegacyNPCC.Stage12` in the
transitive closure and no contact with the AGHP balanced-family axiom.
`EXPANDER-001` occurs in no hypothesis of any declaration below.  No `axiom`, no
opaque certificate, no unproved obligation marker.

## DEFINED-VS-FREE ledger for this tranche

| quantity | status | how it is obtained here |
| --- | --- | --- |
| `kappa_v` | DEFINED, `09:1255` | the banked `kappaFrontier` / `kappaAt` |
| `ell_v` | DEFINED, `09:1278` | `Nat.log 2 kappa_v`, evaluated to `r - d_v` |
| `r'`, `t`, `a^sharp` | DEFINED, `09:1272--1273` | `frontierCopies`, `tRef`, `1` |
| `p_t` | DEFINED, `A:120` | the banked `certifiedPt`, evaluated |
| `A_0` | DEFINED, `09:1219` | `initialRefRows xT (Fintype.card X)`, evaluated |
| `A_{ell_v}` | DEFINED, `09:1221` | the banked `refRowFloor`, evaluated |
| `vartheta` | DEFINED, `09:1268` | the banked `vartheta` |
| `rho`, `y` | DEFINED, `09:436`, `09:1290` | `rhoSmall`; `y = 3/5` via `rhoSmall_eq_two_y_sq` |
| `x_T` | DEFINED, `08:166` with `06:243` | the banked `xTdepth` at `b_T` |
| `b_T` | **DEFINED**, `06:239--241` | a Lean binder except in the two labelled probes below |
| `m_G` | DEFINED, `09:113--116` | `Fintype.card X`, read at the carrier |
| `k_ref`, `r`, `C`, `y` | binders | never assigned outside the labelled probes |

**Self-chosen values occur in exactly three places, all labelled.**  `b_T = 10`
and the carrier `Fin 16` in `hone_can_fail_at_legal_positive_xT` (Section 3), the
triple `(r,d_v,k_ref) = (4,0,3)` in `frontierBlockCount_needs_the_kref_floor`
(Section 2), and the whole of Section 4.  The first two are **rejection probes
claiming no legality**; Section 4 is an explicitly labelled **BEYOND-PAPER**
audit instance.  Every other numeral is a frozen literal of a cited display
(`1`, `2`, `4`, `9`, `16`) or the output of an evaluation.
-/

namespace EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors

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
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction

/-! ## §1  `L1-F1`: the `hA` discharge, composed at the paper's schedule

The predecessor proved `certificate_rows_meet_trim_demand` -- at the paper's own
`A_0 = ceil(2 x_T m_G)` (`09:1219`) the routed descendant of coordinate `i` holds
at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` rows (`09:1291--1295`) --
and then left `hA` a binder in its headline, recording the composition as
successor `L1-F1`.  It is executed here.

Two things change against the predecessor's headline, and both are the point:

* `A_0` is no longer free.  It is `initialRefRows xT (Fintype.card X)`, i.e.
  `09:1219` with `m_G` read at the **row carrier**: `09:113--116` is the defining
  display, `m_G = abs(Rows(G))`, and this module carries those rows on `X`.
  (`09:1270` only *announces* the certified-scale invocation "on `G`"; the
  substitution display `M = G` itself sits at `09:1299`, and `A:111` names that
  lemma's own `m`.  All three are use sites, and none defines `m_G` -- `09:1270`
  does not even contain the symbol.)  The predecessor's
  `certificate_rows_meet_trim_demand` quantifies over a free `m_G : ℕ` and so
  degenerates at `m_G = 0`; here that cannot happen, because the hypothesis and
  the conclusion read the same carrier.
* `Arows` is no longer free.  It is the certificate's own `rowsAt P (R i) v.val`,
  and `hA` is discharged from the routing invariant. -/

section PaperSchedule

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord]

/-- **`L1-F1`: `09:1268--1296` at the paper's own index tuple AND its own row
schedule.**

The predecessor's `exists_frontier_routedTriple_at_paper_indices` with `hA`
discharged: at `A_0 = ceil(2 x_T m_G)` and `m_G = |X|` (`09:1219` with the
defining display `09:113--116`), on a
frontier node lying on coordinate `i`'s route, the trim demand of `09:1291--1295`
is met by `FrontierIndexing.coordRoutes_rows_floor` and the produced row set is a
subset of the certificate's actual rows.

Compared with the predecessor exactly one hypothesis disappears (`hA`) and one
conclusion sharpens (`T ⊆ rowsAt P (R i) v.val` rather than `T ⊆ Arows` for a
free `Arows`).  Nothing else moves: `r' = kappa_v/t_ref`, `t = t_ref`,
`a^sharp = 1` are the same frozen tuple, and the block count is still discharged
by `frontierBlockCount_le_heavy_ceiling`.

**`WDFW-F13`, taken here as a consumer.**  The predecessor's row-density binder
was the paper-shaped `hone : kappa_v x_T m_G >= 1`, retired from the banked
supply by `L1-F6` (tranche `cc-t5h`) and from the predecessor's own headline by
`WDFW-F13`; this statement follows it, in the same binder position, to
`hpos : 0 < kappa_v x_T m_G`.  The conclusion is byte-identical, so the theorem
is strictly stronger, and every model of the old bundle is a model of the new
one.  The replacement is also what the schedule itself supplies: `08:166`'s
`x_T = 2^{-b_T}` is positive (`xTdepth_pos`) and `A:111`'s row carrier is
nonempty, whereas the retired binder can fail at legal schedule values --
`hone_can_fail_at_legal_positive_xT` exhibits some.  Recording that supply as a
declaration of its own is successor `L1-F10`, deliberately not taken here.

*Why the trivial witness fails.*  `S = empty` has card `0` while the demanded
`r' p_t` is positive at the frozen guards (`paper_blockCount_is_positive`), and
`T = empty` is refuted through the banked `exists_trimmed_reference_rows`, whose
nonemptiness clause forces the row floor `ceil(r' t x m)` to be at least `1`
under `hpos` (`certifiedRowFloor_pos_iff_trim_positive`).  Neither degenerate
choice satisfies the conclusion.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `r`, the
coordinate, the node, `k_ref`, `x_T` and `theta`. -/
theorem exists_frontier_routedTriple_at_paper_schedule (P : Protocol X Y Z)
    (R : Coord → Finset X) (r : ℕ) {xT θ : ℝ} {kref : ℕ} (i : Coord)
    (hR : refRowFloor (initialRefRows xT (Fintype.card X)) r ≤ (R i).card)
    (v : FrontierNode P R (initialRefRows xT (Fintype.card X)) r)
    (hv : v.val ∈ coordRoutes P R (initialRefRows xT (Fintype.card X)) r i)
    (Sc : Finset Y)
    (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length)
    (hY : 0 < Fintype.card Y)
    (hbob : IsBobNode (descend P v.val))
    (hheavy : vartheta
        * ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ)
      ≤ frontierWeight P R (initialRefRows xT (Fintype.card X)) r v)
    (hpos : 0 < ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ)
      * xT * ((Fintype.card X : ℕ) : ℝ))
    (hdens : θ ≤ ((retainedCols P Sc v.val).card : ℝ) / (Fintype.card Y : ℝ)) :
    ∃ (S : Finset Coord) (T : Finset X) (b : Bool),
      S ⊆ representedCoords P R (initialRefRows xT (Fintype.card X)) r v ∧
        T ⊆ rowsAt P (R i) v.val ∧
        RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
          (frontierCopies r v.val.length kref) (tRef kref) 1 xT θ S T
          (retainedCols P Sc (v.val ++ [b])) :=
  exists_frontier_routedTriple_at_paper_indices P R
    (initialRefRows xT (Fintype.card X)) r v Sc (rowsAt P (R i) v.val) hk hcap hY hbob
    hheavy hpos (certificate_rows_meet_trim_demand hR hv) hdens

end PaperSchedule

/-! ## §2  `L1-F3`: the `4 <= k_ref` rejection probe

The predecessor's two new binders were `hk : 4 <= k_ref` (the `16 | t_ref` of
`A:117--118`) and `hcap : k_ref <= r - d_v` (the branch guard of `09:1269`).
Only `hcap` was probed.  The probe below is at the witness the predecessor
computed and is stated so that the two guards are **separated**: `hcap` holds at
the witness, so nothing but `hk` is doing the work. -/

section KrefProbe

/-- **Statement pole: `4 <= k_ref` is load-bearing on its own.**

At `r = 4`, `d_v = 0`, `k_ref = 3` the branch guard `k_ref <= r - d_v` of
`09:1269` **holds** (`3 <= 4`), and yet the census identity
`r' p_{t_ref} = p_{kappa_v}` of `09:1272` with `A:120` **fails**: the demanded
count is `2 . certifiedPt 8 = 2 . 4 = 8` while the frozen `9 kappa_v/16` at
`kappa_v = 16` is `9`.  The natural division of `A:120` floors, and `16 | t_ref`
is exactly what stops it flooring away a block; without `A:117--118`'s
divisibility the frontier census **undercounts by one block**.

So `frontierBlockCount_eq_certifiedPt_kappa` needs `hk` for a reason independent
of `hcap`, and `paperFrontierRestriction_selCard` would read back the wrong count
without it.

Concrete numerals here are a **refutation witness**, not an instantiation, and
`k_ref = 3` is illegal twice over (`A:117--118` demands `16 | t_ref`, and `A:26`
with `A:117` demands `t_ref >= 2^{2^20}`): this statement claims no legality. -/
theorem frontierBlockCount_needs_the_kref_floor :
    ∃ r d kref : ℕ, ¬ (4 ≤ kref) ∧ kref ≤ r - d
      ∧ frontierCopies r d kref * RestrictionDatum.certifiedPt (tRef kref) = 8
      ∧ RestrictionDatum.certifiedPt (kappaFrontier r d) = 9
      ∧ frontierCopies r d kref * RestrictionDatum.certifiedPt (tRef kref)
          < RestrictionDatum.certifiedPt (kappaFrontier r d) := by
  refine ⟨4, 0, 3, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [frontierCopies, tRef, kappaFrontier, stoppingCapacity,
      RestrictionDatum.certifiedPt]

end KrefProbe

/-! ## §3  `L1-F2`: `hone` re-fired inside the legal range, and what replaced it

`08:166` fixes `x_T = 2^{-b_T}`, which is strictly positive for every `b_T`
(`06:239--241` makes `b_T` itself a schedule value, never a free input).  The
predecessor's pole for `hone` fired at `x = 0`, outside that range, and two facts
were needed to describe the binder honestly, neither implying the other.

Since `L1-F6` and `WDFW-F13` retired the binder, `L1-F9` has removed the one
declaration here that had become a duplicate of the banked interface.  What is
left is the three `xTdepth` readouts and the rejection probe
`hone_can_fail_at_legal_positive_xT`, which is what makes the retirement a
strict weakening rather than a rename.  Nothing here states the trim, and
nothing here restates a banked conclusion; the facts describing the
*replacement* binder are registered as successor `L1-F10` and are not declared
in this module. -/

section HoneProbe

/-- **Aux L1-F2/1 (`08:166` is positive at every schedule depth).**  General in
`b_T`: no numeral is assigned, so this holds at the paper's own `b_T` obtained by
evaluating `06:239--241`. -/
theorem xTdepth_pos (bT : ℕ) : 0 < xTdepth bT := by
  rw [xTdepth]
  positivity

/-- **Aux L1-F2/2 (`08:166` is at most one).**  General in `b_T`; this is the
side the legality chain `kappa_v x_T <= t_ref x_T <= 1` of `09:1304` starts
from. -/
theorem xTdepth_le_one (bT : ℕ) : xTdepth bT ≤ 1 := by
  rw [xTdepth, div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

/-- **Aux L1-F2/3 (`08:166` is antitone in the depth).**  A deeper Stage-3 depth
is a smaller row density.  General. -/
theorem xTdepth_antitone {b c : ℕ} (h : b ≤ c) : xTdepth c ≤ xTdepth b := by
  rw [xTdepth, xTdepth]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- **`L1-F2`, first half: `hone` can fail at a legal positive `x_T`.**

At the legal closed form `x_T = xTdepth b_T` (`08:166`) with `b_T = 10` and the
row carrier `Fin 16`, the frozen regime `kappa_v x_T m_G >= 1` is **false** at
the maximal capacity `kappa_v = 2^4 = 16`: `16 . 2^{-10} . 16 = 1/4`.  So the
binder is not automatic inside the legal range -- unlike the predecessor's `x = 0`
probe, which fired at a point `08:166` can never reach.

`b_T = 10` and the carrier are **ours**, and `b_T` is DEFINED by `06:239--241`;
this is a rejection probe and **claims no legality**. -/
theorem hone_can_fail_at_legal_positive_xT :
    0 < xTdepth 10
      ∧ ¬ (1 ≤ ((kappaFrontier 4 0 : ℕ) : ℝ) * xTdepth 10
            * ((Fintype.card (Fin 16) : ℕ) : ℝ)) := by
  refine ⟨xTdepth_pos 10, ?_⟩
  have hcard : (Fintype.card (Fin 16) : ℕ) = 16 := by simp
  rw [hcard]
  norm_num [kappaFrontier, stoppingCapacity, xTdepth]

/-! ### `L1-F9`'s DEDUPLICATION half, DISCHARGED: `L1-F2`'s second half is DELETED

The declaration that stood here was
`exists_trimmed_reference_rows_in_the_positive_regime`: the conclusion of the
banked `WrapperDenseFrontierWiring.exists_trimmed_reference_rows`, obtained from
`hA` together with the four *unbundled* binders `0 < r'`, `0 < t`, `0 < m`,
`0 < x`.  When it was written it was a genuine strengthening, because the banked
lemma still demanded the paper-shaped `hone : kappa_v x_T m_G >= 1`, and its
proof was `L1-F2`'s finding.  `L1-F6` (tranche `cc-t5h`) then acted on that
finding: the banked lemma took the binder `hpos : 0 < r' t x m`, and the banked
`trim_positivity_iff_factors_positive` proves that `hpos` and the four
positivity facts are the **same hypothesis**.  From that moment the two
statements were logically equivalent and this one was a redundant unbundling of
a banked interface, which is what `L1-F9` registered.

**Deleted outright, and NOT re-declared under another name.**  A logically
equivalent second name is not evidence: it lets a later tranche pin the copy
instead of the bank, splits one interface into two, and makes the banked lemma
read as weaker than it is.  That is the same defect the `cc-t5d-r2` dedup
removed from the branch-(ii) join, and the same remedy applies.  Round `r0` of
tranche `cc-t5i` deleted the identifier but immediately re-declared its **exact
type** as `trim_of_unbundled_positivity`, changing only the proof body; that is
a rename of the duplicate, not a deduplication, and every consequence `L1-F9`
listed as the reason to delete survived it verbatim.  The statement gate
rejected it and round `r1` deletes it as well, so after this generation **no
statement of the trim is made anywhere in this module**.

**Consumer census, taken first-hand over `src/` before the deletion.**  Exactly
one proof consumed it: `positive_regime_trim_holds_where_hone_fails` in Section
6, whose third conjunct it produced.  That consumer now fires the banked
`WrapperDenseFrontierWiring.exists_trimmed_reference_rows` **directly**, with
**all three of its conjuncts unchanged**; its four positivity facts are turned
into that lemma's single `hpos` at the call site by the banked
`trim_positivity_iff_factors_positive.mpr`, and nowhere else.  The only other
occurrences of the identifier anywhere in `src/` were prose in this module's own
docstrings, which this tranche rewrites.  `tools/AxiomAudit.lean` carried one
`#print axioms` line for it; that line is dropped and **no line replaces it**.

**Nothing is lost that is not recoverable in one step**, and the recovery is the
banked `iff` itself -- `trim_positivity_iff_factors_positive.mpr` turns the four
binders into `hpos`, exactly as the surviving consumer now does inline.  Making
that step a declaration of its own would be a **new** interface decision, which
`L1-F9` does not license (its whole content is that a statement of this type
should go); it is registered as successor `L1-F10`, to be re-landed with its
consumers, and is not taken here.

The **first** half of `L1-F2` is untouched: `hone_can_fail_at_legal_positive_xT`
above is a rejection probe about a *legal* schedule point, not a duplicate of
anything, and it is what makes the retirement a strict weakening rather than a
rename. -/

end HoneProbe

/-! ## §5  Residue `L1` branch (ii): `09:1276--1296`, toward
`eq:wrapper-first-bob-light`

"When `2 <= kappa_v < t_ref`, write `ell_v = log_2 kappa_v`. ...  Hence the
number of represented coordinates is at least `ceil(W_v)`, and
`ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`. ...  Every represented
coordinate is outside `E_0`, so the parent projection to any selected
`u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob child
retains density at least `y^2`.  Each selected certificate has at least
`A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows, so trim it to the
row density `kappa_v x_T`.  Apply `lem:certified-row-ladder` with `M = G`,
`H = C-1`, `x = x_T`, `z = y`, `ell = ell_v`. ...  `kappa_v x_T <= t_ref x_T <= 1`
verifies legality.  The selected Bob child therefore has complexity at least
`C + log_2 kappa_v - 1`. ...  Its lower bound is one more bit than the remaining
child budget."

Five of those sentences land below.  The one that does not is
`09:1287--1290`'s **projection** form, which stays GAP-EXPOSED; only its
arithmetic consequence is evaluated. -/

section BranchTwo

section Census

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1280--1283` at a node, WITH the middle term the display prints.**

"Hence the number of represented coordinates is at least `ceil(W_v)`, and
`ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`."

The frozen chain has three links and the banked
`SplitFirstBobInstance.heavy_firstBob_smallCopyWidth_le` collapses it to its two
endpoints.  Here all three appear, at the node-indexed capacity of the
predecessor's `kappaAt`:

* `u_{kappa_v} <= ceil(9 kappa_v/16)` is the banked `smallCopyWidth_le_ceil_weight`
  fired at `W := 9 kappa_v/16`, i.e. exactly at the frozen threshold rather than
  at `W_v`; this is where the case split of `09:1285--1287` lives;
* `ceil(9 kappa_v/16) <= ceil(W_v)` is `09:1268`'s heavy condition under
  `Nat.ceil` monotonicity -- the only place the heavy hypothesis is used;
* `ceil(W_v) <= |representedCoords v|` is the banked
  `ceil_frontierWeight_le_card_representedCoords`, consumed by pin.

The middle term is the object `09:1283` is *about*: it is what the selection of
`u_{kappa_v}` coordinates in `09:1288--1289` is counted against, and it had no
name in `src/`.

**Domain note (the statement is deliberately broader than the display), inherited
verbatim from the predecessor's `smallBranch_coverEntry_at_kappaAt`.**  `09:1283`
is printed inside branch (ii)'s paragraph `2 <= kappa_v < t_ref` (`09:1277`), and
`09:440` defines `u_kappa` only there.  This declaration carries **no** upper
guard: it inherits the banked generality and therefore asserts the chain also at
`kappa_v >= t_ref`.  That is a *strengthening*, not a weakening, and it is true
for the paper's own reason (`09:1285--1287`); the census bound it rests on depends
only on `09:1268`'s heavy condition, which is stated *before* the branch split.
A consumer needing the branch restriction must add `kappaAt ... < tRef kref`
itself.

General in `P`, `Coord`, `R`, `A_0`, `r` and the node. -/
theorem branchTwo_census_chain {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hheavy : vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) ≤ frontierWeight P R A0 r v) :
    smallCopyWidth (kappaAt P R A0 r v)
        ≤ ⌈9 * ((kappaAt P R A0 r v : ℕ) : ℝ) / 16⌉₊
      ∧ ⌈9 * ((kappaAt P R A0 r v : ℕ) : ℝ) / 16⌉₊
        ≤ ⌈frontierWeight P R A0 r v⌉₊
      ∧ ⌈frontierWeight P R A0 r v⌉₊ ≤ (representedCoords P R A0 r v).card := by
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  have hℓ : 1 ≤ r - v.val.length := by omega
  have hcapEq : kappaAt P R A0 r v = 2 ^ (r - v.val.length) := rfl
  have hcast : ((kappaAt P R A0 r v : ℕ) : ℝ) = (2 : ℝ) ^ (r - v.val.length) := by
    rw [hcapEq]; push_cast; ring
  refine ⟨?_, ?_, ceil_frontierWeight_le_card_representedCoords P R A0 r v⟩
  · rw [hcapEq]
    refine smallCopyWidth_le_ceil_weight hℓ ?_
    rw [vartheta_val, hcast] at *
    push_cast
    linarith [pow_pos (by norm_num : (0 : ℝ) < 2) (r - v.val.length)]
  · refine Nat.ceil_le_ceil ?_
    rw [vartheta_val] at hheavy
    linarith

end Census

/-- **`09:1288--1290` at the frozen numbers, EVALUATED.**

"the parent projection ... has density at least `rho = 2y^2`.  The denser Bob
child retains density at least `y^2`."  In the certified call's own language the
denser child is `a^sharp = 1` (`09:1273`), and `A:141`'s floor there is
`certifiedColFloor h 1 = h/2`.  Substituting `h = rho` and using the banked
`rhoSmall_eq_two_y_sq` (`09:436`, `rho = 2y^2 = 18/25` at `y = 3/5`) the floor is
literally the frozen `y^2 = 9/25`.

**Scope, stated precisely.**  This is the *arithmetic* of `09:1290`, not the
sentence of `09:1287--1290`, which is about the **projection** `projSet J` of the
retained column set and stays GAP-EXPOSED exactly as
`WrapperDenseFrontierWiring.exists_denser_child_colFloor` records.  Nothing here
narrows that residue. -/
theorem denserChild_colFloor_eq_y_sq :
    RestrictionDatum.certifiedColFloor rhoSmall 1 = ((3 : ℝ) / 5) ^ 2 := by
  rw [RestrictionDatum.certifiedColFloor, ← rhoSmall_eq_two_y_sq]
  norm_num

section RowSide

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

omit [Fintype Coord] in
/-- **`09:1291--1296`, the branch-(ii) trim, REALIZED.**

"Each selected certificate has at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
m_G` reference rows, so trim it to the row density `kappa_v x_T`."

Branch (ii) has no `(r', t)` factorization -- it never calls the certified-scale
reference stopping lemma -- so the banked `exists_trimmed_reference_rows`, whose
floor is `ceil(r' t x m)`, does not state its trim.  The frozen trim target here
is the row density `kappa_v x_T` itself, i.e. `ceil(kappa_v x_T m_G)`, and the
row supply is the predecessor's `certificate_rows_meet_trim_demand`: at the
paper's own `A_0` the routing already delivers `kappa_v A_0 >= 2 kappa_v x_T m_G`
rows at every frontier address.

So the trim is **executed** rather than assumed: a subset of the certificate's
own rows, of card exactly the frozen floor, nonempty.  The frozen factor `2` is
consumed (it is what makes the floor fit inside the certificate) and is not
re-supplied.

*Why the trivial witness fails.*  `hone` forces the floor to be at least `1`, so
`T = empty` cannot have the demanded card.

General in `P`, `Coord`, `R`, `r`, the coordinate, the address and `x_T`; `m_G`
is read at the row carrier throughout. -/
theorem exists_branchTwo_trimmed_rows {P : Protocol X Y Z} {R : Coord → Finset X}
    {r : ℕ} {xT : ℝ} {i : Coord}
    (hR : refRowFloor (initialRefRows xT (Fintype.card X)) r ≤ (R i).card)
    {p : List Bool}
    (hp : p ∈ coordRoutes P R (initialRefRows xT (Fintype.card X)) r i)
    (hone : 1 ≤ ((kappaFrontier r p.length : ℕ) : ℝ) * xT * ((Fintype.card X : ℕ) : ℝ)) :
    ∃ T ⊆ rowsAt P (R i) p,
      T.card = ⌈((kappaFrontier r p.length : ℕ) : ℝ) * xT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ∧ T.Nonempty := by
  classical
  set z : ℝ := ((kappaFrontier r p.length : ℕ) : ℝ) * xT * ((Fintype.card X : ℕ) : ℝ)
    with hz
  have hrows : 2 * z ≤ ((rowsAt P (R i) p).card : ℝ) :=
    certificate_rows_meet_trim_demand hR hp
  have hzpos : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hone
  have hzle : z ≤ ((rowsAt P (R i) p).card : ℝ) := by linarith
  obtain ⟨T, hTA, hTcard⟩ :=
    Finset.exists_subset_card_eq (Nat.ceil_le.mpr hzle)
  refine ⟨T, hTA, hTcard, ?_⟩
  rw [← Finset.card_pos, hTcard]
  exact Nat.ceil_pos.mpr hzpos

end RowSide

/-- **`09:1302--1304`, the legality chain, in the TWO steps the display prints.**

"`kappa_v x_T <= t_ref x_T <= 1` verifies legality."

The banked `DenseWrapperFrontier.capacity_row_density_legal` delivers only the
composite `2^{ell} x_T <= 1`.  The frozen sentence is a chain of two comparisons,
and each carries its own reason: the first is branch (ii)'s guard
`kappa_v < t_ref` (`09:1277`) times the nonnegative `x_T`, the second is the
banked `WrapperLowRungs.simple_gate_forces_tRef_row_legality` reading
`eq:wrapper-low-simple-gate` with `A:118`.  Both are stated, so a consumer that
needs only the first does not silently import the gate.

General in `r`, `d_v`, `k_ref` and `x_T`, at the frozen guards. -/
theorem branchTwo_row_density_legality {r d kref : ℕ} {xT : ℝ} (hxT0 : 0 ≤ xT)
    (hbranch : kappaFrontier r d ≤ tRef kref) (hq4 : kref + 2 ≤ r)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025) :
    ((kappaFrontier r d : ℕ) : ℝ) * xT ≤ ((tRef kref : ℕ) : ℝ) * xT
      ∧ ((tRef kref : ℕ) : ℝ) * xT ≤ 1 := by
  constructor
  · have hle : ((kappaFrontier r d : ℕ) : ℝ) ≤ ((tRef kref : ℕ) : ℝ) := by
      exact_mod_cast hbranch
    exact mul_le_mul_of_nonneg_right hle hxT0
  · have hgateK : ((2 : ℝ) ^ kref) * xT ≤ 1 :=
      simple_gate_forces_tRef_row_legality hq4 hxT0 hgate
    have hcast : ((tRef kref : ℕ) : ℝ) = (2 : ℝ) ^ kref := by
      rw [tRef_eq]; push_cast; ring
    rw [hcast]
    exact hgateK

section LadderCall

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1296--1306`, the branch-(ii) ladder call, at the node's own `ell_v`.**

"Apply `lem:certified-row-ladder` with `M = G`, `H = C-1`, `x = x_T`, `z = y`,
`ell = ell_v`. ...  The selected Bob child therefore has complexity at least
`C + log_2 kappa_v - 1`."

The ladder itself is the banked, **proved**
`DenseWrapperFrontier.smallCapacity_child_bound` (which in turn consumes
`TerminalTwoStream.certifiedRowLadder_of_base` by pin); it is re-derived nowhere.
Two substitutions are performed here and they are the content:

* `ell := ell_v` is the node's own `Nat.log 2 kappa_v` of `09:1278`, evaluated
  through the predecessor's `log_kappaAt_eq_capacity_exponent` -- never a free
  exponent;
* the row density fed to the ladder is written `kappa_v x_T`, which is the
  frozen trim target of `09:1296`, rather than `2^{ell} x_T`.

The conclusion is the frozen `C + log_2 kappa_v - 1` verbatim.  `hlegal` is
`09:1302--1304` (`branchTwo_row_density_legality` supplies it at the frozen
gates); `hbase` is the second clause of `lem:wrapper-reference`, carried as the
binder it is; `hC : 3 <= C` is `09:1302`'s "`C >= 3` verifies `H >= 2`".

*Why the trivial witness fails.*  This is a bound on a named quantity, not an
existential, so the pole is `hlegal`: `capacity_row_density_legal`'s hypothesis
`2^{ell} x_T <= 1` fails as soon as `x_T` exceeds `2^{-ell}`, and the banked
ladder is then unavailable -- which is exactly why `09:1304` verifies it.

General in the matrix carriers, in `P`, `Coord`, `R`, `A_0`, `r`, the node, `C`,
`x_T` and `y`. -/
theorem branchTwo_ladder_call_at_node {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (v : FrontierNode P R A0 r) {C : ℕ} {xT y : ℝ}
    (hX : 1 ≤ Fintype.card Rw) (hY : 1 ≤ Fintype.card Cl) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (hℓ : 1 ≤ Nat.log 2 (kappaAt P R A0 r v))
    (hlegal : ((kappaAt P R A0 r v : ℕ) : ℝ) * xT ≤ 1) :
    C + Nat.log 2 (kappaAt P R A0 r v) - 1
      ≤ LambdaGE Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
          (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) (y ^ 2) := by
  have hlog : Nat.log 2 (kappaAt P R A0 r v) = r - v.val.length :=
    log_kappaAt_eq_capacity_exponent P R A0 r v
  have hcast : ((kappaAt P R A0 r v : ℕ) : ℝ) = (2 : ℝ) ^ (r - v.val.length) := by
    change ((kappaFrontier r v.val.length : ℕ) : ℝ) = _
    rw [kappaFrontier_eq]; push_cast; ring
  have hℓ' : 1 ≤ r - v.val.length := by rwa [hlog] at hℓ
  have hlegal' : ((2 : ℝ) ^ (r - v.val.length)) * xT ≤ 1 := by rwa [hcast] at hlegal
  rw [hlog, hcast]
  exact smallCapacity_child_bound Gmat hX hY hC hxT0 hy0 hy1 hbase hℓ' hlegal'

end LadderCall

section Budget

variable {X Y Z : Type*}

/-- **`09:1306--1308` at the SELECTED Bob child.**

"Its lower bound is one more bit than the remaining child budget in the alleged
protocol."

The banked `RoutedCertificateSystem.firstBob_residual_budget` bounds the budget
at the first-Bob node itself; the frozen sentence compares against the budget of
the **child** the closure selects, one Bob bit lower.  That step is the banked
`DenseWeightedCount.cost_descendStep_succ_le` at the Bob query, and it is
supplied here for either bit -- the closure's own choice of child is not needed.

General in the carriers, in `P`, `r`, `C`, the address and the bit. -/
theorem firstBob_selected_child_budget {P : Protocol X Y Z} {r C : ℕ} {p : List Bool}
    (h : IsFirstBobNode P r p) (hcost : P.cost ≤ C + r - 1) (b : Bool) :
    (descend P (p ++ [b])).cost + (p.length + 1) ≤ C + r - 1 := by
  have hres := firstBob_residual_budget h hcost
  have hbob : IsBobNode (descend P p) := h.2.1
  have hnode : IsQueryNode (descend P p) := by
    revert hbob
    cases descend P p with
    | leaf z => exact fun hb => hb.elim
    | aNode a l r' => exact fun hb => hb.elim
    | bNode f l r' => exact fun _ => trivial
  have hstep : (descendStep (descend P p) b).cost + 1 ≤ (descend P p).cost :=
    cost_descendStep_succ_le hnode b
  have hsplit : descend P (p ++ [b]) = descendStep (descend P p) b := by
    rw [descend_append]
    rfl
  rw [hsplit]
  omega

/-- **`09:1304--1308`: the branch-(ii) closure output is IMPOSSIBLE at the child.**

"The selected Bob child therefore has complexity at least `C + log_2 kappa_v - 1`
...  Its lower bound is one more bit than the remaining child budget in the
alleged protocol."

The frozen contradiction, joined at a routed first-Bob address: with
`d_v = |p|` and `ell_v = r - d_v` (so `kappa_v = 2^{ell_v}`, `09:1255`), the
selected child of the alleged `(C+r-1)`-bit protocol keeps at most
`C + ell_v - 2` bits (`firstBob_selected_child_budget`), while the branch's own
output is `C + ell_v - 1`.  The banked
`DenseWrapperFrontier.firstBob_budget_contradiction` is the arithmetic; what is
new is that its `d`, `ell` and `B` are now the routed node's own, with
`d + ell = r` derived from the exposure rule `09:1251--1252` rather than assumed.

**This is not `eq:wrapper-first-bob-light`.**  It says that *if* the closure
output holds at the child then the alleged protocol cannot exist; the closure
output itself is the unbuilt composition of the `lem:certified-row-ladder` call
with `hselect` (`09:1287--1296`), which stays a hypothesis.  Turning this into
`W_v < vartheta kappa_v` is successor `L1-F5`.

**The conclusion is `False` by design, and the hypothesis bundle is therefore
*meant* to be unsatisfiable** -- it is the frozen contradiction of
`09:1306--1308`, not a statement about a reachable configuration.  The
non-vacuity question for it is whether each hypothesis is individually
attainable, and the margin is exactly one bit: the banked
`FirstWrapperAssembly.assembled_join_margin_is_one_bit` records that at every
tuple meeting `C >= 3`, `d + ell = r`, `ell >= 1` and the budget relation the
output `C + ell - 1` exceeds the budget by exactly one, so nothing weaker than
`hlower` would fire the contradiction and nothing stronger is needed.

General in the carriers, in `P`, `r`, `C`, the address and the bit. -/
theorem branchTwo_closure_contradicts_child_budget {P : Protocol X Y Z} {r C : ℕ}
    {p : List Bool} (h : IsFirstBobNode P r p) (hcost : P.cost ≤ C + r - 1)
    (hC : 3 ≤ C) (b : Bool)
    (hlower : C + (r - p.length) - 1 ≤ (descend P (p ++ [b])).cost) : False := by
  have hlt : p.length < r := h.2.2
  exact firstBob_budget_contradiction (C := C) (r := r) (d := p.length)
    (ℓ := r - p.length) (B := (descend P (p ++ [b])).cost) hC (by omega) (by omega)
    (firstBob_selected_child_budget h hcost b) hlower

end Budget

end BranchTwo

/-! ## §4  `L1-F4`: a joint-satisfiability witness at `d_v > 0`, with a real split

**NON-FIDELITY / BEYOND-PAPER.**  Everything in this section audits *our*
encoding at a point the frozen paper never visits, and it claims no legality:

* `k_ref = 4` meets every gate this module carries (`A:117--118`'s `16 | t_ref`),
  but `A:117` with `A:26` forces `t_ref >= t_cert = 2^{2^20}`, so the paper's own
  `k_ref` is astronomically larger.  This is the clause that makes the instance
  an audit rather than the paper's instance.
* the alphabet `Fin 32`, the column alphabet `Bool`, the Alice predicate, the Bob
  predicate, the leaf value, the coordinate count `18`, the wrapper exponent
  `r = 5` and the depth `b_T = 9` are **ours**; the frozen text fixes none of
  them, and `06:239--241` DEFINES `b_T`.

What is **not** ours, and is evaluated rather than assigned:

* `x_T = 2^{-b_T}` is the banked `xTdepth` (`08:166`) -- the paper's closed form,
  at our `b_T`;
* `m_G = |Fin 32|` is read at the carrier -- `09:113--116` defines
  `m_G = abs(Rows(G))` -- never as a numeral;
* `A_0 = ceil(2 x_T m_G)` is the banked `initialRefRows` (`09:1219`) evaluated at
  those values, and `splitAudit_A0_is_evaluated` proves the evaluation;
* the qualification threshold `ceil(A_{k}/2) = A_{k-1}` is the banked
  `childFloor` (`09:1242`), and the split decision is `splitsAt` computed from
  the rows, never asserted;
* the certificate kind `low` and its weight `1/2` are `kindAlong` and
  `CertKind.weight` (`09:1245--1247`), evaluated;
* `theta = rho = 18/25` is the banked `rhoSmall` (`09:436`);
* `kappa_v = 2^{r-d_v} = 16`, `r' = kappa_v/t_ref = 1` and `p_t = 9` are
  evaluations of the predecessor's Sections 1--2;
* `W_v = 9` is an evaluation of `frontierWeight`.

**What this instance adds over the predecessor's.**  The predecessor's audit sat
at a depth-`1` protocol with `d_v = 0`: no Alice query was routed, no certificate
split, and the weight bookkeeping of `09:1244--1248` was never exercised.  Here
the root **is** an Alice query, both children qualify at the frozen floor
`A_{r-1} = 16`, so `09:1244`'s "route it to both children if both qualify" fires;
every descendant is `low` with weight `1/2` (`09:1246`), and the node sits at
`d_v = 1` with `kappa_v = 16 = t_ref`, on branch (i)'s boundary.  `hA` is
**discharged through Section 1** rather than supplied, so the instance also
witnesses `L1-F1` at a node where the routing has actually done work.

Every clause is tight: `W_v = vartheta kappa_v = 9` exactly, `kappa_v = t_ref`
exactly, `k_ref = r - d_v` exactly, `kappa_v x_T m_G = 1` exactly, and the
retention `A_r = 2^5 A_0 = 32 = |X|` exactly. -/

section SplitAudit

/-- The audit transcript: an Alice query at the root whose two children are Bob
queries.  The first Alice answer is routed, the branch then stops at its first
Bob query (`09:1250`).  **Ours**, per the BEYOND-PAPER label. -/
def splitAudit : Protocol (Fin 32) Bool Bool :=
  Protocol.aNode (fun x => decide (16 ≤ x.val))
    (bobRootTranscript (fun y => y) true) (bobRootTranscript (fun y => y) true)

/-- The eighteen started outer coordinates and their reference rows.  Eighteen is
not free: it is the smallest count for which eighteen **low** certificates of
weight `1/2` each meet `09:1268`'s heavy threshold `vartheta kappa_v = 9` at
`kappa_v = 16`. -/
def splitAuditRows : Fin 18 → Finset (Fin 32) := fun _ => Finset.univ

/-- `x_T = 2^{-b_T}` (`08:166`) at our `b_T = 9`, through the banked `xTdepth`:
the paper's closed form, never a numeral shortcut of it. -/
noncomputable def splitAuditXT : ℝ := xTdepth 9

/-- `A_0 = ceil(2 x_T m_G)` (`09:1219`) through the banked `initialRefRows`, with
`m_G` read at the row carrier: the defining display is `09:113--116`,
`m_G = abs(Rows(G))`, and this instance's reference rows sit on `Fin 32`.  Its
value is computed, not assigned -- see `splitAudit_A0_is_evaluated`. -/
noncomputable def splitAuditA0 : ℕ :=
  initialRefRows splitAuditXT (Fintype.card (Fin 32))

/-- **`09:1219` EVALUATED at the audit values.**
`A_0 = ceil(2 . 2^{-9} . 32) = ceil(1/8) = 1`.  The numeral is an output of the
frozen display, not an input. -/
theorem splitAudit_A0_is_evaluated : splitAuditA0 = 1 := by
  have hcard : (Fintype.card (Fin 32) : ℕ) = 32 := by simp
  have h : (2 : ℝ) * splitAuditXT * ((Fintype.card (Fin 32) : ℕ) : ℝ) = 1 / 8 := by
    rw [hcard]
    norm_num [splitAuditXT, xTdepth]
  rw [splitAuditA0, initialRefRows, h, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- **`09:1233--1235` at the audit instance.**  Every started coordinate retains
all `A_r = 2^5 A_0 = 32` reference rows, so the frozen retention holds with
equality. -/
theorem splitAudit_hR (i : Fin 18) :
    refRowFloor splitAuditA0 5 ≤ (splitAuditRows i).card := by
  rw [splitAudit_A0_is_evaluated, refRowFloor]
  simp [splitAuditRows]

/-- **Aux (the root is an Alice query).**  The frozen routing rule of `09:1240`
therefore fires at the root, which is what the predecessor's instance could not
exercise. -/
theorem splitAudit_root_isANodeB : isANodeB splitAudit = true := rfl

/-- **Aux (the children are Bob queries).**  Each routed branch stops at depth
`1` by `09:1250`'s first stopping rule. -/
theorem splitAudit_child_not_isANodeB (b : Bool) :
    isANodeB (descend splitAudit [b]) = false := by
  cases b <;> rfl

/-- **`09:1240--1244` EVALUATED at the audit root: both children qualify.**

The frozen threshold at the root is `ceil(A_5/2) = A_4 = 2^4 A_0 = 16`
(`childFloor`, `09:1242`), and the Alice predicate splits the `32` reference rows
into two halves of `16`.  So `09:1244`'s "route it to both children if both
qualify" fires, and the certificate **splits** -- the event the predecessor's
instance never reached. -/
theorem splitAudit_splitsAt_root_univ :
    splitsAt splitAudit (Finset.univ : Finset (Fin 32)) 1 5 ([] : List Bool) = true := by
  decide

/-- **Aux (the split, read at the audit's own reference rows).**  The same fact
as `splitAudit_splitsAt_root_univ`, stated at `splitAuditRows i` so that the
routing recursion below rewrites with it directly. -/
theorem splitAudit_splitsAt_root (i : Fin 18) :
    splitsAt splitAudit (splitAuditRows i) 1 5 ([] : List Bool) = true :=
  splitAudit_splitsAt_root_univ

/-- **`09:1250--1252` EVALUATED at the audit instance.**  Every coordinate's
routed branch splits once and then stops at the two first-Bob addresses. -/
theorem splitAudit_coordRoutes (i : Fin 18) :
    coordRoutes splitAudit splitAuditRows splitAuditA0 5 i
      = {([false] : List Bool), ([true] : List Bool)} := by
  rw [splitAudit_A0_is_evaluated]
  have hdesc : descendants splitAudit (splitAuditRows i) 1 5 5 ([] : List Bool)
      = [([false] : List Bool), ([true] : List Bool)] := by
    rw [descendants_succ, if_pos ⟨splitAudit_root_isANodeB, by norm_num⟩,
      if_pos (splitAudit_splitsAt_root i)]
    have hf : descendants splitAudit (splitAuditRows i) 1 5 4
        (([] : List Bool) ++ [false]) = [([false] : List Bool)] := by
      refine descendants_of_stopped ?_
      rintro ⟨hcon, -⟩
      rw [List.nil_append, splitAudit_child_not_isANodeB] at hcon
      exact Bool.noConfusion hcon
    have ht : descendants splitAudit (splitAuditRows i) 1 5 4
        (([] : List Bool) ++ [true]) = [([true] : List Bool)] := by
      refine descendants_of_stopped ?_
      rintro ⟨hcon, -⟩
      rw [List.nil_append, splitAudit_child_not_isANodeB] at hcon
      exact Bool.noConfusion hcon
    rw [hf, ht]
    simp
  rw [coordRoutes, hdesc]
  simp

/-- **`09:1245--1247` EVALUATED at the audit instance.**  The certificate split
at the root, so every descendant is a **low** certificate; its weight is the
frozen `1/2`. -/
theorem splitAudit_kindAlong (i : Fin 18) (b : Bool) :
    kindAlong splitAudit (splitAuditRows i) splitAuditA0 5 [b] = CertKind.low := by
  have hsb : splitBefore splitAudit (splitAuditRows i) 1 5 [b] = true := by
    rw [show ([b] : List Bool) = [] ++ [b] by simp, splitBefore_append_bit]
    simp [splitAudit_splitsAt_root i]
  rw [splitAudit_A0_is_evaluated]
  simp [kindAlong, hsb]

/-- The audit frontier node: the `false` child of the root, an exposed first-Bob
address of depth `d_v = 1`. -/
def splitAuditNode : FrontierNode splitAudit splitAuditRows splitAuditA0 5 :=
  ⟨[false], mem_frontierRoutes_of_mem_coordRoutes (i := (0 : Fin 18))
    (by rw [splitAudit_coordRoutes]; simp)⟩

/-- **Aux (the audit node's address).**  `d_v = 1`: one Alice query was routed
before the branch stopped. -/
@[simp] theorem splitAudit_node_val : splitAuditNode.val = ([false] : List Bool) := rfl

/-- **`09:1255` EVALUATED at the audit node.**  `kappa_v = 2^{5-1} = 16`, which is
`t_ref` at `k_ref = 4` -- the boundary `09:1269` assigns to branch (i). -/
theorem splitAudit_kappa :
    kappaAt splitAudit splitAuditRows splitAuditA0 5 splitAuditNode = 16 := rfl

/-- **`09:1257` EVALUATED at the audit node.**  `W_v = 9`: eighteen **low**
certificates of the frozen weight `1/2` each.  This is the sum the predecessor's
`d_v = 0` instance could not exercise, because there every certificate was still
clean. -/
theorem splitAudit_frontierWeight :
    frontierWeight splitAudit splitAuditRows splitAuditA0 5 splitAuditNode = 9 := by
  classical
  rw [frontierWeight_eq_sum_reaching]
  have hterm : ∀ i : Fin 18,
      (if splitAuditNode.val ∈ coordRoutes splitAudit splitAuditRows splitAuditA0 5 i
        then (kindAlong splitAudit (splitAuditRows i) splitAuditA0 5
          splitAuditNode.val).weight else 0) = (1 / 2 : ℝ) := by
    intro i
    rw [if_pos (by rw [splitAudit_node_val, splitAudit_coordRoutes]; simp)]
    rw [splitAudit_node_val, splitAudit_kindAlong i false]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp [Finset.card_univ]
  norm_num

/-- **Aux (the audit node lies on every coordinate's route).**  Needed to feed
`L1-F1`: the row set the trim demand is discharged against is coordinate `i`'s
own certificate at this address. -/
theorem splitAudit_node_mem_coordRoutes (i : Fin 18) :
    splitAuditNode.val ∈ coordRoutes splitAudit splitAuditRows splitAuditA0 5 i := by
  rw [splitAudit_node_val, splitAudit_coordRoutes]
  simp

/-- **The heavy premise bundle of `09:1268--1296` is JOINTLY SATISFIABLE AT
`d_v > 0`, with a real certificate split.**

All the clauses of `exists_frontier_routedTriple_at_paper_schedule` hold at once,
each of them tight:

* `4 <= k_ref` and `k_ref <= r - d_v` hold with equality at `k_ref = 4`,
  `r - d_v = 5 - 1 = 4`; equivalently `t_ref = kappa_v = 16`;
* `hbob`: the node is a Bob query (the root's `false` child);
* `hheavy`: `vartheta kappa_v = (9/16) . 16 = 9 = W_v`, with equality, and `W_v`
  is a sum of **half**-weights because the certificates split;
* the row-density clause: `kappa_v x_T m_G = 16 . 2^{-9} . 32 = 1`, with
  equality.  Since `WDFW-F13` the headline's own binder there is only
  `hpos : 0 < kappa_v x_T m_G`, and this witness deliberately keeps the
  **retired** and strictly stronger `1 <= kappa_v x_T m_G`, weakening it at the
  call in `splitAudit_yields_paper_indexed_triple`: retiring a binder must not
  quietly weaken the evidence that the bundle is inhabited, so the clause stays
  at the form it was verified at;
* `hdens`: `theta = rho = 18/25` against the root child's retained density `1`.

`hA` does not appear: `L1-F1` discharges it from the routing.  **This does not
discharge the canonical-inhabitation obligation** -- see the BEYOND-PAPER label
above and the header. -/
theorem heavy_bundle_jointly_satisfiable_at_positive_depth :
    (4 : ℕ) ≤ 4 ∧ (4 : ℕ) ≤ 5 - splitAuditNode.val.length
      ∧ 1 ≤ splitAuditNode.val.length
      ∧ 0 < Fintype.card Bool
      ∧ IsBobNode (descend splitAudit splitAuditNode.val)
      ∧ vartheta * ((kappaAt splitAudit splitAuditRows splitAuditA0 5 splitAuditNode : ℕ) : ℝ)
          ≤ frontierWeight splitAudit splitAuditRows splitAuditA0 5 splitAuditNode
      ∧ 1 ≤ ((kappaAt splitAudit splitAuditRows splitAuditA0 5 splitAuditNode : ℕ) : ℝ)
          * splitAuditXT * ((Fintype.card (Fin 32) : ℕ) : ℝ)
      ∧ rhoSmall ≤ ((retainedCols splitAudit (Finset.univ : Finset Bool)
          splitAuditNode.val).card : ℝ) / (Fintype.card Bool : ℝ) := by
  have hcard : (Fintype.card (Fin 32) : ℕ) = 32 := by simp
  refine ⟨le_refl 4, by simp, by simp, by norm_num, trivial, ?_, ?_, ?_⟩
  · rw [splitAudit_kappa, splitAudit_frontierWeight, vartheta_val]; norm_num
  · rw [splitAudit_kappa, hcard]; norm_num [splitAuditXT, xTdepth]
  · have halice : IsAlicePath splitAudit ([false] : List Bool) := ⟨⟨_, _, _, rfl⟩, trivial⟩
    rw [splitAudit_node_val,
      retainedCols_of_isAlicePath (P := splitAudit) (S := (Finset.univ : Finset Bool))
        (p := [false]) halice]
    norm_num [rhoSmall]

/-- **`L1-F1` and `L1-F4` together: the audit instance produces an actual routed
triple at the paper's index tuple, at `d_v > 0`, with `hA` discharged.**

The Section 1 headline fired at the satisfiable bundle: a genuine `(S,T,K)` with
`S` inside the node's own census, `T` inside the **certificate's own rows** at
that address (not a free `Finset`), and the triple indexed by
`r' = kappa_v/t_ref = 1`, `t = t_ref = 16`, `a^sharp = 1`.

**NON-FIDELITY**, per the BEYOND-PAPER label: it audits our encoding, and does
not exhibit the paper's object. -/
theorem splitAudit_yields_paper_indexed_triple :
    ∃ (S : Finset (Fin 18)) (T : Finset (Fin 32)) (b : Bool),
      S ⊆ representedCoords splitAudit splitAuditRows splitAuditA0 5 splitAuditNode
        ∧ T ⊆ rowsAt splitAudit (splitAuditRows 0) splitAuditNode.val
        ∧ RoutedTriple (Blk := Fin 18) (Row := Fin 32) (Col := Bool)
            (frontierCopies 5 splitAuditNode.val.length 4) (tRef 4) 1 splitAuditXT
            rhoSmall S T
            (retainedCols splitAudit (Finset.univ : Finset Bool)
              (splitAuditNode.val ++ [b])) := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ :=
    heavy_bundle_jointly_satisfiable_at_positive_depth
  exact exists_frontier_routedTriple_at_paper_schedule splitAudit splitAuditRows 5 0
    (splitAudit_hR 0) splitAuditNode (splitAudit_node_mem_coordRoutes 0) Finset.univ
    h1 h2 h4 h5 h6 (lt_of_lt_of_le zero_lt_one h7) h8

end SplitAudit

/-! ## §6  Aux battery

Five general properties of the objects this tranche introduces or re-reads.  A
green build sees none of them. -/

section Aux

/-- **Aux 1 (the branch-(ii) trim target is monotone in the capacity).**  A node
one Alice query higher trims to a larger row set, which is the direction
`09:1291--1296` is used in.  General. -/
theorem branchTwo_trimTarget_mono {κ κ' m : ℕ} {x : ℝ} (hx : 0 ≤ x) (h : κ ≤ κ') :
    ⌈((κ : ℕ) : ℝ) * x * ((m : ℕ) : ℝ)⌉₊ ≤ ⌈((κ' : ℕ) : ℝ) * x * ((m : ℕ) : ℝ)⌉₊ := by
  refine Nat.ceil_le_ceil ?_
  have hκ : ((κ : ℕ) : ℝ) ≤ ((κ' : ℕ) : ℝ) := by exact_mod_cast h
  have hm : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hx) hm

/-- **Aux 2 (the branch-(ii) trim target is positive exactly in the frozen
regime).**  `hone` and a nonempty trim are the same condition up to the ceiling.
General. -/
theorem branchTwo_trimTarget_pos {κ m : ℕ} {x : ℝ}
    (h : 1 ≤ ((κ : ℕ) : ℝ) * x * ((m : ℕ) : ℝ)) :
    0 < ⌈((κ : ℕ) : ℝ) * x * ((m : ℕ) : ℝ)⌉₊ :=
  Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one h)

/-- **Aux 3 (`09:1283`'s middle term at the frozen dyadic capacities).**  The
cover entry `u_{kappa}` never exceeds `ceil(9 kappa/16)` at any capacity the
frontier can produce, i.e. at every `kappa = 2^ell` with `ell >= 1` (`09:1259`).
This is the general form of `branchTwo_census_chain`'s first link, stated free of
any routed system.  General. -/
theorem smallCopyWidth_le_ceil_ninesixteenths {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    smallCopyWidth (2 ^ ℓ) ≤ ⌈9 * ((2 : ℝ) ^ ℓ) / 16⌉₊ := by
  refine smallCopyWidth_le_ceil_weight hℓ ?_
  rw [vartheta_val]
  linarith [pow_pos (by norm_num : (0 : ℝ) < 2) ℓ]

/-- **Aux 4 (`A:141` at `a^sharp = 1` is a halving, in general).**  The frozen
difference between the two certified calls -- `09:322`'s `a^sharp = 0` and
`09:1273`'s `a^sharp = 1` -- is exactly one factor of two on the column side.
General in `h`; `denserChild_colFloor_eq_y_sq` is the substitution `h = rho`. -/
theorem certifiedColFloor_one_eq_half (h : ℝ) :
    RestrictionDatum.certifiedColFloor h 1 = h / 2 := by
  rw [RestrictionDatum.certifiedColFloor]
  norm_num

/-- **Aux 5 (the child budget is monotone in the depth).**  A first-Bob node one
Alice query deeper leaves its selected child strictly fewer bits, which is why
`09:1306--1308`'s margin closes at every depth rather than only at the root.
General. -/
theorem child_budget_antitone {C r d d' B : ℕ} (h : d ≤ d')
    (hbudget : B + (d' + 1) ≤ C + r - 1) : B + (d + 1) ≤ C + r - 1 := by omega

end Aux

/-! ### Non-vacuity witnesses for the two `L1-F2`/branch-(ii) statements

`exists_frontier_routedTriple_at_paper_schedule` has its witness in §4.  The two
statements below supply the same service for the remaining new bundles. -/

section NonVacuity

/-- **Non-vacuity of the positive-regime trim, and the `hone` clause's failure.**

At `x_T = xTdepth b_T` with `b_T = 10`, `r' = 1`, `t = t_ref = 16` and the row
carrier `Fin 32`, the clause `hone` **fails** (`1 . 16 . 2^{-10} . 32 = 1/2`),
while the row supply `hA` holds and the trim is still produced, of card
`ceil(1/2) = 1` and nonempty.  All three conjuncts are proved below.

**`L1-F9`'s rename half, DISCHARGED here (tranche `cc-t5i`).**  The banked name
was `positive_regime_trim_is_strictly_stronger`.  When it was chosen, the
pre-retirement `WrapperDenseFrontierWiring.exists_trimmed_reference_rows`
demanded `hone` and so was genuinely unavailable at this point, which did make
the statement below a strict strengthening of it.  After `L1-F6` (tranche
`cc-t5h`) that is **no longer true**: the banked lemma asks only
`hpos : r' t x m > 0`, and here `z = 1/2 > 0`, so it fires at exactly this point
too.  By `WrapperDenseFrontierWiring.trim_positivity_iff_factors_positive` the
two are now **logically equivalent**, and a name claiming a strict strengthening
asserted something false about the interface.  The name below says instead what
the three conjuncts do assert -- at this point `hone` fails, `hA` holds, and the
positive-regime trim is still delivered -- and the old name is **not** kept as an
alias.  **No statement byte moves:** the three conjuncts were true exactly as
stated then and are unchanged now; what was stale was the name and the
commentary, never the mathematics.

**`L1-F9`'s deduplication half, DISCHARGED here too (same tranche).**  This is
the one proof in `src/` that consumed the deleted
`exists_trimmed_reference_rows_in_the_positive_regime`, and the census that
preceded the deletion found no other.  It fires the banked
`WrapperDenseFrontierWiring.exists_trimmed_reference_rows` **directly**: the four
unbundled positivity facts become that lemma's single `hpos` inline, through the
banked `trim_positivity_iff_factors_positive.mpr`, so the deleted statement is
not reintroduced under any name and this module pins the bank rather than a copy
of it.  **The three conjuncts below are byte-identical** across the rewiring:
only the proof term moved, from a duplicate of the banked lemma to the banked
lemma itself.  Together with `hone_can_fail_at_legal_positive_xT` this is the
whole of `L1-F2`'s finding, and `L1-F2` is what motivated `L1-F6`.

**BEYOND-PAPER.**  `b_T = 10`, `k_ref = 4` and the carrier are ours; `b_T` is
DEFINED by `06:239--241` and `A:117` with `A:26` forces `t_ref >= 2^{2^20}`.  No
legality is claimed. -/
theorem positive_regime_trim_holds_where_hone_fails :
    ¬ (1 ≤ (((1 * tRef 4 : ℕ) : ℕ) : ℝ) * xTdepth 10
          * ((Fintype.card (Fin 32) : ℕ) : ℝ))
      ∧ 2 * ((((1 * tRef 4 : ℕ) : ℕ) : ℝ) * xTdepth 10
          * ((Fintype.card (Fin 32) : ℕ) : ℝ))
          ≤ (((Finset.univ : Finset (Fin 32))).card : ℝ)
      ∧ ∃ T ⊆ (Finset.univ : Finset (Fin 32)),
          T.card = RestrictionDatum.certifiedRowFloor 1 (tRef 4) (xTdepth 10)
              (Fintype.card (Fin 32))
            ∧ T.Nonempty := by
  have hcard : (Fintype.card (Fin 32) : ℕ) = 32 := by simp
  have hfail : ¬ (1 ≤ (((1 * tRef 4 : ℕ) : ℕ) : ℝ) * xTdepth 10
      * ((Fintype.card (Fin 32) : ℕ) : ℝ)) := by
    rw [hcard]
    norm_num [tRef, xTdepth]
  have hA : 2 * ((((1 * tRef 4 : ℕ) : ℕ) : ℝ) * xTdepth 10
      * ((Fintype.card (Fin 32) : ℕ) : ℝ))
      ≤ (((Finset.univ : Finset (Fin 32))).card : ℝ) := by
    rw [hcard]
    simp only [Finset.card_univ, Fintype.card_fin]
    norm_num [tRef, xTdepth]
  refine ⟨hfail, hA, ?_⟩
  exact exists_trimmed_reference_rows (r' := 1) (t := tRef 4)
    (m := Fintype.card (Fin 32)) (x := xTdepth 10) (A := (Finset.univ : Finset (Fin 32)))
    (trim_positivity_iff_factors_positive.mpr
      ⟨by norm_num, by norm_num [tRef], by rw [hcard]; norm_num, xTdepth_pos 10⟩) hA

/-- **Hypothesis consistency for the legality chain (BEYOND-PAPER AUDIT).**

`branchTwo_row_density_legality` carries four binders, and two of them pull in
opposite directions: the gate `2^r x_T <= 4/25025` of `eq:wrapper-low-simple-gate`
wants `x_T` small, while `hbranch` wants the capacity below `t_ref`.  They are
jointly satisfiable, and the instance takes `x_T` from the banked **closed-form**
accessor `WrapperLowRungs.wrapperLowRungGates_legal_instance` at `(k, r) = (4, 6)`
rather than as a numeral: at `d_v = 2` the capacity is
`kappa_v = 2^{6-2} = 16 = t_ref`, so `hbranch` holds with equality on the
boundary `09:1269` assigns to branch (i), and the gate holds with room to spare.

**BEYOND-PAPER.**  `r = 6`, `k_ref = 4`, `d_v = 2` and the resulting
`x_T = 2^{-22}` are **ours** -- `06:515` DEFINES `r`, `06:558--569` DEFINES
`k_ref`, `06:243` DEFINES `x_T` -- and no legality is claimed for them.  The
accessor is a paper expression evaluated at BEYOND-PAPER arguments, which is why
the value is disclosed here rather than hidden inside the accessor. -/
theorem branchTwo_legality_binders_consistent :
    (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ kappaFrontier 6 2 ≤ tRef 4
      ∧ (4 : ℕ) + 2 ≤ 6
      ∧ ((2 : ℝ) ^ (6 : ℕ)) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025
      ∧ ((tRef 4 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 1 := by
  obtain ⟨-, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  refine ⟨le_of_lt hpos, by norm_num [kappaFrontier, stoppingCapacity, tRef],
    by norm_num, ?_, ?_⟩
  · rw [hval]; norm_num
  · exact (branchTwo_row_density_legality (r := 6) (d := 2) (kref := 4) (le_of_lt hpos)
      (by norm_num [kappaFrontier, stoppingCapacity, tRef]) (by norm_num)
      (by rw [hval]; norm_num)).2

end NonVacuity

end EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors
