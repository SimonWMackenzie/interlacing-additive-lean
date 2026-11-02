import EthInapproximability.ParameterizedNP.MassRedistributionOwners

/-!
# Parameterized NP route: the OWNER-TRANSFER FAMILY on the CONSTRUCTION PATH

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche), **lines `09:1617--1702`**.  Every
  anchor named below was opened first-hand in that file for this tranche.

  The frozen block this module carries onto the construction path, in print
  order:

  1. `09:1617--1625`, the owner-threshold display -- "For `i in J_good`, let
     `eps_i` be the fraction of its ordinary baseline missing at `own(i)`, and
     set `lambda_0 = q_2 2^{1-b_1}`, `delta_i = lambda_0 + 5 eps_i + 2/q_2`"
     (`eq:wrapper-owner-threshold`, label `09:1624`);
  2. `eq:wrapper-baseline-deficit-sum` (display `09:1627--1631`, label
     `09:1630`) with its frozen justification `09:1632--1642`;
  3. `09:1643--1646`, the transfer trigger -- "If a different donor `j` sent
     protected mass at least `2 mu_P delta_i` to `own(i)`, one of the two
     reservoir types would arrive there at relative density at least `delta_i`.
     Such a transfer is possible only when `delta_i <= 1`";
  4. `09:1648--1679`, the per-owner realization paragraph, whose `09:1661--1669`
     call to `lem:terminal-state-realization` is made **"with the completed
     protocol `P`"** (`09:1664`), and whose conclusion `09:1676--1679` is that
     "every such transfer is strictly below `2 mu_P delta_i`";
  5. `eq:wrapper-owner-gates` (display `09:1682--1689`, label `09:1688`);
  6. `eq:wrapper-good-to-good` (display `09:1692--1699`, label `09:1698`), the
     constant `3 eta_R/16` and its strict gap to `eta_R/4`;
  7. `09:1700--1701`, "Together with `eq:wrapper-mass-leaves-owner`, this says
     that every good donor sends more than `eta_R/4` protected mass to
     exceptional final nodes", and `09:1702`, "If `e_T = 0`, this is already a
     contradiction".

* **The construction chain this module fires them at** -- the second frozen
  strand, opened first-hand for this tranche:
  * `09:1187--1193`, the contradiction frame: "Fix an arbitrary retained matrix
    `U'` in `[U]_{1,1-delta_U,theta}` and suppose for contradiction that a
    protocol `P` of cost at most `C+r-1` computes `U'`."  The protocol is
    **arbitrary**; nothing about completion is supposed;
  * `09:1195--1215`, `lem:wrapper-no-bob-completion` and the substitution step
    `09:1215`, banked as `RoutedCertificateConstruction.completeNoBob`,
    `completedNoBob_completeNoBob`, `completeNoBob_cost_le_frame` (the `C >= 1`
    cost clause, `09:1207--1212`), `completeNoBob_computes` (the
    "they do not change ... the computed matrix" clause, `09:1205--1206`) and
    `completedSystem`;
  * `09:105`, "Let `q = 2^r` be the scale-alignment width", which fixes the
    coordinate carrier both strands read.

* **Cross-anchors opened first-hand for this tranche:** `09:1566--1568` (the
  `m_{j,T}`/`own(i)` conventions), `09:1569--1584` (the four-category table),
  `09:1600--1615` (the retention/hardness step and
  `eq:wrapper-mass-leaves-owner`), `09:1550` (the owner definition and
  uniqueness sentence, "Every clean reference certificate has a unique final
  node, its *owner*"; the routed **stopping rule** is `09:1250`, quoted below),
  `09:1553` (the exceptional classification), `09:1704` ("Assume then that
  `e_T > 0`"), `09:1250` ("Stop each routed branch at its first Bob query, or
  after `r` Alice queries"), `09:1264` (`sum_v kappa_v <= q`),
  `09:1233--1236` (the retention and "Start one clean reference certificate in
  every coordinate outside `E_0`") and `09:447--450` (the **definition** of
  `E_0` as the union of the singleton, pair and small-copy covers, with
  `e_0 = |E_0|`).  From `06-parameter-schedule.tex` (SHA-256
  `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
  recomputed first-hand for this tranche): `06:122--125`, the **defining
  display of `q_2`** ("The source theorem then fixes `q_2 = the least power of
  two at least 12 s N_E`"), and `06:312--320`, `eq:stage1-scales`, the
  **defining display of `b_1`** (`06:317`, "`b_1 = 2^{j_49(a-2)}`"; the
  following sentence at `06:321` reads "All these quantities are integers;
  `t_1` and `b_1` are powers of two" -- `06:319--320` are the display's own
  `\label` and `\end{equation}` and carry no such text).  Both are read in
  Section 5 below, and the reason they are read is recorded there.

* **Reader counterpart: NONE claimable.**  `routes/parameterized-np/reader-facing/`
  `sections/` was searched first-hand for this tranche.  The only passages
  covering this material are running prose in the proof of
  `thm:paper-adapted-stage4-interface`: `A-stage4-details.tex:376` ("restriction
  or one terminal owner receives enough protected mass from a ...") and
  `A-stage4-details.tex:396` ("The complete owner--donor count is finite: it uses
  only the fixed reservoir ...").  Neither is a numbered item, and the
  READER-COUNTERPART rule forbids citing prose and forbids reusing another
  declaration's item.  `WRAPPER-LOSS-TABLE-001`, `USET-SELECTION-001` and
  `MASS-REDISTRIBUTION-OWNERS-001` recorded the same absence; it is inherited,
  not newly asserted.  The route-level crosswalk row for
  `thm:first-wrapper` (`READER_CROSSWALK.md`, the "Scale-aligned adapted
  Stage 4" row) records this module in the same change, which is what entry
  requirement 8 asks for; that row is a route-level statement crosswalk and is
  **not** a per-declaration reader counterpart.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively, by the single import.
* **Proof status:** new wiring; no mathematics is added.

## What this tranche lands, and what it deliberately is not

`MASS-REDISTRIBUTION-OWNERS-001` carried the owners and loss-table layer of
`09:1535--1615` onto the construction path and named, as its **GAP-EXPOSED item
1**, that

> `09:1617--1699` (the owner-to-owner transfer family and
> `eq:wrapper-good-to-good`) is NOT travelled on the construction path ... so the
> vanishing-case section takes the `09:1700--1701` endpoint as the explicit
> binder `hexc`.

**This module travels it at ONE width, and `hexc` is discharged.**  Every
declaration of Sections 1--4 is stated at
`RoutedCertificateConstruction.completedSystem P hR` for an **arbitrary**
alleged protocol `P` of `09:1192--1193`, with

* `hcomp : CompletedNoBob` discharged by `completedNoBob_completeNoBob`, inside
  `completedSystem`;
* the completed protocol's cost bound derived from the *original* protocol's
  `09:1192` bound by `completeNoBob_cost_le_frame` -- which is exactly the
  frozen `09:1664` reading, "with the completed protocol `P`", made honest: the
  realization paragraph is entitled to a completed protocol only because
  `09:1207--1212` produced one from the arbitrary one;
* the completed protocol's `Computes` obligation derived from the original's by
  `completeNoBob_computes`;
* and, in Section 4, `hexc` -- the `09:1700--1701` endpoint -- **produced**
  rather than assumed, which is what closes the predecessor's GAP item 1.

### ONE WIDTH: what "travelled" means here, precisely

The frozen text uses a single exponent `r`.  `09:105` sets the
scale-alignment width `q = 2^r`; `09:1192` bounds the alleged protocol by
`C + r - 1`; `09:1250` stops each routed branch "after `r` Alice queries"; and
`09:1264` bounds the frontier by that same `q`.  Sections 1--4 therefore carry
**one** natural-number binder `r`:

* the coordinate carrier is `Slot (scaleAlignWidth r)`, i.e. `q = 2^r`;
* the routed system is `completedSystem P hR`, whose Alice budget is that same
  `r` by construction;
* the width in `eq:wrapper-owner-gates` and in the good-donor count is
  `scaleAlignWidth r`, not a free `qw`.

Accordingly the endpoints consumed are the banked
`OwnerIndexedTransferFamily.goodToGood_engine_of_realization` and
`goodDonor_mass_to_exceptional_of_realization`, whose own readout
`identified_width_is_nondegenerate` records that they "take all three at one
`rq`".  The weaker `*_derived` endpoints -- which carry three independent
naturals (`rq`, the system budget `rw'`, and `qw`) *and* take the per-owner
two-stream state as the premise `hstateOf` -- are **not** consumed anywhere in
this module.

The practical consequence is what makes `09:1617--1699` *travelled* rather than
merely *stated*: with `hstateOf` gone, the frozen realization call of
`09:1661--1669` (`lem:terminal-state-realization`, "with the completed protocol
`P`") is performed **inside** the proof term at every good owner, from the
realization data, rather than being assumed as a produced state.

### What is still a binder, and what is still GAP-EXPOSED

*Still a binder, inherited verbatim from the banked endpoints:* the terminal
lemma family `hTTS` (`lem:terminal-two-stream`, a cited interface), the seed
certificates `hseed`, the fixed-width and Extension-call data `hfixed`/`hcalls`,
the reservoir split `hsplit`, the owner uniqueness `huniq` of `09:1550--1552`,
the schedule gates `hgates`, the width bound `hcard`, the deficit sum `hdeficit`
of `eq:wrapper-baseline-deficit-sum`, the template/regularity/selector data of
`09:1648--1660`, and the potential `Pv`.  **No hypothesis is added to either
banked endpoint and none is weakened; full-bundle satisfiability is not
claimed.**

*Still GAP-EXPOSED after this module:*

1. `Pv` and the two protected reservoirs (`09:1367--1384`, `09:1418--1531`) are
   still binders;
2. the coordinate restriction of `09:1233--1236` against the definition of `E_0`
   at `09:447--450` is still not performed (the predecessor's item 4: the
   retention seam is index-typed -- `RetentionSupply.retentionSupply` produces
   `hR` over `Fin (2^r)` while the canonical firings are stated over
   `StartedCoord E_0`).  It was offered in the parked generation of this module
   as a substitute for the primary target; the primary target is now performed,
   so the substitute is **not** performed and stays the predecessor's open item;
3. `09:1704--1781` -- the pigeonhole branch, `eq:wrapper-terminal-density`, the
   projection cover, the coordinate extraction, the block supply and the final
   Extension call -- is untouched.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:262--263`,
`09:1780--1781`) is neither stated nor implied.

**Canonical inhabitation: INHERITED, REGISTERED and DEFERRED.**  This module
declares no new type, so it opens no new canonical-inhabitation obligation.  The
inherited one cannot be discharged here, because the paper's own instance of
every statement below is a function of the alleged shallow protocol of
`09:1187--1193`, whose non-existence is the conclusion of the subsection: the
frozen paper exhibits no routed instance by construction.  Section 5's poles are
explicitly **NON-FIDELITY** on that axis -- they are satisfiability statements
about the arithmetic seam, at values of their own, and none is offered as the
paper's instance.  **Full-bundle satisfiability is not claimed.**

## Census of the banked modules this one sits on

Everything consumed is consumed **by pin**; nothing is restated.

* `OwnerIndexedTransferFamily` **owns** `09:1617--1699`: `ownerStateOf`,
  `ownerTransfer_lt_of_realization`, `ownerTransfer_family_of_realization`,
  `goodToGood_engine_of_realization`,
  `goodDonor_mass_to_exceptional_of_realization`, and the weaker `*_derived`
  pair.  **Consumed here:** the two `*_of_realization` endpoints (Sections
  1--2) and nothing else; the `*_derived` pair is consumed nowhere.
* `OwnerMassTransfer` **owns** `ownerLeakage`, `goodOwnerMass`,
  `exceptionalMass`, `ownerLeakage_split`, `exceptionalMass_of_empty` and
  `goodDonor_to_exceptional_engine`.
  **Consumed here:** the three readouts and the split (Section 5), and
  `exceptionalMass_of_empty` at Pole 1 (Section 5), which is disclosed at that
  pole itself.
* `OwnerFamilyToPigeonhole` **owns** `09:1704`'s branch as a conclusion.
  **Consumed here:** `exceptionalCount_pos_of_goodDonor` (Section 4).
* `WrapperLossTable` **owns** `09:1702` in both frozen forms over a routed
  system.  **Consumed here** only through the construction-path wrappers below.
* `MassRedistributionOwners` **owns** the construction-path owners layer: the
  frozen `LossTable` display, `constructionPath_ownerLeakage_gt`,
  `constructionPath_eT_zero_is_contradictory`,
  `constructionPath_not_finalNodes_subset_goodOwners` and the probe accessor
  `probe_at_schedule_etaR`.  **Consumed here:** all five (Sections 3--5).
* `RoutedCertificateConstruction` **owns** the completion operator and
  `completedSystem`.  **Consumed here:** `completeNoBob_cost_le_frame` and
  `completeNoBob_computes`, the two transports.
* `WrapperMassRedistribution` **owns** the pure arithmetic of `09:1526--1781`.
  **Consumed here DIRECTLY**, not merely transitively: `wrapperOwnerGates`
  (`eq:wrapper-owner-gates`) is named in the hypothesis bundle of every
  declaration of Sections 1--4, and Section 5 names `ownerGates_nonvacuous`,
  `muP_le_g_div_twenty` and `muP`.
* `ParameterSchedule` **owns** `etaR` (`eq:eta-choice`), `etaR_pos`,
  `etaR_le_bound` and the least-power-of-two accessors `leastPowTwoExp` /
  `le_two_pow_leastPowTwoExp` (`06:1253--1268`).  **Consumed here DIRECTLY:**
  all five, in Section 5's two bundle audits.
* `StageTwoRelaxed` **owns** `StageTwoWidths` and its accessors `q₂ = 2^{r_2}`,
  `b₁` (`07:278--281`, `07:398--401`).  **Consumed here DIRECTLY:** the
  structure itself carries `q_2` and `b_1` in every statement of Sections 1--4,
  and Section 5's Pole 7 builds one.
* `DenseBranchSelection` **owns** `lambdaZero` (`eq:wrapper-owner-threshold`'s
  `lambda_0 = q_2 2^{1-b_1}`, `09:1621`).  **Consumed here DIRECTLY** in Poles 5
  and 7.
-/

namespace EthInapproximability.ParameterizedNP.OwnerTransferFamily

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.TwoStreamState
open EthInapproximability.ParameterizedNP.TerminalStateRealization
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.MassLeavesOwner
open EthInapproximability.ParameterizedNP.OwnerMassTransfer
open EthInapproximability.ParameterizedNP.OwnerIndexedTransferFamily
open EthInapproximability.ParameterizedNP.OwnerFamilyToPigeonhole
open EthInapproximability.ParameterizedNP.MassRedistributionOwners

/-! ## §1  `eq:wrapper-good-to-good` (`09:1617--1699`) on the CONSTRUCTION PATH

The owner-to-owner transfer family fired at the routed system the construction
chain builds from an **arbitrary** alleged protocol, at the single frozen width
`r` of `09:105`/`09:1192`/`09:1250`/`09:1264`.  Three obligations of the banked
endpoint are discharged here that no banked module could discharge: `hcomp` (by
`completedSystem` itself), the completed protocol's cost bound (from `09:1192`'s
bound on the original, by `completeNoBob_cost_le_frame`), and the completed
protocol's `Computes` obligation (from `09:1205--1206`, by
`completeNoBob_computes`).

`09:1664` says the realization call is made "with the completed protocol `P`";
this section is what makes that phrase legitimate over the frame of
`09:1187--1193`, where the supposed protocol is arbitrary. -/

section TransferFamilyOnPath

variable {X Y : Type*} [Fintype X] [DecidableEq X]
variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
  [Fintype Rone] [DecidableEq Rone]

/-- **`eq:wrapper-good-to-good` (`09:1690--1699`) on the construction path, at
ONE width.**

"Using `eq:wrapper-baseline-deficit-sum`, each good donor therefore sends to all
other good owners total mass less than `2 mu_P (q lambda_0 + 5 eta_R/(8g) +
2q/q_2) <= 3 eta_R/16 < eta_R/4`."

The banked `OwnerIndexedTransferFamily.goodToGood_engine_of_realization` states
this at a routed system whose protocol is already assumed completed, over the
single width `q = 2^r`.  Here the system is `completedSystem P hR`: `P` is the
arbitrary alleged protocol of `09:1192--1193`, `hcost` is the **original**
protocol's `09:1192` cost bound, and `halleged` is the **original** protocol's
computation of the retained matrix `U'`.  No caller has to know that a
completion happened.

*What is derived rather than assumed.*  `hcomp`, the completed cost bound, the
completed `Computes` obligation; and, inside the banked endpoint, the owner
definition and uniqueness of `09:1550--1552` (the routed **stopping rule** is
`09:1250`), the per-owner realization call of `09:1661--1669`
(so no `hstateOf` premise survives), and the whole transfer family
`09:1677--1679`.

*What is still a binder.*  The terminal lemma family `hTTS`, the seed and
Extension-call data, the template/regularity/selector data of `09:1648--1660`,
`huniq`, `hgates`, `hcard`, `hdeficit` and `hsplit` -- all inherited
**verbatim** from the banked endpoint.  **No hypothesis is added and none is
weakened; full-bundle satisfiability is not claimed.**

*Why the trivial witness fails.*  The conclusion is a conjunction of two
inequalities between fixed reals, not an existential; and its second clause
`3 eta_R/16 < eta_R/4` is false at `eta_R = 0`, so the tolerance hypothesis is
load-bearing and the statement is not an arithmetic tautology.

General in all six carriers, in both protocol carriers, and in every width. -/
theorem constructionPath_goodToGood
    (W : StageTwoRelaxed.StageTwoWidths)
    (r s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth r) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth r) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ) (pOrd pFor : Slot s)
    (P : Protocol X Y Bool) {R : Slot (scaleAlignWidth r) → Finset X} {A0 : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pstar : CertIndex (completeNoBob r P) R A0 r → Finset (Cl × Cl))
    (Rbin : CertIndex (completeNoBob r P) R A0 r → Slot s → Finset Ltwo)
    (selRow : CertIndex (completeNoBob r P) R A0 r → Slot s × Ltwo →
      (Slot (scaleAlignWidth r) → Cl))
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR g : ℝ} {j : CertIndex (completeNoBob r P) R A0 r}
    (huniq : ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors (completedSystem P hR) Pv etaR)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth r) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ≤ ((scaleAlignWidth r : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors (completedSystem P hR) Pv etaR,
        ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      donorCoord (completedSystem P hR) i ≠ donorCoord (completedSystem P hR) j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      (streamRows XZ (donorCoord (completedSystem P hR) i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ, w (donorCoord (completedSystem P hR) i) = yp.1
        ∧ w (donorCoord (completedSystem P hR) j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (donorCoord (completedSystem P hR) i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (donorCoord (completedSystem P hR) i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (donorCoord (completedSystem P hR) i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth r) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + r - 1)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (iotaA : CertIndex (completeNoBob r P) R A0 r → {a // a ∈ XZ} → X)
    (iotaB : CertIndex (completeNoBob r P) R A0 r → {b // b ∈ YZ} → Y)
    (hrow : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a, RouteRows (completeNoBob r P)
        ((completedSystem P hR).node ((completedSystem P hR).owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat r) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
          ≤ Pv ((completedSystem P hR).owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        ≤ muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RD).card : ℝ)
              / (RD.card : ℝ))) :
    goodOwnerMass (completedSystem P hR) Pv etaR j ≤ 3 * etaR / 16
      ∧ 3 * etaR / 16 < etaR / 4 :=
  goodToGood_engine_of_realization W r s mT dT dOrd bcap r₃ bT Lh vmax Nmat Mmat cFam
    Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd pFor Pstar Rbin
    selRow (completedSystem P hR) Pv huniq hj hetaR hg hgates hcard hdeficit hOuter
    hbins htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd hRegF
    hdF hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist
    hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls hC
    (completeNoBob_cost_le_frame (le_trans (by norm_num) hC) hcost)
    (completeNoBob_computes halleged r) iotaA iotaB hrow hgame hsplit

/-! ## §2  `09:1700--1701` on the construction path, with `hleaves` still frozen

The endpoint the predecessor's vanishing case took as the binder `hexc`, now
proved at the walked system of an arbitrary alleged protocol -- but still with
`eq:wrapper-mass-leaves-owner` as its own binder `hleaves`, exactly as the
banked endpoint carries it.  Section 3 fills that slot from the frozen table. -/

/-- **`09:1700--1701` on the construction path, at ONE width.**

"Together with `eq:wrapper-mass-leaves-owner`, this says that every good donor
sends more than `eta_R/4` protected mass to exceptional final nodes."

The banked `OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization`
fired at `completedSystem P hR`, with the same three discharges as Section 1 and
the same single width.

*What is still a binder.*  Section 1's binders inherited verbatim, plus
`hleaves` -- `eq:wrapper-mass-leaves-owner` (`09:1611--1615`) itself, which
Section 3 discharges from the frozen four-category table.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
fixed reals, not an existential, and it is not vacuous: `exceptionalMass` is a
sum over the derived exceptional set of `09:1553`, which the banked
`OwnerMassTransfer.exceptionalMass_of_empty` evaluates to `0` when that set is
empty -- so at a positive `eta_R` the conclusion already forces `e_T > 0`, which
is what Section 4 extracts.  Section 5's `endpoint_fails_at_empty_exceptional`
records that pole.

General in all six carriers, in both protocol carriers, and in every width. -/
theorem constructionPath_goodDonor_mass_to_exceptional
    (W : StageTwoRelaxed.StageTwoWidths)
    (r s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth r) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth r) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ) (pOrd pFor : Slot s)
    (P : Protocol X Y Bool) {R : Slot (scaleAlignWidth r) → Finset X} {A0 : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pstar : CertIndex (completeNoBob r P) R A0 r → Finset (Cl × Cl))
    (Rbin : CertIndex (completeNoBob r P) R A0 r → Slot s → Finset Ltwo)
    (selRow : CertIndex (completeNoBob r P) R A0 r → Slot s × Ltwo →
      (Slot (scaleAlignWidth r) → Cl))
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR g : ℝ} {j : CertIndex (completeNoBob r P) R A0 r}
    (huniq : ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors (completedSystem P hR) Pv etaR)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth r) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ≤ ((scaleAlignWidth r : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors (completedSystem P hR) Pv etaR,
        ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      donorCoord (completedSystem P hR) i ≠ donorCoord (completedSystem P hR) j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      (streamRows XZ (donorCoord (completedSystem P hR) i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ, w (donorCoord (completedSystem P hR) i) = yp.1
        ∧ w (donorCoord (completedSystem P hR) j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (donorCoord (completedSystem P hR) i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (donorCoord (completedSystem P hR) i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (donorCoord (completedSystem P hR) i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth r) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + r - 1)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (iotaA : CertIndex (completeNoBob r P) R A0 r → {a // a ∈ XZ} → X)
    (iotaB : CertIndex (completeNoBob r P) R A0 r → {b // b ∈ YZ} → Y)
    (hrow : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a, RouteRows (completeNoBob r P)
        ((completedSystem P hR).node ((completedSystem P hR).owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat r) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
          ≤ Pv ((completedSystem P hR).owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        ≤ muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RD).card : ℝ)
              / (RD.card : ℝ)))
    (hleaves : etaR / 2 < ownerLeakage (completedSystem P hR) Pv j) :
    etaR / 4 < exceptionalMass (completedSystem P hR) Pv etaR j :=
  goodDonor_mass_to_exceptional_of_realization W r s mT dT dOrd bcap r₃ bT Lh vmax Nmat
    Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd pFor
    Pstar Rbin selRow (completedSystem P hR) Pv huniq hj hetaR hg hgates hcard hdeficit
    hOuter hbins htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd
    hRegF hdF hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped
    hSelDist hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls hC
    (completeNoBob_cost_le_frame (le_trans (by norm_num) hC) hcost)
    (completeNoBob_computes halleged r) iotaA iotaB hrow hgame hsplit hleaves

/-! ## §3  `09:1566--1701` in ONE proof term on the construction path

The two frozen halves joined over the arbitrary alleged protocol: the
four-category table of `09:1571--1584` supplies `eq:wrapper-mass-leaves-owner`
through the banked `MassRedistributionOwners.constructionPath_ownerLeakage_gt`,
and the transfer family of `09:1617--1699` subtracts the good-owner part from
it.  `hleaves` is not re-introduced as a binder on the way. -/

/-- **`09:1566--1701` travelled on the construction path, at ONE width.**

The frozen four-category table at the owner of the same good donor `j`, at the
same arbitrary protocol `P`, the same original-protocol cost bound, the same
original computation `halleged`, the same target
`C = terminalTarget bcap W.r_2 r_3` and the same tolerance `eta_R`, produces
`eq:wrapper-mass-leaves-owner`; the transfer family then produces
`09:1700--1701`.

The table is supplied as the single frozen display `MassRedistributionOwners.
LossTable` rather than as ten loose binders, so the four rows, the cover
`09:1569`, the six disjointness clauses `09:1569--1570` and the three printed
budgets `09:1575`/`09:1577`/`09:1579` travel as one object.

*What is still a binder.*  Section 2's binders inherited verbatim, plus the
loss table's own data: the deletion-stable Stage-4 conclusion `hdense` at the
owner's copy of `N`, the owner rectangle's column density `hcolsL` and sections
`iotaLA`/`iotaLB`/`hrowL`/`hgameL`, and the frozen prose reading `hfourth`
(`09:1580--1581` against `09:1566--1568`, that the fourth category *is* the
leakage).  **No hypothesis is added to either banked endpoint and none is
weakened; full-bundle satisfiability is not claimed.**

*Why the trivial witness fails.*  As in Section 2, and additionally: the table
alone does not give the conclusion -- the banked
`MassRedistributionOwners.lossTable_alone_does_not_give_massLeavesOwner`
exhibits a legal table whose fourth row is far below `eta_R/2`, so the hardness
step of `09:1600--1610` inside `constructionPath_ownerLeakage_gt` is
load-bearing.

General in all six carriers, in both protocol carriers, and in every width. -/
theorem constructionPath_goodDonor_mass_to_exceptional_of_lossTable
    (W : StageTwoRelaxed.StageTwoWidths)
    (r s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth r) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth r) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ) (pOrd pFor : Slot s)
    (P : Protocol X Y Bool) {R : Slot (scaleAlignWidth r) → Finset X} {A0 : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pstar : CertIndex (completeNoBob r P) R A0 r → Finset (Cl × Cl))
    (Rbin : CertIndex (completeNoBob r P) R A0 r → Slot s → Finset Ltwo)
    (selRow : CertIndex (completeNoBob r P) R A0 r → Slot s × Ltwo →
      (Slot (scaleAlignWidth r) → Cl))
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR g : ℝ} {j : CertIndex (completeNoBob r P) R A0 r}
    (huniq : ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors (completedSystem P hR) Pv etaR)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth r) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ≤ ((scaleAlignWidth r : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors (completedSystem P hR) Pv etaR,
        ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      donorCoord (completedSystem P hR) i ≠ donorCoord (completedSystem P hR) j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      (streamRows XZ (donorCoord (completedSystem P hR) i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ, w (donorCoord (completedSystem P hR) i) = yp.1
        ∧ w (donorCoord (completedSystem P hR) j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (donorCoord (completedSystem P hR) i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (donorCoord (completedSystem P hR) i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (donorCoord (completedSystem P hR) i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth r) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + r - 1)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (iotaA : CertIndex (completeNoBob r P) R A0 r → {a // a ∈ XZ} → X)
    (iotaB : CertIndex (completeNoBob r P) R A0 r → {b // b ∈ YZ} → Y)
    (hrow : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a, RouteRows (completeNoBob r P)
        ((completedSystem P hR).node ((completedSystem P hR).owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat r) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
          ≤ Pv ((completedSystem P hR).owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        ≤ muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RD).card : ℝ)
              / (RD.card : ℝ)))
    -- `09:1566--1615`: the frozen four-category table at the owner of `j`
    {ηC : ℝ} (hRw : 0 < Fintype.card Rw) (T : LossTable Rw etaR)
    {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat etaR ηC
      (TerminalTwoStream.terminalTarget bcap W.r₂ r₃))
    (hcolsL : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaLA : {a // a ∈ (ownerRect T.retained cols).1} → X)
    (iotaLB : {c // c ∈ (ownerRect T.retained cols).2} → Y)
    (hrowL : ∀ a, RouteRows (completeNoBob r P)
      ((completedSystem P hR).node ((completedSystem P hR).owner j)) (iotaLA a))
    (hgameL : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect T.retained cols).1
      (ownerRect T.retained cols).2 a b = gamb (iotaLA a) (iotaLB b))
    (hfourth : rowDensity T.sentElsewhere = ownerLeakage (completedSystem P hR) Pv j) :
    etaR / 4 < exceptionalMass (completedSystem P hR) Pv etaR j :=
  constructionPath_goodDonor_mass_to_exceptional W r s mT dT dOrd bcap r₃ bT Lh vmax
    Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd
    pFor P hR Pstar Rbin selRow Pv huniq hj hetaR hg hgates hcard hdeficit hOuter hbins
    htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd hRegF hdF
    hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist
    hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls hC hcost halleged
    iotaA iotaB hrow hgame hsplit
    (MassRedistributionOwners.constructionPath_ownerLeakage_gt
      (C := TerminalTwoStream.terminalTarget bcap W.r₂ r₃) P hR Pv hj hC hcost halleged
      Nmat hRw T hdense hcolsL iotaLA iotaLB hrowL hgameL hetaR hfourth)

end TransferFamilyOnPath

/-! ## §4  `09:1702` on the construction path with `hexc` DISCHARGED

The predecessor's GAP-EXPOSED item 1, closed.  `MassRedistributionOwners`
carried `09:1702` onto the construction path in both frozen forms, but took the
`09:1700--1701` endpoint as the explicit binder `hexc`, because the transfer
family of `09:1617--1699` had not been travelled there.  Section 3 travelled it;
these two declarations fire `09:1702` with `hexc` **produced** inside the proof
term from the four-category table alone.

`09:1704`'s "Assume then that `e_T > 0`" is therefore a *conclusion* on this
path, never a branch assumption -- which is what the frozen text says it is.
Nothing beyond `09:1702` is claimed; the pigeonhole paragraph `09:1704--1781` is
untouched. -/

section VanishingCaseTravelled

variable {X Y : Type*} [Fintype X] [DecidableEq X]
variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
  [Fintype Rone] [DecidableEq Rone]

/-- **`09:1617--1702` in ONE proof term on the construction path -- the seam test
for this tranche.**

From the frozen four-category table of `09:1571--1584` at the owner of one good
donor of the walked system of an **arbitrary** alleged protocol, and nothing else
new, the frozen `09:1702` -- "If `e_T = 0`, this is already a contradiction" --
is produced in **both** its forms: the exceptional count of `09:1553` is
positive (which is `09:1704`'s branch, as a conclusion), and the final nodes are
not all owned by good donors (which is `09:1553`'s classification form).

No intermediate endpoint is re-introduced as a binder on the way:
`eq:wrapper-mass-leaves-owner`, `eq:wrapper-good-to-good` and `09:1700--1701`
are all consumed inside this proof term, and the predecessor's `hexc` binder is
gone.

*What is still a binder.*  Exactly the union of Sections 1--3, inherited
verbatim; nothing is added and nothing is weakened.  **Full-bundle
satisfiability is not claimed.**

*Why the trivial witness fails.*  The first clause is a strict natural-number
inequality and the second a negation, neither of which is an existential; and
the negated statement is genuinely satisfiable in general -- with
`goodDonors = empty` the owner image is empty, so the inclusion holds **iff**
the final-node set is empty, and this declaration's own `hj` rules that
configuration out.  So the conclusion is a real constraint on the frontier.

General in all six carriers, in both protocol carriers, and in every width. -/
theorem constructionPath_eT_pos_and_not_goodOwned_of_transferFamily
    (W : StageTwoRelaxed.StageTwoWidths)
    (r s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth r) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth r) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ) (pOrd pFor : Slot s)
    (P : Protocol X Y Bool) {R : Slot (scaleAlignWidth r) → Finset X} {A0 : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pstar : CertIndex (completeNoBob r P) R A0 r → Finset (Cl × Cl))
    (Rbin : CertIndex (completeNoBob r P) R A0 r → Slot s → Finset Ltwo)
    (selRow : CertIndex (completeNoBob r P) R A0 r → Slot s × Ltwo →
      (Slot (scaleAlignWidth r) → Cl))
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR g : ℝ} {j : CertIndex (completeNoBob r P) R A0 r}
    (huniq : ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors (completedSystem P hR) Pv etaR)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth r) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ≤ ((scaleAlignWidth r : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors (completedSystem P hR) Pv etaR,
        ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      donorCoord (completedSystem P hR) i ≠ donorCoord (completedSystem P hR) j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      (streamRows XZ (donorCoord (completedSystem P hR) i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ, w (donorCoord (completedSystem P hR) i) = yp.1
        ∧ w (donorCoord (completedSystem P hR) j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (donorCoord (completedSystem P hR) i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (donorCoord (completedSystem P hR) i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (donorCoord (completedSystem P hR) i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth r) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + r - 1)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (iotaA : CertIndex (completeNoBob r P) R A0 r → {a // a ∈ XZ} → X)
    (iotaB : CertIndex (completeNoBob r P) R A0 r → {b // b ∈ YZ} → Y)
    (hrow : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a, RouteRows (completeNoBob r P)
        ((completedSystem P hR).node ((completedSystem P hR).owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat r) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
          ≤ Pv ((completedSystem P hR).owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        ≤ muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RD).card : ℝ)
              / (RD.card : ℝ)))
    {ηC : ℝ} (hRw : 0 < Fintype.card Rw) (T : LossTable Rw etaR)
    {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat etaR ηC
      (TerminalTwoStream.terminalTarget bcap W.r₂ r₃))
    (hcolsL : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaLA : {a // a ∈ (ownerRect T.retained cols).1} → X)
    (iotaLB : {c // c ∈ (ownerRect T.retained cols).2} → Y)
    (hrowL : ∀ a, RouteRows (completeNoBob r P)
      ((completedSystem P hR).node ((completedSystem P hR).owner j)) (iotaLA a))
    (hgameL : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect T.retained cols).1
      (ownerRect T.retained cols).2 a b = gamb (iotaLA a) (iotaLB b))
    (hfourth : rowDensity T.sentElsewhere = ownerLeakage (completedSystem P hR) Pv j) :
    0 < (exceptionalFinal (completedSystem P hR) Pv etaR).card
      ∧ ¬ ((completedSystem P hR).toWrapperFrontier.finalNodes
          ⊆ (goodDonors (completedSystem P hR) Pv etaR).image
              (completedSystem P hR).owner) := by
  have hexc : etaR / 4 < exceptionalMass (completedSystem P hR) Pv etaR j :=
    constructionPath_goodDonor_mass_to_exceptional_of_lossTable W r s mT dT dOrd bcap r₃
      bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd
      xT yy pOrd pFor P hR Pstar Rbin selRow Pv huniq hj hetaR hg hgates hcard hdeficit
      hOuter hbins htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG
      hdOrd hRegF hdF hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem
      hSelRowTyped hSelDist hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls
      hC hcost halleged iotaA iotaB hrow hgame hsplit hRw T hdense hcolsL iotaLA iotaLB
      hrowL hgameL hfourth
  exact ⟨exceptionalCount_pos_of_goodDonor (completedSystem P hR) Pv hetaR hexc,
    MassRedistributionOwners.constructionPath_not_finalNodes_subset_goodOwners P hR Pv
      hetaR hexc⟩

/-- **`09:1702` as the literal frozen contradiction, with `hexc` DISCHARGED.**

"If `e_T = 0`, this is already a contradiction."  On the construction path, from
the four-category table alone: the frozen `e_T = 0` and the walked system of an
arbitrary alleged protocol are jointly inconsistent, with the `09:1700--1701`
endpoint produced rather than assumed.

This is the same statement the predecessor's
`MassRedistributionOwners.constructionPath_eT_zero_is_contradictory` makes, with
its binder `hexc` removed; that theorem is consumed **by pin** and is not
restated.  General. -/
theorem constructionPath_eT_zero_is_contradictory_of_transferFamily
    (W : StageTwoRelaxed.StageTwoWidths)
    (r s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth r) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth r) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ) (pOrd pFor : Slot s)
    (P : Protocol X Y Bool) {R : Slot (scaleAlignWidth r) → Finset X} {A0 : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (Pstar : CertIndex (completeNoBob r P) R A0 r → Finset (Cl × Cl))
    (Rbin : CertIndex (completeNoBob r P) R A0 r → Slot s → Finset Ltwo)
    (selRow : CertIndex (completeNoBob r P) R A0 r → Slot s × Ltwo →
      (Slot (scaleAlignWidth r) → Cl))
    (Pv : FrontierNode (completeNoBob r P) R A0 r →
      CertIndex (completeNoBob r P) R A0 r → ℝ)
    {etaR g : ℝ} {j : CertIndex (completeNoBob r P) R A0 r}
    (huniq : ∀ v : FrontierNode (completeNoBob r P) R A0 r,
      ((completedSystem P hR).cleanFinal.filter
        fun i => (completedSystem P hR).owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors (completedSystem P hR) Pv etaR)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth r) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors (completedSystem P hR) Pv etaR).card : ℝ)
      ≤ ((scaleAlignWidth r : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors (completedSystem P hR) Pv etaR,
        ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG
      ≤ etaR / (8 * g))
    (hOuter : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      donorCoord (completedSystem P hR) i ≠ donorCoord (completedSystem P hR) j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      (streamRows XZ (donorCoord (completedSystem P hR) i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ, w (donorCoord (completedSystem P hR) i) = yp.1
        ∧ w (donorCoord (completedSystem P hR) j) = yp.2)
    (hPairDensity : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (donorCoord (completedSystem P hR) i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (donorCoord (completedSystem P hR) i)) = l)
    (hSelDist : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (donorCoord (completedSystem P hR) i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth r) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + r - 1)
    {gamb : X → Y → Bool} (halleged : Protocol.Computes P gamb)
    (iotaA : CertIndex (completeNoBob r P) R A0 r → {a // a ∈ XZ} → X)
    (iotaB : CertIndex (completeNoBob r P) R A0 r → {b // b ∈ YZ} → Y)
    (hrow : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a, RouteRows (completeNoBob r P)
        ((completedSystem P hR).node ((completedSystem P hR).owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat r) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors (completedSystem P hR) Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
          ≤ Pv ((completedSystem P hR).owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (donorCoord (completedSystem P hR) i) RG)
        ≤ muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord (completedSystem P hR) j) RD).card : ℝ)
              / (RD.card : ℝ)))
    {ηC : ℝ} (hRw : 0 < Fintype.card Rw) (T : LossTable Rw etaR)
    {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat etaR ηC
      (TerminalTwoStream.terminalTarget bcap W.r₂ r₃))
    (hcolsL : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaLA : {a // a ∈ (ownerRect T.retained cols).1} → X)
    (iotaLB : {c // c ∈ (ownerRect T.retained cols).2} → Y)
    (hrowL : ∀ a, RouteRows (completeNoBob r P)
      ((completedSystem P hR).node ((completedSystem P hR).owner j)) (iotaLA a))
    (hgameL : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect T.retained cols).1
      (ownerRect T.retained cols).2 a b = gamb (iotaLA a) (iotaLB b))
    (hfourth : rowDensity T.sentElsewhere = ownerLeakage (completedSystem P hR) Pv j)
    (heT : (exceptionalFinal (completedSystem P hR) Pv etaR).card = 0) : False :=
  MassRedistributionOwners.constructionPath_eT_zero_is_contradictory P hR Pv hetaR
    (constructionPath_goodDonor_mass_to_exceptional_of_lossTable W r s mT dT dOrd bcap r₃
      bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd
      xT yy pOrd pFor P hR Pstar Rbin selRow Pv huniq hj hetaR hg hgates hcard hdeficit
      hOuter hbins htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG
      hdOrd hRegF hdF hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem
      hSelRowTyped hSelDist hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls
      hC hcost halleged iotaA iotaB hrow hgame hsplit hRw T hdense hcolsL iotaLA iotaLB
      hrowL hgameL hfourth)
    heT

end VanishingCaseTravelled

/-! ## §5  Aux-lemma battery, statement poles and rejection probes

This module declares no new type, so its battery tests the **seam** it lands:
the one coordinate carrier the census turned on, the readout that travels across
it, the exact frozen arithmetic of `eq:wrapper-good-to-good` against `09:1701`,
and the mass identity `09:1700` splits.  All are general and proved.

The poles below claim **no** legality: each shows that a hypothesis of Sections
1--4 really bites, or that a conclusion is not met by its trivial witness, or --
in the last two -- what our encoding of `eq:wrapper-owner-gates` does *not*
determine.  None is offered as an instance of the frozen frame. -/

section Battery

/-- **Aux A1 (the ONE-WIDTH census identity).**

The banked owner-transfer family is stated over the coordinate carrier
`Slot (scaleAlignWidth r)` -- `09:105`'s scale-alignment width `q = 2^r` read
through `conv:finite-slots`' zero-based finite slots -- while
`RoutedCertificateConstruction.completedSystem` is generic in a `Coord : Type`.
The two meet on the nose: `Slot d` is `Fin d` and `scaleAlignWidth r` is
`2 ^ r`, so the instantiation performed throughout Sections 1--4 is legal and
needs no transport.  Recorded as an equation rather than asserted in prose.

This is also the exact carrier `RetentionSupply.retentionSupply` produces its
retention over, which is why the retention seam that remains open (the
predecessor's GAP item 4) is about the restriction to `StartedCoord E_0` of
`09:1233--1236` against the definition of `E_0` at `09:447--450`, and **not**
about the width.  General in `r`. -/
theorem coordCarrier_eq (r : ℕ) : Slot (scaleAlignWidth r) = Fin (2 ^ r) := rfl

/-- **Aux A2 (round trip on the carrier).**  The scale-alignment carrier has
exactly `2 ^ r` coordinates, which is `09:105`'s `q = 2^r`.  General. -/
theorem card_coordCarrier (r : ℕ) :
    Fintype.card (Slot (scaleAlignWidth r)) = 2 ^ r :=
  Fintype.card_fin (2 ^ r)

/-- **Aux A3 (the readout travels, at the ONE width).**

The banked family reads each good donor's outer coordinate through
`OwnerIndexedTransferFamily.donorCoord`, and every consumer of
`eq:wrapper-baseline-deficit-sum` and of the transfer bound evaluates
`ordinaryDeficit XZ (donorCoord S i) RG` at it.  On the construction path that
readout lands inside the scale-alignment width of `09:105`: the coordinate of a
certificate of the walked system is a genuine outer coordinate index, not an
index of some wider ambient set.

The single binder `r` carries the routed system's Alice budget (`09:1250`) and
the width exponent (`09:105`) at once -- the statement would not even typecheck
with the two split apart, which is the point of the repair.

General in the protocol carriers, the retention, the width and the index. -/
theorem donorCoord_lt_width {X Y : Type*} [Fintype X] [DecidableEq X] {r : ℕ}
    (P : Protocol X Y Bool) {R : Slot (scaleAlignWidth r) → Finset X} {A0 : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (i : CertIndex (completeNoBob r P) R A0 r) :
    (donorCoord (completedSystem P hR) i).val < 2 ^ r :=
  (donorCoord (completedSystem P hR) i).isLt

/-- **Aux A4 (the exact frozen slack of `09:1697` against `09:1701`).**

`eq:wrapper-good-to-good` ends at `3 eta_R/16 < eta_R/4`, and `09:1700--1701`
reads that gap as the mass forced onto exceptional nodes.  The gap is exactly
one sixteenth of the tolerance, and it is strict precisely because the tolerance
is positive -- which is why `hetaR` is carried through every declaration above
and is not decoration.  General in the tolerance. -/
theorem goodToGood_slack {etaR : ℝ} (hetaR : 0 < etaR) :
    3 * etaR / 16 + etaR / 16 = etaR / 4 ∧ 3 * etaR / 16 < etaR / 4 :=
  ⟨by ring, by linarith⟩

end Battery

section Split

variable {Xa Yb Zc : Type*} {Coord ι Vn : Type*} {Pr : Protocol Xa Yb Zc} {rr A0 : ℕ}
variable [Fintype Vn] [DecidableEq Vn] [Fintype ι] [DecidableEq ι]

/-- **Aux A5 (monotonicity through the frozen split of `09:1700`).**

`09:1553` splits the final nodes other than `own(j)` into the owners of other
good donors and the exceptional nodes, and the banked
`OwnerMassTransfer.ownerLeakage_split` is that split as a mass identity.  The
banked module recorded the *good-owner* half of the resulting monotonicity
(`goodOwnerMass_le_ownerLeakage`); the exceptional half -- the one Sections 2--4
actually push through -- was not recorded, and is proved here.

It is the sanity check that the endpoint of `09:1701` is a statement *about* the
leakage of `09:1612` and cannot exceed it.  General in every carrier. -/
theorem exceptionalMass_le_ownerLeakage (S : RoutedSystem Pr Coord ι Vn rr A0)
    {Pv : Vn → ι → ℝ} {etaR : ℝ} {j : ι} (hj : j ∈ goodDonors S Pv etaR)
    (hnn : ∀ T : Vn, 0 ≤ Pv T j) :
    exceptionalMass S Pv etaR j ≤ ownerLeakage S Pv j := by
  have hsplit := ownerLeakage_split S Pv etaR hj
  have hgood : 0 ≤ goodOwnerMass S Pv etaR j := by
    unfold goodOwnerMass
    exact Finset.sum_nonneg fun T _ => hnn T
  linarith

/-- **Pole 1: the discharged `hexc` is a real constraint, not a bookkeeping
identity.**

`09:1702` says `e_T = 0` contradicts the endpoint.  The reason is that with no
exceptional node there is no exceptional mass at all, so at a positive tolerance
the endpoint of `09:1701` fails outright.  This is why Section 4 can extract
`09:1704`'s branch as a *conclusion*, and it is the pole showing that the
conclusion of Sections 2--3 is not met by the trivial witness.

Consumed from the banked `OwnerMassTransfer.exceptionalMass_of_empty`.
General. -/
theorem endpoint_fails_at_empty_exceptional (S : RoutedSystem Pr Coord ι Vn rr A0)
    (Pv : Vn → ι → ℝ) {etaR : ℝ} (hetaR : 0 < etaR) (j : ι)
    (hempty : exceptionalFinal S Pv etaR = ∅) :
    ¬ (etaR / 4 < exceptionalMass S Pv etaR j) := by
  rw [exceptionalMass_of_empty S Pv etaR j hempty]
  intro h
  linarith

end Split

section Poles

/-- **Pole 2: `eq:wrapper-good-to-good` alone does NOT give `09:1701`.**

The transfer family bounds the good-to-good mass by `3 eta_R/16`; that bound is
compatible with *no* exceptional mass whatsoever.  What forces the endpoint is
`eq:wrapper-mass-leaves-owner`, the second half Section 3 supplies from the
frozen four-category table.  At `eta_R = 1` a configuration with zero
good-to-good mass and zero exceptional mass meets the good-to-good clause and
fails `09:1701`.

**Claims no legality:** the values are this pole's own and no routed instance is
exhibited.  This is a load-bearingness check on `hleaves`, not an instance of
the frozen frame. -/
theorem goodToGood_alone_does_not_give_the_endpoint :
    (0 : ℝ) ≤ 3 * (1 : ℝ) / 16 ∧ ¬ ((1 : ℝ) / 4 < 0) := by
  constructor
  · norm_num
  · norm_num

/-- **Pole 3: the two frozen halves are jointly satisfiable (hypothesis
consistency for the seam this tranche composes).**

Section 3 conjoins `eq:wrapper-good-to-good` (`good <= 3 eta_R/16`),
`eq:wrapper-mass-leaves-owner` (`eta_R/2 < leak`) and the banked split
(`leak = good + exc`), and concludes `eta_R/4 < exc`.  A green build would not
notice if that bundle were contradictory at the frozen side conditions.  It is
not: the four quantities are simultaneously realizable at a positive tolerance,
with the conclusion strictly satisfied.

*Why the trivial witness fails.*  The all-zero assignment
`good = leak = exc = 0` satisfies the first two conjuncts and fails the third,
`eta_R/2 < leak`, at every positive tolerance -- so the exhibited witness has to
carry real mass and the statement is not met by zero.

**Claims no legality:** the values are this pole's own; `eta_R = 1` is outside
the schedule's own range and no routed instance is exhibited.  This is a
consistency check on the arithmetic seam, not an instance of the frozen
frame. -/
theorem the_two_frozen_halves_are_jointly_satisfiable :
    ∃ etaR good leak exc : ℝ, 0 < etaR ∧ good ≤ 3 * etaR / 16
      ∧ etaR / 2 < leak ∧ leak = good + exc ∧ etaR / 4 < exc :=
  ⟨1, 0, 3 / 5, 3 / 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Pole 4: the ONE coordinate carrier is not degenerate.**

At the frozen width the scale-alignment carrier of `09:105` is inhabited, so the
per-donor readout of Aux A3 is a statement about a nonempty index set and the
instantiation of Sections 1--4 is not vacuous at the carrier level.  Recorded at
`r` arbitrary, so it is not a claim about one width.  General. -/
theorem coordCarrier_nonempty (r : ℕ) : 0 < Fintype.card (Slot (scaleAlignWidth r)) := by
  rw [card_coordCarrier]
  positivity

/-- **Pole 5 (DEFINED-VS-FREE): `eq:wrapper-owner-gates` does NOT pin `q_2` or
`b_1`, so no witness extracted from it may be called the paper's.**

This is the kernel-checked form of the provenance correction this generation
carries.  `q_2` and `b_1` are **DEFINED** quantities of the frozen schedule:

* `q_2` is fixed by `06:122--125`, "The source theorem then fixes `q_2 = the
  least power of two at least `12 s N_E`" -- reified in this repository as
  `GuardedSourceSlab.q2` and identified as that least power of two by
  `DenseStageFourOpening.schedule_q2` / `schedule_q2_unique`;
* `b_1` is fixed by `eq:stage1-scales` (`06:312--320`), `b_1 = 2^{j_49(a-2)}`
  with `a = C_0(log_2 A_*)^2` of `06:314`.  **Census fact, recorded rather than
  guessed:** this repository contains **no** reification of that display; `b_1`
  occurs in Section 9 only as the field `StageTwoRelaxed.StageTwoWidths.b₁`.
  Reifying `06:317` belongs to a `ParameterSchedule` tranche and is registered
  as a deferred obligation, not performed here.

The banked `WrapperMassRedistribution.ownerGates_nonvacuous` produces *some*
pair satisfying the block's own three gates, by a least-power-of-two search at
the gate thresholds.  That is a satisfiability witness and nothing more: this
pole proves that the gate bundle together with the two structural readouts of
`09:1670--1671` is satisfied by **strictly more than one** pair, because
`(2 q_2, b_1 + 1)` satisfies it whenever `(q_2, b_1)` does -- `lambdaZero` is
invariant under that shift, so the first gate is untouched, the third only
loosens, and the readouts survive.  A predicate with two distinct solutions
identifies neither of them, so an existential witness carries **no** provenance
and may never be presented as the `06:124`/`06:317` values.

*Why the trivial witness fails.*  The conclusion is not an existential over a
free variable: the exhibited second solution is a named function of the input
pair and is proved distinct from it, so nothing here is met by re-returning the
hypothesis.

**Claims no legality and exhibits no instance of the frozen frame.**  General in
the width, the tolerance, the base-row fraction and both scales. -/
theorem ownerGates_do_not_pin_the_widths {q q₂ b₁ : ℕ} {etaR g : ℝ}
    (h16 : 16 ≤ q₂) (hgate16 : 16 * q₂ ≤ 2 ^ b₁)
    (hgates : wrapperOwnerGates q q₂ etaR g b₁) :
    (2 * q₂, b₁ + 1) ≠ (q₂, b₁)
      ∧ 16 ≤ 2 * q₂
      ∧ 16 * (2 * q₂) ≤ 2 ^ (b₁ + 1)
      ∧ wrapperOwnerGates q (2 * q₂) etaR g (b₁ + 1) := by
  obtain ⟨hg1, hg2, hg3⟩ := hgates
  have hne : (2 * q₂, b₁ + 1) ≠ (q₂, b₁) := by
    intro h
    have : b₁ + 1 = b₁ := congrArg Prod.snd h
    omega
  have h16' : 16 ≤ 2 * q₂ := by omega
  have hpow : 16 * (2 * q₂) ≤ 2 ^ (b₁ + 1) := by
    have hstep : 2 * (16 * q₂) ≤ 2 * 2 ^ b₁ := Nat.mul_le_mul_left 2 hgate16
    calc 16 * (2 * q₂) = 2 * (16 * q₂) := by ring
      _ ≤ 2 * 2 ^ b₁ := hstep
      _ = 2 ^ (b₁ + 1) := by rw [pow_succ]; ring
  have hlam : DenseBranchSelection.lambdaZero (2 * q₂) (b₁ + 1)
      = DenseBranchSelection.lambdaZero q₂ b₁ := by
    have h2 : ((2 : ℝ) ^ b₁) ≠ 0 := by positivity
    simp only [DenseBranchSelection.lambdaZero, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  have hcast : ((2 * q₂ : ℕ) : ℝ) = 2 * (q₂ : ℝ) := by push_cast; ring
  have hq₂nn : (0 : ℝ) ≤ (q₂ : ℝ) := Nat.cast_nonneg _
  refine ⟨hne, h16', hpow, ?_, hg2, ?_⟩
  · rw [hlam]; exact hg1
  · rw [hcast]; linarith

/-- **Pole 6 (HYPOTHESIS CONSISTENCY at SYNTHETIC widths -- NON-FIDELITY): the
two `eta_R`-coupled bundles Section 3 newly conjoins are jointly satisfiable.**

Section 3 is the first statement in the development to carry, in one hypothesis
bundle and at **one and the same** tolerance, both

* `eq:wrapper-owner-gates` (`09:1682--1689`), the schedule side of the transfer
  family, as `wrapperOwnerGates`; and
* the four-category loss table of `09:1571--1584`, as `LossTable`,

together with `09:1670--1671`'s two structural readouts `q_2 >= 16` and
`16 q_2 <= 2^{b_1}`.  A green build would not notice if that conjunction were
contradictory.  It is not: both are inhabited at the same `eta_R`.

**What is the paper's, and what is not -- stated exactly.**  `eta_R` is
**DEFINED and EVALUATED**: it is `ParameterSchedule.etaR`, tracing
`eq:eta-choice` (`06:204--219`), and both legality inputs are the banked
readouts of that definitional chain -- `etaR_pos` at the frozen side conditions
`3 < s`, `0 < delta_v(G)`, `0 < zeta`, and `etaR_le_bound`, whose value
`1/36800` is exactly the range `ownerGates_nonvacuous` demands.  `g` is the
frozen `91/92` (`09:297`) and `mu_P <= g/20` is the checked identity
`WrapperMassRedistribution.muP_le_g_div_twenty`.  **No numeral is assigned to
any of those.**

**The widths `q_2` and `b_1` are NOT the paper's, and are not claimed to be.**
They are produced by `ownerGates_nonvacuous`, an existential over the block's
own three gates; Pole 5 proves that those gates have at least two distinct
solutions and therefore identify neither.  The DEFINING displays are `06:124`
(`q_2` = the least power of two at least `12 s N_E`, reified as
`GuardedSourceSlab.q2`) and `06:317` (`b_1 = 2^{j_49(a-2)}`, **not reified
anywhere in this repository**).  Discharging this pole at those values is a
registered, deferred obligation; it is not attempted here, and the earlier
generation's claim that these witnesses "come out of the least-power-of-two
accessors of `06:1253--1268`" was **false and is withdrawn** -- `06:1253--1268`
is the generic least-power-of-two record machinery, and is the defining display
of neither quantity.

*Why the trivial witness fails.*  The exhibited table must have all four
categories at strictly positive density and an inhabited retained set, so a
table with any empty row -- in particular the empty table -- does not satisfy
this statement.

**NON-FIDELITY on both axes, and no legality claimed.**  The loss table's
carrier is `Fin (probeWidth eta_R)`, not `Rows(N)`, and the widths are
synthetic; so this is a consistency check on the *bundle*, never the paper's
instance.  The canonical-inhabitation obligation registered by
`MASS-REDISTRIBUTION-OWNERS-001` is untouched and is **not** discharged here.
General in `s`, `delta_v(G)`, `zeta` and the wrapper width. -/
theorem gates_and_lossTable_are_consistent_at_synthetic_widths
    {s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    ∃ (q₂ b₁ : ℕ) (T : LossTable (Fin (probeWidth (ParameterSchedule.etaR s dv zeta)))
        (ParameterSchedule.etaR s dv zeta)),
      16 ≤ q₂ ∧ 16 * q₂ ≤ 2 ^ b₁
        ∧ wrapperOwnerGates q q₂ (ParameterSchedule.etaR s dv zeta) (91 / 92) b₁
        ∧ 0 < rowDensity T.deleted ∧ 0 < rowDensity T.routeLoss
        ∧ 0 < rowDensity T.earlyStopped ∧ 0 < rowDensity T.sentElsewhere
        ∧ T.retained.Nonempty := by
  obtain ⟨q₂, b₁, h16, hgate16, hgates⟩ :=
    ownerGates_nonvacuous hq (ParameterSchedule.etaR_pos hs hdv hz)
      (ParameterSchedule.etaR_le_bound s dv zeta) muP_le_g_div_twenty
  obtain ⟨T, hd, hr, he, hse, hret⟩ :=
    MassRedistributionOwners.probe_at_schedule_etaR hs hdv hz
  exact ⟨q₂, b₁, T, h16, hgate16, hgates, hd, hr, he, hse, hret⟩

/-- **Pole 7 (NON-VACUITY at the carrier Sections 1--4 actually use): the owner
gates are STRUCTURALLY COMPATIBLE with the banked `StageTwoWidths` record.**

**NON-FIDELITY, and no legality is claimed.**  Read the heading as *structural
compatibility*, not as legality at the paper's schedule: what is proved is that
the banked `StageTwoRelaxed.StageTwoWidths` record and `eq:wrapper-owner-gates`
can be inhabited simultaneously, and nothing more.  The identifier still reads
`..._at_a_legal_stageTwoWidths`; that word over-claims in exactly the way this
paragraph corrects, and the rename to
`ownerGates_at_a_structurally_compatible_stageTwoWidths` is REGISTERED for a
later tranche because renaming moves the module hash and the
`tools/AxiomAudit.lean` pin, so it is a re-bank rather than a record repair.

Sections 1--4 do not take `q_2` and `b_1` as free naturals: they read them off a
`StageTwoRelaxed.StageTwoWidths`, whose fields carry the frozen Stage-2
structural constraints -- `4 t_2 <= q_2` (`eq:stage2-balance-ceilings`,
`07:280`), `5 <= m_HS <= k_2`
(`D-inherited-contracts.tex:496` and `07:281`) and the depth gate
`131072 q_2 <= 2^{b_1}` (`07:398--401`).  Pole 6 exhibits a pair satisfying
`eq:wrapper-owner-gates` alone; nothing before this declaration showed that such
a pair can also carry that record's Stage-2 structure, and a bundle whose
schedule side were inhabitable by no `W` at all would make every statement of
Sections 1--4 vacuous while compiling green.

The two are compatible.  The exhibited `W` takes `k_2 = m_HS = 5` and, at the
tolerance ceiling `eta_R <= 1/36800` of `eq:eta-choice` (banked as
`ParameterSchedule.etaR_le_bound`, so this is not an extra demand), sets
`r_2` to the banked generic least-power-of-two exponent at the third gate's
threshold `64 mu_P q/eta_R` and `b_1` to the least exponent clearing **both**
`07:398--401`'s `131072 q_2` and the first gate's `64 mu_P q q_2/eta_R` at once.
`4 t_2 = 128 <= q_2` is then forced rather than posited, because the third gate
already drives `q_2 >= 12800`; and `mu_P <= g/20` enters as the checked identity
`muP_le_g_div_twenty` at the frozen `g = 91/92`.

*Why the trivial witness fails.*  The conclusion is not "some structure exists":
the `StageTwoWidths` constructor demands the two exponent inequalities as proof
fields, and the depth gate in particular is what forces `b_1` well above the
first owner gate's own threshold -- exhibiting the pair of Pole 6 alone does not
satisfy this statement.

**The FOUR non-paper values, on the DEFINED-vs-FREE axis.**  Every one of
`k_2`, `m_HS`, `r_2` and `b_1` here is synthetic; none is the schedule's DEFINED
value.

* `m_HS` is DEFINED at `D:508--509` as the least-witness
  `m_HS = min { r : HSThreshold(r) }`, and `D:516` rules out any numeral
  outright: "No numerical value is required."  Setting `m_HS = 5` is therefore
  **not** the paper's value; `D:496` bounds it only from below (`HSThreshold(r)`
  contains the conjunct `5 <= r`), and the unrelated `j = 5` of `D:495` is a
  call parameter, not `m_HS`.
* `k_2` is DEFINED at `06:763--772` (`eq:t2-search`) as the least integer
  satisfying, among other conditions, `k_2 >= max{4, 2^19, m_HS}`.  The
  synthetic `k_2 = 5` is far below that floor.
* `r_2` and `b_1` are search outputs at this block's own thresholds, not the
  schedule's DEFINED values (`06:124` for `q_2`, `06:317` for `b_1`); Pole 5 is
  precisely the proof that the gates cannot identify them.

**This pole is therefore NOT evidence that the bundle is satisfiable at the
schedule's own `k_2`.**  The field `four_t_2 <= q_2` is discharged here as
`4 * 2^5 = 128 <= q_2` off `q_2 >= 12800`; at the DEFINED `k_2 >= 2^19` of
`06:766` that field would **not** follow from `q_2 >= 12800`, and `r_2` would
have to be raised with it.  Reification of `m_HS` and `k_2`, and the
corresponding canonical-inhabitation check, are REGISTERED as deferred
obligations alongside `q_2` and `b_1` in the route ledger.

What this statement does assert is the *structural compatibility* of
`eq:stage2-balance-ceilings` with `eq:wrapper-owner-gates`, never the paper's
instance.  General in the wrapper width and the tolerance. -/
theorem ownerGates_at_a_legal_stageTwoWidths {q : ℕ} {etaR : ℝ}
    (hq : 0 < q) (hetaR0 : 0 < etaR) (hetaR : etaR ≤ 1 / 36800) :
    ∃ W : StageTwoRelaxed.StageTwoWidths,
      16 ≤ W.q₂ ∧ 16 * W.q₂ ≤ 2 ^ W.b₁
        ∧ wrapperOwnerGates q W.q₂ etaR (91 / 92) W.b₁ := by
  classical
  have hmu : muP = 1 / 184 := rfl
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set r₂ : ℕ := ParameterSchedule.leastPowTwoExp (64 * muP * (q : ℝ) / etaR) with hr₂def
  have hx : 64 * muP * (q : ℝ) / etaR ≤ (2 : ℝ) ^ r₂ :=
    ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hbig : (12800 : ℝ) ≤ (2 : ℝ) ^ r₂ := by
    have h1 : (12800 : ℝ) ≤ 64 * muP * (q : ℝ) / etaR := by
      rw [le_div_iff₀ hetaR0, hmu]
      nlinarith [hetaR, hqR, hetaR0]
    linarith
  set b₁ : ℕ := ParameterSchedule.leastPowTwoExp
    (131072 * (2 : ℝ) ^ r₂ + 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ / etaR) with hb₁def
  have hsum : 131072 * (2 : ℝ) ^ r₂ + 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ / etaR
      ≤ (2 : ℝ) ^ b₁ := ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ r₂ := by positivity
  have hterm2 : (0 : ℝ) ≤ 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ / etaR := by
    rw [hmu]; positivity
  have hdepthR : 131072 * (2 : ℝ) ^ r₂ ≤ (2 : ℝ) ^ b₁ := by linarith
  have hgate1R : 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ / etaR ≤ (2 : ℝ) ^ b₁ := by
    nlinarith [hpow2]
  have hcast₂ : (((2 : ℕ) ^ r₂ : ℕ) : ℝ) = (2 : ℝ) ^ r₂ := by push_cast; ring
  have hdepthN : 131072 * 2 ^ r₂ ≤ 2 ^ b₁ := by
    have : ((131072 * 2 ^ r₂ : ℕ) : ℝ) ≤ (((2 : ℕ) ^ b₁ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have h128 : 4 * 2 ^ 5 ≤ 2 ^ r₂ := by
    have : ((4 * 2 ^ 5 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ r₂ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  refine ⟨⟨5, r₂, b₁, 5, le_refl 5, le_refl 5, h128, hdepthN⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have : ((16 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ r₂ : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have h16 : 16 * 2 ^ r₂ ≤ 131072 * 2 ^ r₂ :=
      Nat.mul_le_mul_right _ (by norm_num)
    exact le_trans h16 hdepthN
  · show 2 * muP * (q : ℝ) * DenseBranchSelection.lambdaZero (2 ^ r₂) b₁ ≤ etaR / 16
    have hlhs : 2 * muP * (q : ℝ) * DenseBranchSelection.lambdaZero (2 ^ r₂) b₁
        = (4 * muP * (q : ℝ) * (2 : ℝ) ^ r₂) / 2 ^ b₁ := by
      rw [DenseBranchSelection.lambdaZero, hcast₂]
      field_simp
      ring
    have hpowb : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
    have hkey : 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ ≤ etaR * (2 : ℝ) ^ b₁ := by
      rw [div_le_iff₀ hetaR0] at hgate1R
      linarith
    rw [hlhs, div_le_div_iff₀ hpowb (by norm_num : (0 : ℝ) < 16)]
    nlinarith [hkey]
  · exact muP_le_g_div_twenty
  · show 64 * muP * (q : ℝ) / etaR ≤ ((2 ^ r₂ : ℕ) : ℝ)
    rw [hcast₂]
    exact hx

end Poles

end EthInapproximability.ParameterizedNP.OwnerTransferFamily
