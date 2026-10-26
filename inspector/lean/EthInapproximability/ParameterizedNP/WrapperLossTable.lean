import EthInapproximability.ParameterizedNP.OwnerFamilyToPigeonhole
import EthInapproximability.ParameterizedNP.WrapperExceptionalCount

/-!
# Parameterized NP route: the loss table consumed, and the terminal donor gate

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche), **lines `09:1566--1741`**.  Every
  anchor below was opened first-hand in that file for this tranche.

  The four frozen deliverables this module consumes **in proof terms**, in the
  order the frozen block prints them:

  1. `09:1566--1568`, the `m_{j,T}` and `own(i)` conventions ("For a donor `j`
     and final node `T`, let `m_{j,T}` be the protected mass from `j` reaching
     `T`, normalized by `m`.  Write `own(i)` for the owner of `i in J_good`"),
     the four-category sentence `09:1569--1570`, the table `09:1571--1584` with
     its fourth line `09:1580--1581` ("protected rows sent to other final nodes
     -- the remaining loss"), and `eq:wrapper-mass-leaves-owner` (display
     `09:1611--1615`, label `09:1614`);
  2. the owner-to-owner transfer bound `09:1617--1689` --
     `eq:wrapper-owner-threshold` (display `09:1620--1625`, label `09:1624`),
     `eq:wrapper-baseline-deficit-sum` (display `09:1627--1631`, label
     `09:1630`), `eq:wrapper-owner-gates` (display `09:1682--1689`, label
     `09:1688`) -- and `eq:wrapper-good-to-good` (display `09:1692--1699`, label
     `09:1698`), whose consequence `09:1700--1701` is "every good donor sends
     more than `eta_R/4` protected mass to exceptional final nodes";
  3. `09:1702`, the vanishing case: "If `e_T = 0`, this is already a
     contradiction", together with `09:1704`'s "Assume then that `e_T > 0`";
  4. `eq:wrapper-terminal-donor-gate` (display `09:1736--1741`, label
     `09:1740`): "`|J_good| > q/2`, `q/(4 E_T) > u_don B_theta`", with its
     frozen justification `09:1732--1734` ("The first gate in
     `eq:terminal-wrapper-gates` gives `E_T <= q/8`, whereas its second gate and
     `u_don <= u_term` give the other inequality below").

* **Cross-anchors opened first-hand for this tranche:**
  * `09:1715--1716`, "The parameter schedule computes deterministic bounds
    `e_T <= E_T` and `u_don <= u_term`" -- the first of which is **derived** in
    Section 4b below and the second of which is the banked
    `WrapperMassRedistribution.uDon_le_uTerm`;
  * `09:1717--1718`, **the defining display of `u_don`**: "`u_don` is the least
    power of two satisfying `u_don delta_0 >= 8s`".  This is the *only* frozen
    definition of `u_don`; `06:726--728` defines `u_term` at the *different*
    density `delta_term` and is not a defining display for `u_don`.  `u_don` is
    therefore reified here as the banked least-power-of-two accessor
    `ParameterSchedule.uTerm` read at `deltaZero`, i.e. as the paper's own
    closed form, never as a numeral;
  * `eq:wrapper-terminal-density` (display `09:1710--1713`, label `09:1712`),
    `delta_0 = eta_R/(8 e_T mu_P)`, banked as
    `WrapperMassRedistribution.deltaZero`;
  * `09:1718--1726`, the derived good-donor count `|J_good| >= q - E_T`, banked
    at the canonical system as
    `WrapperExceptionalCount.canonical_goodDonorCount_ge_q_sub_ET` and consumed
    here **by pin** as the `hjgood` slot of `eq:wrapper-terminal-donor-gate`;
  * `09:1727--1731`, "`e_0^max >= 1` and `E_T >= 1`.  Thus the division by
    `E_T` below is legal", banked as
    `WrapperMassRedistribution.one_le_ET_of_e0Max_pos`;
  * `eq:wrapper-exceptional-count` (display `09:1555--1563`, label `09:1562`)
    and `eq:wrapper-bob-heavy-count` (`09:1542--1547`), the two frozen counts
    whose canonical firings supply `e_T <= E_T` in Section 4b;
  * `eq:terminal-uniform-bounds` (display `06:716--731`, label `06:730`;
    `vartheta = 9/16` at `06:718`, `E_B` at `06:720--722`, `E_T` at `06:723`,
    `delta_term` at `06:724--725`, `u_term` at `06:726--728`) and
    `eq:terminal-wrapper-gates` (display `06:738--743`, label `06:742`), both in
    `06-parameter-schedule.tex` (SHA-256
    `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
    recomputed first-hand this tranche);
  * `09:452--453`, the deterministic bound `e_0 <= e_0^max`, and `09:1346--1347`,
    a clean-classified final node hosts a clean certificate -- the two binders
    the predecessor tranche introduced and this one inherits **verbatim**;
  * `09:1550`, the owner sentence, and `09:1330--1331`, "no Bob query has
    occurred on the route to this node" -- which is why the owner's stopping
    rule is **derived** here (`OwnerIndexedTransferFamily.goodDonor_owner_not_firstBob`)
    rather than assumed.

* **Reader counterpart: NONE claimable, inherited.**  Checked first-hand this
  tranche over `routes/parameterized-np/reader-facing/sections/`: the 41-page
  reader artifact carries no item stating any of these four displays.  Its only
  passage covering this material is `A-stage4-details.tex:370--399`, which is
  running prose ("The complete owner--donor count is finite: it uses only the
  fixed reservoir masses above ... It is expanded line by line in the
  ultra-explicit companion", `396--399`); its single displayed endpoint
  (`A-stage4-details.tex:393--395`) is `D_U(1; 1 - delta_U, theta) >= C + r_q`,
  carries no label, and is **not** stated by any declaration below.  The
  READER-COUNTERPART rule forbids citing prose and forbids reusing another
  declaration's item, so none is cited rather than one invented.

## What this module is, and what it deliberately is not

Everything below is **composition of banked lemmas at the frozen index sets**.
No new mathematical claim is made, no new `structure`, `def` or `abbrev` is
declared, and no banked statement is restated.  In particular:

* the four-category arithmetic is the banked
  `MassLeavesOwner.massLeavesOwner_of_fourCategories` (which itself pins
  `WrapperMassRedistribution.wrapperMassLeavesOwner` and discharges its `hHard`
  binder through the deletion-stable Stage-4 theorem);
* the owner-to-owner transfer family and `eq:wrapper-good-to-good` are the
  banked `OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_derived`;
* the `e_T = 0` case split runs through the banked **iff**
  `WrapperExceptionalCount.exceptionalFinal_eq_empty_iff` and the banked
  `OwnerFamilyToPigeonhole.exceptionalFinal_nonempty_of_goodDonor`;
* `eq:wrapper-terminal-donor-gate`'s arithmetic is the banked
  `WrapperMassRedistribution.wrapperTerminalDonorGate`.

**What is new is that they are wired.**  Named for what each firing retires:

* Section 1 turns the four-category table into the `hleaves` slot the transfer
  chain consumes.  Before this tranche `eq:wrapper-mass-leaves-owner` was proved
  about `rowDensity D_4` and `09:1700--1701` *assumed*
  `eta_R/2 < ownerLeakage`; the two were never joined.  The join costs exactly
  one binder, `hfourth`, which is the frozen reading of `09:1580--1581` against
  `09:1566--1568` (the fourth category *is* `sum_{T != own(j)} m_{j,T}`), and
  that reading is a modelling identification the paper states in prose, so it is
  carried as the explicit binder it is and is never derived from the encoding.
* Section 2 fires the transfer chain with `hleaves` **discharged** by Section 1.
* Section 3 executes `09:1702` at the routed system: `e_T = 0` is refuted, in
  both the cardinality form and the frozen ownership form of the banked iff.
  Section 3b then **travels** the whole seam: from the four-category table alone,
  with no intermediate endpoint re-introduced as a binder, `09:1702` follows in
  one proof term.
* Section 4a proves `eq:wrapper-terminal-donor-gate` with **both** analytic
  inputs of `09:1732--1734` discharged: `E_T >= 1` from
  `one_le_ET_of_e0Max_pos`, and `u_don <= u_term` from `uDon_le_uTerm`.  The
  three rows of `eq:terminal-wrapper-gates` enter as the banked
  `ParameterSchedule.terminalWrapperGates`, i.e. as the paper's own `Prop` and
  not as three ad hoc inequalities.
* Section 4b fires 4a at `FrontierIndexing.canonicalSystem`, with `hjgood` the
  banked `09:1718--1726` closure and with `e_T <= E_T` (`09:1715`) **derived**
  from the two canonical counts rather than assumed.

**`hcount` and `hclean` are not re-hoisted.**  Both were retired by the
predecessor tranches (`BobHeavyDonorCount`, `FrontierSumAssembly`,
`WrapperExceptionalCount`) and are obtained in-proof in Section 4b from
`BobHeavyDonorCount.canonical_wrapperBobHeavyCount` and
`FrontierSumAssembly.canonical_cleanCount_of_reference_construction`; neither
appears as a hypothesis of any declaration below.

**What is still a binder.**  Everything the predecessors carried, inherited
verbatim: `hladder` with `residual`/`hresidual`, `hhost`, `hLocExCC`/`hLocExEP`
(the **EXPANDER-001** entry point, `thm:certified-localized-extension`,
`A:109--146`), `hfinal`, `halleged`, `hcost`, `hres`, `hinj`, the realization
telescope `hstateOf`/`hTTS`/`hsplit`/`iotaA`/`iotaB`/`hrow`/`hgame`, the loss
table's own three budget lines `h1`/`h2`/`h3` and its rectangle sections, the
frozen reading `hfourth`, the gate system `hgates`, and `heTpos` (`09:1704`'s
own branch assumption).  **No hypothesis is added to any banked endpoint and
none is weakened.  Full-bundle satisfiability is not claimed.**

**Canonical inhabitation: INHERITED, REGISTERED and DEFERRED.**  This module
declares no new type, so it opens no new canonical-inhabitation obligation.  The
inherited one cannot be discharged, because the paper's own instance of every
statement here is a function of the alleged shallow protocol of `09:1187--1193`,
whose non-existence is the conclusion of the subsection: the frozen paper
exhibits no routed instance by construction.  The consistency lemma of Section 6
is explicitly **NON-FIDELITY** on that axis -- it is a satisfiability statement
about the *gate system*, at symbolic schedule quantities, and is not offered as
the paper's instance.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:262--263`,
`09:1780--1781`) is neither stated nor implied; `09:1742--1781` -- the
`delta_0 < 1` step, the projection cover, the coordinate extraction, the block
supply and the final Extension call -- remains **OPEN**.
-/

namespace EthInapproximability.ParameterizedNP.WrapperLossTable

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
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply
open EthInapproximability.ParameterizedNP.SelectEmbedComposition
open EthInapproximability.ParameterizedNP.FirstBobLightClosure
open EthInapproximability.ParameterizedNP.ClosureSelectSupply
open EthInapproximability.ParameterizedNP.ProtectedEarlyClosure
open EthInapproximability.ParameterizedNP.BobHeavyDonorCount
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.MassLeavesOwner
open EthInapproximability.ParameterizedNP.OwnerMassTransfer
open EthInapproximability.ParameterizedNP.OwnerIndexedTransferFamily
open EthInapproximability.ParameterizedNP.OwnerFamilyToPigeonhole

/-! ## §1  The four-category table read as the owner leakage
(`09:1566--1615`)

`MassLeavesOwner` banked `eq:wrapper-mass-leaves-owner` as a statement about
`rowDensity D_4`, the normalized size of the fourth table category.
`OwnerMassTransfer` banked `ownerLeakage S Pv j = sum_{T != own(j)} m_{j,T}` and
every consumer of `09:1700--1701` takes `eta_R/2 < ownerLeakage` as its
`hleaves` slot.  The frozen text identifies the two on `09:1580--1581`
("protected rows sent to other final nodes") read against `09:1566--1568`
("`m_{j,T}` is the protected mass from `j` reaching `T`, normalized by `m`").

That identification is prose in the source, so it is the single explicit binder
`hfourth` here -- never a derived fact of the encoding, and never quietly
inserted into a banked statement.  Everything else on this leg is discharged:
the owner's stopping rule `09:1550` is
`OwnerIndexedTransferFamily.goodDonor_owner_not_firstBob`, and the hardness step
`09:1609--1610` is already inside the banked four-category endpoint. -/

section LossTable

variable {Xa Yb : Type*} {Coord ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
variable [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]

/-- **`09:1566--1615` delivered in the shape `09:1700--1701` consumes.**

The frozen four-category table at the owner of a good donor `j`, concluded on
the *leakage* rather than on the fourth category's density: the four rows are
the categories `D_1` (`09:1574--1575`, initially deleted rows, at most
`eta_R m/16`), `D_2` (`09:1576--1577`, base rows lost along the unique clean
route, less than `eta_R m/16`), `D_3` (`09:1578--1579`, protected rows stopped
at first-Bob nodes, at most `eta_R m/4`) and `D_4` (`09:1580--1581`, protected
rows sent to other final nodes, "the remaining loss"), and the conclusion is
`eq:wrapper-mass-leaves-owner`, `sum_{T != own(j)} m_{j,T} > eta_R/2`.

*What is derived rather than assumed.*  The node is the owner `own(j)` of
`09:1568` and its stopping rule `S.firstBob (own j) = false` (`09:1550`) is
produced from `j in J_good` by
`OwnerIndexedTransferFamily.goodDonor_owner_not_firstBob`, not assumed; the
retention identity and the hardness contradiction of `09:1600--1610` are inside
the banked endpoint and are restated nowhere.

*What is still a binder.*  `hfourth`, the frozen reading of `09:1580--1581`;
the three budget lines `h1`, `h2`, `h3`; the Stage-4 conclusion `hdense`; the
rectangle data `hcols`, `iotaA`, `iotaB`, `hrow`, `hgame`; and the four
categories' cover and pairwise disjointness, which are `09:1569--1570` itself.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
two fixed reals, not an existential.  It is not vacuous either: the frozen
budget lines force `L_1 + L_2 + L_3 <= 3 eta_R/8`, so a `D_4` of density `0`
would leave retention `>= 1 - 3 eta_R/8 > 1 - eta_R`, which the banked hardness
step refutes -- see `fourth_category_cannot_vanish` below.

General in the five carriers, in the protocol, in both index types, in the
matrix and in both tolerances. -/
theorem ownerLeakage_gt_of_fourCategories
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] [DecidableEq Rw]
    {C : ℕ} (S : RoutedSystem Pr Coord ιc Vn rw' A0) (Pv : Vn → ιc → ℝ)
    {etaR : ℝ} {j : ιc} (hj : j ∈ goodDonors S Pv etaR)
    (hC : 3 ≤ C) (hcost : Pr.cost ≤ C + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (Nmat : Rw → Cl → Bool) {ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    {retained D₁ D₂ D₃ D₄ : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat etaR ηC C)
    (hcols : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaA : {a // a ∈ (ownerRect retained cols).1} → Xa)
    (iotaB : {c // c ∈ (ownerRect retained cols).2} → Yb)
    (hrow : ∀ a, RouteRows Pr (S.node (S.owner j)) (iotaA a))
    (hgame : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2 a b = gamb (iotaA a) (iotaB b))
    (hcover : (Finset.univ : Finset Rw) \ retained = D₁ ∪ D₂ ∪ D₃ ∪ D₄)
    (h₁₂ : Disjoint D₁ D₂) (h₁₃ : Disjoint D₁ D₃) (h₁₄ : Disjoint D₁ D₄)
    (h₂₃ : Disjoint D₂ D₃) (h₂₄ : Disjoint D₂ D₄) (h₃₄ : Disjoint D₃ D₄)
    (hetaR : 0 < etaR)
    (h₁ : rowDensity D₁ ≤ etaR / 16) (h₂ : rowDensity D₂ < etaR / 16)
    (h₃ : rowDensity D₃ ≤ etaR / 4)
    -- `09:1580--1581` read against `09:1566--1568`: the fourth category *is*
    -- the leakage `sum_{T != own(j)} m_{j,T}`
    (hfourth : rowDensity D₄ = ownerLeakage S Pv j) :
    etaR / 2 < ownerLeakage S Pv j := by
  rw [← hfourth]
  exact massLeavesOwner_of_fourCategories S hC hcost
    (goodDonor_owner_not_firstBob S Pv etaR hj) hcomp Nmat hRw hdense hcols iotaA iotaB
    hrow hgame hcover h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hetaR h₁ h₂ h₃

end LossTable

/-! ## §2  `09:1700--1701` with the loss table TRAVELLED

"Together with `eq:wrapper-mass-leaves-owner`, this says that every good donor
sends more than `eta_R/4` protected mass to exceptional final nodes."

`OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_derived` banked exactly
this sentence: the owner-to-owner transfer family of `09:1643--1689` and
`eq:wrapper-good-to-good` (`09:1692--1699`) are produced inside it, and its only
remaining analytic input is the `hleaves` slot -- `eq:wrapper-mass-leaves-owner`
itself.  Until now that slot was a hypothesis of every consumer.

This section fills it from Section 1.  The frozen argument's two halves are then
joined in one proof term for the first time: the four-category table produces the
leakage bound, and the transfer bound subtracts the good-owner part from it.
Nothing is restated -- the transfer family, `eq:wrapper-owner-threshold`,
`eq:wrapper-baseline-deficit-sum`, `eq:wrapper-owner-gates` and the constant
`3 eta_R/16` all stay inside the banked endpoint. -/

section Travelled

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
  [Fintype Rone] [DecidableEq Rone]

/-- **`09:1700--1701`, with `eq:wrapper-mass-leaves-owner` DISCHARGED.**

The banked `goodDonor_mass_to_exceptional_derived` with its `hleaves` binder
**removed**: it is supplied by `ownerLeakage_gt_of_fourCategories`, i.e. by the
frozen four-category table of `09:1571--1584` at the owner of the same good
donor `j`, at the same protocol, the same completed computation `hcomp`, the
same target `C = terminalTarget bcap r_2 r_3` and the same tolerance `eta_R`.

*What is derived rather than assumed.*  `hleaves`; and inside the loss table, the
owner's stopping rule (`09:1550`, from `j in J_good`) and the hardness step
(`09:1609--1610`, inside the banked endpoint).

*What is still a binder.*  The realization telescope of the transfer family
(`huniq`, `hgates`, `hcard`, `hdeficit`, `hstateOf`, `hTTS`, `hseed`, `hfixed`,
`hcalls`, `iotaA`, `iotaB`, `hrow`, `hgame`, `hsplit`) inherited **verbatim**,
plus the loss table's own data: the deletion-stable Stage-4 conclusion `hdense`
at the owner's copy of `N`, the owner rectangle's column density `hcolsL` and
sections `iotaLA`/`iotaLB`/`hrowL`/`hgameL`, the four categories with their
cover and pairwise disjointness (`09:1569--1570`), the three frozen budget lines
`h1`/`h2`/`h3` (`09:1575`, `09:1577`, `09:1579`) and the frozen reading
`hfourth` (`09:1580--1581`).  **No hypothesis is added to the banked endpoint and
none is weakened; full-bundle satisfiability is not claimed.**

*Why the trivial witness fails.*  The conclusion is a strict inequality between
fixed reals, not an existential, and it is not vacuous: `exceptionalMass` is a
sum over the derived exceptional set of `09:1553`, which the banked
`OwnerMassTransfer.exceptionalMass_of_empty` evaluates to `0` when that set is
empty -- so the conclusion at a positive `eta_R` already forces `e_T > 0`, which
is exactly what Section 3 extracts.

General in all six carriers, in the protocol, in both index types and in every
width. -/
theorem goodDonor_mass_to_exceptional_of_lossTable
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT bcap r₃ bT Lh vmax qw : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (eps2 epsProd xT yy : ℝ)
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} {j : ιc}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors S Pv etaR) (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates qw W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ (qw : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR, ordinaryDeficit XZ (donorCoord S i) RG
      ≤ etaR / (8 * g))
    (hstateOf : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ Rf : Finset Rw,
      (Rf = RSig ∨ Rf = RD) →
      ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ ((streamRows XZ (donorCoord S j) Rf).card : ℝ) / (Rf.card : ℝ) →
      TwoStreamState (scaleAlignWidth rq) s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
        omg (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ)))
    -- `09:1566--1615`: the four-category loss table at the owner of `j`
    {ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    {retained D₁ D₂ D₃ D₄ : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat etaR ηC
      (TerminalTwoStream.terminalTarget bcap W.r₂ r₃))
    (hcolsL : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaLA : {a // a ∈ (ownerRect retained cols).1} → Xa)
    (iotaLB : {c // c ∈ (ownerRect retained cols).2} → Yb)
    (hrowL : ∀ a, RouteRows Pr (S.node (S.owner j)) (iotaLA a))
    (hgameL : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2 a b = gamb (iotaLA a) (iotaLB b))
    (hcoverL : (Finset.univ : Finset Rw) \ retained = D₁ ∪ D₂ ∪ D₃ ∪ D₄)
    (h₁₂ : Disjoint D₁ D₂) (h₁₃ : Disjoint D₁ D₃) (h₁₄ : Disjoint D₁ D₄)
    (h₂₃ : Disjoint D₂ D₃) (h₂₄ : Disjoint D₂ D₄) (h₃₄ : Disjoint D₃ D₄)
    (h₁ : rowDensity D₁ ≤ etaR / 16) (h₂ : rowDensity D₂ < etaR / 16)
    (h₃ : rowDensity D₃ ≤ etaR / 4)
    (hfourth : rowDensity D₄ = ownerLeakage S Pv j) :
    etaR / 4 < exceptionalMass S Pv etaR j :=
  goodDonor_mass_to_exceptional_derived W rq s mT dT bcap r₃ bT Lh vmax qw Nmat Mmat
    cFam Stwo RG RSig RD omg tup YT zeta XZ YZ eps2 epsProd xT yy S Pv huniq hj hetaR hg
    hgates hcard hdeficit hstateOf hTTS hs hxTd hyy hseed hfixed hcalls hC hcost hcomp
    iotaA iotaB hrow hgame hsplit
    (ownerLeakage_gt_of_fourCategories S Pv hj hC hcost hcomp Nmat hRw hdense hcolsL
      iotaLA iotaLB hrowL hgameL hcoverL h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hetaR h₁ h₂ h₃ hfourth)

end Travelled

/-! ## §3  `09:1702`: the vanishing case, executed through the banked iff

"If `e_T = 0`, this is already a contradiction."

The predecessor banked the iff `exceptionalFinal = empty` iff every final node is
owned by a good donor (`WrapperExceptionalCount.exceptionalFinal_eq_empty_iff`,
from the set difference of `09:1553`), and banked separately that a good donor's
positive exceptional mass makes the exceptional set inhabited
(`OwnerFamilyToPigeonhole.exceptionalFinal_nonempty_of_goodDonor`, `09:1701`).
Neither consumed the other.  This section joins them: at a good donor meeting
`09:1701`, the *ownership* form of `e_T = 0` is refuted, which is the frozen
sentence in the form the classification of `09:1553` states it.

Kept separate from Section 2's telescope on purpose: `09:1702` is a statement
about the endpoint `eta_R/4 < exceptionalMass` and nothing else, so it is stated
against that endpoint and fired from Section 2 only at the point of use. -/

section EmptyCase

variable {Xa Yb Zc : Type*} {Coord ιc Vn : Type*} {Pr : Protocol Xa Yb Zc} {rw' A0 : ℕ}
variable [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]

/-- **`09:1702` in the ownership form of `09:1553`.**

From the `09:1700--1701` endpoint at one good donor: it is **not** the case that
every final node is owned by a good donor.  Equivalently, by the banked iff, the
exceptional set of `09:1553` is not empty -- which is the frozen "If `e_T = 0`,
this is already a contradiction" stated against the classification that defines
`e_T`.  General. -/
theorem not_finalNodes_subset_goodOwners (S : RoutedSystem Pr Coord ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) {etaR : ℝ} {j : ιc} (hetaR : 0 < etaR)
    (hexc : etaR / 4 < exceptionalMass S Pv etaR j) :
    ¬ (S.toWrapperFrontier.finalNodes ⊆ (goodDonors S Pv etaR).image S.owner) := by
  intro hsub
  have hempty : exceptionalFinal S Pv etaR = ∅ :=
    (WrapperExceptionalCount.exceptionalFinal_eq_empty_iff S Pv etaR).mpr hsub
  have hne := exceptionalFinal_nonempty_of_goodDonor S Pv hetaR hexc
  rw [hempty] at hne
  exact absurd hne (Finset.not_nonempty_empty)

/-- **`09:1702` in the counting form, as the frozen contradiction.**

"If `e_T = 0`, this is already a contradiction": the hypothesis `e_T = 0` and the
`09:1701` endpoint at one good donor are jointly inconsistent.  This is the
literal frozen sentence; `09:1704`'s "Assume then that `e_T > 0`" is its
contrapositive and is the banked
`OwnerFamilyToPigeonhole.exceptionalCount_pos_of_goodDonor`, consumed by pin and
not restated.  General. -/
theorem eT_zero_is_contradictory (S : RoutedSystem Pr Coord ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) {etaR : ℝ} {j : ιc} (hetaR : 0 < etaR)
    (hexc : etaR / 4 < exceptionalMass S Pv etaR j)
    (heT : (exceptionalFinal S Pv etaR).card = 0) : False := by
  have hpos := exceptionalCount_pos_of_goodDonor S Pv hetaR hexc
  omega

end EmptyCase

/-! ### §3b  Sections 1--3 in one proof term

The seam between the loss table and the vanishing case, **travelled**: the frozen
`09:1702` is reached from the four-category table alone, with every intermediate
endpoint produced inside the proof rather than assumed. -/

section Travelled3b

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
  [Fintype Rone] [DecidableEq Rone]

/-- **`09:1566--1702` in one proof term: the loss table travelled all the way to
the vanishing case.**

The seam test for this tranche.  From the four-category table of `09:1571--1584`
at the owner of one good donor, and nothing else new, the frozen `09:1702` --
"If `e_T = 0`, this is already a contradiction" -- is produced in **both** its
forms: the exceptional count of `09:1553` is positive, and the final nodes are
not all owned by good donors.  No intermediate endpoint is re-introduced as a
binder on the way: `eq:wrapper-mass-leaves-owner` (Section 1),
`eq:wrapper-good-to-good` and `09:1700--1701` (Section 2) and the banked
`e_T = 0` iff (Section 3) are all consumed inside this proof term.

This is what makes Sections 1--3 *compose* rather than merely coexist: the
predecessor tranches proved each link, and the `hleaves` and `hexc` slots joining
them were hypotheses of every consumer.

*What is still a binder.*  Exactly the union of Sections 1 and 2, inherited
verbatim; nothing is added and nothing is weakened.  **Full-bundle satisfiability
is not claimed**, and `09:1704`'s branch is not entered here -- Section 4b
carries `e_T > 0` as the frozen branch assumption it is, because fusing this
telescope into that one would merge two frozen cases of one construction.

*Why the trivial witness fails.*  The conclusion is a conjunction of a strict
natural-number inequality and a negation, neither of which is an existential; and
the negated statement is genuinely satisfiable in general -- with
`goodDonors = empty` the owner image is empty, so the inclusion holds **iff** the
final-node set is empty, and this declaration's own `hj : j in goodDonors` rules
that configuration out, so the conclusion is a real constraint on the frontier.

General in all six carriers and every width. -/
theorem eT_pos_and_not_goodOwned_of_lossTable
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {rw' A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT bcap r₃ bT Lh vmax qw : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (eps2 epsProd xT yy : ℝ)
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} {j : ιc}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hj : j ∈ goodDonors S Pv etaR) (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates qw W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ (qw : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR, ordinaryDeficit XZ (donorCoord S i) RG
      ≤ etaR / (8 * g))
    (hstateOf : ∀ i ∈ (goodDonors S Pv etaR).erase j, ∀ Rf : Finset Rw,
      (Rf = RSig ∨ Rf = RD) →
      ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ ((streamRows XZ (donorCoord S j) Rf).card : ℝ) / (Rf.card : ℝ) →
      TwoStreamState (scaleAlignWidth rq) s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
        omg (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hTTS : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rw' - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hsplit : ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁ (ordinaryDeficit XZ (donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (donorCoord S j) RSig).card : ℝ) / (RSig.card : ℝ))
          + muP * (((streamRows XZ (donorCoord S j) RD).card : ℝ) / (RD.card : ℝ)))
    -- `09:1566--1615`: the four-category loss table at the owner of `j`
    {ηC : ℝ} (hRw : 0 < Fintype.card Rw)
    {retained D₁ D₂ D₃ D₄ : Finset Rw} {cols : Finset (Fin 1 → Cl)}
    (hdense : DenseStageFourConclusion Nmat etaR ηC
      (TerminalTwoStream.terminalTarget bcap W.r₂ r₃))
    (hcolsL : ((Fintype.card Cl : ℝ) ^ 1) * (1 - ηC) ≤ (cols.card : ℝ))
    (iotaLA : {a // a ∈ (ownerRect retained cols).1} → Xa)
    (iotaLB : {c // c ∈ (ownerRect retained cols).2} → Yb)
    (hrowL : ∀ a, RouteRows Pr (S.node (S.owner j)) (iotaLA a))
    (hgameL : ∀ a b, subgame (interlaceFun Nmat 1) (ownerRect retained cols).1
      (ownerRect retained cols).2 a b = gamb (iotaLA a) (iotaLB b))
    (hcoverL : (Finset.univ : Finset Rw) \ retained = D₁ ∪ D₂ ∪ D₃ ∪ D₄)
    (h₁₂ : Disjoint D₁ D₂) (h₁₃ : Disjoint D₁ D₃) (h₁₄ : Disjoint D₁ D₄)
    (h₂₃ : Disjoint D₂ D₃) (h₂₄ : Disjoint D₂ D₄) (h₃₄ : Disjoint D₃ D₄)
    (h₁ : rowDensity D₁ ≤ etaR / 16) (h₂ : rowDensity D₂ < etaR / 16)
    (h₃ : rowDensity D₃ ≤ etaR / 4)
    (hfourth : rowDensity D₄ = ownerLeakage S Pv j) :
    0 < (exceptionalFinal S Pv etaR).card
      ∧ ¬ (S.toWrapperFrontier.finalNodes ⊆ (goodDonors S Pv etaR).image S.owner) := by
  have hexc := goodDonor_mass_to_exceptional_of_lossTable W rq s mT dT bcap r₃ bT Lh vmax
    qw Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ eps2 epsProd xT yy S Pv huniq
    hj hetaR hg hgates hcard hdeficit hstateOf hTTS hs hxTd hyy hseed hfixed hcalls hC
    hcost hcomp iotaA iotaB hrow hgame hsplit hRw hdense hcolsL iotaLA iotaLB hrowL hgameL
    hcoverL h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ h₁ h₂ h₃ hfourth
  exact ⟨exceptionalCount_pos_of_goodDonor S Pv hetaR hexc,
    not_finalNodes_subset_goodOwners S Pv hetaR hexc⟩

end Travelled3b


/-! ## §4a  `eq:wrapper-terminal-donor-gate` (`09:1732--1741`)

"The first gate in `eq:terminal-wrapper-gates` gives `E_T <= q/8`, whereas its
second gate and `u_don <= u_term` give the other inequality below.  Consequently
the proof has `|J_good| > q/2`, `q/(4 E_T) > u_don B_theta`."

The banked `WrapperMassRedistribution.wrapperTerminalDonorGate` is the frozen
arithmetic over five free reals.  This section is its consumer, with **every**
analytic input of `09:1727--1734` discharged:

* `E_T >= 1` (`09:1727--1731`, "Thus the division by `E_T` below is legal") is
  `one_le_ET_of_e0Max_pos` at `e_0^max >= 1`;
* `B_theta >= 1` (`09:1380`) is `WrapperProtectedEarly.one_le_Btheta` at a
  positive retained-column density;
* `u_don <= u_term` (`09:1715--1716`) is `uDon_le_uTerm`, itself the frozen
  observation that the two are the *same* least-power-of-two search run at two
  densities;
* the two gate rows are projected out of the banked
  `ParameterSchedule.terminalWrapperGates`, the paper's own three-row `Prop`.

`u_don` is the accessor `ParameterSchedule.uTerm sv (deltaZero etaR eT)`: this is
`09:1717--1718`'s defining display -- "the least power of two satisfying
`u_don delta_0 >= 8s`" -- formalized as the paper's closed form, at the paper's
own `delta_0` of `eq:wrapper-terminal-density`.  No numeral is assigned to
`u_don`, `u_term`, `E_T`, `E_B`, `B_theta`, `s`, `t_ref` or `q`. -/

section TerminalGate

/-- **`eq:wrapper-terminal-donor-gate` (`09:1736--1741`), both clauses.**

`|J_good| > q/2` and `u_don B_theta < q/(4 E_T)`, at the schedule's own `E_T`,
`u_term` and `delta_term` and at the paper's `u_don`.

*What is derived rather than assumed.*  `0 < E_T`, `0 < B_theta`, both gate rows
and `u_don <= u_term`; only `hjgood` (`09:1718--1726`, itself a banked theorem),
the gate system, `e_0^max >= 1`, `0 < theta`, `0 < eta_R` and `09:1704`'s own
branch assumption `0 < e_T` with its majorant `e_T <= E_T` remain hypotheses.

*Why the trivial witness fails.*  The conclusion is a conjunction of two strict
inequalities between fixed reals, not an existential, and neither clause is
free: `q - E_T <= |J_good|` alone does **not** give `q/2 < |J_good|`
(`gate_rows_are_load_bearing` below refutes it at `q = 2`, `E_T = 1`), and the
second clause is false outright at `E_T = 0` (`second_clause_fails_at_zero_ET`).

General in every schedule quantity. -/
theorem terminalDonorGate_of_gates
    {q e0m EBv sv trefv eT : ℕ} {θ etaR jgood : ℝ}
    (hetaR : 0 < etaR) (hθ : 0 < θ) (he0m : 1 ≤ e0m)
    (heTpos : 0 < eT) (heTle : eT ≤ ParameterSchedule.ET e0m EBv)
    (hgates : ParameterSchedule.terminalWrapperGates q
      (ParameterSchedule.ET e0m EBv)
      (ParameterSchedule.uTerm sv
        (ParameterSchedule.deltaTerm etaR (ParameterSchedule.ET e0m EBv)))
      (Btheta θ) trefv)
    (hjgood : (q : ℝ) - ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ) ≤ jgood) :
    (q : ℝ) / 2 < jgood
      ∧ ((ParameterSchedule.uTerm sv (deltaZero etaR eT) : ℕ) : ℝ) * ((Btheta θ : ℕ) : ℝ)
          < (q : ℝ) / (4 * ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ)) := by
  obtain ⟨hrow1, hrow2, -⟩ := hgates
  -- `09:1727--1731`: `E_T >= 1`, so the division by `E_T` is legal
  have hET1 : 1 ≤ ParameterSchedule.ET e0m EBv := one_le_ET_of_e0Max_pos he0m
  have hETpos : (0 : ℝ) < ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ) := by
    exact_mod_cast hET1
  -- `09:1380`: `B_theta >= 1` at a legal retained-column density
  have hBt1 : 1 ≤ Btheta θ := one_le_Btheta hθ
  have hBtpos : (0 : ℝ) < ((Btheta θ : ℕ) : ℝ) := by exact_mod_cast hBt1
  -- first row of `eq:terminal-wrapper-gates`
  have hgate1 : 8 * ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ) ≤ (q : ℝ) := by
    have hmax : ParameterSchedule.ET e0m EBv ≤ max 1 (ParameterSchedule.ET e0m EBv) :=
      le_max_right _ _
    have : 8 * ParameterSchedule.ET e0m EBv ≤ q := le_trans (by omega) hrow1
    exact_mod_cast this
  -- second row of `eq:terminal-wrapper-gates`
  have hgate2 : 4 * ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ)
      * ((ParameterSchedule.uTerm sv
          (ParameterSchedule.deltaTerm etaR (ParameterSchedule.ET e0m EBv)) : ℕ) : ℝ)
      * ((Btheta θ : ℕ) : ℝ) < (q : ℝ) := by
    have := hrow2
    exact_mod_cast this
  -- `09:1715--1716`: `u_don <= u_term`, derived
  have hdpos : 0 < ParameterSchedule.deltaTerm etaR (ParameterSchedule.ET e0m EBv) :=
    ParameterSchedule.deltaTerm_pos hetaR
  have huT : ((ParameterSchedule.uTerm sv (deltaZero etaR eT) : ℕ) : ℝ)
      ≤ ((ParameterSchedule.uTerm sv
          (ParameterSchedule.deltaTerm etaR (ParameterSchedule.ET e0m EBv)) : ℕ) : ℝ) := by
    have := uDon_le_uTerm (s := sv) (le_of_lt hetaR) heTpos heTle hdpos
    exact_mod_cast this
  exact wrapperTerminalDonorGate hETpos hBtpos hgate1 hgate2 huT hjgood

end TerminalGate

/-! ## §4b  `eq:wrapper-terminal-donor-gate` at the canonical routed system

Section 4a fired at `FrontierIndexing.canonicalSystem`, with **both** of its
wrapper-side inputs discharged rather than assumed:

* `hjgood` is `09:1718--1726` at the canonical system, i.e. the banked
  `WrapperExceptionalCount.canonical_goodDonorCount_ge_q_sub_ET` -- the predecessor
  tranche's endpoint, which that tranche deliberately did **not** feed to the
  banked `wrapperTerminalDonorGate` consumer.  This is that firing;
* `e_T <= E_T` (`09:1715--1716`, "The parameter schedule computes deterministic
  bounds `e_T <= E_T`") is **derived** here, from
  `WrapperExceptionalCount.canonical_wrapperExceptionalCount`
  (`eq:wrapper-exceptional-count`) chained with
  `BobHeavyDonorCount.canonical_wrapperBobHeavyCount`
  (`eq:wrapper-bob-heavy-count`) through
  `BobHeavyDonorCount.bobHeavyCount_le_EB`, `09:452--453`'s `e_0 <= e_0^max` and
  `Nat.le_ceil` at the preserved ceiling of `06:723`.  Neither `hcount` nor
  `hclean` is re-hoisted: both are obtained in-proof, exactly as the predecessor
  tranches left them.

The two `vartheta` twins (`09:1268` and `06:718`) are crossed by the two banked
evaluations `one_sub_vartheta` and `ParameterSchedule.one_sub_vartheta`, which
give `1 - vartheta = 7/16` on both sides; neither is re-declared.

`s` is the frozen `2^{r_3}` fixed at `09:1038` ("put `r_3 = log_2 s`"), the
symbol `eq:wrapper-bob-heavy-count` (`09:1543--1545`) prints on its own
right-hand side, `B_theta = WrapperProtectedEarly.Btheta theta` and
`L_q = WrapperProtectedEarly.Lq q` likewise, and `E_B`, `E_T`, `delta_term`,
`u_term` and `u_don` are the banked `ParameterSchedule` accessors evaluated
through that chain.  **No numeral is assigned to any schedule quantity.** -/

section CanonicalGate

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-terminal-donor-gate` (`09:1736--1741`) at the canonical system.**

`|J_good| > q/2` and `u_don B_theta < q/(4 E_T)`, at
`FrontierIndexing.canonicalSystem`, with `|J_good|` the derived good-donor count
of `09:1548`, `e_T` the derived exceptional count of `09:1553`, and `u_don` the
`09:1717--1718` least-power-of-two search read at `eq:wrapper-terminal-density`'s
`delta_0`.

*What is derived rather than assumed.*  `hjgood` (`09:1718--1726`), `e_T <= E_T`
(`09:1715`), `E_T >= 1` (`09:1727--1731`), `B_theta >= 1` (`09:1380`),
`u_don <= u_term` (`09:1715--1716`), and both rows of the gate that the frozen
justification `09:1732--1734` names.

*What is still a binder.*  The predecessor bundle inherited **verbatim** --
`hLocExCC`/`hLocExEP` (**EXPANDER-001**), `hfinal`, `halleged`, `hcost`, `hres`,
`hinj`, `hhost`, `he0`, and the analytic members of the protected-closure bundle
-- together with `residual`/`hresidual`/`hladder` (`lem:certified-row-ladder`,
`09:1334--1338`, needed for the exceptional count), the gate system `hgates`
(`eq:terminal-wrapper-gates`, whose eventual validity `06:744--747` defers to the
effective-cutoff audit), `he0m` (`09:1730`, `e_0^max >= 1`) and `heTpos`, which is
`09:1704`'s own branch assumption "Assume then that `e_T > 0`".  **No hypothesis
is added to any banked endpoint and none is weakened.  Full-bundle satisfiability
is not claimed.**

*Why `heTpos` is a binder and not a conjunct.*  `09:1702` and `09:1704` are two
frozen **cases** of one construction; Section 3 produces `e_T > 0` from the
`09:1701` endpoint at one good donor, and conjoining that telescope with this one
would fuse the two cases into a single hypothesis bundle.  The schedule alone
does not give it -- see `majorant_does_not_give_positivity`.

*Why the trivial witness fails.*  The conclusion is a conjunction of two strict
inequalities between fixed reals, not an existential; `gate_rows_are_load_bearing`
refutes the first clause from `hjgood` alone, and `second_clause_fails_at_zero_ET`
refutes the second at `E_T = 0`.

*No route completion.*  `eq:wrapper-u-dense` is neither stated nor implied;
`09:1742--1781` remains open.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet `Yc`,
the Alice carrier `X`, and in every width and schedule quantity. -/
theorem canonical_terminalDonorGate {RwN : Type*} [Fintype RwN]
    {r bT kref tcert e0m : ℕ} {E0 : Finset (Fin q)} {xU θ etaR : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
    {k₂ b₁ r₂ r₃ bcap tcertEP selCard rowsPerBlock : ℕ} {lamT epsProd : ℝ}
    (isRestrEP : Protocol X (Fin q → Yc) Bool → ℕ → ℕ → ℝ → Prop)
    (Scol : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Finset (Fin q → Yc))
    (YT : Finset Yc)
    (Pv : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    (donor : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Fin q)
    (d₀ d₁ : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Fin q → ℝ)
    (ell : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℕ)
    (bsel : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Bool)
    (hdepth : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ((canonicalSystem hcomp hR).node v).length + ell v = r)
    (hinj : ∀ i ∈ (canonicalSystem hcomp hR).cleanFinal,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal, donor i = donor j → i = j)
    (hres : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j)))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1
      ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1cc : (3 / 5 : ℝ) ^ (2 ^ kref)
      ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + r)))
    (hE2cc : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + kref)))
    (hLocExCC :
      ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (Sblk : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ Sblk T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1
        ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref)
        ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1) + (r - v.val.length)
        ≤ (descend P (v.val ++ [c])).cost)
    {Scover : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scover →
      (E0 ∩ K).Nonempty)
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
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scover,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
    (hfinal : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ finalWeight (certOpt v))
    (hqpos : 0 < q)
    (hk₂ : 4 ≤ k₂)
    (hk₂le : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      k₂ ≤ r₃ + ell v + r₂)
    (hbcap : 2 ≤ bcap)
    (hd₀0 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, 0 ≤ d₀ v j)
    (hd₀1 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, d₀ v j ≤ 1)
    (hd₁0 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, 0 ≤ d₁ v j)
    (hd₁1 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, d₁ v j ≤ 1)
    (hGateEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ((2 : ℝ) ^ (r₃ + ell v + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hYT0 : 0 < YT.card)
    (hSep : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      θ * (Fintype.card Yc : ℝ) ^ q ≤ ((Scol v).card : ℝ))
    (hYT : lamT * (Fintype.card Yc : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (u : ℕ) (J : Finset (Fin q)), J.card = u →
        ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Yc)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ (Scol v))
    (hBlocks : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < xTdepth bT) (hx1 : xTdepth bT ≤ 1)
    (htx : ((2 : ℝ) ^ k₂) * xTdepth bT ≤ 1)
    (hMne : 1 ≤ Fintype.card RwN)
    (hbaseEP : bcap ≤ NPCC.LambdaGE Nmat 1 (xTdepth bT) (3 / 5))
    (htcertEP : tcertEP ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1ep : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e Rex : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        Rex + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((Rex : ℝ) + k₂)))) / (1 + epsProd))
    (hE2ep : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ⌈((2 : ℝ) ^ (r₃ + ell v + r₂ - k₂)) * 2 ^ k₂ * xTdepth bT
          * (Fintype.card RwN)⌉₊ ≤ rowsPerBlock)
    -- `09:1499--1504`, the round-`r4` selection binder at every first-Bob node
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- The extraction re-gate is forwarded verbatim from the banked
    -- `WrapperProtectedEarly.earlyProtectedClosure`: the `09:1499` selection fires
    -- only on `ExtractionOutput`, the deliverable of `09:1458--1471`, so the
    -- density chain stays load-bearing through this application too.
    (hSelectEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      earlyMassCoeff θ q (2 ^ r₃)
          * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)
          ≤ donorMass Pv ((canonicalSystem hcomp hR).cleanFinal) v →
        ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
          ExtractionOutput (Scol v) YT e →
          isRestrEP (descendStep (descend P ((canonicalSystem hcomp hR).node v)) (bsel v))
            ((2 : ℕ) ^ (r₃ + ell v + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
              (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocExEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e Rex Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ)
        (w : Protocol X (Fin q → Yc) Bool),
        ExtensionCallThree k₂ Rex Rloc b₁ e r₂ r₃ (ell v) dcls colDens →
        1 ≤ Fintype.card RwN → 2 ≤ bcap →
        0 < xTdepth bT → xTdepth bT ≤ 1 →
        bcap ≤ NPCC.LambdaGE Nmat 1 (xTdepth bT) (3 / 5) →
        tcertEP ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * xTdepth bT ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ Rex →
        (2 : ℕ) ^ Rex * 2 ^ k₂ = 2 ^ (Rex + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((Rex : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        isRestrEP w blocks rowsEach colDens →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * xTdepth bT * (Fintype.card RwN)⌉₊ ≤ rowsEach →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ w.cost)
    (hne : ((canonicalSystem hcomp hR).toWrapperFrontier.bobNodes).Nonempty)
    (hetaR : 0 < etaR)
    -- `09:452--453`: the construction records `e_0 <= e_0^max`
    (he0 : (E0.card : ℝ) ≤ (e0m : ℝ))
    -- `09:1346--1347`: a clean-classified final node hosts a clean certificate
    (hhost : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.cleanNodes certOpt,
      ∃ i ∈ (canonicalSystem hcomp hR).cleanFinal,
        (canonicalSystem hcomp hR).owner i = v)
    -- `lem:certified-row-ladder` (`09:1334--1338`), the route to owner uniqueness
    (residual : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℕ)
    (hresidual : ∀ i j, residual i j
      ≤ (descend P ((canonicalSystem hcomp hR).node
          ((canonicalSystem hcomp hR).owner i))).cost)
    (hladder : ∀ i ∈ (canonicalSystem hcomp hR).cleanFinal,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal,
      (canonicalSystem hcomp hR).owner i = (canonicalSystem hcomp hR).owner j →
      ((canonicalSystem hcomp hR).cert i).coord
          ≠ ((canonicalSystem hcomp hR).cert j).coord →
      TerminalTwoStream.terminalTarget bcap r₂ r₃ ≤ residual i j)
    -- `09:1727--1731`: the construction records `e_0^max >= 1`
    (he0m : 1 ≤ e0m)
    -- `09:1704`: "Assume then that `e_T > 0`", the frozen branch assumption
    (heTpos : 0 < (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card)
    -- `eq:terminal-wrapper-gates` (`06:738--743`), all three rows, at the
    -- schedule's own `E_T` and `u_term`
    {trefv : ℕ}
    (hgates : ParameterSchedule.terminalWrapperGates q
      (ParameterSchedule.ET e0m
        (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR))
      (ParameterSchedule.uTerm (2 ^ r₃)
        (ParameterSchedule.deltaTerm etaR
          (ParameterSchedule.ET e0m
            (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR))))
      (Btheta θ) trefv) :
    (q : ℝ) / 2 < ((goodDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ∧ ((ParameterSchedule.uTerm (2 ^ r₃)
            (deltaZero etaR
              (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card) : ℕ) : ℝ)
          * ((Btheta θ : ℕ) : ℝ)
        < (q : ℝ) / (4 * ((ParameterSchedule.ET e0m
            (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) : ℕ) : ℝ)) := by
  -- `eq:wrapper-bob-heavy-count` at the canonical system, then `06:732--733`
  have hcount := canonical_wrapperBobHeavyCount Nmat Gmat ιR hsub halleged hcomp hR certOpt
    isRestrEP Scol YT Pv donor d₀ d₁ ell bsel hdepth hinj hres hC hcost hq hmem hk hq4 hX hYc
    hθ0 hθ1
    hgate hbase htcert hE1cc hE2cc hLocExCC hcover B hB plc hblock hplace hfinal hqpos hk₂
    hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0 hSep hYT hgap hQuery hBlocks hx0 hx1 htx
    hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep hrows hSelectEP hLocExEP hne hetaR
  have heB : (bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card
      ≤ ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR :=
    bobHeavyCount_le_EB hetaR he0 hcount
  have heBR : ((bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ≤ ((ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR : ℕ) : ℝ) := by
    exact_mod_cast heB
  -- `eq:wrapper-exceptional-count` at the canonical system
  have hexc := WrapperExceptionalCount.canonical_wrapperExceptionalCount (etaR := etaR)
    Nmat Gmat ιR hsub halleged hcomp hR certOpt Pv hq hmem hk hq4 hX hYc hθ0 hθ1 hC hgate
    hbase htcert hE1cc hE2cc hcost hLocExCC hcover B hB plc hblock hplace hfinal
    residual hresidual hladder hhost
  -- `09:1715`: `e_T <= E_T`, derived through the two `vartheta` twins
  have hv : (1 : ℝ) - DenseWrapperFrontier.vartheta = 7 / 16 :=
    DenseWrapperFrontier.one_sub_vartheta
  have hvP : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
    ParameterSchedule.one_sub_vartheta
  have heTle : (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card
      ≤ ParameterSchedule.ET e0m
          (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) := by
    have h1 := le_trans hexc.1 hexc.2
    have e1 : (E0.card : ℝ) / (1 - DenseWrapperFrontier.vartheta)
        = 16 / 7 * (E0.card : ℝ) := by rw [hv]; ring
    have e2 : (e0m : ℝ) / (1 - ParameterSchedule.vartheta)
        = 16 / 7 * (e0m : ℝ) := by rw [hvP]; ring
    rw [e1] at h1
    have hceil : 16 / 7 * (e0m : ℝ)
        ≤ ((⌈(e0m : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ : ℕ) : ℝ) := by
      rw [← e2]
      exact Nat.le_ceil _
    have hchain : (((exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card : ℕ) : ℝ)
        ≤ ((ParameterSchedule.ET e0m
            (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) : ℕ) : ℝ) := by
      rw [ParameterSchedule.ET, Nat.cast_add]
      linarith
    exact_mod_cast hchain
  -- Section 4a, with `hjgood` the banked `09:1718--1726` closure
  exact terminalDonorGate_of_gates (sv := 2 ^ r₃) hetaR hθ0 he0m heTpos heTle hgates
    (WrapperExceptionalCount.canonical_goodDonorCount_ge_q_sub_ET Nmat Gmat ιR hsub
      halleged hcomp hR certOpt isRestrEP Scol YT Pv donor d₀ d₁ ell bsel hdepth hinj hres hC hcost
      hq hmem hk hq4 hX hYc hθ0 hθ1 hgate hbase htcert hE1cc hE2cc hLocExCC hcover B hB
      plc hblock hplace hfinal hqpos hk₂ hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0 hSep
      hYT hgap hQuery hBlocks hx0 hx1 htx hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep
      hrows hSelectEP hLocExEP hne hetaR he0 hhost)

end CanonicalGate

/-! ## §5  Aux-lemma battery

Five general checks.  **Canonical inhabitation is INHERITED, REGISTERED and
DEFERRED** per the header: this module declares no new type, so it opens no new
obligation, and the inherited one cannot be discharged because the paper's own
instance of every statement above is a function of the alleged protocol of
`09:1187--1193`, which does not exist.  Nothing in this section evaluates a
schedule parameter or carries a numeral of its own. -/

section Battery

variable {Xa Yb Zc : Type*} {Coord ιc Vn : Type*} {Pr : Protocol Xa Yb Zc} {rw' A0 : ℕ}
variable [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]

/-- **Battery 1 (round trip on the banked `e_T = 0` iff).**

`09:1702` and `09:1704` are the two sides of one condition, and the banked iff of
`09:1553` makes them exactly complementary: `e_T > 0` holds precisely when the
final nodes are *not* all owned by good donors.  A one-way reading would let a
consumer of `09:1704` silently strengthen the branch it opens.  General. -/
theorem exceptionalCount_pos_iff_not_goodOwned (S : RoutedSystem Pr Coord ιc Vn rw' A0)
    (Pv : Vn → ιc → ℝ) (etaR : ℝ) :
    0 < (exceptionalFinal S Pv etaR).card
      ↔ ¬ (S.toWrapperFrontier.finalNodes ⊆ (goodDonors S Pv etaR).image S.owner) := by
  have hiff := WrapperExceptionalCount.exceptionalFinal_eq_empty_iff S Pv etaR
  constructor
  · intro hpos hsub
    have : (exceptionalFinal S Pv etaR).card = 0 := by rw [hiff.mpr hsub]; simp
    omega
  · intro hsub
    rcases Nat.eq_zero_or_pos (exceptionalFinal S Pv etaR).card with hz | hp
    · exact absurd (hiff.mp (Finset.card_eq_zero.mp hz)) hsub
    · exact hp

/-- **Battery 2 (the donor width grows with the exceptional count).**

`delta_0 = eta_R/(8 e_T mu_P)` shrinks as `e_T` grows
(`OwnerFamilyToPigeonhole.deltaZero_antitone_count`), and the least-power-of-two
search is antitone in its density (`WrapperMassRedistribution.uTerm_antitone`),
so a larger exceptional count forces a **wider** donor set.  This is exactly why
`09:1715` bounds `e_T` by the schedule's majorant `E_T` before comparing widths:
the comparison `u_don <= u_term` runs in the direction the majorant supplies, and
would be false in the other direction.  Positivity of the smaller count is
load-bearing -- at `e_T = 0` the frozen `delta_0` is Lean's total division by
zero.  General. -/
theorem uDon_mono_in_exceptionalCount {etaR : ℝ} (hetaR : 0 ≤ etaR) {s a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) :
    ParameterSchedule.uTerm s (deltaZero etaR a)
      ≤ ParameterSchedule.uTerm s (deltaZero etaR b) := by
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hd : 0 < deltaZero etaR b → deltaZero etaR b ≤ deltaZero etaR a :=
    fun _ => deltaZero_antitone_count hetaR ha hab
  rcases lt_or_eq_of_le hetaR with hpos | hzero
  · have hbd : 0 < deltaZero etaR b := deltaZero_pos hpos hbpos
    exact uTerm_antitone hbd (hd hbd)
  · have hz : deltaZero etaR a = 0 := by
      rw [deltaZero, ← hzero]; simp
    have hz' : deltaZero etaR b = 0 := by
      rw [deltaZero, ← hzero]; simp
    rw [hz, hz']

/-- **Battery 3 (the second gate clause weakens as the majorant grows).**

`q/(4 E_T)` is antitone in `E_T`, so a consumer holding only a weaker bound on
the exceptional count gets a weaker donor-width gate -- never a stronger one.
This is the check that replacing `e_T` by `E_T` in `09:1732--1734` is a legal
weakening of the frozen statement rather than a change of statement.  General. -/
theorem gate_bound_antitone_in_ET {q a b : ℝ} (hq : 0 ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    q / (4 * b) ≤ q / (4 * a) := by
  have h4a : (0 : ℝ) < 4 * a := by linarith
  have h4b : (0 : ℝ) < 4 * b := by linarith
  exact div_le_div_of_nonneg_left hq h4a (by linarith)

omit [Fintype ιc] [DecidableEq ιc] in
/-- **Battery 4 (the leakage sees only the final nodes off the owner).**

`sum_{T != own(j)} m_{j,T}` depends on the mass family only at final nodes other
than `own(j)`: two families agreeing there have the same leakage.  A congruence
check, and the reason `hfourth` of Section 1 is a statement about the *frozen*
index set rather than about the whole carrier.  General. -/
theorem ownerLeakage_congr (S : RoutedSystem Pr Coord ιc Vn rw' A0)
    {Pv Qv : Vn → ιc → ℝ} (j : ιc)
    (h : ∀ T ∈ S.toWrapperFrontier.finalNodes \ {S.owner j}, Pv T j = Qv T j) :
    ownerLeakage S Pv j = ownerLeakage S Qv j :=
  Finset.sum_congr rfl h

/-- **Battery 5 (the fourth category cannot vanish under the frozen budgets).**

If the fourth line of the table were empty, the first three budgets
(`eta_R/16`, `eta_R/16`, `eta_R/4`) would leave the owner retaining more than
`1 - 3 eta_R/8 > 1 - eta_R` of its rows, which `eq:wrapper-mass-leaves-owner`'s
own conclusion `eta_R/2 < L_4` forbids at a positive tolerance.  Stated as the
arithmetic it is, over abstract reals: the frozen endpoint is inconsistent with
a vanishing fourth category, so the table's last line really is where the mass
goes.  This is the non-triviality witness the statement pole of Section 1 asks
for.  General. -/
theorem fourth_category_cannot_vanish {etaR L₄ : ℝ} (hetaR : 0 < etaR)
    (hgt : etaR / 2 < L₄) : L₄ ≠ 0 := by
  intro h
  rw [h] at hgt
  linarith

end Battery

/-! ## §6  Statement poles and the gate-system consistency check

A green build sees none of this.  Each item shows that a hypothesis carried
above is load-bearing, or that a conclusion is not trivially available. -/

section Poles

/-- **Pole 1 (`hfourth` is load-bearing).**

Without the frozen reading of `09:1580--1581`, the banked conclusion about
`rowDensity D_4` says nothing about `ownerLeakage`: two reals can sit on opposite
sides of `eta_R/2`.  So Section 1's single binder is not decoration, and the join
it performs is a real step rather than a rename. -/
theorem fourth_reading_is_load_bearing :
    ∃ (etaR a b : ℝ), 0 < etaR ∧ etaR / 2 < a ∧ ¬ (etaR / 2 < b) :=
  ⟨1, 1, 0, by norm_num, by norm_num, by norm_num⟩

/-- **Pole 2 (the second gate clause fails at `E_T = 0`).**

`09:1727--1731` spends a paragraph establishing `E_T >= 1` precisely so that
"the division by `E_T` below is legal".  At `E_T = 0` Lean's total division makes
`q/(4 E_T)` zero, and the frozen clause `u_don B_theta < q/(4 E_T)` is false for
every positive width -- so `one_le_ET_of_e0Max_pos` is not bookkeeping, it is
what makes `eq:wrapper-terminal-donor-gate` a statement at all. -/
theorem second_clause_fails_at_zero_ET :
    ¬ ((1 : ℝ) * 1 < (8 : ℝ) / (4 * 0)) := by norm_num

/-- **Pole 3 (the gate rows are load-bearing).**

`09:1718--1726` alone gives `q - E_T <= |J_good|`, which does **not** give
`q/2 < |J_good|`: at `q = 2`, `E_T = 1`, `|J_good| = 1` the premise holds and the
conclusion fails.  The first row of `eq:terminal-wrapper-gates` -- `q >= 8 E_T`,
i.e. `E_T <= q/8` at `09:1732--1733` -- is exactly what closes the gap, so the
gate system is a genuine hypothesis of `eq:wrapper-terminal-donor-gate`. -/
theorem gate_rows_are_load_bearing :
    ((2 : ℝ) - 1 ≤ 1) ∧ ¬ ((2 : ℝ) / 2 < 1) := by
  constructor <;> norm_num

/-- **Pole 4 (`09:1704`'s branch assumption is not derivable from the schedule).**

`e_T <= E_T` is the schedule's majorant and says nothing about positivity: the
value `e_T = 0` satisfies it at every legal `E_T`.  This is why `heTpos` is
carried as the frozen branch assumption of `09:1704` ("Assume then that
`e_T > 0`") rather than derived from the counting, and why Section 3 -- which
*does* produce it, from the `09:1701` endpoint at one good donor -- is a separate
leg.  Conjoining the two would collapse two frozen cases of one construction into
a single hypothesis bundle. -/
theorem majorant_does_not_give_positivity (ETv : ℕ) : (0 : ℕ) ≤ ETv ∧ ¬ (0 < (0 : ℕ)) :=
  ⟨Nat.zero_le _, by omega⟩

end Poles

section Consistency

/-- **The gate bundle of Section 4a is jointly satisfiable at symbolic schedule
values -- NON-FIDELITY.**

Every hypothesis of `terminalDonorGate_of_gates` is met simultaneously, at
`q = 2^{A_wrap L_P^2}` and with `E_T`, `E_B`, `u_term`, `B_theta`, `s`, `k_ref`
and `L_P` **symbolic**: the gate system is the banked
`WrapperMassRedistribution.terminalWrapperGates_nonvacuous`, which is
`06:744--747`'s own order of determination ("Their eventual validity is why
`A_wrap` is chosen after the universal coefficient audit"), and the remaining
slots are filled at the frozen majorant `e_T = E_T` and the frozen floor
`|J_good| = q - E_T` of `09:1725`.  Nothing is assigned a numeral, and the
witness `A_wrap` clears the frozen floor `A_wrap > c_seed` of `06:1671`.

**This is a satisfiability statement about the gate system, not the paper's
instance.**  The paper's `A_wrap` is fixed by `thm:eff-ledger`, and that
canonical-inhabitation obligation stays REGISTERED and DEFERRED; this lemma is
explicitly not offered as its discharge. -/
theorem terminalDonorGate_bundle_is_consistent
    (LP e0m EBv sv kref : ℕ) {θ etaR : ℝ}
    (hetaR : 0 < etaR) (hθ : 0 < θ) (he0m : 1 ≤ e0m) (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, ParameterSchedule.cSeed < Awrap ∧
      ((ParameterSchedule.qWrap Awrap LP : ℕ) : ℝ) / 2
          < ((ParameterSchedule.qWrap Awrap LP : ℕ) : ℝ)
            - ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ)
        ∧ ((ParameterSchedule.uTerm sv
              (deltaZero etaR (ParameterSchedule.ET e0m EBv)) : ℕ) : ℝ)
            * ((Btheta θ : ℕ) : ℝ)
          < ((ParameterSchedule.qWrap Awrap LP : ℕ) : ℝ)
            / (4 * ((ParameterSchedule.ET e0m EBv : ℕ) : ℝ)) := by
  obtain ⟨Awrap, hseed, hgates⟩ :=
    terminalWrapperGates_nonvacuous LP (ParameterSchedule.ET e0m EBv)
      (ParameterSchedule.uTerm sv
        (ParameterSchedule.deltaTerm etaR (ParameterSchedule.ET e0m EBv)))
      (Btheta θ) kref hLP
  refine ⟨Awrap, hseed, ?_⟩
  exact terminalDonorGate_of_gates hetaR hθ he0m
    (one_le_ET_of_e0Max_pos he0m) (le_refl _) hgates (le_refl _)

end Consistency

end EthInapproximability.ParameterizedNP.WrapperLossTable
