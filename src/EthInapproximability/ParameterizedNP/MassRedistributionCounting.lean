import EthInapproximability.ParameterizedNP.SplitFirstBobInstance

/-!
# Parameterized NP route: the counting head of the mass-redistribution segment

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 1512--1615**, the
  opening of the subsubsection `sec:wrapper-mass-redistribution` (`09:1512--1513`)
  through `eq:wrapper-mass-leaves-owner` (label `09:1614`).  Every anchor below was
  opened first-hand in that file for this tranche.

  The anchors traced here, in the order the frozen block prints them:

  * `09:1515--1517`, the no-omitted-early-leaf remark;
  * `09:1519--1525`, `J_clean` and the contrapositive call: "Let `J_clean` be the
    `c` outer coordinates whose clean reference certificates reach final Alice
    nodes.  Apply the contrapositive of `lem:early-protected-closure` at every
    first-Bob node, with `J_0 = J_clean`.  Such a node has `kappa_v >= 2`, and the
    conclusion of the lemma would exceed its remaining child budget";
  * `eq:wrapper-total-early-mass` (label `09:1533`, display `09:1526--1534`):
    `P_B < 128 mu_P B_theta L_q s K_B <= 128 mu_P B_theta L_q s e_0/(1-vartheta)`;
  * `09:1535--1541`, the Bob-heavy definition
    `sum_{v first-Bob} P_v({j}) > eta_R/4`, "where mass is normalized by `m`, as in
    the definition of `P_v`", and "Their number `e_B` satisfies";
  * `eq:wrapper-bob-heavy-count` (label `09:1546`, display `09:1542--1547`);
  * `09:1548`, "Let `J_good` be the other clean donors";
  * `09:1550--1554`, owners, `n_T`, and the exceptional final nodes: "Every clean
    reference certificate has a unique final node, its *owner*.  Distinct clean
    donors have distinct owners because a final node contains at most one clean
    certificate.  Let `n_T` be the total number of final nodes.  All final nodes
    not owned by `J_good` are called exceptional; their number is";
  * `eq:wrapper-exceptional-count` (label `09:1562`, display `09:1555--1563`):
    `e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`;
  * `09:1564`, its justification "Here we used `K_B + n_T <= q` and
    `eq:wrapper-clean-count`";
  * `09:1566--1584`, the four-category loss table for the rows of a good donor
    missing from its owner (`09:1574--1575` initially deleted rows, at most
    `eta_R m/16`; `09:1576--1577` base rows lost along the unique clean route,
    less than `eta_R m/16`; `09:1578--1579` protected rows stopped at first-Bob
    nodes, at most `eta_R m/4`; `09:1580--1581` protected rows sent to other final
    nodes, "the remaining loss");
  * `09:1585`, the first line's justification `delta_U q <= eta_R/16`;
  * `09:1585--1597`, the second line's justification: "consider a clean
    certificate at selector level `k >= 1`.  If both Alice children contained at
    least `A_{k-1}` of its reference rows, the certificate would split and both
    descendants would be low.  Since the certificate remains clean, the child not
    followed by its unique clean route contains fewer than `A_{k-1}` such rows.
    Its total loss is therefore strictly less than
    `sum_{h=0}^{r-1} A_h = A_0 sum 2^h = (q-1)A_0 < qA_0`.  The schedule requires
    `q A_0 <= eta_R m/16`, proving the second line";
  * `09:1598`, the third line's justification "The third line is the definition of
    not being Bob-heavy".

* **Cross-anchors opened first-hand for this tranche:**
  * `09:1250--1259`, the two frozen stopping rules and `kappa_v = 2^{r-d_v}`, and
    `09:1306--1308`, "one more bit than the remaining child budget", which is the
    budget the contrapositive of `09:1522--1523` spends;
  * `lem:early-protected-closure` (statement `09:1418--1430`), whose conclusion is
    "one child of `v` has communication complexity at least `C + log_2 kappa - 1`";
  * `eq:wrapper-clean-count` (label `09:1356`, display `09:1352--1357`) and its
    frozen derivation `09:1358--1365`, whose Kraft input is `K_B + c + ell <= q`
    (`09:1365`).  This is a *different* inequality from the `K_B + n_T <= q` that
    `09:1564` re-uses; both come from the same Kraft device (`09:1264`,
    `sum_v kappa_v <= q`), and since `n_T >= c + ell` the one this module proves
    (`bobCapacity_add_card_finalNodes_le`) is the stronger of the two;
  * `09:1347--1349`, the frozen definitions of `K_B` ("the sum of `kappa_v` over
    first-Bob nodes") and of `c` ("the number of final nodes with one clean
    certificate"), which `09:1519--1520` re-reads as the size of `J_clean`;
  * `09:1221`, `A_k = 2^k A_0`, the frozen reference-row floors the second table
    line sums;
  * `09:1240--1248`, the frozen routing rule ("route it to a child containing at
    least `ceil(A_k/2) >= A_{k-1}` of those rows ... route it to both children if
    both qualify.  A clean certificate routed uniquely stays clean with weight
    one.  When a clean certificate splits, both descendants become low
    certificates of weight `1/2`"), which is what makes the second table line's
    justification a statement about `splitsAt` and `kindAlong`.

## What this module is, and what it deliberately is not

`WrapperMassRedistribution` banked this block's **arithmetic** over abstract
reals and an abstract index type: `wrapperTotalEarlyMass`, `wrapperBobHeavyCount`,
`owner_injOn_of_unique_clean`, `wrapperExceptionalCount`, `cleanRouteLoss_*`, and
`wrapperMassLeavesOwner`.  Every one of those is consumed here **by pin** and none
is restated.

What this module adds is the **engine layer**: the same frozen sentences read on
the banked routed certificate system of a genuine protocol
(`RoutedCertificateSystem.RoutedSystem`), where

* the "remaining child budget" of `09:1522--1523` is *derived* from the alleged
  `(C+r-1)`-bit protocol rather than assumed (`firstBob_child_budget`);
* `P_B` and the per-donor first-Bob mass of `09:1537` are two aggregations of one
  doubly-indexed mass, and the frozen chain `09:1526 -> 09:1542` is exactly the
  exchange of the two summation orders (`earlyMass_eq_sum_firstBobMass`);
* `J_good` is the frozen set difference and `|J_good| = c - e_B` is an identity of
  cardinalities, not a hypothesis (`card_goodDonors_add_card_bobHeavy`);
* the exceptional final nodes are a *set*, and `e_T = n_T - |J_good|`
  (`09:1558`) is **proved** from the owner injectivity of `09:1551--1552`
  (`card_exceptionalFinal`);
* `09:1564`'s "Here we used `K_B + n_T <= q`" is **proved** from the banked Kraft
  inequality and `kappa_v = 1` at final nodes
  (`bobCapacity_add_card_finalNodes_le`), not carried as a binder;
* the second table line's frozen justification ("the child not followed by its
  unique clean route contains fewer than `A_{k-1}` such rows") is **proved** from
  the derived routing dynamics of `RoutingDynamics`
  (`offRoute_rows_lt_childFloor`).

**M3 (reservoir types).**  The two protected reservoir types of `09:1367--1371`
enter only through banked counting consequences: the halving of `09:1433--1439`
lives inside `WrapperProtectedEarly.earlyProtectedClosure`, whose *conclusion*
this module consumes as the hypothesis `hclosure` of `firstBob_earlyMass_lt`.  No
reservoir type is re-modelled here.

**M4 (fixed member, fixed protocol).**  Every statement below is about one fixed
`RoutedSystem` on one fixed `Protocol`; no quantification over protocol families
and no selection of a member occurs.

**`hDenseRung` is neither discharged nor fed by this module.**  `DenseRung` (the
`eq:wrapper-u-dense` endpoint) falls only at the genuine end of the
mass-redistribution segment, through the banked bridge; nothing below mentions
it, and no route completion is claimed.

## GAP-EXPOSED, with the next-round prescription

1. **`09:1600--1615`, the fourth table line and `eq:wrapper-mass-leaves-owner`.**
   Not landed here.  The frozen step is a contrapositive through the
   deletion-stable Stage-4 theorem ("The deletion-stable Stage-4 theorem would
   make the owner `C`-hard, impossible under the alleged shallow protocol"), i.e.
   it consumes hardness, not counting.  Its arithmetic is already banked as
   `WrapperMassRedistribution.wrapperMassLeavesOwner` and
   `fourCategory_coefficients`.  *Next round:* supply the engine retention
   `1 - (L1+L2+L3+L4) <= retained` at the owner rectangle of the routed system and
   feed `wrapperMassLeavesOwner` with the banked deletion-stable endpoint; this is
   the first step of the segment that touches hardness rather than counting.
2. **`eq:wrapper-clean-count` at the donor side.**  `09:1519--1520` reads the
   frozen `c` of `09:1348` as `|J_clean|`.  The identification of the node count
   `|cleanNodes|` with the donor count `|J_clean|` is the frozen owner bijection,
   and only its `<=` half (owner injectivity) is landed here; the reverse
   inclusion needs the final-node classification of `09:1346--1347` as a
   *surjection* onto `cleanNodes`.  Until then the first clause of
   `eq:wrapper-clean-count` enters `wrapperExceptionalCount_engine` as the explicit
   binder `hclean`, read at `J_clean`.  *Next round:* land
   `cleanNodes_image_owner` and replace the binder by the banked
   `DenseWrapperFrontier.wrapperCleanCount` conclusion.
3. **The per-node mass `P_v` itself.**  `09:1374--1376` defines `P_v(J_0)` as the
   protected mass reaching `v`, normalized by `m`.  It is the routing's output on
   the *protected* reservoirs, which the routed system does not carry (the banked
   record deliberately excludes `W_v` and every mass), so it enters as the
   explicit doubly-indexed binder `Pv : V -> iota -> R`.  *Next round:* derive
   `Pv` from a protected-reservoir routing once `09:1367--1371` is modelled.
4. **The first and second table lines' schedule gates.**  These are two
   *different* frozen gates, and only the second one lives in
   `eq:wrapper-initial-survival`.
   * `delta_U q <= eta_R/16` is stated at `09:1585` ("The first line follows from
     `delta_U q <= eta_R/16`").  It is not a row of `eq:wrapper-initial-survival`;
     the schedule discharges it with **equality**, since `eq:q-deltaU`
     (`06:513--519`, label `06:518`) sets `delta_U = eta_R/(16 q)`.
   * `q A_0 <= eta_R m/16` is stated at `09:1597` ("The schedule requires
     `q A_0 <= eta_R m/16`") and *is* the first row of
     `eq:wrapper-initial-survival` (`09:1226`, `q A_0 / m <= eta_R/16`).

   Both are carried as binders here, exactly as the banked
   `cleanRouteLoss_lt_budget` carries them.

## Unexercised joints (next-round live-fire targets)

Neither item below is a vacuity defect -- each bundle is demonstrably
non-contradictory -- but each is a joint this tranche states without firing at a
live instance, and they are the honest next targets.

* **Section 3 is entirely un-live-fired**, and `offRoute_rows_lt_childFloor` is
  cheaply fireable: at `P := liveProtocol`, `R := liveRows 0`, `A0 := 1`,
  `r := 2`, `p := []`, `b := false`, all four hypotheses are already banked
  (`hnode` from `live_hcomp`, `hlt : 0 < 2`, `hrows` from `live_hR` -- the
  `09:1233--1235` retention holding at equality, `refRowFloor 1 2 = 4` against
  `(liveRows 0).card = 4` -- and `hclean` from `live_descendants_zero`).
  `initiallyDeleted_le_budget` and `cleanRouteLoss_engine` stay unfireable until
  `delta_U`, `m` and `m_G` are pinned, and that is honest rather than deferred.
* **Section 1 has no consistency instance.**  `firstBob_earlyMass_lt` and
  `firstBob_earlyMass_lt_frozen` are the tranche's link from
  `lem:early-protected-closure` to the mass bound, and neither is exercised.  The
  bundle is satisfiable (`liveSystem` has a first-Bob node and
  `liveProtocol.cost = 2 <= C + r - 1 = 4` at `C = 3`).  *Next round:* fire
  `firstBob_child_budget` at `liveSystem`/`liveBobNode` with `C = 3`, then
  `firstBob_earlyMass_lt` with `hclosure` obtained by instantiating the banked
  `WrapperProtectedEarly.earlyProtectedClosure` -- the actual remaining wiring.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for this
tranche (`redistribut`, `owner`, `donor`, `heavy`, `exceptional`, `clean`,
`protected mass`, `final node`, `frontier`).  The predecessor's finding is
re-confirmed and **not** re-used: the reader has no counterpart for this block.

* `A-stage4-details.tex:373--377` ("At the frontier, associate every surviving
  ordinary outer copy with a protected donor copy.  The fixed masses and the
  certified cover bounds ensure that either an early protected reservoir already
  gives a hard restriction or one terminal owner receives enough protected mass
  from a donor") is unnumbered prose inside the proof of
  `thm:paper-adapted-stage4-interface`; line `374` is already recorded by
  `WrapperProjectionCovers` as unclaimed prose, and citing prose as a statement is
  barred.
* `A-stage4-details.tex:396--399` ("The complete owner--donor count is finite: it
  uses only the fixed reservoir masses above, the two source deletion tolerances,
  and the exact cover and ceiling inequalities certified by the parameter
  compiler.  It is expanded line by line in the ultra-explicit companion") is the
  reader's nearest account of exactly this counting head, and is likewise
  unnumbered proof prose.
* The one display in range, `A-stage4-details.tex:393--395`
  (`D_U(1; 1-delta_U, theta) >= C + r_q`), is `eq:wrapper-u-dense` itself, which
  this module does **not** close and therefore must not claim.  It is an
  *unnumbered* `\[...\]` display carrying no `\label`: the only `\label` anywhere
  in `A-stage4-details.tex:340--420` is at line `345`
  (`eq:paper-adapted-stage4-interface`).  So the reader offers nothing citable
  here even in principle.
* `A-stage4-details.tex:318` and `371` ("terminal frontier"; line `387` reads
  "supply the mass and profile routed to this frontier.  At the frontier, the
  two-stream lemma", and does *not* carry the phrase) and
  `A-stage4-details.tex:263--271`, `02-preliminaries.tex:563--564`,
  `01-introduction.tex:101` ("weighted frontier") are the Stage-4
  quotient-support frontier, already disclosed as near-misses by
  `FrontierIndexing` and `FirstBobFrontierInstance`.

**This module claims no reader item**, and recording the absence is a finding
about the reader artifact, not a licence to invent one.

## Axiom surface

No new `axiom`.  Every external contact is an explicit binder: the closure
conclusion `hclosure` (the banked `WrapperProtectedEarly.earlyProtectedClosure`
read at one node), the per-node mass `Pv`, the clean-count binder `hclean`, the
final-node uniqueness `huniq` (the banked `lem:final-reference-uniqueness` in
counting form), and the two schedule gates.  `EXPANDER-001` is not reachable from
this module.

## Non-vacuity

Section 8 exercises every definition on the banked live routed system
`FirstBobFrontierInstance.liveSystem` at a mass assignment that makes **both**
sides of the frozen `J_clean = J_good + Bob-heavy` split nonempty, so
`e_B = |J_good| = e_T = 1` and `n_T = 2`: no cardinality identity below is
satisfied by an empty case.  That instance is labelled **NON-FIDELITY**: the
paper's own instance of this counting head is the routed system of the *alleged
shallow protocol*, which is not built yet, and the canonical-inhabitation
obligation for it is registered as GAP-EXPOSED item 3 above.
-/

namespace EthInapproximability.ParameterizedNP.MassRedistributionCounting

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance

/-! ## §1  The remaining child budget at a first-Bob node (`09:1522--1523`)

"Such a node has `kappa_v >= 2`, and the conclusion of the lemma would exceed its
remaining child budget."

The budget is not a hypothesis at the engine: it is what the alleged
`(C+r-1)`-bit protocol leaves below the Bob query the frontier node exposes. -/

section Budget

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}

/-- **`09:1306--1308` and `09:1522--1523`, at a Bob child of a first-Bob node.**

At a first-Bob node `v` of depth `d_v` in the alleged `(C+r-1)`-bit protocol,
*each* of the two children of the exposed Bob query keeps at most
`C + r - 1 - (d_v + 1)` further bits: the node's own residual budget is the banked
`RoutedSystem.firstBob_residual_budget'`, and answering the Bob query costs the
extra bit, which is the banked `cost_descendStep_succ_le` at the exposed query.

This is precisely the `hbudget` shape the banked
`DenseWrapperFrontier.firstBob_budget_contradiction` consumes, and therefore the
shape `WrapperMassRedistribution.firstBob_protectedMass_lt` consumes.  General in
the node type, the certificate index, `r`, `A_0`, `C` and the child bit. -/
theorem firstBob_child_budget {C : ℕ} (S : RoutedSystem P Coord ι V r A0) {v : V}
    (hv : S.firstBob v = true) (hcost : P.cost ≤ C + r - 1) (b : Bool) :
    (descendStep (descend P (S.node v)) b).cost + ((S.node v).length + 1) ≤ C + r - 1 := by
  have hres := S.firstBob_residual_budget' hv hcost
  have hbob : IsBobNode (descend P (S.node v)) := (S.firstBob_spec v hv).2.1
  have hstep := cost_descendStep_succ_le (isQueryNode_of_isBobNode hbob) b
  omega

/-- **`09:1255` at a first-Bob node of the routed system.**  `kappa_v = 2^{r-d_v}`,
the banked `stoppingCapacity`, read through the banked bridge
`RoutedSystem.toWrapperFrontier`.  A readout, not a new constant. -/
theorem capacity_eq_two_pow (S : RoutedSystem P Coord ι V r A0) (v : V) :
    S.toWrapperFrontier.capacity v = 2 ^ (r - (S.node v).length) := rfl

/-- **`09:1519--1525`, the contrapositive call, at the routed system.**

"Apply the contrapositive of `lem:early-protected-closure` at every first-Bob
node, with `J_0 = J_clean`.  Such a node has `kappa_v >= 2`, and the conclusion of
the lemma would exceed its remaining child budget.  Therefore the total protected
mass from clean donors that stops at first-Bob nodes is strictly less than ..."

`hclosure` is `lem:early-protected-closure` read at this node: the banked
`WrapperProtectedEarly.earlyProtectedClosure`, whose conclusion is that *one child
of `v`* has complexity at least `C + log_2 kappa_v - 1`.  Here `kappa_v = 2^ell`
with `ell = r - d_v >= 1`, so `log_2 kappa_v = ell` and the conclusion is the
natural-number `C + ell - 1 <= cost(child)`.  Everything else -- the frozen
`kappa_v >= 2`, the depth relation `d_v + ell = r`, and the remaining child budget
-- is derived from the frontier's own stopping rule and from `firstBob_child_budget`.

The arithmetic contradiction is the banked
`WrapperMassRedistribution.firstBob_protectedMass_lt`, re-proved nowhere.
General in the mass and the threshold. -/
theorem firstBob_earlyMass_lt {C : ℕ} (S : RoutedSystem P Coord ι V r A0) {v : V}
    (hv : S.firstBob v = true) (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1) (b : Bool)
    {Pv thr : ℝ}
    (hclosure : thr ≤ Pv →
      C + (r - (S.node v).length) - 1 ≤ (descendStep (descend P (S.node v)) b).cost) :
    Pv < thr := by
  have hlt : (S.node v).length < r := (S.firstBob_spec v hv).2.2
  exact firstBob_protectedMass_lt (C := C) (r := r) (d := (S.node v).length)
    (ℓ := r - (S.node v).length) (B := (descendStep (descend P (S.node v)) b).cost)
    hC (by omega) (by omega) (firstBob_child_budget S hv hcost b) hclosure

/-- **`09:1519--1525` at the frozen threshold of `eq:protected-early-threshold`.**

The same contrapositive with the threshold instantiated at the frozen coefficient
`128 mu_P B_theta L_q s` times `kappa_v`, i.e. at
`WrapperMassRedistribution.earlyMassCoeff theta q s * kappa_v`.  This is the exact
per-node bound `eq:wrapper-total-early-mass` sums over first-Bob nodes. -/
theorem firstBob_earlyMass_lt_frozen {C : ℕ} (S : RoutedSystem P Coord ι V r A0) {v : V}
    (hv : S.firstBob v = true) (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1) (b : Bool)
    {θ : ℝ} {q s : ℕ} {Pv : ℝ}
    (hclosure : earlyMassCoeff θ q s * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ) ≤ Pv →
      C + (r - (S.node v).length) - 1 ≤ (descendStep (descend P (S.node v)) b).cost) :
    Pv < earlyMassCoeff θ q s * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ) :=
  firstBob_earlyMass_lt S hv hC hcost b hclosure

end Budget

/-! ## §2  The two aggregations of protected mass (`09:1526`, `09:1537`)

`09:1374--1376` defines `P_v(J_0)` as the protected mass from the donors in `J_0`
reaching `v`, normalized by `m`.  It is additive in the donor set, so the frozen
block's two quantities -- `P_B`, the mass over all first-Bob nodes from
`J_clean` (`09:1524--1528`), and `sum_{v first-Bob} P_v({j})`, the mass of a
single donor (`09:1537`) -- are the two summation orders of one doubly-indexed
family.  Carrying `P_v` as `Pv : V -> iota -> R` is what makes that an identity
rather than an assumption. -/

section Masses

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V]

/-- **`09:1374--1376`, `P_v(J_0)` at one frontier node.**  The protected mass from
the donors of `J_0` that reaches `v`, normalized by `m` -- the sum of the
per-donor masses.  It is a function of the mass family and the donor set alone;
the routed system enters only when the *frontier* is summed over. -/
noncomputable def donorMass {ι V : Type*} (Pv : V → ι → ℝ)
    (J₀ : Finset ι) (v : V) : ℝ :=
  ∑ j ∈ J₀, Pv v j

/-- **`09:1537`.**  `sum_{v : first-Bob frontier node} P_v({j})`, the first-Bob
mass of a single donor -- the quantity the Bob-heavy threshold of `09:1538` is
compared against. -/
noncomputable def firstBobMass (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (j : ι) : ℝ :=
  ∑ v ∈ S.toWrapperFrontier.bobNodes, Pv v j

/-- **`09:1524--1528`, `P_B`.**  "the total protected mass from clean donors that
stops at first-Bob nodes". -/
noncomputable def earlyMass (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (J₀ : Finset ι) : ℝ :=
  ∑ v ∈ S.toWrapperFrontier.bobNodes, donorMass Pv J₀ v

/-- **Aux 0a (`P_v({j})`, the frozen singleton readout of `09:1537`).**

`09:1537` writes the Bob-heavy test on `P_v({j})`, the mass of the *single* donor
`j` reaching `v`.  At the doubly-indexed carrier that is `Pv v j` itself, which is
why `firstBobMass` may be written as a plain sum of `Pv v j`.  General. -/
@[simp] theorem donorMass_singleton {ι V : Type*} (Pv : V → ι → ℝ) (j : ι) (v : V) :
    donorMass Pv ({j} : Finset ι) v = Pv v j := by
  simp [donorMass]

/-- **Aux 0b (`09:1537` verbatim).**  `sum_{v : first-Bob frontier node} P_v({j})`,
with `P_v` at the frozen singleton donor set.  General. -/
theorem firstBobMass_eq_sum_donorMass_singleton (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (j : ι) :
    firstBobMass S Pv j
      = ∑ v ∈ S.toWrapperFrontier.bobNodes, donorMass Pv ({j} : Finset ι) v := by
  simp [firstBobMass]

/-- **Aux 1 (the aggregation identity, `09:1526` vs `09:1537`).**

`P_B = sum_{j in J_0} sum_{v first-Bob} P_v({j})`.  This is the exchange of
summation orders, and it is the step that lets the bound
`eq:wrapper-total-early-mass` on `P_B` be spent as a bound on the *total of the
per-donor masses* in `eq:wrapper-bob-heavy-count`.  General. -/
theorem earlyMass_eq_sum_firstBobMass (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (J₀ : Finset ι) :
    earlyMass S Pv J₀ = ∑ j ∈ J₀, firstBobMass S Pv j := by
  unfold earlyMass donorMass firstBobMass
  exact Finset.sum_comm

/-- **Aux 2.**  No donors, no early mass.  General. -/
@[simp] theorem earlyMass_empty (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ) :
    earlyMass S Pv (∅ : Finset ι) = 0 := by
  simp [earlyMass, donorMass]

/-- **Aux 3 (monotonicity in the donor set).**  Protected mass is nonnegative, so
enlarging the donor set can only enlarge `P_B`.  General. -/
theorem earlyMass_mono (S : RoutedSystem P Coord ι V r A0) {Pv : V → ι → ℝ}
    {J₀ J₁ : Finset ι} (hsub : J₀ ⊆ J₁) (hnn : ∀ v : V, ∀ j ∈ J₁, 0 ≤ Pv v j) :
    earlyMass S Pv J₀ ≤ earlyMass S Pv J₁ := by
  unfold earlyMass donorMass
  refine Finset.sum_le_sum fun v _ => ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hnn v j hj

/-- **Aux 4.**  Nonnegative per-node mass gives nonnegative per-donor first-Bob
mass -- the `hnonneg` the banked counting lemma consumes.  General. -/
theorem firstBobMass_nonneg (S : RoutedSystem P Coord ι V r A0) {Pv : V → ι → ℝ}
    {j : ι} (hnn : ∀ v : V, 0 ≤ Pv v j) : 0 ≤ firstBobMass S Pv j :=
  Finset.sum_nonneg fun v _ => hnn v

/-! ### `eq:wrapper-total-early-mass` (`09:1526--1534`) at the routed system -/

/-- **`eq:wrapper-clean-count`, second clause, at the routed system.**

`K_B <= e_0/(1-vartheta)`, obtained from the banked
`DenseWrapperFrontier.wrapperCleanCount` by dropping the nonnegative split tally
`ell`.  The banked theorem is consumed by pin; nothing of its derivation is
restated. -/
theorem bobCapacity_le_of_cleanCount (S : RoutedSystem P Coord ι V r A0)
    (cert : V → Option CertKind) (W : V → ℝ) {q e0 : ℝ}
    (hq : q = (2 : ℝ) ^ r)
    (hlight : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      W v ≤ vartheta * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ))
    (hfinal : ∀ v ∈ S.toWrapperFrontier.finalNodes, W v ≤ finalWeight (cert v))
    (hcons : q - e0 ≤ ∑ v, W v) :
    S.toWrapperFrontier.bobCapacity ≤ e0 / (1 - vartheta) := by
  have h := (wrapperCleanCount S.toWrapperFrontier cert W hq hlight hfinal hcons).2
  have hsplit : (0 : ℝ) ≤ ((S.toWrapperFrontier.splitNodes cert).card : ℝ) :=
    Nat.cast_nonneg _
  linarith

/-- **`eq:wrapper-total-early-mass` (`09:1526--1534`) at the routed system.**

`P_B < 128 mu_P B_theta L_q s K_B <= 128 mu_P B_theta L_q s e_0/(1-vartheta)`.

The per-node strict bound `hlt` is what `firstBob_earlyMass_lt_frozen` produces at
each first-Bob node from the contrapositive of `lem:early-protected-closure`; the
replacement of `K_B` by `e_0/(1-vartheta)` is `eq:wrapper-clean-count`, available
at the routed system through `bobCapacity_le_of_cleanCount`.  The summation is the
banked `WrapperMassRedistribution.wrapperTotalEarlyMass_frozen`, consumed by pin.

The nonemptiness binder is the banked theorem's own: with no first-Bob node at all
the frozen strict inequality is false, and the banked
`totalEarlyMass_needs_a_first_bob_node` is the pole for it. -/
theorem wrapperTotalEarlyMass_engine (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (J₀ : Finset ι) {θ e0 : ℝ} {q s : ℕ}
    (hθ : 0 < θ) (hs : 1 ≤ s)
    (hne : (S.toWrapperFrontier.bobNodes).Nonempty)
    (hlt : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      donorMass Pv J₀ v < earlyMassCoeff θ q s * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ))
    (hKB : S.toWrapperFrontier.bobCapacity ≤ e0 / (1 - vartheta)) :
    earlyMass S Pv J₀ < earlyMassCoeff θ q s * (e0 / (1 - vartheta)) :=
  wrapperTotalEarlyMass_frozen (S.toWrapperFrontier.bobNodes)
    (donorMass Pv J₀) (fun v => ((S.toWrapperFrontier.capacity v : ℕ) : ℝ))
    hθ hs hne hlt hKB

/-- **`09:1564`, "Here we used `K_B + n_T <= q`", PROVED.**

Kraft's inequality on the routed frontier gives `sum_v kappa_v <= q = 2^r`; the
frontier splits into the first-Bob nodes, contributing exactly `K_B`, and the
final Alice nodes, each of capacity `kappa_v = 1` (`09:1250--1252`) and therefore
contributing exactly `n_T`.  Both halves are banked
(`DenseWrapperFrontier.sum_capacity_le_width`,
`sum_bobNodes_add_sum_finalNodes`, `capacity_final_eq_one`); the frozen sentence
is their combination and is not carried as a binder.  General. -/
theorem bobCapacity_add_card_finalNodes_le (S : RoutedSystem P Coord ι V r A0) :
    S.toWrapperFrontier.bobCapacity + ((S.toWrapperFrontier.finalNodes).card : ℝ)
      ≤ (2 : ℝ) ^ r := by
  classical
  set F := S.toWrapperFrontier with hF
  have hone : ∀ v ∈ F.finalNodes, ((F.capacity v : ℕ) : ℝ) = 1 := by
    intro v hv
    have hb : F.firstBob v = false := by
      simpa [WrapperFrontier.finalNodes] using hv
    rw [F.capacity_final_eq_one hb]
    norm_num
  have hfin : ∑ v ∈ F.finalNodes, ((F.capacity v : ℕ) : ℝ) = (F.finalNodes.card : ℝ) := by
    rw [Finset.sum_congr rfl hone]
    simp
  have hsplit := F.sum_bobNodes_add_sum_finalNodes (fun v => ((F.capacity v : ℕ) : ℝ))
  have hk : (∑ v, ((F.capacity v : ℕ) : ℝ)) ≤ (2 : ℝ) ^ r := by
    have := F.sum_capacity_le_width
    have hcast : ((∑ v, F.capacity v : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    exact hcast
  rw [WrapperFrontier.bobCapacity, ← hfin]
  rw [hsplit]
  exact hk

end Masses

section Donors

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [Fintype ι]

/-! ### `eq:wrapper-bob-heavy-count` (`09:1535--1547`) at the routed system -/

/-- **`09:1535--1539`, the Bob-heavy clean donors.**

"Call a clean donor `j` *Bob-heavy* if `sum_{v first-Bob} P_v({j}) > eta_R/4`."
The set is a subset of `J_clean` -- the banked `RoutedSystem.cleanFinal`, which is
`09:1519--1520`'s "the `c` outer coordinates whose clean reference certificates
reach final Alice nodes" -- because `09:1535` says *clean* donor.  The threshold is
the banked `WrapperMassRedistribution.BobHeavy`, unfolded so that the comparison
is decidable in Lean's linear order on the reals. -/
noncomputable def bobHeavyDonors (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) : Finset ι :=
  S.cleanFinal.filter fun j => etaR / 4 < firstBobMass S Pv j

/-- **Aux 5.**  Membership readout, at the banked `BobHeavy` predicate.  General. -/
theorem mem_bobHeavyDonors {S : RoutedSystem P Coord ι V r A0} {Pv : V → ι → ℝ}
    {etaR : ℝ} {j : ι} :
    j ∈ bobHeavyDonors S Pv etaR ↔
      j ∈ S.cleanFinal ∧ BobHeavy etaR (firstBobMass S Pv j) := by
  simp [bobHeavyDonors, BobHeavy]

/-- **`09:1535`, "a clean donor".**  Bob-heavy donors are clean donors.  General. -/
theorem bobHeavyDonors_subset (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) : bobHeavyDonors S Pv etaR ⊆ S.cleanFinal :=
  Finset.filter_subset _ _

/-- **Aux 6 (antitone in the threshold).**  Lowering `eta_R` can only make more
donors Bob-heavy.  General. -/
theorem bobHeavyDonors_antitone (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    {etaR etaR' : ℝ} (h : etaR ≤ etaR') :
    bobHeavyDonors S Pv etaR' ⊆ bobHeavyDonors S Pv etaR := by
  intro j hj
  rw [mem_bobHeavyDonors] at hj ⊢
  exact ⟨hj.1, lt_of_le_of_lt (by linarith [hj.2]) hj.2⟩

/-- **`eq:wrapper-bob-heavy-count` (`09:1542--1547`) at the routed system.**

"Their number `e_B` satisfies
`e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)`."

The counting is the banked `WrapperMassRedistribution.wrapperBobHeavyCount`,
consumed by pin at `J = J_clean` and `H = ` the Bob-heavy donors.  What the engine
supplies is the conversion of its total-mass hypothesis: the banked lemma bounds
`sum_{j in J_clean}` of the per-donor masses, and `eq:wrapper-total-early-mass`
bounds `P_B`; `earlyMass_eq_sum_firstBobMass` is exactly the identification of the
two, and is why `htot` below may be stated on `P_B` as the frozen text states
it. -/
theorem wrapperBobHeavyCount_engine (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {θ : ℝ} {q s : ℕ} {e0 etaR : ℝ}
    (hetaR : 0 < etaR)
    (hnonneg : ∀ j ∈ S.cleanFinal, 0 ≤ firstBobMass S Pv j)
    (htot : earlyMass S Pv S.cleanFinal ≤ earlyMassCoeff θ q s * (e0 / (1 - vartheta))) :
    ((bobHeavyDonors S Pv etaR).card : ℝ)
      ≤ 512 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * e0
          / ((1 - vartheta) * etaR) := by
  refine wrapperBobHeavyCount S.cleanFinal (bobHeavyDonors S Pv etaR) (firstBobMass S Pv)
    hetaR (bobHeavyDonors_subset S Pv etaR) hnonneg
    (fun j hj => (mem_bobHeavyDonors.mp hj).2) ?_
  rw [← earlyMass_eq_sum_firstBobMass]
  exact htot

end Donors

section Good

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [Fintype ι] [DecidableEq ι]

/-! ### `09:1548--1564`: `J_good`, owners, and `eq:wrapper-exceptional-count` -/

/-- **`09:1548`.**  "Let `J_good` be the other clean donors."  The frozen set
difference; the resulting `|J_good| = c - e_B` -- the consequence of `09:1548`
that `09:1559` spends as `e_T <= q - c + e_B` -- is then the cardinality identity
`card_goodDonors_add_card_bobHeavy` below, not a hypothesis. -/
noncomputable def goodDonors (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) : Finset ι :=
  S.cleanFinal \ bobHeavyDonors S Pv etaR

/-- **Aux 7.**  Good donors are clean donors.  General. -/
theorem goodDonors_subset (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) : goodDonors S Pv etaR ⊆ S.cleanFinal :=
  Finset.sdiff_subset

/-- **`09:1598`, the third table line, at the routed system.**

"The third line is the definition of not being Bob-heavy": a good donor's
protected mass stopped at first-Bob nodes is at most `eta_R/4`.  The frozen table
row (`09:1578--1579`) prints the same bound un-normalized, as `eta_R m/4`; the
factor `m` is the normalization `09:1540` already fixes for `P_v` ("where mass is
normalized by `m`"), so this is that row and not a weakening of it.  General. -/
theorem goodDonor_firstBobMass_le {S : RoutedSystem P Coord ι V r A0} {Pv : V → ι → ℝ}
    {etaR : ℝ} {j : ι} (hj : j ∈ goodDonors S Pv etaR) :
    firstBobMass S Pv j ≤ etaR / 4 := by
  rw [goodDonors, Finset.mem_sdiff, mem_bobHeavyDonors] at hj
  by_contra hcon
  exact hj.2 ⟨hj.1, not_le.mp hcon⟩

/-- **`09:1548`, `|J_good| = c - e_B`, as an identity** (the frozen step
`09:1559` spends it; `09:1558` is the *other* identity, `e_T = n_T - |J_good|`).

The clean donors split into the Bob-heavy ones and the good ones, so the two
counts add up to `c = |J_clean|`.  Stated additively so that no natural-number
truncation is involved.  General. -/
theorem card_goodDonors_add_card_bobHeavy (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (etaR : ℝ) :
    (goodDonors S Pv etaR).card + (bobHeavyDonors S Pv etaR).card = S.cleanFinal.card :=
  Finset.card_sdiff_add_card_eq_card (bobHeavyDonors_subset S Pv etaR)

end Good

section Exceptional

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **`09:1553`.**  "All final nodes not owned by `J_good` are called
exceptional."  The frozen set, at the banked owner map
`RoutedSystem.owner`. -/
noncomputable def exceptionalFinal (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) : Finset V :=
  S.toWrapperFrontier.finalNodes \ (goodDonors S Pv etaR).image S.owner

/-- **`09:1550--1551`, at the routed system.**  "Every clean reference certificate
has a unique final node, its *owner*": the owner of a good donor is a final Alice
node, so the owned nodes are a subset of the `n_T` final nodes.  General. -/
theorem goodDonors_image_owner_subset (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (etaR : ℝ) :
    (goodDonors S Pv etaR).image S.owner ⊆ S.toWrapperFrontier.finalNodes := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have hjc : j ∈ S.cleanFinal := goodDonors_subset S Pv etaR hj
  rw [RoutedSystem.cleanFinal, Finset.mem_filter] at hjc
  simp only [WrapperFrontier.finalNodes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hjc.2.2

/-- **`09:1557--1558`, `e_T = n_T - |J_good|`, PROVED.**

"All final nodes not owned by `J_good` are called exceptional; their number is
`e_T = n_T - |J_good|`."

At the engine this is an identity, not a definition: the owned nodes are a subset
of the final nodes and the owner map is injective on the clean donors
(`09:1551--1552`, "Distinct clean donors have distinct owners because a final node
contains at most one clean certificate"), so the image has exactly `|J_good|`
elements and the complement has exactly `n_T - |J_good|`.  The injectivity is the
banked `RoutedSystem.owner_injOn`, whose input `huniq` is the banked
`lem:final-reference-uniqueness` in counting form.  Stated additively.  General. -/
theorem card_exceptionalFinal (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ)
    (huniq : ∀ v : V, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1) :
    (exceptionalFinal S Pv etaR).card + (goodDonors S Pv etaR).card
      = (S.toWrapperFrontier.finalNodes).card := by
  have hinj : Set.InjOn S.owner (goodDonors S Pv etaR) := by
    intro i hi j hj hij
    exact S.owner_injOn huniq i (goodDonors_subset S Pv etaR hi) j
      (goodDonors_subset S Pv etaR hj) hij
  have himg : ((goodDonors S Pv etaR).image S.owner).card = (goodDonors S Pv etaR).card :=
    Finset.card_image_of_injOn hinj
  rw [exceptionalFinal, ← himg]
  exact Finset.card_sdiff_add_card_eq_card (goodDonors_image_owner_subset S Pv etaR)

/-- **`eq:wrapper-exceptional-count` (`09:1555--1564`) at the routed system.**

`e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`, with `e_T` the
cardinality of the derived exceptional set, `c = |J_clean|` the banked
`RoutedSystem.cleanFinal` count and `e_B` the derived Bob-heavy count.

Both frozen inputs of `09:1564` are supplied and neither is postulated:
`K_B + n_T <= q` is `bobCapacity_add_card_finalNodes_le`, and `|J_good| = c - e_B`
is `card_goodDonors_add_card_bobHeavy`.  The only binder is the first clause of
`eq:wrapper-clean-count` read at `J_clean` -- GAP-EXPOSED item 2 of the header.
The arithmetic is the banked
`WrapperMassRedistribution.wrapperExceptionalCount`, consumed by pin. -/
theorem wrapperExceptionalCount_engine (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (etaR : ℝ)
    (huniq : ∀ v : V, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    {q e0 : ℝ} (hq : q = (2 : ℝ) ^ r)
    (hclean : q - e0 / (1 - vartheta) ≤ (S.cleanFinal.card : ℝ)) :
    ((exceptionalFinal S Pv etaR).card : ℝ)
        ≤ q - (S.cleanFinal.card : ℝ) + ((bobHeavyDonors S Pv etaR).card : ℝ)
      ∧ q - (S.cleanFinal.card : ℝ) + ((bobHeavyDonors S Pv etaR).card : ℝ)
        ≤ e0 / (1 - vartheta) + ((bobHeavyDonors S Pv etaR).card : ℝ) := by
  have hcard := card_exceptionalFinal S Pv etaR huniq
  have hgood := card_goodDonors_add_card_bobHeavy S Pv etaR
  have hkraft := bobCapacity_add_card_finalNodes_le S
  have hjgood : ((goodDonors S Pv etaR).card : ℝ)
      = (S.cleanFinal.card : ℝ) - ((bobHeavyDonors S Pv etaR).card : ℝ) := by
    have : (((goodDonors S Pv etaR).card + (bobHeavyDonors S Pv etaR).card : ℕ) : ℝ)
        = (S.cleanFinal.card : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hgood
    push_cast at this
    linarith
  have hnT : ((exceptionalFinal S Pv etaR).card : ℝ)
      = ((S.toWrapperFrontier.finalNodes).card : ℝ) - ((goodDonors S Pv etaR).card : ℝ) := by
    have : (((exceptionalFinal S Pv etaR).card + (goodDonors S Pv etaR).card : ℕ) : ℝ)
        = ((S.toWrapperFrontier.finalNodes).card : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hcard
    push_cast at this
    linarith
  have hmain := wrapperExceptionalCount
    (nT := ((S.toWrapperFrontier.finalNodes).card : ℝ))
    (jgood := ((goodDonors S Pv etaR).card : ℝ))
    (c := (S.cleanFinal.card : ℝ))
    (eB := ((bobHeavyDonors S Pv etaR).card : ℝ))
    (KB := S.toWrapperFrontier.bobCapacity) (q := q) (e0 := e0)
    hjgood S.toWrapperFrontier.bobCapacity_nonneg (by rw [hq]; exact hkraft) hclean
  exact ⟨by rw [hnT]; exact hmain.1, hmain.2⟩

end Exceptional

/-! ## §3  The four-category loss table (`09:1566--1598`)

The first three lines.  The fourth line and `eq:wrapper-mass-leaves-owner`
(`09:1600--1615`) are GAP-EXPOSED item 1 of the header: their frozen justification
runs through the deletion-stable Stage-4 theorem, i.e. through hardness rather
than counting. -/

section Table

/-- **`09:1574--1575` and `09:1585`, the first table line.**

"initially deleted rows: at most `eta_R m/16`.  The first line follows from
`delta_U q <= eta_R/16`."

The schedule gate `hgate` is `09:1585`'s own `delta_U q <= eta_R/16`, which the
schedule discharges with **equality**: `eq:q-deltaU` (`06:513--519`) sets
`delta_U = eta_R/(16 q)`.  It is *not* a row of `eq:wrapper-initial-survival`,
whose first row (`09:1226`, `q A_0 / m <= eta_R/16`) is the *second* table line's
gate and is consumed by `cleanRouteLoss_engine` instead.  Carried as the binder it
is (GAP-EXPOSED item 4).  General in all quantities. -/
theorem initiallyDeleted_le_budget {deltaU etaR loss : ℝ} {q m : ℕ}
    (hgate : deltaU * (q : ℝ) ≤ etaR / 16)
    (hloss : loss ≤ deltaU * (q : ℝ) * (m : ℝ)) :
    loss ≤ etaR * (m : ℝ) / 16 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  nlinarith [hloss, hgate, hm]

section CleanRoute

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- **`09:1586--1588`, the frozen split trigger.**

"If both Alice children contained at least `A_{k-1}` of its reference rows, the
certificate would split and both descendants would be low."

At the derived routing dynamics of `RoutingDynamics` this is a theorem: `A_{k-1}`
at a node of depth `d` (so `k = r - d`) is the banked `childFloor`, "both children
contain at least `A_{k-1}`" is `splitsAt = true`, and the banked
`kindAlong_append_bit` then makes *every* descendant one step down `low`.
General. -/
theorem both_children_qualify_forces_low {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    {p : List Bool} (b : Bool)
    (h0 : Qualifies P R A0 r p false) (h1 : Qualifies P R A0 r p true) :
    kindAlong P R A0 r (p ++ [b]) = CertKind.low := by
  have hsplit : splitsAt P R A0 r p = true := splitsAt_eq_true_iff.mpr ⟨h0, h1⟩
  rw [kindAlong_append_bit, if_pos hsplit]

/-- **`09:1588--1590`, the second table line's engine step, PROVED.**

"Since the certificate remains clean, the child not followed by its unique clean
route contains fewer than `A_{k-1}` such rows."

At a clean descendant of `p` the certificate did not split at `p`; the frozen
routing rule of `09:1240--1244` sends it along `routeBit`, which qualifies; so the
*other* child fails to qualify, i.e. holds fewer than
`childFloor A0 r p = A_{k-1}` reference rows with `k = r - d_v`.  Every ingredient
-- `splitsAt`, `routeBit`, `kindAlong`, `Qualifies` -- is the banked derived
routing of `RoutingDynamics`, consumed by pin.

`hrows` is the frozen `09:1238--1239` floor at the parent, which the banked
`FrontierIndexing.coordRoutes_rows_floor` supplies at every routed certificate.
General. -/
theorem offRoute_rows_lt_childFloor {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    {p : List Bool} {b : Bool}
    (hclean : kindAlong P R A0 r (p ++ [b]) = CertKind.clean)
    (hnode : DenseSynchronisation.IsANode (descend P p)) (hlt : p.length < r)
    (hrows : refRowFloor A0 (r - p.length) ≤ (rowsAt P R p).card) :
    (rowsAt P R (p ++ [!(routeBit P R A0 r p)])).card < refRowFloor A0 (r - p.length - 1) := by
  have hsplit : splitsAt P R A0 r p = false := by
    by_cases hs : splitsAt P R A0 r p = true
    · rw [kindAlong_append_bit, if_pos hs] at hclean
      exact absurd hclean (by decide)
    · simpa using hs
  have hnb : ¬ (Qualifies P R A0 r p false ∧ Qualifies P R A0 r p true) := by
    intro hcon
    rw [splitsAt_eq_true_iff.mpr hcon] at hsplit
    exact Bool.noConfusion hsplit
  have hq := routeBit_qualifies (R := R) (A0 := A0) hnode hlt hrows
  cases hrb : routeBit P R A0 r p with
  | false =>
      rw [hrb] at hq
      have hnot : ¬ Qualifies P R A0 r p true := fun h1 => hnb ⟨hq, h1⟩
      unfold Qualifies childFloor at hnot
      simpa using Nat.lt_of_not_le hnot
  | true =>
      rw [hrb] at hq
      have hnot : ¬ Qualifies P R A0 r p false := fun h0 => hnb ⟨h0, hq⟩
      unfold Qualifies childFloor at hnot
      simpa using Nat.lt_of_not_le hnot

end CleanRoute

/-- **Aux 8 (the frozen level reindexing).**

The per-level off-route loss at depth `d` is `A_{r-d-1}`; as `d` runs over
`0, ..., r-1` these are the floors `A_0, ..., A_{r-1}` in reverse order, which is
the sum `sum_{h=0}^{r-1} A_h` the frozen display `09:1593--1595` evaluates.
General. -/
theorem sum_offRoute_floors (A0 r : ℕ) :
    ∑ d ∈ Finset.range r, refRowFloor A0 (r - d - 1)
      = ∑ h ∈ Finset.range r, refRowFloor A0 h := by
  rw [← Finset.sum_range_reflect (fun h => refRowFloor A0 h) r]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_range] at hd
  congr 1
  omega

/-- **`09:1590--1597`, the second table line, assembled.**

"Its total loss is therefore strictly less than
`sum_{h=0}^{r-1} A_h = A_0 sum 2^h = (q-1) A_0 < q A_0`.  The schedule requires
`q A_0 <= eta_R m/16`, proving the second line."

`hloss` is the per-level bound `offRoute_rows_lt_childFloor` produces at each
selector level; the geometric sum, its strict form and the schedule gate are the
banked `WrapperMassRedistribution.cleanRouteLoss_eq`, `cleanRouteLoss_lt` and
`cleanRouteLoss_lt_budget`, consumed by pin.  General in the loss profile. -/
theorem cleanRouteLoss_engine {A0 r m : ℕ} {etaR : ℝ} {loss : ℕ → ℕ}
    (hA0 : 1 ≤ A0) (hgate : ((2 ^ r * A0 : ℕ) : ℝ) ≤ etaR * (m : ℝ) / 16)
    (hloss : ∀ d ∈ Finset.range r, loss d ≤ refRowFloor A0 (r - d - 1)) :
    ((∑ d ∈ Finset.range r, loss d : ℕ) : ℝ) < etaR * (m : ℝ) / 16 := by
  have h1 : ∑ d ∈ Finset.range r, loss d
      ≤ ∑ d ∈ Finset.range r, refRowFloor A0 (r - d - 1) :=
    Finset.sum_le_sum hloss
  rw [sum_offRoute_floors] at h1
  have h2 := cleanRouteLoss_lt_budget (A0 := A0) (r := r) (m := m) (etaR := etaR) hA0 hgate
  have h3 : ((∑ d ∈ Finset.range r, loss d : ℕ) : ℝ)
      ≤ ((∑ h ∈ Finset.range r, refRowFloor A0 h : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

end Table

/-! ## §4  Statement poles

A green build sees none of this.  Each of the **first four** items below is a
genuine pole: it shows that a hypothesis of a statement above is load-bearing, or
that a conclusion is not satisfied by its trivial witness.  The **fifth**
(`bobHeavyCount_needs_the_exchange`) is an illustrative arithmetic remark rather
than a pole, and its docstring says so. -/

section Poles

/-- **Pole for `firstBob_child_budget`: the exposed Bob query is load-bearing.**

The extra bit of `09:1306--1308` comes from *answering* the Bob query.  At a leaf
the walk is stationary and the inequality
`cost(child) + 1 <= cost(node)` fails outright, so the theorem's use of the frozen
first stopping rule (`09:1250--1251`, the node exposes a Bob query) is not
decoration. -/
theorem child_budget_needs_the_bob_query :
    ¬ ((descendStep (Protocol.leaf true : Protocol Bool Bool Bool) false).cost + 1
        ≤ (Protocol.leaf true : Protocol Bool Bool Bool).cost) := by
  decide

/-- **Pole for `card_exceptionalFinal`: owner injectivity is load-bearing.**

`09:1551--1552` ("Distinct clean donors have distinct owners") is what makes
`e_T = n_T - |J_good|` an identity.  Without it the image of the owner map can be
strictly smaller than `J_good`, and the frozen subtraction over-counts the
exceptional nodes: here two donors share one owner and the image has one element
rather than two. -/
theorem card_exceptionalFinal_needs_owner_injectivity :
    (({0, 1} : Finset (Fin 2)).image (fun _ => (0 : Fin 2))).card
      ≠ ({0, 1} : Finset (Fin 2)).card := by
  decide

/-- **Pole for `offRoute_rows_lt_childFloor`: cleanness is load-bearing.**

If both Alice children qualify the certificate splits, and then the "off-route"
child does *not* hold fewer than `A_{k-1}` rows -- it holds at least that many, by
the very definition of qualifying.  So `09:1588`'s "Since the certificate remains
clean" is what the bound rests on.  General. -/
theorem offRoute_bound_needs_cleanness {X Y Z : Type*} [Fintype X] [DecidableEq X]
    {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ} {p : List Bool}
    (h1 : Qualifies P R A0 r p true) :
    ¬ ((rowsAt P R (p ++ [true])).card < refRowFloor A0 (r - p.length - 1)) := by
  unfold Qualifies childFloor at h1
  omega

/-- **Pole for `bobCapacity_add_card_finalNodes_le`: `kappa_v = 1` at final nodes
is load-bearing.**

`09:1564`'s `K_B + n_T <= q` counts each final node once because a final Alice node
has capacity exactly one (`09:1250--1252`, `d_v = r`).  A node of capacity two
would be counted once on the left and twice inside Kraft's sum, and the
substitution of `n_T` for the final nodes' capacity total would be false: at
`r = 2` a node of depth `1` already has capacity `2 != 1`. -/
theorem finalNode_count_needs_unit_capacity :
    stoppingCapacity 2 1 = 2 ∧ stoppingCapacity 2 2 = 1 := by
  constructor <;> decide

/-- **Illustrative remark, NOT a pole.**  The declaration name overstates what is
proved here; the upgrade is registered as a next-round item in the ledger.

`eq:wrapper-total-early-mass` bounds `P_B`, a sum over *nodes*; the Bob-heavy
count divides a sum over *donors*.  The two agree only because the mass is doubly
indexed and both aggregations are total, which is precisely what
`earlyMass_eq_sum_firstBobMass` supplies to `wrapperBobHeavyCount_engine`.  The
arithmetic below only *illustrates* the size of the gap -- two first-Bob nodes
each carrying mass `1` from a single donor give per-node masses `1` but a
per-donor total of `2`.

Unlike the four genuine poles above, it mentions no declaration of this module and
negates no inequality that a hypothesis forbids, so it rules nothing out.
*Next round:* replace it by a real pole exhibiting `Pv : Fin 2 -> Fin 1 -> R` whose
every per-node mass is `< 2` while `firstBobMass` at the single donor equals `2`,
so that dropping `earlyMass_eq_sum_firstBobMass` demonstrably breaks
`wrapperBobHeavyCount_engine`'s `htot`. -/
theorem bobHeavyCount_needs_the_exchange :
    ∑ _v ∈ (Finset.univ : Finset (Fin 2)), (1 : ℝ) = 2 ∧ (1 : ℝ) ≠ 2 := by
  constructor
  · simp
  · norm_num

end Poles

/-! ## §5  Non-vacuity at the banked live routed system

**NON-FIDELITY.**  The paper's own instance of this counting head is the routed
certificate system of the *alleged shallow protocol*, which is not built yet; the
canonical-inhabitation obligation for it is registered as GAP-EXPOSED item 3 of
the header and is **not** discharged by anything below.  What follows is a smoke
probe on the banked `FirstBobFrontierInstance.liveSystem` -- itself carrying that
module's own BEYOND-PAPER label for its alphabet and predicates -- chosen so that
every definition of this module is evaluated at a **nondegenerate** point:
`n_T = 2`, `e_B = 1`, `|J_good| = 1`, `e_T = 1`.  Both sides of the frozen
`J_clean = J_good + Bob-heavy` split are nonempty, so no cardinality identity
above is satisfied by an empty case.

**Self-chosen quantities in this section, named explicitly.**  Two values below
are *ours* rather than the paper's, and neither may be read as legal:

* `probeMass`, standing in for `P_v` -- the routing's output on the protected
  reservoirs, GAP-EXPOSED item 3;
* `eta_R = 1`, at which the Bob-heavy threshold is exercised.  `eta_R` is DEFINED
  by `eq:eta-choice` (`06:206--217`) and every legal value is far below `1`; see
  `exceptionalCount_engine_hypotheses_consistent` for the pinned constants.

`q = 4` by contrast is DERIVED (`09:105`, `q = 2^r` at `r = 2`), and `r`, `A_0`,
`e_0` carry `FirstBobFrontierInstance`'s own BEYOND-PAPER AUDIT label. -/

section Probe

/-- The clean donor of the live system routed to the final node `[false, false]`.
Its certificate is the routed descendant of coordinate `0`, computed by the frozen
rule in `FirstBobFrontierInstance.live_descendants_zero`. -/
def probeDonorZero : CertIndex liveProtocol liveRows 1 2 := ⟨0, ⟨[false, false], by decide⟩⟩

/-- The clean donor of the live system routed to the final node `[false, true]`,
from `FirstBobFrontierInstance.live_descendants_one`. -/
def probeDonorOne : CertIndex liveProtocol liveRows 1 2 := ⟨1, ⟨[false, true], by decide⟩⟩

/-- A protected-mass assignment putting all first-Bob mass on the donor from
coordinate `0`.  **Ours**, not the paper's: `P_v` is the routing's output on the
protected reservoirs, which is GAP-EXPOSED item 3.  Its only role is to make both
sides of the frozen Bob-heavy split nonempty. -/
noncomputable def probeMass :
    FrontierNode liveProtocol liveRows 1 2 → CertIndex liveProtocol liveRows 1 2 → ℝ :=
  fun _ x => if x.1 = (0 : Fin 3) then 1 else 0

theorem probe_firstBobMass_zero :
    firstBobMass liveSystem probeMass probeDonorZero = 1 := by
  rw [firstBobMass, live_bobNodes]
  simp [probeMass, probeDonorZero]

theorem probe_firstBobMass_one :
    firstBobMass liveSystem probeMass probeDonorOne = 0 := by
  rw [firstBobMass, live_bobNodes]
  simp [probeMass, probeDonorOne]

/-- Both live donors are clean donors reaching final Alice nodes, i.e. members of
the banked `J_clean`, and there are exactly two of them: the third started
coordinate is stopped at the exposed Bob query and is therefore not in
`J_clean`. -/
theorem probe_cleanFinal_card : liveSystem.cleanFinal.card = 2 := by decide

theorem probe_mem_cleanFinal_zero : probeDonorZero ∈ liveSystem.cleanFinal := by decide

theorem probe_mem_cleanFinal_one : probeDonorOne ∈ liveSystem.cleanFinal := by decide

/-- `n_T = 2` at the live system: the two final Alice nodes of
`FirstBobFrontierInstance.live_finalNodes`. -/
theorem probe_finalNodes_card :
    (liveSystem.toWrapperFrontier.finalNodes).card = 2 := by decide

/-- `lem:final-reference-uniqueness` in counting form, live: no final node of the
audit instance carries two clean certificates. -/
theorem probe_owner_unique :
    ∀ v : FrontierNode liveProtocol liveRows 1 2,
      (liveSystem.cleanFinal.filter fun i => liveSystem.owner i = v).card ≤ 1 := by
  decide

/-- `e_B >= 1`: the coordinate-`0` donor is Bob-heavy at `eta_R = 1`, because all
its protected mass stops at the exposed first-Bob node. -/
theorem probe_bobHeavy_zero : probeDonorZero ∈ bobHeavyDonors liveSystem probeMass 1 := by
  rw [mem_bobHeavyDonors]
  refine ⟨probe_mem_cleanFinal_zero, ?_⟩
  rw [BobHeavy, probe_firstBobMass_zero]
  norm_num

/-- `|J_good| >= 1`: the coordinate-`1` donor is clean and not Bob-heavy. -/
theorem probe_good_one : probeDonorOne ∈ goodDonors liveSystem probeMass 1 := by
  rw [goodDonors, Finset.mem_sdiff]
  refine ⟨probe_mem_cleanFinal_one, ?_⟩
  rw [mem_bobHeavyDonors]
  rintro ⟨-, hheavy⟩
  rw [BobHeavy, probe_firstBobMass_one] at hheavy
  norm_num at hheavy

/-- **The probe is nondegenerate.**

`e_B = 1`, `|J_good| = 1`, `n_T = 2` and `e_T = 1`: every count this module
defines is positive, both sides of the frozen `09:1548` split are inhabited, and
the derived identity `card_exceptionalFinal` fires with **no** empty summand. -/
theorem probe_counts :
    (bobHeavyDonors liveSystem probeMass 1).card = 1
      ∧ (goodDonors liveSystem probeMass 1).card = 1
      ∧ (exceptionalFinal liveSystem probeMass 1).card = 1 := by
  have hsplit := card_goodDonors_add_card_bobHeavy liveSystem probeMass 1
  rw [probe_cleanFinal_card] at hsplit
  have hbh : 1 ≤ (bobHeavyDonors liveSystem probeMass 1).card :=
    Finset.card_pos.mpr ⟨probeDonorZero, probe_bobHeavy_zero⟩
  have hgd : 1 ≤ (goodDonors liveSystem probeMass 1).card :=
    Finset.card_pos.mpr ⟨probeDonorOne, probe_good_one⟩
  have hbh1 : (bobHeavyDonors liveSystem probeMass 1).card = 1 := by omega
  have hgd1 : (goodDonors liveSystem probeMass 1).card = 1 := by omega
  have hexc := card_exceptionalFinal liveSystem probeMass 1 probe_owner_unique
  rw [probe_finalNodes_card, hgd1] at hexc
  exact ⟨hbh1, hgd1, by omega⟩

/-- **Hypothesis consistency for `wrapperTotalEarlyMass_engine`.**

Its two structural binders are simultaneously satisfiable at the live routed
system with `e_0 = 1`: the first-Bob set is nonempty (`hne`), and
`K_B = kappa_v = 2` at the single exposed node, which is at most
`e_0/(1-vartheta) = 16/7` at the frozen `vartheta = 9/16` (`hKB`).  So the
frozen `eq:wrapper-clean-count` bound and a live first-Bob node do not conflict,
and `eq:wrapper-total-early-mass` is not entered on an inconsistent bundle. -/
theorem totalEarlyMass_engine_hypotheses_consistent :
    (liveSystem.toWrapperFrontier.bobNodes).Nonempty
      ∧ liveSystem.toWrapperFrontier.bobCapacity ≤ (1 : ℝ) / (1 - vartheta) := by
  constructor
  · exact ⟨liveBobNode, by rw [live_bobNodes]; simp⟩
  · rw [WrapperFrontier.bobCapacity, live_bobNodes, Finset.sum_singleton,
      live_kappa_attained, one_sub_vartheta]
    norm_num

/-- **Hypothesis consistency for `wrapperExceptionalCount_engine`.**

**BEYOND-PAPER AUDIT values -- explicitly NOT legal ones.**  This instance audits
*our* encoding at a point the paper never visits.  It is strictly weaker evidence
than the paper's own application point and is not a canonical inhabitant; the
canonical obligation stays GAP-EXPOSED item 3.  Value by value:

* `q = 4` is DERIVED, by evaluating `09:105`'s `q = 2^r` at `r = 2`;
* `r = 2` and `A_0 = 1` are inherited from `FirstBobFrontierInstance` under that
  module's own **BEYOND-PAPER AUDIT** label (`r` is DEFINED by `eq:q-deltaU`,
  `06:513--519`, with `09:105`; `A_0` is DEFINED by `09:1219`), as is `e_0 = 1`;
* `vartheta = 9/16` is DEFINED and consumed *by pin*
  (`DenseWrapperFrontier.vartheta`, `09:1268`), never as a numeral;
* `eta_R = 1` is **ours**, and it is illegal by a wide margin.  `eta_R` is DEFINED
  by `eq:eta-choice` (`06:206--217`); `06:228` records
  `0 < eta_R <= eta_C/2 < tau < x_N`, and `eq:fixed-protected-masses`
  (`06:127--138`) pins `tau = 1/92`, `x_N = 1/16` and `mu_Sigma = 1/184`, so the
  first branch of `eq:eta-choice` already forces
  `eta_R <= mu_Sigma/200 = 1/36800`.

What this theorem therefore establishes is only that the binder bundle is
**non-contradictory**, not that it is inhabited legally:
`q - e_0/(1-vartheta) = 4 - 16/7 <= 2 = c`, and `probe_owner_unique` supplies the
uniqueness input, so the conclusion reads `e_T = 1 <= 4 - 2 + 1 = 3` and
`3 <= 16/7 + 1`.  Neither vacuous nor self-contradictory -- and no legality
claim. -/
theorem exceptionalCount_engine_hypotheses_consistent :
    ((exceptionalFinal liveSystem probeMass 1).card : ℝ)
        ≤ (4 : ℝ) - (liveSystem.cleanFinal.card : ℝ)
            + ((bobHeavyDonors liveSystem probeMass 1).card : ℝ)
      ∧ (4 : ℝ) - (liveSystem.cleanFinal.card : ℝ)
            + ((bobHeavyDonors liveSystem probeMass 1).card : ℝ)
          ≤ 1 / (1 - vartheta) + ((bobHeavyDonors liveSystem probeMass 1).card : ℝ) := by
  refine wrapperExceptionalCount_engine liveSystem probeMass 1 probe_owner_unique
    (q := 4) (e0 := 1) (by norm_num) ?_
  rw [probe_cleanFinal_card, one_sub_vartheta]
  norm_num

end Probe

end EthInapproximability.ParameterizedNP.MassRedistributionCounting
