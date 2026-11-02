import EthInapproximability.ParameterizedNP.FirstBobLightClosure

/-!
# Parameterized NP route: the closure arc's `hselect` supply (`09:1287--1296`)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand this tranche), with
  `sections/A-certified-stopping.tex`
  (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`,
  recomputed first-hand this tranche).
* **The exact frozen lines traced here**, in print order:
  * **`09:434--440`**, "For the small-capacity calls put `rho = 2y^2 = 18/25`,
    `u_2 = 2`, `u_kappa = kappa/2 + 1` (`4 <= kappa < t_ref`)";
  * **`09:442--444`**, the cover clause -- "For every dyadic
    `2 <= kappa < t_ref`, take one maximal-matching cover of the coordinate sets
    of size `u_kappa` whose projection density is below `rho`" -- which is the
    exact range the binder `hcover` below is quantified over, and no wider;
  * **`09:1268--1269`, the split**, read at its printed non-strict inequality, so
    the boundary `kappa_v = t_ref` belongs to branch (i);
  * **`09:1269--1276`, branch (i)**, "follow the denser Bob child and invoke the
    certified-scale reference stopping lemma on `G`";
  * **`09:1276--1296`, branch (ii)**, `ell_v = log_2 kappa_v`, the represented
    count `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`, "Every represented
    coordinate is outside `E_0`, so the parent projection to any selected
    `u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob
    child retains density at least `y^2`", the `A_{ell_v} = kappa_v A_0
    >= 2 kappa_v x_T m_G` reference rows and the trim "to the row density
    `kappa_v x_T`";
  * **`09:1296--1300`**, the substitution `M = G`, `H = C-1`, `x = x_T`, `z = y`,
    `ell = ell_v` into `lem:certified-row-ladder`;
  * **`09:1307--1308`**, "Its lower bound is one more bit than the remaining
    child budget in the alleged protocol.  Therefore";
  * **`09:1309--1313`, `eq:wrapper-first-bob-light`**, display `09:1310`, label
    `09:1312`.
* **Cross-anchors opened first-hand this tranche:** `09:105--107` (the ambient
  `U = interlaceOp(N, q)`), `09:113--116` (`m_G = |Rows(G)|`), `09:311--313`
  (specified-coordinate projection), `09:322` (`h = theta`), `09:1188--1193` (the
  alleged `(C+r-1)`-bit protocol and `09:1190`'s bracket member), `09:1219`
  (`A_0 = ceil(2 x_T m_G)`), `09:1235--1236` (the start rule), `09:1250--1252`
  (the exposure rule), `09:1255--1257` (`kappa_v = 2^{r-d_v}` at `09:1255`, `W_v`
  at `09:1257`), `A:109--146`
  (`thm:certified-localized-extension`, with the `A:138--144` readout clause).
* **Reader counterpart:** none is claimed.  The 41-page reader artifact carries
  no item stating either conjunct below; per the predecessor's first-hand search
  `A-stage4-details.tex:394` is explicitly *not* claimable for this material, and
  the READER-COUNTERPART rule forbids citing prose or reusing another
  declaration's item.

## What this tranche does

`FirstBobLightClosure` (tranche `cc-t5m-r1`) landed **two** deliverables:

* `canonical_firstBobLight_closure_at_a_bracket_member` (its Section 3):
  `09:1310`'s display at a first-Bob node, unconditional in `09:1269`'s capacity
  split, carrying two named binders -- `hLocEx` (branch (i)) and **`hselect`**
  (branch (ii), `09:1287--1296`, GAP-EXPOSED);
* `branchOne_closure_carries_the_projected_column_density` (its Section 4): the
  same display **on branch (i) only** -- guarded by `hcap : k_ref <= r - d_v` --
  conjoined with `09:311--313`'s projected column density at the frozen ambient
  carrier `Y = Fin q -> Yc` of `09:105--107`.

`SelectEmbedComposition.hselect_of_reference_construction` (tranche `cc-t5g-r1`)
is the one-term composition that **proves** branch (ii)'s selection step from the
reference construction of `09:105--123`: `projection_at_a_node ->
nodeProjection_transport_density -> hselect_of_trims_and_projection`, with
`2^{ell_v} = kappa_v`, the selection equivalence, the ambient section and the
interlace identity supplied rather than assumed.  Its conclusion is *exactly*
`hselect`'s consequent, existential in the child bit.

**This module connects the two arcs.**  The single declaration below is the
closure with `hselect` **discharged**: it appears nowhere in the statement, and
`hselect_of_reference_construction` appears in the proof term.  What the
statement records instead is the reference construction itself -- `Nmat`, `Gmat`,
`ιR`, `hsub`, `halleged`, the cover of `09:442--444`, the trims `B` with their
`09:1294--1296` floor, and the placement `plc` -- which is data of `09:105--123`,
not an assumption about the argument's own conclusion.

### The dispatch, and why it is *not* branch-(ii)-only

`SelectEmbedComposition`'s own re-fires (`firstBobLight_of_reference_construction`
and its `_at_paper_schedule` twin) carry `hsmall : kappa_v < t_ref` as a
hypothesis, so they close **branch (ii) only** and leave branch (i) to a separate
firing.  This module does **not** repeat that shape.  It performs `09:1269`'s
split itself, at the banked `TranscriptLevelConstruction.frontier_branch_dichotomy`
and in the printed orientation (the boundary `kappa_v = t_ref` goes to branch
(i)):

* on `t_ref <= kappa_v` the **Section 4 deliverable** is fired, at
  `hcap` obtained from the banked `tRef_le_kappaFrontier_iff`; `hselect` is not
  needed there and the composition is not invoked;
* on `kappa_v < t_ref` that inequality **is** `hsmall`, so the composition
  applies, and the **Section 3 deliverable** is fired at the bit the composition
  returns.

So the conclusion carries no capacity guard, and `hcover` is quantified over
`Finset.Ico 1 k_ref` -- exactly `09:442--444`'s "for every dyadic
`2 <= kappa < t_ref`" and not one dyadic index more.  Demanding covers at
`l >= k_ref` would be an over-strong hypothesis the frozen text does not supply,
and it is deliberately not demanded: see `cover_window_is_the_frozen_dyadic_range`
in Section 2.

### The existential bit is obtained, never fixed

`hselect_of_reference_construction` concludes `∃ b, ...` and the banked closure
takes `b` as an input whose *only* use is `hselect`; its conclusion is `b`-free.
The proof therefore `obtain`s the bit from the existential and instantiates the
closure at that bit.  Fixing a literal would be a defect: the banked
`RoutingDynamics.projection_denserChild_needs_the_right_bit` exhibits a Bob query
sending every column to the `true` child, where the bound at `false` fails
outright.  (The one literal that does appear -- `false` in the branch where
`09:1283`'s count fails -- is not a choice of denser child: in that branch the
binder is discharged vacuously, so its bit is irrelevant and the closure's
`b`-free conclusion is unaffected.)

### `09:1283`'s count is decided, never hoisted

`smallCopyWidth (kappa_v) <= |representedCoords v|` is **not** a hypothesis
below.  It is decided inside the proof by `by_cases`: the positive branch enters
the composition, and the negative branch discharges the banked implication-shaped
`hselect` slot against its own failed antecedent.  Hoisting it past
`TranscriptLevelJoin.cover_of_heavy` -- the banked derivation of that very
inequality from heaviness (`09:1280--1283`) -- was the defect the `cc-t5g` gate
recorded, and it is not reintroduced here.

### What is NOT discharged

`hLocEx` -- `thm:certified-localized-extension` (`A:109--146`), the place
**EXPANDER-001** would enter -- stays an explicit named binder, in the frozen
theorem's own universal shape over the routed triple, byte-identical in
re-association to `FirstBobLightClosure.lean`'s.  It is never an `axiom`, never a
premise-bundle field and never an opaque certificate.  Nothing here proves
`thm:first-wrapper`, and `hE1`, `hE2`, `htcert` remain the `06` binders that
`eq:tref-search` (`06:558--572`, whose following prose at `06:574--578` names the
hypotheses its terms verify) discharges at `k_ref >= 2^19`.

### Why ONE supplied form and not two

Both banked deliverables are consumed -- Section 4's in the branch-(i) arm of the
proof term, Section 3's in the branch-(ii) arm -- and both of their conclusions
appear, as the two conjuncts of the statement below.  A *second* declaration
carrying Section 3's conclusion alone would not be a second supplied form: the
supply itself forces `Y := Fin q -> Yc`, `Z := Bool`, `Cl := Yc` and
`Rw := X` (the composition's conclusion is an inequality about the **same**
`LambdaGE Gmat`, so the reference matrix's carriers and the closure's must
coincide), which spends the only axis -- generality in `Y`, `Z` and `Cl` -- on
which Section 3 is not implied by Section 4.  At the ambient carrier the two
supplied forms would have *identical* hypotheses, with one the first conjunct of
the other, and `1 <= |Cl|` and `0 < |Fin q -> Yc|` both collapse into the single
`hYc`.  That is a duplicate, and it is not landed.  Consumers wanting only
`09:1310`'s display take `.1`.

## Statement-content and dependency notes

* **Widths.** `q` is FREE throughout: `09:105`'s `q = 2^r` is one instance of the
  quantified form, never a pin.  The second interlace width `Q` does not occur.
* **Carriers.** `Coord := StartedCoord E_0` is `09:1235--1236`'s start rule as a
  type (`SelectEmbedComposition` Section 1), so "every represented coordinate is
  outside `E_0`" (`09:1287`) is a theorem of the carrier and not a binder;
  `m_G` is read at `Fintype.card X` (`09:113--116`); `A_0` is
  `initialRefRows (xTdepth bT) (Fintype.card X)`, the reified `09:1219`.
* **`Rw := X` is inherited, not introduced.**  The composition is general in the
  reference matrix's row carrier `Rw`, but the banked closure already states `G`
  at `Gmat : X -> Cl -> Bool` -- that is the `m_G = Fintype.card X` reading of
  `09:113--116` fixed by the `cc-t4l-r1` repair, and it is what makes
  `LambdaGE Gmat` the *same* quantity on both sides of the supply.  So the
  instantiation is forced by the parent's convention; the placement
  `plc : StartedCoord E_0 -> X -> X` of `09:1291--1296` remains an arbitrary map
  and no row is identified with any input.
* **Defined quantities are evaluated, never assigned.** `vartheta = 9/16`
  (`09:1268`, the `DenseWrapperFrontier` twin, **not** `ParameterSchedule`'s),
  `u_kappa = kappa/2 + 1` (`09:438--440`, the banked `smallCopyWidth`),
  `rho = 2y^2 = 18/25` (`09:434--436`, the banked `rhoSmall`) and the retained
  child density `y^2 = (3/5)^2` at the DEFINED `y = 3/5` all arrive through the
  banked definitional chain.  No numeral is chosen for any of them here.
* **Imports.** The sole import is `FirstBobLightClosure`, whose transitive
  closure already contains `SelectEmbedComposition` (the chain is
  `SelectEmbedComposition -> FrontierBundleConstruction ->
  FrontierProjectionSupply -> AliceOnlyHdensSupply -> FirstBobLightClosure`), so
  both parents are reached without widening the axiom surface.
  `LegacyNPCC.Stage12` is **not** in that closure, so the cited AGHP
  balanced-family axiom is unreachable from every declaration here.  No `axiom`,
  no opaque certificate, no premise bundle, and no new structure.

## Canonical inhabitation

**REGISTERED and DEFERRED, inherited unchanged.**  The paper's own instance of
this statement is a function of the *alleged* protocol of `09:1188--1193`, whose
non-existence is the conclusion of the whole argument, so no paper instance can
be exhibited and none of Section 2's probes discharges the obligation.  The one
probe below that evaluates numerals is labelled **NON-FIDELITY / BEYOND-PAPER**
and claims no legality; the remaining four checks are general and evaluate
nothing.
-/

namespace EthInapproximability.ParameterizedNP.ClosureSelectSupply

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

/-! ## §1  The closure with `hselect` supplied

`09:1269`'s split dispatched to the two banked closure deliverables, with
branch (ii)'s selection step supplied by the banked composition instead of
assumed. -/

section Supply

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) with `hselect` discharged,
together with `09:311--313`'s projected column density.**

At a first-Bob node `v` of `FrontierIndexing.canonicalSystem` over the start-rule
carrier `StartedCoord E_0` (`09:1235--1236`), lying on coordinate `i`'s route, at
the frozen ambient `Y = Fin q -> Yc` of `09:105--107`, with
`A_0 = ceil(2 x_T m_G)` (`09:1219`) and a member of `09:1190`'s `p = 1` bracket
family at column parameter `theta`:

* `W_v < vartheta kappa_v` -- `09:1310`'s display, **at both branches of
  `09:1269`**; and
* for every selected coordinate set `J`, the projection of the retained outer
  column set has at least `theta . |Yc|^{|J|}` columns -- `09:311--313`'s
  "Its normalized density remains at least `theta`, by specified-coordinate
  projection", which is `h = theta` at `09:322`.

**The two banked closure deliverables are the two arms of the proof.**  On
`t_ref <= kappa_v` -- the boundary included, exactly as `09:1269`'s non-strict
inequality assigns it -- `FirstBobLightClosure`'s Section 4 deliverable fires and
returns *both* conjuncts at once, with its `hcap` obtained from
`tRef_le_kappaFrontier_iff` rather than assumed.  On `kappa_v < t_ref` that
strict inequality is the composition's branch-(ii) entry condition `hsmall`, the
paper's remaining `2 <= kappa_v` at `09:1276--1277` being supplied by the same
dichotomy from `09:1259`; so `SelectEmbedComposition.hselect_of_reference_construction`
supplies the binder and `FirstBobLightClosure`'s Section 3 deliverable fires at
the child bit it returns; the density conjunct is the banked
`AliceOnlyHdensSupply.branch_one_column_density_at_a_bracket_member`, which needs
no capacity guard.

**What is genuinely different from the predecessors.**  Against Section 3: the
`hselect` binder is gone, replaced by the reference construction of
`09:105--123` (`Nmat`, `Gmat`, `ιR`, `hsub`, `halleged`, `hcover`, `B`, `hB`,
`plc`, `hblock`, `hplace`) -- data, not an assumption about the conclusion.
Against Section 4: the capacity guard `hcap` is gone, so the display holds at
every first-Bob node and not only on branch (i).  Against
`SelectEmbedComposition`'s own two re-fires: those carry `hsmall` and close
branch (ii) only; this one carries no branch hypothesis at all.  `hLocEx`
survives verbatim -- `A:109--146`, where **EXPANDER-001** would enter -- and so do
`hE1`, `hE2` and `htcert`.

**`09:1283`'s count is not a hypothesis.**  It is decided inside the proof;
neither hoisting nor weakening occurs.

*Why the trivial witness fails.*  Neither conjunct is existential, so the
question is whether either can fail at all, and both can.  The first is false at
the banked `TranscriptLevelJoin.splitAudit` routed system, whose first-Bob node
meets the heavy threshold with equality `W_v = 9 = vartheta . 16`
(`TranscriptLevelJoin.splitAudit_is_not_light`), so it is not an arithmetic
tautology; the second is not free of `hmem`, since the banked
`FrontierProjectionSupply.projected_rho_does_not_supply_hdens_at_rho` exhibits a
column set satisfying a projection form while the ambient density fails.
Full-bundle satisfiability is **not** claimed -- the paper's instance is a
function of the alleged protocol -- and
`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`
shows why no finite firing of the analytic binders is available.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet
`Yc`, the Alice carrier `X`, in `q`, `r`, `b_T`, `k_ref`, `C`, `t_cert`, `E_0`,
the node, the coordinate, the bracket member, the retained column set, the trims,
the placement, and the real parameters `x_U` and `theta`. -/
theorem closure_and_projected_density_of_reference_construction {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (i : StartedCoord E0)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
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
    (hLocEx : ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
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
    (B : StartedCoord E0 → Finset X)
    (hB : ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B j).card)
    (plc : StartedCoord E0 → X → X)
    (hblock : ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B j, plc j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        < vartheta
          * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
      ∧ ∀ J : Finset (Fin q),
          θ * (Fintype.card Yc : ℝ) ^ J.card
            ≤ ((nodeProjection P (rootColumnSet RC.2) J v.val).card : ℝ) := by
  classical
  have hY : 0 < Fintype.card (Fin q → Yc) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact pow_pos hYc q
  rcases frontier_branch_dichotomy hcomp hR hv kref with ⟨hge, -⟩ | ⟨-, hlt, -⟩
  · -- Branch (i), `09:1269--1276`: the Section 4 deliverable returns both conjuncts.
    exact branchOne_closure_carries_the_projected_column_density Gmat P R i hcomp hR v hv hroute
      hmem hk ((tRef_le_kappaFrontier_iff r v.val.length kref).mp hge) hq4 hX hYc hθ0 hθ1 hC
      hgate hbase htcert hE1 hE2 hcost hLocEx
  · -- Branch (ii), `09:1276--1306`: the composition supplies `hselect`.
    refine ⟨?_, fun J => branch_one_column_density_at_a_bracket_member P R hroute hmem J hYc⟩
    by_cases hcnt :
        smallCopyWidth (kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v)
          ≤ (representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v).card
    · obtain ⟨b, hsel⟩ := hselect_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR
        v hv (by simpa only [tRef_eq] using hlt) hcover B hB plc hblock hplace hcnt
      exact canonical_firstBobLight_closure_at_a_bracket_member Gmat P R i b hcomp hR v hv hroute
        hmem hk hq4 hX hY hYc hθ0 hθ1 hC hgate hbase htcert hE1 hE2 hcost hLocEx (fun _ => hsel)
    · exact canonical_firstBobLight_closure_at_a_bracket_member Gmat P R i false hcomp hR v hv
        hroute hmem hk hq4 hX hY hYc hθ0 hθ1 hC hgate hbase htcert hE1 hE2 hcost hLocEx
        (fun h => absurd h hcnt)

end Supply

/-! ## §2  Aux-lemma battery, non-vacuity and the statement poles

Four general checks on the dispatch this tranche performs, plus one labelled
reachability probe.  Canonical inhabitation of the paper's own object is
INHERITED, REGISTERED and DEFERRED per the header: `09:1190`'s bracket member and
the reference construction both belong to the **alleged** protocol of
`09:1188--1193`, which does not exist, so no paper instance can be exhibited and
nothing below discharges the obligation. -/

section Battery

/-- **Battery 1 (the dispatch is exhaustive and exclusive).**

Every frontier capacity falls in exactly one of the two arms of Section 1's
proof: the branch-(i) entry `t_ref <= kappa_v` of `09:1269` and the branch-(ii)
entry `kappa_v < t_ref` of `09:1276--1277`, the latter being literally the
composition's `hsmall`.  So no node is left unserved and none is served twice --
which is what makes the supplied statement carry no capacity guard.

General in `r`, the node depth and `k_ref`; nothing is evaluated. -/
theorem supply_dispatch_is_exhaustive_and_exclusive (r d kref : ℕ) :
    (tRef kref ≤ kappaFrontier r d ∧ ¬ kappaFrontier r d < 2 ^ kref)
      ∨ (kappaFrontier r d < 2 ^ kref ∧ ¬ tRef kref ≤ kappaFrontier r d) := by
  rcases Nat.lt_or_ge (kappaFrontier r d) (2 ^ kref) with h | h
  · exact Or.inr ⟨h, by simpa only [tRef_eq] using Nat.not_le.mpr h⟩
  · exact Or.inl ⟨by simpa only [tRef_eq] using h, Nat.not_lt.mpr h⟩

/-- **Battery 2 (the cover window is exactly the frozen dyadic range).**

`09:442--444` supplies one maximal-matching cover "For every dyadic
`2 <= kappa < t_ref`", and nothing beyond.  Section 1's binder `hcover` is
quantified over `Finset.Ico 1 k_ref`; this identifies that index set with the
frozen range, so the hypothesis is neither narrower than what the composition
consumes nor -- the live risk -- wider than what the paper supplies.  A cover
demanded at `l >= k_ref` would be an over-strong hypothesis, and this lemma is
the check that none is.

General in `k_ref` and `l`; nothing is evaluated. -/
theorem cover_window_is_the_frozen_dyadic_range (kref l : ℕ) :
    l ∈ Finset.Ico 1 kref ↔ (1 ≤ l ∧ 2 ^ l < tRef kref) := by
  simp only [Finset.mem_Ico, tRef_eq]
  exact and_congr_right fun _ => (Nat.pow_lt_pow_iff_right (by norm_num)).symm

/-- **Battery 3 (the boundary is assigned to branch (i)).**

`09:1269` prints the non-strict `kappa_v >= t_ref`, so the boundary case
`kappa_v = t_ref` belongs to the certified-scale branch and **not** to the
selection branch -- the composition is never invoked there.  This is a fidelity
check on the direction of the printed inequality: reading `09:1269` strictly
would send the boundary into a branch whose covers `09:442--444` does not supply.

General in `r`, the node depth and `k_ref`; nothing is evaluated. -/
theorem boundary_node_is_served_by_branch_one (r d kref : ℕ)
    (h : kappaFrontier r d = tRef kref) :
    tRef kref ≤ kappaFrontier r d ∧ ¬ kappaFrontier r d < 2 ^ kref := by
  refine ⟨h.ge, ?_⟩
  rw [h]
  simp only [tRef_eq]
  exact lt_irrefl _

/-- **Battery 4 (monotonicity: branch (ii) is closed downward in depth).**

`kappa_v = 2^{r-d_v}` (`09:1255`) decreases as the node deepens, so once a
first-Bob node enters the selection branch every deeper node of the same routed
system does too.  This is the sanity property the dispatch needs in order to be a
property of the *node* rather than an accident of the split: it rules out an
encoding in which the two arms interleave along a root-to-leaf path.

General in `r`, both depths and `k_ref`; nothing is evaluated. -/
theorem branch_two_is_downward_closed_in_depth {r d d' kref : ℕ} (hd : d ≤ d')
    (h : kappaFrontier r d < 2 ^ kref) : kappaFrontier r d' < 2 ^ kref := by
  refine lt_of_le_of_lt ?_ h
  simp only [kappaFrontier_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Battery 5 (both arms of the dispatch are reachable).**

A dispatch whose branches cannot both occur would make Section 1's split
decoration, and a green build cannot see the difference.  At the smallest
exponent the banked guards allow, `k_ref = 4` with `k_ref + 2 <= r` forcing
`r >= 6`, both arms occur at two admissible depths of one and the same `r`:
depth `2` gives `kappa_v = 16 = t_ref`, the boundary, which Battery 3 assigns to
branch (i); depth `3` gives `kappa_v = 8`, which satisfies `09:1259`'s
`kappa_v >= 2` and lies strictly inside branch (ii).

**NON-FIDELITY / BEYOND-PAPER.**  This audits *our* dispatch at a point the
frozen paper never visits and claims no legality.  `4` is not a paper value: it
is the boundary of the Lean-visible guard `hk`, whereas `k_ref` is DEFINED by
`eq:tref-search` (`06:558--572`) as the least integer meeting
`k_ref >= max{2^19, ...}`, whence `k_ref >= 2^19 = 524288`, five orders of
magnitude away and beyond any decidable instance; and `A:117` with `A:26` forces
`t_ref >= t_cert = 2^{2^20}`.  Correspondingly `r = 6` is only the smallest value
`hq4` permits at that boundary.  The two depths `2` and `3` are ours as well.
Nothing here discharges the deferred canonical-inhabitation obligation, and the
analytic binders `hE1`, `hE2` and `hLocEx` are **not** inhabited: the banked
`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`
proves `hE2` is false at `k_ref = 4` for every `theta <= 1`. -/
theorem both_dispatch_arms_are_reachable :
    (tRef 4 ≤ kappaFrontier 6 2 ∧ ¬ kappaFrontier 6 2 < 2 ^ 4)
      ∧ (2 ≤ kappaFrontier 6 3 ∧ kappaFrontier 6 3 < 2 ^ 4
          ∧ ¬ tRef 4 ≤ kappaFrontier 6 3)
      ∧ (4 : ℕ) ≤ 4 ∧ (4 : ℕ) + 2 ≤ 6 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by norm_num, by norm_num⟩

end Battery

end EthInapproximability.ParameterizedNP.ClosureSelectSupply
