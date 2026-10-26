import EthInapproximability.ParameterizedNP.WrapperLossTable

/-!
# Parameterized NP route: the `u`-dense opening, `09:1742--1744`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche), **lines `09:1742--1744` and nothing
  else**:

  "If `delta_0 >= 1`, the strict pigeonhole conclusion preceding
  `eq:wrapper-terminal-density` is itself impossible.  We may therefore assume
  `delta_0 < 1`, and hence `u_don >= 8s`."

* **Cross-anchors opened first-hand in the frozen file for this tranche:**
  * `09:1717--1718`, **the defining display of `u_don`**: "`u_don` is the least
    power of two satisfying `u_don delta_0 >= 8s`".  This is the *only* frozen
    definition of `u_don`, and it is what makes the accessor reading below
    legitimate: `u_don` is the paper's own least-power-of-two search, run at the
    paper's own `delta_0`.  `06:726--728` defines `u_term` at the **different**
    density `delta_term` and is **not** a defining display for `u_don`; it is
    cited nowhere in this module.
  * `eq:wrapper-terminal-density` (display `09:1710--1713`, label `09:1712`),
    `delta_0 = eta_R/(8 e_T mu_P)`, banked as
    `WrapperMassRedistribution.deltaZero`.
  * `09:1038`, **the defining display of `s`**: "put `r_3 = log_2 s`", i.e.
    `s = 2^{r_3}`.  This is where the canonical firing below takes its `s`; it is
    the same identification the pinned
    `WrapperLossTable.canonical_terminalDonorGate` already makes at its own
    `(sv := 2 ^ r_3)`.  No numeral is assigned to `s`.
  * `eq:wrapper-terminal-donor-gate` (display `09:1736--1741`, label `09:1740`),
    landed at the canonical routed system by the predecessor tranche as
    `WrapperLossTable.canonical_terminalDonorGate` and consumed here **by pin**
    -- its statement is not restated, re-proved, or weakened, and its hypothesis
    bundle is carried through verbatim.
  * `09:1704`, "Assume then that `e_T > 0`", the frozen branch assumption, which
    stays the binder `heTpos` it is in the pinned predecessor.  It is *not*
    fused with the `09:1702` leg: `09:1702` and `09:1704` are two frozen cases
    of one construction and the predecessor's `Pole 4` records why conjoining
    them would be a defect.
  * `09:1746--1781`, the paragraph this module deliberately stops before: the
    poor-`u_don` projection cover, `lem:template-coordinate-extraction`, the
    block supply `eq:wrapper-terminal-block-supply`, `kappa = 2 s q_2`, and
    call (iv) of `sec:extension-call-ledger`.  **None of it is entered, and
    `eq:wrapper-u-dense` is neither stated nor implied.**
  * `06-parameter-schedule.tex` (SHA-256
    `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
    recomputed first-hand this tranche) for the banked accessors
    `ParameterSchedule.uTerm`, `ParameterSchedule.ET`, `ParameterSchedule.EB`
    and `ParameterSchedule.deltaTerm` that the pinned gate carries.

* **Reader counterpart: NONE claimable, inherited.**  Checked first-hand this
  tranche over `routes/parameterized-np/reader-facing/sections/`: the 41-page
  reader artifact carries no item stating `09:1742--1744`.  Its only passage
  covering this material is `A-stage4-details.tex:370--399`, running prose whose
  single displayed endpoint (`A-stage4-details.tex:393--395`) is
  `D_U(1; 1 - delta_U, theta) >= C + r_q`, carries no label, and is stated by no
  declaration below.  The READER-COUNTERPART rule forbids citing prose and
  forbids reusing another declaration's item, so none is cited rather than one
  invented.

## What this module adds, and what it deliberately does not

`09:1742--1744` was already landed **generally** by
`OwnerFamilyToPigeonhole.terminal_uDon_floor` and its wired form
`uDon_floor_of_owner_family`, in the shape the banked
`WrapperMassRedistribution.uDon_ge_eight_s` fixes: `u_don` a bare `{uDon : N}`
binder and its frozen defining demand `8 s <= u_don delta_0` an explicit
**hypothesis** `hdef`.  That form is strictly weaker and was correct for its
round.

**What is new here is that `hdef` is discharged.**  Read as `09:1717--1718`
writes it -- `u_don` the least power of two with `u_don delta_0 >= 8s`, i.e. the
banked accessor `ParameterSchedule.uTerm` evaluated at
`eq:wrapper-terminal-density`'s `delta_0` -- the defining demand is a *theorem*
(`ParameterSchedule.uTerm_spec` at `WrapperMassRedistribution.deltaZero_pos`),
not an assumption.  So the frozen floor `u_don >= 8s` holds of the paper's own
`u_don` outright, with only the frozen branch input `delta_0 <= 1` left.

That is also the reason the accessor, and not a free binder, is the right reading
at the wrapper site: the pinned `canonical_terminalDonorGate` already carries
`u_don` as that same accessor in its second clause, so before this tranche the
gate's `u_don` and the pigeonhole leg's `u_don` were **two different symbols**.
Section 3 makes them one.

No new `structure`, `def`, `abbrev`, `instance` or `axiom` is declared, no banked
statement is restated, and no banked hypothesis is weakened.  Every declaration
below is a `theorem`.

**Canonical inhabitation: INHERITED, REGISTERED and DEFERRED.**  This module
declares no new type, so it opens no new canonical-inhabitation obligation.  The
inherited one cannot be discharged here for the reason the predecessor records:
the paper's own instance of every statement below is a function of the alleged
shallow protocol of `09:1187--1193`, which by the argument's own design does not
exist.  Nothing below evaluates a schedule parameter or carries a numeral of its
own, with the single exception of the explicitly labelled rejection probe in
Section 4, which claims **no** legality.
-/

namespace EthInapproximability.ParameterizedNP.WrapperUDenseOpening

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
open EthInapproximability.ParameterizedNP.WrapperLossTable

/-! ## Section 1  `09:1744` at the paper's own `u_don`, with `hdef` DISCHARGED

"We may therefore assume `delta_0 < 1`, and hence `u_don >= 8s`."

`u_don` is read as `09:1717--1718` writes it -- "the least power of two
satisfying `u_don delta_0 >= 8s`" -- i.e. as the banked least-power-of-two
accessor `ParameterSchedule.uTerm` evaluated at `eq:wrapper-terminal-density`'s
`delta_0`.  At that reading the frozen defining demand is the banked
`ParameterSchedule.uTerm_spec`, available at `0 < delta_0`
(`WrapperMassRedistribution.deltaZero_pos`), and the frozen floor follows from
the banked `WrapperMassRedistribution.uDon_ge_eight_s` with nothing assumed about
`u_don` at all.

`06:726--728` is **not** cited: that display fixes `u_term` against
`delta_term = eta_R/(8 mu_P max{1, E_T})`, a different quantity of a different
display; only `09:1715--1716`'s relational `u_don <= u_term` connects the two
searches, and that relation is banked as
`WrapperMassRedistribution.uDon_le_uTerm` and is not used here. -/

section Accessor

/-- **`09:1744` at the accessor: `u_don >= 8s`, with the defining demand proved.**

The frozen floor, over the banked `WrapperMassRedistribution.deltaZero` and the
banked `ParameterSchedule.uTerm`.  Its only remaining input is the frozen branch
hypothesis `delta_0 <= 1` of `09:1742--1743`.

*What is derived rather than assumed.*  `hdef`, the `09:1717--1718` defining
demand `8 s <= u_don delta_0`, which every previously banked form of this step
carried as a hypothesis.

*Why this is not a restatement.*  `uDon_ge_eight_s` is general in a free
`{uDon : N}` and is silent about which naturals meet `hdef`; this theorem names
the paper's own one and proves that it does.  The two statements have different
content: instantiating the banked one at this `u_don` still leaves `hdef` open.

*Why `heT` is load-bearing.*  At `e_T = 0` the frozen `delta_0` is Lean's total
division by zero, `uTerm_spec` is unavailable, and the conclusion fails for every
`s >= 1`.  `09:1704`'s branch assumption is therefore a genuine input here.

General in `s`, `e_T` and `eta_R`. -/
theorem uDonAccessor_floor {s eT : ℕ} {etaR : ℝ} (hetaR : 0 < etaR) (heT : 0 < eT)
    (hd1 : deltaZero etaR eT ≤ 1) :
    8 * s ≤ ParameterSchedule.uTerm s (deltaZero etaR eT) :=
  uDon_ge_eight_s hd1 (ParameterSchedule.uTerm_spec (deltaZero_pos hetaR heT))

end Accessor

/-! ## Section 2  `09:1742--1744` whole, at a routed system

The frozen branch is not assumed away: `delta_0 <= 1` is the banked
`OwnerFamilyToPigeonhole.deltaZero_le_one_of_selected`, i.e. `09:1742`'s "the
strict pigeonhole conclusion preceding `eq:wrapper-terminal-density` is itself
impossible" executed against an actual selected donor.  The hypotheses below are
exactly that banked theorem's, in its binder order, plus the positivity
`09:1704` supplies. -/

section RoutedSite

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **`09:1742--1744` at a routed system, at the paper's own `u_don`.**

From the `eq:wrapper-terminal-density` endpoint of `09:1708--1713` -- a common
reservoir type `ty`, a terminal node `T_*`, a nonempty selection, and
`delta_0 <= dens ty j T_*` on it -- together with the fact that `dens` is a
relative density, the frozen floor `u_don >= 8s` holds of the accessor.

*What is derived rather than assumed.*  Both halves of `09:1742--1744`: the
branch `delta_0 <= 1` (banked `deltaZero_le_one_of_selected`) and the defining
demand `hdef` (Section 1).  Only `09:1704`'s `e_T > 0` and the `09:1708--1713`
endpoint remain hypotheses.

*Why the trivial reading fails.*  The conclusion is an inequality between two
fixed naturals, not an existential; at `s >= 1` it is false for the least power
of two computed at a density exceeding one (Section 4's rejection probe), so it
is not available from the accessor's definition alone.

**Nothing beyond `09:1744`.**  The projection cover, the coordinate extraction,
the block supply and the Extension call of `09:1746--1781` are not entered.
General. -/
theorem uDonAccessor_floor_of_selected (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool)
    {s : ℕ} (hetaR : 0 < etaR)
    (heT : 0 < (exceptionalFinal S Pv etaR).card)
    (hsel : (selectedDonors S Pv etaR dens Tstar ty).Nonempty)
    (hdelta : ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty,
      deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ dens ty j Tstar)
    (hdens1 : ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty, dens ty j Tstar ≤ 1) :
    8 * s ≤ ParameterSchedule.uTerm s
      (deltaZero etaR (exceptionalFinal S Pv etaR).card) :=
  uDonAccessor_floor hetaR heT
    (deltaZero_le_one_of_selected S Pv dens Tstar ty hsel hdelta hdens1)

end RoutedSite

/-! ## Section 3  The opening at the canonical routed system

`eq:wrapper-terminal-donor-gate` and the `09:1742--1744` floor at **one** site,
with `u_don` **one** symbol.  The gate is the pinned
`WrapperLossTable.canonical_terminalDonorGate`, consumed as a proof term with its
hypothesis bundle carried through verbatim; the floor is Section 2 at
`FrontierIndexing.canonicalSystem`.

`s` is `2^{r_3}`, the frozen `09:1038` identification ("put `r_3 = log_2 s`"),
which is also the `s` the pinned gate carries; the two are the *same* expression
here, which is the point of the section.  `E_B`, `E_T`, `delta_term`, `u_term`,
`B_theta` and `L_q` are the banked accessors the pinned gate already carries.
**No numeral is assigned to any schedule quantity.**

*What is added to the pinned bundle.*  Exactly the `09:1708--1713` endpoint --
`dens`, `T_*`, `ty`, the nonempty selection, its `delta_0` lower bound, and the
relative-density upper bound -- i.e. the hypotheses of the banked
`deltaZero_le_one_of_selected`, unweakened and in its binder order.  Nothing in
that set is derivable from the pinned bundle, and `heTpos` is not derivable from
it either (`T_*` is not required to be exceptional), so no binder restates
another.

*What is still a binder.*  Everything the predecessor left as one, verbatim:
`hLocExCC`/`hLocExEP` (**EXPANDER-001**), `hfinal`, `halleged`, `hcost`, `hres`,
`hinj`, `hhost`, `he0`, `residual`/`hresidual`/`hladder`, the gate system
`hgates`, `he0m`, and `09:1704`'s own `heTpos`.  **No hypothesis is added to any
banked endpoint and none is weakened.  Full-bundle satisfiability is not
claimed.**

*No route completion.*  `eq:wrapper-u-dense` is neither stated nor implied, and
`09:1746--1781` remains open. -/

section CanonicalOpening

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-terminal-donor-gate` and `09:1742--1744` at the canonical
system, at one and the same `u_don`.**

`|J_good| > q/2`, `u_don B_theta < q/(4 E_T)`, and `u_don >= 8 s` at
`s = 2^{r_3}` (`09:1038`), with `u_don` the `09:1717--1718` least-power-of-two
search read at `eq:wrapper-terminal-density`'s `delta_0` in **all** clauses that
mention it.

*What is derived rather than assumed.*  The first two clauses are the pinned
predecessor endpoint (which itself derives `hjgood`, `e_T <= E_T`, `E_T >= 1`,
`B_theta >= 1`, `u_don <= u_term` and both gate rows); the third adds
`09:1742--1743`'s branch and `09:1717--1718`'s defining demand, both proved.

*Why the trivial witness fails.*  The conclusion is a conjunction of two strict
inequalities and one floor between fixed naturals and reals -- not an
existential.  The predecessor's `gate_rows_are_load_bearing` and
`second_clause_fails_at_zero_ET` refute the first two clauses from weaker data,
and Section 4's `density_bound_is_load_bearing` refutes the third at a density
above one.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet `Yc`,
the Alice carrier `X`, and in every width and schedule quantity. -/
theorem canonical_uDenseOpening {RwN : Type*} [Fintype RwN]
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
      (Btheta θ) trefv)
    -- `09:1708--1713`, the `eq:wrapper-terminal-density` endpoint: a common
    -- reservoir type, a terminal node, and a nonempty selection carrying
    -- `delta_0` as a lower bound on a genuine relative density
    (dens : Bool → CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    (Tstar : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (ty : Bool)
    (hsel : (selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty).Nonempty)
    (hdelta : ∀ j ∈ selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty,
      deltaZero etaR (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card
        ≤ dens ty j Tstar)
    (hdens1 : ∀ j ∈ selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty,
      dens ty j Tstar ≤ 1) :
    (q : ℝ) / 2 < ((goodDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ∧ ((ParameterSchedule.uTerm (2 ^ r₃)
            (deltaZero etaR
              (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card) : ℕ) : ℝ)
          * ((Btheta θ : ℕ) : ℝ)
        < (q : ℝ) / (4 * ((ParameterSchedule.ET e0m
            (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) : ℕ) : ℝ))
      ∧ 8 * 2 ^ r₃
        ≤ ParameterSchedule.uTerm (2 ^ r₃)
            (deltaZero etaR
              (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card) := by
  -- `eq:wrapper-terminal-donor-gate` at the canonical system, consumed by pin
  have hgateOut := canonical_terminalDonorGate Nmat Gmat ιR hsub halleged hcomp hR certOpt
    isRestrEP Scol YT Pv donor d₀ d₁ ell bsel hdepth hinj hres hC hcost hq hmem hk hq4 hX hYc
    hθ0 hθ1
    hgate hbase htcert hE1cc hE2cc hLocExCC hcover B hB plc hblock hplace hfinal hqpos hk₂
    hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0 hSep hYT hgap hQuery hBlocks hx0 hx1 htx
    hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep hrows hSelectEP hLocExEP hne hetaR he0 hhost
    residual hresidual hladder he0m heTpos hgates
  -- `09:1742--1744` at the same `u_don`, Section 2
  exact ⟨hgateOut.1, hgateOut.2,
    uDonAccessor_floor_of_selected (canonicalSystem hcomp hR) Pv dens Tstar ty hetaR
      heTpos hsel hdelta hdens1⟩

end CanonicalOpening

/-! ## Section 4  Aux-lemma battery

Five general checks.  **Canonical inhabitation is INHERITED, REGISTERED and
DEFERRED** per the header: this module declares no new type, so it opens no new
obligation, and the inherited one cannot be discharged because the paper's own
instance of every statement above is a function of the alleged shallow protocol
of `09:1187--1193`, which does not exist.

Battery 4 is an explicitly labelled **rejection probe**: it claims no legality
and exists only to show that the `delta_0 <= 1` guard of Section 1 fires. -/

section Battery

/-- **Battery 1 (the donor width grows with the slot count).**

`09:1717--1718` demands `u_don delta_0 >= 8s`, so a larger `s` needs a wider
donor product at a fixed density.  The banked `uTerm_antitone` is the *other*
axis (fixed `s`, varying density); this is the missing monotonicity in `s`, and
it is what makes the frozen substitution `s = 2^{r_3}` of `09:1038` a
*strengthening* of the demand rather than a change of statement.  General. -/
theorem uTerm_mono_slots {s s' : ℕ} {d : ℝ} (hd : 0 < d) (hss : s ≤ s') :
    ParameterSchedule.uTerm s d ≤ ParameterSchedule.uTerm s' d := by
  have hsR : (s : ℝ) ≤ (s' : ℝ) := by exact_mod_cast hss
  have hinv : (0 : ℝ) ≤ d⁻¹ := le_of_lt (inv_pos.mpr hd)
  have hkey : 8 * (s : ℝ) / d ≤ 8 * (s' : ℝ) / d := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) hinv
  simp only [ParameterSchedule.uTerm]
  exact leastPowTwoGe_mono hkey

/-- **Battery 2 (the frozen adjective survives the floor).**

`09:1717--1718` says `u_don` is the least **power of two** meeting the demand,
and `09:1746--1752` immediately spends that adjective (it halves `u_don` at
`09:1751` and indexes `C_2^{u_don/2}` at `09:1752`).  So the floor of Section 1
must be compatible with dyadic form, not merely with size: the same natural is
simultaneously `2^e` and at least `8s`.

*Why the trivial witness fails.*  The first conjunct pins `e` to the accessor's
own exponent -- the existential is a named-def claim about
`ParameterSchedule.uTerm`, not a free choice -- and the second conjunct is then a
statement about that pinned value, false at `e = 0` for every `s >= 1`.
General. -/
theorem uDonAccessor_isPowTwo_ge {s eT : ℕ} {etaR : ℝ} (hetaR : 0 < etaR) (heT : 0 < eT)
    (hd1 : deltaZero etaR eT ≤ 1) :
    ∃ e : ℕ, ParameterSchedule.uTerm s (deltaZero etaR eT) = 2 ^ e ∧ 8 * s ≤ 2 ^ e := by
  obtain ⟨e, he⟩ := ParameterSchedule.uTerm_isPowTwo s (deltaZero etaR eT)
  refine ⟨e, he, ?_⟩
  rw [← he]
  exact uDonAccessor_floor hetaR heT hd1

/-- **Battery 3 (the two conclusions are jointly informative).**

The floor `u_don >= 8s` and the gate `u_don B_theta < q/(4 E_T)` are not
independent decorations: together they force `32 s E_T < q`, i.e. the wrapper
width really does dominate the slot count against the terminal majorant.  This is
the joint non-vacuity check for Section 3's conjunction -- a conjunction of two
clauses about the *same* `u_don` says strictly more than either clause about two
unrelated symbols, which is the defect Section 3 exists to remove.  General over
abstract reals. -/
theorem floor_and_gate_force_width {sv u Bt qv Ev : ℝ}
    (hEv : 0 < Ev) (hBt : 1 ≤ Bt) (hu : 0 ≤ u)
    (hfloor : 8 * sv ≤ u) (hgate : u * Bt < qv / (4 * Ev)) :
    32 * sv * Ev < qv := by
  have h1 : u ≤ u * Bt := by nlinarith
  have h2 : 8 * sv < qv / (4 * Ev) := by linarith
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * Ev)] at h2
  have heq : 8 * sv * (4 * Ev) = 32 * sv * Ev := by ring
  rw [heq] at h2
  exact h2

/-- **Battery 4 (REJECTION PROBE, claims no legality): the `delta_0 <= 1` guard
fires.**

`09:1742--1743` spends a sentence discharging `delta_0 >= 1` precisely because
the floor is false there.  At the density `8` -- which
`eq:wrapper-terminal-density` attains at `eta_R = 64 e_T mu_P` -- the least power
of two meeting `u delta_0 >= 8s` at `s = 1` is `1`, and `8 <= 1` fails.  So
`hd1` in Section 1 is load-bearing and not bookkeeping.

**This is a rejection probe at self-chosen values and claims nothing about legal
parameters**: it exhibits the guard firing on input the frozen branch excludes,
which is the one use of self-chosen values the witness rule permits. -/
theorem density_bound_is_load_bearing :
    ParameterSchedule.uTerm 1 8 = 1 ∧ ¬ (8 * 1 ≤ ParameterSchedule.uTerm 1 8) := by
  have hexp : ParameterSchedule.leastPowTwoExp (8 * ((1 : ℕ) : ℝ) / 8) = 0 :=
    Nat.le_zero.mp (ParameterSchedule.leastPowTwoExp_le (by norm_num))
  have hval : ParameterSchedule.uTerm 1 8 = 1 := by
    rw [ParameterSchedule.uTerm, ParameterSchedule.leastPowTwoGe, hexp, pow_zero]
  refine ⟨hval, ?_⟩
  rw [hval]
  norm_num

/-- **Battery 5 (BEYOND-PAPER AUDIT: the frozen branch of `09:1743` is reachable
at every tolerance).**

`delta_0 <= 1` is a hypothesis of Sections 1--3, so it must not be vacuous.  It
is not: for every positive tolerance `eta_R` there is a positive exceptional
count at which `eq:wrapper-terminal-density`'s own `delta_0` lies at or below
one.  The witness is the paper's own quantity `eta_R/(8 mu_P)` rounded up by
`Nat.le_ceil` -- a closed form in `eta_R` and the frozen reservoir mass, never a
numeral -- so nothing here assigns a value to a source-defined quantity.

This is a satisfiability statement about the branch hypothesis, **not** the
paper's instance; the canonical-inhabitation obligation stays REGISTERED and
DEFERRED and this lemma is explicitly not offered as its discharge.  General. -/
theorem deltaZero_le_one_is_reachable {etaR : ℝ} (hetaR : 0 < etaR) :
    ∃ eT : ℕ, 0 < eT ∧ deltaZero etaR eT ≤ 1 := by
  have hmu : 0 < muP := muP_pos
  have h8 : (0 : ℝ) < 8 * muP := by linarith
  refine ⟨⌈etaR / (8 * muP)⌉₊ + 1, Nat.succ_pos _, ?_⟩
  have hc : (0 : ℝ) ≤ ((⌈etaR / (8 * muP)⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ ((⌈etaR / (8 * muP)⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hceil : etaR / (8 * muP) ≤ ((⌈etaR / (8 * muP)⌉₊ + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil (etaR / (8 * muP))
    push_cast
    linarith
  rw [div_le_iff₀ h8] at hceil
  have hden : (0 : ℝ) < 8 * ((⌈etaR / (8 * muP)⌉₊ + 1 : ℕ) : ℝ) * muP := by
    nlinarith [hn1, hmu]
  rw [deltaZero, div_le_one hden]
  nlinarith [hceil]

end Battery

end EthInapproximability.ParameterizedNP.WrapperUDenseOpening
