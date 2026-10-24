import EthInapproximability.ParameterizedNP.FrontierSumAssembly
import EthInapproximability.ParameterizedNP.MassRedistributionCounting

/-!
# Parameterized NP route: the protected-early closure fired at the frontier

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines `09:1367--1534`**.
* **The exact frozen lines traced here**, in print order:
  * **`09:1367--1368`**, `\subsubsection{Protected mass cannot stop early}` /
    `sec:wrapper-protected-early`;
  * **`09:1370--1376`**, the two protected row reservoirs "each of mass
    `mu_P = 1/184` relative to the `m` rows of one copy of `N`", and the donor
    functional: "For a first-Bob node `v` and a donor set `J_0 subseteq [q]`, let
    `P_v(J_0)` denote, normalized by `m`, the protected mass from those donors
    reaching `v`";
  * **`09:1378--1384`**, the block constants `rho_0`, `rho_1`, `B_theta`, `L_q`;
  * **`lem:early-protected-closure`** (label `09:1419`, statement
    `09:1418--1430`) with **`eq:protected-early-threshold`** (display
    `09:1421--1425`, the inequality at `09:1422--1423`) and its proof
    `09:1432--1510`, whose endpoint identity is `09:1505--1507`
    `Bcap + log_2 K_int = C + log_2 kappa - 1`;
  * **`09:1512--1513`**, `\subsubsection{Mass redistribution and completion of
    scale alignment}` / `sec:wrapper-mass-redistribution`;
  * **`09:1515--1517`**, "By `lem:wrapper-no-bob-completion`, every retained
    protected row from every donor reaches exactly one first-Bob node or one
    final Alice-frontier node.  Thus the mass decomposition below has no omitted
    early-leaf term";
  * **`09:1519--1525`**, "Let `J_clean` be the `c` outer coordinates whose clean
    reference certificates reach final Alice nodes.  Apply the contrapositive of
    `lem:early-protected-closure` at every first-Bob node, with
    `J_0 = J_clean`.  Such a node has `kappa_v >= 2`, and the conclusion of the
    lemma would exceed its remaining child budget";
  * **`eq:wrapper-total-early-mass`** (display `09:1526--1533`, label
    `09:1534`): `P_B < 128 mu_P B_theta L_q s K_B <= 128 mu_P B_theta L_q s
    e_0/(1-vartheta)` -- the **strict** first line at `09:1528--1529` and the
    **non-strict** second line at `09:1530--1531`.
* **Cross-anchors opened first-hand this tranche:** `09:105` (`q = 2^r`),
  `09:447--451` (`E_0` and `e_0 = |E_0|`, display `09:450`), `09:855` with
  `09:1038` (`C = D_2 + log_2 s + 1`, the frozen terminal target),
  `09:1187--1193` (the alleged `(C+r-1)`-bit protocol), `09:1196`
  (`lem:wrapper-no-bob-completion`), `09:1250--1257` (the stopping rule, `d_v`,
  `kappa_v = 2^{r-d_v}`, `W_v`), `09:1259--1266`
  (`eq:wrapper-frontier-conservation`), `09:1268` (`vartheta = 9/16`),
  `09:1346--1350` (the final-node classification and the frozen names `K_B`,
  `c`, `ell`), `09:1352--1357` (`eq:wrapper-clean-count`), `09:1535--1547`
  (`eq:wrapper-bob-heavy-count`, the *next* frozen step: only the **quantity**
  named at `09:1537`, `sum_v P_v({j})`, is reached, and only as the definitional
  readout of Battery 4b -- the threshold `eta_R/4` of `09:1538`, the Bob-heavy
  classification and the count itself at `09:1541--1547` are deliberately NOT
  reached here) and `06:1864--1894` (`s = 2^{h_s}`).
* **Reader counterpart:** **none is claimed.**
  `routes/parameterized-np/reader-facing/sections/A-stage4-details.tex:370--399`
  was opened first-hand this tranche and is the only reader passage covering this
  material.  It is running prose -- "The complete owner--donor count is finite:
  it uses only the fixed reservoir masses above ... It is expanded line by line
  in the ultra-explicit companion" -- and its one displayed endpoint
  (`A-stage4-details.tex:394`) is `eq:wrapper-u-dense`, which is *not* stated
  here.  The READER-COUNTERPART rule forbids citing prose and forbids reusing an
  item already assigned to another declaration, so none is cited rather than one
  invented.  This matches the inherited outcome recorded for
  `FRONTIER-SUM-ASSEMBLY-001`.

## Census first: what was already banked, and what this tranche adds

The declared range `09:1367--1534` was censused line by line against the banked
tree before a single line was written.

* `09:1370--1384` -- `mu_P = 1/184`, `rho_0`, `rho_1`, `B_theta`, `L_q`.
  **BANKED** as `WrapperProtectedEarly.muP`, `.rhoZero`, `.rhoOne`, `.Btheta`,
  `.Lq` (`WRAPPER-PROTECTED-EARLY-001`).  Consumed **by pin**; that module is not
  opened for edit and nothing of it is restated.
* `lem:template-coordinate-extraction` (`09:1388--1416`).  **BANKED** as
  `WrapperProtectedEarly.templateCoordinateExtraction`.
* `lem:early-protected-closure` (`09:1418--1510`).  **BANKED** as
  `WrapperProtectedEarly.earlyProtectedClosure`.
* `09:1515--1517`, the no-omitted-early-leaf decomposition.  **BANKED** as
  `WrapperMassRedistribution.protectedMass_two_term` over the banked
  `DenseWrapperFrontier.sum_bobNodes_add_sum_finalNodes`.
* `09:1519--1525`, the contrapositive **in its budget form**.  **BANKED** as
  `WrapperMassRedistribution.firstBob_protectedMass_lt` and, at a routed system,
  `MassRedistributionCounting.firstBob_earlyMass_lt_frozen` -- but only with the
  frozen lemma's conclusion carried as an `hclosure` *binder*.
* `eq:wrapper-total-early-mass` (`09:1526--1534`).  **BANKED as an engine**:
  `MassRedistributionCounting.wrapperTotalEarlyMass_engine`, with **both** of its
  two inputs -- the per-node strict bound `hlt` and the `K_B` replacement `hKB`
  -- carried as binders.

**The gap this tranche closes is exactly those two binders.**  Nothing above is
re-proved, re-stated, or weakened; what is new is that

1. `hlt` is **obtained** at every first-Bob node by firing the banked
   `earlyProtectedClosure` in an actual proof term (Section 3), rather than
   assumed -- the contrapositive of `09:1519--1525` performed, not postulated;
   and
2. `hKB` is **obtained** at the canonical routed system from the banked
   `eq:wrapper-clean-count` (Section 4), rather than assumed.

Both retirements happen at the site that consumes them, which is the only place a
binder can be retired.

## What is asserted, and what is not

`eq:wrapper-total-early-mass` **is** asserted, in both of its frozen lines, and it
is genuinely derived:

* the first line (`09:1528--1529`, **strict** `<`) is Section 5, the per-node
  bounds of Section 3 summed over the first-Bob nodes by the banked engine;
* the second line (`09:1530--1531`, **non-strict** `<=`) is Section 6, where the
  `K_B` of the first line is replaced by `e_0/(1-vartheta)` through the banked
  `eq:wrapper-clean-count`.

Neither guard direction is flipped: `09:1529` is strict here and `09:1531` is
non-strict here.  Section 5 is stated with the `hKB` slot still open so that the
strict line is available over an abstract routed system; Section 6 is the frozen
display at the canonical system with that slot closed.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:262--263`) is
neither stated nor implied.  `09:1535--1781` -- the Bob-heavy donor count
`eq:wrapper-bob-heavy-count`, the exceptional-final count, the terminal
pigeonhole, call (iv), and the final contradiction -- remains **OPEN**.  Nothing
on the spine (Sections 1--6) touches it, and the one declaration below that
reaches into that range at all -- Battery 4b -- states only the definitional
readout of the quantity `09:1537` names: no threshold, no classification, no
count, and `eta_R` does not occur anywhere in this module.

## GAP-EXPOSED, explicitly

* `hLocEx` (`thm:certified-localized-extension`, `A:109--146`), the entry point
  of **EXPANDER-001**, survives as an explicit named binder in **both** bundles
  -- the protected-closure bundle of Section 3 and the clean-count bundle of
  Section 4.  It is never an `axiom`, never a premise-bundle field, never an
  opaque certificate.
* `hfinal` (`09:1346--1350`, licensed by `lem:final-reference-uniqueness`
  `09:1315--1318`, banked as
  `DenseWrapperFrontier.wrapperFinalReferenceUniqueness` with its own unwired
  `hladder` binder) likewise stays an explicit binder in Section 4 and Section 6.
* `hE1`, `hE2`, `htcert`, `halleged`, `hcost`, `hQuery`, `hBlocks`, `hbase`,
  `hres` are explicit binders.
* `hres` (Section 1) is the frozen reservoir readout of `09:1370--1376`: the mass
  a clean donor sends to `v` is `mu_P` times the two retained reservoir
  densities.  It is a *definitional* reading of `P_v`, carried as a binder rather
  than baked into a structure field.
* **Full-bundle satisfiability is NOT claimed** anywhere in this module, and no
  probe below is presented as a fidelity witness.  Section 3's bundle is the
  banked one, whose block-level consistency is the banked
  `WrapperProtectedEarly.earlyProtectedClosure_block_bundle_is_consistent`;
  Section 4's is the banked clean-count bundle.

## Axiom surface

The imports are `FrontierSumAssembly` and `MassRedistributionCounting`, whose
transitive closures reach `ClosureSelectSupply`, `FrontierIndexing`,
`DenseWrapperFrontier`, `WrapperProtectedEarly`, `WrapperMassRedistribution`,
`SplitFirstBobInstance` and `ParameterSchedule`.  `LegacyNPCC.Stage12` is **not**
in that closure, so the cited AGHP balanced-family axiom is unreachable from every
declaration here.  No `axiom`, no opaque certificate, no premise bundle, no new
`structure`, `abbrev` or `instance` is declared.

## Defined-vs-free

Every quantity this module substitutes is **DEFINED** in the frozen source and is
reached by evaluating the definitional chain, never by assignment:

* `mu_P = 1/184` (`09:1370--1373`) -- the banked `WrapperProtectedEarly.muP`;
* `B_theta`, `L_q` (`09:1380--1382`) -- the banked `.Btheta`, `.Lq`;
* `128 mu_P B_theta L_q s` (`09:1423`, `09:1529`) -- the banked
  `WrapperMassRedistribution.earlyMassCoeff`;
* `s = 2^{h_s}` (`06:1864--1894`) -- carried as the dyadic `2^{r_3}`, matching the
  banked `earlyProtectedClosure`'s own exponent form;
* `kappa_v = 2^{r-d_v}` (`09:1255`) -- the banked
  `DenseWrapperFrontier.WrapperFrontier.capacity`, read out by
  `MassRedistributionCounting.capacity_eq_two_pow`;
* `C = D_2 + log_2 s + 1` (`09:855` with `09:1038`) -- the banked
  `TerminalTwoStream.terminalTarget`, which is why Section 6 substitutes
  `terminalTarget bcap r_2 r_3` for `C` rather than carrying a free `C`;
* `e_0 = |E_0|` (`09:450`) -- evaluated, not assigned, by the banked
  `FrontierSumAssembly.startedCoord_census_evaluates_e_zero` inside `D4`;
* `vartheta = 9/16` (`09:1268`) -- the `DenseWrapperFrontier` twin, which is the
  one `eq:wrapper-clean-count` and `eq:wrapper-total-early-mass` use, pinned
  against the schedule homonym by the banked
  `FrontierSumAssembly.vartheta_twins_agree`.

The module declares **no numeral without banked or frozen pedigree**, and the
only place it instantiates a schedule parameter at all is the guard-level
**Battery 6** of Section 7, at the banked probe family's own values
(`k_2 = 5`, `r_2 = 13`, `r_3 = 2`, `ell = 1`, the tuple of
`WrapperProtectedEarly.extensionCallThree_floorTier_instance` -- a
**FLOOR-TIER, BEYOND-PAPER** probe, not a schedule point: the round-`r2` name
`extensionCallThree_legal_instance` and its legality claim were **withdrawn** by
the `cc-t6e` repair, because `s = 2^{r_3} = 4` meets the Section-4 floor but not
`eq:s-choice` (`06:112--120` with `06:394--395`), which forces `s >= 512` with
`64 | s`); `Bcap` is given no
value there or anywhere else in the module, because `07:156` `Bcap := D + a`
makes it a source-**DEFINED** quantity.  Nothing on the spine (Sections 1--6)
instantiates any schedule parameter.  Only the first interlace width `q` occurs;
the second interlace width `Q` does not, as it must not at Section 9.

## Canonical inhabitation

**REGISTERED and DEFERRED, inherited unchanged.**  This module declares no new
type, so it opens no new inhabitation obligation.  The inherited one cannot be
discharged as mathematics: the paper's own instance of every statement below is a
function of the **alleged** protocol of `09:1187--1193`, whose non-existence is
the conclusion of the whole subsection, so the frozen paper exhibits no routed
instance by construction.  The battery below is general apart from the
guard-level Battery 6, which instantiates the schedule exponents at the banked
witness family's own values and at none of its own; no declaration below presents
a synthetic object as a fidelity witness.
-/

namespace EthInapproximability.ParameterizedNP.ProtectedEarlyClosure

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
open EthInapproximability.ParameterizedNP.ClosureSelectSupply
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.MassRedistributionCounting

/-! ## §1  The reservoir readout of `P_v` (`09:1370--1376`)

"Each outer coordinate contains two protected row reservoirs, each of mass
`mu_P = 1/184` relative to the `m` rows of one copy of `N`.  For a first-Bob node
`v` and a donor set `J_0 subseteq [q]`, let `P_v(J_0)` denote, normalized by `m`,
the protected mass from those donors reaching `v`."

Two frozen index conventions meet here and must be reconciled *by a proof*, not by
a coincidence of names.  The banked counting spine indexes donors by the routed
system's certificate index (a clean donor is a clean reference certificate,
`09:1519`); the banked `earlyProtectedClosure` indexes them by the outer
coordinate `j in [q]`, because its ambient product is `Y^q`.  `09:1519`'s
"`J_clean` ... the `c` outer coordinates whose clean reference certificates reach
final Alice nodes" is exactly the statement that the first indexing maps
**injectively** into the second, which is what `donor` and `hinj` carry below. -/

section Reservoirs

variable {ι V : Type*} {q : ℕ}

/-- **`09:1370--1376`, `P_v(J_0)` decomposed into its two reservoirs.**

`P_v(J_0) = mu_P * (sum_j d_0(j) + sum_j d_1(j))`, where `d_0` and `d_1` are the
retained relative densities of the two protected reservoir types of the outer
coordinate `donor j` -- the very `d_j in [0,1]` that `09:1434--1436` names at the
start of the frozen proof.

Reindexing along `donor` is where `09:1519`'s injectivity is spent: the frozen
sentence says `J_clean` *is* a set of outer coordinates, one per clean
certificate, and `Finset.sum_image` needs precisely that.

This is the identity that makes the banked
`MassRedistributionCounting.donorMass` -- the aggregate the counting spine sums
-- the same real number as the `sum_j d_j` the banked `earlyProtectedClosure`
consumes.  Without it the two banked modules could only be juxtaposed, never
composed.

General in the donor index, the node type and the width; nothing is evaluated. -/
theorem donorMass_eq_reservoirs (Pv : V → ι → ℝ) (donor : ι → Fin q)
    (d₀ d₁ : Fin q → ℝ) (J₀ : Finset ι) (v : V)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hres : ∀ j ∈ J₀, Pv v j = muP * (d₀ (donor j) + d₁ (donor j))) :
    donorMass Pv J₀ v
      = muP * ((∑ j ∈ J₀.image donor, d₀ j) + (∑ j ∈ J₀.image donor, d₁ j)) := by
  classical
  have h0 : (∑ j ∈ J₀.image donor, d₀ j) = ∑ j ∈ J₀, d₀ (donor j) :=
    Finset.sum_image hinj
  have h1 : (∑ j ∈ J₀.image donor, d₁ j) = ∑ j ∈ J₀, d₁ (donor j) :=
    Finset.sum_image hinj
  rw [h0, h1, donorMass, Finset.sum_congr rfl hres, ← Finset.sum_add_distrib,
    Finset.mul_sum]

/-- **`09:1375`, `J_0 subseteq [q]`, as a theorem of the carrier.**

The banked `earlyProtectedClosure` carries `hJ : J_0.card <= q`.  After the
reindexing of `donorMass_eq_reservoirs` that hypothesis is not an assumption at
all: the image lives in `Fin q`, whose carrier has exactly `q` elements.  It is
discharged here so that Section 3 never has to carry it.

General. -/
theorem donorImage_card_le (donor : ι → Fin q) (J₀ : Finset ι) :
    (J₀.image donor).card ≤ q := by
  classical
  simpa using Finset.card_le_univ (J₀.image donor)

end Reservoirs

/-! ## §2  The threshold of `eq:protected-early-threshold` is the coefficient of
`eq:wrapper-total-early-mass` (`09:1423` against `09:1529`) -- **by pin**

`09:1423` reads `128 mu_P B_theta L_q s kappa`; `09:1529` reads
`128 mu_P B_theta L_q s K_B`.  The banked
`WrapperMassRedistribution.earlyMassCoeff` is the common factor
`128 mu_P B_theta L_q s`, and the banked `earlyProtectedClosure` states its
threshold at the dyadic `s = 2^{r_3}`, `kappa = 2^{ell}` of the frozen schedule
(`06:1864--1894` for `s`, `09:1253--1255` for `kappa_v`).  The checked identity
that lets the two be the same inequality is therefore

```
earlyMassCoeff theta q s * kappa
  = 128 * muP * Btheta theta * Lq q * s * kappa,
```

and that identity is **already banked**, in this fully general form, as
`WrapperMassRedistribution.earlyMassCoeff_threshold`.  It is consumed **by pin**
at its use site in Section 3, at `s := 2^{r_3}` and `kappa := 2^{ell}`; this
module declares no local copy of it.  A dyadic specialization would add nothing
to the banked statement and would be a restatement of a strictly more general
banked interface, which fixed-interface discipline forbids.  This section
therefore contributes no declaration -- only the pin. -/

/-! ## §3  The contrapositive **performed** at one first-Bob node
(`09:1519--1525` against `lem:early-protected-closure`)

"Apply the contrapositive of `lem:early-protected-closure` at every first-Bob
node, with `J_0 = J_clean`.  Such a node has `kappa_v >= 2`, and the conclusion of
the lemma would exceed its remaining child budget."

The banked `MassRedistributionCounting.firstBob_earlyMass_lt_frozen` does the
budget arithmetic but takes the frozen lemma's conclusion as an `hclosure`
binder.  Here that binder is **discharged**: `hclosure` is produced by applying
the banked `WrapperProtectedEarly.earlyProtectedClosure` to the very threshold
hypothesis the contrapositive hands it. -/

section PerNode

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}

/-- **`09:1519--1525`, the contrapositive of `lem:early-protected-closure`,
performed.**

At a first-Bob node `v` of a routed certificate system, the protected mass
`P_v(J_0)` from the donor set `J_0` is **strictly** below the frozen threshold
`128 mu_P B_theta L_q s kappa_v` of `eq:protected-early-threshold`.

*What is discharged.*  The banked `firstBob_earlyMass_lt_frozen` needs
`hclosure : threshold <= P_v(J_0) -> C + ell - 1 <= cost(child)`.  That
implication is `lem:early-protected-closure` itself, and it is supplied here by
an actual application of the banked `earlyProtectedClosure`, through three
bridges, each of which is a frozen identity rather than an assumption:

* the mass bridge, `donorMass_eq_reservoirs` (`09:1370--1376`);
* the coefficient bridge, the banked
  `WrapperMassRedistribution.earlyMassCoeff_threshold` (`09:1423`), consumed by
  pin at `s = 2^{r_3}`, `kappa = 2^{ell}`;
* the endpoint bridge, `09:1505--1507`'s
  `Bcap + log_2 K_int = C + log_2 kappa - 1`, which is why `C` is the banked
  `TerminalTwoStream.terminalTarget bcap r_2 r_3` (`09:855`, `09:1038`) and
  not a free natural number.

*What is derived, not assumed.*  `kappa_v >= 2` -- the frozen side condition of
`09:1522` -- is **not** a hypothesis: `hdepth` is `09:1253`'s `d_v + ell = r` and
the routed system's own `firstBob_spec` gives `d_v < r`, so `1 <= ell` follows,
i.e. `kappa_v = 2^{ell} >= 2`.  So does `hJ : J_0.card <= q`
(`donorImage_card_le`).  The remaining child budget is the banked
`firstBob_child_budget`, reached inside `firstBob_earlyMass_lt_frozen`.

*Why the trivial witness fails.*  The conclusion is not existential and not a
formal truth: it is a strict upper bound on a quantity the hypotheses do not bound
directly, and it is false without the budget contradiction -- the banked
`WrapperMassRedistribution.firstBob_protectedMass_lt` is where that contradiction
lives, and the banked `MassRedistributionCounting.child_budget_needs_the_bob_query`
is the pole showing the budget step is load-bearing.

The binder list is the banked `earlyProtectedClosure`'s own, unchanged except that
its `ell` is this node's `ell`, its `child` is this node's Bob child, its `hthr`
is discharged, and its donor set is the reindexed `J_0`.  `hLocEx` is carried
verbatim. -/
theorem firstBob_protectedMass_lt_of_earlyClosure
    (S : RoutedSystem P Coord ι V r A0) {v : V} (hv : S.firstBob v = true)
    {Ycol : Type*} [Fintype Ycol] [DecidableEq Ycol]
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    (isRestr : Protocol X Y Z → ℕ → ℕ → ℝ → Prop)
    {q k₂ b₁ r₂ r₃ ℓ bcap tcert selCard rowsPerBlock : ℕ}
    {θ lamT x epsProd : ℝ}
    (Scol : Finset (Fin q → Ycol)) (YT : Finset Ycol)
    (Pv : V → ι → ℝ) (J₀ : Finset ι) (donor : ι → Fin q) (d₀ d₁ : Fin q → ℝ)
    (b : Bool)
    -- `09:1253`, `d_v + ell = r`; with `firstBob_spec` this gives `kappa_v >= 2`
    (hdepth : (S.node v).length + ℓ = r)
    -- the reservoir readout of `09:1370--1376` and the `09:1519` reindexing
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hres : ∀ j ∈ J₀, Pv v j = muP * (d₀ (donor j) + d₁ (donor j)))
    -- the alleged protocol's budget (`09:1187--1193`) at the frozen `C`
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    -- the banked `earlyProtectedClosure` bundle, verbatim
    (hq : 0 < q) (hθ0 : 0 < θ)
    (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hbcap : 2 ≤ bcap)
    (hd₀0 : ∀ j ∈ J₀.image donor, 0 ≤ d₀ j)
    (hd₀1 : ∀ j ∈ J₀.image donor, d₀ j ≤ 1)
    (hd₁0 : ∀ j ∈ J₀.image donor, 0 ≤ d₁ j)
    (hd₁1 : ∀ j ∈ J₀.image donor, d₁ j ≤ 1)
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hY : 0 < Fintype.card Ycol) (hYT0 : 0 < YT.card)
    (hS : θ * (Fintype.card Ycol : ℝ) ^ q ≤ (Scol.card : ℝ))
    (hYT : lamT * (Fintype.card Ycol : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ (u : ℕ) (J : Finset (Fin q)), J.card = u →
        ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Ycol)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ Scol)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1 : ∀ (e R : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ⌈((2 : ℝ) ^ (r₃ + ℓ + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊
        ≤ rowsPerBlock)
    -- `09:1499--1504`, the round-`r4` selection binder, gated on the very
    -- threshold whose contrapositive this theorem takes: below the threshold the
    -- frozen proof selects nothing, so no restriction is produced and the
    -- inherited endpoint is not applicable
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- The extraction re-gate of the banked statement is forwarded verbatim: the
    -- `09:1499` selection fires only on the output of `09:1458--1471`.
    (hSelect : earlyMassCoeff θ q (2 ^ r₃) * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ)
          ≤ donorMass Pv J₀ v →
        ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
          ExtractionOutput Scol YT e →
          isRestr (descendStep (descend P (S.node v)) b)
            ((2 : ℕ) ^ (r₃ + ℓ + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
              (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocEx : ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Protocol X Y Z),
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        0 < x → x ≤ 1 →
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R →
        (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        isRestr w blocks rowsEach colDens →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsEach →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ w.cost) :
    donorMass Pv J₀ v
      < earlyMassCoeff θ q (2 ^ r₃) * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  classical
  have hlen : (S.node v).length < r := (S.firstBob_spec v hv).2.2
  have hℓ1 : 1 ≤ ℓ := by omega
  have hcap : S.toWrapperFrontier.capacity v = 2 ^ ℓ := by
    rw [MassRedistributionCounting.capacity_eq_two_pow]
    congr 1
    omega
  refine MassRedistributionCounting.firstBob_earlyMass_lt_frozen S hv hC hcost b ?_
  intro hthr
  have hthrFrontier := hthr
  rw [hcap] at hthr
  have hthr' :
      128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)
        ≤ muP * ((∑ j ∈ J₀.image donor, d₀ j) + (∑ j ∈ J₀.image donor, d₁ j)) := by
    rw [← donorMass_eq_reservoirs Pv donor d₀ d₁ J₀ v hinj hres,
      ← WrapperMassRedistribution.earlyMassCoeff_threshold θ q (2 ^ r₃)
        (((2 ^ ℓ : ℕ) : ℝ))]
    exact hthr
  have hconc :=
    earlyProtectedClosure (q := q) (ℓ := ℓ) Mmat (fun p : Protocol X Y Z => p.cost)
      (descendStep (descend P (S.node v)) b) isRestr Scol YT (J₀.image donor) d₀ d₁
      hq hℓ1 hθ0 hk₂ hk₂le hbcap (donorImage_card_le donor J₀)
      hd₀0 hd₀1 hd₁0 hd₁1 hthr' hGate hY hYT0 hS hYT hgap hQuery hBlocks
      hx0 hx1 htx hMne hbase htcert heps0 heps1 hE1 hE2 hrows
      (fun _ => hSelect hthrFrontier) hLocEx
  have hconc' :
      TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ
        ≤ (descendStep (descend P (S.node v)) b).cost + 1 := hconc
  have hrl : r - (S.node v).length = ℓ := by omega
  rw [hrl]
  omega

end PerNode

/-! ## §4  `K_B <= e_0/(1-vartheta)` at the canonical system (`09:1355` feeding
`09:1530--1531`)

The second line of `eq:wrapper-total-early-mass` replaces `K_B` by
`e_0/(1-vartheta)`, and `09:1355` -- the second inequality of
`eq:wrapper-clean-count` -- is the only thing that licenses it.

Both halves of that supply are banked in the `cc-t5o` assembly and are consumed
here **in actual proof terms**: `D4`
(`FrontierSumAssembly.canonical_cleanCount_of_reference_construction`) produces
`K_B + ell <= e_0/(1-vartheta)` at the canonical routed system with its `hlight`
and `hcoord` binders already retired, and `D7`
(`FrontierSumAssembly.cleanCount_supplies_the_earlyMass_slot`) drops the
nonnegative split tally `ell` to leave exactly the `hKB` shape the banked engine
takes. -/

section CleanCountSupply

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`09:1355` at the canonical system, in the `hKB` shape of `09:1530--1531`.**

`K_B <= e_0/(1-vartheta)`, with `e_0 = |E_0|` (`09:450`) evaluated rather than
assigned.

The whole content is the composition of the two banked `cc-t5o` deliverables, and
neither is restated: the binder list below is `D4`'s own, byte-for-byte, and the
proof is `D7` applied to `D4`'s second conjunct.  `hLocEx` and `hfinal` remain
explicit binders exactly as they are there.

*Why this is not a restatement.*  `D4`'s conclusion is a conjunction whose second
member still carries the split tally `ell`; the banked engine's `hKB` slot is the
bare `K_B <= e_0/(1-vartheta)`.  Producing the second from the first at the
canonical system is the one step that connects `eq:wrapper-clean-count` to
`eq:wrapper-total-early-mass`, and Section 6 spends it.

General in the same data as `D4`. -/
theorem canonical_bobCapacity_le_earlyMassSlot {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
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
    (hLocEx : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (S : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
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
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scol,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
    (hfinal : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ finalWeight (certOpt v)) :
    (canonicalSystem hcomp hR).toWrapperFrontier.bobCapacity
      ≤ (E0.card : ℝ) / (1 - vartheta) :=
  FrontierSumAssembly.cleanCount_supplies_the_earlyMass_slot
    (canonicalSystem hcomp hR).toWrapperFrontier certOpt
    (FrontierSumAssembly.canonical_cleanCount_of_reference_construction
      Nmat Gmat ιR hsub halleged hcomp hR certOpt hq hmem hk hq4 hX hYc hθ0 hθ1 hC
      hgate hbase htcert hE1 hE2 hcost hLocEx hcover B hB plc hblock hplace hfinal).2

end CleanCountSupply

/-! ## §5  `eq:wrapper-total-early-mass`, first line (`09:1526--1529`)

`P_B < 128 mu_P B_theta L_q s K_B`, **strict** -- stated here in the *chained*
form `P_B < 128 mu_P B_theta L_q s * (e_0/(1-vartheta))` with `hKB` left as an
explicit binder, so that the strict line is available before the clean count is.

The banked `MassRedistributionCounting.wrapperTotalEarlyMass_engine` sums the
per-node bounds; what is new is that its `hlt` slot is no longer a binder.  It is
filled by Section 3 fired at every first-Bob node, which is `09:1521`'s "at every
first-Bob node" performed rather than assumed.

The `hKB` slot is deliberately left open here, so that the strict first line is
available over an *abstract* routed system; Section 6 closes it at the canonical
system, where `eq:wrapper-clean-count` is available. -/

section StrictLine

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V]

/-- **`eq:wrapper-total-early-mass` with the per-node binder retired.**

`P_B < 128 mu_P B_theta L_q s * (e_0/(1-vartheta))`, obtained by summing Section
3 over the first-Bob nodes through the banked engine.

*What is discharged.*  The engine's `hlt` -- the per-node strict bound -- is
produced here, not assumed: every node-indexed hypothesis below is a member of
the banked `earlyProtectedClosure` bundle, quantified over the first-Bob nodes
because `09:1521` fires the lemma at every one of them, and Section 3 turns them
into the engine's input.  The engine is consumed **by pin**; its summation is not
restated.

*What is still a binder, and why.*  `hKB` is `eq:wrapper-clean-count`'s second
inequality (`09:1355`).  It is not available over an abstract routed system --
it needs the frozen clean-count derivation -- so it stays open here and is
supplied in Section 6.  `hne` is the banked engine's own nonemptiness binder and
is not decoration: the banked
`WrapperMassRedistribution.totalEarlyMass_needs_a_first_bob_node` is the pole
showing the frozen strict inequality fails with no first-Bob node at all.
`hLocEx` is carried verbatim, per node.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
two sums, not an existential; and it is not the trivial bound `P_B < infinity`:
`earlyMassCoeff theta q s * (e_0/(1-vartheta))` is a fixed real, and by the
banked `WrapperMassRedistribution.earlyMassCoeff_threshold` it is the frozen
`128 mu_P B_theta L_q s` times `e_0/(1-vartheta)` exactly.

General in the routed system, the donor index, the node type, and every schedule
exponent. -/
theorem wrapperTotalEarlyMass_of_earlyClosure
    (S : RoutedSystem P Coord ι V r A0)
    {Ycol : Type*} [Fintype Ycol] [DecidableEq Ycol]
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    (isRestr : Protocol X Y Z → ℕ → ℕ → ℝ → Prop)
    {q k₂ b₁ r₂ r₃ bcap tcert selCard rowsPerBlock : ℕ}
    {θ lamT x epsProd e0 : ℝ}
    (Scol : V → Finset (Fin q → Ycol)) (YT : Finset Ycol)
    (Pv : V → ι → ℝ) (J₀ : Finset ι) (donor : ι → Fin q)
    (d₀ d₁ : V → Fin q → ℝ) (ell : V → ℕ) (bsel : V → Bool)
    -- `09:1253`, `d_v + ell_v = r`, at every first-Bob node
    (hdepth : ∀ v ∈ S.toWrapperFrontier.bobNodes, (S.node v).length + ell v = r)
    -- `09:1370--1376` and the `09:1519` reindexing, at every first-Bob node
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hres : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j)))
    -- the alleged protocol's budget at the frozen `C` (`09:855`, `09:1038`)
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    -- the banked `earlyProtectedClosure` bundle, per first-Bob node
    (hq : 0 < q) (hθ0 : 0 < θ)
    (hk₂ : 4 ≤ k₂)
    (hk₂le : ∀ v ∈ S.toWrapperFrontier.bobNodes, k₂ ≤ r₃ + ell v + r₂)
    (hbcap : 2 ≤ bcap)
    (hd₀0 : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀.image donor, 0 ≤ d₀ v j)
    (hd₀1 : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀.image donor, d₀ v j ≤ 1)
    (hd₁0 : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀.image donor, 0 ≤ d₁ v j)
    (hd₁1 : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀.image donor, d₁ v j ≤ 1)
    (hGate : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ((2 : ℝ) ^ (r₃ + ell v + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hY : 0 < Fintype.card Ycol) (hYT0 : 0 < YT.card)
    (hS : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      θ * (Fintype.card Ycol : ℝ) ^ q ≤ ((Scol v).card : ℝ))
    (hYT : lamT * (Fintype.card Ycol : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ∀ (u : ℕ) (J : Finset (Fin q)), J.card = u →
        ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Ycol)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ (Scol v))
    (hBlocks : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1 : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ∀ (e R : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ⌈((2 : ℝ) ^ (r₃ + ell v + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊
        ≤ rowsPerBlock)
    -- `09:1499--1504`, the round-`r4` selection binder at every first-Bob node
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- with the extraction re-gate forwarded verbatim, per node
    (hSelect : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      earlyMassCoeff θ q (2 ^ r₃) * ((S.toWrapperFrontier.capacity v : ℕ) : ℝ)
          ≤ donorMass Pv J₀ v →
        ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
          ExtractionOutput (Scol v) YT e →
          isRestr (descendStep (descend P (S.node v)) (bsel v))
            ((2 : ℕ) ^ (r₃ + ell v + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
              (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocEx : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Protocol X Y Z),
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ (ell v) dcls colDens →
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        0 < x → x ≤ 1 →
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R →
        (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        isRestr w blocks rowsEach colDens →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsEach →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ w.cost)
    -- the banked engine's own two slots
    (hne : (S.toWrapperFrontier.bobNodes).Nonempty)
    (hKB : S.toWrapperFrontier.bobCapacity ≤ e0 / (1 - vartheta)) :
    earlyMass S Pv J₀ < earlyMassCoeff θ q (2 ^ r₃) * (e0 / (1 - vartheta)) := by
  classical
  have hs : 1 ≤ (2 : ℕ) ^ r₃ := Nat.one_le_two_pow
  refine MassRedistributionCounting.wrapperTotalEarlyMass_engine S Pv J₀ hθ0 hs hne ?_ hKB
  intro v hv
  have hvtrue : S.firstBob v = true := by
    simpa [WrapperFrontier.bobNodes] using hv
  exact firstBob_protectedMass_lt_of_earlyClosure S hvtrue Mmat isRestr (Scol v) YT Pv J₀
    donor (d₀ v) (d₁ v) (bsel v) (hdepth v hv) hinj (hres v hv) hC hcost hq hθ0 hk₂
    (hk₂le v hv) hbcap (hd₀0 v hv) (hd₀1 v hv) (hd₁0 v hv) (hd₁1 v hv) (hGate v hv)
    hY hYT0 (hS v hv) hYT hgap (hQuery v hv) (hBlocks v hv) hx0 hx1 htx hMne hbase
    htcert heps0 heps1 (hE1 v hv) (hE2 v hv) (hrows v hv) (hSelect v hv) (hLocEx v hv)

end StrictLine

/-! ## §6  `eq:wrapper-total-early-mass` at the canonical system, both lines
(`09:1526--1534`)

`P_B < 128 mu_P B_theta L_q s K_B <= 128 mu_P B_theta L_q s e_0/(1-vartheta)`.

Section 5 supplies the strict first line with the `K_B` slot open; Section 4
closes it with `eq:wrapper-clean-count`.  Composing them at the canonical routed
system is the frozen display, with **both** of the banked engine's binders
retired at the site that consumes them. -/

section FrozenDisplay

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-total-early-mass` (`09:1526--1534`), at the canonical system.**

`P_B < 128 mu_P B_theta L_q s * (e_0/(1-vartheta))`, with `e_0 = |E_0|`
(`09:450`) and `s = 2^{r_3}` (`06:1864--1894`).

*Both frozen lines, in their frozen directions.*  `09:1528--1529` is **strict**
and it is strict here; `09:1530--1531` is **non-strict** and enters here only
through `eq:wrapper-clean-count`'s second inequality (`09:1355`).  No guard is
flipped and nothing weaker is substituted for either.

*What is derived rather than assumed.*  Both inputs of the banked
`MassRedistributionCounting.wrapperTotalEarlyMass_engine`:

* `hlt` is Section 5, i.e. Section 3's contrapositive of
  `lem:early-protected-closure` fired at every first-Bob node of the canonical
  system -- `09:1521`'s "at every first-Bob node" performed;
* `hKB` is Section 4, i.e. the `cc-t5o` deliverables `D4` and `D7` composed --
  `09:1530--1531`'s replacement of `K_B` by `e_0/(1-vartheta)`.

`kappa_v >= 2` (`09:1522`) is derived per node from the routed system's own
stopping rule, and `hJ : J_0.card <= q` (`09:1375`) from the carrier.

*What is still a binder.*  `hLocEx` appears twice -- once in the clean-count
bundle and once, per node, in the protected-closure bundle -- because
`thm:certified-localized-extension` (`A:109--146`) is called at both sites, and
it is the entry point of **EXPANDER-001**; `hfinal` (`09:1346--1350`) likewise.
Both are explicit named binders, never axioms, never premise-bundle fields, never
opaque certificates.  `hne` is the banked engine's own nonemptiness binder.
**Full-bundle satisfiability is not claimed**, and no synthetic instance below is
offered as a fidelity witness: the paper's own instance is a function of the
alleged protocol of `09:1187--1193`, which does not exist.

*No route completion.*  `eq:wrapper-u-dense` (`09:262--263`) is neither stated
nor implied; `09:1535--1781` remains open.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
two fixed reals, not an existential, and the right-hand side is not vacuously
large: the banked `WrapperMassRedistribution.earlyMassCoeff_threshold`
identifies it with the frozen
`128 mu_P B_theta L_q s` times `e_0/(1-vartheta)` exactly, and
`earlyMassCoeff_mono_in_capacity` shows the coefficient is a positive multiplier,
so the bound degrades to nothing only when `e_0` does. -/
theorem canonical_wrapperTotalEarlyMass {RwN : Type*} [Fintype RwN]
    {r bT kref tcert : ℕ} {E0 : Finset (Fin q)} {xU θ : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
    -- the protected-closure data, per first-Bob node
    {k₂ b₁ r₂ r₃ bcap tcertEP selCard rowsPerBlock : ℕ} {lamT epsProd : ℝ}
    (isRestrEP : Protocol X (Fin q → Yc) Bool → ℕ → ℕ → ℝ → Prop)
    (Scol : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Finset (Fin q → Yc))
    (YT : Finset Yc)
    (Pv : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    (J₀ : Finset (CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r))
    (donor : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Fin q)
    (d₀ d₁ : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Fin q → ℝ)
    (ell : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℕ)
    (bsel : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Bool)
    (hdepth : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ((canonicalSystem hcomp hR).node v).length + ell v = r)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hres : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes, ∀ j ∈ J₀,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j)))
    -- the alleged protocol (`09:1187--1193`) at the frozen `C` (`09:855`, `09:1038`)
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    -- the clean-count bundle (`cc-t5o` `D4`), verbatim
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
    -- the protected-closure bundle (`lem:early-protected-closure`), per node
    (hqpos : 0 < q)
    (hk₂ : 4 ≤ k₂)
    (hk₂le : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      k₂ ≤ r₃ + ell v + r₂)
    (hbcap : 2 ≤ bcap)
    (hd₀0 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ J₀.image donor, 0 ≤ d₀ v j)
    (hd₀1 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ J₀.image donor, d₀ v j ≤ 1)
    (hd₁0 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ J₀.image donor, 0 ≤ d₁ v j)
    (hd₁1 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ J₀.image donor, d₁ v j ≤ 1)
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
    -- with the extraction re-gate forwarded verbatim, per node
    (hSelectEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      earlyMassCoeff θ q (2 ^ r₃)
          * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)
          ≤ donorMass Pv J₀ v →
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
    (hne : ((canonicalSystem hcomp hR).toWrapperFrontier.bobNodes).Nonempty) :
    earlyMass (canonicalSystem hcomp hR) Pv J₀
      < earlyMassCoeff θ q (2 ^ r₃) * ((E0.card : ℝ) / (1 - vartheta)) :=
  wrapperTotalEarlyMass_of_earlyClosure (canonicalSystem hcomp hR) Nmat isRestrEP Scol YT Pv
    J₀ donor d₀ d₁ ell bsel hdepth hinj hres hC hcost hqpos hθ0 hk₂ hk₂le hbcap
    hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYc hYT0 hSep hYT hgap hQuery hBlocks hx0 hx1 htx hMne
    hbaseEP htcertEP heps0 heps1 hE1ep hE2ep hrows hSelectEP hLocExEP hne
    (canonical_bobCapacity_le_earlyMassSlot Nmat Gmat ιR hsub halleged hcomp hR certOpt hq
      hmem hk hq4 hX hYc hθ0 hθ1 hC hgate hbase htcert hE1cc hE2cc hcost hLocExCC hcover
      B hB plc hblock hplace hfinal)

end FrozenDisplay

/-! ## §7  Aux-lemma battery

General checks on the reindexing bridge of Section 1 (Batteries 1--2, on the mass
and on the count respectively), on the banked coefficient identity Section 2 pins
(Battery 3), on the frozen reservoir readout at a single donor together with its
`09:1537` sum (Batteries 4 and 4b), and on the frozen constant substitutions of
Sections 3 and 5 (Batteries 5--6).  Canonical inhabitation is **INHERITED,
REGISTERED and DEFERRED** per the header: this module declares no new type, so it
opens no new obligation, and the inherited one cannot be discharged because the
paper's own instance of every statement here is a function of the alleged
protocol of `09:1187--1193`, which does not exist.  Batteries 1--5 evaluate no
schedule parameter; **Battery 6 is the single exception** -- a guard-level check
that instantiates `k_2`, `r_2`, `r_3` and `ell` at the banked witness family's
own values, and at no value of its own.  No declaration below carries a numeral
without banked or frozen pedigree. -/

section Battery

/-- **Battery 1 (the reindexing is load-bearing, not decoration).**

`donorMass_eq_reservoirs` reindexes the donor sum along `donor`, and `09:1519`'s
"the `c` outer coordinates whose clean reference certificates reach final Alice
nodes" is what makes that injective.  Drop the injectivity and the identity is
simply false: two distinct clean certificates pointing at one outer coordinate
double the left-hand side while the right-hand side counts the coordinate once.

This is the pole for `hinj`.  A green build sees nothing wrong with an
`hinj`-free statement; this exhibits the collapse. -/
theorem reservoir_decomposition_needs_injectivity :
    ∃ (Pv : Unit → Fin 2 → ℝ) (donor : Fin 2 → Fin 1) (d₀ d₁ : Fin 1 → ℝ)
      (J₀ : Finset (Fin 2)),
      (∀ j ∈ J₀, Pv () j = muP * (d₀ (donor j) + d₁ (donor j)))
        ∧ donorMass Pv J₀ ()
            ≠ muP * ((∑ j ∈ J₀.image donor, d₀ j) + (∑ j ∈ J₀.image donor, d₁ j)) := by
  classical
  refine ⟨fun _ _ => muP, fun _ => 0, fun _ => 1, fun _ => 0, Finset.univ, ?_, ?_⟩
  · intro j _
    norm_num
  · have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
    simp only [donorMass]
    have himg : (Finset.univ : Finset (Fin 2)).image (fun _ : Fin 2 => (0 : Fin 1))
        = ({0} : Finset (Fin 1)) := by decide
    rw [himg]
    simp only [Finset.sum_const, hcard]
    have := muP_pos
    norm_num
    linarith

/-- **Battery 2 (the reindexing loses nothing: `09:1375` also holds in the
*certificate* index).**

`donorImage_card_le` discharges the banked lemma's `hJ` **after** the reindexing
of `donorMass_eq_reservoirs`, so what it bounds is the *image* `J_0.image donor`.
The frozen `09:1375` reads `J_0 subseteq [q]`, and `09:1519` fixes `J_clean` as
"the `c` outer coordinates whose clean reference certificates reach final Alice
nodes" -- so the frozen `c` counts certificates and coordinates at once, which is
exactly what `09:1365`'s `K_B + c + ell <= q` then spends.

This probe checks the reindexing against that reading: under the very `hinj` of
`donorMass_eq_reservoirs`, the carrier bound transports back to the *unreindexed*
donor set, `|J_0| <= q`.

*Not the vacuous direction.*  `donorImage_card_le` alone says nothing here: a
donor map that collapses many certificates onto one outer coordinate keeps the
image bound while leaving `|J_0|` arbitrarily large, so the statement below is
false without `hinj` and its proof genuinely spends
`Finset.card_image_of_injOn`.  That is the same injectivity Battery 1 exhibits
the collapse for, checked on the *count* rather than on the mass.

General in the donor index and the width; nothing is evaluated. -/
theorem donorSet_card_le_width {ι : Type*} {q : ℕ} (donor : ι → Fin q)
    (J₀ : Finset ι) (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j) :
    J₀.card ≤ q := by
  classical
  rw [← Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h)]
  exact donorImage_card_le donor J₀

/-- **Battery 3 (the frozen threshold is monotone in the capacity).**

`eq:protected-early-threshold` is `128 mu_P B_theta L_q s kappa`, and `09:1529`
sums it against `K_B = sum_v kappa_v`.  For that sum to behave, the coefficient
must be nonnegative, so that a larger capacity gives a larger threshold; the
banked `earlyMassCoeff_pos` supplies positivity and this is the monotonicity it
buys.

This is what makes `09:1530--1531`'s replacement of `K_B` by the *upper* bound
`e_0/(1-vartheta)` a weakening in the right direction rather than an unjustified
substitution.  General in `theta`, `q`, `s` and the two capacities. -/
theorem earlyMassCoeff_mono_in_capacity {θ : ℝ} (hθ : 0 < θ) {q s : ℕ} (hs : 1 ≤ s)
    {κ κ' : ℝ} (h : κ ≤ κ') :
    earlyMassCoeff θ q s * κ ≤ earlyMassCoeff θ q s * κ' :=
  mul_le_mul_of_nonneg_left h (le_of_lt (earlyMassCoeff_pos hθ hs))

/-- **Battery 4 (round trip: the reservoir readout at a single donor).**

At a singleton donor set `donorMass_eq_reservoirs` must collapse to the frozen
per-donor mass `P_v({j}) = mu_P (d_0(j) + d_1(j))` of `09:1370--1376`, which is
the quantity `09:1537`'s Bob-heavy test compares against `eta_R/4`.  It does, and
injectivity is free there -- so the general identity is not stronger than the
frozen reading at the point the *next* frozen step consumes.

General; nothing is evaluated. -/
theorem donorMass_singleton_reservoirs {ι V : Type*} {q : ℕ} (Pv : V → ι → ℝ)
    (donor : ι → Fin q) (d₀ d₁ : Fin q → ℝ) (j : ι) (v : V)
    (hres : Pv v j = muP * (d₀ (donor j) + d₁ (donor j))) :
    donorMass Pv ({j} : Finset ι) v = muP * (d₀ (donor j) + d₁ (donor j)) := by
  classical
  rw [MassRedistributionCounting.donorMass_singleton]
  exact hres

/-- **Battery 4b (the `09:1537` bridge -- Battery 4 summed over the first-Bob
frontier, which is where Battery 4 is spent).**

`09:1537` writes its test on `sum_{v : first-Bob frontier node} P_v({j})`, the
banked `MassRedistributionCounting.firstBobMass`.  Battery 4 is that sum's
summand in the reservoir form of `09:1370--1376`; this is the sum itself, and it
is the single site in this module that consumes Battery 4.

*What is asserted, and what is not.*  This is a definitional readout of the
quantity `09:1537` names, and nothing more.  The threshold `eta_R/4`
(`09:1538`), the Bob-heavy classification (`09:1535--1540`), the count
`eq:wrapper-bob-heavy-count` (`09:1541--1547`) and everything after `09:1547`
are absent here and remain **OPEN**: no inequality is stated, no donor is
classified, `eta_R` does not occur, and `eq:wrapper-u-dense` (`09:262--263`) is
neither stated nor implied.

*Why the trivial witness fails.*  The conclusion is an equation between two named
quantities, not an existential, and it is not `rfl`: the left side is the banked
`firstBobMass`, whose summand is the abstract `Pv v j`, and reaching the frozen
`mu_P (d_0(j) + d_1(j))` needs `hres` at **every** first-Bob node together with
the banked `donorMass_singleton` collapse.  Weaken `hres` at a single node of a
nonempty frontier and the two sides differ there.

General in the routed system, the donor index, the node type and the width;
nothing is evaluated. -/
theorem firstBobMass_eq_reservoirs {X Y Z : Type*} {Coord ι V : Type*} [Fintype V]
    {P : Protocol X Y Z} {r A0 q : ℕ} (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (donor : ι → Fin q) (d₀ d₁ : V → Fin q → ℝ) (j : ι)
    (hres : ∀ v ∈ S.toWrapperFrontier.bobNodes,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j))) :
    firstBobMass S Pv j
      = ∑ v ∈ S.toWrapperFrontier.bobNodes,
          muP * (d₀ v (donor j) + d₁ v (donor j)) := by
  classical
  rw [MassRedistributionCounting.firstBobMass_eq_sum_donorMass_singleton]
  refine Finset.sum_congr rfl fun v hv => ?_
  exact donorMass_singleton_reservoirs Pv donor (d₀ v) (d₁ v) j v (hres v hv)

/-- **Battery 5 (the `C` of Section 3 is the frozen `C`, evaluated).**

`09:855` with `09:1038` fixes `C = D_2 + log_2 s + 1`, and `09:1505--1507`
closes `lem:early-protected-closure` with
`Bcap + log_2 K_int = C + log_2 kappa - 1` at `K_int = s kappa q_2`
(`09:1481`, display `09:1480--1482`).  Substituting the frozen exponents
`s = 2^{r_3}`, `kappa = 2^{ell}`, `q_2 = 2^{r_2}` gives
`log_2 K_int = r_3 + ell + r_2`, so the endpoint reads
`Bcap + r_3 + ell + r_2 = C + ell - 1`, i.e. `C = Bcap + r_2 + r_3 + 1`.

That is exactly the banked `TerminalTwoStream.terminalTarget`, which is why
Sections 3 and 5 substitute it for `C` instead of carrying a free natural number.
This records the evaluation of that definitional chain as a checked identity, so
a later tranche cannot silently reintroduce a free `C` at this site.

*Scope: only the `C`-evaluation half is stated here.*  The endpoint half itself --
`Bcap + (r_3 + ell + r_2) + 1 = C + ell`, the subtraction-free form of
`09:1505--1507` -- is the banked `WrapperProtectedEarly.endpoint_identity`
(`Dtwo bcap r_2 + (r_3 + ell) + 1 = terminalTarget bcap r_2 r_3 + ell`, which is
the same statement up to re-association since `Dtwo bcap r_2 = bcap + r_2` by
`rfl`).  It is consumed **by pin** inside the banked `earlyProtectedClosure`,
whose conclusion Section 3 applies, and is deliberately not restated here.

*Banked neighbours, named so a later tranche does not rediscover this as a
duplicate.*  `TerminalFixedBin.fixedBinTarget_eq`
(`fixedBinTarget bcap r_2 = bcap + r_2 + 1`) composed with
`TerminalFixedBin.terminalTarget_eq_fixedBinTarget_add`
(`terminalTarget bcap r_2 r_3 = fixedBinTarget bcap r_2 + r_3`) reaches this
statement after delta-unfolding `fixedBinTarget` and commuting the trailing `1`
past `r_3`.  That is a two-lemma composition rather than a restatement, and
`TerminalFixedBin` is not in this module's `open` list, so nothing is displaced
at any use site; the pin is kept here for the same reason `fixedBinTarget_eq`
itself exists.

General. -/
theorem terminalTarget_is_the_frozen_C (bcap r₂ r₃ : ℕ) :
    TerminalTwoStream.terminalTarget bcap r₂ r₃ = bcap + r₂ + r₃ + 1 := by
  simp [TerminalTwoStream.terminalTarget, DenseBranchSelection.Dtwo]

/-- **Battery 6 (the newly coupled guards are not jointly impossible).**

Section 6 is the first place where the clean-count bundle and the
protected-closure bundle meet, and the coupling introduces exactly two new
numeric constraints on the shared exponents: `hk_2le : k_2 <= r_3 + ell_v + r_2`
(the banked `earlyProtectedClosure`'s own, now node-indexed) and
`hC : 3 <= terminalTarget bcap r_2 r_3` (the frozen `C` of `09:855` with
`09:1038` in place of a free `C`).  If those two contradicted each other,
Section 6 would be vacuous and every gate would still pass.

They do not.  The exponents are the **banked** probe family's own --
`k_2 = 5`, `r_2 = 13`, `r_3 = 2`, `ell = 1`, i.e. the values of
`WrapperProtectedEarly.extensionCallThree_floorTier_instance`
(`ExtensionCallThree 5 14 11 40 7 13 2 1 (1/2) (callThreeH 7)` at the signature
`(T R Rloc b_1 e r_2 r_3 ell dcls colDens)`).

*That tuple is FLOOR-TIER and BEYOND-PAPER, and this comment no longer says
otherwise.*  Round `r2` called it schedule-legal and cited a theorem then named
`witness_family_schedule_legality`; the `cc-t6e` repair **withdrew** that claim
and renamed the theorem `WrapperProtectedEarly.witness_family_floorTier_anchors`,
because what it actually certifies is exactly two inequalities -- the Section-4
guarded-source floor `s >= 4` a power of two
(`04:389`/`04:460`/`04:481`/`04:504`/`04:619`) at `s = 2^{r_3} = 4`, and
`eq:stage2-structural-gates` `4 t_2 <= q_2` (`06:835`) -- while `eq:s-choice`
(`06:112--120`, with `06:394--395`) forces `s >= 512` with `64 | s`.  A floor is
not a defining display.  Battery 6 is therefore a guard-level consistency probe
at a point the paper never visits; it reads **no** parameter value out of the
tuple, and it claims no legality.  (This is the `cc-t6e` finding **F7**
propagation, discharged here.)

*`Bcap` is given no value here, and must not be.*  `07:156` reads
`Bcap := D + a`, so `Bcap` is a source-**DEFINED** quantity and substituting a
numeral for it would be assignment to a defined quantity -- the defect this
declaration previously carried.  It is instead universally quantified, with
**no** guard at all, not even the `2 <= bcap` floor the banked bundle carries:
`terminalTarget bcap 13 2 = bcap + 16 >= 3` for every `bcap : ℕ`, so the guard is
unused and the statement below is strictly stronger than any guarded form of it.
No numeral for a defined quantity remains, in the statement or in this comment.

This is a **guard-level** check only.  It is emphatically **not** a claim that the
full Section 6 bundle is satisfiable -- that claim is not made anywhere in this
module -- and it is not a fidelity witness: the paper's own instance is a function
of the alleged protocol of `09:1187--1193`, which does not exist. -/
theorem coupled_guards_are_jointly_satisfiable (bcap : ℕ) :
    (5 : ℕ) ≤ 2 + 1 + 13
      ∧ 3 ≤ TerminalTwoStream.terminalTarget bcap 13 2 := by
  refine ⟨by norm_num, ?_⟩
  simp only [TerminalTwoStream.terminalTarget, DenseBranchSelection.Dtwo]
  omega

end Battery

end EthInapproximability.ParameterizedNP.ProtectedEarlyClosure
