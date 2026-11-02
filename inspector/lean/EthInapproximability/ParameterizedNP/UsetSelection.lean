import EthInapproximability.ParameterizedNP.ProtectedRowReservoirs

/-!
# Parameterized NP route: the `u`-set selection of `09:1441--1471`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche).
* **The exact frozen lines traced here**, in print order -- the block is the
  middle of the frozen proof of `lem:early-protected-closure` (`09:1432--1509`),
  which opens at `09:1433` and whose selection chain this module wires to the
  reservoirs built by `PROTECTED-ROW-RESERVOIRS-001`:
  * **`09:1433--1436`**, the entry: "One of the two protected reservoir types
    contributes at least half of `eq:protected-early-threshold`.  Let
    `d_j in [0,1]` be the retained relative density of this type from donor `j`,
    and write `D_mass = sum_j d_j`."
  * **`09:1439`**, the halved threshold: `D_mass >= 64 B_theta L_q s kappa`.
  * **`09:1441--1448`**: "Discard donors with `d_j < D_mass/(2q)`.  Their total
    contribution is below `D_mass/2`.  Partition the others into at most `L_q`
    dyadic classes `d_cls/2 < d_j <= d_cls`.  Some class `V` satisfies
    `|V| d_cls >= D_mass/(2 L_q)`."
  * **`09:1449--1456`**, `eq:protected-dyadic-class` (label `09:1455`): "Let `u`
    be the least power of two at least `8 s kappa/d_cls`.  Then
    `8 s kappa <= u d_cls < 16 s kappa`, `|V| >= u B_theta`."
  * **`09:1458--1464`**: "Call a `u`-set of donors poor if its projection of the
    retained outer column set has density below `rho_0`.  By
    `lem:product-projection-cover`, the union of a maximal disjoint family of
    poor `u`-sets has size at most `u(B_theta-1)`.  Hence
    `eq:protected-dyadic-class` leaves a `u`-set of donors outside that cover.
    Its projection has density at least `rho_0`; after Bob's query, one child has
    density at least `rho_1`."
  * **`09:1466--1471`**: "The schedule gives `1-lambda_T <= 1/100 <= rho_1/8`, so
    `lem:template-coordinate-extraction` applies.  It leaves `u/2` donors whose
    projected all-template set has density at least `rho_1 2^{-u-1}` in
    `Y_T^{u/2}`.  Averaging over the equal template bins, fix one Stage-3 bin in
    each donor without reducing this relative density."
  * **`09:1486--1490`**, `eq:protected-delta-min` (label `09:1489`),
    `d_cls >= 64 B_theta L_q s/q =: delta_min`, which the frozen proof produces
    together with the dyadic class and which is therefore carried through the
    selection rather than dropped.
  * **`09:1421--1425`**, `eq:protected-early-threshold` (label `09:1424`),
    `P_v(J_0) >= 128 mu_P B_theta L_q s kappa` -- the frozen hypothesis whose
    left-hand side is the built `P_v` of `PROTECTED-ROW-RESERVOIRS-001`.  It is
    consumed as a **binder** here; `lem:early-protected-closure`'s conclusion is
    *not* asserted anywhere in this module.
  * **`09:1378--1384`**, the four block constants `rho_0 = 99/100`,
    `rho_1 = rho_0/2`, `B_theta = min{B >= 1 : rho_0^B < theta}`,
    `L_q = ceil(log_2(2q)) + 1`, consumed by pin as
    `WrapperProtectedEarly.{rhoZero, rhoOne, Btheta, Lq}` and never re-defined.
  * **`09:1375`**, the donor index convention `J_0 subseteq [q]`, and
    **`09:105--109`** (`q = 2^r` the scale-alignment width, `U = Int_q(N)`,
    `m = |Rows(N)|`), which is why every donor set below is a
    `Finset (Fin q)` at the *scale-alignment* width and never at `q_2` or `Q`.
  * **`09:1519--1520`**, the donor reindexing "`J_clean` the `c` outer
    coordinates whose clean reference certificates reach final Alice nodes",
    consumed only through the banked
    `ProtectedRowReservoirs.donorMass_systemPv`, whose injectivity binder is
    passed through unchanged.
  * **`09:1537`**, `sum_{v : first-Bob frontier node} P_v({j})`, the aggregate
    that Section 5 contacts.  See the census below for exactly why that contact
    is a domination statement and nothing more.
* **Cross-anchors opened first-hand in the frozen files for this tranche:**
  * `06-parameter-schedule.tex` (SHA-256
    `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
    recomputed first-hand this round): the four **defining displays** that fix
    the schedule quantities this module's Section-6 inhabitants stand at, each
    opened at its own anchor rather than at a consumption site --
    * `eq:s-choice` at `06:110--121`, `s = 2^{ceil(B_s u^2)}` with
      `u = clog_2(clog_2(A_pre + 16))` and `A_pre = max{16, b_out, ...}`, and the
      divisibility `64 | s` at `06:394--395`;
    * `eq:q-deltaU` at `06:513--519`, `q = 2^{A_wrap L_P^2}` with `A_wrap` a
      positive integer of the universal configuration field (`06:56--61`) and
      `L_P = clog_2(P_0)`, `P_0 >= 16` (`06:465--472`);
    * `eq:Q-theta-choice` at `06:527--538`,
      `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`, `Q` the least power of
      two at least `Q_0`, `theta = delta/(16Q)`, with `1/theta = 160 Q` at
      `delta = 1/10` (`06:539`) and the finite gate `delta_U <= 1/200`
      (`06:547`);
    * `06:1147--1153` (row (iii) of `sec:extension-call-ledger`, where
      `h = rho_1 2^{-u-1}` at `06:1150` is the entering column density this block
      produces -- the banked `WrapperProtectedEarly.callThreeH` -- and where
      `06:1151` supplies the per-block row density `d_cls/4`).
  * `05-public-records.tex` (SHA-256
    `757D328B09060B4EBECEA5CF6C20259B3E17DC8250680FF0E9F9BBA35AE0A39A`):
    `05:39--40`, "`b_0, b_out in N` are positive incoming and requested outgoing
    robustness depths" (the sentence straddles the two lines), the only fact
    about `b_out` the schedule bracket below uses.
  * `04-guarded-source.tex` (SHA-256
    `15692565E4519C71D671664C8AEF4463389721ED8303EC58EAAFB06001A9DF2D`):
    `04:389`, `04:460`, `04:481`, `04:504` and `04:619`, each requiring the
    Stage-3 multiplicity `s` to be a power of two with `s >= 4`.  This is a
    **floor**, not a defining display: `eq:s-choice` above is what defines `s`,
    and it forces `s >= 512`.  The distinction is the whole content of the
    round-`r1` repair recorded under "Schedule tiers" below.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the single import is
  `ProtectedRowReservoirs`, whose closure was enumerated mechanically this
  tranche and contains neither `LegacyNPCC.Stage12` nor `NPCC.Stage2`.  **No
  opt-in ledger note is owed.**
* **Proof status:** new.  Every declaration is either a general property of one
  of the two definitions below, or a composition of banked interfaces at the
  built reservoir densities.  No mathematics is added: the dyadic classification,
  the width construction, the poor-`u`-set cover and the template-coordinate
  extraction are all banked arithmetic in `WrapperProtectedEarly`, and what is
  new is exclusively the *wiring* of that arithmetic to
  `ProtectedRowReservoirs.reservoirDensity`.  No schedule inequality is asserted:
  every declaration outside Section 6 is uniform in `s`, `kappa`, `theta` and
  `q` and carries only their frozen guards.

## Schedule tiers in Section 6 (round `r1`)

Section 6 carries inhabitants at **two tiers**, and the labels are load-bearing.

* **Schedule tier.**  `uSetSelection_at_scheduleTheta` and
  `protectedMass_threshold_at_scheduleTheta` stand at values *evaluated* through
  the frozen defining displays: `theta = 1/(160 Q)` at the banked
  `EntryGates.Qwidth` of `06:532` (`eq:Q-theta-choice`), `s = 2^{r_3}` under
  `eq:s-choice`'s consequences `512 <= s` and `64 | s`, `kappa = 2^{ell} >= 2`
  (`09:1420`), and `q = 2^{A_wrap L_P^2}` of `eq:q-deltaU` with `A_wrap`
  *produced* by the banked `WrapperProtectedEarly.exists_wrapper_width` (the pin
  actually consumed in the proof term; `exists_wrapper_exponent` is its base) from
  `06:520--522`.  These are the non-vacuity certificates for `USetSelected` and
  for `uSetSelection_of_protectedMass`'s premise bundle.
* **Floor tier (BEYOND-PAPER, FULL NON-FIDELITY, schedule half included).**
  `uSetSelection_probe` and `protectedMass_threshold_is_satisfiable` run at
  `s = 4`, `theta = 1/20480`, `q = 2^24`.  Round `r0` called those three numerals
  legal; that claim is **withdrawn in every half, the schedule half included**.
  `eq:s-choice` forces `s >= 512` with `64 | s`; `eq:Q-theta-choice` with
  `06:547` and `05:39--40` forces `Q >= 2^14`, hence `theta <= 1/2621440` (the
  banked `WrapperProtectedEarly.scheduleTheta_route_le`); and `eq:q-deltaU` has
  no reachable exponent `24`, since `L_P >= 4` makes `A_wrap L_P^2` a multiple of
  a square at least `16` (the banked
  `WrapperProtectedEarly.wrapper_exponent_ne_twentyfour`).  The two floor-tier
  statements are true arithmetic about our own encoding at a point the frozen
  schedule never visits; **no parameter value may be read out of either**, and
  neither is offered against any vacuity charge.

## Reader counterpart: NONE claimable, and why

`routes/parameterized-np/reader-facing/sections/` was searched first-hand this
tranche for "u-set", "poor", "dyadic", "cover", "projection", "template" and
"donor", and every hit was opened.  The 41-page reader artifact carries **no**
item stating any sentence of `09:1441--1471`.

* `reader A-stage4-details.tex:396--399` ("The complete owner--donor count is
  finite: it uses only the fixed reservoir masses above, the two source deletion
  tolerances, and the exact cover and ceiling inequalities certified by the
  parameter compiler.  It is expanded line by line in the ultra-explicit
  companion") is the only reader sentence that mentions cover inequalities at
  all.  It is unnumbered proof prose, it states no `u`-set, no dyadic class and
  no density, and it is **already** the cited counterpart of
  `MassRedistributionCounting.lean:208`, `OwnerMassTransfer.lean:227` and
  `WrapperMassRedistribution.lean:344`.  The READER-COUNTERPART rule forbids
  assigning one reader item to a fourth declaration, and it forbids citing prose
  as a statement.
* `reader A-stage4-details.tex:374--376` (the only reader mention of protected
  mass reaching a node) is already the counterpart of six banked declarations,
  including `ProtectedEarlyClosure` and `BobHeavyDonorCount`.
* `reader A-stage4-details.tex:393--395` is the display
  `D_U(1;1-delta_U,theta) >= C + r_q`, i.e. `eq:wrapper-u-dense`, which this
  module neither states nor implies; it is already cited by eight banked modules.

So no reader item is cited rather than one invented, and the absence is recorded
as a finding about the reader artifact.  The reader's own sentence explains it:
this block "is expanded line by line in the ultra-explicit companion".

## What this tranche lands

`PROTECTED-ROW-RESERVOIRS-001` records, as its **GAP-EXPOSED item 1**, that "the
`u`-set selection of `09:1441--1471` is not built.  The dyadic classification,
the poor-`u`-set cover and the template-coordinate extraction of the frozen proof
are banked as *arithmetic* in `WrapperProtectedEarly`
(`exists_protected_dyadic_class`, `exists_dense_uset_in_class`,
`templateCoordinateExtraction`); nothing here connects them to the reservoir row
sets just built."  Its prescription is, verbatim, *"feed `reservoirDensity` into
`exists_protected_dyadic_class` at `d := fun i => reservoirDensity ...` and
discharge its `D_mass` hypothesis from `donorMass_systemPv`."*  That is precisely
and only what this module does, in four steps.

1. **The `d_j` family and `D_mass`** (Section 1).  `donorDensity` is the
   `d_j in [0,1]` of `09:1434--1435` presented as the *function of the donor
   index* that `exists_protected_dyadic_class` consumes, and `dMass` is
   `D_mass = sum_j d_j` of `09:1436`.  Neither is new mathematics: both are the
   banked `ProtectedRowReservoirs.reservoirDensity` re-associated, and the frozen
   bracket `d_j in [0,1]` is inherited as a *theorem*, not assumed.
2. **The type split** (Section 2).  `09:1433`'s "one of the two protected
   reservoir types contributes at least half" is the banked
   `WrapperProtectedEarly.protected_reservoir_halving`, and its `hthr` binder is
   discharged at the built `P_v` by the banked
   `ProtectedRowReservoirs.donorMass_systemPv`.  The output is `09:1439`'s
   `D_mass >= 64 B_theta L_q s kappa` for **one** of the two built reservoirs.
3. **The dyadic class and the width** (Section 3).  `exists_reservoir_dyadic_class`
   is the prescription executed: `exists_protected_dyadic_class` at
   `d := donorDensity P Res p`, chained into `exists_width_u`, producing the
   frozen `(V, d_cls, u = 2^e)` of `09:1441--1456` together with
   `eq:protected-delta-min`.  The only new arithmetic is
   `four_le_width_exponent`, which reads `e >= 4` off
   `8 s kappa <= u d_cls <= u` at `s >= 1`, `kappa >= 2` -- the fact that makes
   `4 | u` (demanded by `lem:template-coordinate-extraction`, `09:1390--1391`,
   where the clause "`u` is / divisible by four" straddles the two lines)
   available without assuming it.
4. **The whole of `09:1441--1471`** (Section 4).  `USetSelected` names the frozen
   deliverable and `uSetSelection_of_dMass` produces it, by handing Section 3's
   `(V, e)` to the banked `WrapperProtectedEarly.selectedColumnDensity` (which is
   `09:1458--1471` as arithmetic on an abstract class).
   `uSetSelection_of_protectedMass` then starts from
   `eq:protected-early-threshold` itself at the built `P_v`, so the frozen
   hypothesis of `lem:early-protected-closure` reaches the frozen output of its
   `09:1471` line with no abstract `d_j` left in between.

**What is NOT landed, and is not implied.**  `lem:early-protected-closure`'s
*conclusion* -- the prose clause "then one child of `v` has communication
complexity at least" at `09:1426` with its display `C + log_2 kappa - 1` at
`09:1427--1429` -- is **not** stated here: its arithmetic is the banked
`WrapperProtectedEarly.earlyProtectedClosure`, which this module does not consume
at all.  `eq:wrapper-u-dense` (`09:1188`, `09:1780--1781`) is neither stated nor
implied, `eta_R` occurs in no statement, no donor is classified Bob-heavy, and
**no route completion is claimed.**

**OBS-1 is honoured.**  `RETENTION-SUPPLY-001` records that the `RetentionSupply`
audit runs at `delta_U = 1/640` while a chain-legal `eta_R < tau = 1/92` forces
`delta_U < 1/2944`, so that audit's satisfiability does **not** transfer to the
legal `delta_U`.  No declaration of this module consumes any `RetentionSupply`
audit declaration.  `eta_R` and `bracketGE` occur in no declaration statement and
in no proof term here (they appear only in this prose, describing what is *not*
stated).  `delta_U` occurs only as a **universally quantified variable** of the
two Section-6 schedule-tier statements, where it carries the frozen finite gate
`delta_U <= 1/200` (`06:547`) together with `0 < delta_U`, and enters solely
through the banked `EntryGates.Qwidth b_out delta_U`; **no value is asserted for
it**, so the `RETENTION-SUPPLY-001` transfer defect is not repeated.  The only
`RetentionSupply` interfaces reached are
`refBlock`, `retainedRefRows` and their general counting lemmas, all through the
banked `reservoirDensity`, and they mention no schedule constant.

## Census of `09:1441--1471`, sentence by sentence

Each frozen sentence of the traced range, and the interface that serves it.  The
census is what rules the forward deliverables of `PROTECTED-ROW-RESERVOIRS-001`
in or out of this module.

* `09:1441--1442`, the light-donor discard -- banked `sum_light_le_half`, inside
  `exists_heavy_dyadic_class`.  Nothing new.
* `09:1442--1448`, the dyadic classes and the heavy class `V` -- banked
  `exists_protected_dyadic_class`.  **New: the wiring at `donorDensity`.**
* `09:1449--1456`, the width `u = 2^e` -- banked `exists_width_u`.  **New: the
  wiring, plus `four_le_width_exponent`.**
* `09:1458--1462`, the poor-`u`-set cover -- banked `exists_dense_uset_in_class`.
  Nothing new.
* `09:1463--1464`, `rho_0`, Bob's query, `rho_1` -- banked `denserChild_rhoOne`,
  inside `selectedColumnDensity`.  Nothing new.
* `09:1466--1471`, the template extraction -- banked
  `templateCoordinateExtraction`, inside `selectedColumnDensity`.  Nothing new.
* `09:1486--1490`, `delta_min` -- the fourth clause of
  `exists_protected_dyadic_class`, carried through rather than dropped.

**`donorMass_systemPv` is ruled IN** and is consumed in the proof term of
`exists_heavy_reservoir_type`: it is the only route from
`eq:protected-early-threshold` (which is stated on `P_v(J_0)`) to `09:1436`'s
`D_mass` (which is stated on the `d_j`).

**`firstBobMass_systemPv` is ruled OUT of the selection chain**, and Section 5
records why rather than leaving it unexplained.  Every sentence of
`09:1441--1471` is stated at **one** first-Bob node `v`: the threshold
`eq:protected-early-threshold` is `P_v(J_0) >= ...` at the `v` fixed by
`09:1418--1420`, and every `d_j`, `D_mass`, `V`, `u` and projection below it
inherits that node.  The frontier *sum* `sum_v P_v({j})` first appears at
`09:1537`, inside `sec:wrapper-mass-redistribution` (`09:1512--`), which
`PROTECTED-ROW-RESERVOIRS-001` registers as its own GAP-EXPOSED item 3 and which
this module does not enter.  The census therefore rules the deliverable in at
exactly one point -- the **domination** of a single node's readout by the
frontier sum -- and Section 5 lands that, plus the general averaging statement in
the same direction, and stops there.  Nothing in Section 5 classifies a donor, and
`eta_R` does not occur.

## GAP-EXPOSED (named ranges, with the next-round prescription)

1. **`09:1466--1471`'s last sentence is not modelled**: "Averaging over the equal
   template bins, fix one Stage-3 bin in each donor without reducing this
   relative density."  Section 4 stops at the template-coordinate extraction, and
   the Stage-3 bin structure of `09:367--371` is not carried into the
   deliverable.  *Next round:* transport the banked
   `WrapperProjectionCovers.singleton_bin_retention` along the selected `u/2`
   coordinate set.
2. **`09:1473--1483` is not entered**: "In a protected reservoir, all rows
   carrying a fixed Stage-2 coordinate have the same Stage-4 entry map", and the
   represented-block count `K_int = s kappa q_2`.  This is item 2 of
   `PROTECTED-ROW-RESERVOIRS-001`'s own gap list and is untouched here: no
   declaration below mentions a Stage-4 entry.  *Next round:* prove the fibre
   constancy from `protectedDup_ignores_labels` and bridge to
   `WrapperProtectedEarly.{Kint, representedBlocks_ge}`.
3. **`09:1491--1509` is not entered**: the ambient product width, `r' = K_int/t_2`
   "in the literal range of Localized Extension", the selection of exactly
   `9 K_int/16` blocks and the endpoint `B_cap + log_2 K_int = C + log_2 kappa - 1`.
   These are the banked `ambient_width_ge`, `ExtensionCallThree` and
   `endpoint_identity`, and nothing here connects them to the `(V, e)` produced
   above.  *Next round:* build `ExtensionCallThree` from Section 3's `e` and
   `classWidth k`.
4. **`09:1512--1531` (`sec:wrapper-mass-redistribution`) is not entered**, exactly
   as `PROTECTED-ROW-RESERVOIRS-001` item 3 leaves it.  Section 5 supplies only a
   domination and an averaging statement about the built `P_v`; `P_B`, `J_clean`,
   `J_good` and `eq:wrapper-total-early-mass` are untouched.
5. **The canonical inhabitation of the selection is REGISTERED and DEFERRED** (see
   Section 6).  The paper's own instance of `USetSelected` is the selection run
   inside `lem:early-protected-closure` at the retained matrix `U'` and the
   alleged protocol of `09:1188--1193`, at the schedule's *materialized*
   parameters (`06:859--887`, MATERIALIZE-001 on the Lean side), and at the
   retained outer column set of `09:1458--1459` -- none of which is built.  Both
   Section-6 tiers are labelled **NON-FIDELITY** and neither discharges that
   obligation: the schedule-tier pair repairs the *parameter* half only, and its
   protocol, column and template halves remain ours.
-/

namespace EthInapproximability.ParameterizedNP.UsetSelection

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.RetentionSupply
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.ProtectedEarlyClosure
open EthInapproximability.ParameterizedNP.ProtectedRowReservoirs

/-! ## Section 1  The `d_j` family and `D_mass` (`09:1433--1436`)

"Let `d_j in [0,1]` be the retained relative density of this type from donor `j`,
and write `D_mass = sum_j d_j`."

The banked `ProtectedRowReservoirs.reservoirDensity` already *is* `d_j`; what is
missing for `09:1441`'s classification step is its presentation as a function of
the donor index, which is the shape `exists_protected_dyadic_class` consumes.
Nothing here re-defines a density: `donorDensity` is a re-association and
`dMass` is a sum. -/

section Densities

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1434--1435`, the family `j |-> d_j`.**  The retained relative density of
one protected reservoir type, as a function of the donor index -- the frozen
`d_j` of `09:1434` read as the `d : iota -> R` argument that
`WrapperProtectedEarly.exists_protected_dyadic_class` classifies.

The donor index is the **outer coordinate** `J_0 subseteq [q]` of `09:1375` at
the scale-alignment width `q = 2^r` of `09:105--107`; neither `q_2` nor the second
interlace width `Q` is involved. -/
noncomputable def donorDensity (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (p : List Bool) : Fin q → ℝ :=
  fun i => reservoirDensity P Res i p

/-- **`09:1436`, `D_mass = sum_j d_j`.**  The total retained density of one
protected reservoir type over a donor set, at the node addressed by `p`. -/
noncomputable def dMass (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (J : Finset (Fin q)) (p : List Bool) : ℝ :=
  ∑ i ∈ J, donorDensity P Res p i

variable (P : Protocol {a // a ∈ Rset} Yc Zc) (Res : Finset Rw) (p : List Bool)

/-- **Aux 1a (identity).**  `donorDensity` is the banked `reservoirDensity`
re-associated and nothing else.  General. -/
@[simp] theorem donorDensity_apply (i : Fin q) :
    donorDensity P Res p i = reservoirDensity P Res i p := rfl

/-- **Aux 1b (`09:1434`, `0 <= d_j`).**  Inherited from the banked
`reservoirDensity_nonneg`; the frozen bracket is a theorem, not a hypothesis.
General. -/
theorem donorDensity_nonneg (i : Fin q) : 0 ≤ donorDensity P Res p i :=
  reservoirDensity_nonneg P Res i p

/-- **Aux 1c (`09:1434`, `d_j <= 1`).**  Inherited from the banked
`reservoirDensity_le_one`.  General. -/
theorem donorDensity_le_one (i : Fin q) : donorDensity P Res p i ≤ 1 :=
  reservoirDensity_le_one P Res i p

/-- **Aux 1d (degeneracy).**  No donors, no mass.  General. -/
@[simp] theorem dMass_empty : dMass P Res (∅ : Finset (Fin q)) p = 0 := by
  simp [dMass]

/-- **Aux 1e.**  `D_mass >= 0`.  General. -/
theorem dMass_nonneg (J : Finset (Fin q)) : 0 ≤ dMass P Res J p :=
  Finset.sum_nonneg fun i _ => donorDensity_nonneg P Res p i

/-- **Aux 1f (monotonicity).**  Adding donors can only add retained density --
the property that makes `09:1441`'s "discard donors" step a passage to a
*subset*.  General. -/
theorem dMass_mono {J₀ J₁ : Finset (Fin q)} (h : J₀ ⊆ J₁) :
    dMass P Res J₀ p ≤ dMass P Res J₁ p :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => donorDensity_nonneg P Res p i

/-- **Aux 1g (the ceiling `09:1434` imposes).**  Since every `d_j` is at most one,
`D_mass` never exceeds the number of donors.  This is the fact that makes the
frozen threshold `09:1439` a genuine constraint on the donor set rather than a
statement about a single large density.  General. -/
theorem dMass_le_card (J : Finset (Fin q)) : dMass P Res J p ≤ (J.card : ℝ) := by
  calc dMass P Res J p ≤ ∑ _i ∈ J, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => donorDensity_le_one P Res p i
    _ = (J.card : ℝ) := by simp

/-- **Aux 1h (the threshold forces donors).**  Any lower bound on `D_mass` is
inherited by the donor count.  Applied at the frozen `09:1439` threshold this
says `64 B_theta L_q s kappa <= |J_0|`, which is exactly why the class `V` of
`09:1444` can be large enough to contain a `u`-set.  General in the bound. -/
theorem card_ge_of_dMass_ge {J : Finset (Fin q)} {c : ℝ}
    (h : c ≤ dMass P Res J p) : c ≤ (J.card : ℝ) :=
  h.trans (dMass_le_card P Res p J)

/-- **Aux 1i (the root readout).**  At the root of the alleged protocol every
retained reservoir row is still held, so `D_mass` is the total retained fraction.
The banked `reservoirDensity_nil` summed.  General. -/
theorem dMass_nil (J : Finset (Fin q)) :
    dMass P Res J ([] : List Bool)
      = ∑ i ∈ J, ((retainedRefRows Rset Res i).card : ℝ) / (Res.card : ℝ) :=
  Finset.sum_congr rfl fun i _ => reservoirDensity_nil P Res i

end Densities

/-! ## Section 2  One of the two types carries `D_mass` (`09:1433--1439`)

"One of the two protected reservoir types contributes at least half of
`eq:protected-early-threshold` ... Then `D_mass >= 64 B_theta L_q s kappa`."

The halving arithmetic is the banked
`WrapperProtectedEarly.protected_reservoir_halving`, stated on an abstract pair
of density families.  What is new is that its `hthr` binder -- the frozen
threshold on `P_v(J_0)` -- is now discharged at the **built** `P_v`, through the
banked `ProtectedRowReservoirs.donorMass_systemPv`.  This is the census's
ruled-in use of that deliverable. -/

section TypeSplit

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*} {ι V : Type*}

/-- **`09:1433--1439` at the built reservoirs.**

From `eq:protected-early-threshold` (`09:1421--1425`) at the built `P_v` --
`128 mu_P B_theta L_q s kappa <= P_v(J_0)` -- one of the two built reservoirs
carries `09:1439`'s `D_mass >= 64 B_theta L_q s kappa` over the frozen donor
image of `09:1519--1520`.

*The two mass hypotheses are the paper's, not free parameters.*  `hSig` and `hD`
are `09:1370--1374` at the built reservoirs; at the paper's own carriers they are
the theorems `ProtectedRowReservoirs.{selReservoirF_card_eq_muP_mul,
diagReservoirF_card_eq_muP_mul}`.  They are explicit binders, never a bundle, so
this lemma stays general in the row carrier.

*Why `mu_P` cancels and the constant halves.*  `P_v({j}) = mu_P (d_0 + d_1)` is
the banked readout, so the threshold `128 mu_P B L s kappa` on the left becomes
`128 B L s kappa` on the two density sums, and "one of the two contributes at
least half" is `64 B L s kappa`.  Nothing here re-derives that: it is the banked
`protected_reservoir_halving` applied at the frozen donor image.

General in the row carrier, the donor index, the node type, the width, and the
four constants. -/
theorem exists_heavy_reservoir_type (P : Protocol {a // a ∈ Rset} Yc Zc)
    (node : V → List Bool) (donor : ι → Fin q) {RSig RD : Finset Rw} {m : ℕ}
    (hm : 0 < m) (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ))
    {B L : ℕ} {s κ : ℝ} (J₀ : Finset ι) (v : V)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hthr : 128 * muP * (B : ℝ) * (L : ℝ) * s * κ
      ≤ donorMass (systemPv P node donor RSig RD m) J₀ v) :
    64 * (B : ℝ) * (L : ℝ) * s * κ ≤ dMass P RSig (J₀.image donor) (node v) ∨
      64 * (B : ℝ) * (L : ℝ) * s * κ ≤ dMass P RD (J₀.image donor) (node v) := by
  classical
  rw [donorMass_systemPv P node donor hm hSig hD J₀ v hinj] at hthr
  exact protected_reservoir_halving (J₀.image donor)
    (fun i => reservoirDensity P RSig i (node v))
    (fun i => reservoirDensity P RD i (node v)) hthr

end TypeSplit

/-! ## Section 3  The dyadic class and the width (`09:1441--1456`)

"Discard donors with `d_j < D_mass/(2q)` ... Partition the others into at most
`L_q` dyadic classes `d_cls/2 < d_j <= d_cls`.  Some class `V` satisfies
`|V| d_cls >= D_mass/(2 L_q)`.  Let `u` be the least power of two at least
`8 s kappa/d_cls`.  Then `8 s kappa <= u d_cls < 16 s kappa`, `|V| >= u B_theta`."

Both halves are banked arithmetic (`exists_protected_dyadic_class`,
`exists_width_u`); this section is the prescription of
`PROTECTED-ROW-RESERVOIRS-001`'s GAP item 1 executed literally, at
`d := donorDensity P Res p`. -/

section DyadicClass

/-- **Aux 3a (`09:1451--1452` forces `4 | u`).**

`eq:protected-dyadic-class` gives `8 s kappa <= u d_cls` and `d_cls <= 1`, so
`u >= 8 s kappa >= 16` at the frozen floors `s >= 1`, `kappa >= 2`; hence
`u = 2^e` has `e >= 4`.

This is the fact that makes `lem:template-coordinate-extraction`'s divisibility
requirement (`09:1390--1391`, "`u` is / divisible by four") *available* rather than
assumed: the banked `selectedColumnDensity` asks for `2 <= e`, and `e >= 4` is
strictly stronger.  It is also why `D:761--762`'s power-of-two product count
`u/2 = 2^{e-1}` is a positive power of two.  The banked
`WrapperProtectedEarly.width_exponent_ge` proves the sharper `e >= r_3 + ell + 3`
but only at the *dyadic* `s = 2^{r_3}`, `kappa = 2^{ell}`; this statement holds at
every legal `(s, kappa)` and is what the composition below needs.  General. -/
theorem four_le_width_exponent {e s κ : ℕ} {dcls : ℝ} (hs : 1 ≤ s) (hκ : 2 ≤ κ)
    (hdcls1 : dcls ≤ 1) (hlow : 8 * ((s : ℝ) * κ) ≤ (2 : ℝ) ^ e * dcls) : 4 ≤ e := by
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hκR : (2 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hle : (2 : ℝ) ^ e * dcls ≤ (2 : ℝ) ^ e := by nlinarith
  have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ e := by nlinarith
  by_contra hcon
  push Not at hcon
  have hnat : (2 : ℕ) ^ e < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hcon
  have hcast := (Nat.cast_lt (α := ℝ)).mpr hnat
  push_cast at hcast
  linarith

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1441--1456` AT THE BUILT RESERVOIR DENSITIES.**

The prescription of `PROTECTED-ROW-RESERVOIRS-001` GAP item 1, executed: from
`09:1439`'s `D_mass >= 64 B_theta L_q s kappa` on the *built* densities of one
protected reservoir, the frozen proof's dyadic class `V`, its representative
`d_cls = classWidth k`, and its width `u = 2^e` all exist, satisfying
`eq:protected-dyadic-class` and `eq:protected-delta-min`.

Every clause is the frozen one:

* `V subseteq J` and `d_cls/2 < d_j <= d_cls` on `V` is `09:1443--1444`;
* `8 s kappa <= u d_cls < 16 s kappa` is `eq:protected-dyadic-class` (`09:1452`);
* `u B_theta <= |V|` is the second half of the same display (`09:1454`);
* `64 B_theta L_q s/q <= d_cls` is `eq:protected-delta-min` (`09:1486--1490`),
  carried rather than dropped, because Localized Extension call (iii) reads its
  per-block row density from `d_cls/4` (`06:1151`);
* `4 <= e` is `four_le_width_exponent`, i.e. `09:1451--1452` read at the frozen
  floors, and it is what supplies `09:1390--1391`'s `4 | u` downstream.

*Why the trivial witness fails.*  `V := empty` is refuted by the clause
`u B_theta <= |V|`, since `u B_theta >= 16` at every legal `theta`
(`empty_class_fails_the_width_bound` below); and the hypothesis itself is not
vacuously satisfiable at an empty donor set, since `card_ge_of_dMass_ge` forces
`64 B_theta L_q s kappa <= |J|`.

*Nothing about the protocol, the reservoirs' geometry or the Stage-4 entry maps
is asserted.*  The alleged protocol `P`, the retained row set `Rset`, the
reservoir `Res` and the route `p` are all arbitrary, and only the two banked
facts `0 <= d_j <= 1` are used about them.

General in the row carrier, the width, the alleged protocol, the reservoir and
the route. -/
theorem exists_reservoir_dyadic_class (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (p : List Bool) (J : Finset (Fin q)) {s κ : ℕ} {θ : ℝ}
    (hq : 0 < q) (hs : 1 ≤ s) (hκ : 2 ≤ κ) (hθ : 0 < θ)
    (hmass : 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s * κ ≤ dMass P Res J p) :
    ∃ (k e : ℕ) (V : Finset (Fin q)),
      V ⊆ J ∧ 4 ≤ e ∧
      (∀ i ∈ V, classWidth k < 2 * donorDensity P Res p i ∧
        donorDensity P Res p i ≤ classWidth k) ∧
      8 * ((s : ℝ) * κ) ≤ (2 : ℝ) ^ e * classWidth k ∧
      (2 : ℝ) ^ e * classWidth k < 16 * ((s : ℝ) * κ) ∧
      64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s / q ≤ classWidth k ∧
      2 ^ e * Btheta θ ≤ V.card := by
  classical
  have hJq : J.card ≤ q := by simpa using J.card_le_univ
  obtain ⟨k, V, hVsub, hVspec, hVheavy, hVdelta⟩ :=
    exists_protected_dyadic_class (ι := Fin q) J (donorDensity P Res p) hq hs hκ hθ
      hJq (fun i _ => donorDensity_nonneg P Res p i)
      (fun i _ => donorDensity_le_one P Res p i) hmass
  obtain ⟨e, _he1, hlow, hhigh, hVcard⟩ :=
    exists_width_u (B := Btheta θ) (s := s) (κ := κ) (dcls := classWidth k)
      (Vcard := (V.card : ℝ)) (classWidth_pos k) (classWidth_le_one k) hs hκ
      (one_le_Btheta hθ) hVheavy
  refine ⟨k, e, V, hVsub, four_le_width_exponent hs hκ (classWidth_le_one k) hlow,
    hVspec, hlow, hhigh, hVdelta, ?_⟩
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ e * (Btheta θ : ℝ) := by positivity
  have hR : ((2 ^ e * Btheta θ : ℕ) : ℝ) ≤ ((V.card : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hR

end DyadicClass

/-! ## Section 4  The whole of `09:1441--1471`

`USetSelected` names the frozen deliverable of the block: the dyadic class, its
width, the `u`-set outside the poor cover, the `rho_1`-dense Bob child, and the
`u/2` template coordinates with the entering density `rho_1 2^{-u-1}` of
`06:1150`.  `uSetSelection_of_dMass` produces it from `09:1439`'s threshold on the
built densities, by handing Section 3's `(V, e)` to the banked
`WrapperProtectedEarly.selectedColumnDensity`, which is `09:1458--1471` as
arithmetic on an abstract class. -/

section Selection

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **The `09:1441--1471` deliverable, named.**

Named as a `Prop` so that the two producers of Section 4 and the Section-6 probe
speak about one and the same object, and so that the fourteen frozen clauses are
written down exactly once.  It is a **conclusion** bundle, never a hypothesis
bundle: no declaration below takes it as a premise except the two general readout
lemmas, which only project out of it.

The clauses, in the frozen print order:

1. `V subseteq J` -- `09:1442`, the class is drawn from the surviving donors;
2. `4 <= e` -- `09:1451--1452` at the frozen floors, which supplies `4 | u`;
3. `d_cls/2 < d_j <= d_cls` on `V` -- `09:1443--1444`;
4. and 5. `8 s kappa <= u d_cls < 16 s kappa` -- `eq:protected-dyadic-class`;
6. `delta_min <= d_cls` -- `eq:protected-delta-min` (`09:1486--1490`);
7. `u B_theta <= |V|` -- the second half of `eq:protected-dyadic-class`;
8. and 9. the selected `u`-set: `J_sel subseteq V`, `|J_sel| = u` -- `09:1462`;
10. `J_sel` is not poor -- `09:1458--1463`;
11. and 12. the Bob child's provenance and `rho_1` density -- `09:1463--1464`;
13. and 14. the `u/2` template coordinates and their entering density
    `callThreeH e = rho_1 2^{-u-1}` -- `09:1466--1469` with `06:1150`.

*Why the trivial witness fails.*  Clause 11 pins the produced child `Pc` to the
relabelled parent `ambientRelabel J_sel eJ S`, so `Pc := univ` -- which would make
clause 14 free -- is refuted whenever the projection is proper, exactly as the
banked `selectedColumnDensity_univ_child_pole` records; and clause 7 refutes
`V := empty`.  Neither the class nor the child can be chosen independently of `S`.

*Non-vacuity at LEGAL parameter values.*  `uSetSelection_at_scheduleTheta`
(Section 6) inhabits this predicate at `theta = 1/(160 Q)` of `eq:Q-theta-choice`,
`s = 2^{r_3}` under `eq:s-choice`'s `512 <= s` with `64 | s`, `kappa = 2^{ell}`
at the `09:1420` floor, and a width `q = 2^{A_wrap L_P^2}` of `eq:q-deltaU` --
every one obtained by *evaluating* the frozen defining display rather than by
assigning a numeral.  The round-`r0` floor-tier probe `uSetSelection_probe` runs
at `(s, theta, q) = (4, 1/20480, 2^24)`, which the same three displays refute
(`floorTier_point_fails_the_schedule_tier`), and carries **no** legality claim.
The *canonical* inhabitation -- the paper's own selection inside
`lem:early-protected-closure` -- remains registered and deferred; see the
Section-6 header. -/
def USetSelected {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Protocol {a // a ∈ Rset} Yc Zc) (Res : Finset Rw) (p : List Bool)
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J : Finset (Fin q)) (s κ : ℕ)
    (θ : ℝ) : Prop :=
  ∃ (k e : ℕ) (V Jsel : Finset (Fin q)) (eJ : Fin (2 ^ e) ≃ ↥Jsel)
    (Pc : Finset (Fin (2 ^ e) → Y)) (J' : Finset (Fin (2 ^ e))),
    V ⊆ J ∧ 4 ≤ e ∧
    (∀ i ∈ V, classWidth k < 2 * donorDensity P Res p i ∧
      donorDensity P Res p i ≤ classWidth k) ∧
    8 * ((s : ℝ) * κ) ≤ (2 : ℝ) ^ e * classWidth k ∧
    (2 : ℝ) ^ e * classWidth k < 16 * ((s : ℝ) * κ) ∧
    64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s / q ≤ classWidth k ∧
    2 ^ e * Btheta θ ≤ V.card ∧
    Jsel ⊆ V ∧ Jsel.card = 2 ^ e ∧ ¬ PoorProjection rhoZero Jsel S ∧
    Pc ⊆ ambientRelabel Jsel eJ S ∧
    rhoOne * (Fintype.card Y : ℝ) ^ (2 ^ e) ≤ (Pc.card : ℝ) ∧
    J'.card = 2 ^ e / 2 ∧
    callThreeH e * (YT.card : ℝ) ^ (2 ^ e / 2)
      ≤ ((projSet J' (Pc.filter (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ)

/-- **`09:1441--1471` PRODUCED at the built reservoir densities.**

The composition: Section 3 turns `09:1439`'s threshold on the built `d_j` into the
frozen `(V, d_cls, u = 2^e)`, and the banked
`WrapperProtectedEarly.selectedColumnDensity` turns that class into the poor-cover
survivor, the `rho_1`-dense Bob child and the `u/2` template coordinates.

The binders that are **not** discharged, and are honest GAP:

* `hQuery` is `09:1463`'s "after Bob's query": the alleged protocol is not
  modelled, so the relabelling of the selected donors as the coordinates of `Y^u`
  and the split of the relabelled parent into two children are *assumed*.  The
  binder is stated uniformly in the width so that Section 3's `e` -- which is
  produced, not supplied -- can be fed to it.  It asserts only the *geometry* of
  a query (a partition), never its conclusion, and the banked
  `bobQuery_partition_is_satisfiable` shows it carries no existence burden;
* `hS` is `09:1458--1459`'s "the retained outer / column set", whose `theta`-density is
  the frozen input of `lem:product-projection-cover`;
* `hYT`, `hgap` are `09:1466`'s "The schedule gives `1 - lambda_T <= 1/100 <=
  rho_1/8`"; the banked `one_hundredth_le_rhoOne_div_eight` is the schedule half
  and is not restated here, so `hgap` is the frozen inequality itself.

*Why the trivial witness fails.*  See `USetSelected`: the produced child is
pinned to the relabelled parent, and the produced class must meet
`u B_theta <= |V|`.

General in the row carrier, the column alphabet, the width, the alleged protocol,
the reservoir and the route. -/
theorem uSetSelection_of_dMass {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Protocol {a // a ∈ Rset} Yc Zc) (Res : Finset Rw) (p : List Bool)
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J : Finset (Fin q))
    {s κ : ℕ} {θ lamT : ℝ}
    (hq : 0 < q) (hs : 1 ≤ s) (hκ : 2 ≤ κ) (hθ : 0 < θ) (hY : 0 < Fintype.card Y)
    (hmass : 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s * κ ≤ dMass P Res J p)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ (u : ℕ) (Jq : Finset (Fin q)), Jq.card = u →
      ∃ (eJ : Fin u ≃ ↥Jq) (P₀ P₁ : Finset (Fin u → Y)),
        Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel Jq eJ S) :
    USetSelected P Res p S YT J s κ θ := by
  classical
  obtain ⟨k, e, V, hVsub, he4, hVspec, hlow, hhigh, hdelta, hVcard⟩ :=
    exists_reservoir_dyadic_class P Res p J hq hs hκ hθ hmass
  obtain ⟨Jsel, eJ, Pc, J', hJselV, hJselcard, hpoor, hPsub, hPdense,
      hJ'card, hJ'dense⟩ :=
    selectedColumnDensity (e := e) S YT V hY hθ (le_trans (by norm_num) he4) hVcard
      hS hYT hgap (fun Jq _ hJqcard => hQuery (2 ^ e) Jq hJqcard)
  exact ⟨k, e, V, Jsel, eJ, Pc, J', hVsub, he4, hVspec, hlow, hhigh, hdelta,
    hVcard, hJselV, hJselcard, hpoor, hPsub, hPdense, hJ'card, hJ'dense⟩

end Selection

section SelectionFromThreshold

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*} {ι V : Type*}

/-- **`eq:protected-early-threshold` (`09:1421--1425`) TO `09:1471`, at the built
`P_v`.**

The frozen hypothesis of `lem:early-protected-closure`, stated on the built
protected mass `P_v(J_0)` of `PROTECTED-ROW-RESERVOIRS-001`, reaches the frozen
output of `09:1471` with no abstract density left in between: Section 2 splits
the two reservoir types, Section 3 classifies the surviving type's donors, and
Section 4 runs the cover and the extraction.

The disjunction is `09:1433` itself -- "one of the two protected reservoir types
contributes at least half" -- and is deliberately *not* collapsed: the frozen
proof does not say which type, and neither does this statement.

**The lemma's conclusion is NOT `lem:early-protected-closure`'s conclusion.**  No
communication-complexity bound is stated, `C` does not occur, and
`WrapperProtectedEarly.earlyProtectedClosure` is consumed nowhere in this module.

*Hypothesis consistency.*  The bundle is not vacuous: the two mass binders are
theorems at the paper's carriers (`ProtectedRowReservoirs.{selReservoirF_card_eq_muP_mul,
diagReservoirF_card_eq_muP_mul}`), `hQuery` is satisfiable with no protocol
(`bobQuery_partition_is_satisfiable`), and `uSetSelection_probe` below exhibits a
point at which every remaining hypothesis holds simultaneously in the kernel.

General in the row carrier, the column alphabet, the donor index, the node type
and the width. -/
theorem uSetSelection_of_protectedMass {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Protocol {a // a ∈ Rset} Yc Zc) (node : V → List Bool) (donor : ι → Fin q)
    {RSig RD : Finset Rw} {m : ℕ} (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ))
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J₀ : Finset ι) (v : V)
    {s κ : ℕ} {θ lamT : ℝ}
    (hq : 0 < q) (hs : 1 ≤ s) (hκ : 2 ≤ κ) (hθ : 0 < θ) (hY : 0 < Fintype.card Y)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hthr : 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * s * κ
      ≤ donorMass (systemPv P node donor RSig RD m) J₀ v)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ (u : ℕ) (Jq : Finset (Fin q)), Jq.card = u →
      ∃ (eJ : Fin u ≃ ↥Jq) (P₀ P₁ : Finset (Fin u → Y)),
        Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel Jq eJ S) :
    USetSelected P RSig (node v) S YT (J₀.image donor) s κ θ ∨
      USetSelected P RD (node v) S YT (J₀.image donor) s κ θ := by
  classical
  rcases exists_heavy_reservoir_type P node donor hm hSig hD J₀ v hinj hthr with
    hSigMass | hDMass
  · exact Or.inl (uSetSelection_of_dMass P RSig (node v) S YT (J₀.image donor)
      hq hs hκ hθ hY hSigMass hS hYT hgap hQuery)
  · exact Or.inr (uSetSelection_of_dMass P RD (node v) S YT (J₀.image donor)
      hq hs hκ hθ hY hDMass hS hYT hgap hQuery)

end SelectionFromThreshold

section Readouts

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **Aux 4a (readout: the selection really selects donors).**  `09:1462`'s
surviving `u`-set is a set of at least `16` of the donors it was drawn from --
`u = 2^e` with `e >= 4`.  A round-trip check on the encoding: the deliverable
cannot be satisfied by an empty or singleton coordinate set, which is what makes
"`u`-set of donors" a genuine product width.  General. -/
theorem uSetSelected_gives_sixteen_donors {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)} {s κ : ℕ}
    {θ : ℝ} (h : USetSelected P Res p S YT J s κ θ) :
    ∃ Jsel : Finset (Fin q), Jsel ⊆ J ∧ 16 ≤ Jsel.card := by
  obtain ⟨_k, e, V, Jsel, _eJ, _Pc, _J', hVJ, he4, _, _, _, _, _, hJselV,
    hJselcard, _, _, _, _, _⟩ := h
  refine ⟨Jsel, hJselV.trans hVJ, ?_⟩
  rw [hJselcard]
  calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he4

/-- **Aux 4b (readout: the class width is in the frozen window).**  The produced
`d_cls` satisfies `eq:protected-dyadic-class` at the produced width: this is the
projection of the deliverable that Localized Extension call (iii) reads.
General. -/
theorem uSetSelected_width_window {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)} {s κ : ℕ}
    {θ : ℝ} (h : USetSelected P Res p S YT J s κ θ) :
    ∃ (k e : ℕ), 4 ≤ e ∧ 8 * ((s : ℝ) * κ) ≤ (2 : ℝ) ^ e * classWidth k ∧
      (2 : ℝ) ^ e * classWidth k < 16 * ((s : ℝ) * κ) := by
  obtain ⟨k, e, _V, _Jsel, _eJ, _Pc, _J', _, he4, _, hlow, hhigh, _, _, _, _, _,
    _, _, _, _⟩ := h
  exact ⟨k, e, he4, hlow, hhigh⟩

end Readouts

/-! ## Section 5  The frontier-sum contact (census: ruled in only here)

`09:1537`'s `sum_{v : first-Bob frontier node} P_v({j})` is the banked
`ProtectedRowReservoirs.firstBobMass_systemPv`, and it belongs to
`sec:wrapper-mass-redistribution` (`09:1512--`), not to the traced range.  The
census above rules it in at exactly one point: the selection of Sections 3--4 runs
at **one** node, and the frontier sum *dominates* that node's contribution.  Both
statements below are that domination, in the two directions a later tranche can
use, and neither classifies a donor, mentions `eta_R`, or enters
`sec:wrapper-mass-redistribution`. -/

section FrontierContact

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*} {Coord ι V : Type*}

/-- **`09:1537` dominates the per-node readout, at the built `P_v`.**

A first-Bob frontier node's own protected mass from donor `j` is at most the
frontier sum, because every summand is a nonnegative multiple of `mu_P`.  This is
the census's ruled-in contact between the aggregate of `09:1537` and the
single-node selection of `09:1441--1471`: it says the two quantities are
comparable and in which direction, and it says nothing else.

The banked `firstBobMass_systemPv` is consumed by pin in the proof term; its
three mass binders are passed through unchanged.  General. -/
theorem nodeReadout_le_firstBobMass_systemPv [Fintype V]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {r A0 : ℕ}
    (S : RoutedSystem P Coord ι V r A0) (donor : ι → Fin q)
    {RSig RD : Finset Rw} {m : ℕ} (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ)) (j : ι)
    {v : V} (hv : v ∈ S.toWrapperFrontier.bobNodes) :
    muP * (donorDensity P RSig (S.node v) (donor j)
        + donorDensity P RD (S.node v) (donor j))
      ≤ firstBobMass S (systemPv P S.node donor RSig RD m) j := by
  classical
  rw [firstBobMass_systemPv S donor hm hSig hD j]
  refine Finset.single_le_sum (f := fun w : V => muP *
    (reservoirDensity P RSig (donor j) (S.node w)
      + reservoirDensity P RD (donor j) (S.node w))) ?_ hv
  intro w _
  have h1 := reservoirDensity_nonneg P RSig (donor j) (S.node w)
  have h2 := reservoirDensity_nonneg P RD (donor j) (S.node w)
  have hμ := muP_pos
  nlinarith

/-- **The averaging in the same direction, general.**

If the frontier sum of `09:1537` is at least `c` times the number of first-Bob
nodes, some node's own readout is at least `c`.  Pure pigeonhole over the banked
`firstBobMass_systemPv`.

**This is availability, not a transcription.**  No sentence of `09:1441--1471`
performs this step -- the frozen proof fixes its node at `09:1418--1420` -- and
the paper's own use of the frontier sum is inside
`sec:wrapper-mass-redistribution`, where `09:1541--1547` is
`eq:wrapper-bob-heavy-count`, i.e. the bound
`e_B <= 512 mu_P B_theta L_q s e_0 / ((1 - vartheta) eta_R)` on the *number of
Bob-heavy donors* -- **not** a frontier-sum-to-node bridge, as round `r0`'s
one-line description said.  That whole range is GAP-EXPOSED item 4 and is **not**
entered here.  It is landed because it is
the only shape in which a later tranche can legally supply
`eq:protected-early-threshold` at a node from an aggregate, and landing it now
keeps that step visible instead of hidden inside a future proof.  General. -/
theorem exists_bobNode_readout_ge [Fintype V]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {r A0 : ℕ}
    (S : RoutedSystem P Coord ι V r A0) (donor : ι → Fin q)
    {RSig RD : Finset Rw} {m : ℕ} (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ)) (j : ι) {c : ℝ}
    (hne : (S.toWrapperFrontier.bobNodes).Nonempty)
    (hsum : c * ((S.toWrapperFrontier.bobNodes).card : ℝ)
      ≤ firstBobMass S (systemPv P S.node donor RSig RD m) j) :
    ∃ v ∈ S.toWrapperFrontier.bobNodes,
      c ≤ muP * (donorDensity P RSig (S.node v) (donor j)
        + donorDensity P RD (S.node v) (donor j)) := by
  classical
  rw [firstBobMass_systemPv S donor hm hSig hD j] at hsum
  by_contra hcon
  push Not at hcon
  have hlt : ∑ w ∈ S.toWrapperFrontier.bobNodes,
      muP * (reservoirDensity P RSig (donor j) (S.node w)
        + reservoirDensity P RD (donor j) (S.node w))
      < ∑ _w ∈ S.toWrapperFrontier.bobNodes, c :=
    Finset.sum_lt_sum_of_nonempty hne fun w hw => hcon w hw
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  nlinarith [hsum, hlt]

end FrontierContact

/-! ## Section 6  Inhabitation

**CANONICAL INHABITATION IS REGISTERED AND DEFERRED.**  The paper's own instance
of `USetSelected` is the selection carried out inside the frozen proof of
`lem:early-protected-closure`: its retained outer column set is the one of
`09:1458--1459` inside the retained matrix `U'` of `09:1188--1191`, its protocol
is the alleged `(C+r-1)`-cost protocol of `09:1192--1193`, its `Y_T` is the
template set of `09:367--371`, and all of these live at the schedule's
**materialized** parameters (`06:859--887`, MATERIALIZE-001 on the Lean side).
None of that is built, so the obligation is registered here and is discharged
when the materialization lands.  It is **never** satisfied by any inhabitant
below, at either tier.

### The schedule-tier values, and how each one is obtained (round `r1`)

Round `r0` supplied `USetSelected` with a single inhabitant, at
`(s, kappa, theta, q) = (4, 2, 1/20480, 2^24)`, and called those numerals legal.
Three of the four are values the frozen definitional chain **cannot produce**.
The schedule-tier inhabitants below therefore take every quantity the frozen
source defines by *evaluating* that definition, in dependency order:

* **`s = 2^{r_3}` with `9 <= r_3`, plus `64 | s`.**  `s` is DEFINED at
  `eq:s-choice` (`06:110--121`): `u = clog_2(clog_2(A_pre + 16))` and
  `s = 2^{ceil(B_s u^2)}`, with `A_pre = max{16, b_out, ...} >= 16` and `B_s` a
  *positive integer* of the universal configuration field (`06:56--61`).
  Evaluating: `A_pre + 16 >= 32`, so `clog_2(A_pre + 16) >= 5`, so `u >= 3`, so
  `s >= 2^{B_s . 9} >= 2^9 = 512`.  Independently `06:394--395` states `64 | s`
  outright.  Both consequences enter as the binder `9 <= r_3` and are *returned*
  in the deliverable rather than assumed downstream.  `04:389`, `04:460`,
  `04:481`, `04:504` and `04:619` give only the **floor** `s >= 4` a power of
  two: a floor is not a defining display, and reading `s = 4` off it was exactly
  the round-`r0` defect.
* **`kappa = 2^{ell}` with `1 <= ell`.**  `09:1420` fixes `kappa = kappa_v >= 2`
  and leaves `kappa_v` genuinely free per node; the banked
  `FirstBobFrontierInstance.firstBob_capacity_dyadic` puts it in the form
  `2^{ell}`.  `2` is the frozen floor and is the value the paper's own display
  admits, so it enters as `1 <= ell` and is likewise returned.
* **`theta = 1/(160 Q)` at `Q = EntryGates.Qwidth b_out delta_U`.**  `theta` is
  DEFINED at `eq:Q-theta-choice` (`06:527--538`):
  `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`, `Q` the least power of two
  at least `Q_0`, `theta = delta/(16Q)`; `06:539` prints the closed form
  `1/theta = 160 Q` at `delta = 1/10`.  Nothing is pinned: `Q` is the banked
  `EntryGates.Qwidth` -- `06:532`'s least-power-of-two accessor -- so the
  threshold is an expression in the public record's own `b_out` and `delta_U`
  under their frozen side conditions `b_out >= 1` (`05:39--40`) and
  `delta_U <= 1/200` (`06:547`).  Those force `Q_0 >= 16000`, hence `Q >= 2^14`
  and `theta <= 1/2621440` (banked `WrapperProtectedEarly.Q0_route_floor`,
  `Qwidth_route_floor`, `scheduleTheta_route_le`).  The ceiling is *recorded*,
  never used to legalize a value under it.
* **`q = 2^{A_wrap L_P^2}`.**  `q` is DEFINED at `eq:q-deltaU` (`06:513--519`),
  with `L_P = clog_2(P_0)` and `P_0 >= 16` (`06:465--472`), so `L_P >= 4` and
  the reachable exponents are the multiples `A_wrap L_P^2` of a square at least
  `16`.  `A_wrap` is the one genuinely **free** input in sight: `06:520--522`
  fixes only that it is "chosen large enough to dominate every
  protocol-independent exceptional-set bound".  It is therefore *produced* in
  closed form by the banked `WrapperProtectedEarly.exists_wrapper_width` (the pin
  actually consumed below; `exists_wrapper_exponent` is its base) from
  the single demand this block makes on `q`, never picked; the statements below
  carry only `1 <= L_P`, which is weaker than the schedule's `L_P >= 4`, so they
  cover every legal `L_P` and assume less than the schedule provides.

The `B_theta` bracket is not pinned either: the banked
`Btheta_ge_two_at_scheduleTheta` gives `B_theta >= 2` at every schedule
threshold, so the poor-`u`-set cover `u(B_theta - 1)` of `09:1460--1461` is never
the empty cover, and no constant upper bound on `B_theta` is needed -- the width
`q` is produced *from* `B_theta` rather than compared against a numeral for it.

The reservoir half is the paper's at both tiers: `Res` is the frozen
`selReservoirF` at the frozen carriers and multiplicities of
`eq:protected-labelled-carriers` and `eq:protected-multiplicities`.  The
**protocol, column and template halves are ours and the paper never visits
them**: the alleged protocol is a leaf, the retained row set is everything, the
node is the root, the retained outer column set is the full product and the
template set is the full alphabet.  So every inhabitant below is **NON-FIDELITY**
on those halves; the schedule-tier pair is non-fidelity on those halves *only*,
and the floor-tier pair is non-fidelity on the schedule half as well. -/

section Inhabitation

/-- **Aux 6a (the full product carries every density).**  For `0 <= theta <= 1`
the whole column space is `theta`-dense, which is the trivially satisfiable end
of `09:1458--1459`'s density input to `lem:product-projection-cover`.  Landed as a
general lemma because it is the only thing the probe needs about its own `S`, and
it makes plain that the probe assumes nothing about the retained set.  General. -/
theorem univ_column_density {Y : Type*} [Fintype Y] {q : ℕ}
    {θ : ℝ} (hθ1 : θ ≤ 1) :
    θ * (Fintype.card Y : ℝ) ^ q
      ≤ (((Finset.univ : Finset (Fin q → Y)).card : ℕ) : ℝ) := by
  have hcard : ((Finset.univ : Finset (Fin q → Y)).card : ℕ)
      = Fintype.card Y ^ q := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  have hpow : (0 : ℝ) ≤ (Fintype.card Y : ℝ) ^ q := by positivity
  push_cast
  nlinarith

/-- **Aux 6c (`09:1382` evaluated at the floor-tier audit width).**
`L_q = ceil(log_2(2q)) + 1` is at most `26` at `q = 2^24`, because `2q = 2^25`.
Derived from the frozen definition through `Nat.clog_le_of_le_pow`; no value is
assigned to `L_q`, so the statement itself is true arithmetic about `Lq` at a
natural number and claims nothing about legality.

*Tier note (round `r1`).*  `2^24` is **not** a reachable width: `eq:q-deltaU`
(`06:513--519`) gives `q = 2^{A_wrap L_P^2}` with `L_P >= 4` (`06:465--472`), and
`24` is not a multiple of a square at least `16` -- the banked
`WrapperProtectedEarly.wrapper_exponent_ne_twentyfour`.  This lemma is therefore
retained only as the arithmetic the floor-tier probe below is stated at.  The
schedule-tier width identity is the banked `WrapperProtectedEarly.Lq_two_pow`,
`L_q(2^n) = n + 2`, which is what the schedule-tier inhabitants use. -/
theorem Lq_probe_bound : Lq 16777216 ≤ 26 := by
  have hclog : Nat.clog 2 (2 * 16777216) ≤ 25 := Nat.clog_le_of_le_pow (by norm_num)
  simpa [Lq] using Nat.succ_le_succ hclog

/-- **Aux 6d (the floor-tier probe's threshold arithmetic, general in its four
atoms).**

`64 B_theta L_q s kappa <= q` at `B_theta <= 1100`, `L_q <= 26`, `s <= 4`,
`kappa <= 2`, `q = 16777216`.  Stated with the four schedule quantities as
*variables* so that nothing about `Btheta` or `Lq` is unfolded: those are
`Nat.sInf` and `Nat.clog` respectively, and evaluating either inside the
arithmetic would replace a pinned bound by a computation.  General.

*Tier note (round `r1`).*  The four numeric bounds are calibrated to the
floor-tier audit point and to nothing else; the statement is a true implication
about four natural numbers and asserts no legality.  At the schedule tier the
comparison is not made against a numeral at all: `exists_scheduleWidth_threshold`
below *produces* a width dominating `64 B_theta L_q s kappa`, so no upper bound
on `B_theta` is required. -/
theorem probe_threshold_arith {b l s κ : ℕ} (hb : b ≤ 1100) (hl : l ≤ 26)
    (hs : s ≤ 4) (hκ : κ ≤ 2) :
    64 * (b : ℝ) * (l : ℝ) * (s : ℝ) * (κ : ℝ) ≤ (16777216 : ℝ) := by
  have hbR : (b : ℝ) ≤ 1100 := by exact_mod_cast hb
  have hlR : (l : ℝ) ≤ 26 := by exact_mod_cast hl
  have hsR : (s : ℝ) ≤ 4 := by exact_mod_cast hs
  have hκR : (κ : ℝ) ≤ 2 := by exact_mod_cast hκ
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg κ
  nlinarith [hbR, hlR, hsR, hκR, hb0, hl0, hs0, hκ0,
    mul_nonneg hb0 hl0, mul_nonneg (mul_nonneg hb0 hl0) hs0]

/-- **Aux 6b (full retention).**  At the root of a leaf protocol whose retained
row set is everything, a nonempty reservoir's density is exactly `1`.  The banked
`rowsAt_nil`, `retainedRefRows_card_eq` and `refBlock_card` composed.  General;
this is the only fact the probe uses about its own protocol. -/
theorem reservoirDensity_full_retention {Rw : Type*} [Fintype Rw] [DecidableEq Rw]
    {q : ℕ} (Res : Finset Rw) (hRes : Res.Nonempty) (i : Fin q) (z : Bool) :
    reservoirDensity
        (Protocol.leaf (X := {a // a ∈ (Finset.univ :
          Finset (Fin 1 × (Fin q × Rw)))}) (Y := Unit) z) Res i
        ([] : List Bool) = 1 := by
  classical
  have hcount : (rowsAt
      (Protocol.leaf (X := {a // a ∈ (Finset.univ :
        Finset (Fin 1 × (Fin q × Rw)))}) (Y := Unit) z)
      (retainedRefRows Finset.univ Res i) ([] : List Bool)).card = Res.card := by
    rw [rowsAt_nil, retainedRefRows_card_eq, Finset.univ_inter, refBlock_card]
  have hne : ((Res.card : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hRes).ne'
  rw [reservoirDensity, hcount, div_self hne]

/-- **Aux 6e (`09:1436` at full retention over all `q` donors).**  If every
donor's retained relative density is `1`, then `D_mass = q`.  The identity that
turns `09:1439`'s threshold into a comparison against the *width*, which is what
both schedule-tier inhabitants below discharge through `eq:q-deltaU`.  General in
the width, the row carrier and the reservoir; the only hypothesis is
nonemptiness of the reservoir, and `dMass_le_card` shows `q` is the largest
value `D_mass` can take on `q` donors, so this is the extreme point of the frozen
bracket `d_j in [0,1]` rather than an interior guess. -/
theorem dMass_full_retention_univ {Rw : Type*} [Fintype Rw] [DecidableEq Rw]
    {q : ℕ} (Res : Finset Rw) (hRes : Res.Nonempty) (z : Bool) :
    dMass
        (Protocol.leaf (X := {a // a ∈ (Finset.univ :
          Finset (Fin 1 × (Fin q × Rw)))}) (Y := Unit) z) Res
        (Finset.univ : Finset (Fin q)) ([] : List Bool) = (q : ℝ) := by
  classical
  have hone : ∀ i ∈ (Finset.univ : Finset (Fin q)),
      donorDensity
        (Protocol.leaf (X := {a // a ∈ (Finset.univ :
          Finset (Fin 1 × (Fin q × Rw)))}) (Y := Unit) z) Res ([] : List Bool) i = 1 :=
    fun i _ => reservoirDensity_full_retention Res hRes i z
  rw [dMass, Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Aux 6f (`eq:Q-theta-choice` never exceeds one).**  Every schedule threshold
`theta = 1/(160 Q)` of `06:539` is at most `1`, already at `Q = 1`.  Composed from
the banked `WrapperProtectedEarly.scheduleTheta_le_rhoZero` and
`rhoZero_lt_one`, so the cover base `rho_0 = 99/100` of `09:1379` is what
supplies it and no numeral for `theta` is introduced.  This is the only fact
`univ_column_density` needs about a schedule threshold.  General in `Q`. -/
theorem scheduleTheta_le_one {Q : ℕ} (hQ : 0 < Q) : 1 / (160 * (Q : ℝ)) ≤ 1 :=
  le_trans (scheduleTheta_le_rhoZero hQ) (le_of_lt rhoZero_lt_one)

/-- **Aux 6g (`09:1439`'s threshold met at an `eq:q-deltaU` width).**

Given the frozen scale `s = 2^{r_3}`, capacity `kappa = 2^{ell}` and the
schedule's `L_P`, some positive `A_wrap` makes the halved protected threshold
`64 B_theta L_q s kappa <= q` hold at `q = 2^{A_wrap L_P^2}`.

*Everything is evaluated.*  `q` has the `eq:q-deltaU` shape (`06:513--519`),
`L_q` is the frozen `09:1382` definition evaluated by the banked
`WrapperProtectedEarly.Lq_two_pow` (`L_q(2^n) = n + 2`), and `A_wrap` is produced
by the banked `WrapperProtectedEarly.exists_wrapper_width` from `06:520--522`'s
"chosen large enough" stipulation.  No upper bound on `B_theta` is used, and
none is available uniformly: the banked `Btheta_le_tested_at_scheduleTheta` is a
function of `Q`, not a constant, so a width had to be *produced from* `B_theta`
rather than compared against a numeral for it.

General in `theta` (only positivity is used), in `r_3`, `ell` and `L_P`. -/
theorem exists_scheduleWidth_threshold {θ : ℝ} (hθ : 0 < θ) (r₃ ℓ LP : ℕ)
    (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧
      64 * (Btheta θ : ℝ) * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
          * ((2 ^ ℓ : ℕ) : ℝ) ≤ ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) := by
  obtain ⟨Awrap, hA1, hAle⟩ := exists_wrapper_width hθ r₃ ℓ LP hLP
  refine ⟨Awrap, hA1, ?_⟩
  have hnat : 64 * Btheta θ * Lq (2 ^ (Awrap * LP ^ 2)) * 2 ^ r₃ * 2 ^ ℓ
      ≤ 2 ^ (Awrap * LP ^ 2) := by
    rw [Lq_two_pow]
    refine le_trans ?_ hAle
    have h1 : 64 * Btheta θ * (Awrap * LP ^ 2 + 2) * 2 ^ r₃ * 2 ^ ℓ
        = 64 * (Btheta θ * (Awrap * LP ^ 2 + 2) * 2 ^ r₃ * 2 ^ ℓ) := by ring
    have h2 : 128 * Btheta θ * 2 ^ r₃ * 2 ^ ℓ * (Awrap * LP ^ 2 + 2)
        = 128 * (Btheta θ * (Awrap * LP ^ 2 + 2) * 2 ^ r₃ * 2 ^ ℓ) := by ring
    rw [h1, h2]
    exact Nat.mul_le_mul_right _ (by norm_num)
  exact_mod_cast hnat

/-- **SCHEDULE-TIER NON-VACUITY 1: `USetSelected` is inhabited at parameter
values the frozen defining displays produce.**

`09:1441--1471`'s fourteen-clause deliverable holds at
`theta = 1/(160 Q)` (`eq:Q-theta-choice` in the `06:539` closed form, at the
banked `Q = EntryGates.Qwidth b_out delta_U` of `06:532`), at every scale
`s = 2^{r_3}` meeting `eq:s-choice`'s consequences, at every capacity
`kappa = 2^{ell} >= 2` (`09:1420`), and at a width `q = 2^{A_wrap L_P^2}` of the
`eq:q-deltaU` shape with `A_wrap` produced from `06:520--522`.

*Every schedule value is obtained by evaluating its defining display; none is
chosen.*  The four legality consequences the paper's own displays impose --
`512 <= s`, `64 | s` (`06:110--121` with `06:394--395`), `kappa >= 2` (`09:1420`) and
`B_theta >= 2` at this `theta` (banked `Btheta_ge_two_at_scheduleTheta`) -- are
**returned** as conjuncts of the deliverable rather than assumed downstream, so
the statement cannot be read at an illegal point.  `b_out` and `delta_U` enter
only through their frozen side conditions `b_out >= 1` (`05:39--40`) and
`delta_U <= 1/200` (`06:547`); `L_P` carries only `1 <= L_P`, weaker than the
schedule's `L_P >= 4` (`06:465--472`).

*Nondegeneracy.*  `B_theta >= 2` is returned, so the poor-`u`-set cover
`u(B_theta - 1)` of `09:1460--1461` is not the empty cover -- the degenerate
corner in which the whole cover argument has no content.  The produced width
satisfies `e >= 4` (`four_le_width_exponent`), so `u >= 16` donors are selected
(`uSetSelected_gives_sixteen_donors`), and the donor densities sit at the
extreme `d_j = 1` of the frozen bracket `d_j in [0,1]`, where
`dMass_le_card` shows the threshold is hardest to beat by adding donors.

**This is NOT the paper's instance** and does not discharge the deferred
canonical-inhabitation obligation of the Section-6 header: the reservoir half is
the paper's, but the protocol, column and template halves are ours (a leaf
protocol, full retention, the root node, the full column product, the full
template alphabet).  What it does establish is exactly what round `r0` failed to:
that `USetSelected` and the full hypothesis bundle of `uSetSelection_of_dMass`
are simultaneously satisfiable **at values the frozen definitional chain
produces**. -/
theorem uSetSelection_at_scheduleTheta (F : FiniteSlots.Stage1SlotBinding)
    {q₂ : ℕ} {Yf : Type*} [Fintype Yf] [DecidableEq Yf] (hq₂ : 0 < q₂) (y₀ : Yf)
    (z₀ : SelCar F q₂ Yf) (z : Bool)
    {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 200)
    {r₃ ℓ LP : ℕ} (hr₃ : 9 ≤ r₃) (hℓ : 1 ≤ ℓ) (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧
      512 ≤ (2 ^ r₃ : ℕ) ∧ (64 : ℕ) ∣ 2 ^ r₃ ∧ 2 ≤ (2 ^ ℓ : ℕ) ∧
      2 ≤ Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) ∧
      USetSelected
        (Protocol.leaf (X := {a // a ∈ (Finset.univ :
          Finset (Fin 1 × (Fin (2 ^ (Awrap * LP ^ 2))
            × ProtColsFrozen F q₂ Yf)))}) (Y := Unit) z)
        (selReservoirF F q₂ Yf) ([] : List Bool)
        (Finset.univ : Finset (Fin (2 ^ (Awrap * LP ^ 2)) → Bool))
        (Finset.univ : Finset Bool)
        (Finset.univ : Finset (Fin (2 ^ (Awrap * LP ^ 2))))
        (2 ^ r₃) (2 ^ ℓ)
        (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) := by
  classical
  obtain ⟨hM, hS0, hD0⟩ := section8_col_counts_pos F hq₂ y₀
  have hRes : (selReservoirF F q₂ Yf).Nonempty :=
    selReservoir_nonempty z₀ (Nat.mul_pos hM hD0)
  have hQ : 0 < EntryGates.Qwidth bout δU := by
    have := Qwidth_route_floor hb hδ0 hδ
    omega
  have hθ : 0 < 1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) :=
    scheduleTheta_pos hQ
  obtain ⟨Awrap, hA1, hAle⟩ := exists_scheduleWidth_threshold hθ r₃ ℓ LP hLP
  -- `eq:s-choice`'s two consequences and `09:1420`'s floor, as returned facts.
  have hs512 : 512 ≤ (2 ^ r₃ : ℕ) := by
    calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ r₃ := Nat.pow_le_pow_right (by norm_num) hr₃
  have hs64 : (64 : ℕ) ∣ 2 ^ r₃ := by
    refine ⟨2 ^ (r₃ - 6), ?_⟩
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]
    congr 1
    omega
  have hκ2 : 2 ≤ (2 ^ ℓ : ℕ) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hdens := dMass_full_retention_univ (q := 2 ^ (Awrap * LP ^ 2))
    (selReservoirF F q₂ Yf) hRes z
  refine ⟨Awrap, hA1, hs512, hs64, hκ2, Btheta_ge_two_at_scheduleTheta hQ, ?_⟩
  refine uSetSelection_of_dMass
    (lamT := 1) (θ := 1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)))
    _ _ _ _ _ _ (Nat.two_pow_pos _) Nat.one_le_two_pow hκ2 hθ (by simp)
    ?_ ?_ ?_ ?_ ?_
  · rw [hdens]
    exact_mod_cast hAle
  · exact univ_column_density (scheduleTheta_le_one hQ)
  · simp
  · have hρ := rhoOne_pos
    norm_num
    linarith
  · exact fun u Jq hJq => bobQuery_partition_is_satisfiable _ Jq hJq

/-- **SCHEDULE-TIER NON-VACUITY 2: `eq:protected-early-threshold` is reachable at
parameter values the frozen defining displays produce.**

`uSetSelection_of_protectedMass` adds exactly one hypothesis to the bundle that
`uSetSelection_at_scheduleTheta` already exhibits: the frozen threshold
`eq:protected-early-threshold` (`09:1421--1425`,
`P_v(J_0) >= 128 mu_P B_theta L_q s kappa`) on the **built** `P_v`.  This lemma
shows that hypothesis reachable simultaneously with the two frozen mass binders
at the schedule's own `theta`, `s`, `kappa` and `q`.

The mass binders are not assumed: `P_v` is instantiated at the paper's own
reservoirs, where they are theorems, and the per-donor value is the banked
`ProtectedRowReservoirs.protectedMass_probe_full_retention` -- `P_v({j}) = 2 mu_P`,
the frozen `tau` of `08:133` at one donor -- so `mu_P` cancels out of the
comparison exactly as `09:1433--1439` says it does, leaving
`64 B_theta L_q s kappa <= q`, which is `exists_scheduleWidth_threshold`.

**Not a fidelity claim.**  The protocol is a leaf, the retained row set is
everything and the node is the root, so this is *our* point, not the paper's; the
paper's own `P_v` at its own protocol remains the deferred canonical-inhabitation
obligation.  What is repaired relative to round `r0` is the schedule half: every
one of `theta`, `s`, `kappa` and `q` is now an evaluated display rather than a
numeral. -/
theorem protectedMass_threshold_at_scheduleTheta
    (F : FiniteSlots.Stage1SlotBinding) {q₂ : ℕ} {Yf : Type*} [Fintype Yf]
    [DecidableEq Yf] (hq₂ : 0 < q₂) (y₀ : Yf) (z : Bool)
    {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 200)
    {r₃ ℓ LP : ℕ} (hr₃ : 9 ≤ r₃) (hℓ : 1 ≤ ℓ) (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧
      512 ≤ (2 ^ r₃ : ℕ) ∧ (64 : ℕ) ∣ 2 ^ r₃ ∧ 2 ≤ (2 ^ ℓ : ℕ) ∧
      2 ≤ Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) ∧
      128 * muP * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
          * ((2 ^ ℓ : ℕ) : ℝ)
        ≤ donorMass
            (systemPv
              (Protocol.leaf (X := {a // a ∈ (Finset.univ :
                Finset (Fin 1 × (Fin (2 ^ (Awrap * LP ^ 2))
                  × ProtColsFrozen F q₂ Yf)))}) (Y := Unit) z)
              (fun _ : Unit => ([] : List Bool))
              (id : Fin (2 ^ (Awrap * LP ^ 2)) → Fin (2 ^ (Awrap * LP ^ 2)))
              (selReservoirF F q₂ Yf) (diagReservoirF F q₂ Yf)
              (Fintype.card (ProtColsFrozen F q₂ Yf)))
            (Finset.univ : Finset (Fin (2 ^ (Awrap * LP ^ 2)))) () := by
  classical
  have hQ : 0 < EntryGates.Qwidth bout δU := by
    have := Qwidth_route_floor hb hδ0 hδ
    omega
  have hθ : 0 < 1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) :=
    scheduleTheta_pos hQ
  obtain ⟨Awrap, hA1, hAle⟩ := exists_scheduleWidth_threshold hθ r₃ ℓ LP hLP
  have hs512 : 512 ≤ (2 ^ r₃ : ℕ) := by
    calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ r₃ := Nat.pow_le_pow_right (by norm_num) hr₃
  have hs64 : (64 : ℕ) ∣ 2 ^ r₃ := by
    refine ⟨2 ^ (r₃ - 6), ?_⟩
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]
    congr 1
    omega
  have hκ2 : 2 ≤ (2 ^ ℓ : ℕ) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  refine ⟨Awrap, hA1, hs512, hs64, hκ2, Btheta_ge_two_at_scheduleTheta hQ, ?_⟩
  · have hval : ∀ j ∈ (Finset.univ : Finset (Fin (2 ^ (Awrap * LP ^ 2)))),
        systemPv
            (Protocol.leaf (X := {a // a ∈ (Finset.univ :
              Finset (Fin 1 × (Fin (2 ^ (Awrap * LP ^ 2))
                × ProtColsFrozen F q₂ Yf)))}) (Y := Unit) z)
            (fun _ : Unit => ([] : List Bool))
            (id : Fin (2 ^ (Awrap * LP ^ 2)) → Fin (2 ^ (Awrap * LP ^ 2)))
            (selReservoirF F q₂ Yf) (diagReservoirF F q₂ Yf)
            (Fintype.card (ProtColsFrozen F q₂ Yf)) () j = muP + muP :=
      fun j _ => protectedMass_probe_full_retention F hq₂ y₀ j z
    rw [donorMass, Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hμ : (0 : ℝ) < muP := muP_pos
    nlinarith [hAle, hμ]

/-- **FLOOR-TIER SMOKE PROBE (BEYOND-PAPER on every half, the schedule half
included; FULL NON-FIDELITY).**

*What is the paper's, and what is ours.*  Only the reservoir is the paper's --
the frozen `R_Sigma` at the frozen carriers and multiplicities, nonempty at the
legality inputs `0 < q_2` (`06:124`) and `Y_f` inhabited (`08:33`).  The
protocol, column and template halves are ours (a leaf protocol, full retention,
the root node, the full column product, the full template alphabet), **and so is
the schedule half**: `s = 4`, `theta = 1/20480` and `q = 2^24` are values the
frozen definitional chain cannot produce.

* `s = 4` fails `eq:s-choice` (`06:110--121`), which forces `s >= 512`, and
  fails `06:394--395`'s `64 | s`.  It meets only the Section-4 **floor** `s >= 4`
  (`04:389`, `04:460`, `04:481`, `04:504`, `04:619`), and a floor is not a
  defining display.
* `theta = 1/20480` would force `Q = 128` in `eq:Q-theta-choice`
  (`06:527--538`), but `06:547`'s `delta_U <= 1/200` and `05:39--40`'s
  `b_out >= 1` give `Q_0 >= 16000`, hence `Q >= 2^14` and `theta <= 1/2621440`
  (banked `WrapperProtectedEarly.scheduleTheta_route_le`).
* `q = 2^24` fails `eq:q-deltaU` (`06:513--519`): the reachable exponents are
  `A_wrap L_P^2` with `L_P >= 4` (`06:465--472`), and `24` is not one (banked
  `WrapperProtectedEarly.wrapper_exponent_ne_twentyfour`).

`kappa = 2` is the one admissible value here, at `09:1420`'s floor
`kappa = kappa_v >= 2`.  Round `r0` called all four legal; that claim is
**withdrawn in every half**, and **no parameter value may be read out of this
statement**.  It is not the paper's instance of `USetSelected`, it never
discharges the deferred canonical-inhabitation obligation, and it is not offered
against any vacuity charge -- `uSetSelection_at_scheduleTheta` above is the
schedule-tier inhabitant that carries that burden.

*What it does establish.*  That the fourteen-clause deliverable of Section 4 and
the full hypothesis bundle of `uSetSelection_of_dMass` are simultaneously
satisfiable in the kernel at one concrete audit point -- no clause contradicts
another.  It is retained because it is the concrete arithmetic against which the
composition was first exercised, and because its bounds
(`64 * 1100 * 26 * 4 * 2 = 14643200 <= 16777216`, with the donor densities at
their maximum `1`) are checked rather than asserted. -/
theorem uSetSelection_probe (F : FiniteSlots.Stage1SlotBinding) {q₂ : ℕ}
    {Yf : Type*} [Fintype Yf] [DecidableEq Yf] (hq₂ : 0 < q₂) (y₀ : Yf)
    (z₀ : SelCar F q₂ Yf) (z : Bool) :
    USetSelected
      (Protocol.leaf (X := {a // a ∈ (Finset.univ :
        Finset (Fin 1 × (Fin 16777216 × ProtColsFrozen F q₂ Yf)))}) (Y := Unit) z)
      (selReservoirF F q₂ Yf) ([] : List Bool)
      (Finset.univ : Finset (Fin 16777216 → Bool)) (Finset.univ : Finset Bool)
      (Finset.univ : Finset (Fin 16777216)) 4 2 (1 / 20480) := by
  classical
  obtain ⟨hM, hS0, hD0⟩ := section8_col_counts_pos F hq₂ y₀
  have hRes : (selReservoirF F q₂ Yf).Nonempty :=
    selReservoir_nonempty z₀ (Nat.mul_pos hM hD0)
  have hLq : Lq 16777216 ≤ 26 := Lq_probe_bound
  have hB : Btheta (1 / 20480) ≤ 1100 := Btheta_floorTier_le
  -- every donor density is `1` at full retention.
  have hdens : dMass
      (Protocol.leaf (X := {a // a ∈ (Finset.univ :
        Finset (Fin 1 × (Fin 16777216 × ProtColsFrozen F q₂ Yf)))}) (Y := Unit) z)
      (selReservoirF F q₂ Yf) (Finset.univ : Finset (Fin 16777216))
      ([] : List Bool) = (16777216 : ℝ) := by
    have hone : ∀ i ∈ (Finset.univ : Finset (Fin 16777216)),
        donorDensity
          (Protocol.leaf (X := {a // a ∈ (Finset.univ :
            Finset (Fin 1 × (Fin 16777216 × ProtColsFrozen F q₂ Yf)))})
            (Y := Unit) z) (selReservoirF F q₂ Yf) ([] : List Bool) i = 1 :=
      fun i _ => reservoirDensity_full_retention (selReservoirF F q₂ Yf) hRes i z
    rw [dMass, Finset.sum_congr rfl hone]
    simp
  refine uSetSelection_of_dMass (lamT := 1) (θ := 1 / 20480) _ _ _ _ _ _
    (by positivity) (by norm_num) (le_refl 2) (by norm_num) (by simp) ?_ ?_ ?_ ?_ ?_
  · -- `09:1439`'s threshold at the probe's constants.
    rw [hdens]
    exact probe_threshold_arith hB hLq (le_refl 4) (le_refl 2)
  · exact univ_column_density (by norm_num)
  · simp
  · have hρ := rhoOne_pos
    norm_num
    linarith
  · exact fun u Jq hJq => bobQuery_partition_is_satisfiable _ Jq hJq

/-- **FLOOR-TIER HYPOTHESIS-CONSISTENCY PROBE for
`uSetSelection_of_protectedMass` (BEYOND-PAPER on every half, the schedule half
included; FULL NON-FIDELITY).**

`uSetSelection_of_protectedMass` adds exactly one hypothesis to the bundle that
`uSetSelection_probe` already exhibits: the frozen threshold
`eq:protected-early-threshold` (`09:1421--1425`) itself, on the built `P_v`.  This
lemma shows that hypothesis is reachable *simultaneously with the two frozen mass
binders*, so no pair of the bundle is contradictory and the principal deliverable
is not vacuous.

The two mass binders are not assumed here: `P_v` is instantiated at the paper's
own reservoirs, where they are theorems, and the value is the banked
`ProtectedRowReservoirs.protectedMass_probe_full_retention` -- `P_v({j}) = 2 mu_P`,
the frozen `tau` of `08:133` at one donor -- so `mu_P` cancels out of the
comparison exactly as `09:1433--1439` says it does.  What remains is
`1024 B_theta L_q <= 2 q`, and at the probe's `theta` and width that is
`28600 <= 32768`.

**Why this is not a fidelity claim, and not a legality claim either.**  The
protocol is a leaf, the retained row set is everything and the node is the root,
so this is *our* point, not the paper's; and `s = 4`, `theta = 1/20480`,
`q = 2^24` are the same three unreachable numerals the floor-tier probe above
carries, refuted by `eq:s-choice` with `06:394--395`, by `eq:Q-theta-choice` with
`06:547` and `05:39--40`, and by `eq:q-deltaU` with `06:465--472` respectively.
Round `r0` offered this statement against the vacuity charge on
`uSetSelection_of_protectedMass`; that offer is **withdrawn**, and
`protectedMass_threshold_at_scheduleTheta` above -- the same comparison at
evaluated displays -- is what answers it.  What remains here is a true arithmetic
consistency check of our encoding at one audit point, from which **no parameter
value may be read**. -/
theorem protectedMass_threshold_is_satisfiable (F : FiniteSlots.Stage1SlotBinding)
    {q₂ : ℕ} {Yf : Type*} [Fintype Yf] [DecidableEq Yf] (hq₂ : 0 < q₂) (y₀ : Yf)
    (z : Bool) :
    128 * muP * ((Btheta (1 / 20480) : ℕ) : ℝ) * ((Lq 16777216 : ℕ) : ℝ)
        * (((4 : ℕ) : ℕ) : ℝ) * (((2 : ℕ) : ℕ) : ℝ)
      ≤ donorMass
          (systemPv
            (Protocol.leaf (X := {a // a ∈ (Finset.univ :
              Finset (Fin 1 × (Fin 16777216 × ProtColsFrozen F q₂ Yf)))})
              (Y := Unit) z)
            (fun _ : Unit => ([] : List Bool)) (id : Fin 16777216 → Fin 16777216)
            (selReservoirF F q₂ Yf) (diagReservoirF F q₂ Yf)
            (Fintype.card (ProtColsFrozen F q₂ Yf)))
          (Finset.univ : Finset (Fin 16777216)) () := by
  classical
  have hval : ∀ j ∈ (Finset.univ : Finset (Fin 16777216)),
      systemPv
          (Protocol.leaf (X := {a // a ∈ (Finset.univ :
            Finset (Fin 1 × (Fin 16777216 × ProtColsFrozen F q₂ Yf)))})
            (Y := Unit) z)
          (fun _ : Unit => ([] : List Bool)) (id : Fin 16777216 → Fin 16777216)
          (selReservoirF F q₂ Yf) (diagReservoirF F q₂ Yf)
          (Fintype.card (ProtColsFrozen F q₂ Yf)) () j = muP + muP :=
    fun j _ => protectedMass_probe_full_retention F hq₂ y₀ j z
  rw [donorMass, Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hB : ((Btheta (1 / 20480) : ℕ) : ℝ) ≤ 1100 := by exact_mod_cast Btheta_floorTier_le
  have hL : ((Lq 16777216 : ℕ) : ℝ) ≤ 26 := by exact_mod_cast Lq_probe_bound
  have hB0 : (0 : ℝ) ≤ ((Btheta (1 / 20480) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ ((Lq 16777216 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hBL : ((Btheta (1 / 20480) : ℕ) : ℝ) * ((Lq 16777216 : ℕ) : ℝ) ≤ 1100 * 26 :=
    mul_le_mul hB hL hL0 (by norm_num)
  have hμ : (0 : ℝ) < muP := muP_pos
  have hstep := mul_le_mul_of_nonneg_left hBL (le_of_lt hμ)
  push_cast
  nlinarith [hstep, hμ]

end Inhabitation

/-! ## Section 7  Statement poles

A green build sees neither of these.  Each records that a clause of the sections
above is load-bearing. -/

section Poles

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **Statement pole (the empty donor set cannot meet the frozen threshold).**

`09:1439`'s `D_mass >= 64 B_theta L_q s kappa` is not a formality: at an empty
donor set `D_mass` is exactly `0`, so any strictly positive threshold fails.  The
hypothesis of `exists_reservoir_dyadic_class` therefore genuinely constrains the
donor set, and the lemma is not provable by producing a class inside nothing.
General in the bound; nothing is asserted about the frozen constants here. -/
theorem empty_donor_set_fails_the_threshold (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (p : List Bool) {c : ℝ} (hc : 0 < c) :
    ¬ (c ≤ dMass P Res (∅ : Finset (Fin q)) p) := by
  rw [dMass_empty]
  exact not_le.mpr hc

/-- **Statement pole (the empty class fails `eq:protected-dyadic-class`).**

The clause `u B_theta <= |V|` of `09:1454` is what stops
`exists_reservoir_dyadic_class` and `USetSelected` from being satisfied by the
empty class: at every legal `theta` the banked `one_le_Btheta` gives
`B_theta >= 1`, so `u B_theta >= 2^e >= 1 > 0 = |empty|`.  Without that clause the
`u`-set of `09:1462` could not be extracted at all, and the whole cover argument
would be inert.  General. -/
theorem empty_class_fails_the_width_bound {e : ℕ} {θ : ℝ} (hθ : 0 < θ) :
    ¬ (2 ^ e * Btheta θ ≤ ((∅ : Finset (Fin q)).card)) := by
  have hp : 0 < 2 ^ e := pow_pos (by norm_num) e
  have hpos : 0 < 2 ^ e * Btheta θ := Nat.mul_pos hp (one_le_Btheta hθ)
  rw [Finset.card_empty, Nat.le_zero]
  exact hpos.ne'

/-- **Statement pole (the schedule-tier conjuncts are not free, and the
floor-tier point cannot satisfy them).**

`uSetSelection_at_scheduleTheta` returns `512 <= s`, `64 | s` and the width shape
`q = 2^{A_wrap L_P^2}` as *conjuncts* rather than assuming them, so the trivial
route -- reusing the round-`r0` floor-tier point `s = 4`, `q = 2^24` and reading
it as a schedule point -- is refuted inside the kernel:

* `64 | 4` is false and `512 <= 4` is false, so `eq:s-choice`'s two consequences
  (`06:110--121` with `06:394--395`) reject `s = 4` outright;
* `2^{A_wrap L_P^2} = 2^24` is impossible whenever `L_P >= 4`, which
  `06:465--472` (`P_0 >= 16`) forces, by the banked
  `WrapperProtectedEarly.wrapper_exponent_ne_twentyfour` and injectivity of
  `n |-> 2^n`.

Without these conjuncts the schedule-tier statement would be no stronger than
the floor-tier probe; with them it cannot be read at the floor-tier point.
General in `A_wrap` and `L_P`. -/
theorem floorTier_point_fails_the_schedule_tier {Awrap LP : ℕ} (hLP : 4 ≤ LP) :
    ¬ ((64 : ℕ) ∣ 4) ∧ ¬ (512 ≤ (4 : ℕ)) ∧
      (2 : ℕ) ^ (Awrap * LP ^ 2) ≠ 2 ^ 24 := by
  refine ⟨by decide, by decide, ?_⟩
  intro hcon
  exact wrapper_exponent_ne_twentyfour (Awrap := Awrap) hLP
    (Nat.pow_right_injective (le_refl 2) hcon)

end Poles

end EthInapproximability.ParameterizedNP.UsetSelection
