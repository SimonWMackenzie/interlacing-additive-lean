import EthInapproximability.ParameterizedNP.UsetSelection

/-!
# Parameterized NP route: the early-closure block selection of `09:1473--1509`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche).
* **The exact frozen lines traced here**, in print order.  The block is the
  *tail* of the frozen proof of `lem:early-protected-closure` (`09:1432--1510`),
  whose head `09:1433--1471` is the banked `UsetSelection` deliverable
  `USetSelected`:
  * **`09:1469--1471`**, the last sentence of the head, which
    `USET-SELECTION-001` left as its **GAP-EXPOSED item 1**: "Averaging over the
    equal template bins, fix one Stage-3 bin in each donor without reducing this
    relative density."  Section 1 lands it **by derivation**, not as a
    hypothesis.
  * **`09:367--371`**, the Stage-3 template bins the previous sentence averages
    over: `Y_T = bigsqcup_{p in [s]} Y_{T,p}`, `|Y_{T,p}| = m_T`,
    `lambda_T = |Y_T|/|Y|` -- an equipartition of the template alphabet into `s`
    equal bins, `s` being the same Stage-3 multiplicity that indexes the width
    window.  This is why the bin index type below is `Fin s` and the bin map is a
    function of the *letter* alone: the frozen display partitions `Y_T`, not
    `Y_T^{u/2}`.
  * **`09:1473--1476`**: "Every selected donor has protected-reservoir density
    greater than `d_cls/2`.  In a protected reservoir, all rows carrying a fixed
    Stage-2 coordinate have the same Stage-4 entry map."  The first sentence is a
    clause of the banked `USetSelected` (`09:1443--1444` at the selected class);
    the second is the Stage-4 reservoir geometry, which is **not built** and
    which Section 2 therefore carries as the explicit named hypothesis `havg`,
    never silently.
  * **`09:1476--1479`**: "Averaging these `q_2` coordinate fibres therefore
    supplies more than `d_cls q_2/4` Stage-2 coordinates whose surviving
    `C_1`-density is at least `d_cls/4` in each donor."  Section 2 lands this
    averaging **by derivation** from the banked
    `WrapperProtectedEarly.card_ge_of_sum_ge`.
  * **`09:1480--1483`**, the represented-block total
    `K_int = s kappa q_2` across the selected donors -- the banked
    `WrapperProtectedEarly.{Kint, representedBlocks_ge}`, fired here at the
    width the selection produces.
  * **`09:1484--1490`**, `eq:protected-delta-min` (label `09:1489`),
    `d_cls >= 64 B_theta L_q s/q =: delta_min`, which is what transports the
    schedule-owned row gate of `06:1151--1152` up to the class the argument
    happens to select.
  * **`09:1491--1497`**: "The ambient product width is `(u/2)q_2`.  Since
    `d_cls <= 1` and `eq:protected-dyadic-class` gives `u d_cls >= 8 s kappa`,
    this width is at least `4 K_int`.  Thus `r' = K_int/t_2` lies in the literal
    range of Localized Extension."  Banked `ambient_width_ge`, fired at the
    produced width.
  * **`09:1499--1503`**: "Select exactly `9 K_int/16` of these represented
    Stage-2 blocks.  This is call~(iii) in `sec:extension-call-ledger`.  The row
    there records the ambient product width, the per-block row threshold, the
    entering column density, and all integer binders.  The uniform gates verify
    its balancedness, both column-loss clauses, and hard-seed comparison."  This
    is the banked record `WrapperProtectedEarly.ExtensionCallThree`, **constructed
    here** from the produced width by `extensionCallThree_of_width`.
  * **`09:1504--1509`**: "Localized Extension gives the selected Bob child
    complexity `B_cap + log_2 K_int = C + log_2 kappa - 1`.  This proves the
    lemma."  Banked `endpoint_identity`; Section 5 reads it off the produced
    record, and Section 6 lands the frozen conclusion itself at the built `P_v`.
  * **`09:1418--1430`**, the statement of `lem:early-protected-closure` with
    `eq:protected-early-threshold` (label `09:1424`),
    `P_v(J_0) >= 128 mu_P B_theta L_q s kappa`, and the conclusion clause "then
    one child of `v` has communication complexity at least" with its display
    `C + log_2 kappa - 1`.  **This is the first tranche in which that conclusion
    may enter**, and Section 6 is the only place it does.
  * **`09:1375`** and **`09:105--109`**, the donor convention `J_0 subseteq [q]`
    at the scale-alignment width `q = 2^r`; every donor set below is a
    `Finset (Fin q)` at that width and never at `q_2` or `Q`.
  * **`09:1378--1384`**, the four block constants `rho_0`, `rho_1`, `B_theta`,
    `L_q`, consumed by pin as `WrapperProtectedEarly.{rhoZero, rhoOne, Btheta,
    Lq}` and never re-defined.
* **Cross-anchors opened first-hand in the frozen files for this tranche:**
  * `06-parameter-schedule.tex` (SHA-256
    `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
    recomputed first-hand this round):
    * **`06:1147--1153`**, row (iii) of `sec:extension-call-ledger`: `v = u/2`,
      `K = K_int`, `h = rho_1 2^{-u-1}` (`06:1150`, the banked
      `WrapperProtectedEarly.callThreeH`), `a^sharp = 0`, and the per-block row
      density `d_cls/4` at `06:1151` with its structural-gate comparison
      `d_cls/4 >= K 2^{-b_1}` at `06:1152`.
    * `06:1107--1113` (`eq:extension-common-binders`) and `06:1122--1125`
      (`r = q_amb/t_2`, `r' = K/t_2`), the binders the record carries.
    * `06:763--770` (`eq:t2-search`), the defining display of `k_2`; it is
      **not evaluated** anywhere below, and `4 <= k_2` (a consequence, `16 | t_2`)
      enters only as an explicit binder.
    * `06:527--539` (`eq:Q-theta-choice`) with `06:547` and `05:39--40`, and
      `06:110--121` with `06:394--395` (`eq:s-choice`), and `06:513--522`
      (`eq:q-deltaU`) -- the three defining displays the Section-7 schedule-tier
      inhabitant *evaluates* through the banked
      `WrapperProtectedEarly.{reachableWidth_at_scheduleTheta,
      earlyProtectedClosure_block_bundle_at_scheduleTheta}`.  No numeral is
      assigned to any of `theta`, `s`, `q`.
  * `D-inherited-contracts.tex`: `D:717--744` (the checked inherited Localized
    Extension declaration) and `D:746--764` (`eq:contract-extension-exponents`,
    the `T, R, R_loc` exhibition obligation) -- the contract the banked
    `ExtensionCallThree` records and that `extensionCallThree_of_width`
    *constructs* rather than assumes.
  * `02-mechanical-contract.tex`, `02:74--126`, the ten mechanical rules
    **M1--M10**; the re-run is recorded below.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in **no** hypothesis of this module: the balanced family
  reaches `lem:early-protected-closure` only through the banked `hLocEx` binder
  of `WrapperProtectedEarly.earlyProtectedClosure`, which Section 6 forwards
  verbatim as an explicit named hypothesis and never as a silent axiom.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, directly or transitively: the single import is
  `UsetSelection`, whose closure was enumerated mechanically last tranche and
  contains neither `LegacyNPCC.Stage12` nor `NPCC.Stage2`.  **No opt-in ledger
  note is owed.**
* **Proof status:** new.  Two things are genuinely new mathematics-free
  *derivations* -- the Stage-3 bin averaging of `09:1469--1471` (Section 1) and
  the `q_2`-fibre averaging of `09:1476--1479` (Section 2) -- and everything else
  is the *wiring* of banked arithmetic to the banked `USetSelected` deliverable.
  No new `axiom`, no unproved placeholder, no opaque certificate.

## What this tranche lands, against the predecessor's own gap list

`USET-SELECTION-001` records four forward gaps.  This tranche discharges items 1,
2 and 3 and leaves item 4 untouched.

1. **GAP item 1 -- `09:1469--1471`'s Stage-3 bin averaging -- DISCHARGED BY
   DERIVATION.**  Section 1 partitions the template alphabet exactly as
   `09:367--369` does, and `exists_stageThreeBin` is the pigeonhole over the
   `s^{u/2}` bin choices: some choice retains a `s^{-u/2}` share of the projected
   all-template set, which is precisely "without reducing this relative density"
   once both sides are read against their own boxes (`stageThreeBin_density`).
   `stageThreeBin_of_uSetSelected` fires it on the banked deliverable, so the
   frozen entering density `h = rho_1 2^{-u-1}` of `06:1150` survives the bin
   fixing.  The predecessor's prescription named
   `WrapperProjectionCovers.singleton_bin_retention`; that lemma is the
   *one-coordinate* retention step of `09:414--417` (the anchor it cites itself;
   `09:344--352` is `lem:product-projection-cover`'s poor-`k`-set cover bound,
   which is a different statement) and does not perform this
   average, so the derivation is done from the frozen display itself.  **Nothing
   is assumed here**: the equipartition is the frozen `09:367--369`, and the
   averaging is proved.
2. **GAP item 2 -- `09:1473--1483` -- ENTERED, with the unbuilt half named.**
   `09:1473`'s "every selected donor has protected-reservoir density greater than
   `d_cls/2`" is a clause of the banked `USetSelected` and is *read off* it
   (`selectedDonor_density_gt`).  `09:1474--1476`'s "in a protected reservoir,
   all rows carrying a fixed Stage-2 coordinate have the same Stage-4 entry map"
   is the Stage-4 reservoir geometry, which this repository has **not built**; it
   is carried as the explicit named hypothesis `havg` of `fibreBlocks_ge`, whose
   content is exactly that the `q_2` coordinate fibres *average* the donor
   density.  The averaging step `09:1476--1479` is then **proved**, and
   `09:1480--1483`'s `K_int` total is the banked `representedBlocks_ge` fired at
   the produced width.
3. **GAP item 3 -- `09:1491--1509` -- ENTERED IN FULL.**  `BlockSelected` names
   the frozen deliverable of the tail; `blockSelection_of_uSetSelected` produces
   it from the banked `USetSelected`; `blockSelection_of_protectedMass` runs the
   whole chain from `eq:protected-early-threshold` at the **built** `P_v` of
   `PROTECTED-ROW-RESERVOIRS-001`, consuming `uSetSelection_of_protectedMass` in
   its proof term; and Section 5 reads the ambient width, the exact `9K_int/16`
   output size and the endpoint identity off the produced record.
4. **GAP item 4 -- `09:1512--1531`, `sec:wrapper-mass-redistribution` -- NOT
   ENTERED**, exactly as the predecessor leaves it.  `P_B`, `J_clean`, `J_good`,
   `eta_R`, Bob-heaviness and `eq:wrapper-total-early-mass` occur in **no**
   declaration below.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:1188`,
`09:1780--1781`) is neither stated nor implied; the ranges `09:1184--1366` and
`09:1512--1781` stay GAP-EXPOSED; `thm:certified-localized-extension` remains
unproved and unconsumed; and the conclusion of `lem:early-protected-closure` that
Section 6 lands is *conditional on the same named binders* the banked
`WrapperProtectedEarly.earlyProtectedClosure` already carries -- this tranche
discharges none of them.

## M1--M10 re-run, from scratch (`02:74--126`)

This is the first tranche in which `lem:early-protected-closure`'s **conclusion**
may enter a statement, so the ten mechanical rules are re-checked from scratch
against every declaration below rather than inherited.

* **M1 (public data are immutable).**  Nothing below mutates a public datum.
  `s = 2^{r_3}`, `q_2 = 2^{r_2}`, `t_2 = 2^{k_2}`, `q`, `b_1`, `B_cap` and
  `theta` are binders fixed before any selection is made, and no declaration
  chooses one of them after inspecting a density.  The two derivations of
  Sections 1--2 quantify over the schedule symbols and never instantiate them.
* **M2 (the constructor does not contain a promise certificate).**  `BlockSelected`
  is the only new `Prop`-valued definition, and its three clauses are the
  reachable-width window, the call-(iii) record, and the block count -- all
  computed from the schedule exponents and the produced width.  **It does not
  contain the closure's conclusion.**  `memCost`, `child`, `B_cap + log_2 K_int`
  and `C + log_2 kappa - 1` occur in *no* clause of `BlockSelected` and in no
  argument of it; the conclusion appears only in Section 6, as the *conclusion of
  a theorem* whose Localized-Extension hypothesis is an explicit named binder.
  `stageThreeBinVector` is a bin index and carries no certificate.
* **M3 (constructed and derived objects are distinct).**  The constructed objects
  are the bin partition (`09:367--369`) and the call record; the derived ones are
  the retained bin density, the per-donor block count, `K_int`, the ambient
  width, the `9K_int/16` output size and the endpoint.  Every derived quantity is
  *recomputed* from the constructed object by a named lemma
  (`stageThreeBin_density`, `fibreBlocks_ge`, `blockSelected_forces_blocks`,
  `blockSelected_selected_count`, `blockSelected_ambient_width`,
  `blockSelected_endpoint`), never stipulated as a field.
* **M4 (every construction has a frame condition).**  `stageThreeBinVector` states
  its input (a letter-level bin map and a tuple), its output carrier
  (`iota -> Fin s`), its entry rule (`binOf (f i)`), and leaves the tuple
  untouched; `stageThreeBin_fiber_mem` is the map witnessing the restriction.
  `BlockSelected` states its inputs (the six schedule exponents, the width, the
  threshold) and its output carrier explicitly.
* **M5 (every finite choice is deterministic).**  The one existential choice made
  here -- the Stage-3 bin vector `p` of `09:1471` -- is a *proof-only* witness
  produced by pigeonhole, and it is **not reused as construction data**: no
  definition below takes it as an argument, and `BlockSelected` does not mention
  it.  The width `u = 2^e` is the frozen least power of two of `09:1449--1450`,
  produced by the banked `exists_width_u` inside `USetSelected`, not chosen here.
* **M6 (ceilings are part of the statement).**  Every density comparison below is
  written multiplicatively against an integer cardinality, in the frozen
  direction: `h * m_T^{u/2} <= |A ∩ box|` (Section 1),
  `d_cls q_2/4 <= |{fibres}|` (Section 2), `K_int <= selCard` (Section 3).  No
  division by a cardinality is taken, so no ceiling is silently dropped; the one
  frozen ceiling of row (iii), `ceil(r' t x m)`, belongs to the inherited
  contract and is forwarded verbatim in Section 6's `hrows`.
* **M7 (carrier equations accompany entry equations).**  `templateCard_eq_bins`
  is the carrier equation of `09:367--369` (`|Y_T| = s m_T`), proved rather than
  assumed, and it is what makes the two boxes of `09:1471` comparable.
  `Kint_dyadic` is the carrier count of `09:1481`.  A width and its logarithm are
  never interchanged: `u`, `q_2`, `t_2`, `K_int` are carried as `2^e`, `2^{r_2}`,
  `2^{k_2}`, `2^{r_3+ell+r_2}` and their exponents as separate naturals.
* **M8 (protocol cost is exact at every selector).**  No selector is introduced
  here.  The one cost statement, Section 6's conclusion, is the banked
  `TerminalTwoStream.terminalTarget` written **subtraction-free** so that the
  frozen `-1` of `09:1428` never becomes a truncated natural subtraction, and it
  adds no conclusion bit by convention: `blockSelected_endpoint` proves the
  identity `B_cap + log_2 K_int + 1 = C + log_2 kappa` at the produced record's
  own exponents, and `log_2 K_int = R_loc + k_2` is the record's
  `capacity_exponent` field, i.e. a proved power-of-two reading and not a
  convention.
* **M9 (unreachable cases remain explicit).**  The degenerate branches are named
  and proved impossible rather than omitted: `blockSelected_forces_blocks` rules
  out `selCard = 0`, `uSetSelected_halfWidth_pos` rules out the empty or
  singleton donor half-width (`u/2 >= 8`), and `blockSelected_width_window` keeps
  `4 <= e`, which is what supplies `09:1390--1391`'s `4 | u`.  The bin index type
  `Fin s` is nonempty exactly under the frozen `s >= 4` (`04:389`), carried as
  `0 < s`.
* **M10 (asymptotics do not discharge finite obligations).**  No `O`, `o`, or
  "eventually" occurs; every bound below is a finite expression in the schedule
  exponents with explicit integer coefficients (`8`, `16`, `4`, `9/16`, `64`,
  `128`).

## Fidelity labels, full coverage (every declaration is labelled)

* **FIDELITY (frozen derivation).**  `templateCard_eq_bins`, `exists_stageThreeBin`,
  `stageThreeBin_fiber_mem`, `stageThreeBin_density`, `stageThreeBin_of_uSetSelected`,
  `selectedDonor_density_gt`, `fibreBlocks_ge`, `blockCount_of_perDonor`,
  `uSetSelected_ambient_room`, `uSetSelected_halfWidth_pos`, `BlockSelected`,
  `blockSelection_of_uSetSelected`, `blockSelection_of_protectedMass`,
  `blockSelected_forces_blocks`, `blockSelected_selected_count`,
  `blockSelected_ambient_width`, `blockSelected_width_window`,
  `blockSelected_capacity_exponent`, `blockSelected_endpoint`,
  `earlyProtectedClosure_at_builtPv` -- each traces the frozen anchor named in
  its docstring and asserts nothing beyond it.
* **SCAFFOLDING (general lemma the paper never instantiates as an object).**
  `stageThreeBinVector` is a naming device for the frozen bin index; the paper
  writes the bins, not the index map, and its docstring says so.
* **SCHEDULE-TIER NON-VACUITY (parameter half evaluated, other halves ours).**
  `blockSelected_at_scheduleTheta` -- see Section 7.
* **STATEMENT POLES (a green build sees none of these).**
  `blockSelected_forces_blocks`, `stageThreeBin_is_not_free`,
  `fibreBlocks_needs_the_average`, `blockSelected_is_not_the_one_copy_count`.
* **CANONICAL INHABITATION: REGISTERED AND DEFERRED.**  The paper's own instance
  of `BlockSelected` is the block selection carried out inside
  `lem:early-protected-closure` at the retained matrix `U'` and the alleged
  protocol of `09:1188--1193`, at the schedule's *materialized* parameters
  (`06:859--887`, MATERIALIZE-001 on the Lean side).  None of that is built, so
  the obligation is registered here and discharged when the materialization
  lands.  The Section-7 inhabitant is **NON-FIDELITY on the protocol, column,
  template and block-supply halves** and repairs the *parameter* half only; it is
  never offered against that obligation.

## Aux-lemma battery

Every entry is **proved**; nothing is stated and left open.

* `A` the Stage-3 bins, general (5): `templateCard_eq_bins`,
  `exists_stageThreeBin`, `stageThreeBin_fiber_mem`, `stageThreeBin_density`,
  `stageThreeBin_of_uSetSelected`.
* `B` the fibre average, general (3): `selectedDonor_density_gt`,
  `fibreBlocks_ge`, `blockCount_of_perDonor`.
* `C` the two continuation readouts, consumed (2): `uSetSelected_ambient_room`,
  `uSetSelected_halfWidth_pos`.
* `D` the deliverable and its producers (3): `blockSelection_of_uSetSelected`,
  `blockSelection_of_protectedMass`, `earlyProtectedClosure_at_builtPv`.
* `E` the readouts of the deliverable, general (6):
  `blockSelected_forces_blocks`, `blockSelected_selected_count`,
  `blockSelected_ambient_width`, `blockSelected_width_window`,
  `blockSelected_capacity_exponent`, `blockSelected_endpoint`.
* `F` non-vacuity and poles (4): `blockSelected_at_scheduleTheta`,
  `stageThreeBin_is_not_free`, `fibreBlocks_needs_the_average`,
  `blockSelected_is_not_the_one_copy_count`.

That is **23 theorems proved, 0 unproved**, over 25 source declarations
(23 `theorem`, 2 `def`, and `0` each of `abbrev`, `structure`, `class`,
`instance` and `axiom`).

## Predecessor modules consumed **by pin**, never restated

* `UsetSelection`: `USetSelected`, `uSetSelection_of_protectedMass`,
  `uSetSelected_gives_sixteen_donors`, `uSetSelected_width_window`,
  `donorDensity`, `donorDensity_nonneg`, `donorDensity_le_one`.
* `WrapperProtectedEarly`: `classWidth`, `classWidth_pos`, `classWidth_le_one`,
  `callThreeH`, `Kint`, `Kint_dyadic`, `representedBlocks_ge`,
  `ambient_width_ge`, `ExtensionCallThree`, `extensionCallThree_of_width`,
  `endpoint_identity`, `ReachableWidth`, `card_ge_of_sum_ge`, `Btheta`, `Lq`,
  `muP`, `rhoOne`, `earlyProtectedClosure`,
  `earlyProtectedClosure_block_bundle_at_scheduleTheta`.
* `ProtectedRowReservoirs`: `donorMass_systemPv`, `systemPv`.
* `WrapperProjectionCovers`: `projSet`.

Two banked names are *provenance*, not consumption, and are listed separately so
the pin list stays literally true: `WrapperProtectedEarly.reachableWidth_at_scheduleTheta`
occurs in no proof term here -- its `(e, d_cls) = (r_3 + ell + 4, 1/2)` pair is
re-derived by hand inside `blockSelected_at_scheduleTheta`, because that lemma and
`earlyProtectedClosure_block_bundle_at_scheduleTheta` bind *different* `A_wrap`
existentials and cannot be composed as they stand -- and
`WrapperProjectionCovers.PoorProjection` reaches this module only inside the banked
`USetSelected` definition, never through a local proof term.
* `MassRedistributionCounting`: `donorMass`.
* `TerminalTwoStream.terminalTarget`, `DenseBranchSelection.Dtwo`,
  `HardSeedFacade.hardSeedColumnDensity`, and the vendored, project-axiom-free
  `NPCC.LambdaGE` through `LegacyNPCC.Core`.

## HYPOTHESIS-CONSISTENCY note

The two new premise bundles are `fibreBlocks_ge`'s (three explicit binders, no
bundle field) and `blockSelection_of_uSetSelected`'s.  Neither conjoins two
frozen items the paper states as separate cases: the `v = 1` row of the call
table is never assumed together with row (iii), and the two protected reservoir
types of `09:1433` are kept in the frozen *disjunction* rather than conjoined.
What is discharged constructively at the schedule tier is the *conclusion*
`BlockSelected`, by `blockSelected_at_scheduleTheta`, whose parameter half is
*evaluated* through `eq:Q-theta-choice`, `eq:s-choice` and `eq:q-deltaU`.  That
lemma does **not** discharge `blockSelection_of_uSetSelected`'s premise bundle:
it never mentions `USetSelected` and never invokes `blockSelection_of_uSetSelected`,
building `BlockSelected` directly from the banked
`earlyProtectedClosure_block_bundle_at_scheduleTheta` and `extensionCallThree_of_width`
instead.  The producer's bundle is composed of banked binders that each carry
banked schedule-tier evidence, but at *different* `A_wrap` existentials, so it is
not cheaply composable -- which is why the direct route is taken here, and a
schedule-tier inhabitant of that bundle remains a registered forward obligation.
Section 6 introduces **no** premise bundle of its own: every hypothesis is either
a binder of the banked `WrapperProtectedEarly.earlyProtectedClosure` forwarded
verbatim, or one of the four reservoir-mass binders of the banked
`ProtectedRowReservoirs.donorMass_systemPv`, which are *theorems* at the paper's
own carriers (`selReservoirF_card_eq_muP_mul`, `diagReservoirF_card_eq_muP_mul`).
-/

namespace EthInapproximability.ParameterizedNP.EarlyClosureBlockSelection

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.ProtectedRowReservoirs
open EthInapproximability.ParameterizedNP.UsetSelection

/-! ## Section 1  The Stage-3 bin averaging (`09:1469--1471`, `09:367--371`)

"Averaging over the equal template bins, fix one Stage-3 bin in each donor
without reducing this relative density."

The bins are `09:367--369`'s equipartition
`Y_T = bigsqcup_{p in [s]} Y_{T,p}` with `|Y_{T,p}| = m_T`: a partition of the
*alphabet*, one and the same for every coordinate.  So a "Stage-3 bin in each
donor" is a vector `p : iota -> [s]` over the selected donors, and the averaging
is the pigeonhole over the `s^{|iota|}` such vectors.  Nothing here is assumed:
the equipartition is the frozen display and the average is proved. -/

section StageThreeBins

variable {ι Y : Type*} [Fintype ι] {s : ℕ}

/-- **SCAFFOLDING.  The Stage-3 bin index of a tuple (`09:367--369`).**

`09:367--369` partitions the template alphabet `Y_T` into the `s` equal bins
`Y_{T,p}`; a letter's bin is therefore a function of the letter alone, and a
tuple's bin vector is that function applied coordinatewise.  The paper writes the
bins, never this index map, so this definition is scaffolding: it exists only so
that "fix one Stage-3 bin in each donor" is a single equation rather than `|iota|`
separate ones. -/
def stageThreeBinVector (binOf : Y → Fin s) (f : ι → Y) : ι → Fin s :=
  fun i => binOf (f i)

/-- **Aux A1 (`09:367--369`, the carrier equation `|Y_T| = s m_T`).**

If every one of the `s` Stage-3 bins of the template set has exactly `m_T`
letters -- the frozen `|Y_{T,p}| = m_T` -- then the template set has `s m_T`
letters.  This is M7's carrier equation for the partition, proved rather than
assumed, and it is what makes the two boxes of `09:1471` (`Y_T^{u/2}` before the
fixing, `Y_{T,p}^{u/2}` after) comparable.  General in the alphabet, the bin map
and `m_T`. -/
theorem templateCard_eq_bins {mT : ℕ} (binOf : Y → Fin s)
    (YT : Finset Y) (hbin : ∀ p : Fin s, (YT.filter (fun y => binOf y = p)).card = mT) :
    YT.card = s * mT := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := binOf) (s := YT) (t := (Finset.univ : Finset (Fin s)))
    (fun x _ => Finset.mem_univ _)
  rw [h, Finset.sum_congr rfl (fun p _ => hbin p), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **`09:1471`, the averaging over the equal template bins, PROVED.**

"Averaging over the equal template bins, fix one Stage-3 bin in each donor."
Formally: among the `s^{|iota|}` bin vectors, one has a fibre carrying at least a
`s^{-|iota|}` share of `A`.  This is the pigeonhole the frozen sentence performs,
and it is exact -- the fibres partition `A`.

*Why the trivial witness fails.*  The conclusion is an inequality about a
*specific* fibre of `A`, so it is not satisfiable by an unrelated set: at
`A = univ` and `s >= 2` every fibre is a proper subset, and the constant
`s^{|iota|}` is the smallest one that works (`stageThreeBin_is_not_free`).

General in the donor index type, the alphabet, the bin count and `A`. -/
theorem exists_stageThreeBin (hs : 0 < s) (binOf : Y → Fin s)
    (A : Finset (ι → Y)) :
    ∃ p : ι → Fin s,
      (A.card : ℝ) ≤ ((s : ℝ) ^ Fintype.card ι)
        * ((A.filter (fun f => stageThreeBinVector binOf f = p)).card : ℝ) := by
  classical
  have hne : (Finset.univ : Finset (ι → Fin s)).Nonempty := by
    have : Nonempty (ι → Fin s) := ⟨fun _ => ⟨0, hs⟩⟩
    exact Finset.univ_nonempty
  have hcard : ((Finset.univ : Finset (ι → Fin s)).card : ℝ)
      = (s : ℝ) ^ Fintype.card ι := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hspos : (0 : ℝ) < (s : ℝ) ^ Fintype.card ι := by
    have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    positivity
  have hsum : (A.card : ℝ)
      = ∑ p ∈ (Finset.univ : Finset (ι → Fin s)),
          ((A.filter (fun f => stageThreeBinVector binOf f = p)).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun f : ι → Y => stageThreeBinVector binOf f) (s := A)
      (t := (Finset.univ : Finset (ι → Fin s))) (fun x _ => Finset.mem_univ _)
    exact_mod_cast h
  by_contra hcon
  push Not at hcon
  have hlt : ∀ p ∈ (Finset.univ : Finset (ι → Fin s)),
      ((A.filter (fun f => stageThreeBinVector binOf f = p)).card : ℝ)
        < (A.card : ℝ) / ((s : ℝ) ^ Fintype.card ι) := by
    intro p _
    rw [lt_div_iff₀ hspos]
    have h := hcon p
    linarith [h, mul_comm ((s : ℝ) ^ Fintype.card ι)
      (((A.filter (fun f => stageThreeBinVector binOf f = p)).card : ℝ))]
  have hstrict := Finset.sum_lt_sum_of_nonempty hne hlt
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hstrict
  have hcancel : (s : ℝ) ^ Fintype.card ι * ((A.card : ℝ) / ((s : ℝ) ^ Fintype.card ι))
      = (A.card : ℝ) := by
    field_simp
  rw [hcancel] at hstrict
  linarith [hsum, hstrict]

/-- **Aux A2 (`09:1471`, the fixed bin really is fixed).**

Every tuple of the selected fibre lies in the *named* Stage-3 bin at every donor.
This is the frame condition (M4) of the restriction: the fibre is not merely
large, it is the set of tuples whose donor `i` sits in bin `p i`.  General. -/
theorem stageThreeBin_fiber_mem {binOf : Y → Fin s}
    {A : Finset (ι → Y)} {p : ι → Fin s} {f : ι → Y}
    (hf : f ∈ A.filter (fun g => stageThreeBinVector binOf g = p)) (i : ι) :
    binOf (f i) = p i := by
  classical
  have h := (Finset.mem_filter.mp hf).2
  exact congrFun h i

/-- **`09:1469--1471` AS A DENSITY STATEMENT: "without reducing this relative
density".**

The frozen sentence compares two relative densities: before the fixing, `A` sits
inside `Y_T^{u/2}` and has density at least `h`; after it, the retained tuples sit
inside the product of the chosen bins, of size `m_T^{u/2}`, and the claim is that
the density there is still at least `h`.  Written multiplicatively (M6), that is
exactly the implication below at `|Y_T| = s m_T` (`templateCard_eq_bins`).

General in the donor index type, the alphabet, the bin count, `m_T` and `h`. -/
theorem stageThreeBin_density {mT : ℕ} {h : ℝ} (hs : 0 < s)
    (binOf : Y → Fin s) (A : Finset (ι → Y))
    (hA : h * (((s * mT : ℕ)) : ℝ) ^ Fintype.card ι ≤ (A.card : ℝ)) :
    ∃ p : ι → Fin s,
      h * ((mT : ℕ) : ℝ) ^ Fintype.card ι
        ≤ ((A.filter (fun f => stageThreeBinVector binOf f = p)).card : ℝ) := by
  classical
  obtain ⟨p, hp⟩ := exists_stageThreeBin hs binOf A
  refine ⟨p, ?_⟩
  have hspos : (0 : ℝ) < (s : ℝ) ^ Fintype.card ι := by
    have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    positivity
  have hsplit : (((s * mT : ℕ)) : ℝ) ^ Fintype.card ι
      = (s : ℝ) ^ Fintype.card ι * ((mT : ℕ) : ℝ) ^ Fintype.card ι := by
    push_cast
    rw [mul_pow]
  rw [hsplit] at hA
  have hchain : (s : ℝ) ^ Fintype.card ι * (h * ((mT : ℕ) : ℝ) ^ Fintype.card ι)
      ≤ (s : ℝ) ^ Fintype.card ι
        * ((A.filter (fun f => stageThreeBinVector binOf f = p)).card : ℝ) := by
    nlinarith [hA, hp]
  exact le_of_mul_le_mul_left hchain hspos

end StageThreeBins

section StageThreeBinsAtSelection

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1469--1471` FIRED ON THE BANKED `u`-SET SELECTION.**

`USET-SELECTION-001`'s GAP item 1, discharged.  The banked deliverable ends at
the template-coordinate extraction: `u/2` donors whose projected all-template set
has density at least `h = rho_1 2^{-u-1}` (`06:1150`) inside `Y_T^{u/2}`.  This
lemma performs the frozen next sentence on that very set, at the frozen bins of
`09:367--369`: some Stage-3 bin vector over the selected donors retains density
at least `h` inside the product of the chosen bins.

The Stage-3 multiplicity indexing the bins is the frozen `s = 2^{r_3}` -- the
same `s` that indexes the width window `8 s kappa <= u d_cls` -- because
`09:367--368` partitions `Y_T` into exactly `s` bins.

*What is assumed.*  Only `09:367--369` itself: that the `s` bins of the template
set are equal, of size `m_T` (`hbin`), and that `s` is nonempty (`0 < s`, the
frozen `s >= 4` of `04:389`).  Nothing about the protocol, the reservoirs or the
Stage-4 entry maps enters.

General in the row carrier, the alphabet, the width, the alleged protocol, the
reservoir and the route. -/
theorem stageThreeBin_of_uSetSelected {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)} {s κ mT : ℕ}
    {θ : ℝ} (hs : 0 < s) (binOf : Y → Fin s)
    (hbin : ∀ b : Fin s, (YT.filter (fun y => binOf y = b)).card = mT)
    (hSel : USetSelected P Res p S YT J s κ θ) :
    ∃ (e : ℕ) (Jsel : Finset (Fin q)) (eJ : Fin (2 ^ e) ≃ ↥Jsel)
      (Pc : Finset (Fin (2 ^ e) → Y)) (J' : Finset (Fin (2 ^ e)))
      (bins : ↥J' → Fin s),
      Pc ⊆ ambientRelabel Jsel eJ S ∧ J'.card = 2 ^ e / 2 ∧
        callThreeH e * ((mT : ℕ) : ℝ) ^ (2 ^ e / 2)
          ≤ ((((projSet J' (Pc.filter (fun f => ∀ i ∈ J', f i ∈ YT))).filter
              (fun g => stageThreeBinVector binOf g = bins))).card : ℝ) := by
  classical
  obtain ⟨_k, e, _V, Jsel, eJ, Pc, J', _hVJ, _he4, _hspec, _hlow, _hhigh, _hdelta,
    _hVcard, _hJselV, _hJselcard, _hpoor, hPsub, _hPdense, hJ'card, hJ'dense⟩ := hSel
  have hYT : YT.card = s * mT := templateCard_eq_bins binOf YT hbin
  have hcardι : Fintype.card ↥J' = 2 ^ e / 2 := by
    rw [Fintype.card_coe, hJ'card]
  have hA : callThreeH e * (((s * mT : ℕ)) : ℝ) ^ Fintype.card ↥J'
      ≤ (((projSet J' (Pc.filter (fun f => ∀ i ∈ J', f i ∈ YT)))).card : ℝ) := by
    rw [hcardι, ← hYT]
    exact hJ'dense
  obtain ⟨bins, hbins⟩ :=
    stageThreeBin_density (mT := mT) (h := callThreeH e) hs binOf
      (projSet J' (Pc.filter (fun f => ∀ i ∈ J', f i ∈ YT))) hA
  refine ⟨e, Jsel, eJ, Pc, J', bins, hPsub, hJ'card, ?_⟩
  rw [hcardι] at hbins
  exact hbins

end StageThreeBinsAtSelection

/-! ## Section 2  The `q_2`-fibre average of `09:1473--1479`

"Every selected donor has protected-reservoir density greater than `d_cls/2`.  In
a protected reservoir, all rows carrying a fixed Stage-2 coordinate have the same
Stage-4 entry map.  Averaging these `q_2` coordinate fibres therefore supplies
more than `d_cls q_2/4` Stage-2 coordinates whose surviving `C_1`-density is at
least `d_cls/4` in each donor."

The first sentence is a clause of the banked `USetSelected` and is read off it.
The second is the **Stage-4 reservoir geometry**, which this repository has not
built; its whole content, for this step, is that the donor's density *is* the
average of its `q_2` coordinate fibres, and that is carried below as the explicit
named hypothesis `havg`.  The third sentence -- the averaging -- is then
**proved**. -/

section FibreAverage

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1473`, read off the banked deliverable.**

"Every selected donor has protected-reservoir density greater than `d_cls/2`."
This is clause 3 of `USetSelected` (`09:1443--1444`, `d_cls/2 < d_j`) restricted
along `Jsel subseteq V`, so it is a *theorem* about the produced selection and
not an assumption of this module.  General. -/
theorem selectedDonor_density_gt {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)} {s κ : ℕ}
    {θ : ℝ} (hSel : USetSelected P Res p S YT J s κ θ) :
    ∃ (k : ℕ) (Jsel : Finset (Fin q)), Jsel ⊆ J ∧
      ∀ i ∈ Jsel, classWidth k / 2 < donorDensity P Res p i := by
  obtain ⟨k, _e, _V, Jsel, _eJ, _Pc, _J', hVJ, _he4, hspec, _hlow, _hhigh, _hdelta,
    _hVcard, hJselV, _hJselcard, _hpoor, _hPsub, _hPdense, _hJ'card, _hJ'dense⟩ := hSel
  refine ⟨k, Jsel, hJselV.trans hVJ, ?_⟩
  intro i hi
  have h := (hspec i (hJselV hi)).1
  linarith

/-- **`09:1476--1479`, the fibre average, PROVED.**

"Averaging these `q_2` coordinate fibres therefore supplies more than
`d_cls q_2/4` Stage-2 coordinates whose surviving `C_1`-density is at least
`d_cls/4` in each donor."

*What is a hypothesis and what is proved.*  `havg` is the **only** input, and it
is exactly `09:1474--1476`'s reservoir geometry in the form this step uses: the
`q_2` coordinate fibres of one selected donor average at least the donor's own
lower bound `d_cls/2`.  The Stage-4 entry-map constancy that justifies it is
**not built** in this repository, so it is carried as an explicit named
hypothesis and is never closed silently.  The averaging itself -- the passage
from an average `d_cls/2` to more than `d_cls q_2/4` fibres above `d_cls/4` --
is the banked `WrapperProtectedEarly.card_ge_of_sum_ge` and is proved here.

*Why the average is genuinely needed.*  `fibreBlocks_needs_the_average` shows the
conclusion fails outright when `havg` is dropped, at `d_cls = 1` and all fibres
zero.

General in `q_2`, `d_cls` and the fibre-density family. -/
theorem fibreBlocks_ge {q₂ : ℕ} {dcls : ℝ} (fib : Fin q₂ → ℝ)
    (hd0 : 0 ≤ dcls) (hfib1 : ∀ c, fib c ≤ 1)
    (havg : (dcls / 2) * (q₂ : ℝ) ≤ ∑ c, fib c) :
    dcls * (q₂ : ℝ) / 4
      ≤ (((Finset.univ : Finset (Fin q₂)).filter (fun c => dcls / 4 ≤ fib c)).card : ℝ) := by
  classical
  have hcard : ((Finset.univ : Finset (Fin q₂)).card : ℝ) = (q₂ : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hsum : dcls / 2 * ((Finset.univ : Finset (Fin q₂)).card : ℝ)
      ≤ ∑ c ∈ (Finset.univ : Finset (Fin q₂)), fib c := by
    rw [hcard]
    exact havg
  have h := card_ge_of_sum_ge (Finset.univ : Finset (Fin q₂)) fib
    (a := dcls / 2) (b := dcls / 4) (by linarith) (fun i _ => hfib1 i) hsum
  rw [hcard] at h
  linarith

/-- **`09:1480--1483`, the represented-block total across the selected donors.**

"Across the selected donors there are at least `K_int = s kappa q_2` represented
Stage-2 outer blocks satisfying that row-density threshold."  The banked
`representedBlocks_ge` is the arithmetic `(u/2)(d_cls q_2/4) >= s kappa q_2` under
`eq:protected-dyadic-class`'s `u d_cls >= 8 s kappa`; this lemma is that
arithmetic fired at the width `u = 2^e` the selection produces, so the frozen
`u` is the frozen one and not an abstract even number.

`4 <= e` is *derived* from `09:1451--1452`'s `8 s kappa <= u d_cls < 16 s kappa`
together with `s >= 4` (`04:389`), `kappa >= 2` (`09:1420`) and `d_cls <= 1` -- it
is the banked `UsetSelection.four_le_width_exponent`, carried here as a clause of
`USetSelected` rather than read off that display alone -- and it is what makes
`u = 2^e` even, hence `u/2` a genuine half.

General in the four exponents, the class width and the per-donor block count. -/
theorem blockCount_of_perDonor {e r₂ r₃ ℓ : ℕ} {dcls perDonor : ℝ} (he : 4 ≤ e)
    (hlow : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * dcls)
    (hper : dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4 ≤ perDonor) :
    ((Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) : ℕ) : ℝ) ≤ (((2 ^ e / 2 : ℕ)) : ℝ) * perDonor := by
  have hud : 8 * (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ))
      ≤ (((2 ^ e : ℕ)) : ℝ) * dcls := by
    have hc : (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) = (2 : ℝ) ^ (r₃ + ℓ) := by
      push_cast
      rw [pow_add]
    have hu : (((2 ^ e : ℕ)) : ℝ) = (2 : ℝ) ^ e := by push_cast; ring
    rw [hc, hu]
    exact hlow
  exact representedBlocks_ge (s := 2 ^ r₃) (κ := 2 ^ ℓ) (q₂ := 2 ^ r₂) (u := 2 ^ e)
    (dvd_pow_self 2 (by omega)) hud hper

end FibreAverage

/-! ## Section 3  The two continuation readouts of `USET-SELECTION-001`, consumed

The predecessor lands exactly two readouts of `USetSelected`
(`uSetSelected_gives_sixteen_donors`, `uSetSelected_width_window`) and marks them
endpoints.  Both are consumed here, in proof terms, and each supplies one clause
of `09:1491--1497`. -/

section Readouts

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1491--1495` from the width readout alone.**

"The ambient product width is `(u/2)q_2`.  Since `d_cls <= 1` and
`eq:protected-dyadic-class` gives `u d_cls >= 8 s kappa`, this width is at least
`4 K_int`."

Proved from the banked readout `uSetSelected_width_window` -- which projects out
exactly `4 <= e` and the two dyadic bounds -- together with `classWidth_le_one`
and the banked `ambient_width_ge`.  Nothing else about the selection is used, so
the clause is visibly a consequence of the *window* and not of the geometry.

General in the row carrier, the alphabet, the width, the alleged protocol, the
reservoir and the route. -/
theorem uSetSelected_ambient_room {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)} {r₂ r₃ ℓ : ℕ}
    {θ : ℝ} (hSel : USetSelected P Res p S YT J (2 ^ r₃) (2 ^ ℓ) θ) :
    ∃ e : ℕ, 4 ≤ e ∧
      4 * Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) ≤ (2 ^ e / 2) * 2 ^ r₂ := by
  obtain ⟨k, e, he4, hlow, _hhigh⟩ := uSetSelected_width_window hSel
  refine ⟨e, he4, ?_⟩
  have hud : 8 * (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ))
      ≤ (((2 ^ e : ℕ)) : ℝ) * classWidth k := by
    have hu : (((2 ^ e : ℕ)) : ℝ) = (2 : ℝ) ^ e := by push_cast; ring
    rw [hu]
    exact hlow
  exact ambient_width_ge (dvd_pow_self 2 (by omega)) (classWidth_le_one k) hud

/-- **`09:1491`'s product width is a genuine product width.**

The banked readout `uSetSelected_gives_sixteen_donors` says the selected `u`-set
has at least `16` donors; halving it, `09:1466--1471`'s `u/2` selected donors are
at least `8`, so the ambient product width `(u/2)q_2` of `09:1491` is not the
empty or the one-copy product.  This is M9's explicit treatment of the degenerate
branches: they are ruled out by a named lemma rather than by an omitted clause.

General. -/
theorem uSetSelected_halfWidth_pos {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)} {s κ : ℕ}
    {θ : ℝ} (hSel : USetSelected P Res p S YT J s κ θ) :
    ∃ Jsel : Finset (Fin q), Jsel ⊆ J ∧ 8 ≤ Jsel.card / 2 := by
  obtain ⟨Jsel, hsub, hcard⟩ := uSetSelected_gives_sixteen_donors hSel
  exact ⟨Jsel, hsub, by omega⟩

end Readouts

/-! ## Section 4  The `09:1491--1509` deliverable, named and produced

`BlockSelected` names what the tail of the frozen proof produces before the
inherited corollary is invoked: a reachable width, the call-(iii) record of
`06:1147--1153` at that width, and the `K_int` block supply of `09:1480--1483`.

**M2 check.**  It contains no promise certificate and no complexity conclusion:
`memCost`, `child`, `B_cap` and `C` occur in none of its clauses or arguments.
Its three clauses are also mutually irredundant -- the block count is not implied
by the record, and the record is not implied by the window -- so no field
restates a derived telescope. -/

section Deliverable

/-- **The `09:1491--1509` deliverable, named.**

The three clauses, in frozen print order:

1. `ReachableWidth q r_3 ell theta e d_cls` -- `09:1449--1456` with
   `eq:protected-delta-min` (`09:1486--1490`): the width window the extraction
   chain produces, at `u = 2^e` and `d_cls = classWidth k`;
2. `ExtensionCallThree k_2 R R_loc b_1 e r_2 r_3 ell d_cls (callThreeH e)` --
   row (iii) of `sec:extension-call-ledger` (`06:1147--1153`) together with
   `eq:contract-extension-exponents` (`D:746--764`), whose exponent triple
   `(T, R, R_loc)` the record exhibits.  The entering column density is pinned at
   the frozen `h = rho_1 2^{-u-1}` of `06:1150` rather than left as a free real:
   at `a^sharp = 0` the frozen requirement is exactly `h <= colDens`, so the
   record at `colDens = h` is the frozen threshold itself and no unconstrained
   number enters;
3. `K_int <= selCard` -- `09:1480--1483`, the represented Stage-2 outer blocks
   available at the row-density threshold.

*Why the trivial witness fails.*  Clause 3 forces `selCard >= 2^{r_3+ell+r_2}`
(`blockSelected_forces_blocks`), so `selCard = 0` is refuted; clause 2's
`ambient_width` field forces `4 K_int <= 2^{e-1} q_2`, so the one-copy ambient
width `q_2` of the `v = 1` table row is refuted at every legal capacity
(`blockSelected_is_not_the_one_copy_count`); and clause 2's `four_le_e` keeps the
width at `u >= 16`, which is what supplies `09:1390--1391`'s `4 | u`.

*Non-vacuity at LEGAL parameter values.*  `blockSelected_at_scheduleTheta`
inhabits it at `theta = 1/(160 Q)` of `eq:Q-theta-choice`, at every scale
`s = 2^{r_3}` meeting `eq:s-choice`'s `512 <= s` with `64 | s`, at every capacity
`kappa = 2^{ell} >= 2` (`09:1420`), and at a width `q = 2^{A_wrap L_P^2}` of
`eq:q-deltaU` -- every one obtained by *evaluating* the frozen defining display.
The **canonical** inhabitation, the paper's own block selection inside
`lem:early-protected-closure`, remains registered and deferred. -/
def BlockSelected (q k₂ b₁ r₂ r₃ ℓ selCard : ℕ) (θ : ℝ) : Prop :=
  ∃ k e R Rloc : ℕ,
    ReachableWidth q r₃ ℓ θ e (classWidth k) ∧
      ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ (classWidth k) (callThreeH e) ∧
      ((Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) : ℕ) : ℝ) ≤ (selCard : ℝ)

end Deliverable

section Production

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1473--1509` PRODUCED from the banked `u`-set selection.**

The tail of the frozen proof, run on the head's own output.  Given the banked
`USetSelected` at the frozen dyadic scale `s = 2^{r_3}` and capacity
`kappa = 2^{ell}`:

* the width window is read off the deliverable, giving `ReachableWidth`;
* `eq:protected-delta-min` transports the schedule-owned row gate `hGate` (stated
  at `delta_min`, because the schedule cannot see which class the argument
  selects) up to the selected `d_cls`, which is what makes that display
  load-bearing;
* the call-(iii) record is **constructed** by the banked
  `extensionCallThree_of_width`, so `eq:contract-extension-exponents` is derived
  rather than assumed;
* the block supply is `09:1480--1483` through `blockCount_of_perDonor`, whose
  per-donor factor `d_cls q_2/4` is the output of Section 2's fibre average.

`hBlocks` is the one binder that is not discharged, and it is honest GAP: it says
that the `(u/2)` selected donors' represented Stage-2 blocks really are available
in the supply, i.e. `09:1479--1483` at the built Stage-4 reservoirs, which are not
modelled.  It is quantified over `ReachableWidth` rather than over all widths --
`06:938--940`'s own uniformity -- which is what keeps it satisfiable.

General in the row carrier, the alphabet, the width, the alleged protocol, the
reservoir and the route. -/
theorem blockSelection_of_uSetSelected {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Protocol {a // a ∈ Rset} Yc Zc} {Res : Finset Rw} {p : List Bool}
    {S : Finset (Fin q → Y)} {YT : Finset Y} {J : Finset (Fin q)}
    {k₂ b₁ r₂ r₃ ℓ selCard : ℕ} {θ : ℝ}
    (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hℓ : 1 ≤ ℓ)
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
      ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
      ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hSel : USetSelected P Res p S YT J (2 ^ r₃) (2 ^ ℓ) θ) :
    BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ := by
  classical
  obtain ⟨k, e, _V, _Jsel, _eJ, _Pc, _J', _hVJ, he4, _hspec, hlow0, hhigh0, hdelta,
    _hVcard, _hJselV, _hJselcard, _hpoor, _hPsub, _hPdense, _hJ'card, _hJ'dense⟩ := hSel
  have hcast : (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) = (2 : ℝ) ^ (r₃ + ℓ) := by
    push_cast
    rw [pow_add]
  have hlow : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * classWidth k := by
    rw [← hcast]
    exact hlow0
  have hhigh : (2 : ℝ) ^ e * classWidth k < 16 * ((2 : ℝ) ^ (r₃ + ℓ)) := by
    rw [← hcast]
    exact hhigh0
  have hreach : ReachableWidth q r₃ ℓ θ e (classWidth k) :=
    ⟨hlow, hhigh, classWidth_pos k, classWidth_le_one k, hdelta⟩
  have hGate' : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁ ≤ classWidth k / 4 :=
    le_trans hGate (by linarith [hdelta])
  have hcol : callThreeH e / 2 ^ (0 : ℕ) ≤ callThreeH e := by
    rw [pow_zero, div_one]
  have hcall := extensionCallThree_of_width (T := k₂) (b₁ := b₁) (e := e) (r₂ := r₂)
    (r₃ := r₃) (ℓ := ℓ) (dcls := classWidth k) (colDens := callThreeH e)
    hk₂ hk₂le hℓ (classWidth_le_one k) hlow hhigh hGate' hcol
  refine ⟨k, e, (e - 1) + r₂ - k₂, r₃ + ℓ + r₂ - k₂, hreach, hcall, ?_⟩
  exact le_trans (blockCount_of_perDonor (r₂ := r₂) he4 hlow (le_refl _))
    (hBlocks e (classWidth k) hreach)

/-- **`eq:protected-early-threshold` (`09:1421--1425`) TO `09:1509`, at the built
`P_v`.**

The whole of `lem:early-protected-closure`'s construction, run from the frozen
hypothesis on the **built** protected mass `P_v(J_0)` of
`PROTECTED-ROW-RESERVOIRS-001`: the banked `uSetSelection_of_protectedMass` is
consumed in the proof term to reach `09:1471`, and Section 4 continues to
`09:1509`'s call record and block supply.

The frozen disjunction of `09:1433` -- "one of the two protected reservoir types
contributes at least half" -- **collapses here**, and legitimately: the produced
`BlockSelected` mentions no reservoir, so both branches deliver the same
statement.  That is the first point in the chain at which the frozen proof stops
caring which type survived, and it is exactly where the frozen text stops saying
so.

**This lemma states no complexity bound.**  `C` does not occur, `memCost` does
not occur, and `WrapperProtectedEarly.earlyProtectedClosure` is not consumed.

General in the row carrier, the alphabet, the donor index, the node type and the
width. -/
theorem blockSelection_of_protectedMass {Y : Type*} [Fintype Y] [DecidableEq Y]
    {ι V : Type*} (P : Protocol {a // a ∈ Rset} Yc Zc) (node : V → List Bool)
    (donor : ι → Fin q) {RSig RD : Finset Rw} {m : ℕ} (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ))
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J₀ : Finset ι) (v : V)
    {k₂ b₁ r₂ r₃ ℓ selCard : ℕ} {θ lamT : ℝ}
    (hq : 0 < q) (hℓ : 1 ≤ ℓ) (hθ : 0 < θ) (hY : 0 < Fintype.card Y)
    (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hthr : 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
        * ((2 ^ ℓ : ℕ) : ℝ)
      ≤ donorMass (systemPv P node donor RSig RD m) J₀ v)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ (u : ℕ) (Jq : Finset (Fin q)), Jq.card = u →
      ∃ (eJ : Fin u ≃ ↥Jq) (P₀ P₁ : Finset (Fin u → Y)),
        Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel Jq eJ S)
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
      ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
      ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ)) :
    BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ := by
  have hs : 1 ≤ (2 ^ r₃ : ℕ) := Nat.one_le_two_pow
  have hκ : 2 ≤ (2 ^ ℓ : ℕ) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  rcases uSetSelection_of_protectedMass P node donor hm hSig hD S YT J₀ v
      hq hs hκ hθ hY hinj hthr hS hYT hgap hQuery with hSel | hSel
  · exact blockSelection_of_uSetSelected hk₂ hk₂le hℓ hGate hBlocks hSel
  · exact blockSelection_of_uSetSelected hk₂ hk₂le hℓ hGate hBlocks hSel

end Production

/-! ## Section 5  Readouts of the deliverable (`09:1491--1509`) -/

section DeliverableReadouts

variable {q k₂ b₁ r₂ r₃ ℓ selCard : ℕ} {θ : ℝ}

/-- **Aux E1 (`09:1480--1483`, the block supply is real).**

`BlockSelected` forces `selCard >= 2^{r_3+ell+r_2}`, since `K_int` at the frozen
dyadic widths is `2^{r_3+ell+r_2}` (`Kint_dyadic`).  This is the pole that refutes
`selCard = 0`: a green build would accept an empty block supply, and this lemma is
what does not.  General. -/
theorem blockSelected_forces_blocks (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    (((2 ^ (r₃ + ℓ + r₂) : ℕ)) : ℝ) ≤ (selCard : ℝ) := by
  obtain ⟨_k, _e, _R, _Rloc, _hreach, _hcall, hK⟩ := h
  rwa [Kint_dyadic] at hK

/-- **Aux E2 (`09:1499`, "select exactly `9 K_int/16`").**

The exact output size of row (iii) is available in the produced supply: `9K/16`
of the `K_int` represented blocks exist because `K_int` of them do.  Written in
the shape the inherited contract's `A:138--139` clause consumes.  General. -/
theorem blockSelected_selected_count (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    9 * (((2 ^ (r₃ + ℓ + r₂) : ℕ)) : ℝ) / 16 ≤ (selCard : ℝ) := by
  have hK := blockSelected_forces_blocks h
  have hnn : (0 : ℝ) ≤ (((2 ^ (r₃ + ℓ + r₂) : ℕ)) : ℝ) := by positivity
  linarith

/-- **Aux E3 (`09:1491--1497`, the ambient product width).**

"The ambient product width is `(u/2)q_2` ... this width is at least `4 K_int`.
Thus `r' = K_int/t_2` lies in the literal range of Localized Extension."  Read off
the produced record's `ambient_width` field, together with the record's own
`r' <= r`, which is `A:125`'s range clause.  General. -/
theorem blockSelected_ambient_width (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    ∃ e R Rloc : ℕ,
      4 * Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) ≤ 2 ^ (e - 1) * 2 ^ r₂ ∧
        (2 : ℕ) ^ Rloc ≤ 2 ^ R := by
  obtain ⟨_k, e, R, Rloc, _hreach, hcall, _hK⟩ := h
  exact ⟨e, R, Rloc, hcall.ambient_width, hcall.r'_le_r⟩

/-- **Aux E4 (`eq:protected-dyadic-class` survives into the tail).**

The produced width still satisfies the two frozen dyadic bounds and `4 <= e`, so
`09:1390--1391`'s `4 | u` remains available at the call site.  General. -/
theorem blockSelected_width_window (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    ∃ (k e : ℕ), 4 ≤ e ∧ 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * classWidth k ∧
      (2 : ℝ) ^ e * classWidth k < 16 * ((2 : ℝ) ^ (r₃ + ℓ)) := by
  obtain ⟨k, e, _R, _Rloc, hreach, hcall, _hK⟩ := h
  exact ⟨k, e, hcall.four_le_e, hreach.1, hreach.2.1⟩

/-- **Aux E5 (`D:752`, `K = 2^{R_loc + T}`).**

The record's capacity exponent, read off: `log_2 K_int = R_loc + k_2` at the
frozen dyadic widths.  This is the power-of-two reading that M8 demands before a
selector width may be replaced by its logarithm.  General. -/
theorem blockSelected_capacity_exponent (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    ∃ Rloc : ℕ, Rloc + k₂ = r₃ + ℓ + r₂ := by
  obtain ⟨_k, _e, _R, Rloc, _hreach, hcall, _hK⟩ := h
  exact ⟨Rloc, hcall.capacity_exponent⟩

/-- **`09:1504--1507`, the endpoint identity at the produced record.**

"Localized Extension gives the selected Bob child complexity
`B_cap + log_2 K_int = C + log_2 kappa - 1`."  At the produced record's own
capacity exponent this is `B_cap + (R_loc + k_2) + 1 = C + log_2 kappa`, written
subtraction-free (M8) at the banked `TerminalTwoStream.terminalTarget`
(`09:1777--1778`), so the frozen `-1` never becomes a truncated natural
subtraction.  General in `B_cap`. -/
theorem blockSelected_endpoint (bcap : ℕ)
    (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    ∃ Rloc : ℕ, Rloc + k₂ = r₃ + ℓ + r₂ ∧
      bcap + (Rloc + k₂) + 1 = TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ := by
  obtain ⟨Rloc, hcap⟩ := blockSelected_capacity_exponent h
  refine ⟨Rloc, hcap, ?_⟩
  have hid := endpoint_identity bcap r₂ r₃ ℓ
  simp only [TerminalTwoStream.terminalTarget, DenseBranchSelection.Dtwo] at hid ⊢
  omega

end DeliverableReadouts

/-! ## Section 6  `lem:early-protected-closure`'s conclusion, at the built `P_v`

This is the **only** place in this module where the conclusion of
`lem:early-protected-closure` (`09:1426--1429`) occurs, and it occurs as the
conclusion of a theorem, never inside constructor data (M2).

The banked `WrapperProtectedEarly.earlyProtectedClosure` already runs the frozen
proof from `eq:protected-early-threshold` stated on two abstract density families.
What is new here is that its threshold is discharged at the **built** `P_v` of
`PROTECTED-ROW-RESERVOIRS-001` through the banked `donorMass_systemPv`, so the
frozen hypothesis is now a statement about the constructed protected reservoirs
rather than about arbitrary densities.

Every remaining binder is the banked one, forwarded **verbatim and in order**; not
one of them is discharged here, and in particular `hLocEx` -- the inherited
Localized Extension corollary with the whole of `A:109--146` as its antecedent
list -- stays an explicit named hypothesis.  `EXPANDER-001` therefore reaches this
statement only through that binder and never as a silent axiom.

**Re-shape tranche.**  `hLocEx` now carries `A:138`'s own subject: the object
whose cost it concludes must *be* a restriction of `Mhat` with exactly `r' p_t`
represented outer blocks, and that object, its block count and its per-block row
count are bound inside the record quantifier.  Two binders appear here in
consequence, both forwarded and neither discharged: the abstract restriction
datum `isRestr` and the `09:1499--1504` selection `hSelect`, the latter **gated on
the built `P_v` threshold** so that no mass-free bundle reaches the endpoint.  The
conclusion is unchanged. -/

section Conclusion

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`lem:early-protected-closure` (`09:1418--1509`) at the BUILT protected
mass.**

"Let `v` be a first-Bob node and put `kappa = kappa_v >= 2`.  If
`P_v(J_0) >= 128 mu_P B_theta L_q s kappa`, then one child of `v` has
communication complexity at least `C + log_2 kappa - 1`."

The hypothesis is `eq:protected-early-threshold` on the **built** `P_v` --
`donorMass (systemPv ...) J_0 v` of `PROTECTED-ROW-RESERVOIRS-001` -- rather than
on abstract densities: the banked `donorMass_systemPv` rewrites it into the
`mu_P`-weighted sum of the two built reservoir densities, which is the shape the
banked `earlyProtectedClosure` consumes.  The frozen bracket `d_j in [0,1]` is
inherited as a theorem (`donorDensity_nonneg`, `donorDensity_le_one`), not
assumed.

The conclusion is the frozen `C + log_2 kappa - 1` at the banked
`TerminalTwoStream.terminalTarget`, written subtraction-free.

**What this does NOT do.**  It discharges none of the inherited binders:
`hLocEx`, `hbase`, `htcert`, `hE1`, `hE2`, `hrows`, `hQuery`, `hBlocks` and the
re-shape tranche's `hSelect` are
forwarded exactly as the banked statement carries them, and
`thm:certified-localized-extension` remains unproved.  `sec:wrapper-mass-`
`redistribution` (`09:1512--1781`) is not entered, `eq:wrapper-u-dense` is neither
stated nor implied, and **no route completion is claimed**.

General in the reservoir row carrier, the matrix carriers, the alphabet, the donor
index, the node type and the width. -/
theorem earlyProtectedClosure_at_builtPv
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {Rm Cm : Type*} [Fintype Rm] [Fintype Cm] (Mmat : Rm → Cm → Bool)
    {Mem : Type*} (memCost : Mem → ℕ) (child : Mem)
    (isRestr : Mem → ℕ → ℕ → ℝ → Prop)
    {ι V : Type*} (P : Protocol {a // a ∈ Rset} Yc Zc) (node : V → List Bool)
    (donor : ι → Fin q) {RSig RD : Finset Rw} {m : ℕ}
    {k₂ b₁ r₂ r₃ ℓ bcap tcert selCard rowsPerBlock : ℕ}
    {θ lamT x epsProd : ℝ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J₀ : Finset ι) (v : V)
    (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j)
    (hq : 0 < q) (hℓ : 1 ≤ ℓ) (hθ0 : 0 < θ)
    (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hbcap : 2 ≤ bcap)
    -- `eq:protected-early-threshold` (`09:1421--1425`) at the BUILT `P_v`
    (hthr : 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
        * ((2 ^ ℓ : ℕ) : ℝ)
      ≤ donorMass (systemPv P node donor RSig RD m) J₀ v)
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
      ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hY : 0 < Fintype.card Y) (hYT0 : 0 < YT.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ (u : ℕ) (Jq : Finset (Fin q)), Jq.card = u →
      ∃ (eJ : Fin u ≃ ↥Jq) (P₀ P₁ : Finset (Fin u → Y)),
        Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel Jq eJ S)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
      ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rm)
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
    (hrows : ⌈((2 : ℝ) ^ (r₃ + ℓ + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rm)⌉₊
      ≤ rowsPerBlock)
    -- `09:1499--1504`, the round-`r4` selection binder, gated on the BUILT `P_v`
    -- threshold: the restriction the endpoint speaks about exists only because
    -- `eq:protected-early-threshold` holds at the constructed reservoirs
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- The extraction re-gate is forwarded verbatim from the banked
    -- `WrapperProtectedEarly.earlyProtectedClosure`: the selection of `09:1499`
    -- fires only on the output of `09:1458--1471`, so the density chain the banked
    -- statement carries stays load-bearing through this application too.
    (hSelect : 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
          * ((2 ^ ℓ : ℕ) : ℝ)
        ≤ donorMass (systemPv P node donor RSig RD m) J₀ v →
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        ExtractionOutput S YT e →
        isRestr child ((2 : ℕ) ^ (r₃ + ℓ + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
          (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocEx : ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Mem),
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
        1 ≤ Fintype.card Rm → 2 ≤ bcap →
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
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rm)⌉₊ ≤ rowsEach →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ memCost w) :
    TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ ≤ memCost child + 1 := by
  classical
  have hthrBuilt := hthr
  rw [donorMass_systemPv P node donor hm hSig hD J₀ v hinj] at hthr
  have hJq : (J₀.image donor).card ≤ q := by simpa using (J₀.image donor).card_le_univ
  exact earlyProtectedClosure Mmat memCost child isRestr S YT (J₀.image donor)
    (donorDensity P RSig (node v)) (donorDensity P RD (node v))
    hq hℓ hθ0 hk₂ hk₂le hbcap hJq
    (fun j _ => donorDensity_nonneg P RSig (node v) j)
    (fun j _ => donorDensity_le_one P RSig (node v) j)
    (fun j _ => donorDensity_nonneg P RD (node v) j)
    (fun j _ => donorDensity_le_one P RD (node v) j)
    hthr hGate hY hYT0 hS hYT hgap hQuery hBlocks hx0 hx1 htx hMne hbase htcert
    heps0 heps1 hE1 hE2 hrows (fun _ => hSelect hthrBuilt) hLocEx

end Conclusion

/-! ## Section 7  Non-vacuity and statement poles

**CANONICAL INHABITATION IS REGISTERED AND DEFERRED.**  The paper's own instance
of `BlockSelected` is the block selection carried out inside the frozen proof of
`lem:early-protected-closure`, at the retained matrix `U'` and the alleged
protocol of `09:1188--1193`, at the schedule's materialized parameters
(`06:859--887`, MATERIALIZE-001 on the Lean side), with a block supply produced by
the Stage-4 reservoir geometry of `09:1474--1476`.  None of that is built, so the
obligation is registered here and discharged when the materialization lands.  The
inhabitant below repairs the **parameter** half only and is **NON-FIDELITY** on
the protocol, column, template and block-supply halves. -/

section NonVacuity

/-- **SCHEDULE-TIER NON-VACUITY (NON-FIDELITY on the geometry halves).**

`BlockSelected` is inhabited at parameter values the frozen defining displays
*produce*:

* `theta = 1/(160 Q)` is `eq:Q-theta-choice` in the `06:539` closed form, at the
  banked `Q = EntryGates.Qwidth b_out delta_U` of `06:532`, entering only through
  the frozen side conditions `b_out >= 1` (`05:39--40`) and `delta_U <= 1/200`
  (`06:547`);
* `s = 2^{r_3}` carries `eq:s-choice`'s consequences `512 <= s` and `64 | s`
  (`06:110--121` with `06:394--395`) through the binder `9 <= r_3`;
* `kappa = 2^{ell} >= 2` is `09:1420`;
* `q = 2^{A_wrap L_P^2}` is `eq:q-deltaU` (`06:513--519`) with `A_wrap` *produced*
  by the banked `exists_wrapper_width` from `06:520--522`, never picked;
* `b_1` is likewise produced, in closed form, by the banked
  `earlyProtectedClosure_block_bundle_at_scheduleTheta`;
* the width is the banked `reachableWidth_at_scheduleTheta`'s
  `(e, d_cls) = (r_3 + ell + 4, 1/2)`, which attains the lower dyadic bound of
  `eq:protected-dyadic-class` exactly, and `1/2 = classWidth 1`;
* `k_2` is a binder at `4 <= k_2` with the frozen Stage-2 gate `k_2 + 2 <= r_2`
  (`eq:stage2-structural-gates`, `06:830--837`); `eq:t2-search` (`06:763--770`) is
  **not** evaluated, and no numeral is assigned to `k_2`.

The block supply is taken at `selCard = K_int`, the extreme legal point of
`09:1480--1483`'s own inequality "there are **at least** `K_int` represented
blocks", so it is the frozen bound itself and not a chosen number.

*What this does not do.*  It is not the canonical inhabitation: the protocol,
column, template and block-supply halves of the paper's instance are unbuilt, and
this statement is about the arithmetic deliverable alone.  It is offered only
against the LANE-GATE-3 vacuity charge on the parameter half. -/
theorem blockSelected_at_scheduleTheta {bout : ℕ} {δU : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 200)
    {r₃ ℓ r₂ k₂ LP : ℕ} (hr₃ : 9 ≤ r₃) (hℓ : 1 ≤ ℓ) (hLP : 1 ≤ LP)
    (hk₂ : 4 ≤ k₂) (hgate : k₂ + 2 ≤ r₂) :
    ∃ Awrap b₁ : ℕ, 1 ≤ Awrap ∧
      512 ≤ (2 ^ r₃ : ℕ) ∧ (64 : ℕ) ∣ 2 ^ r₃ ∧ 2 ≤ (2 ^ ℓ : ℕ) ∧
      BlockSelected (2 ^ (Awrap * LP ^ 2)) k₂ b₁ r₂ r₃ ℓ
        (Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂))
        (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) := by
  classical
  set θ : ℝ := 1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) with hθdef
  obtain ⟨Awrap, b₁, hA1, h512, h64, h2, _hB2, _hBle, _hLq, _hstage2, hthrq, hGate⟩ :=
    earlyProtectedClosure_block_bundle_at_scheduleTheta (r₂ := r₂) (k₂ := k₂)
      (LP := LP) hb hδ0 hδ hr₃ hℓ hLP hgate
  refine ⟨Awrap, b₁, hA1, h512, h64, h2, ?_⟩
  -- `1/2 = classWidth 1`, the class width `reachableWidth_at_scheduleTheta` stands at
  have hcw : classWidth 1 = 1 / 2 := by
    rw [classWidth]
    norm_num
  -- `eq:protected-delta-min` at this width, from the bundle's own threshold clause
  have hqpos : (0 : ℝ) < ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) := by positivity
  have h2R : (2 : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h2
  have hXnn : (0 : ℝ) ≤ 64 * (Btheta θ : ℝ) * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ)
      * ((2 ^ r₃ : ℕ) : ℝ) := by positivity
  have hdouble : (64 * (Btheta θ : ℝ) * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ)
        * ((2 ^ r₃ : ℕ) : ℝ)) * 2
      ≤ ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) := by
    have hmono : (64 * (Btheta θ : ℝ) * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ)
          * ((2 ^ r₃ : ℕ) : ℝ)) * 2
        ≤ (64 * (Btheta θ : ℝ) * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ)
          * ((2 ^ r₃ : ℕ) : ℝ)) * ((2 ^ ℓ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h2R hXnn
    linarith [hthrq, hmono]
  have hdelta : 64 * (Btheta θ : ℝ) * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ)
        * ((2 ^ r₃ : ℕ) : ℝ) / ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ)
      ≤ classWidth 1 := by
    rw [hcw, div_le_iff₀ hqpos]
    linarith [hdouble]
  -- `eq:protected-dyadic-class` at `e = r_3 + ell + 4`, the lower bound attained exactly
  have hexact : (2 : ℝ) ^ (r₃ + ℓ + 4) * classWidth 1 = 8 * (2 : ℝ) ^ (r₃ + ℓ) := by
    rw [hcw, show r₃ + ℓ + 4 = (r₃ + ℓ) + 4 by ring, pow_add]
    ring
  have hlow : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ (r₃ + ℓ + 4) * classWidth 1 := by
    rw [hexact]
  have hhigh : (2 : ℝ) ^ (r₃ + ℓ + 4) * classWidth 1 < 16 * ((2 : ℝ) ^ (r₃ + ℓ)) := by
    rw [hexact]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (r₃ + ℓ) := by positivity
    linarith
  have hreach : ReachableWidth (2 ^ (Awrap * LP ^ 2)) r₃ ℓ θ (r₃ + ℓ + 4) (classWidth 1) :=
    ⟨hlow, hhigh, classWidth_pos 1, classWidth_le_one 1, hdelta⟩
  have hGate' : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁ ≤ classWidth 1 / 4 :=
    le_trans hGate (by linarith [hdelta])
  have hcol : callThreeH (r₃ + ℓ + 4) / 2 ^ (0 : ℕ) ≤ callThreeH (r₃ + ℓ + 4) := by
    rw [pow_zero, div_one]
  have hcall := extensionCallThree_of_width (T := k₂) (b₁ := b₁) (e := r₃ + ℓ + 4)
    (r₂ := r₂) (r₃ := r₃) (ℓ := ℓ) (dcls := classWidth 1)
    (colDens := callThreeH (r₃ + ℓ + 4))
    hk₂ (by omega) hℓ (classWidth_le_one 1) hlow hhigh hGate' hcol
  exact ⟨1, r₃ + ℓ + 4, (r₃ + ℓ + 4 - 1) + r₂ - k₂, r₃ + ℓ + r₂ - k₂,
    hreach, hcall, le_refl _⟩

/-- **STATEMENT POLE 1: the bin average really loses a factor.**

`exists_stageThreeBin` produces a fibre carrying at least a `s^{-|iota|}` share,
and the shrinkage is not an artefact: at one donor over a two-letter alphabet
whose two Stage-3 bins are singletons, **every** bin fibre is a proper subset of
`A`.  So an encoding that dropped the `s^{|iota|}` factor -- and thereby claimed
the fixing loses nothing in absolute count rather than in relative density --
would be false, and a green build would not see it.  Unconditional. -/
theorem stageThreeBin_is_not_free (p : Fin 1 → Fin 2) :
    ((Finset.univ : Finset (Fin 1 → Fin 2)).filter
        (fun f => stageThreeBinVector (fun y : Fin 2 => y) f = p)).card
      < (Finset.univ : Finset (Fin 1 → Fin 2)).card := by
  classical
  have hfil : ((Finset.univ : Finset (Fin 1 → Fin 2)).filter
      (fun f => stageThreeBinVector (fun y : Fin 2 => y) f = p)) = {p} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hf
      exact hf
    · intro hf
      exact hf
  rw [hfil, Finset.card_singleton, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  norm_num

/-- **STATEMENT POLE 2: `09:1476--1479` genuinely needs `09:1473--1476`.**

Drop the averaging hypothesis `havg` of `fibreBlocks_ge` and its conclusion is
false: at `d_cls = 1`, `q_2 = 4` and all four coordinate fibres empty, the frozen
count `d_cls q_2/4 = 1` exceeds the actual count `0`.  This is why the Stage-4
entry-map constancy of `09:1474--1476` is carried as an explicit named hypothesis
rather than closed silently.  Unconditional. -/
theorem fibreBlocks_needs_the_average :
    ¬ ((1 : ℝ) * ((4 : ℕ) : ℝ) / 4
        ≤ (((Finset.univ : Finset (Fin 4)).filter
            (fun _c : Fin 4 => (1 : ℝ) / 4 ≤ (0 : ℝ))).card : ℝ)) := by
  classical
  have hempty : ((Finset.univ : Finset (Fin 4)).filter
      (fun _c : Fin 4 => (1 : ℝ) / 4 ≤ (0 : ℝ))) = ∅ := by
    refine Finset.filter_false_of_mem ?_
    intro c _
    norm_num
  rw [hempty]
  norm_num

/-- **STATEMENT POLE 3: the ambient product width is not the one-copy width.**

`09:1491` reads the ambient product width as `(u/2)q_2`, and `09:1493--1495`
forces it to be at least `4 K_int`.  At every legal capacity (`kappa >= 2`, i.e.
`1 <= ell`) that is strictly more than the one-copy width `q_2` of the `v = 1`
table row (`07:316--319`), so reading row (iii)'s ambient width off the wrong
table row is a real error that a green build would accept.  General. -/
theorem blockSelected_is_not_the_one_copy_count {q k₂ b₁ r₂ r₃ ℓ selCard : ℕ} {θ : ℝ}
    (hℓ : 1 ≤ ℓ) (h : BlockSelected q k₂ b₁ r₂ r₃ ℓ selCard θ) :
    ∃ e : ℕ, 2 ^ r₂ < 2 ^ (e - 1) * 2 ^ r₂ := by
  obtain ⟨_k, e, _R, _Rloc, _hreach, hcall, _hK⟩ := h
  refine ⟨e, ?_⟩
  have hamb := hcall.ambient_width
  rw [Kint_dyadic] at hamb
  have hPpos : 0 < (2 : ℕ) ^ r₂ := pow_pos (by norm_num) r₂
  have hstep : (2 : ℕ) ^ (1 + r₂) ≤ 2 ^ (r₃ + ℓ + r₂) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdouble : 2 * (2 : ℕ) ^ r₂ ≤ 2 ^ (r₃ + ℓ + r₂) := by
    rw [pow_add] at hstep
    simpa using hstep
  omega

end NonVacuity

end EthInapproximability.ParameterizedNP.EarlyClosureBlockSelection
