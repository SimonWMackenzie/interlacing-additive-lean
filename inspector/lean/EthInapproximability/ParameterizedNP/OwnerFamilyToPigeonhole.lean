import EthInapproximability.ParameterizedNP.OwnerIndexedTransferFamily

/-!
# Parameterized NP route: the owner family wired into the terminal pigeonhole

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche).  Every anchor below was opened
  first-hand in that file for this tranche.

  This module is **round 5** of the mass-redistribution segment.  It is a
  **wiring** round: it introduces no new frozen display of its own beyond the
  three sentences `09:1702`, `09:1704--1709` and `eq:wrapper-terminal-density`
  (`09:1710--1713`), and its whole content is the passage from the *realization
  form* of the round-4 endpoint into the *already banked* pigeonhole layer of
  `WrapperMassRedistribution`.  Both sides are consumed **by pin in actual proof
  terms**: the pigeonhole layer throughout §1--§5, and the round-4 realization
  endpoint in **§5b**, which applies it at every member of `J_good`.

  ### Repair record (this generation)

  The previous generation of this module carried the round-4 endpoint **only**
  as the binder `hexc` and applied the banked declaration nowhere; its header
  and ledger row nonetheless claimed it was consumed by pin.  That claim was
  false as written, a green build could not see it, and it was the reason the
  generation was not banked.  This generation:

  * adds **§5b**, whose `goodDonorFamily_exceptionalMass_of_realization`
    discharges `hexc` in a proof term by applying
    `OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization`
    under the realization telescope quantified over `J_good`;
  * re-expresses the two endpoints through it as
    `exists_terminal_star_and_reservoir_of_realization` and
    `uDon_floor_of_realization`, keeping the general `hexc`-taking forms
    alongside as the weaker interface;
  * corrects the `u_don` citation (`06:726--728` defines `u_term`, not
    `u_don`), the description of `u_don` as an accessor, the `eta_R <= 1/36800`
    attribution, and the inline re-spelling of the banked `probeMass`;
  * closes the `u_don` leg's live-fire coverage gap
    (`uDon_bundle_is_consistent`, `uDon_floor_fires_at_the_probe`).

  The `DenseRung` reach posture is **unchanged**: `hDenseRung` still does not
  land, L1 remains the registered gap, and no probe discharges it.

  The anchors traced here, in the order the frozen block prints them:

  * **`09:1700--1701`**, the round-4 endpoint: "Together with
    `eq:wrapper-mass-leaves-owner`, this says that every good donor sends more
    than `eta_R/4` protected mass to exceptional final nodes."  Consumed **by
    pin** as the banked
    `OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization`,
    which **§5b applies in a proof term** at every member of `J_good`; this
    module proves that endpoint nowhere and states it in no banked form of its
    own.  The general declarations of §1--§5 take it as the explicit hypothesis
    `hexc` -- exactly that endpoint's conclusion quantified over `J_good` --
    and §5b is what discharges `hexc` from the realization telescope, so that
    the general forms and the wired `_of_realization` forms sit side by side
    and the consumption claim is literal rather than nominal.
  * **`09:1702`**, "If `e_T = 0`, this is already a contradiction."  Landed as
    `exceptionalFinal_nonempty_of_goodDonor` and its cardinality form
    `exceptionalCount_pos_of_goodDonor`, through the banked
    `WrapperMassRedistribution.exceptional_nonempty_of_positive_mass`.
  * **`09:1704--1705`**, "Assume then that `e_T > 0`.  For each good donor
    choose an exceptional node receiving more than `eta_R/(4 e_T)` of its
    protected mass."  The choice is *produced*, not assumed: the general
    averaging step is `exists_heavy_member` and its instance at the routed
    system is `exists_heavy_exceptional_node`.
  * **`09:1705--1707`**, "Some exceptional node `T_*` is chosen by at least
    `|J_good|/e_T` donors."  Landed as `exists_common_exceptional_node`,
    through the banked `WrapperMassRedistribution.exists_heavy_fibre`, with the
    frozen chosen-donor set reified as `donorsHeavyAt`.
  * **`09:1707--1708`**, "One common reservoir type accounts for at least half
    of those donors."  Landed as `exists_half_fibre` (the *same* banked
    `exists_heavy_fibre` run at the two-element type carrier) together with
    `dominantReservoir` and `selectedDonors`.
  * **`09:1708--1713`**, "for each selected donor its density at `T_*` is at
    least `delta_0 = eta_R/(8 e_T mu_P)`" (`eq:wrapper-terminal-density`).
    `delta_0` is the banked `WrapperMassRedistribution.deltaZero` and is
    **not** redefined; the per-donor bound is
    `deltaZero_le_dens_of_selected`, through the banked
    `WrapperMassRedistribution.deltaZero_of_pigeonhole`, and the halving of the
    frozen mass between the two reservoir types is **derived**
    (`mass_halved_at_dominantReservoir`) rather than assumed.
  * **`09:1370--1373`**, "Each outer coordinate contains two protected row
    reservoirs, each of mass `mu_P = 1/184` relative to the `m` rows of one copy
    of `N`."  This is the display that makes the mass split
    `m_{j,T} <= mu_P d_Sigma + mu_P d_D` the frozen reading of a donor's
    protected mass at a node, and it is the *only* place the two reservoir
    types enter below (still by counting only -- GAP item M3).
  * **`09:1742--1744`**, "If `delta_0 >= 1`, the strict pigeonhole conclusion
    preceding `eq:wrapper-terminal-density` is itself impossible.  We may
    therefore assume `delta_0 < 1`, and hence `u_don >= 8s`."  Landed as
    `deltaZero_le_one_of_selected` and `terminal_uDon_floor`, through the banked
    `WrapperMassRedistribution.uDon_ge_eight_s`.  This is the one step past
    `09:1713` that the wired chain genuinely reaches: the relative density
    produced at `T_*` is at most one, so the frozen alternative is discharged
    from the chain rather than assumed.

* **Cross-anchors opened first-hand for this tranche:** `09:1553` (the
  definition of "exceptional"), `09:1548` and `09:1550--1552` (`J_good`, the
  unique owner, distinct owners), `09:1557--1558` (`e_T = n_T - |J_good|`),
  `09:1566--1568` (`m_{j,T}`), `09:1537` (`P_v({j})`), `09:1611--1615`
  (`eq:wrapper-mass-leaves-owner`), `09:1643--1646` (the two reservoir types),
  `09:1683--1687` (`eq:wrapper-owner-gates`), `09:1697`
  (`eq:wrapper-good-to-good`), `09:1715--1744` (the schedule layer that consumes
  `delta_0`), `09:1746--1781` (the final Extension call, **not** entered here),
  `09:1188--1193` and `09:1783` (the shape of the whole dense argument and the
  start of the proof of `thm:first-wrapper`).

## What this module adds, item by item

1. **`e_T > 0` is now a theorem of the chain, not a case assumption.**  The
   frozen `09:1702` is a one-line contradiction only because the endpoint of
   `09:1701` is already available at *some* good donor.  Here that implication
   is executed: `hexc` at one member of `J_good` produces
   `(exceptionalFinal S Pv etaR).Nonempty`, hence `0 < e_T`, and the frozen
   "assume then that `e_T > 0`" of `09:1704` needs no separate binder anywhere
   below.
2. **The frozen choice of `09:1704--1705` is constructed.**  A general averaging
   lemma over a nonempty finite set (`exists_heavy_member`) turns the endpoint's
   *aggregate* bound `eta_R/4 < sum_{T exceptional} m_{j,T}` into the frozen
   *pointwise* one `eta_R/(4 e_T) < m_{j,T_j}` at some exceptional `T_j`.  No
   choice function is assumed; the one the frozen sentence names is built inside
   `exists_common_exceptional_node` and discarded, so nothing below depends on
   which node a donor chose.
3. **Both pigeonholes are the *same* banked lemma.**  `09:1706--1707`'s node
   pigeonhole and `09:1707--1708`'s reservoir-type pigeonhole are two
   instantiations of `WrapperMassRedistribution.exists_heavy_fibre`, at the
   exceptional-node carrier and at `Bool`.  This is why the module defines no
   averaging machinery of its own beyond the one-line `exists_half_fibre`.
4. **The reservoir halving is derived.**  The frozen "one common reservoir type
   accounts for at least half of those donors" is *not* carried as a numerical
   binder.  Given only the `09:1370--1373` mass split
   `m_{j,T} <= mu_P d_Sigma + mu_P d_D`, `dominantReservoir` picks the larger of
   the two relative densities and `mass_halved_at_dominantReservoir` proves the
   halving; the *common* type across donors is then the `Bool` pigeonhole.  What
   remains a binder is only the split itself (M3).
5. **`eq:wrapper-terminal-density` lands as a per-donor conclusion.**  The
   endpoint `exists_terminal_star_and_reservoir` produces, from `hexc` and the
   mass split alone, an exceptional node `T_*`, a reservoir type `ty`, the
   frozen donor count `|J_good| <= 2 e_T |D_sel|` and the frozen density bound
   `delta_0 <= d_ty(j, T_*)` at every selected donor.
6. **One step past `09:1713` closes from the chain.**  Because a relative
   density is at most one, `delta_0 <= 1` follows from the produced bound, and
   the banked `uDon_ge_eight_s` then gives the frozen `u_don >= 8s` of
   `09:1744`.  The frozen `09:1742`'s "if `delta_0 >= 1` ... impossible" is
   therefore discharged here rather than assumed.
7. **`hexc` is discharged, not merely carried (§5b).**  The round-4 endpoint is
   *applied* at every good donor from the realization telescope of
   `09:1661--1669`, so `09:1701` enters the wired endpoints
   `exists_terminal_star_and_reservoir_of_realization` and
   `uDon_floor_of_realization` through a proof term rather than a hypothesis.
   The seam those two carry is therefore `09:1701 -> 09:1713` and
   `09:1701 -> 09:1744`; the general forms carry `09:1702 -> ...`, because for
   them `09:1701` *is* the hypothesis.

## REACH GOAL, recorded honestly: `hDenseRung` does **not** land

The stated reach of this round was the `DenseRung` discharge through the banked
`WrapperMassRedistribution.denseRung_of_no_shallow_member` at its pin.  **It does
not land, and no conditional shell is offered in its place**: this module
contains no declaration whose conclusion is `eq:wrapper-u-dense`, none that takes
`hmember` and returns `DenseRung`, and none that mentions `Dfamily`.  What that
bridge needs is the per-member refutation
`forall RC in bracketGE ..., forall c in AchievableCosts ..., C + r <= c`, and the
exact links still missing between the endpoint proved here and that hypothesis
are:

* **(L1) the routed system itself.**  The bridge quantifies over an *arbitrary*
  member of the bracket family and an *arbitrary* shallow protocol on it.
  Producing, from that data, a `RoutedCertificateSystem.RoutedSystem` together
  with its protected-mass family `P_v` is the transcript-level construction
  recorded as GAP item M1 of `OwnerMassTransfer` and as GAP item 1 of
  `ROUTED-CERTIFICATE-SYSTEM-001`.  Every theorem below begins with a routed
  system already in hand.
* **(L2) the realization telescope itself.**  `hexc` is no longer the residue:
  §5b discharges it from the round-4 realization bundle in a proof term.  What
  the wired endpoints now demand instead is that bundle -- the row sections
  `iotaA`/`iotaB` and games `hgame`, the owner-side reservoir split
  `hownerSplit` (`09:1643--1646`), the deficit-sum majorant, the frozen
  `eq:wrapper-mass-leaves-owner` family `hleaves`, and above all
  `TERMINAL-TWO-STREAM-001` (the `hTTS` family), which is **stated and not
  proved**.  This is a strictly shorter residue than the previous generation's,
  since the arithmetic from that bundle to `09:1701` is now discharged; but it
  is still a residue, and none of it is claimed here.
* **(L3) the poor-`u_don` projection cover at `T_*` (`09:1746--1749`).**  The
  cover exists (`WrapperProjectionCovers.productProjectionCover`) and the
  counting step is banked (`WrapperMassRedistribution.donors_survive_cover`),
  but applying it to `donorsHeavyAt` requires the outer-coordinate injectivity
  of `09:1235--1236`, which round 4 recorded as NOT ENCODED (its GAP item 2).
* **(L4) `lem:template-coordinate-extraction` at the selected donors
  (`09:1750--1762`).**  The per-donor Stage-2 averaging that turns the density
  `delta_0` into represented blocks is not formalized; only its arithmetic
  (`terminalBlockSupply`) is banked.
* **(L5) the row-(iv) Localized Extension endpoint (`09:1764--1779`).**  The
  call record `ExtensionCallFour` is banked and constructible
  (`extensionCallFour_of_width`), but its *conclusion* is the INHERITED
  Localized Extension corollary of Appendix D, which enters
  `terminalCall_contradiction` as the separate named implication `hExtension`
  and has no Lean proof.

Only after L1--L5 does `terminalCall_contradiction` fire and `hmember` become
available.  This module closes L0 (the pigeonhole layer) and nothing else; the
five items above are the exact residue, and **no route completion is claimed**.

## What this module deliberately is not

* **No new frozen constant, carrier or gate.**  `mu_P`, `delta_0`, `J_good`,
  the exceptional set and both averaging lemmas are consumed by pin from
  `WrapperProtectedEarly`, `WrapperMassRedistribution` and
  `MassRedistributionCounting`.  The three definitions introduced
  (`donorsHeavyAt`, `dominantReservoir`, `selectedDonors`) are *derived* finite
  sets and a derived choice of index; none carries a complexity or robustness
  conclusion, and none restates a derived telescope.
* **No new premise bundle.**  Every hypothesis is an explicit binder, per the
  standing preference over bundles; no `structure`, `inductive` or `class` is
  declared here, so no *new* bundle inhabitation is owed.  §5b's telescope does
  mention banked structures (`StageTwoRelaxed.StageTwoWidths`,
  `TerminalTwoStream.TerminalTwoStream`,
  `TerminalTwoStream.ExtensionCallTwoFixedWidth`,
  `TerminalTwoStream.terminalSeedInputs`), but only as the *banked endpoint's
  own* binders reproduced unchanged; their inhabitation obligations belong to
  their own ledger rows and are neither restated nor discharged here.
* **`TERMINAL-TWO-STREAM-001` is not proved, and after this round it is
  visible.**  In the previous generation it occurred in no hypothesis, because
  the round-4 endpoint was carried as the flat binder `hexc`.  Now that §5b
  applies that endpoint, the endpoint's own `hTTS` binder is reproduced in the
  wired telescope, so `TERMINAL-TWO-STREAM-001` is an explicit named hypothesis
  of `goodDonorFamily_exceptionalMass_of_realization`,
  `exists_terminal_star_and_reservoir_of_realization` and
  `uDon_floor_of_realization`.  It is **stated and not proved** upstream, this
  module neither proves nor weakens it, and the conditional shape it carries is
  exactly the banked one -- which is the honest cost of turning a restatement
  into a wiring, and is recorded as reach-goal residue L2.  The general forms of
  §1--§5 are unaffected and still do not mention it.
* **`R5` is not leaned on.**  The `r5_seven_binders_live` /
  `r5_eighth_binder_fails_here` audit pair of `MassLeavesOwner` is a
  NON-FIDELITY probe whose eighth item is provably false at that point; no
  declaration below consumes it, mentions it, or treats it as an inhabitant.

## GAP-EXPOSED, carried forward

1. **L1--L5 above**, which are the reach-goal residue and the reason
   `hDenseRung` is untouched.
2. **M3, the two reservoir types, still enters only by counting.**  The mass
   split `hsplit` is the frozen `09:1370--1373` sentence carried as a binder;
   what is *derived* here is only that the larger of the two densities carries
   at least half the mass.
3. **`P_v` is still the doubly-indexed binder** that
   `MASS-REDISTRIBUTION-COUNTING-001` registered; this module only aggregates
   and re-slices it.
4. **The relative-density bound `d <= 1` is a binder** (`hdens1`), because the
   density carrier `dens` is itself a binder; it becomes derivable exactly when
   L1 lands and `dens` is read off `streamRows`.
5. **`|J_good|` is not compared to the schedule here.**  `09:1719--1741`'s
   `|J_good| >= q - E_T` and `eq:wrapper-terminal-donor-gate` are banked as the
   general `goodDonorCount_ge` and `wrapperTerminalDonorGate` and are *not*
   instantiated at the routed system by this round; that instantiation needs
   `eq:wrapper-clean-count`'s first clause, still a binder.

## Reader counterpart

**None claimed, deliberately rather than by omission.**  All nine files of
`routes/parameterized-np/reader-facing/sections/` were swept first-hand for this
tranche (`exceptional`, `pigeonhole`, `reservoir`, `donor`, `owner`, `density`,
`terminal`): the words `e_T`, `T_*`, `delta_0`, `J_good` and "pigeonhole" occur
nowhere in the reader artifact.  The reader's nearest account of this block is
`A-stage4-details.tex:370--399`, which is **unnumbered proof prose** inside the
proof of `thm:paper-adapted-stage4-interface` -- `:373--378` and `:396--399` are
already recorded as unclaimed by `WrapperProjectionCovers`,
`MassRedistributionCounting`, `MassLeavesOwner`, `OwnerMassTransfer` and
`OwnerIndexedTransferFamily`; `:387--391` is already assigned to
`TERMINAL-TWO-STREAM-001`; and the one display in range, `:393--395`, is
`eq:wrapper-u-dense` itself, which this module does **not** close and therefore
must not claim.  Citing prose as a statement is barred, and a reader item may not
be assigned twice.  `READER_CROSSWALK.md` is therefore unmodified by this
tranche.

## Axiom surface

No new `axiom`, no proof-suppression token, no opaque certificate.  Every
external contact is an explicit binder.

In the general forms of §1--§5: the protected-mass family `Pv`, the per-donor
endpoint `hexc` (`09:1700--1701`, the round-4 conclusion), the frozen mass split
`hsplit` (`09:1370--1373`), the relative-density bound `hdens1`, and -- in the
`u_don` leg only -- the frozen defining demand `hdef` (`09:1717--1718`), which
is the least-power-of-two search read as an inequality and not a new definition.

In the wired forms of §5b: `hexc` is **gone** (it is discharged in a proof term)
and in its place stands the banked endpoint's own realization telescope,
reproduced binder for binder and quantified over `J_good`.  That telescope
contains `hTTS` -- `TERMINAL-TWO-STREAM-001`, stated and not proved upstream --
so the wired declarations are conditional on it *by explicit named hypothesis*,
never by axiom and never silently.  Nothing in the telescope is strengthened,
weakened, or replaced by a bundle field.

`EXPANDER-001` occurs in no hypothesis of this module and has no Lean
declaration by design.  `LegacyNPCC.Stage12` -- whose closure reaches the cited
AGHP balanced-family axiom -- is **not** in the import closure: the single
import is `OwnerIndexedTransferFamily`, whose ledger row records the same
exclusion.  Every declaration below is `Classical`-only.

## Non-vacuity and canonical inhabitation

**CANONICAL INHABITATION -- REGISTERED and DEFERRED, inherited unchanged.**  The
paper's own instance of this block is the exceptional frontier of the routed
certificate system of the *alleged shallow protocol* at the matrix `N` of the
frozen construction.  That routing, its protected-mass family `P_v` and the
reservoir densities are unbuilt (L1 above), so **no paper instance exists to
exhibit**, and the obligation is discharged only when the wrapper's
transcript-level construction lands -- never by the probe below.

The non-vacuity load is carried by two sections.  §6 exhibits the statement
poles: the strictness of the averaging hypothesis is shown to be load-bearing
(a flat family has no heavy member), the dominance rule is shown not to be
replaceable by a fixed type, the produced density bound is shown to refute the
zero-density family, and `e_T = 0` is shown to be genuinely impossible rather
than merely excluded by fiat.  §8 then fires the **whole hypothesis bundle of
the endpoint** at the banked live routed system, at a point where
`|J_good| = 1`, `e_T = 1`, both reservoirs are present and the frozen mass split
holds with equality -- so the bundle is demonstrably not contradictory.  §8 then
*applies* the endpoint to that bundle (`endpoint_fires_at_the_probe`), which a
green statement gate cannot distinguish from mere consistency.  This generation
extends that live fire to the **`u_don` leg**, which the previous one left
unexercised: `deltaZero_at_probe_eq` evaluates `eq:wrapper-terminal-density`
through its definitional chain (`23/100`, computed, never assigned),
`uDon_bundle_is_consistent` shows the two extra binders `hdens1` and `hdef`
jointly satisfied non-degenerately, and `uDon_floor_fires_at_the_probe` runs
`09:1701 -> 09:1744` on the concrete system.  Every one of these is labelled
**NON-FIDELITY / BEYOND-PAPER AUDIT** in situ: the mass family, the `eta_R`, the
`s` and the `u_don` used there are ours, not the paper's, and they audit our
encoding at a point the frozen construction never visits.

**The wired §5b declarations are NOT fired at the probe, deliberately.**  Their
telescope is the round-4 realization bundle, whose inhabitation is exactly
residue L1--L2; constructing a synthetic inhabitant for it would be a
degenerate, cardinality-unchecked object, and firing the wired endpoints at one
would be evidence of nothing.  The canonical-inhabitation obligation therefore
stays **REGISTERED and DEFERRED** for those three declarations as well, and the
probes above are explicitly *not* offered as its discharge.
-/

namespace EthInapproximability.ParameterizedNP.OwnerFamilyToPigeonhole

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.OwnerMassTransfer

/-! ## §1  `09:1702`: the `e_T = 0` contradiction, executed

"If `e_T = 0`, this is already a contradiction."

At the routed system this is not a case split to be assumed away: the round-4
endpoint at *one* good donor already forces the exceptional set to be inhabited,
because a strictly positive mass cannot be spread over no nodes.  The arithmetic
is the banked `WrapperMassRedistribution.exceptional_nonempty_of_positive_mass`,
consumed by pin. -/

section EmptyCase

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **`09:1702`, at the routed system.**

From the `09:1701` endpoint at a single good donor: the exceptional final nodes
form a nonempty set.  `exceptionalMass` is the banked
`OwnerMassTransfer.exceptionalMass`, i.e. the sum of `m_{j,T}` over the derived
exceptional set of `09:1553`, so this is literally the frozen sentence.
General. -/
theorem exceptionalFinal_nonempty_of_goodDonor (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} {j : ι} (hetaR : 0 < etaR)
    (hexc : etaR / 4 < exceptionalMass S Pv etaR j) :
    (exceptionalFinal S Pv etaR).Nonempty :=
  exceptional_nonempty_of_positive_mass (exceptionalFinal S Pv etaR) (fun T => Pv T j)
    hetaR hexc

/-- **`09:1704`, "Assume then that `e_T > 0`", as a conclusion.**

The cardinality form of the previous theorem: the frozen assumption opening the
pigeonhole paragraph is produced by the endpoint and is therefore never a binder
below.  General. -/
theorem exceptionalCount_pos_of_goodDonor (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} {j : ι} (hetaR : 0 < etaR)
    (hexc : etaR / 4 < exceptionalMass S Pv etaR j) :
    0 < (exceptionalFinal S Pv etaR).card :=
  Finset.card_pos.mpr (exceptionalFinal_nonempty_of_goodDonor S Pv hetaR hexc)

end EmptyCase

/-! ## §2  `09:1704--1705`: the per-donor choice of a heavy exceptional node

"For each good donor choose an exceptional node receiving more than
`eta_R/(4 e_T)` of its protected mass."

The choice is produced from the aggregate bound by averaging.  The general step
is stated for an arbitrary nonempty finite family of reals so that nothing about
the wrapper enters it. -/

section Averaging

/-- **The averaging step behind `09:1704--1705`, general.**

If a nonempty finite family of reals sums to strictly more than `c`, some member
strictly exceeds the average `c/|T|`.  Proved by contradiction against the
constant majorant; general in the carrier. -/
theorem exists_heavy_member {κ : Type*} (T : Finset κ) (f : κ → ℝ) (c : ℝ)
    (hT : T.Nonempty) (hsum : c < ∑ v ∈ T, f v) :
    ∃ v ∈ T, c / (T.card : ℝ) < f v := by
  classical
  by_contra hcon
  push Not at hcon
  have hcard : (0 : ℝ) < (T.card : ℝ) := by
    have := Finset.card_pos.mpr hT
    exact_mod_cast this
  have hle : ∑ v ∈ T, f v ≤ ∑ _v ∈ T, c / (T.card : ℝ) :=
    Finset.sum_le_sum fun v hv => hcon v hv
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  have hrhs : (T.card : ℝ) * (c / (T.card : ℝ)) = c := by
    field_simp
  rw [hrhs] at hle
  exact absurd hsum (not_lt.mpr hle)

end Averaging

section HeavyNode

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **`09:1704--1705` at the routed system.**

"For each good donor choose an exceptional node receiving more than
`eta_R/(4 e_T)` of its protected mass."  The frozen threshold is the average of
the endpoint's `eta_R/4` over the `e_T` exceptional nodes, so it is *produced*
by `exists_heavy_member` and not posited.  General. -/
theorem exists_heavy_exceptional_node (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} {j : ι}
    (hne : (exceptionalFinal S Pv etaR).Nonempty)
    (hexc : etaR / 4 < exceptionalMass S Pv etaR j) :
    ∃ T ∈ exceptionalFinal S Pv etaR,
      etaR / (4 * ((exceptionalFinal S Pv etaR).card : ℝ)) < Pv T j := by
  obtain ⟨T, hT, hlt⟩ :=
    exists_heavy_member (exceptionalFinal S Pv etaR) (fun T => Pv T j) (etaR / 4) hne hexc
  exact ⟨T, hT, by rwa [div_div] at hlt⟩

/-- **`09:1705--1706`, the donors chosen by a fixed exceptional node.**

"Some exceptional node `T_*` is chosen by at least `|J_good|/e_T` donors": the
set over which that count is taken.  A *derived* finite set -- the good donors
whose protected mass at `Tstar` clears the frozen threshold of `09:1705` -- and
not a carrier of any conclusion. -/
noncomputable def donorsHeavyAt (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) (Tstar : V) : Finset ι :=
  (goodDonors S Pv etaR).filter fun j =>
    etaR / (4 * ((exceptionalFinal S Pv etaR).card : ℝ)) < Pv Tstar j

/-- **Aux (membership readout).**  General. -/
theorem mem_donorsHeavyAt {S : RoutedSystem P Coord ι V r A0} {Pv : V → ι → ℝ}
    {etaR : ℝ} {Tstar : V} {j : ι} :
    j ∈ donorsHeavyAt S Pv etaR Tstar ↔
      j ∈ goodDonors S Pv etaR ∧
        etaR / (4 * ((exceptionalFinal S Pv etaR).card : ℝ)) < Pv Tstar j := by
  simp [donorsHeavyAt]

/-- **Aux (`09:1705`, "for each good donor").**  Chosen donors are good donors.
General. -/
theorem donorsHeavyAt_subset (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) (Tstar : V) : donorsHeavyAt S Pv etaR Tstar ⊆ goodDonors S Pv etaR :=
  Finset.filter_subset _ _

end HeavyNode

/-! ## §3  `09:1706--1707`: the node pigeonhole

"Some exceptional node `T_*` is chosen by at least `|J_good|/e_T` donors."

The averaging is the banked `WrapperMassRedistribution.exists_heavy_fibre`,
consumed by pin.  The choice function the frozen sentence names is built inside
the proof from §2 and then discarded: the conclusion speaks only about
`donorsHeavyAt`, so no declaration downstream depends on which node a donor
happened to choose. -/

section NodePigeonhole

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **`09:1705--1707`, the node pigeonhole at the routed system.**

From the `09:1701` endpoint at every good donor: some exceptional `T_*` is chosen
by at least `|J_good|/e_T` donors, written multiplicatively so that no division
by `e_T` occurs before `09:1730` has licensed it.  General. -/
theorem exists_common_exceptional_node (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ}
    (hne : (exceptionalFinal S Pv etaR).Nonempty)
    (hexc : ∀ j ∈ goodDonors S Pv etaR, etaR / 4 < exceptionalMass S Pv etaR j) :
    ∃ Tstar ∈ exceptionalFinal S Pv etaR,
      ((goodDonors S Pv etaR).card : ℝ)
        ≤ ((exceptionalFinal S Pv etaR).card : ℝ)
            * ((donorsHeavyAt S Pv etaR Tstar).card : ℝ) := by
  classical
  set E := exceptionalFinal S Pv etaR with hE
  set thr := etaR / (4 * (E.card : ℝ)) with hthr
  -- `09:1704--1705`: the frozen per-donor choice, produced by §2.
  have hpick : ∀ j ∈ goodDonors S Pv etaR, ∃ T, T ∈ E ∧ thr < Pv T j := by
    intro j hj
    obtain ⟨T, hT, hlt⟩ := exists_heavy_exceptional_node S Pv hne (hexc j hj)
    exact ⟨T, hT, hlt⟩
  obtain ⟨v0, hv0⟩ := hne
  set choice : ι → V := fun j =>
    if h : ∃ T, T ∈ E ∧ thr < Pv T j then h.choose else v0 with hchoice
  have hchoice_mem : ∀ j ∈ goodDonors S Pv etaR, choice j ∈ E := by
    intro j hj
    have h := hpick j hj
    simp only [hchoice, dif_pos h]
    exact h.choose_spec.1
  have hchoice_heavy : ∀ j ∈ goodDonors S Pv etaR, thr < Pv (choice j) j := by
    intro j hj
    have h := hpick j hj
    simp only [hchoice, dif_pos h]
    exact h.choose_spec.2
  -- `09:1706--1707`: the banked fibre pigeonhole.
  obtain ⟨t, ht, hfib⟩ :=
    exists_heavy_fibre (goodDonors S Pv etaR) choice E hchoice_mem ⟨v0, hv0⟩
  refine ⟨t, ht, ?_⟩
  have hsub : (goodDonors S Pv etaR).filter (fun j => choice j = t)
      ⊆ donorsHeavyAt S Pv etaR t := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [mem_donorsHeavyAt]
    refine ⟨hj.1, ?_⟩
    have := hchoice_heavy j hj.1
    rwa [hj.2] at this
  have hcard : (((goodDonors S Pv etaR).filter fun j => choice j = t).card : ℝ)
      ≤ ((donorsHeavyAt S Pv etaR t).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hEnn : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
  calc ((goodDonors S Pv etaR).card : ℝ)
      ≤ (E.card : ℝ) * (((goodDonors S Pv etaR).filter fun j => choice j = t).card : ℝ) :=
        hfib
    _ ≤ (E.card : ℝ) * ((donorsHeavyAt S Pv etaR t).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hEnn

end NodePigeonhole

/-! ## §4  `09:1707--1713`: the reservoir halving and `eq:wrapper-terminal-density`

"One common reservoir type accounts for at least half of those donors; for each
selected donor its density at `T_*` is at least `delta_0 = eta_R/(8 e_T mu_P)`."

Two independent halvings hide in that sentence and both are executed here:

* *across donors*, a common reservoir type is selected -- the same banked fibre
  pigeonhole run at the two-element type carrier (`exists_half_fibre`);
* *within a donor*, the frozen mass `> eta_R/(4 e_T)` is split between the two
  reservoirs of `09:1370--1373`, so the larger one carries at least half of it
  (`mass_halved_at_dominantReservoir`).  This is **derived** from the split, not
  assumed.

`delta_0` itself is the banked `WrapperMassRedistribution.deltaZero` and the
passage from "half the mass" to "density `delta_0`" is the banked
`deltaZero_of_pigeonhole`; neither is restated. -/

section Reservoirs

/-- **`09:1707--1708`, the reservoir-type pigeonhole, general.**

"One common reservoir type accounts for at least half of those donors."  Exactly
the banked `WrapperMassRedistribution.exists_heavy_fibre` at the two-element type
carrier: there are two protected reservoirs per outer coordinate
(`09:1370--1371`), so the fibre bound reads `|J| <= 2|fibre|`.  General in the
donor carrier. -/
theorem exists_half_fibre {κ : Type*} (J : Finset κ) (choice : κ → Bool) :
    ∃ ty : Bool, (J.card : ℝ) ≤ 2 * ((J.filter fun j => choice j = ty).card : ℝ) := by
  classical
  obtain ⟨ty, -, h⟩ :=
    exists_heavy_fibre J choice Finset.univ (fun j _ => Finset.mem_univ _)
      ⟨true, Finset.mem_univ _⟩
  exact ⟨ty, by simpa using h⟩

variable {ι V : Type*}

/-- **`09:1707--1708`, the reservoir type a donor is counted in.**

Of the two protected reservoirs of `09:1370--1373`, the one whose relative
density at the node is larger.  A *derived* index -- no conclusion is attached to
it, and the frozen "common type" is obtained from it by the pigeonhole above,
never by fiat. -/
noncomputable def dominantReservoir (dens : Bool → ι → V → ℝ) (j : ι) (T : V) : Bool :=
  if dens false j T ≤ dens true j T then true else false

/-- **Aux battery 1 (identity).**  The dominant reservoir attains the larger of
the two densities.  General; this is the *only* property of
`dominantReservoir` that anything below uses. -/
theorem dominantReservoir_attains_max (dens : Bool → ι → V → ℝ) (j : ι) (T : V) :
    dens (dominantReservoir dens j T) j T = max (dens true j T) (dens false j T) := by
  unfold dominantReservoir
  split_ifs with h
  · exact (max_eq_left h).symm
  · exact (max_eq_right (le_of_lt (not_le.mp h))).symm

/-- **`09:1370--1373` + `09:1708`, the within-donor halving, DERIVED.**

"Each outer coordinate contains two protected row reservoirs, each of mass
`mu_P`."  If the donor's protected mass at a node is at most the two reservoir
contributions `mu_P d_Sigma + mu_P d_D`, then the *larger* reservoir alone
carries at least half of it.  This is the step the frozen text compresses into
"one common reservoir type accounts for at least half"; the *common* half is the
pigeonhole above, this is the *per-donor* half.  General. -/
theorem mass_halved_at_dominantReservoir (dens : Bool → ι → V → ℝ) (j : ι) (T : V)
    {mass : ℝ} (hsplit : mass ≤ muP * dens true j T + muP * dens false j T) :
    mass / 2 ≤ muP * dens (dominantReservoir dens j T) j T := by
  have hmuP : 0 < muP := muP_pos
  have hmax := dominantReservoir_attains_max dens j T
  rw [hmax]
  rcases le_total (dens false j T) (dens true j T) with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

end Reservoirs

section Selected

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **`09:1708`, "those donors" of the common reservoir type.**

The chosen donors at `Tstar` whose dominant reservoir is the common type `ty`.
Derived from `donorsHeavyAt` by a `Bool` filter; carries no conclusion. -/
noncomputable def selectedDonors (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool) : Finset ι :=
  (donorsHeavyAt S Pv etaR Tstar).filter fun j => dominantReservoir dens j Tstar = ty

/-- **Aux (membership readout).**  General. -/
theorem mem_selectedDonors {S : RoutedSystem P Coord ι V r A0} {Pv : V → ι → ℝ}
    {etaR : ℝ} {dens : Bool → ι → V → ℝ} {Tstar : V} {ty : Bool} {j : ι} :
    j ∈ selectedDonors S Pv etaR dens Tstar ty ↔
      j ∈ donorsHeavyAt S Pv etaR Tstar ∧ dominantReservoir dens j Tstar = ty := by
  simp [selectedDonors]

/-- **Aux.**  Selected donors are chosen donors, hence good donors.  General. -/
theorem selectedDonors_subset (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool) :
    selectedDonors S Pv etaR dens Tstar ty ⊆ donorsHeavyAt S Pv etaR Tstar :=
  Finset.filter_subset _ _

/-- **Aux battery 2 (round-trip / partition).**

The two reservoir types partition the chosen donors exactly: the frozen "one
common reservoir type accounts for at least half of those donors" is a statement
about a genuine two-block partition, and nothing is lost or double counted.
General. -/
theorem selectedDonors_card_add (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    (etaR : ℝ) (dens : Bool → ι → V → ℝ) (Tstar : V) :
    (selectedDonors S Pv etaR dens Tstar true).card
        + (selectedDonors S Pv etaR dens Tstar false).card
      = (donorsHeavyAt S Pv etaR Tstar).card := by
  classical
  have hfalse : selectedDonors S Pv etaR dens Tstar false
      = (donorsHeavyAt S Pv etaR Tstar).filter
          fun j => ¬ (dominantReservoir dens j Tstar = true) := by
    unfold selectedDonors
    apply Finset.filter_congr
    intro j _
    simp
  rw [selectedDonors, hfalse]
  exact Finset.card_filter_add_card_filter_not _

/-- **`eq:wrapper-terminal-density` (`09:1708--1713`) at one selected donor.**

"for each selected donor its density at `T_*` is at least
`delta_0 = eta_R/(8 e_T mu_P)`."

The frozen chain, executed: membership in `selectedDonors` supplies the
`09:1705` mass bound `> eta_R/(4 e_T)`, the `09:1370--1373` split supplies the
halving through `mass_halved_at_dominantReservoir`, and the banked
`WrapperMassRedistribution.deltaZero_of_pigeonhole` turns half the mass into the
relative density `delta_0`.  `delta_0` is the banked `deltaZero`, consumed by
pin.  General. -/
theorem deltaZero_le_dens_of_selected (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool)
    {j : ι} (hetaR : 0 < etaR) (heT : 0 < (exceptionalFinal S Pv etaR).card)
    (hj : j ∈ selectedDonors S Pv etaR dens Tstar ty)
    (hsplit : Pv Tstar j ≤ muP * dens true j Tstar + muP * dens false j Tstar) :
    deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ dens ty j Tstar := by
  rw [mem_selectedDonors] at hj
  obtain ⟨hheavy, hdom⟩ := hj
  rw [mem_donorsHeavyAt] at hheavy
  have hhalf : Pv Tstar j / 2 ≤ muP * dens ty j Tstar := by
    have := mass_halved_at_dominantReservoir dens j Tstar hsplit
    rwa [hdom] at this
  exact deltaZero_of_pigeonhole hetaR heT hheavy.2 hhalf

/-- **THE ENDPOINT: `09:1702--1713` wired to the `09:1701` owner family.**

Given only the round-4 endpoint at every good donor (`hexc`, consumed by pin --
`OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization`) and
the frozen two-reservoir mass split of `09:1370--1373` (`hsplit`, GAP item M3),
the frozen pigeonhole paragraph is produced whole:

* the `e_T = 0` case of `09:1702` is discharged (`hne` is derived, not assumed);
* an exceptional node `T_*` and a common reservoir type `ty` exist;
* the frozen donor count `|J_good| <= 2 e_T |D_sel|` holds -- the multiplicative
  form of `09:1707`'s "at least `|J_good|/e_T` donors" halved by `09:1708`;
* every selected donor has density at least `delta_0` at `T_*`
  (`eq:wrapper-terminal-density`).

**Nothing beyond `09:1713` is claimed here.**  `eq:wrapper-u-dense` is concluded
nowhere, `hDenseRung` is neither discharged nor fed, and the Extension call of
`09:1746--1781` is not entered.  General. -/
theorem exists_terminal_star_and_reservoir (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} (dens : Bool → ι → V → ℝ)
    (hetaR : 0 < etaR)
    (hgood : (goodDonors S Pv etaR).Nonempty)
    (hexc : ∀ j ∈ goodDonors S Pv etaR, etaR / 4 < exceptionalMass S Pv etaR j)
    (hsplit : ∀ j ∈ goodDonors S Pv etaR, ∀ T ∈ exceptionalFinal S Pv etaR,
      Pv T j ≤ muP * dens true j T + muP * dens false j T) :
    ∃ Tstar ∈ exceptionalFinal S Pv etaR, ∃ ty : Bool,
      ((goodDonors S Pv etaR).card : ℝ)
          ≤ 2 * ((exceptionalFinal S Pv etaR).card : ℝ)
              * ((selectedDonors S Pv etaR dens Tstar ty).card : ℝ)
        ∧ ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty,
            deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ dens ty j Tstar := by
  classical
  obtain ⟨j0, hj0⟩ := hgood
  -- `09:1702`, executed.
  have hne : (exceptionalFinal S Pv etaR).Nonempty :=
    exceptionalFinal_nonempty_of_goodDonor S Pv hetaR (hexc j0 hj0)
  have heT : 0 < (exceptionalFinal S Pv etaR).card := Finset.card_pos.mpr hne
  -- `09:1705--1707`, the node pigeonhole.
  obtain ⟨Tstar, hTstar, hnode⟩ := exists_common_exceptional_node S Pv hne hexc
  -- `09:1707--1708`, the reservoir-type pigeonhole.
  obtain ⟨ty, htype⟩ :=
    exists_half_fibre (donorsHeavyAt S Pv etaR Tstar)
      (fun j => dominantReservoir dens j Tstar)
  refine ⟨Tstar, hTstar, ty, ?_, ?_⟩
  · have hEnn : (0 : ℝ) ≤ ((exceptionalFinal S Pv etaR).card : ℝ) := Nat.cast_nonneg _
    have hstep :
        ((exceptionalFinal S Pv etaR).card : ℝ) * ((donorsHeavyAt S Pv etaR Tstar).card : ℝ)
          ≤ ((exceptionalFinal S Pv etaR).card : ℝ)
              * (2 * ((selectedDonors S Pv etaR dens Tstar ty).card : ℝ)) :=
      mul_le_mul_of_nonneg_left htype hEnn
    calc ((goodDonors S Pv etaR).card : ℝ)
        ≤ ((exceptionalFinal S Pv etaR).card : ℝ)
            * ((donorsHeavyAt S Pv etaR Tstar).card : ℝ) := hnode
      _ ≤ ((exceptionalFinal S Pv etaR).card : ℝ)
            * (2 * ((selectedDonors S Pv etaR dens Tstar ty).card : ℝ)) := hstep
      _ = 2 * ((exceptionalFinal S Pv etaR).card : ℝ)
            * ((selectedDonors S Pv etaR dens Tstar ty).card : ℝ) := by ring
  · intro j hj
    have hjgood : j ∈ goodDonors S Pv etaR :=
      donorsHeavyAt_subset S Pv etaR Tstar (selectedDonors_subset S Pv etaR dens Tstar ty hj)
    exact deltaZero_le_dens_of_selected S Pv dens Tstar ty hetaR heT hj
      (hsplit j hjgood Tstar hTstar)

end Selected

/-! ## §5  `09:1742--1744`: the one step past the pigeonhole that the chain closes

"If `delta_0 >= 1`, the strict pigeonhole conclusion preceding
`eq:wrapper-terminal-density` is itself impossible.  We may therefore assume
`delta_0 < 1`, and hence `u_don >= 8s`."

The frozen alternative is not assumed away here: the endpoint of §4 produces a
*relative* density bounded by one, so `delta_0 <= 1` is a consequence of the
wired chain.  The passage to the frozen `u_don >= 8s` is then the banked
`WrapperMassRedistribution.uDon_ge_eight_s`, consumed by pin.

`u_don` is **not** identified with any accessor below.  It stays a bare
`{uDon : ℕ}` constrained only by the frozen defining demand of `09:1717--1718`
("`u_don` is the least power of two satisfying `u_don delta_0 >= 8s`"), and the
floor holds for *every* natural number meeting that inequality -- which is
strictly weaker, hence safe.  The banked `ParameterSchedule` least-power-of-two
accessor is **one such** value only once it is applied at `delta_0`: its own
frozen defining display is `06:726--728`, which fixes `u_term` against
`delta_term = eta_R / (8 mu_P max{1, E_T})`, a different quantity from
`delta_0 = eta_R / (8 e_T mu_P)`.  `09:1715--1716` relates the two only as the
schedule bound `u_don <= u_term`. -/

section TerminalFloor

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **The selected donor set is inhabited, DERIVED.**

If the endpoint's count holds and `J_good` is nonempty, then so is `D_sel`: an
empty selection would force `|J_good| <= 0`.  This is what makes `09:1742`'s
"the strict pigeonhole conclusion" available at an actual donor.  General. -/
theorem selectedDonors_nonempty_of_count (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (etaR : ℝ) (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool)
    (hgood : (goodDonors S Pv etaR).Nonempty)
    (hcount : ((goodDonors S Pv etaR).card : ℝ)
      ≤ 2 * ((exceptionalFinal S Pv etaR).card : ℝ)
          * ((selectedDonors S Pv etaR dens Tstar ty).card : ℝ)) :
    (selectedDonors S Pv etaR dens Tstar ty).Nonempty := by
  rw [← Finset.card_pos]
  by_contra hcon
  have hzero : (selectedDonors S Pv etaR dens Tstar ty).card = 0 := by omega
  rw [hzero, Nat.cast_zero, mul_zero] at hcount
  have hpos : 0 < (goodDonors S Pv etaR).card := Finset.card_pos.mpr hgood
  have hposR : (0 : ℝ) < ((goodDonors S Pv etaR).card : ℝ) := by exact_mod_cast hpos
  linarith

/-- **`09:1742--1744`, first half: `delta_0 <= 1`, DERIVED.**

"If `delta_0 >= 1`, the strict pigeonhole conclusion preceding
`eq:wrapper-terminal-density` is itself impossible."  A relative density never
exceeds one, and the endpoint puts `delta_0` below the density of an actual
selected donor -- so the frozen alternative is discharged from the chain.
General. -/
theorem deltaZero_le_one_of_selected (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool)
    (hsel : (selectedDonors S Pv etaR dens Tstar ty).Nonempty)
    (hdelta : ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty,
      deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ dens ty j Tstar)
    (hdens1 : ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty, dens ty j Tstar ≤ 1) :
    deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ 1 := by
  obtain ⟨j, hj⟩ := hsel
  exact le_trans (hdelta j hj) (hdens1 j hj)

/-- **`09:1744`, "and hence `u_don >= 8s`", at the terminal node.**

The frozen floor, reached from the wired chain rather than from a case
assumption: `hdef` is the defining demand of `u_don` (`09:1717--1718`,
"`u_don` is the least power of two satisfying `u_don delta_0 >= 8s`"), the
density bound comes from §4, and the arithmetic is the banked
`WrapperMassRedistribution.uDon_ge_eight_s`.

**Citation, corrected this round (R-2).**  `06:726--728` of
`eq:terminal-uniform-bounds` defines `u_term` against
`delta_term = eta_R/(8 mu_P max{1, E_T})` -- a *different* quantity of a
*different* display -- and is therefore **not** a defining display for `u_don`.
It is cited nowhere in this module's `u_don` leg.  The only frozen definition of
`u_don` is `09:1717--1718`, taken at `delta_0`; the two searches are connected
only by the schedule's relational bound `u_don <= u_term` (`09:1715--1716`).
General. -/
theorem terminal_uDon_floor (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool)
    {s uDon : ℕ}
    (hsel : (selectedDonors S Pv etaR dens Tstar ty).Nonempty)
    (hdelta : ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty,
      deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ dens ty j Tstar)
    (hdens1 : ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty, dens ty j Tstar ≤ 1)
    (hdef : 8 * (s : ℝ)
      ≤ (uDon : ℝ) * deltaZero etaR (exceptionalFinal S Pv etaR).card) :
    8 * s ≤ uDon :=
  uDon_ge_eight_s (deltaZero_le_one_of_selected S Pv dens Tstar ty hsel hdelta hdens1) hdef

/-- **The wired chain in one term: `09:1701` to `09:1744`.**

The seam test for this round.  From the round-4 endpoint (`hexc`) and the frozen
`09:1370--1373` mass split (`hsplit`) alone, with the relative-density bound
that makes `dens` a density at all, the frozen `u_don >= 8s` of `09:1744`
follows -- travelling through `09:1702` (the `e_T = 0` contradiction),
`09:1704--1707` (the two pigeonholes), `eq:wrapper-terminal-density`
(`09:1710--1713`) and `09:1742--1744`.  No intermediate binder is re-introduced
on the way: `T_*`, `ty`, `e_T > 0`, `D_sel` nonempty and `delta_0 <= 1` are all
produced inside this proof term.

`hdef` is the *defining* demand of `u_don` -- "the least power of two satisfying
`u_don delta_0 >= 8s`" (`09:1717--1718`) read at `delta_0` -- and not a chosen
bound.  `06:726--728` is **not** cited (R-2): that display defines `u_term`
against `delta_term`, and only the relation `u_don <= u_term` (`09:1715--1716`)
connects the two searches.

`u_don` itself is not redefined here and is not an accessor call either (R-3):
it is a bare `{uDon : ℕ}` binder, i.e. *any* natural number meeting the frozen
defining demand, of which the banked `ParameterSchedule` least-power-of-two
accessor is one.  The statement is strictly *stronger* for this, and the shape
is inherited from the banked `uDon_ge_eight_s`.  Free `s` likewise: §5b's
`uDon_floor_of_realization` is the form in which `s` is identified with the
telescope's global slot parameter, as `09:1717--1718` does.

**Still nothing beyond `09:1744`.**  The projection cover, the coordinate
extraction, the block supply and the Extension call of `09:1746--1781` are the
reach-goal residue L3--L5 and are not entered.  General. -/
theorem uDon_floor_of_owner_family (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} (dens : Bool → ι → V → ℝ) {s uDon : ℕ}
    (hetaR : 0 < etaR)
    (hgood : (goodDonors S Pv etaR).Nonempty)
    (hexc : ∀ j ∈ goodDonors S Pv etaR, etaR / 4 < exceptionalMass S Pv etaR j)
    (hsplit : ∀ j ∈ goodDonors S Pv etaR, ∀ T ∈ exceptionalFinal S Pv etaR,
      Pv T j ≤ muP * dens true j T + muP * dens false j T)
    (hdens1 : ∀ (b : Bool) (j : ι) (T : V), dens b j T ≤ 1)
    (hdef : 8 * (s : ℝ)
      ≤ (uDon : ℝ) * deltaZero etaR (exceptionalFinal S Pv etaR).card) :
    8 * s ≤ uDon := by
  obtain ⟨Tstar, -, ty, hcount, hdelta⟩ :=
    exists_terminal_star_and_reservoir S Pv dens hetaR hgood hexc hsplit
  exact terminal_uDon_floor S Pv dens Tstar ty
    (selectedDonors_nonempty_of_count S Pv etaR dens Tstar ty hgood hcount)
    hdelta (fun j _ => hdens1 ty j Tstar) hdef

end TerminalFloor

/-! ## §5b  `09:1700--1701` DISCHARGED: the round-4 endpoint applied, not restated

**This is the wiring gate of this round, and the reason the module exists.**

§1--§5 above are stated generally, and each takes the round-4 conclusion as the
explicit hypothesis

  `hexc : forall j in J_good, eta_R/4 < exceptionalMass S Pv eta_R j`

which is exactly `09:1700--1701` quantified over `J_good`.  Carrying only that
hypothesis would leave the module's contact with round 4 a *restatement*: the
banked endpoint would be named in prose and applied nowhere.  This section
removes the hypothesis from the chain by **applying** the banked

  `OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization`

once at every member of `J_good`, under the realization telescope of
`09:1661--1669`.  `OwnerIndexedTransferFamily` therefore occurs in actual proof
terms below, and the endpoints of §4 and §5 are re-expressed through it.

**The telescope is reproduced exactly as the banked endpoint states it**, with
the single change the frozen text itself makes: every hypothesis that mentions
the distinguished donor `j` -- and only those -- is quantified as
`forall j in J_good, ...` and used at that `j`.  Nothing is strengthened.  In
particular a premise about `i in J_good.erase j` is **not** promoted to a premise
about `i in J_good`: that would be a strictly stronger demand than the banked
endpoint makes, and an over-strong hypothesis typechecks perfectly.  `hleaves` is
`eq:wrapper-mass-leaves-owner` (`09:1611--1615`), whose frozen display already
prints the side condition `(j in J_good)`, so quantifying it over `J_good` *is*
the display; `hownerSplit` is the owner-side reservoir split of `09:1643--1646`
(the banked endpoint's `hsplit`, renamed here only to keep it distinct from the
`09:1370--1373` split of §4).

**The general forms of §1--§5 are kept alongside** and are unchanged.  They are
the weaker interface: a consumer that obtains `hexc` by some other route may
still use them, and keeping both is what lets the seam be inspected.  What this
section removes is the possibility of banking the module with `hexc` as its only
contact with round 4. -/

section Wiring

open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.TwoStreamState
open EthInapproximability.ParameterizedNP.TerminalStateRealization
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open NPCC

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
  [Fintype Rone] [DecidableEq Rone]

/-- **THE WIRING DECLARATION: `09:1700--1701` at every good donor, DERIVED.**

"Together with `eq:wrapper-mass-leaves-owner`, this says that every good donor
sends more than `eta_R/4` protected mass to exceptional final nodes."

The banked `OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization`
proves that sentence at *one* good donor from the realization data of
`09:1661--1669`.  Here it is applied at every member of `J_good`, producing the
family that §1--§5 carried as the hypothesis `hexc`.  The proof term is one
`intro` and one application of the banked endpoint -- the whole content of the
declaration is the binder bookkeeping, which is exactly what "consumed by pin"
has to mean.

Every hypothesis below is byte-for-byte the banked endpoint's own hypothesis;
the `j`-dependent ones are quantified over `J_good` and instantiated at the
intro'd `j`.  No hypothesis is added, none is strengthened, and none restates a
derived telescope.  General. -/
theorem goodDonorFamily_exceptionalMass_of_realization
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ)
    (pOrd pFor : Slot s) (Pstar : ιc → Finset (Cl × Cl))
    (Rbin : ιc → Slot s → Finset Ltwo)
    (selRow : ιc → Slot s × Ltwo → (Slot (scaleAlignWidth rq) → Cl))
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rq A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth rq) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ ((scaleAlignWidth rq : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR,
      ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG ≤ etaR / (8 * g))
    (hOuter : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      OwnerIndexedTransferFamily.donorCoord S i
        ≠ OwnerIndexedTransferFamily.donorCoord S j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      (streamRows XZ (OwnerIndexedTransferFamily.donorCoord S i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ,
        w (OwnerIndexedTransferFamily.donorCoord S i) = yp.1
          ∧ w (OwnerIndexedTransferFamily.donorCoord S j) = yp.2)
    (hPairDensity : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (OwnerIndexedTransferFamily.donorCoord S i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (OwnerIndexedTransferFamily.donorCoord S i)) = l)
    (hSelDist : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (OwnerIndexedTransferFamily.donorCoord S i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rq - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hownerSplit : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (OwnerIndexedTransferFamily.donorCoord S j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (OwnerIndexedTransferFamily.donorCoord S j) RD).card : ℝ)
              / (RD.card : ℝ)))
    (hleaves : ∀ j ∈ goodDonors S Pv etaR, etaR / 2 < ownerLeakage S Pv j) :
    ∀ j ∈ goodDonors S Pv etaR, etaR / 4 < exceptionalMass S Pv etaR j := by
  intro j hj
  exact OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization
    W rq s mT dT dOrd bcap r₃ bT Lh vmax Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta
    XZ YZ dF eps2 epsProd xT yy pOrd pFor Pstar Rbin selRow S Pv huniq hj hetaR hg hgates
    hcard hdeficit (hOuter j hj) hbins htemplate_card htemplate_regular hStwo hNval
    (hOrdNe j hj) hRGpos hRegG hdOrd hRegF hdF (hPstarTyped j hj) (hPstarProj j hj)
    (hPairDensity j hj) (hRbinCard j hj) (hSelRowMem j hj) (hSelRowTyped j hj)
    (hSelDist j hj) hEps2 hxT hSelectorGate (hTTS j hj) hs hxTd hyy hseed hfixed hcalls
    hC hcost hcomp iotaA iotaB (hrow j hj) (hgame j hj) (hownerSplit j hj) (hleaves j hj)

/-- **`09:1701--1713` from the realization data: §4's endpoint, wired.**

`exists_terminal_star_and_reservoir` with its `hexc` binder **removed**: the
round-4 endpoint is now produced inside the proof term by
`goodDonorFamily_exceptionalMass_of_realization`, i.e. by applying the banked
`OwnerIndexedTransferFamily.goodDonor_mass_to_exceptional_of_realization` at
every good donor.  The conclusion is byte-for-byte §4's -- an exceptional node
`T_*`, a common reservoir type, the frozen donor count of `09:1707--1708` and
`eq:wrapper-terminal-density` at every selected donor.

What remains a binder is exactly what round 5 never had a source for: `hgood`
(`|J_good| > 0`, whose frozen derivation `09:1719--1741` is GAP item 5) and
`hsplit`, the `09:1370--1373` two-reservoir split at exceptional nodes (GAP item
M3).  Note that `hsplit` here and `hownerSplit` in the telescope are *different*
frozen sentences: `hsplit` splits a donor's mass at an **exceptional** node
(`09:1370--1373` read at `T`), `hownerSplit` is the **owner**-side transfer
sentence of `09:1643--1646` that the banked endpoint consumes.

**Still nothing beyond `09:1713`.**  General. -/
theorem exists_terminal_star_and_reservoir_of_realization
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ)
    (pOrd pFor : Slot s) (Pstar : ιc → Finset (Cl × Cl))
    (Rbin : ιc → Slot s → Finset Ltwo)
    (selRow : ιc → Slot s × Ltwo → (Slot (scaleAlignWidth rq) → Cl))
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rq A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} (dens : Bool → ιc → Vn → ℝ)
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth rq) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ ((scaleAlignWidth rq : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR,
      ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG ≤ etaR / (8 * g))
    (hOuter : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      OwnerIndexedTransferFamily.donorCoord S i
        ≠ OwnerIndexedTransferFamily.donorCoord S j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      (streamRows XZ (OwnerIndexedTransferFamily.donorCoord S i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ,
        w (OwnerIndexedTransferFamily.donorCoord S i) = yp.1
          ∧ w (OwnerIndexedTransferFamily.donorCoord S j) = yp.2)
    (hPairDensity : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (OwnerIndexedTransferFamily.donorCoord S i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (OwnerIndexedTransferFamily.donorCoord S i)) = l)
    (hSelDist : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (OwnerIndexedTransferFamily.donorCoord S i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rq - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hownerSplit : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (OwnerIndexedTransferFamily.donorCoord S j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (OwnerIndexedTransferFamily.donorCoord S j) RD).card : ℝ)
              / (RD.card : ℝ)))
    (hleaves : ∀ j ∈ goodDonors S Pv etaR, etaR / 2 < ownerLeakage S Pv j)
    (hgood : (goodDonors S Pv etaR).Nonempty)
    (hsplit : ∀ j ∈ goodDonors S Pv etaR, ∀ T ∈ exceptionalFinal S Pv etaR,
      Pv T j ≤ muP * dens true j T + muP * dens false j T) :
    ∃ Tstar ∈ exceptionalFinal S Pv etaR, ∃ ty : Bool,
      ((goodDonors S Pv etaR).card : ℝ)
          ≤ 2 * ((exceptionalFinal S Pv etaR).card : ℝ)
              * ((selectedDonors S Pv etaR dens Tstar ty).card : ℝ)
        ∧ ∀ j ∈ selectedDonors S Pv etaR dens Tstar ty,
            deltaZero etaR (exceptionalFinal S Pv etaR).card ≤ dens ty j Tstar :=
  exists_terminal_star_and_reservoir S Pv dens hetaR hgood
    (goodDonorFamily_exceptionalMass_of_realization W rq s mT dT dOrd bcap r₃ bT Lh vmax
      Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd
      pFor Pstar Rbin selRow S Pv huniq hetaR hg hgates hcard hdeficit hOuter hbins
      htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd hRegF hdF
      hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist
      hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls hC hcost hcomp iotaA
      iotaB hrow hgame hownerSplit hleaves)
    hsplit

/-- **`09:1701` to `09:1744` in one proof term from the realization data.**

`uDon_floor_of_owner_family` with its `hexc` binder **removed**: the seam this
tranche exists to close, now travelled end to end from the realization telescope
of `09:1661--1669` to the frozen floor `u_don >= 8s` of `09:1744`, with the
round-4 endpoint *applied* rather than assumed.  With `hexc` as a hypothesis the
general form carried only `09:1702 -> 09:1744`, because `09:1701` **was** its
hypothesis; this form carries `09:1701 -> 09:1744`.

**The `s` of `hdef` is the telescope's `s`, not a fresh binder.**  `09:1717--1718`
reads "`u_don` is the least power of two satisfying `u_don delta_0 >= 8s`", and
that `s` is the same global slot parameter the realization telescope carries
(`hs : s = 2 ^ r_3`).  The general `terminal_uDon_floor` and
`uDon_floor_of_owner_family` leave `s` free, which is strictly weaker; wiring
identifies it, as the frozen text does.

`u_don` itself stays a bare `{uDon : ℕ}` constrained only by `hdef`: the frozen
demand of `09:1717--1718` is an inequality about `u_don` at `delta_0`, and the
floor holds for *every* natural number meeting it -- the banked
`ParameterSchedule` least-power-of-two accessor being one such.  **General.** -/
theorem uDon_floor_of_realization
    {Xa Yb : Type*} {ιc Vn : Type*} {Pr : Protocol Xa Yb Bool} {A0 : ℕ}
    [Fintype Vn] [DecidableEq Vn] [Fintype ιc] [DecidableEq ιc]
    (W : StageTwoRelaxed.StageTwoWidths)
    (rq s mT dT dOrd bcap r₃ bT Lh vmax : ℕ)
    (Nmat : Rw → Cl → Bool) (Mmat : Cone → Rone → Bool)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (tup : Om → Slot s → Slot W.q₂ × Cone)
    (YT : Slot s → Finset Cl) (zeta : Slot s → Cl → Ltwo)
    (XZ : Finset (Slot (scaleAlignWidth rq) × Rw))
    (YZ : Finset (Slot (scaleAlignWidth rq) → Cl))
    (dF : Finset Rw → ℕ)
    (eps2 epsProd xT yy : ℝ)
    (pOrd pFor : Slot s) (Pstar : ιc → Finset (Cl × Cl))
    (Rbin : ιc → Slot s → Finset Ltwo)
    (selRow : ιc → Slot s × Ltwo → (Slot (scaleAlignWidth rq) → Cl))
    (S : RoutedSystem Pr (Slot (scaleAlignWidth rq)) ιc Vn rq A0)
    (Pv : Vn → ιc → ℝ) {etaR g : ℝ} (dens : Bool → ιc → Vn → ℝ) {uDon : ℕ}
    (huniq : ∀ v : Vn, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1)
    (hetaR : 0 < etaR) (hg : 0 < g)
    (hgates : wrapperOwnerGates (scaleAlignWidth rq) W.q₂ etaR g W.b₁)
    (hcard : ((goodDonors S Pv etaR).card : ℝ) ≤ ((scaleAlignWidth rq : ℕ) : ℝ))
    (hdeficit : ∑ i ∈ goodDonors S Pv etaR,
      ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG ≤ etaR / (8 * g))
    (hOuter : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      OwnerIndexedTransferFamily.donorCoord S i
        ≠ OwnerIndexedTransferFamily.donorCoord S j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot W.q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (yc : Cl), yc ∈ YT p → ∀ rw : Rw,
      Nmat rw yc = Stwo (zeta p yc) (tup (omg rw) p))
    (hOrdNe : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      (streamRows XZ (OwnerIndexedTransferFamily.donorCoord S i) RG).Nonempty)
    (hRGpos : 0 < RG.card)
    (hRegG : RegularOn RG (fun rw => tup (omg rw)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) →
      RegularOn Rf (fun rw => tup (omg rw) pFor) (dF Rf))
    (hdF : ∀ Rf : Finset Rw, (Rf = RSig ∨ Rf = RD) → 0 < dF Rf)
    (hPstarTyped : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, yp.1 ∈ YT pOrd ∧ yp.2 ∈ YT pFor)
    (hPstarProj : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ yp ∈ Pstar i, ∃ w ∈ YZ,
        w (OwnerIndexedTransferFamily.donorCoord S i) = yp.1
          ∧ w (OwnerIndexedTransferFamily.donorCoord S j) = yp.2)
    (hPairDensity : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      aMin rhoPair (templateDensity YT) ≤ ((Pstar i).card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin i p).card)
    (hSelRowMem : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p, selRow i (p, l) ∈ YZ)
    (hSelRowTyped : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ p : Slot s, ∀ l ∈ Rbin i p,
        selRow i (p, l) (OwnerIndexedTransferFamily.donorCoord S i) ∈ YT p
          ∧ zeta p (selRow i (p, l) (OwnerIndexedTransferFamily.donorCoord S i)) = l)
    (hSelDist : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ l ∈ Rbin i pOrd, ∃ yp ∈ Pstar i,
        selRow i (pOrd, l) (OwnerIndexedTransferFamily.donorCoord S i) = yp.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2)
    (hTTS : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      TerminalTwoStream.TerminalTwoStream W (scaleAlignWidth rq) s mT dT bcap r₃ bT Lh
        vmax Nmat Mmat cFam Stwo RG RSig RD omg (fun p o => tup o p) YT zeta XZ YZ
        (templateDensity YT) eps2 epsProd xT yy
        (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
        (ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)))
    (hs : s = 2 ^ r₃) (hxTd : xT = DenseStageFourOpening.xTdepth bT) (hyy : yy = 3 / 5)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT yy)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ →
      W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂
        (DenseWeightedCount.stoppingCapacity W.r₂ d))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃)
    (hcost : Pr.cost ≤ TerminalTwoStream.terminalTarget bcap W.r₂ r₃ + rq - 1)
    {gamb : Xa → Yb → Bool} (hcomp : Protocol.Computes Pr gamb)
    (iotaA : ιc → {a // a ∈ XZ} → Xa) (iotaB : ιc → {b // b ∈ YZ} → Yb)
    (hrow : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a, RouteRows Pr (S.node (S.owner i)) (iotaA i a))
    (hgame : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      ∀ a b, subgame (wrapperU Nmat rq) XZ YZ a b = gamb (iotaA i a) (iotaB i b))
    (hownerSplit : ∀ j ∈ goodDonors S Pv etaR, ∀ i ∈ (goodDonors S Pv etaR).erase j,
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
          ≤ Pv (S.owner i) j →
      2 * muP * ownerThreshold W.q₂ W.b₁
          (ordinaryDeficit XZ (OwnerIndexedTransferFamily.donorCoord S i) RG)
        ≤ muP * (((streamRows XZ (OwnerIndexedTransferFamily.donorCoord S j) RSig).card : ℝ)
              / (RSig.card : ℝ))
          + muP * (((streamRows XZ (OwnerIndexedTransferFamily.donorCoord S j) RD).card : ℝ)
              / (RD.card : ℝ)))
    (hleaves : ∀ j ∈ goodDonors S Pv etaR, etaR / 2 < ownerLeakage S Pv j)
    (hgood : (goodDonors S Pv etaR).Nonempty)
    (hsplit : ∀ j ∈ goodDonors S Pv etaR, ∀ T ∈ exceptionalFinal S Pv etaR,
      Pv T j ≤ muP * dens true j T + muP * dens false j T)
    (hdens1 : ∀ (b : Bool) (j : ιc) (T : Vn), dens b j T ≤ 1)
    (hdef : 8 * (s : ℝ)
      ≤ (uDon : ℝ) * deltaZero etaR (exceptionalFinal S Pv etaR).card) :
    8 * s ≤ uDon :=
  uDon_floor_of_owner_family S Pv dens hetaR hgood
    (goodDonorFamily_exceptionalMass_of_realization W rq s mT dT dOrd bcap r₃ bT Lh vmax
      Nmat Mmat cFam Stwo RG RSig RD omg tup YT zeta XZ YZ dF eps2 epsProd xT yy pOrd
      pFor Pstar Rbin selRow S Pv huniq hetaR hg hgates hcard hdeficit hOuter hbins
      htemplate_card htemplate_regular hStwo hNval hOrdNe hRGpos hRegG hdOrd hRegF hdF
      hPstarTyped hPstarProj hPairDensity hRbinCard hSelRowMem hSelRowTyped hSelDist
      hEps2 hxT hSelectorGate hTTS hs hxTd hyy hseed hfixed hcalls hC hcost hcomp iotaA
      iotaB hrow hgame hownerSplit hleaves)
    hsplit hdens1 hdef

end Wiring

/-! ## §6  Statement poles

A green build sees none of this.  Each item shows either that a hypothesis kept
above is genuinely needed, or that a step taken above is not the trivial one. -/

section Poles

/-- **Pole 1: `exists_heavy_member` genuinely needs the strict hypothesis.**

At a flat family the sum equals `c` exactly and *no* member exceeds the average,
so weakening `c < sum` to `c <= sum` would make the frozen `09:1705` choice
unavailable.  Exhibited at the two-point carrier with the family constant `1/2`
and `c = 1`.

**Self-chosen values, NO legality claimed.**  This is a rejection probe about the
general averaging lemma; `1/2` and `1` are not paper quantities and are not
offered as any. -/
theorem heavy_member_needs_strict_sum :
    (∑ _v ∈ (Finset.univ : Finset Bool), (1 / 2 : ℝ)) = 1
      ∧ ∀ v ∈ (Finset.univ : Finset Bool),
          ¬ ((1 : ℝ) / ((Finset.univ : Finset Bool).card : ℝ) < (1 / 2 : ℝ)) := by
  constructor
  · simp
  · intro v _
    simp

/-- **Pole 2: the dominance rule may not be replaced by a fixed reservoir type.**

`09:1708`'s "one common reservoir type accounts for at least half" is a
*selection*, not a convention: if the first reservoir is always taken, the
halving fails outright.  Exhibited with all the mass in the second reservoir --
`mass = mu_P`, `d_true = 0`, `d_false = 1` -- where the split hypothesis of
`mass_halved_at_dominantReservoir` holds but `mass/2 <= mu_P * d_true` is false.

**Self-chosen values, NO legality claimed** -- a rejection probe on the shape of
the halving step. -/
theorem halving_needs_the_dominant_type :
    muP ≤ muP * (0 : ℝ) + muP * (1 : ℝ) ∧ ¬ (muP / 2 ≤ muP * (0 : ℝ)) := by
  have hmuP : 0 < muP := muP_pos
  constructor
  · linarith
  · intro h
    rw [mul_zero] at h
    linarith

/-- **Pole 3: the produced density bound is not the empty bound.**

`eq:wrapper-terminal-density` is a *positive* threshold at every legal
`e_T >= 1`, so the endpoint's second clause refutes the zero-density family
outright: no selected donor may have density zero in the common reservoir at
`T_*`.  Were `delta_0` allowed to be zero the whole `09:1746--1781` Extension
call would carry no information.  The positivity is the banked
`WrapperMassRedistribution.deltaZero_pos`, consumed by pin.  General. -/
theorem terminalDensity_refutes_zero {etaR : ℝ} {eT : ℕ} (hetaR : 0 < etaR)
    (heT : 0 < eT) : ¬ (deltaZero etaR eT ≤ 0) :=
  not_le.mpr (deltaZero_pos hetaR heT)

/-- **Pole 4: `e_T = 0` is genuinely impossible, not merely excluded.**

`09:1702` reads "If `e_T = 0`, this is already a contradiction", and the
contradiction is real: over an empty exceptional set the mass is exactly zero,
which never exceeds `eta_R/4` at a positive `eta_R`.  Stated generally over the
mass family so that no wrapper datum enters. -/
theorem emptyExceptional_refutes_endpoint {κ : Type*} (mss : κ → ℝ) {etaR : ℝ}
    (hetaR : 0 < etaR) : ¬ (etaR / 4 < ∑ v ∈ (∅ : Finset κ), mss v) := by
  simp
  linarith

/-- **Pole 5: the node pigeonhole needs `e_T > 0` and not merely `e_T >= 0`.**

Division by `e_T` is illegal at `e_T = 0`, which is why `09:1707`'s
"`|J_good|/e_T` donors" is carried multiplicatively above.  Here is the price of
the other convention: at `e_T = 0` the frozen threshold `eta_R/(4 e_T)` collapses
to zero in Lean's total division, so *every* donor would count as chosen and the
frozen strict count would say nothing.  General; a rejection probe on the
formalization choice, claiming no legality. -/
theorem threshold_collapses_at_zero_count (etaR : ℝ) :
    etaR / (4 * ((0 : ℕ) : ℝ)) = 0 := by
  simp

end Poles

/-! ## §7  Aux-lemma battery

General properties of the three definitions introduced above.  Battery members 1
and 2 are stated in §4 next to the definitions they test; the remaining ones are
here. -/

section BatteryGeneral

/-- **Aux battery 3 (monotonicity).**  `eq:wrapper-terminal-density` is antitone
in the exceptional count: more exceptional nodes means a weaker per-donor density
demand.  This is the direction `09:1715--1716`'s `e_T <= E_T` is used in, and it
is why the schedule may replace `e_T` by its majorant.

**The positivity hypothesis is load-bearing and is not decoration.**  At `a = 0`
the frozen `delta_0 = eta_R/(8 e_T mu_P)` is Lean's total division by zero, so
`deltaZero etaR 0 = 0` and the antitone statement is *false* against any positive
`b`.  That is exactly why `09:1704` opens with "assume then that `e_T > 0`" and
why §1 derives it rather than assuming it.  General. -/
theorem deltaZero_antitone_count {etaR : ℝ} (hetaR : 0 ≤ etaR) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) : deltaZero etaR b ≤ deltaZero etaR a := by
  have hmuP : 0 < muP := muP_pos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hle : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hbR : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le haR hle
  have hda : (0 : ℝ) < 8 * (a : ℝ) * muP := by positivity
  have hdb : (0 : ℝ) < 8 * (b : ℝ) * muP := by positivity
  unfold deltaZero
  rw [div_le_div_iff₀ hdb hda]
  nlinarith [mul_nonneg hetaR
    (mul_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ)) (le_of_lt hmuP))]

/-- **Aux battery 4 (monotonicity in the threshold).**

Lowering the frozen threshold of `09:1705` can only enlarge the chosen-donor set
at a fixed node.  Stated over an arbitrary donor set and an arbitrary mass family
so that no derived wrapper datum is silently held fixed on one side only.
General.  (Stated over an abstract donor set and mass family, because the two
derived sets `donorsHeavyAt` refers to -- `J_good` and the exceptional count --
both move with `eta_R`; holding them fixed on one side only would be a false
monotonicity statement about `donorsHeavyAt` itself.) -/
theorem heavyAt_filter_mono_threshold {ι V : Type*} {J : Finset ι}
    {thr thr' : ℝ} {Pv : V → ι → ℝ} {Tstar : V} (h : thr ≤ thr') :
    (J.filter fun j => thr' < Pv Tstar j) ⊆ (J.filter fun j => thr < Pv Tstar j) := by
  classical
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_le_of_lt h hj.2⟩

/-- **Aux battery 5 (identity / round-trip on the reservoir index).**

At the degenerate reservoir family, where both reservoirs carry the same density,
the dominant choice is `true` and the halving reduces to the frozen split with
`d_Sigma = d_D`.  A round-trip test: the derived selection does not secretly
depend on which of two equal reservoirs it is handed.  General. -/
theorem dominantReservoir_of_equal {ι V : Type*} (d : ι → V → ℝ) (j : ι) (T : V) :
    dominantReservoir (fun _ => d) j T = true := by
  unfold dominantReservoir
  simp

end BatteryGeneral

section Battery

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **Aux battery 6 (containment).**  Every selected donor is a good donor: the
two filters above never leave `J_good`.  General. -/
theorem selectedDonors_subset_goodDonors (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) (etaR : ℝ) (dens : Bool → ι → V → ℝ) (Tstar : V) (ty : Bool) :
    selectedDonors S Pv etaR dens Tstar ty ⊆ goodDonors S Pv etaR :=
  subset_trans (selectedDonors_subset S Pv etaR dens Tstar ty)
    (donorsHeavyAt_subset S Pv etaR Tstar)

/-- **Aux battery 7 (pointwise readout of the wired family).**

`09:1701` says "*every* good donor sends more than `eta_R/4` ...", so the object
§5b produces is a **pointwise family over `J_good`**, not an aggregate about
`J_good`.  This lemma is that reading: the family fires at any named good donor
and returns exactly the banked endpoint's own conclusion at that donor, with no
averaging and no side condition.  Together with battery 8 it is the round-trip
test on the quantification `§5b` performs.

It is deliberately stated about the *shape* `forall j in J_good, ...` rather
than about `goodDonorFamily_exceptionalMass_of_realization` itself, so that it
tests the encoding and not one call site.  General. -/
theorem goodDonorFamily_at_member (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} {j : ι}
    (hfam : ∀ i ∈ goodDonors S Pv etaR, etaR / 4 < exceptionalMass S Pv etaR i)
    (hj : j ∈ goodDonors S Pv etaR) :
    etaR / 4 < exceptionalMass S Pv etaR j :=
  hfam j hj

/-- **Aux battery 8 (the wired family restricts).**

The other half of the round trip: a pointwise family over `J_good` restricts to
every subset of `J_good` -- in particular to `donorsHeavyAt` and to
`selectedDonors`, which is how §3 and §4 consume it.  An *aggregate* encoding of
`09:1701` (a bound on a sum over `J_good`, say) would **not** satisfy this, so
the lemma genuinely discriminates the encoding rather than decorating it.
General. -/
theorem goodDonorFamily_restricts (S : RoutedSystem P Coord ι V r A0)
    (Pv : V → ι → ℝ) {etaR : ℝ} {J : Finset ι} (hsub : J ⊆ goodDonors S Pv etaR)
    (hfam : ∀ i ∈ goodDonors S Pv etaR, etaR / 4 < exceptionalMass S Pv etaR i) :
    ∀ i ∈ J, etaR / 4 < exceptionalMass S Pv etaR i :=
  fun i hi => hfam i (hsub hi)

end Battery

/-! ## §8  Hypothesis consistency for the endpoint

**NON-FIDELITY / BEYOND-PAPER AUDIT.**  The paper's own instance of this block is
the exceptional frontier of the routed certificate system of the *alleged shallow
protocol*, which is unbuilt (reach-goal residue L1); the canonical-inhabitation
obligation for it is registered in the ledger row and is **not** discharged by
anything below.  What follows fires the *whole* hypothesis bundle of
`exists_terminal_star_and_reservoir` at the banked
`FirstBobFrontierInstance.liveSystem`, at a point chosen so that no clause is
satisfied vacuously: `|J_good| = 1`, `e_T = 1`, both reservoirs are present, and
the frozen mass split of `09:1370--1373` holds **with equality**.  The bundle is
therefore demonstrably non-contradictory -- and that is all this section claims.

**Self-chosen quantities, named explicitly.**  Two values are ours and neither is
legal:

* `probeTerminalMass`, standing in for `P_v` -- the routing's output on the
  protected reservoirs, which is GAP item 3 of the header;
* `eta_R = 1/100`.  `eta_R` is DEFINED by `eq:eta-choice` (`06:206--217`), whose
  **first branch** `eta_R <= (1/2)(mu_Sigma/100)` (`06:212--217`), read with
  `mu_Sigma = 1/184` from `eq:fixed-protected-masses` (`06:133`), already forces
  `eta_R <= mu_Sigma/200 = 1/36800`, so `1/100` is illegal by a wide margin.
  (Attribution corrected this round, R-5: `06:228`'s
  `0 < eta_R <= eta_C/2 < tau < x_N` supplies positivity and the ordering only,
  and is not the source of the numeric bound.)  It
  is chosen only so that the frozen threshold `eta_R/4` sits below the one
  protected-reservoir mass `mu_P = 1/184` that the probe can carry, which is the
  regime the paper itself works in.

`mu_P = 1/184` by contrast is DEFINED (`09:1370--1373`) and consumed **by pin**
from `WrapperProtectedEarly.muP`, never as a numeral; the live protocol, `r = 2`,
`A_0 = 1` carry `FirstBobFrontierInstance`'s own BEYOND-PAPER AUDIT label. -/

section Consistency

/-- The probe mass: the banked `MassRedistributionCounting.probeMass` -- which
puts all first-Bob mass on the coordinate-`0` donor and so reproduces the banked
`e_B = 1`, `|J_good| = 1`, `e_T = 1` configuration -- plus one protected
reservoir pair's worth of mass, `mu_P + mu_P = 1/92`, delivered to the freed
final node `liveFinalNodeZero`.  **Ours, not the paper's** (GAP item 3).

**R-4, repaired this round:** the banked `probeMass` is now *consumed* here
rather than re-spelled.  The park generation wrote its body
`fun _ x => if x.1 = (0 : Fin 3) then 1 else 0` out inline; that was the right
content but the wrong discipline in a module whose whole gate is
consumption-by-pin, so the summand is now the banked definition itself.  The
type is unchanged and the two bodies are definitionally equal. -/
noncomputable def probeTerminalMass :
    FrontierNode liveProtocol liveRows 1 2 → CertIndex liveProtocol liveRows 1 2 → ℝ :=
  fun v x => probeMass v x + (if v = liveFinalNodeZero then (1 : ℝ) / 92 else 0)

/-- The probe reservoir densities: both protected reservoirs full.  **Ours, not
the paper's** -- the real density carrier is read off `streamRows` once the
transcript-level construction lands (reach-goal residue L1).  At this value the
frozen `09:1370--1373` split holds with equality, which is the tightest point of
the bundle and therefore the honest one to audit at. -/
noncomputable def probeDens :
    Bool → CertIndex liveProtocol liveRows 1 2
      → FrontierNode liveProtocol liveRows 1 2 → ℝ :=
  fun _ _ _ => 1

/-- The exceptional-node mass is untouched at the first-Bob node, so the banked
Bob-heavy classification survives the added terminal mass. -/
theorem probeTerminal_firstBobMass (x : CertIndex liveProtocol liveRows 1 2) :
    firstBobMass liveSystem probeTerminalMass x
      = if x.1 = (0 : Fin 3) then 1 else 0 := by
  rw [firstBobMass, live_bobNodes, Finset.sum_singleton]
  have hne : liveBobNode ≠ liveFinalNodeZero := by decide
  simp [probeTerminalMass, probeMass, hne]

theorem probeTerminal_firstBobMass_zero :
    firstBobMass liveSystem probeTerminalMass probeDonorZero = 1 := by
  rw [probeTerminal_firstBobMass]
  norm_num [probeDonorZero]

theorem probeTerminal_firstBobMass_one :
    firstBobMass liveSystem probeTerminalMass probeDonorOne = 0 := by
  rw [probeTerminal_firstBobMass]
  norm_num [probeDonorOne]

/-- The two clean donors of the live system, explicitly. -/
theorem probe_cleanFinal_eq :
    liveSystem.cleanFinal = {probeDonorZero, probeDonorOne} := by decide

/-- `e_B = 1` at the probe: the coordinate-`0` donor alone is Bob-heavy. -/
theorem probeTerminal_bobHeavy_eq :
    bobHeavyDonors liveSystem probeTerminalMass (1 / 100) = {probeDonorZero} := by
  classical
  rw [bobHeavyDonors, probe_cleanFinal_eq]
  have hzero : (1 : ℝ) / 100 / 4 < firstBobMass liveSystem probeTerminalMass probeDonorZero := by
    rw [probeTerminal_firstBobMass_zero]; norm_num
  have hone : ¬ ((1 : ℝ) / 100 / 4 < firstBobMass liveSystem probeTerminalMass probeDonorOne) := by
    rw [probeTerminal_firstBobMass_one]; norm_num
  rw [Finset.filter_insert, if_pos hzero, Finset.filter_singleton, if_neg hone]
  rfl

/-- `|J_good| = 1` at the probe: the coordinate-`1` donor alone is good. -/
theorem probeTerminal_goodDonors_eq :
    goodDonors liveSystem probeTerminalMass (1 / 100) = {probeDonorOne} := by
  classical
  rw [goodDonors, probeTerminal_bobHeavy_eq, probe_cleanFinal_eq]
  decide

/-- `e_T = 1` at the probe: the final node freed by the Bob-heavy donor. -/
theorem probeTerminal_exceptional_eq :
    exceptionalFinal liveSystem probeTerminalMass (1 / 100) = {liveFinalNodeZero} := by
  classical
  rw [exceptionalFinal, probeTerminal_goodDonors_eq, live_finalNodes]
  decide

/-- **Hypothesis consistency for `exists_terminal_star_and_reservoir`.**

**BEYOND-PAPER AUDIT values -- explicitly NOT legal ones** (see the section
docstring).  All four hypotheses of the endpoint hold simultaneously at the live
routed system with `eta_R = 1/100`, the probe mass, and the constant density
family `d_Sigma = d_D = 1`:

* `0 < eta_R`;
* `J_good` is nonempty (`|J_good| = 1`);
* the round-4 endpoint `eta_R/4 < exceptionalMass` holds at that donor, with
  `1/400 < 1/92`;
* the `09:1370--1373` split holds **with equality**, `1/92 = mu_P + mu_P`.

So the bundle admits no derivation of `False`, and the endpoint is not entered on
an inconsistent premise set.  Nothing here is a canonical inhabitant: the
obligation stays registered and deferred. -/
theorem endpoint_bundle_is_consistent :
    (0 : ℝ) < 1 / 100
      ∧ (goodDonors liveSystem probeTerminalMass (1 / 100)).Nonempty
      ∧ (∀ j ∈ goodDonors liveSystem probeTerminalMass (1 / 100),
          (1 : ℝ) / 100 / 4 < exceptionalMass liveSystem probeTerminalMass (1 / 100) j)
      ∧ (∀ j ∈ goodDonors liveSystem probeTerminalMass (1 / 100),
          ∀ T ∈ exceptionalFinal liveSystem probeTerminalMass (1 / 100),
            probeTerminalMass T j
              ≤ muP * probeDens true j T + muP * probeDens false j T) := by
  classical
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [probeTerminal_goodDonors_eq]
    exact ⟨probeDonorOne, Finset.mem_singleton_self _⟩
  · intro j hj
    rw [probeTerminal_goodDonors_eq, Finset.mem_singleton] at hj
    subst hj
    rw [exceptionalMass, probeTerminal_exceptional_eq, Finset.sum_singleton]
    norm_num [probeTerminalMass, probeMass, probeDonorOne]
  · intro j hj T hT
    rw [probeTerminal_goodDonors_eq, Finset.mem_singleton] at hj
    rw [probeTerminal_exceptional_eq, Finset.mem_singleton] at hT
    subst hj
    subst hT
    simp only [muP, probeDens]
    norm_num [probeTerminalMass, probeMass, probeDonorOne]

/-- **The probe is nondegenerate.**

`|J_good| = 1` and `e_T = 1`: neither the good-donor set nor the exceptional set
is empty, so no clause of the endpoint above is satisfied vacuously, and the
frozen `09:1702` case is genuinely avoided rather than trivially so. -/
theorem probeTerminal_counts_nondegenerate :
    (goodDonors liveSystem probeTerminalMass (1 / 100)).card = 1
      ∧ (exceptionalFinal liveSystem probeTerminalMass (1 / 100)).card = 1 := by
  rw [probeTerminal_goodDonors_eq, probeTerminal_exceptional_eq]
  exact ⟨Finset.card_singleton _, Finset.card_singleton _⟩

/-- **The endpoint FIRES at the probe.**

Not merely "the bundle is non-contradictory": the endpoint of §4 is *applied* to
that bundle, so the whole pigeonhole layer runs end to end on a concrete routed
system and produces an actual `T_*`, an actual common reservoir type, the frozen
donor count and the frozen density bound.  A green statement gate cannot see the
difference between a consistent bundle and a firing one; this is the firing test.

**NON-FIDELITY / BEYOND-PAPER AUDIT** -- see the section docstring.  This is not
the canonical inhabitant and does not discharge the deferred obligation. -/
theorem endpoint_fires_at_the_probe :
    ∃ Tstar ∈ exceptionalFinal liveSystem probeTerminalMass (1 / 100), ∃ ty : Bool,
      ((goodDonors liveSystem probeTerminalMass (1 / 100)).card : ℝ)
          ≤ 2 * ((exceptionalFinal liveSystem probeTerminalMass (1 / 100)).card : ℝ)
              * ((selectedDonors liveSystem probeTerminalMass (1 / 100) probeDens
                    Tstar ty).card : ℝ)
        ∧ ∀ j ∈ selectedDonors liveSystem probeTerminalMass (1 / 100) probeDens Tstar ty,
            deltaZero (1 / 100)
                (exceptionalFinal liveSystem probeTerminalMass (1 / 100)).card
              ≤ probeDens ty j Tstar := by
  obtain ⟨h1, h2, h3, h4⟩ := endpoint_bundle_is_consistent
  exact exists_terminal_star_and_reservoir liveSystem probeTerminalMass probeDens
    h1 h2 h3 h4

/-- **`eq:wrapper-terminal-density` EVALUATED at the probe.**

`delta_0 = eta_R/(8 e_T mu_P)` (`09:1710--1713`) is a DEFINED quantity, so its
value here is *computed* through the definitional chain -- the banked
`WrapperMassRedistribution.deltaZero` at the banked `WrapperProtectedEarly.muP`
(`= 1/184`, `09:1372` / `06:133`) and the probe's own `e_T`, which
`probeTerminal_exceptional_eq` already pinned to `1`.  No numeral is assigned to
`delta_0` anywhere; `23/100` is the *output* of `(1/100)/(8 * 1 * (1/184))`.

**NON-FIDELITY / BEYOND-PAPER AUDIT** -- `eta_R = 1/100` is ours and illegal
(see the section docstring); this evaluates our encoding at a point the frozen
construction never visits. -/
theorem deltaZero_at_probe_eq :
    deltaZero (1 / 100) (exceptionalFinal liveSystem probeTerminalMass (1 / 100)).card
      = 23 / 100 := by
  rw [probeTerminal_exceptional_eq, Finset.card_singleton, deltaZero]
  norm_num [muP]

/-- **R-6 closed: the enlarged §5 bundle is jointly satisfied, non-degenerately.**

The `u_don` leg of §5 introduces two hypotheses that §4's endpoint does not
carry -- the relative-density bound `hdens1` and the frozen defining demand
`hdef` of `09:1717--1718`.  The park generation fired only §4's bundle, so no
declaration exhibited the *enlarged* bundle jointly satisfied; this is that
exhibit, and neither clause holds vacuously:

* `hdens1` holds with **equality** at the probe (`d = 1`), the tightest point;
* `hdef` holds **strictly** at `s = 1`, `u_don = 64`:
  `8 * 1 = 8 <= 64 * (23/100) = 14.72`, with `delta_0` evaluated, not assigned.

`s = 1` and `u_don = 64` are self-chosen and **NO legality is claimed** for
them: `09:1717--1718` fixes `u_don` as the least power of two clearing the
demand at the *frozen* `delta_0`, and the frozen `s = 2^{r_3}` is unavailable
here because the routed system of the paper is unbuilt (residue L1).  This is a
**BEYOND-PAPER AUDIT** of our encoding, not an instantiation of the schedule. -/
theorem uDon_bundle_is_consistent :
    (∀ (b : Bool) (j : CertIndex liveProtocol liveRows 1 2)
        (T : FrontierNode liveProtocol liveRows 1 2), probeDens b j T ≤ 1)
      ∧ 8 * ((1 : ℕ) : ℝ) ≤ ((64 : ℕ) : ℝ)
          * deltaZero (1 / 100)
              (exceptionalFinal liveSystem probeTerminalMass (1 / 100)).card := by
  refine ⟨fun b j T => ?_, ?_⟩
  · norm_num [probeDens]
  · rw [deltaZero_at_probe_eq]; norm_num

/-- **R-6 closed: the `u_don` leg FIRES at the probe.**

`09:1744`'s "and hence `u_don >= 8s`", run end to end on the concrete routed
system: from the round-4 endpoint at the probe's good donor, through both
pigeonholes, `eq:wrapper-terminal-density`, `delta_0 <= 1` and the banked
`uDon_ge_eight_s`.  The park generation fired only §4's endpoint, leaving
`terminal_uDon_floor` and `uDon_floor_of_owner_family` unexercised.

**The statement is not arithmetically trivial.**  `s` and `u_don` are left free
and only `hdef` is assumed, so the theorem says: at the probe, clearing the
frozen demand `8s <= u_don delta_0` forces `8s <= u_don`.  That implication is
*false* for a density above one -- at `delta_0 = 10`, `s = 1`, `u_don = 1` one
has `8 <= 10` but not `8 <= 1` -- so it is exactly `09:1742`'s content, and it
is discharged here from `delta_0 = 23/100` rather than assumed.

**NON-FIDELITY / BEYOND-PAPER AUDIT** -- see the section docstring.  This is not
the canonical inhabitant and does not discharge the deferred obligation. -/
theorem uDon_floor_fires_at_the_probe {s uDon : ℕ}
    (hdef : 8 * (s : ℝ)
      ≤ (uDon : ℝ) * deltaZero (1 / 100)
          (exceptionalFinal liveSystem probeTerminalMass (1 / 100)).card) :
    8 * s ≤ uDon := by
  obtain ⟨h1, h2, h3, h4⟩ := endpoint_bundle_is_consistent
  exact uDon_floor_of_owner_family liveSystem probeTerminalMass probeDens h1 h2 h3 h4
    (fun b j T => (uDon_bundle_is_consistent.1 b j T)) hdef

end Consistency

end EthInapproximability.ParameterizedNP.OwnerFamilyToPigeonhole
