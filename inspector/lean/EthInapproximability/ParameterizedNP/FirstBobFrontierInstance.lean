import EthInapproximability.ParameterizedNP.FrontierIndexing

/-!
# Parameterized NP route: the live first-Bob frontier instance

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`),
  the **frontier layer** of the per-member shallow-protocol refutation engine.
* **The exact frozen lines traced here**, in print order:
  * `09:105`, "Let `q = 2^r` be the scale-alignment width", which fixes the
    width/exponent identification used at every `q`-vs-`2^r` substitution below.
  * `09:1217--1221`, `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0` -- the **defining
    display** of the initial row floor, reified in the banked
    `DenseWrapperFrontier.refRowFloor` and consumed here by pin.
  * `09:1233--1236`, the initial placement: "that coordinate would therefore
    retain at least `A_r = q A_0` reference rows.  Start one clean reference
    certificate in every coordinate outside `E_0`, each with weight one."
  * `09:1238--1248`, the routing rule with its branching clause and the kind
    transition, consumed through `RoutingDynamics` and `FrontierIndexing`.
  * `09:1250--1259`, the two stopping rules, `d_v`, `kappa_v = 2^{r-d_v}`,
    `W_v = total certificate weight at v`, and "Every first-Bob node has
    `kappa_v >= 2`".
  * `09:1259--1266`, `eq:wrapper-frontier-conservation`.
  * `09:1268`, "Put `vartheta = 9/16`".
  * `09:1278--1280`, coordinate uniqueness at a node ("at a fixed node there is
    at most one descendant of each initial outer coordinate"), which is what the
    weight decomposition of §1 turns into an identity.
  * `09:1309--1313`, `eq:wrapper-first-bob-light`, "`W_v < vartheta kappa_v` at
    every first-Bob node `v`".
  * `09:1346--1350` and `09:1352--1357`, the final-node classification and
    `eq:wrapper-clean-count`.
* **Cross-anchors opened first-hand for this tranche:** `09:1188--1213` (the
  contradiction frame and `lem:wrapper-no-bob-completion`), `09:1315--1344`
  (`lem:final-reference-uniqueness`), `09:1367--1384` (the protected reservoirs
  and `mu_P`), `09:1388--1416` (`lem:template-coordinate-extraction`),
  `09:1417--1531` (`lem:early-protected-closure` and the opening of
  `sec:wrapper-mass-redistribution`), and `06:513--520` (`eq:q-deltaU`,
  `q = 2^{A_wrap L_P^2}`) in
  `sections/06-parameter-schedule.tex` (SHA-256
  `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the only import is `FrontierIndexing`,
  whose ledger row records the same exclusion.
* **Proof status.**  Every declaration is either a general property of the banked
  `FrontierIndexing.frontierWeight`, or a **BEYOND-PAPER audit instance** of the
  banked `FrontierIndexing.canonicalSystem`, explicitly labelled as such.  **No
  mathematics is added**, and no conclusion of `eq:wrapper-u-dense` is asserted
  anywhere.

## What this tranche closes in the predecessor module

`FrontierIndexing.lean` (SHA-256
`057A0B39EDB5BA909AEC4A0061598BE3D38E8CCC781F3343D659089099F42F4B`, which pins
`RoutingDynamics.lean` at SHA-256
`30554259FA94484328EC60E94F199F57DF0DB0ECC3B20CF6DDAE6B4B9E4AA64C`) recorded one
**new** GAP-EXPOSED item, (11).  This module discharges it and touches no other.

* **Item (11), the consistency instance had an empty first-Bob set, discharged.**
  The banked record read, verbatim in the docstring of
  `canonical_cleanCount_consistent`: "`hlight` holds **vacuously**: that shape
  has no first-Bob node at all (`aliceLadder_not_isFirstBobNode`), so
  `bobNodes = {}` and `bobCapacity = 0` ... exhibiting the canonical system with
  a *nonempty* first-Bob set is a registered next-round obligation."
  `liveSystem` below is `canonicalSystem` at a protocol with an Alice root and a
  Bob query at depth `1`, at `r = 2`.  Its frontier is
  `{[false,false], [false,true], [true]}`; `[true]` is an **exposed first-Bob
  node**, so `bobNodes = {liveBobNode}` is nonempty, the frozen `09:1259`
  `kappa_v >= 2` is **attained** (`kappa_v = 2^{2-1} = 2`, not merely bounded),
  `bobCapacity = 2 > 0`, and `eq:wrapper-first-bob-light` enters
  `canonical_cleanCount` as a **real inequality with both sides positive**:
  `W_v = 1 <= vartheta . 2 = 9/8`, with strict slack.  `canonical_cleanCount` is
  then re-run at that instance (`live_cleanCount`) with a **positive first
  conjunct LHS** `q - e_0/(1-vartheta) = 4 - 16/7 = 12/7 > 0`, so the first
  conclusion is a genuine lower bound on the clean count rather than a
  vacuously-true inequality below zero (`live_cleanCount_first_conjunct_is_live`
  contrasts the `e_0 = 2` regime, where the same conjunct reads `-4/7 <= c` and
  says nothing).

**Why the frontier is not the `wrapperFrontierProbe` shape restated.**  The
banked `DenseWrapperFrontier.wrapperFrontierProbe` is an *abstract*
`WrapperFrontier` whose `route`, `firstBob` and per-node weights are chosen
directly.  Here nothing is chosen: the frontier is `frontierRoutes`, produced by
running the frozen routing rule of `09:1238--1248` on a protocol object, the
kinds are `RoutingDynamics.kindAlong`, and the weights are `frontierWeight`.  The
three-node shape is a **computed output**, not constructor data
(`live_frontierRoutes`).

## Predecessor modules consumed **by pin**, never restated

* `Workspace.Types.Protocol` (through `LegacyNPCC.Core`, project-axiom-free):
  `Protocol`, `Protocol.aNode`, `Protocol.bNode`, `Protocol.leaf`.
* `EthInapproximability.ParameterizedNP.DenseWeightedCount`: `stoppingCapacity`.
* `EthInapproximability.ParameterizedNP.DenseWrapperFrontier`: `refRowFloor`,
  `CertKind` with `CertKind.weight`, `WrapperFrontier` with `capacity`,
  `bobNodes`, `finalNodes`, `bobCapacity`, `cleanNodes`, `splitNodes`,
  `finalWeight`, and `vartheta`.
* `EthInapproximability.ParameterizedNP.RoutedCertificateSystem`:
  `IsFirstBobNode`, `RoutedSystem`, `toWrapperFrontier`.
* `EthInapproximability.ParameterizedNP.RoutingDynamics`: `kindAlong`,
  `CompletedNoBob`.
* `EthInapproximability.ParameterizedNP.FrontierIndexing`: `descendants`,
  `coordRoutes`, `frontierRoutes`, `FrontierNode`, `CertIndex`,
  `canonicalSystem`, `frontierWeight`, `frontier_conservation`,
  `canonical_cleanCount`, each consumed at its own interface.

## Canonical inhabitation

* **The canonical-inhabitation obligation for `RoutedSystem` is already
  discharged** at the paper's own construction by
  `FrontierIndexing.canonicalSystem`, and this module defines **no new type**, so
  it inherits that discharge rather than re-opening it.  What was still open was
  narrower and is what this tranche settles: the canonical system had never been
  exhibited at a protocol where the **first** frozen stopping rule fires, so
  every statement about first-Bob nodes downstream of it was being discharged on
  an empty set.
* **`liveSystem` is `canonicalSystem` itself**, at the two frozen inputs `hcomp`
  (the conclusion of `lem:wrapper-no-bob-completion`, `09:1195--1200`) and `hR`
  (the retention `A_r <= |R i|` of `09:1233--1235`).  Nothing about the routed
  system, the frontier, the kinds or the weights is chosen; the only choices are
  the ambient alphabet and the numerals `r`, `A_0`, `e_0`, and those are exactly
  what the BEYOND-PAPER label below covers.
* **BEYOND-PAPER AUDIT label (mandatory, and not a legality claim).**  `r` is
  DEFINED by the schedule -- `06:515` `q = 2^{A_wrap L_P^2}` with `09:105`
  `q = 2^r`, so `r = A_wrap L_P^2` -- `A_0` is DEFINED by `09:1219`
  `A_0 = ceil(2 x_T m_G)`, and `e_0 = |E_0|` is fixed by the exceptional-set
  bookkeeping of `WrapperProjectionCovers`.  Putting the numerals `r = 2`,
  `A_0 = 1`, `e_0 = 1` at those three places, and choosing the alphabet
  `Fin 12`, the two Alice predicates and the Bob predicate, is **ours**: this
  instance audits *our encoding* at a point the paper never visits, and is
  strictly weaker evidence than the paper's own application point.  It is
  recorded here for exactly what it is.  `q = 4` is **not** chosen: it is
  *derived*, by evaluating `09:105`'s `q = 2^r` at `r = 2`; the row floor
  `A_r = 4` is derived by evaluating `09:1221`'s `A_k = 2^k A_0` through the
  banked `refRowFloor`; and `kappa_v = 2` is derived by evaluating `09:1255`'s
  `kappa_v = 2^{r-d_v}` through the banked `stoppingCapacity`.  The parametric
  legality statement, valid at *every* legal `(r, A_0)` including the schedule's,
  remains `FrontierIndexing.canonicalSystem_legal_instance`.
* `r = 2` is the least exponent at which the audit is possible at all: a **final**
  Alice node needs an Alice path of depth exactly `r`, which forces the root to be
  an Alice query, so an exposed first-Bob node coexisting with one sits at
  `1 <= d_v < r`; a frontier carrying both stopping rules therefore needs
  `r >= 2`.  (The forcing is the coexistence of a final Alice node, **not**
  `lem:wrapper-no-bob-completion`: that lemma, `09:1197--1199`, constrains only
  root-to-leaf paths containing no Bob query, and would hold vacuously if the root
  were itself a Bob query.)  At `r = 2` Kraft is met with equality, `2 + 1 + 1 = 4 = q`
  (`live_kraft_tight`), so the instance sits on the frozen boundary rather than
  in a slack corner.

## Aux-lemma battery and statement poles

General identity, specialization, positivity and bound properties of the banked
`frontierWeight`, all proved: `frontierWeight_eq_sum_reaching`,
`frontierWeight_eq_weight_of_unique_coord`, `frontierWeight_le_one_of_unique_coord`,
`frontierWeight_pos`, `frontierWeight_le_card_reaching`; plus the general
dyadic readout `firstBob_capacity_dyadic`.

Three **statement poles**: `firstBobLight_pole_two_clean_certificates` (the light
bound is not automatic -- at `kappa_v = 2` the frozen right-hand side `9/8` is
strictly below `2`, so a first-Bob node reached by two clean certificates would
violate `eq:wrapper-first-bob-light`; the live node is reached by exactly one),
`live_cleanCount_first_conjunct_is_live` (at `e_0 = 2` the same first conjunct
has a negative left-hand side and is satisfied by every cardinality, so a
positive LHS is what makes the conclusion content), and
`live_hlight_is_not_vacuous` (the quantifier of `hlight` ranges over a nonempty
set here, unlike at the predecessor's consistency instance).

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for
this tranche (`first-Bob`, `first Bob`, `frontier`, `certificate weight`,
`Kraft`, `kappa`).  Every hit was opened and none states what any declaration
below states:

* `01-introduction.tex:101` and `02-preliminaries.tex:564` ("a weighted
  frontier", "the weighted frontier") are the **Stage-4 quotient-support**
  weighted frontier, a different mechanism from the wrapper's first-Bob frontier.
* `02-preliminaries.tex:301` ("not stable under the first Bob bit") is a remark
  about rectangle stability, not about a frontier node.
* `A-stage4-details.tex:263--271` is the **same Stage-4 quotient-support**
  stopping count: its `kappa_v` is a residual copy capacity and its conserved
  quantity is a template/witness mass, not the certificate weight `W_v` of
  `09:1257`.  It is also unnumbered prose.
* `A-stage4-details.tex:318--319`, `371--373` and `387` ("terminal frontier") are
  the direct-bridge / two-stream terminal frontier; `371--373` is already
  recorded as unclaimed prose by `WRAPPER-PROJECTION-COVERS-001` and `390--391`
  is already assigned to `TERMINAL-TWO-STREAM-001`.

**No reader item is claimed**, and the absence is a finding about the reader
artifact rather than an omission here.

## `lem:early-protected-closure` (`09:1417--1531`): the RCS item-2 disposition

The tranche brief asked for the transcription of `lem:early-protected-closure`,
`ROUTED-CERTIFICATE-SYSTEM-001` GAP-EXPOSED item (2), "if capacity remains".  It
is **not transcribed here, and it does not need to be**: the frozen statement and
proof `09:1418--1509` are **already banked**, in
`EthInapproximability.ParameterizedNP.WrapperProtectedEarly` (SHA-256
`AF27C17C71BB2E964F68D1E7F41C9DBAF0C867BCACEF9797A09285F0BB883F59`) as
`earlyProtectedClosure`, under `WRAPPER-PROTECTED-EARLY-001`, together with
`lem:template-coordinate-extraction` (`09:1388--1425`) in the same module.  That
module is already a transitive import here (through `ParameterSchedule` and
`WrapperMassRedistribution`), so restating any part of it would violate the
fixed-interface discipline.  The honest disposition is therefore:

* **RCS item (2) is superseded, not open**: the transcription exists by pin, so
  the item should be re-read in the ledger as a *cross-reference* rather than a
  missing transcription.  This module verifies the claim first-hand by opening
  `WrapperProtectedEarly.earlyProtectedClosure` and confirming its docstring
  anchors `09:1418--1509`, its `hthr` binder is `eq:protected-early-threshold`
  (`09:1421--1425`), and its conclusion is the frozen `C + log_2 kappa - 1`.
* **What genuinely remains in the named range `09:1417--1531` is `09:1510--1531`
  only** -- the opening of `sec:wrapper-mass-redistribution` -- which is
  GAP-EXPOSED **in full** under `WRAPPER-MASS-REDISTRIBUTION-001` and is
  **DEFERRED here, with the range named**: `09:1512--1781`.  Nothing of it is
  formalized, cited, or implied below.
* The one link this module does land is the *interface* fact `09:1521--1523`
  needs to apply that lemma at a first-Bob node -- "Such a node has
  `kappa_v >= 2`" -- in the dyadic form the banked lemma consumes as its `hl`
  binder: `firstBob_capacity_dyadic` gives `kappa_v = 2^l` with `1 <= l` at every
  first-Bob node of every routed system, and `live_bobNode_dyadic_capacity`
  attains it at `l = 1`.  **No conclusion of `earlyProtectedClosure` is invoked,
  and `sec:wrapper-mass-redistribution` is not entered.**

## What is *not* claimed

`hDenseRung` is **neither discharged nor fed**; `eq:wrapper-u-dense` is asserted
nowhere below; `eq:wrapper-first-bob-light` and `lem:final-reference-uniqueness`
remain the named binders `hlight` and `hfinal` of the banked
`canonical_cleanCount` -- this tranche *supplies* them at one audit instance and
**does not discharge them in general**; GAP-EXPOSED items 3, 4, 5 and 6 of
`ROUTED-CERTIFICATE-SYSTEM-001` are untouched; item 2 is dispositioned above as a
by-pin supersession, not as new work; and **no route completion is claimed.**

**GAP-EXPOSED, recorded rather than papered over, with a next-round prescription:**

12. **`eq:wrapper-first-bob-light` is supplied, not derived.**  `live_hlight`
    exhibits the frozen light condition at one first-Bob node of one audit
    instance; **no declaration derives `W_v < vartheta kappa_v` at an arbitrary
    first-Bob node from the routing.**  The frozen derivation of `09:1270--1308`
    runs through the certified-scale reference stopping lemma and the
    small-capacity fallback of `09:1283--1308`, neither of which is consumed
    here.  Until that lands, `hlight` stays a binder of `canonical_cleanCount`
    everywhere it is used, and citing this module as evidence that it is
    discharged would be a misreading.
13. **The split branch never reaches a first-Bob node at the audit instance.**
    No certificate splits along any route of `liveProtocol`, so every derived
    kind is `clean`, the frozen `ell` of `09:1349--1350` is `0`
    (`live_splitNodes_card`) and the half-weight column of
    `eq:wrapper-clean-count` is empty here.  A live instance in which a *split*
    certificate's half-weight descendant reaches an exposed first-Bob node --
    exercising `09:1244`'s branching clause and the light bound at the same node
    -- is the next-round obligation.  `FrontierIndexing.splitProbe` shows the
    split branch is reachable at `r = 1`, but that shape has no Bob query.
-/

namespace EthInapproximability.ParameterizedNP.FirstBobFrontierInstance

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing

/-! ## §1  `W_v` resolved by coordinate (`09:1257`, `09:1278--1280`)

"`W_v = total certificate weight at v`", together with "at a fixed node there is
at most one descendant of each initial outer coordinate".  The banked
`frontierWeight` sums over the certificate index `CertIndex`, which is a sigma
type over coordinates; the frozen uniqueness sentence says the inner sum has at
most one surviving term, and that is what the identity below records.  Everything
here is **general** in the protocol, the coordinate type, the reference rows and
the two frozen numerals. -/

section General

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **Aux A1 (`09:1257` resolved by `09:1278--1280`).**  `W_v` is the sum, over
the outer coordinates, of the derived kind weight of the one descendant of that
coordinate sitting at `v` -- and `0` for the coordinates that do not reach `v`.

This is an *identity*, not an estimate: the frozen "at most one descendant of
each initial outer coordinate" is what collapses the inner sum, and it holds here
because the routed descendants of one coordinate carry pairwise distinct
addresses (`FrontierIndexing.coordRoutes` is a `Finset`).  General. -/
theorem frontierWeight_eq_sum_reaching (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) :
    frontierWeight P R A0 r v
      = ∑ i : Coord, (if v.val ∈ coordRoutes P R A0 r i
          then (kindAlong P (R i) A0 r v.val).weight else 0) := by
  classical
  unfold frontierWeight
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoe : ∑ p : {p : List Bool // p ∈ coordRoutes P R A0 r i},
      (if p.val = v.val then (kindAlong P (R i) A0 r p.val).weight else 0)
      = ∑ p ∈ coordRoutes P R A0 r i,
        (if p = v.val then (kindAlong P (R i) A0 r p).weight else 0) :=
    Finset.sum_coe_sort (coordRoutes P R A0 r i)
      (fun p => if p = v.val then (kindAlong P (R i) A0 r p).weight else 0)
  rw [hcoe, Finset.sum_ite_eq' (coordRoutes P R A0 r i) v.val
    (fun p => (kindAlong P (R i) A0 r p).weight)]

/-- **Aux A2.**  The specialization the frozen counting actually uses: when
exactly one outer coordinate reaches `v`, `W_v` **is** that coordinate's derived
kind weight.  General. -/
theorem frontierWeight_eq_weight_of_unique_coord (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode P R A0 r) {i₀ : Coord}
    (h : ∀ i : Coord, v.val ∈ coordRoutes P R A0 r i ↔ i = i₀) :
    frontierWeight P R A0 r v = (kindAlong P (R i₀) A0 r v.val).weight := by
  classical
  rw [frontierWeight_eq_sum_reaching, Finset.sum_eq_single i₀]
  · rw [if_pos ((h i₀).mpr rfl)]
  · intro b _ hb
    exact if_neg fun hcon => hb ((h b).mp hcon)
  · intro hcon; exact absurd (Finset.mem_univ i₀) hcon

/-- **Aux A3.**  A node reached by exactly one coordinate carries at most the
clean weight `1` of `09:1236`.  General. -/
theorem frontierWeight_le_one_of_unique_coord (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode P R A0 r) {i₀ : Coord}
    (h : ∀ i : Coord, v.val ∈ coordRoutes P R A0 r i ↔ i = i₀) :
    frontierWeight P R A0 r v ≤ 1 := by
  rw [frontierWeight_eq_weight_of_unique_coord P R A0 r v h]
  exact CertKind.weight_le_one _

/-- **Aux A4.**  Every frontier node carries **strictly positive** weight: it is
on the frontier because some coordinate's routed branch stopped there, and every
frozen kind has positive weight (`09:1236`, `09:1246`).  General. -/
theorem frontierWeight_pos (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : 0 < frontierWeight P R A0 r v := by
  classical
  obtain ⟨i, hi⟩ := exists_coord_of_mem_frontierRoutes v.property
  rw [frontierWeight_eq_sum_reaching]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · by_cases h : v.val ∈ coordRoutes P R A0 r j
    · rw [if_pos h]; exact le_of_lt (CertKind.weight_pos _)
    · rw [if_neg h]
  · rw [if_pos hi]; exact CertKind.weight_pos _

/-- **Aux A5 (monotone in the number of donors).**  `W_v` never exceeds the number
of outer coordinates whose routed branch reaches `v`, because each contributes at
most the clean weight `1`.  General; this is the sharpening of the banked
`frontierWeight_le_card` from "all certificates" to "the ones actually at `v`". -/
theorem frontierWeight_le_card_reaching (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) :
    frontierWeight P R A0 r v
      ≤ (((Finset.univ.filter fun i : Coord => v.val ∈ coordRoutes P R A0 r i)).card : ℝ) := by
  classical
  rw [frontierWeight_eq_sum_reaching]
  calc ∑ i : Coord, (if v.val ∈ coordRoutes P R A0 r i
        then (kindAlong P (R i) A0 r v.val).weight else 0)
      ≤ ∑ i : Coord, (if v.val ∈ coordRoutes P R A0 r i then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : v.val ∈ coordRoutes P R A0 r i
        · rw [if_pos h, if_pos h]; exact CertKind.weight_le_one _
        · rw [if_neg h, if_neg h]
    _ = _ := by simp [Finset.sum_boole]

end General

/-! ## §2  `kappa_v >= 2` in the dyadic form the protected-mass lemma consumes
(`09:1259`, `09:1521--1523`)

"Every first-Bob node has `kappa_v >= 2`", and `09:1521--1523` applies
`lem:early-protected-closure` "at every first-Bob node ... Such a node has
`kappa_v >= 2`".  The banked `WrapperProtectedEarly.earlyProtectedClosure` takes
that input in its dyadic form -- `kappa = 2^l` with `1 <= l` -- which is exactly
what `09:1255`'s `kappa_v = 2^{r-d_v}` supplies (`09:1253` introduces `d_v`; the
display itself is at `09:1255`).  The readout below is the
interface fact only; **no conclusion of that lemma is invoked here.** -/

section Dyadic

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}

/-- **Aux A6 (`09:1255` + `09:1259`, dyadic form).**  At a first-Bob node the
frozen `kappa_v` is a power of two with positive exponent.  This is the shape
`09:1521--1523` needs in order to enter `lem:early-protected-closure`, whose
banked transcription takes `kappa = 2^l` with `1 <= l`.  General. -/
theorem firstBob_capacity_dyadic (S : RoutedSystem P Coord ι V r A0) {v : V}
    (h : S.firstBob v = true) :
    ∃ l : ℕ, 1 ≤ l ∧ S.toWrapperFrontier.capacity v = 2 ^ l := by
  refine ⟨r - (S.node v).length, ?_, rfl⟩
  have := (S.firstBob_spec v h).2.2
  omega

end Dyadic

/-! ## §3  The live first-Bob instance (BEYOND-PAPER AUDIT, `r = 2`)

Everything in this section is an audit of *our encoding* at self-chosen numerals.
See the module header for the mandatory BEYOND-PAPER label and for which
quantities are DEFINED by the frozen source (`r`, `A_0`, `e_0`) and therefore not
legitimately assigned. -/

section LiveInstance

/-- The root Alice predicate of the audit protocol.  **Ours**, not the paper's:
the frozen text fixes no alphabet and no Alice predicate.  It sends the third
block of rows to the `true` child and the first two to the `false` child. -/
def rootPred : Fin 12 → Bool := fun x => decide (8 ≤ x.val)

/-- The depth-`1` Alice predicate on the `false` side.  **Ours**, as above: it
separates the first block of rows from the second. -/
def midPred : Fin 12 → Bool := fun x => decide (4 ≤ x.val)

/-- **The audit protocol: an Alice root, an Alice query at depth `1` on the
`false` side, and a Bob query at depth `1` on the `true` side.**

This is the *shape* `lem:wrapper-no-bob-completion` (`09:1195--1213`) leaves
behind: no root-to-leaf path without a Bob query is shorter than `r = 2`, because
the only Bob-free branch runs through the depth-`1` Alice query.  The Bob query
sitting at depth `1 < r` is what makes the **first** frozen stopping rule of
`09:1250` fire, which the predecessor's consistency instance could not do.

**BEYOND-PAPER label.**  The alphabet `Fin 12`, both Alice predicates and the Bob
predicate are ours; the frozen text fixes none of them. -/
def liveProtocol : Protocol (Fin 12) Bool Bool :=
  Protocol.aNode rootPred
    (Protocol.aNode midPred (Protocol.leaf true) (Protocol.leaf true))
    (Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf true))

/-- The three started outer coordinates of the audit instance and their reference
rows, one block of four each.  Four is not a chosen number: it is
`A_r = refRowFloor A_0 r` at `r = 2`, `A_0 = 1`, i.e. `09:1221`'s `A_k = 2^k A_0`
evaluated through the banked `refRowFloor`, which is the retention `09:1234--1235`
demands ("that coordinate would therefore retain at least `A_r = q A_0` reference
rows"). -/
def liveRows : Fin 3 → Finset (Fin 12) :=
  ![Finset.univ.filter (fun x => x.val < 4),
    Finset.univ.filter (fun x => 4 ≤ x.val ∧ x.val < 8),
    Finset.univ.filter (fun x => 8 ≤ x.val)]

/-- **`09:1233--1235` at the audit instance.**  Every started coordinate holds all
`A_r = 2^2 . 1 = 4` retained reference rows, so the frozen retention holds with
equality. -/
theorem live_hR : ∀ i : Fin 3, refRowFloor 1 2 ≤ (liveRows i).card := by decide

/-- **`09:1195--1200` at the audit instance.**  The frame condition of
`lem:wrapper-no-bob-completion`: every Alice-only route shorter than `r = 2`
reaches a query node -- the root and the depth-`1` Alice node on the `false`
side, and the depth-`1` Bob node on the `true` side. -/
theorem live_hcomp : CompletedNoBob liveProtocol 2 := by
  intro p _ hlt
  match p with
  | [] => trivial
  | [b] => cases b <;> trivial
  | (_ :: _ :: _) => simp at hlt

/-- **The canonical routed certificate system at the audit instance.**  This is
`FrontierIndexing.canonicalSystem` itself, at its own two frozen inputs; nothing
about the system is chosen here. -/
abbrev liveSystem :
    RoutedSystem liveProtocol (Fin 3) (CertIndex liveProtocol liveRows 1 2)
      (FrontierNode liveProtocol liveRows 1 2) 2 1 :=
  canonicalSystem live_hcomp live_hR

/-! ### The routing, computed

Each of the three started coordinates is routed by the frozen rule of
`09:1238--1248`, and where it stops is a **computed output**.  Coordinates `0`
and `1` route uniquely to the `false` side (their rows all fail the frozen
qualification threshold on the `true` side) and are separated at depth `1`;
coordinate `2` routes uniquely to the `true` side and is stopped there by the
first frozen rule at the Bob query. -/

/-- **`09:1238--1252` at coordinate `0`.**  A unique route to the final Alice node
`[false, false]`. -/
theorem live_descendants_zero :
    descendants liveProtocol (liveRows 0) 1 2 2 ([] : List Bool) = [[false, false]] := by
  decide

/-- **`09:1238--1252` at coordinate `1`.**  A unique route to the final Alice node
`[false, true]`. -/
theorem live_descendants_one :
    descendants liveProtocol (liveRows 1) 1 2 2 ([] : List Bool) = [[false, true]] := by
  decide

/-- **`09:1238--1251` at coordinate `2`.**  A unique route stopped by the *first*
frozen rule, at the Bob query of depth `1`. -/
theorem live_descendants_two :
    descendants liveProtocol (liveRows 2) 1 2 2 ([] : List Bool) = [[true]] := by
  decide

/-- **The frontier of the audit instance, computed.**  Three nodes: two final
Alice nodes at depth `2` and one exposed first-Bob node at depth `1`. -/
theorem live_frontierRoutes :
    frontierRoutes liveProtocol liveRows 1 2
      = ({[false, false], [false, true], [true]} : Finset (List Bool)) := by decide

/-- The exposed first-Bob node of the audit instance (`09:1250--1251`). -/
def liveBobNode : FrontierNode liveProtocol liveRows 1 2 := ⟨[true], by decide⟩

/-- The final Alice node reached by coordinate `0` (`09:1252`). -/
def liveFinalNodeZero : FrontierNode liveProtocol liveRows 1 2 := ⟨[false, false], by decide⟩

/-- The final Alice node reached by coordinate `1` (`09:1252`). -/
def liveFinalNodeOne : FrontierNode liveProtocol liveRows 1 2 := ⟨[false, true], by decide⟩

/-- **`09:1250--1251`, live.**  The first-Bob set of the canonical system is the
singleton `{[true]}` -- **nonempty**, which is exactly what the predecessor's
consistency instance could not exhibit. -/
theorem live_bobNodes : liveSystem.toWrapperFrontier.bobNodes = {liveBobNode} := by decide

/-- **`09:1252`, live.**  The final Alice nodes are the two depth-`2` addresses. -/
theorem live_finalNodes :
    liveSystem.toWrapperFrontier.finalNodes = {liveFinalNodeZero, liveFinalNodeOne} := by decide

/-- **`09:1255` evaluated, `09:1259` ATTAINED (not merely satisfied).**  The
`09:1255` display `kappa_v = 2^{r-d_v}` evaluates to `2^{2-1} = 2` at the live
first-Bob node, so the frozen `09:1259` bound "Every first-Bob node has
`kappa_v >= 2`" holds here **with equality**, and the instance sits on the frozen
boundary. -/
theorem live_kappa_attained : liveSystem.toWrapperFrontier.capacity liveBobNode = 2 := by decide

/-- **`09:1521--1523` interface, attained.**  The live first-Bob node supplies the
dyadic input `kappa = 2^l`, `1 <= l`, at `l = 1` -- the exact `hl` shape the
banked `WrapperProtectedEarly.earlyProtectedClosure` consumes.  **No conclusion of
that lemma is invoked**, and `sec:wrapper-mass-redistribution` (`09:1512--1781`)
is not entered. -/
theorem live_bobNode_dyadic_capacity :
    (∃ l : ℕ, 1 ≤ l ∧ liveSystem.toWrapperFrontier.capacity liveBobNode = 2 ^ l)
      ∧ liveSystem.toWrapperFrontier.capacity liveBobNode = 2 ^ 1 :=
  ⟨firstBob_capacity_dyadic liveSystem (by decide), by decide⟩

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), attained.**
`sum_v kappa_v = 2 + 1 + 1 = 4 = q`: Kraft is met with **equality** at the audit
instance, so the frontier is not a slack corner of the frozen bound. -/
theorem live_kraft_tight :
    ∑ v : FrontierNode liveProtocol liveRows 1 2,
        liveSystem.toWrapperFrontier.capacity v = 2 ^ 2 := by decide

/-! ### The weights, computed

Each frontier node is reached by exactly one coordinate, and no certificate ever
splits, so every derived kind is `clean` and every `W_v` is the clean weight `1`
of `09:1236`.  Each value is obtained by *evaluating* `frontierWeight` through
Aux A2, never assigned. -/

/-- **`09:1278--1280` at the live first-Bob node.**  Exactly one coordinate
reaches it. -/
theorem live_bobNode_unique_coord :
    ∀ i : Fin 3, liveBobNode.val ∈ coordRoutes liveProtocol liveRows 1 2 i ↔ i = 2 := by decide

/-- **`09:1278--1280` at the first final Alice node.** -/
theorem live_finalNodeZero_unique_coord :
    ∀ i : Fin 3, liveFinalNodeZero.val ∈ coordRoutes liveProtocol liveRows 1 2 i ↔ i = 0 := by
  decide

/-- **`09:1278--1280` at the second final Alice node.** -/
theorem live_finalNodeOne_unique_coord :
    ∀ i : Fin 3, liveFinalNodeOne.val ∈ coordRoutes liveProtocol liveRows 1 2 i ↔ i = 1 := by
  decide

/-- **`09:1236`, `09:1245--1247` at the live first-Bob node.**  Nothing split above
it, so its derived kind is `clean`. -/
theorem live_bobNode_kind :
    kindAlong liveProtocol (liveRows 2) 1 2 liveBobNode.val = CertKind.clean := by decide

/-- **`09:1236`, `09:1245--1247` at the first final Alice node.** -/
theorem live_finalNodeZero_kind :
    kindAlong liveProtocol (liveRows 0) 1 2 liveFinalNodeZero.val = CertKind.clean := by decide

/-- **`09:1236`, `09:1245--1247` at the second final Alice node.** -/
theorem live_finalNodeOne_kind :
    kindAlong liveProtocol (liveRows 1) 1 2 liveFinalNodeOne.val = CertKind.clean := by decide

/-- **`09:1257` evaluated at the live first-Bob node.**  `W_v = 1`. -/
theorem live_frontierWeight_bobNode :
    frontierWeight liveProtocol liveRows 1 2 liveBobNode = 1 := by
  rw [frontierWeight_eq_weight_of_unique_coord liveProtocol liveRows 1 2 liveBobNode
      live_bobNode_unique_coord, live_bobNode_kind]
  norm_num [CertKind.weight]

/-- **`09:1257` evaluated at the first final Alice node.**  `W_v = 1`. -/
theorem live_frontierWeight_finalNodeZero :
    frontierWeight liveProtocol liveRows 1 2 liveFinalNodeZero = 1 := by
  rw [frontierWeight_eq_weight_of_unique_coord liveProtocol liveRows 1 2 liveFinalNodeZero
      live_finalNodeZero_unique_coord, live_finalNodeZero_kind]
  norm_num [CertKind.weight]

/-- **`09:1257` evaluated at the second final Alice node.**  `W_v = 1`. -/
theorem live_frontierWeight_finalNodeOne :
    frontierWeight liveProtocol liveRows 1 2 liveFinalNodeOne = 1 := by
  rw [frontierWeight_eq_weight_of_unique_coord liveProtocol liveRows 1 2 liveFinalNodeOne
      live_finalNodeOne_unique_coord, live_finalNodeOne_kind]
  norm_num [CertKind.weight]

/-! ### The two binders of `canonical_cleanCount`, supplied live -/

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) at the audit instance -- a
REAL inequality.**

`W_v = 1 <= vartheta . kappa_v = (9/16) . 2 = 9/8` at the single first-Bob node.
Both sides are strictly positive and the bound has genuine slack, so the frozen
light condition is *checked* here rather than satisfied by an empty quantifier
(contrast `FrontierIndexing.canonical_cleanCount_consistent`, where
`bobNodes = {}`).

**On the relation `<=` versus `<`.**  The frozen display `09:1309--1313` is the
**strict** `W_v < vartheta kappa_v`; the banked `wrapperCleanCount`, and with it
`canonical_cleanCount`, consumes the weaker non-strict binder, which is what this
statement matches at that interface.  The audit instance satisfies the frozen
**strict** form as well, and `live_hlight_is_not_vacuous` records that separately
so that nothing here is read as a weakening of the frozen display.

**This supplies the binder at one audit instance; it does not discharge
`eq:wrapper-first-bob-light` in general.** -/
theorem live_hlight :
    ∀ v ∈ liveSystem.toWrapperFrontier.bobNodes,
      frontierWeight liveProtocol liveRows 1 2 v
        ≤ vartheta * ((liveSystem.toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  intro v hv
  rw [live_bobNodes, Finset.mem_singleton] at hv
  subst hv
  rw [live_frontierWeight_bobNode, live_kappa_attained]
  norm_num [vartheta]

/-- **The final-node classification of `09:1346--1350` at the audit instance.**

Both final Alice nodes carry exactly one clean certificate, so
`W_v = 1 = finalWeight (some clean)` there.  This is the shape
`lem:final-reference-uniqueness` (`09:1315--1344`) licenses -- "every final Alice
node contains either one clean certificate, one half-weight descendant of a split
certificate, or none" -- and it is *verified* here rather than assumed, because
`live_finalNodeZero_unique_coord` and `live_finalNodeOne_unique_coord` are
computed from the routing.

**This supplies the binder at one audit instance; it does not discharge
`lem:final-reference-uniqueness` in general.** -/
theorem live_hfinal :
    ∀ v ∈ liveSystem.toWrapperFrontier.finalNodes,
      frontierWeight liveProtocol liveRows 1 2 v
        ≤ finalWeight ((fun _ => some CertKind.clean) v) := by
  intro v hv
  rw [live_finalNodes] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · rw [live_frontierWeight_finalNodeZero]; norm_num
  · rw [live_frontierWeight_finalNodeOne]; norm_num

/-! ### `eq:wrapper-clean-count` re-run at the live instance -/

/-- **`09:1347--1348`, `K_B`, at the audit instance.**  `K_B = kappa_v = 2` --
**positive**, where the predecessor's instance had `K_B = 0`. -/
theorem live_bobCapacity : liveSystem.toWrapperFrontier.bobCapacity = 2 := by
  rw [WrapperFrontier.bobCapacity, live_bobNodes, Finset.sum_singleton, live_kappa_attained]
  norm_num

/-- **`09:1348--1349`, `c`, at the audit instance.** -/
theorem live_cleanNodes_card :
    (liveSystem.toWrapperFrontier.cleanNodes (fun _ => some CertKind.clean)).card = 2 := by decide

/-- **`09:1349--1350`, `ell`, at the audit instance.**  No certificate ever split,
so the half-weight column is empty. -/
theorem live_splitNodes_card :
    (liveSystem.toWrapperFrontier.splitNodes (fun _ => some CertKind.clean)).card = 0 := by decide

/-- **`eq:wrapper-clean-count` (`09:1352--1357`) re-run at the live first-Bob
instance.**

The banked `FrontierIndexing.canonical_cleanCount` -- itself the banked
`DenseWrapperFrontier.wrapperCleanCount` with the conservation binder already
retired -- applied verbatim at its own interface to the audit instance, with
`q = 4` **derived** from `09:105` at `r = 2` and with the self-chosen `e_0 = 1`.
Both remaining binders are supplied live: `hlight` at a **nonempty** first-Bob
set, `hfinal` at two verified final nodes.

The frozen coordinate count `hcoord` of `09:1235--1236` holds with equality here:
`q - e_0 = 3 = |Coord|`, three coordinates started outside `E_0`.

**BEYOND-PAPER AUDIT**, per the module header. -/
theorem live_cleanCount :
    (4 : ℝ) - 1 / (1 - vartheta)
        ≤ ((liveSystem.toWrapperFrontier.cleanNodes (fun _ => some CertKind.clean)).card : ℝ)
      ∧ liveSystem.toWrapperFrontier.bobCapacity
          + ((liveSystem.toWrapperFrontier.splitNodes (fun _ => some CertKind.clean)).card : ℝ)
        ≤ 1 / (1 - vartheta) :=
  canonical_cleanCount live_hcomp live_hR (fun _ => some CertKind.clean)
    (q := 4) (e0 := 1) (by norm_num) (by norm_num [Fintype.card_fin]) live_hlight live_hfinal

/-- **The first conjunct of `eq:wrapper-clean-count` is LIVE at the audit
instance: its left-hand side is POSITIVE.**

`q - e_0/(1-vartheta) = 4 - 16/7 = 12/7 > 0`, and the clean count is `c = 2`, so
the first frozen conclusion is a genuine lower bound that the instance clears
with room -- not an inequality made true by a nonpositive left-hand side.  The
second conjunct is likewise live: `K_B + ell = 2 + 0 = 2 <= 16/7`, with
`K_B = 2 > 0` because the first-Bob set is nonempty. -/
theorem live_cleanCount_positive_lhs :
    (0 : ℝ) < 4 - 1 / (1 - vartheta)
      ∧ (4 : ℝ) - 1 / (1 - vartheta)
          ≤ ((liveSystem.toWrapperFrontier.cleanNodes (fun _ => some CertKind.clean)).card : ℝ)
      ∧ (0 : ℝ) < liveSystem.toWrapperFrontier.bobCapacity
      ∧ liveSystem.toWrapperFrontier.bobCapacity
          + ((liveSystem.toWrapperFrontier.splitNodes (fun _ => some CertKind.clean)).card : ℝ)
        ≤ 1 / (1 - vartheta) := by
  obtain ⟨h1, h2⟩ := live_cleanCount
  refine ⟨by norm_num [vartheta], h1, ?_, h2⟩
  rw [live_bobCapacity]; norm_num

end LiveInstance

/-! ## §4  Statement poles

A green build sees none of this. -/

section Poles

/-- **Statement pole: `hlight` is not vacuous here.**

The predecessor's consistency instance discharged `eq:wrapper-first-bob-light` by
`absurd` on an empty `bobNodes`; at the live instance the quantifier ranges over a
nonempty set, and the inequality is checked at a node whose `kappa_v` attains the
frozen floor `2`.  Both facts together are what item (11) asked for. -/
theorem live_hlight_is_not_vacuous :
    liveSystem.toWrapperFrontier.bobNodes.Nonempty
      ∧ liveSystem.toWrapperFrontier.capacity liveBobNode = 2
      ∧ frontierWeight liveProtocol liveRows 1 2 liveBobNode
          < vartheta * ((liveSystem.toWrapperFrontier.capacity liveBobNode : ℕ) : ℝ) := by
  refine ⟨⟨liveBobNode, by rw [live_bobNodes]; exact Finset.mem_singleton_self _⟩,
    live_kappa_attained, ?_⟩
  rw [live_frontierWeight_bobNode, live_kappa_attained]
  norm_num [vartheta]

/-- **Statement pole: the frozen light bound is a real constraint at `kappa_v = 2`.**

`vartheta . 2 = 9/8 < 2`.  So a first-Bob node of capacity `2` reached by **two**
clean certificates would carry `W_v = 2` and violate
`eq:wrapper-first-bob-light`: the bound is not automatic, and the live node
satisfies it only because exactly one coordinate reaches it
(`live_bobNode_unique_coord`).  The frozen `09:1278--1280` uniqueness is
therefore load-bearing at this node, not decoration. -/
theorem firstBobLight_pole_two_clean_certificates :
    ¬ ((2 : ℝ) ≤ vartheta * ((2 : ℕ) : ℝ)) := by norm_num [vartheta]

/-- **Statement pole: a positive first-conjunct LHS is what makes the first frozen
conclusion say anything.**

At `e_0 = 2` and the same `q = 4` the first conjunct reads
`4 - 32/7 = -4/7 <= c`, which **every** cardinality satisfies, so the conclusion
carries no information there.  The audit instance is run at `e_0 = 1`, where the
left-hand side is `12/7 > 0` and the conclusion genuinely constrains `c`. -/
theorem live_cleanCount_first_conjunct_is_live :
    (4 : ℝ) - 2 / (1 - vartheta) < 0
      ∧ (∀ c : ℕ, (4 : ℝ) - 2 / (1 - vartheta) ≤ (c : ℝ))
      ∧ (0 : ℝ) < 4 - 1 / (1 - vartheta) := by
  refine ⟨by norm_num [vartheta], fun c => ?_, by norm_num [vartheta]⟩
  have : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have h : (4 : ℝ) - 2 / (1 - vartheta) < 0 := by norm_num [vartheta]
  linarith

end Poles

end EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
