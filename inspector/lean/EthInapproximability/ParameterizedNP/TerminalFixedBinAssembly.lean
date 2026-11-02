import EthInapproximability.ParameterizedNP.TerminalResidualComparison

/-!
# Parameterized NP route: the phase-1 assembly of `eq:terminal-fixed-bin`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 862--1033** -- the
  first of the two phases the frozen proof of `lem:terminal-two-stream`
  announces at `09:867--868`, ending at `eq:terminal-fixed-bin`
  (`09:1030--1033`), whose consumption in the Stage-3 lift is `09:1101--1103`.
  The anchors this module traces, in the frozen print order:
  * `09:916--923`, the fixed-bin frame and the **contradiction hypothesis**:
    "Fix the pair of Stage-3 template bins in clause (ii) of
    `def:two-stream-state` and work inside one of them.  Transpose this
    fixed-bin state, and suppose for contradiction that the resulting matrix has
    a protocol `P_2` of depth at most `D_2`.  Until `eq:terminal-fixed-bin`,
    every remaining-budget reference is to the suffix depth in `P_2`."
  * `09:937--938`, the stopping rule: "Put `r_2 = log_2 q_2`.  Stop a token at
    the first Alice query or when its Stage-2 coordinate is isolated."
  * `09:943--948`, the one-copy residual certificate: "At any such node, project
    to the coordinate carried by an ordinary token and transpose the resulting
    local block.  Its surviving `C_1`-support is the row restriction of
    `M = M_1^T`, and the retained typed projection is its column restriction.
    Both have the thresholds in `eq:stage1-robust-certificate`, so one-copy
    robustness gives residual complexity `B_cap`."
  * `09:948--951`, the isolated case and the top two-copy rung: "If the
    coordinate is isolated, this is exactly the surviving local block; an unsplit
    attached pair there has residual complexity `B_cap + 1` by the inherited top
    two-copy rung.  In particular, no routed token can end at a protocol leaf at
    a depth at most `r_2`."
  * `09:953--965`, the isolation-node bookkeeping and `h_v + z_v <= kappa_v`.
  * `09:967--978`, the premature-leaf exclusion at depth `r_2 + 1`.
  * `09:980--994`, the frontier substitution producing `eq:terminal-first-alice`.
  * `eq:terminal-stage2-budget` (label `09:1001`, display `09:998--1002`).
  * `09:1014--1028`, the three-case Extension dispatch and its closing sentence
    "In every case one Alice child has complexity at least `B_cap + log_2
    kappa_v`, which exceeds `eq:terminal-stage2-budget`."
  * `eq:terminal-fixed-bin` (label `09:1032`, display `09:1030--1033`).
* **Cross-anchors opened first-hand for this tranche:** `09:834--860`
  (`lem:terminal-two-stream`'s statement), `09:1035--1173` (the Stage-3 lift,
  read only to confirm that `09:1101--1103` *consumes* `eq:terminal-fixed-bin`),
  `A-certified-stopping.tex:109--146` (`thm:certified-localized-extension` and
  its conclusion `eq:certified-E3`, read to census what the `kappa_v >= t_2`
  branch of `09:1014--1019` needs), and `A-certified-stopping.tex:148--200`
  (`lem:certified-row-ladder`, the branch `09:1020` uses).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively; the sole import is
  `TerminalResidualComparison`, whose ledger row records the same exclusion.

## What this tranche is, in one sentence

It is the **assembly attempt** for `eq:terminal-fixed-bin`: it wires the T1
residual comparisons of `TerminalResidualComparison` (the development's largest
unwired block) into the Stage-2 stopping frontier, the isolation capacity and the
weighted-frontier substitution, lands the R6 narrowing of `denseNoLeaf`'s section
bundle as an adapter, and then **reports precisely where the chain stops**.

## The verdict of the assembly: the chain does *not* close

`TerminalFixedBin.FixedBinLowerBound` is **not** proved here, and no declaration
below has it as a conclusion.  That is a finding, not an omission, and the census
is exact.  Writing `->` for "is now discharged" and `X` for "is not available":

1. `->` **the residual comparison** at every address (`09:919--921`): T1's
   `D_le_cost_descend_of_computes`, consumed by pin.  Every `hresidual`,
   `hnodeResidual`, `hdeepResidual` and gated `hres` binder of the Stage-2 blocks
   is discharged below from `Protocol.Computes` alone.
2. `->` **the one-copy certificate** (`09:943--948`) and **the top two-copy rung**
   (`09:949--950`): `TerminalCertificateInputs.oneCopy_residual_at_seed_floor`
   and `.topTwoCopy_residual_at_pair_floor`, both proved, consumed by pin.
3. `->` **the no-leaf clause and the depth bound** (`09:951`, `09:967--978`):
   `stage2_frontier_from_certificates`, from the alleged protocol.
4. `->` **`h_v + z_v <= kappa_v`** (`09:953--965`):
   `stage2_isolation_capacity_from_certificates`, from the alleged protocol.
5. `->` **`eq:terminal-first-alice`** (`09:980--994`):
   `terminal_first_alice_from_protocol` derives it with `hisocap` **discharged**
   by item 4, leaving only the routing bookkeeping binder `hwitness`.
6. `->` **the closing budget comparison** (`09:1023--1028`, `09:996--1002`):
   `stage2_no_alleged_protocol_at_forced_child`.
7. `->` **contradiction to bound** (`09:1030--1033`): `lt_D_of_every_protocol_absurd`
   turns "no alleged protocol of depth `D_2`" into `D_2 + 1 <= comp`.

**X 8. `eq:certified-E3` is asserted nowhere in the development.**  The frozen
dispatch of `09:1014--1019` sends the branch `kappa_v >= t_2` to
`thm:certified-localized-extension` (`A-certified-stopping.tex:109--146`), whose
conclusion `H + log_2(r' t)` is the *only* source of the Alice child's residual
lower bound in that branch.  `TerminalTwoStream` records the same exclusion, and
this module does not change it: the child certificate stays the named binder
`hchild` of item 6.

**X 9. The routed object system is not constructed from a protocol.**  Items 3--5
all quantify over *given* stopped tokens, arrivals `arr`, routes and isolation
predicates.  The frozen proof **builds** them: it places one ordinary token on
each coordinate of `H` and one bonus token on each coordinate of `Z`
(`09:923--925`), routes each through Bob queries by the split-or-route rule
(`09:930--935`), and stops it by `09:937--938`.  Nothing in the development
produces a `StoppedToken` family, an arrival family, or the frontier's
prefix-freeness *from* an arbitrary protocol; `hwitness` (`09:986--988`) is the
same gap seen from the counting side.

Items 8 and 9 are jointly what a genuine proof of `eq:terminal-fixed-bin` still
needs.  Because they are missing, **no theorem below concludes
`FixedBinLowerBound`, and none takes it, or `eq:terminal-first-alice`, as a
hypothesis in order to conclude the phase-1 target.**  A theorem of the shape
"assume the frontier verdict, conclude `D_2 + 1`" would typecheck and establish
nothing; that is the statement pole `TerminalFixedBin` already refuses and this
module continues to refuse.  What item 6 does instead is the frozen *reductio*:
it derives `False` from the alleged protocol together with the one genuinely
external certificate `hchild`, which is exactly how `Stage3ProtocolRouting`
already binds it.

## The R6 narrowing (the named repair this tranche was asked to land)

`TerminalResidualComparison.denseNoLeaf_of_alleged_protocol` closes the banked
`denseNoLeaf`'s two residual binders, but it demands the node-game section data
`A p`, `B p`, `iotaA p`, `iotaB p`, `hrow p`, `hcol p`, `hgame p` at **every**
address `p : List Bool`, while the frozen proof reads the node game only at
`t.route` (`09:943--948`) and at `t.route.take (r + 1)` (`09:967--978`).  Its own
verify-seat note (finding R6 of `cc-t4o`) asks the consuming assembly to narrow
the bundle to those two addresses.  `denseNoLeaf_at_stop_addresses` is that
narrowing: two carrier pairs, two games, two section pairs, two route facts, two
game identifications, and the frozen gates unchanged.
`denseNoLeaf_of_alleged_protocol_of_narrow` proves the narrowing loses nothing --
the banked wide form is recovered from it by instantiation -- so the adapter is
a strict improvement rather than a different lemma.

## Predecessor modules consumed **by pin**, never restated

* `TerminalResidualComparison`: `RouteRows`, `RouteCols`, `routeRows_nil`,
  `routeCols_nil`, `D_le_cost_descend_of_computes`,
  `denseNoLeaf_of_alleged_protocol` (recovered, not restated).
* `TerminalCertificateInputs`: `liftRows`, `pairRows`, `pairFloor`,
  `oneCopy_residual_at_seed_floor`, `topTwoCopy_residual_at_pair_floor`.
* `Stage3ProtocolRouting`: `stage2_isolation_capacity_from_protocol`,
  `stage2_alice_child_budget_contradiction`.
* `TerminalFixedBin`: `terminal_first_alice`, `fixedBinTarget`,
  `FixedBinLowerBound` (named in prose only; **not** a conclusion or a hypothesis
  of any declaration here).
* `DenseWeightedCount`: `StoppedToken`, `StopEvent`, `denseNoLeaf_depth_le`,
  `denseNoLeaf_event_ne_atLeaf`, `descend`, `descendStep`, `IsQueryPath`,
  `IsQueryNode`, `stoppingCapacity`, `isolationNodes`, `aliceNodes`,
  `PrefixFreeFrontier`, `trim_to_seed_floor`, `probeProtocol`, `probeToken`.
* `DenseFrontierConservation`: `FrontierArrival`, `hMass`, `zMass`,
  `zMass_le_hMass`, `witnessCount`.
* `Workspace.Types.CommComplexity.D`, `AchievableCosts`,
  `Workspace.UpperBound.AchievableCosts_nonempty`, `Workspace.Types.Protocol`,
  `NPCC.subgame`, `Workspace.Types.Interlace.interlaceFun` -- the vendored,
  project-axiom-free interface reached through `LegacyNPCC.Core`.

## Reader counterparts

The 41-page reader artifact of the same frozen release was swept first-hand this
tranche (`reader-facing/sections/`, all nine files).  **This module claims no
reader item, deliberately rather than by omission**, with two declinations:

* `A-stage4-details.tex:370--373`, "For the near-full rung, inspect an arbitrary
  protocol for the retained interlace.  Before its terminal frontier, the
  all-column reference follows every Bob query and its one-bit-down certificate
  prevents an early cheap termination", is the nearest reader sentence to the
  reductio frame and the no-premature-leaf clause.  It is declined twice over:
  it is unlabelled proof prose, and the reader-counterpart rule bars citing prose
  as a statement counterpart; and `371--373` is already recorded as
  navigation-only by `RoutedCertificateSystem`, `FirstBobFrontierInstance`,
  `SplitFirstBobInstance`, `FrontierIndexing` and `MassRedistributionCounting`,
  and a reader item may not be assigned twice.
* `A-stage4-details.tex:387--390` ("At the frontier, the two-stream lemma
  combines ... to contribute the missing bit") is the reader's entire
  condensation of `09:862--1033`; it is already recorded by `TerminalFixedBin`,
  and line `391` is already assigned to `TerminalTwoStream`'s certified-row-ladder
  group.  Declined.

The reader prints `D_2`, `kappa_v`, `49/128`, `9/25`, "fixed bin" and both budget
displays **nowhere**; the reader itself says at lines `396--399` that the count
"is expanded line by line in the ultra-explicit companion", which is the frozen
`09:862--1033` traced here.

## Canonical inhabitation

The object every declaration below quantifies over is the frozen proof's
**alleged** protocol `P_2`, introduced at `09:918--919` by "suppose for
contradiction".  The paper never constructs it -- it derives a contradiction from
the assumption that one exists -- so there is no paper instance to exhibit, and
this module is scaffolding in the precise sense: statements about a hypothetical
object.  The same reading is recorded by `TerminalResidualComparison` for its own
apparatus, and it is why the concrete readouts below are labelled
**NON-FIDELITY**: they evaluate our encoding at a two-bit probe protocol the
frozen paper never visits, and are never evidence that the terminal regime is
inhabited.

No **new** structure, record or premise bundle is introduced by this module, so
no new non-vacuity obligation is created: every hypothesis below is an explicit
binder, and every carrier it mentions is a banked one whose inhabitation its own
ledger row already records.

## Aux-lemma battery

Every battery item is **proved**; nothing is stated and left open.

* `A` the reductio frame, general (4): `exists_alleged_protocol`,
  `alleged_protocol_cost_eq`, `exists_alleged_protocol_mono`,
  `lt_D_of_every_protocol_absurd`.
* `B` the R6 narrowing, general (2): `denseNoLeaf_at_stop_addresses`,
  `denseNoLeaf_of_alleged_protocol_of_narrow`.
* `C` the Stage-2 frontier and the isolation capacity, general (2):
  `stage2_frontier_from_certificates`,
  `stage2_isolation_capacity_from_certificates`.
* `D` the frontier substitution and the close, general (2):
  `terminal_first_alice_from_protocol`,
  `stage2_no_alleged_protocol_at_forced_child`.

That is **10 general battery entries proved**, with `0` unproved, alongside
**three statement poles** (`alleged_protocol_frame_is_not_vacuous`,
`alice_child_certificate_is_not_free`, `assembly_does_not_reach_the_phase_one_target`)
and **two NON-FIDELITY readouts** (`denseNoLeaf_at_stop_addresses_at_probe`,
`narrowed_bundle_is_inhabited_at_probe`).

## HYPOTHESIS-CONSISTENCY note

No new headline theorem is introduced.  The two theorems with a nontrivial binder
bundle are `stage2_frontier_from_certificates` and
`terminal_first_alice_from_protocol`, and both are **compositions**: their binder
sets are the unions of binder sets whose joint consistency the predecessor modules
already record (`DenseWeightedCount.denseNoLeaf_hypotheses_consistent`,
`TerminalCertificateInputs.certificate_floors_are_satisfiable`,
`TerminalCertificateInputs.topTwoCopy_hypotheses_consistent`,
`TerminalFixedBin.fixedBinLowerBound_arith_hypotheses_consistent`), plus the
`Protocol.Computes` clause and the section data, which
`denseNoLeaf_at_stop_addresses_at_probe` exhibits simultaneously with the rest at
a concrete protocol.  No conjunction below pairs two frozen clauses the paper
states as separate cases: the two gates `t.route.length <= r_2` and
`r_2 + 1 <= t.route.length` are carried exactly as the banked `denseNoLeaf`
carries them, mutually exclusive and never conjoined.

Machine evidence, recorded by this generation
(`scratch/TerminalFixedBinAssemblyProbes.lean`, disposable, one `example`
expected to fail): probe 2 attempts `False` from the reductio frame at a
nondegenerate frozen regime -- a game whose complexity is at most
`D_2 = B_cap + log_2 q_2` at `B_cap = 5`, `r_2 = 7` -- with the alleged protocol
already extracted into context, and **fails**.  Probe 1 *does* close and is the
composition check: §4's conclusion is `hverdict` of §5 verbatim, at
`hmass := hMass arr`, `zmass := zMass arr`, with no reshaping, so the two halves
of the assembly really do meet.

## Dependencies, imports and adapters

* Import: `EthInapproximability.ParameterizedNP.TerminalResidualComparison` only.
* Proof status: **new** (§1 and §2 are new apparatus; §3--§5 are compositions of
  banked results with the T1 binders discharged).
* Unproved placeholders, new axioms and opaque certificates: **none**.
* `hDenseRung` is **neither discharged nor fed** by this module;
  `eq:wrapper-u-dense` is asserted nowhere, the ranges `09:1184--1366`,
  `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly as `ScaleAlignOpening`
  records them, and **no route completion is claimed**.
-/

namespace EthInapproximability.ParameterizedNP.TerminalFixedBinAssembly

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open NPCC
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.TerminalResidualComparison

/-! ## §1  The reductio frame of `09:918--919` and `09:1030--1033`

"suppose for contradiction that the resulting matrix has a protocol `P_2` of depth
at most `D_2`" ... "Consequently the fixed-bin state has complexity at least
`D_2 + 1`".

The frozen phase opens by *producing* a protocol from a complexity assumption and
closes by *converting* the absence of such a protocol into the bound one bit
above the budget.  Both directions are stated here, once, at the vendored
`D = sInf(AchievableCosts)`. -/

section Reductio

variable {A B : Type*} [Fintype A] [Fintype B]

/-- **`09:918--919`, the contradiction hypothesis as an object.**  If a finite
Boolean game has complexity at most `budget`, then some protocol of cost at most
`budget` computes it.  This is what "suppose for contradiction that the resulting
matrix has a protocol `P_2` of depth at most `D_2`" asserts, and it is a
consequence of the vendored definition of `D` rather than an extra assumption:
`AchievableCosts` is nonempty on finite carriers, so its infimum is attained.
General in both carriers and in the budget. -/
theorem exists_alleged_protocol (g : A → B → Bool) {budget : ℕ} (h : D g ≤ budget) :
    ∃ P : Protocol A B Bool, P.cost ≤ budget ∧ Protocol.Computes P g := by
  have hne : (AchievableCosts g).Nonempty := Workspace.UpperBound.AchievableCosts_nonempty g
  have hmem : D g ∈ AchievableCosts g := by
    simpa [D] using Nat.sInf_mem hne
  obtain ⟨P, hcost, hcomp⟩ := hmem
  exact ⟨P, by rw [hcost]; exact h, hcomp⟩

/-- **Aux A2 (identity instance).**  At the tight budget the produced protocol has
cost exactly `D g`: the frozen "depth at most `D_2`" is attained by the optimal
protocol, so nothing is lost by phrasing the reductio at an inequality.  General. -/
theorem alleged_protocol_cost_eq (g : A → B → Bool) :
    ∃ P : Protocol A B Bool, P.cost = D g ∧ Protocol.Computes P g := by
  have hne : (AchievableCosts g).Nonempty := Workspace.UpperBound.AchievableCosts_nonempty g
  have hmem : D g ∈ AchievableCosts g := by
    simpa [D] using Nat.sInf_mem hne
  obtain ⟨P, hcost, hcomp⟩ := hmem
  exact ⟨P, hcost, hcomp⟩

/-- **Aux A3 (monotonicity in the budget).**  A larger budget still produces the
alleged protocol, so the frame is not tied to the particular value `D_2`.
General. -/
theorem exists_alleged_protocol_mono (g : A → B → Bool) {budget budget' : ℕ}
    (hb : budget ≤ budget') (h : D g ≤ budget) :
    ∃ P : Protocol A B Bool, P.cost ≤ budget' ∧ Protocol.Computes P g :=
  exists_alleged_protocol g (le_trans h hb)

/-- **`09:1030--1033`, the reductio closed.**  "Consequently the fixed-bin state has
complexity at least `D_2 + 1`."

If **every** protocol of cost at most `budget` that computes `g` yields a
contradiction, then `g` has complexity at least `budget + 1`.  This is the exact
step by which the frozen phase converts its `09:918--919` reductio into
`eq:terminal-fixed-bin`, and it is where the `+ 1` of that display comes from.

*Why the hypothesis is not vacuous.*  It is a universally quantified statement
about a set that is generally inhabited: `alleged_protocol_frame_is_not_vacuous`
exhibits a game and a budget at which a protocol exists, so the hypothesis has to
be *earned* at every application site rather than holding for free.  General. -/
theorem lt_D_of_every_protocol_absurd (g : A → B → Bool) {budget : ℕ}
    (h : ∀ P : Protocol A B Bool, P.cost ≤ budget → Protocol.Computes P g → False) :
    budget + 1 ≤ D g := by
  by_contra hlt
  obtain ⟨P, hcost, hcomp⟩ := exists_alleged_protocol (budget := budget) g (by omega)
  exact h P hcost hcomp

end Reductio

/-! ## §2  The R6 narrowing of `lem:dense-no-leaf`'s section bundle
(`09:943--948`, `09:967--978`)

The banked `denseNoLeaf` reads the node game at two addresses only: the token's
own stopping node (`09:943--948`) and the length-`(r+1)` prefix of its route
(`09:967--978`).  `TerminalResidualComparison.denseNoLeaf_of_alleged_protocol`
discharged the two residual binders but demanded the section data at every
address; the adapter below demands it exactly where the frozen proof reads it. -/

section Narrowing

variable {X Y Coord An Bn Ad Bd : Type*} [Fintype An] [Fintype Bn] [Fintype Ad]
  [Fintype Bd]

/-- **`lem:dense-no-leaf` at the two frozen addresses (the R6 narrowing).**

"Every positive token stops at coordinate isolation or before its first Alice
query, and it does so at suffix depth at most `r`."

That sentence is `lem:dense-no-leaf` itself: label `08:956`, statement
`08:957--958`, with its premature-leaf clause at `08:974--978`.  The two
addresses below are where the terminal regime *consumes* it -- `09:943--948`
and `09:967--978` -- so both attributions are named here rather than only the
consumption site.

Same conclusion as `TerminalResidualComparison.denseNoLeaf_of_alleged_protocol`,
same discharge of the two residual binders from `Protocol.Computes`, but the node
games and their sections are demanded only at `t.route` (`09:943--948`) and at
`t.route.take (r + 1)` (`09:967--978`).  The two frozen gates are unchanged and
stay mutually exclusive: `hnodeHard` fires only at depth at most `r`, `hdeepHard`
only at depth at least `r + 1`, and the two are never conjoined.

The section triples are `09:943--946` read literally: `iotaA` picks the rows of
the local block inside the fixed-bin rows, `iotaB` its columns inside the
fixed-bin columns, and `hgame` is the frozen identification of the projected,
transposed local block with the ambient entry.  General in all six carriers, in
the protocol, in the token and in the two exponents. -/
theorem denseNoLeaf_at_stop_addresses
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool}
    (hcomp : Protocol.Computes Pstar gamb) (t : StoppedToken Pstar Coord)
    {r bcap : ℕ} (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r)
    (gnode : An → Bn → Bool) (iotaAn : An → X) (iotaBn : Bn → Y)
    (hrown : ∀ a : An, RouteRows Pstar t.route (iotaAn a))
    (hcoln : ∀ b : Bn, RouteCols Pstar t.route (iotaBn b))
    (hgamen : ∀ a b, gnode a b = gamb (iotaAn a) (iotaBn b))
    (hnodeHard : t.route.length ≤ r → bcap ≤ D gnode)
    (gdeep : Ad → Bd → Bool) (iotaAd : Ad → X) (iotaBd : Bd → Y)
    (hrowd : ∀ a : Ad, RouteRows Pstar (t.route.take (r + 1)) (iotaAd a))
    (hcold : ∀ b : Bd, RouteCols Pstar (t.route.take (r + 1)) (iotaBd b))
    (hgamed : ∀ a b, gdeep a b = gamb (iotaAd a) (iotaBd b))
    (hdeepHard : r + 1 ≤ t.route.length → bcap ≤ D gdeep) :
    (t.event = StopEvent.isolation ∨ t.event = StopEvent.beforeAlice)
      ∧ t.route.length ≤ r := by
  have hshallow : t.route.length ≤ r :=
    denseNoLeaf_depth_le (A := fun _ => Ad) (B := fun _ => Bd) (fun _ => gdeep) t hbudget
      hdeepHard
      (fun _ => D_le_cost_descend_of_computes hcomp iotaAd iotaBd hrowd hcold hgamed)
  have hne : t.event ≠ StopEvent.atLeaf :=
    denseNoLeaf_event_ne_atLeaf (A := fun _ => An) (B := fun _ => Bn) (fun _ => gnode) t
      hbcap hshallow hnodeHard
      (fun _ => D_le_cost_descend_of_computes hcomp iotaAn iotaBn hrown hcoln hgamen)
  refine ⟨?_, hshallow⟩
  rcases t.event_cases with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hne

/-- **Aux B2 (the narrowing loses nothing).**  The banked wide form
`TerminalResidualComparison.denseNoLeaf_of_alleged_protocol` -- which demands the
section data at *every* address -- is recovered from the adapter by instantiating
its families at the two frozen addresses.  So the narrowed bundle is a genuine
weakening of the hypotheses and not a different lemma: anything the wide form
proves, the adapter proves.  General. -/
theorem denseNoLeaf_of_alleged_protocol_of_narrow
    {A B : List Bool → Type*} [∀ p, Fintype (A p)] [∀ p, Fintype (B p)]
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool}
    (hcomp : Protocol.Computes Pstar gamb) (g : ∀ p : List Bool, A p → B p → Bool)
    (iotaA : ∀ p : List Bool, A p → X) (iotaB : ∀ p : List Bool, B p → Y)
    (hrow : ∀ (p : List Bool) (a : A p), RouteRows Pstar p (iotaA p a))
    (hcol : ∀ (p : List Bool) (b : B p), RouteCols Pstar p (iotaB p b))
    (hgame : ∀ (p : List Bool) (a : A p) (b : B p),
      g p a b = gamb (iotaA p a) (iotaB p b))
    (t : StoppedToken Pstar Coord) {r bcap : ℕ}
    (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r)
    (hnodeHard : t.route.length ≤ r → bcap ≤ D (g t.route))
    (hdeepHard : r + 1 ≤ t.route.length → bcap ≤ D (g (t.route.take (r + 1)))) :
    (t.event = StopEvent.isolation ∨ t.event = StopEvent.beforeAlice)
      ∧ t.route.length ≤ r :=
  denseNoLeaf_at_stop_addresses hcomp t hbcap hbudget
    (g t.route) (iotaA t.route) (iotaB t.route) (hrow t.route) (hcol t.route)
    (hgame t.route) hnodeHard
    (g (t.route.take (r + 1))) (iotaA (t.route.take (r + 1)))
    (iotaB (t.route.take (r + 1))) (hrow (t.route.take (r + 1)))
    (hcol (t.route.take (r + 1))) (hgame (t.route.take (r + 1))) hdeepHard

end Narrowing

/-! ## §3  The Stage-2 frontier with **both** T1 binders discharged
(`09:937--978`)

"Put `r_2 = log_2 q_2`.  Stop a token at the first Alice query or when its Stage-2
coordinate is isolated. ...  Both have the thresholds in
`eq:stage1-robust-certificate`, so one-copy robustness gives residual complexity
`B_cap`. ...  In particular, no routed token can end at a protocol leaf at a depth
at most `r_2`."

`Stage3ProtocolRouting.stage2_routed_token_frontier` left `honeCopy` and
`hresidual` as binders.  Both are discharged here: the certificate by
`TerminalCertificateInputs.oneCopy_residual_at_seed_floor` through the banked
trim, and the residual reading by T1 through `Protocol.Computes`. -/

section StageTwoFrontier

variable {X Y Coord Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone] [Fintype Rone]

/-- **`09:937--978` from the alleged protocol alone, PROVED.**

The token's node game and the game at the length-`(r_2+1)` prefix are the frozen
local blocks of `M = M_1^T` at `09:943--946`: the one-copy interlace restricted to
the lifted surviving `C_1`-support and to the retained typed projection.  The two
row hypotheses are the banked routing-floor invariant at the two frozen depths,
gated exactly as the frozen proof gates them; the two column hypotheses are the
frozen ceiling at `y`; `hseed` is the first clause of `eq:terminal-seed-inputs`
(`09:847`).

Everything else is discharged: the one-copy certificate through
`DenseWeightedCount.trim_to_seed_floor` and
`TerminalCertificateInputs.oneCopy_residual_at_seed_floor`, and *both* residual
readings through the T1 comparison.  No `hresidual` or `honeCopy` binder
survives.  General in all five carriers and in the four exponents. -/
theorem stage2_frontier_from_certificates
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool}
    (hcomp : Protocol.Computes Pstar gamb) (M1T : Cone → Rone → Bool)
    (t : StoppedToken Pstar Coord) {r₂ b₁ bcap : ℕ} {y : ℝ}
    (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) y)
    {Tn Td : Finset Cone} {Cn Cd : Finset (Slot 1 → Rone)}
    (hTn : t.route.length ≤ r₂ →
      DenseRoutingInvariant.routingFloor Cone (2 ^ r₂) b₁ t.route.length ≤ Tn.card)
    (hCn : ⌈((Fintype.card Rone : ℝ) ^ 1) * y⌉₊ ≤ Cn.card)
    (iotaAn : {a // a ∈ TerminalCertificateInputs.liftRows Tn} → X)
    (iotaBn : {c // c ∈ Cn} → Y)
    (hrown : ∀ a, RouteRows Pstar t.route (iotaAn a))
    (hcoln : ∀ b, RouteCols Pstar t.route (iotaBn b))
    (hgamen : ∀ a b,
      subgame (interlaceFun M1T 1) (TerminalCertificateInputs.liftRows Tn) Cn a b
        = gamb (iotaAn a) (iotaBn b))
    (hTd : r₂ + 1 ≤ t.route.length →
      DenseRoutingInvariant.routingFloor Cone (2 ^ r₂) b₁ (r₂ + 1) ≤ Td.card)
    (hCd : ⌈((Fintype.card Rone : ℝ) ^ 1) * y⌉₊ ≤ Cd.card)
    (iotaAd : {a // a ∈ TerminalCertificateInputs.liftRows Td} → X)
    (iotaBd : {c // c ∈ Cd} → Y)
    (hrowd : ∀ a, RouteRows Pstar (t.route.take (r₂ + 1)) (iotaAd a))
    (hcold : ∀ b, RouteCols Pstar (t.route.take (r₂ + 1)) (iotaBd b))
    (hgamed : ∀ a b,
      subgame (interlaceFun M1T 1) (TerminalCertificateInputs.liftRows Td) Cd a b
        = gamb (iotaAd a) (iotaBd b)) :
    (t.event = StopEvent.isolation ∨ t.event = StopEvent.beforeAlice)
      ∧ t.route.length ≤ r₂ :=
  denseNoLeaf_at_stop_addresses hcomp t hbcap hbudget
    (subgame (interlaceFun M1T 1) (TerminalCertificateInputs.liftRows Tn) Cn)
    iotaAn iotaBn hrown hcoln hgamen
    (fun h => TerminalCertificateInputs.oneCopy_residual_at_seed_floor M1T hseed
      (DenseWeightedCount.trim_to_seed_floor (hTn h) (by omega)) hCn)
    (subgame (interlaceFun M1T 1) (TerminalCertificateInputs.liftRows Td) Cd)
    iotaAd iotaBd hrowd hcold hgamed
    (fun h => TerminalCertificateInputs.oneCopy_residual_at_seed_floor M1T hseed
      (DenseWeightedCount.trim_to_seed_floor (hTd h) le_rfl) hCd)

/-- **`09:953--965` from the alleged protocol alone, PROVED.**

"Coordinatewise uniqueness leaves at most one routed object there.  An ordinary
object contributes one token, hence at most `kappa_v`.  An unsplit attached pair
contributes two tokens and can occur only when `kappa_v >= 2` ...  Thus
`h_v + z_v <= kappa_v` at every isolation node."

`Stage3ProtocolRouting.stage2_isolation_capacity_from_protocol` left the pair
certificate `hpair` and its residual reading `hres` as binders.  Both are
discharged: the `B_cap + 1` rung by
`TerminalCertificateInputs.topTwoCopy_residual_at_pair_floor` (the `ell = 1`
instance of `lem:certified-row-ladder`), and the residual reading by T1.  The two
frozen clauses that stay named are `huniq` (coordinatewise uniqueness,
`09:955--956`, a coverage limit of the banked `DenseRoutingInvariant`) and `hz`.
Both pair-floor hypotheses are gated on `0 < z`, so nothing is assumed at a node
carrying no bonus component.  General. -/
theorem stage2_isolation_capacity_from_certificates
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool} {p : List Bool}
    {bcap r₂ b₁ h z : ℕ}
    (hcomp : Protocol.Computes Pstar gamb) (M1T : Cone → Rone → Bool)
    (huniq : h ≤ 1) (hz : z ≤ h)
    (hpath : IsQueryPath Pstar p)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone) (hH : 2 ≤ bcap)
    (hlegal : 2 * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    {To Tf : Finset Cone} {Cp : Finset (Slot 2 → Rone)}
    (hTo : 0 < z → TerminalCertificateInputs.pairFloor Cone b₁ ≤ To.card)
    (hTf : 0 < z → TerminalCertificateInputs.pairFloor Cone b₁ ≤ Tf.card)
    (hCp : ⌈((Fintype.card Rone : ℝ) ^ 2) * (9 / 25)⌉₊ ≤ Cp.card)
    (iotaA : {a // a ∈ TerminalCertificateInputs.pairRows To Tf} → X)
    (iotaB : {c // c ∈ Cp} → Y)
    (hrow : ∀ a, RouteRows Pstar p (iotaA a))
    (hcol : ∀ b, RouteCols Pstar p (iotaB b))
    (hgame : ∀ a b,
      subgame (interlaceFun M1T 2) (TerminalCertificateInputs.pairRows To Tf) Cp a b
        = gamb (iotaA a) (iotaB b)) :
    h + z ≤ DenseWeightedCount.stoppingCapacity r₂ p.length :=
  Stage3ProtocolRouting.stage2_isolation_capacity_from_protocol huniq hz hpath hbudget
    (fun hzpos => TerminalCertificateInputs.topTwoCopy_residual_at_pair_floor M1T hX hY
      hH hlegal hseed (hTo hzpos) (hTf hzpos) hCp)
    (fun _ => D_le_cost_descend_of_computes hcomp iotaA iotaB hrow hcol hgame)

end StageTwoFrontier

/-! ## §4  `eq:terminal-first-alice` with `hisocap` discharged (`09:980--994`)

"The proof of `lem:dense-weighted-frontier` uses only one ordinary component per
good coordinate, one attached bonus component per witness coordinate, the
split-or-route support rule above, and the exclusion of premature leaves.  All
four properties hold for the present labelled fibres.  Substituting witness count
`|Z|` and bad count `b`, and then using `eq:terminal-excess`, shows that some
first-Alice node satisfies `eq:terminal-first-alice`."

`TerminalFixedBin.terminal_first_alice` already discharges the width hypothesis
and the counting gap; it left `hwitness` and `hisocap` as binders.  `hisocap` is
discharged here from the alleged protocol by §3's isolation capacity, applied at
every isolation node.  `hwitness` (`09:986--988`) stays a binder: it is the
routing bookkeeping the development does not build (census item 9). -/

section FirstAlice

variable {Rw Cl Om Cone Ltwo Rone ι Xp Yp : Type*}
  [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] [Fintype Cone]
  [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo] [Fintype ι] [DecidableEq ι]
  [Fintype Rone]

/-- **`eq:terminal-first-alice` (label `09:993`, display `09:989--994`) with the
isolation-capacity input derived from the alleged protocol, PROVED.**

Everything `TerminalFixedBin.terminal_first_alice` derives is inherited by pin:
the frontier lemma is applied at `Coord = [q_2]`, at the Stage-2 exponent `r_2`,
its width hypothesis discharged from `q_2 = 2^{r_2}` and its gap hypothesis from
`eq:terminal-excess`.  What this adds is that `hisocap` is no longer assumed: at
each isolation node the frozen `h_v + z_v <= kappa_v` is produced by §3 from the
alleged protocol's own budget together with the inherited top two-copy rung, with
`z_v <= h_v` supplied by the banked `zMass_le_hMass` rather than assumed.

The per-node data is exactly the frozen reading of `09:949--950` at that node: the
two labelled fibres `To v`, `Tf v`, the retained typed two-copy projection
`Cp v`, and the sections identifying the pair's local block with the ambient
game.  `huniq` remains the frozen coordinatewise-uniqueness clause, and
`hwitness` remains the routing bookkeeping of `09:986--988`.

**The per-node bundle is narrowed the same way §2 narrows `denseNoLeaf`'s.**
Every node-indexed *proposition* -- the query-path clause, the two pair floors,
the column ceiling, the two route clauses and the game identification -- is
demanded only at `v` in the isolation class, and the two pair floors only when
that node actually carries a bonus component.  Nothing is assumed at an Alice
node, the two classes being disjoint (`DenseWeightedCount.frontier_disjoint`);
and the two pair floors specifically are not assumed at an isolation node with
`z_v = 0`, which is exactly the range over which `09:953--965` claims the pair
certificate.  The remaining isolation-node clauses -- the query-path clause, the
column ceiling, the two route clauses and the game identification -- are demanded
at every member of the isolation class, including nodes with `z_v = 0`.  The
node-indexed *data*
`To`, `Tf`, `Cp`, `iotaA`, `iotaB` stays total, and is free away from the
isolation class: taking `To v = Tf v = emptyset` there empties the section's
domain.

There is one `b_1` here, not two: the frozen Stage-1 exponent that fixes
`lambda_0 = 2 q_2 2^{-b_1}` (`08:796`) and the seed scale `2^{-b_1}` of
`eq:terminal-seed-inputs` (`09:847`) is a single schedule quantity, so the entry
condition, the witness count and the pair floor all read the same binder.

General in all nine carriers, in the state, in the protocol and in the frontier
index. -/
theorem terminal_first_alice_from_protocol
    {q s q₂ mT dT b₁ r₂ : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
    {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
    {RG RSig RD : Finset Rw} {omg : Rw → Om} {rho : Slot s → Om → Slot q₂ × Cone}
    {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
    {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)} {lamT eps2 xT ε δ' : ℝ}
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hentry : TerminalTwoStream.terminalEntry q₂ b₁ ε δ') (hwidth : q₂ = 2 ^ r₂)
    (arr : Slot q₂ → DenseFrontierConservation.FrontierArrival ι)
    (route : ι → List Bool) (iso : ι → Prop) [DecidablePred iso]
    (hpf : DenseWeightedCount.PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r₂)
    (hwitness :
      (TerminalTwoStream.zoneSet (TwoStreamState.fibreDensity
            (TwoStreamState.streamImage omg rho st.pOrd XZ st.iOrd RG))
          (TwoStreamState.fibreDensity
            (TwoStreamState.streamImage omg rho st.pFor XZ st.iFor st.Rfor))
          (DenseBranchSelection.lambdaZero q₂ b₁)).card
        ≤ DenseFrontierConservation.witnessCount arr
          + (TerminalTwoStream.badSet (TwoStreamState.fibreDensity
                (TwoStreamState.streamImage omg rho st.pOrd XZ st.iOrd RG))
              (DenseBranchSelection.lambdaZero q₂ b₁)).card)
    {Pstar : Protocol Xp Yp Bool} {gamb : Xp → Yp → Bool} {bcap : ℕ}
    (hcomp : Protocol.Computes Pstar gamb) (M1T : Cone → Rone → Bool)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hpath : ∀ v ∈ DenseWeightedCount.isolationNodes iso, IsQueryPath Pstar (route v))
    (huniq : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      DenseFrontierConservation.hMass arr v ≤ 1)
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone) (hH : 2 ≤ bcap)
    (hlegal : 2 * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    (To Tf : ι → Finset Cone) (Cp : ι → Finset (Slot 2 → Rone))
    (hTo : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      0 < DenseFrontierConservation.zMass arr v →
        TerminalCertificateInputs.pairFloor Cone b₁ ≤ (To v).card)
    (hTf : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      0 < DenseFrontierConservation.zMass arr v →
        TerminalCertificateInputs.pairFloor Cone b₁ ≤ (Tf v).card)
    (hCp : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      ⌈((Fintype.card Rone : ℝ) ^ 2) * (9 / 25)⌉₊ ≤ (Cp v).card)
    (iotaA : ∀ v : ι, {a // a ∈ TerminalCertificateInputs.pairRows (To v) (Tf v)} → Xp)
    (iotaB : ∀ v : ι, {c // c ∈ Cp v} → Yp)
    (hrow : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      ∀ a, RouteRows Pstar (route v) (iotaA v a))
    (hcol : ∀ v ∈ DenseWeightedCount.isolationNodes iso,
      ∀ b, RouteCols Pstar (route v) (iotaB v b))
    (hgame : ∀ v ∈ DenseWeightedCount.isolationNodes iso, ∀ a b,
      subgame (interlaceFun M1T 2)
          (TerminalCertificateInputs.pairRows (To v) (Tf v)) (Cp v) a b
        = gamb (iotaA v a) (iotaB v b)) :
    ∃ v ∈ DenseWeightedCount.aliceNodes iso,
      3 * DenseWeightedCount.stoppingCapacity r₂ (route v).length
          ≤ 4 * DenseFrontierConservation.hMass arr v ∧
        DenseWeightedCount.stoppingCapacity r₂ (route v).length
          < DenseFrontierConservation.hMass arr v
            + DenseFrontierConservation.zMass arr v := by
  refine TerminalFixedBin.terminal_first_alice st hentry hwidth arr route iso hpf hdepth
    hwitness ?_
  intro v hv
  exact stage2_isolation_capacity_from_certificates hcomp M1T (huniq v hv)
    (DenseFrontierConservation.zMass_le_hMass arr v) (hpath v hv) hbudget hX hY hH hlegal
    hseed (hTo v hv) (hTf v hv) (hCp v hv) (iotaA v) (iotaB v) (hrow v hv) (hcol v hv)
    (hgame v hv)

end FirstAlice

/-! ## §5  The closing comparison, and where the chain stops
(`09:996--1002`, `09:1014--1028`)

"In every case one Alice child has complexity at least `B_cap + log_2 kappa_v`,
which exceeds `eq:terminal-stage2-budget`."

The comparison itself is banked
(`Stage3ProtocolRouting.stage2_alice_child_budget_contradiction`).  What is landed
here is its application at the node §4 *produces*, so that the frozen sentence is
consumed at a derived first-Alice node rather than at an assumed one.

`hchild` is the endpoint of the frozen three-case dispatch of `09:1014--1023`.  It
stays an explicit binder because its `kappa_v >= t_2` branch is
`thm:certified-localized-extension` and its conclusion `eq:certified-E3`
(`A-certified-stopping.tex:142--145`) is asserted nowhere in the development --
census item 8.  It is **not** the phase-1 target in disguise: it is a statement
about one child of one node, at the scale `B_cap + log_2 kappa_v`, whereas the
target is a statement about the whole fixed-bin matrix at `D_2 + 1`, and
`alice_child_certificate_is_not_free` shows it fails at nodes that satisfy every
other hypothesis. -/

section Closing

variable {X Y ι : Type*} [Fintype ι]

/-- **`09:1023--1028` at the node the frontier substitution produces, PROVED.**

Given the alleged protocol, the frozen first-Alice verdict at some node of the
Alice class (which §4 derives rather than assumes), and the frozen child
certificate at the nodes that carry the verdict, the alleged protocol cannot
exist.  This is the frozen reductio's last step; combined with §1's
`lt_D_of_every_protocol_absurd` it is what `eq:terminal-fixed-bin` would follow
from, once census items 8 and 9 are supplied.

`hnode` is the frozen "first-Alice node": the node is a query node, which is what
lets the Alice query itself cost the one bit of `eq:terminal-stage2-budget`.

The two masses are abstract `ℕ`-valued readouts rather than the banked
`hMass`/`zMass` of a particular arrival family, so that §4's conclusion plugs in
verbatim at `hmass := DenseFrontierConservation.hMass arr` and
`zmass := DenseFrontierConservation.zMass arr` without this statement having to
repeat the arrival bookkeeping.  General in the frontier index, the protocol and
both exponents. -/
theorem stage2_no_alleged_protocol_at_forced_child
    {Pstar : Protocol X Y Bool} {route : ι → List Bool} {iso : ι → Prop}
    [DecidablePred iso] {hmass zmass : ι → ℕ} {bcap r₂ : ℕ}
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hpath : ∀ v ∈ DenseWeightedCount.aliceNodes iso, IsQueryPath Pstar (route v))
    (hnode : ∀ v ∈ DenseWeightedCount.aliceNodes iso,
      IsQueryNode (DenseWeightedCount.descend Pstar (route v)))
    (hverdict : ∃ v ∈ DenseWeightedCount.aliceNodes iso,
      3 * DenseWeightedCount.stoppingCapacity r₂ (route v).length ≤ 4 * hmass v ∧
        DenseWeightedCount.stoppingCapacity r₂ (route v).length < hmass v + zmass v)
    (hchild : ∀ v ∈ DenseWeightedCount.aliceNodes iso,
      3 * DenseWeightedCount.stoppingCapacity r₂ (route v).length ≤ 4 * hmass v →
      DenseWeightedCount.stoppingCapacity r₂ (route v).length < hmass v + zmass v →
        ∃ b : Bool, bcap + (r₂ - (route v).length)
          ≤ (DenseWeightedCount.descendStep
              (DenseWeightedCount.descend Pstar (route v)) b).cost) :
    False := by
  obtain ⟨v, hv, hforced, hexcess⟩ := hverdict
  obtain ⟨b, hb⟩ := hchild v hv hforced hexcess
  exact Stage3ProtocolRouting.stage2_alice_child_budget_contradiction (b := b)
    (hpath v hv) hbudget (hnode v hv) hb

end Closing

/-! ## §6  Statement poles

A green build sees none of the three failure modes these record. -/

/-- **Statement pole 1 (the reductio frame is not vacuous).**  §1's
`lt_D_of_every_protocol_absurd` would be worthless if no protocol ever existed
below the budget: its hypothesis would hold for free and the conclusion would be
a theorem about nothing.  The witness is Bob's one-bit game on `Bool x Bool`,
whose optimal protocol has cost `1`, so at `budget = 1` the hypothesis genuinely
fails and has to be earned.  Self-chosen values are legitimate here and only
here: this is a rejection probe claiming **no** legality at any paper parameter,
in the sense of the defined-vs-free witness rule. -/
theorem alleged_protocol_frame_is_not_vacuous :
    ∃ P : Protocol Bool Bool Bool,
      P.cost ≤ 1 ∧ Protocol.Computes P (fun _ y : Bool => y) := by
  refine ⟨Protocol.bNode (fun y : Bool => y) (Protocol.leaf false) (Protocol.leaf true),
    ?_, ?_⟩
  · simp [Protocol.cost]
  · intro x y
    cases y <;> rfl

/-- **Statement pole 2 (the child certificate is load-bearing).**  In
`stage2_no_alleged_protocol_at_forced_child` the binder `hchild` is what the
missing `eq:certified-E3` would supply, and it is not implied by the other
hypotheses: at an Alice query node whose two children are leaves, every child has
cost `0`, while the frozen demand at `B_cap = 1`, `r_2 = 1` and suffix depth `0`
is `1 + (1 - 0) = 2`.  So `hchild` fails at a node satisfying `IsQueryNode`, and
census item 8 is a genuine gap rather than a bookkeeping remark.

The values are self-chosen and claim **no** legality: like statement pole 1 this
is a rejection probe -- a `¬∃` exhibiting a node at which the certificate fails
-- not a claim that these are paper parameters, in the sense of the
defined-vs-free witness rule. -/
theorem alice_child_certificate_is_not_free :
    IsQueryNode (Protocol.aNode (fun x : Bool => x) (Protocol.leaf false)
        (Protocol.leaf true) : Protocol Bool Bool Bool)
      ∧ ¬ ∃ b : Bool, 1 + (1 - 0)
          ≤ (DenseWeightedCount.descendStep
              (Protocol.aNode (fun x : Bool => x) (Protocol.leaf false)
                (Protocol.leaf true) : Protocol Bool Bool Bool) b).cost := by
  constructor
  · trivial
  · rintro ⟨b, hb⟩
    cases b <;> simp [DenseWeightedCount.descendStep, Protocol.cost] at hb

/-- **Statement pole 3 (this module does not reach the phase-1 target).**  The
frozen phase-1 target `D_2 + 1` is strictly above the budget `D_2` of the alleged
protocol, and `stage2_no_alleged_protocol_at_forced_child` concludes `False`, not
the target: converting the one into the other is §1's
`lt_D_of_every_protocol_absurd`, which needs the reductio to run at *every*
protocol -- i.e. it needs census items 8 and 9.  The arithmetic record below is
the exact statement that the gap is one bit, at the banked
`TerminalFixedBin.fixedBinTarget`, so no rearrangement of this module can be
mistaken for `eq:terminal-fixed-bin`.  General. -/
theorem assembly_does_not_reach_the_phase_one_target (bcap r₂ : ℕ) :
    DenseBranchSelection.Dtwo bcap r₂ + 1 = TerminalFixedBin.fixedBinTarget bcap r₂
      ∧ DenseBranchSelection.Dtwo bcap r₂ < TerminalFixedBin.fixedBinTarget bcap r₂ := by
  constructor
  · rfl
  · simp [TerminalFixedBin.fixedBinTarget]

/-! ## §7  NON-FIDELITY readouts

The alleged protocol is hypothetical, so there is no paper instance of the data
§2--§5 quantify over (see the canonical-inhabitation note).  What is checked here
is that the narrowed bundle is inhabited at all -- that the adapter is not
quantified over an empty premise set -- at the banked two-bit probe protocol,
which is a point the frozen paper never visits. -/

/-- **NON-FIDELITY 1 (the narrowed bundle is inhabited).**  At the banked
`DenseWeightedCount.probeProtocol` -- one Bob query above one Alice query, of cost
`2` -- with the ambient game it actually computes, the banked `probeToken`, and
the node game read through the sections `id` and `fun _ => true`, every hypothesis
of `denseNoLeaf_at_stop_addresses` holds simultaneously at `r = 1`, `B_cap = 1`:
the budget is tight (`2 = D_2` at `B_cap = 1`, `r = 1`), the node's route
rectangle is the full row set and the single column `true`, the node game has
complexity exactly `1 = B_cap`, and the deep gate does not fire.

The values are self-chosen and claim **no** legality: this audits our encoding at
a two-element carrier, and is never evidence that the terminal regime is
inhabited. -/
theorem narrowed_bundle_is_inhabited_at_probe :
    Protocol.Computes DenseWeightedCount.probeProtocol (fun x y : Bool => x && y)
      ∧ DenseWeightedCount.probeProtocol.cost ≤ DenseBranchSelection.Dtwo 1 1
      ∧ (∀ a : Bool, RouteRows DenseWeightedCount.probeProtocol
          DenseWeightedCount.probeToken.route a)
      ∧ (∀ _b : Unit, RouteCols DenseWeightedCount.probeProtocol
          DenseWeightedCount.probeToken.route true)
      ∧ D (fun (x : Bool) (_ : Unit) => x) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    cases x <;> cases y <;> rfl
  · rw [DenseWeightedCount.probeProtocol_cost, DenseBranchSelection.Dtwo_eq]
  · intro a
    exact ⟨trivial, trivial⟩
  · intro _
    exact ⟨rfl, trivial⟩
  · refine le_antisymm ?_ ?_
    · refine Nat.sInf_le ⟨Protocol.aNode (fun x : Bool => x) (Protocol.leaf false)
        (Protocol.leaf true), ?_, ?_⟩
      · simp [Protocol.cost]
      · intro x y
        cases x <;> rfl
    · refine DenseWeightedCount.one_le_D_of_ne (a₁ := true) (a₂ := false) (b₁ := ())
        (b₂ := ()) (by simp) ?_
      exact ⟨1, Protocol.aNode (fun x : Bool => x) (Protocol.leaf false)
        (Protocol.leaf true), by simp [Protocol.cost], by intro x y; cases x <;> rfl⟩

/-- **NON-FIDELITY 2 (the R6 adapter fires).**  The narrowed adapter is applied at
the probe of the previous readout and produces the frozen conclusion: the token
stops before the Alice query, at suffix depth `1 = r`.  So the adapter is asserted
at a real point and not only in the abstract.  Same NON-FIDELITY caveat. -/
theorem denseNoLeaf_at_stop_addresses_at_probe :
    (DenseWeightedCount.probeToken.event = StopEvent.isolation
        ∨ DenseWeightedCount.probeToken.event = StopEvent.beforeAlice)
      ∧ DenseWeightedCount.probeToken.route.length ≤ 1 := by
  have hframe := narrowed_bundle_is_inhabited_at_probe
  refine denseNoLeaf_at_stop_addresses (r := 1) (bcap := 1) hframe.1
    DenseWeightedCount.probeToken (by norm_num) hframe.2.1
    (fun (x : Bool) (_ : Unit) => x) id (fun _ => true) hframe.2.2.1
    (fun _ => hframe.2.2.2.1 ()) (fun a b => by cases a <;> rfl)
    (fun _ => by rw [hframe.2.2.2.2])
    (fun (x : Bool) (_ : Unit) => x) id (fun _ => true) ?_ ?_
    (fun a b => by cases a <;> rfl) ?_
  · intro a
    exact ⟨trivial, trivial⟩
  · intro _
    exact ⟨rfl, trivial⟩
  · intro h
    exact absurd h (by decide)

end EthInapproximability.ParameterizedNP.TerminalFixedBinAssembly
