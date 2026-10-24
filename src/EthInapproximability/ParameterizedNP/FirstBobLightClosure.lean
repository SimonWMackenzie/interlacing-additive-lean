import EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply

/-!
# Parameterized NP route: `eq:wrapper-first-bob-light` closed against the child budget

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
  recomputed), `sections/03-preliminaries.tex`
  (SHA-256 `5A321B8B3577BC9AFB5E2C172C7FA375D046D50A81D490BBB1293F01FE34F99F`,
  recomputed) and `sections/06-parameter-schedule.tex`
  (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
  recomputed).
* **The exact frozen lines traced here**, in print order:
  * `09:1250--1252`, the exposure rule -- "Stop each routed branch at its first
    Bob query, or after `r` Alice queries"; `d_v < r` is **not printed there**,
    it is **derived from** that rule, and in Lean it arrives as the third
    component of `IsFirstBobNode` rather than as a separate binder;
  * `09:1255`/`09:1257`, `kappa_v = 2^{r-d_v}` and `W_v`;
  * `09:1268--1269`, `vartheta = 9/16` and the heavy selector, printed **before**
    the capacity split;
  * **`09:1269`, the split**, read at its printed non-strict inequality, so the
    boundary `kappa_v = t_ref` belongs to branch (i);
  * **`09:1269--1276`, branch (i)**: "follow the denser Bob child and invoke the
    certified-scale reference stopping lemma on `G`" at `r' = kappa_v/t_ref`
    (`09:1272`) and **`a^sharp = 1` (`09:1273`)**, "The other parameters are those
    of `sec:wrapper-low-rungs`" (`09:1275`), "This gives residual complexity at
    least `C + log_2 kappa_v - 1`" (`09:1275--1276`);
  * **`09:1296--1300`, branch (ii)'s substitution** into
    `lem:certified-row-ladder` -- `M = G`, `H = C-1`, `x = x_T`, `z = y`,
    `ell = ell_v` -- with **`09:1302--1304`'s legality check**, `C >= 3` verifying
    `H >= 2` and `kappa_v x_T <= t_ref x_T <= 1`;
  * **`09:1304--1306`**, "The selected Bob child therefore has complexity at least
    `C + log_2 kappa_v - 1`" -- the sentence ends inside `09:1306`, where the
    unrelated small-capacity-fallback remark begins, so the range stops there;
  * **`09:1307--1308`**, "Its lower bound is one more bit than the remaining child
    budget in the alleged protocol.  Therefore";
  * **`09:1309--1313`, `eq:wrapper-first-bob-light`**, whose display is `09:1310`
    and whose label is `09:1312`.
  * **`A:138--141`**, the readout clause of `thm:certified-localized-extension`:
    "every restriction of `\widehat M` with exactly `r' p_t` represented outer
    blocks, at least `ceil(r' t x m)` rows in each represented block, and column
    density at least `h 2^{-a^sharp}`, has communication complexity at least
    `H + log_2(r' t)`" (`A:142--144`).
* **Cross-anchors opened first-hand this tranche:** `09:105` (`q = 2^r`),
  `09:113--116` (`m_G = |Rows(G)|`), `09:311--313` (specified-coordinate
  projection), `09:322` (`h = theta`), `09:436` (`rho = 2y^2 = 18/25`, which
  DEFINES `y = 3/5`), `09:1187--1193` (the alleged `(C+r-1)`-bit protocol and
  `09:1190`'s bracket member), `09:1219` (`A_0 = ceil(2 x_T m_G)`),
  `09:1277--1283` (`ell_v`, the represented-coordinate census),
  `09:1291--1296` (the trim), `A:111--118`, `A:125--129`, `03:112--122`
  (`def:interlace`), `03:167--173` (`def:bracket`), `06:558--572`
  (`eq:tref-search`).

## What this tranche does

`AliceOnlyHdensSupply` (tranche `cc-t5l`) landed **two headlines** at a member of
`09:1190`'s bracket family, each a *dichotomy*: at a first-Bob node of
`FrontierIndexing.canonicalSystem` **either** `W_v < vartheta kappa_v` -- the
frozen `eq:wrapper-first-bob-light` conclusion, carried there as a case -- **or**
the branch-(i) supply of `09:1270--1274` exists, in the second headline together
with the four `A:138--141` readouts of the built `RestrictionDatum`.  Neither
headline had a consumer.

This module **refutes the right disjunct of exactly one of them** -- the
restriction headline `frontier_restriction_or_light_at_a_bracket_member`, the
strictly stronger of the two (same disjunction, plus the four readouts) and the
only `cc-t5l` headline that appears in a proof term below -- and thereby
collapses **that** headline to its left half.

**Named rather than asserted away: the bundle headline keeps no consumer.**
`AliceOnlyHdensSupply.frontier_bundle_or_light_at_a_bracket_member` occurs in no
statement and no proof term of this module, and its collapse is **not proved
here**.  Nothing below needs it: its right disjunct delivers the routed triple
without the `A:138--141` readouts, which is exactly the data
`RestrictionDatum.largeCapacityExtension_ofDatum` consumes.  It is an engineering
observation, and **not a claim this module proves**, that the same route would
close it -- `paperFrontierRestriction` is built from the triple together with
`hθ0`/`hθ1`, both of which are present here.  The wiring of that headline stays
**OPEN**.

The refutation performed is the frozen one and nothing else: by
`A:138--141` the restriction the right disjunct produces has complexity at least
`H + log_2(r' t) = (C-1) + log_2 kappa_v`, which is `09:1276`'s "residual
complexity at least `C + log_2 kappa_v - 1`"; and `09:1307--1308` says that is
one bit more than the selected Bob child of the alleged `(C+r-1)`-bit protocol
can carry.  So the right disjunct is impossible, the left one holds, and
`09:1310`'s display is reached at a first-Bob node **with the capacity guard
still present**.  Section 3 then removes the guard, running the same closure at
**both** branches of `09:1269`:

* **branch (i)**, `kappa_v >= t_ref`, is the new argument above, with `a^sharp`
  overridden to `1` at `09:1273`;
* **branch (ii)**, `2 <= kappa_v < t_ref`, is the banked
  `TranscriptLevelJoin.branchTwo_firstBobLight_join`, which performs the
  `09:1298--1300` substitution into `lem:certified-row-ladder` and its
  `09:1302--1304` legality check, and closes against the *same* child budget.

Section 4 gives `AliceOnlyHdensSupply.branch_one_column_density_at_a_bracket_member`
-- the branch-(i) density input, `09:1190 -> 09:311--313 -> 09:322` -- its first
consumer, at the paper's own ambient column carrier `Y = Fin q -> Yc` of
`09:105--107`.

### What changed against the predecessor, precisely

`FirstBobLightDichotomy.canonical_firstBobLight_dichotomy` already joins the two
capacity branches.  It does so through
`LargeCapacityBranch.canonical_firstBobLight_largeCapacity`, whose branch-(i)
side carries **four free binders this module does not have**:

* `hcount`, the `A:138` represented-block census, was a bound on a free natural;
  here it is `D.selCard` of the restriction the headline builds;
* `hcol`, the `A:141` column density, was a bound on a free real `colDens` --
  satisfiable by `colDens := theta` and therefore evacuable; here it is
  `D.colDens`, the retained fraction of `D`'s own column set;
* the `A:139--140` per-block row floor was outside the statement altogether;
  here it is `D.rowsPerBlock`, the minimum fibre over the **counted** blocks;
* `hbudget` was a clause about an **abstract** residual budget `B`; here the
  endpoint's output is compared with `(descend P (v.val ++ [b])).cost`, the
  alleged protocol's own selected-child cost, through the banked
  `TranscriptLevelSuccessors.firstBob_selected_child_budget`.

So the predecessor's `B` is gone and `09:1307--1308` is read against the object
the sentence names.  What is **not** removed: `hLocEx`, the certified-scale
endpoint `A:109--146` itself, where `EXPANDER-001` would enter.  It is an
explicit named binder here as it is there -- never an `axiom`, never a
premise-bundle field -- but it is now stated in the frozen theorem's own
**universal** shape, "every restriction of `\widehat M` with [the three clauses]
has communication complexity at least `H + log_2(r' t)`", quantified over the
routed triple rather than fired at one abstract member.  The quantification is
deliberately **not** over the restriction and the child bit independently: the
triple's retained columns are the columns retained at the address
`v.val ++ [b]`, so the restriction and the child that carries it move together,
and the conclusion bounds **that** child's cost.  Quantifying the two separately
would demand a bound on children carrying no restriction, which `09:1269--1270`
("follow the denser Bob child") does not assert.  And `hselect`
(`09:1287--1296`) is still carried on branch (ii), narrowed by nothing here.

### The one interface decision (DEFINED-vs-FREE)

Branch (ii) is banked at a free density `y` with `0 < y <= 1`; branch (i)'s base
certificate is banked at the literal `3/5`.  `y` is **not** ours to choose:
`09:436` prints `rho = 2y^2 = 18/25`, which defines it on the nonnegative reals,
and the banked `FirstBobLightDichotomy.wrapper_y_is_pinned_by_rho` proves `3/5`
is the only solution.  So instantiating branch (ii) at `3/5` in Section 3 is an
evaluation of the frozen definitional chain, consumed by pin from the
predecessor and not re-derived.  Every other quantity entering here is DEFINED
and enters as a banked reification or a universally quantified binder: `x_T` is
`xTdepth b_T` (`08:166`), `A_0` is `initialRefRows` (`09:1219`), `kappa_v` is
`kappaAt` (`09:1255`), `r'` is `frontierCopies` (`09:1272`), `t` is `tRef`
(`09:319` via `09:1275`), `p_t` is `certifiedPt` (`A:120`), `a^sharp` is the
literal `1` of `09:1273`, `vartheta` is `9/16` (`09:1268`).  `C` is the one
genuinely free input and appears only under `09:1302`'s own floor `C >= 3`.

## Reader counterpart: NONE claimable, re-verified first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was searched again this round
for `vartheta`, `first Bob`, `first-Bob`, `9/16`, `child budget` and
`remaining budget`.  The search returns **one** hit in the whole artifact,
`02-preliminaries.tex:301`, "not stable under the first Bob bit" -- motivating
prose for `thm:paper-density-amplification`, about a bundled density statement
and not about the routed certificate weight of a frontier node.  Prose inside a
proof may not be cited as a statement.  `eq:wrapper-first-bob-light`, the
capacity dichotomy and the child-budget sentence therefore have **no** reader
counterpart, so **no declaration of this module claims one**, and the trace is
recorded once, here.

## Canonical inhabitation

This module defines **no `structure`, no `inductive`, no `def`**, so it opens no
new canonical-inhabitation obligation.  The inherited one is **REGISTERED and
DEFERRED**, unchanged: `09:1190`'s bracket member belongs to the family of the
**alleged** `(C+r-1)`-bit protocol's matrix, and `09:1192--1193` supposes that
protocol exists only for contradiction, so the frozen paper exhibits no routed
instance to inhabit.  The honest Lean form is the implication each theorem below
states, and Section 5's satisfiability probe is labelled
**NON-FIDELITY / BEYOND-PAPER** and discharges nothing.

## What a green build cannot see, and what is done about it

**Full-bundle satisfiability is not exhibited and is not claimed.**  The
predecessor measured this and the measurement is inherited verbatim:
`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`
proves in the kernel that `hk : 4 <= k_ref` with `hq4 : k_ref + 2 <= r` forces
`6 <= r`, so the smallest instance any of these statements can be fired at has
`k_ref = 4`, and that at `k_ref = 4` branch (i)'s `hE2` is false outright for
every `theta <= 1`.  A `False` derived at such a tuple would be a fact about
`hE2`, not a measurement of the closure.  `eq:tref-search` (`06:558--572`) forces
`k_ref >= 2^19`, which puts the inhabited regime beyond any finite check -- which
is exactly why `k_ref` is universally quantified everywhere here.  What **is**
exhibited, in Section 5, is joint satisfiability of the closure's *new* clause
group: the routing, the branch-(i) guard, `09:1190`'s bracket membership, and
the alleged-protocol budget `P.cost <= C + r - 1` at `09:1302`'s own `C = 3`.
Section 5 also records, rather than glossing, that the banked routed system it
uses sits at `r = 5` and so fails `hq4` outright -- `hk` with `hq4` forces
`6 <= r` -- so what it establishes is the consistency of that clause group and
**not** an application of any theorem below.

## Residues this module does NOT close (named, not implied)

* **`hLocEx` is carried, not discharged.**  `thm:certified-localized-extension`
  (`A:109--146`) has no Lean proof and `EXPANDER-001` has no Lean declaration by
  design; both stay named hypotheses.
* **`09:1287--1290` stays GAP-EXPOSED.**  `hselect` is branch (ii)'s
  projection/selection step and is narrowed by nothing here.
* **The two column-density normalizations stay apart.**  `A:141` is consumed here
  at the *ambient* reading `|K|/|Y|` that the built datum carries, while
  `09:311--313`'s projected reading is delivered separately in Section 4; closing
  the normalization between them (`09:344--347`) is a named residue and is **not**
  attempted.
* `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-u-dense` is not approached; `hDenseRung` is neither discharged nor
  fed; `thm:first-wrapper` is **not** proved; **no route completion is claimed,
  and none may be inferred.**
* `L1-F6` (the redundant `hone` binder of `WrapperDenseFrontierWiring`) and
  `L1-F7` (the `m_G` docstring anchor in `TranscriptLevelSuccessors`) are carried
  unedited.

## Unwired census of this module's own declarations

Seven declarations.

**The one-bit margin is not recorded here.**  That the closure output
`C + ell_v - 1` exceeds the remaining child budget by exactly one bit, at every
legal depth, is the banked
`FirstBobLightDichotomy.paper_residual_budget_is_one_bit_short` -- already
universally quantified in `d_v` under `09:1302`'s `C >= 3` and the exposure
rule's `d_v < r`, and stated there as `(C-1) + (r-d_v) = ((C+r-1)-(d_v+1)) + 1`,
which `A1` turns into this module's print shape.  It is **cited by name and
restated nowhere** -- no proof term below consumes it.  Accordingly `A1`, `A2`
and `A4` label the three surviving section-1 declarations and there is
deliberately **no `A3`**: that slot held a restatement of the banked lemma, which
was deleted rather than renamed, so the surviving labels stay stable.

`endpoint_print_shapes_agree` (`A1`) is consumed by
`endpoint_output_refutes_the_selected_child_budget` (`A2`) and by
`selected_child_budget_forbids_the_endpoint_output` (`A4`); `A2` is consumed by
both Section-2/3 deliverables; `A2` and Section 2's headline are consumed by
Section 3 and Section 4 respectively.  Consumed by no proof term, each by
design: `A4`'s rejection half, `canonical_firstBobLight_closure_at_a_bracket_member`
and `branchOne_closure_carries_the_projected_column_density` (this tranche's
deliverables, whose wiring target is the assembly of `thm:first-wrapper` and
which cannot be consumed until `hselect` lands), and Section 5's probe (a
measurement endpoint).

## Axioms and imports

The sole import is `AliceOnlyHdensSupply`, whose transitive closure is the linear
chain down through `FrontierProjectionSupply`, `FrontierBundleConstruction`,
`SelectEmbedComposition`, `SelectDischarge`, `FirstBobLightDichotomy`,
`TranscriptLevelJoin` and below.  `LegacyNPCC.Stage12` is **not** in that
closure, so the cited AGHP balanced-family axiom is unreachable from every
declaration here, and **`EXPANDER-001` occurs in no hypothesis**: where the
frozen paper uses the balanced family it is the named binder `hLocEx`.  No
`axiom`, no opaque certificate, no premise bundle.
-/

namespace EthInapproximability.ParameterizedNP.FirstBobLightClosure

open Finset
open NPCC
open Workspace.Types.Protocol
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
open EthInapproximability.ParameterizedNP.LargeCapacityBranch
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors
open EthInapproximability.ParameterizedNP.TranscriptLevelJoin
open EthInapproximability.ParameterizedNP.FirstBobLightDichotomy
open EthInapproximability.ParameterizedNP.FrontierBundleConstruction
open EthInapproximability.ParameterizedNP.FrontierProjectionSupply
open EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply

/-! ## §1  The refutation engine (`A:142--144` against `09:1307--1308`)

Everything in this section is **general**: in the protocol carriers, in `P`, `r`,
`C`, the address, the bit, and the two naturals being compared.  Nothing is
evaluated and no instance is chosen. -/

section Engine

/-- **`A1` (`A:142--144` versus `09:1305--1306`): the two print shapes of the
frozen output are the same statement.**

`thm:certified-localized-extension` concludes "communication complexity at least
`H + log_2(r' t)`", and the banked `LargeCapacityBranch.largeCapacityExtension`
prints that at `H = C-1`, `r' t = kappa_v` in the addition-only form
`C + ell_v <= 1 + cost`.  The frozen budget sentence `09:1305--1306` prints the
same bound as "complexity at least `C + log_2 kappa_v - 1`", which the banked
`TranscriptLevelSuccessors.branchTwo_closure_contradicts_child_budget` consumes
as `C + ell_v - 1 <= cost`.

In `Nat` these are **equivalent unconditionally** -- including at `C + ell_v = 0`,
where truncated subtraction would be the usual trap -- so no floor has to be
carried across the bridge and neither side is weakened by using the other.  This
is the only reason the branch-(i) endpoint and the branch-(ii) budget lemma can
be composed without an arithmetic side condition.  General in all three
naturals. -/
theorem endpoint_print_shapes_agree (C ℓ cost : ℕ) :
    C + ℓ ≤ 1 + cost ↔ C + ℓ - 1 ≤ cost := by
  omega

variable {X Y Z : Type*}

/-- **`A2` (`09:1307--1308`): the endpoint output is impossible at the selected
Bob child, in the endpoint's own print shape.**

"Its lower bound is one more bit than the remaining child budget in the alleged
protocol.  Therefore ..."

At a first-Bob address of an alleged `(C+r-1)`-bit protocol, the child the
closure selects keeps at most `C + ell_v - 2` bits -- the banked
`TranscriptLevelSuccessors.firstBob_selected_child_budget`, consumed by pin
through the banked contradiction lemma -- while **either** branch's closure
output is `C + ell_v - 1`.  So no first-Bob node can carry the closure output at
its selected child.

This is the branch-independent form the frozen sentence has.  The banked
contradiction lemma is stated against `09:1305--1306`'s print shape and is named
for branch (ii), where the frozen sentence is printed; what is added here is the
composition with `A1`, so that branch (i)'s endpoint conclusion -- which arrives
in `A:142--144`'s shape, not in `09:1305--1306`'s -- can fire the very same
contradiction.  Branch (i) is its first consumer.

*Why the trivial witness fails.*  The conclusion is `False`, so the content is
that the hypothesis bundle is genuinely unsatisfiable rather than unsatisfiable
for a cheap reason: the margin between the two named quantities is exactly one
bit at every depth the exposure rule allows -- the banked
`FirstBobLightDichotomy.paper_residual_budget_is_one_bit_short`, **cited by
name and restated nowhere in this module**, whose second conjunct
`(C-1) + (r-d_v) = ((C+r-1)-(d_v+1)) + 1` is already universally quantified in
`d_v` and is this bound's print shape through `A1` -- and `A4` exhibits a tuple
where relaxing the budget by that one bit makes the endpoint output attainable.

General in the three protocol carriers, in `P`, `r`, `C`, the address and the
bit. -/
theorem endpoint_output_refutes_the_selected_child_budget {P : Protocol X Y Z}
    {r C : ℕ} {p : List Bool} (h : IsFirstBobNode P r p) (hcost : P.cost ≤ C + r - 1)
    (hC : 3 ≤ C) (b : Bool)
    (hend : C + (r - p.length) ≤ 1 + (descend P (p ++ [b])).cost) : False :=
  branchTwo_closure_contradicts_child_budget h hcost hC b
    ((endpoint_print_shapes_agree _ _ _).mp hend)

/-- **`A4`, a STATEMENT POLE: the alleged-protocol budget is load-bearing, and
exactly one bit of it is.**

Clause 1 is general and is the arithmetic content of the whole tranche, stated
once in the endpoint's own print shape: at every tuple meeting `09:1302`'s
`C >= 3`, the `d_v < r` **derived from** `09:1250--1252`'s exposure rule (it is
not printed at `09:1251--1252`), and `09:1307--1308`'s budget relation, the
endpoint conclusion `C + ell_v <= 1 + cost` is **outright false**.  It is
obtained by composing the banked
`FirstWrapperAssembly.assembled_join_margin_is_one_bit` with `A1`; neither is
re-derived.

Clauses 2--3 are the rejection half.  Relax the budget by the single bit
`09:1307--1308` names -- take the child cost one higher than the budget allows --
and the endpoint output becomes attainable, so `A2` genuinely fails without its
budget hypothesis.  Nothing weaker than the frozen one-bit margin would fire the
contradiction and nothing stronger is needed.

**Clause 2 is consumed by pin, not re-proved.**  It is byte-identical to the
fifth conjunct of the banked `FirstWrapperAssembly.assembled_join_margin_is_one_bit`
-- whose first conjunct this same proof already consumes -- so it is taken as
`....2.2.2.2` rather than re-established by `norm_num`.  Only clause 3 is
discharged locally.

**A REJECTION PROBE for clauses 2--3.**  The numerals
`(C, r, d_v, cost) = (3, 6, 2, 6)` are **ours** -- clause 2's instance of them is
the banked lemma's own and arrives with it; clause 3's is this module's.  They
claim no legality and exist only to make a guard fire.  Clause 1 is general and
assigns nothing. -/
theorem selected_child_budget_forbids_the_endpoint_output :
    (∀ C r d cost : ℕ, 3 ≤ C → d < r → cost + (d + 1) ≤ C + r - 1 →
        ¬ (C + (r - d) ≤ 1 + cost))
      ∧ ¬ ((6 : ℕ) + (2 + 1) ≤ 3 + 6 - 1)
      ∧ (3 : ℕ) + (6 - 2) ≤ 1 + 6 := by
  refine ⟨fun C r d cost hC hd hbudget hend => ?_,
    FirstWrapperAssembly.assembled_join_margin_is_one_bit.2.2.2.2, by norm_num⟩
  have hmargin := FirstWrapperAssembly.assembled_join_margin_is_one_bit.1
    C r d (r - d) cost hC (by omega) (by omega) hbudget
  have hlow : C + (r - d) - 1 ≤ cost := (endpoint_print_shapes_agree _ _ _).mp hend
  omega

end Engine

/-! ## §2  Branch (i) closed: the right disjunct refuted (`09:1269--1276`)

`AliceOnlyHdensSupply.frontier_restriction_or_light_at_a_bracket_member` gets its
first consumer.  Its right disjunct produces the `09:1270--1274` restriction with
the four `A:138--141` readouts; the certified-scale endpoint turns those readouts
into `A:142--144`'s output at the selected Bob child; and `09:1307--1308` forbids
that output.  What survives is the left disjunct, which is `09:1310`'s display. -/

section BranchOne

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- **`09:1310`'s display on branch (i), reached by refuting the right disjunct of
`09:1270--1274` against the alleged protocol's child budget.**

At a first-Bob node `v` of `FrontierIndexing.canonicalSystem` lying on
coordinate `i`'s route, with `A_0 = ceil(2 x_T m_G)` (`09:1219`, `m_G` at the row
carrier per `09:113--116`), the branch-(i) guard `k_ref <= r - d_v` (`09:1269` in
exponent form), and a member of `09:1190`'s `p = 1` bracket family at column
parameter `theta`:

`W_v < vartheta kappa_v`.

**The argument, in the frozen order.**  The `cc-t5l` headline splits on the heavy
selector of `09:1268--1269`.  If the node is light there is nothing to do.
Otherwise it delivers the routed triple of `09:1270--1274` at
`r' = kappa_v/t_ref` (`09:1272`), `t = t_ref` (`09:319` via `09:1275`) and
`a^sharp = 1` (`09:1273`), together with the built `RestrictionDatum` whose
`selCard`, `rowsPerBlock` and `colDens` are exactly `A:138`'s census,
`A:139--140`'s per-block row floor and `A:141`'s column density.  Those three are
the antecedents `thm:certified-localized-extension` reads, so `hLocEx` fires and
returns `A:142--144`'s `H + log_2(r' t) = (C-1) + ell_v`, which is `09:1276`'s
"residual complexity at least `C + log_2 kappa_v - 1`" -- at the **selected Bob
child**, the object `09:1269--1270` says to follow.  `A2` then refutes it against
`09:1307--1308`.  Hence the heavy case is impossible and the light one holds.

**What is inherited and stays visible.**  `hLocEx` is
`thm:certified-localized-extension` (`A:109--146`), the place `EXPANDER-001`
would enter, as an explicit named binder in the frozen theorem's own universal
shape: quantified over the routed triple of `09:1270--1274` ("every restriction
of `\widehat M` ..."), whose retained columns are those of the child address
`v.val ++ [b]`, so the bound it returns is on **that** child -- the one
`09:1269--1270` says to follow -- and not on an arbitrary one.  Its antecedents
are listed in the order `A:109--146` prints them, with the `A:139--140` clause
where the banked `RestrictionDatum.largeCapacityExtension_ofDatum` puts it, and
its three restriction quantities are the readouts of the built datum rather than
free parameters.  It is never an `axiom` and never a premise-bundle field.
`hE1`, `hE2` and `htcert` belong to `06` and are discharged there by
`eq:tref-search` (`06:574--578`); `hbase` is the second clause of
`lem:wrapper-reference`.

**No free census, density or budget.**  There is no `hcount` binder, no `colDens`
binder, no `hrows` binder and no abstract residual budget `B`: the first three
are readouts of the datum the headline builds, and the fourth is
`(descend P (v.val ++ [b])).cost`, the alleged protocol's own selected-child
cost.

*Why the trivial witness fails.*  The conclusion is a strict inequality between
two named quantities of the routed system, not an existential, so the question is
whether it can fail at all -- and it can: the banked
`TranscriptLevelJoin.splitAudit_is_not_light` exhibits a routed system whose
first-Bob node meets the heavy threshold with **equality**,
`W_v = 9 = vartheta . 16`, so the conclusion is false there and is not an
arithmetic tautology.

General in the source-matrix column carrier, in the three protocol carriers, in
`Coord`, `P`, `R`, `r`, `b_T`, the coordinate, the node, `C`, `k_ref`, `t_cert`,
the bracket member, and the real parameters `x_U` and `theta`. -/
theorem branchOne_firstBobLight_at_a_bracket_member {Cl : Type*} [Fintype Cl]
    (Gmat : X → Cl → Bool) (P : Protocol X Y Z) (R : Coord → Finset X)
    {r bT kref C tcert : ℕ} {xU θ : ℝ} (i : Coord)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hmem : RC ∈ bracketGE X Y 1 xU θ)
    (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ (S : Finset Coord) (T : Finset X) (b : Bool)
      (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [b]))),
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
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
      < vartheta
        * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ) := by
  rcases frontier_restriction_or_light_at_a_bracket_member P R i hcomp hR v hv hroute
      hmem hk hcap hX hY hθ0 hθ1 with
    hlight | ⟨S, T, b, htr, -, -, -, -, -, -⟩
  · exact hlight
  · exfalso
    have hend : C + (r - v.val.length) ≤ 1 + (descend P (v.val ++ [b])).cost :=
      RestrictionDatum.largeCapacityExtension_ofDatum (Mem := ℕ) (fun n => n)
        ((descend P (v.val ++ [b])).cost) Gmat
        (C := C) (r := r) (k := kref) (ℓ := r - v.val.length) (tcert := tcert)
        (paperFrontierRestriction htr hθ0 hθ1)
        hk hcap (Nat.sub_le _ _) hq4 hC (xTdepth_pos bT) (xTdepth_le_one bT)
        hgate hbase htcert hE1 hE2 (hLocEx S T b htr)
    exact endpoint_output_refutes_the_selected_child_budget
      ((canonicalSystem hcomp hR).firstBob_spec v hv) hcost hC b hend

end BranchOne

/-! ## §3  `eq:wrapper-first-bob-light`, at BOTH capacity branches

`09:1269`'s split performed, with branch (i) supplied by Section 2 and branch (ii)
by the banked `TranscriptLevelJoin.branchTwo_firstBobLight_join`.  The conclusion
carries **no capacity guard**. -/

section Closure

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`, display `09:1310`, label
`09:1312`) at a first-Bob node, unconditional in the capacity split.**

"Therefore `W_v < vartheta kappa_v` at every first-Bob node `v`."

`frontier_branch_dichotomy` exhausts `09:1269`'s split at its printed non-strict
inequality, and both branches now end in the **same** refutation against the
**same** budget:

* on `t_ref <= kappa_v` -- the boundary included, exactly as `09:1269` assigns it
  -- Section 2 closes the node: the `A:138--141` readouts of the restriction the
  `cc-t5l` headline builds feed `hLocEx` at `a^sharp = 1` (`09:1273`), whose
  output `(C-1) + ell_v` is refuted by `09:1307--1308`;
* on `kappa_v <= t_ref` the banked `branchTwo_firstBobLight_join` closes it: the
  `09:1298--1300` substitution `M = G`, `H = C-1`, `x = x_T`, `z = y`,
  `ell = ell_v` into `lem:certified-row-ladder`, with `09:1302--1304`'s legality
  check supplied by `capacity_row_density_legal_at_capacity`, gives the selected
  child `C + ell_v - 1`, refuted against the same sentence.

Branch (ii) is instantiated at `y = 3/5`, which the banked
`FirstBobLightDichotomy.wrapper_y_is_pinned_by_rho` proves is the **only** value
`09:436`'s `rho = 2y^2 = 18/25` permits, so the two branches are joined at one
evaluated `y` and not at two free ones; the single `hbase` binder therefore
serves both.  Both branches are consumed **by pin**; nothing they prove is
re-derived and neither statement is weakened.

**What "unconditional" means here.**  Unconditional in the capacity split, and in
nothing else.  The two named binders survive: `hLocEx` on branch (i) and
`hselect` (`09:1287--1296`, GAP-EXPOSED) on branch (ii).  This is not a route
completion, does not prove `thm:first-wrapper`, and narrows no certificate
residue.

*Why the trivial witness fails.*  Same pole as Section 2: the conclusion is false
at the banked `splitAudit` routed system, where `W_v = vartheta kappa_v` exactly,
so it is not an arithmetic tautology.  Full-bundle satisfiability is **not**
claimed -- see the header, and
`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor` for
why no finite firing of the analytic binders is available.

General in the source-matrix column carrier, in the three protocol carriers, in
`Coord`, `P`, `R`, `r`, `b_T`, the coordinate, the node, `C`, `k_ref`, `t_cert`,
the bracket member, the selected bit, and the real parameters `x_U` and
`theta`. -/
theorem canonical_firstBobLight_closure_at_a_bracket_member {Cl : Type*} [Fintype Cl]
    (Gmat : X → Cl → Bool) (P : Protocol X Y Z) (R : Coord → Finset X)
    {r bT kref C tcert : ℕ} {xU θ : ℝ} (i : Coord) (b : Bool)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hmem : RC ∈ bracketGE X Y 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y) (hCl : 1 ≤ Fintype.card Cl)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ (S : Finset Coord) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
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
    (hselect :
      smallCopyWidth (kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v)
          ≤ (representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v).card →
      LambdaGE Gmat
          (2 ^ (Nat.log 2
            (kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v) - 1) + 1)
          (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)
          ((3 / 5 : ℝ) ^ 2)
        ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
      < vartheta
        * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ) := by
  rcases frontier_branch_dichotomy hcomp hR hv kref with ⟨hge, -⟩ | ⟨-, hlt, -⟩
  · exact branchOne_firstBobLight_at_a_bracket_member Gmat P R i hcomp hR v hv hroute hmem
      hk ((tRef_le_kappaFrontier_iff r v.val.length kref).mp hge) hq4 hX hY hθ0 hθ1 hC
      hgate hbase htcert hE1 hE2 hcost hLocEx
  · exact branchTwo_firstBobLight_join (y := 3 / 5) Gmat hcomp hR b hv hcost hC hX hCl
      (xTdepth_pos bT) (by norm_num) (by norm_num) hbase (le_of_lt hlt) hq4 hgate hselect

end Closure

/-! ## §4  The branch-(i) density input, consumed (`09:1190 -> 09:311--313 -> 09:322`)

At the paper's own ambient column carrier `Y = Fin q -> Yc` of `09:105--107`
(`U = interlaceOp(N, q)`, `q = 2^r`), the single bracket member of `09:1190`
supplies **both** things branch (i) reads off it: the ambient column density that
`A:141` consumes through the built restriction, and -- by specified-coordinate
projection, `09:311--313` -- the projected density on any selected coordinate
set, which is the quantity `09:322` substitutes as `h` into
`thm:certified-localized-extension`.

`AliceOnlyHdensSupply.branch_one_column_density_at_a_bracket_member` gets its
first consumer here. -/

section AmbientCarrier

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}
  {X Z : Type*} [Fintype X] [DecidableEq X]
  {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- **Branch (i) closed at the frozen ambient carrier, carrying `09:311--313`'s
projected density.**

Same conclusion as Section 2 at `Y = Fin q -> Yc`, together with the second
supply the same bracket member yields: for **every** selected coordinate set `J`,
the projection of the retained outer column set has at least
`theta . |Yc|^{|J|}` columns -- `09:311--313`'s "Its normalized density remains
at least `theta`, by specified-coordinate projection", which is `h = theta` at
`09:322` and the input to `A:140--141`'s "column density at least
`h 2^{-a^sharp}`".

**What the second conjunct is, and what it is not.**  It is *not* the clause fed
to `hLocEx` above: `A:141` is consumed there at the **ambient** normalization
`|K|/|Y|` that the built `RestrictionDatum` carries, whereas this is the
**projected** normalization against `|Yc|^{|J|}`.  The two are kept apart exactly
as the banked layer keeps them (`09:344--347`), and closing the normalization
between them is a named residue this module does not touch.  What the conjunction
records is that one member of `09:1190`'s family supplies both, with no density
hypothesis anywhere: the arc `09:1190 -> 09:311--313 -> 09:322` runs off `hmem`
alone.

`0 < |Yc|` is `A:111`'s nonemptiness read at the per-coordinate column carrier;
the ambient nonemptiness `0 < |Fin q -> Yc|` that Section 2 needs is *derived*
from it rather than assumed, so the statement carries one carrier hypothesis and
not two.

**`q` is FREE in this statement, and the paper's `q` is an instance of it.**  The
carrier fixed here is the *shape* `Fin q -> Yc` of `09:105--107`, with `q` left a
universally quantified natural.  `09:105`'s `q = 2^r` -- the scale-alignment
width, with `U = interlaceOp(N, q)` -- is therefore **one instance** of what is
proved, not a restriction of it, and the surrounding section prose naming that
value is to be read as identifying the paper's instance.  The forall-`q` form
contains it and is strictly stronger; nothing below substitutes a value for `q`.

*Why the trivial witness fails.*  The first conjunct is refutable exactly as in
Section 2.  The second is not free of `hmem`: the banked
`FrontierProjectionSupply.projected_rho_does_not_supply_hdens_at_rho` exhibits a
column set satisfying a projection form while the ambient density fails, so the
two readings are genuinely different statements and this one does not follow from
nothing.

General in the per-coordinate alphabet, in `q`, in the two remaining protocol
carriers, in the source-matrix column carrier, in `Coord`, `P`, `R`, `r`, `b_T`,
the coordinate, the node, `C`, `k_ref`, `t_cert`, the bracket member, `x_U` and
`theta`. -/
theorem branchOne_closure_carries_the_projected_column_density {Cl : Type*} [Fintype Cl]
    (Gmat : X → Cl → Bool) (P : Protocol X (Fin q → Yc) Z) (R : Coord → Finset X)
    {r bT kref C tcert : ℕ} {xU θ : ℝ} (i : Coord)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx : ∀ (S : Finset Coord) (T : Finset X) (b : Bool)
      (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [b]))),
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
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [b])).cost) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        < vartheta
          * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
      ∧ ∀ J : Finset (Fin q),
          θ * (Fintype.card Yc : ℝ) ^ J.card
            ≤ ((nodeProjection P (rootColumnSet RC.2) J v.val).card : ℝ) := by
  have hY : 0 < Fintype.card (Fin q → Yc) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact pow_pos hYc q
  refine ⟨branchOne_firstBobLight_at_a_bracket_member Gmat P R i hcomp hR v hv hroute hmem
      hk hcap hq4 hX hY hθ0 hθ1 hC hgate hbase htcert hE1 hE2 hcost hLocEx, ?_⟩
  intro J
  exact branch_one_column_density_at_a_bracket_member P R hroute hmem J hYc

end AmbientCarrier

/-! ## §5  The new clause group, inhabited

**NON-FIDELITY / BEYOND-PAPER.**  This audits *our* encoding at a point the
frozen paper never visits and claims no legality.  It discharges **nothing**, and
in particular does not discharge the canonical-inhabitation obligation, which
stays REGISTERED and DEFERRED per the header. -/

section Satisfiability

/-- **The clause group this tranche introduces is jointly satisfiable.**

A conditional theorem whose new hypotheses cannot hold together measures nothing,
and a green build cannot tell the difference.  The clause `cc-t5l`'s own
satisfiability probe did **not** carry is the one this tranche adds: `hcost`, the
alleged `(C+r-1)`-bit protocol's budget of `09:1192--1193`.  It is exhibited here
alongside the group `cc-t5l` inhabited, at one and the same routed system:

* clause 1: the branch-(i) guard `k_ref <= r - d_v` of `09:1269`, at `k_ref = 4`;
* clause 2: the first-Bob flag of `09:1250--1252`, consumed by pin from the
  banked instance;
* clause 3: the address lies on coordinate `0`'s route (`09:1250--1252`);
* clause 4: **`hcost` at `09:1302`'s own floor `C = 3`** -- the banked
  `splitAudit` transcript has cost `2`, well inside the alleged budget
  `C + r - 1 = 7` at `r = 5`;
* clause 5: `09:1190`'s bracket membership with the column parameter taken to be
  `rhoSmall`, consumed by pin from `cc-t5l`.  Its pedigree is the banked
  disclosure and is reproduced here rather than thinned: `09:434--436` reads "For
  the small-capacity calls put" and prints `rho = 2y^2 = 18/25` at `09:436`, and
  "the small-capacity calls" are branch (ii)'s `2 <= kappa_v < t_ref`, whereas
  this instance sits at `kappa_v = t_ref = 16`, the boundary `09:1269` assigns to
  branch (i), whose column parameter is `h = theta` at `09:322` and is left open
  there.  So `rhoSmall` is a legal `A:128` value **BORROWED from branch (ii)**
  and used in the slot `09:1190` fills with `theta` -- application site
  `09:1190`, borrow site `09:436` -- and **not** a value the frozen text fixes at
  this node.

So the routing, the guard, the bracket member and the alleged-protocol budget
hold at once.

**Scope, stated exactly, because it is narrower than it looks.**  Two of Section
2's binders are **not** in this group and **cannot** be inhabited at this routed
system, and neither omission is an oversight:

* **`hq4` fails outright at `r = 5`.**  `hq4 : k_ref + 2 <= r` (`09:327`) with
  `hk : 4 <= k_ref` (`A:117--118`) forces `6 <= r`, which the banked instance --
  built at `r = 5` by `cc-t5c`, before either binder was in play -- does not
  meet.  So Section 2 cannot be *fired* here at all; what is exhibited is the
  consistency of its new clause group, not an application of it.  This is
  recorded rather than papered over: the group is what the tranche adds, and it
  is what is measured.
* **`hE1`, `hE2` and `hLocEx` are not inhabited anywhere a finite check can
  reach.**  `FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`
  proves in the kernel that the smallest `r` those two binders allow is `6`,
  where the only permitted exponent is `k_ref = 4`, and that at `k_ref = 4`
  `hE2` is false for every `theta <= 1`.  `eq:tref-search` (`06:558--572`) puts
  the inhabited regime at `k_ref >= 2^19`.

Full-bundle satisfiability is therefore **not** exhibited and is **not**
claimed.

**NON-FIDELITY / BEYOND-PAPER.**  Every disclosure the banked
`TranscriptLevelSuccessors.splitAudit` carries is inherited verbatim: `k_ref = 4`
meets every gate carried in `src/`, but `A:117` with `A:26` forces
`t_ref >= t_cert = 2^{2^20}`; `r = 5`, the alphabets `Fin 32` and `Bool`, the
Alice predicate and the coordinate count `18` are the banked instance's; `b_T` is
DEFINED at `06:239--241` as a function of the schedule, so only the numeral `9`
is ours.  `C = 3` is `09:1302`'s own floor and is the one numeral here that is
the paper's. -/
theorem closure_clause_group_is_jointly_satisfiable :
    (4 : ℕ) ≤ 5 - splitAuditNode.val.length
      ∧ (canonicalSystem TranscriptLevelJoin.splitAudit_completedNoBob splitAudit_hR).firstBob
          splitAuditNode = true
      ∧ splitAuditNode.val ∈ coordRoutes splitAudit splitAuditRows splitAuditA0 5 0
      ∧ splitAudit.cost ≤ 3 + 5 - 1
      ∧ (((Finset.univ : Finset (Fin 1 × Fin 32)), (Finset.univ : Finset (Fin 1 → Bool)))
          ∈ bracketGE (Fin 32) Bool 1 1 rhoSmall) := by
  obtain ⟨hmem, hroute, hfb, hcap, -⟩ :=
    splitAudit_bracket_hypothesis_group_is_jointly_satisfiable
  exact ⟨hcap, hfb, hroute, by norm_num [splitAudit, bobRootTranscript, Protocol.cost], hmem⟩

end Satisfiability

end EthInapproximability.ParameterizedNP.FirstBobLightClosure
