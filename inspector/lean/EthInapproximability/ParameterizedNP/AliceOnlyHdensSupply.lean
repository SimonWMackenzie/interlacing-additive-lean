import EthInapproximability.ParameterizedNP.FrontierProjectionSupply

/-!
# Parameterized NP route: the Alice-only `hdens` supply (`FBC-F1`, DISCHARGED)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche, after the final edit to this file.
  * `03-preliminaries.tex`
    (SHA-256 `5A321B8B3577BC9AFB5E2C172C7FA375D046D50A81D490BBB1293F01FE34F99F`):
    * **`03:112--122`**, `def:interlace`: "Its `p`-fold classical interlace
      `Lambda_p(M)` has row set `[p] x X`, **column set `Y^p`**"  -- so at
      `p = 1` a bracket member's column set lives on `[1] -> Y`, which §1 reads
      back at `Y`.
    * **`03:167--173`**, `def:bracket`: "For `p >= 1` and `x, z in (0,1]`, the
      family `M[p,x,z]` consists of the submatrices of `Lambda_p(M)` that retain
      at least `ceil(m x)` rows in every outer block and **at least
      `ceil(n^p z)` columns**."  The second clause, at `p = 1`, is the whole
      input of §2.  The legality range `z in (0,1]` printed at `03:169` is the
      same interval as `A:128`'s `h in (0,1]`.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:105--107`**, "Let `q = 2^r` be the scale-alignment width and set
      `U = interlaceOp(N, q)`" -- so the ambient column carrier of `U` is
      `Cols(N)^q`, this module's `Fin q -> Yc` in §5 and its abstract `Y`
      elsewhere.
    * **`09:1187--1193`**, the opening of `sec:dense-wrapper-frontier`: "Fix an
      arbitrary retained matrix" and the display
      **`09:1190`**, `U' in bracket(U, 1, 1 - delta_U, theta)`, then "suppose
      for contradiction that a protocol `P` of cost at most `C+r-1` computes
      `U'`".  This is the sentence that FIXES `theta` for the whole wrapper
      argument, and it is the supply this tranche wires in.
    * **`09:311--313`**, "Project the retained outer column set to any
      `9 kappa_j/16` such coordinates.  Its normalized density remains at least
      `theta`, by specified-coordinate projection" -- landed last tranche as
      `FrontierProjectionSupply.specified_coordinate_projection_preserves_density`
      and `..._hdens_projects_to_the_selected_coordinates`, consumed here by pin.
    * **`09:314--323`**, the substitution block, with **`09:322`** fixing
      `h = theta` and `a^sharp = 0`: the branch-(i) column parameter.
    * **`09:404`**, "For a retained outer column set of density at least
      `theta`" -- the same normalized ambient density, named again inside
      `sec:wrapper-low-rungs`.
    * **`09:1250--1252`**, the two stopping rules, whose Lean form is
      `FrontierIndexing.coordRoutes`; **`09:1329--1331`**, "no Bob query has
      occurred on the route to this node", the frozen sentence that makes the
      composition of §3 available.
    * **`09:1269--1276`**, branch (i), and its guard `kappa_v >= t_ref` in
      exponent form `k_ref <= r - d_v`; **`09:1287--1290`**, the branch-(ii)
      projection form, which is NOT used here (last tranche machine-checked
      that it cannot supply `hdens`).
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    **`A:128`** (`h in (0,1]`) and **`A:138--141`**, "every restriction of
    `hat M` with exactly `r' p_t` represented outer blocks, at least
    `ceil(r' t x m)` rows in each represented block, and **column density at
    least `h 2^{-a^sharp}`**" -- the clause the `hdens` binder serves.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `06:558--572` (`eq:tref-search`), consumed only through the banked
    `WrapperReferenceConstruction.tRef`.

## Reader counterparts: TWO claimable, searched first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was searched this round for
`bracket`, `retained matrix`, `column density`, `no Bob query`, `Alice-only` and
`mathcal B`.  The word `bracket` does **not** occur in the reader artifact at
all; the family is written `B(M;p,x,z)` there.  Two hits are genuine
counterparts, each assigned to exactly one declaration:

* `reader 02-preliminaries.tex:43--53`, `def:paper-interlace` -- the reader's
  numbered `def:interlace`: "the `p`-fold interlace of `M : X x Y -> {0,1}` is
  `Int_p(M) : ([p] x X) x Y^p -> {0,1}`".  Its column set `Y^p` is what §1's
  `rootColumnSet` reindexes at `p = 1`, and it is cited **only** by that
  declaration.
* `reader 02-preliminaries.tex:63--75`, the definition of the bracket family:
  "let `B(M;p,x,z)` be the family of restrictions of `Int_p(M)` that retain at
  least `ceil(m x)` rows in each outer block and **at least `ceil(n^p z)`
  columns** ... ceilings are part of the definition".  This is the reader's
  `def:bracket`, and its column clause is the hypothesis of §2's
  `root_density_of_bracket_member`, the **only** declaration that cites it.

The remaining hits are **not** counterparts and no declaration claims them:
`reader 02-preliminaries.tex:299--301` (the inherited *density-lowering*
operation, `thm:paper-density-amplification`, which moves a density rather than
reading one off a member); `reader 02-preliminaries.tex:467--472` (`y_c(h)` at
"an intended starting column density `h`", the terminal-hypothesis abbreviation
of `A:128`'s `h`, not a supply for it); `reader B-bridge-details.tex:99` and
`:139` (the bridge induction's own column densities, a different mechanism at a
different stage); and `reader A-stage4-details.tex:246`, "Fix one retained matrix
and one alleged protocol of cost at most `C-1`" -- unnumbered proof-outline prose
about the **Stage--4** argument at cost `C-1`, not `09:1192`'s first-wrapper
`C+r-1`, and prose is what the reader-counterpart rule forbids assigning to a
theorem.  So **§§3--6 claim no reader counterpart**, and the absence is recorded
once, here.

## What this tranche does: `FBC-F1` DISCHARGED, from `09:1190`

`FrontierBundleConstruction`'s two headlines each carry exactly one binder,

```text
hdens : theta <= |retainedCols P Sc v.val| / |Y|,
```

registered as successor `FBC-F1`.  Last tranche censused the route the successor
was registered against -- `09:1287--1290`'s branch-(ii) projection form -- and
**refuted** it: the projected and ambient normalizations differ by the whole
unprojected width, and `projected_rho_does_not_supply_hdens_at_rho` machine-checks
the failure at the frozen `rho`.  The same tranche's verify seat recorded the one
route left untested, and re-registered `FBC-F1` against `09:1190`.  This module
takes that route, and it closes.

The chain is three frozen sentences, in this order:

1. **`09:1190`.**  `U' in bracket(U, 1, 1 - delta_U, theta)`.  By `def:bracket`'s
   column clause at `p = 1` (`03:171--172`, `ceil(n^p z)` columns with
   `n = |Cols(U)| = |Y|`), the retained outer column set `Sc` of `U'` satisfies
   `ceil(|Y| theta) <= |Sc|`, hence `theta <= |Sc| / |Y|`.  This is
   `root_density_of_bracket_member`, and it is the *only* place `theta` enters
   the wrapper argument.
2. **`09:1250--1252` with `09:1329--1331`.**  A frontier address is reached by
   the routing rule, which only ever follows Alice queries, so "no Bob query has
   occurred on the route to this node".  The banked
   `FrontierIndexing.coordRoutes_isAlicePath` -- applied to
   `FrontierBundleConstruction`'s own `hroute` binder -- followed by the banked
   `RoutedCertificateSystem.retainedCols_of_isAlicePath` gives
   `retainedCols P Sc p = Sc` at every such address.  This is
   `retainedCols_on_a_coordRoute`; neither banked lemma is restated, and neither
   has this hypothesis (the first concludes an `IsAlicePath`, the second assumes
   one; the already-banked composition `retainedCols_frontier` is stated for a
   `RoutedSystem` node rather than for a `coordRoutes` address).
3. Therefore `hdens` at a frontier node **is** the root density, and it is
   supplied rather than assumed: `hdens_of_root_density_on_a_coordRoute`.

§4 then re-states `FrontierBundleConstruction`'s two headlines with the `hdens`
binder **gone** and `09:1190`'s bracket membership in its place.  Nothing else in
either statement moves: same guards, same index tuple, same disjunction, same
readouts.  `FrontierBundleConstruction` is **not edited** by this tranche; the
successor said the discharge is "a new declaration in the module that lands the
supply", and this is that module.

§5 gives last tranche's supply pair its first consumers: at the paper's own
ambient carrier `Y = Fin q -> Yc` (`09:105--107`), `09:1190`'s bracket membership
plus a frontier address yields, through `09:311--313`, the **projected** column
density at the selected coordinates -- which is `h = theta` at `09:322`, the
quantity `A:141` consumes.  So the arc `09:1190 -> 09:311--313 -> 09:322 -> A:141`
is closed in Lean, with no density hypothesis anywhere along it.

### What is NOT claimed

* `delta_U` plays no role here and no clause of it is used: `def:bracket`'s row
  parameter is `x = 1 - delta_U` and every statement below is independent of it,
  which is why it appears as a free binder `xU` and is never constrained.
* The bracket's **row** clause is likewise untouched.  Only the column clause is
  consumed, and the module claims nothing about the row side.
* `09:1287--1290` stays exactly as the banked layer records it.  Nothing here
  revisits last tranche's negative census, and nothing here narrows or
  strengthens `SelectDischarge.projection_at_a_node`.
* `eq:wrapper-first-bob-light` (`09:1310--1313`) is not proved;
  `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-u-dense` is asserted nowhere; `hDenseRung` is neither discharged
  nor fed; `thm:first-wrapper` is **not** proved.  **No route completion is
  claimed, and none may be inferred.**

## CANONICAL INHABITATION -- INHERITED, REGISTERED and DEFERRED

The object `09:1190` fixes is a member of a bracket family of the **alleged**
`(C+r-1)`-bit protocol's matrix, and `09:1192--1193` supposes that protocol
exists only for contradiction.  No such protocol exists -- that is the conclusion
of the whole argument -- so the paper exhibits no routed instance, and the
deferred canonical-inhabitation obligation of `FRONTIER-BUNDLE-CONSTRUCTION-001`
is carried unchanged.  Nothing below discharges it.

Two things are nevertheless machine-checked, and neither is a substitute for it:

* `bracket_member_is_nondegenerately_inhabited` exhibits a member of a `p = 1`
  bracket family at legal parameters whose column set is a **proper nonempty**
  subset of the carrier, so `root_density_of_bracket_member` is not vacuous and
  is not satisfied only at the full carrier.  **BEYOND-PAPER audit instance**:
  the carriers and the two parameters are ours.
* `splitAudit_bracket_hypothesis_group_is_jointly_satisfiable` inhabits the
  **new** binder group of §4 -- the routing hypotheses together with `09:1190`'s
  bracket membership, and with no density binder at all -- at the banked
  `TranscriptLevelSuccessors.splitAudit` routed system, and derives the density
  the old binder used to assume.  **NON-FIDELITY**, inheriting every disclosure
  the banked instance carries.

## Structures, definitions and premise bundles

This module introduces **no `structure`, no `inductive` and no premise bundle**,
and exactly one `def`, `rootColumnSet`.  That `def` is a **reindexing, not a
choice**: `def:interlace` (`03:114--115`) gives `Lambda_1(M)` the column set
`Y^1 = [1] -> Y`, and `rootColumnSet` is the canonical identification of that
with `Y`.  It carries no clause of any frozen display -- no floor, no density, no
complexity claim -- and §6 proves it is a cardinality-preserving bijection onto
its image, which is the whole of its content.

## DEFINED-VS-FREE ledger for this tranche

| quantity | status | how it is obtained here |
| --- | --- | --- |
| `theta` | DEFINED, `09:1190` | the fixed `U'`'s bracket parameter, taken from `hmem` |
| `n` of `ceil(n^p z)` | DEFINED, `03:170--172` | `n = |Cols(U)| = Fintype.card Y` |
| `p = 1` | DEFINED, `09:1190` | the literal first argument of the frozen bracket |
| `x = 1 - delta_U` | DEFINED, `09:1190` | the binder `xU`, **never used**: no row clause |
| `A_0` | DEFINED, `09:1219` | the banked `initialRefRows (xTdepth bT) (Fintype.card X)` |
| `x_T` | DEFINED, `08:166` | the banked `xTdepth` at `b_T` |
| `t = t_ref` | DEFINED, `06:558--572` | the banked `tRef kref`, never a numeral |
| `r'`, `a^sharp` | DEFINED, `09:1272--1273` | the banked `frontierCopies` and the literal `1` |
| `q`, `J`, `Yc`, `kref`, `bT`, `r` | binders | universally quantified in §§1--5 |

Sections 1--5 assign no numeral at all.  Self-chosen values occur in exactly two
labelled places: §6's nondegenerate audit instance and §6's rejection probe
(which claims **no** legality and exists only to show a hypothesis is
load-bearing), plus the inherited `splitAudit` tuple, whose disclosures are
reproduced at its use site.

## Axioms and imports

The sole import is `FrontierProjectionSupply`, whose transitive closure carries
every banked module consumed below.  `LegacyNPCC.Stage12` is **not** in that
closure, so the cited AGHP balanced-family axiom is unreachable from every
declaration here, and `EXPANDER-001` occurs in no hypothesis.  No `axiom`, no
opaque certificate, no premise bundle, no proof hole.  The external interfaces
consumed (`NPCC.bracketGE`, `coordRoutes_isAlicePath`,
`retainedCols_of_isAlicePath`, `retainedCols_nil`,
`frontier_bundle_or_light_at_paper_schedule`,
`frontier_restriction_or_light_at_paper_schedule`,
`hdens_projects_to_the_selected_coordinates`, `splitAudit_hR`,
`splitAudit_completedNoBob`, `splitAudit_firstBob_true`,
`splitAudit_node_mem_coordRoutes`, `rhoSmall`) are all proved declarations or
frozen definitions reached by pin, and none is restated.
-/

namespace EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors
open EthInapproximability.ParameterizedNP.FrontierBundleConstruction
open EthInapproximability.ParameterizedNP.FrontierProjectionSupply

/-! ## §1  `def:interlace` at `p = 1`: a one-copy column set read at `Cols(U)`

`03:114--115` gives `Lambda_p(M)` the column set `Y^p`, so a member of the
`p = 1` bracket family `09:1190` fixes carries its columns as a
`Finset ([1] -> Y)`.  The frozen `p = 1` interlace is the matrix itself, and the
identification `[1] -> Y ~= Y` is the reindexing that says so.  Nothing is
chosen: the map is evaluation at the unique coordinate. -/

section RootColumns

variable {Y : Type*} [DecidableEq Y]

/-- **`def:interlace` at `p = 1` (`03:114--115`), the column reindexing.**

*Reader counterpart:* `reader 02-preliminaries.tex:43--53`, `def:paper-interlace`
(`Int_p(M) : ([p] x X) x Y^p -> {0,1}`).  This declaration is the only one in the
module that claims it.


The column set of a one-copy bracket member, read at the ambient column carrier
`Y` of `U`.  This is a *reindexing*, not a choice: `Fin 1` has one element, and
the map is evaluation at it.  §6 proves it preserves cardinality, is monotone,
and takes the full one-copy carrier to the full ambient carrier -- which is the
whole of its content.  It carries no clause of any frozen display. -/
def rootColumnSet (C : Finset (Fin 1 → Y)) : Finset Y :=
  C.image fun f => f 0

omit [DecidableEq Y] in
/-- **Aux R0 (the reindexing is injective).**  Two one-copy columns agreeing at
the unique coordinate are equal.  General in `Y`. -/
theorem rootColumn_injective :
    Function.Injective (fun f : Fin 1 → Y => f 0) := by
  intro f g h
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  exact h

end RootColumns

/-! ## §2  `09:1190` through `def:bracket`'s column clause: the root density

`def:bracket` (`03:167--173`) asks a member of `M[p,x,z]` to retain "at least
`ceil(n^p z)` columns", where `n` is the column count of `M`.  At `09:1190`'s
`p = 1` and `M = U` that is `ceil(|Y| theta) <= |Sc|`, i.e. exactly the ambient
normalized density `theta <= |Sc| / |Y|` that `09:404` names again inside
`sec:wrapper-low-rungs`.

The row parameter `x = 1 - delta_U` is carried as a free binder and is **never
used**: only the column clause is consumed. -/

section RootDensity

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- **`09:1190` read through `def:bracket`'s column clause (`03:171--172`), at
`p = 1`: the retained outer column set has ambient density at least `theta`.**

*Reader counterpart:* `reader 02-preliminaries.tex:63--75`, the definition of
`B(M;p,x,z)` ("at least `ceil(n^p z)` columns ... ceilings are part of the
definition").  This declaration is the only one in the module that claims it.

This is where `theta` enters the whole first-wrapper argument.  `09:1187--1191`
fixes an arbitrary `U' in bracket(U, 1, 1 - delta_U, theta)`; the frozen column
clause demands `ceil(n^1 theta)` columns with `n = |Cols(U)| = |Y|`; dividing by
the positive `|Y|` gives the frozen normalized density of `09:404`.

The ceiling is the frozen one and is not weakened: the proof goes through
`Nat.le_ceil`, so the real bound `|Y| theta <= ceil(|Y| theta)` is used in the
only direction `def:bracket` licenses.

*Why this is not vacuous.*  The conclusion is an inequality between two named
quantities, so no trivial witness is available to it; and the hypothesis is not
free, since §6 exhibits a member at legal parameters whose column set is a proper
nonempty subset of the carrier, where the conclusion is a strict statement about
a strictly smaller set.

*Why the alphabet hypothesis is load-bearing.*  `0 < |Y|` is the nonemptiness of
`Cols(U)`; at `|Y| = 0` the division producing the conclusion is unavailable.

General in both carriers, in the member, in the row parameter `xU` (which is
unconstrained and unused) and in `theta`. -/
theorem root_density_of_bracket_member {xU θ : ℝ}
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hmem : RC ∈ bracketGE X Y 1 xU θ) (hY : 0 < Fintype.card Y) :
    θ ≤ ((rootColumnSet RC.2).card : ℝ) / (Fintype.card Y : ℝ) := by
  have hcol : ⌈((Fintype.card Y : ℝ) ^ 1) * θ⌉₊ ≤ RC.2.card := hmem.2
  have hYR : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hcard : (rootColumnSet RC.2).card = RC.2.card :=
    Finset.card_image_of_injective _ rootColumn_injective
  have hceil : ((Fintype.card Y : ℝ) ^ 1) * θ ≤ (RC.2.card : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hcol
  rw [le_div_iff₀ hYR, hcard]
  calc θ * (Fintype.card Y : ℝ) = ((Fintype.card Y : ℝ) ^ 1) * θ := by ring
    _ ≤ (RC.2.card : ℝ) := hceil

end RootDensity

/-! ## §3  `09:1250--1252` with `09:1329--1331`: the Alice-only composition

"No Bob query has occurred on the route to this node."  The routing rule of
`09:1250--1252` descends only through Alice queries, so every address it produces
is Alice-only, and the retained outer column set arrives at such an address
undiminished.  Both halves are banked; what is new is the composition **at a
`coordRoutes` address**, and the density transport it yields, which is the shape
`FrontierBundleConstruction` consumes. -/

section Route

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type}

/-- **`09:1329--1331` at a routed address: nothing is cut.**

At an address produced by the frozen routing rule of `09:1250--1252` the retained
outer column set is literally unchanged.

*What is new, and what is consumed by pin.*  The two inputs are banked and
neither is restated: `FrontierIndexing.coordRoutes_isAlicePath` **concludes** an
`IsAlicePath` from a `coordRoutes` membership, and
`RoutedCertificateSystem.retainedCols_of_isAlicePath` **assumes** an
`IsAlicePath`.  The already-banked composition
`RoutedCertificateSystem.retainedCols_frontier` is stated at a node of a
`RoutedSystem` (`S.node v`, through `S.node_isAlicePath`), which is a different
hypothesis from membership in a single coordinate's route -- the form
`FrontierBundleConstruction`'s `hroute` binder actually carries.  This
declaration is that form, and it is consumed twice below.

*Why this is not vacuous.*  It is an equation between two named finite sets, and
§6's rejection probe exhibits a protocol and an address at which the same
equation is **false**, so the routing hypothesis is load-bearing.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `A0`, `r`, the
coordinate, the address and the column set. -/
theorem retainedCols_on_a_coordRoute {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} {i : Coord} {p : List Bool}
    (hp : p ∈ coordRoutes P R A0 r i) (Sc : Finset Y) :
    retainedCols P Sc p = Sc :=
  retainedCols_of_isAlicePath (coordRoutes_isAlicePath hp)

/-- **`FBC-F1`, DISCHARGED: the `hdens` binder is the root density.**

`FrontierBundleConstruction`'s binder is
`theta <= |retainedCols P Sc v.val| / |Y|`.  At an address the frozen routing
rule produces, `09:1329--1331` makes the retained set the root set, so that
binder **is** `theta <= |Sc| / |Y|` -- and that is `09:1190`'s bracket density,
delivered by §2.  Nothing about the node, the branch, the capacity or the weight
enters: the supply is available at every routed address.

*Why this is not vacuous, and why it is not reversible.*  Both sides are
inequalities between named quantities.  The hypothesis is strictly stronger than
the conclusion in general -- §6's rejection probe exhibits a protocol and an
address where the root density holds and the node density fails -- so the
routing hypothesis genuinely does the work.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `A0`, `r`, the
coordinate, the address, the column set and `theta`. -/
theorem hdens_of_root_density_on_a_coordRoute {P : Protocol X Y Z}
    {R : Coord → Finset X} {A0 r : ℕ} {i : Coord} {p : List Bool}
    (hp : p ∈ coordRoutes P R A0 r i) (Sc : Finset Y) {θ : ℝ}
    (hroot : θ ≤ (Sc.card : ℝ) / (Fintype.card Y : ℝ)) :
    θ ≤ ((retainedCols P Sc p).card : ℝ) / (Fintype.card Y : ℝ) := by
  rw [retainedCols_on_a_coordRoute hp Sc]
  exact hroot

end Route

/-! ## §4  The two headlines, with `hdens` GONE and `09:1190` in its place

`FrontierBundleConstruction.frontier_bundle_or_light_at_paper_schedule` and
`..._restriction_...` are re-stated here with their single density binder
replaced by the frozen bracket membership of `09:1190`.  Every other binder,
guard, index and readout is carried over unchanged, and the retained outer column
set is `09:1190`'s own, read at `Cols(U)` by §1.

`FrontierBundleConstruction` is **not edited** by this tranche. -/

section Headlines

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord]

/-- **Branch (i), `09:1269--1276`, at a member of `09:1190`'s bracket family: the
bundle is constructed with NO density hypothesis.**

Identical to `FrontierBundleConstruction.frontier_bundle_or_light_at_paper_schedule`
except that its `hdens` binder is replaced by `hmem`, the frozen
`U' in bracket(U, 1, 1 - delta_U, theta)` of `09:1190`, and the retained outer
column set is that member's own column set read at `Cols(U)`.  The guards
(`hk : 4 <= k_ref`, `A:117--118`; `hcap : k_ref <= r - d_v`, `09:1269`), the
first-Bob flag (`09:1250--1252` through `firstBob_spec`), the route (`hroute`),
the index tuple (`r' = kappa_v/t_ref` at `09:1272`, `a^sharp = 1` at `09:1273`,
`t = t_ref` at `09:319` via `09:1275`) and the disjunction are unchanged.

`xU` is `1 - delta_U`; it is unconstrained and unused, because only the column
clause of `def:bracket` is consumed.

*Why the trivial witness fails.*  Inherited verbatim from the banked headline:
the right disjunct demands `S.card = r' p_t`, positive at the frozen guards
(`paper_blockCount_is_positive`), so `S = empty` fails; and `T.Nonempty` with
`T.card` at least `ceil(r' t x_T m_G)`, positive by
`certifiedRowFloor_pos_at_paper_schedule`, so `T = empty` fails.  The left
disjunct is refutable (`TranscriptLevelJoin.splitAudit_is_not_light`), so the
disjunction is not carried by its left half.

*Why the hypothesis group is consistent.*  §6 inhabits it at the banked
`splitAudit` routed system, with the bracket member exhibited and no density
binder present.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `r`, the
coordinate, the node, the bracket member, `k_ref`, `b_T`, `xU` and `theta`. -/
theorem frontier_bundle_or_light_at_a_bracket_member (P : Protocol X Y Z)
    (R : Coord → Finset X) {r bT kref : ℕ} {xU θ : ℝ} (i : Coord)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hmem : RC ∈ bracketGE X Y 1 xU θ)
    (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length)
    (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
          < vartheta
            * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
      ∨ ∃ (S : Finset Coord) (T : Finset X) (b : Bool),
          S ⊆ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v ∧
            T ⊆ rowsAt P (R i) v.val ∧
            RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
              (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
              (retainedCols P (rootColumnSet RC.2) (v.val ++ [b])) :=
  frontier_bundle_or_light_at_paper_schedule P R i hcomp hR v hv hroute
    (rootColumnSet RC.2) hk hcap hX hY
    (hdens_of_root_density_on_a_coordRoute hroute (rootColumnSet RC.2)
      (root_density_of_bracket_member hmem hY))

/-- **`09:1270--1274`'s restriction, produced from `09:1190` with NO density
hypothesis.**

Identical to
`FrontierBundleConstruction.frontier_restriction_or_light_at_paper_schedule`
except for the same replacement: the `hdens` binder becomes `hmem`.  All four
`A:138--141` readouts off the built `RestrictionDatum` are carried over
unchanged -- the `A:138` block census at the frozen `p_{kappa_v}`, the
`A:139--140` common fibre `= |T|`, its positivity, and `A:141`'s density.

`hθ0` and `hθ1` are `A:128`'s `h in (0,1]`, which the banked constructor and
`RestrictionDatum` both demand.  They are **not** redundant with `hmem`:
`def:bracket`'s printed legality range `z in (0,1]` (`03:169`) is prose about the
family's parameters and is not part of the `bracketGE` membership predicate, so
the range is carried explicitly rather than extracted.

*Why the trivial witness fails.*  Inherited from the banked headline and
sharpened there: the datum's `selCard` is pinned to the frozen positive
`p_{kappa_v}` and its common fibre to a positive cardinality, so no degenerate
rectangle satisfies the right disjunct.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `r`, the
coordinate, the node, the bracket member, `k_ref`, `b_T`, `xU` and `theta`. -/
theorem frontier_restriction_or_light_at_a_bracket_member [DecidableEq Coord]
    (P : Protocol X Y Z) (R : Coord → Finset X) {r bT kref : ℕ} {xU θ : ℝ} (i : Coord)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hmem : RC ∈ bracketGE X Y 1 xU θ)
    (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length)
    (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
          < vartheta
            * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
      ∨ ∃ (S : Finset Coord) (T : Finset X) (b : Bool)
          (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
            (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
            (retainedCols P (rootColumnSet RC.2) (v.val ++ [b]))),
          S ⊆ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v ∧
            T ⊆ rowsAt P (R i) v.val ∧
            (paperFrontierRestriction htr hθ0 hθ1).selCard
                = RestrictionDatum.certifiedPt (kappaFrontier r v.val.length) ∧
            (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock = T.card ∧
            0 < T.card ∧
            (paperFrontierRestriction htr hθ0 hθ1).colDens
                = ((retainedCols P (rootColumnSet RC.2) (v.val ++ [b])).card : ℝ)
                    / (Fintype.card Y : ℝ) :=
  frontier_restriction_or_light_at_paper_schedule P R i hcomp hR v hv hroute
    (rootColumnSet RC.2) hk hcap hX hY hθ0 hθ1
    (hdens_of_root_density_on_a_coordRoute hroute (rootColumnSet RC.2)
      (root_density_of_bracket_member hmem hY))

end Headlines

/-! ## §5  `09:1190 -> 09:311--313 -> 09:322 -> A:141`, closed

At the paper's own ambient column carrier `Y = Fin q -> Yc` (`09:105--107`,
`U = interlaceOp(N, q)` with `q = 2^r`), the two supplies join: `09:1190` fixes
`theta`, §3 carries it to the frontier node, and last tranche's
`FrontierProjectionSupply.hdens_projects_to_the_selected_coordinates` --
the Lean form of `09:311--313` -- turns it into the **projected** density on the
selected coordinates.  That projected density is `h = theta` at `09:322`, and
`h 2^{-a^sharp}` is what `A:141` consumes.

This is the first consumer of last tranche's supply pair. -/

section BranchOne

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}
  {X Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type}

/-- **The branch-(i) column density `h = theta` (`09:322`), supplied from
`09:1190` alone.**

At the frozen ambient carrier `Y = Fin q -> Yc` of `09:105--107`: given a member
of `09:1190`'s bracket family and an address the frozen routing rule produces,
the projection of the retained outer column set to any selected coordinate set
`J` has projected density at least `theta` -- the conclusion of `09:311--313`,
and exactly the quantity `09:322` substitutes as `h` into
`thm:certified-localized-extension`, whose `A:140--141` clause reads "column
density at least `h 2^{-a^sharp}`".

The two normalizations of `09:344--347` are kept apart exactly as last tranche
kept them: the hypothesis normalizes against `|Y| = |Yc|^q`, the conclusion
against `|Yc|^{|J|}`.  Nothing here revisits `09:1287--1290`, whose branch-(ii)
projection form was machine-checked last tranche **not** to supply the ambient
density; this runs the other way, which is the direction the frozen text asserts.

*Why this is not vacuous.*  The conclusion is an inequality between two named
quantities, and it is not free of the hypothesis: last tranche's
`projected_rho_does_not_supply_hdens_at_rho` exhibits a column set satisfying a
projection form while the ambient density fails, so the two are genuinely
different statements and this implication is not reversible.

*Why the alphabet hypothesis is load-bearing.*  `0 < |Yc|` is `A:111`'s
nonemptiness read at the per-coordinate column carrier; at `|Yc| = 0` with
`|J| < q` the divisor `|Yc|^{q - |J|}` vanishes.

General in the per-coordinate alphabet, in `q`, in the two remaining carriers, in
`Coord`, in `P`, `R`, `A0`, `r`, the coordinate, the address, the bracket member,
the selection, `xU` and `theta`. -/
theorem branch_one_column_density_at_a_bracket_member
    (P : Protocol X (Fin q → Yc) Z) (R : Coord → Finset X) {A0 r : ℕ} {i : Coord}
    {p : List Bool} (hp : p ∈ coordRoutes P R A0 r i)
    {xU θ : ℝ} {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ) (J : Finset (Fin q))
    (hYc : 0 < Fintype.card Yc) :
    θ * (Fintype.card Yc : ℝ) ^ J.card
      ≤ ((nodeProjection P (rootColumnSet RC.2) J p).card : ℝ) := by
  have hY : 0 < Fintype.card (Fin q → Yc) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact pow_pos hYc q
  exact hdens_projects_to_the_selected_coordinates P (rootColumnSet RC.2) J p hYc
    (hdens_of_root_density_on_a_coordRoute hp (rootColumnSet RC.2)
      (root_density_of_bracket_member hmem hY))

end BranchOne

/-! ## §6  Aux-lemma battery, non-vacuity, and the statement poles

Five general checks on §1's reindexing and on the two hypothesis groups §§2--4
join, plus the inherited live-fire probe.  Canonical inhabitation of the paper's
own object is INHERITED, REGISTERED and DEFERRED per the header: `09:1190`'s
member belongs to the bracket family of the **alleged** protocol's matrix, which
does not exist, so no paper instance can be exhibited and none of the probes
below discharges the obligation. -/

section Battery

/-- **Battery 1 (identity: the reindexing preserves cardinality).**

`|rootColumnSet C| = |C|`, so the column clause of `def:bracket` transfers to the
ambient reading with no loss -- which is why §2 may divide by `|Y|` without
tracking the reindexing.  General in `Y` and `C`. -/
theorem rootColumnSet_card {Y : Type*} [DecidableEq Y] (C : Finset (Fin 1 → Y)) :
    (rootColumnSet C).card = C.card :=
  Finset.card_image_of_injective _ rootColumn_injective

/-- **Battery 2 (monotonicity).**  A larger one-copy column set has a larger
ambient reading.  General in `Y`. -/
theorem rootColumnSet_mono {Y : Type*} [DecidableEq Y] {C C' : Finset (Fin 1 → Y)}
    (h : C ⊆ C') : rootColumnSet C ⊆ rootColumnSet C' :=
  Finset.image_subset_image h

/-- **Battery 3 (round trip: the full one-copy carrier reads back as the full
ambient carrier).**

`rootColumnSet univ = univ`, the degenerate case of §2 where the retained set is
all of `Cols(U)` and the density is `1`.  General in `Y`. -/
theorem rootColumnSet_univ {Y : Type*} [Fintype Y] [DecidableEq Y] :
    rootColumnSet (Finset.univ : Finset (Fin 1 → Y)) = (Finset.univ : Finset Y) := by
  refine Finset.eq_univ_of_forall ?_
  intro y
  exact Finset.mem_image.mpr ⟨fun _ => y, Finset.mem_univ _, rfl⟩

/-- **Battery 4 (NONDEGENERATE inhabitation of §2's hypothesis group).**

A conditional theorem whose hypothesis holds only degenerately measures nothing.
Here `def:bracket`'s two clauses are met at legal parameters (`x = 1` and
`z = 1/2`, both inside `03:169`'s `(0,1]`) by a member whose retained column set
is a **proper nonempty** subset of the ambient carrier -- so
`root_density_of_bracket_member` is not satisfied only at the full carrier, and
its conclusion at this member is the strict statement `1/2 <= 2/4`.

**A BEYOND-PAPER audit instance.**  The carriers `Bool` and `Fin 4`, the row
parameter `1` and the column parameter `1/2` are **ours**; they claim no legality
and exist only to keep §2 from being vacuous.  The frozen `theta` of `09:1190` is
a bracket parameter of the alleged protocol's matrix and is not instantiated
here. -/
theorem bracket_member_is_nondegenerately_inhabited :
    (((Finset.univ : Finset (Fin 1 × Bool)),
        ((Finset.univ : Finset (Fin 1 → Fin 4)).filter fun f => (f 0).val < 2))
        ∈ bracketGE Bool (Fin 4) 1 1 (1 / 2 : ℝ))
      ∧ (rootColumnSet ((Finset.univ : Finset (Fin 1 → Fin 4)).filter
            fun f => (f 0).val < 2)).card = 2
      ∧ (rootColumnSet ((Finset.univ : Finset (Fin 1 → Fin 4)).filter
            fun f => (f 0).val < 2)) ≠ (∅ : Finset (Fin 4))
      ∧ (rootColumnSet ((Finset.univ : Finset (Fin 1 → Fin 4)).filter
            fun f => (f 0).val < 2)) ≠ (Finset.univ : Finset (Fin 4)) := by
  have hfilter : ((Finset.univ : Finset (Fin 1 → Fin 4)).filter
      fun f => (f 0).val < 2).card = 2 := by decide
  have hcard : (rootColumnSet ((Finset.univ : Finset (Fin 1 → Fin 4)).filter
      fun f => (f 0).val < 2)).card = 2 := by
    rw [rootColumnSet_card, hfilter]
  have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
  refine ⟨⟨?_, ?_⟩, hcard, ?_, ?_⟩
  · intro j _
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have hT : ⌈(Fintype.card Bool : ℝ) * 1⌉₊ = 2 := by
      simp
    rw [hT]
    decide
  · have hT : ⌈((Fintype.card (Fin 4) : ℝ) ^ 1) * (1 / 2 : ℝ)⌉₊ = 2 := by
      simp only [Fintype.card_fin]
      norm_num
    rw [hT, hfilter]
  · intro hcon
    rw [hcon] at hcard
    simp at hcard
  · intro hcon
    rw [hcon, huniv] at hcard
    omega

/-- **Battery 5, a STATEMENT POLE: the routing hypothesis of §3 is load-bearing.**

`retainedCols_on_a_coordRoute` and `hdens_of_root_density_on_a_coordRoute` are
false without the Alice-only address.  At the one-query Bob protocol below, at
the address `[false]`:

* the retained outer column set is **strictly cut** -- the equation of
  `retainedCols_on_a_coordRoute` fails; and
* the root density holds at `theta = 1` while the node density fails at
  `theta = 1`, so the transport of `hdens_of_root_density_on_a_coordRoute` fails
  too.

So `09:1329--1331` ("no Bob query has occurred on the route to this node") is
doing real work in the discharge, and neither declaration is a triviality about
`retainedCols`.

**A REJECTION PROBE.  It claims no legality**: the carriers `Unit`, `Bool` and
the protocol are self-chosen and exist only to make a guard fire.  The address
`[false]` is deliberately **not** a `coordRoutes` address of anything. -/
theorem hdens_transport_needs_the_alice_only_address :
    retainedCols (Protocol.bNode (fun y : Bool => y)
          (Protocol.leaf true) (Protocol.leaf true) : Protocol Unit Bool Bool)
        (Finset.univ : Finset Bool) [false]
        ≠ (Finset.univ : Finset Bool)
      ∧ (1 : ℝ) ≤ ((Finset.univ : Finset Bool).card : ℝ) / (Fintype.card Bool : ℝ)
      ∧ ¬ ((1 : ℝ) ≤ ((retainedCols (Protocol.bNode (fun y : Bool => y)
              (Protocol.leaf true) (Protocol.leaf true) : Protocol Unit Bool Bool)
              (Finset.univ : Finset Bool) [false]).card : ℝ)
            / (Fintype.card Bool : ℝ)) := by
  have hret : retainedCols (Protocol.bNode (fun y : Bool => y)
      (Protocol.leaf true) (Protocol.leaf true) : Protocol Unit Bool Bool)
      (Finset.univ : Finset Bool) [false] = ({false} : Finset Bool) := by
    decide
  have hcardBool : (Fintype.card Bool : ℕ) = 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hret]
    decide
  · rw [Finset.card_univ, hcardBool]
    norm_num
  · rw [hret, hcardBool]
    norm_num

/-- **The NEW binder group of §4 is jointly satisfiable, with NO density binder.**

**NON-FIDELITY / BEYOND-PAPER.**  This audits *our* encoding at a point the
frozen paper never visits and claims no legality.  Every disclosure the banked
`TranscriptLevelSuccessors.splitAudit` carries is inherited verbatim: `k_ref = 4`
meets every gate carried in `src/`, but `A:117` with `A:26` forces
`t_ref >= t_cert = 2^{2^20}`; and `r = 5`, the alphabets `Fin 32` and `Bool`, the
Alice predicate and the coordinate count `18` are the banked instance's.  `b_T`
is DEFINED at `06:239--241` as a function of the schedule, so only the numeral
`9` is ours.  **This probe does not discharge canonical inhabitation.**

What it establishes is what a green build cannot see: the hypothesis group of
`frontier_bundle_or_light_at_a_bracket_member` is **consistent**, in its new
shape.  Five clauses hold simultaneously at one routed system --

* the frozen routing hypotheses (`hcomp`, `hR` and the first-Bob flag are the
  banked ones and are consumed by pin; the address lies on coordinate `0`'s
  route, `09:1250--1252`);
* the branch-(i) guards `4 <= k_ref` (`A:117--118`) and
  `k_ref <= r - d_v` (`09:1269`);
* **a member of `09:1190`'s `p = 1` bracket family at the frozen column
  parameter `rho = 2y^2 = 18/25`** of `09:436` (borrowed from branch (ii), as the
  banked module discloses at this node, and legal for `A:128` by
  `probe_rhoSmall_le_one`), whose two `def:bracket` clauses are met; and
* the density `FrontierBundleConstruction` used to demand as `hdens`, here
  **derived** from that membership by §§2--3 rather than assumed.

The last clause is the point of the tranche: at this instance the old binder is
an output. -/
theorem splitAudit_bracket_hypothesis_group_is_jointly_satisfiable :
    (((Finset.univ : Finset (Fin 1 × Fin 32)), (Finset.univ : Finset (Fin 1 → Bool)))
        ∈ bracketGE (Fin 32) Bool 1 1 rhoSmall)
      ∧ splitAuditNode.val ∈ coordRoutes splitAudit splitAuditRows splitAuditA0 5 0
      ∧ (canonicalSystem TranscriptLevelJoin.splitAudit_completedNoBob splitAudit_hR).firstBob
            splitAuditNode = true
      ∧ (4 : ℕ) ≤ 5 - splitAuditNode.val.length
      ∧ rhoSmall ≤ ((retainedCols splitAudit
            (rootColumnSet (Finset.univ : Finset (Fin 1 → Bool)))
            splitAuditNode.val).card : ℝ) / (Fintype.card Bool : ℝ) := by
  have hmem : (((Finset.univ : Finset (Fin 1 × Fin 32)),
      (Finset.univ : Finset (Fin 1 → Bool))) : Finset (Fin 1 × Fin 32) × Finset (Fin 1 → Bool))
      ∈ bracketGE (Fin 32) Bool 1 1 rhoSmall := by
    constructor
    · intro j _
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      have hT : ⌈(Fintype.card (Fin 32) : ℝ) * 1⌉₊ = 32 := by
        simp
      rw [hT]
      decide
    · have hT : ⌈((Fintype.card Bool : ℝ) ^ 1) * rhoSmall⌉₊ = 2 := by
        have hb : (Fintype.card Bool : ℝ) = 2 := by simp
        rw [hb]
        rw [show ((2 : ℝ) ^ 1) * rhoSmall = 36 / 25 by norm_num [rhoSmall]]
        rw [Nat.ceil_eq_iff (by norm_num)]
        norm_num
      have hc : (Finset.univ : Finset (Fin 1 → Bool)).card = 2 := by decide
      rw [hT, hc]
  refine ⟨hmem, splitAudit_node_mem_coordRoutes 0,
    TranscriptLevelJoin.splitAudit_firstBob_true, by simp, ?_⟩
  exact hdens_of_root_density_on_a_coordRoute (splitAudit_node_mem_coordRoutes 0)
    (rootColumnSet (Finset.univ : Finset (Fin 1 → Bool)))
    (root_density_of_bracket_member hmem (by norm_num))

end Battery

end EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply
