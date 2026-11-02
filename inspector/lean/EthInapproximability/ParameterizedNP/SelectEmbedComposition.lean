import EthInapproximability.ParameterizedNP.SelectDischarge

/-!
# Parameterized NP route: the reference-copy embedding and the select composition

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
  recomputed), `sections/02-mechanical-contract.tex`
  (SHA-256 `019209B4EDF21015507148310EFBED757A83FD7709CF3880E178A4C535097A3D`,
  recomputed) and `sections/06-parameter-schedule.tex`
  (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`,
  recomputed), the last of these traced only for `eq:tref-search` (`06:558--572`)
  at the section 8 index battery, where `k_ref >= 2^19` is what makes the
  Lean-visible guard boundary `k = 4` a **BEYOND-PAPER** value rather than a
  paper one.
* **The exact frozen lines traced here**, in print order:
  * `09:105`, `q = 2^r`, and `09:107`, `U = <N>^q` -- the ambient game of the
    alleged protocol is the `q`-fold interlace of `N`, so Alice's ambient input is
    a pair `(coordinate, row of N)` and Bob's is a `q`-tuple of `Cols(N)`;
  * `09:113--116`, `R_G = {base} x Omega x [w_0] subseteq Rows(N)`,
    `G = N[R_G, Cols(N)]`, `m_G = |Rows(G)|` (the list of `113--116` stops at
    `m_G`), and `09:117`, `g = m_G/m = 91/92`;
    **the `g` overload, disambiguated once here.**  That frozen `g` is a *density
    ratio* of row counts.  It is **not** the `g : X -> (Fin q -> Yc) -> Bool` that
    every theorem below binds, which is the function the alleged protocol of
    `09:1188--1193` computes; the two are unrelated, no statement here conflates
    them, and `09:117`'s ratio is used by no declaration of this module (the
    section 5 identity is entrywise and never needs it);
  * `09:121--123` (`eq:reference-all-columns`), `Cols(G) = Cols(N)`, with its
    frozen reading "no auxiliary projection or reduced column alphabet is
    involved";
  * `09:1188--1193`, the **alleged** protocol: a retained matrix
    `U' in <U, 1, 1-delta_U, theta>` and a protocol `P` of cost at most `C+r-1`
    computing it;
  * `09:1235--1236`, "Start one clean reference certificate in every coordinate
    outside `E_0`" -- the start rule, **reified** in section 1;
  * `09:1238--1239`, "a certificate consists of at least `A_k` reference rows in
    one outer coordinate";
  * `09:1250--1257`, the two stopping rules, `d_v`, `kappa_v = 2^{r-d_v}`, `W_v`;
  * `09:1259`, "Every first-Bob node has `kappa_v >= 2`";
  * `09:1276--1278`, branch (ii)'s entry `2 <= kappa_v < t_ref` and
    `ell_v = log_2 kappa_v`;
  * `09:1283`, `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}` -- the count that
    licenses the selection;
  * `09:1287--1290`, the projection-at-a-node sentence (banked in
    `SelectDischarge.projection_at_a_node`);
  * `09:1291--1296`, `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows
    per selected certificate, trimmed to row density `kappa_v x_T`;
  * `09:1296--1306`, the `lem:certified-row-ladder` call at
    `M = G, H = C-1, x = x_T, z = y, ell = ell_v`;
  * `09:434--441`, `rho = 2y^2 = 18/25` (`09:436`), `u_2 = 2` (`09:438`),
    `u_kappa = kappa/2 + 1` (`09:440`), and `09:442--445`, the cover clause;
  * `09:445--447`, the identity `u_2 = 2` at `ell = 1` and
    `u_kappa = kappa/2 + 1` at `ell = log_2 kappa >= 2`, i.e. the frozen
    `u_kappa = 2^{ell-1}+1` matching the ladder's copy count at **`A:158`**
    (`\LambdaThree{M}{2^{\ell-1}+1}{2^\ell x}{z^2}`);
  * `A:150--160`, `lem:certified-row-ladder`, consumed **only** through the banked
    `TerminalTwoStream.certifiedRowLadder_of_base` at its call sites and not
    re-derived here.

## What this tranche does

The predecessor (`SelectDischarge`, `SELECT-DISCHARGE-001`) proved both legs of
`09:1287--1306` and then **stopped and reported** two residues, which are exactly
this tranche's targets.

* **`SELECT-EMBED-001`, the reference-copy embedding.**  The predecessor carried
  `iotaA`, `iotaB` and
  `hgame : interlaceFun G pc a c = g (iotaA a) (iotaB c)` as explicit named
  binders, observing that a numeric `Lambda` bound (`hbase`) cannot produce an
  embedding of carriers.  Section 5 **proves** the identification from the
  construction instead: `09:107` makes the ambient game the `q`-fold interlace of
  `N`, `09:113--116` cuts `G` out of `N` on the base reservoir, and
  `09:121--123` gives `Cols(G) = Cols(N)`; so a selection of outer coordinates
  and a column of the ambient carrier that restricts to `c` on them produce the
  interlace identity outright.  `iotaB` is no longer a binder either: section 4
  builds it as a **section of the node projection**, which is what makes its image
  reach the node.
* **The `F6` composition.**  The predecessor's two legs met in prose only:
  leg (1) was stated at a free dyadic index `l` with
  `J.card = smallCopyWidth (2^l)`, the discharge at `smallCopyWidth (kappa_v)`,
  and nothing in Lean asserted `2^l = kappa_v`.  Section 2 supplies that identity
  **through the banked chain** -- `TranscriptLevelConstruction.kappaAt` is
  `2^{r-d_v}` and its `Nat.log` is the capacity exponent
  (`log_kappaAt_eq_capacity_exponent`) -- and section 6 is the single term
  `projection_at_a_node -> nodeProjection_transport_density ->
  hselect_of_trims_and_projection`.
* **The `F3` start-rule obligation.**  `09:1235--1236` was a call-site binder
  (`hstart`) in the predecessor.  Section 1 reifies the started coordinate type as
  `[q] \ E_0` itself, so the frozen exclusion is a **theorem** of the type rather
  than a hypothesis, and `SelectDischarge.representedCoords_image_avoids_E0` is
  fired at it with no binder left.

The payoff is that section 6's conclusion is the exact `hselect` consequent, with
`hselect`'s own antecedent (`09:1283`'s count) **consumed** rather than discarded:
the count is what produces the selected coordinate set.  Section 7 re-fires both
`cc-t5e` dichotomy deliverables through it, with the `hselect` binder gone.

### What is still assumed, named exactly

Section 6 keeps four explicit named binders, and each is a frozen sentence about
the **construction**, never about the alleged protocol's residual cost:

* `hsub : Gmat a c = Nmat (ιR a) c` -- `09:113--116` with `09:121--123`: `G` is a
  row-submatrix of `N` on the full column alphabet.
* `hplace` -- the retained matrix `U'` of `09:1188--1193`, read at a reference row
  placed in an outer coordinate, is the ambient interlace entry.  This is what
  "retained matrix in `<U,1,1-delta_U,theta>`" means together with `09:107`, and
  it is quantified only over columns of the retained set `S`.
* `hblock` -- `09:1291--1296` with `09:1238--1239`: the trimmed block of a
  selected certificate consists of that certificate's own rows at the node.
* `hcover` -- `09:442--445`, the maximal-matching covers built once at the root.

None is an `axiom`, an opaque certificate, or a premise bundle; `EXPANDER-001`
occurs in no hypothesis of this module.

### DEFINED-vs-FREE, and the `vartheta` twin

* `y` is **DEFINED** by `09:436` (`rho = 2y^2 = 18/25`); the banked
  `FirstBobLightDichotomy.wrapper_y_is_pinned_by_rho` proves `3/5` is its only
  nonnegative solution.  Every `3/5` below is an evaluation of that chain.
* `kappa_v` is **DEFINED** by `09:1253--1255` and reified as the banked
  `TranscriptLevelConstruction.kappaAt`; `ell_v = log_2 kappa_v` is **DEFINED** by
  `09:1278` and evaluated by the banked `log_kappaAt_eq_capacity_exponent`.
  Section 2 computes through that chain and assigns no numeral.
* `u_kappa` is **DEFINED** by `09:438`/`09:440` and reified as the banked
  `WrapperProjectionCovers.smallCopyWidth`; `A_0` by `09:1219`
  (`initialRefRows`).  None is re-reified here.
* **The `vartheta` twin, named at every use.**  Two declarations spell
  `vartheta`: `DenseWrapperFrontier.vartheta` and `ParameterSchedule.vartheta`.
  This module `open`s **`DenseWrapperFrontier`** and not `ParameterSchedule`, so
  every occurrence of `vartheta` below -- it occurs only in the two re-fired
  dichotomy conclusions of section 7 -- is `DenseWrapperFrontier.vartheta`, the
  `9/16` of `09:1268`.  No declaration here defines, restates or evaluates either
  twin.

## Reader counterpart: NONE claimable, re-verified first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was searched again this round
for `interlace`, `reference`, `copy`, `embed`, `projection` and `started`.  The
hits are `02-preliminaries.tex:119--140` (`prop:paper-projection-facts`, the
inherited bracket projection facts, about `CC` of bracket families and not about a
protocol node), `A-stage4-details.tex:394` -- **description corrected this round,
re-opened first-hand**: that line is the dense-Stage-4 residual-complexity display
`D_U(1;1-delta_U,theta) >= C+r_q`, *not* `lem:certified-row-ladder` (the reader
names its own ladder `lem:paper-certified-row-ladder` three lines earlier, at
`:390--391`, and this module states neither) -- `B-bridge-details.tex:146`
and `:163` (the *bridge* induction's denser child) and
`C-effectivity-details.tex:74` ("represented" of encoded indices).  None states
`09:105--123`'s reference-copy placement, the start-rule carrier, or the
composition.  So **no declaration of this module claims a reader counterpart**,
and the absence is recorded once, here.

## Canonical inhabitation

This module declares no `structure` and no `inductive`.  It declares one type
abbreviation (`StartedCoord`, the frozen `[q] \ E_0`), two `def`s (`startedIdx`,
`transportedProj`) and two `noncomputable def`s (`selectionEquiv`,
`ambientColumn`).

* `StartedCoord` **is** the paper's own started-coordinate carrier
  (`09:1235--1236`), and section 1 inhabits it at the paper's own legality
  condition `e_0 < q`: `09:448--453` defines `E_0` and records the deterministic
  bound `e_0 <= e_0^max`, `09:456` reads it as
  `e_0 = O((s + t_ref) log(1/theta))`, and `09:1262`
  (`eq:wrapper-frontier-conservation`, label `09:1265`) spends the resulting
  `q - e_0` certificate mass.  So this is a genuine paper-side inhabitation, not a
  synthetic probe.
* The composition of section 6 is a statement about the **alleged** protocol of
  `09:1188--1193`, whose non-existence is the conclusion of the whole argument, so
  the paper constructs no instance of its hypothesis bundle.  The inherited
  deferred canonical-inhabitation registration is therefore carried unchanged and
  nothing below discharges it; every numeric instance in section 8 is labelled
  **NON-FIDELITY / BEYOND-PAPER**.

## Residues this module does NOT close (named, not implied)

* `hbase` (`lem:wrapper-reference`) is untouched: section 6 does not use it, and
  the numeric-to-embedding gap the predecessor reported is closed by tracing the
  construction, not by converting `hbase`.
* `hLocEx` (branch (i)'s certified-scale endpoint `A:109--146`, the place
  `EXPANDER-001` would enter) is inherited verbatim by the section 7 re-fires.
* **`L1-F6`** (retire the redundant `hone` binder of
  `WrapperDenseFrontierWiring`) and **`L1-F7`** (the `m_G` anchor in
  `TranscriptLevelSuccessors`' docstring) are **carried, unedited**: both are
  edits to other modules and therefore their own tranches.
* `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-u-dense` is not approached; `hDenseRung` is neither discharged nor
  fed; `thm:first-wrapper` is **not** proved; **no route completion is claimed,
  and none may be inferred.**

## Unwired census of this module's own declarations

Thirty-one declarations follow -- twenty-six theorems, one type abbreviation and
four `def`s -- and **twenty-two are consumed by another proof term here**
(recounted mechanically after the last edit).  The nine that are not are endpoints
by design rather than oversight:

* The two section 7 dichotomies are **deliverables**; their consumer is the
  assembly of `thm:first-wrapper`, which does not exist yet.
  (`hselect_of_reference_construction` is a deliverable too, but it is **not** one
  of the nine and is deliberately not listed here: it is consumed internally, in
  both section 7 proofs.  Miscounting it as an endpoint was the record defect the
  gate recorded as `R1`; the totals 22/9 were already correct and are unchanged.)
* `startedCoord_nonempty` and `startedCoord_isEmpty_of_full` are the start rule's
  inhabitation and its pole.
* `selectionEquiv_roundTrip`,
  `composition_index_constraints_are_jointly_satisfiable`,
  `interlace_reference_copy_is_nondegenerate`, `cover_antecedent_is_refutable`
  and `reference_copy_needs_the_selected_agreement` are battery and pole endpoints
  (**NON-FIDELITY / BEYOND-PAPER** wherever they name a carrier), consumed by
  nothing by construction.

## Two banked lemmas consumed rather than restated (SHADOW check)

A cross-module scan for statement twins was run before landing, and it caught two:
`09:445--447`'s copy-count identity `u_{2^l} = 2^{l-1}+1` is the banked
`WrapperProjectionCovers.smallCopyWidth_dyadic`, and `09:1259` in logarithmic form
(`1 <= ell_v` at a first-Bob node) is the banked
`TranscriptLevelJoin.one_le_log_kappaAt_of_firstBob`.  Both were drafted here and
**deleted**; section 2 consumes them by pin.  The nearest relative of section 5's
identity, `TwoStreamState`'s `selector_entry`, is **not** a twin: it is a
structure *field* of the transposed Stage-3 selector state (`09:628--630`), an
assumption about a two-stream state, not a proved identity about a row-submatrix
on the ambient column alphabet.

## Instance-binder hygiene (this tranche's only edit)

Five unused instance binders that the compiler itself named on this module were
dropped, and nothing else moved.  Three are the section variable `[Fintype Cl]`
of §4, auto-included into `ambientColumn_mem`, `ambientColumn_apply` and
`routeCols_ambientColumn` although none of the three mentions it; they now carry
the `omit [Fintype Cl] in` that `exists_ambientColumn` already carried, so §4 is
uniform.  Two are the explicit `[DecidableEq Rw]` of
`hselect_of_reference_construction` and `firstBobLight_of_reference_construction`;
the first already opens with `classical`, the second needs no decidability of `Rw`
at all, and the schedule-indexed twin never carried the binder -- which is why the
twin could already call the first.  All five removals *strengthen* the statements
they touch (a hypothesis is discharged, never weakened), the four carriers and
both interlace widths are untouched, and every call site is unaffected because
instance binders are instance-implicit.  The counts above -- thirty-one
declarations, the 22/9 consumed/endpoint split and the axiom split -- are
unchanged, and this module now compiles with **zero** warnings.

## Axioms and imports

The sole import is `SelectDischarge`, whose transitive closure carries every
banked module consumed below.  `LegacyNPCC.Stage12` is **not** in that closure, so
the cited AGHP balanced-family axiom is unreachable from every declaration here.
No `axiom`, no opaque certificate, no premise bundle.  `#print axioms` was run on
all thirty-one declarations (they are added to `tools/AxiomAudit.lean` in this
tranche), and the split is: **twenty-three** depend on the full core triple
`[propext, Classical.choice, Quot.sound]`; **six** on `[propext, Quot.sound]`
(`StartedCoord`, `startedIdx`, `startedIdx_notMem_E0`, `startedIdx_injective`,
`interlace_reference_copy_is_nondegenerate`,
`reference_copy_needs_the_selected_agreement`); `routeRows_snoc_of_isBobNode` on
`[propext]` alone; and `interlaceFun_reference_copy` -- the reference-copy
embedding itself -- on **no axioms at all**.  Zero `sorryAx`, zero project axioms,
and zero occurrences of `NPCC.aghp_balanced_family_exists`.
-/

namespace EthInapproximability.ParameterizedNP.SelectEmbedComposition

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.SelectDischarge

/-! ## §1  The start rule as a carrier (`09:1235--1236`), the `F3` obligation

"Start one clean reference certificate in every coordinate outside `E_0`."

The predecessor carried this as the call-site binder `hstart : idx i notin E_0`
and the judge's finding `F3` recorded the genuinely unformalized fact behind it:
that the *started* coordinate type is exactly `[q] \ E_0`.  Making it the carrier
turns the frozen exclusion into a theorem of the type and removes the binder. -/

section StartRule

variable {q : ℕ}

/-- **`09:1235--1236`, the started coordinate carrier.**

The coordinates in which a clean reference certificate is started: the outer
coordinates outside the exceptional set `E_0` of `09:448--450`.  The whole banked
frontier machinery is `Coord`-generic, so instantiating `Coord` at this type is
the reification `F3` asks for and costs nothing downstream. -/
abbrev StartedCoord (E0 : Finset (Fin q)) : Type := {i : Fin q // i ∉ E0}

/-- **The placement of a started coordinate in `[q]`.**  The frozen argument
addresses started coordinates by their outer index, and nothing else; this is that
address map. -/
def startedIdx {E0 : Finset (Fin q)} : StartedCoord E0 → Fin q := Subtype.val

/-- **`09:1235--1236` as a theorem, not a binder (`F3`).**  Every started
coordinate lies outside `E_0`.  General. -/
theorem startedIdx_notMem_E0 {E0 : Finset (Fin q)} (i : StartedCoord E0) :
    startedIdx i ∉ E0 := i.2

/-- **Aux S1 (the addressing is faithful).**  Distinct started coordinates have
distinct outer addresses, so a selection of coordinates and a selection of outer
indices are the same datum.  General. -/
theorem startedIdx_injective {E0 : Finset (Fin q)} :
    Function.Injective (startedIdx (E0 := E0)) := fun _ _ h => Subtype.ext h

/-- **Aux S2 (the census of the start rule).**  Exactly `q - e_0` certificates are
started, which is the count `eq:wrapper-frontier-conservation` reads as
`sum_v W_v >= q - e_0`.  General. -/
theorem card_startedCoord (E0 : Finset (Fin q)) :
    Fintype.card (StartedCoord E0) = q - E0.card := by
  classical
  rw [Fintype.card_subtype]
  have hfil : (Finset.univ.filter fun i : Fin q => i ∉ E0) = E0ᶜ := by
    ext i; simp
  rw [hfil, Finset.card_compl, Fintype.card_fin]

/-- **Non-vacuity of the start rule at legal parameters (LANE-GATE 3).**

The started carrier is inhabited exactly when the exceptional set does not
exhaust the width, which is the paper's own regime: `09:448--453` bounds
`e_0 <= e_0^max` well below `q`, and `eq:wrapper-frontier-conservation`'s
`q - e_0` is the certificate mass the argument spends.  So this is the paper's
inhabitation of `StartedCoord`, not a synthetic one.  General. -/
theorem startedCoord_nonempty {E0 : Finset (Fin q)} (h : E0.card < q) :
    Nonempty (StartedCoord E0) := by
  rw [← Fintype.card_pos_iff, card_startedCoord]
  omega

/-- **Statement pole: the exclusion is doing work.**  If `E_0` swallowed every
coordinate there would be no certificate to start at all, so `09:1235--1236`'s
"outside `E_0`" is not decoration.  General. -/
theorem startedCoord_isEmpty_of_full :
    IsEmpty (StartedCoord (Finset.univ : Finset (Fin q))) := by
  constructor
  intro i
  exact i.2 (Finset.mem_univ _)

/-- **`09:1287`, "Every represented coordinate is outside `E_0`", with no binder.**

The predecessor's `SelectDischarge.representedCoords_image_avoids_E0` fired at the
started carrier: its `hstart` is now `startedIdx_notMem_E0`, a theorem, so the
frozen sentence holds of any routed object over `StartedCoord E0`.  This is the
`F3` discharge.  General in the protocol, the reference rows, `A_0`, `r` and the
node. -/
theorem representedCoords_avoids_E0 {Yc : Type*} {X Z : Type*} [Fintype X] [DecidableEq X]
    {E0 : Finset (Fin q)} {P : Protocol X (Fin q → Yc) Z} {R : StartedCoord E0 → Finset X}
    {A0 r : ℕ} (v : FrontierNode P R A0 r) :
    ∀ i ∈ (representedCoords P R A0 r v).image startedIdx, i ∉ E0 :=
  representedCoords_image_avoids_E0 v startedIdx startedIdx_notMem_E0

end StartRule

/-! ## §2  The width chain: `2^{ell_v} = kappa_v` supplied, not assumed

Judge finding `F6`: leg (1) is stated at a free dyadic index `l`, the discharge at
`kappa_v`, and nothing in Lean asserted `2^l = kappa_v`.  It is supplied here
**through the banked chain**: `kappaAt` is `09:1255`'s `2^{r-d_v}` and its
`Nat.log` is the capacity exponent, both banked in
`TranscriptLevelConstruction`. -/

section Width

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1255` and `09:1278` composed: `2^{ell_v} = kappa_v`.**

The node capacity is a power of two by its own defining display, and `ell_v` is
its logarithm; so exponentiating `ell_v` returns `kappa_v` exactly.  Both inputs
are banked (`kappaAt`, `log_kappaAt_eq_capacity_exponent`) and neither is restated.
This is the identity the `F6` composition needs.  General. -/
theorem pow_log_kappaAt (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) :
    2 ^ (Nat.log 2 (kappaAt P R A0 r v)) = kappaAt P R A0 r v := by
  rw [log_kappaAt_eq_capacity_exponent]
  rfl

/-- **`09:1276--1277`, branch (ii)'s entry, in logarithmic form.**  `kappa_v <
t_ref = 2^{k_ref}` gives `ell_v < k_ref`, which is the dyadic range of the cover
clause `09:442--445`.  General. -/
theorem log_kappaAt_lt_of_lt_tRef {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r k : ℕ}
    (v : FrontierNode P R A0 r) (hlt : kappaAt P R A0 r v < 2 ^ k) :
    Nat.log 2 (kappaAt P R A0 r v) < k :=
  Nat.log_lt_of_lt_pow (by have := one_le_kappaAt P R A0 r v; omega) hlt

/-- **The selected width at a first-Bob node equals the ladder's copy count.**

`u_{kappa_v} = 2^{ell_v - 1} + 1`: `pow_log_kappaAt` composed with the two banked
facts it needs -- `WrapperProjectionCovers.smallCopyWidth_dyadic` for
`09:445--447`'s identity and `TranscriptLevelJoin.one_le_log_kappaAt_of_firstBob`
for `09:1259`'s `ell_v >= 1` -- both consumed by pin and restated nowhere.  This
is what makes the coordinate selection of `09:1287--1290` and the interlace copy
set of `A:158` the *same* index set, and hence what lets leg (1)'s density become
the bracket family's column clause.  General. -/
theorem smallCopyWidth_kappaAt {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} (hv : (canonicalSystem hcomp hR).firstBob v = true) :
    smallCopyWidth (kappaAt P R A0 r v)
      = 2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1 := by
  conv_lhs => rw [← pow_log_kappaAt P R A0 r v]
  exact smallCopyWidth_dyadic
    (TranscriptLevelJoin.one_le_log_kappaAt_of_firstBob hcomp hR hv)

end Width

/-! ## §3  The selection as an index identification (`eIdx` discharged)

The predecessor carried `eIdx : Fin pc ≃ {i // i ∈ J}` as part of the documented
STOP.  A selection of `pc` distinct outer coordinates *is* such an equivalence, so
once the selection is made the identification is free. -/

section Selection

variable {q pc : ℕ}

/-- **The selected coordinate set, identified with the interlace copy index.**

An injective `sigma : [pc] -> [q]` -- the frozen "any selected `u_{kappa_v}` of
them" -- identifies the copy index with its own image.  General. -/
noncomputable def selectionEquiv (σ : Fin pc → Fin q) (hσ : Function.Injective σ) :
    Fin pc ≃ {i : Fin q // i ∈ Finset.image σ (Finset.univ : Finset (Fin pc))} :=
  (Equiv.ofInjective σ hσ).trans
    (Equiv.subtypeEquivRight (fun i => by simp [Set.mem_range, eq_comm]))

/-- **Aux E1 (the identification is the selection).**  General. -/
@[simp] theorem selectionEquiv_val (σ : Fin pc → Fin q) (hσ : Function.Injective σ)
    (j : Fin pc) : (selectionEquiv σ hσ j).val = σ j := rfl

/-- **Aux E2 (the selected set has the selected width).**  General. -/
theorem card_image_selection (σ : Fin pc → Fin q) (hσ : Function.Injective σ) :
    (Finset.image σ (Finset.univ : Finset (Fin pc))).card = pc := by
  rw [Finset.card_image_of_injective _ hσ, Finset.card_univ, Fintype.card_fin]

end Selection

/-! ## §4  A section of the node projection (`iotaB` discharged)

Leg (1) bounds the size of `nodeProjection P S J p`, a set of *restrictions* of
retained columns.  The bridge needs actual ambient columns that reach the node.
Both are available at once: a member of the projection has, by construction, a
preimage in the retained set at the node, and the retained set at a node is cut by
`bobCols`, which is the routing predicate (`SelectDischarge.mem_bobCols_iff_routeCols`).
So the section supplies `iotaB` **and** its `hcol` together. -/

section ColumnSection

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ} {X Z : Type*}
  {Cl : Type*} [Fintype Cl] [DecidableEq Cl] {pc : ℕ}

/-- **The transported projection, i.e. the `Cset` of the join.**

Literally the set `nodeProjection_transport_density` bounds: leg (1)'s projection
carried to the bracket family's column type along the two identifications.  It is
named here only so that a section of it can be defined; no clause of `def:bracket`
is built into it. -/
def transportedProj (P : Protocol X (Fin q → Yc) Z) (S : Finset (Fin q → Yc))
    (J : Finset (Fin q)) (p : List Bool) (eIdx : Fin pc ≃ {i // i ∈ J}) (eCol : Cl ≃ Yc) :
    Finset (Fin pc → Cl) :=
  (nodeProjection P S J p).image fun f => fun j : Fin pc => eCol.symm (f (eIdx j))

/-- **Aux C1 (a projected column has an ambient preimage at the node).**  Unfolds
the banked `nodeProjection`/`projSet` pair; nothing is restated.  General. -/
theorem exists_ambient_of_mem_nodeProjection {P : Protocol X (Fin q → Yc) Z}
    {S : Finset (Fin q → Yc)} {J : Finset (Fin q)} {p : List Bool}
    {f : {i // i ∈ J} → Yc} (hf : f ∈ nodeProjection P S J p) :
    ∃ y ∈ retainedCols P S p, (fun i : {i // i ∈ J} => y i.1) = f := by
  simpa [nodeProjection, WrapperProjectionCovers.projSet, Finset.mem_image] using hf

omit [Fintype Cl] in
/-- **The section, existentially.**  Every member of the transported projection is
the restriction of an ambient column retained at the node.  General. -/
theorem exists_ambientColumn {P : Protocol X (Fin q → Yc) Z} {S : Finset (Fin q → Yc)}
    {J : Finset (Fin q)} {p : List Bool} {eIdx : Fin pc ≃ {i // i ∈ J}} {eCol : Cl ≃ Yc}
    (c : {c // c ∈ transportedProj P S J p eIdx eCol}) :
    ∃ y ∈ retainedCols P S p, ∀ j : Fin pc, y (eIdx j).1 = eCol (c.val j) := by
  obtain ⟨f, hf, hfc⟩ := Finset.mem_image.mp c.2
  obtain ⟨y, hy, hyf⟩ := exists_ambient_of_mem_nodeProjection hf
  refine ⟨y, hy, fun j => ?_⟩
  have h1 : y (eIdx j).1 = f (eIdx j) := congrFun hyf (eIdx j)
  have h2 : eCol.symm (f (eIdx j)) = c.val j := congrFun hfc j
  rw [h1, ← h2, Equiv.apply_symm_apply]

/-- **`iotaB`, built rather than assumed.**  A choice of ambient preimage; the two
readouts below are its whole interface. -/
noncomputable def ambientColumn (P : Protocol X (Fin q → Yc) Z) (S : Finset (Fin q → Yc))
    (J : Finset (Fin q)) (p : List Bool) (eIdx : Fin pc ≃ {i // i ∈ J}) (eCol : Cl ≃ Yc)
    (c : {c // c ∈ transportedProj P S J p eIdx eCol}) : Fin q → Yc :=
  (exists_ambientColumn c).choose

omit [Fintype Cl] in
/-- **Aux C2 (the section lands in the retained set at the node).**  General. -/
theorem ambientColumn_mem {P : Protocol X (Fin q → Yc) Z} {S : Finset (Fin q → Yc)}
    {J : Finset (Fin q)} {p : List Bool} {eIdx : Fin pc ≃ {i // i ∈ J}} {eCol : Cl ≃ Yc}
    (c : {c // c ∈ transportedProj P S J p eIdx eCol}) :
    ambientColumn P S J p eIdx eCol c ∈ retainedCols P S p :=
  (exists_ambientColumn c).choose_spec.1

omit [Fintype Cl] in
/-- **Aux C3 (round trip: the section really is a section).**  On the selected
coordinates the chosen ambient column is the projected one.  This is the only
property the interlace identity of section 5 uses.  General. -/
theorem ambientColumn_apply {P : Protocol X (Fin q → Yc) Z} {S : Finset (Fin q → Yc)}
    {J : Finset (Fin q)} {p : List Bool} {eIdx : Fin pc ≃ {i // i ∈ J}} {eCol : Cl ≃ Yc}
    (c : {c // c ∈ transportedProj P S J p eIdx eCol}) (j : Fin pc) :
    ambientColumn P S J p eIdx eCol c (eIdx j).1 = eCol (c.val j) :=
  (exists_ambientColumn c).choose_spec.2 j

omit [Fintype Cl] in
/-- **`hcol` for free.**  The retained set at a node is cut by `bobCols`, and the
banked `SelectDischarge.mem_bobCols_iff_routeCols` says that set is the routing
predicate; so the section's image reaches the node.  General. -/
theorem routeCols_ambientColumn {P : Protocol X (Fin q → Yc) Z} {S : Finset (Fin q → Yc)}
    {J : Finset (Fin q)} {p : List Bool} {eIdx : Fin pc ≃ {i // i ∈ J}} {eCol : Cl ≃ Yc}
    (c : {c // c ∈ transportedProj P S J p eIdx eCol}) :
    RouteCols P p (ambientColumn P S J p eIdx eCol c) :=
  (mem_bobCols_iff_routeCols P p _).mp
    (Finset.mem_inter.mp (ambientColumn_mem c)).2

end ColumnSection

/-! ## §5  `SELECT-EMBED-001`: the reference-copy embedding (`09:105--123`)

The documented STOP of the predecessor, proved.  Nothing here is about the
protocol: it is the arithmetic of `U = <N>^q` with `G = N[R_G, Cols(N)]` and
`Cols(G) = Cols(N)`, which is why a numeric `Lambda` bound was never going to
produce it and why the construction does. -/

section Embedding

/-- **`09:107` with `09:113--116` and `09:121--123`: the interlace identity.**

Let `N` be the ambient matrix, `G` a row-submatrix of it on the **same** column
alphabet (`eq:reference-all-columns`), `sigma` a selection of outer coordinates,
and `y` an ambient column tuple agreeing with `cJ` on the selected coordinates.
Then the `pc`-fold interlace of `G` read at `(copy, row)` and `cJ` is the `q`-fold
interlace of `N` read at the placed row and `y`.  That is exactly `hgame` with the
ambient side made explicit: the selected outer coordinates carry literal copies of
`G`.

*Why the trivial witness fails.*  The statement is an equation between two matrix
entries, so there is nothing to witness; and it is false without `hy` --
`reference_copy_needs_the_selected_agreement` in section 8 exhibits a matrix, a
selection and a `y` that disagrees at the selected coordinate, where the two sides
differ.

General in the three carriers, in `q`, in `pc`, in the selection and in both
column tuples. -/
theorem interlaceFun_reference_copy {RwN Rw Yc : Type*} {q pc : ℕ}
    (Nmat : RwN → Yc → Bool) (Gmat : Rw → Yc → Bool) (ιR : Rw → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    (σ : Fin pc → Fin q) (y : Fin q → Yc) (cJ : Fin pc → Yc)
    (hy : ∀ j, y (σ j) = cJ j) (a : Fin pc × Rw) :
    interlaceFun Gmat pc a cJ = interlaceFun Nmat q (σ a.1, ιR a.2) y := by
  simp only [interlaceFun]
  rw [hsub, hy]

end Embedding

/-! ## §6  The composition (`F6`): one term, `hselect` unconditional

`projection_at_a_node -> nodeProjection_transport_density ->
hselect_of_trims_and_projection`, with `2^{ell_v} = kappa_v` supplied by section 2,
`eIdx` by section 3, `iotaB` and `hcol` by section 4, and `hgame` by section 5. -/

section Composition

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- **Aux R1 (a Bob step constrains no row).**  Appending a Bob edge to a node's
address leaves Alice's half of the rectangle unchanged -- the row-side reading of
`09:1043--1044` -- so the certificate rows that reach a first-Bob node also reach
its children.  General. -/
theorem routeRows_snoc_of_isBobNode {Y Z : Type*} {P : Protocol X Y Z} {p : List Bool}
    {x : X} (hbob : IsBobNode (descend P p)) (h : RouteRows P p x) (b : Bool) :
    RouteRows P (p ++ [b]) x := by
  have hstep : ∀ Q : Protocol X Y Z, IsBobNode Q → aliceStepConsistent Q b x := by
    intro Q hQ
    cases Q with
    | leaf z => exact hQ.elim
    | aNode a l r => exact hQ.elim
    | bNode f l r => trivial
  exact (routeRows_append p [b] x).mpr ⟨h, hstep _ hbob, trivial⟩

/-- **`09:1287--1306` with `hselect` discharged from the construction.**

The frozen branch-(ii) argument, end to end, at a first-Bob node of the canonical
routed system:

* `hcount` is `09:1283`'s `ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`.  It is
  **consumed**, not discarded: it is what produces the selected set of
  `u_{kappa_v}` represented coordinates, whose outer addresses avoid `E_0` by
  section 1's `F3` discharge.
* leg (1) (`SelectDischarge.projection_at_a_node`, `09:1287--1290`) delivers the
  denser Bob child and its column density, at the dyadic index
  `ell_v = log_2 kappa_v` supplied by section 2 rather than assumed;
* the join (`SelectDischarge.nodeProjection_transport_density`) carries that
  density to the bracket family's column type, with `eIdx` the selection itself
  and `eCol` the identity of `eq:reference-all-columns`;
* the discharge (`SelectDischarge.hselect_of_trims_and_projection`) assembles the
  bracket member from `09:1291--1296`'s trims and that density and fires the
  residual comparison, with `iotaB` the section of §4, `hcol` its routing readout,
  `hrow` the certificate's own rows at the node, and `hgame` §5's interlace
  identity.

The conclusion is the exact consequent of the binder `hselect` carried through
`SplitFirstBobInstance`, `LargeCapacityBranch`, `TranscriptLevelJoin` and
`FirstBobLightDichotomy`, at the paper's own quantities: copy count
`2^{ell_v-1}+1` (`A:158`), row density `kappa_v x_T` (`09:1296`), column density
`y^2` at the DEFINED `y = 3/5` (`09:436`).

*Why the trivial witness fails.*  The deliverable is existential in the child bit
only, and no fixed bit works: the banked
`RoutingDynamics.projection_denserChild_needs_the_right_bit` exhibits a Bob query
sending every column to the `true` child, so the bound at `false` fails outright.
The frozen "*the* denser Bob child" names a genuine choice, and the body of the
existential is an inequality between two named quantities, with nothing to
witness.

General in the four carriers, in `q`, `k_ref`, `r`, `A_0`, `E_0`, the node, the
retained column set, `x_T`, the reference inclusion, the trims and the
placement. -/
theorem hselect_of_reference_construction {Yc RwN Rw : Type*} [Fintype Yc] [DecidableEq Yc]
    [Fintype Rw] {q k r A0 : ℕ} {E0 : Finset (Fin q)}
    (Nmat : RwN → Yc → Bool) (Gmat : Rw → Yc → Bool) (ιR : Rw → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) (hv : (canonicalSystem hcomp hR).firstBob v = true)
    {S : Finset (Fin q → Yc)} {xT : ℝ}
    (hsmall : kappaAt P R A0 r v < 2 ^ k)
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (B : StartedCoord E0 → Finset Rw)
    (hB : ∀ i ∈ representedCoords P R A0 r v,
      ⌈(Fintype.card Rw : ℝ) * (((kappaAt P R A0 r v : ℕ) : ℝ) * xT)⌉₊ ≤ (B i).card)
    (plc : StartedCoord E0 → Rw → X)
    (hblock : ∀ i ∈ representedCoords P R A0 r v, ∀ a ∈ B i,
      plc i a ∈ rowsAt P (R i) v.val)
    (hplace : ∀ (i : StartedCoord E0) (a : Rw), ∀ c ∈ S,
      g (plc i a) c = interlaceFun Nmat q (startedIdx i, ιR a) c)
    (hcount : smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card) :
    ∃ b : Bool,
      LambdaGE Gmat (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1)
          (((kappaAt P R A0 r v : ℕ) : ℝ) * xT) ((3 / 5 : ℝ) ^ 2)
        ≤ (descend P (v.val ++ [b])).cost := by
  classical
  -- §2: the width chain, supplied through the banked `kappaAt`.
  have hwidth : smallCopyWidth (kappaAt P R A0 r v)
      = 2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1 := smallCopyWidth_kappaAt hcomp hR hv
  have hcount' : 2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1
      ≤ (representedCoords P R A0 r v).card := hwidth ▸ hcount
  -- `09:1283` produces the selection of `u_{kappa_v}` represented coordinates.
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcount'
  have eT : Fin (2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1) ≃ {i // i ∈ T} :=
    (T.equivFin.trans (finCongr hTcard)).symm
  set pc := 2 ^ (Nat.log 2 (kappaAt P R A0 r v) - 1) + 1 with hpc
  set coordOf : Fin pc → StartedCoord E0 := fun j => (eT j).val with hcoordOf
  set σ : Fin pc → Fin q := fun j => startedIdx (coordOf j) with hσdef
  have hcoordMem : ∀ j, coordOf j ∈ representedCoords P R A0 r v := by
    intro j
    exact hTsub (eT j).2
  have hσinj : Function.Injective σ := by
    intro j₁ j₂ h
    have h1 : (eT j₁).val = (eT j₂).val := startedIdx_injective h
    exact eT.injective (Subtype.ext h1)
  set J : Finset (Fin q) := Finset.image σ Finset.univ with hJdef
  have hJcard : J.card = pc := card_image_selection σ hσinj
  set eIdx : Fin pc ≃ {i // i ∈ J} := selectionEquiv σ hσinj with heIdxdef
  have heIdx : ∀ j, (eIdx j).val = σ j := by
    intro j
    rw [heIdxdef]
    exact selectionEquiv_val σ hσinj j
  -- The selected addresses avoid `E_0`: §1's `F3` discharge.
  have hout : ∀ i ∈ J, i ∉ E0 := by
    intro i hi
    refine representedCoords_avoids_E0 v i ?_
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨coordOf j, hcoordMem j, hj⟩
  -- Leg (1) at the dyadic index `ell_v`.
  have hbob : IsBobNode (descend P ((canonicalSystem hcomp hR).node v)) :=
    ((canonicalSystem hcomp hR).firstBob_spec v hv).2.1
  have hl : Nat.log 2 (kappaAt P R A0 r v) ∈ Finset.Ico 1 k :=
    Finset.mem_Ico.mpr ⟨TranscriptLevelJoin.one_le_log_kappaAt_of_firstBob hcomp hR hv,
      log_kappaAt_lt_of_lt_tRef v hsmall⟩
  have hJwidth : J.card = smallCopyWidth (2 ^ Nat.log 2 (kappaAt P R A0 r v)) := by
    rw [hJcard, pow_log_kappaAt, hwidth]
  obtain ⟨b, hdens⟩ :=
    projection_at_a_node (canonicalSystem hcomp hR) v S hbob hcover hl hJwidth hout
  -- The join: leg (1)'s density in the bracket family's own units.
  have hC : ((3 : ℝ) / 5) ^ 2 * (Fintype.card Yc : ℝ) ^ pc
      ≤ ((transportedProj P S J (v.val ++ [b]) eIdx (Equiv.refl Yc)).card : ℝ) :=
    nodeProjection_transport_density eIdx (Equiv.refl Yc) hdens
  -- The row side: `09:1291--1296`'s trims, placed.
  set B' : Fin pc → Finset Rw := fun j => B (coordOf j) with hB'def
  have hBfloor : ∀ j, ⌈(Fintype.card Rw : ℝ) * (((kappaAt P R A0 r v : ℕ) : ℝ) * xT)⌉₊
      ≤ (B' j).card := fun j => hB (coordOf j) (hcoordMem j)
  set iotaA : {a // a ∈ blockRows B'} → X := fun a => plc (coordOf a.1.1) a.1.2 with hiotaA
  set iotaB : {c // c ∈ transportedProj P S J (v.val ++ [b]) eIdx (Equiv.refl Yc)}
      → (Fin q → Yc) := ambientColumn P S J (v.val ++ [b]) eIdx (Equiv.refl Yc) with hiotaB
  have hrow : ∀ a, RouteRows P (v.val ++ [b]) (iotaA a) := by
    intro a
    have hmem : a.1.2 ∈ B' a.1.1 := (mem_blockRows B' a.1).mp a.2
    have hrows : plc (coordOf a.1.1) a.1.2 ∈ rowsAt P (R (coordOf a.1.1)) v.val :=
      hblock (coordOf a.1.1) (hcoordMem a.1.1) a.1.2 hmem
    exact routeRows_snoc_of_isBobNode hbob (routeRows_of_mem_rowsAt hrows) b
  have hcol : ∀ c, RouteCols P (v.val ++ [b]) (iotaB c) := fun c => routeCols_ambientColumn c
  -- `SELECT-EMBED-001`: the interlace identity, proved.
  have hgame : ∀ a c, interlaceFun Gmat pc a.1 c.1 = g (iotaA a) (iotaB c) := by
    intro a c
    have hyagree : ∀ j : Fin pc, iotaB c (σ j) = c.val j := by
      intro j
      have := ambientColumn_apply (P := P) (S := S) (J := J) (p := v.val ++ [b])
        (eIdx := eIdx) (eCol := Equiv.refl Yc) c j
      rw [heIdx j] at this
      exact this
    have hmemS : iotaB c ∈ S :=
      (Finset.mem_inter.mp (ambientColumn_mem (P := P) (S := S) (J := J)
        (p := v.val ++ [b]) (eIdx := eIdx) (eCol := Equiv.refl Yc) c)).1
    calc interlaceFun Gmat pc a.1 c.1
        = interlaceFun Nmat q (σ a.1.1, ιR a.1.2) (iotaB c) :=
          interlaceFun_reference_copy Nmat Gmat ιR hsub σ (iotaB c) c.1 hyagree a.1
      _ = g (iotaA a) (iotaB c) := (hplace (coordOf a.1.1) a.1.2 (iotaB c) hmemS).symm
  exact ⟨b, hselect_of_trims_and_projection Gmat halleged v b B'
    (transportedProj P S J (v.val ++ [b]) eIdx (Equiv.refl Yc)) hBfloor hC iotaA iotaB
    hrow hcol hgame hcount⟩

end Composition

/-! ## §7  The two `cc-t5e` deliverables re-fired with `hselect` gone

`SelectDischarge`'s section 5 re-fired both dichotomies with `hselect` replaced by
the localization datum `(hmem, iotaA, iotaB, hrow, hcol, hgame)`.  Here they are
re-fired again with that datum **also** gone: what remains is the construction of
`09:105--123` plus the frozen inputs of section 6.

**What is honestly different from the predecessor, in added restrictive
hypotheses: `hsmall`, and nothing else.**  (That scope is exact and is not the
whole delta: these statements also *specialize the carriers* to the frozen
ambient of `09:107` -- `Y := Fin q -> Yc`, `Z := Bool`, `Cl := Yc` and
`Coord := StartedCoord E_0`, where the predecessor is generic.  That
specialization is disclosed separately at `:283--285` and in the docstring of the
first re-fire below, and it adds no hypothesis; the sentence above is about
hypotheses only.)
The predecessor's re-fires carried `hselect` as a binder over *both* capacity
branches; these carry the branch-(ii) entry condition `kappa_v < t_ref`
(`09:1276--1277`, `hsmall`) instead, because the covers of `09:442--445` exist
only "for every dyadic `2 <= kappa < t_ref`" and the selection argument is
branch (ii)'s.  So the two forms are incomparable *along that one axis*: this one
discharges the binder exactly where the paper proves it, at the cost of naming the
branch the paper states it in.  Branch (i) is untouched and still runs inside the
banked dichotomy through its own certified-scale endpoint; nothing here restates
either branch.

**And `hsmall` is the whole delta -- in particular `09:1283`'s count is not a
second, unnamed one.**  Neither declaration below takes
`smallCopyWidth (kappaAt ...) <= (representedCoords ...).card` as a hypothesis.
The count is *decided inside the proof*: `by_cases hcnt` sends the positive branch
into section 6's composition and closes the negative branch by `absurd` against
the banked dichotomy's `hselect` slot, which the banked interface already states
in implication form.  So no antecedent is hoisted past
`TranscriptLevelJoin.cover_of_heavy` -- the banked derivation of that very
inequality from heaviness (`09:1280--1283`), which
`TranscriptLevelJoin.branchTwo_firstBobLight_join` runs inside the frozen
contradiction -- and the two statements keep parity with the banked predecessors
`SelectDischarge.canonical_firstBobLight_dichotomy_of_localized_copies` and its
schedule-indexed twin, which carry no such binder either.  Hoisting it *was* the
defect the statement gate recorded on this module and it is repaired here, not
disclosed away.

`vartheta` in both conclusions is `DenseWrapperFrontier.vartheta` (the `9/16` of
`09:1268`), never `ParameterSchedule.vartheta`; the twin is named here once for
both statements, and neither is restated or evaluated. -/

section Refire

open EthInapproximability.ParameterizedNP.FirstBobLightDichotomy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) on branch (ii), with
`hselect` discharged.**

`FirstBobLightDichotomy.canonical_firstBobLight_dichotomy` consumed by pin, with
its `hselect` binder supplied by section 6's composition at the child bit that
leg (1) delivers.  Every other binder -- `hLocEx` (branch (i)'s certified-scale
endpoint `A:109--146`, the place `EXPANDER-001` would enter), both budget readings
of `09:1306--1308`, and every schedule parameter -- is passed through verbatim,
and the conclusion is the frozen `W_v < vartheta kappa_v` with `vartheta` the
`DenseWrapperFrontier` twin.

The ambient carriers are the frozen ones (`Fin q -> Yc` for Bob, `Bool` output),
because the composition is about the interlace `U = <N>^q` of `09:107`; the
predecessor is general there, so this is a specialization to the frozen setting
and not a weakening.

*Why no full-bundle pole is fired here.*  Unchanged from the predecessor: `hk`
with `hq4` forces `r >= 6`, and at the guard boundary `k = 4` branch (i)'s `hE2`
is false for every `theta <= 1`
(`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`),
so a `False` derived at any decidable instance would measure `hE2` rather than
this statement.  This tranche adds only the construction data, whose index
constraints are measured separately in section 8.

General in the carriers, `q`, `k_ref`, `r`, `A_0`, `E_0`, the node and every
schedule parameter. -/
theorem firstBobLight_of_reference_construction {Yc RwN Rw : Type*} [Fintype Yc]
    [DecidableEq Yc] [Fintype Rw] {q k r A0 : ℕ} {E0 : Finset (Fin q)}
    (Nmat : RwN → Yc → Bool) (Gmat : Rw → Yc → Bool) (ιR : Rw → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) (hv : (canonicalSystem hcomp hR).firstBob v = true)
    {S : Finset (Fin q → Yc)} {C Bbud tcert : ℕ} {xT θ colDens : ℝ}
    (hC : 3 ≤ C) (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw) (hCne : 1 ≤ Fintype.card Yc)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcolDens : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : Bbud + (v.val.length + 1) ≤ C + r - 1)
    (hcost : P.cost ≤ C + r - 1)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) →
      (C - 1) + (r - v.val.length) ≤ Bbud)
    (hsmall : kappaAt P R A0 r v < 2 ^ k)
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (B : StartedCoord E0 → Finset Rw)
    (hB : ∀ i ∈ representedCoords P R A0 r v,
      ⌈(Fintype.card Rw : ℝ) * (((kappaAt P R A0 r v : ℕ) : ℝ) * xT)⌉₊ ≤ (B i).card)
    (plc : StartedCoord E0 → Rw → X)
    (hblock : ∀ i ∈ representedCoords P R A0 r v, ∀ a ∈ B i,
      plc i a ∈ rowsAt P (R i) v.val)
    (hplace : ∀ (i : StartedCoord E0) (a : Rw), ∀ c ∈ S,
      g (plc i a) c = interlaceFun Nmat q (startedIdx i, ιR a) c) :
    frontierWeight P R A0 r v < vartheta * ((kappaAt P R A0 r v : ℕ) : ℝ) := by
  by_cases hcnt : smallCopyWidth (kappaAt P R A0 r v) ≤ (representedCoords P R A0 r v).card
  · obtain ⟨b, hsel⟩ := hselect_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR v hv
      hsmall hcover B hB plc hblock hplace hcnt
    exact canonical_firstBobLight_dichotomy Gmat hcomp hR b hv hC hk hq4 hxT0 hxT1 hθ0 hθ1
      hGne hCne hgate hbase htcert hE1 hE2 hcolDens hbudget hcost hLocEx (fun _ => hsel)
  · exact canonical_firstBobLight_dichotomy Gmat hcomp hR false hv hC hk hq4 hxT0 hxT1 hθ0 hθ1
      hGne hCne hgate hbase htcert hE1 hE2 hcolDens hbudget hcost hLocEx (fun h => absurd h hcnt)

/-- **The schedule-indexed dichotomy with `hselect` discharged.**

The second `cc-t5e` deliverable re-fired the same way: `A_0` pinned to `09:1219`'s
`ceil(2 x_T m_G)` through the banked `initialRefRows`, the node on coordinate
`i`'s route, and the second conjunct `09:1291--1296` executed.

`hone` is inherited verbatim and **not** retired: it is an *extra* hypothesis
relative to `09:1291--1296`, and retiring it is the open **`L1-F6`**, an edit to
`WrapperDenseFrontierWiring` and therefore its own tranche.

*Why the trivial witness fails.*  `T = empty` is refuted by the `Nonempty`
conjunct, exactly as in the predecessor; the light conjunct is refutable at the
banked `TranscriptLevelJoin.interiorAudit_is_not_light`.

General in the carriers, `q`, `k_ref`, `r`, `E_0`, the node, the coordinate and
every schedule parameter. -/
theorem firstBobLight_of_reference_construction_at_paper_schedule {Yc RwN Rw : Type*}
    [Fintype Yc] [DecidableEq Yc] [Fintype Rw] {q k r : ℕ}
    {E0 : Finset (Fin q)} (Nmat : RwN → Yc → Bool) (Gmat : Rw → Yc → Bool) (ιR : Rw → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool} {xT : ℝ}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ i, refRowFloor (initialRefRows xT (Fintype.card X)) r ≤ (R i).card)
    (v : FrontierNode P R (initialRefRows xT (Fintype.card X)) r)
    (i : StartedCoord E0)
    (hp : v.val ∈ coordRoutes P R (initialRefRows xT (Fintype.card X)) r i)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    {S : Finset (Fin q → Yc)} {C Bbud tcert : ℕ} {θ colDens : ℝ}
    (hC : 3 ≤ C) (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw) (hCne : 1 ≤ Fintype.card Yc)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcolDens : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : Bbud + (v.val.length + 1) ≤ C + r - 1)
    (hcost : P.cost ≤ C + r - 1)
    (hone : 1 ≤ ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
      * ((Fintype.card X : ℕ) : ℝ))
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R (initialRefRows xT (Fintype.card X)) r v).card : ℕ) : ℝ) →
      (C - 1) + (r - v.val.length) ≤ Bbud)
    (hsmall : kappaAt P R (initialRefRows xT (Fintype.card X)) r v < 2 ^ k)
    (hcover : ∀ l ∈ Finset.Ico 1 k, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K S → (E0 ∩ K).Nonempty)
    (B : StartedCoord E0 → Finset Rw)
    (hB : ∀ j ∈ representedCoords P R (initialRefRows xT (Fintype.card X)) r v,
      ⌈(Fintype.card Rw : ℝ)
          * (((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT)⌉₊
        ≤ (B j).card)
    (plc : StartedCoord E0 → Rw → X)
    (hblock : ∀ j ∈ representedCoords P R (initialRefRows xT (Fintype.card X)) r v,
      ∀ a ∈ B j, plc j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ (j : StartedCoord E0) (a : Rw), ∀ c ∈ S,
      g (plc j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c) :
    frontierWeight P R (initialRefRows xT (Fintype.card X)) r v
        < vartheta
          * ((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ)
      ∧ ∃ T ⊆ rowsAt P (R i) v.val,
          T.card = ⌈((kappaAt P R (initialRefRows xT (Fintype.card X)) r v : ℕ) : ℝ) * xT
              * ((Fintype.card X : ℕ) : ℝ)⌉₊
            ∧ T.Nonempty := by
  classical
  by_cases hcnt : smallCopyWidth (kappaAt P R (initialRefRows xT (Fintype.card X)) r v)
      ≤ (representedCoords P R (initialRefRows xT (Fintype.card X)) r v).card
  · obtain ⟨b, hsel⟩ := hselect_of_reference_construction Nmat Gmat ιR hsub halleged hcomp hR v hv
      hsmall hcover B hB plc hblock hplace hcnt
    exact canonical_firstBobLight_dichotomy_at_paper_schedule Gmat hcomp hR i b hp hv hC hk hq4
      hxT0 hxT1 hθ0 hθ1 hGne hCne hgate hbase htcert hE1 hE2 hcolDens hbudget hcost hone hLocEx
      (fun _ => hsel)
  · exact canonical_firstBobLight_dichotomy_at_paper_schedule Gmat hcomp hR i false hp hv hC hk hq4
      hxT0 hxT1 hθ0 hθ1 hGne hCne hgate hbase htcert hE1 hE2 hcolDens hbudget hcost hone hLocEx
      (fun h => absurd h hcnt)

end Refire

/-! ## §8  Aux-lemma battery, non-vacuity and the statement poles

**NON-FIDELITY / BEYOND-PAPER** throughout this section: the paper's own instance
of the composition is a function of the **alleged** protocol of `09:1188--1193`,
whose non-existence is the conclusion of the whole argument, so no paper instance
exists to exhibit and nothing here discharges the deferred canonical-inhabitation
registration.  Section 1's `startedCoord_nonempty` is the exception: it inhabits
the paper's own started carrier at the paper's own legality condition. -/

section Battery

/-- **Aux B1 (round trip on the selection).**  A selection of two distinct
coordinates identifies the copy index with its image and nothing else.
**BEYOND-PAPER AUDIT** in the carriers. -/
theorem selectionEquiv_roundTrip :
    ∃ h : Function.Injective (![(0 : Fin 3), 2]),
      (Finset.image (![(0 : Fin 3), 2]) (Finset.univ : Finset (Fin 2))).card = 2
        ∧ ∀ j, (selectionEquiv (![(0 : Fin 3), 2]) h j).val = (![(0 : Fin 3), 2]) j := by
  have hinj : Function.Injective (![(0 : Fin 3), 2]) := by decide
  exact ⟨hinj, card_image_selection _ hinj, fun j => selectionEquiv_val _ hinj j⟩

/-- **The composition's index constraints are jointly satisfiable, at the smallest
value the banked guard `hk` allows (HYPOTHESIS-CONSISTENCY, partial and labelled
so).**

Section 6 imposes three arithmetic conditions on the node at once: `ell_v >= 1`
(from `09:1259`'s `kappa_v >= 2`), `ell_v < k_ref` (from `09:1276--1277`'s
`kappa_v < t_ref`, the binder `hsmall`), and the width identity
`u_{kappa_v} = 2^{ell_v-1}+1`.  They hold simultaneously at `kappa_v = 2` and
`k = 4`, so the composition's index bundle is **not** contradictory.

**The `4` is not a paper value and is not claimed to be one.**  `kappa_v = 2` is
paper-derived (`09:1259`, "Every first-Bob node has `kappa_v >= 2`").  The `4` is
merely the boundary of the Lean-visible guard `hk : 4 <= k` carried by the banked
chain.  The paper's own `k_ref` is DEFINED by `eq:tref-search` (`06:558--572`,
verified first-hand this round) as *the least integer satisfying*
`k_ref >= max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}` together with two further
`2^{...}` clauses, whence `k_ref >= 2^19 = 524288` -- five orders of magnitude
above `4`, and far beyond any decidable instance.  This module corroborates the
illegality itself, at the `firstBobLight_of_reference_construction` docstring
**above** (`:786--792`, i.e. earlier in the file than this battery): the banked
`FirstBobLightDichotomy.branchOne_analytic_binder_fails_below_the_tref_floor`
shows branch (i)'s `hE2` is unsatisfiable at `k = 4`, `C = 3`, `theta <= 1`.  The
value is therefore usable here **only** under section 8's blanket
**NON-FIDELITY / BEYOND-PAPER AUDIT** label; choosing it because it is the
boundary of the locally-visible constraints would be an authoring defect if it
were dressed as paper legality, and no such claim is made.  Statement and proof
are unaffected by this correction.

**This is a partial check and is labelled as such.**  The full hypothesis bundle
of `hselect_of_reference_construction` -- an alleged protocol with a first-Bob
node over the started carrier, a cover, trims and a placement -- is **not**
exhibited here, and the green build must not be read as non-vacuity of it: the
paper's own instance is a function of the alleged protocol of `09:1188--1193`,
whose non-existence is the argument's conclusion, so the deferred
canonical-inhabitation registration stands and a synthetic full-bundle instance
remains a named successor measurement, not a claim of this tranche. -/
theorem composition_index_constraints_are_jointly_satisfiable :
    Nat.log 2 2 ∈ Finset.Ico 1 4
      ∧ smallCopyWidth 2 = 2 ^ (Nat.log 2 2 - 1) + 1
      ∧ (2 : ℕ) < 2 ^ 4 := by
  have hlog : Nat.log 2 2 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  refine ⟨?_, ?_, by norm_num⟩
  · rw [hlog]
    decide
  · rw [hlog]
    exact smallCopyWidth_dyadic (le_refl 1)

/-- **Non-vacuity of the reference-copy embedding (LANE-GATE 3).**

`interlaceFun_reference_copy` would prove nothing if it were only reachable at a
constant matrix or at `G = N`, and a green build cannot see the difference.  Here
it fires with `N` the **nonconstant** equality matrix on two symbols, `G` a
**proper** row-submatrix of it (`Rw = Fin 1`, `ιR = 0`, i.e. `R_G` a single row of
two, the shape `09:113--116` gives) on the **full** column alphabet
(`eq:reference-all-columns`), at a genuine selection of one coordinate out of two
(`sigma 0 = 1`), and with both Boolean values occurring on `G` itself.

**BEYOND-PAPER AUDIT** in every value: `09:105--123`'s own carriers are far beyond
any decidable instance. -/
theorem interlace_reference_copy_is_nondegenerate :
    interlaceFun (fun (_ : Fin 1) (c : Fin 2) => decide ((0 : Fin 2) = c)) 1
        ((0 : Fin 1), (0 : Fin 1)) (fun _ => 0) = true
      ∧ interlaceFun (fun (_ : Fin 1) (c : Fin 2) => decide ((0 : Fin 2) = c)) 1
        ((0 : Fin 1), (0 : Fin 1)) (fun _ => 1) = false
      ∧ ∀ (y : Fin 2 → Fin 2) (cJ : Fin 1 → Fin 2),
          (∀ j, y (![(1 : Fin 2)] j) = cJ j) →
          ∀ a : Fin 1 × Fin 1,
            interlaceFun (fun (_ : Fin 1) (c : Fin 2) => decide ((0 : Fin 2) = c)) 1 a cJ
              = interlaceFun (fun a c : Fin 2 => decide (a = c)) 2
                  (![(1 : Fin 2)] a.1, (fun _ : Fin 1 => (0 : Fin 2)) a.2) y := by
  refine ⟨by decide, by decide, fun y cJ hy a => ?_⟩
  exact interlaceFun_reference_copy (fun a c : Fin 2 => decide (a = c))
    (fun (_ : Fin 1) (c : Fin 2) => decide ((0 : Fin 2) = c)) (fun _ => (0 : Fin 2))
    (fun _ _ => rfl) ![(1 : Fin 2)] y cJ hy a

/-- **Statement pole: the cover clause's antecedent is a real condition.**

`hcover` (`09:442--445`) is an implication whose antecedent is poorness of the
selected set.  If poorness held of every set the clause would carry no
information, and section 6's `hout` would be doing all the work.  It does not: at
full retention the projection has density `1 > rho = 18/25`, so the antecedent
fails outright, and the frozen covers are cutting out a genuine minority.
**BEYOND-PAPER AUDIT** in the carriers; `rho` is the paper's DEFINED `2y^2`. -/
theorem cover_antecedent_is_refutable :
    ¬ PoorProjection rhoSmall (Finset.univ : Finset (Fin 1))
        (Finset.univ : Finset (Fin 1 → Fin 2)) := by
  have hcard : (projSet (Finset.univ : Finset (Fin 1))
      (Finset.univ : Finset (Fin 1 → Fin 2))).card = 2 := by decide
  simp only [PoorProjection, hcard, rhoSmall, Fintype.card_fin, Finset.card_univ]
  norm_num

/-- **Statement pole: the agreement on selected coordinates is not free.**

Without `hy` the interlace identity is false: at the equality matrix, the
selection `sigma 0 = 1`, the ambient column `y = (0,0)` and the projected column
`cJ = (1)`, the two sides are `true` and `false`.  So `hy` -- which section 4's
section supplies -- is load-bearing, and `interlaceFun_reference_copy` is not an
identity of shapes.  **BEYOND-PAPER AUDIT** in the carriers. -/
theorem reference_copy_needs_the_selected_agreement :
    interlaceFun (fun a c : Fin 2 => decide (a = c)) 1 ((0 : Fin 1), (1 : Fin 2))
        (fun _ => 1) ≠
      interlaceFun (fun a c : Fin 2 => decide (a = c)) 2 ((1 : Fin 2), (1 : Fin 2))
        (fun _ => 0) := by
  decide

end Battery

end EthInapproximability.ParameterizedNP.SelectEmbedComposition
