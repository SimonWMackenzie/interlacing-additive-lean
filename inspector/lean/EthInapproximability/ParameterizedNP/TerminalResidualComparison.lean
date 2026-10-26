import EthInapproximability.ParameterizedNP.TerminalCertificateInputs

/-!
# Parameterized NP route: the residual comparison at a node of the alleged protocol

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand this tranche).  `sections/08-dense-stage4.tex` is read
  for cross-anchors only and **no hash is pinned for it** -- see the note on
  hashes below.
* **The exact frozen lines traced here**, in print order:
  * **`09:918--919`** -- the alleged protocol of phase 1: "Transpose this
    fixed-bin state, and suppose for contradiction that the resulting matrix has
    a protocol `P_2` of depth at most `D_2`."
  * **`09:919--921`** -- the budget convention this module's conclusion is stated
    in: "Until `eq:terminal-fixed-bin`, every remaining-budget reference is to
    the suffix depth in `P_2`."
  * **`09:1037--1039`** -- the alleged protocol of phase 2: "Now suppose for
    contradiction that `Z` has a protocol `P_3` of depth at most
    `C-1 = D_2 + log_2 s` ...  Every remaining-budget reference in this second
    part is to the suffix depth in `P_3`."
  * **`09:943--946`** -- the node's game as a restriction read through sections:
    "At any such node, project to the coordinate carried by an ordinary token and
    transpose the resulting local block."  This is the frozen instruction that
    the node's game is the ambient game *read through* a row map and a column
    map -- which is why the deliverable below is stated with two explicit
    sections `iota_A`, `iota_B` and not only for literal sub-Finsets.
  * **`09:1039--1044`** -- the party orientation of phase 2, which is what makes
    the Alice/Bob split of the route rectangle load-bearing: "Transpose to the
    Stage-3 selector orientation.  Thus Alice owns the `s` outer row blocks of
    `interlace(S_2, s)`, while Bob owns its product columns."
  * **`09:1076`** -- "Until the first Bob query, these Alice restrictions do not
    change the ordinary and foreign fibre sets `O_alpha, F_alpha`", the frozen
    sentence whose two carriers are censused in §5--§6.
  * **`09:512--516`** (`rho_p(c) = j(p)`), **`09:518--527`** (`E_o`, `E_f`,
    `O_alpha`, `F_alpha`), **`09:804--810`** (the construction of
    `K_ord`: "Before fixing the two bins, forgetting the raw-column prefix gives
    the ordinary Stage-3 restriction ..."), **`09:814--816`** ("The least
    representatives above and the corresponding least representatives of the
    outer column projection are the entry-preserving sections in clause (iv)"),
    **`09:805`** ("the **ordinary** Stage-3
    restriction") and **`09:1085--1086`** ("the joint **ordinary** column set
    `K_ord` is unchanged") -- the six anchors the §4 census turns on.
* **Cross-anchors opened first-hand for this tranche and *not* traced into a
  declaration:** `09:862--868` (the two-phase announcement), `09:937--942` (the
  Stage-2 stopping rule), `09:953--965` and `09:1097--1110` (the two isolation
  blocks, whose residual readings this module's deliverable feeds),
  `09:1112--1123` (the first-Bob frontier), `09:1152--1173` (the phase-2 close),
  `08:946--979` (`lem:dense-no-leaf`, whose two `hnodeResidual`/`hdeepResidual`
  binders §3 discharges), and `def:two-stream-state` clauses (i) and (iv)
  (`09:500--546`, `09:609--632`).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively; the sole import is
  `TerminalCertificateInputs`, whose ledger row records the same exclusion.
  The only vendored declarations consumed are
  `Workspace.UpperBound.Protocol.comap`, `.comap_cost` and `.comap_eval`, which
  reach the same three Lean-kernel axioms as the rest of the facade.

**A note on hashes.**  Only the section-09 hash above is a pin: it was
recomputed after this file's final edit and re-verified immediately before this
tranche returned.  No other SHA-256 is pinned by this module, and no ledger row
of this tranche pins one.

## Reader counterpart

**This module claims no reader item, deliberately rather than by omission.**  The
41-page reader artifact was swept first-hand this tranche
(`routes/parameterized-np/reader-facing/sections/`, all nine files) for the two
facts below, and the outcome is two *declinations*, each with its reason:

* `01-introduction.tex:126--131`, "suppose an optimal depth-`C` protocol for a
  matrix begins with an Alice query.  One child contains at least half the rows
  and is computed by a protocol of depth at most `C-1`", is a verbatim
  statement of §2's residual comparison -- but it is **unlabelled introduction
  prose inside the overview of a refuted route** (the direct-full-anchor
  obstruction), not a labelled statement.  The `FinalOnlyDuplication` precedent
  (`01-introduction.tex:234--237`) declines exactly this kind of locus, and
  the reader-counterpart rule forbids citing prose as a statement.  Declined.
* `A-stage4-details.tex:256--259`, "The Stage--2 lower bounds are applied to
  quotient supports ... while the residual protocol is routed through arbitrary
  later queries", is the reader's condensation of the same mechanism -- but both
  of its clauses are **already assigned**: `256--258` to `DenseRoutingThresholds`
  and `258--259` to `DenseBranchSelection`.  A reader item may not be assigned
  twice.  Declined.
* `prop:paper-projection-facts` (`02-preliminaries.tex:119--140`) is the reader's
  monotonicity/projection package and is claimed by `InheritedContracts`; it is
  about `CC` of bracket families, not about the suffix depth of a protocol at a
  node, so it is a different fact as well as an assigned one.

The precedent for claiming none is `DenseRoutingInvariant` and
`DenseWrapperFrontier`, both of which record a named prior assignment instead of
inventing a counterpart.

## What this module is for

Every terminal-arc lower bound in the frozen phase-1 argument is a comparison
between a *certificate* at a protocol node (the node's game is hard) and a
*budget* at that node (the residual subtree is shallow).  The banked
`DenseWeightedCount` carries the certificate side and states the budget side as
a **named hypothesis** -- its coverage limit 3 says so in terms:

> `hresidual : D (gnode) <= (descend P p).cost` ... this block builds no
> rectangle apparatus and so never derives it.

That hypothesis is the *last non-certificate binder* standing between the banked
machinery and `eq:terminal-fixed-bin`, and it is exactly the one thing the frozen
proof never assumes: `09:918--919` and `09:1037--1039` **hypothesise a protocol**
and the residual reading is then a consequence of what a protocol is.  §1--§3
build the missing rectangle apparatus and derive it.

Concretely, §3's `denseNoLeaf_of_alleged_protocol` has the banked `denseNoLeaf`'s
six hypotheses **minus two**: `hnodeResidual` and `hdeepResidual` are gone,
replaced by one `Protocol.Computes` for the alleged protocol plus the node's own
sections.  Nothing else about the banked lemma changes, and no banked byte is
touched: this is supersession at the consumption site, in the
`RestrictionDatum` manner.

## §5--§6: the `hpresOrd`/`hpresFor` census (TRACE-001-class, three-outcome rule)

`TerminalCertificateInputs.terminal_averages_unchanged_until_first_bob` carries
two explicit binders, introduced there with the reason "because the frozen text
displays no equation for it":

* `hpresOrd : binImage st.Kord st.pOrd = streamImage omg rho st.pOrd XZ st.iOrd RG`
* `hpresFor : binImage st.Kord st.pFor = streamImage omg rho st.pFor XZ st.iFor st.Rfor`

Neither is instantiated anywhere in `src/` (verified first-hand this tranche by a
whole-tree search for both names), so this census changes no existing proof.  The
outcome is **split**, and the two halves are reported separately because they are
genuinely different findings.

### `hpresOrd`: **outcome (1), derivable from frozen displays.**  Discharged here.

The frozen displays are three, and together they are an equation:

1. `09:512--516`: "For a raw column `c = (xi, j) in Omega`, where `j : [s] -> J_2`,
   define `rho_p(c) = j(p) in J_2 = [q_2] x C_1`."
2. `09:518--522`: `E_o = (rho_{p_o} . omega_o)(X_o)`.
3. `09:804--810`: "Before fixing the two bins, **forgetting the raw-column
   prefix** gives the ordinary Stage-3 restriction
   `<interlace(S_2,s), union_p {p} x R_p, K_ord>`", with `09:814--816` naming its
   sections.

Forgetting the prefix of `c = (xi, j)` is `c |-> j`, and `j` *is* the tuple
`fun p => rho_p(c)`.  So `K_ord` is the image of the ordinary row stream under
`x |-> (fun p => rho p (omg x))`, which is `stage3Cols` below; and reading that
image at a bin is `Finset.image_image`.  `binImage_stage3Cols` is the resulting
one-line theorem, and `hpresOrd_of_kordDef` is `hpresOrd` **proved** from the
single frozen equation `Kord = stage3Cols ...`.

The residue is an encoding gap of a precisely nameable kind, and it is reported,
not patched: the banked `TwoStreamState` record carries `Kord` together with
`selCol`, `selCol_mem`, `selCol_inj`, `selector_entry` and `Kord_density` --
i.e. everything `09:611--632`'s clause (iv) *demands of* `K_ord` -- but **not the
`09:804--810` equation that constructs it**.  Its `selCol_mem` says only that the
section lands in the ordinary row stream; it does not say that the section
inverts the prefix-forgetting map.  So the identification cannot be read off the
record's fields, which is why `TerminalCertificateInputs` had to bind it.  The
repair is one field, `Kord_def : Kord = stage3Cols omg rho XZ iOrd RG`, and it is
**registered in the ledger, not made here**: adding a field to a banked structure
would invalidate every instance of it, which is a structural tranche of its own.
`kordDef_is_consistent_with_the_banked_fields` below is the machine-checked
statement that the proposed field does not fight the fields already present.

### `hpresFor`: **outcome (3) in encoding, not in mathematics.**  A
**FINDING**, recorded precisely and parked for Simon; the paper is not patched.

`hpresFor` asks for the **foreign** stream image at the foreign bin to be a
readout of `K_ord`.  The frozen text says twice, in its own words, that `K_ord`
is the *ordinary* carrier:

* `09:804--805`: "forgetting the raw-column prefix gives the **ordinary** Stage-3
  restriction";
* `09:1085--1086`: "Until a Bob query, the joint **ordinary** column set `K_ord`
  is unchanged".

and the banked record already agrees: `selCol_mem` pins `selCol` into
`streamRows XZ iOrd RG`, the **ordinary** row stream.  Meanwhile `E_f` is built
from `streamRows XZ iFor Rfor` (`09:508`, `09:523--525`), and the record's own
`outer_distinct` (`09:501`, `iOrd != iFor`) makes those two row sets disjoint.
So `hpresFor` equates readouts of two *different* frozen objects, and the frozen
text asserts no equation between them: `hpresFor` is **not derivable, and false
at general data**.  `ordinary_carrier_has_no_foreign_bin` is an explicit finite
countermodel at nondegenerate data (distinct outer coordinates, distinct bins,
both row streams nonempty).

*What the countermodel does and does not settle.*  Its data is raw
(`probeXZ`, `probeOmg`, `probeRho`) and is **not** exhibited as a
`TwoStreamState`, so it refutes derivability at general data; it does not show
that every legal state falsifies `hpresFor`.  Nor may disjointness of the two
physical row sets be used to argue the point: the frozen text forbids exactly
that inference at `09:534--537` -- "Their physical images are disjoint, ...
There is no requirement that the underlying subsets `O_alpha, F_alpha` be
disjoint" -- so images of disjoint row sets are deliberately allowed to
coincide.  The finding rests instead on the naming evidence above: `09:805` and
`09:1085--1086` call `K_ord` the *ordinary* carrier, `selCol_mem` pins it to the
ordinary row stream, and `E_f` is defined from the foreign stream at `09:508`
and `09:523--525`.

**This is not a `FAIL-MATH-CANDIDATE` against the paper.**  The frozen claim at
`09:1076--1078` -- that the Stage-3 Alice restrictions leave `O_alpha` *and*
`F_alpha` unchanged -- is supported by the text's **own prose section-argument**,
which is outcome (2) of the three-outcome rule and is quoted in full here:

> "Transpose to the Stage-3 selector orientation.  Thus Alice owns the `s` outer
> row blocks of `interlace(S_2, s)`, while Bob owns its product columns."
> (`09:1039--1041`)
>
> "Until the first Bob query, these Alice restrictions do not change the ordinary
> and foreign fibre sets `O_alpha, F_alpha`, so the averages
> `eq:terminal-averages` are unchanged."  (`09:1076--1078`)

Both fibre families are Bob-side data in that orientation, and an Alice query
deletes only rows; that is the whole argument and it is sound.  What is *absent*
from clause (iv) is a **name** for the foreign stream's Stage-3 column carrier --
clause (iv) names only `K_ord`, because the foreign component is not routed as a
bin of its own but attached to the ordinary object in the distinguished bin
(`09:1046--1050`).  The gap is therefore a naming gap in the source and a
mis-transcription in our Lean, in that order of blame, and the honest repair uses
the paper's own one-formula habit: the same `stage3Cols` at the *foreign* stream
data.  `foreign_bin_of_foreign_carrier` proves the corrected identification, and
`terminal_averages_unchanged_of_carriers` is the corrected invariance -- the
ordinary half now **derived from the single registered equation `hKord`**
(itself an unproved binder, registered in the ledger for a later structural
tranche) rather than bound outright, the foreign half stated about the carrier
it is actually about.

**What is parked for Simon** (one item, and it is the only thing this tranche
asks for): whether `stage3Cols omg rho XZ iFor Rfor` is the intended reading of
the foreign Stage-3 column carrier, or whether the intended reading is the
tagged foreign fibre family of clause (ii) (`09:576--578`,
`{f} x {alpha} x F_alpha`) transported to the selector orientation.  The two are
*expected* to agree on their bin readouts, but that is an expectation and not a
consequence of `binImage_stage3Cols`, which is about the tuple carrier and says
nothing about the clause-(ii) triple family -- a different type.  Nothing landed
below depends on the answer; but the record field that eventually replaces
`hpresFor` does.

## Dependencies, imports and adapters

* Import: `EthInapproximability.ParameterizedNP.TerminalCertificateInputs` only.
* Consumed **by pin**, never restated: `Workspace.UpperBound.Protocol.comap`,
  `Protocol.comap_cost`, `Protocol.comap_eval`;
  `DenseWeightedCount.descend`, `.descendStep`, `.descend_cons`, `.IsBobPath`,
  `.StoppedToken`, `.denseNoLeaf`, `.node_not_leaf`, `.one_le_D_of_ne`;
  `RoutedCertificateSystem.IsAlicePath`; `DenseSynchronisation.IsANode`;
  `TwoStreamState.streamRows`, `.streamImage`, `.colFibre`, `.meanFibreDensity`;
  `TerminalCertificateInputs.binImage`, `.kordAt`, `.fibreAt`,
  `.fibres_unchanged_until_first_bob`; `NPCC.subgame`.
* Proof status: **new** (§1--§3 build apparatus the development did not have;
  §4 derives one previously bound identification and refutes another).
* Unproved placeholders, new axioms and opaque certificates: **none**.  Axiom
  surface of every named result: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace EthInapproximability.ParameterizedNP.TerminalResidualComparison

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.DenseWeightedCount

/-! ## §1  The route rectangle of an alleged protocol (`09:918--919`,
`09:1037--1039`, `09:1039--1044`)

A protocol node is reached by an address, and the set of inputs that reach it is
a *rectangle*: Alice's constraint depends only on `x` and Bob's only on `y`.  The
frozen proof uses that split at every step -- `09:1039--1044` fixes which player
owns which side, `09:1076` reasons that "these Alice restrictions" leave the
Bob-side fibre sets alone -- so the two halves are separate definitions here,
never one joint predicate on pairs. -/

section Rectangle

variable {X Y Z : Type*}

/-- The Alice-side constraint imposed by taking edge `b` at the node `P`.  At a
Bob node and at a leaf there is none: `09:1043--1044`'s "the ordinary column set
remains unchanged until the first Bob query" is the same observation with the
players exchanged. -/
def aliceStepConsistent : Protocol X Y Z → Bool → X → Prop
  | Protocol.aNode a _ _, b, x => a x = b
  | _, _, _ => True

/-- The Bob-side constraint imposed by taking edge `b` at the node `P`.  At an
Alice node and at a leaf there is none -- this is the formal content of
`09:1076`'s "Until the first Bob query". -/
def bobStepConsistent : Protocol X Y Z → Bool → Y → Prop
  | Protocol.bNode f _ _, b, y => f y = b
  | _, _, _ => True

/-- Alice's half of the rectangle of inputs reaching the node addressed by `p`. -/
def RouteRows : Protocol X Y Z → List Bool → X → Prop
  | _, [], _ => True
  | P, b :: p, x => aliceStepConsistent P b x ∧ RouteRows (descendStep P b) p x

/-- Bob's half of the rectangle of inputs reaching the node addressed by `p`. -/
def RouteCols : Protocol X Y Z → List Bool → Y → Prop
  | _, [], _ => True
  | P, b :: p, y => bobStepConsistent P b y ∧ RouteCols (descendStep P b) p y

@[simp] theorem routeRows_nil (P : Protocol X Y Z) (x : X) : RouteRows P [] x := trivial

@[simp] theorem routeCols_nil (P : Protocol X Y Z) (y : Y) : RouteCols P [] y := trivial

theorem routeRows_cons (P : Protocol X Y Z) (b : Bool) (p : List Bool) (x : X) :
    RouteRows P (b :: p) x ↔
      aliceStepConsistent P b x ∧ RouteRows (descendStep P b) p x := Iff.rfl

theorem routeCols_cons (P : Protocol X Y Z) (b : Bool) (p : List Bool) (y : Y) :
    RouteCols P (b :: p) y ↔
      bobStepConsistent P b y ∧ RouteCols (descendStep P b) p y := Iff.rfl

/-- **Aux R1.**  Bob's queries constrain no Alice input: along a Bob-only address
every row of the ambient carrier reaches the node.  This is the row-side reading
of `08:880`'s "Tokens can be routed through every Bob query of `P_*`" -- under the
stopping rule of `08:952--953` -- and it is what lets `08:962` say the template
row set is unchanged.  General. -/
theorem routeRows_of_isBobPath : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsBobPath P p → ∀ x : X, RouteRows P p x := by
  intro P p
  induction p generalizing P with
  | nil => intro _ x; exact routeRows_nil P x
  | cons b p ih =>
      intro h x
      obtain ⟨hnode, hrest⟩ := h
      refine ⟨?_, ih hrest x⟩
      cases P with
      | leaf z => exact absurd hnode (by simp [IsBobNode])
      | aNode a l r => exact absurd hnode (by simp [IsBobNode])
      | bNode f l r => trivial

/-- **Aux R2.**  Alice's queries constrain no Bob input: along an Alice-only
address every column of the ambient carrier reaches the node.  This is the
formal content of the frozen "Until the first Bob query" (`09:1076`), and it is
the column-side dual of `routeRows_of_isBobPath`.  General. -/
theorem routeCols_of_isAlicePath : ∀ {P : Protocol X Y Z} {p : List Bool},
    RoutedCertificateSystem.IsAlicePath P p → ∀ y : Y, RouteCols P p y := by
  intro P p
  induction p generalizing P with
  | nil => intro _ y; exact routeCols_nil P y
  | cons b p ih =>
      intro h y
      obtain ⟨hnode, hrest⟩ := h
      refine ⟨?_, ih hrest y⟩
      cases P with
      | leaf z => exact absurd hnode (by simp [DenseSynchronisation.IsANode])
      | aNode a l r => trivial
      | bNode f l r => exact absurd hnode (by simp [DenseSynchronisation.IsANode])

/-- **Aux R3.**  The rectangle decomposes along any split of the address: reaching
`p ++ q` from `P` is reaching `p` from `P` and then `q` from the node `p`
reaches.  General. -/
theorem routeRows_append : ∀ {P : Protocol X Y Z} (p q : List Bool) (x : X),
    RouteRows P (p ++ q) x ↔ RouteRows P p x ∧ RouteRows (descend P p) q x := by
  intro P p
  induction p generalizing P with
  | nil => intro q x; simp [descend_nil]
  | cons b p ih =>
      intro q x
      rw [List.cons_append, routeRows_cons, routeRows_cons, ih, descend_cons]
      tauto

/-- **Aux R4.**  Same decomposition on Bob's side.  General. -/
theorem routeCols_append : ∀ {P : Protocol X Y Z} (p q : List Bool) (y : Y),
    RouteCols P (p ++ q) y ↔ RouteCols P p y ∧ RouteCols (descend P p) q y := by
  intro P p
  induction p generalizing P with
  | nil => intro q y; simp [descend_nil]
  | cons b p ih =>
      intro q y
      rw [List.cons_append, routeCols_cons, routeCols_cons, ih, descend_cons]
      tauto

/-- **Aux R5.**  An input that reaches a node reaches every node above it.  The
frozen proof needs exactly this at the length-`(r+1)` prefix of a token's route
(`08:974--978`).  General. -/
theorem routeRows_take {P : Protocol X Y Z} {p : List Bool} {x : X}
    (h : RouteRows P p x) (n : ℕ) : RouteRows P (p.take n) x := by
  have hsplit := (routeRows_append (P := P) (p.take n) (p.drop n) x).1
  rw [List.take_append_drop] at hsplit
  exact (hsplit h).1

/-- **Aux R6.**  Same prefix closure on Bob's side.  General. -/
theorem routeCols_take {P : Protocol X Y Z} {p : List Bool} {y : Y}
    (h : RouteCols P p y) (n : ℕ) : RouteCols P (p.take n) y := by
  have hsplit := (routeCols_append (P := P) (p.take n) (p.drop n) y).1
  rw [List.take_append_drop] at hsplit
  exact (hsplit h).1

end Rectangle

/-! ## §2  The residual comparison (`09:918--919`, `09:1037--1039`,
`09:943--946`)

"suppose for contradiction that the resulting matrix has a protocol `P_2` of
depth at most `D_2`.  Until `eq:terminal-fixed-bin`, every remaining-budget
reference is to the suffix depth in `P_2`."

At a node addressed by `p`, the residual subtree `descend P p` *computes* the
ambient game on the rectangle that reaches the node.  Hence any game obtained by
reading the ambient game through sections into that rectangle -- the frozen
"project to the coordinate carried by an ordinary token and transpose the
resulting local block" (`09:943--946`) -- has complexity at most the suffix
depth.  That is the whole of the residual comparison, and it is a *consequence*
of the contradiction hypothesis rather than a companion assumption. -/

section Residual

variable {X Y Z : Type*}

/-- One step of the walk is invisible to an input inside the rectangle.
General. -/
theorem eval_descendStep_of_consistent (P : Protocol X Y Z) (b : Bool) {x : X} {y : Y}
    (hr : aliceStepConsistent P b x) (hc : bobStepConsistent P b y) :
    (descendStep P b).eval x y = P.eval x y := by
  cases P with
  | leaf z => cases b <;> rfl
  | aNode a l r =>
      simp only [aliceStepConsistent] at hr
      cases b <;> simp [Protocol.eval, descendStep, hr]
  | bNode f l r =>
      simp only [bobStepConsistent] at hc
      cases b <;> simp [Protocol.eval, descendStep, hc]

/-- **The semantic content of a node (`09:919--921`).**  On the rectangle that
reaches the node, the residual subtree computes what the whole protocol computes.
General in the carriers, the protocol and the address. -/
theorem eval_descend_of_route : ∀ {P : Protocol X Y Z} {p : List Bool} {x : X} {y : Y},
    RouteRows P p x → RouteCols P p y → (descend P p).eval x y = P.eval x y := by
  intro P p
  induction p generalizing P with
  | nil => intro x y _ _; rfl
  | cons b p ih =>
      intro x y hr hc
      obtain ⟨hr1, hr2⟩ := hr
      obtain ⟨hc1, hc2⟩ := hc
      rw [descend_cons, ih hr2 hc2]
      exact eval_descendStep_of_consistent P b hr1 hc1

/-- **The residual comparison, `09:918--919` and `09:1037--1039` (T1).**

Let `P` be an alleged protocol for the ambient game `g` -- the frozen "suppose
for contradiction that the resulting matrix has a protocol `P_2` of depth at most
`D_2`" -- and let `p` address a node of it.  Let `gnode` be the node's local
game, presented the way `09:943--946` presents it: as the ambient game read
through a row section `iotaA` and a column section `iotaB` whose images lie in
the rectangle reaching the node.  Then

  `D gnode <= (descend P p).cost`,

the frozen "every remaining-budget reference is to the suffix depth".

This is the binder `DenseWeightedCount`'s coverage limit 3 names as unproved
(`hresidual`), **derived**.  General in all five carriers, in the protocol, in
the address, and in the two sections.

*Why the trivial witness does not give this.*  The deliverable is a `<=`, not an
existential, so there is nothing to witness trivially; and it is not vacuous
either, because it is false without the rectangle hypotheses --
`residual_needs_the_rectangle` exhibits a protocol, an address and a game where
`D g = 1` while the suffix depth is `0`. -/
theorem D_le_cost_descend_of_computes {A B : Type*} [Fintype A] [Fintype B]
    {P : Protocol X Y Z} {p : List Bool} {g : X → Y → Z} {gnode : A → B → Z}
    (hcomp : Protocol.Computes P g) (iotaA : A → X) (iotaB : B → Y)
    (hrow : ∀ a : A, RouteRows P p (iotaA a))
    (hcol : ∀ b : B, RouteCols P p (iotaB b))
    (hgame : ∀ a b, gnode a b = g (iotaA a) (iotaB b)) :
    D gnode ≤ (descend P p).cost := by
  have hmem : (descend P p).cost ∈ AchievableCosts gnode := by
    refine ⟨Workspace.UpperBound.Protocol.comap iotaA iotaB (descend P p),
      Workspace.UpperBound.Protocol.comap_cost iotaA iotaB (descend P p), ?_⟩
    intro a b
    rw [Workspace.UpperBound.Protocol.comap_eval,
      eval_descend_of_route (hrow a) (hcol b), hcomp, hgame]
  exact Nat.sInf_le hmem

/-- **Aux R7 (identity instance).**  At the root the comparison is the plain
statement that an alleged protocol bounds the complexity of the game it computes.
This is the round-trip check on §1--§2: the apparatus specialises back to the
definition it generalises.  General. -/
theorem D_le_cost_of_computes [Fintype X] [Fintype Y]
    {P : Protocol X Y Z} {g : X → Y → Z} (hcomp : Protocol.Computes P g) :
    D g ≤ P.cost := by
  have := D_le_cost_descend_of_computes (P := P) (p := []) (gnode := g) hcomp id id
    (fun a => routeRows_nil P a) (fun b => routeCols_nil P b) (fun _ _ => rfl)
  simpa [descend_nil] using this

/-- **`09:943--946` with literal sub-Finsets.**  The special case in which the
node's game is a literal subgame of the ambient game -- the banked `NPCC.subgame`
shape that `TerminalCertificateInputs` states its isolation certificates in.
General. -/
theorem D_subgame_le_cost_descend {P : Protocol X Y Bool} {p : List Bool}
    {g : X → Y → Bool} (hcomp : Protocol.Computes P g) {R : Finset X} {C : Finset Y}
    (hR : ∀ x ∈ R, RouteRows P p x) (hC : ∀ y ∈ C, RouteCols P p y) :
    D (NPCC.subgame g R C) ≤ (descend P p).cost :=
  D_le_cost_descend_of_computes hcomp Subtype.val Subtype.val
    (fun a => hR a.1 a.2) (fun b => hC b.1 b.2) (fun _ _ => rfl)

/-- **Aux R8 (the gated form the isolation blocks consume).**  Every gated
residual binder of the terminal arc -- `TerminalCertificateInputs`'s
`hres : 0 < z -> D (subgame ...) <= (descend Pstar p).cost` is the pattern -- is
this comparison weakened by an irrelevant guard.  Recorded so that a consumption
site never has to re-derive the shape.  General in the guard. -/
theorem gated_D_subgame_le_cost_descend {P : Protocol X Y Bool} {p : List Bool}
    {g : X → Y → Bool} (hcomp : Protocol.Computes P g) {R : Finset X} {C : Finset Y}
    (hR : ∀ x ∈ R, RouteRows P p x) (hC : ∀ y ∈ C, RouteCols P p y) (guard : Prop) :
    guard → D (NPCC.subgame g R C) ≤ (descend P p).cost :=
  fun _ => D_subgame_le_cost_descend hcomp hR hC

end Residual

/-! ## §3  Discharging the banked residual binders (`08:961--979`)

`lem:dense-no-leaf` is stated in `DenseWeightedCount` with four deep inputs in two
gated pairs, of which two are certificates and two are residual readings.  With
§2 the residual half is no longer an input. -/

section Discharge

variable {X Y Coord : Type*}

/-- **`08:972` with its budget side derived.**  The banked `node_not_leaf` with
`hresidual` replaced by the alleged protocol and the node's sections.  General. -/
theorem node_not_leaf_of_alleged_protocol {A B : Type*} [Fintype A] [Fintype B]
    {P : Protocol X Y Bool} {p : List Bool} {g : X → Y → Bool} {gnode : A → B → Bool}
    {bcap : ℕ} (hcomp : Protocol.Computes P g) (iotaA : A → X) (iotaB : B → Y)
    (hrow : ∀ a : A, RouteRows P p (iotaA a))
    (hcol : ∀ b : B, RouteCols P p (iotaB b))
    (hgame : ∀ a b, gnode a b = g (iotaA a) (iotaB b))
    (hbcap : 0 < bcap) (hhard : bcap ≤ D gnode) (z : Bool) :
    descend P p ≠ Protocol.leaf z :=
  node_not_leaf hbcap hhard
    (D_le_cost_descend_of_computes hcomp iotaA iotaB hrow hcol hgame) z

/-- **`lem:dense-no-leaf` (`08:955--959`) from the alleged protocol.**

"Every positive token stops at coordinate isolation or before its first Alice
query, and it does so at suffix depth at most `r`."

The banked `denseNoLeaf` takes six hypotheses; this takes four of them plus one
`Protocol.Computes` and the node-game family's sections.  Its two residual
binders `hnodeResidual` and `hdeepResidual` are **discharged**, at every address
rather than only at the two the banked statement gates -- which is legitimate
precisely because the residual comparison is an unconditional consequence of the
contradiction hypothesis (`09:918--919`), not a fact that holds only at shallow
depth.  The two *certificate* hypotheses keep their frozen gates unchanged: they
are the ones the frozen proof states as two mutually exclusive cases
(`08:962--972` and `08:974--978`), and conjoining them would be exactly the
error the hypothesis-consistency rule forbids.

No banked byte is touched; `DenseWeightedCount.denseNoLeaf` keeps its statement,
its proof term and its pin, and is consumed here by pin.

**Note for the eventual consumer (verify-seat finding R6, `cc-t4o`).**  The
section data `A`, `B`, `iotaA`, `iotaB`, `hrow`, `hcol`, `hgame` is demanded at
**every** address `p : List Bool`, while the frozen proof reads the node game
only at `t.route` and `t.route.take (r + 1)`.  These are strictly stronger
hypotheses, so this theorem is strictly weaker than it needs to be -- sound, and
satisfiable (take `A p` empty away from the two addresses), but the consumer
would be forced to manufacture node games at unreachable addresses.  Narrow the
bundle to the two gated addresses when the terminal assembly consumes it. -/
theorem denseNoLeaf_of_alleged_protocol
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
  denseNoLeaf g t hbcap hbudget hnodeHard
    (fun _ => D_le_cost_descend_of_computes hcomp (iotaA t.route) (iotaB t.route)
      (hrow t.route) (hcol t.route) (hgame t.route))
    hdeepHard
    (fun _ => D_le_cost_descend_of_computes hcomp (iotaA (t.route.take (r + 1)))
      (iotaB (t.route.take (r + 1))) (hrow (t.route.take (r + 1)))
      (hcol (t.route.take (r + 1))) (hgame (t.route.take (r + 1))))

end Discharge

/-! ## §4  Statement poles for §1--§3

A green build sees neither of these. -/

/-- **Statement pole 1 (the rectangle hypotheses are load-bearing).**  Without
them the residual comparison is false, so `D_le_cost_descend_of_computes` is not
a repackaging of `cost_descend_le`.

The witness is Bob's one-bit game `g x y = y` on `Bool x Bool`, its optimal
protocol `bNode id (leaf false) (leaf true)`, and the address `[true]`.  The
residual subtree is a leaf, of cost `0`, while the ambient game has complexity
`1`.  The gap is closed exactly by `RouteCols`, which at this address forces
`y = true`.

Self-chosen values are legitimate here and only here: this is a rejection probe
claiming **no** legality at any paper parameter, in the sense of the
defined-vs-free witness rule. -/
theorem residual_needs_the_rectangle :
    ¬ D (fun _ y : Bool => y) ≤
        (descend (Protocol.bNode (fun y : Bool => y)
          (Protocol.leaf false) (Protocol.leaf true) : Protocol Bool Bool Bool)
          [true]).cost := by
  have hleaf : descend (Protocol.bNode (fun y : Bool => y)
      (Protocol.leaf false) (Protocol.leaf true) : Protocol Bool Bool Bool) [true]
      = Protocol.leaf true := by
    simp [descend, descendStep]
  have hach : (AchievableCosts (fun _ y : Bool => y)).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty _
  have hone : 1 ≤ D (fun _ y : Bool => y) :=
    one_le_D_of_ne (a₁ := true) (b₁ := true) (a₂ := true) (b₂ := false) (by simp) hach
  rw [hleaf]
  simp only [Protocol.cost]
  omega

/-! ### The hypothesis-consistency witness for §2

**On canonical inhabitation.**  The object §1--§3 quantify over is the frozen
proof's *alleged* protocol, introduced at `09:918--919` and `09:1037--1039` by
"suppose for contradiction".  The paper therefore never constructs an instance --
it derives a contradiction from the assumption that one exists -- so there is no
paper instance to exhibit, and this is scaffolding in the precise sense: a
predicate on a hypothetical object.  What must nonetheless be checked, and is
checked here, is that the hypothesis bundle of `D_le_cost_descend_of_computes`
is **consistent and nondegenerate**: it is met by a genuine two-sided protocol at
a genuine two-sided address, with a nonconstant node game, and the bound is
**attained**.  A bundle met only where the conclusion is vacuous would prove
nothing. -/

/-- The consistency witness's ambient game: Bob's parity game on `Bool x Bool`. -/
def probeGame : Bool → Bool → Bool := fun x y => xor x y

/-- The consistency witness's protocol: Bob speaks, then Alice.  It computes
`probeGame` and has cost `2`, so it is a genuine two-sided protocol and not a
degenerate one-player tree. -/
def probeProtocol : Protocol Bool Bool Bool :=
  Protocol.bNode (fun y => y)
    (Protocol.aNode (fun x => x) (Protocol.leaf false) (Protocol.leaf true))
    (Protocol.aNode (fun x => x) (Protocol.leaf true) (Protocol.leaf false))

/-- The node game at the address `[false]`: the ambient game read through the
inclusion of the rectangle `Bool x {false}`, which is the `09:943--946` shape
with `iotaA = id` and `iotaB` the constant column section. -/
def probeNodeGame : Bool → Unit → Bool := fun a _ => probeGame a false

/-- **Aux R9 (hypothesis consistency, and the bound is attained).**

Every hypothesis of `D_le_cost_descend_of_computes` holds at this witness, at
values that are nondegenerate in every direction that matters: the protocol is
two-sided, the address passes through a real Bob query, the surviving rectangle
is a proper subrectangle (`RouteCols` forces `y = false`), and the node game is
**nonconstant**, so its complexity is `1` rather than `0`.  The residual cost is
also `1`, so the deliverable is **tight** here -- the comparison is not slack
arithmetic that any protocol would satisfy.

Self-chosen carriers are legitimate here for the same reason as in the poles:
this instance claims no legality at any paper parameter and audits our encoding
only.  It is **BEYOND-PAPER**, and it is not a substitute for a paper instance;
there is none to be had, for the reason given above. -/
theorem residual_comparison_hypotheses_consistent :
    Protocol.Computes probeProtocol probeGame
      ∧ (∀ a : Bool, RouteRows probeProtocol [false] a)
      ∧ (∀ _ : Unit, RouteCols probeProtocol [false] false)
      ∧ (descend probeProtocol [false]).cost = 1
      ∧ D probeNodeGame = 1 := by
  have hcomp : Protocol.Computes probeProtocol probeGame := by
    intro x y
    cases x <;> cases y <;> rfl
  have hrow : ∀ a : Bool, RouteRows probeProtocol [false] a := by
    intro a; exact ⟨trivial, trivial⟩
  have hcol : ∀ _ : Unit, RouteCols probeProtocol [false] false := by
    intro _; exact ⟨rfl, trivial⟩
  have hcost : (descend probeProtocol [false]).cost = 1 := by
    simp [descend, descendStep, probeProtocol, Protocol.cost]
  refine ⟨hcomp, hrow, hcol, hcost, le_antisymm ?_ ?_⟩
  · have hle := D_le_cost_descend_of_computes (P := probeProtocol) (p := [false])
      (gnode := probeNodeGame) hcomp id (fun _ => false) hrow hcol (fun _ _ => rfl)
    rwa [hcost] at hle
  · have hach : (AchievableCosts probeNodeGame).Nonempty :=
      Workspace.UpperBound.AchievableCosts_nonempty _
    exact one_le_D_of_ne (a₁ := true) (b₁ := ()) (a₂ := false) (b₂ := ())
      (by decide) hach

/-- **Statement pole 2 (the alleged protocol is load-bearing).**  The comparison
is not a statement about `descend` alone: for a protocol that computes something
else, the residual subtree of a node says nothing about `g`.  The same witness
with the *constant* protocol `leaf false`, which does not compute `g`, has
residual cost `0` at the empty address while `D g = 1`. -/
theorem residual_needs_the_computes :
    ¬ Protocol.Computes (Protocol.leaf false : Protocol Bool Bool Bool)
        (fun _ y : Bool => y) := by
  intro h
  have := h true true
  simp [Protocol.eval] at this

/-! ## §5  The `hpresOrd`/`hpresFor` census (`09:512--516`, `09:518--527`,
`09:804--816`, `09:1085--1086`)

See the module docstring for the full census.  The mathematics is three
declarations: one definition reifying `09:804--810`, one theorem discharging
`hpresOrd`, and one countermodel refuting `hpresFor`'s carrier. -/

section Census

variable {Rw Om Cone : Type*} [DecidableEq Rw] [DecidableEq Cone]

/-- **`09:804--810`, the frozen construction of `K_ord`.**

"Before fixing the two bins, **forgetting the raw-column prefix** gives the
ordinary Stage-3 restriction `<interlace(S_2,s), union_p {p} x R_p, K_ord>`."

A raw column is `c = (xi, j)` with `j : [s] -> J_2` (`09:512--514`), forgetting
the prefix is `c |-> j`, and `j` is the tuple `fun p => rho_p(c)` because
`rho_p(c) = j(p)` (`09:515`).  So the carrier is the image of a row stream under
`x |-> (fun p => rho p (omg x))`.

**One definition serves both streams**, exactly as the frozen `E_.` display and
the banked `streamImage` do: substituting `(iOrd, RG)` gives clause (iv)'s
`K_ord`, and substituting `(iFor, Rfor)` gives the foreign Stage-3 carrier the
frozen clause (iv) does not name (see the census).  No complexity or density
conclusion is a component of it: `M1--M10`. -/
def stage3Cols {q s q₂ : ℕ} (omg : Rw → Om) (rho : Slot s → Om → Slot q₂ × Cone)
    (XZ : Finset (Slot q × Rw)) (i : Slot q) (R : Finset Rw) :
    Finset (Slot s → Slot q₂ × Cone) :=
  (TwoStreamState.streamRows XZ i R).image (fun x p => rho p (omg x.2))

/-- **Aux C1, the census's derivation (`hpresOrd`, outcome (1)).**  Reading the
Stage-3 column carrier of a stream at a bin returns that stream's image at that
bin.  This is `09:515`'s `rho_p(c) = j(p)` composed with `09:804--810`'s
construction, and the proof is `Finset.image_image` and nothing else.  General in
the carriers, the three widths, the stream data **and the bin** -- in particular
it is not special to `p_o`. -/
theorem binImage_stage3Cols {q s q₂ : ℕ} (omg : Rw → Om)
    (rho : Slot s → Om → Slot q₂ × Cone) (XZ : Finset (Slot q × Rw)) (i : Slot q)
    (R : Finset Rw) (p : Slot s) :
    TerminalCertificateInputs.binImage (stage3Cols omg rho XZ i R) p
      = TwoStreamState.streamImage omg rho p XZ i R := by
  simp [TerminalCertificateInputs.binImage, stage3Cols, TwoStreamState.streamImage,
    Finset.image_image, Function.comp_def]

end Census

section CensusOnStates

variable {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl]
  [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]
variable {q s q₂ mT dT : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
  {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
  {RG RSig RD : Finset Rw} {omg : Rw → Om}
  {rho : Slot s → Om → Slot q₂ × Cone} {YT : Slot s → Finset Cl}
  {zeta : Slot s → Cl → Ltwo} {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
  {lamT eps2 xT ε δ' : ℝ}

/-- **`hpresOrd` DERIVED (census outcome (1)).**

The binder `TerminalCertificateInputs` introduces "because the frozen text
displays no equation for it" is a theorem once the one frozen equation the
banked record omits -- `09:804--810`'s construction of `K_ord` -- is supplied.
General in the state. -/
theorem hpresOrd_of_kordDef
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hKord : st.Kord = stage3Cols omg rho XZ st.iOrd RG) :
    TerminalCertificateInputs.binImage st.Kord st.pOrd
      = TwoStreamState.streamImage omg rho st.pOrd XZ st.iOrd RG := by
  rw [hKord, binImage_stage3Cols]

/-- **The corrected foreign identification (the repair `hpresFor` needs).**  At
the **foreign** stream's Stage-3 carrier the foreign identification is a theorem,
by the same one-formula lemma.  No binder, no state hypothesis, no new frozen
input.  General. -/
theorem foreign_bin_of_foreign_carrier
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ') :
    TerminalCertificateInputs.binImage (stage3Cols omg rho XZ st.iFor st.Rfor) st.pFor
      = TwoStreamState.streamImage omg rho st.pFor XZ st.iFor st.Rfor :=
  binImage_stage3Cols omg rho XZ st.iFor st.Rfor st.pFor

/-- **`09:1076--1078` with both carriers correct.**

"Until the first Bob query, these Alice restrictions do not change the ordinary
and foreign fibre sets `O_alpha, F_alpha`, so the averages
`eq:terminal-averages` are unchanged."

This supersedes
`TerminalCertificateInputs.terminal_averages_unchanged_until_first_bob` at the
consumption site.  Two changes, both recorded in the census:

* the **ordinary** identification is no longer a binder: it is derived from the
  single frozen equation `hKord` (`09:804--810`), which is the equation the
  banked record omits;
* the **foreign** half is stated about the foreign stream's own carrier, not
  about a bin of the ordinary carrier `K_ord`.  `09:804--805` and `09:1085--1086`
  both call `K_ord` the *ordinary* set, and
  `ordinary_carrier_has_no_foreign_bin` shows the substitution is not merely
  unlicensed but false.

The invariance itself is the banked
`TerminalCertificateInputs.fibres_unchanged_until_first_bob`, which is general in
the carrier and is therefore applied twice, once per stream, without restating
it.  General in the state, the protocol and the Alice-only address. -/
theorem terminal_averages_unchanged_of_carriers {Xr Zo : Type*}
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo) {route : List Bool}
    (h : RoutedCertificateSystem.IsAlicePath P₃ route)
    (hKord : st.Kord = stage3Cols omg rho XZ st.iOrd RG) :
    (∀ α : Slot q₂, TerminalCertificateInputs.fibreAt P₃ st.Kord route st.pOrd α
        = TwoStreamState.colFibre
            (TwoStreamState.streamImage omg rho st.pOrd XZ st.iOrd RG) α)
      ∧ 1 - ε ≤ TwoStreamState.meanFibreDensity
          (TerminalCertificateInputs.binImage
            (TerminalCertificateInputs.kordAt P₃ st.Kord route) st.pOrd)
      ∧ (∀ α : Slot q₂,
          TerminalCertificateInputs.fibreAt P₃
              (stage3Cols omg rho XZ st.iFor st.Rfor) route st.pFor α
            = TwoStreamState.colFibre
                (TwoStreamState.streamImage omg rho st.pFor XZ st.iFor st.Rfor) α)
      ∧ δ' ≤ TwoStreamState.meanFibreDensity
          (TerminalCertificateInputs.binImage
            (TerminalCertificateInputs.kordAt P₃
              (stage3Cols omg rho XZ st.iFor st.Rfor) route) st.pFor) := by
  obtain ⟨-, hfibO, hmeanO⟩ :=
    TerminalCertificateInputs.fibres_unchanged_until_first_bob (P₃ := P₃) st.Kord h
  obtain ⟨-, hfibF, hmeanF⟩ :=
    TerminalCertificateInputs.fibres_unchanged_until_first_bob (P₃ := P₃)
      (stage3Cols omg rho XZ st.iFor st.Rfor) h
  have hOrd := hpresOrd_of_kordDef st hKord
  have hFor := foreign_bin_of_foreign_carrier st
  refine ⟨fun α => ?_, ?_, fun α => ?_, ?_⟩
  · rw [hfibO st.pOrd α, hOrd]
  · rw [hmeanO st.pOrd, hOrd]
    exact st.ordinary_density
  · rw [hfibF st.pFor α, hFor]
  · rw [hmeanF st.pFor, hFor]
    exact st.foreign_density

/-- **Aux C2 (the proposed record field does not fight the banked ones).**

The census's repair is one new `TwoStreamState` field,
`Kord_def : Kord = stage3Cols omg rho XZ iOrd RG`.  This readout is the
machine-checked statement that the field is *compatible* with the two banked
fields that already constrain `Kord` on the ordinary side: with `Kord_def` in
force, `selCol` still lands in the ordinary row stream (`selCol_mem`,
`09:507--509`), and the density field `Kord_density` (`09:621--622`) is
untouched.  Nothing here proves the field; it records that assuming it leaves the
banked constraints exactly where they were, which is what a structural repair
tranche will need.  General in the state. -/
theorem kordDef_is_consistent_with_the_banked_fields
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hKord : st.Kord = stage3Cols omg rho XZ st.iOrd RG) :
    (∀ k ∈ stage3Cols omg rho XZ st.iOrd RG,
        st.selCol k ∈ TwoStreamState.streamRows XZ st.iOrd RG)
      ∧ 1 - ε ≤ ((stage3Cols omg rho XZ st.iOrd RG).card : ℝ)
          / (Fintype.card (Slot q₂ × Cone) : ℝ) ^ s := by
  constructor
  · intro k hk
    exact st.selCol_mem k (by rw [hKord]; exact hk)
  · have := st.Kord_density
    rwa [hKord] at this

end CensusOnStates

/-! ## §6  The countermodel behind the `hpresFor` finding

A green build sees this one too. -/

/-- Probe carriers for the countermodel: two outer coordinates, two Stage-3 bins,
one Stage-2 coordinate, and a two-element reservoir alphabet.  These are
**BEYOND-PAPER** values: the probe claims no legality at any parameter the paper
visits, and exists only to refute an identification. -/
abbrev ProbeRw : Type := Bool

/-- The probe's row rectangle: one ordinary row at outer coordinate `0` and one
foreign row at outer coordinate `1`.  Both streams are nonempty, so the
countermodel is not an artifact of an empty carrier. -/
def probeXZ : Finset (Slot 2 × ProbeRw) := {(0, false), (1, true)}

/-- The probe's forgetful map, the identity. -/
def probeOmg : ProbeRw → Bool := id

/-- The probe's bin readout: every bin reads the reservoir label into the single
Stage-2 coordinate.  This is the simplest map for which the two streams disagree,
which is the point. -/
def probeRho : Slot 2 → Bool → Slot 1 × Bool := fun _ o => (0, o)

/-- **The countermodel refuting `hpresFor`'s carrier (census outcome for the
foreign half).**

At nondegenerate data -- distinct outer coordinates `0 != 1` (`09:501`'s
`outer_distinct`), distinct bins `0 != 1`, and both row streams nonempty -- the
`p_f`-bin readout of the **ordinary** Stage-3 carrier is not the **foreign**
stream image.  So `hpresFor` is not an under-recorded consequence of the frozen
displays: it is **not derivable, and false at general data**.

This probe's data is raw and is **not** a `TwoStreamState`, so it settles
non-derivability, not illegality at every legal state; and the frozen text
explicitly declines the disjointness shortcut at `09:534--537` ("There is no
requirement that the underlying subsets `O_alpha, F_alpha` be disjoint"), so
disjoint physical row sets are not by themselves a reason for the readouts to
differ.  The finding rests on the naming evidence in the module docstring:
`09:805` and `09:1085--1086` call `K_ord` the *ordinary* carrier, while `E_f` is
built from the foreign stream at `09:508` and `09:523--525`.

The corrected statement is `foreign_bin_of_foreign_carrier`, and the finding is
parked for Simon in the module docstring.  The paper is not patched. -/
theorem ordinary_carrier_has_no_foreign_bin :
    TerminalCertificateInputs.binImage
        (stage3Cols probeOmg probeRho probeXZ (0 : Slot 2) {false}) (1 : Slot 2)
      ≠ TwoStreamState.streamImage probeOmg probeRho (1 : Slot 2) probeXZ
          (1 : Slot 2) {true} := by
  rw [binImage_stage3Cols]
  intro h
  have hmem : ((0 : Slot 1), true) ∈
      TwoStreamState.streamImage probeOmg probeRho (1 : Slot 2) probeXZ
        (1 : Slot 2) {true} := by
    decide
  rw [← h] at hmem
  revert hmem
  decide

/-- **Aux C3 (the countermodel is nondegenerate).**  Both probe streams are
nonempty and the two probe outer coordinates are distinct, so the previous
theorem is a genuine disagreement and not a vacuous one.  General only in the
sense that it is the probe's own readout. -/
theorem probe_is_nondegenerate :
    (TwoStreamState.streamRows probeXZ (0 : Slot 2) {false}).Nonempty
      ∧ (TwoStreamState.streamRows probeXZ (1 : Slot 2) {true}).Nonempty
      ∧ (0 : Slot 2) ≠ (1 : Slot 2) := by
  refine ⟨?_, ?_, by decide⟩
  · exact ⟨(0, false), by decide⟩
  · exact ⟨(1, true), by decide⟩

end EthInapproximability.ParameterizedNP.TerminalResidualComparison
