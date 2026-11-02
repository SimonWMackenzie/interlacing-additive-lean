import EthInapproximability.ParameterizedNP.WrapperMassRedistribution

/-!
# Parameterized NP route: the routed certificate system on the alleged protocol

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8a54aaa6f0e60eaeb31ac1719cd696b169d5a845381fbd810a18a86c6b2a24e5`),
  the **protocol-object layer** of the per-member shallow-protocol refutation
  engine that runs from `09:1188` (the contradiction frame) to `09:1781` (the
  terminal Extension call).  This module is the first tranche of the standing
  **GAP-EXPOSED item M1** of `WRAPPER-MASS-REDISTRIBUTION-001`, recorded verbatim
  there as "M1, the protocol and its routed certificate system (no protocol
  object, no Bob query, no owner rectangle, no per-node column projection)", and
  as GAP-EXPOSED item 2 of `DENSE-WRAPPER-FRONTIER-001` ("The protocol side is
  not modelled").
* **The exact frozen lines traced here**, in print order:
  * `09:1188--1193`, the contradiction frame: "Fix an arbitrary retained matrix
    `U' in [U]_{1, 1-delta_U, theta}` and suppose for contradiction that a
    protocol `P` of cost at most `C+r-1` computes `U'`."  The protocol is the
    vendored `Workspace.Types.Protocol.Protocol`; the cost bound is
    `Protocol.cost P <= C + r - 1`, carried as an explicit hypothesis at every
    use site and never as structure data.
  * `09:1195--1213`, `lem:wrapper-no-bob-completion`: "every root-to-leaf path
    containing no Bob query contains at least `r` Alice queries".  Its arithmetic
    is banked (`DenseWrapperFrontier.wrapperNoBobCompletion`); what this module
    adds is the *protocol-side* predicate the completed protocol satisfies, and a
    protocol that satisfies it (`aliceLadder_noBob_depth`).
  * `09:1250--1252`, the two frozen stopping rules: "Stop each routed branch at
    its first Bob query, or after `r` Alice queries.  A Bob query that occurs
    only after all `r` Alice queries is not exposed; its state is a final Alice
    frontier node."  These become the two *addresses*
    `IsFirstBobNode` and `IsFinalAliceNode`, defined on routes of the vendored
    protocol, whose depth clauses are exactly `09:1251--1252`.
  * `09:1253--1256`, "let `d_v` be the number of preceding Alice queries and set
    `kappa_v = 2^{r-d_v}`" -- the depth is the route length, and `kappa_v` is the
    banked `DenseWeightedCount.stoppingCapacity`, consumed by pin.
  * `09:1259`, "Every first-Bob node has `kappa_v >= 2`.  Prefix-freeness ...".
  * `09:1236`, `09:1238--1248`, the certificate: "At remaining selector capacity
    `2^k`, a certificate consists of at least `A_k` reference rows in one outer
    coordinate", "Start one clean reference certificate in every coordinate
    outside `E_0`, each with weight one", and the clean/low kinds.  `A_k` is the
    banked `DenseWrapperFrontier.refRowFloor`; the kinds are the banked
    `DenseWrapperFrontier.CertKind`.
  * `09:1278--1280`, "at a fixed node there is at most one descendant of each
    initial outer coordinate" -- the field `coordUnique`.
  * `09:1287--1290` and `09:1327--1331`, the **per-node column projection**:
    "Every represented coordinate is outside `E_0`, so the parent projection to
    any selected `u_{kappa_v}` of them has density at least `rho = 2y^2`.  The
    denser Bob child retains density at least `y^2`", and at a final node "no Bob
    query has occurred on the route to this node.  Its two-coordinate column
    projection consequently still has density at least `rho = 2y^2`".  Both are
    *derived* here from the definition of the node's column set, not assumed.
  * `09:1346--1350`, "Thus every final Alice node contains either one clean
    certificate, one half-weight descendant of a split certificate, or none", and
    `09:1548--1552`, "Every clean reference certificate has a unique final node,
    its *owner*.  Distinct clean donors have distinct owners because a final node
    contains at most one clean certificate."
  * `09:1341--1343`, the suffix budget: "the suffix below a node reached after
    `r` Alice bits in the alleged `(C+r-1)`-bit protocol has depth at most
    `C-1`", which this module proves *of the protocol object* rather than
    assuming.
* **Cross-anchors opened first-hand for this tranche:** `09:1315--1344`
  (`lem:final-reference-uniqueness`), `09:1367--1384` (the protected constants
  the successor rounds consume), `09:1512--1517` (the no-omitted-early-leaf
  fact), `09:1611--1615`, `09:1620--1631`, `09:1700--1713`, `09:1746--1781`;
  `sections/08-dense-stage4.tex` `08:981` (prefix-freeness), `08:1115`
  (`kappa_v`); `sections/A-certified-stopping.tex` `A:148--162`
  (`lem:certified-row-ladder`).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the import is
  `WrapperMassRedistribution`, whose own ledger row records the same exclusion.
* **Proof status.**  Every declaration is either a transcription of a frozen
  display of the range above, a general property of one of those
  transcriptions, or one of the block's own protocol-side derivations carried
  out in the kernel.  **No mathematics is added**, and no conclusion of
  `eq:wrapper-u-dense` is asserted anywhere.
* **What was a hypothesis and is now a theorem.**  Three frozen sentences that
  the banked abstract modules carried as named binders for want of a protocol
  object are *proved* here: "no Bob query has occurred on the route to this node"
  (`bobCols_of_isAlicePath`, `retainedCols_of_isAlicePath`,
  `nodeProjection_of_isAlicePath`); "the denser Bob child" (`card_bobCols_children_add`,
  `exists_denser_bob_child`); and the suffix budget of `09:1341--1343`
  (`finalNode_residual_budget`, `firstBob_residual_budget`), which the banked
  `finalNode_budget_contradiction` and `firstBob_budget_contradiction` previously
  received as the unexamined `hbudget`.
* **Aux-lemma battery and poles.**  Every new type carries general identity,
  composition, monotonicity and round-trip properties (`isAlicePath_take`,
  `isAlicePath_append`, `bobCols_children_union`, `bobCols_children_disjoint`,
  `retainedCols_subset`, `RoutedCertificate.capacity_mul_initial_le_rows`,
  `RoutedSystem.node_injective`, `tupleRoute_injective`, ...), all proved.  Three
  statement poles show the load-bearing hypotheses really bite:
  `bobCols_pole_at_bob_query`, `bobCols_children_add_pole_at_alice` and
  `denserChild_needs_the_right_bit`.  `ladderSystem_owner_injOn` is the
  hypothesis-consistency instance for `owner_injOn_of_ladder`.

## Predecessor modules consumed **by pin**, never restated

* `Workspace.Types.Protocol` (through `LegacyNPCC.Core`, project-axiom-free):
  `Protocol`, `Protocol.cost`, `Protocol.eval`.  This is the vendored protocol
  object the frozen frame quantifies over; no protocol type is defined here.
* `EthInapproximability.ParameterizedNP.DenseWeightedCount`: `descendStep`,
  `descend`, `IsQueryNode`, `IsBobNode`, `IsQueryPath`, `IsBobPath`,
  `cost_descend_add_length_le`, `isQueryPath_take`, `stoppingCapacity`,
  `one_le_stoppingCapacity`, `PrefixFreeFrontier`,
  `prefixFreeFrontier_injective`.
* `EthInapproximability.ParameterizedNP.DenseSynchronisation`: `IsANode`.
* `EthInapproximability.ParameterizedNP.DenseWrapperFrontier`: `refRowFloor`
  (the frozen `A_k = 2^k A_0`), `CertKind` with `CertKind.weight`,
  `WrapperFrontier` (the abstract frontier record this module *realizes*),
  `firstBob_budget_contradiction`, `finalNode_budget_contradiction`,
  `wrapperFinalReferenceUniqueness`.
* `EthInapproximability.ParameterizedNP.WrapperProjectionCovers`: `projSet`, the
  banked column projection whose *node-indexed* instance is built here.
* `EthInapproximability.ParameterizedNP.WrapperMassRedistribution`:
  `owner_injOn_of_unique_clean` (`09:1550--1552`), consumed at the owner map
  this module defines.

## GAP-EXPOSED (named ranges, with the next-round prescription)

This tranche lands the protocol object, the Bob query, the per-node column
projection and the owner rectangle.  It does **not** land the rest of M1, and
records the remainder as named ranges rather than papering over them.

1. **The routing dynamics are not modelled** (`09:1238--1248`).  Which reference
   *rows* land in which Alice child, hence the clean/low transition of an
   individual certificate across a query, is not declared: `RoutedCertificate`
   carries a row count meeting the frozen floor `A_k`, not a row set.  The
   consequence is that `eq:wrapper-frontier-conservation`'s first clause
   (`sum_v W_v >= q - e_0`) stays the binder it already is in
   `DenseWrapperFrontier.wrapperCleanCount`.  *Next round:* carry
   `rowsAt : List Bool -> Finset Row` with the frozen halving law
   `refRowFloor_ceil_half` (already banked) as the transition, and derive the
   kind transition from it.
2. **`lem:early-protected-closure` is not transcribed** (`09:1417--1531`).  The
   dyadic donor classes, the poor-`u`-set cover call and call (iii) of
   `sec:extension-call-ledger` are not declared here; the block's arithmetic is
   banked in `WrapperProtectedEarly`, and only its protocol-side *frame* (a
   first-Bob node with `kappa_v >= 2` and a residual child budget) is landed.
3. **The counting spine through the four-category loss table is not re-sited on
   the protocol object** (`09:1566--1615`).  `WrapperMassRedistribution` proves
   `eq:wrapper-mass-leaves-owner` over abstract reals; attaching those four
   categories to *this* module's owner rectangle needs item 1 first.
4. **The owner-threshold system and the terminal two-stream substitution are not
   re-sited** (`09:1617--1699`).  `TERMINAL-TWO-STREAM-001` is a *stated, not
   proved* claim, and M2 of `WRAPPER-MASS-REDISTRIBUTION-001` records a binder
   shape mismatch at `lem:terminal-state-realization` that this module does not
   repair: `epsilon_i` and `delta_i` there are a normalized baseline deficit and
   a threshold, while the banked realization takes ratios of physical row counts
   at a realized rectangle.  **No declaration below mentions
   `TerminalTwoStream.TerminalTwoStream` or any of its conclusions.**
5. **The pigeonhole at `T_*` and the terminal Extension call (iv) are not
   re-sited** (`09:1700--1713`, `09:1746--1781`).  `WrapperMassRedistribution`
   owns them as arithmetic (`deltaZero_of_pigeonhole`, `ExtensionCallFour`); the
   protocol-side statement "`T_*` is an exceptional *final node of this
   frontier*" needs items 1 and 3.
6. **`hDenseRung` is neither discharged nor fed further.**  `eq:wrapper-u-dense`
   is asserted nowhere below, and **no route completion is claimed.**
7. **The *projection* form of the denser-child halving is not landed**
   (`09:1287--1290`).  What is proved below is the halving of the node's
   **column set** (`bobCols_children_union`, `bobCols_children_disjoint`,
   `card_bobCols_children_add`, `exists_denser_bob_child`); the frozen sentence
   "the parent projection to any selected `u_{kappa_v}` of them has density at
   least `rho=2y^2`.  The denser Bob child retains density at least `y^2`" is
   about the *projection* `projSet J` of that set, and `nodeProjection` carries
   only its Alice-path invariance.  **No downstream consumer may cite
   `exists_denser_bob_child` as discharging `09:1287--1290`.**  *Next round:*
   land `card_projSet_children_le`, `|projSet J (A union B)| <= |projSet J A| +
   |projSet J B|`, applied to `bobCols_children_union`.
8. **`owner_injOn_of_ladder`'s ladder binder is not yet exercised at a live
   pair.**  `ladderSystem_owner_injOn` shows the hypothesis bundle is
   non-contradictory, but at `ladderSystem` the owner map is the identity, so no
   pair with `owner i = owner j` and `coord i /= coord j` exists and `hladder`
   is discharged vacuously.  *Next round:* a probe with `iota` strictly larger
   than `V` -- two certificates placed at one final node with distinct `coord`
   -- so that `hladder` fires and the budget contradiction is the operative
   step.

### Successor record (comment-only; nothing above is restated or weakened)

The numbered list above is the banked judged opening of this module and is left
exactly as it was written.  For navigation only, the successor tranches have
since closed part of it:

* Items **1**, **7** and **8** are discharged by
  `EthInapproximability.ParameterizedNP.RoutingDynamics` (tranche `cc-t4d`), each
  along the prescription recorded above.
* Items **2**, **3**, **4**, **5** and **6** remain open, unchanged.  In
  particular `hDenseRung` is neither discharged nor fed and `eq:wrapper-u-dense`
  is asserted nowhere.
* The **deferred canonical-inhabitation obligation** registered below for
  `RoutedSystem` -- narrowed by `RoutingDynamics` to the simultaneous indexing of
  all initial coordinates by one `V` -- is discharged by
  `EthInapproximability.ParameterizedNP.FrontierIndexing` (tranche `cc-t4e`),
  whose `canonicalSystem` is a `RoutedSystem` on the paper's own inputs.
  `ladderSystem` and `earlySystem` below keep their **NON-FIDELITY** labels and
  are still not the paper's instance.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for
this tranche.  The strings "first-Bob", "routed certificate", "clean
certificate", "owner rectangle", "column projection" and "frontier node" occur
**nowhere** in the reader artifact.  Its only account of this block is
unnumbered prose inside the proof of `thm:paper-adapted-stage4-interface` at
`A-stage4-details.tex:370--399`; line `371--373` is already recorded as
unclaimed prose by `WRAPPER-PROJECTION-COVERS-001`, lines `390--391` are already
assigned to `TERMINAL-TWO-STREAM-001`, and the one numbered display in range,
`A-stage4-details.tex:394`, is `eq:wrapper-u-dense` itself, which this module
does not close.  **No reader item is claimed**, and the absence is a finding
about the reader artifact rather than an omission here.

## Canonical inhabitation

The frozen frame quantifies over an *arbitrary* alleged protocol `P`; the paper
therefore exhibits no single protocol object, and the canonical instance of
`RoutedCertificateSystem` is "the routing of the paper's completed protocol",
which needs the routing dynamics of GAP-EXPOSED item 1.  **That obligation is
registered as deferred, not silently satisfied.**  What is landed instead are
two *frame-legal* inhabitants -- protocols proved to satisfy the frozen frame
conditions of `09:1188--1213` (the cost bound and the conclusion of
`lem:wrapper-no-bob-completion`) -- one all-final (`ladderSystem`, the frozen
`e_0 = 0` shape) and one all-first-Bob (`earlySystem`), so that neither branch of
`firstBob` is inhabited only vacuously.  Neither is claimed to compute `U'`;
computing `U'` is a hypothesis of the frozen contradiction, never constructor
data.
-/

namespace EthInapproximability.ParameterizedNP.RoutedCertificateSystem

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution

/-! ## §1  Alice-only routes (`09:1250--1252`)

"Stop each routed branch at its first Bob query, or after `r` Alice queries."  A
route that has not yet stopped therefore passes through Alice queries only; this
is the exact dual of the banked `IsBobPath` of `08:952--953`, and it is what the
frozen proof means at `09:1330` by "no Bob query has occurred on the route to
this node". -/

section AliceRoutes

variable {X Y Z : Type*}

/-- **`09:1250--1251`.**  Every node strictly along `p` is an Alice query.  The
node `p` itself reaches is unconstrained: it is where the branch stops.  Exact
dual of the banked `DenseWeightedCount.IsBobPath`. -/
def IsAlicePath : Protocol X Y Z → List Bool → Prop
  | _, [] => True
  | P, b :: p => IsANode P ∧ IsAlicePath (descendStep P b) p

/-- **Aux A1.**  The empty route is an Alice route.  General. -/
@[simp] theorem isAlicePath_nil (P : Protocol X Y Z) : IsAlicePath P [] := trivial

/-- **Aux A2.**  The defining step of an Alice route.  General. -/
theorem isAlicePath_cons {P : Protocol X Y Z} {b : Bool} {p : List Bool} :
    IsAlicePath P (b :: p) ↔ IsANode P ∧ IsAlicePath (descendStep P b) p := Iff.rfl

/-- **Aux A3.**  An Alice query is a query.  General. -/
theorem isQueryNode_of_isANode {P : Protocol X Y Z} (h : IsANode P) : IsQueryNode P := by
  obtain ⟨a, l, r, rfl⟩ := h
  trivial

/-- **Aux A4 (the two players' nodes are exclusive).**  An Alice query is not a
Bob query -- the frozen stopping rule would otherwise be ambiguous.  General. -/
theorem not_isBobNode_of_isANode {P : Protocol X Y Z} (h : IsANode P) : ¬ IsBobNode P := by
  obtain ⟨a, l, r, rfl⟩ := h
  simp [IsBobNode]

/-- **Aux A5.**  An Alice-only route is a query route, so the banked budget
accounting applies to it verbatim.  General. -/
theorem isQueryPath_of_isAlicePath : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsAlicePath P p → IsQueryPath P p := by
  intro P p
  induction p generalizing P with
  | nil => intro _; trivial
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩
      exact ⟨isQueryNode_of_isANode hnode, ih hrest⟩

/-- **Aux A6 (prefix closure).**  Every prefix of an Alice route is an Alice
route.  General. -/
theorem isAlicePath_take : ∀ (n : ℕ) {P : Protocol X Y Z} {p : List Bool},
    IsAlicePath P p → IsAlicePath P (p.take n) := by
  intro n
  induction n with
  | zero => intro P p _; simp only [List.take_zero]; trivial
  | succ n ih =>
      intro P p h
      cases p with
      | nil => simp
      | cons b p =>
          obtain ⟨hnode, hrest⟩ := h
          exact ⟨hnode, ih hrest⟩

/-- **Aux A7 (composition).**  An Alice route splits at any point into an Alice
route and an Alice route below it.  General. -/
theorem isAlicePath_append : ∀ {P : Protocol X Y Z} {p q : List Bool},
    IsAlicePath P p → IsAlicePath (descend P p) q → IsAlicePath P (p ++ q) := by
  intro P p
  induction p generalizing P with
  | nil => intro q _ hq; simpa using hq
  | cons b p ih =>
      rintro q ⟨hnode, hrest⟩ hq
      exact ⟨hnode, ih hrest (by simpa [descend_cons] using hq)⟩

/-- **`09:1341--1343`, the suffix budget, on the protocol object.**  "the suffix
below a node reached after `r` Alice bits in the alleged `(C+r-1)`-bit protocol
has depth at most `C-1`".  A node reached by an Alice route of length `d` keeps
at most `cost(P) - d` further bits.  Consumed from the banked
`cost_descend_add_length_le` at the Alice-route specialization. -/
theorem cost_descend_add_length_le_of_isAlicePath {P : Protocol X Y Z} {p : List Bool}
    (h : IsAlicePath P p) : (descend P p).cost + p.length ≤ P.cost :=
  cost_descend_add_length_le (isQueryPath_of_isAlicePath h)

/-- **Aux A8.**  In particular no Alice route is longer than the budget.
General. -/
theorem length_le_cost_of_isAlicePath {P : Protocol X Y Z} {p : List Bool}
    (h : IsAlicePath P p) : p.length ≤ P.cost := by
  have := cost_descend_add_length_le_of_isAlicePath h
  omega

end AliceRoutes

/-! ## §2  The two frozen frontier addresses (`09:1250--1259`)

"Stop each routed branch at its first Bob query, or after `r` Alice queries.  A
Bob query that occurs only after all `r` Alice queries is not exposed; its state
is a final Alice-frontier node.  ...  Every first-Bob node has
`kappa_v >= 2`." -/

section Addresses

variable {X Y Z : Type*}

/-- **`09:1250--1251`, `09:1259`.**  A *first-Bob node*: an Alice-only route that
arrives at a Bob query, strictly before the `r`-th Alice query.  The strict depth
clause is the frozen exposure rule of `09:1251--1252`. -/
def IsFirstBobNode (P : Protocol X Y Z) (r : ℕ) (p : List Bool) : Prop :=
  IsAlicePath P p ∧ IsBobNode (descend P p) ∧ p.length < r

/-- **`09:1250--1252`.**  A *final Alice-frontier node*: an Alice-only route of
length exactly `r`.  A Bob query here "is not exposed". -/
def IsFinalAliceNode (P : Protocol X Y Z) (r : ℕ) (p : List Bool) : Prop :=
  IsAlicePath P p ∧ p.length = r

/-- **Aux B1 (the two stopping rules are exclusive).**  No address is both a
first-Bob node and a final Alice node: the depth clauses `< r` and `= r`
separate them.  General. -/
theorem not_isFirstBob_and_isFinal {P : Protocol X Y Z} {r : ℕ} {p : List Bool}
    (h₁ : IsFirstBobNode P r p) (h₂ : IsFinalAliceNode P r p) : False := by
  have := h₁.2.2
  have := h₂.2
  omega

/-- **`09:1259`, "Every first-Bob node has `kappa_v >= 2`".**  At a first-Bob
address the banked `stoppingCapacity` is at least two.  Proved from the frozen
exposure rule alone. -/
theorem two_le_stoppingCapacity_firstBob {P : Protocol X Y Z} {r : ℕ} {p : List Bool}
    (h : IsFirstBobNode P r p) : 2 ≤ stoppingCapacity r p.length := by
  have hlt := h.2.2
  have h1 : 1 ≤ r - p.length := by omega
  unfold stoppingCapacity
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (r - p.length) := Nat.pow_le_pow_right (by norm_num) h1

/-- **`09:1250--1252`.**  A final Alice node has capacity one: `d_v = r`. -/
theorem stoppingCapacity_final_eq_one {P : Protocol X Y Z} {r : ℕ} {p : List Bool}
    (h : IsFinalAliceNode P r p) : stoppingCapacity r p.length = 1 := by
  unfold stoppingCapacity
  rw [h.2]
  simp

/-- **`09:1341--1343`, at a final node.**  In the alleged `(C+r-1)`-bit protocol
the residual subtree below a final Alice node has depth at most `C-1`, which is
exactly the input the banked `finalNode_budget_contradiction` consumes. -/
theorem finalNode_residual_budget {P : Protocol X Y Z} {r C : ℕ} {p : List Bool}
    (h : IsFinalAliceNode P r p) (hcost : P.cost ≤ C + r - 1) :
    (descend P p).cost + r ≤ C + r - 1 := by
  have hb := cost_descend_add_length_le_of_isAlicePath h.1
  rw [h.2] at hb
  omega

/-- **`09:1306--1308`, at a first-Bob node.**  "Its lower bound is one more bit
than the remaining child budget in the alleged protocol": at a first-Bob address
of depth `d` the residual subtree keeps at most `C + r - 1 - d` bits, the input
of the banked `firstBob_budget_contradiction`. -/
theorem firstBob_residual_budget {P : Protocol X Y Z} {r C : ℕ} {p : List Bool}
    (h : IsFirstBobNode P r p) (hcost : P.cost ≤ C + r - 1) :
    (descend P p).cost + p.length ≤ C + r - 1 := by
  have hb := cost_descend_add_length_le_of_isAlicePath h.1
  omega

end Addresses

/-! ## §3  The node's column set and the owner rectangle
(`09:1287--1290`, `09:1327--1331`)

"Every represented coordinate is outside `E_0`, so the parent projection to any
selected `u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob
child retains density at least `y^2`" and, at a final node, "no Bob query has
occurred on the route to this node.  Its two-coordinate column projection
consequently still has density at least `rho = 2y^2`."

The frozen sentences are statements about *Bob's* side of the rectangle at a
protocol node.  Both are derived below; neither is assumed. -/

section Columns

variable {X Y Z : Type*} [Fintype Y] [DecidableEq Y]

/-- The constraint one step of the walk places on Bob's inputs: a Bob query cuts
his column set by the answer bit, an Alice query and a leaf cut nothing. -/
def bobConstraint : Protocol X Y Z → Bool → Finset Y
  | Protocol.bNode f _ _, b => Finset.univ.filter fun y => f y = b
  | Protocol.leaf _, _ => Finset.univ
  | Protocol.aNode _ _ _, _ => Finset.univ

/-- **The per-node column set.**  Bob's inputs consistent with the route `p`
below `P`.  This is the object the frozen "column projection at a node" of
`09:1287--1290` and `09:1330--1331` projects. -/
def bobCols : Protocol X Y Z → List Bool → Finset Y
  | _, [] => Finset.univ
  | P, b :: p => bobConstraint P b ∩ bobCols (descendStep P b) p

/-- **Aux C1.**  At the root every column survives.  General. -/
@[simp] theorem bobCols_nil (P : Protocol X Y Z) : bobCols P ([] : List Bool) = Finset.univ :=
  rfl

/-- **Aux C2.**  The defining step of the column set.  General. -/
theorem bobCols_cons (P : Protocol X Y Z) (b : Bool) (p : List Bool) :
    bobCols P (b :: p) = bobConstraint P b ∩ bobCols (descendStep P b) p := rfl

omit [DecidableEq Y] in
/-- **Aux C3.**  An Alice query places no constraint on Bob's columns -- the
protocol-side content of "no Bob query has occurred".  General. -/
theorem bobConstraint_of_isANode {P : Protocol X Y Z} (h : IsANode P) (b : Bool) :
    bobConstraint P b = Finset.univ := by
  obtain ⟨a, l, r, rfl⟩ := h
  rfl

/-- **`09:1330--1331`, proved.**  "no Bob query has occurred on the route to this
node.  Its two-coordinate column projection consequently still has density at
least `rho = 2y^2`."  Along an Alice-only route Bob's column set is *unchanged*:
it is still all of `Y`.  This is the exact protocol-side fact the frozen final
node argument uses, and the banked `wrapperFinalReferenceUniqueness` carried as
the hypothesis `hladder` for want of it. -/
theorem bobCols_of_isAlicePath : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsAlicePath P p → bobCols P p = Finset.univ := by
  intro P p
  induction p generalizing P with
  | nil => intro _; rfl
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩
      rw [bobCols_cons, bobConstraint_of_isANode hnode, ih hrest, Finset.univ_inter]

/-- **Aux C4 (a Bob query splits, it does not delete).**  At a Bob node the two
answer bits cover every column.  General. -/
theorem bobConstraint_union {P : Protocol X Y Z} (h : IsBobNode P) :
    bobConstraint P false ∪ bobConstraint P true = Finset.univ := by
  cases P with
  | leaf z => exact absurd h (by simp [IsBobNode])
  | aNode a l r => exact absurd h (by simp [IsBobNode])
  | bNode f l r =>
      ext y
      simp only [bobConstraint, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      cases f y <;> simp

omit [DecidableEq Y] in
/-- **Aux C5.**  The two Bob children of a Bob query are disjoint on columns: the
answer bit is a genuine partition of Bob's inputs, so `09:1287--1290`'s "the
denser Bob child" is a choice between two disjoint halves.  General. -/
theorem bobConstraint_disjoint_of_isBobNode {P : Protocol X Y Z} (h : IsBobNode P) :
    Disjoint (bobConstraint P false) (bobConstraint P true) := by
  cases P with
  | leaf z => exact absurd h (by simp [IsBobNode])
  | aNode a l r => exact absurd h (by simp [IsBobNode])
  | bNode f l r =>
      refine Finset.disjoint_left.mpr fun y hy hy' => ?_
      simp only [bobConstraint, Finset.mem_filter] at hy hy'
      rw [hy.2] at hy'
      exact Bool.noConfusion hy'.2

/-- **The column split at a Bob query, proved** -- the **column-set** form of the
partition the frozen `09:1287--1290` argument projects.  The two Bob children of
the node at `p` partition that node's column set.  This is *not* the frozen
projection statement itself; see GAP-EXPOSED item 7. -/
theorem bobCols_children_union : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsBobNode (descend P p) →
      bobCols P (p ++ [false]) ∪ bobCols P (p ++ [true]) = bobCols P p := by
  intro P p
  induction p generalizing P with
  | nil =>
      intro h
      simp only [List.nil_append, bobCols_cons, bobCols_nil, Finset.inter_univ, bobCols_nil]
      exact bobConstraint_union (by simpa using h)
  | cons c p ih =>
      intro h
      have hstep : IsBobNode (descend (descendStep P c) p) := by
        simpa [descend_cons] using h
      simp only [List.cons_append, bobCols_cons]
      rw [← Finset.inter_union_distrib_left, ih hstep]

/-- **The split is a partition** (column-set form; cf. `09:1287--1290`).  The two
Bob children of the node at `p` are disjoint -- so the frozen "denser Bob child"
is a choice between two halves that exhaust the parent without overlap. -/
theorem bobCols_children_disjoint : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsBobNode (descend P p) →
      Disjoint (bobCols P (p ++ [false])) (bobCols P (p ++ [true])) := by
  intro P p
  induction p generalizing P with
  | nil =>
      intro h
      simp only [List.nil_append, bobCols_cons, bobCols_nil, Finset.inter_univ]
      exact bobConstraint_disjoint_of_isBobNode (by simpa using h)
  | cons c p ih =>
      intro h
      have hstep : IsBobNode (descend (descendStep P c) p) := by
        simpa [descend_cons] using h
      have hdisj := ih hstep
      simp only [List.cons_append, bobCols_cons]
      refine Finset.disjoint_left.mpr fun y hy hy' => ?_
      rw [Finset.mem_inter] at hy hy'
      exact (Finset.disjoint_left.mp hdisj hy.2) hy'.2

/-- **The exact mass balance at a Bob query** (column-set form of the counting the
frozen `09:1287--1290` performs on the projection).  Against any ambient column
family `S`, the two Bob children of the node at `p` split `S`'s
share of that node *exactly*.  The hypothesis is load-bearing: at an Alice query
both children inherit the whole parent set and the two shares sum to **twice**
the parent's, which `bobCols_children_add_pole_at_alice` exhibits. -/
theorem card_bobCols_children_add {P : Protocol X Y Z} {p : List Bool}
    (h : IsBobNode (descend P p)) (S : Finset Y) :
    (S ∩ bobCols P (p ++ [false])).card + (S ∩ bobCols P (p ++ [true])).card
      = (S ∩ bobCols P p).card := by
  have hdisj : Disjoint (S ∩ bobCols P (p ++ [false])) (S ∩ bobCols P (p ++ [true])) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right
        (bobCols_children_disjoint h))
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left,
    bobCols_children_union h]

/-- **The denser-Bob-child halving in its column-set form.**  Against any ambient
column family `S`, one of the two Bob children of the node at `p` retains at
least half of `S`'s share of that node.

**Scope (GAP-EXPOSED item 7).**  The frozen sentence at `09:1287--1290` -- "the
parent projection to any selected `u_{kappa_v}` of them has density at least
`rho=2y^2`.  The denser Bob child retains density at least `y^2`" -- is about the
*projection* `projSet J` of the retained column set, not about the column set
itself.  This theorem is the column-set analogue that argument runs on; the
projection form is **not landed**, and this declaration must not be cited as
discharging `09:1287--1290`.

*Why no fixed bit works.*  The existential really quantifies: neither `false` nor
`true` is a uniform witness, because a Bob predicate may send every column to one
child.  `denserChild_needs_the_right_bit` exhibits a Bob query at which `false`
fails the bound outright.  General in `S`. -/
theorem exists_denser_bob_child {P : Protocol X Y Z} {p : List Bool}
    (h : IsBobNode (descend P p)) (S : Finset Y) :
    ∃ b : Bool, (S ∩ bobCols P p).card ≤ 2 * (S ∩ bobCols P (p ++ [b])).card := by
  have hcard := card_bobCols_children_add h S
  rcases le_total (S ∩ bobCols P (p ++ [false])).card
      (S ∩ bobCols P (p ++ [true])).card with hle | hle
  · exact ⟨true, by omega⟩
  · exact ⟨false, by omega⟩

/-- **`09:1287--1290`, the retained column set at a node.**  The frozen argument
never projects all of `Y`: it projects the *retained* outer column set of `U'`,
cut by the node.  This is that intersection. -/
def retainedCols (P : Protocol X Y Z) (S : Finset Y) (p : List Bool) : Finset Y :=
  S ∩ bobCols P p

/-- **Aux C6.**  At the root nothing is cut.  General. -/
@[simp] theorem retainedCols_nil (P : Protocol X Y Z) (S : Finset Y) :
    retainedCols P S [] = S := by simp [retainedCols]

/-- **`09:1330--1331`, the form the frozen proof uses.**  Along an Alice-only
route the retained column set is *literally unchanged*, so whatever density it
had at the root it still has at the node.  This is what discharges the density
input the banked `wrapperFinalReferenceUniqueness` carries as `hladder`. -/
theorem retainedCols_of_isAlicePath {P : Protocol X Y Z} {S : Finset Y} {p : List Bool}
    (h : IsAlicePath P p) : retainedCols P S p = S := by
  simp [retainedCols, bobCols_of_isAlicePath h]

/-- **Aux C7 (the retained set only shrinks along a Bob step).**  General. -/
theorem retainedCols_subset (P : Protocol X Y Z) (S : Finset Y) (p : List Bool) :
    retainedCols P S p ⊆ S := Finset.inter_subset_left

/-- **`09:1287--1290`, the per-node column projection.**  The banked
`WrapperProjectionCovers.projSet` applied to the node's retained column set: the
object whose density the frozen sentences bound.  Consumed by pin; `projSet` is
not restated. -/
def nodeProjection {q : ℕ} {Yc : Type*} [DecidableEq Yc] [Fintype Yc]
    {X Z : Type*} (P : Protocol X (Fin q → Yc) Z) (S : Finset (Fin q → Yc))
    (J : Finset (Fin q)) (p : List Bool) : Finset (↥J → Yc) :=
  WrapperProjectionCovers.projSet J (retainedCols P S p)

/-- **`09:1330--1331`, the projection form, proved.**  At an Alice-only address
the node's column projection is the ambient one -- no density is lost, which is
exactly the frozen "its two-coordinate column projection consequently still has
density at least `rho`". -/
theorem nodeProjection_of_isAlicePath {q : ℕ} {Yc : Type*} [DecidableEq Yc] [Fintype Yc]
    {X Z : Type*} {P : Protocol X (Fin q → Yc) Z} {S : Finset (Fin q → Yc)}
    {J : Finset (Fin q)} {p : List Bool} (h : IsAlicePath P p) :
    nodeProjection P S J p = WrapperProjectionCovers.projSet J S := by
  simp [nodeProjection, retainedCols_of_isAlicePath h]

end Columns

/-! ## §4  The owner rectangle (`09:1611--1615`, `09:1666--1669`)

"That lemma supplies the explicit restriction-preserving maps and makes the owner
rectangle an `(eps_i, delta_i)`-two-stream terminal state."  The *rectangle* at a
node is the product of the two players' surviving input sets, and the property
that makes it a rectangle at all is that the protocol's output on it is decided
by the node's subtree.  That property is proved here. -/

section Rectangle

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The constraint one step of the walk places on Alice's inputs. -/
def aliceConstraint : Protocol X Y Z → Bool → Finset X
  | Protocol.aNode a _ _, b => Finset.univ.filter fun x => a x = b
  | Protocol.leaf _, _ => Finset.univ
  | Protocol.bNode _ _ _, _ => Finset.univ

/-- Alice's surviving input set at the node reached by `p`. -/
def aliceCols : Protocol X Y Z → List Bool → Finset X
  | _, [] => Finset.univ
  | P, b :: p => aliceConstraint P b ∩ aliceCols (descendStep P b) p

omit [Fintype Y] [DecidableEq Y] in
/-- **Aux R1.**  At the root every row survives.  General. -/
@[simp] theorem aliceCols_nil (P : Protocol X Y Z) : aliceCols P ([] : List Bool) = Finset.univ :=
  rfl

omit [Fintype Y] [DecidableEq Y] in
/-- **Aux R2.**  The defining step of Alice's set.  General. -/
theorem aliceCols_cons (P : Protocol X Y Z) (b : Bool) (p : List Bool) :
    aliceCols P (b :: p) = aliceConstraint P b ∩ aliceCols (descendStep P b) p := rfl

omit [Fintype Y] [DecidableEq Y] in
/-- **Aux R3 (dual of `bobCols_of_isAlicePath`).**  A Bob-only route leaves
Alice's set untouched.  General; the banked `IsBobPath` is the frozen
`08:952--953` route type. -/
theorem aliceCols_of_isBobPath : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsBobPath P p → aliceCols P p = Finset.univ := by
  intro P p
  induction p generalizing P with
  | nil => intro _; rfl
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩
      have hc : aliceConstraint P b = Finset.univ := by
        cases P with
        | leaf z => exact absurd hnode (by simp [IsBobNode])
        | aNode a l r => exact absurd hnode (by simp [IsBobNode])
        | bNode f l r => rfl
      rw [aliceCols_cons, hc, ih hrest, Finset.univ_inter]

/-- **The node is a rectangle (`09:1666--1669`, "the owner rectangle").**

On the product `aliceCols P p × bobCols P p` the whole protocol agrees with the
subtree at `p`.  This is what makes the node's surviving inputs a combinatorial
rectangle on which the residual protocol -- of cost at most
`cost(P) - p.length`, by `cost_descend_add_length_le_of_isAlicePath` -- is the
only thing left to run, and hence what makes the frozen "budget below the node"
sentences meaningful.  General. -/
theorem eval_descend_of_mem_rect : ∀ {P : Protocol X Y Z} {p : List Bool} {x : X} {y : Y},
    x ∈ aliceCols P p → y ∈ bobCols P p →
      Protocol.eval P x y = Protocol.eval (descend P p) x y := by
  intro P p
  induction p generalizing P with
  | nil => intro x y _ _; rfl
  | cons b p ih =>
      intro x y hx hy
      rw [aliceCols_cons, Finset.mem_inter] at hx
      rw [bobCols_cons, Finset.mem_inter] at hy
      have hstep : Protocol.eval P x y = Protocol.eval (descendStep P b) x y := by
        cases P with
        | leaf z => cases b <;> rfl
        | aNode a l r =>
            have hax : a x = b := by
              have := hx.1
              simpa [aliceConstraint] using this
            cases b <;> simp [Protocol.eval, descendStep, hax]
        | bNode f l r =>
            have hfy : f y = b := by
              have := hy.1
              simpa [bobConstraint] using this
            cases b <;> simp [Protocol.eval, descendStep, hfy]
      rw [hstep, descend_cons]
      exact ih hx.2 hy.2

/-- **Aux R4 (the rectangle is nonempty exactly when the node is reachable).**
Alice's and Bob's surviving sets at the root are both everything, so the root
rectangle is the whole input space.  General. -/
theorem rect_root (P : Protocol X Y Z) (x : X) (y : Y) :
    x ∈ aliceCols P ([] : List Bool) ∧ y ∈ bobCols P ([] : List Bool) :=
  ⟨Finset.mem_univ x, Finset.mem_univ y⟩

end Rectangle

/-! ## §5  The routed certificate (`09:1236--1248`)

"Start one clean reference certificate in every coordinate outside `E_0`, each
with weight one.  At remaining selector capacity `2^k`, a certificate consists of
at least `A_k` reference rows in one outer coordinate." -/

section Certificate

variable {X Y Z : Type*}

/-- **`09:1236--1248`, the routed certificate as an object of the protocol.**

A certificate carries an outer coordinate, the route it has followed below the
root, its kind (the banked `CertKind`), and the number of reference rows it still
holds.  The three laws are the frozen ones and no others: the route it has
followed is Alice-only (it has not yet met a Bob query, `09:1250`), it has not
outrun the `r` Alice queries (`09:1251`), and at remaining selector capacity
`2^k` -- i.e. at `k = r - d` -- it holds at least `A_k` reference rows
(`09:1238--1239`), where `A_k` is the banked `refRowFloor`.

**No complexity or robustness conclusion is constructor data** (mechanical rules
M1--M10), and in particular nothing here says the certificate is *hard*. -/
structure RoutedCertificate (P : Protocol X Y Z) (Coord : Type*) (r A0 : ℕ) where
  /-- The outer coordinate the certificate descends from (`09:1236`). -/
  coord : Coord
  /-- The route followed below the root (`09:1238--1244`). -/
  route : List Bool
  /-- Clean or low (`09:1245--1247`), the banked `CertKind`. -/
  kind : CertKind
  /-- The reference rows it still holds (`09:1239--1240`). -/
  rows : ℕ
  /-- `09:1250`: the branch has not yet met a Bob query. -/
  route_alice : IsAlicePath P route
  /-- `09:1250`: it has not outrun the `r` Alice queries (the frozen clause "or
  after `r` Alice queries" is on line 1250; 1251 is the non-exposure sentence). -/
  route_len_le : route.length ≤ r
  /-- `09:1238--1239`: at remaining selector capacity `2^k` the certificate holds
  at least `A_k` reference rows.  `refRowFloor` is the banked `A_k = 2^k A_0`. -/
  rows_floor : refRowFloor A0 (r - route.length) ≤ rows

namespace RoutedCertificate

variable {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}

/-- `09:1253`, `d_v`: the number of preceding Alice queries (`09:1254` is the
display opener). -/
def depth (c : RoutedCertificate P Coord r A0) : ℕ := c.route.length

/-- `09:1255`, `kappa_v = 2^{r - d_v}`, the banked `stoppingCapacity`. -/
def capacity (c : RoutedCertificate P Coord r A0) : ℕ := stoppingCapacity r c.depth

/-- `09:1236`, `09:1246`: the certificate's weight, the banked `CertKind.weight`. -/
noncomputable def weight (c : RoutedCertificate P Coord r A0) : ℝ := c.kind.weight

/-- **Aux D1.**  The depth is the route length.  General. -/
@[simp] theorem depth_eq (c : RoutedCertificate P Coord r A0) : c.depth = c.route.length := rfl

/-- **Aux D2.**  Every certificate has positive remaining selector capacity.
General. -/
theorem one_le_capacity (c : RoutedCertificate P Coord r A0) : 1 ≤ c.capacity :=
  one_le_stoppingCapacity _ _

/-- **Aux D3.**  No certificate's capacity exceeds the wrapper width `q = 2^r`.
General. -/
theorem capacity_le_width (c : RoutedCertificate P Coord r A0) : c.capacity ≤ 2 ^ r := by
  unfold capacity stoppingCapacity depth
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`09:1238--1239`, the frozen row floor in capacity form.**  "At remaining
selector capacity `2^k`, a certificate consists of at least `A_k` reference
rows": since `A_k = 2^k A_0` and `2^k` is the capacity, the certificate holds at
least `kappa_v A_0` rows.  This is the exact quantity the frozen
`A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` of `09:1292--1295` names. -/
theorem capacity_mul_initial_le_rows (c : RoutedCertificate P Coord r A0) :
    c.capacity * A0 ≤ c.rows := by
  have h := c.rows_floor
  unfold capacity stoppingCapacity depth
  simpa [refRowFloor] using h

/-- **Aux D4.**  A certificate with a positive initial row floor holds rows.
General. -/
theorem rows_pos (c : RoutedCertificate P Coord r A0) (hA0 : 1 ≤ A0) : 0 < c.rows := by
  have h := c.capacity_mul_initial_le_rows
  have h1 := c.one_le_capacity
  have : 1 ≤ c.capacity * A0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- **Aux D5.**  A certificate's route is a query route, so the banked budget
accounting applies to it.  General. -/
theorem route_isQueryPath (c : RoutedCertificate P Coord r A0) :
    IsQueryPath P c.route :=
  isQueryPath_of_isAlicePath c.route_alice

/-- **Aux D6.**  A certificate never outruns the protocol's budget.  General. -/
theorem depth_le_cost (c : RoutedCertificate P Coord r A0) : c.depth ≤ P.cost :=
  length_le_cost_of_isAlicePath c.route_alice

/-- **Aux D7.**  Bob's columns are untouched at a certificate's node -- every
certificate sits on an Alice-only route by construction.  General. -/
theorem bobCols_eq_univ [Fintype Y] [DecidableEq Y] (c : RoutedCertificate P Coord r A0) :
    bobCols P c.route = Finset.univ :=
  bobCols_of_isAlicePath c.route_alice

end RoutedCertificate

/-- **`09:1233--1236`, the paper's own initial placement.**

"Even if every deleted row of `U` were concentrated in one nonexceptional outer
coordinate, that coordinate would therefore retain at least `A_r = q A_0`
reference rows.  Start one clean reference certificate in every coordinate
outside `E_0`, each with weight one."

The route is empty (the root), the kind is `clean`, and the row count is the
frozen `A_r`, obtained by **evaluating** the banked `refRowFloor` at the frozen
exponent `r` -- not by assigning a numeral.

**On the `E_0` side condition of the quotation.**  The coordinate `i` is
arbitrary here, with no "outside `E_0`" restriction, and that is deliberate:
membership outside `E_0` is **not** one of the certificate's three frozen laws
(`09:1238--1239`, `09:1250--1251`) but a fact about *which* coordinates the
frozen argument starts certificates in, tracked by the exceptional-set and cover
bookkeeping of the banked `WrapperProjectionCovers`.  Folding it into the
constructor would make this definition demand more than the frozen text states
(mechanical rules M1--M10). -/
def initialCertificate (P : Protocol X Y Z) {Coord : Type*} (i : Coord) (r A0 : ℕ) :
    RoutedCertificate P Coord r A0 where
  coord := i
  route := []
  kind := CertKind.clean
  rows := refRowFloor A0 r
  route_alice := isAlicePath_nil P
  route_len_le := by simp
  rows_floor := by simp

/-- **`09:1236`, evaluated.**  The initial certificate holds exactly the frozen
`A_r = q A_0` reference rows at the wrapper width `q = 2^r`. -/
theorem initialCertificate_rows (P : Protocol X Y Z) {Coord : Type*} (i : Coord) (r A0 : ℕ) :
    (initialCertificate P i r A0).rows = 2 ^ r * A0 := rfl

/-- **`09:1255` at the root.**  The initial certificate has full remaining
selector capacity `2^r = q`. -/
theorem initialCertificate_capacity (P : Protocol X Y Z) {Coord : Type*} (i : Coord)
    (r A0 : ℕ) : (initialCertificate P i r A0).capacity = 2 ^ r := by
  simp [RoutedCertificate.capacity, RoutedCertificate.depth, initialCertificate,
    stoppingCapacity]

/-- **Non-vacuity of `RoutedCertificate` at the paper's own placement.**  At any
legal wrapper width and any positive initial row floor the paper's initial
certificate is clean, carries weight one, holds `q A_0 > 0` rows and has full
capacity: the structure is inhabited by the paper's object, not by a degenerate
one. -/
theorem initialCertificate_nondegenerate (P : Protocol X Y Z) {Coord : Type*} (i : Coord)
    {r A0 : ℕ} (hA0 : 1 ≤ A0) :
    (initialCertificate P i r A0).kind = CertKind.clean ∧
      (initialCertificate P i r A0).weight = 1 ∧
      0 < (initialCertificate P i r A0).rows ∧
      (initialCertificate P i r A0).capacity = 2 ^ r := by
  refine ⟨rfl, rfl, ?_, initialCertificate_capacity P i r A0⟩
  exact (initialCertificate P i r A0).rows_pos hA0

end Certificate

/-! ## §6  The routed certificate system (`09:1250--1259`, `09:1278--1280`)

The frontier of the routed branches, together with the certificates sitting on
it.  This is the object `WRAPPER-MASS-REDISTRIBUTION-001` records as absent under
GAP-EXPOSED M1. -/

section System

variable {X Y Z : Type*}

/-- **The routed certificate system on an alleged protocol.**

The frontier is indexed by `V`; each node has an address in the protocol, the
addresses are prefix-free (`09:1259`), and each is one of the two frozen stopping
states (`09:1250--1252`).  The certificates are indexed by `ι`, each placed at a
frontier node whose address it has reached, subject to the frozen coordinate
uniqueness of `09:1278--1280` and `09:1323--1324`: "a fixed protocol node
receives at most one descendant of any initial certificate".

**Deliberately not fields:** the per-node weight `W_v`, the count `c`, the
capacities `K_B`, and every complexity conclusion.  `W_v` is the routing's output
and enters the banked counting lemmas as an explicit binder; folding it in would
make this record demand more than `09:1250--1258` states (mechanical rules
M1--M10). -/
structure RoutedSystem (P : Protocol X Y Z) (Coord ι V : Type*) (r A0 : ℕ) where
  /-- The address of each frontier node (`09:1253`). -/
  node : V → List Bool
  /-- `09:1259`, "Prefix-freeness", the banked `PrefixFreeFrontier`. -/
  prefixFree : PrefixFreeFrontier node
  /-- Which of the two frozen stopping rules stopped the branch (`09:1250`). -/
  firstBob : V → Bool
  /-- `09:1250--1251`: an exposed first-Bob node. -/
  firstBob_spec : ∀ v, firstBob v = true → IsFirstBobNode P r (node v)
  /-- `09:1251--1252`: a final Alice-frontier node. -/
  final_spec : ∀ v, firstBob v = false → IsFinalAliceNode P r (node v)
  /-- Where each certificate stopped. -/
  place : ι → V
  /-- The certificate itself. -/
  cert : ι → RoutedCertificate P Coord r A0
  /-- The certificate's route is its node's address. -/
  cert_at : ∀ i, (cert i).route = node (place i)
  /-- `09:1278--1280`, `09:1323--1324`: "a fixed protocol node receives at most
  one descendant of any initial certificate". -/
  coordUnique : ∀ i j, place i = place j → (cert i).coord = (cert j).coord → i = j

namespace RoutedSystem

variable {P : Protocol X Y Z} {Coord ι V : Type*} {r A0 : ℕ}

/-- **`09:1250--1252`.**  Every frontier address is an Alice-only route: neither
stopping rule has passed a Bob query. -/
theorem node_isAlicePath (S : RoutedSystem P Coord ι V r A0) (v : V) :
    IsAlicePath P (S.node v) := by
  cases h : S.firstBob v
  · exact (S.final_spec v h).1
  · exact (S.firstBob_spec v h).1

/-- **`09:1250--1252`.**  No branch is stopped later than the `r`-th Alice
query. -/
theorem node_depth_le (S : RoutedSystem P Coord ι V r A0) (v : V) :
    (S.node v).length ≤ r := by
  cases h : S.firstBob v
  · exact le_of_eq (S.final_spec v h).2
  · exact le_of_lt (S.firstBob_spec v h).2.2

/-- **The bridge to the banked abstract frontier.**

Every routed certificate system on a genuine protocol *is* a
`DenseWrapperFrontier.WrapperFrontier` at the same width, so the whole banked
counting spine of `09:1259--1365` -- Kraft, `eq:wrapper-clean-count`, the
capacity readouts -- applies to the protocol object without restatement.  This
is the payoff of the tranche: the abstract record was banked with GAP-EXPOSED
item 2 ("the protocol side is not modelled"), and this is the missing
realization. -/
def toWrapperFrontier (S : RoutedSystem P Coord ι V r A0) : WrapperFrontier r V where
  route := S.node
  prefixFree := S.prefixFree
  depth_le := S.node_depth_le
  firstBob := S.firstBob
  firstBob_depth_lt := fun v h => (S.firstBob_spec v h).2.2
  final_depth_eq := fun v h => (S.final_spec v h).2

/-- **Aux S1.**  The bridge keeps the addresses.  General. -/
@[simp] theorem toWrapperFrontier_route (S : RoutedSystem P Coord ι V r A0) :
    S.toWrapperFrontier.route = S.node := rfl

/-- **Aux S2.**  The bridge keeps `kappa_v`.  General. -/
theorem toWrapperFrontier_capacity (S : RoutedSystem P Coord ι V r A0) (v : V) :
    S.toWrapperFrontier.capacity v = stoppingCapacity r (S.node v).length := rfl

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), on the
protocol object.**  `sum_v kappa_v <= q` at the wrapper width `q = 2^r`,
obtained from the banked Kraft inequality through the bridge.  Not re-proved. -/
theorem sum_capacity_le_width [Fintype V] (S : RoutedSystem P Coord ι V r A0) :
    ∑ v, stoppingCapacity r (S.node v).length ≤ 2 ^ r :=
  S.toWrapperFrontier.sum_capacity_le_width

/-- **Aux S3.**  Prefix-freeness makes frontier nodes determined by their
addresses.  Consumed from the banked `prefixFreeFrontier_injective`.  General. -/
theorem node_injective (S : RoutedSystem P Coord ι V r A0) {v w : V}
    (h : S.node v = S.node w) : v = w :=
  prefixFreeFrontier_injective S.prefixFree h

/-- **`09:1330--1331`, at every frontier node of a genuine protocol.**  Bob's
column set is untouched everywhere on the frontier: both stopping rules stop
*before* any Bob query is answered. -/
theorem bobCols_frontier [Fintype Y] [DecidableEq Y]
    (S : RoutedSystem P Coord ι V r A0) (v : V) :
    bobCols P (S.node v) = Finset.univ :=
  bobCols_of_isAlicePath (S.node_isAlicePath v)

/-- **`09:1330--1331`, the retained form.**  The retained outer column set of `U'`
reaches every frontier node undiminished, so its ambient density is its density
at the node.  This is the frozen density input of `lem:final-reference-uniqueness`
and of the small-capacity branch, now derived. -/
theorem retainedCols_frontier [Fintype Y] [DecidableEq Y]
    (S : RoutedSystem P Coord ι V r A0) (Scols : Finset Y) (v : V) :
    retainedCols P Scols (S.node v) = Scols :=
  retainedCols_of_isAlicePath (S.node_isAlicePath v)

/-- **`09:1341--1343`, on the protocol object.**  At a final Alice node of the
alleged `(C+r-1)`-bit protocol the residual subtree has depth at most `C-1`; this
is exactly the `hsuffix` the banked `finalNode_budget_contradiction` and
`wrapperFinalReferenceUniqueness` consume. -/
theorem final_residual_budget {C : ℕ} (S : RoutedSystem P Coord ι V r A0) {v : V}
    (hv : S.firstBob v = false) (hcost : P.cost ≤ C + r - 1) :
    (descend P (S.node v)).cost + r ≤ C + r - 1 :=
  finalNode_residual_budget (S.final_spec v hv) hcost

/-- **`09:1306--1308`, on the protocol object.**  At a first-Bob node the residual
subtree keeps at most `C + r - 1 - d_v` bits -- the `hbudget` of the banked
`firstBob_budget_contradiction`. -/
theorem firstBob_residual_budget' {C : ℕ} (S : RoutedSystem P Coord ι V r A0) {v : V}
    (hv : S.firstBob v = true) (hcost : P.cost ≤ C + r - 1) :
    (descend P (S.node v)).cost + (S.node v).length ≤ C + r - 1 :=
  firstBob_residual_budget (S.firstBob_spec v hv) hcost

section Owners

variable [Fintype ι]

/-- **`09:1519--1520`.**  The clean certificates that reached a final
Alice node: the frozen `J_clean`, "the `c` outer coordinates whose clean
reference certificates reach final Alice nodes". -/
def cleanFinal (S : RoutedSystem P Coord ι V r A0) : Finset ι :=
  Finset.univ.filter fun i => (S.cert i).kind = CertKind.clean ∧ S.firstBob (S.place i) = false

/-- **`09:1550`.**  "Every clean reference certificate has a unique final
node, its *owner*." -/
def owner (S : RoutedSystem P Coord ι V r A0) (i : ι) : V := S.place i

/-- **Aux O1.**  The owner of a clean-final certificate is a final Alice node.
General. -/
theorem owner_isFinal (S : RoutedSystem P Coord ι V r A0) {i : ι} (hi : i ∈ S.cleanFinal) :
    IsFinalAliceNode P r (S.node (S.owner i)) := by
  simp only [cleanFinal, Finset.mem_filter] at hi
  exact S.final_spec _ hi.2.2

omit [Fintype ι] in
/-- **Aux O2.**  A certificate sits at its owner's address.  General. -/
theorem cert_route_eq_owner (S : RoutedSystem P Coord ι V r A0) (i : ι) :
    (S.cert i).route = S.node (S.owner i) := S.cert_at i

/-- **`09:1550--1552`, owner injectivity, on the protocol object.**

"Distinct clean donors have distinct owners because a final node contains at most
one clean certificate."  The uniqueness input is the banked
`lem:final-reference-uniqueness` in counting form; the conclusion is the banked
`WrapperMassRedistribution.owner_injOn_of_unique_clean`, consumed by pin at the
owner map this module defines. -/
theorem owner_injOn [DecidableEq V] (S : RoutedSystem P Coord ι V r A0)
    (huniq : ∀ v : V, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1) :
    ∀ i ∈ S.cleanFinal, ∀ j ∈ S.cleanFinal, S.owner i = S.owner j → i = j :=
  owner_injOn_of_unique_clean S.cleanFinal S.owner huniq

/-- **`09:1315--1344` and `09:1550--1552`, chained on the protocol object.**

`lem:final-reference-uniqueness` in the shape the frozen text uses it: at a final
node, two distinct clean certificates carry distinct outer coordinates (this
module's `coordUnique`), the ladder call at those two coordinates would give the
node residual complexity at least `C`, and the frozen suffix budget of
`09:1341--1343` -- here *derived* from the protocol object by
`final_residual_budget` -- allows only `C-1`.  Hence at most one clean
certificate per final node, hence injective owners.

`hladder` is the `lem:certified-row-ladder` call of `09:1334--1338`, carried as
the named hypothesis it is: the ladder itself is the banked
`TerminalTwoStream.certifiedRowLadder_of_base`, and re-siting it at this
module's owner rectangle is GAP-EXPOSED item 1.  What this declaration removes
from the banked statement is the *density* premise: by `retainedCols_frontier`
the node's column projection is the ambient one, so the frozen "no Bob query has
occurred on the route to this node" is discharged rather than assumed. -/
theorem owner_injOn_of_ladder {C : ℕ} (S : RoutedSystem P Coord ι V r A0)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (residual : ι → ι → ℕ)
    (hresidual : ∀ i j, residual i j ≤ (descend P (S.node (S.owner i))).cost)
    (hladder : ∀ i ∈ S.cleanFinal, ∀ j ∈ S.cleanFinal,
      S.owner i = S.owner j → (S.cert i).coord ≠ (S.cert j).coord → C ≤ residual i j) :
    ∀ i ∈ S.cleanFinal, ∀ j ∈ S.cleanFinal, S.owner i = S.owner j → i = j := by
  intro i hi j hj hij
  by_contra hne
  have hcoord : (S.cert i).coord ≠ (S.cert j).coord := by
    intro hc
    exact hne (S.coordUnique i j hij hc)
  have hhard : C ≤ residual i j := hladder i hi j hj hij hcoord
  have hfinal : S.firstBob (S.owner i) = false := by
    simp only [cleanFinal, Finset.mem_filter] at hi
    exact hi.2.2
  have hbudget : (descend P (S.node (S.owner i))).cost + r ≤ C + r - 1 :=
    S.final_residual_budget hfinal hcost
  have hres := hresidual i j
  exact finalNode_budget_contradiction (C := C) (r := r) (B := residual i j) hC
    (by omega) hhard

end Owners

end RoutedSystem

end System

/-! ## §7  Frame-legal inhabitants

The frozen frame quantifies over an arbitrary alleged protocol, so the canonical
instance of `RoutedSystem` is the routing of the paper's *completed* protocol,
which needs the routing dynamics of GAP-EXPOSED item 1 and is therefore
**registered as a deferred canonical-inhabitation obligation**, not discharged
here.  What follows are two protocols proved to satisfy the frozen frame
conditions of `09:1188--1213`, carrying the two shapes of frontier the frozen
text distinguishes, so that neither branch of `firstBob` is inhabited only
vacuously. -/

section Inhabitants

variable {X Y Z : Type*}

/-- The complete Alice tree of depth `n`: the shape `lem:wrapper-no-bob-completion`
(`09:1195--1213`) forces on every Bob-free path of the completed protocol, where
"append `r-d` fixed Alice messages" makes the new depth "exactly `r`". -/
def aliceLadder (a : X → Bool) (z : Z) : ℕ → Protocol X Y Z
  | 0 => Protocol.leaf z
  | n + 1 => Protocol.aNode a (aliceLadder a z n) (aliceLadder a z n)

/-- **Aux L1.**  Its cost is its depth -- "their new depth is exactly `r`"
(`09:1207`). -/
theorem aliceLadder_cost (a : X → Bool) (z : Z) (n : ℕ) :
    (aliceLadder (X := X) (Y := Y) a z n).cost = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [aliceLadder, Protocol.cost, ih, max_self]
      omega

/-- **`09:1207--1212`, the frame's cost clause.**  "the completed protocol has
cost at most `max{cost(P), r} <= C+r-1`, because `C >= 1`". -/
theorem aliceLadder_cost_le_frame (a : X → Bool) (z : Z) {C r : ℕ} (hC : 1 ≤ C) :
    (aliceLadder (X := X) (Y := Y) a z r).cost ≤ C + r - 1 := by
  rw [aliceLadder_cost]
  omega

/-- **Aux L2.**  Walking the ladder lands on the shorter ladder. -/
theorem descend_aliceLadder (a : X → Bool) (z : Z) :
    ∀ {n : ℕ} {p : List Bool}, p.length ≤ n →
      descend (aliceLadder (X := X) (Y := Y) a z n) p = aliceLadder a z (n - p.length) := by
  intro n p
  induction p generalizing n with
  | nil => intro _; simp
  | cons b p ih =>
      intro h
      cases n with
      | zero => simp at h
      | succ m =>
          have hm : p.length ≤ m := by simpa using h
          have hstep : descendStep (aliceLadder (X := X) (Y := Y) a z (m + 1)) b
              = aliceLadder a z m := by
            cases b <;> simp [aliceLadder, descendStep]
          rw [descend_cons, hstep, ih hm]
          simp

/-- **Aux L3.**  Every route of length at most `n` is an Alice route in the
ladder. -/
theorem isAlicePath_aliceLadder (a : X → Bool) (z : Z) :
    ∀ {n : ℕ} {p : List Bool}, p.length ≤ n →
      IsAlicePath (aliceLadder (X := X) (Y := Y) a z n) p := by
  intro n p
  induction p generalizing n with
  | nil => intro _; trivial
  | cons b p ih =>
      intro h
      cases n with
      | zero => simp at h
      | succ m =>
          refine ⟨⟨a, aliceLadder a z m, aliceLadder a z m, rfl⟩, ?_⟩
          have hstep : descendStep (aliceLadder (X := X) (Y := Y) a z (m + 1)) b
              = aliceLadder a z m := by
            cases b <;> simp [aliceLadder, descendStep]
          rw [hstep]
          exact ih (by simpa using h)

/-- **`09:1195--1200`, the conclusion of `lem:wrapper-no-bob-completion`, checked
on the ladder.**  "every root-to-leaf path containing no Bob query contains at
least `r` Alice queries": in the ladder every route reaching a leaf has length
exactly `r`, so the frame condition holds. -/
theorem aliceLadder_noBob_depth (a : X → Bool) (z : Z) {r : ℕ} {p : List Bool}
    (hlen : p.length ≤ r)
    (hleaf : ∃ w : Z, descend (aliceLadder (X := X) (Y := Y) a z r) p = Protocol.leaf w) :
    p.length = r := by
  obtain ⟨w, hw⟩ := hleaf
  rw [descend_aliceLadder a z hlen] at hw
  by_contra hne
  have hpos : 0 < r - p.length := by omega
  obtain ⟨m, hm⟩ : ∃ m, r - p.length = m + 1 := ⟨r - p.length - 1, by omega⟩
  rw [hm] at hw
  simp [aliceLadder] at hw

/-- The complete Alice tree of depth `n` capped by a Bob query: the shape a
branch has when it is stopped by the frozen "first Bob query" rule
(`09:1250`). -/
def bobCappedLadder (a : X → Bool) (f : Y → Bool) (z : Z) : ℕ → Protocol X Y Z
  | 0 => Protocol.bNode f (Protocol.leaf z) (Protocol.leaf z)
  | n + 1 => Protocol.aNode a (bobCappedLadder a f z n) (bobCappedLadder a f z n)

/-- **Aux L4.** -/
theorem descend_bobCappedLadder (a : X → Bool) (f : Y → Bool) (z : Z) :
    ∀ {n : ℕ} {p : List Bool}, p.length ≤ n →
      descend (bobCappedLadder a f z n) p = bobCappedLadder a f z (n - p.length) := by
  intro n p
  induction p generalizing n with
  | nil => intro _; simp
  | cons b p ih =>
      intro h
      cases n with
      | zero => simp at h
      | succ m =>
          have hstep : descendStep (bobCappedLadder a f z (m + 1)) b
              = bobCappedLadder a f z m := by
            cases b <;> simp [bobCappedLadder, descendStep]
          rw [descend_cons, hstep, ih (by simpa using h)]
          simp

/-- **Aux L5.** -/
theorem isAlicePath_bobCappedLadder (a : X → Bool) (f : Y → Bool) (z : Z) :
    ∀ {n : ℕ} {p : List Bool}, p.length ≤ n →
      IsAlicePath (bobCappedLadder a f z n) p := by
  intro n p
  induction p generalizing n with
  | nil => intro _; trivial
  | cons b p ih =>
      intro h
      cases n with
      | zero => simp at h
      | succ m =>
          refine ⟨⟨a, bobCappedLadder a f z m, bobCappedLadder a f z m, rfl⟩, ?_⟩
          have hstep : descendStep (bobCappedLadder a f z (m + 1)) b
              = bobCappedLadder a f z m := by
            cases b <;> simp [bobCappedLadder, descendStep]
          rw [hstep]
          exact ih (by simpa using h)

/-- **Non-vacuity of `IsFirstBobNode` (`09:1250`, `09:1259`).**  A route of length
`d < r` in the `d`-capped ladder *is* an exposed first-Bob node, so the first-Bob
branch of the frozen stopping rule is inhabited at legal depths, with the frozen
`kappa_v = 2^{r-d} >= 2`. -/
theorem isFirstBobNode_bobCappedLadder (a : X → Bool) (f : Y → Bool) (z : Z)
    {r d : ℕ} {p : List Bool} (hlen : p.length = d) (hd : d < r) :
    IsFirstBobNode (bobCappedLadder a f z d) r p := by
  refine ⟨isAlicePath_bobCappedLadder a f z (le_of_eq hlen), ?_, by omega⟩
  rw [descend_bobCappedLadder a f z (le_of_eq hlen), hlen]
  simp [bobCappedLadder, IsBobNode]

/-- **Statement pole for `bobCols_of_isAlicePath`.**  The hypothesis is
load-bearing: at a genuine Bob query with a nonconstant predicate the node's
column set is *not* everything, so "no Bob query has occurred" is doing real work
and the lemma is not a tautology about `bobCols`. -/
theorem bobCols_pole_at_bob_query {Y : Type*} [Fintype Y] [DecidableEq Y]
    (a : X → Bool) (f : Y → Bool) (z : Z) {y : Y} (hy : f y = true) :
    y ∉ bobCols (bobCappedLadder (X := X) a f z 0) [false] := by
  simp [bobCols, bobConstraint, bobCappedLadder, hy]

/-- **Statement pole for `card_bobCols_children_add`.**  The `IsBobNode`
hypothesis is load-bearing, not decoration: at an *Alice* query both children
inherit the whole parent column set, so the two shares sum to twice the parent's
and the exact mass balance fails. -/
theorem bobCols_children_add_pole_at_alice :
    (Finset.univ ∩ bobCols
        (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1) ([] ++ [false])).card
      + (Finset.univ ∩ bobCols
        (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1) ([] ++ [true])).card
      ≠ (Finset.univ ∩ bobCols
        (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1) []).card := by
  decide

/-- **Statement pole for `exists_denser_bob_child`.**  No fixed bit is a witness:
at a Bob query whose predicate sends every column to the `true` child, the bound
at `false` is `2 <= 0` and fails.  The existential is therefore doing real work,
and the frozen "*the* denser Bob child" of `09:1290` names a genuine choice. -/
theorem denserChild_needs_the_right_bit :
    ¬ ((Finset.univ ∩ bobCols
        (bobCappedLadder (X := Bool) (fun _ => true) (fun _ : Bool => true) true 0) []).card
      ≤ 2 * (Finset.univ ∩ bobCols
        (bobCappedLadder (X := Bool) (fun _ => true) (fun _ : Bool => true) true 0)
        ([] ++ [false])).card) := by
  decide

/-- **Aux L6.**  Distinct addresses of equal length are never prefixes of one
another, so any equal-length family of addresses is prefix-free (`09:1259`). -/
theorem prefixFree_of_length_eq {V : Type*} (node : V → List Bool) (n : ℕ)
    (hlen : ∀ v, (node v).length = n) (hinj : ∀ v w, node v = node w → v = w) :
    PrefixFreeFrontier node := by
  intro v w hvw hpre
  exact hvw (hinj v w (hpre.eq_of_length (by rw [hlen, hlen])))

/-- The address of a depth-`n` frontier node, read off a Boolean tuple. -/
def tupleRoute {n : ℕ} (v : Fin n → Bool) : List Bool := List.ofFn v

/-- **Aux L7.** -/
@[simp] theorem tupleRoute_length {n : ℕ} (v : Fin n → Bool) :
    (tupleRoute v).length = n := by simp [tupleRoute]

/-- **Aux L8.** -/
theorem tupleRoute_injective {n : ℕ} {v w : Fin n → Bool} (h : tupleRoute v = tupleRoute w) :
    v = w := by
  funext i
  have hget := congrArg (fun l => l[i.1]?) h
  simpa [tupleRoute, List.getElem?_ofFn, i.2] using hget

/-- **The all-final frame-legal system (the frozen `e_0 = 0` shape).**

Every branch is stopped by the second rule -- after `r` Alice queries -- and
carries one clean certificate holding the frozen `A_0 = refRowFloor A0 0`
reference rows, which is exactly what `09:1324--1329` says a certificate holds at
a final node ("At a final node `d_v = r`, so each certificate contains at least
`A_0` rows of its copy of `G`").  Every value is evaluated through the frozen
definitional chain; none is assigned.

**NON-FIDELITY label.**  This is not the paper's own routed system: the paper
routes the *alleged* protocol, whose routing dynamics are GAP-EXPOSED item 1.
The deferred canonical-inhabitation obligation stays open. -/
def ladderSystem (a : X → Bool) (z : Z) (r A0 : ℕ) :
    RoutedSystem (aliceLadder (X := X) (Y := Y) a z r) (Fin r → Bool) (Fin r → Bool)
      (Fin r → Bool) r A0 where
  node := tupleRoute
  prefixFree := prefixFree_of_length_eq _ r (fun v => tupleRoute_length v)
    (fun _ _ h => tupleRoute_injective h)
  firstBob := fun _ => false
  firstBob_spec := fun v h => by exact absurd h (by simp)
  final_spec := fun v _ =>
    ⟨isAlicePath_aliceLadder a z (le_of_eq (tupleRoute_length v)), tupleRoute_length v⟩
  place := id
  cert := fun v =>
    { coord := v
      route := tupleRoute v
      kind := CertKind.clean
      rows := refRowFloor A0 0
      route_alice := isAlicePath_aliceLadder a z (le_of_eq (tupleRoute_length v))
      route_len_le := le_of_eq (tupleRoute_length v)
      rows_floor := by rw [tupleRoute_length]; simp }
  cert_at := fun _ => rfl
  coordUnique := fun _ _ h _ => h

/-- **Non-vacuity of `RoutedSystem` at the all-final shape.**  At every legal
width the system has `2^r` frontier nodes, each of capacity one (`09:1252`), each
carrying a clean certificate with the frozen `A_0` rows, and Kraft is *tight*:
`sum_v kappa_v = 2^r = q`, the frozen `eq:wrapper-frontier-conservation` second
clause at equality.  Nothing here is degenerate or cardinality-contradictory. -/
theorem ladderSystem_nondegenerate (a : X → Bool) (z : Z) (r A0 : ℕ) (v : Fin r → Bool) :
    ((ladderSystem (X := X) (Y := Y) a z r A0).cert v).kind = CertKind.clean ∧
      ((ladderSystem (X := X) (Y := Y) a z r A0).cert v).rows = A0 ∧
      stoppingCapacity r ((ladderSystem (X := X) (Y := Y) a z r A0).node v).length = 1 := by
  refine ⟨rfl, by simp [ladderSystem, refRowFloor], ?_⟩
  simp [ladderSystem, stoppingCapacity]

/-- **Kraft is tight on the all-final system.**  `sum_v kappa_v = 2^r`, so the
banked `sum_capacity_le_width` is met with equality: the frozen conservation
bound of `09:1264` is achieved, not merely satisfiable. -/
theorem ladderSystem_kraft_tight (a : X → Bool) (z : Z) (r A0 : ℕ) :
    ∑ v : Fin r → Bool,
        stoppingCapacity r ((ladderSystem (X := X) (Y := Y) a z r A0).node v).length
      = 2 ^ r := by
  have hone : ∀ v : Fin r → Bool,
      stoppingCapacity r ((ladderSystem (X := X) (Y := Y) a z r A0).node v).length = 1 :=
    fun v => (ladderSystem_nondegenerate (X := X) (Y := Y) a z r A0 v).2.2
  rw [Finset.sum_congr rfl (fun v _ => hone v)]
  simp [Finset.card_univ]

/-- **Hypothesis consistency for `owner_injOn_of_ladder`.**

The theorem's full hypothesis bundle -- `3 <= C`, the frozen frame cost bound
`cost(P) <= C+r-1`, the residual-cost bound, and the ladder call -- is
**jointly satisfiable at legal parameters**: it is met at the all-final
frame-legal system for every `C >= 3`, every wrapper width `r` and every initial
row floor `A0`, with `residual = 0`, and the conclusion follows rather than
`False`.  So the statement is not vacuous through contradictory hypotheses.

The instance is honest about what it does *not* show: at this system the owner
map is the identity, so the conclusion is cheap there.  Its purpose is the
consistency check, not a claim that the frozen counting is discharged.

**Scope (GAP-EXPOSED item 8).**  Because the owner map is injective here, no pair
`(i, j)` with `owner i = owner j` and `coord i /= coord j` exists, so the
`hladder` obligation is discharged *vacuously* (by `absurd`) and neither
`hladder` nor `hresidual` is exercised at a live pair.  The next round owes a
probe with `iota` strictly larger than `V` -- two certificates at one final node,
distinct `coord` -- in which the budget contradiction is the operative step. -/
theorem ladderSystem_owner_injOn (a : X → Bool) (z : Z) {r C : ℕ} (hC : 3 ≤ C) (A0 : ℕ) :
    ∀ i ∈ (ladderSystem (X := X) (Y := Y) a z r A0).cleanFinal,
      ∀ j ∈ (ladderSystem (X := X) (Y := Y) a z r A0).cleanFinal,
      (ladderSystem (X := X) (Y := Y) a z r A0).owner i
        = (ladderSystem (X := X) (Y := Y) a z r A0).owner j → i = j := by
  refine (ladderSystem (X := X) (Y := Y) a z r A0).owner_injOn_of_ladder (C := C) hC
    (aliceLadder_cost_le_frame a z (by omega)) (fun _ _ => 0) (fun _ _ => Nat.zero_le _)
    ?_
  intro i _ j _ hij hcoord
  exact absurd hij (fun h => hcoord (congrArg id h))

/-- **The all-first-Bob frame-legal system (the frozen early-stopping shape).**

Every branch is stopped by the *first* rule, at a Bob query at depth `d < r`, so
the `firstBob` branch of `RoutedSystem` is inhabited at legal parameters and the
frozen `kappa_v >= 2` of `09:1259` is live rather than vacuous.  Certificates
hold the frozen `A_{r-d}` rows at remaining selector capacity `2^{r-d}`,
evaluated through the banked `refRowFloor`.

**NON-FIDELITY label** as above. -/
def earlySystem (a : X → Bool) (f : Y → Bool) (z : Z) {r d : ℕ} (hd : d < r) (A0 : ℕ) :
    RoutedSystem (bobCappedLadder a f z d) (Fin d → Bool) (Fin d → Bool)
      (Fin d → Bool) r A0 where
  node := tupleRoute
  prefixFree := prefixFree_of_length_eq _ d (fun v => tupleRoute_length v)
    (fun _ _ h => tupleRoute_injective h)
  firstBob := fun _ => true
  firstBob_spec := fun v _ =>
    isFirstBobNode_bobCappedLadder a f z (tupleRoute_length v) hd
  final_spec := fun v h => by exact absurd h (by simp)
  place := id
  cert := fun v =>
    { coord := v
      route := tupleRoute v
      kind := CertKind.clean
      rows := refRowFloor A0 (r - d)
      route_alice := isAlicePath_bobCappedLadder a f z (le_of_eq (tupleRoute_length v))
      route_len_le := by rw [tupleRoute_length]; omega
      rows_floor := by rw [tupleRoute_length] }
  cert_at := fun _ => rfl
  coordUnique := fun _ _ h _ => h

/-- **Non-vacuity of the first-Bob branch (`09:1259`).**  Every node of the early
system is an exposed first-Bob node with the frozen `kappa_v = 2^{r-d} >= 2`, so
`IsFirstBobNode` is inhabited at legal parameters and the frozen "Every first-Bob
node has `kappa_v >= 2`" is a statement about a nonempty class. -/
theorem earlySystem_firstBob_capacity (a : X → Bool) (f : Y → Bool) (z : Z)
    {r d : ℕ} (hd : d < r) (A0 : ℕ) (v : Fin d → Bool) :
    (earlySystem (X := X) a f z hd A0).firstBob v = true ∧
      2 ≤ stoppingCapacity r ((earlySystem (X := X) a f z hd A0).node v).length := by
  refine ⟨rfl, ?_⟩
  exact two_le_stoppingCapacity_firstBob
    ((earlySystem (X := X) a f z hd A0).firstBob_spec v rfl)

/-- **The two systems really differ.**  The early system's certificates hold
strictly more rows than the final system's whenever the initial floor is
positive, because their remaining selector capacity is larger: the frozen
`A_k = 2^k A_0` is not a constant, and the two frontier shapes are not the same
object under a relabelling. -/
theorem earlySystem_rows_gt_final (a : X → Bool) (f : Y → Bool) (z : Z)
    {r d : ℕ} (hd : d < r) {A0 : ℕ} (hA0 : 1 ≤ A0) (v : Fin d → Bool) :
    A0 < ((earlySystem (X := X) a f z hd A0).cert v).rows := by
  have hpos : 0 < r - d := by omega
  have h2 : 2 ≤ 2 ^ (r - d) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - d) := Nat.pow_le_pow_right (by norm_num) hpos
  have : A0 < 2 ^ (r - d) * A0 := by nlinarith
  simpa [earlySystem, refRowFloor] using this

end Inhabitants

end EthInapproximability.ParameterizedNP.RoutedCertificateSystem
