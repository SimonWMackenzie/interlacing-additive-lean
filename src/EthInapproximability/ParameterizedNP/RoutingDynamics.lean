import EthInapproximability.ParameterizedNP.RoutedCertificateSystem

/-!
# Parameterized NP route: the routing dynamics of the routed certificate system

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8a54aaa6f0e60eaeb31ac1719cd696b169d5a845381fbd810a18a86c6b2a24e5`),
  the **routing layer** of the per-member shallow-protocol refutation engine:
  the frozen paragraph `09:1236--1248` (the certificate, its rows, the halving
  routing rule and the clean/low kinds), the stopping rules of `09:1250--1252`,
  and the denser-Bob-child projection sentence of `09:1287--1290`.
* **The exact frozen lines traced here**, in print order:
  * `09:1233--1236`, the initial placement: "that coordinate would therefore
    retain at least `A_r = q A_0` reference rows.  Start one clean reference
    certificate in every coordinate outside `E_0`, each with weight one."
  * `09:1238--1244`, the routing rule: "At remaining selector capacity `2^k`, a
    certificate consists of at least `A_k` reference rows in one outer
    coordinate.  At an Alice query, route it to a child containing at least
    `ceil(A_k/2) >= A_{k-1}` of those rows; route it to both children if both
    qualify."
  * `09:1244--1248`, the kind transition: "A clean certificate routed uniquely
    stays clean with weight one.  When a clean certificate splits, both
    descendants become low certificates of weight `1/2`.  A low certificate
    keeps weight `1/2`, whether it has one or two qualifying children.  Thus
    total certificate weight never decreases."
  * `09:1195--1200`, the completed-protocol frame condition of
    `lem:wrapper-no-bob-completion`, and `09:1250--1252`, the two stopping
    rules, which together decide **where** a routed branch stops.
  * `09:1287--1290`, the denser Bob child: "Every represented coordinate is
    outside `E_0`, so the parent projection to any selected `u_{kappa_v}` of
    them has density at least `rho = 2y^2`.  The denser Bob child retains
    density at least `y^2`."
  * `09:1315--1344`, `lem:final-reference-uniqueness` and its proof, whose
    `lem:certified-row-ladder` call and suffix-budget contradiction are
    exercised below at a live owner pair.
* **Cross-anchors opened first-hand for this tranche:** `09:1180--1232` (the
  contradiction frame, the completion lemma and `A_k = 2^k A_0`), `09:1250--1266`
  (`d_v`, `kappa_v`, `eq:wrapper-frontier-conservation`), `09:1268--1313` (the
  first-Bob closing argument and `eq:wrapper-first-bob-light`), `09:1346--1365`
  (`eq:wrapper-clean-count`).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the only import is
  `RoutedCertificateSystem`, whose ledger row records the same exclusion.
* **Proof status.**  Every declaration is a transcription of a frozen display of
  the range above, a general property of one of those transcriptions, or one of
  the block's own derivations carried out in the kernel.  **No mathematics is
  added**, and no conclusion of `eq:wrapper-u-dense` is asserted anywhere.

## What this tranche closes in the banked module

`RoutedCertificateSystem.lean` (SHA-256
`B019BE34A74934390ABA184C5E5143DA6C53C7064AE0B9D2C5AF82502E3A73DF`) recorded
eight GAP-EXPOSED items.  This module discharges three of them and touches no
other:

* **Item 1 (the routing dynamics are not modelled), discharged.**  The banked
  prescription was, verbatim: "carry `rowsAt : List Bool -> Finset Row` with the
  frozen halving law `refRowFloor_ceil_half` (already banked) as the transition,
  and derive the kind transition from it."  That is what `rowsAt`, `routeBit`,
  `splitsAt` and `kindAlong` do: the certificate's rows at a node are the
  *derived* set `R inter aliceCols P p`, the routing bit is *computed* from the
  frozen floor `A_{k-1}`, and the certificate's kind is a *function* of the
  route rather than free constructor data.  The three frozen sentences of
  `09:1245--1247` are then theorems
  (`step_kind_of_not_split`, `step_kind_of_split`, `kind_low_of_kind_low`), and
  the banked `CertKind.routeOut` is proved to be exactly the list of descendant
  kinds the dynamics produce (`split_children_kinds`, `unique_child_kinds`).
* **Item 7 (the projection form of the denser-child halving), discharged.**  The
  banked prescription was, verbatim: "land `card_projSet_children_le`,
  `|projSet J (A union B)| <= |projSet J A| + |projSet J B|`, applied to
  `bobCols_children_union`."  That is `card_projSet_union_le` and
  `card_nodeProjection_children_le`, from which
  `exists_denser_bob_child_projection` and the density form
  `exists_denser_bob_child_density` follow; `denserBobChild_retains_y_sq` is the
  frozen `rho = 2y^2 -> y^2` sentence verbatim.  **The banked prohibition on
  citing `exists_denser_bob_child` for `09:1287--1290` is discharged by the
  projection theorems of §5**: a new module cannot lift a banked module's
  prohibition, and what is true is that those theorems now discharge
  `09:1287--1290` while the banked column-set theorem remains a column-set
  theorem.
* **Item 8 (the ladder binder is not exercised at a live pair), discharged.**
  `twinSystem` is a frame-legal `RoutedSystem` with `iota` strictly larger than
  `V` -- two certificates at one final node with distinct `coord` --
  `twinSystem_live_pair` exhibits the pair, and `twinSystem_ladder_refuted` runs
  the frozen `09:1321--1343` argument on it: `hladder` and `hresidual` fire at
  that pair and the suffix-budget contradiction is the operative step.

Items 2, 3, 4, 5 and **6** are untouched.  In particular **`hDenseRung` is
neither discharged nor fed**, `eq:wrapper-u-dense` is asserted nowhere below,
and **no route completion is claimed.**  The `lem:certified-row-ladder` call of
`09:1334--1338` remains the named binder pair `(hresidual, hladder)` of the
banked `owner_injOn_of_ladder`: it is used, never proved.

**"Discharged" above means the banked prescription is met in full, not that the
frozen block is closed.**  Item 1's own text names a consequence that this module
does *not* deliver, and the two new openings below are exactly that residue.

## GAP-EXPOSED, newly recorded by this module

9. **The frontier is constructed only *per certificate*** (`09:1250--1259`).
   `routeFuel_stops` gives each initial coordinate a stopping address, but the
   simultaneous indexing of all of them by a single `V` is not landed here.
10. **`eq:wrapper-frontier-conservation`'s first clause** (`09:1259--1266`).
    `sum_v W_v >= q - e_0` still enters the banked counting as a binder, because
    summing the now-derived weights over the frontier needs (9).

### Successor record (comment-only; nothing above is restated or weakened)

Items (9) and (10) are discharged by
`EthInapproximability.ParameterizedNP.FrontierIndexing` (tranche `cc-t4e`).  Two
points of that module bear on how the text above should be read, and neither
edits anything here:

* The frozen rule of `09:1244` also routes "to both children if both qualify",
  and `routeFuel` below follows only the single `routeBit` child.  That is
  sufficient for the stopping dichotomy proved here, but **not** for `09:1248`
  summed over the frontier: at a genuine split the single tracked branch carries
  weight `1/2` where the frozen rule carries `1/2 + 1/2`.  The successor module
  therefore builds the branching family and proves `routeFuel`'s address is
  always one of its addresses; `routeFuel` is a correct *trace* of the frozen
  rule, never a replacement for it.
* The `RoutedSystem` canonical-inhabitation obligation narrowed to (9) below is
  discharged there at the paper's own inputs.  `twinSystem` keeps its
  **NON-FIDELITY** label and the five parameter probes keep their
  **BEYOND-PAPER** labels.

## Predecessor modules consumed **by pin**, never restated

* `Workspace.Types.Protocol` (through `LegacyNPCC.Core`, project-axiom-free):
  `Protocol`, `Protocol.cost`.
* `EthInapproximability.ParameterizedNP.DenseWeightedCount`: `descendStep`,
  `descend`, `IsQueryNode`, `IsBobNode`, `IsQueryPath`, `stoppingCapacity`,
  `PrefixFreeFrontier`.
* `EthInapproximability.ParameterizedNP.DenseSynchronisation`: `IsANode`.
* `EthInapproximability.ParameterizedNP.DenseWrapperFrontier`: `refRowFloor`
  (the frozen `A_k = 2^k A_0`), `refRowFloor_ceil_half` (the frozen
  `ceil(A_k/2) >= A_{k-1}`, banked as an identity), `routedChild_rows_ge`,
  `CertKind` with `CertKind.weight`, `CertKind.routeOut`,
  `CertKind.weight_le_totalRouteWeight`.
* `EthInapproximability.ParameterizedNP.WrapperProjectionCovers`: `projSet`.
* `EthInapproximability.ParameterizedNP.RoutedCertificateSystem`: `IsAlicePath`,
  `IsFirstBobNode`, `IsFinalAliceNode`, `aliceCols`, `aliceConstraint`,
  `bobCols`, `retainedCols`, `nodeProjection`, `bobCols_children_union`,
  `RoutedCertificate`, `RoutedSystem`, `owner_injOn_of_ladder`, `aliceLadder`
  and its frame lemmas, `tupleRoute`, `prefixFree_of_length_eq`.

## Canonical inhabitation

* **`RoutedRowCertificate`: the paper's own instance inhabits it.**
  `09:1235--1236` constructs one object -- "Start one clean reference
  certificate in every coordinate outside `E_0`, each with weight one" -- resting
  on the retention `A_r = q A_0` of `09:1233--1235`.  `initialRowCertificate` is
  exactly that object: its route is the root, its row set is the coordinate's
  reference rows, its floor hypothesis is the frozen retention statement, and
  its kind and weight are **computed** to be `clean` and `1` rather than
  assigned (`initialRowCertificate_kind`, `initialRowCertificate_weight`).  The
  legality of the floor hypothesis at nondegenerate parameters is witnessed by
  `initialRowCertificate_hypothesis_legal`.
* **`RoutedSystem`: the deferred obligation registered by the banked module
  stays open, with its named unblocker now landed.**  The frozen frame
  quantifies over an *arbitrary* alleged protocol, so the canonical system is
  the routing of the paper's completed protocol.  What this module adds is the
  routing itself: `routeFuel` iterates the frozen rule, and `routeFuel_stops`
  proves that under the frame condition of `lem:wrapper-no-bob-completion` every
  routed branch stops at one of the two frozen addresses -- so the *addresses*
  of the canonical system are now constructed, and only the indexing of the
  frontier by those addresses remains.  `prefixFree_of_stopping` supplies the
  remaining structural law from the addresses alone, and
  `initial_stopAt_firstBob` runs the whole chain -- the frozen initial placement,
  the frozen routing rule, the frozen stopping rule -- end to end on a protocol
  that meets the completion frame condition.  The obligation is **narrowed and
  still registered**, not silently satisfied: what is still missing is the
  indexing of the frontier by the stopping addresses of *all* initial
  coordinates at once.
* `twinSystem` is a **counterfactual** probe, labelled NON-FIDELITY in its
  docstring: it is the configuration `lem:final-reference-uniqueness` refutes,
  built in order to make the refutation operative.

## Aux-lemma battery and statement poles

Every new object carries general identity, composition, monotonicity and
round-trip properties, all proved: `rowsAt_nil`, `rowsAt_cons` (the walk law),
`rowsAt_subset`, `rowsAt_mono`, `rowsAt_children_union`,
`rowsAt_children_disjoint`, `card_rowsAt_children_add`; `splitsAt_eq_true_iff`,
`splitBefore_nil`, `splitBefore_append_bit`, `kindAlong_nil`,
`kindAlong_append_bit`, `kindAlong_low_of_low`, `kindAlong_clean_of_clean`;
`RoutedRowCertificate.one_le_capacity`, `.capacity_mul_initial_le_rows`,
`.rows_nonempty`, `.rows_subset_refRows`, `.step_route`, `.step_refRows`,
`.step_depth`, and the three bridge round-trips `toRoutedCertificate_route`,
`_kind`, `_rows`; `routeFuel_zero`, `routeFuel_of_stopped`,
`isANodeB_eq_true_iff`, `isBobNode_of_not_isANode`,
`isANode_take_of_isAlicePath`, `isAlicePath_bobCappedLadder_length_le`;
`projSet_union`, `card_projSet_union_le`, `retainedCols_children_union`.

Three **statement poles** show the load-bearing hypotheses bite:
`denserAliceChild_needs_the_right_bit` (no fixed bit routes the rows),
`projection_denserChild_needs_the_right_bit` (the same in the projection form of
`09:1287--1290`), and `twinSystem_owner_not_injective` (the `RoutedSystem` laws
alone, coordinate uniqueness included, do **not** give owner injectivity -- so the
ladder binder of `owner_injOn_of_ladder` is doing the work).

Neither branch of any new dichotomy is vacuous: `splitsAt_probe_true` /
`splitsAt_probe_false` and `kindAlong_probe_low` / `kindAlong_probe_clean` reach
both derived kinds (labelled **BEYOND-PAPER**, since the paper fixes no alphabet
or width there), while `aliceLadder_stopAt_final` and
`bobCappedLadder_stopAt_firstBob` reach both frozen stopping addresses at
protocols the paper's own completion lemma describes, with
`completedNoBob_aliceLadder` and `completedNoBob_bobCappedLadder` showing the
frame hypothesis is satisfiable.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for
this tranche (`denser`, `routing`, `clean certificate`, `reference certificate`,
`selector capacity`, `half-weight`).  The only hits are
`B-bridge-details.tex:146` and `:163` ("If Bob speaks, keep a denser child and
maximum-project to two copies", "If Bob speaks, the denser child has defect at
most ...") and `A-stage4-details.tex:259`, `02-preliminaries.tex:563`
("quotient-support routing").  None is a counterpart: the two `B-bridge-details`
sentences are the **direct bridge** induction of Section 10, not the wrapper's
first-Bob frontier, and the two "routing" hits are Stage-4 quotient-support
routing, a different mechanism.  **No reader item is claimed**, and the absence
is a finding about the reader artifact rather than an omission here.
-/

namespace EthInapproximability.ParameterizedNP.RoutingDynamics

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem

/-! ## §1  The reference rows a certificate holds at a node (`09:1238--1244`)

"At remaining selector capacity `2^k`, a certificate consists of at least `A_k`
reference rows in one outer coordinate.  At an Alice query, route it to a child
containing at least `ceil(A_k/2) >= A_{k-1}` of those rows."

The rows a certificate holds at a node are **not** free data: they are the
certificate's initial reference rows cut by Alice's answers along the route, so
`rowsAt` is the Alice-side dual of the banked `retainedCols`.  Everything the
frozen routing rule says about rows is then a theorem about `aliceCols`. -/

section Rows

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- **Aux A1 (an Alice query splits Alice's rows, it does not delete them).**  At
an Alice node the two answer bits cover every row.  General. -/
theorem aliceConstraint_union {P : Protocol X Y Z} (h : IsANode P) :
    aliceConstraint P false ∪ aliceConstraint P true = (Finset.univ : Finset X) := by
  obtain ⟨a, l, rr, rfl⟩ := h
  ext x
  simp only [aliceConstraint, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, iff_true]
  cases a x <;> simp

omit [DecidableEq X] in
/-- **Aux A2 (the split is a partition).**  The two Alice children of an Alice
query are disjoint on rows: Alice's answer bit partitions her inputs, so the
frozen "route it to a child containing at least `ceil(A_k/2)`" is a choice
between two disjoint halves.  General. -/
theorem aliceConstraint_disjoint {P : Protocol X Y Z} (h : IsANode P) :
    Disjoint (aliceConstraint P false) (aliceConstraint P true) := by
  obtain ⟨a, l, rr, rfl⟩ := h
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  simp only [aliceConstraint, Finset.mem_filter] at hx hx'
  rw [hx.2] at hx'
  exact Bool.noConfusion hx'.2

/-- **Aux A3.**  The two Alice children of the node at `p` partition that node's
surviving row set.  Dual of the banked `bobCols_children_union`.  General. -/
theorem aliceCols_children_union : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsANode (descend P p) →
      aliceCols P (p ++ [false]) ∪ aliceCols P (p ++ [true]) = aliceCols P p := by
  intro P p
  induction p generalizing P with
  | nil =>
      intro h
      simp only [List.nil_append, aliceCols_cons, aliceCols_nil, Finset.inter_univ]
      exact aliceConstraint_union (by simpa using h)
  | cons c p ih =>
      intro h
      have hstep : IsANode (descend (descendStep P c) p) := by
        simpa [descend_cons] using h
      simp only [List.cons_append, aliceCols_cons]
      rw [← Finset.inter_union_distrib_left, ih hstep]

/-- **Aux A4.**  The same split is disjoint.  General. -/
theorem aliceCols_children_disjoint : ∀ {P : Protocol X Y Z} {p : List Bool},
    IsANode (descend P p) →
      Disjoint (aliceCols P (p ++ [false])) (aliceCols P (p ++ [true])) := by
  intro P p
  induction p generalizing P with
  | nil =>
      intro h
      simp only [List.nil_append, aliceCols_cons, aliceCols_nil, Finset.inter_univ]
      exact aliceConstraint_disjoint (by simpa using h)
  | cons c p ih =>
      intro h
      have hstep : IsANode (descend (descendStep P c) p) := by
        simpa [descend_cons] using h
      have hdisj := ih hstep
      simp only [List.cons_append, aliceCols_cons]
      refine Finset.disjoint_left.mpr fun x hx hx' => ?_
      rw [Finset.mem_inter] at hx hx'
      exact (Finset.disjoint_left.mp hdisj hx.2) hx'.2

/-- **`09:1238--1240`, the rows a certificate holds at a node.**

"a certificate consists of at least `A_k` reference rows in one outer
coordinate": the rows it *holds at the node reached by `p`* are its initial
reference rows `R` cut by Alice's answers along `p`.  This is the Alice-side dual
of the banked `RoutedCertificateSystem.retainedCols`, and it is the object the
banked `RoutedCertificate.rows` counted without naming. -/
def rowsAt (P : Protocol X Y Z) (R : Finset X) (p : List Bool) : Finset X :=
  R ∩ aliceCols P p

/-- **Aux A5.**  At the root the certificate holds all of its reference rows.
General. -/
@[simp] theorem rowsAt_nil (P : Protocol X Y Z) (R : Finset X) :
    rowsAt P R ([] : List Bool) = R := by
  simp [rowsAt]

/-- **Aux A6 (the routing is a walk).**  One step of the route consumes one
Alice answer: routing `R` from `P` along `b :: p` is routing `R` cut by `b` from
the child.  General; this is the round-trip law that makes `rowsAt` a genuine
dynamics rather than a static intersection. -/
theorem rowsAt_cons (P : Protocol X Y Z) (R : Finset X) (b : Bool) (p : List Bool) :
    rowsAt P R (b :: p) = rowsAt (descendStep P b) (R ∩ aliceConstraint P b) p := by
  simp [rowsAt, aliceCols_cons, Finset.inter_assoc]

/-- **Aux A7 (monotonicity: rows are only lost).**  General. -/
theorem rowsAt_subset (P : Protocol X Y Z) (R : Finset X) (p : List Bool) :
    rowsAt P R p ⊆ R := Finset.inter_subset_left

/-- **Aux A8 (monotonicity in the reference set).**  General. -/
theorem rowsAt_mono {P : Protocol X Y Z} {R R' : Finset X} (h : R ⊆ R') (p : List Bool) :
    rowsAt P R p ⊆ rowsAt P R' p := Finset.inter_subset_inter h (Finset.Subset.refl _)

/-- **`09:1239--1244`, the row split at an Alice query.**  The two children of an
Alice node partition the rows the certificate holds there. -/
theorem rowsAt_children_union {P : Protocol X Y Z} {R : Finset X} {p : List Bool}
    (h : IsANode (descend P p)) :
    rowsAt P R (p ++ [false]) ∪ rowsAt P R (p ++ [true]) = rowsAt P R p := by
  simp only [rowsAt, ← Finset.inter_union_distrib_left, aliceCols_children_union h]

/-- **`09:1239--1244`, disjointness of the split.** -/
theorem rowsAt_children_disjoint {P : Protocol X Y Z} {R : Finset X} {p : List Bool}
    (h : IsANode (descend P p)) :
    Disjoint (rowsAt P R (p ++ [false])) (rowsAt P R (p ++ [true])) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (aliceCols_children_disjoint h))

/-- **The exact row balance at an Alice query.**  The two children's row counts
sum to the parent's, which is what makes "at least `ceil(A_k/2)`" attainable. -/
theorem card_rowsAt_children_add {P : Protocol X Y Z} {R : Finset X} {p : List Bool}
    (h : IsANode (descend P p)) :
    (rowsAt P R (p ++ [false])).card + (rowsAt P R (p ++ [true])).card
      = (rowsAt P R p).card := by
  rw [← Finset.card_union_of_disjoint (rowsAt_children_disjoint (R := R) h),
    rowsAt_children_union h]

/-- **`09:1239--1244`, the frozen halving law, in its row form.**

"At an Alice query, route it to a child containing at least `ceil(A_k/2)` of
those rows."  Such a child exists: the two children's counts sum to the parent's,
so the larger one holds at least `ceil(n/2) = (n+1)/2`.

*Why no fixed bit works.*  The existential really quantifies -- an Alice
predicate may send every row to one child; `denserAliceChild_needs_the_right_bit`
exhibits a query at which `false` fails the bound outright. -/
theorem exists_denser_alice_child {P : Protocol X Y Z} {R : Finset X} {p : List Bool}
    (h : IsANode (descend P p)) :
    ∃ b : Bool, ((rowsAt P R p).card + 1) / 2 ≤ (rowsAt P R (p ++ [b])).card := by
  have hadd := card_rowsAt_children_add (R := R) h
  rcases le_total (rowsAt P R (p ++ [false])).card (rowsAt P R (p ++ [true])).card with hle | hle
  · exact ⟨true, by omega⟩
  · exact ⟨false, by omega⟩

/-- **`09:1240--1244`, the invariant restored one level down.**

"route it to a child containing at least `ceil(A_k/2) >= A_{k-1}` of those rows":
if the certificate meets the frozen floor `A_k` at the parent, some child meets
the frozen floor `A_{k-1}`.  The arithmetic is the banked `routedChild_rows_ge`,
consumed by pin; what is added here is that the child is a *node of the
protocol* and the rows are the *derived* `rowsAt`. -/
theorem exists_routed_child_floor {P : Protocol X Y Z} {R : Finset X} {A0 k : ℕ}
    {p : List Bool} (h : IsANode (descend P p)) (hk : 1 ≤ k)
    (hrows : refRowFloor A0 k ≤ (rowsAt P R p).card) :
    ∃ b : Bool, refRowFloor A0 (k - 1) ≤ (rowsAt P R (p ++ [b])).card := by
  obtain ⟨b, hb⟩ := exists_denser_alice_child (R := R) h
  exact ⟨b, routedChild_rows_ge hk hrows hb⟩

end Rows

/-! ## §2  The routing decision and the derived kind (`09:1244--1248`)

"route it to both children if both qualify.  A clean certificate routed uniquely
stays clean with weight one.  When a clean certificate splits, both descendants
become low certificates of weight `1/2`.  A low certificate keeps weight `1/2`,
whether it has one or two qualifying children."

The qualification threshold is the frozen `ceil(A_k/2)`, which the banked
`refRowFloor_ceil_half` records as the *identity* `ceil(A_k/2) = A_{k-1}`; so
"qualifies" is "meets the floor `A_{k-1}`", and the kind of a certificate is a
**function** of its route, not free data. -/

section Decision

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- **`09:1242`, the qualification threshold at a node of depth `d`.**  The
remaining selector capacity there is `2^k` with `k = r - d`, so a child qualifies
when it holds at least `ceil(A_k/2) = A_{k-1} = refRowFloor A0 (r - d - 1)`
rows.  The identity `ceil(A_k/2) = A_{k-1}` is the banked
`refRowFloor_ceil_half`; nothing is assigned.

**The threshold is the frozen one, read at its defining display.**  `09:1242`
demands `ceil(A_k/2)` of the certificate's rows, with `A_k` the *floor* of
`09:1238--1239`, and records `ceil(A_k/2) >= A_{k-1}`.  Because `A_k = 2A_{k-1}`
is even, the banked `refRowFloor_ceil_half` proves the frozen inequality is an
identity, so `A_{k-1}` **is** the frozen demand and not a use-site weakening of
it.

**On the truncation at `d = r`.**  In natural-number subtraction
`r - r - 1 = 0`, so at a final node this expression reads `A_0`.  That value is
never consumed: the frozen rule fires only at an Alice query strictly below the
`r`-th (`step` carries `hlt`), and `kindAlong` evaluates the split test only at
*proper* prefixes of a route of length at most `r`. -/
def childFloor (A0 r : ℕ) (p : List Bool) : ℕ := refRowFloor A0 (r - p.length - 1)

/-- **`09:1240--1244`.**  "route it to a child containing at least
`ceil(A_k/2) >= A_{k-1}` of those rows": the child along `b` *qualifies*. -/
def Qualifies (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) (p : List Bool) (b : Bool) :
    Prop :=
  childFloor A0 r p ≤ (rowsAt P R (p ++ [b])).card

/-- Qualification is a decidable comparison of two natural numbers, so the frozen
routing decision is computable and the split test below is not a classical
choice. -/
instance decidableQualifies (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) (p : List Bool)
    (b : Bool) : Decidable (Qualifies P R A0 r p b) := by
  unfold Qualifies; infer_instance

/-- **`09:1244`.**  "route it to both children if both qualify": the certificate
*splits* at `p`. -/
def splitsAt (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) (p : List Bool) : Bool :=
  decide (Qualifies P R A0 r p false) && decide (Qualifies P R A0 r p true)

/-- **Aux B1.**  Reading of the split decision.  General. -/
theorem splitsAt_eq_true_iff {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ} {p : List Bool} :
    splitsAt P R A0 r p = true ↔
      (Qualifies P R A0 r p false ∧ Qualifies P R A0 r p true) := by
  simp [splitsAt]

/-- **Aux B2.**  A split certificate qualifies at `false`.  General. -/
theorem qualifies_false_of_splitsAt {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    {p : List Bool} (h : splitsAt P R A0 r p = true) : Qualifies P R A0 r p false :=
  (splitsAt_eq_true_iff.mp h).1

/-- **Aux B3.**  A split certificate qualifies at `true`.  General. -/
theorem qualifies_true_of_splitsAt {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    {p : List Bool} (h : splitsAt P R A0 r p = true) : Qualifies P R A0 r p true :=
  (splitsAt_eq_true_iff.mp h).2

/-- **`09:1240--1244`, the bit the frozen rule routes a *unique* descendant
along.**  "route it to a child containing at least `ceil(A_k/2)` of those rows":
take the `false` child when it qualifies, otherwise the `true` child.  When both
qualify the certificate splits instead and this bit is not consulted. -/
def routeBit (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) (p : List Bool) : Bool :=
  if Qualifies P R A0 r p false then false else true

/-- **`09:1239--1244`, the routing rule is well defined.**  At an Alice query
below the `r`-th, a certificate meeting the frozen floor `A_{r-d}` has a
qualifying child, and `routeBit` names one. -/
theorem routeBit_qualifies {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ} {p : List Bool}
    (h : IsANode (descend P p)) (hlt : p.length < r)
    (hrows : refRowFloor A0 (r - p.length) ≤ (rowsAt P R p).card) :
    Qualifies P R A0 r p (routeBit P R A0 r p) := by
  unfold routeBit
  by_cases hf : Qualifies P R A0 r p false
  · simp [hf]
  · have hk : 1 ≤ r - p.length := by omega
    obtain ⟨b, hb⟩ := exists_routed_child_floor (R := R) (A0 := A0) h hk hrows
    have hb' : Qualifies P R A0 r p b := hb
    cases b with
    | false => exact absurd hb' hf
    | true => simpa [hf] using hb'

/-- **`09:1245--1247`, the kind of a certificate, derived.**

"A clean certificate routed uniquely stays clean with weight one.  When a clean
certificate splits, both descendants become low certificates of weight `1/2`.  A
low certificate keeps weight `1/2`."

Unwinding the three sentences: a descendant at `p` is *low* exactly when some
strict ancestor of `p` split, and *clean* otherwise.  So the kind is a **function
of the route and the row dynamics**, which is the whole content of GAP-EXPOSED
item 1 of the banked module: the banked `RoutedCertificate.kind` was free
constructor data, and here it is computed. -/
def splitBefore (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) (p : List Bool) : Bool :=
  (List.range p.length).any fun n => splitsAt P R A0 r (p.take n)

/-- **`09:1236`, `09:1245--1247`, the derived kind.**  The banked
`DenseWrapperFrontier.CertKind` is consumed by pin; only the *assignment* of a
kind to a route is new. -/
def kindAlong (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) (p : List Bool) : CertKind :=
  if splitBefore P R A0 r p then CertKind.low else CertKind.clean

/-- **Aux B4.**  Nothing has split above the root.  General. -/
@[simp] theorem splitBefore_nil (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    splitBefore P R A0 r ([] : List Bool) = false := by
  simp [splitBefore]

/-- **`09:1235--1236`, evaluated.**  "Start one clean reference certificate in every
coordinate outside `E_0`": at the root the derived kind is `clean`. -/
@[simp] theorem kindAlong_nil (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    kindAlong P R A0 r ([] : List Bool) = CertKind.clean := by
  simp [kindAlong]

/-- **Aux B5 (one step of the split history).**  General; this is the recursion
that makes `splitBefore` a dynamics on routes. -/
theorem splitBefore_append_bit (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ)
    (p : List Bool) (b : Bool) :
    splitBefore P R A0 r (p ++ [b])
      = (splitBefore P R A0 r p || splitsAt P R A0 r p) := by
  have hlen : (p ++ [b]).length = p.length + 1 := by simp
  have hlast : (p ++ [b]).take p.length = p := by
    rw [List.take_append_of_le_length (le_refl _), List.take_length]
  have hhead : ((List.range p.length).any fun n => splitsAt P R A0 r ((p ++ [b]).take n))
      = ((List.range p.length).any fun n => splitsAt P R A0 r (p.take n)) := by
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨n, hn, hs⟩
      exact ⟨n, hn, by rwa [List.take_append_of_le_length hn.le] at hs⟩
    · rintro ⟨n, hn, hs⟩
      exact ⟨n, hn, by rwa [List.take_append_of_le_length hn.le]⟩
  unfold splitBefore
  rw [hlen, List.range_succ, List.any_append, hhead]
  simp [hlast]

/-- **`09:1244--1248`, the frozen kind transition, derived.**

The single theorem that carries all three frozen sentences: the kind of a
descendant one Alice query below `p` is `low` if the certificate split at `p`,
and otherwise the kind it already had.  Nothing here is postulated -- `splitsAt`
is computed from `rowsAt` and the frozen floor. -/
theorem kindAlong_append_bit (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ)
    (p : List Bool) (b : Bool) :
    kindAlong P R A0 r (p ++ [b])
      = if splitsAt P R A0 r p then CertKind.low else kindAlong P R A0 r p := by
  unfold kindAlong
  rw [splitBefore_append_bit]
  cases splitsAt P R A0 r p <;> cases splitBefore P R A0 r p <;> simp

/-- **`09:1247`, "A low certificate keeps weight `1/2`".**  Once low, always low:
no descendant of a split ever becomes clean again.  General. -/
theorem kindAlong_low_of_low {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    {p : List Bool} (h : kindAlong P R A0 r p = CertKind.low) (b : Bool) :
    kindAlong P R A0 r (p ++ [b]) = CertKind.low := by
  rw [kindAlong_append_bit]
  cases splitsAt P R A0 r p <;> simp [h]

/-- **`09:1245`, "A clean certificate routed uniquely stays clean".**  The
contrapositive form: a clean descendant has a clean ancestor.  General. -/
theorem kindAlong_clean_of_clean {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    {p : List Bool} {b : Bool} (h : kindAlong P R A0 r (p ++ [b]) = CertKind.clean) :
    kindAlong P R A0 r p = CertKind.clean := by
  unfold kindAlong at h ⊢
  rw [splitBefore_append_bit] at h
  cases hsb : splitBefore P R A0 r p with
  | false => simp
  | true => rw [hsb] at h; simp at h

/-- **Statement pole for `exists_denser_alice_child`.**  No fixed bit is a
witness: at an Alice query whose predicate sends every row to the `true` child,
the bound at `false` reads `2 <= 0` and fails.  So the frozen "route it to *a*
child containing at least `ceil(A_k/2)`" names a genuine choice, and the
existential is not decoration. -/
theorem denserAliceChild_needs_the_right_bit :
    ¬ (((rowsAt (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1)
            Finset.univ ([] : List Bool)).card + 1) / 2
        ≤ (rowsAt (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1)
            Finset.univ ([] ++ [false])).card) := by
  decide

/-- **BEYOND-PAPER audit probe (non-vacuity of the split branch).**

The frozen text never fixes an alphabet, a wrapper width or an initial row floor,
so the parameters here are **ours**, not the paper's: this instance audits *our*
encoding at a point the paper never visits, and is strictly weaker evidence than
the paper's own application point.  What it establishes is that the derived
`splitsAt` is not constantly `false`: at the Alice query that sends each of two
rows to a different child, with the frozen floor `A_0 = 1`, **both children
qualify** and the certificate splits.  Without this the `low` half of `09:1246`
would be unreachable and the derived kind would be a constant. -/
theorem splitsAt_probe_true :
    splitsAt (aliceLadder (X := Bool) (Y := Bool) (fun x => x) true 1)
      Finset.univ 1 1 ([] : List Bool) = true := by
  decide

/-- **BEYOND-PAPER audit probe (the `low` kind is reached by the dynamics).**
`09:1246`, "When a clean certificate splits, both descendants become low": at the
splitting query above, the descendant's derived kind really is `low`, so the
banked `CertKind.low` is *produced* by the routing and not merely nameable. -/
theorem kindAlong_probe_low :
    kindAlong (aliceLadder (X := Bool) (Y := Bool) (fun x => x) true 1)
      Finset.univ 1 1 [false] = CertKind.low := by
  decide

/-- **BEYOND-PAPER audit probe (non-vacuity of the unique-routing branch).**  At an
Alice query whose predicate sends both rows to the `true` child, the `false` child
holds no rows and fails the frozen floor, so the certificate does **not** split. -/
theorem splitsAt_probe_false :
    splitsAt (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1)
      Finset.univ 1 1 ([] : List Bool) = false := by
  decide

/-- **BEYOND-PAPER audit probe (`routeBit` follows the rows).**  At that same query
the frozen rule routes the certificate to the `true` child: `routeBit` is not a
constant, and it answers to the row counts. -/
theorem routeBit_probe_true :
    routeBit (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1)
      Finset.univ 1 1 ([] : List Bool) = true := by
  decide

/-- **BEYOND-PAPER audit probe (`09:1245`, "stays clean").**  A certificate routed
uniquely keeps the derived kind `clean`, so both kinds are reachable and the
derived kind separates the two frozen cases rather than collapsing them. -/
theorem kindAlong_probe_clean :
    kindAlong (aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1)
      Finset.univ 1 1 [true] = CertKind.clean := by
  decide

end Decision

/-! ## §3  The row-carrying routed certificate (`09:1236--1248`)

The banked `RoutedCertificate` carries a row *count* and a *free* kind.  The
frozen text determines both from the routing, and this section is that
refinement: the rows are `rowsAt`, the kind is `kindAlong`, and the bridge
`toRoutedCertificate` shows the refinement lands in the banked type, so every
banked consumer applies unchanged. -/

section Certificate

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- **`09:1236--1243`, the routed certificate with its rows.**

A certificate carries its outer coordinate, the reference rows it started with
in that coordinate, and the route it has followed.  Its three laws are the frozen
ones and no others: the route is Alice-only (`09:1250`), it has not outrun the
`r` Alice queries (`09:1250`), and at remaining selector capacity `2^k` it still
holds at least `A_k` of its reference rows (`09:1238--1239`), where the rows held
are the *derived* `rowsAt` and `A_k` is the banked `refRowFloor`.

**Deliberately not fields:** the kind and the row count.  Both are frozen
*consequences* of the routing (`kind`, `rows` below), and carrying them as data
is exactly the GAP-EXPOSED item 1 defect of the banked record.  No complexity or
robustness conclusion is constructor data (mechanical rules M1--M10). -/
structure RoutedRowCertificate (P : Protocol X Y Z) (Coord : Type*) (r A0 : ℕ) where
  /-- The outer coordinate the certificate descends from (`09:1236`). -/
  coord : Coord
  /-- The reference rows it started with in that coordinate (`09:1233--1236`). -/
  refRows : Finset X
  /-- The route followed below the root (`09:1238--1244`). -/
  route : List Bool
  /-- `09:1250`: the branch has not yet met a Bob query. -/
  route_alice : IsAlicePath P route
  /-- `09:1250`: it has not outrun the `r` Alice queries (the frozen clause "or
  after `r` Alice queries" is on line 1250; 1251 is the non-exposure sentence). -/
  route_len_le : route.length ≤ r
  /-- `09:1238--1239`: at remaining selector capacity `2^k` the certificate still
  holds at least `A_k` reference rows. -/
  rows_floor : refRowFloor A0 (r - route.length) ≤ (rowsAt P refRows route).card

namespace RoutedRowCertificate

variable {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}

/-- `09:1253`, `d_v`: the number of preceding Alice queries (`09:1254` is the
display opener). -/
def depth (c : RoutedRowCertificate P Coord r A0) : ℕ := c.route.length

/-- `09:1255`, `kappa_v = 2^{r - d_v}`, the banked `stoppingCapacity`. -/
def capacity (c : RoutedRowCertificate P Coord r A0) : ℕ := stoppingCapacity r c.depth

/-- **`09:1239`, derived.**  The reference rows the certificate holds now. -/
def rows (c : RoutedRowCertificate P Coord r A0) : Finset X := rowsAt P c.refRows c.route

/-- **`09:1245--1247`, derived.**  The certificate's kind, computed from the
routing rather than carried. -/
def kind (c : RoutedRowCertificate P Coord r A0) : CertKind :=
  kindAlong P c.refRows A0 r c.route

/-- `09:1236`, `09:1246`: the weight, the banked `CertKind.weight`. -/
noncomputable def weight (c : RoutedRowCertificate P Coord r A0) : ℝ := c.kind.weight

/-- **Aux C1.**  The depth is the route length.  General. -/
@[simp] theorem depth_eq (c : RoutedRowCertificate P Coord r A0) :
    c.depth = c.route.length := rfl

/-- **Aux C2.**  Every certificate has positive remaining selector capacity.
General. -/
theorem one_le_capacity (c : RoutedRowCertificate P Coord r A0) : 1 ≤ c.capacity :=
  one_le_stoppingCapacity _ _

/-- **`09:1238--1239`, in capacity form.**  `kappa_v A_0 <= |rows|`. -/
theorem capacity_mul_initial_le_rows (c : RoutedRowCertificate P Coord r A0) :
    c.capacity * A0 ≤ c.rows.card := by
  have h := c.rows_floor
  unfold capacity stoppingCapacity depth rows
  simpa [refRowFloor] using h

/-- **Aux C3.**  A certificate with a positive initial floor holds rows.
General. -/
theorem rows_nonempty (c : RoutedRowCertificate P Coord r A0) (hA0 : 1 ≤ A0) :
    c.rows.Nonempty := by
  have h := c.capacity_mul_initial_le_rows
  have h1 := c.one_le_capacity
  have hpos : 0 < c.rows.card := by
    have : 1 ≤ c.capacity * A0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  exact Finset.card_pos.mp hpos

/-- **Aux C4.**  A certificate's rows are a subset of the reference rows it
started with.  General round-trip law. -/
theorem rows_subset_refRows (c : RoutedRowCertificate P Coord r A0) :
    c.rows ⊆ c.refRows := rowsAt_subset _ _ _

/-- **The bridge to the banked `RoutedCertificate`.**

Every row-carrying certificate *is* one of the banked certificates, with its row
count and kind now computed rather than supplied.  This is the payoff of the
refinement: the banked record and every consumer of it apply verbatim, and the
GAP-EXPOSED item 1 defect -- free kind data -- is removed without restating a
single banked lemma. -/
def toRoutedCertificate (c : RoutedRowCertificate P Coord r A0) :
    RoutedCertificate P Coord r A0 where
  coord := c.coord
  route := c.route
  kind := c.kind
  rows := c.rows.card
  route_alice := c.route_alice
  route_len_le := c.route_len_le
  rows_floor := c.rows_floor

/-- **Aux C5.**  The bridge keeps the route.  General. -/
@[simp] theorem toRoutedCertificate_route (c : RoutedRowCertificate P Coord r A0) :
    c.toRoutedCertificate.route = c.route := rfl

/-- **Aux C6.**  The bridge keeps the derived kind -- it is not re-chosen.
General. -/
@[simp] theorem toRoutedCertificate_kind (c : RoutedRowCertificate P Coord r A0) :
    c.toRoutedCertificate.kind = c.kind := rfl

/-- **Aux C7.**  The bridge keeps the derived row count.  General. -/
@[simp] theorem toRoutedCertificate_rows (c : RoutedRowCertificate P Coord r A0) :
    c.toRoutedCertificate.rows = c.rows.card := rfl

/-- **`09:1240--1244`, one routing step.**

"At an Alice query, route it to a child containing at least `ceil(A_k/2)` of
those rows."  The descendant along a *qualifying* bit is again a routed
certificate: its route is one Alice query longer and the frozen floor is restored
at the smaller capacity. -/
def step (c : RoutedRowCertificate P Coord r A0) (hnode : IsANode (descend P c.route))
    (hlt : c.route.length < r) (b : Bool) (hb : Qualifies P c.refRows A0 r c.route b) :
    RoutedRowCertificate P Coord r A0 where
  coord := c.coord
  refRows := c.refRows
  route := c.route ++ [b]
  route_alice := isAlicePath_append c.route_alice ⟨hnode, isAlicePath_nil _⟩
  route_len_le := by
    have : (c.route ++ [b]).length = c.route.length + 1 := by simp
    omega
  rows_floor := by
    have hlen : (c.route ++ [b]).length = c.route.length + 1 := by simp
    have hsub : r - (c.route.length + 1) = r - c.route.length - 1 := by omega
    rw [hlen, hsub]
    exact hb

/-- **Aux C8.**  A routing step advances the depth by exactly one.  General. -/
@[simp] theorem step_route (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b) :
    (c.step hnode hlt b hb).route = c.route ++ [b] := rfl

/-- **Aux C9.**  A routing step keeps the coordinate and the reference rows: the
frozen rule moves a certificate, it never re-seeds one.  General. -/
@[simp] theorem step_refRows (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b) :
    (c.step hnode hlt b hb).refRows = c.refRows := rfl

/-- **Aux C10.**  Depth readout of a step.  General. -/
theorem step_depth (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b) :
    (c.step hnode hlt b hb).depth = c.depth + 1 := by
  simp [depth]

/-- **`09:1244--1248`, the kind transition on the certificate.**  The derived kind
of the descendant is `low` when the certificate split at the parent and is
otherwise unchanged. -/
theorem step_kind (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b) :
    (c.step hnode hlt b hb).kind
      = if splitsAt P c.refRows A0 r c.route then CertKind.low else c.kind := by
  simp [kind, step, kindAlong_append_bit]

/-- **`09:1244--1245`, "A clean certificate routed uniquely stays clean with
weight one" -- proved.** -/
theorem step_kind_of_not_split (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b)
    (hs : splitsAt P c.refRows A0 r c.route = false) :
    (c.step hnode hlt b hb).kind = c.kind := by
  rw [step_kind, hs]; simp

/-- **`09:1245--1246`, "When a clean certificate splits, both descendants become
low certificates of weight `1/2`" -- proved, for both descendants at once. -/
theorem step_kind_of_split (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b)
    (hs : splitsAt P c.refRows A0 r c.route = true) :
    (c.step hnode hlt b hb).kind = CertKind.low := by
  rw [step_kind, hs]; simp

/-- **`09:1247--1248`, "A low certificate keeps weight `1/2`, whether it has one
or two qualifying children" -- proved. -/
theorem kind_low_of_kind_low (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) (b : Bool)
    (hb : Qualifies P c.refRows A0 r c.route b) (hlow : c.kind = CertKind.low) :
    (c.step hnode hlt b hb).kind = CertKind.low := by
  rw [step_kind]
  cases splitsAt P c.refRows A0 r c.route <;> simp [hlow]

/-- **`09:1240--1242`, the frozen unique routing step.**  When the certificate
does not split, it goes to the child named by `routeBit`, which the frozen rule
guarantees qualifies. -/
def routedStep (c : RoutedRowCertificate P Coord r A0) (hnode : IsANode (descend P c.route))
    (hlt : c.route.length < r) : RoutedRowCertificate P Coord r A0 :=
  c.step hnode hlt (routeBit P c.refRows A0 r c.route)
    (routeBit_qualifies hnode hlt c.rows_floor)

/-- **Aux C11.**  Depth readout of the frozen step.  General. -/
@[simp] theorem routedStep_route (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) :
    (c.routedStep hnode hlt).route = c.route ++ [routeBit P c.refRows A0 r c.route] := rfl

/-- **Aux C12.**  General. -/
@[simp] theorem routedStep_refRows (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r) :
    (c.routedStep hnode hlt).refRows = c.refRows := rfl

/-- **`09:1246`, the two descendants of a split, against the banked
`CertKind.routeOut`.**

The banked `CertKind.routeOut k true = [low, low]` was a *stipulated* table.  Here
the two descendants produced by the row dynamics are shown to carry exactly those
kinds, so the banked weight bookkeeping is a statement about the actual routing
and not about a parallel invention. -/
theorem split_children_kinds (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r)
    (hs : splitsAt P c.refRows A0 r c.route = true) :
    [(c.step hnode hlt false (qualifies_false_of_splitsAt hs)).kind,
      (c.step hnode hlt true (qualifies_true_of_splitsAt hs)).kind]
      = CertKind.routeOut c.kind true := by
  rw [step_kind_of_split _ _ _ _ _ hs, step_kind_of_split _ _ _ _ _ hs]
  cases h : c.kind <;> simp [CertKind.routeOut]

/-- **`09:1245`, `09:1247`, the unique descendant, against the banked
`CertKind.routeOut`.**  `routeOut k false = [k]`, and the dynamics agree. -/
theorem unique_child_kinds (c : RoutedRowCertificate P Coord r A0)
    (hnode : IsANode (descend P c.route)) (hlt : c.route.length < r)
    (hs : splitsAt P c.refRows A0 r c.route = false) :
    [(c.routedStep hnode hlt).kind] = CertKind.routeOut c.kind false := by
  rw [routedStep, step_kind_of_not_split _ _ _ _ _ hs]
  cases h : c.kind <;> simp [CertKind.routeOut]

/-- **`09:1248`, "Thus total certificate weight never decreases", at the derived
kinds.**  The one-step estimate is the banked
`CertKind.weight_le_totalRouteWeight`, consumed by pin; what is new is that its
argument is now this module's *computed* kind and *computed* split decision, so
the frozen sentence is a statement about the routing itself. -/
theorem weight_le_descendant_weight (c : RoutedRowCertificate P Coord r A0) :
    c.weight
      ≤ CertKind.totalRouteWeight
          (CertKind.routeOut c.kind (splitsAt P c.refRows A0 r c.route)) :=
  CertKind.weight_le_totalRouteWeight _ _

end RoutedRowCertificate

/-- **`09:1233--1236`, the paper's own initial placement -- the canonical
inhabitant.**

"Even if every deleted row of `U` were concentrated in one nonexceptional outer
coordinate, that coordinate would therefore retain at least `A_r = q A_0`
reference rows.  Start one clean reference certificate in every coordinate
outside `E_0`, each with weight one."

The hypothesis `hR` is the frozen retention statement itself, evaluated through
the banked `refRowFloor` at the frozen exponent `r`; the route is the root; and
the kind and weight are **computed** below to be `clean` and `1` rather than
assigned.

**On the `E_0` side condition.**  As in the banked `initialCertificate`, "outside
`E_0`" is not one of the certificate's frozen laws but a fact about *which*
coordinates the argument starts certificates in, tracked by the exceptional-set
bookkeeping of `WrapperProjectionCovers`; folding it in would make the definition
demand more than the frozen text states (mechanical rules M1--M10). -/
def initialRowCertificate (P : Protocol X Y Z) {Coord : Type*} (i : Coord) (R : Finset X)
    (r A0 : ℕ) (hR : refRowFloor A0 r ≤ R.card) : RoutedRowCertificate P Coord r A0 where
  coord := i
  refRows := R
  route := []
  route_alice := isAlicePath_nil P
  route_len_le := by simp
  rows_floor := by simpa using hR

/-- **`09:1235--1236`, evaluated.**  The paper's initial certificate is clean. -/
@[simp] theorem initialRowCertificate_kind (P : Protocol X Y Z) {Coord : Type*} (i : Coord)
    (R : Finset X) (r A0 : ℕ) (hR : refRowFloor A0 r ≤ R.card) :
    (initialRowCertificate P i R r A0 hR).kind = CertKind.clean := by
  simp [RoutedRowCertificate.kind, initialRowCertificate]

/-- **`09:1235--1236`, evaluated.**  "each with weight one". -/
@[simp] theorem initialRowCertificate_weight (P : Protocol X Y Z) {Coord : Type*} (i : Coord)
    (R : Finset X) (r A0 : ℕ) (hR : refRowFloor A0 r ≤ R.card) :
    (initialRowCertificate P i R r A0 hR).weight = 1 := by
  simp [RoutedRowCertificate.weight, RoutedRowCertificate.kind, initialRowCertificate,
    CertKind.weight]

/-- **`09:1233--1235`, evaluated.**  At the root the certificate holds all `A_r`
retained reference rows, and its remaining selector capacity is the full
`q = 2^r`. -/
theorem initialRowCertificate_rows (P : Protocol X Y Z) {Coord : Type*} (i : Coord)
    (R : Finset X) (r A0 : ℕ) (hR : refRowFloor A0 r ≤ R.card) :
    (initialRowCertificate P i R r A0 hR).rows = R ∧
      (initialRowCertificate P i R r A0 hR).capacity = 2 ^ r := by
  refine ⟨by simp [RoutedRowCertificate.rows, initialRowCertificate], ?_⟩
  simp [RoutedRowCertificate.capacity, RoutedRowCertificate.depth, initialRowCertificate,
    stoppingCapacity]

/-- **Hypothesis legality of the canonical inhabitant.**

The floor hypothesis `A_r <= |R|` of `initialRowCertificate` is satisfiable at
legal, nondegenerate parameters: on a row space of exactly `A_r = 2^r A_0` rows it
holds with equality, and the resulting certificate is clean, of weight one, and
holds a **nonempty** row set whenever the initial floor `A_0` is positive.  So the
canonical placement is not inhabited only at a degenerate or
cardinality-contradictory point. -/
theorem initialRowCertificate_hypothesis_legal {Z : Type*} {Coord : Type*} (i : Coord)
    (r A0 : ℕ) (hA0 : 1 ≤ A0) (z : Z) :
    ∃ hR : refRowFloor A0 r ≤ (Finset.univ : Finset (Fin (refRowFloor A0 r))).card,
      (initialRowCertificate (Protocol.leaf z : Protocol (Fin (refRowFloor A0 r)) Bool Z)
          i Finset.univ r A0 hR).kind = CertKind.clean ∧
        (initialRowCertificate (Protocol.leaf z : Protocol (Fin (refRowFloor A0 r)) Bool Z)
          i Finset.univ r A0 hR).rows.Nonempty := by
  have hcard : (Finset.univ : Finset (Fin (refRowFloor A0 r))).card = refRowFloor A0 r := by
    simp
  refine ⟨by omega, ?_, ?_⟩
  · simp
  · exact RoutedRowCertificate.rows_nonempty _ hA0

end Certificate

/-! ## §4  Where a routed branch stops (`09:1195--1200`, `09:1250--1252`)

"Stop each routed branch at its first Bob query, or after `r` Alice queries."

With the routing rule now a function, the stopping rule becomes an iteration, and
the frozen dichotomy becomes a theorem: under the frame condition of
`lem:wrapper-no-bob-completion` every routed branch stops at one of the two
frozen addresses of the banked module. -/

section Stopping

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- Decidable form of the banked `IsANode`. -/
def isANodeB : Protocol X Y Z → Bool
  | Protocol.aNode _ _ _ => true
  | Protocol.leaf _ => false
  | Protocol.bNode _ _ _ => false

omit [Fintype X] [DecidableEq X] in
/-- **Aux D1.**  The decidable form agrees with the banked predicate.  General. -/
theorem isANodeB_eq_true_iff {P : Protocol X Y Z} : isANodeB P = true ↔ IsANode P := by
  constructor
  · intro h
    cases P with
    | leaf z => simp [isANodeB] at h
    | aNode a l rr => exact ⟨a, l, rr, rfl⟩
    | bNode f l rr => simp [isANodeB] at h
  · rintro ⟨a, l, rr, rfl⟩; rfl

omit [Fintype X] [DecidableEq X] in
/-- **Aux D2.**  A query node that is not Alice's is Bob's -- the frozen stopping
rule has exactly two outcomes at an internal node.  General. -/
theorem isBobNode_of_not_isANode {P : Protocol X Y Z} (hq : IsQueryNode P)
    (ha : ¬ IsANode P) : IsBobNode P := by
  cases P with
  | leaf z => exact hq.elim
  | aNode a l rr => exact absurd ⟨a, l, rr, rfl⟩ ha
  | bNode f l rr => trivial

/-- **`09:1195--1200`, the frame condition of `lem:wrapper-no-bob-completion`.**

"The protocol may be chosen ... so that every root-to-leaf path containing no Bob
query contains at least `r` Alice queries."  Equivalently: no Alice-only route
shorter than `r` reaches a leaf.  Carried as an explicit named hypothesis, never
as structure data and never as an axiom. -/
def CompletedNoBob (P : Protocol X Y Z) (r : ℕ) : Prop :=
  ∀ p : List Bool, IsAlicePath P p → p.length < r → IsQueryNode (descend P p)

/-- **`09:1250`, the routing iterated.**  Follow the frozen rule while the node
is an Alice query and the `r` Alice queries are not exhausted. -/
def routeFuel {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ} :
    ℕ → RoutedRowCertificate P Coord r A0 → RoutedRowCertificate P Coord r A0
  | 0, c => c
  | n + 1, c =>
      if h : isANodeB (descend P c.route) = true ∧ c.route.length < r then
        routeFuel n (c.routedStep (isANodeB_eq_true_iff.mp h.1) h.2)
      else c

/-- **Aux D3.**  With no fuel the routing stands still.  General. -/
@[simp] theorem routeFuel_zero {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}
    (c : RoutedRowCertificate P Coord r A0) : routeFuel 0 c = c := rfl

/-- **Aux D4.**  A stopped branch is stopped: if the node is not an Alice query
below the `r`-th, no fuel is consumed.  General. -/
theorem routeFuel_of_stopped {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}
    (c : RoutedRowCertificate P Coord r A0) (n : ℕ)
    (h : ¬ (isANodeB (descend P c.route) = true ∧ c.route.length < r)) :
    routeFuel (n + 1) c = c := by
  simp [routeFuel, h]

/-- **`09:1250--1252`, the frozen stopping dichotomy, proved.**

"Stop each routed branch at its first Bob query, or after `r` Alice queries."
Under the completion frame condition, iterating the frozen routing rule from a
certificate at depth `d` for `r - d` steps always lands on one of the two frozen
addresses of the banked module -- an exposed first-Bob node, or a final Alice
node.

This is the address half of the deferred canonical-inhabitation obligation: the
frontier of the paper's own routing is now constructed from the protocol, and
only its indexing remains. -/
theorem routeFuel_stops {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}
    (hcomp : CompletedNoBob P r) :
    ∀ (n : ℕ) (c : RoutedRowCertificate P Coord r A0), c.route.length + n = r →
      IsFirstBobNode P r (routeFuel n c).route ∨
        IsFinalAliceNode P r (routeFuel n c).route := by
  intro n
  induction n with
  | zero =>
      intro c hlen
      refine Or.inr ?_
      rw [routeFuel_zero]
      exact ⟨c.route_alice, by omega⟩
  | succ n ih =>
      intro c hlen
      by_cases h : isANodeB (descend P c.route) = true ∧ c.route.length < r
      · have hstep : routeFuel (n + 1) c
            = routeFuel n (c.routedStep (isANodeB_eq_true_iff.mp h.1) h.2) := by
          simp [routeFuel, h]
        rw [hstep]
        refine ih _ ?_
        have : (c.routedStep (isANodeB_eq_true_iff.mp h.1) h.2).route.length
            = c.route.length + 1 := by simp
        omega
      · rw [routeFuel_of_stopped c n h]
        have hlt : c.route.length < r := by omega
        have hna : ¬ IsANode (descend P c.route) := by
          intro hcon
          exact h ⟨isANodeB_eq_true_iff.mpr hcon, hlt⟩
        have hq : IsQueryNode (descend P c.route) := hcomp _ c.route_alice hlt
        exact Or.inl ⟨c.route_alice, isBobNode_of_not_isANode hq hna, hlt⟩

/-- **`09:1250`, the stopping node of a certificate.** -/
def stopAt {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}
    (c : RoutedRowCertificate P Coord r A0) : RoutedRowCertificate P Coord r A0 :=
  routeFuel (r - c.route.length) c

/-- **`09:1250--1252`, on the stopping node.** -/
theorem stopAt_isFrontier {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ}
    (hcomp : CompletedNoBob P r) (c : RoutedRowCertificate P Coord r A0) :
    IsFirstBobNode P r (stopAt c).route ∨ IsFinalAliceNode P r (stopAt c).route :=
  routeFuel_stops hcomp _ c (by have := c.route_len_le; omega)

omit [Fintype X] [DecidableEq X] in
/-- **Aux D5 (every node strictly inside an Alice route is an Alice query).**
General; the fact the frozen prefix-freeness argument of `09:1259` rests on. -/
theorem isANode_take_of_isAlicePath : ∀ {P : Protocol X Y Z} {p : List Bool} {n : ℕ},
    IsAlicePath P p → n < p.length → IsANode (descend P (p.take n)) := by
  intro P p
  induction p generalizing P with
  | nil => intro n _ h; simp at h
  | cons b q ih =>
      intro n hpath hn
      obtain ⟨hnode, hrest⟩ := hpath
      cases n with
      | zero => simpa using hnode
      | succ m =>
          have hm : m < q.length := by simpa using hn
          have := ih (P := descendStep P b) hrest hm
          simpa [List.take_succ_cons, descend_cons] using this

omit [Fintype X] [DecidableEq X] in
/-- **`09:1259`, "Prefix-freeness", derived from the two stopping rules.**

A family of frontier addresses, each stopped by one of the two frozen rules and
pairwise distinct, is automatically prefix-free: a first-Bob address cannot lie
strictly inside another branch's Alice-only route, and a final address already has
the maximal depth `r`.

This is a **structural finding about the banked `RoutedSystem`**: its `prefixFree`
field is not independent data but a consequence of `firstBob_spec` and
`final_spec` together with injectivity of the address map.  The banked record is
not edited; the lemma is offered as the constructor helper that discharges the
field, and it is what the canonical system will use. -/
theorem prefixFree_of_stopping {P : Protocol X Y Z} {V : Type*} {r : ℕ}
    (node : V → List Bool)
    (hstop : ∀ v, IsFirstBobNode P r (node v) ∨ IsFinalAliceNode P r (node v))
    (hinj : ∀ v w : V, node v = node w → v = w) : PrefixFreeFrontier node := by
  intro v w hvw hpre
  have hlen_le : (node v).length ≤ (node w).length := hpre.length_le
  have hne : (node v).length ≠ (node w).length := by
    intro heq
    exact hvw (hinj v w (hpre.eq_of_length heq))
  have hlt : (node v).length < (node w).length := by omega
  have hpath_w : IsAlicePath P (node w) := by
    rcases hstop w with hw | hw
    · exact hw.1
    · exact hw.1
  have hdepth_w : (node w).length ≤ r := by
    rcases hstop w with hw | hw
    · exact le_of_lt hw.2.2
    · exact le_of_eq hw.2
  have htake : node v = (node w).take (node v).length := List.prefix_iff_eq_take.mp hpre
  rcases hstop v with hv | hv
  · have halice : IsANode (descend P ((node w).take (node v).length)) :=
      isANode_take_of_isAlicePath hpath_w hlt
    rw [← htake] at halice
    exact not_isBobNode_of_isANode halice hv.2.1
  · have hvr := hv.2
    omega

/-! ### The stopping dichotomy at live protocols

`routeFuel_stops` and `prefixFree_of_stopping` would be worth nothing if
`CompletedNoBob` were unsatisfiable, or if only one branch of the dichotomy could
occur.  Both branches are exhibited below on the two frame-legal protocols the
banked module already carries, so neither the hypothesis nor either outcome is
vacuous. -/

omit [Fintype X] [DecidableEq X] in
/-- **`09:1195--1213`, the completion frame condition on the completed shape.**
The banked `aliceLadder` is exactly the shape `lem:wrapper-no-bob-completion`
produces -- "append `r-d` fixed Alice messages ... their new depth is exactly
`r`" -- and it satisfies the frame condition: no Alice-only route shorter than
`r` reaches a leaf. -/
theorem completedNoBob_aliceLadder (a : X → Bool) (z : Z) (r : ℕ) :
    CompletedNoBob (aliceLadder (X := X) (Y := Y) a z r) r := by
  intro p _ hlt
  have hlen : p.length ≤ r := le_of_lt hlt
  rw [descend_aliceLadder a z hlen]
  obtain ⟨m, hm⟩ : ∃ m, r - p.length = m + 1 := ⟨r - p.length - 1, by omega⟩
  rw [hm]
  trivial

/-- **`09:1252`, the final-node branch is live.**  On the completed shape every
routed branch stops by the *second* frozen rule, after `r` Alice queries: that
protocol has no Bob query at all, so the first rule cannot fire. -/
theorem aliceLadder_stopAt_final (a : X → Bool) (z : Z) {Coord : Type*} {r A0 : ℕ}
    (c : RoutedRowCertificate (aliceLadder (X := X) (Y := Y) a z r) Coord r A0) :
    IsFinalAliceNode (aliceLadder (X := X) (Y := Y) a z r) r (stopAt c).route := by
  rcases stopAt_isFrontier (completedNoBob_aliceLadder (Y := Y) a z r) c with h | h
  · exfalso
    have hlen : (stopAt c).route.length ≤ r := (stopAt c).route_len_le
    have hbob := h.2.1
    rw [descend_aliceLadder a z hlen] at hbob
    rcases Nat.eq_zero_or_pos (r - (stopAt c).route.length) with hm | hm
    · rw [hm] at hbob; exact hbob
    · obtain ⟨m, hm'⟩ : ∃ m, r - (stopAt c).route.length = m + 1 :=
        ⟨r - (stopAt c).route.length - 1, by omega⟩
      rw [hm'] at hbob; exact hbob
  · exact h

omit [Fintype X] [DecidableEq X] in
/-- **Aux D6.**  No Alice-only route outruns the Bob cap of the banked
`bobCappedLadder`: the capping Bob query is not an Alice node, so the route stops
there.  General. -/
theorem isAlicePath_bobCappedLadder_length_le {a : X → Bool} {f : Y → Bool} {z : Z} :
    ∀ {d : ℕ} {p : List Bool}, IsAlicePath (bobCappedLadder a f z d) p → p.length ≤ d := by
  intro d p
  induction p generalizing d with
  | nil => intro _; simp
  | cons b q ih =>
      intro h
      obtain ⟨hnode, hrest⟩ := h
      cases d with
      | zero =>
          obtain ⟨a', l', r', hEq⟩ := hnode
          exact absurd hEq (by simp [bobCappedLadder])
      | succ m =>
          have hstep : descendStep (bobCappedLadder a f z (m + 1)) b
              = bobCappedLadder a f z m := by
            cases b <;> simp [bobCappedLadder, descendStep]
          rw [hstep] at hrest
          have hq := ih hrest
          simpa using Nat.succ_le_succ hq

omit [Fintype X] [DecidableEq X] in
/-- **`09:1195--1213` on the Bob-capped shape.**  The frame condition also holds
there: every node an Alice-only route can reach is a query node -- Alice's below
the cap, Bob's at it. -/
theorem completedNoBob_bobCappedLadder (a : X → Bool) (f : Y → Bool) (z : Z) {r d : ℕ} :
    CompletedNoBob (bobCappedLadder a f z d) r := by
  intro p hpath _
  have hlen : p.length ≤ d := isAlicePath_bobCappedLadder_length_le hpath
  rw [descend_bobCappedLadder a f z hlen]
  rcases Nat.eq_zero_or_pos (d - p.length) with hm | hm
  · rw [hm]; trivial
  · obtain ⟨m, hm'⟩ : ∃ m, d - p.length = m + 1 := ⟨d - p.length - 1, by omega⟩
    rw [hm']; trivial

/-- **`09:1250--1251`, the first-Bob branch is live.**  On the Bob-capped shape
with the cap strictly below the `r`-th Alice query, every routed branch stops by
the *first* frozen rule, at an exposed first-Bob node.  So neither outcome of
`routeFuel_stops` is vacuous, and the frozen `kappa_v >= 2` of `09:1259` applies
to a nonempty class of stopping nodes produced by the routing itself. -/
theorem bobCappedLadder_stopAt_firstBob (a : X → Bool) (f : Y → Bool) (z : Z)
    {Coord : Type*} {r d A0 : ℕ} (hd : d < r)
    (c : RoutedRowCertificate (bobCappedLadder a f z d) Coord r A0) :
    IsFirstBobNode (bobCappedLadder a f z d) r (stopAt c).route := by
  rcases stopAt_isFrontier (completedNoBob_bobCappedLadder (r := r) a f z) c with h | h
  · exact h
  · exfalso
    have hlen := isAlicePath_bobCappedLadder_length_le (a := a) (f := f) (z := z) h.1
    have hr := h.2
    omega

/-- **The paper's own initial placement reaches an exposed first-Bob node.**
Chaining `initialRowCertificate` -- the frozen `09:1235--1236` object -- with the
routing exhibits the first frozen stopping rule firing end to end, from the
initial clean certificate to its stopping address. -/
theorem initial_stopAt_firstBob (a : X → Bool) (f : Y → Bool) (z : Z) {Coord : Type*}
    (i : Coord) (R : Finset X) {r d A0 : ℕ} (hd : d < r)
    (hR : refRowFloor A0 r ≤ R.card) :
    IsFirstBobNode (bobCappedLadder a f z d) r
      (stopAt (initialRowCertificate (bobCappedLadder a f z d) i R r A0 hR)).route :=
  bobCappedLadder_stopAt_firstBob a f z hd _

end Stopping

/-! ## §5  The denser Bob child, in its projection form (`09:1287--1290`)

"Every represented coordinate is outside `E_0`, so the parent projection to any
selected `u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob
child retains density at least `y^2`."

The banked module proved the **column-set** halving and explicitly forbade citing
it for this sentence, because the sentence is about the *projection* of the
column set.  This section lands the projection form, discharging GAP-EXPOSED
item 7. -/

section Projection

variable {q : ℕ} {Yc : Type*} [DecidableEq Yc] [Fintype Yc] {X Z : Type*}

omit [Fintype Yc] in
/-- **Aux E1.**  Projection commutes with union: a projection is an image, and
images distribute over unions.  General. -/
theorem projSet_union (J : Finset (Fin q)) (A B : Finset (Fin q → Yc)) :
    WrapperProjectionCovers.projSet J (A ∪ B)
      = WrapperProjectionCovers.projSet J A ∪ WrapperProjectionCovers.projSet J B := by
  unfold WrapperProjectionCovers.projSet
  exact Finset.image_union _ _

omit [Fintype Yc] in
/-- **The subadditivity the banked module prescribed**, verbatim:
`|projSet J (A union B)| <= |projSet J A| + |projSet J B|`.  General. -/
theorem card_projSet_union_le (J : Finset (Fin q)) (A B : Finset (Fin q → Yc)) :
    (WrapperProjectionCovers.projSet J (A ∪ B)).card
      ≤ (WrapperProjectionCovers.projSet J A).card
        + (WrapperProjectionCovers.projSet J B).card := by
  rw [projSet_union]
  exact Finset.card_union_le _ _

/-- **Aux E2.**  The two Bob children of a Bob query split the node's *retained*
column set, by the banked `bobCols_children_union`.  General. -/
theorem retainedCols_children_union {P : Protocol X (Fin q → Yc) Z} {p : List Bool}
    (h : IsBobNode (descend P p)) (S : Finset (Fin q → Yc)) :
    retainedCols P S (p ++ [false]) ∪ retainedCols P S (p ++ [true]) = retainedCols P S p := by
  simp only [retainedCols, ← Finset.inter_union_distrib_left, bobCols_children_union h]

/-- **`09:1287--1290`, the projection subadditivity at a Bob query.**  The banked
`card_projSet_children_le` applied to `bobCols_children_union`, exactly as the
banked next-round prescription asked. -/
theorem card_nodeProjection_children_le {P : Protocol X (Fin q → Yc) Z} {p : List Bool}
    (h : IsBobNode (descend P p)) (S : Finset (Fin q → Yc)) (J : Finset (Fin q)) :
    (nodeProjection P S J p).card
      ≤ (nodeProjection P S J (p ++ [false])).card
        + (nodeProjection P S J (p ++ [true])).card := by
  unfold nodeProjection
  rw [← retainedCols_children_union h S]
  exact card_projSet_union_le _ _ _

/-- **`09:1290`, "The denser Bob child" -- the projection form.**

One of the two Bob children retains at least half of the parent node's column
*projection*.  This is the statement the frozen sentence makes, and the banked
`exists_denser_bob_child` (a column-set statement) was explicitly not permitted
to stand in for it. -/
theorem exists_denser_bob_child_projection {P : Protocol X (Fin q → Yc) Z} {p : List Bool}
    (h : IsBobNode (descend P p)) (S : Finset (Fin q → Yc)) (J : Finset (Fin q)) :
    ∃ b : Bool,
      (nodeProjection P S J p).card ≤ 2 * (nodeProjection P S J (p ++ [b])).card := by
  have hle := card_nodeProjection_children_le h S J
  rcases le_total (nodeProjection P S J (p ++ [false])).card
      (nodeProjection P S J (p ++ [true])).card with hc | hc
  · exact ⟨true, by omega⟩
  · exact ⟨false, by omega⟩

/-- **`09:1287--1290`, in the frozen density form.**

"the parent projection ... has density at least `rho`.  The denser Bob child
retains density at least `rho/2`."  The density denominator is the frozen
`|Y|^{|J|}` of the banked `WrapperProjectionCovers`, so no new normalization is
introduced. -/
theorem exists_denser_bob_child_density {P : Protocol X (Fin q → Yc) Z} {p : List Bool}
    {ρ : ℝ} (h : IsBobNode (descend P p)) (S : Finset (Fin q → Yc)) (J : Finset (Fin q))
    (hdens : ρ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((nodeProjection P S J p).card : ℝ)) :
    ∃ b : Bool,
      (ρ / 2) * (Fintype.card Yc : ℝ) ^ J.card
        ≤ ((nodeProjection P S J (p ++ [b])).card : ℝ) := by
  obtain ⟨b, hb⟩ := exists_denser_bob_child_projection h S J
  refine ⟨b, ?_⟩
  have hb' : ((nodeProjection P S J p).card : ℝ)
      ≤ 2 * ((nodeProjection P S J (p ++ [b])).card : ℝ) := by exact_mod_cast hb
  linarith

/-- **`09:1289--1290`, verbatim.**  "the parent projection to any selected
`u_{kappa_v}` of them has density at least `rho = 2y^2`.  The denser Bob child
retains density at least `y^2`."  The frozen constants are substituted, not
re-derived: `rho = 2y^2` in, `y^2` out. -/
theorem denserBobChild_retains_y_sq {P : Protocol X (Fin q → Yc) Z} {p : List Bool}
    {y : ℝ} (h : IsBobNode (descend P p)) (S : Finset (Fin q → Yc)) (J : Finset (Fin q))
    (hdens : 2 * y ^ 2 * (Fintype.card Yc : ℝ) ^ J.card
      ≤ ((nodeProjection P S J p).card : ℝ)) :
    ∃ b : Bool,
      y ^ 2 * (Fintype.card Yc : ℝ) ^ J.card
        ≤ ((nodeProjection P S J (p ++ [b])).card : ℝ) := by
  obtain ⟨b, hb⟩ := exists_denser_bob_child_density (ρ := 2 * y ^ 2) h S J hdens
  exact ⟨b, by linarith⟩

end Projection

/-- **Statement pole for the projection halving.**  No fixed bit is a witness in
the projection form either: at a Bob query whose predicate sends every column to
the `true` child, the `false` child's projection is empty while the parent's is
not, so the bound at `false` fails.  The frozen "*the* denser Bob child" of
`09:1290` therefore names a genuine choice in the projection form as well. -/
theorem projection_denserChild_needs_the_right_bit :
    ¬ ((nodeProjection
          (bobCappedLadder (X := Bool) (fun _ => true) (fun _ : Fin 1 → Bool => true) true 0)
          Finset.univ (Finset.univ : Finset (Fin 1)) ([] : List Bool)).card
        ≤ 2 * (nodeProjection
          (bobCappedLadder (X := Bool) (fun _ => true) (fun _ : Fin 1 → Bool => true) true 0)
          Finset.univ (Finset.univ : Finset (Fin 1)) ([] ++ [false])).card) := by
  decide

/-! ## §6  The ladder call at a live owner pair (`09:1315--1344`)

`lem:final-reference-uniqueness`: "Every final Alice-frontier node ... contains at
most one reference certificate."  Its proof supposes the opposite -- two
certificates from distinct initial coordinates at one final node -- invokes
`lem:certified-row-ladder`, and contradicts the suffix budget of `09:1341--1343`.

The banked `owner_injOn_of_ladder` carries that argument, but its
hypothesis-consistency instance `ladderSystem_owner_injOn` has an identity owner
map, so the `hladder` and `hresidual` binders were discharged vacuously
(GAP-EXPOSED item 8).  This section builds the configuration the frozen lemma
refutes -- `iota` strictly larger than `V` -- and runs the argument on it. -/

section LivePair

variable {X Y Z : Type*}

/-- **The counterfactual two-certificates-per-node system.**

Every branch is stopped after `r` Alice queries, as in the banked `ladderSystem`,
but the certificate index type is `(Fin r -> Bool) x Bool`: **two** certificates
sit at each final node, carrying distinct outer coordinates.  All of
`RoutedSystem`'s laws hold -- in particular the frozen coordinate uniqueness of
`09:1278--1280`, which forbids two descendants of *one* initial coordinate at a
node and says nothing about two descendants of *two* -- and the underlying
protocol satisfies the frozen frame cost bound of `09:1207--1212`.

**NON-FIDELITY label.**  This is emphatically *not* the paper's routed system: it
is the configuration `lem:final-reference-uniqueness` exists to rule out.  It is
built so that the frozen refutation has something to bite on, and its prefix-free
field is discharged through this module's own `prefixFree_of_stopping`, exercising
that lemma at a live family. -/
def twinSystem (a : X → Bool) (z : Z) (r A0 : ℕ) :
    RoutedSystem (aliceLadder (X := X) (Y := Y) a z r) ((Fin r → Bool) × Bool)
      ((Fin r → Bool) × Bool) (Fin r → Bool) r A0 where
  node := tupleRoute
  prefixFree :=
    prefixFree_of_stopping (P := aliceLadder (X := X) (Y := Y) a z r) (r := r) tupleRoute
      (fun v => Or.inr ⟨isAlicePath_aliceLadder a z (le_of_eq (tupleRoute_length v)),
        tupleRoute_length v⟩)
      (fun _ _ h => tupleRoute_injective h)
  firstBob := fun _ => false
  firstBob_spec := fun v h => by exact absurd h (by simp)
  final_spec := fun v _ =>
    ⟨isAlicePath_aliceLadder a z (le_of_eq (tupleRoute_length v)), tupleRoute_length v⟩
  place := fun i => i.1
  cert := fun i =>
    { coord := i
      route := tupleRoute i.1
      kind := CertKind.clean
      rows := refRowFloor A0 0
      route_alice := isAlicePath_aliceLadder a z (le_of_eq (tupleRoute_length i.1))
      route_len_le := le_of_eq (tupleRoute_length i.1)
      rows_floor := by rw [tupleRoute_length]; simp }
  cert_at := fun _ => rfl
  coordUnique := fun _ _ _ hc => hc

/-- **Aux F1.**  Every index of the twin system is a clean certificate at a final
node.  General in the parameters. -/
theorem twinSystem_mem_cleanFinal (a : X → Bool) (z : Z) (r A0 : ℕ)
    (i : (Fin r → Bool) × Bool) :
    i ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl, rfl⟩

/-- **The live owner pair (GAP-EXPOSED item 8).**

Two *distinct* clean-final certificates of the twin system share an owner and
carry distinct outer coordinates.  This is precisely the configuration the frozen
`09:1322--1324` supposes, and it is what the banked `ladderSystem` could not
supply. -/
theorem twinSystem_live_pair (a : X → Bool) (z : Z) (r A0 : ℕ) :
    ∃ i ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal,
      ∃ j ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal,
        i ≠ j ∧
          (twinSystem (X := X) (Y := Y) a z r A0).owner i
            = (twinSystem (X := X) (Y := Y) a z r A0).owner j ∧
          ((twinSystem (X := X) (Y := Y) a z r A0).cert i).coord
            ≠ ((twinSystem (X := X) (Y := Y) a z r A0).cert j).coord := by
  refine ⟨(fun _ => false, false), twinSystem_mem_cleanFinal a z r A0 _,
    (fun _ => false, true), twinSystem_mem_cleanFinal a z r A0 _, ?_, rfl, ?_⟩
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)

/-- **The residual binder alone is satisfiable.**  `hresidual` is met by the zero
residual, so the refutation below is not an artefact of an unsatisfiable
residual-cost premise: it is `hladder`, the `lem:certified-row-ladder` call, that
cannot hold at the twin configuration. -/
theorem twinSystem_hresidual_satisfiable (a : X → Bool) (z : Z) (r A0 : ℕ) :
    ∃ residual : ((Fin r → Bool) × Bool) → ((Fin r → Bool) × Bool) → ℕ,
      ∀ i j, residual i j
        ≤ (descend (aliceLadder (X := X) (Y := Y) a z r)
            ((twinSystem (X := X) (Y := Y) a z r A0).node
              ((twinSystem (X := X) (Y := Y) a z r A0).owner i))).cost :=
  ⟨fun _ _ => 0, fun _ _ => Nat.zero_le _⟩

/-- **`09:1321--1343`, the frozen refutation, run at a live pair.**

"Suppose a final node contained two certificates.  They descend from distinct
initial outer coordinates ... Invoke `lem:certified-row-ladder` ... The resulting
two-copy restriction has complexity at least `C`.  But the suffix below a node
reached after `r` Alice bits in the alleged `(C+r-1)`-bit protocol has depth at
most `C-1`, a contradiction."

At the twin system every hypothesis of the banked `owner_injOn_of_ladder` is
present except that its conclusion is false there, so the bundle is
contradictory -- which *is* the frozen lemma.  Unlike the banked
`ladderSystem_owner_injOn`, `hladder` and `hresidual` are consumed at the pair
`((v,false),(v,true))`, whose owners coincide and whose coordinates differ, and
the operative step is the suffix-budget contradiction.

**This derives `False` by design**: it is the frozen proof by contradiction, not a
defective hypothesis bundle.  The bundle minus `hladder` is satisfiable
(`twinSystem_hresidual_satisfiable`), which pins the ladder call as the premise
that fails, and the same bundle *without* the twin configuration is satisfiable
too (the banked `ladderSystem_owner_injOn`).

The `lem:certified-row-ladder` call itself remains a **named hypothesis**: it is
used here, never proved. -/
theorem twinSystem_ladder_refuted (a : X → Bool) (z : Z) {r C : ℕ} (A0 : ℕ) (hC : 3 ≤ C)
    (residual : ((Fin r → Bool) × Bool) → ((Fin r → Bool) × Bool) → ℕ)
    (hresidual : ∀ i j, residual i j
      ≤ (descend (aliceLadder (X := X) (Y := Y) a z r)
          ((twinSystem (X := X) (Y := Y) a z r A0).node
            ((twinSystem (X := X) (Y := Y) a z r A0).owner i))).cost)
    (hladder : ∀ i ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal,
      ∀ j ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal,
        (twinSystem (X := X) (Y := Y) a z r A0).owner i
          = (twinSystem (X := X) (Y := Y) a z r A0).owner j →
        ((twinSystem (X := X) (Y := Y) a z r A0).cert i).coord
          ≠ ((twinSystem (X := X) (Y := Y) a z r A0).cert j).coord →
        C ≤ residual i j) : False := by
  have hinj := (twinSystem (X := X) (Y := Y) a z r A0).owner_injOn_of_ladder (C := C) hC
    (aliceLadder_cost_le_frame a z (by omega)) residual hresidual hladder
  obtain ⟨i, hi, j, hj, hne, hown, _⟩ := twinSystem_live_pair (X := X) (Y := Y) a z r A0
  exact hne (hinj i hi j hj hown)

/-- **Statement pole for `owner_injOn_of_ladder`'s ladder binder.**

The `RoutedSystem` laws alone do **not** give owner injectivity: the twin system
satisfies every one of them, including the frozen coordinate uniqueness of
`09:1278--1280`, and its owner map collides on two distinct clean-final
certificates.  So `hladder` is load-bearing, and `lem:final-reference-uniqueness`
is a genuine theorem about the alleged protocol rather than a bookkeeping
identity. -/
theorem twinSystem_owner_not_injective (a : X → Bool) (z : Z) (r A0 : ℕ) :
    ¬ (∀ i ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal,
        ∀ j ∈ (twinSystem (X := X) (Y := Y) a z r A0).cleanFinal,
          (twinSystem (X := X) (Y := Y) a z r A0).owner i
            = (twinSystem (X := X) (Y := Y) a z r A0).owner j → i = j) := by
  intro hcon
  obtain ⟨i, hi, j, hj, hne, hown, _⟩ := twinSystem_live_pair (X := X) (Y := Y) a z r A0
  exact hne (hcon i hi j hj hown)

end LivePair

end EthInapproximability.ParameterizedNP.RoutingDynamics
