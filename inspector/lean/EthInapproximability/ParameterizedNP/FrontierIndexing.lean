import EthInapproximability.ParameterizedNP.RoutingDynamics

/-!
# Parameterized NP route: the canonical frontier indexing of the routed system

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8a54aaa6f0e60eaeb31ac1719cd696b169d5a845381fbd810a18a86c6b2a24e5`),
  the **frontier layer** of the per-member shallow-protocol refutation engine.
* **The exact frozen lines traced here**, in print order:
  * `09:1233--1236`, the initial placement: "Even if every deleted row of `U`
    were concentrated in one nonexceptional outer coordinate, that coordinate
    would therefore retain at least `A_r = q A_0` reference rows.  Start one
    clean reference certificate in every coordinate outside `E_0`, each with
    weight one."
  * `09:1238--1244`, the routing rule, **including its branching clause**: "At
    remaining selector capacity `2^k`, a certificate consists of at least `A_k`
    reference rows in one outer coordinate.  At an Alice query, route it to a
    child containing at least `ceil(A_k/2) >= A_{k-1}` of those rows; route it to
    both children if both qualify."
  * `09:1244--1248`, the kind transition and the conservation sentence: "A clean
    certificate routed uniquely stays clean with weight one.  When a clean
    certificate splits, both descendants become low certificates of weight
    `1/2`.  A low certificate keeps weight `1/2`, whether it has one or two
    qualifying children.  Thus total certificate weight never decreases."
  * `09:1250--1252`, the two stopping rules, and `09:1252--1257`, "If `v` is a
    frontier node, let `d_v` be the number of preceding Alice queries and set
    `kappa_v = 2^{r-d_v}`, `W_v = total certificate weight at v`."  (The
    sentence opens on `09:1252`, which is also the last line of the preceding
    stopping-rule range; the display `kappa_v`/`W_v` occupies `09:1254--1258`.)
  * `09:105`, the width identification "Let `q = 2^r` be the scale-alignment
    width", which licenses every `q`-vs-`2^r` substitution below.
    Independently corroborated by `09:1221` (`A_k = 2^k A_0`) together with
    `09:1234--1235` (`A_r = q A_0`), which force `q = 2^r`.
  * `09:1259--1266`, "Every first-Bob node has `kappa_v >= 2`.  Prefix-freeness
    and conservation give `sum_v W_v >= q - e_0`, `sum_v kappa_v <= q`"
    (`eq:wrapper-frontier-conservation`).
* **Cross-anchors opened first-hand for this tranche:** `09:1188--1213` (the
  contradiction frame and `lem:wrapper-no-bob-completion`), `09:1268--1313`
  (`eq:wrapper-first-bob-light`), `09:1315--1344`
  (`lem:final-reference-uniqueness`), `09:1346--1365`
  (`eq:wrapper-clean-count` and its two-line derivation).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the only import is `RoutingDynamics`,
  whose ledger row records the same exclusion.
* **Proof status.**  Every declaration is a transcription of a frozen display of
  the range above, a general property of one of those transcriptions, or one of
  the block's own derivations carried out in the kernel.  **No mathematics is
  added**, and no conclusion of `eq:wrapper-u-dense` is asserted anywhere.

## What this tranche closes in the predecessor module

`RoutingDynamics.lean` (SHA-256
`30554259FA94484328EC60E94F199F57DF0DB0ECC3B20CF6DDAE6B4B9E4AA64C`, which pins
`RoutedCertificateSystem.lean` at SHA-256
`B019BE34A74934390ABA184C5E5143DA6C53C7064AE0B9D2C5AF82502E3A73DF`) recorded two
**new** GAP-EXPOSED items, (9) and (10).  This module discharges both and touches
no other:

* **Item (9), the frontier is constructed only per certificate, discharged.**
  The banked record read: "`routeFuel_stops` gives each initial coordinate a
  stopping address, but the simultaneous indexing of all of them by a single `V`
  is not landed."  `frontierRoutes` is that single `V`: the union, over **all**
  initial coordinates, of the stopping addresses their routed branches reach, and
  `canonicalSystem` is a genuine `RoutedSystem` on it whose frontier is that
  union, whose certificates are the routed descendants themselves, and whose
  `prefixFree` field is discharged through the banked `prefixFree_of_stopping`.
* **Item (10), `eq:wrapper-frontier-conservation`'s first clause, discharged.**
  The banked record read: "`sum_v W_v >= q - e_0` still enters the banked
  counting as a binder, because summing the now-derived weights over the frontier
  needs (9)."  `frontierWeight` is `W_v` of `09:1257` -- the total weight of the
  certificates sitting at `v`, with every summand the **derived** kind weight of
  `RoutingDynamics.kindAlong` -- and `sum_frontierWeight_ge_card` sums them,
  yielding `q - e_0 <= sum_v W_v` in `frontier_conservation`.  At the consumption
  site `canonical_cleanCount` the banked `DenseWrapperFrontier.wrapperCleanCount`
  is applied with its `hcons` binder **supplied by a proof rather than assumed**.
  The banked statement is *not* edited; the binder is retired where it is
  consumed, which is the only place a binder can honestly be retired.

**Why the branching family and not `routeFuel`.**  The frozen rule of `09:1244`
routes a certificate "to both children if both qualify", and `09:1248` concludes
"total certificate weight never decreases" *because* a splitting certificate
leaves two half-weight descendants rather than one.  The banked `routeFuel`
follows the single `routeBit` branch, so the weight it carries to the frontier is
`1/2` at a split: it can prove `sum_v W_v >= (q-e_0)/2` and no more.
`singleBranch_weight_drops` exhibits exactly that loss at a probe where the
frozen rule really splits, so the branching family `descendants` is *forced* by
the frozen clause and is not a stylistic choice.  `routeFuel` is not discarded:
`routeFuel_route_mem_descendants` proves the banked iteration's stopping address
is always one of the branching family's, so the canonical system contains the
banked routing as the sub-family the frozen rule takes when nothing splits.

## Predecessor modules consumed **by pin**, never restated

* `Workspace.Types.Protocol` (through `LegacyNPCC.Core`, project-axiom-free):
  `Protocol`, `Protocol.cost`.
* `EthInapproximability.ParameterizedNP.DenseWeightedCount`: `descend`,
  `IsQueryNode`, `stoppingCapacity`, `PrefixFreeFrontier`.
* `EthInapproximability.ParameterizedNP.DenseSynchronisation`: `IsANode`.
* `EthInapproximability.ParameterizedNP.DenseWrapperFrontier`: `refRowFloor`,
  `CertKind` with `CertKind.weight`, `WrapperFrontier`, `vartheta`,
  `finalWeight`, and the headline `wrapperCleanCount`, consumed at its own
  interface.
* `EthInapproximability.ParameterizedNP.RoutedCertificateSystem`: `IsAlicePath`,
  `IsFirstBobNode`, `IsFinalAliceNode`, `RoutedCertificate`, `RoutedSystem`,
  `aliceLadder` with its frame lemmas.
* `EthInapproximability.ParameterizedNP.RoutingDynamics`: `rowsAt`, `Qualifies`,
  `splitsAt`, `routeBit`, `kindAlong`, `RoutedRowCertificate`,
  `initialRowCertificate`, `isANodeB`, `CompletedNoBob`, `routeFuel`,
  `prefixFree_of_stopping`, `completedNoBob_aliceLadder`.

## Canonical inhabitation

* **`RoutedSystem`: the deferred obligation registered by
  `ROUTED-CERTIFICATE-SYSTEM-001` and narrowed by `ROUTING-DYNAMICS-001` is now
  discharged at the paper's own construction.**  The frozen frame quantifies over
  an *arbitrary* alleged protocol `P` satisfying the completion frame condition
  of `lem:wrapper-no-bob-completion`, and starts one certificate in every
  coordinate outside `E_0` with the retention `A_r <= |R i|` of `09:1233--1235`.
  `canonicalSystem` takes exactly those two frozen inputs -- `hcomp` and `hR` --
  and returns the routed certificate system the frozen text builds from them:
  `canonicalSystem_cert_is_routed_initial` proves each of its certificates is a
  routed descendant of the paper's own `initialRowCertificate` at its coordinate,
  and no protocol, no width and no floor is chosen here.  The obligation is
  therefore discharged **at the paper's instance**, not at a synthetic one.
* `canonicalSystem_legal_instance` witnesses that the two frozen inputs are
  satisfiable at nondegenerate parameters, and `splitProbe_frontier_card`
  exhibits a frontier with *two* nodes produced by a genuine split, so the
  construction is not inhabited only where the routing is trivial.
* `canonical_cleanCount_consistent` is the hypothesis-consistency instance for
  the headline, and it is a **BEYOND-PAPER AUDIT**: the bundle is jointly
  satisfiable and the conclusion follows rather than `False`, at *self-chosen*
  `r = 1`, `A_0 = 1`, `e_0 = 1` (`q = 2` is then *derived* from `09:105`).  Of
  those, `r` is DEFINED by the schedule (`06:515` `q = 2^{A_wrap L_P^2}` with
  `09:105` `q = 2^r`), `A_0` is DEFINED by `09:1219` `A_0 = ceil(2 x_T m_G)`,
  and `e_0 = |E_0|` is fixed by the exceptional-set bookkeeping -- so this
  instance audits **our encoding at a point the paper never visits** and is
  strictly weaker evidence than the paper's own application point.  The
  legality weight is carried instead by `canonicalSystem_legal_instance`, which
  is parametric in `r` and `A_0` and therefore exhibits the two frozen inputs at
  *every* legal pair, the schedule's included.

## Aux-lemma battery and statement poles

General identity, composition, monotonicity and round-trip properties, all
proved: `descendants_zero`, `descendants_succ`, `descendants_of_stopped`,
`descendants_ne_nil`, `descendants_prefix`, `descendants_length_le`,
`descendants_nodup`, `descendants_isAlicePath`, `descendants_rows_floor`,
`descendants_length_le_r`, `routeFuel_route_mem_descendants`;
`mem_frontierRoutes_of_mem_coordRoutes`, `coordRoutes_nonempty`,
`frontierRoutes_nonempty`, `card_certIndex_eq`, `frontierWeight_nonneg`,
`frontierWeight_le_card`, `sum_frontierWeight_eq_sum_cert`.

Two **statement poles**: `singleBranch_weight_drops` (the single-branch
`routeFuel` trace loses half the weight at a genuine split, so the frozen
branching clause of `09:1244` is load-bearing for `09:1248`) and
`conservation_needs_the_coordinate_count` (the conservation clause is not a
formal truth about `W_v`: without the frozen cardinality input `q - e_0 <=
|Coord|` the bound fails at an empty coordinate set).

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for
this tranche (`frontier`, `conservation`, `certificate weight`, `Kraft`,
`prefix-free`, `prefix free`).  Every hit was opened and none states what any
declaration below states:

* `01-introduction.tex:101` and `02-preliminaries.tex:564` ("a weighted frontier",
  "the weighted frontier") are the **Stage-4 quotient-support** weighted frontier,
  a different mechanism from the wrapper's first-Bob frontier.
* `A-stage4-details.tex:263--266` -- "If `kappa_v` is its residual copy capacity
  and `h_v, z_v` are its routed template and witness masses, isolation gives
  `h_v + z_v <= kappa_v`.  Conservation gives `sum_v (kappa_v - h_v) <= b`" -- is
  the **same Stage-4 quotient-support** stopping count.  Its `kappa_v` is a
  residual copy capacity and its conserved quantity is a template/witness mass,
  not the certificate weight `W_v` of `09:1257`; the inequality is a different
  inequality about different symbols.  It is also unnumbered prose.
* `A-stage4-details.tex:318--319`, `371--373` and `387` ("terminal frontier") are
  the direct-bridge / two-stream terminal frontier; `371--373` is already recorded
  as unclaimed prose by `WRAPPER-PROJECTION-COVERS-001` and `390--391` is already
  assigned to `TERMINAL-TWO-STREAM-001`.  The one display in that range,
  `A-stage4-details.tex:394`, is the reader's **unnumbered, unlabelled**
  restatement of `eq:wrapper-u-dense` (frozen `09:262--263`), written in the
  reader's own notation (`\mathcal D_U`, `r_q`), which this module does **not**
  close.

**No reader item is claimed**, and the absence is a finding about the reader
artifact rather than an omission here.

## What is *not* claimed

`hDenseRung` is **neither discharged nor fed**; `eq:wrapper-u-dense` is asserted
nowhere below; GAP-EXPOSED items 2, 3, 4, 5 and 6 of
`ROUTED-CERTIFICATE-SYSTEM-001` are untouched; and **no route completion is
claimed.**  `eq:wrapper-first-bob-light` (`hlight`) and the final-node
classification of `09:1346--1350` (`hfinal`) remain the named binders they are in
the banked `wrapperCleanCount`: this tranche retires the *first* clause of
`eq:wrapper-frontier-conservation` and no other hypothesis.
-/

namespace EthInapproximability.ParameterizedNP.FrontierIndexing

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics

/-! ## §1  The branching descendant family (`09:1238--1248`)

"At an Alice query, route it to a child containing at least
`ceil(A_k/2) >= A_{k-1}` of those rows; **route it to both children if both
qualify**."

The banked `routeFuel` iterates the *unique* branch named by `routeBit`.  The
frozen rule is branching, and the branching is what makes `09:1248` true, so the
family of all routed descendants is the object this section builds.  Everything
it uses -- `rowsAt`, `Qualifies`, `splitsAt`, `routeBit`, `kindAlong`,
`isANodeB` -- is consumed from `RoutingDynamics` by pin. -/

section Descendants

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- **`09:1238--1248`, the routed descendants of one certificate.**

Starting from the node `p`, follow the frozen routing rule for `n` further Alice
queries: while the node is an Alice query strictly below the `r`-th, route to
*both* qualifying children when the certificate splits and to the unique
`routeBit` child otherwise; stop where the frozen stopping rule of `09:1250`
stops.  The result is the list of addresses the certificate's descendants
occupy.

**Deliberately not carried:** any weight, kind or count.  All three are frozen
*consequences* of the route (`kindAlong`, `CertKind.weight`), and carrying them
would put a conclusion into constructor data (mechanical rules M1--M10). -/
def descendants (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ℕ → List Bool → List (List Bool)
  | 0, p => [p]
  | n + 1, p =>
      if isANodeB (descend P p) = true ∧ p.length < r then
        (if splitsAt P R A0 r p = true then
            descendants P R A0 r n (p ++ [false]) ++ descendants P R A0 r n (p ++ [true])
          else descendants P R A0 r n (p ++ [routeBit P R A0 r p]))
      else [p]

/-- **Aux A1.**  With no queries left the certificate is where it is.  General. -/
@[simp] theorem descendants_zero (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ)
    (p : List Bool) : descendants P R A0 r 0 p = [p] := rfl

/-- **Aux A2.**  The defining step of the family.  General. -/
theorem descendants_succ (P : Protocol X Y Z) (R : Finset X) (A0 r n : ℕ) (p : List Bool) :
    descendants P R A0 r (n + 1) p =
      if isANodeB (descend P p) = true ∧ p.length < r then
        (if splitsAt P R A0 r p = true then
            descendants P R A0 r n (p ++ [false]) ++ descendants P R A0 r n (p ++ [true])
          else descendants P R A0 r n (p ++ [routeBit P R A0 r p]))
      else [p] := rfl

/-- **`09:1250--1252`, the stopping rule as a fixed point.**  A branch already
stopped -- the node is not an Alice query below the `r`-th -- consumes no further
query.  General. -/
theorem descendants_of_stopped {P : Protocol X Y Z} {R : Finset X} {A0 r n : ℕ}
    {p : List Bool} (h : ¬ (isANodeB (descend P p) = true ∧ p.length < r)) :
    descendants P R A0 r (n + 1) p = [p] := by
  rw [descendants_succ, if_neg h]

/-- **Aux A3 (no certificate is ever destroyed).**  The descendant family is never
empty: the frozen rule always routes a certificate somewhere.  General. -/
theorem descendants_ne_nil (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p : List Bool), descendants P R A0 r n p ≠ [] := by
  intro n
  induction n with
  | zero => intro p; simp
  | succ n ih =>
      intro p
      rw [descendants_succ]
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos h]
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs]
          intro hcon
          exact ih (p ++ [false]) (List.append_eq_nil_iff.mp hcon).1
        · rw [if_neg hs]; exact ih _
      · rw [if_neg h]; simp

/-- **Aux A4 (a descendant is a descendant).**  Every routed descendant's address
extends the address it was routed from.  General; this is the round-trip law that
makes the family a genuine dynamics on routes. -/
theorem descendants_prefix (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p q : List Bool), q ∈ descendants P R A0 r n p → p <+: q := by
  intro n
  induction n with
  | zero =>
      intro p q hq
      rw [descendants_zero, List.mem_singleton] at hq
      exact hq ▸ List.prefix_rfl
  | succ n ih =>
      intro p q hq
      rw [descendants_succ] at hq
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos h] at hq
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · exact List.IsPrefix.trans (List.prefix_append _ _) (ih _ _ hq)
          · exact List.IsPrefix.trans (List.prefix_append _ _) (ih _ _ hq)
        · rw [if_neg hs] at hq
          exact List.IsPrefix.trans (List.prefix_append _ _) (ih _ _ hq)
      · rw [if_neg h, List.mem_singleton] at hq
        exact hq ▸ List.prefix_rfl

/-- **Aux A5 (the routing consumes fuel).**  A descendant reached in at most `n`
further Alice queries sits at most `n` levels deeper.  General. -/
theorem descendants_length_le (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p q : List Bool), q ∈ descendants P R A0 r n p → q.length ≤ p.length + n := by
  intro n
  induction n with
  | zero =>
      intro p q hq
      rw [descendants_zero, List.mem_singleton] at hq
      simp [hq]
  | succ n ih =>
      intro p q hq
      rw [descendants_succ] at hq
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos h] at hq
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · have := ih _ _ hq; simp only [List.length_append, List.length_singleton] at this; omega
          · have := ih _ _ hq; simp only [List.length_append, List.length_singleton] at this; omega
        · rw [if_neg hs] at hq
          have := ih _ _ hq
          simp only [List.length_append, List.length_singleton] at this
          omega
      · rw [if_neg h, List.mem_singleton] at hq
        simp [hq]

/-- **`09:1244`, the two descendants of a split occupy *distinct* addresses.**

The frozen "route it to both children" sends the two halves down different
answer bits, so no address is repeated in the family.  This is what licenses the
frozen coordinate uniqueness of `09:1278--1280` at the canonical system below,
and what makes `W_v` a sum over genuinely distinct certificates.  General. -/
theorem descendants_nodup (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p : List Bool), (descendants P R A0 r n p).Nodup := by
  intro n
  induction n with
  | zero => intro p; simp
  | succ n ih =>
      intro p
      rw [descendants_succ]
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos h]
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs]
          refine List.Nodup.append (ih _) (ih _) ?_
          intro a ha ha'
          have h0 : p ++ [false] <+: a := descendants_prefix P R A0 r n _ _ ha
          have h1 : p ++ [true] <+: a := descendants_prefix P R A0 r n _ _ ha'
          have e0 : p ++ [false] = a.take ((p ++ [false]).length) :=
            List.prefix_iff_eq_take.mp h0
          have e1 : p ++ [true] = a.take ((p ++ [true]).length) :=
            List.prefix_iff_eq_take.mp h1
          have hlen : (p ++ [false]).length = (p ++ [true]).length := by simp
          rw [hlen] at e0
          have heq : p ++ [false] = p ++ [true] := e0.trans e1.symm
          simp at heq
        · rw [if_neg hs]; exact ih _
      · rw [if_neg h]; simp

/-- **`09:1250`, the routed branch never passes a Bob query.**  Every descendant's
address is again an Alice-only route.  General. -/
theorem descendants_isAlicePath (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p : List Bool), IsAlicePath P p →
      ∀ q ∈ descendants P R A0 r n p, IsAlicePath P q := by
  intro n
  induction n with
  | zero =>
      intro p hp q hq
      rw [descendants_zero, List.mem_singleton] at hq
      exact hq ▸ hp
  | succ n ih =>
      intro p hp q hq
      rw [descendants_succ] at hq
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · have hnode : IsANode (descend P p) := isANodeB_eq_true_iff.mp h.1
        have hchild : ∀ b : Bool, IsAlicePath P (p ++ [b]) := fun b =>
          isAlicePath_append hp ⟨hnode, isAlicePath_nil _⟩
        rw [if_pos h] at hq
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · exact ih _ (hchild false) q hq
          · exact ih _ (hchild true) q hq
        · rw [if_neg hs] at hq
          exact ih _ (hchild _) q hq
      · rw [if_neg h, List.mem_singleton] at hq
        exact hq ▸ hp

/-- **`09:1238--1244`, the frozen row floor is restored at every descendant.**

"At remaining selector capacity `2^k`, a certificate consists of at least `A_k`
reference rows"; the routing rule keeps that true one level down, at both
children of a split (each qualifies by definition of `splitsAt`) and at the
unique `routeBit` child otherwise (`routeBit_qualifies`).  So the whole family
consists of legal certificates. -/
theorem descendants_rows_floor (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p : List Bool),
      refRowFloor A0 (r - p.length) ≤ (rowsAt P R p).card →
        ∀ q ∈ descendants P R A0 r n p,
          refRowFloor A0 (r - q.length) ≤ (rowsAt P R q).card := by
  intro n
  induction n with
  | zero =>
      intro p hp q hq
      rw [descendants_zero, List.mem_singleton] at hq
      exact hq ▸ hp
  | succ n ih =>
      intro p hp q hq
      rw [descendants_succ] at hq
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · have hnode : IsANode (descend P p) := isANodeB_eq_true_iff.mp h.1
        have hshift : ∀ b : Bool, r - (p ++ [b]).length = r - p.length - 1 := by
          intro b; simp only [List.length_append, List.length_singleton]; omega
        have hchild : ∀ b : Bool, Qualifies P R A0 r p b →
            refRowFloor A0 (r - (p ++ [b]).length) ≤ (rowsAt P R (p ++ [b])).card := by
          intro b hb
          rw [hshift b]
          exact hb
        rw [if_pos h] at hq
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · exact ih _ (hchild false (qualifies_false_of_splitsAt hs)) q hq
          · exact ih _ (hchild true (qualifies_true_of_splitsAt hs)) q hq
        · rw [if_neg hs] at hq
          exact ih _ (hchild _ (routeBit_qualifies hnode h.2 hp)) q hq
      · rw [if_neg h, List.mem_singleton] at hq
        exact hq ▸ hp

/-- **`09:1250--1252`, the frozen stopping dichotomy for the whole family.**

"Stop each routed branch at its first Bob query, or after `r` Alice queries."
Under the completion frame condition of `lem:wrapper-no-bob-completion`, every
descendant of a certificate at depth `d` routed for the remaining `r - d` queries
sits at one of the two frozen addresses.  This is the branching analogue of the
banked `routeFuel_stops`. -/
theorem descendants_stop {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) :
    ∀ (n : ℕ) (p : List Bool), IsAlicePath P p → p.length + n = r →
      ∀ q ∈ descendants P R A0 r n p,
        IsFirstBobNode P r q ∨ IsFinalAliceNode P r q := by
  intro n
  induction n with
  | zero =>
      intro p hp hlen q hq
      rw [descendants_zero, List.mem_singleton] at hq
      exact Or.inr ⟨hq ▸ hp, by rw [hq]; omega⟩
  | succ n ih =>
      intro p hp hlen q hq
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · have hnode : IsANode (descend P p) := isANodeB_eq_true_iff.mp h.1
        have hchild : ∀ b : Bool, IsAlicePath P (p ++ [b]) := fun b =>
          isAlicePath_append hp ⟨hnode, isAlicePath_nil _⟩
        have hchildlen : ∀ b : Bool, (p ++ [b]).length + n = r := by
          intro b; simp only [List.length_append, List.length_singleton]; omega
        rw [descendants_succ, if_pos h] at hq
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · exact ih _ (hchild false) (hchildlen false) q hq
          · exact ih _ (hchild true) (hchildlen true) q hq
        · rw [if_neg hs] at hq
          exact ih _ (hchild _) (hchildlen _) q hq
      · rw [descendants_of_stopped h, List.mem_singleton] at hq
        have hlt : p.length < r := by omega
        have hna : ¬ IsANode (descend P p) := fun hcon =>
          h ⟨isANodeB_eq_true_iff.mpr hcon, hlt⟩
        have hqn : IsQueryNode (descend P p) := hcomp _ hp hlt
        exact Or.inl ⟨hq ▸ hp, hq ▸ isBobNode_of_not_isANode hqn hna,
          by rw [hq]; exact hlt⟩

/-- **Aux A6.**  No frontier address outruns the `r` Alice queries.  General
consequence of the stopping dichotomy. -/
theorem descendants_length_le_r {P : Protocol X Y Z} {R : Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) {n : ℕ} {p : List Bool} (hp : IsAlicePath P p)
    (hlen : p.length + n = r) {q : List Bool} (hq : q ∈ descendants P R A0 r n p) :
    q.length ≤ r := by
  rcases descendants_stop hcomp n p hp hlen q hq with hstop | hstop
  · exact le_of_lt hstop.2.2
  · exact le_of_eq hstop.2

/-- **`09:1248`, "Thus total certificate weight never decreases" -- proved.**

The weight of a certificate at `p` is at most the total weight of its routed
descendants.  The three frozen sentences of `09:1244--1248` are exactly what
makes this true: a unique routing preserves the kind, and a split replaces one
certificate of weight at most `1` by two of weight `1/2` each.  Every weight here
is the **derived** `kindAlong` weight, not an assigned one. -/
theorem weight_le_sum_descendants (P : Protocol X Y Z) (R : Finset X) (A0 r : ℕ) :
    ∀ (n : ℕ) (p : List Bool),
      (kindAlong P R A0 r p).weight
        ≤ ((descendants P R A0 r n p).map
            (fun q => (kindAlong P R A0 r q).weight)).sum := by
  intro n
  induction n with
  | zero => intro p; simp
  | succ n ih =>
      intro p
      rw [descendants_succ]
      by_cases h : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos h]
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.map_append, List.sum_append]
          have hk : ∀ b : Bool, kindAlong P R A0 r (p ++ [b]) = CertKind.low := by
            intro b; rw [kindAlong_append_bit, hs]; simp
          have h0 := ih (p ++ [false])
          have h1 := ih (p ++ [true])
          rw [hk false] at h0
          rw [hk true] at h1
          have hw : (CertKind.low).weight = 1 / 2 := rfl
          rw [hw] at h0 h1
          have hle : (kindAlong P R A0 r p).weight ≤ 1 := CertKind.weight_le_one _
          linarith
        · rw [if_neg hs]
          have hsf : splitsAt P R A0 r p = false := by
            cases hb : splitsAt P R A0 r p
            · rfl
            · exact absurd hb hs
          have hk : kindAlong P R A0 r (p ++ [routeBit P R A0 r p]) = kindAlong P R A0 r p := by
            rw [kindAlong_append_bit, hsf]
            simp
          have := ih (p ++ [routeBit P R A0 r p])
          rwa [hk] at this
      · rw [if_neg h]; simp

/-- **`09:1235--1236` and `09:1248` chained at the root.**  "Start one clean reference
certificate in every coordinate outside `E_0`, each with weight one", and weight
never decreases: the routed descendants of one initial coordinate carry total
weight at least one. -/
theorem one_le_sum_descendants_root (P : Protocol X Y Z) (R : Finset X) (A0 r n : ℕ) :
    (1 : ℝ) ≤ ((descendants P R A0 r n ([] : List Bool)).map
        (fun q => (kindAlong P R A0 r q).weight)).sum := by
  have h := weight_le_sum_descendants P R A0 r n ([] : List Bool)
  rwa [kindAlong_nil, show (CertKind.clean).weight = 1 from rfl] at h

/-- **The banked `routeFuel` is the non-splitting trace of the frozen rule.**

`routeFuel` follows the single `routeBit` child; the frozen rule of `09:1244`
also keeps the other child when both qualify.  So the banked iteration's stopping
address is always one of this family's addresses -- the two constructions agree
wherever nothing splits, and the family is the strictly larger object the frozen
clause demands.  General round-trip law. -/
theorem routeFuel_route_mem_descendants {P : Protocol X Y Z} {Coord : Type*} {r A0 : ℕ} :
    ∀ (n : ℕ) (c : RoutedRowCertificate P Coord r A0),
      (routeFuel n c).route ∈ descendants P c.refRows A0 r n c.route := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
      intro c
      by_cases h : isANodeB (descend P c.route) = true ∧ c.route.length < r
      · have hstep : routeFuel (n + 1) c
            = routeFuel n (c.routedStep (isANodeB_eq_true_iff.mp h.1) h.2) := by
          simp [routeFuel, h]
        have hmem : (routeFuel n (c.routedStep (isANodeB_eq_true_iff.mp h.1) h.2)).route
            ∈ descendants P c.refRows A0 r n (c.route ++ [routeBit P c.refRows A0 r c.route]) :=
          ih (c.routedStep (isANodeB_eq_true_iff.mp h.1) h.2)
        rw [hstep, descendants_succ, if_pos h]
        by_cases hs : splitsAt P c.refRows A0 r c.route = true
        · have hbit : routeBit P c.refRows A0 r c.route = false := by
            unfold routeBit
            rw [if_pos (qualifies_false_of_splitsAt hs)]
          rw [hbit] at hmem
          rw [if_pos hs]
          exact List.mem_append_left _ hmem
        · rw [if_neg hs]
          exact hmem
      · rw [routeFuel_of_stopped c n h, descendants_of_stopped h, List.mem_singleton]

end Descendants

/-! ## §2  The canonical frontier and the canonical routed system
(`09:1233--1236`, `09:1250--1259`)

`ROUTING-DYNAMICS-001` GAP-EXPOSED item (9), verbatim: "the frontier is
constructed only *per certificate* -- `routeFuel_stops` gives each initial
coordinate a stopping address, but the simultaneous indexing of all of them by a
single `V` is not landed."

The frozen construction starts one certificate in every coordinate outside `E_0`
(`09:1235--1236`) and stops each routed branch by one of the two rules of
`09:1250--1252`.  The frontier is therefore the union of the stopping addresses
of **all** initial coordinates, and that union is what `frontierRoutes` builds.

**On the universe of `Coord`.**  The frozen index set of outer coordinates is
`[q]`, a finite type in `Type`; the banked `RoutedSystem` takes its three index
types in one universe, so `Coord` is taken in `Type` here.  No generality is lost
at the paper's own instance. -/

section Frontier

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1250--1252` at one initial coordinate.**  The stopping addresses reached
by the routed descendants of the clean certificate started in coordinate `i`. -/
def coordRoutes (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) (i : Coord) :
    Finset (List Bool) :=
  (descendants P (R i) A0 r r ([] : List Bool)).toFinset

/-- **`09:1252--1253`, the frontier, indexed once for all coordinates (item (9)).**

"If `v` is a frontier node ...": the frontier of the routed certificate system is
the set of stopping addresses of the branches started in *every* coordinate
outside `E_0`, taken together. -/
def frontierRoutes (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) :
    Finset (List Bool) :=
  Finset.univ.biUnion fun i => coordRoutes P R A0 r i

/-- The frontier node type: one index `V` for the whole frontier. -/
abbrev FrontierNode (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) :=
  {p : List Bool // p ∈ frontierRoutes P R A0 r}

/-- The certificate index type: a routed descendant is named by the coordinate it
descends from together with the address it stopped at. -/
abbrev CertIndex (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) :=
  Σ i : Coord, {p : List Bool // p ∈ coordRoutes P R A0 r i}

/-- **Aux B1.**  A coordinate's stopping addresses are frontier addresses.
General. -/
theorem mem_frontierRoutes_of_mem_coordRoutes {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} {i : Coord} {p : List Bool} (h : p ∈ coordRoutes P R A0 r i) :
    p ∈ frontierRoutes P R A0 r :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩

/-- **Aux B2.**  Every frontier address is some coordinate's stopping address.
General. -/
theorem exists_coord_of_mem_frontierRoutes {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} {p : List Bool} (h : p ∈ frontierRoutes P R A0 r) :
    ∃ i : Coord, p ∈ coordRoutes P R A0 r i := by
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
  exact ⟨i, hi⟩

omit [Fintype Coord] in
/-- **Aux B3 (no coordinate loses its certificate).**  Each coordinate's stopping
address set is nonempty.  General. -/
theorem coordRoutes_nonempty (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (i : Coord) : (coordRoutes P R A0 r i).Nonempty := by
  have h := descendants_ne_nil P (R i) A0 r r ([] : List Bool)
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨p, List.mem_toFinset.mpr hp⟩

/-- **Aux B4.**  The frontier itself is nonempty whenever some coordinate is
started.  General. -/
theorem frontierRoutes_nonempty (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (i : Coord) : (frontierRoutes P R A0 r).Nonempty := by
  obtain ⟨p, hp⟩ := coordRoutes_nonempty P R A0 r i
  exact ⟨p, mem_frontierRoutes_of_mem_coordRoutes hp⟩

/-- **Aux B4a (the certificate census).**  The number of routed certificates in
the system is the total number of stopping addresses reached, coordinate by
coordinate.  General. -/
theorem card_certIndex_eq (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) :
    Fintype.card (CertIndex P R A0 r)
      = ∑ i : Coord, (coordRoutes P R A0 r i).card := by
  simp [CertIndex, Fintype.card_sigma, Fintype.card_coe]

/-- **`09:1250--1252` on the whole frontier.**  Every frontier address is one of
the two frozen stopping states. -/
theorem frontierRoutes_stop {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) {p : List Bool} (h : p ∈ frontierRoutes P R A0 r) :
    IsFirstBobNode P r p ∨ IsFinalAliceNode P r p := by
  obtain ⟨i, hi⟩ := exists_coord_of_mem_frontierRoutes h
  exact descendants_stop hcomp r ([] : List Bool) (isAlicePath_nil P) (by simp) p
    (List.mem_toFinset.mp hi)

omit [Fintype Coord] in
/-- **`09:1238--1239` at every certificate of the frontier.**  A routed descendant
of coordinate `i` still meets the frozen floor `A_{r-d}`. -/
theorem coordRoutes_rows_floor {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    {i : Coord} (hR : refRowFloor A0 r ≤ (R i).card) {p : List Bool}
    (hp : p ∈ coordRoutes P R A0 r i) :
    refRowFloor A0 (r - p.length) ≤ (rowsAt P (R i) p).card := by
  refine descendants_rows_floor P (R i) A0 r r ([] : List Bool) ?_ p (List.mem_toFinset.mp hp)
  simpa using hR

omit [Fintype Coord] in
/-- **`09:1250` at every certificate of the frontier.** -/
theorem coordRoutes_isAlicePath {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    {i : Coord} {p : List Bool} (hp : p ∈ coordRoutes P R A0 r i) : IsAlicePath P p :=
  descendants_isAlicePath P (R i) A0 r r ([] : List Bool) (isAlicePath_nil P) p
    (List.mem_toFinset.mp hp)

omit [Fintype Coord] in
/-- **`09:1250` at every certificate of the frontier.** -/
theorem coordRoutes_length_le {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) {i : Coord} {p : List Bool}
    (hp : p ∈ coordRoutes P R A0 r i) : p.length ≤ r :=
  descendants_length_le_r hcomp (isAlicePath_nil P) (by simp) (List.mem_toFinset.mp hp)

/-- **`09:1235--1248`, the routed certificate at a frontier index.**

The certificate named by `(i, p)` is the paper's own initial certificate of
coordinate `i` -- same coordinate, same reference rows -- carried by the frozen
routing rule to the address `p`.  Its three laws are the frozen ones, each
supplied by a theorem of §1 rather than assumed. -/
def rowCertAt {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) : RoutedRowCertificate P Coord r A0 where
  coord := x.1
  refRows := R x.1
  route := x.2.val
  route_alice := coordRoutes_isAlicePath x.2.property
  route_len_le := coordRoutes_length_le hcomp x.2.property
  rows_floor := coordRoutes_rows_floor (hR x.1) x.2.property

omit [Fintype Coord] in
/-- **Aux B5.**  The routed certificate keeps its coordinate.  General. -/
@[simp] theorem rowCertAt_coord {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) : (rowCertAt hcomp hR x).coord = x.1 := rfl

omit [Fintype Coord] in
/-- **Aux B6.**  It keeps the coordinate's initial reference rows: the frozen rule
moves a certificate, it never re-seeds one.  General. -/
@[simp] theorem rowCertAt_refRows {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) : (rowCertAt hcomp hR x).refRows = R x.1 := rfl

omit [Fintype Coord] in
/-- **Aux B7.**  Its route is its frontier address.  General. -/
@[simp] theorem rowCertAt_route {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) : (rowCertAt hcomp hR x).route = x.2.val := rfl

omit [Fintype Coord] in
/-- **`09:1235--1236`, canonical inhabitation, made explicit.**

Every certificate of the canonical system is a routed descendant of **the paper's
own initial placement** at its coordinate: same coordinate, same reference rows,
and an address the frozen routing rule reaches from the root.  Nothing in the
construction is chosen. -/
theorem canonicalSystem_cert_is_routed_initial {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) :
    (rowCertAt hcomp hR x).coord = (initialRowCertificate P x.1 (R x.1) r A0 (hR x.1)).coord ∧
      (rowCertAt hcomp hR x).refRows
        = (initialRowCertificate P x.1 (R x.1) r A0 (hR x.1)).refRows ∧
      (rowCertAt hcomp hR x).route ∈
        descendants P (initialRowCertificate P x.1 (R x.1) r A0 (hR x.1)).refRows A0 r r
          (initialRowCertificate P x.1 (R x.1) r A0 (hR x.1)).route :=
  ⟨rfl, rfl, List.mem_toFinset.mp x.2.property⟩

/-- **`09:1250--1259`, the canonical routed certificate system (item (9)).**

The routed certificate system the frozen text builds from its two inputs -- an
alleged protocol satisfying the completion frame condition of
`lem:wrapper-no-bob-completion`, and the retention `A_r <= |R i|` of
`09:1233--1235` at every coordinate outside `E_0`.  Its frontier is the single
index `V` of **all** stopping addresses, its certificates are the routed
descendants of the paper's own initial placement, its prefix-freeness is the
banked `prefixFree_of_stopping` at those addresses, and the frozen coordinate
uniqueness of `09:1278--1280` holds because the split of `09:1244` sends its two
descendants to distinct addresses (`descendants_nodup`).

**Deliberately not fields:** `W_v`, `c`, `K_B`.  They are the routing's output and
are computed below (`frontierWeight`) or supplied at the banked counting
interface. -/
def canonicalSystem {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) :
    RoutedSystem P Coord (CertIndex P R A0 r) (FrontierNode P R A0 r) r A0 where
  node := Subtype.val
  prefixFree :=
    prefixFree_of_stopping (P := P) (r := r) Subtype.val
      (fun v => frontierRoutes_stop hcomp v.property)
      (fun _ _ h => Subtype.ext h)
  firstBob := fun v => decide (v.val.length < r)
  firstBob_spec := by
    intro v hv
    have hlt : v.val.length < r := of_decide_eq_true hv
    rcases frontierRoutes_stop hcomp v.property with hstop | hstop
    · exact hstop
    · exact absurd hstop.2 (by omega)
  final_spec := by
    intro v hv
    have hlt : ¬ (v.val.length < r) := of_decide_eq_false hv
    rcases frontierRoutes_stop hcomp v.property with hstop | hstop
    · exact absurd hstop.2.2 hlt
    · exact hstop
  place := fun x => ⟨x.2.val, mem_frontierRoutes_of_mem_coordRoutes x.2.property⟩
  cert := fun x => (rowCertAt hcomp hR x).toRoutedCertificate
  cert_at := fun _ => rfl
  coordUnique := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hplace hcoord
    have hij : i = j := hcoord
    subst hij
    have hpq : (p : List Bool) = (q : List Bool) := by
      have := congrArg (fun v : FrontierNode P R A0 r => (v : List Bool)) hplace
      simpa using this
    have hp : p = q := Subtype.ext hpq
    subst hp
    rfl

/-- **Aux B8.**  The canonical system's addresses are the frontier's elements.
General. -/
@[simp] theorem canonicalSystem_node {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode P R A0 r) : (canonicalSystem hcomp hR).node v = v.val := rfl

/-- **`09:1244--1248` at the canonical system.**  Every certificate's kind is the
**derived** `kindAlong` of the routing, never free constructor data. -/
@[simp] theorem canonicalSystem_cert_kind {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) :
    ((canonicalSystem hcomp hR).cert x).kind = kindAlong P (R x.1) A0 r x.2.val := rfl

/-- **`09:1235--1236`, `09:1246` at the canonical system.**  Every certificate's weight
is the derived kind's weight. -/
@[simp] theorem canonicalSystem_cert_weight {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (x : CertIndex P R A0 r) :
    ((canonicalSystem hcomp hR).cert x).weight
      = (kindAlong P (R x.1) A0 r x.2.val).weight := rfl

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), at the
canonical system.**  `sum_v kappa_v <= q`, obtained from the banked Kraft
inequality through the banked bridge.  Not re-proved here.

The `q` of `09:1264` is stated here in its `2^r` form; the substitution is
licensed by `09:105`, "Let `q = 2^r` be the scale-alignment width", and is
independently corroborated by `09:1221` (`A_k = 2^k A_0`) with `09:1234--1235`
(`A_r = q A_0`). -/
theorem canonicalSystem_sum_capacity_le_width {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) :
    ∑ v : FrontierNode P R A0 r, stoppingCapacity r v.val.length ≤ 2 ^ r :=
  (canonicalSystem hcomp hR).sum_capacity_le_width

end Frontier

/-! ## §3  `W_v` and the first clause of `eq:wrapper-frontier-conservation`
(`09:1257`, `09:1259--1266`)

`ROUTING-DYNAMICS-001` GAP-EXPOSED item (10), verbatim:
"`eq:wrapper-frontier-conservation`'s first clause `sum_v W_v >= q - e_0` still
enters the banked counting as a binder, because summing the now-derived weights
over the frontier needs (9)."

With (9) landed the sum is available, and the clause becomes a theorem. -/

section Conservation

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1257`, `W_v = total certificate weight at v`.**

The sum of the **derived** weights of the certificates sitting at `v`.  Every
summand is `CertKind.weight (kindAlong ...)`: computed from the routing by
`RoutingDynamics`, never assigned. -/
noncomputable def frontierWeight (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : ℝ :=
  ∑ x : CertIndex P R A0 r,
    if x.2.val = v.val then (kindAlong P (R x.1) A0 r x.2.val).weight else 0

/-- **Aux C1.**  `W_v` is nonnegative -- certificate weights are.  General. -/
theorem frontierWeight_nonneg (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) : 0 ≤ frontierWeight P R A0 r v := by
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases h : x.2.val = v.val
  · rw [if_pos h]; exact le_of_lt (CertKind.weight_pos _)
  · rw [if_neg h]

/-- **Aux C2.**  `W_v` never exceeds the number of certificates in the system:
each carries weight at most the clean weight `1` (`09:1235--1236`, `09:1246`).
General. -/
theorem frontierWeight_le_card (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (v : FrontierNode P R A0 r) :
    frontierWeight P R A0 r v ≤ (Fintype.card (CertIndex P R A0 r) : ℝ) := by
  have hle : ∀ x : CertIndex P R A0 r,
      (if x.2.val = v.val then (kindAlong P (R x.1) A0 r x.2.val).weight else 0) ≤ 1 := by
    intro x
    by_cases h : x.2.val = v.val
    · rw [if_pos h]; exact CertKind.weight_le_one _
    · rw [if_neg h]; norm_num
  calc frontierWeight P R A0 r v
      ≤ ∑ _x : CertIndex P R A0 r, (1 : ℝ) := Finset.sum_le_sum fun x _ => hle x
    _ = (Fintype.card (CertIndex P R A0 r) : ℝ) := by
        simp [Finset.card_univ]

/-- **Aux C3.**  The frontier sum of `W_v` is the total certificate weight of the
system: every certificate is counted at exactly one frontier node.  General. -/
theorem sum_frontierWeight_eq_sum_cert (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) :
    ∑ v : FrontierNode P R A0 r, frontierWeight P R A0 r v
      = ∑ x : CertIndex P R A0 r, (kindAlong P (R x.1) A0 r x.2.val).weight := by
  classical
  unfold frontierWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hmem : (⟨x.2.val, mem_frontierRoutes_of_mem_coordRoutes x.2.property⟩ :
      FrontierNode P R A0 r) ∈ (Finset.univ : Finset (FrontierNode P R A0 r)) :=
    Finset.mem_univ _
  rw [Finset.sum_eq_single (⟨x.2.val, mem_frontierRoutes_of_mem_coordRoutes x.2.property⟩ :
      FrontierNode P R A0 r)]
  · simp
  · intro b _ hb
    refine if_neg fun hcon => hb (Subtype.ext hcon.symm)
  · intro h; exact absurd hmem h

/-- **Aux C4.**  The certificates group by the coordinate they descend from.
General. -/
theorem sum_cert_eq_sum_coord (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) :
    ∑ x : CertIndex P R A0 r, (kindAlong P (R x.1) A0 r x.2.val).weight
      = ∑ i : Coord, ∑ p ∈ coordRoutes P R A0 r i, (kindAlong P (R i) A0 r p).weight := by
  classical
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_coe_sort (coordRoutes P R A0 r i) fun p => (kindAlong P (R i) A0 r p).weight

omit [Fintype Coord] in
/-- **`09:1235--1236` and `09:1248` at one coordinate, in Finset form.**  The clean
certificate started in coordinate `i` leaves total weight at least one on the
frontier.  The dedup is harmless because the split of `09:1244` sends its two
descendants to distinct addresses (`descendants_nodup`). -/
theorem one_le_sum_coordRoutes (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    (i : Coord) :
    (1 : ℝ) ≤ ∑ p ∈ coordRoutes P R A0 r i, (kindAlong P (R i) A0 r p).weight := by
  classical
  have hnodup := descendants_nodup P (R i) A0 r r ([] : List Bool)
  have hsum := List.sum_toFinset (fun p => (kindAlong P (R i) A0 r p).weight) hnodup
  rw [coordRoutes]
  rw [hsum]
  exact one_le_sum_descendants_root P (R i) A0 r r

/-- **`eq:wrapper-frontier-conservation`, first clause, at the coordinate count
(`09:1262`).**  `sum_v W_v >= |Coord|`: the frozen conservation with the frozen
right-hand side still in its structural form, one unit per coordinate outside
`E_0`. -/
theorem sum_frontierWeight_ge_card (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ) :
    (Fintype.card Coord : ℝ) ≤ ∑ v : FrontierNode P R A0 r, frontierWeight P R A0 r v := by
  classical
  rw [sum_frontierWeight_eq_sum_cert, sum_cert_eq_sum_coord]
  calc (Fintype.card Coord : ℝ) = ∑ _i : Coord, (1 : ℝ) := by simp [Finset.card_univ]
    _ ≤ ∑ i : Coord, ∑ p ∈ coordRoutes P R A0 r i, (kindAlong P (R i) A0 r p).weight :=
        Finset.sum_le_sum fun i _ => one_le_sum_coordRoutes P R A0 r i

/-- **`eq:wrapper-frontier-conservation`, first clause (`09:1259--1266`) -- proved.**

"Prefix-freeness and conservation give `sum_v W_v >= q - e_0`."

`hcoord` is the frozen cardinality input of `09:1235--1236`: certificates are
started in every coordinate *outside* `E_0`, of which there are `q - e_0`.  It is
a statement about which coordinates are started, tracked by the exceptional-set
bookkeeping of `WrapperProjectionCovers`, and is carried as the explicit binder
it is rather than folded into the construction (mechanical rules M1--M10).

Everything else is derived: the weights are `RoutingDynamics.kindAlong`'s, the
frontier is `frontierRoutes`, and the conservation is `09:1248` summed. -/
theorem frontier_conservation (P : Protocol X Y Z) (R : Coord → Finset X) (A0 r : ℕ)
    {q e0 : ℝ} (hcoord : q - e0 ≤ (Fintype.card Coord : ℝ)) :
    q - e0 ≤ ∑ v : FrontierNode P R A0 r, frontierWeight P R A0 r v :=
  le_trans hcoord (sum_frontierWeight_ge_card P R A0 r)

/-- **`eq:wrapper-clean-count` (`09:1352--1357`) at the canonical system, with the
conservation binder retired.**

The banked `DenseWrapperFrontier.wrapperCleanCount` is applied **verbatim, at its
own interface** to the canonical system's frontier, with its `hcons` argument
supplied by `frontier_conservation` instead of assumed.  The banked statement is
untouched: a binder can only be retired where it is consumed, and this is that
site.

`hq : q = 2^r` is not an assumption about a free parameter: it is the frozen
width identification of `09:105`, "Let `q = 2^r` be the scale-alignment width",
carried as a binder because the banked `wrapperCleanCount` takes it as one.  It
is independently corroborated by `09:1221` with `09:1234--1235`.

What remains a named binder is exactly what `ROUTING-DYNAMICS-001` says remains:
`hlight` is `eq:wrapper-first-bob-light` (`09:1312`), and `hfinal` is the
final-node classification of `09:1346--1350` licensed by
`lem:final-reference-uniqueness`.  Neither is discharged here, and `hDenseRung`
is neither discharged nor fed. -/
theorem canonical_cleanCount {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (certOpt : FrontierNode P R A0 r → Option CertKind) {q e0 : ℝ}
    (hq : q = (2 : ℝ) ^ r) (hcoord : q - e0 ≤ (Fintype.card Coord : ℝ))
    (hlight : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      frontierWeight P R A0 r v
        ≤ vartheta * ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℝ))
    (hfinal : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
      frontierWeight P R A0 r v ≤ finalWeight (certOpt v)) :
    q - e0 / (1 - vartheta)
        ≤ (((canonicalSystem hcomp hR).toWrapperFrontier.cleanNodes certOpt).card : ℝ)
      ∧ (canonicalSystem hcomp hR).toWrapperFrontier.bobCapacity
          + (((canonicalSystem hcomp hR).toWrapperFrontier.splitNodes certOpt).card : ℝ)
        ≤ e0 / (1 - vartheta) :=
  wrapperCleanCount (canonicalSystem hcomp hR).toWrapperFrontier certOpt
    (frontierWeight P R A0 r) hq hlight hfinal
    (frontier_conservation P R A0 r hcoord)

/-- **Statement pole for `frontier_conservation`.**

The conservation clause is not a formal truth about `W_v`: it needs the frozen
count of coordinates started.  With no coordinate outside `E_0` the frontier is
empty and `sum_v W_v = 0`, so the frozen right-hand side `q - e_0` must really be
bounded by the number of started coordinates.  Here `q = 1`, `e_0 = 0`, and the
conclusion `1 <= 0` fails, so `hcoord` is load-bearing. -/
theorem conservation_needs_the_coordinate_count
    (P : Protocol Bool Bool Bool) (R : (Fin 0) → Finset Bool) (A0 r : ℕ) :
    ¬ ((1 : ℝ) - 0 ≤ ∑ v : FrontierNode P R A0 r, frontierWeight P R A0 r v) := by
  have hempty : ∀ v : FrontierNode P R A0 r, False := by
    intro v
    obtain ⟨i, -⟩ := exists_coord_of_mem_frontierRoutes v.property
    exact i.elim0
  have hsum : ∑ v : FrontierNode P R A0 r, frontierWeight P R A0 r v = 0 := by
    refine Finset.sum_eq_zero fun v _ => (hempty v).elim
  rw [hsum]
  norm_num

end Conservation

/-! ## §4  Non-vacuity, canonical legality, and the branching pole

`canonicalSystem` is the paper's own construction at the paper's own inputs, so
its canonical-inhabitation obligation is discharged by the definition itself.
What has to be checked is that those inputs are *satisfiable at legal,
nondegenerate parameters* -- otherwise the construction would be vacuous -- and
that the branching clause of `09:1244` is doing real work. -/

section Probes

/-- The probe protocol at which the frozen rule genuinely **splits**: one Alice
query whose predicate sends the two available rows to different children.

**BEYOND-PAPER label.**  The frozen text fixes no alphabet, no wrapper width and
no initial row floor, so these parameters are *ours*: this instance audits our
encoding at a point the paper never visits, and is strictly weaker evidence than
the paper's own application point.  It is used only to show that the split branch
of the frozen rule is reachable. -/
def splitProbe : Protocol Bool Bool Bool :=
  aliceLadder (X := Bool) (Y := Bool) (fun x => x) true 1

/-- **BEYOND-PAPER audit probe: the frozen split really branches.**  At the probe
the certificate is routed to **both** children, so the descendant family has two
distinct addresses where the banked single-branch `routeFuel` has one. -/
theorem splitProbe_descendants :
    descendants splitProbe Finset.univ 1 1 1 ([] : List Bool) = [[false], [true]] := by
  decide

/-- **BEYOND-PAPER audit probe: the canonical frontier has two nodes.**  With one
started coordinate the frozen split already produces a two-node frontier, so the
frontier indexing of §2 is not inhabited only at a one-point frontier. -/
theorem splitProbe_frontier_card :
    (frontierRoutes splitProbe (fun _ : Fin 1 => (Finset.univ : Finset Bool)) 1 1).card = 2 := by
  decide

/-- **Statement pole: the frozen branching clause of `09:1244` is load-bearing.**

`09:1248` says total certificate weight never decreases.  The banked `routeFuel`
follows only the `routeBit` child, and at the probe that child is a **low**
certificate of weight `1/2`, strictly below the weight `1` the clean certificate
started with.  So a frontier built from `routeFuel` alone could only prove
`sum_v W_v >= (q - e_0)/2`, and the branching family of §1 is forced by the frozen
"route it to both children if both qualify" rather than chosen. -/
theorem singleBranch_weight_drops :
    (kindAlong splitProbe Finset.univ 1 1 [false]).weight
      < (kindAlong splitProbe Finset.univ 1 1 ([] : List Bool)).weight := by
  have h0 : kindAlong splitProbe Finset.univ 1 1 [false] = CertKind.low := by decide
  have h1 : kindAlong splitProbe Finset.univ 1 1 ([] : List Bool) = CertKind.clean := by decide
  rw [h0, h1]
  norm_num [CertKind.weight]

/-- **The branching family restores the frozen conservation at the same probe.**
Summing the two half-weight descendants returns the weight `1` the initial clean
certificate started with, which is `09:1248` at a point where it is not an
equality for the single branch. -/
theorem splitProbe_descendants_weight :
    ((descendants splitProbe Finset.univ 1 1 1 ([] : List Bool)).map
        (fun p => (kindAlong splitProbe Finset.univ 1 1 p).weight)).sum = 1 := by
  have hd := splitProbe_descendants
  have h0 : kindAlong splitProbe Finset.univ 1 1 [false] = CertKind.low := by decide
  have h1 : kindAlong splitProbe Finset.univ 1 1 [true] = CertKind.low := by decide
  rw [hd]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1]
  norm_num [CertKind.weight]

/-- The probe protocol at which the frozen rule routes **uniquely**: one Alice
query whose predicate keeps both rows on the same side, so the other child holds
no rows and fails the frozen floor.  **BEYOND-PAPER label** as above. -/
abbrev uniqueProbe : Protocol Bool Bool Bool :=
  aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1

/-- The one started coordinate of the consistency instance, holding all `A_r`
retained reference rows of `09:1233--1235`. -/
def uniqueProbeRows : Fin 1 → Finset Bool := fun _ => Finset.univ

/-- **BEYOND-PAPER audit probe: the unique-routing branch is reachable too.**  One
descendant, one frontier node. -/
theorem uniqueProbe_descendants :
    descendants uniqueProbe Finset.univ 1 1 1 ([] : List Bool) = [[true]] := by
  decide

/-- **`09:1233--1235` at the consistency instance.**  The started coordinate holds
all `A_r = 2^1 * 1 = 2` retained reference rows, so the frozen retention holds
with equality. -/
theorem uniqueProbe_hR : ∀ i : Fin 1, refRowFloor 1 1 ≤ (uniqueProbeRows i).card := by
  intro _
  change refRowFloor 1 1 ≤ (Finset.univ : Finset Bool).card
  decide

/-- **`09:1195--1200` at the consistency instance.**  The completed shape of
`lem:wrapper-no-bob-completion` satisfies the frame condition. -/
theorem uniqueProbe_hcomp : CompletedNoBob uniqueProbe 1 :=
  completedNoBob_aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1

/-- The canonical routed certificate system at the consistency instance. -/
abbrev uniqueProbeSystem :
    RoutedSystem uniqueProbe (Fin 1) (CertIndex uniqueProbe uniqueProbeRows 1 1)
      (FrontierNode uniqueProbe uniqueProbeRows 1 1) 1 1 :=
  canonicalSystem uniqueProbe_hcomp uniqueProbe_hR

/-- **BEYOND-PAPER audit probe: the census of the consistency instance.**  One
started coordinate, one routed descendant, hence one certificate. -/
theorem uniqueProbe_coordRoutes (i : Fin 1) :
    coordRoutes uniqueProbe uniqueProbeRows 1 1 i = ({[true]} : Finset (List Bool)) := by
  change (descendants uniqueProbe Finset.univ 1 1 1 ([] : List Bool)).toFinset
      = ({[true]} : Finset (List Bool))
  rw [uniqueProbe_descendants]
  rfl

/-- **BEYOND-PAPER audit probe: the census of the consistency instance.**  One
started coordinate, one routed descendant, hence one certificate. -/
theorem uniqueProbe_card_certIndex :
    Fintype.card (CertIndex uniqueProbe uniqueProbeRows 1 1) = 1 := by
  rw [card_certIndex_eq,
    Finset.sum_congr rfl (fun i _ => congrArg Finset.card (uniqueProbe_coordRoutes i))]
  simp

/-- **Legality of the canonical system's two frozen inputs.**

`canonicalSystem` takes exactly `hcomp` (the conclusion of
`lem:wrapper-no-bob-completion`, `09:1195--1200`) and `hR` (the retention
`A_r <= |R i|` of `09:1233--1235`).  Both hold at legal, nondegenerate
parameters: the completed Alice ladder of `09:1207` satisfies the frame
condition, and a coordinate holding all `A_r = 2^r A_0` retained reference rows
satisfies the retention with equality.  So the canonical construction is not
inhabited only at degenerate or cardinality-contradictory values. -/
theorem canonicalSystem_legal_instance (r A0 : ℕ) (hA0 : 1 ≤ A0)
    (a : Fin (refRowFloor A0 r) → Bool) :
    CompletedNoBob (aliceLadder (X := Fin (refRowFloor A0 r)) (Y := Bool) a true r) r ∧
      (∀ _i : Fin 1,
        refRowFloor A0 r
          ≤ ((Finset.univ : Finset (Fin (refRowFloor A0 r)))).card) ∧
      0 < refRowFloor A0 r := by
  refine ⟨completedNoBob_aliceLadder (Y := Bool) a true r, fun _ => by simp, ?_⟩
  have h2 : 0 < 2 ^ r := pow_pos (by norm_num) r
  simpa [refRowFloor] using Nat.mul_pos h2 hA0

/-- **Non-vacuity of the canonical system at a legal instance.**  At those
parameters the canonical system exists, its frontier is nonempty, and its
certificates carry the frozen data. -/
theorem canonicalSystem_nonempty_frontier (r A0 : ℕ)
    (a : Fin (refRowFloor A0 r) → Bool) :
    (frontierRoutes (aliceLadder (X := Fin (refRowFloor A0 r)) (Y := Bool) a true r)
      (fun _ : Fin 1 => (Finset.univ : Finset (Fin (refRowFloor A0 r)))) A0 r).Nonempty :=
  frontierRoutes_nonempty _ _ _ _ 0

/-- **Aux D1.**  On the completed Alice ladder no frontier node is a first-Bob
node: the shape `lem:wrapper-no-bob-completion` produces has no Bob query at all.
General in the parameters. -/
theorem aliceLadder_not_isFirstBobNode {X Z : Type*} {Y : Type*} (a : X → Bool) (z : Z)
    (r : ℕ) (p : List Bool) :
    ¬ IsFirstBobNode (aliceLadder (X := X) (Y := Y) a z r) r p := by
  rintro ⟨-, hbob, hlt⟩
  rw [descend_aliceLadder a z (le_of_lt hlt)] at hbob
  rcases Nat.eq_zero_or_pos (r - p.length) with hm | hm
  · rw [hm] at hbob; exact hbob
  · obtain ⟨m, hm'⟩ : ∃ m, r - p.length = m + 1 := ⟨r - p.length - 1, by omega⟩
    rw [hm'] at hbob; exact hbob

/-- **Hypothesis consistency for `canonical_cleanCount` -- BEYOND-PAPER AUDIT.**

The headline's full bundle -- the two frozen construction inputs, `hq`, the
frozen coordinate count `hcoord`, `eq:wrapper-first-bob-light` and the final-node
classification -- is **jointly satisfiable, and the conclusion follows rather
than `False`**, at *self-chosen* `r = 1`, `A_0 = 1`, `e_0 = 1`; `q = 2` is not
chosen but *derived*, by evaluating `09:105`'s `q = 2^r` at `r = 1`.

**This is not a legality claim.**  `r` is DEFINED by the schedule (`06:515`
`q = 2^{A_wrap L_P^2}` together with `09:105` `q = 2^r`, so `r = A_wrap L_P^2`),
`A_0` is DEFINED by `09:1219` `A_0 = ceil(2 x_T m_G)`, and `e_0 = |E_0|` is fixed
by the exceptional-set bookkeeping.  Putting numerals at those three places is
*our* choice, so this instance audits our encoding at a point the paper never
visits and is strictly weaker evidence than the paper's application point.  The
parametric legality statement is `canonicalSystem_legal_instance`.

The witness is the completed Alice ladder with a unique-routing predicate and one
started coordinate, so `q - e_0 = 1` and the single routed certificate carries
exactly the weight the classification allows.  `hlight` holds **vacuously**:
that shape has no first-Bob node at all (`aliceLadder_not_isFirstBobNode`), so
`bobNodes = {}` and `bobCapacity = 0`; `hfinal` holds because the system carries
a single certificate, so `W_v <= 1 = finalWeight (some clean)`.  The vacuity of
`hlight` is why this instance is consistency evidence only -- exhibiting the
canonical system with a *nonempty* first-Bob set is a registered next-round
obligation. -/
theorem canonical_cleanCount_consistent :
    (2 : ℝ) - 1 / (1 - vartheta)
        ≤ ((uniqueProbeSystem.toWrapperFrontier.cleanNodes
            (fun _ => some CertKind.clean)).card : ℝ)
      ∧ uniqueProbeSystem.toWrapperFrontier.bobCapacity
          + ((uniqueProbeSystem.toWrapperFrontier.splitNodes
              (fun _ => some CertKind.clean)).card : ℝ)
        ≤ 1 / (1 - vartheta) := by
  refine canonical_cleanCount uniqueProbe_hcomp uniqueProbe_hR (fun _ => some CertKind.clean)
    (q := 2) (e0 := 1) (by norm_num) (by norm_num) ?_ ?_
  · intro v hv
    exfalso
    have hfb : uniqueProbeSystem.firstBob v = true := by
      simpa [WrapperFrontier.bobNodes, RoutedSystem.toWrapperFrontier] using hv
    exact aliceLadder_not_isFirstBobNode (Y := Bool) (fun _ => true) true 1 v.val
      (uniqueProbeSystem.firstBob_spec v hfb)
  · intro v _
    have hle := frontierWeight_le_card uniqueProbe uniqueProbeRows 1 1 v
    rw [uniqueProbe_card_certIndex] at hle
    simpa [finalWeight, CertKind.weight] using hle

end Probes

end EthInapproximability.ParameterizedNP.FrontierIndexing
