import EthInapproximability.ParameterizedNP.FrontierIndexing

/-!
# Parameterized NP route: the routed-certificate construction, `(M-c)` opener

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand this tranche).
* **The exact frozen lines traced here**, in print order:
  * **`09:1187--1193`, the contradiction frame** (`sec:dense-wrapper-frontier`):
    "We now prove the remaining full-strength estimate `eq:wrapper-u-dense`.
    Fix an arbitrary retained matrix `U' in [U]_{1, 1-delta_U, theta}` and
    suppose for contradiction that a protocol `P` of cost at most `C+r-1`
    computes `U'`."  The protocol is the vendored
    `Workspace.Types.Protocol.Protocol`; the cost bound is
    `P.cost <= C + r - 1`; "computes `U'`" is the vendored
    `Protocol.Computes`.  Nothing here is structure data.
  * **`09:1195--1200`, `lem:wrapper-no-bob-completion`** (statement): "The
    protocol may be chosen, without increasing its cost beyond `C+r-1` or
    changing any first-Bob node, so that every root-to-leaf path containing no
    Bob query contains at least `r` Alice queries."
  * **`09:1202--1213`, its proof, transcribed as an operator**: "At every leaf
    reached after `d<r` Alice queries and no Bob query, append `r-d` fixed Alice
    messages and retain the original output label at the new leaf.  These are
    actual communicated bits, but they do not change the current rectangle or
    the computed matrix.  Only the formerly short paths are enlarged, and their
    new depth is exactly `r`.  Hence the completed protocol has cost at most
    `max{cost(P),r} <= C+r-1`, because `C>=1`.  No path containing a Bob query
    is modified."  Each clause is one theorem below:
    `completeNoBob` is the operator, `alicePad` the "`r-d` fixed Alice messages
    ... retain the original output label", `completeNoBob_eval` /
    `completeNoBob_computes` the "do not change ... the computed matrix",
    `completed_short_leaf_depth` the "their new depth is exactly `r`",
    `completeNoBob_cost` / `completeNoBob_cost_le_frame` the cost display with
    its own frozen justification `1 <= C`, and
    `completeNoBob_of_isBobNode` / `descend_eq_at_firstBob` /
    `isFirstBobNode_completeNoBob` the "no path containing a Bob query is
    modified" together with the statement's "or changing any first-Bob node".
  * **`09:1215`**, "Replace `P` by this completed protocol and retain the same
    notation" -- the substitution step, landed as
    `le_of_no_completed_protocol` (and its bracket-shaped corollary
    `member_of_no_completed_protocol`), which is what makes the substitution a
    *reduction* rather than a change of notation: every `hmember` obligation of
    the frozen frame is reduced to the refutation of a **completed** shallow
    protocol.  `completeNoBob_idem` is the "retain the same notation" half: the
    completion is idempotent, so the replacement is stable.
  * `09:1217--1222` (`A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0`), `09:1235--1236`
    ("Start one clean reference certificate in every coordinate outside `E_0`"),
    `09:1250--1259` (the two stopping rules, `d_v`, `kappa_v`, prefix-freeness)
    and `09:1264` (`sum_v kappa_v <= q`) are **banked** as `refRowFloor`,
    `initialCertificate`, `IsFirstBobNode` / `IsFinalAliceNode`,
    `stoppingCapacity`, `PrefixFreeFrontier` and `canonicalSystem`; they are
    consumed here **by pin** and restated nowhere.  What this module adds at
    that interface is the walked system *on a protocol that was arbitrary*:
    `completedSystem` and the readouts of Section 6.
  * `09:1341--1343`, the suffix budget, is the banked
    `RoutedSystem.final_residual_budget`; `completedSystem_final_residual_budget`
    feeds it the completed protocol's own cost bound, which
    `completeNoBob_cost_le_frame` derives from the frozen `09:1192`'s bound on
    the *original* protocol.
* **Cross-anchors opened first-hand for this tranche:** `09:1130--1182` (the
  terminal lemma's reading warning, to confirm the frame this section opens),
  `09:1224--1248` (the survival gates and the routing rule -- banked, not
  restated), `09:1315--1344` (`lem:final-reference-uniqueness`),
  `09:1346--1365` (`eq:wrapper-clean-count`), `09:1367--1384` (the protected
  reservoir constants, GAP-EXPOSED item 3 below), `09:1746--1781` (the row-(iv)
  tail, the one consumer named in the task frame).
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the single import is `FrontierIndexing`,
  whose own ledger row records the same exclusion.
* **Proof status:** new (adapted from the frozen text only in the sense that the
  proof of `lem:wrapper-no-bob-completion` is carried out in the kernel rather
  than in prose).  No mathematics is added.

## What this tranche lands

The banked substrate of `09:1233--1365` -- `RoutedCertificate`, `RoutedSystem`,
`canonicalSystem`, `frontierWeight`, `frontier_conservation`, the two budget
contradictions -- all begins at a protocol already **assumed** to satisfy
`RoutingDynamics.CompletedNoBob`, carried in every downstream statement as the
binder `hcomp`.  Nothing produced that binder: the frozen operator that produces
it, `lem:wrapper-no-bob-completion`, was banked only as the *arithmetic*
`DenseWrapperFrontier.wrapperNoBobCompletion` (`max{cost,r} <= C+r-1`) plus a
*predicate* and one example protocol satisfying it
(`RoutedCertificateSystem.aliceLadder_noBob_depth`).

This module builds the operator.  From an **arbitrary** protocol -- the frozen
`09:1192--1193` contradiction supposition, with no completion assumed -- it
constructs `completeNoBob r P` and proves, in the kernel, every clause the frozen
proof claims for it.  Three consequences follow that no banked module could
state:

1. `hcomp` is **discharged, not assumed**, at every site reachable from an
   arbitrary shallow protocol (`completedNoBob_completeNoBob`).
2. The frozen `hmember` obligation -- "*every* member of the bracket family and
   *every* achievable cost" -- is **reduced** to the refutation of a *completed*
   shallow protocol (`le_of_no_completed_protocol`,
   `member_of_no_completed_protocol`).  This is the exact reduction
   `09:1215` performs, and it is the reason the rest of `sec:wrapper-mass-`
   `redistribution` may assume completion at all.
3. The walked tree, frontier and certificates now exist **over an arbitrary
   alleged protocol** (`completedSystem` and Section 6), rather than over a
   protocol hypothesised to be already completed.

## Predecessor modules consumed **by pin**, never restated

* `Workspace.Types.Protocol` (through `LegacyNPCC.Core`, project-axiom-free):
  `Protocol`, `Protocol.cost`, `Protocol.eval`, `Protocol.Computes`.
* `Workspace.Types.CommComplexity`: `AchievableCosts`.
* `NPCC`: `subgame`, `bracketGE` (statement shapes of the corollary only).
* `EthInapproximability.ParameterizedNP.DenseSynchronisation`: `IsANode`.
* `EthInapproximability.ParameterizedNP.DenseWeightedCount`: `descendStep`,
  `descend`, `descend_cons`, `IsQueryNode`, `IsBobNode`, `stoppingCapacity`.
* `EthInapproximability.ParameterizedNP.DenseWrapperFrontier`: `refRowFloor`.
* `EthInapproximability.ParameterizedNP.RoutedCertificateSystem`: `IsAlicePath`,
  `IsFirstBobNode`, `IsFinalAliceNode`, `RoutedSystem` and its readouts.
* `EthInapproximability.ParameterizedNP.RoutingDynamics`: `CompletedNoBob`.
* `EthInapproximability.ParameterizedNP.FrontierIndexing`: `canonicalSystem`,
  `FrontierNode`, `CertIndex`, `frontierRoutes`, `frontierRoutes_nonempty`,
  `canonicalSystem_sum_capacity_le_width`.

## GAP-EXPOSED (named ranges, with the next-round prescription)

`eq:wrapper-u-dense` (`09:1188`, `09:1780--1781`) is **neither stated nor
implied** anywhere below, and **no route completion is claimed.**  What the
frozen `09:1187--1193` frame still needs, beyond this tranche, is recorded as
named ranges rather than papered over.

1. **The retention `hR` is not produced** (`09:1224--1236`).  The frozen
   sentence "Even if every deleted row of `U` were concentrated in one
   nonexceptional outer coordinate, that coordinate would therefore retain at
   least `A_r = q A_0` reference rows" is banked in real form as
   `DenseWrapperFrontier.retainedRefRows_ge`, and the three survival gates as
   `wrapperInitialSurvival`.  Producing the *row sets* `R : Coord -> Finset X`
   of the retained matrix `U'` from its bracket membership, and the natural
   number inequality `refRowFloor A0 r <= (R i).card` from the real one, is a
   matrix-side step this module does not take: `completedSystem` takes `hR` as
   an explicit binder, exactly as `canonicalSystem` does.  *Next round:* build
   `R` from `RC.1`'s equipartition clause in `bracketGE` and bridge
   `retainedRefRows_ge` to the cardinality form.
2. **The reservoirs are not constructed** (`09:1367--1384`, `09:1418--1531`).
   "Each outer coordinate contains two protected row reservoirs, each of mass
   `mu_P = 1/184`", and `P_v(J_0)`, the protected mass from a donor set reaching
   a first-Bob node `v`.  The reservoirs are a *matrix-side* object (rows of the
   protected duplication inside `N`), not a protocol-side one; their mass
   accounting is banked in `WrapperProtectedEarly` and `ProtectedEarlyClosure`
   and enters this arc as the binders `Pv`, `donor`, `d_0`, `d_1`.  Nothing
   below constructs them, and no declaration below mentions `Pv`.  *Next round:*
   define the reservoir row sets on the protected duplication and transport them
   along `RoutingDynamics.rowsAt` to the frontier, which is the protocol-side
   half of `P_v(J_0)`.
3. **`Scol`, `ell`, `bsel` and `certOpt` are not produced.**  These are the
   remaining data of the frozen `hmember` discharge listed by the pinned
   `WrapperProjectionCoverTail`; items 1 and 2 precede them.
4. **(M-a) and (M-b) are untouched.**  The row-(iv) Localized Extension endpoint
   is the pinned `TerminalLocalizedCall`'s subject and is not consumed here; the
   geometry of `T_*` at the canonical system remains the wiring step
   `WrapperProjectionCoverTail` records as unattempted.  No declaration below
   mentions `TerminalCostTarget`, `TerminalClashComposition` or
   `ExtensionCallFour`.
5. **`A:285--329`, the stopping argument of
   `thm:certified-localized-extension`, is not attempted** and is not reached
   from anything below.
6. **`hDenseRung` is neither discharged nor fed further.**  The reduction of
   Section 5 replaces one binder (`hmember`) by a strictly weaker-to-supply one
   (`hmember` restricted to completed protocols); it closes no rung.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/` was searched first-hand for
this tranche.  The strings "no Bob", "completion", "fixed Alice", "padding" (in
this sense) and "first-Bob" occur **nowhere** in the reader artifact; the only
account of this block is unnumbered prose inside the proof of
`thm:paper-adapted-stage4-interface`, whose opening line
`A-stage4-details.tex:370` reads "For the near-full rung, inspect an arbitrary
protocol for the retained interlace."  That sentence is the reader's whole
rendering of the frozen `09:1188--1193` frame, it is **prose, not a numbered
item**, and lines `371--373` are already recorded as unclaimed prose by
`WRAPPER-PROJECTION-COVERS-001`.  **No reader item is claimed** by this module,
and the absence is a finding about the reader artifact rather than an omission
here.

## Canonical inhabitation

The paper's own instance of the completion is `completeNoBob r P` for *the*
arbitrary alleged protocol `P` of `09:1192--1193`.  Because that protocol is
universally quantified in the frozen text, the canonical instance is not one
term but a family, and `wrapperNoBobCompletion_exists` is exactly that family:
it is proved **for every** protocol at the frozen side conditions, so the
paper's instance is contained in it by instantiation rather than by resemblance.
The inhabitation obligation of this module's one `RoutedSystem`-valued
declaration, `completedSystem`, is **inherited** from `canonicalSystem`, whose
deferred obligation the pinned `FrontierIndexing` already discharged at the
paper's own inputs; `completedSystem_canonical_at_paper_inputs` records that the
inherited discharge survives the completion.  The two `Bool`-carrier probes of
Section 7 claim **no** legality: they are labelled statement poles and
rejection probes, and neither is offered as an instance of the frozen frame.
-/

namespace EthInapproximability.ParameterizedNP.RoutedCertificateConstruction

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing

/-! ## Section 1  `09:1203--1205`, the `r-d` fixed Alice messages

"At every leaf reached after `d<r` Alice queries and no Bob query, append `r-d`
fixed Alice messages and retain the original output label at the new leaf."

A *fixed* Alice message is one whose bit does not depend on Alice's input, so the
appended node is `aNode` with a constant predicate and, since the message is
fixed, both of its children carry the same continuation: this is what makes the
frozen "they do not change the current rectangle or the computed matrix" true.
The "original output label" is the leaf's own `z`, retained at the bottom of the
appended chain. -/

section Padding

variable {X Y Z : Type*}

/-- **`09:1203--1204`, the appended chain.**  `alicePad z n` is `n` fixed Alice
messages ending at a leaf that retains the original output label `z`.  The
message is fixed, so the predicate is constant and both children are the same
continuation. -/
def alicePad (z : Z) : ℕ → Protocol X Y Z
  | 0 => Protocol.leaf z
  | n + 1 => Protocol.aNode (fun _ => false) (alicePad z n) (alicePad z n)

@[simp] theorem alicePad_zero (z : Z) : alicePad (X := X) (Y := Y) z 0 = Protocol.leaf z := rfl

@[simp] theorem alicePad_succ (z : Z) (n : ℕ) :
    alicePad (X := X) (Y := Y) z (n + 1)
      = Protocol.aNode (fun _ => false) (alicePad z n) (alicePad z n) := rfl

/-- **`09:1205--1206`, "These are actual communicated bits".**  The chain costs
exactly its length: the appended messages are paid for.  General. -/
@[simp] theorem alicePad_cost (z : Z) (n : ℕ) : (alicePad (X := X) (Y := Y) z n).cost = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [alicePad_succ, Protocol.cost, ih, max_self]
      omega

/-- **`09:1204`, "retain the original output label at the new leaf".**  The chain
computes the constant `z`, whatever the inputs.  General. -/
@[simp] theorem alicePad_eval (z : Z) (n : ℕ) (x : X) (y : Y) :
    (alicePad (X := X) (Y := Y) z n).eval x y = z := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Protocol.eval, ih]

/-- **Aux P1.**  One step down the chain is the shorter chain, on either bit --
the two children coincide because the message is fixed.  General. -/
@[simp] theorem descendStep_alicePad (z : Z) (n : ℕ) (b : Bool) :
    descendStep (alicePad (X := X) (Y := Y) z n) b = alicePad z (n - 1) := by
  cases n with
  | zero => cases b <;> rfl
  | succ n => cases b <;> rfl

/-- **Aux P2 (walking the chain).**  Any route of length `k` inside the chain
lands on the chain of length `n - k`.  General. -/
theorem descend_alicePad (z : Z) : ∀ (p : List Bool) (n : ℕ),
    descend (alicePad (X := X) (Y := Y) z n) p = alicePad z (n - p.length) := by
  intro p
  induction p with
  | nil => intro n; simp
  | cons b p ih =>
      intro n
      rw [descend_cons, descendStep_alicePad, ih]
      congr 1
      simp only [List.length_cons]
      omega

/-- **Aux P3.**  No node of the chain is a Bob query: the completion adds only
Alice messages.  This is the shape fact behind the frozen "no path containing a
Bob query is modified".  General. -/
theorem not_isBobNode_alicePad (z : Z) (n : ℕ) :
    ¬ IsBobNode (alicePad (X := X) (Y := Y) z n) := by
  cases n with
  | zero => simp [IsBobNode]
  | succ n => simp [IsBobNode]

/-- **Aux P4.**  A nonempty chain is an Alice query.  General. -/
theorem isANode_alicePad_succ (z : Z) (n : ℕ) :
    IsANode (alicePad (X := X) (Y := Y) z (n + 1)) :=
  ⟨_, _, _, rfl⟩

/-- **Aux P5.**  A nonempty chain is a query node.  General. -/
theorem isQueryNode_alicePad (z : Z) {n : ℕ} (hn : 1 ≤ n) :
    IsQueryNode (alicePad (X := X) (Y := Y) z n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact trivial

/-- **`09:1206--1207`, "their new depth is exactly `r`", inside the chain.**
Every route of length at most `n` through the chain is an Alice route.  This is
what makes the appended messages count towards the frozen "`r` Alice queries".
General. -/
theorem isAlicePath_alicePad (z : Z) : ∀ (p : List Bool) (n : ℕ), p.length ≤ n →
    IsAlicePath (alicePad (X := X) (Y := Y) z n) p := by
  intro p
  induction p with
  | nil => intro n _; trivial
  | cons b p ih =>
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
      refine ⟨isANode_alicePad_succ z m, ?_⟩
      rw [descendStep_alicePad]
      exact ih m (by simp only [List.length_cons] at hn; omega)

end Padding

/-! ## Section 2  `09:1202--1207`, the completion operator

"At every leaf reached after `d<r` Alice queries **and no Bob query**, append
`r-d` fixed Alice messages ... Only the formerly short paths are enlarged."

The recursion carries the *remaining* Alice budget `k`: it starts at `r`, drops
by one at each Alice query, and is spent at a leaf.  A Bob node stops the
recursion outright -- the frozen clause "and no Bob query" -- so the whole
subtree below any Bob query is returned unchanged, which is `09:1212`, "No path
containing a Bob query is modified". -/

section Completion

variable {X Y Z : Type*}

/-- **`09:1202--1207`, the completion of `lem:wrapper-no-bob-completion`.**

`completeNoBob k P` pads every leaf of `P` that is reachable by `k` or fewer
Alice queries and no Bob query, up to depth exactly `k`, and changes nothing
else.  `k` is the remaining Alice budget; the frozen instance is `k = r`.

**No complexity or robustness conclusion is data here** (mechanical rules
M1--M10): the operator is a pure tree transformation, and every property the
frozen proof claims for it is a theorem below. -/
def completeNoBob : ℕ → Protocol X Y Z → Protocol X Y Z
  | k, Protocol.leaf z => alicePad z k
  | k, Protocol.aNode a l r => Protocol.aNode a (completeNoBob (k - 1) l) (completeNoBob (k - 1) r)
  | _, Protocol.bNode b l r => Protocol.bNode b l r

@[simp] theorem completeNoBob_leaf (k : ℕ) (z : Z) :
    completeNoBob k (Protocol.leaf z : Protocol X Y Z) = alicePad z k := rfl

@[simp] theorem completeNoBob_aNode (k : ℕ) (a : X → Bool) (l r : Protocol X Y Z) :
    completeNoBob k (Protocol.aNode a l r)
      = Protocol.aNode a (completeNoBob (k - 1) l) (completeNoBob (k - 1) r) := rfl

/-- **`09:1212`, "No path containing a Bob query is modified", at the query
itself.**  A Bob node and everything below it is returned verbatim. -/
@[simp] theorem completeNoBob_bNode (k : ℕ) (b : Y → Bool) (l r : Protocol X Y Z) :
    completeNoBob k (Protocol.bNode b l r) = Protocol.bNode b l r := rfl

/-- **Aux C1 (identity at the empty budget).**  With no Alice queries left to
demand, the completion changes nothing.  General. -/
@[simp] theorem completeNoBob_zero (P : Protocol X Y Z) : completeNoBob 0 P = P := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [completeNoBob_aNode, Nat.zero_sub, ihl, ihr]
  | bNode b l r _ _ => rfl

/-- **`09:1212`, "No path containing a Bob query is modified", as a rewrite.**
The completion is the identity on any Bob node.  General. -/
theorem completeNoBob_of_isBobNode {P : Protocol X Y Z} (k : ℕ) (h : IsBobNode P) :
    completeNoBob k P = P := by
  cases P with
  | leaf z => simp [IsBobNode] at h
  | aNode a l r => simp [IsBobNode] at h
  | bNode b l r => rfl

/-- **Aux C2 (the completion creates no Bob query).**  A Bob node in the
completed protocol was a Bob node already: the appended messages are Alice's.
General. -/
theorem isBobNode_of_completeNoBob {P : Protocol X Y Z} {k : ℕ}
    (h : IsBobNode (completeNoBob k P)) : IsBobNode P := by
  cases P with
  | leaf z => exact absurd h (not_isBobNode_alicePad z k)
  | aNode a l r => simp [IsBobNode] at h
  | bNode b l r => trivial

/-- **Aux C3 (the completion destroys no Bob query).**  Converse of `Aux C2`.
General. -/
theorem isBobNode_completeNoBob {P : Protocol X Y Z} {k : ℕ} (h : IsBobNode P) :
    IsBobNode (completeNoBob k P) := by
  rw [completeNoBob_of_isBobNode k h]
  exact h

/-- **`09:1203`, the frozen stopping condition `d<r`, read off the operator.**
With a positive remaining budget the completed protocol is a query node at the
root -- there are no short leaves left.  General. -/
theorem isQueryNode_completeNoBob (P : Protocol X Y Z) {k : ℕ} (hk : 1 ≤ k) :
    IsQueryNode (completeNoBob k P) := by
  cases P with
  | leaf z => exact isQueryNode_alicePad z hk
  | aNode a l r => exact trivial
  | bNode b l r => exact trivial

/-- **`09:1208--1211`, the cost display.**  "Hence the completed protocol has
cost at most `max{cost(P), r}`."  Proved for every remaining budget `k`, of which
the frozen instance is `k = r`.  General. -/
theorem completeNoBob_cost (P : Protocol X Y Z) : ∀ k : ℕ,
    (completeNoBob k P).cost ≤ max P.cost k := by
  induction P with
  | leaf z => intro k; simp [Protocol.cost]
  | aNode a l r ihl ihr =>
      intro k
      have hl := ihl (k - 1)
      have hr := ihr (k - 1)
      simp only [completeNoBob_aNode, Protocol.cost]
      omega
  | bNode b l r _ _ => intro k; simp [Protocol.cost]

/-- **`09:1205--1206`, "they do not change the current rectangle or the computed
matrix".**  The completed protocol has the same output on every input.
General. -/
theorem completeNoBob_eval (P : Protocol X Y Z) : ∀ (k : ℕ) (x : X) (y : Y),
    (completeNoBob k P).eval x y = P.eval x y := by
  induction P with
  | leaf z => intro k x y; simp [Protocol.eval]
  | aNode a l r ihl ihr =>
      intro k x y
      by_cases h : a x
      · simp [Protocol.eval, h, ihr]
      · simp [Protocol.eval, h, ihl]
  | bNode b l r ihl ihr =>
      intro k x y
      rfl

/-- **`09:1205--1206`, in the vendored `Computes` form.**  If `P` computes the
retained matrix `U'` of `09:1188--1193`, so does its completion.  General. -/
theorem completeNoBob_computes {P : Protocol X Y Z} {f : X → Y → Z}
    (h : Protocol.Computes P f) (k : ℕ) : Protocol.Computes (completeNoBob k P) f := by
  intro x y
  rw [completeNoBob_eval]
  exact h x y

/-- **`09:1215`, "retain the same notation", as a general property.**  The
completion is idempotent: replacing `P` by its completion and completing again
changes nothing, so the frozen substitution step is stable.  General. -/
theorem completeNoBob_idem (P : Protocol X Y Z) : ∀ k : ℕ,
    completeNoBob k (completeNoBob k P) = completeNoBob k P := by
  have hpad : ∀ (z : Z) (n : ℕ),
      completeNoBob (X := X) (Y := Y) n (alicePad z n) = alicePad z n := by
    intro z n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [alicePad_succ, completeNoBob_aNode, Nat.add_sub_cancel, ih]
  induction P with
  | leaf z => intro k; simpa using hpad z k
  | aNode a l r ihl ihr =>
      intro k
      simp only [completeNoBob_aNode, ihl, ihr]
  | bNode b l r _ _ => intro k; rfl

end Completion

/-! ## Section 3  `09:1197--1198`, `09:1212`: the frontier is not disturbed

"without increasing its cost beyond `C+r-1` **or changing any first-Bob node**"
and "No path containing a Bob query is modified".

Both clauses are about *addresses*: the first-Bob nodes of the completed
protocol are exactly those of the original, and at such an address the two
protocols are the same subtree. -/

section Frontier

variable {X Y Z : Type*}

/-- **Aux F1 (the step transfer).**  Below an Alice query of the completed
protocol, the completion of the child is the child of the completion, with the
budget dropped by one.  This is the induction step of everything in this
section.  General. -/
theorem descendStep_completeNoBob {P : Protocol X Y Z} {k : ℕ} (b : Bool)
    (h : IsANode (completeNoBob k P)) :
    descendStep (completeNoBob k P) b = completeNoBob (k - 1) (descendStep P b) := by
  cases P with
  | leaf z => exact descendStep_alicePad z k b
  | aNode a l r => cases b <;> rfl
  | bNode b' l r => simp [IsANode] at h

/-- **Aux F2 (the walk transfer).**  Along any Alice route of the completed
protocol, walking commutes with the completion.  General. -/
theorem descend_completeNoBob : ∀ {P : Protocol X Y Z} {k : ℕ} {p : List Bool},
    IsAlicePath (completeNoBob k P) p →
      descend (completeNoBob k P) p = completeNoBob (k - p.length) (descend P p) := by
  intro P k p
  induction p generalizing P k with
  | nil => intro _; simp
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩
      have hstep := descendStep_completeNoBob (P := P) (k := k) b hnode
      rw [hstep] at hrest
      have hih := ih (P := descendStep P b) (k := k - 1) hrest
      have hlen : k - 1 - p.length = k - (b :: p).length := by
        simp only [List.length_cons]; omega
      calc descend (completeNoBob k P) (b :: p)
          = descend (descendStep (completeNoBob k P) b) p := rfl
        _ = descend (completeNoBob (k - 1) (descendStep P b)) p := by rw [hstep]
        _ = completeNoBob (k - 1 - p.length) (descend (descendStep P b) p) := hih
        _ = completeNoBob (k - (b :: p).length) (descend P (b :: p)) := by rw [hlen]; rfl

/-- **Aux F3 (Alice routes survive the completion).**  Every Alice route of the
original protocol is an Alice route of the completion.  General. -/
theorem isAlicePath_completeNoBob : ∀ {P : Protocol X Y Z} {k : ℕ} {p : List Bool},
    IsAlicePath P p → IsAlicePath (completeNoBob k P) p := by
  intro P k p
  induction p generalizing P k with
  | nil => intro _; trivial
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩
      obtain ⟨a, l, r, rfl⟩ := hnode
      refine ⟨⟨a, _, _, rfl⟩, ?_⟩
      have hstep : descendStep (completeNoBob k (Protocol.aNode a l r)) b
          = completeNoBob (k - 1) (descendStep (Protocol.aNode a l r) b) := by
        cases b <;> rfl
      rw [hstep]
      exact ih hrest

/-- **`09:1212`, the converse direction.**  An Alice route of the completion that
reaches a Bob query was an Alice route of the original: the padding chain
contains no Bob query, so such a route never entered the padding.  General. -/
theorem isAlicePath_of_completeNoBob : ∀ {P : Protocol X Y Z} {k : ℕ} {p : List Bool},
    IsAlicePath (completeNoBob k P) p → IsBobNode (descend (completeNoBob k P) p) →
      IsAlicePath P p := by
  intro P k p
  induction p generalizing P k with
  | nil => intro _ _; trivial
  | cons b p ih =>
      rintro ⟨hnode, hrest⟩ hbob
      cases P with
      | leaf z =>
          exfalso
          rw [completeNoBob_leaf, descend_alicePad] at hbob
          exact not_isBobNode_alicePad z _ hbob
      | aNode a l r =>
          refine ⟨⟨a, l, r, rfl⟩, ?_⟩
          have hstep : descendStep (completeNoBob k (Protocol.aNode a l r)) b
              = completeNoBob (k - 1) (descendStep (Protocol.aNode a l r) b) := by
            cases b <;> rfl
          rw [hstep] at hrest
          rw [descend_cons, hstep] at hbob
          exact ih hrest hbob
      | bNode b' l r => simp [IsANode] at hnode

/-- **`09:1197--1198`, "without ... changing any first-Bob node".**

The first-Bob addresses of the completed protocol are **exactly** those of the
original, at the same stopping width `r`.  Both directions are proved; neither
is assumed. -/
theorem isFirstBobNode_completeNoBob {P : Protocol X Y Z} {r : ℕ} {p : List Bool} :
    IsFirstBobNode (completeNoBob r P) r p ↔ IsFirstBobNode P r p := by
  constructor
  · rintro ⟨halice, hbob, hlen⟩
    refine ⟨isAlicePath_of_completeNoBob halice hbob, ?_, hlen⟩
    rw [descend_completeNoBob halice] at hbob
    exact isBobNode_of_completeNoBob hbob
  · rintro ⟨halice, hbob, hlen⟩
    refine ⟨isAlicePath_completeNoBob halice, ?_, hlen⟩
    rw [descend_completeNoBob (isAlicePath_completeNoBob halice)]
    exact isBobNode_completeNoBob hbob

/-- **`09:1212`, "No path containing a Bob query is modified", at the address.**

At a first-Bob node the two protocols are literally the same subtree, so every
statement the frozen argument makes below a first-Bob node -- the small-capacity
fallback, the denser-child selection, the residual budget -- transfers verbatim
between `P` and its completion. -/
theorem descend_eq_at_firstBob {P : Protocol X Y Z} {r : ℕ} {p : List Bool}
    (h : IsFirstBobNode P r p) : descend (completeNoBob r P) p = descend P p := by
  rw [descend_completeNoBob (isAlicePath_completeNoBob (k := r) h.1)]
  exact completeNoBob_of_isBobNode _ h.2.1

/-- **`09:1206--1207`, "Only the formerly short paths are enlarged, and their new
depth is exactly `r`".**

A leaf of `P` reached by an Alice route of length `d <= r` with no Bob query is,
in the completion, extended by a route of length exactly `r - d`, so the enlarged
path has depth exactly `r` and is an Alice route throughout. -/
theorem completed_short_leaf_depth {P : Protocol X Y Z} {r : ℕ} {p : List Bool} {z : Z}
    (halice : IsAlicePath P p) (hlen : p.length ≤ r) (hleaf : descend P p = Protocol.leaf z) :
    IsAlicePath (completeNoBob r P) (p ++ List.replicate (r - p.length) false)
      ∧ (p ++ List.replicate (r - p.length) false).length = r := by
  have hpre : IsAlicePath (completeNoBob r P) p := isAlicePath_completeNoBob halice
  refine ⟨isAlicePath_append hpre ?_, ?_⟩
  · rw [descend_completeNoBob hpre, hleaf, completeNoBob_leaf]
    exact isAlicePath_alicePad z _ _ (by simp)
  · simp only [List.length_append, List.length_replicate]
    omega

end Frontier

/-! ## Section 4  `09:1195--1215`, `lem:wrapper-no-bob-completion` as one theorem

Every clause of the frozen statement and of its proof, at the frozen frame
conditions of `09:1192--1193`. -/

section FrameLemma

variable {X Y Z : Type*}

/-- **`09:1208--1212`, the cost clause at the frozen frame.**

"Hence the completed protocol has cost at most `max{cost(P),r} <= C+r-1`,
because `C>=1`."  The hypothesis `1 <= C` is the frozen justification, quoted;
`completeNoBob_cost_needs_C_ge_one` below shows it really bites.

The `ℕ`-arithmetic half is **not** re-derived here: the banked
`DenseWrapperFrontier.noBobCompletion_cost_le` (fixed-interface discipline) is
consumed at its banked signature, and this module contributes only the operator
half `completeNoBob_cost`. -/
theorem completeNoBob_cost_le_frame {P : Protocol X Y Z} {C r : ℕ} (hC : 1 ≤ C)
    (hcost : P.cost ≤ C + r - 1) : (completeNoBob r P).cost ≤ C + r - 1 :=
  le_trans (completeNoBob_cost P r) (noBobCompletion_cost_le hC hcost)

/-- **`09:1195--1200`, the frame condition itself, discharged.**

`CompletedNoBob (completeNoBob r P) r`: "every root-to-leaf path containing no
Bob query contains at least `r` Alice queries", i.e. no Alice-only route shorter
than `r` reaches a leaf.  This is the binder `hcomp` that every banked module of
`sec:wrapper-mass-redistribution` assumes; here it is **proved**, from an
arbitrary protocol, with no completion hypothesis anywhere. -/
theorem completedNoBob_completeNoBob (P : Protocol X Y Z) (r : ℕ) :
    CompletedNoBob (completeNoBob r P) r := by
  intro p halice hlen
  rw [descend_completeNoBob halice]
  exact isQueryNode_completeNoBob _ (by omega)

/-- **`09:1195--1215`, `lem:wrapper-no-bob-completion`, entire.**

From the frozen contradiction supposition of `09:1192--1193` -- an *arbitrary*
protocol `P` of cost at most `C+r-1` computing the retained matrix -- the frozen
lemma produces a replacement protocol with, in the frozen order:

* cost still at most `C+r-1` (`09:1208--1212`, using `C >= 1`);
* the same computed matrix (`09:1205--1206`);
* the completion property (`09:1197--1200`);
* the same first-Bob nodes (`09:1197--1198`); and
* the same subtree below every first-Bob node (`09:1212`).

**Non-triviality.**  The trivial witness `P' = P` fails the third clause: the
protocol `Protocol.leaf z` at `r = 1` has cost `0 <= C + 1 - 1` for `C = 1` and
is *not* `CompletedNoBob` at `r = 1` (`leafProtocol_not_completed`), so the
conclusion is not obtainable by returning the input. -/
theorem wrapperNoBobCompletion_exists (P : Protocol X Y Z) {f : X → Y → Z} {C r : ℕ}
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1) (hf : Protocol.Computes P f) :
    ∃ P' : Protocol X Y Z,
      P'.cost ≤ C + r - 1
        ∧ Protocol.Computes P' f
        ∧ CompletedNoBob P' r
        ∧ (∀ p : List Bool, IsFirstBobNode P' r p ↔ IsFirstBobNode P r p)
        ∧ (∀ p : List Bool, IsFirstBobNode P r p → descend P' p = descend P p) :=
  ⟨completeNoBob r P,
    completeNoBob_cost_le_frame hC hcost,
    completeNoBob_computes hf r,
    completedNoBob_completeNoBob P r,
    fun _ => isFirstBobNode_completeNoBob,
    fun _ h => descend_eq_at_firstBob h⟩

end FrameLemma

/-! ## Section 5  `09:1215`, the substitution as a reduction

"Replace `P` by this completed protocol and retain the same notation."

Read as a reduction, this sentence says: to refute *every* shallow protocol it
suffices to refute every *completed* shallow protocol.  That is what the rest of
`sec:wrapper-mass-redistribution` actually proves, and it is why the section may
assume completion at all.  The statement below is the bridge; it discharges no
rung and asserts nothing about `eq:wrapper-u-dense`. -/

section Reduction

variable {X Y Z : Type*}

/-- **`09:1188--1215`, the frozen frame as a reduction on achievable costs.**

If no *completed* protocol of cost at most `C+r-1` computes `f`, then every
achievable cost of `f` is at least `C+r`.  The completion clause `CompletedNoBob`
is supplied to the refuter, not demanded of it: this is exactly the strengthening
`09:1215` grants the rest of the section.

**Non-triviality.**  The hypothesis is strictly weaker than the corresponding
statement without `CompletedNoBob` -- it may ignore every non-completed shallow
protocol -- so the theorem is not an instance of the unrestricted refutation, and
`reduction_needs_C_ge_one` shows the frozen `C >= 1` is load-bearing here too:
that pole exhibits `C = 0`, `r = 1` at which the *conclusion* fails outright.  It
does **not** prove that the refutation hypothesis is vacuous at `C = 0`, and no
claim of that kind is made here. -/
theorem le_of_no_completed_protocol {f : X → Y → Z} {C r : ℕ} (hC : 1 ≤ C)
    (href : ∀ P : Protocol X Y Z, P.cost ≤ C + r - 1 → CompletedNoBob P r →
      Protocol.Computes P f → False) :
    ∀ c ∈ AchievableCosts f, C + r ≤ c := by
  rintro c ⟨P, rfl, hcomp⟩
  by_contra hlt
  exact href (completeNoBob r P)
    (completeNoBob_cost_le_frame hC (by omega))
    (completedNoBob_completeNoBob P r)
    (completeNoBob_computes hcomp r)

end Reduction

/-! ### The reduction in the shape the frozen `hmember` binder has

`WrapperMassRedistribution.denseRung_of_no_shallow_member` reduces
`eq:wrapper-u-dense` to the binder

  `hmember : forall RC in bracketGE ..., forall c in AchievableCosts (subgame ...), C + r <= c`,

and every pinned module of this arc records that binder as the standing
GAP-EXPOSED item M1.  The corollary below rewrites it, without weakening, as the
refutation of *completed* shallow protocols -- the frozen `09:1215` normalization
applied uniformly over the bracket family.  **`eq:wrapper-u-dense` is not
asserted, and `hDenseRung` is not discharged**: what changes is only which
protocols a future refutation must consider. -/

section MemberShape

/-- **`09:1188--1215` at the frozen `hmember` shape.**

The bracket family, the interlace width `1`, the retained-matrix parameters
`(1-delta_U, theta)` and the cost target `C+r` are the pinned
`FirstWrapperClose.denseRung_of_no_shallow_member` binder's own, byte for byte;
only the protocol side is normalized by `09:1215`. -/
theorem member_of_no_completed_protocol {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ : ℝ} (hC : 1 ≤ C)
    (href : ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ,
      ∀ P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool,
        P.cost ≤ C + r - 1 → CompletedNoBob P r →
          Protocol.Computes P
            (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2) → False) :
    ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ,
      ∀ c ∈ AchievableCosts (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2),
        C + r ≤ c :=
  fun RC hRC => le_of_no_completed_protocol hC (href RC hRC)

end MemberShape

/-! ## Section 6  `09:1233--1259` on an arbitrary alleged protocol

With `hcomp` discharged, the banked walked system of `FrontierIndexing` applies
to the completion of an *arbitrary* protocol.  The retention `hR` of
`09:1233--1235` stays an explicit binder (GAP-EXPOSED item 1); everything else
is now produced rather than assumed. -/

section WalkedSystem

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1250--1259` over the contradiction supposition of `09:1192--1193`.**

The routed certificate system of the frozen argument, built on the *completion*
of an arbitrary protocol.  Its frontier, prefix-freeness, certificates,
coordinate uniqueness and Kraft bound are the pinned `canonicalSystem`'s,
consumed unchanged; what this definition supplies is the completion hypothesis
`canonicalSystem` demands, which no caller now has to assume.

**Deliberately not data:** the retention `hR`, which is a fact about the retained
matrix `U'` and not about the protocol (GAP-EXPOSED item 1). -/
def completedSystem (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) :
    RoutedSystem (completeNoBob r P) Coord
      (CertIndex (completeNoBob r P) R A0 r) (FrontierNode (completeNoBob r P) R A0 r) r A0 :=
  canonicalSystem (completedNoBob_completeNoBob P r) hR

/-- **Aux W1.**  The walked system's addresses are the frontier's elements.
General. -/
@[simp] theorem completedSystem_node (P : Protocol X Y Z) {R : Coord → Finset X} {A0 r : ℕ}
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (v : FrontierNode (completeNoBob r P) R A0 r) :
    (completedSystem P hR).node v = v.val := rfl

/-- **`eq:wrapper-frontier-conservation`, second clause (`09:1264`), over an
arbitrary alleged protocol.**  `sum_v kappa_v <= q` at the wrapper width
`q = 2^r`, now with no completion hypothesis on the caller's side. -/
theorem completedSystem_sum_capacity_le_width (P : Protocol X Y Z) {R : Coord → Finset X}
    {A0 r : ℕ} (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) :
    ∑ v : FrontierNode (completeNoBob r P) R A0 r, stoppingCapacity r v.val.length ≤ 2 ^ r :=
  (completedSystem P hR).sum_capacity_le_width

/-- **`09:1235--1236`, the frontier is not empty.**  "Start one clean reference
certificate in every coordinate outside `E_0`" is the frozen *supply* of a
started coordinate; with at least one such coordinate the walked frontier of an
arbitrary alleged protocol has a node.  Consumed from the pinned
`frontierRoutes_nonempty` at the supplied coordinate `i`. -/
theorem completedSystem_frontier_nonempty (P : Protocol X Y Z) {R : Coord → Finset X}
    {A0 r : ℕ} (i : Coord) :
    (frontierRoutes (completeNoBob r P) R A0 r).Nonempty :=
  frontierRoutes_nonempty _ _ _ _ i

/-- **`09:1341--1343` over an arbitrary alleged protocol.**

"The suffix below a node reached after `r` Alice bits in the alleged `(C+r-1)`-bit
protocol has depth at most `C-1`."  The budget is the *original* protocol's, from
`09:1192`; it survives the completion by `completeNoBob_cost_le_frame`, which is
the only reason the frozen argument may run its residual-budget contradictions on
the completed protocol at all. -/
theorem completedSystem_final_residual_budget (P : Protocol X Y Z) {R : Coord → Finset X}
    {A0 r C : ℕ} (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) (hC : 1 ≤ C)
    (hcost : P.cost ≤ C + r - 1)
    {v : FrontierNode (completeNoBob r P) R A0 r} (hv : (completedSystem P hR).firstBob v = false) :
    (descend (completeNoBob r P) ((completedSystem P hR).node v)).cost + r ≤ C + r - 1 :=
  (completedSystem P hR).final_residual_budget hv (completeNoBob_cost_le_frame hC hcost)

/-- **`09:1306--1308` over an arbitrary alleged protocol.**  The same, at a
first-Bob address. -/
theorem completedSystem_firstBob_residual_budget (P : Protocol X Y Z) {R : Coord → Finset X}
    {A0 r C : ℕ} (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) (hC : 1 ≤ C)
    (hcost : P.cost ≤ C + r - 1)
    {v : FrontierNode (completeNoBob r P) R A0 r} (hv : (completedSystem P hR).firstBob v = true) :
    (descend (completeNoBob r P) ((completedSystem P hR).node v)).cost
        + ((completedSystem P hR).node v).length ≤ C + r - 1 :=
  (completedSystem P hR).firstBob_residual_budget' hv (completeNoBob_cost_le_frame hC hcost)

/-- **`09:1197--1198` at the walked system.**  Every first-Bob address of the
walked system is a first-Bob address of the **original** alleged protocol, at the
same width: the frontier the banked counting spine works over is the frontier of
the protocol `09:1192--1193` supposes, not an artifact of the completion. -/
theorem completedSystem_firstBob_of_original (P : Protocol X Y Z) {R : Coord → Finset X}
    {A0 r : ℕ} (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode (completeNoBob r P) R A0 r} (hv : (completedSystem P hR).firstBob v = true) :
    IsFirstBobNode P r ((completedSystem P hR).node v) :=
  isFirstBobNode_completeNoBob.mp ((completedSystem P hR).firstBob_spec v hv)

/-- **Canonical inhabitation, inherited and preserved.**

The pinned `FrontierIndexing.canonicalSystem` is the paper's own routed
certificate system at the paper's own inputs.  `completedSystem` is *that*
system, at the completion of an arbitrary protocol: the two are the same term,
so the canonical-inhabitation discharge banked for `canonicalSystem` transfers
verbatim and no new obligation is opened.  Recorded as an equation rather than
asserted in prose. -/
theorem completedSystem_canonical_at_paper_inputs (P : Protocol X Y Z) {R : Coord → Finset X}
    {A0 r : ℕ} (hR : ∀ i, refRowFloor A0 r ≤ (R i).card) :
    completedSystem P hR = canonicalSystem (completedNoBob_completeNoBob P r) hR := rfl

end WalkedSystem

/-! ## Section 7  Statement poles and rejection probes

Each declaration below claims **no** legality: it exhibits a protocol at values
of its own to show that a load-bearing hypothesis of Sections 2--5 really bites.
None is offered as an instance of the frozen frame. -/

section Poles

/-- **Statement pole 1: the completion is not the identity, and the frame
condition is not automatic.**

`Protocol.leaf z` has an Alice-free root-to-leaf path of length `0 < 1`, so it
fails `CompletedNoBob _ 1`; its completion satisfies it.  Hence
`wrapperNoBobCompletion_exists` cannot be discharged by returning its input, and
`lem:wrapper-no-bob-completion` has content. -/
theorem leafProtocol_not_completed (z : Bool) :
    ¬ CompletedNoBob (Protocol.leaf z : Protocol Bool Bool Bool) 1
      ∧ CompletedNoBob (completeNoBob 1 (Protocol.leaf z : Protocol Bool Bool Bool)) 1 := by
  refine ⟨?_, completedNoBob_completeNoBob _ 1⟩
  intro h
  have hq := h [] trivial (by simp)
  simp [IsQueryNode] at hq

/-- **Statement pole 2: the frozen `C >= 1` of `09:1212` is load-bearing.**

At `C = 0` and `r = 1` the leaf protocol satisfies the frozen cost bound
`cost(P) <= C+r-1 = 0`, but its completion costs `1`.  So the cost clause of
`lem:wrapper-no-bob-completion` is false without the frozen justification, and
`completeNoBob_cost_le_frame` may not drop `hC`.  **Claims no legality: `C = 0`
is outside the frozen range `09:1302`'s `C >= 3`.** -/
theorem completeNoBob_cost_needs_C_ge_one :
    (Protocol.leaf true : Protocol Bool Bool Bool).cost ≤ 0 + 1 - 1
      ∧ ¬ (completeNoBob 1 (Protocol.leaf true : Protocol Bool Bool Bool)).cost ≤ 0 + 1 - 1 := by
  constructor
  · simp [Protocol.cost]
  · simp [Protocol.cost]

/-- **Statement pole 3: the same, transported to the reduction.**

At `C = 0`, `r = 1` and the constant game the *conclusion* of
`le_of_no_completed_protocol` fails: the cost `0` is achievable and is not at
least `C + r = 1`.  Exactly those two facts are what this pole proves, and that
is all it claims.

**Scope note (deliberately not asserted).**  The stronger narration -- that the
refutation hypothesis is *vacuously* available at `C = 0` because no
`CompletedNoBob _ 1` protocol has cost at most `0` -- is believed true (such a
protocol must be a query node at the root) but is **not** proved here and is not
part of the statement.  Read this pole only as "the conclusion is false at
`C = 0`", which is already enough to show `1 <= C` is load-bearing.
**Claims no legality.**
-/
theorem reduction_needs_C_ge_one :
    (0 : ℕ) ∈ AchievableCosts (fun _ _ : Bool => true)
      ∧ ¬ (0 + 1 ≤ (0 : ℕ)) := by
  refine ⟨⟨Protocol.leaf true, rfl, fun _ _ => rfl⟩, by omega⟩

/-- **Rejection probe: the completion leaves Bob subtrees alone.**

A protocol whose root is a Bob query has short leaves everywhere, yet the
completion returns it unchanged at every budget -- the frozen "and no Bob query"
of `09:1203` and "No path containing a Bob query is modified" of `09:1212`.  A
completion that padded through Bob queries would fail this equation.  **Claims no
legality: the values are the probe's own.** -/
theorem completeNoBob_leaves_bob_subtree_alone (k : ℕ) :
    completeNoBob k
        (Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf false)
          : Protocol Bool Bool Bool)
      = Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf false) := rfl

/-- **Aux C4 (a cost-`0` protocol is a leaf).**  General; the shape fact the
consistency instance below turns on. -/
theorem eq_leaf_of_cost_zero {X Y Z : Type*} {P : Protocol X Y Z} (h : P.cost = 0) :
    ∃ z : Z, P = Protocol.leaf z := by
  cases P with
  | leaf z => exact ⟨z, rfl⟩
  | aNode a l r => simp [Protocol.cost] at h
  | bNode b l r => simp [Protocol.cost] at h

/-- **Hypothesis consistency for `le_of_no_completed_protocol`, at `r = 1`.**

The reduction's hypothesis bundle `(1 <= C, href)` is **not** contradictory, and
`href` is not satisfiable only by degenerate `r`: at `C = 1`, `r = 1` and the
two-variable parity game, no protocol of cost at most `C+r-1 = 1` computes it, so
`href` holds while the completion clause is a live constraint (`r >= 1`).  The
reduction then yields `C + r = 2 <= c` for every achievable cost, which is the
true parity bound.

**Labelled BEYOND-PAPER.**  The carriers, the game and the values `C = 1`,
`r = 1` are this probe's own; the frozen frame runs at `C >= 3` (`09:1302`) over
the wrapper interlace, and this instance audits **our** encoding of the
reduction at a point the paper never visits.  It is strictly weaker evidence than
the paper's application point and is not offered as a substitute for it. -/
theorem reduction_hypotheses_consistent :
    (1 : ℕ) ≤ 1
      ∧ (∀ P : Protocol Bool Bool Bool, P.cost ≤ 1 + 1 - 1 → CompletedNoBob P 1 →
          Protocol.Computes P (fun x y => xor x y) → False)
      ∧ (∀ c ∈ AchievableCosts (fun x y : Bool => xor x y), 1 + 1 ≤ c) := by
  have href : ∀ P : Protocol Bool Bool Bool, P.cost ≤ 1 + 1 - 1 → CompletedNoBob P 1 →
      Protocol.Computes P (fun x y => xor x y) → False := by
    intro P hcost _ hf
    cases P with
    | leaf z =>
        have h1 := hf false false
        have h2 := hf false true
        simp only [Protocol.eval] at h1 h2
        rw [h1] at h2
        simp at h2
    | aNode a l r =>
        simp only [Protocol.cost] at hcost
        obtain ⟨zl, rfl⟩ := eq_leaf_of_cost_zero (P := l) (by omega)
        obtain ⟨zr, rfl⟩ := eq_leaf_of_cost_zero (P := r) (by omega)
        have h1 := hf false false
        have h2 := hf false true
        simp only [Protocol.eval] at h1 h2
        rw [h1] at h2
        simp at h2
    | bNode b l r =>
        simp only [Protocol.cost] at hcost
        obtain ⟨zl, rfl⟩ := eq_leaf_of_cost_zero (P := l) (by omega)
        obtain ⟨zr, rfl⟩ := eq_leaf_of_cost_zero (P := r) (by omega)
        have h1 := hf false false
        have h2 := hf true false
        simp only [Protocol.eval] at h1 h2
        rw [h1] at h2
        simp at h2
  exact ⟨le_refl 1, href, le_of_no_completed_protocol (le_refl 1) href⟩

/-- **Rejection probe: padding is not free.**

The completion of the leaf protocol at budget `k` costs exactly `k`: the frozen
"These are actual communicated bits" is not a figure of speech, and the cost
clause of `lem:wrapper-no-bob-completion` is tight at `max{cost(P),r}`.  **Claims
no legality.** -/
theorem completeNoBob_cost_tight (k : ℕ) :
    (completeNoBob k (Protocol.leaf true : Protocol Bool Bool Bool)).cost = k := by
  simp

end Poles

end EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
