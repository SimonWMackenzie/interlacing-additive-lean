import EthInapproximability.ParameterizedNP.WrapperProjectionCovers
import EthInapproximability.ParameterizedNP.TwoStreamState
import EthInapproximability.ParameterizedNP.TerminalStateRealization
import EthInapproximability.ParameterizedNP.TerminalTwoStream
import EthInapproximability.ParameterizedNP.DenseWrapperFrontier
import EthInapproximability.ParameterizedNP.WrapperProtectedEarly
import EthInapproximability.ParameterizedNP.ParameterSchedule
import EthInapproximability.ParameterizedNP.WrapperMassRedistribution

/-!
# Parameterized NP route: the closing layer of `thm:first-wrapper`, and the interface box

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8a54aaa6f0e60eaeb31ac1719cd696b169d5a845381fbd810a18a86c6b2a24e5`),
  **lines 1783--1816** -- the closing `\begin{proof}[Proof of
  \Cref{thm:first-wrapper}]` (`09:1783--1808`) together with the
  `interfacebox` "Boundary of the adapted Stage 4" (`09:1809--1816`).  This is
  the **last** print-order block of Section 9: with it the section is tiled end
  to end, `09:1--273` (`ScaleAlignOpening`), `09:274--334` (`WrapperLowRungs`),
  `09:335--460`, `09:461--657`, `09:658--833`, `09:834--1183`, `09:1184--1366`,
  `09:1367--1511`, `09:1512--1781` (the seven dense-rung blocks), and
  `09:1783--1816` (here).

  The anchors traced here, in the order the frozen block prints them:
  * `09:1784--1786`: "The three one-bit-down clauses were proved in
    `sec:wrapper-low-rungs`, and the full-strength clause was just proved";
  * `09:1786--1791`: "The standard interlace protocol identifies the outer
    coordinate in `r` bits and then runs an optimal protocol for `N`, so
    `comp U <= C + r`";
  * `09:1791--1792`: "Applying `eq:wrapper-u-dense` to the full matrix gives the
    reverse inequality and proves `eq:wrapper-u-exact`";
  * `09:1794--1795`: "Finally set `W = ^T U` and `C_W = C + r`";
  * `09:1795--1804`: "Transposition exchanges the row and column restrictions in
    each one-copy bracket.  Therefore `eq:wrapper-u-dense` becomes
    `comp<W,1,theta,1-delta_U> >= C_W`, while the three clauses in
    `eq:wrapper-u-low` become `Lambda_3(W,1,theta,y) >= C_W - 1`";
  * `09:1804--1805`: "Together with `comp W = C_W`, these are
    `eq:common-exact`--`eq:common-low`";
  * `09:1805--1806`: "The same outer selector adds exactly `r` bits to the `YES`
    protocol";
  * the interface box `09:1810--1816`: "The proof of the scale-aligned Stage-4
    profile `thm:first-wrapper` used the reference `G`, protected reservoirs,
    donor coordinates, and the internal Stage-2 and Stage-3 certificates.  None
    of these objects is an input to the generic bridge.  From this point onward,
    `W` is an ordinary Boolean matrix known only through
    `eq:common-exact`--`eq:common-low` and its explicit `YES` protocol."

* **Reader counterpart.**  `routes/parameterized-np/reader-facing/sections/`
  `A-stage4-details.tex`, `thm:adapted-stage4-profile` (label line 335).  Exactly
  **one** reader item is claimed by this module, and it is one no other
  declaration in `src/` claims:
  * lines **356--357**, "The construction, parameters, carriers, and evaluator
    are identical in the two promise cases" -- claimed by
    `outer_selector_cost_is_shared` and by nothing else.

  **Deliberately not claimed**, to avoid a double assignment:
  * `eq:paper-adapted-stage4-interface` (reader line 345) in all three clauses is
    **already assigned** to `ScaleAlignOpening.commonThreshold_of_wrapper`.  The
    structure `CommonThreshold` below is a *packaging* of the three clauses that
    composition already delivers, carries the autoformalization anchor
    `09:1810--1816` alone, and reclaims no reader item.
  * `def:paper-adapted-stage4` (reader lines 325--331) is already assigned to
    `ScaleAlignOpening.wrapperU` / `wrapperW` / `wrapperW_apply`; nothing here
    redefines either matrix.
  * the reader's `YES` clause (lines 347--350, `comp W <= Y + a + log q_2 + log s
    + r_q`) is the one-level assembly's, as `ScaleAlignOpening`'s header already
    records; `outer_selector_cost_is_shared` is the *generic* selector bound of
    `09:1805--1806` at an arbitrary `YES` cost for `N` and asserts no
    schedule-specific value.
  * reader lines 351--355 (the carrier cardinalities) belong to the
    carrier-recurrence row and are untouched.

## What this module is, and what it is emphatically not

It is the **closing layer**: the composition that turns the two halves of
`thm:first-wrapper` into the three output-contract clauses
`eq:common-exact`--`eq:common-low`, plus the Lean rendering of the boundary the
interface box draws.  It is **not** a discharge of the theorem, and **no route
completion is claimed anywhere**.

### The one deferred binder, named and never assumed

`eq:wrapper-u-dense` (`09:263`) enters **as an explicit named hypothesis**:
the predicate `DenseRung` below, and the binder `hDense` of `firstWrapperClose`.

* It is **not** an `axiom`, and this module declares none.
* It is **not** a conclusion-bearing opaque certificate: `denseRung_not_automatic`
  proves it is **false** at the constant matrix for every `1 <= C + r`, so it is a
  genuine constraint and not a triviality that a green build would hide.
* It is **not** silently discharged: the only route from block content to
  `DenseRung` offered here is `denseRung_of_no_shallow_member`, which is the
  banked `WrapperMassRedistribution.denseRung_of_no_shallow_member` -- itself a
  **bridge, not a discharge** -- re-exported in the named form.

### Conditional statuses of the consumed blocks, disclosed exactly

The seven statement-tiled Section-9 blocks and the schedule module are consumed
**strictly by pin** (imported, cited, never restated).  Their ledger statuses
travel with them unchanged, and this module improves none of them:

1. `WrapperProjectionCovers` (`09:335--460`), `TwoStreamState` (`09:461--657`),
   `TerminalStateRealization` (`09:658--833`) -- landed construction modules; each
   **feeds and does not discharge** `hDenseRung`.
2. `TerminalTwoStream` (`09:834--1183`) -- **the headline
   `lem:terminal-two-stream` is landed as a *stated* claim, not as a proved
   theorem** (`TERMINAL-TWO-STREAM-001`: "No declaration in the module concludes
   it").  Everything this module takes from it is arithmetic that is *proved*
   there -- `terminalTarget`, `terminalTarget_sub_one`, `scale_guard` -- and the
   stated claim `TerminalTwoStream.TerminalTwoStream` is **not** invoked,
   assumed, or weakened anywhere below.
3. `DenseWrapperFrontier` (`09:1184--1366`) and `WrapperProtectedEarly`
   (`09:1367--1511`) -- landed, with the frontier block's GAP-EXPOSED items (no
   protocol object, no routed certificate system) unchanged.
4. `WrapperMassRedistribution` (`09:1512--1781`) -- landed with four GAP-EXPOSED
   items (M1 the protocol and routed certificate system, M2 the
   realization-binder shape mismatch, M3 the two reservoir types, M4
   `hDenseRung` **bridged, not discharged**), and with a **DEFERRED CANONICAL
   INHABITATION** obligation on record: the paper's own instance of that block's
   gate system is not exhibited, its satisfiability endpoint
   `massRedistribution_block_bundle_is_consistent` is an explicitly
   **NON-FIDELITY** probe, and the obligation is discharged only when the
   effective-cutoff pass (`PARAM-001`) lands.  None of that changes here.
5. `ParameterSchedule` (`SCHEDULE-001`) -- consumed only through
   `WrapperMassRedistribution`'s own pins; this module assigns no numeral to any
   quantity `sec:parameters` defines, and states no schedule legality.

### Canonical inhabitation of `CommonThreshold`

The paper constructs exactly one instance of the interface: `W = ^T U` at
`C_W = C + r` (`09:1794--1795`).  That instance is the required witness, and it
is landed here as `commonThreshold_of_firstWrapperClose` -- **conditionally**, on
the named `DenseRung` binder and the low-rung inputs, because the dense rung's
frozen proof (`09:335--1781`) is block-covered but undischarged.

**DEFERRED CANONICAL-INHABITATION OBLIGATION (registered, open).**  An
*unconditional* inhabitant of `CommonThreshold` at the paper's own matrix and at
the schedule's own `C_W` is **not** exhibited here and is not claimed.  It is
discharged exactly when `DenseRung` is proved, i.e. when the routed
certificate system of GAP-EXPOSED M1 lands in Lean -- never by the probe below.
`probeCommonThreshold` is an explicitly **NON-FIDELITY** smoke inhabitant: its
matrix is the two-by-two exchange game `probeW a b = a XOR b` and its `C_W` is
`2`, whereas every legal wrapper output has `C_W = C + r >= 3` and a matrix of
the shape `^T Int_q(N)`.  What it establishes is that the three-clause bundle is
simultaneously satisfiable with **all three fields carrying content**: at
`C_W = 2` the `low` field sits above the `ℕ`-truncation floor, so
`eq:common-low` reads `1 <= Lambda_3(W,1,theta,y)` there and must be proved
rather than inherited from `2 - 2 = 0`.  It establishes nothing about the
paper's `W`, and `commonThreshold_probe_is_not_the_paper_instance` records that
gap kernel-visibly *inside its own statement*, by naming `probeW` and
`CommonThreshold` and refuting the interface at every legal `C_W = C + r`.

**Parameter ranges of the probe, disclosed.**  `delta_U` ranges over `[0, 1/2)`
and `y` over `(0, 1]`; both contain the schedule's own values (`delta_U` is tiny
by `eq:q-deltaU`, and the frozen `y = 3/5` of `06:1110`).  The row threshold
`theta` ranges over `(1/2, 1]`, which does **not** contain the schedule's
`theta = delta/(16 Q)` of `06:533`: any inhabitant with `C_W >= 2` needs at least
two retained rows in the single copy, so a two-element row carrier forces
`card(X) * theta > 1`.  That narrowing is a further NON-FIDELITY departure; it is
disclosed here rather than hidden, and `commonThreshold_probe_needs_dense_rows`
proves it is *forced* rather than chosen.

### Repair record (r1)

Landed against the r0 statement gate, which returned two REVISE items (`R1`,
`R2`) and four record-level items (`A1`--`A4`):

* **R1** -- `commonThreshold_probe_is_not_the_paper_instance` was, comment
  stripped, an arithmetic tautology naming neither `probeW` nor
  `CommonThreshold`, while the module header rested its admission of the probe on
  it.  It now *states* that fact: `probeW` carries `CommonThreshold` at
  `C_W = 2`, and carries it at **no** legal wrapper value `C + r` with `3 <= C`.
  The refutation runs through `probeW_D`, so the statement breaks the moment the
  probe's complexity changes.
* **R2** -- `probeCommonThreshold` inhabited the interface at `C_W = 1`, where
  the `low` field is `1 - 1 = 0 <= _` by `ℕ`-truncation and hence vacuous for
  every `theta`, `delta_U`, `y` (and `y` was constrained by no binder at all).
  Raised, per the gate's option 1, to the exchange game at `C_W = 2`: `probeW_D`
  is an exact `2`, `probeW_dense` proves a two-bit family bound, and `probeW_low`
  proves the untruncated `1 <= Lambda_3`.  All three fields carry content and
  every binder is used.
* **A1** -- the canonical-inhabitation paragraph above describes the raised probe.
* **A2** -- the Section-4 preamble and the `probeW` docstring name the new matrix
  and record why the one-bit game could not carry the `low` field.
* **A3** -- the `probeCommonThreshold` docstring's "three fields" claim is now
  accurate and says *why*, with `commonThreshold_low_carries_content_iff_two_le`
  proving the `C_W >= 2` boundary in the kernel.
* **A4** -- the probe's parameter ranges are disclosed above against the
  schedule's own values, including the `theta` narrowing the raise forces.

Of the 23 declarations the r0 gate returned CLEAR, 20 are byte-identical to the
park; `probeW`, `probeW_D` and `probeW_dense` moved with **R2**, because raising
`C_W` changes the probe matrix, and nothing else moved.  The closing theorem
`firstWrapperClose` under the named `DenseRung` binder, the interface box
`CommonThreshold`, the canonical-inhabitation theorem
`commonThreshold_of_firstWrapperClose`, and the Section-5 endpoint identities are
untouched.

### Axiom surface

`LegacyNPCC.Core` and `LegacyNPCC.Bridge` only, through the existing chain.
`LegacyNPCC.Stage12` is **not** imported and the AGHP balanced-family axiom is
**not** reached.  In particular `one_le_D_of_two_values` below is re-derived from
the banked `WrapperMassRedistribution.le_D_of_no_shallow_protocol` rather than
imported from `NPCC.Stage1`, which is outside both facades.  Every declaration is
`Classical`-only; there is no unproved placeholder of either kind the release
gate scans for, no new `axiom`, and no opaque certificate.
-/

namespace EthInapproximability.ParameterizedNP.FirstWrapperClose

open Finset
open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.ScaleAlignOpening

/-! ## Section 1  `eq:wrapper-u-dense` as a named hypothesis -/

/-- **`eq:wrapper-u-dense` (`09:262--263`), named.**

`comp<U,1,1-delta_U,theta> >= C + r`, written at the banked
`ScaleAlignOpening.wrapperU` and the banked one-copy bracket family.  This is a
**hypothesis**, never an assertion: no declaration in this module proves it, and
`denseRung_not_automatic` shows it is not vacuously true.

Naming it changes nothing about `ScaleAlignOpening.firstWrapper`'s binder -- the
two are definitionally the same proposition, as `denseRung_iff` records -- and it
is introduced only so that the closing layer can pass the deferred half around
under the name the frozen display gives it. -/
def DenseRung {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) (δU θ : ℝ) : Prop :=
  C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
    (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)

/-- **Aux 1.1.**  The named form is literally `ScaleAlignOpening.firstWrapper`'s
`hDenseRung` binder: nothing is strengthened, weakened, or reoriented in the
naming.  General. -/
theorem denseRung_iff {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) (δU θ : ℝ) :
    DenseRung Nmat r C δU θ ↔
      C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
        (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ) :=
  Iff.rfl

/-- **The bridge into the named binder (`09:1188--1193`), consumed by pin.**

The banked `WrapperMassRedistribution.denseRung_of_no_shallow_member` performs
the frozen reduction "fix an arbitrary retained matrix and refute every protocol
of cost at most `C+r-1`" and no more.  This re-export changes only the name of
the conclusion.

**It is a bridge, not a discharge**: the per-member refutation stays the binder
`hmember`, which is exactly GAP-EXPOSED M1 of `WRAPPER-MASS-REDISTRIBUTION-001`
(no protocol object, no routed certificate system).  General. -/
theorem denseRung_of_no_shallow_member {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ : ℝ}
    (hθ1 : θ ≤ 1) (hδ1 : 1 - δU ≤ 1) (hRw : 1 ≤ Fintype.card Rw)
    (hmember : ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ,
      ∀ c ∈ AchievableCosts (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2),
        C + r ≤ c) :
    DenseRung Nmat r C δU θ :=
  WrapperMassRedistribution.denseRung_of_no_shallow_member Nmat r C hθ1 hδ1 hRw hmember

/-- **General aux: a two-valued game needs at least one bit.**

If `g` takes two different values then no cost-`0` protocol computes it, so
`comp g >= 1`.  The `sInf` step is the banked
`WrapperMassRedistribution.le_D_of_no_shallow_protocol` (whose nonemptiness side
condition is the vendored reveal-everything protocol); what is added here is the
leaf case analysis.

Re-derived rather than imported: the vendored `NPCC.Stage1.one_le_D_of_two_values`
lies outside both the `LegacyNPCC.Core` and `LegacyNPCC.Bridge` facades, and this
module does not widen its axiom surface to reach it.  General in both
carriers. -/
theorem one_le_D_of_two_values {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) {a₁ a₂ : A} {b₁ b₂ : B} (hne : g a₁ b₁ ≠ g a₂ b₂) :
    1 ≤ D g := by
  refine WrapperMassRedistribution.le_D_of_no_shallow_protocol g 1 ?_
  rintro c ⟨P, hcost, hcomp⟩
  cases P with
  | leaf z =>
      exfalso
      have h1 := hcomp a₁ b₁
      have h2 := hcomp a₂ b₂
      simp only [Workspace.Types.Protocol.Protocol.eval] at h1 h2
      exact hne (by rw [← h1, ← h2])
  | aNode a l r =>
      subst hcost
      simp [Workspace.Types.Protocol.Protocol.cost]
  | bNode b l r =>
      subst hcost
      simp [Workspace.Types.Protocol.Protocol.cost]

/-- **General aux: a depth-`0` protocol is a leaf.**

Unregistered supporting lemma about the vendored
`Workspace.Types.Protocol.Protocol` tree: both internal constructors cost
`1 + max _ _`, which is never `0`.  Needed to enumerate the shapes a protocol of
cost at most `1` can have.  General in all three type parameters. -/
theorem eq_leaf_of_cost_zero {X Y Z : Type*}
    {P : Workspace.Types.Protocol.Protocol X Y Z} (h : P.cost = 0) :
    ∃ z, P = Workspace.Types.Protocol.Protocol.leaf z := by
  cases P with
  | leaf z => exact ⟨z, rfl⟩
  | aNode a l r =>
      exfalso
      simp only [Workspace.Types.Protocol.Protocol.cost] at h
      omega
  | bNode b l r =>
      exfalso
      simp only [Workspace.Types.Protocol.Protocol.cost] at h
      omega

/-- **General aux: a game depending on both coordinates needs at least two bits.**

A protocol of cost at most `1` is either a leaf (constant), an Alice node with
two leaf children (a function of Alice's input alone), or a Bob node with two
leaf children (a function of Bob's input alone).  So if `g` varies in the row at
some fixed column *and* varies in the column at some fixed row, no such protocol
computes it, and `comp g >= 2`.

This is the depth-`2` companion of `one_le_D_of_two_values`, obtained the same
way -- through the banked
`WrapperMassRedistribution.le_D_of_no_shallow_protocol`, whose nonemptiness side
condition is the vendored reveal-everything protocol -- and, like it, it is
re-derived here rather than imported, so that the module's axiom surface stays
inside `LegacyNPCC.Core` and `LegacyNPCC.Bridge`.  General in both carriers. -/
theorem two_le_D_of_depends_on_both {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) {a₁ a₂ a₀ : A} {b₀ b₁ b₂ : B}
    (hrow : g a₁ b₀ ≠ g a₂ b₀) (hcol : g a₀ b₁ ≠ g a₀ b₂) :
    2 ≤ D g := by
  refine WrapperMassRedistribution.le_D_of_no_shallow_protocol g 2 ?_
  rintro c ⟨P, hcost, hcomp⟩
  by_contra hcon
  have hlt : c < 2 := Nat.lt_of_not_le hcon
  subst hcost
  cases P with
  | leaf z =>
      refine hrow ?_
      have h1 := hcomp a₁ b₀
      have h2 := hcomp a₂ b₀
      simp only [Workspace.Types.Protocol.Protocol.eval] at h1 h2
      rw [← h1, ← h2]
  | aNode a l r =>
      have hzero : l.cost = 0 ∧ r.cost = 0 := by
        simp only [Workspace.Types.Protocol.Protocol.cost] at hlt
        omega
      obtain ⟨zl, rfl⟩ := eq_leaf_of_cost_zero hzero.1
      obtain ⟨zr, rfl⟩ := eq_leaf_of_cost_zero hzero.2
      refine hcol ?_
      have h1 := hcomp a₀ b₁
      have h2 := hcomp a₀ b₂
      simp only [Workspace.Types.Protocol.Protocol.eval] at h1 h2
      rw [← h1, ← h2]
  | bNode b l r =>
      have hzero : l.cost = 0 ∧ r.cost = 0 := by
        simp only [Workspace.Types.Protocol.Protocol.cost] at hlt
        omega
      obtain ⟨zl, rfl⟩ := eq_leaf_of_cost_zero hzero.1
      obtain ⟨zr, rfl⟩ := eq_leaf_of_cost_zero hzero.2
      refine hrow ?_
      have h1 := hcomp a₁ b₀
      have h2 := hcomp a₂ b₀
      simp only [Workspace.Types.Protocol.Protocol.eval] at h1 h2
      rw [← h1, ← h2]

/-- **Statement pole: `DenseRung` is a genuine constraint.**

At the constant matrix over two-element carriers every member of every bracket
family induces a constant subgame, so the family complexity is `0`, and the
binder demands `C + r <= 0`.  Hence `DenseRung` is **false** there for every
`1 <= C + r`: carrying it as a hypothesis defers content and does not smuggle a
triviality past a green build.

The member exhibited is the one the banked `NPCC.bracketGE.nonempty` produces,
and the constant complexity is the banked `PublicRecords.D_const`. -/
theorem denseRung_not_automatic (r C : ℕ) {δU θ : ℝ}
    (hθ1 : θ ≤ 1) (hδ1 : 1 - δU ≤ 1) (hpos : 1 ≤ C + r) :
    ¬ DenseRung (fun (_ : Bool) (_ : Bool) => false) r C δU θ := by
  classical
  intro hD
  have hcard : 1 ≤ Fintype.card (Fin (2 ^ r) × Bool) := by
    have hq : 0 < 2 ^ r := pow_pos (by norm_num) r
    exact Fintype.card_pos_iff.mpr ⟨(⟨0, hq⟩, true)⟩
  obtain ⟨RC, hRC⟩ :=
    NPCC.bracketGE.nonempty (X := Fin (2 ^ r) × Bool) (Y := Fin (2 ^ r) → Bool)
      1 (1 - δU) θ hδ1 hθ1 hcard
  have hconst : subgame (interlaceFun
      (wrapperU (fun (_ : Bool) (_ : Bool) => false) r) 1) RC.1 RC.2
      = fun _ _ => false := rfl
  have hzero : D (subgame (interlaceFun
      (wrapperU (fun (_ : Bool) (_ : Bool) => false) r) 1) RC.1 RC.2) = 0 := by
    rw [hconst]; exact PublicRecords.D_const false
  have hle := HardSeedFacade.Dfamily_le_of_mem
    (interlaceFun (wrapperU (fun (_ : Bool) (_ : Bool) => false) r) 1) _ hRC
  rw [hzero] at hle
  have := le_trans hD hle
  omega

/-! ## Section 2  `09:1786--1806`: the closing derivation -/

/-- **`09:1786--1791`, the `YES`-side selector at the `NO`-case value.**

"The standard interlace protocol identifies the outer coordinate in `r` bits and
then runs an optimal protocol for `N`, so `comp U <= C + r`."  The selector is
the banked `ScaleAlignOpening.wrapperU_yes_upper`, consumed by pin; the only step
added is the substitution of the exact identity `comp N = C` (`09:242`).

This is the **upper** half of `eq:wrapper-u-exact` and is unconditional: it uses
neither `DenseRung` nor any block content.  General. -/
theorem wrapperU_le_of_exact {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) (hN : D Nmat = C) :
    D (wrapperU Nmat r) ≤ C + r := by
  have h := wrapperU_yes_upper Nmat r
  rwa [hN] at h

/-- **`09:1805--1806`: "The same outer selector adds exactly `r` bits to the
`YES` protocol."**

*Reader counterpart:* `A-stage4-details.tex` lines **356--357**, "The
construction, parameters, carriers, and evaluator are identical in the two
promise cases."  That is exactly the content proved here: `wrapperU Nmat r` is
one term, built from `Nmat` and `r` alone, and the very same banked selector
bound `ScaleAlignOpening.wrapperU_yes_upper` produces the `NO`-case value
`C + r` (via `wrapperU_le_of_exact`, at `comp N = C`) and the `YES`-case value
`yesN + r` (here, at any upper bound `yesN` for `comp N`).  No second
construction, no second parameter set, no second carrier appears.

General in `yesN`: no schedule-specific `YES` budget is asserted, which is why
the reader's own `YES` display (lines 347--350) is **not** claimed. -/
theorem outer_selector_cost_is_shared {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r yesN : ℕ) (hyes : D Nmat ≤ yesN) :
    D (wrapperU Nmat r) ≤ yesN + r :=
  le_trans (wrapperU_yes_upper Nmat r) (by omega)

/-- **The closing proof of `thm:first-wrapper` (`09:1783--1808`).**

Hypotheses, in the frozen order:

* `hC : 3 <= C` (`09:240`) and `hN : comp N = C` (`09:242`);
* the density guards of the scheduled `theta`, `delta_U` and the frozen
  `y = 3/5`, and the two carrier nonemptiness facts the bracket families need;
* `hDense : DenseRung N r C delta_U theta` -- `eq:wrapper-u-dense`, the **named,
  undischarged** binder whose frozen proof is the seven blocks `09:335--1781`;
* `hne`, `hmem` -- the low-rung inputs of `sec:wrapper-low-rungs` (`09:274--334`),
  consumed by the banked `WrapperLowRungs.firstWrapperOfLowRungs`, which
  discharges `eq:wrapper-u-low` from them.

Conclusions, in frozen print order:

1. `comp U <= C + r` (`09:1789--1791`);
2. `comp U = C + r`, i.e. `eq:wrapper-u-exact` (`09:1791--1792`);
3. `comp W = C_W` at `W = ^T U`, `C_W = C + r`, i.e. `eq:common-exact`;
4. `comp<W,1,theta,1-delta_U> >= C_W`, i.e. `eq:common-dense`;
5. `Lambda_3(W,1,theta,y) >= C_W - 1`, i.e. `eq:common-low`.

Items 2--5 are the banked `WrapperLowRungs.firstWrapperOfLowRungs` composed with
the named binder; item 1 is `wrapperU_le_of_exact`, surfaced because the frozen
closing paragraph states it explicitly and the composition does not return it.
Nothing is weakened: `theta`, `delta_U` and `y` are quantified exactly as they
are there, and the `U`-side clauses `eq:wrapper-u-dense`/`eq:wrapper-u-low`
remain available from that composition unchanged. -/
theorem firstWrapperClose {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ y : ℝ}
    (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hDense : DenseRung Nmat r C δU θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2)) :
    D (wrapperU Nmat r) ≤ C + r
      ∧ D (wrapperU Nmat r) = C + r
      ∧ D (wrapperW Nmat r) = C + r
      ∧ C + r ≤ Dfamily (interlaceFun (wrapperW Nmat r) 1)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 1 θ (1 - δU))
      ∧ C + r - 1 ≤ LambdaGE (wrapperW Nmat r) 1 θ y := by
  obtain ⟨hexact, -, -, -, hWexact, hWdense, hWlow⟩ :=
    WrapperLowRungs.firstWrapperOfLowRungs Nmat r C hC hN hθ0 hθ1 hδ0 hδ1 hy0 hy1
      hRw hCl hDense hne hmem
  exact ⟨wrapperU_le_of_exact Nmat r C hN, hexact, hWexact, hWdense, hWlow⟩

/-! ## Section 3  `09:1810--1816`: the interface box -/

/-- **The boundary of the adapted Stage 4 (`09:1810--1816`), as a record.**

"From this point onward, `W` is an ordinary Boolean matrix known only through
`eq:common-exact`--`eq:common-low` and its explicit `YES` protocol."

The three fields are exactly the three displays of `09:16--22`, at one common row
threshold `theta`, and there are **no other fields**.  That is the whole content
of the box: the reference `G`, the protected reservoirs, the donor coordinates
and the internal Stage-2 and Stage-3 certificates are absent from the type, so no
consumer can read them back out.

**The `YES` protocol is deliberately not a field.**  `09:1815` lists it beside
the three displays, but `thm:first-wrapper` states the `NO` clauses and the `YES`
clause as the two promise cases of one construction (`09:258--272`), and
conjoining them is inconsistent in the intended regime -- see
`promise_cases_do_not_conjoin` and `commonThreshold_excludes_a_cheap_yes`.  The
`YES` side therefore travels as the separate, unconditional
`outer_selector_cost_is_shared`.

`Prop`-valued and general in the carriers, in the matrix, in `C_W`, and in the
three real parameters. -/
structure CommonThreshold {X Y : Type*} [Fintype X] [Fintype Y]
    (Wmat : X → Y → Bool) (CW : ℕ) (θ δU y : ℝ) : Prop where
  /-- `eq:common-exact` (`09:17`): `comp W = C_W`. -/
  exact : D Wmat = CW
  /-- `eq:common-dense` (`09:18--19`): `comp<W,1,theta,1-delta_U> >= C_W`. -/
  dense : CW ≤ Dfamily (interlaceFun Wmat 1) (bracketGE X Y 1 θ (1 - δU))
  /-- `eq:common-low` (`09:20--21`): `Lambda_3(W,1,theta,y) >= C_W - 1`. -/
  low : CW - 1 ≤ LambdaGE Wmat 1 θ y

/-- **Canonical inhabitation: the paper's own instance (`09:1794--1804`).**

The paper constructs exactly one object satisfying the interface -- `W = ^T U` at
`C_W = C + r` -- so that instance, and not a synthetic one, is the required
witness.  It is delivered here from `firstWrapperClose`, hence **conditionally**
on the named `DenseRung` binder and the low-rung inputs.

This is the fidelity test in the required direction: the encoding is not merely
inhabited, it is inhabited *by the paper's matrix at the paper's `C_W`*.  What is
still open is the unconditional form, and it is open for exactly one reason --
`DenseRung` is undischarged.  See the module header's registered deferred
obligation. -/
theorem commonThreshold_of_firstWrapperClose {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ y : ℝ}
    (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hDense : DenseRung Nmat r C δU θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2)) :
    CommonThreshold (wrapperW Nmat r) (C + r) θ δU y := by
  obtain ⟨-, -, hWexact, hWdense, hWlow⟩ :=
    firstWrapperClose Nmat r C hC hN hθ0 hθ1 hδ0 hδ1 hy0 hy1 hRw hCl hDense hne hmem
  exact ⟨hWexact, hWdense, hWlow⟩

/-! ### Aux battery for `CommonThreshold` -/

/-- **Battery 1 (identity).**  The interface pins `C_W` uniquely: two records for
the same matrix at the same densities agree on `C_W`, because both name
`comp W`.  General. -/
theorem commonThreshold_determines_CW {X Y : Type*} [Fintype X] [Fintype Y]
    {Wmat : X → Y → Bool} {CW CW' : ℕ} {θ δU y θ' δU' y' : ℝ}
    (h : CommonThreshold Wmat CW θ δU y) (h' : CommonThreshold Wmat CW' θ' δU' y') :
    CW = CW' := by
  rw [← h.exact, ← h'.exact]

/-- **Battery 2 (the dense clause is saturated, not an over-demand).**

`Dfamily` is a minimum over members, so it never exceeds the complexity of the
ambient one-copy interlace, which in turn never exceeds `comp W`.  Together with
`eq:common-exact` this upgrades the frozen inequality `eq:common-dense` to an
**equality**: the interface demands exactly what the matrix can supply, and its
two nontrivial fields cannot be jointly contradictory for a magnitude reason.

The two ingredients are the banked `NPCC.familyComplexity_le_ambient` and the
banked one-copy selector `NPCC.interlace_selector_upper` at `p = 1`, consumed by
pin.  General. -/
theorem commonThreshold_dense_is_saturated {X Y : Type*} [Fintype X] [Fintype Y]
    {Wmat : X → Y → Bool} {CW : ℕ} {θ δU y : ℝ}
    (hθ1 : θ ≤ 1) (hδ1 : 1 - δU ≤ 1) (hX : 1 ≤ Fintype.card X)
    (h : CommonThreshold Wmat CW θ δU y) :
    Dfamily (interlaceFun Wmat 1) (bracketGE X Y 1 θ (1 - δU)) = CW := by
  classical
  haveI : DecidableEq X := Classical.decEq _
  have hne := NPCC.bracketGE.nonempty (X := X) (Y := Y) 1 θ (1 - δU) hθ1 hδ1 hX
  have hfam := familyComplexity_le_ambient (interlaceFun Wmat 1) hne
  have hone : D (interlaceFun Wmat 1) ≤ D Wmat := by
    have h1 := interlace_selector_upper Wmat 1 (le_refl 1)
    rwa [Nat.clog_one_right, Nat.add_zero] at h1
  have hup : Dfamily (interlaceFun Wmat 1) (bracketGE X Y 1 θ (1 - δU)) ≤ CW := by
    rw [← h.exact]; exact le_trans hfam hone
  have hdn := h.dense
  omega

/-- **Battery 3 (round trip along an entrywise identification).**

The interface is a statement about the entry function and nothing else, so it
transports along a pointwise equality of matrices.  This is the smallest honest
rendering of "`W` is an ordinary Boolean matrix": no field can distinguish two
matrices with the same entries, whatever their provenance.  General. -/
theorem commonThreshold_congr {X Y : Type*} [Fintype X] [Fintype Y]
    {W₁ W₂ : X → Y → Bool} {CW : ℕ} {θ δU y : ℝ}
    (hW : ∀ a b, W₁ a b = W₂ a b) (h : CommonThreshold W₁ CW θ δU y) :
    CommonThreshold W₂ CW θ δU y := by
  have hfun : W₁ = W₂ := funext fun a => funext fun b => hW a b
  subst hfun
  exact h

/-- **Battery 4 (the trivial witness fails).**

A constant matrix inhabits the interface only at `C_W = 0`: `eq:common-exact`
alone forces it, because a constant game has a cost-`0` protocol.  Hence at every
legal wrapper output, where `C_W = C + r >= 3`, the constant matrix is **not** a
model, and `CommonThreshold` at `C_W >= 1` is not satisfied by the degenerate
object.  This is the existential pole the interface needs: the deliverable is not
met by the trivial witness.  General in the carriers and in the constant. -/
theorem commonThreshold_of_constant_forces_zero {X Y : Type*} [Fintype X] [Fintype Y]
    (b : Bool) {CW : ℕ} {θ δU y : ℝ}
    (h : CommonThreshold (fun (_ : X) (_ : Y) => b) CW θ δU y) : CW = 0 := by
  rw [← h.exact]; exact PublicRecords.D_const b

/-- **Battery 5 (the two promise cases must not be conjoined).**

If a matrix satisfies `eq:common-exact` at `C_W` and also admits a protocol of
cost at most `yesCost`, then `C_W <= yesCost`.  Contrapositively, a `YES` budget
strictly below `C_W` is inconsistent with the `NO` clause -- which is why the
`YES` protocol of `09:1815` is *not* a field of `CommonThreshold` and travels as
`outer_selector_cost_is_shared` instead.

This is the hypothesis-consistency receipt for the structure: the frozen text
states the two as separate cases of one construction (`09:258--272`), and the
encoding keeps them separate.  General. -/
theorem promise_cases_do_not_conjoin {X Y : Type*} [Fintype X] [Fintype Y]
    {Wmat : X → Y → Bool} {CW yesCost : ℕ}
    (hno : D Wmat = CW) (hyes : D Wmat ≤ yesCost) : CW ≤ yesCost := by
  omega

/-- **Battery 5b.**  The same fact stated on the record, in the refutation form
the statement pole wants: a `YES` cost strictly below `C_W` is impossible for a
matrix carrying the interface.  General. -/
theorem commonThreshold_excludes_a_cheap_yes {X Y : Type*} [Fintype X] [Fintype Y]
    {Wmat : X → Y → Bool} {CW yesCost : ℕ} {θ δU y : ℝ}
    (h : CommonThreshold Wmat CW θ δU y) (hyes : D Wmat ≤ yesCost)
    (hlt : yesCost < CW) : False := by
  have := promise_cases_do_not_conjoin h.exact hyes
  omega

/-- **Battery 6 (where the `low` field starts to carry content).**

`eq:common-low` is written `C_W - 1 <= Lambda_3(W,1,theta,y)` with `C_W : ℕ`, so
the subtraction is truncated.  The exact boundary, both directions:

* below the boundary the clause is free -- at `C_W <= 1` it holds for **every**
  matrix, every `theta` and every `y`, so an inhabitant at `C_W = 1` certifies
  nothing about `Lambda_3`;
* at and above the boundary it bites -- from `C_W >= 2` the record yields the
  untruncated positive statement `1 <= Lambda_3(W,1,theta,y)`, which is false
  whenever the bracket family at `(theta, y)` has a constant member.

This is the kernel-visible form of the reason the probe below is stated at
`C_W = 2` and not at `C_W = 1`.  General. -/
theorem commonThreshold_low_carries_content_iff_two_le {X Y : Type*}
    [Fintype X] [Fintype Y] :
    (∀ (Wmat : X → Y → Bool) (CW : ℕ) (θ y : ℝ), CW ≤ 1 →
        CW - 1 ≤ LambdaGE Wmat 1 θ y)
      ∧ (∀ (Wmat : X → Y → Bool) (CW : ℕ) (θ δU y : ℝ),
          CommonThreshold Wmat CW θ δU y → 2 ≤ CW →
            1 ≤ LambdaGE Wmat 1 θ y) := by
  refine ⟨fun Wmat CW θ y hCW => by omega, fun Wmat CW θ δU y h hCW => ?_⟩
  have hlow := h.low
  omega

/-! ## Section 4  The `NON-FIDELITY` smoke inhabitant

Read the module header before consuming anything in this section: these
declarations are **not** the canonical inhabitation of `CommonThreshold`, and
they do not discharge the deferred obligation registered there.

**A2 (r1 record).**  The r0 probe was the one-bit Bob game `fun _ c => c` at
`C_W = 1`.  That game cannot carry the `low` field at all: `eq:common-low` reads
`C_W - 1 <= Lambda_3` with `C_W : ℕ`, so at `C_W = 1` it is `0 <= _` and holds
for every `theta` and every `y` -- see
`commonThreshold_low_carries_content_iff_two_le`.  The probe is therefore raised
to a game of complexity exactly `2`, the least value at which all three fields
demand something. -/

/-- **NON-FIDELITY probe matrix.**  The two-by-two exchange game
`probeW a b = a XOR b`: the smallest Boolean matrix that depends on both
coordinates, hence the smallest one whose complexity is `2` rather than `1`.

It is *not* the paper's `W`: the paper's matrix is `^T Int_q(N)` at a protected
Stage-4 matrix `N`, with `|Rows(W)| = n_N^q` and `C_W = C + r >= 3`.  This object
exists only to show that the three-clause bundle has a model in which no field is
free. -/
def probeW : Bool → Bool → Bool := fun a b => xor a b

/-- **The probe's exact complexity is `2`.**

Upper: the explicit depth-`2` protocol in which Alice announces her bit and Bob
then announces his, the four leaves carrying the four entries.  Lower: the game
varies in the row at the column `false` and varies in the column at the row
`false`, so `two_le_D_of_depends_on_both` applies.  Not general -- this is a
probe. -/
theorem probeW_D : D probeW = 2 := by
  refine Nat.le_antisymm ?_ (two_le_D_of_depends_on_both probeW
    (a₁ := false) (a₂ := true) (b₀ := false)
    (a₀ := false) (b₁ := false) (b₂ := true) (by decide) (by decide))
  refine Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.aNode (fun a => a)
    (Workspace.Types.Protocol.Protocol.bNode (fun b => b)
      (Workspace.Types.Protocol.Protocol.leaf false)
      (Workspace.Types.Protocol.Protocol.leaf true))
    (Workspace.Types.Protocol.Protocol.bNode (fun b => b)
      (Workspace.Types.Protocol.Protocol.leaf true)
      (Workspace.Types.Protocol.Protocol.leaf false)), ?_, ?_⟩
  · simp [Workspace.Types.Protocol.Protocol.cost]
  · intro a b
    cases a <;> cases b <;> rfl

/-- **Both rows of the single copy survive above row density `1/2`.**

On a two-element row carrier the bracket threshold is `ceil(2 theta)`, which is
`2` as soon as `theta > 1/2`; the fibre of the single copy has at most two
elements, so it is the whole of `Fin 1 x Bool`.  This is the step that forces the
probe's `theta` range, and it is why the raise costs a narrowing there: an
inhabitant with `C_W >= 2` needs two retained rows, because a one-row subgame is
computed by one bit. -/
theorem probe_rows_retained {θ : ℝ} (hθ2 : 1 / 2 < θ)
    {R : Finset (Fin 1 × Bool)}
    (hRow : IsEquipartitionedGE R (Finset.univ : Finset (Fin 1))
      ⌈(Fintype.card Bool : ℝ) * θ⌉₊) :
    ((0 : Fin 1), false) ∈ R ∧ ((0 : Fin 1), true) ∈ R := by
  classical
  have hrowth : (2 : ℕ) ≤ (R.filter (fun p => p.1 = (0 : Fin 1))).card := by
    refine le_trans ?_ (hRow 0 (Finset.mem_univ _))
    have hpos : (1 : ℝ) < (Fintype.card Bool : ℝ) * θ := by
      simp only [Fintype.card_bool]
      push_cast
      linarith
    exact Nat.lt_ceil.mpr (by push_cast; exact hpos)
  have hFuniv : R.filter (fun p => p.1 = (0 : Fin 1)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    have hle : (R.filter (fun p => p.1 = (0 : Fin 1))).card
        ≤ Fintype.card (Fin 1 × Bool) := Finset.card_le_univ _
    have hcard2 : Fintype.card (Fin 1 × Bool) = 2 := by simp
    omega
  constructor
  · have hmem : ((0 : Fin 1), false) ∈ R.filter (fun p => p.1 = (0 : Fin 1)) := by
      rw [hFuniv]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hmem).1
  · have hmem : ((0 : Fin 1), true) ∈ R.filter (fun p => p.1 = (0 : Fin 1)) := by
      rw [hFuniv]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hmem).1

/-- **The probe's dense clause fires, at the full two bits.**

At row density `1/2 < theta <= 1` and column deficiency `0 <= delta_U < 1/2` --
a `delta_U` range that contains the schedule's own, which `eq:q-deltaU` makes
tiny -- every member of the one-copy bracket family keeps **both** columns (the
ceiling `ceil(2(1 - delta_U))` is `2`) and **both** rows of the single copy (the
ceiling `ceil(2 theta)` is `2`).  The induced subgame is therefore the whole
exchange game, which depends on both coordinates, so its complexity is at
least `2`.

This is the field the raise makes hardest: at the r0 probe it asked for one bit
and Bob's column alone supplied it. -/
theorem probeW_dense {θ δU : ℝ} (hθ2 : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hδ0 : 0 ≤ δU) (hδ2 : δU < 1 / 2) :
    2 ≤ Dfamily (interlaceFun probeW 1) (bracketGE Bool Bool 1 θ (1 - δU)) := by
  classical
  have hcard : 1 ≤ Fintype.card Bool := by simp
  have hδ1 : 1 - δU ≤ 1 := by linarith
  have hne := NPCC.bracketGE.nonempty (X := Bool) (Y := Bool) 1 θ (1 - δU) hθ1 hδ1 hcard
  refine EthBridge.le_Dfamily _ _ 2 hne ?_
  rintro ⟨R, Cs⟩ ⟨hRow, hCol⟩
  -- the column side keeps every column
  have hcolth : (2 : ℕ) ≤ Cs.card := by
    refine le_trans ?_ hCol
    have hpos : (1 : ℝ) < ((Fintype.card Bool : ℝ) ^ (1 : ℕ)) * (1 - δU) := by
      simp only [Fintype.card_bool, pow_one]
      push_cast
      linarith
    exact Nat.lt_ceil.mpr (by push_cast; exact hpos)
  have hCuniv : Cs = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    have hle : Cs.card ≤ Fintype.card (Fin 1 → Bool) := Finset.card_le_univ _
    have hcard2 : Fintype.card (Fin 1 → Bool) = 2 := by simp
    omega
  -- the row side keeps both rows of the single copy
  obtain ⟨hr0, hr1⟩ := probe_rows_retained hθ2 hRow
  refine two_le_D_of_depends_on_both (subgame (interlaceFun probeW 1) R Cs)
    (a₁ := ⟨_, hr0⟩) (a₂ := ⟨_, hr1⟩)
    (b₀ := ⟨fun _ => false, by rw [hCuniv]; exact Finset.mem_univ _⟩)
    (a₀ := ⟨_, hr0⟩)
    (b₁ := ⟨fun _ => false, by rw [hCuniv]; exact Finset.mem_univ _⟩)
    (b₂ := ⟨fun _ => true, by rw [hCuniv]; exact Finset.mem_univ _⟩) ?_ ?_
  · simp [subgame, interlaceFun, probeW]
  · simp [subgame, interlaceFun, probeW]

/-- **The probe's low clause fires, untruncated.**

`Lambda_3` at `p = 1` is the minimum of the rungs at `y`, `y/2`, `y/4` with
offsets `0, 1, 2`; the two offset rungs are at least `1` for free, so the content
is the `y`-rung.  Every member of that rung keeps both rows of the single copy
(row density above `1/2`) and at least one column (`ceil(2 y) >= 1` for
`y > 0`), and the exchange game separates the two rows at *every* column, so the
induced subgame is non-constant and costs at least one bit.

`y` ranges over `(0, 1]`, which contains the frozen `y = 3/5` of `06:1110`, and
the upper bound is used: it is the side condition under which the three bracket
families of `Lambda_3` are nonempty, without which `Dfamily` would collapse to
the `sInf` of the empty set. -/
theorem probeW_low {θ y : ℝ} (hθ2 : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    1 ≤ LambdaGE probeW 1 θ y := by
  classical
  have hcard : 1 ≤ Fintype.card Bool := by simp
  have hrung : 1 ≤ Dfamily (interlaceFun probeW 1) (bracketGE Bool Bool 1 θ y) := by
    have hne := NPCC.bracketGE.nonempty (X := Bool) (Y := Bool) 1 θ y hθ1 hy1 hcard
    refine EthBridge.le_Dfamily _ _ 1 hne ?_
    rintro ⟨R, Cs⟩ ⟨hRow, hCol⟩
    obtain ⟨hr0, hr1⟩ := probe_rows_retained hθ2 hRow
    have hcolpos : (1 : ℕ) ≤ Cs.card := by
      refine le_trans ?_ hCol
      have hpos : (0 : ℝ) < ((Fintype.card Bool : ℝ) ^ (1 : ℕ)) * y := by
        simp only [Fintype.card_bool, pow_one]
        push_cast
        linarith
      exact Nat.ceil_pos.mpr hpos
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcolpos)
    refine one_le_D_of_two_values (subgame (interlaceFun probeW 1) R Cs)
      (a₁ := ⟨_, hr0⟩) (a₂ := ⟨_, hr1⟩) (b₁ := ⟨c, hc⟩) (b₂ := ⟨c, hc⟩) ?_
    cases hcval : c 0 <;>
      simp [subgame, interlaceFun, probeW, hcval]
  unfold LambdaGE
  omega

/-- **NON-FIDELITY smoke inhabitation of `CommonThreshold`, at `C_W = 2`.**

The three-clause bundle is simultaneously satisfiable at `C_W = 2`, and at that
value **all three fields carry content**:

* `exact` is the exact complexity `2` of the exchange game, not an upper bound;
* `dense` demands two full bits from every member of the `(theta, 1 - delta_U)`
  bracket family, which is `probeW_dense` and needs both rows and both columns;
* `low` demands `2 - 1 = 1 <= Lambda_3`, which is above the `ℕ`-truncation floor
  of `commonThreshold_low_carries_content_iff_two_le`, so it is `probeW_low` and
  not an artefact of the subtraction.  Every binder is used: `theta` by the row
  ceiling, `delta_U` by the column ceiling, and `y` by the nonemptiness of the
  three `Lambda_3` rungs.

**It is not the canonical inhabitation.**  The paper's instance is
`commonThreshold_of_firstWrapperClose`; this probe's matrix is not the paper's,
its `C_W` is `2` where every legal wrapper output has `C_W >= 3`, and its
`theta` range is narrower than the schedule's -- all three gaps are recorded in
the module header and the first two in
`commonThreshold_probe_is_not_the_paper_instance`.  The deferred obligation in
the module header is discharged only when `DenseRung` is proved. -/
theorem probeCommonThreshold {θ δU y : ℝ} (hθ2 : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hδ0 : 0 ≤ δU) (hδ2 : δU < 1 / 2) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    CommonThreshold probeW 2 θ δU y where
  exact := probeW_D
  dense := probeW_dense hθ2 hθ1 hδ0 hδ2
  low := by simpa using probeW_low hθ2 hθ1 hy0 hy1

/-- **The probe's `theta` narrowing is forced, not chosen.**

At row density `theta <= 1/2` the single copy may be cut to one row -- the
one-element row set `{(0, true)}` is `ceil(2 theta)`-equipartitioned there -- and
a one-row subgame is computed by one bit of Bob.  So the dense clause caps at
`1` and `CommonThreshold probeW 2 theta delta_U y` is **false**.

This is the statement pole for the raise: the probe's `(1/2, 1]` range for
`theta` is the exact price of `C_W = 2` on a two-element row carrier, and the
disclosure in the module header is a theorem rather than a caveat. -/
theorem commonThreshold_probe_needs_dense_rows {θ δU y : ℝ}
    (hθ2 : θ ≤ 1 / 2) (hδ0 : 0 ≤ δU) :
    ¬ CommonThreshold probeW 2 θ δU y := by
  classical
  intro h
  -- a legal member that keeps one row and both columns
  have hmemR : IsEquipartitionedGE ({((0 : Fin 1), true)} : Finset (Fin 1 × Bool))
      (Finset.univ : Finset (Fin 1)) ⌈(Fintype.card Bool : ℝ) * θ⌉₊ := by
    intro q _
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    have hceil : ⌈(Fintype.card Bool : ℝ) * θ⌉₊ ≤ 1 := by
      refine Nat.ceil_le.mpr ?_
      simp only [Fintype.card_bool]
      push_cast
      linarith
    have hfilter :
        (({((0 : Fin 1), true)} : Finset (Fin 1 × Bool)).filter
          (fun p => p.1 = (0 : Fin 1))).card = 1 := by decide
    omega
  have hmemC : ⌈((Fintype.card Bool : ℝ) ^ (1 : ℕ)) * (1 - δU)⌉₊
      ≤ (Finset.univ : Finset (Fin 1 → Bool)).card := by
    have hcard2 : (Finset.univ : Finset (Fin 1 → Bool)).card = 2 := by simp
    have hceil : ⌈((Fintype.card Bool : ℝ) ^ (1 : ℕ)) * (1 - δU)⌉₊ ≤ 2 := by
      refine Nat.ceil_le.mpr ?_
      simp only [Fintype.card_bool, pow_one]
      push_cast
      linarith
    omega
  have hmem : (({((0 : Fin 1), true)} : Finset (Fin 1 × Bool)),
      (Finset.univ : Finset (Fin 1 → Bool))) ∈ bracketGE Bool Bool 1 θ (1 - δU) :=
    ⟨hmemR, hmemC⟩
  have hle := HardSeedFacade.Dfamily_le_of_mem (interlaceFun probeW 1) _ hmem
  -- the one-row subgame is computed by one bit of Bob
  have hone : D (subgame (interlaceFun probeW 1)
      ({((0 : Fin 1), true)} : Finset (Fin 1 × Bool))
      (Finset.univ : Finset (Fin 1 → Bool))) ≤ 1 := by
    refine Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.bNode (fun c => c.val 0)
      (Workspace.Types.Protocol.Protocol.leaf true)
      (Workspace.Types.Protocol.Protocol.leaf false), ?_, ?_⟩
    · simp [Workspace.Types.Protocol.Protocol.cost]
    · rintro ⟨a, ha⟩ ⟨c, hc⟩
      have haval : a = ((0 : Fin 1), true) := Finset.mem_singleton.mp ha
      subst haval
      cases hcval : c 0 <;>
        simp [Workspace.Types.Protocol.Protocol.eval, subgame, interlaceFun,
          probeW, hcval]
  have hle' : Dfamily (interlaceFun probeW 1) (bracketGE Bool Bool 1 θ (1 - δU))
      ≤ D (subgame (interlaceFun probeW 1)
        ({((0 : Fin 1), true)} : Finset (Fin 1 × Bool))
        (Finset.univ : Finset (Fin 1 → Bool))) := hle
  have hdense := h.dense
  omega

/-- **The probe is nondegenerate, and it is not the paper's instance.**

Three clauses, all kernel-visible, and all of them *about* `probeW` and
`CommonThreshold` rather than about arithmetic:

* satisfiability -- `probeW` really does carry the interface, at `C_W = 2`, at
  every legal density triple in the probe's disclosed ranges;
* nondegeneracy -- that `C_W` is nonzero, so the record is not the empty bound
  `C_W = 0` at which `commonThreshold_of_constant_forces_zero` shows the constant
  matrix is stuck;
* non-fidelity -- at **no** legal wrapper value `C_W = C + r` with `3 <= C` does
  `probeW` carry the interface, at any densities whatever.  The refutation runs
  through `probeW_D`: the `exact` field would force `2 = C + r`.

The third clause is the one the module header rests on, and it is now a checked
fact about the two named objects rather than an arithmetic remark that happens to
be printed beside them. -/
theorem commonThreshold_probe_is_not_the_paper_instance {θ δU y : ℝ}
    (hθ2 : 1 / 2 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 ≤ δU) (hδ2 : δU < 1 / 2)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    CommonThreshold probeW 2 θ δU y
      ∧ (2 : ℕ) ≠ 0
      ∧ ∀ (C r : ℕ) (θ' δU' y' : ℝ), 3 ≤ C →
          ¬ CommonThreshold probeW (C + r) θ' δU' y' := by
  refine ⟨probeCommonThreshold hθ2 hθ1 hδ0 hδ2 hy0 hy1, two_ne_zero, ?_⟩
  intro C r θ' δU' y' hC h
  have hx := h.exact
  rw [probeW_D] at hx
  omega

/-! ## Section 5  The dense-rung endpoints, and the closing value `C`

The frozen closing paragraph reads "This again contradicts the shallow protocol"
(`09:1780`) -- *again*, because the three Localized-Extension calls the dense
argument fires all land at the **same** value `C`.  The three banked identities
are consumed by pin here and composed into the closing layer's reading; nothing
is restated and no call is invoked. -/

/-- **The dense-rung endpoints agree (`09:1505--1507`, `09:1775--1778`).**

Both banked identities at the frozen dyadic exponents `s = 2^{r_3}`,
`q_2 = 2^{r_2}`, `kappa = 2^{ell}`:

* call (iv)'s terminal endpoint `B_cap + log_2 kappa = C`
  (`WrapperMassRedistribution.terminalEndpoint_identity`);
* call (iii)'s endpoint `B_cap + log_2 K_int = C + log_2 kappa - 1`, written
  subtraction-free (`WrapperProtectedEarly.endpoint_identity`);

both against the same `C = TerminalTwoStream.terminalTarget b_cap r_2 r_3 =
D_2 + log_2 s + 1` of `09:1038`/`09:1777`.  Consumed by pin from three modules;
general in the four exponents. -/
theorem denseRungEndpoints_agree (bcap r₂ r₃ ℓ : ℕ) :
    bcap + (r₃ + 1 + r₂) = TerminalTwoStream.terminalTarget bcap r₂ r₃
      ∧ DenseBranchSelection.Dtwo bcap r₂ + (r₃ + ℓ) + 1
          = TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ :=
  ⟨WrapperMassRedistribution.terminalEndpoint_identity bcap r₂ r₃,
    WrapperProtectedEarly.endpoint_identity bcap r₂ r₃ ℓ⟩

/-- **The frozen `C >= 3` of `09:240` is *derived* at the terminal endpoint.**

`thm:first-wrapper` opens "Assume `C >= 3`".  At the value the dense rung's own
endpoints deliver, that is not an extra assumption: the banked
`TerminalTwoStream.scale_guard` gives `D_2 >= 2` from `q_2 >= 16`
(`09:1148--1149`), and `terminalTarget = D_2 + log_2 s + 1` adds at least one
more.  So the closing layer's `hC` is discharged from a Stage-2 width gate the
schedule already carries, rather than assumed afresh.  General in the three
exponents. -/
theorem three_le_terminalTarget (bcap r₂ r₃ : ℕ) (h16 : 16 ≤ 2 ^ r₂) :
    3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ := by
  have h := TerminalTwoStream.scale_guard bcap r₂ h16
  simp only [TerminalTwoStream.terminalTarget]
  omega

/-- **`09:1780`, "This again contradicts the shallow protocol", with `hC`
discharged.**

The banked `WrapperMassRedistribution.terminalCall_contradiction` takes the
frozen `C >= 3` as a hypothesis; at the terminal endpoint that hypothesis is now
`three_le_terminalTarget`, so the refutation of the alleged `(C+r-1)`-bit
protocol needs only the budget and the Extension endpoint.  One hypothesis fewer,
no new mathematics, and **no discharge of `DenseRung`**: this is the frozen
contradiction *inside* the dense argument, not the dense rung itself. -/
theorem closing_budget_refutation {bcap r₂ r₃ r B : ℕ} (h16 : 16 ≤ 2 ^ r₂)
    (hbudget : B + r ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    (hExtension : bcap + (r₃ + 1 + r₂) ≤ B) : False :=
  WrapperMassRedistribution.terminalCall_contradiction
    (three_le_terminalTarget bcap r₂ r₃ h16) hbudget hExtension

/-- **The closing layer at the terminal value.**

Assembling the section: if the closing layer's `C` is the value the dense rung's
endpoints deliver, then `hC` comes for free and the whole closing derivation
runs on the named `DenseRung` binder and the low-rung inputs alone.  The
conclusion is verbatim `firstWrapperClose`'s; the only change is that `3 <= C` is
now produced rather than requested.

Still **conditional on `DenseRung`**, and still claiming no route completion. -/
theorem firstWrapperClose_at_terminal_value {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r bcap r₂ r₃ : ℕ) {δU θ y : ℝ}
    (h16 : 16 ≤ 2 ^ r₂)
    (hN : D Nmat = TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hDense : DenseRung Nmat r (TerminalTwoStream.terminalTarget bcap r₂ r₃) δU θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ,
        TerminalTwoStream.terminalTarget bcap r₂ r₃ + r
          ≤ j + 1 + D (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2)) :
    CommonThreshold (wrapperW Nmat r)
      (TerminalTwoStream.terminalTarget bcap r₂ r₃ + r) θ δU y :=
  commonThreshold_of_firstWrapperClose Nmat r _
    (three_le_terminalTarget bcap r₂ r₃ h16) hN hθ0 hθ1 hδ0 hδ1 hy0 hy1 hRw hCl
    hDense hne hmem

end EthInapproximability.ParameterizedNP.FirstWrapperClose
