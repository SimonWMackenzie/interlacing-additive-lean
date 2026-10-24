import EthInapproximability.ParameterizedNP.DepthThread
import EthInapproximability.ParameterizedNP.CommonPadding

/-!
# Parameterized NP route: the final-only duplication of `thm:fixed-level-gap-size`

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`FINAL-ONLY-DUPLICATION-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened in
the same change as this module.  It is the first of the seven entries of item
(4) of the `BUDGET-THREAD-WIRING-001` gap list -- "`step:I-11`'s final
duplication (`12:307--317`)" -- and it is the only one of the seven that is
pure mathematics with no machine-layer dependency; the other six
(`A_realize`, `A_materialize`, the descriptor codec, the padding maps,
`eq:materializer-exact-runtime`, and the runtime tail) are untouched here and
remain open.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchor (proof source).**
  `sections/12-iteration-specification.tex`, `thm:fixed-level-gap-size`
  (label line 192), conclusion item (v), **lines 307--317**:

  > "If, only after all `k` calls, rows and columns are duplicated along
  > surjections `pi_X : Xhat -> [m_k]` and `pi_Z : Zhat -> [n_k]` that have
  > right inverses, then the matrix `Rhat_k(u,v) = R_k(pi_X(u), pi_Z(v))`
  > satisfies `comp(Rhat_k) = comp(R_k)`, so the two complexity conclusions in
  > `eq:k-level-gap` transfer unchanged.  This final-only duplication is not
  > part of any `T_i`, and no robustness claim for `Rhat_k` is made or used to
  > justify another level."

  Its proof paragraph is **lines 352--357** of the same file: "a protocol for
  `R_k` computes `Rhat_k` after the parties locally apply `pi_X` and `pi_Z`.
  Conversely, the right inverses identify a restriction of `Rhat_k` equal to
  `R_k`.  Restriction monotonicity gives the reverse inequality, proving
  equality of communication complexities.  The argument uses no density
  statement about the duplicated matrix."

* **Surrounding frozen anchors consumed, never restated.**
  * `eq:k-level-gap` (label line 305, display lines 301--306): the exact
    additive separation `YES: comp R_k <= Y_k`, `NO: comp R_k = D_k = Y_k + k`
    under the frozen seed identity `D_0 = Y_0` of line 299.  The two rows are
    the *two cases of one construction* and are carried here as **separate
    implications**; `dupPromiseCases_exclusive` records in the kernel that
    conjoining them at `k >= 1` would be vacuous.
  * `eq:fixed-level-closed-budgets` (label line 251) and the sentence of line
    253, "If `D_0 = Y_0`, then `D_j = Y_j + j`": consumed by pin as
    `BudgetThreadWiring.realizedBudgets_gap`.
  * `eq:fixed-level-carriers` (label line 264, display lines 260--265), the
    exact recurrence `m_{i+1} = (q_i m_{N,i})^{Q_i}`,
    `n_{i+1} = Q_i (n_{N,i})^{q_i}`: consumed by pin as
    `FixedLevelCarriers.fixedLevelCarriers`.  It is what makes `[m_k]`,
    `[n_k]` -- the *targets* of the two surjections -- banked quantities
    rather than binders.
  * `conv:finite-slots` (`sections/02-mechanical-contract.tex`), the zero-based
    reading of `[m_k] = {0, ..., m_k - 1}`, already transcribed in
    `FiniteSlots.lean`: the two projections land in `Fin m`, `Fin n`.
  * `sec:common-padding` (label line 565) and its duplication paragraph at
    lines 630--636, which is where the paper itself *applies* this clause, and
    `step:I-11` (`sections/13-iteration-assembly.tex`, label line 809), which
    is that application's mechanical form.

* **Banked endpoints consumed by pin** (all grep-verified present before use;
  nothing any of them states is restated here).
  * `CommonPadding.precomposition_no_increase` -- the route-named facade for the
    kernel-checked vendored `Workspace.ProofLemmas.SublemmaPrecompNoIncrease`.
    It is the formal content of "the parties locally apply `pi_X` and `pi_Z`"
    for arbitrary local maps, and it is consumed **through that facade**, not
    re-exported a second time.
  * `CommonPadding.PadEnum`, `.rep`, `.idx`, `.rep_idx`, `.frozenPadEnum`,
    `.frozenCommonPadding`, `.paddedMatrix`, `.two_le_sCommon` -- used only in
    Part 5, to exhibit the paper's own final padding as an instance of the
    abstract clause landed here.
  * `BudgetThreadWiring.realizedY`, `.realizedD`, `.realizedBudgets_gap` -- the
    budget thread.
  * `SizeThreadWiring.realizedZ`, `FixedLevelCarriers.LevelCarrierSpec` with
    its `rowCarrier` / `colCarrier` / `q` / `Q` / `mN` / `nN`,
    `FixedLevelCarriers.fixedLevelCarriers`, `OneLevelAssembly.sideExponent` --
    the size thread.
  * `DepthThread.realizedDepth`, `.realizedYk`,
    `.depthThread_shares_the_realized_chain`,
    `.realizedFields_promiseCases_exclusive`, `PaddingAndClock.slowIndex` --
    the depth thread and the clock index `k = L(n)`.

* **What is deliberately *not* consumed.**  No bracket, no `Lambda`, no
  `def:robust-seed` output, no promise certificate and no density statement
  occurs anywhere below -- frozen lines 316--317 forbid exactly that, and
  `duplicationDestroysRowDistinctness` shows the prohibition has content.
  `LegacyNPCC.Stage12` is **not** in this module's import closure, so the cited
  AGHP balanced-family axiom of `EXPANDER-001` stays outside it and no opt-in
  ledger note is owed.

* **Imports.**  `EthInapproximability.ParameterizedNP.DepthThread` and
  `EthInapproximability.ParameterizedNP.CommonPadding`, hence
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.

* **Proof status.**  Every declaration below is **new** and elementary.  No
  declaration is an inherited facade, and none re-proves a banked fact.

## What this module lands

1. **The duplication datum** (frozen lines 307--310).  `Duplication Xhat m` is
   the pair `(pi_X, its right inverse)` with the single frozen identity
   `pi_X . sigma_X = id_{[m]}`, and nothing else.  Surjectivity is the frozen
   word "surjections" and is a **derived** lemma (`proj_surjective`), not a
   field: making it a field would restate a derived telescope (`M4`).
2. **The duplicated matrix** (frozen lines 311--313), as `dupMatrix`, with the
   restriction identity of frozen line 353--354 as `dupMatrix_restrict`.
3. **Preservation of deterministic communication complexity** (frozen line 314;
   proof lines 352--356), as three theorems in the frozen order:
   `complexity_le_dup` (the restriction-monotonicity direction),
   `dup_le_complexity` (the local-application direction), and the headline
   `dupComplexity`, which is the frozen `comp(Rhat_k) = comp(R_k)` as an
   **equality**.
4. **The transfer of `eq:k-level-gap`** (frozen lines 314--315) through the
   banked budget thread, as `kLevelGapTransfers` and its clock-indexed form
   `kLevelGapTransfers_at_the_clock`; with `dupPromiseCases_exclusive` for why
   the two rows stay separate implications.
5. **Composition with the three landed threads** at one index of one realized
   chain, as `dupIndexCarriers_are_the_exact_recurrence` (size) and
   `finalDuplication_reads_all_three_threads` (size, budget and depth
   together, the last two by pin from
   `DepthThread.depthThread_shares_the_realized_chain`).
6. **Canonical inhabitation** (Part 5): the paper's own final padding --
   `step:I-11` at the frozen common square `S_n` of `eq:common-size` -- is an
   instance of this clause, via `Duplication.ofPadEnum`,
   `dupMatrix_ofPadEnum` and `frozenFinalDuplication`, with
   `frozenFinalDuplication_is_the_paper_padding` identifying the two matrices
   and `frozenFinalDuplication_nondegenerate` showing the instance genuinely
   duplicates at the frozen parameters.

## Guard scopes, kept distinct

The frozen clause carries two scope restrictions, and both are stated, neither
globalized:

* **"only after all `k` calls" / "is not part of any `T_i`"** (lines 307, 316).
  No declaration below produces a level, an arrow, a trace or a successor
  state; the two carriers `Xhat`, `Zhat` are free types that no thread reads.
  `dupCarrier_escapes_every_level_bound` makes the restriction *necessary*
  rather than decorative: for every level carrier `m >= 1` and every bound `B`
  there is a legal duplication whose carrier exceeds `B`, so the duplicated
  matrix is outside every level's size envelope and could not be fed to a
  further level even in principle.
* **"no robustness claim for `Rhat_k` is made or used"** (lines 316--317), and
  the proof's "uses no density statement about the duplicated matrix"
  (lines 356--357).  Nothing about robustness, density or the bracket appears
  below, and `duplicationDestroysRowDistinctness` exhibits a legal duplication
  that destroys pairwise row distinctness, so a transport of any
  density-sensitive certificate through this clause would be false.

These are distinct from `DepthThread.guardScopes_stay_distinct` (which
separates the depth thread's unconditional level-count scope from the branch
decision's `L(n) >= 1`) and from `CommonPadding`'s scope sentences at
`13:878--884` (which restrict the *machine-layer* padding); no scope statement
is transferred between the three.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: `Duplication` carries one map, one right inverse and the one
  frozen identity.  No matrix, no protocol, no complexity value, no budget, no
  robustness or promise certificate is a field.  `dupComplexity` is a theorem
  about the pinned construction, never a field.
* `M3`: every schedule quantity is taken through a banked definition and no
  numeral is assigned to one -- `Y_k` is `BudgetThreadWiring.realizedY`, `D_k`
  is `.realizedD`, `k` at the application site is `PaddingAndClock.slowIndex`
  (given no alias), `m_k`/`n_k` are `FixedLevelCarriers.rowCarrier` /
  `.colCarrier`, `b_i` is `DepthThread.realizedDepth`, and `S_n` in Part 5 is
  `PaddingAndClock.sCommon`.
* `M6`: zero-based finite slots (`conv:finite-slots`) throughout; the
  projections land in `Fin m`, never in a one-based segment.
* `M9`: both interlace widths stay distinct -- `S.q i` and `S.Q i` occur in
  exchanged roles in `dupIndexCarriers_are_the_exact_recurrence`, exactly as
  `eq:fixed-level-carriers` prints them.

## Reader counterparts

**No declaration in this module claims a reader item**, and the sweep behind
that statement was run first-hand this tranche over
`routes/parameterized-np/reader-facing/sections/`:

* The reader's own iteration theorem, `thm:paper-finite-iteration`
  (`05-iteration.tex`, label line 120, environment lines 119--144), prints the
  closed budgets (lines 129--133), the `YES`/`NO` rows (lines 137--140) and "In
  particular the final additive separation is exactly `k`" (line 143) -- and
  **stops there**.  It contains no duplication clause, no surjection, no right
  inverse and no `Rhat_k`.  Those four reader lines are already assigned to
  `IterationAssembly` under `ITER-001`, and lines 121--122 to
  `FixedLevelCarriers.LevelCarrierSpec` under `FIXED-LEVEL-CARRIERS-001`;
  nothing here is assigned twice.
* The reader's duplication content is in `06-eth.tex`, subsection "A common
  truth-table length", lines 322--341, and **every** item of it is already
  assigned to `CommonPadding` under `CLOCK-001` (lines 325--329, 330,
  332--333, 333--334, `eq:paper-padding-invariance` at label line 338) or to
  `TruthTableExponent`.  Re-citing any of them here would assign one reader
  item to two declarations.
* `01-introduction.tex:234--237` ("Only then do we duplicate rows and columns
  to a common binary side length.  This final padding preserves communication
  complexity ...") is the only other reader locus that states the final-only
  scope, and it is **introduction prose inside the overview, not a labelled
  statement**, so it is not claimed -- the same precedent `EFFECTIVE-MAIN-001`
  and `cc-t1x` record for proof-internal prose.  A repository-wide sweep of
  `src/EthInapproximability/ParameterizedNP/*.lean` for `01-introduction.tex`
  citations returns exactly one hit (`:100--101`, in
  `DenseRoutingInvariant.lean`), so that locus is unclaimed and stays so.

The final-only duplication clause is therefore **autoformalization-only
content**, in the same sense as `CommonPadding`'s enumerations and duplicate
count.

## GAP-EXPOSED

1. **The level-`k` matrix `R_k` itself is a binder.**  `thm:fixed-level-gap-size`
   quantifies `R_i` in its hypothesis block F2 (lines 201--204) and this
   module does the same: `R` is an arbitrary
   `Fin (S.rowCarrier k) -> Fin (S.colCarrier k) -> Bool`.  The identification
   `m_k = |Rows(R_k)|` of `eq:iterated-canonical-chaining` (label line 229)
   needs the level-`k` matrix object and `lem:canonical-reindexing-invariance`,
   neither of which is in Lean; both stay owed by `ITER-001`.
2. **The two promise-case hypotheses are named binders, not derived here.**
   `comp R_k <= Y_k` and `comp R_k = D_k` are the conclusions of items (iii)
   and (iv) of the frozen theorem (lines 267--298).  This module lands the
   *transfer*, not the two inductions; the inductions are `ITER-001`'s
   `fixedLevelGap_yes_induction` / `fixedLevelGap_no_induction` on the numeric
   complexity sequence, and wiring them to a typed level-`k` matrix is not
   done.
3. **Canonical inhabitation is landed for the paper's construction, not for
   the paper's fully instantiated carrier.**  Part 5 shows that the paper's own
   final padding (`step:I-11` at the frozen `S_n`) is a `Duplication` and that
   the two matrices agree, for **every** carrier `X` with an enumeration
   satisfying the frozen bounds.  The specific carrier -- the row set of the
   level-`L(n)` matrix -- does not exist in Lean, so the fully instantiated
   canonical inhabitation stays **REGISTERED AS DEFERRED** against `ITER-001`
   and `MATERIALIZE-001`, and is not silently satisfied by Part 5's evaluation
   at a one-element carrier, which is labelled where it occurs.
4. **The machine layer is absent, deliberately.**  The remaining six entries of
   item (4) of the `BUDGET-THREAD-WIRING-001` gap list are untouched: nothing
   below models `A_realize`, `A_materialize`, the descriptor codec, the padding
   maps, `eq:materializer-exact-runtime`, or any runtime.  The frozen clause is
   finite mathematics and is landed as such.
5. **No route completion is claimed.**  The construction layer and the machine
   layer are both unlanded; this row discharges one clause of one theorem.
-/

namespace EthInapproximability.ParameterizedNP.FinalOnlyDuplication

open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.SizeThreadWiring
open EthInapproximability.ParameterizedNP.BudgetThreadWiring
open EthInapproximability.ParameterizedNP.DepthThread

/-! ## Part 1: the duplication datum and the duplicated matrix -/

/-- **The final-only duplication datum of `12-iteration-specification.tex:307--310`.**

Frozen text: "rows and columns are duplicated along surjections
`pi_X : Xhat -> [m_k]` and `pi_Z : Zhat -> [n_k]` that have right inverses".

One side of that sentence, as a record: the projection `pi_X` and a right
inverse `sigma_X` with the single identity `pi_X . sigma_X = id`.  Under
`conv:finite-slots` the target is the zero-based slot type `Fin m`.

**Two fields and one proof field, and nothing else** (`M4`).  There is no
matrix, no protocol, no complexity value, no budget and no certificate here;
in particular the frozen word *surjections* is **not** a field, because
`proj_surjective` derives it from `proj_sect` -- adding it would restate a
derived telescope.  Conversely `proj_sect` is not derivable from surjectivity
without choice, and the frozen text names the right inverse explicitly, so the
right inverse is the datum and surjectivity is the theorem.

The carrier `Xhat` is an arbitrary type: the frozen clause imposes no bound on
it, and `dupCarrier_escapes_every_level_bound` shows that is not an oversight.

Claims no reader item (the reader prints no surjection and no right inverse). -/
structure Duplication (Xhat : Type u) (m : ℕ) where
  /-- `pi_X : Xhat -> [m]`, the duplication projection (frozen line 309). -/
  proj : Xhat → Fin m
  /-- The right inverse whose existence frozen line 310 requires. -/
  sect : Fin m → Xhat
  /-- `pi_X . sigma_X = id_{[m]}`, the frozen "have right inverses". -/
  proj_sect : ∀ x : Fin m, proj (sect x) = x

namespace Duplication

variable {Xhat : Type u} {Zhat : Type v} {m n : ℕ}

/-- **Aux 1 (the frozen word "surjections", derived).**

`12-iteration-specification.tex:308`.  Made a theorem rather than a field, so
that `Duplication` stays minimal (`M4`).

Statement pole: the trivial map `Xhat -> Fin m` is a constant map, and a
constant map fails surjectivity as soon as `m >= 2`; so this is not a property
every map has, and the field it replaces is genuinely recovered.  General in
the carrier, the slot count and the datum. -/
theorem proj_surjective (d : Duplication Xhat m) : Function.Surjective d.proj :=
  fun x => ⟨d.sect x, d.proj_sect x⟩

/-- **Aux 2 (the right inverse is injective).**

Immediate from the frozen identity, and the reason the restriction of the
duplicated matrix along `sigma_X` recovers the whole of `R_k` rather than a
quotient of it (frozen lines 353--354).  General. -/
theorem sect_injective (d : Duplication Xhat m) : Function.Injective d.sect :=
  Function.LeftInverse.injective d.proj_sect

/-- **The identity duplication.**

The degenerate member of the family: `Xhat = [m]` and both maps the identity.
It duplicates nothing, which is why it is *not* used as a non-vacuity witness
anywhere below; it exists so that `dupMatrix_id` can record the identity law of
the family.  General in the slot count. -/
def id' (m : ℕ) : Duplication (Fin m) m where
  proj := _root_.id
  sect := _root_.id
  proj_sect := fun _ => rfl

/-- **Composition of duplications.**

If `Xhat` duplicates `[m]` and `[m]` duplicates `[l]`, then `Xhat` duplicates
`[l]`.  This is an algebraic fact about the datum and is **not** a licence to
insert a duplication between two levels: frozen lines 307 and 316 restrict the
duplication to run once, after all `k` calls, and outside every `T_i`.  What it
records is that the clause is closed under the composition the frozen
"row--column enumeration followed by the final duplication maps" performs at
one place.  General. -/
def comp (d : Duplication Xhat m) (e : Duplication (Fin m) n) :
    Duplication Xhat n where
  proj := fun u => e.proj (d.proj u)
  sect := fun x => d.sect (e.sect x)
  proj_sect := fun x => by
    simp only [d.proj_sect, e.proj_sect]

end Duplication

variable {Xhat : Type u} {Zhat : Type v} {m n : ℕ} {Z : Type w}

/-- **The duplicated matrix `Rhat_k`** --
`12-iteration-specification.tex:311--313`,

```
Rhat_k(u,v) = R_k(pi_X(u), pi_Z(v)).
```

The index types are the frozen ones: `R_k` is indexed by the zero-based slots
`[m_k] x [n_k]` of `conv:finite-slots`, and `Rhat_k` by the two duplicated
carriers.  The output type is arbitrary; the frozen Boolean case is `Z = Bool`.

Claims no reader item. -/
def dupMatrix (dX : Duplication Xhat m) (dZ : Duplication Zhat n)
    (R : Fin m → Fin n → Z) : Xhat → Zhat → Z :=
  fun u v => R (dX.proj u) (dZ.proj v)

/-- **Aux 3 (the defining equation).**  Recorded so that consumers never unfold
`dupMatrix` by hand.  General in everything. -/
theorem dupMatrix_apply (dX : Duplication Xhat m) (dZ : Duplication Zhat n)
    (R : Fin m → Fin n → Z) (u : Xhat) (v : Zhat) :
    dupMatrix dX dZ R u v = R (dX.proj u) (dZ.proj v) := rfl

/-- **"the right inverses identify a restriction of `Rhat_k` equal to `R_k`"**
-- `12-iteration-specification.tex:353--354`.

The restriction is written as the composite along the two right inverses
rather than as a set-theoretic restriction; that is the same statement, and it
is the form the two complexity directions consume.  General in the carriers,
the two duplication data, the output type and the matrix. -/
theorem dupMatrix_restrict (dX : Duplication Xhat m) (dZ : Duplication Zhat n)
    (R : Fin m → Fin n → Z) (x : Fin m) (z : Fin n) :
    dupMatrix dX dZ R (dX.sect x) (dZ.sect z) = R x z := by
  simp only [dupMatrix, dX.proj_sect, dZ.proj_sect]

/-- **Aux 4 (identity law).**  Duplicating along the identity changes nothing.

This is the `k`-fold analogue of the frozen `k = 0` paragraph
(`12-iteration-specification.tex:320--323`): when nothing is duplicated, the
clause reduces to its hypothesis.  General in the slot counts, the output type
and the matrix. -/
theorem dupMatrix_id (R : Fin m → Fin n → Z) :
    dupMatrix (Duplication.id' m) (Duplication.id' n) R = R := rfl

/-- **Aux 5 (composition law / round trip).**  Duplicating along a composite is
duplicating twice, in the frozen order.  General in the carrier, the three slot
counts, the four data, the output type and the matrix. -/
theorem dupMatrix_comp {l : ℕ} (dX : Duplication Xhat m) (dZ : Duplication Zhat n)
    (eX : Duplication (Fin m) l) (eZ : Duplication (Fin n) l)
    (R : Fin l → Fin l → Z) :
    dupMatrix (dX.comp eX) (dZ.comp eZ) R
      = dupMatrix dX dZ (dupMatrix eX eZ R) := rfl

/-! ## Part 2: preservation of deterministic communication complexity -/

/-- **The restriction-monotonicity direction** --
`12-iteration-specification.tex:353--356`: "the right inverses identify a
restriction of `Rhat_k` equal to `R_k`.  Restriction monotonicity gives the
reverse inequality".

The restriction of a protocol is precomposition along the two right inverses,
followed by `dupMatrix_restrict`.  The precomposition principle is consumed by
pin through `CommonPadding.precomposition_no_increase`, the route facade for
the kernel-checked vendored `Workspace.ProofLemmas.SublemmaPrecompNoIncrease`;
it is not re-exported here.

General in the carriers, the two duplication data, the output type and the
matrix.  Claims no reader item. -/
theorem complexity_le_dup [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat m) (dZ : Duplication Zhat n) (R : Fin m → Fin n → Z) :
    D R ≤ D (dupMatrix dX dZ R) := by
  have h := CommonPadding.precomposition_no_increase (dupMatrix dX dZ R)
    dX.sect dZ.sect
  have hfun : (fun x y => dupMatrix dX dZ R (dX.sect x) (dZ.sect y)) = R := by
    funext x z
    exact dupMatrix_restrict dX dZ R x z
  rwa [hfun] at h

/-- **The local-application direction** --
`12-iteration-specification.tex:352--353`: "a protocol for `R_k` computes
`Rhat_k` after the parties locally apply `pi_X` and `pi_Z`".

Precomposition along the two projections; "locally" is the cost-preservation
half of the vendored principle.  General in the carriers, the two duplication
data, the output type and the matrix.  Claims no reader item. -/
theorem dup_le_complexity [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat m) (dZ : Duplication Zhat n) (R : Fin m → Fin n → Z) :
    D (dupMatrix dX dZ R) ≤ D R :=
  CommonPadding.precomposition_no_increase R dX.proj dZ.proj

/-- **The frozen `comp(Rhat_k) = comp(R_k)`** --
`12-iteration-specification.tex:314`, proved at lines 352--356.

An **equality**, as the frozen line writes it, obtained from the two frozen
directions in the frozen order; neither one-sided form is landed as the
headline.

Scope, honoured exactly (frozen lines 316--317, 356--357): the transport is of
deterministic communication complexity and of nothing else.  No density
statement about the duplicated matrix is made or used, and
`duplicationDestroysRowDistinctness` shows that boundary is real.

General in the carriers, the two duplication data, the output type and the
matrix.  Claims no reader item -- the reader's `eq:paper-padding-invariance`
(`06-eth.tex`, label line 338) is the *machine-layer* padding statement and is
already assigned to `CommonPadding.paddedComplexity`. -/
theorem dupComplexity [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat m) (dZ : Duplication Zhat n) (R : Fin m → Fin n → Z) :
    D (dupMatrix dX dZ R) = D R :=
  le_antisymm (dup_le_complexity dX dZ R) (complexity_le_dup dX dZ R)

/-! ## Part 3: the transfer of `eq:k-level-gap` through the banked budget thread -/

/-- **"the two complexity conclusions in `eq:k-level-gap` transfer unchanged"**
-- `12-iteration-specification.tex:314--315`, at the banked budget thread.

`eq:k-level-gap` (label line 305) prints

```
YES: comp R_k <= Y_k,      NO: comp R_k = D_k = Y_k + k
```

under the frozen seed identity `D_0 = Y_0` of line 299.  Here `Y_k` and `D_k`
are the banked `BudgetThreadWiring.realizedY` / `.realizedD` -- **no numeral is
assigned to either**, and the `NO` row's second equality is
`BudgetThreadWiring.realizedBudgets_gap` consumed by pin, with the seed
identity carried as the explicit binder `hbase` exactly as line 299 prints it.
The two carriers `[m_k]`, `[n_k]` are `FixedLevelCarriers.rowCarrier` /
`.colCarrier` at the same level.

**The two rows are separate implications, never a conjunction**: they are the
two cases of one construction, and `dupPromiseCases_exclusive` records in the
kernel that conjoining them at `k >= 1` derives `False`.  Neither hypothesis is
weakened to make the pair look consistent.

Statement pole: the trivial witness for the `NO` row would be an `Rhat_k` whose
complexity is *bounded* by `Y_k + k`; the frozen row is an **equality**, so a
duplication that lowered the complexity would fail it -- which is exactly what
`complexity_le_dup` rules out and what makes `dupComplexity`, not
`dup_le_complexity`, the input to this theorem.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state, the level, the two duplicated carriers, the two
duplication data and the matrix.  Claims no reader item. -/
theorem kLevelGapTransfers (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (hbase : S₀.budgetD = S₀.budgetY) (k : ℕ) [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier k))
    (dZ : Duplication Zhat (S.colCarrier k))
    (R : Fin (S.rowCarrier k) → Fin (S.colCarrier k) → Bool) :
    (D R ≤ realizedY S aE q2E sE auxW invT robD S₀ k →
        D (dupMatrix dX dZ R) ≤ realizedY S aE q2E sE auxW invT robD S₀ k) ∧
      (D R = realizedD S aE q2E sE auxW invT robD S₀ k →
        D (dupMatrix dX dZ R) = realizedD S aE q2E sE auxW invT robD S₀ k ∧
          D (dupMatrix dX dZ R) =
            realizedY S aE q2E sE auxW invT robD S₀ k + k) := by
  have htrans := dupComplexity dX dZ R
  have hgap := realizedBudgets_gap S aE q2E sE auxW invT robD S₀ hbase k
  refine ⟨fun hyes => ?_, fun hno => ⟨?_, ?_⟩⟩
  · rw [htrans]; exact hyes
  · rw [htrans, hno]
  · rw [htrans, hno, hgap]

/-- **The same transfer at the paper's own level count `k = L(n)`.**

`12-iteration-specification.tex:360` fixes the intended fixed-level application
and `14-final-consequence.tex:1617` fixes `k = L(n)`; the clock index is the
banked `PaddingAndClock.slowIndex`, consumed by pin and given no alias, and the
budget field is the banked `DepthThread.realizedYk`, which is `realizedY`
evaluated at it.  So neither quantity is re-derived here: this is
`kLevelGapTransfers` read at the index the frozen controller parses.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state, the clock, the source size, the two duplicated
carriers, the two duplication data and the matrix.  Claims no reader item. -/
theorem kLevelGapTransfers_at_the_clock (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (hbase : S₀.budgetD = S₀.budgetY) (V : ℕ → ℕ) (n : ℕ)
    [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier (slowIndex V n)))
    (dZ : Duplication Zhat (S.colCarrier (slowIndex V n)))
    (R : Fin (S.rowCarrier (slowIndex V n)) →
      Fin (S.colCarrier (slowIndex V n)) → Bool) :
    (D R ≤ realizedYk S aE q2E sE auxW invT robD S₀ V n →
        D (dupMatrix dX dZ R) ≤ realizedYk S aE q2E sE auxW invT robD S₀ V n) ∧
      (D R = realizedD S aE q2E sE auxW invT robD S₀ (slowIndex V n) →
        D (dupMatrix dX dZ R) =
            realizedD S aE q2E sE auxW invT robD S₀ (slowIndex V n) ∧
          D (dupMatrix dX dZ R) =
            realizedYk S aE q2E sE auxW invT robD S₀ V n + slowIndex V n) :=
  kLevelGapTransfers S aE q2E sE auxW invT robD S₀ hbase (slowIndex V n) dX dZ R

/-- **The two transferred promise rows are exclusive at the frozen guard.**

`eq:k-level-gap` prints its two rows as the two cases of one construction.  At
the frozen `k = L(n) >= 1` of `14-final-consequence.tex:2633` they cannot both
hold of the **duplicated** matrix either, so a formalization that conjoined the
two transferred conclusions would be vacuous -- which is why
`kLevelGapTransfers` keeps them as separate implications.

The transport is used non-trivially: the hypothesis is about `R_k` and the
conclusion about `Rhat_k`, and `dupComplexity` is what closes the gap between
them.  The arithmetic is not re-proved: this is
`DepthThread.realizedFields_promiseCases_exclusive` consumed by pin at the
realized budget field.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state, the clock, the source size, the carriers, the data
and the matrix.  Claims no reader item. -/
theorem dupPromiseCases_exclusive (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (V : ℕ → ℕ) (n : ℕ) (hk : 1 ≤ slowIndex V n)
    [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier (slowIndex V n)))
    (dZ : Duplication Zhat (S.colCarrier (slowIndex V n)))
    (R : Fin (S.rowCarrier (slowIndex V n)) →
      Fin (S.colCarrier (slowIndex V n)) → Bool)
    (hyes : D R ≤ realizedYk S aE q2E sE auxW invT robD S₀ V n)
    (hno : D (dupMatrix dX dZ R) =
      realizedYk S aE q2E sE auxW invT robD S₀ V n + slowIndex V n) : False := by
  rw [dupComplexity dX dZ R] at hno
  exact realizedFields_promiseCases_exclusive S aE q2E sE auxW invT robD S₀ V n hk
    (c := (D R : ℤ)) (by exact_mod_cast hyes) (by exact_mod_cast hno)

/-! ## Part 4: composition with the three landed threads -/

/-- **The duplication's targets are the banked exact carriers.**

`eq:fixed-level-carriers` (`12-iteration-specification.tex`, label line 264)
gives the *exact*, rather than asymptotic, recurrence
`m_{i+1} = (q_i m_{N,i})^{Q_i}`, `n_{i+1} = Q_i (n_{N,i})^{q_i}`, and the
statement below reads it off the **index types** of the matrix the final
duplication consumes: the two slot types of `R_k` have exactly those
cardinalities.  So the
`[m_k]`, `[n_k]` of frozen line 309--310 are the size thread's own carriers and
not free parameters.

The recurrence is `FixedLevelCarriers.fixedLevelCarriers` consumed by pin and
is not re-derived.  The two interlace widths stay in their exchanged roles
(`M9`): `Q_i` exponentiates on the row side and multiplies on the column side.

General in the specification and the level.  Claims no reader item;
`eq:paper-exact-carrier-recurrence` (reader `05-iteration.tex`, label line 166)
is already assigned to `SIZE-001`. -/
theorem dupIndexCarriers_are_the_exact_recurrence
    (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) :
    Fintype.card (Fin (S.rowCarrier (i + 1))) = (S.q i * S.mN i) ^ S.Q i ∧
      Fintype.card (Fin (S.colCarrier (i + 1))) = S.Q i * S.nN i ^ S.q i := by
  obtain ⟨hrow, hcol⟩ := FixedLevelCarriers.fixedLevelCarriers S i
  exact ⟨by simpa using hrow, by simpa using hcol⟩

/-- **The final-only duplication sits beside all three landed threads at one
index of one realized chain.**

`14-final-consequence.tex:1644--1649` updates the two budgets and holds the
depth fixed, and `eq:fixed-level-carriers` updates the two carriers, all along
the **same** realized arrow.  The final duplication of frozen lines 307--317 is
applied at the last index of that chain and adds no arrow to it, so the honest
composite statement is this one: the clause's own conclusion, the two
transferred promise rows, and the size and depth readouts of the same chain at
the same index, none of which the duplication perturbs.

The last two conjuncts are
`DepthThread.depthThread_shares_the_realized_chain` consumed by pin -- no size
fact and no depth fact is re-derived here -- and the first three are Parts 2
and 3.  What the theorem records is that the duplication statement is available
at the index the three threads are read at, without a compatibility hypothesis.

It records nothing about robustness: the depth conjunct is the chain's own
`b_i` slot, and no bracket or certificate for `Rhat_k` is claimed (frozen lines
316--317).

General in the specification, the three exponent families, the three `AuxOut`
families, the base state, the level, the two duplicated carriers, the two
duplication data and the matrix.  Claims no reader item. -/
theorem finalDuplication_reads_all_three_threads
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (hbase : S₀.budgetD = S₀.budgetY) (k : ℕ) [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier k))
    (dZ : Duplication Zhat (S.colCarrier k))
    (R : Fin (S.rowCarrier k) → Fin (S.colCarrier k) → Bool) :
    D (dupMatrix dX dZ R) = D R ∧
      (D R ≤ realizedY S aE q2E sE auxW invT robD S₀ k →
        D (dupMatrix dX dZ R) ≤ realizedY S aE q2E sE auxW invT robD S₀ k) ∧
      (D R = realizedD S aE q2E sE auxW invT robD S₀ k →
        D (dupMatrix dX dZ R) = realizedD S aE q2E sE auxW invT robD S₀ k ∧
          D (dupMatrix dX dZ R) =
            realizedY S aE q2E sE auxW invT robD S₀ k + k) ∧
      realizedZ S aE q2E sE auxW invT robD S₀ (k + 1) =
        sideExponent (S.rowCarrier (k + 1)) (S.colCarrier (k + 1)) ∧
      realizedDepth S aE q2E sE auxW invT robD S₀ k = S₀.depth := by
  obtain ⟨hyes, hno⟩ :=
    kLevelGapTransfers S aE q2E sE auxW invT robD S₀ hbase k dX dZ R
  obtain ⟨hZ, -, -, hdepth⟩ :=
    depthThread_shares_the_realized_chain S aE q2E sE auxW invT robD S₀ k
  exact ⟨dupComplexity dX dZ R, hyes, hno, hZ, hdepth⟩

/-! ## Part 5: canonical inhabitation, non-vacuity, and the two scope poles -/

/-- **The paper's own final padding, viewed as a duplication datum.**

`step:I-11` (`13-iteration-assembly.tex:835--856`) builds the representative
map `pi_X : [S_n] -> X` from an enumeration together with the inverse index
`iota_X`, and proves the round trip `pi_X . iota_X = id`.  Transported along
that enumeration, this is exactly the frozen datum of
`12-iteration-specification.tex:307--310`: the duplicated carrier is the slot
type `[S_n]`, the target is `[|X|]`, and the round trip is the required right
inverse.

So the abstract clause landed in Parts 1--3 is not a new object -- it is the
shape the paper's own padding already has, and this definition is the bridge.
Consumes `CommonPadding.PadEnum.rep`, `.idx` and `.rep_idx` by pin; nothing of
`step:I-11` is restated.

General in the carrier, the common square side and the padding datum.  Claims
no reader item. -/
def Duplication.ofPadEnum {X : Type u} [Fintype X] {S : ℕ}
    (p : CommonPadding.PadEnum X S) : Duplication (Fin S) (Fintype.card X) where
  proj := fun u => p.enum.symm (p.rep u)
  sect := fun a => p.idx (p.enum a)
  proj_sect := fun a => by
    rw [p.rep_idx (p.enum a), Equiv.symm_apply_apply]

/-- **The two matrices agree.**

`CommonPadding.paddedMatrix` (the machine-layer padded square of
`13-iteration-assembly.tex:860--864`) is literally the `dupMatrix` of the two
duplication data extracted by `Duplication.ofPadEnum`, applied to the matrix
`R` read in the two canonical enumerations.

This is the fidelity test the canonical-inhabitation rule asks for at the level
of the *construction*: the paper's own object inhabits the encoding, rather
than some object inhabiting it.  General in the two carriers, the common square
side, the padding datum, the output type and the matrix.  Claims no reader
item. -/
theorem dupMatrix_ofPadEnum {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    {S : ℕ} (C : CommonPadding.CommonPadding X Y S) (R : X → Y → Z) :
    dupMatrix (Duplication.ofPadEnum C.rows) (Duplication.ofPadEnum C.cols)
        (fun a b => R (C.rows.enum a) (C.cols.enum b))
      = CommonPadding.paddedMatrix C R := by
  funext u v
  simp only [dupMatrix, Duplication.ofPadEnum, CommonPadding.paddedMatrix,
    Equiv.apply_symm_apply]

/-- **The paper's final duplication at the frozen common square `S_n`.**

`CommonPadding.frozenPadEnum` is `step:I-11` instantiated at
`S = S_n = sCommon V n` of `eq:common-size`
(`12-iteration-specification.tex`, label line 628), which is the paper's own
value; no numeral is chosen here and none is chosen there.  This is the datum
the frozen clause of lines 307--317 is applied to at the application site.

General in the clock, the source size, the carrier, the enumeration and the
frozen size bound.  Claims no reader item. -/
noncomputable def frozenFinalDuplication {X : Type u} [Fintype X] (V : ℕ → ℕ) (n : ℕ)
    (e : Fin (Fintype.card X) ≃ X) (hpos : 0 < Fintype.card X)
    (hX : Fintype.card X ≤ 2 ^ gMaj V n) :
    Duplication (Fin (sCommon V n)) (Fintype.card X) :=
  Duplication.ofPadEnum (CommonPadding.frozenPadEnum V n e hpos hX)

/-- **Canonical inhabitation: the paper's own final padding satisfies this
module's clause, and its complexity transport is this module's headline.**

Both conjuncts are at the paper's own parameters -- the frozen common square
`S_n` of `eq:common-size`, the frozen carrier bounds `|X| <= 2^{g(n)}` of
`13-iteration-assembly.tex:815--818`, and the frozen enumerations -- and hold
for **every** clock, source size, carrier, enumeration, output type and matrix.

The first conjunct identifies the object: the machine-layer padded square is
the `dupMatrix` of two `frozenFinalDuplication` data.  The second delivers the
frozen `comp(Rhat_k) = comp(R_k)` of line 314 for it, through `dupComplexity`
rather than through `CommonPadding.paddedComplexity`, so the abstract clause is
what does the work.

**What this is not** (GAP-EXPOSED 3): the specific carrier of the level-`L(n)`
matrix does not exist in Lean, so the *fully instantiated* canonical
inhabitation stays REGISTERED AS DEFERRED against `ITER-001` and
`MATERIALIZE-001`.  What is discharged is the paper's construction at the
paper's own square exponent, general in the carrier.

Claims no reader item. -/
theorem frozenFinalDuplication_is_the_paper_padding {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (V : ℕ → ℕ) (n : ℕ)
    (eX : Fin (Fintype.card X) ≃ X) (eY : Fin (Fintype.card Y) ≃ Y)
    (hXpos : 0 < Fintype.card X) (hYpos : 0 < Fintype.card Y)
    (hX : Fintype.card X ≤ 2 ^ gMaj V n) (hY : Fintype.card Y ≤ 2 ^ gMaj V n)
    (R : X → Y → Z) :
    dupMatrix (frozenFinalDuplication V n eX hXpos hX)
        (frozenFinalDuplication V n eY hYpos hY) (fun a b => R (eX a) (eY b))
      = CommonPadding.paddedMatrix
          (CommonPadding.frozenCommonPadding V n eX eY hXpos hYpos hX hY) R ∧
      D (dupMatrix (frozenFinalDuplication V n eX hXpos hX)
          (frozenFinalDuplication V n eY hYpos hY) (fun a b => R (eX a) (eY b)))
        = D (fun a b => R (eX a) (eY b)) := by
  refine ⟨?_, dupComplexity _ _ _⟩
  exact dupMatrix_ofPadEnum
    (CommonPadding.frozenCommonPadding V n eX eY hXpos hYpos hX hY) R

/-- **The paper's instance genuinely duplicates, at the frozen parameters**
(LANE-GATE 3).

A one-element carrier satisfies the frozen bound `|X| <= 2^{g(n)}` for every
clock and every `n`, and `CommonPadding.two_le_sCommon` gives `S_n >= 2`, so the
projection of `frozenFinalDuplication` is **not** injective: at least two slots
of `[S_n]` are identified.  The duplication is therefore real at the frozen
square exponent, for every clock and every source size, and the premise bundle
of Parts 2--3 is consistent there.

Statement pole: the trivial inhabitant of `Duplication` is the identity
(`Duplication.id'`), which duplicates nothing; it fails this statement, which
is exactly why the non-injectivity conjunct is present.

**Evaluation point, labelled:** the carrier `Fin 1` is a legal frozen carrier
but is *not* the level-`L(n)` carrier, which is unbuilt; this evaluation is the
same one `CommonPadding.frozenCommonPadding_inhabited_nondegenerate` uses and
carries the same weight -- it establishes non-degeneracy at legal values, not
fidelity at the application point.  Fidelity at the construction is
`frozenFinalDuplication_is_the_paper_padding`; fidelity at the fully
instantiated carrier stays deferred (GAP-EXPOSED 3).

General in the clock and the source size.  Claims no reader item. -/
theorem frozenFinalDuplication_nondegenerate (V : ℕ → ℕ) (n : ℕ) :
    ¬ Function.Injective
        (frozenFinalDuplication (X := Fin 1) V n (finCongr (by simp))
          (by simp) (by simpa using Nat.one_le_two_pow)).proj := by
  intro hinj
  have hcard := Fintype.card_le_of_injective _ hinj
  have h2 := CommonPadding.two_le_sCommon V n
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Scope pole 1: the duplicated carrier escapes every level bound.**

Frozen lines 307 and 316 restrict the duplication to run *only after all `k`
calls* and to be *no part of any `T_i`*.  That restriction is not decorative.
The frozen clause imposes **no** bound on `Xhat`, and here is the consequence:
for every level carrier `m >= 1` and every bound `B` there is a legal
duplication datum whose carrier has more than `B` elements.  So the duplicated
matrix has no place in the size thread's envelope
(`13-iteration-assembly.tex:295--296`, `LevelState.UnderEnvelope`), and a
formalization that fed `Rhat_k` back into a level would be feeding it an object
the schedule never bounds.

Statement pole: the trivial witness is the identity duplication, whose carrier
has exactly `m` elements; it fails the bound as soon as `B >= m`.  The witness
here is the paper's own shape -- a projection with a fallback, exactly as
`step:I-11`'s `pi_X` has -- and it claims **no** legality for its own carrier
size, which is the point: the clause permits any.

General in the level carrier and the bound.  Claims no reader item. -/
theorem dupCarrier_escapes_every_level_bound (m : ℕ) (hm : 0 < m) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ Nonempty (Duplication (Fin N) m) := by
  refine ⟨m + B + 1, by omega, ⟨?_⟩⟩
  refine
    { proj := fun u => ⟨(u : ℕ) % m, Nat.mod_lt _ hm⟩
      sect := fun x => ⟨(x : ℕ), by have := x.isLt; omega⟩
      proj_sect := ?_ }
  intro x
  apply Fin.ext
  simpa using Nat.mod_eq_of_lt x.isLt

/-- **A nondegenerate duplication datum at legal values**, for the
row-distinctness probe below: two level slots `[2]`, a three-element duplicated
carrier, so exactly one slot of the carrier is a duplicate and the projection is
genuinely non-injective.  The frozen clause bounds neither number, so both are
legal; the datum claims **no** further legality and is not an instance of the
paper's construction (that is `frozenFinalDuplication`).  It has the frozen
shape all the same -- a projection with a fallback branch, together with its
right inverse.  Claims no reader item. -/
def probeRowDuplication : Duplication (Fin 3) 2 where
  proj := fun u => if (u : ℕ) = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  sect := fun x => ⟨(x : ℕ), by have := x.isLt; omega⟩
  proj_sect := by decide

/-- **A genuinely non-constant Boolean matrix on the pinned level carriers**,
used to exercise the row-distinctness probe on something a constant matrix
would not distinguish.  Claims no reader item. -/
def probeMatrix : Fin 2 → Fin 1 → Bool := fun x _ => decide ((x : ℕ) = 0)

/-- **Scope pole 2: duplication does not preserve density-sensitive
properties.**

Frozen lines 316--317 say that "no robustness claim for `Rhat_k` is made or
used to justify another level", and the proof paragraph closes with "The
argument uses no density statement about the duplicated matrix"
(lines 356--357).  That restriction is refutation-backed: the pinned matrix has
pairwise distinct rows and its duplication does not, because two slots of the
duplicated carrier are identified.  Any encoding that let a density-sensitive
certificate ride through this clause would be refuted by this pair, so the
frozen refusal is necessary and not merely cautious.

This is a **rejection probe**: it claims no legality for its own parameters and
is not an instance of the paper's construction.  Claims no reader item. -/
theorem duplicationDestroysRowDistinctness :
    Function.Injective probeMatrix ∧
      ¬ Function.Injective
        (dupMatrix probeRowDuplication (Duplication.id' 1) probeMatrix) := by
  decide

/-! ## Part 6: hypothesis consistency of the transfer theorem

`kLevelGapTransfers` keeps the two rows of `eq:k-level-gap` as separate
implications because `dupPromiseCases_exclusive` shows that conjoining them at
`k >= 1` derives `False`.  A gate that stops there would leave the opposite
danger untested: an implication whose antecedent is never satisfiable is
vacuously true, and a bundle that is inconsistent *everywhere* would make the
whole theorem empty.  Part 6 answers that question in the kernel. -/

/-- **The full hypothesis bundle of `kLevelGapTransfers` is consistent, and both
promise antecedents hold simultaneously at the paper's own zero-level point.**

Frozen `12-iteration-specification.tex:320--323`: "For `k = 0`, the family
indexed by `0 <= i < k` is empty ... All conclusions reduce to their stated
hypotheses at `R_0`, the sums are empty, and **the additive gap is zero**."  At
zero levels the two rows of `eq:k-level-gap` are `comp R_0 <= Y_0` and
`comp R_0 = D_0 = Y_0 + 0`, which are compatible -- and the theorem's guarded
form is exactly what makes that possible while `dupPromiseCases_exclusive`
still fires at `k = L(n) >= 1`.  So the two gates agree, and neither statement
is vacuous.

**No value is invented.**  The base state is the paper's own
`SuccessorMajorant.seedState n scales` with exactly the two slots the frozen
`NO` hypothesis `comp R_0 = D_0` (line 287) determines overwritten by
`comp R_0`; every other slot -- the two logarithmic side lengths, the depth
`B(n)` of `IterationAssembly.depthB`, and the public scales -- is the banked
seed value, unchanged.  `D_0 = Y_0` (frozen line 299) then holds by
construction, and the two budget readouts are `realizedBudgets_zero` consumed
by pin.

**What is deliberately not claimed** (GAP-EXPOSED 1--3): the frozen application
site of `12:370` instantiates `D_0 = Y_0 = comp F_{B(n)} = a_seed + 1`, and that
identity is **not** discharged here, because the complexity display of
`lem:full-cube-seed` is banked only at requested depth `b = 0`, not at the
scheduled depth `B(n)` -- the same boundary `FixedLevelCarriers`'
`seedAnchored_carriers` records, and the reason that theorem carries the two
carriers and the depth but not the budget.  This consistency instance therefore
runs at the frozen theorem's own generality, where `F2` (lines 201--204)
quantifies `D_i`, `Y_i` freely; it is **not** a claim that the paper's seed
budget equals `comp R_0` in Lean.

General in the specification, the three exponent families, the three `AuxOut`
families, the source size, the public scale list, the two duplicated carriers,
the two duplication data and the matrix.  Claims no reader item. -/
theorem kLevelGapTransfers_hypotheses_consistent
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (n : ℕ) (scales : List ℕ)
    [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier 0))
    (dZ : Duplication Zhat (S.colCarrier 0))
    (R : Fin (S.rowCarrier 0) → Fin (S.colCarrier 0) → Bool) :
    ∃ S₀ : LevelState,
      S₀ = { seedState n scales with budgetD := D R, budgetY := D R } ∧
        S₀.depth = IterationAssembly.depthB n ∧
        S₀.budgetD = S₀.budgetY ∧
        D R ≤ realizedY S aE q2E sE auxW invT robD S₀ 0 ∧
        D R = realizedD S aE q2E sE auxW invT robD S₀ 0 ∧
        D (dupMatrix dX dZ R) ≤ realizedY S aE q2E sE auxW invT robD S₀ 0 ∧
        D (dupMatrix dX dZ R) = realizedD S aE q2E sE auxW invT robD S₀ 0 ∧
        D (dupMatrix dX dZ R) =
          realizedY S aE q2E sE auxW invT robD S₀ 0 + 0 := by
  refine ⟨{ seedState n scales with budgetD := D R, budgetY := D R },
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hY, -⟩ := realizedBudgets_zero S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R }
    rw [hY]
  · obtain ⟨-, hD⟩ := realizedBudgets_zero S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R }
    rw [hD]
  · obtain ⟨hyes, -⟩ := kLevelGapTransfers S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R } rfl 0 dX dZ R
    refine hyes ?_
    obtain ⟨hY, -⟩ := realizedBudgets_zero S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R }
    rw [hY]
  · obtain ⟨-, hno⟩ := kLevelGapTransfers S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R } rfl 0 dX dZ R
    obtain ⟨-, hD⟩ := realizedBudgets_zero S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R }
    exact (hno (by rw [hD])).1
  · obtain ⟨-, hno⟩ := kLevelGapTransfers S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R } rfl 0 dX dZ R
    obtain ⟨-, hD⟩ := realizedBudgets_zero S aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D R, budgetY := D R }
    exact (hno (by rw [hD])).2

end EthInapproximability.ParameterizedNP.FinalOnlyDuplication
