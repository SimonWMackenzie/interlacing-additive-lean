import EthInapproximability.ParameterizedNP.FinalOnlyDuplication

/-!
# Parameterized NP route: canonical reindexing and the iterated canonical chaining

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ITERATED-CANONICAL-CHAINING-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened in
the same change as this module against the two named-pending items of
**`ITER-001`**: `lem:canonical-reindexing-invariance` (which `ITER-001` records
as "absorbed into the named transfer hypotheses of the composed steps") and the
level-`k` matrix object of `eq:iterated-canonical-chaining`.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchors (proof source).**
  `sections/12-iteration-specification.tex`:
  * `sec:canonical-reindexing` **lines 93--104**, the unique increasing
    equivalence `e_X : [|X|] -> X`: "This equivalence is determined by the
    carrier itself; it is not an additional choice and cannot depend on a YES or
    NO certificate."
  * `def:canonical-reindexing` (label line 107), **lines 106--137**, with
    `eq:canonical-reindexing` (label line 116)
    `Can(M)(u,v) = M(e_X(u), e_Y(v))`, the two-index form `Can_{m,n}(M)`
    (lines 119--126) and the frozen reading of the typed assertion at lines
    127--136: it "abbreviates the pointwise equation ... together with the two
    cardinality equalities that define the displayed increasing equivalences.
    It never denotes a heterogeneous equality of functions."
  * `lem:canonical-reindexing-invariance` (label line 140), **lines 139--166**,
    whose first display `eq:canonical-complexity-invariance` (label line 144) is
    `comp(Can(M)) = comp(M)`; proof lines 168--180, "A protocol is transported in
    either direction by applying the row and column equivalences locally, so
    ... follows with no communication overhead."
  * `eq:iterated-canonical-chaining` (label line 229, display lines
    **222--230**), clause F3 of `thm:fixed-level-gap-size`:
    `m_{i+1} = |Rows(R_i^+)|`, `n_{i+1} = |Cols(R_i^+)|`,
    `R_{i+1} = Can_{m_{i+1},n_{i+1}}(R_i^+)`, quantified for `0 <= i < k`.
  * The frozen application site **lines 360--368**: "take
    `R_0 = Can(F_{B(n)})`, `m_0 = |Rows(F_{B(n)})|`, `n_0 = |Cols(F_{B(n)})|`",
    and line 379's use of
    `lem:full-cube-seed, lem:canonical-reindexing-invariance` to move the two
    seed statements onto `R_0`.

* **Surrounding frozen anchors consumed, never restated.**
  * `eq:fixed-level-carriers` (label line 264): consumed by pin as
    `FixedLevelCarriers.fixedLevelCarriers` and
    `.fixedLevelCarriers_realized`.  It is what makes the two *targets* of the
    chaining, `[m_{i+1}]` and `[n_{i+1}]`, banked schedule quantities.
  * `thm:fixed-level-gap-size` (iii)/(iv), lines 267--297: consumed by pin as
    `IterationAssembly.fixedLevelGap_yes_induction` /
    `.fixedLevelGap_no_induction` on the numeric complexity sequence.  Neither
    induction is re-proved here; what is new is that the sequence is now the
    sequence of complexities of a **typed** chain rather than a free binder.
  * `eq:iterated-budgets` (label line 239) and
    `eq:fixed-level-closed-budgets` (label line 251): consumed by pin through
    `BudgetThreadWiring.realizedY`, `.realizedD`,
    `.realizedBudgets_are_the_banked_ladders`, `.realizedBudgets_gap`.
  * `12:307--317`, the final-only duplication: consumed by pin through
    `FinalOnlyDuplication.dupMatrix`, `.dupComplexity`, `.kLevelGapTransfers`
    and `.dupPromiseCases_exclusive`.  Nothing that module states is restated.
  * `conv:finite-slots` (`sections/02-mechanical-contract.tex`): zero-based
    slots throughout; `[m]` is `Fin m`.
  * `12:16--21` and `eq:full-cube-seed` (label line 29): the seed and its two
    carriers, consumed by pin through `FixedLevelCarriers.qSeed`,
    `.seedMatrix`, `.seedMatrix_carriers`, `.aSeed_spec`.

* **What is deliberately *not* consumed.**  No bracket, no `Lambda`, no promise
  certificate and no density statement occurs in any definition below; the
  bracket half of `lem:canonical-reindexing-invariance`
  (`eq:canonical-bracket-invariance`, label line 163) is **GAP-EXPOSED 1** and is
  not asserted anywhere.  `LegacyNPCC.Stage12` is **not** in this module's
  import closure, so the cited AGHP balanced-family axiom of `EXPANDER-001`
  stays outside it and no opt-in ledger note is owed.

* **Imports.**  `EthInapproximability.ParameterizedNP.FinalOnlyDuplication`
  only, hence `DepthThread`, `CommonPadding`, `BudgetThreadWiring`,
  `SizeThreadWiring`, `FixedLevelCarriers`, `IterationAssembly`,
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.

* **Proof status.**  Every declaration below is **new**.  None is an inherited
  facade and none re-proves a banked fact.

## What this module lands

1. **The unique increasing equivalence** (frozen lines 93--104), as
   `canonOrderEquiv` / `canonEquiv` over Mathlib's `monoEquivOfFin`, together
   with `canonOrderEquiv_unique`, which is the kernel form of "it is not an
   additional choice".
2. **`def:canonical-reindexing`** (frozen lines 106--137): the general transport
   `reindex` along a pair of equivalences, the canonical instance `Can`
   (`eq:canonical-reindexing`), and `IsCanonicalReindex`, which is the frozen
   *typed assertion* of lines 127--136 -- the pointwise equation together with
   the two cardinality equalities, never a heterogeneous equality of functions.
3. **`lem:canonical-reindexing-invariance`, complexity half** (frozen line 144),
   as `reindex_complexity`, `canonicalReindexing_invariance` and
   `isCanonicalReindex_complexity`, plus `Can_complexity_indep_of_order`, which
   shows the consumed content does not depend on which linear order the carrier
   is given (see GAP-EXPOSED 2).
4. **`eq:iterated-canonical-chaining`** (frozen lines 222--230) as
   `CanonicalChain`, a level-indexed record over a banked
   `FixedLevelCarriers.LevelCarrierSpec` whose three fields `rowCard`,
   `colCard`, `chain` are the display's three equations verbatim, and
   `chainingStep_from_oneLevel`, which composes the chaining with the banked
   one-level carrier equations by pin.
5. **The two inductions carried on a typed chain** (frozen lines 267--297),
   `chainYesFold` and `chainNoFold`, each quantifying its per-level clause over
   `i < j` exactly as frozen F3 does, and each obtained by feeding the chain's
   own complexity sequence to the banked `ITER-001` induction.
6. **The three wirings of `FinalOnlyDuplication`** whose absence that module
   records as its GAP-EXPOSED 1 and 2: `chainedFinalCarriers`,
   `chainedKLevelGapTransfers` and `chainedFinalDuplication_at_the_clock`.  In
   all three the level-`k` matrix is `C.lev k` -- a member of the chain with the
   banked carriers -- and not a free binder, and the two promise rows are
   *derived* from the frozen seed conditions and the frozen per-level updates
   rather than assumed.
7. **Canonical inhabitation** (Part 7): the paper's own `R_0 = Can(F_{B(n)})`
   of frozen line 363, at the paper's own carrier `{0,1}^{q_seed}` with the
   paper's own lexicographic order, as `paperSeedReindexed` with
   `paperSeedReindexed_isCanonical`, `paperSeedReindexed_at_seedAnchored` and
   `paperSeedReindexed_nondegenerate`.

## Guard scopes, kept distinct

* **`0 <= i < k`.**  Frozen F3 (line 205) quantifies the public records, traces
  and chaining equations over `0 <= i < k`, and frozen lines 320--323 state that
  at `k = 0` the family is empty.  `chainYesFold` and `chainNoFold` therefore
  take their per-level clauses as `∀ i, i < j -> ...`; a global `∀ i` would be an
  over-strong hypothesis that the frozen theorem never imposes, and
  `chainedFold_hypotheses_consistent` shows the bounded form is exactly what
  makes the `k = 0` reading non-vacuous.
* **The chaining is a *typed* equation, not a heterogeneous one** (frozen lines
  135--136).  `CanonicalChain.chain` is an equality of functions on
  `Fin m_{i+1} x Fin n_{i+1}`; nowhere is a matrix on a level carrier equated
  with a matrix on a slot type.
* **No robustness, density or bracket content.**  `lem:canonical-reindexing-`
  `invariance`'s bracket half is not asserted (GAP-EXPOSED 1), and no
  declaration below mentions a certificate.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: `CanonicalChain` carries the level matrices, the per-level output
  carriers with their orders, the output matrices and the three frozen
  equations, and **nothing else**.  No complexity value, no budget, no depth, no
  robustness or promise certificate is a field; `chain_complexity` is a theorem
  about the pinned construction.  `OutputCarriers` carries types and their two
  instances only.
* `M3`: every schedule quantity runs through a banked definition -- `m_i`, `n_i`
  are `FixedLevelCarriers.LevelCarrierSpec.rowCarrier` / `.colCarrier`, `H_i` is
  `EffectiveMaterialization.realizedOverhead`, `Y_i`/`D_i` are
  `BudgetThreadWiring.realizedY` / `.realizedD`, `Y_{L(n)}` is
  `DepthThread.realizedYk`, `k` at the application site is
  `PaddingAndClock.slowIndex`, `q_seed` is `FixedLevelCarriers.qSeed` and `B(n)`
  is `IterationAssembly.depthB`.  **No numeral is assigned to any of them**, and
  the seed carriers of Part 7 are *evaluated* through
  `n -> depthB n -> aSeed -> qSeed -> (2 ^ qSeed, qSeed)`.
* `M6`: zero-based finite slots throughout (`conv:finite-slots`); every
  reindexing lands in `Fin m`.
* `M9`: both interlace widths stay distinct and in their exchanged roles --
  `chainedFinalCarriers` prints `(q_i m_{N,i})^{Q_i}` on the row side and
  `Q_i n_{N,i}^{q_i}` on the column side, exactly as `eq:fixed-level-carriers`
  does.

## Reader counterparts

**No declaration in this module claims a reader item**, and the sweep behind
that statement was run first-hand this tranche over
`routes/parameterized-np/reader-facing/sections/`:

* The reader's only statement of canonical-reindexing invariance is
  `05-iteration.tex:152--154`, "Relabelling the finite row and column carriers by
  initial segments changes neither protocols nor retained densities" -- and it
  sits **inside the proof environment** of `thm:paper-finite-iteration`
  (`\begin{proof}` at line 146, `\end{proof}` at line 155).  Proof-internal prose
  is a navigation locus and not a claimable reader item, by the precedent
  `EFFECTIVE-MAIN-001`, `cc-t1x` and `FINAL-ONLY-DUPLICATION-001` record; it is
  named here and claimed nowhere.
* `C-effectivity-details.tex:104--106`, "record the exact budgets, carrier
  equivalences, forgetful maps, least-representative sections, and the canonical
  reindexing used as the next seed", is an unlabelled item of a descriptive
  enumerate in the reader appendix.  A repository-wide sweep of
  `src/EthInapproximability/ParameterizedNP/*.lean` for
  `C-effectivity-details.tex` citations returns, outside this module, only
  `:82--84` (`CoefficientTraversal`, `EnvelopeRealization`), `:86--88`
  (`EnvelopeRealization`) and `:134--138` (`EffectiveMaterialization`), so
  `:104--106` is unclaimed -- and it stays unclaimed here, being prose rather
  than a statement.
* The labelled reader displays in the neighbourhood are already assigned and are
  **not** re-cited: `eq:paper-exact-carrier-recurrence`
  (`05-iteration.tex`, label line 166) to `SIZE-001`/`ITER-001`,
  `eq:paper-budget-update` (label line 116), the closed-form display (lines
  129--133) and the `YES`/`NO` lines (137, 138) to `ITER-001`.

The canonical reindexing is therefore **autoformalization-only content**, in the
same sense as `FinalOnlyDuplication`'s final-only duplication clause.

## GAP-EXPOSED

1. **The bracket half of `lem:canonical-reindexing-invariance` is not landed.**
   Frozen lines 146--165 assert a cardinality-preserving bijection between the
   extraction data of `bracket(Can(M), p, x, z)` and `bracket(M, p, x, z)` and
   the resulting equalities `eq:canonical-bracket-invariance`, including the
   three-rung `Lambda_3` equality.  Nothing below asserts, uses or approximates
   any of that: the bracket, the retained densities and `Lambda_3` do not occur
   in this module at all.  The range **`12:146--165` stays GAP-EXPOSED in full**
   and remains owed by `ITER-001`.  In particular the second conclusion of the
   frozen display 374--378, `Lambda_3(R_0, 1, 2^{-B(n)}, 3/5) >= D_0` at **line
   377** (line 379 is its two-lemma justification), is **not** delivered by Part 7,
   which lands the complexity half only.
2. **The recursive canonical orders of `def:level-public-input` are not
   transcribed.**  Frozen lines 93--98 fix the order on each constructed carrier
   (initial segments naturally, tagged sums by tag then within a tag, products
   lexicographically, function spaces lexicographically in increasing coordinate
   order, subtypes by the induced order).  This module takes the carrier's linear
   order as an *instance argument* rather than deriving it from a transcription
   of that recursion, so `CanonicalChain` is general in the order.  Two
   mitigations, both landed: `canonOrderEquiv_unique` shows that once an order is
   fixed the equivalence is not a further choice, and
   `Can_complexity_indep_of_order` shows that the only content this module and
   its consumers take from `Can` -- the two cardinalities and the transported
   complexity -- is the same for every linear order.  Part 7 does **not** use
   that latitude: it supplies the frozen lexicographic order on
   `{0,1}^{q_seed}` itself.
3. **The canonical inhabitation of `CanonicalChain` is REGISTERED AS DEFERRED.**
   The paper's own chain has `R_i^+` equal to the level-`i` constructor output,
   which needs the unbuilt Stage-1--4 chain; `probeChain` is therefore a
   **NON-FIDELITY** smoke probe and is labelled as such where it occurs.  What is
   discharged at the paper's own instance is the *seed* equation
   `R_0 = Can(F_{B(n)})` of frozen line 363 (Part 7) and the *successor* carrier
   identification `chainingStep_from_oneLevel`, which is the paper's own one-level
   output.  The fully instantiated chain stays owed by `ITER-001`,
   `STAGE1-001 .. WRAP-001` and `MATERIALIZE-001`.
4. **The per-level clause shape is the banked one, and it is not the frozen
   clause C2/C3 shape.**  Frozen lines 336--345 obtain the per-level updates as
   implications out of `YesCert(Public_i)` / `NoCert(Public_i)`; the banked
   `ITER-001` inductions take the *difference* form
   `cc (i+1) <= cc i + H i` and `cc (i+1) = cc i + H i + 1`, and this module
   consumes them at exactly that shape.  Turning the frozen certificate-guarded
   clauses into those differences needs `thm:one-level` C1--C3 in Lean, which is
   `ONELEVEL-001` and is not claimed here.
5. **The seed budget identity is not discharged.**  Frozen line 370 sets
   `D_0 = Y_0 = comp F_{B(n)} = a_seed + 1`; Part 7 delivers
   `comp R_0 = comp F_{B(n)}` and stops, because the complexity display of
   `lem:full-cube-seed` is banked only at requested depth `b = 0`, not at the
   scheduled depth `B(n)` -- the same boundary `FixedLevelCarriers`'
   `seedAnchored_carriers` records.
6. **No route completion is claimed.**  The construction layer and the machine
   layer are both unlanded; this row discharges one definition, one lemma's
   complexity half, one hypothesis display, and the three wirings named above.
-/

namespace EthInapproximability.ParameterizedNP.IteratedCanonicalChaining

open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.BudgetThreadWiring
open EthInapproximability.ParameterizedNP.DepthThread
open EthInapproximability.ParameterizedNP.EffectiveMaterialization
open EthInapproximability.ParameterizedNP.FinalOnlyDuplication

/-! ## Part 1: the unique increasing equivalence (`12:93--104`) -/

/-- **The unique increasing equivalence `e_X^m : [m] -> X`** --
`12-iteration-specification.tex:93--104`.

Frozen text: "if `X` is one of these nonempty carriers, there is a unique
increasing equivalence `e_X : [|X|] -> X`.  This equivalence is determined by the
carrier itself; it is not an additional choice and cannot depend on a YES or NO
certificate."

The carrier's canonical order of frozen lines 93--98 is taken as the ambient
`LinearOrder` instance (GAP-EXPOSED 2), and the increasing equivalence is
Mathlib's `monoEquivOfFin`, i.e. the order isomorphism `Fin m ≃o X` determined by
that order and the cardinality equation.  Under `conv:finite-slots` the source is
the zero-based slot type `Fin m`.

General in the carrier, its order, and the slot count.  Claims no reader item. -/
noncomputable def canonOrderEquiv (X : Type u) [Fintype X] [LinearOrder X] {m : ℕ}
    (h : Fintype.card X = m) : Fin m ≃o X :=
  monoEquivOfFin X h

/-- **The same equivalence, forgetting the order** -- the map frozen line 101
writes as `e_X`. -/
noncomputable def canonEquiv (X : Type u) [Fintype X] [LinearOrder X] {m : ℕ}
    (h : Fintype.card X = m) : Fin m ≃ X :=
  (canonOrderEquiv X h).toEquiv

/-- **Aux 1 (uniqueness: "it is not an additional choice").**

`12-iteration-specification.tex:103--104`.  Every increasing equivalence
`[m] -> X` *is* `canonOrderEquiv`, so nothing downstream can depend on a
selection: in particular no YES or NO certificate can influence it, which is the
frozen sentence's purpose.

Statement pole: this is false for equivalences that are merely bijective -- for
`m >= 2` the type `Fin m ≃ X` has `m!` members -- so the increasing hypothesis is
doing the work and is not decoration.

General in the carrier, its order and the slot count. -/
theorem canonOrderEquiv_unique {X : Type u} [Fintype X] [LinearOrder X] {m : ℕ}
    (h : Fintype.card X = m) (e : Fin m ≃o X) : e = canonOrderEquiv X h :=
  Subsingleton.elim _ _

/-- **Aux 2 (the equivalence is increasing).**  The frozen word "increasing" of
line 99, recorded so consumers never unfold `monoEquivOfFin`.  General. -/
theorem canonEquiv_strictMono {X : Type u} [Fintype X] [LinearOrder X] {m : ℕ}
    (h : Fintype.card X = m) : StrictMono (canonEquiv X h) :=
  (canonOrderEquiv X h).strictMono

/-- **Aux 3 (identity law: an initial segment is already canonically ordered).**

Frozen lines 94--95: "initial segments use their natural order".  So on `[m]` itself
the increasing equivalence is the identity, and the canonical transport of
`def:canonical-reindexing` does nothing -- which is why the frozen chaining is
applied to the *level output carriers* and not to the slot types.  General in the
slot count. -/
theorem canonEquiv_fin {m : ℕ} (h : Fintype.card (Fin m) = m) :
    canonEquiv (Fin m) h = Equiv.refl (Fin m) := by
  have hrefl : canonOrderEquiv (Fin m) h = OrderIso.refl (Fin m) := Subsingleton.elim _ _
  rw [canonEquiv, hrefl]
  rfl

/-! ## Part 2: `def:canonical-reindexing` (`12:106--137`) -/

/-- **Transport of a matrix along a pair of equivalences.**

The general shape of `eq:canonical-reindexing`
(`12-iteration-specification.tex`, label line 116) before the increasing
equivalences are fixed.  It is separated from `Can` because
`lem:canonical-reindexing-invariance`'s proof (frozen lines 169--171) uses only
that the two maps are equivalences: "A protocol is transported in either
direction by applying the row and column equivalences locally."

The output type is arbitrary; the frozen Boolean case is `Z = Bool`.  General in
everything.  Claims no reader item. -/
def reindex {X : Type u} {Y : Type v} {Z : Type w} {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Z) : Fin m → Fin n → Z :=
  fun u v => M (eX u) (eY v)

/-- **Aux 4 (the defining equation of `reindex`).**  Recorded so that consumers
never unfold it by hand.  General in everything. -/
theorem reindex_apply {X : Type u} {Y : Type v} {Z : Type w} {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Z) (u : Fin m) (v : Fin n) :
    reindex eX eY M u v = M (eX u) (eY v) := rfl

/-- **`Can_{m,n}(M)`, the canonical finite reindexing** --
`def:canonical-reindexing` (`12-iteration-specification.tex`, label line 107)
with `eq:canonical-reindexing` (label line 116):

```
Can(M)(u,v) = M(e_X(u), e_Y(v)),      u in [m], v in [n].
```

The two-index form of frozen lines 119--126 is the one taken here, because it is
the form `eq:iterated-canonical-chaining` consumes: the slot counts `m`, `n` are
given, and the two cardinality equalities `hm`, `hn` are what tie them to the
carriers.

Claims no reader item. -/
noncomputable def Can {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y] {m n : ℕ}
    (hm : Fintype.card X = m) (hn : Fintype.card Y = n) (M : X → Y → Z) :
    Fin m → Fin n → Z :=
  reindex (canonEquiv X hm) (canonEquiv Y hn) M

/-- **Aux 5 (the frozen pointwise display).**  `eq:canonical-reindexing` read at
one entry.  General in everything. -/
theorem Can_apply {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y] {m n : ℕ}
    (hm : Fintype.card X = m) (hn : Fintype.card Y = n) (M : X → Y → Z)
    (u : Fin m) (v : Fin n) :
    Can hm hn M u v = M (canonEquiv X hm u) (canonEquiv Y hn v) := rfl

/-- **Aux 6 (identity law).**  On the slot types themselves the canonical
reindexing is the identity, by `canonEquiv_fin`.  This is the `Can` half of the
frozen `k = 0` reading (lines 320--323): when there is nothing to relabel, the
clause reduces to its hypothesis.  General in the slot counts, the output type
and the matrix. -/
theorem Can_fin_id {Z : Type w} {m n : ℕ}
    (hm : Fintype.card (Fin m) = m) (hn : Fintype.card (Fin n) = n)
    (M : Fin m → Fin n → Z) : Can hm hn M = M := by
  funext u v
  rw [Can_apply, canonEquiv_fin, canonEquiv_fin]
  rfl

/-- **Aux 7 (round trip).**  Reading the reindexed matrix back through the two
inverse equivalences recovers the original.  This is the formal content of "the
row and column equivalences" being applied "in either direction" (frozen lines
169--170), and it is what the second half of `reindex_complexity` consumes.
General in everything. -/
theorem reindex_symm_apply {X : Type u} {Y : Type v} {Z : Type w} {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Z) :
    (fun x y => reindex eX eY M (eX.symm x) (eY.symm y)) = M := by
  funext x y
  simp [reindex]

/-- **Aux 8 (the transport is faithful on rows).**

A reindexing along equivalences never identifies two distinct rows: if the rows
of `M` are pairwise distinct then so are the rows of `reindex eX eY M`.

Statement pole, and the reason this lemma is here: a *duplication* in the sense
of `FinalOnlyDuplication.Duplication` does exactly the opposite -- its
`duplicationDestroysRowDistinctness` exhibits a legal duplication that collapses
two rows.  So the frozen distinction between the canonical reindexing of
`12:106--137` (a bijective relabelling, run at every level) and the final-only
duplication of `12:307--317` (a surjective collapse, run once, outside every
`T_i`) is real, and an encoding that conflated them would be refuted by this
pair.  General in everything. -/
theorem reindex_row_injective {X : Type u} {Y : Type v} {Z : Type w} {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Z) (hM : Function.Injective M) :
    Function.Injective (reindex eX eY M) := by
  intro u u' huu'
  apply eX.injective
  apply hM
  funext y
  have := congrFun huu' (eY.symm y)
  simpa [reindex] using this

/-- **The frozen typed assertion `R = Can_{m,n}(M)`** --
`12-iteration-specification.tex:127--136`.

Frozen text: the assertion "abbreviates the pointwise equation
`R(u,v) = M(e_X^m(u), e_Y^n(v))` for `u in [m]`, `v in [n]`, together with the
two cardinality equalities that define the displayed increasing equivalences.  It
never denotes a heterogeneous equality of functions."

That is exactly this predicate: two cardinality equalities and one pointwise
equation, and no equality between matrices of unlike carrier type anywhere.  The
two equalities are existentially bound because the frozen sentence makes them
*part of* the assertion rather than side conditions of it; by proof irrelevance
the bound proofs are unique, so `canonEquiv X hm` is well defined.

Claims no reader item. -/
def IsCanonicalReindex {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y]
    (M : X → Y → Z) (m n : ℕ) (R : Fin m → Fin n → Z) : Prop :=
  ∃ (hm : Fintype.card X = m) (hn : Fintype.card Y = n),
    ∀ u v, R u v = M (canonEquiv X hm u) (canonEquiv Y hn v)

/-- **Aux 9 (the canonical reindexing satisfies the frozen typed assertion).**

Non-vacuity of `IsCanonicalReindex` at the construction it names.  General in
everything. -/
theorem Can_isCanonicalReindex {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y] {m n : ℕ}
    (hm : Fintype.card X = m) (hn : Fintype.card Y = n) (M : X → Y → Z) :
    IsCanonicalReindex M m n (Can hm hn M) :=
  ⟨hm, hn, fun _ _ => rfl⟩

/-- **Aux 10 (the frozen typed assertion determines the matrix).**

The converse of Aux 9: anything satisfying the assertion *is* `Can_{m,n}(M)`.  So
the predicate is not a weakening of the definition, which is what lets
`eq:iterated-canonical-chaining` be read either way without ambiguity.  General
in everything. -/
theorem isCanonicalReindex_eq_Can {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y] {m n : ℕ}
    {M : X → Y → Z} {R : Fin m → Fin n → Z} (h : IsCanonicalReindex M m n R) :
    ∃ (hm : Fintype.card X = m) (hn : Fintype.card Y = n), R = Can hm hn M := by
  obtain ⟨hm, hn, hpt⟩ := h
  refine ⟨hm, hn, ?_⟩
  funext u v
  rw [Can_apply]
  exact hpt u v

/-! ## Part 3: `lem:canonical-reindexing-invariance`, complexity half
(statement `12:139--166`, proof `12:168--180`) -/

/-- **The transport of protocols in either direction** --
`12-iteration-specification.tex:169--171`: "A protocol is transported in either
direction by applying the row and column equivalences locally, so
`eq:canonical-complexity-invariance` follows with no communication overhead."

Both directions are precomposition, consumed by pin through
`CommonPadding.precomposition_no_increase` -- the route facade for the
kernel-checked vendored `Workspace.ProofLemmas.SublemmaPrecompNoIncrease`.  It is
not re-exported here.  General in the carriers, the two equivalences, the output
type and the matrix.  Claims no reader item. -/
theorem reindex_complexity {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Z) :
    D (reindex eX eY M) = D M := by
  refine le_antisymm (CommonPadding.precomposition_no_increase M eX eY) ?_
  have h := CommonPadding.precomposition_no_increase (reindex eX eY M) eX.symm eY.symm
  rwa [reindex_symm_apply eX eY M] at h

/-- **`eq:canonical-complexity-invariance`** --
`12-iteration-specification.tex`, label line 144:

```
comp(Can(M)) = comp(M).
```

The first display of `lem:canonical-reindexing-invariance`, at the two-index form
`Can_{m,n}` covered by the lemma's closing sentence (line 165, "The same
conclusions hold for `Can_{m,n}(M)`").

Scope, honoured exactly: only the deterministic communication complexity is
transported.  The lemma's second half -- the bijection between bracket extraction
data and `eq:canonical-bracket-invariance` (lines 146--165) -- is **not** asserted
here and is GAP-EXPOSED 1.

General in the carriers, their orders, the slot counts, the output type and the
matrix.  Claims no reader item. -/
theorem canonicalReindexing_invariance {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y] {m n : ℕ}
    (hm : Fintype.card X = m) (hn : Fintype.card Y = n) (M : X → Y → Z) :
    D (Can hm hn M) = D M :=
  reindex_complexity _ _ M

/-- **The invariance, read through the frozen typed assertion.**

The form the chaining consumes: whatever satisfies the frozen assertion of lines
127--136 has the complexity of the matrix it reindexes.  General in everything.
Claims no reader item. -/
theorem isCanonicalReindex_complexity {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [LinearOrder X] [Fintype Y] [LinearOrder Y] {m n : ℕ}
    {M : X → Y → Z} {R : Fin m → Fin n → Z} (h : IsCanonicalReindex M m n R) :
    D R = D M := by
  obtain ⟨hm, hn, hEq⟩ := isCanonicalReindex_eq_Can h
  rw [hEq, canonicalReindexing_invariance]

/-- **Aux 11 (the consumed content does not depend on which order the carrier
carries).**

GAP-EXPOSED 2's mitigation.  This module takes the carrier's canonical order of
frozen lines 93--98 as an instance rather than transcribing that recursion, and
the risk that would create is that `Can` -- and hence the whole chaining -- might
secretly depend on the choice.  It does not, for the content used: whichever
linear orders the two carriers are given, the transported complexity is the same
integer, namely `comp(M)`.  The two cardinality equalities of the frozen typed
assertion are likewise order-free.

What this does **not** say is that `Can` itself is order-free: it is not, and
`canonOrderEquiv_unique` is what pins it once an order is fixed.

General in the carriers, the four orders, the slot counts, the output type and
the matrix.  Claims no reader item. -/
theorem Can_complexity_indep_of_order {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] (oX oX' : LinearOrder X) (oY oY' : LinearOrder Y)
    {m n : ℕ} (hm : Fintype.card X = m) (hn : Fintype.card Y = n) (M : X → Y → Z) :
    D (@Can X Y Z _ oX _ oY m n hm hn M) = D (@Can X Y Z _ oX' _ oY' m n hm hn M) := by
  rw [@canonicalReindexing_invariance X Y Z _ oX _ oY m n hm hn M,
    @canonicalReindexing_invariance X Y Z _ oX' _ oY' m n hm hn M]

/-! ## Part 4: `eq:iterated-canonical-chaining` (`12:222--230`) -/

/-- **The per-level output carriers with their canonical orders.**

Frozen lines 87--88: "The literal output carriers of one level are tagged sums,
finite products, and finite function spaces", each carrying the recursive
canonical order of lines 93--98.  This record bundles, for each level `i`, the two carriers
of `R_i^+` together with the two instances the canonical reindexing needs, and
**nothing else** (`M2`/`M4`): no matrix, no cardinality, no complexity.

The order is an instance argument, not a transcription of the frozen recursion
(GAP-EXPOSED 2).  Claims no reader item. -/
structure OutputCarriers where
  /-- `Rows(R_i^+)`, the row carrier of the level-`i` output (frozen line 224). -/
  Row : ℕ → Type
  /-- `Cols(R_i^+)`, the column carrier of the level-`i` output (frozen line 226). -/
  Col : ℕ → Type
  /-- Finiteness of the row carrier -- frozen lines 108--109, "nonempty finite
  carriers". -/
  rowFintype : ∀ i, Fintype (Row i)
  /-- The carrier's canonical order (frozen lines 93--98), taken as an instance. -/
  rowOrder : ∀ i, LinearOrder (Row i)
  /-- Finiteness of the column carrier. -/
  colFintype : ∀ i, Fintype (Col i)
  /-- The column carrier's canonical order. -/
  colOrder : ∀ i, LinearOrder (Col i)

attribute [instance] OutputCarriers.rowFintype OutputCarriers.rowOrder
  OutputCarriers.colFintype OutputCarriers.colOrder

/-- **`eq:iterated-canonical-chaining`, level-indexed** --
`12-iteration-specification.tex`, label line 229, display lines 222--230:

```
m_{i+1} = |Rows(R_i^+)|,   n_{i+1} = |Cols(R_i^+)|,
R_{i+1} = Can_{m_{i+1}, n_{i+1}}(R_i^+).
```

The three fields `rowCard`, `colCard`, `chain` are those three equations, at the
banked carriers of a `FixedLevelCarriers.LevelCarrierSpec`: `m_i` is
`S.rowCarrier i` and `n_i` is `S.colCarrier i`, so the chaining's *targets* are
schedule quantities and not binders (`M3`).  The `chain` field is an equality of
functions on `Fin m_{i+1} x Fin n_{i+1}`, which is the frozen reading of lines
135--136 -- never a heterogeneous equality.

**Fields, and nothing else** (`M2`/`M4`): the level matrices, the output carriers
with their two instances, the output matrices, and the three frozen equations.
No complexity value, no budget, no depth, no overhead, no promise certificate and
no robustness statement is a field; `chain_complexity` is a theorem about the
pinned construction.  Surjectivity, injectivity and the invariance are all
derived and none is a field, since each would restate a derived telescope.

The frozen display quantifies over `0 <= i < k` for a fixed `k`; the record
carries the whole zero-based family, and it is the *fold theorems*
(`chainYesFold`, `chainNoFold`) that reinstate the frozen bound, since that is
where the bound has content.

Claims no reader item. -/
structure CanonicalChain (S : FixedLevelCarriers.LevelCarrierSpec)
    extends OutputCarriers where
  /-- `R_i : [m_i] x [n_i] -> {0,1}`, clause F2 (frozen lines 201--204). -/
  lev : ∀ i : ℕ, Fin (S.rowCarrier i) → Fin (S.colCarrier i) → Bool
  /-- `R_i^+`, the level-`i` output matrix on its own carriers (frozen line 218). -/
  out : ∀ i : ℕ, Row i → Col i → Bool
  /-- `m_{i+1} = |Rows(R_i^+)|` -- frozen line 224. -/
  rowCard : ∀ i, Fintype.card (Row i) = S.rowCarrier (i + 1)
  /-- `n_{i+1} = |Cols(R_i^+)|` -- frozen line 226. -/
  colCard : ∀ i, Fintype.card (Col i) = S.colCarrier (i + 1)
  /-- `R_{i+1} = Can_{m_{i+1},n_{i+1}}(R_i^+)` -- frozen line 227. -/
  chain : ∀ i, lev (i + 1) = Can (rowCard i) (colCard i) (out i)

namespace CanonicalChain

variable {S : FixedLevelCarriers.LevelCarrierSpec}

/-- **Aux 12 (the chaining equation, pointwise).**

`eq:iterated-canonical-chaining` read at one entry, through
`def:canonical-reindexing`'s own pointwise display.  Recorded so that consumers
never unfold `Can`.  General in the specification, the chain and the level. -/
theorem chain_apply (C : CanonicalChain S) (i : ℕ)
    (u : Fin (S.rowCarrier (i + 1))) (v : Fin (S.colCarrier (i + 1))) :
    C.lev (i + 1) u v =
      C.out i (canonEquiv (C.Row i) (C.rowCard i) u)
        (canonEquiv (C.Col i) (C.colCard i) v) := by
  rw [C.chain i, Can_apply]

/-- **Aux 13 (the frozen typed assertion holds at every level of the chain).**

The record's three fields are literally an instance of `IsCanonicalReindex` at
each level, which is the check that the encoding of frozen lines 222--230 is the
encoding of frozen lines 127--136 and not a second, weaker reading.  General. -/
theorem isCanonicalReindex (C : CanonicalChain S) (i : ℕ) :
    IsCanonicalReindex (C.out i) (S.rowCarrier (i + 1)) (S.colCarrier (i + 1))
      (C.lev (i + 1)) := by
  rw [C.chain i]
  exact Can_isCanonicalReindex _ _ _

/-- **`lem:canonical-reindexing-invariance` along the chain** --
`12-iteration-specification.tex:339--341`: "Canonical-reindexing invariance and
`eq:iterated-canonical-chaining` give the same inequality for `R_{i+1}`."

This is that sentence: at every level the relabelled matrix has the complexity of
the level output it relabels.  It is the single fact the two inductions of Part 5
need from the chaining, and it is what `ITER-001` records as "absorbed into the
named transfer hypotheses of the composed steps" -- here it is proved instead of
assumed.

Statement pole: the trivial reading would bound one complexity by the other; the
frozen sentence transports the *equality*, and the `NO` fold of Part 5 needs the
equality, not either inequality.

General in the specification, the chain and the level.  Claims no reader item. -/
theorem chain_complexity (C : CanonicalChain S) (i : ℕ) :
    D (C.lev (i + 1)) = D (C.out i) :=
  isCanonicalReindex_complexity (C.isCanonicalReindex i)

end CanonicalChain

/-- **The chaining composed with the banked one-level carrier equations** --
`eq:iterated-canonical-chaining` (label line 229) at the output of the frozen
constructor call of clause F3.

Frozen lines 257--258 attribute the carrier equations to "clause C4 of
`thm:one-level`", and the banked `FixedLevelCarriers.fixedLevelCarriers_realized`
is that attribution: the level output `R_i^+ = levelOutput N ...` has exactly the
schedule's carriers `m_{i+1}`, `n_{i+1}`.  So the two cardinality equalities the
frozen chaining *demands* are supplied by the one-level theorem rather than
assumed, and the third equation then determines `R_{i+1}` outright.

Nothing is re-derived: the two cardinalities are the banked theorem consumed by
pin, and the complexity transport is `reindex_complexity`.  The two interlace
widths reach this statement only through the banked `S.qExp i` and
`EntryGates.Qwidth (S.bout i) (S.dU i)`, and neither is assigned a numeral
(`M3`, `M9`).

The two linear orders are instance arguments (GAP-EXPOSED 2); by
`Can_complexity_indep_of_order` the conclusion does not depend on them.

General in the two pre-wrapper carriers, the specification, the level, the
pre-wrapper matrix, its two recorded counts and the two orders.  Claims no reader
item. -/
theorem chainingStep_from_oneLevel {X Y : Type} [Fintype X] [Fintype Y]
    (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) (N : X → Y → Bool)
    (hm : BridgeOutputEquality.rowsCard N = S.mN i)
    (hn : BridgeOutputEquality.colsCard N = S.nN i)
    [LinearOrder (Fin (EntryGates.Qwidth (S.bout i) (S.dU i)) → Fin (2 ^ S.qExp i) × X)]
    [LinearOrder (Fin (EntryGates.Qwidth (S.bout i) (S.dU i)) × (Fin (2 ^ S.qExp i) → Y))] :
    ∃ (hrow : Fintype.card
          (Fin (EntryGates.Qwidth (S.bout i) (S.dU i)) → Fin (2 ^ S.qExp i) × X)
          = S.rowCarrier (i + 1))
      (hcol : Fintype.card
          (Fin (EntryGates.Qwidth (S.bout i) (S.dU i)) × (Fin (2 ^ S.qExp i) → Y))
          = S.colCarrier (i + 1)),
      IsCanonicalReindex
          (OneLevelCompletion.levelOutput N (S.qExp i) (S.bout i) (S.dU i))
          (S.rowCarrier (i + 1)) (S.colCarrier (i + 1))
          (Can hrow hcol (OneLevelCompletion.levelOutput N (S.qExp i) (S.bout i) (S.dU i)))
        ∧ D (Can hrow hcol
              (OneLevelCompletion.levelOutput N (S.qExp i) (S.bout i) (S.dU i)))
            = D (OneLevelCompletion.levelOutput N (S.qExp i) (S.bout i) (S.dU i)) := by
  obtain ⟨hrow, hcol⟩ := FixedLevelCarriers.fixedLevelCarriers_realized S i N hm hn
  exact ⟨hrow, hcol, Can_isCanonicalReindex _ _ _, canonicalReindexing_invariance _ _ _⟩

/-! ## Part 5: the two inductions carried on a typed chain (`12:267--297`)

Both folds quantify the per-level clause over `i < j`, which is frozen F3's own
range `0 <= i < k` (line 205); and both consume the banked `ITER-001` induction
on the numeric complexity sequence rather than restating it. -/

/-- **The truncated complexity sequence of a chain, for the `NO` fold.**

Pure scaffolding, and the paper instantiates nothing of the kind: it exists only
so that the banked `IterationAssembly.fixedLevelGap_no_induction`, whose
hypothesis is the *unbounded* per-level equality, can be consumed at the frozen
*bounded* hypothesis `0 <= i < j` without restating the induction.  Below `j` it
is the chain's own complexity sequence; from `j` on it continues along the ladder
by definition, which is vacuous for the conclusion at index `j`.

The `YES` fold needs no such device: `fun i => D (C.lev (min i j))` already has
the banked shape there, because the extension has to satisfy an inequality rather
than an equality. -/
noncomputable def chainNoSequence {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (H : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => D (C.lev 0)
  | i + 1 => if i < j then D (C.lev (i + 1)) else chainNoSequence C H j i + H i + 1

/-- **Aux 14 (the truncated sequence is the chain's complexity sequence below the
bound).**  General in the specification, the chain, the overhead sequence, the
bound and the index. -/
theorem chainNoSequence_eq {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (H : ℕ → ℕ) (j : ℕ) {t : ℕ} (ht : t ≤ j) :
    chainNoSequence C H j t = D (C.lev t) := by
  cases t with
  | zero => rfl
  | succ i =>
    rw [chainNoSequence, if_pos (by omega)]

/-- **The `YES` fold on a typed chain** -- `thm:fixed-level-gap-size` (iii),
`12-iteration-specification.tex:267--277`, carried on the matrices themselves.

Frozen line 277: "No robustness hypothesis or conclusion is used in this
implication" -- accordingly no depth, density, bracket or robustness quantity
occurs in this statement.

The two hypotheses are the frozen ones, in the frozen ranges: the seed bound
`comp R_0 <= Y_0` at the base state's own budget slot, and the per-level clause
for `0 <= i < j` only (frozen F3, line 205).  The chaining enters through
`CanonicalChain.chain_complexity`, and the arithmetic is the banked
`IterationAssembly.fixedLevelGap_yes_induction` consumed by pin at the truncated
sequence; the budget readout is the banked
`BudgetThreadWiring.realizedBudgets_are_the_banked_ladders`, so `Y_j` is the live
arrow's own slot and no numeral is assigned to it (`M3`).

Per-level clause shape: this is the banked difference form, not the frozen
certificate-guarded clause C2 (GAP-EXPOSED 4).

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the base state and the level.  Claims no reader item. -/
theorem chainYesFold (S : FixedLevelCarriers.LevelCarrierSpec) (C : CanonicalChain S)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (j : ℕ)
    (hbase : D (C.lev 0) ≤ S₀.budgetY)
    (hstep : ∀ i, i < j → D (C.out i) ≤ D (C.lev i) + realizedOverhead S aE q2E sE i) :
    D (C.lev j) ≤ realizedY S aE q2E sE auxW invT robD S₀ j := by
  have hcc : ∀ i : ℕ,
      D (C.lev (min (i + 1) j)) ≤
        D (C.lev (min i j)) + realizedOverhead S aE q2E sE i := by
    intro i
    by_cases hij : i < j
    · have e1 : D (C.lev (min (i + 1) j)) = D (C.lev (i + 1)) :=
        congrArg (fun t : ℕ => D (C.lev t)) (by omega)
      have e2 : D (C.lev (min i j)) = D (C.lev i) :=
        congrArg (fun t : ℕ => D (C.lev t)) (by omega)
      rw [e1, e2, C.chain_complexity i]
      exact hstep i hij
    · have e1 : D (C.lev (min (i + 1) j)) = D (C.lev j) :=
        congrArg (fun t : ℕ => D (C.lev t)) (by omega)
      have e2 : D (C.lev (min i j)) = D (C.lev j) :=
        congrArg (fun t : ℕ => D (C.lev t)) (by omega)
      rw [e1, e2]
      omega
  have hzero : D (C.lev (min 0 j)) ≤ S₀.budgetY := by
    have e0 : D (C.lev (min 0 j)) = D (C.lev 0) :=
      congrArg (fun t : ℕ => D (C.lev t)) (by omega)
    rw [e0]; exact hbase
  have hfold := IterationAssembly.fixedLevelGap_yes_induction S₀.budgetY
    (realizedOverhead S aE q2E sE) (fun i => D (C.lev (min i j))) hzero hcc j
  have ej : D (C.lev (min j j)) = D (C.lev j) :=
    congrArg (fun t : ℕ => D (C.lev t)) (by omega)
  rw [(realizedBudgets_are_the_banked_ladders S aE q2E sE auxW invT robD S₀ j).1]
  simpa [ej] using hfold

/-- **The `NO` fold on a typed chain** -- `thm:fixed-level-gap-size` (iv),
`12-iteration-specification.tex:279--297`, complexity half, carried on the
matrices themselves.

The frozen clause has two displays; only the **first** of
`eq:fixed-level-no-induction` (`comp R_j = D_j`) is claimed here.  The second --
the regenerated depth-`b_j` robustness certificate -- is a bracket statement and
is deliberately absent (GAP-EXPOSED 1); it is delivered per level by the banked
`OneLevelAssembly.oneLevelAssembly_no` and is not transported through this module.

The hypotheses are the frozen ones in the frozen ranges, and the arithmetic is
the banked `IterationAssembly.fixedLevelGap_no_induction` consumed by pin at
`chainNoSequence`.  `D_j` is the live arrow's own slot through
`BudgetThreadWiring.realizedD` (`M3`).

Per-level clause shape: the banked difference form, not the frozen
certificate-guarded clause C3 (GAP-EXPOSED 4).

General in the same arguments as `chainYesFold`.  Claims no reader item. -/
theorem chainNoFold (S : FixedLevelCarriers.LevelCarrierSpec) (C : CanonicalChain S)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (j : ℕ)
    (hbase : D (C.lev 0) = S₀.budgetD)
    (hstep : ∀ i, i < j →
      D (C.out i) = D (C.lev i) + realizedOverhead S aE q2E sE i + 1) :
    D (C.lev j) = realizedD S aE q2E sE auxW invT robD S₀ j := by
  set H := realizedOverhead S aE q2E sE with hH
  have hcc : ∀ i : ℕ,
      chainNoSequence C H j (i + 1) = chainNoSequence C H j i + H i + 1 := by
    intro i
    by_cases hij : i < j
    · rw [chainNoSequence, if_pos hij, chainNoSequence_eq C H j (by omega : i ≤ j),
        C.chain_complexity i]
      exact hstep i hij
    · rw [chainNoSequence, if_neg hij]
  have hzero : chainNoSequence C H j 0 = S₀.budgetD := hbase
  have hfold := IterationAssembly.fixedLevelGap_no_induction S₀.budgetD H
    (chainNoSequence C H j) hzero hcc j
  rw [(realizedBudgets_are_the_banked_ladders S aE q2E sE auxW invT robD S₀ j).2,
    ← chainNoSequence_eq C H j (le_refl j), hfold]

/-! ## Part 6: the three wirings of `FinalOnlyDuplication`

`FinalOnlyDuplication` records two obstructions in its GAP-EXPOSED list: the
level-`k` matrix is a free binder there because the chaining and the invariance
were not in Lean, and the two promise-case hypotheses are named binders rather
than the conclusions of the two inductions.  Both are removed below: the matrix
is `C.lev k`, a member of a chain whose carriers are the banked schedule
carriers, and the two rows are derived from the frozen seed conditions and the
frozen per-level updates. -/

/-- **Wiring 1: the duplication's targets are the chain's own carriers, and they
are the exact recurrence.**

Three frozen facts at one index, none re-derived.  The two cardinality equations
are `eq:iterated-canonical-chaining`'s first line (frozen lines 224--226), read
off the chain's `rowCard` / `colCard` fields; the two closed forms are
`eq:fixed-level-carriers` (label line 264) consumed by pin as
`FixedLevelCarriers.fixedLevelCarriers`.  Together they say that the `[m_k]`,
`[n_k]` of `12:309--310` -- the targets of the two duplication surjections -- are
simultaneously the cardinalities of the previous level's *output* carriers and
the schedule's own exact carriers.

That is exactly what `FinalOnlyDuplication`'s GAP-EXPOSED 1 records as missing:
"The identification `m_k = |Rows(R_k)|` of `eq:iterated-canonical-chaining` needs
the level-`k` matrix object and `lem:canonical-reindexing-invariance`, neither of
which is in Lean."

`M9` is visible in the two closed forms: `Q_i` exponentiates on the row side and
multiplies on the column side, and `q_i` does the reverse.

General in the specification, the chain and the level.  Claims no reader item;
`eq:paper-exact-carrier-recurrence` (reader `05-iteration.tex`, label line 166)
is already assigned to `SIZE-001`. -/
theorem chainedFinalCarriers (S : FixedLevelCarriers.LevelCarrierSpec)
    (C : CanonicalChain S) (i : ℕ) :
    Fintype.card (C.Row i) = S.rowCarrier (i + 1) ∧
      Fintype.card (C.Col i) = S.colCarrier (i + 1) ∧
      S.rowCarrier (i + 1) = (S.q i * S.mN i) ^ S.Q i ∧
      S.colCarrier (i + 1) = S.Q i * S.nN i ^ S.q i := by
  obtain ⟨hrow, hcol⟩ := FixedLevelCarriers.fixedLevelCarriers S i
  exact ⟨C.rowCard i, C.colCard i, hrow, hcol⟩

/-- **Wiring 2: `eq:k-level-gap` derived along the chain and transferred through
the final-only duplication.**

`12-iteration-specification.tex:301--315`.  Both rows are now *conclusions*: the
`YES` row from `chainYesFold` and the `NO` row from `chainNoFold`, each out of the
frozen seed condition and the frozen per-level clause for `0 <= i < k`, and both
then moved onto the duplicated matrix by
`FinalOnlyDuplication.kLevelGapTransfers` consumed by pin.  Nothing of that
module is restated, and neither induction is re-proved.

**The two rows stay separate implications, never a conjunction**: they are the
two cases of one construction, and their per-level clauses are incompatible
whenever the range `i < k` is non-empty -- `chainedPromiseCases_exclusive` records
the transported form of that separation in the kernel, and
`chainedFold_hypotheses_consistent` records that at `k = 0`, where the frozen
family is empty, nothing is vacuous.

Statement pole: the trivial witness for the `NO` row would be a duplicated matrix
whose complexity is merely bounded by `Y_k + k`; the frozen row is an equality,
which a duplication that lowered the complexity would fail -- and that is exactly
what `FinalOnlyDuplication.dupComplexity`, not either one-sided direction, rules
out.

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the base state, the level, the two duplicated carriers and the
two duplication data.  Claims no reader item. -/
theorem chainedKLevelGapTransfers (S : FixedLevelCarriers.LevelCarrierSpec)
    (C : CanonicalChain S) (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ)
    (S₀ : LevelState) (hseed : S₀.budgetD = S₀.budgetY) (k : ℕ)
    {Xhat : Type u} {Zhat : Type v} [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier k)) (dZ : Duplication Zhat (S.colCarrier k)) :
    (D (C.lev 0) ≤ S₀.budgetY →
        (∀ i, i < k → D (C.out i) ≤ D (C.lev i) + realizedOverhead S aE q2E sE i) →
        D (dupMatrix dX dZ (C.lev k)) ≤ realizedY S aE q2E sE auxW invT robD S₀ k) ∧
      (D (C.lev 0) = S₀.budgetD →
        (∀ i, i < k →
          D (C.out i) = D (C.lev i) + realizedOverhead S aE q2E sE i + 1) →
        D (dupMatrix dX dZ (C.lev k)) = realizedD S aE q2E sE auxW invT robD S₀ k ∧
          D (dupMatrix dX dZ (C.lev k)) =
            realizedY S aE q2E sE auxW invT robD S₀ k + k) := by
  obtain ⟨htyes, htno⟩ :=
    kLevelGapTransfers S aE q2E sE auxW invT robD S₀ hseed k dX dZ (C.lev k)
  refine ⟨fun h0 hs => htyes (chainYesFold S C aE q2E sE auxW invT robD S₀ k h0 hs),
    fun h0 hs => htno (chainNoFold S C aE q2E sE auxW invT robD S₀ k h0 hs)⟩

/-- **Wiring 3: the same, at the paper's own level count `k = L(n)`.**

`12-iteration-specification.tex:360` fixes the intended fixed-level application
and `14-final-consequence.tex:1617` fixes `k = L(n)`; the clock index is the
banked `PaddingAndClock.slowIndex` consumed by pin and given no alias, and the
budget field is the banked `DepthThread.realizedYk`, which is `realizedY`
evaluated at it.  Neither quantity is re-derived: this is
`chainedKLevelGapTransfers` read at the index the frozen controller parses.

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the base state, the clock, the source size, the two duplicated
carriers and the two duplication data.  Claims no reader item. -/
theorem chainedFinalDuplication_at_the_clock
    (S : FixedLevelCarriers.LevelCarrierSpec) (C : CanonicalChain S)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (hseed : S₀.budgetD = S₀.budgetY) (V : ℕ → ℕ) (n : ℕ)
    {Xhat : Type u} {Zhat : Type v} [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier (slowIndex V n)))
    (dZ : Duplication Zhat (S.colCarrier (slowIndex V n))) :
    (D (C.lev 0) ≤ S₀.budgetY →
        (∀ i, i < slowIndex V n →
          D (C.out i) ≤ D (C.lev i) + realizedOverhead S aE q2E sE i) →
        D (dupMatrix dX dZ (C.lev (slowIndex V n))) ≤
          realizedYk S aE q2E sE auxW invT robD S₀ V n) ∧
      (D (C.lev 0) = S₀.budgetD →
        (∀ i, i < slowIndex V n →
          D (C.out i) = D (C.lev i) + realizedOverhead S aE q2E sE i + 1) →
        D (dupMatrix dX dZ (C.lev (slowIndex V n))) =
            realizedD S aE q2E sE auxW invT robD S₀ (slowIndex V n) ∧
          D (dupMatrix dX dZ (C.lev (slowIndex V n))) =
            realizedYk S aE q2E sE auxW invT robD S₀ V n + slowIndex V n) :=
  chainedKLevelGapTransfers S C aE q2E sE auxW invT robD S₀ hseed (slowIndex V n) dX dZ

/-- **The two transferred rows are exclusive at the frozen guard.**

`FinalOnlyDuplication.dupPromiseCases_exclusive` consumed by pin, now at the
chain's own level-`L(n)` matrix rather than at a free binder: at the frozen
`k = L(n) >= 1` of `14-final-consequence.tex:2633` the two transferred
conclusions cannot both hold, so a formalization that conjoined them would be
vacuous.  No arithmetic is re-proved here.

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the base state, the clock, the source size, the two duplicated
carriers and the two duplication data.  Claims no reader item. -/
theorem chainedPromiseCases_exclusive (S : FixedLevelCarriers.LevelCarrierSpec)
    (C : CanonicalChain S) (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ)
    (S₀ : LevelState) (V : ℕ → ℕ) (n : ℕ) (hk : 1 ≤ slowIndex V n)
    {Xhat : Type u} {Zhat : Type v} [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier (slowIndex V n)))
    (dZ : Duplication Zhat (S.colCarrier (slowIndex V n)))
    (hyes : D (C.lev (slowIndex V n)) ≤ realizedYk S aE q2E sE auxW invT robD S₀ V n)
    (hno : D (dupMatrix dX dZ (C.lev (slowIndex V n))) =
      realizedYk S aE q2E sE auxW invT robD S₀ V n + slowIndex V n) : False :=
  dupPromiseCases_exclusive S aE q2E sE auxW invT robD S₀ V n hk dX dZ
    (C.lev (slowIndex V n)) hyes hno

/-! ## Part 7: canonical inhabitation, non-vacuity and hypothesis consistency -/

/-- **The frozen lexicographic order on the seed row carrier `{0,1}^{q_seed}`.**

`12-iteration-specification.tex:93--98`: "finite function spaces use
lexicographic order in increasing coordinate order".  Mathlib's `Pi.Lex` order on
`Fin q -> Bool` is exactly that, read in the natural order of `Fin q` and with
`false < true`; it is transported to the bare function space, which is the type
`eq:full-cube-seed` (label line 29) gives the seed's rows.

This is the one place in the module where the frozen recursive order is supplied
rather than taken as a binder, and it is supplied because Part 7 is a fidelity
claim about the paper's own instance.  Scaffolding elsewhere: it is a local
instance and is not exported. -/
@[reducible] noncomputable def seedRowOrder (b : ℕ) :
    LinearOrder (Fin (FixedLevelCarriers.qSeed b) → Bool) :=
  (inferInstance : LinearOrder (Lex (Fin (FixedLevelCarriers.qSeed b) → Bool)))

attribute [local instance] seedRowOrder

/-- **`R_0 = Can(F_{B(n)})`, the paper's own instance of
`def:canonical-reindexing`** -- `12-iteration-specification.tex:360--368`:

> "For the intended fixed-level application, set `b_i = B(n) = E_2(n)` for every
> `i`, take `R_0 = Can(F_{B(n)})`, `m_0 = |Rows(F_{B(n)})|`,
> `n_0 = |Cols(F_{B(n)})|` ..."

Every quantity is *evaluated* through the banked chain
`n -> depthB n -> aSeed -> qSeed -> (2^{q_seed}, q_seed)`: `B(n)` is
`IterationAssembly.depthB`, `F_b` is `FixedLevelCarriers.seedMatrix` at the
reified width, and the two carriers are the banked `seedMatrix_carriers`.  **No
numeral is assigned to anything.**

This is the canonical-inhabitation witness for `Can` and `IsCanonicalReindex`:
the paper's own object, at the paper's own application site, with the paper's own
carrier order.  General in the source size. -/
noncomputable def paperSeedReindexed (n : ℕ) :
    Fin (2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n)) →
      Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n)) → Bool :=
  Can (FixedLevelCarriers.seedMatrix_carriers (IterationAssembly.depthB n)).1
    (FixedLevelCarriers.seedMatrix_carriers (IterationAssembly.depthB n)).2
    (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n))

/-- **Canonical inhabitation: the paper's `R_0` satisfies the frozen typed
assertion, and its complexity is the seed's.**

The first conjunct is `12:363`'s `R_0 = Can(F_{B(n)})` in the frozen reading of
lines 127--136 -- the pointwise equation together with the two cardinality
equalities, at the paper's own carriers.  The second is
`eq:canonical-complexity-invariance` for it, which is the half of frozen line
379's two-lemma justification this module delivers.

**What this is not** (GAP-EXPOSED 1 and 5): the frozen display 374--378 also
concludes, at **line 377**,
`Lambda_3(R_0, 1, 2^{-B(n)}, 3/5) >= D_0`, by line 379's
`lem:full-cube-seed, lem:canonical-reindexing-invariance`, and that bracket
statement is **not** delivered here; nor is the budget identity
`D_0 = Y_0 = comp F_{B(n)} = a_seed + 1` of frozen line 370, since the complexity
display of `lem:full-cube-seed` is banked only at requested depth `b = 0`.

General in the source size.  Claims no reader item. -/
theorem paperSeedReindexed_isCanonical (n : ℕ) :
    IsCanonicalReindex (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n))
        (2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n))
        (FixedLevelCarriers.qSeed (IterationAssembly.depthB n))
        (paperSeedReindexed n) ∧
      D (paperSeedReindexed n)
        = D (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n)) :=
  ⟨Can_isCanonicalReindex _ _ _, canonicalReindexing_invariance _ _ _⟩

/-- **The paper's `R_0` is transported onto the specification's own level-zero
slots, and is the canonical reindexing there.**

Frozen `12:360--368` sets `m_0 = |Rows(F_{B(n)})|`, `n_0 = |Cols(F_{B(n)})|` and
`R_0 = Can(F_{B(n)})` in one breath, so under the banked
`FixedLevelCarriers.SeedAnchored` the paper's seed instance must live on the
specification's *own* level-zero slot types `[m_0] = Fin (S.rowCarrier 0)` and
`[n_0] = Fin (S.colCarrier 0)`, not merely on numerals that happen to agree with
them.  This theorem says exactly that: moving `paperSeedReindexed n` along the
two banked carrier evaluations produces a matrix on `S`'s level-zero slots that
satisfies the frozen typed assertion of lines 127--136 for `F_{B(n)}` **at the
counts `S.rowCarrier 0` and `S.colCarrier 0`**.  Unfolding `IsCanonicalReindex`,
the two existentially bound cardinality equalities are precisely
`|Rows(F_{B(n)})| = m_0` and `|Cols(F_{B(n)})| = n_0`, which is the frozen
sentence's own content.

`FixedLevelCarriers.seedAnchored_carriers` is consumed **as an input by pin**:
its two carrier equalities are the transport data appearing in the statement, and
nothing it proves is restated.  Consumers get `comp` on the transported matrix
from `isCanonicalReindex_complexity`, so no complexity conjunct is bundled here.

Statement pole: the transported matrix is *pinned*, not existentially quantified,
so there is no witness freedom at all -- and by `isCanonicalReindex_eq_Can` the
predicate forces it to be `Can` of `F_{B(n)}` at those two counts, which a
constant or arbitrary matrix on `Fin (S.rowCarrier 0) -> Fin (S.colCarrier 0)`
fails as soon as `F_{B(n)}` is nonconstant (`paperSeedReindexed_nondegenerate`
runs the carriers past one).  The three-part conclusion of the banked
`seedAnchored_carriers`, including its depth clause, is *not* re-printed.

General in the specification and the source size.  Claims no reader item. -/
theorem paperSeedReindexed_at_seedAnchored
    {S : FixedLevelCarriers.LevelCarrierSpec} {n : ℕ}
    (h : FixedLevelCarriers.SeedAnchored S n) :
    IsCanonicalReindex (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n))
      (S.rowCarrier 0) (S.colCarrier 0)
      (fun u v =>
        paperSeedReindexed n
          (Fin.cast (FixedLevelCarriers.seedAnchored_carriers h).1 u)
          (Fin.cast (FixedLevelCarriers.seedAnchored_carriers h).2.1 v)) := by
  have key : ∀ (Z : Type) [Fintype Z] [LinearOrder Z] {a c : ℕ}
      (hc : Fintype.card Z = c) (hac : a = c) (u : Fin a),
      canonEquiv Z hc (Fin.cast hac u) = canonEquiv Z (hc.trans hac.symm) u := by
    intro Z _ _ a c hc hac u
    cases hac
    rfl
  refine ⟨(FixedLevelCarriers.seedMatrix_carriers (IterationAssembly.depthB n)).1.trans
      (FixedLevelCarriers.seedAnchored_carriers h).1.symm,
    (FixedLevelCarriers.seedMatrix_carriers (IterationAssembly.depthB n)).2.trans
      (FixedLevelCarriers.seedAnchored_carriers h).2.1.symm, ?_⟩
  intro u v
  simp only [paperSeedReindexed, Can_apply]
  rw [key, key]

/-- **The paper's seed instance is nondegenerate at the frozen parameters**
(LANE-GATE 3).

`12:16--21` fixes `a_seed >= 3` least with `q_seed = 2^{a_seed} - 2 >= 64(b+1)`,
so at the scheduled depth `B(n)` the two carriers of `R_0` are at least
`2^{64(B(n)+1)}` and `64(B(n)+1)` -- in particular both exceed one, and the
canonical reindexing of Part 2 is applied at a genuinely many-element carrier
rather than at a point.  The bound is the banked
`FixedLevelCarriers.aSeed_spec` consumed by pin and is not re-derived.

Statement pole: an encoding that only ever instantiated `Can` at a one-element
carrier would satisfy every lemma of Parts 2 and 3 while relabelling nothing;
this rules that reading out at the paper's own application point.

General in the source size.  Claims no reader item. -/
theorem paperSeedReindexed_nondegenerate (n : ℕ) :
    64 * (IterationAssembly.depthB n + 1)
        ≤ FixedLevelCarriers.qSeed (IterationAssembly.depthB n) ∧
      1 < FixedLevelCarriers.qSeed (IterationAssembly.depthB n) ∧
      1 < 2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n) := by
  have hspec := (FixedLevelCarriers.aSeed_spec (IterationAssembly.depthB n)).2
  refine ⟨hspec, by omega, ?_⟩
  have : 2 ^ 1 ≤ 2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### The chain probe (NON-FIDELITY) -/

/-- **A nonconstant level matrix on the banked carriers**, for the chain probe.
The diagonal indicator; it is nonconstant as soon as the row carrier has two
slots, which `FixedLevelCarriers.carriers_two_le_succ` supplies above level zero.
Claims no reader item. -/
noncomputable def probeLev (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) :
    Fin (S.rowCarrier i) → Fin (S.colCarrier i) → Bool :=
  fun u v => decide ((u : ℕ) = (v : ℕ))

/-- **A `CanonicalChain` at every legal specification -- NON-FIDELITY.**

This inhabitant shows that `CanonicalChain` is not over-constrained: the three
frozen equations are simultaneously satisfiable at *every* banked
`LevelCarrierSpec`, with nonconstant level matrices.  It takes the output carrier
to be the slot type of the next level, where `Can` is the identity by
`Can_fin_id`.

**It is explicitly NOT the paper's chain** (GAP-EXPOSED 3): the paper's `R_i^+` is
the level-`i` constructor output on a tagged-sum/product/function-space carrier,
which needs the unbuilt Stage-1--4 chain.  The canonical inhabitation of
`CanonicalChain` therefore stays **REGISTERED AS DEFERRED** against `ITER-001`,
`STAGE1-001 .. WRAP-001` and `MATERIALIZE-001`, and is not silently satisfied by
this probe.  What *is* discharged at the paper's own objects is the seed equation
`R_0 = Can(F_{B(n)})` above and the successor carrier identification
`chainingStep_from_oneLevel`.

General in the specification.  Claims no reader item. -/
noncomputable def probeChain (S : FixedLevelCarriers.LevelCarrierSpec) :
    CanonicalChain S where
  Row := fun i => Fin (S.rowCarrier (i + 1))
  Col := fun i => Fin (S.colCarrier (i + 1))
  rowFintype := fun _ => inferInstance
  rowOrder := fun _ => inferInstance
  colFintype := fun _ => inferInstance
  colOrder := fun _ => inferInstance
  lev := probeLev S
  out := fun i => probeLev S (i + 1)
  rowCard := fun _ => Fintype.card_fin _
  colCard := fun _ => Fintype.card_fin _
  chain := fun _ => (Can_fin_id _ _ _).symm

/-- **The probe chain is nondegenerate at legal values** (LANE-GATE 3).

Above level zero the banked `FixedLevelCarriers.carriers_two_le_succ` gives at
least two row slots and at least two column slots, and the probe's level matrix
separates them: it is not a constant matrix, so the chain is not inhabited only
at a degenerate point.  The chaining equation of the probe is nevertheless the
identity relabelling, which is why the probe is NON-FIDELITY and the paper's own
chain stays owed.

General in the specification and the level.  Claims no reader item. -/
theorem probeChain_nondegenerate (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) :
    ∃ u u' : Fin (S.rowCarrier (i + 1)), ∃ v : Fin (S.colCarrier (i + 1)),
      (probeChain S).lev (i + 1) u v ≠ (probeChain S).lev (i + 1) u' v := by
  obtain ⟨hrow, hcol⟩ := FixedLevelCarriers.carriers_two_le_succ S i
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩, ?_⟩
  simp [probeChain, probeLev]

/-! ### Hypothesis consistency

`chainedKLevelGapTransfers` keeps the two rows of `eq:k-level-gap` as separate
implications, and `chainedPromiseCases_exclusive` shows that conjoining the two
*transferred conclusions* at `k = L(n) >= 1` derives `False`.  A gate that stopped
there would leave the opposite danger untested: an implication whose antecedent
is never satisfiable is vacuously true.  This part answers that in the kernel, at
the frozen `k = 0` reading. -/

/-- **Both antecedents of `chainedKLevelGapTransfers` are simultaneously
satisfiable at the paper's own zero-level point, and both conclusions then hold.**

Frozen `12-iteration-specification.tex:320--323`: "For `k = 0`, the family indexed
by `0 <= i < k` is empty: no public record, parameter record, trace, or
constructor call is required.  All conclusions reduce to their stated hypotheses
at `R_0`, the sums are empty, and the additive gap is zero."  This theorem is that
paragraph: at `k = 0` the two per-level clauses are vacuous -- which is precisely
what the frozen bound `i < k` buys, and what a global `∀ i` would have destroyed --
and the two seed conditions are compatible, so neither implication of
`chainedKLevelGapTransfers` is vacuously true.

**No value is invented.**  The base state is the paper's own
`SuccessorMajorant.seedState n scales` with exactly the two budget slots the
frozen `NO` hypothesis `comp R_0 = D_0` (line 287) determines overwritten by
`comp R_0`; every other slot -- the two logarithmic side lengths, the depth, the
public scales -- is the banked seed value, unchanged.  `D_0 = Y_0` (frozen line
299) then holds by construction.  The frozen budget identity of line 370 is
**not** claimed (GAP-EXPOSED 5); this instance runs at the frozen theorem's own
generality, where clause F2 quantifies `D_i`, `Y_i` freely.

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the source size, the public scale list, the two duplicated
carriers and the two duplication data.  Claims no reader item. -/
theorem chainedFold_hypotheses_consistent (S : FixedLevelCarriers.LevelCarrierSpec)
    (C : CanonicalChain S) (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ)
    (n : ℕ) (scales : List ℕ)
    {Xhat : Type u} {Zhat : Type v} [Fintype Xhat] [Fintype Zhat]
    (dX : Duplication Xhat (S.rowCarrier 0)) (dZ : Duplication Zhat (S.colCarrier 0)) :
    ∃ S₀ : LevelState,
      S₀ = { seedState n scales with budgetD := D (C.lev 0), budgetY := D (C.lev 0) } ∧
        S₀.budgetD = S₀.budgetY ∧
        D (C.lev 0) ≤ S₀.budgetY ∧
        D (C.lev 0) = S₀.budgetD ∧
        (∀ i, i < 0 → D (C.out i) ≤ D (C.lev i) + realizedOverhead S aE q2E sE i) ∧
        (∀ i, i < 0 →
          D (C.out i) = D (C.lev i) + realizedOverhead S aE q2E sE i + 1) ∧
        D (dupMatrix dX dZ (C.lev 0)) ≤ realizedY S aE q2E sE auxW invT robD S₀ 0 ∧
        D (dupMatrix dX dZ (C.lev 0)) = realizedD S aE q2E sE auxW invT robD S₀ 0 := by
  refine ⟨{ seedState n scales with budgetD := D (C.lev 0), budgetY := D (C.lev 0) },
    rfl, rfl, le_refl _, rfl, by omega, by omega, ?_, ?_⟩
  · obtain ⟨hy, -⟩ := chainedKLevelGapTransfers S C aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D (C.lev 0), budgetY := D (C.lev 0) }
      rfl 0 dX dZ
    exact hy (le_refl _) (by omega)
  · obtain ⟨-, hn⟩ := chainedKLevelGapTransfers S C aE q2E sE auxW invT robD
      { seedState n scales with budgetD := D (C.lev 0), budgetY := D (C.lev 0) }
      rfl 0 dX dZ
    exact (hn rfl (by omega)).1

end EthInapproximability.ParameterizedNP.IteratedCanonicalChaining
