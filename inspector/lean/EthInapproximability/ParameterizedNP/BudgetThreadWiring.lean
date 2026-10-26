import EthInapproximability.ParameterizedNP.SizeThreadWiring

/-!
# Parameterized NP route: the budget thread wired to the realized chain

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`BUDGET-THREAD-WIRING-001`**, consuming
**`ITER-001`**'s two budget ladders and **`MATERIALIZE-001`**'s realized chain by
pin, and reading the shared-chain bridge banked by **`SIZE-THREAD-WIRING-001`**.

`SizeThreadWiring.lean` wired `step:I-07`'s *size* family to the realized chain.
This module is its **budget companion**: `step:I-03`'s two recursions and the
`k = 0`-safe closed form of `thm:fixed-level-gap-size` (i) become theorems about
the banked `SuccessorMajorant.LevelState.budgetY` / `.budgetD` slots of the same
chain.  **No record is introduced**: the two readouts are projections of the
banked state, and every ladder is the banked `IterationAssembly.budgetY` /
`.budgetD` consumed by pin, never a second definition of it.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module traces

Opened first-hand this tranche.

`12-iteration-specification.tex`, `thm:fixed-level-gap-size` (label line 191),
clause F3's tail at `:234--240` (`eq:iterated-budgets`, label line 239):

```
 Require also the budget updates
   Y_{i+1} = Y_i + H_i,      D_{i+1} = D_i + H_i + 1.        (12:234--240)
```

the same theorem's conclusion (i), `:244--253`
(`eq:fixed-level-closed-budgets`, label line 251):

```
 For every j with 0 <= j <= k, with an empty sum when j = 0,
   Y_j = Y_0 + sum_{i=0}^{j-1} H_i,
   D_j = D_0 + sum_{i=0}^{j-1}(H_i + 1) = D_0 + sum_{i=0}^{j-1} H_i + j.
 If D_0 = Y_0, then D_j = Y_j + j for every such j.           (12:244--253)
```

and the theorem's own `k = 0` paragraph, `:320--323`:

```
 For k = 0, the family indexed by 0 <= i < k is empty: no public record,
 parameter record, trace, or constructor call is required.  All conclusions
 reduce to their stated hypotheses at R_0, the sums are empty, and the
 additive gap is zero.                                        (12:320--323)
```

`14-final-consequence.tex`, the realization record, clause (c) at `:1636--1652`:

```
 ... and the literal updates
   Y_{i+1} = Y_i + H_i,   D_{i+1} = D_i + H_i + 1,   b_i = b_{i+1} = B(n).
 In particular, the output record has explicit fields k and Y_k, which the
 final branch decision parses.                                (14:1643--1652)
```

together with clause (a) at `:1617--1620`, "`D_0 = Y_0 = comp F_{B(n)}`, and the
positive depth `b_0 = B(n) > 0`, **including when `k = 0`**".  The two budget
displays `12:236--238` and `14:1645--1647` are the **same two equations**; this
module transcribes them once and cites both.

The supporting displays are opened at their own anchors, never recalled:

1. `13-iteration-assembly.tex:327--394`, `step:I-03` (label line 327): the
   one-based arrow dictionary at `:336--347`, the overhead
   `H_i = a_i + log_2 q_{2,i} + log_2 s_i + log_2 q_i + log_2 Q_i`
   (`expi:E-03-overhead`, label line 360), the closed forms `expi:E-03-closed`
   (label line 385) in one-based form, and the reconciliation sentence at
   `:388--393` -- "Equivalently, if arrows are numbered from zero and
   `Htilde_i = H_{i+1}`, the same transition reads `Y_{i+1} = Y_i + Htilde_i`,
   `D_{i+1} = D_i + Htilde_i + 1`".  Banked as
   `IterationAssembly.budgetY` / `.budgetD`, `.iterationBudgetLadder`,
   `.iterationClosedBudgets`, `.kLevelAdditiveGap`; consumed by pin.
2. `13-iteration-assembly.tex:786--790`, the seed budget row
   `D_0 = Y_0 = a + 1 <= b + 1 < 130 b < E_3(n)` -- banked as
   `PaddingAndClock.seedBudgetRow` and evaluated into
   `SuccessorMajorant.seedState`'s two budget slots.
3. `13-iteration-assembly.tex:521`, `step:I-07`'s **own** guard "Suppose
   `k >= 1` and `n >= n_val(k)`" -- quoted here only to keep it *out* of this
   module; see **N2** below.

**N1 (the two index conventions).**  `12:236--238` is zero-based
(`conv:finite-slots`); `13:379--386` prints the same ladders one-based and
`13:388--393` reconciles them.  The banked `IterationAssembly.budgetY` /
`.budgetD` are the zero-based transcription and `.budgetY_arrowDictionary` is the
reconciliation; nothing here re-opens either.  `realizedY ... i` is the budget
**before** the Lean arrow from level `i` to level `i + 1`, the same convention
`EffectiveMaterialization.realizedOverhead` uses for `H_i` and
`SizeThreadWiring.levelArrow` uses for the size arrow.

**N2 (the two guard scopes, kept distinct and neither globalized).**
`13:521` guards `step:I-07`'s *driver* by `k >= 1` and `n >= n_val(k)`;
`12:244` guards nothing at all -- it says "for every `j` with `0 <= j <= k`,
with an empty sum when `j = 0`", and `12:320--323` spells the `k = 0` case out.
So:

* this module states the closed form with **no** level-count hypothesis, which
  is the frozen scope, and `realizedBudgets_at_zero_levels` exhibits the
  boundary case the frozen paragraph names;
* nothing here weakens or re-uses `13:521`.  `zeroLevel_safety_is_not_globalized`
  records the converse direction: the `k = 0` equation is a boundary case and
  does **not** extend to a claim about any arrow, because the `D`-ladder moves
  strictly at every level -- even at zero overhead, by the frozen `+1`.

## What lands

* `realizedY`, `realizedD` -- the frozen `Y_i` and `D_i` of `12:236--238`, no
  longer binders: they are the banked `LevelState.budgetY` / `.budgetD` read at
  `EffectiveMaterialization.realizedState`.  **No new record**: both are plain
  projections of the banked state, and neither carries an envelope, complexity,
  robustness or promise field.
* `realizedBudgetRecursions` -- `12:235--240` = `14:1644--1648` at the realized
  chain, both updates by `rfl`, so the recursions are the construction's own
  transition and not a parallel definition of it.
* `realizedBudgets_closed` -- `eq:fixed-level-closed-budgets` (`12:246--251`) at
  the realized chain, **`k = 0`-safe**: stated for every `j`, with the empty sum
  at `j = 0`, and with no level-count hypothesis anywhere.
* `realizedBudgets_gap` -- the frozen consequence of `12:253`, `D_j = Y_j + j`
  under the printed seed identity `D_0 = Y_0`, by pin.
* `realizedBudgets_at_zero_levels` -- the frozen `12:320--323` paragraph and
  `14:1620`'s "including when `k = 0`": empty sums, both budgets at the base, and
  additive gap zero.
* `realizedBudgets_are_the_shared_chain_readout` -- the budgets are read from the
  **same** realized chain as the size thread, by pin through the banked
  `SizeThreadWiring.sizeThread_and_budgetThread_share_one_chain`, never
  re-derived from the size side and never re-deriving it.
* `realizedBudgets_at_seed` -- the seed base by pin: at the banked
  `SuccessorMajorant.seedState` the two budgets are the frozen
  `D_0 = Y_0 = a_seed(n) + 1` of `13:786--790`, so the seed identity is
  **discharged** rather than assumed and both the closed form and the exact gap
  fire with no budget hypothesis at all.
* `realizedBudgets_fire_at_paperCarrierSpec` -- the canonical firing: the whole
  budget thread at the banked `CoefficientTraversal.paperCarrierSpec` and at the
  paper's own base state, with the ladder **moving**.
* Three statement poles: `zeroLevel_safety_is_not_globalized`,
  `gap_needs_the_seed_identity`, `budgetThread_reads_the_source_exponents`.

## DEFINED-vs-FREE

* **DEFINED, reified and evaluated, never assigned a numeral:** `Y_i`, `D_i`
  (`12:236--238`, evaluated as the realized chain's own two budget slots);
  `H_i` (`expi:E-03-overhead`, banked `EffectiveMaterialization.realizedOverhead`
  through `OneLevelCompletion.levelOverhead`); `q_i = 2^{A_wrap,i L_{P,i}^2}` and
  `Q_i = 2^{r_{Q,i}}` inside `H_i` (banked `LevelCarrierSpec.qExp`,
  `EffectiveMaterialization.outerExp`); `D_0 = Y_0 = a_seed(n) + 1`
  (`13:789`, banked `PaddingAndClock.aSeed` through
  `SuccessorMajorant.seedState`); the base state itself (banked `seedState`).
* **FREE in the paper itself, therefore binders:** the Stage-1 exponent `a_i` and
  the two source exponents `log_2 q_{2,i}`, `log_2 s_i`, which come from the
  pre-family traversal (`14:1878--1889`) and the guarded source and are
  `PARAM-001` / `STAGE2-001`; the emission `Cert_c` and hence the three `AuxOut`
  list families, inherited unchanged from `MATERIALIZE-001`'s GAP-EXPOSED 1 --
  which `realizedBudgets_ignore_the_emission_binders` shows do not reach the
  budget thread either; the public scale list, which the frozen base sentence
  does not supply (`SuccessorMajorant`'s GAP-EXPOSED 4).

Note the deliberate asymmetry with the size thread, exhibited in the kernel by
`budgetThread_reads_the_source_exponents`: above level zero the size family
ignores `a_i`, `log_2 q_{2,i}` and `log_2 s_i`
(`SizeThreadWiring.realizedZ_succ_ignores_the_emission_binders`), but the budget
family does **not** -- they are summands of `H_i`.  So `PARAM-001`'s debt reaches
the budget thread where it did not reach the size thread, and that is recorded
rather than left to be inferred.

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate read in place.

**No reader item is claimed by this module.**

* `05-iteration.tex:121--122` -- `thm:paper-finite-iteration`'s own scope clause,
  "Fix `k >= 0`, and fix any public sequence of `k` legal calls to the one-level
  amplifier" -- was the single candidate `realizedBudgets_at_zero_levels` could
  have claimed, and it is **declined**: the item is **already assigned** to
  `FixedLevelCarriers.LevelCarrierSpec` under ledger row
  `FIXED-LEVEL-CARRIERS-001` (crosswalk row 12), whose reader column records it
  as claimed "by `LevelCarrierSpec` and by **nothing else**".  **Correction
  (records-only repair, `cc-t3p`).**  This tranche's first sweep asserted the
  item was previously unassigned; that assertion was false, and it is withdrawn
  here, in the declaration docstring, in the `BUDGET-THREAD-WIRING-001` ledger
  row and in crosswalk row 6.  The sweep missed the owner because it grepped only
  for citations of the shape `05-iteration.tex:NNN`, whereas `FixedLevelCarriers`
  writes the claim as "`thm:paper-finite-iteration` (label line 120)
  **hypothesis lines 121--122 only**", carrying the line numbers without the
  filename prefix.  The corrected sweep of every module under
  `src/EthInapproximability/ParameterizedNP/`, over **both** spellings, returns
  `:109` (`OneLevelCompletion`), `:116` (`IterationAssembly.budgetY` and
  `.iterationBudgetLadder`; declined by `EffectiveMaterialization`),
  `:129--133` (`IterationAssembly.iterationClosedBudgets`; declined by
  `EffectiveMaterialization`), `:137` and `:143` (`IterationAssembly`), the label
  line `120` (`FixedLevelCarriers`, `OneLevelCompletion`, `IterationAssembly` --
  as the *theorem label*), and **`121--122` itself, owned by
  `FixedLevelCarriers.LevelCarrierSpec`**.  Nothing is assigned twice.
  Independently of ownership, the reader states the `k = 0` admission as the
  theorem's quantifier only, whereas the consequences
  `realizedBudgets_at_zero_levels` actually delivers -- empty sums, both budgets
  at the base, additive gap zero -- are printed in the **paper** at
  `12:320--323` and in the realization record at `14:1620`, which are that
  declaration's anchors and remain unaffected by this withdrawal.

**No other declaration claims a reader item either, and the reason is
recorded.**  `eq:paper-budget-update` (label line 116, display lines 112--117) is
**already assigned** to `IterationAssembly.budgetY` and
`.iterationBudgetLadder`, so `realizedBudgetRecursions` claims nothing and
consumes that endpoint by pin.  The closed-form display `05-iteration.tex:129--133`
is already assigned to `IterationAssembly.iterationClosedBudgets`, so
`realizedBudgets_closed` and `realizedBudgets_at_seed` claim nothing; `:137` and
`:143` are already assigned to `IterationAssembly`.  The seed budget row
`13:786--790` has **no** reader counterpart at all: `PaddingAndClock`'s header
already records that the reader "gives the seed constants without the `a >= 4`,
`a <= b`, ceiling-identity or `130 E_2(n) < E_3(n)` derivations", and
`05-iteration.tex:278--280` (the enveloping sentence) is already assigned to
`SuccessorMajorant.seedState_underEnvelope`.

Crosswalk: no new row and **no new assignment**; the existing row **6,
"Simultaneous parameters and size"**, of `READER_CROSSWALK.md` records this
module's landing and the declined item above.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is a
  transcription of a frozen display, a general property of that transcription, or
  a composition of banked results.  No communication-complexity lemma is
  introduced, adapted or re-proved, and no banked module is edited.
* Consumed by pin, never restated: `IterationAssembly.budgetY`, `.budgetD`,
  `.budgetY_zero`, `.budgetY_succ`, `.budgetD_zero`, `.budgetD_succ`,
  `.budget_closed_forms`, `.kLevelAdditiveGap`;
  `EffectiveMaterialization.realizedState`, `.realizedOverhead`,
  `.realizedOverhead_eq`, `.realizedState_budgets`, `.realizedState_gap`,
  `.outerExp`;
  `SuccessorMajorant.LevelState`, `.seedState`;
  `PaddingAndClock.aSeed`, `.aSeed_bounds`;
  `FixedLevelCarriers.LevelCarrierSpec`, `.qExp`;
  `CoefficientTraversal.paperCarrierSpec`;
  `SizeThreadWiring.sizeThread_and_budgetThread_share_one_chain`,
  `.realizedZ`;
  `OneLevelAssembly.sideExponent`.
* Imports: `SizeThreadWiring` only, hence transitively
  `EffectiveMaterialization`, `SuccessorComposition`, `CoefficientTraversal`,
  `EnvelopeRealization`, `SuccessorMajorant`, `SizePropagation`,
  `FixedLevelCarriers`, `IterationAssembly`, `OneLevelCompletion`,
  `OneLevelAssembly`, `ParameterSchedule`, `PaddingAndClock`, `EntryGates` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  **`LegacyNPCC.Stage12` is not imported**, so no
  declaration reaches the cited AGHP balanced-family axiom and no opt-in ledger
  note is owed; `EXPANDER-001` has no contact with this module.
* External adapters: none.  No new `axiom`, no opaque certificate.
* Axiom surface (Appendix D, and `#print axioms`): at most `propext`,
  `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **No new structure.**  This module introduces no record and no premise bundle.
  `realizedY` and `realizedD` are projections of the banked
  `SuccessorMajorant.LevelState`, so no field can be added to the paper's own
  state, and nothing restates a derived telescope: the closed form is a
  *theorem* about the two ladders, never a field.
* **The desired conclusions stay out of the data.**  Neither readout carries an
  envelope, complexity, robustness or promise field; every bound and every
  closed form satisfied by them is a theorem about them.
* **Both interlace widths stay distinct.**  They enter this module only inside
  `H_i`, through the banked `realizedOverhead`, whose two width arguments are
  `LevelCarrierSpec.qExp` and `EffectiveMaterialization.outerExp` in that fixed
  order.  This module neither merges nor reorders them -- and, as
  `EffectiveMaterialization.realizedOverhead_reads_both_widths_separately`
  already records, `H_i` is a *sum* and is therefore **not** where the two widths
  are told apart; no pole here claims otherwise.
* **Every comparison is transcribed as printed.**  `12:236--238` and
  `14:1645--1647` are **equalities** and are transcribed as equalities;
  `12:253`'s consequence is an equality under the printed seed identity and is
  transcribed with that identity as an explicit hypothesis, not globalized.
* **Guard scopes.**  See **N2**: the `k = 0`-safe closed form carries no
  level-count hypothesis, `step:I-07`'s `k >= 1` driver guard is not imported,
  and neither is exported to the other thread.
* **Statement poles.**  `gap_needs_the_seed_identity` shows `D_j = Y_j + j` is
  not free of `D_0 = Y_0`; `zeroLevel_safety_is_not_globalized` shows the
  `k = 0` equation is a boundary case and not the general one;
  `budgetThread_reads_the_source_exponents` shows the budget thread genuinely
  reads `PARAM-001`'s free exponents, in explicit contrast with the size thread.

## GAP-EXPOSED

1. **`PARAM-001`'s free exponents reach this thread.**  `H_i` contains `a_i`,
   `log_2 q_{2,i}` and `log_2 s_i`, which the pre-family traversal of
   `14:1878--1889` computes and which have no Lean declaration.  They are
   level-indexed binders here, exactly as in `MATERIALIZE-001`, and
   `budgetThread_reads_the_source_exponents` records in the kernel that they are
   not inert.  Nothing below asserts a numerical value for any of them.
2. **The closed form is about the realized chain's own slots.**  As in
   `SIZE-THREAD-WIRING-001`'s GAP-EXPOSED 2, canonical reindexing
   (`lem:canonical-reindexing-invariance`) has no Lean declaration; the frozen
   `13:373--374` sentence "This transport changes neither carrier cardinality nor
   any budget or depth field" is what makes the budget slots insensitive to it,
   and `MATERIALIZE-001`'s index convention carries that.  The invariance lemma
   remains owed by `ITER-001`.
3. **The canonical inhabitation of the whole thread with every input built is
   registered, not discharged.**  `realizedBudgets_fire_at_paperCarrierSpec`
   fires the ladder at the paper's own carrier specification and at the paper's
   own base state; but supplying `a_i`, `log_2 q_{2,i}`, `log_2 s_i` from the
   traversal is `PARAM-001`, and supplying the specification's level-`i`
   reservoir data from level `i`'s own output is `STAGE1-001 .. WRAP-001`.
   Until those land, the fully-instantiated budget thread is a **deferred**
   obligation on the `BUDGET-THREAD-WIRING-001` row.
4. **The padding hook and the runtime tail are out of scope.**  `step:I-11`'s
   final duplication (`12:307--317`), `Y_k`'s consumption by the final branch
   decision (`14:1651--1652`), `A_realize`, `A_materialize`, the descriptor
   codec, the padding maps and `eq:materializer-exact-runtime` have no Lean
   declaration; per the standing gap-and-size-first priority the budget side
   lands and the padding and machine layers do not.  No route completion is
   claimed.
-/

namespace EthInapproximability.ParameterizedNP.BudgetThreadWiring

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.EffectiveMaterialization
open EthInapproximability.ParameterizedNP.SizeThreadWiring

/-! ## Part 1: the two budget families of `step:I-03`, instantiated -/

/-- **`Y_i`, the frozen public robustness budget of
`12-iteration-specification.tex:236` (= `14-final-consequence.tex:1645`), read
off the realized chain.**

`MATERIALIZE-001` builds the chain whose state slot `budgetY` **is** the literal
update `Y_{i+1} = Y_i + H_i` at the evaluated overhead; this projection turns the
binder `Y_i` of clause F2 into that slot.  No record is introduced: this is the
banked `SuccessorMajorant.LevelState.budgetY`.

Reader counterpart: **none claimed** for this definition; `eq:paper-budget-update`
(`05-iteration.tex`, label line 116) is already assigned to
`IterationAssembly.budgetY`.  General in the specification, the three exponent
families, the three `AuxOut` families, the base state and the level. -/
noncomputable def realizedY (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (i : ℕ) : ℕ :=
  (realizedState S aE q2E sE auxW invT robD S₀ i).budgetY

/-- **`D_i`, the frozen public complexity budget of
`12-iteration-specification.tex:238` (= `14-final-consequence.tex:1647`), read
off the realized chain.**

The companion projection.  The trailing `+ 1` of `D_{i+1} = D_i + H_i + 1` is the
raw Stage-4 one-bit gap and is the *only* asymmetry between the two ladders --
which is what makes the additive separation after `k` levels exactly `k`.

Reader counterpart: **none claimed**; see `realizedY`.  General in the same
arguments. -/
noncomputable def realizedD (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (i : ℕ) : ℕ :=
  (realizedState S aE q2E sE auxW invT robD S₀ i).budgetD

/-! ## Part 2: the aux-lemma battery

Seven general properties.  None is about a pinned instance: each quantifies over
arbitrary specifications, exponent families, `AuxOut` families, base states and
levels. -/

/-- **Aux 1 (both budgets at the base are the base state's own slots).**

Definitional, and recorded because it is what lets the frozen seed identity
`D_0 = Y_0` of `12:253` and `14:1619` be stated about the paper's base state
rather than about a numeral.  General. -/
theorem realizedBudgets_zero (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) :
    realizedY S aE q2E sE auxW invT robD S₀ 0 = S₀.budgetY ∧
      realizedD S aE q2E sE auxW invT robD S₀ 0 = S₀.budgetD := ⟨rfl, rfl⟩

/-- **Aux 2 (`Y_{i+1} = Y_i + H_i` at the realized chain).**

`12-iteration-specification.tex:236` = `14-final-consequence.tex:1645`, by
`rfl`.  That it holds by `rfl` is the point: the frozen update is the realized
chain's own transition and not a second recursion laid beside it.  General. -/
theorem realizedY_succ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedY S aE q2E sE auxW invT robD S₀ (i + 1) =
      realizedY S aE q2E sE auxW invT robD S₀ i + realizedOverhead S aE q2E sE i :=
  rfl

/-- **Aux 3 (`D_{i+1} = D_i + H_i + 1` at the realized chain).**

`12-iteration-specification.tex:238` = `14-final-consequence.tex:1647`, by
`rfl`, with the frozen `+ 1` transcribed exactly where it is printed.
General. -/
theorem realizedD_succ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedD S aE q2E sE auxW invT robD S₀ (i + 1) =
      realizedD S aE q2E sE auxW invT robD S₀ i +
        realizedOverhead S aE q2E sE i + 1 :=
  rfl

/-- **Aux 4 (the two readouts are the banked ladders, not new recursions).**

The round-trip property: at every level the two state slots are exactly
`IterationAssembly.budgetY` and `.budgetD` of the base budgets at the overhead
sequence `H_i = realizedOverhead`.  Consumes the banked
`EffectiveMaterialization.realizedState_budgets` by pin, so `step:I-03`'s ladders
are *evaluated* here and never restated.  General. -/
theorem realizedBudgets_are_the_banked_ladders
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedY S aE q2E sE auxW invT robD S₀ i =
        budgetY S₀.budgetY (realizedOverhead S aE q2E sE) i ∧
      realizedD S aE q2E sE auxW invT robD S₀ i =
        budgetD S₀.budgetD (realizedOverhead S aE q2E sE) i :=
  realizedState_budgets S aE q2E sE auxW invT robD S₀ i

/-- **Aux 5 (the emission binders do not reach the budget thread either).**

`MATERIALIZE-001` carries `AuxOut(Cert_c)` as three level-indexed list binders
(its GAP-EXPOSED 1).  None of the three occurs in either budget family at any
level: the two slots are pure functions of the base budgets and the overhead
sequence.  So the unbuilt emission is not a hidden input to `step:I-03`.

This is the *budget* analogue of
`SizeThreadWiring.realizedZ_succ_ignores_the_emission_binders`; the exponent
families are deliberately **not** included here, and
`budgetThread_reads_the_source_exponents` below shows why they could not be.
General in both sets of data and the level. -/
theorem realizedBudgets_ignore_the_emission_binders
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD auxW' invT' robD' : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedY S aE q2E sE auxW invT robD S₀ i =
        realizedY S aE q2E sE auxW' invT' robD' S₀ i ∧
      realizedD S aE q2E sE auxW invT robD S₀ i =
        realizedD S aE q2E sE auxW' invT' robD' S₀ i := by
  obtain ⟨hY, hD⟩ := realizedState_budgets S aE q2E sE auxW invT robD S₀ i
  obtain ⟨hY', hD'⟩ := realizedState_budgets S aE q2E sE auxW' invT' robD' S₀ i
  exact ⟨hY.trans hY'.symm, hD.trans hD'.symm⟩

/-- **Aux 6 (both ladders are monotone, and the `D`-ladder gains at least one per
level).**

`Y` is nondecreasing because every summand `H_i` is a natural number, and `D`
gains at least `d` over `d` levels because of the frozen `+ 1` of `12:238`.  This
is the property that makes the closed forms usable at a level *count* rather than
only at a fixed index, and it is stated at an arbitrary starting level and an
arbitrary number of further levels, not at the pinned ones.  General. -/
theorem realizedBudgets_monotone (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (i d : ℕ) :
    realizedY S aE q2E sE auxW invT robD S₀ i ≤
        realizedY S aE q2E sE auxW invT robD S₀ (i + d) ∧
      realizedD S aE q2E sE auxW invT robD S₀ i + d ≤
        realizedD S aE q2E sE auxW invT robD S₀ (i + d) := by
  induction d with
  | zero => simp
  | succ m ih =>
    obtain ⟨hY, hD⟩ := ih
    have hstep : i + (m + 1) = i + m + 1 := by omega
    rw [hstep]
    have h1 := realizedY_succ S aE q2E sE auxW invT robD S₀ (i + m)
    have h2 := realizedD_succ S aE q2E sE auxW invT robD S₀ (i + m)
    omega

/-- **Aux 7 (the two ladders differ by the base offset plus the level, without
natural subtraction).**

The frozen proof at `12:328--329` says "subtracting the two closed forms gives
`D_j - Y_j = (D_0 - Y_0) + j`".  Over `ℕ` that subtraction is not total, so the
same content is recorded in its subtraction-free form -- which is *stronger*, in
that it holds at every base pair rather than only when `Y_0 <= D_0`.  General. -/
theorem realizedD_add_base_budgetY (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (j : ℕ) :
    realizedD S aE q2E sE auxW invT robD S₀ j + S₀.budgetY =
      realizedY S aE q2E sE auxW invT robD S₀ j + S₀.budgetD + j := by
  obtain ⟨hY, hD⟩ := realizedState_budgets S aE q2E sE auxW invT robD S₀ j
  obtain ⟨hYc, hDc⟩ :=
    budget_closed_forms S₀.budgetY S₀.budgetD (realizedOverhead S aE q2E sE) j
  have hY' : realizedY S aE q2E sE auxW invT robD S₀ j =
      S₀.budgetY + ∑ i ∈ Finset.range j, realizedOverhead S aE q2E sE i :=
    hY.trans hYc
  have hD' : realizedD S aE q2E sE auxW invT robD S₀ j =
      S₀.budgetD + (∑ i ∈ Finset.range j, realizedOverhead S aE q2E sE i) + j :=
    hD.trans hDc
  omega

/-! ## Part 3: the two recursions and the `k = 0`-safe closed form -/

/-- **`eq:iterated-budgets` at the realized chain**
(`12-iteration-specification.tex`, label line 239, display lines 235--240; the
same two equations at `14-final-consequence.tex:1644--1648`).

```
 Y_{i+1} = Y_i + H_i,      D_{i+1} = D_i + H_i + 1.
```

Both updates hold at the realized chain by `rfl`, with `H_i` the *evaluated*
`EffectiveMaterialization.realizedOverhead`, i.e. the five-term sum
`a_i + log_2 q_{2,i} + log_2 s_i + log_2 q_i + log_2 Q_i` of
`expi:E-03-overhead` (`13:358--361`).  The third conjunct records that the two
ladders are the banked ones, so nothing here is a second definition of
`step:I-03`.

See **N1** in the module header for the two frozen index conventions.

Reader counterpart: **none claimed**; `eq:paper-budget-update`
(`05-iteration.tex`, label line 116, display lines 112--117) is already assigned
to `IterationAssembly.budgetY` and `.iterationBudgetLadder`.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level. -/
theorem realizedBudgetRecursions (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedY S aE q2E sE auxW invT robD S₀ (i + 1) =
        realizedY S aE q2E sE auxW invT robD S₀ i +
          realizedOverhead S aE q2E sE i ∧
      realizedD S aE q2E sE auxW invT robD S₀ (i + 1) =
        realizedD S aE q2E sE auxW invT robD S₀ i +
          realizedOverhead S aE q2E sE i + 1 ∧
      realizedOverhead S aE q2E sE i =
        aE i + q2E i + sE i + S.qExp i + outerExp S i :=
  ⟨realizedY_succ S aE q2E sE auxW invT robD S₀ i,
    realizedD_succ S aE q2E sE auxW invT robD S₀ i,
    realizedOverhead_eq S aE q2E sE i⟩

/-- **`eq:fixed-level-closed-budgets` at the realized chain, `k = 0`-safe**
(`12-iteration-specification.tex`, label line 251, display lines 246--251, with
the scope sentence at lines 244--245).

```
 For every j with 0 <= j <= k, with an empty sum when j = 0,
   Y_j = Y_0 + sum_{i=0}^{j-1} H_i,
   D_j = D_0 + sum_{i=0}^{j-1}(H_i + 1) = D_0 + sum_{i=0}^{j-1} H_i + j.
```

The frozen display prints **two** right-hand sides for `D_j` (lines 249--250);
the Lean statement below transcribes the second, already-simplified one, and the
two are equal over `ℕ` by `Finset.sum_add_distrib` and `Finset.sum_const`.

Stated for **every** `j`, with no level-count hypothesis at all -- which is the
frozen scope: `12:244` guards nothing, and `12:320--323` spells the `j = k = 0`
case out.  `step:I-07`'s `k >= 1` driver guard (`13:521`) is a different
statement's guard and is deliberately not imported here; see **N2** in the module
header.

The proof is the banked `IterationAssembly.budget_closed_forms` fed the realized
chain, so `step:I-03`'s induction is consumed by pin and not re-run.

Reader counterpart: **none claimed**; the closed-form display
`05-iteration.tex:129--133` is already assigned to
`IterationAssembly.iterationClosedBudgets`.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level. -/
theorem realizedBudgets_closed (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (j : ℕ) :
    realizedY S aE q2E sE auxW invT robD S₀ j =
        S₀.budgetY + ∑ i ∈ Finset.range j, realizedOverhead S aE q2E sE i ∧
      realizedD S aE q2E sE auxW invT robD S₀ j =
        S₀.budgetD + (∑ i ∈ Finset.range j, realizedOverhead S aE q2E sE i)
          + j := by
  obtain ⟨hY, hD⟩ := realizedState_budgets S aE q2E sE auxW invT robD S₀ j
  obtain ⟨hYc, hDc⟩ :=
    budget_closed_forms S₀.budgetY S₀.budgetD (realizedOverhead S aE q2E sE) j
  exact ⟨hY.trans hYc, hD.trans hDc⟩

/-- **The frozen consequence of `12-iteration-specification.tex:253`:
`D_j = Y_j + j` under the printed seed identity.**

Frozen text: "If `D_0 = Y_0`, then `D_j = Y_j + j` for every such `j`."  The
seed identity is an **explicit hypothesis**, exactly as printed, and is never
globalized: `gap_needs_the_seed_identity` below shows the conclusion fails
without it.  Consumes the banked `EffectiveMaterialization.realizedState_gap`,
hence `IterationAssembly.kLevelAdditiveGap`, by pin.

Reader counterpart: **none claimed**; `05-iteration.tex:129--133` and `:143` are
already assigned to `IterationAssembly`.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level, under the frozen base identity. -/
theorem realizedBudgets_gap (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (hbase : S₀.budgetD = S₀.budgetY) (j : ℕ) :
    realizedD S aE q2E sE auxW invT robD S₀ j =
      realizedY S aE q2E sE auxW invT robD S₀ j + j :=
  (realizedState_gap S aE q2E sE auxW invT robD S₀ hbase j).2

/-- **The frozen `k = 0` paragraph, `12-iteration-specification.tex:320--323`.**

Frozen text: "For `k = 0`, the family indexed by `0 <= i < k` is empty: no public
record, parameter record, trace, or constructor call is required.  All
conclusions reduce to their stated hypotheses at `R_0`, the sums are empty, and
the additive gap is zero."  The realization record says the same on its own side
at `14:1617--1620`: clause (a) supplies `D_0 = Y_0` and the positive depth
"including when `k = 0`".

All four printed consequences are delivered: the sum is empty, each budget
reduces to its base slot, and the additive gap is zero under the printed seed
identity.  No arrow datum -- no overhead value, no exponent, no carrier count --
occurs in the statement, which is the frozen "no constructor call is required".

Reader counterpart: **none claimed**.  `05-iteration.tex:121--122`,
`thm:paper-finite-iteration`'s scope clause "Fix `k >= 0`, and fix any public
sequence of `k` legal calls to the one-level amplifier", is already assigned to
`FixedLevelCarriers.LevelCarrierSpec` under ledger row
`FIXED-LEVEL-CARRIERS-001` (crosswalk row 12).  See the module header for the
withdrawal of this tranche's earlier claim and for the corrected sweep.  The
anchors above -- `12:320--323` and `14:1617--1620` -- are unaffected.

General in the specification, the three exponent families, the three `AuxOut`
families and the base state. -/
theorem realizedBudgets_at_zero_levels (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) :
    (∑ i ∈ Finset.range 0, realizedOverhead S aE q2E sE i) = 0 ∧
      realizedY S aE q2E sE auxW invT robD S₀ 0 = S₀.budgetY ∧
      realizedD S aE q2E sE auxW invT robD S₀ 0 = S₀.budgetD ∧
      (S₀.budgetD = S₀.budgetY →
        realizedD S aE q2E sE auxW invT robD S₀ 0 =
          realizedY S aE q2E sE auxW invT robD S₀ 0 + 0) := by
  refine ⟨Finset.sum_range_zero _, rfl, rfl, ?_⟩
  intro hbase
  exact realizedBudgets_gap S aE q2E sE auxW invT robD S₀ hbase 0

/-! ## Part 4: one chain, two threads -/

/-- **The budgets are read from the same realized chain as the size thread.**

`14:1644--1648` updates the two budgets and `eq:fixed-level-carriers`
(`12:260--265`) updates the two carriers along the **same** realized arrow, so
`step:I-03`'s ladders and `step:I-07`'s size majorant are not two parallel
inductions but two projections of `EffectiveMaterialization.realizedState`.

Consumed **by pin** from the banked
`SizeThreadWiring.sizeThread_and_budgetThread_share_one_chain`: no budget is
re-derived from the size side and no size fact is re-derived from the budget
side.  A consumer must read this as the licence to use both threads at one index
without a compatibility hypothesis.

Reader counterpart: **none claimed**; the shared-chain fact has no reader
display, and both endpoint families are already assigned to
`IterationAssembly`.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level. -/
theorem realizedBudgets_are_the_shared_chain_readout
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedZ S aE q2E sE auxW invT robD S₀ (i + 1) =
        sideExponent (S.rowCarrier (i + 1)) (S.colCarrier (i + 1)) ∧
      realizedY S aE q2E sE auxW invT robD S₀ i =
        budgetY S₀.budgetY (realizedOverhead S aE q2E sE) i ∧
      realizedD S aE q2E sE auxW invT robD S₀ i =
        budgetD S₀.budgetD (realizedOverhead S aE q2E sE) i :=
  sizeThread_and_budgetThread_share_one_chain S aE q2E sE auxW invT robD S₀ i

/-! ## Part 5: the seed base, by pin -/

/-- **`13-iteration-assembly.tex:786--790` at the realized chain: the seed
identity is discharged, not assumed.**

Frozen text: "The seed budget also lies below the base majorant, because
`D_0 = Y_0 = a + 1 <= b + 1 < 130 b < E_3(n)`", and clause (a) of the realization
record prints the same identity as `D_0 = Y_0 = comp F_{B(n)}` (`14:1619`).  At
the banked `SuccessorMajorant.seedState` -- the paper's own base state, whose two
budget slots *are* `a_seed(n) + 1` -- the identity `D_0 = Y_0` therefore holds by
`rfl`, so both the closed form of `12:246--251` and the exact gap of `12:253`
fire here **with no budget hypothesis at all**.

The third conjunct is what keeps the firing from being a renaming: the frozen
`a_seed(n) >= 4` of `13:751` (banked `PaddingAndClock.aSeed_bounds`) forces both
base budgets to be at least `5`, so the base is not the degenerate all-zero
state.  The fifth conjunct is `12:253` at the paper's base.

Reader counterpart: **none claimed**; `05-iteration.tex:278--280` (the
enveloping sentence for the seed budgets) is already assigned to
`SuccessorMajorant.seedState_underEnvelope`, and the reader prints no seed budget
identity of its own.

General in `n >= 1`, the specification, the three exponent families, the three
`AuxOut` families, the public scale list and the level. -/
theorem realizedBudgets_at_seed (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (n : ℕ) (hn : 1 ≤ n)
    (scales : List ℕ) (j : ℕ) :
    realizedY S aE q2E sE auxW invT robD (seedState n scales) 0 =
        PaddingAndClock.aSeed n + 1 ∧
      realizedD S aE q2E sE auxW invT robD (seedState n scales) 0 =
        PaddingAndClock.aSeed n + 1 ∧
      4 ≤ PaddingAndClock.aSeed n ∧
      realizedY S aE q2E sE auxW invT robD (seedState n scales) j =
        PaddingAndClock.aSeed n + 1 +
          ∑ i ∈ Finset.range j, realizedOverhead S aE q2E sE i ∧
      realizedD S aE q2E sE auxW invT robD (seedState n scales) j =
        realizedY S aE q2E sE auxW invT robD (seedState n scales) j + j := by
  refine ⟨rfl, rfl, (PaddingAndClock.aSeed_bounds n hn).1, ?_, ?_⟩
  · exact (realizedBudgets_closed S aE q2E sE auxW invT robD
      (seedState n scales) j).1
  · exact realizedBudgets_gap S aE q2E sE auxW invT robD (seedState n scales)
      rfl j

/-- **Canonical inhabitation: the whole budget thread at the paper's own carrier
specification and the paper's own base state.**

`CoefficientTraversal.paperCarrierSpec` is the banked specification in which
every schedule field is the paper's own evaluated value, and
`SuccessorMajorant.seedState` is the paper's own base state of `13:786--790`.
Firing the ladder there is the fidelity test the canonical-inhabitation rule
demands: the object the thread runs on is the paper's, not a stand-in that
happens to satisfy the guards.

Three conjuncts carry the content.  The closed form and the exact gap hold at the
paper's data with the seed identity discharged; and the ladder **moves** --
`D_j < D_{j+1}` at every level, by the frozen `+ 1` of `12:238` alone, so the
statement is not about a constant sequence.

This is **not** a discharge of the fully-instantiated obligation: the three
exponent families are still `PARAM-001` binders and the specification's
level-`i` reservoir data is still `STAGE1-001 .. WRAP-001`.  See GAP-EXPOSED 3.

Reader counterpart: **none claimed**; the reader prints no carrier
specification.

General in the Section-8 data, the schedule inputs, the exponent families, the
`AuxOut` families, the public scale list, `n >= 1` and the level. -/
theorem realizedBudgets_fire_at_paperCarrierSpec
    (F : FiniteSlots.Stage1SlotBinding) {q : ℕ} {V X L₂ Y : Type*} [Fintype V]
    [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y)
    (v₀ : V) (x₀ : X) (l₀ : L₂) (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ)
    (dv zeta : ℝ) (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ)
    (hn : 1 ≤ n) (scales : List ℕ) (j : ℕ) :
    realizedY (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
          Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
        (seedState n scales) j =
        PaddingAndClock.aSeed n + 1 +
          ∑ i ∈ Finset.range j,
            realizedOverhead (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀
              x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE i ∧
      realizedD (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
          Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
        (seedState n scales) j =
        realizedY (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0
          B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
          (seedState n scales) j + j ∧
      realizedD (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
          Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
        (seedState n scales) j <
        realizedD (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0
          B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
          (seedState n scales) (j + 1) := by
  set S := CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
    Ccert sPar lq2 clU0 zR dv zeta with hS
  obtain ⟨-, -, -, hclosed, hgap⟩ :=
    realizedBudgets_at_seed S aE q2E sE auxW invT robD n hn scales j
  refine ⟨hclosed, hgap, ?_⟩
  have hstep := realizedD_succ S aE q2E sE auxW invT robD (seedState n scales) j
  omega

/-! ## Part 6: statement poles -/

/-- **Statement pole: the `k = 0` equation is a boundary case and is not
globalized.**

`realizedBudgets_at_zero_levels` delivers the frozen `12:320--323` content at the
level count `13:521`'s guard excludes.  A reader could mistake that for a claim
that the budgets are insensitive to the level count, so the opposite fact is
exhibited: at **every** level the complexity ladder moves strictly, and it moves
even when the overhead vanishes, because of the frozen `+ 1` of `12:238`.  So the
`k = 0` equation cannot be extended to any arrow, and the `k = 0` safety of the
closed form is not a statement about the thread being constant.

The third conjunct is deliberately weak, and is recorded as such so that it is
not over-read.  Its kernel content is the closed numeral fact `¬ (1 <= 0)`: it
mentions no guard, no driver and no `k`, and it is **not** a statement about
`step:I-07`, whose guard this module does not import.  What it pins is only the
arithmetic reason the two scopes cannot be merged -- the `k >= 1` of `13:521`
fails at `k = 0`, the very level count at which the frozen budget clause
`12:244` is stated.  The content of this declaration is carried by the first two
conjuncts.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level. -/
theorem zeroLevel_safety_is_not_globalized
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedD S aE q2E sE auxW invT robD S₀ i <
        realizedD S aE q2E sE auxW invT robD S₀ (i + 1) ∧
      (realizedOverhead S aE q2E sE i = 0 →
        realizedD S aE q2E sE auxW invT robD S₀ (i + 1) =
          realizedD S aE q2E sE auxW invT robD S₀ i + 1) ∧
      ¬ (1 ≤ (0 : ℕ)) := by
  have hstep := realizedD_succ S aE q2E sE auxW invT robD S₀ i
  refine ⟨by omega, ?_, by omega⟩
  intro h0
  omega

/-- **Statement pole: the exact gap genuinely needs the frozen seed identity.**

`12:253` states `D_j = Y_j + j` **only** under `D_0 = Y_0`, and a formalization
that dropped that hypothesis would still typecheck at every instance where it
happens to hold.  So the failure is exhibited: whenever the base pair is strictly
ordered the conclusion is already false at `j = 0`, before any arrow is run.
This is also the trivial-witness check for `realizedBudgets_gap`: the conclusion
is not satisfied by an arbitrary base state, so the hypothesis is not free.

General in the specification, the three exponent families, the three `AuxOut`
families and the base state. -/
theorem gap_needs_the_seed_identity (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (h : S₀.budgetY < S₀.budgetD) :
    realizedY S aE q2E sE auxW invT robD S₀ 0 + 0 <
      realizedD S aE q2E sE auxW invT robD S₀ 0 := by
  obtain ⟨hY, hD⟩ := realizedBudgets_zero S aE q2E sE auxW invT robD S₀
  omega

/-- **Statement pole: the budget thread reads `PARAM-001`'s free exponents, and
the size thread does not.**

`SizeThreadWiring.realizedZ_succ_ignores_the_emission_binders` shows that above
level zero the *size* family is a pure function of the carrier specification: the
three source-exponent families drop out.  A reader could carry that over to the
budgets, which would be wrong -- `a_i`, `log_2 q_{2,i}` and `log_2 s_i` are three
of the five summands of `H_i` (`expi:E-03-overhead`, `13:358--361`), so they
enter every level of both ladders.

The obstruction is exhibited at the cheapest possible perturbation: raising the
Stage-1 exponent family by one raises the robustness budget by at least the level
index, at **every** specification, every base state and every level.  Hence no
analogue of `realizedZ_succ_ignores_the_emission_binders` can hold here, and
`PARAM-001`'s debt reaches this thread (GAP-EXPOSED 1).

**The two constant families `fun _ => 0` and `fun _ => 1` claim no legality.**
Neither is a legal Stage-1 exponent family -- `13:353` fixes the trace identity
`q_{1,i} = 2^{a_i} - 2` and `13:751` gives `a >= 4` -- and neither is a parameter
assignment of any kind.  They are a *perturbation*, exhibited only to show that
the budget thread is not inert in `a_i`, in exactly the sense in which
`FixedLevelCarriers.seedAnchor_is_not_automatic` is a rejection probe claiming
no legality.  The statement is universally quantified in `S`, `q2E`, `sE`, `S₀`
and `i`, and asserts nothing whatever about the paper's own values.

General in the specification, the two remaining exponent families, the three
`AuxOut` families, the base state and the level. -/
theorem budgetThread_reads_the_source_exponents
    (S : FixedLevelCarriers.LevelCarrierSpec) (q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedY S (fun _ => 0) q2E sE auxW invT robD S₀ i + i ≤
      realizedY S (fun _ => 1) q2E sE auxW invT robD S₀ i := by
  induction i with
  | zero =>
    have z0 : realizedY S (fun _ => 0) q2E sE auxW invT robD S₀ 0 = S₀.budgetY :=
      (realizedBudgets_zero S (fun _ => 0) q2E sE auxW invT robD S₀).1
    have z1 : realizedY S (fun _ => 1) q2E sE auxW invT robD S₀ 0 = S₀.budgetY :=
      (realizedBudgets_zero S (fun _ => 1) q2E sE auxW invT robD S₀).1
    omega
  | succ m ih =>
    have h0 := realizedY_succ S (fun _ => 0) q2E sE auxW invT robD S₀ m
    have h1 := realizedY_succ S (fun _ => 1) q2E sE auxW invT robD S₀ m
    have e : realizedOverhead S (fun _ => 1) q2E sE m =
        realizedOverhead S (fun _ => 0) q2E sE m + 1 := by
      simp only [realizedOverhead_eq]
      omega
    omega

end EthInapproximability.ParameterizedNP.BudgetThreadWiring
