import EthInapproximability.ParameterizedNP.BudgetThreadWiring
import EthInapproximability.ParameterizedNP.EffectiveMain

/-!
# Parameterized NP route: the depth thread and the two parsed output fields

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`DEPTH-THREAD-WIRING-001`**, consuming
**`ITER-001`**'s `step:I-04` depth thread, **`MATERIALIZE-001`**'s realized
chain, **`BUDGET-THREAD-WIRING-001`**'s two budget readouts, the banked
shared-chain bridge of **`SIZE-THREAD-WIRING-001`**, and **`CLOCK-001`** /
**`EFFECTIVE-MAIN-001`**'s branch-decision deliverables -- every one of them
**by pin**, none restated.

`SizeThreadWiring.lean` wired `step:I-07`'s size family to the realized chain and
`BudgetThreadWiring.lean` wired `step:I-03`'s two budget ladders to the same
chain.  This module is the **third and last** projection of clause (c) of the
realization record: the constant-depth slot `b_i = b_{i+1} = B(n)` of
`14:1649`, together with the two explicit output fields `k` and `Y_k` of
`14:1651--1652` that the final branch decision parses.  **No record is
introduced**: the depth readout is a projection of the banked
`SuccessorMajorant.LevelState`, and `Y_k` is the banked budget ladder evaluated
at the banked clock index.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module traces

Opened first-hand this tranche.

`14-final-consequence.tex`, `thm:effective-materialization` (label line 1548),
clause (a) at `:1617--1620`:

```
 (a) k = L(n), the seed R_0 = Can(F_{B(n)}), its canonical carrier
 equivalences, D_0 = Y_0 = comp F_{B(n)}, and the positive depth
 b_0 = B(n) > 0, including when k = 0.                       (14:1617--1620)
```

the same theorem's clause (c) at `:1636--1652`, whose **last** display and whose
closing sentence are this module's two deliverables:

```
 For every 0 <= i < k, the exact cross-level public-record equation
   Public_i = (N_V, N_E, d_0, d_1, m_i, n_i, R_i,
               gamma_eps, Delta_eps, D_i, Y_i, B(n), B(n)),   (14:1636--1640)
 ... and the literal updates
   Y_{i+1} = Y_i + H_i,   D_{i+1} = D_i + H_i + 1,   b_i = b_{i+1} = B(n).
                                                             (14:1644--1649)
 In particular, the output record has explicit fields k and Y_k,
 which the final branch decision parses.                     (14:1651--1652)
```

The supporting displays are opened at their own anchors, never recalled:

1. `13-iteration-assembly.tex:407--428`, `step:I-04` ("Constant depth thread:
   the depth thread is constant in value: every outgoing depth is exactly the
   incoming depth of the next level"), whose three loci are the schedule choice
   `beta_i = B(n) = E_2(n) = 2^{l(n)^2}` for `i >= 0` at `:414`, the **two
   distinct guard scopes** at `:418--419`

   ```
    b_0 = beta_{i-1} = B(n),      b^+ = beta_i = B(n).       (13:418--419)
   ```

   and the interface sentence at `:421--428`, "Since `beta_i = beta_{i+1} =
   B(n)`, the output certificate of level `i` has exactly the depth used as the
   input certificate of level `i+1`.  No density-monotonicity conversion and no
   rounding of the exponent occurs at this interface. ... `B(n) >= 2^9 = 512`,
   in particular `B(n) >= 1`."  Banked as `IterationAssembly.depthB`,
   `.depthB_ge`, `.depthThread_constant`, `.depthThread_pole`, consumed here by
   pin.
2. `13-iteration-assembly.tex:396--405`, the level-independence sentence: "The
   original variable count `n`, the reduced source graph, the universal
   constants (including `mu_P`), and the common depth `B(n)` are
   level-independent.  The matrix `R_{i-1}`, the budgets `D_{i-1}, Y_{i-1}`, and
   their logarithmic side-length majorant change with the level."
3. `12-iteration-specification.tex:360--370`, the fixed-level application site
   ("set `b_i = B(n) = E_2(n)` for every `i`"), banked as
   `FixedLevelCarriers.SeedAnchored` and realized by
   `FixedLevelCarriers.paperSeedSpec` / `CoefficientTraversal.paperCarrierSpec`.
4. `12-iteration-specification.tex:502--553`, `cor:realized-effective-prefix`
   (label line 503): clause (b)'s `b_0 = B(n) > 0` at `:525`, clause (c)'s public
   record with **two** depth slots `(..., B(n), B(n))` at `:534`, and clause
   (d)'s literal depth identities `b_i = b_{i+1} = B(n)` at `:546--548` -- the
   specification-side counterpart of `14:1649`.
5. `12-iteration-specification.tex:299--306`, `eq:k-level-gap` (label line 305):
   `YES: comp R_k <= Y_k`, `NO: comp R_k = D_k = Y_k + k`, under the frozen
   `D_0 = Y_0`.  Banked as `IterationAssembly.kLevelAdditiveGap` and reached here
   through `BudgetThreadWiring.realizedBudgets_at_seed`.
6. `14-final-consequence.tex:2622--2654`, the branch controller: "Run
   `A_realize`, parse its data record `D(n,G)` and explicit fields `k = L(n)` and
   `Y_k` ... put `k = L(n)`, `A = alpha(T_n)` ... Thus comparing the integer `2z`
   with `2Y_k + k` decides whether this branch is satisfiable."  The arithmetic
   is banked as `EffectiveMain.branchSeparation_holds` /
   `.branchComparisonDecides` at a **free** budget binder `Y`; this module
   supplies that binder from the realized chain.

**N1 (the two guard scopes, and why they stay distinct).**  Two different pairs
of guards meet here and neither may be merged into the other.

*Record scopes.*  `13:418--419` distinguishes the **incoming** depth `b_0` of a
level from its **requested outgoing** depth `b^+`.  In Lean these live in two
different banked records: the incoming common depth is the state slot
`SuccessorMajorant.LevelState.depth`, and the requested outgoing depth is the
specification field `FixedLevelCarriers.LevelCarrierSpec.bout`, which the outer
bridge width `Q_i` is computed from.  Nothing definitional ties them: the chain's
depth slot is transported from the base state by
`SuccessorOutputs.nextState` and never reads `bout`, and
`depthInterface_is_not_definitional` exhibits a legal-guard specification at
which the two genuinely disagree.  Their agreement is exactly the frozen
schedule choice `12:360` = `13:414`, imported here as
`FixedLevelCarriers.SeedAnchored` and never as a silent identification.

*Level-count scopes.*  Clause (a)'s depth row holds "including when `k = 0`"
(`14:1620`), so every depth statement below is unconditional in the level count.
The branch decision, by contrast, is guarded by `L(n) >= 1` (`14:2633`), which is
also `AlphaAllowance.alphaGapFit`'s guard.  `guardScopes_stay_distinct` exhibits
a legal source size at which the depth thread fires in full while the branch
guard fails, so neither guard is globalized onto the other.

**N2 (the two promise cases are cases, never a conjunction).**  `eq:k-level-gap`
prints `YES` and `NO` as the two cases of one construction.  They enter
`realizedFieldsDecideTheBranch` as the guarded binders `hyes`/`hno` exactly as in
the banked `EffectiveMain.comparisonDecides`, and
`realizedFields_promiseCases_exclusive` records in the kernel that conjoining
them at `k >= 1` would be vacuous.

**N3 (`k` is consumed, not redefined).**  `k = L(n)` is the banked
`PaddingAndClock.slowIndex`, reified from `eq:L-clock` under `CLOCK-001`.  No
alias for it is introduced here: an alias would be a second name for a banked
definition and would restate a derived telescope.  Only `Y_k` gets a definition,
because it is a **composite** of two banked deliverables (the budget ladder and
the clock) that the frozen record stores as one field.

## What lands

* `realizedDepth` -- the frozen `b_i` of `14:1649` and `12:546--548`, no longer a
  binder: it is the banked `SuccessorMajorant.LevelState.depth` read at
  `EffectiveMaterialization.realizedState`.  `realizedDepth_succ` is the literal
  frozen equation `b_i = b_{i+1}`, and it holds by `rfl`, which is the point --
  the constant thread is the realized chain's own transition, not a second
  recursion laid beside it.
* `realizedDepth_at_seed` -- the `= B(n)` half, at the paper's own base state
  `SuccessorMajorant.seedState`, together with the frozen `B(n) >= 512 >= 1` of
  `13:427--428`.  Nothing is assumed: the base state's depth slot **is**
  `IterationAssembly.depthB n`.
* `realizedDepthInterface` -- `13:418--419` and `13:421--428` at the realized
  chain, with the two record scopes kept distinct: the incoming depth at level
  `i`, the requested outgoing depth of arrow `i`, and the incoming depth at level
  `i + 1` are the same integer, the two requested densities coincide, and the
  frozen floors hold.  The last four conjuncts are the banked
  `IterationAssembly.depthThread_constant` consumed by pin.
* `depthThread_shares_the_realized_chain` -- the depth readout, the size readout
  and the two budget readouts are **four projections of one**
  `EffectiveMaterialization.realizedState`, by pin from
  `BudgetThreadWiring.realizedBudgets_are_the_shared_chain_readout`.
* `realizedYk` -- the frozen output field `Y_k` of `14:1651`: the banked budget
  ladder `BudgetThreadWiring.realizedY` evaluated at the banked clock index
  `PaddingAndClock.slowIndex V n`.  `realizedYk_is_the_banked_ladder` is the
  round trip onto `IterationAssembly.budgetY`.
* `realizedFields_at_seed` -- both parsed fields at the paper's own base state:
  `Y_k` in the evaluated closed form of `eq:fixed-level-closed-budgets`, the
  `NO`-row identity `D_k = Y_k + k` of `eq:k-level-gap` with the seed identity
  **discharged** rather than assumed, and the depth still `B(n)` at the final
  index.
* `realizedFieldsDecideTheBranch` -- `14:2653` with **both** parsed fields
  realized: the banked `EffectiveMain.branchComparisonDecides` at
  `Y := realizedYk` and `k := slowIndex V n`.  This is the declaration that
  closes the `Y_k`-consumption clause of item (4) of the
  `BUDGET-THREAD-WIRING-001` gap list -- that item's clause "`Y_k`'s consumption
  by the final branch decision (`14:1651--1652`)".  `step:I-11`'s final
  duplication (`12:307--317`), `A_realize`, `A_materialize`, the descriptor
  codec, the padding maps and `eq:materializer-exact-runtime` **remain open on
  that item**, whose title is "The padding hook and the runtime tail are out of
  scope"; see GAP-EXPOSED 3.
* `depthThread_fires_at_paperCarrierSpec` -- the canonical-inhabitation firing at
  the banked `CoefficientTraversal.paperCarrierSpec` (whose `bout` is the
  paper's own `B(n)`) and the paper's own base state.
* `realizedFieldsDecideTheBranch_fires` -- the decision is genuinely two-valued
  at the realized field: the `YES` instantiation is accepted and the `NO`
  instantiation is rejected, both obtained by *running* the deliverable.

## GAP-EXPOSED (this module claims none of the following)

1. **`PARAM-001`'s three exponent families remain binders.**  They do not reach
   the depth thread at all -- `realizedDepth_ignores_every_arrow_datum` proves
   that in the kernel -- but they are three of the five summands of `H_i` and so
   they do reach `Y_k` through the budget ladder, exactly as
   `BudgetThreadWiring.budgetThread_reads_the_source_exponents` records.
2. **`lem:canonical-reindexing-invariance` is still not in Lean.**  The frozen
   `13:373--374` sentence "This transport changes neither carrier cardinality nor
   any budget or depth field" is what makes the depth slot insensitive to the
   canonical transport; the invariance lemma stays owed by `ITER-001`.
3. **The machine layer is absent.**  `A_realize`, the descriptor codec, the
   parse functions `parse_real` / `parse_{0,1}`, `A_materialize`,
   `eq:effective-entry-agreement`, `eq:materializer-output-position` and the
   runtime tail have **no** Lean declaration.  In particular "the output record
   has explicit fields" is modelled here as *the two integers the decision
   consumes are the realized chain's own*, not as a statement about a serialized
   record; the serialization obligation stays registered.
4. **Canonical inhabitation of the fully-instantiated thread is REGISTERED AS
   DEFERRED.**  `depthThread_fires_at_paperCarrierSpec` runs the thread at the
   paper's own specification and base state, but the specification's level-`i`
   reservoir data is still `STAGE1-001 .. WRAP-001` and the exponent families are
   still `PARAM-001` binders.
5. **`z` and `sat` stay binders.**  The signed estimate `z` of `14:2639` is the
   parser output of the unmodelled `A_app`, and `sat` is the branch predicate; as
   in the banked `EffectiveMain`, both are universally quantified and no
   approximation algorithm is modelled.  No route completion is claimed.

## Reader counterparts

Exactly **one** reader item is claimed by this module, by
`realizedDepthInterface`: `05-iteration.tex` lines **206--211**,
`thm:paper-effective-level`'s scope sentence "Let the source graph arise from an
`n`-variable branch of `thm:paper-sparse-gap-source`, and use the common
scheduled robustness depth" together with its display `b_0 = b^+ = B(n)` at line
210.  That display is the reader's statement of the **two guard scopes** of
`13:418--419` -- incoming `b_0` and requested outgoing `b^+`, both `B(n)` -- and
it is the fact `realizedDepthInterface` states level by level.  A sweep of every
module under `src/EthInapproximability/ParameterizedNP/` for `05-iteration.tex`
line citations returns `:26--44`, `:34--38`, `:96--100`, `:97`, `:99`, `:101`,
`:109`, `:121--122`, `:129--133`, `:137`, `:143`, `:157--167`, `:176`, `:178`,
`:192`, `:194--196`, `:201--204`, `:212--215`, `:221--226`, `:226--229`, `:228`,
`:240--246`, `:245--246`, `:247--248`, `:272`, `:273--277`, `:278--280`,
`:280--283`, `:281`, `:289`, `:298`, `:308--310` and `:349--351`; **`:206--211`
occurs in none of them**, so no reader line is assigned twice.  The banked
`SuccessorComposition` module's own sweep records the same gap independently:
"no other claimed row meets the interval `205--220` at all".  The alternative
prefix-free spelling that the `cc-t3p` verify seat found (line numbers carried
without the filename, as `FixedLevelCarriers` writes `121--122`) was swept as
well, over `205`--`212`, and returns only `06-parameter-schedule.tex:206--211`
(`eq:eta-choice`'s first line, `ParameterSchedule.etaC`),
`12-iteration-specification.tex:205--211` (`LevelCarrierSpec.bout`'s own
docstring), `07-one-level-construction.tex:206--215` and `09:205--218` -- four
different section files, none of them the reader.

Every other declaration claims **no** reader item, and the reasons are recorded
here rather than repeated in each docstring:

* `05-iteration.tex:272`, "Use the common requested depth `b_i = B(n)` at the
  seed and at every level", is **already assigned** to
  `IterationAssembly.depthB` and `.depthThread_constant`;
* `05-iteration.tex:188`, `B(n) = E_2(n)`, sits inside `eq:paper-envelope`
  (label line 189), already assigned to `IterationAssembly.ellN` / `.envE`;
* the reader's `YES`/`NO` display at `06-eth.tex:428--434` and its closing
  sentence at `:435--436` are **proof-internal** loci inside
  `prop:paper-eth-consequence`, and `EffectiveMain`'s ledger row already records
  that this tranche family treats proof-internal loci as navigation and never
  cites prose as a statement;
* the reader prints no carrier specification, no realization record and no
  parsed output field, so `realizedYk`, `realizedFields_at_seed` and the two
  probes have no reader locus at all.
-/

namespace EthInapproximability.ParameterizedNP.DepthThread

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.AlphaAllowance
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.EffectiveMaterialization
open EthInapproximability.ParameterizedNP.SizeThreadWiring
open EthInapproximability.ParameterizedNP.BudgetThreadWiring
open EthInapproximability.ParameterizedNP.EffectiveMain

/-! ## Part 1: the two readouts clause (c) still owed -/

/-- **`b_i`, the frozen common depth of `14:1649` (= `12:546--548`), read off the
realized chain.**

`MATERIALIZE-001` builds the chain whose transition
`SuccessorMajorant.SuccessorOutputs.nextState` copies the incoming depth slot
unchanged; this projection turns the binder `b_i` of `cor:realized-effective-prefix`
clause (d) into that slot.  No record is introduced: this is the banked
`SuccessorMajorant.LevelState.depth`.

Reader counterpart: **none claimed** for this definition; see the module header.
General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level. -/
noncomputable def realizedDepth (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (i : ℕ) : ℕ :=
  (realizedState S aE q2E sE auxW invT robD S₀ i).depth

/-- **`Y_k`, the frozen parsed output field of `14:1651` (= `14:2624`), read off
the realized chain.**

The record stores one integer; in Lean it is the composite of **two** banked
deliverables, taken by pin and never redefined: the budget ladder
`BudgetThreadWiring.realizedY` and the clock index
`PaddingAndClock.slowIndex V n`, which is `k = L(n)` (`14:1617`, `14:2635`).
Reading note N3 records why `k` itself gets no alias.

Reader counterpart: **none claimed**; the reader prints no realization record.
General in the specification, the three exponent families, the three `AuxOut`
families, the base state, the clock and the source size. -/
noncomputable def realizedYk (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (V : ℕ → ℕ) (n : ℕ) : ℕ :=
  realizedY S aE q2E sE auxW invT robD S₀ (slowIndex V n)

/-! ## Part 2: the aux-lemma battery

Five general properties.  None is about a pinned instance: each quantifies over
arbitrary specifications, exponent families, `AuxOut` families, base states,
clocks, source sizes and levels. -/

/-- **Aux 1 (the depth at the base is the base state's own slot).**

Definitional, and recorded because it is what lets clause (a)'s frozen
`b_0 = B(n) > 0` (`14:1619--1620`) be stated about the paper's base state rather
than about a numeral.  General. -/
theorem realizedDepth_zero (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) :
    realizedDepth S aE q2E sE auxW invT robD S₀ 0 = S₀.depth := rfl

/-- **Aux 2 (`b_i = b_{i+1}` at the realized chain).**

`14-final-consequence.tex:1649` = `12-iteration-specification.tex:546--548`, by
`rfl`.  That it holds by `rfl` is the point: the frozen identity is the realized
chain's own transition -- `SuccessorOutputs.nextState` copies the depth slot --
and not a second recursion laid beside it.  General. -/
theorem realizedDepth_succ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedDepth S aE q2E sE auxW invT robD S₀ i =
      realizedDepth S aE q2E sE auxW invT robD S₀ (i + 1) := rfl

/-- **Aux 3 (the depth readout is the base slot at every level).**

`13-iteration-assembly.tex:396--405`, "the common depth `B(n)` [is]
level-independent", read off the whole chain.  Consumes the banked
`EffectiveMaterialization.realizedState_depth` by pin, so the induction is
evaluated here and never restated.  General. -/
theorem realizedDepth_const (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedDepth S aE q2E sE auxW invT robD S₀ i = S₀.depth :=
  realizedState_depth S aE q2E sE auxW invT robD S₀ i

/-- **Aux 4 (no arrow datum whatsoever reaches the depth thread).**

The sharp form of `13:396--405`: the depth readout is a function of the base
state **alone**.  Neither the carrier specification, nor `PARAM-001`'s three
exponent families, nor `MATERIALIZE-001`'s three `AuxOut` list binders, nor even
the level index occurs in it.

This is strictly stronger than the size and budget analogues --
`SizeThreadWiring.realizedZ_succ_ignores_the_emission_binders` drops only the
three emission binders, and
`BudgetThreadWiring.budgetThread_reads_the_source_exponents` shows the budget
thread cannot drop the exponents at all.  It is also what makes the depth
statements below unconditional in the level count, as `14:1620` demands.
General in both sets of data and both levels. -/
theorem realizedDepth_ignores_every_arrow_datum
    (S S' : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE aE' q2E' sE' : ℕ → ℕ)
    (auxW invT robD auxW' invT' robD' : ℕ → List ℕ) (S₀ : LevelState) (i j : ℕ) :
    realizedDepth S aE q2E sE auxW invT robD S₀ i =
      realizedDepth S' aE' q2E' sE' auxW' invT' robD' S₀ j :=
  (realizedDepth_const S aE q2E sE auxW invT robD S₀ i).trans
    (realizedDepth_const S' aE' q2E' sE' auxW' invT' robD' S₀ j).symm

/-- **Aux 5 (the parsed budget field is the banked ladder, not a new recursion).**

The round-trip property for `Y_k`: the field is exactly
`IterationAssembly.budgetY` of the base budget at the overhead sequence
`H_i = realizedOverhead`, evaluated at the clock index.  Consumes
`BudgetThreadWiring.realizedBudgets_are_the_banked_ladders` by pin, so
`step:I-03`'s ladder is *evaluated* here and never restated.  General. -/
theorem realizedYk_is_the_banked_ladder (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (V : ℕ → ℕ) (n : ℕ) :
    realizedYk S aE q2E sE auxW invT robD S₀ V n =
      budgetY S₀.budgetY (realizedOverhead S aE q2E sE) (slowIndex V n) :=
  (realizedBudgets_are_the_banked_ladders S aE q2E sE auxW invT robD S₀
    (slowIndex V n)).1

/-! ## Part 3: the depth thread at the paper's own data -/

/-- **The depth thread at the paper's base state: `b_i = B(n)`, with the frozen
floors.**

`14:1619--1620` ("the positive depth `b_0 = B(n) > 0`, including when `k = 0`")
composed with `13:427--428` ("`B(n) >= 2^9 = 512`, in particular `B(n) >= 1`").
At the banked `SuccessorMajorant.seedState` -- the paper's own base state, whose
depth slot *is* `IterationAssembly.depthB n` -- the identity holds by `rfl` at
every level, so **no depth hypothesis is taken anywhere**, and the two floors are
the banked `IterationAssembly.depthB_ge`.

The statement is deliberately unconditional in the level count: `14:1620` says
"including when `k = 0`", and `realizedDepth_ignores_every_arrow_datum` is why no
level-count guard could enter.

Reader counterpart: **none claimed**; `05-iteration.tex:272` is already assigned
to `IterationAssembly.depthB`.  General in the specification, the three exponent
families, the three `AuxOut` families, `n >= 1`, the public scale list and the
level. -/
theorem realizedDepth_at_seed (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (n : ℕ) (hn : 1 ≤ n)
    (scales : List ℕ) (i : ℕ) :
    realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i = depthB n ∧
      512 ≤ realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i ∧
      1 ≤ realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i := by
  have hd : realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i =
      depthB n := realizedDepth_const S aE q2E sE auxW invT robD (seedState n scales) i
  obtain ⟨h512, h1⟩ := depthB_ge n hn
  exact ⟨hd, by rw [hd]; exact h512, by rw [hd]; exact h1⟩

/-- **`step:I-04`'s interface at the realized chain, with the two record scopes
kept distinct.**

`13:418--419` writes the level's two depths separately -- the incoming
`b_0 = beta_{i-1}` and the requested outgoing `b^+ = beta_i` -- and `13:421--428`
then says they meet: "Since `beta_i = beta_{i+1} = B(n)`, the output certificate
of level `i` has exactly the depth used as the input certificate of level `i+1`.
No density-monotonicity conversion and no rounding of the exponent occurs at this
interface."

In Lean the two scopes are two **different banked records**, and this theorem is
the only place they are identified:

* the incoming common depth is the chain slot, `realizedDepth`;
* the requested outgoing depth of arrow `i` is the specification field
  `FixedLevelCarriers.LevelCarrierSpec.bout i`, the field the outer bridge width
  `Q_i` is computed from.

The identification is **not** definitional -- `depthInterface_is_not_definitional`
exhibits a specification satisfying every record guard at which the two disagree
-- and it is not assumed either: its input is the frozen application site
`12:360` = `13:414`, imported as the banked `FixedLevelCarriers.SeedAnchored`.
The last four conjuncts are the banked `IterationAssembly.depthThread_constant`
consumed by pin at `beta := S.bout`, so the density sentence and the two floors
are the frozen ones and not re-derived.

Reader counterpart: `05-iteration.tex:206--211`, "Let the source graph arise from
an `n`-variable branch of `thm:paper-sparse-gap-source`, and use the common
scheduled robustness depth `b_0 = b^+ = B(n)`" (display line 210).  The reader
states the two guard scopes at one level; this theorem states them at every
level of the chain.  General in the specification, the three exponent families,
the three `AuxOut` families, `n >= 1`, the public scale list and the level. -/
theorem realizedDepthInterface (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hanch : FixedLevelCarriers.SeedAnchored S n) (scales : List ℕ) (i : ℕ) :
    realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i = S.bout i ∧
      S.bout i =
        realizedDepth S aE q2E sE auxW invT robD (seedState n scales) (i + 1) ∧
      S.bout i = S.bout (i + 1) ∧
      DirectOutputLower.xOut (S.bout i) = DirectOutputLower.xOut (S.bout (i + 1)) ∧
      512 ≤ S.bout i ∧ 1 ≤ S.bout i := by
  have hbout : ∀ j, S.bout j = depthB n := fun j => congrFun hanch.1 j
  have hchain : ∀ j,
      realizedDepth S aE q2E sE auxW invT robD (seedState n scales) j = depthB n :=
    fun j => realizedDepth_const S aE q2E sE auxW invT robD (seedState n scales) j
  obtain ⟨hne, hdens, h512, h1⟩ := depthThread_constant n hn S.bout hbout i
  exact ⟨by rw [hchain i, hbout i], by rw [hbout i, hchain (i + 1)],
    hne, hdens, h512, h1⟩

/-- **One chain, four threads.**

`14:1644--1649` updates the two budgets and holds the depth fixed, and
`eq:fixed-level-carriers` (`12:260--265`) updates the two carriers, all along the
**same** realized arrow.  So `step:I-03`'s ladders, `step:I-07`'s size majorant
and `step:I-04`'s depth thread are not three parallel inductions but four
projections of `EffectiveMaterialization.realizedState`.

The first three conjuncts are the banked
`BudgetThreadWiring.realizedBudgets_are_the_shared_chain_readout` applied
unchanged; the fourth adds the depth.  A consumer must read this as the licence
to use all four threads at one index without a compatibility hypothesis.

Reader counterpart: **none claimed**; the shared-chain fact has no reader
display.  General in the specification, the three exponent families, the three
`AuxOut` families, the base state and the level. -/
theorem depthThread_shares_the_realized_chain
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedZ S aE q2E sE auxW invT robD S₀ (i + 1) =
        sideExponent (S.rowCarrier (i + 1)) (S.colCarrier (i + 1)) ∧
      realizedY S aE q2E sE auxW invT robD S₀ i =
        budgetY S₀.budgetY (realizedOverhead S aE q2E sE) i ∧
      realizedD S aE q2E sE auxW invT robD S₀ i =
        budgetD S₀.budgetD (realizedOverhead S aE q2E sE) i ∧
      realizedDepth S aE q2E sE auxW invT robD S₀ i = S₀.depth := by
  obtain ⟨hZ, hY, hD⟩ :=
    realizedBudgets_are_the_shared_chain_readout S aE q2E sE auxW invT robD S₀ i
  exact ⟨hZ, hY, hD, realizedDepth_const S aE q2E sE auxW invT robD S₀ i⟩

/-! ## Part 4: the two parsed output fields -/

/-- **Both parsed fields at the paper's own base state.**

`14:1651--1652` says the record has explicit fields `k` and `Y_k`.  Here they
are, evaluated through the banked definitional chain rather than assigned:

* `Y_k` in the closed form of `eq:fixed-level-closed-budgets` (`12:246--251`) at
  the paper's seed budget `D_0 = Y_0 = a_seed(n) + 1` (`13:786--790`, printed
  again as `14:1619`);
* the `NO`-row identity `D_k = Y_k + k` of `eq:k-level-gap` (`12:301--306`), with
  the frozen seed identity `D_0 = Y_0` **discharged** at the paper's base state
  rather than assumed;
* the depth still `B(n)` at the final index, which is the clause-(c) row this
  module wires.

Every conjunct is `BudgetThreadWiring.realizedBudgets_at_seed` or
`realizedDepth_at_seed` consumed by pin; nothing is re-derived.  The level index
is the banked clock `k = L(n)`, so this is the record the frozen controller of
`14:2623--2624` parses, not a record at an arbitrary index.

Reader counterpart: **none claimed**; `05-iteration.tex:129--133` (the reader's
closed-form display) is already assigned to
`IterationAssembly.iterationClosedBudgets` and `:143` to `.kLevelAdditiveGap`.
General in the specification, the three exponent families, the three `AuxOut`
families, the clock, `n >= 1` and the public scale list. -/
theorem realizedFields_at_seed (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (V : ℕ → ℕ) (n : ℕ)
    (hn : 1 ≤ n) (scales : List ℕ) :
    realizedYk S aE q2E sE auxW invT robD (seedState n scales) V n =
        aSeed n + 1 +
          ∑ i ∈ Finset.range (slowIndex V n), realizedOverhead S aE q2E sE i ∧
      realizedD S aE q2E sE auxW invT robD (seedState n scales) (slowIndex V n) =
        realizedYk S aE q2E sE auxW invT robD (seedState n scales) V n +
          slowIndex V n ∧
      realizedDepth S aE q2E sE auxW invT robD (seedState n scales)
          (slowIndex V n) = depthB n := by
  obtain ⟨-, -, -, hclosed, hgap⟩ :=
    realizedBudgets_at_seed S aE q2E sE auxW invT robD n hn scales (slowIndex V n)
  exact ⟨hclosed, hgap,
    (realizedDepth_at_seed S aE q2E sE auxW invT robD n hn scales
      (slowIndex V n)).1⟩

/-- **The final branch decision, with both parsed fields realized.**

`14:2653`, "Thus comparing the integer `2z` with `2Y_k + k` decides whether this
branch is satisfiable", at the frozen data `k = L(n)`, `A = alpha(T_n)` of
`14:2635--2637`.

The arithmetic is **not** re-proved: this is the banked
`EffectiveMain.branchComparisonDecides` with its free budget binder `Y`
instantiated by `realizedYk` -- the realized chain's own budget ladder at the
realized chain's own clock index -- and its frozen strictness input supplied by
`EffectiveMain.branchSeparation_holds`, i.e. by `eq:alpha-gap-fit`.  What is new
is exactly the wiring `14:1651--1652` demands: the two integers the decision
consumes are the record's fields, not binders.

The two `eq:k-level-gap` cases stay the guarded binders `hyes`/`hno` and are
never conjoined (reading note N2); `realizedFields_promiseCases_exclusive`
records why.  The frozen guard `L(n) >= 1` of `14:2633` is an explicit binder,
and reading note N1 records that it is **not** the depth thread's guard.

The trivial witness fails: the conclusion is an equivalence, and
`realizedFieldsDecideTheBranch_fires` exhibits one instantiation on which the
left-hand comparison is **true** and another on which it is **false**, so the
biconditional is not satisfied by a constantly-true or constantly-false
comparison.

Reader counterpart: **none claimed**; the reader's `06-eth.tex:428--436` locus is
proof-internal (see the module header).  General in the clock, the cutoff
function, the specification, the three exponent families, the three `AuxOut`
families, the base state, the source size, the estimate, the complexity value and
the branch predicate. -/
theorem realizedFieldsDecideTheBranch {V nstep : ℕ → ℕ}
    (hg : SlowClockGateSet V nstep) (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) {n : ℕ}
    (hk : 1 ≤ slowIndex V n) {z c : ℤ} {sat : Prop}
    (happ : |z - c| ≤ (alphaAllowance V (tCommon V n) : ℤ))
    (hyes : sat → c ≤ (realizedYk S aE q2E sE auxW invT robD S₀ V n : ℤ))
    (hno : ¬ sat → c = (realizedYk S aE q2E sE auxW invT robD S₀ V n : ℤ) +
      (slowIndex V n : ℤ)) :
    (2 * z < 2 * (realizedYk S aE q2E sE auxW invT robD S₀ V n : ℤ) +
      (slowIndex V n : ℤ)) ↔ sat :=
  branchComparisonDecides (branchSeparation_holds hg) hk happ hyes hno

/-- **The two promise cases at the realized field are exclusive.**

`eq:k-level-gap` prints `YES: comp R_k <= Y_k` and `NO: comp R_k = Y_k + k` as
the two cases of one construction.  At the frozen guard `k = L(n) >= 1` they
cannot both hold of the same complexity value, so a statement conjoining them
would be vacuous -- which is why `realizedFieldsDecideTheBranch` keeps them as
guarded binders.  Consumes the banked `EffectiveMain.promiseCasesAreExclusive`
by pin at the realized budget field.

Reader counterpart: **none claimed**.  General in the clock, the specification,
the three exponent families, the three `AuxOut` families, the base state, the
source size and the complexity value. -/
theorem realizedFields_promiseCases_exclusive
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (V : ℕ → ℕ) (n : ℕ)
    (hk : 1 ≤ slowIndex V n) {c : ℤ}
    (hyes : c ≤ (realizedYk S aE q2E sE auxW invT robD S₀ V n : ℤ))
    (hno : c = (realizedYk S aE q2E sE auxW invT robD S₀ V n : ℤ) +
      (slowIndex V n : ℤ)) : False := by
  have hk' : (1 : ℤ) ≤ (slowIndex V n : ℤ) := by exact_mod_cast hk
  exact promiseCasesAreExclusive hk' hyes hno

/-! ## Part 5: canonical inhabitation and non-vacuity -/

/-- **Canonical inhabitation: the depth thread and both parsed fields at the
paper's own carrier specification and base state.**

`CoefficientTraversal.paperCarrierSpec` is the banked specification whose
requested outgoing depth field is the paper's own `B(n)` -- it is built from
`FixedLevelCarriers.paperSeedSpec`, whose `bout` is `IterationAssembly.depthB n`
by construction -- and `SuccessorMajorant.seedState` is the paper's own base
state of `13:317--321` ("The base is literal: `n_val(0) = 1`, the seed depth is
`B(n) = E_2(n)`, and the seed size and budget are below `E_3(n) = E_{c_0}(n)`"),
whose seed budget row is `13:786--790`.  Firing there is the fidelity test the
canonical-inhabitation rule demands: the object the thread runs on is the
paper's, not a stand-in that happens to satisfy the guards.

Four conjuncts carry the content: the specification really is seed-anchored (so
the interface hypothesis is discharged, not assumed); the incoming depth, the
requested outgoing depth and the next incoming depth are one integer; that
integer is at least the frozen `512`; and the parsed budget field is the
evaluated closed form at the paper's own seed budget.

This is **not** a discharge of the fully-instantiated obligation: the three
exponent families are still `PARAM-001` binders and the specification's level-`i`
reservoir data is still `STAGE1-001 .. WRAP-001`.  See GAP-EXPOSED 4.

Reader counterpart: **none claimed**; the reader prints no carrier
specification.  General in the Section-8 data, the schedule inputs, the exponent
families, the `AuxOut` families, the clock, `n >= 1`, the public scale list and
the level. -/
theorem depthThread_fires_at_paperCarrierSpec
    (F : FiniteSlots.Stage1SlotBinding) {q : ℕ} {V₀ X L₂ Y : Type*} [Fintype V₀]
    [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y)
    (v₀ : V₀) (x₀ : X) (l₀ : L₂) (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ)
    (dv zeta : ℝ) (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ)
    (hn : 1 ≤ n) (scales : List ℕ) (V : ℕ → ℕ) (i : ℕ) :
    FixedLevelCarriers.SeedAnchored (CoefficientTraversal.paperCarrierSpec F hq hs
      y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR dv zeta) n ∧
    realizedDepth (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0
          B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
        (seedState n scales) i =
        (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert
          sPar lq2 clU0 zR dv zeta).bout i ∧
      (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert
          sPar lq2 clU0 zR dv zeta).bout i =
        realizedDepth (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n
          C0 B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
          (seedState n scales) (i + 1) ∧
      512 ≤ (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
        Ccert sPar lq2 clU0 zR dv zeta).bout i ∧
      realizedYk (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0
          B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD
        (seedState n scales) V n =
        aSeed n + 1 +
          ∑ j ∈ Finset.range (slowIndex V n),
            realizedOverhead (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀
              x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE j := by
  set S := CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert
    sPar lq2 clU0 zR dv zeta with hS
  have hanch : FixedLevelCarriers.SeedAnchored S n := ⟨rfl, rfl, rfl⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ :=
    realizedDepthInterface S aE q2E sE auxW invT robD n hn hanch scales i
  obtain ⟨hclosed, -, -⟩ :=
    realizedFields_at_seed S aE q2E sE auxW invT robD V n hn scales
  exact ⟨hanch, h1, h2, h5, hclosed⟩

/-- **Non-vacuity of `realizedFieldsDecideTheBranch`: the decision is genuinely
two-valued at the realized field** (LANE-GATE 3).

The whole hypothesis bundle is inhabited at legal parameter values, and the
deliverable is *run* twice at the same realized field:

* the `YES` instantiation (`sat := True`, estimate exact at `c = Y_k`) makes the
  frozen comparison `2z < 2Y_k + k` **true**;
* the `NO` instantiation (`sat := False`, estimate exact at `c = Y_k + k`) makes
  it **false**.

So the biconditional of `realizedFieldsDecideTheBranch` is not satisfied by a
constantly-true or constantly-false comparison, which is the trivial-witness
check that an equivalence deliverable needs.

`PaddingAndClock.witnessClock` is the banked nondegenerate inhabitant of the four
frozen clock gates and `witnessClock_reaches_positive_index` supplies a source
size at which the frozen guard `L(n) >= 1` genuinely holds; both come from
`CLOCK-001` and neither is chosen here.  The specification, the exponent
families, the `AuxOut` families and the base state stay **universally
quantified**, so no value of any of them is assigned.

General in the cutoff function, the specification, the three exponent families,
the three `AuxOut` families and the base state. -/
theorem realizedFieldsDecideTheBranch_fires (nstep : ℕ → ℕ)
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) :
    (2 * (realizedYk S aE q2E sE auxW invT robD S₀ (witnessClock nstep)
          (witnessClock nstep 1) : ℤ) <
        2 * (realizedYk S aE q2E sE auxW invT robD S₀ (witnessClock nstep)
          (witnessClock nstep 1) : ℤ) +
          (slowIndex (witnessClock nstep) (witnessClock nstep 1) : ℤ)) ∧
      ¬ (2 * ((realizedYk S aE q2E sE auxW invT robD S₀ (witnessClock nstep)
            (witnessClock nstep 1) : ℤ) +
          (slowIndex (witnessClock nstep) (witnessClock nstep 1) : ℤ)) <
        2 * (realizedYk S aE q2E sE auxW invT robD S₀ (witnessClock nstep)
          (witnessClock nstep 1) : ℤ) +
          (slowIndex (witnessClock nstep) (witnessClock nstep 1) : ℤ)) := by
  set V := witnessClock nstep with hV
  set n := witnessClock nstep 1 with hn
  set Yk := (realizedYk S aE q2E sE auxW invT robD S₀ V n : ℤ) with hYk
  have hk : 1 ≤ slowIndex V n := witnessClock_reaches_positive_index nstep
  have hg : SlowClockGateSet V nstep := witnessClock_gates nstep
  have hyes := realizedFieldsDecideTheBranch (z := Yk) (c := Yk) (sat := True)
    hg S aE q2E sE auxW invT robD S₀ hk (by simp)
    (fun _ => le_rfl) (fun h => absurd trivial h)
  have hno := realizedFieldsDecideTheBranch
    (z := Yk + (slowIndex V n : ℤ)) (c := Yk + (slowIndex V n : ℤ))
    (sat := False) hg S aE q2E sE auxW invT robD S₀ hk (by simp)
    (fun h => absurd h not_false) (fun _ => rfl)
  exact ⟨hyes.mpr trivial, fun h => hno.mp h⟩

/-! ## Part 6: statement poles -/

/-- **Statement pole: the chain's depth slot and the specification's requested
depth are two records, and their agreement is a schedule constraint.**

`realizedDepthInterface` identifies the incoming common depth with the
specification's `bout`.  A reader could take that identification for a
definitional triviality, so the failure is exhibited: the realized chain
transports the base state's depth slot and **never reads** `bout`, so at a
specification whose requested depth differs from the base state's the two are
genuinely different integers -- here `1` against `B(n) >= 512`.

That is exactly the content of the frozen schedule choice `12:360` = `13:414`:
`b_i = B(n)` is a *constraint the schedule imposes*, not a notational identity,
and dropping the `SeedAnchored` hypothesis from `realizedDepthInterface` would
make it false.

**`SizeThreadWiring.probeSpec` claims no legality.**  It is the banked
NON-FIDELITY probe: every record guard of `LevelCarrierSpec` holds, and nothing
else about it is asserted.  It is used here as a *rejection probe* in the sense
of `FixedLevelCarriers.seedAnchor_is_not_automatic`, never as a parameter
assignment.

General in the three exponent families, the three `AuxOut` families, `n >= 1`,
the public scale list and the level. -/
theorem depthInterface_is_not_definitional (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (n : ℕ) (hn : 1 ≤ n) (scales : List ℕ)
    (i : ℕ) :
    realizedDepth probeSpec aE q2E sE auxW invT robD (seedState n scales) i ≠
      probeSpec.bout i := by
  obtain ⟨-, h512, -⟩ :=
    realizedDepth_at_seed probeSpec aE q2E sE auxW invT robD n hn scales i
  have hb : probeSpec.bout i = 1 := rfl
  rw [hb]
  omega

/-- **Statement pole: the depth guard and the branch guard are different guards.**

Clause (a) states the depth row "including when `k = 0`" (`14:1620`), while the
branch decision is guarded by `L(n) >= 1` (`14:2633`).  A formalization that
merged the two would either weaken the depth thread onto the positive-clock
branch or -- far worse -- carry the branch decision onto a level count at which
`eq:alpha-gap-fit` is unavailable.

The separation is exhibited at a legal source size: at the banked witness clock
there is an `n >= 1` whose clock index is `0`, and there the depth thread still
fires in full (the readout is `B(n)`, it is at least the frozen `512`, and
`b_i = b_{i+1}`) while the branch guard **fails**.

The witness is not trivial: `n = 0` would satisfy the guard failure alone, and
the frozen `1 <= n` binder -- which `IterationAssembly.depthB_ge` needs -- excludes
it, so the banked `PaddingAndClock.slowIndex_zero_is_attained` is used precisely
because it supplies a *positive* source size on the zero branch.

General in the cutoff function, the specification, the three exponent families,
the three `AuxOut` families, the public scale list and the level. -/
theorem guardScopes_stay_distinct (nstep : ℕ → ℕ)
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (scales : List ℕ) (i : ℕ) :
    ∃ n, 1 ≤ n ∧
      realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i = depthB n ∧
      512 ≤ realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i ∧
      realizedDepth S aE q2E sE auxW invT robD (seedState n scales) i =
        realizedDepth S aE q2E sE auxW invT robD (seedState n scales) (i + 1) ∧
      ¬ (1 ≤ slowIndex (witnessClock nstep) n) := by
  obtain ⟨-, n, hn, hzero⟩ := slowIndex_zero_is_attained nstep
  obtain ⟨hd, h512, -⟩ :=
    realizedDepth_at_seed S aE q2E sE auxW invT robD n hn scales i
  exact ⟨n, hn, hd, h512,
    realizedDepth_succ S aE q2E sE auxW invT robD (seedState n scales) i,
    by omega⟩

/-- **Statement pole: the frozen threshold really reads the `Y_k` field.**

`14:2653` compares `2z` with `2Y_k + k`.  A formalization that dropped the parsed
budget field -- comparing against `k` alone, or against a constant -- would still
typecheck, so two things are recorded in the kernel.

First, the field is not inert in the construction: raising the base robustness
budget by one raises `Y_k` by exactly one, at every specification, every exponent
family, every clock and every source size.  (The base budget itself is the
paper's `a_seed(n) + 1`; the perturbation claims **no** legality and is a
rejection probe, exactly as in
`BudgetThreadWiring.budgetThread_reads_the_source_exponents`.)

Second, the comparison is not insensitive to that value: at `z = 1`, `k = 1` the
frozen comparison is **false** at `Y_k = 0` and **true** at `Y_k = 1`.  So the
threshold genuinely depends on the field, and a decision procedure that did not
parse it would decide a different predicate.  The two numeral conjuncts carrying
this second point are a **BEYOND-PAPER** sensitivity evaluation at self-chosen
`z`, `k` and `Y_k`, **not a legal parameter point**: they are free-standing
integer arithmetic, bound neither to `realizedYk` nor to `slowIndex`, they claim
no legality and inhabit no structure, and they audit the frozen comparison's
*shape* only.  The first conjunct is the rejection probe that carries the
legality-free content about the construction itself.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state, the clock and the source size. -/
theorem branchThreshold_reads_the_realized_field
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (V : ℕ → ℕ) (n : ℕ) :
    realizedYk S aE q2E sE auxW invT robD
        { S₀ with budgetY := S₀.budgetY + 1 } V n =
        realizedYk S aE q2E sE auxW invT robD S₀ V n + 1 ∧
      ¬ (2 * (1 : ℤ) < 2 * 0 + 1) ∧ (2 * (1 : ℤ) < 2 * 1 + 1) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  have h1 := realizedYk_is_the_banked_ladder S aE q2E sE auxW invT robD
    { S₀ with budgetY := S₀.budgetY + 1 } V n
  have h2 := realizedYk_is_the_banked_ladder S aE q2E sE auxW invT robD S₀ V n
  have hbase : ({ S₀ with budgetY := S₀.budgetY + 1 } : LevelState).budgetY =
      S₀.budgetY + 1 := rfl
  rw [h1, h2, hbase]
  obtain ⟨hA, -⟩ := budget_closed_forms (S₀.budgetY + 1) S₀.budgetD
    (realizedOverhead S aE q2E sE) (slowIndex V n)
  obtain ⟨hB, -⟩ := budget_closed_forms S₀.budgetY S₀.budgetD
    (realizedOverhead S aE q2E sE) (slowIndex V n)
  omega

end EthInapproximability.ParameterizedNP.DepthThread
