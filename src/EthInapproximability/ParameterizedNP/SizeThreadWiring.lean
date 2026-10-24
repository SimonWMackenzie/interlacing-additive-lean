import EthInapproximability.ParameterizedNP.EffectiveMaterialization

/-!
# Parameterized NP route: the size thread wired to the realized chain

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`SIZE-001`** (the size thread), consuming
**`MATERIALIZE-001`**'s seed-anchored deliverables by pin.

`SizePropagation.lean` (`SIZE-001`) transcribed `step:I-07`
(`13-iteration-assembly.tex`, label line 516) with the whole size family a
binder: `iteratedSizeMajorant` quantifies over an arbitrary `z : ℕ → ℕ` and an
arbitrary arrow family `arr : ℕ → ArrowSize`, and its `hcarry` -- the frozen
sentence "Canonical reindexing preserves both carrier cardinalities, so the next
public matrix also satisfies `z_{i+1} <= z_{i+1}^+`" (`13:555--556`) -- was a
named hypothesis.  `EffectiveMaterialization.lean` (`MATERIALIZE-001`) then built
the realized chain, whose state slots `logRow`, `logCol` **are** `clog_2` of the
exact carrier recurrence.  This module wires the two together: the size family is
no longer a binder but the realized chain's own `z_R`, the arrow family is no
longer a binder but the specification's own two interlace widths and the level's
own source exponents, and the frozen carry step becomes a **theorem** modulo the
one comparison the paper itself withholds.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module traces

Opened first-hand this tranche, `13-iteration-assembly.tex:516--580`,
`step:I-07` (label line 516):

```
 Let z_i denote an integer upper bound on the two ceiling-logarithmic side
 lengths of R_i.  The seed satisfies z_0 < E_3(n) = E_{c_0}(n).      (:519--520)

 For every 0 <= i < k, at arrow i+1, define the integer driver
   Z_{i,N} = max{1, z_i, floor log_2(n+2), log_2 q_{2,i+1},
                 floor log_2 q_{1,i+1}, log_2 s_{i+1}, log_2 t_{2,i+1}},  (:529--537)
 and put
   z_{N,i} = C_dim (t_{2,i+1} + s_{i+1}(q_{1,i+1} + s_{i+1}) + 1) Z_{i,N}, (:538--543)
   z_{i+1}^+ = max{Q_{i+1}(log_2 q_{i+1} + z_{N,i}),
                   log_2 Q_{i+1} + q_{i+1} z_{N,i}}.                      (:544--549)

 The exact wrapper calculation in (exp:E-14-step) bounds the raw output by
 z_{i+1}^+.  Canonical reindexing preserves both carrier cardinalities, so the
 next public matrix also satisfies z_{i+1} <= z_{i+1}^+.               (:553--556)
```

The supporting displays are opened at their own anchors, never recalled:

1. `11-one-level-assembly.tex:846--856`, `exp:E-14-raw`: the uniform comparison
   `z_N <= zbar_N = C_dim (t_2 + s(q_1 + s) + 1) Z_N`, immediately followed by
   ":852--856", "This inequality is not inferred from the big-`O` display.
   `thm:eff-ledger` prints a size-successor row with a numerical integer `C_dim`,
   the seven multiplicity contributions, and a checked derivation of
   `exp:E-14-raw`.  The finite one-level theorem and the exact recurrence below
   do not consume that uniform comparison."  It is therefore a **named
   hypothesis** at every use site below, in its carrier form (GAP-EXPOSED 1).
2. `11-one-level-assembly.tex:858--882`, the exact wrapper cardinalities
   `|Rows(Rnext)| = (q m_N)^Q`, `|Cols(Rnext)| = Q n_N^q`, the two power
   estimates at lines 867--873, and `exp:E-14-step` (label line 881) -- banked as
   `OneLevelAssembly.rowBranch_bound`, `.colBranch_bound`, `.sideStep`,
   `.sideStep_bounds` and consumed by pin.
3. `12-iteration-specification.tex:260--265`, `eq:fixed-level-carriers`:
   `m_{i+1} = (q_i m_{N,i})^{Q_i}`, `n_{i+1} = Q_i (n_{N,i})^{q_i}` -- banked as
   `FixedLevelCarriers.LevelCarrierSpec.rowCarrier` / `.colCarrier`.
4. `13-iteration-assembly.tex:520`, the strict seed row `z_0 < E_3(n)`,
   discharged at the paper's own base state through the banked
   `PaddingAndClock.seedSizeChain` (`13:761--766`).
5. `06-parameter-schedule.tex`, label line 319 (`eq:stage1-scales`) and
   `07-one-level-construction.tex:118`, `q_1 = 2^a - 2` with `a >= 3` -- carried
   by the banked `SizePropagation.ArrowSize` record's own guard field, never
   restated here.

**N1 (the two index conventions, and why they agree).**  `12:255--265` labels the
widths of the arrow that maps level `i` to level `i+1` as `q_i, Q_i`; `13:529`
labels the *same* arrow "arrow `i+1`" and its data `q_{2,i+1}, q_{1,i+1},
s_{i+1}, t_{2,i+1}, q_{i+1}, r_{Q,i+1}`.  Both sections are frozen and both are
transcribed as printed: `levelArrow S ... i` is the Lean arrow **from** level `i`
**to** level `i+1`, its two interlace fields are the specification's `S.qExp i`
and `outerExp S i` (which `eq:fixed-level-carriers` uses to build level `i+1`),
and its four source exponents are the frozen `a_{i+1}, log_2 q_{2,i+1},
log_2 s_{i+1}, log_2 t_{2,i+1}`.  This is the same zero-based re-indexing
`SizePropagation.iteratedSizeMajorant` already records in its own N1, and the
same one `EffectiveMaterialization.realizedOverhead` uses for `H_i`.

## What lands

* `realizedZ` -- the frozen `z_i` of `13:519`, no longer a binder: it is
  `EffectiveMaterialization.stateZR` read at
  `EffectiveMaterialization.realizedState`, i.e. the realized chain's own
  `max{ceil(log_2 m_i), ceil(log_2 n_i)}`.  At every successor level it is
  **exactly** `sideExponent` of the carrier recurrence (`realizedZ_succ`, by
  `rfl`), so it is the recurrence evaluated and never a majorant of it.
* `levelArrow` -- the frozen arrow record of `13:529--549`, no longer a binder:
  the two interlace fields are the specification's own `q_i` and `Q_i` (through
  the banked `LevelCarrierSpec.qExp` and `EffectiveMaterialization.outerExp`),
  and the Stage-1 guard `a >= 3` is discharged by an explicit binder rather than
  by a premise bundle.
* `realizedCarry` -- the frozen `13:553--556` **derived**: from the exact carrier
  recurrence and the two power estimates of `11:867--873`, the realized chain's
  own `z_{i+1}` is at most `z_{i+1}^+`.  Its only inputs are the two carrier
  forms of `exp:E-14-raw`, which the paper itself declines to derive.
* `realizedZ_seed_lt` -- the frozen strict seed row `z_0 < E_{c_0}(n)` of
  `13:520`, **derived** at the paper's own base state (the banked
  `SuccessorMajorant.seedState`) rather than assumed.
* `realizedSizeThread` -- `step:I-07` run over the realized chain: the frozen
  induction with `z` and `arr` instantiated by the construction and `hcarry`
  discharged by `realizedCarry`.
* `realizedSizeThread_at_seed` -- the same at the paper's own base state, with
  the seed row **derived** from `realizedZ_seed_lt`, so both ends of the
  induction are the paper's own data.
* `realizedZ_fires_at_paperCarrierSpec` -- the canonical-inhabitation firing: at
  the banked `CoefficientTraversal.paperCarrierSpec` the size readout is the
  paper's own `N = A^T` carriers, and the `2^{22}`-fold column blow-up forces a
  numeric floor `22 <= z_{i+1}` that no renaming could produce.
* `sizeThread_bundle_consistent` -- joint satisfiability of the whole hypothesis
  bundle at `k = 1` together with its conclusion, with the thread **moving**
  (`z_0 = 0`, `8192 <= z_1`).  Its specification and base state are explicitly
  NON-FIDELITY; see GAP-EXPOSED 3.

## DEFINED-vs-FREE

* **DEFINED, reified and evaluated, never assigned a numeral:** `z_i` (the
  `13:519` quantity, evaluated as `stateZR` of the realized chain); `m_{i+1}`,
  `n_{i+1}` (`eq:fixed-level-carriers`, banked); `q_i = 2^{A_wrap,i L_{P,i}^2}`
  and `Q_i = 2^{r_{Q,i}}` (banked `LevelCarrierSpec.q`, `.Q`, `EntryGates.rQ`);
  `q_{1,i} = 2^{a_i} - 2` (banked `FiniteSlots.Stage1SlotBinding`, through
  `ArrowSize.q1`); `Z_{i,N}`, `z_{N,i}`, `z_{i+1}^+` (banked
  `SizePropagation.sizeDriver`, `.rawSideMajorant`, `OneLevelAssembly.sideStep`,
  through `ArrowSize.driver`, `.rawMajorant`, `.stepBound`); `c_i` and `E_c(n)`
  (banked `IterationAssembly.cexp`, `.envE`); `q_seed(n)`, `z_seed(n)`, `B(n)`
  (banked `PaddingAndClock`); the base state (banked
  `SuccessorMajorant.seedState`).
* **FREE in the paper itself, therefore binders:** `C_dim`, whose literal
  producer `eq:Cdim-literal-producer` (`06:2195--2200`) is compiler output that
  `PARAM-001` does not build; the Stage-1 exponent `a_i` and the three source
  exponents `log_2 q_{2,i}`, `log_2 s_i`, `log_2 t_{2,i}`, which come from the
  pre-family traversal (`14:1878--1889`) and the guarded source, neither of which
  is in Lean; the emission `Cert_c` and hence the three `AuxOut` list families
  (inherited unchanged from `MATERIALIZE-001`'s GAP-EXPOSED 1), which this module
  shows do not reach the size thread at all
  (`realizedZ_succ_ignores_the_emission_binders`); the two carrier forms of
  `exp:E-14-raw`, which `11:852--856` assigns to `thm:eff-ledger`'s checked
  size-successor row; the recorded successor row itself, which is the frozen
  conditional of the `13:558--571` reading warning.

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate read in place.

**One reader item is claimed, by one declaration, not previously assigned.**

* `05-iteration.tex:273--277` -- "Since `n >= 1` implies `l(n) >= 3`, minimality
  in the definition of the seed gives, with `b = B(n)`,
  `q < 128(B(n)+1)+2 < 129 B(n) < E_3(n)`." -- the reader's own **strict** seed
  row, claimed by `realizedZ_seed_lt`, which delivers exactly its endpoints
  `q_seed(n) < E_3(n) = E_{c_0}(n)`.  **Disclosure (records-only repair, cc-t3p;
  the earlier wording here was inaccurate and is corrected).**  The two artifacts
  print the *same* intermediate constants: `128` stands in the paper at `13:758`
  (`2^a < 128(b+1)+4`, hence `q < 128b+130` at `13:759`, which is the reader's
  `128(B(n)+1)+2` written differently -- the two are the same integer) and `129`
  stands in the paper at `13:764`.  What differs is the **quantity carried
  through the second half of the chain**: the reader bounds `q` alone all the way
  (`q < 128(B(n)+1)+2 < 129 B(n) < E_3(n)`), whereas the paper switches at
  `13:763` to `z_seed(n) = q + a` and finishes through
  `129b+130 < 130b = 130 E_2(n)` (`13:764`) with `130 E_2(n) < E_3(n)` at
  `13:786`.  The Lean proof takes the **paper's** chain -- the banked
  `PaddingAndClock.seedSizeChain`, via `q_seed(n) <= z_seed(n)` -- and lands on
  the printed endpoints `q < E_3(n)`, which both artifacts state identically;
  where the two disagree the paper wins.  A sweep of every module under
  `src/EthInapproximability/ParameterizedNP/` for `05-iteration.tex` citations in
  the interval `269--285` returns `:272` (`IterationAssembly`), `:278--280`
  (`SuccessorMajorant.seedState_underEnvelope`, and declined by
  `SuccessorComposition`), `:280--283`
  (`OneLevelCompletion.pinnedOutput_carriers_invariant`, navigation-cited by
  `FixedLevelCarriers` and `SizePropagation`) and `:281`
  (`IterationAssembly`) -- none of which meets `273--277`.

**No reader item is claimed by any other declaration here, and the reason is
recorded.**  `eq:paper-log-carrier-recurrence` (`05-iteration.tex`, label line
174, display lines 168--175) is **already assigned** to
`SizePropagation.arrowSizeStep`, so `realizedCarry` claims nothing and consumes
that endpoint's arithmetic by pin.  `eq:paper-fixed-level-growth` (label line
289, display lines 286--290) is already assigned to
`SizePropagation.iteratedSizeMajorant`, so `realizedSizeThread` and
`realizedSizeThread_at_seed` claim nothing.  `eq:paper-exact-carrier-recurrence`
(label line 166) is the `SIZE-001` row's own reader item.  `05-iteration.tex:176`
(the `n^{o(1)}` clause) and `04-bridge.tex:177--181`
(`eq:one-level-exact-carriers`) remain unclaimed here as well: the first is an
asymptotic clause this module proves nothing about, the second was deliberately
declined by `ONELEVEL-001` and nothing here changes that.  `C_dim`, `Z_N` and
`z_N` have no reader counterpart at all -- the reader prints none of
`C_{\mathrm{dim}}`, `Z_{\mathbb N}`, `z_{N}` -- which `SIZE-001` already records.

Crosswalk: no new row; the assignment stays in the existing row **6,
"Simultaneous parameters and size"**, of `READER_CROSSWALK.md`.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is a
  transcription of a frozen display, a general property of that transcription, or
  a composition of banked results.  No communication-complexity lemma is
  introduced, adapted or re-proved, and no banked module is edited.
* **Six previously unwired `MATERIALIZE-001` declarations become consumed:**
  `EffectiveMaterialization.realizedState`, `.stateZR` (both inside `realizedZ`),
  `.realizedState_sides` (inside `realizedZ_succ`), `.outerExp` (inside
  `levelArrow`), `.two_pow_outerExp` (inside `levelArrow_widths`) and
  `.stateZR_seedState` (inside `realizedZ_seed_lt`); `.realizedState_budgets` is
  consumed as a seventh, by `sizeThread_and_budgetThread_share_one_chain`.
* Consumed by pin, never restated: `IterationAssembly.cexp`, `.cexp_zero`,
  `.envE`, `.carrierRowNext`, `.carrierColNext`, `.budgetY`, `.budgetD`,
  `.envelope_fires_nondegenerate`;
  `OneLevelAssembly.sideExponent`, `.sideStep`, `.sideStep_bounds`,
  `.rowBranch_bound`, `.colBranch_bound`;
  `SizePropagation.ArrowSize` and its `q1`, `sVal`, `t2Val`, `driver`,
  `.rawMajorant`, `.stepBound`, plus `.sizeDriver`, `.dimMultiplicity`,
  `.rawSideMajorant`, `.maxFrom_ge_base`, `.sideExponent_le_of_carriers_le`,
  `.iteratedSizeMajorant`;
  `FixedLevelCarriers.LevelCarrierSpec` and its `.q`, `.qExp`, `.Q`,
  `.rowCarrier`, `.colCarrier`;
  `PaddingAndClock.seedSizeChain`, `.qSeed`, `.zSeed`;
  `SuccessorMajorant.LevelState`, `.seedState`;
  `SuccessorComposition.seedZR`, `.seedZR_eq`;
  `CoefficientTraversal.paperCarrierSpec`;
  `EntryGates.rQ`, `.Qwidth`, `.directEntryGates_fires`;
  `EffectiveMaterialization.realizedChain_record_fires_at_paperCarrierSpec`.
* Imports: `EffectiveMaterialization` only, hence transitively
  `SuccessorComposition`, `CoefficientTraversal`, `EnvelopeRealization`,
  `SuccessorMajorant`, `SizePropagation`, `FixedLevelCarriers`,
  `IterationAssembly`, `OneLevelCompletion`, `OneLevelAssembly`,
  `ParameterSchedule`, `PaddingAndClock`, `EntryGates` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  **`LegacyNPCC.Stage12` is not
  imported**, so no declaration reaches the cited AGHP balanced-family axiom and
  no opt-in ledger note is owed; `EXPANDER-001` has no contact with this module.
* External adapters: none.  No new `axiom`, no opaque certificate.
* Axiom surface (Appendix D, and `#print axioms`): at most `propext`,
  `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **No new structure.**  This module introduces no record at all.  `levelArrow`
  produces the **banked** `SizePropagation.ArrowSize`, so no field can be added
  to the paper's own record, and its one guard arrives as an explicit binder
  `ha : 3 <= aE i` rather than as a premise bundle.  Nothing restates a derived
  telescope.
* **The desired conclusions stay out of the data.**  `realizedZ` is a `def` over
  the banked state record and carries no envelope, complexity, robustness or
  promise field; every bound it satisfies is a theorem about it.
* **Both interlace widths stay distinct.**  `q_i` enters only through
  `LevelCarrierSpec.qExp` and `Q_i` only through
  `EffectiveMaterialization.outerExp`; `levelArrow_widths` exhibits them in the
  two distinct fields, and the carry proof reads them on **opposite** sides of
  the two branches -- `Q` exponentiates the row branch and multiplies the column
  branch.  `realizedCarry_reads_the_widths_on_opposite_branches` refutes the
  merge in the kernel.
* **Every comparison is transcribed as printed.**  `13:520`'s seed row is
  **strict** and is transcribed strict; `13:556`'s carry row and the reading
  warning's successor row are non-strict and are transcribed non-strict.
* **Statement poles.**  `successorRow_is_not_free` shows the recorded
  size-successor row is a genuine hypothesis, not a derivable one -- the arrow's
  step bound is unbounded in `C_dim` at fixed legal widths, so no envelope
  dominates it uniformly.  `sizeThread_bundle_consistent` shows the whole bundle
  is nonetheless jointly satisfiable **with the thread moving**.
  `realizedCarry_hypotheses_consistent` shows the two carrier hypotheses of
  `realizedCarry` are satisfiable at every specification and level, so the carry
  theorem is not vacuous.

## GAP-EXPOSED

1. **`exp:E-14-raw` is not derived, and is not an axiom.**  The uniform
   comparison `z_N <= zbar_N` is, by `11:852--856`, delivered by
   `thm:eff-ledger`'s checked size-successor row and "is not inferred from the
   big-`O` display".  `realizedCarry` therefore takes it in its two carrier
   forms, `m_{N,i}, n_{N,i} <= 2^{zbar_{N,i}}`, as explicit binders.  Nothing
   below asserts them, and `PARAM-001` stays open.
2. **Canonical reindexing is still not in Lean, and this module does not need
   it.**  `13:555--556` deduces `z_{i+1} <= z_{i+1}^+` for the *canonically
   reindexed* matrix from the invariance of both carrier cardinalities.
   `lem:canonical-reindexing-invariance` has no Lean declaration (`ITER-001`
   GAP-EXPOSED 2).  What `realizedCarry` proves is the bound at the realized
   chain's own state slots, which `14:1936--1938` fixes as
   `R_{i+1} = Can(T_i.Rnext)` and `MATERIALIZE-001` builds as `clog_2` of the
   *successor carriers*; so the reindexing step is **built into the banked
   construction's index convention**, not proved here.  A consumer must read
   this as: the thread is threaded through `MATERIALIZE-001`'s convention, and
   the invariance lemma remains owed by `ITER-001`.
3. **The consistency probe's specification and base state are NON-FIDELITY.**
   `probeSpec` records `m_{N,i} = n_{N,i} = 1`, which is *not* the paper's
   `184` / `2^{22}` (banked
   `EffectiveMaterialization.realizedChain_record_fires_at_paperCarrierSpec`),
   and `probeBase` is the all-zero state, not
   `SuccessorMajorant.seedState`.  It is an audit instance and stands in for
   nothing: what it establishes is exactly what the hypothesis-consistency rule
   demands, that the bundle of `realizedSizeThread` is jointly satisfiable
   together with its conclusion at a level count `k >= 1`, so no `False`
   derives from it.  The paper's own instance appears separately, in
   `realizedZ_fires_at_paperCarrierSpec` and
   `realizedSizeThread_at_seed`.
4. **The canonical inhabitation of the *whole* thread at the paper's instance is
   registered, not discharged.**  `realizedZ_fires_at_paperCarrierSpec` fires the
   size readout at `CoefficientTraversal.paperCarrierSpec`; but supplying that
   specification's level-`i` reservoir data from level `i`'s own output is
   `STAGE1-001 .. WRAP-001`, and supplying `C_dim`, `a_i`, `log_2 q_{2,i}`,
   `log_2 s_i`, `log_2 t_{2,i}` and the recorded successor row is `PARAM-001`.
   Until those land, `realizedSizeThread` at `paperCarrierSpec` with all
   hypotheses discharged is a **deferred** obligation on the `SIZE-001` row, and
   the NON-FIDELITY probe of GAP-EXPOSED 3 does not satisfy it.
5. **Nothing about the machines is claimed.**  `A_realize`, `A_materialize`, the
   descriptor codec, the entry evaluator, the padding maps and
   `eq:materializer-exact-runtime` have no Lean declaration, per the standing
   runtime deferral; the size side lands and the machine layer does not.  No
   route completion is claimed.
-/

namespace EthInapproximability.ParameterizedNP.SizeThreadWiring

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.SizePropagation
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.EffectiveMaterialization

/-! ## Part 1: the two families `step:I-07` quantifies over, instantiated -/

/-- **`z_i`, the frozen size family of `13-iteration-assembly.tex:519`, read off
the realized chain.**

Frozen text: "Let `z_i` denote an integer upper bound on the two
ceiling-logarithmic side lengths of `R_i`."  At the realized chain the two state
slots **are** those two ceiling logarithms (`MATERIALIZE-001`'s
`realizedState_sides`), so their maximum -- the banked
`EffectiveMaterialization.stateZR`, itself the `z_R` display of `06:51--55` -- is
the least such integer, not an assumed majorant of it.

This is what turns `SizePropagation.iteratedSizeMajorant`'s binder `z : ℕ → ℕ`
into the construction.

Reader counterpart: **none claimed** for this definition; the reader item is
claimed by `realizedZ_seed_lt` below.  General in the specification, the three
exponent families, the three `AuxOut` families, the base state and the level. -/
noncomputable def realizedZ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (i : ℕ) : ℕ :=
  stateZR (realizedState S aE q2E sE auxW invT robD S₀ i)

/-- **The arrow record of `13-iteration-assembly.tex:529--549`, with both
interlace widths read off the specification.**

The banked `SizePropagation.ArrowSize` carries six public numbers and one
legality guard.  Four of them -- `a_i`, `log_2 q_{2,i}`, `log_2 s_i`,
`log_2 t_{2,i}` -- are FREE in the paper (they are pre-family traversal and
guarded-source output, `PARAM-001` and `STAGE2-001`), so they arrive as explicit
level-indexed binders.  The two interlace exponents are **not** free: `q_i` is
`eq:q-deltaU` through the banked `LevelCarrierSpec.qExp`, and `r_{Q,i}` is
`10-direct-bridge.tex:51` through the banked
`EffectiveMaterialization.outerExp`.  Neither is assigned a numeral and neither
is a second copy of the other.

The guard `a_i >= 3` (`07-one-level-construction.tex:118`) is an explicit binder
`ha`, never a premise bundle and never a field restating a derived telescope.

See **N1** in the module header for the two frozen index conventions.

Reader counterpart: **none claimed**; the reader prints no arrow record.
General in the specification, the four exponent families and the level. -/
noncomputable def levelArrow (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE t2E : ℕ → ℕ) (i : ℕ) (ha : 3 ≤ aE i) : ArrowSize where
  wq := S.qExp i
  rQv := outerExp S i
  wq2 := q2E i
  ws := sE i
  wt2 := t2E i
  aExp := aE i
  three_le_aExp := ha

/-! ## Part 2: the aux-lemma battery

Seven general properties.  None is about a pinned instance: each quantifies over
arbitrary specifications, exponent families, `AuxOut` families, base states and
levels. -/

/-- **Aux 1 (the frozen legality guard `q_i >= 2` holds at every specification).**

`02-mechanical-contract.tex:771--775` fixes `q >= 2`, i.e. `1 <= log_2 q`.  At a
`LevelCarrierSpec` this is not a hypothesis: `eq:q-deltaU` puts
`q_i = 2^{A_wrap,i L_{P,i}^2}` and the record's own two guards give
`A_wrap,i, L_{P,i} >= 1`.  This is what discharges the `hq` binder that
`SizePropagation.arrowSizeStep` and `OneLevelAssembly.oneLevelAssembly_sideBound`
carry.  General in the specification and the level. -/
theorem one_le_qExp (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) :
    1 ≤ S.qExp i := by
  have hA := S.one_le_Awrap i
  have hL := S.one_le_LP i
  change 1 ≤ S.Awrap i * S.LP i ^ 2
  calc (1 : ℕ) = 1 * 1 ^ 2 := by norm_num
    _ ≤ S.Awrap i * S.LP i ^ 2 := Nat.mul_le_mul hA (Nat.pow_le_pow_left hL 2)

/-- **Aux 2 (the arrow's two interlace fields are the specification's two
widths, and they stay apart).**

`2^{w_{q,i}} = q_i` and `2^{r_{Q,i}} = Q_i`, both by `rfl`, through the banked
`LevelCarrierSpec.q` and `EffectiveMaterialization.two_pow_outerExp`.  Recorded
so that no proof below reopens either width, and so that the identification is
inspectable rather than hidden behind the record.  General. -/
theorem levelArrow_widths (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE t2E : ℕ → ℕ) (i : ℕ) (ha : 3 ≤ aE i) :
    2 ^ (levelArrow S aE q2E sE t2E i ha).wq = S.q i ∧
      2 ^ (levelArrow S aE q2E sE t2E i ha).rQv = S.Q i ∧
      1 ≤ (levelArrow S aE q2E sE t2E i ha).wq :=
  ⟨rfl, two_pow_outerExp S i, one_le_qExp S i⟩

/-- **Aux 3 (the size family at the base is the base state's own `z_R`).**

Definitional, and recorded because it is what lets the seed row of `13:520` be
stated about the paper's base state rather than about a numeral.  General. -/
theorem realizedZ_zero (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) :
    realizedZ S aE q2E sE auxW invT robD S₀ 0 = stateZR S₀ := rfl

/-- **Aux 4 (the size family at every successor is the exact carrier recurrence,
read through the two ceilings).**

`realizedZ ... (i+1) = max{ceil(log_2 m_{i+1}), ceil(log_2 n_{i+1})}` with
`m_{i+1} = (q_i m_{N,i})^{Q_i}` and `n_{i+1} = Q_i (n_{N,i})^{q_i}`, by `rfl`.
That it holds by `rfl` is the point: `13:519`'s "integer upper bound" is here the
*evaluated* recurrence and not a binder above it, which is exactly what
`MATERIALIZE-001`'s `realizedState_sides` bought.  General. -/
theorem realizedZ_succ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedZ S aE q2E sE auxW invT robD S₀ (i + 1) =
      sideExponent (S.rowCarrier (i + 1)) (S.colCarrier (i + 1)) := by
  obtain ⟨hrow, hcol⟩ :=
    realizedState_sides S aE q2E sE auxW invT robD S₀ i
  simp only [realizedZ, stateZR, sideExponent, hrow, hcol]

/-- **Aux 5 (the emission binders do not reach the size thread).**

`MATERIALIZE-001` carries `AuxOut(Cert_c)` as three level-indexed list binders
(its GAP-EXPOSED 1) and the base state as a fourth binder.  None of the four --
nor the three source-exponent families that feed the overhead `H_i` -- occurs in
the size family above level zero: after one arrow the two state slots are pure
functions of the carrier specification.  So the unbuilt compiler is not a
hidden input to `step:I-07`, and `PARAM-001`'s debt at the size thread is
confined to `C_dim` and the recorded successor row.  Holds by `rfl`; general in
both sets of data and the level. -/
theorem realizedZ_succ_ignores_the_emission_binders
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE aE' q2E' sE' : ℕ → ℕ)
    (auxW invT robD auxW' invT' robD' : ℕ → List ℕ) (S₀ S₀' : LevelState)
    (i : ℕ) :
    realizedZ S aE q2E sE auxW invT robD S₀ (i + 1) =
      realizedZ S aE' q2E' sE' auxW' invT' robD' S₀' (i + 1) := rfl

/-- **Aux 6 (the frozen step bound is monotone in the incoming side length).**

`z_i <= z_i'` gives `z_{i+1}^+ <= z_{i+1}'^+`, by composing the banked
`sizeDriver_mono_incoming`, `rawSideMajorant_mono` and `sideStep_mono` along
`13:529--549`.  This is the property that makes the frozen induction usable at a
*majorant* of the realized side length as well as at the realized one, and it is
stated at an arbitrary arrow, not at the pinned ones.  General in the arrow, the
recorded coefficient, both side lengths and the source size. -/
theorem stepBound_mono_incoming (a : ArrowSize) (Cdim n : ℕ) {z z' : ℕ}
    (h : z ≤ z') : a.stepBound Cdim z n ≤ a.stepBound Cdim z' n :=
  sideStep_mono a.wq a.rQv
    (rawSideMajorant_mono Cdim a.t2Val a.sVal a.q1
      (sizeDriver_mono_incoming n a.q1 a.wq2 a.ws a.wt2 h))

/-- **Aux 7 (the arrow's raw majorant dominates the recorded coefficient).**

`zbar_N = C_dim (t_2 + s(q_1 + s) + 1) Z_N` with `t_2 + s(q_1 + s) + 1 >= 1` and
the frozen floor `Z_N >= 1` of `11:816` gives `C_dim <= zbar_N`.  Both factors
are bounded below by the frozen data itself -- the `+1` of the multiplicity
display and the literal `1` inside `max{1, z, ...}` -- so this needs no legality
hypothesis.  It is what makes the two carrier hypotheses of `realizedCarry`
satisfiable and the successor row a genuine constraint.  General in the arrow,
the coefficient, the incoming side length and the source size. -/
theorem le_rawMajorant (a : ArrowSize) (Cdim z n : ℕ) :
    Cdim ≤ a.rawMajorant Cdim z n := by
  have hZ : 1 ≤ a.driver z n := maxFrom_ge_base 1 _
  have hM : 1 ≤ dimMultiplicity a.t2Val a.sVal a.q1 := by
    simp only [dimMultiplicity]
    omega
  calc Cdim = Cdim * 1 * 1 := by ring
    _ ≤ Cdim * dimMultiplicity a.t2Val a.sVal a.q1 * a.driver z n :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hZ

/-! ## Part 3: the frozen carry step, derived -/

/-- **`13-iteration-assembly.tex:553--556`, derived at the realized chain.**

Frozen text: "The exact wrapper calculation in `exp:E-14-step` bounds the raw
output by `z_{i+1}^+`.  Canonical reindexing preserves both carrier
cardinalities, so the next public matrix also satisfies
`z_{i+1} <= z_{i+1}^+`."

Here `z_{i+1}` is the realized chain's own side length (`realizedZ_succ`), so the
statement is about the construction and not about an assumed family.  The proof
is the frozen calculation of `11:865--874` and nothing else: `m_{i+1}` and
`n_{i+1}` are the exact carriers of `eq:fixed-level-carriers`, the two widths are
powers of two (`levelArrow_widths`), and the two power estimates land on the two
**different** branches of `exp:E-14-step` -- `Q` exponentiates the row branch and
multiplies the column branch.

The two hypotheses are the carrier form of `exp:E-14-raw`
(`11-one-level-assembly.tex:846--851`), which `11:852--856` states is supplied by
`thm:eff-ledger`'s checked size-successor row and "is not inferred from the
big-`O` display".  They are binders, not axioms (GAP-EXPOSED 1), and
`realizedCarry_hypotheses_consistent` inhabits them at every specification and
level.

See GAP-EXPOSED 2 for what "canonical reindexing" contributes and what it does
not.

Reader counterpart: **none claimed**; `eq:paper-log-carrier-recurrence`
(`05-iteration.tex`, label line 174) is already assigned to
`SizePropagation.arrowSizeStep`, whose arithmetic this consumes by pin.

General in the specification, the four exponent families, the three `AuxOut`
families, the base state, the recorded coefficient, the source size and the
level. -/
theorem realizedCarry (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE t2E : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (Cdim n i : ℕ) (ha : 3 ≤ aE i)
    (hmN : S.mN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i ha).rawMajorant Cdim
      (realizedZ S aE q2E sE auxW invT robD S₀ i) n)
    (hnN : S.nN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i ha).rawMajorant Cdim
      (realizedZ S aE q2E sE auxW invT robD S₀ i) n) :
    realizedZ S aE q2E sE auxW invT robD S₀ (i + 1) ≤
      (levelArrow S aE q2E sE t2E i ha).stepBound Cdim
        (realizedZ S aE q2E sE auxW invT robD S₀ i) n := by
  set A := levelArrow S aE q2E sE t2E i ha with hA
  set z := realizedZ S aE q2E sE auxW invT robD S₀ i with hz
  set zN := A.rawMajorant Cdim z n with hzN
  obtain ⟨hb1, hb2⟩ := sideStep_bounds A.wq A.rQv zN
  have hstep : A.stepBound Cdim z n = sideStep A.wq A.rQv zN := rfl
  have hq : S.q i = 2 ^ A.wq := rfl
  have hQ : S.Q i = 2 ^ A.rQv := (two_pow_outerExp S i).symm
  have hrow : S.rowCarrier (i + 1) ≤ 2 ^ A.stepBound Cdim z n := by
    have hcarr : S.rowCarrier (i + 1) = (2 ^ A.wq * S.mN i) ^ 2 ^ A.rQv := by
      change carrierRowNext (S.q i) (S.mN i) (S.Q i) = _
      rw [carrierRowNext, hq, hQ]
    rw [hcarr, hstep]
    exact le_trans (rowBranch_bound A.wq zN (2 ^ A.rQv) (S.mN i) hmN)
      (Nat.pow_le_pow_right (by norm_num) hb1)
  have hcol : S.colCarrier (i + 1) ≤ 2 ^ A.stepBound Cdim z n := by
    have hcarr : S.colCarrier (i + 1) = 2 ^ A.rQv * S.nN i ^ 2 ^ A.wq := by
      change carrierColNext (S.Q i) (S.nN i) (S.q i) = _
      rw [carrierColNext, hq, hQ]
    rw [hcarr, hstep]
    exact le_trans (colBranch_bound A.rQv (2 ^ A.wq) zN (S.nN i) hnN)
      (Nat.pow_le_pow_right (by norm_num) hb2)
  rw [realizedZ_succ]
  exact sideExponent_le_of_carriers_le hrow hcol

/-- **Statement pole: the two power estimates land on opposite branches.**

A transcription that read `q` and `Q` in the same role would typecheck, so the
asymmetry has to be exhibited.  The row carrier exponentiates by `Q_i` and
multiplies by `q_i`; the column carrier does the reverse.  At the audit point
where both recorded pre-wrapper counts are one, the two successor carriers are
therefore **strictly** different numbers -- the banked
`FixedLevelCarriers.widths_are_not_interchangeable` -- so no single carrier
equation, and no equation reading the two widths in the same role, could have
produced the pair the carry step consumes.

General in the specification, the four exponent families and the level. -/
theorem realizedCarry_reads_the_widths_on_opposite_branches
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE t2E : ℕ → ℕ) (i : ℕ)
    (ha : 3 ≤ aE i) (hm : S.mN i = 1) (hn : S.nN i = 1) :
    S.colCarrier (i + 1) < S.rowCarrier (i + 1) ∧
      S.rowCarrier (i + 1) =
        (2 ^ (levelArrow S aE q2E sE t2E i ha).wq * S.mN i) ^
          2 ^ (levelArrow S aE q2E sE t2E i ha).rQv ∧
      S.colCarrier (i + 1) =
        2 ^ (levelArrow S aE q2E sE t2E i ha).rQv *
          S.nN i ^ 2 ^ (levelArrow S aE q2E sE t2E i ha).wq := by
  have hq : S.q i = 2 ^ (levelArrow S aE q2E sE t2E i ha).wq := rfl
  have hQ : S.Q i = 2 ^ (levelArrow S aE q2E sE t2E i ha).rQv :=
    (two_pow_outerExp S i).symm
  refine ⟨FixedLevelCarriers.widths_are_not_interchangeable S i hm hn, ?_, ?_⟩
  · change carrierRowNext (S.q i) (S.mN i) (S.Q i) = _
    rw [carrierRowNext, hq, hQ]
  · change carrierColNext (S.Q i) (S.nN i) (S.q i) = _
    rw [carrierColNext, hq, hQ]

/-- **The two carrier hypotheses of `realizedCarry` are satisfiable everywhere.**

`exp:E-14-raw` is a hypothesis here, so it must be shown non-contradictory at
legal data: at *every* specification, every level and every incoming side length
there is a recorded coefficient making both carrier bounds hold.  The witness is
the paper's own shape, not a search -- `C_dim` is a literal maximum over a
printed table (`eq:Cdim-literal-producer`), hence at least the largest recorded
row, and `le_rawMajorant` transports any such choice through the multiplicity and
the driver.

This is the joint-satisfiability check for `realizedCarry`: no `False` derives
from its hypothesis bundle.  General in the specification, the four exponent
families, the three `AuxOut` families, the base state, the source size and the
level. -/
theorem realizedCarry_hypotheses_consistent
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE t2E : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (n i : ℕ) (ha : 3 ≤ aE i) :
    ∃ Cdim, 1 ≤ Cdim ∧
      S.mN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i ha).rawMajorant Cdim
        (realizedZ S aE q2E sE auxW invT robD S₀ i) n ∧
      S.nN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i ha).rawMajorant Cdim
        (realizedZ S aE q2E sE auxW invT robD S₀ i) n := by
  set A := levelArrow S aE q2E sE t2E i ha with hA
  set z := realizedZ S aE q2E sE auxW invT robD S₀ i with hz
  refine ⟨max (S.mN i) (S.nN i), le_trans (S.one_le_mN i) (le_max_left _ _),
    ?_, ?_⟩
  · calc S.mN i ≤ max (S.mN i) (S.nN i) := le_max_left _ _
      _ ≤ 2 ^ max (S.mN i) (S.nN i) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ A.rawMajorant (max (S.mN i) (S.nN i)) z n :=
          Nat.pow_le_pow_right (by norm_num)
            (le_rawMajorant A (max (S.mN i) (S.nN i)) z n)
  · calc S.nN i ≤ max (S.mN i) (S.nN i) := le_max_right _ _
      _ ≤ 2 ^ max (S.mN i) (S.nN i) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ A.rawMajorant (max (S.mN i) (S.nN i)) z n :=
          Nat.pow_le_pow_right (by norm_num)
            (le_rawMajorant A (max (S.mN i) (S.nN i)) z n)

/-! ## Part 4: the strict seed row, derived at the paper's own base state -/

/-- **`13-iteration-assembly.tex:520`, derived: `z_0 < E_{c_0}(n)`.**

Frozen text: "The seed satisfies `z_0 < E_3(n) = E_{c_0}(n)`", **strict** as
printed.  At the paper's own base state -- the banked
`SuccessorMajorant.seedState`, whose row slot is `q_seed(n)` and whose column
slot is `a_seed(n)` -- the size family's value is `q_seed(n)` (the banked
`EffectiveMaterialization.stateZR_seedState` composed with
`SuccessorComposition.seedZR_eq`), and `13:761--766` gives
`q_seed(n) <= z_seed(n) < 130 E_2(n) < E_3(n)` through the banked
`PaddingAndClock.seedSizeChain`.  So the seed row of `step:I-07` is a theorem
about the paper's construction and not a hypothesis.

Reader counterpart: `05-iteration.tex:273--277`, "Since `n >= 1` implies
`l(n) >= 3`, minimality in the definition of the seed gives, with `b = B(n)`,
`q < 128(B(n)+1)+2 < 129 B(n) < E_3(n)`."  Both artifacts print the same
constants `128` and `129` (`13:758`, `13:764`); they differ in which quantity the
second half of the chain carries -- `q` in the reader, `z_seed(n) = q + a` in the
paper -- and the proof above takes the paper's chain.  See the module header for
the full disclosure and for the sweep showing this item was previously
unassigned.

General in `n >= 1`, in the specification, in the three exponent families, in the
three `AuxOut` families and in the public scale list. -/
theorem realizedZ_seed_lt (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (n : ℕ) (hn : 1 ≤ n)
    (scales : List ℕ) :
    realizedZ S aE q2E sE auxW invT robD (seedState n scales) 0 <
      envE (cexp 0) n := by
  have hzr : realizedZ S aE q2E sE auxW invT robD (seedState n scales) 0 =
      PaddingAndClock.qSeed n := by
    rw [realizedZ_zero, stateZR_seedState n hn scales,
      SuccessorComposition.seedZR_eq n hn]
  obtain ⟨h1, h2⟩ := PaddingAndClock.seedSizeChain n hn
  have hq : PaddingAndClock.qSeed n ≤ PaddingAndClock.zSeed n := by
    simp only [PaddingAndClock.zSeed]
    omega
  rw [hzr, cexp_zero]
  omega

/-! ## Part 5: `step:I-07` run over the realized chain -/

/-- **`step:I-07` at the realized chain** (`13-iteration-assembly.tex`, label
line 516, body lines 519--580).

The banked `SizePropagation.iteratedSizeMajorant` is consumed by pin, with two
things no longer binders:

* `z` is `realizedZ`, the realized chain's own two ceiling logarithms;
* `arr` is `levelArrow`, whose two interlace fields are the specification's own
  `q_i` and `Q_i`;

and with `hcarry` -- the frozen `13:553--556` -- **discharged** by
`realizedCarry` rather than assumed.  What remains hypothesis is exactly what the
frozen text withholds:

* `hraw`, the two carrier forms of `exp:E-14-raw`, which `11:852--856` assigns to
  `thm:eff-ledger`'s checked size-successor row (GAP-EXPOSED 1);
* `hsuccRow`, the reading warning of `13:558--571` in its printed conditional
  form "if `z_i <= E_{c_i}(n)` then `z_{i+1}^+ <= E_{16(c_i+1)}(n)`";
* `hseed`, the strict row of `13:520`, which
  `realizedSizeThread_at_seed` then derives at the paper's own base state.

Neither `hraw` nor `hsuccRow` is a Lean axiom.

**N2 (dropped enabling conditions), inherited verbatim from the banked
statement.**  The frozen step assumes `k >= 1` and `n >= n_val(k)` and derives
`2 <= n`; none of the three is a hypothesis here, each omission *strengthens* the
statement, and a later consumer must treat them as facts available from
`step:I-01`/`step:I-02` rather than as new obligations.

Reader counterpart: **none claimed**; `eq:paper-fixed-level-growth`
(`05-iteration.tex`, label line 289) is already assigned to
`SizePropagation.iteratedSizeMajorant`.

General in the specification, the four exponent families, the three `AuxOut`
families, the base state, the recorded coefficient, the source size and the arrow
count. -/
theorem realizedSizeThread (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE t2E : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (Cdim n k : ℕ) (ha : ∀ i, 3 ≤ aE i)
    (hseed : realizedZ S aE q2E sE auxW invT robD S₀ 0 < envE (cexp 0) n)
    (hraw : ∀ i, i < k →
      S.mN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i (ha i)).rawMajorant Cdim
        (realizedZ S aE q2E sE auxW invT robD S₀ i) n ∧
      S.nN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i (ha i)).rawMajorant Cdim
        (realizedZ S aE q2E sE auxW invT robD S₀ i) n)
    (hsuccRow : ∀ i, i < k →
      realizedZ S aE q2E sE auxW invT robD S₀ i ≤ envE (cexp i) n →
      (levelArrow S aE q2E sE t2E i (ha i)).stepBound Cdim
        (realizedZ S aE q2E sE auxW invT robD S₀ i) n ≤
        envE (cexp (i + 1)) n) :
    (∀ i, i ≤ k → realizedZ S aE q2E sE auxW invT robD S₀ i ≤
        envE (cexp i) n) ∧
      (∀ i, i ≤ k → realizedZ S aE q2E sE auxW invT robD S₀ i ≤
        envE (cexp k) n) := by
  refine iteratedSizeMajorant n k Cdim
    (realizedZ S aE q2E sE auxW invT robD S₀)
    (fun i => levelArrow S aE q2E sE t2E i (ha i)) hseed ?_ hsuccRow
  intro i hi
  obtain ⟨hm, hn⟩ := hraw i hi
  exact realizedCarry S aE q2E sE t2E auxW invT robD S₀ Cdim n i (ha i) hm hn

/-- **`step:I-07` at the realized chain and at the paper's own base state.**

The same induction with `S₀` instantiated at the banked
`SuccessorMajorant.seedState` -- the literal base of `13:317--319` and
`12:565--577` -- and with the seed row of `13:520` **derived** from
`realizedZ_seed_lt` rather than assumed, so both ends of the thread are the
paper's own data.

Reader counterpart: **none claimed**; the reader item for the seed row is claimed
by `realizedZ_seed_lt` and re-citing it here would be the double assignment the
rule forbids.

General in `n >= 1`, the specification, the four exponent families, the three
`AuxOut` families, the public scale list, the recorded coefficient and the arrow
count. -/
theorem realizedSizeThread_at_seed (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE t2E : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (scales : List ℕ)
    (Cdim n k : ℕ) (hn : 1 ≤ n) (ha : ∀ i, 3 ≤ aE i)
    (hraw : ∀ i, i < k →
      S.mN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i (ha i)).rawMajorant Cdim
        (realizedZ S aE q2E sE auxW invT robD (seedState n scales) i) n ∧
      S.nN i ≤ 2 ^ (levelArrow S aE q2E sE t2E i (ha i)).rawMajorant Cdim
        (realizedZ S aE q2E sE auxW invT robD (seedState n scales) i) n)
    (hsuccRow : ∀ i, i < k →
      realizedZ S aE q2E sE auxW invT robD (seedState n scales) i ≤
        envE (cexp i) n →
      (levelArrow S aE q2E sE t2E i (ha i)).stepBound Cdim
        (realizedZ S aE q2E sE auxW invT robD (seedState n scales) i) n ≤
        envE (cexp (i + 1)) n) :
    (∀ i, i ≤ k →
        realizedZ S aE q2E sE auxW invT robD (seedState n scales) i ≤
          envE (cexp i) n) ∧
      (∀ i, i ≤ k →
        realizedZ S aE q2E sE auxW invT robD (seedState n scales) i ≤
          envE (cexp k) n) :=
  realizedSizeThread S aE q2E sE t2E auxW invT robD (seedState n scales) Cdim n k
    ha (realizedZ_seed_lt S aE q2E sE auxW invT robD n hn scales) hraw hsuccRow

/-- **The size thread and the budget thread are two readouts of one chain.**

`14:1644--1648` updates the two budgets and `eq:fixed-level-carriers` updates the
two carriers along the **same** realized arrow, so the size majorant of
`step:I-07` and the budget ladder of `eq:iterated-budgets` are not two parallel
inductions but two projections of `realizedState`.  Recorded because the frozen
`step:I-07` is stated inside the same fixed-depth induction as `step:I-03`, and
because a consumer must not re-derive the budgets from the size thread or vice
versa.  Consumes the banked `EffectiveMaterialization.realizedState_budgets` and
`IterationAssembly.budgetY` / `.budgetD` by pin.  General in every argument. -/
theorem sizeThread_and_budgetThread_share_one_chain
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedZ S aE q2E sE auxW invT robD S₀ (i + 1) =
        sideExponent (S.rowCarrier (i + 1)) (S.colCarrier (i + 1)) ∧
      (realizedState S aE q2E sE auxW invT robD S₀ i).budgetY =
        budgetY S₀.budgetY (realizedOverhead S aE q2E sE) i ∧
      (realizedState S aE q2E sE auxW invT robD S₀ i).budgetD =
        budgetD S₀.budgetD (realizedOverhead S aE q2E sE) i :=
  ⟨realizedZ_succ S aE q2E sE auxW invT robD S₀ i,
    (realizedState_budgets S aE q2E sE auxW invT robD S₀ i).1,
    (realizedState_budgets S aE q2E sE auxW invT robD S₀ i).2⟩

/-! ## Part 6: statement poles and the canonical firing -/

/-- **Statement pole: the recorded size-successor row is a genuine hypothesis.**

`hsuccRow` in `realizedSizeThread` is the frozen reading warning of
`13:558--571`, and `11:852--856` insists it is *supplied* by `thm:eff-ledger`
rather than inferred.  A formalization that quietly derived it would be wrong,
and a green build cannot see the difference -- so the obstruction is exhibited:
at fixed legal widths and a fixed incoming side length, the step bound
`z^+` is unbounded in the recorded coefficient `C_dim`, hence exceeds any
envelope value whatever.  No uniform bound on `z_{i+1}^+` follows from the
frozen displays alone.

General in the arrow, both side lengths, the source size and the target bound. -/
theorem successorRow_is_not_free (a : ArrowSize) (z n M : ℕ) :
    ∃ Cdim, M < a.stepBound Cdim z n := by
  refine ⟨M + 1, ?_⟩
  have h1 : M + 1 ≤ a.rawMajorant (M + 1) z n := le_rawMajorant a (M + 1) z n
  have h2 : a.rawMajorant (M + 1) z n ≤ a.stepBound (M + 1) z n := by
    exact le_trans (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)
      (le_trans (Nat.le_add_left _ a.rQv) (le_max_right _ _))
  omega

/-- **Canonical inhabitation of the size readout at the paper's own carrier
specification.**

`CoefficientTraversal.paperCarrierSpec` evaluates `m_{N,i}` and `n_{N,i}` through
the paper's own `N = A^T` over the protected duplicate
(`08-dense-stage4.tex:147`, `eq:protected-carrier-cardinalities`), so the size
readout of `13:519` is here taken at the paper's construction and not at a
stand-in.  The `2^{22}`-fold column blow-up the banked
`EffectiveMaterialization.realizedChain_record_fires_at_paperCarrierSpec` carries
is content: it forces the numeric floor `22 <= z_{i+1}` through the column
carrier `n_{i+1} = Q_i (n_{N,i})^{q_i}`, which no renaming of an empty
specification could produce.

This is **not** a discharge of `SIZE-001`'s canonical-inhabitation obligation for
the whole thread: see GAP-EXPOSED 4.  What is discharged is the size *readout* at
the paper's counts.

General in the Section-8 data, the schedule inputs, the exponent families, the
`AuxOut` families, the base state and the level. -/
theorem realizedZ_fires_at_paperCarrierSpec
    (F : FiniteSlots.Stage1SlotBinding) {q : ℕ} {V X L₂ Y : Type*} [Fintype V]
    [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y)
    (v₀ : V) (x₀ : X) (l₀ : L₂) (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ)
    (dv zeta : ℝ) (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ)
    (S₀ : LevelState) (i : ℕ) :
    realizedZ (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
        Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD S₀ (i + 1) =
      sideExponent
        ((CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert
          sPar lq2 clU0 zR dv zeta).rowCarrier (i + 1))
        ((CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert
          sPar lq2 clU0 zR dv zeta).colCarrier (i + 1)) ∧
      184 ≤ (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
        Ccert sPar lq2 clU0 zR dv zeta).mN i ∧
      2 ^ 22 ≤ (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
        Ccert sPar lq2 clU0 zR dv zeta).nN i ∧
      22 ≤ realizedZ (CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n
        C0 B0 Ccert sPar lq2 clU0 zR dv zeta) aE q2E sE auxW invT robD S₀
        (i + 1) := by
  set S := CoefficientTraversal.paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
    Ccert sPar lq2 clU0 zR dv zeta with hS
  obtain ⟨-, hmN, hnN⟩ :=
    realizedChain_record_fires_at_paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0
      Ccert sPar lq2 clU0 zR dv zeta i
  have hread := realizedZ_succ S aE q2E sE auxW invT robD S₀ i
  refine ⟨hread, hmN, hnN, ?_⟩
  have hcol : 2 ^ 22 ≤ S.colCarrier (i + 1) := by
    have hpow : S.nN i ≤ S.nN i ^ S.q i := by
      have h1 : 1 ≤ S.q i := by
        have : (1 : ℕ) ≤ 2 ^ S.qExp i := Nat.one_le_two_pow
        exact this
      calc S.nN i = S.nN i ^ 1 := (pow_one _).symm
        _ ≤ S.nN i ^ S.q i := Nat.pow_le_pow_right (S.one_le_nN i) h1
    have hQ : 1 ≤ S.Q i := by
      have : (1 : ℕ) ≤ 2 ^ outerExp S i := Nat.one_le_two_pow
      rw [← two_pow_outerExp S i]
      exact this
    change 2 ^ 22 ≤ carrierColNext (S.Q i) (S.nN i) (S.q i)
    rw [carrierColNext]
    calc (2 : ℕ) ^ 22 ≤ S.nN i := hnN
      _ ≤ S.nN i ^ S.q i := hpow
      _ = 1 * S.nN i ^ S.q i := (one_mul _).symm
      _ ≤ S.Q i * S.nN i ^ S.q i := Nat.mul_le_mul_right _ hQ
  rw [hread]
  calc (22 : ℕ) = Nat.clog 2 (2 ^ 22) := (Nat.clog_pow 2 22 (by norm_num)).symm
    _ ≤ Nat.clog 2 (S.colCarrier (i + 1)) := Nat.clog_mono_right 2 hcol
    _ ≤ sideExponent (S.rowCarrier (i + 1)) (S.colCarrier (i + 1)) :=
        le_max_right _ _

/-! ### The joint-satisfiability probe (NON-FIDELITY; see GAP-EXPOSED 3) -/

/-- **A probe carrier specification (NON-FIDELITY).**

Every legality guard of `FixedLevelCarriers.LevelCarrierSpec` holds, and the
outer entry data `(b_out, delta_U) = (1, 1/60)` is the banked audited point of
`EntryGates.directEntryGates_fires`, where `r_Q = 13` and `Q = 8192` -- so the
outer width here is the route's own accessor evaluated at a *legal* entry point,
not a numeral.  The two recorded pre-wrapper counts are **not** the paper's
`184` and `2^{22}`: this specification exists only to show that the hypothesis
bundle of `realizedSizeThread` is jointly satisfiable, and it claims no
legality of its own beyond the record's guards. -/
noncomputable def probeSpec : FixedLevelCarriers.LevelCarrierSpec where
  Awrap := fun _ => 1
  LP := fun _ => 1
  bout := fun _ => 1
  dU := fun _ => 1 / 60
  mN := fun _ => 1
  nN := fun _ => 1
  mBase := 1
  nBase := 1
  one_le_Awrap := fun _ => le_rfl
  one_le_LP := fun _ => le_rfl
  one_le_mN := fun _ => le_rfl
  one_le_nN := fun _ => le_rfl
  one_le_mBase := le_rfl
  one_le_nBase := le_rfl

/-- **The probe's base state (NON-FIDELITY).**

The all-zero incoming state.  It is *not* `SuccessorMajorant.seedState`; the
paper's own base appears in `realizedSizeThread_at_seed`. -/
def probeBase : LevelState where
  logRow := 0
  logCol := 0
  budgetD := 0
  budgetY := 0
  depth := 0
  scales := []

/-- **The probe's arrow.**

`a = 3` is the frozen Stage-1 floor of `07-one-level-construction.tex:118`, so
`q_1 = 2^3 - 2 = 6`; `log_2 s = 2` gives the guarded-source floor `s = 4`
(`04-guarded-source.tex:389`); `log_2 t_2 = 3` and `log_2 q_2 = 8` are the probe's
own, and claim no legality (`eq:t2-search` forces a vastly larger `t_2`).  The
two interlace exponents are **not** chosen: they are `probeSpec`'s own
`q_i` and `Q_i`. -/
noncomputable def probeArrow (i : ℕ) : ArrowSize :=
  levelArrow probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2) (fun _ => 3) i
    (by norm_num)

/-- **The probe's two interlace exponents, evaluated.**

`w_q = 1` from `eq:q-deltaU` at `A_wrap = L_P = 1`, and `r_Q = 13` from the
banked `EntryGates.directEntryGates_fires` at `(b_out, delta_U) = (1, 1/60)`.
Neither is assigned: both are the route's own accessors run at the probe's
inputs. -/
theorem probeArrow_widths (i : ℕ) :
    (probeArrow i).wq = 1 ∧ (probeArrow i).rQv = 13 := by
  refine ⟨rfl, ?_⟩
  change EntryGates.rQ 1 (1 / 60) = 13
  exact EntryGates.directEntryGates_fires.2.2.1

/-- **The probe's step bound, evaluated through the frozen displays.**

`Z_{0,N} = max{1, 0, floor log_2 3, 8, floor log_2 6, 2, 3} = 8`,
`zbar_{N,0} = 1 * (8 + 4(6+4) + 1) * 8 = 392`, and
`z_1^+ = max{2^13(1 + 392), 13 + 2 * 392} = 3219456`, all at `C_dim = 1` and
`n = 1`.  Every number is the frozen definitional chain evaluated in dependency
order; none is assigned. -/
theorem probeArrow_stepBound : (probeArrow 0).stepBound 1 0 1 = 3219456 := by
  have hw := probeArrow_widths 0
  have hq1 : (probeArrow 0).q1 = 6 := by decide
  have hdriver : (probeArrow 0).driver 0 1 = 8 := by
    change sizeDriver 0 1 (probeArrow 0).q1 8 2 3 = 8
    rw [hq1]
    simp only [sizeDriver, maxFrom_cons, maxFrom_nil]
    norm_num
  have hraw : (probeArrow 0).rawMajorant 1 0 1 = 392 := by
    change rawSideMajorant 1 (probeArrow 0).t2Val (probeArrow 0).sVal
      (probeArrow 0).q1 ((probeArrow 0).driver 0 1) = 392
    rw [hq1, hdriver]
    change rawSideMajorant 1 (2 ^ 3) (2 ^ 2) 6 8 = 392
    simp only [rawSideMajorant, dimMultiplicity]
    norm_num
  change sideStep (probeArrow 0).wq (probeArrow 0).rQv
    ((probeArrow 0).rawMajorant 1 0 1) = 3219456
  rw [hw.1, hw.2, hraw]
  simp only [sideStep]
  norm_num

/-- **Joint satisfiability of the whole `realizedSizeThread` bundle, with the
thread moving (BEYOND-PAPER probe; see GAP-EXPOSED 3).**

Every hypothesis of `realizedSizeThread` holds simultaneously at `k = 1`,
`C_dim = 1`, `n = 1` -- the strict seed row, both carrier rows of
`exp:E-14-raw`, and the recorded size-successor row of the reading warning -- and
the conclusion is delivered.  Two further conjuncts make the instance
non-vacuous: the thread **moves** (`z_0 = 0` but `8192 <= z_1`, so the induction
is not about a constant sequence), and `z_1` is the exact carrier readout, not a
free number.

The specification and the base state are NON-FIDELITY and claim no legality; the
recorded coefficient `C_dim = 1` is the frozen floor of
`eq:Cdim-literal-producer` (`C_dim >= 1`), and `n = 1` is the least source size
the envelope accessor accepts.  What this establishes is exactly what the
hypothesis-consistency rule demands: no `False` derives from the bundle. -/
theorem sizeThread_bundle_consistent :
    realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
        (fun _ => []) (fun _ => []) (fun _ => []) probeBase 0 <
      envE (cexp 0) 1 ∧
    (∀ i, i < 1 →
      probeSpec.mN i ≤ 2 ^ (probeArrow i).rawMajorant 1
          (realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
            (fun _ => []) (fun _ => []) (fun _ => []) probeBase i) 1 ∧
        probeSpec.nN i ≤ 2 ^ (probeArrow i).rawMajorant 1
          (realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
            (fun _ => []) (fun _ => []) (fun _ => []) probeBase i) 1) ∧
    (∀ i, i < 1 →
      realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
          (fun _ => []) (fun _ => []) (fun _ => []) probeBase i ≤
        envE (cexp i) 1 →
      (probeArrow i).stepBound 1
          (realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
            (fun _ => []) (fun _ => []) (fun _ => []) probeBase i) 1 ≤
        envE (cexp (i + 1)) 1) ∧
    (∀ i, i ≤ 1 →
      realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
          (fun _ => []) (fun _ => []) (fun _ => []) probeBase i ≤
        envE (cexp i) 1) ∧
    realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
        (fun _ => []) (fun _ => []) (fun _ => []) probeBase 0 = 0 ∧
    8192 ≤ realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
        (fun _ => []) (fun _ => []) (fun _ => []) probeBase 1 := by
  have hz0 : realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
      (fun _ => []) (fun _ => []) (fun _ => []) probeBase 0 = 0 := rfl
  have hell : ellN 1 = 3 := envelope_fires_nondegenerate.1
  have henv0 : envE (cexp 0) 1 = 2 ^ 3 ^ 3 := by
    simp only [envE, cexp_zero, hell]
  have henv1 : envE (cexp 1) 1 = 2 ^ 3 ^ 64 := by
    simp only [envE, cexp_succ, cexp_zero, hell]
  have hseed : realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
      (fun _ => []) (fun _ => []) (fun _ => []) probeBase 0 <
      envE (cexp 0) 1 := by
    rw [hz0, henv0]
    positivity
  have hraw : ∀ i, i < 1 →
      probeSpec.mN i ≤ 2 ^ (probeArrow i).rawMajorant 1
          (realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
            (fun _ => []) (fun _ => []) (fun _ => []) probeBase i) 1 ∧
        probeSpec.nN i ≤ 2 ^ (probeArrow i).rawMajorant 1
          (realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
            (fun _ => []) (fun _ => []) (fun _ => []) probeBase i) 1 := by
    intro i _
    exact ⟨Nat.one_le_two_pow, Nat.one_le_two_pow⟩
  have hsucc : ∀ i, i < 1 →
      realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
          (fun _ => []) (fun _ => []) (fun _ => []) probeBase i ≤
        envE (cexp i) 1 →
      (probeArrow i).stepBound 1
          (realizedZ probeSpec (fun _ => 3) (fun _ => 8) (fun _ => 2)
            (fun _ => []) (fun _ => []) (fun _ => []) probeBase i) 1 ≤
        envE (cexp (i + 1)) 1 := by
    intro i hi _
    interval_cases i
    rw [hz0, probeArrow_stepBound, henv1]
    calc (3219456 : ℕ) ≤ 2 ^ 22 := by norm_num
      _ ≤ 2 ^ 3 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hmain := realizedSizeThread probeSpec (fun _ => 3) (fun _ => 8)
    (fun _ => 2) (fun _ => 3) (fun _ => []) (fun _ => []) (fun _ => [])
    probeBase 1 1 1 (fun _ => by norm_num) hseed hraw hsucc
  refine ⟨hseed, hraw, hsucc, hmain.1, hz0, ?_⟩
  have hrowc : probeSpec.rowCarrier 1 = 2 ^ 8192 := by
    change carrierRowNext (probeSpec.q 0) (probeSpec.mN 0) (probeSpec.Q 0) =
      2 ^ 8192
    have hq : probeSpec.q 0 = 2 := rfl
    have hQ : probeSpec.Q 0 = 8192 := by
      change EntryGates.Qwidth 1 (1 / 60) = 8192
      exact EntryGates.directEntryGates_fires.2.2.2.1
    rw [carrierRowNext, hq, hQ]
    change (2 * 1 : ℕ) ^ 8192 = 2 ^ 8192
    rw [Nat.mul_one]
  rw [realizedZ_succ]
  calc (8192 : ℕ) = Nat.clog 2 (2 ^ 8192) := (Nat.clog_pow 2 8192 (by norm_num)).symm
    _ = Nat.clog 2 (probeSpec.rowCarrier 1) := by rw [hrowc]
    _ ≤ sideExponent (probeSpec.rowCarrier 1) (probeSpec.colCarrier 1) :=
        le_max_left _ _

end EthInapproximability.ParameterizedNP.SizeThreadWiring
