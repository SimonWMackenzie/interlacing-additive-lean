import EthInapproximability.ParameterizedNP.SuccessorComposition

/-!
# Parameterized NP route: the realized outgoing tuple and the live arrow induction

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`MATERIALIZE-001`** (the realization thread), and
**discharging** — for the four principal roots, which are exactly the fields the
state map reads — the canonical-inhabitation deferral that
`SuccessorMajorant`/`SuccessorComposition` registered for `SuccessorOutputs`.

`SuccessorComposition.lean` (tranche 65) composed the successor majorant at the
**incoming** state the paper constructs, but left the **outgoing** side a binder:
its GAP-EXPOSED 2 says "`O` is a binder in every theorem, and the one exhibited
`probeOutputs` is explicitly NON-FIDELITY", and its GAP-EXPOSED 4 says "Only the
first arrow is realized … arrows `r >= 1` need the previous arrow's realized
output as the incoming state".  This module builds that outgoing tuple as the
paper's own construction, evaluated through the banked definitional chains, and
therefore turns the whole state family from a binder into a live induction.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module traces

Opened first-hand this tranche, `14-final-consequence.tex:1547--1678`,
`thm:effective-materialization` (label line 1548), clause (c) at lines
1636--1652:

```
For every 0 <= i < k, the exact cross-level public-record equation
  Public_i = (N_V, N_E, d_0, d_1, m_i, n_i, R_i, gamma_e, Delta_e,
              D_i, Y_i, B(n), B(n)),
the canonical row and column equivalences defining
R_{i+1} = Can(T_i.Rnext), and the literal updates
  Y_{i+1} = Y_i + H_i,     D_{i+1} = D_i + H_i + 1,     b_i = b_{i+1} = B(n).
```

and the same three updates again inside the algorithm, at `14:1936--1942` (step
R5): "Append the canonical `Reindex` node `R_{i+1} = Can(T_i.Rnext)`, store its
row and column equivalences, and then perform, in this order,
`Y_{i+1} = Y_i + H_i`, `D_{i+1} = D_i + H_i + 1`.  This completes the loop body
before the next public record is formed."

The supporting displays are opened at their own anchors, never recalled:

1. `06-parameter-schedule.tex:2043--2052`, the four **principal** successor
   roots the outgoing tuple must carry:
   `ceil(log_2 m_next)`, `ceil(log_2 n_next)`, `D + H + 1`, `Y + H`, with the
   frozen preamble "Define, **without adding a new root**".  These are the four
   slots of `SuccessorOutputs` that `nextState` reads.
2. `06:2053--2062`, what `AuxOut(Cert_c)` contains: "the raw values in
   `ScalarOut_{c_i}`, `H`, `ceil(log_2 q_2)`, `ceil(log_2 N_2)`, the two
   incoming logarithmic side lengths, and the stated rational-code and physical
   cardinality binary lengths"; and, immediately, what it does **not** contain:
   "neither raw `q_2` nor raw `N_2`".
3. `12-iteration-specification.tex:260--265` (`eq:fixed-level-carriers`), the
   exact carrier recurrence `m_{i+1} = (q_i m_{N,i})^{Q_i}`,
   `n_{i+1} = Q_i (n_{N,i})^{q_i}`, reified in the banked
   `FixedLevelCarriers.LevelCarrierSpec.rowCarrier` / `.colCarrier`.
4. `07-one-level-construction.tex:43` and `10-direct-bridge.tex:516--518`,
   `H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`, reified in the banked
   `OneLevelCompletion.levelOverhead`.
5. `13-iteration-assembly.tex:398--400`, level-independence of `B(n)` and of the
   source-instance data, which is what `SuccessorOutputs.nextState` already
   encodes and what `realizedState_depth` / `_scales` read back out.

## What lands

* `outerExp`, `realizedOverhead` -- `r_{Q,i}` and `H_i` at a level, **evaluated**
  from the carrier specification's own depth and tolerance and from the level's
  Stage-1/source exponents.  Not assigned, and not a second copy of either
  interlace width: the inner exponent is the specification's `qExp` and the outer
  one its own `rQ`, so `q` and `Q` cannot be interchanged
  (`realizedOverhead_reads_both_widths_separately`).
* `realizedOutputs` -- the outgoing tuple of `14:1636--1652`, with all four
  principal roots and the source width **computed**: the two logarithmic side
  lengths are `clog_2` of the exact carrier recurrence at level `i+1`, the two
  budgets are the frozen literal updates at `H_i`, and `q_{2,i} = 2^{log_2
  q_{2,i}}` is the frozen power of two of `11-one-level-assembly.tex:820--821`.
  Only the three list fields are carried, because they are `AuxOut(Cert_c)` and
  the compiler is unbuilt (GAP-EXPOSED 1).
* `realizedState`, `realizedArrow` -- the **live arrow induction**: level `i+1`'s
  incoming state is level `i`'s realized outgoing tuple applied to level `i`'s
  state, so `realizedState_succ` holds by `rfl` and no state family is a binder.
* `realizedState_depth`, `realizedState_scales`, `realizedState_budgets`,
  `realizedState_sides`, `realizedState_gap` -- the realized chain read back
  against the banked ladders: `IterationAssembly.budgetY` / `.budgetD`, the exact
  carrier recurrence, and `kLevelAdditiveGap`'s `D_j = Y_j + j`.
* `realizedChain_underEnvelope` -- `SuccessorComposition.iteratedStateMajorant_of_rows`
  with `St` and `Out` **instantiated by the construction** and `hchain` discharged
  by `rfl`, and with the three `A_pre` state inputs read off the realized state
  rather than supplied as binders with membership hypotheses.
* `realizedChain_underEnvelope_at_seed` -- the same induction with the base state
  instantiated at the banked `SuccessorMajorant.seedState` and its envelope row
  **derived** from `seedState_underEnvelope` rather than assumed, so both ends of
  every arrow are the paper's own data.
* `realizedOutputs_successorMajorant_at_seed` -- the base arrow of
  `SuccessorComposition.successorMajorant_at_seed` with the outgoing tuple no
  longer a binder.
* `realizedChain_is_the_realization_record` -- the canonical-inhabitation
  statement: at a seed-anchored specification every state slot of the realized
  chain is the corresponding field of `14:1617--1652`, base included.
* `realizedChain_record_fires_at_paperCarrierSpec` -- that statement's
  specification hypothesis **discharged** at the banked
  `CoefficientTraversal.paperCarrierSpec`, i.e. at the paper's own carrier
  specification with the two Stage-4 counts evaluated through the protected
  duplicate, with the `184`- and `2^{22}`-fold blow-up rows carried so the
  discharge is content and not a renaming.
* `realizedChain_bundle_consistent` -- joint satisfiability of the whole live
  bundle together with its conclusion, at an arbitrary legal specification **and
  an arbitrary sparsity input `cle`**, whose envelope row is exhibited rather
  than dodged (through the new `le_envE_of_cutoff`).  BEYOND-PAPER in its
  coefficient rows, NON-FIDELITY in its base state, and audit-witnessed in the
  second-pass table `rows3`; nowhere else.  See GAP-EXPOSED 3.

## DEFINED-vs-FREE

* **DEFINED, reified and evaluated, never assigned a numeral:**
  `m_{i+1}`, `n_{i+1}` (`eq:fixed-level-carriers`, through the banked
  `LevelCarrierSpec.rowCarrier` / `.colCarrier`, whose `q_i` and `Q_i` are the
  banked `innerWidth` / `outerWidth`); `ceil(log_2 m_{i+1})`,
  `ceil(log_2 n_{i+1})` (`06:2049--2050`, taken as `Nat.clog 2` of those);
  `H_i` (`07:43`, through the banked `OneLevelCompletion.levelOverhead` at the
  specification's own two interlace exponents); `D_{i+1} = D_i + H_i + 1` and
  `Y_{i+1} = Y_i + H_i` (`14:1644--1648`); `q_{2,i} = 2^{log_2 q_{2,i}}`
  (`11-one-level-assembly.tex:820--821`, "the logarithms of `q_2, s, t_2` are
  integers because these widths are powers of two"); `b_i = b_{i+1} = B(n)`
  (`14:1649`, carried unchanged by the banked `SuccessorOutputs.nextState`); the
  base state (banked `SuccessorMajorant.seedState`); `B_pub`, `z_R`, `A_pre`,
  `L`, `c_j`, `n_val`,
  `E_c` (all banked, consumed by pin).
* **FREE in the paper itself, therefore binders:** the emission `Cert_c`
  (`thm:eff-ledger`, unbuilt -- `PARAM-001`), hence `AuxOut(Cert_c)`, hence the
  three list fields `auxWidths`, `invTolerances`, `robustDepths`; the registry's
  per-root coefficient table, which `06:1628--1631` forbids a formalizer to
  supply; the sparsity input `cle_i = clog_2(|E|+2)` (`06:114`, the fifth branch
  of `eq:s-choice`'s `A_pre`), which the paper **defines** but only out of
  source-graph data no Lean module produces, so it stays a binder carrying its
  own frozen bound `cle_i <= E_{c_i}(n)` and is never instantiated -- in
  particular never at the unattainable `0`, since `|E| + 2 >= 2` forces
  `clog_2(|E| + 2) >= 1`; the Stage-1 exponent `a_i` and the
  source exponents `log_2 q_{2,i}`, `log_2 s_i`, which are produced by the
  pre-family part of the traversal (`14:1878--1889`) and by the guarded source,
  neither of which is in Lean; the Section-8 reservoir data behind
  `m_{N,i}, n_{N,i}`, held level-uniformly by the banked
  `CoefficientTraversal.paperCarrierSpec` (its GAP-EXPOSED 5, inherited
  unchanged).

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate read in place.

**One reader item is claimed, by one declaration, not previously assigned.**

* `C-effectivity-details.tex:134--138` -- "For every encoded source pair
  `(n,G)` in the large-carrier output domain of `thm:paper-source-realization`,
  `A_realize` writes a finite descriptor containing the full-cube seed, the
  `L(n)` successful one-level traces, their exact budget updates and carrier
  maps, and the final padding maps." -- the reader's statement of what the
  realization record contains, claimed by
  `realizedChain_is_the_realization_record`, which delivers exactly the
  seed-anchored base, the per-level budget updates and the per-level carrier
  readouts (and claims nothing about the padding maps, which stay `PAD-001`).
  It is `thm:paper-materialization` **statement** text, inside `\begin{theorem}`
  (`:126`, `\label{thm:paper-materialization}` on `:127`) and well before
  `\begin{proof}`; so it is statement text, not proof prose.  A sweep of every
  module under `src/EthInapproximability/ParameterizedNP/` for
  `C-effectivity-details.tex` citations returns only `:82--84` (cited by
  `EnvelopeRealization` **and** `CoefficientTraversal`) and `:86--88` (cited by
  `EnvelopeRealization`), neither of which meets the interval `134--138`.

**No reader item is claimed by any other declaration here, and the reason is
recorded.**  The reader's own budget display `eq:paper-budget-update`
(`05-iteration.tex`, label line 116, display lines 112--117) is **already
assigned** to the banked `IterationAssembly.iterationBudgetLadder`, and
`05-iteration.tex:129--133` to `.iterationClosedBudgets`; re-citing either would
be the double assignment the rule forbids, so `realizedOutputs` and
`realizedState_budgets` claim nothing and consume those endpoints by pin.
`05-iteration.tex:109` (`H_i = K_i + r_{q,i} + r_{Q,i}`) is already assigned to
`OneLevelCompletion.levelOverhead`, so `realizedOverhead` claims nothing.
`05-iteration.tex:212--215` is already assigned to
`SuccessorComposition.successorMajorant_of_rows`, so the two composition
theorems here claim nothing.  The reader prints no successor-root display and no
`AuxOut` at all: a search of all nine reader files for `AuxOut`,
`\mathsf{Roots}` and `m_{\mathrm{next}}` returns no occurrence.

Crosswalk: no new row; the assignment stays in the existing row **12, "Slow
iteration, padding, and ETH interface"**, of `READER_CROSSWALK.md`.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is a
  transcription of a frozen display, a general property of that transcription, or
  a composition of banked results.  No communication-complexity lemma is
  introduced, adapted or re-proved, and no banked module is edited.
* Consumed by pin, never restated: `IterationAssembly.cexp`, `.nval`, `.envE`,
  `.depthB`, `.budgetY`, `.budgetD`, `.budget_closed_forms`, `.kLevelAdditiveGap`,
  `.carrierRowNext`, `.carrierColNext`;
  `EntryGates.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`;
  `OneLevelCompletion.levelOverhead`;
  `FixedLevelCarriers.LevelCarrierSpec`, `.qExp`, `.q`, `.Q`, `.rowCarrier`,
  `.colCarrier`, `.SeedAnchored`, `.seedMatrix`, `.fixedLevelCarriers`,
  `.widths_are_not_interchangeable`, `.carriers_two_le_succ`;
  `SuccessorMajorant.LevelState`, `.SuccessorOutputs`, `.nextState`,
  `.levelState_underEnvelope_iff`, `.seedState`, `.seedState_underEnvelope`,
  `.seedRowSide_is_the_paper_carrier`;
  `EnvelopeRealization.CutoffEmission`, `.absorbedCoeff`, `.dExp`, `.eExp`,
  `.normalizedL`, `.one_le_nval`;
  `CoefficientTraversal.CoeffRow`, `.RowChecked`, `.passCsize`, `.passValues`;
  `SuccessorComposition.publicBudgetMax`, `.seedZR`, `.seedZR_eq`,
  `.publicBudgetMax_seedState`, `.successorMajorant_at_seed`,
  `.iteratedStateMajorant_of_rows`;
  `BridgeOutputEquality.rowsCard`, `.colsCard`.
* Imports: `SuccessorComposition` only, hence transitively `CoefficientTraversal`,
  `EnvelopeRealization`, `SuccessorMajorant`, `SizePropagation`,
  `FixedLevelCarriers`, `IterationAssembly`, `OneLevelCompletion`,
  `ParameterSchedule`, `EntryGates` and `EthInapproximability.Prelude`, hence
  `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  **`LegacyNPCC.Stage12` is not imported**, so no declaration reaches the cited
  AGHP balanced-family axiom and no opt-in ledger note is owed; `EXPANDER-001`
  has no contact with this module.
* External adapters: none.  No new `axiom`, no opaque certificate.
* Axiom surface (Appendix D, and `#print axioms`): at most `propext`,
  `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **No new structure.**  This module introduces no record at all.  The outgoing
  tuple is a `def` producing the **banked** `SuccessorOutputs`, so no field can
  be added to the paper's own record, and every remaining input is an explicit
  binder rather than a premise bundle.
* **The desired conclusions stay out of the data.**  `realizedOutputs` carries no
  envelope, complexity, robustness or promise field -- by the banked record's
  design it has none -- and every bound it satisfies is a theorem about it.  The
  chain `realizedState` likewise carries only state slots.
* **Both interlace widths stay distinct.**  `q_i` enters only as the banked
  `LevelCarrierSpec.qExp` / `.q` and `Q_i` only as `outerExp` / `.Q`; the
  overhead reads them in different argument positions and the carriers in
  exchanged roles, and `realizedOverhead_reads_both_widths_separately` refutes
  the merge in the kernel.
* **Every comparison is transcribed as printed.**  The literal updates of
  `14:1644--1648` are equalities, not inequalities; the majorant rows stay
  non-strict; the one strict row of the passage is not restated here.
* **Statement poles.**  `realizedState_budgets_strictly_increase` shows the
  realized chain is not a constant sequence whenever a level has positive
  overhead, so the induction is not vacuously about a fixed point;
  `realizedOutputs_is_not_the_all_zero_tuple` separates the realized tuple from
  the degenerate record at the same legal inputs; and
  `realizedOverhead_reads_both_widths_separately` is the width pole.

## GAP-EXPOSED

1. **The compiler is still not built, so the three list fields stay carried.**
   `AuxOut(Cert_c)` of `06:2053--2062` is produced by `thm:eff-ledger`'s
   emission, which has no Lean declaration.  `realizedOutputs` therefore takes
   `auxWidths`, `invTolerances` and `robustDepths` as level-indexed inputs and
   asserts nothing about them; `PARAM-001` stays open, and nothing below is an
   axiom.
2. **The canonical-inhabitation deferral is discharged exactly as far as the
   principal roots reach, and not one field further.**  `SuccessorOutputs.nextState`
   (`SuccessorMajorant.lean:474--481`) reads only `logRow`, `logCol`, `budgetD`,
   `budgetY`; all four are computed here from the paper's own displays, so the
   **state** side of the deferral is discharged and `realizedChain_underEnvelope`
   is a genuine induction over the paper's construction.  The **tuple** side is
   discharged only in those four slots plus `srcWidth`; the three `AuxOut` list
   slots remain registered against `PARAM-001`.  This is a narrowing of
   `SuccessorComposition`'s GAP-EXPOSED 2 and 4, not their closure, and the
   NON-FIDELITY probe there is not what discharges anything here.
3. **The consistency probe's coefficient rows are BEYOND-PAPER.**
   `06:1628--1631` states that no formalizer supplies a registry coefficient, so
   `chainRow`'s pair `(C_u, d_u) = (val(u), 0)` is our value and claims no
   legality; it audits our encoding at a point the paper never prints.  It is
   strictly weaker evidence than the paper's application point and stands in for
   nothing.  What it does establish is what the hypothesis-consistency rule
   demands: the live bundle is jointly satisfiable together with its conclusions,
   so no `False` derives from it.
   **Its base state is the audit base, not the paper's seed, and the reason is
   itself a frozen fact.**  With the outgoing tuples realized, the recorded
   coefficients depend on the tuples, the tuples on the base state, and the
   eligible source size on the recorded coefficients; at the paper's own base the
   base state depends on `n` as well, so the three choices close a cycle.  The
   paper breaks that cycle in the one place a formalizer cannot: `thm:eff-ledger`
   clause (b) fixes `Cert_c` -- hence every recorded coefficient -- **before** the
   recursion and before `n` is chosen.  Until that emission exists in Lean, the
   fully realized probe is available only at a base fixed in advance, and the
   residual consistency risk for `realizedChain_underEnvelope_at_seed` is confined
   to the three `PARAM-001` slots, since its base envelope row is a banked
   theorem.
4. **The Section-8 reservoir data behind `m_{N,i}`, `n_{N,i}` is still
   level-uniform.**  A `LevelCarrierSpec` records those two counts per level, and
   the banked `CoefficientTraversal.paperCarrierSpec` evaluates them through the
   paper's own protected duplicate at **one** choice of reservoir data.  Building
   level `i`'s data from level `i`'s incoming matrix is `STAGE1-001 .. WRAP-001`,
   none of which is in Lean.  The chain here is therefore stated over an arbitrary
   legal specification, which covers that instance but does not build it.
5. **Nothing about the machines is claimed.**  `A_bal`, `A_balEntry`,
   `A_realize`, `A_entry`, `A_materialize`, the descriptor codec, the entry
   evaluator `Eval`, the row-major streaming materializer, the padding maps
   `pi_X, pi_Y`, the exponent `e(n)`, the side `S_n`, the bit count `T_n` and the
   runtime bound `eq:materializer-exact-runtime` have no declaration here.  This
   module realizes the **record's level data** of clause (c) and nothing else.
6. **No route completion is claimed.**  Stages 1--4, the slow clock beyond what
   is banked, the padded square matrix and the ETH consequence are untouched.
-/

namespace EthInapproximability.ParameterizedNP.EffectiveMaterialization

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.EnvelopeRealization
open EthInapproximability.ParameterizedNP.CoefficientTraversal
open EthInapproximability.ParameterizedNP.SuccessorComposition

/-! ## Part 1: the two evaluated scalars of a realized level

`14-final-consequence.tex:1636--1652` needs one integer the incoming state does
not carry, namely `H_i`; everything else in the clause is either an incoming
slot or a carrier readout. -/

/-- **`r_{Q,i}`, the outer bridge exponent at a level, read off the
specification's own data.**

`10-direct-bridge.tex:51` fixes `Q = 2^{r_Q}` and the banked
`FixedLevelCarriers.LevelCarrierSpec.Q` is `EntryGates.Qwidth` at the level's
requested depth and deletion tolerance.  This is that exponent, so the level has
exactly one outer width and no second one is introduced.

Reader counterpart: **none claimed**; `04-bridge.tex:94` is already assigned to
`EntryGates.Qwidth`.  General in the specification and the level. -/
noncomputable def outerExp (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) : ℕ :=
  EntryGates.rQ (S.bout i) (S.dU i)

/-- **Aux 1 (the outer exponent really is the specification's outer width).**

`Q_i = 2^{r_{Q,i}}` at every level, by the banked `EntryGates.Qwidth_eq_two_pow`.
Recorded so that no later proof reopens `Qwidth`.  General. -/
theorem two_pow_outerExp (S : FixedLevelCarriers.LevelCarrierSpec) (i : ℕ) :
    2 ^ outerExp S i = S.Q i := rfl

/-- **`H_i = a_i + log_2 q_{2,i} + log_2 s_i + log_2 q_i + log_2 Q_i`,
evaluated.**

`07-one-level-construction.tex:43`, restated at `10-direct-bridge.tex:516--518`,
through the banked `OneLevelCompletion.levelOverhead`, which is consumed by pin
and never restated.

**Both interlace exponents come from the specification**, not from a second
record: the inner one is the banked `LevelCarrierSpec.qExp` of
`eq:q-deltaU` and the outer one is `outerExp` above.  Only the three quantities
the carrier specification genuinely does not carry -- the Stage-1 exponent `a_i`
of `eq:stage1-scales` and the two source exponents `log_2 q_{2,i}`, `log_2 s_i`
of `13:529--537` -- are inputs, and they are explicit binders because the
pre-family traversal that computes them (`14:1878--1889`) is `PARAM-001`.

Reader counterpart: **none claimed**; `05-iteration.tex:109` is already assigned
to `OneLevelCompletion.levelOverhead`.  General in the specification, in the
three exponent families and in the level. -/
noncomputable def realizedOverhead (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (i : ℕ) : ℕ :=
  OneLevelCompletion.levelOverhead (aE i) (q2E i) (sE i) (S.qExp i) (outerExp S i)

/-- **Aux 2 (the overhead is the printed five-term sum).**

`H_i = a_i + log_2 q_{2,i} + log_2 s_i + log_2 q_i + log_2 Q_i` read off the
banked definition, so the transcription is visible in the kernel rather than
hidden behind a name.  General. -/
theorem realizedOverhead_eq (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (i : ℕ) :
    realizedOverhead S aE q2E sE i =
      aE i + q2E i + sE i + S.qExp i + outerExp S i := rfl

/-- **Statement pole: the carriers are what tell the two interlace widths apart,
and the overhead is not.**

`02-mechanical-contract.tex:771--775` and `eq:fixed-level-carriers` keep `q_i`
and `Q_i` apart; a module that merged them would still typecheck, so the
separation has to be exhibited.  Two kernel facts at once, and they point in
**opposite** directions:

* at the audit point where the recorded pre-wrapper counts are one, the successor
  column carrier is **strictly** below the successor row carrier -- the banked
  `FixedLevelCarriers.widths_are_not_interchangeable` -- so no single carrier
  equation, and no equation reading the two widths in the same role, could have
  produced the pair;
* the overhead `H_i` of `07:43` is a **sum** of the five exponents, hence
  symmetric in its last two arguments.  So `H_i` is *not* where the two widths
  are told apart, and a reader must not take its five printed summands as
  evidence that they are distinguished.  Recorded rather than left implicit,
  because the natural conjecture "the two occurrences of an interlace width in
  `H_i` cannot be swapped" is **false** here and would be an over-strong pole.

General in the specification, the three exponent families and the level. -/
theorem realizedOverhead_reads_both_widths_separately
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ) (i : ℕ)
    (hm : S.mN i = 1) (hn : S.nN i = 1) :
    S.colCarrier (i + 1) < S.rowCarrier (i + 1) ∧
      OneLevelCompletion.levelOverhead (aE i) (q2E i) (sE i) (S.qExp i)
          (outerExp S i) =
        OneLevelCompletion.levelOverhead (aE i) (q2E i) (sE i) (outerExp S i)
          (S.qExp i) := by
  refine ⟨FixedLevelCarriers.widths_are_not_interchangeable S i hm hn, ?_⟩
  simp only [OneLevelCompletion.levelOverhead, OneLevelCompletion.stage4Overhead]
  omega

/-! ## Part 2: the realized outgoing tuple

`14-final-consequence.tex:1636--1652`, clause (c), together with the four
principal successor roots of `06-parameter-schedule.tex:2043--2052`. -/

/-- **The outgoing tuple of one realized arrow, built by the paper's own
construction.**

Every slot that `06:2043--2052` names a **principal** root is *computed*:

* `logRow = ceil(log_2 m_{i+1})` and `logCol = ceil(log_2 n_{i+1})`, where
  `m_{i+1}` and `n_{i+1}` are the exact carrier recurrence of
  `eq:fixed-level-carriers` (`12:260--265`) through the banked
  `LevelCarrierSpec.rowCarrier` / `.colCarrier`.  `14:1936--1938` fixes that the
  next public matrix is `R_{i+1} = Can(T_i.Rnext)`, and canonical reindexing
  preserves both cardinalities (`13:555--556`), so these are the next level's own
  logarithmic side lengths and not a majorant of them.
* `budgetD = D_i + H_i + 1` and `budgetY = Y_i + H_i`, the literal updates of
  `14:1644--1648`, at the incoming state's own two budget slots and at the
  evaluated `realizedOverhead`.
* `srcWidth = 2^{log_2 q_{2,i}}`, because `11-one-level-assembly.tex:820--821`
  records that `q_2` is a power of two, so the width is the exponential of the
  exponent the schedule carries and is never confused with it (`06:1703--1704`).

The three list slots are `AuxOut(Cert_c)` of `06:2053--2062` and are **carried**,
because the emission that produces them is unbuilt (GAP-EXPOSED 1).  They are
level-indexed inputs and nothing below asserts anything about their contents.

No conclusion sits in this data: the banked `SuccessorOutputs` has no envelope,
complexity, robustness or promise field, and every bound satisfied by this value
is a theorem about it.

Reader counterpart: **none claimed**; the reader's budget display
`eq:paper-budget-update` is already assigned to
`IterationAssembly.iterationBudgetLadder`.

General in the specification, the three exponent families, the three `AuxOut`
families, the incoming state and the level. -/
noncomputable def realizedOutputs (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (St : LevelState) (i : ℕ) :
    SuccessorOutputs where
  auxWidths := auxW i
  logRow := Nat.clog 2 (S.rowCarrier (i + 1))
  logCol := Nat.clog 2 (S.colCarrier (i + 1))
  invTolerances := invT i
  robustDepths := robD i
  budgetD := St.budgetD + realizedOverhead S aE q2E sE i + 1
  budgetY := St.budgetY + realizedOverhead S aE q2E sE i
  srcWidth := 2 ^ q2E i

/-- **Aux 3 (the two logarithmic side lengths are the carrier recurrence, read
through `clog`).**

`eq:fixed-level-carriers` spelled out at the realized tuple: the row slot is
`ceil(log_2 ((q_i m_{N,i})^{Q_i}))` and the column slot
`ceil(log_2 (Q_i (n_{N,i})^{q_i}))`, with the two widths in exchanged roles.
This is the readout that makes `logRow`/`logCol` evaluated rather than assigned.
General. -/
theorem realizedOutputs_sides (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (St : LevelState) (i : ℕ) :
    (realizedOutputs S aE q2E sE auxW invT robD St i).logRow =
        Nat.clog 2 ((S.q i * S.mN i) ^ S.Q i) ∧
      (realizedOutputs S aE q2E sE auxW invT robD St i).logCol =
        Nat.clog 2 (S.Q i * S.nN i ^ S.q i) := ⟨rfl, rfl⟩

/-- **Aux 4 (the source width's logarithm is a requested root, its value is
not).**

`06:1703--1704`, "only `log_2 q_2` appears among the new logarithmic side
lengths", and `06:2057--2058`, `AuxOut` "contains neither raw `q_2` nor raw
`N_2`".  So the tuple's `srcWidth` recovers its own exponent under `clog_2`, and
whenever the compiler's `AuxOut` list contains that exponent -- which
`06:2054--2057` states it does -- the membership row the traversal consumes is
available without a second free bound.  General in every argument. -/
theorem realizedOutputs_srcLog (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (St : LevelState) (i : ℕ) :
    Nat.clog 2 (realizedOutputs S aE q2E sE auxW invT robD St i).srcWidth =
      q2E i := by
  simp only [realizedOutputs]
  exact Nat.clog_pow 2 _ one_lt_two

/-- **Aux 5 (`log_2 q_{2,i}` is a majorised root as soon as the emission records
it).**

The paper's own sentence `06:2054--2057` -- `AuxOut(Cert_{c_i})` "contains … `H`,
`ceil(log_2 q_2)`, `ceil(log_2 N_2)`" -- turned into the membership the
traversal's source-width row needs.  Stated as an implication, because supplying
the emission is `PARAM-001`: nothing here asserts that a compiler emits that
list.  General. -/
theorem realizedOutputs_srcLog_mem (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (St : LevelState) (i : ℕ)
    (hq2 : q2E i ∈ auxW i) :
    Nat.clog 2 (realizedOutputs S aE q2E sE auxW invT robD St i).srcWidth ∈
      (realizedOutputs S aE q2E sE auxW invT robD St i).majorised := by
  rw [realizedOutputs_srcLog]
  simp only [SuccessorOutputs.majorised, realizedOutputs, List.append_assoc,
    List.mem_append]
  exact Or.inl hq2

/-- **Statement pole: the realized tuple is not the degenerate record.**

The all-zero `SuccessorOutputs` satisfies every majorant row vacuously, so a
statement proved only for it would be empty.  At legal parameters the realized
tuple avoids it on **two independent slots**: its complexity budget is strictly
larger than the incoming one, by the frozen `+1` of `14:1647` alone, and its
source width is a positive power of two.  General in the specification, the
exponent families, the list families, the incoming state and the level. -/
theorem realizedOutputs_is_not_the_all_zero_tuple
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (St : LevelState) (i : ℕ) :
    St.budgetD < (realizedOutputs S aE q2E sE auxW invT robD St i).budgetD ∧
      0 < (realizedOutputs S aE q2E sE auxW invT robD St i).srcWidth := by
  refine ⟨?_, ?_⟩
  · simp only [realizedOutputs]
    omega
  · simpa only [realizedOutputs] using Nat.two_pow_pos (q2E i)

/-! ## Part 3: the live arrow induction

`14-final-consequence.tex:1943`, "This completes the loop body before the next
public record is formed": level `i+1`'s incoming state is level `i`'s outgoing
tuple applied to level `i`'s state. -/

/-- **The realized state family.**

The loop of `14:1875--1943` as a recursion: `realizedState … 0` is the incoming
base state, and every later state is the previous arrow's realized outgoing
tuple applied to the previous state, through the banked
`SuccessorOutputs.nextState` (which carries `b_i = b_{i+1} = B(n)` and the
source-instance scales unchanged, `14:1649` and `13:398--400`).

This is the point of the module: `SuccessorComposition`'s state family `St` was a
binder with a chaining hypothesis, and here it is the construction itself, so the
chaining hypothesis becomes `rfl`.

Reader counterpart: **none claimed** for this definition; the reader item is
claimed by `realizedChain_is_the_realization_record` below.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level. -/
noncomputable def realizedState (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) :
    ℕ → LevelState
  | 0 => S₀
  | i + 1 =>
      (realizedOutputs S aE q2E sE auxW invT robD
          (realizedState S aE q2E sE auxW invT robD S₀ i) i).nextState
        (realizedState S aE q2E sE auxW invT robD S₀ i)

/-- **The realized outgoing tuple at arrow `i`**, i.e. the tuple of
`realizedOutputs` read at the state the chain has actually reached.  This is the
`Out` family `SuccessorComposition.iteratedStateMajorant_of_rows` quantifies
over, no longer a binder.  General. -/
noncomputable def realizedArrow (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    SuccessorOutputs :=
  realizedOutputs S aE q2E sE auxW invT robD
    (realizedState S aE q2E sE auxW invT robD S₀ i) i

/-- **Aux 6 (the chaining hypothesis is an identity).**

`14:1943` read in the kernel: the state after arrow `i` **is** the successor
state of arrow `i`'s realized tuple.  In `SuccessorComposition` this was the
hypothesis `hchain`; here it holds by `rfl`, which is exactly what turns the
banked induction from a statement about an assumed family into a statement about
the construction.  General. -/
theorem realizedState_succ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    realizedState S aE q2E sE auxW invT robD S₀ (i + 1) =
      (realizedArrow S aE q2E sE auxW invT robD S₀ i).nextState
        (realizedState S aE q2E sE auxW invT robD S₀ i) := rfl

/-- **Aux 7 (the common depth is level-independent).**

`14:1649`, "`b_i = b_{i+1} = B(n)`", and `13:398--400`, "the common depth `B(n)`
… are level-independent", read off the whole realized chain by induction.
General in every argument. -/
theorem realizedState_depth (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    (realizedState S aE q2E sE auxW invT robD S₀ i).depth = S₀.depth := by
  induction i with
  | zero => rfl
  | succ m ih => exact ih

/-- **Aux 8 (the source-instance scales are level-independent).**

The same frozen sentence `13:398--400` for "the original variable count `n`, the
reduced source graph, the universal constants".  General. -/
theorem realizedState_scales (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    (realizedState S aE q2E sE auxW invT robD S₀ i).scales = S₀.scales := by
  induction i with
  | zero => rfl
  | succ m ih => exact ih

/-- **Aux 9 (the realized budgets are the banked ladder).**

`eq:iterated-budgets` as the realization writes it (`14:1644--1648`): the chain's
two budget slots at level `i` are exactly `IterationAssembly.budgetY` and
`.budgetD` of the base budgets at the overhead sequence `H_i = realizedOverhead`.

This is the round-trip property that makes the recursion an *evaluation* of the
banked definitional chain rather than a second, parallel definition of it.
General in every argument. -/
theorem realizedState_budgets (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    (realizedState S aE q2E sE auxW invT robD S₀ i).budgetY =
        budgetY S₀.budgetY (realizedOverhead S aE q2E sE) i ∧
      (realizedState S aE q2E sE auxW invT robD S₀ i).budgetD =
        budgetD S₀.budgetD (realizedOverhead S aE q2E sE) i := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨hY, hD⟩ := ih
    refine ⟨?_, ?_⟩
    · change (realizedState S aE q2E sE auxW invT robD S₀ m).budgetY +
        realizedOverhead S aE q2E sE m = _
      rw [hY, budgetY_succ]
    · change (realizedState S aE q2E sE auxW invT robD S₀ m).budgetD +
        realizedOverhead S aE q2E sE m + 1 = _
      rw [hD, budgetD_succ]

/-- **Aux 10 (the closed forms and the exact `k`-gap survive the realization).**

`expi:E-03-closed` and `eq:fixed-level-closed-budgets` through the banked
`IterationAssembly.budget_closed_forms`, plus `kLevelAdditiveGap`'s exact
separation `D_j = Y_j + j` under the frozen seed identity `D_0 = Y_0` of clause
(a) (`14:1619`, "`D_0 = Y_0 = comp F_{B(n)}`").  Nothing is re-proved: the
realized chain is fed into the banked ladders.  General in every argument, under
the frozen base identity. -/
theorem realizedState_gap (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (hbase : S₀.budgetD = S₀.budgetY) (j : ℕ) :
    (realizedState S aE q2E sE auxW invT robD S₀ j).budgetY =
        S₀.budgetY + ∑ i ∈ Finset.range j, realizedOverhead S aE q2E sE i ∧
      (realizedState S aE q2E sE auxW invT robD S₀ j).budgetD =
        (realizedState S aE q2E sE auxW invT robD S₀ j).budgetY + j := by
  obtain ⟨hY, hD⟩ := realizedState_budgets S aE q2E sE auxW invT robD S₀ j
  obtain ⟨hYc, -⟩ :=
    budget_closed_forms S₀.budgetY S₀.budgetD (realizedOverhead S aE q2E sE) j
  refine ⟨by rw [hY, hYc], ?_⟩
  rw [hY, hD]
  exact kLevelAdditiveGap S₀.budgetY S₀.budgetD (realizedOverhead S aE q2E sE)
    hbase j

/-- **Aux 11 (every later state's two side lengths are the carrier readout).**

`14:1936--1938` composed with `eq:fixed-level-carriers`: after arrow `i` the
public matrix is `R_{i+1} = Can(T_i.Rnext)` and its two logarithmic side lengths
are `clog_2` of the exact successor carriers.  Holds by `rfl`, which is the point:
the state slots are not stored numbers but the evaluated recurrence.  General. -/
theorem realizedState_sides (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    (realizedState S aE q2E sE auxW invT robD S₀ (i + 1)).logRow =
        Nat.clog 2 (S.rowCarrier (i + 1)) ∧
      (realizedState S aE q2E sE auxW invT robD S₀ (i + 1)).logCol =
        Nat.clog 2 (S.colCarrier (i + 1)) := ⟨rfl, rfl⟩

/-- **Statement pole: the realized chain is not a constant sequence.**

A green induction over a family that never moves would prove nothing.  Whenever a
level has positive overhead -- and `H_i` is a sum of five exponents, so this is
the generic case, not a contrivance -- the complexity budget **strictly**
increases at that level, and by the frozen `+1` of `14:1647` it increases even at
zero overhead.  So the realized states at `i` and `i+1` are distinct records.
General in every argument. -/
theorem realizedState_budgets_strictly_increase
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    (realizedState S aE q2E sE auxW invT robD S₀ i).budgetD <
        (realizedState S aE q2E sE auxW invT robD S₀ (i + 1)).budgetD ∧
      realizedState S aE q2E sE auxW invT robD S₀ i ≠
        realizedState S aE q2E sE auxW invT robD S₀ (i + 1) := by
  have hlt : (realizedState S aE q2E sE auxW invT robD S₀ i).budgetD <
      (realizedState S aE q2E sE auxW invT robD S₀ (i + 1)).budgetD := by
    change _ < (realizedState S aE q2E sE auxW invT robD S₀ i).budgetD +
      realizedOverhead S aE q2E sE i + 1
    omega
  refine ⟨hlt, ?_⟩
  intro h
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-! ## Part 4: the two `A_pre` state inputs the chain supplies itself

`06-parameter-schedule.tex:47--55`, read at a state of the realized chain rather
than at a binder. -/

/-- **`z_R = max{ceil(log_2 |Rows(R)|), ceil(log_2 |Cols(R)|)}` at a state.**

`06-parameter-schedule.tex:51--55`, the fourth branch of `eq:s-choice`'s `A_pre`.
At a realized level the state's two side slots **are** those two ceiling
logarithms (`realizedState_sides`), so this is the frozen display evaluated and
not a majorant of it.  A `def` over the banked record, never a stored field.

Reader counterpart: **none**; the reader prints no `z_R`.  General. -/
def stateZR (St : LevelState) : ℕ := max St.logRow St.logCol

/-- **Aux 12 (`z_R` is a quantity of its own state).**

`13:292--294` lists the two logarithmic side lengths among the state's
quantities, and a maximum of two of them is one of them.  This is what lets the
composition below supply the third `A_pre` input from the chain itself instead of
taking it as a binder with a membership hypothesis.  General in the state. -/
theorem stateZR_mem (St : LevelState) : stateZR St ∈ St.quantities := by
  rcases le_total St.logRow St.logCol with h | h
  · rw [stateZR, max_eq_right h]
    simp [LevelState.quantities]
  · rw [stateZR, max_eq_left h]
    simp [LevelState.quantities]

/-- **Aux 13 (`B_pub` is a quantity of its own state).**

`06:48--50` reads `B_pub = max{D, Y}` off the two public budgets, both of which
`13:292--294` lists among the state's quantities.  The companion of `Aux 12` for
the second `A_pre` state input.  General in the state. -/
theorem publicBudgetMax_mem (St : LevelState) :
    publicBudgetMax St ∈ St.quantities := by
  rcases le_total St.budgetD St.budgetY with h | h
  · rw [publicBudgetMax, max_eq_right h]
    simp [LevelState.quantities]
  · rw [publicBudgetMax, max_eq_left h]
    simp [LevelState.quantities]

/-- **Aux 14 (`z_R` at the base is the banked seed evaluation).**

`SuccessorComposition.seedZR` evaluates `06:51--55` at the paper's own full-cube
seed and gets `q_seed(n)`; the same display read at the banked
`SuccessorMajorant.seedState` gets the same integer, because the seed state's row
slot is `q_seed(n)` and its column slot is `a_seed(n) <= q_seed(n)`.  So the
chain's own `A_pre` input at level zero is the one `SuccessorComposition` already
computed, and no second convention is introduced.  General in `n >= 1` and the
scales. -/
theorem stateZR_seedState (n : ℕ) (hn : 1 ≤ n) (scales : List ℕ) :
    stateZR (seedState n scales) = seedZR n := by
  rw [seedZR_eq n hn, stateZR]
  change max (qSeed n) (aSeed n) = qSeed n
  exact max_eq_left (Nat.le_of_lt (aSeed_lt_qSeed n hn))

/-! ## Part 5: the live arrow induction under the envelope

`13-iteration-assembly.tex:291--315` through
`SuccessorComposition.iteratedStateMajorant_of_rows`, with the state family and
the outgoing tuples instantiated by Part 3. -/

/-- **The reading warning's state induction, run over the paper's own
construction.**

The banked `SuccessorComposition.iteratedStateMajorant_of_rows` is consumed by
pin, with three things no longer binders:

* `St` is `realizedState` and `Out` is `realizedArrow`, so the family really is
  the chain the realization builds;
* `hchain` is discharged by `rfl` (`realizedState_succ`) rather than assumed;
* the three `A_pre` state inputs are read off the chain itself -- the depth slot,
  `publicBudgetMax` and `stateZR` -- so the three membership hypotheses are
  discharged internally by `Aux 12`, `Aux 13` and the state's own depth slot.

The base state stays an explicit binder here, with its envelope row as an
explicit hypothesis, because the induction of `13:292--296` is stated for an
arbitrary incoming state; `realizedChain_underEnvelope_at_seed` instantiates it
at the paper's own base and **derives** that hypothesis.

What remains hypothesis is exactly what `PARAM-001` owes: the emission `Em`, the
per-arrow traversal tables `rows`, `rows3`, their checked rows, the emitted
absorbed tuple, and the identification `hmaj` of the realized tuple's majorised
list with the traversal's value list.  The sparsity input `cle` is source-graph
data and travels with its own frozen bound.

Reader counterpart: **none claimed**; `05-iteration.tex:212--215` is already
assigned to `SuccessorComposition.successorMajorant_of_rows`.

General in the specification, the exponent families, the `AuxOut` families, the
emission, both traversal tables, the sparsity input, the source size, the arrow
count and the base state. -/
theorem realizedChain_underEnvelope (Em : CutoffEmission)
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (rows : ℕ → List CoeffRow)
    (rows3 : ℕ → List ℕ) (cle : ℕ → ℕ) (n k : ℕ) (S₀ : LevelState) (hn : 1 ≤ n)
    (hseed : S₀.UnderEnvelope (cexp 0) n)
    (hnval : nval Em.nStep k ≤ n)
    (habs : ∀ i, i < k →
      (absorbedCoeff (passCsize (rows i) (rows3 i)) (cexp i), dExp (cexp i),
        eExp (cexp i)) ∈ Em.pArgs (cexp i))
    (hclE : ∀ i, i < k → cle i ≤ envE (cexp i) n)
    (hmaj : ∀ i, i < k →
      (realizedArrow S aE q2E sE auxW invT robD S₀ i).majorised =
        passValues (rows i))
    (hchk : ∀ i, i < k → ∀ x ∈ rows i,
      RowChecked
        (normalizedL
            (realizedState S aE q2E sE auxW invT robD S₀ i).depth
            (publicBudgetMax (realizedState S aE q2E sE auxW invT robD S₀ i))
            (stateZR (realizedState S aE q2E sE auxW invT robD S₀ i))
            (cle i) + 2) x) :
    (∀ i, i ≤ k →
        (realizedState S aE q2E sE auxW invT robD S₀ i).UnderEnvelope
          (cexp i) n) ∧
      ∀ i, i ≤ k →
        (realizedState S aE q2E sE auxW invT robD S₀ i).UnderEnvelope
          (cexp k) n :=
  iteratedStateMajorant_of_rows Em n k rows rows3
    (fun i => (realizedState S aE q2E sE auxW invT robD S₀ i).depth)
    (fun i => publicBudgetMax (realizedState S aE q2E sE auxW invT robD S₀ i))
    (fun i => stateZR (realizedState S aE q2E sE auxW invT robD S₀ i))
    cle
    (realizedState S aE q2E sE auxW invT robD S₀)
    (realizedArrow S aE q2E sE auxW invT robD S₀) hn hseed hnval
    (fun _ _ => rfl) habs
    (fun _ _ => by simp [LevelState.quantities])
    (fun _ _ => publicBudgetMax_mem _) (fun _ _ => stateZR_mem _) hclE hmaj hchk

/-- **The same induction at the paper's own base state.**

`13-iteration-assembly.tex:317--319`, "The base is literal: `n_val(0) = 1`, the
seed depth is `B(n) = E_2(n)`, and the seed size and budget are below
`E_3(n) = E_{c_0}(n)`", through the banked
`SuccessorMajorant.seedState_underEnvelope`, so the base envelope row is derived
and not assumed.

This is the first statement in the development in which **both** ends of every
arrow are the paper's own data: the incoming state at level zero is `seedState`,
every later incoming state is the previous arrow's realized outgoing tuple, and
every outgoing tuple is `realizedArrow`.

**Consistency disclosure.**  `realizedChain_bundle_consistent` inhabits this
theorem's bundle at the audit base rather than at `seedState`, for the frozen
reason recorded in GAP-EXPOSED 3; the base envelope row here is a banked theorem,
so the residual risk that this specialization is vacuous is confined to the three
`PARAM-001` slots `habs`, `hmaj`, `hchk`.

Reader counterpart: **none claimed** (see `realizedChain_underEnvelope`).
General in every argument. -/
theorem realizedChain_underEnvelope_at_seed (Em : CutoffEmission)
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (rows : ℕ → List CoeffRow)
    (rows3 : ℕ → List ℕ) (cle : ℕ → ℕ) (n k : ℕ) (scales : List ℕ) (hn : 1 ≤ n)
    (hscales : ∀ x ∈ scales, x ≤ envE (cexp 0) n)
    (hnval : nval Em.nStep k ≤ n)
    (habs : ∀ i, i < k →
      (absorbedCoeff (passCsize (rows i) (rows3 i)) (cexp i), dExp (cexp i),
        eExp (cexp i)) ∈ Em.pArgs (cexp i))
    (hclE : ∀ i, i < k → cle i ≤ envE (cexp i) n)
    (hmaj : ∀ i, i < k →
      (realizedArrow S aE q2E sE auxW invT robD (seedState n scales)
        i).majorised = passValues (rows i))
    (hchk : ∀ i, i < k → ∀ x ∈ rows i,
      RowChecked
        (normalizedL
            (realizedState S aE q2E sE auxW invT robD (seedState n scales)
              i).depth
            (publicBudgetMax
              (realizedState S aE q2E sE auxW invT robD (seedState n scales) i))
            (stateZR
              (realizedState S aE q2E sE auxW invT robD (seedState n scales) i))
            (cle i) + 2) x) :
    (∀ i, i ≤ k →
        (realizedState S aE q2E sE auxW invT robD (seedState n scales)
          i).UnderEnvelope (cexp i) n) ∧
      ∀ i, i ≤ k →
        (realizedState S aE q2E sE auxW invT robD (seedState n scales)
          i).UnderEnvelope (cexp k) n :=
  realizedChain_underEnvelope Em S aE q2E sE auxW invT robD rows rows3 cle n k
    (seedState n scales) hn (seedState_underEnvelope n hn scales hscales) hnval
    habs hclE hmaj hchk

/-- **The base arrow with the outgoing tuple realized.**

`SuccessorComposition.successorMajorant_at_seed` was general in the output record
`O`; here `O` is the realized tuple of arrow zero, so both sides of the arrow are
the paper's own data.  All four frozen conclusions survive unchanged -- the
eligibility of `13:297--298`, the exponent identity of line 308, the majorant of
lines 303--307 and the source-width logarithmic row of lines 311--313.

`hq2` is `06:2054--2057`'s own sentence about `AuxOut`, which is why the
source-width membership is discharged internally rather than assumed.

Reader counterpart: **none claimed** (see `realizedChain_underEnvelope`).
General in every argument. -/
theorem realizedOutputs_successorMajorant_at_seed (Em : CutoffEmission)
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (rows : List CoeffRow) (rows3 : List ℕ)
    (clE n : ℕ) (scales : List ℕ) (hn : 1 ≤ n)
    (hscales : ∀ x ∈ scales, x ≤ envE (cexp 0) n)
    (hnval : nval Em.nStep 1 ≤ n)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp 0), dExp (cexp 0),
      eExp (cexp 0)) ∈ Em.pArgs (cexp 0))
    (hclE : clE ≤ envE (cexp 0) n)
    (hq2 : q2E 0 ∈ auxW 0)
    (hmaj :
      (realizedArrow S aE q2E sE auxW invT robD (seedState n scales)
        0).majorised = passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked
      (normalizedL (depthB n) (publicBudgetMax (seedState n scales))
        (seedZR n) clE + 2) x) :
    Em.nStep (cexp 0) ≤ n ∧
      envE (16 * (cexp 0 + 1)) n = envE (cexp 1) n ∧
      (realizedArrow S aE q2E sE auxW invT robD (seedState n scales)
        0).UnderEnvelope (cexp 1) n ∧
      Nat.clog 2
          (realizedArrow S aE q2E sE auxW invT robD (seedState n scales)
            0).srcWidth ≤ envE (cexp 1) n := by
  have hmem :
      Nat.clog 2
          (realizedArrow S aE q2E sE auxW invT robD (seedState n scales)
            0).srcWidth ∈ passValues rows := by
    rw [← hmaj]
    exact realizedOutputs_srcLog_mem S aE q2E sE auxW invT robD _ 0 hq2
  exact successorMajorant_at_seed Em rows rows3 clE n scales
    (realizedArrow S aE q2E sE auxW invT robD (seedState n scales) 0) hn hscales
    hnval habs hclE hmaj hmem hchk

/-! ## Part 6: canonical inhabitation

The registered deferral of `SuccessorMajorant`'s `SuccessorOutputs` row, read at
the paper's own realization record. -/

/-- **The realized chain is the level data of the realization record.**

`14-final-consequence.tex:1617--1652`, clauses (a) and (c), at a specification
whose base carriers are the paper's own full-cube seed (the banked
`FixedLevelCarriers.SeedAnchored`).  Four readings at once:

* the base's two logarithmic side lengths are `clog_2` of the seed's carriers --
  clause (a)'s `R_0 = Can(F_{B(n)})` -- so the base and every successor use the
  **same** readout convention and the chain is anchored, not merely started;
* every later state's two side lengths are `clog_2` of the exact carrier
  recurrence at that level -- clause (c)'s `R_{i+1} = Can(T_i.Rnext)`;
* the two budgets at every level are the banked ladder of clause (c)'s literal
  updates, at the frozen base `D_0 = Y_0 = a_seed(n) + 1` of `13:786--790`;
* the depth is `B(n)` at every level -- clause (c)'s `b_i = b_{i+1} = B(n)`.

This is the canonical-inhabitation statement for `SuccessorOutputs`, in the only
form the paper supports: the four principal roots of `06:2049--2051` and the
source width are the paper's own construction, so the tuple the chain uses is the
paper's tuple, and the state map `nextState` reads nothing else.  The three
`AuxOut` list slots are **not** claimed (GAP-EXPOSED 1, 2).

Reader counterpart: `C-effectivity-details.tex:134--138`, "`A_realize` writes a
finite descriptor containing the full-cube seed, the `L(n)` successful one-level
traces, their exact budget updates and carrier maps, and the final padding maps"
-- the seed, the budget updates and the carrier maps; the padding maps are
deliberately not claimed.

General in the specification, the exponent families, the `AuxOut` families, the
public scales, the source size `n >= 1` and the level. -/
theorem realizedChain_is_the_realization_record
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (n : ℕ) (hn : 1 ≤ n) (scales : List ℕ)
    (hanch : FixedLevelCarriers.SeedAnchored S n) (i : ℕ) :
    (realizedState S aE q2E sE auxW invT robD (seedState n scales) 0).logRow =
        Nat.clog 2 (S.rowCarrier 0) ∧
      (realizedState S aE q2E sE auxW invT robD (seedState n scales) 0).logCol =
        Nat.clog 2 (S.colCarrier 0) ∧
      (realizedState S aE q2E sE auxW invT robD (seedState n scales)
          (i + 1)).logRow = Nat.clog 2 (S.rowCarrier (i + 1)) ∧
      (realizedState S aE q2E sE auxW invT robD (seedState n scales)
          (i + 1)).logCol = Nat.clog 2 (S.colCarrier (i + 1)) ∧
      (realizedState S aE q2E sE auxW invT robD (seedState n scales)
          i).budgetY = budgetY (aSeed n + 1) (realizedOverhead S aE q2E sE) i ∧
      (realizedState S aE q2E sE auxW invT robD (seedState n scales)
          i).budgetD = budgetD (aSeed n + 1) (realizedOverhead S aE q2E sE) i ∧
      (realizedState S aE q2E sE auxW invT robD (seedState n scales) i).depth =
        depthB n := by
  obtain ⟨-, hmb, hnb⟩ := hanch
  obtain ⟨-, hrow, hcol⟩ := seedRowSide_is_the_paper_carrier n hn
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · change qSeed n = Nat.clog 2 S.mBase
    rw [hmb, hrow]
  · change aSeed n = Nat.clog 2 S.nBase
    rw [hnb, hcol]
  · exact (realizedState_budgets S aE q2E sE auxW invT robD
      (seedState n scales) i).1
  · exact (realizedState_budgets S aE q2E sE auxW invT robD
      (seedState n scales) i).2
  · exact realizedState_depth S aE q2E sE auxW invT robD (seedState n scales) i

/-- **The record theorem's specification hypothesis is discharged at the paper's
own carrier specification.**

Canonical inhabitation is not left as a hypothesis:
`CoefficientTraversal.paperCarrierSpec` is the banked specification in which
every schedule field is the paper's own evaluated value and the two Stage-4
counts `m_{N,i}, n_{N,i}` are the carriers of the paper's own protected
duplicate: the frozen `N = A^T` of `08:147`, over the protected duplicate whose
label `eq:protected-labelled-carriers` stands at `08:94`.  It
satisfies `FixedLevelCarriers.SeedAnchored` by `rfl` -- its base carriers *are*
`eq:full-cube-seed`'s -- so `realizedChain_is_the_realization_record` applies to
it, and the realized chain there is the paper's chain rather than an arbitrary
one meeting a hypothesis.

The two blow-up rows are carried alongside because they are what make the
firing content rather than a renaming: the banked
`CoefficientTraversal.paperCarrierSpec_counts_are_not_the_stand_in` bounds the
two counts below by the frozen `184`- and `2^{22}`-fold protection factors, so
the specification cannot be the collapsed stand-in that a degenerate inhabitant
would supply, and the discharge is content rather than a renaming.

**Still disclosed (GAP-EXPOSED 4).**  The Section-8 reservoir data
`(F, q, V, X, L_2, Y)` is held level-uniformly by that banked specification;
producing level `i`'s data from level `i`'s incoming matrix is `STAGE1-001 ..
WRAP-001`.  So the firing is at one legal choice of that data, which is exactly
the scope the banked instance already carries.

Reader counterpart: **none claimed**; the reader item of this part is claimed by
`realizedChain_is_the_realization_record`.  General in the Section-8 data, the
schedule inputs and the level. -/
theorem realizedChain_record_fires_at_paperCarrierSpec
    (F : FiniteSlots.Stage1SlotBinding) {q : ℕ} {V X L₂ Y : Type*} [Fintype V]
    [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y)
    (v₀ : V) (x₀ : X) (l₀ : L₂) (n C0 B0 Ccert sPar lq2 clU0 zR : ℕ)
    (dv zeta : ℝ) (i : ℕ) :
    FixedLevelCarriers.SeedAnchored
        (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR dv
          zeta) n ∧
      184 ≤ (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0 zR
        dv zeta).mN i ∧
      2 ^ 22 ≤ (paperCarrierSpec F hq hs y₀ v₀ x₀ l₀ n C0 B0 Ccert sPar lq2 clU0
        zR dv zeta).nN i :=
  ⟨⟨rfl, rfl, rfl⟩,
    paperCarrierSpec_counts_are_not_the_stand_in F hq hs y₀ v₀ x₀ l₀ n C0 B0
      Ccert sPar lq2 clU0 zR dv zeta i⟩

/-! ## Part 7: joint satisfiability of the live bundle (BEYOND-PAPER rows) -/

/-- **A probe coefficient row (BEYOND-PAPER).**

Value `v` at coefficient `v` and degree zero, so the checked derivation reads
`v <= 2^v` and holds at **every** driver, with no clock hypothesis and hence no
circularity between the probe rows and the clock they are checked at.
`06:1628--1631` forbids a formalizer to supply the registry's `(C_u, d_u)`, so
this pair is **our** value and claims no legality (GAP-EXPOSED 3).  General in
the value. -/
def chainRow (v : ℕ) : CoeffRow := ⟨v, v, 0, by norm_num⟩

/-- **Aux 15 (a probe row is checked at every driver).**  `v <= 2^{v P^0} = 2^v`
by `Nat.lt_two_pow_self`, so the check is independent of the clock.  General in
the driver and the value. -/
theorem chainRow_checked (P v : ℕ) : RowChecked P (chainRow v) := by
  simp only [RowChecked, chainRow, pow_zero, mul_one]
  exact Nat.le_of_lt Nat.lt_two_pow_self

/-- **The probe row list of an output tuple (BEYOND-PAPER).**  One row per
majorised root, in the frozen printed order of `13:303--307`. -/
def chainRows (O : SuccessorOutputs) : List CoeffRow := O.majorised.map chainRow

/-- **Aux 16 (the probe pass's value list is the tuple's majorised list).**
`13:303--307` read off both records, so the identification the traversal needs is
satisfied by construction rather than by choosing the tuple to fit the table.
General in the tuple. -/
theorem chainRows_values (O : SuccessorOutputs) :
    passValues (chainRows O) = O.majorised := by
  have h : (CoeffRow.value ∘ chainRow) = id := funext fun _ => rfl
  simp only [passValues, chainRows, List.map_map, h, List.map_id]

/-- **The probe emission (BEYOND-PAPER).**

Not `Cert_c`: the fixed rational cutoffs, the `ECut` list and the `DCut` list are
empty, and the `PCut` list records exactly the absorbed successor tuples of the
first `k` arrows' probe tables.  It exists only to inhabit the emitted-tuple
slot, and by the banked `R_mono` adjoining further rows only raises the cutoff,
hence only strengthens the eligibility hypothesis.  General in the table family
and the arrow count. -/
def chainEmission (rows : ℕ → List CoeffRow) (k : ℕ) : CutoffEmission where
  fixedRational := fun _ => []
  eArgs := fun _ => []
  pArgs := fun c =>
    (List.range k).map fun i =>
      (absorbedCoeff (passCsize (rows i) []) c, dExp c, eExp c)
  dArgs := fun _ => []

/-- **Aux 17 (the probe emission records every arrow's absorbed tuple).**
The emitted-tuple slot of the live induction, inhabited at every arrow below the
count.  General in the table family, the count, the arrow and the exponent. -/
theorem chainEmission_mem (rows : ℕ → List CoeffRow) (k i : ℕ) (hi : i < k)
    (c : ℕ) :
    (absorbedCoeff (passCsize (rows i) []) c, dExp c, eExp c) ∈
      (chainEmission rows k).pArgs c :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- **The audit base state (BEYOND-PAPER).**

The banked `EnvelopeRealization.twoSidedBound_bundle_consistent` already reads
the clock at the all-zero incoming state; this is the same audit point, lifted to
a whole level state.  It is **not** the paper's base: `13:317--319` fixes that,
and `SuccessorComposition.seedApreInputs_nondegenerate` separates the two by
`B(n) >= 512`, `D_0 = Y_0 >= 5` and `z_R >= 9`.  It exists only to break the
circularity a realized-value probe would otherwise have -- the realized tuples
depend on the base state, the emission on those tuples, and the eligible source
size on the emission -- so that a base fixed in advance makes the whole chain of
choices well founded. -/
def auditBase : LevelState where
  logRow := 0
  logCol := 0
  budgetD := 0
  budgetY := 0
  depth := 0
  scales := []

/-- **Aux 18 (the audit base is under every envelope).**  All six slots are zero
and the scale list is empty, so the base envelope row of `13:295--296` holds at
every exponent and every source size.  General in the exponent and the source
size. -/
theorem auditBase_underEnvelope (c n : ℕ) : auditBase.UnderEnvelope c n := by
  refine (levelState_underEnvelope_iff auditBase c n).2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [auditBase]

/-- **Aux 19 (a sparsity input lands inside every level envelope once the source
size clears its own double exponential).**

The one arithmetic fact that lets the consistency probe below keep `cle`
**general** instead of instantiating it at a value no source graph realizes.
`06-parameter-schedule.tex:114` makes `cle = clog_2(|E| + 2)` the fifth branch of
`eq:s-choice`'s `A_pre`, a quantity of the encoded source graph with no a-priori
bound; it is **not** a slot of the incoming state, so the envelope row it needs
is not the state row of `13:292--296` but the sparsity clause of
`06:1851--1853`, "the upper bound [follows] from the incoming `E_c(n)` bounds and
sparsity of the source graph", which is what the banked
`EnvelopeRealization.lSandwich_upper` consumes as `hclE`.
The banked `EnvelopeRealization.ellN_ge_of_cutoff` turns the frozen cutoff shape
`2^{2^{R+2}}` of `eq:nstep` (`06`, label line 1956, display line 1955) into
`l(n) >= R + 3`, and
`E_c(n) = 2^{l(n)^c}` dominates `l(n)` because every scheduled exponent satisfies
`c_i >= 3` (banked `IterationAssembly.cexp_ge_three_and_lt`).

Reader counterpart: **none claimed**; `05-iteration.tex:201--204` is already
assigned to `EnvelopeRealization.CutoffEmission.nStep`.  General in the bound,
the source size and the level. -/
theorem le_envE_of_cutoff {M n : ℕ} (hn : 1 ≤ n) (h : 2 ^ 2 ^ (M + 2) ≤ n)
    (i : ℕ) : M ≤ envE (cexp i) n := by
  have hell : M + 3 ≤ ellN n := ellN_ge_of_cutoff hn h
  have hc : cexp i ≠ 0 := by
    have h3 := (cexp_ge_three_and_lt i).1
    omega
  have hpow : ellN n ≤ ellN n ^ cexp i := Nat.le_self_pow hc _
  have hlt : ellN n ^ cexp i < 2 ^ ellN n ^ cexp i := Nat.lt_two_pow_self
  change M ≤ 2 ^ ellN n ^ cexp i
  omega

/-- **The live bundle is jointly satisfiable, together with its conclusion.**

The hypothesis-consistency rule demands that a headline theorem's full bundle be
checked for joint satisfiability, so that a green build is not
green-because-vacuous.  Here the bundle of `realizedChain_underEnvelope` is
exhibited satisfied at an **arbitrary legal** carrier specification, arbitrary
level exponents, arbitrary `AuxOut` families **and an arbitrary sparsity input
`cle`**, together with the induction's own conclusion, so no `False` derives from
combining the eligibility, the base envelope, the emitted absorbed tuples, the
sparsity envelope row, the identification of the realized majorised lists with
the traversal tables, and the checked rows at the frozen clocks
`L_i = clog_2(A_pre)`.

**`cle` is a binder here, and that is the point.**  It is the fifth branch of
`eq:s-choice`'s `A_pre`, `clog_2(|E| + 2)` (`06-parameter-schedule.tex:114`),
which the paper **defines** out of the encoded source graph; `|E| + 2 >= 2`
forces `clog_2(|E| + 2) >= 1`, so `0` is unattainable and instantiating the probe
there would exhibit an input no legal instance realizes.  So `cle` stays general
in both the hypothesis and the conclusion, its envelope row
`cle_i <= E_{c_i}(n)` -- the sparsity clause of `06:1851--1853`, not a slot of
the state row of `13:292--296` -- is one of the exhibited components rather than
something dodged, and the exhibited source size is pushed past it by
`le_envE_of_cutoff` above.

Non-degeneracy: the exhibited source size dominates the emission's own threshold,
so the eligibility row is reachable rather than assumed; the chain's complexity
budget **strictly** increases at every arrow, so the family the induction runs
over is not constant; and the exhibited row lists are the realized tuples' own
majorised lists, so the empty pass -- which
`SuccessorComposition.majorised_never_matches_the_empty_pass` refutes -- is not
what satisfies the identification.

**Three honest labels, and no fourth.**  The coefficient rows are
**BEYOND-PAPER** (GAP-EXPOSED 3); the base state is the **NON-FIDELITY**
`auditBase`; and the second-pass table exhibited for `rows3` is the empty list,
an **audit witness** for a `PARAM-001` datum.  `rows3` is quantified
existentially here, exactly like the emission `Em` and the first-pass tables
`rows`, so what is exhibited is the bundle **as stated** and not a `rows3 = []`
specialization of it -- but the witness is ours, and is disclosed as such.
Everything else is the paper's own: the outgoing tuples, the budget ladder, the
carrier readouts, the level-independent depth, the three `A_pre` state inputs and
the sparsity input.  This probe therefore stands in for nothing, and it is
**not** what discharges the canonical-inhabitation row -- that is
`realizedChain_is_the_realization_record`, which is stated at the paper's own
seed-anchored base.

General in the specification, the exponent families, the `AuxOut` families, the
sparsity input and the arrow count. -/
theorem realizedChain_bundle_consistent
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (cle : ℕ → ℕ) (k : ℕ) :
    ∃ (Em : CutoffEmission) (rows : ℕ → List CoeffRow) (rows3 : ℕ → List ℕ)
      (n : ℕ),
      1 ≤ n ∧ nval Em.nStep k ≤ n ∧
        (∀ i, i < k →
          (absorbedCoeff (passCsize (rows i) (rows3 i)) (cexp i), dExp (cexp i),
            eExp (cexp i)) ∈ Em.pArgs (cexp i)) ∧
        (∀ i, i < k → cle i ≤ envE (cexp i) n) ∧
        (∀ i, i < k →
          (realizedArrow S aE q2E sE auxW invT robD auditBase i).majorised =
            passValues (rows i)) ∧
        (∀ i, i < k → ∀ x ∈ rows i, RowChecked
          (normalizedL
              (realizedState S aE q2E sE auxW invT robD auditBase i).depth
              (publicBudgetMax
                (realizedState S aE q2E sE auxW invT robD auditBase i))
              (stateZR (realizedState S aE q2E sE auxW invT robD auditBase i))
              (cle i) + 2) x) ∧
        (∀ i, i < k →
          (realizedState S aE q2E sE auxW invT robD auditBase i).budgetD <
            (realizedState S aE q2E sE auxW invT robD auditBase
              (i + 1)).budgetD) ∧
        (∀ i, i ≤ k →
          (realizedState S aE q2E sE auxW invT robD auditBase i).UnderEnvelope
            (cexp i) n) := by
  refine ⟨chainEmission
      (fun i => chainRows (realizedArrow S aE q2E sE auxW invT robD auditBase i))
      k,
    (fun i => chainRows (realizedArrow S aE q2E sE auxW invT robD auditBase i)),
    (fun _ => []),
    max
      (nval (chainEmission
        (fun i =>
          chainRows (realizedArrow S aE q2E sE auxW invT robD auditBase i))
        k).nStep k)
      (2 ^ 2 ^ (literalMax ((List.range k).map cle) + 2)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (one_le_nval _ _) (le_max_left _ _)
  · exact le_max_left _ _
  · exact fun i hi => chainEmission_mem _ k i hi (cexp i)
  · exact fun i hi =>
      le_trans
        (le_literalMax (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
        (le_envE_of_cutoff (le_trans (one_le_nval _ _) (le_max_left _ _))
          (le_max_right _ _) i)
  · exact fun _ _ => (chainRows_values _).symm
  · intro i _ x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact chainRow_checked _ v
  · exact fun i _ => (realizedState_budgets_strictly_increase S aE q2E sE auxW
      invT robD auditBase i).1
  · exact (realizedChain_underEnvelope
      (chainEmission
        (fun i =>
          chainRows (realizedArrow S aE q2E sE auxW invT robD auditBase i)) k)
      S aE q2E sE auxW invT robD
      (fun i => chainRows (realizedArrow S aE q2E sE auxW invT robD auditBase i))
      (fun _ => []) cle
      (max
        (nval (chainEmission
          (fun i =>
            chainRows (realizedArrow S aE q2E sE auxW invT robD auditBase i))
          k).nStep k)
        (2 ^ 2 ^ (literalMax ((List.range k).map cle) + 2)))
      k auditBase (le_trans (one_le_nval _ _) (le_max_left _ _))
      (auditBase_underEnvelope _ _) (le_max_left _ _)
      (fun i hi => chainEmission_mem _ k i hi (cexp i))
      (fun i hi =>
        le_trans
          (le_literalMax (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
          (le_envE_of_cutoff (le_trans (one_le_nval _ _) (le_max_left _ _))
            (le_max_right _ _) i))
      (fun _ _ => (chainRows_values _).symm)
      (fun _ _ x hx => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
        exact chainRow_checked _ v)).1

end EthInapproximability.ParameterizedNP.EffectiveMaterialization
