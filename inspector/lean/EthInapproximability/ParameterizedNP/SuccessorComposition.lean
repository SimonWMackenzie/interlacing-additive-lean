import EthInapproximability.ParameterizedNP.CoefficientTraversal

/-!
# Parameterized NP route: the successor composition at a realized level

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`PARAM-001`** (the schedule-compiler thread), and
narrowing one registered deferral of `SuccessorMajorant`'s canonical-inhabitation
row.

`CoefficientTraversal.lean` (tranche 64) turned `EnvelopeRealization`'s
structural-majorant hypothesis into a theorem and banked **four**
hypothesis-bearing deliverables:

```text
traversalRealization_of_rows      srcWidthLogRealization_of_rows
htraversal_of_state_of_rows       hsrclog_of_state_of_rows
```

but it stopped at the two antecedent *slots*: nothing there composed them into
`SuccessorMajorant.successorMajorant`, and nothing exhibited the composition at
an incoming state the paper itself constructs.  This module does exactly that,
and nothing beyond it.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The frozen chain this module traces

Opened first-hand this tranche, `13-iteration-assembly.tex:291--321`, the
reading warning "Use of the schedule compiler":

```
For the induction underlying (thm:effective-parameter-schedule), the state
before one-based arrow r+1 consists of the current two logarithmic side-length
bounds, the public budgets D_r, Y_r, the common depth B(n), and the public
scales carried from the source instance.  Suppose that every one of these
quantities is at most E_{c_r}(n) and that n >= n_val(r+1).  Equation
(expi:E-02-nval) supplies n >= n_step(c_r), so Step I-01 verifies every finite
numerical gate emitted for exponent c_r, including the incoming-depth request,
and the static package supplies each covered analytic consequence.  The
second-pass traversal then bounds every newly constructed auxiliary width other
than the numerical source width, both new logarithmic side lengths, the inverse
tolerances and robustness depths, and the updated public budgets by
     E_{16(c_r+1)}(n) = E_{c_{r+1}}(n).
Only the numerical value of q_{2,r+1} is treated separately, through
q_{2,r+1} < 24 s_{r+1} |E(G)|; its logarithm remains in the displayed majorant.
...
The base is literal: n_val(0) = 1, the seed depth is B(n) = E_2(n), and the seed
size and budget are below E_3(n) = E_{c_0}(n) by the arithmetic in Step I-10
below.
```

The three supporting displays are opened at their own anchors, never recalled:

1. `06-parameter-schedule.tex:47--55`, the two public scales this module reifies:
   `B_pub = max{D, Y}` and
   `z_R = max{ceil(log_2 |Rows(R)|), ceil(log_2 |Cols(R)|)}`.  These are the
   third and fourth branches of `eq:s-choice`'s `A_pre`
   (`06:111--115`, whose printed branch order on `06:113--114` is
   `16, b_out, B_pub, z_R, clog_2(|E|+2)`), i.e. exactly the arguments the banked
   `EnvelopeRealization.normalizedL` takes.
2. `13-iteration-assembly.tex:417--419`, the first branch's own value:
   "`b_0 = beta_{i-1} = B(n)`, `b_out = beta_i = B(n)`", the depth the schedule
   makes level-independent at `13:410--412`.
3. `12-iteration-specification.tex:23--30` (`eq:full-cube-seed`) with
   `13:733--737` and `13:786--790`: the seed matrix, its exponent search, and
   the frozen base budgets `D_0 = Y_0 = a_seed + 1`.  These enter only through
   the banked `SuccessorMajorant.seedState` and
   `.seedRowSide_is_the_paper_carrier`, consumed by pin.

## What lands

* `majorantPair_of_rows`, `majorantPair_at_scheduled_exponent` -- the display's
  **two** conclusion rows of `13:303--313` delivered together from checked rows
  at a free clock satisfying the frozen sandwich, through the banked
  `traversalRealization_of_rows` and `srcWidthLogRealization_of_rows`.  The
  second reads them at the scheduled exponent, so the reading warning's own
  identity `E_{16(c_r+1)}(n) = E_{c_{r+1}}(n)` is taken once, through the banked
  `SuccessorMajorant.underEnvelope_of_traversal_bound`.
* `successorMajorant_of_rows`, `successorMajorant_chains_of_rows`,
  `sourceWidthSeparate_of_rows`, `iteratedStateMajorant_of_rows` -- the four
  banked `SuccessorMajorant` deliverables that carry a `PARAM-001` slot, each
  with **both** (respectively, the one) antecedent slot filled by
  `htraversal_of_state_of_rows` / `hsrclog_of_state_of_rows`.  No consumer
  supplies a structural-majorant hypothesis by hand, and no clock is assumed:
  `L` is the banked `EnvelopeRealization.normalizedL` at the frozen `A_pre`
  inputs and its `L >= 1` side condition is derived inside the banked lemmas.
* `publicBudgetMax`, `seedZR` -- the two `A_pre` public scales of `06:49--55`,
  reified as `def`s at their own display and **evaluated** through the paper's
  own seed carriers, never assigned.
* `successorMajorant_at_seed`, `successorMajorant_chains_at_seed` -- the
  composition at the **incoming state the paper itself constructs**: the base of
  `13:317--319`, i.e. the banked `SuccessorMajorant.seedState`, whose envelope
  hypothesis is **derived** from the banked `seedState_underEnvelope` rather than
  assumed, and whose three `A_pre` state inputs are the seed's own evaluated
  slots.  This is the first point in the development where the majorant
  machinery is read at an incoming state that is not a binder.
* `successorMajorant_at_seed_bundle_consistent` -- the joint satisfiability of
  that composed bundle **together with its conclusions**, at the seed state.
  Labelled BEYOND-PAPER in its coefficient rows and NON-FIDELITY in its output
  tuple; see GAP-EXPOSED 1 and 2.

## DEFINED-vs-FREE

* **DEFINED, reified and evaluated, never assigned a numeral:** `B_pub`
  (`06:49`, reified here as `publicBudgetMax` and evaluated at the seed to
  `a_seed(n) + 1` through the banked `SuccessorMajorant.seedState`); `z_R`
  (`06:51--55`, reified here as `seedZR` over the paper's own seed matrix and
  evaluated to `q_seed(n)` through the banked
  `seedRowSide_is_the_paper_carrier`); `b_out = B(n)` (`13:419`, the banked
  `IterationAssembly.depthB`); `A_pre` and the clock `L = clog_2(A_pre)` (banked
  `ParameterSchedule.Apre`, `EnvelopeRealization.normalizedL`); `c_0 = 3` and
  `c_1 = 16(c_0+1) = 64` (banked `IterationAssembly.cexp`, evaluated in
  `successorExponent_at_seed`, never written as a numeral in a statement);
  `n_val`, `n_step`, `E_c`, `W(L)`, `C_size`, `d_c`, `e_c`, the absorbed
  coefficient and the seed's `a_seed`, `q_seed`, `B(n)` (all banked, consumed by
  pin).
* **FREE in the paper itself, therefore binders:** the emission `Cert_c`
  (`thm:eff-ledger`, unbuilt -- `PARAM-001`); the registry's per-root
  coefficient table, which `06:1628--1631` forbids a formalizer to supply; the
  sparsity input `clog_2(|E|+2)`, which is source-graph data no Lean module
  produces and which therefore travels with its own frozen bound
  `<= E_{c_r}(n)`; the successor output tuple `O`, which `13:313--315` calls a
  **candidate** tuple (`MATERIALIZE-001`); the public scales carried from the
  source instance, which the frozen base sentence does not supply
  (`SuccessorMajorant`'s own GAP-EXPOSED 4, inherited unchanged).

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate read in place.

**One reader item is claimed, by one declaration, not previously assigned.**

* `05-iteration.tex:212--215` -- "Suppose `n >= n_step(c)`.  Suppose also that
  the incoming seed is supplied with ordered row and column carriers of size at
  least two, a correct entry evaluator, and logarithmic side lengths and budgets
  at most `E_c(n)`." -- the reader's statement of the two frozen antecedents the
  composition consumes (numerical eligibility, and the incoming logarithmic side
  lengths and budgets under the envelope), claimed by
  `successorMajorant_of_rows`.  It is `thm:paper-effective-level` **statement**
  text, inside `\begin{theorem}` (`05:198`, `\label{thm:paper-effective-level}`
  on `:199`) and closing at `\end{theorem}` (`:236`), well before
  `\begin{proof}` (`:238`) -- so it is statement text, not proof prose.
  A sweep of every module under `src/EthInapproximability/ParameterizedNP/` for
  `05-iteration.tex` citations returns `:212--215` from this module **only**, and
  no other claimed row meets the interval `205--220` at all: the nearest
  neighbours are `:201--204` below and `:221--226` above.  Neither overlaps
  `212--215`.

**No reader item is claimed by any other declaration here, and the reason is
recorded.**  The reader prints no reading warning at all: a search of all nine
reader files for `B_{\mathrm{pub}}`, `z_R`, `A_{\mathrm{pre}}`, `n_{\rm val}`
and `majorant` returns no occurrence of `B_pub`, of `z_R`, of `A_pre`, or of the
successor-majorant display, so `publicBudgetMax`, `seedZR` and the four
`*_at_seed` declarations claim nothing.  The reader's one sentence on the base,
`05-iteration.tex:278--280` ("Moreover `a+1 <= q`.  Hence the initial
logarithmic side length, the two initial budgets, and the common requested depth
are all at most `E_{c_0}(n)`"), is **already assigned** to the banked
`SuccessorMajorant.seedState_underEnvelope`, and re-citing it would be the
double assignment the rule forbids; `05-iteration.tex:272` ("Use the common
requested depth `b_i = B(n)` at the seed and at every level"), which is `b_out`'s
own reader locus, is **already assigned** to `IterationAssembly.depthB`; and
`eq:paper-fixed-level-growth` (label line 289), the reader's induction display,
is **already assigned** to `SizePropagation`.  The reader's remaining sentences
touching the induction, `:283--285`, are inseparable from that assigned display.

Crosswalk: no new row; the assignment and the compiler's remaining Lean-pending
status stay in the existing row **6, "Simultaneous parameters and size"**, of
`READER_CROSSWALK.md`, which is `PARAM-001`'s row.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is a
  transcription of a frozen display, a general property of that transcription,
  or a composition of banked results.  No communication-complexity lemma is
  introduced, adapted or re-proved, and no banked module is edited.
* Consumed by pin, never restated: `IterationAssembly.cexp`, `.cexp_zero`,
  `.cexp_succ`, `.cexp_ge_three_and_lt`, `.nval`, `.envE`, `.depthB`,
  `.depthB_ge`, `.ellN`;
  `PaddingAndClock.aSeed`, `.qSeed`, `.aSeed_bounds`, `.qSeed_sandwich`;
  `ParameterSchedule.Apre`;
  `SuccessorMajorant.LevelState`, `.SuccessorOutputs`, `.successorMajorant`,
  `.successorMajorant_chains`, `.sourceWidthSeparate`, `.iteratedStateMajorant`,
  `.underEnvelope_of_traversal_bound`, `.envE_display_exponents`, `.seedState`,
  `.seedState_underEnvelope`, `.seedRowSide_is_the_paper_carrier`;
  `EnvelopeRealization.CutoffEmission`, `.absorbedCoeff`, `.dExp`, `.eExp`,
  `.normalizedL`, `.absorbedEmission`, `.absorbedEmission_mem`, `.one_le_nval`;
  `CoefficientTraversal.CoeffRow`, `.RowChecked`, `.passCsize`, `.passValues`,
  `.traversalRealization_of_rows`, `.srcWidthLogRealization_of_rows`,
  `.htraversal_of_state_of_rows`, `.hsrclog_of_state_of_rows`;
  `FixedLevelCarriers.seedMatrix`; `BridgeOutputEquality.rowsCard`, `.colsCard`.
* Imports: `CoefficientTraversal`, hence transitively `EnvelopeRealization`,
  `DenseStageFourOpening`, `SuccessorMajorant`, `PilotPCut`,
  `DominantWidthBound`, `PaddingAndClock`, `FixedLevelCarriers`,
  `SizePropagation`, `IterationAssembly`, `ParameterSchedule`, `EntryGates`,
  `RawStageFour` and `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  **`LegacyNPCC.Stage12` is not
  imported**, so no declaration reaches the cited AGHP balanced-family axiom and
  no opt-in ledger note is owed; `EXPANDER-001` has no contact with this module.
* External adapters: none.  No new `axiom`, no opaque certificate.
* Axiom surface (Appendix D, and `#print axioms`): at most `propext`,
  `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **No new structure.**  This module introduces no record at all: the two new
  `def`s are the frozen public scales of `06:49--55`, both `ℕ`-valued
  expressions over already-banked data, and every hypothesis is an explicit
  binder rather than a premise bundle.  Nothing here restates a derived
  telescope: `publicBudgetMax` is the printed maximum and its seed value is a
  theorem, not a definition.
* **The desired conclusions stay out of the data.**  `probeOutputs` is a
  `SuccessorOutputs` value, which by the banked record's design carries no
  envelope, complexity, robustness or promise field; the bounds it satisfies are
  theorems about it.
* **Both interlace widths stay distinct.**  `q_i` and `Q_i` do not occur in this
  module at all; nothing here merges them or reads one for the other.
* **Every comparison is transcribed as printed.**  The eligibility rows
  `n >= n_val(r+1)`, `n >= n_step(c_r)` and the majorant rows `<= E_{c_{r+1}}(n)`
  are non-strict exactly as at `13:296--297` and `13:303--308`; the one strict
  comparison of the passage, `q_{2,r+1} < 24 s_{r+1} |E(G)|` of `13:312`, stays
  strict in `sourceWidthSeparate_of_rows`.
* **Statement poles.**  `majorised_never_matches_the_empty_pass` shows the
  trivial witness `rows = []` fails `hmaj` for **every** output record;
  `seedApreInputs_nondegenerate` separates the seed's three `A_pre` inputs from
  the all-zero probe values of the banked
  `EnvelopeRealization.twoSidedBound_bundle_consistent`; and
  `successorExponent_at_seed` evaluates the arrow's own successor exponent, so
  the composed conclusion is visibly at a different exponent from its hypothesis.

## GAP-EXPOSED

1. **The compiler is still not built, and the emission stays a binder.**
   `thm:eff-ledger`'s existential -- `K_*`, `c |-> Cert_c`, the byte machine
   `A_cert`, `SchemaChecked`, `NumChecked`, the expression graph and the two
   producers' recorded tables -- has no Lean declaration and none is given.
   Every theorem below quantifies over the emission `Em` and takes the emitted
   absorbed tuple as a hypothesis.  Nothing below asserts that a concrete
   compiler emits it, and nothing below is an axiom.  `PARAM-001` stays open.
2. **The outgoing tuple is a candidate, not a realized one, so the composed
   inhabitation is one-sided.**  `13:313--315` -- "This is a successor statement
   for a candidate tuple inside the exact balanced-family envelope.  The
   realization theorem supplies the actual tuple and trace on the same index."
   What this module makes canonical is the **incoming** side: the state at the
   arrow out of the seed is the paper's own base state of `13:317--319`, derived
   and not assumed.  The **outgoing** side is untouched: `O` is a binder in every
   theorem, and the one exhibited `probeOutputs` is explicitly **NON-FIDELITY**.
   `SuccessorMajorant`'s canonical-inhabitation row for `SuccessorOutputs` stays
   **registered as deferred** against `MATERIALIZE-001`, discharged when
   `thm:effective-materialization` lands, and is **not** satisfied by the probe.
3. **The probe's coefficient rows are BEYOND-PAPER.**  `06:1628--1631` states
   that no formalizer supplies a registry coefficient, so `probeRow`'s pair
   `(C_u, d_u) = (1, 8)` is our value and claims no legality; it audits our
   encoding at a tightness point the paper never prints.  It is strictly weaker
   evidence than the paper's application point and stands in for nothing.  The
   one thing the probe does establish is what the hypothesis-consistency rule
   demands: the composed bundle at the seed is jointly satisfiable together with
   its conclusions, so no `False` derives from it.
4. **Only the first arrow is realized.**  `successorMajorant_at_seed` is the
   arrow `r = 0` out of the base state.  Arrows `r >= 1` need the previous
   arrow's realized output as the incoming state, which is GAP-EXPOSED 2's
   deferral; `iteratedStateMajorant_of_rows` therefore keeps the whole state
   family `St` as a binder, exactly as the banked
   `SuccessorMajorant.iteratedStateMajorant` does, and no chain of realized
   arrows is claimed.
5. **The other rows of the reading warning are not claimed.**  The static
   package's "each covered analytic consequence" (`13:301--302`), the
   incoming-depth request (`13:301`), and the realization sentence
   (`13:314--315`) have no declaration here.
6. **No route completion is claimed.**  Stages 1--4, the materialization, the
   slow clock beyond what is banked, and the ETH consequence are untouched.
-/

namespace EthInapproximability.ParameterizedNP.SuccessorComposition

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.SizePropagation
open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.SuccessorMajorant
open EthInapproximability.ParameterizedNP.EnvelopeRealization
open EthInapproximability.ParameterizedNP.CoefficientTraversal

/-! ## Part 1: the display's two rows, from checked rows at a free clock

`13-iteration-assembly.tex:300--313` through the banked
`CoefficientTraversal.traversalRealization_of_rows` and
`.srcWidthLogRealization_of_rows`. -/

/-- **Both conclusion rows of the reading warning, from checked rows.**

`13-iteration-assembly.tex:303--308` bounds the five majorised families, and
`13:312--313` puts the numerical source width's **logarithm** -- not the width --
under the same displayed majorant.  The two banked deliverables are consumed by
pin at one and the same clock, emission and output record, so the pair really is
one traversal's output and not two independent bounds.

`hmaj` is `13:303--307`'s reading of `majorised` as the traversal's own value
list; `hmem` is `06:1703--1704`'s ("Here `q_2` itself is not called an auxiliary
scale: only `log_2 q_2` appears among the new logarithmic side lengths"), so the
source-width row is a **membership** rather than a second free bound.

General in the emission, both traversal tables, the clock, the exponent, the
source size and the output record. -/
theorem majorantPair_of_rows (Em : CutoffEmission) (rows : List CoeffRow)
    (rows3 : List ℕ) (L c n : ℕ) (O : SuccessorOutputs) (hn : 1 ≤ n)
    (hL1 : 1 ≤ L)
    (habs : (absorbedCoeff (passCsize rows rows3) c, dExp c, eExp c) ∈ Em.pArgs c)
    (hL : L ≤ (ellN n + 2) ^ (c + 1))
    (hmaj : O.majorised = passValues rows)
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked (L + 2) x)
    (hcut : Em.nStep c ≤ n) :
    (∀ x ∈ O.majorised, x ≤ envE (eExp c) n) ∧
      Nat.clog 2 O.srcWidth ≤ envE (eExp c) n :=
  ⟨traversalRealization_of_rows Em rows rows3 L c n O hn hL1 habs hL hmaj hchk hcut,
    srcWidthLogRealization_of_rows Em rows rows3 L c n O hn hL1 habs hL hmem hchk hcut⟩

/-- **The same pair, read at the scheduled exponent.**

`13-iteration-assembly.tex:307--309` is the display
`E_{16(c_r+1)}(n) = E_{c_{r+1}}(n)`: the traversal bounds by the *unevaluated*
exponent and the reading warning concludes at the *evaluated* one.  The single
bridge is the banked `SuccessorMajorant.underEnvelope_of_traversal_bound` and its
`envE_display_exponents`, taken once here and never re-derived.

Note that `eExp (cexp r)` and `16(c_r+1)` are the same term by the banked
`EnvelopeRealization.eExp`'s own definition, so no exponent is silently changed.

General in every argument. -/
theorem majorantPair_at_scheduled_exponent (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (L n r : ℕ) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hL1 : 1 ≤ L)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp r), dExp (cexp r),
      eExp (cexp r)) ∈ Em.pArgs (cexp r))
    (hL : L ≤ (ellN n + 2) ^ (cexp r + 1))
    (hmaj : O.majorised = passValues rows)
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked (L + 2) x)
    (hcut : Em.nStep (cexp r) ≤ n) :
    O.UnderEnvelope (cexp (r + 1)) n ∧
      Nat.clog 2 O.srcWidth ≤ envE (cexp (r + 1)) n := by
  obtain ⟨hmajor, hsrc⟩ :=
    majorantPair_of_rows Em rows rows3 L (cexp r) n O hn hL1 habs hL hmaj hmem
      hchk hcut
  refine ⟨underEnvelope_of_traversal_bound hmajor, ?_⟩
  rw [← envE_display_exponents n r]
  exact hsrc

/-! ## Part 2: the four `SuccessorMajorant` deliverables, both slots filled -/

/-- **`eq:iteration-successor-majorant`, with both antecedent slots filled from
checked rows.**

`13-iteration-assembly.tex`, label line 310, reading warning lines 291--315.
The banked `SuccessorMajorant.successorMajorant` is consumed by pin in its exact
binder shape; its two `PARAM-001` hypotheses `htraversal` and `hsrclog`
(`SuccessorMajorant.lean:659--662`) are supplied by the banked
`CoefficientTraversal.htraversal_of_state_of_rows` and `.hsrclog_of_state_of_rows`.

So **no structural-majorant hypothesis is supplied by hand at this consumer**,
and no clock is assumed: `L` is the banked `EnvelopeRealization.normalizedL`
at the frozen `A_pre` inputs of `eq:s-choice`, and its `L >= 1` side condition is
derived inside the banked lemmas from `four_le_normalizedL`.

All four frozen conclusions survive: the eligibility of `13:297--298`, the
exponent identity of line 308, the majorant of lines 303--307, and the
source-width logarithmic row of line 313.

`hboutS`, `hBpubS`, `hzRS` say that the three public inputs of `eq:s-choice` are
quantities of the incoming state; `hclE` is the sparsity input
`clog_2(|E|+2)`, which is not a state slot and carries its own frozen bound.

General in the emission, both traversal tables, the four `A_pre` inputs, the
source size, the arrow, the state and the output record.

Reader counterpart: `05-iteration.tex:212--215`, "Suppose `n >= n_step(c)`.
Suppose also that the incoming seed is supplied with ordered row and column
carriers of size at least two, a correct entry evaluator, and logarithmic side
lengths and budgets at most `E_c(n)`." -/
theorem successorMajorant_of_rows (Em : CutoffEmission) (rows : List CoeffRow)
    (rows3 : List ℕ) (bout Bpub zR clE n r : ℕ) (S : LevelState)
    (O : SuccessorOutputs) (hn : 1 ≤ n) (hstate : S.UnderEnvelope (cexp r) n)
    (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp r), dExp (cexp r),
      eExp (cexp r)) ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hmaj : O.majorised = passValues rows)
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked (normalizedL bout Bpub zR clE + 2) x) :
    Em.nStep (cexp r) ≤ n ∧
      envE (16 * (cexp r + 1)) n = envE (cexp (r + 1)) n ∧
      O.UnderEnvelope (cexp (r + 1)) n ∧
      Nat.clog 2 O.srcWidth ≤ envE (cexp (r + 1)) n :=
  successorMajorant Em.nStep n r S O hstate hnval
    (htraversal_of_state_of_rows Em rows rows3 bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hmaj hchk)
    (hsrclog_of_state_of_rows Em rows rows3 bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hmem hchk)

/-- **The successor state re-enters the envelope, from checked rows.**

The banked `SuccessorMajorant.successorMajorant_chains` with its one
`PARAM-001` hypothesis filled.  `hsrclog` is deliberately absent there --
`LevelState` has no source-width slot, so the display's fourth clause plays no
part in the state induction -- and stays absent here; requiring it would be an
over-strong hypothesis.

General in every argument. -/
theorem successorMajorant_chains_of_rows (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (bout Bpub zR clE n r : ℕ)
    (S : LevelState) (O : SuccessorOutputs) (hn : 1 ≤ n)
    (hstate : S.UnderEnvelope (cexp r) n)
    (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp r), dExp (cexp r),
      eExp (cexp r)) ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hmaj : O.majorised = passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked (normalizedL bout Bpub zR clE + 2) x) :
    (O.nextState S).UnderEnvelope (cexp (r + 1)) n :=
  successorMajorant_chains Em.nStep n r S O hstate hnval
    (htraversal_of_state_of_rows Em rows rows3 bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hmaj hchk)

/-- **The separate numerical source width, from checked rows.**

The banked `SuccessorMajorant.sourceWidthSeparate` with both `PARAM-001`
hypotheses filled.  All four frozen conclusions survive, including the **strict**
graph row `q_{2,r+1} < 24 s_{r+1} |E(G)|` of `13:312`, which stays an explicit
hypothesis because line 311 leaves the numerical width to the source graph.

General in every argument. -/
theorem sourceWidthSeparate_of_rows (Em : CutoffEmission) (rows : List CoeffRow)
    (rows3 : List ℕ) (bout Bpub zR clE n r : ℕ) (S : LevelState)
    (O : SuccessorOutputs) (s edges : ℕ) (hn : 1 ≤ n)
    (hgraph : O.srcWidth < 24 * s * edges)
    (hstate : S.UnderEnvelope (cexp r) n)
    (hnval : nval Em.nStep (r + 1) ≤ n)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp r), dExp (cexp r),
      eExp (cexp r)) ∈ Em.pArgs (cexp r))
    (hboutS : bout ∈ S.quantities) (hBpubS : Bpub ∈ S.quantities)
    (hzRS : zR ∈ S.quantities) (hclE : clE ≤ envE (cexp r) n)
    (hmaj : O.majorised = passValues rows)
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked (normalizedL bout Bpub zR clE + 2) x) :
    O.UnderEnvelope (cexp (r + 1)) n ∧
      O.srcWidth < 24 * s * edges ∧
      Nat.clog 2 O.srcWidth ≤ envE (cexp (r + 1)) n ∧
      O.srcWidth ≤ 2 ^ envE (cexp (r + 1)) n :=
  sourceWidthSeparate Em.nStep n r S O s edges hgraph hstate hnval
    (htraversal_of_state_of_rows Em rows rows3 bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hmaj hchk)
    (hsrclog_of_state_of_rows Em rows rows3 bout Bpub zR clE (cexp r) n S O hn
      (cexp_ge_three_and_lt r).1 habs hboutS hBpubS hzRS hclE hmem hchk)

/-- **The state induction of the reading warning, from checked rows at every
arrow.**

The banked `SuccessorMajorant.iteratedStateMajorant` with its per-arrow
`PARAM-001` hypothesis filled at every arrow.  The traversal's two tables, the
three `A_pre` state inputs and the sparsity input are per-arrow functions,
because `eq:s-choice` is evaluated at each level's own public data
(`13:399--402`); the emission is a single object, because `thm:eff-ledger`(b)
fixes `Cert` before the recursion.

The whole state family `St` stays a binder: realizing arrow `i+1`'s incoming
state from arrow `i`'s output is `MATERIALIZE-001` (GAP-EXPOSED 2, 4).

General in every argument. -/
theorem iteratedStateMajorant_of_rows (Em : CutoffEmission) (n k : ℕ)
    (rows : ℕ → List CoeffRow) (rows3 : ℕ → List ℕ) (bo Bp zr cle : ℕ → ℕ)
    (St : ℕ → LevelState) (Out : ℕ → SuccessorOutputs) (hn : 1 ≤ n)
    (hseed : (St 0).UnderEnvelope (cexp 0) n) (hnval : nval Em.nStep k ≤ n)
    (hchain : ∀ i, i < k → St (i + 1) = (Out i).nextState (St i))
    (habs : ∀ i, i < k →
      (absorbedCoeff (passCsize (rows i) (rows3 i)) (cexp i), dExp (cexp i),
        eExp (cexp i)) ∈ Em.pArgs (cexp i))
    (hboutS : ∀ i, i < k → bo i ∈ (St i).quantities)
    (hBpubS : ∀ i, i < k → Bp i ∈ (St i).quantities)
    (hzRS : ∀ i, i < k → zr i ∈ (St i).quantities)
    (hclE : ∀ i, i < k → cle i ≤ envE (cexp i) n)
    (hmaj : ∀ i, i < k → (Out i).majorised = passValues (rows i))
    (hchk : ∀ i, i < k → ∀ x ∈ rows i,
      RowChecked (normalizedL (bo i) (Bp i) (zr i) (cle i) + 2) x) :
    (∀ i, i ≤ k → (St i).UnderEnvelope (cexp i) n) ∧
      ∀ i, i ≤ k → (St i).UnderEnvelope (cexp k) n :=
  iteratedStateMajorant Em.nStep n k St Out hseed hnval hchain
    (fun i hi => htraversal_of_state_of_rows Em (rows i) (rows3 i) (bo i) (Bp i)
      (zr i) (cle i) (cexp i) n (St i) (Out i) hn (cexp_ge_three_and_lt i).1
      (habs i hi) (hboutS i hi) (hBpubS i hi) (hzRS i hi) (hclE i hi)
      (hmaj i hi) (hchk i hi))

/-! ## Part 3: the two `A_pre` public scales, reified and evaluated

`06-parameter-schedule.tex:47--55`. -/

/-- **`B_pub = max{D, Y}`** -- `06-parameter-schedule.tex:48--50`, the third
branch of `eq:s-choice`'s `A_pre` (`06:113`), and `normalizedL`'s second
argument.  (`06:113` prints `16, b_out, B_pub, z_R,` and `06:114` the fifth
branch `clog_2(|E|+2)`; `16` is not a `normalizedL` argument, which is why the
branch ordinal and the argument position differ by one.)

Read off a level state's two public budget slots, which `13:292--294` names as
"the public budgets `D_r, Y_r`".  A `def` over the banked record, never a stored
field: putting it in `LevelState` would restate a derived telescope. -/
def publicBudgetMax (S : LevelState) : ℕ := max S.budgetD S.budgetY

/-- **`z_R = max{ceil(log_2 |Rows(R)|), ceil(log_2 |Cols(R)|)}` at the seed** --
`06-parameter-schedule.tex:51--55`, the fourth branch of `eq:s-choice`'s `A_pre`
(`06:113`), and `normalizedL`'s third argument, evaluated at the paper's own base
matrix.

`R` at the base is the full-cube seed `eq:full-cube-seed`
(`12-iteration-specification.tex`, label line 29, display lines 23--30) at the
frozen requested depth `B(n)` -- the banked `FixedLevelCarriers.seedMatrix
(depthB n)` -- and the two cardinalities are read through the banked
`BridgeOutputEquality.rowsCard` / `.colsCard`.

This is a DEFINED quantity and is therefore **evaluated through the definitional
chain**, never assigned: `seedZR_eq` computes it to `q_seed(n)` using the banked
`SuccessorMajorant.seedRowSide_is_the_paper_carrier`, which is itself the frozen
exact sandwich `2^{a-1} < q_seed < 2^a` of `13:768--772`. -/
noncomputable def seedZR (n : ℕ) : ℕ :=
  max (Nat.clog 2 (BridgeOutputEquality.rowsCard
      (FixedLevelCarriers.seedMatrix (depthB n))))
    (Nat.clog 2 (BridgeOutputEquality.colsCard
      (FixedLevelCarriers.seedMatrix (depthB n))))

/-- **Aux 1 (`05-iteration.tex`'s "Moreover `a+1 <= q`", in the strict form the
seed search gives).**

`a_seed(n) < q_seed(n)` at every `n >= 1`, from the banked
`PaddingAndClock.qSeed_sandwich`'s lower half `2^{a-1} < q_seed` together with
`a - 1 < 2^{a-1}`.  This is the one arithmetic fact `seedZR_eq` needs, and it is
recorded separately because it is a property of the frozen seed search rather
than of this module's definition.  General in `n >= 1`. -/
theorem aSeed_lt_qSeed (n : ℕ) (hn : 1 ≤ n) : aSeed n < qSeed n := by
  have h4 := (aSeed_bounds n hn).1
  have hsw := (qSeed_sandwich n hn).1
  have hlt : aSeed n - 1 < 2 ^ (aSeed n - 1) := Nat.lt_two_pow_self
  omega

/-- **Aux 2 (`z_R` at the seed, evaluated).**

`seedZR n = q_seed(n)`: the frozen display of `06:51--55` computed through the
paper's own seed carriers.  No numeral is assigned and no binder is left --
this is the definitional chain of `eq:full-cube-seed` run in dependency order,
through the banked `seedRowSide_is_the_paper_carrier` and `Aux 1`.  General in
`n >= 1`. -/
theorem seedZR_eq (n : ℕ) (hn : 1 ≤ n) : seedZR n = qSeed n := by
  obtain ⟨-, hrow, hcol⟩ := seedRowSide_is_the_paper_carrier n hn
  simp only [seedZR, hrow, hcol]
  exact max_eq_left (Nat.le_of_lt (aSeed_lt_qSeed n hn))

/-- **Aux 3 (`B_pub` at the seed, evaluated).**

`B_pub = max{D_0, Y_0} = a_seed(n) + 1`, from the frozen base budgets
`D_0 = Y_0 = a_seed + 1` of `13-iteration-assembly.tex:786--790` as carried by
the banked `SuccessorMajorant.seedState`.  Independent of the public scale list,
which is what makes it a property of the budgets alone.  General in `n` and the
scales. -/
theorem publicBudgetMax_seedState (n : ℕ) (scales : List ℕ) :
    publicBudgetMax (seedState n scales) = aSeed n + 1 := by
  simp [publicBudgetMax, seedState]

/-- **Aux 4 (`B_pub` inherits the incoming envelope).**

If every quantity of a level state is at most `E_c(n)` -- `13:295--296` -- then
so is the reified `B_pub`, since both budget slots are quantities.  A general
property of the reification, recorded so that no later proof reopens
`quantities`.  General in the state, the exponent and the source size. -/
theorem publicBudgetMax_le_of_underEnvelope {S : LevelState} {c n : ℕ}
    (h : S.UnderEnvelope c n) : publicBudgetMax S ≤ envE c n := by
  obtain ⟨-, -, hD, hY, -, -⟩ := (levelState_underEnvelope_iff S c n).1 h
  exact max_le hD hY

/-- **Aux 5 (the clock is monotone in the sparsity input).**

`L = clog_2(A_pre)` and `A_pre` is a maximum containing `clog_2(|E|+2)`
(`eq:s-choice`, `06:111--115`), so a larger sparsity input can only raise the
clock.  With the banked `CoefficientTraversal.rowChecked_mono_driver` this says
that rows checked at a smaller graph's clock stay checked at a larger one's,
which is the direction the composition needs when the source graph is enlarged.
General in the three state inputs and both sparsity values. -/
theorem normalizedL_mono_clE (bout Bpub zR : ℕ) {clE clE' : ℕ} (h : clE ≤ clE') :
    normalizedL bout Bpub zR clE ≤ normalizedL bout Bpub zR clE' := by
  refine Nat.clog_mono_right _ ?_
  simp only [ParameterSchedule.Apre]
  exact max_le_max_left _ h

/-- **Aux 6 (the three `A_pre` state inputs are quantities of the seed state).**

`eq:s-choice`'s three state-borne branches, at the base of `13:317--319`:

* `b_out = B(n)` (`13:419`) is the seed state's depth slot;
* `B_pub = max{D_0, Y_0} = a_seed(n) + 1` (`06:49`, `13:788--790`) is its budget
  slot;
* `z_R = q_seed(n)` (`06:51--55`, evaluated by `Aux 2`) is its row side-length
  slot.

This is exactly what `htraversal_of_state_of_rows` asks of the incoming state,
so the composition below needs no membership hypothesis at all.  General in
`n >= 1` and the scales. -/
theorem seedApreInputs_mem (n : ℕ) (hn : 1 ≤ n) (scales : List ℕ) :
    depthB n ∈ (seedState n scales).quantities ∧
      publicBudgetMax (seedState n scales) ∈ (seedState n scales).quantities ∧
      seedZR n ∈ (seedState n scales).quantities := by
  refine ⟨?_, ?_, ?_⟩
  · simp [seedState, LevelState.quantities]
  · rw [publicBudgetMax_seedState]
    simp [seedState, LevelState.quantities]
  · rw [seedZR_eq n hn]
    simp [seedState, LevelState.quantities]

/-! ## Part 4: the composition at the realized level -/

/-- **The successor majorant at the base state the paper constructs.**

`13-iteration-assembly.tex:317--319`: "The base is literal: `n_val(0) = 1`, the
seed depth is `B(n) = E_2(n)`, and the seed size and budget are below
`E_3(n) = E_{c_0}(n)` by the arithmetic in Step I-10 below."

This is `successorMajorant_of_rows` read at `r = 0` with the incoming state
**instantiated** rather than quantified: `S` is the banked
`SuccessorMajorant.seedState`, whose six slots are all evaluated through banked
accessors, and the envelope hypothesis `hstate` is **derived** from the banked
`seedState_underEnvelope` instead of assumed.  The three `A_pre` state inputs are
the seed's own slots, supplied by `Aux 6`, so the only remaining `A_pre` input is
the sparsity `clog_2(|E|+2)`, which is source-graph data and keeps its own frozen
bound.

This is the first application of the majorant machinery at an incoming state the
paper itself constructs.  What stays a candidate is the **outgoing** side: `O` is
a binder, exactly as `13:313--315` requires (GAP-EXPOSED 2).

General in the emission, both traversal tables, the sparsity input, the source
size, the public scales and the output record. -/
theorem successorMajorant_at_seed (Em : CutoffEmission) (rows : List CoeffRow)
    (rows3 : List ℕ) (clE n : ℕ) (scales : List ℕ) (O : SuccessorOutputs)
    (hn : 1 ≤ n) (hscales : ∀ x ∈ scales, x ≤ envE (cexp 0) n)
    (hnval : nval Em.nStep 1 ≤ n)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp 0), dExp (cexp 0),
      eExp (cexp 0)) ∈ Em.pArgs (cexp 0))
    (hclE : clE ≤ envE (cexp 0) n)
    (hmaj : O.majorised = passValues rows)
    (hmem : Nat.clog 2 O.srcWidth ∈ passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked
      (normalizedL (depthB n) (publicBudgetMax (seedState n scales))
        (seedZR n) clE + 2) x) :
    Em.nStep (cexp 0) ≤ n ∧
      envE (16 * (cexp 0 + 1)) n = envE (cexp 1) n ∧
      O.UnderEnvelope (cexp 1) n ∧
      Nat.clog 2 O.srcWidth ≤ envE (cexp 1) n := by
  obtain ⟨hb, hB, hz⟩ := seedApreInputs_mem n hn scales
  exact successorMajorant_of_rows Em rows rows3 (depthB n)
    (publicBudgetMax (seedState n scales)) (seedZR n) clE n 0
    (seedState n scales) O hn (seedState_underEnvelope n hn scales hscales)
    hnval habs hb hB hz hclE hmaj hmem hchk

/-- **The successor state after the base arrow, at the realized level.**

`successorMajorant_chains_of_rows` at the same instantiated incoming state.  The
conclusion is the state the induction of `13:292` carries into arrow two: the
seed's depth and public scales unchanged (`13:398--400`), the four traversal
slots replaced, all under `E_{c_1}(n)`.

`hsrclog` is absent for the same frozen reason as in the banked lemma:
`LevelState` has no source-width slot.

General in every argument. -/
theorem successorMajorant_chains_at_seed (Em : CutoffEmission)
    (rows : List CoeffRow) (rows3 : List ℕ) (clE n : ℕ) (scales : List ℕ)
    (O : SuccessorOutputs) (hn : 1 ≤ n)
    (hscales : ∀ x ∈ scales, x ≤ envE (cexp 0) n)
    (hnval : nval Em.nStep 1 ≤ n)
    (habs : (absorbedCoeff (passCsize rows rows3) (cexp 0), dExp (cexp 0),
      eExp (cexp 0)) ∈ Em.pArgs (cexp 0))
    (hclE : clE ≤ envE (cexp 0) n)
    (hmaj : O.majorised = passValues rows)
    (hchk : ∀ x ∈ rows, RowChecked
      (normalizedL (depthB n) (publicBudgetMax (seedState n scales))
        (seedZR n) clE + 2) x) :
    (O.nextState (seedState n scales)).UnderEnvelope (cexp 1) n := by
  obtain ⟨hb, hB, hz⟩ := seedApreInputs_mem n hn scales
  exact successorMajorant_chains_of_rows Em rows rows3 (depthB n)
    (publicBudgetMax (seedState n scales)) (seedZR n) clE n 0
    (seedState n scales) O hn (seedState_underEnvelope n hn scales hscales)
    hnval habs hb hB hz hclE hmaj hchk

/-! ## Part 5: joint satisfiability of the composed bundle (BEYOND-PAPER) -/

/-- **A probe coefficient row (BEYOND-PAPER).**

Value `2^{(L+2)^8}` at coefficient one and degree eight, so the checked
derivation `RowChecked (L+2)` holds by `le_refl` and no slack hides an
inconsistency.  `06:1628--1631` forbids a formalizer to supply the registry's
`(C_u, d_u)`, so this pair is **our** value and claims no legality; it audits our
encoding at a tightness point the paper never prints (GAP-EXPOSED 3). -/
def probeRow (L : ℕ) : CoeffRow := ⟨2 ^ (L + 2) ^ 8, 1, 8, le_refl 8⟩

/-- **Seven copies of the probe row (BEYOND-PAPER).**

Seven, because `SuccessorOutputs.majorised` of `13:303--307` has four printed
scalar slots and three list slots, and the probe keeps every list slot
non-empty. -/
def probeRows (L : ℕ) : List CoeffRow :=
  [probeRow L, probeRow L, probeRow L, probeRow L, probeRow L, probeRow L,
    probeRow L]

/-- **A probe output tuple (NON-FIDELITY).**

`13:313--315` calls the successor tuple a **candidate**; the realized tuple is
`MATERIALIZE-001` and is not in Lean.  This record therefore stands in for
nothing: it exists only to show that `hmaj` and `hmem` are jointly satisfiable.
Its `srcWidth` is `2^v` and not `v`, which is `06:1703--1704` realized -- the
source width's *logarithm*, not the width, is one of the traversal's requested
roots.  The canonical-inhabitation obligation for `SuccessorOutputs` stays
registered against `MATERIALIZE-001` and is **not** discharged here. -/
def probeOutputs (L : ℕ) : SuccessorOutputs where
  auxWidths := [(probeRow L).value]
  logRow := (probeRow L).value
  logCol := (probeRow L).value
  invTolerances := [(probeRow L).value]
  robustDepths := [(probeRow L).value]
  budgetD := (probeRow L).value
  budgetY := (probeRow L).value
  srcWidth := 2 ^ (probeRow L).value

/-- **The probe emission (BEYOND-PAPER).**

The successor-row half of `eq:successor-pcut-normal-form` at the constant
coefficient the probe rows produce, through the banked
`EnvelopeRealization.absorbedEmission`.  It is **not** `Cert_c`: the fixed
rational cutoffs, the `ECut` list and the `DCut` list are empty, and by the
banked `R_mono` adjoining them only raises the cutoff, hence only strengthens
the eligibility hypothesis. -/
noncomputable def probeEmission : CutoffEmission := absorbedEmission (fun _ => 6561)

/-- **Aux 7 (the probe's recorded `C_size` does not move with the clock).**

`passCsize (probeRows L) [] = 6561 = 3^8`: the banked producer
`eq:Csize-literal-producer` reads only the pairs `(C_u, d_u)`, which are
`(1, 8)` at every clock, so the emission below can be fixed **before** the source
size and the clock are chosen.  That is what keeps the consistency probe free of
circularity.  General in the clock. -/
theorem probeRows_csize (L : ℕ) : passCsize (probeRows L) [] = 6561 := by
  simp [passCsize, probeRows, probeRow, passRows12, csizeLiteral, maxFrom]

/-- **Aux 8 (every probe row is checked at its own driver).**  By `le_refl`, so
the derivation is an equality and no slack is available.  General in the
clock. -/
theorem probeRows_checked (L : ℕ) : ∀ x ∈ probeRows L, RowChecked (L + 2) x := by
  intro x hx
  simp only [probeRows, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h <;>
    (subst h; simp [RowChecked, probeRow])

/-- **Aux 9 (the probe tuple's majorised list is the probe pass's value list).**
`13:303--307` read off both records.  General in the clock. -/
theorem probeOutputs_majorised (L : ℕ) :
    (probeOutputs L).majorised = passValues (probeRows L) := by
  simp [probeOutputs, SuccessorOutputs.majorised, passValues, probeRows]

/-- **Aux 10 (the probe tuple's source-width logarithm is a requested root).**

`Nat.clog 2 (2^v) = v` and `v` is exactly what `passValues (probeRows L)`
contains.  This is `06:1703--1704` -- "only `log_2 q_2` appears among the new
logarithmic side lengths" -- realized, and it is why `hmem` is a membership and
not a second free bound.  General in the clock. -/
theorem probeOutputs_srcLog_mem (L : ℕ) :
    Nat.clog 2 (probeOutputs L).srcWidth ∈ passValues (probeRows L) := by
  have hclog : Nat.clog 2 (2 ^ (probeRow L).value) = (probeRow L).value :=
    Nat.clog_pow 2 _ one_lt_two
  simp only [probeOutputs, hclog]
  simp [passValues, probeRows]

/-- **The probe's own eligibility threshold is reachable.**

`n_val(1) = max{1, n_step(c_0)}` is a concrete natural number, so the source-size
hypothesis of the consistency probe below is not an empty premise: taking `n` to
be that threshold itself satisfies it, and the banked
`EnvelopeRealization.one_le_nval` gives `n >= 1` at the same point. -/
theorem probeEmission_threshold_reachable :
    ∃ n : ℕ, 1 ≤ n ∧ nval probeEmission.nStep 1 ≤ n :=
  ⟨nval probeEmission.nStep 1, one_le_nval _ _, le_refl _⟩

/-- **The composed bundle at the realized level is jointly satisfiable, together
with its conclusions.**

The hypothesis-consistency rule demands that a headline theorem's full bundle be
checked for joint satisfiability, so that a green build is not
green-because-vacuous.  Here the bundle of `successorMajorant_at_seed` is
exhibited satisfied **at the paper's own base state** together with the two
majorant conclusions of the display, so no `False` derives from combining the
eligibility, the incoming envelope, the emitted absorbed tuple, `hmaj`, `hmem`
and `hchk` at the frozen `L = clog_2(A_pre)`.

Non-degeneracy: the exhibited row list has seven entries, the output tuple's
auxiliary-width list is non-empty, the checked derivation is an equality, and the
source width is `2^v` rather than `v` -- so the empty row list, the all-zero
record and the "width equals its own logarithm" shortcut all fail.

**Two honest labels, and no third.**  The coefficient rows are **BEYOND-PAPER**
(GAP-EXPOSED 3): `06:1628--1631` forbids a formalizer to supply the registry's
table, so `(C_u, d_u) = (1, 8)` is our value and claims no legality.  The output
tuple is **NON-FIDELITY** (GAP-EXPOSED 2): `13:313--315` supplies the realized
tuple through `thm:effective-materialization`, which is not in Lean, so
`probeOutputs` stands in for nothing and does **not** discharge the registered
canonical-inhabitation obligation for `SuccessorOutputs`.  What is **not** a
probe value here is the incoming side: the state, its three `A_pre` inputs and
the clock are the paper's own, evaluated.

General in the sparsity input, the source size above the probe's own threshold,
and the public scales. -/
theorem successorMajorant_at_seed_bundle_consistent (clE n : ℕ)
    (scales : List ℕ) (hnval : nval probeEmission.nStep 1 ≤ n)
    (hscales : ∀ x ∈ scales, x ≤ envE (cexp 0) n)
    (hclE : clE ≤ envE (cexp 0) n) :
    ∃ (rows : List CoeffRow) (O : SuccessorOutputs),
      rows.length = 7 ∧ O.auxWidths ≠ [] ∧
        (absorbedCoeff (passCsize rows []) (cexp 0), dExp (cexp 0),
          eExp (cexp 0)) ∈ probeEmission.pArgs (cexp 0) ∧
        O.majorised = passValues rows ∧
        Nat.clog 2 O.srcWidth ∈ passValues rows ∧
        (∀ x ∈ rows, RowChecked
          (normalizedL (depthB n) (publicBudgetMax (seedState n scales))
            (seedZR n) clE + 2) x) ∧
        probeEmission.nStep (cexp 0) ≤ n ∧
        O.UnderEnvelope (cexp 1) n ∧
        Nat.clog 2 O.srcWidth ≤ envE (cexp 1) n := by
  have hn : 1 ≤ n := le_trans (one_le_nval _ _) hnval
  set L : ℕ :=
    normalizedL (depthB n) (publicBudgetMax (seedState n scales)) (seedZR n) clE
      with hL
  have habs : (absorbedCoeff (passCsize (probeRows L) []) (cexp 0),
      dExp (cexp 0), eExp (cexp 0)) ∈ probeEmission.pArgs (cexp 0) := by
    rw [probeRows_csize]
    exact absorbedEmission_mem (fun _ => 6561) (cexp 0)
  obtain ⟨hcut, -, hout, hsrc⟩ :=
    successorMajorant_at_seed probeEmission (probeRows L) [] clE n scales
      (probeOutputs L) hn hscales hnval habs hclE (probeOutputs_majorised L)
      (probeOutputs_srcLog_mem L) (probeRows_checked L)
  exact ⟨probeRows L, probeOutputs L, by simp [probeRows], by simp [probeOutputs],
    habs, probeOutputs_majorised L, probeOutputs_srcLog_mem L,
    probeRows_checked L, hcut, hout, hsrc⟩

/-! ## Part 6: statement poles -/

/-- **Statement pole: the trivial witness fails `hmaj`, for every output record.**

`rows = []` would make every theorem of Parts 2 and 4 vacuous through `hmaj`
alone, since `passValues [] = []`.  It cannot: `SuccessorOutputs.majorised` of
`13:303--307` always contains the two printed logarithmic side lengths, so it is
never the empty list.  Exhibited in the kernel rather than argued in prose, and
general in the record. -/
theorem majorised_never_matches_the_empty_pass (O : SuccessorOutputs) :
    O.majorised ≠ passValues [] := by
  intro h
  have hmem : O.logRow ∈ O.majorised := by
    simp [SuccessorOutputs.majorised]
  rw [h] at hmem
  simp [passValues] at hmem

/-- **Statement pole: the seed's three `A_pre` inputs are not the probe's zeros.**

The banked `EnvelopeRealization.twoSidedBound_bundle_consistent` reads the clock
at the all-zero incoming state, where `A_pre` collapses to its literal floor
`16`.  At the paper's own base state all three state-borne branches of
`eq:s-choice` are bounded **below** by frozen quantities: `B(n) >= 512`
(`13:427--428`), `D_0 = Y_0 = a_seed + 1 >= 5` (`13:788--790` with
`a_seed >= 4`), and `z_R = q_seed > 2^{a_seed-1} >= 8` (`13:768--772`).

So the composition at the seed is genuinely read at a non-degenerate clock and
is not a renaming of the probe point.  General in `n >= 1` and the scales. -/
theorem seedApreInputs_nondegenerate (n : ℕ) (hn : 1 ≤ n) (scales : List ℕ) :
    512 ≤ depthB n ∧ 5 ≤ publicBudgetMax (seedState n scales) ∧
      9 ≤ seedZR n := by
  refine ⟨(depthB_ge n hn).1, ?_, ?_⟩
  · rw [publicBudgetMax_seedState]
    have h4 := (aSeed_bounds n hn).1
    omega
  · rw [seedZR_eq n hn]
    have h4 := (aSeed_bounds n hn).1
    have hsw := (qSeed_sandwich n hn).1
    have h8 : (8 : ℕ) ≤ 2 ^ (aSeed n - 1) := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (aSeed n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **Statement pole: the base arrow's successor exponent is a different
number.**

`13-iteration-assembly.tex:258--263` -- the display `K_rec = 16`, `c_0 = 3`,
`c_{j+1} = 16(c_j+1)`, with the two constants on `13:261--262` specifically --
so the base arrow concludes at `c_1 = 64`, not at `c_0`.  Evaluated through the
banked `IterationAssembly.cexp` -- no numeral is written into any statement above
-- and paired with the display's own identity `E_{16(c_0+1)}(n) = E_{c_1}(n)` of
line 308, so `successorMajorant_at_seed`'s conclusion is visibly at a strictly
larger exponent than its incoming hypothesis and is not a restatement of it.
General in the source size. -/
theorem successorExponent_at_seed (n : ℕ) :
    cexp 0 = 3 ∧ cexp 1 = 64 ∧ cexp 0 < cexp 1 ∧
      envE (16 * (cexp 0 + 1)) n = envE (cexp 1) n := by
  refine ⟨rfl, rfl, by norm_num [cexp], ?_⟩
  exact envE_display_exponents n 0

end EthInapproximability.ParameterizedNP.SuccessorComposition
