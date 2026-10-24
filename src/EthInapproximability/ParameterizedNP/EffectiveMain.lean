import EthInapproximability.ParameterizedNP.LiteralFinalRuntime

/-!
# Parameterized NP route: the effective ETH consequence (`thm:effective-main`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ETH-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), whose Lean
cell already carries tranches `cc-t1w` (`AlphaAllowance.lean`) and
`cc-t1x`/`-r1`/`-r2` (`LiteralFinalRuntime.lean`), and whose GAP-EXPOSED list
names `thm:effective-main` as the row's remaining open Lean content.  This
module lands *that*, in the conditional shape its frozen proof actually has.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchors (proof source).**  All in
  `sections/14-final-consequence.tex` unless stated otherwise.
  * `thm:effective-main` (label line 2576, environment lines 2575--2587):
    "Assume `CitedETH`, and instantiate B1--B6 by
    `thm:canonical-machine-environment`, `thm:encoded-source-package`,
    `thm:eff-ledger`, `thm:effective-materialization`.  Then
    `not PolyApprox_M(alpha)`."  Its proof is frozen lines 2589--2682.
  * `EncodedETH` is fixed at frozen lines 487--499, with its runtime display
    `eq:encoded-ETH-runtime` at lines 493--497; `PolyApprox_M(alpha)` at frozen
    lines 510--523, its accuracy contract at line 518 and its step bound at
    line 521; the declared interpretation at frozen lines 527--535;
    `def:cited-eth` at label line 115.  **All three are carried below as
    opaque `Prop` parameters, never as definitions and never as axioms**
    (GAP-EXPOSED 1--3).
  * `eq:cited-to-encoded-ETH` (label line 1207, display lines 1203--1208,
    inside `thm:encoded-source-package`, label line 1199):
    `CitedETH ==> EncodedETH(M_*, delta_ETH)` for one positive rational
    `delta_ETH`, with the frozen sentence at lines 1209--1210, "This datum is
    chosen before, and is uniform over, every `epsilon` below."  Consumed at
    frozen lines 2590--2593, and carried below as the named binder
    `hCitedToEncoded`.
  * The B1--B6 binder list (frozen lines 2266--2291), with the frozen sentence
    at lines 2290--2291, "Only after B1--B6 are fixed are the functions
    `L, g, e, T_n` instantiated."
  * Frozen line 2633: "For the remaining argument `n >= n_tail`, so
    `L(n) >= 1`."  Frozen lines 2634--2638: "Put `k = L(n)`, `A = alpha(T_n)`,
    and let `z` be the signed-integer parser output of `A_app` for one branch."
  * **The frozen decision display, frozen lines 2646--2651:**
    `YES : z <= Y_k + A`, hence `2z < 2Y_k + k`;
    `NO  : z >= Y_k + k - A`, hence `2z > 2Y_k + k`.
    Its two stated inputs are named at frozen line 2644: "`eq:k-level-gap` and
    `eq:alpha-gap-fit` give" the display.
  * Frozen lines 2652--2658: "Thus comparing the integer `2z` with `2Y_k + k`
    decides whether this branch is satisfiable ... Hence `A_SAT` decides encoded
    ordered 3-SAT on every bitstring."  The first clause is proved below; the
    passage from it to the semantic conclusion is the binder `hSatDecided`.
  * Frozen lines 2662--2674: the tail bound, then "Because
    `2 epsilon_* = delta_ETH/4 <= delta_ETH`, this is at most
    `K_SAT 2^{delta_ETH n}(H+1)^{r_SAT}`."  Carried below as the binder
    `hTailRuntime` (GAP-EXPOSED 4).
  * Frozen lines 2675--2681: "Thus `A_SAT`, together with the literal witnesses
    `K = K_SAT`, `r = r_SAT`, `n_0 = n_tail`, violates
    `EncodedETH(M, delta_ETH)`.  This is the required contradiction."  Carried
    below as the binder `hEncodedViolated` (GAP-EXPOSED 4).
  * `eq:k-level-gap` (`sections/12-iteration-specification.tex`, label line
    305, display lines 301--306): `YES: comp(R_k) <= Y_k`,
    `NO: comp(R_k) = D_k = Y_k + k`.  These are the two frozen promise-case
    hypotheses transcribed below as `hyes`/`hno`, and they are **separate cases
    of one construction**, never conjoined.
  * `eq:alpha-gap-fit` (label line 2320, display lines 2318--2321):
    `2 alpha(T_n) < L(n)` whenever `L(n) >= 1` -- already banked as
    `AlphaAllowance.alphaGapFit`, and the sole source of the strictness that
    makes the frozen comparison decide.
  * `eq:literal-final-cutoff` (label line 2447) fixes `n_L` and `n_tail`;
    both are banked in `LiteralFinalRuntime` and are consumed read-only.
  * `cor:realized-effective-prefix` is used at frozen lines 2640--2643 to
    certify that the records fed to `thm:fixed-level-gap-size` are the ones the
    materializer used, together with "Final padding preserves complexity"
    (frozen line 2643).  Both are upstream of what is landed here; see
    GAP-EXPOSED 5.
  * `conv:finite-slots` (`sections/02-mechanical-contract.tex`) fixes the
    zero-based reading of every finite index set; no finite carrier is
    introduced or re-indexed in this module.

* **Banked endpoints, all grep-verified present in
  `src/EthInapproximability/ParameterizedNP/` before use.**
  *Actually consumed:*
  * from `AlphaAllowance.lean` (tranche `cc-t1w`): **`alphaAllowance`** (the
    frozen `alpha`) and **`alphaGapFit`** (the frozen `eq:alpha-gap-fit`);
  * from `PaddingAndClock.lean` (tranche `cc-t1t-r1`): **`slowIndex`** (the
    frozen `L`), **`tCommon`** (the frozen `T_n`), **`SlowClockGateSet`**
    (explicit binder, never a new bundle), **`witnessClock`**,
    **`witnessClock_gates`** and **`witnessClock_reaches_positive_index`**
    (non-vacuity only);
  * from `LiteralFinalRuntime.lean` (tranches `cc-t1x`/`-r1`/`-r2`), which is
    consumed **read-only at the pinned SHA-256
    `55FD88056BCE0D9E69B407A17A3A4D158A88712984102E5B795B16F148240395`**
    (re-hashed first-hand this tranche): **`TailCutoffSet`**, **`tailCutoff`**,
    **`tailCutoff_guards`**, **`slowIndexCutoff`** and
    **`slowIndexCutoff_spec`**.

  *Verified present but deliberately **not** consumed:*
  `CommonPadding.paddedComplexity` and `frozenPaddedComplexity`, the banked form
  of frozen line 2643, "Final padding preserves complexity"; that sentence is
  what identifies the complexity of the padded branch matrix with `comp(R_k)`,
  so it is what licenses the caller to supply `hyes`/`hno` at the padded value,
  and it is upstream of the arithmetic landed here (GAP-EXPOSED 5).
  `AlphaAllowance.allowance_pointwise_maximal` and `allowance_exactness` (the
  frozen maximality paragraph is `cc-t1w`'s content and plays no part in the
  decision).  `LiteralFinalRuntime.tailAllowanceGapFit`, which states exactly
  the fit the tail needs but is stated at the frozen tail regime only, whereas
  the frozen display of lines 2646--2651 is argued from `eq:alpha-gap-fit`
  itself at the guard `L(n) >= 1` (frozen line 2644 names `eq:alpha-gap-fit`,
  not the tail set); the tail regime is traced separately, in
  `tailIndexHasPositiveClockIndex`, which is frozen line 2633 and nothing more.
  `LiteralFinalRuntime.literalFinalRuntime`, `literalFinalTailBound` and
  `topControllerEnvelope`: the frozen instantiation of `lem:literal-final-runtime`
  at frozen lines 2598--2604 and the frozen rate replacement of lines 2669--2674
  enter here as the single binder `hTailRuntime`, because `epsilon_*`,
  `delta_ETH` and the machine step count are unmodelled (GAP-EXPOSED 4).

* **Imports.**  `EthInapproximability.ParameterizedNP.LiteralFinalRuntime` and,
  through it, `AlphaAllowance`, `TruthTableExponent`, `CommonPadding`,
  `PaddingAndClock`, `SizePropagation`, `IterationAssembly` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom stays outside this
  module's closure and no ledger note for it is needed.  No new import is added.

* **Proof status.**  Every declaration below is **new**.  Nothing is
  inherited, nothing is ported, and nothing is transcribed from
  `C:/lean/npc-cc/EthProof`, which traced the older fixed-width manuscript and
  is not a trace or style source here.

## What this module lands

1. **The frozen approximation contract, split into its two frozen legs**
   (`approxUpper`, `approxLower`) -- the two left-hand columns of the frozen
   display at lines 2646--2651 -- and **the frozen strictness step**
   (`strictFitYes`, `strictFitNo`), the two "hence" columns, each obtained from
   `2A < k` and nothing else.
2. **The frozen decision** (`comparisonDecides`), frozen lines 2652--2654:
   comparing `2z` with `2Y_k + k` decides the branch.
3. **`BranchSeparation`** -- the frozen display itself, at the frozen data
   `k = L(n)`, `A = alpha(T_n)` of line 2637 -- and `branchSeparation_holds`,
   which **proves** it from the banked `alphaGapFit`; plus the frozen tail guard
   (`tailIndexHasPositiveClockIndex`, frozen line 2633) and the decision read on
   the frozen tail (`tailBranchComparisonDecides`).
4. **`effectiveMain`** -- `thm:effective-main` as the closed **conditional**
   statement its frozen proof actually is: from `CitedETH`, the frozen bridge
   `eq:cited-to-encoded-ETH`, the frozen runtime step, the frozen semantic step
   and the frozen violation step, conclude `not PolyApprox`.  The one
   non-arithmetic machine-layer step (`hSatDecided`, frozen lines 2652--2658)
   has the frozen decision as its **antecedent**, supplied by item 3 rather
   than assumed.
5. **Non-vacuity, hypothesis consistency, and statement poles** (Part 5),
   including a full simultaneous discharge of `effectiveMain`'s binder list at
   legal values and one load-bearing pole per frozen binder.

## Reader counterparts

The reader artifact is
`routes/parameterized-np/reader-facing/sections/06-eth.tex`.  **That file was
opened first-hand and every locus named below was read to confirm what it
states.**

**No declaration below claims a reader item, and that is a deliberate,
recorded disposition rather than an omission.**  Three loci were considered and
each is declined for a stated reason:

* `prop:paper-eth-consequence` (label line 388, statement lines 389--392),
  "Assume the Exponential Time Hypothesis.  Then no truth-table
  polynomial-time algorithm approximates deterministic communication
  complexity to additive error `alpha`".  This is a closed proposition about
  machines.  `effectiveMain` is **not** that proposition: it is the frozen
  conditional shape, with `CitedETH`, `EncodedETH`, `PolyApprox`, the semantic
  decision predicate and the runtime-fit predicate all opaque parameters.
  Assigning the reader's closed statement to a schema that does not state it
  would be exactly the mis-assignment the reader-counterpart rule forbids, so
  the item stays unassigned and remains available to whichever later tranche
  lands the machine layer.
* Reader line 401, "Choose `eps = delta_ETH/8`", and reader lines 457--462,
  which run the reader's own exponent comparison `3 eps = 3 delta_ETH/8`
  against `delta_ETH`.  Both sit inside the proof of
  `prop:paper-eth-consequence`, and nothing below models either rate.  This
  ledger row's own precedent (`CLOCK-001`'s treatment of
  `05-iteration.tex:308--310`, `cc-t1x`'s treatment of `06-eth.tex:442--464`)
  is that proof-internal loci are navigation, not statements.
* The `YES`/`NO` display at reader lines 428--434, and reader lines 435--436,
  "Thus comparison with the integer threshold `2Y_k + k` decides whether that
  branch is satisfiable", with reader lines 420--422 fixing `k = L(n)` and
  `A = alpha(T_n)`.  All are proof-internal, and prose is never cited as a
  statement.

**No already-assigned reader line is re-claimed.**  In particular
`eq:paper-alpha` (label line 358) belongs to `cc-t1w`'s `pIndex` and
`alphaAllowance`; `eq:paper-alpha-fits-gap` (label line 370) and reader lines
360--363 were assigned by `cc-t1x` to `AlphaAllowance.alphaGapFit`,
`pIndex_monotone`, `alpha_monotone` and `alpha_unbounded`; and every item
`CLOCK-001` owns in `06-eth.tex` is untouched.  **`eq:paper-g-little-o` (label
line 312) remains unclaimed**, and this tranche does not change that: no
little-`o`, `Filter.Tendsto`, or asymptotic order relation is landed here.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: **this module introduces no structure at all**, so no constructor
  can carry a conclusion.  `BranchSeparation` is a `Prop`-valued abbreviation of
  a frozen display, in the same style as the banked
  `LiteralFinalRuntime.TailCutoffSet`.  Every clause of it is printed in the
  frozen text and **neither restates a derived telescope**: the `NO` row is not
  derivable from the `YES` row, since the frozen `NO` hypothesis is an equality
  at `Y_k + k` and its conclusion is a strict lower bound.  `BranchSeparation`
  is moreover **proved** (`branchSeparation_holds`), so it is not a premise
  bundle at all.  Every other conditional deliverable takes explicit binders:
  the frozen clock gates as the banked `SlowClockGateSet`, the frozen guard
  `1 <= L(n)` as `hn`, the approximation contract as `happ`, and the two
  `eq:k-level-gap` cases as the two separate binders `hyes`/`hno`.
* `M3` (binder order): the frozen text fixes B1--B6 first and only then
  instantiates `L, g, e, T_n` (frozen lines 2290--2291).  `effectiveMain` puts
  the clock data `V`/`hg` first and the opaque `Prop` parameters after; because
  those parameters mention neither `V` nor `alpha`, **no dependency is
  inverted**, and within the `Prop` block the binders follow the frozen proof
  order 2590 -> 2594 -> 2598 -> 2652 -> 2675 exactly.
* `M7` (nonemptiness facts are proved, never posited): the only such fact in
  play is that the frozen `n_L` set is inhabited, proved in the banked
  `LiteralFinalRuntime.positiveIndexTailExists`.  Nothing new is posited.
* `M9`: no ceiling is introduced.  The frozen rounding of the allowance is the
  banked `alphaAllowance`, spelled exactly, and the arithmetic below performs no
  rounding of its own.
* Selector costs, both interlace widths `q` and `Q`, and every finite carrier
  are untouched: the decision runs strictly after the last level and after
  final padding (frozen line 2643), so no interlace, carrier, or slot occurs
  below.
* Zero-based slots (`conv:finite-slots`) are untouched: no finite index type
  occurs in this module.

## GAP-EXPOSED (what this module deliberately does not claim)

1. **The machine layer is not defined, by design, and B1--B6 are not
   instantiated.**  Nothing here defines `mathfrak M`, `time_M`, `Comp_M`, the
   codecs, the parsers, `A_spar`, `A_gap`, `A_realize`, `A_materialize`,
   `A_app`, `A_br`, `A_SAT`, `A_bf`, an M2 certificate, an M5 primitive,
   `delta_ETH`, `epsilon_*`, the S1--S2 package, `thm:eff-ledger`, `A_cert`,
   `A_raw`, or `thm:effective-materialization`.  So `SOURCE-001`, `PARAM-001`
   and `MATERIALIZE-001` are GAP-EXPOSED here in exactly the frozen places where
   `thm:effective-main` cites them.
2. **`CitedETH`, `EncodedETH` and `PolyApprox` are opaque `Prop` parameters.**
   They are never `axiom`s, never `def`s, and carry no field.  The declared
   interpretation of frozen lines 527--535 and 2583--2586 is therefore not
   formalized either.
3. **`effectiveMain` is a conditional schema, not the closed theorem.**  It
   proves that the frozen contradiction closes *given* the frozen machine-layer
   steps, with the decision arithmetic discharged for real.  It does **not**
   prove `thm:main`, and it does not prove `not PolyApprox_{M_*}(alpha)` for the
   frozen canonical environment, because nothing here constructs that
   environment and `PolyApprox` is not tied to the `alpha` built from this `V`.
   **No route completion is claimed.**
4. **The runtime leg and the violation leg are binders, not derivations.**
   Frozen lines 2598--2604 (instantiating `lem:literal-final-runtime`),
   2662--2674 (the tail bound and the rate replacement
   `2 epsilon_* = delta_ETH/4 <= delta_ETH`) and 2675--2681 (assembling the
   literal witnesses `K_SAT`, `r_SAT`, `n_tail`) enter as `hTailRuntime` and
   `hEncodedViolated`, because `epsilon_*`, `delta_ETH`, the exponential
   envelope and the machine step count are unmodelled.  Likewise frozen lines
   2605--2617 and 2655--2658 -- the exhaustive short-input branch, totality, and
   the S1 identification of the branch disjunction with `Sat(Phi)` -- enter
   through `hSatDecided`, whose antecedent is the frozen decision proved here.
5. **`cor:realized-effective-prefix` and "final padding preserves complexity"
   are not formalized here.**  Frozen lines 2640--2643 use them to certify that
   the records fed to `thm:fixed-level-gap-size` are the ones the materializer
   used and that the padded branch matrix has complexity `comp(R_k)`.  Both are
   upstream of the arithmetic landed here and enter as the caller's obligation
   to supply `hyes`/`hno` at the realized, padded records.  The banked
   `CommonPadding.paddedComplexity` is verified present rather than re-derived.
6. **Every limit form stays out.**  No `Filter.Tendsto`, no little-`o`, no real
   exponentiation, and no asymptotic order relation appears anywhere below,
   exactly as in the two banked tranches.
7. **The clock is still a parameter.**  `L` and `T_n` are the banked
   `slowIndex` and `tCommon` of an arbitrary `V`, and the frozen tie of `V_k`
   to the compiler's running time `tau_k` is not modelled (this is
   `PaddingAndClock`'s GAP-EXPOSED 2, inherited unchanged).

## Reading notes

* **N1 (why the estimate is an integer and not a natural number).**  Frozen
  line 2639 calls `z` "the signed-integer parser output of `A_app`", and the
  frozen `PolyApprox` contract at line 516 says the parser "returns an integer
  `z`" with `|z - comp M| <= alpha(...)`.  Nothing in the frozen contract
  forces `z >= 0`: an approximation algorithm is allowed to under-report a
  complexity of `0`.  Typing `z` as a natural number would silently add
  `0 <= z` to the frozen hypothesis -- an over-strong hypothesis that
  typechecks perfectly -- so every estimate below is an `Int`, and
  `signedEstimateIsOutsideTheNaturalSpelling` records the difference in the
  kernel.
* **N2 (why the two `eq:k-level-gap` cases are separate binders).**  Frozen
  display lines 301--306 give `YES: comp(R_k) <= Y_k` and
  `NO: comp(R_k) = Y_k + k` as the two cases of one construction.  They are
  contradictory when `k >= 1`, so conjoining them would make every downstream
  statement vacuous.  Below they are `hyes : sat -> ...` and
  `hno : not sat -> ...`, guarded by the branch's own satisfiability, exactly
  as the frozen display is.  `promiseCasesAreExclusive` records in the kernel
  that conjoining them is inconsistent at the frozen guard.
* **N3 (why the strictness is the whole point).**  The frozen display's two
  conclusions are strict: `2z < 2Y_k + k` and `2z > 2Y_k + k`.  Strictness is
  what makes the single integer comparison decide, and it comes from
  `2 alpha(T_n) < L(n)` and from nothing else.  With the non-strict fit
  `2 alpha(T_n) <= L(n)` the comparison misclassifies a satisfiable branch;
  `strictAllowanceIsNecessary` exhibits that at the smallest legal values.
* **N4 (`Y_k` and `comp` are typed as integers although the paper's values are
  nonnegative).**  A statement quantified over all integers implies the
  nonnegative case, so this is a generalization and never a weakening; it also
  keeps the frozen subtraction `Y_k + k - A` of line 2649 honest rather than
  truncated.  The frozen `k = L(n)` and `A = alpha(T_n)` are natural numbers and
  are cast into `Z` at each use, which is why no truncated `k - A` occurs.
* **N5 (why `hSatDecided` keeps the `BranchSeparation V` antecedent).**
  Weakening a hypothesis strengthens a theorem, so `effectiveMain` is
  inter-derivable with the variant lacking that antecedent, and the antecedent
  is a **faithfulness** choice rather than a source of content: it mirrors the
  frozen proof's dependence of lines 2655--2658 on the display of lines
  2646--2651.  Consequently `effectiveMain` on its own is a propositional
  consequence, and this tranche's proved mathematics is `branchSeparation_holds`
  and `comparisonDecides`.

## Candidate encodings and ranking (NOVEL-concept protocol)

Two encodings of the frozen decision display were written and run against the
same aux-lemma battery before landing.

* **Candidate A (landed).**  The estimate, the budget and the complexity value
  are `Int`; the approximation contract is the frozen two-sided
  `|z - c| <= A`; the two `eq:k-level-gap` cases are separate guarded binders;
  the frozen strictness enters only through `2A < k`.
* **Candidate B (rejected).**  The same display with the estimate, the budget
  and the complexity value typed as `Nat` -- the "complexity is a nonnegative
  quantity, so its estimate is too" spelling -- with truncated subtraction in
  the frozen `Y_k + k - A`.

Ranking.  Battery (the aux lemmas marked **Aux 1**--**Aux 5** below): A proved
all of them, and additionally the inhabitation lemma at the hardest field,
`comparisonDecides_fires_at_a_negative_estimate`.  B fails and is
**disqualified on the inhabitation lemma**: it cannot even state it.  Frozen
line 2639 fixes `z` as the *signed*-integer parser output, and the frozen
`PolyApprox` contract of line 518 allows an estimate below `0` whenever the
true complexity is small -- for instance `comp = 0` with allowance `1` allows
`z = -1`.  `signedEstimateIsOutsideTheNaturalSpelling` proves in the kernel
that this legal frozen output is represented by no natural-number estimate, so
B's typing silently strengthens the frozen hypothesis by `0 <= z`.  That is not
cosmetic: an over-strong hypothesis makes the resulting lemma inapplicable at
precisely the outputs the frozen contract allows.  Faithfulness: A transcribes
lines 2639 and 2646--2651 symbol for symbol, including the sign and the
untruncated subtraction; B changes the type and silently truncates.  Length:
B is marginally shorter (no cast lemmas), which is the wrong trade.  Candidate
A wins on all three axes and is landed.

## Statement poles

* `effectiveMain` concludes `not PolyApprox` from five hypotheses, so the check
  it needs is that **its full binder list is consistent** -- otherwise the
  schema would be an unsatisfiable bundle that compiles green and proves
  nothing.  `effectiveMain_hypotheses_consistent` discharges every binder
  simultaneously at the banked legal `witnessClock`, with `PolyApprox` the
  genuine proposition `(0 : N) = 1` rather than `False`, and
  `effectiveMain_fires` then reaches the frozen conclusion *through*
  `effectiveMain` at exactly those values.  Noted for the record: for a
  refutation-shaped schema **any** consistent instantiation must falsify
  `PolyApprox`, so `hTailRuntime` and the second argument of `hSatDecided` are
  necessarily vacuous there; that is inherent to the frozen statement shape and
  not an artefact of this encoding.
* **No proper subset of `effectiveMain`'s binders proves it.**  One pole per
  frozen binder -- `citedBridgeIsLoadBearing`, `tailRuntimeIsLoadBearing`,
  `satDecisionIsLoadBearing`, `encodedViolationIsLoadBearing` -- exhibits an
  instantiation at which the other three binders and `hCited` all hold while
  the conclusion `not PolyApprox` is **false**.  In particular
  `satDecisionIsLoadBearing` shows that the binder consuming this module's
  proved arithmetic cannot be dropped.
* `BranchSeparation` is a universally quantified deliverable, so its pole is
  triviality rather than a trivial witness.  It is not a tautology:
  `strictAllowanceIsNecessary` exhibits legal values -- one below the frozen
  strict fit -- at which the very same display is **false**, and
  `comparisonDecides_fires_at_a_negative_estimate` exhibits both frozen cases at
  the exact allowance boundary, so the statement is neither empty nor free.
  `branchSeparation_fires` inhabits it at the banked witness clock.
* `promiseCasesAreExclusive` is the hypothesis-consistency pole for the two
  frozen promise cases: conjoining them at the frozen guard `k >= 1` is
  inconsistent, which is why they enter as guarded binders and never as a
  conjunction.
-/

namespace EthInapproximability.ParameterizedNP.EffectiveMain

open EthInapproximability.ParameterizedNP.PaddingAndClock
open EthInapproximability.ParameterizedNP.AlphaAllowance
open EthInapproximability.ParameterizedNP.LiteralFinalRuntime

/-! ## Part 1: the frozen approximation contract, split into its two frozen legs

Frozen line 518 fixes the `PolyApprox` accuracy contract as `|z - comp M| <= A`
with `A = alpha(T_n)` (frozen line 2637); `eq:k-level-gap`
(`12-iteration-specification.tex`, display lines 301--306) supplies the two
promise cases `comp <= Y_k` and `comp = Y_k + k`.  The two lemmas below are the
two left-hand columns of the frozen display at lines 2646--2651. -/

/-- **Aux 1 (the frozen `YES` estimate bound).**

Frozen line 2648: `YES : z <= Y_k + A`.  Its two inputs are the frozen accuracy
contract of line 518 and the `YES` half of `eq:k-level-gap`, `comp(R_k) <= Y_k`.
General in the allowance, the estimate, the complexity value and the budget; no
clock and no hypothesis beyond the two frozen ones.  Claims no reader item (see
"Reader counterparts"). -/
theorem approxUpper {A z c Y : ℤ} (happ : |z - c| ≤ A) (hc : c ≤ Y) : z ≤ Y + A := by
  have h : z - c ≤ A := (abs_le.mp happ).2
  omega

/-- **Aux 2 (the frozen `NO` estimate bound).**

Frozen line 2650: `NO : z >= Y_k + k - A`.  Its two inputs are the frozen
accuracy contract of line 518 and the `NO` half of `eq:k-level-gap`,
`comp(R_k) = D_k = Y_k + k`.  The subtraction is over the integers, exactly as
the frozen display writes it (reading note N4).  General in the allowance, the
estimate, the complexity value, the budget and the level count.  Claims no
reader item. -/
theorem approxLower {A z c Y k : ℤ} (happ : |z - c| ≤ A) (hc : c = Y + k) :
    Y + k - A ≤ z := by
  have h : -A ≤ z - c := (abs_le.mp happ).1
  omega

/-! ## Part 2: the frozen strictness step (`eq:alpha-gap-fit` at work)

The two "hence" columns of the frozen display at lines 2646--2651.  Each is
obtained from the frozen strict fit `2A < k` and nothing else, which is why
`eq:alpha-gap-fit` is the only other equation frozen line 2644 names. -/

/-- **Aux 3 (the frozen `YES` conclusion).**

Frozen line 2648: from `z <= Y_k + A` and `2 alpha(T_n) < L(n)`, "hence
`2z < 2Y_k + k`".  General in the allowance, the level count, the budget and
the estimate.  Claims no reader item. -/
theorem strictFitYes {A k Y z : ℤ} (hfit : 2 * A < k) (hz : z ≤ Y + A) :
    2 * z < 2 * Y + k := by omega

/-- **Aux 4 (the frozen `NO` conclusion).**

Frozen line 2650: from `z >= Y_k + k - A` and `2 alpha(T_n) < L(n)`, "hence
`2z > 2Y_k + k`".  General in the allowance, the level count, the budget and
the estimate.  Claims no reader item. -/
theorem strictFitNo {A k Y z : ℤ} (hfit : 2 * A < k) (hz : Y + k - A ≤ z) :
    2 * Y + k < 2 * z := by omega

/-- **Aux 5 (the frozen comparison decides).**

Frozen lines 2652--2654: "Thus comparing the integer `2z` with `2Y_k + k`
decides whether this branch is satisfiable."  Both frozen cases are used: the
forward direction is the contrapositive of the `NO` row, the backward direction
is the `YES` row.  The two `eq:k-level-gap` cases enter as the two guarded
binders `hyes` and `hno` and are never conjoined (reading note N2).

General in the allowance, the level count, the budget, the estimate, the
complexity value and the branch predicate.  Claims no reader item. -/
theorem comparisonDecides {A k Y z c : ℤ} {sat : Prop} (hfit : 2 * A < k)
    (happ : |z - c| ≤ A) (hyes : sat → c ≤ Y) (hno : ¬ sat → c = Y + k) :
    (2 * z < 2 * Y + k) ↔ sat := by
  constructor
  · intro hlt
    by_contra hsat
    have hno' : 2 * Y + k < 2 * z := strictFitNo hfit (approxLower happ (hno hsat))
    omega
  · intro hsat
    exact strictFitYes hfit (approxUpper happ (hyes hsat))

/-! ## Part 3: the frozen display at the frozen data `k = L(n)`, `A = alpha(T_n)`

Frozen lines 2634--2638 put `k = L(n)` and `A = alpha(T_n)`.  `BranchSeparation`
is the frozen display at those values, and `branchSeparation_holds` **proves**
it from the banked `eq:alpha-gap-fit`. -/

/-- The frozen decision display of lines 2646--2651, at the frozen data of line
2637, as a proposition about the clock alone.

Its two clauses are the two frozen rows.  Neither restates the other: the `NO`
row's hypothesis is the frozen equality at `Y_k + k` and its conclusion is a
strict *lower* bound on `2z`, so it is not a consequence of the `YES` row.
Both are printed in the frozen display, so this is a transcription and not a
premise bundle -- and it is proved rather than assumed
(`branchSeparation_holds`). -/
def BranchSeparation (V : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ slowIndex V n → ∀ Y z c : ℤ,
    |z - c| ≤ (alphaAllowance V (tCommon V n) : ℤ) →
      (c ≤ Y → 2 * z < 2 * Y + (slowIndex V n : ℤ)) ∧
      (c = Y + (slowIndex V n : ℤ) → 2 * Y + (slowIndex V n : ℤ) < 2 * z)

/-- **The frozen display holds** -- frozen lines 2646--2651, at the frozen data
`k = L(n)`, `A = alpha(T_n)` of line 2637.

The only input beyond Part 1 and Part 2 is the banked
`AlphaAllowance.alphaGapFit`, which is `eq:alpha-gap-fit` -- exactly the
equation frozen line 2644 names alongside `eq:k-level-gap`.  The frozen guard
`L(n) >= 1` of line 2633 is the explicit binder inside the statement, and the
frozen clock gates enter as the banked `SlowClockGateSet`, never as a new
bundle.

This is the module's real content: nothing below assumes it.  General in the
clock and the cutoff function.  Claims no reader item. -/
theorem branchSeparation_holds {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) :
    BranchSeparation V := by
  intro n hn Y z c happ
  have hfit : 2 * (alphaAllowance V (tCommon V n) : ℤ) < (slowIndex V n : ℤ) := by
    exact_mod_cast alphaGapFit hg n hn
  exact ⟨fun hc => strictFitYes hfit (approxUpper happ hc),
    fun hc => strictFitNo hfit (approxLower happ hc)⟩

/-- **The frozen comparison decides, at the frozen data** -- frozen lines
2652--2654, read off the frozen display.

The two `eq:k-level-gap` cases are the guarded binders `hyes`/`hno`.  General in
the clock, the source size, the budget, the estimate, the complexity value and
the branch predicate.  Claims no reader item. -/
theorem branchComparisonDecides {V : ℕ → ℕ} (hs : BranchSeparation V) {n : ℕ}
    (hn : 1 ≤ slowIndex V n) {Y z c : ℤ} {sat : Prop}
    (happ : |z - c| ≤ (alphaAllowance V (tCommon V n) : ℤ))
    (hyes : sat → c ≤ Y) (hno : ¬ sat → c = Y + (slowIndex V n : ℤ)) :
    (2 * z < 2 * Y + (slowIndex V n : ℤ)) ↔ sat := by
  obtain ⟨hY, hN⟩ := hs n hn Y z c happ
  constructor
  · intro hlt
    by_contra hsat
    have := hN (hno hsat)
    omega
  · intro hsat
    exact hY (hyes hsat)

/-- **The frozen tail guard** -- frozen line 2633: "For the remaining argument
`n >= n_tail`, so `L(n) >= 1`."

The frozen `n_tail` set is constrained to lie above the frozen `n_L`, and past
`n_L` the guard holds; both cutoffs are the banked ones of
`eq:literal-final-cutoff`.  General in the clock, the cutoff function, the three
remaining cutoff data and the source size.  Claims no reader item. -/
theorem tailIndexHasPositiveClockIndex {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    {nEps nMat : ℕ} {Rbr E : ℕ → ℕ}
    (h : ∃ N, TailCutoffSet nEps nMat (slowIndexCutoff hg) Rbr E N) {n : ℕ}
    (hn : tailCutoff nEps nMat (slowIndexCutoff hg) Rbr E h ≤ n) :
    1 ≤ slowIndex V n := by
  obtain ⟨-, -, hnL, -⟩ := tailCutoff_guards nEps nMat (slowIndexCutoff hg) Rbr E h hn
  exact (slowIndexCutoff_spec hg).2 n hnL

/-- **The frozen comparison decides on the frozen tail** -- frozen lines 2633
and 2652--2654 composed.

This is the form the frozen proof actually uses: the guard is not
re-hypothesized, it is supplied by the frozen `n_tail` constraint.  General in
the clock, the cutoff function, the cutoff data, the source size and the branch
data.  Claims no reader item. -/
theorem tailBranchComparisonDecides {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    {nEps nMat : ℕ} {Rbr E : ℕ → ℕ}
    (h : ∃ N, TailCutoffSet nEps nMat (slowIndexCutoff hg) Rbr E N) {n : ℕ}
    (hn : tailCutoff nEps nMat (slowIndexCutoff hg) Rbr E h ≤ n)
    {Y z c : ℤ} {sat : Prop}
    (happ : |z - c| ≤ (alphaAllowance V (tCommon V n) : ℤ))
    (hyes : sat → c ≤ Y) (hno : ¬ sat → c = Y + (slowIndex V n : ℤ)) :
    (2 * z < 2 * Y + (slowIndex V n : ℤ)) ↔ sat :=
  branchComparisonDecides (branchSeparation_holds hg)
    (tailIndexHasPositiveClockIndex hg h hn) happ hyes hno

/-! ## Part 4: `thm:effective-main` (frozen lines 2575--2587)

The frozen statement is conditional: "Assume `CitedETH`, and instantiate B1--B6
... Then `not PolyApprox_M(alpha)`."  Its proof (frozen lines 2589--2682) runs
through exactly four steps, and each is a named binder below because each is a
statement about the unmodelled machine layer:

* frozen 2590--2593, apply `eq:cited-to-encoded-ETH`   -> `hCitedToEncoded`;
* frozen 2594--2597, suppose `PolyApprox`              -> `intro happrox`;
* frozen 2598--2604 with 2662--2674, the runtime fit   -> `hTailRuntime`;
* frozen 2652--2658, the branch decision decides 3-SAT -> `hSatDecided`;
* frozen 2675--2681, the violation and contradiction   -> `hEncodedViolated`.

Only `hSatDecided`'s **antecedent** is discharged here, by
`branchSeparation_holds`; the frozen decision is proved, never assumed. -/

/-- **`thm:effective-main`** (frozen lines 2575--2587), as the closed
conditional statement its frozen proof (frozen lines 2589--2682) actually is.

`CitedETH`, `EncodedETH`, `PolyApprox`, `SatDecided` and `TailFits` are opaque
`Prop` parameters: never definitions, never axioms, carrying no field
(GAP-EXPOSED 2).  The four binders are the four frozen proof steps listed above,
in the frozen order.  The conclusion is the frozen `not PolyApprox_M(alpha)` of
frozen lines 2581--2583.

`hSatDecided` keeps the frozen antecedent `BranchSeparation V` -- a faithfulness
choice recorded in reading note N5 -- and it is supplied by
`branchSeparation_holds hg`, so the frozen decision display enters this theorem
as **proved content** rather than as an assumption.

General in the clock, the cutoff function and all five propositions.  Claims no
reader item; in particular this is **not** the reader's closed
`prop:paper-eth-consequence` (see "Reader counterparts") and no route completion
is claimed (GAP-EXPOSED 3). -/
theorem effectiveMain {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    {CitedETH EncodedETH PolyApprox SatDecided TailFits : Prop}
    (hCited : CitedETH)
    (hCitedToEncoded : CitedETH → EncodedETH)
    (hTailRuntime : PolyApprox → TailFits)
    (hSatDecided : BranchSeparation V → PolyApprox → SatDecided)
    (hEncodedViolated : SatDecided → TailFits → ¬ EncodedETH) :
    ¬ PolyApprox := by
  intro happrox
  exact hEncodedViolated (hSatDecided (branchSeparation_holds hg) happrox)
    (hTailRuntime happrox) (hCitedToEncoded hCited)

/-! ## Part 5: non-vacuity, hypothesis consistency, and statement poles -/

/-- **Hypothesis consistency for `effectiveMain`** (the check a five-hypothesis
schema needs: an unsatisfiable binder bundle compiles green and proves nothing).

Every binder of `effectiveMain` is discharged **simultaneously**, at the banked
`witnessClock` -- a legal clock, since `witnessClock_gates` proves all four
frozen gates -- under the assignment

* `CitedETH  := (0 : N) = 0`   (true),
* `EncodedETH := (1 : N) = 1`  (true),
* `PolyApprox := (0 : N) = 1`  (a genuine proposition, **not** `False`),
* `SatDecided := (4 : N) = 5`,
* `TailFits   := (2 : N) = 3`.

Noted for the record: for a refutation-shaped schema any consistent
instantiation must falsify `PolyApprox`, so `hTailRuntime` and the second
argument of `hSatDecided` are necessarily vacuous here.  That is inherent to the
frozen statement shape, not to this encoding.  General in the cutoff
function. -/
theorem effectiveMain_hypotheses_consistent (nstep : ℕ → ℕ) :
    SlowClockGateSet (witnessClock nstep) nstep
      ∧ ((0 : ℕ) = 0)
      ∧ (((0 : ℕ) = 0) → ((1 : ℕ) = 1))
      ∧ (((0 : ℕ) = 1) → ((2 : ℕ) = 3))
      ∧ (BranchSeparation (witnessClock nstep) → ((0 : ℕ) = 1) → ((4 : ℕ) = 5))
      ∧ (((4 : ℕ) = 5) → ((2 : ℕ) = 3) → ¬ ((1 : ℕ) = 1)) := by
  refine ⟨witnessClock_gates nstep, rfl, fun _ => rfl, fun h => absurd h (by norm_num),
    fun _ h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩

/-- **`effectiveMain` fires at legal values** (LANE-GATE 3).

The frozen conclusion is *reached through* `effectiveMain`, applied to the
legal instantiation of `effectiveMain_hypotheses_consistent` -- the banked
`witnessClock` with its four frozen gates, and `PolyApprox` the genuine
proposition `(0 : N) = 1`.  Together with that lemma this shows the schema is
neither an unsatisfiable bundle nor `False -> False`.  General in the cutoff
function. -/
theorem effectiveMain_fires (nstep : ℕ → ℕ) : ¬ ((0 : ℕ) = 1) := by
  obtain ⟨hg, hCited, hCitedToEncoded, hTailRuntime, hSatDecided, hEncodedViolated⟩ :=
    effectiveMain_hypotheses_consistent nstep
  exact effectiveMain hg hCited hCitedToEncoded hTailRuntime hSatDecided hEncodedViolated

/-- **Statement pole: `hCitedToEncoded` is load-bearing.**

Frozen lines 2590--2593 open the proof by applying `eq:cited-to-encoded-ETH`.
Drop that binder and `thm:effective-main` fails: at

* `CitedETH := (0 : N) = 0`, `EncodedETH := (1 : N) = 2`,
* `PolyApprox := (3 : N) = 3`, `SatDecided := (4 : N) = 4`,
  `TailFits := (2 : N) = 2`,

the three conjuncts below are the remaining binders of `effectiveMain` in the
frozen order, the fourth is `hCited`, and the fifth says the conclusion
`not PolyApprox` is **false** there.  General in the clock. -/
theorem citedBridgeIsLoadBearing (V : ℕ → ℕ) :
    (((3 : ℕ) = 3) → ((2 : ℕ) = 2))
      ∧ (BranchSeparation V → ((3 : ℕ) = 3) → ((4 : ℕ) = 4))
      ∧ (((4 : ℕ) = 4) → ((2 : ℕ) = 2) → ¬ ((1 : ℕ) = 2))
      ∧ ((0 : ℕ) = 0)
      ∧ ¬ ¬ ((3 : ℕ) = 3) := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ h => absurd h (by norm_num), rfl, ?_⟩
  exact fun h => h rfl

/-- **Statement pole: `hTailRuntime` is load-bearing.**

Frozen lines 2598--2604 and 2662--2674 are what put the controller's running
time inside the frozen envelope.  Drop that binder and `thm:effective-main`
fails: at

* `CitedETH := (0 : N) = 0`, `EncodedETH := (1 : N) = 1`,
* `PolyApprox := (3 : N) = 3`, `SatDecided := (4 : N) = 4`,
  `TailFits := (2 : N) = 5`,

the three conjuncts below are the remaining binders of `effectiveMain` in the
frozen order, the fourth is `hCited`, and the fifth says the conclusion
`not PolyApprox` is **false** there.  General in the clock. -/
theorem tailRuntimeIsLoadBearing (V : ℕ → ℕ) :
    (((0 : ℕ) = 0) → ((1 : ℕ) = 1))
      ∧ (BranchSeparation V → ((3 : ℕ) = 3) → ((4 : ℕ) = 4))
      ∧ (((4 : ℕ) = 4) → ((2 : ℕ) = 5) → ¬ ((1 : ℕ) = 1))
      ∧ ((0 : ℕ) = 0)
      ∧ ¬ ¬ ((3 : ℕ) = 3) := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ h => absurd h (by norm_num), rfl, ?_⟩
  exact fun h => h rfl

/-- **Statement pole: `hSatDecided` is load-bearing** -- so the binder that
consumes this module's proved arithmetic cannot be dropped.

Frozen lines 2652--2658 carry the branch decision to "`A_SAT` decides encoded
ordered 3-SAT on every bitstring".  Drop that binder and `thm:effective-main`
fails: at

* `CitedETH := (0 : N) = 0`, `EncodedETH := (1 : N) = 1`,
* `PolyApprox := (3 : N) = 3`, `SatDecided := (4 : N) = 5` (false),
  `TailFits := (2 : N) = 2`,

the three conjuncts below are the remaining binders of `effectiveMain` in the
frozen order -- the third being `hEncodedViolated`, which holds vacuously
because `SatDecided` is false -- the fourth is `hCited`, and the fifth says the
conclusion `not PolyApprox` is **false** there.  The clock does not occur,
because `BranchSeparation V` sits only inside the dropped binder. -/
theorem satDecisionIsLoadBearing :
    (((0 : ℕ) = 0) → ((1 : ℕ) = 1))
      ∧ (((3 : ℕ) = 3) → ((2 : ℕ) = 2))
      ∧ (((4 : ℕ) = 5) → ((2 : ℕ) = 2) → ¬ ((1 : ℕ) = 1))
      ∧ ((0 : ℕ) = 0)
      ∧ ¬ ¬ ((3 : ℕ) = 3) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun h => absurd h (by norm_num), rfl, ?_⟩
  exact fun h => h rfl

/-- **Statement pole: `hEncodedViolated` is load-bearing.**

Frozen lines 2675--2681 assemble the literal witnesses and conclude "violates
`EncodedETH(M, delta_ETH)`.  This is the required contradiction."  Drop that
binder and `thm:effective-main` fails: at

* `CitedETH := (0 : N) = 0`, `EncodedETH := (1 : N) = 1`,
* `PolyApprox := (3 : N) = 3`, `SatDecided := (4 : N) = 4`,
  `TailFits := (2 : N) = 2`,

the three conjuncts below are the remaining binders of `effectiveMain` in the
frozen order, the fourth is `hCited`, and the fifth says the conclusion
`not PolyApprox` is **false** there.  General in the clock. -/
theorem encodedViolationIsLoadBearing (V : ℕ → ℕ) :
    (((0 : ℕ) = 0) → ((1 : ℕ) = 1))
      ∧ (((3 : ℕ) = 3) → ((2 : ℕ) = 2))
      ∧ (BranchSeparation V → ((3 : ℕ) = 3) → ((4 : ℕ) = 4))
      ∧ ((0 : ℕ) = 0)
      ∧ ¬ ¬ ((3 : ℕ) = 3) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, ?_⟩
  exact fun h => h rfl

/-- **Inhabitation at the hardest field: both frozen rows fire at the exact
allowance boundary, with a negative estimate** (LANE-GATE 3).

Frozen line 2639 types `z` as the *signed*-integer parser output, and the frozen
contract of line 518 permits an estimate below zero when the true complexity is
small.  Both frozen cases are instantiated here at the smallest legal strict
fit, `A = 1` and `k = 3` (so `2A < k` holds by one):

* `YES`: `Y_k = 0`, `comp = 0 <= Y_k`, and the estimate `z = -1` is exactly at
  the allowance boundary and **negative**; the frozen comparison returns
  satisfiable.
* `NO`: `comp = Y_k + k = 3`, and the estimate `z = 2` is exactly at the
  allowance boundary; the frozen comparison returns unsatisfiable.

Neither conclusion is `0 <= _`: each is a strict integer comparison against the
frozen threshold `2Y_k + k = 3`, obtained with no slack in the accuracy
hypothesis. -/
theorem comparisonDecides_fires_at_a_negative_estimate :
    ((2 * (-1 : ℤ) < 2 * 0 + 3) ↔ True) ∧ ((2 * (2 : ℤ) < 2 * 0 + 3) ↔ False) := by
  refine ⟨comparisonDecides (A := 1) (k := 3) (Y := 0) (c := 0) (z := -1) (sat := True)
      (by norm_num) (by norm_num) (fun _ => le_refl 0) (fun h => absurd trivial h),
    comparisonDecides (A := 1) (k := 3) (Y := 0) (c := 3) (z := 2) (sat := False)
      (by norm_num) (by norm_num) (fun h => h.elim) (fun _ => by norm_num)⟩

/-- **Non-vacuity of `BranchSeparation` at legal parameter values**
(LANE-GATE 3).

`PaddingAndClock.witnessClock` is the banked nondegenerate inhabitant of the
four frozen clock gates, and `witnessClock_reaches_positive_index` is a source
size at which the frozen guard `1 <= L(n)` genuinely holds.  Both binders of the
frozen display are therefore inhabited **simultaneously** at legal values, and
the statement is the frozen `YES` row read there at a possibly negative estimate
sitting exactly on the allowance boundary.  General in the cutoff function and
the budget. -/
theorem branchSeparation_fires (nstep : ℕ → ℕ) (Y : ℤ) :
    2 * (Y - (alphaAllowance (witnessClock nstep)
        (tCommon (witnessClock nstep) (witnessClock nstep 1)) : ℤ))
      < 2 * Y + (slowIndex (witnessClock nstep) (witnessClock nstep 1) : ℤ) := by
  have happ : |(Y - (alphaAllowance (witnessClock nstep)
      (tCommon (witnessClock nstep) (witnessClock nstep 1)) : ℤ)) - Y|
      ≤ (alphaAllowance (witnessClock nstep)
          (tCommon (witnessClock nstep) (witnessClock nstep 1)) : ℤ) := by
    rw [abs_le]
    omega
  exact (branchSeparation_holds (witnessClock_gates nstep) _
    (witnessClock_reaches_positive_index nstep) Y _ Y happ).1 (le_refl Y)

/-- **Statement pole: the frozen strict fit is necessary, not decorative.**

Frozen `eq:alpha-gap-fit` reads `2 alpha(T_n) < L(n)`, strictly.  At the nearest
illegal values -- `A = 1`, `k = 2`, so `2A = k` and the fit fails by one -- the
frozen `YES` row is **false**: with `Y_k = 0` and `comp = 0 <= Y_k`, the
estimate `z = 1` is legal (`|1 - 0| <= 1`), yet `2z = 2` is not below the frozen
threshold `2Y_k + k = 2`, so the frozen comparison misclassifies a satisfiable
branch.  Hence `BranchSeparation` is not a tautology and the banked strict
allowance is exactly what carries it (reading note N3).

This is an illustrative numeric conjunction with no formal link to
`BranchSeparation` or `comparisonDecides`; it must never be cited as a formal
necessity result. -/
theorem strictAllowanceIsNecessary :
    2 * (1 : ℤ) = 2 ∧ |(1 : ℤ) - 0| ≤ 1 ∧ ((0 : ℤ) ≤ 0) ∧ ¬ (2 * (1 : ℤ) < 2 * 0 + 2) := by
  refine ⟨by norm_num, by norm_num, le_refl 0, by norm_num⟩

/-- **Statement pole: the two `eq:k-level-gap` cases are exclusive, which is why
they are guarded binders and never a conjunction** (reading note N2).

`12-iteration-specification.tex`, display lines 301--306, gives
`YES: comp(R_k) <= Y_k` and `NO: comp(R_k) = Y_k + k` as the two cases of one
construction.  At the frozen guard `k >= 1` they cannot both hold, so a
statement conjoining them would be vacuous.  General in the budget, the
complexity value and the level count. -/
theorem promiseCasesAreExclusive {Y c k : ℤ} (hk : 1 ≤ k) (hyes : c ≤ Y)
    (hno : c = Y + k) : False := by omega

/-- **Candidate B refuted in the kernel: a natural-number estimate cannot
express the frozen signed output.**

Frozen line 2639 fixes `z` as the *signed*-integer parser output, and the frozen
`PolyApprox` contract of line 518 permits `z = -1` when the true complexity is
`0` and the allowance is `1`.  No natural-number estimate represents that value,
so the rejected spelling silently adds `0 <= z` to the frozen hypothesis
(reading note N1). -/
theorem signedEstimateIsOutsideTheNaturalSpelling :
    |(-1 : ℤ) - 0| ≤ 1 ∧ ∀ z : ℕ, ((z : ℤ) ≠ -1) := by
  refine ⟨by norm_num, fun z => ?_⟩
  omega

end EthInapproximability.ParameterizedNP.EffectiveMain
