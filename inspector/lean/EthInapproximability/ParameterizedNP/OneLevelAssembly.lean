import EthInapproximability.ParameterizedNP.OneLevelCompletion

/-!
# Parameterized NP route: the mechanical assembly of one level (`thm:one-level`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ONELEVEL-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by the
`cc-t1q` tranche for `sec:one-level-assembly` (`11-one-level-assembly.tex`) and
the theorem it assembles, `thm:one-level`
(`07-one-level-construction.tex`, label line 37, statement lines 36--108).

`BRIDGE-COMPLETION-001`'s GAP-EXPOSED 1 named this row explicitly: frozen
`10-direct-bridge.tex:537--541` hands the *hypothesis-by-hypothesis* assembly to
`sec:one-level-assembly`, so the two promise-case budget theorems of
`OneLevelCompletion.lean` were deliberately **not** joined there -- "joining them
needs the promise hypothesis this subsection does not have".  This module
supplies exactly that promise hypothesis and nothing else.

## What the frozen theorem is, clause by clause

`05-public-records.tex:798--850` prints `thm:one-level` as **four separate
propositions about one output**, and line 849 states the discipline this module
follows: "Only after C1--C4 have been proved for the same output is the
aggregated one-level theorem invoked."

* **C1** (`05-public-records.tex:804--811`; `07-one-level-construction.tex:47--53`;
  `11-one-level-assembly.tex` `step:L-01`, label line 20).  "If `Public = Public'`
  and `Pi = Pi'`, then `LevelStep(Public,Pi) = LevelStep(Public',Pi')`.  In
  particular, supplying a proof of `YesCert(Public)` or a proof of
  `NoCert(Public)` to a later branch argument cannot change any trace field."
* **C2** (`05-public-records.tex:812--813`; `07-one-level-construction.tex:55--58`;
  `step:L-13`, label line 789).  `YesCert(Public) => comp R+ <= Y + H`.
* **C3** (`05-public-records.tex:814--822`; `07-one-level-construction.tex:60--67`;
  `step:L-12`, label line 766).  `NoCert(Public) => (comp R+ = D + H + 1 and
  Lambda_3(R+, 1, 2^{-b_out}, 3/5) >= D + H + 1)`, "the equality and the
  robustness lower bound use the same integer" (line 784).
* **C4** (`05-public-records.tex:823--847`; `07-one-level-construction.tex:69--106`;
  `step:L-14`, label line 809).  The carrier ledger equations
  `Rows(R+) = Cols(W)^Q`, `Cols(R+) = [Q] x Rows(W)`, their Stage-4 substitution
  `m_next = (q m_N)^Q`, `n_next = Q n_N^q`, and the integer side bounds
  `m_next, n_next <= 2^{z+}` at
  `z_N = max{clog_2 m_N, clog_2 n_N}` (`exp:E-14-raw-exact`, label line 842) and
  `z+ = max{Q(log_2 q + z_N), log_2 Q + q z_N}` (`exp:E-14-step`, label line 881).

## The promise hypothesis, and why the join is guarded

`OneLevelCompletion.promiseConjunction_refuted_at_step_I05` is a kernel
refutation: taking the `NO` input `comp W = C_W = C + w_q` and the `YES` input
`comp N <= Y + K` **on the same matrix at once** derives `Dsrc < Ysrc`, the exact
negation of the frozen side condition `Y_i <= D_i` of
`13-iteration-assembly.tex:431` (`step:I-05`).  Any unconditional join is
therefore a theorem about the empty parameter set.

Frozen `thm:one-level` does not join them unconditionally either: C2 and C3 are
**implications** out of `YesCert(Public)` and `NoCert(Public)`
(`def:level-certificates`, `05-public-records.tex`, label line 54, statement
lines 55--73).  This module transcribes that shape literally.  Every promise-side
input is a *guarded* binder `YesCert -> ...` or `NoCert -> ...`; no binder and no
conclusion of this module is an unguarded conjunction of the two sides.  The
guard is proved load-bearing twice:

* `oneLevelAssembly_promises_exclusive` -- at legal budgets the two certificates
  cannot both hold, straight through the banked refutation;
* `unguardedJoin_refuted_at_legal_budgets` -- even the two *conclusions*, taken
  unguarded, are contradictory at `Y <= D`.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/07-one-level-construction.tex`, `thm:one-level` (label line 37):
  line 43 (the overhead `H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`),
  clauses C1--C4 at lines 46--107, and `eq:one-level-exact-carriers`
  (label line 83, display lines 78--84).
* `sections/05-public-records.tex`:
  * `def:level-certificates` (label line 54, statement lines 55--73) -- the two
    promise propositions `YesCert(Public)` and `NoCert(Public)`, the source of
    the guarded binders;
  * the carrier and certificate ledger, lines 763--850, whose four-proposition
    proof ledger (lines 798--850) is the clause decomposition landed here;
  * lines 830--833, `Rows(R+) = Cols(W)^Q` and `Cols(R+) = [Q] x Rows(W)`, which
    `BRIDGE-OUTPUT-003` recorded as **not** claimed by the generic bridge because
    the Stage-4 substitution "needs the scale-alignment width `q`, which this
    generic bridge never sees";
  * lines 834--836, that substitution, `m_next = (q m_N)^Q`, `n_next = Q n_N^q`;
  * lines 839--847, `z+` and the two integer side bounds.
* `sections/11-one-level-assembly.tex`, the mechanical steps this module
  consumes by name:
  * `step:L-01` (label line 20, body lines 22--36) -- one fixed, unpadded,
    promise-independent rectangular output `R+ = transpose(Int_Q(W))` at
    `U = Int_q(N)`, `W = transpose U`;
  * `step:L-02` (label line 98) -- the exact robustness convention, three
    ceiling-defined rungs, `exp:E-02-rungs` (label line 110);
  * `step:L-03` (label line 127, hypotheses lines 130--136) -- the `NO`-case
    Stage-1 hypotheses `comp R = D`, `Lambda_3(R,1,2^{-b_0},3/5) >= D`,
    `D >= 3`; only the entry floor is consumed here, see GAP-EXPOSED 2;
  * `step:L-10` (label line 542) and `exp:E-10-common` (label line 638, display
    lines 632--639) -- `comp W = C_W`,
    `comp[W]_{1,theta,1-delta_U} >= C_W`, `Lambda_3(W,1,theta,3/5) >= C_W - 1`,
    followed at line 643 by "the direct bridge consumes only
    `exp:E-10-common`", which is exactly the guarded `NO` input list below;
  * `step:L-11` (label line 645) and `exp:E-11-exact` (label line 763),
    `exp:E-11-robust` (label line 756) -- discharged by the banked
    `BridgeOutputEquality.directRobustification`, never re-derived;
  * `step:L-12` (label line 766, body lines 769--787) -- the substitution
    `C_W + r_Q = D + H + 1` and "the equality and the robustness lower bound use
    the same integer, as required in clause C3" (line 784);
  * `step:L-13` (label line 789), line 793 `comp N <= Y + a + log_2 q_2 +
    log_2 s`, and lines 800--807 -- the `YES` chain and the sentence "the YES
    argument uses only `comp R <= Y` and source feasibility; it does not use an
    exact value for `comp R` or any robustness certificate";
  * `step:L-14` (label line 809), lines 858--882 -- `m_N`, `n_N`, the two exact
    wrapper cardinalities, and the integer upper-bound step `z+`;
  * `step:L-15` (label line 890) -- padding is final-only and is **not** part of
    `thm:one-level`, so no padded proxy appears anywhere below.
* `sections/13-iteration-assembly.tex`, `step:I-05` (label line 430, side
  conditions line 431) -- `Y_i <= D_i` and `3 <= D_i`, the legal-budget regime
  the two refutations are read at.
* `sections/02-mechanical-contract.tex` lines 767--775 -- the realized-input
  carrier invariant and the frozen legality `q, Q >= 2`, which is the binder
  `hq : 1 <= wq` (i.e. `q = 2^{w_q} >= 2`) carried on both C4 declarations.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex` of the same frozen
release was opened first-hand this tranche and each cited item read to check that
it states the same fact.  The reader locus of this row is
`cor:one-level-amplifier` (label line 155, statement lines 154--182), which
`BRIDGE-COMPLETION-001` recorded as deliberately unclaimed and reserved for
`ONELEVEL-001`.  Its lines are partitioned so that **no reader line is assigned
to two declarations**:

* lines 154--167 -- the corollary's setup and the sentence "The
  promise-independent output `R+ = Int_Q(W)^T`" -- to
  `oneLevelAssembly_promiseIndependent`;
* `eq:one-level-amplifier-conclusion` (label line 174) **first line**, line 170,
  `YES : comp R+ <= Y + H` -- to `oneLevelAssembly_yes`;
* the same display's **second and third lines**, lines 171--172,
  `NO : comp R+ = D + H + 1` and `Lambda_{R+}(1,2^{-b+},3/5) >= D + H + 1` -- to
  `oneLevelAssembly_no`;
* the corollary read as one aggregated statement of those clauses about one
  output -- to `oneLevelAssembly`, which claims no line the three clause
  declarations do not already carry and exists precisely because
  `05-public-records.tex:849` states the aggregation separately.

**Deliberately not claimed.**  `eq:one-level-exact-carriers` (reader label line
180, display lines 177--181) belongs to ledger row `SIZE-001` and is **not**
claimed here; `oneLevelAssembly_carriers` and `oneLevelAssembly_sideBound` take
their statements from the autoformalization side only
(`05-public-records.tex:823--847` and `11-one-level-assembly.tex:858--882`), and
the reader display is named as a navigation locus, never as their counterpart.
The reader's `thm:near-to-robust` and `eq:bridge-output` stay with
`BRIDGE-OUTPUT-002` / `-003` and are *consumed*, never restated.  The aux battery,
the two refutations and the witnesses of Parts 1, 3 and 4 claim no reader item:
they are interface properties, not transcriptions of reader statements.

Crosswalk row: `READER_CROSSWALK.md`, row 11 "Mechanical one-level assembly"
(`Sections 3--4, especially cor:one-level-amplifier`).

## Dependencies, imports, external adapters

* Imports `OneLevelCompletion.lean` only, hence transitively
  `DirectOutputEqualityClose`, `BridgeOutputEquality`, `EntryAssembly`,
  `DefectDischarge`, `CopyRestriction`, `DirectOutputLower`, `DirectOutput`,
  `EntryGates`, `ThreeCopyRowStep`, `TwoCopyLadder`, `DefectInduction`,
  `InheritedContracts`, `PilotStage3` and `EthInapproximability.Prelude`, and
  through it `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP balanced-family
  axiom is outside this module's closure, and there is no contact with
  `EXPANDER-001`, which by design has no Lean declaration and stays an explicit
  named hypothesis wherever it is needed.
* Consumed, never edited, widened or re-proved (names grep-verified against the
  banked sources):
  * `BridgeOutputEquality.directRobustification` -- `thm:direct-robustification`
    as one closed statement, the whole `step:L-11` discharge;
  * `BridgeOutputEquality.bridgeCarriers` and `.bridgeCarriers_canonical` --
    `eq:bridge-carriers` at an arbitrary and at the canonical width, the engine
    of C4;
  * `BridgeOutputEquality.rowsCard`, `.colsCard`;
  * `OneLevelCompletion.oneLevelCompletion_yes` -- the `YES` seed endpoint;
  * `OneLevelCompletion.alignedMatrix`, `.levelOutput` -- the pinned
    `W = transpose(Int_q(N))` and `R+ = transpose(Int_Q(W))` of `step:L-01`;
  * `OneLevelCompletion.stage4Overhead`, `.levelOverhead`, `.stage4Exact`,
    `.alignedExact`, `.noBudget_collect` -- the public budget names and the
    arithmetic engine of `step:L-12`;
  * `OneLevelCompletion.promiseConjunction_refuted_at_step_I05` -- the kernel
    refutation that makes the guard mandatory;
  * `EntryGates.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`, `.directEntryGates`,
    `.directEntryGates_fires`, `.deltaFixed`, `.Q0`;
  * `DirectOutputLower.xOut`;
  * `DirectOutput.directOutput_fires_second_witness`.
* External theorem adapters: **none new**.  One vendored name appears and is
  already inside the route's closure: `EthBridge.Rnext`
  (`vendor/npc-cc/EthBridge/Entry.lean:181`), used only through the banked
  carrier lemmas.
* Proof status: **new (elementary)** throughout.  Every deliverable is either an
  application of a banked kernel-checked route facade, linear `Nat` arithmetic
  (`omega`), `Fintype.card` bookkeeping, or a `Nat.clog` / `Nat.pow` monotonicity
  chain.  Nothing banked is edited or re-proved.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`): at
  most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings (k = 2) and the ranking

The genuinely open choice is **how the promise enters the joined theorem**.

**Candidate A (landed) -- the frozen implication shape.**  `YesCert` and
`NoCert` are abstract `Prop` parameters; every promise-side input is a guarded
binder, and C2 and C3 are guarded conclusions.  This is literally
`05-public-records.tex:812--822`.  Consistency is immediate (the two guards are
independent propositions), the two clauses stay syntactically separated -- C2
mentions no `Dsrc` and C3 no `Ysrc` -- and the aggregate can still state C1--C4
"for the same output" as line 849 requires.

**Candidate B (refuted) -- a two-sided premise bundle.**  Carry the `YES` input
and the `NO` inputs as unguarded binders of one theorem and conclude the
conjunction of both budgets.  In Lean this is not merely unfaithful: the
hypothesis bundle derives `Dsrc < Ysrc` through the inner selector bound, so at
the frozen `Y_i <= D_i` of `step:I-05` it has **no** legal instance, and even its
two conclusions alone are contradictory.  Refuted here, not in prose, by
`oneLevelAssembly_promises_exclusive` (through the banked
`promiseConjunction_refuted_at_step_I05`) and by
`unguardedJoin_refuted_at_legal_budgets`.

Aux battery: A = 8/8, B = 6/8 (B can state neither the promise-freedom property
nor the promise pole, having no promise label to be free of).  Faithfulness: A is
the frozen clause shape; B merges two propositions the paper prints as separate
items of one enumerate.  Length: A is shorter at every use site, since a caller
holding one promise supplies one guard.  **A is landed; B survives only as its
own refutation.**

## GAP-EXPOSED

1. **The Stage-1 to `W` chain is not formalized, so C2 and C3 are conditional.**
   Steps `L-03` through `L-10` derive `exp:E-10-common` and the Stage-4 `YES`
   budget from the promise certificates through Stages 1--4, the dense Stage-4
   theorem and the first wrapper.  None of that is in Lean yet
   (`STAGE1-001` .. `WRAP-001`).  This module therefore takes `exp:E-10-common`
   and `11-one-level-assembly.tex:793` as the guarded inputs the frozen text
   itself names at those two lines, and derives C2 and C3 from them.  **No route
   completion is claimed.**
2. **The parametric robust seed is a precise gap, and is deliberately not
   substituted.**  `step:L-03` states the `NO`-case Stage-1 hypotheses as the
   triple `comp R = D`, `Lambda_3(R,1,2^{-b_0},3/5) >= D`, `D >= 3`.  Only the
   entry floor `3 <= D` is carried below, as the guarded binder `hEntry`, and it
   is genuinely consumed (it is what makes `C_W >= 3` for the bridge).  The other
   two conjuncts are **not** bundled into a premise here, because the route has
   no Lean inhabitant of the middle one at any `b_0 >= 1`: `sec:full-cube-seed`
   opens at `12-iteration-specification.tex:16` with "Fix a requested depth
   `b >= 1`", so `lem:full-cube-seed` (label line 32) is scoped to `b >= 1`,
   while the landed `OneLevelCompletion.fullCubeSeed_lambda` sits at `b = 0`,
   outside that range (`BRIDGE-COMPLETION-001` GAP-EXPOSED 7).  Introducing the
   bundle without an inhabitant would put the principal deliverable behind a
   premise no legal parameter value is known to satisfy, and substituting the
   `b = 0` instance for the parametric seed is forbidden.  Nothing below reads
   the depth-zero instance as `lem:full-cube-seed`, and nothing below uses it at
   all.
3. **`Admissible(Public,Pi,T)` is not transcribed as a single predicate.**
   `def:admissible-parameters` is the whole finite list of
   `sec:effective-cutoff`; certifying a parameter tuple against it is
   `PARAM-001`'s work.  The binders below are the *structural* legality facts the
   assembly consumes -- `1 <= w_q`, `1 <= b_out`, `0 < delta_U < 1`,
   `0 < theta <= 1`, the frozen entry-gate pair, and nonempty carriers -- so the
   witnesses of Part 4 are *structurally legal* rather than *schedule certified*.
4. **C1 is the frozen congruence, not a semantic independence theorem.**
   `05-public-records.tex:806--808` states C1 as the equality of two
   `LevelStep` values at equal arguments, and lines 809--811 as the "in
   particular" that a promise argument cannot change a trace field.  Both are
   landed; what is *not* claimed is any statement about a hypothetical
   promise-reading constructor, which the route does not have.
5. **The size recurrence landed is the unconditional one.**
   `11-one-level-assembly.tex:883--888` separates the unconditional pair
   `exp:E-14-raw-exact` / `exp:E-14-step` from the *uniform majorant*
   `exp:E-14-raw` (label line 850), which is conditional on the checked
   size-successor row of `thm:eff-ledger` and is explicitly not consumed by "the
   finite one-level theorem and the exact recurrence" (line 856).  Only the
   unconditional pair is landed; the majorant stays with `SIZE-001` and
   `EFFECTIVE-001`.
-/

namespace EthInapproximability.ParameterizedNP.OneLevelAssembly

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion

/-! ## Part 0: the promise label and the two size names

Three public items.  `PromiseCase` is a **label**, carrying no certificate and no
conclusion: it is the object C1's "in particular" sentence
(`05-public-records.tex:809--811`) quantifies over.  `sideExponent` and
`sideStep` are the two integers `z_N` and `z+` of `exp:E-14-raw-exact`
(label line 842) and `exp:E-14-step` (label line 881), written as transparent
`Nat` functions of public data.  None of the three has a complexity, robustness
or promise field (mechanical rules M1, M2). -/

/-- **The promise label of `def:level-certificates`**
(`05-public-records.tex`, label line 54).

Two constructors and no fields: this is the *name* of a promise branch, never a
certificate.  A certificate is an arbitrary `Prop` binder (`YesCert`, `NoCert`)
at every use site below, exactly as `thm:one-level` quantifies over proofs of
`YesCert(Public)` and `NoCert(Public)` without giving them structure. -/
inductive PromiseCase where
  /-- The `YES` branch, `YesCert(Public)` of `05-public-records.tex:56--61`. -/
  | yes : PromiseCase
  /-- The `NO` branch, `NoCert(Public)` of `05-public-records.tex:64--71`. -/
  | no : PromiseCase
  deriving DecidableEq, Repr

/-- **A promise-branch argument applied to the level output.**

`05-public-records.tex:809--811`: "supplying a proof of `YesCert(Public)` or a
proof of `NoCert(Public)` to a later branch argument cannot change any trace
field."  The frozen sentence is about *supplying* a branch argument, so the
branch is written as an argument here and the definition discards it.  What makes
the discard content rather than notation is `promiseFreedom_not_automatic`: a
function of `PromiseCase` need not be constant. -/
noncomputable def levelOutputOfCase {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) (_c : PromiseCase) :
    (Fin (Qwidth bout δU) → Fin (2 ^ wq) × X) →
      Fin (Qwidth bout δU) × (Fin (2 ^ wq) → Y) → Bool :=
  levelOutput N wq bout δU

/-- **`z_N = max{ceil(log_2 m_N), ceil(log_2 n_N)}`** --
`11-one-level-assembly.tex`, `exp:E-14-raw-exact` (label line 842, display lines
837--843); `05-public-records.tex:826`.

The frozen line defines `z_N` "directly from the constructed carriers", i.e. from
the two cardinalities and nothing else, and line 844 records the consequence
`|Rows(N)|, |Cols(N)| <= 2^{z_N}` "without an asymptotic witness".  `Nat.clog 2`
is the integer `ceil(log_2 .)`, so the two frozen ceilings are literal. -/
def sideExponent (mN nN : ℕ) : ℕ := max (Nat.clog 2 mN) (Nat.clog 2 nN)

/-- **`z+ = max{Q(log_2 q + z_N), log_2 Q + q z_N}`** --
`11-one-level-assembly.tex`, `exp:E-14-step` (label line 881, display lines
876--882); `05-public-records.tex:841`.

Both interlace widths are carried by their **exponents** and never conflated:
`w_q = log_2 q` is the inner scale-alignment exponent and `r_Q = log_2 Q` the
outer bridge exponent, so the widths appear only as `2 ^ w_q` and `2 ^ r_Q`.
This is the M8 spelling the frozen line uses, and it is why the definition takes
`wq` and `rQv` rather than `q` and `Q`. -/
def sideStep (wq rQv zN : ℕ) : ℕ :=
  max (2 ^ rQv * (wq + zN)) (rQv + 2 ^ wq * zN)

/-! ## Part 1: the aux-lemma battery

Eight general properties.  None is about a pinned instance: each quantifies over
arbitrary carriers, widths, exponents or cardinalities. -/

/-- **Aux 1 (the two frozen ceilings do bound the two carriers).**

`11-one-level-assembly.tex:844`: "Thus `|Rows(N)|, |Cols(N)| <= 2^{z_N}` without
an asymptotic witness."  Both halves at once, general in the two cardinalities.
This is the only property of `z_N` the size step uses. -/
lemma sideExponent_bounds (mN nN : ℕ) :
    mN ≤ 2 ^ sideExponent mN nN ∧ nN ≤ 2 ^ sideExponent mN nN := by
  constructor
  · calc mN ≤ 2 ^ Nat.clog 2 mN := Nat.le_pow_clog (by norm_num) mN
      _ ≤ 2 ^ sideExponent mN nN :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  · calc nN ≤ 2 ^ Nat.clog 2 nN := Nat.le_pow_clog (by norm_num) nN
      _ ≤ 2 ^ sideExponent mN nN :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

/-- **Aux 2 (the size step dominates both of its branches).**

Readout of the maximum in `exp:E-14-step`.  General in all three exponents; it is
what lets the two carrier estimates, which land on different branches, be stated
at the single integer `z+` the frozen line defines. -/
lemma sideStep_bounds (wq rQv zN : ℕ) :
    2 ^ rQv * (wq + zN) ≤ sideStep wq rQv zN ∧
      rQv + 2 ^ wq * zN ≤ sideStep wq rQv zN :=
  ⟨le_max_left _ _, le_max_right _ _⟩

/-- **Aux 3 (the composed double-interlace carriers).**

`05-public-records.tex:830--836` in one statement, at **arbitrary** widths: the
carrier ledger rows `Rows(R+) = Cols(W)^Q`, `Cols(R+) = [Q] x Rows(W)` composed
with the same equations one level in, at `W = transpose(Int_q(N))`, give the
Stage-4 substitution `m_next = (q m_N)^Q`, `n_next = Q n_N^q`.

Purely the banked `BridgeOutputEquality.bridgeCarriers` applied twice; nothing is
re-proved.  General in `q` and `Q` -- the route's pinned widths appear only in
Part 2. -/
theorem doubleInterlaceCarriers {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (q Q : ℕ) :
    rowsCard (EthBridge.Rnext (EthBridge.Rnext N q) Q)
        = (q * rowsCard N) ^ Q ∧
      colsCard (EthBridge.Rnext (EthBridge.Rnext N q) Q)
        = Q * colsCard N ^ q := by
  obtain ⟨hrow, hcol⟩ := bridgeCarriers (EthBridge.Rnext N q) Q
  obtain ⟨hrow0, hcol0⟩ := bridgeCarriers N q
  rw [hrow, hcol, hrow0, hcol0]
  exact ⟨rfl, rfl⟩

/-- **Aux 4 (the row branch of the size step, as arithmetic).**

`11-one-level-assembly.tex:867--870`: `(q m_N)^Q <= (2^{log_2 q} 2^{z_N})^Q =
2^{Q(log_2 q + z_N)}` when `m_N <= 2^{z_N}` and `q = 2^{w_q}`.  Stated at four
arbitrary numbers, so it is the shape of the estimate and not the route's
values. -/
lemma rowBranch_bound (w z Q m : ℕ) (h : m ≤ 2 ^ z) :
    (2 ^ w * m) ^ Q ≤ 2 ^ (Q * (w + z)) := by
  have h1 : 2 ^ w * m ≤ 2 ^ (w + z) := by
    calc 2 ^ w * m ≤ 2 ^ w * 2 ^ z := Nat.mul_le_mul_left _ h
      _ = 2 ^ (w + z) := (pow_add 2 w z).symm
  calc (2 ^ w * m) ^ Q ≤ (2 ^ (w + z)) ^ Q := Nat.pow_le_pow_left h1 Q
    _ = 2 ^ ((w + z) * Q) := by rw [← pow_mul]
    _ = 2 ^ (Q * (w + z)) := by rw [Nat.mul_comm]

/-- **Aux 5 (the column branch of the size step, as arithmetic).**

`11-one-level-assembly.tex:871--873`: `Q n_N^q <= 2^{log_2 Q}(2^{z_N})^q =
2^{log_2 Q + q z_N}` when `n_N <= 2^{z_N}` and `Q = 2^{r_Q}`.  General in all
four numbers. -/
lemma colBranch_bound (r q z n : ℕ) (h : n ≤ 2 ^ z) :
    2 ^ r * n ^ q ≤ 2 ^ (r + q * z) := by
  have h1 : n ^ q ≤ 2 ^ (q * z) := by
    calc n ^ q ≤ (2 ^ z) ^ q := Nat.pow_le_pow_left h q
      _ = 2 ^ (z * q) := by rw [← pow_mul]
      _ = 2 ^ (q * z) := by rw [Nat.mul_comm]
  calc 2 ^ r * n ^ q ≤ 2 ^ r * 2 ^ (q * z) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (r + q * z) := (pow_add 2 r (q * z)).symm

/-- **Aux 6 (a supplied promise branch cannot change the output).**

`05-public-records.tex:809--811` verbatim, at arbitrary branches.  Identity
property, general in both carriers, both exponents and the deletion parameter. -/
lemma levelOutput_promise_free {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) (c c' : PromiseCase) :
    levelOutputOfCase N wq bout δU c = levelOutputOfCase N wq bout δU c' := rfl

/-- **Aux 7 (the promise label really has two branches).**

Without this the previous lemma would be a statement about a one-element type and
would say nothing.  General: it is a property of the label, not of any use
site. -/
lemma promiseCase_ne : PromiseCase.yes ≠ PromiseCase.no := by decide

/-- **Aux 8 (the pole: branch-freedom is not automatic).**

A function of `PromiseCase` need **not** be constant, so aux 6 is a genuine
constraint on `levelOutput` rather than a triviality of the label.  This is the
LANE-GATE-4c line for C1: the trivial reading of "promise independence" fails
here, so the clause has content. -/
theorem promiseFreedom_not_automatic :
    ¬ ∀ f : PromiseCase → ℕ, f PromiseCase.yes = f PromiseCase.no := by
  intro h
  have hbad := h (fun c => match c with | PromiseCase.yes => 0 | PromiseCase.no => 1)
  simp only [] at hbad
  omega

/-! ## Part 2: the four clauses of `thm:one-level`

Each clause is a separate declaration, as `05-public-records.tex:801--802` prints
them -- "the proof ledger contains the following four separate propositions about
that one output" -- and the aggregate of Part 2d joins them "for the same output"
per line 849. -/

/-- **C1 -- promise independence** (`05-public-records.tex:804--811`;
`07-one-level-construction.tex:47--53`; `step:L-01`, label line 20).

Both halves of the frozen clause:

* the congruence of lines 806--808, `LevelStep(Public,Pi) = LevelStep(Public',Pi')`
  whenever `Public = Public'` and `Pi = Pi'`.  The output type depends on the
  widths, so equality across two argument tuples is heterogeneous; the hypotheses
  are exactly the frozen ones and nothing is assumed about the two tuples beyond
  their equality;
* the "in particular" of lines 809--811: a supplied promise branch changes
  nothing.

Reader counterpart: `04-bridge.tex:154--167`, "The promise-independent output
`R+ = Int_Q(W)^T`". -/
theorem oneLevelAssembly_promiseIndependent {X Y : Type*} [Fintype X] [Fintype Y]
    (N N' : X → Y → Bool) {wq wq' bout bout' : ℕ} {δU δU' : ℝ}
    (hN : N = N') (hwq : wq = wq') (hb : bout = bout') (hδ : δU = δU') :
    HEq (levelOutput N wq bout δU) (levelOutput N' wq' bout' δU') ∧
      ∀ c c' : PromiseCase,
        levelOutputOfCase N wq bout δU c = levelOutputOfCase N wq bout δU c' := by
  subst hN
  subst hwq
  subst hb
  subst hδ
  exact ⟨HEq.rfl, fun c c' => levelOutput_promise_free N wq bout δU c c'⟩

/-- **C2 -- the `YES` upper bound** (`05-public-records.tex:812--813`;
`07-one-level-construction.tex:55--58`; `step:L-13` `11:789`, body `11:789--807`).

`YesCert(Public) => comp R+ <= Y + H`.  The certificate is an abstract `Prop` and
the Stage-4 `YES` input of line 793, `comp N <= Y + a + log_2 q_2 + log_2 s`, is
**guarded by it**: this is the only way the two promise cases may be carried in
one module, since the unguarded pair derives the negation of `step:I-05` (see
`oneLevelAssembly_promises_exclusive`).

`Dsrc` does not occur in this statement, so it cannot constrain the pair
`(Dsrc, Ysrc)` and cannot contradict `Ysrc <= Dsrc`.  Lines 805--807 record that
the `YES` argument "uses only `comp R <= Y` and source feasibility; it does not
use an exact value for `comp R` or any robustness certificate" -- accordingly no
lower-bound binder, no robustness binder and no carrier binder appears.

Reader counterpart: `eq:one-level-amplifier-conclusion` first line,
`04-bridge.tex:170`. -/
theorem oneLevelAssembly_yes {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Ysrc a w2 ws wq bout : ℕ) {δU : ℝ} (YesCert : Prop)
    (hYesInput : YesCert → D N ≤ Ysrc + stage4Overhead a w2 ws) :
    YesCert →
      D (levelOutput N wq bout δU)
        ≤ Ysrc + levelOverhead a w2 ws wq (rQ bout δU) :=
  fun hc => oneLevelCompletion_yes N Ysrc a w2 ws wq bout (hYesInput hc)

/-- **C3 -- `NO` exactness and robustness** (`05-public-records.tex:814--822`;
`07-one-level-construction.tex:60--67`; `step:L-12`, label line 766).

`NoCert(Public) => (comp R+ = D + H + 1 and Lambda_3(R+,1,2^{-b_out},3/5) >=
D + H + 1)`, at the **one** integer `D + H + 1`, which is the content of line
784, "the equality and the robustness lower bound use the same integer, as
required in clause C3".

The guarded inputs are exactly the four things `step:L-10` hands the bridge, and
`11-one-level-assembly.tex:643` states that the bridge "consumes only
`exp:E-10-common`":

* `hEntry` -- the entry floor `3 <= D` of `step:L-03` (line 135) and
  `step:I-05` (line 431).  It is genuinely consumed: it is what makes
  `C_W = alignedExact >= 3`, the frozen `comp W = C_W >= 3` of
  `10-direct-bridge.tex:40`.  See GAP-EXPOSED 2 for why the other two Stage-1
  conjuncts are a gap rather than a premise;
* `hCW` -- `comp W = C_W`, the first display of `exp:E-10-common` (line 633) at
  the aligned value `C_W = C + w_q`;
* `hNear` -- its second display (line 635), `comp[W]_{1,theta,1-delta_U} >= C_W`;
* `hInput` -- its third display (line 637), `Lambda_3(W,1,theta,3/5) >= C_W - 1`.

The unguarded binders are the structural legality facts of
`thm:direct-robustification` (`10-direct-bridge.tex:38--41,53--56`), which are
promise-free public data.  `Ysrc` does not occur.

`step:L-11` is not re-derived: the banked
`BridgeOutputEquality.directRobustification` is applied once, and the only
arithmetic performed here is the substitution `C_W + r_Q = D + H + 1` of
`step:L-12`, i.e. the banked `OneLevelCompletion.noBudget_collect`.

Reader counterpart: `eq:one-level-amplifier-conclusion` second and third lines,
`04-bridge.tex:171--172`. -/
theorem oneLevelAssembly_no {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc a w2 ws wq bout : ℕ) {δU θ : ℝ} (NoCert : Prop)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hb : 1 ≤ bout) (hgates : directEntryGates bout δU θ (3 / 5))
    (hEntry : NoCert → 3 ≤ Dsrc)
    (hCW : NoCert → D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hNear : NoCert → alignedExact Dsrc a w2 ws wq
      ≤ Dfamily (interlaceFun (alignedMatrix N wq) 1)
          (bracketGE (Fin (2 ^ wq) → Y) (Fin (2 ^ wq) × X) 1 θ (1 - δU)))
    (hInput : NoCert → alignedExact Dsrc a w2 ws wq - 1
      ≤ LambdaGE (alignedMatrix N wq) 1 θ (3 / 5)) :
    NoCert →
      D (levelOutput N wq bout δU)
          = Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 ∧
        Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1
          ≤ LambdaGE (levelOutput N wq bout δU) 1 (xOut bout) ((3 : ℝ) / 5) := by
  intro hc
  have hYne : Nonempty Y := Fintype.card_pos_iff.mp hY
  have hXne : Nonempty X := Fintype.card_pos_iff.mp hX
  have hrow : 1 ≤ Fintype.card (Fin (2 ^ wq) → Y) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Classical.arbitrary Y⟩
  have hcol : 1 ≤ Fintype.card (Fin (2 ^ wq) × X) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, Nat.one_le_two_pow⟩, Classical.arbitrary X)⟩
  have h3 : 3 ≤ alignedExact Dsrc a w2 ws wq := by
    have hD := hEntry hc
    unfold alignedExact stage4Exact stage4Overhead
    omega
  obtain ⟨heq, hrob, -, -⟩ :=
    directRobustification (alignedMatrix N wq) (alignedExact Dsrc a w2 ws wq) bout
      hδ0 hδ1 hθ0 hθ1 hrow hcol (hCW hc) h3 (hNear hc) (hInput hc) hb hgates
  have heq' : D (levelOutput N wq bout δU)
      = alignedExact Dsrc a w2 ws wq + rQ bout δU := heq
  have hrob' : alignedExact Dsrc a w2 ws wq + rQ bout δU
      ≤ LambdaGE (levelOutput N wq bout δU) 1 (xOut bout) ((3 : ℝ) / 5) := hrob
  have hcollect := noBudget_collect Dsrc a w2 ws wq (rQ bout δU)
  refine ⟨?_, ?_⟩
  · rw [heq']
    exact hcollect
  · rw [← hcollect]
    exact hrob'

/-- **C4a -- the exact carrier equations**
(`05-public-records.tex:828--837`; `07-one-level-construction.tex:69--84`,
`eq:one-level-exact-carriers`; `step:L-14`, lines 858--864).

All four frozen equations of the clause, in the frozen order: the two carrier
ledger rows at the outer interlace,

    Rows(R+) = Cols(W)^Q,   Cols(R+) = [Q] x Rows(W),

and their Stage-4 substitution at `W = transpose(Int_q(N))`,

    m_next = (q m_N)^Q,     n_next = Q n_N^q,

with `m_N = |Rows(N)|`, `n_N = |Cols(N)|`, `q = 2^{w_q}` and
`Q = Qwidth b_out delta_U`.  No promise hypothesis occurs: the clause is public
data, per C1.

`hq : 1 <= w_q` is the frozen legality guard `q = 2^{w_q} >= 2` of
`02-mechanical-contract.tex:771--775`, carried for the same reason
`OneLevelCompletion.pinnedOutput_carriers` carries it: without it the
frozen-illegal `q = 1` would be an instantiation.  It is a **lower** bound on the
width and never an upper one.

Reader locus (navigation only, **not** claimed): `eq:one-level-exact-carriers`,
`04-bridge.tex:177--181`, which belongs to ledger row `SIZE-001`. -/
theorem oneLevelAssembly_carriers {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) (hq : 1 ≤ wq) :
    rowsCard (levelOutput N wq bout δU)
        = colsCard (alignedMatrix N wq) ^ Qwidth bout δU ∧
      colsCard (levelOutput N wq bout δU)
        = Qwidth bout δU * rowsCard (alignedMatrix N wq) ∧
      rowsCard (levelOutput N wq bout δU)
        = (2 ^ wq * rowsCard N) ^ Qwidth bout δU ∧
      colsCard (levelOutput N wq bout δU)
        = Qwidth bout δU * colsCard N ^ 2 ^ wq := by
  have _hq : 1 ≤ wq := hq
  obtain ⟨hledgerRow, hledgerCol⟩ :=
    bridgeCarriers_canonical (alignedMatrix N wq) bout δU
  obtain ⟨hrow, hcol⟩ := doubleInterlaceCarriers N (2 ^ wq) (Qwidth bout δU)
  exact ⟨hledgerRow, hledgerCol, hrow, hcol⟩

/-- **C4b -- the integer side bounds**
(`05-public-records.tex:839--847`; `07-one-level-construction.tex:86--106`,
`eq:one-level-side-recurrence`; `step:L-14`, lines 865--882).

`m_next <= 2^{z+}` and `n_next <= 2^{z+}` at the frozen `z_N` and `z+`, the
"unconditional one-level size recurrence" of line 883.  The proof is the frozen
one: the exact carriers of C4a, the two ceiling bounds `m_N, n_N <= 2^{z_N}` of
line 844, and the two power estimates of lines 867--873, at
`Q = 2^{r_Q}` (the banked `EntryGates.Qwidth_eq_two_pow`).

The uniform majorant `exp:E-14-raw` (label line 850) is **not** proved here; line
856 states that "the finite one-level theorem and the exact recurrence below do
not consume that uniform comparison", and it stays with `SIZE-001` (GAP-EXPOSED
5).

Reader locus (navigation only, not claimed): `04-bridge.tex:177--181`. -/
theorem oneLevelAssembly_sideBound {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) (hq : 1 ≤ wq) :
    rowsCard (levelOutput N wq bout δU)
        ≤ 2 ^ sideStep wq (rQ bout δU)
            (sideExponent (rowsCard N) (colsCard N)) ∧
      colsCard (levelOutput N wq bout δU)
        ≤ 2 ^ sideStep wq (rQ bout δU)
            (sideExponent (rowsCard N) (colsCard N)) := by
  obtain ⟨-, -, hrow, hcol⟩ := oneLevelAssembly_carriers N wq bout δU hq
  obtain ⟨hm, hn⟩ := sideExponent_bounds (rowsCard N) (colsCard N)
  obtain ⟨hleft, hright⟩ :=
    sideStep_bounds wq (rQ bout δU) (sideExponent (rowsCard N) (colsCard N))
  have hQ : Qwidth bout δU = 2 ^ rQ bout δU := Qwidth_eq_two_pow bout δU
  constructor
  · rw [hrow, hQ]
    calc (2 ^ wq * rowsCard N) ^ 2 ^ rQ bout δU
        ≤ 2 ^ (2 ^ rQ bout δU
            * (wq + sideExponent (rowsCard N) (colsCard N))) :=
          rowBranch_bound wq (sideExponent (rowsCard N) (colsCard N))
            (2 ^ rQ bout δU) (rowsCard N) hm
      _ ≤ 2 ^ sideStep wq (rQ bout δU)
            (sideExponent (rowsCard N) (colsCard N)) :=
          Nat.pow_le_pow_right (by norm_num) hleft
  · rw [hcol, hQ]
    calc 2 ^ rQ bout δU * colsCard N ^ 2 ^ wq
        ≤ 2 ^ (rQ bout δU
            + 2 ^ wq * sideExponent (rowsCard N) (colsCard N)) :=
          colBranch_bound (rQ bout δU) (2 ^ wq)
            (sideExponent (rowsCard N) (colsCard N)) (colsCard N) hn
      _ ≤ 2 ^ sideStep wq (rQ bout δU)
            (sideExponent (rowsCard N) (colsCard N)) :=
          Nat.pow_le_pow_right (by norm_num) hright

/-- **`thm:one-level` -- the aggregated one-level theorem**
(`07-one-level-construction.tex`, label line 37; the four propositions of
`05-public-records.tex:798--850`, aggregated as line 849 licenses:
"Only after C1--C4 have been proved for the same output is the aggregated
one-level theorem invoked").

The five conclusions are C1's "in particular" sentence, C2, C3, C4a's Stage-4
substitution and C4b, **all about the single term
`levelOutput N w_q b_out delta_U`** -- which is the formal content of "the same
output".  The overhead is the frozen
`H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q` of
`07-one-level-construction.tex:43`, i.e. the banked
`OneLevelCompletion.levelOverhead` at the five exponents.

**The promise is the only join.**  `YesCert` and `NoCert` are abstract `Prop`
binders; the `YES` input is guarded by the first and the four `NO` inputs by the
second, so no hypothesis of this theorem asserts both promise cases, and the two
budget conclusions are guarded implications rather than a conjunction.  Dropping
either guard makes the statement vacuous at every legal parameter value -- see
`oneLevelAssembly_promises_exclusive` and
`unguardedJoin_refuted_at_legal_budgets`, both of which are theorems here rather
than remarks.

**No route completion is claimed** (GAP-EXPOSED 1): the guarded inputs are the
frozen lines 643 and 793 themselves, and the chain that produces them from the
promise certificates through Stages 1--4 and the two wrappers is not yet in Lean.

Reader counterpart: `cor:one-level-amplifier` read as the aggregation of its
clauses, `04-bridge.tex:154--182`; the individual budget lines 170--172 are
carried by `oneLevelAssembly_yes` and `oneLevelAssembly_no` and are not
re-claimed here. -/
theorem oneLevelAssembly {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq bout : ℕ) {δU θ : ℝ}
    (YesCert NoCert : Prop)
    (hq : 1 ≤ wq) (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hb : 1 ≤ bout) (hgates : directEntryGates bout δU θ (3 / 5))
    (hYesInput : YesCert → D N ≤ Ysrc + stage4Overhead a w2 ws)
    (hEntry : NoCert → 3 ≤ Dsrc)
    (hCW : NoCert → D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hNear : NoCert → alignedExact Dsrc a w2 ws wq
      ≤ Dfamily (interlaceFun (alignedMatrix N wq) 1)
          (bracketGE (Fin (2 ^ wq) → Y) (Fin (2 ^ wq) × X) 1 θ (1 - δU)))
    (hInput : NoCert → alignedExact Dsrc a w2 ws wq - 1
      ≤ LambdaGE (alignedMatrix N wq) 1 θ (3 / 5)) :
    (∀ c c' : PromiseCase,
        levelOutputOfCase N wq bout δU c = levelOutputOfCase N wq bout δU c') ∧
      (YesCert → D (levelOutput N wq bout δU)
        ≤ Ysrc + levelOverhead a w2 ws wq (rQ bout δU)) ∧
      (NoCert → D (levelOutput N wq bout δU)
          = Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1 ∧
        Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1
          ≤ LambdaGE (levelOutput N wq bout δU) 1 (xOut bout) ((3 : ℝ) / 5)) ∧
      (rowsCard (levelOutput N wq bout δU)
          = (2 ^ wq * rowsCard N) ^ Qwidth bout δU ∧
        colsCard (levelOutput N wq bout δU)
          = Qwidth bout δU * colsCard N ^ 2 ^ wq) ∧
      (rowsCard (levelOutput N wq bout δU)
          ≤ 2 ^ sideStep wq (rQ bout δU)
              (sideExponent (rowsCard N) (colsCard N)) ∧
        colsCard (levelOutput N wq bout δU)
          ≤ 2 ^ sideStep wq (rQ bout δU)
              (sideExponent (rowsCard N) (colsCard N))) := by
  obtain ⟨-, -, hrow, hcol⟩ := oneLevelAssembly_carriers N wq bout δU hq
  refine ⟨fun c c' => levelOutput_promise_free N wq bout δU c c',
    oneLevelAssembly_yes N Ysrc a w2 ws wq bout YesCert hYesInput,
    oneLevelAssembly_no N Dsrc a w2 ws wq bout NoCert hX hY hδ0 hδ1 hθ0 hθ1 hb
      hgates hEntry hCW hNear hInput,
    ⟨hrow, hcol⟩,
    oneLevelAssembly_sideBound N wq bout δU hq⟩

/-! ## Part 3: the promise guard is load-bearing

Two refutations.  Together they say that the guard added in Part 2 is the *only*
thing standing between this module and a theorem about the empty parameter
set. -/

/-- **The two promise certificates are never both available at legal budgets.**

Straight through the banked
`OneLevelCompletion.promiseConjunction_refuted_at_step_I05`: the `NO` input at
`hn` and the `YES` input at `hy` are exactly the pair that derives
`Dsrc < Ysrc`, and `step:I-05` (`13-iteration-assembly.tex:431`) fixes
`Y_i <= D_i` at every level "including every one-level call site".

So the guards of `oneLevelAssembly` are not decoration: an instantiation in which
both certificates hold has no legal parameter value at all.  General in every
parameter. -/
theorem oneLevelAssembly_promises_exclusive {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc Ysrc a w2 ws wq : ℕ) (YesCert NoCert : Prop)
    (hYD : Ysrc ≤ Dsrc)
    (hYesInput : YesCert → D N ≤ Ysrc + stage4Overhead a w2 ws)
    (hCW : NoCert → D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hy : YesCert) (hn : NoCert) : False :=
  promiseConjunction_refuted_at_step_I05 N Dsrc Ysrc a w2 ws wq hYD (hCW hn)
    (hYesInput hy)

/-- **Even the two conclusions, unguarded, are contradictory.**

The previous theorem refutes the joined *hypotheses*; this one refutes the joined
*conclusions*, so no repair that weakens the inputs can rescue an unguarded join.
At `Y <= D` the frozen budgets `comp R+ = D + H + 1` and `comp R+ <= Y + H` force
`D + 1 <= Y`.  This is the C2/C3 form of
`OneLevelCompletion.flatInterface_refuted_at_legal_budgets`, stated about the
level output rather than about a record.  General in all parameters. -/
theorem unguardedJoin_refuted_at_legal_budgets {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) {Dsrc Ysrc : ℕ} (a w2 ws wq bout : ℕ)
    {δU : ℝ} (hYD : Ysrc ≤ Dsrc)
    (hno : D (levelOutput N wq bout δU)
      = Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1)
    (hyes : D (levelOutput N wq bout δU)
      ≤ Ysrc + levelOverhead a w2 ws wq (rQ bout δU)) : False := by
  omega

/-! ## Part 4: non-vacuity

LANE-GATE 3 and LANE-GATE 4b/4c.  Each item excludes one degeneracy that a green
build cannot see.  The parameter tuples are *structurally legal* in the sense of
GAP-EXPOSED 3. -/

/-- **Witness 1: the aggregate fires on a genuinely inhabited `YES` promise.**

`YesCert := True` (so the `YES` guard is discharged by a real proof and the
conclusion is a real bound) and `NoCert := False`, at the first banked entry-gate
parameters of `EntryGates.directEntryGates_fires`: `b_out = 1`,
`delta_U = 1/60`, `theta = 1/192000`, whence `r_Q = 13` and `Q = 8192`; widths
`a = 4`, `w_2 = 6`, `w_s = 1`, `w_q = 3`; and the frozen seed budget `Y = 4` of
`13-iteration-assembly.tex:435`.

Then `K = 11`, `H = 27`, and the delivered `YES` budget is the frozen `31` of
`10-direct-bridge.tex:534` -- not the one-bit-weaker `32`, which would be
numerically indistinguishable from the `NO` value.  The carrier and size clauses
fire unconditionally at the same instantiation, so this single witness exercises
C1, C2, C4a and C4b at once.  `X`, `Y`, `N` stay universally quantified. -/
theorem oneLevelAssembly_fires_yes_witness {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hYesN : D N ≤ 4 + stage4Overhead 4 6 1) :
    rQ 1 (1 / 60 : ℝ) = 13 ∧ Qwidth 1 (1 / 60 : ℝ) = 8192 ∧
      stage4Overhead 4 6 1 = 11 ∧
      levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 ∧
      D (levelOutput N 3 1 (1 / 60 : ℝ)) ≤ 31 ∧
      rowsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        = (2 ^ 3 * rowsCard N) ^ Qwidth 1 (1 / 60 : ℝ) ∧
      colsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        = Qwidth 1 (1 / 60 : ℝ) * colsCard N ^ 2 ^ 3 ∧
      rowsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        ≤ 2 ^ sideStep 3 (rQ 1 (1 / 60 : ℝ))
            (sideExponent (rowsCard N) (colsCard N)) := by
  obtain ⟨hgates, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  have hK : stage4Overhead 4 6 1 = 11 := by unfold stage4Overhead; norm_num
  have hH : levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  obtain ⟨-, hyes, -, ⟨hrow, hcol⟩, hsize, -⟩ :=
    oneLevelAssembly N 4 4 4 6 1 3 1 (δU := 1 / 60) (θ := 1 / 192000)
      True False (by norm_num) hX hY (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (le_refl 1) hgates
      (fun _ => hYesN) (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      (fun h => h.elim)
  have hyes' := hyes trivial
  rw [hH] at hyes'
  exact ⟨hrQ, hQ, hK, hH, hyes', hrow, hcol, hsize⟩

/-- **Witness 2: the aggregate fires on a genuinely inhabited `NO` promise.**

The mirror instantiation: `NoCert := True`, `YesCert := False`, at the same
banked parameters and the frozen seed budget `D = 4`.  The delivered values are
the exact `comp R+ = 32` and the robustness bound at the **same** integer `32`,
which is clause C3's "same integer" requirement made numeric.

The four `NO` inputs stay universally quantified binders, since the bridge's
input matrix has no exhibited inhabitant in Lean and can have none until
Stages 1--4 land (GAP-EXPOSED 1).  No `YES` quantity occurs anywhere in the
statement, so the hypothesis context is consistent and the closing arithmetic is
genuine rather than an explosion. -/
theorem oneLevelAssembly_fires_no_witness {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCW : D (alignedMatrix N 3) = alignedExact 4 4 6 1 3)
    (hNear : alignedExact 4 4 6 1 3
      ≤ Dfamily (interlaceFun (alignedMatrix N 3) 1)
          (bracketGE (Fin (2 ^ 3) → Y) (Fin (2 ^ 3) × X) 1 (1 / 192000)
            (1 - 1 / 60)))
    (hInput : alignedExact 4 4 6 1 3 - 1
      ≤ LambdaGE (alignedMatrix N 3) 1 (1 / 192000) (3 / 5)) :
    rQ 1 (1 / 60 : ℝ) = 13 ∧ alignedExact 4 4 6 1 3 = 19 ∧
      levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 ∧
      D (levelOutput N 3 1 (1 / 60 : ℝ)) = 32 ∧
      (32 : ℕ) ≤ LambdaGE (levelOutput N 3 1 (1 / 60 : ℝ)) 1 (xOut 1)
        ((3 : ℝ) / 5) := by
  obtain ⟨hgates, -, hrQ, -, -, -, -⟩ := directEntryGates_fires
  have hCWval : alignedExact 4 4 6 1 3 = 19 := by
    unfold alignedExact stage4Exact stage4Overhead; norm_num
  have hH : levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  obtain ⟨-, -, hno, -, -⟩ :=
    oneLevelAssembly N 4 4 4 6 1 3 1 (δU := 1 / 60) (θ := 1 / 192000)
      False True (by norm_num) hX hY (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (le_refl 1) hgates
      (fun h => h.elim) (fun _ => by norm_num) (fun _ => hCW) (fun _ => hNear)
      (fun _ => hInput)
  obtain ⟨heq, hlam⟩ := hno trivial
  rw [hH] at heq hlam
  exact ⟨hrQ, hCWval, hH, by omega, by omega⟩

/-- **Witness 3: the aggregate fires again at a second, different arithmetic.**

The `YES` side at the second banked witness, `delta_U = 1/200`,
`theta = 1/640000`, where `r_Q = 14` and `Q = 16384`, and at the moved inner
width `w_q = 5`.  Now `H = 30` and the delivered budget is `34`.  Both interlace
widths, the overhead and the delivered constant move; a hypothesis list
satisfiable at only one numeral could not do that. -/
theorem oneLevelAssembly_fires_second_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) (hX : 1 ≤ Fintype.card X)
    (hY : 1 ≤ Fintype.card Y) (hYesN : D N ≤ 4 + stage4Overhead 4 6 1) :
    rQ 1 (1 / 200 : ℝ) = 14 ∧ Qwidth 1 (1 / 200 : ℝ) = 16384 ∧
      levelOverhead 4 6 1 5 (rQ 1 (1 / 200 : ℝ)) = 30 ∧
      D (levelOutput N 5 1 (1 / 200 : ℝ)) ≤ 34 ∧
      colsCard (levelOutput N 5 1 (1 / 200 : ℝ))
        = Qwidth 1 (1 / 200 : ℝ) * colsCard N ^ 2 ^ 5 := by
  obtain ⟨-, hrQ, hQ, hgates, -, -, -⟩ := directOutput_fires_second_witness
  have hH : levelOverhead 4 6 1 5 (rQ 1 (1 / 200 : ℝ)) = 30 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ]
  obtain ⟨-, hyes, -, ⟨-, hcol⟩, -⟩ :=
    oneLevelAssembly N 4 4 4 6 1 5 1 (δU := 1 / 200) (θ := 1 / 640000)
      True False (by norm_num) hX hY (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (le_refl 1) hgates
      (fun _ => hYesN) (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      (fun h => h.elim)
  have hyes' := hyes trivial
  rw [hH] at hyes'
  exact ⟨hrQ, hQ, hH, hyes', hcol⟩

/-- **Witness 4: the composed carrier equations fire nondegenerately, and pin the
orientation.**

At `m_N = 3`, `n_N = 5`, `q = 2`, `Q = 3` -- all distinct, all at least two --
the frozen equations read `m_next = (2 * 3)^3 = 216` and
`n_next = 3 * 5^2 = 75`.  The six separating conjuncts exclude every neighbouring
misreading of `05-public-records.tex:834--836`: `(Q m_N)^q = 81`,
`(q n_N)^Q = 1000`, `q m_N^Q = 54`, `q n_N^Q = 250`, `Q m_N^q = 27` and
`Q n_N = 15`.  A degenerate witness at `m_N = n_N = q = Q = 1` would satisfy the
two equations and separate nothing. -/
theorem doubleInterlaceCarriers_fires_nondegenerate :
    rowsCard (EthBridge.Rnext
        (EthBridge.Rnext (fun (_ : Fin 3) (_ : Fin 5) => true) 2) 3) = 216 ∧
      colsCard (EthBridge.Rnext
        (EthBridge.Rnext (fun (_ : Fin 3) (_ : Fin 5) => true) 2) 3) = 75 ∧
      (216 : ℕ) ≠ 81 ∧ (216 : ℕ) ≠ 1000 ∧ (216 : ℕ) ≠ 54 ∧
      (75 : ℕ) ≠ 250 ∧ (75 : ℕ) ≠ 27 ∧ (75 : ℕ) ≠ 15 := by
  obtain ⟨hrow, hcol⟩ :=
    doubleInterlaceCarriers (fun (_ : Fin 3) (_ : Fin 5) => true) 2 3
  refine ⟨?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩
  · rw [hrow]; simp [rowsCard]
  · rw [hcol]; simp [colsCard]

/-- **Witness 5: the size step fires, and genuinely depends on both exponents.**

At `m_N = 2^2`, `n_N = 2^3` the frozen `z_N` is `3`; at `w_q = 1`, `r_Q = 2` the
frozen `z+` is `max{4 * 4, 2 + 2 * 3} = 16`, and both carrier estimates hold
strictly inside `2^16`.  The last two conjuncts move one exponent at a time --
`z+ = 20` at `w_q = 2` and `z+ = 32` at `r_Q = 3` -- so neither interlace width is
being silently ignored, which is the degeneracy a single numeric check cannot
see. -/
theorem sideStep_fires_nondegenerate :
    sideExponent (2 ^ 2) (2 ^ 3) = 3 ∧ sideStep 1 2 3 = 16 ∧
      (2 ^ 1 * 2 ^ 2) ^ 2 ^ 2 ≤ 2 ^ sideStep 1 2 3 ∧
      2 ^ 2 * (2 ^ 3 : ℕ) ^ 2 ^ 1 ≤ 2 ^ sideStep 1 2 3 ∧
      sideStep 2 2 3 = 20 ∧ sideStep 1 3 3 = 32 := by
  have h2 : Nat.clog 2 (2 ^ 2) = 2 := Nat.clog_pow 2 2 (by norm_num)
  have h3 : Nat.clog 2 (2 ^ 3) = 3 := Nat.clog_pow 2 3 (by norm_num)
  have hz : sideExponent (2 ^ 2) (2 ^ 3) = 3 := by
    unfold sideExponent; rw [h2, h3]; norm_num
  refine ⟨hz, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold sideStep <;> norm_num

/-- **Witness 6: the promise guard is exercised at the frozen seed budgets.**

`13-iteration-assembly.tex:435` fixes `D_0 = Y_0 = a_seed + 1 >= 4` at the seed
level, and line 431 fixes `Y_i <= D_i` at every level.  At those legal values the
two certificates cannot both be available, which is what makes the guarded join
of `oneLevelAssembly` the only admissible shape.  `X`, `Y`, `N` and both
certificate propositions stay universally quantified. -/
theorem oneLevelAssembly_promises_exclusive_at_seed {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) (wq : ℕ) (YesCert NoCert : Prop)
    (hYesInput : YesCert → D N ≤ 4 + stage4Overhead 4 6 1)
    (hCW : NoCert → D (alignedMatrix N wq) = alignedExact 4 4 6 1 wq)
    (hy : YesCert) (hn : NoCert) : False :=
  oneLevelAssembly_promises_exclusive N 4 4 4 6 1 wq YesCert NoCert (le_refl 4)
    hYesInput hCW hy hn

/-- **Witness 7: promise independence fires, and is not automatic.**

The congruence of C1 at moved arguments together with the branch-freedom of its
"in particular" sentence, followed by the pole: a `PromiseCase`-indexed family
need not be constant, so C1 is a property of `levelOutput` and not of the label
type. -/
theorem oneLevelAssembly_promiseIndependent_fires {X Y : Type*} [Fintype X]
    [Fintype Y] (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) :
    HEq (levelOutput N wq bout δU) (levelOutput N wq bout δU) ∧
      levelOutputOfCase N wq bout δU PromiseCase.yes
        = levelOutputOfCase N wq bout δU PromiseCase.no ∧
      PromiseCase.yes ≠ PromiseCase.no ∧
      ¬ ∀ f : PromiseCase → ℕ, f PromiseCase.yes = f PromiseCase.no := by
  obtain ⟨hheq, hfree⟩ :=
    oneLevelAssembly_promiseIndependent N N (wq := wq) (wq' := wq)
      (bout := bout) (bout' := bout) (δU := δU) (δU' := δU) rfl rfl rfl rfl
  exact ⟨hheq, hfree PromiseCase.yes PromiseCase.no, promiseCase_ne,
    promiseFreedom_not_automatic⟩

end EthInapproximability.ParameterizedNP.OneLevelAssembly
