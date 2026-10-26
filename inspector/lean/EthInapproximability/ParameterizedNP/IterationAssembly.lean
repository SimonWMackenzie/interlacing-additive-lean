import EthInapproximability.ParameterizedNP.OneLevelAssembly

/-!
# Parameterized NP route: the per-step iteration assembly (`sec:iteration-assembly`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ITER-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 126),
opened by the `cc-t1r` tranche for `sec:iteration-assembly`
(`13-iteration-assembly.tex`) read together with the statement lock
`thm:fixed-level-gap-size` (`12-iteration-specification.tex`, label line 192).
The exact per-step carrier growth additionally serves the first half of
**`SIZE-001`** (line 127), whose fixed-level subexponential successor half stays
pending here.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## What this module lands

The frozen section is a twelve-step mechanical ladder.  This tranche lands the
**per-step** half of it -- the ladder `step:I-01` .. `step:I-05`, the exact
double-interlace carrier growth, and the two fixed-level promise inductions read
at a genuinely composed pair of levels.  `step:I-07` .. `step:I-12` (the iterated
size majorant, the padding-threshold search, the slow clock, the seed and
prefix-maximum bounds, the common padding and the common truth-table exponent)
are **not** claimed; see GAP-EXPOSED.

* **`step:I-01`** (label line 21, body lines 25--253).  The persistent one-level
  cutoff.  Landed: the **affine coefficient form** of lines 57--68,
  `(c_0(u) + b_0(u) clog_2(X+2)) L_P^2`, its **two literal maxima**
  `C_exc^0` and `B_exc^0` of `eq:Cexc0-literal-producer`
  (`06-parameter-schedule.tex`, label line 1574, display lines 1566--1574), the
  nonemptiness of the search `eq:Awrap-coefficient-search`
  (`06-parameter-schedule.tex`, label line 1677) exactly as lines 69--84 prove
  it, and the numerical margin `A_wrap >= C_exc + 4` of lines 92--97.  Lines
  66--68 are load-bearing and are transcribed literally: "Retaining `B_exc^0` is
  essential: repeated occurrences of the formal leaf `X` are not silently
  assigned coefficient one."  Accordingly **no unit-slope restatement** appears
  anywhere below; `bexcZero` is a separate binder throughout, and
  `unitSlopeSearch_is_not_the_frozen_search` is a kernel refutation of the
  reading that sets it to one.
* **`step:I-02`** (label line 255, body lines 258--289).  `K_rec = 16`,
  `c_0 = 3`, `c_{j+1} = 16(c_j + 1)` -- the frozen successor exponent -- and the
  cumulative threshold `n_val` with its closed form `expi:E-02-nval`
  (label line 277) and the eligibility consequence of lines 279--283.
* **`step:I-03`** (label line 327, body lines 331--405).  The public budget
  updates `Y_i = Y_{i-1} + H_i`, `D_i = D_{i-1} + H_i + 1`, their closed forms
  `expi:E-03-closed` (label line 385), and the arrow dictionary of lines
  336--347 and 388--394 that reconciles the section's one-based arrow numbering
  with the realization interface's zero-based slots (`conv:finite-slots`).
* **`step:I-04`** (label line 407, body lines 410--428).  The constant depth
  thread `beta_i = B(n) = E_2(n) = 2^{l(n)^2}`, the identity of the outgoing and
  next incoming depth, the frozen sentence "No density-monotonicity conversion
  and no rounding of the exponent occurs at this interface", and the arithmetic
  of line 427, `l(n) >= 3` and `B(n) >= 2^9 = 512` for `n >= 1`.
* **`step:I-05`** (label line 430, body lines 433--455).  `D_0 = Y_0 =
  a_seed + 1 >= 4 >= 3`, the gap `expi:E-05-gap` (label line 441)
  `D_i = Y_i + i`, the two side conditions `Y_i <= D_i` and `3 <= D_i` at every
  level "including every one-level call site", and the explicit no-truncation
  check of lines 450--455.
* **Exact carrier growth.**  `eq:fixed-level-carriers`
  (`12-iteration-specification.tex`, label line 264, display lines 260--265):
  `m_{i+1} = (q_i m_{N,i})^{Q_i}` and `n_{i+1} = Q_i (n_{N,i})^{q_i}`, at the
  **two separate** interlace widths, obtained from clause C4 of `thm:one-level`
  through the banked `OneLevelAssembly.oneLevelAssembly_carriers`.
* **The two fixed-level inductions.**  `thm:fixed-level-gap-size` (iii) and (iv)
  (`12-iteration-specification.tex`, lines 267--297) in their general `k`-level
  numeric form, plus the exact `k`-gap `eq:k-level-gap` (label line 305), and
  their typed instantiation at a genuinely composed **pair** of levels through
  the banked `OneLevelAssembly.oneLevelAssembly_yes` and `.oneLevelAssembly_no`
  (`step:I-06`, lines 457--514).

## Reader counterparts

`routes/parameterized-np/.../reader-facing/sections/05-iteration.tex` of the same
frozen release was opened first-hand this tranche and every cited item read to
confirm it states the same fact.  Its lines are partitioned so that **no reader
item is assigned to two declarations**:

* `eq:paper-budget-update` (label line 116, display lines 112--117) -- the two
  literal updates -- to `iterationBudgetLadder`;
* `thm:paper-finite-iteration` (label line 120) **closed-form display**,
  lines 129--133 -- to `iterationClosedBudgets`;
* the same theorem's **`YES` line**, line 137 -- to `fixedLevelGap_yes_induction`;
* its **`NO` line**, lines 138--140, **complexity half only** (line 138,
  `CC(R_j) = D_j`) -- to `fixedLevelGap_no_induction`.  The robustness half of
  that line (line 140) is **not** claimed at the `k`-level scale by anything
  here: it is delivered *per level* by the banked
  `OneLevelAssembly.oneLevelAssembly_no`, whose own reader item is
  `04-bridge.tex:171--172` (`ONELEVEL-001`), and `iterationStep_no` /
  `iterationTwoSteps_no` merely repackage that endpoint and claim no reader item;
* its **final sentence**, line 143 ("In particular the final additive separation
  is exactly `k`") -- to `kLevelAdditiveGap`;
* `eq:paper-exact-carrier-recurrence` (label line 166, boxed display lines
  161--167) -- to `iterationCarrierStep`.  This is a **different** display from
  `04-bridge.tex`'s `eq:one-level-exact-carriers`, which `ONELEVEL-001`
  deliberately declined and which stays with `SIZE-001`;
* `eq:paper-envelope` (label line 189, display lines 184--190) together with the
  equivalent least-integer characterization at line 192 -- to `ellN_spec`;
* line 272, "Use the common requested depth `b_i = B(n)` at the seed and at every
  level" -- to `depthThread_constant`;
* `eq:paper-exponent-recursion` (label line 270, display lines 262--271) together
  with `thm:paper-effective-level`'s successor `F(c) = 16(c+1)` (lines 202--203)
  -- to `cumulativeThreshold`.

**No reader counterpart exists for `step:I-01`'s coefficient pass.**  The reader
artifact never names `C_exc^0`, `B_exc^0`, `A_wrap`, `C_exc` or `C_size`; a
search of all nine reader section files for `exc`, `coefficient`, `affine` and
`binary length` returns only unrelated prose.  The nearest reader *locus* is
`thm:paper-effective-level` lines 216--235 ("The producer ... verifies every
finite hypothesis of the one-level amplifier"), which is named here as navigation
only and is **not** claimed as a counterpart by any declaration.  The coefficient
pass is autoformalization-only content, and is reported as such rather than
matched to reader prose.

Crosswalk rows: `READER_CROSSWALK.md` row 12 ("Slow iteration, padding, and ETH
interface") and row 13 ("Mechanical iteration and size propagation").

## Dependencies, imports, external adapters

* Imports `OneLevelAssembly.lean` only, hence transitively `OneLevelCompletion`,
  `DirectOutputEqualityClose`, `BridgeOutputEquality`, `EntryAssembly`,
  `DefectDischarge`, `CopyRestriction`, `DirectOutputLower`, `DirectOutput`,
  `EntryGates`, `ThreeCopyRowStep`, `TwoCopyLadder`, `DefectInduction`,
  `InheritedContracts`, `PilotStage3` and `EthInapproximability.Prelude`, and
  through it `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP balanced-family
  axiom stays outside this module's closure.  There is no contact with
  `EXPANDER-001`, which by design has no Lean declaration; nothing below turns a
  cited external interface into an axiom.
* Consumed, never edited, widened or re-proved (names grep-verified against the
  banked sources before use):
  * `OneLevelAssembly.oneLevelAssembly_yes` -- clause C2, the `YES` endpoint;
  * `OneLevelAssembly.oneLevelAssembly_no` -- clause C3, the `NO` endpoint, both
    of whose conclusions sit at the same integer;
  * `OneLevelAssembly.oneLevelAssembly_carriers` -- clause C4a, the exact
    double-interlace carrier equations;
  * `OneLevelAssembly.oneLevelAssembly_promises_exclusive` -- the guard
    refutation, re-read here at the iterated budgets;
  * `OneLevelCompletion.levelOutput`, `.alignedMatrix`, `.alignedExact`,
    `.stage4Overhead`, `.levelOverhead`;
  * `EntryGates.rQ`, `.Qwidth`, `.directEntryGates`, `.directEntryGates_fires`;
  * `DirectOutputLower.xOut`;
  * `DirectOutput.directOutput_fires_second_witness`;
  * `BridgeOutputEquality.rowsCard`, `.colsCard`.
* External theorem adapters: **none new**.
* Proof status: **new (elementary)** throughout -- `Nat` induction, `Finset`
  sums, `Nat.clog` monotonicity, and applications of the banked route facades.
* Axiom surface (Appendix D; `#print axioms` in `tools/AxiomAudit.lean`): at most
  `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings (k = 2) and the ranking

The genuinely open choice is **how a level boundary is represented**, given that
the row and column carriers change type at every level.

**Candidate A (landed) -- numeric ladder plus typed composed steps.**  The
budget, exponent, threshold and depth ladders are transparent `Nat` recursions of
public data; the carrier growth is stated on the two **cardinalities** `rowsCard`
and `colsCard`, which is exactly the data `lem:canonical-reindexing-invariance`
preserves; the two promise inductions are proved in general `k`-level numeric
form and then *instantiated* at a literally composed pair of levels, each
promise-side input a guarded binder out of an abstract `Prop`.  No new structure
is introduced, so no constructor can carry a conclusion.

**Candidate B (refuted) -- a dependent `n`-fold `LevelState` iteration.**  Carry
a structure with fields `(table, noComplexity, yesBudget, depth)` *plus* fields
asserting `comp table = noComplexity` and the robustness bound, and iterate it by
recursion on the level index.  Refuted on three independent counts, each of which
is a frozen line rather than a taste judgement:

1. `def:canonical-reindexing` (`12-iteration-specification.tex`, label line 107)
   closes at line 135 with "It never denotes a heterogeneous equality of
   functions."  A dependent `n`-fold iteration forces exactly the heterogeneous
   carrier equality the frozen definition forbids, and would need a Lean `Can`,
   which the route does not have.
2. The two proof-carrying fields are complexity and robustness **conclusions** in
   constructor data, against mechanical rules M2/M4 and against the frozen output
   tuple `(R^+, D+H+1, Y+H, b_out)` of `03-preliminaries.tex:450--453`, which is
   public data only.  The banked `OneLevelCompletion.SeedInterface` already fixes
   the correct shape: four public fields, with `noReading` and `yesReading` as
   separate predicates.
3. A state bundling **both** readings has no legal inhabitant: at the frozen side
   condition `Y_i <= D_i` of `step:I-05` the banked
   `promiseConjunction_refuted_at_step_I05` derives `False`, and
   `iteratedReadings_refuted_at_positive_gap` below re-derives it from the
   iterated budgets alone, at every `k >= 1`.

Aux battery: A = 18/18 below; B cannot state aux 13--15 at all (no separated
readings to compare) and fails aux 16--18 (no nondegenerate inhabitant at legal
values).  Faithfulness: A transcribes the frozen numeric ladder line by line and
keeps `q` and `Q` in separate binders everywhere; B merges the four frozen
carrier equations into a single opaque state.  Length: A is shorter at every use
site.  **A is landed; B survives only as its own refutation.**

## GAP-EXPOSED

1. **No route completion is claimed.**  Every promise-side input of every typed
   step below is a *guarded* binder, and the Stage-1 to Stage-4 chain that would
   produce those inputs from the previous level's output is not in Lean
   (`STAGE1-001` .. `WRAP-001`).  The composed pair of levels therefore takes the
   level-2 inputs as named hypotheses **consuming the level-1 conclusion**, which
   is the frozen shape of `step:I-06` lines 465--473 and 482--500, not a derived
   chain.  What *is* derived across the boundary is the entire numeric ladder:
   level 2's side conditions `Y_1 <= D_1` and `3 <= D_1` are proved from
   `step:I-05`, never assumed.
2. **`lem:canonical-reindexing-invariance` is not formalized.**
   `12-iteration-specification.tex` label line 140 is the transport
   `comp Can(M) = comp M` and its bracket analogue.  In Lean the level output
   keeps its structured carrier type and the chaining is read on cardinalities;
   the invariance itself is absorbed into the named transfer hypotheses of the
   composed steps and stays with `ITER-001`.
3. **`step:I-01`'s expression graph is not transcribed.**  What is landed is the
   *coefficient form and the two literal maxima* of lines 57--68 and the `A_wrap`
   search of lines 69--97, at an **arbitrary** recorded coefficient table.  The
   traversal that computes that table, the four adverse-term classes at line 120,
   the gate-record normal form (`eq:iteration-gate-record-normal-form`, label
   line 148), the protected-mass schedule at lines 182--199 and the three
   persistent-cutoff searches `ECut`/`PCut`/`DCut` at lines 201--230 are
   `PARAM-001` and `PILOT-PCUT-001` work.
4. **`step:I-02`'s realization clause is not claimed.**  Lines 284--289 state
   that no parameter record, balanced family, trace or admissibility proof is
   asserted at the threshold, and that realization is supplied separately by
   `thm:effective-materialization`.  Accordingly `cumulativeThreshold` concludes
   *numerical eligibility only*, at an arbitrary cutoff function `n_step`; it
   constructs nothing.
5. **`step:I-04`'s depth thread is landed as an equality of requested depths,**
   not as a claim that the Lean bridge output is a `def:robust-seed` at that
   depth -- that is clause C3 of `thm:one-level`, already banked, and is consumed
   rather than restated.
6. **Steps `I-07` .. `I-12` are out of scope.**  The iterated size majorant
   (`step:I-07`, `SIZE-001`/`EFFECTIVE-001`), the padding-threshold search
   (`step:I-08`), the numerically certified slow clock (`step:I-09`,
   `CLOCK-001`), the seed and prefix-maximum bounds (`step:I-10`, `SEED-001`),
   the common padding (`step:I-11`) and the common truth-table exponent
   (`step:I-12`) are named here only as the consumers of what is landed.
-/

namespace EthInapproximability.ParameterizedNP.IterationAssembly

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.OneLevelAssembly

/-! ## Part 0: public data

Every definition in this part is a function of public data alone -- a coefficient
table, an overhead sequence, a cutoff function, a source size, two carrier
cardinalities.  None has a complexity, robustness or promise field, and none is a
structure, so mechanical rules M1, M2 and M4 hold by construction rather than by
inspection. -/

/-! ### `step:I-01` -- the coefficient pass and the `A_wrap` search -/

/-- **The frozen affine exceptional-set binary length** --
`13-iteration-assembly.tex:57--68`, display lines 61--64; the same display is
`06-parameter-schedule.tex:1665--1669`.

```
(c_0(u) + b_0(u) clog_2(X + 2)) L_P^2
```

`X` is the formal integer leaf standing for `A_wrap` in the first pass
(`06-parameter-schedule.tex:1540--1541`), `L_P = clog_2(P_0)` is the driver of
line 471, and `c_0(u) = 9 c_0bar(u)`, `b_0(u) = 9 b_0bar(u)` already carry the
explicit factor-nine shift absorption of lines 1556--1565.

The **slope binder `b0` is separate and never defaulted to one**: line 66 of the
frozen section states that retaining it "is essential: repeated occurrences of
the formal leaf `X` are not silently assigned coefficient one".
`Nat.clog 2` is the frozen `clog_2` of `06-parameter-schedule.tex:75`,
`clog_2(z) = min{j >= 0 : z <= 2^j}`, on integer arguments. -/
def excAffine (c0 b0 X LP : ℕ) : ℕ := (c0 + b0 * Nat.clog 2 (X + 2)) * LP ^ 2

/-- **The literal maximum `max({1} ∪ ...)` of `eq:Cexc0-literal-producer`**
(`06-parameter-schedule.tex`, label line 1574, display lines 1566--1574).

The frozen producer takes `max` of the singleton `{1}` with a finite ordered list
of computed integers; the empty list therefore returns `1`, not `0`.  Written as
a fold so that the guard is part of the definition rather than of a side
lemma. -/
def literalMax (xs : List ℕ) : ℕ := xs.foldr max 1

@[simp] lemma literalMax_nil : literalMax [] = 1 := rfl

@[simp] lemma literalMax_cons (a : ℕ) (t : List ℕ) :
    literalMax (a :: t) = max a (literalMax t) := rfl

/-- **`C_exc^0`** -- the first literal maximum of `eq:Cexc0-literal-producer`.

The argument is the recorded coefficient table: one pair `(c_0(u), b_0(u))` per
root `u` of the ordered list `U_exc` of `eq:exceptional-coefficient-roots`
(`06-parameter-schedule.tex`, label line 1553, display lines 1541--1554).  The
frozen text calls these "two maxima of fifteen named, computed integers"
(line 1576), so the table is a genuine argument and never an invented
constant. -/
def cexcZero (tbl : List (ℕ × ℕ)) : ℕ := literalMax (tbl.map Prod.fst)

/-- **`B_exc^0`** -- the second literal maximum of `eq:Cexc0-literal-producer`,
taken over the **same** table, so that the pairing of the constant coefficient
with its slope at each node is preserved. -/
def bexcZero (tbl : List (ℕ × ℕ)) : ℕ := literalMax (tbl.map Prod.snd)

/-- **The tested predicate of `eq:Awrap-coefficient-search`**
(`06-parameter-schedule.tex`, label line 1677, display lines 1673--1677) together
with the frozen side condition "`A_wrap > c_seed`" of line 1670 and
`02-mechanical-contract.tex:878--880`, "the least integer greater than `c_seed`
satisfying `eq:Awrap-coefficient-search`".

```
c_seed < A    and    C_exc^0 + B_exc^0 clog_2(A + 2) + 4 <= A
```

Both conjuncts are needed: the first is the frozen strict inequality against the
seed constant, the second is the search itself.  `B_exc^0` occurs as a genuine
multiplier -- this predicate is *not* the unit-slope predicate, and
`unitSlopeSearch_is_not_the_frozen_search` refutes the identification. -/
def AwrapAdmissible (cseed C0 B0 A : ℕ) : Prop :=
  cseed < A ∧ C0 + B0 * Nat.clog 2 (A + 2) + 4 ≤ A

instance decidableAwrapAdmissible (cseed C0 B0 A : ℕ) :
    Decidable (AwrapAdmissible cseed C0 B0 A) := by
  unfold AwrapAdmissible
  infer_instance

/-! ### `step:I-02` -- the exponent recursion and the cumulative threshold -/

/-- **`c_0 = 3`, `c_{j+1} = 16(c_j + 1)`** --
`13-iteration-assembly.tex:259--262`, with `K_rec = 16` and the frozen sentence
of lines 264--266: "The rootwise `Successor_16` theorem supplied by
`thm:eff-ledger` is fixed before this recursion and has exactly the displayed
successor exponent."  Reader `eq:paper-exponent-recursion` (label line 270) and
`thm:paper-effective-level`'s `F(c) = 16(c+1)` (lines 202--203). -/
def cexp : ℕ → ℕ
  | 0 => 3
  | j + 1 => 16 * (cexp j + 1)

@[simp] lemma cexp_zero : cexp 0 = 3 := rfl

@[simp] lemma cexp_succ (j : ℕ) : cexp (j + 1) = 16 * (cexp j + 1) := rfl

/-- **`n_val(0) = 1`, `n_val(j+1) = max{n_val(j), n_step(c_j)}`** --
`13-iteration-assembly.tex:267--271`.

`n_step` is an **arbitrary** cutoff function here.  `step:I-01` supplies the
route's one, but nothing below depends on which function it is: lines 284--289
insist that this step "neither constructs records nor proves a promise-branch
conclusion", so the threshold is exactly a maximum and nothing else. -/
def nval (nstep : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => max (nval nstep j) (nstep (cexp j))

@[simp] lemma nval_zero (nstep : ℕ → ℕ) : nval nstep 0 = 1 := rfl

@[simp] lemma nval_succ (nstep : ℕ → ℕ) (j : ℕ) :
    nval nstep (j + 1) = max (nval nstep j) (nstep (cexp j)) := rfl

/-! ### `step:I-03` -- the two public budget ladders -/

/-- **`Y_{i+1} = Y_i + H_i`** -- `eq:iterated-budgets`
(`12-iteration-specification.tex`, label line 239, display lines 235--240) and
`13-iteration-assembly.tex:390--393`, the zero-based reading of clause C2's
public update.  Reader `eq:paper-budget-update` (label line 116).

Zero-based, per `conv:finite-slots`; the section's one-based arrow numbering is
recovered by `budgetY_arrowDictionary`. -/
def budgetY (Y0 : ℕ) (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => Y0
  | j + 1 => budgetY Y0 H j + H j

/-- **`D_{i+1} = D_i + H_i + 1`** -- the second half of `eq:iterated-budgets`,
the zero-based reading of clause C3's public update.

The trailing `+ 1` is the raw Stage-4 one-bit gap and is the *only* asymmetry
between the two ladders; that is what makes the additive separation after `k`
levels exactly `k`. -/
def budgetD (D0 : ℕ) (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => D0
  | j + 1 => budgetD D0 H j + H j + 1

@[simp] lemma budgetY_zero (Y0 : ℕ) (H : ℕ → ℕ) : budgetY Y0 H 0 = Y0 := rfl

@[simp] lemma budgetY_succ (Y0 : ℕ) (H : ℕ → ℕ) (j : ℕ) :
    budgetY Y0 H (j + 1) = budgetY Y0 H j + H j := rfl

@[simp] lemma budgetD_zero (D0 : ℕ) (H : ℕ → ℕ) : budgetD D0 H 0 = D0 := rfl

@[simp] lemma budgetD_succ (D0 : ℕ) (H : ℕ → ℕ) (j : ℕ) :
    budgetD D0 H (j + 1) = budgetD D0 H j + H j + 1 := rfl

/-! ### `step:I-04` -- the envelope and the constant depth thread -/

/-- The frozen least-integer characterization of `l(n)` is inhabited.
`13-iteration-assembly.tex:248--249`: "`l(n)` is the least integer `r >= 2`
for which `n + 16 <= 2^{2^r}`"; reader `05-iteration.tex:192` states the same
equivalence for `eq:paper-envelope`. -/
lemma ellN_exists (n : ℕ) : ∃ r : ℕ, 2 ≤ r ∧ n + 16 ≤ 2 ^ 2 ^ r := by
  refine ⟨n + 16, by omega, ?_⟩
  have h1 : n + 16 ≤ 2 ^ (n + 16) := Nat.le_of_lt Nat.lt_two_pow_self
  calc n + 16 ≤ 2 ^ (n + 16) := h1
    _ ≤ 2 ^ 2 ^ (n + 16) := Nat.pow_le_pow_right (by norm_num) h1

/-- **`l(n) = max{2, ceil(log_2 log_2(n+16))}`** -- `13-iteration-assembly.tex:9`
and `eq:paper-envelope` (reader label line 189), transcribed through the frozen
equivalent least-integer form of `13-iteration-assembly.tex:248--249`.

The least-integer form is used because it is an exact integer predicate: the
nested real logarithm of the displayed formula is not evaluated anywhere in the
frozen reduction (`06-parameter-schedule.tex:71`, "No real logarithm or square
root is evaluated by the reduction"). -/
def ellN (n : ℕ) : ℕ := Nat.find (ellN_exists n)

/-- **`E_c(n) = 2^{l(n)^c}`** -- `13-iteration-assembly.tex:10`;
reader `eq:paper-envelope`. -/
def envE (c n : ℕ) : ℕ := 2 ^ ellN n ^ c

/-- **`B(n) = E_2(n)`** -- `13-iteration-assembly.tex:11` and `step:I-04`
line 415, the single scheduled robustness depth used at the seed and at every
level. -/
def depthB (n : ℕ) : ℕ := envE 2 n

/-! ### Exact carrier growth, at two separate widths -/

/-- **The row half of `eq:fixed-level-carriers`**
(`12-iteration-specification.tex`, label line 264):
`m_{i+1} = (q_i m_{N,i})^{Q_i}`.

The inner scale-alignment width `q` multiplies, the outer bridge width `Q`
exponentiates.  The two are distinct arguments in a fixed order and are never
interchanged; `carrierGrowth_orientation_pole` refutes the transposed reading. -/
def carrierRowNext (q mN Q : ℕ) : ℕ := (q * mN) ^ Q

/-- **The column half of `eq:fixed-level-carriers`**:
`n_{i+1} = Q_i (n_{N,i})^{q_i}`.

Here the roles are exchanged relative to the row half -- `Q` multiplies and `q`
exponentiates -- which is precisely the asymmetry a single carrier equation
cannot express and a single numeric check cannot see. -/
def carrierColNext (Q nN q : ℕ) : ℕ := Q * nN ^ q

/-! ### The two promise readings, kept separate -/

/-- **The `YES` reading of a level output** -- `13-iteration-assembly.tex:463`
and `12-iteration-specification.tex:273--276`, `comp R_j <= Y_j`.

A proposition about the output, never a field of anything.  Line 474 of the
frozen section records that this branch "consumes no robustness hypothesis", so
no density or depth occurs in it. -/
def levelYesReading {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (Yval : ℕ) : Prop := D M ≤ Yval

/-- **The `NO` reading of a level output** --
`13-iteration-assembly.tex:483--485` and `eq:fixed-level-no-induction`
(`12-iteration-specification.tex`, label line 296): `comp R_j = D_j` **and**
`Lambda_3(R_j, 1, 2^{-B(n)}, 3/5) >= D_j`.

Both conjuncts stand at the **same** integer `Dval`, which is the content of
`11-one-level-assembly.tex:784` carried through the iteration: "the equality and
the robustness lower bound use the same integer".  The density is `xOut bout`,
the frozen `2^{-b_out}` at the level's requested depth, and `bout` is a binder so
that `step:I-04`'s constant thread is a stated hypothesis rather than a silent
identification. -/
def levelNoReading {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (Dval bout : ℕ) : Prop :=
  D M = Dval ∧ Dval ≤ LambdaGE M 1 (xOut bout) ((3 : ℝ) / 5)

/-! ## Part 1: the aux-lemma battery

Eighteen general properties.  None is about a pinned instance: each quantifies
over arbitrary tables, sequences, cutoff functions, cardinalities, carriers or
source sizes. -/

/-- **Aux 1 (the frozen `clog_2` is identified by its defining sandwich).**

`06-parameter-schedule.tex:75`, `clog_2(z) = min{j >= 0 : z <= 2^j}`.  General in
both arguments; this is the only property of the ceiling logarithm used below,
and it is what makes every numeric reading of `A_wrap` checkable. -/
lemma clog_two_eq_succ (n j : ℕ) (hlt : 2 ^ j < n) (hle : n ≤ 2 ^ (j + 1)) :
    Nat.clog 2 n = j + 1 :=
  le_antisymm (Nat.clog_le_of_le_pow hle)
    ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt)

/-- **Aux 2 (the literal maximum carries its frozen floor).**

`eq:Cexc0-literal-producer` takes `max({1} ∪ ...)`, so the producer never returns
zero even on an empty node list.  General in the list. -/
lemma one_le_literalMax (xs : List ℕ) : 1 ≤ literalMax xs := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [literalMax_cons]
    exact le_trans ih (le_max_right _ _)

/-- **Aux 3 (the literal maximum dominates every recorded coefficient).**

The defining property of the two producers: every node's computed integer is
bounded by the emitted maximum.  General in the list and the member. -/
lemma le_literalMax : ∀ {xs : List ℕ} {x : ℕ}, x ∈ xs → x ≤ literalMax xs := by
  intro xs
  induction xs with
  | nil => intro x hx; cases hx
  | cons a t ih =>
    intro x hx
    rw [literalMax_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- **Aux 4 (both producers dominate their node, and both are at least one).**

The two maxima read off the *same* table at the *same* node, which is what keeps
the constant coefficient paired with its slope.  General in the table and the
node. -/
lemma cexcZero_bexcZero_spec {tbl : List (ℕ × ℕ)} {u : ℕ × ℕ} (hu : u ∈ tbl) :
    u.1 ≤ cexcZero tbl ∧ u.2 ≤ bexcZero tbl ∧
      1 ≤ cexcZero tbl ∧ 1 ≤ bexcZero tbl :=
  ⟨le_literalMax (List.mem_map.mpr ⟨u, hu, rfl⟩),
   le_literalMax (List.mem_map.mpr ⟨u, hu, rfl⟩),
   one_le_literalMax _, one_le_literalMax _⟩

/-- **Aux 5 (the affine form is monotone in its slope).**

Raising `b_0(u)` can only raise the emitted binary length, which is why the
frozen pass must retain `B_exc^0` rather than discard it: discarding it can only
*lower* the recorded majorant, and a lowered majorant is an unproved one.
General in all five numbers. -/
lemma excAffine_mono_slope (c0 b0 b0' X LP : ℕ) (h : b0 ≤ b0') :
    excAffine c0 b0 X LP ≤ excAffine c0 b0' X LP := by
  unfold excAffine
  exact Nat.mul_le_mul_right _
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _)

/-- **Aux 6 (the elementary induction the frozen proof names).**

`02-mechanical-contract.tex:891--892`: "The last inequality follows by the
elementary induction `M^2 + 2M + 4 <= 2^M` for `M >= 8`."  Transcribed at that
exact threshold and general in `M`. -/
lemma sq_le_two_pow (M : ℕ) (hM : 8 ≤ M) : M ^ 2 + 2 * M + 4 ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    have key : (n + 1) ^ 2 + 2 * (n + 1) + 4 ≤ 2 * (n ^ 2 + 2 * n + 4) := by
      nlinarith [sq_nonneg n]
    calc (n + 1) ^ 2 + 2 * (n + 1) + 4 ≤ 2 * (n ^ 2 + 2 * n + 4) := key
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **Aux 7 (`clog_2(2^M + 2) <= M + 1`).**

`13-iteration-assembly.tex:75--76`, "because `2^M + 2 <= 2^{M+1}`", and
`02-mechanical-contract.tex:886`.  General in `M >= 1`. -/
lemma clog_two_pow_add_two (M : ℕ) (hM : 1 ≤ M) :
    Nat.clog 2 (2 ^ M + 2) ≤ M + 1 := by
  refine Nat.clog_le_of_le_pow ?_
  have h2 : (2 : ℕ) ≤ 2 ^ M := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM
  calc 2 ^ M + 2 ≤ 2 ^ M + 2 ^ M := by omega
    _ = 2 ^ (M + 1) := by rw [pow_succ]; ring

/-- **Aux 8 (the exponent recursion is strictly increasing and floored at
three).**

`13-iteration-assembly.tex:573--575`: "The exponents `c_i` are strictly
increasing: since `c_i >= 3`, `c_{i+1} = 16(c_i + 1) > c_i`."  Both halves at
once, general in the index. -/
lemma cexp_ge_three_and_lt (j : ℕ) : 3 ≤ cexp j ∧ cexp j < cexp (j + 1) := by
  induction j with
  | zero => constructor <;> norm_num
  | succ n ih =>
    obtain ⟨h3, -⟩ := ih
    constructor <;> simp only [cexp_succ] <;> omega

/-- **Aux 9 (the cumulative threshold is exactly the maximum of
`expi:E-02-nval`).**

`13-iteration-assembly.tex`, label line 277, display lines 273--278:
`n_val(j) = max({1} ∪ {n_step(c_r) : 0 <= r < j})`.  Stated as the three
characterizing properties of that maximum -- it is at least one, it dominates
every earlier cutoff, and it is least among such bounds -- which is the frozen
`max` of a singleton with a finite set, without introducing any lattice
apparatus the frozen text does not use.  Proved by the frozen argument of
lines 279--281: "the formula is `1` when `j = 0`, and the recursion adjoins
exactly the term with `r = j`".  General in the cutoff function and the index. -/
lemma nval_closed (nstep : ℕ → ℕ) (j : ℕ) :
    1 ≤ nval nstep j ∧ (∀ r, r < j → nstep (cexp r) ≤ nval nstep j) ∧
      ∀ M, 1 ≤ M → (∀ r, r < j → nstep (cexp r) ≤ M) → nval nstep j ≤ M := by
  induction j with
  | zero =>
    refine ⟨by simp, fun _r hr => by omega, fun M hM _ => by simpa using hM⟩
  | succ n ih =>
    obtain ⟨h1, hdom, hleast⟩ := ih
    refine ⟨by rw [nval_succ]; omega, ?_, ?_⟩
    · intro r hr
      rw [nval_succ]
      rcases Nat.lt_or_ge r n with h | h
      · have := hdom r h
        omega
      · have hrn : r = n := by omega
        subst hrn
        omega
    · intro M hM hall
      have hn := hleast M hM fun r hr => hall r (by omega)
      have := hall n (by omega)
      rw [nval_succ]
      omega

/-- **Aux 10 (the threshold dominates each earlier cutoff, and is monotone).**

`13-iteration-assembly.tex:281--283`: "`n >= n_val(j)` implies
`n >= n_step(c_r)` for every `0 <= r < j`", together with the monotonicity of
`n_val` used at line 687.  General in the cutoff function and both indices. -/
lemma nval_ge_of_lt (nstep : ℕ → ℕ) {r j : ℕ} (hr : r < j) :
    nstep (cexp r) ≤ nval nstep j :=
  (nval_closed nstep j).2.1 r hr

/-- **Aux 11 (both budget ladders have the frozen closed forms).**

`expi:E-03-closed` (`13-iteration-assembly.tex`, label line 385, display lines
379--386) and `eq:fixed-level-closed-budgets`
(`12-iteration-specification.tex`, label line 251), in the zero-based reading:
`Y_j = Y_0 + sum_{i<j} H_i` and `D_j = D_0 + sum_{i<j} H_i + j`.  Both at once,
general in the seed budgets, the overhead sequence and the index. -/
lemma budget_closed_forms (Y0 D0 : ℕ) (H : ℕ → ℕ) (j : ℕ) :
    budgetY Y0 H j = Y0 + ∑ i ∈ Finset.range j, H i ∧
      budgetD D0 H j = D0 + (∑ i ∈ Finset.range j, H i) + j := by
  induction j with
  | zero => simp
  | succ n ih =>
    obtain ⟨hY, hD⟩ := ih
    rw [Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · rw [budgetY_succ, hY]; omega
    · rw [budgetD_succ, hD]; omega

/-- **Aux 12 (the arrow dictionary of `step:I-03`).**

`13-iteration-assembly.tex:336--347` fixes the dictionary between the section's
one-based arrow index and the realization interface's zero-based slot, and lines
388--394 record the resulting reconciliation, "if arrows are numbered from zero
and `H~_i = H_{i+1}`, the same transition reads `Y_{i+1} = Y_i + H~_i`".  Under
that dictionary the zero-based ladder is exactly the one-based closed form
`Y_i = Y_0 + sum_{r=1}^{i} H_r`.  General in both sequences and the index. -/
lemma budgetY_arrowDictionary (Y0 : ℕ) (Harrow H : ℕ → ℕ)
    (hdict : ∀ r, H r = Harrow (r + 1)) (j : ℕ) :
    budgetY Y0 H j = Y0 + ∑ r ∈ Finset.Icc 1 j, Harrow r := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hsum : ∑ r ∈ Finset.Icc 1 (n + 1), Harrow r
        = (∑ r ∈ Finset.Icc 1 n, Harrow r) + Harrow (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [budgetY_succ, ih, hdict n, hsum]
    omega

/-- **Aux 13 (the `NO` reading determines its integer, and both conjuncts sit on
it).**

Two general properties of the reading at once: it pins the value, and the frozen
"same integer" sentence is a consequence rather than an extra assumption.  This
is the property Candidate B cannot state, because a bundle offers no second value
to compare against. -/
lemma levelNoReading_spec {A B : Type*} [Fintype A] [Fintype B]
    {M : A → B → Bool} {v w bout : ℕ}
    (hv : levelNoReading M v bout) (hw : levelNoReading M w bout) :
    v = w ∧ D M ≤ LambdaGE M 1 (xOut bout) ((3 : ℝ) / 5) := by
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hw1, -⟩ := hw
  refine ⟨by omega, ?_⟩
  rw [hv1]
  exact hv2

/-- **Aux 14 (the `YES` reading is monotone in its budget).**

`13-iteration-assembly.tex:465--473` uses the reading only through this
monotonicity when the budget is rewritten by the closed form.  General in the
carriers, the matrix and both budgets. -/
lemma levelYesReading_mono {A B : Type*} [Fintype A] [Fintype B]
    {M : A → B → Bool} {v w : ℕ} (h : levelYesReading M v) (hvw : v ≤ w) :
    levelYesReading M w := le_trans h hvw

/-- **Aux 15 (the two readings on one output force the budgets to close).**

If a single matrix carries both readings then `Dval <= Yval`.  Since `step:I-05`
fixes `Y_i <= D_i` and the gap `D_i = Y_i + i` is strict for `i >= 1`, this is
what makes the two promise branches mutually exclusive from level one onwards; it
is used by `iteratedReadings_refuted_at_positive_gap`.  General in
everything. -/
lemma levelReadings_force_closure {A B : Type*} [Fintype A] [Fintype B]
    {M : A → B → Bool} {Dval Yval bout : ℕ}
    (hno : levelNoReading M Dval bout) (hyes : levelYesReading M Yval) :
    Dval ≤ Yval := by
  obtain ⟨h1, -⟩ := hno
  have h2 : D M ≤ Yval := hyes
  omega

/-- **Aux 16 (the frozen envelope is well defined and floored at three).**

`step:I-04` line 427 and `step:I-10` lines 738--739: "For `n >= 1`,
`n + 16 > 2^{2^2}`, so `l(n) >= 3`".  All three properties of `l(n)` used below
-- it satisfies its own predicate, it is minimal, and it is at least three for
every positive source size.  General in `n`. -/
lemma ellN_spec (n : ℕ) (hn : 1 ≤ n) :
    (2 ≤ ellN n ∧ n + 16 ≤ 2 ^ 2 ^ ellN n) ∧
      (∀ r, r < ellN n → ¬(2 ≤ r ∧ n + 16 ≤ 2 ^ 2 ^ r)) ∧ 3 ≤ ellN n := by
  have hspec : 2 ≤ ellN n ∧ n + 16 ≤ 2 ^ 2 ^ ellN n :=
    Nat.find_spec (ellN_exists n)
  have hmin : ∀ r, r < ellN n → ¬(2 ≤ r ∧ n + 16 ≤ 2 ^ 2 ^ r) := fun r hr =>
    Nat.find_min (ellN_exists n) hr
  refine ⟨hspec, hmin, ?_⟩
  by_contra hcon
  have h2 := hspec.1
  have heq : ellN n = 2 := by omega
  have hle := hspec.2
  rw [heq] at hle
  have hval : (2 : ℕ) ^ 2 ^ 2 = 16 := by norm_num
  rw [hval] at hle
  omega

/-- **Aux 17 (the scheduled depth is bounded below by the frozen `512`).**

`step:I-04` line 428: "`B(n) >= 2^9 = 512`, in particular `B(n) >= 1`."  Both
halves, general in every positive source size.  The lower bound is what makes the
banked one-level `NO` clause applicable at every level, since its guard is
`1 <= b_out`. -/
lemma depthB_ge (n : ℕ) (hn : 1 ≤ n) : 512 ≤ depthB n ∧ 1 ≤ depthB n := by
  obtain ⟨-, -, h3⟩ := ellN_spec n hn
  have hsq : 9 ≤ ellN n ^ 2 := by nlinarith
  have hpow : (512 : ℕ) ≤ 2 ^ ellN n ^ 2 := by
    calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ ellN n ^ 2 := Nat.pow_le_pow_right (by norm_num) hsq
  exact ⟨hpow, le_trans (by norm_num) hpow⟩

/-- **Aux 18 (both carrier halves are positive at legal widths).**

`02-mechanical-contract.tex` lines 771--775 fix `q, Q >= 2`, and reader
`05-iteration.tex:281` records the same invariant ("At every successor,
`q, Q >= 2` and `m^+ = (q m_N)^Q`, `n^+ = Q n_N^q`, so this lower-carrier
invariant is preserved").  Nonemptiness of both carriers is preserved by the
step, which is what lets the next level be invoked at all.  General in all four
numbers. -/
lemma carrierNext_pos (q mN Q nN : ℕ) (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hm : 1 ≤ mN) (hn : 1 ≤ nN) :
    1 ≤ carrierRowNext q mN Q ∧ 1 ≤ carrierColNext Q nN q := by
  refine ⟨Nat.one_le_pow _ _ (Nat.mul_pos hq hm), ?_⟩
  exact Nat.mul_le_mul hQ (Nat.one_le_pow _ _ hn)

/-! ## Part 2: `step:I-01` -- the coefficient pass

The `A_wrap` search, its nonemptiness proof transcribed line for line from
`13-iteration-assembly.tex:69--84`, and the numerical margin of lines 92--97. -/

/-- **The search of `eq:Awrap-coefficient-search` is nonempty** --
`13-iteration-assembly.tex:69--84`, and identically
`02-mechanical-contract.tex:880--896`.

The frozen witness is transcribed exactly: put

```
M = C_exc^0 + B_exc^0 + c_seed + 8,   A = 2^M,
```

then `clog_2(A + 2) <= M + 1` (aux 7, "because `2^M + 2 <= 2^{M+1}`"), and

```
C_exc^0 + B_exc^0 (M + 1) + 4 <= M + M(M + 1) + 4 <= 2^M = A
```

by aux 6.  Both conjuncts of the tested predicate are delivered: `A > c_seed`
because `c_seed < M < 2^M`.  General in all three inputs -- the frozen text fixes
`c_seed = 100` (`02-mechanical-contract.tex:896`), but the argument uses only
`M >= 8`, which the shift `+ 8` supplies unconditionally. -/
lemma awrap_search_nonempty (cseed C0 B0 : ℕ) :
    ∃ A, AwrapAdmissible cseed C0 B0 A := by
  refine ⟨2 ^ (C0 + B0 + cseed + 8), ?_, ?_⟩
  · have h1 : cseed < C0 + B0 + cseed + 8 := by omega
    exact lt_of_lt_of_le h1 (Nat.le_of_lt Nat.lt_two_pow_self)
  · set M := C0 + B0 + cseed + 8 with hMdef
    have hM8 : 8 ≤ M := by omega
    have hM1 : 1 ≤ M := by omega
    have hclog : Nat.clog 2 (2 ^ M + 2) ≤ M + 1 := clog_two_pow_add_two M hM1
    have hC0 : C0 ≤ M := by omega
    have hB0 : B0 ≤ M := by omega
    have hstep : B0 * Nat.clog 2 (2 ^ M + 2) ≤ M * (M + 1) :=
      Nat.mul_le_mul hB0 hclog
    calc C0 + B0 * Nat.clog 2 (2 ^ M + 2) + 4
        ≤ M + M * (M + 1) + 4 :=
          Nat.add_le_add (Nat.add_le_add hC0 hstep) (le_refl 4)
      _ = M ^ 2 + 2 * M + 4 := by ring
      _ ≤ 2 ^ M := sq_le_two_pow M hM8

/-- **`A_wrap`** -- the least tested integer of `eq:Awrap-coefficient-search`
above `c_seed` (`06-parameter-schedule.tex:1670--1677`;
`02-mechanical-contract.tex:878--880`).

Public data: a function of the seed constant and the two literal maxima alone.
It carries no promise case and no conclusion. -/
def awrap (cseed C0 B0 : ℕ) : ℕ := Nat.find (awrap_search_nonempty cseed C0 B0)

/-- **`C_exc = C_exc^0 + B_exc^0 clog_2(A_wrap + 2)`** --
`13-iteration-assembly.tex:86--91`, and identically
`06-parameter-schedule.tex:1680--1684`.

The slope `B_exc^0` multiplies the ceiling logarithm.  **This is not the
unit-slope expression** `C_exc^0 + clog_2(A_wrap + 2)`; the frozen text bans that
reading at line 65, and `unitSlopeSearch_is_not_the_frozen_search` refutes it in
the kernel. -/
def cexcOf (cseed C0 B0 : ℕ) : ℕ :=
  C0 + B0 * Nat.clog 2 (awrap cseed C0 B0 + 2)

/-- **`step:I-01`, the coefficient-pass deliverable**
(`13-iteration-assembly.tex:57--97`).

Five conclusions about the same triple, in the frozen order:

* the search is nonempty and `A_wrap` is a tested value -- lines 69--84;
* `A_wrap` is *least* among tested values -- "the least admissible integer
  `A_wrap` exists", line 84;
* `A_wrap > c_seed` -- line 81;
* the numerical margin `A_wrap >= C_exc + 4` and hence `A_wrap > C_exc` --
  lines 92--97.

The margin is the frozen consequence of the defining inequality, obtained by
substituting the definition of `C_exc`; nothing is re-derived and no unit-slope
shortcut is taken.  General in `c_seed` and in both literal maxima, so this is a
property of the search and not of the route's numerals.

Reader counterpart: **none**; see the module header.  The coefficient pass has no
reader item, and `thm:paper-effective-level` is named there as navigation only. -/
theorem coefficientPass_awrap (cseed C0 B0 : ℕ) :
    AwrapAdmissible cseed C0 B0 (awrap cseed C0 B0) ∧
      (∀ A, AwrapAdmissible cseed C0 B0 A → awrap cseed C0 B0 ≤ A) ∧
      cseed < awrap cseed C0 B0 ∧
      cexcOf cseed C0 B0 + 4 ≤ awrap cseed C0 B0 ∧
      cexcOf cseed C0 B0 < awrap cseed C0 B0 := by
  have hspec : AwrapAdmissible cseed C0 B0 (awrap cseed C0 B0) :=
    Nat.find_spec (awrap_search_nonempty cseed C0 B0)
  obtain ⟨hgt, hle⟩ := hspec
  have hmargin : cexcOf cseed C0 B0 + 4 ≤ awrap cseed C0 B0 := hle
  exact ⟨⟨hgt, hle⟩, fun A hA => Nat.find_min' _ hA, hgt, hmargin, by omega⟩

/-! ## Part 3: `step:I-02` -- the cumulative numerical threshold -/

/-- **`step:I-02`, the cumulative threshold**
(`13-iteration-assembly.tex:255--289`).

Four conclusions:

* the frozen closed form `expi:E-02-nval`, `n_val(j)` is exactly
  `max({1} ∪ {n_step(c_r) : 0 <= r < j})`, stated by its three characterizing
  properties;
* the eligibility consequence of lines 281--283: if `n >= n_val(j)` then
  `n >= n_step(c_r)` **simultaneously** for every `0 <= r < j`;
* the successor exponent is exactly the frozen `16(c + 1)`;
* the exponents are strictly increasing and floored at three (line 573).

The cutoff function `n_step` is an arbitrary argument: lines 284--289 state that
this step asserts no parameter record, balanced family, trace or admissibility
proof, so numerical eligibility is the whole conclusion (GAP-EXPOSED 4).

Reader counterpart: `eq:paper-exponent-recursion` (`05-iteration.tex`, label
line 270, display lines 262--271) together with `thm:paper-effective-level`'s
`F(c) = 16(c+1)` at lines 202--203. -/
theorem cumulativeThreshold (nstep : ℕ → ℕ) (n j : ℕ) (hn : nval nstep j ≤ n) :
    (1 ≤ nval nstep j ∧ (∀ r, r < j → nstep (cexp r) ≤ nval nstep j) ∧
        ∀ M, 1 ≤ M → (∀ r, r < j → nstep (cexp r) ≤ M) → nval nstep j ≤ M) ∧
      (∀ r, r < j → nstep (cexp r) ≤ n) ∧
      (∀ i, cexp (i + 1) = 16 * (cexp i + 1)) ∧
      (∀ i, 3 ≤ cexp i ∧ cexp i < cexp (i + 1)) :=
  ⟨nval_closed nstep j,
   fun _r hr => le_trans (nval_ge_of_lt nstep hr) hn,
   fun i => cexp_succ i,
   cexp_ge_three_and_lt⟩

/-! ## Part 4: `step:I-03` -- the escalating public budgets -/

/-- **`step:I-03`, the two literal updates and the arrow dictionary**
(`13-iteration-assembly.tex:376--394`).

Clause C2 of `thm:one-level` licenses `Y_i = Y_{i-1} + H_i` and clause C3
licenses `D_i = D_{i-1} + H_i + 1`; the third conclusion is the reconciliation of
the section's one-based arrow numbering with the zero-based realization slots,
lines 388--394.  General in the seed budgets, the overhead sequence and the
index.

Reader counterpart: `eq:paper-budget-update` (`05-iteration.tex`, label line 116,
display lines 112--117). -/
theorem iterationBudgetLadder (Y0 D0 : ℕ) (H Harrow : ℕ → ℕ)
    (hdict : ∀ r, H r = Harrow (r + 1)) (i : ℕ) :
    budgetY Y0 H (i + 1) = budgetY Y0 H i + H i ∧
      budgetD D0 H (i + 1) = budgetD D0 H i + H i + 1 ∧
      budgetY Y0 H i = Y0 + ∑ r ∈ Finset.Icc 1 i, Harrow r :=
  ⟨rfl, rfl, budgetY_arrowDictionary Y0 Harrow H hdict i⟩

/-- **`step:I-03`, the closed forms** -- `expi:E-03-closed`
(`13-iteration-assembly.tex`, label line 385) in its zero-based reading, and
`eq:fixed-level-closed-budgets` (`12-iteration-specification.tex`, label
line 251), together with the frozen consequence of line 253, "If `D_0 = Y_0`,
then `D_j = Y_j + j` for every such `j`", which is `expi:E-05-gap`
(label line 441).

General in the overhead sequence and the index; the last conjunct is guarded by
the frozen seed identity rather than assumed of an arbitrary pair.

Reader counterpart: `thm:paper-finite-iteration`'s closed-form display,
`05-iteration.tex:129--133`. -/
theorem iterationClosedBudgets (Y0 D0 : ℕ) (H : ℕ → ℕ) (hseed : D0 = Y0)
    (j : ℕ) :
    budgetY Y0 H j = Y0 + ∑ i ∈ Finset.range j, H i ∧
      budgetD D0 H j = D0 + (∑ i ∈ Finset.range j, H i) + j ∧
      budgetD D0 H j = budgetY Y0 H j + j := by
  obtain ⟨hY, hD⟩ := budget_closed_forms Y0 D0 H j
  exact ⟨hY, hD, by omega⟩

/-! ## Part 5: `step:I-04` -- the constant depth thread -/

/-- **`step:I-04`, the constant depth thread**
(`13-iteration-assembly.tex:407--428`).

The schedule makes the explicit choice `beta_i = B(n) = E_2(n) = 2^{l(n)^2}` for
every `i >= 0`, so level `i >= 1` is invoked with `b_0 = beta_{i-1} = B(n)` and
`b^+ = beta_i = B(n)`.  The conclusions are the frozen ones:

* the outgoing depth of level `i` is *literally* the incoming depth of level
  `i + 1` -- lines 423--425;
* consequently the two robustness densities coincide, which is the frozen
  sentence at line 426, "No density-monotonicity conversion and no rounding of
  the exponent occurs at this interface";
* `B(n) >= 512`, hence `B(n) >= 1` -- lines 427--428, which is exactly the guard
  `1 <= b_out` the banked `NO` clause requires.

That the second conclusion has content -- i.e. that `xOut` is not constant -- is
`depthThread_pole`.  General in the source size and the level index.

Reader counterpart: `05-iteration.tex:272`, "Use the common requested depth
`b_i = B(n)` at the seed and at every level." -/
theorem depthThread_constant (n : ℕ) (hn : 1 ≤ n) (β : ℕ → ℕ)
    (hβ : ∀ i, β i = depthB n) (i : ℕ) :
    β i = β (i + 1) ∧ xOut (β i) = xOut (β (i + 1)) ∧
      512 ≤ β i ∧ 1 ≤ β i := by
  obtain ⟨h512, h1⟩ := depthB_ge n hn
  have he : β i = β (i + 1) := by rw [hβ i, hβ (i + 1)]
  refine ⟨he, by rw [he], ?_, ?_⟩ <;> rw [hβ i] <;> assumption

/-! ## Part 6: `step:I-05` -- the per-level budget side conditions -/

/-- **`step:I-05`, the two side conditions at every level**
(`13-iteration-assembly.tex:430--455`).

The frozen seed identity is `D_0 = Y_0 = a_seed + 1 >= 4 >= 3` (lines 433--436).
From it, `expi:E-05-gap` gives `D_i = Y_i + i`, hence `Y_i <= D_i`; and since
every summand `H_r + 1` is nonnegative, `D_i >= D_0 >= 3`.  The last conclusion is
the frozen no-truncation check of lines 450--455, computed *before* subtracting,
which is what shows that nothing is hidden in natural subtraction:

```
(D_i + H_{i+1} + 1) - (Y_i + H_{i+1}) = i + 1.
```

General in the overhead sequence, the index and the next overhead value.

Reader counterpart: **none** -- the reader states the closed forms and the gap
(assigned to `iterationClosedBudgets`) but never the two side conditions
`Y_i <= D_i` and `3 <= D_i`, which are autoformalization-only.  Frozen line 449
records that these are "exactly the side conditions of `thm:one-level`". -/
theorem iterationSideConditions (Y0 D0 : ℕ) (H : ℕ → ℕ) (hseed : D0 = Y0)
    (hentry : 3 ≤ D0) (i : ℕ) (Hnext : ℕ) :
    budgetY Y0 H i ≤ budgetD D0 H i ∧ 3 ≤ budgetD D0 H i ∧
      budgetD D0 H i = budgetY Y0 H i + i ∧
      (budgetD D0 H i + Hnext + 1) - (budgetY Y0 H i + Hnext) = i + 1 := by
  obtain ⟨hY, hD, hgap⟩ := iterationClosedBudgets Y0 D0 H hseed i
  exact ⟨by omega, by omega, hgap, by omega⟩

/-! ## Part 7: exact carrier growth, per step

The double-interlace recurrence: one level is the inner scale-alignment interlace
at width `q` followed by the outer bridge interlace at width `Q`, and the frozen
carrier equations record how each of the two widths acts. -/

/-- **`eq:fixed-level-carriers` at one step**
(`12-iteration-specification.tex`, label line 264, display lines 260--265):

```
m_{i+1} = (q_i m_{N,i})^{Q_i},     n_{i+1} = Q_i (n_{N,i})^{q_i}.
```

Frozen line 258 attributes exactly this to "the carrier clause C4 of
`thm:one-level`", and calls the recurrence "exact, rather than asymptotic".  The
proof is that attribution: the banked
`OneLevelAssembly.oneLevelAssembly_carriers` applied once, then read through the
two names above.

Both widths appear by their **exponents**, `q = 2^{w_q}` and
`Q = Qwidth b_out delta_U = 2^{r_Q}`, and they are never conflated.  The two
conclusions are stated on the cardinalities `|Rows(R_i^+)|` and `|Cols(R_i^+)|`,
which is the frozen chaining `m_{i+1} = |Rows(R_i^+)|`,
`n_{i+1} = |Cols(R_i^+)|` of `eq:iterated-canonical-chaining`
(`12-iteration-specification.tex`, label line 229) and exactly the data
`lem:canonical-reindexing-invariance` preserves (GAP-EXPOSED 2).

`hq : 1 <= w_q` is the frozen legality guard `q >= 2` of
`02-mechanical-contract.tex:771--775`; reader `05-iteration.tex:281` states the
same invariant.  It is a lower bound on the width and never an upper one.

Reader counterpart: `eq:paper-exact-carrier-recurrence` (`05-iteration.tex`,
label line 166, boxed display lines 161--167). -/
theorem iterationCarrierStep {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (wq bout : ℕ) (δU : ℝ) (hq : 1 ≤ wq) :
    rowsCard (levelOutput N wq bout δU)
        = carrierRowNext (2 ^ wq) (rowsCard N) (Qwidth bout δU) ∧
      colsCard (levelOutput N wq bout δU)
        = carrierColNext (Qwidth bout δU) (colsCard N) (2 ^ wq) := by
  obtain ⟨-, -, hrow, hcol⟩ := oneLevelAssembly_carriers N wq bout δU hq
  exact ⟨hrow, hcol⟩

/-! ## Part 8: the two fixed-level inductions

`thm:fixed-level-gap-size` (iii) and (iv), and `step:I-06`.  The general `k`-level
form is stated on the *numeric* sequence of complexities: the matrices `R_j` have
level-dependent carrier types and, per `def:canonical-reindexing` line 135, the
frozen chaining is deliberately **not** a heterogeneous equality of functions.
The per-step hypotheses are exactly the frozen clause C2 and C3 updates; their
typed instantiation at a composed pair of levels is Part 9. -/

/-- **The `YES` induction of `thm:fixed-level-gap-size` (iii)**
(`12-iteration-specification.tex:267--277`; `step:I-06`, lines 461--474).

If the seed satisfies `comp R_0 <= Y_0` and every level obeys clause C2's update
`comp R_{i+1} <= comp R_i + H_i`, then `comp R_j <= Y_j` for every `j`.  Frozen
line 277: "No robustness hypothesis or conclusion is used in this implication" --
accordingly no depth, density or robustness quantity occurs anywhere in this
statement.  General in `k`.

Reader counterpart: `thm:paper-finite-iteration`'s `YES` line,
`05-iteration.tex:137`. -/
theorem fixedLevelGap_yes_induction (Y0 : ℕ) (H cc : ℕ → ℕ)
    (hbase : cc 0 ≤ Y0) (hstep : ∀ i, cc (i + 1) ≤ cc i + H i) (j : ℕ) :
    cc j ≤ budgetY Y0 H j := by
  induction j with
  | zero => simpa using hbase
  | succ n ih =>
    have hn := hstep n
    rw [budgetY_succ]
    omega

/-- **The `NO` induction of `thm:fixed-level-gap-size` (iv)**
(`12-iteration-specification.tex:279--297`; `step:I-06`, lines 476--504).

If `comp R_0 = D_0` and every level obeys clause C3's update
`comp R_{i+1} = comp R_i + H_i + 1`, then `comp R_j = D_j` for every `j`, which
is the first display of `eq:fixed-level-no-induction`.

The second display -- the regenerated robustness certificate at the *same*
integer -- is carried by `levelNoReading` and delivered per level by the banked
`OneLevelAssembly.oneLevelAssembly_no`; frozen line 501 states that "the exact
complexity and the ordinary robustness certificate are regenerated together", and
Part 9 exhibits that regeneration across two composed levels.  General in `k`.

Reader counterpart: `thm:paper-finite-iteration`'s `NO` line, **line 138 only**
(`CC(R_j) = D_j`).  Line 140, the `k`-level robustness bound, is deliberately
**not** claimed here; see the module header. -/
theorem fixedLevelGap_no_induction (D0 : ℕ) (H cc : ℕ → ℕ)
    (hbase : cc 0 = D0) (hstep : ∀ i, cc (i + 1) = cc i + H i + 1) (j : ℕ) :
    cc j = budgetD D0 H j := by
  induction j with
  | zero => simpa using hbase
  | succ n ih => rw [budgetD_succ, hstep n, ih]

/-- **The exact `k`-level additive separation** -- `eq:k-level-gap`
(`12-iteration-specification.tex`, label line 305, display lines 301--306).

```
YES : comp R_k <= Y_k,     NO : comp R_k = D_k = Y_k + k.
```

Under the frozen seed identity `D_0 = Y_0` (clause (v), line 299) the two ladders
separate by exactly `k` after `k` levels -- not `O(k)`, and not `k` only in the
limit.  General in the overhead sequence and in `k`.

Reader counterpart: `thm:paper-finite-iteration`'s final sentence,
`05-iteration.tex:143`, "In particular the final additive separation is exactly
`k`." -/
theorem kLevelAdditiveGap (Y0 D0 : ℕ) (H : ℕ → ℕ) (hseed : D0 = Y0) (k : ℕ) :
    budgetD D0 H k = budgetY Y0 H k + k :=
  (iterationClosedBudgets Y0 D0 H hseed k).2.2

/-! ## Part 9: the typed iteration steps

One level, then a genuinely composed pair.  Every promise-side input is a guarded
binder out of an abstract `Prop`, exactly as `thm:one-level` clauses C2 and C3 are
implications out of `YesCert(Public)` and `NoCert(Public)`; nothing below is an
unguarded conjunction of the two branches. -/

/-- **One `YES` step of the ladder** -- `step:I-06`, `13-iteration-assembly.tex`
lines 461--474, at the budget names of `step:I-03`.

The guarded input is the frozen Stage-4 `YES` line
`11-one-level-assembly.tex:793`; the conclusion is clause C2 read at the ladder's
next budget `Y_{i+1} = Y_i + H_i`.  Purely a repackaging of the banked
`OneLevelAssembly.oneLevelAssembly_yes` -- nothing is re-proved. -/
theorem iterationStep_yes {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Y0 : ℕ) (H : ℕ → ℕ) (i a w2 ws wq bout : ℕ) {δU : ℝ}
    (YesCert : Prop)
    (hH : H i = levelOverhead a w2 ws wq (rQ bout δU))
    (hIn : YesCert → D N ≤ budgetY Y0 H i + stage4Overhead a w2 ws) :
    YesCert →
      levelYesReading (levelOutput N wq bout δU) (budgetY Y0 H (i + 1)) := by
  intro hc
  have h := oneLevelAssembly_yes N (budgetY Y0 H i) a w2 ws wq bout
    (δU := δU) YesCert hIn hc
  change D (levelOutput N wq bout δU) ≤ budgetY Y0 H (i + 1)
  rw [budgetY_succ, hH]
  exact h

/-- **One `NO` step of the ladder** -- `step:I-06`, `13-iteration-assembly.tex`
lines 476--504, at the budget names of `step:I-03`.

The four guarded inputs are the ones `step:L-10` hands the bridge
(`exp:E-10-common`), and the entry floor is `step:I-05`'s `3 <= D_i` supplied by
`iterationSideConditions` at the *previous* level; the conclusion is the pair
`levelNoReading` at the ladder's next budget `D_{i+1} = D_i + H_i + 1`, i.e. the
exact complexity and the ordinary robustness certificate regenerated **together
at one integer** (frozen line 501).  Purely a repackaging of the banked
`OneLevelAssembly.oneLevelAssembly_no`. -/
theorem iterationStep_no {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (D0 : ℕ) (H : ℕ → ℕ) (i a w2 ws wq bout : ℕ) {δU θ : ℝ}
    (NoCert : Prop)
    (hH : H i = levelOverhead a w2 ws wq (rQ bout δU))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hb : 1 ≤ bout) (hgates : directEntryGates bout δU θ (3 / 5))
    (hEntry : NoCert → 3 ≤ budgetD D0 H i)
    (hCW : NoCert → D (alignedMatrix N wq)
      = alignedExact (budgetD D0 H i) a w2 ws wq)
    (hNear : NoCert → alignedExact (budgetD D0 H i) a w2 ws wq
      ≤ Dfamily (interlaceFun (alignedMatrix N wq) 1)
          (bracketGE (Fin (2 ^ wq) → Y) (Fin (2 ^ wq) × X) 1 θ (1 - δU)))
    (hInput : NoCert → alignedExact (budgetD D0 H i) a w2 ws wq - 1
      ≤ LambdaGE (alignedMatrix N wq) 1 θ (3 / 5)) :
    NoCert →
      levelNoReading (levelOutput N wq bout δU) (budgetD D0 H (i + 1)) bout := by
  intro hc
  obtain ⟨heq, hrob⟩ :=
    oneLevelAssembly_no N (budgetD D0 H i) a w2 ws wq bout (δU := δU) (θ := θ)
      NoCert hX hY hδ0 hδ1 hθ0 hθ1 hb hgates hEntry hCW hNear hInput hc
  change D (levelOutput N wq bout δU) = budgetD D0 H (i + 1) ∧
    budgetD D0 H (i + 1)
      ≤ LambdaGE (levelOutput N wq bout δU) 1 (xOut bout) ((3 : ℝ) / 5)
  rw [budgetD_succ, hH]
  exact ⟨heq, hrob⟩

/-- **Two genuinely composed `YES` steps** -- `step:I-06` lines 461--474 run
twice, at the frozen constant depth `b_out` of `step:I-04`.

The second level's Stage-4 input is a named hypothesis that **consumes the first
level's conclusion**: `hTransfer` receives `levelYesReading R_1 Y_1` and returns
the frozen line `comp N_1 <= Y_1 + K_1`.  That implication is exactly the Stage-1
to Stage-4 chain the route has not yet formalized (GAP-EXPOSED 1), so it is a
hypothesis and not a claim; what is *derived* across the boundary is the budget
arithmetic `Y_2 = Y_1 + H_1 = Y_0 + H_0 + H_1`.

Both levels carry their **own** inner width `w_q` and their own deletion
tolerance, hence their own outer exponent `r_Q`; only the requested depth `b_out`
is shared, which is `step:I-04`.  No `NO` quantity occurs anywhere in the
statement. -/
theorem iterationTwoSteps_yes {X₀ Y₀ X₁ Y₁ : Type*} [Fintype X₀] [Fintype Y₀]
    [Fintype X₁] [Fintype Y₁]
    (N₀ : X₀ → Y₀ → Bool) (N₁ : X₁ → Y₁ → Bool) (Y0 : ℕ) (H : ℕ → ℕ)
    (a₀ w2₀ ws₀ wq₀ a₁ w2₁ ws₁ wq₁ bout : ℕ) {δ₀ δ₁ : ℝ} (YesCert : Prop)
    (hH0 : H 0 = levelOverhead a₀ w2₀ ws₀ wq₀ (rQ bout δ₀))
    (hH1 : H 1 = levelOverhead a₁ w2₁ ws₁ wq₁ (rQ bout δ₁))
    (hSeed : YesCert → D N₀ ≤ Y0 + stage4Overhead a₀ w2₀ ws₀)
    (hTransfer : YesCert →
      levelYesReading (levelOutput N₀ wq₀ bout δ₀) (budgetY Y0 H 1) →
        D N₁ ≤ budgetY Y0 H 1 + stage4Overhead a₁ w2₁ ws₁) :
    YesCert →
      levelYesReading (levelOutput N₀ wq₀ bout δ₀) (budgetY Y0 H 1) ∧
        levelYesReading (levelOutput N₁ wq₁ bout δ₁) (budgetY Y0 H 2) := by
  intro hc
  have hstep0 :=
    iterationStep_yes N₀ Y0 H 0 a₀ w2₀ ws₀ wq₀ bout (δU := δ₀) YesCert hH0
      hSeed hc
  refine ⟨hstep0, ?_⟩
  exact iterationStep_yes N₁ Y0 H 1 a₁ w2₁ ws₁ wq₁ bout (δU := δ₁) YesCert hH1
    (fun h => hTransfer h hstep0) hc

/-- **Two genuinely composed `NO` steps** -- `step:I-06` lines 476--504 run twice,
at the frozen constant depth `b_out` of `step:I-04`.

The three matrix-level inputs of the second level are named hypotheses that
**consume the first level's conclusion pair**, which is the frozen shape at
lines 482--490: the induction hypothesis at the start of level `i` is the pair
`comp R_{i-1} = D_{i-1}`, `Lambda_3(R_{i-1}, 1, 2^{-B(n)}, 3/5) >= D_{i-1}`, and
the actual record is supplied by `cor:realized-effective-prefix`.  Those transfer
implications are the unformalized Stage-1 to Stage-4 chain (GAP-EXPOSED 1).

What **is** derived across the boundary, and is the point of this theorem, is the
entire numeric ladder: the second level's entry floor `3 <= D_1` is *proved* from
`step:I-05` and the seed floor `3 <= D_0`, never assumed; and the delivered budget
is `D_2 = D_1 + H_1 + 1 = D_0 + H_0 + H_1 + 2`, so the two levels contribute
exactly two extra bits.  Both levels carry their own inner width, deletion
tolerance and outer exponent; only `b_out` is shared.  No `YES` quantity occurs
anywhere in the statement, so the hypothesis context contains no promise
conjunction. -/
theorem iterationTwoSteps_no {X₀ Y₀ X₁ Y₁ : Type*} [Fintype X₀] [Fintype Y₀]
    [Fintype X₁] [Fintype Y₁]
    (N₀ : X₀ → Y₀ → Bool) (N₁ : X₁ → Y₁ → Bool) (D0 : ℕ) (H : ℕ → ℕ)
    (a₀ w2₀ ws₀ wq₀ a₁ w2₁ ws₁ wq₁ bout : ℕ) {δ₀ δ₁ θ₀ θ₁ : ℝ} (NoCert : Prop)
    (hH0 : H 0 = levelOverhead a₀ w2₀ ws₀ wq₀ (rQ bout δ₀))
    (hH1 : H 1 = levelOverhead a₁ w2₁ ws₁ wq₁ (rQ bout δ₁))
    (hX₀ : 1 ≤ Fintype.card X₀) (hY₀ : 1 ≤ Fintype.card Y₀)
    (hX₁ : 1 ≤ Fintype.card X₁) (hY₁ : 1 ≤ Fintype.card Y₁)
    (hδ₀0 : 0 < δ₀) (hδ₀1 : δ₀ < 1) (hθ₀0 : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hδ₁0 : 0 < δ₁) (hδ₁1 : δ₁ < 1) (hθ₁0 : 0 < θ₁) (hθ₁1 : θ₁ ≤ 1)
    (hb : 1 ≤ bout)
    (hgates₀ : directEntryGates bout δ₀ θ₀ (3 / 5))
    (hgates₁ : directEntryGates bout δ₁ θ₁ (3 / 5))
    (hEntry : NoCert → 3 ≤ D0)
    (hCW₀ : NoCert → D (alignedMatrix N₀ wq₀) = alignedExact D0 a₀ w2₀ ws₀ wq₀)
    (hNear₀ : NoCert → alignedExact D0 a₀ w2₀ ws₀ wq₀
      ≤ Dfamily (interlaceFun (alignedMatrix N₀ wq₀) 1)
          (bracketGE (Fin (2 ^ wq₀) → Y₀) (Fin (2 ^ wq₀) × X₀) 1 θ₀ (1 - δ₀)))
    (hInput₀ : NoCert → alignedExact D0 a₀ w2₀ ws₀ wq₀ - 1
      ≤ LambdaGE (alignedMatrix N₀ wq₀) 1 θ₀ (3 / 5))
    (hCW₁ : NoCert →
      levelNoReading (levelOutput N₀ wq₀ bout δ₀) (budgetD D0 H 1) bout →
        D (alignedMatrix N₁ wq₁)
          = alignedExact (budgetD D0 H 1) a₁ w2₁ ws₁ wq₁)
    (hNear₁ : NoCert →
      levelNoReading (levelOutput N₀ wq₀ bout δ₀) (budgetD D0 H 1) bout →
        alignedExact (budgetD D0 H 1) a₁ w2₁ ws₁ wq₁
          ≤ Dfamily (interlaceFun (alignedMatrix N₁ wq₁) 1)
              (bracketGE (Fin (2 ^ wq₁) → Y₁) (Fin (2 ^ wq₁) × X₁) 1 θ₁
                (1 - δ₁)))
    (hInput₁ : NoCert →
      levelNoReading (levelOutput N₀ wq₀ bout δ₀) (budgetD D0 H 1) bout →
        alignedExact (budgetD D0 H 1) a₁ w2₁ ws₁ wq₁ - 1
          ≤ LambdaGE (alignedMatrix N₁ wq₁) 1 θ₁ (3 / 5)) :
    NoCert →
      levelNoReading (levelOutput N₀ wq₀ bout δ₀) (budgetD D0 H 1) bout ∧
        levelNoReading (levelOutput N₁ wq₁ bout δ₁) (budgetD D0 H 2) bout ∧
        3 ≤ budgetD D0 H 1 := by
  intro hc
  have hstep0 :=
    iterationStep_no N₀ D0 H 0 a₀ w2₀ ws₀ wq₀ bout (δU := δ₀) (θ := θ₀) NoCert
      hH0 hX₀ hY₀ hδ₀0 hδ₀1 hθ₀0 hθ₀1 hb hgates₀ hEntry hCW₀ hNear₀ hInput₀ hc
  have hbase := hEntry hc
  have hfloor : 3 ≤ budgetD D0 H 1 := by
    rw [budgetD_succ, budgetD_zero]
    omega
  refine ⟨hstep0, ?_, hfloor⟩
  exact iterationStep_no N₁ D0 H 1 a₁ w2₁ ws₁ wq₁ bout (δU := δ₁) (θ := θ₁)
    NoCert hH1 hX₁ hY₁ hδ₁0 hδ₁1 hθ₁0 hθ₁1 hb hgates₁ (fun _ => hfloor)
    (fun h => hCW₁ h hstep0) (fun h => hNear₁ h hstep0)
    (fun h => hInput₁ h hstep0) hc

/-! ## Part 10: the promise guard is load-bearing across the iteration

Two refutations.  The first is the banked one-level guard re-read at the iterated
budgets; the second is new to the iteration and is the reason the exact gap
matters. -/

/-- **The two certificates are never both available at any level of the ladder.**

Straight through the banked
`OneLevelAssembly.oneLevelAssembly_promises_exclusive` at the iterated budgets:
`step:I-05` fixes `Y_i <= D_i` at every level "including every one-level call
site" (`13-iteration-assembly.tex:431`), and `iterationSideConditions` proves that
side condition for the ladder, so the banked refutation applies verbatim at each
index.  General in the level index and in every parameter. -/
theorem iterationPromises_exclusive {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Y0 D0 : ℕ) (H : ℕ → ℕ) (i a w2 ws wq : ℕ)
    (YesCert NoCert : Prop) (hseed : D0 = Y0) (hentry : 3 ≤ D0)
    (hYesInput : YesCert → D N ≤ budgetY Y0 H i + stage4Overhead a w2 ws)
    (hCW : NoCert → D (alignedMatrix N wq)
      = alignedExact (budgetD D0 H i) a w2 ws wq)
    (hy : YesCert) (hn : NoCert) : False := by
  obtain ⟨hYD, -, -, -⟩ := iterationSideConditions Y0 D0 H hseed hentry i 0
  exact oneLevelAssembly_promises_exclusive N (budgetD D0 H i) (budgetY Y0 H i)
    a w2 ws wq YesCert NoCert hYD hYesInput hCW hy hn

/-- **From level one onwards the two readings on the same matrix are
contradictory.**

`eq:k-level-gap` gives `D_k = Y_k + k`, so for `k >= 1` the frozen `NO` value is
*strictly* above the frozen `YES` budget.  A matrix carrying both readings would
force `D_k <= Y_k` by aux 15, which is false.  This is the iteration-level
statement of why the promise cases may only ever appear under an explicit
hypothesis: an unguarded conjunction of the two branches is a theorem about the
empty parameter set at every positive level.  General in the carriers, the matrix,
the overhead sequence, the depth and `k >= 1`. -/
theorem iteratedReadings_refuted_at_positive_gap {A B : Type*} [Fintype A]
    [Fintype B] (M : A → B → Bool) (Y0 D0 : ℕ) (H : ℕ → ℕ) (k bout : ℕ)
    (hseed : D0 = Y0) (hk : 1 ≤ k)
    (hno : levelNoReading M (budgetD D0 H k) bout)
    (hyes : levelYesReading M (budgetY Y0 H k)) : False := by
  have hgap := kLevelAdditiveGap Y0 D0 H hseed k
  have hle := levelReadings_force_closure hno hyes
  omega

/-! ## Part 11: non-vacuity

LANE-GATE 3 and LANE-GATE 4b/4c.  Each item excludes one degeneracy that a green
build cannot see.  Three of them run the ladder for **two genuine levels** with
different arithmetic at each level. -/

/-- **Witness 1: the coefficient pass is nondegenerate, and the affine form has
genuine slope.**

`clog_2` is identified at two separating values, and the affine form of
`13-iteration-assembly.tex:61--64` is exhibited to depend on `b_0(u)`: at
`c_0 = 0`, `b_0 = 2`, `X = 2`, `L_P = 1` it returns `4`, while the unit-slope
reading returns `2`.  The two literal maxima read off a two-node table return
different values, so the pairing of each constant coefficient with its own slope
is visible rather than accidental. -/
theorem coefficientPass_fires_nondegenerate :
    Nat.clog 2 4 = 2 ∧ Nat.clog 2 12 = 4 ∧
      excAffine 0 2 2 1 = 4 ∧ excAffine 0 1 2 1 = 2 ∧
      cexcZero [(3, 5), (7, 2)] = 7 ∧ bexcZero [(3, 5), (7, 2)] = 5 ∧
      cexcZero [(3, 5), (7, 2)] ≠ bexcZero [(3, 5), (7, 2)] := by
  have h4 : Nat.clog 2 4 = 2 := by
    have := clog_two_eq_succ 4 1 (by norm_num) (by norm_num)
    omega
  have h12 : Nat.clog 2 12 = 4 := by
    have := clog_two_eq_succ 12 3 (by norm_num) (by norm_num)
    omega
  have hc : cexcZero [(3, 5), (7, 2)] = 7 := by decide
  have hb : bexcZero [(3, 5), (7, 2)] = 5 := by decide
  refine ⟨h4, h12, ?_, ?_, hc, hb, by rw [hc, hb]; norm_num⟩
  · unfold excAffine
    norm_num [h4]
  · unfold excAffine
    norm_num [h4]

/-- **Witness 2 (the `step:I-01` pole): the unit-slope search is a different,
weaker search.**

Frozen line 65: "Retaining `B_exc^0` is essential: repeated occurrences of the
formal leaf `X` are not silently assigned coefficient one."  Here is that
sentence as a kernel refutation.  At `c_seed = 0`, `C_exc^0 = 1` the integer
`A = 10` passes the unit-slope test `C_exc^0 + clog_2(A+2) + 4 <= A` (since
`clog_2 12 = 4` and `1 + 4 + 4 = 9 <= 10`) but **fails** the frozen test at
`B_exc^0 = 10` (`1 + 40 + 4 = 45 > 10`).

So a formalization that dropped the slope would return a strictly smaller
`A_wrap`, and every downstream margin -- including `A_wrap >= C_exc + 4` -- would
be certifying an integer the frozen search does not return.  A green build cannot
see this; only the refutation can. -/
theorem unitSlopeSearch_is_not_the_frozen_search :
    AwrapAdmissible 0 1 1 10 ∧ ¬ AwrapAdmissible 0 1 10 10 := by
  have h12 : Nat.clog 2 12 = 4 := by
    have := clog_two_eq_succ 12 3 (by norm_num) (by norm_num)
    omega
  constructor
  · refine ⟨by norm_num, ?_⟩
    show 1 + 1 * Nat.clog 2 (10 + 2) + 4 ≤ 10
    norm_num [h12]
  · rintro ⟨-, hle⟩
    rw [show (10 : ℕ) + 2 = 12 from rfl, h12] at hle
    omega

/-- **Witness 3: the exponent recursion and the cumulative threshold fire.**

`c_0 = 3`, `c_1 = 16 * 4 = 64` -- the frozen `c_k >= c_1 = 16(c_0+1) = 64` of
`13-iteration-assembly.tex:619` -- and `c_2 = 16 * 65 = 1040`.  The threshold is
exercised at a cutoff function that is **not** constant, so the maximum in
`n_val` is genuinely taken: with `n_step(c) = c`, `n_val(2) = 64` rather than the
degenerate `1`, and every earlier index is simultaneously eligible at
`n = 64`. -/
theorem cumulativeThreshold_fires_nondegenerate :
    cexp 0 = 3 ∧ cexp 1 = 64 ∧ cexp 2 = 1040 ∧
      nval (fun c => c) 0 = 1 ∧ nval (fun c => c) 1 = 3 ∧
      nval (fun c => c) 2 = 64 ∧ (∀ r, r < 2 → cexp r ≤ 64) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro r hr
  interval_cases r <;> decide

/-- **Witness 4: the frozen envelope fires, and the depth genuinely moves.**

At `n = 1` the least-integer rule returns `l(1) = 3` (since
`17 > 16 = 2^{2^2}`), so `B(1) = 2^9 = 512`, the exact constant of
`13-iteration-assembly.tex:428`.  At `n = 241` the rule returns `l(241) = 4`
(since `257 > 256`) and `B(241) = 2^16`.  A single source size could not
distinguish `l` from a constant; two can. -/
theorem envelope_fires_nondegenerate :
    ellN 1 = 3 ∧ depthB 1 = 512 ∧ ellN 241 = 4 ∧ depthB 241 = 65536 ∧
      depthB 1 ≠ depthB 241 := by
  have h1 : ellN 1 = 3 := by
    change Nat.find (ellN_exists 1) = 3
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro m hm
    interval_cases m <;> decide
  have h241 : ellN 241 = 4 := by
    change Nat.find (ellN_exists 241) = 4
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro m hm
    interval_cases m <;> decide
  refine ⟨h1, ?_, h241, ?_, ?_⟩
  · unfold depthB envE
    rw [h1]
    norm_num
  · unfold depthB envE
    rw [h241]
    norm_num
  · unfold depthB envE
    rw [h1, h241]
    norm_num

/-- **Witness 5 (the `step:I-04` pole): the depth thread is not automatic.**

`13-iteration-assembly.tex:426`: "No density-monotonicity conversion and no
rounding of the exponent occurs at this interface."  The requested densities at
two different depths are genuinely different reals, so the frozen identity
`beta_i = beta_{i+1}` is a constraint on the schedule and not a triviality of
notation. -/
theorem depthThread_pole : xOut 1 ≠ xOut 2 := by
  unfold xOut
  norm_num

/-- **Witness 6 (the carrier pole): the row and column halves are not the same
equation at swapped widths.**

At `q = 2`, `Q = 3`, `m_N = 3`, `n_N = 5` the frozen recurrence reads
`m_next = (2 * 3)^3 = 216` and `n_next = 3 * 5^2 = 75`.  The separating conjuncts
exclude every neighbouring misreading of `eq:fixed-level-carriers`: swapping the
two widths in the row half gives `81`, swapping them in the column half gives
`250`, and neither half is the other.  A degenerate witness at
`q = Q = m_N = n_N = 1` satisfies both equations and separates nothing. -/
theorem carrierGrowth_orientation_pole :
    carrierRowNext 2 3 3 = 216 ∧ carrierColNext 3 5 2 = 75 ∧
      carrierRowNext 3 3 2 = 81 ∧ carrierColNext 2 5 3 = 250 ∧
      carrierRowNext 2 3 3 ≠ carrierRowNext 3 3 2 ∧
      carrierColNext 3 5 2 ≠ carrierColNext 2 5 3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Witness 7: the exact carrier growth fires at the banked entry parameters.**

At the first banked witness of `EntryGates.directEntryGates_fires` --
`b_out = 1`, `delta_U = 1/60`, hence `r_Q = 13` and `Q = 8192` -- and at the
inner width `w_q = 3`, hence `q = 8`, the frozen recurrence delivers
`m_next = (8 m_N)^{8192}` and `n_next = 8192 n_N^8`.  Both widths are at least
two, so the frozen legality invariant of `02-mechanical-contract.tex:771--775`
holds, and the two widths are different, which is what makes the orientation
observable here rather than only in the abstract pole.

The two carrier equations are stated at the name `Qwidth 1 (1/60)` rather than at
its numeral, because the level output's carrier *type* depends on that width; the
numeral is carried by the first and last conjuncts. -/
theorem iterationCarrierStep_fires {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) :
    Qwidth 1 (1 / 60 : ℝ) = 8192 ∧
      rowsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        = carrierRowNext (2 ^ 3) (rowsCard N) (Qwidth 1 (1 / 60 : ℝ)) ∧
      colsCard (levelOutput N 3 1 (1 / 60 : ℝ))
        = carrierColNext (Qwidth 1 (1 / 60 : ℝ)) (colsCard N) (2 ^ 3) ∧
      Qwidth 1 (1 / 60 : ℝ) ≠ 2 ^ 3 := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  obtain ⟨hrow, hcol⟩ := iterationCarrierStep N 3 1 (1 / 60 : ℝ) (by norm_num)
  refine ⟨hQ, hrow, hcol, ?_⟩
  rw [hQ]
  norm_num

/-- **Witness 8: the budget ladder runs two genuine levels with different
arithmetic.**

The two overheads are the two *banked* one-level values: `H_0 = 27` at the first
entry-gate witness (`delta_U = 1/60`, `w_q = 3`) and `H_1 = 30` at the second
(`delta_U = 1/200`, `w_q = 5`), both delivered by
`OneLevelAssembly.oneLevelAssembly_fires_yes_witness` and
`.oneLevelAssembly_fires_second_witness`.  At the frozen seed
`D_0 = Y_0 = a_seed + 1 = 4` of `13-iteration-assembly.tex:435` the ladder gives

```
Y_1 = 31,  Y_2 = 61,   D_1 = 32,  D_2 = 63 = Y_2 + 2,
```

so the additive separation after two levels is exactly two.  The overheads
differ, so a ladder that silently reused one level's overhead could not produce
these values; and the side conditions of `step:I-05` are exhibited at the first
index. -/
theorem budgetLadder_fires_twoLevels (H : ℕ → ℕ) (h0 : H 0 = 27)
    (h1 : H 1 = 30) :
    budgetY 4 H 1 = 31 ∧ budgetY 4 H 2 = 61 ∧
      budgetD 4 H 1 = 32 ∧ budgetD 4 H 2 = 63 ∧
      budgetD 4 H 2 = budgetY 4 H 2 + 2 ∧
      budgetY 4 H 1 ≤ budgetD 4 H 1 ∧ 3 ≤ budgetD 4 H 1 ∧
      (27 : ℕ) ≠ 30 := by
  simp only [budgetY_succ, budgetY_zero, budgetD_succ, budgetD_zero, h0, h1]
  norm_num

/-- **Witness 9: the `YES` ladder fires for two genuine levels.**

The composed pair at the two banked parameter sets -- level one at
`delta_U = 1/60`, `w_q = 3`, `H_0 = 27`; level two at `delta_U = 1/200`,
`w_q = 5`, `H_1 = 30` -- and at the frozen seed budget `Y_0 = 4`.  The delivered
budgets are `Y_1 = 31` and `Y_2 = 61`, both exactly the frozen values, and the
promise certificate is genuinely inhabited (`YesCert := True`), so the two
conclusions are real bounds rather than vacuous implications.  The Stage-4
transfer into level two is the named hypothesis of GAP-EXPOSED 1; it consumes the
level-one conclusion, so the two steps are sequential rather than parallel. -/
theorem iterationTwoSteps_yes_fires {X₀ Y₀ X₁ Y₁ : Type*} [Fintype X₀]
    [Fintype Y₀] [Fintype X₁] [Fintype Y₁]
    (N₀ : X₀ → Y₀ → Bool) (N₁ : X₁ → Y₁ → Bool) (H : ℕ → ℕ)
    (h0 : H 0 = 27) (h1 : H 1 = 30)
    (hSeed : D N₀ ≤ 4 + stage4Overhead 4 6 1)
    (hTransfer : D (levelOutput N₀ 3 1 (1 / 60 : ℝ)) ≤ 31 →
      D N₁ ≤ 31 + stage4Overhead 4 6 1) :
    D (levelOutput N₀ 3 1 (1 / 60 : ℝ)) ≤ 31 ∧
      D (levelOutput N₁ 5 1 (1 / 200 : ℝ)) ≤ 61 := by
  obtain ⟨-, -, hrQ0, -, -, -, -⟩ := directEntryGates_fires
  obtain ⟨-, hrQ1, -, -, -, -, -⟩ := directOutput_fires_second_witness
  have hOv0 : levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ0]
  have hOv1 : levelOverhead 4 6 1 5 (rQ 1 (1 / 200 : ℝ)) = 30 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ1]
  have hH0 : H 0 = levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) := by omega
  have hH1 : H 1 = levelOverhead 4 6 1 5 (rQ 1 (1 / 200 : ℝ)) := by omega
  have hY1 : budgetY 4 H 1 = 31 := by
    simp only [budgetY_succ, budgetY_zero, h0]
  have hY2 : budgetY 4 H 2 = 61 := by
    simp only [budgetY_succ, budgetY_zero, h0, h1]
  obtain ⟨hs0, hs1⟩ :=
    iterationTwoSteps_yes N₀ N₁ 4 H 4 6 1 3 4 6 1 5 1 (δ₀ := 1 / 60)
      (δ₁ := 1 / 200) True hH0 hH1 (fun _ => hSeed)
      (fun _ hprev => by
        rw [hY1] at hprev ⊢
        exact hTransfer hprev) trivial
  rw [hY1] at hs0
  rw [hY2] at hs1
  exact ⟨hs0, hs1⟩

/-- **Witness 10: the `NO` ladder fires for two genuine levels, and level two's
side condition is derived.**

The mirror instantiation at the same two banked parameter sets and the frozen
seed budget `D_0 = 4`.  The delivered values are `D_1 = 32` and `D_2 = 63`, with
the robustness bound sitting at the **same** integer at both levels, which is
clause C3's "same integer" requirement carried through the iteration.  The entry
floor `3 <= D_1` needed by level two is **proved** from `step:I-05`, not assumed:
it appears as a conclusion, not a hypothesis.  Combined with witness 9, the pair
`(Y_2, D_2) = (61, 63)` is the exact additive separation `k = 2`.

The matrix-level `NO` inputs stay universally quantified binders, since the
bridge's input matrix has no exhibited Lean inhabitant until Stages 1--4 land.  No
`YES` quantity occurs in the statement, so the hypothesis context carries no
promise conjunction and the closing arithmetic is genuine rather than an
explosion. -/
theorem iterationTwoSteps_no_fires {X₀ Y₀ X₁ Y₁ : Type*} [Fintype X₀]
    [Fintype Y₀] [Fintype X₁] [Fintype Y₁]
    (N₀ : X₀ → Y₀ → Bool) (N₁ : X₁ → Y₁ → Bool) (H : ℕ → ℕ)
    (h0 : H 0 = 27) (h1 : H 1 = 30)
    (hX₀ : 1 ≤ Fintype.card X₀) (hY₀ : 1 ≤ Fintype.card Y₀)
    (hX₁ : 1 ≤ Fintype.card X₁) (hY₁ : 1 ≤ Fintype.card Y₁)
    (hCW₀ : D (alignedMatrix N₀ 3) = alignedExact 4 4 6 1 3)
    (hNear₀ : alignedExact 4 4 6 1 3
      ≤ Dfamily (interlaceFun (alignedMatrix N₀ 3) 1)
          (bracketGE (Fin (2 ^ 3) → Y₀) (Fin (2 ^ 3) × X₀) 1 (1 / 192000)
            (1 - 1 / 60)))
    (hInput₀ : alignedExact 4 4 6 1 3 - 1
      ≤ LambdaGE (alignedMatrix N₀ 3) 1 (1 / 192000) (3 / 5))
    (hCW₁ : levelNoReading (levelOutput N₀ 3 1 (1 / 60 : ℝ)) 32 1 →
      D (alignedMatrix N₁ 5) = alignedExact 32 4 6 1 5)
    (hNear₁ : levelNoReading (levelOutput N₀ 3 1 (1 / 60 : ℝ)) 32 1 →
      alignedExact 32 4 6 1 5
        ≤ Dfamily (interlaceFun (alignedMatrix N₁ 5) 1)
            (bracketGE (Fin (2 ^ 5) → Y₁) (Fin (2 ^ 5) × X₁) 1 (1 / 640000)
              (1 - 1 / 200)))
    (hInput₁ : levelNoReading (levelOutput N₀ 3 1 (1 / 60 : ℝ)) 32 1 →
      alignedExact 32 4 6 1 5 - 1
        ≤ LambdaGE (alignedMatrix N₁ 5) 1 (1 / 640000) (3 / 5)) :
    D (levelOutput N₀ 3 1 (1 / 60 : ℝ)) = 32 ∧
      (32 : ℕ) ≤ LambdaGE (levelOutput N₀ 3 1 (1 / 60 : ℝ)) 1 (xOut 1)
        ((3 : ℝ) / 5) ∧
      D (levelOutput N₁ 5 1 (1 / 200 : ℝ)) = 63 ∧
      (63 : ℕ) ≤ LambdaGE (levelOutput N₁ 5 1 (1 / 200 : ℝ)) 1 (xOut 1)
        ((3 : ℝ) / 5) ∧
      3 ≤ budgetD 4 H 1 := by
  obtain ⟨hgates₀, -, hrQ0, -, -, -, -⟩ := directEntryGates_fires
  obtain ⟨-, hrQ1, -, hgates₁, -, -, -⟩ := directOutput_fires_second_witness
  have hOv0 : levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) = 27 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ0]
  have hOv1 : levelOverhead 4 6 1 5 (rQ 1 (1 / 200 : ℝ)) = 30 := by
    unfold levelOverhead stage4Overhead
    rw [hrQ1]
  have hH0 : H 0 = levelOverhead 4 6 1 3 (rQ 1 (1 / 60 : ℝ)) := by omega
  have hH1 : H 1 = levelOverhead 4 6 1 5 (rQ 1 (1 / 200 : ℝ)) := by omega
  have hD1 : budgetD 4 H 1 = 32 := by
    simp only [budgetD_succ, budgetD_zero, h0]
  have hD2 : budgetD 4 H 2 = 63 := by
    simp only [budgetD_succ, budgetD_zero, h0, h1]
  obtain ⟨hs0, hs1, hfloor⟩ :=
    iterationTwoSteps_no N₀ N₁ 4 H 4 6 1 3 4 6 1 5 1 (δ₀ := 1 / 60)
      (δ₁ := 1 / 200) (θ₀ := 1 / 192000) (θ₁ := 1 / 640000) True hH0 hH1
      hX₀ hY₀ hX₁ hY₁ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (le_refl 1)
      hgates₀ hgates₁ (fun _ => by norm_num) (fun _ => hCW₀) (fun _ => hNear₀)
      (fun _ => hInput₀)
      (fun _ hprev => by rw [hD1] at hprev ⊢; exact hCW₁ hprev)
      (fun _ hprev => by rw [hD1] at hprev ⊢; exact hNear₁ hprev)
      (fun _ hprev => by rw [hD1] at hprev ⊢; exact hInput₁ hprev) trivial
  rw [hD1] at hs0
  rw [hD2] at hs1
  obtain ⟨he0, hr0⟩ := hs0
  obtain ⟨he1, hr1⟩ := hs1
  exact ⟨he0, hr0, he1, hr1, hfloor⟩

/-- **Witness 11: the exact two-level gap refutes the joint reading.**

At the same seed and the same two banked overheads, `Y_2 = 61 < 63 = D_2`, so a
matrix carrying both readings after two levels is contradictory.  This is
`iteratedReadings_refuted_at_positive_gap` made numeric, and it is why the two
promise branches of the ladder appear only under explicit hypotheses. -/
theorem iteratedReadings_refuted_at_twoLevels {A B : Type*} [Fintype A]
    [Fintype B] (M : A → B → Bool) (H : ℕ → ℕ) (h0 : H 0 = 27) (h1 : H 1 = 30)
    (hno : levelNoReading M 63 1) (hyes : levelYesReading M 61) : False := by
  have hD2 : budgetD 4 H 2 = 63 := by
    simp only [budgetD_succ, budgetD_zero, h0, h1]
  have hY2 : budgetY 4 H 2 = 61 := by
    simp only [budgetY_succ, budgetY_zero, h0, h1]
  refine iteratedReadings_refuted_at_positive_gap M 4 4 H 2 1 rfl (by norm_num)
    ?_ ?_
  · rw [hD2]; exact hno
  · rw [hY2]; exact hyes

/-- **Witness 12: the `k`-level inductions fire at a nonconstant overhead
sequence.**

The two general inductions instantiated at the two banked overheads and at
complexity sequences that follow the frozen per-level updates exactly.  Because
`H` is not constant, an induction that silently assumed a level-independent
overhead could not deliver `cc 2 = 63`; and the `YES` sequence lands at or below
`61`, so the exact separation `k = 2` is visible on the two sequences themselves
rather than only on the budgets. -/
theorem fixedLevelInductions_fire (H ccY ccN : ℕ → ℕ) (h0 : H 0 = 27)
    (h1 : H 1 = 30) (hY0 : ccY 0 ≤ 4) (hN0 : ccN 0 = 4)
    (hYstep : ∀ i, ccY (i + 1) ≤ ccY i + H i)
    (hNstep : ∀ i, ccN (i + 1) = ccN i + H i + 1) :
    ccY 2 ≤ 61 ∧ ccN 2 = 63 ∧ ccY 2 < ccN 2 := by
  have hy := fixedLevelGap_yes_induction 4 H ccY hY0 hYstep 2
  have hn := fixedLevelGap_no_induction 4 H ccN hN0 hNstep 2
  have hY2 : budgetY 4 H 2 = 61 := by
    simp only [budgetY_succ, budgetY_zero, h0, h1]
  have hD2 : budgetD 4 H 2 = 63 := by
    simp only [budgetD_succ, budgetD_zero, h0, h1]
  rw [hY2] at hy
  rw [hD2] at hn
  exact ⟨hy, hn, by omega⟩

end EthInapproximability.ParameterizedNP.IterationAssembly
