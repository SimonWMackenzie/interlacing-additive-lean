import EthInapproximability.ParameterizedNP.SizePropagation

/-!
# Parameterized NP route: the padding-threshold search and the slow clock

`step:I-08`, `step:I-09`, `step:I-10`, `sec:slow-clock`, `sec:common-padding`.

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`CLOCK-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 134),
"Total computable nondecreasing unbounded slow diagonal tied to the same
machine/compiler, with final-only padding and subexponential table size",
recorded there as human **proved** / Lean **pending**.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Relaunch round `cc-t1t-r1`

The first `cc-t1t` round produced **no module at all**: the statement gate
returned `BLOCK` on an absent file
(`handoffs/cc-formalize/judge-cc-t1t-padding-and-clock.md`, "the artifact under
judgement does not exist"), and the worktree was byte-identical to the pinned
baseline `48d13c8`.  There is therefore **no carried-forward text** and no
byte-identity inventory to report: every declaration below is new in this round,
and every one of the judge's eleven re-gate criteria is addressed by a named
declaration rather than by a note.

## What this module lands

* **`step:I-08`, the padding-threshold search**
  (`13-iteration-assembly.tex`, label line 581, body lines 581--646).
  * `eq:Tk-search` (`12-iteration-specification.tex`, label line 436, display
    lines 429--437) as the **three-inequality conjunction** `TkSearch`, under
    `Nat.find`; never a weakened or unit-slope variant.  Termination is the
    *proved* `tkSearch_exists`, not an assertion.
  * `expi:E-08-ceiling` (label line 587, display lines 585--588),
    `k <= 2^{lambda_k} < 2k` and `2^{lambda_k + 1} >= 2k`, as
    `lambdaK_sandwich`, guarded by `k >= 1`, with the `k = 1` half
    (`lambda_1 = 0`, `1 < 2`) discharged separately inside the proof exactly as
    frozen line 590 requires.
  * `expi:E-08-persistent` (label line 612, display lines 607--613) as the
    **discrete induction** `tkSearch_step` / `tkSearch_persistent`.  The frozen
    argument at lines 594--604 is a real logarithmic derivative; the transposition
    is recorded in reading note N1 below.  It is a theorem with a proof: not an
    axiom, not an opaque certificate, and not a field of any structure.
  * `expi:E-08-margin` (label line 626) and the closing chain of lines
    629--646, as `paddingThresholdSearch`.  Its conclusion is the frozen
    `E_{c_k}(n) < n/(2k)` in **multiplicative** form
    `2 * k * envE (cexp k) n < n`; `natDivision_is_not_the_frozen_conclusion`
    refutes the truncated-division spelling in the kernel.
* **`step:I-09`, the numerically certified slow clock**
  (label line 648, body lines 648--728), as a **gate-parameterized** clock:
  * the three displayed clock gates of lines 672--676 plus `V_0 = 1` of line 653
    are four explicit binders on an arbitrary `V : ℕ → ℕ`.  Nothing models the
    canonical environment `M_*`, the machines `A_cert` / `A_raw`, the running
    time `tau_k`, or the polynomial-time simulation of lines 712--719: those are
    named in GAP-EXPOSED 2 and 3;
  * `eq:L-clock` (`12-iteration-specification.tex`, label line 486) as
    `slowIndex V n = Nat.findGreatest (fun k => V k <= n) n`, the frozen
    `max({0} ∪ {k : V_k <= n})`, whose search bound is licensed by the frozen
    `V_k >= k + 1` of line 678 (`slowClock_ge_succ`);
  * the monotonicity clause of lines 708--710 and the unboundedness clause of
    line 704 (kept in the frozen finite form "for every fixed `K`, all
    `n >= V_K` satisfy `K <= L(n)`"), landed together as the two conjuncts of
    `slowDiagonal_monotone_unbounded`;
    `slowIndex_safePrefix` (`expi:E-09-pairs`, label line 695,
    with the `n_val` monotonicity of lines 687--691), and the capstone
    `slowClock_sublinear` (lines 721--724).
* **`step:I-10`, the seed and prefix-maximum bounds** (label line 730, body lines
  733--807) together with `sec:common-padding`
  (`12-iteration-specification.tex`, label line 565): `aSeed`, `qSeed`, `zSeed`,
  the exact ceiling identity of lines 768--778, the strict chain
  `z_seed(n) < 130 E_2(n) < E_3(n)` of lines 761--785, the seed budget row of
  lines 786--790, and `eq:uniform-size-majorant` (label line 597, display lines
  589--598) as `zhat` and `gMaj`, the latter folding **from `m = 1`**.
  `eq:common-size` (label line 628, display lines 621--629) is `eCommon`,
  `sCommon`, `tCommon`.

## Reader counterparts

Two reader files carry this row's counterparts, and **both were opened
first-hand this tranche** and every cited item read to confirm it states the same
fact: `.../reader-facing/sections/05-iteration.tex` for the clock and
`.../reader-facing/sections/06-eth.tex` for the padding half.  Reader items are
partitioned so that **no reader item is assigned to two declarations**, and
`READER_CROSSWALK.md` row 12 already reserves exactly these three clock labels
for `CLOCK-001` ("the slow clock and final-only padding
(`lem:paper-slow-diagonal`, `eq:paper-Vk`, `eq:paper-slow-clock`) stay with
`CLOCK-001` and are **not** claimed" by `ITER-001`).  No earlier ledger row cites
`06-eth.tex` at all.

From `05-iteration.tex`:

* `eq:paper-Tk-search` (label line 306, display lines 300--307) -- to
  `TkSearch`;
* `eq:paper-Vk` (label line 322, display lines 320--323),
  `V_k = max{A_k(V_{k-1}), tau_k}` -- to `SlowClockGateSet` (the four-gate
  binder list is the Lean reading of that recursion's three consequences plus
  `V_0 = 1`);
* `eq:paper-slow-clock` (label line 327, display lines 325--328),
  `L(n) = max({0} ∪ {k : V_k <= n})` -- to `slowIndex`;
* `lem:paper-slow-diagonal` (label line 331) has three separable clauses and is
  **split one clause per declaration**, none claimed twice -- the same
  clause-by-clause split this route already uses for `eq:bridge-output` and
  `eq:paper-budget-update`: lines 332--333, "`L` is total, computable,
  nondecreasing, and unbounded", to `slowDiagonal_monotone_unbounded` (which
  carries the *nondecreasing* and *unbounded* clauses only; totality is automatic
  for a Lean function and computability is GAP-EXPOSED 3); lines 333--334, "All
  of the first `L(n)` levels are valid", to `slowIndex_safePrefix`; and the
  display at line 336, `E_{c_{L(n)}}(n) = o(n)`, to `slowClock_sublinear`.

From `06-eth.tex`, subsection "A common truth-table length":

* line 281 with line 284, "Let `a_seed(n)` be least such that ... `>= 64(B(n)+1)`"
  -- to `aSeed`;
* line 283, `q_seed(n) = 2^{a_seed(n)} - 2` -- to `qSeed`;
* line 288, `z_seed(n) = q_seed(n) + a_seed(n)` -- to `zSeed`;
* the two-branch display at lines 298--302 -- to `zhat`;
* line 304, `g(n) = max_{1 <= m <= n} zhat(m)` -- to `gMaj`;
* `eq:paper-common-table-size` (label line 320) is split by line: line 317,
  `e(n) = g(n) + ceil(log(n+2))`, to `eCommon`; line 318, `S_n = 2^{e(n)}`, to
  `sCommon`; the first equality of line 319, `T_n = S_n^2`, to `tCommon`; and its
  second equality, `T_n = 2^{2 e(n)}`, to `commonSizeParameters`.

**Four reader loci are named as navigation only and claimed by nothing.**
(i) The persistence sentence at `05-iteration.tex:308--310` and (ii) the
displayed `E_{c_k}(n) < n/(2k)` at `05-iteration.tex:349--351` both sit **inside
proof prose** (the first is the paragraph after `eq:paper-Tk-search`, the second
is inside the proof of `lem:paper-slow-diagonal`), so per the reader-counterpart
rule they are not cited as statement counterparts of `tkSearch_persistent` or
`paddingThresholdSearch`; those two take their statements from the
autoformalization anchors `expi:E-08-persistent` and `expi:E-08-margin`.
(iii) `06-eth.tex:291--292`, "Minimality gives `z_seed(n) = O(B(n))`", is an
asymptotic restatement; `seedSizeChain` lands the frozen *finite* chain of
`13-iteration-assembly.tex:761--766` instead and claims no big-`O`.
(iv) `eq:paper-g-little-o` (`06-eth.tex` label line 312, display line 311,
`g(n) = o(n)`) is **not claimed**: its limit argument is GAP-EXPOSED 4.
`06-eth.tex:322` ("Both carrier sizes of every branch output are at most
`2^{g(n)}`") is likewise unclaimed, being a statement about matrices
(GAP-EXPOSED 5).

**No reader counterpart exists for `T_k` itself, for `lambda_k` alone, or for the
seed-exponent bounds.**  `lambdaK`, `Tk`, `seedGrowth`, `aSeed_bounds`,
`aSeed_min`, `qSeed_le`, `qSeed_sandwich`, `envelope_gap`, `seedCeiling` and
`seedBudgetRow` claim **no** reader item: the reader states the search
`eq:paper-Tk-search` but never names `T_k` or `lambda_k` as objects, and it gives
the seed constants without the `a >= 4`, `a <= b`, ceiling-identity or
`130 E_2(n) < E_3(n)` derivations, which appear only in
`13-iteration-assembly.tex:741--790`.  They are reported as
autoformalization-only content.

Crosswalk rows: `READER_CROSSWALK.md` row 12 ("Slow iteration, padding, and ETH
interface") and the alignment row "Slow diagonal and padding".

## Dependencies, imports, external adapters

* Imports `SizePropagation.lean` only, hence transitively `IterationAssembly`,
  `FiniteSlots`, `OneLevelAssembly`, `OneLevelCompletion`,
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
  * `IterationAssembly.cexp`, `.cexp_zero`, `.cexp_succ`,
    `.cexp_ge_three_and_lt`, `.nval`, `.nval_closed`, `.nval_ge_of_lt`,
    `.ellN`, `.ellN_exists`, `.ellN_spec`, `.envE`, `.depthB`, `.depthB_ge`,
    `.sq_le_two_pow`;
  * `SizePropagation.two_le_ellN`, `.envE_mono_exp`, `.cexp_mono`.
  No second definition of `ellN`, `envE`, `cexp` or `nval` is introduced; every
  occurrence below is the banked one.
* **`K4.slowClock_*` is NOT ported.**  `docs/REUSE_LEDGER.md:187` lists that
  arithmetic battery (with its two sublinearity lemmas) as a *gated-port lead*
  requiring the six-step salvage gate and its own tranche.  That gate was **not**
  run this round, so per the same ledger entry every arithmetic fact below is
  re-derived fresh in-module from the frozen anchors.  Nothing here is copied,
  adapted, or transcribed from `C:/lean/npc-cc`, which traced the older
  fixed-width manuscript and is not a trace or style source.
* External theorem adapters: **none new**.
* Proof status: **new (elementary)** throughout -- `Nat` induction,
  `Nat.find` / `Nat.findGreatest` bookkeeping, `Nat.clog` comparisons, and
  applications of the banked route facades.
* Axiom surface (Appendix D; `#print axioms` in `tools/AxiomAudit.lean`): at most
  `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings (k = 2) and the ranking

The genuinely open choice is **how the ceiling exponent `lambda_k` of
`expi:E-08-ceiling` is encoded**, because it is the one place where the frozen
chain `n > 2^{x^{c_k}} 2^{lambda_k + 1} >= 2k E_{c_k}(n)` converts a logarithm
back into a multiplicative factor of `k`.

**Candidate A (landed) -- the ceiling logarithm, `lambda_k = Nat.clog 2 k`.**
This is `\ceil{\log_2 k}` of `12-iteration-specification.tex:427` and
`13-iteration-assembly.tex:584` read literally.  It delivers the whole frozen
sandwich `k <= 2^{lambda_k} < 2k <= 2^{lambda_k + 1}` (`lambdaK_sandwich`), and
the first of those three inequalities is exactly what the final division by `2k`
consumes.

**Candidate B (refuted) -- the floor logarithm, `lambda_k = Nat.log 2 k`.**  This
is the spelling the displays *look* like once the ceiling bars are dropped, and
it typechecks everywhere.  It is refuted in the kernel by
`floorLogarithm_breaks_the_ceiling_sandwich`: at `k = 3`, `Nat.log 2 3 = 1`, so
`2^{lambda_3} = 2 < 3 = k` -- the **first** inequality of `expi:E-08-ceiling`
fails outright -- and consequently `2^{lambda_3 + 1} = 4 < 6 = 2k`, so the closing
step of `step:I-08` (frozen lines 637--641,
`2^{x^{c_k}} 2^{lambda_k + 1} >= 2k 2^{x^{c_k}}`) is unavailable.  Candidate B
cannot state, let alone prove, aux 6 below.

Aux battery: A = 24/24 below (twenty-one numbered items, plus `mul_pow_pred_le`
at 4b and the two search-property lemmas at 15b).  B **fails** aux 6
(`lambdaK_sandwich`) outright,
which is the disqualifying unprovable lemma, and every later aux lemma that
consumes it (aux 12, aux 15) is then unstatable.  Faithfulness: A is the frozen
ceiling, B is not.  Length: identical.  **A is landed; B survives only as its own
refutation.**

## GAP-EXPOSED

1. **No route completion is claimed.**  Every statement below is about a
   *supplied* clock, a *supplied* cutoff function `nstep`, or the pure integer
   ladders `cexp` / `ellN` / `envE`.  Stages 1--4 (`STAGE1-001` .. `WRAP-001`),
   `thm:effective-materialization` (`MATERIALIZE-001`) and
   `cor:realized-effective-prefix` are **not** formalized, and nothing below
   asserts them.  In particular `slowIndex_safePrefix` is a statement about
   numerical eligibility only: frozen lines 697--702 say the clock "does not
   construct a record on any pair", and no eligibility or realization claim is
   made for `i >= L(n)`.
2. **`thm:eff-ledger` is not formalized.**  `n_step`, `Cert_c`, `NumChecked`,
   `Successor_16` and the certificate compiler are `PARAM-001` work.  Here
   `n_step` enters as an **arbitrary** function argument of the banked `nval`,
   exactly as `IterationAssembly` already carries it, and the clock's three
   numeric gates enter as **binders**, never as an axiom or an opaque
   certificate.
3. **No computability claim is made.**  The frozen lemma also asserts that `L` is
   computable in polynomial time by simulating `A_raw` for `n` steps
   (`13-iteration-assembly.tex:712--719`); that argument needs the machine model
   `M_*` and is out of scope for this module.  `slowIndex` happens to be a
   computable Lean function of `V`, but no complexity statement about it is
   made anywhere below, and `slowDiagonal_monotone_unbounded` deliberately
   carries only the *nondecreasing* and *unbounded* clauses of
   `lem:paper-slow-diagonal`.
4. **Every `o(n)` claim is in the frozen finite-inequality form.**  Nothing below
   mentions `Filter.Tendsto` or an asymptotic order relation.  The frozen
   quantifier order is the point of lines 725--728 ("with the quantifier order
   justified by the single clock rather than by substituting an unbounded level
   into a separate fixed-level eventual statement"), so `slowClock_sublinear`
   and `zhat_sublinear` are single-`n` inequalities at the single clock index
   `L(n)`, and the prefix-maximum limit argument of lines 796--807 (the
   `epsilon`/`N` estimate) is **not** landed at all: `gMaj_spec` carries only
   the two defining properties of the finite maximum `max_{1 <= m <= n}`.
5. **`step:I-11` is out of scope.**  The representative maps `pi_X`, `pi_Y`, the
   duplication argument, and the preservation of communication complexity under
   padding (`13-iteration-assembly.tex:809--` and
   `12-iteration-specification.tex:630--636`) are not formalized.  `eCommon`,
   `sCommon` and `tCommon` are the frozen *numbers* of `eq:common-size` and
   carry no statement about any matrix.
6. **The source-coordinate width is absent by construction.**  Frozen lines
   577--579 keep the numerical width `24 s_i |E(G)|` out of the logarithmic
   recurrence, only `log_2 q_{2,i}` entering.  No declaration below has a width
   argument at all, and nothing is imported from `SizePropagation`'s width rows;
   the clock inequalities depend on `(k, n)` only through `envE (cexp k) n`.

## Two recorded reading notes

* **N1 (the persistence transposition).**  Frozen lines 594--604 argue by the
  logarithmic derivative of a real function: `log 2 - (c_k - 1)/(t + 2) > 0`
  because `t + 2 >= 2(c_k - 1)` and `log 2 > 1/2`.  The Lean transposition is a
  **discrete induction on integers `t >= T_k`** landing the same frozen endpoint
  inequality `expi:E-08-persistent`.  The frozen conclusion
  `2^t - (t+2)^{c_k} >= lambda_k + 2` is carried **additively**,
  `(t+2)^{c_k} + lambda_k + 2 <= 2^t`, because `Nat` subtraction truncates; the
  two are the same statement over the integers, and the additive form is the one
  every consumer below uses.  The discrete step is *not* the naive left-endpoint
  difference bound (which is false for a unit step): `tkSearch_step` uses the
  right-endpoint bound `(t+3)^c <= (t+2)^c + c (t+3)^{c-1}` of aux 3, and
  discharges the resulting `(t+3)^{c-1} <= 2 (t+2)^{c-1}` from the **third**
  frozen search inequality through aux 2.  This is why the whole three-inequality
  conjunction, and not just its first line, is the induction invariant:
  `tkSearch_step` propagates `TkSearch` itself.
* **N2 (junk conventions, and where they are not consumed).**  The frozen text
  defines `lambda_k` and `T_k` for `k >= 1` only (`12-iteration-specification.tex:427`).
  The Lean `lambdaK` and `Tk` are total: `lambdaK 0 = Nat.clog 2 0 = 0` and
  `Tk 0 = Nat.find (tkSearch_exists (cexp 0) 0)` are well defined junk.  Neither
  is consumed: `lambdaK_sandwich`, `tk_ge`, `paddingThresholdSearch` and the two
  clock gates `nval_gate` / `threshold_gate` are all guarded by `1 <= k`, and
  `slowIndex` is allowed to be `0` with **no** claim on that branch beyond the
  seed bound `zhat_zero_branch`.  `slowIndex_zero_is_attained` records that the
  zero branch is genuinely reachable, so the guard is live rather than
  decorative -- and it records this **twice**, because `zhat_zero_branch` is
  guarded by `1 <= n` as well, so the obvious `n = 0` witness does not inhabit
  its hypothesis bundle.  The second conjunct supplies `n = 1`, where the frozen
  seed `V_0 = 1` is feasible but `V_1 >= 2` is not.
-/

namespace EthInapproximability.ParameterizedNP.PaddingAndClock

open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.SizePropagation

/-! ## Part 0: public data

Two search predicates, their `Nat.find` selections, the clock index, and the
common-size parameters.  Everything here is a transparent function of public
integers: there is no complexity, robustness, promise or envelope field anywhere,
and no definition takes a certificate (mechanical rules M1, M2, M4). -/

/-- **`lambda_k = ceil(log_2 k)`** -- `12-iteration-specification.tex:427` and
`13-iteration-assembly.tex:584`.

Reader counterpart: **none**.  The reader writes the same `\ceil{\log k}` inside
`eq:paper-Tk-search` (`05-iteration.tex:298`), but that display is claimed by
`TkSearch`, so it is named here as navigation only.  The **ceiling** is
load-bearing: it is what makes `k <= 2^{lambda_k}` true, hence what lets the
closing division by `2k` in `step:I-08` go through.  Candidate B --
`Nat.log 2 k` -- is refuted by `floorLogarithm_breaks_the_ceiling_sandwich`.

Junk convention (reading note N2): the frozen text defines `lambda_k` for
`k >= 1` only, and `lambdaK 0 = 0` is never consumed. -/
def lambdaK (k : ℕ) : ℕ := Nat.clog 2 k

/-- **`eq:Tk-search`** -- `12-iteration-specification.tex`, label line 436,
display lines 429--437:

```
2^T >= (T+2)^{c_k} + lambda_k + 2,
2^{T-1} >= c_k (T+2)^{c_k - 1},
T + 2 >= 2(c_k - 1).
```

All **three** rows, in the frozen order, as one decidable predicate on `T`.  The
frozen sentence at lines 439--441 records what the last two rows are for: they
"make `2^T - (T+2)^{c_k}` nondecreasing for all real `T >= T_k`; the first gives
the desired starting margin".  Dropping either of them is not a simplification:
`tkSearch_step` propagates the **conjunction**, and its proof consumes the second
row (through `hkey`) and the third row (through aux 2) separately.

The truncated subtractions `T - 1` and `c - 1` are the literal frozen exponents;
every consumer below works in the regime `3 <= c` and `2 <= T`, where `Nat`
subtraction agrees with integer subtraction.  `tkSearch_second_row_unfolded`
records that agreement.

Reader counterpart: `eq:paper-Tk-search` (`05-iteration.tex`, label line 306,
display lines 300--307), opened first-hand and confirmed to print the same three
rows in the same order. -/
def TkSearch (c lamv T : ℕ) : Prop :=
  (T + 2) ^ c + lamv + 2 ≤ 2 ^ T ∧
    c * (T + 2) ^ (c - 1) ≤ 2 ^ (T - 1) ∧
    2 * (c - 1) ≤ T + 2

instance decidableTkSearch (c lamv T : ℕ) : Decidable (TkSearch c lamv T) := by
  unfold TkSearch; infer_instance

/-! ### Part 1: the aux-lemma battery

Twenty-four general properties -- twenty-one numbered, plus `mul_pow_pred_le` at
4b and the two search-property lemmas at 15b -- spread over Parts 1, 1b and 4.
None is about a pinned instance: each quantifies over arbitrary exponents,
ceiling parameters, source sizes, clocks or cutoff functions. -/

/-- **Aux 1 (the ratio induction behind the unit-step bound).**

The frozen persistence argument compares `(t+3)^d` with `(t+2)^d`; over the
integers that comparison is governed by the exact inequality below, whose
induction step is precisely the frozen side condition `t + 2 >= 2 d`.  General in
both arguments; stated in the cleared multiplicative form so that no division and
no truncated subtraction appears. -/
lemma succPow_mul_le (n : ℕ) :
    ∀ d : ℕ, 2 * d ≤ n → (n + 1) ^ d * n ≤ n ^ d * (n + 2 * d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ e ih =>
    intro h
    have he : 2 * e ≤ n := by omega
    have ih' := ih he
    calc (n + 1) ^ (e + 1) * n = (n + 1) * ((n + 1) ^ e * n) := by ring
      _ ≤ (n + 1) * (n ^ e * (n + 2 * e)) := Nat.mul_le_mul_left _ ih'
      _ = n ^ e * ((n + 1) * (n + 2 * e)) := by ring
      _ ≤ n ^ e * (n * (n + 2 * (e + 1))) := by
          refine Nat.mul_le_mul_left _ ?_
          nlinarith
      _ = n ^ (e + 1) * (n + 2 * (e + 1)) := by ring

/-- **Aux 2 (a unit shift at most doubles a guarded power).**

`(n+1)^d <= 2 n^d` whenever `2d <= n`, which is exactly the frozen third search
row `T + 2 >= 2(c_k - 1)` at `n = t + 2`, `d = c_k - 1`.  This is the discrete
substitute for the frozen `log 2 > 1/2` estimate of line 601.  General in `n` and
`d`. -/
lemma succPow_le_two_mul (n d : ℕ) (hn : 1 ≤ n) (h : 2 * d ≤ n) :
    (n + 1) ^ d ≤ 2 * n ^ d := by
  have h1 := succPow_mul_le n d h
  have h2 : (n + 1) ^ d * n ≤ (2 * n ^ d) * n := by
    calc (n + 1) ^ d * n ≤ n ^ d * (n + 2 * d) := h1
      _ ≤ n ^ d * (2 * n) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * n ^ d) * n := by ring
  exact Nat.le_of_mul_le_mul_right h2 hn

/-- **Aux 3 (the right-endpoint difference bound).**

`(n+1)^{d+1} <= n^{d+1} + (d+1)(n+1)^d`.  The **right** endpoint `n + 1` is
essential: the left-endpoint form `(n+1)^{d+1} <= n^{d+1} + (d+1) n^d` is false
already at `n = 1`, `d = 2` (`8 > 1 + 3`), so a discrete transcription of the
frozen derivative estimate must use this shape.  General in both arguments and
free of truncated subtraction. -/
lemma succPow_le_add_mul (n : ℕ) :
    ∀ d : ℕ, (n + 1) ^ (d + 1) ≤ n ^ (d + 1) + (d + 1) * (n + 1) ^ d := by
  intro d
  induction d with
  | zero => simp
  | succ e ih =>
    have hmono : n ^ (e + 1) ≤ (n + 1) ^ (e + 1) :=
      Nat.pow_le_pow_left (by omega) _
    calc (n + 1) ^ (e + 1 + 1) = (n + 1) * (n + 1) ^ (e + 1) := by ring
      _ ≤ (n + 1) * (n ^ (e + 1) + (e + 1) * (n + 1) ^ e) :=
          Nat.mul_le_mul_left _ ih
      _ = n ^ (e + 1 + 1) + n ^ (e + 1) + (e + 1) * ((n + 1) * (n + 1) ^ e) := by
          ring
      _ = n ^ (e + 1 + 1) + n ^ (e + 1) + (e + 1) * (n + 1) ^ (e + 1) := by ring
      _ ≤ n ^ (e + 1 + 1) + (n + 1) ^ (e + 1) + (e + 1) * (n + 1) ^ (e + 1) := by
          omega
      _ = n ^ (e + 1 + 1) + (e + 1 + 1) * (n + 1) ^ (e + 1) := by ring

/-- **Aux 4 (the second frozen search row, with the truncated exponent
cleared).**

In the regime the frozen text works in -- `3 <= c` and `2 <= T` -- the `Nat`
subtraction in `2^{T-1} >= c (T+2)^{c-1}` agrees with integer subtraction, so the
row is equivalent to the doubled form used inside `tkSearch_step`.  Recording
this makes the truncation checkable rather than assumed.  General in `c`, `T` and
the row's own two sides. -/
lemma tkSearch_second_row_unfolded (c T : ℕ) (hT : 2 ≤ T) :
    (c * (T + 2) ^ (c - 1) ≤ 2 ^ (T - 1)) ↔
      2 * (c * (T + 2) ^ (c - 1)) ≤ 2 ^ T := by
  obtain ⟨s, rfl⟩ : ∃ s, T = s + 1 := ⟨T - 1, by omega⟩
  have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ (s + 1 - 1) := by
    simp [pow_succ]; ring
  omega

/-- **Aux 4b (a guarded power absorbs its own multiplicity).**

`c N^{c-1} <= N^c` whenever `c <= N`, which is how the frozen second search row
`c_k (T+2)^{c_k - 1}` is compared with `(T+2)^{c_k}` at the witness of aux 7.
General in `c >= 1` and `N`, and free of truncated subtraction after the single
destructuring step. -/
lemma mul_pow_pred_le (c N : ℕ) (hc : 1 ≤ c) (h : c ≤ N) :
    c * N ^ (c - 1) ≤ N ^ c := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  calc (d + 1) * N ^ d ≤ N * N ^ d := Nat.mul_le_mul_right _ h
    _ = N ^ (d + 1) := by ring

/-- **Aux 5 (the frozen search is self-propagating).**

`expi:E-08-persistent` (`13-iteration-assembly.tex`, label line 612) as a single
discrete step: the **whole** three-row conjunction at `t` gives the whole
conjunction at `t + 1`.  General in the exponent `c >= 3`, the ceiling parameter
and the index.

This is the module's one genuinely hard proof, and reading note N1 records the
transposition.  Its three ingredients are exactly the frozen ones: aux 2 for the
unit shift (frozen line 601's `log 2 > 1/2`), aux 3 for the difference (frozen
lines 605--606's "the derivative of `2^t - (t+2)^{c_k}` is positive"), and the
second frozen row for the resulting `c (t+3)^{c-1} <= 2^t`. -/
lemma tkSearch_step (c lamv t : ℕ) (hc : 3 ≤ c) (h : TkSearch c lamv t) :
    TkSearch c lamv (t + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have ht2 : 2 ≤ t := by omega
  have hE : (t + 3) ^ (c - 1) ≤ 2 * (t + 2) ^ (c - 1) := by
    have hh := succPow_le_two_mul (t + 2) (c - 1) (by omega) h3
    rwa [show t + 2 + 1 = t + 3 by omega] at hh
  have hpow : 2 * 2 ^ (t - 1) = 2 ^ t := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp [pow_succ]; ring
  have hkey : c * (t + 3) ^ (c - 1) ≤ 2 ^ t := by
    calc c * (t + 3) ^ (c - 1) ≤ c * (2 * (t + 2) ^ (c - 1)) :=
          Nat.mul_le_mul_left _ hE
      _ = 2 * (c * (t + 2) ^ (c - 1)) := by ring
      _ ≤ 2 * 2 ^ (t - 1) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ t := hpow
  have hdiff : (t + 3) ^ c ≤ (t + 2) ^ c + c * (t + 3) ^ (c - 1) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hh := succPow_le_add_mul (t + 2) d
    rwa [show t + 2 + 1 = t + 3 by omega] at hh
  have hA : (t + 3) ^ c ≤ (t + 2) ^ c + 2 ^ t :=
    le_trans hdiff (Nat.add_le_add_left hkey _)
  refine ⟨?_, ?_, by omega⟩
  · rw [show t + 1 + 2 = t + 3 by omega]
    have hp1 : (2 : ℕ) ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [pow_succ]; ring
    omega
  · rw [show t + 1 + 2 = t + 3 by omega, show t + 1 - 1 = t by omega]
    exact hkey

/-- **Aux 6 (`expi:E-08-ceiling`).**

`13-iteration-assembly.tex`, label line 587, display lines 585--588:
`k <= 2^{lambda_k} < 2k` and `2^{lambda_k + 1} >= 2k`.  Frozen line 590 records
that the first inequality "also holds at `k = 1`, where `lambda_k = 0`"; the
`k = 1` strict half is therefore discharged separately in the proof below.
General in `k >= 1`.

This is the lemma Candidate B cannot state: with `Nat.log` in place of
`Nat.clog` the first conjunct is false at `k = 3`
(`floorLogarithm_breaks_the_ceiling_sandwich`). -/
lemma lambdaK_sandwich (k : ℕ) (hk : 1 ≤ k) :
    k ≤ 2 ^ lambdaK k ∧ 2 ^ lambdaK k < 2 * k ∧ 2 * k ≤ 2 ^ (lambdaK k + 1) := by
  have hle : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by norm_num) k
  have hstrict : 2 ^ Nat.clog 2 k < 2 * k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · have hk1 : k = 1 := by omega
      subst hk1
      simp
    · have hpos : 0 < Nat.clog 2 k := Nat.clog_pos (by norm_num) (by omega)
      have hlt : 2 ^ (Nat.clog 2 k - 1) < k :=
        Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
      have hdouble : (2 : ℕ) ^ Nat.clog 2 k = 2 * 2 ^ (Nat.clog 2 k - 1) := by
        obtain ⟨s, hs⟩ : ∃ s, Nat.clog 2 k = s + 1 :=
          ⟨Nat.clog 2 k - 1, by omega⟩
        rw [hs]
        simp [pow_succ]
        ring
      omega
  have hup : 2 * k ≤ 2 ^ (Nat.clog 2 k + 1) := by
    have hp : (2 : ℕ) ^ (Nat.clog 2 k + 1) = 2 * 2 ^ Nat.clog 2 k := by
      rw [pow_succ]; ring
    omega
  exact ⟨hle, hstrict, hup⟩

/-- **Aux 7 (the frozen search terminates).**

`13-iteration-assembly.tex:592--594`: "This search terminates because, for the
fixed integers `c_k` and `lambda_k`, the ratio `2^T/(T+2)^{c_k}` tends to
infinity", and `12-iteration-specification.tex:438--439`: "an exponential
eventually dominates every fixed polynomial".  Here that is **proved**, not
asserted: the witness is the explicit
`T = c(2c + lambda + 8) + lambda + 3`, and the exponential domination is the
banked `IterationAssembly.sq_le_two_pow` transported through
`(cm)^c <= (m^2)^c <= (2^m)^c`.  General in both parameters, including the
degenerate `c = 0`.

Statement pole: the trivial witness `T = 0` fails, since
`(0+2)^c + lamv + 2 >= 3 > 1 = 2^0` at every `c` and `lamv`. -/
lemma tkSearch_exists (c lamv : ℕ) : ∃ T, TkSearch c lamv T := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨lamv + 3, ?_, by simp, by simp⟩
    have := Nat.lt_two_pow_self (n := lamv + 3)
    simpa using by omega
  · set m := 2 * c + lamv + 8 with hm
    have hm8 : 8 ≤ m := by omega
    have hmsq : m ^ 2 ≤ 2 ^ m := by
      have := sq_le_two_pow m hm8
      omega
    have hcm : c ≤ c * m := Nat.le_mul_of_pos_right _ (by omega)
    have hmcm : m ≤ c * m := Nat.le_mul_of_pos_left _ (by omega)
    have hT2 : c * m + lamv + 3 + 2 ≤ m * m := by
      have h1 : lamv + 5 ≤ m := by omega
      have h2 : c * m + m ≤ m * m := by nlinarith
      omega
    have hbig : (c * m + lamv + 3 + 2) ^ c ≤ 2 ^ (c * m) := by
      calc (c * m + lamv + 3 + 2) ^ c ≤ (m * m) ^ c :=
            Nat.pow_le_pow_left hT2 c
        _ = (m ^ 2) ^ c := by ring
        _ ≤ (2 ^ m) ^ c := Nat.pow_le_pow_left hmsq c
        _ = 2 ^ (c * m) := by rw [← pow_mul]; ring_nf
    refine ⟨c * m + lamv + 3, ?_, ?_, by omega⟩
    · -- first row
      have hsplit : (2 : ℕ) ^ (c * m + lamv + 3) = 2 ^ (c * m) * 2 ^ (lamv + 3) := by
        rw [show c * m + lamv + 3 = c * m + (lamv + 3) by omega, pow_add]
      have hlam : lamv + 4 ≤ 2 ^ (lamv + 3) := by
        have := Nat.lt_two_pow_self (n := lamv + 3)
        omega
      have hone : 1 ≤ (c * m + lamv + 3 + 2) ^ c := Nat.one_le_pow _ _ (by omega)
      have hmul : (c * m + lamv + 3 + 2) ^ c * (lamv + 4)
          ≤ 2 ^ (c * m) * 2 ^ (lamv + 3) := Nat.mul_le_mul hbig hlam
      nlinarith [hmul, hone, hsplit]
    · -- second row
      have hcollapse : c * (c * m + lamv + 3 + 2) ^ (c - 1)
          ≤ (c * m + lamv + 3 + 2) ^ c :=
        mul_pow_pred_le c (c * m + lamv + 3 + 2) hc (by omega)
      have hstep : (2 : ℕ) ^ (c * m) ≤ 2 ^ (c * m + lamv + 3 - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact le_trans hcollapse (le_trans hbig hstep)

/-- **`T_k`, the least integer satisfying `eq:Tk-search`** --
`13-iteration-assembly.tex:592`, "Let `T_k` be the least integer satisfying
`eq:Tk-search`", at the frozen exponent `c_k = cexp k` and ceiling parameter
`lambda_k`.

Junk convention (reading note N2): the frozen text defines `T_k` for `k >= 1`
only; `Tk 0` is well defined and never consumed. -/
noncomputable def Tk (k : ℕ) : ℕ := Nat.find (tkSearch_exists (cexp k) (lambdaK k))

/-- **Aux 8 (the search index satisfies its own three-row predicate).**

The defining property of the frozen least-integer search, general in the level
index. -/
lemma tk_spec (k : ℕ) : TkSearch (cexp k) (lambdaK k) (Tk k) :=
  Nat.find_spec (tkSearch_exists (cexp k) (lambdaK k))

/-- **Aux 9 (the frozen exponent floor at every positive index).**

`13-iteration-assembly.tex:619`: "`c_k >= c_1 = 16(c_0 + 1) = 64`".  Derived from
the banked ladder `cexp 0 = 3`, `cexp (j+1) = 16(cexp j + 1)` and the banked
monotonicity `SizePropagation.cexp_mono`; the numeral `64` is computed, never
assumed.  General in `k >= 1`. -/
lemma cexp_ge_sixtyfour (k : ℕ) (hk : 1 ≤ k) : 64 ≤ cexp k := by
  have h1 : cexp 1 = 64 := by norm_num [cexp_succ, cexp_zero]
  have := cexp_mono hk
  omega

/-- **Aux 10 (`T_k >= 124`).**

`13-iteration-assembly.tex:619--620`: "the last inequality in `eq:Tk-search`
gives `T_k >= 124`".  Derived from the **third** search row at `c_k >= 64`
(`2(c_k - 1) >= 126`, so `T_k + 2 >= 126`); the numeral `124` is computed from
aux 9, never hardcoded.  General in `k >= 1`. -/
lemma tk_ge (k : ℕ) (hk : 1 ≤ k) : 124 ≤ Tk k := by
  have h3 := (tk_spec k).2.2
  have h64 := cexp_ge_sixtyfour k hk
  omega

/-- **Aux 11 (the frozen minimality step for `l(n)`).**

`13-iteration-assembly.tex:616--618`: "Since `n + 16 > 2^{2^{T_k}}` and `x` is
the least admissible integer in the definition of `l(n)`, `x >= T_k + 1`".  Since
`l` is a least-integer search with admissibility floor `2 <= r`, the argument is
run in the contrapositive direction that never applies minimality below the
floor.  General in `n` and `T`. -/
lemma ellN_gt_of_pow_le (n T : ℕ) (h : 2 ^ 2 ^ T ≤ n) : T + 1 ≤ ellN n := by
  have hn : 1 ≤ n := le_trans Nat.one_le_two_pow h
  by_contra hcon
  have hle : ellN n ≤ T := by omega
  have hspec := (ellN_spec n hn).1.2
  have hmono : (2 : ℕ) ^ 2 ^ ellN n ≤ 2 ^ 2 ^ T :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hle)
  omega

/-- **Aux 12 (`expi:E-08-persistent`, in additive form).**

`13-iteration-assembly.tex`, label line 612, display lines 607--613:
`2^t - (t+2)^{c_k} >= 2^{T_k} - (T_k+2)^{c_k} >= lambda_k + 2` for every
`t >= T_k`.  Carried additively per reading note N1, and obtained by iterating
aux 5.  General in `c >= 3`, the ceiling parameter, the base index and `t`. -/
lemma tkSearch_persistent (c lamv T : ℕ) (hc : 3 ≤ c) (hT : TkSearch c lamv T) :
    ∀ t, T ≤ t → TkSearch c lamv t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hT
  | succ m _ ih => exact tkSearch_step c lamv m hc ih

/-! ### Part 1b: the clock's aux battery -/

/-- **The four frozen clock gates** -- `13-iteration-assembly.tex:653`
(`V_0 = 1`) and lines 672--676:

```
V_k >= V_{k-1} + 1,   V_k >= n_val(k),   V_k >= 2^{2^{T_k}}.
```

Reader `eq:paper-Vk` (label line 322).  This is the **only** thing this module
uses about the frozen clock: the machine `A_raw`, its exact running time
`tau_k`, and the canonical environment `M_*` are not modelled (GAP-EXPOSED 2, 3).
Each field is a `Prop`-valued numerical gate on public data; there is no
complexity, promise, envelope or conclusion field, so no constructor can carry a
conclusion (mechanical rules M1, M2, M4).  The last two gates are guarded by
`1 <= k`, because the frozen output `A_k` is defined for `k >= 1` only (reading
note N2). -/
structure SlowClockGateSet (V : ℕ → ℕ) (nstep : ℕ → ℕ) : Prop where
  /-- Frozen line 653: "Set `V_0 = 1`." -/
  seed : V 0 = 1
  /-- Frozen line 673: `V_k >= V_{k-1} + 1`, in the zero-based successor form. -/
  strict : ∀ k, V k + 1 ≤ V (k + 1)
  /-- Frozen line 674: `V_k >= n_val(k)`. -/
  nval_gate : ∀ k, 1 ≤ k → nval nstep k ≤ V k
  /-- Frozen line 675: `V_k >= 2^{2^{T_k}}`. -/
  threshold_gate : ∀ k, 1 ≤ k → 2 ^ 2 ^ Tk k ≤ V k

/-- **Aux 13 (`V_k >= k + 1`).**

`13-iteration-assembly.tex:677--678`: "The first inequality makes `V_k` strictly
increasing and, by induction, `V_k >= k + 1`."  This is what bounds the frozen
search set and licenses the `Nat.findGreatest` encoding of `L`.  General in the
clock and the index. -/
lemma slowClock_ge_succ {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep) (k : ℕ) :
    k + 1 ≤ V k := by
  induction k with
  | zero =>
    have := hg.seed
    omega
  | succ m ih =>
    have := hg.strict m
    omega

/-- **`L(n) = max({0} ∪ {k : V_k <= n})`** -- `eq:L-clock`
(`12-iteration-specification.tex`, label line 486) and
`13-iteration-assembly.tex:680--683`.

Frozen lines 684--685 justify the search bound: "The maximum exists because
`V_k >= k + 1` implies that every feasible `k` is at most `n - 1`."  `Nat.findGreatest`
is exactly `max({0} ∪ {k <= n : P k})`, and the second conjunct of
`slowDiagonal_monotone_unbounded` shows the bound `n` loses no feasible index.

Frozen line 686: "If `L(n) = 0`, no one-level arrow is invoked."  The zero branch
carries no claim here beyond `zhat_zero_branch`, and
`slowIndex_zero_is_attained` shows the branch is genuinely reachable.

Reader counterpart: `eq:paper-slow-clock` (`05-iteration.tex`, label line 327,
display lines 325--328). -/
def slowIndex (V : ℕ → ℕ) (n : ℕ) : ℕ := Nat.findGreatest (fun k => V k ≤ n) n

/-- **Aux 14 (the clock index is inside its own search range, and is feasible
whenever it is positive).**

Both defining properties of the frozen maximum, general in the clock and the
source size. -/
lemma slowIndex_le_and_spec (V : ℕ → ℕ) (n : ℕ) :
    slowIndex V n ≤ n ∧ (1 ≤ slowIndex V n → V (slowIndex V n) ≤ n) := by
  refine ⟨Nat.findGreatest_le n, fun h => ?_⟩
  exact Nat.findGreatest_of_ne_zero (P := fun k => V k ≤ n) rfl (by omega)

/-! ## Part 2: `step:I-08` -- the padding-threshold search -/

/-- **`step:I-08`, the padding-threshold search**
(`13-iteration-assembly.tex`, label line 581, body lines 581--646).

Frozen headline: "The search defining `T_k` gives the displayed inequality
`E_{c_k}(n) < n/(2k)` with all ceiling margins exposed."

The conclusion is stated **multiplicatively**, `2 k E_{c_k}(n) < n`, which is
the frozen line 643--645 "Dividing by the positive integer `2k`" read backwards;
`natDivision_is_not_the_frozen_conclusion` refutes the truncated-division
spelling in the kernel.  Strictness enters exactly where the frozen proof puts
it: at the minimality of `l(n)` (frozen lines 629--634,
`n + 16 > 2^{2^{x-1}}`), and is never manufactured from the non-strict search
rows.

The single hypothesis is the frozen entry condition of line 615--616, "Now
suppose `n >= V_k`.  By definition `V_k >= 2^{2^{T_k}}`", used only through that
consequence, so the theorem needs no clock at all.  General in `k >= 1` and
`n`. -/
theorem paddingThresholdSearch (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ^ 2 ^ Tk k ≤ n) :
    2 * k * envE (cexp k) n < n := by
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have hT124 : 124 ≤ Tk k := tk_ge k hk
  have hx : Tk k + 1 ≤ ellN n := ellN_gt_of_pow_le n (Tk k) hn
  obtain ⟨u, hu⟩ : ∃ u, ellN n = u + 1 := ⟨ellN n - 1, by omega⟩
  have huT : Tk k ≤ u := by omega
  have hu3 : 3 ≤ u := by omega
  have hc3 : 3 ≤ cexp k := (cexp_ge_three_and_lt k).1
  have hpers : TkSearch (cexp k) (lambdaK k) u :=
    tkSearch_persistent (cexp k) (lambdaK k) (Tk k) hc3 (tk_spec k) u huT
  have hmargin : (u + 2) ^ cexp k + lambdaK k + 2 ≤ 2 ^ u := hpers.1
  have hxc : ellN n ^ cexp k ≤ (u + 2) ^ cexp k :=
    Nat.pow_le_pow_left (by omega) _
  have hmargin2 : ellN n ^ cexp k + lambdaK k + 2 ≤ 2 ^ u := by omega
  -- minimality of `l(n)`, applied strictly above the admissibility floor
  have hmin := (ellN_spec n hn1).2.1 u (by omega)
  have hminu : 2 ^ 2 ^ u < n + 16 := by
    have hnot : ¬ (n + 16 ≤ 2 ^ 2 ^ u) := fun hh => hmin ⟨by omega, hh⟩
    omega
  have hbig : (8 : ℕ) ≤ 2 ^ u := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu3
  have hhalf : (2 : ℕ) ^ 2 ^ u = 2 ^ (2 ^ u - 1) + 2 ^ (2 ^ u - 1) := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ u = s + 1 := ⟨2 ^ u - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel, pow_succ]
    ring
  have h16 : (16 : ℕ) ≤ 2 ^ (2 ^ u - 1) := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 ^ u - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnlow : 2 ^ (2 ^ u - 1) < n := by omega
  have hexp : ellN n ^ cexp k + lambdaK k + 1 ≤ 2 ^ u - 1 := by omega
  have hchain : (2 : ℕ) ^ (ellN n ^ cexp k + lambdaK k + 1) ≤ 2 ^ (2 ^ u - 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hsplit : (2 : ℕ) ^ (ellN n ^ cexp k + lambdaK k + 1)
      = 2 ^ ellN n ^ cexp k * 2 ^ (lambdaK k + 1) := by
    rw [show ellN n ^ cexp k + lambdaK k + 1 = ellN n ^ cexp k + (lambdaK k + 1) by
      omega, pow_add]
  have hceil := (lambdaK_sandwich k hk).2.2
  have hfinal : 2 * k * envE (cexp k) n
      ≤ 2 ^ ellN n ^ cexp k * 2 ^ (lambdaK k + 1) := by
    have : envE (cexp k) n * (2 * k) ≤ 2 ^ ellN n ^ cexp k * 2 ^ (lambdaK k + 1) :=
      Nat.mul_le_mul (le_of_eq rfl) hceil
    simpa [envE, Nat.mul_comm] using this
  omega

/-! ## Part 3: `step:I-09` -- the numerically certified slow clock -/

/-- **`step:I-09`, monotonicity and unboundedness of the clock index**
(`13-iteration-assembly.tex:704--710`).

Frozen line 704: "For every fixed `K`, all `n >= V_K` satisfy `K <= L(n)`.  This
is the precise meaning of an unbounded numerical prefix."  That finite form is
kept verbatim; nothing below states an asymptotic limit (GAP-EXPOSED 4).
Frozen lines 708--710: "Monotonicity follows directly because increasing `n` can
only enlarge the feasible set."

Reader counterpart: `lem:paper-slow-diagonal` lines 332--333, the
*nondecreasing* and *unbounded* clauses only.  General in the clock. -/
theorem slowDiagonal_monotone_unbounded {V nstep : ℕ → ℕ}
    (hg : SlowClockGateSet V nstep) :
    (∀ n n', n ≤ n' → slowIndex V n ≤ slowIndex V n') ∧
      (∀ K n, V K ≤ n → K ≤ slowIndex V n) := by
  constructor
  · intro n n' hnn'
    rcases Nat.eq_zero_or_pos (slowIndex V n) with h0 | hpos
    · omega
    · have hfeas := (slowIndex_le_and_spec V n).2 hpos
      have hle := (slowIndex_le_and_spec V n).1
      exact Nat.le_findGreatest (by omega) (by omega)
  · intro K n hK
    have hKn : K ≤ n := by
      have := slowClock_ge_succ hg K
      omega
    exact Nat.le_findGreatest hKn hK

/-- **`expi:E-09-pairs`, the certified safe prefix**
(`13-iteration-assembly.tex`, label line 695, display lines 693--696, with the
monotonicity argument of lines 687--691).

Frozen text: "If `L(n) = k >= 1`, then `V_k <= n`, and therefore
`n >= n_val(k)`.  For every `0 <= i < k`, monotonicity of `n_val` gives
`n >= n_val(k) >= n_val(i+1)`.  Thus the clock certifies every pair in the safe
prefix `(n, i)` with `0 <= i < L(n)`."

This is a **numerical eligibility** statement and nothing more: frozen lines
697--702 add that the clock "need not include every index which happens to
satisfy the numerical gates", that "it does not construct a record on any pair",
and that "no eligibility or realization claim for `i >= L(n)` is needed or made".
Accordingly the conclusion is the threshold inequality alone -- no record, no
trace, no admissibility (GAP-EXPOSED 1).

Reader counterpart: `lem:paper-slow-diagonal` lines 333--334, "All of the first
`L(n)` levels are valid".  General in the clock, the cutoff function, the source
size and the index. -/
theorem slowIndex_safePrefix {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    (n i : ℕ) (hi : i < slowIndex V n) : nval nstep (i + 1) ≤ n := by
  have hpos : 1 ≤ slowIndex V n := by omega
  have hfeas := (slowIndex_le_and_spec V n).2 hpos
  have hgate := hg.nval_gate (slowIndex V n) hpos
  have hmono : nval nstep (i + 1) ≤ nval nstep (slowIndex V n) := by
    refine (nval_closed nstep (i + 1)).2.2 _ ?_ ?_
    · exact (nval_closed nstep (slowIndex V n)).1
    · intro r hr
      exact nval_ge_of_lt nstep (by omega)
  omega

/-- **The capstone of `step:I-09`** (`13-iteration-assembly.tex:721--724`).

Frozen text: "Finally, when `L(n) >= 1`, Step `step:I-08` with `k = L(n)` gives
`E_{c_{L(n)}}(n)/n < 1/(2 L(n))`."

Kept in the frozen **finite-inequality** form, at the single clock index, with no
`Filter.Tendsto` and no asymptotic order relation anywhere (GAP-EXPOSED 4).
Frozen lines 725--728 record why the quantifier order matters: the estimate is
"justified by the single clock rather than by substituting an unbounded level
into a separate fixed-level eventual statement", which is exactly why `L n`
appears on both sides of the inequality below and the statement is not a
fixed-`k` eventual one.

Reader counterpart: `lem:paper-slow-diagonal` line 336, the display
`E_{c_{L(n)}}(n) = o(n)`.  General in the clock, the cutoff function and the
source size. -/
theorem slowClock_sublinear {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    (n : ℕ) (hpos : 1 ≤ slowIndex V n) :
    2 * slowIndex V n * envE (cexp (slowIndex V n)) n < n := by
  have hfeas := (slowIndex_le_and_spec V n).2 hpos
  have hgate := hg.threshold_gate (slowIndex V n) hpos
  exact paddingThresholdSearch (slowIndex V n) n hpos (by omega)

/-! ## Part 4: `step:I-10` and `sec:common-padding` -- the seed and the
common-size parameters -/

/-- The frozen seed search is inhabited -- `12-iteration-specification.tex:569--572`
and `13-iteration-assembly.tex:733--737`: `a_seed(n)` is "the least integer
`a >= 3` such that `q = 2^a - 2 >= 64(b+1)`" with `b = E_2(n)`.

Written additively, `64(b+1) + 2 <= 2^a`, which is the same condition on `ℕ`
(the frozen `q = 2^a - 2` is a genuine subtraction only once `a >= 1`) and avoids
a truncated subtraction inside a search predicate.

Statement pole: the trivial witness `a = 0` fails the frozen floor `3 <= a`, and
`a = 3` fails the size row for every `n >= 1`, since `b >= 512`. -/
lemma aSeedExists (n : ℕ) : ∃ a, 3 ≤ a ∧ 64 * (depthB n + 1) + 2 ≤ 2 ^ a := by
  refine ⟨64 * (depthB n + 1) + 2, by omega, Nat.le_of_lt Nat.lt_two_pow_self⟩

/-- **`a_seed(n)`** -- `12-iteration-specification.tex:569--572`,
`13-iteration-assembly.tex:733--737`.  Reader counterpart: `06-eth.tex:281`
with `:284`, "Let `a_seed(n)` be least such that ... `>= 64(B(n)+1)`". -/
noncomputable def aSeed (n : ℕ) : ℕ := Nat.find (aSeedExists n)

/-- **`q_seed(n) = 2^{a_seed(n)} - 2`** -- `12-iteration-specification.tex:575`.
Reader counterpart: `06-eth.tex:283`. -/
noncomputable def qSeed (n : ℕ) : ℕ := 2 ^ aSeed n - 2

/-- **`z_seed(n) = q_seed(n) + a_seed(n)`** --
`12-iteration-specification.tex:577` and `13-iteration-assembly.tex:763`.
Reader counterpart: `06-eth.tex:288`. -/
noncomputable def zSeed (n : ℕ) : ℕ := qSeed n + aSeed n

/-- **Aux 15 (the frozen induction `2^r - 2 >= 64(r+1)` for `r >= 10`).**

`13-iteration-assembly.tex:741--748`: "The inequality `2^r - 2 >= 64(r+1)` holds
at `r = 10`, since `2^{10} - 2 = 1022 >= 704 = 64 * 11`.  If it holds at `r`,
then `2^{r+1} - 2 = 2(2^r - 2) + 2 >= 128(r+1) + 2 >= 64(r+2)`."  Transcribed at
that exact threshold, additively, and general in `r`. -/
lemma seedGrowth (r : ℕ) (hr : 10 ≤ r) : 64 * (r + 1) + 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h64 : (64 : ℕ) ≤ 2 ^ m := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hd : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    omega

/-- **Aux 15b (the frozen seed search's own two defining properties).**

The search index satisfies its predicate, and no smaller index does.  Stated
against `aSeed` rather than against the raw `Nat.find` so that every consumer
below reads the frozen name.  General in `n` and the candidate index. -/
lemma aSeed_spec (n : ℕ) : 3 ≤ aSeed n ∧ 64 * (depthB n + 1) + 2 ≤ 2 ^ aSeed n :=
  Nat.find_spec (aSeedExists n)

/-- The minimality half of aux 15b, again stated against the frozen name. -/
lemma aSeed_find_min (n r : ℕ) (hr : r < aSeed n) :
    ¬ (3 ≤ r ∧ 64 * (depthB n + 1) + 2 ≤ 2 ^ r) :=
  Nat.find_min (aSeedExists n) hr

/-- **Aux 16 (the two frozen seed-exponent bounds).**

`13-iteration-assembly.tex:741--751`: `a <= b` ("Minimality of `a` therefore
gives `a <= b`") and `a >= 4` ("Also `a >= 4`, since `2^3 - 2 = 6 < 64(b+1)`").
Both halves at once, general in `n >= 1`. -/
lemma aSeed_bounds (n : ℕ) (hn : 1 ≤ n) : 4 ≤ aSeed n ∧ aSeed n ≤ depthB n := by
  have hb := (depthB_ge n hn).1
  obtain ⟨h3, hsize⟩ := aSeed_spec n
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have heq : aSeed n = 3 := by omega
    have hval : (2 : ℕ) ^ aSeed n = 8 := by rw [heq]; norm_num
    omega
  · exact Nat.find_le ⟨by omega, seedGrowth (depthB n) (by omega)⟩

/-- **Aux 17 (frozen minimality at the preceding integer).**

`13-iteration-assembly.tex:751--755`: "Hence `a - 1 >= 3`, and minimality at the
preceding integer gives `2^{a-1} - 2 < 64(b+1)`."  Carried additively.  General
in `n >= 1`. -/
lemma aSeed_min (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (aSeed n - 1) < 64 * (depthB n + 1) + 2 := by
  have h4 := (aSeed_bounds n hn).1
  have hmin := aSeed_find_min n (aSeed n - 1) (by omega)
  by_contra hcon
  exact hmin ⟨by omega, by omega⟩

/-- **Aux 18 (the frozen seed-width bound).**

`13-iteration-assembly.tex:756--759`: "Adding two, multiplying by two, and
subtracting two gives `2^a < 128(b+1) + 4`, `q = 2^a - 2 < 128 b + 130`."
General in `n >= 1`. -/
lemma qSeed_le (n : ℕ) (hn : 1 ≤ n) : qSeed n ≤ 128 * depthB n + 128 := by
  have h4 := (aSeed_bounds n hn).1
  have hmin := aSeed_min n hn
  have hdouble : (2 : ℕ) ^ aSeed n = 2 * 2 ^ (aSeed n - 1) := by
    obtain ⟨s, hs⟩ : ∃ s, aSeed n = s + 1 := ⟨aSeed n - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel, pow_succ]
    ring
  simp only [qSeed]
  omega

/-- **Aux 19 (the exact frozen power sandwich around the seed width).**

`13-iteration-assembly.tex:768--772`: "Since `a >= 3`,
`2^{a-1} < 2^a - 2 = q < 2^a`."  Both halves, general in `n >= 1`.  This is what
makes the ceiling identity exact rather than approximate. -/
lemma qSeed_sandwich (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (aSeed n - 1) < qSeed n ∧ qSeed n < 2 ^ aSeed n := by
  have h4 := (aSeed_bounds n hn).1
  have hdouble : (2 : ℕ) ^ aSeed n = 2 * 2 ^ (aSeed n - 1) := by
    obtain ⟨s, hs⟩ : ∃ s, aSeed n = s + 1 := ⟨aSeed n - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel, pow_succ]
    ring
  have hfour : (4 : ℕ) ≤ 2 ^ (aSeed n - 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (aSeed n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [qSeed]
  omega

/-- **Aux 20 (`E_2(n) >= 1` and the envelope gap `130 E_2(n) < E_3(n)`).**

`13-iteration-assembly.tex:779--785`:
`E_3(n)/E_2(n) = 2^{l(n)^2(l(n)-1)} >= 2^{18} = 262144 > 130`, using the banked
`l(n) >= 3`.  Stated multiplicatively so no division occurs.  General in
`n >= 1`. -/
lemma envelope_gap (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ envE 2 n ∧ 130 * envE 2 n < envE 3 n := by
  have h3 := (ellN_spec n hn).2.2
  have hx9 : 9 ≤ ellN n ^ 2 := by nlinarith
  have hexp : ellN n ^ 2 + 18 ≤ ellN n ^ 3 := by nlinarith
  have hle : (2 : ℕ) ^ (ellN n ^ 2 + 18) ≤ 2 ^ (ellN n ^ 3) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have heq : (2 : ℕ) ^ (ellN n ^ 2 + 18) = 262144 * 2 ^ ellN n ^ 2 := by
    rw [pow_add]
    norm_num
    ring
  have hone : 1 ≤ (2 : ℕ) ^ ellN n ^ 2 := Nat.one_le_two_pow
  simp only [envE]
  omega

/-- **`step:I-10`, the strict seed chain** (`13-iteration-assembly.tex:761--766`
and `12-iteration-specification.tex:599--602`):

```
z_seed(n) = q + a < 129 b + 130 < 130 b = 130 E_2(n) < E_3(n).
```

Frozen line 766 records why the middle inequality is strict: "the last strict
inequality uses `b >= 512 > 130`".  Both strict comparisons are landed together,
because the frozen sentence at `12-iteration-specification.tex:603` uses exactly
their composition ("so the positive-level branch also covers the initial seed").
General in `n >= 1`. -/
theorem seedSizeChain (n : ℕ) (hn : 1 ≤ n) :
    zSeed n < 130 * envE 2 n ∧ 130 * envE 2 n < envE 3 n := by
  have hq := qSeed_le n hn
  have ha := (aSeed_bounds n hn).2
  have hb := (depthB_ge n hn).1
  have hgap := envelope_gap n hn
  simp only [zSeed, depthB] at *
  omega

/-- **`step:I-10`, the exact ceiling identity**
(`13-iteration-assembly.tex:768--778`; `12-iteration-specification.tex:579--587`).

Frozen text: "The seed has `2^q q` entries, so
`ceil(log_2(2^q q)) = ceil(q + log_2 q) = q + a = z_seed(n)`", and frozen line
768 insists it "follows without approximation".  The proof is the frozen power
sandwich of aux 19 transported through `Nat.clog`, so nothing is estimated.
General in `n >= 1`. -/
theorem seedCeiling (n : ℕ) (hn : 1 ≤ n) :
    Nat.clog 2 (2 ^ qSeed n * qSeed n) = zSeed n := by
  obtain ⟨hlow, hhigh⟩ := qSeed_sandwich n hn
  have h4 := (aSeed_bounds n hn).1
  have hupper : 2 ^ qSeed n * qSeed n ≤ 2 ^ (qSeed n + aSeed n) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt hhigh)
  have hlower : 2 ^ (qSeed n + aSeed n - 1) < 2 ^ qSeed n * qSeed n := by
    have : (2 : ℕ) ^ (qSeed n + aSeed n - 1) = 2 ^ qSeed n * 2 ^ (aSeed n - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this]
    exact mul_lt_mul_of_pos_left hlow (by positivity)
  have hle : Nat.clog 2 (2 ^ qSeed n * qSeed n) ≤ qSeed n + aSeed n :=
    Nat.clog_le_of_le_pow hupper
  have hge : qSeed n + aSeed n ≤ Nat.clog 2 (2 ^ qSeed n * qSeed n) := by
    by_contra hcon
    have hlt : Nat.clog 2 (2 ^ qSeed n * qSeed n) ≤ qSeed n + aSeed n - 1 := by omega
    have := Nat.le_pow_clog (b := 2) (by norm_num) (2 ^ qSeed n * qSeed n)
    have hmono : (2 : ℕ) ^ Nat.clog 2 (2 ^ qSeed n * qSeed n)
        ≤ 2 ^ (qSeed n + aSeed n - 1) := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  simp only [zSeed]
  omega

/-- **`step:I-10`, the seed budget row** (`13-iteration-assembly.tex:786--790`).

Frozen text: "The seed budget also lies below the base majorant, because
`D_0 = Y_0 = a + 1 <= b + 1 < 130 b < E_3(n)`."  The frozen chain is landed as a
chain: no step is collapsed, and the middle strict inequality again uses
`b >= 512`.  General in `n >= 1`. -/
theorem seedBudgetRow (n : ℕ) (hn : 1 ≤ n) :
    aSeed n + 1 ≤ depthB n + 1 ∧ depthB n + 1 < 130 * depthB n ∧
      130 * depthB n < envE 3 n := by
  have ha := (aSeed_bounds n hn).2
  have hb := (depthB_ge n hn).1
  have hgap := envelope_gap n hn
  simp only [depthB] at *
  omega

/-- **`zhat(n)`, the uniform size majorant** -- `eq:uniform-size-majorant`
(`12-iteration-specification.tex`, label line 597, display lines 589--598):

```
zhat(n) = z_seed(n)          if L(n) = 0,
          E_{c_{L(n)}}(n)    if L(n) >= 1.
```

The two branches are the frozen ones, in the frozen order; nothing merges them.
Frozen line 603 records that the positive-level branch "also covers the initial
seed", which is `seedSizeChain`, not a redefinition.

Reader counterpart: the two-branch display at `06-eth.tex:298--302`. -/
noncomputable def zhat (V : ℕ → ℕ) (n : ℕ) : ℕ :=
  if slowIndex V n = 0 then zSeed n else envE (cexp (slowIndex V n)) n

/-- **`g(n) = max_{1 <= m <= n} zhat(m)`** -- the second half of
`eq:uniform-size-majorant` (`12-iteration-specification.tex:596`).

The fold starts at `m = 1`, exactly as the frozen index range does: `gMaj V 0` is
the empty maximum `0` and every recursive step adjoins `zhat V (m+1)`, so the
value at `n` is the maximum over `1 <= m <= n` and over nothing else.

Reader counterpart: `06-eth.tex:304`. -/
noncomputable def gMaj (V : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => max (gMaj V m) (zhat V (m + 1))

/-- **`e(n) = g(n) + ceil(log_2(n+2))`** -- `eq:common-size`
(`12-iteration-specification.tex`, label line 628, display lines 621--629) and
`13-iteration-assembly.tex:822`.  Reader counterpart: `06-eth.tex:317`, the first
line of `eq:paper-common-table-size`. -/
noncomputable def eCommon (V : ℕ → ℕ) (n : ℕ) : ℕ := gMaj V n + Nat.clog 2 (n + 2)

/-- **`S_n = 2^{e(n)}`** -- `eq:common-size`.  Reader counterpart:
`06-eth.tex:318`. -/
noncomputable def sCommon (V : ℕ → ℕ) (n : ℕ) : ℕ := 2 ^ eCommon V n

/-- **`T_n = S_n^2`** -- `eq:common-size`
(`12-iteration-specification.tex:627`).  Reader counterpart: the **first**
equality of `06-eth.tex:319`; its second equality `T_n = 2^{2 e(n)}` is claimed
by `commonSizeParameters` and is not restated in this definition. -/
noncomputable def tCommon (V : ℕ → ℕ) (n : ℕ) : ℕ := (sCommon V n) ^ 2

/-- **Aux 21 (the prefix maximum dominates every index in the frozen range, and
is nondecreasing).**

The two defining properties of `max_{1 <= m <= n}`, general in the clock, the
index and the source size.  The lower guard `1 <= m` is the frozen index range
and is live: `gMaj V 0 = 0` claims nothing about `zhat V 0`. -/
lemma gMaj_spec (V : ℕ → ℕ) :
    (∀ n m, 1 ≤ m → m ≤ n → zhat V m ≤ gMaj V n) ∧
      (∀ n, gMaj V n ≤ gMaj V (n + 1)) := by
  constructor
  · intro n
    induction n with
    | zero => intro m _ hm; omega
    | succ p ih =>
      intro m h1 hm
      rcases Nat.lt_or_ge m (p + 1) with h | h
      · exact le_trans (ih m h1 (by omega)) (le_max_left _ _)
      · have : m = p + 1 := by omega
        subst this
        exact le_max_right _ _
  · intro n
    exact le_max_left _ _

/-- **The common-size parameters of `eq:common-size`**
(`12-iteration-specification.tex`, label line 628; `13-iteration-assembly.tex:820--825`).

Frozen line 825: "Then `g(n) <= e(n)`, so both carriers have at most `S_n`
elements", and frozen line 627: `T_n = S_n^2 = 2^{2 e(n)}`.  Both facts, plus the
positivity of `S_n` that makes the square meaningful.

**No statement about any matrix is made here** (GAP-EXPOSED 5): `e`, `S` and `T`
are the frozen numbers, and the representative maps and the duplication argument
of `step:I-11` are not formalized.  General in the clock and the source size.

Reader counterpart: the **second** equality of `06-eth.tex:319`,
`T_n = 2^{2 e(n)}`. -/
theorem commonSizeParameters (V : ℕ → ℕ) (n : ℕ) :
    gMaj V n ≤ eCommon V n ∧ 1 ≤ sCommon V n ∧
      tCommon V n = 2 ^ (2 * eCommon V n) := by
  refine ⟨Nat.le_add_right _ _, Nat.one_le_two_pow, ?_⟩
  simp only [tCommon, sCommon, ← pow_mul]
  ring_nf

/-- **The uniform majorant is sublinear at the single clock index, in the frozen
finite form** (`12-iteration-specification.tex:604--605`,
"Equation `eq:Ek-sublinear` gives `zhat(n)/n <= 1/L(n)` whenever `L(n) >= 1`";
`13-iteration-assembly.tex:792--796`).

Multiplicative, at the single clock index, with no `Filter.Tendsto` anywhere
(GAP-EXPOSED 4).  The limit half of frozen lines 796--807 -- the `epsilon`/`N`
argument showing the prefix maximum preserves the estimate -- is **not** landed.
General in the clock, the cutoff function and the source size. -/
theorem zhat_sublinear {V nstep : ℕ → ℕ} (hg : SlowClockGateSet V nstep)
    (n : ℕ) (hpos : 1 ≤ slowIndex V n) :
    2 * slowIndex V n * zhat V n < n := by
  have h := slowClock_sublinear hg n hpos
  have hne : slowIndex V n ≠ 0 := by omega
  simpa [zhat, hne] using h

/-- **The zero branch of `eq:uniform-size-majorant`, and the frozen sentence that
covers it** (`12-iteration-specification.tex:591--592, 599--603`).

Frozen line 686: "If `L(n) = 0`, no one-level arrow is invoked."  On that branch
the majorant is the seed value, and frozen line 603 records that the seed value
is itself below the positive-level envelope: "so the positive-level branch also
covers the initial seed".  Nothing stronger is claimed on the zero branch
(reading note N2).  General in the clock and `n >= 1`. -/
theorem zhat_zero_branch (V : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (h0 : slowIndex V n = 0) :
    zhat V n = zSeed n ∧ zSeed n < 130 * envE 2 n ∧ 130 * envE 2 n < envE 3 n := by
  refine ⟨by simp [zhat, h0], (seedSizeChain n hn).1, (seedSizeChain n hn).2⟩

/-! ## Part 5: non-vacuity, statement poles, and the refuted candidate -/

/-- **A nondegenerate inhabitant of `SlowClockGateSet` at legal values**
(LANE-GATE 3).

The frozen recursion of `13-iteration-assembly.tex:653--669` sets `V_0 = 1` and
`V_k = max{A_k, tau_k}` with `A_k = max{n_val(k), V_{k-1} + 1, 2^{2^{T_k}}}`.
This witness drops the running-time term `tau_k` (which the module deliberately
does not model, GAP-EXPOSED 2) and keeps the three components of `A_k`, so it is
`A_k` itself -- a **legal** clock in the sense that it satisfies every gate the
frozen text imposes, at the frozen seed `V_0 = 1`, for an arbitrary cutoff
function.

It is nondegenerate in the sense that matters: it is not eventually constant
(the `strict` gate is proved, not assumed), its threshold gate is met at the
genuine frozen value `2^{2^{T_k}}` rather than at a weakened one, and
`witnessClock_reaches_positive_index` exhibits a source size at which the clock
index is genuinely positive, so the `1 <= L(n)` branch of every theorem above is
inhabited. -/
noncomputable def witnessClock (nstep : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => max (max (witnessClock nstep k + 1) (nval nstep (k + 1)))
      (2 ^ 2 ^ Tk (k + 1))

/-- **The witness clock satisfies all four frozen gates.**  General in the cutoff
function. -/
theorem witnessClock_gates (nstep : ℕ → ℕ) :
    SlowClockGateSet (witnessClock nstep) nstep where
  seed := rfl
  strict := fun k => by
    simp only [witnessClock]
    omega
  nval_gate := fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [witnessClock]
    omega
  threshold_gate := fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [witnessClock]
    omega

/-- **Non-vacuity of the positive-index branch.**

Every theorem in Part 3 and Part 4 that is guarded by `1 <= L(n)` is inhabited:
at `n = V_1` the clock index is at least `1`.  Without this, `slowClock_sublinear`
and `zhat_sublinear` would be statements about a possibly-empty branch. -/
theorem witnessClock_reaches_positive_index (nstep : ℕ → ℕ) :
    1 ≤ slowIndex (witnessClock nstep) (witnessClock nstep 1) :=
  (slowDiagonal_monotone_unbounded (witnessClock_gates nstep)).2 1 _ (le_refl _)

/-- **The zero branch is genuinely attained, so its guard is live.**

Frozen line 686 allows `L(n) = 0`, and at `n = 0` the frozen seed `V_0 = 1`
already exceeds `n`, so no index is feasible.

The second conjunct is the one that makes `zhat_zero_branch` non-vacuous, and it
is deliberately not the first: `zhat_zero_branch` is guarded by `1 <= n` as well
as by `L(n) = 0`, so the `n = 0` witness does **not** inhabit its hypothesis
bundle.  At `n = 1` both guards hold at once, because the frozen seed `V_0 = 1`
is feasible while `V_1 >= V_0 + 1 = 2` is not, so the frozen maximum
`max({0} ∪ {k : V_k <= 1})` is `0` even though the source size is positive.
That is why the zero branch is a real case rather than an unreachable one, and
why no theorem above claims anything on it beyond the seed bound. -/
theorem slowIndex_zero_is_attained (nstep : ℕ → ℕ) :
    slowIndex (witnessClock nstep) 0 = 0 ∧
      ∃ n, 1 ≤ n ∧ slowIndex (witnessClock nstep) n = 0 := by
  refine ⟨rfl, 1, le_refl _, ?_⟩
  have hstep : witnessClock nstep 0 + 1 ≤ witnessClock nstep 1 :=
    (witnessClock_gates nstep).strict 0
  have hseed : witnessClock nstep 0 = 1 := (witnessClock_gates nstep).seed
  have hnot : ¬ (witnessClock nstep 1 ≤ 1) := by omega
  simpa [slowIndex, Nat.findGreatest] using hnot

/-- **Hypothesis consistency for `paddingThresholdSearch`.**

The theorem's two hypotheses `1 <= k` and `2^{2^{T_k}} <= n` are jointly
satisfiable, so its conclusion is not vacuous.  Deriving `False` from them is
impossible for the trivial reason exhibited here: the frozen entry condition is
a lower bound on `n` and imposes nothing else, which is exactly why frozen line
615 can open with "Now suppose `n >= V_k`" and nothing more. -/
theorem paddingThresholdSearch_hypotheses_consistent :
    ∃ k n, 1 ≤ k ∧ 2 ^ 2 ^ Tk k ≤ n :=
  ⟨1, 2 ^ 2 ^ Tk 1, le_refl _, le_refl _⟩

/-- **Statement pole: the truncated-division spelling is not the frozen
conclusion.**

`step:I-08` concludes `E_{c_k}(n) < n/(2k)` over the rationals, and frozen lines
643--645 obtain it by "dividing by the positive integer `2k`".  Transcribing that
literally with `Nat` division would be a **strictly stronger** statement, because
`Nat` division truncates: `2 k E < n` does not imply `E < n / (2k)`.  The witness
below is `k = 1`, `E = 1`, `n = 3`.

An over-strong hypothesis or conclusion typechecks perfectly, which is why this
is recorded in the kernel and not in prose.  The multiplicative form landed above
is the frozen inequality's exact integer content. -/
theorem natDivision_is_not_the_frozen_conclusion :
    ∃ k E n : ℕ, 2 * k * E < n ∧ ¬ (E < n / (2 * k)) := by
  refine ⟨1, 1, 3, by norm_num, ?_⟩
  norm_num

/-- **Candidate B refuted: the floor logarithm breaks `expi:E-08-ceiling`.**

Candidate B spells `lambda_k = ceil(log_2 k)` as `Nat.log 2 k`.  At `k = 3` that
returns `1`, so `2^{lambda_3} = 2 < 3 = k`: the **first** inequality of
`expi:E-08-ceiling` (frozen display lines 585--588) fails outright, and with it
`2^{lambda_3 + 1} = 4 < 6 = 2k`, which is the exact step frozen lines 637--641
use to convert `2^{lambda_k + 1}` into the factor `2k`.  Candidate A's ceiling
delivers both at the same `k`, as the second conjunct records. -/
theorem floorLogarithm_breaks_the_ceiling_sandwich :
    (2 ^ Nat.log 2 3 < 3 ∧ 2 ^ (Nat.log 2 3 + 1) < 2 * 3) ∧
      (3 ≤ 2 ^ lambdaK 3 ∧ 2 * 3 ≤ 2 ^ (lambdaK 3 + 1)) := by
  refine ⟨⟨by norm_num [Nat.log], by norm_num [Nat.log]⟩, ?_⟩
  have h := lambdaK_sandwich 3 (by norm_num)
  exact ⟨h.1, h.2.2⟩

/-- **Statement pole: the frozen search is a three-row conjunction, and the
persistence estimate is a consequence of it, never a premise.**

A candidate encoding that kept only the first row and carried the persistence
estimate as an extra field would restate a derived telescope, which is banned.
`tkSearch_persistent` is exactly that field's content, derived from the
three-row predicate alone, so the field would be redundant.  Recorded here at the
frozen shape so the reading cannot return unnoticed.  General in `c >= 3`, the
ceiling parameter, the base index and `t`. -/
theorem persistence_field_would_be_redundant (c lamv T : ℕ) (hc : 3 ≤ c)
    (hT : TkSearch c lamv T) :
    ∀ t, T ≤ t → (t + 2) ^ c + lamv + 2 ≤ 2 ^ t :=
  fun t ht => (tkSearch_persistent c lamv T hc hT t ht).1

/-- **The search predicate fires nondegenerately at a legal exponent.**

`TkSearch` is inhabited at the smallest frozen exponent `c_0 = 3` with
`lambda = 0`, at `T = 12`, where all three rows are strict-or-tight numerically:
`14^3 + 2 = 2746 <= 4096`, `3 * 14^2 = 588 <= 2048`, `4 <= 14`.  This is the
witness that shows the conjunction is not accidentally empty, and it is checked
by evaluation rather than asserted. -/
theorem tkSearch_fires_nondegenerate : TkSearch 3 0 12 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The persistence step fires at that witness.**

Aux 5 applied to the concrete inhabitant above: the conjunction really does
propagate, at a legal exponent, one integer step at a time. -/
theorem tkSearch_step_fires : TkSearch 3 0 13 ∧ TkSearch 3 0 20 := by
  refine ⟨tkSearch_step 3 0 12 (by norm_num) tkSearch_fires_nondegenerate, ?_⟩
  exact tkSearch_persistent 3 0 12 (by norm_num) tkSearch_fires_nondegenerate 20
    (by norm_num)

end EthInapproximability.ParameterizedNP.PaddingAndClock
