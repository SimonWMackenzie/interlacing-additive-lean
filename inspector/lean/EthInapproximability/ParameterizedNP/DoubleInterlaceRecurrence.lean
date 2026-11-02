import EthInapproximability.ParameterizedNP.PublicRecords
import EthInapproximability.ParameterizedNP.DirectOutputFromOpening

/-!
# Parameterized NP route: the double-interlace recurrence and the per-level
selector accumulation (`step:L-01`, `step:L-14`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`ONELEVEL-OVERHEAD-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t3g` tranche.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## What this module is, and what it is not

`sec:one-level-assembly` (`11-one-level-assembly.tex`) opens with `step:L-01`
(label line 20), which does two things in one step:

1. it **composes** the two interlaces at two *different* widths,

   ```
   U = Int_q(N),   W = transpose U,   R+ = transpose (Int_Q W),
   q = 2^r,        Q = 2^{r_Q}        (lines 16--17, 22--29);
   ```

2. it prints the **per-level selector accumulation** at the manuscript
   schedule (lines 58--96): the four power-of-two widths `q_2, s, q, Q` with
   their defining exponents, the two least-power-of-two sandwiches, the
   overhead `H` in its three displayed forms (`exp:E-01-overhead`, label line
   92), and the closing sentence of lines 94--96 -- "There is therefore no
   ceiling loss hidden in a selector cost: for each of the four power-of-two
   widths, the protocol cost `ceil(log_2 w)` equals `log_2 w`."

`step:L-14` (label line 809) then states the exact carrier equations of lines
858--864, `|Rows(R+)| = (q m_N)^Q` and `|Cols(R+)| = Q n_N^q`.

**The carrier equations themselves are already banked** and are *not* re-proved
here: `OneLevelAssembly.doubleInterlaceCarriers` and
`.oneLevelAssembly_carriers` (`ONELEVEL-001`) and
`IterationAssembly.carrierRowNext` / `.carrierColNext` (`SIZE-001`) own them.
What is **new** in this module is:

* the accumulation written as the **protocol cost at the four widths**
  (`selectorCostSum`), i.e. `H` in the honest `ceil(log_2 w)` spelling that
  mechanical rule `M8` demands *before* the power-of-two licence is applied,
  together with the equation that collapses it onto the banked exponent form
  `OneLevelCompletion.levelOverhead` -- which is exactly lines 90 and 94--96;
* `H` at its **defining displays** (`scheduleOverhead`), so that the five
  exponents are *evaluated* through their own definitional chains
  (`u -> s -> q_2`, `A_wrap, L_P -> q`, `Q_0 -> r_Q`) rather than assigned;
* the two least-power-of-two sandwiches of lines 76--81, `12s|E| <= q_2 <
  24s|E|` and `Q_0 <= Q < 2Q_0`, read off the two banked accessors;
* the **join**: the Section-10 hub's exact complexity for `R+` and the
  Section-11 carrier equations, delivered about **one and the same term**.

Nothing here strengthens, weakens, or discharges anything banked, and **no
route completion is claimed.**

## The join, and why it is a `rfl`

`ScaleAlignOpening.wrapperW N r`, `OneLevelCompletion.alignedMatrix N r` and
`EthBridge.Rnext N (2^r)` are the *same term*; hence so are
`EthBridge.Rnext (ScaleAlignOpening.wrapperW N r) (Qwidth b_out delta_U)` --
the object the Section-10 hub speaks about -- and
`OneLevelCompletion.levelOutput N r b_out delta_U` -- the object the Section-11
carrier equations speak about.  `levelOutput_eq_bridge_of_wrapperW` states that
identification in the kernel, so that the headline theorem is a checked join
and not an appeal to two similar-looking matrices.

## Both interlace widths, kept distinct, neither a numeral

`q = 2^r` is the inner scale-alignment width of `09-first-wrapper.tex`; `Q =
2^{r_Q}` is the outer bridge width of `10-direct-bridge.tex:51`.  They occur
here only through their exponents `r` and `rQ b_out delta_U`, both of which
stay binders or banked accessors: **no numeral is assigned to either**.  The
asymmetry is proved to be real and not notational --
`selectorAccumulation_symmetric_carriers_are_not` shows that the *cost* is
symmetric under exchanging the two exponents while the *row carrier* is not,
so a module that conflated the widths would still typecheck against the cost
equation and fail against the carrier equation.

## Autoformalization anchors

* `sections/11-one-level-assembly.tex` (SHA-256
  `8d2ac12b0da9c23eb1f97167060e0afc3b26dcc0a7052c37e1aa2eb8e258f97d`),
  `step:L-01` (label line 20): lines 16--17 (`q = 2^r`, `Q = 2^{r_Q}`), 22--29
  (the two-interlace composition), 58--67 (the manuscript schedule), 68--75
  (the two exact least-power-of-two exponents), 76--81 (the two sandwiches),
  `exp:E-01-overhead` (label line 92, display lines 83--93), 94--96 (the
  no-ceiling-loss sentence); `step:L-12` (label line 766) lines 769--783; and
  `step:L-14` (label line 809) lines 858--864.
* `sections/06-parameter-schedule.tex` (SHA-256
  `46a9aa59695357e5e2a42fa08537939a70f0d8421eb9cf1365ab42f8125b5fb9`):
  `eq:s-choice` (label line 120, display lines 109--121: `A_pre` at 111--115,
  `u` at 116--117, `s = 2^{ceil(B_s u^2)}` at 118), line 124 (`q_2` the least power of
  two at least `12 s N_E`), `eq:stage1-scales` (`06:314`, `a = C_0
  (log_2 A_*)^2`), `eq:q-deltaU` (`06:515`, `q = 2^{A_wrap L_P^2}`),
  `eq:Q-theta-choice` (`06:533`).
* `sections/10-direct-bridge.tex` lines 43--51 (`Q_0`, `Q = 2^{r_Q}`), 63, 67,
  69--70, 73--74; `sections/09-first-wrapper.tex` lines 107, 268, 1794.
* `sections/02-mechanical-contract.tex` lines 771--775 (`q, Q >= 2`).

## Reader counterpart

**Exactly one** reader item is claimed, and a repository-wide census of every
`03-parameterized-construction.tex` citation in `src/` confirmed it was
previously unassigned (the claimed lines of that file are 44, 53--58, 59,
64--67, 72, 72--73, 81--82, 92, 100--101, 105--107, 121--123, 142, 153,
187--195, 290--297, 306--358, 318--326, 329--336, 338--346, 348--354,
417--429, 431--435, 437--449, 493--498 -- line 619 appears nowhere):

* `sections/03-parameterized-construction.tex` (SHA-256
  `72c451612475b85d2fef1ca3eb4492a100defebc95125a35a02f98622ba0ec61`), lines
  **617--619**, "The interlace `W = Int_q(N)^T` aligns their row thresholds and
  adds exactly `r_q = log q` selector bits in both promise cases" -- claimed by
  `innerSelector_adds_exactly_rq`, and by that declaration alone.  The file was
  opened and the item checked, first-hand, to state the same fact.

**Deliberately given no reader counterpart, to avoid a double assignment.**
Every other component fact already has an assigned reader item:
`05-iteration.tex:109` (`H_i = K_i + r_{q,i} + r_{Q,i}`) belongs to
`BRIDGE-COMPLETION-001`'s `OneLevelCompletion.levelOverhead`;
`05-iteration.tex:97` and `:99` are the navigation loci of
`OneLevelCompletion.alignedMatrix` and `.levelOutput`; `:101` is the inner
width sentence already used by `OneLevelCompletion.alignedSelectorCost_exact`;
`eq:paper-exact-carrier-recurrence` (`05-iteration.tex`, label line 166)
belongs to `SIZE-001`'s `IterationAssembly.iterationCarrierStep`;
`eq:one-level-exact-carriers` (`04-bridge.tex:177--181`) belongs to `SIZE-001`;
and the bridge output items of `04-bridge.tex` lines 101--104, 107, 109 and
112--113 belong to `BRIDGE-OUTPUT-004`, `-003`, `-002` and `-001`.  Claiming
any of them here would reassign an assigned item.

Crosswalk row: "One-level fold".

## Status and dependencies

* Proof status: **new (elementary) wiring plus two new public integers**,
  relative to landed inputs.  No new mathematics; nothing banked is edited,
  widened, or re-proved.
* Consumed strictly **by pin**, never restated:
  * `DirectOutputFromOpening.directOutput_at_the_paper_instance` and
    `.directOutput_from_opening_at_the_scheduled_point` (`BRIDGE-OUTPUT-004`)
    -- the Section-10 hub;
  * `OneLevelAssembly.oneLevelAssembly_carriers`,
    `.doubleInterlaceCarriers` (`ONELEVEL-001`);
  * `OneLevelCompletion.levelOverhead`, `.stage4Overhead`, `.stage4Exact`,
    `.alignedMatrix`, `.levelOutput`, `.alignedSelectorCost_exact`
    (`BRIDGE-COMPLETION-001`);
  * `BridgeOutputEquality.rowsCard`, `.colsCard`, `.bridgeCarriers`
    (`BRIDGE-OUTPUT-003`);
  * `DirectOutput.clog_two_pow` (`BRIDGE-OUTPUT-001`);
  * `EntryGates.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`, `.four_le_rQ`, `.Q0`,
    `.Q0_le_Qwidth`, `.two_pow_pred_lt_Q0`, `.directEntryGates`
    (`BRIDGE-ENTRY-001`);
  * `ParameterSchedule.sScale`, `.sScale_eq_pow`, `.sScale_floor`, `.uAux`,
    `.Apre`, `.three_le_uAux`, `.qWrap`, `.qWrap_eq_two_pow`, `.deltaU`,
    `.etaR`, `.theta` (`SCHEDULE-001`);
  * `GuardedSourceSlab.q2`, `.card_le_q2`, `.q2_le_of_le`, `.q2_lt`
    (`SOURCE-SLAB-001`);
  * `ScaleAlignOpening.wrapperW`, `.scaleAlignWidth`,
    `.scaleAlignWidth_def` (`SCALEALIGN-001`);
  * `FirstWrapperClose.DenseRung` (`FIRST-WRAPPER-CLOSE-001`);
  * the vendored `EthBridge.Rnext`.
* Imports: `PublicRecords.lean` and `DirectOutputFromOpening.lean` only, hence
  `GuardedSourceSlab.lean`, `OneLevelAssembly.lean`, `OneLevelCompletion.lean`,
  `DirectBridgeOpening.lean`, `FirstWrapperClose.lean`,
  `ParameterSchedule.lean` and their chains, `EthInapproximability.Prelude`,
  and through it `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP balanced-family
  axiom is not in scope, and there is no contact with `EXPANDER-001` (which by
  design has no Lean declaration and would have to stay an explicit named
  hypothesis).
* External adapters: none.  Nothing here is axiomatized; no opaque certificate
  and no unproved placeholder of either kind the release gate scans for.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Conditional statuses of the consumed chain, disclosed exactly

The ledger statuses of every consumed row travel unchanged; this module
improves none of them, and each conditionality below is inherited, never
introduced.

1. **`FIRST-WRAPPER-CLOSE-001`.**  The canonical instance
   `doubleInterlaceRecurrence` runs under the **named, undischarged** binder
   `FirstWrapperClose.DenseRung` (`eq:wrapper-u-dense`, `09:262--263`), exactly
   as its supplier `DirectOutputFromOpening.directOutput_at_the_paper_instance`
   does, and to exactly the same degree.  The unconditional form is
   GAP-EXPOSED G3 of `BRIDGE-OPENING-001`.  Nothing here weakens, discharges,
   or reorients that binder.
2. **The close's named hypothesis.**  Through that row travel, unchanged, the
   low-rung inputs `hne`, `hmem` of `09:274--334`, which
   `FirstWrapperClose.commonThreshold_of_firstWrapperClose` takes as explicit
   binders rather than proving.  They are carried verbatim here.
3. **The stated-not-proved terminal lemma.**  `TERMINAL-TWO-STREAM-001`'s
   headline `lem:terminal-two-stream` is landed as a **stated** claim, not a
   proved theorem, and is **not invoked** anywhere below; it reaches this
   module only as part of the `FIRST-WRAPPER-CLOSE-001` chain's recorded
   status.  Likewise `DENSE-WRAPPER-FRONTIER-001`,
   `WRAPPER-PROTECTED-EARLY-001` (landed, GAP-EXPOSED items intact) and
   `WRAPPER-MASS-REDISTRIBUTION-001` (landed with four GAP-EXPOSED items and
   its own deferred canonical-inhabitation obligation on record).
4. **`BRIDGE-OUTPUT-002`/`-003`/`-004`.**  Their own GAP-EXPOSED items --
   including `-003`'s item 1, that `eq:direct-input` has no exhibited
   unconditional inhabitant in Lean -- are untouched.
5. **`SIZE-001`.**  The uniform majorant `exp:E-14-raw` (label line 850) is
   **not** proved here and stays where it is; frozen line 856 records that
   "the finite one-level theorem and the exact recurrence below do not consume
   that uniform comparison".

## GAP-EXPOSED

1. **`a = C_0 (log_2 A_*)^2` is consumed at its exponent, not at its own
   definitional chain.**  `scheduleOverhead` takes `C_0` and `log_2 A_*` as
   binders, because the frozen `A_*` of `eq:Astar-choice` (`06:298--304`) is
   the least power of two above a six-branch maximum whose branches include
   `B_pub`, `z_R`, `log_2 q_2` and `ceil(log_2 U_0)`, and neither `A_*` nor
   `U_0` has a Lean reification yet.  This range -- the Stage-1 half of
   `06:290--330` -- is **deferred**, and the module states nothing about it.
   The remaining four exponents *are* evaluated through their own chains.
2. **The unconditional canonical inhabitation of the headline** is deferred
   with, and only with, `DenseRung`: see conditional status 1 above.  The
   obligation is registered in the ledger row and is discharged when
   `DenseRung` is proved, never by any probe in this module.
3. **The `H`-to-budget substitution is stated, not chained to Stages 1--4.**
   `doubleInterlaceRecurrence_budget` derives `comp R+ = D + H + 1` from
   `C = stage4Exact D a w_2 w_s` taken as a *binder*.  The chain producing that
   equation from the promise certificates through Stages 1--4 is `ONELEVEL-001`
   and `STAGE4-ALIGN-001`, not this module.
-/

set_option linter.unusedVariables false

namespace EthInapproximability.ParameterizedNP.DoubleInterlaceRecurrence

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion

/-! ## Part 0  The two public integers

Both are functions of public data alone (mechanical rules `M1`, `M2`): no
promise certificate, no complexity value and no robustness value is an
argument of either.  Neither carries a conclusion. -/

/-- **The per-level selector accumulation, in the honest `M8` spelling.**

`11-one-level-assembly.tex`, `exp:E-01-overhead` (label line 92) read together
with lines 94--96.  Mechanical rule `M8` (`02-mechanical-contract.tex`) prices
a selector of width `w` at `ceil(log_2 w)` and permits the reading `log_2 w`
only after `w` has been proved to be a power of two.  This definition is `H`
*before* that licence is applied: the seed-copy exponent `a` plus the four
protocol costs

```
ceil(log_2 q_2) + ceil(log_2 s) + ceil(log_2 q) + ceil(log_2 Q)
```

at the four widths the level actually sends selectors over -- the Stage-2
coordinate width `q_2`, the Stage-3 bin count `s`, the inner scale-alignment
width `q`, and the outer bridge width `Q`.  `Nat.clog 2` is the integer
`ceil(log_2 .)`.

The frozen closing sentence of lines 94--96 is then the *equation*
`selectorCostSum_eq_levelOverhead` below, not a definitional convention: at the
four power-of-two widths this integer equals the banked exponent form
`OneLevelCompletion.levelOverhead`, so "there is no ceiling loss hidden in a
selector cost".

The four widths are separate arguments in a fixed order and are never
identified; in particular `q` and `Q` are the third and fourth. -/
def selectorCostSum (a q2 s q Q : ℕ) : ℕ :=
  a + Nat.clog 2 q2 + Nat.clog 2 s + Nat.clog 2 q + Nat.clog 2 Q

/-- **`H` at its five defining displays** --
`11-one-level-assembly.tex`, `exp:E-01-overhead` (label line 92), the **first**
of its three displayed forms (lines 86--87):

```
H = a + r_2 + ceil(B_s u^2) + A_wrap L_P^2 + r_Q.
```

Each summand is written at the display that *defines* it, not at a free
exponent:

* `a = C_0 (log_2 A_*)^2` (`eq:stage1-scales`, `06:314`; restated `11:61`).
  `C_0` and `log_2 A_*` are binders -- see GAP-EXPOSED 1 in the module header;
  `A_*` is a power of two (`06:298`), so `log_2 A_*` is an integer.
* `r_2 = clog_2(12 s |E|)` (`11:70--71`), the exponent of the Stage-2
  coordinate width `q_2` of `06:124`.
* `ceil(B_s u^2) = log_2 s` (`eq:s-choice` line `06:118`; restated `11:63`).  The
  frozen ceiling is the identity at an integer configuration field, which is
  the banked `ParameterSchedule.sScale_eq_pow`.
* `A_wrap L_P^2 = log_2 q` (`eq:q-deltaU`, `06:515`; restated `11:64`).
* `r_Q = clog_2 Q_0 = log_2 Q` (`11:73--74`), supplied here as the banked
  accessor `EntryGates.rQ` at its own arguments.

`sVal` and `eE` are the source scale `s` and the edge count `|E|`; they occur
only inside `r_2`, exactly as `11:70` writes it. -/
def scheduleOverhead (C0 lA sVal eE Bs u Awrap LP rQv : ℕ) : ℕ :=
  C0 * lA ^ 2 + Nat.clog 2 (12 * sVal * eE) + Bs * u ^ 2 + Awrap * LP ^ 2 + rQv

/-! ## Part 1  The aux-lemma battery

Six general properties.  None is about a pinned instance: each quantifies over
arbitrary widths, exponents, carriers or matrices. -/

/-- **Aux 1 (the `M8` licence, at an arbitrary power-of-two width).**

`02-mechanical-contract.tex` rule `M8`, and the frozen sentence
`11-one-level-assembly.tex:94--96`: at a width that *is* a power of two the
protocol cost `ceil(log_2 w)` equals the exponent exactly -- an equation, never
an inequality.  General in the width and the exponent; this is the only
property of `Nat.clog` the accumulation uses. -/
lemma selectorCost_of_powTwo {w e : ℕ} (h : w = 2 ^ e) : Nat.clog 2 w = e := by
  subst h
  exact DirectOutput.clog_two_pow e

/-- **Aux 2 (the accumulation splits at the Stage-4 boundary).**

`11-one-level-assembly.tex:12`, `K = a + log_2 q_2 + log_2 s`, and the reader's
`H_i = K_i + r_{q,i} + r_{Q,i}`: the level's cost is the Stage-4 public
overhead plus the two wrapper selectors, and the split is exact.  Recorded so
that the two interlace contributions are visibly *separate summands* rather
than an aggregate.  General in all five arguments. -/
lemma selectorCostSum_split (a q2 s q Q : ℕ) :
    selectorCostSum a q2 s q Q
      = (a + Nat.clog 2 q2 + Nat.clog 2 s) + (Nat.clog 2 q + Nat.clog 2 Q) := by
  unfold selectorCostSum
  omega

/-- **Aux 3 (monotone in every width).**

Widening any selector never lowers its cost, because `Nat.clog 2` is monotone.
This is the direction the schedule uses whenever it enlarges a width to clear a
gate (for instance `06:744--747` raising `A_wrap`), and it is what makes the
accumulation a *bound* as well as an equation.  General in all eight widths. -/
lemma selectorCostSum_mono {a q2 s q Q q2' s' q' Q' : ℕ} (h2 : q2 ≤ q2')
    (hs : s ≤ s') (hq : q ≤ q') (hQ : Q ≤ Q') :
    selectorCostSum a q2 s q Q ≤ selectorCostSum a q2' s' q' Q' := by
  unfold selectorCostSum
  have e2 := Nat.clog_mono_right 2 h2
  have es := Nat.clog_mono_right 2 hs
  have eq' := Nat.clog_mono_right 2 hq
  have eQ := Nat.clog_mono_right 2 hQ
  omega

/-- **Aux 4 (no ceiling loss: the accumulation collapses onto the exponents).**

The frozen sentence `11-one-level-assembly.tex:94--96` in its exact reading,
and with it the third displayed form of `exp:E-01-overhead` (line 90),
`H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`.  Whenever the four widths
are powers of two -- which the schedule proves separately for each of them --
the `M8` protocol cost of the level equals the banked exponent form
`OneLevelCompletion.levelOverhead`.

Stated at **four arbitrary powers of two**, so it is the shape of the frozen
sentence and not the route's values; the route's own widths appear only in
Part 2.  This is the round-trip property of `selectorCostSum`: widths in,
exponents out, and back. -/
theorem selectorCostSum_eq_levelOverhead (a w2 ws wq wQ : ℕ) {q2 s q Q : ℕ}
    (hq2 : q2 = 2 ^ w2) (hs : s = 2 ^ ws) (hq : q = 2 ^ wq) (hQ : Q = 2 ^ wQ) :
    selectorCostSum a q2 s q Q = levelOverhead a w2 ws wq wQ := by
  unfold selectorCostSum levelOverhead stage4Overhead
  rw [selectorCost_of_powTwo hq2, selectorCost_of_powTwo hs,
    selectorCost_of_powTwo hq, selectorCost_of_powTwo hQ]

/-- **Aux 5 (round trip at the exponents).**

The specialization of aux 4 in which the widths are *written* as powers of two.
Recorded separately because it is the form the size thread consumes: the level
overhead is recovered from the four exponents with no residue. General. -/
lemma selectorCostSum_pow (a w2 ws wq wQ : ℕ) :
    selectorCostSum a (2 ^ w2) (2 ^ ws) (2 ^ wq) (2 ^ wQ)
      = levelOverhead a w2 ws wq wQ :=
  selectorCostSum_eq_levelOverhead a w2 ws wq wQ rfl rfl rfl rfl

/-- **Aux 6 (the accumulation is strictly increasing in the outer exponent).**

Adding one bit to the bridge width adds exactly one bit to the level, and in
particular the level overhead is *not* constant in `r_Q`.  General in all five
arguments; this is the property that makes the `H`-indexed budget update of
`eq:paper-budget-update` a real recursion rather than a fixed shift. -/
lemma levelOverhead_succ_outer (a w2 ws wq wQ : ℕ) :
    levelOverhead a w2 ws wq (wQ + 1) = levelOverhead a w2 ws wq wQ + 1 := by
  unfold levelOverhead stage4Overhead
  omega

/-! ## Part 2  `exp:E-01-overhead` at the manuscript schedule

The four widths are now the route's own, and each exponent is obtained by
**evaluating** its defining display in dependency order -- `A_pre -> u -> s ->
q_2` for the Stage-2 width, `A_wrap, L_P -> q` for the inner width, and
`Q_0 -> r_Q -> Q` for the outer width.  No numeral is assigned to any of
them. -/

/-- **The four scheduled widths are powers of two, with their exact
exponents.**

One statement collecting the four `M8` licences the level needs, each read off
the banked reification of its own defining display:

* `q_2 = 2^{clog_2(12 s |E|)}` -- `06:124`, banked as `GuardedSourceSlab.q2`;
* `s = 2^{B_s u^2}` -- `eq:s-choice` `06:118`, banked as
  `ParameterSchedule.sScale` with `ParameterSchedule.sScale_eq_pow` supplying
  the frozen ceiling at an integer configuration field;
* `q = 2^{A_wrap L_P^2}` -- `eq:q-deltaU` `06:515`, banked as
  `ParameterSchedule.qWrap`;
* `Q = 2^{r_Q}` -- `10:51`, banked as `EntryGates.Qwidth_eq_two_pow`.

General in `s`, `B_s`, `u`, `A_wrap`, `L_P`, `b_out`, `delta_U` and the source
graph; nothing is instantiated. -/
theorem scheduledWidths_are_powers_of_two {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : GuardedSourceGraph.EndpointGraph V E) (sVal Bs u Awrap LP bout : ℕ)
    (δU : ℝ) :
    GuardedSourceSlab.q2 G sVal
        = 2 ^ Nat.clog 2 (12 * sVal * Fintype.card E) ∧
      ParameterSchedule.sScale Bs u = 2 ^ (Bs * u ^ 2) ∧
      ParameterSchedule.qWrap Awrap LP = 2 ^ (Awrap * LP ^ 2) ∧
      Qwidth bout δU = 2 ^ rQ bout δU :=
  ⟨rfl, ParameterSchedule.sScale_eq_pow Bs u,
    ParameterSchedule.qWrap_eq_two_pow Awrap LP, Qwidth_eq_two_pow bout δU⟩

/-- **`exp:E-01-overhead`: the three displayed forms agree, at the manuscript
schedule.**

`11-one-level-assembly.tex`, display lines 83--93.  The frozen chain is

```
H = a + r_2 + ceil(B_s u^2) + A_wrap L_P^2 + r_Q          (line 87)
  = a + clog_2(12 s |E|) + ceil(B_s u^2) + A_wrap L_P^2
      + clog_2(Q_0)                                        (lines 88--89)
  = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q,           (line 90)
```

and this theorem is exactly that chain, read in the direction the level
consumes it: the `M8` protocol cost at the four scheduled widths (first
conjunct's left-hand side) equals `H` at its defining displays
(`scheduleOverhead`), which equals the banked exponent form
`OneLevelCompletion.levelOverhead` (second conjunct).

**The source scale is evaluated, not assigned.**  `s` enters `r_2` as
`ParameterSchedule.sScale B_s u`, i.e. through `eq:s-choice`, so the
dependency order `u -> s -> q_2` of `06:116--124` is respected rather than
short-circuited by a value for `s`.

`C_0` and `lA = log_2 A_*` are binders (GAP-EXPOSED 1); every other exponent is
computed.  No numeral is assigned to any quantity the source defines. -/
theorem overhead_three_displays {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : GuardedSourceGraph.EndpointGraph V E)
    (C0 lA Bs u Awrap LP bout : ℕ) (δU : ℝ) :
    selectorCostSum (C0 * lA ^ 2)
        (GuardedSourceSlab.q2 G (ParameterSchedule.sScale Bs u))
        (ParameterSchedule.sScale Bs u)
        (ParameterSchedule.qWrap Awrap LP)
        (Qwidth bout δU)
      = scheduleOverhead C0 lA (ParameterSchedule.sScale Bs u)
          (Fintype.card E) Bs u Awrap LP (rQ bout δU) ∧
    scheduleOverhead C0 lA (ParameterSchedule.sScale Bs u)
        (Fintype.card E) Bs u Awrap LP (rQ bout δU)
      = levelOverhead (C0 * lA ^ 2)
          (Nat.clog 2 (12 * ParameterSchedule.sScale Bs u * Fintype.card E))
          (Bs * u ^ 2) (Awrap * LP ^ 2) (rQ bout δU) := by
  have hcost : selectorCostSum (C0 * lA ^ 2)
      (GuardedSourceSlab.q2 G (ParameterSchedule.sScale Bs u))
      (ParameterSchedule.sScale Bs u)
      (ParameterSchedule.qWrap Awrap LP)
      (Qwidth bout δU)
      = levelOverhead (C0 * lA ^ 2)
          (Nat.clog 2 (12 * ParameterSchedule.sScale Bs u * Fintype.card E))
          (Bs * u ^ 2) (Awrap * LP ^ 2) (rQ bout δU) :=
    selectorCostSum_eq_levelOverhead _ _ _ _ _ rfl
      (ParameterSchedule.sScale_eq_pow Bs u)
      (ParameterSchedule.qWrap_eq_two_pow Awrap LP)
      (Qwidth_eq_two_pow bout δU)
  have hdisp : scheduleOverhead C0 lA (ParameterSchedule.sScale Bs u)
      (Fintype.card E) Bs u Awrap LP (rQ bout δU)
      = levelOverhead (C0 * lA ^ 2)
          (Nat.clog 2 (12 * ParameterSchedule.sScale Bs u * Fintype.card E))
          (Bs * u ^ 2) (Awrap * LP ^ 2) (rQ bout δU) := by
    unfold scheduleOverhead levelOverhead stage4Overhead
    omega
  exact ⟨hcost.trans hdisp.symm, hdisp⟩

/-! ## Part 3  The two least-power-of-two sandwiches (`11:76--81`) -/

/-- **`12 s |E| <= q_2 < 24 s |E|` and `Q_0 <= Q < 2 Q_0`** --
`11-one-level-assembly.tex:76--81`.

The frozen text states both sandwiches as consequences of "the two
least-power-of-two choices" of lines 68--75, and they are what keeps the
overshoot of each exponent below one bit.  Both are read off the banked
accessors: the `q_2` pair from `GuardedSourceSlab.card_le_q2` and `.q2_lt`, the
`Q` pair from `EntryGates.Q0_le_Qwidth` and `.two_pow_pred_lt_Q0`.  Nothing is
re-proved.

`hs : 3 < s` is the frozen source-scale floor -- the guarded source fixes a
power of two `s >= 4` (navigation: reader `03-parameterized-construction.tex`
lines 13--14), and the schedule's own chain derives `s >= 512` in
`ParameterSchedule.sScale_floor`; it is the side
condition the banked `q2_lt` states, carried verbatim.  General in the graph,
the scale, `b_out` and `delta_U`. -/
theorem width_sandwiches {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : GuardedSourceGraph.EndpointGraph V E) {sVal : ℕ}
    (hs : 3 < sVal) (bout : ℕ) (δU : ℝ) :
    12 * sVal * Fintype.card E ≤ GuardedSourceSlab.q2 G sVal ∧
      GuardedSourceSlab.q2 G sVal < 24 * sVal * Fintype.card E ∧
      Q0 bout δU ≤ ((Qwidth bout δU : ℕ) : ℝ) ∧
      ((Qwidth bout δU : ℕ) : ℝ) < 2 * Q0 bout δU :=
  ⟨GuardedSourceSlab.card_le_q2 G sVal, GuardedSourceSlab.q2_lt G (by omega),
    Q0_le_Qwidth bout δU, two_pow_pred_lt_Q0 bout δU⟩

/-- **The sandwiches at the evaluated source scale.**

The same statement with `s` obtained by evaluating `eq:s-choice` rather than
assumed: `u = clog_2(clog_2(A_pre + 16))` (`06:116--117`) and
`s = 2^{ceil(B_s u^2)}` (`06:118`), so the
floor `3 < s` is *derived* from `ParameterSchedule.sScale_floor` at the frozen
positivity `1 <= B_s` (`06:56`) and the derived `3 <= u`
(`ParameterSchedule.three_le_uAux`), never assumed.  This is the dependency
order `A_pre -> u -> s` of `06:109--121`.  General in every free input. -/
theorem width_sandwiches_at_evaluated_scale {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : GuardedSourceGraph.EndpointGraph V E) {Bs : ℕ} (hBs : 1 ≤ Bs)
    (bout Bpub zR clE : ℕ) (δU : ℝ) :
    12 * ParameterSchedule.sScale Bs
          (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE))
        * Fintype.card E
      ≤ GuardedSourceSlab.q2 G (ParameterSchedule.sScale Bs
          (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE))) ∧
    GuardedSourceSlab.q2 G (ParameterSchedule.sScale Bs
        (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE)))
      < 24 * ParameterSchedule.sScale Bs
          (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE))
        * Fintype.card E ∧
    Q0 bout δU ≤ ((Qwidth bout δU : ℕ) : ℝ) ∧
    ((Qwidth bout δU : ℕ) : ℝ) < 2 * Q0 bout δU := by
  have hu : 3 ≤ ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE) :=
    ParameterSchedule.three_le_uAux bout Bpub zR clE
  have hfloor := (ParameterSchedule.sScale_floor hBs hu).1
  exact width_sandwiches G hfloor bout δU

/-! ## Part 4  The reader-claimed item: the inner selector in both promise
cases -/

/-- **The inner interlace adds exactly `r_q = log_2 q` selector bits in both
promise cases.**

*Reader counterpart:* `03-parameterized-construction.tex:617--619`, "The
interlace `W = Int_q(N)^T` aligns their row thresholds and adds exactly
`r_q = log q` selector bits in both promise cases".  This is the one reader
item this module claims, and it is claimed by this declaration alone.

*Autoformalization loci:* `11-one-level-assembly.tex` `step:L-10` lines
624--627 (the `q`-selector costs `r = log_2 q` bits) and `step:L-13` lines
795--798 ("Because both widths are powers of two, their costs are exactly
`log_2 q` and `log_2 Q`"); `09-first-wrapper.tex:1794`.

Three conjuncts, which together are the reader sentence:

1. the width's protocol cost is exactly `w_q` -- the banked
   `OneLevelCompletion.alignedSelectorCost_exact` at
   `ScaleAlignOpening.scaleAlignWidth`, consumed by pin;
2. the `YES` budget of `step:L-13` moves by exactly `w_q`;
3. the `NO` budget of `step:L-12` moves by exactly `w_q`, with its `+1` gap
   untouched -- "in both promise cases", and by the *same* integer.

The comparison point `levelOverhead a w_2 w_s 0 w_Q` is the same level with the
inner selector absent.  It is a **comparison term only**: `w_q = 0` is the
frozen-illegal width `q = 1` of `02-mechanical-contract.tex:771--775`, and
nothing here asserts that it is a legal instantiation.  General in the two
budgets and all four exponents. -/
theorem innerSelector_adds_exactly_rq (Dsrc Ysrc a w2 ws wq wQ : ℕ) :
    Nat.clog 2 (ScaleAlignOpening.scaleAlignWidth wq) = wq ∧
      Ysrc + levelOverhead a w2 ws wq wQ
        = (Ysrc + levelOverhead a w2 ws 0 wQ) + wq ∧
      Dsrc + levelOverhead a w2 ws wq wQ + 1
        = (Dsrc + levelOverhead a w2 ws 0 wQ + 1) + wq := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ScaleAlignOpening.scaleAlignWidth_def]
    exact alignedSelectorCost_exact wq
  · unfold levelOverhead stage4Overhead
    omega
  · unfold levelOverhead stage4Overhead
    omega

/-! ## Part 5  The double interlace, joined to the Section-10 hub

`step:L-01` lines 22--29 build `R+` from `N` by two interlaces at two different
widths.  The Lean composite already exists in two places under two names, and
the first theorem below states in the kernel that they are one term; the
headline then delivers the Section-11 carrier equations and the Section-10
complexity **about that single term**. -/

/-- **The two names of `R+` are one term.**

`ScaleAlignOpening.wrapperW N r` (`09:268`, `W = transpose U` at the inner
width `q = 2^r`) is `OneLevelCompletion.alignedMatrix N r`, and applying the
outer bridge to it is `OneLevelCompletion.levelOutput N r b_out delta_U`
(`10:63`, `R+ = transpose (Int_Q W)`).  So the object
`DirectOutputFromOpening.directOutput_at_the_paper_instance` speaks about and
the object `OneLevelAssembly.oneLevelAssembly_carriers` speaks about are the
same, and the join below is a checked identification rather than a resemblance
argument.  General in the carriers, `N`, `r`, `b_out` and `delta_U`. -/
theorem levelOutput_eq_bridge_of_wrapperW {Rw Cl : Type*}
    (Nmat : Rw → Cl → Bool) (r bout : ℕ) (δU : ℝ) :
    levelOutput Nmat r bout δU
      = EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r) (Qwidth bout δU) :=
  rfl

/-- **The composed carrier equations, at two exponents and no numerals.**

`11-one-level-assembly.tex`, `step:L-14` lines 858--864:

```
m_next = |Rows(R+)| = (q m_N)^Q,      n_next = |Cols(R+)| = Q n_N^q,
```

at `q = 2^r` (`11:16`) and `Q = Qwidth b_out delta_U = 2^{r_Q}` (`10:51`),
stated on the *bridge* spelling of `R+` so that it can be conjoined with the
Section-10 conclusions in the headline below.  Purely the banked
`OneLevelAssembly.oneLevelAssembly_carriers` transported along
`levelOutput_eq_bridge_of_wrapperW`; nothing is re-proved.

`hq : 1 <= r` is the frozen legality guard `q = 2^r >= 2` of
`02-mechanical-contract.tex:771--775`.  It is a **lower** bound on the inner
width and never an upper one.  General in the carriers, `N`, `b_out` and
`delta_U`. -/
theorem bridgeCarriers_of_wrapperW {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r bout : ℕ) (δU : ℝ) (hq : 1 ≤ r) :
    rowsCard (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
        (Qwidth bout δU))
        = (2 ^ r * rowsCard Nmat) ^ Qwidth bout δU ∧
      colsCard (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
        (Qwidth bout δU))
        = Qwidth bout δU * colsCard Nmat ^ 2 ^ r := by
  obtain ⟨-, -, hrow, hcol⟩ :=
    OneLevelAssembly.oneLevelAssembly_carriers Nmat r bout δU hq
  rw [levelOutput_eq_bridge_of_wrapperW] at hrow hcol
  exact ⟨hrow, hcol⟩

/-- **The double-interlace recurrence at the paper's own entry object.**

`11-one-level-assembly.tex`, `step:L-01` (lines 22--29) composed with
`step:L-11` (`exp:E-11-exact`, label line 763) and `step:L-14` (lines
858--864), on one term.

Hypotheses are **exactly** those of the Section-10 hub
`DirectOutputFromOpening.directOutput_at_the_paper_instance`, carried verbatim
and in its binder order, plus the frozen inner-width legality `hq : 1 <= r`
(`q = 2^r >= 2`, `02-mechanical-contract.tex:771--775`) that the carrier clause
needs.

Conclusions, on the single term `R+ = Rnext (wrapperW N r) Q`:

1. `comp R+ = C + r + r_Q` -- the per-level selector accumulation as an
   *equation*: the Section-4 exact value `C`, plus the inner selector `r`,
   plus the outer selector `r_Q`;
2. `Lambda_3(R+, 1, 2^{-b_out}, 3/5) >= C + r + r_Q` -- the regenerated
   robustness certificate at the **same** integer, which is the frozen
   discipline of line 784, "the equality and the robustness lower bound use the
   same integer";
3. `ceil(log_2 Q) = r_Q` -- the outer selector's cost, as an equation and never
   an inequality (`10:74`);
4. `|Rows(R+)| = (q m_N)^Q` and `|Cols(R+)| = Q n_N^q` at `q = 2^r`.

**Both widths occur and neither is a numeral.**  `r` is a binder fixed by the
frozen schedule; `r_Q` is the banked accessor `EntryGates.rQ` at `b_out` and
`delta_U`.  The row branch exponentiates by `Q` and multiplies by `q`, the
column branch does the reverse; `selectorAccumulation_symmetric_carriers_are_not`
below shows this orientation is not recoverable from the cost equation alone.

**Conditional, and registered as such.**  `hDense` is the named, undischarged
`FirstWrapperClose.DenseRung` (`eq:wrapper-u-dense`, `09:262--263`), and `hne`,
`hmem` are the low-rung inputs of `09:274--334`.  This is the module's canonical
instance -- it is the paper's own object, not a synthetic one -- and it is
delivered exactly as conditionally as its supplier delivers it.  Nothing here
weakens, discharges, or reorients that binder, and **no route completion is
claimed.** -/
theorem doubleInterlaceRecurrence {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C bout : ℕ) {δU θ : ℝ}
    (hq : 1 ≤ r) (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hbout : 1 ≤ bout)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hgates : directEntryGates bout δU θ (3 / 5))
    (hDense : FirstWrapperClose.DenseRung Nmat r C δU θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1
        (DirectBridgeOpening.yFixed / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1
        (DirectBridgeOpening.yFixed / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame
          (interlaceFun (ScaleAlignOpening.wrapperU Nmat r) 1) RC.1 RC.2)) :
    D (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r) (Qwidth bout δU))
        = C + r + rQ bout δU
      ∧ C + r + rQ bout δU
          ≤ LambdaGE (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
              (Qwidth bout δU)) 1 (xOut bout) (3 / 5)
      ∧ Nat.clog 2 (Qwidth bout δU) = rQ bout δU
      ∧ rowsCard (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
            (Qwidth bout δU))
          = (2 ^ r * rowsCard Nmat) ^ Qwidth bout δU
      ∧ colsCard (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
            (Qwidth bout δU))
          = Qwidth bout δU * colsCard Nmat ^ 2 ^ r := by
  obtain ⟨heq, hrob, hbits⟩ :=
    DirectOutputFromOpening.directOutput_at_the_paper_instance Nmat r C bout hC
      hN hθ0 hθ1 hδ0 hδ1 hbout hRw hCl hgates hDense hne hmem
  obtain ⟨hrow, hcol⟩ := bridgeCarriers_of_wrapperW Nmat r bout δU hq
  exact ⟨heq, hrob, hbits, hrow, hcol⟩

/-- **The `NO`-case budget, `comp R+ = D + H + 1`** --
`11-one-level-assembly.tex`, `step:L-12` lines 769--783.

The frozen substitution is
`comp R+ = C_W + r_Q = C + log_2 q + log_2 Q = D + H + 1`, with
`H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q`.  Here `C` is supplied as the
Stage-4 exact value `stage4Exact D a w_2 w_s = D + a + w_2 + w_s + 1`
(`10:507`, `08:149`) through the binder `hC4`, and the conclusion is stated at
the banked `OneLevelCompletion.levelOverhead`, so the accumulated integer of
Part 1 and the budget of `step:L-12` are the *same* integer by construction.

`hC4` is a binder, not a derivation: producing it from the promise certificates
through Stages 1--4 is `ONELEVEL-001` and `STAGE4-ALIGN-001` (GAP-EXPOSED 3).
No promise hypothesis occurs in this statement's conclusion, only in its
inputs. General in the four Stage-4 exponents. -/
theorem doubleInterlaceRecurrence_budget {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] {Nmat : Rw → Cl → Bool} {r C bout : ℕ} {δU : ℝ}
    (Dsrc a w2 ws : ℕ) (hC4 : C = stage4Exact Dsrc a w2 ws)
    (hexact : D (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r)
      (Qwidth bout δU)) = C + r + rQ bout δU) :
    D (EthBridge.Rnext (ScaleAlignOpening.wrapperW Nmat r) (Qwidth bout δU))
      = Dsrc + levelOverhead a w2 ws r (rQ bout δU) + 1 := by
  rw [hexact, hC4]
  unfold stage4Exact levelOverhead stage4Overhead
  omega

/-! ## Part 6  Statement poles

Three, and the first two are **already banked declarations**, cited by name
rather than restated (fixed-interface discipline; a local twin would be a
duplicate declaration and a stale-twin hazard):

* the **vacuous-conclusion pole** is
  `BridgeOutputEquality.directRobustification_conclusion_nontrivial`, which
  reads `comp R+ = C_W + r_Q >= 7` at every legal parameter from the frozen
  `C_W >= 3` (`10:40`) and the banked `EntryGates.four_le_rQ`.  It is stated at
  the same universally quantified symbols as this module's conclusion 1, so
  nothing would be added by repeating it;
* the **vacuous-hypothesis pole** is
  `DirectBridgeOpening.opening_rejects_the_wrapper_close_probe`, which refutes
  the bridge input at `FirstWrapperClose.probeW` whenever `3 <= C_W`, because
  `FirstWrapperClose.probeW_D` pins that NON-FIDELITY probe's complexity at
  exactly `2`.  It is stated general in `y`, so it applies verbatim at this
  module's binders.

The third is genuinely local: it is about the *new* integers of Part 0, and
there is nothing banked to cite. -/

/-- **Pole: the cost equation cannot recover the carrier orientation.**

Two conjuncts that pull in opposite directions.  The accumulated selector cost
is **symmetric** under exchanging the two interlace exponents -- addition does
not see which width is inner and which is outer -- while the row carrier is
**not**: at an arbitrary base matrix the two orders give
`(q m_N)^Q` and `(Q m_N)^q`, which differ.

So a transcription that conflated `q` with `Q`, or that swapped them, would
still satisfy every equation of Parts 1--2 and would be caught only by the
carrier clause of `doubleInterlaceRecurrence`.  This is why both widths are
carried separately throughout, and why the carrier clause is part of the
headline rather than a remark.

The second and third conjuncts are an explicitly labelled **BEYOND-PAPER
AUDIT** evaluation: `q = 2`, `Q = 4`, `m_N = 3` are self-chosen numbers at
which the frozen source never instantiates anything, used purely to separate
the two orders in the kernel.  They audit **our encoding**, claim no legality,
and are never evidence about the route's own widths. -/
theorem selectorAccumulation_symmetric_carriers_are_not :
    (∀ a q2 s r rQv : ℕ,
        selectorCostSum a q2 s (2 ^ r) (2 ^ rQv)
          = selectorCostSum a q2 s (2 ^ rQv) (2 ^ r)) ∧
      rowsCard (EthBridge.Rnext (EthBridge.Rnext
        (fun (_ : Fin 3) (_ : Fin 5) => true) 2) 4) = 1296 ∧
      rowsCard (EthBridge.Rnext (EthBridge.Rnext
        (fun (_ : Fin 3) (_ : Fin 5) => true) 4) 2) = 144 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a q2 s r rQv
    unfold selectorCostSum
    rw [DirectOutput.clog_two_pow, DirectOutput.clog_two_pow]
    omega
  · obtain ⟨hrow, -⟩ :=
      OneLevelAssembly.doubleInterlaceCarriers
        (fun (_ : Fin 3) (_ : Fin 5) => true) 2 4
    rw [hrow]
    simp [rowsCard]
  · obtain ⟨hrow, -⟩ :=
      OneLevelAssembly.doubleInterlaceCarriers
        (fun (_ : Fin 3) (_ : Fin 5) => true) 4 2
    rw [hrow]
    simp [rowsCard]

/-! ## Part 7  Non-vacuity

The canonical inhabitation of this module's headline is
`doubleInterlaceRecurrence` itself: it runs on the **paper's own** entry object
`W = transpose(U)` at `C_W = C + r`, and it is conditional exactly where its
supplier is (`DenseRung`).  The registered deferred obligation in the module
header is discharged when `DenseRung` is proved, never by anything below.

The two theorems here concern the *new* integers of Part 0, which are `Nat`
functions of public data and therefore have no inhabitation obligation of their
own.  They record that the accumulation is not degenerate. -/

/-- **Non-vacuity (i): the two wrapper selectors contribute strictly, at the
route's own outer exponent and with no numeral for either width.**

At the frozen legalities `q = 2^r >= 2` (`hq : 1 <= r`,
`02-mechanical-contract.tex:771--775`) and the banked `EntryGates.four_le_rQ`
(`r_Q >= 4`, from `Q_0 >= 16` at `10:51`), the level overhead exceeds the
Stage-4 overhead `K = a + log_2 q_2 + log_2 s` by at least five bits.  So the
double interlace is a strict addition to the budget and `H` is not `K` in
disguise -- a statement that fails for the frozen-illegal `q = 1`, `Q = 1`, and
therefore is not a tautology of the definition.

`r` stays a binder and `r_Q` is evaluated through `EntryGates.rQ`; no numeral
is assigned to either width. -/
theorem levelOverhead_strictly_exceeds_stage4 (a w2 ws r bout : ℕ) (δU : ℝ)
    (hq : 1 ≤ r) :
    stage4Overhead a w2 ws + 5 ≤ levelOverhead a w2 ws r (rQ bout δU) := by
  have h4 := four_le_rQ bout δU
  unfold levelOverhead
  omega

/-- **Non-vacuity (ii): the three displays fire at the paper's own scheduled
point, with no numeral assigned to any defined quantity.**

Every width is obtained by evaluating its own defining chain -- `A_pre -> u ->
s` (`eq:s-choice`, `06:109--121`), `s -> q_2` (`06:124`), `A_wrap, L_P -> q`
(`eq:q-deltaU`, `06:515`), `Q_0 -> r_Q -> Q` (`10:43--51`) -- and the only free
inputs are the ones `06:4--8` names as the universal configuration and the
source graph: `C_0`, `log_2 A_*`, `B_s`, `A_wrap`, `L_P`, the public bounds
`B_pub`, `z_R`, `clE`, the requested depth `b_out`, the tolerance `delta_U`,
and `G` itself.  All stay universally quantified.

The conclusion returns, additionally, the derived source-scale floor `3 < s`
and the outer exponent bound `4 <= r_Q`, so that the legality of the evaluated
point is visible rather than merely internal.  This is a **parameter** witness,
not an inhabitation: no matrix and no promise certificate occurs. -/
theorem overhead_fires_at_the_scheduled_point {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : GuardedSourceGraph.EndpointGraph V E) (C0 lA Awrap LP : ℕ) {Bs : ℕ}
    (hBs : 1 ≤ Bs) (bout Bpub zR clE : ℕ) (δU : ℝ) :
    3 < ParameterSchedule.sScale Bs
        (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE)) ∧
      4 ≤ rQ bout δU ∧
      selectorCostSum (C0 * lA ^ 2)
          (GuardedSourceSlab.q2 G (ParameterSchedule.sScale Bs
            (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE))))
          (ParameterSchedule.sScale Bs
            (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE)))
          (ParameterSchedule.qWrap Awrap LP)
          (Qwidth bout δU)
        = levelOverhead (C0 * lA ^ 2)
            (Nat.clog 2 (12 * ParameterSchedule.sScale Bs
              (ParameterSchedule.uAux
                (ParameterSchedule.Apre bout Bpub zR clE))
              * Fintype.card E))
            (Bs * ParameterSchedule.uAux
              (ParameterSchedule.Apre bout Bpub zR clE) ^ 2)
            (Awrap * LP ^ 2) (rQ bout δU) := by
  have hu : 3 ≤ ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE) :=
    ParameterSchedule.three_le_uAux bout Bpub zR clE
  refine ⟨(ParameterSchedule.sScale_floor hBs hu).1, four_le_rQ bout δU, ?_⟩
  obtain ⟨h1, h2⟩ :=
    overhead_three_displays G C0 lA Bs
      (ParameterSchedule.uAux (ParameterSchedule.Apre bout Bpub zR clE))
      Awrap LP bout δU
  exact h1.trans h2

/-- **Non-vacuity (iii): the carrier recurrence and the accumulation move
together at two distinct widths.**

A BEYOND-PAPER AUDIT evaluation, labelled as such: the exponents `r = 2` and
`r_Q = 4` are self-chosen, the frozen source instantiates neither, and the
instance claims **no** legality beyond the two frozen lower bounds it displays.
Its purpose is a consistency check on Part 0 and Part 5 together -- the level
overhead, the row carrier and the column carrier all move when the two
exponents move, which a definition satisfiable at a single arithmetic could
not do.

It is strictly weaker evidence than `doubleInterlaceRecurrence`, which is the
paper's own instance, and is never a substitute for it. -/
theorem recurrence_and_accumulation_move_together (a w2 ws : ℕ) :
    levelOverhead a w2 ws 2 4 = stage4Overhead a w2 ws + 6 ∧
      levelOverhead a w2 ws 4 2 = stage4Overhead a w2 ws + 6 ∧
      rowsCard (EthBridge.Rnext (EthBridge.Rnext
        (fun (_ : Fin 3) (_ : Fin 5) => true) (2 ^ 2)) (2 ^ 4)) = 12 ^ 16 ∧
      colsCard (EthBridge.Rnext (EthBridge.Rnext
        (fun (_ : Fin 3) (_ : Fin 5) => true) (2 ^ 2)) (2 ^ 4))
          = 16 * 5 ^ 4 := by
  refine ⟨by unfold levelOverhead; omega, by unfold levelOverhead; omega, ?_, ?_⟩
  · obtain ⟨hrow, -⟩ :=
      OneLevelAssembly.doubleInterlaceCarriers
        (fun (_ : Fin 3) (_ : Fin 5) => true) (2 ^ 2) (2 ^ 4)
    rw [hrow]
    simp [rowsCard]
  · obtain ⟨-, hcol⟩ :=
      OneLevelAssembly.doubleInterlaceCarriers
        (fun (_ : Fin 3) (_ : Fin 5) => true) (2 ^ 2) (2 ^ 4)
    rw [hcol]
    simp [colsCard]

end EthInapproximability.ParameterizedNP.DoubleInterlaceRecurrence
