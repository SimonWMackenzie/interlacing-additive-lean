import EthInapproximability.ParameterizedNP.IterationAssembly
import EthInapproximability.ParameterizedNP.FiniteSlots

/-!
# Parameterized NP route: the size thread

`exp:E-14-raw`, `step:I-07`, and `thm:effective-parameter-schedule`.

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`SIZE-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 127),
whose exact double-interlace recurrence was landed by the `cc-t1r` tranche and
whose remaining half -- named there as "**Not landed:** `exp:E-14-raw` (the
uniform majorant), `step:I-07`'s size thread with its `C_dim` driver, and
`thm:effective-parameter-schedule`" -- is what this `cc-t1s` tranche opens.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Repair round `cc-t1s-r1`

The first round of this module was **parked** at the statement gate
(`wip/cc-t1s-size-propagation`), not banked: `ArrowSize.q1` was a free width,
so the module's one new structure had no inhabitant inside the frozen
admissible region, and pole 1 fired at an arrow violating `4 t_2 <= q_2`.  This
round repairs exactly the flagged surface and carries everything else forward
with **byte-identical closed statements**.

*Exact inventory, recomputed by declaration-level diff against `83f4dda`.*  The
parked round had **57** declarations, of which the statement gate marked **42**
`CLEAR` and **15** `REVISE`.  Nine closed statements changed here -- `ArrowSize`,
`uniformSideMajorant_hypothesis_not_free`, `dimMultiplicity_is_not_additive`,
`sizeDriver_fires_nondegenerate`, `rawSideMajorant_fires_nondegenerate`,
`arrowSize_fires_at_banked_entry_parameters`, `arrowSizeStep_fires`,
`witnessArrow` and `iteratedSizeMajorant_fires_growing` -- every one of them a
declaration the gate marked `REVISE`.  So **all 42 gate-cleared declarations are
byte-identical**, and so are six of the fifteen flagged ones: the five
`ArrowSize` accessors `sVal`, `t2Val`, `driver`, `rawMajorant`, `stepBound`
(unchanged because `q1` stayed a projection of the record) and the ladder
`witnessZ`.  **48** of the 57 are therefore carried verbatim.  The repair:

* `ArrowSize` gains the frozen Stage-1 guard and derives `q_1` from the banked
  `FiniteSlots.Stage1SlotBinding` (aux 17--19 below are the new general
  properties this buys);
* pole 1 and the five arrow-shaped witnesses are re-instantiated at
  `minimalLegalArrow` / `witnessArrow`, whose numerals were recomputed from the
  module's own definitions rather than inherited;
* every blanket "every field is legal" docstring is replaced by an explicit
  list of the displays actually discharged, and the candidate-versus-realized
  distinction is stated wherever a witness could be mistaken for a realized
  arrow.

**Deviation from the gate's suggested numerals, recorded deliberately.**  The
statement gate proposed repairing at `<w_q=3, r_Q=13, log_2 q_2=3, log_2 s=2,
log_2 t_2=1, q_1=6>`.  That tuple has `t_2 = 2 < 48 = 8 q_1`, violating the
**first** row of `eq:stage2-structural-gates` -- the same display whose second
row the gate's own finding enforced.  The frozen paper wins: the minimal tuple
clearing both evaluable rows at `q_1 = 6` is `log_2 t_2 = 6` and
`log_2 q_2 = 8`, which is what is landed, and every numeral downstream of it
(`105`, `1680`, `13787136`, and the ladder `0 < 13456 < 22606096`) was
recomputed at that tuple.

## What this module lands

* **`exp:E-14-raw`** (`11-one-level-assembly.tex`, label line 850, display lines
  846--851): the uniform comparison
  `z_N <= zbar_N = C_dim (t_2 + s(q_1 + s) + 1) Z_N`.  The frozen text states at
  lines 852--855 that this inequality "is not inferred from the big-`O` display"
  and that `thm:eff-ledger` "prints a size-successor row with a numerical integer
  `C_dim`, the seven multiplicity contributions, and a checked derivation".  It
  is therefore carried as a **named hypothesis** on the checked row, never as a
  Lean derivation, and `uniformSideMajorant_hypothesis_not_free` exhibits legal
  values at which it fails, so it is a genuine premise.
* **The `Z_N` driver** of `step:L-14` (`11-one-level-assembly.tex:812--819`)
  and `step:I-07` (`13-iteration-assembly.tex:529--537`), as `sizeDriver`:
  the literal seven-entry maximum
  `max{1, z, floor log_2(n+2), log_2 q_2, floor log_2 q_1, log_2 s, log_2 t_2}`,
  with the three power-of-two widths carried by their **exponents** (frozen line
  820, "The logarithms of `q_2, s, t_2` are integers because these widths are
  powers of two") and the two genuine floors kept as `Nat.log`.
* **`C_dim`** as the literal maximum of `eq:Cdim-literal-producer`
  (`06-parameter-schedule.tex`, label line 2199, display lines 2195--2200),
  "a literal maximum over nineteen named, computed rows", with the multiplicity
  polynomial `P_dim = (t_2 + s(q_1 + s) + 1) Z` of lines 2188--2191.
* **`C_size`** as the literal maximum of `eq:Csize-literal-producer`
  (`06-parameter-schedule.tex`, label line 1624, display lines 1611--1625).  The
  frozen line 1688 is load-bearing and is obeyed literally: "Equation
  `eq:Csize-literal-producer`, **rather than the four-row degree summary**,
  produces `C_size >= 2`."  Accordingly the four-row degree table of lines
  1643--1656 appears nowhere below, the two passes are kept **separate** (the C7
  roots and nine `T1`--`T2` factors carry the `3^{d_u}` absorption at driver
  `L+2`; the seven `T3` factors carry **no** shift, at driver `A_*`, lines
  1634--1637), and two kernel poles -- `degreeSummary_does_not_determine_csize`
  and `t3Pass_carries_no_shift_pole` -- refute the two readings a green build
  cannot see.
* **`step:I-07`, the iterated size majorant** (`13-iteration-assembly.tex`, label
  line 516, body lines 519--571) together with its `readingwarning` "Use of the
  size-successor row" (lines 558--571): the per-arrow driver `Z_{i,N}`, the raw
  majorant `z_{N,i}`, the step `z_{i+1}^+`, and the induction
  `z_i <= E_{c_i}(n) <= E_{c_k}(n)` for `0 <= i <= k`.  The successor row itself
  is a **named hypothesis** (it is `thm:eff-ledger` output, `PARAM-001`).
* **`thm:effective-parameter-schedule`** (`06-parameter-schedule.tex`, label line
  1975, statement lines 1977--2081): the simultaneous eligibility of every
  earlier cutoff, the frozen successor exponent `c_{i+1} = 16(c_i + 1)`, the
  `AuxOut` set identity of lines 2043--2058 ("Define, **without adding a new
  root**, `AuxOut(Cert_{c_i}) = Roots(Successor_{c_i}) \ {ceil log_2 m_next,
  ceil log_2 n_next, D+H+1, Y+H}`" together with "It contains neither raw `q_2`
  nor raw `N_2`, source carrier sizes, incoming carrier sizes, or physical
  carrier cardinalities"), the transport of the rootwise `Successor_16` bound to
  the four principal rows and to every auxiliary root, and the envelope
  persistence `E_{c_i}(n) <= E_{c_{i+1}}(n)`.  The separate numerical source
  width row of lines 2071--2076 is `sourceWidthRow`, with its pole.
* The **`M = C_exc^0 + B_exc^0 + c_seed + 8` nonemptiness calculation** of
  `13-iteration-assembly.tex:69--84`, repaired under `AUDIT-007` and banked as
  `IterationAssembly.awrap_search_nonempty`, is **consumed, not re-proved**:
  `scheduleCoefficientInputs` re-reads it at the two literal maxima of
  `eq:Cexc0-literal-producer` and threads its margin `A_wrap >= C_exc + 4` into
  this module's constant inventory.  Both maxima stay separate binders
  throughout; no unit-slope restatement occurs anywhere below.

## Reader counterparts

`.../reader-facing/sections/05-iteration.tex` of the same frozen release was
opened first-hand this tranche and every cited item read to confirm it states the
same fact.  Reader lines are partitioned so that **no reader item is assigned to
two declarations**, and none of the items below is claimed by `ITER-001`,
`ONELEVEL-001` or any earlier row:

* `eq:paper-log-carrier-recurrence` (label line 174, display lines 168--175),
  `z(R_{i+1}) <= max{Q_i(log q_i + z_{N,i}), log Q_i + q_i z_{N,i}}` -- to
  `arrowSizeStep`;
* `eq:paper-fixed-level-growth` (label line 289, display lines 286--290),
  `z(R_j) <= E_{c_j}(n) <= E_{c_k}(n)` for `0 <= j <= k` -- to
  `iteratedSizeMajorant`;
* `thm:paper-effective-level`'s displayed successor bound, lines 221--226
  (`z(N), q, Q, z(R^+), D^+, Y^+ <= E_{F(c)}(n)`, together with "The logarithmic
  cardinality of every internal carrier and indexed family, and the binary length
  of every descriptor, is also at most `E_{F(c)}(n)`") -- to
  `effectiveParameterSchedule`.  `ITER-001` names lines 216--235 as a navigation
  locus only and claims no counterpart there, and `cumulativeThreshold` claims
  only lines 202--203 (`F(c) = 16(c+1)`), so this display is unassigned;
* line 178 alone, "the numerical source width `q_{2,i}` enters this logarithmic
  carrier bound only through `log q_{2,i}`" -- to `sourceWidthRow`.  Line 176's
  `n^{o(1)}` clause is **not** claimed by anything here.

**No reader counterpart exists for `C_dim`, `Z_N`, `C_size` or `W(L)`.**  A
search of all nine reader section files for `C_{\mathrm{dim}}`,
`C_{\mathrm{size}}`, `Z_{\mathbb N}` and `\mathrm{exc}` returns nothing; the
reader artifact never names the producers.  Accordingly `sizeDriver`,
`cdimLiteral`, `csizeLiteral`, `structuralW`, `uniformSideMajorant` and
`literalProducers` claim **no** reader item and are reported as
autoformalization-only content rather than matched to reader prose.

**The repair round adds no reader assignment.**  `ArrowSize`'s Stage-1 guard,
the banked-binding aux lemmas `six_le_q1` / `log_q1` / `log_q1_lt_clog_q1`, the
pinned `minimalLegalArrow` with its evaluation lemmas, and the witnesses
`sizeDriver_fires_at_realized_t2_scale` and `sourceWidthRow_fires` take their
statements from `eq:stage1-scales`, `eq:stage2-structural-gates` and
`eq:t2-search` in the autoformalization source.  The reader artifact does print
analogues of the first two -- `q_1 := 2^a - 2` at
`reader-facing/sections/03-parameterized-construction.tex:142` and
`4 t_2 <= q_2` with `q_2, t_2` powers of two at `:72--73` -- but that section is
the reader's Stage-1--Stage-4 construction, which belongs to `STAGE1-001` ..
`WRAP-001` and not to this row, and none of the declarations here claims a line
of it.  Every reader item this module claims is in `05-iteration.tex`, and the
partition above is unchanged by the repair.

**One deliberate reader/paper divergence, resolved in favour of the paper.**
The reader's own theorem `thm:parameterized-one-bit` chooses "an integer
`a >= 6`" (`03-parameterized-construction.tex:59`), while the autoformalization
fixes `a >= 3` -- `07-one-level-construction.tex:118`, and again at
`10-direct-bridge.tex:261`, `11-one-level-assembly.tex:148` and
`13-iteration-assembly.tex:734, 769`.  The guard field of `ArrowSize` is the
paper's `3 <= a`, per the full-paper mandate; it is the weaker of the two, so
every reader-legal `a` is also legal here, and `sizeDriver_fires_nondegenerate`
exercises `a = 6` as well as the boundary `a = 3`.

Crosswalk row: `READER_CROSSWALK.md` row 13 ("Mechanical iteration and size
propagation").

## Dependencies, imports, external adapters

* Imports `IterationAssembly.lean` and `FiniteSlots.lean`, hence transitively
  `OneLevelAssembly`,
  `OneLevelCompletion`, `DirectOutputEqualityClose`, `BridgeOutputEquality`,
  `EntryAssembly`, `DefectDischarge`, `CopyRestriction`, `DirectOutputLower`,
  `DirectOutput`, `EntryGates`, `ThreeCopyRowStep`, `TwoCopyLadder`,
  `DefectInduction`, `InheritedContracts`, `PilotStage3` and
  `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not**
  imported, so the cited AGHP balanced-family axiom stays outside this module's
  closure.  There is no contact with `EXPANDER-001`, which by design has no Lean
  declaration; nothing below turns a cited external interface into an axiom.
* Consumed, never edited, widened or re-proved (names grep-verified against the
  banked sources before use):
  * `OneLevelAssembly.sideExponent`, `.sideStep`, `.sideExponent_bounds`,
    `.sideStep_bounds`, `.rowBranch_bound`, `.colBranch_bound`,
    `.levelOutputOfCase`, `.levelOutput_promise_free`, `.promiseCase_ne`,
    `.promiseFreedom_not_automatic`, `.PromiseCase`;
  * `OneLevelCompletion.levelOutput`, `.pinnedOutput_carriers`,
    `.pinnedOutput_carriers_invariant` -- the pinned-output carrier invariant;
  * `IterationAssembly.literalMax`, `.le_literalMax`, `.one_le_literalMax`,
    `.cexp`, `.cexp_ge_three_and_lt`, `.nval`, `.cumulativeThreshold`,
    `.ellN`, `.ellN_exists`, `.envE`, `.envelope_fires_nondegenerate`,
    `.awrap`, `.cexcOf`, `.cexcZero`, `.bexcZero`, `.coefficientPass_awrap`,
    `.AwrapAdmissible`;
  * `EntryGates.rQ`, `.Qwidth`, `.Qwidth_eq_two_pow`, `.four_le_rQ`,
    `.directEntryGates_fires`;
  * `BridgeOutputEquality.rowsCard`, `.colsCard`;
  * `FiniteSlots.Stage1SlotBinding` with its two guard fields `three_le_a` and
    `s_pos`, its derived width `q₁ = 2^a - 2` and its derived floor
    `six_le_q₁`.  The Stage-1 legality of every arrow below is **that** banked
    structure, built and consumed; `six_le_q₁` is never restated.
* External theorem adapters: **none new**.
* Proof status: **new (elementary)** throughout -- `Nat` induction,
  `Nat.log`/`Nat.clog` comparisons, list folds, and applications of the banked
  route facades.
* Axiom surface (Appendix D; `#print axioms` in `tools/AxiomAudit.lean`): at most
  `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings (k = 2) and the ranking

The genuinely open choice is **how the per-arrow size data of `step:I-07` is
represented**, since each arrow contributes six public numbers to one driver and
two more to the wrapper step.

**Candidate A (landed) -- an exponent-carrying public record `ArrowSize`.**  The
five power-of-two widths `q, Q, q_2, s, t_2` are carried by their **exponents**
`w_q, r_Q, log_2 q_2, log_2 s, log_2 t_2`, while `q_1` -- the one width the
frozen driver reads through a genuine floor logarithm, and the one width that is
*not* a power of two -- is the **derived** `q_1 = 2^a - 2` of `eq:stage1-scales`
(`06-parameter-schedule.tex`, label line 319).  The record therefore carries the
compiler-fixed Stage-1 exponent `a` with its frozen guard `3 <= a`
(`07-one-level-construction.tex:118`) and reads `q_1` off the banked
`FiniteSlots.Stage1SlotBinding`, so `ArrowSize.q1` is a projection of that
banked structure rather than a free width.  Six data fields and one legality
guard; no complexity, robustness, promise or envelope field, so
no constructor can carry a conclusion (mechanical rules M1, M2, M4).  The derived
`q1`, `sVal`, `t2Val`, `driver`, `rawMajorant` and `stepBound` are transparent
functions, not fields, so no field restates a derived telescope.

**Candidate B (refuted) -- a record carrying the widths `q` and `Q` raw,** with
the step spelled `max{Q(log_2 q + z_N), log_2 Q + q z_N}` using `Nat.log`.  This
is the spelling the frozen displays *look* like when the power-of-two side
condition is dropped.  It is refuted in the kernel by
`rawWidthEncoding_breaks_the_row_branch`: at the legal-looking `q = 3`, `Q = 1`,
`m_N = n_N = 1`, `z_N = 0` the frozen carrier equation gives
`|Rows(R^+)| = (q m_N)^Q = 3`, while the candidate's own step returns `1`, so
`3 <= 2^1` fails.  A floor logarithm of a non-dyadic width is strictly smaller
than the ceiling the estimate needs; the exponent encoding cannot express that
error at all.

Aux battery: A = 19/19 below.  B cannot state aux 6 (`sideStep` monotonicity is
banked at exponents), cannot state aux 18--19 at all (they are about the guarded
Stage-1 width `q_1 = 2^a - 2`, which B would carry as an exponent), and **fails**
the row-branch property outright, which is the
disqualifying unprovable lemma.  Faithfulness: A keeps `q` and `Q` in separate
fields with the frozen orientation (`sideStep_orientation_pole` refutes the
transposed reading) and keeps `q_2`, `s`, `t_2` logarithmic exactly as
`11-one-level-assembly.tex:886--888` demands.  Length: A is shorter at every use
site.  **A is landed; B survives only as its own refutation.**

## GAP-EXPOSED

1. **No route completion is claimed.**  Every size statement below is about a
   *supplied* matrix or a *supplied* numeric ladder.  The Stage-1 to Stage-4
   chain that would produce those inputs is not in Lean (`STAGE1-001` ..
   `WRAP-001`), and `thm:effective-materialization` (`MATERIALIZE-001`) --
   which the frozen theorem explicitly defers to at lines 2078--2081, "The
   required `Pi`, `c_2`, and `T` for every admitted source output are constructed
   separately" -- is not formalized.
2. **`thm:eff-ledger` is not formalized.**  `NumChecked`, `Successor_16`,
   `Cert_c`, `CoeffPass`, `SchemaChecked` and the expression-graph traversal are
   `PARAM-001` work.  Here the certificate output enters as **named hypotheses**:
   the checked size-successor row of `exp:E-14-raw`, the rootwise successor bound
   of `thm:effective-parameter-schedule`, and the recorded coefficient tables
   feeding `cdimLiteral` / `csizeLiteral`.  No such predicate is introduced as an
   axiom or as an opaque certificate.
3. **`lem:canonical-reindexing-invariance` is still not formalized**
   (`ITER-001` GAP-EXPOSED 2).  `step:I-07`'s sentence "Canonical reindexing
   preserves both carrier cardinalities, so the next public matrix also satisfies
   `z_{i+1} <= z_{i+1}^+`" is therefore the *hypothesis* `hcarry` of
   `iteratedSizeMajorant`, not a derived transport.
4. **The producers are consumed at an arbitrary recorded table.**  `cdimLiteral`
   and `csizeLiteral` are the two literal maxima of
   `eq:Cdim-literal-producer` and `eq:Csize-literal-producer` **as maxima**; the
   nineteen dimension rows, the sixteen tail factors, the C7 root list, the
   `CoeffRules` binary-length rewrite table and the reduced source-template row
   of lines 1587--1600 are not transcribed.  That traversal is `PARAM-001`.
5. **`step:I-08` .. `step:I-12` remain out of scope.**  The padding-threshold
   search, the slow clock (`CLOCK-001`), the seed and prefix-maximum bounds
   (`SEED-001`, including `eq:uniform-size-majorant`'s `zhat` and `g`), the
   common padding and the common truth-table exponent are named here only as the
   consumers of what is landed.  In particular **no `o(n)` statement is made**.

## The legal parameter region, and exactly what the witnesses discharge

Every arrow-shaped witness below sits at

```
w_q = 3 or 1,  r_Q = 13 or 4,  log_2 q_2 = 8,  log_2 s = 2,
log_2 t_2 = 6,  a = 3  (hence q_1 = 2^3 - 2 = 6),
```

which is the **smallest** tuple satisfying every frozen condition the six-field
record can evaluate:

* `q_1 = 2^a - 2` with `a >= 3` -- `07-one-level-construction.tex:118`
  ("The parameter compiler has fixed `a >= 3`; put `q_1 = 2^a - 2`") and
  `eq:stage1-scales` (`06-parameter-schedule.tex`, label line 319).  This is a
  *field-level* guard, so it is discharged by the record itself and not by any
  witness.
* `t_2 >= 8 q_1` -- the **first** row of `eq:stage2-structural-gates`
  (`06-parameter-schedule.tex`, label line 848): `64 >= 48`.
* `4 t_2 <= q_2` -- the **second** row of the same display: `4 * 64 = 256 <= 256`.
* `s >= 4` and `s` a power of two -- `04-guarded-source.tex:281` and
  `04-guarded-source.tex:389` ("Let `s >= 4` be a power of two"):
  `s = 2^2 = 4`.
* `q >= 2`, i.e. `1 <= w_q` -- `02-mechanical-contract.tex:771--775`; and
  `4 <= r_Q`, the banked `EntryGates.four_le_rQ`.

Nothing else about the region is claimed.  The remaining rows of
`eq:stage2-structural-gates` constrain `zeta`, `b_1`, `delta_min`,
`delta_term`, `mu_P`, `eta_R`, `v_max`, `t_ref` and `|C_1|` -- quantities that
are **not** fields of the record -- so no witness asserts them, and no docstring
below calls any tuple legal without naming which display it clears.

**Candidate context, not realized arrow (frozen `eq:t2-search`).**  A *realized*
`step:I-07` arrow additionally carries `t_2 = 2^{k_2}` with
`k_2 >= max{4, 2^19, m_HS}` (`06-parameter-schedule.tex`, label line 772).  The
witnesses above are therefore legal for the **candidate context** that
`thm:effective-parameter-schedule` is stated for (frozen line 2077, "This
numerical theorem is deliberately stated for a candidate context") and are never
described as realized arrows.  `sizeDriver_fires_at_realized_t2_scale` exhibits
the realized `k_2 = 2^19` scale in the driver, where the exponent encoding makes
it free.

## Two recorded reading notes

* **N1 (index convention).**  In `iteratedSizeMajorant` the family `arr` is
  zero-based over Lean's `i`, and `arr i` is the arrow the frozen text indexes
  as **arrow `i+1`**: its fields are the frozen `q_{2,i+1}`, `q_{1,i+1}`,
  `s_{i+1}`, `t_{2,i+1}`, `q_{i+1}`, `r_{Q,i+1}`, while `z i` is the frozen
  `z_i`.  `13-iteration-assembly.tex:529`, "For every `0 <= i < k`, at arrow
  `i+1`, define the integer driver".  This is the same zero-based re-indexing
  `IterationAssembly` records
  for `step:I-03`.
* **N2 (dropped enabling conditions).**  The frozen thread supplies `2 <= n` for
  `step:L-14` (`13-iteration-assembly.tex:521--526`, derived from
  `n >= n_val(k)` through `n >= 2^{2^{R(c_0)+1}} >= 256 > 2`) and assumes
  `k >= 1` and `n >= n_val(k)` throughout `step:I-07`.  **None of the three
  appears in `iteratedSizeMajorant`.**  Every omission strengthens the Lean
  statement -- `n >= n_val(k)` did its work inside the successor row, which is
  here the per-`i` hypothesis `hsuccRow` -- so nothing below is false, but the
  omission is recorded here so that a later consumer reads them as *available*
  rather than as new obligations.
-/

namespace EthInapproximability.ParameterizedNP.SizePropagation

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.IterationAssembly

/-! ## Part 0: public data

Seven transparent functions and one public record, the record carrying six data
fields plus one legality guard and exposing four further derived widths
(`sVal`, `t2Val`, `slots`, `q1`) as transparent functions.  Nothing here has a
complexity,
robustness, promise or envelope field, and none takes a certificate: every
constant below is a maximum of a *recorded table* of integers, exactly as the
frozen producers print them (mechanical rules M1, M2, M4). -/

/-- **A literal maximum of a printed table over a frozen floor.**

The two producers this module consumes are stated in the frozen source as maxima
of a singleton with a finite list -- `max({1} ∪ {K_v : ...})` in
`eq:Cdim-literal-producer` (`06-parameter-schedule.tex`, label line 2199) and
`max({2} ∪ ... )` in `eq:Csize-literal-producer` (label line 1624) -- so the
floor is part of the datum and differs between them.  `maxFrom` is that schema;
`IterationAssembly.literalMax` is exactly its `b = 1` instance, and
`maxFrom_one_eq_literalMax` records the identification rather than duplicating
the banked function. -/
def maxFrom (b : ℕ) (xs : List ℕ) : ℕ := xs.foldr max b

@[simp] lemma maxFrom_nil (b : ℕ) : maxFrom b [] = b := rfl

@[simp] lemma maxFrom_cons (b a : ℕ) (t : List ℕ) :
    maxFrom b (a :: t) = max a (maxFrom b t) := rfl

/-- **The integer driver `Z_N`** -- `step:L-14`
(`11-one-level-assembly.tex:812--819`) and, per arrow, `step:I-07`
(`13-iteration-assembly.tex:529--537`):

```
Z_N = max{1, z, floor log_2(n+2), log_2 q_2, floor log_2 q_1, log_2 s, log_2 t_2}
```

The seven entries are kept in the frozen order and the floor `1` is the frozen
floor, not a Lean convenience.  Frozen line 820 records why three of them are
*exponents* rather than logarithms to be computed: "The logarithms of
`q_2, s, t_2` are integers because these widths are powers of two."  Accordingly
`wq2`, `ws`, `wt2` are the exponents themselves, while the two genuine floors --
`floor log_2(n+2)` and `floor log_2 q_1` -- stay as `Nat.log 2`, which is the
integer `floor(log_2 .)`.

This is the M8 spelling that keeps the numerical source width out of the
multiplicative part of the wrapper dimension: frozen lines 886--888, "neither
`q_2` nor the numerical source size appears as a multiplicative factor in the
logarithmic wrapper dimension; they enter through `Z_N`". -/
def sizeDriver (z n q1 wq2 ws wt2 : ℕ) : ℕ :=
  maxFrom 1 [z, Nat.log 2 (n + 2), wq2, Nat.log 2 q1, ws, wt2]

/-- **The seven multiplicity contributions `t_2 + s(q_1 + s) + 1`** of
`exp:E-14-raw` (`11-one-level-assembly.tex`, display lines 846--851) and of
`P_dim = (t_2 + s(q_1 + s) + 1) Z` (`06-parameter-schedule.tex:2188--2191`).

Written in the frozen shape, so the `s`-fold occurrence of `q_1 + s` is a genuine
product and not a sum: `dimMultiplicity_is_not_additive` refutes the flattened
reading in the kernel. -/
def dimMultiplicity (t2 s q1 : ℕ) : ℕ := t2 + s * (q1 + s) + 1

/-- **`C_dim`** -- `eq:Cdim-literal-producer` (`06-parameter-schedule.tex`, label
line 2199, display lines 2195--2200):
`C_dim = max({1} ∪ {K_v : v ∈ U_dim})`.

Frozen lines 2201--2203: "This is a literal maximum over nineteen named, computed
rows.  In particular `C_dim` is produced by the compiler; it is neither a big-`O`
witness nor an extra configuration input."  The argument is therefore the
*recorded list of the `K_v`*, at an arbitrary length: the traversal producing that
list is `PARAM-001` (GAP-EXPOSED 4). -/
def cdimLiteral (rows : List ℕ) : ℕ := maxFrom 1 rows

/-- **`zbar_N = C_dim (t_2 + s(q_1 + s) + 1) Z_N`** -- `exp:E-14-raw`
(`11-one-level-assembly.tex`, label line 850, display lines 846--851).

Public arithmetic on public data.  The inequality `z_N <= zbar_N` is **not** part
of this definition: frozen lines 852--855 state that it "is not inferred from the
big-`O` display" but is delivered by the checked size-successor row of
`thm:eff-ledger`, so it travels as a named hypothesis at every use site. -/
def rawSideMajorant (Cdim t2 s q1 Z : ℕ) : ℕ :=
  Cdim * dimMultiplicity t2 s q1 * Z

/-- **`C_size`** -- `eq:Csize-literal-producer` (`06-parameter-schedule.tex`,
label line 1624, display lines 1611--1625):

```
C_size = max({2}
   ∪ {3^{d_u} C_u : (u, C_u, d_u, P_u) ∈ CoeffPass(D, L+2, U_C7 || U_tail^{12}; ...)}
   ∪ {C_u      : (u, C_u, d_u, P_u) ∈ CoeffPass(D, A_*, U_tail^{3}; ...)}).
```

Two **separate** passes with two **different** drivers, and only the first
carries the checked absorption `(L+2)^{d_u} <= 3^{d_u} L^{d_u}` of lines
1631--1633.  Frozen lines 1634--1637: "The seven T3 rows instead have checked
degree `d_u <= 2` in the driver `A_*`, so they feed `2^{C_size A_*^2}` directly
and undergo no `L+2`-to-`L` shift."  `rows12` therefore carries the pairs
`(C_u, d_u)` and `rows3` carries bare coefficients;
`t3Pass_carries_no_shift_pole` refutes merging them.

Frozen line 1688 fixes what this constant is **not**: "Equation
`eq:Csize-literal-producer`, rather than the four-row degree summary, produces
`C_size >= 2`."  The four-row degree table of lines 1643--1656 accordingly appears
nowhere in this module, and `degreeSummary_does_not_determine_csize` shows in the
kernel that it could not have produced this value. -/
def csizeLiteral (rows12 : List (ℕ × ℕ)) (rows3 : List ℕ) : ℕ :=
  maxFrom 2 ((rows12.map fun r => 3 ^ r.2 * r.1) ++ rows3)

/-- **`W(L) = 2^{C_size L^8}`** -- the first line of `eq:structural-majorants`
(`06-parameter-schedule.tex`, label line 1701, display lines 1691--1702), "every
new logarithmic side length and auxiliary scale `<= W(L)`".

Frozen lines 1704--1706: "The exponent eight is not optimised; it is the largest
entry in the displayed, mechanically generated degree table."  The numeral eight
is therefore literal here, and the constant it multiplies is `csizeLiteral`, never
a degree read off that table. -/
def structuralW (Csize L : ℕ) : ℕ := 2 ^ (Csize * L ^ 8)

/-- **The public per-arrow size record of `step:I-07`**
(`13-iteration-assembly.tex:519--556`).

Six public numbers and one legality guard, and nothing else.  Frozen lines
529--537 name the driver inputs
`z_i, n, q_{2,i+1}, q_{1,i+1}, s_{i+1}, t_{2,i+1}`, and lines 544--549 name the
two wrapper widths `q_{i+1}` and `Q_{i+1}`.  Here:

* the three dyadic widths `q`, `Q`, `q_2` and the two dyadic source widths
  `s`, `t_2` are carried by their **exponents**, which is the frozen fact of line
  820 and the M8 spelling the banked `OneLevelAssembly.sideStep` already uses;
* `q_1` is **not** a free width and is **not** carried by an exponent.  The
  frozen source fixes it completely: "The parameter compiler has fixed `a >= 3`;
  put `q_1 = 2^a - 2`" (`07-one-level-construction.tex:118`), repeated as
  `eq:stage1-scales` (`06-parameter-schedule.tex`, label line 319, which adds
  "`q_1 + 2` is a power of two").  The record therefore carries `a` with its
  guard, and `q1` is the derived width of the banked
  `FiniteSlots.Stage1SlotBinding` -- the same structure, the same guard field
  name, and the same derivation, so `FiniteSlots.Stage1SlotBinding.six_le_q₁` is
  consumed rather than restated.  `q_1` is then *never* a power of two
  (`2^a - 2` is twice the odd `2^{a-1} - 1` for `a >= 2`), which is exactly why
  the driver must read it through the genuine floor `floor log_2 q_1`;
  `sizeDriver_fires_nondegenerate` exercises that floor at `q_1 = 62`, where it
  differs from the ceiling.

There is no field for `z_i`, for the envelope, for a promise branch or for any
bound: those are arguments of the derived functions or hypotheses at the use
sites, so no conclusion sits in constructor data (rules M2, M4).  The one
`Prop`-valued field is a *legality guard* on public parameter data, exactly as
in the banked `Stage1SlotBinding` (`M1`, `M2`), and it is why the derived
`DecidableEq`/`Repr` instances of the parked first round are gone.  Candidate B
-- carrying `q` and `Q` raw -- is refuted by
`rawWidthEncoding_breaks_the_row_branch`. -/
structure ArrowSize where
  /-- `w_q = log_2 q`, the inner scale-alignment exponent
  (`09-first-wrapper.tex:105`, `q = 2^r`).  The frozen legality guard is
  `1 <= w_q`, i.e. `q >= 2`. -/
  wq : ℕ
  /-- `r_Q = log_2 Q`, the outer bridge exponent (`10-direct-bridge.tex:51`).
  Never interchanged with `wq`; `sideStep_orientation_pole` refutes the swap. -/
  rQv : ℕ
  /-- `log_2 q_2`, the numerical source width's **logarithm**.  The raw width is
  deliberately absent: frozen lines 886--888. -/
  wq2 : ℕ
  /-- `log_2 s`. -/
  ws : ℕ
  /-- `log_2 t_2`. -/
  wt2 : ℕ
  /-- `a`, the compiler-fixed Stage-1 exponent of `eq:stage1-scales`
  (`06-parameter-schedule.tex`, label line 319).  `q_1` is derived from it and
  is not itself a field. -/
  aExp : ℕ
  /-- The frozen legality guard "The parameter compiler has fixed `a >= 3`"
  (`07-one-level-construction.tex:118`).  Same guard, same role and same proof
  obligation as `FiniteSlots.Stage1SlotBinding.three_le_a`. -/
  three_le_aExp : 3 ≤ aExp

namespace ArrowSize

/-- `s = 2^{log_2 s}`, the Stage-1 slab count of the driver. -/
def sVal (a : ArrowSize) : ℕ := 2 ^ a.ws

/-- `t_2 = 2^{log_2 t_2}`, the balanced-family tuple width of the driver. -/
def t2Val (a : ArrowSize) : ℕ := 2 ^ a.wt2

/-- **The banked Stage-1 slot binding of this arrow.**

`FiniteSlots.Stage1SlotBinding` is the already-gated encoding of the same two
frozen facts -- `a >= 3` (`07-one-level-construction.tex:118`) and `s > 0`
(`eq:raw-stage4-universes`) -- so the arrow builds one rather than duplicating
the guard.  `s_pos` is discharged from the exponent encoding: `s = 2^{log_2 s}`
is positive for every exponent. -/
def slots (a : ArrowSize) : FiniteSlots.Stage1SlotBinding where
  a := a.aExp
  s := a.sVal
  three_le_a := a.three_le_aExp
  s_pos := Nat.one_le_two_pow

/-- **`q_1 = 2^a - 2`** -- `eq:stage1-scales` (`06-parameter-schedule.tex`,
label line 319) and `07-one-level-construction.tex:118`, read off the banked
`FiniteSlots.Stage1SlotBinding.q₁`.  A derived width, never a field. -/
def q1 (a : ArrowSize) : ℕ := a.slots.q₁

/-- **`Z_{i,N}` at this arrow** -- `13-iteration-assembly.tex:529--537`. -/
def driver (a : ArrowSize) (z n : ℕ) : ℕ :=
  sizeDriver z n a.q1 a.wq2 a.ws a.wt2

/-- **`z_{N,i} = C_dim (t_{2,i+1} + s_{i+1}(q_{1,i+1} + s_{i+1}) + 1) Z_{i,N}`**
-- `13-iteration-assembly.tex:538--543`, which is `exp:E-14-raw` at arrow
`i+1`. -/
def rawMajorant (a : ArrowSize) (Cdim z n : ℕ) : ℕ :=
  rawSideMajorant Cdim a.t2Val a.sVal a.q1 (a.driver z n)

/-- **`z_{i+1}^+ = max{Q_{i+1}(log_2 q_{i+1} + z_{N,i}), log_2 Q_{i+1}
+ q_{i+1} z_{N,i}}`** -- `13-iteration-assembly.tex:544--549`, i.e. the banked
`exp:E-14-step` of `OneLevelAssembly.sideStep` evaluated at this arrow's raw
majorant.  The banked step is consumed, never restated. -/
def stepBound (a : ArrowSize) (Cdim z n : ℕ) : ℕ :=
  sideStep a.wq a.rQv (a.rawMajorant Cdim z n)

end ArrowSize

/-- **`AuxOut(Cert_c) = Roots(Successor_c) \ {ceil log_2 m_next, ceil log_2
n_next, D+H+1, Y+H}`** -- `thm:effective-parameter-schedule`
(`06-parameter-schedule.tex:2043--2052`), whose frozen preamble is "Define,
**without adding a new root**".

Roots are abstract tokens with decidable equality; nothing about their internal
structure is used, which is exactly the frozen situation -- the four principal
roots are named by the display, and the C7 list of lines 2053--2058 is
`PARAM-001` (GAP-EXPOSED 4).  The set-difference spelling is the whole content:
`auxOut_spec` proves membership is `in roots and not in principal`, so no root is
added. -/
def auxOut {α : Type*} [DecidableEq α] (roots principal : List α) : List α :=
  roots.filter (fun a => decide (a ∉ principal))

/-! ## Part 1: the aux-lemma battery

Nineteen general properties.  None is about a pinned instance: each quantifies
over arbitrary tables, drivers, exponents, source sizes, root tokens or legal
arrows. -/

/-- **Aux 1 (the frozen floor is a floor).**

The singleton in `max({1} ∪ ...)` and `max({2} ∪ ...)` is a genuine lower bound
on the produced constant, at an arbitrary table.  This is what delivers
`C_dim >= 1` and `C_size >= 2` without evaluating either producer. -/
lemma maxFrom_ge_base (b : ℕ) (xs : List ℕ) : b ≤ maxFrom b xs := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [maxFrom_cons]; exact le_trans ih (le_max_right _ _)

/-- **Aux 2 (every recorded row is dominated).**

The defining property of a literal maximum over a printed table, general in the
floor, the table and the row. -/
lemma le_maxFrom {b : ℕ} : ∀ {xs : List ℕ} {x : ℕ}, x ∈ xs → x ≤ maxFrom b xs := by
  intro xs
  induction xs with
  | nil => intro x hx; cases hx
  | cons a t ih =>
    intro x hx
    rcases List.mem_cons.1 hx with h | h
    · subst h; simp only [maxFrom_cons]; exact le_max_left _ _
    · simp only [maxFrom_cons]; exact le_trans (ih h) (le_max_right _ _)

/-- **Aux 3 (round trip: the `b = 1` schema is the banked literal maximum).**

`IterationAssembly.literalMax` was banked for `eq:Cexc0-literal-producer`, whose
frozen floor is `1`; `eq:Cdim-literal-producer` has the same floor.  Rather than
duplicating the banked function, this identifies the two, so `cdimLiteral` and
the banked `cexcZero`/`bexcZero` are literally the same maximum schema.  General
in the table. -/
lemma maxFrom_one_eq_literalMax (xs : List ℕ) : maxFrom 1 xs = literalMax xs := rfl

/-- **Aux 4 (the driver dominates all seven frozen entries).**

`11-one-level-assembly.tex:812--819` read as seven separate inequalities.  This
is the only property of `Z_N` the size thread uses, and it is general in all six
inputs.  The frozen conclusion `Z_N ∈ ℕ` of line 815--817 is automatic here
because every entry is already a natural number. -/
lemma sizeDriver_dominates (z n q1 wq2 ws wt2 : ℕ) :
    1 ≤ sizeDriver z n q1 wq2 ws wt2 ∧
      z ≤ sizeDriver z n q1 wq2 ws wt2 ∧
      Nat.log 2 (n + 2) ≤ sizeDriver z n q1 wq2 ws wt2 ∧
      wq2 ≤ sizeDriver z n q1 wq2 ws wt2 ∧
      Nat.log 2 q1 ≤ sizeDriver z n q1 wq2 ws wt2 ∧
      ws ≤ sizeDriver z n q1 wq2 ws wt2 ∧
      wt2 ≤ sizeDriver z n q1 wq2 ws wt2 := by
  refine ⟨maxFrom_ge_base 1 _, le_maxFrom ?_, le_maxFrom ?_, le_maxFrom ?_,
    le_maxFrom ?_, le_maxFrom ?_, le_maxFrom ?_⟩ <;> simp

/-- **Aux 5 (the driver is monotone in the incoming side length).**

Needed to thread the induction of `step:I-07`, where the incoming `z_i` is only
known through an upper bound.  General in every other input. -/
lemma sizeDriver_mono_incoming {z z' : ℕ} (n q1 wq2 ws wt2 : ℕ) (h : z ≤ z') :
    sizeDriver z n q1 wq2 ws wt2 ≤ sizeDriver z' n q1 wq2 ws wt2 := by
  simp only [sizeDriver, maxFrom_cons]
  exact max_le_max h (le_refl _)

/-- **Aux 6 (the raw majorant is monotone in the driver).**

`exp:E-14-raw` is a product with a nonnegative coefficient, so it transports the
previous monotonicity.  General in the coefficient and the three multiplicity
inputs. -/
lemma rawSideMajorant_mono {Z Z' : ℕ} (Cdim t2 s q1 : ℕ) (h : Z ≤ Z') :
    rawSideMajorant Cdim t2 s q1 Z ≤ rawSideMajorant Cdim t2 s q1 Z' :=
  Nat.mul_le_mul_left _ h

/-- **Aux 7 (the banked size step is monotone in the raw majorant).**

`exp:E-14-step` is a maximum of two increasing affine functions of `z_N`; the
banked `sideStep` is consumed and not restated.  General in both exponents. -/
lemma sideStep_mono {zN zN' : ℕ} (wq rQv : ℕ) (h : zN ≤ zN') :
    sideStep wq rQv zN ≤ sideStep wq rQv zN' := by
  simp only [sideStep]
  exact max_le_max (Nat.mul_le_mul_left _ (Nat.add_le_add_left h _))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _)

/-- **Aux 8 (`l(n) >= 2` unconditionally).**

The banked `IterationAssembly.ellN_spec` delivers this only under `1 <= n`,
because it also delivers the sharper `l(n) >= 3` of `step:I-04` line 427.  The
weaker half needs no hypothesis at all -- it is the `2 <= r` conjunct of the
frozen least-integer predicate `13-iteration-assembly.tex:248--249` -- and the
envelope monotonicity below is stated for every source size, including zero. -/
lemma two_le_ellN (n : ℕ) : 2 ≤ ellN n := (Nat.find_spec (ellN_exists n)).1

/-- **Aux 9 (the envelope is monotone in its exponent).**

`13-iteration-assembly.tex:574--577`: "The exponents `c_i` are strictly
increasing ... Therefore `E_{c_i}(n) <= E_{c_k}(n)` for `i <= k`."  General in
`n` and both exponents; the proof uses only `l(n) >= 1`. -/
lemma envE_mono_exp {c c' : ℕ} (n : ℕ) (h : c ≤ c') : envE c n ≤ envE c' n := by
  have h1 : 1 ≤ ellN n := le_trans (by norm_num) (two_le_ellN n)
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right h1 h)

/-- **Aux 10 (the exponent recursion is monotone).**

The frozen sentence of `13-iteration-assembly.tex:573--575` in its non-strict
form, obtained from the banked strict step `cexp_ge_three_and_lt`.  General in
both indices. -/
lemma cexp_mono {i k : ℕ} (h : i ≤ k) : cexp i ≤ cexp k := by
  induction k, h using Nat.le_induction with
  | base => exact le_refl _
  | succ m _ ih => exact le_trans ih (Nat.le_of_lt (cexp_ge_three_and_lt m).2)

/-- **Aux 11 (`C_size >= 2`, and both passes are dominated with their own
shifts).**

`06-parameter-schedule.tex:1689` (`C_size >= 2`) together with the two branches
of the maximum in `eq:Csize-literal-producer`: a first-pass row `(C_u, d_u)`
contributes `3^{d_u} C_u`, a `T3` row contributes `C_u` alone.  General in both
tables. -/
lemma csizeLiteral_spec (rows12 : List (ℕ × ℕ)) (rows3 : List ℕ) :
    2 ≤ csizeLiteral rows12 rows3 ∧
      (∀ r ∈ rows12, 3 ^ r.2 * r.1 ≤ csizeLiteral rows12 rows3) ∧
      (∀ v ∈ rows3, v ≤ csizeLiteral rows12 rows3) := by
  refine ⟨maxFrom_ge_base 2 _, ?_, ?_⟩
  · intro r hr
    exact le_maxFrom (List.mem_append_left _ (List.mem_map_of_mem hr))
  · intro v hv
    exact le_maxFrom (List.mem_append_right _ hv)

/-- **Aux 12 (`C_dim >= 1`, and every dimension row is dominated).**

`eq:Cdim-literal-producer` read as its two characterizing properties, general in
the recorded table. -/
lemma cdimLiteral_spec (rows : List ℕ) :
    1 ≤ cdimLiteral rows ∧ ∀ K ∈ rows, K ≤ cdimLiteral rows :=
  ⟨maxFrom_ge_base 1 _, fun _K hK => le_maxFrom hK⟩

/-- **Aux 13 (the structural majorant is monotone and never trivial).**

`eq:structural-majorants` is used as an upper envelope, so both the floor
`W(L) >= 1` and monotonicity in the driver `L` are needed.  General in the
constant and in `L`. -/
lemma structuralW_mono {L L' : ℕ} (Csize : ℕ) (h : L ≤ L') :
    1 ≤ structuralW Csize L ∧ structuralW Csize L ≤ structuralW Csize L' := by
  refine ⟨Nat.one_le_two_pow, ?_⟩
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 8))

/-- **Aux 14 (the `AuxOut` set identity).**

`06-parameter-schedule.tex:2043--2052` -- membership in `AuxOut` is exactly
"is a successor root, and is not one of the four principal roots".  Both
directions, general in the token type and in both lists.  It is what makes
"without adding a new root" checkable. -/
lemma auxOut_spec {α : Type*} [DecidableEq α] (roots principal : List α)
    (a : α) : a ∈ auxOut roots principal ↔ a ∈ roots ∧ a ∉ principal := by
  simp [auxOut]

/-- **Aux 15 (the frozen ceiling really is a ceiling of the wrapper carriers).**

The banked `OneLevelAssembly.sideExponent_bounds` transported through an
arbitrary upper bound on the exponent, which is the shape every use of
`exp:E-14-raw` takes: the checked row bounds `z_N`, and the carriers must still
be bounded by `2` to the *majorant*.  General in both cardinalities and the
majorant. -/
lemma carriers_le_two_pow_of_sideExponent_le {mN nN M : ℕ}
    (h : sideExponent mN nN ≤ M) : mN ≤ 2 ^ M ∧ nN ≤ 2 ^ M := by
  obtain ⟨hm, hn⟩ := sideExponent_bounds mN nN
  exact ⟨le_trans hm (Nat.pow_le_pow_right (by norm_num) h),
    le_trans hn (Nat.pow_le_pow_right (by norm_num) h)⟩

/-- **Aux 16 (and its converse).**

The frozen `z_N` of `exp:E-14-raw-exact` is *defined* as a maximum of two
ceilings, so an integer dominating both carriers dominates it.  This is the
direction `eq:paper-log-carrier-recurrence` is stated in -- a bound on
`z(R_{i+1})` rather than on the two cardinalities -- and it is what lets the
output of one arrow be the input `z_i` of the next.  General in both
cardinalities and the bound. -/
lemma sideExponent_le_of_carriers_le {mN nN M : ℕ} (hm : mN ≤ 2 ^ M)
    (hn : nN ≤ 2 ^ M) : sideExponent mN nN ≤ M := by
  simp only [sideExponent]
  exact max_le (Nat.clog_le_of_le_pow hm) (Nat.clog_le_of_le_pow hn)

/-- **Aux 17 (the Stage-1 floor, consumed from the banked binding).**

`FiniteSlots.Stage1SlotBinding.six_le_q₁` transported along `ArrowSize.slots`.
The frozen fact is `q_1 = 2^a - 2` with `a >= 3` (`eq:stage1-scales`,
`06-parameter-schedule.tex`, label line 319; `07-one-level-construction.tex:118`);
the banked module already proved the consequence, so it is **re-exported, never
re-proved**.  General in the arrow. -/
lemma six_le_q1 (a : ArrowSize) : 6 ≤ a.q1 := a.slots.six_le_q₁

/-- **Aux 18 (the exact floor logarithm of every legal Stage-1 width).**

For every legal arrow `2^{a-1} <= q_1 = 2^a - 2 < 2^a`, so
`floor log_2 q_1 = a - 1`.  General in the arrow; the guard `3 <= a` is what
makes the left inequality available.  This is the entry `step:I-07` reads at
`floor log_2 q_{1,i+1}` (`13-iteration-assembly.tex:534`). -/
lemma log_q1 (a : ArrowSize) : Nat.log 2 a.q1 = a.aExp - 1 := by
  have h3 := a.three_le_aExp
  have hq : a.q1 = 2 ^ a.aExp - 2 := rfl
  have hsplit : 2 ^ a.aExp = 2 * 2 ^ (a.aExp - 1) := by
    conv_lhs => rw [show a.aExp = (a.aExp - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have h2 : (2 : ℕ) ≤ 2 ^ (a.aExp - 1) := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ (a.aExp - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hge : 2 ^ (a.aExp - 1) ≤ a.q1 := by omega
  have hlt : a.q1 < 2 ^ (a.aExp - 1 + 1) := by
    have he : a.aExp - 1 + 1 = a.aExp := by omega
    rw [he]
    omega
  exact Nat.log_eq_of_pow_le_of_lt_pow hge hlt

/-- **Aux 19 (the floor is genuine: at every legal arrow it is strictly below
the ceiling).**

`q_1 = 2^a - 2` is never a power of two once `a >= 3`, so
`ceil log_2 q_1 = a > a - 1 = floor log_2 q_1`.  This is the general property
separating the landed encoding from the refuted Candidate B: carrying `q_1` by
an exponent would assert `q_1 = 2^w`, and that is false at *every* legal arrow,
not merely at a chosen witness.  General in the arrow. -/
lemma log_q1_lt_clog_q1 (a : ArrowSize) : Nat.log 2 a.q1 < Nat.clog 2 a.q1 := by
  have h3 := a.three_le_aExp
  have hq : a.q1 = 2 ^ a.aExp - 2 := rfl
  have hsplit : 2 ^ a.aExp = 2 * 2 ^ (a.aExp - 1) := by
    conv_lhs => rw [show a.aExp = (a.aExp - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have h4 : (4 : ℕ) ≤ 2 ^ (a.aExp - 1) := by
    have h : (2 : ℕ) ^ 2 ≤ 2 ^ (a.aExp - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hstrict : 2 ^ (a.aExp - 1) < a.q1 := by omega
  have hclog : a.aExp - 1 < Nat.clog 2 a.q1 :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hstrict
  rw [log_q1 a]
  exact hclog

/-! ## Part 2: `exp:E-14-raw` -- the uniform majorant

The frozen inequality is *supplied* by the checked size-successor row, so it is a
binder here.  What is proved is its stated consequence for the two carriers. -/

/-- **`exp:E-14-raw`** (`11-one-level-assembly.tex`, label line 850, display
lines 846--851):

```
z_N <= zbar_N := C_dim (t_2 + s(q_1 + s) + 1) Z_N.
```

Frozen lines 852--855: "This inequality is not inferred from the big-`O` display.
`thm:eff-ledger` prints a size-successor row with a numerical integer `C_dim`,
the seven multiplicity contributions, and a checked derivation of
`exp:E-14-raw`."  The hypothesis `hrow` **is** that checked row, named rather
than derived (GAP-EXPOSED 2), and `uniformSideMajorant_hypothesis_not_free`
exhibits legal values at which it fails, so it constrains rather than decorates.

The conclusion is the frozen consequence of lines 844--845 read at the majorant:
`|Rows(N)|, |Cols(N)| <= 2^{zbar_N}` "without an asymptotic witness".  General in
both carriers, in the recorded coefficient and in every arrow field.

Reader counterpart: **none** -- the reader artifact never names `C_dim`, `Z_N` or
the multiplicity polynomial; see the module header. -/
theorem uniformSideMajorant {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (a : ArrowSize) (Cdim z n : ℕ)
    (hrow : sideExponent (rowsCard N) (colsCard N) ≤ a.rawMajorant Cdim z n) :
    rowsCard N ≤ 2 ^ a.rawMajorant Cdim z n ∧
      colsCard N ≤ 2 ^ a.rawMajorant Cdim z n :=
  carriers_le_two_pow_of_sideExponent_le hrow

/-- **The two literal producers, as the frozen text prints them.**

`eq:Cdim-literal-producer` and `eq:Csize-literal-producer` in one statement:
`C_dim >= 1` and dominates every recorded `K_v`; `C_size >= 2`, dominates every
first-pass row **through its own `3^{d_u}` absorption**, and dominates every `T3`
row **without** that shift.  Frozen line 1688 is obeyed literally -- the four-row
degree summary is not consulted, and `degreeSummary_does_not_determine_csize`
shows it could not have produced this value.

General in both recorded tables (GAP-EXPOSED 4).

Reader counterpart: **none**; the reader artifact never names either constant. -/
theorem literalProducers (dimRows : List ℕ) (rows12 : List (ℕ × ℕ))
    (rows3 : List ℕ) :
    (1 ≤ cdimLiteral dimRows ∧ ∀ K ∈ dimRows, K ≤ cdimLiteral dimRows) ∧
      2 ≤ csizeLiteral rows12 rows3 ∧
      (∀ r ∈ rows12, 3 ^ r.2 * r.1 ≤ csizeLiteral rows12 rows3) ∧
      (∀ v ∈ rows3, v ≤ csizeLiteral rows12 rows3) := by
  obtain ⟨h2, h12, h3⟩ := csizeLiteral_spec rows12 rows3
  exact ⟨cdimLiteral_spec dimRows, h2, h12, h3⟩

/-- **The `A_wrap` search of `step:I-01` is consumed at the two literal maxima.**

`13-iteration-assembly.tex:69--97` and `eq:Awrap-coefficient-search`
(`06-parameter-schedule.tex`, label line 1677).  The `AUDIT-007`-repaired
nonemptiness calculation -- the frozen witness `M = C_exc^0 + B_exc^0 + c_seed +
8` with `A = 2^M`, transcribed at lines 69--84 -- is banked as
`IterationAssembly.awrap_search_nonempty` and is **not** re-proved here; this
statement threads its recorded deliverables into the constant inventory the size
thread shares with the schedule, at the **two** literal maxima of
`eq:Cexc0-literal-producer` read off one recorded coefficient table.

`B_exc^0` occurs throughout as its own binder: frozen line 66, "Retaining
`B_exc^0` is essential: repeated occurrences of the formal leaf `X` are not
silently assigned coefficient one."  No unit-slope restatement appears anywhere
in this module.

Reader counterpart: **none** (the reader never names `A_wrap` or `C_exc`); see
the `ITER-001` module header, which reports the same absence. -/
theorem scheduleCoefficientInputs (cseed : ℕ) (tbl : List (ℕ × ℕ)) :
    AwrapAdmissible cseed (cexcZero tbl) (bexcZero tbl)
        (awrap cseed (cexcZero tbl) (bexcZero tbl)) ∧
      cseed < awrap cseed (cexcZero tbl) (bexcZero tbl) ∧
      cexcOf cseed (cexcZero tbl) (bexcZero tbl) + 4
        ≤ awrap cseed (cexcZero tbl) (bexcZero tbl) := by
  obtain ⟨hadm, -, hgt, hmargin, -⟩ :=
    coefficientPass_awrap cseed (cexcZero tbl) (bexcZero tbl)
  exact ⟨hadm, hgt, hmargin⟩

/-! ## Part 3: the one-arrow size step

`step:L-14` (`11-one-level-assembly.tex`, label line 800) evaluated at the pinned
double-interlace output, which is where `step:I-07`'s arrow calculation happens.
Both interlace widths stay in separate binders. -/

/-- **The one-arrow size step at the pinned output**
(`step:L-14`, `11-one-level-assembly.tex:857--882`, and the arrow calculation of
`step:I-07`, `13-iteration-assembly.tex:538--556`).

From the exact wrapper cardinalities `|Rows(R^+)| = (q m_N)^Q` and
`|Cols(R^+)| = Q n_N^q` of the banked `OneLevelCompletion.pinnedOutput_carriers`,
together with `m_N, n_N <= 2^{zbar_N}` from `exp:E-14-raw`, both sides of the
frozen output are bounded by `2^{z^+}` at the single integer `z^+` of
`exp:E-14-step`.

The two widths enter through **separate** binders and on **opposite** sides of
the two branches -- `Q = 2^{r_Q}` exponentiates the row branch and multiplies the
column branch -- which is the asymmetry `sideStep_orientation_pole` pins.  The
guard `hq : 1 <= a.wq` is the frozen legality condition `q >= 2` of
`02-mechanical-contract.tex:771--775`; it is a lower bound on the width and never
an upper one.  `hQ` identifies the arrow's recorded outer exponent with the
route's `r_Q`, so no second bridge width is introduced.

The third conjunct is the reader's own spelling: `eq:paper-log-carrier-recurrence`
bounds `z(R_{i+1})` rather than the two cardinalities, and it is what lets this
arrow's output be the next arrow's incoming `z_i`.

General in both carriers, in the recorded coefficient, in the incoming side
length and in the source size.

Reader counterpart: `eq:paper-log-carrier-recurrence` (`05-iteration.tex`, label
line 174, display lines 168--175). -/
theorem arrowSizeStep {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (a : ArrowSize) (Cdim z n bout : ℕ) (δU : ℝ)
    (hq : 1 ≤ a.wq) (hQ : rQ bout δU = a.rQv)
    (hrow : sideExponent (rowsCard N) (colsCard N) ≤ a.rawMajorant Cdim z n) :
    rowsCard (levelOutput N a.wq bout δU) ≤ 2 ^ a.stepBound Cdim z n ∧
      colsCard (levelOutput N a.wq bout δU) ≤ 2 ^ a.stepBound Cdim z n ∧
      sideExponent (rowsCard (levelOutput N a.wq bout δU))
          (colsCard (levelOutput N a.wq bout δU))
        ≤ a.stepBound Cdim z n := by
  obtain ⟨hm, hn⟩ := uniformSideMajorant N a Cdim z n hrow
  obtain ⟨hrowCard, hcolCard⟩ := pinnedOutput_carriers N a.wq bout δU hq
  have hQpow : Qwidth bout δU = 2 ^ a.rQv := by
    rw [Qwidth_eq_two_pow bout δU, hQ]
  obtain ⟨hb1, hb2⟩ := sideStep_bounds a.wq a.rQv (a.rawMajorant Cdim z n)
  have hrowOut : rowsCard (levelOutput N a.wq bout δU)
      ≤ 2 ^ a.stepBound Cdim z n := by
    rw [hrowCard, hQpow]
    exact le_trans (rowBranch_bound a.wq (a.rawMajorant Cdim z n) (2 ^ a.rQv)
      (Fintype.card X) hm) (Nat.pow_le_pow_right (by norm_num) hb1)
  have hcolOut : colsCard (levelOutput N a.wq bout δU)
      ≤ 2 ^ a.stepBound Cdim z n := by
    rw [hcolCard, hQpow]
    exact le_trans (colBranch_bound a.rQv (2 ^ a.wq) (a.rawMajorant Cdim z n)
      (Fintype.card Y) hn) (Nat.pow_le_pow_right (by norm_num) hb2)
  exact ⟨hrowOut, hcolOut, sideExponent_le_of_carriers_le hrowOut hcolOut⟩

/-- **The pinned-output carrier invariant travels with the size step.**

`02-mechanical-contract.tex:767--775`, consumed through the banked
`OneLevelCompletion.pinnedOutput_carriers_invariant`: "the exact successor
equations give `m_next = (q m_N)^Q >= 2`, `n_next = Q n_N^q >= 2` because
`q, Q >= 2` and `m_N, n_N >= 1`.  Hence realization preserves the invariant."

Stated as a separate declaration so that `arrowSizeStep` keeps its full
generality (the two upper bounds need neither carrier to be inhabited), while the
next arrow's applicability -- which does need it -- is still recorded here.
`Q >= 2` is not assumed: it is discharged inside the banked lemma from
`EntryGates.four_le_rQ`.

Reader counterpart: `05-iteration.tex:280--283` is already assigned to the banked
`pinnedOutput_carriers_invariant` under `BRIDGE-COMPLETION-001`, so this
declaration claims **no** reader item and merely re-exports that endpoint at the
size thread. -/
theorem arrowSizeStep_preserves_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (a : ArrowSize) (bout : ℕ) (δU : ℝ)
    (hq : 1 ≤ a.wq) (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) :
    2 ≤ rowsCard (levelOutput N a.wq bout δU) ∧
      2 ≤ colsCard (levelOutput N a.wq bout δU) :=
  pinnedOutput_carriers_invariant N a.wq bout δU hq hX hY

/-- **The size thread consumes no promise branch.**

`step:L-14` and `step:I-07` are stated for the constructed carriers alone: no
`YES` or `NO` certificate occurs in either frozen step, and
`05-public-records.tex:809--811` records that supplying a branch argument "cannot
change any trace field".  Here the promise label is an **explicit binder** and
the delivered bounds are the same integer on both branches, which is the frozen
content; `promiseFreedom_not_automatic` (banked) is the pole showing that a
`PromiseCase`-indexed family need not be constant, so this is a property of the
level output and not of the label type.

General in both carriers, in every arrow field and in both branches.

Reader counterpart: **none**; branch-freedom of the level output is
`ONELEVEL-001`'s `04-bridge.tex:154--167`, already assigned. -/
theorem arrowSizeStep_promise_free {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (a : ArrowSize) (Cdim z n bout : ℕ) (δU : ℝ)
    (hq : 1 ≤ a.wq) (hQ : rQ bout δU = a.rQv)
    (hrow : sideExponent (rowsCard N) (colsCard N) ≤ a.rawMajorant Cdim z n)
    (c c' : PromiseCase) :
    levelOutputOfCase N a.wq bout δU c = levelOutputOfCase N a.wq bout δU c' ∧
      rowsCard (levelOutputOfCase N a.wq bout δU c)
        ≤ 2 ^ a.stepBound Cdim z n ∧
      colsCard (levelOutputOfCase N a.wq bout δU c')
        ≤ 2 ^ a.stepBound Cdim z n ∧
      PromiseCase.yes ≠ PromiseCase.no ∧
      ¬ ∀ f : PromiseCase → ℕ, f PromiseCase.yes = f PromiseCase.no := by
  obtain ⟨hr, hc, -⟩ := arrowSizeStep N a Cdim z n bout δU hq hQ hrow
  exact ⟨levelOutput_promise_free N a.wq bout δU c c', hr, hc, promiseCase_ne,
    promiseFreedom_not_automatic⟩

/-! ## Part 4: `step:I-07` -- the iterated size majorant

The frozen thread and its `readingwarning`.  Both conditional inputs -- the
canonical-reindexing transport and the checked size-successor row -- are named
hypotheses. -/

/-- **`step:I-07`, the iterated size majorant**
(`13-iteration-assembly.tex`, label line 516, body lines 519--571, together with
the `readingwarning` "Use of the size-successor row", lines 558--571).

The frozen thread is: the seed satisfies `z_0 < E_3(n) = E_{c_0}(n)` (line 520);
at every arrow the exact wrapper calculation bounds the raw output by
`z_{i+1}^+`, and "Canonical reindexing preserves both carrier cardinalities, so
the next public matrix also satisfies `z_{i+1} <= z_{i+1}^+`" (lines 555--556);
and, by the reading warning, if `z_i <= E_{c_i}(n)` then the recorded successor
row gives `z_{i+1}^+ <= E_{16(c_i+1)}(n) = E_{c_{i+1}}(n)`, whence by induction
`z_i <= E_{c_i}(n)` for `0 <= i <= k`.  Lines 573--580 then add
`E_{c_i}(n) <= E_{c_k}(n)`, so "every intermediate matrix in a realized
`k`-level construction consequently has maximum logarithmic side length at most
`E_{c_k}(n)`."

The two conditional inputs are **named hypotheses**, matching the frozen text:

* `hcarry` is the arrow calculation composed with canonical reindexing.
  `lem:canonical-reindexing-invariance` is still not in Lean (`ITER-001`
  GAP-EXPOSED 2), so the transport is assumed, not derived; `arrowSizeStep`
  above is what discharges its non-transport half at a genuine level output.
* `hsuccRow` is the checked size-successor row of `thm:eff-ledger` -- exactly the
  reading warning's implication, in the frozen conditional form `if
  z_i <= E_{c_i}(n) then ...`.  It is **not** a Lean axiom (GAP-EXPOSED 2).

`hseed` is the frozen strict seed inequality at `c_0 = 3`.  Nothing is assumed
about the arrows beyond their public fields, and no promise branch occurs.
General in `n`, in `k`, in the recorded coefficient, in the ladder and in the
arrow family.

`iteratedSizeMajorant_fires_growing` inhabits every hypothesis at legal values
with a **strictly growing** ladder, so the bundle is consistent and the
conclusion is not vacuously about a constant sequence.

**N1 (index convention).**  `arr` is zero-based over Lean's `i`, and `arr i` is
the arrow the frozen text indexes as **arrow `i+1`**: its fields are the frozen
`q_{2,i+1}`, `q_{1,i+1}`, `s_{i+1}`, `t_{2,i+1}`, `q_{i+1}` and `r_{Q,i+1}`,
while `z i` is the frozen `z_i`.  `13-iteration-assembly.tex:529`, "For every
`0 <= i < k`, at arrow `i+1`, define the integer driver".  This is the same
zero-based re-indexing `IterationAssembly` records for `step:I-03`.

**N2 (dropped enabling conditions).**  The frozen step assumes `k >= 1` and
`n >= n_val(k)` (line 521) and derives `2 <= n` for `step:L-14` from them
(lines 521--526, `n >= 2^{2^{R(c_0)+1}} >= 256 > 2`); the readingwarning repeats
`n >= n_val(k)`.  **None of the three is a hypothesis here.**  Each omission
*strengthens* the statement -- `n >= n_val(k)` did its work inside the recorded
successor row, which is the per-`i` hypothesis `hsuccRow`, and `k = 0` is
allowed because both conclusions are then just the seed bound -- so nothing
above is false.  The omission is recorded so that a later consumer treats those
three as facts *available* from `step:I-01`/`step:I-02`, never as new
obligations created here.

Reader counterpart: `eq:paper-fixed-level-growth` (`05-iteration.tex`, label line
289, display lines 286--290). -/
theorem iteratedSizeMajorant (n k Cdim : ℕ) (z : ℕ → ℕ) (arr : ℕ → ArrowSize)
    (hseed : z 0 < envE (cexp 0) n)
    (hcarry : ∀ i, i < k → z (i + 1) ≤ (arr i).stepBound Cdim (z i) n)
    (hsuccRow : ∀ i, i < k → z i ≤ envE (cexp i) n →
      (arr i).stepBound Cdim (z i) n ≤ envE (cexp (i + 1)) n) :
    (∀ i, i ≤ k → z i ≤ envE (cexp i) n) ∧
      (∀ i, i ≤ k → z i ≤ envE (cexp k) n) := by
  have hmain : ∀ i, i ≤ k → z i ≤ envE (cexp i) n := by
    intro i
    induction i with
    | zero => intro _; exact Nat.le_of_lt hseed
    | succ m ih =>
      intro hm
      have hmk : m < k := by omega
      have hprev : z m ≤ envE (cexp m) n := ih (by omega)
      exact le_trans (hcarry m hmk) (hsuccRow m hmk hprev)
  refine ⟨hmain, fun i hi => ?_⟩
  exact le_trans (hmain i hi) (envE_mono_exp n (cexp_mono hi))

/-! ## Part 5: `thm:effective-parameter-schedule` -/

/-- **`thm:effective-parameter-schedule`** (`06-parameter-schedule.tex`, label
line 1975, statement lines 1977--2081).

The frozen theorem is explicitly *numerical*: line 2077, "This numerical theorem
is deliberately stated for a candidate context and does not invoke
`thm:one-level`", and lines 2078--2081 defer the construction of `Pi`, `c_2` and
`T` to `thm:effective-materialization`.  Accordingly the certificate machinery --
`Cert_c`, `TypeFacts`, `InputEnvelope`, `NumChecked`, `Successor_16` -- is
`PARAM-001` and enters here as **named hypotheses** on abstract root tokens
(GAP-EXPOSED 2); it is neither axiomatized nor packaged as an opaque certificate.

What is proved is the numerical residue the frozen proof actually performs:

1. simultaneous eligibility of every earlier cutoff, from the banked
   `IterationAssembly.cumulativeThreshold` (frozen proof lines 2086--2093);
2. the same at the fixed index `i < j`;
3. the frozen successor exponent `c_{i+1} = 16(c_i + 1)` with `K_rec = 16` fixed
   before the recursion (lines 1980--1984, and `eq:parameter-recursion`,
   label line 1993, display lines 1986--1994);
4. the four principal successor rows under the envelope (lines 2059--2069);
5. **every auxiliary root** under the *same* envelope -- frozen lines 2102--2105,
   "by definition, every named successor root is bounded by
   `E_{16(c_i+1)}(n) = E_{c_{i+1}}(n)`.  **No inference from a degree annotation
   is used.**"  Accordingly the bound is transported from the rootwise hypothesis
   and never from a degree;
6. the `AuxOut` set identity of lines 2043--2052, "Define, **without adding a new
   root**": every auxiliary root is a successor root and is not principal;
7. the exclusion of lines 2057--2058, "It contains neither raw `q_2` nor raw
   `N_2`, source carrier sizes, incoming carrier sizes, or physical carrier
   cardinalities" -- transcribed as: tokens that are not successor roots are not
   auxiliary roots;
8. envelope persistence `E_{c_i}(n) <= E_{c_{i+1}}(n)`.

The separate numerical source-width row of lines 2071--2076 is `sourceWidthRow`
below, not a conjunct here, because the frozen text controls it "separately" and
because `sourceWidth_enters_only_logarithmically` shows the raw width is **not**
under the envelope.

General in the root token type, in all three recorded lists, in the valuation, in
the cutoff function and in `n, i, j`.  `effectiveParameterSchedule_fires`
inhabits every hypothesis with a nonempty root list whose `AuxOut` is a proper
nonempty subset, so no conjunct is vacuously true.

Reader counterpart: `thm:paper-effective-level`'s displayed successor bound,
`05-iteration.tex:221--226`. -/
theorem effectiveParameterSchedule {α : Type*} [DecidableEq α]
    (nstep : ℕ → ℕ) (val : α → ℕ) (roots principal banned : List α)
    (n j i : ℕ) (hij : i < j) (hn : nval nstep j ≤ n)
    (hprincipal : ∀ p ∈ principal, p ∈ roots)
    (hbanned : ∀ b ∈ banned, b ∉ roots)
    (hsucc : ∀ r ∈ roots, val r ≤ envE (cexp (i + 1)) n) :
    (∀ r, r < j → nstep (cexp r) ≤ n) ∧
      nstep (cexp i) ≤ n ∧
      cexp (i + 1) = 16 * (cexp i + 1) ∧
      (∀ p ∈ principal, val p ≤ envE (cexp (i + 1)) n) ∧
      (∀ A ∈ auxOut roots principal, val A ≤ envE (cexp (i + 1)) n) ∧
      (∀ A ∈ auxOut roots principal, A ∈ roots ∧ A ∉ principal) ∧
      (∀ b ∈ banned, b ∉ auxOut roots principal) ∧
      envE (cexp i) n ≤ envE (cexp (i + 1)) n := by
  obtain ⟨-, helig, -, -⟩ := cumulativeThreshold nstep n j hn
  refine ⟨helig, helig i hij, rfl, fun p hp => hsucc p (hprincipal p hp),
    ?_, ?_, ?_, ?_⟩
  · intro A hA
    exact hsucc A ((auxOut_spec roots principal A).1 hA).1
  · intro A hA
    exact (auxOut_spec roots principal A).1 hA
  · intro b hb hcon
    exact hbanned b hb ((auxOut_spec roots principal b).1 hcon).1
  · exact envE_mono_exp n (Nat.le_of_lt (cexp_ge_three_and_lt i).2)

/-- **The separate numerical source-width row**
(`06-parameter-schedule.tex:2071--2076`):

```
q_2 < 24 s |E(G)|,      log_2 q_2 <= E_{c_{i+1}}(n).
```

Frozen line 2081: "while the numerical source width is controlled **separately**
by ...".  Two different facts about two different quantities, so they are two
binders and two conclusions; the raw width is bounded by the source graph, and
only its binary length is bounded by the envelope.  Frozen
`11-one-level-assembly.tex:886--888` gives the reason: "neither `q_2` nor the
numerical source size appears as a multiplicative factor in the logarithmic
wrapper dimension; they enter through `Z_N`."

`sourceWidth_enters_only_logarithmically` is the pole: a width can satisfy the
logarithmic row while grossly violating the envelope, so the two rows are not
interchangeable and the separation is content.

General in the width, the slab count, the edge count, the exponent and `n`.

Reader counterpart: `05-iteration.tex:178`, "the numerical source width
`q_{2,i}` enters this logarithmic carrier bound only through `log q_{2,i}`". -/
theorem sourceWidthRow (q2 s edges c n : ℕ)
    (hgraph : q2 < 24 * s * edges)
    (hlog : Nat.clog 2 q2 ≤ envE c n) :
    q2 < 24 * s * edges ∧ Nat.clog 2 q2 ≤ envE c n ∧ q2 ≤ 2 ^ envE c n := by
  refine ⟨hgraph, hlog, ?_⟩
  exact le_trans (Nat.le_pow_clog (by norm_num) q2)
    (Nat.pow_le_pow_right (by norm_num) hlog)

/-! ## Part 5b: the two pinned legal arrows

One pole and five witnesses below are arrow-shaped.  Each is pinned at one of
these two records, and both are legal in exactly the sense recorded in the module
header -- `q_1 = 2^a - 2` with `a >= 3` (a *field* guard, discharged by the
record), `t_2 >= 8 q_1`, `4 t_2 <= q_2`, `s >= 4` a power of two, `q >= 2` and
`Q >= 2^4`.  Nothing beyond those five displays is claimed of either arrow, and
neither is a **realized** `step:I-07` arrow (`eq:t2-search` forces
`t_2 = 2^{k_2}` with `k_2 >= 2^19`); both are candidate-context arrows, which is
what `thm:effective-parameter-schedule` is stated for. -/

/-- **The minimal legal arrow at the banked entry parameters.**

`w_q = 3` (`q = 8`) and `r_Q = 13` (`Q = 8192`) are the banked entry parameters
of `EntryGates.directEntryGates_fires`.  `a = 3` is the frozen Stage-1 floor of
`07-one-level-construction.tex:118`, so `q_1 = 2^3 - 2 = 6`.  `log_2 s = 2`
gives `s = 4`, the guarded-source floor of `04-guarded-source.tex:281` and
`04-guarded-source.tex:389` ("Let `s >= 4` be a power of two").
`log_2 t_2 = 6`
gives `t_2 = 64`, the least power of two clearing the first row `t_2 >= 8 q_1`
of `eq:stage2-structural-gates` (`06-parameter-schedule.tex`, label line 848),
since `8 q_1 = 48`.  `log_2 q_2 = 8` gives `q_2 = 256`, the least power of two
clearing that display's second row `4 t_2 <= q_2`, since `4 t_2 = 256`.

This is the smallest tuple the six-field record can carry that clears every
frozen row it is able to evaluate; `arrowSize_fires_at_banked_entry_parameters`
checks all of them in the kernel. -/
def minimalLegalArrow : ArrowSize := ⟨3, 13, 8, 2, 6, 3, by norm_num⟩

@[simp] lemma minimalLegalArrow_wq : minimalLegalArrow.wq = 3 := rfl

@[simp] lemma minimalLegalArrow_rQv : minimalLegalArrow.rQv = 13 := rfl

@[simp] lemma minimalLegalArrow_wq2 : minimalLegalArrow.wq2 = 8 := rfl

@[simp] lemma minimalLegalArrow_q1 : minimalLegalArrow.q1 = 6 := rfl

@[simp] lemma minimalLegalArrow_sVal : minimalLegalArrow.sVal = 4 := rfl

@[simp] lemma minimalLegalArrow_t2Val : minimalLegalArrow.t2Val = 64 := rfl

/-- The driver of `minimalLegalArrow` at the seed `z = 0` and source size `1`:
`max{1, 0, floor log_2 3, 8, floor log_2 6, 2, 6} = 8`.  The two genuine floors
are computed, not assumed; `floor log_2 6 = 2` is the entry `aux 18--19` show is
strictly below `ceil log_2 6 = 3`. -/
@[simp] lemma minimalLegalArrow_driver_zero_one :
    minimalLegalArrow.driver 0 1 = 8 := by
  have hlog3 : Nat.log 2 (1 + 2) = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hlog6 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [show minimalLegalArrow.driver 0 1 = sizeDriver 0 1 6 8 2 6 from rfl]
  simp only [sizeDriver, maxFrom_cons, maxFrom_nil, hlog3, hlog6]
  norm_num

/-- The driver of `minimalLegalArrow` at incoming side length `z` and source
size `1` is `max{z, 8}`: the six frozen entries other than `z_i` contribute
`max{1, 1, 8, 2, 2, 6} = 8`, so the driver moves exactly when the incoming side
length passes `log_2 q_2`.  General in `z`. -/
lemma minimalLegalArrow_driver (z : ℕ) :
    minimalLegalArrow.driver z 1 = max z 8 := by
  have hlog3 : Nat.log 2 (1 + 2) = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hlog6 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [show minimalLegalArrow.driver z 1 = sizeDriver z 1 6 8 2 6 from rfl]
  simp only [sizeDriver, maxFrom_cons, maxFrom_nil, hlog3, hlog6]
  omega

/-- The raw majorant `exp:E-14-raw` of `minimalLegalArrow` at the recorded
coefficient `C_dim = 2` and source size `1`:
`2 * (t_2 + s(q_1 + s) + 1) * Z = 2 * 105 * Z`.  General in the driver value, so
the multiplicity is exercised as a coefficient and not only at one point. -/
lemma minimalLegalArrow_rawMajorant (z : ℕ) :
    minimalLegalArrow.rawMajorant 2 z 1 = 210 * minimalLegalArrow.driver z 1 := by
  rw [show minimalLegalArrow.rawMajorant 2 z 1
      = rawSideMajorant 2 minimalLegalArrow.t2Val minimalLegalArrow.sVal
          minimalLegalArrow.q1 (minimalLegalArrow.driver z 1) from rfl,
    minimalLegalArrow_t2Val, minimalLegalArrow_sVal, minimalLegalArrow_q1]
  norm_num [rawSideMajorant, dimMultiplicity]

/-! ## Part 6: statement poles

Each refutes a neighbouring reading that typechecks.  A green build sees none of
them. -/

/-- **Pole 1: the `exp:E-14-raw` hypothesis is not free.**

At `minimalLegalArrow`, with `C_dim = 2`, `z = 0` and `n = 1`, the driver is
`max{1, 0, 1, 8, 2, 2, 6} = 8`, the multiplicity is
`t_2 + s(q_1 + s) + 1 = 64 + 4*10 + 1 = 105`, and the raw majorant is
`2 * 105 * 8 = 1680`.  A `2^1681 x 1` matrix has `z_N = 1681`, so the checked
size-successor row genuinely constrains: a formalization that dropped it would
be claiming `2^1681 <= 2^1680`.

Every parameter here clears the frozen rows listed on `minimalLegalArrow` -- in
particular `4 t_2 <= q_2` (`256 <= 256`), the row the first round violated, and
`q_1 = 2^3 - 2`, which the record's own guard now enforces.

This is the LANE-GATE-4c line for `uniformSideMajorant`: its conclusion is an
upper bound, and the trivial way to obtain such a bound -- assert it for every
matrix -- is refuted here at a legal arrow rather than at a gate-violating
one. -/
theorem uniformSideMajorant_hypothesis_not_free :
    minimalLegalArrow.rawMajorant 2 0 1 = 1680 ∧
      sideExponent (rowsCard (fun (_ : Fin (2 ^ 1681)) (_ : Fin 1) => true))
        (colsCard (fun (_ : Fin (2 ^ 1681)) (_ : Fin 1) => true)) = 1681 ∧
      ¬ sideExponent (rowsCard (fun (_ : Fin (2 ^ 1681)) (_ : Fin 1) => true))
          (colsCard (fun (_ : Fin (2 ^ 1681)) (_ : Fin 1) => true))
        ≤ minimalLegalArrow.rawMajorant 2 0 1 := by
  have hmaj : minimalLegalArrow.rawMajorant 2 0 1 = 1680 := by
    rw [minimalLegalArrow_rawMajorant, minimalLegalArrow_driver_zero_one]
  have hcbig : Nat.clog 2 (2 ^ 1681) = 1681 := Nat.clog_pow 2 1681 (by norm_num)
  have hc1 : Nat.clog 2 1 = 0 := Nat.clog_one_right 2
  have hz : sideExponent (rowsCard (fun (_ : Fin (2 ^ 1681)) (_ : Fin 1) => true))
      (colsCard (fun (_ : Fin (2 ^ 1681)) (_ : Fin 1) => true)) = 1681 := by
    simp only [sideExponent, rowsCard, colsCard, Fintype.card_fin, hcbig, hc1]
    norm_num
  exact ⟨hmaj, hz, by rw [hmaj, hz]; norm_num⟩

/-- **Pole 2: `C_size` is not a function of the four-row degree summary.**

`06-parameter-schedule.tex:1688`: "Equation `eq:Csize-literal-producer`, rather
than the four-row degree summary, produces `C_size >= 2`."  Two recorded first-pass
tables with **identical degree profiles** -- both a single row of degree `8`, the
largest entry of the frozen table -- return `6561` and `13122`.  No function of
the degree summary alone can therefore be `C_size`, and a formalization that read
the constant off the table of lines 1643--1656 would be reading a different
number. -/
theorem degreeSummary_does_not_determine_csize :
    ([(1, 8)] : List (ℕ × ℕ)).map Prod.snd
        = ([(2, 8)] : List (ℕ × ℕ)).map Prod.snd ∧
      csizeLiteral [(1, 8)] [] = 6561 ∧
      csizeLiteral [(2, 8)] [] = 13122 ∧
      csizeLiteral [(1, 8)] [] ≠ csizeLiteral [(2, 8)] [] := by
  refine ⟨rfl, by decide, by decide, by decide⟩

/-- **Pole 3: the `T3` pass carries no `3^{d_u}` shift.**

`06-parameter-schedule.tex:1634--1637`: the seven `T3` rows "feed
`2^{C_size A_*^2}` directly and undergo no `L+2`-to-`L` shift", whereas every
first-pass row carries `(L+2)^{d_u} <= 3^{d_u} L^{d_u}`.  Moving one row between
the two lists changes the produced constant from `5` to `15`, so the two passes
are not interchangeable and the frozen split is content rather than
presentation. -/
theorem t3Pass_carries_no_shift_pole :
    csizeLiteral [] [5] = 5 ∧ csizeLiteral [(5, 1)] [] = 15 ∧
      csizeLiteral [] [5] ≠ csizeLiteral [(5, 1)] [] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Pole 4: the two interlace widths are not interchangeable.**

`exp:E-14-step` is asymmetric -- `Q` exponentiates the row branch and multiplies
the column branch.  At `w_q = 1`, `r_Q = 2`, `z_N = 1` the frozen step returns
`8`; transposing the two exponents returns `6`.  This is the `q`/`Q` separation
that a single numeric check cannot see, at the banked `sideStep`. -/
theorem sideStep_orientation_pole :
    sideStep 1 2 1 = 8 ∧ sideStep 2 1 1 = 6 ∧ sideStep 1 2 1 ≠ sideStep 2 1 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Pole 5: the multiplicity contribution is a product, not a sum.**

`exp:E-14-raw` reads `t_2 + s(q_1 + s) + 1`, with the `s`-fold occurrence of
`q_1 + s` a genuine product.  At the `minimalLegalArrow` values `t_2 = 64`,
`s = 4`, `q_1 = 6` -- so the check runs inside the frozen admissible region,
`t_2 >= 8 q_1` and `q_1 = 2^3 - 2` -- the frozen shape gives
`64 + 4*10 + 1 = 105`; the flattened reading `t_2 + s + q_1 + s + 1` gives `79`.
A formalization that dropped the product would understate the majorant by a
third at legal values, and understating a majorant is exactly the error a green
build cannot detect. -/
theorem dimMultiplicity_is_not_additive :
    dimMultiplicity minimalLegalArrow.t2Val minimalLegalArrow.sVal
        minimalLegalArrow.q1 = 105 ∧
      (64 + 4 + 6 + 4 + 1 : ℕ) = 79 ∧
      dimMultiplicity minimalLegalArrow.t2Val minimalLegalArrow.sVal
        minimalLegalArrow.q1 ≠ (64 + 4 + 6 + 4 + 1 : ℕ) := by
  have h : dimMultiplicity minimalLegalArrow.t2Val minimalLegalArrow.sVal
      minimalLegalArrow.q1 = 105 := by
    rw [minimalLegalArrow_t2Val, minimalLegalArrow_sVal, minimalLegalArrow_q1]
    norm_num [dimMultiplicity]
  exact ⟨h, by norm_num, by rw [h]; norm_num⟩

/-- **Pole 6 (candidate B refuted): raw widths break the row branch.**

Candidate B carries the two interlace widths raw and spells the step with
`Nat.log`.  At `q = 3`, `Q = 1`, `m_N = 1`, `z_N = 0` its step returns
`max{1 * (Nat.log 2 3 + 0), Nat.log 2 1 + 3 * 0} = 1`, while the frozen carrier
equation gives `|Rows(R^+)| = (q m_N)^Q = 3 > 2 = 2^1`.  The floor logarithm of a
non-dyadic width is strictly below the ceiling the estimate needs, so the
candidate's own bound is false at legal-looking values.  The landed exponent
encoding cannot express this error, since `q = 2^{w_q}` by construction. -/
theorem rawWidthEncoding_breaks_the_row_branch :
    Nat.log 2 3 = 1 ∧ Nat.log 2 1 = 0 ∧
      max (1 * (Nat.log 2 3 + 0)) (Nat.log 2 1 + 3 * 0) = 1 ∧
      ¬ ((3 * 1 : ℕ) ^ 1 ≤ 2 ^ max (1 * (Nat.log 2 3 + 0)) (Nat.log 2 1 + 3 * 0)) := by
  have h3 : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h1 : Nat.log 2 1 = 0 := Nat.log_one_right 2
  refine ⟨h3, h1, by rw [h3, h1]; omega, ?_⟩
  rw [h3, h1]
  norm_num

/-- **Pole 7: the raw source width is not under the envelope.**

`06-parameter-schedule.tex:2071--2076` bounds `log_2 q_2`, never `q_2`, by
`E_{c_{i+1}}(n)`, and `11-one-level-assembly.tex:886--888` gives the reason.  At
the envelope value `4` the width `16` satisfies the logarithmic row exactly and
violates the envelope by a factor of four, so the two rows are genuinely
different statements. -/
theorem sourceWidth_enters_only_logarithmically :
    Nat.clog 2 16 = 4 ∧ ¬ ((16 : ℕ) ≤ 4) := by
  have h : Nat.clog 2 16 = 4 := by
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16]; exact Nat.clog_pow 2 4 (by norm_num)
  exact ⟨h, by norm_num⟩

/-! ## Part 7: non-vacuity witnesses

Every new definition and every headline hypothesis bundle is inhabited at legal
parameter values, and the size ladder is exercised where it **grows**. -/

/-- **Witness 1: the driver moves with each of its six entries, and its one
non-dyadic entry is a genuine floor.**

Seven evaluations of `sizeDriver`, one per frozen entry plus the floor: the base
alone gives `1`; the incoming side length gives `7`; the source size gives `6`
(at `n = 62`, `floor log_2 64 = 6`); `log_2 q_2` gives `9`; `floor log_2 q_1`
gives `5` (at `q_1 = 62`); `log_2 s` gives `4`; `log_2 t_2` gives `3`.  All seven
values are distinct, so no entry is silently ignored -- the degeneracy a single
evaluation cannot see.

**This is a statement about `sizeDriver` alone, not about an arrow.**  The six
numbers are driver arguments; no tuple here is claimed to clear
`eq:stage2-structural-gates`, and none is an `ArrowSize`.

The Stage-1 entry is exercised at `q_1 = 62 = 2^6 - 2`, a legal Stage-1 width
(`a = 6` in `eq:stage1-scales`) that is **not** a power of two, and the last
three conjuncts record the consequence the encoding turns on:
`floor log_2 62 = 5` while `ceil log_2 62 = 6`.  Had `q_1` been carried by an
exponent -- refuted Candidate B -- the driver would have read `6` here and the
majorant would have been overstated at a value the paper actually reaches.  The
same numeral `62` in the source-size slot gives `6`, because that entry is
`floor log_2 (n + 2)`; the two are deliberately different, and `aux 19` proves
the gap at *every* legal arrow rather than only at this one. -/
theorem sizeDriver_fires_nondegenerate :
    sizeDriver 0 0 0 0 0 0 = 1 ∧ sizeDriver 7 0 0 0 0 0 = 7 ∧
      sizeDriver 0 62 0 0 0 0 = 6 ∧ sizeDriver 0 0 0 9 0 0 = 9 ∧
      sizeDriver 0 0 62 0 0 0 = 5 ∧ sizeDriver 0 0 0 0 4 0 = 4 ∧
      sizeDriver 0 0 0 0 0 3 = 3 ∧
      (62 : ℕ) = 2 ^ 6 - 2 ∧
      Nat.log 2 62 = 5 ∧ Nat.clog 2 62 = 6 := by
  have hl2 : Nat.log 2 (0 + 2) = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hl64 : Nat.log 2 (62 + 2) = 6 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hl0 : Nat.log 2 0 = 0 := Nat.log_zero_right 2
  have hl62 : Nat.log 2 62 = 5 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hc62 : Nat.clog 2 62 = 6 := by
    have hle : Nat.clog 2 62 ≤ 6 := Nat.clog_le_of_le_pow (by norm_num)
    have hlt : 5 < Nat.clog 2 62 :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by norm_num)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, hl62, hc62⟩ <;>
    simp [sizeDriver, hl2, hl64, hl0, hl62]

/-- **Witness 1b: the driver also fires at the realized `t_2` scale.**

`eq:t2-search` (`06-parameter-schedule.tex`, label line 772) forces a *realized*
`step:I-07` arrow to carry `t_2 = 2^{k_2}` with `k_2 >= max{4, 2^19, m_HS}`,
which is far beyond `minimalLegalArrow`'s `t_2 = 64`.  In the exponent encoding
that scale is free: at `log_2 t_2 = 2^19 = 524288` and
`log_2 q_2 = 524290` -- the least exponent clearing `4 t_2 <= q_2`, since
`4 * 2^524288 = 2^524290` -- the driver is `524290`, and the two evaluable rows
of `eq:stage2-structural-gates` still hold with `q_1 = 6`.

This witness exists so that no reader mistakes the small-`t_2` arrows above for
realized ones; it is **extra**, never a substitute for them, and the two gate
conjuncts are proved without evaluating either tower. -/
theorem sizeDriver_fires_at_realized_t2_scale :
    sizeDriver 0 1 6 524290 2 524288 = 524290 ∧
      8 * 6 ≤ 2 ^ 524288 ∧ 4 * 2 ^ 524288 ≤ 2 ^ 524290 := by
  have hl3 : Nat.log 2 (1 + 2) = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hl6 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp only [sizeDriver, maxFrom_cons, maxFrom_nil, hl3, hl6]
    omega
  · calc (8 : ℕ) * 6 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ 524288 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · calc (4 : ℕ) * 2 ^ 524288 = 2 ^ 2 * 2 ^ 524288 := by norm_num
      _ = 2 ^ 524290 := by rw [← pow_add]
      _ ≤ 2 ^ 524290 := le_refl _

/-- **Witness 2: `exp:E-14-raw` fires at a nondegenerate legal arrow.**

At `minimalLegalArrow` -- `w_q = 3`, `r_Q = 13`, the banked entry parameters of
`EntryGates.directEntryGates_fires` (`q = 8`, `Q = 8192`), with `q_2 = 2^8`,
`s = 2^2`, `t_2 = 2^6` and `q_1 = 2^3 - 2 = 6` -- and at the recorded
coefficient `C_dim = 2`, the driver at `z = 0`, `n = 1` is `8`, the multiplicity
polynomial is `64 + 4*(6+4) + 1 = 105`, and the raw majorant is
`2 * 105 * 8 = 1680`.  Both the coefficient and the multiplicity polynomial are
strictly above their frozen floors, and the majorant moves with the incoming
side length (`z = 100` gives `21000`), so neither factor is degenerate.

Every field of `minimalLegalArrow` clears the frozen rows listed on that
definition; nothing else about the region is asserted here. -/
theorem rawSideMajorant_fires_nondegenerate :
    minimalLegalArrow.driver 0 1 = 8 ∧
      dimMultiplicity minimalLegalArrow.t2Val minimalLegalArrow.sVal
        minimalLegalArrow.q1 = 105 ∧
      minimalLegalArrow.rawMajorant 2 0 1 = 1680 ∧
      minimalLegalArrow.rawMajorant 2 100 1 = 21000 := by
  obtain ⟨hmult, -, -⟩ := dimMultiplicity_is_not_additive
  refine ⟨minimalLegalArrow_driver_zero_one, hmult, ?_, ?_⟩
  · rw [minimalLegalArrow_rawMajorant, minimalLegalArrow_driver_zero_one]
  · rw [minimalLegalArrow_rawMajorant, minimalLegalArrow_driver]
    norm_num

/-- **Witness 3: `C_size` and `W(L)` fire, and both genuinely move.**

A two-row first pass and a two-row `T3` pass: `3^2 * 4 = 36`, `3^1 * 2 = 6`, and
the bare `T3` coefficients `7` and `5`, so the produced constant is `36` -- the
first-pass maximum, strictly above both the frozen floor `2` and every `T3` row,
which is exactly the situation where merging the passes would be invisible.  The
structural majorant at that constant is `2^36` at `L = 1` and `2^{36 * 256}` at
`L = 2`, so the degree-eight exponent is exercised rather than assumed. -/
theorem csizeLiteral_fires_nondegenerate :
    csizeLiteral [(4, 2), (2, 1)] [7, 5] = 36 ∧
      structuralW 36 1 = 2 ^ 36 ∧ structuralW 36 2 = 2 ^ 9216 ∧
      structuralW 36 1 ≠ structuralW 36 2 := by
  have hA : structuralW 36 1 = 2 ^ 36 := by norm_num [structuralW]
  have hB : structuralW 36 2 = 2 ^ 9216 := by norm_num [structuralW]
  refine ⟨by decide, hA, hB, ?_⟩
  rw [hA, hB]
  have hlt : (2 : ℕ) ^ 36 < 2 ^ 9216 :=
    Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  omega

/-- **Witness 4: the arrow record has a nondegenerate inhabitant that clears
every frozen row it can evaluate.**

`EntryGates.directEntryGates_fires` pins `b_out = 1`, `delta_U = 1/60`,
`r_Q = 13`, `Q = 8192`; the inner width is the banked `w_q = 3`, i.e. `q = 8`.
The conjuncts are, in order and with the display each one discharges:

* `r_Q` is the route's own bridge exponent and `Q = 8192` -- banked
  `EntryGates.directEntryGates_fires`;
* `1 <= w_q`, i.e. `q >= 2` -- `02-mechanical-contract.tex:771--775`;
* `4 <= r_Q` -- the banked `EntryGates.four_le_rQ` floor;
* `q_1 = 2^3 - 2 = 6` -- `eq:stage1-scales` (`06-parameter-schedule.tex`, label
  line 319) and `07-one-level-construction.tex:118`.  It is discharged by the
  record's own guard field, not by this witness;
* `8 q_1 <= t_2`, i.e. `48 <= 64` -- the **first** row of
  `eq:stage2-structural-gates` (label line 848), which the parked first round
  had no inhabitant for;
* `4 t_2 <= q_2`, i.e. `256 <= 256` -- the **second** row of that display;
* `4 <= s` and `s` a power of two -- `04-guarded-source.tex:281` and
  `04-guarded-source.tex:389`;
* `q != Q`, so the two interlace widths are **different** and the orientation is
  observable here and not only in the abstract pole.

Nothing else is claimed: the remaining rows of `eq:stage2-structural-gates`
mention `zeta`, `b_1`, `delta_min`, `delta_term`, `mu_P`, `eta_R`, `v_max`,
`t_ref` and `|C_1|`, which are not fields of this record, and this arrow is a
candidate-context arrow rather than a realized one (`eq:t2-search`; see
`sizeDriver_fires_at_realized_t2_scale`). -/
theorem arrowSize_fires_at_banked_entry_parameters :
    rQ 1 (1 / 60 : ℝ) = minimalLegalArrow.rQv ∧
      Qwidth 1 (1 / 60 : ℝ) = 8192 ∧
      1 ≤ minimalLegalArrow.wq ∧
      4 ≤ minimalLegalArrow.rQv ∧
      minimalLegalArrow.q1 = 2 ^ 3 - 2 ∧
      8 * minimalLegalArrow.q1 ≤ minimalLegalArrow.t2Val ∧
      4 * minimalLegalArrow.t2Val ≤ 2 ^ minimalLegalArrow.wq2 ∧
      4 ≤ minimalLegalArrow.sVal ∧
      2 ^ minimalLegalArrow.wq ≠ Qwidth 1 (1 / 60 : ℝ) := by
  obtain ⟨-, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  refine ⟨hrQ, hQ, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  change (2 : ℕ) ^ 3 ≠ Qwidth 1 (1 / 60 : ℝ)
  rw [hQ]; norm_num

/-- **Witness 5: the one-arrow size step fires at `minimalLegalArrow`.**

At the banked `b_out = 1`, `delta_U = 1/60`, `r_Q = 13`, at the inner width
`w_q = 3`, and at a `4 x 8` incoming matrix, `z_N = 3` and the raw majorant is
`1680`, so the frozen row of `exp:E-14-raw` is available; the step then returns
`sideStep 3 13 1680 = max{8192 * 1683, 13 + 8 * 1680} = 13787136`, and both
carriers of the pinned output are under `2^{13787136}`.  The two branches are
wildly unequal (`13787136` against `13453`), so the maximum is genuinely taken.

Every hypothesis of `arrowSizeStep` is discharged at these values, which is the
consistency check for its bundle: the guard `1 <= w_q`, the identification
`hQ : rQ b_out delta_U = r_Q` at the banked entry parameters, and the checked
size-successor row `hrow` at a genuine incoming matrix.  Since the bundle is
inhabited, it is consistent, and the theorem is not vacuous. -/
theorem arrowSizeStep_fires :
    minimalLegalArrow.rawMajorant 2 0 1 = 1680 ∧
      sideExponent (rowsCard (fun (_ : Fin 4) (_ : Fin 8) => true))
        (colsCard (fun (_ : Fin 4) (_ : Fin 8) => true)) = 3 ∧
      minimalLegalArrow.stepBound 2 0 1 = 13787136 ∧
      rowsCard (levelOutput (fun (_ : Fin 4) (_ : Fin 8) => true) 3 1
          (1 / 60 : ℝ))
        ≤ 2 ^ minimalLegalArrow.stepBound 2 0 1 ∧
      colsCard (levelOutput (fun (_ : Fin 4) (_ : Fin 8) => true) 3 1
          (1 / 60 : ℝ))
        ≤ 2 ^ minimalLegalArrow.stepBound 2 0 1 := by
  obtain ⟨-, -, hrQ, -, -, -, -⟩ := directEntryGates_fires
  have hmaj : minimalLegalArrow.rawMajorant 2 0 1 = 1680 := by
    obtain ⟨-, -, h, -⟩ := rawSideMajorant_fires_nondegenerate
    exact h
  have hc4 : Nat.clog 2 4 = 2 := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h]; exact Nat.clog_pow 2 2 (by norm_num)
  have hc8 : Nat.clog 2 8 = 3 := by
    have h : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h]; exact Nat.clog_pow 2 3 (by norm_num)
  have hz : sideExponent (rowsCard (fun (_ : Fin 4) (_ : Fin 8) => true))
      (colsCard (fun (_ : Fin 4) (_ : Fin 8) => true)) = 3 := by
    simp only [sideExponent, rowsCard, colsCard, Fintype.card_fin, hc4, hc8]
    norm_num
  have hstep : minimalLegalArrow.stepBound 2 0 1 = 13787136 := by
    rw [show minimalLegalArrow.stepBound 2 0 1
        = sideStep minimalLegalArrow.wq minimalLegalArrow.rQv
            (minimalLegalArrow.rawMajorant 2 0 1) from rfl,
      minimalLegalArrow_wq, minimalLegalArrow_rQv, hmaj]
    norm_num [sideStep]
  have hrow : sideExponent (rowsCard (fun (_ : Fin 4) (_ : Fin 8) => true))
      (colsCard (fun (_ : Fin 4) (_ : Fin 8) => true))
      ≤ minimalLegalArrow.rawMajorant 2 0 1 := by
    rw [hz, hmaj]; norm_num
  obtain ⟨hr, hc, -⟩ := arrowSizeStep (fun (_ : Fin 4) (_ : Fin 8) => true)
    minimalLegalArrow 2 0 1 1 (1 / 60 : ℝ) (by norm_num) hrQ hrow
  exact ⟨hmaj, hz, hstep, hr, hc⟩

/-- The arrow used by the growth witness: `w_q = 1` (i.e. `q = 2`, the frozen
legality floor of `02-mechanical-contract.tex:771--775`), `r_Q = 4`, and the same
Stage-1/Stage-2 tuple as `minimalLegalArrow` -- `q_2 = 2^8`, `s = 2^2`,
`t_2 = 2^6`, `a = 3` hence `q_1 = 6`.  It therefore clears the same four displays
listed on `minimalLegalArrow` (`eq:stage1-scales`, the two evaluable rows of
`eq:stage2-structural-gates`, and `s >= 4` a power of two) and nothing further;
like that arrow it is a candidate-context arrow, not a realized one.  The two
interlace exponents are dropped as far as the recorded bounds allow, so that the
growth below is *not* an artefact of a large `Q`.

**`r_Q = 4` is the *proved-bound* floor, not a realizable exponent.**  The banked
`EntryGates.four_le_rQ` derives `4 <= r_Q` from the `16` branch of `Q_0`, and
that is all this witness leans on.  The realizable floor is strictly larger:
`EntryGates.Q0` also carries the branch `8 / deltaFixed = 80`, so `Q_0 >= 80 > 64`
at every `(b_out, delta_U)` and hence `r_Q >= 7` for every genuine entry.  No
claim is made here that some `(b_out, delta_U)` realizes `r_Q = 4`; the arrow is
a legal *value* of the record, and the realized exponent is exercised separately
at `r_Q = 13 = rQ 1 (1/60)` by `arrowSize_fires_at_banked_entry_parameters` and
`arrowSizeStep_fires`. -/
def witnessArrow : ArrowSize := ⟨1, 4, 8, 2, 6, 3, by norm_num⟩

/-- The size ladder generated by `witnessArrow` at `C_dim = 1` and source size
`1`, i.e. `z_{i+1} = z_{i+1}^+` exactly.  Taking the ladder to be its own step
bound discharges the transport hypothesis of `iteratedSizeMajorant` by
reflexivity, so the witness tests the *arithmetic*, not the transport. -/
def witnessZ : ℕ → ℕ
  | 0 => 0
  | i + 1 => witnessArrow.stepBound 1 (witnessZ i) 1

/-- **Witness 6: the iterated size majorant fires on a strictly growing ladder.**

`13-iteration-assembly.tex:519--571` at `k = 2`, `n = 1`, `C_dim = 1` and the
legal `witnessArrow`.  The ladder is

```
z_0 = 0,   z_1 = 13456,   z_2 = 22606096,
```

so it **grows** at every arrow -- the degeneracy a constant or eventually
constant ladder would hide.  Each hypothesis of `iteratedSizeMajorant` is
discharged at these values: the seed bound against `E_{c_0}(1) = 2^{27}`, the
transport by reflexivity, and the size-successor row from
`13456 <= 2^{14} <= 2^{3^{64}} = E_{c_1}(1)` and
`22606096 <= 2^{25} <= 2^{3^{1040}} = E_{c_2}(1)`.  The bundle is therefore
consistent, and the delivered conclusion is a real bound on a moving quantity.

The numerals moved with the repair: raising `t_2` from `2` to the legal `64` and
`q_1` from the illegal `2` to `2^3 - 2 = 6` multiplies the multiplicity
polynomial from `11` to `105`, so the parked round's `544 / 95760` are *not*
these values, and the envelope headroom was recomputed rather than inherited. -/
theorem iteratedSizeMajorant_fires_growing :
    witnessZ 0 = 0 ∧ witnessZ 1 = 13456 ∧ witnessZ 2 = 22606096 ∧
      witnessZ 0 < witnessZ 1 ∧ witnessZ 1 < witnessZ 2 ∧
      (∀ i, i ≤ 2 → witnessZ i ≤ envE (cexp i) 1) ∧
      (∀ i, i ≤ 2 → witnessZ i ≤ envE (cexp 2) 1) := by
  have hell : ellN 1 = 3 := envelope_fires_nondegenerate.1
  have hl3 : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hl6 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hdrv : ∀ z : ℕ, witnessArrow.driver z 1 = max z 8 := by
    intro z
    change sizeDriver z 1 6 8 2 6 = max z 8
    simp only [sizeDriver, maxFrom_cons, maxFrom_nil, hl3, hl6]
    omega
  have hraw : ∀ z : ℕ, witnessArrow.rawMajorant 1 z 1 = 105 * max z 8 := by
    intro z
    change rawSideMajorant 1 (2 ^ 6) (2 ^ 2) 6 (witnessArrow.driver z 1)
      = 105 * max z 8
    rw [hdrv z]
    simp only [rawSideMajorant, dimMultiplicity]
    norm_num
  have hstepEq : ∀ z : ℕ, witnessArrow.stepBound 1 z 1
      = max (16 * (1 + 105 * max z 8)) (4 + 2 * (105 * max z 8)) := by
    intro z
    change sideStep 1 4 (witnessArrow.rawMajorant 1 z 1)
      = max (16 * (1 + 105 * max z 8)) (4 + 2 * (105 * max z 8))
    rw [hraw z]
    simp only [sideStep]
    norm_num
  have h1 : witnessZ 1 = 13456 := by
    change witnessArrow.stepBound 1 (witnessZ 0) 1 = 13456
    rw [show witnessZ 0 = 0 from rfl, hstepEq 0]
    norm_num
  have h2 : witnessZ 2 = 22606096 := by
    change witnessArrow.stepBound 1 (witnessZ 1) 1 = 22606096
    rw [h1, hstepEq 13456]
    norm_num
  -- the two envelope values, without evaluating the towers
  have henv0 : envE (cexp 0) 1 = 2 ^ 27 := by
    simp only [envE, hell, cexp_zero]
    norm_num
  have henv1 : (13456 : ℕ) ≤ envE (cexp 1) 1 := by
    have hc : cexp 1 = 64 := by decide
    have hexp : (14 : ℕ) ≤ 3 ^ 64 :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
        (by norm_num : (3 : ℕ) ≤ 64))
    calc (13456 : ℕ) ≤ 2 ^ 14 := by norm_num
      _ ≤ 2 ^ (3 : ℕ) ^ 64 := Nat.pow_le_pow_right (by norm_num) hexp
      _ = envE (cexp 1) 1 := by simp only [envE, hell, hc]
  have henv2 : (22606096 : ℕ) ≤ envE (cexp 2) 1 := by
    have hc : cexp 2 = 1040 := by decide
    have hexp : (25 : ℕ) ≤ 3 ^ 1040 :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
        (by norm_num : (3 : ℕ) ≤ 1040))
    calc (22606096 : ℕ) ≤ 2 ^ 25 := by norm_num
      _ ≤ 2 ^ (3 : ℕ) ^ 1040 := Nat.pow_le_pow_right (by norm_num) hexp
      _ = envE (cexp 2) 1 := by simp only [envE, hell, hc]
  obtain ⟨hall, hallk⟩ :=
    iteratedSizeMajorant 1 2 1 witnessZ (fun _ => witnessArrow)
      (by change (0 : ℕ) < envE (cexp 0) 1; rw [henv0]; norm_num)
      (by intro i _; exact le_refl _)
      (by
        intro i hi _
        interval_cases i
        · change witnessArrow.stepBound 1 (witnessZ 0) 1 ≤ envE (cexp 1) 1
          rw [show witnessArrow.stepBound 1 (witnessZ 0) 1 = 13456 from h1]
          exact henv1
        · change witnessArrow.stepBound 1 (witnessZ 1) 1 ≤ envE (cexp 2) 1
          rw [show witnessArrow.stepBound 1 (witnessZ 1) 1 = 22606096 from h2]
          exact henv2)
  refine ⟨rfl, h1, h2, ?_, by rw [h1, h2]; norm_num, hall, hallk⟩
  rw [h1]
  change (0 : ℕ) < 13456
  norm_num

/-- **Witness 7: the effective parameter schedule fires on a nonempty root
table.**

Four root tokens `0, 1, 2, 3` with `principal = [0, 1]` the two carrier rows and
`banned = [9]` a raw source width that is not a successor root at all.  Then
`AuxOut = [2, 3]` is a **proper nonempty** subset of the roots -- not empty (which
would make conjunct 5 vacuous) and not everything (which would make conjunct 6
vacuous) -- and the banned token is excluded.  The cutoff function is the
non-constant `n_step(c) = c`, so `n_val(2) = 64` is genuinely a maximum, and the
eligibility conclusion is exercised at `n = 64`.

Every hypothesis of `effectiveParameterSchedule` is discharged here, which is the
consistency check for its bundle. -/
theorem effectiveParameterSchedule_fires :
    auxOut [0, 1, 2, 3] [0, 1] = [2, 3] ∧
      nval (fun c => c) 2 = 64 ∧
      (∀ r, r < 2 → (fun c => c) (cexp r) ≤ 64) ∧
      cexp 1 = 16 * (cexp 0 + 1) ∧
      (9 : ℕ) ∉ auxOut [0, 1, 2, 3] [0, 1] ∧
      auxOut [0, 1, 2, 3] [0, 1] ≠ [] ∧
      auxOut [0, 1, 2, 3] [0, 1] ≠ [0, 1, 2, 3] := by
  have hnval : nval (fun c => c) 2 = 64 := by decide
  have hell64 : ellN 64 = 3 := by
    change Nat.find (ellN_exists 64) = 3
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro m hm
    interval_cases m <;> decide
  have hge : (4 : ℕ) ≤ envE (cexp 1) 64 := by
    have hc : cexp 1 = 64 := by decide
    have hexp : (2 : ℕ) ≤ 3 ^ 64 :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
        (by norm_num : (1 : ℕ) ≤ 64))
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 : ℕ) ^ 64 := Nat.pow_le_pow_right (by norm_num) hexp
      _ = envE (cexp 1) 64 := by simp only [envE, hell64, hc]
  obtain ⟨helig, -, hrec, -, -, -, -, -⟩ :=
    effectiveParameterSchedule (α := ℕ) (fun c => c) (fun a => a)
      [0, 1, 2, 3] [0, 1] [9] 64 2 0 (by norm_num) (le_of_eq hnval)
      (by decide) (by decide)
      (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        change r ≤ envE (cexp 1) 64
        omega)
  exact ⟨by decide, hnval, helig, hrec, by decide, by decide, by decide⟩

/-- **Witness 8: the separate numerical source-width row is inhabited.**

`06-parameter-schedule.tex:2071--2076` at the `minimalLegalArrow` source width
`q_2 = 2^8 = 256` and slab count `s = 4`, with `|E(G)| = 100`: the graph row
`q_2 < 24 s |E(G)|` reads `256 < 9600`, and the logarithmic row
`ceil log_2 q_2 = 8 <= E_{c_0}(1) = 2^{27}` holds with room.  Both hypotheses of
`sourceWidthRow` are therefore discharged simultaneously at values the record
itself carries, so that bundle is consistent and its conclusion is not vacuous.

The witness also shows the two rows are not the same statement: `q_2 = 256` is
far above `ceil log_2 q_2 = 8`, which is the separation
`sourceWidth_enters_only_logarithmically` pins in general. -/
theorem sourceWidthRow_fires :
    (256 : ℕ) < 24 * 4 * 100 ∧
      Nat.clog 2 256 = 8 ∧
      Nat.clog 2 256 ≤ envE (cexp 0) 1 ∧
      (256 : ℕ) ≤ 2 ^ envE (cexp 0) 1 := by
  have hell : ellN 1 = 3 := envelope_fires_nondegenerate.1
  have henv0 : envE (cexp 0) 1 = 2 ^ 27 := by
    simp only [envE, hell, cexp_zero]
    norm_num
  have hc256 : Nat.clog 2 256 = 8 := by
    have h : (256 : ℕ) = 2 ^ 8 := by norm_num
    rw [h]; exact Nat.clog_pow 2 8 (by norm_num)
  have hlog : Nat.clog 2 256 ≤ envE (cexp 0) 1 := by
    rw [hc256, henv0]; norm_num
  obtain ⟨hgraph, hlog', hraw⟩ :=
    sourceWidthRow 256 4 100 (cexp 0) 1 (by norm_num) hlog
  exact ⟨hgraph, hc256, hlog', hraw⟩

end EthInapproximability.ParameterizedNP.SizePropagation
