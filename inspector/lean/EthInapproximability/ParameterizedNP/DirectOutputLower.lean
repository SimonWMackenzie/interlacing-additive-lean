import EthInapproximability.ParameterizedNP.DirectOutput

/-!
# Parameterized NP route: the lower-direction apparatus of `eq:direct-output`

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-OUTPUT-002`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1i` tranche as the **lower** direction of `eq:direct-output`: the
entry parameters of `sec:direct-entry`, the width bounds
`eq:direct-Q-bounds`, the exact rational search `eq:direct-d-search` with its
window `eq:direct-d-window`, the ceiling-safe count
`eq:direct-good-copy-count`, the level step that feeds the banked defect
induction, and the three output rungs they assemble into.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`,
and all are in `sections/10-direct-bridge.tex`.

* `eq:direct-input` (label line 11, display lines 7--12) — the two
  common-threshold clauses `D(W[1, θ, 1 - δ_U]) ≥ C_W` and
  `Λ_W(1, θ, y) ≥ C_W - 1`.  They are carried here as the **explicit named
  binders** `hNear` and `hInput`, exactly as the frozen section carries them;
  nothing is axiomatized.
* §`sec:direct-entry` "Entry at the requested robust depth" (label line 390):
  * lines 393--396, `x_out = 2^{-b_out}` and `L = ln(1/x_out) = b_out ln 2`;
  * lines 398--400, "Because `λ = -ln(1 - δ_U) ≥ δ_U` and `ln 2 < 1`, the
    definition of `Q_0`, the choice `Q < 2 Q_0`, and `eq:direct-entry-gates`
    imply";
  * `eq:direct-Q-bounds` (label line 407, display lines 402--407),
    `Q ≥ 8L/(δλ)`, `Q ≥ 8/δ`, `Q θ < δ/2`;
  * `eq:direct-d-search` (label line 414, display lines 412--414),
    `d = min{e ≥ 1 : (1 - δ_U)^e ≤ 2^{-b_out}}`, with the sentence at lines
    410--411 that it is computed "by exact rational comparisons";
  * `eq:direct-d-window` (label line 419, display lines 417--419),
    `(d - 1) λ < L ≤ d λ`, and line 416, "Minimality is equivalent to";
  * lines 421--428, `a_t = r_Q - t` and `p_t = 2^{a_t - 1} + d` for
    `t = 0, 1, 2`, with "Then `p_t > 2^{a_t - 1}`, the strict copy-count
    hypothesis of `lem:defect-induction`";
  * `eq:direct-good-copy-count` (label line 435, display lines 432--435),
    `(p_t - 1) m + (Q - p_t + 1)(A_{a_t} - 1) < Q m y / 2^t`, together with
    the ceiling bookkeeping at lines 437--450 and its conclusion `p_t ≤ Q`;
  * lines 452--463, the transposed member, the good-copy dichotomy, and "Hence
    at least `p_t` copies are good";
  * lines 465--478, "Choose any `p_t` good copies and project the column set
    to them ... its defect is at most `L`", the legality readout
    `2^{a_t} θ = Q θ / 2^t < 1` (lines 470--472), and
    `L ≤ d λ = (p_t - 2^{a_t-1}) λ = c_{a_t}(p_t) λ` (lines 474--478);
  * lines 479--487, "`lem:defect-induction` gives complexity at least
    `C_W + a_t = C_W + r_Q - t`.  This holds for `t = 0, 1, 2`, and hence
    `Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q`";
  * line 488, "The `t = 0` case gives `comp(R⁺) ≥ C_W + r_Q`".
* `eq:direct-output` (label line 71, display lines 66--72) — **only its lower
  direction** is claimed here; see GAP-EXPOSED.
* line 63, `R⁺ = Int_Q(W)^T`, the orientation the output rungs are stated
  about.
* lines 36--37, the globally fixed `δ = 1/10` and `y = 1/2 + δ = 3/5`
  (`sections/03-preliminaries.tex` lines 216--219), consumed from
  `BRIDGE-ENTRY-001` as `EntryGates.deltaFixed`.

## Reader counterpart

`routes/parameterized-np/reader-facing/`.  Each file was opened and each cited
item checked, first-hand, to state the same fact.  **No reader item is assigned
twice**, here or against any earlier row.

* `sections/04-bridge.tex`, `eq:bridge-output` (label line 110, display lines
  106--110), **second equation**, `Λ_{R^+}(1, 2^{-b^+}, 3/5) ≥ C_W + r_Q` —
  counterpart of `directOutputLower`, and of that declaration alone.
  `BRIDGE-ENTRY-001` and `BRIDGE-OUTPUT-001` both recorded `eq:bridge-output`
  as deliberately unclaimed; it is claimed here and nowhere else.
* `sections/B-bridge-details.tex`, §"Entry at the requested depth" (line 173):
  * line 175, `L = b^+ \ln 2` — counterpart of `entryDefectL`;
  * `eq:appendix-Q-bounds` (label line 182, display lines 178--182) —
    counterpart of `directQBounds`;
  * the definition display at lines 185--192,
    `d = min{e ≥ 1 : (1 - δ_U)^e ≤ 2^{-b^+}}` with "This is an exact rational
    search and satisfies `(d-1) λ < L ≤ d λ`", and `a_t = r_Q - t`,
    `p_t = 2^{a_t - 1} + d` — counterpart of the three definitions
    `entryCount`, `entryLevelA`, `entryCopyCount` and of the window claim
    `entryWindow`;
  * `lem:bridge-good-block-count` (label line 195, statement lines 194--203),
    "For `t = 0,1,2`, one has `p_t ≤ Q`, `2^{a_t} θ < 1`, and
    `eq:appendix-good-block-count`" — counterpart of `entryGoodCopyCount`,
    whose closed statement is exactly that three-part conjunction.

Deliberately given **no** reader counterpart, with reasons:

* `entryLevelStep`.  The reader states the corresponding step only as proof
  prose (`B-bridge-details.tex` lines 227--233, "Keep `p_t` good copies and
  project ... The main defect induction gives complexity at least
  `C_W + a_t`"), and prose inside a proof is never cited as a statement.
* `directOutputRung`.  The reader's three rungs appear only inside the proof
  of `thm:near-to-robust` (`04-bridge.tex` lines 137--142); the labelled
  reader item they add up to is `eq:bridge-output`, already assigned above.
* `directOutputComplexityLower`.  The reader writes `comp R^+ = C_W + r_Q`,
  an **equality** (`eq:bridge-output`, first equation).  Citing an equality as
  the counterpart of a one-sided bound would misreport it, so no reader item is
  assigned; the first equation of `eq:bridge-output` stays unclaimed and
  remains with `BRIDGE-001`.
* `eq:bridge-carriers` (label line 117) stays unclaimed and remains with
  `BRIDGE-001`.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Vendored-counterpart finding

The tranche brief asks which case applies: *kernel-checked counterparts already
exist in the vendored `EthBridge` development, and they are consumed here
rather than re-proved.*

* `EthBridge.theorem_two` (`vendor/npc-cc/EthBridge/Entry.lean:759`) is the
  kernel-checked per-rung counterpart of lines 452--487: it delivers
  `C + (R - t) ≤ comp(bracket(R_next, 1, x_out, y/2^t))` from the Theorem-1
  hypothesis block plus `p_t ≤ Q` and `eq:direct-good-copy-count`.  Its own
  proof runs through `EthBridge.theorem_one`, i.e. through exactly the
  statement route-facaded as `DefectInduction.defectInduction`.
* `EthBridge.uniform_package` (`Entry.lean:855`) is the kernel-checked
  counterpart of lines 432--450 and of the reader's
  `lem:bridge-good-block-count`.
* `EthBridge.entryDefect`, `.entryExcess`, `.entryLevel`, `.entryCopies`,
  `.entryRowBound` (`Entry.lean:142, 148, 153, 159, 167`) are the vendored
  readouts; `EthBridge.cExcess_entryCopies` is the kernel-checked identity
  `c_{a}(2^{a-1} + d) = d`.

Two differences from the frozen paper are handled explicitly rather than
absorbed:

1. The vendored `entryExcess` is the ceiling `⌈L/λ⌉₊`.  The frozen paper
   defines `d` by the **exact rational search** `eq:direct-d-search`, which is
   a different function — they disagree at `b_out = 0`
   (`entryCount_refutes_candidateB`).  This module transcribes the frozen
   search as `entryCount` and proves `entryCount_eq_excess`, i.e. that the two
   agree on the frozen legal range `b_out ≥ 1`, `0 < δ_U < 1`.  Nothing
   vendored is consumed before that identification is proved.
2. The vendored package carries `δ` as a variable with `y = 1/2 + δ`; the
   frozen paper pins `δ = 1/10`, `y = 3/5`.  The pinned constants are
   substituted here from `EntryGates.deltaFixed`, never re-introduced as
   parameters.

## Status and dependencies

* Proof status: **inherited** for `entryGoodCopyCount`, `directOutputRung` and
  hence for the two assembled bounds (the vendored terms are consumed, never
  re-proved and never widened); **new (elementary)** for the entry parameters,
  the exact-search transcription and its window, the width bounds, the level
  readouts, the level step, the aux battery and every witness.
* Consumed, never edited or re-proved:
  * `DirectOutput.levelAdmissible`, `.le_rowFloor`, `.rowFloor_le_rows`,
    `.directCeilingLadder_of_levelAdmissible`,
    `.rows_equipartitionedGE_of_levelAdmissible`,
    `.levelAdmissible_refuted_at_large_theta` (`BRIDGE-OUTPUT-001`);
  * `DefectInduction.defectInduction`, `.rowFloor`, `.excessCopies`
    (`BRIDGE-DEFECT-001`), reached through
    `TwoCopyLadder.defectInduction_ofLadderInput` so that the two clauses of
    `eq:direct-input` are the only semantic inputs;
  * `EntryGates.Q0`, `.rQ`, `.Qwidth`, `.lambdaU`, `.deltaFixed`,
    `.Q0_first_le`, `.Q0_second_le`, `.Q0_le_Qwidth`, `.deltaU_le_lambdaU`,
    `.lambdaU_spec`, `.entryGate_theta_le`, `.two_pow_pred_lt_Q0`,
    `.four_le_rQ`, `.bridgeBaseEstimates_of_entryGates`,
    `.directEntryGates_fires` (`BRIDGE-ENTRY-001`);
  * `EthInapproximability.ParameterizedNP.familyComplexity_le_ambient` and
    `.powerOfTwoInterlace_upper` (`PilotStage3.lean`).
* Imports: `DirectOutput.lean` only, hence `EntryGates.lean`,
  `PilotStage3.lean`, `ThreeCopyRowStep.lean`, `TwoCopyLadder.lean`,
  `DefectInduction.lean`, `InheritedContracts.lean`,
  `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom is not in scope,
  and there is no contact with `EXPANDER-001` (which by design has no Lean
  declaration and would have to stay an explicit named hypothesis).
* External adapters: none.  Nothing here is axiomatized.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

The one genuinely open encoding choice is the excess-copy count `d` of
`eq:direct-d-search`.  Two candidates were written out and run against the
same four aux lemmas — (a) inhabitation of the search set at legal values,
(b) the window `eq:direct-d-window`, (c) `d ≥ 1` **unconditionally**, which is
what line 427 needs for the strict copy guard `p_t > 2^{a_t-1}`, and (d) the
round trip back to line 414 itself.

**Candidate A (landed).**
`entryCount b_out δ_U = sInf {e : ℕ | 1 ≤ e ∧ (1 - δ_U)^e ≤ 2^{-b_out}}`.
This is line 414 read literally — a minimum over integers `e ≥ 1` of an exact
rational comparison, matching the sentence at lines 410--411 that no real
logarithm is evaluated.  All four aux lemmas proved: (a)
`entryCount_set_nonempty`, (b) `entryWindow`, (c) `entryCount_pos`, (d)
`entryCount_mem` together with `entryCount_min`, the two defining properties of
the minimum at the literal predicate.

**Candidate B (rejected — disqualified by a failed aux lemma).**
`d = ⌈L/λ⌉₊`, the vendored `EthBridge.entryExcess`.  Aux lemma (c) is
**false** for it: `entryCount_refutes_candidateB` proves in Lean that at
`b_out = 0` the ceiling reads `0` while the frozen search reads `1`.  A `d`
that can be `0` destroys the strict copy guard of line 427 — with
`p_t = 2^{a_t-1} + 0` the hypothesis `p_t > 2^{a_t-1}` fails, so
`lem:defect-induction` would be invoked outside its own hypothesis.  Candidate
B is also not the frozen text: it evaluates a real logarithm, which lines
410--411 explicitly say the construction does not do.

Ranking (aux lemmas proved, faithfulness, length): A = 4/4, literal, exact
rational search; B = 3/4, real-logarithmic, degenerate at `b_out = 0`.  A
landed, and `entryCount_eq_excess` records exactly where the two agree, so the
vendored arithmetic is still consumed — but only after the identification is
proved on the frozen legal range.

## Faithfulness notes (mechanical rules M1--M10)

* **No structure at all** is introduced, and no premise bundle: every
  deliverable takes `eq:direct-input`, the two entry gates, the carrier
  nonemptiness facts and `C_W ≥ 3` as **explicit binders**.  No conclusion of
  `eq:direct-output` sits in constructor data, and no field restates a derived
  telescope.  The six new definitions (`xOut`, `entryDefectL`, `entryCount`,
  `entryLevelA`, `entryCopyCount`, `entryRowCap`) are numeric readouts of
  public parameters only.
* **Literal ceilings.**  `A_a` is not redefined: `DefectInduction.rowFloor` is
  imported and used, and `entryRowCap` keeps the frozen `ℕ`-subtractions
  `p - 1`, `Q - p + 1`, `A - 1` verbatim rather than rewriting them.
* **Selector costs preserved.**  This module proves no protocol upper bound;
  the `r_Q`-bit selector of lines 73--74 is `BRIDGE-OUTPUT-001`'s
  `canonicalSelectorUpper` and is not restated.
* **Both interlace widths.**  Only the outer width `Q = Qwidth` occurs; the
  scale-alignment width `q` does not appear and is not conflated with it.
  `entryCopyCount` and `entryLevelA` are counts and land in `ℕ`;
  `entryDefectL` and `xOut` are densities and land in `ℝ`.
* **The half-integer at level zero is untouched.**  `c_a(p)` is the banked
  `DefectInduction.excessCopies` with its `ℤ` exponent; it is used here at
  `a = a_t ≥ 2` through `EthBridge.cExcess_entryCopies` and never truncated.
* **Binder order** follows the frozen sentence: the matrix and its exact
  complexity, then the rung index `t`, then the requested depth `b_out` and
  the deletion tolerance `δ_U` that fix `Q`, then the row threshold `θ`, then
  the gates, then the carriers.
* **Finite carriers and nonemptiness.**  `1 ≤ |X|` and `1 ≤ |Y|` are explicit
  binders wherever the frozen argument needs nonempty carriers, and
  `entryRows_equipartitionedGE` records, through the banked
  `rows_equipartitionedGE_of_levelAdmissible`, that the row premise at the
  entry level is satisfiable rather than empty.
* **Trivial-witness pole.**  There is **no existential deliverable** in this
  module.  Every claim is a bound on a named readout or a named-def claim
  about a pinned construction, exactly as the pipeline requires when a trivial
  witness cannot be excluded.  In particular `entryCount` is not "there exists
  an exponent that works" — which every large exponent satisfies — but the
  minimum, which every larger exponent refutes; `entryCount_min` is the half a
  trivial witness fails.  The one existential statement in the module is the
  aux inhabitation lemma `entryCount_set_nonempty`, and it is not a
  deliverable: its trivial witness `e = 0` **fails**, because line 414's search
  set requires `e ≥ 1`, so the lemma has to exhibit `max 1 ⌈L/λ⌉₊`.
* **Vacuous-conclusion pole.**  `C_W + r_Q ≥ 3 + 4 = 7` at every legal
  parameter (`hCW` and `EntryGates.four_le_rQ`), recorded by
  `directOutputLower_conclusion_nontrivial`, so the delivered bounds are not
  free.
* **Vacuous-hypothesis pole.**  `entryLevel_refuted_at_large_theta` checks
  that the level readout genuinely restricts: at `θ = 1` — inside line 39's
  own range `0 < θ ≤ 1` — the top entry level is **inadmissible**, so
  admissibility at `a_0` is a consequence of the entry gate and not of the
  frozen range of `θ`.
* **Non-vacuity at legal values, at *both* banked entry-gate witnesses.**  The
  `BRIDGE-ENTRY-001` witness `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`,
  `y = 3/5`, with `Q_0 = 4800`, `r_Q = 13`, `Q = 8192`, is carried through the
  whole apparatus: the three entry levels read `13, 12, 11`, all admissible;
  the excess-copy count is pinned into the **interior** window `41 ≤ d ≤ 42`,
  far from the degenerate `0` or `1`, so `p_0 = 4096 + d` sits strictly between
  `2^{a_0-1} = 4096` and `Q = 8192`; the three width bounds of
  `eq:direct-Q-bounds` are discharged by computation; and at `m = 192000` the
  row floors read `A_{13} = 8192`, `A_{12} = 4096`, `A_{11} = 2048`,
  exhibiting the banked ceiling ladder **tight and with no zero rung**.  A
  degenerate inhabitant would read `d = 0` (no excess copies, strict copy guard
  lost), `p_t = Q` (no room in the outer interlace), or `A_{a_t} = 0` (empty
  row floors); this one reads none of them.  The `BRIDGE-OUTPUT-001` second
  witness `b_out = 1`, `δ_U = 1/200`, `θ = 1/640000`, with `Q_0 = 16000`,
  `r_Q = 14`, `Q = 16384`, is carried through the *same* readouts and moves all
  of them — levels `14, 13, 12`, count `41 ≤ d ≤ 139`, `8192 < p_0 < 16384`,
  floors `A_{14} = 16384`, `A_{13} = 8192`, `A_{12} = 4096` — so no readout
  here is tuned to one numeral.
* **The premise bundle is satisfiable at legal values.**
  `directOutputLower_fires_first_witness` and
  `directOutputLower_fires_second_witness` discharge **every** binder of the
  two deliverables except the two clauses of `eq:direct-input`, at the two
  witnesses above and at `C_W = 3` (the boundary of line 40), delivering the
  concrete bounds `16` and `17`.  In particular the second-gate margin
  `3λ + (7/5) ln 2 ≤ -2 ln(3/5)` — which is *tight* at `δ_U = 1/60` and is not
  implied by `0 < δ_U < 1` — is discharged by computation through the banked
  `EntryGates.secondEntryGate_of_deltaU_small`, so the hypothesis list is not
  an unsatisfiable over-strong bundle.  `X`, `Y` and `W` stay universally
  quantified, since `eq:direct-input` has no exhibited inhabitant and can have
  none until Stages 1--4 land.

## GAP-EXPOSED (nothing is weakened to close these)

1. **`thm:direct-robustification` is not claimed.**  No declaration in this
   module has the theorem's closed statement, and the **equality**
   `comp R⁺ = C_W + r_Q` of `eq:direct-output` is not stated anywhere: only
   its lower direction is proved here, and only its upper direction was proved
   in `BRIDGE-OUTPUT-001`.  Assembling the two into the frozen equality, under
   the theorem's own hypothesis list and with `comp W = C_W` as line 40 states
   it, is left to `BRIDGE-001`.
2. **`lem:copy-restriction` (line 132) is still not landed.**  `entryLevelStep`
   therefore takes the literal `p_t`-copy restriction as **given** — its row
   set, its column set and their two premises are explicit binders — instead
   of extracting it from a transposed bracket member.  The extraction is
   performed inside the consumed vendored term for `directOutputRung`, so the
   route does not need `lem:copy-restriction` to state or use the rungs, but
   it remains the separate reboot obligation the `INHERIT-001` ledger row
   already records.
3. **`eq:direct-input` has no exhibited inhabitant**, and none can be
   exhibited until Stages 1--4 land in Lean.  Both clauses are carried as
   explicit named binders, and every witness below is therefore *conditional
   only*: every numeric guard, every level readout, every width bound and the
   whole ceiling-safe count are discharged unconditionally, but nothing here
   asserts that any `W` satisfying the two clauses exists.  This is faithful to
   the frozen section, whose opening sentence (line 3) is that all
   construction-specific information has already been discarded.
4. **`eq:bridge-carriers`** (`|Rows(R⁺)| = n^Q`, `|Cols(R⁺)| = Q m`) and the
   budget collection of §`sec:one-level-completion` (lines 500--563) are
   untouched.
-/

namespace EthInapproximability.ParameterizedNP.DirectOutputLower

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.TwoCopyLadder
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput

/-! ## Part 1: the entry parameters of `10-direct-bridge.tex:392--396`

`x_out = 2^{-b_out}` and `L = ln(1/x_out) = b_out ln 2`.  Plain definitions;
no conclusion of `eq:direct-output` is placed in either. -/

/-- **`x_out = 2^{-b_out}`** (`10-direct-bridge.tex:394`).

The requested output column density.  Written as the reciprocal of a natural
power, so `b_out` stays the integer line 41 declares it to be and no real
exponentiation is introduced. -/
noncomputable def xOut (bout : ℕ) : ℝ := ((2 : ℝ) ^ bout)⁻¹

/-- **`L = ln(1/x_out) = b_out ln 2`** (`10-direct-bridge.tex:396`; reader
`B-bridge-details.tex:174`).

The absolute column-defect budget the projected column set must respect. -/
noncomputable def entryDefectL (bout : ℕ) : ℝ := (bout : ℝ) * Real.log 2

/-! ### Aux battery for `xOut` and `entryDefectL` -/

/-- **Aux 1 (positivity).**  `x_out > 0`, needed before it is used as a density
and before `ln(1/x_out)` is formed. -/
lemma xOut_pos (bout : ℕ) : 0 < xOut bout := by
  unfold xOut
  positivity

/-- **Aux 2 (a legal density).**  `x_out ≤ 1` for every `b_out`. -/
lemma xOut_le_one (bout : ℕ) : xOut bout ≤ 1 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ bout := by positivity
  have h : (1 : ℝ) ≤ (2 : ℝ) ^ bout := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ bout := pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  unfold xOut
  rw [inv_eq_one_div, div_le_one hpos]
  linarith

/-- **Aux 3 (strict at the frozen legal depths).**  `x_out < 1` exactly where
line 41 puts `b_out`, namely `b_out ≥ 1`.  This is the load-bearing half: it is
what makes the excess-copy count positive and hence the copy guard of line 427
strict. -/
lemma xOut_lt_one {bout : ℕ} (hb : 1 ≤ bout) : xOut bout < 1 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ bout := by positivity
  have h : (2 : ℝ) ≤ (2 : ℝ) ^ bout := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ bout := pow_le_pow_right₀ (by norm_num) hb
  unfold xOut
  rw [inv_eq_one_div, div_lt_one hpos]
  linarith

/-- **Aux 4 (round trip, `L = ln(1/x_out)`).**  Line 396 states the budget
twice, as `ln(1/x_out)` and as `b_out ln 2`; this proves the two spellings
agree, and simultaneously identifies `entryDefectL` with the vendored readout,
so no quantity is defined a second time. -/
lemma entryDefect_eq (bout : ℕ) :
    EthBridge.entryDefect (xOut bout) = entryDefectL bout := by
  unfold EthBridge.entryDefect xOut entryDefectL
  rw [one_div, inv_inv, Real.log_pow]

/-- **Aux 5 (positivity of the budget).**  `L > 0` at every frozen legal
depth. -/
lemma entryDefectL_pos {bout : ℕ} (hb : 1 ≤ bout) : 0 < entryDefectL bout := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb' : (1 : ℝ) ≤ (bout : ℝ) := by exact_mod_cast hb
  unfold entryDefectL
  nlinarith

/-- **Aux 6 (`ln 2 < 1`, in the shape line 398 uses it).**  `L ≤ b_out`.  This
is the only place the frozen sentence "`ln 2 < 1`" is consumed, and it is what
turns the `Q_0` branch `8 b_out/(δ δ_U)` into the first width bound of
`eq:direct-Q-bounds`. -/
lemma entryDefectL_le_depth (bout : ℕ) : entryDefectL bout ≤ (bout : ℝ) := by
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hb : (0 : ℝ) ≤ (bout : ℝ) := Nat.cast_nonneg _
  unfold entryDefectL
  nlinarith

/-- **`x_out = e^{-L}`.**  The conversion that turns the exact rational
comparison of line 414 into the defect inequality the induction consumes. -/
lemma xOut_eq_exp (bout : ℕ) : xOut bout = Real.exp (-entryDefectL bout) := by
  have hpos : (0 : ℝ) < xOut bout := xOut_pos bout
  rw [← Real.exp_log hpos]
  congr 1
  unfold xOut entryDefectL
  rw [Real.log_inv, Real.log_pow]

/-! ## Part 2: the exact rational search `eq:direct-d-search`

`10-direct-bridge.tex:412--414`; reader `B-bridge-details.tex:185--190`.  This
is Candidate A of the header: the frozen minimum over integers `e ≥ 1` of an
exact rational comparison. -/

/-- **`d = min{e ≥ 1 : (1 - δ_U)^e ≤ 2^{-b_out}}`** (`eq:direct-d-search`,
`10-direct-bridge.tex:414`; reader `B-bridge-details.tex:186--188`).

The excess-copy count the bridge purchases to pay for the entry column defect.
Transcribed literally: a minimum over integers `e ≥ 1` of a comparison between
two rationals, with no real logarithm evaluated, exactly as lines 410--411
insist. -/
noncomputable def entryCount (bout : ℕ) (δU : ℝ) : ℕ :=
  sInf {e : ℕ | 1 ≤ e ∧ (1 - δU) ^ e ≤ xOut bout}

/-! ### Aux battery for `entryCount` -/

/-- **Aux 7 (the search predicate in defect form).**  For `0 < δ_U < 1` the
exact rational comparison `(1 - δ_U)^e ≤ 2^{-b_out}` is precisely the defect
inequality `L ≤ e λ`.  This is the only conversion between the two spellings
used anywhere below, and it is the equivalence line 416 asserts.

Only `δ_U < 1` is assumed: the frozen range also has `δ_U > 0`, but this
equivalence does not need it, and carrying it would be an over-strong
hypothesis the conversion does not have. -/
lemma entryCount_mem_iff {δU : ℝ} (hδ1 : δU < 1) (bout e : ℕ) :
    (1 - δU) ^ e ≤ xOut bout ↔ entryDefectL bout ≤ (e : ℝ) * lambdaU δU := by
  have hc : (0 : ℝ) < 1 - δU := by linarith
  have h1 : (1 - δU) ^ e = Real.exp (Real.log (1 - δU) * (e : ℝ)) := by
    rw [← Real.rpow_natCast (1 - δU) e, Real.rpow_def_of_pos hc]
  have hkey : ((e : ℝ) * lambdaU δU) = -(Real.log (1 - δU) * (e : ℝ)) := by
    unfold lambdaU
    ring
  rw [h1, xOut_eq_exp, Real.exp_le_exp, hkey]
  constructor <;> intro h <;> linarith

/-- **Aux 8 (inhabitation of the search set).**  At every legal deletion
tolerance the set line 414 minimizes over is nonempty, so the minimum is a
genuine value and not the `sInf` junk value `0`. -/
lemma entryCount_set_nonempty {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (bout : ℕ) :
    {e : ℕ | 1 ≤ e ∧ (1 - δU) ^ e ≤ xOut bout}.Nonempty := by
  have hlam : 0 < lambdaU δU := (lambdaU_spec hδ0 hδ1).2
  refine ⟨max 1 ⌈entryDefectL bout / lambdaU δU⌉₊, le_max_left _ _, ?_⟩
  rw [entryCount_mem_iff hδ1]
  have h1 : entryDefectL bout / lambdaU δU
      ≤ (⌈entryDefectL bout / lambdaU δU⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hlam] at h1
  have h2 : ((⌈entryDefectL bout / lambdaU δU⌉₊ : ℕ) : ℝ)
      ≤ ((max 1 ⌈entryDefectL bout / lambdaU δU⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 1 ⌈entryDefectL bout / lambdaU δU⌉₊
  nlinarith

/-- **Aux 9 (`sInf` membership: `d` is admissible).**  The frozen minimum
satisfies both defining conditions of line 414. -/
lemma entryCount_mem {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) (bout : ℕ) :
    1 ≤ entryCount bout δU ∧ (1 - δU) ^ (entryCount bout δU) ≤ xOut bout :=
  Nat.sInf_mem (entryCount_set_nonempty hδ0 hδ1 bout)

/-- **Aux 10 (`sInf` minimality: `d` is *the* minimum).**  Every admissible
exponent is at least `d`.  This is the half a trivial large witness refutes
rather than satisfies, and it is what makes `entryCount` a named-def claim
instead of an existential. -/
lemma entryCount_min {δU : ℝ} {bout e : ℕ} (he1 : 1 ≤ e)
    (he : (1 - δU) ^ e ≤ xOut bout) : entryCount bout δU ≤ e :=
  Nat.sInf_le ⟨he1, he⟩

/-- **Aux 11 (`d ≥ 1`, unconditionally).**  The frozen search ranges over
`e ≥ 1`, so its minimum is at least `1` at every legal deletion tolerance and
every depth — including `b_out = 0`.  This is the aux lemma Candidate B fails,
and it is what makes the copy guard of line 427 strict. -/
lemma entryCount_pos {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) (bout : ℕ) :
    1 ≤ entryCount bout δU :=
  (entryCount_mem hδ0 hδ1 bout).1

/-- **`eq:direct-d-window`** (`10-direct-bridge.tex:417--419`; reader
`B-bridge-details.tex:189--190`): `(d - 1) λ < L ≤ d λ`.

Line 416 states that minimality *is* this window, and both halves are proved
here from the two `sInf` properties.  The subtraction is real, not truncated:
`d ≥ 1` makes `(d : ℝ) - 1` the paper's `d - 1`. -/
theorem entryWindow {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) {bout : ℕ}
    (hb : 1 ≤ bout) :
    ((entryCount bout δU : ℝ) - 1) * lambdaU δU < entryDefectL bout ∧
      entryDefectL bout ≤ (entryCount bout δU : ℝ) * lambdaU δU := by
  have hL : 0 < entryDefectL bout := entryDefectL_pos hb
  obtain ⟨hd1, hdmem⟩ := entryCount_mem hδ0 hδ1 bout
  have hupper : entryDefectL bout ≤ (entryCount bout δU : ℝ) * lambdaU δU :=
    (entryCount_mem_iff hδ1 bout _).mp hdmem
  refine ⟨?_, hupper⟩
  by_contra hcon
  rw [not_lt] at hcon
  rcases Nat.lt_or_ge (entryCount bout δU) 2 with hsmall | hbig
  · have hone : entryCount bout δU = 1 := by omega
    rw [hone] at hcon
    norm_num at hcon
    linarith
  · have hcast : ((entryCount bout δU - 1 : ℕ) : ℝ)
        = (entryCount bout δU : ℝ) - 1 := by
      push_cast [Nat.cast_sub hd1]
      ring
    have hmem' : (1 - δU) ^ (entryCount bout δU - 1) ≤ xOut bout := by
      rw [entryCount_mem_iff hδ1, hcast]
      exact hcon
    have hle := entryCount_min (by omega : 1 ≤ entryCount bout δU - 1) hmem'
    omega

/-- **The identification with the vendored ceiling.**

On the frozen legal range `b_out ≥ 1`, `0 < δ_U < 1`, the exact rational search
of line 414 and the vendored `EthBridge.entryExcess = ⌈L/λ⌉₊` agree.  Nothing
vendored is consumed before this is proved; off that range the two genuinely
differ (`entryCount_refutes_candidateB`). -/
theorem entryCount_eq_excess {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1)
    {bout : ℕ} (hb : 1 ≤ bout) :
    entryCount bout δU = EthBridge.entryExcess (xOut bout) (lambdaU δU) := by
  have hlam : 0 < lambdaU δU := (lambdaU_spec hδ0 hδ1).2
  have hL : 0 < entryDefectL bout := entryDefectL_pos hb
  have hexc : EthBridge.entryExcess (xOut bout) (lambdaU δU)
      = ⌈entryDefectL bout / lambdaU δU⌉₊ := by
    unfold EthBridge.entryExcess
    rw [entryDefect_eq]
  rw [hexc]
  refine le_antisymm ?_ ?_
  · refine entryCount_min ?_ ?_
    · have hp : 0 < ⌈entryDefectL bout / lambdaU δU⌉₊ :=
        Nat.ceil_pos.mpr (div_pos hL hlam)
      omega
    · rw [entryCount_mem_iff hδ1]
      have h1 : entryDefectL bout / lambdaU δU
          ≤ (⌈entryDefectL bout / lambdaU δU⌉₊ : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hlam] at h1
      exact h1
  · refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ hlam]
    exact (entryWindow hδ0 hδ1 hb).2

/-! ## Part 3: the width bounds `eq:direct-Q-bounds`

`10-direct-bridge.tex:398--408`; reader `eq:appendix-Q-bounds`,
`B-bridge-details.tex:178--182`.  Everything here is derived from the landed
entry apparatus of `BRIDGE-ENTRY-001`; no new property of `Q_0` or `r_Q` is
introduced. -/

/-- The canonical width as a real number.  `Q = 2^{r_Q}` is a copy count in
`ℕ`; every comparison in `eq:direct-Q-bounds` is real, so the cast is recorded
once here rather than inline. -/
lemma Qwidth_cast (bout : ℕ) (δU : ℝ) :
    ((Qwidth bout δU : ℕ) : ℝ) = (2 : ℝ) ^ rQ bout δU := by
  rw [Qwidth]
  push_cast
  ring

/-- **`eq:direct-Q-bounds`** (`10-direct-bridge.tex:402--407`; reader
`eq:appendix-Q-bounds`, `B-bridge-details.tex:178--182`):
`Q ≥ 8L/(δλ)`, `Q ≥ 8/δ`, `Q θ < δ/2`.

The frozen derivation at lines 398--400 is followed literally: `λ ≥ δ_U`
(`EntryGates.deltaU_le_lambdaU`) and `ln 2 < 1` (`entryDefectL_le_depth`) give
the first from the `Q_0` branch `8 b_out/(δ δ_U)`; the second is the `Q_0`
branch `8/δ`; the third is `Q < 2 Q_0` (`EntryGates.two_pow_pred_lt_Q0`)
against the first entry gate.  Only the **first** gate is taken as a binder —
the second plays no part in these three bounds. -/
theorem directQBounds {bout : ℕ} {δU θ : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hθ0 : 0 < θ) (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) :
    8 * entryDefectL bout / (deltaFixed * lambdaU δU)
        ≤ ((Qwidth bout δU : ℕ) : ℝ) ∧
      8 / deltaFixed ≤ ((Qwidth bout δU : ℕ) : ℝ) ∧
      ((Qwidth bout δU : ℕ) : ℝ) * θ < deltaFixed / 2 := by
  have hlam : 0 < lambdaU δU := (lambdaU_spec hδ0 hδ1).2
  have hδfix : deltaFixed = 1 / 10 := deltaFixed_eq
  have hQ0Q : Q0 bout δU ≤ ((Qwidth bout δU : ℕ) : ℝ) := Q0_le_Qwidth bout δU
  have hprodL : (0 : ℝ) < deltaFixed * lambdaU δU := by
    rw [hδfix]; positivity
  have hprodU : (0 : ℝ) < deltaFixed * δU := by
    rw [hδfix]; positivity
  refine ⟨?_, ?_, ?_⟩
  · have hLb : entryDefectL bout ≤ (bout : ℝ) := entryDefectL_le_depth bout
    have hδlam : δU ≤ lambdaU δU := deltaU_le_lambdaU hδ1
    have hbnn : (0 : ℝ) ≤ (bout : ℝ) := Nat.cast_nonneg _
    have hstep1 : 8 * entryDefectL bout / (deltaFixed * lambdaU δU)
        ≤ 8 * (bout : ℝ) / (deltaFixed * lambdaU δU) := by
      rw [div_le_div_iff₀ hprodL hprodL]
      nlinarith [mul_nonneg
        (by linarith : (0 : ℝ) ≤ 8 * (bout : ℝ) - 8 * entryDefectL bout)
        hprodL.le]
    have hstep2 : 8 * (bout : ℝ) / (deltaFixed * lambdaU δU)
        ≤ 8 * (bout : ℝ) / (deltaFixed * δU) := by
      rw [div_le_div_iff₀ hprodL hprodU]
      nlinarith [mul_nonneg
        (mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * (bout : ℝ))
          (by rw [hδfix]; norm_num : (0 : ℝ) ≤ deltaFixed))
        (by linarith : (0 : ℝ) ≤ lambdaU δU - δU)]
    calc 8 * entryDefectL bout / (deltaFixed * lambdaU δU)
        ≤ 8 * (bout : ℝ) / (deltaFixed * lambdaU δU) := hstep1
      _ ≤ 8 * (bout : ℝ) / (deltaFixed * δU) := hstep2
      _ ≤ Q0 bout δU := Q0_first_le bout δU
      _ ≤ ((Qwidth bout δU : ℕ) : ℝ) := hQ0Q
  · exact le_trans (Q0_second_le bout δU) hQ0Q
  · have hlt : ((Qwidth bout δU : ℕ) : ℝ) < 2 * Q0 bout δU :=
      two_pow_pred_lt_Q0 bout δU
    have hpos := mul_pos
      (by linarith : (0 : ℝ) < 2 * Q0 bout δU - ((Qwidth bout δU : ℕ) : ℝ))
      hθ0
    nlinarith [hpos, hgate]

/-! ## Part 4: the entry levels and copy counts of `10-direct-bridge.tex:421--428` -/

/-- **`a_t = r_Q - t`** (`10-direct-bridge.tex:423`; reader
`B-bridge-details.tex:191`).  `ℕ`-subtraction, exact for `t ≤ 2 ≤ 4 ≤ r_Q`. -/
noncomputable def entryLevelA (bout : ℕ) (δU : ℝ) (t : ℕ) : ℕ := rQ bout δU - t

/-- **`p_t = 2^{a_t - 1} + d`** (`10-direct-bridge.tex:425`; reader
`B-bridge-details.tex:191`).  A copy count, so it lands in `ℕ`. -/
noncomputable def entryCopyCount (bout : ℕ) (δU : ℝ) (t : ℕ) : ℕ :=
  2 ^ (entryLevelA bout δU t - 1) + entryCount bout δU

/-- **The left side of `eq:direct-good-copy-count`**
(`10-direct-bridge.tex:433`; reader `eq:appendix-good-block-count`,
`B-bridge-details.tex:199--200`): `(p - 1) m + (Q - p + 1)(A - 1)`, the largest
row count a restriction can retain when fewer than `p` outer copies are good at
floor `A`.  The three frozen `ℕ`-subtractions are kept verbatim. -/
def entryRowCap (Q m p A : ℕ) : ℕ := (p - 1) * m + (Q - p + 1) * (A - 1)

/-! ### Aux battery for the three counts -/

/-- **Aux 12 (the level readout is the vendored one).** -/
lemma entryLevelA_eq (bout : ℕ) (δU : ℝ) (t : ℕ) :
    entryLevelA bout δU t = EthBridge.entryLevel (rQ bout δU) t := rfl

/-- **Aux 13 (the row cap is the vendored one).** -/
lemma entryRowCap_eq (Q m p A : ℕ) :
    entryRowCap Q m p A = EthBridge.entryRowBound Q m p A := rfl

/-- **Aux 14 (calibration at the top rung).**  `a_0 = r_Q`. -/
lemma entryLevelA_zero (bout : ℕ) (δU : ℝ) :
    entryLevelA bout δU 0 = rQ bout δU := rfl

/-- **Aux 15 (successive rungs).**  `a_{t+1} = a_t - 1`: consecutive entry
levels differ by exactly one, which is what makes the banked ceiling ladder
apply between them. -/
lemma entryLevelA_succ (bout : ℕ) (δU : ℝ) (t : ℕ) :
    entryLevelA bout δU (t + 1) = entryLevelA bout δU t - 1 := by
  unfold entryLevelA
  omega

/-- **Aux 16 (every used level is positive).**  `a_t ≥ 1` for `t ≤ 2`, from
`EntryGates.four_le_rQ`.  This is what makes `2^{a_t - 1}` a genuine power and
`c_{a_t}` a genuine integer power. -/
lemma one_le_entryLevelA (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    1 ≤ entryLevelA bout δU t := by
  have h4 := four_le_rQ bout δU
  unfold entryLevelA
  omega

/-- **Aux 17 (the copy count is the vendored one, on the legal range).** -/
lemma entryCopyCount_eq {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) {bout : ℕ}
    (hb : 1 ≤ bout) (t : ℕ) :
    entryCopyCount bout δU t
      = EthBridge.entryCopies (rQ bout δU) t (xOut bout) (lambdaU δU) := by
  unfold entryCopyCount EthBridge.entryCopies entryLevelA EthBridge.entryLevel
  rw [entryCount_eq_excess hδ0 hδ1 hb]

/-- **The strict copy guard** (`10-direct-bridge.tex:427--428`): "Then
`p_t > 2^{a_t-1}`, the strict copy-count hypothesis of
`lem:defect-induction`".

Rendered in the doubled `ℕ`-safe form `2^{a_t} < 2 p_t` that the banked
`defectInduction` takes, which is exact at every level.  It rests on
`entryCount_pos`, i.e. on the fact that the frozen search ranges over
`e ≥ 1`. -/
theorem entryCopyCount_copyGuard {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (bout : ℕ) {t : ℕ} (ht : t ≤ 2) :
    2 ^ entryLevelA bout δU t < 2 * entryCopyCount bout δU t := by
  have hd := entryCount_pos hδ0 hδ1 bout
  have h1 := one_le_entryLevelA bout δU ht
  have h2 : 2 * 2 ^ (entryLevelA bout δU t - 1) = 2 ^ entryLevelA bout δU t := by
    conv_rhs =>
      rw [show entryLevelA bout δU t = (entryLevelA bout δU t - 1) + 1 by omega]
    rw [pow_succ]
    ring
  unfold entryCopyCount
  omega

/-- **`c_{a_t}(p_t) = d` exactly** (`10-direct-bridge.tex:475--478`).

The banked `DefectInduction.excessCopies` evaluated at the entry parameters
returns the excess-copy count itself, which is what turns the defect budget
`L ≤ d λ` into the induction's `Def(K) ≤ c_{a_t}(p_t) λ`.  The `ℤ` exponent of
`c_a` is not truncated: `a_t ≥ 1` makes it a genuine natural power. -/
theorem excessCopies_entryCopyCount (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    excessCopies (entryLevelA bout δU t) (entryCopyCount bout δU t)
      = (entryCount bout δU : ℝ) := by
  have h1 := one_le_entryLevelA bout δU ht
  unfold entryCopyCount
  exact EthBridge.cExcess_entryCopies (entryLevelA bout δU t)
    (entryCount bout δU) h1

/-! ### The entry level restriction, and the banked level-admissible services -/

/-- **`2^{a_t} = Q / 2^t`** (`10-direct-bridge.tex:471`), the exact identity
behind the legality readout. -/
lemma entryLevel_pow_eq (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    (2 : ℝ) ^ entryLevelA bout δU t = ((Qwidth bout δU : ℕ) : ℝ) / 2 ^ t := by
  have h4 := four_le_rQ bout δU
  rw [Qwidth_cast]
  unfold entryLevelA
  rw [eq_div_iff (by positivity : ((2 : ℝ) ^ t) ≠ 0), ← pow_add]
  congr 1
  omega

/-- **`2^{a_t} θ = Q θ / 2^t < 1`** (`10-direct-bridge.tex:470--472`; reader
`lem:bridge-good-block-count`, second conclusion).

Strict, exactly as the frozen line writes it.  The third width bound of
`eq:direct-Q-bounds` is the whole content. -/
theorem entryLevel_lt_one {bout : ℕ} {δU θ : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hθ0 : 0 < θ) (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) {t : ℕ}
    (ht : t ≤ 2) :
    (2 : ℝ) ^ entryLevelA bout δU t * θ < 1 := by
  obtain ⟨-, -, hQx⟩ := directQBounds hδ0 hδ1 hθ0 hgate
  have h4 := four_le_rQ bout δU
  have hle : (2 : ℝ) ^ entryLevelA bout δU t ≤ ((Qwidth bout δU : ℕ) : ℝ) := by
    rw [Qwidth_cast]
    refine pow_le_pow_right₀ (by norm_num) ?_
    unfold entryLevelA
    omega
  rw [deltaFixed_eq] at hQx
  nlinarith [mul_le_mul_of_nonneg_right hle hθ0.le]

/-- **The entry level is admissible**, in the banked `levelAdmissible`
spelling of `BRIDGE-OUTPUT-001` (`10-direct-bridge.tex:84`).  The banked
predicate is consumed here, never redefined. -/
theorem entryLevel_admissible {bout : ℕ} {δU θ : ℝ} (hδ0 : 0 < δU)
    (hδ1 : δU < 1) (hθ0 : 0 < θ) (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    {t : ℕ} (ht : t ≤ 2) :
    levelAdmissible θ (entryLevelA bout δU t) :=
  le_of_lt (entryLevel_lt_one hδ0 hδ1 hθ0 hgate ht)

/-- **The banked ceiling ladder between consecutive entry rungs.**

`eq:direct-ceiling-ladder` relates level `a` to level `a - 1`, and
`entryLevelA_succ` says consecutive entry rungs are exactly that pair.  The
banked `DirectOutput.directCeilingLadder_of_levelAdmissible` is consumed
unchanged, so the row floors of the three output rungs halve down the ladder
and every rung stays inside the range line 84 permits. -/
theorem entryRowFloor_ladder (m : ℕ) {bout : ℕ} {δU θ : ℝ} (hδ0 : 0 < δU)
    (hδ1 : δU < 1) (hθ0 : 0 < θ) (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    {t : ℕ} (ht : t + 1 ≤ 2) :
    rowFloor m θ (entryLevelA bout δU (t + 1))
        ≤ ⌈(rowFloor m θ (entryLevelA bout δU t) : ℝ) / 2⌉₊ ∧
      levelAdmissible θ (entryLevelA bout δU (t + 1)) := by
  have hlev := entryLevel_admissible hδ0 hδ1 hθ0 hgate (by omega : t ≤ 2)
  have h1 := one_le_entryLevelA bout δU (by omega : t ≤ 2)
  rw [entryLevelA_succ]
  exact directCeilingLadder_of_levelAdmissible m hθ0.le h1 hlev

/-- **The row premise at an entry rung is satisfiable.**

The banked `DirectOutput.rows_equipartitionedGE_of_levelAdmissible` at the
entry level: the full row carrier of the interlace meets the floor `A_{a_t}`,
so the row condition the induction imposes is never vacuous at the levels the
bridge actually uses. -/
theorem entryRows_equipartitionedGE {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] {bout : ℕ} {δU θ : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hθ0 : 0 < θ) (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) {t : ℕ}
    (ht : t ≤ 2) :
    IsEquipartitionedGE (Finset.univ : Finset (ι × X))
      (Finset.univ : Finset ι)
      (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)) :=
  rows_equipartitionedGE_of_levelAdmissible
    (entryLevel_admissible hδ0 hδ1 hθ0 hgate ht)

/-- **The entry row floor brackets the real row count from above and the row
carrier from below.**

The banked `DirectOutput.le_rowFloor` (`10-direct-bridge.tex:90`) and
`DirectOutput.rowFloor_le_rows` (line 84's purpose) read off at the entry
level: `m 2^{a_t} θ ≤ A_{a_t} ≤ m`.  Both are consumed, neither re-proved. -/
theorem entryRowFloor_bracket (m : ℕ) {bout : ℕ} {δU θ : ℝ} (hδ0 : 0 < δU)
    (hδ1 : δU < 1) (hθ0 : 0 < θ) (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    {t : ℕ} (ht : t ≤ 2) :
    (m : ℝ) * (2 : ℝ) ^ (entryLevelA bout δU t) * θ
        ≤ (rowFloor m θ (entryLevelA bout δU t) : ℝ) ∧
      rowFloor m θ (entryLevelA bout δU t) ≤ m :=
  ⟨le_rowFloor m θ (entryLevelA bout δU t),
    rowFloor_le_rows m (entryLevel_admissible hδ0 hδ1 hθ0 hgate ht)⟩

/-! ## Part 5: the ceiling-safe good-copy count `eq:direct-good-copy-count` -/

/-- **`eq:direct-good-copy-count` and `p_t ≤ Q`**
(`10-direct-bridge.tex:432--450`; reader `lem:bridge-good-block-count`,
`B-bridge-details.tex:194--203`).

For every rung `t ≤ 2`: `p_t ≤ Q`, `2^{a_t} θ < 1`, and
`(p_t - 1) m + (Q - p_t + 1)(A_{a_t} - 1) < Q m y / 2^t` at the globally fixed
`y = 3/5`.  The closed statement is exactly the reader lemma's three-part
conjunction.

The kernel-checked `EthBridge.uniform_package` is *consumed*, with `δ` pinned
to the frozen `deltaFixed = 1/10` and `y` to `1/2 + δ = 3/5`; its three package
hypotheses are the three bounds of `directQBounds`, and its excess-copy count
is identified with the frozen exact search by `entryCount_eq_excess` before
anything is consumed. -/
theorem entryGoodCopyCount (m : ℕ) {bout : ℕ} {δU θ : ℝ} (hb : 1 ≤ bout)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hm : 1 ≤ m) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) {t : ℕ} (ht : t ≤ 2) :
    entryCopyCount bout δU t ≤ Qwidth bout δU ∧
      (2 : ℝ) ^ entryLevelA bout δU t * θ < 1 ∧
      ((entryRowCap (Qwidth bout δU) m (entryCopyCount bout δU t)
            (rowFloor m θ (entryLevelA bout δU t)) : ℕ) : ℝ)
        < ((Qwidth bout δU : ℕ) : ℝ) * (m : ℝ) * (3 / 5) / 2 ^ t := by
  obtain ⟨hQL, hQδ, hQx⟩ := directQBounds hδ0 hδ1 hθ0 hgate
  have hlam : 0 < lambdaU δU := (lambdaU_spec hδ0 hδ1).2
  have hcast := Qwidth_cast bout δU
  have hpack := EthBridge.uniform_package (rQ bout δU) m θ (lambdaU δU)
      (xOut bout) deltaFixed (3 / 5) (four_le_rQ bout δU) hm
      (by rw [deltaFixed_eq]; norm_num) (by rw [deltaFixed_eq]; norm_num)
      (by rw [deltaFixed_eq]; norm_num) hlam hθ0 (xOut_pos bout)
      (xOut_lt_one hb)
      (by rw [entryDefect_eq, ← hcast]; exact hQL)
      (by rw [← hcast]; exact hQδ)
      (by rw [← hcast]; exact hQx)
      t ht
  rw [← entryCopyCount_eq hδ0 hδ1 hb t] at hpack
  refine ⟨hpack.1, entryLevel_lt_one hδ0 hδ1 hθ0 hgate ht, ?_⟩
  rw [hcast]
  exact hpack.2

/-! ## Part 6: the level step of `10-direct-bridge.tex:465--482`

The final step of the frozen entry argument, with the literal `p_t`-copy
restriction taken as **given** (see GAP-EXPOSED item 2): from the row floor
`A_{a_t}` and a column carrier of defect at most `L`, the banked defect
induction returns complexity at least `C_W + a_t`. -/

/-- **The entry level step** (`10-direct-bridge.tex:465--482`).

Given a literal restriction of `Int_{p_t}(W)` that retains at least `A_{a_t}`
rows in every active copy and whose nonempty column carrier has defect at most
`L`, `lem:defect-induction` gives complexity at least `C_W + a_t`.  The frozen
chain `L ≤ d λ = (p_t - 2^{a_t-1}) λ = c_{a_t}(p_t) λ` (lines 474--478) is
discharged internally by `entryWindow` and `excessCopies_entryCopyCount`.

The two clauses of `eq:direct-input` are the explicit binders `hNear` (first
clause, at the frozen literal density `1 - δ_U`) and `hInput` (second clause);
the banked `TwoCopyLadder.defectInduction_ofLadderInput` is consumed, so
`eq:direct-two-copy` is *derived* rather than re-assumed and no hypothesis
beyond the frozen pair enters. -/
theorem entryLevelStep {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2)
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    (R : Finset (Fin (entryCopyCount bout δU t) × X))
    (K : Finset (Fin (entryCopyCount bout δU t) → Y))
    (hK : K.Nonempty)
    (hrows : IsEquipartitionedGE R
      (Finset.univ : Finset (Fin (entryCopyCount bout δU t)))
      (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)))
    (hdefect : columnDefect K ≤ entryDefectL bout) :
    CW + entryLevelA bout δU t
      ≤ D (subgame (interlaceFun W (entryCopyCount bout δU t)) R K) := by
  have hlam : 0 < lambdaU δU := (lambdaU_spec hδ0 hδ1).2
  have hθ4 : θ ≤ 1 / 4 := by
    have := entryGate_theta_le hθ0 hgate
    linarith
  have hNear' : CW ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 θ (Real.exp (-(lambdaU δU)))) := by
    rw [(lambdaU_spec hδ0 hδ1).1]
    exact hNear
  have hdefect' : columnDefect K
      ≤ excessCopies (entryLevelA bout δU t) (entryCopyCount bout δU t)
          * lambdaU δU := by
    rw [excessCopies_entryCopyCount bout δU ht]
    exact le_trans hdefect (entryWindow hδ0 hδ1 hb).2
  exact defectInduction_ofLadderInput W CW (entryCopyCount bout δU t)
    (entryLevelA bout δU t) θ (3 / 5) (lambdaU δU)
    (entryCopyCount_copyGuard hδ0 hδ1 bout ht)
    (entryLevel_admissible hδ0 hδ1 hθ0 hgate ht) hθ0 hθ4 (by norm_num)
    (by norm_num) hlam hX hY hCW hmargin hNear' hInput R K hK hrows hdefect'

/-! ## Part 7: the three output rungs and the lower direction of
`eq:direct-output` -/

/-- **The `t`-th output rung** (`10-direct-bridge.tex:452--482`):
`comp(bracket(R⁺, 1, 2^{-b_out}, y/2^t)) ≥ C_W + a_t = C_W + r_Q - t`.

The kernel-checked `EthBridge.theorem_two` is *consumed*: it performs the
transpose, the good-copy dichotomy of lines 456--463 and the exact-image
projection of lines 465--469, and lands in `EthBridge.theorem_one`, i.e. in the
statement route-facaded as `DefectInduction.defectInduction`.  Its two
construction inputs are supplied here from the frozen `eq:direct-input` pair:
`hNear` directly, and `eq:direct-two-copy` through the banked
`EntryGates.bridgeBaseEstimates_of_entryGates`.  Its two counting inputs are
`entryGoodCopyCount`. -/
theorem directOutputRung {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2)
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    CW + entryLevelA bout δU t
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 / 5) / 2 ^ t)) := by
  have hlam : 0 < lambdaU δU := (lambdaU_spec hδ0 hδ1).2
  have hθ4 : θ ≤ 1 / 4 := by
    have := entryGate_theta_le hθ0 hgate
    linarith
  have hcast := Qwidth_cast bout δU
  obtain ⟨hpQ, -, h21⟩ :=
    entryGoodCopyCount (Fintype.card X) hb hδ0 hδ1 hX hθ0 hgate ht
  rw [entryCopyCount_eq hδ0 hδ1 hb t] at hpQ h21
  rw [hcast] at h21
  have hNear' : EthBridge.NearFull W CW θ (lambdaU δU) := by
    unfold EthBridge.NearFull
    rw [(lambdaU_spec hδ0 hδ1).1]
    exact hNear
  have hTwo : EthBridge.TwoCopyBundle W CW θ (3 / 5) :=
    (bridgeBaseEstimates_of_entryGates W CW bout hCW hθ0 hgate (by norm_num)
      (by norm_num) hInput).1
  exact EthBridge.theorem_two W CW (rQ bout δU) t θ (3 / 5) (lambdaU δU)
    (xOut bout) (four_le_rQ bout δU) ht (xOut_pos bout) (xOut_lt_one hb)
    (entryLevel_admissible hδ0 hδ1 hθ0 hgate ht) hθ0 hθ4 (by norm_num)
    (by norm_num) hlam hX hY hCW hmargin hNear' hTwo hpQ h21

/-- **The lower direction of `eq:direct-output`, robustness half**
(`10-direct-bridge.tex:483--487`; reader `eq:bridge-output`, second equation,
`04-bridge.tex:108--109`):
`Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q` at the globally fixed `y = 3/5`.

The three rungs `t = 0, 1, 2` are exactly the three branches of the typed `Λ`
(`TwoCopyLadder.le_LambdaGE_iff`), so the frozen sentence "This holds for
`t = 0, 1, 2`, and hence ..." is the assembly performed here.  The offsets stay
on the complexity side (`1 + comp`, `2 + comp`), so no truncated `ℕ`
subtraction is introduced. -/
theorem directOutputLower {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    CW + rQ bout δU
      ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
          (3 / 5) := by
  have h4 := four_le_rQ bout δU
  have h0 := directOutputRung W CW bout (t := 0) (by norm_num) hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput
  have h1 := directOutputRung W CW bout (t := 1) (by norm_num) hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput
  have h2 := directOutputRung W CW bout (t := 2) (by norm_num) hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput
  have e0 : ((3 : ℝ) / 5) / 2 ^ (0 : ℕ) = (3 : ℝ) / 5 := by norm_num
  have e1 : ((3 : ℝ) / 5) / 2 ^ (1 : ℕ) = ((3 : ℝ) / 5) / 2 := by norm_num
  have e2 : ((3 : ℝ) / 5) / 2 ^ (2 : ℕ) = ((3 : ℝ) / 5) / 4 := by norm_num
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have a0 : entryLevelA bout δU 0 = rQ bout δU := rfl
  have a1 : entryLevelA bout δU 1 = rQ bout δU - 1 := rfl
  have a2 : entryLevelA bout δU 2 = rQ bout δU - 2 := rfl
  rw [a0] at h0
  rw [a1] at h1
  rw [a2] at h2
  rw [le_LambdaGE_iff]
  exact ⟨h0, by omega, by omega⟩

/-- **The lower direction of `eq:direct-output`, complexity half**
(`10-direct-bridge.tex:488`): "The `t = 0` case gives
`comp(R⁺) ≥ C_W + r_Q`".

The top rung bounds a nonempty family of restrictions of the one-copy
interlace of `R⁺`, so it bounds that interlace
(`PilotStage3.familyComplexity_le_ambient`), which in turn costs no more than
`R⁺` itself (`PilotStage3.powerOfTwoInterlace_upper` at exponent `0`).  Only
the **lower** direction is claimed: the frozen equality of `eq:direct-output`
is not stated here (GAP-EXPOSED item 1). -/
theorem directOutputComplexityLower {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    CW + rQ bout δU ≤ D (EthBridge.Rnext W (Qwidth bout δU)) := by
  classical
  have h0 := directOutputRung W CW bout (t := 0) (by norm_num) hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput
  have e0 : ((3 : ℝ) / 5) / 2 ^ (0 : ℕ) = (3 : ℝ) / 5 := by norm_num
  rw [e0] at h0
  have a0 : entryLevelA bout δU 0 = rQ bout δU := rfl
  rw [a0] at h0
  have hcardrow : 1 ≤ Fintype.card (Fin (Qwidth bout δU) → Y) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.one_le_pow _ _ hY
  have hne : (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X)
      1 (xOut bout) ((3 : ℝ) / 5)).Nonempty :=
    bracketGE.nonempty 1 (xOut bout) (3 / 5) (xOut_le_one bout) (by norm_num)
      hcardrow
  have hfam := familyComplexity_le_ambient
    (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1) hne
  have hone : D (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
      ≤ D (EthBridge.Rnext W (Qwidth bout δU)) := by
    have h := powerOfTwoInterlace_upper (EthBridge.Rnext W (Qwidth bout δU)) 0
    simpa using h
  omega

/-! ## Non-vacuity and the statement poles

LANE-GATE 3.  Each witness excludes one degeneracy that a green build cannot
see.  Nothing here asserts that an inhabitant of `eq:direct-input` exists — it
cannot, until Stages 1--4 land (GAP-EXPOSED item 3). -/

/-- **Non-vacuity (i): Candidate B of the header is refuted in Lean.**

At `b_out = 0` the vendored ceiling `⌈L/λ⌉₊` reads `0` while the frozen exact
search of line 414 reads `1`.  A `d = 0` would make `p_t = 2^{a_t-1}`, which
**fails** the strict copy guard of line 427, so the two encodings are not
interchangeable and the identification `entryCount_eq_excess` genuinely needs
its `b_out ≥ 1` hypothesis. -/
theorem entryCount_refutes_candidateB {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) :
    EthBridge.entryExcess (xOut 0) (lambdaU δU) = 0 ∧ entryCount 0 δU = 1 := by
  have hx0 : xOut 0 = 1 := by
    unfold xOut
    norm_num
  constructor
  · unfold EthBridge.entryExcess EthBridge.entryDefect
    rw [hx0]
    norm_num
  · refine le_antisymm ?_ (entryCount_pos hδ0 hδ1 0)
    refine entryCount_min le_rfl ?_
    rw [hx0]
    have : (1 : ℝ) - δU ≤ 1 := by linarith
    simpa using this

/-- **Non-vacuity (ii): the entry levels of the carried witness are interior
and admissible.**

At the `BRIDGE-ENTRY-001` witness `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`
(with `Q_0 = 4800`, `r_Q = 13`, `Q = 8192`), the three entry levels read
`13, 12, 11` — none of them the degenerate `0` — and every one of them is
admissible at that row threshold. -/
theorem entryLevels_fire_first_witness :
    entryLevelA 1 (1 / 60) 0 = 13 ∧ entryLevelA 1 (1 / 60) 1 = 12 ∧
      entryLevelA 1 (1 / 60) 2 = 11 ∧
      levelAdmissible (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 0) ∧
      levelAdmissible (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 1) ∧
      levelAdmissible (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 2) := by
  obtain ⟨-, -, hrQ, -, -, -, -⟩ := directEntryGates_fires
  have h0 : entryLevelA 1 (1 / 60) 0 = 13 := by
    unfold entryLevelA
    omega
  have h1 : entryLevelA 1 (1 / 60) 1 = 12 := by
    unfold entryLevelA
    omega
  have h2 : entryLevelA 1 (1 / 60) 2 = 11 := by
    unfold entryLevelA
    omega
  refine ⟨h0, h1, h2, ?_, ?_, ?_⟩
  · rw [h0]; simp only [levelAdmissible]; norm_num
  · rw [h1]; simp only [levelAdmissible]; norm_num
  · rw [h2]; simp only [levelAdmissible]; norm_num

/-- **Non-vacuity (iii): the excess-copy count of the carried witness is deep
in the interior.**

`41 ≤ d ≤ 42` at `b_out = 1`, `δ_U = 1/60`, pinned from `eq:direct-d-window`
against the landed bounds `δ_U ≤ λ ≤ 17/1000` and Mathlib's decimal window for
`ln 2`.  So the excess-copy count is neither the degenerate `0` that Candidate
B permits nor the boundary value `1`; the bridge genuinely buys dozens of
copies. -/
theorem entryCount_fires_first_witness :
    41 ≤ entryCount 1 (1 / 60) ∧ entryCount 1 (1 / 60) ≤ 42 := by
  have hδ0 : (0 : ℝ) < 1 / 60 := by norm_num
  have hδ1 : (1 : ℝ) / 60 < 1 := by norm_num
  have hL : entryDefectL 1 = Real.log 2 := by
    unfold entryDefectL
    norm_num
  obtain ⟨hlow, hhigh⟩ := entryWindow hδ0 hδ1 (le_refl 1)
  rw [hL] at hlow hhigh
  have hlamlow : (1 : ℝ) / 60 ≤ lambdaU (1 / 60) := deltaU_le_lambdaU hδ1
  have hlamhigh : lambdaU (1 / 60) ≤ 17 / 1000 :=
    lambdaU_le_of_deltaU_le hδ0 le_rfl
  have hlog_lt := Real.log_two_lt_d9
  have hlog_gt := Real.log_two_gt_d9
  constructor
  · by_contra hcon
    have hle : entryCount 1 (1 / 60) ≤ 40 := by omega
    have hcast : ((entryCount 1 (1 / 60) : ℕ) : ℝ) ≤ 40 := by exact_mod_cast hle
    nlinarith [hhigh, hcast, hlamhigh, hlog_gt]
  · by_contra hcon
    have hge : 43 ≤ entryCount 1 (1 / 60) := by omega
    have hcast : (43 : ℝ) ≤ ((entryCount 1 (1 / 60) : ℕ) : ℝ) := by
      exact_mod_cast hge
    nlinarith [hlow, hcast, hlamlow, hlog_lt]

/-- **Non-vacuity (iv): the copy count sits strictly inside the outer
interlace.**

At the same witness `p_0 = 2^{12} + d` with `41 ≤ d ≤ 42`, so
`4137 ≤ p_0 ≤ 4138`: strictly above `2^{a_0 - 1} = 4096` (the strict copy guard
of line 427 has room to spare) and strictly below `Q = 8192` (the outer
interlace is not exhausted).  A degenerate inhabitant would sit at one of the
two ends. -/
theorem entryCopyCount_fires_first_witness :
    4096 < entryCopyCount 1 (1 / 60) 0 ∧
      entryCopyCount 1 (1 / 60) 0 < Qwidth 1 (1 / 60) ∧
      2 ^ entryLevelA 1 (1 / 60) 0 < 2 * entryCopyCount 1 (1 / 60) 0 := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  obtain ⟨hd1, hd2⟩ := entryCount_fires_first_witness
  obtain ⟨ha0, -, -, -, -, -⟩ := entryLevels_fire_first_witness
  have hp : entryCopyCount 1 (1 / 60) 0
      = 2 ^ (entryLevelA 1 (1 / 60) 0 - 1) + entryCount 1 (1 / 60) := rfl
  rw [ha0] at hp
  norm_num at hp
  rw [hQ, hp, ha0]
  refine ⟨by omega, by omega, by norm_num; omega⟩

/-- **Non-vacuity (v): the banked ceiling ladder is exhibited tight, with no
zero rung, across the three entry levels.**

At the carried witness and `m = 192000` the frozen floors read
`A_{13} = 8192`, `A_{12} = 4096`, `A_{11} = 2048`, and
`eq:direct-ceiling-ladder` holds with **equality** at both steps.  A degenerate
inhabitant would read `A_{a_t} = 0` at every level and satisfy the ladder
trivially; this one does not. -/
theorem entryRowFloor_ladder_fires_first_witness :
    rowFloor 192000 (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 0) = 8192 ∧
      rowFloor 192000 (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 1) = 4096 ∧
      rowFloor 192000 (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 2) = 2048 ∧
      rowFloor 192000 (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 1)
        = ⌈(rowFloor 192000 (1 / 192000 : ℝ)
            (entryLevelA 1 (1 / 60) 0) : ℝ) / 2⌉₊ ∧
      rowFloor 192000 (1 / 192000 : ℝ) (entryLevelA 1 (1 / 60) 2)
        = ⌈(rowFloor 192000 (1 / 192000 : ℝ)
            (entryLevelA 1 (1 / 60) 1) : ℝ) / 2⌉₊ := by
  obtain ⟨ha0, ha1, ha2, -, -, -⟩ := entryLevels_fire_first_witness
  rw [ha0, ha1, ha2]
  have h0 : rowFloor 192000 (1 / 192000 : ℝ) 13 = 8192 := by
    rw [rowFloor]
    norm_num
  have h1 : rowFloor 192000 (1 / 192000 : ℝ) 12 = 4096 := by
    rw [rowFloor]
    norm_num
  have h2 : rowFloor 192000 (1 / 192000 : ℝ) 11 = 2048 := by
    rw [rowFloor]
    norm_num
  refine ⟨h0, h1, h2, ?_, ?_⟩
  · rw [h0, h1]; norm_num
  · rw [h1, h2]; norm_num

/-- **Non-vacuity (vi): the three width bounds fire at the carried witness.**

`eq:direct-Q-bounds` at `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, where the
first entry gate is **tight** (`4 Q_0 θ = δ` exactly).  Every bound is
discharged by computation from the landed apparatus, not assumed. -/
theorem directQBounds_fire_first_witness :
    8 * entryDefectL 1 / (deltaFixed * lambdaU (1 / 60))
        ≤ ((Qwidth 1 (1 / 60) : ℕ) : ℝ) ∧
      8 / deltaFixed ≤ ((Qwidth 1 (1 / 60) : ℕ) : ℝ) ∧
      ((Qwidth 1 (1 / 60) : ℕ) : ℝ) * (1 / 192000 : ℝ) < deltaFixed / 2 := by
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  exact directQBounds (by norm_num) (by norm_num) (by norm_num) hgate

/-- **Non-vacuity (vii): the level restriction genuinely bites.**

At `θ = 1` — inside line 39's own range `0 < θ ≤ 1` — the top entry level is
**inadmissible**, by the banked
`DirectOutput.levelAdmissible_refuted_at_large_theta`.  So admissibility at
`a_0` is a consequence of the entry gate and not of the frozen range of `θ`,
and a transcription that dropped the gate would be strictly weaker. -/
theorem entryLevel_refuted_at_large_theta (bout : ℕ) (δU : ℝ) :
    ¬ levelAdmissible (1 : ℝ) (entryLevelA bout δU 0) := by
  have h4 := four_le_rQ bout δU
  have a0 : entryLevelA bout δU 0 = rQ bout δU := rfl
  rw [a0]
  exact levelAdmissible_refuted_at_large_theta (by omega)

/-- **Non-vacuity (viii): the delivered conclusion is not trivial.**

Both lower bounds deliver at least `7`, from the frozen `C_W ≥ 3` (line 40)
and the landed `r_Q ≥ 4` (`EntryGates.four_le_rQ`).  A bound of `0` would be
free; this one is not. -/
theorem directOutputLower_conclusion_nontrivial {CW bout : ℕ} {δU : ℝ}
    (hCW : 3 ≤ CW) : 7 ≤ CW + rQ bout δU := by
  have h4 := four_le_rQ bout δU
  omega

/-! ### The second entry-gate witness, carried through the same apparatus

`BRIDGE-OUTPUT-001` pins a second legal point `b_out = 1`, `δ_U = 1/200`,
`θ = 1/640000` (`Q_0 = 16000`, `r_Q = 14`, `Q = 16384`, first gate again
tight).  Carrying it through `d`, `a_t`, `p_t`, the width bounds and the row
floors is what shows the entry apparatus is not tuned to one numeral: every
readout moves, and none of them moves to a degenerate value. -/

/-- **Non-vacuity (ix): the entry levels of the second witness.**

At `b_out = 1`, `δ_U = 1/200`, `θ = 1/640000` the three entry levels read
`14, 13, 12` — one higher than the first witness, as the smaller deletion
tolerance forces — and every one of them is admissible at that row
threshold. -/
theorem entryLevels_fire_second_witness :
    entryLevelA 1 (1 / 200) 0 = 14 ∧ entryLevelA 1 (1 / 200) 1 = 13 ∧
      entryLevelA 1 (1 / 200) 2 = 12 ∧
      levelAdmissible (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 0) ∧
      levelAdmissible (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 1) ∧
      levelAdmissible (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 2) := by
  obtain ⟨-, hrQ, -, -, -, -, -⟩ := directOutput_fires_second_witness
  have h0 : entryLevelA 1 (1 / 200) 0 = 14 := by
    unfold entryLevelA
    omega
  have h1 : entryLevelA 1 (1 / 200) 1 = 13 := by
    unfold entryLevelA
    omega
  have h2 : entryLevelA 1 (1 / 200) 2 = 12 := by
    unfold entryLevelA
    omega
  refine ⟨h0, h1, h2, ?_, ?_, ?_⟩
  · rw [h0]; simp only [levelAdmissible]; norm_num
  · rw [h1]; simp only [levelAdmissible]; norm_num
  · rw [h2]; simp only [levelAdmissible]; norm_num

/-- **Non-vacuity (x): the excess-copy count of the second witness is interior
too, and strictly larger.**

`41 ≤ d ≤ 139` at `b_out = 1`, `δ_U = 1/200`, pinned from
`eq:direct-d-window` exactly as at the first witness.  The count is again
neither the degenerate `0` that Candidate B permits nor the boundary `1`, and
the smaller deletion tolerance genuinely buys the bridge more copies. -/
theorem entryCount_fires_second_witness :
    41 ≤ entryCount 1 (1 / 200) ∧ entryCount 1 (1 / 200) ≤ 139 := by
  have hδ0 : (0 : ℝ) < 1 / 200 := by norm_num
  have hδ1 : (1 : ℝ) / 200 < 1 := by norm_num
  have hL : entryDefectL 1 = Real.log 2 := by
    unfold entryDefectL
    norm_num
  obtain ⟨hlow, hhigh⟩ := entryWindow hδ0 hδ1 (le_refl 1)
  rw [hL] at hlow hhigh
  have hlamlow : (1 : ℝ) / 200 ≤ lambdaU (1 / 200) := deltaU_le_lambdaU hδ1
  have hlamhigh : lambdaU (1 / 200) ≤ 17 / 1000 :=
    lambdaU_le_of_deltaU_le hδ0 (by norm_num)
  have hlog_lt := Real.log_two_lt_d9
  have hlog_gt := Real.log_two_gt_d9
  constructor
  · by_contra hcon
    have hle : entryCount 1 (1 / 200) ≤ 40 := by omega
    have hcast : ((entryCount 1 (1 / 200) : ℕ) : ℝ) ≤ 40 := by exact_mod_cast hle
    nlinarith [hhigh, hcast, hlamhigh, hlog_gt]
  · by_contra hcon
    have hge : 140 ≤ entryCount 1 (1 / 200) := by omega
    have hcast : (140 : ℝ) ≤ ((entryCount 1 (1 / 200) : ℕ) : ℝ) := by
      exact_mod_cast hge
    nlinarith [hlow, hcast, hlamlow, hlog_lt]

/-- **Non-vacuity (xi): the second witness's copy count is also strictly
inside the outer interlace.**

`p_0 = 2^{13} + d` with `41 ≤ d ≤ 139`, so `8233 ≤ p_0 ≤ 8331`: strictly above
`2^{a_0 - 1} = 8192` and strictly below `Q = 16384`. -/
theorem entryCopyCount_fires_second_witness :
    8192 < entryCopyCount 1 (1 / 200) 0 ∧
      entryCopyCount 1 (1 / 200) 0 < Qwidth 1 (1 / 200) ∧
      2 ^ entryLevelA 1 (1 / 200) 0 < 2 * entryCopyCount 1 (1 / 200) 0 := by
  obtain ⟨-, -, hQ, -, -, -, -⟩ := directOutput_fires_second_witness
  obtain ⟨hd1, hd2⟩ := entryCount_fires_second_witness
  obtain ⟨ha0, -, -, -, -, -⟩ := entryLevels_fire_second_witness
  have hp : entryCopyCount 1 (1 / 200) 0
      = 2 ^ (entryLevelA 1 (1 / 200) 0 - 1) + entryCount 1 (1 / 200) := rfl
  rw [ha0] at hp
  norm_num at hp
  rw [hQ, hp, ha0]
  refine ⟨by omega, by omega, by norm_num; omega⟩

/-- **Non-vacuity (xii): the ceiling ladder is tight and zero-free at the
second witness as well.**

At `m = 640000` and `θ = 1/640000` the entry-level floors read
`A_{14} = 16384`, `A_{13} = 8192`, `A_{12} = 4096`, with equality at both
steps of `eq:direct-ceiling-ladder`. -/
theorem entryRowFloor_ladder_fires_second_witness :
    rowFloor 640000 (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 0) = 16384 ∧
      rowFloor 640000 (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 1) = 8192 ∧
      rowFloor 640000 (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 2) = 4096 ∧
      rowFloor 640000 (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 1)
        = ⌈(rowFloor 640000 (1 / 640000 : ℝ)
            (entryLevelA 1 (1 / 200) 0) : ℝ) / 2⌉₊ ∧
      rowFloor 640000 (1 / 640000 : ℝ) (entryLevelA 1 (1 / 200) 2)
        = ⌈(rowFloor 640000 (1 / 640000 : ℝ)
            (entryLevelA 1 (1 / 200) 1) : ℝ) / 2⌉₊ := by
  obtain ⟨ha0, ha1, ha2, -, -, -⟩ := entryLevels_fire_second_witness
  rw [ha0, ha1, ha2]
  have h0 : rowFloor 640000 (1 / 640000 : ℝ) 14 = 16384 := by
    rw [rowFloor]
    norm_num
  have h1 : rowFloor 640000 (1 / 640000 : ℝ) 13 = 8192 := by
    rw [rowFloor]
    norm_num
  have h2 : rowFloor 640000 (1 / 640000 : ℝ) 12 = 4096 := by
    rw [rowFloor]
    norm_num
  refine ⟨h0, h1, h2, ?_, ?_⟩
  · rw [h0, h1]; norm_num
  · rw [h1, h2]; norm_num

/-- **Non-vacuity (xiii): the three width bounds fire at the second witness.**

`eq:direct-Q-bounds` at `b_out = 1`, `δ_U = 1/200`, `θ = 1/640000`, where the
first entry gate is again tight (`4 Q_0 θ = δ` exactly). -/
theorem directQBounds_fire_second_witness :
    8 * entryDefectL 1 / (deltaFixed * lambdaU (1 / 200))
        ≤ ((Qwidth 1 (1 / 200) : ℕ) : ℝ) ∧
      8 / deltaFixed ≤ ((Qwidth 1 (1 / 200) : ℕ) : ℝ) ∧
      ((Qwidth 1 (1 / 200) : ℕ) : ℝ) * (1 / 640000 : ℝ) < deltaFixed / 2 := by
  have hgate : 4 * Q0 1 (1 / 200) * (1 / 640000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  exact directQBounds (by norm_num) (by norm_num) (by norm_num) hgate

/-! ### Conditional firing witnesses for the two delivered bounds

LANE-GATE 3, applied to the deliverables themselves.  `X`, `Y` and `W` stay
**universally quantified** and the two clauses of `eq:direct-input` stay
hypotheses — they have no exhibited inhabitant and can have none until Stages
1--4 land (GAP-EXPOSED item 3).  What these two theorems establish is that
*every other* binder of `directOutputLower` and
`directOutputComplexityLower` — the depth, the deletion tolerance, the row
threshold, the entry gate and, in particular, the second-gate margin
`3λ + (7/5) ln 2 ≤ -2 ln(3/5)` — is simultaneously satisfiable at legal
frozen parameters, and that the delivered bounds then read the concrete
`C_W + r_Q = 16` and `17`.  A premise bundle satisfiable only at degenerate or
cardinality-contradictory values would fail exactly here. -/

/-- **Non-vacuity (xiv): both lower bounds fire at the first witness.**

`b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `C_W = 3` (the boundary of line
40), where `Q = 8192`, `x_out = 1/2` and `r_Q = 13`, so both delivered bounds
read `16`.  Every numeric binder — including the second-gate margin, through
the banked `EntryGates.secondEntryGate_of_deltaU_small` — is discharged by
computation, not assumed. -/
theorem directOutputLower_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 (1 / 192000) (1 - 1 / 60)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 192000) (3 / 5)) :
    Qwidth 1 (1 / 60) = 8192 ∧ xOut 1 = 1 / 2 ∧
      (3 : ℕ) + 13 ≤ LambdaGE (EthBridge.Rnext W (Qwidth 1 (1 / 60))) 1
        (xOut 1) (3 / 5) ∧
      (3 : ℕ) + 13 ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) := by
  obtain ⟨-, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 60) (le_refl (1 / 60 : ℝ))
  have hx : xOut 1 = 1 / 2 := by
    unfold xOut
    norm_num
  have hlow := directOutputLower W 3 1 (δU := 1 / 60) (θ := 1 / 192000)
    (le_refl 1) (by norm_num) (by norm_num) (by norm_num) hgate hmargin hX hY
    (le_refl 3) hNear hInput
  have hcomp := directOutputComplexityLower W 3 1 (δU := 1 / 60)
    (θ := 1 / 192000) (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
    hgate hmargin hX hY (le_refl 3) hNear hInput
  rw [hrQ] at hlow hcomp
  exact ⟨hQ, hx, hlow, hcomp⟩

/-- **Non-vacuity (xv): both lower bounds fire at the second witness, at a
different arithmetic.**

`b_out = 1`, `δ_U = 1/200`, `θ = 1/640000`, `C_W = 3`, where `Q = 16384` and
`r_Q = 14`, so both delivered bounds read `17`.  The width, the canonical
exponent and the delivered constant all move with the deletion tolerance,
which a bundle satisfiable at only one numeral could not do. -/
theorem directOutputLower_fires_second_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 (1 / 640000) (1 - 1 / 200)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 640000) (3 / 5)) :
    Qwidth 1 (1 / 200) = 16384 ∧ xOut 1 = 1 / 2 ∧
      (3 : ℕ) + 14 ≤ LambdaGE (EthBridge.Rnext W (Qwidth 1 (1 / 200))) 1
        (xOut 1) (3 / 5) ∧
      (3 : ℕ) + 14 ≤ D (EthBridge.Rnext W (Qwidth 1 (1 / 200))) := by
  obtain ⟨-, hrQ, hQ, -, -, -, -⟩ := directOutput_fires_second_witness
  have hgate : 4 * Q0 1 (1 / 200) * (1 / 640000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 200) (by norm_num : (1 / 200 : ℝ) ≤ 1 / 60)
  have hx : xOut 1 = 1 / 2 := by
    unfold xOut
    norm_num
  have hlow := directOutputLower W 3 1 (δU := 1 / 200) (θ := 1 / 640000)
    (le_refl 1) (by norm_num) (by norm_num) (by norm_num) hgate hmargin hX hY
    (le_refl 3) hNear hInput
  have hcomp := directOutputComplexityLower W 3 1 (δU := 1 / 200)
    (θ := 1 / 640000) (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
    hgate hmargin hX hY (le_refl 3) hNear hInput
  rw [hrQ] at hlow hcomp
  exact ⟨hQ, hx, hlow, hcomp⟩

end EthInapproximability.ParameterizedNP.DirectOutputLower
