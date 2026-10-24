import EthInapproximability.ParameterizedNP.ThreeCopyRowStep

/-!
# Parameterized NP route: the entry apparatus of the direct bridge

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-ENTRY-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1g` tranche as the entry apparatus that
`thm:direct-robustification` fixes *before* any of its conclusions: the
deletion exponent `λ`, the threshold `Q_0`, the canonical width `Q = 2^{r_Q}`,
the gate pair `eq:direct-entry-gates`, and the legality implication that makes
the already-landed `eq:direct-three-copy` invocation applicable.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`, `thm:direct-robustification` (label
  line 35):
  * lines 36--37, "Use the globally fixed constants `δ = 1/10` and
    `y = 1/2 + δ = 3/5` from `sec:preliminaries`";
  * line 38, `0 < δ_U < 1`; line 39, `0 < θ ≤ 1`; line 40, `comp W = C_W ≥ 3`;
  * line 41, "Fix an integer `b_out ≥ 1`, put";
  * line 43, `λ = -ln(1 - δ_U)`;
  * lines 47--49, `Q_0 = max{8 b_out/(δ δ_U), 8/δ, 16}`;
  * line 51, "Let `Q = 2^{r_Q}` be the least power of two at least `Q_0`";
  * `eq:direct-entry-gates` (label line 56), the displayed pair at lines
    53--55, `4 Q_0 θ ≤ δ` and `3λ + (7/5) ln 2 ≤ -2 ln y`;
  * lines 58--60, "The first inequality and `Q_0 ≥ 16` imply
    `4θ ≤ δ/Q_0 < 1`, so the invocation `eq:direct-three-copy` is legal."
* `sections/10-direct-bridge.tex`, `eq:direct-three-copy` (label line 31) and
  `eq:direct-input` clause two (line 10) — the two already-landed statements
  the legality implication is wired to.  Neither is re-proved here.
* `sections/03-preliminaries.tex`, lines 216--219, the globally fixed
  `δ = 1/10` and `y = 1/2 + δ = 3/5`.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex`.  The file was
opened and each cited item checked to state the same fact:

* the fixed-constant display at lines 22--26, `δ = 1/10`, `y = 3/5`,
  `λ = -ln(1 - δ_U)` — counterpart of `deltaFixed` and `lambdaU`;
* `eq:bridge-Q0` (label line 92, display lines 88--93),
  `Q_0 = max{8 b^+/(δ δ_U), 8/δ, 16}` — counterpart of `Q0`;
* line 94, "and let `Q = 2^{r_Q}` be the least power of two at least `Q_0`" —
  counterpart of `rQ`, `Qwidth`, and the three claim theorems
  `Qwidth_eq_two_pow`, `Q0_le_Qwidth`, `Qwidth_least`;
* `eq:bridge-exact-Q-gates` (label line 99, display lines 95--100),
  `4 Q_0 θ ≤ δ` and `3λ + (7/5) ln 2 ≤ -2 ln y` — counterpart of
  `directEntryGates`.

These four are distinct labelled/displayed items of the reader's
`thm:near-to-robust`; **no reader item is assigned twice**.  `INHERIT-001`
records `thm:near-to-robust` (label line 82) as a counterpart for the
*projection* facts it consumes, not for these entry-apparatus displays, and
`BRIDGE-DEFECT-001` explicitly claims none of them.  The reader items
`eq:bridge-output` (label line 110), `eq:bridge-carriers` (label line 117),
and the selector sentence at lines 112--113 stay **unclaimed** and remain with
`BRIDGE-001`.

The legality implication (`entryLegality`) has **no reader counterpart and is
not assigned one**: the reader's `thm:near-to-robust` does not spell that step
out, and the reader's `lem:bridge-base-estimates` carries the resulting
condition as its own hypothesis `0 < θ ≤ 1/4` (line 32) — an item already
assigned, in its two inequalities, to `BRIDGE-TWOCOPY-001` and
`BRIDGE-THREECOPY-001`.  Accordingly the two wiring corollaries
`directThreeCopy_of_entryGates` and `bridgeBaseEstimates_of_entryGates` claim
**no** reader item: they consume the landed theorems of those two rows under
the frozen autoformalization sentence at lines 58--60 and add no reader-facing
statement of their own.  No reader prose is cited as a statement.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is either
  a plain transcription of a frozen display, a general property of one of
  those transcriptions, or the frozen legality sentence applied to results
  already landed in `BRIDGE-TWOCOPY-001` and `BRIDGE-THREECOPY-001`.  No
  communication-complexity lemma is introduced, adapted, or re-proved.
* The second gate is **consumed, never redefined**: `entry_gate_of_lambda_small`
  and `entry_gate_lambda_window` are the landed `BRIDGE-DEFECT-001` lemmas
  (`DefectInduction.lean`), and `exp_neg_lambda` is likewise consumed as
  `lambdaU_spec`.  Nothing in that module is edited, and `λ` is not defined
  twice: `lambdaU_eq` records that `lambdaU δ_U` is the very expression
  `-Real.log (1 - δ_U)` those lemmas are stated about.
* Imports: `EthInapproximability.ParameterizedNP.ThreeCopyRowStep` only, hence
  `TwoCopyLadder.lean`, `DefectInduction.lean`, `InheritedContracts.lean` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported, so the
  AGHP balanced-family axiom is not in scope, and there is no contact with
  `EXPANDER-001` (which by design has no Lean declaration and would have to
  remain a named hypothesis).
* External adapters: none.  Nothing here is axiomatized.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

The one genuinely open encoding choice is the canonical width: line 51 says
`Q = 2^{r_Q}` is "the least power of two at least `Q_0`".  Both candidates
were written out and run against the same three aux lemmas — (a) the defining
upper property `Q_0 ≤ 2^{r_Q}`, (b) minimality `Q_0 ≤ 2^r → r_Q ≤ r`, and
(c) the pinned readout `r_Q = 13` at the route value `Q_0 = 4800` used by the
non-vacuity witness.

**Candidate A (landed).**  `r_Q = sInf {r : ℕ | Q_0 ≤ 2^r}`, `Q = 2^{r_Q}`.
This *is* line 51 read literally: `2^·` is monotone, so the least power of two
at least `Q_0` is `2` raised to the least admissible exponent.  All three aux
lemmas proved; (a) is `Nat.sInf_mem` and (b) is `Nat.sInf_le`, each a
one-liner, and **neither carries a side condition**.

**Candidate B (rejected).**  `r_Q = ⌈log₂ Q_0⌉₊`, `Q = 2^{r_Q}`.  All three
aux lemmas are also provable, so this candidate is not disqualified outright —
it is beaten on faithfulness and length.  Faithfulness: both (a) and (b)
require the extra guard `0 < Q_0`, which line 51 does not state, and
minimality becomes an analytic consequence of `Nat.le_ceil` rather than the
defining property; the frozen sentence quantifies over powers of two, not over
logarithms.  Length: the three proofs run 20 lines against Candidate A's 10,
and the pinned readout (c) needs two `Real.rpow` window bounds where
Candidate A needs one `le_antisymm` over `Nat.sInf`.

Ranking (aux lemmas proved, faithfulness, length): A = 3/3, guard-free,
literal, 10 lines; B = 3/3, two invented guards, derived minimality, 20 lines.
A landed.

## Faithfulness notes (mechanical rules M1--M10)

* Every definition is a plain `def` with no field carrying a conclusion.  The
  module introduces **no structure at all**; `directEntryGates` is a `Prop`
  abbreviation for the *conjunction the paper displays*, not a bundle of
  derived facts, and `directEntryGates_iff` shows it is exactly that
  conjunction.  Every deliverable is stated with **explicit binders** — the
  gate appears as the binder `hgate`, never as the bundle — so no derived
  telescope is restated as a hypothesis.
* `δ` is the route's globally fixed `1/10` (line 37, `03-preliminaries.tex`
  lines 216--219) and is transcribed as the named constant `deltaFixed`, not
  as a new parameter.  Making `δ` a binder would have generalized the frozen
  theorem and forced guards (`δ < 2√2`) onto callers that the paper does not
  have.  `y` **is** kept as a binder, because line 55 writes the second gate
  with the symbol `y`.
* `b_out` is an integer `≥ 1` (line 41), so it is a `ℕ` binder; the guard
  `1 ≤ b_out` appears only where the paper's own statement uses it
  (`Q0_eq_route`, `Q0_gt_sixteen_of_route`), never on the definition, because
  line 47 defines `Q_0` for the fixed `b_out` without re-stating the guard.
* `Q` is a **width**, i.e. a copy count, so `Qwidth` lands in `ℕ` and the
  comparison with `Q_0` is `Q_0 ≤ (Q : ℝ)`.  The other interlace width `q` of
  the scale-alignment step does not appear here and is not conflated with it.
* `λ` is not redefined: `lambdaU_eq` is `rfl`, and the second gate is
  discharged by the landed `DefectInduction` lemmas, consumed unchanged.
* Trivial-witness pole.  There is **no existential deliverable** in this
  module: `rQ` and `Qwidth` are pinned constructions and every claim about
  them is a named-def claim, exactly as the pipeline requires when a trivial
  witness cannot be excluded.  In particular `Qwidth_least` is *not* "there
  exists a power of two above `Q_0`" (which `2^r` for huge `r` would satisfy);
  it is the minimality of the pinned `Qwidth`, which the trivial large witness
  refutes rather than satisfies.
* Vacuous-hypothesis pole.  `directEntryGates` is not free: it is **false**
  at `δ_U = δ = 1/10` for every `b_out`, `θ` (`directEntryGates_refuted_at_deltaU_eq_delta`,
  via the landed `entry_gate_lambda_window`), and false at a legal `δ_U` with
  `θ` too large (`directEntryGates_refuted_at_large_theta`).  So both halves of
  the pair genuinely constrain the parameters.
* Non-degeneracy of the maximum.  `Q0_gt_sixteen_of_route` shows the constant
  branch `16` is *never* the operative one at legal route values, and
  `Q0_eq_route` identifies the operative branch as the first, `80 b_out/δ_U`.
  A witness sitting on the `16` branch would be the degenerate inhabitant this
  excludes.
* Non-vacuity at legal values.  `directEntryGates_fires` pins
  `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `y = 3/5` — all strictly inside
  the frozen ranges `b_out ≥ 1`, `0 < δ_U < 1`, `0 < θ ≤ 1` — and computes
  `Q_0 = 4800`, `r_Q = 13`, `Q = 8192`, with the **first gate tight**
  (`4 Q_0 θ = δ` exactly) and the legality readout `4θ ≤ δ/Q_0 < 1` explicit.
  `r_Q = 13` is in the interior, not the degenerate `r_Q = 0`; `four_le_rQ`
  proves `r_Q ≥ 4` in general, so the selector always costs at least four bits.

## GAP-EXPOSED

`thm:direct-robustification` is **not** claimed.  Its conclusion
`eq:direct-output` (label line 71), the interlaced transpose
`R⁺ = Int_Q(W)^T` (line 63), the exact complexity `comp R⁺ = C_W + r_Q`, the
output robustness `Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q`, the selector
sentence at lines 73--74, and the carrier identities are all untouched.
`eq:direct-input` remains a pair of named hypotheses supplied by Sections
8--9.  Nothing about route completion is claimed.
-/

namespace EthInapproximability.ParameterizedNP.EntryGates

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.TwoCopyLadder
open EthInapproximability.ParameterizedNP.ThreeCopyRowStep

/-! ## The entry apparatus of `thm:direct-robustification`

`sections/10-direct-bridge.tex:36--56`; reader `04-bridge.tex:22--26` and
`86--99`.  Plain definitions only: no conclusion of the theorem is placed in
any of them. -/

/-- The route's globally fixed `δ = 1/10` (`10-direct-bridge.tex:37`,
`03-preliminaries.tex:216--219`; reader `04-bridge.tex:24`).  It is a fixed
constant of the route, not a parameter of the bridge, so it is transcribed as
a constant rather than as a binder. -/
noncomputable def deltaFixed : ℝ := 1 / 10

@[simp] lemma deltaFixed_eq : deltaFixed = 1 / 10 := rfl

/-- **`λ = -ln(1 - δ_U)`** (`10-direct-bridge.tex:43`; reader
`04-bridge.tex:25`).

The deletion exponent of the bridge.  This is the *same expression* the landed
`DefectInduction` lemmas are stated about (`lambdaU_eq` below is `rfl`), so `λ`
is named here without being defined a second time. -/
noncomputable def lambdaU (δU : ℝ) : ℝ := -Real.log (1 - δU)

/-- **`Q_0 = max{8 b_out/(δ δ_U), 8/δ, 16}`** (`10-direct-bridge.tex:47--49`;
reader `eq:bridge-Q0`, `04-bridge.tex:91`).

The three-term maximum written literally, with the globally fixed `δ` of
line 37 substituted for the symbol `δ`.  Nothing is simplified away: the
`8/δ` and `16` branches are kept so that `Q0_ge_sixteen`, which line 58 uses
by name, is a property of the transcription rather than of a rewritten
formula. -/
noncomputable def Q0 (bout : ℕ) (δU : ℝ) : ℝ :=
  max (max (8 * (bout : ℝ) / (deltaFixed * δU)) (8 / deltaFixed)) 16

/-- **The canonical exponent `r_Q`** (`10-direct-bridge.tex:51`; reader
`04-bridge.tex:94`): `Q = 2^{r_Q}` is the least power of two at least `Q_0`.

Since `r ↦ 2^r` is monotone, "least power of two at least `Q_0`" is `2` raised
to the least exponent `r` with `Q_0 ≤ 2^r`, which is this infimum.  The
landed encoding (Candidate A of the header); `rQ_min` is its defining
minimality and carries no side condition. -/
noncomputable def rQ (bout : ℕ) (δU : ℝ) : ℕ :=
  sInf {r : ℕ | Q0 bout δU ≤ (2 : ℝ) ^ r}

/-- **The canonical interlace width `Q = 2^{r_Q}`**
(`10-direct-bridge.tex:51`; reader `04-bridge.tex:94`).

`Q` is a copy count, so it lands in `ℕ`; the comparison against the real
threshold `Q_0` is made by casting `Q`. -/
noncomputable def Qwidth (bout : ℕ) (δU : ℝ) : ℕ := 2 ^ rQ bout δU

/-- **`eq:direct-entry-gates`** (`10-direct-bridge.tex:53--56`; reader
`eq:bridge-exact-Q-gates`, `04-bridge.tex:98`).

The displayed pair, transcribed as the paper states it and nothing more:
`4 Q_0 θ ≤ δ` and `3λ + (7/5) ln 2 ≤ -2 ln y`.  It is a hypothesis, never a
conclusion; every deliverable below takes the halves it needs as explicit
binders, and this name exists so that the pair can be refuted at illegal
parameters. -/
def directEntryGates (bout : ℕ) (δU θ y : ℝ) : Prop :=
  4 * Q0 bout δU * θ ≤ deltaFixed ∧
    3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log y

lemma directEntryGates_iff (bout : ℕ) (δU θ y : ℝ) :
    directEntryGates bout δU θ y ↔
      (4 * Q0 bout δU * θ ≤ deltaFixed ∧
        3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log y) :=
  Iff.rfl

/-! ## Aux-lemma battery

General properties of the four transcriptions, each stated for arbitrary
parameters rather than for a pinned assignment. -/

/-- **Aux 1 (`λ` is not defined twice).**  `lambdaU` is literally the
expression the landed `DefectInduction` lemmas quantify over, so those lemmas
apply to it without any translation step. -/
lemma lambdaU_eq (δU : ℝ) : lambdaU δU = -Real.log (1 - δU) := rfl

/-- **Aux 2 (round trip, and positivity).**  `e^{-λ} = 1 - δ_U` and `λ > 0` on
the frozen range `0 < δ_U < 1` (`10-direct-bridge.tex:38`).  This is the
landed `DefectInduction.exp_neg_lambda`, consumed unchanged: it is what lets
the first input clause be *stated* with `1 - δ_U` and *consumed* at density
`e^{-λ}`. -/
lemma lambdaU_spec {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) :
    Real.exp (-(lambdaU δU)) = 1 - δU ∧ 0 < lambdaU δU :=
  exp_neg_lambda hδ0 hδ1

/-- **Aux 3 (monotonicity).**  A larger deletion tolerance costs a larger
exponent.  Recorded because the second gate is an *upper* bound on `λ`, so the
gate is a ceiling on `δ_U`; `lambdaU_le_of_deltaU_le` turns that reading into a
usable numeric criterion. -/
lemma lambdaU_mono {δU δU' : ℝ} (h : δU ≤ δU') (h1 : δU' < 1) :
    lambdaU δU ≤ lambdaU δU' := by
  have hpos : (0 : ℝ) < 1 - δU' := by linarith
  have hlog : Real.log (1 - δU') ≤ Real.log (1 - δU) :=
    Real.log_le_log hpos (by linarith)
  simp only [lambdaU]
  linarith

/-- **Aux 4 (`λ` dominates `δ_U`).**  `-ln(1 - δ_U) ≥ δ_U` for every
`δ_U < 1`.  The elementary direction of the exponential comparison; it is what
makes the second gate strictly stronger than the naive bound `δ_U ≤ 17/1000`
and is therefore recorded rather than assumed. -/
lemma deltaU_le_lambdaU {δU : ℝ} (hδ1 : δU < 1) : δU ≤ lambdaU δU := by
  have hpos : (0 : ℝ) < 1 - δU := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  simp only [lambdaU]
  linarith

/-- **Aux 5 (a checkable criterion for the second gate).**  `δ_U ≤ 1/60`
forces `λ ≤ 17/1000`, which is exactly the window the landed
`DefectInduction.entry_gate_of_lambda_small` accepts.  Proved from
`log t ≤ t - 1` at `t = (1 - δ_U)⁻¹`, i.e. `λ ≤ δ_U/(1 - δ_U) ≤ 1/59`. -/
lemma lambdaU_le_of_deltaU_le {δU : ℝ} (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 60) :
    lambdaU δU ≤ 17 / 1000 := by
  have hpos : (0 : ℝ) < 1 - δU := by linarith
  have hinvpos : (0 : ℝ) < (1 - δU)⁻¹ := by positivity
  have hlog : Real.log (1 - δU)⁻¹ ≤ (1 - δU)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hinvpos
  have hlogeq : Real.log (1 - δU)⁻¹ = lambdaU δU := by
    simp only [Real.log_inv, lambdaU]
  have hmul : (1 - δU) * (1 - δU)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
  have hbound : (1 - δU)⁻¹ - 1 ≤ 17 / 1000 := by
    nlinarith [hmul, hinvpos,
      mul_nonneg hinvpos.le (by linarith : (0 : ℝ) ≤ 1 / 60 - δU)]
  rw [← hlogeq]
  linarith

/-- **Aux 6 (the first branch of the maximum).**  `Q_0` dominates
`8 b_out/(δ δ_U)`, the branch that carries the requested output depth. -/
lemma Q0_first_le (bout : ℕ) (δU : ℝ) :
    8 * (bout : ℝ) / (deltaFixed * δU) ≤ Q0 bout δU :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- **Aux 7 (the second branch of the maximum).**  `Q_0 ≥ 8/δ`. -/
lemma Q0_second_le (bout : ℕ) (δU : ℝ) : (8 : ℝ) / deltaFixed ≤ Q0 bout δU :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- **Aux 8 / claim (`Q_0 ≥ 16`).**  The third branch, and the fact line 58
uses by name.  It holds unconditionally, for every `b_out` and every `δ_U`,
because it is a branch of the maximum rather than a derived estimate. -/
theorem Q0_ge_sixteen (bout : ℕ) (δU : ℝ) : (16 : ℝ) ≤ Q0 bout δU :=
  le_max_right _ _

/-- **Aux 9 (positivity).**  Immediate from `Q_0 ≥ 16`, and needed before any
division by `Q_0`. -/
lemma Q0_pos (bout : ℕ) (δU : ℝ) : 0 < Q0 bout δU :=
  lt_of_lt_of_le (by norm_num) (Q0_ge_sixteen bout δU)

/-- **Aux 10 (the maximum with `δ` evaluated).**  Substituting the fixed
`δ = 1/10` turns the displayed branches into `80 b_out/δ_U`, `80`, and `16`.
Recorded separately so that the evaluation step is visible and is never done
silently inside another proof. -/
lemma Q0_eq_max (bout : ℕ) {δU : ℝ} (hδ0 : 0 < δU) :
    Q0 bout δU = max (max (80 * (bout : ℝ) / δU) 80) 16 := by
  have hne : δU ≠ 0 := ne_of_gt hδ0
  have hA : 8 * (bout : ℝ) / (deltaFixed * δU) = 80 * (bout : ℝ) / δU := by
    rw [deltaFixed_eq]
    field_simp
    ring
  have hB : (8 : ℝ) / deltaFixed = 80 := by
    rw [deltaFixed_eq]; norm_num
  rw [Q0, hA, hB]

/-- **Aux 11 (the operative branch on the route).**  At the frozen legal
values `b_out ≥ 1` (line 41) and `0 < δ_U < 1` (line 38) the maximum is
*always* attained by its first branch: `Q_0 = 80 b_out/δ_U`.  So the constant
branches `8/δ` and `16` never bind on the route, and a witness sitting on them
would be degenerate. -/
lemma Q0_eq_route {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout) (hδ0 : 0 < δU)
    (hδ1 : δU < 1) : Q0 bout δU = 80 * (bout : ℝ) / δU := by
  have hb1 : (1 : ℝ) ≤ (bout : ℝ) := by exact_mod_cast hb
  have hge : (80 : ℝ) ≤ 80 * (bout : ℝ) / δU := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  rw [Q0_eq_max bout hδ0, max_eq_left hge, max_eq_left (by linarith)]

/-- **Aux 12 (monotone in the requested depth).**  A deeper requested output
`b_out` needs a wider interlace. -/
lemma Q0_mono_bout {bout bout' : ℕ} {δU : ℝ} (hδ0 : 0 < δU)
    (h : bout ≤ bout') : Q0 bout δU ≤ Q0 bout' δU := by
  have hb : (bout : ℝ) ≤ (bout' : ℝ) := by exact_mod_cast h
  have hden : (0 : ℝ) < deltaFixed * δU := by
    rw [deltaFixed_eq]; positivity
  have hfirst : 8 * (bout : ℝ) / (deltaFixed * δU)
      ≤ 8 * (bout' : ℝ) / (deltaFixed * δU) := by
    gcongr
  exact max_le_max (max_le_max hfirst le_rfl) le_rfl

/-- **Aux 13 (antitone in the deletion tolerance).**  A *smaller* deletion
tolerance `δ_U` — which the second gate pushes towards — needs a wider
interlace.  The two gates therefore pull in opposite directions, which is why
neither can be dropped. -/
lemma Q0_antitone_deltaU {bout : ℕ} {δU δU' : ℝ} (hδ0 : 0 < δU)
    (h : δU ≤ δU') : Q0 bout δU' ≤ Q0 bout δU := by
  have hden : (0 : ℝ) < deltaFixed * δU := by
    rw [deltaFixed_eq]; positivity
  have hfirst : 8 * (bout : ℝ) / (deltaFixed * δU')
      ≤ 8 * (bout : ℝ) / (deltaFixed * δU) := by
    have hb : (0 : ℝ) ≤ 8 * (bout : ℝ) := by positivity
    gcongr
    · rw [deltaFixed_eq]; positivity
  exact max_le_max (max_le_max hfirst le_rfl) le_rfl

/-- **Aux 14 (the exponent set is nonempty).**  Some power of two exceeds
`Q_0`, so the infimum defining `r_Q` is not the junk value `0`.  Archimedean
in `ℝ`; no property of `Q_0` beyond being a real number is used. -/
lemma exists_pow_ge_Q0 (bout : ℕ) (δU : ℝ) :
    ∃ r : ℕ, Q0 bout δU ≤ (2 : ℝ) ^ r := by
  obtain ⟨r, hr⟩ :=
    pow_unbounded_of_one_lt (Q0 bout δU) (by norm_num : (1 : ℝ) < 2)
  exact ⟨r, hr.le⟩

/-- **Aux 15 (`r_Q` is admissible).**  The defining upper property of the
canonical exponent, with no side condition. -/
lemma Q0_le_two_pow_rQ (bout : ℕ) (δU : ℝ) :
    Q0 bout δU ≤ (2 : ℝ) ^ rQ bout δU :=
  Nat.sInf_mem (exists_pow_ge_Q0 bout δU)

/-- **Aux 16 / claim (minimality of `r_Q`).**  Any admissible exponent is at
least `r_Q`.  This is the defining property of the landed encoding, again with
no side condition. -/
theorem rQ_min {bout : ℕ} {δU : ℝ} {r : ℕ} (hr : Q0 bout δU ≤ (2 : ℝ) ^ r) :
    rQ bout δU ≤ r :=
  Nat.sInf_le hr

/-- **Aux 17 (`r_Q ≥ 4`).**  Because `Q_0 ≥ 16 = 2^4`, the canonical exponent
is never degenerate: the selector of `lem:interlace-selector-protocol` always
costs at least four bits.  In particular `r_Q ≥ 1`, which
`two_pow_pred_lt_Q0` needs. -/
lemma four_le_rQ (bout : ℕ) (δU : ℝ) : 4 ≤ rQ bout δU := by
  by_contra hcon
  have h3 : rQ bout δU ≤ 3 := by omega
  have hpow : (2 : ℝ) ^ rQ bout δU ≤ (2 : ℝ) ^ (3 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) h3
  have hmem := Q0_le_two_pow_rQ bout δU
  have h16 := Q0_ge_sixteen bout δU
  norm_num at hpow
  linarith

/-- **Aux 18 (`Q` overshoots by less than a factor of two).**  The predecessor
exponent is inadmissible, so `2^{r_Q - 1} < Q_0` and hence `Q < 2 Q_0`.  This
is the substantive content of "*least* power of two": without it, any large
power of two would do. -/
lemma two_pow_pred_lt_Q0 (bout : ℕ) (δU : ℝ) :
    ((Qwidth bout δU : ℕ) : ℝ) < 2 * Q0 bout δU := by
  have h4 := four_le_rQ bout δU
  have hlt : rQ bout δU - 1 < rQ bout δU := by omega
  have hnot : rQ bout δU - 1 ∉ {r : ℕ | Q0 bout δU ≤ (2 : ℝ) ^ r} :=
    Nat.notMem_of_lt_sInf hlt
  have hstrict : (2 : ℝ) ^ (rQ bout δU - 1) < Q0 bout δU := by
    simpa only [Set.mem_setOf_eq, not_le] using hnot
  have hsplit : rQ bout δU = (rQ bout δU - 1) + 1 := by omega
  have hnat : Qwidth bout δU = 2 * 2 ^ (rQ bout δU - 1) := by
    rw [Qwidth]
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hQ : ((Qwidth bout δU : ℕ) : ℝ) = 2 * (2 : ℝ) ^ (rQ bout δU - 1) := by
    rw [hnat]
    push_cast
    ring
  rw [hQ]
  linarith

/-! ## The claim theorems

Each is a named-def claim about the pinned entry apparatus, in the frozen
spelling. -/

/-- **Claim (power of two)** — `10-direct-bridge.tex:51`; reader
`04-bridge.tex:94`.  `Q = 2^{r_Q}`, definitionally, so the selector protocol's
`r_Q`-bit cost is the exact base-two logarithm of the width. -/
theorem Qwidth_eq_two_pow (bout : ℕ) (δU : ℝ) :
    Qwidth bout δU = 2 ^ rQ bout δU := rfl

/-- **Claim (`Q_0 ≤ Q`)** — `10-direct-bridge.tex:51`; reader
`04-bridge.tex:94`.  The canonical width meets the threshold. -/
theorem Q0_le_Qwidth (bout : ℕ) (δU : ℝ) :
    Q0 bout δU ≤ ((Qwidth bout δU : ℕ) : ℝ) := by
  have h := Q0_le_two_pow_rQ bout δU
  rwa [Qwidth, Nat.cast_pow, Nat.cast_ofNat]

/-- **Claim (`Q` is the *least* such power of two)** —
`10-direct-bridge.tex:51`; reader `04-bridge.tex:94`.  Every power of two at
least `Q_0` is at least `Q`. -/
theorem Qwidth_least {bout : ℕ} {δU : ℝ} {r : ℕ}
    (hr : Q0 bout δU ≤ (2 : ℝ) ^ r) : Qwidth bout δU ≤ 2 ^ r :=
  Nat.pow_le_pow_right (by norm_num) (rQ_min hr)

/-- **Claim (the frozen legality implication)** —
`10-direct-bridge.tex:58--60`: "The first inequality and `Q_0 ≥ 16` imply
`4θ ≤ δ/Q_0 < 1`, so the invocation `eq:direct-three-copy` is legal."

Both halves are returned in the paper's own spelling.  Only the first gate is
taken as a binder; `Q_0 ≥ 16` is `Q0_ge_sixteen` and is not re-assumed. -/
theorem entryLegality (bout : ℕ) {δU θ : ℝ}
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) :
    4 * θ ≤ deltaFixed / Q0 bout δU ∧ deltaFixed / Q0 bout δU < 1 := by
  have h16 := Q0_ge_sixteen bout δU
  have hpos := Q0_pos bout δU
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith [hgate]
  · rw [div_lt_one hpos, deltaFixed_eq]
    linarith

/-- **The row request is legal.**  The consequence line 60 draws: `4θ ≤ 1`,
which is precisely the guard of the landed `eq:direct-three-copy`. -/
theorem entryGate_row_request_legal (bout : ℕ) {δU θ : ℝ}
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) : 4 * θ ≤ 1 := by
  obtain ⟨h1, h2⟩ := entryLegality bout hgate
  linarith

/-- **Aux 19 (the first gate's ceiling on `θ`).**  Consumes the landed
`DefectInduction.routeGate_forces_theta_small`: on the route itself every row
threshold satisfies `θ ≤ 1/640`.  Recorded because it is the quantitative
reason the row request is never near its boundary. -/
lemma entryGate_theta_le {bout : ℕ} {δU θ : ℝ} (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) : θ ≤ 1 / 640 :=
  routeGate_forces_theta_small (Q0_ge_sixteen bout δU) hθ0
    (by rw [deltaFixed_eq] at hgate; exact hgate)

/-- **Aux 20 (a checkable criterion for the second gate at the fixed `y`).**
At the route's globally fixed `y = 3/5` (`10-direct-bridge.tex:37`), the
second half of `eq:direct-entry-gates` holds whenever `δ_U ≤ 1/60`.  This
chains Aux 5 into the landed `DefectInduction.entry_gate_of_lambda_small`; no
new numeric fact about the gate is proved here. -/
theorem secondEntryGate_of_deltaU_small {δU : ℝ} (hδ0 : 0 < δU)
    (hδ : δU ≤ 1 / 60) :
    3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5) :=
  entry_gate_of_lambda_small (lambdaU_spec hδ0 (by linarith)).2
    (lambdaU_le_of_deltaU_le hδ0 hδ)

/-! ## Wiring to the landed base estimates

These two corollaries claim **no** reader item: they apply the frozen legality
sentence at lines 58--60 to results already landed in `BRIDGE-TWOCOPY-001` and
`BRIDGE-THREECOPY-001`, which are imported and consumed, never edited. -/

/-- **`eq:direct-three-copy` under the entry gate.**

The frozen composition of `10-direct-bridge.tex:58--60` with
`eq:direct-three-copy` (line 31): the first gate replaces the guard `4θ ≤ 1`
of the landed `ThreeCopyRowStep.directThreeCopy`, which is exactly what line
60 asserts it does.  The row threshold's own positivity `0 < θ` (line 39)
stays an explicit binder, since the gate alone does not supply it. -/
theorem directThreeCopy_of_entryGates {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    CW + 1 ≤ Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2)) :=
  directThreeCopy W CW hCW hθ0 (entryGate_row_request_legal bout hgate) hy0 hy1
    hTwo

/-- **Both base estimates under the entry gate.**

The same substitution applied to the landed
`ThreeCopyRowStep.bridgeBaseEstimates`: from `eq:direct-input` clause two
(`10-direct-bridge.tex:10`) and the first entry gate, both `eq:direct-two-copy`
and `eq:direct-three-copy` follow. -/
theorem bridgeBaseEstimates_of_entryGates {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) (CW bout : ℕ) {δU θ y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hInput : CW - 1 ≤ LambdaGE W 1 θ y) :
    CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2) ∧
      CW + 1 ≤
        Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2)) :=
  bridgeBaseEstimates W CW hCW hθ0 (entryGate_row_request_legal bout hgate) hy0
    hy1 hInput

/-! ## Non-vacuity and the statement poles -/

/-- **Non-vacuity (i): the `16` branch never binds on the route.**

At every legal `b_out ≥ 1` (line 41) and `0 < δ_U < 1` (line 38) the maximum
is strictly above its constant branch, so an inhabitant sitting on `Q_0 = 16`
would be degenerate and is excluded. -/
theorem Q0_gt_sixteen_of_route {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) : (16 : ℝ) < Q0 bout δU := by
  have hb1 : (1 : ℝ) ≤ (bout : ℝ) := by exact_mod_cast hb
  have hroute := Q0_eq_route hb hδ0 hδ1
  have hge : (80 : ℝ) ≤ 80 * (bout : ℝ) / δU := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  rw [hroute]
  linarith

/-- **Non-vacuity (ii): the gate pair fires at nondegenerate legal values.**

`b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `y = 3/5` — all strictly inside the
frozen ranges of lines 38--41 — satisfy **both** halves of
`eq:direct-entry-gates`, and the entry apparatus takes the interior values
`Q_0 = 4800`, `r_Q = 13`, `Q = 8192`.  The first gate is **tight**
(`4 Q_0 θ = δ` exactly), the maximum is on its first branch
(`Q_0 = 4800 > 80 > 16`), the canonical exponent is far from the degenerate
`r_Q = 0`, and the legality readout `4θ ≤ δ/Q_0 < 1` is exhibited. -/
theorem directEntryGates_fires :
    directEntryGates 1 (1 / 60) (1 / 192000) (3 / 5) ∧
      Q0 1 (1 / 60) = 4800 ∧ rQ 1 (1 / 60) = 13 ∧ Qwidth 1 (1 / 60) = 8192 ∧
      (16 : ℝ) < Q0 1 (1 / 60) ∧
      4 * (1 / 192000 : ℝ) ≤ deltaFixed / Q0 1 (1 / 60) ∧
      deltaFixed / Q0 1 (1 / 60) < 1 := by
  have hQ0 : Q0 1 (1 / 60) = 4800 := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [hQ0, deltaFixed_eq]; norm_num
  have hrQ : rQ 1 (1 / 60) = 13 := by
    refine le_antisymm (rQ_min (by rw [hQ0]; norm_num)) ?_
    by_contra hcon
    have h12 : rQ 1 (1 / 60) ≤ 12 := by omega
    have hmem := Q0_le_two_pow_rQ 1 (1 / 60)
    have hpow : (2 : ℝ) ^ rQ 1 (1 / 60) ≤ (2 : ℝ) ^ (12 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) h12
    rw [hQ0] at hmem
    norm_num at hpow
    linarith
  obtain ⟨hleg1, hleg2⟩ := entryLegality 1 hgate
  refine ⟨⟨hgate, secondEntryGate_of_deltaU_small (by norm_num) le_rfl⟩, hQ0,
    hrQ, ?_, ?_, hleg1, hleg2⟩
  · rw [Qwidth, hrQ]; norm_num
  · rw [hQ0]; norm_num

/-- **Non-vacuity (iii): the second gate genuinely constrains `δ_U`.**

The pair is **false** at `δ_U = δ = 1/10`, for every `b_out` and every `θ`:
the route's deletion tolerance is strictly smaller than its density margin,
and a transcription conflating the two would typecheck and prove nothing.
Consumes the landed `DefectInduction.entry_gate_lambda_window`. -/
theorem directEntryGates_refuted_at_deltaU_eq_delta (bout : ℕ) (θ : ℝ) :
    ¬ directEntryGates bout (1 / 10) θ (3 / 5) := by
  rintro ⟨-, hsecond⟩
  exact entry_gate_lambda_window.2.2 hsecond

/-- **Non-vacuity (iv): the first gate genuinely constrains `θ`.**

At the legal `b_out = 1`, `δ_U = 1/60` of the firing witness, the row
threshold `θ = 1/1000` — itself well inside line 39's `0 < θ ≤ 1` — already
violates `4 Q_0 θ ≤ δ`.  So the first gate is not implied by the frozen range
of `θ`. -/
theorem directEntryGates_refuted_at_large_theta :
    ¬ directEntryGates 1 (1 / 60) (1 / 1000) (3 / 5) := by
  rintro ⟨hfirst, -⟩
  rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num),
    deltaFixed_eq] at hfirst
  norm_num at hfirst

/-- **Non-vacuity (v): the wiring fires at pinned constants.**

`directThreeCopy_of_entryGates` at the witness parameters of
`directEntryGates_fires`, with `C_W = 3` (the boundary of line 40) and with
`X`, `Y`, `W` left universally quantified — deliberately, since the semantic
premise `Λ_W(2, 2θ, y²) ≥ C_W` has no exhibited inhabitant in Lean and cannot
have one until Stages 1--4 land.  The gate binder is discharged by a genuine
numeric computation at `Q_0 = 4800`, not by an assumption. -/
theorem directThreeCopy_of_entryGates_fires {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool)
    (hTwo : (3 : ℕ) ≤ LambdaGE W 2 (2 * (1 / 192000)) ((3 / 5 : ℝ) ^ 2)) :
    (3 : ℕ) + 1 ≤ Dfamily (interlaceFun W 3)
      (bracketGE X Y 3 (4 * (1 / 192000)) ((3 / 5 : ℝ) ^ 2)) := by
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  exact directThreeCopy_of_entryGates W 3 1 (le_refl 3) (by norm_num) hgate
    (by norm_num) (by norm_num) hTwo

end EthInapproximability.ParameterizedNP.EntryGates
