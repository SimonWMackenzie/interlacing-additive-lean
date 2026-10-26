import EthInapproximability.ParameterizedNP.DirectOutputLower

/-!
# Parameterized NP route: the `eq:direct-output` equality and `thm:direct-robustification`

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-OUTPUT-003`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1j` tranche as the remainder that `BRIDGE-001` records as still Lean
pending after the three earlier splits:

* the **equality** of `eq:direct-output`, `comp R⁺ = C_W + r_Q`, assembling
  `BRIDGE-OUTPUT-001`'s upper direction with `BRIDGE-OUTPUT-002`'s lower
  direction under one reconciled hypothesis list, with the frozen
  `comp W = C_W` of line 40 added as a **new explicit binder**;
* `thm:direct-robustification` itself as a single closed conditional statement;
* `eq:bridge-carriers`, stated as a separate cardinality declaration.

`lem:copy-restriction` stays out of scope and remains with `BRIDGE-001`.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`, `thm:direct-robustification` (label line
  35), taken as one closed statement:
  * lines 36--37, the globally fixed `δ = 1/10` and `y = 1/2 + δ = 3/5`,
    consumed from `BRIDGE-ENTRY-001` as `EntryGates.deltaFixed` and the literal
    `3/5`;
  * line 38, `0 < δ_U < 1` and `0 < θ ≤ 1`;
  * lines 39--41, "let `W` satisfy `comp W = C_W ≥ 3` and `eq:direct-input`" —
    the first conjunct is the binder `hCWeq` this module adds, the second is
    `hCW`, and `eq:direct-input` (label line 11) stays the pair of explicit
    named binders `hNear`, `hInput` that `BRIDGE-OUTPUT-002` carries;
  * line 41, "Fix an integer `b_out ≥ 1`";
  * lines 43--51, `λ = -ln(1 - δ_U)`, `Q_0 = max{8 b_out/(δ δ_U), 8/δ, 16}`,
    and `Q = 2^{r_Q}` the least power of two at least `Q_0` — the banked
    `EntryGates.lambdaU`, `.Q0`, `.rQ`, `.Qwidth`, consumed and never redefined;
  * `eq:direct-entry-gates` (label line 56, display lines 52--57), taken as the
    single frozen named pair `EntryGates.directEntryGates` at `y = 3/5`;
  * line 63, `R⁺ = transpose(Int_Q(W))`, the vendored `EthBridge.Rnext`;
  * `eq:direct-output` (label line 71, display lines 66--72), **both** halves;
  * lines 73--74, "The selector protocol of `lem:interlace-selector-protocol`
    adds exactly `r_Q` bits to a protocol for `W`, because `Q = 2^{r_Q}`" —
    the banked `DirectOutput.canonicalSelectorBits` and
    `.canonicalSelectorProtocol`, consumed.
* `sections/03-preliminaries.tex`, line 11, "We write `Rows(M) = X` and
  `Cols(M) = Y`" — the two carrier readouts transcribed here as `rowsCard`
  and `colsCard`.
* `sections/03-preliminaries.tex`, `def:interlace` (label line 112, display
  lines 113--118): the `p`-fold classical interlace has "row set `[p] × X`,
  column set `Y^p`".  With line 63's transposition this is the frozen reason
  for the carrier equations.
* `sections/05-public-records.tex`, lines 830--833, the exact output carrier
  equations `Rows(R⁺) = Cols(W)^Q` and `Cols(R⁺) = [Q] × Rows(W)`.  The
  Stage-4 substitution of lines 834--836 (`m_next = (q m_N)^Q`,
  `n_next = Q n_N^q`) is **not** claimed here: it belongs to the one-level
  assembly and needs the scale-alignment width `q`, which this generic bridge
  never sees.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex`.  The file was
opened and each cited item checked, first-hand, to state the same fact.  **No
reader item is assigned twice**, here or against any earlier row.

* `eq:bridge-output` (label line 110, display lines 106--110), **first
  equation**, `comp R^+ = C_W + r_Q` — counterpart of `directOutputEquality`,
  and of that declaration alone.  `BRIDGE-001`, `BRIDGE-OUTPUT-001` and
  `BRIDGE-OUTPUT-002` all recorded this first equation as deliberately
  unclaimed; it is claimed here and nowhere else.  The **second** equation of
  the same display stays with `BRIDGE-OUTPUT-002`'s `directOutputLower` and is
  *consumed*, never restated.
* `eq:bridge-carriers` (label line 117, display lines 113--118), "Its carriers
  are exactly `|Rows(R^+)| = n^Q`, `|Cols(R^+)| = Q m`" — counterpart of
  `bridgeCarriers`, and of that declaration alone.  `BRIDGE-OUTPUT-001` and
  `BRIDGE-OUTPUT-002` both recorded it as deliberately unclaimed.

Deliberately given **no** reader counterpart, with reasons:

* `directRobustification`.  Every component of its closed statement already has
  an assigned reader item: its hypotheses are the four `BRIDGE-ENTRY-001`
  items (the fixed-constant display at lines 22--26, `eq:bridge-Q0`, the
  canonical-`Q` sentence at line 94, `eq:bridge-exact-Q-gates`), its first
  conclusion is the first equation of `eq:bridge-output` assigned just above,
  its second is the second equation of `eq:bridge-output` held by
  `BRIDGE-OUTPUT-002`, and its selector conclusion is the protocol sentence at
  lines 112--113 held by `BRIDGE-OUTPUT-001`.  Assigning the reader theorem
  `thm:near-to-robust` as a whole would therefore reassign items already
  assigned, so nothing fresh is claimed for the assembly itself.
* `rowsCard`, `colsCard` and the carrier aux battery.  The reader's only
  carrier statement is `eq:bridge-carriers`, assigned above to a single
  declaration; the readouts are transcriptions of
  `03-preliminaries.tex` line 11, whose reader counterpart (`04-bridge.tex`
  preliminaries) is a notation sentence and not a statement.
* the poles and witnesses of Part 4, which are interface properties, not
  transcriptions of reader statements.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **new (elementary)** throughout — every deliverable is an
  assembly of banked, already kernel-checked route facades by `omega`,
  `le_antisymm`, or a `Fintype.card` computation.  Nothing banked is edited,
  widened, or re-proved.
* Consumed, never edited or re-proved:
  * `DirectOutput.canonicalSelectorUpper_transpose`, `.canonicalSelectorBits`,
    `.canonicalSelectorProtocol` (`BRIDGE-OUTPUT-001`), the upper direction and
    the selector sentence of lines 73--74;
  * `DirectOutputLower.directOutputComplexityLower`, `.directOutputLower`,
    `.xOut`, `.directOutputLower_conclusion_nontrivial` (`BRIDGE-OUTPUT-002`),
    the lower direction and the entry readouts;
  * `EntryGates.Q0`, `.rQ`, `.Qwidth`, `.lambdaU`, `.deltaFixed`,
    `.directEntryGates`, `.four_le_rQ`, `.Q0_eq_route`,
    `.secondEntryGate_of_deltaU_small`, `.directEntryGates_fires`
    (`BRIDGE-ENTRY-001`);
  * the vendored `EthBridge.Rnext` for the `R⁺` orientation of line 63 and
    `NPCC.D_le_one_of_unit_row` for one refutation witness.
* Imports: `DirectOutputLower.lean` only, hence `DirectOutput.lean`,
  `EntryGates.lean`, `PilotStage3.lean`, `ThreeCopyRowStep.lean`,
  `TwoCopyLadder.lean`, `DefectInduction.lean`, `InheritedContracts.lean`,
  `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom is not in scope,
  and there is no contact with `EXPANDER-001` (which by design has no Lean
  declaration and would have to stay an explicit named hypothesis).
* External adapters: none.  Nothing here is axiomatized.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why these landed

Two genuinely open encoding choices arise in this tranche, and each was written
out twice and run against the aux battery.

### Choice 1 — how to state the equality of `eq:direct-output`

**Candidate A (landed).**  One equation `comp R⁺ = C_W + r_Q` under a binder
list that reconciles the two banked directions at the same parameters **and
adds the frozen `comp W = C_W` of line 40** as a new explicit binder.  Aux
lemmas: (a) both banked directions apply verbatim at that list, (b) the
equality specialises to each of them, (c) the delivered value is `≥ 7`, and
(d) the round trip back to line 71.  All four proved.

**Candidate B (rejected — disqualified by a failed aux lemma).**  Keep the two
directions side by side, `comp R⁺ ≤ comp W + r_Q ∧ C_W + r_Q ≤ comp R⁺`, and
never mention line 40.  Aux lemma (d), the round trip, is **false**:
`directOutput_needs_exact_complexity` proves in Lean that the two bounds do not
determine `comp R⁺` — at `C_W = 0`, `comp W = 1`, `r_Q = 0` both hold with
`comp R⁺ = 1 ≠ 0 = C_W + r_Q`.  So Candidate B is strictly weaker than
`eq:direct-output`, and the line-40 binder is exactly what closes the gap.  It
is also not the frozen text, which writes an equality.

Ranking (aux lemmas proved, faithfulness, length): A = 4/4, literal equality,
one `omega`; B = 3/4, strictly weaker, and silent about line 40.  A landed.

### Choice 2 — how to state `eq:bridge-carriers`

**Candidate A (landed).**  Cardinality readouts `rowsCard`, `colsCard`
transcribing `03-preliminaries.tex` line 11, and the pair of exact equations
`|Rows(R⁺)| = |Cols(W)|^Q`, `|Cols(R⁺)| = Q · |Rows(W)|`.  Aux lemmas: (a) the
readouts round-trip to `Fintype.card`, (b) transposition exchanges them, (c)
the interlace carriers at an **arbitrary** width `k`, (d) nonemptiness is
preserved, (e) monotonicity in the width.  All five proved.

**Candidate B (rejected — disqualified by a failed aux lemma).**  The integer
side-bound form of `05-public-records.tex` lines 844--846,
`m_next ≤ 2^{z⁺}`, `n_next ≤ 2^{z⁺}`.  The round-trip aux lemma is **false**:
`bridgeCarriers_candidateB_refuted` proves in Lean that a side bound does not
pin a carrier — at `n = 5`, `Q = 4`, `z = 10` the value `0` satisfies the same
bound as `5^4 = 625`.  A carrier-degenerate output would therefore pass
Candidate B, and the exact equations of lines 830--833 would be lost.  The side
bound is a *consequence* of the carriers, not a statement of them.

Ranking: A = 5/5, exact equations, literal; B = 4/5, satisfied by a degenerate
carrier.  A landed.

## Faithfulness notes (mechanical rules M1--M10)

* **No structure and no premise bundle** is introduced.  Every deliverable
  takes its hypotheses as **explicit binders**, and no conclusion of
  `eq:direct-output` sits in constructor data.  The one bundled hypothesis,
  `EntryGates.directEntryGates`, is the paper's own display
  `eq:direct-entry-gates` and was banked in `BRIDGE-ENTRY-001`; it is not a new
  bundle, `directEntryGates_iff` is `Iff.rfl`, and
  `directOutputEquality` still takes its two halves as separate binders exactly
  as the banked lower direction does.
* **The two new definitions are carrier readouts only.**  `rowsCard` and
  `colsCard` are `Fintype.card` of the two index types and restate no derived
  telescope.
* **Literal ceilings.**  None is introduced; `A_a` is neither redefined nor
  mentioned.  The carrier equations keep the frozen `n^Q` and `Q m` in that
  exact orientation — `bridgeCarriers_fires_nondegenerate` separates them from
  `Q^n`, `m^Q`, `Q^m`, `Q n` and `m n`.
* **Selector costs preserved.**  Line 74's *exactly* `r_Q` is carried into the
  closed statement as the banked `Nat.clog 2 Q = r_Q`, not as an inequality,
  and the protocol form keeps `U` an explicit binder as the reader writes it.
* **Both interlace widths.**  Only the outer width `Q` occurs.  The
  scale-alignment width `q` does not appear and is not conflated with it, and
  the Stage-4 carrier substitution `(q m_N)^Q`, `Q n_N^q` of
  `05-public-records.tex` lines 834--836 is deliberately **not** claimed.
* **Binder order** follows the frozen sentence of lines 38--57: `δ_U`, then
  `θ` with its full frozen range `0 < θ ≤ 1`, then the carriers and
  `comp W = C_W ≥ 3`, then `eq:direct-input`, then `b_out ≥ 1`, then
  `eq:direct-entry-gates`.
* **Finite carriers and nonemptiness.**  `1 ≤ |X|` and `1 ≤ |Y|` are explicit
  binders, as the reader's line 83 ("Let `W` have nonempty carriers") and
  `10-direct-bridge.tex` line 102 require, and
  `one_le_rowsCard_Rnext` / `one_le_colsCard_Rnext` carry that nonemptiness
  through to the output carriers.
* **No over-strengthening.**  `θ ≤ 1` is line 39's own range and is carried
  because the frozen theorem states it; `theta_le_one_of_entryGate` records
  that it is in fact *implied* by the first entry gate, so including it neither
  strengthens the hypothesis list beyond the paper nor weakens the theorem
  relative to what the gates already give.

## Statement poles

* **Trivial-witness pole.**  There is **no existential deliverable** in this
  module: every claim is an equation between named readouts, a bound on a named
  readout, or a named-def claim about a pinned construction.  The pipeline's
  one-line trivial-witness check therefore has no existential to run against,
  and the substitute check is Choice 1's Candidate-B refutation, which shows
  precisely that the weakest form a trivial reading would deliver is *not* the
  frozen equality.
* **Vacuous-conclusion pole.**  `directRobustification_conclusion_nontrivial`
  records `comp R⁺ = C_W + r_Q ≥ 7` at every legal parameter, from the frozen
  `C_W ≥ 3` (line 40) and the banked `r_Q ≥ 4`.  An equality delivering `0`
  would be free; this one is not.
* **Vacuous-hypothesis pole.**  The new binder `comp W = C_W` is not free:
  `exactComplexity_refuted_at_unit_row` shows it **fails** at `C_W ≥ 3` for the
  one-row matrix, whose complexity is at most one bit
  (`NPCC.D_le_one_of_unit_row`).  So line 40 genuinely restricts `W`, and a
  transcription that dropped it would be strictly weaker — indeed strictly too
  weak to give the equality at all, by Choice 1's refutation.

## GAP-EXPOSED

1. `eq:direct-input` still has **no exhibited inhabitant** in Lean and can have
   none until Stages 1--4 land, so `hNear`, `hInput` and `hCWeq` remain
   hypotheses in every witness below: the witnesses discharge every *numeric*
   binder by computation and leave `X`, `Y`, `W` universally quantified.
   Nothing here asserts that the bridge's input exists, and **no route
   completion is claimed**.
2. `lem:copy-restriction` (`10-direct-bridge.tex` line 132) is still not
   landed; it is consumed inside the vendored term that `BRIDGE-OUTPUT-002`
   uses and is untouched here.
3. The budget collection of `sec:one-level-completion` (lines 500--563), the
   Stage-4 carrier substitution of `05-public-records.tex` lines 834--836, and
   `sec:one-level-assembly` are untouched.
-/

namespace EthInapproximability.ParameterizedNP.BridgeOutputEquality

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput
open EthInapproximability.ParameterizedNP.DirectOutputLower

/-! ## Part 1: the carrier readouts and `eq:bridge-carriers`

`03-preliminaries.tex:11` writes `Rows(M) = X` and `Cols(M) = Y`; the carrier
equations compare their **cardinalities**, so the readouts land in `ℕ`. -/

/-- **`|Rows(M)|`** — `03-preliminaries.tex:11`.

The row-carrier cardinality of a Boolean matrix, i.e. the size of the index
type Alice receives.  The matrix argument is used for elaboration only, which
is why it is written `_M`: the value depends on nothing else. -/
def rowsCard {A B : Type*} [Fintype A] [Fintype B] (_M : A → B → Bool) : ℕ :=
  Fintype.card A

/-- **`|Cols(M)|`** — `03-preliminaries.tex:11`.  The column-carrier
cardinality, i.e. the size of the index type Bob receives. -/
def colsCard {A B : Type*} [Fintype A] [Fintype B] (_M : A → B → Bool) : ℕ :=
  Fintype.card B

/-! ### Aux-lemma battery for the carrier readouts

Five general properties, each stated at an **arbitrary** matrix and an
arbitrary interlace width rather than at the route's pinned values. -/

/-- **Aux 1a (round trip).**  `rowsCard` is `Fintype.card` of the row index
type and nothing else. -/
@[simp] lemma rowsCard_eq {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) : rowsCard M = Fintype.card A := rfl

/-- **Aux 1b (round trip).**  `colsCard` is `Fintype.card` of the column index
type and nothing else. -/
@[simp] lemma colsCard_eq {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) : colsCard M = Fintype.card B := rfl

/-- **Aux 2 (transposition exchanges the carriers).**  This is the frozen
reason `Cols(R⁺) = [Q] × Rows(W)` reads off `def:interlace`'s *row* set: line
63 transposes. -/
lemma rowsCard_transpose {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) : rowsCard (fun (b : B) (a : A) => M a b) = colsCard M :=
  rfl

/-- **Aux 2' (transposition exchanges the carriers, the other way).** -/
lemma colsCard_transpose {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) : colsCard (fun (b : B) (a : A) => M a b) = rowsCard M :=
  rfl

/-- **Aux 3a (`def:interlace` row set, at an arbitrary width).**
`Rows(Int_k(M)) = [k] × Rows(M)` (`03-preliminaries.tex:114`). -/
lemma rowsCard_interlace {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (k : ℕ) :
    rowsCard (interlaceFun M k) = k * rowsCard M := by
  simp [rowsCard, Fintype.card_prod]

/-- **Aux 3b (`def:interlace` column set, at an arbitrary width).**
`Cols(Int_k(M)) = Cols(M)^k` (`03-preliminaries.tex:114--115`). -/
lemma colsCard_interlace {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (k : ℕ) :
    colsCard (interlaceFun M k) = colsCard M ^ k := by
  simp [colsCard]

/-- **Aux 4a (nonemptiness is preserved on the row side).**  A nonempty column
carrier for `W` gives a nonempty row carrier for `R⁺`, at every width including
`Q = 0` (where the empty product is the one-point carrier). -/
lemma one_le_rowsCard_Rnext {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (Q : ℕ) (hY : 1 ≤ colsCard W) :
    1 ≤ rowsCard (EthBridge.Rnext W Q) := by
  simp only [rowsCard, Fintype.card_fun, Fintype.card_fin]
  simpa using Nat.one_le_pow Q (Fintype.card Y) (by simpa [colsCard] using hY)

/-- **Aux 4b (nonemptiness is preserved on the column side).**  A nonempty row
carrier for `W` and at least one copy give a nonempty column carrier for `R⁺`.
The copy count is a genuine hypothesis here: at `Q = 0` the column carrier is
empty, which is why the bridge's canonical width satisfies `Q ≥ 16`. -/
lemma one_le_colsCard_Rnext {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {Q : ℕ} (hQ : 1 ≤ Q) (hX : 1 ≤ rowsCard W) :
    1 ≤ colsCard (EthBridge.Rnext W Q) := by
  simp only [colsCard, Fintype.card_prod, Fintype.card_fin]
  simpa using Nat.mul_le_mul hQ (by simpa [rowsCard] using hX)

/-- **Aux 5 (monotone in the interlace width).**  A wider outer interlace has a
larger column carrier.  Recorded because the route compares two canonical
widths, `Q = 8192` and `Q = 16384`, and the comparison is this monotonicity
rather than a coincidence of the numerals. -/
lemma colsCard_Rnext_mono {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {Q Q' : ℕ} (h : Q ≤ Q') :
    colsCard (EthBridge.Rnext W Q) ≤ colsCard (EthBridge.Rnext W Q') := by
  simp only [colsCard, Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ h

/-! ### The carrier claim -/

/-- **`eq:bridge-carriers`** (reader `04-bridge.tex:113--118`, "Its carriers
are exactly `|Rows(R^+)| = n^Q`, `|Cols(R^+)| = Q m`"; autoformalization
`05-public-records.tex:830--833`, `Rows(R⁺) = Cols(W)^Q` and
`Cols(R⁺) = [Q] × Rows(W)`, over `def:interlace` and the transposition of
`10-direct-bridge.tex:63`).

Stated as a **separate cardinality declaration**, at an arbitrary width `Q`:
the carriers of `R⁺` are a property of the interlace and the transpose alone,
and depend on none of the bridge's gates, thresholds or complexity
hypotheses.  With `m = |Rows(W)|` and `n = |Cols(W)|` this is exactly
`|Rows(R⁺)| = n^Q` and `|Cols(R⁺)| = Q m`. -/
theorem bridgeCarriers {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (Q : ℕ) :
    rowsCard (EthBridge.Rnext W Q) = colsCard W ^ Q ∧
      colsCard (EthBridge.Rnext W Q) = Q * rowsCard W := by
  constructor
  · simp [rowsCard, colsCard, Fintype.card_fin]
  · simp [rowsCard, colsCard, Fintype.card_prod, Fintype.card_fin]

/-- **The carriers at the canonical width.**  `eq:bridge-carriers` specialised
to the bridge's own `Q = Qwidth b_out δ_U` of `BRIDGE-ENTRY-001`.  Claims no
further reader item: it is `bridgeCarriers` at a pinned width. -/
theorem bridgeCarriers_canonical {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (bout : ℕ) (δU : ℝ) :
    rowsCard (EthBridge.Rnext W (Qwidth bout δU)) = colsCard W ^ Qwidth bout δU ∧
      colsCard (EthBridge.Rnext W (Qwidth bout δU))
        = Qwidth bout δU * rowsCard W :=
  bridgeCarriers W (Qwidth bout δU)

/-! ## Part 2: the equality of `eq:direct-output`

`10-direct-bridge.tex:67`, `comp R⁺ = C_W + r_Q`.  The two directions are
banked; what is new is the reconciled hypothesis list and the frozen
`comp W = C_W` of line 40, without which the two directions do not meet (see
`directOutput_needs_exact_complexity`). -/

/-- **The equality of `eq:direct-output`** (`10-direct-bridge.tex:67`; reader
`eq:bridge-output`, **first equation**, `04-bridge.tex:107`):
`comp R⁺ = C_W + r_Q`.

The hypothesis list is exactly `BRIDGE-OUTPUT-002`'s, at the same parameters,
plus the new explicit binder `hCWeq : comp W = C_W` of line 40 — placed
immediately before `hCW : 3 ≤ C_W` so that the two read as the frozen sentence
"`comp W = C_W ≥ 3`".  `BRIDGE-OUTPUT-001`'s upper direction needs no
hypotheses of its own, so the reconciliation adds nothing else.

The proof is `le_antisymm` in `ℕ`, discharged by `omega`: the upper bound gives
`comp R⁺ ≤ comp W + r_Q = C_W + r_Q` after rewriting along `hCWeq`, and the
lower bound is the banked `directOutputComplexityLower`. -/
theorem directOutputEquality {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU := by
  have hupper := canonicalSelectorUpper_transpose W bout δU
  rw [hCWeq] at hupper
  have hlower := directOutputComplexityLower W CW bout hb hδ0 hδ1 hθ0 hgate
    hmargin hX hY hCW hNear hInput
  omega

/-- **`eq:direct-output` as one statement** (`10-direct-bridge.tex:66--72`):
the exact complexity **and** the output robustness at the same parameters.

The second conjunct is the banked `BRIDGE-OUTPUT-002` bound, *consumed* and not
restated; the first is `directOutputEquality`.  This is the display the
`interfacebox` at lines 492--498 hands to the next recursive level. -/
theorem directOutput {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU ∧
      CW + rQ bout δU
        ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
            (3 / 5) :=
  ⟨directOutputEquality W CW bout hb hδ0 hδ1 hθ0 hgate hmargin hX hY hCWeq hCW
      hNear hInput,
    directOutputLower W CW bout hb hδ0 hδ1 hθ0 hgate hmargin hX hY hCW hNear
      hInput⟩

/-! ## Part 3: `thm:direct-robustification` as one closed statement

`10-direct-bridge.tex:34--75`.  The entry apparatus `λ`, `Q_0`, `r_Q`, `Q` is
the banked `BRIDGE-ENTRY-001` transcription; the gate pair is the banked
`directEntryGates` at the globally fixed `y = 3/5`. -/

/-- **The frozen range `θ ≤ 1` of line 39 is implied by the first entry gate.**

`entryGate_theta_le` gives `θ ≤ δ/(4 Q_0) ≤ 1/640` from `4 Q_0 θ ≤ δ` and
`Q_0 ≥ 16`.  Recorded so that carrying line 39's `0 < θ ≤ 1` as an explicit
binder in the closed statement below is **not** an over-strengthening: the
theorem's own gates already deliver it. -/
lemma theta_le_one_of_entryGate {bout : ℕ} {δU θ : ℝ} (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) : θ ≤ 1 := by
  have h := entryGate_theta_le hθ0 hgate
  linarith

/-- **`thm:direct-robustification`** (`10-direct-bridge.tex`, label line 35),
as a **single closed conditional statement**.

Hypotheses, in the frozen order of lines 38--57 (the constants `δ = 1/10` and
`y = 3/5` of lines 36--37 are substituted, not quantified):

* `0 < δ_U < 1` and `0 < θ ≤ 1` (lines 38--39);
* nonempty carriers (reader line 83, `10-direct-bridge.tex:102`);
* `comp W = C_W ≥ 3` (line 40) and `eq:direct-input` (label line 11), the
  latter as the two explicit named binders `hNear`, `hInput`;
* an integer `b_out ≥ 1` (line 41);
* `eq:direct-entry-gates` (label line 56) as the banked frozen pair at
  `y = 3/5`.

The definitions of lines 43--51 are the banked `lambdaU`, `Q0`, `rQ`, `Qwidth`
and appear in the conclusion by name, so this is a named-def claim about the
pinned construction rather than an existential over widths.

Conclusions: `eq:direct-output` (both halves, lines 66--72) together with the
selector sentence of lines 73--74 in both of its frozen readings — *exactly*
`r_Q` bits (`Nat.clog 2 Q = r_Q`, not an inequality) and the protocol form the
reader states at lines 112--113.

Nothing is claimed about the existence of an input satisfying the hypotheses;
see GAP-EXPOSED item 1. -/
theorem directRobustification {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = CW) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    (hb : 1 ≤ bout)
    (hgates : directEntryGates bout δU θ (3 / 5)) :
    D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU ∧
      CW + rQ bout δU
        ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
            (3 / 5) ∧
      Nat.clog 2 (Qwidth bout δU) = rQ bout δU ∧
      (∀ U : ℕ, D W ≤ U →
        D (EthBridge.Rnext W (Qwidth bout δU)) ≤ U + rQ bout δU) := by
  obtain ⟨hgate, hmargin⟩ := hgates
  have hθrange : 0 < θ ∧ θ ≤ 1 := ⟨hθ0, hθ1⟩
  obtain ⟨heq, hrob⟩ :=
    directOutput W CW bout hb hδ0 hδ1 hθrange.1 hgate hmargin hX hY hCWeq hCW
      hNear hInput
  exact ⟨heq, hrob, canonicalSelectorBits bout δU,
    fun U hU => canonicalSelectorProtocol W bout δU U hU⟩

/-! ## Part 4: non-vacuity and the statement poles

LANE-GATE 3 and LANE-GATE 4b/4c.  Each item excludes one degeneracy that a
green build cannot see. -/

/-- **Non-vacuity (i): Candidate B of Choice 1 is refuted in Lean, so the
line-40 binder is load-bearing.**

The two banked directions alone read, in `ℕ`, as `n ≤ d + r` (the selector
upper bound, with `d = comp W`) and `c + r ≤ n` (the lower bound, with
`c = C_W`).  They do **not** determine `n`: at `c = 0`, `d = 1`, `r = 0`,
`n = 1` both hold while `n ≠ c + r`.  The frozen `comp W = C_W` of line 40 is
exactly what collapses `d` onto `c` and closes the two bounds into the
equality, so a transcription that kept the directions side by side would be
strictly weaker than `eq:direct-output`. -/
theorem directOutput_needs_exact_complexity :
    ¬ ∀ c d r n : ℕ, n ≤ d + r → c + r ≤ n → n = c + r := by
  intro h
  have hbad := h 0 1 0 1 (by norm_num) (by norm_num)
  omega

/-- **Non-vacuity (ii): the new binder is not free.**

`comp W = C_W` with `C_W ≥ 3` **fails** for the one-row matrix, whose
complexity is at most one bit (`NPCC.D_le_one_of_unit_row`).  So line 40
genuinely restricts `W` rather than holding for every matrix, and the frozen
range of the other hypotheses does not imply it. -/
theorem exactComplexity_refuted_at_unit_row {CW : ℕ} (hCW : 3 ≤ CW) :
    D (fun (_ : Unit) (y : Bool) => y) ≠ CW := by
  have h : D (fun (_ : Unit) (y : Bool) => y) ≤ 1 :=
    NPCC.D_le_one_of_unit_row (fun y : Bool => y)
  omega

/-- **Non-vacuity (iii): Candidate B of Choice 2 is refuted in Lean.**

An integer side bound `≤ 2^z` does not pin a carrier: at `n = 5`, `Q = 4`,
`z = 10` the degenerate value `0` satisfies the same bound as `n^Q = 625`.  So
the side-bound form of `05-public-records.tex:844--846` cannot stand in for the
exact equations of lines 830--833, and a carrier-degenerate output would pass
it. -/
theorem bridgeCarriers_candidateB_refuted :
    ¬ ∀ r n Q z : ℕ, n ^ Q ≤ 2 ^ z → r ≤ 2 ^ z → r = n ^ Q := by
  intro h
  have hbad := h 0 5 4 10 (by norm_num) (by norm_num)
  omega

/-- **Non-vacuity (iv): the carrier equations fire at a nondegenerate
inhabitant, and pin the orientation.**

At `m = |Rows(W)| = 3`, `n = |Cols(W)| = 5`, `Q = 4` — all distinct, all at
least two — the carriers read `|Rows(R⁺)| = 5^4 = 625` and
`|Cols(R⁺)| = 4 · 3 = 12`.  The last five conjuncts separate this from every
neighbouring misreading: `Q^n = 1024`, `m^Q = 81`, `Q^m = 64`, `Q n = 20` and
`m n = 15`.  A degenerate witness with `m = n = Q = 1` would satisfy all of
them at once and pin nothing. -/
theorem bridgeCarriers_fires_nondegenerate :
    rowsCard (EthBridge.Rnext (fun (_ : Fin 3) (_ : Fin 5) => true) 4) = 625 ∧
      colsCard (EthBridge.Rnext (fun (_ : Fin 3) (_ : Fin 5) => true) 4) = 12 ∧
      (625 : ℕ) ≠ 4 ^ 5 ∧ (625 : ℕ) ≠ 3 ^ 4 ∧ (625 : ℕ) ≠ 4 ^ 3 ∧
      (12 : ℕ) ≠ 4 * 5 ∧ (12 : ℕ) ≠ 3 * 5 := by
  obtain ⟨hrow, hcol⟩ :=
    bridgeCarriers (fun (_ : Fin 3) (_ : Fin 5) => true) 4
  refine ⟨?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩
  · rw [hrow]; simp [colsCard]
  · rw [hcol]; simp [rowsCard]

/-- **Non-vacuity (v): the nonemptiness services fire at that inhabitant.**

Both output carriers are nonempty there, through `one_le_rowsCard_Rnext` and
`one_le_colsCard_Rnext`, so the carrier equations are not being read on an
empty matrix. -/
theorem bridgeCarriers_nonempty_fires :
    1 ≤ rowsCard (EthBridge.Rnext (fun (_ : Fin 3) (_ : Fin 5) => true) 4) ∧
      1 ≤ colsCard (EthBridge.Rnext (fun (_ : Fin 3) (_ : Fin 5) => true) 4) :=
  ⟨one_le_rowsCard_Rnext _ 4 (by simp [colsCard]),
    one_le_colsCard_Rnext _ (by norm_num) (by simp [rowsCard])⟩

/-- **Non-vacuity (vi): the delivered equality is not trivial.**

`comp R⁺ = C_W + r_Q ≥ 7` at every legal parameter, from the frozen `C_W ≥ 3`
(line 40) and the banked `EntryGates.four_le_rQ`, consumed through
`BRIDGE-OUTPUT-002`'s `directOutputLower_conclusion_nontrivial`.  An equality
delivering `0` would be free; this one is not. -/
theorem directRobustification_conclusion_nontrivial {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) {CW bout : ℕ} {δU : ℝ} (hCW : 3 ≤ CW)
    (heq : D (EthBridge.Rnext W (Qwidth bout δU)) = CW + rQ bout δU) :
    7 ≤ D (EthBridge.Rnext W (Qwidth bout δU)) := by
  have h7 : 7 ≤ CW + rQ bout δU :=
    directOutputLower_conclusion_nontrivial (bout := bout) (δU := δU) hCW
  omega

/-- **Non-vacuity (vii): the closed theorem fires at the first banked
entry-gate witness.**

`b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `C_W = 3` (the boundary of line 40),
where `Q_0 = 4800`, `r_Q = 13`, `Q = 8192` and `x_out = 1/2`.  Every numeric
binder of `directRobustification` is discharged **by computation** — including
the frozen range `θ ≤ 1` and the second-gate margin, which is tight at
`δ_U = 1/60` and is not implied by `0 < δ_U < 1`, through the banked
`EntryGates.secondEntryGate_of_deltaU_small`.  `X`, `Y`, `W` stay universally
quantified and `eq:direct-input` together with `comp W = C_W` stay hypotheses,
since the bridge's input has no exhibited inhabitant and can have none until
Stages 1--4 land.  The equality then reads `comp R⁺ = 16`. -/
theorem directRobustification_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = 3)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 (1 / 192000) (1 - 1 / 60)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 192000) (3 / 5)) :
    Qwidth 1 (1 / 60) = 8192 ∧
      D (EthBridge.Rnext W (Qwidth 1 (1 / 60))) = 16 ∧
      (3 : ℕ) + 13 ≤ LambdaGE (EthBridge.Rnext W (Qwidth 1 (1 / 60))) 1
        (xOut 1) (3 / 5) ∧
      Nat.clog 2 (Qwidth 1 (1 / 60)) = 13 := by
  obtain ⟨-, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 60) (le_refl (1 / 60 : ℝ))
  have hθ1 : (1 / 192000 : ℝ) ≤ 1 :=
    theta_le_one_of_entryGate (bout := 1) (by norm_num) hgate
  obtain ⟨heq, hrob, hbits, -⟩ :=
    directRobustification W 3 1 (δU := 1 / 60) (θ := 1 / 192000) (by norm_num)
      (by norm_num) (by norm_num) hθ1 hX hY hCWeq (le_refl 3) hNear hInput
      (le_refl 1) ⟨hgate, hmargin⟩
  rw [hrQ] at heq hrob hbits
  exact ⟨hQ, by omega, hrob, hbits⟩

/-- **Non-vacuity (viii): the closed theorem fires again at the second banked
witness, at a different arithmetic.**

`b_out = 1`, `δ_U = 1/200`, `θ = 1/640000`, `C_W = 3`, where `Q_0 = 16000`,
`r_Q = 14` and `Q = 16384`.  The width, the canonical exponent, the selector
cost and the delivered constant all move — the equality now reads
`comp R⁺ = 17` — which a hypothesis list satisfiable at only one numeral could
not do. -/
theorem directRobustification_fires_second_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hCWeq : D W = 3)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 (1 / 640000) (1 - 1 / 200)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 640000) (3 / 5)) :
    Qwidth 1 (1 / 200) = 16384 ∧
      D (EthBridge.Rnext W (Qwidth 1 (1 / 200))) = 17 ∧
      (3 : ℕ) + 14 ≤ LambdaGE (EthBridge.Rnext W (Qwidth 1 (1 / 200))) 1
        (xOut 1) (3 / 5) ∧
      Nat.clog 2 (Qwidth 1 (1 / 200)) = 14 := by
  obtain ⟨-, hrQ, hQ, -, -, -, -⟩ := directOutput_fires_second_witness
  have hgate : 4 * Q0 1 (1 / 200) * (1 / 640000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 200) (by norm_num : (1 / 200 : ℝ) ≤ 1 / 60)
  have hθ1 : (1 / 640000 : ℝ) ≤ 1 :=
    theta_le_one_of_entryGate (bout := 1) (by norm_num) hgate
  obtain ⟨heq, hrob, hbits, -⟩ :=
    directRobustification W 3 1 (δU := 1 / 200) (θ := 1 / 640000) (by norm_num)
      (by norm_num) (by norm_num) hθ1 hX hY hCWeq (le_refl 3) hNear hInput
      (le_refl 1) ⟨hgate, hmargin⟩
  rw [hrQ] at heq hrob hbits
  exact ⟨hQ, by omega, hrob, hbits⟩

/-- **Non-vacuity (ix): the carriers fire at the canonical width of the first
witness.**

`|Rows(R⁺)| = n^{8192}` and `|Cols(R⁺)| = 8192 m` there, so the carrier
equations are read at the width the bridge actually uses and not only at the
small nondegenerate inhabitant.  `X`, `Y`, `W` stay universally quantified,
which is what makes this a property of the construction rather than of one
matrix. -/
theorem bridgeCarriers_canonical_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) :
    Qwidth 1 (1 / 60) = 8192 ∧
      rowsCard (EthBridge.Rnext W (Qwidth 1 (1 / 60))) = colsCard W ^ 8192 ∧
      colsCard (EthBridge.Rnext W (Qwidth 1 (1 / 60))) = 8192 * rowsCard W := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  obtain ⟨hrow, hcol⟩ := bridgeCarriers_canonical W 1 (1 / 60)
  refine ⟨hQ, ?_, ?_⟩
  · rw [hrow, hQ]
  · rw [hcol, hQ]

end EthInapproximability.ParameterizedNP.BridgeOutputEquality
