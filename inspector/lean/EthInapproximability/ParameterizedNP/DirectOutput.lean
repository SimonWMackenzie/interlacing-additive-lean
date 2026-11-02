import EthInapproximability.ParameterizedNP.EntryGates
import EthInapproximability.ParameterizedNP.PilotStage3

/-!
# Parameterized NP route: the output-side apparatus of the direct bridge

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-OUTPUT-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1h` tranche as the output-side apparatus of
`thm:direct-robustification`: the selector claims of lines 73--74, which
consume the landed canonical-`Q` interface of `BRIDGE-ENTRY-001`, and the
ceiling ladder of lines 78--91 — the retained-row floor `A_a`, the level
restriction `2^a θ ≤ 1`, and `eq:direct-ceiling-ladder` — with the literal
ceilings preserved exactly as the frozen source writes them.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`, `thm:direct-robustification` (label
  line 35):
  * lines 73--74, "The selector protocol of
    `lem:interlace-selector-protocol` adds exactly `r_Q` bits to a protocol
    for `W`, because `Q = 2^{r_Q}`" — the whole selector section below;
  * line 63, `R⁺ = Int_Q(W)^T`, used **only** as the orientation the selector
    sentence is stated about.  The equalities of `eq:direct-output` are not
    claimed (see GAP-EXPOSED).
* `sections/03-preliminaries.tex`, `lem:interlace-selector-protocol` (label
  line 149): `eq:interlace-selector-upper` (label line 154), the displayed
  bound at lines 152--153, and the sentence at lines 156--157, "In
  particular, if `p = 2^w`, the displayed protocol uses exactly `w` selector
  bits before running a protocol for `M`."
* `sections/10-direct-bridge.tex`, `subsec` "Column defect and row
  thresholds" (line 77):
  * line 79, `m = |Rows(W)|` and `n = |Cols(W)|`;
  * lines 81--83, `A_a = ⌈m 2^a θ⌉` for every integer `a ≥ 0`;
  * line 84, "We use only levels for which `2^a θ ≤ 1`" — the level
    restriction, transcribed here as `levelAdmissible`;
  * `eq:direct-ceiling-ladder` (label line 88, display lines 86--87),
    `A_{a-1} ≤ ⌈A_a/2⌉` for `a ≥ 1`;
  * lines 90--91, its two-step justification, "Indeed, `A_a ≥ m 2^a θ`, so
    `⌈A_a/2⌉ ≥ ⌈m 2^{a-1} θ⌉ = A_{a-1}`" — the first step is `le_rowFloor`
    below.
* `sections/10-direct-bridge.tex`, `eq:direct-entry-gates` (label line 56)
  and lines 58--60, consumed unchanged from `BRIDGE-ENTRY-001` to discharge
  the level restriction at the levels the bridge uses.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex`.  The file was
opened and the cited item checked to state the same fact:

* lines 112--113, inside the statement of `thm:near-to-robust`: "If `W` has a
  protocol of cost at most `U`, then `R⁺` has a protocol of cost at most
  `U + r_Q`."  This is the reader counterpart of the selector sentence, and it
  is assigned to **exactly one** declaration, `canonicalSelectorProtocol`,
  whose closed statement is that sentence.  `BRIDGE-ENTRY-001` recorded this
  item as deliberately unclaimed; it is claimed here and nowhere else.

No other reader item is claimed, and **no reader item is assigned twice**.  In
particular:

* `eq:bridge-output` (label line 110) and `eq:bridge-carriers` (label line
  117) stay **unclaimed** and remain with `BRIDGE-001` — see GAP-EXPOSED.
* The ceiling material has **no reader counterpart available, and none is
  assigned**: the reader states `A_a = ⌈m 2^a θ⌉` and
  `eq:appendix-ceiling-ladder` in `B-bridge-details.tex` lines 39--69, and
  that whole subsection is already recorded as the counterpart of
  `BRIDGE-DEFECT-001`'s readouts (`rowFloor`, `rowFloor_ceiling_ladder`).
  Those two are therefore **consumed here, never redefined and never
  re-proved**, and the genuinely new declarations of this module's ceiling
  section — the level restriction and its consequences — are given no reader
  counterpart rather than a shared one.  The reader's only mention of the
  level restriction is the proof-body sentence at line 130 ("The gates imply
  `p_t ≤ Q`, `2^{a_t} θ < 1`"), and prose inside a proof is not cited as a
  statement.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **new (elementary)** throughout, over two **consumed**
  checked interfaces.  Nothing in either interface is edited or re-proved:
  * `EthInapproximability.ParameterizedNP.powerOfTwoInterlace_upper`
    (`PilotStage3.lean`), the already-audited transcription of
    `lem:interlace-selector-protocol` at a power-of-two width, and
    `NPCC.comp_transpose` for the `R⁺` orientation;
  * `EthInapproximability.ParameterizedNP.DefectInduction.rowFloor` and
    `.rowFloor_ceiling_ladder` (`BRIDGE-DEFECT-001`), the banked `A_a` and
    `eq:direct-ceiling-ladder`; the ladder is re-exported as
    `directCeilingLadder` and both are otherwise untouched;
  * `EthInapproximability.ParameterizedNP.EntryGates.rQ`, `.Qwidth`,
    `.Q0`, `.deltaFixed`, `.entryGate_row_request_legal`,
    `.secondEntryGate_of_deltaU_small` (`BRIDGE-ENTRY-001`), the canonical-`Q`
    interface, likewise consumed.
* Imports: `EntryGates.lean` and `PilotStage3.lean` only, hence
  `ThreeCopyRowStep.lean`, `TwoCopyLadder.lean`, `DefectInduction.lean`,
  `InheritedContracts.lean`, `EthInapproximability.Prelude`, and through it
  `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`; `PilotStage3`
  adds `NPCC.Upper` and `Workspace.UpperBound`, neither of which reaches
  `NPCC.Axioms`.  `LegacyNPCC.Stage12` is **not** imported, so the AGHP
  balanced-family axiom is not in scope, and there is no contact with
  `EXPANDER-001` (which by design has no Lean declaration and would have to
  remain an explicit named hypothesis).
* External adapters: none.  Nothing here is axiomatized.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

The one genuinely open encoding choice is the **level restriction** of line
84, "We use only levels for which `2^a θ ≤ 1`".  Two candidates were written
out and run against the same aux battery — (a) closure downwards in the level,
(b) closure downwards in the row threshold, (c) the bound `A_a ≤ m` that the
restriction exists to supply, and (d) the round trip back to line 84 itself.

**Candidate A (landed).**  `levelAdmissible θ a : Prop := 2^a * θ ≤ 1`.  This
is line 84 read literally, and it is *byte-identical to the `hlevel` binder of
the landed* `DefectInduction.defectInduction`, so `levelAdmissible_iff` is
`Iff.rfl` and the binder is discharged with no translation step at all.  All
four aux lemmas proved: (a) `levelAdmissible_of_le`, (b)
`levelAdmissible_of_theta_le`, (c) `rowFloor_le_rows`, (d) `levelAdmissible_iff`.

**Candidate B (rejected — disqualified by a failed aux lemma).**
`levelAdmissible' m θ a : Prop := rowFloor m θ a ≤ m`, i.e. "the level is legal
when its retained-row floor fits inside the row carrier".  This reads the
*purpose* of line 84 rather than its text, and (d) is **false**:
`levelAdmissible_candidateB_refuted` proves, in Lean, that at `m = 0`,
`θ = 2`, `a = 0` the predicate `rowFloor 0 2 0 ≤ 0` holds while `2^0 · 2 ≤ 1`
does not.  So Candidate B is satisfied at *every* level by an empty row
carrier and would let a cardinality-degenerate instance pass the very check
line 84 imposes.  A failed aux lemma disqualifies the encoding, so Candidate B
was not landed; its refutation is kept as a checked theorem rather than as
prose.

Ranking (aux lemmas proved, faithfulness, length): A = 4/4, literal, `Iff.rfl`
against the landed binder; B = 3/4, purposive rather than literal, and
vacuously true on the degenerate carrier.  A landed.

## Faithfulness notes (mechanical rules M1--M10)

* The module introduces **no structure at all** and exactly one new definition,
  `levelAdmissible`, which is a `Prop` abbreviation for the inequality the
  paper displays.  No conclusion of `thm:direct-robustification` sits in
  constructor data, and no premise bundle is introduced: every deliverable
  takes its hypotheses as **explicit binders**.
* **Literal ceilings.**  `A_a` is not redefined: `DefectInduction.rowFloor`
  is `⌈m 2^a θ⌉₊` and is imported.  `eq:direct-ceiling-ladder` keeps the
  frozen outer ceiling `⌈A_a / 2⌉` verbatim — it is *not* rewritten as
  `(A_a + 1) / 2` in `ℕ`, even though the two agree, because the frozen
  display is a real-valued ceiling.
* **Selector costs preserved.**  Line 74 says *exactly* `r_Q` bits, and
  `canonicalSelectorBits` pins the count as `Nat.clog 2 Q = r_Q` rather than
  leaving an inequality; the additive upper bound is separately
  `canonicalSelectorUpper`.  `r_Q` is the exponent of the canonical width
  `Q = 2^{r_Q}` of `BRIDGE-ENTRY-001` and is never recomputed here.
* **Both interlace widths.**  Only the outer width `Q` occurs in this module.
  The scale-alignment width `q` does not appear and is not conflated with it;
  `Qwidth` lands in `ℕ` because it is a copy count.
* **Binder order** follows the frozen sentence: the matrix, then the requested
  depth `b_out` and the deletion tolerance `δ_U` that fix `Q`, then the row
  threshold `θ` and the level `a`.
* **Finite carriers and nonemptiness.**  `rowFloor_le_rows` is the frozen
  reason the level restriction is imposed, and
  `rows_equipartitionedGE_of_levelAdmissible` turns it into the row-carrier
  nonemptiness fact the bracket family needs, by consuming the landed
  `DefectInduction.univ_rows_equipartitionedGE`.
* **Trivial-witness pole.**  There is **no existential deliverable** in this
  module.  Every claim is either an upper bound on a named complexity, an
  equation between named readouts, or a named-def claim about
  `levelAdmissible`, exactly as the pipeline requires when a trivial witness
  cannot be excluded.  In particular `canonicalSelectorBits` is not "there
  exists a bit count that works" — which any large count would satisfy — but
  the exact value of `Nat.clog 2 Q`, which every other count refutes.
* **Vacuous-hypothesis pole.**  `levelAdmissible` is not free: it is **false**
  at `θ = 1` for every `a ≥ 1` (`levelAdmissible_refuted_at_large_theta`), so
  the frozen range `0 < θ ≤ 1` of line 39 does not imply it and line 84 is a
  genuine restriction.
* **Non-vacuity at legal values.**  Two independent entry-gate witnesses are
  carried, both at the globally fixed `y = 3/5`: the `BRIDGE-ENTRY-001`
  witness `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000` with `Q_0 = 4800`,
  `r_Q = 13`, `Q = 8192`; and the second witness at `δ_U ≤ 1/200`, namely
  `b_out = 1`, `δ_U = 1/200`, `θ = 1/640000` with `Q_0 = 16000`, `r_Q = 14`,
  `Q = 16384`, whose first gate is again **tight** (`4 Q_0 θ = δ` exactly).
  Both give interior selector costs (13 and 14 bits, against the general floor
  `r_Q ≥ 4`), and the second is carried through the ceiling ladder as well:
  at `m = 640000` the floors read `A_0 = 1`, `A_1 = 2`, `A_2 = 4`, so the
  ladder is exhibited **tight and with no zero rung**, which a degenerate
  witness (`A_a = 0` throughout) would not be.

## GAP-EXPOSED

`thm:direct-robustification` is **not** claimed.  Its conclusion
`eq:direct-output` (label line 71) is untouched in both halves: neither the
exact complexity `comp R⁺ = C_W + r_Q` (this module proves only the selector's
**upper** direction, which line 73 is about) nor the output robustness
`Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q`.  The carrier identities
`eq:bridge-carriers`, the good-block count, the three output rungs, and the
column-defect induction that produces them are all untouched, and
`eq:direct-input` remains a pair of named hypotheses supplied by Sections
8--9.  Nothing about route completion is claimed.
-/

namespace EthInapproximability.ParameterizedNP.DirectOutput

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.EntryGates

/-! ## Part 1: the selector claims of `10-direct-bridge.tex:73--74`

"The selector protocol of `lem:interlace-selector-protocol` adds exactly `r_Q`
bits to a protocol for `W`, because `Q = 2^{r_Q}`."

`lem:interlace-selector-protocol` itself is the checked interface
`EthInapproximability.ParameterizedNP.powerOfTwoInterlace_upper`; it is
consumed, never re-proved. -/

/-- **Facade re-export of the checked selector interface.**

`lem:interlace-selector-protocol` (`03-preliminaries.tex:148--158`) at a
power-of-two width: `comp(Int_M(2^w)) ≤ comp M + w`.  This is the already
audited `powerOfTwoInterlace_upper`, re-exported under a route-local name so
that every consumer below reads it through one place. -/
theorem selectorUpper_two_pow {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (w : ℕ) :
    D (interlaceFun W (2 ^ w)) ≤ D W + w :=
  powerOfTwoInterlace_upper W w

/-! ### Aux-lemma battery for the selector readout

General properties of the canonical width, each stated for arbitrary `b_out`
and `δ_U` rather than for a pinned assignment. -/

/-- **Aux 1 (the power-of-two bit count).**  `⌈log₂ 2^w⌉ = w`: the general
fact behind line 74's "because `Q = 2^{r_Q}`".  Stated for an arbitrary
exponent, so it is not a property of the route's particular width. -/
lemma clog_two_pow (w : ℕ) : Nat.clog 2 (2 ^ w) = w :=
  Nat.clog_pow 2 w one_lt_two

/-- **Aux 2 (the canonical width is positive).**  A copy count of zero would
make every statement below vacuous, so positivity is recorded before anything
consumes the width. -/
lemma Qwidth_pos (bout : ℕ) (δU : ℝ) : 0 < Qwidth bout δU := by
  rw [Qwidth]
  exact pow_pos (by norm_num) _

/-- **Aux 3 (the canonical width is at least sixteen).**  From
`EntryGates.four_le_rQ`: `Q = 2^{r_Q} ≥ 2^4`.  So the selector is never
degenerate — it always carries at least four bits and the interlace always has
at least sixteen copies. -/
lemma sixteen_le_Qwidth (bout : ℕ) (δU : ℝ) : 16 ≤ Qwidth bout δU := by
  have h4 := four_le_rQ bout δU
  have : (2 : ℕ) ^ 4 ≤ 2 ^ rQ bout δU := Nat.pow_le_pow_right (by norm_num) h4
  simpa [Qwidth] using this

/-- **Aux 4 (monotone in the width exponent).**  A wider canonical interlace
costs more selector bits.  Recorded because the two carried witnesses sit at
`r_Q = 13` and `r_Q = 14`, and the comparison between them is this
monotonicity rather than a coincidence of the numerals. -/
lemma selectorBits_mono {w w' : ℕ} (h : w ≤ w') {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) :
    D (interlaceFun W (2 ^ w)) ≤ D W + w' :=
  le_trans (selectorUpper_two_pow W w) (Nat.add_le_add_left h _)

/-! ### The selector claim theorems -/

/-- **Claim (exactly `r_Q` bits)** — `10-direct-bridge.tex:74`, "because
`Q = 2^{r_Q}`".

The selector count of `lem:interlace-selector-protocol` at the canonical width
is *exactly* `r_Q`, not merely at most `r_Q`.  This is a named-def claim about the
pinned `Qwidth` of `BRIDGE-ENTRY-001`; a larger count refutes it rather than
satisfying it. -/
theorem canonicalSelectorBits (bout : ℕ) (δU : ℝ) :
    Nat.clog 2 (Qwidth bout δU) = rQ bout δU := by
  rw [Qwidth]
  exact clog_two_pow _

/-- **Claim (the selector adds `r_Q` bits to a protocol for `W`)** —
`10-direct-bridge.tex:73--74`.

The interlace at the canonical width costs at most `comp W + r_Q`.  Only the
upper direction is claimed: the matching lower bound is part of
`eq:direct-output` and is **not** touched here. -/
theorem canonicalSelectorUpper {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (bout : ℕ) (δU : ℝ) :
    D (interlaceFun W (Qwidth bout δU)) ≤ D W + rQ bout δU := by
  rw [Qwidth]
  exact selectorUpper_two_pow W (rQ bout δU)

/-- **Claim (the same, in the `R⁺` orientation)** —
`10-direct-bridge.tex:63` for the orientation, lines 73--74 for the cost.

`R⁺ = Int_Q(W)^T`, and transposition costs nothing
(`NPCC.comp_transpose`, consumed), so the selector bound transports to the
transposed matrix unchanged.  The vendored `EthBridge.Rnext` is the frozen
`R⁺` and is used here rather than a second transcription of line 63. -/
theorem canonicalSelectorUpper_transpose {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (bout : ℕ) (δU : ℝ) :
    D (EthBridge.Rnext W (Qwidth bout δU)) ≤ D W + rQ bout δU := by
  have hswap : D (EthBridge.Rnext W (Qwidth bout δU))
      = D (interlaceFun W (Qwidth bout δU)) :=
    NPCC.comp_transpose (interlaceFun W (Qwidth bout δU))
  rw [hswap]
  exact canonicalSelectorUpper W bout δU

/-- **Claim (the reader's protocol form)** — reader
`04-bridge.tex:112--113`: "If `W` has a protocol of cost at most `U`, then
`R⁺` has a protocol of cost at most `U + r_Q`."

This is the one reader item claimed by this module, and it is claimed by this
declaration alone.  `U` is an explicit binder, exactly as the reader writes
it. -/
theorem canonicalSelectorProtocol {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (bout : ℕ) (δU : ℝ) (U : ℕ) (hU : D W ≤ U) :
    D (EthBridge.Rnext W (Qwidth bout δU)) ≤ U + rQ bout δU :=
  le_trans (canonicalSelectorUpper_transpose W bout δU)
    (Nat.add_le_add_right hU _)

/-! ## Part 2: the ceiling ladder of `10-direct-bridge.tex:78--91`

`A_a` and `eq:direct-ceiling-ladder` are **banked** in `BRIDGE-DEFECT-001`
(`DefectInduction.rowFloor`, `.rowFloor_ceiling_ladder`).  They are related to
here, never redefined and never re-proved.  What is new is the level
restriction of line 84 and the two frozen facts the ladder's justification at
lines 90--91 rests on. -/

/-- **The level restriction** — `10-direct-bridge.tex:84`, "We use only levels
for which `2^a θ ≤ 1`".

A `Prop` abbreviation for exactly the inequality the paper writes, and nothing
more.  It is *byte-identical* to the `hlevel` binder of the landed
`DefectInduction.defectInduction`, so `levelAdmissible_iff` below is `Iff.rfl`
and that binder is discharged with no translation step.  This is Candidate A of
the header. -/
def levelAdmissible (θ : ℝ) (a : ℕ) : Prop := (2 : ℝ) ^ a * θ ≤ 1

/-- **Aux 5 / round trip (the landed encoding is line 84 verbatim).**  Also
the shape in which `DefectInduction.defectInduction` takes its `hlevel`
binder. -/
lemma levelAdmissible_iff (θ : ℝ) (a : ℕ) :
    levelAdmissible θ a ↔ (2 : ℝ) ^ a * θ ≤ 1 := Iff.rfl

/-- **Aux 6 (level zero).**  Line 39's own range `0 < θ ≤ 1` already makes the
bottom level legal, so the restriction bites only at positive levels. -/
lemma levelAdmissible_zero {θ : ℝ} (hθ : θ ≤ 1) : levelAdmissible θ 0 := by
  simpa [levelAdmissible] using hθ

/-- **Aux 7 (closed downwards in the level).**  If a level is legal then so is
every lower one.  This is what lets `eq:direct-ceiling-ladder`, which relates
level `a` to level `a - 1`, be applied inside the legal range without a fresh
check at each rung. -/
lemma levelAdmissible_of_le {θ : ℝ} {a a' : ℕ} (hθ0 : 0 ≤ θ) (haa : a' ≤ a)
    (h : levelAdmissible θ a) : levelAdmissible θ a' := by
  have hpow : (2 : ℝ) ^ a' ≤ (2 : ℝ) ^ a :=
    pow_le_pow_right₀ (by norm_num) haa
  exact le_trans (mul_le_mul_of_nonneg_right hpow hθ0) h

/-- **Aux 8 (closed downwards in the row threshold).**  Lowering `θ` keeps a
level legal.  Recorded because the first entry gate is an *upper* bound on
`θ`, so legality is inherited by every smaller threshold the route may
choose. -/
lemma levelAdmissible_of_theta_le {θ θ' : ℝ} {a : ℕ} (hθθ : θ' ≤ θ)
    (h : levelAdmissible θ a) : levelAdmissible θ' a := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hθθ hpow.le) h

/-- **Aux 9 (`A_a ≥ m 2^a θ`)** — `10-direct-bridge.tex:90`, the first step of
the ladder's justification.  It is `Nat.le_ceil` on the banked `rowFloor`, and
it is the only place the frozen line-90 inequality is needed. -/
lemma le_rowFloor (m : ℕ) (θ : ℝ) (a : ℕ) :
    (m : ℝ) * (2 : ℝ) ^ a * θ ≤ (rowFloor m θ a : ℝ) := by
  rw [rowFloor]
  exact Nat.le_ceil _

/-- **Aux 10 (the point of the level restriction).**  On a legal level the
retained-row floor fits inside the row carrier: `A_a ≤ m`.  This is why line
84 is imposed, and it is the fact the bracket family's row premise needs.

Line 84 alone suffices: no positivity of `θ` is assumed here, because carrying
`0 ≤ θ` would be an over-strong hypothesis the frozen sentence does not
have. -/
lemma rowFloor_le_rows (m : ℕ) {θ : ℝ} {a : ℕ}
    (hlev : levelAdmissible θ a) : rowFloor m θ a ≤ m := by
  rw [rowFloor]
  refine Nat.ceil_le.mpr ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hstep : (m : ℝ) * ((2 : ℝ) ^ a * θ) ≤ (m : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hlev hm
  calc (m : ℝ) * (2 : ℝ) ^ a * θ = (m : ℝ) * ((2 : ℝ) ^ a * θ) := by ring
    _ ≤ (m : ℝ) * 1 := hstep
    _ = (m : ℝ) := by ring

/-- **Facade re-export of `eq:direct-ceiling-ladder`** —
`10-direct-bridge.tex:86--88`, `A_{a-1} ≤ ⌈A_a/2⌉` for `a ≥ 1`.

The banked `DefectInduction.rowFloor_ceiling_ladder`, consumed unchanged and
re-exported under the route-local name so that this module's ladder statements
read through one place.  The outer ceiling is kept **literally** as the frozen
real-valued `⌈A_a / 2⌉`; it is not rewritten into `ℕ`. -/
theorem directCeilingLadder (m : ℕ) (θ : ℝ) (a : ℕ) (ha : 1 ≤ a) :
    rowFloor m θ (a - 1) ≤ ⌈(rowFloor m θ a : ℝ) / 2⌉₊ :=
  rowFloor_ceiling_ladder m θ a ha

/-- **The ladder inside the legal range.**  Combining the re-export with Aux 7:
if level `a ≥ 1` is legal, then the ladder step is available *and* its lower
rung `a - 1` is legal too, so the descent never leaves the range line 84
permits. -/
theorem directCeilingLadder_of_levelAdmissible (m : ℕ) {θ : ℝ} {a : ℕ}
    (hθ0 : 0 ≤ θ) (ha : 1 ≤ a) (hlev : levelAdmissible θ a) :
    rowFloor m θ (a - 1) ≤ ⌈(rowFloor m θ a : ℝ) / 2⌉₊ ∧
      levelAdmissible θ (a - 1) :=
  ⟨directCeilingLadder m θ a ha,
    levelAdmissible_of_le hθ0 (Nat.sub_le a 1) hlev⟩

/-- **Row-carrier nonemptiness on a legal level.**  The full row carrier of an
interlace meets the floor `A_a` at every legal level, by feeding
`rowFloor_le_rows` to the banked
`DefectInduction.univ_rows_equipartitionedGE`.  So the row premise of the
bridge's bracket families is never vacuous inside the range line 84 permits —
which is exactly the service the level restriction performs. -/
theorem rows_equipartitionedGE_of_levelAdmissible {ι X : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype X] {θ : ℝ} {a : ℕ}
    (hlev : levelAdmissible θ a) :
    IsEquipartitionedGE (Finset.univ : Finset (ι × X))
      (Finset.univ : Finset ι) (rowFloor (Fintype.card X) θ a) :=
  univ_rows_equipartitionedGE _ (rowFloor_le_rows (Fintype.card X) hlev)

/-! ## Wiring to the landed entry gate

The frozen legality sentence at `10-direct-bridge.tex:58--60` is consumed from
`BRIDGE-ENTRY-001`; nothing there is re-derived. -/

/-- **The entry gate makes every level up to two legal.**

`10-direct-bridge.tex:58--60` gives `4θ ≤ δ/Q_0 < 1`, hence `2^2 θ ≤ 1`, and
Aux 7 propagates legality downwards.  The bridge's base games sit at levels
`0, 1, 2` (`eq:direct-input`, `eq:direct-two-copy`, `eq:direct-three-copy`), so
this is precisely the range they need.  Claims **no** reader item: it is the
frozen sentence applied to a statement already landed in
`BRIDGE-ENTRY-001`. -/
theorem levelAdmissible_of_entryGate (bout : ℕ) {δU θ : ℝ} {a : ℕ}
    (hθ0 : 0 ≤ θ) (ha : a ≤ 2)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed) : levelAdmissible θ a := by
  have hrow : 4 * θ ≤ 1 := entryGate_row_request_legal bout hgate
  have htwo : levelAdmissible θ 2 := by
    simp only [levelAdmissible]
    norm_num
    linarith
  exact levelAdmissible_of_le hθ0 ha htwo

/-! ## Non-vacuity and the statement poles -/

/-- **Non-vacuity (i): the level restriction is not free.**

At `θ = 1` — inside line 39's own range `0 < θ ≤ 1` — every level `a ≥ 1` is
**illegal**.  So line 84 genuinely restricts, and a transcription that dropped
it would be strictly weaker than the frozen text. -/
theorem levelAdmissible_refuted_at_large_theta {a : ℕ} (ha : 1 ≤ a) :
    ¬ levelAdmissible (1 : ℝ) a := by
  simp only [levelAdmissible, mul_one, not_le]
  calc (1 : ℝ) < 2 ^ 1 := by norm_num
    _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha

/-- **Non-vacuity (ii): Candidate B is refuted in Lean.**

The rejected encoding "`A_a ≤ m`" does **not** imply line 84: at `m = 0`,
`θ = 2`, `a = 0` the floor condition holds (`⌈0⌉ = 0 ≤ 0`) while `2^0 · 2 ≤ 1`
fails.  A cardinality-degenerate row carrier would therefore pass Candidate B
at every level, which is exactly the failure mode the level restriction
exists to block. -/
theorem levelAdmissible_candidateB_refuted :
    ¬ ∀ (m : ℕ) (θ : ℝ) (a : ℕ), 0 ≤ θ → rowFloor m θ a ≤ m →
        levelAdmissible θ a := by
  intro h
  have hfloor : rowFloor 0 (2 : ℝ) 0 ≤ 0 := by
    simp [rowFloor]
  have := h 0 (2 : ℝ) 0 (by norm_num) hfloor
  simp only [levelAdmissible] at this
  norm_num at this

/-- **Non-vacuity (iii): the first carried entry-gate witness.**

The `BRIDGE-ENTRY-001` witness `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`,
`y = 3/5` gives `r_Q = 13` and `Q = 8192`, so the selector costs **exactly**
thirteen bits — interior, against the general floor `r_Q ≥ 4` of
`EntryGates.four_le_rQ` — and every level up to two is legal. -/
theorem selector_fires_first_witness :
    rQ 1 (1 / 60) = 13 ∧ Qwidth 1 (1 / 60) = 8192 ∧
      Nat.clog 2 (Qwidth 1 (1 / 60)) = 13 ∧
      (∀ a : ℕ, a ≤ 2 → levelAdmissible (1 / 192000 : ℝ) a) := by
  obtain ⟨-, -, hrQ, hQ, -, -, -⟩ := directEntryGates_fires
  refine ⟨hrQ, hQ, ?_, ?_⟩
  · rw [canonicalSelectorBits, hrQ]
  · intro a ha
    refine levelAdmissible_of_entryGate 1 (δU := 1 / 60) (by norm_num) ha ?_
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num

/-- **Non-vacuity (iv): the carried second entry-gate witness at
`δ_U ≤ 1/200`.**

`b_out = 1`, `δ_U = 1/200`, `θ = 1/640000`, and the globally fixed `y = 3/5`
— all strictly inside the frozen ranges of lines 38--41 — satisfy **both**
halves of `eq:direct-entry-gates`, with the entry apparatus taking the values
`Q_0 = 16000`, `r_Q = 14`, `Q = 16384`.  The first gate is again **tight**
(`4 Q_0 θ = δ` exactly), the maximum rests on its first branch, the selector
costs exactly fourteen bits, and every level up to two is legal.

Carrying a second witness at a strictly smaller deletion tolerance is what
shows the apparatus is not tuned to one numeral: `Q_0`, `r_Q` and the selector
cost all move, in the direction `EntryGates.Q0_antitone_deltaU` predicts. -/
theorem directOutput_fires_second_witness :
    Q0 1 (1 / 200) = 16000 ∧ rQ 1 (1 / 200) = 14 ∧
      Qwidth 1 (1 / 200) = 16384 ∧
      directEntryGates 1 (1 / 200) (1 / 640000) (3 / 5) ∧
      Nat.clog 2 (Qwidth 1 (1 / 200)) = 14 ∧
      (16 : ℝ) < Q0 1 (1 / 200) ∧
      (∀ a : ℕ, a ≤ 2 → levelAdmissible (1 / 640000 : ℝ) a) := by
  have hQ0 : Q0 1 (1 / 200) = 16000 := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hgate : 4 * Q0 1 (1 / 200) * (1 / 640000 : ℝ) ≤ deltaFixed := by
    rw [hQ0, deltaFixed_eq]; norm_num
  have hrQ : rQ 1 (1 / 200) = 14 := by
    refine le_antisymm (rQ_min (by rw [hQ0]; norm_num)) ?_
    by_contra hcon
    have h13 : rQ 1 (1 / 200) ≤ 13 := by omega
    have hmem := Q0_le_two_pow_rQ 1 (1 / 200)
    have hpow : (2 : ℝ) ^ rQ 1 (1 / 200) ≤ (2 : ℝ) ^ (13 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) h13
    rw [hQ0] at hmem
    norm_num at hpow
    linarith
  have hQwidth : Qwidth 1 (1 / 200) = 16384 := by
    rw [Qwidth, hrQ]; norm_num
  refine ⟨hQ0, hrQ, hQwidth,
    ⟨hgate, secondEntryGate_of_deltaU_small (by norm_num) (by norm_num)⟩,
    ?_, ?_, ?_⟩
  · rw [canonicalSelectorBits, hrQ]
  · rw [hQ0]; norm_num
  · intro a ha
    exact levelAdmissible_of_entryGate 1 (by norm_num) ha hgate

/-- **Non-vacuity (v): the ceiling ladder is exhibited tight, with no zero
rung, at the second witness.**

At `θ = 1/640000` and `m = 640000` the frozen floors read `A_0 = 1`,
`A_1 = 2`, `A_2 = 4`, and `eq:direct-ceiling-ladder` holds with **equality** at
both steps.  A degenerate inhabitant would read `A_a = 0` at every level and
satisfy the ladder trivially; this one does not, and every level used is legal
by `directOutput_fires_second_witness`. -/
theorem rowFloor_ladder_fires_second_witness :
    rowFloor 640000 (1 / 640000 : ℝ) 0 = 1 ∧
      rowFloor 640000 (1 / 640000 : ℝ) 1 = 2 ∧
      rowFloor 640000 (1 / 640000 : ℝ) 2 = 4 ∧
      rowFloor 640000 (1 / 640000 : ℝ) 0
        = ⌈(rowFloor 640000 (1 / 640000 : ℝ) 1 : ℝ) / 2⌉₊ ∧
      rowFloor 640000 (1 / 640000 : ℝ) 1
        = ⌈(rowFloor 640000 (1 / 640000 : ℝ) 2 : ℝ) / 2⌉₊ := by
  have h0 : rowFloor 640000 (1 / 640000 : ℝ) 0 = 1 := by
    rw [rowFloor]
    norm_num
  have h1 : rowFloor 640000 (1 / 640000 : ℝ) 1 = 2 := by
    rw [rowFloor]
    norm_num
  have h2 : rowFloor 640000 (1 / 640000 : ℝ) 2 = 4 := by
    rw [rowFloor]
    norm_num
  refine ⟨h0, h1, h2, ?_, ?_⟩
  · rw [h0, h1]; norm_num
  · rw [h1, h2]; norm_num

/-- **Non-vacuity (vi): the row floors of the second witness fit the carrier.**

`rowFloor_le_rows` at the same numbers: `A_2 = 4 ≤ 640000 = m`.  Together with
`rows_equipartitionedGE_of_levelAdmissible` this is the concrete form of the
service line 84 performs. -/
theorem rowFloor_le_rows_second_witness :
    rowFloor 640000 (1 / 640000 : ℝ) 2 ≤ 640000 := by
  refine rowFloor_le_rows 640000 ?_
  simp only [levelAdmissible]
  norm_num

/-- **Non-vacuity (vii): the selector claim fires at the pinned second
witness.**

`canonicalSelectorProtocol` at `b_out = 1`, `δ_U = 1/200`, where the canonical
width is `Q = 16384` and the selector cost is `r_Q = 14`.  The matrix `W` and
its carriers are left universally quantified — deliberately, since the bridge's
input matrix has no exhibited inhabitant in Lean and can have none until
Stages 1--4 land — but every numeric parameter is discharged by computation,
not assumed. -/
theorem canonicalSelectorProtocol_fires {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (U : ℕ) (hU : D W ≤ U) :
    D (EthBridge.Rnext W 16384) ≤ U + 14 := by
  obtain ⟨-, hrQ, hQwidth, -, -, -, -⟩ := directOutput_fires_second_witness
  have h := canonicalSelectorProtocol W 1 (1 / 200) U hU
  rw [hQwidth, hrQ] at h
  exact h

end EthInapproximability.ParameterizedNP.DirectOutput
