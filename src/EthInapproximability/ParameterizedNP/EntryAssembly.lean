import EthInapproximability.ParameterizedNP.DefectDischarge

/-!
# Parameterized NP route: the `t`-loop that assembles the entry rungs

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-ASSEMBLY-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1m` tranche for the assembly sentence of
`10-direct-bridge.tex:483--487`:

> "`\Cref{lem:defect-induction}` gives complexity at least `C_W + a_t = C_W +
> r_Q - t`.  This holds for `t = 0, 1, 2`, and hence
> `\LambdaThree{\Rnext}{1}{2^{-\bout}}{y} \ge C_W + r_Q`."

This module claims exactly that loop and nothing else.  It introduces **no new
definition**: every quantity it names (`entryLevelA`, `entryCopyCount`,
`entryDefectL`, `xOut`, `rowFloor`, `rQ`, `Qwidth`, `columnDensity`,
`LambdaGE`, `Dfamily`, `bracketGE`, `subgame`) is already banked.  What is new
is the *loop* — its invariant, its termination, and the fold of the three rungs
into the three-rung readout.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`,
and (unless stated otherwise) to `sections/10-direct-bridge.tex`.

* `thm:direct-robustification` (label line 35, statement lines 34--75):
  * line 51, "Let `Q = 2^{r_Q}` be the least power of two at least `Q_0`" —
    the width whose exponent is the loop's top level;
  * line 63, `R⁺ = Int_Q(W)^T`, the matrix the loop's conclusion is about;
  * `eq:direct-output` (label line 71, display lines 66--72), **second
    equation only**, `Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q`.
* `eq:direct-input` (label line 11, display lines 7--12) — the two
  common-threshold clauses.  They are carried as the **explicit named binders**
  `hNear` and `hInput` wherever the per-level entry step is consumed; nothing
  is axiomatized.
* §`sec:direct-entry` (label line 390):
  * lines 421--426, the **level schedule** of the loop: "For `t = 0, 1, 2`,
    define `a_t = r_Q - t`, `p_t = 2^{a_t - 1} + d`";
  * lines 452--455, "Let `V = Int_Q(W)`, so that `R⁺ = ᵀV`.  Take an arbitrary
    member of `B(R⁺; 1, x_out, y/2^t)`" — the loop body's universally
    quantified input, and the reason the rung premise is a `Dfamily` bound;
  * **line 457**, the transposition "Let `V = Int_Q(W)`, so that `R⁺ = ᵀV` ...
    and transpose it" — **discharged here**, route-natively, by
    `entryRung_transpose` over the banked one-copy transport
    `EthBridge.dfamily_one_transpose`;
  * lines 458--469, the good-copy dichotomy and the projection to `p_t` good
    copies — these, and only these, remain the **named hypothesis** `hsel`, see
    GAP-EXPOSED 2;
  * **line 471**, `2^{a_t} θ = Q θ / 2^t < 1` — the level schedule identity
    `2^{a_t} = Q / 2^t`, banked as `DirectOutputLower.entryLevel_pow_eq` and
    consumed here (never re-proved) in the product form
    `2^{a_t} · 2^t = Q`;
  * **lines 479--487**, the assembly proper: "`lem:defect-induction` gives
    complexity at least `C_W + a_t = C_W + r_Q - t`.  This holds for
    `t = 0, 1, 2`, and hence `Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W + r_Q`";
  * **line 488**, "The `t = 0` case gives `comp(R⁺) ≥ C_W + r_Q`".
* `def:lambda` (`sections/03-preliminaries.tex:224`, displayed unfolding at
  lines 234--240) — the three-rung readout `Λ` is a minimum of exactly three
  terms at densities `z`, `z/2`, `z/4`.  This is what fixes the loop's range at
  `t ∈ {0, 1, 2}` and is the whole content of its **termination**.
* `conv:finite-slots` (`sections/03-preliminaries.tex`) — zero-based finite
  slots; the coordinate carriers are `Fin Q` and `Fin (Qwidth b_out δ_U)`,
  exactly as in `FiniteSlots.lean`, `CopyRestriction.lean` and
  `DefectDischarge.lean`.

## Reader counterpart

The reader artifact of the same frozen release,
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/reader-facing`,
was opened first-hand before this section was written.

**No reader item is claimed by this module**, and that is deliberate: every
labelled reader item that states any part of the assembled bound is already
assigned to another declaration, and assigning one twice is forbidden.

* `sections/04-bridge.tex`, `eq:bridge-output` (label line 110, display lines
  106--111), **second equation**, is already assigned to
  `DirectOutputLower.directOutputLower` by `BRIDGE-OUTPUT-002`, and its
  **first** equation stays with `BRIDGE-001`.  Neither is reassigned here.
* The reader's own account of this very loop — `04-bridge.tex` lines 145--147
  ("Lemma ... gives complexity at least `C_W + a_t = C_W + r_Q - t`.  These are
  the three output rungs in `eq:bridge-output`.  The top rung lower-bounds the
  whole matrix.") and `B-bridge-details.tex` lines 233--234 ("The main defect
  induction gives complexity at least `C_W + a_t = C_W + r_Q - t`.  This proves
  all three output rungs.") — is **proof prose inside a proof environment**,
  which `BRIDGE-OUTPUT-002` already recorded as prose that is not cited as a
  statement.  Both are named here as the reader's navigation loci for what this
  module proves, and neither is claimed as a reader counterpart.
* `B-bridge-details.tex` line 175, `eq:appendix-Q-bounds`, the definition
  display at lines 185--192, and `lem:bridge-good-block-count` are the four
  items assigned to `BRIDGE-OUTPUT-002`; the schedule `a_t = r_Q - t` and the
  count `p_t` consumed here are that row's, not this one's.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge" (the row that
already carries `INHERIT-001`, `BRIDGE-COPYREST-001`, `BRIDGE-OUTPUT-002` and
`BRIDGE-DISCHARGE-001`).

## Dependencies, imports, external adapters

* Import: `EthInapproximability.ParameterizedNP.DefectDischarge` only (which
  transitively carries `CopyRestriction`, `DirectOutputLower`, `DirectOutput`,
  `EntryGates`, `TwoCopyLadder`, `DefectInduction`, `InheritedContracts`,
  `PilotStage3` and `Prelude`).  `LegacyNPCC.Stage12` is **not** reached, so
  the AGHP balanced-family axiom is not in this module's closure.
* Consumed, never re-proved: `DefectDischarge.entryLevelStep_ofParentColumnCount`,
  `.le_columnDensity_iff_ceil_le_card`, `.exists_proper_halfDensity_cols`,
  `DirectOutputLower.entryLevel_pow_eq`, `.entryLevelA`, `.entryCopyCount`,
  `.xOut`, `.xOut_le_one`, `.entryLevels_fire_first_witness`,
  `.entryCount_fires_first_witness`, `.directOutputRung`,
  `TwoCopyLadder.le_LambdaGE_iff`, `EntryGates.rQ`, `.Qwidth`, `.four_le_rQ`,
  `.Q0`, `.deltaFixed`, `.Q0_eq_route`, `.secondEntryGate_of_deltaU_small`,
  `.directEntryGates_fires`, `.xOut_pos`, `familyComplexity_le_ambient`,
  `powerOfTwoInterlace_upper`, `NPCC.bracketGE.nonempty`.
* External theorem adapters: **none new**.  Three vendored names are used
  directly, all of them already inside the route's closure: `EthBridge.Rnext`
  (`vendor/npc-cc/EthBridge/Entry.lean:181`) and `EthBridge.le_Dfamily`
  (line 311), which are plumbing rather than mathematics, and
  `EthBridge.dfamily_one_transpose` (line 285), the **one-copy transpose
  transport** `comp(bracket(fᵀ,1,y,x)) = comp(bracket(f,1,x,y))`.  The third is
  genuine content, and it is exactly the content of frozen line 457; it is
  consumed verbatim, never re-proved and never widened, and it carries no
  bracket-membership, density, counting or complexity claim of its own beyond
  that one equality.  It was already reached (inside `EthBridge.theorem_two`)
  by `BRIDGE-OUTPUT-002`'s `directOutputRung`, so consuming it adds nothing to
  the route's axiom surface.  The cited expander family `EXPANDER-001` is not
  touched and has, by design, no Lean declaration.
* Proof status: **new** (the loop), over inherited and previously landed parts.

## The inter-derivability note is honoured

`BRIDGE-DISCHARGE-001` records that its two discharge theorems are
inter-derivable: `entryLevelStep_ofParentDensity` (Candidate A, the frozen
density floor of lines 458--459) and `entryLevelStep_ofParentColumnCount`
(Candidate B, the inherited ceiling guard of
`D-inherited-contracts.tex:258`), with B proved *from* A by
`le_columnDensity_iff_ceil_le_card` so that only A carries content.  Its note
is explicit that "a caller holding a bracket membership has B".

The loop's caller is exactly such a caller: frozen lines 453--455 say "Take an
arbitrary member of `B(R⁺; 1, x_out, y/2^t)`", and after the transposition of
line 457 the surviving column set carries the **ceiling** count.  This module
therefore consumes **`entryLevelStep_ofParentColumnCount` only**, never both
variants and never the density variant, so no statement is double-consumed.

## Candidate encodings (k = 2) and the ranking

The concept is a *loop*, so the two candidates differ in how the loop variable
`t` is carried.

**Candidate A — the loop variable is a genuine binder.**  One premise,
universally quantified over the loop range:
`hrung : ∀ t, t ≤ 2 → C_W + a_t ≤ comp⟨R⁺, 1, x_out, y/2^t⟩`, with the fold
performed by a general engine `le_LambdaGE_of_rungs` that is stated for an
arbitrary rung function `c` satisfying the loop invariant `t + c t = n`.

**Candidate B — the loop is unrolled into three premises.**  Three separate
binders `h0`, `h1`, `h2` at the three densities `y`, `y/2`, `y/4`, folded by
`le_LambdaGE_iff` directly.

Both were written out.  Ranking (aux lemmas proved, faithfulness, length):

* aux lemmas: A = 6/6, B = 4/6 (B cannot state the invariant lemma or the
  strict-decrease lemma as properties of the loop, because it has no loop
  variable);
* faithfulness: the frozen sentence quantifies — "This holds for `t = 0, 1, 2`"
  — over a level schedule `a_t = r_Q - t` that is itself a function of `t`.  A
  keeps that quantification and derives the three instances; B hard-codes them
  and silently discards the schedule, so nothing in B would notice a wrong
  offset at a rung;
* length: A is shorter at every use site, because `directOutputRung` already
  has `t` as a binder and can be handed over wholesale.

**A is landed.**  B survives only as the trivially derived corollary shape
inside the non-vacuity witness, where the three instances are read off
explicitly at the carried numerals.

## Aux-lemma battery (8, all general, all proved)

None is about the pinned instance; each quantifies over arbitrary `b_out`,
`δ_U`, `t` (and, for the engine, over an arbitrary game, copy count,
parameters, target and rung function).

1. `one_le_two_pow_real` — the elementary helper `1 ≤ 2^t` over `ℝ`.
2. `entryRungOffset` — **the loop invariant**, verbatim from line 481:
   `t + a_t = r_Q` for `t ≤ 2`.  Stated on the additive side so the frozen
   `ℕ`-subtraction in `a_t = r_Q - t` is never truncated.  Identity property.
3. `entryLevelA_succ_lt` — **the termination measure**: `a_{t+1} < a_t` on the
   loop range, so the level schedule strictly descends.  Monotonicity property.
4. `two_le_entryLevelA` — **nondegeneracy of every rung**: `2 ≤ a_t` for
   `t ≤ 2`, from `EntryGates.four_le_rQ`.  This strengthens the banked
   `one_le_entryLevelA` to exactly what the three-rung range needs.
5. `entryLevelPow_mul_eq_Qwidth` — **round trip on the level schedule**:
   the banked `entryLevel_pow_eq` (`2^{a_t} = Q / 2^t`, line 471) in product
   form `2^{a_t} · 2^t = Q`.  Consumed, not re-derived.
6. `le_LambdaGE_of_rungs` — **the loop engine**, fully general: for any game,
   copy count, parameters, target `n` and rung function `c` with `t + c t = n`
   on the loop range, three rung bounds at densities `z / 2^t` fold into
   `n ≤ Λ`.  Inhabitation-of-the-hardest-field property: it is the only place
   the three-rung structure of `def:lambda` is used.
7. `entryRungFamily_nonempty` — **inhabitation**: at every rung the bracket
   family the loop quantifies over is nonempty (so the loop body is a genuine
   universal statement, and `Dfamily`'s `sInf` is not the empty-family `0`).
8. `entryColumnCarrier_nonempty` — **inhabitation of the transposed carrier**:
   the row carrier `Fin Q × X` of `V = Int_Q(W)` (equivalently the column
   carrier of `R⁺`) is nonempty whenever `X` is, since `Q = 2^{r_Q} > 0`.  This
   is the guard the `V`-side family needs.  Inhabitation property.

## Faithfulness notes (mechanical rules M1--M10)

* **No new definition, no structure, no premise bundle.**  Every hypothesis is
  an explicit binder; where the per-level entry step is consumed the binder
  list and order of `entryLevelStep_ofParentColumnCount` are reproduced
  unchanged.  Since there is no constructor anywhere in the module, no
  complexity or robustness conclusion can sit in constructor data.
* **Nothing is weakened.**  `entryDescent`'s conclusion is byte-identical to
  the conclusion of `DirectOutputLower.directOutputLower`; the difference is
  entirely on the premise side, where the concrete banked rung is replaced by
  an abstract rung premise that the banked rung discharges (non-vacuity
  witness 1).
* **Both interlace widths.**  Only the outer width `Q = Qwidth b_out δ_U` and
  the copy count `p_t = entryCopyCount b_out δ_U t` occur.  The
  scale-alignment width `q` does not appear and is not conflated with either.
* **Ceilings are preserved, not smoothed.**  The parent column guard stays in
  the `Nat.ceil` form `⌈|Y|^Q x_out⌉ ≤ |K|`; `rowFloor` is consumed unchanged.
* **Nonemptiness is carried.**  `hK : K.Nonempty` stays an explicit binder in
  every step statement, and aux 7 supplies the family nonemptiness that
  `Dfamily`'s `sInf` needs.
* **Finite carriers.**  `Fin Q`, `Fin Q × X`, `Fin Q → Y`; zero-based, per
  `conv:finite-slots`.
* **Trivial-witness pole.**  `entryDescent`, `entryAssembly_ofSelection`,
  `entryAssembly_ofVSideSelection`, `entryRung_transpose`,
  `entryRung_ofTransposedMembers`, `entryRung_ofVSideSelection`,
  `entryLoopStep` and `entryComplexityDescent` are **not** existentials — they
  are named-def claims about the pinned `R⁺ = Rnext W Q` and about the caller's
  own state — so there is no trivial witness to exclude on the deliverable
  side.  The one existential in the module is the loop witness
  `entryLoop_fires_two_levels`, and the trivial witness fails it in one line:
  `P = univ` and `K = univ` are refuted by the explicit `⊂ univ` conjuncts, and
  `P = ∅` is refuted by `P.card = p_t` together with `2048 < p_t`.
  Inside `hsel` the trivial selection is likewise excluded — `K = ∅` fails both
  `K.Nonempty` and `⌈|Y|^Q x_out⌉ ≤ |K|` (the ceiling is at least `1`), and
  `P = ∅` fails `P.card = p_t`.
* **Termination is the paper's, not invented.**  The loop stops at `t = 2`
  because `def:lambda` has exactly three rungs; the strict descent of aux 3 and
  the floor of aux 4 record that no rung of that range is degenerate.

## GAP-EXPOSED (nothing is weakened to close these)

1. **The upper direction of `eq:direct-output` is untouched.**  Only the second
   equation, and only its `≥` direction, is assembled.  The equality
   `comp R⁺ = C_W + r_Q` remains with `BRIDGE-OUTPUT-003`.
2. **The good-copy selection is not rewired — but the transpose now is.**
   Frozen line 457 (the transposition to `V = Int_Q(W)`) **is** discharged
   route-natively by `entryRung_transpose`, so what remains hypothetical is
   strictly less than the whole of lines 456--469: it is the row-count
   dichotomy of `eq:direct-good-copy-count` (lines 459--463) together with the
   projection of lines 465--469.  Those are the named hypothesis `hsel` of
   `entryRung_ofVSideSelection` and `entryAssembly_ofVSideSelection`, where
   `hsel` is stated on the `V` side — about a restriction of `Int_Q(W)`, which
   is the object those frozen lines are about — rather than on the `R⁺` side.
   The older `R⁺`-side forms `entryRung_ofSelection` and
   `entryAssembly_ofSelection` are kept because a caller may hold either
   orientation; they absorb the transpose into `hsel` and are therefore the
   weaker pair.  Neither pair discharges the dichotomy: the kernel-checked
   route that does is `EthBridge.theorem_two`, consumed by
   `DirectOutputLower.directOutputRung`, which is exactly what non-vacuity
   witness 1 feeds into the loop.  Aux 7 and aux 8 show the families `hsel`
   quantifies over are nonempty, so `hsel` is not a vacuous hypothesis.
3. **`eq:direct-input` still has no exhibited inhabitant.**  Every statement
   here is conditional in `hNear` and `hInput` exactly as the banked steps are;
   the module adds no unconditional complexity claim, and the loop witness
   keeps `X`, `W` and both input clauses universally quantified.
4. **`lem:interlace-selector-protocol` is not invoked.**  Line 488's matching
   upper bound belongs to `BRIDGE-OUTPUT-001`; only the lower half of line 488
   is read off the loop.
-/

namespace EthInapproximability.ParameterizedNP.EntryAssembly

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.TwoCopyLadder
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutput
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.CopyRestriction
open EthInapproximability.ParameterizedNP.DefectDischarge

/-! ## Part 1: the aux-lemma battery

Eight general properties: one elementary helper, the loop invariant, the
termination measure, the rung floor, the level-schedule round trip, the fold
engine, family inhabitation, and inhabitation of the transposed carrier.  None
is about the pinned instance of Part 4.
-/

/-- **Aux 1 (helper).**  `1 ≤ 2^t` over `ℝ`, for every `t`.  Used only to see
that the rung densities `y / 2^t` stay in `(0, 1]`, which is what the bracket
side conditions of `def:bracket-ge` ask for. -/
lemma one_le_two_pow_real (t : ℕ) : (1 : ℝ) ≤ 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith

/-- **Aux 2 (the loop invariant).**  `10-direct-bridge.tex:481`, the identity
`C_W + a_t = C_W + r_Q - t` read on the additive side:

`t + a_t = r_Q`  for every rung `t ≤ 2`.

This is what makes the three rungs contribute the *same* value to the minimum
of `def:lambda`, and it is stated additively so the frozen `ℕ`-subtraction in
`a_t = r_Q - t` is never truncated.  `EntryGates.four_le_rQ` is the only input.
-/
lemma entryRungOffset (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    t + entryLevelA bout δU t = rQ bout δU := by
  have h4 := four_le_rQ bout δU
  unfold entryLevelA
  omega

/-- **Aux 3 (the termination measure).**  The level schedule of lines 421--423
strictly descends along the loop: `a_{t+1} < a_t` for every `t ≤ 2`.  Together
with the three-rung range of `def:lambda` this is the loop's termination, and
it is the reason the banked ceiling ladder applies between consecutive rungs.
-/
lemma entryLevelA_succ_lt (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    entryLevelA bout δU (t + 1) < entryLevelA bout δU t := by
  have h4 := four_le_rQ bout δU
  unfold entryLevelA
  omega

/-- **Aux 4 (every rung is nondegenerate).**  `2 ≤ a_t` for `t ≤ 2`, from
`EntryGates.four_le_rQ`.  This strengthens the banked `one_le_entryLevelA` to
exactly what the three-rung range needs: even the bottom rung sits two levels
above `0`, so no rung of the loop is the degenerate level. -/
lemma two_le_entryLevelA (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    2 ≤ entryLevelA bout δU t := by
  have h4 := four_le_rQ bout δU
  unfold entryLevelA
  omega

/-- **Aux 5 (round trip on the level schedule).**  `10-direct-bridge.tex:471`
writes `2^{a_t} θ = Q θ / 2^t`; the banked
`DirectOutputLower.entryLevel_pow_eq` states the underlying identity
`2^{a_t} = Q / 2^t`.  Multiplied out, that is

`2^{a_t} · 2^t = Q`,

the form in which the loop reads the schedule: the level halves exactly as the
column density halves, at every rung.  The banked lemma is *consumed*, never
re-derived. -/
lemma entryLevelPow_mul_eq_Qwidth (bout : ℕ) (δU : ℝ) {t : ℕ} (ht : t ≤ 2) :
    (2 : ℝ) ^ entryLevelA bout δU t * 2 ^ t = ((Qwidth bout δU : ℕ) : ℝ) := by
  rw [entryLevel_pow_eq bout δU ht]
  have h2 : ((2 : ℝ) ^ t) ≠ 0 := by positivity
  field_simp

/-- **Aux 6 (the loop engine).**  The general fold behind
`10-direct-bridge.tex:483--487`.

For an arbitrary game `f`, copy count `p`, parameters `x`, `z`, target `n` and
rung function `c`: if the loop invariant `t + c t = n` holds on `t ≤ 2` and
each rung bound `c t ≤ comp⟨f, p, x, z/2^t⟩` holds there too, then
`n ≤ Λ_f(p, x, z)`.

The range `t ∈ {0, 1, 2}` is not a choice: `def:lambda`
(`03-preliminaries.tex:224`) is a minimum of exactly three terms, at densities
`z`, `z/2`, `z/4`, and `z / 2^t` hits those three at exactly those three `t`.
Everything stays on the complexity side (`1 + comp`, `2 + comp`), so no
truncated `ℕ` subtraction is introduced. -/
lemma le_LambdaGE_of_rungs {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) (n : ℕ) (c : ℕ → ℕ)
    (hinv : ∀ t, t ≤ 2 → t + c t = n)
    (hrung : ∀ t, t ≤ 2 →
      c t ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 2 ^ t))) :
    n ≤ LambdaGE f p x z := by
  have h0 := hrung 0 (by norm_num)
  have h1 := hrung 1 (by norm_num)
  have h2 := hrung 2 (by norm_num)
  have i0 := hinv 0 (by norm_num)
  have i1 := hinv 1 (by norm_num)
  have i2 := hinv 2 (by norm_num)
  have e0 : z / 2 ^ (0 : ℕ) = z := by norm_num
  have e1 : z / 2 ^ (1 : ℕ) = z / 2 := by norm_num
  have e2 : z / 2 ^ (2 : ℕ) = z / 4 := by norm_num
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [le_LambdaGE_iff]
  exact ⟨by omega, by omega, by omega⟩

/-- **Aux 7 (family inhabitation).**  Every bracket family the loop quantifies
over is nonempty: `x_out ≤ 1` (banked `xOut_le_one`), `y / 2^t ≤ 1` for the
globally fixed `y = 3/5`, and the row carrier `Y^{[Q]}` of `R⁺` is nonempty
whenever `Y` is.

This matters twice.  `Dfamily` is an `sInf` over `ℕ`, which is `0` on the empty
family, so the rung bounds would be unprovable without it; and it shows the
selection hypothesis `hsel` of Part 3 quantifies over something, i.e. is not
vacuously satisfiable. -/
lemma entryRungFamily_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (bout : ℕ) (δU : ℝ) (hY : 1 ≤ Fintype.card Y) (t : ℕ) :
    (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
      (xOut bout) ((3 / 5) / 2 ^ t)).Nonempty := by
  classical
  have hcardrow : 1 ≤ Fintype.card (Fin (Qwidth bout δU) → Y) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.one_le_pow _ _ hY
  have h2t : (1 : ℝ) ≤ 2 ^ t := one_le_two_pow_real t
  have hz1 : ((3 : ℝ) / 5) / 2 ^ t ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  exact bracketGE.nonempty 1 (xOut bout) ((3 / 5) / 2 ^ t) (xOut_le_one bout)
    hz1 hcardrow

/-- **Aux 8 (the transposed carrier is inhabited).**  `10-direct-bridge.tex:452`
puts `V = Int_Q(W)` on carriers `Fin Q × X` (rows) and `Fin Q → Y` (columns).
The row carrier of `V` — which is the *column* carrier of `R⁺` — is nonempty
whenever `X` is, because `Q = 2^{r_Q} > 0`.  This is the nonemptiness guard the
transposed family needs, and it is stated for arbitrary `b_out`, `δ_U`. -/
lemma entryColumnCarrier_nonempty {X : Type*} [Fintype X] (bout : ℕ) (δU : ℝ)
    (hX : 1 ≤ Fintype.card X) :
    1 ≤ Fintype.card (Fin (Qwidth bout δU) × X) := by
  have hQ : 0 < Qwidth bout δU := by
    unfold Qwidth
    exact Nat.two_pow_pos _
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_pos hQ hX

/-! ## Part 2: the per-level entry step, in loop-invariant form

`10-direct-bridge.tex:479--481`.  The banked step returns `C_W + a_t`; the loop
consumes it as the invariant `C_W + r_Q ≤ t + comp`, which is the same
statement rearranged by aux 2 and is what makes the three rungs comparable.
-/

/-- **The loop body** (`10-direct-bridge.tex:465--482`, read at line 481).

At every rung `t ≤ 2`, the selected state of the entry step satisfies the loop
invariant

`C_W + r_Q ≤ t + comp(state)`,

which is the frozen `C_W + a_t = C_W + r_Q - t` with the offset moved to the
complexity side.

The banked `DefectDischarge.entryLevelStep_ofParentColumnCount` is *consumed*
with its binder list and order unchanged — this is the ceiling-guard variant,
the one a caller coming out of the bracket of line 455 actually holds, per the
inter-derivability note; the density variant is deliberately not consumed as
well.  The two clauses of `eq:direct-input` stay the explicit binders `hNear`
and `hInput`, so the statement is conditional and adds no unconditional
complexity claim. -/
theorem entryLoopStep {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2)
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    {Q : ℕ} (P : Finset (Fin Q))
    (hcard : P.card = entryCopyCount bout δU t)
    (Rstar : Finset (Fin Q × X)) (K : Finset (Fin Q → Y)) (hK : K.Nonempty)
    (hrows : IsEquipartitionedGE Rstar P
      (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)))
    (hcount : ⌈((Fintype.card Y : ℝ) ^ Q) * xOut bout⌉₊ ≤ K.card) :
    CW + rQ bout δU ≤ t + D (subgame (interlaceFun W Q) Rstar K) := by
  have hstep := entryLevelStep_ofParentColumnCount W CW bout ht hb hδ0 hδ1 hθ0
    hgate hmargin hX hY hCW hNear hInput P hcard Rstar K hK hrows hcount
  have hoff := entryRungOffset bout δU ht
  omega

/-! ## Part 3: the `t`-loop of `10-direct-bridge.tex:483--487` -/

/-- **The assembly** (`10-direct-bridge.tex:483--487`; reader navigation
`04-bridge.tex:145--147`, no reader item claimed):

"This holds for `t = 0, 1, 2`, and hence `Λ_{R⁺}(1, 2^{-b_out}, y) ≥ C_W +
r_Q`."

Candidate A of the header: the loop variable is a genuine binder, the level
schedule `a_t = r_Q - t` is carried as a function of it, and the fold is aux 6
at the rung function `t ↦ C_W + a_t`, whose loop invariant is aux 2.  The
conclusion is byte-identical to that of `DirectOutputLower.directOutputLower`;
the rung premise is abstract, and non-vacuity witness 1 discharges it from the
banked rung. -/
theorem entryDescent {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ}
    (hrung : ∀ t, t ≤ 2 →
      CW + entryLevelA bout δU t
        ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
            (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
              (xOut bout) ((3 / 5) / 2 ^ t))) :
    CW + rQ bout δU
      ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) (3 / 5) :=
  le_LambdaGE_of_rungs (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout)
    (3 / 5) (CW + rQ bout δU) (fun t => CW + entryLevelA bout δU t)
    (fun t ht => by
      have h := entryRungOffset bout δU ht
      change t + (CW + entryLevelA bout δU t) = CW + rQ bout δU
      omega)
    hrung

/-- **The complexity half of the loop's output** (`10-direct-bridge.tex:488`):
"The `t = 0` case gives `comp(R⁺) ≥ C_W + r_Q`."

The top rung bounds a nonempty family of restrictions of the one-copy interlace
of `R⁺`, so it bounds that interlace (`familyComplexity_le_ambient`), which in
turn costs no more than `R⁺` itself (`powerOfTwoInterlace_upper` at exponent
`0`).  Only the **lower** direction is read off; the matching upper bound of
line 488 belongs to `BRIDGE-OUTPUT-001` (GAP-EXPOSED 4). -/
theorem entryComplexityDescent {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ} (hY : 1 ≤ Fintype.card Y)
    (h0 : CW + entryLevelA bout δU 0
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) (3 / 5))) :
    CW + rQ bout δU ≤ D (EthBridge.Rnext W (Qwidth bout δU)) := by
  classical
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

/-- **The transposition of `10-direct-bridge.tex:452--457`, route-native.**

"Let `V = Int_Q(W)`, so that `R⁺ = ᵀV`.  Take an arbitrary member of
`B(R⁺; 1, x_out, y/2^t)` **and transpose it**."

At one copy this is an *equality* of family complexities, not merely an
inequality: the rung family of `R⁺` at `(x_out, y/2^t)` and the rung family of
`V` at `(y/2^t, x_out)` have the same `comp`.  The banked one-copy transpose
transport `EthBridge.dfamily_one_transpose` is consumed for it — the frozen
proof's own step, and the reason line 452 introduces `V` at all.  Both density
side conditions are discharged from the banked `xOut_pos`/`xOut_le_one` and
from `y/2^t ∈ (0,1]` at the globally fixed `y = 3/5`. -/
lemma entryRung_transpose {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (bout : ℕ) {δU : ℝ} (hX : 1 ≤ Fintype.card X)
    (hY : 1 ≤ Fintype.card Y) (t : ℕ) :
    Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
        (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
          (xOut bout) ((3 / 5) / 2 ^ t))
      = Dfamily (interlaceFun (interlaceFun W (Qwidth bout δU)) 1)
        (bracketGE (Fin (Qwidth bout δU) × X) (Fin (Qwidth bout δU) → Y) 1
          ((3 / 5) / 2 ^ t) (xOut bout)) := by
  classical
  have hcardV : 1 ≤ Fintype.card (Fin (Qwidth bout δU) × X) :=
    entryColumnCarrier_nonempty (X := X) bout δU hX
  have hcardR : 1 ≤ Fintype.card (Fin (Qwidth bout δU) → Y) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.one_le_pow _ _ hY
  have h2t : (1 : ℝ) ≤ 2 ^ t := one_le_two_pow_real t
  have hz0 : (0 : ℝ) < ((3 : ℝ) / 5) / 2 ^ t := by positivity
  have hz1 : ((3 : ℝ) / 5) / 2 ^ t ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  exact EthBridge.dfamily_one_transpose (interlaceFun W (Qwidth bout δU))
    hz0 hz1 (xOut_pos bout) (xOut_le_one bout) hcardV hcardR

/-- **One rung of the loop from a transposed (`V`-side) member bound**
(`10-direct-bridge.tex:452--463`).

After the transposition of `entryRung_transpose`, the rung premise of the loop
is a statement about members of the `V`-side rung family
`B(Int_Q(W); 1, y/2^t, x_out)` — which is exactly the object frozen lines
458--463 reason about ("The resulting restriction of `V` retains at least
`⌈Qmy/2^t⌉` rows in total and a column set of normalized density at least
`x_out`.  Call an outer copy good if ...").  So the orientation flip of line
457 is performed here in the route, not inside a vendored term.

The nonemptiness guard of `EthBridge.le_Dfamily` is discharged from
`NPCC.bracketGE.nonempty` on the `V` side, so the premise is not vacuous. -/
theorem entryRung_ofTransposedMembers {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU : ℝ} {t : ℕ}
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hmem : ∀ M ∈ bracketGE (Fin (Qwidth bout δU) × X)
        (Fin (Qwidth bout δU) → Y) 1 ((3 / 5) / 2 ^ t) (xOut bout),
      CW + entryLevelA bout δU t
        ≤ D (subgame (interlaceFun (interlaceFun W (Qwidth bout δU)) 1)
            M.1 M.2)) :
    CW + entryLevelA bout δU t
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 / 5) / 2 ^ t)) := by
  classical
  have hcardV : 1 ≤ Fintype.card (Fin (Qwidth bout δU) × X) :=
    entryColumnCarrier_nonempty (X := X) bout δU hX
  have h2t : (1 : ℝ) ≤ 2 ^ t := one_le_two_pow_real t
  have hz1 : ((3 : ℝ) / 5) / 2 ^ t ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  rw [entryRung_transpose W bout hX hY t]
  exact EthBridge.le_Dfamily _ _ _
    (bracketGE.nonempty 1 ((3 : ℝ) / 5 / 2 ^ t) (xOut bout) hz1
      (xOut_le_one bout) hcardV) hmem

/-- **One rung of the loop from the good-copy selection, taken on the `V` side**
(`10-direct-bridge.tex:452--482`, with line 457 discharged).

This is the sharper of the module's two selection forms.  The transposition of
line 457 is *performed* by `entryRung_transpose`, so the selection hypothesis
`hsel` here is stated where frozen lines 458--463 actually state it — about a
member of the `V`-side rung family `B(Int_Q(W); 1, y/2^t, x_out)`, i.e. about a
restriction of `Int_Q(W)` itself.  What remains hypothetical is exactly the
good-copy dichotomy of lines 459--463 and the projection of lines 465--469,
and nothing else (GAP-EXPOSED 2).

Everything downstream of the selection is route-native: the selected state is
handed to `DefectDischarge.entryLevelStep_ofParentColumnCount` with its binder
list and order unchanged, which is the ceiling-guard variant the bracket of
lines 453--455 actually supplies. -/
theorem entryRung_ofVSideSelection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2)
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    (hsel : ∀ M ∈ bracketGE (Fin (Qwidth bout δU) × X)
        (Fin (Qwidth bout δU) → Y) 1 ((3 / 5) / 2 ^ t) (xOut bout),
      ∃ (P : Finset (Fin (Qwidth bout δU)))
        (Rstar : Finset (Fin (Qwidth bout δU) × X))
        (K : Finset (Fin (Qwidth bout δU) → Y)),
        P.card = entryCopyCount bout δU t ∧
        K.Nonempty ∧
        IsEquipartitionedGE Rstar P
          (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)) ∧
        ⌈((Fintype.card Y : ℝ) ^ (Qwidth bout δU)) * xOut bout⌉₊ ≤ K.card ∧
        D (subgame (interlaceFun W (Qwidth bout δU)) Rstar K)
          ≤ D (subgame
              (interlaceFun (interlaceFun W (Qwidth bout δU)) 1) M.1 M.2)) :
    CW + entryLevelA bout δU t
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 / 5) / 2 ^ t)) := by
  classical
  refine entryRung_ofTransposedMembers W CW bout hX hY ?_
  intro M hM
  obtain ⟨P, Rstar, K, hcard, hK, hrows, hcount, hle⟩ := hsel M hM
  exact le_trans
    (entryLevelStep_ofParentColumnCount W CW bout ht hb hδ0 hδ1 hθ0 hgate
      hmargin hX hY hCW hNear hInput P hcard Rstar K hK hrows hcount)
    hle

/-- **One rung of the loop from the good-copy selection**
(`10-direct-bridge.tex:452--482`).

Frozen lines 453--455 take "an arbitrary member of `B(R⁺; 1, x_out, y/2^t)`";
lines 456--469 transpose it, count good copies, and project.  That geometric
selection is carried here as the **named hypothesis** `hsel` (GAP-EXPOSED 2):
for every member of the rung family it produces a coordinate set of exactly
`p_t` copies, a nonempty column carrier meeting the inherited ceiling guard at
`x_out`, a row set meeting the floor `A_{a_t}`, and the fact that the resulting
selected state is no more expensive than the member.

Given that, the rung bound follows from the loop body of Part 2 and
`EthBridge.le_Dfamily`, whose nonemptiness side condition is aux 7 — so `hsel`
is a genuine universal statement, not a vacuous one.  Inside `hsel` the trivial
selection is excluded: `K = ∅` fails `K.Nonempty` and fails the ceiling guard
(`⌈|Y|^Q x_out⌉ ≥ 1`), and `P = ∅` fails `P.card = p_t` because
`p_t > 2^{a_t - 1} ≥ 2`. -/
theorem entryRung_ofSelection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2)
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    (hsel : ∀ M ∈ bracketGE (Fin (Qwidth bout δU) → Y)
        (Fin (Qwidth bout δU) × X) 1 (xOut bout) ((3 / 5) / 2 ^ t),
      ∃ (P : Finset (Fin (Qwidth bout δU)))
        (Rstar : Finset (Fin (Qwidth bout δU) × X))
        (K : Finset (Fin (Qwidth bout δU) → Y)),
        P.card = entryCopyCount bout δU t ∧
        K.Nonempty ∧
        IsEquipartitionedGE Rstar P
          (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)) ∧
        ⌈((Fintype.card Y : ℝ) ^ (Qwidth bout δU)) * xOut bout⌉₊ ≤ K.card ∧
        D (subgame (interlaceFun W (Qwidth bout δU)) Rstar K)
          ≤ D (subgame
              (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1) M.1 M.2)) :
    CW + entryLevelA bout δU t
      ≤ Dfamily (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
          (bracketGE (Fin (Qwidth bout δU) → Y) (Fin (Qwidth bout δU) × X) 1
            (xOut bout) ((3 / 5) / 2 ^ t)) := by
  classical
  refine EthBridge.le_Dfamily _ _ _
    (entryRungFamily_nonempty (X := X) bout δU hY t) ?_
  intro M hM
  obtain ⟨P, Rstar, K, hcard, hK, hrows, hcount, hle⟩ := hsel M hM
  exact le_trans
    (entryLevelStep_ofParentColumnCount W CW bout ht hb hδ0 hδ1 hθ0 hgate
      hmargin hX hY hCW hNear hInput P hcard Rstar K hK hrows hcount)
    hle

/-- **The full loop: per-level entry steps assembled into the descent**
(`10-direct-bridge.tex:452--487`).

The composition of `entryRung_ofSelection` over the loop range with
`entryDescent`.  This is the module's principal statement: with the good-copy
selection of lines 456--469 available at every rung — as an explicit named
hypothesis, never as an axiom — the per-level entry step of
`BRIDGE-DISCHARGE-001` assembles into the three-rung output estimate.

All conditional content is on the premise side; the conclusion is
byte-identical to that of `DirectOutputLower.directOutputLower`. -/
theorem entryAssembly_ofSelection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    (hsel : ∀ t, t ≤ 2 →
      ∀ M ∈ bracketGE (Fin (Qwidth bout δU) → Y)
          (Fin (Qwidth bout δU) × X) 1 (xOut bout) ((3 / 5) / 2 ^ t),
        ∃ (P : Finset (Fin (Qwidth bout δU)))
          (Rstar : Finset (Fin (Qwidth bout δU) × X))
          (K : Finset (Fin (Qwidth bout δU) → Y)),
          P.card = entryCopyCount bout δU t ∧
          K.Nonempty ∧
          IsEquipartitionedGE Rstar P
            (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)) ∧
          ⌈((Fintype.card Y : ℝ) ^ (Qwidth bout δU)) * xOut bout⌉₊ ≤ K.card ∧
          D (subgame (interlaceFun W (Qwidth bout δU)) Rstar K)
            ≤ D (subgame
                (interlaceFun (EthBridge.Rnext W (Qwidth bout δU)) 1)
                M.1 M.2)) :
    CW + rQ bout δU
      ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) (3 / 5) :=
  entryDescent W CW bout (fun t ht =>
    entryRung_ofSelection W CW bout ht hb hδ0 hδ1 hθ0 hgate hmargin hX hY hCW
      hNear hInput (hsel t ht))

/-- **The full loop over the `V`-side selection**
(`10-direct-bridge.tex:452--487`, with line 457 discharged).

The sharper counterpart of `entryAssembly_ofSelection`: `entryDescent` folded
over `entryRung_ofVSideSelection`.  Its conclusion is byte-identical to that of
`DirectOutputLower.directOutputLower`; its only hypothetical content beyond the
frozen `eq:direct-input` binders is the good-copy dichotomy and projection of
lines 459--469, taken on the matrix `Int_Q(W)` that those lines are about. -/
theorem entryAssembly_ofVSideSelection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5))
    (hsel : ∀ t, t ≤ 2 →
      ∀ M ∈ bracketGE (Fin (Qwidth bout δU) × X)
          (Fin (Qwidth bout δU) → Y) 1 ((3 / 5) / 2 ^ t) (xOut bout),
        ∃ (P : Finset (Fin (Qwidth bout δU)))
          (Rstar : Finset (Fin (Qwidth bout δU) × X))
          (K : Finset (Fin (Qwidth bout δU) → Y)),
          P.card = entryCopyCount bout δU t ∧
          K.Nonempty ∧
          IsEquipartitionedGE Rstar P
            (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)) ∧
          ⌈((Fintype.card Y : ℝ) ^ (Qwidth bout δU)) * xOut bout⌉₊ ≤ K.card ∧
          D (subgame (interlaceFun W (Qwidth bout δU)) Rstar K)
            ≤ D (subgame
                (interlaceFun (interlaceFun W (Qwidth bout δU)) 1)
                M.1 M.2)) :
    CW + rQ bout δU
      ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) (3 / 5) :=
  entryDescent W CW bout (fun t ht =>
    entryRung_ofVSideSelection W CW bout ht hb hδ0 hδ1 hθ0 hgate hmargin hX hY
      hCW hNear hInput (hsel t ht))

/-! ## Part 4: non-vacuity and the statement poles

LANE-GATE 3.  Five witnesses.  Nothing here asserts that an inhabitant of
`eq:direct-input` exists — it cannot, until Stages 1--4 land (GAP-EXPOSED 3).
-/

/-- **Non-vacuity witness 1: the loop premise is satisfiable with real
content, and the loop reproduces the frozen conclusion.**

The abstract rung premise of `entryDescent` is discharged, at every rung of the
loop range, by the banked `DirectOutputLower.directOutputRung` under exactly
the frozen `eq:direct-input` binders.  So the loop is not an empty container:
fed the route's own rungs it returns the second equation of `eq:direct-output`.

`X`, `Y`, `W` stay universally quantified and both input clauses stay
hypotheses. -/
theorem entryDescent_fires_via_bankedRungs {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
    (hgate : 4 * Q0 bout δU * θ ≤ deltaFixed)
    (hmargin : 3 * lambdaU δU + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ (3 / 5)) :
    CW + rQ bout δU
      ≤ LambdaGE (EthBridge.Rnext W (Qwidth bout δU)) 1 (xOut bout) (3 / 5) :=
  entryDescent W CW bout (fun _t ht =>
    directOutputRung W CW bout ht hb hδ0 hδ1 hθ0 hgate hmargin hX hY hCW hNear
      hInput)

/-- **Non-vacuity witness 2: the loop runs at two genuine levels.**

At the banked first entry-gate parameters `b_out = 1`, `δ_U = 1/60`,
`θ = 1/192000`, `C_W = 3` — where `Q = 8192` and `r_Q = 13` — the loop body of
Part 2 is exercised at **two different rungs**, `t = 0` and `t = 1`, with
everything that distinguishes them exhibited rather than quantified:

* two different levels, `a_0 = 13` and `a_1 = 12`;
* two different copy counts, `p_1 < p_0`, both strictly between `2048` and the
  outer width, so both coordinate sets are **proper** subsets of `[Q]` and
  neither is empty;
* one exhibited **proper**, nonempty parent column carrier `K` of normalized
  density exactly `x_out = 1/2`, meeting the inherited ceiling guard with no
  slack;
* the loop invariant firing at both rungs at the *same* target
  `C_W + r_Q = 16`, with the offsets `0` and `1` in place.

A degenerate inhabitant would read `P = ∅`, `P = [Q]`, `K = Y^{[Q]}` (density
`1`, guard free) or a single rung.  This witness reads none of these.  `X`,
`W`, and the row sets stay universally quantified and both clauses of
`eq:direct-input` stay hypotheses; `Y` is pinned to `Bool` only because a
carrier must be exhibited. -/
theorem entryLoop_fires_two_levels {X : Type*} [Fintype X]
    (W : X → Bool → Bool) (hX : 1 ≤ Fintype.card X)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Bool 1 (1 / 192000) (1 - 1 / 60)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 192000) (3 / 5)) :
    ∃ (P₀ P₁ : Finset (Fin (Qwidth 1 (1 / 60))))
      (K : Finset (Fin (Qwidth 1 (1 / 60)) → Bool)),
      entryLevelA 1 (1 / 60) 0 = 13
      ∧ entryLevelA 1 (1 / 60) 1 = 12
      ∧ P₀.card = entryCopyCount 1 (1 / 60) 0
      ∧ P₁.card = entryCopyCount 1 (1 / 60) 1
      ∧ 2048 < P₁.card
      ∧ P₁.card < P₀.card
      ∧ P₀ ⊂ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60))))
      ∧ P₁ ⊂ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60))))
      ∧ K ⊂ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60)) → Bool))
      ∧ K.Nonempty
      ∧ columnDensity K = 1 / 2
      ∧ ⌈((Fintype.card Bool : ℝ) ^ (Qwidth 1 (1 / 60))) * xOut 1⌉₊ ≤ K.card
      ∧ (∀ Rstar : Finset (Fin (Qwidth 1 (1 / 60)) × X),
          IsEquipartitionedGE Rstar P₀
            (rowFloor (Fintype.card X) (1 / 192000)
              (entryLevelA 1 (1 / 60) 0)) →
          (3 : ℕ) + rQ 1 (1 / 60)
            ≤ 0 + D (subgame (interlaceFun W (Qwidth 1 (1 / 60))) Rstar K))
      ∧ (∀ Rstar : Finset (Fin (Qwidth 1 (1 / 60)) × X),
          IsEquipartitionedGE Rstar P₁
            (rowFloor (Fintype.card X) (1 / 192000)
              (entryLevelA 1 (1 / 60) 1)) →
          (3 : ℕ) + rQ 1 (1 / 60)
            ≤ 1 + D (subgame (interlaceFun W (Qwidth 1 (1 / 60))) Rstar K)) := by
  classical
  obtain ⟨-, -, -, hQ8192, -, -, -⟩ := directEntryGates_fires
  obtain ⟨hd1, hd2⟩ := entryCount_fires_first_witness
  obtain ⟨ha0, ha1, -, -, -, -⟩ := entryLevels_fire_first_witness
  have hY : 1 ≤ Fintype.card Bool := by decide
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 60) (le_refl (1 / 60 : ℝ))
  have hp0 : entryCopyCount 1 (1 / 60) 0
      = 2 ^ (entryLevelA 1 (1 / 60) 0 - 1) + entryCount 1 (1 / 60) := rfl
  have hp1 : entryCopyCount 1 (1 / 60) 1
      = 2 ^ (entryLevelA 1 (1 / 60) 1 - 1) + entryCount 1 (1 / 60) := rfl
  rw [ha0] at hp0
  rw [ha1] at hp1
  norm_num at hp0 hp1
  have hcardle0 : entryCopyCount 1 (1 / 60) 0
      ≤ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60)))).card := by
    rw [Finset.card_univ, Fintype.card_fin, hQ8192]
    omega
  have hcardle1 : entryCopyCount 1 (1 / 60) 1
      ≤ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60)))).card := by
    rw [Finset.card_univ, Fintype.card_fin, hQ8192]
    omega
  obtain ⟨P₀, -, hP0card⟩ := Finset.exists_subset_card_eq hcardle0
  obtain ⟨P₁, -, hP1card⟩ := Finset.exists_subset_card_eq hcardle1
  obtain ⟨K, hKne, hKss, hKdens, hKdef⟩ :=
    exists_proper_halfDensity_cols (Qwidth 1 (1 / 60))
      (by rw [hQ8192]; norm_num)
  have hdensity : xOut 1 ≤ columnDensity K := by
    rw [hKdens]
    unfold xOut
    norm_num
  have hcount : ⌈((Fintype.card Bool : ℝ) ^ (Qwidth 1 (1 / 60))) * xOut 1⌉₊
      ≤ K.card := (le_columnDensity_iff_ceil_le_card K (xOut 1) hY).mp hdensity
  refine ⟨P₀, P₁, K, ha0, ha1, hP0card, hP1card, ?_, ?_, ?_, ?_, hKss, hKne,
    hKdens, hcount, ?_, ?_⟩
  · rw [hP1card, hp1]
    omega
  · rw [hP0card, hP1card, hp0, hp1]
    omega
  · refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    rw [hEq, Finset.card_univ, Fintype.card_fin, hQ8192] at hP0card
    omega
  · refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    rw [hEq, Finset.card_univ, Fintype.card_fin, hQ8192] at hP1card
    omega
  · intro Rstar hrows
    exact entryLoopStep W 3 1 (δU := 1 / 60) (θ := 1 / 192000) (t := 0)
      (by norm_num) (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
      hgate hmargin hX hY (le_refl 3) hNear hInput P₀ hP0card Rstar K hKne
      hrows hcount
  · intro Rstar hrows
    exact entryLoopStep W 3 1 (δU := 1 / 60) (θ := 1 / 192000) (t := 1)
      (by norm_num) (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
      hgate hmargin hX hY (le_refl 3) hNear hInput P₁ hP1card Rstar K hKne
      hrows hcount

/-- **Non-vacuity witness 3: the level schedule is exercised at all three
rungs, and reads the same width every time.**

`10-direct-bridge.tex:471` at the carried witness: `2^{13}·2^0 = 2^{12}·2^1 =
2^{11}·2^2 = 8192 = Q`.  So aux 5 is not a formality at one level — the
schedule genuinely moves down the loop while the product stays pinned to the
outer width. -/
theorem entryLevelSchedule_fires_first_witness :
    (2 : ℝ) ^ entryLevelA 1 (1 / 60) 0 * 2 ^ (0 : ℕ) = 8192
      ∧ (2 : ℝ) ^ entryLevelA 1 (1 / 60) 1 * 2 ^ (1 : ℕ) = 8192
      ∧ (2 : ℝ) ^ entryLevelA 1 (1 / 60) 2 * 2 ^ (2 : ℕ) = 8192 := by
  obtain ⟨-, -, -, hQ, -, -, -⟩ := directEntryGates_fires
  refine ⟨?_, ?_, ?_⟩
  · rw [entryLevelPow_mul_eq_Qwidth 1 (1 / 60) (by norm_num : (0 : ℕ) ≤ 2), hQ]
    norm_num
  · rw [entryLevelPow_mul_eq_Qwidth 1 (1 / 60) (by norm_num : (1 : ℕ) ≤ 2), hQ]
    norm_num
  · rw [entryLevelPow_mul_eq_Qwidth 1 (1 / 60) (by norm_num : (2 : ℕ) ≤ 2), hQ]
    norm_num

/-- **Non-vacuity witness 4: the rung offsets are load-bearing.**

A "flat" mis-encoding of the loop — one that used the top level `r_Q` at every
rung — is refuted in general, for every `b_out` and `δ_U`: the schedule of line
423 strictly descends (aux 3), so `a_1 ≠ r_Q`.  Hence the three rungs of
`entryDescent` are genuinely three different bounds folded by three different
offsets, and a green build of the loop is not a green build of a constant. -/
theorem entryLoop_flat_schedule_refuted (bout : ℕ) (δU : ℝ) :
    ¬ (∀ t, t ≤ 2 → entryLevelA bout δU t = rQ bout δU) := by
  intro h
  have h4 := four_le_rQ bout δU
  have h1 := h 1 (by norm_num)
  unfold entryLevelA at h1
  omega

/-- **Non-vacuity witness 5: the loop's conclusion is not a formality.**

`C_W ≥ 3` and `r_Q ≥ 4` force `C_W + r_Q ≥ 7`, so the assembled bound is a
seven-bit statement at minimum, for every legal parameter choice, and never the
vacuous `0 ≤ Λ`.  The nonemptiness of every rung family (aux 7) is what stops
`Dfamily`'s `sInf` from collapsing to `0` and making the rung premises free. -/
theorem entryDescent_conclusion_nontrivial {CW bout : ℕ} {δU : ℝ}
    (hCW : 3 ≤ CW) : 7 ≤ CW + rQ bout δU := by
  have h4 := four_le_rQ bout δU
  omega

end EthInapproximability.ParameterizedNP.EntryAssembly
