import EthInapproximability.ParameterizedNP.CopyRestriction

/-!
# Parameterized NP route: discharging the entry-step defect binder

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-DISCHARGE-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1l` tranche to close **GAP-EXPOSED 1** of `BRIDGE-COPYREST-001`:
"Composing the frozen chain — parent density to projected defect to
`entryLevelStep` — remains the separate obligation and is not claimed here."

This module claims exactly that composition and nothing else.  It introduces
**no new definition**: every quantity it names (`columnDensity`,
`columnDefect`, `copyCols`, `xOut`, `entryDefectL`, `entryLevelA`,
`entryCopyCount`, `rowFloor`) is already banked, and the module is pure wiring
plus the general density facts the wiring needs.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`, `sec:direct-entry` (label line 390):
  * lines 392--396, the entry parameters
    `x_out = 2^{-b_out}` and `L = ln(1/x_out) = b_out ln 2` — already banked as
    `DirectOutputLower.xOut` and `DirectOutputLower.entryDefectL`; this module
    consumes them and defines neither a second time;
  * lines 453--459, the transposed bracket member: the restriction of
    `V = Int_Q(W)` "retains at least `⌈Q m y / 2^t⌉` rows in total and **a
    column set of normalized density at least `x_out`**".  That sentence is the
    origin of this module's parent hypothesis: the parent column carrier `K`
    enters the entry step carrying a *density floor*, not a defect bound;
  * **lines 465--467**, the discharged step, quoted in full:
    "Choose any `p_t` good copies and project the column set to them.  Its
    normalized density remains at least `x_out`, so its defect is at most
    `L`.";
  * lines 467--469, "By `lem:copy-restriction`, the exact projected image and
    the rows from these good copies form a literal restriction of
    `Int_{p_t}(W)` inside the selected state" — the identification of the
    column set of lines 465--467 with the **exact image** `K_P`, banked as
    `BRIDGE-COPYREST-001`'s `copyCols`;
  * lines 470--482, the legality of the row level and
    `L ≤ dλ = c_{a_t}(p_t)λ`, feeding `lem:defect-induction` — banked as
    `BRIDGE-OUTPUT-002`'s `entryLevelStep` and consumed here through
    `BRIDGE-COPYREST-001`'s `entryLevelStep_ofCopyRestriction`.
* `sections/D-inherited-contracts.tex`:
  * lines 250--265, the checked inherited declaration
    `NPCC.coord_projection`: its column guard is the **ceiling** form
    `⌈|Y|^p z⌉ ≤ |C|` (line 258) and its conclusion places the returned pair in
    the `r`-copy bracket at `(x, z)`, i.e. it *preserves the density parameter
    `z`*.  That is the inherited "density preservation" the entry step cites;
    it is transcribed here in defect form as `coordProjection_columnDefect_le`,
    and the reason it cannot itself discharge the binder is recorded under
    GAP-EXPOSED 1 below;
  * lines 229--248, `eq:contract-defect-projection`
    (`Def(C') ≤ (ℓ/p) Def(C)`), the entropy-averaging strengthening, banked as
    `INHERIT-001`'s `defectProjection`.  **It is not used here**, and
    TRACE-FINDING 1 below records why the frozen step at lines 465--467 does
    not need it.
* `conv:finite-slots` (`sections/03-preliminaries.tex`) — zero-based finite
  slots; the coordinate carriers are `Fin Q` and `Fin p_t`, exactly as in
  `FiniteSlots.lean` and `CopyRestriction.lean`.

## Reader counterpart

The reader artifact of the same frozen release,
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/reader-facing`,
was opened first-hand before this section was written.

**No reader item is claimed by this module**, and that is deliberate: every
reader item that states any part of the composed chain is already assigned to
another declaration, and assigning one twice is forbidden.

* `sections/B-bridge-details.tex` §"Defect and projection", lines 13--38, is
  named at section level for `INHERIT-001`'s `coordProjection` in
  `READER_CROSSWALK.md`, **narrowed** by `BRIDGE-COPYREST-001` to exclude lines
  29--32, which are assigned to `copyRestriction`.  Line 18 ("Projection to a
  specified coordinate set does not increase defect.") and lines 19--20 (the
  entropy-averaging strengthening) therefore stay where the crosswalk already
  puts them; this module does not reassign them.
* `sections/B-bridge-details.tex` line 174 (`L = b^+ ln 2`),
  `eq:appendix-Q-bounds`, the definition display at lines 185--192, and
  `lem:bridge-good-block-count` are the four items assigned to
  `BRIDGE-OUTPUT-002`; the parameters `xOut` and `entryDefectL` consumed here
  are that row's, not this one's.
* The reader's own account of this very step, `B-bridge-details.tex` lines
  227--233 ("Keep `p_t` good copies and project the column set to them.  Its
  defect is at most `L` ..."), is **proof prose inside an unnumbered
  paragraph**, and `BRIDGE-OUTPUT-002` already recorded it as prose that is not
  cited as a statement.  It is named here as the reader's navigation locus for
  what this module proves, and it is *not* claimed as a reader counterpart.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge" (the row that
already carries `INHERIT-001`, `BRIDGE-COPYREST-001` and `BRIDGE-OUTPUT-002`).

## Dependencies, imports, external adapters

* Import: `EthInapproximability.ParameterizedNP.CopyRestriction` only (which
  transitively carries `DirectOutputLower`, `EntryGates`, `DefectInduction`,
  `InheritedContracts` and `Prelude`).  `LegacyNPCC.Stage12` is **not** reached,
  so the AGHP balanced-family axiom is not in this module's closure.
* Consumed, never re-proved: `CopyRestriction.copyCols`,
  `CopyRestriction.copyCols_nonempty`,
  `CopyRestriction.card_le_card_copyCols_mul`,
  `CopyRestriction.entryLevelStep_ofCopyRestriction`,
  `InheritedContracts.columnDensity`, `.columnDefect`,
  `.columnDensity_le_one`, `.coordProjection`, `.bracketGE_cols_nonempty`,
  `DefectInduction.columnDefect_le_iff_density`, `DirectOutputLower.xOut`,
  `.entryDefectL`, `.xOut_pos`, `.xOut_eq_exp`, `.entryLevelA`,
  `.entryCopyCount`, `.entryCopyCount_fires_first_witness`,
  `EntryGates.Q0`, `.Qwidth`, `.deltaFixed`, `.Q0_eq_route`,
  `.secondEntryGate_of_deltaU_small`.
* External theorem adapters: **none new**.  The only external interfaces in the
  closure are the ones the consumed declarations already carry
  (`EthBridge.state_defect_iff_density` behind
  `columnDefect_le_iff_density`, `NPCC.coord_projection` behind
  `coordProjection`, and the `BRIDGE-OUTPUT-002` chain behind
  `entryLevelStep`).  The cited expander family `EXPANDER-001` is not touched.
* Proof status: **new** (adapted wiring).  The six aux lemmas and the two
  discharge theorems are proved here; every declaration they call is inherited
  or previously landed.

## Axiom surface (`#print axioms`, all thirteen declarations)

Every declaration of this module was audited after the green build.  All
thirteen — the seven aux lemmas, `coordProjection_columnDefect_le`, the two
discharge theorems, and the three non-vacuity witnesses — report exactly

```text
[propext, Classical.choice, Quot.sound]
```

No project axiom, no placeholder tactic, no opaque certificate, and in
particular **not** the AGHP balanced-family axiom: `LegacyNPCC.Stage12` is
outside this module's import closure.

## Candidate encodings (k = 2) and the ranking

The concept is a *wiring*, so the two candidates differ only in the shape of
the parent hypothesis that replaces the frozen defect binder.

**Candidate A — the paper's own words: a normalized-density floor.**
`hdensity : xOut bout ≤ columnDensity K`.  This is literally
"a column set of normalized density at least `x_out`" (line 458--459) and
"Its normalized density remains at least `x_out`" (line 466).

**Candidate B — the inherited contract's guard: a ceiling on the count.**
`hcount : ⌈(|Y| : ℝ)^Q * xOut bout⌉₊ ≤ K.card`.  This is literally the column
guard `⌈|Y|^p z⌉ ≤ |C|` of `D-inherited-contracts.tex:258`, at `z = x_out`.
It is also, verbatim, what the frozen bracket at line 455 imposes: the member
of `B(R+; 1, x_out, y/2^t)` carries `x_out` as its **row** density parameter,
and `R+ = Int_Q(W)^T` has row type `Y^{[Q]}`, so after the transposition of
line 457 the surviving column set of `Int_Q(W)` satisfies exactly
`⌈|Y|^Q x_out⌉ ≤ |K|`.  Candidate B is therefore the shape a caller coming
out of `bracketGE` actually holds.

Both were written out and both are landed, because the two consumption shapes
are genuinely different: a caller holding a bracket membership has B, and a
caller reading line 458 has A.  `le_columnDensity_iff_ceil_le_card` (Aux 2)
proves they are *equivalent* whenever `1 ≤ |Y|`, so neither is a weakening of
the other and no third statement is needed.

Ranking (aux lemmas proved, faithfulness, length): A = 6/6 aux lemmas, the
frozen sentence verbatim, and the shorter statement; B = 6/6, the inherited
guard verbatim, one `Nat.ceil` heavier.  **A is landed as the primary**
(`entryLevelStep_ofParentDensity`) and B as the named bridge to the inherited
guard (`entryLevelStep_ofParentColumnCount`), proved *from* A so that only one
statement carries content.

## Aux-lemma battery (7, all general, all proved)

None of the seven is about the pinned instance; each quantifies over arbitrary
`p`, `k`, `P`, `K`, `Y`, `Q` (and, where it appears, an arbitrary budget `L`).

1. `columnDensity_le_copyCols` — **the density-preservation core**:
   `y_K ≤ y_{K_P}` for every coordinate set.  Monotonicity property.
2. `le_columnDensity_iff_ceil_le_card` — **round trip** between the density
   floor and the inherited ceiling guard.
3. `columnDefect_le_iff_exp_le_columnDensity` — **identity**: the defect budget
   `Def(K) ≤ L` is the density floor `e^{-L} ≤ y_K`.
4. `columnDefect_copyCols_le_of_le_columnDensity` — **composition** of 1 and 3
   at an arbitrary budget: the general engine of the discharge.
5. `columnDensity_univ` — **calibration**: the full carrier reads density `1`,
   pairing with the banked `columnDefect_univ = 0`.  This is what makes the
   degenerate witness visible, and hence excluded, in Part 4.
6. `columnDefect_le_entryDefectL_iff` — the **frozen conversion** of line 396,
   `Def(K) ≤ L ⟺ x_out ≤ y_K`, obtained from 3 and the banked `xOut_eq_exp`.
7. `exists_proper_halfDensity_cols` — **inhabitation**: at *every* width
   `Q ≥ 1` there is a proper, nonempty column carrier of density exactly `1/2`
   and defect exactly `ln 2`.  Existence property, stated for arbitrary `Q`;
   it is what lets witness 3 exhibit its parent carrier at the entry-gate
   width instead of quantifying over it.

## Faithfulness notes (mechanical rules M1--M10)

* **No new definition, no structure, no premise bundle.**  Every hypothesis of
  both discharge theorems is an explicit binder, in the binder order of
  `entryLevelStep_ofCopyRestriction`, with the single defect binder `hdefect`
  replaced in place by the parent hypothesis.  Nothing is reordered, added, or
  dropped.  Since there is no constructor anywhere in the module, no complexity
  or robustness conclusion can sit in constructor data.
* **Nothing is weakened.**  The conclusion is byte-identical to the conclusion
  of `entryLevelStep_ofCopyRestriction`:
  `CW + entryLevelA bout δU t ≤ D (subgame (interlaceFun W Q) Rstar K)`.  The
  parent hypothesis is *stronger* than the discharged binder in the sense that
  matters — it implies it (Aux 4) — so the composed theorem is a corollary and
  never a relaxation.
* **Both interlace widths.**  Only the outer width `Q` and the copy count
  `p_t = entryCopyCount bout δU t` occur, linked solely by
  `hcard : P.card = entryCopyCount bout δU t`, exactly as in
  `BRIDGE-COPYREST-001`.  The scale-alignment width `q` does not appear and is
  not conflated with either.
* **Ceilings are preserved, not smoothed.**  Candidate B keeps `Nat.ceil` where
  the inherited guard puts it; `rowFloor` is consumed unchanged; the row floor
  `A_{a_t}` is never re-derived.
* **Nonemptiness is carried.**  `hK : K.Nonempty` stays an explicit binder, and
  `copyCols_nonempty` propagates it to `K_P`; Aux 3 and Aux 4 both carry it,
  because at `K = ∅` the readout `ln(n^k/|K|)` degenerates.
* **Finite carriers.**  `Fin Q`, `Fin p_t`, `Finset (Fin Q → Y)`; zero-based,
  per `conv:finite-slots`.
* **Trivial-witness pole.**  The two discharge theorems are **not**
  existentials — they are named-def claims about the caller's own `Rstar` and
  `K` — so there is no trivial witness to exclude.  The one existential
  deliverable in the module is `coordProjection_columnDefect_le`, and the
  trivial witness fails it in one line: the empty column carrier `RC'.2 = ∅`
  satisfies the two provenance clauses vacuously but is refuted by the
  conjunct `RC'.2.Nonempty`, which is forced (not assumed) because
  `⌈|Y|^r x_out⌉₊ ≥ 1` whenever `1 ≤ |Y|` and `x_out > 0`; and the *singleton*
  carrier is refuted by the bracket conjunct itself, whose count floor
  `⌈|Y|^r x_out⌉₊` exceeds `1` as soon as `|Y|^r x_out > 1`.
  `defectDischarge_fires_first_witness` is existential only in the coordinate
  set `P`, where the trivial witness `P = univ` is excluded by the explicit
  conjunct `P ⊂ univ`.
* **Vacuous-hypothesis pole.**  Part 4 discharges every binder of the
  composition at legal frozen parameters, and Part 3 exhibits the density
  transport at a *proper* instance with **both** defects strictly positive.

## GAP-EXPOSED (nothing is weakened to close these)

1. **`coordProjection` cannot discharge the binder, and is not used to.**  Its
   conclusion is existential: it returns *some* bracket member `RC'` whose
   column carrier meets the count floor.  The entry step needs the floor for
   the **exact image** `K_P = copyCols P hcard K`, which `lem:copy-restriction`
   pins and which `coordProjection` never mentions — precisely the substitution
   `D-inherited-contracts.tex:275--276` forbids.  So
   `coordProjection_columnDefect_le` transcribes the inherited density
   preservation in defect form and is recorded as the traced statement of the
   cited route, while the actual discharge runs through Aux 1, which is a
   statement about `K_P` itself.
2. **The entropy-averaging bound is still not claimed.**  `INHERIT-001`'s
   `defectProjection` (`Def(C') ≤ (ℓ/p) Def(C)`) is strictly stronger than
   Aux 1 and is not proved, re-proved, or consumed here.  See TRACE-FINDING 1
   for why the frozen step does not need it.
3. **`eq:direct-input` still has no exhibited inhabitant.**  Both discharge
   theorems are conditional exactly as `entryLevelStep` is; the module adds no
   unconditional complexity claim, and `defectDischarge_fires_first_witness`
   keeps `X`, `Y`, `W` and the two input clauses universally quantified.
4. **The good-copy *selection* is not rewired.**  Frozen lines 459--463 choose
   the `p_t` good copies by the row-count criterion of
   `eq:direct-good-copy-count`; that counting argument is `BRIDGE-OUTPUT-002`'s
   `entryGoodCopyCount` and is not re-derived here.  This module takes the
   selected `P` as a binder, as `entryLevelStep_ofCopyRestriction` does.

## TRACE-FINDING 1 (recorded, not acted on beyond this module)

`BRIDGE-COPYREST-001`'s GAP-EXPOSED 1 attributes the frozen step at lines
465--467 to "`NPCC.coord_projection`'s density-preservation for a *well-chosen*
coordinate set (reader `B-bridge-details.tex:18--21`, entropy averaging, defect
at most `(p'/p)Δ_p(K)`)".  Reading the frozen sentence at the anchor shows the
attribution is stronger than the step requires, in two independent ways.

* The coordinate set at lines 465--466 is **not** chosen for density: it is
  "any `p_t` good copies", where "good" is the *row*-count criterion of lines
  459--460.  A density-optimal choice is unavailable to the argument at that
  point, so the step cannot be relying on one.
* What the sentence asserts is that the density floor `x_out` is *preserved*,
  not that the defect is *scaled*.  Preservation of a floor under exact-image
  projection is the elementary counting fact `|K| ≤ |K_P| · n^{p-p'}` already
  banked as `card_le_card_copyCols_mul`, and it holds for **every** coordinate
  set — which is exactly what the reader states separately at
  `B-bridge-details.tex:18` ("Projection to a specified coordinate set does not
  increase defect."), one sentence *before* the entropy-averaging strengthening
  at lines 19--20.

Both presentations therefore separate the two facts in the same way, and the
entry step consumes only the weaker one.  Nothing in the frozen paper is
edited, and the stronger bound stays banked and unused; the finding is that
GAP-EXPOSED 1 is closable at the weaker fact, which is what this module does.
-/

namespace EthInapproximability.ParameterizedNP.DefectDischarge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.CopyRestriction

/-! ## Part 1: the aux-lemma battery

Six general properties of the banked readouts.  No definition is introduced,
and none of these is about the pinned instance of Part 3. -/

/-- **Aux 1 (density preservation — the core of `10-direct-bridge.tex:466`).**

For every coordinate set `P ⊆ [p]` with `|P| = k` and every column carrier
`K ⊆ Y^{[p]}`, the exact image has normalized density at least that of its
parent:

`y_K = |K| / n^p ≤ |K_P| / n^k = y_{K_P}`.

This is the frozen phrase "Its normalized density remains at least `x_out`"
in its general form: a density *floor* passes from parent to projection.  The
proof is the banked pigeonhole `|K| ≤ |K_P| · n^{p-k}`
(`card_le_card_copyCols_mul`) and nothing else — no density hypothesis, no
choice of coordinate set, no averaging. -/
lemma columnDensity_le_copyCols {p k : ℕ} {Y : Type*} [Fintype Y]
    [DecidableEq Y] (P : Finset (Fin p)) (hcard : P.card = k)
    (K : Finset (Fin p → Y)) (hY : 1 ≤ Fintype.card Y) :
    columnDensity K ≤ columnDensity (copyCols P hcard K) := by
  classical
  have hkp : k ≤ p := by
    have h := Finset.card_le_univ P
    rw [hcard, Fintype.card_fin] at h
    exact h
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnk : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k := by positivity
  have hnp : (0 : ℝ) < (Fintype.card Y : ℝ) ^ p := by positivity
  have hcount : (K.card : ℝ)
      ≤ ((copyCols P hcard K).card : ℝ) * (Fintype.card Y : ℝ) ^ (p - k) := by
    exact_mod_cast card_le_card_copyCols_mul P hcard K
  have hsplit : (Fintype.card Y : ℝ) ^ p
      = (Fintype.card Y : ℝ) ^ k * (Fintype.card Y : ℝ) ^ (p - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkp]
  unfold columnDensity
  rw [div_le_div_iff₀ hnp hnk]
  calc (K.card : ℝ) * (Fintype.card Y : ℝ) ^ k
      ≤ (((copyCols P hcard K).card : ℝ) * (Fintype.card Y : ℝ) ^ (p - k))
          * (Fintype.card Y : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hcount (le_of_lt hnk)
    _ = ((copyCols P hcard K).card : ℝ) * (Fintype.card Y : ℝ) ^ p := by
        rw [hsplit]; ring

/-- **Aux 2 (round trip: density floor ⟺ inherited ceiling guard).**

`x ≤ y_K` is the same statement as the column guard
`⌈|Y|^p · x⌉ ≤ |K|` that `D-inherited-contracts.tex:258` gives
`NPCC.coord_projection`.  This is what makes Candidate B of the header a
*restatement* of Candidate A rather than a second, differently strong,
hypothesis. -/
lemma le_columnDensity_iff_ceil_le_card {p : ℕ} {Y : Type*} [Fintype Y]
    (K : Finset (Fin p → Y)) (x : ℝ) (hY : 1 ≤ Fintype.card Y) :
    x ≤ columnDensity K ↔ ⌈((Fintype.card Y : ℝ) ^ p) * x⌉₊ ≤ K.card := by
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnp : (0 : ℝ) < (Fintype.card Y : ℝ) ^ p := by positivity
  rw [Nat.ceil_le, mul_comm ((Fintype.card Y : ℝ) ^ p) x]
  unfold columnDensity
  rw [le_div_iff₀ hnp]

/-- **Aux 3 (identity: a defect budget is a density floor).**

`Def(K) ≤ L ⟺ e^{-L} ≤ y_K`, for a nonempty column carrier over a nonempty
`Y`.  This is `10-direct-bridge.tex:98`'s dictionary read in the direction the
entry step needs, and it holds at an arbitrary budget `L`. -/
lemma columnDefect_le_iff_exp_le_columnDensity {k : ℕ} {Y : Type*} [Fintype Y]
    (K : Finset (Fin k → Y)) (L : ℝ) (hK : K.Nonempty)
    (hY : 1 ≤ Fintype.card Y) :
    columnDefect K ≤ L ↔ Real.exp (-L) ≤ columnDensity K := by
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnk : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k := by positivity
  rw [columnDefect_le_iff_density K L hK hY]
  unfold columnDensity
  rw [le_div_iff₀ hnk, mul_comm (Real.exp (-L)) ((Fintype.card Y : ℝ) ^ k)]

/-- **Aux 4 (composition — the general discharge engine).**

Aux 1 followed by Aux 3, at an arbitrary budget `L`: a density floor `e^{-L}`
on the *parent* carrier bounds the defect of the *exact image* by `L`.  This is
the whole mathematical content of `10-direct-bridge.tex:465--467`, with `L`
still free. -/
lemma columnDefect_copyCols_le_of_le_columnDensity {p k : ℕ} {Y : Type*}
    [Fintype Y] [DecidableEq Y] (P : Finset (Fin p)) (hcard : P.card = k)
    {K : Finset (Fin p → Y)} {L : ℝ} (hK : K.Nonempty)
    (hY : 1 ≤ Fintype.card Y) (h : Real.exp (-L) ≤ columnDensity K) :
    columnDefect (copyCols P hcard K) ≤ L :=
  (columnDefect_le_iff_exp_le_columnDensity (copyCols P hcard K) L
      (copyCols_nonempty P hcard hK) hY).mpr
    (le_trans h (columnDensity_le_copyCols P hcard K hY))

/-- **Aux 5 (calibration).**  The full column carrier reads density exactly
`1`, which is the density counterpart of the banked `columnDefect_univ = 0`.

This is the lemma that makes the degenerate instance visible: at `K = Y^{[p]}`
every density floor `x ≤ 1` holds for free and Aux 1 becomes `1 ≤ 1`, so a
witness there would test nothing.  Part 3 is therefore stated at a proper
carrier. -/
lemma columnDensity_univ (Y : Type*) [Fintype Y] (k : ℕ)
    (hY : 1 ≤ Fintype.card Y) :
    columnDensity (Finset.univ : Finset (Fin k → Y)) = 1 := by
  classical
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnk : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k := by positivity
  have hcard : ((Finset.univ : Finset (Fin k → Y)).card : ℝ)
      = (Fintype.card Y : ℝ) ^ k := by
    have h : (Finset.univ : Finset (Fin k → Y)).card = Fintype.card Y ^ k := by
      simp [Finset.card_univ]
    exact_mod_cast h
  unfold columnDensity
  rw [hcard, div_self (ne_of_gt hnk)]

/-- **Aux 6 (the frozen conversion of `10-direct-bridge.tex:396`).**

`L = ln(1/x_out)` inverts to `x_out = e^{-L}` (banked as `xOut_eq_exp`), so the
budget form and the density form of the entry condition are the same
statement:

`Def(K) ≤ L ⟺ x_out ≤ y_K`.

This is the only place where the route's own `x_out` and `L` meet the general
readouts, and it is an equivalence, so neither direction is a weakening. -/
lemma columnDefect_le_entryDefectL_iff {k : ℕ} {Y : Type*} [Fintype Y]
    (K : Finset (Fin k → Y)) (bout : ℕ) (hK : K.Nonempty)
    (hY : 1 ≤ Fintype.card Y) :
    columnDefect K ≤ entryDefectL bout ↔ xOut bout ≤ columnDensity K := by
  rw [columnDefect_le_iff_exp_le_columnDensity K (entryDefectL bout) hK hY,
    xOut_eq_exp]

/-! ## Part 2: the inherited density preservation, in defect form

`D-inherited-contracts.tex:250--265`.  The checked declaration
`NPCC.coord_projection` is *consumed* here at the route's own density
parameter `z = x_out`; its conclusion is converted to the frozen defect budget
`L` by Aux 2 and Aux 6.  This is the traced statement of the route the entry
step cites — and, per GAP-EXPOSED 1, it is **not** what discharges the binder,
because its column carrier is existential while the entry step needs the exact
image. -/

/-- **The inherited specified-coordinate projection, read as a defect bound**
(`D-inherited-contracts.tex:250--265`, at `z = x_out`;
`10-direct-bridge.tex:394--396` for the two parameters).

Given the inherited guards at the route's output density `x_out`, the returned
bracket member has a **nonempty** column carrier whose logarithmic defect is at
most `L = b_out ln 2`, and both provenance clauses of lines 261--265 are
retained verbatim.

Nonemptiness is *forced*, not assumed: `⌈|Y|^r x_out⌉₊ ≥ 1` because
`x_out > 0` and `|Y|^r ≥ 1`.  This is what stops the two universally
quantified provenance clauses, and the defect conjunct, from holding
vacuously. -/
theorem coordProjection_columnDefect_le {X Y : Type*} [Fintype X] [Fintype Y]
    (p r : ℕ) (hr : 0 < r) (Q : Finset (Fin p)) (e : Fin r ≃ {q // q ∈ Q})
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y)) (T : ℕ) (x : ℝ)
    (bout : ℕ) (hY : 1 ≤ Fintype.card Y)
    (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ p) * xOut bout⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T) :
    ∃ RC' : Finset (Fin r × X) × Finset (Fin r → Y),
      RC' ∈ bracketGE X Y r x (xOut bout) ∧
      RC'.2.Nonempty ∧
      columnDefect RC'.2 ≤ entryDefectL bout ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c' ∈ RC'.2, ∃ c ∈ C, ∀ j : Fin r, c' j = c (e j).val) := by
  classical
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnr : (0 : ℝ) < (Fintype.card Y : ℝ) ^ r := by positivity
  obtain ⟨RC', hmem, hrows, hcols⟩ :=
    coordProjection p r hr Q e R C T x (xOut bout) hrow hcol hxT
  have hfloor : 1 ≤ ⌈((Fintype.card Y : ℝ) ^ r) * xOut bout⌉₊ := by
    have hpos : (0 : ℕ) < ⌈((Fintype.card Y : ℝ) ^ r) * xOut bout⌉₊ :=
      Nat.lt_ceil.mpr (by
        have := xOut_pos bout
        push_cast
        positivity)
    omega
  have hne : RC'.2.Nonempty := bracketGE_cols_nonempty hfloor hmem
  refine ⟨RC', hmem, hne, ?_, hrows, hcols⟩
  refine (columnDefect_le_entryDefectL_iff RC'.2 bout hne hY).mpr ?_
  exact (le_columnDensity_iff_ceil_le_card RC'.2 (xOut bout) hY).mpr hmem.2

/-! ## Part 3: the discharge

The two candidate encodings of the header.  Both have exactly the binder list
of `CopyRestriction.entryLevelStep_ofCopyRestriction`, in the same order, with
its single defect binder `hdefect` replaced in place; the conclusion is
unchanged. -/

/-- **Candidate A (landed as the primary): the entry level step from a parent
density floor** (`10-direct-bridge.tex:458--469`).

The parent column carrier `K` of the selected state arrives with a normalized
density floor `x_out` — the frozen sentence at lines 458--459 — and the `p_t`
good copies arrive as the coordinate set `P` with `|P| = p_t`.  Lines 465--467
then say the projection keeps that floor, hence has defect at most `L`, and
lines 467--469 identify the projected column set as the exact image `K_P`.

That is exactly this statement: `hdefect` of
`entryLevelStep_ofCopyRestriction` is discharged by Aux 4 from `hdensity`, and
nothing else about the composed chain changes.  `GAP-EXPOSED 1` of
`BRIDGE-COPYREST-001` is closed here.

The conclusion is byte-identical to the conclusion of
`entryLevelStep_ofCopyRestriction`; the two clauses of `eq:direct-input`
(`hNear`, `hInput`) remain explicit hypotheses, so this is a conditional
statement and adds no unconditional complexity claim. -/
theorem entryLevelStep_ofParentDensity {X Y : Type*} [Fintype X] [Fintype Y]
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
    (hdensity : xOut bout ≤ columnDensity K) :
    CW + entryLevelA bout δU t ≤ D (subgame (interlaceFun W Q) Rstar K) := by
  classical
  refine entryLevelStep_ofCopyRestriction W CW bout ht hb hδ0 hδ1 hθ0 hgate
    hmargin hX hY hCW hNear hInput P hcard Rstar K hK hrows ?_
  refine columnDefect_copyCols_le_of_le_columnDensity P hcard hK hY ?_
  rw [← xOut_eq_exp]
  exact hdensity

/-- **Candidate B: the same step from the inherited ceiling guard**
(`D-inherited-contracts.tex:258` at `z = x_out`).

A caller holding a bracket membership has the column count in ceiling form
rather than as a real density.  Aux 2 proves the two are equivalent, so this is
a restatement of Candidate A and not a second claim: it is proved *from* A, and
only A carries content. -/
theorem entryLevelStep_ofParentColumnCount {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) (CW bout : ℕ) {δU θ : ℝ} {t : ℕ}
    (ht : t ≤ 2) (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
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
    CW + entryLevelA bout δU t ≤ D (subgame (interlaceFun W Q) Rstar K) :=
  entryLevelStep_ofParentDensity W CW bout ht hb hδ0 hδ1 hθ0 hgate hmargin
    hX hY hCW hNear hInput P hcard Rstar K hK hrows
    ((le_columnDensity_iff_ceil_le_card K (xOut bout) hY).mpr hcount)

/-! ## Part 4: non-vacuity

LANE-GATE 3.  Three witnesses, at three different kinds of legality:

* the density transport of Aux 1 and Aux 4 at a **proper** instance where both
  defects are strictly positive and the entry condition is met *tightly*;
* the full composition at the banked first entry-gate parameters, where the
  coordinate set is a **proper** subset of the outer interlace;
* the same composition with the parent carrier itself **exhibited** at that
  width — proper, nonempty, density exactly `x_out`, defect exactly `ln 2` —
  so that the new hypothesis `hdensity` is shown satisfiable at legal
  parameters by something other than the full carrier.

A degenerate inhabitant would read `K = Y^{[p]}` (density `1`, defect `0`, so
Aux 5 makes the floor free), `P = [p]` (no projection), or `b_out = 0`
(`x_out = 1`, `L = 0`).  No witness reads any of these. -/

/-- **Non-vacuity witness 1: the density transport at a proper instance.**

The banked proper instance of `BRIDGE-COPYREST-001`: `p = 3`, `P = {0,2}` (a
proper coordinate subset, so the projection genuinely forgets copy `1`), and
`K = sampleCols = {y : y(0) = y(2)}`, four of the eight parent columns, whose
exact image is two of the four child columns.

Read out here:

* the parent density is `4/2^3 = 1/2` and the projected density is
  `2/2^2 = 1/2`, so Aux 1 fires at **equality** — the floor is preserved
  exactly, not slackly;
* **both** defects are strictly positive (`Def = ln 2 > 0` on each side), so
  neither side is the degenerate full carrier of Aux 5;
* at the frozen legal depth `b_out = 1` the entry condition
  `x_out = 1/2 ≤ y_K` holds, and the discharged conclusion
  `Def(K_P) ≤ L = ln 2` holds — again tightly, so the budget is exactly
  consumed rather than trivially satisfied. -/
theorem densityTransport_fires_proper :
    columnDensity sampleCols = 1 / 2
      ∧ columnDensity (copyCols sampleP sampleP_card sampleCols) = 1 / 2
      ∧ 0 < columnDefect sampleCols
      ∧ 0 < columnDefect (copyCols sampleP sampleP_card sampleCols)
      ∧ xOut 1 ≤ columnDensity sampleCols
      ∧ columnDensity sampleCols
          ≤ columnDensity (copyCols sampleP sampleP_card sampleCols)
      ∧ columnDefect (copyCols sampleP sampleP_card sampleCols)
          ≤ entryDefectL 1 := by
  classical
  have hY : (1 : ℕ) ≤ Fintype.card Bool := by decide
  have hYcast : ((Fintype.card Bool : ℕ) : ℝ) = 2 := by simp
  have hK : sampleCols.Nonempty := by decide
  have hparent : (sampleCols.card : ℝ) = 4 := by
    have h : sampleCols.card = 4 := by decide
    rw [h]; norm_num
  have himage : ((copyCols sampleP sampleP_card sampleCols).card : ℝ) = 2 := by
    rw [sampleCols_image_card]; norm_num
  have hdensP : columnDensity sampleCols = 1 / 2 := by
    unfold columnDensity
    rw [hparent, hYcast]
    norm_num
  have hdensI : columnDensity (copyCols sampleP sampleP_card sampleCols)
      = 1 / 2 := by
    unfold columnDensity
    rw [himage, hYcast]
    norm_num
  have hdefP : 0 < columnDefect sampleCols := by
    unfold columnDefect
    rw [hparent, hYcast]
    have h : ((2 : ℝ) ^ (3 : ℕ)) / 4 = 2 := by norm_num
    rw [h]
    exact Real.log_pos (by norm_num)
  have hdefI : 0 < columnDefect (copyCols sampleP sampleP_card sampleCols) := by
    unfold columnDefect
    rw [himage, hYcast]
    have h : ((2 : ℝ) ^ (2 : ℕ)) / 2 = 2 := by norm_num
    rw [h]
    exact Real.log_pos (by norm_num)
  refine ⟨hdensP, hdensI, hdefP, hdefI, ?_, ?_, ?_⟩
  · rw [hdensP]
    unfold xOut
    norm_num
  · rw [hdensP, hdensI]
  · refine (columnDefect_le_entryDefectL_iff
      (copyCols sampleP sampleP_card sampleCols) 1
      (copyCols_nonempty sampleP sampleP_card hK) hY).mpr ?_
    rw [hdensI]
    unfold xOut
    norm_num

/-- **Non-vacuity witness 2: the composition fires at the banked first
entry-gate parameters.**

`b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `C_W = 3` — the parameters carried
by `DirectOutputLower.directOutputLower_fires_first_witness` and by
`CopyRestriction.entryLevelStep_ofCopyRestriction_fires_first_witness` — where
`Q = Qwidth 1 (1/60) = 8192` and the copy count `p_0 = entryCopyCount 1 (1/60) 0`
satisfies `4096 < p_0 < 8192`.  So a coordinate set of exactly the right size
exists and is a **proper** subset of the outer interlace: the discharge is
exercised where `lem:copy-restriction` actually projects, not at `P = [Q]`.

`X`, `Y`, `W` stay universally quantified and the two clauses of
`eq:direct-input` stay hypotheses — they have no exhibited inhabitant and can
have none until Stages 1--4 land.  What is established is that every *other*
binder of `entryLevelStep_ofParentDensity` — the depth, the deletion tolerance,
the row threshold, both entry gates, the width `Q`, the cardinality link
`|P| = p_t`, and the parent density floor `x_out = 1/2` — is simultaneously
satisfiable at legal frozen parameters. -/
theorem defectDischarge_fires_first_witness {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 (1 / 192000) (1 - 1 / 60)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 192000) (3 / 5)) :
    ∃ P : Finset (Fin (Qwidth 1 (1 / 60))),
      P.card = entryCopyCount 1 (1 / 60) 0
      ∧ P ⊂ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60))))
      ∧ 4096 < P.card
      ∧ ∀ (Rstar : Finset (Fin (Qwidth 1 (1 / 60)) × X))
          (K : Finset (Fin (Qwidth 1 (1 / 60)) → Y)),
          K.Nonempty →
          IsEquipartitionedGE Rstar P
            (rowFloor (Fintype.card X) (1 / 192000)
              (entryLevelA 1 (1 / 60) 0)) →
          xOut 1 ≤ columnDensity K →
          (3 : ℕ) + entryLevelA 1 (1 / 60) 0
            ≤ D (subgame (interlaceFun W (Qwidth 1 (1 / 60))) Rstar K) := by
  classical
  obtain ⟨hlow, hhigh, -⟩ := entryCopyCount_fires_first_witness
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 60) (le_refl (1 / 60 : ℝ))
  have hcardle : entryCopyCount 1 (1 / 60) 0
      ≤ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60)))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨P, -, hPcard⟩ := Finset.exists_subset_card_eq hcardle
  refine ⟨P, hPcard, ?_, ?_, ?_⟩
  · refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    rw [hEq, Finset.card_univ, Fintype.card_fin] at hPcard
    omega
  · rw [hPcard]
    exact hlow
  · intro Rstar K hK hrows hdensity
    exact entryLevelStep_ofParentDensity W 3 1 (δU := 1 / 60)
      (θ := 1 / 192000) (t := 0) (by norm_num) (le_refl 1) (by norm_num)
      (by norm_num) (by norm_num) hgate hmargin hX hY (le_refl 3) hNear hInput
      P hPcard Rstar K hK hrows hdensity

/-- **Aux 7 (a proper column carrier that meets the entry floor tightly, at
every legal width).**

For every width `Q ≥ 1` there is a column carrier over `Y = Bool` that is a
**proper** subset of `Y^{[Q]}`, is nonempty, has normalized density exactly
`1/2`, and has defect exactly `ln 2 > 0`.  The carrier is the image of
`z ↦ Fin.cons false z`, i.e. the columns whose coordinate `0` is fixed — the
`p'`-coordinate half space, not a hand-picked finite set — so the statement is
about arbitrary `Q` and never about a pinned numeral.

This is the aux lemma that lets the entry-gate witness below *exhibit* its
parent carrier rather than quantify over it.  Both extremes are excluded by
construction: the density is not `1` (so the carrier is not the degenerate full
space of Aux 5, and the floor `x_out = 1/2` is met with **no slack**), and the
defect is not `0`. -/
lemma exists_proper_halfDensity_cols (Q : ℕ) (hQ : 0 < Q) :
    ∃ K : Finset (Fin Q → Bool),
      K.Nonempty
        ∧ K ⊂ (Finset.univ : Finset (Fin Q → Bool))
        ∧ columnDensity K = 1 / 2
        ∧ columnDefect K = Real.log 2 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  have hinj : Function.Injective
      (fun z : Fin n → Bool => (Fin.cons false z : Fin (n + 1) → Bool)) := by
    intro z1 z2 h
    funext i
    have hi := congrFun h i.succ
    simpa using hi
  refine ⟨(Finset.univ : Finset (Fin n → Bool)).image
    (fun z : Fin n → Bool => (Fin.cons false z : Fin (n + 1) → Bool)),
    ?_, ?_, ?_, ?_⟩
  · exact (Finset.univ_nonempty).image _
  all_goals
    have hcardK : ((Finset.univ : Finset (Fin n → Bool)).image
        (fun z : Fin n → Bool =>
          (Fin.cons false z : Fin (n + 1) → Bool))).card = 2 ^ n := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      simp
  · refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    have huniv : ((Finset.univ : Finset (Fin n → Bool)).image
        (fun z : Fin n → Bool =>
          (Fin.cons false z : Fin (n + 1) → Bool))).card = 2 ^ (n + 1) := by
      rw [hEq, Finset.card_univ]
      simp
    rw [hcardK, pow_succ] at huniv
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    omega
  · have hB : ((Fintype.card Bool : ℕ) : ℝ) = 2 := by simp
    unfold columnDensity
    rw [hcardK, hB]
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    push_cast
    rw [pow_succ]
    field_simp
  · have hB : ((Fintype.card Bool : ℕ) : ℝ) = 2 := by simp
    unfold columnDefect
    rw [hcardK, hB]
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have hkey : ((2 : ℝ) ^ (n + 1)) / ((2 : ℝ) ^ n) = 2 := by
      rw [pow_succ]
      field_simp
    push_cast
    rw [hkey]

/-- **Non-vacuity witness 3: the composition fires at the banked first
entry-gate parameters with the parent carrier *exhibited*.**

Witness 2 discharges every parameter binder but leaves `K` universally
quantified, so on its own it does not show that the new hypothesis `hdensity`
is satisfiable at the entry-gate width by anything other than the full carrier.
This witness closes that: at `Q = Qwidth 1 (1/60) = 8192` and `Y = Bool` it
**produces** a parent column carrier `K` that is

* a **proper** subset of `Y^{[Q]}` (so the density floor is not met by the
  degenerate `K = Y^{[Q]}` of Aux 5),
* of normalized density exactly `1/2 = x_out`, i.e. the frozen floor of
  `10-direct-bridge.tex:458--459` is met with **no slack**, and
* of defect exactly `ln 2 > 0`,

alongside the coordinate set `P` of exactly `p_0 = entryCopyCount 1 (1/60) 0`
copies with `4096 < p_0 < 8192`, again a proper subset.

`X`, `W` and the row set `R_*` stay universally quantified and the two clauses
of `eq:direct-input` stay hypotheses — they have no exhibited inhabitant and
can have none until Stages 1--4 land.  `Y` is pinned to `Bool` only because a
carrier must be exhibited; the theorems of Part 3 remain stated at an arbitrary
`Y`. -/
theorem defectDischarge_fires_pinned_carrier {X : Type*} [Fintype X]
    (W : X → Bool → Bool) (hX : 1 ≤ Fintype.card X)
    (hNear : (3 : ℕ) ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Bool 1 (1 / 192000) (1 - 1 / 60)))
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 192000) (3 / 5)) :
    ∃ (P : Finset (Fin (Qwidth 1 (1 / 60))))
      (K : Finset (Fin (Qwidth 1 (1 / 60)) → Bool)),
      P.card = entryCopyCount 1 (1 / 60) 0
      ∧ P ⊂ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60))))
      ∧ 4096 < P.card
      ∧ K ⊂ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60)) → Bool))
      ∧ K.Nonempty
      ∧ columnDensity K = 1 / 2
      ∧ columnDefect K = Real.log 2
      ∧ xOut 1 ≤ columnDensity K
      ∧ ∀ Rstar : Finset (Fin (Qwidth 1 (1 / 60)) × X),
          IsEquipartitionedGE Rstar P
            (rowFloor (Fintype.card X) (1 / 192000)
              (entryLevelA 1 (1 / 60) 0)) →
          (3 : ℕ) + entryLevelA 1 (1 / 60) 0
            ≤ D (subgame (interlaceFun W (Qwidth 1 (1 / 60))) Rstar K) := by
  classical
  obtain ⟨-, -, -, hQ8192, -, -, -⟩ := directEntryGates_fires
  obtain ⟨hlow, hhigh, -⟩ := entryCopyCount_fires_first_witness
  have hY : 1 ≤ Fintype.card Bool := by decide
  have hgate : 4 * Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ deltaFixed := by
    rw [Q0_eq_route (by norm_num) (by norm_num) (by norm_num), deltaFixed_eq]
    norm_num
  have hmargin := secondEntryGate_of_deltaU_small
    (by norm_num : (0 : ℝ) < 1 / 60) (le_refl (1 / 60 : ℝ))
  have hcardle : entryCopyCount 1 (1 / 60) 0
      ≤ (Finset.univ : Finset (Fin (Qwidth 1 (1 / 60)))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨P, -, hPcard⟩ := Finset.exists_subset_card_eq hcardle
  obtain ⟨K, hKne, hKss, hKdens, hKdef⟩ :=
    exists_proper_halfDensity_cols (Qwidth 1 (1 / 60)) (by rw [hQ8192]; norm_num)
  have hdensity : xOut 1 ≤ columnDensity K := by
    rw [hKdens]
    unfold xOut
    norm_num
  refine ⟨P, K, hPcard, ?_, ?_, hKss, hKne, hKdens, hKdef, hdensity, ?_⟩
  · refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    rw [hEq, Finset.card_univ, Fintype.card_fin] at hPcard
    omega
  · rw [hPcard]
    exact hlow
  · intro Rstar hrows
    exact entryLevelStep_ofParentDensity W 3 1 (δU := 1 / 60)
      (θ := 1 / 192000) (t := 0) (by norm_num) (le_refl 1) (by norm_num)
      (by norm_num) (by norm_num) hgate hmargin hX hY (le_refl 3) hNear hInput
      P hPcard Rstar K hKne hrows hdensity

end EthInapproximability.ParameterizedNP.DefectDischarge
