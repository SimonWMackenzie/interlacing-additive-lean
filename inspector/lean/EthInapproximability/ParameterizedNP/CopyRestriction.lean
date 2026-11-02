import EthInapproximability.ParameterizedNP.DirectOutputLower

/-!
# Parameterized NP route: exact-image copy restriction

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-COPYREST-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1k` tranche as the local typed interface `lem:copy-restriction`, which
Appendix D records as a *reboot obligation* that
"must not be replaced by citing `NPCC.coord_projection` alone".

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`, `lem:copy-restriction` (label line 132,
  statement lines 131--165, proof lines 167--186) — the whole content of this
  module:
  * lines 133--144, the frozen binder list: `W : X × Y → {0,1}`, `p ≥ 1`,
    `R ⊆ [p] × X`, `∅ ≠ K ⊆ Y^{[p]}` "the row and column sets of a restriction
    of `Int_p(W)`", `∅ ≠ R_* ⊆ R` regarded as the row-restricted submatrix
    ("an Alice protocol child is the principal application"), a nonempty
    coordinate set `P ⊆ [p]`, `p' = |P|`, and
    "let `e : [p'] ≃ P` be **the increasing equivalence**";
  * `eq:copy-restriction-data` (label line 153, display lines 145--153) — the
    three pinned data: `R_{*,P} = {(j,x) ∈ [p'] × X : (e(j),x) ∈ R_*}`,
    `π_P(y)(j) = y(e(j))`, and `K_P = π_P(K)`;
  * lines 155--161, the conclusion "the extracted matrix
    `extract(Int_{p'}(W), R_{*,P}, K_P)` is entry-preservingly row--column
    isomorphic to a restriction of the selected row-restricted matrix.  In
    particular, its communication complexity is at most that of this matrix";
  * lines 161--164, "Moreover, if every coordinate in `P` has at least `A`
    surviving rows in `R_*`, then every outer block of `R_{*,P}` has at least
    `A` rows, and its column set is **the exact image `K_P`, not an
    arbitrarily chosen subset of that image**";
  * lines 168--172 of the proof, "the restricted projection
    `π_P : K ↠ K_P` is surjective.  Choose a right inverse `σ_P` by finite
    choice.  The lemma is existential in this proof witness, and **no later
    constructor output depends on which section is used**";
  * lines 173--182, the entry computation
    `Int_p(W)((e(j),x), σ_P(z)) = W(x, σ_P(z)(e(j))) = W(x, z(j))
    = Int_{p'}(W)((j,x), z)`, and lines 184--185, "The fibre-count assertion
    follows immediately from the definition of `R_{*,P}`".
* `sections/10-direct-bridge.tex`, the four consumption sites this interface
  exists for, quoted so that the shape landed here is the shape they need:
  * lines 286--291 (Alice case, `a ≥ 3`): "`lem:copy-restriction`, with
    `P = P_i`, produces inside that child a literal restriction of
    `Int_{p_i}(W)` with exact column set `K_i` and at least `A_{a-1}` rows in
    every block";
  * lines 326--329 (level `a = 1`): "`lem:copy-restriction` identifies the
    corresponding exact-image restriction as a literal `p_i`-copy state";
  * lines 350--352 (Alice case at level `a ≥ 2`, inside the proof of
    `lem:defect-induction`): "For that child `d_i > 0`, so
    `lem:copy-restriction` supplies the literal `p_i`-copy restriction to
    which the induction hypothesis at level `a-1` applies";
  * lines 465--469 (`sec:direct-entry`): "Choose any `p_t` good copies and
    project the column set to them ... By `lem:copy-restriction`, the exact
    projected image and the rows from these good copies form a literal
    restriction of `Int_{p_t}(W)` inside the selected state."
* `sections/D-inherited-contracts.tex`, "Locally proved typed interface:
  exact-image copy restriction" (paragraph at lines 267--276) — "The
  specified-coordinate theorem above returns legal bracket extraction data; it
  does not identify an Alice protocol child with a literal smaller interlace
  whose column set is the full projection image of a fixed parent set.  The
  additional interface consumed by the defect induction is therefore the local
  `lem:copy-restriction`.  It defines the projected row set and exact image
  column set, chooses a section of the finite projection, and proves an
  entry-preserving isomorphism to a restriction of the child.  Its human proof
  is present; its Lean declaration remains a reboot obligation and must not be
  replaced by citing `NPCC.coord_projection` alone."
* `conv:finite-slots` (`sections/03-preliminaries.tex`) — zero-based finite
  slots; the coordinate carriers here are `Fin p` and `Fin k`, and the row
  carrier of the interlace is `Fin _ × X`, as in `FiniteSlots.lean`.

## Reader counterpart

`routes/parameterized-np/reader-facing/`.  Each candidate file was opened and
read first-hand in the frozen release source.

Reader counterpart: `sections/B-bridge-details.tex` **lines 29--32 only**,
assigned to **exactly one** declaration, `copyRestriction`:

> "Whenever a projected set is used as a communication subproblem, keep the
> least original representative of each projected tuple.  On the selected row
> blocks, the interlace reads only the projected coordinates, so the resulting
> restriction is literally the claimed smaller interlace."

That is the reader's statement of `lem:copy-restriction`: the chosen section
(`σ_P`, "the least original representative"), and the identification of the
restriction with a literal smaller interlace.  It is navigation only; the
proof source is the frozen autoformalization section.

Two prior records are reconciled here, and neither is deleted:

* `BRIDGE-DEFECT-001` records that `B-bridge-details.tex` lines 18--21 **and**
  29--32 "match `INHERIT-001`'s content but are not listed in its counterpart
  record; they remain unassigned and are not claimed here either".  This row
  assigns **29--32 only**; lines 18--21 (the entropy-averaging defect
  sentences) **remain unassigned**, exactly as that record leaves them.
* `READER_CROSSWALK.md`'s "Generic robustness bridge" row names, for
  `INHERIT-001`'s `coordProjection`, the whole Appendix B subsection
  §"Defect and projection" (lines 13--38).  That section-level naming is
  **narrowed** in the same change to exclude lines 29--32, which state the
  copy-restriction fact rather than a projection fact, so no reader item is
  assigned twice.  `INHERIT-001`'s ledger-recorded counterparts
  (`prop:paper-projection-facts`, `thm:near-to-robust`) are untouched.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Vendored-counterpart finding (reuse check, performed before any new proof)

The vendored development was searched for a counterpart before anything was
written.  The finding is **split**, and Appendix D's warning is honoured:

* **Not reusable as the lemma.**  `NPCC.coord_projection`
  (`vendor/npc-cc/NPCC/CoordProjection.lean:26`, route-facaded as
  `InheritedContracts.coordProjection`) and its consumer
  `EthBridge.entry_projected_state` (`vendor/npc-cc/EthBridge/Entry.lean:603`)
  deliver an **existential** pair `RC'` in a bracket family, whose column set
  is only known to satisfy a cardinality lower bound and a provenance clause.
  Neither pins the **exact image** `K_P = π_P(K)`, and neither identifies the
  row set as the literal fibre set `R_{*,P}` of a *fixed* parent.  That is
  exactly the substitution `D-inherited-contracts.tex:275--276` forbids, so
  neither is used to state or prove `copyRestriction`.
* **Reusable as the complexity half only.**  `EthBridge.projected_subgame_le`
  (`vendor/npc-cc/EthBridge/Entry.lean:500`) is the kernel-checked
  `D`-comparison along two provenance maps: from
  `∀ a ∈ R', (emb a.1, a.2) ∈ R` and
  `∀ c' ∈ C', ∃ c ∈ C, ∀ j, c' j = c (emb j)` it returns
  `D(subgame(Int(f,r), R', C')) ≤ D(subgame(Int(f,q), R, C))`.  Its body is the
  vendored `D_mapNodes_le` along the row map `(j,x) ↦ (e(j),x)` and a section
  of the column projection chosen by `Classical.choose` — i.e. it *is* the
  frozen proof's own two injections and its `σ_P` (frozen lines 173--182).  It
  is **consumed**, never re-proved and never widened.  It is not
  `coord_projection`: it is a generic comparison lemma with no bracket, no
  density and no cardinality content, so consuming it does not let
  `coord_projection` stand in for this lemma.

Everything that `D-inherited-contracts.tex:272--274` says is *new* here — the
projected row set, the exact-image column set, the fibre count — is defined and
proved in this module.

## Status and dependencies

* Proof status: **new (elementary)** for every definition, every aux lemma,
  every witness and the fibre-count and exact-image clauses; **inherited** for
  the `D`-comparison clause alone (the consumed
  `EthBridge.projected_subgame_le`).
* Consumed, never edited or re-proved:
  * `EthBridge.projected_subgame_le` (see above);
  * `DirectOutputLower.entryLevelStep` and, through it, the banked
    `DefectInduction.defectInduction` chain — used *only* in the composition
    `entryLevelStep_ofCopyRestriction`, whose statement adds nothing to
    `entryLevelStep` beyond replacing its two carrier binders by the pinned
    construction of this module;
  * `DefectInduction.rowFloor`, `InheritedContracts.columnDefect`,
    `EntryGates.*` and `DirectOutputLower.entryCopyCount`, `.entryLevelA`,
    `.entryDefectL` as readouts only.
* Imports: `DirectOutputLower.lean` only, hence `DirectOutput.lean`,
  `EntryGates.lean`, `PilotStage3.lean`, `ThreeCopyRowStep.lean`,
  `TwoCopyLadder.lean`, `DefectInduction.lean`, `InheritedContracts.lean`,
  `EthInapproximability.Prelude`, and through it `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom is not in scope,
  and there is no contact with `EXPANDER-001` (which by design has no Lean
  declaration and would have to stay an explicit named hypothesis).
* External adapters: none.  Nothing here is axiomatized, and no opaque
  certificate is introduced.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

The open encoding choice is *what kind of object* `lem:copy-restriction` is.

**Candidate A (landed): a named-def claim about the pinned data of
`eq:copy-restriction-data`.**  `copyEmb`, `copyProj`, `copyRows`, `copyCols`
are definitions — respectively `e`, `π_P`, `R_{*,P}`, `K_P` — and
`copyRestriction` is a closed statement *about those definitions*.  `e` is
pinned to `Finset.orderEmbOfFin`, the unique **increasing** enumeration of `P`
(frozen line 144), rather than bound as an arbitrary equivalence.  Aux battery:
**18/18 proved**, in seven general property classes — enumeration behaviour
(`copyEmb_mem`, `copyEmb_strictMono`, `copyEmb_injective`,
`copyEmb_image_univ`, `exists_copyEmb_eq`), membership characterization
(`mem_copyRows`, `mem_copyCols`, `copyProj_mem_copyCols`), monotonicity
(`copyRows_mono`, `copyCols_mono`), nonemptiness and surjectivity
(`copyCols_nonempty`, `copyProj_surjective`), round trips on the full carriers
(`copyCols_univ`, `copyRows_univ`, `isEquipartitionedGE_univ`), counting
(`card_le_card_copyCols_mul`, `columnDefect_copyCols_le`), and the row-floor
equivalence (`copyRows_isEquipartitionedGE_iff`).  Every one is a statement
about arbitrary `p`, `k`, `P`, `R_*`, `K` and arbitrary carriers, not about the
pinned instances of Part 5.

**Candidate B (rejected — disqualified by the trivial-witness pole).**  The
existential reading: "there exist `R'`, `K'` with `K'` nonempty, with row and
column provenance into `(R_*, K)`, with every block of `R'` holding `A` rows,
and with `D(subgame) ≤ D(parent)`".  One line refutes it: **the singleton
`K' = {c₀}` for any one projected column satisfies every clause** — it is
nonempty, its provenance clause holds, its blocks are the same blocks, and its
complexity is *smaller*, so the inequality only gets easier.  Hence the
existential does not pin `K_P` at all, and frozen lines 163--164 ("the exact
image `K_P`, **not an arbitrarily chosen subset of that image**") would be
lost.  This is not an informal objection: `copyCols_refutes_candidateB` proves
the refutation in Lean, and `copyRestriction_fires_nondegenerate` exhibits a
legal instance where the exact image has `4` columns while the degenerate
witness has `1`.

Ranking (aux lemmas proved, faithfulness, length): A = 18/18, literal in
`eq:copy-restriction-data`, `e` increasing, exact image pinned; B = existential,
satisfied by a witness the frozen text explicitly excludes.  A landed.

Frozen lines 169--172 are what makes A the *right* shape rather than merely the
safe one: the paper says the lemma is existential **in the section `σ_P`** and
that "no later constructor output depends on which section is used".  Candidate
A puts the choice exactly there — inside the consumed `projected_subgame_le`,
whose `Classical.choose` picks the section — and nowhere else: `copyRows` and
`copyCols` are choice-free.

## Faithfulness notes (mechanical rules M1--M10)

* **No structure and no premise bundle.**  Four plain definitions and named
  theorems; every hypothesis of the frozen lemma is an explicit binder.  No
  field restates a derived telescope, and no conclusion of the lemma (the
  complexity comparison, the fibre count, the exactness) sits in constructor
  data: `copyRows` and `copyCols` are pure finite data built from `P`, `R_*`
  and `K`, with no hypothesis attached and no complexity, density or defect
  content.
* **The increasing equivalence is preserved, not weakened.**  `copyEmb` is
  `Finset.orderEmbOfFin`, and `copyEmb_strictMono` records that it is
  increasing; `copyEmb_image_univ` records that its image is exactly `P`, which
  is the `≃ P` half.  A statement quantified over an arbitrary injection would
  be a different (and, for the "increasing" clause, strictly weaker) claim.
* **Both interlace widths.**  Only coordinate counts occur: the parent width
  `p` and the projected width `k = |P|`.  The scale-alignment width `q` and the
  outer interlace width `Q` do not appear as such; in
  `entryLevelStep_ofCopyRestriction` the parent width is the caller's `Q` and
  the child width is `entryCopyCount bout δU t = p_t`, matching frozen lines
  465--469, and the two are never conflated (`hcard : P.card = p_t` is the only
  link).
* **Finite carriers and nonemptiness.**  `p ≥ 1`, `∅ ≠ P`, `∅ ≠ R_*`,
  `∅ ≠ K` are carried as explicit binders in the bundled `copyRestriction`
  exactly as frozen lines 133--143 carry them, and `copyCols_nonempty`
  propagates nonemptiness of `K` to `K_P` (the frozen lemma needs `K_P` to be a
  legal column set of a restriction).  The component lemmas do **not** assume
  them, so nothing downstream inherits an unnecessary guard.
* **The frozen ambient row set `R` is kept as a binder** in `copyRestriction`,
  with `R_* ⊆ R`, because frozen lines 135--141 carry it; it is not used in the
  proof, and `copyRestriction_binders_satisfiable` records that the pair
  `(R, R_* ⊆ R)` restricts nothing (take `R = R_*`), so keeping it does not
  make the statement an over-strong bundle.
* **Ceilings and row floors are not redefined.**  The row-floor parameter is a
  bare `A : ℕ` here, exactly as frozen line 162 states it; the wiring test
  instantiates it with the banked `DefectInduction.rowFloor`, never with a new
  ceiling.
* **Binder order** follows the frozen sentence: the matrix, the parent width,
  the ambient row set and column set, the row restriction, the coordinate set
  and its cardinality, then the row floor.
* **Trivial-witness pole.**  Stated above and *proved*: the one existential
  reading of this lemma is satisfied by a singleton column set, so the
  deliverable is a named-def claim rather than an existential.  The one
  existential statement in the module is `copyCols_refutes_candidateB`, and it
  is a refutation, not a deliverable.
* **Vacuous-hypothesis pole.**  `copyRestriction`'s hypotheses are discharged
  at legal instances twice over.
  * `copyRestriction_fires_at_sample`, whose data
    `copyRestriction_fires_nondegenerate` reads out: a **proper** coordinate
    subset (`k = 2 < 3 = p`, so the lemma is used where it actually projects),
    a row floor of `2` per block (not `0`), and an exact image of `4` columns
    out of `8` parent columns (neither everything nor a singleton).
  * `copyRestriction_fires_proper`, which additionally takes `R_*` and `K`
    **proper**: `R_* = sampleRows` is five of six rows (so the frozen ambient
    binder `R_* ⊆ R` is used at a strict inclusion), `K = sampleCols` is four
    of eight columns, and the exact image is `2` of the `4` child columns —
    the projection genuinely collapses.  It also reads out the defect
    transport of Aux 15 at that instance.
  * The pinned enumeration is exhibited: `sampleEmb` proves `e(0) = 0`,
    `e(1) = 2` from `copyEmb_strictMono` alone, which is where the frozen word
    "increasing" is visibly doing work — an arbitrary equivalence would also
    permit `e(0) = 2`.
  A degenerate inhabitant would read `P = [p]` (no projection at all), `A = 0`
  (empty blocks), `R_* = K = ` the full carriers (no restriction), or
  `|K_P| = 1` (the collapsed image); none of these reads any of them.
* **Floor-restriction pole.**  The floor clause is neither free nor
  over-strong: `copyRows_isEquipartitionedGE_iff` proves the conclusion
  *equivalent* to the frozen premise, and
  `copyRestriction_rowFloor_premise_bites` exhibits a row restriction thin at a
  coordinate of `P` that fails both.
* **Composition pole.**  `entryLevelStep_ofCopyRestriction_fires_first_witness`
  discharges every binder of the wiring test except `X`, `Y`, `W` and the two
  clauses of `eq:direct-input`, at the banked first entry-gate parameters
  `b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `C_W = 3`, and exhibits a
  coordinate set of exactly `p_0 = entryCopyCount 1 (1/60) 0` copies inside
  `Q = 8192` which is a **proper** subset (`4096 < p_0 < 8192`).
* **Vacuous-conclusion pole.**  The complexity clause is an inequality between
  two `D` values and is *not* free: `copyCols_refutes_candidateB` shows it can
  be satisfied by a strictly smaller column set, so the content of the lemma is
  carried by the other two clauses, both of which are equalities of finite
  data.

## GAP-EXPOSED (nothing is weakened to close these)

1. **The frozen density-preservation step is not claimed.**  Frozen lines
   465--467 say the projected column set keeps normalized *density* at least
   `x_out`, so its defect is at most `L`.  That is
   `NPCC.coord_projection`'s density-preservation for a *well-chosen*
   coordinate set (reader `B-bridge-details.tex:18--21`, entropy averaging,
   defect at most `(p'/p)Δ_p(K)`), already banked as `INHERIT-001`'s
   `coordProjection`; `lem:copy-restriction` itself claims nothing about
   `|K_P|`.  What is proved here is only the *crude* counting transport
   `columnDefect_copyCols_le`: `Def(K_P) ≤ Def(K)` for **every** coordinate
   set, from the pigeonhole `|K| ≤ |K_P| · n^{p-p'}`.  That is strictly weaker
   than the averaging bound and is not a substitute for it.  Accordingly
   `entryLevelStep_ofCopyRestriction` still takes the defect bound on the exact
   image `K_P` as an explicit binder; the corollary
   `entryLevelStep_ofCopyRestriction_ofParentDefect` takes the parent bound
   instead and is *weaker* for exactly that reason.  Composing the frozen
   chain — parent density to projected defect to `entryLevelStep` — remains
   the separate obligation and is not claimed here.
2. **The entry-preserving isomorphism is not stated as an isomorphism.**  The
   frozen conclusion is "entry-preservingly row--column isomorphic to a
   restriction ... In particular, its communication complexity is at most that
   of this matrix" (lines 159--161).  Only the "in particular" is claimed here,
   through the consumed `projected_subgame_le`, whose own proof is the frozen
   entry computation of lines 176--182 along the two injections.  A typed
   `GameIso` witness for the isomorphism itself is not produced.
3. **The four consumption sites are not rewired.**  `DefectInduction`'s three
   Alice cases (frozen lines 286--291, 326--329 and 350--352) still run inside
   the banked vendored term; only the `sec:direct-entry` site (lines 465--469)
   is exercised here, as the composition wiring test.  Rewiring the induction's
   internal Alice split is not attempted and nothing about it is claimed.
4. **`eq:direct-input` still has no exhibited inhabitant**, so
   `entryLevelStep_ofCopyRestriction` is conditional exactly as
   `entryLevelStep` is; this module adds no unconditional complexity claim.
-/

namespace EthInapproximability.ParameterizedNP.CopyRestriction

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutputLower

/-! ## Part 1: the pinned data of `eq:copy-restriction-data`
(`10-direct-bridge.tex:145--153`)

Four definitions and nothing else.  Each is plain finite data; none carries a
hypothesis, and none mentions complexity, density or defect. -/

/-- **The increasing equivalence `e : [p'] ≃ P`**
(`10-direct-bridge.tex:143--144`).

`P.orderEmbOfFin hcard` is the unique *increasing* enumeration of the
coordinate set `P` by `Fin k`, where `hcard : P.card = k` pins `k = p' = |P|`.
The frozen text does not bind an arbitrary equivalence: it says "let
`e : [p'] ≃ P` be **the** increasing equivalence", so the enumeration is
pinned here rather than quantified over. -/
def copyEmb {p k : ℕ} (P : Finset (Fin p)) (hcard : P.card = k) : Fin k → Fin p :=
  fun j => P.orderEmbOfFin hcard j

/-- **The coordinate projection `π_P(y)(j) = y(e(j))`**
(`10-direct-bridge.tex:149--150`). -/
def copyProj {p k : ℕ} {Y : Type*} (P : Finset (Fin p)) (hcard : P.card = k)
    (y : Fin p → Y) : Fin k → Y :=
  fun j => y (copyEmb P hcard j)

/-- **The projected row set
`R_{*,P} = {(j,x) ∈ [p'] × X : (e(j),x) ∈ R_*}`**
(`10-direct-bridge.tex:147--148`).

This is the literal fibre set of the *fixed* parent `R_*`, not a chosen
subset. -/
def copyRows {p k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset (Fin p)) (hcard : P.card = k) (Rstar : Finset (Fin p × X)) :
    Finset (Fin k × X) :=
  Finset.univ.filter fun q => (copyEmb P hcard q.1, q.2) ∈ Rstar

/-- **The exact image `K_P = π_P(K)`** (`10-direct-bridge.tex:151`).

`Finset.image` is the exact image: frozen lines 163--164 insist this is "the
exact image `K_P`, not an arbitrarily chosen subset of that image", and
`mem_copyCols` records both directions of that. -/
def copyCols {p k : ℕ} {Y : Type*} [DecidableEq Y] (P : Finset (Fin p))
    (hcard : P.card = k) (K : Finset (Fin p → Y)) : Finset (Fin k → Y) :=
  K.image (copyProj P hcard)

/-! ## Part 2: the aux-lemma battery

General properties of the four definitions at arbitrary carriers, arbitrary
`p`, `k`, `P`, `R_*` and `K`.  These are the unit tests for the encoding: none
of them is about the pinned instance of Part 5. -/

/-- **Aux 1 (the enumeration lands in `P`).**  Every enumerated coordinate is a
coordinate of `P` — the "`≃ P`" half of `e : [p'] ≃ P`. -/
lemma copyEmb_mem {p k : ℕ} (P : Finset (Fin p)) (hcard : P.card = k)
    (j : Fin k) : copyEmb P hcard j ∈ P :=
  P.orderEmbOfFin_mem hcard j

/-- **Aux 2 (increasing).**  `e` is strictly monotone — this is the word
"increasing" of `10-direct-bridge.tex:144`, and it is the clause an arbitrary
injection would lose. -/
lemma copyEmb_strictMono {p k : ℕ} (P : Finset (Fin p)) (hcard : P.card = k) :
    StrictMono (copyEmb P hcard) :=
  fun _ _ h => (P.orderEmbOfFin hcard).strictMono h

/-- **Aux 2' (injective).**  Immediate from Aux 2; it is what the row map
`(j,x) ↦ (e(j),x)` of `10-direct-bridge.tex:174` needs. -/
lemma copyEmb_injective {p k : ℕ} (P : Finset (Fin p)) (hcard : P.card = k) :
    Function.Injective (copyEmb P hcard) :=
  (copyEmb_strictMono P hcard).injective

/-- **Aux 3 (onto `P`).**  The image of the enumeration is exactly `P`: `e` is
a bijection `[p'] ≃ P`, not merely an injection into `[p]`. -/
lemma copyEmb_image_univ {p k : ℕ} (P : Finset (Fin p)) (hcard : P.card = k) :
    Finset.image (copyEmb P hcard) Finset.univ = P :=
  P.image_orderEmbOfFin_univ hcard

/-- **Aux 4 (membership in the projected row set).**  The literal reading of
`10-direct-bridge.tex:147--148`. -/
@[simp] lemma mem_copyRows {p k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset (Fin p)) (hcard : P.card = k) (Rstar : Finset (Fin p × X))
    (q : Fin k × X) :
    q ∈ copyRows P hcard Rstar ↔ (copyEmb P hcard q.1, q.2) ∈ Rstar := by
  simp [copyRows]

/-- **Aux 5 (membership in the exact image).**  Both directions: every element
of `K_P` comes from an actual column of `K`, and every column of `K` has its
projection in `K_P`.  The second direction is the clause that distinguishes the
exact image from "an arbitrarily chosen subset of that image"
(`10-direct-bridge.tex:163--164`). -/
@[simp] lemma mem_copyCols {p k : ℕ} {Y : Type*} [DecidableEq Y]
    (P : Finset (Fin p)) (hcard : P.card = k) (K : Finset (Fin p → Y))
    (c : Fin k → Y) :
    c ∈ copyCols P hcard K ↔ ∃ y ∈ K, copyProj P hcard y = c := by
  simp [copyCols]

/-- **Aux 5' (the exactness clause, forward form).**  Every parent column
survives projection. -/
lemma copyProj_mem_copyCols {p k : ℕ} {Y : Type*} [DecidableEq Y]
    (P : Finset (Fin p)) (hcard : P.card = k) {K : Finset (Fin p → Y)}
    {y : Fin p → Y} (hy : y ∈ K) : copyProj P hcard y ∈ copyCols P hcard K :=
  Finset.mem_image_of_mem _ hy

/-- **Aux 6 (monotone in the row set).** -/
lemma copyRows_mono {p k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset (Fin p)) (hcard : P.card = k) {R S : Finset (Fin p × X)}
    (h : R ⊆ S) : copyRows P hcard R ⊆ copyRows P hcard S := by
  intro q hq
  rw [mem_copyRows] at hq ⊢
  exact h hq

/-- **Aux 7 (monotone in the column set).** -/
lemma copyCols_mono {p k : ℕ} {Y : Type*} [DecidableEq Y] (P : Finset (Fin p))
    (hcard : P.card = k) {K L : Finset (Fin p → Y)} (h : K ⊆ L) :
    copyCols P hcard K ⊆ copyCols P hcard L :=
  Finset.image_subset_image h

/-- **Aux 8 (nonemptiness propagates).**  `∅ ≠ K` of
`10-direct-bridge.tex:136` gives `∅ ≠ K_P`, so the projected pair is a legal
column set of a restriction. -/
lemma copyCols_nonempty {p k : ℕ} {Y : Type*} [DecidableEq Y]
    (P : Finset (Fin p)) (hcard : P.card = k) {K : Finset (Fin p → Y)}
    (hK : K.Nonempty) : (copyCols P hcard K).Nonempty :=
  hK.image _

/-- **Aux 9 (the projection is onto).**  `π_P : (Fin p → Y) ↠ (Fin k → Y)` is
surjective because `e` is injective; this is the general form of
`10-direct-bridge.tex:168--169`, where the frozen proof needs
`π_P : K ↠ K_P`. -/
lemma copyProj_surjective {p k : ℕ} {Y : Type*} [Nonempty Y]
    (P : Finset (Fin p)) (hcard : P.card = k) :
    Function.Surjective (copyProj P hcard : (Fin p → Y) → (Fin k → Y)) := by
  classical
  intro c
  refine ⟨Function.extend (copyEmb P hcard) c (fun _ => Classical.arbitrary Y), ?_⟩
  funext j
  exact (copyEmb_injective P hcard).extend_apply c _ j

/-- **Aux 10 (round trip on the full column space).**  Projecting the full
column space returns the full column space: the exact image is genuinely large,
not a collapsed set.  Used by the nondegenerate witness. -/
lemma copyCols_univ {p k : ℕ} {Y : Type*} [Nonempty Y] [Fintype Y]
    [DecidableEq Y] (P : Finset (Fin p)) (hcard : P.card = k) :
    copyCols P hcard (Finset.univ : Finset (Fin p → Y)) = Finset.univ :=
  Finset.image_univ_of_surjective (copyProj_surjective P hcard)

/-- **Aux 11 (round trip on the full row set).** -/
lemma copyRows_univ {p k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset (Fin p)) (hcard : P.card = k) :
    copyRows P hcard (Finset.univ : Finset (Fin p × X)) = Finset.univ := by
  ext q
  simp

/-- **Aux 12 (every block of the full row set is full).**  A general
equipartition readout used by the nondegenerate witness; it is not about the
pinned construction. -/
lemma isEquipartitionedGE_univ {k : ℕ} {X : Type*} [Fintype X]
    (Q : Finset (Fin k)) :
    IsEquipartitionedGE (Finset.univ : Finset (Fin k × X)) Q
      (Fintype.card X) := by
  classical
  intro q _
  have hcount : (Finset.univ : Finset X).card
      ≤ (Finset.univ.filter fun r : Fin k × X => r.1 = q).card := by
    refine Finset.card_le_card_of_injOn (fun x => (q, x)) ?_ ?_
    · intro x _
      simp
    · intro x _ y _ hxy
      exact congrArg Prod.snd hxy
  simpa using hcount

/-- **Aux 13 (the enumeration is onto `P`, pointwise form).**  Every coordinate
of `P` is enumerated.  This is `copyEmb_image_univ` in the form the pigeonhole
and the row-floor converse need. -/
lemma exists_copyEmb_eq {p k : ℕ} (P : Finset (Fin p)) (hcard : P.card = k)
    {j : Fin p} (hj : j ∈ P) : ∃ i : Fin k, copyEmb P hcard i = j := by
  classical
  have h := copyEmb_image_univ P hcard
  rw [← h] at hj
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi⟩

/-- **Aux 14 (pigeonhole for the exact image).**  `|K| ≤ |K_P| · n^{p-p'}`,
because `y ↦ (π_P(y), y|_{[p]∖P})` is injective: the enumerated coordinates are
recorded by `π_P(y)` (Aux 13) and the rest by the second component.

This is the counting content behind "projection does not increase defect"; it
holds for *every* coordinate set, with no density hypothesis. -/
lemma card_le_card_copyCols_mul {p k : ℕ} {Y : Type*} [Fintype Y]
    [DecidableEq Y] (P : Finset (Fin p)) (hcard : P.card = k)
    (K : Finset (Fin p → Y)) :
    K.card ≤ (copyCols P hcard K).card * Fintype.card Y ^ (p - k) := by
  classical
  have hcompl : Fintype.card {j : Fin p // j ∉ P} = p - k := by
    rw [Fintype.card_subtype]
    have hfil : (Finset.univ.filter fun j : Fin p => j ∉ P) = Pᶜ := by
      ext j
      simp
    rw [hfil, Finset.card_compl, hcard, Fintype.card_fin]
  have hle := Finset.card_le_card_of_injOn
    (f := fun y : Fin p → Y =>
      (copyProj P hcard y, fun j : {j : Fin p // j ∉ P} => y j.1))
    (s := K)
    (t := (copyCols P hcard K) ×ˢ
      (Finset.univ : Finset ({j : Fin p // j ∉ P} → Y)))
    (by
      intro y hy
      simp only [Finset.mem_coe] at hy
      exact Finset.mem_product.mpr
        ⟨copyProj_mem_copyCols P hcard hy, Finset.mem_univ _⟩)
    (by
      intro y _ z _ h
      have h1 : copyProj P hcard y = copyProj P hcard z := congrArg Prod.fst h
      have h2 : (fun j : {j : Fin p // j ∉ P} => y j.1)
          = fun j : {j : Fin p // j ∉ P} => z j.1 := congrArg Prod.snd h
      funext j
      by_cases hj : j ∈ P
      · obtain ⟨i, hi⟩ := exists_copyEmb_eq P hcard hj
        have hcong := congrFun h1 i
        simp only [copyProj] at hcong
        rw [hi] at hcong
        exact hcong
      · exact congrFun h2 ⟨j, hj⟩)
  rwa [Finset.card_product, Finset.card_univ, Fintype.card_fun, hcompl] at hle

/-- **Aux 15 (defect transport).**  The exact image never has a larger
logarithmic column defect than its parent: `Def_{p'}(K_P) ≤ Def_p(K)`.

Direction matters — the reverse is false — and the nonemptiness binder is
load-bearing: at `K = ∅` the readout `ln(n^{p'}/|K_P|)` degenerates exactly as
`BRIDGE-DEFECT-001` recorded for its own carrier.  This is the crude
counting bound, *not* the entropy-averaging statement of
`B-bridge-details.tex:18--21`; see GAP-EXPOSED 1. -/
lemma columnDefect_copyCols_le {p k : ℕ} {Y : Type*} [Fintype Y]
    [DecidableEq Y] (P : Finset (Fin p)) (hcard : P.card = k)
    {K : Finset (Fin p → Y)} (hK : K.Nonempty) (hY : 1 ≤ Fintype.card Y) :
    columnDefect (copyCols P hcard K) ≤ columnDefect K := by
  classical
  have hkp : k ≤ p := by
    have h := Finset.card_le_univ P
    rw [hcard, Fintype.card_fin] at h
    exact h
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hn0 : (0 : ℝ) < (Fintype.card Y : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hKpos : (0 : ℝ) < (K.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hK
  have hIpos : (0 : ℝ) < ((copyCols P hcard K).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (copyCols_nonempty P hcard hK)
  have hcount : (K.card : ℝ)
      ≤ ((copyCols P hcard K).card : ℝ) * (Fintype.card Y : ℝ) ^ (p - k) := by
    exact_mod_cast card_le_card_copyCols_mul P hcard K
  have hsplit : (Fintype.card Y : ℝ) ^ p
      = (Fintype.card Y : ℝ) ^ k * (Fintype.card Y : ℝ) ^ (p - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkp]
  have hle : (Fintype.card Y : ℝ) ^ k / ((copyCols P hcard K).card : ℝ)
      ≤ (Fintype.card Y : ℝ) ^ p / (K.card : ℝ) := by
    rw [div_le_div_iff₀ hIpos hKpos]
    calc (Fintype.card Y : ℝ) ^ k * (K.card : ℝ)
        ≤ (Fintype.card Y : ℝ) ^ k
            * (((copyCols P hcard K).card : ℝ)
              * (Fintype.card Y : ℝ) ^ (p - k)) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = (Fintype.card Y : ℝ) ^ p * ((copyCols P hcard K).card : ℝ) := by
          rw [hsplit]; ring
  unfold columnDefect
  exact Real.log_le_log (div_pos (pow_pos hn0 k) hIpos) hle

/-! ## Part 3: the two provenance clauses and the three frozen conclusions -/

/-- **Row provenance** (`10-direct-bridge.tex:174`, the row map
`(j,x) ↦ (e(j),x)`): every row of `R_{*,P}` comes from the `e`-fibre of the
fixed parent `R_*`. -/
lemma copyRows_provenance {p k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset (Fin p)) (hcard : P.card = k) (Rstar : Finset (Fin p × X)) :
    ∀ a ∈ copyRows P hcard Rstar, (copyEmb P hcard a.1, a.2) ∈ Rstar := by
  intro a ha
  rwa [mem_copyRows] at ha

/-- **Column provenance** (`10-direct-bridge.tex:170--172`): every column of
`K_P` agrees, on all of `P` read through `e`, with an actual column of `K`. -/
lemma copyCols_provenance {p k : ℕ} {Y : Type*} [DecidableEq Y]
    (P : Finset (Fin p)) (hcard : P.card = k) (K : Finset (Fin p → Y)) :
    ∀ c' ∈ copyCols P hcard K, ∃ c ∈ K, ∀ j : Fin k,
      c' j = c (copyEmb P hcard j) := by
  intro c' hc'
  rw [mem_copyCols] at hc'
  obtain ⟨y, hy, hyc⟩ := hc'
  exact ⟨y, hy, fun j => by rw [← hyc]; rfl⟩

/-- **Conclusion 1: the complexity comparison**
(`10-direct-bridge.tex:155--161`): the extracted matrix
`extract(Int_k(W), R_{*,P}, K_P)` has communication complexity at most that of
the row-restricted parent `(R_*, K)`.

The kernel-checked `EthBridge.projected_subgame_le`
(`vendor/npc-cc/EthBridge/Entry.lean:500`) is *consumed*: it is the frozen
proof's own pair of injections — the row map `(j,x) ↦ (e(j),x)` and a section
`σ_P` of the column projection — together with the entry computation of frozen
lines 176--182.  It is a generic `D`-comparison, not `NPCC.coord_projection`,
so `D-inherited-contracts.tex:275--276` is respected. -/
theorem copyRestriction_le {X Y : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (W : X → Y → Bool) {p k : ℕ} (P : Finset (Fin p))
    (hcard : P.card = k) (Rstar : Finset (Fin p × X))
    (K : Finset (Fin p → Y)) :
    D (subgame (interlaceFun W k) (copyRows P hcard Rstar)
        (copyCols P hcard K))
      ≤ D (subgame (interlaceFun W p) Rstar K) :=
  EthBridge.projected_subgame_le W (copyEmb P hcard)
    (copyRows_provenance P hcard Rstar) (copyCols_provenance P hcard K)

/-- **Conclusion 2: the fibre count** (`10-direct-bridge.tex:161--163`): if
every coordinate in `P` has at least `A` surviving rows in `R_*`, then every
outer block of `R_{*,P}` has at least `A` rows. -/
theorem copyRestriction_rowFloor {p k : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] (P : Finset (Fin p)) (hcard : P.card = k)
    (Rstar : Finset (Fin p × X)) (A : ℕ)
    (hrow : IsEquipartitionedGE Rstar P A) :
    IsEquipartitionedGE (copyRows P hcard Rstar) Finset.univ A := by
  classical
  intro j _
  have hj := hrow (copyEmb P hcard j) (copyEmb_mem P hcard j)
  refine le_trans hj (Finset.card_le_card_of_injOn (fun r => (j, r.2)) ?_ ?_)
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
    obtain ⟨hrR, hr1⟩ := hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · simp only [mem_copyRows]
      simpa [← hr1] using hrR
    · simp
  · intro r hr s hs hrs
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr hs
    have hrs' : (j, r.2) = (j, s.2) := hrs
    have hr2 : r.2 = s.2 := by simpa using hrs'
    exact Prod.ext_iff.mpr ⟨hr.2.trans hs.2.symm, hr2⟩

/-- **Conclusion 2 is not free: the converse holds too.**  The block floor of
`R_{*,P}` is *equivalent* to the per-coordinate floor of `R_*` on `P`, so the
frozen hypothesis "every coordinate in `P` has at least `A` surviving rows"
(line 162) is exactly what the conclusion needs — it is neither an over-strong
premise nor a conclusion available for free.

Together with `copyRestriction_rowFloor_premise_bites` this is the
floor-restriction pole: a parent whose `P`-blocks are thin fails the premise,
and by this equivalence its projection fails the conclusion. -/
theorem copyRows_isEquipartitionedGE_iff {p k : ℕ} {X : Type*} [Fintype X]
    [DecidableEq X] (P : Finset (Fin p)) (hcard : P.card = k)
    (Rstar : Finset (Fin p × X)) (A : ℕ) :
    IsEquipartitionedGE (copyRows P hcard Rstar)
        (Finset.univ : Finset (Fin k)) A
      ↔ IsEquipartitionedGE Rstar P A := by
  classical
  refine ⟨?_, copyRestriction_rowFloor P hcard Rstar A⟩
  intro h q hq
  obtain ⟨i, hi⟩ := exists_copyEmb_eq P hcard hq
  refine le_trans (h i (Finset.mem_univ i))
    (Finset.card_le_card_of_injOn (fun r => (q, r.2)) ?_ ?_)
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
    obtain ⟨hrR, hr1⟩ := hr
    rw [mem_copyRows] at hrR
    rw [hr1, hi] at hrR
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hrR, trivial⟩
  · intro r hr s hs hrs
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr hs
    have hrs' : (q, r.2) = (q, s.2) := hrs
    have hr2 : r.2 = s.2 := by simpa using hrs'
    exact Prod.ext_iff.mpr ⟨hr.2.trans hs.2.symm, hr2⟩

/-- **Conclusion 3: exactness** (`10-direct-bridge.tex:163--164`): the column
set of the extracted matrix is the exact image `K_P`, characterized by the two
directions of `mem_copyCols`. -/
theorem copyRestriction_exactImage {p k : ℕ} {Y : Type*} [DecidableEq Y]
    (P : Finset (Fin p)) (hcard : P.card = k) (K : Finset (Fin p → Y)) :
    ∀ c : Fin k → Y,
      c ∈ copyCols P hcard K ↔ ∃ y ∈ K, copyProj P hcard y = c :=
  fun c => mem_copyCols P hcard K c

/-! ## Part 4: `lem:copy-restriction` as one closed statement

The frozen binder list of `10-direct-bridge.tex:133--144` and the frozen
conclusion of lines 155--164, with the pinned data of
`eq:copy-restriction-data` substituted. -/

/-- **`lem:copy-restriction`** (`10-direct-bridge.tex:131--165`), as a
named-def claim about the pinned data of `eq:copy-restriction-data`.

Binders, in the frozen order: the matrix `W`, the parent width `p ≥ 1`, the
ambient row and column sets `R`, `∅ ≠ K` of a restriction of `Int_p(W)`, the
row restriction `∅ ≠ R_* ⊆ R`, the nonempty coordinate set `P` with
`|P| = k = p'`, and the per-coordinate row floor `A`.

Conclusion, in the frozen order:
1. the complexity comparison of lines 159--161;
2. the fibre count of lines 161--163;
3. the exactness of lines 163--164;
4. nonemptiness of `K_P`, which lines 136 and 151 require of a legal column
   set.

This is *not* an existential: an existential reading is satisfied by a
singleton column set (`copyCols_refutes_candidateB`), which is exactly what
lines 163--164 rule out. -/
theorem copyRestriction {X Y : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (W : X → Y → Bool) {p k : ℕ} (_hp : 1 ≤ p)
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (Rstar : Finset (Fin p × X)) (_hRstar : Rstar.Nonempty)
    (_hsub : Rstar ⊆ R) (P : Finset (Fin p)) (_hP : P.Nonempty)
    (hcard : P.card = k) (A : ℕ) (hrow : IsEquipartitionedGE Rstar P A) :
    D (subgame (interlaceFun W k) (copyRows P hcard Rstar)
          (copyCols P hcard K))
        ≤ D (subgame (interlaceFun W p) Rstar K)
      ∧ IsEquipartitionedGE (copyRows P hcard Rstar) Finset.univ A
      ∧ (∀ c : Fin k → Y,
          c ∈ copyCols P hcard K ↔ ∃ y ∈ K, copyProj P hcard y = c)
      ∧ (copyCols P hcard K).Nonempty :=
  ⟨copyRestriction_le W P hcard Rstar K,
    copyRestriction_rowFloor P hcard Rstar A hrow,
    copyRestriction_exactImage P hcard K,
    copyCols_nonempty P hcard hK⟩

/-- The frozen ambient row set `R` and the guard `R_* ⊆ R` restrict nothing:
`R = R_*` is legal, so keeping the frozen binders does not turn
`copyRestriction` into an over-strong premise bundle. -/
lemma copyRestriction_binders_satisfiable {p : ℕ} {X : Type*}
    (Rstar : Finset (Fin p × X)) : Rstar ⊆ Rstar :=
  Finset.Subset.refl Rstar

/-! ## Part 5: the trivial-witness refutation and the nondegenerate inhabitant

`10-direct-bridge.tex:163--164` says the column set is "the exact image `K_P`,
not an arbitrarily chosen subset of that image".  The first theorem below shows
that the existential reading of the lemma cannot see that difference; the
second exhibits a legal instance where the difference is `4` columns against
`1`. -/

/-- **Candidate B is refuted.**  Whenever the exact image has at least two
columns, there is a *strictly smaller* column set — the singleton — that still
satisfies every clause of the existential reading: it is nonempty, it has
column provenance into `K`, and its subgame is no harder than the parent.  So
an existential statement would not pin `K_P`, and the deliverable has to be the
named-def claim `copyRestriction`. -/
theorem copyCols_refutes_candidateB {X Y : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (W : X → Y → Bool) {p k : ℕ} (P : Finset (Fin p))
    (hcard : P.card = k) (Rstar : Finset (Fin p × X))
    (K : Finset (Fin p → Y)) (h2 : 2 ≤ (copyCols P hcard K).card) :
    ∃ K' : Finset (Fin k → Y),
      K'.Nonempty
      ∧ K' ⊆ copyCols P hcard K
      ∧ K' ≠ copyCols P hcard K
      ∧ (∀ c' ∈ K', ∃ c ∈ K, ∀ j : Fin k, c' j = c (copyEmb P hcard j))
      ∧ D (subgame (interlaceFun W k) (copyRows P hcard Rstar) K')
          ≤ D (subgame (interlaceFun W p) Rstar K) := by
  classical
  obtain ⟨c₀, hc₀⟩ : (copyCols P hcard K).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsub : ({c₀} : Finset (Fin k → Y)) ⊆ copyCols P hcard K := by
    simpa using hc₀
  have hprov : ∀ c' ∈ ({c₀} : Finset (Fin k → Y)), ∃ c ∈ K,
      ∀ j : Fin k, c' j = c (copyEmb P hcard j) := by
    intro c' hc'
    rw [Finset.mem_singleton] at hc'
    subst hc'
    exact copyCols_provenance P hcard K c' hc₀
  refine ⟨{c₀}, ⟨c₀, Finset.mem_singleton_self c₀⟩, hsub, ?_, hprov, ?_⟩
  · intro hEq
    have : ({c₀} : Finset (Fin k → Y)).card = (copyCols P hcard K).card := by
      rw [hEq]
    rw [Finset.card_singleton] at this
    omega
  · exact EthBridge.projected_subgame_le W (copyEmb P hcard)
      (copyRows_provenance P hcard Rstar) hprov

/-- The pinned nondegenerate coordinate set: a **proper** two-element subset of
three parent coordinates, so the projection is a genuine projection
(`k = 2 < 3 = p`) rather than the identity. -/
def sampleP : Finset (Fin 3) := {0, 2}

/-- `|P| = 2` at the pinned instance. -/
lemma sampleP_card : sampleP.card = 2 := by decide

/-- The pinned coordinate set is a proper subset of all three coordinates. -/
lemma sampleP_ssubset : sampleP ⊂ (Finset.univ : Finset (Fin 3)) := by decide

/-- **Nondegenerate inhabitant at legal parameter values.**  At `p = 3`,
`P = {0,2}` (so `k = 2 < 3`), `X = Fin 2`, `Y = Bool`, `R_* = ` all rows and
`K = ` all columns:

* the coordinate set is a proper subset, so the lemma is used where it actually
  projects;
* every block of the projected row set has `2` rows, so the row floor is `2`,
  not `0`;
* the exact image has `4` columns out of the `8` parent columns — neither
  everything nor the singleton that `copyCols_refutes_candidateB` produces.

`copyRestriction_fires_at_sample` then discharges **every** binder of
`copyRestriction` at exactly this instance, so the premise list is satisfiable
at legal values. -/
theorem copyRestriction_fires_nondegenerate :
    sampleP ⊂ (Finset.univ : Finset (Fin 3))
      ∧ copyRows sampleP sampleP_card
          (Finset.univ : Finset (Fin 3 × Fin 2)) = Finset.univ
      ∧ IsEquipartitionedGE
          (copyRows sampleP sampleP_card
            (Finset.univ : Finset (Fin 3 × Fin 2))) Finset.univ 2
      ∧ (copyCols sampleP sampleP_card
          (Finset.univ : Finset (Fin 3 → Bool))).card = 4
      ∧ (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by
  classical
  refine ⟨sampleP_ssubset, copyRows_univ sampleP sampleP_card, ?_, ?_, ?_⟩
  · rw [copyRows_univ sampleP sampleP_card]
    simpa using
      (isEquipartitionedGE_univ (X := Fin 2) (Finset.univ : Finset (Fin 2)))
  · rw [copyCols_univ sampleP sampleP_card, Finset.card_univ]
    simp
  · rw [Finset.card_univ]
    simp

/-- **`copyRestriction` fires at the nondegenerate instance.**  Every binder of
the frozen lemma — `p ≥ 1`, the ambient `R` with `R_* ⊆ R`, `∅ ≠ K`,
`∅ ≠ R_*`, `∅ ≠ P`, `|P| = k` and the row floor `A = 2` — is discharged at
`p = 3`, `P = {0,2}`, `X = Fin 2`, `Y = Bool`, for an arbitrary matrix `W`.
The premise list is therefore satisfiable at legal values, and not by a
degenerate choice: `k = 2 < 3 = p`, `A = 2 > 0`, and the exact image has `4` of
the `8` parent columns. -/
theorem copyRestriction_fires_at_sample (W : Fin 2 → Bool → Bool) :
    D (subgame (interlaceFun W 2)
          (copyRows sampleP sampleP_card (Finset.univ : Finset (Fin 3 × Fin 2)))
          (copyCols sampleP sampleP_card (Finset.univ : Finset (Fin 3 → Bool))))
        ≤ D (subgame (interlaceFun W 3)
          (Finset.univ : Finset (Fin 3 × Fin 2))
          (Finset.univ : Finset (Fin 3 → Bool)))
      ∧ IsEquipartitionedGE
          (copyRows sampleP sampleP_card
            (Finset.univ : Finset (Fin 3 × Fin 2))) Finset.univ 2
      ∧ (∀ c : Fin 2 → Bool,
          c ∈ copyCols sampleP sampleP_card
              (Finset.univ : Finset (Fin 3 → Bool))
            ↔ ∃ y ∈ (Finset.univ : Finset (Fin 3 → Bool)),
                copyProj sampleP sampleP_card y = c)
      ∧ (copyCols sampleP sampleP_card
          (Finset.univ : Finset (Fin 3 → Bool))).Nonempty :=
  copyRestriction W (by norm_num) Finset.univ Finset.univ
    ⟨fun _ => true, Finset.mem_univ _⟩ Finset.univ
    ⟨(0, 0), Finset.mem_univ _⟩ (Finset.Subset.refl _) sampleP (by decide)
    sampleP_card 2
    (by simpa using isEquipartitionedGE_univ (X := Fin 2) sampleP)

/-- The pinned increasing enumeration reads `e(0) = 0` and `e(1) = 2`.

It is derived, not computed: `copyEmb_mem` puts both values in `{0,2}` and
`copyEmb_strictMono` orders them.  An arbitrary equivalence `[2] ≃ {0,2}` would
also permit `e(0) = 2`, `e(1) = 0`; the frozen "increasing" of
`10-direct-bridge.tex:144` is what excludes it, and this lemma is where that
exclusion is visible. -/
lemma sampleEmb :
    copyEmb sampleP sampleP_card 0 = 0 ∧ copyEmb sampleP sampleP_card 1 = 2 := by
  have hmem : ∀ j : Fin 3, j ∈ sampleP → j = 0 ∨ j = 2 := by decide
  have h0 := hmem _ (copyEmb_mem sampleP sampleP_card 0)
  have h1 := hmem _ (copyEmb_mem sampleP sampleP_card 1)
  have hlt : copyEmb sampleP sampleP_card 0 < copyEmb sampleP sampleP_card 1 :=
    copyEmb_strictMono sampleP sampleP_card (by decide)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rw [h0, h1] at hlt ⊢ <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd hlt (by decide)

/-- The projection at the pinned instance keeps coordinates `0` and `2`. -/
lemma copyProj_sample (y : Fin 3 → Bool) :
    copyProj sampleP sampleP_card y = ![y 0, y 2] := by
  obtain ⟨h0, h1⟩ := sampleEmb
  funext j
  fin_cases j
  · simp [copyProj, h0]
  · simp [copyProj, h1]

/-- A **proper** row restriction: five of the six rows of `[3] × Fin 2`, thin at
coordinate `1` and full at the two coordinates of `P`. -/
def sampleRows : Finset (Fin 3 × Fin 2) := {(0, 0), (0, 1), (1, 0), (2, 0), (2, 1)}

/-- A **proper** column carrier: the four columns with `y(0) = y(2)`, whose
exact image is the two columns with `c(0) = c(1)`. -/
def sampleCols : Finset (Fin 3 → Bool) := Finset.univ.filter fun y => y 0 = y 2

/-- The exact image at the proper instance has `2` columns, out of `4` in the
child column space and `4` in the parent carrier: the projection genuinely
collapses, and the image is neither everything nor a singleton. -/
lemma sampleCols_image_card :
    (copyCols sampleP sampleP_card sampleCols).card = 2 := by
  have hcongr : copyCols sampleP sampleP_card sampleCols
      = sampleCols.image fun y => ![y 0, y 2] := by
    unfold copyCols
    exact Finset.image_congr fun y _ => copyProj_sample y
  rw [hcongr]
  decide

/-- **Nondegenerate inhabitant at a proper restriction.**  `p = 3`,
`P = {0,2}` proper, `R_* = sampleRows` a **proper** subset of the ambient rows
(so the ambient binder `R_* ⊆ R` is used at a strict inclusion), and
`K = sampleCols` a **proper** nonempty column carrier whose exact image is
strictly smaller than the child column space.  Every conclusion of
`copyRestriction` is delivered here, together with the defect transport of
Aux 15.

This is the LANE-GATE 3 reading the earlier `Finset.univ` instance cannot give:
there `R_*` and `K` were the full carriers, so no clause was tested at a
strict restriction. -/
theorem copyRestriction_fires_proper (W : Fin 2 → Bool → Bool) :
    sampleRows ⊂ (Finset.univ : Finset (Fin 3 × Fin 2))
      ∧ sampleCols ⊂ (Finset.univ : Finset (Fin 3 → Bool))
      ∧ sampleCols.card = 4
      ∧ (copyCols sampleP sampleP_card sampleCols).card = 2
      ∧ D (subgame (interlaceFun W 2)
            (copyRows sampleP sampleP_card sampleRows)
            (copyCols sampleP sampleP_card sampleCols))
          ≤ D (subgame (interlaceFun W 3) sampleRows sampleCols)
      ∧ IsEquipartitionedGE
          (copyRows sampleP sampleP_card sampleRows) Finset.univ 2
      ∧ (∀ c : Fin 2 → Bool,
          c ∈ copyCols sampleP sampleP_card sampleCols
            ↔ ∃ y ∈ sampleCols, copyProj sampleP sampleP_card y = c)
      ∧ (copyCols sampleP sampleP_card sampleCols).Nonempty
      ∧ columnDefect (copyCols sampleP sampleP_card sampleCols)
          ≤ columnDefect sampleCols := by
  have hK : sampleCols.Nonempty := by decide
  have hR : sampleRows.Nonempty := by decide
  have hrow : IsEquipartitionedGE sampleRows sampleP 2 := by
    change ∀ q ∈ sampleP, 2 ≤ (sampleRows.filter fun r => r.1 = q).card
    decide
  obtain ⟨hle, hfloor, hexact, hne⟩ :=
    copyRestriction W (by norm_num) (Finset.univ : Finset (Fin 3 × Fin 2))
      sampleCols hK sampleRows hR (Finset.subset_univ _) sampleP (by decide)
      sampleP_card 2 hrow
  exact ⟨by decide, by decide, by decide, sampleCols_image_card, hle, hfloor,
    hexact, hne,
    columnDefect_copyCols_le sampleP sampleP_card hK (by decide)⟩

/-- A row restriction that is **thin at a coordinate of `P`**: coordinate `0`
retains a single row. -/
def thinRows : Finset (Fin 3 × Fin 2) := {(0, 0), (1, 0), (1, 1), (2, 0), (2, 1)}

/-- **Floor-restriction pole.**  The frozen premise "every coordinate in `P`
has at least `A` surviving rows in `R_*`" (`10-direct-bridge.tex:161--162`)
genuinely restricts: `thinRows` fails it at `A = 2`, and by
`copyRows_isEquipartitionedGE_iff` its projection fails the conclusion.  So
the floor clause of `copyRestriction` is not a statement that holds for every
row restriction, and it is not derivable without the premise. -/
theorem copyRestriction_rowFloor_premise_bites :
    ¬ IsEquipartitionedGE thinRows sampleP 2
      ∧ ¬ IsEquipartitionedGE (copyRows sampleP sampleP_card thinRows)
          (Finset.univ : Finset (Fin 2)) 2 := by
  have h : ¬ IsEquipartitionedGE thinRows sampleP 2 := by
    change ¬ ∀ q ∈ sampleP, 2 ≤ (thinRows.filter fun r => r.1 = q).card
    decide
  refine ⟨h, fun hc => h ?_⟩
  exact (copyRows_isEquipartitionedGE_iff sampleP sampleP_card thinRows 2).mp hc

/-- The pinned instance is exactly where `copyCols_refutes_candidateB` bites:
the exact image has `4` columns, so the degenerate singleton witness is
strictly smaller. -/
theorem copyRestriction_candidateB_bites :
    2 ≤ (copyCols sampleP sampleP_card
      (Finset.univ : Finset (Fin 3 → Bool))).card := by
  have h := copyRestriction_fires_nondegenerate
  omega

/-! ## Part 6: the wiring test

The composition that discharges `DirectOutputLower.entryLevelStep`'s explicit
carrier binders from the pinned construction of this module, following
`10-direct-bridge.tex:465--469`: "Choose any `p_t` good copies and project the
column set to them ... By `lem:copy-restriction`, the exact projected image and
the rows from these good copies form a literal restriction of `Int_{p_t}(W)`
inside the selected state." -/

/-- **The entry level step, driven by the exact-image copy restriction**
(`10-direct-bridge.tex:465--482`).

Given a parent restriction `(R_*, K)` of `Int_Q(W)` and a set `P` of exactly
`p_t = entryCopyCount b_out δ_U t` good copies — each holding at least the row
floor `A_{a_t}` — `lem:copy-restriction` supplies the literal `p_t`-copy
restriction that `entryLevelStep` previously took as a bare binder, and the
complexity comparison transports the conclusion back to the parent.

Both of `entryLevelStep`'s carrier binders `R`, `K` and both of its carrier
premises `hK`, `hrows` are discharged here by the pinned `copyRows` and
`copyCols`; nothing is weakened, and the two clauses of `eq:direct-input`
remain the explicit binders `hNear` and `hInput`.

The defect premise is stated on the exact image `K_P`, not on the parent: the
frozen density-preservation step of lines 465--467 is
`NPCC.coord_projection`'s, already banked as `INHERIT-001`, and
`lem:copy-restriction` itself claims nothing about `|K_P|` (GAP-EXPOSED 1). -/
theorem entryLevelStep_ofCopyRestriction {X Y : Type*} [Fintype X]
    [Fintype Y] [DecidableEq Y] (W : X → Y → Bool)
    (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2) (hb : 1 ≤ bout)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
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
    (hdefect : columnDefect (copyCols P hcard K) ≤ entryDefectL bout) :
    CW + entryLevelA bout δU t ≤ D (subgame (interlaceFun W Q) Rstar K) := by
  classical
  exact le_trans
    (entryLevelStep W CW bout ht hb hδ0 hδ1 hθ0 hgate hmargin hX hY hCW
      hNear hInput (copyRows P hcard Rstar) (copyCols P hcard K)
      (copyCols_nonempty P hcard hK)
      (copyRestriction_rowFloor P hcard Rstar
        (rowFloor (Fintype.card X) θ (entryLevelA bout δU t)) hrows)
      hdefect)
    (copyRestriction_le W P hcard Rstar K)

/-- **The same step with the defect binder on the parent carrier.**

`10-direct-bridge.tex:465--467` reads the defect bound off the *parent* column
set and transports it to the projection.  The transport used here is the
elementary counting bound `columnDefect_copyCols_le` (Aux 15), which holds for
every coordinate set with no density hypothesis; the frozen sentence's stronger
route — normalized density is preserved, hence defect at most `L` — is
`NPCC.coord_projection`'s and remains GAP-EXPOSED 1.

This corollary is strictly *weaker* than
`entryLevelStep_ofCopyRestriction`, since `Def(K_P) ≤ Def(K)`: it assumes the
bound on the larger defect.  Both are recorded because the consumer supplies
whichever of the two it has. -/
theorem entryLevelStep_ofCopyRestriction_ofParentDefect {X Y : Type*}
    [Fintype X] [Fintype Y] (W : X → Y → Bool)
    (CW bout : ℕ) {δU θ : ℝ} {t : ℕ} (ht : t ≤ 2) (hb : 1 ≤ bout)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ)
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
    (hdefect : columnDefect K ≤ entryDefectL bout) :
    CW + entryLevelA bout δU t ≤ D (subgame (interlaceFun W Q) Rstar K) := by
  classical
  exact entryLevelStep_ofCopyRestriction W CW bout ht hb hδ0 hδ1 hθ0 hgate
    hmargin hX hY hCW hNear hInput P hcard Rstar K hK hrows
    (le_trans (columnDefect_copyCols_le P hcard hK hY) hdefect)

/-- **Non-vacuity of the composition: it fires at the banked first entry-gate
witness.**

`b_out = 1`, `δ_U = 1/60`, `θ = 1/192000`, `C_W = 3` — the parameters carried
by `DirectOutputLower.directOutputLower_fires_first_witness` — where
`Q = Qwidth 1 (1/60) = 8192` and the copy count `p_0 = entryCopyCount 1 (1/60) 0`
satisfies `4096 < p_0 < 8192`.  So a coordinate set of exactly the right size
exists and is a **proper** subset of the outer interlace: the wiring is used
where `lem:copy-restriction` actually projects, not at `P = [Q]`.

`X`, `Y` and `W` stay universally quantified and the two clauses of
`eq:direct-input` stay hypotheses — they have no exhibited inhabitant and can
have none until Stages 1--4 land, exactly as
`DirectOutputLower`'s own conditional firing witnesses record.  What is
established is that every *other* binder of
`entryLevelStep_ofCopyRestriction_ofParentDefect` — the depth, the deletion
tolerance, the row threshold, both entry gates, the width `Q`, and the
cardinality link `|P| = p_t` — is simultaneously satisfiable at legal frozen
parameters. -/
theorem entryLevelStep_ofCopyRestriction_fires_first_witness {X Y : Type*}
    [Fintype X] [Fintype Y] (W : X → Y → Bool)
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
          columnDefect K ≤ entryDefectL 1 →
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
  · intro Rstar K hK hrows hdefect
    exact entryLevelStep_ofCopyRestriction_ofParentDefect W 3 1 (δU := 1 / 60)
      (θ := 1 / 192000) (t := 0) (by norm_num) (le_refl 1) (by norm_num)
      (by norm_num) (by norm_num) hgate hmargin hX hY (le_refl 3) hNear hInput
      P hPcard Rstar K hK hrows hdefect

end EthInapproximability.ParameterizedNP.CopyRestriction
