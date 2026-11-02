import EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-!
# Parameterized NP route: the guarded-source constructor and slab layer

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `sec:source`, *A deletion-stable
  guarded source*, in the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/04-guarded-source.tex`, **lines 386--673**.  The
  anchors traced here are
  * `def:guarded-source-constructor` (lines 386--428), including `q_2`, the
    zero-based rank embedding `ι`, and the entry equation
    `eq:guarded-source-slab-entry` (line 419);
  * `def:guarded-source-slabs` (lines 430--439);
  * `lem:guarded-source-slab-decomposition` (lines 441--457) with its proof;
  * `lem:guarded-source-active-slot` (lines 459--476) with its proof;
  * `def:guarded-source-retention` (lines 478--500), including
    `eq:guarded-source-deletion-hypotheses` (line 496);
  * `thm:guarded-source` (lines 502--537) with its proof (lines 539--606),
    conclusions S1, S2, S3 and `eq:guarded-source-active-incidences` (line 532);
  * `cor:guarded-source-encoded-size` (lines 608--657) with its proof,
    including `eq:guarded-source-encoded-length` (line 643) and
    `eq:guarded-source-source-size` (line 653).

  Everything **before** line 386 -- the graph layer, the packing vocabulary, the
  unslabbed copy `U(G,s)`, the public deletion fractions,
  `lem:source-completeness` and `lem:source-one-copy` -- is banked in
  `GuardedSourceGraph.lean` (`SOURCE-GRAPH-001`, tranche `cc-t2a`/`cc-t2a-r1`)
  and is **consumed by pin, never restated**.
* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`
  `A-stage4-details.tex`, subsection `sec:paper-guarded-source-details`), one
  reader item per declaration, no **item** claimed twice here or in any earlier
  row.  Two physical lines carry more than one item, and are split explicitly
  rather than reclaimed: line 64 holds both "Every padding coordinate is zero"
  (claimed here) and "Each coordinate is active on at most `s` items" (banked,
  `SOURCE-GRAPH-001`); and each sentence of `thm:paper-guarded-source` holds a
  promise clause already banked as `SourceYES` / `SourceNO` together with a
  conclusion claimed here.  The list:
  * `eq:paper-guarded-carriers` (label line 30), first half, line 26,
    `I(G,s) = [4s] × (V ⊔ [s-3])` -> `SlabRow`; second half, lines 28--29,
    `Q_real(G,s) = [4s] × (E ⊔ Inc(G))` -> `SlabCoord`;
  * `eq:paper-guarded-q2` (label line 36), first half, line 34,
    `q_2 = min{2^r : 12 s m_G ≤ 2^r}` -> `q2`; second half, line 35, the
    two-sided estimate `12 s m_G ≤ q_2 < 24 s m_G` -> its two inequalities
    `card_le_q2` and `q2_lt`;
  * `eq:paper-guarded-edge-evaluator` (label line 54) and
    `eq:paper-guarded-incidence-evaluator` (label line 62), the two
    slab-guarded evaluator displays, are the two branches of the single frozen
    `eq:guarded-source-slab-entry` and are jointly matched to the single
    characterisation `guardedRow_iota`, which is exactly their common `r = r'`
    clause.  The banked `unslabbedRow` deliberately claims neither, precisely
    because it lacks that guard, and the definition `guardedRow` claims none
    either, the reader having no definitional display for `v` apart from these
    two evaluator equations;
  * line 64, "Every padding coordinate is zero" -> `guardedRow_padding`;
  * the `ζ = γ/24` half of `eq:paper-source-stability-constants` (display line
    72, label line 73) -> `zeta`.  The `δ_v` half is banked as
    `GuardedSourceGraph.EndpointGraph.deltaV` and is not reclaimed;
  * `thm:paper-guarded-source`, first sentence, **conclusion half** (lines
    78--79, "the items allow an `s`-bin partition with at most one active item
    in every bin and coordinate") -> S2, `guardedSource_legal_of_sourceYES`.
    Its promise clause on line 78, "If `G` is three-colourable", is **not**
    reclaimed: the banked row `SOURCE-GRAPH-001` already assigns it to
    `GuardedSourceGraph.SourceYES`;
  * `thm:paper-guarded-source`, second sentence, **deletion clauses and
    conclusion** (lines 81--84, "after deleting fewer than `(s/2)δ_v(G)N_G`
    vertex items and fewer than `s/2` blocker items, every partition of the
    retained items into `s` bins has overload-plus-neutral witnesses on at
    least `ζ q_2` coordinates") -> `RetentionOK` (the two deletion clauses) and
    S1, `guardedSource_wit_of_sourceNO` (the conclusion).  Its promise clause
    on lines 79--80, "if every three-colouring of `G` makes at least `γ m_G`
    edge occurrences monochromatic", is **not** reclaimed either: the banked
    row already assigns it to `GuardedSourceGraph.SourceNO`;
  * `eq:paper-guarded-size` (label line 90), first half, line 88,
    `|I(G,s)| = 4s(N_G+s-3)` -> `card_slabRow`; second half, line 89,
    `|Q_real(G,s)| = 12 s m_G` -> `card_slabCoord`.  This locus was explicitly
    **declined** by the banked row `SOURCE-GRAPH-001` (its unslabbed counts are
    different values), so it is unclaimed until now;
  * `eq:paper-guarded-active-incidences` (label line 95), `4 s m_G (3s-5)`
    -> `card_activeIncidences`;
  * `eq:paper-guarded-encoding-size` (label line 101),
    `s^2 m_G(log(N_G+s+2)+log(s m_G+2))` -> `encodedLength_le`.

  **Reader items deliberately declined, with the reason recorded** (the
  precedent is `CLOCK-001`/`cc-t1x`/`cc-t1y-r1` in the crosswalk):
  * lines 64--65, "Each coordinate is active on at most `s` items", is
    **already assigned** to `GuardedSourceGraph.card_activeRows_le` by the
    banked row `SOURCE-GRAPH-001`.  The slabbed refinement proved here
    (`card_activeSlot_le`, `lem:guarded-source-active-slot`) therefore claims
    **no** reader item, since no reader line may be assigned twice.  The same
    holds for its exact per-coordinate values `card_activeSlot_edge` (`s-1`)
    and `card_activeSlot_guard` (`s-2`).
  * lines 38--45, the reader's rank embedding, is stated **one-based**
    (`ι(x) = 1 + |{y < x}|`) whereas the frozen autoformalization anchor at
    04:405--409 is **zero-based** (`ι(x) = |{y < x}|`), per `conv:finite-slots`.
    `iota` transcribes the frozen zero-based display, so it claims no reader
    item; the one-based/zero-based transport is the standing convention already
    recorded for `SLOTS-001`.
  * `def:guarded-source-slabs` and `lem:guarded-source-slab-decomposition` have
    no reader statement at all -- the reader mentions slabs only inside proof
    prose (lines 126--136, "In every remaining slab, every chosen overloaded bin
    also contains an item from a different slab, which is neutral because
    coordinate slabs are disjoint"), and prose is never cited as a statement --
    so `rowSlab`, `coordSlab`, `rowSlab_disjoint`,
    `rowSlab_cover`, `coordSlab_disjoint`, `coordSlab_cover`,
    `guardedRow_same_slab` and `guardedRow_cross_slab` claim no reader item.
  * `eq:guarded-source-encoded-length` has no reader display: the reader gives
    only the `O(·)` size clause `eq:paper-guarded-encoding-size`.  So
    `encodedLength` and `encodedLength_eq` claim no reader item, and only the
    bound `encodedLength_le` is matched to line 101.

## Dependencies, imports, adapters

* `EthInapproximability.ParameterizedNP.GuardedSourceGraph` (banked, consumed
  by pin) and Mathlib.  **No** `LegacyNPCC.Stage12` import, hence no contact
  with the cited AGHP balanced-family axiom; no `LegacyNPCC` facade is used at
  all, this module being upstream of the matrix layer.
* The banked module supplies, and this module never restates: `EndpointGraph`,
  `Inc`, `Row`, `Coord`, `unslabbedRow`, `activeRows`, `binOf`, `activeSet`,
  `Legal`, `Over`, `Wit`, `SourceCommon`, `SourceYES`, `SourceNO`, `deltaV`,
  `source_completeness`, `source_one_copy`, `card_coord`, `card_row`,
  `card_activeRows_edge`, `card_activeRows_guard`, `card_activeRows_le`,
  `sum_card_activeRows`, `deltaV_mul_card`, `K3`, `K4` and the `copies`
  construction.
* External theorem adapters: **none are taken as axioms**, and none is needed:
  everything below is a construction on an arbitrary `EndpointGraph`.  The
  cited `thm:gap-colouring` chain enters only through the banked records
  `DinurConstraintGraph` / `GapColouringOutput`, which this module does not
  consume.
* Proof status of every declaration: **new** (first transcription of
  `sec:source`, lines 386--673).

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: **no structure is introduced at all.**  The guarded source is a
  pinned *function* `guardedRow`, not a record with an entry-equation field, so
  no complexity, robustness, or promise conclusion can sit in constructor data.
  `RetentionOK` is a `Prop` holding exactly the two displayed deletion
  inequalities of `eq:guarded-source-deletion-hypotheses` and nothing else; the
  promise predicates stay the banked separate `Prop`s and appear only as
  **separate implications** in `guardedSource`, exactly as the frozen theorem
  states S1 and S2.
* `M3`: `q2`, `iota`, `iotaSlot`, `rowSlab`, `coordSlab`, `activeSlot`,
  `sourceRows`, `encodedLength`, `zeta`, `localRetained`, `localAssign`,
  `localOver`, `goodSlabs`, `privateBins` are derived accessors or
  proof-internal names of the frozen proof; none restates a derived telescope
  as a bundle field.
* `M7`: nonemptiness is preserved and used -- `card_edge_pos` drives `q2_lt`,
  `activeIncidences_nonempty` exhibits an active incidence, and both promise
  branches are separately inhabited.
* `M9`: the coordinate dichotomy *real versus padding* is exhaustive by an
  explicit case split on `∃ x, ι(x) = j` (`card_activeSlot_le`,
  `guardedSource_legal_of_sourceYES`, `card_activeIncidences`), never by an
  implicit convention; the slab dichotomy `r = r'` versus `r ≠ r'` is
  `guardedRow_same_slab` / `guardedRow_cross_slab`.
* `M10`: every count is a `Finset.card` of tagged rows and tagged coordinates
  (`deletedVertices` and `deletedBlockers` are counted separately, matching the
  frozen closing sentence "this predicate counts deleted tagged vertex and
  blocker rows separately; it does not identify equal row vectors").

## Candidate encodings of `def:guarded-source-constructor`

Two encodings of the rank embedding `ι` were built and raced.

* **Candidate A (landed).**  `ι` is the genuine zero-based rank `rankBy` of the
  displayed lexicographic key `realKey`, and `guardedRow` is the decidable
  existential over the real-coordinate carrier, so padding is zero *by the same
  clause* rather than by a separate stipulation.
* **Candidate B (rejected).**  `ι` is the mixed-radix index
  `ι(r,q) = r·3m + coordIndex(q)`.

Both were compiled.  Candidate B proves the two elementary battery items --
boundedness (`iotaB_lt`) and injectivity (`iotaB_injective`) -- but needs about
ninety lines of `Nat` interval arithmetic to do it, against candidate A's two
general four-line lemmas (`rankBy_lt_card`, `rankBy_injective`), and it **fails
the discriminating battery item**: the frozen display
`ι(x) = |{y ∈ Q_real(G,s) : y < x}|` (04:405--409) is the *definition* under A
and an *unproved theorem* under B.  Ranking (aux lemmas proved, faithfulness,
length): A wins on all three.  The candidate-B file is kept as scratch evidence
at `scratch/CandidateB.lean` (gitignored), where the discriminating item is left
as the explicit unproved `Prop` `B4_frozen_display`.

## Aux-lemma battery

Every battery item below is proved; nothing is stated and left open.

* `A1` general properties of zero-based ranks (6): `rankIn_strictMono`,
  `rankIn_injective`, `rankBy_eq_rankIn`, `rankBy_lt_card`, `rankBy_injective`,
  `edgeKey_injective`.
* `A2` the pinned lexicographic key (2): `coordKey_injective`,
  `realKey_injective`.
* `A3` the padded width `q_2` (5): `q2_isPowTwo`, `card_le_q2`, `q2_le_of_le`
  (minimality), `q2_lt`, `q2_pos`.
* `A4` the embedding (5): `iota_lt_card`, `iota_lt_q2`, `iota_injective`,
  `iotaSlot_injective`, `card_image_iota`.
* `A5` the entry equation (5): `guardedRow_eq_true_iff`, `guardedRow_iota`,
  `guardedRow_padding`, `guardedRow_same_slab`, `guardedRow_cross_slab`.
* `A6` `lem:guarded-source-slab-decomposition` (4): `rowSlab_disjoint`,
  `rowSlab_cover`, `coordSlab_disjoint`, `coordSlab_cover`.
* `A7` `lem:guarded-source-active-slot` (6): `activeSlot_padding`,
  `activeSlot_iota`, `card_activeSlot_iota`, `card_activeSlot_edge`,
  `card_activeSlot_guard`, `card_activeSlot_le`.
* `A8` carrier counts and the incidence sum (5): `card_slabRow`,
  `card_slabCoord`, `card_activeIncidences_eq_sum`, `activeIncidences_real`,
  `card_paddingSlots`.
* `A9` the slab views used by the frozen S1 proof (7): `mem_localRetained`,
  `localRetained_univ`, `mem_goodSlabs`, `card_deletedVertices_sum`,
  `card_deletedBlockers_sum`, `card_filter_prod`, `mem_privateBins`.
* `A10` the local-to-global transfer (4): `card_activeSet_local_le`,
  `two_le_card_activeSet_iota`, `card_privateSlabs_le`,
  `mem_Wit_of_nonprivate`.

## Non-vacuity and statement poles

* `RetentionOK` is inhabited twice: `retentionOK_univ` (the full row set, at any
  legal `s ≥ 4`, `Δ > 0`, `γ > 0`) and -- the point -- `retentionOK_erase`, a
  retention that **genuinely deletes** a tagged vertex row and is a proper
  subset of `I(G,s)`.  Without the second, `RetentionOK` could be a predicate
  satisfied only by the zero-deletion case, and S1 would say nothing about
  deletion stability.
* The frozen budget is genuinely binding, and the witness is chosen so that it
  bites: at `G = K_4` and `s = 4` the vertex budget `(s/2)δ_v N` is `1/3`, so
  *no* vertex row may be deleted; `witnessGraph`, six disjoint copies of `K_4`,
  raises it to `2`.  `guardedSource_witness` therefore exhibits the **whole S1
  hypothesis bundle** simultaneously satisfied at legal, nondegenerate values
  (`s = 4` a power of two, `Δ = 3`, `γ = 1/6`, `SourceCommon`, `SourceNO`, and a
  properly deleting `J`), and records that what S1 there delivers is a strictly
  positive witness count.
* **Statement pole for S1** (`guardedSource_wit_pos`): the conclusion is
  `0 < |Wit|`, not the trivial `0 ≤ |Wit|`.  A construction with no witnesses at
  all would refute it.
* **Statement pole for S2** (`sourceYES_of_legal`): the existential of S2 is not
  satisfiable by an arbitrary `φ`, because a globally legal packing forces
  `SourceYES(G)` back out.  `guardedSource_legal_witness` (at `K_3`) and
  `guardedSource_illegal_witness` (at `K_4`, which allows **no** legal global
  packing) pin both sides, so S2 is not an existential over a carrier where
  every assignment is legal.
* **Statement pole for S3** (`activeIncidences_nonempty`): `A(G,s)` is nonempty,
  so `card_activeIncidences` is not a statement about `0`; and
  `card_paddingSlots` shows the padding region is exactly `q_2 - 12sm` slots, so
  the "padding contributes no active incidences" clause is about a genuinely
  present region rather than an empty one.
* **Hypothesis consistency.**  S1 and S2 are stated as two **separate
  implications** under one common bundle, exactly as the frozen theorem does.
  They are never conjoined: `GuardedSourceGraph.sourceYES_not_sourceNO` shows
  that `SourceYES(G) ∧ SourceNO(G;γ)` is contradictory at every `γ > 0`, so a
  version of `guardedSource` that took both promises as hypotheses would be
  vacuous.  The common bundle itself (`s ≥ 4` a power of two, `Δ > 0`,
  `0 < γ ≤ 1`, `SourceCommon(G;γ,Δ)`) is inhabited by `witnessGraph` above.

## Frozen hypotheses carried but not used

`thm:guarded-source`, `lem:guarded-source-active-slot`, and
`def:guarded-source-retention` all state "`s ≥ 4` a power of two".  The power-of
-two clause is carried in the headline `guardedSource` exactly as the frozen
theorem states it (`hpow`), and is **not** used by the present proofs; the
individual lemmas are therefore proved without it and are strictly stronger than
their anchors.  Both directions are sound: no lemma below assumes more than its
frozen anchor.

## Coverage limit of `cor:guarded-source-encoded-size` (binding on consumers)

`eq:guarded-source-encoded-length` is landed **letter-exact** as
`encodedLength_eq`.  The corollary's second display,
`eq:guarded-source-source-size`, is an **asymptotic** estimate obtained by
substituting the real-valued size clauses of `thm:gap-colouring`
(`N, m ≤ n(log₂(n+2))^c`) into that equation and packaging the result as
`O(s^2 n(log₂(n+2))^c(log₂(n+2)+log₂(s+2))) = n(log(n+2))^{O(1)} poly(s)`.  What
is landed here is the *elementary, kernel-checked* inequality `encodedLength_le`
-- the encoded length is at most a fixed polynomial in `s` and `m` times one
`Nat.clog` of the carrier sizes -- from which that substitution is a purely
asymptotic step.  **The `O(·)` packaging itself is not stated in Lean**; it is
recorded as a disclosed coverage limit in the route obligation ledger under the
standing runtime/consequence tail deferral, and no downstream consumer may cite
this module for it.

The matching reader locus, `eq:paper-guarded-encoding-size` (line 101), is
introduced by the sentence "A sparse encoding and random-access evaluator have
**size and running time** polynomial in ...".  Only the **size** half is claimed
here.  This module states no evaluator, no random access, and no running-time
bound of any kind, so `encodedLength_le` is strictly weaker than that reader
sentence -- never stronger -- and the evaluator/running-time half of the locus
stays Lean pending under the same deferral.

## Interlace widths

This module is upstream of the interlace layer.  Neither `q` nor `Q` occurs
here, and no declaration below may be read as fixing either.  In particular
`q_2` is the frozen **padded coordinate width of the guarded source**
(04:391), not an interlace width.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false

namespace EthInapproximability.ParameterizedNP.GuardedSourceSlab

open Finset
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-! ## Zero-based ranks in a finite linearly ordered carrier -/

/-- The **zero-based rank** `|{y : y < x}|` of `x` in a finite carrier `α`
linearly ordered by `o` (an order supplied as *data*, as `EndpointGraph`
supplies its two orders). -/
def rankIn {α : Type*} [Fintype α] (o : LinearOrder α) (x : α) : ℕ :=
  letI := o
  (Finset.univ.filter fun y => y < x).card

theorem rankIn_strictMono {α : Type*} [Fintype α] (o : LinearOrder α) {x y : α}
    (h : o.lt x y) : rankIn o x < rankIn o y := by
  letI := o
  have hsub : (Finset.univ.filter fun z => z < x) ⊆ (Finset.univ.filter fun z => z < y) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ _, lt_trans hz.2 h⟩
  have hx : x ∉ (Finset.univ.filter fun z => z < x) := by simp
  have hx' : x ∈ (Finset.univ.filter fun z => z < y) := by simp [h]
  exact Finset.card_lt_card ⟨hsub, fun hc => hx (hc hx')⟩

theorem rankIn_injective {α : Type*} [Fintype α] (o : LinearOrder α) :
    Function.Injective (rankIn o) := by
  letI := o
  intro x y hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (Nat.ne_of_lt (rankIn_strictMono o h))
  · exact h
  · exact absurd hxy.symm (Nat.ne_of_lt (rankIn_strictMono o h))

/-- The **zero-based rank** `|{y : key y < key x}|` of `x` in the order pulled
back along an injective `key`; this is `rankIn (LinearOrder.lift' key h)`
unfolded, and it is the form in which the frozen `ι` is transcribed. -/
def rankBy {α β : Type*} [Fintype α] [LinearOrder β] (key : α → β) (x : α) : ℕ :=
  (Finset.univ.filter fun y => key y < key x).card

theorem rankBy_eq_rankIn {α β : Type*} [Fintype α] [LinearOrder β] (key : α → β)
    (h : Function.Injective key) (x : α) :
    rankBy key x = rankIn (LinearOrder.lift' key h) x := rfl

theorem rankBy_lt_card {α β : Type*} [Fintype α] [LinearOrder β] (key : α → β)
    (h : Function.Injective key) (x : α) : rankBy key x < Fintype.card α := by
  classical
  have hsub : (Finset.univ.filter fun y => key y < key x) ⊆ Finset.univ.erase x := by
    intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_erase.mpr ⟨fun hc => ?_, Finset.mem_univ _⟩
    exact absurd (congrArg key hc) (ne_of_lt hy.2)
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.erase x).card = Fintype.card α - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have h3 : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [rankBy]
  omega

theorem rankBy_injective {α β : Type*} [Fintype α] [LinearOrder β] (key : α → β)
    (h : Function.Injective key) : Function.Injective (rankBy key) := by
  rw [funext fun x => rankBy_eq_rankIn key h x]
  exact rankIn_injective _

/-! ## Carriers -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The slabbed row carrier `I(G,s) = [4s] × I_0(G,s)`. -/
abbrev SlabRow (V : Type*) (s : ℕ) : Type _ := Fin (4 * s) × Row V s

/-- The slabbed real-coordinate carrier `Q_real(G,s) = [4s] × Q_0(G)`. -/
abbrev SlabCoord (E : Type*) (s : ℕ) : Type _ := Fin (4 * s) × Coord E

theorem card_slabRow (V : Type*) [Fintype V] (s : ℕ) :
    Fintype.card (SlabRow V s) = 4 * s * (Fintype.card V + (s - 3)) := by
  rw [Fintype.card_prod, Fintype.card_fin, EndpointGraph.card_row]

theorem card_slabCoord (E : Type*) [Fintype E] (s : ℕ) :
    Fintype.card (SlabCoord E s) = 12 * s * Fintype.card E := by
  rw [Fintype.card_prod, Fintype.card_fin, EndpointGraph.card_coord]
  ring

/-! ## The pinned lexicographic order and the rank embedding -/

/-- The zero-based rank of an edge in `G`'s own linear order on `E`. -/
def edgeKey (G : EndpointGraph V E) (e : E) : ℕ := rankIn G.orderE e

theorem edgeKey_injective (G : EndpointGraph V E) : Function.Injective (edgeKey G) :=
  rankIn_injective G.orderE

/-- The lexicographic key of a coordinate of `Q_0(G) = E ⊔ Inc(G)`: the tagged
sum is ordered with `E` first, and `Inc(G) = E × [2]` lexicographically. -/
def coordKey (G : EndpointGraph V E) : Coord E → ℕ ×ₗ (ℕ ×ₗ ℕ)
  | Sum.inl e => toLex (0, toLex (edgeKey G e, 0))
  | Sum.inr p => toLex (1, toLex (edgeKey G p.1, (p.2 : ℕ)))

theorem coordKey_injective (G : EndpointGraph V E) : Function.Injective (coordKey G) := by
  rintro (e | p) (e' | p') h <;> simp only [coordKey, toLex_inj, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (edgeKey_injective G h.2.1)
  · exact absurd h.1 (by norm_num)
  · exact absurd h.1 (by norm_num)
  · exact congrArg Sum.inr (Prod.ext (edgeKey_injective G h.2.1) (Fin.ext h.2.2))

/-- The displayed lexicographic key of a real coordinate `(r,q) ∈ [4s] × Q_0(G)`. -/
def realKey (G : EndpointGraph V E) (s : ℕ) (x : SlabCoord E s) : ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex ((x.1 : ℕ), coordKey G x.2)

theorem realKey_injective (G : EndpointGraph V E) (s : ℕ) :
    Function.Injective (realKey G s) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ h
  simp only [realKey, toLex_inj, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (coordKey_injective G h.2)

/-! ## The padded coordinate width `q₂` -/

/-- `q_2 = min{2^r : 12 s |E| ≤ 2^r}`. -/
def q2 (G : EndpointGraph V E) (s : ℕ) : ℕ := 2 ^ Nat.clog 2 (12 * s * Fintype.card E)

theorem q2_isPowTwo (G : EndpointGraph V E) (s : ℕ) : ∃ r : ℕ, q2 G s = 2 ^ r :=
  ⟨Nat.clog 2 (12 * s * Fintype.card E), rfl⟩

theorem card_le_q2 (G : EndpointGraph V E) (s : ℕ) :
    12 * s * Fintype.card E ≤ q2 G s :=
  Nat.le_pow_clog (by norm_num) _

/-- `q_2` is the *least* power of two above `12 s |E|`. -/
theorem q2_le_of_le (G : EndpointGraph V E) (s : ℕ) {r : ℕ}
    (h : 12 * s * Fintype.card E ≤ 2 ^ r) : q2 G s ≤ 2 ^ r :=
  Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow h)

theorem q2_lt (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) :
    q2 G s < 24 * s * Fintype.card E := by
  have hm : 0 < Fintype.card E := G.card_edge_pos
  have h2 : 2 ≤ 12 * s * Fintype.card E := by nlinarith
  have hpos : 0 < Nat.clog 2 (12 * s * Fintype.card E) :=
    Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num)
    (x := 12 * s * Fintype.card E) (by omega)
  have hsplit : q2 G s = 2 * 2 ^ (Nat.clog 2 (12 * s * Fintype.card E) - 1) := by
    rw [q2, ← pow_succ']
    congr 1
    omega
  have double : ∀ A B : ℕ, A < B → 2 * A < 2 * B := by intro A B h; omega
  calc q2 G s = 2 * 2 ^ (Nat.clog 2 (12 * s * Fintype.card E) - 1) := hsplit
    _ < 2 * (12 * s * Fintype.card E) := double _ _ hlt
    _ = 24 * s * Fintype.card E := by ring

theorem q2_pos (G : EndpointGraph V E) (s : ℕ) : 0 < q2 G s :=
  pow_pos (by norm_num) _

/-! ## The rank embedding `ι` -/

/-- The zero-based rank embedding `ι(x) = |{y ∈ Q_real(G,s) : y < x}|`. -/
def iota (G : EndpointGraph V E) (s : ℕ) (x : SlabCoord E s) : ℕ :=
  rankBy (realKey G s) x

theorem iota_lt_card (G : EndpointGraph V E) (s : ℕ) (x : SlabCoord E s) :
    iota G s x < 12 * s * Fintype.card E := by
  have := rankBy_lt_card (realKey G s) (realKey_injective G s) x
  rwa [card_slabCoord] at this

theorem iota_lt_q2 (G : EndpointGraph V E) (s : ℕ) (x : SlabCoord E s) :
    iota G s x < q2 G s :=
  lt_of_lt_of_le (iota_lt_card G s x) (card_le_q2 G s)

/-- `ι` typed into `[q_2]`. -/
def iotaSlot (G : EndpointGraph V E) (s : ℕ) (x : SlabCoord E s) : Fin (q2 G s) :=
  ⟨iota G s x, iota_lt_q2 G s x⟩

theorem iota_injective (G : EndpointGraph V E) (s : ℕ) :
    Function.Injective (iota G s) := rankBy_injective _ (realKey_injective G s)

theorem iotaSlot_injective (G : EndpointGraph V E) (s : ℕ) :
    Function.Injective (iotaSlot G s) := fun _ _ h =>
  iota_injective G s (congrArg Fin.val h)

/-! ## The guarded source's rows -/

/-- The rows of the guarded source, `eq:guarded-source-slab-entry`: a row
`(r,a)` is active at a coordinate `j` exactly when `j` is the `ι`-image of a
real coordinate `(r',q)` with `r = r'` and `v^0_a(q) = 1`.  Coordinates outside
the image of `ι` are padding and are zero for every row, by the same clause. -/
def guardedRow (G : EndpointGraph V E) (s : ℕ) (i : SlabRow V s) (j : Fin (q2 G s)) : Bool :=
  decide (∃ x : SlabCoord E s, iotaSlot G s x = j ∧ i.1 = x.1 ∧
    G.unslabbedRow s i.2 x.2 = true)

theorem guardedRow_eq_true_iff (G : EndpointGraph V E) (s : ℕ) (i : SlabRow V s)
    (j : Fin (q2 G s)) :
    guardedRow G s i j = true ↔ ∃ x : SlabCoord E s, iotaSlot G s x = j ∧ i.1 = x.1 ∧
      G.unslabbedRow s i.2 x.2 = true := by
  simp [guardedRow]

/-- **`eq:guarded-source-slab-entry`.** -/
@[simp] theorem guardedRow_iota (G : EndpointGraph V E) (s : ℕ) (r r' : Fin (4 * s))
    (a : Row V s) (q : Coord E) :
    guardedRow G s (r, a) (iotaSlot G s (r', q)) = true
      ↔ (r = r' ∧ G.unslabbedRow s a q = true) := by
  rw [guardedRow_eq_true_iff]
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    obtain rfl : x = (r', q) := iotaSlot_injective G s hx
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, h⟩
    exact ⟨(r, q), rfl, rfl, h⟩

/-- "On every coordinate outside the image of `ι`, set `v_i = 0`." -/
theorem guardedRow_padding (G : EndpointGraph V E) (s : ℕ) (i : SlabRow V s)
    {j : Fin (q2 G s)} (h : ∀ x : SlabCoord E s, iotaSlot G s x ≠ j) :
    guardedRow G s i j = false := by
  rw [Bool.eq_false_iff, ne_eq, guardedRow_eq_true_iff]
  rintro ⟨x, hx, -, -⟩
  exact h x hx

/-- The within-slab identification of `lem:guarded-source-slab-decomposition`:
"deleting the first coordinate identifies `(I_r,Q_r,v)` with `U(G,s)`". -/
theorem guardedRow_same_slab (G : EndpointGraph V E) (s : ℕ) (r : Fin (4 * s))
    (a : Row V s) (q : Coord E) :
    guardedRow G s (r, a) (iotaSlot G s (r, q)) = G.unslabbedRow s a q := by
  cases h : G.unslabbedRow s a q
  · rw [Bool.eq_false_iff, ne_eq, guardedRow_iota]
    rintro ⟨-, h'⟩
    rw [h] at h'
    exact Bool.noConfusion h'
  · rw [guardedRow_iota]
    exact ⟨rfl, h⟩

/-- The cross-slab neutrality half of `lem:guarded-source-slab-decomposition`:
"every row outside `I_r` is neutral on every coordinate in `Q_r`". -/
theorem guardedRow_cross_slab (G : EndpointGraph V E) (s : ℕ) {r r' : Fin (4 * s)}
    (hne : r ≠ r') (a : Row V s) (q : Coord E) :
    guardedRow G s (r, a) (iotaSlot G s (r', q)) = false := by
  rw [Bool.eq_false_iff, ne_eq, guardedRow_iota]
  rintro ⟨rfl, -⟩
  exact hne rfl

/-! ## `def:guarded-source-slabs` -/

/-- The row slab `I_r = {r} × I_0(G,s)`. -/
def rowSlab (V : Type*) [Fintype V] (s : ℕ) (r : Fin (4 * s)) : Finset (SlabRow V s) :=
  Finset.univ.filter fun i => i.1 = r

@[simp] theorem mem_rowSlab {V : Type*} [Fintype V] {s : ℕ} {r : Fin (4 * s)}
    (i : SlabRow V s) : i ∈ rowSlab V s r ↔ i.1 = r := by simp [rowSlab]

/-- The coordinate slab `Q_r = ι({r} × Q_0(G)) ⊆ [q_2]`. -/
def coordSlab (G : EndpointGraph V E) (s : ℕ) (r : Fin (4 * s)) : Finset (Fin (q2 G s)) :=
  Finset.univ.image fun q : Coord E => iotaSlot G s (r, q)

@[simp] theorem mem_coordSlab (G : EndpointGraph V E) (s : ℕ) (r : Fin (4 * s))
    (j : Fin (q2 G s)) : j ∈ coordSlab G s r ↔ ∃ q : Coord E, iotaSlot G s (r, q) = j := by
  simp [coordSlab]

/-! ### `lem:guarded-source-slab-decomposition` -/

/-- The row slabs are pairwise disjoint. -/
theorem rowSlab_disjoint (V : Type*) [Fintype V] (s : ℕ) {r r' : Fin (4 * s)}
    (h : r ≠ r') : Disjoint (rowSlab V s r) (rowSlab V s r') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [mem_rowSlab] at hi hi'
  exact h (hi.symm.trans hi')

/-- The row slabs cover `I(G,s)`. -/
theorem rowSlab_cover (V : Type*) [Fintype V] [DecidableEq V] (s : ℕ) :
    (Finset.univ : Finset (Fin (4 * s))).biUnion (rowSlab V s)
      = (Finset.univ : Finset (SlabRow V s)) := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_rowSlab, iff_true]
  exact ⟨i.1, rfl⟩

/-- The coordinate slabs are pairwise disjoint: this is injectivity of `ι`. -/
theorem coordSlab_disjoint (G : EndpointGraph V E) (s : ℕ) {r r' : Fin (4 * s)}
    (h : r ≠ r') : Disjoint (coordSlab G s r) (coordSlab G s r') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  rw [mem_coordSlab] at hj hj'
  obtain ⟨q, hq⟩ := hj
  obtain ⟨q', hq'⟩ := hj'
  have : ((r, q) : SlabCoord E s) = (r', q') :=
    iotaSlot_injective G s (hq.trans hq'.symm)
  exact h (congrArg Prod.fst this)

/-- The coordinate slabs cover the image of `ι`. -/
theorem coordSlab_cover (G : EndpointGraph V E) (s : ℕ) :
    (Finset.univ : Finset (Fin (4 * s))).biUnion (coordSlab G s)
      = Finset.univ.image (iotaSlot G s) := by
  ext j
  constructor
  · intro hj
    obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨q, hq⟩ := (mem_coordSlab G s r j).mp hr
    exact Finset.mem_image.mpr ⟨(r, q), Finset.mem_univ _, hq⟩
  · intro hj
    obtain ⟨⟨r, q⟩, -, hq⟩ := Finset.mem_image.mp hj
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, (mem_coordSlab G s r j).mpr ⟨q, hq⟩⟩

/-! ## `lem:guarded-source-active-slot` -/

theorem mem_activeRows (G : EndpointGraph V E) (s : ℕ) (q : Coord E) (a : Row V s) :
    a ∈ G.activeRows s q ↔ G.unslabbedRow s a q = true := by
  simp [EndpointGraph.activeRows]

/-- The induced ordered active set `I_α = {i ∈ I(G,s) : v_i(α) = 1}`. -/
def activeSlot (G : EndpointGraph V E) (s : ℕ) (j : Fin (q2 G s)) : Finset (SlabRow V s) :=
  Finset.univ.filter fun i => guardedRow G s i j

@[simp] theorem mem_activeSlot (G : EndpointGraph V E) (s : ℕ) (j : Fin (q2 G s))
    (i : SlabRow V s) : i ∈ activeSlot G s j ↔ guardedRow G s i j = true := by
  simp [activeSlot]

/-- "It is empty on padding coordinates." -/
theorem activeSlot_padding (G : EndpointGraph V E) (s : ℕ) {j : Fin (q2 G s)}
    (h : ∀ x : SlabCoord E s, iotaSlot G s x ≠ j) : activeSlot G s j = ∅ := by
  ext i
  simp only [mem_activeSlot, Finset.notMem_empty, iff_false]
  rw [guardedRow_padding G s i h]
  exact Bool.noConfusion

/-- "A real coordinate belongs to one unique coordinate slab.  All rows in the
other slabs are neutral there, and within its slab the exact counts are those
of `def:unslabbed-guarded-copy`." -/
theorem activeSlot_iota (G : EndpointGraph V E) (s : ℕ) (r : Fin (4 * s)) (q : Coord E) :
    activeSlot G s (iotaSlot G s (r, q))
      = ({r} : Finset (Fin (4 * s))) ×ˢ G.activeRows s q := by
  ext i
  obtain ⟨r', a⟩ := i
  rw [mem_activeSlot, Finset.mem_product, Finset.mem_singleton, mem_activeRows,
    guardedRow_iota]

theorem card_activeSlot_iota (G : EndpointGraph V E) (s : ℕ) (r : Fin (4 * s))
    (q : Coord E) :
    (activeSlot G s (iotaSlot G s (r, q))).card = (G.activeRows s q).card := by
  rw [activeSlot_iota, Finset.card_product, Finset.card_singleton, one_mul]

/-- "On a real edge coordinate it has size `s-1`." -/
theorem card_activeSlot_edge (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (r : Fin (4 * s)) (e : E) :
    (activeSlot G s (iotaSlot G s (r, Sum.inl e))).card = s - 1 := by
  rw [card_activeSlot_iota, G.card_activeRows_edge hs e]

/-- "On a real guard coordinate it has size `s-2`." -/
theorem card_activeSlot_guard (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (r : Fin (4 * s)) (p : Inc E) :
    (activeSlot G s (iotaSlot G s (r, Sum.inr p))).card = s - 2 := by
  rw [card_activeSlot_iota, G.card_activeRows_guard hs p]

/-- **`lem:guarded-source-active-slot`**: every coordinate of `[q_2]`, real or
padding, is active on at most `s` rows. -/
theorem card_activeSlot_le (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (j : Fin (q2 G s)) : (activeSlot G s j).card ≤ s := by
  by_cases h : ∃ x : SlabCoord E s, iotaSlot G s x = j
  · obtain ⟨⟨r, q⟩, rfl⟩ := h
    rw [card_activeSlot_iota]
    exact G.card_activeRows_le hs q
  · simp only [not_exists] at h
    rw [activeSlot_padding G s h, Finset.card_empty]
    omega

/-! ## `def:guarded-source-retention` -/

/-- `RetentionOK(G,s;γ,Δ,J)` of `def:guarded-source-retention`: the two strict
deletion hypotheses of `eq:guarded-source-deletion-hypotheses`.  Deleted tagged
vertex rows and deleted tagged blocker rows are counted **separately**, and
equal row vectors are never identified. -/
def RetentionOK (G : EndpointGraph V E) (s : ℕ) (γ : ℚ) (Δ : ℕ)
    (J : Finset (SlabRow V s)) : Prop :=
  (((Finset.univ.filter fun x : Fin (4 * s) × V =>
        ((x.1, Sum.inl x.2) : SlabRow V s) ∉ J).card : ℚ)
      < (s : ℚ) / 2 * (G.deltaV γ Δ * (Fintype.card V : ℚ)))
    ∧ (((Finset.univ.filter fun x : Fin (4 * s) × Fin (s - 3) =>
        ((x.1, Sum.inr x.2) : SlabRow V s) ∉ J).card : ℚ) < (s : ℚ) / 2)

/-- Splitting a filter over a product carrier into its `[4s]` fibres.  This is
the slab bookkeeping behind every count below. -/
theorem card_filter_prod {A B : Type*} [Fintype A] [Fintype B] (P : A × B → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card
      = ∑ a : A, (Finset.univ.filter fun b => P (a, b)).card := by
  simp only [Finset.card_filter]
  exact Fintype.sum_prod_type _

/-! ## `thm:guarded-source`, conclusion S3 -/

/-- The set `A(G,s) = {(i,j) : v_i(j) = 1}` of active row--coordinate
incidences. -/
def activeIncidences (G : EndpointGraph V E) (s : ℕ) :
    Finset (SlabRow V s × Fin (q2 G s)) :=
  Finset.univ.filter fun z => guardedRow G s z.1 z.2

/-- "The padding coordinates outside the image of `ι` contribute no active
incidences." -/
theorem activeIncidences_real (G : EndpointGraph V E) (s : ℕ)
    {z : SlabRow V s × Fin (q2 G s)} (hz : z ∈ activeIncidences G s) :
    ∃ x : SlabCoord E s, iotaSlot G s x = z.2 := by
  rw [activeIncidences, Finset.mem_filter] at hz
  obtain ⟨x, hx, -, -⟩ := (guardedRow_eq_true_iff G s z.1 z.2).mp hz.2
  exact ⟨x, hx⟩

theorem card_activeIncidences_eq_sum (G : EndpointGraph V E) (s : ℕ) :
    (activeIncidences G s).card = ∑ j : Fin (q2 G s), (activeSlot G s j).card := by
  rw [activeIncidences, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [activeSlot, Finset.card_filter]

/-- **`eq:guarded-source-active-incidences`**: the guarded source has exactly
`4s|E|(3s-5)` active row--coordinate incidences. -/
theorem card_activeIncidences (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s) :
    (activeIncidences G s).card = 4 * s * Fintype.card E * (3 * s - 5) := by
  classical
  rw [card_activeIncidences_eq_sum]
  have h2 : ∑ j : Fin (q2 G s), (activeSlot G s j).card
      = ∑ j ∈ Finset.univ.image (iotaSlot G s), (activeSlot G s j).card := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    have hpad : ∀ x : SlabCoord E s, iotaSlot G s x ≠ j := fun x hx =>
      hj (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)
    rw [activeSlot_padding G s hpad, Finset.card_empty]
  have h3 : ∑ j ∈ Finset.univ.image (iotaSlot G s), (activeSlot G s j).card
      = ∑ x : SlabCoord E s, (activeSlot G s (iotaSlot G s x)).card :=
    Finset.sum_image fun x _ y _ h => iotaSlot_injective G s h
  have h4 : ∑ x : SlabCoord E s, (activeSlot G s (iotaSlot G s x)).card
      = ∑ _r : Fin (4 * s), ∑ q : Coord E, (G.activeRows s q).card := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun q _ => card_activeSlot_iota G s r q
  rw [h2, h3, h4]
  simp only [G.sum_card_activeRows hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-! ## `thm:guarded-source`, conclusion S2 -/

/-- The global packing of S2: "assigning corresponding vertex-colour bins and
blocker bins the same labels in all slabs". -/
theorem guardedSource_legal_of_sourceYES (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    (hnoiso : ∀ u : V, 1 ≤ G.degree u) (hyes : G.SourceYES) :
    ∃ φ : SlabRow V s → Fin s,
      Legal (guardedRow G s) (Finset.univ : Finset (SlabRow V s)) φ ∧
        ∀ J : Finset (SlabRow V s), Legal (guardedRow G s) J φ := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := (G.source_completeness hs hnoiso).mpr hyes
  have hlegal : Legal (guardedRow G s) (Finset.univ : Finset (SlabRow V s))
      (fun i => φ₀ i.2) := by
    intro b j
    by_cases hj : ∃ x : SlabCoord E s, iotaSlot G s x = j
    · obtain ⟨⟨r, c⟩, rfl⟩ := hj
      have hEq : activeSet (guardedRow G s) (Finset.univ : Finset (SlabRow V s))
            (fun i => φ₀ i.2) b (iotaSlot G s (r, c))
          = ({r} : Finset (Fin (4 * s))) ×ˢ
              activeSet (G.unslabbedRow s) (Finset.univ : Finset (Row V s)) φ₀ b c := by
        ext i
        obtain ⟨r', a⟩ := i
        rw [mem_activeSet, Finset.mem_product, Finset.mem_singleton, mem_activeSet,
          guardedRow_iota]
        constructor
        · rintro ⟨⟨-, hb⟩, hr, hv⟩
          exact ⟨hr, ⟨Finset.mem_univ _, hb⟩, hv⟩
        · rintro ⟨rfl, ⟨-, hb⟩, hv⟩
          exact ⟨⟨Finset.mem_univ _, hb⟩, rfl, hv⟩
      rw [hEq, Finset.card_product, Finset.card_singleton, one_mul]
      exact hφ₀ b c
    · simp only [not_exists] at hj
      have hsub : activeSet (guardedRow G s) (Finset.univ : Finset (SlabRow V s))
          (fun i => φ₀ i.2) b j ⊆ ∅ := by
        intro i hi
        rw [mem_activeSet] at hi
        rw [guardedRow_padding G s i hj] at hi
        exact absurd hi.2 (by simp)
      rw [Finset.subset_empty.mp hsub, Finset.card_empty]
      omega
  exact ⟨fun i => φ₀ i.2, hlegal, fun J => hlegal.mono (Finset.subset_univ J)⟩

/-! ## `thm:guarded-source`, conclusion S1: the slab vocabulary of the frozen
proof

The frozen proof of S1 names `J_r = J ∩ I_r`, `φ_r = φ|_{J_r}`, `O_r`, the
*good* slabs and the *private* slabs.  Each is transcribed as a named object
below; none of them is constructor data, and none carries a conclusion. -/

/-- `J_r`, the retained rows of slab `r`, read inside the unslabbed carrier. -/
def localRetained (s : ℕ) (J : Finset (SlabRow V s)) (r : Fin (4 * s)) : Finset (Row V s) :=
  Finset.univ.filter fun a => ((r, a) : SlabRow V s) ∈ J

@[simp] theorem mem_localRetained {s : ℕ} {J : Finset (SlabRow V s)} {r : Fin (4 * s)}
    (a : Row V s) : a ∈ localRetained s J r ↔ ((r, a) : SlabRow V s) ∈ J := by
  simp [localRetained]

/-- `φ_r`, the restriction of the global `s`-bin assignment to slab `r`. -/
def localAssign (s : ℕ) (φ : SlabRow V s → Fin s) (r : Fin (4 * s)) : Row V s → Fin s :=
  fun a => φ (r, a)

/-- `O_r`, the overloaded coordinates of slab `r` under `(J_r, φ_r)`. -/
def localOver (G : EndpointGraph V E) (s : ℕ) (J : Finset (SlabRow V s))
    (φ : SlabRow V s → Fin s) (r : Fin (4 * s)) : Finset (Coord E) :=
  Over (G.unslabbedRow s) (localRetained s J r) (localAssign s φ r)

/-- The deleted tagged vertex rows of slab `r`. -/
def deletedVertices (s : ℕ) (J : Finset (SlabRow V s)) (r : Fin (4 * s)) : Finset V :=
  Finset.univ.filter fun u : V => ((r, Sum.inl u) : SlabRow V s) ∉ J

/-- The deleted tagged blocker rows of slab `r`. -/
def deletedBlockers (s : ℕ) (J : Finset (SlabRow V s)) (r : Fin (4 * s)) :
    Finset (Fin (s - 3)) :=
  Finset.univ.filter fun k => ((r, Sum.inr k) : SlabRow V s) ∉ J

/-- "Call `r` *good* when `J_r` retains every blocker row of `I_r` and deletes
at most `δ_v(G;γ,Δ)N` vertex rows of `I_r`." -/
def goodSlabs (G : EndpointGraph V E) (s : ℕ) (γ : ℚ) (Δ : ℕ)
    (J : Finset (SlabRow V s)) : Finset (Fin (4 * s)) :=
  Finset.univ.filter fun r =>
    (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J) ∧
      (((deletedVertices s J r).card : ℚ) ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))

theorem mem_goodSlabs (G : EndpointGraph V E) {s : ℕ} {γ : ℚ} {Δ : ℕ}
    {J : Finset (SlabRow V s)} {r : Fin (4 * s)} :
    r ∈ goodSlabs G s γ Δ J ↔
      (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J) ∧
        (((deletedVertices s J r).card : ℚ) ≤ G.deltaV γ Δ * (Fintype.card V : ℚ)) := by
  simp [goodSlabs]

/-- The global deletion count of `eq:guarded-source-deletion-hypotheses` splits
over the `4s` slabs. -/
theorem card_deletedVertices_sum (s : ℕ) (J : Finset (SlabRow V s)) :
    (Finset.univ.filter fun x : Fin (4 * s) × V =>
        ((x.1, Sum.inl x.2) : SlabRow V s) ∉ J).card
      = ∑ r : Fin (4 * s), (deletedVertices s J r).card :=
  card_filter_prod _

theorem card_deletedBlockers_sum (s : ℕ) (J : Finset (SlabRow V s)) :
    (Finset.univ.filter fun x : Fin (4 * s) × Fin (s - 3) =>
        ((x.1, Sum.inr x.2) : SlabRow V s) ∉ J).card
      = ∑ r : Fin (4 * s), (deletedBlockers s J r).card :=
  card_filter_prod _

/-- "The first strict inequality implies that fewer than `s/2` slabs fail the
vertex condition.  The second implies that fewer than `s/2` slabs lose a
blocker.  Hence there are more than `3s` good slabs." -/
theorem three_mul_lt_card_goodSlabs (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (J : Finset (SlabRow V s))
    (hJ : RetentionOK G s γ Δ J) :
    (3 * s : ℚ) < ((goodSlabs G s γ Δ J).card : ℚ) := by
  classical
  have hm : (0:ℚ) < (Fintype.card E : ℚ) := by exact_mod_cast G.card_edge_pos
  have hΔq : (0:ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  have hDeq : G.deltaV γ Δ * (Fintype.card V : ℚ)
      = γ * (Fintype.card E : ℚ) / (2 * (Δ : ℚ)) := G.deltaV_mul_card γ hΔ
  have hDpos : 0 < G.deltaV γ Δ * (Fintype.card V : ℚ) := by
    rw [hDeq]; exact div_pos (mul_pos hγ0 hm) (by linarith)
  -- the slabs failing the vertex condition
  have hBadV : (((Finset.univ.filter fun r : Fin (4 * s) =>
        ¬ (((deletedVertices s J r).card : ℚ)
            ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))).card : ℚ)) < (s : ℚ) / 2 := by
    have step1 : (((Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (((deletedVertices s J r).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))).card : ℚ))
        * (G.deltaV γ Δ * (Fintype.card V : ℚ))
        ≤ ∑ r ∈ (Finset.univ.filter fun r : Fin (4 * s) =>
              ¬ (((deletedVertices s J r).card : ℚ)
                  ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))),
            ((deletedVertices s J r).card : ℚ) := by
      have h := Finset.sum_le_sum
        (s := (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (((deletedVertices s J r).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))))
        (f := fun _ : Fin (4 * s) => G.deltaV γ Δ * (Fintype.card V : ℚ))
        (g := fun r => ((deletedVertices s J r).card : ℚ))
        (fun r hr => le_of_lt (not_le.mp (Finset.mem_filter.mp hr).2))
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
    have step2 : ∑ r ∈ (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (((deletedVertices s J r).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))),
          ((deletedVertices s J r).card : ℚ)
        ≤ ∑ r : Fin (4 * s), ((deletedVertices s J r).card : ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => by positivity)
    have step3 : (∑ r : Fin (4 * s), ((deletedVertices s J r).card : ℚ))
        = (((Finset.univ.filter fun x : Fin (4 * s) × V =>
              ((x.1, Sum.inl x.2) : SlabRow V s) ∉ J).card : ℕ) : ℚ) := by
      rw [card_deletedVertices_sum]
      push_cast
      ring
    have hkey : (((Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (((deletedVertices s J r).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))).card : ℚ))
        * (G.deltaV γ Δ * (Fintype.card V : ℚ))
        < ((s : ℚ) / 2) * (G.deltaV γ Δ * (Fintype.card V : ℚ)) := by
      calc _ ≤ ∑ r ∈ _, ((deletedVertices s J r).card : ℚ) := step1
        _ ≤ ∑ r : Fin (4 * s), ((deletedVertices s J r).card : ℚ) := step2
        _ = _ := step3
        _ < ((s : ℚ) / 2) * (G.deltaV γ Δ * (Fintype.card V : ℚ)) := hJ.1
    exact lt_of_mul_lt_mul_right hkey (le_of_lt hDpos)
  -- the slabs losing a blocker
  have hBadB : (((Finset.univ.filter fun r : Fin (4 * s) =>
        ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)).card : ℚ))
        < (s : ℚ) / 2 := by
    have step1 : (((Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)).card : ℚ))
        ≤ ∑ r ∈ (Finset.univ.filter fun r : Fin (4 * s) =>
              ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)),
            ((deletedBlockers s J r).card : ℚ) := by
      have h := Finset.sum_le_sum
        (s := (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)))
        (f := fun _ : Fin (4 * s) => (1 : ℚ))
        (g := fun r => ((deletedBlockers s J r).card : ℚ))
        (fun r hr => by
          obtain ⟨k, hk⟩ := not_forall.mp (Finset.mem_filter.mp hr).2
          have hmem : k ∈ deletedBlockers s J r := by
            rw [deletedBlockers, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hk⟩
          have h1 : 1 ≤ (deletedBlockers s J r).card := Finset.card_pos.mpr ⟨k, hmem⟩
          change (1 : ℚ) ≤ ((deletedBlockers s J r).card : ℚ)
          exact_mod_cast h1)
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    have step2 : ∑ r ∈ (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)),
          ((deletedBlockers s J r).card : ℚ)
        ≤ ∑ r : Fin (4 * s), ((deletedBlockers s J r).card : ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => by positivity)
    have step3 : (∑ r : Fin (4 * s), ((deletedBlockers s J r).card : ℚ))
        = (((Finset.univ.filter fun x : Fin (4 * s) × Fin (s - 3) =>
              ((x.1, Sum.inr x.2) : SlabRow V s) ∉ J).card : ℕ) : ℚ) := by
      rw [card_deletedBlockers_sum]
      push_cast
      ring
    calc _ ≤ ∑ r ∈ _, ((deletedBlockers s J r).card : ℚ) := step1
      _ ≤ ∑ r : Fin (4 * s), ((deletedBlockers s J r).card : ℚ) := step2
      _ = _ := step3
      _ < (s : ℚ) / 2 := hJ.2
  -- the complement of the good slabs is covered by the two bad sets
  have hcover : (Finset.univ : Finset (Fin (4 * s)))
      ⊆ goodSlabs G s γ Δ J ∪
        ((Finset.univ.filter fun r : Fin (4 * s) =>
            ¬ (((deletedVertices s J r).card : ℚ)
                ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))) ∪
          (Finset.univ.filter fun r : Fin (4 * s) =>
            ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J))) := by
    intro r _
    by_cases h1 : ∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J
    · by_cases h2 : ((deletedVertices s J r).card : ℚ)
          ≤ G.deltaV γ Δ * (Fintype.card V : ℚ)
      · exact Finset.mem_union_left _ (mem_goodSlabs G |>.mpr ⟨h1, h2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))
  have hcard : 4 * s ≤ (goodSlabs G s γ Δ J).card
      + ((Finset.univ.filter fun r : Fin (4 * s) =>
            ¬ (((deletedVertices s J r).card : ℚ)
                ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))).card
        + (Finset.univ.filter fun r : Fin (4 * s) =>
            ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)).card) := by
    have h1 : (Finset.univ : Finset (Fin (4 * s))).card ≤ _ := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (goodSlabs G s γ Δ J)
      ((Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (((deletedVertices s J r).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))) ∪
        (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)))
    have h3 := Finset.card_union_le
      (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (((deletedVertices s J r).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ)))
      (Finset.univ.filter fun r : Fin (4 * s) =>
          ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hcardq : (4 * s : ℚ) ≤ ((goodSlabs G s γ Δ J).card : ℚ)
      + ((((Finset.univ.filter fun r : Fin (4 * s) =>
            ¬ (((deletedVertices s J r).card : ℚ)
                ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))).card : ℚ))
        + (((Finset.univ.filter fun r : Fin (4 * s) =>
            ¬ (∀ k : Fin (s - 3), ((r, Sum.inr k) : SlabRow V s) ∈ J)).card : ℚ))) := by
    exact_mod_cast hcard
  linarith

/-! ### Private and nonprivate slabs -/

/-- The bins that make a slab *private*: "the entire global bin
`B_{b}(φ)` lies in `I_r`", for a bin `b` that slab `r` really overloads. -/
def privateBins (G : EndpointGraph V E) (s : ℕ) (J : Finset (SlabRow V s))
    (φ : SlabRow V s → Fin s) (r : Fin (4 * s)) : Finset (Fin s) :=
  Finset.univ.filter fun b => binOf J φ b ⊆ rowSlab V s r ∧
    ∃ α : Coord E, 2 ≤ (activeSet (G.unslabbedRow s) (localRetained s J r)
      (localAssign s φ r) b α).card

theorem mem_privateBins (G : EndpointGraph V E) (s : ℕ) (J : Finset (SlabRow V s))
    (φ : SlabRow V s → Fin s) (r : Fin (4 * s)) (b : Fin s) :
    b ∈ privateBins G s J φ r ↔ binOf J φ b ⊆ rowSlab V s r ∧
      ∃ α : Coord E, 2 ≤ (activeSet (G.unslabbedRow s) (localRetained s J r)
        (localAssign s φ r) b α).card := by
  simp [privateBins]

/-- The slab identification at the level of active sets: the rows of slab `r`
active at `q` inside bin `b` inject into the global active set of the real
coordinate `ι(r,q)` in the same bin. -/
theorem card_activeSet_local_le (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (SlabRow V s)) (φ : SlabRow V s → Fin s) (r : Fin (4 * s))
    (b : Fin s) (q : Coord E) :
    (activeSet (G.unslabbedRow s) (localRetained s J r) (localAssign s φ r) b q).card
      ≤ (activeSet (guardedRow G s) J φ b (iotaSlot G s (r, q))).card := by
  refine Finset.card_le_card_of_injOn (fun a => ((r, a) : SlabRow V s)) ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, mem_activeSet, mem_localRetained] at ha ⊢
    obtain ⟨⟨hJ, hb⟩, hv⟩ := ha
    exact ⟨⟨hJ, hb⟩, by rw [guardedRow_iota]; exact ⟨rfl, hv⟩⟩
  · intro a _ a' _ h'
    exact congrArg Prod.snd h'

/-- "The two rows witnessing the overload are retained rows of `I_r`": a local
overload of slab `r` in bin `b` is a global overload of `ι(r,q)` in bin `b`. -/
theorem two_le_card_activeSet_iota (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (SlabRow V s)) (φ : SlabRow V s → Fin s) (r : Fin (4 * s))
    {b : Fin s} {q : Coord E}
    (h : 2 ≤ (activeSet (G.unslabbedRow s) (localRetained s J r)
      (localAssign s φ r) b q).card) :
    2 ≤ (activeSet (guardedRow G s) J φ b (iotaSlot G s (r, q))).card := by
  exact le_trans h (card_activeSet_local_le G s J φ r b q)

/-- "This map from private slabs to `[s]` is injective ... Thus at most `s`
good slabs are private." -/
theorem card_privateSlabs_le (G : EndpointGraph V E) (s : ℕ) (γ : ℚ) (Δ : ℕ)
    (J : Finset (SlabRow V s)) (φ : SlabRow V s → Fin s) :
    ((goodSlabs G s γ Δ J).filter fun r => (privateBins G s J φ r).Nonempty).card ≤ s := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((goodSlabs G s γ Δ J).filter fun r => (privateBins G s J φ r).Nonempty) with h | h
  · rw [h, Finset.card_empty]; omega
  · obtain ⟨r₀, hr₀⟩ := h
    obtain ⟨b₀, -⟩ := (Finset.mem_filter.mp hr₀).2
    have hmem : ∀ r ∈ (goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty, (privateBins G s J φ r).Nonempty :=
      fun r hr => (Finset.mem_filter.mp hr).2
    have key : ∀ r ∈ (goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty,
        (if hh : (privateBins G s J φ r).Nonempty
            then (privateBins G s J φ r).min' hh else b₀) ∈ privateBins G s J φ r := by
      intro r hr
      rw [dif_pos (hmem r hr)]
      exact Finset.min'_mem _ _
    have hinj : ∀ r ∈ (goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty,
        ∀ r' ∈ (goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty,
        (if hh : (privateBins G s J φ r).Nonempty
            then (privateBins G s J φ r).min' hh else b₀)
          = (if hh : (privateBins G s J φ r').Nonempty
            then (privateBins G s J φ r').min' hh else b₀) → r = r' := by
      intro r hr r' hr' heq
      have h1 := key r hr
      have h2 := key r' hr'
      rw [heq] at h1
      set b : Fin s := (if hh : (privateBins G s J φ r').Nonempty
        then (privateBins G s J φ r').min' hh else b₀) with hbdef
      rw [mem_privateBins] at h1 h2
      obtain ⟨α, hα⟩ := h1.2
      have hne : (activeSet (G.unslabbedRow s) (localRetained s J r)
          (localAssign s φ r) b α).Nonempty :=
        Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hα)
      obtain ⟨a, ha⟩ := hne
      rw [mem_activeSet, mem_localRetained] at ha
      obtain ⟨⟨haJ, hab⟩, -⟩ := ha
      have hbin : ((r, a) : SlabRow V s) ∈ binOf J φ b := by
        rw [mem_binOf]; exact ⟨haJ, hab⟩
      have hfin := h2.1 hbin
      rw [mem_rowSlab] at hfin
      exact hfin
    calc ((goodSlabs G s γ Δ J).filter fun r => (privateBins G s J φ r).Nonempty).card
        ≤ (Finset.univ : Finset (Fin s)).card :=
          Finset.card_le_card_of_injOn _ (fun r _ => Finset.mem_univ _) hinj
      _ = s := by simp

/-- "If `r` is nonprivate and `α ∈ O_r`, the bin `b_r(α)` contains a retained
row from a slab other than `r`.  That row is neutral on `α` ... Hence every
`α ∈ O_r` belongs to `Wit(v,J,φ)`." -/
theorem mem_Wit_of_nonprivate (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (SlabRow V s)) (φ : SlabRow V s → Fin s) (r : Fin (4 * s))
    (hr : ¬ (privateBins G s J φ r).Nonempty) {q : Coord E}
    (hq : q ∈ localOver G s J φ r) :
    iotaSlot G s (r, q) ∈ Wit (guardedRow G s) J φ := by
  rw [localOver, mem_Over] at hq
  obtain ⟨b, hb⟩ := hq
  rw [mem_Wit]
  refine ⟨b, two_le_card_activeSet_iota G s J φ r hb, ?_⟩
  have hnb : b ∉ privateBins G s J φ r := fun hc => hr ⟨b, hc⟩
  rw [mem_privateBins] at hnb
  have hnsub : ¬ (binOf J φ b ⊆ rowSlab V s r) := fun hc => hnb ⟨hc, ⟨q, hb⟩⟩
  obtain ⟨i, hi, hi'⟩ := Finset.not_subset.mp hnsub
  refine ⟨i, hi, ?_⟩
  obtain ⟨r', a'⟩ := i
  rw [mem_rowSlab] at hi'
  exact guardedRow_cross_slab G s hi' a' q

/-! ### `thm:guarded-source`, conclusion S1 -/

/-- `ζ = γ/24` of `thm:guarded-source`.

Reader counterpart: the `ζ` half of `eq:paper-source-stability-constants`
(`A-stage4-details.tex`, display line 72, label line 73).  The `δ_v` half is
banked as `EndpointGraph.deltaV` in `GuardedSourceGraph.lean` and is not
reclaimed here. -/
def zeta (γ : ℚ) : ℚ := γ / 24

/-- **S1 of `thm:guarded-source`.**  Under `SourceNO(G;γ)`, every admissible
retention `J` and every `s`-bin assignment `φ` leave overload-plus-neutral
witnesses on at least `ζ q_2 = (γ/24) q_2` coordinates. -/
theorem guardedSource_wit_of_sourceNO (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (J : Finset (SlabRow V s)) (hJ : RetentionOK G s γ Δ J)
    (φ : SlabRow V s → Fin s) :
    zeta γ * (q2 G s : ℚ) ≤ ((Wit (guardedRow G s) J φ).card : ℚ) := by
  classical
  rw [zeta]
  have hmn : 0 < Fintype.card E := G.card_edge_pos
  have hm : (0:ℚ) < (Fintype.card E : ℚ) := by exact_mod_cast hmn
  have hsq : (0:ℚ) < (s : ℚ) := by
    have : (0:ℕ) < s := by omega
    exact_mod_cast this
  have hgood := three_mul_lt_card_goodSlabs G hs hΔ hγ0 J hJ
  have hsplit : ((goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty).card
      + ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).card
      = (goodSlabs G s γ Δ J).card :=
    Finset.card_filter_add_card_filter_not _
  have hPriv := card_privateSlabs_le G s γ Δ J φ
  have hNonPriv : (2 * s : ℚ) < (((goodSlabs G s γ Δ J).filter
      fun r => ¬ (privateBins G s J φ r).Nonempty).card : ℚ) := by
    have h1 : ((((goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty).card : ℚ)) ≤ (s : ℚ) := by
      exact_mod_cast hPriv
    have h2 : ((((goodSlabs G s γ Δ J).filter
          fun r => (privateBins G s J φ r).Nonempty).card : ℚ))
        + ((((goodSlabs G s γ Δ J).filter
          fun r => ¬ (privateBins G s J φ r).Nonempty).card : ℚ))
        = ((goodSlabs G s γ Δ J).card : ℚ) := by exact_mod_cast hsplit
    linarith
  -- `lem:source-one-copy` in every good slab
  have hOloc : ∀ r ∈ goodSlabs G s γ Δ J,
      γ * (Fintype.card E : ℚ) / 2 ≤ ((localOver G s J φ r).card : ℚ) := by
    intro r hr
    rw [mem_goodSlabs] at hr
    have heq : (Finset.univ.filter fun u : V =>
          (Sum.inl u : Row V s) ∉ localRetained s J r) = deletedVertices s J r := by
      ext u
      simp [deletedVertices, mem_localRetained]
    exact G.source_one_copy hs hΔ hγ0 hγ1 hno (fun u => (hcommon.2 u).2)
      (localRetained s J r) (fun k => by rw [mem_localRetained]; exact hr.1 k)
      (by rw [heq]; exact hr.2) (localAssign s φ r)
  -- the witness coordinates supplied by the nonprivate slabs
  have hdisj : ∀ r ∈ ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty),
      ∀ r' ∈ ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty), r ≠ r' →
      Disjoint ((localOver G s J φ r).image fun q => iotaSlot G s (r, q))
        ((localOver G s J φ r').image fun q => iotaSlot G s (r', q)) := by
    intro r _ r' _ hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hj
    obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp hj'
    have : ((r, q) : SlabCoord E s) = (r', q') :=
      iotaSlot_injective G s (hq.trans hq'.symm)
    exact hne (congrArg Prod.fst this)
  have hWsub : (((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).biUnion
        fun r => (localOver G s J φ r).image fun q => iotaSlot G s (r, q))
      ⊆ Wit (guardedRow G s) J φ := by
    intro j hj
    obtain ⟨r, hr, hjr⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hjr
    exact mem_Wit_of_nonprivate G s J φ r (Finset.mem_filter.mp hr).2 hq
  have hWcard : (((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).biUnion
        fun r => (localOver G s J φ r).image fun q => iotaSlot G s (r, q)).card
      = ∑ r ∈ ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty), (localOver G s J φ r).card := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact Finset.card_image_of_injective _ (fun q q' h =>
      congrArg Prod.snd (iotaSlot_injective G s h))
  -- assemble the count
  have hsum : (((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).card : ℚ)
        * (γ * (Fintype.card E : ℚ) / 2)
      ≤ ∑ r ∈ ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty),
          ((localOver G s J φ r).card : ℚ) := by
    have h := Finset.sum_le_sum
      (s := ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty))
      (f := fun _ : Fin (4 * s) => γ * (Fintype.card E : ℚ) / 2)
      (g := fun r => ((localOver G s J φ r).card : ℚ))
      (fun r hr => hOloc r (Finset.mem_filter.mp hr).1)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
  have hcast : ((((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).biUnion
        fun r => (localOver G s J φ r).image fun q => iotaSlot G s (r, q)).card : ℚ)
      = ∑ r ∈ ((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty),
          ((localOver G s J φ r).card : ℚ) := by
    rw [hWcard]; push_cast; ring
  have hWle : ((((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).biUnion
        fun r => (localOver G s J φ r).image fun q => iotaSlot G s (r, q)).card : ℚ)
      ≤ ((Wit (guardedRow G s) J φ).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hWsub
  have hpos : (0:ℚ) < γ * (Fintype.card E : ℚ) / 2 := by positivity
  have hstrict : (2 * s : ℚ) * (γ * (Fintype.card E : ℚ) / 2)
      < (((goodSlabs G s γ Δ J).filter
        fun r => ¬ (privateBins G s J φ r).Nonempty).card : ℚ)
        * (γ * (Fintype.card E : ℚ) / 2) :=
    mul_lt_mul_of_pos_right hNonPriv hpos
  have hq2 : (q2 G s : ℚ) < 24 * (s : ℚ) * (Fintype.card E : ℚ) := by
    have h := q2_lt G hs
    have : ((q2 G s : ℕ) : ℚ) < ((24 * s * Fintype.card E : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hfinal : γ / 24 * (q2 G s : ℚ) < γ / 24 * (24 * (s : ℚ) * (Fintype.card E : ℚ)) :=
    mul_lt_mul_of_pos_left hq2 (by linarith)
  have hring : γ / 24 * (24 * (s : ℚ) * (Fintype.card E : ℚ))
      = (2 * s : ℚ) * (γ * (Fintype.card E : ℚ) / 2) := by ring
  linarith [hsum, hcast, hWle, hstrict, hfinal, hring.le, hring.ge]

/-! ### `thm:guarded-source`, the three conclusions together -/

/-- **`thm:guarded-source` (deletion-stable guarded source).**  Under the frozen
hypothesis bundle -- `s ≥ 4` a power of two, `Δ > 0`, `0 < γ ≤ 1`, and
`SourceCommon(G;γ,Δ)` -- the three frozen conclusions S1, S2, S3 hold.

The two promise branches are kept as **separate implications**, exactly as the
frozen theorem states them; they are never conjoined
(`GuardedSourceGraph.sourceYES_not_sourceNO` shows why that would be fatal). -/
theorem guardedSource (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    (hpow : ∃ t : ℕ, s = 2 ^ t) {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hcommon : G.SourceCommon γ Δ) :
    (G.SourceNO γ → ∀ J : Finset (SlabRow V s), RetentionOK G s γ Δ J →
        ∀ φ : SlabRow V s → Fin s,
          zeta γ * (q2 G s : ℚ) ≤ ((Wit (guardedRow G s) J φ).card : ℚ))
      ∧ (G.SourceYES → ∃ φ : SlabRow V s → Fin s,
          Legal (guardedRow G s) (Finset.univ : Finset (SlabRow V s)) φ ∧
            ∀ J : Finset (SlabRow V s), Legal (guardedRow G s) J φ)
      ∧ Fintype.card (SlabRow V s) = 4 * s * (Fintype.card V + (s - 3))
      ∧ (activeIncidences G s).card = 4 * s * Fintype.card E * (3 * s - 5) :=
  ⟨fun hno J hJ φ => guardedSource_wit_of_sourceNO G hs hΔ hγ0 hγ1 hcommon hno J hJ φ,
    fun hyes => guardedSource_legal_of_sourceYES G hs (fun u => (hcommon.2 u).1) hyes,
    card_slabRow V s, card_activeIncidences G (by omega)⟩

/-! ## `cor:guarded-source-encoded-size` -/

/-- `w(t) = ⌈log₂(t+1)⌉`. -/
def headerWidth (t : ℕ) : ℕ := Nat.clog 2 (t + 1)

/-- `d(t) = ⌈log₂ max{2,t}⌉`. -/
def indexWidth (t : ℕ) : ℕ := Nat.clog 2 (max 2 t)

/-- `N_src = 4s(N+s-3)`, the row count of `thm:guarded-source` S3. -/
def sourceRows (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  4 * s * (Fintype.card V + (s - 3))

theorem card_slabRow_eq_sourceRows (G : EndpointGraph V E) (s : ℕ) :
    Fintype.card (SlabRow V s) = sourceRows G s := card_slabRow V s

/-- `L_inc(G,s)`, the encoded length of the canonical sparse codec: two
self-delimiting headers of lengths `2w(N_src)+1` and `2w(q_2)+1`, then one
`(d(N_src)+d(q_2))`-bit record per active incidence, in lexicographic order.
The all-zero coordinate suffix is charged through the `q_2` header, not by
writing a dense table. -/
def encodedLength (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  2 * headerWidth (sourceRows G s) + 1 + 2 * headerWidth (q2 G s) + 1
    + (activeIncidences G s).card
        * (indexWidth (sourceRows G s) + indexWidth (q2 G s))

/-- **`eq:guarded-source-encoded-length`**, letter-exact: the frozen display,
obtained by substituting `|A(G,s)| = 4sm(3s-5)` from
`eq:guarded-source-active-incidences`. -/
theorem encodedLength_eq (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s) :
    encodedLength G s
      = 2 * headerWidth (sourceRows G s) + 1 + 2 * headerWidth (q2 G s) + 1
        + 4 * s * Fintype.card E * (3 * s - 5)
            * (indexWidth (sourceRows G s) + indexWidth (q2 G s)) := by
  rw [encodedLength, card_activeIncidences G hs]

/-- The elementary arithmetic step of the size estimate. -/
theorem enc_arith (C P : ℕ) :
    2 * C + 1 + 2 * C + 1 + 12 * P * (2 * C) ≤ (6 + 24 * P) * (C + 1) := by
  have h : (6 + 24 * P) * (C + 1)
      = (2 * C + 1 + 2 * C + 1 + 12 * P * (2 * C)) + (2 * C + 4 + 24 * P) := by ring
  omega

/-- The `poly(s)` half of `eq:guarded-source-source-size`, in the explicit
elementary form the corollary's own proof establishes: the encoded length is at
most a fixed polynomial in `s` and `m` times a single logarithm of the carrier
sizes.  Substituting the source-reduction bounds `N, m ≤ n(log₂(n+2))^c` of
`thm:gap-colouring` into this inequality is what turns it into the frozen
asymptotic display; that asymptotic packaging is **not** stated in Lean (see the
module header). -/
theorem encodedLength_le (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) :
    encodedLength G s
      ≤ (6 + 24 * s ^ 2 * Fintype.card E)
          * (Nat.clog 2 (24 * s ^ 2
              * (Fintype.card V + Fintype.card E + 2)) + 1) := by
  have hm : 0 < Fintype.card E := G.card_edge_pos
  have hs2 : 16 ≤ s ^ 2 := by nlinarith
  have hNle : sourceRows G s + 2
      ≤ 24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2) := by
    have h1 : sourceRows G s ≤ 4 * s * Fintype.card V + 4 * s ^ 2 := by
      rw [sourceRows]
      calc 4 * s * (Fintype.card V + (s - 3))
          ≤ 4 * s * (Fintype.card V + s) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 4 * s * Fintype.card V + 4 * s ^ 2 := by ring
    have b1 : 4 * s * Fintype.card V ≤ 24 * s ^ 2 * Fintype.card V :=
      Nat.mul_le_mul_right _ (by nlinarith)
    have b2 : 4 * s ^ 2 + 2 ≤ 24 * s ^ 2 * Fintype.card E + 48 * s ^ 2 := by nlinarith
    have e1 : 24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)
        = 24 * s ^ 2 * Fintype.card V + (24 * s ^ 2 * Fintype.card E + 48 * s ^ 2) := by
      ring
    omega
  have hqle : q2 G s + 2
      ≤ 24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2) := by
    have h1 : q2 G s ≤ 24 * s * Fintype.card E := le_of_lt (q2_lt G hs)
    nlinarith [hs, hm, h1]
  have hw1 : headerWidth (sourceRows G s)
      ≤ Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)) :=
    Nat.clog_mono_right _ (by omega)
  have hw2 : headerWidth (q2 G s)
      ≤ Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)) :=
    Nat.clog_mono_right _ (by omega)
  have hd1 : indexWidth (sourceRows G s)
      ≤ Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)) :=
    Nat.clog_mono_right _ (max_le (by omega) (by omega))
  have hd2 : indexWidth (q2 G s)
      ≤ Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)) :=
    Nat.clog_mono_right _ (max_le (by omega) (by omega))
  have hA : (activeIncidences G s).card ≤ 12 * s ^ 2 * Fintype.card E := by
    rw [card_activeIncidences G (by omega)]
    calc 4 * s * Fintype.card E * (3 * s - 5)
        ≤ 4 * s * Fintype.card E * (3 * s) := Nat.mul_le_mul_left _ (by omega)
      _ = 12 * s ^ 2 * Fintype.card E := by ring
  rw [encodedLength]
  have hmul : (activeIncidences G s).card
        * (indexWidth (sourceRows G s) + indexWidth (q2 G s))
      ≤ 12 * (s ^ 2 * Fintype.card E)
        * (2 * Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2))) := by
    refine Nat.mul_le_mul ?_ (by omega)
    calc (activeIncidences G s).card ≤ 12 * s ^ 2 * Fintype.card E := hA
      _ = 12 * (s ^ 2 * Fintype.card E) := by ring
  have harith := enc_arith
    (Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)))
    (s ^ 2 * Fintype.card E)
  have hgoal : (6 + 24 * s ^ 2 * Fintype.card E)
      * (Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)) + 1)
      = (6 + 24 * (s ^ 2 * Fintype.card E))
      * (Nat.clog 2 (24 * s ^ 2 * (Fintype.card V + Fintype.card E + 2)) + 1) := by
    ring
  omega

/-! ## Aux-lemma battery: the image of `ι` and its padding complement -/

theorem card_image_iota (G : EndpointGraph V E) (s : ℕ) :
    (Finset.univ.image (iotaSlot G s)).card = 12 * s * Fintype.card E := by
  rw [Finset.card_image_of_injective _ (iotaSlot_injective G s), Finset.card_univ,
    card_slabCoord]

/-- The padding coordinates are exactly the `q_2 - 12sm` slots outside the image
of `ι`; `card_le_q2` makes this count nonnegative. -/
theorem card_paddingSlots (G : EndpointGraph V E) (s : ℕ) :
    (Finset.univ.filter fun j : Fin (q2 G s) =>
        ∀ x : SlabCoord E s, iotaSlot G s x ≠ j).card
      = q2 G s - 12 * s * Fintype.card E := by
  classical
  have h : (Finset.univ.filter fun j : Fin (q2 G s) =>
        ∀ x : SlabCoord E s, iotaSlot G s x ≠ j)
      = (Finset.univ.image (iotaSlot G s))ᶜ := by
    ext j
    rw [Finset.mem_filter, Finset.mem_compl]
    constructor
    · rintro ⟨-, h⟩ hc
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hc
      exact h x hx
    · intro h
      exact ⟨Finset.mem_univ _, fun x hx => h (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)⟩
  rw [h, Finset.card_compl, card_image_iota, Fintype.card_fin]

theorem localRetained_univ (s : ℕ) (r : Fin (4 * s)) :
    localRetained s (Finset.univ : Finset (SlabRow V s)) r = Finset.univ := by
  ext a
  simp [mem_localRetained]

/-! ## Non-vacuity and statement poles -/

/-- **Statement pole for S2.**  The existential of S2 is *not* satisfied by an
arbitrary `φ`: a globally legal packing forces `SourceYES(G)` back out, so a
graph with no proper `3`-colouring allows none.  Without this, S2 could be
discharged by a construction in which every assignment is legal. -/
theorem sourceYES_of_legal (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    (hnoiso : ∀ u : V, 1 ≤ G.degree u) (φ : SlabRow V s → Fin s)
    (h : Legal (guardedRow G s) (Finset.univ : Finset (SlabRow V s)) φ) :
    G.SourceYES := by
  have hr : 0 < 4 * s := by omega
  refine (G.source_completeness hs hnoiso).mp ⟨localAssign s φ ⟨0, hr⟩, ?_⟩
  intro b q
  have h1 := card_activeSet_local_le G s (Finset.univ : Finset (SlabRow V s)) φ ⟨0, hr⟩ b q
  rw [localRetained_univ] at h1
  exact le_trans h1 (h b _)

/-- Every coordinate slab really carries an active incidence: the `s-3 ≥ 1`
blocker rows of a slab are active on every real coordinate of that slab.  So
`A(G,s)` is not the empty set and S3 is not a statement about `0`. -/
theorem activeIncidences_nonempty (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) :
    (activeIncidences G s).Nonempty := by
  have hr : 0 < 4 * s := by omega
  have hk : 0 < s - 3 := by omega
  obtain ⟨e⟩ := G.edgeNonempty
  refine ⟨((⟨0, hr⟩, Sum.inr ⟨0, hk⟩), iotaSlot G s (⟨0, hr⟩, Sum.inl e)), ?_⟩
  rw [activeIncidences, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [guardedRow_iota]; exact ⟨rfl, by simp⟩⟩

/-- The full retention `J = I(G,s)` is admissible: it deletes nothing, and both
frozen bounds are strictly positive. -/
theorem retentionOK_univ (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) {Δ : ℕ}
    (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) :
    RetentionOK G s γ Δ (Finset.univ : Finset (SlabRow V s)) := by
  have hm : (0:ℚ) < (Fintype.card E : ℚ) := by exact_mod_cast G.card_edge_pos
  have hΔq : (0:ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  have hsq : (0:ℚ) < (s : ℚ) := by
    have : (0:ℕ) < s := by omega
    exact_mod_cast this
  have hDpos : 0 < G.deltaV γ Δ * (Fintype.card V : ℚ) := by
    rw [G.deltaV_mul_card γ hΔ]
    exact div_pos (mul_pos hγ0 hm) (by linarith)
  constructor
  · have hempty : (Finset.univ.filter fun x : Fin (4 * s) × V =>
        ((x.1, Sum.inl x.2) : SlabRow V s) ∉ (Finset.univ : Finset (SlabRow V s)))
        = (∅ : Finset (Fin (4 * s) × V)) := by
      ext x; simp
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have : (0:ℚ) < (s : ℚ) / 2 := by linarith
    exact mul_pos this hDpos
  · have hempty : (Finset.univ.filter fun x : Fin (4 * s) × Fin (s - 3) =>
        ((x.1, Sum.inr x.2) : SlabRow V s) ∉ (Finset.univ : Finset (SlabRow V s)))
        = (∅ : Finset (Fin (4 * s) × Fin (s - 3))) := by
      ext x; simp
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    linarith

/-- **Non-vacuity of `RetentionOK` at a genuinely deleting retention.**  Once
the frozen vertex budget `(s/2)δ_v(G;γ,Δ)N` exceeds `1`, deleting a single
tagged vertex row is admissible; the resulting `J` is a proper subset of
`I(G,s)`, so `RetentionOK` is not a predicate satisfied only by the full row
set. -/
theorem retentionOK_erase (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) {Δ : ℕ}
    (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ)
    (hbudget : 1 < (s : ℚ) / 2 * (G.deltaV γ Δ * (Fintype.card V : ℚ)))
    (r : Fin (4 * s)) (u : V) :
    RetentionOK G s γ Δ
        ((Finset.univ : Finset (SlabRow V s)).erase (r, Sum.inl u))
      ∧ ((Finset.univ : Finset (SlabRow V s)).erase (r, Sum.inl u))
          ≠ (Finset.univ : Finset (SlabRow V s)) := by
  classical
  have hsq : (0:ℚ) < (s : ℚ) := by
    have : (0:ℕ) < s := by omega
    exact_mod_cast this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hsingle : (Finset.univ.filter fun x : Fin (4 * s) × V =>
        ((x.1, Sum.inl x.2) : SlabRow V s)
          ∉ (Finset.univ : Finset (SlabRow V s)).erase (r, Sum.inl u))
        = {(r, u)} := by
      ext x
      obtain ⟨r', u'⟩ := x
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩
        have heq : ((r', Sum.inl u') : SlabRow V s) = (r, Sum.inl u) := by
          by_contra hc
          exact hx (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)
        simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
        simp [heq.1, heq.2]
      · intro hx
        simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨Finset.mem_univ _, by simp⟩
    rw [hsingle, Finset.card_singleton, Nat.cast_one]
    exact hbudget
  · have hempty : (Finset.univ.filter fun x : Fin (4 * s) × Fin (s - 3) =>
        ((x.1, Sum.inr x.2) : SlabRow V s)
          ∉ (Finset.univ : Finset (SlabRow V s)).erase (r, Sum.inl u))
        = (∅ : Finset (Fin (4 * s) × Fin (s - 3))) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_not]
      exact Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    linarith
  · intro hc
    have : ((r, Sum.inl u) : SlabRow V s)
        ∈ (Finset.univ : Finset (SlabRow V s)).erase (r, Sum.inl u) := by
      rw [hc]; exact Finset.mem_univ _
    exact (Finset.notMem_erase _ _) this

/-- **Statement pole for S1.**  What S1 delivers is a strictly positive witness
count, not the trivial `0 ≤ |Wit|`. -/
theorem guardedSource_wit_pos (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (J : Finset (SlabRow V s)) (hJ : RetentionOK G s γ Δ J)
    (φ : SlabRow V s → Fin s) :
    0 < ((Wit (guardedRow G s) J φ).card : ℚ) := by
  have h := guardedSource_wit_of_sourceNO G hs hΔ hγ0 hγ1 hcommon hno J hJ φ
  have hq : (0:ℚ) < (q2 G s : ℚ) := by exact_mod_cast q2_pos G s
  have hz : 0 < zeta γ := by rw [zeta]; linarith
  nlinarith [mul_pos hz hq]

/-! ### A nondegenerate instance of the whole S1 hypothesis bundle

`K_4` alone is too small: at `s = 4` its vertex budget `(s/2)δ_v N` is `1/3`,
so no vertex row may be deleted and the only admissible retention is the full
one.  Six disjoint copies of `K_4` make the budget `2`, at which point a
genuinely deleting retention is admissible -- so the frozen deletion
hypotheses are *not* vacuous, and neither is the promise they are used with. -/

/-- Six disjoint copies of `K_4`: `N = 24`, `m = 36`, `Δ = 3`, `γ = 1/6`. -/
def witnessGraph : EndpointGraph (Fin 6 × Fin 4) (Fin 6 × Fin 6) :=
  EndpointGraph.copies K4 6 (by norm_num)

theorem witnessGraph_card_vertex : Fintype.card (Fin 6 × Fin 4) = 24 := by simp

theorem witnessGraph_card_edge : Fintype.card (Fin 6 × Fin 6) = 36 := by simp

theorem witnessGraph_degree : ∀ u : Fin 6 × Fin 4, witnessGraph.degree u = 3 := by
  rintro ⟨c, u⟩
  rw [witnessGraph, EndpointGraph.degree_copies, k4_degree u]

theorem witnessGraph_sourceCommon : witnessGraph.SourceCommon (1 / 6) 3 := by
  refine ⟨?_, fun u => ?_⟩
  · rw [witnessGraph_card_vertex, witnessGraph_card_edge]; omega
  · rw [witnessGraph_degree u]; omega

theorem witnessGraph_sourceNO : witnessGraph.SourceNO (1 / 6) :=
  EndpointGraph.sourceNO_copies K4 6 (by norm_num) k4_sourceNO

theorem witnessGraph_budget :
    1 < (4 : ℚ) / 2 * (witnessGraph.deltaV (1 / 6) 3
      * (Fintype.card (Fin 6 × Fin 4) : ℚ)) := by
  rw [EndpointGraph.deltaV, witnessGraph_card_vertex, witnessGraph_card_edge]
  norm_num

/-- **The full S1 hypothesis bundle is simultaneously satisfiable at legal,
nondegenerate parameter values, and what it then delivers is nonvacuous.**  The
retention `J` genuinely deletes a tagged vertex row, so no hypothesis of S1 is
discharged by the trivial `J = I(G,s)`. -/
theorem guardedSource_witness :
    ∃ J : Finset (SlabRow (Fin 6 × Fin 4) 4),
      J ≠ Finset.univ ∧ RetentionOK witnessGraph 4 (1 / 6) 3 J ∧
        ∀ φ : SlabRow (Fin 6 × Fin 4) 4 → Fin 4,
          0 < ((Wit (guardedRow witnessGraph 4) J φ).card : ℚ) := by
  obtain ⟨hret, hne⟩ := retentionOK_erase witnessGraph (s := 4) (by norm_num)
    (Δ := 3) (by norm_num) (γ := 1 / 6) (by norm_num) witnessGraph_budget
    ⟨0, by norm_num⟩ (0, 0)
  exact ⟨_, hne, hret, fun φ =>
    guardedSource_wit_pos witnessGraph (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) witnessGraph_sourceCommon witnessGraph_sourceNO _ hret φ⟩

/-- ...and the `YES` branch is separately inhabited, at `K_3`: `S2` produces a
legal global packing there.  Together with `sourceYES_of_legal` at `K_4` this
shows that neither promise branch is the vacuous one. -/
theorem guardedSource_legal_witness :
    ∃ φ : SlabRow (Fin 3) 4 → Fin 4,
      Legal (guardedRow K3 4) (Finset.univ : Finset (SlabRow (Fin 3) 4)) φ := by
  obtain ⟨φ, hφ, -⟩ := guardedSource_legal_of_sourceYES K3 (s := 4) (by norm_num)
    (fun u => by rw [k3_degree u]; norm_num) k3_sourceYES
  exact ⟨φ, hφ⟩

/-- ...and `K_4`, which has no proper `3`-colouring, allows **no** legal global
packing at all. -/
theorem guardedSource_illegal_witness :
    ¬ ∃ φ : SlabRow (Fin 4) 4 → Fin 4,
      Legal (guardedRow K4 4) (Finset.univ : Finset (SlabRow (Fin 4) 4)) φ := by
  rintro ⟨φ, hφ⟩
  exact k4_not_sourceYES (sourceYES_of_legal K4 (s := 4) (by norm_num)
    (fun u => by rw [k4_degree u]; norm_num) φ hφ)

end EthInapproximability.ParameterizedNP.GuardedSourceSlab
