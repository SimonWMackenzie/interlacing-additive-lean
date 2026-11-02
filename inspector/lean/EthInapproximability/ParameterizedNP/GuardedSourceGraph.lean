import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Parameterized NP route: the guarded source's graph layer

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `sec:source`, *A deletion-stable
  guarded source*, in the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/04-guarded-source.tex`, **lines 1--386**.  The
  five anchors traced here are
  * `def:endpoint-graph-adapter` (lines 13--47),
  * `def:source-graph-predicates` (lines 49--76),
  * `thm:gap-colouring` (lines 85--113) with its proof and size bookkeeping
    (lines 115--218),
  * `def:source-packing-vocabulary` (lines 226--276),
  * `def:unslabbed-guarded-copy` (lines 278--309), the public deletion
    fractions of lines 311--323, `lem:source-completeness` (lines 325--343),
    and `lem:source-one-copy` (lines 345--382).

  Everything from `def:guarded-source-constructor` (line 386) onwards -- the
  `[4s]`-slab carriers, `q_2`, the rank embedding `iota`, and the slab
  aggregation -- is **out of scope for this module** and is not stated here.
* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`
  `A-stage4-details.tex`, subsection `sec:paper-guarded-source-details`), one
  reader item per declaration, none assigned twice:
  * lines 16--18 ("an ordered loopless multigraph with nonempty vertex and edge
    sets ... Parallel edge occurrences remain distinct") -> `EndpointGraph`;
  * line 21 (the display `Inc(G) = {(u,e) : u in e}`) -> `Inc`, through the
    incidence transport `(e,b) |-> (bd_b(e), e)` already recorded in
    `routes/parameterized-np/autoformalization/READER_CROSSWALK.md`
    ("The guarded-source incidence carriers are likewise canonically
    equivalent");
  * lines 64--65 ("Each coordinate is active on at most `s` items")
    -> `card_activeRows_le`;
  * lines 67--69 ("Call a coordinate an *overload-plus-neutral witness* ...")
    -> `Wit`;
  * `eq:paper-source-stability-constants` (label line 73, display line 71),
    the `delta_v(G)` half only -> `deltaV`; the `zeta = gamma/24` half belongs
    to the slab layer and is not claimed here;
  * line 78, the clause "If `G` is three-colourable" -> `SourceYES`;
  * lines 79--80, "if every three-colouring of `G` makes at least
    `gamma m_G` edge occurrences monochromatic" -> `SourceNO`.

  **Reader items deliberately declined, with the reason recorded** (the
  precedent is `CLOCK-001`/`cc-t1x`/`cc-t1y-r1` in the crosswalk):
  * `thm:paper-guarded-source` itself (lines 76--103) is stated for the
    **slabbed** system `I(G,s) = [4s] x (V u [s-3])` of
    `eq:paper-guarded-carriers`; `source_completeness` and `source_one_copy`
    below are the frozen **one-copy** statements
    `lem:source-completeness`/`lem:source-one-copy` about `U(G,s)`, a
    different carrier.  Its one-slab content appears in the reader only inside
    proof prose (lines 106--124), and prose is never cited as a statement, so
    both lemmas claim **no** reader item.
  * `eq:paper-guarded-edge-evaluator` (line 54) and
    `eq:paper-guarded-incidence-evaluator` (line 62) carry the slab-equality
    guard `r = r'`; `unslabbedRow` is the frozen `v^0` of
    `def:unslabbed-guarded-copy` and is not that display, so it claims no
    reader item.
  * `eq:paper-guarded-size` (line 90) and `eq:paper-guarded-active-incidences`
    (line 95) are slabbed counts (`12 s m_G`, `4 s m_G (3s-5)`); the unslabbed
    counts proved here (`3 m`, `m (3s-5)`) are different values, so
    `card_coord` and `sum_card_activeRows` claim no reader item.
  * The reader's ambient setup does **not** state the density clause
    `2|E| >= |V|` of `SourceCommon`, so `SourceCommon` claims no reader item;
    what the reader does have -- "no isolated vertices" -- is landed as the
    *derivation* `card_vertex_le_two_mul_card_edge`.

## Dependencies, imports, adapters

* Mathlib only.  **No** `LegacyNPCC.Stage12` import, hence no contact with the
  cited AGHP balanced-family axiom; no `LegacyNPCC` facade is used at all, this
  module being upstream of the matrix layer.
* No banked module of this route is consumed and none is restated.
* External theorem adapters: **none are taken as axioms.**  The cited chain of
  `thm:gap-colouring` -- Impagliazzo--Paturi--Zane sparsification
  (`\cite{impagliazzo2001which}`), Dinur's PCP theorem
  (`\cite{dinur2007pcp}`, Lemma 8.3, Theorem 1.5, Lemma 1.7), and
  Bogdanov--Obata--Trevisan Theorem 14 (`\cite{bogdanov2002lower}`) -- enters
  **only** as explicit named hypotheses: the record `DinurConstraintGraph`
  and the record `GapColouringOutput`.  This follows the standing rule that a
  cited external interface stays an explicit named hypothesis or cited-fact
  structure field and never becomes a silent axiom.
* Proof status of every declaration: **new** (first transcription of
  `sec:source`, lines 1--386).

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: no constructor record below carries a complexity, robustness, or
  promise conclusion.  `EndpointGraph` carries exactly the frozen data of
  `def:endpoint-graph-adapter` (two linear orders, two nonemptiness facts, the
  two endpoint maps, looplessness).  The promise predicates `SourceYES` and
  `SourceNO` are **separate** `Prop`s, never fields.  `GapColouringOutput` is
  the *cited output record* of `thm:gap-colouring`; its `yes`/`no` fields are
  guarded by the input branch's satisfiability, exactly as the frozen promise
  is, so the two mutually exclusive branches are never conjoined.
* `M3`: `degree`, `Inc`, `deltaV`, `deltaStar`, `Kcl`, `epsB` are derived
  accessors, not fields; no derived telescope is restated as a bundle field.
* `M7`: both carriers of `def:endpoint-graph-adapter` are nonempty by field,
  and this is used (`card_edge_pos`, `card_vertex_pos`).
* `M9`: the four defining clauses of `def:unslabbed-guarded-copy` are
  exhaustive by the `Sum` match, not by an implicit convention; the frozen
  sentence "These four clauses are exhaustive because both carriers are tagged
  sums" is the pattern match itself.
* `M10`: every cardinality below counts tagged rows and coordinates
  (`Finset.card` of subsets of tagged carriers), never a quotient by equal
  underlying vectors, matching the closing sentence of
  `def:source-packing-vocabulary`.

## Candidate encodings of `def:endpoint-graph-adapter`

Two encodings were built and run against the same aux-lemma battery.

* **Candidate A (landed).** The two linear orders demanded by the frozen
  definition are *fields* of `EndpointGraph`.
* **Candidate B (rejected).** The two linear orders are *instance parameters*
  `[LinearOrder V] [LinearOrder E]`.

Both carry the elementary battery, but B fails the discriminating test: the
copy construction the frozen proof performs at 04:201 ("the disjoint union of
`r` copies") lands on `Fin r x V`, which has no ambient `LinearOrder`
instance, so under B the construction cannot even be *stated* without an
explicit `@`-application threading an ad-hoc order through every consumer, and
instance synthesis fails there anyway.  Under A the same construction is one
`where` block (`copies`) and its degree/promise transfer lemmas are ordinary
statements.  A is also strictly more faithful for a *conclusion* that produces
an ordered endpoint graph, since the order is carried rather than assumed.
Ranking (aux lemmas proved, faithfulness, length): A wins on all three.

## Aux-lemma battery

Every battery below is proved; nothing is stated and left open.

* `A1` carrier identities of `def:endpoint-graph-adapter` (7)
* `A2` general properties of the three promise predicates (4)
* `A3` general properties of the packing vocabulary (6)
* `A4` the exact activity counts of `def:unslabbed-guarded-copy` (7)
* `A5` the public deletion fractions (2)
* `A6` the copy construction of 04:196--204 (7)
* `A7` the free-bin complement used by both frozen lemmas (2)
* `A8` the `thm:gap-colouring` bookkeeping proved outright (14)

## Non-vacuity and statement poles

* `EndpointGraph`: `K3`, `K4`, with looplessness -- the hardest field --
  discharged at genuinely distinct endpoints.
* `SourceYES`/`SourceNO`: `k3_sourceYES`, `k4_sourceNO`, and
  `k4_not_sourceYES`; `sourceYES_not_sourceNO` proves the frozen "mutually
  exclusive" clause, so no later record may conjoin the two branches.
* `GapColouringOutput`: inhabited at **every** legal input size `n >= 1` and
  **separately on each promise branch** (`gapColouringOutput_yes_witness`,
  `gapColouringOutput_no_witness`), so neither `yes` nor `no` is the field
  that is vacuously satisfied.  `gapColouringOutput_zero_absurd` records the
  one illegal parameter value: at `n = 0` the frozen size clause contradicts
  the nonemptiness of `V`, so `1 <= n` is forced by the frozen text.
* `Legal`/`Over`: `unslabbedGuardedCopy_legal_witness` exhibits a legal packing
  and `unslabbedGuardedCopy_illegal_witness` exhibits a carrier admitting
  none, so `source_completeness` is not an equivalence between two always-true
  sides.  `source_one_copy_witness` checks that the full hypothesis bundle of
  `lem:source-one-copy` is simultaneously satisfiable at legal parameters and
  that what it then delivers is the nonvacuous bound `|Over| >= 1/2`, not
  `0 <= |Over|`.
* `DinurConstraintGraph`: `dinurWitness`, at the **nondegenerate** legal values
  `A = 2`, `d = 3`, `rho = 1/2`, together with the end-to-end pin
  `dinurWitness_epsB : eps_B = 1/288` and the strictness check
  `dinurWitness_epsB_lt_half`.  Without an inhabitant, `epsB_pos` and
  `epsB_le_half` -- both of the form `forall D : DinurConstraintGraph, ...` --
  would compile green and assert nothing.  The degenerate inhabitation
  `A = 1, d = 0, rho = 1` is deliberately **not** used: it exercises neither
  `binom{A}{2}` nor the frozen guard `max{1,d}`, whereas at `A = 2, d = 3` the
  pin forces `g(2) = 2`, `binom 2 2 = 1`, `K_cl(2) = 24`, and a guard that
  genuinely selects `d`.

## Premises recorded as anchor-implied rather than anchor-stated

* `DinurConstraintGraph.ρ_le_one` (`rho <= 1`) is **not stated at the frozen
  anchor**: 04:135 gives only "`rho > 0` its `NO`-case rejected-constraint
  fraction".  It is forced by `rho` being a fraction of the constraint set --
  the frozen proof counts "at least `rho |F|` indexed constraints" out of `|F|`
  -- and it is genuinely used by `epsB_le_half`.  It is therefore carried as an
  explicit field and disclosed here, not silently assumed; the non-vacuity
  witness above inhabits the record *with* this field, so the strengthened
  record is not empty.  No other field of any record in this module departs
  from its frozen anchor.

## Coverage limit of `thm:gap-colouring` (binding on every consumer)

The frozen theorem asserts the existence of a **polynomial-time reduction**.
`GapColouringOutput` and `gapColouring` represent only the *combinatorial
output* of that reduction on one input branch.  **No uniformity, algorithm, or
running-time content is stated anywhere in this module.**  The Lean statement
is therefore strictly weaker than its anchor -- never stronger -- and the
algorithmic half of `thm:gap-colouring` remains Lean pending.  No downstream
consumer (in particular a lane at `06-parameter-schedule.tex` line 1201 or in
Section 14) may read uniformity, effectivity, or a running-time bound out of
`gapColouring`.  This deferral is licensed by the standing runtime/consequence
tail deferral and is recorded in the route obligation ledger.

## Interlace widths

This module is upstream of the interlace layer.  Neither `q` nor `Q` occurs
here, and no declaration below may be read as fixing either.
-/

set_option linter.unusedSectionVars false

namespace EthInapproximability.ParameterizedNP.GuardedSourceGraph

open Finset

/-! ## `def:endpoint-graph-adapter` (04:13--47)

> An *ordered endpoint graph* is a tuple `G = (V, E, bd_0, bd_1)` in which `V`
> and `E` are nonempty finite linearly ordered sets and `bd_0, bd_1 : E -> V`
> satisfy `bd_0(e) /= bd_1(e)` for every `e in E`.

The two linear orders are carried as **fields** rather than as instance
arguments.  This is the frozen definition verbatim ("nonempty finite linearly
ordered sets"), and it is what makes the record closed under the carrier
constructions the frozen proof performs (line 201: "the disjoint union of `r`
copies"), whose carriers `Fin r x V` have no ambient `LinearOrder` instance.
-/

/-- An **ordered endpoint graph** `G = (V, E, bd_0, bd_1)` of
`def:endpoint-graph-adapter`.

Reader counterpart: `A-stage4-details.tex` lines 16--18, "an ordered loopless
multigraph with nonempty vertex and edge sets, no isolated vertices, and
maximum degree at most `Delta`.  Parallel edge occurrences remain distinct."
The reader's two extra clauses are hypotheses of the reader's ambient setup,
not part of the frozen record: "no isolated vertices" is `1 <= deg` inside
`SourceCommon`, and the degree bound is its `Delta` clause; keeping them out of
the record is exactly `M2`/`M4`. -/
structure EndpointGraph (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  /-- `V` is linearly ordered. -/
  orderV : LinearOrder V
  /-- `E` is linearly ordered. -/
  orderE : LinearOrder E
  /-- `V` is nonempty. -/
  vertexNonempty : Nonempty V
  /-- `E` is nonempty; its elements are edge *occurrences*, so two parallel
  occurrences remain distinct. -/
  edgeNonempty : Nonempty E
  /-- `bd_0 : E -> V`. -/
  bd₀ : E → V
  /-- `bd_1 : E -> V`. -/
  bd₁ : E → V
  /-- `bd_0(e) /= bd_1(e)` for every `e`: the graph is loopless. -/
  loopless : ∀ e : E, bd₀ e ≠ bd₁ e

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The **tagged incidence carrier** `Inc(G) = E x [2]` of
`def:endpoint-graph-adapter`.

Reader counterpart: the display at `A-stage4-details.tex` line 21,
`Inc(G) = {(u,e) : u in e}`, under the transport `(e,b) |-> (bd_b(e), e)`
recorded in `READER_CROSSWALK.md`; looplessness makes that map a bijection and
parallel occurrences keep their edge tags. -/
abbrev Inc (E : Type*) : Type _ := E × Fin 2

namespace EndpointGraph

/-- `bd(e,b)`, the frozen two-case endpoint selector of
`def:endpoint-graph-adapter`. -/
def bd (G : EndpointGraph V E) (e : E) (b : Fin 2) : V :=
  if b = 0 then G.bd₀ e else G.bd₁ e

@[simp] theorem bd_zero (G : EndpointGraph V E) (e : E) : G.bd e 0 = G.bd₀ e := rfl

@[simp] theorem bd_one (G : EndpointGraph V E) (e : E) : G.bd e 1 = G.bd₁ e := by
  simp [bd]

/-- The endpoint map `vert_G : Inc(G) -> V`, `vert_G(e,b) = bd(e,b)`. -/
def vert (G : EndpointGraph V E) (p : Inc E) : V := G.bd p.1 p.2

@[simp] theorem vert_mk (G : EndpointGraph V E) (e : E) (b : Fin 2) :
    G.vert (e, b) = G.bd e b := rfl

/-- The fibre `Inc_G(u) = {(e,b) : bd(e,b) = u}`. -/
def incFinset (G : EndpointGraph V E) (u : V) : Finset (Inc E) :=
  Finset.univ.filter fun p => G.vert p = u

@[simp] theorem mem_incFinset (G : EndpointGraph V E) (u : V) (p : Inc E) :
    p ∈ G.incFinset u ↔ G.vert p = u := by
  simp [incFinset]

/-- `deg_G(u) = |Inc_G(u)|`. -/
def degree (G : EndpointGraph V E) (u : V) : ℕ := (G.incFinset u).card

/-! ### Aux-lemma battery A1: the carrier identities of the frozen definition -/

omit [DecidableEq V] [DecidableEq E] in
/-- The frozen sentence "Thus `|Inc(G)| = 2|E|` definitionally". -/
theorem card_inc : Fintype.card (Inc E) = 2 * Fintype.card E := by
  simp [Inc, Fintype.card_prod, Nat.mul_comm]

theorem card_edge_pos (G : EndpointGraph V E) : 0 < Fintype.card E :=
  Fintype.card_pos_iff.mpr G.edgeNonempty

theorem card_vertex_pos (G : EndpointGraph V E) : 0 < Fintype.card V :=
  Fintype.card_pos_iff.mpr G.vertexNonempty

/-- The frozen sentence "Equivalently, `u` is incident with `e` precisely when
`u = bd(e,0)` or `u = bd(e,1)`". -/
theorem incident_iff (G : EndpointGraph V E) (u : V) (e : E) :
    (∃ b : Fin 2, (e, b) ∈ G.incFinset u) ↔ (u = G.bd₀ e ∨ u = G.bd₁ e) := by
  constructor
  · rintro ⟨b, hb⟩
    rw [mem_incFinset] at hb
    fin_cases b
    · exact Or.inl hb.symm
    · exact Or.inr (by simpa using hb.symm)
  · rintro (h | h)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩

/-- Aux A1(c) (**handshake**): the degrees sum to `|Inc(G)| = 2|E|`.  This is a
general property of the frozen carrier, and it is what makes the density clause
of `SourceCommon` a *consequence* of "no isolated vertices" rather than an
extra assumption. -/
theorem sum_degree (G : EndpointGraph V E) :
    ∑ u : V, G.degree u = 2 * Fintype.card E := by
  classical
  have h : ∑ u : V, G.degree u = (Finset.univ : Finset (Inc E)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := G.vert)
      (t := (Finset.univ : Finset V)) (fun x _ => Finset.mem_univ _)]
    rfl
  rw [h]
  simp [Finset.card_univ, Inc, Fintype.card_prod, Nat.mul_comm]

/-- The reader's "no isolated vertices" hypothesis
(`A-stage4-details.tex` line 17) forces the frozen density clause
`2|E| >= |V|` of `def:source-graph-predicates`; the reader therefore states no
separate density bound, and none is assumed here. -/
theorem card_vertex_le_two_mul_card_edge (G : EndpointGraph V E)
    (h : ∀ u : V, 1 ≤ G.degree u) :
    Fintype.card V ≤ 2 * Fintype.card E := by
  calc Fintype.card V = ∑ _u : V, 1 := by simp
    _ ≤ ∑ u : V, G.degree u := Finset.sum_le_sum fun u _ => h u
    _ = 2 * Fintype.card E := G.sum_degree

/-- The number of incidences landing in a set `X` of vertices is the sum of the
degrees over `X`.  (Used twice in `lem:source-one-copy`.) -/
theorem card_inc_mem (G : EndpointGraph V E) (X : Finset V) :
    (Finset.univ.filter fun p : Inc E => G.vert p ∈ X).card
      = ∑ u ∈ X, G.degree u := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := G.vert) (t := X)
    (fun p hp => by simpa using (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun u hu => ?_
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_incFinset]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hu, h⟩⟩

end EndpointGraph

/-! ## `def:source-graph-predicates` (04:49--76) -/

namespace EndpointGraph

/-- The set of edge occurrences made monochromatic by `chi`. -/
def monoFinset (G : EndpointGraph V E) (χ : V → Fin 3) : Finset E :=
  Finset.univ.filter fun e => χ (G.bd e 0) = χ (G.bd e 1)

@[simp] theorem mem_monoFinset (G : EndpointGraph V E) (χ : V → Fin 3) (e : E) :
    e ∈ G.monoFinset χ ↔ χ (G.bd e 0) = χ (G.bd e 1) := by
  simp [monoFinset]

/-- `SourceCommon(G;gamma,Delta)`: the **promise-independent** graph
hypotheses of `def:source-graph-predicates` -- the edge/vertex density bound
and the two-sided degree bound.

`gamma` is carried in the signature because the frozen predicate is displayed
as `SourceCommon(G;gamma,Delta)`; it does not occur in the body, and
`sourceCommon_gamma_free` below makes that checkable rather than a comment.

Reader item: **none** -- the reader's ambient setup (lines 15--17) has no
density clause.  Its "no isolated vertices" is landed as
`card_vertex_le_two_mul_card_edge`. -/
def SourceCommon (G : EndpointGraph V E) (_γ : ℚ) (Δ : ℕ) : Prop :=
  Fintype.card V ≤ 2 * Fintype.card E ∧ ∀ u : V, 1 ≤ G.degree u ∧ G.degree u ≤ Δ

/-- `SourceYES(G)`: `G` has a proper `3`-colouring.

Reader counterpart: `A-stage4-details.tex` line 78, the clause "If `G` is
three-colourable". -/
def SourceYES (G : EndpointGraph V E) : Prop :=
  ∃ χ : V → Fin 3, ∀ e : E, χ (G.bd e 0) ≠ χ (G.bd e 1)

/-- `SourceNO(G;gamma)`: every `3`-colouring leaves at least `gamma|E|`
monochromatic edge occurrences.

Reader counterpart: `A-stage4-details.tex` lines 79--80, "if every
three-colouring of `G` makes at least `gamma m_G` edge occurrences
monochromatic". -/
def SourceNO (G : EndpointGraph V E) (γ : ℚ) : Prop :=
  ∀ χ : V → Fin 3, γ * (Fintype.card E : ℚ) ≤ ((G.monoFinset χ).card : ℚ)

/-! ### Aux-lemma battery A2: general properties of the three predicates -/

/-- The frozen signature carries `gamma` into `SourceCommon`, but the frozen
body does not use it.  Stated so that no later declaration can silently read a
`gamma`-dependence into the promise-independent predicate. -/
theorem sourceCommon_gamma_free (G : EndpointGraph V E) (γ γ' : ℚ) (Δ : ℕ) :
    G.SourceCommon γ Δ ↔ G.SourceCommon γ' Δ := Iff.rfl

/-- `SourceCommon` is monotone in the degree bound. -/
theorem SourceCommon.mono_delta {G : EndpointGraph V E} {γ : ℚ} {Δ Δ' : ℕ}
    (h : G.SourceCommon γ Δ) (hle : Δ ≤ Δ') : G.SourceCommon γ Δ' :=
  ⟨h.1, fun u => ⟨(h.2 u).1, le_trans (h.2 u).2 hle⟩⟩

/-- `SourceNO` is antitone in `gamma`. -/
theorem SourceNO.mono {G : EndpointGraph V E} {γ γ' : ℚ} (h : G.SourceNO γ)
    (hle : γ' ≤ γ) : G.SourceNO γ' := by
  intro χ
  exact le_trans (by
    have : (0:ℚ) ≤ (Fintype.card E : ℚ) := by positivity
    exact mul_le_mul_of_nonneg_right hle this) (h χ)

/-- **Statement pole.** The frozen sentence "The other two predicates contain
only the mutually exclusive promise information used by the corresponding
branch proofs" is a mathematical claim, and this is it: at any legal `gamma`
the two promise predicates cannot both hold.  Without this, a later record
conjoining them would typecheck and prove nothing. -/
theorem sourceYES_not_sourceNO (G : EndpointGraph V E) {γ : ℚ} (hγ : 0 < γ)
    (hyes : G.SourceYES) : ¬ G.SourceNO γ := by
  obtain ⟨χ, hχ⟩ := hyes
  intro hno
  have h0 : G.monoFinset χ = ∅ := by
    ext e
    simp only [mem_monoFinset, Finset.notMem_empty, iff_false]
    exact hχ e
  have := hno χ
  rw [h0] at this
  simp only [Finset.card_empty, Nat.cast_zero] at this
  have hm : (0:ℚ) < (Fintype.card E : ℚ) := by
    exact_mod_cast G.card_edge_pos
  nlinarith

end EndpointGraph

/-! ## `def:source-packing-vocabulary` (04:226--276)

The frozen definition "applies to any finite binary row system, not only to
the particular source constructed later", so it is stated here for arbitrary
finite carriers `I`, `Q`.  The frozen `v_i : Q -> {0,1}` is transported to
`v : I -> Q -> Bool` with `true` for `1`; every cardinality below counts
*tagged* rows and coordinates, which is the closing sentence of the frozen
definition (`M10`).

The frozen `phi : J -> [s]` is transported to a total `phi : I -> Fin s`
together with the retained-row set `J`: the bins `B_b(phi) = {i in J : phi i =
b}` are the same finite sets, every `J`-function extends to a total one, and no
statement below quantifies over anything but bins of `J`. -/

section Packing

variable {I Q : Type*} [Fintype Q]

/-- The bin `B_b(phi) = {i in J : phi(i) = b}`. -/
def binOf {s : ℕ} (J : Finset I) (φ : I → Fin s) (b : Fin s) : Finset I :=
  J.filter fun i => φ i = b

@[simp] theorem mem_binOf {s : ℕ} (J : Finset I) (φ : I → Fin s) (b : Fin s)
    (i : I) : i ∈ binOf J φ b ↔ i ∈ J ∧ φ i = b := by
  simp [binOf]

/-- `A_{b,q}(v,J,phi) = {i in B_b(phi) : v_i(q) = 1}`. -/
def activeSet {s : ℕ} (v : I → Q → Bool) (J : Finset I) (φ : I → Fin s)
    (b : Fin s) (q : Q) : Finset I :=
  (binOf J φ b).filter fun i => v i q

omit [Fintype Q] in
@[simp] theorem mem_activeSet {s : ℕ} (v : I → Q → Bool) (J : Finset I)
    (φ : I → Fin s) (b : Fin s) (q : Q) (i : I) :
    i ∈ activeSet v J φ b q ↔ (i ∈ J ∧ φ i = b) ∧ v i q = true := by
  simp [activeSet]

/-- `Legal_s(v,J,phi)`: all `s` bins are capacity one. -/
def Legal {s : ℕ} (v : I → Q → Bool) (J : Finset I) (φ : I → Fin s) : Prop :=
  ∀ (b : Fin s) (q : Q), (activeSet v J φ b q).card ≤ 1

/-- `Over(v,J,phi)`, the set of overloaded coordinates. -/
def Over {s : ℕ} (v : I → Q → Bool) (J : Finset I) (φ : I → Fin s) : Finset Q :=
  Finset.univ.filter fun q => ∃ b : Fin s, 2 ≤ (activeSet v J φ b q).card

@[simp] theorem mem_Over {s : ℕ} (v : I → Q → Bool) (J : Finset I)
    (φ : I → Fin s) (q : Q) :
    q ∈ Over v J φ ↔ ∃ b : Fin s, 2 ≤ (activeSet v J φ b q).card := by
  simp [Over]

/-- `Wit(v,J,phi)` of `eq:source-witness-set`: the coordinates carrying an
**overload-plus-neutral witness** -- some bin contains both an overload and a
retained row neutral there.

Reader counterpart: `A-stage4-details.tex` lines 67--69, "Call a coordinate an
*overload-plus-neutral witness* for a partition if one bin contains two items
active there and also a retained item that is inactive there." -/
def Wit {s : ℕ} (v : I → Q → Bool) (J : Finset I) (φ : I → Fin s) : Finset Q :=
  Finset.univ.filter fun q =>
    ∃ b : Fin s, 2 ≤ (activeSet v J φ b q).card ∧
      ∃ i ∈ binOf J φ b, v i q = false

@[simp] theorem mem_Wit {s : ℕ} (v : I → Q → Bool) (J : Finset I)
    (φ : I → Fin s) (q : Q) :
    q ∈ Wit v J φ ↔ ∃ b : Fin s, 2 ≤ (activeSet v J φ b q).card ∧
      ∃ i ∈ binOf J φ b, v i q = false := by
  simp [Wit]

/-! ### Aux-lemma battery A3: general properties of the packing vocabulary -/

/-- Every witness coordinate is overloaded: `Wit ⊆ Over`. -/
theorem wit_subset_over {s : ℕ} (v : I → Q → Bool) (J : Finset I)
    (φ : I → Fin s) : Wit v J φ ⊆ Over v J φ := by
  intro q hq
  rw [mem_Wit] at hq
  obtain ⟨b, hb, _⟩ := hq
  exact mem_Over .. |>.mpr ⟨b, hb⟩

/-- The frozen "Equivalently, its set of overloaded coordinates ... is empty":
legality is exactly emptiness of `Over`. -/
theorem legal_iff_over_empty {s : ℕ} (v : I → Q → Bool) (J : Finset I)
    (φ : I → Fin s) : Legal v J φ ↔ Over v J φ = ∅ := by
  constructor
  · intro h
    ext q
    simp only [mem_Over, Finset.notMem_empty, iff_false, not_exists, not_le]
    exact fun b => lt_of_le_of_lt (h b q) (by norm_num)
  · intro h b q
    by_contra hc
    have : q ∈ Over v J φ := mem_Over .. |>.mpr ⟨b, by omega⟩
    simp [h] at this

omit [Fintype Q] in
/-- Monotonicity of the active sets in the retained-row set. -/
theorem activeSet_subset {s : ℕ} (v : I → Q → Bool) {J J' : Finset I}
    (hJ : J' ⊆ J) (φ : I → Fin s) (b : Fin s) (q : Q) :
    activeSet v J' φ b q ⊆ activeSet v J φ b q := by
  intro i hi
  rw [mem_activeSet] at hi ⊢
  exact ⟨⟨hJ hi.1.1, hi.1.2⟩, hi.2⟩

omit [Fintype Q] in
/-- The closing sentence of `lem:source-completeness`: "restricting a legal
full packing to any retained-row set remains legal". -/
theorem Legal.mono {s : ℕ} {v : I → Q → Bool} {J J' : Finset I} (hJ : J' ⊆ J)
    {φ : I → Fin s} (h : Legal v J φ) : Legal v J' φ :=
  fun b q => le_trans (Finset.card_le_card (activeSet_subset v hJ φ b q)) (h b q)

/-- Deleting rows can only shrink the overloaded set. -/
theorem over_subset {s : ℕ} (v : I → Q → Bool) {J J' : Finset I} (hJ : J' ⊆ J)
    (φ : I → Fin s) : Over v J' φ ⊆ Over v J φ := by
  intro q hq
  rw [mem_Over] at hq ⊢
  obtain ⟨b, hb⟩ := hq
  exact ⟨b, le_trans hb (Finset.card_le_card (activeSet_subset v hJ φ b q))⟩

/-- Two distinct retained rows of one bin, both active at `q`, overload `q`.
This is the only route by which an overload is produced below. -/
theorem mem_Over_of_two {s : ℕ} (v : I → Q → Bool) (J : Finset I)
    (φ : I → Fin s) (q : Q) {i j : I} (hij : i ≠ j)
    (hi : i ∈ J) (hj : j ∈ J) (hb : φ i = φ j)
    (hvi : v i q = true) (hvj : v j q = true) : q ∈ Over v J φ := by
  classical
  rw [mem_Over]
  refine ⟨φ i, ?_⟩
  have hsub : ({i, j} : Finset I) ⊆ activeSet v J φ (φ i) q := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_activeSet .. |>.mpr ⟨⟨hi, rfl⟩, hvi⟩
    · exact mem_activeSet .. |>.mpr ⟨⟨hj, hb.symm⟩, hvj⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton] at this

end Packing

/-! ## `def:unslabbed-guarded-copy` (04:278--309) -/

/-- The row carrier `I_0(G,s) = V u [s-3]` of `def:unslabbed-guarded-copy`.
`Sum.inl` is the injection `vtx`, `Sum.inr` is `blk`. -/
abbrev Row (V : Type*) (s : ℕ) : Type _ := V ⊕ Fin (s - 3)

/-- The coordinate carrier `Q_0(G) = E u (E x [2])`.  `Sum.inl` is the
injection `edge`, `Sum.inr` is `guard`. -/
abbrev Coord (E : Type*) : Type _ := E ⊕ Inc E

/-- The bins **not** occupied by a blocker.  Both frozen proofs of this section
use it: `lem:source-completeness` ("Let `C` be the three-element complement of
the blocker-bin image") and `lem:source-one-copy` ("Colour the other surviving
vertices by the increasing rank of their three nonblocker bins"). -/
def freeBins {V : Type*} {s : ℕ} (φ : Row V s → Fin s) : Finset (Fin s) :=
  (Finset.univ.image fun k : Fin (s - 3) => φ (Sum.inr k))ᶜ

/-- When the blockers occupy distinct bins there are exactly three free bins.
This is where `s - 3` blockers in `[s]` produce the frozen "three-element
complement", and it needs nothing but `s >= 3`. -/
theorem freeBins_card {V : Type*} {s : ℕ} (hs : 3 ≤ s) {φ : Row V s → Fin s}
    (hinj : Function.Injective fun k : Fin (s - 3) => φ (Sum.inr k)) :
    (freeBins φ).card = 3 := by
  rw [freeBins, Finset.card_compl, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

/-- A bin outside `freeBins` is a blocker bin. -/
theorem exists_blocker_of_notMem_freeBins {V : Type*} {s : ℕ}
    {φ : Row V s → Fin s} {b : Fin s} (hb : b ∉ freeBins φ) :
    ∃ k : Fin (s - 3), φ (Sum.inr k) = b := by
  rw [freeBins, Finset.notMem_compl] at hb
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hb
  exact ⟨k, hk⟩

namespace EndpointGraph

/-- The **unslabbed guarded copy** `U(G,s)` of `def:unslabbed-guarded-copy`,
as the binary row system `v^0 : I_0 -> Q_0 -> {0,1}` (`Bool`, with `true` for
`1`).  The four displayed clauses are exhaustive because both carriers are
tagged sums, and here that is the pattern match itself (`M9`).

Reader item: **none** (see the module header: the reader's evaluators
`eq:paper-guarded-edge-evaluator`/`eq:paper-guarded-incidence-evaluator` carry
the slab guard `r = r'`). -/
def unslabbedRow (G : EndpointGraph V E) (s : ℕ) : Row V s → Coord E → Bool
  | Sum.inl u, Sum.inl e => decide (u = G.bd₀ e ∨ u = G.bd₁ e)
  | Sum.inl u, Sum.inr p => decide (u = G.bd p.1 p.2)
  | Sum.inr _, _ => true

@[simp] theorem unslabbedRow_vtx_edge (G : EndpointGraph V E) (s : ℕ) (u : V)
    (e : E) :
    G.unslabbedRow s (Sum.inl u) (Sum.inl e)
      = decide (u = G.bd₀ e ∨ u = G.bd₁ e) := rfl

@[simp] theorem unslabbedRow_vtx_guard (G : EndpointGraph V E) (s : ℕ) (u : V)
    (p : Inc E) :
    G.unslabbedRow s (Sum.inl u) (Sum.inr p) = decide (u = G.vert p) := rfl

@[simp] theorem unslabbedRow_blk (G : EndpointGraph V E) (s : ℕ)
    (k : Fin (s - 3)) (q : Coord E) : G.unslabbedRow s (Sum.inr k) q = true := by
  cases q <;> rfl

/-- The rows active on a coordinate. -/
def activeRows (G : EndpointGraph V E) (s : ℕ) (q : Coord E) : Finset (Row V s) :=
  Finset.univ.filter fun i => G.unslabbedRow s i q

/-! ### Aux-lemma battery A4: the exact activity counts of the frozen
definition -/

/-- Splitting a filter over a tagged sum into its two tagged halves.  This is
the `M9` bookkeeping behind every count below: the two halves of `I_0 = V u
[s-3]` are counted separately and nothing is left implicit. -/
theorem card_filter_sum {A B : Type*} [Fintype A] [Fintype B]
    (P : A ⊕ B → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card
      = (Finset.univ.filter fun a : A => P (Sum.inl a)).card
        + (Finset.univ.filter fun b : B => P (Sum.inr b)).card := by
  classical
  simp only [Finset.card_filter]
  exact Fintype.sum_sum_type _

omit [DecidableEq V] [DecidableEq E] in
/-- "Thus `|Q_0(G)| = 3|E|`."  Reader item: none (the reader's
`eq:paper-guarded-size` is the slabbed count `12 s m_G`). -/
theorem card_coord : Fintype.card (Coord E) = 3 * Fintype.card E := by
  simp [Coord, Inc, Fintype.card_sum, Fintype.card_prod]
  ring

theorem card_row (V : Type*) [Fintype V] (s : ℕ) :
    Fintype.card (Row V s) = Fintype.card V + (s - 3) := by
  simp [Row, Fintype.card_sum]

/-- "An edge coordinate is active on exactly `s-1` rows."  The two vertex rows
are distinct precisely because the frozen record is loopless -- the hardest
field of `EndpointGraph` is doing the work here. -/
theorem card_activeRows_edge (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (e : E) : (G.activeRows s (Sum.inl e)).card = s - 1 := by
  classical
  rw [activeRows, card_filter_sum]
  have h1 : (Finset.univ.filter
      fun u : V => G.unslabbedRow s (Sum.inl u) (Sum.inl e) = true)
      = ({G.bd₀ e, G.bd₁ e} : Finset V) := by
    ext u; simp
  have h2 : (Finset.univ.filter
      fun k : Fin (s - 3) => G.unslabbedRow s (Sum.inr k) (Sum.inl e) = true)
      = (Finset.univ : Finset (Fin (s - 3))) := by
    ext k; simp
  rw [h1, h2, Finset.card_insert_of_notMem (by simpa using G.loopless e),
    Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
  omega

/-- "A guard coordinate [is active] on exactly `s-2` rows." -/
theorem card_activeRows_guard (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (p : Inc E) : (G.activeRows s (Sum.inr p)).card = s - 2 := by
  classical
  rw [activeRows, card_filter_sum]
  have h1 : (Finset.univ.filter
      fun u : V => G.unslabbedRow s (Sum.inl u) (Sum.inr p) = true)
      = ({G.vert p} : Finset V) := by
    ext u; simp
  have h2 : (Finset.univ.filter
      fun k : Fin (s - 3) => G.unslabbedRow s (Sum.inr k) (Sum.inr p) = true)
      = (Finset.univ : Finset (Fin (s - 3))) := by
    ext k; simp
  rw [h1, h2, Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
  omega

/-- "In particular, every coordinate is active on at most `s` rows."

Reader counterpart: `A-stage4-details.tex` lines 64--65, "Each coordinate is
active on at most `s` items." -/
theorem card_activeRows_le (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (q : Coord E) : (G.activeRows s q).card ≤ s := by
  cases q with
  | inl e => rw [G.card_activeRows_edge hs e]; omega
  | inr p => rw [G.card_activeRows_guard hs p]; omega

/-- The total active incidence count of one unslabbed copy, `m(3s-5)`.  (The
reader's `eq:paper-guarded-active-incidences` is the slabbed `4 s m_G (3s-5)`
and is not claimed here.) -/
theorem sum_card_activeRows (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s) :
    ∑ q : Coord E, (G.activeRows s q).card = Fintype.card E * (3 * s - 5) := by
  classical
  rw [Fintype.sum_sum_type]
  have h1 : ∑ e : E, (G.activeRows s (Sum.inl e)).card
      = Fintype.card E * (s - 1) := by
    simp [G.card_activeRows_edge hs, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have h2 : ∑ p : Inc E, (G.activeRows s (Sum.inr p)).card
      = 2 * Fintype.card E * (s - 2) := by
    simp only [G.card_activeRows_guard hs, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, card_inc]
  rw [h1, h2]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e1 : 3 + t - 1 = t + 2 := by omega
  have e2 : 3 + t - 2 = t + 1 := by omega
  have e3 : 3 * (3 + t) - 5 = 3 * t + 4 := by omega
  rw [e1, e2, e3]
  ring

end EndpointGraph

/-! ## The public deletion fractions (04:311--323) -/

namespace EndpointGraph

/-- `delta_v(G;gamma,Delta) = gamma m / (2 Delta N)` with `N = |V|`, `m = |E|`.

Reader counterpart: the `delta_v` half of
`eq:paper-source-stability-constants` (`A-stage4-details.tex`, label line 73,
display line 71).  The `zeta = gamma/24` half is slab-layer data and is not
claimed here.  The frozen display writes `delta_v(G;gamma,Delta)`; the
dependence on `G` is through `N = |V|` and `m = |E|` only, so the graph
argument is retained for the frozen notation but is not read. -/
def deltaV (_G : EndpointGraph V E) (γ : ℚ) (Δ : ℕ) : ℚ :=
  γ * (Fintype.card E : ℚ) / (2 * (Δ : ℚ) * (Fintype.card V : ℚ))

/-- `delta_* = gamma / (4 Delta)`. -/
def deltaStar (γ : ℚ) (Δ : ℕ) : ℚ := γ / (4 * (Δ : ℚ))

/-- "Whenever `SourceCommon(G;gamma,Delta)` holds, `m >= N/2` and hence
`delta_v(G;gamma,Delta) >= delta_*`." -/
theorem deltaStar_le_deltaV (G : EndpointGraph V E) {γ : ℚ} (hγ : 0 < γ)
    {Δ : ℕ} (hΔ : 0 < Δ) (h : G.SourceCommon γ Δ) :
    deltaStar γ Δ ≤ G.deltaV γ Δ := by
  have hN : (0:ℚ) < (Fintype.card V : ℚ) := by exact_mod_cast G.card_vertex_pos
  have hΔq : (0:ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  have hdens : (Fintype.card V : ℚ) ≤ 2 * (Fintype.card E : ℚ) := by
    exact_mod_cast h.1
  have key : γ * (Fintype.card E : ℚ) / (2 * (Δ : ℚ) * (Fintype.card V : ℚ))
        - γ / (4 * (Δ : ℚ))
      = γ * (2 * (Fintype.card E : ℚ) - (Fintype.card V : ℚ))
          / (4 * (Δ : ℚ) * (Fintype.card V : ℚ)) := by
    field_simp
    ring
  rw [deltaStar, deltaV, ← sub_nonneg, key]
  exact div_nonneg (by nlinarith) (by positivity)

/-- The frozen abbreviation `delta_v(G) N = gamma m / (2 Delta)`: the deletion
budget does not depend on `N`.  This is the form used in
`lem:source-one-copy`. -/
theorem deltaV_mul_card (G : EndpointGraph V E) (γ : ℚ) {Δ : ℕ} (hΔ : 0 < Δ) :
    G.deltaV γ Δ * (Fintype.card V : ℚ)
      = γ * (Fintype.card E : ℚ) / (2 * (Δ : ℚ)) := by
  have hN : (0:ℚ) < (Fintype.card V : ℚ) := by exact_mod_cast G.card_vertex_pos
  have hΔq : (0:ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  simp only [deltaV]
  field_simp

/-! ## `lem:source-completeness` (04:325--343)

> Let `G` be an ordered endpoint graph with no isolated vertices and let
> `s >= 4`.  The full retained-row set `J = I_0(G,s)` of `U(G,s)` admits a
> legal capacity-one `s`-bin packing if and only if `SourceYES(G)`.

Reader item: **none.**  `thm:paper-guarded-source` is stated for the slabbed
`I(G,s) = [4s] x (V u [s-3])`, a different carrier, and its one-slab content
appears in the reader only inside proof prose (`A-stage4-details.tex`
lines 106--110). -/

/-- A nonisolated vertex carries an incidence. -/
theorem exists_inc (G : EndpointGraph V E) {u : V} (h : 1 ≤ G.degree u) :
    ∃ p : Inc E, G.vert p = u := by
  have : (G.incFinset u).Nonempty := Finset.card_pos.mp h
  obtain ⟨p, hp⟩ := this
  exact ⟨p, (mem_incFinset ..).mp hp⟩

theorem source_completeness (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    (hnoiso : ∀ u : V, 1 ≤ G.degree u) :
    (∃ φ : Row V s → Fin s,
        Legal (G.unslabbedRow s) (Finset.univ : Finset (Row V s)) φ)
      ↔ G.SourceYES := by
  classical
  constructor
  · rintro ⟨φ, hφ⟩
    rw [legal_iff_over_empty] at hφ
    have hnotover : ∀ q : Coord E,
        q ∉ Over (G.unslabbedRow s) (Finset.univ : Finset (Row V s)) φ := by
      intro q hq; rw [hφ] at hq; exact absurd hq (Finset.notMem_empty _)
    -- "the blockers must occupy distinct bins"
    have hblkinj : Function.Injective fun k : Fin (s - 3) => φ (Sum.inr k) := by
      intro k k' hkk'
      by_contra hne
      obtain ⟨e₀⟩ := G.edgeNonempty
      exact hnotover (Sum.inl e₀)
        (mem_Over_of_two (G.unslabbedRow s) Finset.univ φ (Sum.inl e₀)
          (i := (Sum.inr k : Row V s)) (j := (Sum.inr k' : Row V s))
          (by simpa using hne) (Finset.mem_univ _) (Finset.mem_univ _)
          hkk' (by simp) (by simp))
    -- "every nonisolated vertex conflicts with every blocker on one of its
    -- guard coordinates, so all vertices lie in the other three bins"
    have hvtxfree : ∀ u : V, φ (Sum.inl u) ∈ freeBins (V := V) φ := by
      intro u
      by_contra hb
      obtain ⟨k, hk⟩ := exists_blocker_of_notMem_freeBins hb
      obtain ⟨p, hp⟩ := G.exists_inc (hnoiso u)
      refine hnotover (Sum.inr p)
        (mem_Over_of_two (G.unslabbedRow s) Finset.univ φ (Sum.inr p)
          (i := (Sum.inl u : Row V s)) (j := (Sum.inr k : Row V s))
          (by simp) (Finset.mem_univ _) (Finset.mem_univ _) hk.symm ?_ (by simp))
      simp [hp]
    have hC : (freeBins (V := V) φ).card = 3 := freeBins_card (by omega) hblkinj
    -- "map `C` increasingly to `[3]`"
    set iso := (freeBins (V := V) φ).orderIsoOfFin hC with hisodef
    refine ⟨fun u => iso.symm ⟨φ (Sum.inl u), hvtxfree u⟩, ?_⟩
    intro e hcon
    have hsub : (⟨φ (Sum.inl (G.bd e 0)), hvtxfree _⟩ :
          {x // x ∈ freeBins (V := V) φ})
        = ⟨φ (Sum.inl (G.bd e 1)), hvtxfree _⟩ := iso.symm.injective hcon
    have hbins : φ (Sum.inl (G.bd₀ e)) = φ (Sum.inl (G.bd₁ e)) := by
      simpa using congrArg Subtype.val hsub
    exact hnotover (Sum.inl e)
      (mem_Over_of_two (G.unslabbedRow s) Finset.univ φ (Sum.inl e)
        (i := (Sum.inl (G.bd₀ e) : Row V s)) (j := (Sum.inl (G.bd₁ e) : Row V s))
        (by simpa using G.loopless e) (Finset.mem_univ _) (Finset.mem_univ _)
        hbins (by simp) (by simp))
  · rintro ⟨χ, hχ⟩
    -- "place vertices in the three colour bins and put the `s-3` blockers in
    -- distinct remaining bins"
    refine ⟨Sum.elim
      (fun u => (⟨(χ u).val, by have := (χ u).isLt; omega⟩ : Fin s))
      (fun k => (⟨3 + k.val, by have := k.isLt; omega⟩ : Fin s)), ?_⟩
    set φ : Row V s → Fin s := Sum.elim
      (fun u => (⟨(χ u).val, by have := (χ u).isLt; omega⟩ : Fin s))
      (fun k => (⟨3 + k.val, by have := k.isLt; omega⟩ : Fin s)) with hφdef
    have hlt : ∀ u : V, (φ (Sum.inl u)).val < 3 := fun u => (χ u).isLt
    have hge : ∀ k : Fin (s - 3), 3 ≤ (φ (Sum.inr k)).val := fun k => Nat.le_add_right _ _
    intro b q
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [mem_activeSet] at hi hj
    obtain ⟨⟨-, hib⟩, hiv⟩ := hi
    obtain ⟨⟨-, hjb⟩, hjv⟩ := hj
    have hij : φ i = φ j := by rw [hib, hjb]
    match i, j with
    | Sum.inl u, Sum.inl u' =>
      have hχu : χ u = χ u' := by
        have := congrArg Fin.val hij
        simp only [hφdef, Sum.elim_inl] at this
        exact Fin.ext this
      cases q with
      | inl e =>
        simp only [unslabbedRow_vtx_edge, decide_eq_true_eq] at hiv hjv
        rcases hiv with rfl | rfl <;> rcases hjv with h' | h'
        · rw [h']
        · exact absurd (by simpa [h'] using hχu) (hχ e)
        · exact absurd (by simpa [h'] using hχu.symm) (hχ e)
        · rw [h']
      | inr p =>
        simp only [unslabbedRow_vtx_guard, decide_eq_true_eq] at hiv hjv
        rw [hiv, hjv]
    | Sum.inl u, Sum.inr k =>
      have h1 := hlt u
      have h2 := hge k
      rw [hij] at h1
      omega
    | Sum.inr k, Sum.inl u =>
      have h1 := hlt u
      have h2 := hge k
      rw [hij] at h2
      omega
    | Sum.inr k, Sum.inr k' =>
      have := congrArg Fin.val hij
      simp only [hφdef, Sum.elim_inr] at this
      have : k = k' := Fin.ext (by omega)
      rw [this]

/-! ## `lem:source-one-copy` (04:345--382)

> Let `G` be an ordered endpoint graph, let `s >= 4`, let `Delta > 0`, and let
> `gamma` satisfy `0 < gamma <= 1`.  Put `N = |V|` and `m = |E|`, and assume
> `SourceNO(G;gamma)` and `deg_G(u) <= Delta` for `u in V`.  Let
> `J ⊆ I_0(G,s)` retain every blocker and satisfy
> `|{u in V : vtx(u) not in J}| <= delta_v(G;gamma,Delta) N`.  Then every
> `s`-bin assignment `phi : J -> [s]` satisfies
> `|Over(v^0,J,phi)| >= gamma m / 2`.

Reader item: **none**, for the reason recorded at `source_completeness`. -/

theorem source_one_copy (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hno : G.SourceNO γ) (hdeg : ∀ u : V, G.degree u ≤ Δ)
    (J : Finset (Row V s))
    (hblk : ∀ k : Fin (s - 3), (Sum.inr k : Row V s) ∈ J)
    (hdel : ((Finset.univ.filter fun u : V => (Sum.inl u : Row V s) ∉ J).card : ℚ)
              ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))
    (φ : Row V s → Fin s) :
    γ * (Fintype.card E : ℚ) / 2
      ≤ ((Over (G.unslabbedRow s) J φ).card : ℚ) := by
  classical
  have hΔq : (0:ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  have hmq : (0:ℚ) < (Fintype.card E : ℚ) := by exact_mod_cast G.card_edge_pos
  set Del : Finset V :=
    Finset.univ.filter fun u : V => (Sum.inl u : Row V s) ∉ J with hDeldef
  -- The deletion budget, in the frozen form `Delta * |deleted| <= gamma m / 2`.
  have hdelbound : (Δ : ℚ) * (Del.card : ℚ) ≤ γ * (Fintype.card E : ℚ) / 2 := by
    rw [G.deltaV_mul_card γ hΔ] at hdel
    have h1 : (Δ : ℚ) * (Del.card : ℚ)
        ≤ (Δ : ℚ) * (γ * (Fintype.card E : ℚ) / (2 * (Δ : ℚ))) :=
      mul_le_mul_of_nonneg_left hdel (le_of_lt hΔq)
    refine le_trans h1 (le_of_eq ?_)
    field_simp
  by_cases hcase : ∃ k k' : Fin (s - 3), k ≠ k' ∧ φ (Sum.inr k) = φ (Sum.inr k')
  · -- "If two blockers share a bin, every edge and guard coordinate is
    -- overloaded."
    obtain ⟨k, k', hne, heq⟩ := hcase
    have hall : Over (G.unslabbedRow s) J φ = (Finset.univ : Finset (Coord E)) := by
      ext q
      simp only [Finset.mem_univ, iff_true]
      exact mem_Over_of_two (G.unslabbedRow s) J φ q
        (i := (Sum.inr k : Row V s)) (j := (Sum.inr k' : Row V s))
        (by simpa using hne) (hblk k) (hblk k') heq (by simp) (by simp)
    rw [hall, Finset.card_univ, card_coord]
    push_cast
    nlinarith
  · -- The blockers occupy distinct bins.
    have hblkinj : Function.Injective fun k : Fin (s - 3) => φ (Sum.inr k) := by
      intro k k' h
      by_contra hne
      exact hcase ⟨k, k', hne, h⟩
    have hC : (freeBins (V := V) φ).card = 3 := freeBins_card (by omega) hblkinj
    set iso := (freeBins (V := V) φ).orderIsoOfFin hC with hisodef
    -- "Colour the other surviving vertices by the increasing rank of their
    -- three nonblocker bins, and extend the colouring arbitrarily."
    set χ : V → Fin 3 := fun u =>
      if h : φ (Sum.inl u) ∈ freeBins (V := V) φ then iso.symm ⟨_, h⟩ else 0
      with hχdef
    -- `S`: the surviving vertices placed in blocker bins.
    set S : Finset V := Finset.univ.filter (fun u : V =>
      (Sum.inl u : Row V s) ∈ J ∧ φ (Sum.inl u) ∉ freeBins (V := V) φ) with hSdef
    -- "Their tagged guard coordinates give `t` distinct overloads."
    set GuardOver : Finset (Inc E) :=
      Finset.univ.filter (fun p : Inc E => G.vert p ∈ S) with hGOdef
    have hguard : ∀ p ∈ GuardOver, (Sum.inr p : Coord E) ∈ Over (G.unslabbedRow s) J φ := by
      intro p hp
      rw [hGOdef, Finset.mem_filter, hSdef, Finset.mem_filter] at hp
      obtain ⟨-, -, hJ, hfree⟩ := hp
      obtain ⟨k, hk⟩ := exists_blocker_of_notMem_freeBins hfree
      exact mem_Over_of_two (G.unslabbedRow s) J φ (Sum.inr p)
        (i := (Sum.inl (G.vert p) : Row V s)) (j := (Sum.inr k : Row V s))
        (by simp) hJ (hblk k) hk.symm (by simp) (by simp)
    -- The monochromatic edges of the induced colouring.
    set Mono : Finset E := G.monoFinset χ with hMonodef
    set touched : E → Prop :=
      fun e => ∃ b : Fin 2, G.vert (e, b) ∈ S ∨ G.vert (e, b) ∈ Del with htouch
    set Bad : Finset E := Mono.filter touched with hBaddef
    set Good : Finset E := Mono.filter (fun e => ¬ touched e) with hGooddef
    have hsplit : Bad.card + Good.card = Mono.card :=
      Finset.card_filter_add_card_filter_not _
    -- "At most `t + Delta |deleted|` monochromatic edge occurrences meet `S`
    -- or a deleted vertex."
    have hbad : Bad.card ≤ GuardOver.card + Δ * Del.card := by
      have hsubset : Bad ⊆
          (Finset.univ.filter fun p : Inc E => G.vert p ∈ S ∪ Del).image Prod.fst := by
        intro e he
        rw [hBaddef, Finset.mem_filter, htouch] at he
        obtain ⟨-, b, hb⟩ := he
        exact Finset.mem_image.mpr ⟨(e, b), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          exact hb, rfl⟩
      calc Bad.card
          ≤ ((Finset.univ.filter fun p : Inc E => G.vert p ∈ S ∪ Del).image
              Prod.fst).card := Finset.card_le_card hsubset
        _ ≤ (Finset.univ.filter fun p : Inc E => G.vert p ∈ S ∪ Del).card :=
              Finset.card_image_le
        _ = ∑ u ∈ S ∪ Del, G.degree u := G.card_inc_mem _
        _ ≤ (∑ u ∈ S, G.degree u) + ∑ u ∈ Del, G.degree u := by
              have hui : (∑ u ∈ S ∪ Del, G.degree u) + ∑ u ∈ S ∩ Del, G.degree u
                  = (∑ u ∈ S, G.degree u) + ∑ u ∈ Del, G.degree u :=
                Finset.sum_union_inter
              omega
        _ = GuardOver.card + ∑ u ∈ Del, G.degree u := by
              rw [hGOdef, G.card_inc_mem S]
        _ ≤ GuardOver.card + Δ * Del.card := by
              have h2 : ∑ u ∈ Del, G.degree u ≤ Del.card * Δ := by
                simpa using Finset.sum_le_sum fun u (_ : u ∈ Del) => hdeg u
              rw [Nat.mul_comm Δ Del.card]
              exact Nat.add_le_add_left h2 _
    -- "Every remaining monochromatic edge is an additional overloaded edge
    -- coordinate."
    have hgood : ∀ e ∈ Good, (Sum.inl e : Coord E) ∈ Over (G.unslabbedRow s) J φ := by
      intro e he
      rw [hGooddef, Finset.mem_filter, hMonodef, mem_monoFinset, htouch] at he
      obtain ⟨hmono, hnt⟩ := he
      have hsurv : ∀ b : Fin 2, (Sum.inl (G.bd e b) : Row V s) ∈ J
          ∧ φ (Sum.inl (G.bd e b)) ∈ freeBins (V := V) φ := by
        intro b
        have hb : ¬ (G.vert (e, b) ∈ S ∨ G.vert (e, b) ∈ Del) := fun h => hnt ⟨b, h⟩
        have hbS : G.bd e b ∉ S := fun h => hb (Or.inl h)
        have hbD : G.bd e b ∉ Del := fun h => hb (Or.inr h)
        rw [hDeldef, Finset.mem_filter] at hbD
        have hJ : (Sum.inl (G.bd e b) : Row V s) ∈ J := by
          by_contra hc
          exact hbD ⟨Finset.mem_univ _, hc⟩
        refine ⟨hJ, ?_⟩
        by_contra hfree
        exact hbS (by
          rw [hSdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hJ, hfree⟩)
      obtain ⟨hJ0, hf0⟩ := hsurv 0
      obtain ⟨hJ1, hf1⟩ := hsurv 1
      have hχ0 : χ (G.bd e 0) = iso.symm ⟨φ (Sum.inl (G.bd e 0)), hf0⟩ := by
        simp only [hχdef]; rw [dif_pos hf0]
      have hχ1 : χ (G.bd e 1) = iso.symm ⟨φ (Sum.inl (G.bd e 1)), hf1⟩ := by
        simp only [hχdef]; rw [dif_pos hf1]
      have hsub : (⟨φ (Sum.inl (G.bd e 0)), hf0⟩ : {x // x ∈ freeBins (V := V) φ})
          = ⟨φ (Sum.inl (G.bd e 1)), hf1⟩ :=
        iso.symm.injective (by rw [← hχ0, ← hχ1]; exact hmono)
      have hbins : φ (Sum.inl (G.bd₀ e)) = φ (Sum.inl (G.bd₁ e)) := by
        simpa using congrArg Subtype.val hsub
      exact mem_Over_of_two (G.unslabbedRow s) J φ (Sum.inl e)
        (i := (Sum.inl (G.bd₀ e) : Row V s)) (j := (Sum.inl (G.bd₁ e) : Row V s))
        (by simpa using G.loopless e) (by simpa using hJ0) (by simpa using hJ1)
        hbins (by simp) (by simp)
    -- The edge overloads and the guard overloads are disjoint tagged
    -- coordinates, so the two counts add.
    have hunion : (Good.image (Sum.inl : E → Coord E))
        ∪ (GuardOver.image (Sum.inr : Inc E → Coord E))
          ⊆ Over (G.unslabbedRow s) J φ := by
      intro q hq
      rcases Finset.mem_union.mp hq with h | h
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
        exact hgood e he
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        exact hguard p hp
    have hdisj : Disjoint (Good.image (Sum.inl : E → Coord E))
        (GuardOver.image (Sum.inr : Inc E → Coord E)) := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨p, -, hcon⟩ := Finset.mem_image.mp hq'
      exact Sum.inl_ne_inr hcon.symm
    have hover : Good.card + GuardOver.card ≤ (Over (G.unslabbedRow s) J φ).card := by
      have h1 := Finset.card_le_card hunion
      rwa [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_image_of_injective _ Sum.inr_injective] at h1
    -- Assemble: `gamma m <= |Bad| + |Good|` and `|Bad| <= t + Delta |deleted|`.
    have hmono : γ * (Fintype.card E : ℚ) ≤ (Mono.card : ℚ) := hno χ
    have hsplitq : (Bad.card : ℚ) + (Good.card : ℚ) = (Mono.card : ℚ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hsplit
    have hbadq : (Bad.card : ℚ) ≤ (GuardOver.card : ℚ) + (Δ : ℚ) * (Del.card : ℚ) := by
      exact_mod_cast hbad
    have hoverq : (Good.card : ℚ) + (GuardOver.card : ℚ)
        ≤ ((Over (G.unslabbedRow s) J φ).card : ℚ) := by
      exact_mod_cast hover
    linarith

/-! ## Disjoint copies (04:196--204)

The final paragraph of the proof of `thm:gap-colouring` outputs "the disjoint
union of `r` copies of `G^+`".  Only the copy construction itself is landed
here; the `G_0 u K_2` padding and the choice of `r` are the arithmetic lemmas
`copyCount_*` below. -/

/-- `r` disjoint copies of `G`.  The two linear orders of the copy carrier are
built from `G`'s, which is exactly why `def:endpoint-graph-adapter` is
transcribed with the orders as fields. -/
def copies (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r) :
    EndpointGraph (Fin r × V) (Fin r × E) where
  orderV := by
    letI := G.orderV
    exact LinearOrder.lift' (fun p : Fin r × V => (toLex p : Fin r ×ₗ V))
      (fun _ _ h => h)
  orderE := by
    letI := G.orderE
    exact LinearOrder.lift' (fun p : Fin r × E => (toLex p : Fin r ×ₗ E))
      (fun _ _ h => h)
  vertexNonempty := ⟨(⟨0, hr⟩, G.vertexNonempty.some)⟩
  edgeNonempty := ⟨(⟨0, hr⟩, G.edgeNonempty.some)⟩
  bd₀ := fun p => (p.1, G.bd₀ p.2)
  bd₁ := fun p => (p.1, G.bd₁ p.2)
  loopless := by
    rintro ⟨c, e⟩ h
    exact G.loopless e (congrArg Prod.snd h)

@[simp] theorem copies_bd (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r)
    (p : Fin r × E) (b : Fin 2) :
    (G.copies r hr).bd p b = (p.1, G.bd p.2 b) := by
  fin_cases b <;> simp [bd, copies]

@[simp] theorem copies_vert (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r)
    (p : Inc (Fin r × E)) :
    (G.copies r hr).vert p = (p.1.1, G.vert (p.1.2, p.2)) := by
  simp [vert]

theorem degree_copies (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r)
    (c : Fin r) (u : V) : (G.copies r hr).degree (c, u) = G.degree u := by
  classical
  rw [degree, degree]
  refine Finset.card_bij (fun p _ => (p.1.2, p.2)) ?_ ?_ ?_
  · rintro ⟨⟨c', e⟩, b⟩ hp
    simp only [mem_incFinset, copies_vert, Prod.mk.injEq] at hp
    rw [mem_incFinset]
    exact hp.2
  · rintro ⟨⟨c₁, e₁⟩, b₁⟩ h₁ ⟨⟨c₂, e₂⟩, b₂⟩ h₂ h
    simp only [mem_incFinset, copies_vert, Prod.mk.injEq] at h₁ h₂
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h₁
    obtain ⟨rfl, -⟩ := h₂
    simp [h.1, h.2]
  · rintro ⟨e, b⟩ he
    rw [mem_incFinset] at he
    refine ⟨((c, e), b), ?_, rfl⟩
    simp only [mem_incFinset, copies_vert, Prod.mk.injEq]
    exact ⟨trivial, he⟩

omit [DecidableEq V] [DecidableEq E] in
theorem card_copies_edge (r : ℕ) :
    Fintype.card (Fin r × E) = r * Fintype.card E := by
  simp [Fintype.card_prod]

theorem sourceYES_copies (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r)
    (h : G.SourceYES) : (G.copies r hr).SourceYES := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨fun p => χ p.2, fun e => ?_⟩
  simpa using hχ e.2

theorem monoFinset_copies_card (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r)
    (χ : Fin r × V → Fin 3) :
    ((G.copies r hr).monoFinset χ).card
      = ∑ c : Fin r, (G.monoFinset fun u => χ (c, u)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (t := (Finset.univ : Finset (Fin r))) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · rintro ⟨c', e⟩ hp
    simp only [Finset.mem_filter, mem_monoFinset, copies_bd] at hp
    obtain ⟨hmono, rfl⟩ := hp
    rw [mem_monoFinset]
    simpa using hmono
  · rintro ⟨c₁, e₁⟩ h₁ ⟨c₂, e₂⟩ h₂ h
    simp only [Finset.mem_filter] at h₁ h₂
    exact Prod.ext (h₁.2.trans h₂.2.symm) h
  · intro e he
    rw [mem_monoFinset] at he
    refine ⟨(c, e), ?_, rfl⟩
    simp only [Finset.mem_filter, mem_monoFinset, copies_bd]
    exact ⟨by simpa using he, trivial⟩

theorem sourceNO_copies (G : EndpointGraph V E) (r : ℕ) (hr : 0 < r) {γ : ℚ}
    (h : G.SourceNO γ) : (G.copies r hr).SourceNO γ := by
  intro χ
  rw [monoFinset_copies_card, card_copies_edge]
  push_cast
  calc γ * ((r : ℚ) * (Fintype.card E : ℚ))
      = ∑ _c : Fin r, γ * (Fintype.card E : ℚ) := by
        simp [Finset.sum_const, Finset.card_univ]; ring
    _ ≤ ∑ c : Fin r, ((G.monoFinset fun u => χ (c, u)).card : ℚ) :=
        Finset.sum_le_sum fun c _ => h _

end EndpointGraph

/-! ## `thm:gap-colouring` (04:85--218)

The frozen theorem's proof cites, in order,

* Impagliazzo--Paturi--Zane sparsification (`\cite{impagliazzo2001which}`),
* Dinur's PCP theorem (`\cite{dinur2007pcp}`: Lemma 8.3, Theorem 1.5 applied
  `O(log log L)` times, then Lemma 1.7), and
* Bogdanov--Obata--Trevisan Theorem 14 (`\cite{bogdanov2002lower}`), using
  only its global counting paragraph and **not** its separate
  local-satisfiability conclusion.

None of these becomes an axiom.  They enter as the two named records
`DinurConstraintGraph` and `GapColouringOutput`.  What is proved outright here
is the frozen bookkeeping: the exact-`3`-CNF clause count `K_cl` and its
consequence `eps_B > 0`, the damaged-clause identity `16 eta k_B n_B = 8M`,
the `eta < eps_B/16 <= 1/16` estimate, the fixed fraction `gamma_0`, and the
`r`-copy padding arithmetic. -/

/-- The frozen width function `g(1)=4, g(2)=2, g(3)=1, g(r)=r-2 (r >= 4)` used
in the exact-`3` conversion.  The frozen text defines it for `r >= 1` only;
`gWidth 0 = 0` here is outside that range and is never used. -/
def gWidth : ℕ → ℕ
  | 1 => 4
  | 2 => 2
  | 3 => 1
  | r => r - 2

/-- Only the widths `1` and `2` are genuinely special: from `r >= 3` the frozen
table already agrees with `r - 2`. -/
theorem gWidth_eq_sub {r : ℕ} (hr : 3 ≤ r) : gWidth r = r - 2 := by
  match r, hr with
  | 3, _ => rfl
  | (n + 4), _ => rfl

/-- `K_cl = 2(g(A) + 2 C(A,2)) + 4A^2`, the frozen bound on the number of exact
clauses produced per constraint. -/
def Kcl (A : ℕ) : ℕ := 2 * (gWidth A + 2 * A.choose 2) + 4 * A ^ 2

@[simp] theorem Kcl_one : Kcl 1 = 12 := rfl
@[simp] theorem Kcl_two : Kcl 2 = 24 := rfl
@[simp] theorem Kcl_three : Kcl 3 = 50 := rfl

/-- `K_cl(A) > 0` for every alphabet of size at least one.  This is what makes
the frozen `eps_B` well defined and positive. -/
theorem Kcl_pos {A : ℕ} (hA : 1 ≤ A) : 0 < Kcl A := by
  have : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  simp only [Kcl]
  omega

/-- The cited constraint graph `G_D = (U,F)` of the Dinur chain, as **named
data**: alphabet size `A = |Sigma|`, maximum degree `d`, and `NO`-case
rejected-constraint fraction `rho > 0`.  No field carries a conclusion of the
frozen theorem. -/
structure DinurConstraintGraph where
  /-- `A = |Sigma|`, the constant alphabet size. -/
  A : ℕ
  /-- `d`, the maximum constraint degree. -/
  d : ℕ
  /-- `rho > 0`, the `NO`-case rejected-constraint fraction. -/
  ρ : ℚ
  /-- Constant alphabets are nonempty. -/
  A_pos : 1 ≤ A
  /-- `rho > 0`. -/
  ρ_pos : 0 < ρ
  /-- `rho` is a fraction. -/
  ρ_le_one : ρ ≤ 1

namespace DinurConstraintGraph

/-- `eps_B = rho / (2 K_cl max{1,d})`, the frozen falsified-clause fraction. -/
def epsB (D : DinurConstraintGraph) : ℚ :=
  D.ρ / (2 * (Kcl D.A : ℚ) * (max 1 D.d : ℚ))

/-- The frozen assertion `eps_B > 0`, proved outright. -/
theorem epsB_pos (D : DinurConstraintGraph) : 0 < D.epsB := by
  have hK : (0:ℚ) < (Kcl D.A : ℚ) := by exact_mod_cast Kcl_pos D.A_pos
  have hd : (1:ℚ) ≤ (max 1 D.d : ℚ) := by
    exact_mod_cast Nat.le_max_left 1 D.d
  exact div_pos D.ρ_pos (by nlinarith)

/-- `eps_B <= 1/2`, hence the frozen chain `eta < eps_B/16 <= 1/16` closes. -/
theorem epsB_le_half (D : DinurConstraintGraph) : D.epsB ≤ 1 / 2 := by
  have hK : (1:ℚ) ≤ (Kcl D.A : ℚ) := by exact_mod_cast Kcl_pos D.A_pos
  have hd : (1:ℚ) ≤ (max 1 D.d : ℚ) := by
    exact_mod_cast Nat.le_max_left 1 D.d
  rw [epsB, div_le_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith [D.ρ_le_one]

end DinurConstraintGraph

/-! ### The Bogdanov--Obata--Trevisan counting step (04:174--193) -/

/-- The frozen damaged-clause identity `16 eta k_B n_B = 8M` at
`eta = M/(2 k_B n_B)`. -/
theorem damaged_clause_identity (M P : ℚ) (hP : P ≠ 0) :
    16 * (M / (2 * P)) * P = 8 * M := by
  field_simp
  ring

/-- The frozen estimate: if `M < eps_B m_B / 8` and `3 m_B <= k_B n_B` then
`eta = M/(2 k_B n_B) < eps_B/16`, and `eps_B <= 1` makes that at most
`1/16`. -/
theorem eta_lt {M mB P εB : ℚ} (hmB : 0 < mB) (hP : 0 < P) (hden : 3 * mB ≤ P)
    (hε : 0 < εB) (hlt : M < εB * mB / 8) : M / (2 * P) < εB / 16 := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_pos hε hmB, mul_le_mul_of_nonneg_left hden (le_of_lt hε)]

/-- `gamma_0 = eps_B / (24 b_BOT c_BOT)`, the frozen fixed monochromatic-edge
fraction of the Bogdanov--Obata--Trevisan graph. -/
def gamma0 (εB : ℚ) (b c : ℕ) : ℚ := εB / (24 * (b : ℚ) * (c : ℚ))

theorem gamma0_pos {εB : ℚ} (hε : 0 < εB) {b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c) :
    0 < gamma0 εB b c := by
  have hb' : (1:ℚ) ≤ (b:ℚ) := by exact_mod_cast hb
  have hc' : (1:ℚ) ≤ (c:ℚ) := by exact_mod_cast hc
  exact div_pos hε (by nlinarith)

/-- The frozen closing estimate "the final monochromatic-edge fraction is at
least `gamma_0 m_0/(m_0+1) >= gamma_0/2`", for `m_0 >= 1`. -/
theorem gamma0_halving {γ₀ : ℚ} (hγ : 0 < γ₀) {m₀ : ℕ} (hm : 1 ≤ m₀) :
    γ₀ / 2 ≤ γ₀ * (m₀ : ℚ) / ((m₀ : ℚ) + 1) := by
  have hm' : (1:ℚ) ≤ (m₀ : ℚ) := by exact_mod_cast hm
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-! ### The `r`-copy padding arithmetic (04:196--212) -/

/-- `r = max{1, ceil(n/(m_0+1))}` of the frozen construction. -/
def copyCount (n m₀ : ℕ) : ℕ := max 1 ((n + m₀) / (m₀ + 1))

theorem copyCount_pos (n m₀ : ℕ) : 0 < copyCount n m₀ :=
  lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

/-- The frozen `n <= m'` with `m' = r(m_0+1)`. -/
theorem le_copyCount_mul (n m₀ : ℕ) : n ≤ copyCount n m₀ * (m₀ + 1) := by
  have hd : 0 < m₀ + 1 := Nat.succ_pos _
  have hdm : (m₀ + 1) * ((n + m₀) / (m₀ + 1)) + (n + m₀) % (m₀ + 1) = n + m₀ :=
    Nat.div_add_mod _ _
  have hmod : (n + m₀) % (m₀ + 1) < m₀ + 1 := Nat.mod_lt _ hd
  rcases Nat.eq_zero_or_pos ((n + m₀) / (m₀ + 1)) with h | h
  · rw [copyCount, h, Nat.max_eq_left (Nat.zero_le 1), Nat.one_mul]
    rw [h, Nat.mul_zero, Nat.zero_add] at hdm
    omega
  · rw [copyCount, Nat.max_eq_right h, Nat.mul_comm]
    omega

/-- The frozen `m' <= n + m_0 + 1`. -/
theorem copyCount_mul_le (n m₀ : ℕ) : copyCount n m₀ * (m₀ + 1) ≤ n + m₀ + 1 := by
  have hd : 0 < m₀ + 1 := Nat.succ_pos _
  have hdm : (m₀ + 1) * ((n + m₀) / (m₀ + 1)) + (n + m₀) % (m₀ + 1) = n + m₀ :=
    Nat.div_add_mod _ _
  have hmod : (n + m₀) % (m₀ + 1) < m₀ + 1 := Nat.mod_lt _ hd
  rcases Nat.eq_zero_or_pos ((n + m₀) / (m₀ + 1)) with h | h
  · rw [copyCount, h, Nat.max_eq_left (Nat.zero_le 1), Nat.one_mul]
    omega
  · rw [copyCount, Nat.max_eq_right h, Nat.mul_comm]
    omega

/-! ### The closed conditional statement -/

/-- The constants `Delta, c, gamma` whose existence `thm:gap-colouring`
asserts. -/
structure GapColouringConstants where
  /-- The degree bound `Delta >= 1`. -/
  Δ : ℕ
  /-- The size exponent `c >= 1`. -/
  c : ℕ
  /-- The soundness fraction `gamma`. -/
  γ : ℚ
  Δ_pos : 1 ≤ Δ
  c_pos : 1 ≤ c
  γ_pos : 0 < γ
  γ_le_one : γ ≤ 1

/-- The **cited output** of the reduction chain of `thm:gap-colouring` on one
input branch: `n` is the number of variables of the sparse `3`-CNF formula and
`sat` is that formula's satisfiability.  Every field is a clause the cited
chain delivers; none is a conclusion the frozen proof derives.

In particular the frozen conclusion `|E| >= |V|/2` is **not** a field: it is a
consequence of `degree_lb` (`card_vertex_le_two_mul_card_edge`), and restating
it would restate a derived telescope.

The promise is carried exactly as the frozen theorem carries it -- one branch
per case of `sat` -- so the two mutually exclusive predicates are never
conjoined. -/
structure GapColouringOutput (K : GapColouringConstants) (n : ℕ) (sat : Prop)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : Prop where
  /-- `|E| >= n`. -/
  edge_lb : n ≤ Fintype.card E
  /-- `|V| <= n (log_2(n+2))^c`. -/
  vertex_size : (Fintype.card V : ℝ) ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ K.c
  /-- `|E| <= n (log_2(n+2))^c`. -/
  edge_size : (Fintype.card E : ℝ) ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ K.c
  /-- `max_v deg(v) <= Delta`. -/
  degree_ub : ∀ u : V, G.degree u ≤ K.Δ
  /-- `min_v deg(v) >= 1`. -/
  degree_lb : ∀ u : V, 1 ≤ G.degree u
  /-- `YES : SourceYES(G)`. -/
  yes : sat → G.SourceYES
  /-- `NO : SourceNO(G;gamma)`. -/
  no : ¬ sat → G.SourceNO K.γ

/-- **`thm:gap-colouring` as a closed conditional statement.**  Given the
cited chain's output on one input branch, the frozen theorem's displayed
conclusion holds, including the density clause `|E| >= |V|/2` and the closing
"In particular, `SourceCommon(G;gamma,Delta)` holds". -/
theorem gapColouring (K : GapColouringConstants) (n : ℕ) (sat : Prop)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (cited : GapColouringOutput K n sat G) :
    n ≤ Fintype.card E
      ∧ (Fintype.card V : ℝ) ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ K.c
      ∧ (Fintype.card E : ℝ) ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ K.c
      ∧ (∀ u : V, G.degree u ≤ K.Δ)
      ∧ (∀ u : V, 1 ≤ G.degree u)
      ∧ Fintype.card V ≤ 2 * Fintype.card E
      ∧ (sat → G.SourceYES)
      ∧ (¬ sat → G.SourceNO K.γ)
      ∧ G.SourceCommon K.γ K.Δ :=
  ⟨cited.edge_lb, cited.vertex_size, cited.edge_size, cited.degree_ub,
    cited.degree_lb, G.card_vertex_le_two_mul_card_edge cited.degree_lb,
    cited.yes, cited.no,
    ⟨G.card_vertex_le_two_mul_card_edge cited.degree_lb,
      fun u => ⟨cited.degree_lb u, cited.degree_ub u⟩⟩⟩

/-- **Statement pole (hypothesis consistency).**  The frozen theorem is stated
for "a sparse 3-CNF formula with `n` variables"; at `n = 0` its own size clause
`|V| <= n(log_2(n+2))^c = 0` contradicts the nonemptiness of `V` demanded by
`def:endpoint-graph-adapter`.  So `1 <= n` is forced by the frozen text rather
than added to it, and every inhabitant below is taken at a legal `n >= 1`. -/
theorem gapColouringOutput_zero_absurd (K : GapColouringConstants) (sat : Prop)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (cited : GapColouringOutput K 0 sat G) : False := by
  have h := cited.vertex_size
  simp only [Nat.cast_zero, zero_mul] at h
  have hV : (1:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast G.card_vertex_pos
  linarith

/-! ### Non-vacuity: nondegenerate inhabitants at legal parameter values

Every structure introduced above is inhabited here at legal parameters, and
both promise branches of `GapColouringOutput` are inhabited **separately**, so
neither `yes` nor `no` is the field that is vacuously satisfied.  The witnesses
are families indexed by every legal input size `n >= 1`, not a single point:
`K_3`-copies on the `YES` branch and `K_4`-copies on the `NO` branch. -/

/-- The triangle `K_3`, a nondegenerate `EndpointGraph`: the hardest field,
looplessness, is discharged at three genuinely distinct edge occurrences. -/
def K3 : EndpointGraph (Fin 3) (Fin 3) where
  orderV := inferInstance
  orderE := inferInstance
  vertexNonempty := ⟨0⟩
  edgeNonempty := ⟨0⟩
  bd₀ := ![0, 1, 0]
  bd₁ := ![1, 2, 2]
  loopless := by decide

/-- `K_4`, the smallest graph with no proper `3`-colouring. -/
def K4 : EndpointGraph (Fin 4) (Fin 6) where
  orderV := inferInstance
  orderE := inferInstance
  vertexNonempty := ⟨0⟩
  edgeNonempty := ⟨0⟩
  bd₀ := ![0, 0, 0, 1, 1, 2]
  bd₁ := ![1, 2, 3, 2, 3, 3]
  loopless := by decide

theorem k3_degree : ∀ u : Fin 3, K3.degree u = 2 := by decide

theorem k4_degree : ∀ u : Fin 4, K4.degree u = 3 := by decide

theorem k3_sourceYES : K3.SourceYES := ⟨fun u => u, by decide⟩

theorem k4_exists_mono :
    ∀ χ : Fin 4 → Fin 3, ∃ e : Fin 6, χ (K4.bd e 0) = χ (K4.bd e 1) := by decide

theorem k4_sourceNO : K4.SourceNO (1 / 6) := by
  intro χ
  obtain ⟨e, he⟩ := k4_exists_mono χ
  have hne : (K4.monoFinset χ).Nonempty := ⟨e, by rw [EndpointGraph.mem_monoFinset]; exact he⟩
  have h1 : (1:ℚ) ≤ ((K4.monoFinset χ).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hcard : (Fintype.card (Fin 6) : ℚ) = 6 := by simp
  rw [hcard]
  linarith

/-- `K_4` really has no proper `3`-colouring: the `NO` witness is not the
trivial one. -/
theorem k4_not_sourceYES : ¬ K4.SourceYES :=
  fun h => EndpointGraph.sourceYES_not_sourceNO K4 (by norm_num) h k4_sourceNO

/-- `log_2 3 >= 3/2`, the only real-analytic input needed to check the frozen
size clause at every legal input size. -/
theorem three_halves_le_logb {n : ℕ} (hn : 1 ≤ n) :
    (3:ℝ) / 2 ≤ Real.logb 2 ((n : ℝ) + 2) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h89 : Real.log 8 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hn' : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmono : Real.log 3 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [Real.logb, le_div_iff₀ hlog2]
  linarith

/-- The frozen size clause has room for the witnesses below: at `c = 8` the
factor `(log_2(n+2))^c` is at least `6` for every `n >= 1`. -/
theorem six_le_logb_pow {n : ℕ} (hn : 1 ≤ n) :
    (6:ℝ) ≤ (Real.logb 2 ((n : ℝ) + 2)) ^ 8 := by
  have h := three_halves_le_logb hn
  calc (6:ℝ) ≤ ((3:ℝ) / 2) ^ 8 := by norm_num
    _ ≤ (Real.logb 2 ((n : ℝ) + 2)) ^ 8 := by gcongr

/-- Legal constants: `Delta = 3`, `c = 8`, `gamma = 1/6`. -/
def gapConstants : GapColouringConstants where
  Δ := 3
  c := 8
  γ := 1 / 6
  Δ_pos := by norm_num
  c_pos := by norm_num
  γ_pos := by norm_num
  γ_le_one := by norm_num

/-- The `YES` branch of `GapColouringOutput` is inhabited at every legal input
size: `n` disjoint triangles. -/
theorem gapColouringOutput_yes_witness {n : ℕ} (hn : 1 ≤ n) :
    GapColouringOutput gapConstants n True (K3.copies n hn) where
  edge_lb := by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; omega
  vertex_size := by
    have hL := six_le_logb_pow hn
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    change ((Fintype.card (Fin n × Fin 3) : ℕ) : ℝ)
        ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ 8
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    nlinarith
  edge_size := by
    have hL := six_le_logb_pow hn
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    change ((Fintype.card (Fin n × Fin 3) : ℕ) : ℝ)
        ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ 8
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    nlinarith
  degree_ub := by
    rintro ⟨c, u⟩
    rw [EndpointGraph.degree_copies, k3_degree u]
    norm_num [gapConstants]
  degree_lb := by
    rintro ⟨c, u⟩
    rw [EndpointGraph.degree_copies, k3_degree u]
    norm_num
  yes := fun _ => EndpointGraph.sourceYES_copies K3 n hn k3_sourceYES
  no := fun h => absurd trivial h

/-- The `NO` branch of `GapColouringOutput` is inhabited at every legal input
size: `n` disjoint copies of `K_4`.  Together with the `YES` witness this shows
that neither promise field is the vacuous one, and (with
`sourceYES_not_sourceNO`) that the two branches are never conjoined. -/
theorem gapColouringOutput_no_witness {n : ℕ} (hn : 1 ≤ n) :
    GapColouringOutput gapConstants n False (K4.copies n hn) where
  edge_lb := by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; omega
  vertex_size := by
    have hL := six_le_logb_pow hn
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    change ((Fintype.card (Fin n × Fin 4) : ℕ) : ℝ)
        ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ 8
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    nlinarith
  edge_size := by
    have hL := six_le_logb_pow hn
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    change ((Fintype.card (Fin n × Fin 6) : ℕ) : ℝ)
        ≤ (n : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ 8
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    nlinarith
  degree_ub := by
    rintro ⟨c, u⟩
    rw [EndpointGraph.degree_copies, k4_degree u]
    norm_num [gapConstants]
  degree_lb := by
    rintro ⟨c, u⟩
    rw [EndpointGraph.degree_copies, k4_degree u]
    norm_num
  yes := fun h => h.elim
  no := fun _ => EndpointGraph.sourceNO_copies K4 n hn k4_sourceNO

/-- The unslabbed guarded copy, the packing vocabulary, and both frozen lemmas
are inhabited together at the smallest legal `s`: a legal capacity-one packing
of `U(K_3, 4)` exists, and it exists *because* `K_3` is three-colourable. -/
theorem unslabbedGuardedCopy_legal_witness :
    ∃ φ : Row (Fin 3) 4 → Fin 4,
      Legal (K3.unslabbedRow 4) (Finset.univ : Finset (Row (Fin 3) 4)) φ :=
  (K3.source_completeness (by norm_num) (fun u => by rw [k3_degree u]; norm_num)).mpr
    k3_sourceYES

/-- ...and the same carrier admits **no** legal packing once the graph has no
proper colouring: `U(K_4, 4)` is a nondegenerate instance of the failing side.
Without this, `source_completeness` could be satisfied by a construction in
which every assignment is legal. -/
theorem unslabbedGuardedCopy_illegal_witness :
    ¬ ∃ φ : Row (Fin 4) 4 → Fin 4,
      Legal (K4.unslabbedRow 4) (Finset.univ : Finset (Row (Fin 4) 4)) φ := by
  intro h
  exact k4_not_sourceYES
    ((K4.source_completeness (by norm_num) (fun u => by rw [k4_degree u]; norm_num)).mp h)

/-- **Hypothesis consistency for `lem:source-one-copy`.**  Its full hypothesis
bundle is simultaneously satisfiable at legal parameters (`s = 4`,
`Delta = 3`, `gamma = 1/6`, `G = K_4`, and `J` the full row set, which retains
every blocker and deletes no vertex), and what it then delivers is the
**nonvacuous** bound `|Over| >= 1/2`, not the trivial `0 <= |Over|`.  So the
lemma's conclusion is not satisfied by an empty overload set. -/
theorem source_one_copy_witness (φ : Row (Fin 4) 4 → Fin 4) :
    (1:ℚ) / 2
      ≤ ((Over (K4.unslabbedRow 4) (Finset.univ : Finset (Row (Fin 4) 4)) φ).card : ℚ) := by
  have hdel : ((Finset.univ.filter fun u : Fin 4 =>
        (Sum.inl u : Row (Fin 4) 4) ∉ (Finset.univ : Finset (Row (Fin 4) 4))).card : ℚ)
      ≤ K4.deltaV (1 / 6) 3 * (Fintype.card (Fin 4) : ℚ) := by
    have hempty : (Finset.univ.filter fun u : Fin 4 =>
        (Sum.inl u : Row (Fin 4) 4) ∉ (Finset.univ : Finset (Row (Fin 4) 4)))
          = (∅ : Finset (Fin 4)) := by
      ext u; simp
    rw [hempty, Finset.card_empty, Nat.cast_zero, EndpointGraph.deltaV]
    norm_num
  have h := K4.source_one_copy (s := 4) (by norm_num) (Δ := 3) (by norm_num)
    (γ := 1 / 6) (by norm_num) (by norm_num) k4_sourceNO
    (fun u => le_of_eq (k4_degree u)) Finset.univ (fun k => Finset.mem_univ _) hdel φ
  have hc : (Fintype.card (Fin 6) : ℚ) = 6 := by simp
  rw [hc] at h
  linarith

/-- **Non-vacuity of `DinurConstraintGraph`** (`04:133--159`).  The cited
constraint graph record is inhabited at **nondegenerate** legal values: a
binary alphabet `A = 2`, a genuine maximum degree `d = 3`, and a genuine
(non-perfect) `NO`-case rejected-constraint fraction `rho = 1/2`.

Degeneracy deliberately avoided: `A := 1`, `d := 0`, `rho := 1` also satisfies
every side condition, but it exercises none of the frozen arithmetic -- it
takes the `g(1) = 4` special arm instead of a generic one, has
`binom{A}{2} = 0`, and lets the frozen guard `max{1,d}` select the constant `1`
rather than `d`.  At `A = 2, d = 3` the special arm `g(2) = 2` is used with
`binom 2 2 = 1` nonzero, and the guard genuinely selects `d`. -/
def dinurWitness : DinurConstraintGraph where
  A := 2
  d := 3
  ρ := 1 / 2
  A_pos := by norm_num
  ρ_pos := by norm_num
  ρ_le_one := by norm_num

/-- The frozen `eps_B` formula pinned **end to end** at the witness: the whole
chain `g(2) = 2` (the special match arm, not `r - 2`) -> `binom 2 2 = 1` ->
`K_cl(2) = 2(2 + 2) + 4 * 4 = 24` -> the guard `max{1,3} = 3` ->
`eps_B = (1/2)/(2 * 24 * 3) = 1/288` is checked by the kernel.  A drift in any
link of that chain changes this value, so this single equation is the
statement pole for `Kcl`, `gWidth`, and the `max{1,d}` guard direction
simultaneously. -/
theorem dinurWitness_epsB : dinurWitness.epsB = 1 / 288 := by
  norm_num [DinurConstraintGraph.epsB, dinurWitness, Kcl, gWidth]

/-- The witness makes `epsB_pos` and `epsB_le_half` nonvacuous, and shows the
bound `1/2` of `epsB_le_half` is not attained here: `1/288 < 1/2` strictly, so
`epsB_le_half` is not a statement about a record whose only inhabitants sit at
the boundary. -/
theorem dinurWitness_epsB_lt_half : dinurWitness.epsB < 1 / 2 := by
  rw [dinurWitness_epsB]; norm_num

end EthInapproximability.ParameterizedNP.GuardedSourceGraph
