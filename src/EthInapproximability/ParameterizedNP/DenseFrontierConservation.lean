import EthInapproximability.ParameterizedNP.DenseWeightedCount

/-!
# Parameterized NP route: the seventh block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 980--1014** -- the
  frontier bookkeeping of `sec:dense-weighted-count` that the predecessor block
  deliberately left open: `eq:frontier-conservation`, Kraft's inequality, and the
  split count `S`.  The anchors traced here, in the order the frozen block prints
  them:
  * `08:981--989`, the frontier and its capacity weight, consumed **by pin** from
    the banked `DenseWeightedCount` (`PrefixFreeFrontier`, `stoppingCapacity`) and
    never restated: "The stopping nodes form a prefix-free frontier. ...  For a
    frontier node `v` at suffix depth `d_v`, put `kappa_v = 2^{r - d_v}`";
  * `08:990--992`, the two masses: "Let `h_v` be the number of ordinary components
    at `v`, counting the ordinary component of an unsplit witness, and let `z_v` be
    the number of unsplit bonus components.  Thus `0 <= z_v <= h_v`";
  * `08:992--993`, the split count: "If `S` witnesses split before reaching the
    frontier";
  * `eq:frontier-conservation` (`08:995--1002`), the four displayed lines
    `sum_v (h_v + z_v) = |H| + |W|`, `sum_v h_v = |H| + S`, `sum_v z_v = |W| - S`
    and `sum_v kappa_v <= q_2`, introduced at `08:993--994` as "conservation of
    components and Kraft's inequality give";
  * `08:1118`, the frozen reading "its third equality also gives `S <= |W|`";
  * `08:1004--1005`, the uniqueness clause "By the coordinatewise uniqueness in
    `lem:dense-routing`, an isolation node contains at most one routed object",
    carried here as a **named hypothesis** (see the interface list below).
  The component dynamics the conservation count is taken over are the frozen ones:
  `08:819--823` ("For each coordinate in `H`, place one *ordinary token* ...  For
  each coordinate in `W`, attach one additional *bonus token* to its ordinary
  token.  Until the pair is split, it is a single weight-two witness object") and
  `08:908--911` ("If both assigned children contain at least `L_{d+1}` quotient
  columns, split the witness and create one ordinary token in each child.
  Otherwise one child has at most `L_{d+1}-1` columns; route the whole witness to
  its complement").
* **Deliberately NOT claimed (the next block's territory).**
  `lem:abstract-weighted-frontier` (`08:1014--1089`) is the banked
  `EthInapproximability.ParameterizedNP.weightedFrontier` pilot and is neither
  restated nor applied here; `lem:dense-weighted-frontier` (`08:1091--1134`), which
  applies it, has no declaration below, and neither does the signed-excess estimate
  `sum_v (h_v + z_v - kappa_v) > 2b` that its second conversion needs.  Nothing
  below asserts the existence of a forced Alice node.  The closure lemmas of
  `sec:dense-alice-closure` (`08:1136--1324`) and `cor:exact-protected-stage4` are
  likewise untouched.
* **Predecessor anchors (the handoffs consumed by pin, never restated):**
  * the banked `EthInapproximability.ParameterizedNP.DenseWeightedCount`, which
    supplies `stoppingCapacity` (the frozen `kappa_v = 2^{r-d_v}`) with
    `one_le_stoppingCapacity`, `PrefixFreeFrontier` (the frozen `08:981`),
    `isolationNode_capacity_at_depth` (`eq:isolation-capacity`, `08:1004--1012`),
    the suffix-depth walk `descend`, the stop record `StoppedToken`, and
    `denseNoLeaf_depth_le` (the depth clause `d_v <= r` of `lem:dense-no-leaf`),
    which is what makes the Kraft exponent `r - d_v` the frozen one;
  * the banked `EthInapproximability.ParameterizedNP.DenseBranchSelection`, which
    supplies `Dtwo` (the frozen `D_2 = B_cap + log_2 q_2`) and, for the deficit
    corollary, `selectedGood` with `card_selectedGood` (`eq:selected-mass`,
    `08:736--741`, in the untruncated form `|H| + b = q_2`).
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design and appears in
  no hypothesis below.  The deep inputs of this block are named hypotheses at the
  exact gates the frozen text states them:
  * the coordinatewise uniqueness clause of `08:1004--1005` is `huniq`, a named
    hypothesis about the arrivals at the node, because the banked
    `DenseRoutingInvariant` recorded (its coverage limit 3) that it did not prove
    the routing preserves the one-object-per-coordinate representation across a
    query, and the banked `DenseWeightedCount` (its coverage limit 4) did not
    upgrade that bar either;
  * the **frontier-pair** clause of `08:934--935` -- "A routed object either
    chooses one child or splits into objects in two incomparable children, and
    protocol branches never merge" -- is `hpair`, the named hypothesis that a split
    witness's two ordinary tokens are counted at two *distinct* frontier nodes.  It
    is stated where it is spent (the uniqueness argument) and nowhere else: no
    conservation equality below uses it, and `FrontierArrival.split` carries **no**
    field demanding it, since demanding more of the constructor than the frozen
    bookkeeping needs would be an over-strong structure;
  * the depth clause `d_v <= r` enters either as the binder `hdepth` or, in the
    stopped-token form, through the banked `denseNoLeaf_depth_le` with its own two
    gated pairs; nothing here re-proves it;
  * `eq:selected-mass` in the form `q_2 <= |H| + b` (`08:1120`) is the binder
    `hselected`, discharged in the corollary by the banked `card_selectedGood`.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency graph.
* **New work.**  Kraft's inequality for the stopping frontier is proved outright,
  which the banked `DenseWeightedCount` explicitly recorded (its coverage limit 5)
  as **not** proved and not citable from there: `blocks`, `extensions`,
  `prefix_or_prefix` and `extensions_disjoint` are the counting device --
  a frontier node of suffix depth `d_v` owns the `2^{r-d_v}` length-`r` completions
  of its route, prefix-freeness makes those blocks disjoint, and there are `2^r`
  length-`r` words in all.  The conservation equalities are proved outright from the
  frozen component dynamics as a counting identity over `FrontierArrival`.
* Proof status: **new** for Kraft's inequality, the arrival bookkeeping, the three
  conservation equalities, the split-count bound and the deficit bound;
  **inherited by pin** for the capacity weight, prefix-freeness, the depth clause,
  `eq:isolation-capacity`, `D_2` and `eq:selected-mass`.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no unproved
  placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, the proof outline of
`thm:paper-protected-stage4`, **lines 265--266**: "Conservation gives
`sum_v(kappa_v - h_v) <= b`".

That single clause is claimed **once**, by `kraft_deficit_le` (the untruncated
natural-number form `sum_v kappa_v + S <= sum_v h_v + b`) together with its literal
real-valued restatement `kraft_deficit_le_real` and the pinned corollary
`kraft_deficit_le_at_selected_branch`; the three named ingredients it is assembled
from -- Kraft, the first conservation equality and `eq:selected-mass` -- are the
block's own results and pins.  No earlier tranche claimed it: the banked
`DenseWeightedCount` recorded that reader lines 259--265 are its own and that "the
reader sentences after line 265 ... are the next block's".  The remainder of that
sentence and everything after it -- "while the selected-branch inequality `w > 4b`
makes the total signed excess `sum_v(h_v+z_v-kappa_v) > 2b`", "If every Alice node
with positive excess had `4h_v < 3kappa_v` ...", "Thus some Alice node satisfies
..." (266--271) -- is **not** claimed here.  No reader prose is cited as a
statement: the clause above is an assertion, not a description of method.

## Candidate encodings of the frontier bookkeeping (`k = 2`, raced)

The novel object of this tranche is the per-coordinate *arrival*: what the frozen
component dynamics of `08:819--823` and `08:908--911` deliver to the frontier, and
which the four lines of `eq:frontier-conservation` count.

**Candidate A (landed, SS3--SS5).**  Make the novelty the *arrival of one
coordinate's routed object*: `FrontierArrival` has exactly the three outcomes the
frozen dynamics permit -- `ordinary v` (a coordinate of `H \ W`, whose single
ordinary token stops at `v`), `unsplit v` (a coordinate of `W` whose weight-two
witness object reaches `v` whole, contributing its ordinary component to `h_v`
*and* its bonus component to `z_v`, exactly as `08:990--992` counts them), and
`split v w` (a coordinate of `W` whose witness was split, "creat[ing] one ordinary
token in each child", so it contributes two ordinary components and no bonus).  The
masses `h_v`, `z_v`, the witness count `|W|` and the split count `S` are all
**derived** from an arrival function `arr : Coord -> FrontierArrival iota`; not one
of the four lines of `eq:frontier-conservation` is a field of anything, and the
Kraft line is proved from prefix-freeness rather than assumed.  12 conservation-side
aux lemmas proved, and the whole bundle is inhabited at a legal instance (SS7).

**Candidate B (rejected, SS6).**  Take the frontier bookkeeping as a record
carrying its own guarantees: `FrontierCounts` stores `route`, `cap`, `h`, `z`, the
three totals `H0`, `W0`, `S` and the frozen conclusions themselves -- the Kraft
bound and two conservation equalities -- as fields.  3 aux lemmas proved, and it
loses decisively on two counts.  First, it puts the frozen conclusions of
`eq:frontier-conservation` into constructor data, which the mechanical contract's
no-conclusion-in-constructor-data rule forbids outright, and which makes the
"theorem" a projection (`frontierCounts_conservation_is_projection` exhibits the
projection).  Second, it is unfaithful even as data: its `cap` field is unrelated to
the frozen `kappa_v = 2^{r-d_v}` of its own `route`, so
`frontierCounts_kraft_is_by_fiat` inhabits it with a **non**-prefix-free frontier
whose true capacities sum to twice the recorded width while the record's Kraft field
holds.  The race is decided on faithfulness, not length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the length-`r` word blocks, general (3): `mem_blocks`, `card_blocks`,
  `card_extensions`.
* `A2` the completion device, general (3): `prefix_of_mem_extensions`,
  `extensions_subset_blocks`, `extensions_disjoint`.
* `A3` the prefix comparison two routes with a common completion satisfy, general
  (1): `prefix_or_prefix`.
* `A4` Kraft (`08:1000`), general (2): `sum_stoppingCapacity_le_width`,
  `sum_stoppingCapacity_le_width_of_stoppedTokens`.
* `A5` the arrival contributions (`08:990--992`), general (4):
  `FrontierArrival.zContrib_le_hContrib`, `FrontierArrival.sum_hContrib`,
  `FrontierArrival.sum_zContrib`, `FrontierArrival.hContrib_le_one`.
* `A6` the mass and count readouts, general (5): `zMass_le_hMass`, `card_splits`,
  `card_unsplitWitnesses`, `card_witnesses`, `card_unsplitWitnesses_add_card_splits`.
* `A7` `eq:frontier-conservation` (`08:995--1002`) and `08:1118`, general (6):
  `sum_hMass_eq`, `sum_zMass_eq_card_unsplitWitnesses`,
  `sum_zMass_add_splitCount_eq`, `sum_zMass_eq_sub`, `sum_hMass_add_zMass_eq`,
  `splitCount_le_witnessCount` (with `splits_subset_witnesses` as its set form).
* `A8` the uniqueness clause (`08:1004--1005`), general (2):
  `hMass_le_one_of_uniqueness`, `isolationNode_capacity_of_uniqueness`.
* `A9` the deficit bound (reader 265--266), general (3): `kraft_deficit_le`,
  `kraft_deficit_le_real`, `kraft_deficit_le_at_selected_branch`.
* Candidate B's own battery (3): `frontierCounts_nonempty`,
  `frontierCounts_conservation_is_projection`, `frontierCounts_kraft_is_by_fiat`.

That is **30 battery entries proved plus 3 for the rejected candidate**, with `0`
unproved, alongside **two statement poles** (`kraft_pole_needs_prefix_free`,
`hMass_pole_needs_distinct_split_targets`) and **four non-vacuity / consistency
readouts** (`kraft_tight_symbolic`, `frontierArrival_nondegenerate`,
`frontierConservation_legal_instance`, `isolation_capacity_hypotheses_consistent`),
plus `probeFrontierRoute_prefixFree`, the prefix-freeness of the tier-2 frontier.

The module has **59** source declarations in all: 17 definitions (`blocks`,
`extensions`, `FrontierArrival.isWitness`, `FrontierArrival.isSplit`,
`FrontierArrival.isUnsplitWitness`, `FrontierArrival.hContrib`,
`FrontierArrival.zContrib`, `hMass`, `zMass`, `witnesses`, `splits`,
`unsplitWitnesses`, `witnessCount`, `splitCount`, `arrivalsAt`,
`probeFrontierRoute`, `probeArrival`), 2 types (`FrontierArrival`,
`FrontierCounts`) and 40 proved results.

`sum_stoppingCapacity_le_width_of_stoppedTokens` is the one result whose premise
bundle is not instantiated here: it passes the banked `denseNoLeaf_depth_le`
hypotheses through unchanged, and their joint consistency at legal values is the
banked `DenseWeightedCount.denseNoLeaf_hypotheses_consistent`, which exhibits
exactly that bundle with both gated hypotheses firing tightly.  Nothing is added to
it, so nothing here can make it vacuous that was not already checked there.

## Three-tier witness legality

Every witness below is labelled with the tier of legality it actually carries, and
no witness is read as more than its tier permits.

* **Tier 1 -- symbolic in the frozen parameters.**  `kraft_tight_symbolic` is
  quantified over every `r`: the full depth-`r` frontier is prefix-free, sits at
  depths `<= r`, and attains `sum_v kappa_v = 2^r` exactly.  Nothing is evaluated,
  so the frozen widths `q_2 = 2^r >= 6144` forced by `eq:stage2-structural-gates`
  (`06:832--847`) are reached, and Kraft is recorded **tight**, hence not
  strengthenable.  Every counting result of SS1--SS5 is itself tier 1: each is
  general in `r`, in the carrier types and in the arrival function, and takes no
  schedule hypothesis whatever.
* **Tier 2 -- a fully instantiated legal instance of the block's regime.**
  `frontierConservation_legal_instance` exhibits the entire bundle at `r = 3`
  (`q_2 = 8`), `b = 1`, `w = 5`, `|H| = 7`, `|W| = 4`, `S = 1`, where the frozen
  side conditions the conservation lines are converted against all hold on the face
  of the statement -- `|H| <= q_2` (the frozen `H = [q_2] \ B`), `q_2 <= |H| + b`
  and `w <= |W| + b` (`eq:selected-mass` as `08:1120--1123` reads it) and `4b < w`
  (`lem:dense-select-branch`, `08:723--726`) -- and where Kraft **and** the deficit
  bound are both attained with equality.  This is the hypothesis-consistency
  readout: the whole premise bundle of the block is simultaneously satisfiable at
  values the frozen text permits, so no result below is vacuous.  The instance is
  **not** a schedule instance: it does not satisfy the full
  `eq:stage2-structural-gates`, which forces `q_2 >= 6144`, and no parameter value
  may be read out of it.  It does not need to: every statement it instantiates is
  tier 1.
* **Tier 3 -- separating probes at deliberately small carriers.**
  `kraft_pole_needs_prefix_free`, `hMass_pole_needs_distinct_split_targets`,
  `isolation_capacity_hypotheses_consistent`, `frontierArrival_nondegenerate` and
  Candidate B's three readouts are probes of one named hypothesis or one definition
  at a minimal carrier.  They are neither schedule instances nor legal instances of
  the block's regime, and are cited only for what they separate.

## Honest scope and recorded coverage limits

1. **The routing is not constructed, and no protocol is evaluated.**  The arrival
   function `arr` is *given*: this block does not prove that the frozen routing of
   `lem:dense-routing` delivers each coordinate to a frontier node, nor which one.
   What is proved is that **whatever** the routing does, if each coordinate's object
   arrives in one of the three frozen ways then the four lines of
   `eq:frontier-conservation` are exactly the resulting counts.  A later tranche may
   not cite this module as having built the routing map.
2. **The uniqueness clause and the frontier-pair clause stay hypotheses.**
   `08:1004--1005` is `huniq` and `08:934--935` is `hpair`, for the reason recorded
   in the interface list; `isolationNode_capacity_of_uniqueness` is the only
   declaration that consumes either, and it discharges the frozen
   `eq:isolation-capacity` through the banked `isolationNode_capacity_at_depth`
   rather than re-proving it.
3. **Kraft is proved for the frontier's routes, not for an abstract weight
   family.**  `sum_stoppingCapacity_le_width` is about `stoppingCapacity r
   (route v).length` with `route` prefix-free and its depths bounded by `r`; it says
   nothing about an arbitrary family of numbers `kappa_v`, and it is the depth bound
   -- supplied by the banked `denseNoLeaf_depth_le` in the stopped-token form -- that
   makes the exponent the frozen `r - d_v` rather than a truncation artefact.
4. **The deficit bound is arithmetic over three named inputs.**  `kraft_deficit_le`
   assembles Kraft, `sum_hMass_eq` and the binder `hselected`; it is stated
   additively (`sum kappa + S <= sum h + b`) precisely because the frozen proof
   takes the same care at `08:1124--1127` ("Thus neither conversion relies on
   truncated subtraction").  The real-valued restatement is the reader's literal
   sentence and adds no mathematics.
5. **The signed-excess estimate is absent.**  The second conversion of `08:1118--1127`
   (`w <= |W| + b`) and the excess bound the reader states after line 266 are **not**
   proved here and must not be cited from here.
6. **`r`, `b`, the counts and the carriers are binders, not values.**  No parameter
   schedule may be read out of any witness below; the tier labelling above is
   binding on consumers.
7. **Candidate B is race evidence with a recorded disposition.**  `FrontierCounts`
   is consumed by nothing and may not be used to re-encode the frontier bookkeeping
   of `08:990--1002` without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseFrontierConservation

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseBranchSelection
open EthInapproximability.ParameterizedNP.DenseWeightedCount

/-! ## §1  Kraft's inequality for the stopping frontier (`08:993--1000`)

"The stopping nodes form a prefix-free frontier" (`08:981`); "conservation of
components and Kraft's inequality give ... `sum_v kappa_v <= q_2`"
(`08:993--1000`), at the frozen width `q_2 = 2^r`.

The device is the standard one: a frontier node at suffix depth `d_v` owns the
`2^{r - d_v} = kappa_v` binary words of length `r` extending its route, the
prefix-free condition makes those blocks pairwise disjoint, and there are `2^r`
words of length `r` in all. -/

/-- The binary words of length `n`. -/
def blocks (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)

/-- **Aux 1.**  Membership in `blocks n` is exactly having length `n`.  General. -/
theorem mem_blocks {n : ℕ} {w : List Bool} : w ∈ blocks n ↔ w.length = n := by
  constructor
  · intro hw
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hw
    simp
  · intro hw
    subst hw
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

/-- **Aux 2.**  There are `2^n` words of length `n` -- the frozen width `q_2 = 2^r`
at `n = r`.  General. -/
theorem card_blocks (n : ℕ) : (blocks n).card = 2 ^ n := by
  rw [blocks, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- The length-`r` completions of a frontier node's route. -/
def extensions (r : ℕ) (p : List Bool) : Finset (List Bool) :=
  (blocks (r - p.length)).image (fun s => p ++ s)

/-- **Aux 3 (the frozen capacity, counted).**  A route of length `d` owns exactly
`2^{r-d} = kappa_v` completions.  General. -/
theorem card_extensions (r : ℕ) (p : List Bool) :
    (extensions r p).card = 2 ^ (r - p.length) := by
  rw [extensions,
    Finset.card_image_of_injective _ (fun s t h => List.append_cancel_left h), card_blocks]

/-- **Aux 4.**  A completion extends the route it completes.  General. -/
theorem prefix_of_mem_extensions {r : ℕ} {p w : List Bool} (h : w ∈ extensions r p) :
    p <+: w := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp h
  exact ⟨s, rfl⟩

/-- **Aux 5.**  A route at suffix depth at most `r` has all its completions among the
length-`r` words.  General; the depth bound is the frozen `d_v <= r`. -/
theorem extensions_subset_blocks {r : ℕ} {p : List Bool} (hp : p.length ≤ r) :
    extensions r p ⊆ blocks r := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
  rw [mem_blocks] at hs ⊢
  rw [List.length_append, hs]
  omega

/-- **Aux 6.**  Two routes with a common completion are comparable: one is a prefix
of the other.  General, and this is the only place prefix-freeness bites. -/
theorem prefix_or_prefix : ∀ {p q w : List Bool}, p <+: w → q <+: w → p <+: q ∨ q <+: p := by
  intro p
  induction p with
  | nil => intro q w _ _; exact Or.inl List.nil_prefix
  | cons a p ih =>
      intro q w hp hq
      cases q with
      | nil => exact Or.inr List.nil_prefix
      | cons b q =>
          obtain ⟨t, rfl⟩ := hp
          obtain ⟨u, hu⟩ := hq
          rw [List.cons_append, List.cons_append, List.cons.injEq] at hu
          obtain ⟨hab, hqu⟩ := hu
          subst hab
          rcases ih (q := q) (w := p ++ t) ⟨t, rfl⟩ ⟨u, hqu⟩ with h | h
          · obtain ⟨s, rfl⟩ := h
            exact Or.inl ⟨s, by simp⟩
          · obtain ⟨s, rfl⟩ := h
            exact Or.inr ⟨s, by simp⟩

/-- **Aux 7 (`08:981`, prefix-freeness spent).**  Incomparable routes own disjoint
blocks of completions.  General. -/
theorem extensions_disjoint {r : ℕ} {p q : List Bool}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    Disjoint (extensions r p) (extensions r q) := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  rcases prefix_or_prefix (prefix_of_mem_extensions hw) (prefix_of_mem_extensions hw') with h | h
  · exact hpq h
  · exact hqp h

/-- **Kraft's inequality, the fourth line of `eq:frontier-conservation`
(`08:1000`).**  For a prefix-free frontier all of whose suffix depths are at most
`r`, the residual capacities sum to at most the frozen width `q_2 = 2^r`:
`sum_v kappa_v <= q_2`.

`PrefixFreeFrontier` and `stoppingCapacity` are the banked `DenseWeightedCount`
definitions, consumed by pin.  The depth hypothesis is the frozen `d_v <= r` of
`lem:dense-no-leaf`; `sum_stoppingCapacity_le_width_of_stoppedTokens` supplies it
from the banked lemma itself.  General in the frontier index type, the routes and
`r`.

*Why the hypothesis is load-bearing.*  Without prefix-freeness the bound is false:
`kraft_pole_needs_prefix_free` exhibits a two-node frontier at depths at most `r`
whose capacities sum to `3/2` times the width. -/
theorem sum_stoppingCapacity_le_width {ι : Type*} [Fintype ι] {r : ℕ}
    (route : ι → List Bool) (hpf : PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r) :
    ∑ v, stoppingCapacity r (route v).length ≤ 2 ^ r := by
  classical
  have hdisj : ∀ v ∈ (Finset.univ : Finset ι), ∀ w ∈ (Finset.univ : Finset ι), v ≠ w →
      Disjoint (extensions r (route v)) (extensions r (route w)) := by
    intro v _ w _ hvw
    exact extensions_disjoint (hpf v w hvw) (hpf w v (Ne.symm hvw))
  have hcard := Finset.card_biUnion hdisj
  have hsub : (Finset.univ.biUnion (fun v => extensions r (route v))) ⊆ blocks r := by
    intro w hw
    obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.mp hw
    exact extensions_subset_blocks (hdepth v) hv
  have hle := Finset.card_le_card hsub
  rw [hcard, card_blocks] at hle
  simpa [stoppingCapacity, card_extensions] using hle

/-- **Kraft at the frozen stopping frontier.**  The same bound with the depth clause
supplied by the banked `denseNoLeaf_depth_le` rather than assumed: a family of
stopped positive tokens whose routes are prefix-free has
`sum_v kappa_v <= q_2 = 2^r`.

`hbudget` is `eq:selected-upper-budget` at the banked `Dtwo = B_cap + log_2 q_2`
with the frozen `q_2 = 2^r`, and the two gated hypotheses are the frozen depth-`r+1`
pair of `08:974--978`, passed through unchanged.  General. -/
theorem sum_stoppingCapacity_le_width_of_stoppedTokens
    {X Y Z Coord ι : Type*} [Fintype ι]
    {A B : List Bool → Type*} [∀ p, Fintype (A p)] [∀ p, Fintype (B p)]
    {Pstar : Protocol X Y Z} (g : ∀ p : List Bool, A p → B p → Bool)
    (t : ι → StoppedToken Pstar Coord) {r bcap : ℕ}
    (hpf : PrefixFreeFrontier (fun v => (t v).route))
    (hbudget : Pstar.cost ≤ Dtwo bcap r)
    (hdeepHard : ∀ v, r + 1 ≤ (t v).route.length → bcap ≤ D (g ((t v).route.take (r + 1))))
    (hdeepResidual : ∀ v, r + 1 ≤ (t v).route.length →
      D (g ((t v).route.take (r + 1))) ≤ (descend Pstar ((t v).route.take (r + 1))).cost) :
    ∑ v, stoppingCapacity r ((t v).route.length) ≤ 2 ^ r :=
  sum_stoppingCapacity_le_width (fun v => (t v).route) hpf
    (fun v => denseNoLeaf_depth_le g (t v) hbudget (hdeepHard v) (hdeepResidual v))

/-! ## §2  What arrives at a frontier node (`08:819--823`, `08:908--911`, `08:990--992`)

The frozen bookkeeping places "one *ordinary token*" at each coordinate of `H` and
attaches "one additional *bonus token*" at each coordinate of `W`, the pair being "a
single weight-two witness object" until it is split; a split "create[s] one ordinary
token in each child".  So a coordinate's routed object reaches the frontier in
exactly one of three ways, and `h_v` "counts the ordinary component of an unsplit
witness" while `z_v` counts "unsplit bonus components". -/

/-- The three frozen outcomes for one coordinate's routed object: an ordinary token
of `H \ W` stopping at `v`; a witness object of `W` reaching `v` unsplit (weight two:
one ordinary component and one bonus component); or a witness of `W` split before the
frontier into one ordinary token at `v` and one at `w` (`08:908--911`).

The frozen "two incomparable children" of `08:934--935` is deliberately **not** a
field: no conservation equality needs it, and it is carried as the named hypothesis
`hpair` exactly where the uniqueness argument spends it. -/
inductive FrontierArrival (ι : Type*)
  | ordinary (v : ι)
  | unsplit (v : ι)
  | split (v w : ι)

namespace FrontierArrival

variable {ι : Type*}

/-- The coordinate carried a witness object, split or not: membership in `W`. -/
def isWitness : FrontierArrival ι → Bool
  | ordinary _ => false
  | unsplit _ => true
  | split _ _ => true

/-- The witness was split before reaching the frontier (`08:992--993`, the `S` of
`eq:frontier-conservation`). -/
def isSplit : FrontierArrival ι → Bool
  | ordinary _ => false
  | unsplit _ => false
  | split _ _ => true

/-- The witness reached the frontier whole, so its bonus component is unsplit
(`08:991--992`). -/
def isUnsplitWitness : FrontierArrival ι → Bool
  | ordinary _ => false
  | unsplit _ => true
  | split _ _ => false

/-- The contribution of one arrival to `h_v`, "the number of ordinary components at
`v`, counting the ordinary component of an unsplit witness" (`08:990--991`); a split
witness contributes its two created ordinary tokens (`08:909--910`). -/
def hContrib [DecidableEq ι] : FrontierArrival ι → ι → ℕ
  | ordinary v, u => if v = u then 1 else 0
  | unsplit v, u => if v = u then 1 else 0
  | split v w, u => (if v = u then 1 else 0) + (if w = u then 1 else 0)

/-- The contribution of one arrival to `z_v`, "the number of unsplit bonus
components" (`08:991--992`). -/
def zContrib [DecidableEq ι] : FrontierArrival ι → ι → ℕ
  | ordinary _, _ => 0
  | unsplit v, u => if v = u then 1 else 0
  | split _ _, _ => 0

variable [DecidableEq ι]

/-- **Aux 8 (`08:992`, "Thus `0 <= z_v <= h_v`"), pointwise.**  General. -/
theorem zContrib_le_hContrib (a : FrontierArrival ι) (u : ι) :
    a.zContrib u ≤ a.hContrib u := by
  cases a <;> simp [zContrib, hContrib]

/-- **Aux 9.**  Each arrival contributes one ordinary component, or two if its
witness was split.  General; this is the arithmetic behind `sum_v h_v = |H| + S`. -/
theorem sum_hContrib [Fintype ι] (a : FrontierArrival ι) :
    ∑ u, a.hContrib u = 1 + (if a.isSplit = true then 1 else 0) := by
  cases a with
  | ordinary v => simp [hContrib, isSplit]
  | unsplit v => simp [hContrib, isSplit]
  | split v w => simp [hContrib, isSplit, Finset.sum_add_distrib]

/-- **Aux 10.**  Each arrival contributes one unsplit bonus component if and only if
it is an unsplit witness.  General; this is the arithmetic behind
`sum_v z_v = |W| - S`. -/
theorem sum_zContrib [Fintype ι] (a : FrontierArrival ι) :
    ∑ u, a.zContrib u = (if a.isUnsplitWitness = true then 1 else 0) := by
  cases a with
  | ordinary v => simp [zContrib, isUnsplitWitness]
  | unsplit v => simp [zContrib, isUnsplitWitness]
  | split v w => simp [zContrib, isUnsplitWitness]

/-- **Aux 11 (`08:934--935` spent).**  If a split witness's two ordinary tokens are
created in two *distinct* children -- the frozen "objects in two incomparable
children", carried as the named hypothesis -- then one arrival contributes at most
one ordinary component to any single frontier node.  General.

Without the hypothesis this is false, which `hMass_pole_needs_distinct_split_targets`
exhibits. -/
theorem hContrib_le_one {a : FrontierArrival ι} {u : ι}
    (hpair : ∀ v w : ι, a = split v w → v ≠ w) : a.hContrib u ≤ 1 := by
  cases a with
  | ordinary v => simp only [hContrib]; split <;> simp
  | unsplit v => simp only [hContrib]; split <;> simp
  | split v w =>
      have hne : v ≠ w := hpair v w rfl
      simp only [hContrib]
      by_cases hv : v = u
      · by_cases hw : w = u
        · exact absurd (hv.trans hw.symm) hne
        · simp [hv, hw]
      · by_cases hw : w = u <;> simp [hv, hw]

end FrontierArrival

/-! ## §3  The masses, the counts and `eq:frontier-conservation` (`08:990--1002`)

`H` is the good-coordinate carrier: "For each coordinate in `H`, place one ordinary
token" (`08:819`), so one arrival per coordinate and `|H| = Fintype.card Coord`.
`W` is the set of coordinates carrying a witness object, `S` the number of those
split before the frontier. -/

section Masses

variable {ι Coord : Type*} [DecidableEq ι] [Fintype Coord]

/-- `h_v`, "the number of ordinary components at `v`, counting the ordinary component
of an unsplit witness" (`08:990--991`). -/
def hMass (arr : Coord → FrontierArrival ι) (u : ι) : ℕ := ∑ α, (arr α).hContrib u

/-- `z_v`, "the number of unsplit bonus components" (`08:991--992`). -/
def zMass (arr : Coord → FrontierArrival ι) (u : ι) : ℕ := ∑ α, (arr α).zContrib u

/-- `W`, the coordinates carrying a witness object (`08:820--823`). -/
def witnesses (arr : Coord → FrontierArrival ι) : Finset Coord :=
  Finset.univ.filter (fun α => (arr α).isWitness = true)

/-- The witnesses split before reaching the frontier (`08:992--993`). -/
def splits (arr : Coord → FrontierArrival ι) : Finset Coord :=
  Finset.univ.filter (fun α => (arr α).isSplit = true)

/-- The witnesses that reach the frontier whole. -/
def unsplitWitnesses (arr : Coord → FrontierArrival ι) : Finset Coord :=
  Finset.univ.filter (fun α => (arr α).isUnsplitWitness = true)

/-- `|W|`, the frozen `W_0` of `lem:abstract-weighted-frontier` (`08:1112`). -/
def witnessCount (arr : Coord → FrontierArrival ι) : ℕ := (witnesses arr).card

/-- `S`, the split count of `08:992--993`. -/
def splitCount (arr : Coord → FrontierArrival ι) : ℕ := (splits arr).card

/-- **`08:992`, "Thus `0 <= z_v <= h_v`".**  General. -/
theorem zMass_le_hMass (arr : Coord → FrontierArrival ι) (u : ι) :
    zMass arr u ≤ hMass arr u :=
  Finset.sum_le_sum (fun α _ => FrontierArrival.zContrib_le_hContrib (arr α) u)

omit [DecidableEq ι] in
/-- **Aux 12.**  `S` as an indicator sum.  General. -/
theorem card_splits (arr : Coord → FrontierArrival ι) :
    splitCount arr = ∑ α : Coord, (if (arr α).isSplit = true then 1 else 0) := by
  rw [splitCount, splits, Finset.card_filter]

omit [DecidableEq ι] in
/-- **Aux 13.**  `|W| - S` as an indicator sum.  General. -/
theorem card_unsplitWitnesses (arr : Coord → FrontierArrival ι) :
    (unsplitWitnesses arr).card
      = ∑ α : Coord, (if (arr α).isUnsplitWitness = true then 1 else 0) := by
  rw [unsplitWitnesses, Finset.card_filter]

omit [DecidableEq ι] in
/-- **Aux 14.**  `|W|` as an indicator sum.  General. -/
theorem card_witnesses (arr : Coord → FrontierArrival ι) :
    witnessCount arr = ∑ α : Coord, (if (arr α).isWitness = true then 1 else 0) := by
  rw [witnessCount, witnesses, Finset.card_filter]

omit [DecidableEq ι] in
/-- **Aux 15 (conservation of witnesses).**  Every witness is either split before the
frontier or unsplit at it, and never both.  General. -/
theorem card_unsplitWitnesses_add_card_splits (arr : Coord → FrontierArrival ι) :
    (unsplitWitnesses arr).card + splitCount arr = witnessCount arr := by
  rw [card_unsplitWitnesses, card_splits, card_witnesses, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  cases arr α <;>
    simp [FrontierArrival.isUnsplitWitness, FrontierArrival.isSplit, FrontierArrival.isWitness]

/-- **`eq:frontier-conservation`, second line (`08:998`).**  `sum_v h_v = |H| + S`:
every coordinate contributes one ordinary component, and each of the `S` split
witnesses contributes a second.  General. -/
theorem sum_hMass_eq [Fintype ι] (arr : Coord → FrontierArrival ι) :
    ∑ u, hMass arr u = Fintype.card Coord + splitCount arr := by
  have h : ∑ u, hMass arr u = ∑ α : Coord, ∑ u, (arr α).hContrib u := Finset.sum_comm
  have h2 : ∀ α ∈ (Finset.univ : Finset Coord), ∑ u, (arr α).hContrib u
      = 1 + (if (arr α).isSplit = true then 1 else 0) :=
    fun α _ => FrontierArrival.sum_hContrib (arr α)
  rw [h, Finset.sum_congr rfl h2, Finset.sum_add_distrib, card_splits]
  congr 1
  simp

/-- **Aux 16.**  `sum_v z_v` counts the unsplit witnesses.  General. -/
theorem sum_zMass_eq_card_unsplitWitnesses [Fintype ι] (arr : Coord → FrontierArrival ι) :
    ∑ u, zMass arr u = (unsplitWitnesses arr).card := by
  have h : ∑ u, zMass arr u = ∑ α : Coord, ∑ u, (arr α).zContrib u := Finset.sum_comm
  have h2 : ∀ α ∈ (Finset.univ : Finset Coord), ∑ u, (arr α).zContrib u
      = (if (arr α).isUnsplitWitness = true then 1 else 0) :=
    fun α _ => FrontierArrival.sum_zContrib (arr α)
  rw [h, Finset.sum_congr rfl h2, card_unsplitWitnesses]

omit [DecidableEq ι] in
/-- **Aux 17.**  Every split witness is a witness.  General. -/
theorem splits_subset_witnesses (arr : Coord → FrontierArrival ι) :
    splits arr ⊆ witnesses arr := by
  intro α hα
  simp only [splits, Finset.mem_filter] at hα
  simp only [witnesses, Finset.mem_filter]
  refine ⟨hα.1, ?_⟩
  cases h : arr α <;> rw [h] at hα <;>
    simp [FrontierArrival.isSplit, FrontierArrival.isWitness] at hα ⊢

omit [DecidableEq ι] in
/-- **`08:1118`, "its third equality also gives `S <= |W|`".**  General. -/
theorem splitCount_le_witnessCount (arr : Coord → FrontierArrival ι) :
    splitCount arr ≤ witnessCount arr :=
  Finset.card_le_card (splits_subset_witnesses arr)

/-- **`eq:frontier-conservation`, third line (`08:999`), in the untruncated form the
frozen proof converts it to at `08:1030`.**  `sum_v z_v + S = |W|`.  General. -/
theorem sum_zMass_add_splitCount_eq [Fintype ι] (arr : Coord → FrontierArrival ι) :
    ∑ u, zMass arr u + splitCount arr = witnessCount arr := by
  rw [sum_zMass_eq_card_unsplitWitnesses, card_unsplitWitnesses_add_card_splits]

/-- **`eq:frontier-conservation`, third line as the frozen text prints it
(`08:999`).**  `sum_v z_v = |W| - S`, with the natural subtraction justified by
`splitCount_le_witnessCount`.  General. -/
theorem sum_zMass_eq_sub [Fintype ι] (arr : Coord → FrontierArrival ι) :
    ∑ u, zMass arr u = witnessCount arr - splitCount arr := by
  have h := sum_zMass_add_splitCount_eq arr
  omega

/-- **`eq:frontier-conservation`, first line (`08:997`).**  `sum_v (h_v + z_v) =
|H| + |W|`: the total unit weight on the frontier is one per good coordinate plus one
per witness, and the split count cancels.  General. -/
theorem sum_hMass_add_zMass_eq [Fintype ι] (arr : Coord → FrontierArrival ι) :
    ∑ u, (hMass arr u + zMass arr u) = Fintype.card Coord + witnessCount arr := by
  rw [Finset.sum_add_distrib, sum_hMass_eq]
  have h := sum_zMass_add_splitCount_eq arr
  omega

/-! ## §4  The uniqueness clause and `eq:isolation-capacity` (`08:1004--1005`)

"By the coordinatewise uniqueness in `lem:dense-routing`, an isolation node contains
at most one routed object."  The clause is a **named hypothesis** here, for the
reason recorded in coverage limit 2; what this section adds is the passage from it to
the banked `isolationNode_capacity_at_depth`, which is where the two capacity
requirements of `08:1005--1007` are spent. -/

/-- The coordinates whose routed object is counted at the frontier node `u`. -/
def arrivalsAt (arr : Coord → FrontierArrival ι) (u : ι) : Finset Coord :=
  Finset.univ.filter (fun α => 0 < (arr α).hContrib u)

/-- **`08:1004--1005`, the uniqueness clause converted to a mass bound.**  At a node
holding at most one routed object, and with a split witness's two ordinary tokens
counted at two distinct nodes, the ordinary mass is at most one.

`huniq` is the frozen coordinatewise uniqueness and `hpair` the frozen
"two incomparable children"; both are named hypotheses, never derived here.
General. -/
theorem hMass_le_one_of_uniqueness (arr : Coord → FrontierArrival ι) (u : ι)
    (huniq : (arrivalsAt arr u).card ≤ 1)
    (hpair : ∀ (α : Coord) (v w : ι), arr α = FrontierArrival.split v w → v ≠ w) :
    hMass arr u ≤ 1 := by
  have hzero : ∀ α ∈ (Finset.univ : Finset Coord), α ∉ arrivalsAt arr u →
      (arr α).hContrib u = 0 := by
    intro α _ hα
    simp only [arrivalsAt, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
      Nat.le_zero] at hα
    exact hα
  have hsum : ∑ α ∈ arrivalsAt arr u, (arr α).hContrib u = hMass arr u :=
    Finset.sum_subset (Finset.filter_subset _ _) hzero
  have hle : ∑ α ∈ arrivalsAt arr u, (arr α).hContrib u
      ≤ ∑ _α ∈ arrivalsAt arr u, 1 :=
    Finset.sum_le_sum (fun α _ => FrontierArrival.hContrib_le_one (hpair α))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hle
  omega

/-- **`eq:isolation-capacity` (`08:1008--1012`) at the counted masses.**  At an
isolation node -- one routed object, by the named `huniq` -- the routed masses fit in
the residual capacity `kappa_v = 2^{r-d_v}`.

The capacity requirements are the banked `isolationNode_capacity_at_depth`: the
frozen `kappa_v >= 1` holds outright, and `htwo` is the frozen "one unsplit witness,
whose `B_cap + 1` certificate requires `kappa_v >= 2`".  General. -/
theorem isolationNode_capacity_of_uniqueness {r d : ℕ} (arr : Coord → FrontierArrival ι) (u : ι)
    (huniq : (arrivalsAt arr u).card ≤ 1)
    (hpair : ∀ (α : Coord) (v w : ι), arr α = FrontierArrival.split v w → v ≠ w)
    (htwo : 0 < zMass arr u → 2 ≤ stoppingCapacity r d) :
    hMass arr u + zMass arr u ≤ stoppingCapacity r d :=
  isolationNode_capacity_at_depth (hMass_le_one_of_uniqueness arr u huniq hpair)
    (zMass_le_hMass arr u) htwo

/-! ## §5  The deficit bound (reader 265--266)

"Conservation gives `sum_v(kappa_v - h_v) <= b`."  Three named inputs: Kraft
(`08:1000`), the first conservation equality (`08:998`) and `eq:selected-mass` in the
form `q_2 <= |H| + b` that `08:1120` converts it to. -/

/-- **The deficit bound, untruncated.**  `sum_v kappa_v + S <= sum_v h_v + b`.

Stated additively because the frozen proof takes exactly this care at
`08:1124--1127` ("Thus neither conversion relies on truncated subtraction").
`hselected` is `eq:selected-mass` at `08:1120`, a binder here and discharged by the
banked `card_selectedGood` in `kraft_deficit_le_at_selected_branch`.  General. -/
theorem kraft_deficit_le [Fintype ι] {r b : ℕ}
    (arr : Coord → FrontierArrival ι) (route : ι → List Bool)
    (hpf : PrefixFreeFrontier route) (hdepth : ∀ v, (route v).length ≤ r)
    (hselected : 2 ^ r ≤ Fintype.card Coord + b) :
    (∑ v, stoppingCapacity r (route v).length) + splitCount arr
      ≤ (∑ v, hMass arr v) + b := by
  have hk := sum_stoppingCapacity_le_width route hpf hdepth
  have hc := sum_hMass_eq arr
  omega

/-- **The reader's literal sentence (265--266).**  `sum_v (kappa_v - h_v) <= b` over
the reals, which is the deficit bound above with the split count discarded.  No new
mathematics: it is `kraft_deficit_le` cast.  General. -/
theorem kraft_deficit_le_real [Fintype ι] {r b : ℕ}
    (arr : Coord → FrontierArrival ι) (route : ι → List Bool)
    (hpf : PrefixFreeFrontier route) (hdepth : ∀ v, (route v).length ≤ r)
    (hselected : 2 ^ r ≤ Fintype.card Coord + b) :
    ∑ v, ((stoppingCapacity r (route v).length : ℝ) - (hMass arr v : ℝ)) ≤ (b : ℝ) := by
  have h := kraft_deficit_le arr route hpf hdepth hselected
  have hcast : (((∑ v, stoppingCapacity r (route v).length) + splitCount arr : ℕ) : ℝ)
      ≤ (((∑ v, hMass arr v) + b : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  rw [Finset.sum_sub_distrib]
  have hS : (0 : ℝ) ≤ (splitCount arr : ℝ) := Nat.cast_nonneg _
  linarith

end Masses

/-- **The deficit bound at the banked selected branch.**  With the good-coordinate
carrier taken to be the banked `selectedGood B = [q_2] \ B` and `b = |B|`, the
hypothesis `hselected` is discharged by the banked `card_selectedGood`
(`eq:selected-mass`, in its untruncated form `|H| + b = q_2`); `hwidth` is the frozen
`q_2 = 2^r` of `08:949` at the banked convention `q_2 = |Coord|`
(`DenseBranchSelection`, its coverage limit 2).  General. -/
theorem kraft_deficit_le_at_selected_branch {ι Coord : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Coord] [DecidableEq Coord] {r : ℕ} (B : Finset Coord)
    (arr : {α // α ∈ selectedGood B} → FrontierArrival ι) (route : ι → List Bool)
    (hpf : PrefixFreeFrontier route) (hdepth : ∀ v, (route v).length ≤ r)
    (hwidth : 2 ^ r = Fintype.card Coord) :
    (∑ v, stoppingCapacity r (route v).length) + splitCount arr
      ≤ (∑ v, hMass arr v) + B.card := by
  refine kraft_deficit_le arr route hpf hdepth ?_
  have hcoe : Fintype.card {α // α ∈ selectedGood B} = (selectedGood B).card :=
    Fintype.card_coe _
  have hsel := card_selectedGood B
  omega

/-! ## §6  Candidate B (rejected): the bookkeeping as a record of its own guarantees

Recorded as race evidence with the disposition of coverage limit 7. -/

/-- **Candidate B.**  The frontier bookkeeping as a record carrying the frozen
conclusions as fields.  Rejected: the Kraft bound and two conservation equalities are
constructor data, so the frozen results become projections, and `cap` is unrelated to
the frozen `kappa_v = 2^{r-d_v}` of the record's own `route`. -/
structure FrontierCounts (ι : Type*) [Fintype ι] where
  /-- The routes of the frontier nodes. -/
  route : ι → List Bool
  /-- The alleged capacities. -/
  cap : ι → ℕ
  /-- The alleged ordinary masses. -/
  h : ι → ℕ
  /-- The alleged bonus masses. -/
  z : ι → ℕ
  /-- The alleged width. -/
  width : ℕ
  /-- The alleged `|H|`. -/
  H0 : ℕ
  /-- The alleged `|W|`. -/
  W0 : ℕ
  /-- The alleged split count. -/
  S : ℕ
  /-- Kraft's inequality, stored rather than proved. -/
  kraft : ∑ v, cap v ≤ width
  /-- The second conservation equality, stored rather than proved. -/
  conservation_h : ∑ v, h v = H0 + S
  /-- The third conservation equality, stored rather than proved. -/
  conservation_z : ∑ v, z v + S = W0

/-- **Candidate-B battery 1.**  The record is inhabited, degenerately. -/
theorem frontierCounts_nonempty : Nonempty (FrontierCounts (Fin 1)) :=
  ⟨{ route := fun _ => [], cap := fun _ => 0, h := fun _ => 0, z := fun _ => 0,
     width := 0, H0 := 0, W0 := 0, S := 0,
     kraft := by simp, conservation_h := by simp, conservation_z := by simp }⟩

/-- **Candidate-B battery 2 (the disqualifying defect).**  The frozen conservation
equality is a projection of the record: nothing is proved by stating it. -/
theorem frontierCounts_conservation_is_projection (c : FrontierCounts (Fin 3)) :
    ∑ v, c.h v = c.H0 + c.S :=
  c.conservation_h

/-- **Candidate-B battery 3 (unfaithfulness).**  The record's Kraft field is
disconnected from the frozen `kappa_v = 2^{r-d_v}` of its own routes: here the field
holds while the routes are not prefix-free and their true capacities sum to twice the
recorded width. -/
theorem frontierCounts_kraft_is_by_fiat :
    ∃ c : FrontierCounts (Fin 2),
      (∑ v, c.cap v ≤ c.width)
        ∧ ¬ PrefixFreeFrontier c.route
        ∧ c.width < ∑ v, stoppingCapacity 2 (c.route v).length := by
  refine ⟨{ route := fun _ => [], cap := fun _ => 0, h := fun _ => 0, z := fun _ => 0,
            width := 4, H0 := 0, W0 := 0, S := 0,
            kraft := by simp, conservation_h := by simp, conservation_z := by simp },
          by simp, ?_, by decide⟩
  intro hpf
  exact hpf 0 1 (by decide) (List.prefix_refl _)

/-! ## §7  Non-vacuity, statement poles and the legal instance

The three tiers of witness legality are named in the module docstring and are binding
on consumers: tier 1 is symbolic in the frozen parameters, tier 2 is a fully
instantiated legal instance of this block's regime, tier 3 is a separating probe at a
minimal carrier and is never a parameter value. -/

/-- **Tier 1 (symbolic in the frozen width).**  For every `r`, the full depth-`r`
frontier is prefix-free, sits at suffix depths at most `r`, and attains Kraft's
inequality with **equality**: `sum_v kappa_v = 2^r = q_2`.

Nothing is evaluated, so this reaches the frozen widths `q_2 >= 6144` forced by
`eq:stage2-structural-gates` (`06:832--847`); and since the bound is attained,
`sum_stoppingCapacity_le_width` cannot be strengthened. -/
theorem kraft_tight_symbolic (r : ℕ) :
    PrefixFreeFrontier (fun f : Fin r → Bool => List.ofFn f)
      ∧ (∀ f : Fin r → Bool, (List.ofFn f).length ≤ r)
      ∧ ∑ f : Fin r → Bool, stoppingCapacity r (List.ofFn f).length = 2 ^ r := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg hpre
    obtain ⟨t, ht'⟩ := hpre
    have ht : List.ofFn f ++ t = List.ofFn g := ht'
    have hlen : (List.ofFn f).length + t.length = (List.ofFn g).length := by
      rw [← ht, List.length_append]
    simp only [List.length_ofFn] at hlen
    have ht0 : t = [] := by
      have h0 : t.length = 0 := by omega
      simpa using h0
    rw [ht0, List.append_nil] at ht
    exact hfg (List.ofFn_injective ht)
  · intro f; simp
  · simp [stoppingCapacity]

/-- **Tier 3 (the three arrivals are separated).**  The two masses distinguish the
three frozen outcomes: an ordinary token carries ordinary mass only, an unsplit
witness carries both masses at one node, and a split witness carries ordinary mass at
two nodes and no bonus mass.  So `FrontierArrival` is no subsingleton and the frozen
three-way bookkeeping has content. -/
theorem frontierArrival_nondegenerate :
    (FrontierArrival.ordinary (0 : Fin 2)).hContrib 0 = 1
      ∧ (FrontierArrival.ordinary (0 : Fin 2)).zContrib 0 = 0
      ∧ (FrontierArrival.unsplit (0 : Fin 2)).hContrib 0 = 1
      ∧ (FrontierArrival.unsplit (0 : Fin 2)).zContrib 0 = 1
      ∧ (FrontierArrival.split (0 : Fin 2) 1).hContrib 0 = 1
      ∧ (FrontierArrival.split (0 : Fin 2) 1).hContrib 1 = 1
      ∧ (FrontierArrival.split (0 : Fin 2) 1).zContrib 0 = 0 := by
  decide

/-- **Statement pole (Kraft needs its prefix-free frontier).**  Two frontier nodes at
suffix depths at most `r = 2`, one of whose routes extends the other, have capacities
summing to `6 > 4 = q_2`.  So `hpf` in `sum_stoppingCapacity_le_width` is
load-bearing and is not an artefact of the proof. -/
theorem kraft_pole_needs_prefix_free :
    ∃ route : Fin 2 → List Bool,
      ¬ PrefixFreeFrontier route
        ∧ (∀ v, (route v).length ≤ 2)
        ∧ 2 ^ 2 < ∑ v, stoppingCapacity 2 (route v).length := by
  refine ⟨![[], [false]], ?_, by decide, by decide⟩
  intro h
  exact h 0 1 (by decide) ⟨[false], by simp⟩

/-- **Statement pole (the uniqueness clause needs the frontier-pair clause).**  A
single split witness whose two ordinary tokens are counted at the *same* node gives a
node holding one routed object and ordinary mass `2`, which no capacity-one node can
carry.  So `hpair` in `hMass_le_one_of_uniqueness` is load-bearing, and
`FrontierArrival.split` would be unsound to equip with an unconditional mass bound. -/
theorem hMass_pole_needs_distinct_split_targets :
    ∃ arr : Fin 1 → FrontierArrival (Fin 1),
      (arrivalsAt arr 0).card = 1
        ∧ hMass arr 0 = 2
        ∧ ¬ (hMass arr 0 + zMass arr 0 ≤ stoppingCapacity 0 0) := by
  refine ⟨![FrontierArrival.split 0 0], by decide, by decide, by decide⟩

/-- The frontier of the legal instance: three prefix-free stopping nodes at suffix
depths `1, 2, 2` below a width `q_2 = 2^3 = 8`, so `kappa = 4, 2, 2`. -/
def probeFrontierRoute : Fin 3 → List Bool := ![[false], [true, false], [true, true]]

/-- The arrivals of the legal instance: seven good coordinates, four of them
witnesses, one of those split.  All three frozen outcomes occur. -/
def probeArrival : Fin 7 → FrontierArrival (Fin 3) :=
  ![FrontierArrival.ordinary 0, FrontierArrival.ordinary 0, FrontierArrival.ordinary 1,
    FrontierArrival.unsplit 0, FrontierArrival.unsplit 1, FrontierArrival.unsplit 2,
    FrontierArrival.split 0 2]

/-- **Aux (the probe frontier is prefix-free).** -/
theorem probeFrontierRoute_prefixFree : PrefixFreeFrontier probeFrontierRoute := by
  intro v w hvw hpre
  obtain ⟨t, ht⟩ := hpre
  fin_cases v <;> fin_cases w <;> simp [probeFrontierRoute] at ht hvw

/-- **Tier 2 -- the legal instance, and the hypothesis-consistency readout of the
whole block.**  At `r = 3` (so `q_2 = 8`), `b = 1`, `w = 5`, `|H| = 7`, `|W| = 4`,
`S = 1`:

* the frontier is prefix-free at suffix depths at most `r`, and Kraft is **attained**
  (`sum_v kappa_v = 8 = q_2`);
* all three frozen conservation equalities hold at those counts, with all three
  arrival kinds occurring and both masses nonzero somewhere;
* the frozen side conditions the conservation lines are converted against hold
  simultaneously: `|H| <= q_2` (the frozen `H = [q_2] \ B` of `08:730`),
  `q_2 <= |H| + b` and `w <= |W| + b` (`eq:selected-mass` as `08:1120--1123` reads
  it), and `4b < w` (`lem:dense-select-branch`, `08:723--726`);
* and the deficit bound of SS5 holds, **with equality**.

So the block's entire premise bundle is simultaneously satisfiable at values the
frozen text permits: no result above is quantified over an empty regime, and no
`False` follows from the bundle.  Tier 2, not a schedule instance: the pair does not
satisfy the full `eq:stage2-structural-gates` (`06:832--847`), which forces
`q_2 >= 6144`, and it does not need to, since every statement instantiated here is
general in `r`, in the carriers and in the arrival function. -/
theorem frontierConservation_legal_instance :
    PrefixFreeFrontier probeFrontierRoute
      ∧ (∀ v, (probeFrontierRoute v).length ≤ 3)
      ∧ (∑ v, stoppingCapacity 3 (probeFrontierRoute v).length) = 2 ^ 3
      ∧ Fintype.card (Fin 7) = 7
      ∧ witnessCount probeArrival = 4
      ∧ splitCount probeArrival = 1
      ∧ (∑ v, hMass probeArrival v) = 7 + 1
      ∧ (∑ v, zMass probeArrival v) + 1 = 4
      ∧ (∑ v, (hMass probeArrival v + zMass probeArrival v)) = 7 + 4
      ∧ hMass probeArrival 0 = 4 ∧ zMass probeArrival 0 = 1
      ∧ hMass probeArrival 2 = 2 ∧ zMass probeArrival 2 = 1
      ∧ (7 : ℕ) ≤ 2 ^ 3
      ∧ (2 ^ 3 : ℕ) ≤ 7 + 1
      ∧ (5 : ℕ) ≤ 4 + 1
      ∧ 4 * 1 < (5 : ℕ)
      ∧ (∑ v, stoppingCapacity 3 (probeFrontierRoute v).length) + splitCount probeArrival
          = (∑ v, hMass probeArrival v) + 1 := by
  refine ⟨probeFrontierRoute_prefixFree, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Tier 3 -- the hypotheses of `isolationNode_capacity_of_uniqueness` fire
together.**  One unsplit witness at a node of residual capacity `kappa = 2`: the node
holds exactly one routed object, the frontier-pair hypothesis is vacuously available,
the bonus mass is positive so the frozen `kappa_v >= 2` requirement genuinely fires,
and the conclusion `h_v + z_v <= kappa_v` is **tight**.  Without this readout the
isolation lemma could be quantified over a bundle its own premises force empty. -/
theorem isolation_capacity_hypotheses_consistent :
    ∃ arr : Fin 1 → FrontierArrival (Fin 1),
      (arrivalsAt arr 0).card = 1
        ∧ (∀ (α : Fin 1) (v w : Fin 1), arr α = FrontierArrival.split v w → v ≠ w)
        ∧ 0 < zMass arr 0
        ∧ hMass arr 0 + zMass arr 0 = stoppingCapacity 1 0 := by
  refine ⟨fun _ => FrontierArrival.unsplit 0, by decide, ?_, by decide, by decide⟩
  intro _ v w hα
  have h : (FrontierArrival.unsplit (0 : Fin 1)) = FrontierArrival.split v w := hα
  simp at h

end EthInapproximability.ParameterizedNP.DenseFrontierConservation
