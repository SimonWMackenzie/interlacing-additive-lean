import EthInapproximability.ParameterizedNP.DenseFrontierConservation
import EthInapproximability.ParameterizedNP.PilotWeightedFrontier

/-!
# Parameterized NP route: the eighth block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 1014--1134** -- the
  weighted-frontier principle of `sec:dense-weighted-count` and its dense
  instantiation, which the predecessor block deliberately left open.  The anchors
  traced here, in the order the frozen block prints them:
  * `lem:abstract-weighted-frontier` (label `08:1015`, statement `08:1014--1046`):
    "Let a finite set of frontier nodes be a disjoint union
    `V = V_A sqcup V_I`.  For every `v in V`, let `kappa_v, h_v, z_v in N` satisfy
    `1 <= kappa_v`, `0 <= z_v <= h_v`.  Let `q, H_0, W_0, S, b, w in N`, with
    `S <= W_0`, and assume the complete conservation, width, retained-mass, and
    isolation hypotheses" `eq:abstract-weighted-frontier-input`
    (`08:1027--1037`), "Then some `v in V_A` satisfies"
    `eq:abstract-weighted-frontier-output` (`08:1039--1044`), i.e.
    `4 h_v >= 3 kappa_v` and `h_v + z_v > kappa_v`;
  * the frozen proof (`08:1048--1089`): "Suppose no Alice node satisfies both
    conclusions.  No node has `h_v > kappa_v` ...  Hence the natural deficit
    `e_v = kappa_v - h_v` is defined without truncation at every node" (`1049--1057`);
    "`sum_v e_v + H_0 + S = sum_v kappa_v <= q <= H_0 + b`, so `sum_v e_v <= b`"
    (`1058--1063`); "Call an Alice node low if `4 h_v < 3 kappa_v`.  Since
    `z_v <= h_v`, its signed excess satisfies `h_v + z_v - kappa_v <= 2 h_v - kappa_v
    = kappa_v - 2 e_v`.  The low inequality and `h_v = kappa_v - e_v` give
    `kappa_v < 4 e_v`.  Thus every positive excess at a low Alice node is strictly
    less than `2 e_v`.  Isolation nodes have nonpositive excess by hypothesis, and
    high Alice nodes have nonpositive excess under the supposition" (`1065--1076`);
    "`sum_v (h_v + z_v - kappa_v) = H_0 + W_0 - sum_v kappa_v >= H_0 + W_0 - q
    >= w - 2b > 2b`" (`1078--1086`); "All positive terms must occur at low Alice
    nodes, where their sum is strictly less than `2 sum_v e_v <= 2b`, a
    contradiction" (`1087--1088`);
  * `lem:dense-weighted-frontier` (label `08:1092`, statement `08:1091--1099`):
    "There is an Alice frontier node `v` satisfying `h_v >= (3/4) kappa_v`,
    `h_v + z_v - kappa_v > 0`";
  * its frozen proof (`08:1101--1134`): "Apply `lem:abstract-weighted-frontier` to
    the stopping frontier, with `V_A = {Alice stopping nodes}`,
    `V_I = {coordinate-isolation nodes}`, and with `q = q_2`, `H_0 = |H|`,
    `W_0 = |W|`.  The no-premature-leaf lemma makes these two node classes
    exhaustive, and `d_v <= r` gives `1 <= kappa_v`.  The inequalities
    `0 <= z_v <= h_v`, the two conservation equalities, and the width bound are
    exactly `eq:frontier-conservation`; its third equality also gives `S <= |W|`.
    Equation `eq:selected-mass` is equivalently `q_2 <= |H| + b`, `w <= |W| + b`.
    For the first conversion, use `b = |B_{j_*}| <= q_2`; for the second, use
    `b < w`, which follows from `4b < w`.  Thus neither conversion relies on
    truncated subtraction.  The strict inequality `4b < w` is
    `lem:dense-select-branch`, and the last hypothesis is `eq:isolation-capacity`.
    The abstract conclusion `4 h_v >= 3 kappa_v` is the same as
    `h_v >= 3 kappa_v / 4`, and its second conclusion is the required positive
    excess."
* **A rendering defect in the frozen source, recorded and not repaired here.**
  Line `08:1036`, the last line of `eq:abstract-weighted-frontier-input`, reads

  > `\forall v\in\mathcal V_I,qquad h_v+z_v\le\kappa_v.`

  with a **missing backslash** on `\qquad`, so the reviewed rendering prints a
  literal `qquad` between the quantifier and the inequality.  This is a spacing
  macro only: the mathematical content of the line is unambiguous, and the frozen
  text pins it twice independently -- `eq:isolation-capacity` (`08:1004--1012`)
  states exactly `h_v + z_v <= kappa_v` "at every isolation node", and the frozen
  proof of `lem:dense-weighted-frontier` says at `08:1130--1131` that "the last
  hypothesis is `eq:isolation-capacity`".  The hypothesis is therefore transcribed
  as `forall v in V_I, h_v + z_v <= kappa_v`, which is what both cross-references
  fix.  No value is invented and no source file is edited: the frozen release is
  immutable, and this is a **rendering** finding, not a missing-value finding.
* **Predecessor anchors (the handoffs consumed by pin, never restated):**
  * the banked `EthInapproximability.ParameterizedNP.DenseFrontierConservation`,
    which supplies all four lines of `eq:frontier-conservation` -- `sum_hMass_eq`
    (`sum_v h_v = |H| + S`), `sum_zMass_add_splitCount_eq` (the untruncated
    `sum_v z_v + S = |W|`), `sum_stoppingCapacity_le_width` (Kraft,
    `sum_v kappa_v <= q_2`) -- together with `zMass_le_hMass` (the frozen
    `0 <= z_v <= h_v`), `splitCount_le_witnessCount` (the frozen `08:1118` reading
    `S <= |W|`), the arrival encoding `FrontierArrival` with `hMass`, `zMass`,
    `witnessCount`, `splitCount`, and `isolationNode_capacity_of_uniqueness`
    (`eq:isolation-capacity` at the counted masses);
  * the banked `EthInapproximability.ParameterizedNP.DenseWeightedCount`, which
    supplies `stoppingCapacity` (the frozen `kappa_v = 2^{r-d_v}`) with
    `one_le_stoppingCapacity` -- the frozen "`d_v <= r` gives `1 <= kappa_v`" of
    `08:1114--1115` -- `PrefixFreeFrontier`, and the frontier classification
    `isolationNodes` / `aliceNodes` with `frontier_disjoint` and `frontier_union`,
    which are the frozen "the no-premature-leaf lemma makes these two node classes
    exhaustive" of `08:1113--1114`;
  * the banked `EthInapproximability.ParameterizedNP.DenseBranchSelection`, which
    supplies `selectedGood` / `selectedWitness` with `card_selectedGood` and
    `card_selectedWitness_ge` -- the two conversions of `eq:selected-mass` the
    frozen proof performs at `08:1119--1127` -- and `denseSelectBranch`, the frozen
    `4b < w` of `lem:dense-select-branch`;
  * the banked `EthInapproximability.ParameterizedNP.weightedFrontier` and
    `weightedFrontier_threeQuarters` (the real-valued transcription pilot), whose
    numerical core is **consumed by pin** in `abstractWeightedFrontier_from_pilot`
    and is **not** claimed as new work by this tranche.
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design and appears in
  no hypothesis below.  The deep inputs of this block are named hypotheses at the
  exact gates the frozen text states them:
  * the coordinatewise uniqueness clause of `08:1004--1005` and the frontier-pair
    clause of `08:934--935` are `huniq` and `hpair`, exactly as the banked
    predecessor carries them; nothing here upgrades that bar, and they are spent
    only in `denseWeightedFrontier_of_uniqueness`;
  * `eq:selected-mass` in its two frozen conversions (`08:1119--1123`) is the pair
    of binders `hselected` (`q_2 <= |H| + b`) and `hwitness` (`w <= |W| + b`),
    discharged in `denseWeightedFrontier_at_selected_branch` by the banked
    `card_selectedGood` and `card_selectedWitness_ge`;
  * `lem:dense-select-branch` (`4b < w`) is the binder `hgap`, never re-proved;
  * the depth clause `d_v <= r` is the binder `hdepth`, and prefix-freeness the
    binder `hpf`, both passed straight through to the banked Kraft bound.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency graph.
* **New work.**  The frozen `lem:abstract-weighted-frontier` in its printed
  natural-number shape, proved outright; the untruncated conversions the frozen
  proof insists on at `08:1124--1127`; the signed-excess estimate the reader states
  (`sum_v (h_v + z_v - kappa_v) > 2b`), which the banked predecessor recorded (its
  coverage limit 5) as **absent** and not citable from there; and
  `lem:dense-weighted-frontier`, the first declaration in the development that
  asserts a forced Alice frontier node.
* Proof status: **new** for the abstract principle, the signed-excess estimate and
  the dense instantiation; **inherited by pin** for every conservation equality,
  Kraft, the capacity weight, the frontier classification, `eq:isolation-capacity`,
  `eq:selected-mass` and the real-valued numerical core.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no unproved
  placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, the proof outline of
`thm:paper-protected-stage4`.  The banked `DenseWeightedCount` row claims lines
259--265 and the banked `DenseFrontierConservation` row claims 265--266; the
remainder of that chain is claimed here, each clause **once**:

* **lines 266--268**, "while the selected-branch inequality `w > 4b` makes the total
  signed excess `sum_v(h_v+z_v-kappa_v) > 2b`" -- `sum_signedExcess_gt`, and its
  real-valued twin `sum_signedExcess_gt_real`;
* **line 269**, "its excess would be less than twice its deficit" --
  `excess_lt_two_mul_deficit_of_low`;
* **lines 270--271**, "Thus some Alice node satisfies `4h_v >= 3kappa_v` and
  `h_v+z_v > kappa_v`" -- `denseWeightedFrontier`, with `denseWeightedFrontier_real`
  the frozen fractional printing `h_v >= (3/4) kappa_v`.

Line 270's "summing would contradict these bounds" is a description of method, not
an assertion, and is **not** cited as a statement by anything below.  The frozen
`lem:abstract-weighted-frontier` has **no** reader counterpart: the reader
condenses the whole principle into the conditional sentence at 268--270 and states
only the dense conclusion, so `abstractWeightedFrontier` and its variants are
carried by the autoformalization anchor alone.  The reader sentences from line 272
onwards ("The retained template/source and selector/diagonal reservoirs close the
resulting stopping cases ...") are `sec:dense-alice-closure`'s and are **not**
claimed here.

## Candidate encodings of the weighted-frontier datum (`k = 2`, raced)

The novel object of this tranche is the *weighted frontier datum*: a finite node set
split into the two frozen classes, carrying the three per-node numbers
`kappa_v, h_v, z_v` and the six global counts `q, H_0, W_0, S, b, w` that
`eq:abstract-weighted-frontier-input` relates.

**Candidate A (landed, SS1--SS5).**  No new type at all: the datum is *explicit
binders*.  The two classes are two `Finset`s with the frozen `V = V_A sqcup V_I` as
the two hypotheses `hdisj` and `hcover`; `kappa, h, z` are functions; the six counts
are natural-number binders; and every line of
`eq:abstract-weighted-frontier-input` is a hypothesis of the theorem, so nothing can
be true by fiat.  The whole statement is **subtraction-free**, which is precisely the
care the frozen proof takes at `08:1124--1127` ("Thus neither conversion relies on
truncated subtraction"): the third conservation line appears in its untruncated form
`sum_v z_v + S = W_0` (`08:1030`), and the two conclusions are
`3 kappa_v <= 4 h_v` and `kappa_v < h_v + z_v` rather than statements about
truncated differences.  10 aux lemmas proved on the binder form, the frozen
hypothesis list transcribed literally as a second entry point, an independent
cross-derivation from the banked real-valued pilot, and a legal instance (SS7).

**Candidate B (rejected, SS6).**  Package the datum as a record
`WeightedFrontierInput` whose fields are the classes, the three functions, the six
counts *and every line of `eq:abstract-weighted-frontier-input`*.  4 aux lemmas
proved, and it loses on three counts.  First, `split_le` (`S <= W_0`) is a field
that restates a derived telescope: `weightedFrontierInput_split_le_is_redundant`
derives it from `conservation_z` alone, and the frozen text derives it too
("its third equality also gives `S <= |W|`", `08:1118`).  Second, the record is
unfaithful as data: `weightedFrontierInput_counts_float` exhibits two inhabitants
with *identical* `cap`, `h`, `z` and classes but different `H0` and `S`, whereas in
the frozen instantiation `H_0 = |H|` and `S` are both determined by the arrival
function -- so the record forgets what the frozen datum knows.  Third, it adds no
mathematics: `weightedFrontierInput_is_a_repackaging` proves the record-form theorem
by projecting the record's fields into Candidate A, so the record is a strictly
lossier spelling of the same binder list.  The race is decided on faithfulness, not
length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the pointwise weighted estimate, general (3): `weighted_le_of_capacity`,
  `weighted_le_of_low`, `weighted_le_of_not_forced`.
* `A2` the frozen deficit reading (`08:1049--1057`, `08:1065--1073`), general (2):
  `le_capacity_of_not_forced`, `excess_lt_two_mul_deficit_of_low`.
* `A3` the summed form, general (1): `sum_weighted_le`.
* `A4` `lem:abstract-weighted-frontier`, general (2): `abstractWeightedFrontier_core`
  (the hypotheses actually consumed) and `abstractWeightedFrontier` (the frozen
  printed hypothesis list, transcribed literally).
* `A5` the frozen conversions of `08:1119--1127`, general (2):
  `pilot_deficit_of_conservation`, `pilot_excess_of_conservation`.
* `A6` the signed-excess estimate (reader 266--268), general (2):
  `sum_signedExcess_gt`, `sum_signedExcess_gt_real`.
* `A7` the pin cross-derivation, general (1): `abstractWeightedFrontier_from_pilot`.
* `A8` `lem:dense-weighted-frontier`, general (4): `denseWeightedFrontier`,
  `denseWeightedFrontier_real`, `denseWeightedFrontier_of_uniqueness`,
  `denseWeightedFrontier_at_selected_branch`.
* Candidate B's own battery (4): `weightedFrontierInput_nonempty`,
  `weightedFrontierInput_split_le_is_redundant`, `weightedFrontierInput_counts_float`,
  `weightedFrontierInput_is_a_repackaging`.

That is **17 battery entries proved for the landed candidate plus 4 for the rejected
one**, with `0` unproved, alongside **three statement poles**
(`weightedFrontier_pole_needs_gap`, `weightedFrontier_pole_needs_isolation`,
`weightedFrontier_not_at_every_alice_node`) and **four non-vacuity / consistency
readouts** (`weightedFrontier_legal_instance`, `weightedFrontier_at_probe`,
`denseWeightedFrontier_legal_instance`, `denseWeightedFrontier_at_probe`), plus the
probe carriers `probeRoute`, `probeIso`, `decidableProbeIso`, `probeArr`,
`probeKappa`, `probeH`, `probeZ`, `probeInput`, `probeInput'` and
`probeRoute_prefixFree`.

The module has **39** source declarations in all: 9 definitions (`probeInput`,
`probeInput'`, `probeKappa`, `probeH`, `probeZ`, `probeRoute`, `probeIso`,
`decidableProbeIso`, `probeArr`), 1 type (`WeightedFrontierInput`) and 29 proved
results; with the structure's constructor and its 22 field projections that is **62**
audited names.

## Why the existential deliverables are not satisfied by a trivial witness

Both headline statements are existential: "some `v in V_A` satisfies ...".  A trivial
witness would be a **fixed** Alice node.  `weightedFrontier_not_at_every_alice_node`
refutes that reading outright: it exhibits a datum satisfying every hypothesis of
`abstractWeightedFrontier` in which one Alice node fails **both** conclusions, so the
content of the statement is not the nonemptiness of `V_A` but that the counted data
*force* a node with three-quarters of its capacity and strictly positive excess.  The
second conclusion `kappa_v < h_v + z_v` is what rules out the other trivial reading:
`kappa_v >= 1` always holds, so a node with `h_v = z_v = 0` would satisfy no clause,
and a node satisfying only `3 kappa_v <= 4 h_v` is exactly the "high Alice node with
nonpositive excess" the frozen proof must exclude (`08:1075--1076`).

## Three-tier witness legality

Every witness below is labelled with the tier of legality it actually carries, and no
witness is read as more than its tier permits.

* **Tier 1 -- symbolic in the frozen parameters.**  Every result of SS1--SS5 is
  general in the node type, in `kappa, h, z` and in all six counts, and takes no
  schedule hypothesis whatever; the dense results of SS5 are general in `r`, in both
  carrier types, in the routes, in the arrival function and in the isolation
  predicate.  Nothing is evaluated, so the frozen widths `q_2 = 2^r >= 6144` forced
  by `eq:stage2-structural-gates` (`06:832--847`) are inside the range of every
  statement.
* **Tier 2 -- a fully instantiated legal instance of the block's regime.**
  `weightedFrontier_legal_instance` and `denseWeightedFrontier_legal_instance`
  exhibit the entire premise bundle at `r = 3` (`q = q_2 = 2^3 = 8`), `b = 1`,
  `w = 6`, `|H| = 8`, `|W| = 5`, `S = 1`, on a two-node frontier at suffix depths
  `1, 1`, where the frozen side conditions all hold on the face of the statement --
  `q_2 <= |H| + b` and `w <= |W| + b` (`eq:selected-mass` as `08:1119--1123` reads
  it) and `4b < w` (`lem:dense-select-branch`, `08:723--726`) -- and where Kraft and
  `eq:isolation-capacity` are both **attained with equality**.
  `denseWeightedFrontier_at_probe` then **applies** the headline at that witness, so
  no `False` follows from the bundle and the lemma is asserted at a real point.  The
  instance is **not** a schedule instance: it does not satisfy the full
  `eq:stage2-structural-gates`, which forces `q_2 >= 6144`, and no parameter value
  may be read out of it.  It does not need to: every statement it instantiates is
  tier 1.
* **Tier 3 -- separating probes at deliberately small carriers.**
  `weightedFrontier_pole_needs_gap`, `weightedFrontier_pole_needs_isolation`,
  `weightedFrontier_not_at_every_alice_node` and Candidate B's four readouts are
  probes of one named hypothesis or one field at a minimal carrier.  They are neither
  schedule instances nor legal instances of the block's regime, and are cited only
  for what they separate.

## Honest scope and recorded coverage limits

1. **The numerical core is inherited, not re-derived.**  The real-valued
   weighted-frontier inequality is the banked
   `EthInapproximability.ParameterizedNP.weightedFrontier_threeQuarters`;
   `abstractWeightedFrontier_from_pilot` consumes it by pin, performing exactly the
   two conversions of `08:1119--1127`.  `abstractWeightedFrontier_core` is a
   *separate*, subtraction-free natural-number derivation of the same frozen
   statement, given because the frozen proof's own care about truncated subtraction
   is invisible over the reals; the two together are a cross-check, and the tranche
   claims the frozen statement and the conversions, not the inequality's discovery.
2. **The routing is still not constructed, and no protocol is evaluated.**  As in the
   banked predecessor, the arrival function, the routes and the isolation predicate
   are *given*.  What is proved is that whatever the routing does, if the frozen
   bookkeeping holds then a forced Alice node exists.  No later tranche may cite this
   module as having built the routing map or the frontier.
3. **The uniqueness and frontier-pair clauses stay hypotheses.**  `08:1004--1005` and
   `08:934--935` are `huniq` and `hpair`; `denseWeightedFrontier_of_uniqueness` is
   the only declaration that consumes them, and it discharges the isolation
   hypothesis through the banked `isolationNode_capacity_of_uniqueness` rather than
   re-proving `eq:isolation-capacity`.
4. **`eq:selected-mass` enters only in its two frozen conversions.**  The
   selected-branch corollary needs one further named hypothesis, `hwitnessSet`, that
   the arrival function's witness coordinates are exactly the frozen
   `W = U_{j_*} \ B_{j_*}` of `08:731`; this is a statement about the routed data
   that the banked bookkeeping does not fix, and it is a binder, never a field.
5. **`4b < w` is never proved here.**  `lem:dense-select-branch` is the banked
   `DenseBranchSelection.denseSelectBranch`; `hgap` passes it through unchanged.
6. **Nothing after `08:1134` is claimed.**  `sec:dense-alice-closure`
   (`08:1136--1324`), `cor:exact-protected-stage4` and `thm:dense-stage4` are
   untouched, and no route completion is claimed.
7. **`r`, `b`, the counts and the carriers are binders, not values.**  No parameter
   schedule may be read out of any witness below; the tier labelling above is binding
   on consumers.
8. **Candidate B is race evidence with a recorded disposition.**
   `WeightedFrontierInput` is consumed by nothing and may not be used to re-encode
   the weighted-frontier datum of `08:1014--1046` without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseWeightedFrontier

open Finset
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseBranchSelection
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseFrontierConservation

/-! ## §1  The pointwise weighted estimate (`08:1065--1076`)

The frozen proof runs the contradiction through a deficit `e_v = kappa_v - h_v` and a
signed excess `h_v + z_v - kappa_v`, both of which are differences of natural numbers.
At the frozen threshold `theta = 3/4` the two cases the proof distinguishes collapse
into a single **subtraction-free** inequality,

  `3 h_v + z_v <= 3 kappa_v`,

which is exactly "the excess is at most twice the deficit" cleared of denominators:
`(h_v + z_v) - kappa_v <= 2 (kappa_v - h_v)`.  Isolation nodes and high Alice nodes
satisfy it because their excess is nonpositive; low Alice nodes satisfy it because
`4 h_v <= 3 kappa_v`.  Keeping the statement subtraction-free is the care the frozen
proof takes at `08:1124--1127`. -/

/-- **Aux 1 (the nonpositive-excess case, `08:1074--1076`).**  A node whose routed
masses fit in its capacity -- an isolation node by `eq:isolation-capacity`, or a high
Alice node under the frozen supposition -- satisfies the pointwise weighted estimate.
General; the frozen standing hypothesis `z_v <= h_v` is deliberately **not** demanded,
because the nonpositive-excess case does not consume it and an unused premise would be
strictly stronger than the paper. -/
theorem weighted_le_of_capacity {κ h z : ℕ} (hcap : h + z ≤ κ) :
    3 * h + z ≤ 3 * κ := by omega

/-- **Aux 2 (the low-node case, `08:1065--1073`).**  "Call an Alice node low if
`4 h_v < 3 kappa_v`.  Since `z_v <= h_v`, its signed excess satisfies
`h_v + z_v - kappa_v <= 2 h_v - kappa_v`" and the low inequality bounds that by twice
the deficit.  General. -/
theorem weighted_le_of_low {κ h z : ℕ} (hz : z ≤ h) (hlow : 4 * h < 3 * κ) :
    3 * h + z ≤ 3 * κ := by omega

/-- **Aux 3 (the dichotomy of the frozen supposition).**  A node that fails **both**
frozen conclusions satisfies the pointwise weighted estimate: either it is high, and
then its excess is nonpositive, or it is low, and then Aux 2 applies.  General. -/
theorem weighted_le_of_not_forced {κ h z : ℕ} (hz : z ≤ h)
    (hnot : ¬ (3 * κ ≤ 4 * h ∧ κ < h + z)) : 3 * h + z ≤ 3 * κ := by
  by_cases hhigh : 3 * κ ≤ 4 * h
  · have hcap : h + z ≤ κ := by
      by_contra hc
      exact hnot ⟨hhigh, by omega⟩
    exact weighted_le_of_capacity hcap
  · exact weighted_le_of_low hz (by omega)

/-- **Aux 4 (`08:1049--1057`, the deficit is untruncated).**  "No node has
`h_v > kappa_v`: this follows from the isolation hypothesis on `V_I`, while at an
Alice node the strict inequality would imply both `4 h_v >= 3 kappa_v` and
`h_v + z_v > kappa_v`.  Hence the natural deficit `e_v = kappa_v - h_v` is defined
without truncation at every node."  General. -/
theorem le_capacity_of_not_forced {κ h z : ℕ}
    (hnot : ¬ (3 * κ ≤ 4 * h ∧ κ < h + z)) : h ≤ κ := by
  by_contra hc
  exact hnot ⟨by omega, by omega⟩

/-- **Aux 5 (reader 269, "its excess would be less than twice its deficit").**  At a
low Alice node the signed excess is strictly below twice the natural deficit.  Stated
over the integers because both quantities are signed in the frozen proof; the
natural-number form cleared of subtraction is Aux 2.  General. -/
theorem excess_lt_two_mul_deficit_of_low {κ h z : ℕ} (hz : z ≤ h) (hlow : 4 * h < 3 * κ) :
    ((h : ℤ) + (z : ℤ) - (κ : ℤ)) < 2 * ((κ : ℤ) - (h : ℤ)) := by
  have hz' : (z : ℤ) ≤ (h : ℤ) := by exact_mod_cast hz
  have hlow' : 4 * (h : ℤ) < 3 * (κ : ℤ) := by exact_mod_cast hlow
  linarith

/-- **Aux 6 (the summed pointwise estimate).**  Summing the pointwise weighted
estimate over the finite frontier.  General in the node type. -/
theorem sum_weighted_le {ι : Type*} [Fintype ι] (κ h z : ι → ℕ)
    (hpt : ∀ v, 3 * h v + z v ≤ 3 * κ v) :
    3 * (∑ v, h v) + (∑ v, z v) ≤ 3 * (∑ v, κ v) := by
  have h1 : ∑ v, (3 * h v + z v) ≤ ∑ v, 3 * κ v :=
    Finset.sum_le_sum (fun v _ => hpt v)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h1

/-! ## §2  `lem:abstract-weighted-frontier` (`08:1014--1089`)

The frozen statement, in the natural numbers it is printed over.  Every line of
`eq:abstract-weighted-frontier-input` is a hypothesis; the two conclusions of
`eq:abstract-weighted-frontier-output` are the frozen `4 h_v >= 3 kappa_v` and
`h_v + z_v > kappa_v`, written without any truncated difference. -/

/-- **`lem:abstract-weighted-frontier` (`08:1014--1046`), with exactly the hypotheses
the proof consumes.**

`hcover` is the exhaustiveness half of the frozen disjoint union `V = V_A sqcup V_I`
(`08:1017--1018`); disjointness is not used by the argument and is therefore **not**
demanded here -- the literal frozen hypothesis list, disjointness included, is the
next declaration.  `hisolation` is the frozen last line of
`eq:abstract-weighted-frontier-input`, i.e. `eq:isolation-capacity`, read through the
two cross-references recorded in the module header (the `08:1036` `qquad` is a
spacing macro, not content).

*The frozen proof, transcribed.*  Suppose no Alice node satisfies both conclusions.
Then every node -- Alice or isolation -- satisfies the subtraction-free pointwise
estimate `3 h_v + z_v <= 3 kappa_v` of SS1, which is the frozen "every positive excess
at a low Alice node is strictly less than `2 e_v`" together with "isolation nodes have
nonpositive excess by hypothesis, and high Alice nodes have nonpositive excess under
the supposition" (`08:1070--1076`).  Summing and substituting the two conservation
equalities, Kraft and the width bound gives `W_0 + 2 S <= 3 b`, hence
`w <= W_0 + b <= 4 b < w`, which is the frozen contradiction of `08:1087--1088`.

General in the node type and in all six counts; no schedule hypothesis appears. -/
theorem abstractWeightedFrontier_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    (alice iso : Finset ι) (κ h z : ι → ℕ) {q H₀ W₀ S b w : ℕ}
    (hcover : alice ∪ iso = Finset.univ)
    (hz : ∀ v, z v ≤ h v)
    (hconsH : ∑ v, h v = H₀ + S)
    (hconsW : (∑ v, z v) + S = W₀)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b)
    (hw : w ≤ W₀ + b)
    (hgap : 4 * b < w)
    (hisolation : ∀ v ∈ iso, h v + z v ≤ κ v) :
    ∃ v ∈ alice, 3 * κ v ≤ 4 * h v ∧ κ v < h v + z v := by
  by_contra hnone
  have hnot : ∀ v ∈ alice, ¬ (3 * κ v ≤ 4 * h v ∧ κ v < h v + z v) := by
    intro v hv hboth
    exact hnone ⟨v, hv, hboth⟩
  have hpt : ∀ v, 3 * h v + z v ≤ 3 * κ v := by
    intro v
    by_cases hva : v ∈ alice
    · exact weighted_le_of_not_forced (hz v) (hnot v hva)
    · have hvi : v ∈ iso := by
        have hmem : v ∈ alice ∪ iso := by rw [hcover]; exact Finset.mem_univ v
        rcases Finset.mem_union.mp hmem with h' | h'
        · exact absurd h' hva
        · exact h'
      exact weighted_le_of_capacity (hisolation v hvi)
  have hsum := sum_weighted_le κ h z hpt
  omega

/-- **`lem:abstract-weighted-frontier` with the frozen hypothesis list transcribed
literally (`08:1014--1046`).**

"Let a finite set of frontier nodes be a disjoint union `V = V_A sqcup V_I`.  For
every `v in V`, let `kappa_v, h_v, z_v in N` satisfy `1 <= kappa_v`,
`0 <= z_v <= h_v`.  Let `q, H_0, W_0, S, b, w in N`, with `S <= W_0`, and assume the
complete conservation, width, retained-mass, and isolation hypotheses ...  Then some
`v in V_A` satisfies `4 h_v >= 3 kappa_v`, `h_v + z_v > kappa_v`."

Three of the printed hypotheses are **not consumed** by the argument and are carried
only for fidelity to the frozen printing: `hdisj` (disjointness -- only
exhaustiveness is used), `hκ` (`1 <= kappa_v` -- a standing condition on the data,
which the frozen proof never invokes) and `hS` (`S <= W_0` -- which the frozen text
itself derives from the third conservation equality at `08:1118`, and which
`weightedFrontierInput_split_le_is_redundant` re-derives below).  Every one of them is
discharged from a banked pin in the dense instantiation, so carrying them costs
consumers nothing.  General. -/
theorem abstractWeightedFrontier {ι : Type*} [Fintype ι] [DecidableEq ι]
    (alice iso : Finset ι) (κ h z : ι → ℕ) {q H₀ W₀ S b w : ℕ}
    (_hdisj : Disjoint alice iso)
    (hcover : alice ∪ iso = Finset.univ)
    (_hκ : ∀ v, 1 ≤ κ v)
    (hz : ∀ v, z v ≤ h v)
    (_hS : S ≤ W₀)
    (hconsH : ∑ v, h v = H₀ + S)
    (hconsW : (∑ v, z v) + S = W₀)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b)
    (hw : w ≤ W₀ + b)
    (hgap : 4 * b < w)
    (hisolation : ∀ v ∈ iso, h v + z v ≤ κ v) :
    ∃ v ∈ alice, 3 * κ v ≤ 4 * h v ∧ κ v < h v + z v :=
  abstractWeightedFrontier_core alice iso κ h z hcover hz hconsH hconsW hkraft hq hw
    hgap hisolation

/-! ## §3  The frozen conversions of `08:1119--1127`, and the pin cross-derivation

"Equation `eq:selected-mass` is equivalently `q_2 <= |H| + b`, `w <= |W| + b`.  For
the first conversion, use `b = |B_{j_*}| <= q_2`; for the second, use `b < w`, which
follows from `4b < w`.  Thus neither conversion relies on truncated subtraction."

The banked real-valued pilot takes the *digested* hypotheses -- a deficit bound and a
signed-excess bound -- rather than the conservation equalities.  The two lemmas below
are exactly the frozen passage from one to the other, and they are what lets the
numerical core be consumed by pin instead of re-derived. -/

/-- **The deficit conversion (`08:1058--1063`).**  "`sum_v e_v + H_0 + S = sum_v
kappa_v <= q <= H_0 + b`, so `sum_v e_v <= b`", in the real-valued shape the banked
pilot consumes.  General. -/
theorem pilot_deficit_of_conservation {ι : Type*} [Fintype ι] (κ h : ι → ℕ)
    {q H₀ S b : ℕ}
    (hconsH : ∑ v, h v = H₀ + S)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b) :
    ∑ v, ((κ v : ℝ) - (h v : ℝ)) ≤ (b : ℝ) := by
  have hnat : (∑ v, κ v) ≤ H₀ + S + b := by omega
  have hsum : ∑ v, ((κ v : ℝ) - (h v : ℝ))
      = ((∑ v, κ v : ℕ) : ℝ) - ((∑ v, h v : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib]
    push_cast
    ring
  rw [hsum, hconsH]
  have h1 : ((∑ v, κ v : ℕ) : ℝ) ≤ ((H₀ + S + b : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at h1 ⊢
  linarith

/-- **The signed-excess conversion (`08:1078--1086`).**  "`sum_v (h_v + z_v -
kappa_v) = H_0 + W_0 - sum_v kappa_v >= H_0 + W_0 - q >= w - 2b`", in the real-valued
shape the banked pilot consumes.  The frozen `H_0` cancels, so the estimate needs only
the width bound and the retained-mass bound.  General. -/
theorem pilot_excess_of_conservation {ι : Type*} [Fintype ι] (κ h z : ι → ℕ)
    {q H₀ W₀ S b w : ℕ}
    (hconsH : ∑ v, h v = H₀ + S)
    (hconsW : (∑ v, z v) + S = W₀)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b)
    (hw : w ≤ W₀ + b) :
    (w : ℝ) - 2 * (b : ℝ) ≤ ∑ v, ((h v : ℝ) + (z v : ℝ) - (κ v : ℝ)) := by
  have hnat : (∑ v, κ v) + w ≤ H₀ + S + (∑ v, z v) + 2 * b := by omega
  have hsum : ∑ v, ((h v : ℝ) + (z v : ℝ) - (κ v : ℝ))
      = ((∑ v, h v : ℕ) : ℝ) + ((∑ v, z v : ℕ) : ℝ) - ((∑ v, κ v : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    push_cast
    ring
  rw [hsum, hconsH]
  have h1 : (((∑ v, κ v) + w : ℕ) : ℝ) ≤ ((H₀ + S + (∑ v, z v) + 2 * b : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at h1 ⊢
  linarith

/-- **The pin cross-derivation.**  The banked real-valued
`weightedFrontier_threeQuarters` -- the transcription pilot for this very lemma --
yields the frozen natural-number conclusion once the two conversions above are
performed.  Consuming it by pin is what keeps the numerical core out of this
tranche's claims: `abstractWeightedFrontier_core` is an independent, subtraction-free
derivation of the same statement, and the two agreeing is the cross-check.

The isolation hypothesis is passed in the pilot's complement form, which is the same
statement as the frozen `forall v in V_I` under the frozen exhaustiveness.  General. -/
theorem abstractWeightedFrontier_from_pilot {ι : Type*} [Fintype ι]
    (alice : Set ι) (κ h z : ι → ℕ) {q H₀ W₀ S b w : ℕ}
    (hz : ∀ v, z v ≤ h v)
    (hconsH : ∑ v, h v = H₀ + S)
    (hconsW : (∑ v, z v) + S = W₀)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b)
    (hw : w ≤ W₀ + b)
    (hgap : 4 * b < w)
    (hisolation : ∀ v, v ∉ alice → h v + z v ≤ κ v) :
    ∃ v ∈ alice, 3 * κ v ≤ 4 * h v ∧ κ v < h v + z v := by
  obtain ⟨v, hv, hhigh, hpos⟩ :=
    weightedFrontier_threeQuarters alice (fun v => (κ v : ℝ)) (fun v => (h v : ℝ))
      (fun v => (z v : ℝ)) (b : ℝ) (w : ℝ)
      (fun v => Nat.cast_nonneg (κ v)) (fun v => Nat.cast_nonneg (z v))
      (fun v => by change ((z v : ℝ)) ≤ ((h v : ℝ)); exact_mod_cast hz v)
      (fun v hva => by
        change ((h v : ℝ)) + ((z v : ℝ)) ≤ ((κ v : ℝ))
        exact_mod_cast hisolation v hva)
      (pilot_deficit_of_conservation κ h hconsH hkraft hq)
      (pilot_excess_of_conservation κ h z hconsH hconsW hkraft hq hw)
      (by exact_mod_cast hgap)
  refine ⟨v, hv, ?_, ?_⟩
  · have hcast : (3 : ℝ) * (κ v : ℝ) ≤ 4 * (h v : ℝ) := by linarith
    exact_mod_cast hcast
  · have hcast : (κ v : ℝ) < (h v : ℝ) + (z v : ℝ) := by linarith
    exact_mod_cast hcast

/-! ## §4  The signed-excess estimate (reader 266--268, `08:1078--1086`)

"while the selected-branch inequality `w > 4b` makes the total signed excess
`sum_v(h_v+z_v-kappa_v) > 2b`."  This is the half of the frozen contradiction the
banked predecessor recorded as absent: it needs the *second* conversion of
`eq:selected-mass`, `w <= |W| + b`, which no earlier tranche established. -/

/-- **The signed-excess estimate over the integers.**  General; the total signed
excess of the frontier strictly exceeds `2b`. -/
theorem sum_signedExcess_gt {ι : Type*} [Fintype ι] (κ h z : ι → ℕ)
    {q H₀ W₀ S b w : ℕ}
    (hconsH : ∑ v, h v = H₀ + S)
    (hconsW : (∑ v, z v) + S = W₀)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b)
    (hw : w ≤ W₀ + b)
    (hgap : 4 * b < w) :
    (2 * b : ℤ) < ∑ v, ((h v : ℤ) + (z v : ℤ) - (κ v : ℤ)) := by
  have hsum : ∑ v, ((h v : ℤ) + (z v : ℤ) - (κ v : ℤ))
      = ((∑ v, h v : ℕ) : ℤ) + ((∑ v, z v : ℕ) : ℤ) - ((∑ v, κ v : ℕ) : ℤ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    push_cast
    ring
  rw [hsum]
  omega

/-- **The reader's literal sentence (266--268), over the reals.**  The same estimate
in the field the reader writes it in; no new mathematics.  General. -/
theorem sum_signedExcess_gt_real {ι : Type*} [Fintype ι] (κ h z : ι → ℕ)
    {q H₀ W₀ S b w : ℕ}
    (hconsH : ∑ v, h v = H₀ + S)
    (hconsW : (∑ v, z v) + S = W₀)
    (hkraft : ∑ v, κ v ≤ q)
    (hq : q ≤ H₀ + b)
    (hw : w ≤ W₀ + b)
    (hgap : 4 * b < w) :
    (2 : ℝ) * (b : ℝ) < ∑ v, ((h v : ℝ) + (z v : ℝ) - (κ v : ℝ)) := by
  have hpilot := pilot_excess_of_conservation κ h z hconsH hconsW hkraft hq hw
  have hgap' : 4 * (b : ℝ) < (w : ℝ) := by exact_mod_cast hgap
  linarith

/-! ## §5  `lem:dense-weighted-frontier` (`08:1091--1134`)

"Apply `lem:abstract-weighted-frontier` to the stopping frontier, with
`V_A = {Alice stopping nodes}`, `V_I = {coordinate-isolation nodes}`, and with
`q = q_2`, `H_0 = |H|`, `W_0 = |W|`."  Every ingredient the application needs is a
banked pin: the classification and its exhaustiveness, the capacity weight and
`1 <= kappa_v`, the four lines of `eq:frontier-conservation`, and `S <= |W|`.  Only
the two conversions of `eq:selected-mass` and the selected-branch gap are binders. -/

/-- **`lem:dense-weighted-frontier` (`08:1091--1099`).**  "There is an Alice frontier
node `v` satisfying `h_v >= (3/4) kappa_v`, `h_v + z_v - kappa_v > 0`", in the
natural-number form `3 kappa_v <= 4 h_v` and `kappa_v < h_v + z_v` that the frozen
proof records at `08:1131--1134` as the same statement.

Discharged from banked pins, in the order the frozen proof names them: the two node
classes are exhaustive by `frontier_union` and disjoint by `frontier_disjoint`
(`08:1113--1114`); `1 <= kappa_v` is `one_le_stoppingCapacity` (`08:1114--1115`);
`0 <= z_v <= h_v` is `zMass_le_hMass`; the two conservation equalities are
`sum_hMass_eq` and `sum_zMass_add_splitCount_eq`; the width bound is Kraft,
`sum_stoppingCapacity_le_width`; and `S <= |W|` is `splitCount_le_witnessCount`
(`08:1118`).  The binders are exactly the frozen ones the paper imports from outside
`sec:dense-weighted-count`: `hselected` and `hwitness` are the two conversions of
`eq:selected-mass` (`08:1119--1123`), `hgap` is `lem:dense-select-branch`
(`08:1128--1129`), and `hisocap` is `eq:isolation-capacity` (`08:1130--1131`).

General in `r`, in both carrier types, in the routes, in the arrival function and in
the isolation predicate; no schedule hypothesis appears.

*Why the trivial witness fails.*  A fixed Alice node does not work:
`weightedFrontier_not_at_every_alice_node` satisfies every hypothesis while one Alice
node fails both conclusions. -/
theorem denseWeightedFrontier {ι Coord : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Coord] {r b w : ℕ}
    (arr : Coord → FrontierArrival ι) (route : ι → List Bool)
    (iso : ι → Prop) [DecidablePred iso]
    (hpf : PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r)
    (hselected : 2 ^ r ≤ Fintype.card Coord + b)
    (hwitness : w ≤ witnessCount arr + b)
    (hgap : 4 * b < w)
    (hisocap : ∀ v ∈ isolationNodes iso,
      hMass arr v + zMass arr v ≤ stoppingCapacity r (route v).length) :
    ∃ v ∈ aliceNodes iso,
      3 * stoppingCapacity r (route v).length ≤ 4 * hMass arr v ∧
        stoppingCapacity r (route v).length < hMass arr v + zMass arr v := by
  refine abstractWeightedFrontier (aliceNodes iso) (isolationNodes iso)
    (fun v => stoppingCapacity r (route v).length) (hMass arr) (zMass arr)
    (frontier_disjoint iso).symm ?_ (fun v => one_le_stoppingCapacity r _)
    (zMass_le_hMass arr) (splitCount_le_witnessCount arr) (sum_hMass_eq arr)
    (sum_zMass_add_splitCount_eq arr) (sum_stoppingCapacity_le_width route hpf hdepth)
    hselected hwitness hgap hisocap
  rw [Finset.union_comm]
  exact frontier_union iso

/-- **`lem:dense-weighted-frontier` in the frozen fractional printing
(`08:1094--1098`).**  "`h_v >= (3/4) kappa_v`, `h_v + z_v - kappa_v > 0`", over the
reals.  No new mathematics: it is the previous statement cast, exactly as the frozen
proof reads it at `08:1131--1134`.  General. -/
theorem denseWeightedFrontier_real {ι Coord : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Coord] {r b w : ℕ}
    (arr : Coord → FrontierArrival ι) (route : ι → List Bool)
    (iso : ι → Prop) [DecidablePred iso]
    (hpf : PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r)
    (hselected : 2 ^ r ≤ Fintype.card Coord + b)
    (hwitness : w ≤ witnessCount arr + b)
    (hgap : 4 * b < w)
    (hisocap : ∀ v ∈ isolationNodes iso,
      hMass arr v + zMass arr v ≤ stoppingCapacity r (route v).length) :
    ∃ v ∈ aliceNodes iso,
      (3 / 4 : ℝ) * (stoppingCapacity r (route v).length : ℝ) ≤ (hMass arr v : ℝ) ∧
        0 < (hMass arr v : ℝ) + (zMass arr v : ℝ)
          - (stoppingCapacity r (route v).length : ℝ) := by
  obtain ⟨v, hv, hhigh, hpos⟩ :=
    denseWeightedFrontier arr route iso hpf hdepth hselected hwitness hgap hisocap
  have hhigh' : (3 : ℝ) * (stoppingCapacity r (route v).length : ℝ)
      ≤ 4 * (hMass arr v : ℝ) := by exact_mod_cast hhigh
  have hpos' : (stoppingCapacity r (route v).length : ℝ)
      < (hMass arr v : ℝ) + (zMass arr v : ℝ) := by exact_mod_cast hpos
  exact ⟨v, hv, by linarith, by linarith⟩

/-- **`lem:dense-weighted-frontier` with `eq:isolation-capacity` discharged from the
frozen uniqueness clause.**  "the last hypothesis is `eq:isolation-capacity`"
(`08:1130--1131`), which the banked predecessor derives from the coordinatewise
uniqueness of `08:1004--1005` (`huniq`), the frontier-pair clause of `08:934--935`
(`hpair`) and the frozen "one unsplit witness, whose `B_cap + 1` certificate requires
`kappa_v >= 2`" (`htwo`).  All three stay named hypotheses; nothing here upgrades
that bar.  General. -/
theorem denseWeightedFrontier_of_uniqueness {ι Coord : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Coord] {r b w : ℕ}
    (arr : Coord → FrontierArrival ι) (route : ι → List Bool)
    (iso : ι → Prop) [DecidablePred iso]
    (hpf : PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r)
    (hselected : 2 ^ r ≤ Fintype.card Coord + b)
    (hwitness : w ≤ witnessCount arr + b)
    (hgap : 4 * b < w)
    (huniq : ∀ v ∈ isolationNodes iso, (arrivalsAt arr v).card ≤ 1)
    (hpair : ∀ (α : Coord) (v u : ι), arr α = FrontierArrival.split v u → v ≠ u)
    (htwo : ∀ v ∈ isolationNodes iso,
      0 < zMass arr v → 2 ≤ stoppingCapacity r (route v).length) :
    ∃ v ∈ aliceNodes iso,
      3 * stoppingCapacity r (route v).length ≤ 4 * hMass arr v ∧
        stoppingCapacity r (route v).length < hMass arr v + zMass arr v :=
  denseWeightedFrontier arr route iso hpf hdepth hselected hwitness hgap
    (fun v hv => isolationNode_capacity_of_uniqueness arr v (huniq v hv) hpair (htwo v hv))

/-- **`lem:dense-weighted-frontier` at the banked selected branch.**  The two
conversions of `eq:selected-mass` (`08:1119--1123`) discharged from the banked
`DenseBranchSelection`: `hselected` from `card_selectedGood` (the untruncated
`|H| + b = q_2`, so "for the first conversion, use `b = |B_{j_*}| <= q_2`"), and
`hwitness` from `card_selectedWitness_ge` (the frozen "removing at most `b`
coordinates from `U_{j_*}`", so "for the second, use `b < w`").  `hwidth` is the
frozen `q_2 = 2^r` of `08:949` at the banked convention `q_2 = |Coord|`.

`hwitnessSet` is the one further named hypothesis: that the arrival function's
witness coordinates are exactly the frozen `W = U_{j_*} \ B_{j_*}` of `08:731`.  It is
a statement about the routed data that the banked bookkeeping does not fix, and it is
a binder, never a field.  General in `U`, `B`, `r`, the routes, the arrivals and the
isolation predicate. -/
theorem denseWeightedFrontier_at_selected_branch {ι Coord : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype Coord] [DecidableEq Coord] {r : ℕ} (U B : Finset Coord)
    (arr : {α // α ∈ selectedGood B} → FrontierArrival ι) (route : ι → List Bool)
    (iso : ι → Prop) [DecidablePred iso]
    (hpf : PrefixFreeFrontier route)
    (hdepth : ∀ v, (route v).length ≤ r)
    (hwidth : 2 ^ r = Fintype.card Coord)
    (hwitnessSet : witnessCount arr = (selectedWitness U B).card)
    (hgap : 4 * B.card < U.card)
    (hisocap : ∀ v ∈ isolationNodes iso,
      hMass arr v + zMass arr v ≤ stoppingCapacity r (route v).length) :
    ∃ v ∈ aliceNodes iso,
      3 * stoppingCapacity r (route v).length ≤ 4 * hMass arr v ∧
        stoppingCapacity r (route v).length < hMass arr v + zMass arr v := by
  refine denseWeightedFrontier arr route iso hpf hdepth ?_ ?_ hgap hisocap
  · have hcoe : Fintype.card {α // α ∈ selectedGood B} = (selectedGood B).card :=
      Fintype.card_coe _
    have hsel := card_selectedGood B
    omega
  · have hU := card_selectedWitness_ge U B
    omega

/-! ## §6  Candidate B (rejected): the datum as a record of its own hypotheses

Recorded as race evidence with the disposition of coverage limit 8. -/

/-- **Candidate B.**  The weighted-frontier datum as a record whose fields are the
classes, the three per-node functions, the six counts and every line of
`eq:abstract-weighted-frontier-input`.  Rejected: `split_le` restates a telescope the
frozen text itself derives (`08:1118`), the record forgets which arrival function
produced `H0` and `S`, and the record-form theorem is a projection of Candidate A. -/
structure WeightedFrontierInput (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The Alice class `V_A`. -/
  alice : Finset ι
  /-- The coordinate-isolation class `V_I`. -/
  iso : Finset ι
  /-- The alleged residual capacities `kappa_v`. -/
  cap : ι → ℕ
  /-- The alleged template masses `h_v`. -/
  h : ι → ℕ
  /-- The alleged witness masses `z_v`. -/
  z : ι → ℕ
  /-- The alleged width `q`. -/
  width : ℕ
  /-- The alleged good-coordinate count `H_0`. -/
  H0 : ℕ
  /-- The alleged witness count `W_0`. -/
  W0 : ℕ
  /-- The alleged split count `S`. -/
  S : ℕ
  /-- The alleged defect size `b`. -/
  defect : ℕ
  /-- The alleged branch witness supply `w`. -/
  wit : ℕ
  /-- Exhaustiveness of the two classes. -/
  cover : alice ∪ iso = Finset.univ
  /-- `1 <= kappa_v`. -/
  cap_pos : ∀ v, 1 ≤ cap v
  /-- `0 <= z_v <= h_v`. -/
  z_le_h : ∀ v, z v ≤ h v
  /-- `S <= W_0` -- the redundant field. -/
  split_le : S ≤ W0
  /-- `sum_v h_v = H_0 + S`. -/
  conservation_h : ∑ v, h v = H0 + S
  /-- `sum_v z_v + S = W_0`. -/
  conservation_z : (∑ v, z v) + S = W0
  /-- `sum_v kappa_v <= q`. -/
  kraft : ∑ v, cap v ≤ width
  /-- `q <= H_0 + b`. -/
  selected_good : width ≤ H0 + defect
  /-- `w <= W_0 + b`. -/
  selected_witness : wit ≤ W0 + defect
  /-- `4b < w`. -/
  gap : 4 * defect < wit
  /-- `h_v + z_v <= kappa_v` on `V_I`. -/
  isolation : ∀ v ∈ iso, h v + z v ≤ cap v

/-- The two-node datum of the legal instance, packaged as Candidate B: capacities
`4, 4`, template masses `5, 4`, witness masses `4, 0`, at `q = 8`, `H_0 = 8`,
`W_0 = 5`, `S = 1`, `b = 1`, `w = 6`. -/
def probeInput : WeightedFrontierInput (Fin 2) where
  alice := {0}
  iso := {1}
  cap := ![4, 4]
  h := ![5, 4]
  z := ![4, 0]
  width := 8
  H0 := 8
  W0 := 5
  S := 1
  defect := 1
  wit := 6
  cover := by decide
  cap_pos := by decide
  z_le_h := by decide
  split_le := by decide
  conservation_h := by decide
  conservation_z := by decide
  kraft := by decide
  selected_good := by decide
  selected_witness := by decide
  gap := by decide
  isolation := by decide

/-- The same per-node data with the counts shifted: `H_0 = 9`, `S = 0`, `W_0 = 4`,
`w = 5`.  Every field still holds, which is Candidate B's faithfulness failure. -/
def probeInput' : WeightedFrontierInput (Fin 2) where
  alice := {0}
  iso := {1}
  cap := ![4, 4]
  h := ![5, 4]
  z := ![4, 0]
  width := 8
  H0 := 9
  W0 := 4
  S := 0
  defect := 1
  wit := 5
  cover := by decide
  cap_pos := by decide
  z_le_h := by decide
  split_le := by decide
  conservation_h := by decide
  conservation_z := by decide
  kraft := by decide
  selected_good := by decide
  selected_witness := by decide
  gap := by decide
  isolation := by decide

/-- **Candidate B, aux 1.**  The record is inhabited at legal values, so its defects
below are not artefacts of an empty type. -/
theorem weightedFrontierInput_nonempty : Nonempty (WeightedFrontierInput (Fin 2)) :=
  ⟨probeInput⟩

/-- **Candidate B, aux 2 (the redundant field).**  `split_le` restates a derived
telescope: `S <= W_0` follows from `conservation_z` alone, exactly as the frozen text
derives it at `08:1118` ("its third equality also gives `S <= |W|`").  A bundle field
that re-asserts a consequence of another field is precisely what the mechanical
contract forbids.  General in the record. -/
theorem weightedFrontierInput_split_le_is_redundant {ι : Type*} [Fintype ι]
    [DecidableEq ι] (c : WeightedFrontierInput ι) : c.S ≤ c.W0 := by
  have h := c.conservation_z
  omega

/-- **Candidate B, aux 3 (the faithfulness failure).**  Two inhabitants with
*identical* classes, capacities and both masses, but different `H0` and `S`.  In the
frozen instantiation `H_0 = |H|` and `S` are both **determined** by the arrival
function (`sum_hMass_eq`), so the record forgets data the frozen datum knows and can
be inhabited at counts no routing produces. -/
theorem weightedFrontierInput_counts_float :
    probeInput.alice = probeInput'.alice ∧ probeInput.iso = probeInput'.iso
      ∧ probeInput.cap = probeInput'.cap ∧ probeInput.h = probeInput'.h
      ∧ probeInput.z = probeInput'.z
      ∧ probeInput.H0 ≠ probeInput'.H0 ∧ probeInput.S ≠ probeInput'.S :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- **Candidate B, aux 4 (the record adds nothing).**  The record-form theorem is
obtained by projecting the record's fields into Candidate A, so `WeightedFrontierInput`
is a strictly lossier spelling of the same binder list and carries no mathematics of
its own.  General in the record. -/
theorem weightedFrontierInput_is_a_repackaging {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : WeightedFrontierInput ι) :
    ∃ v ∈ c.alice, 3 * c.cap v ≤ 4 * c.h v ∧ c.cap v < c.h v + c.z v :=
  abstractWeightedFrontier_core c.alice c.iso c.cap c.h c.z c.cover c.z_le_h
    c.conservation_h c.conservation_z c.kraft c.selected_good c.selected_witness
    c.gap c.isolation

/-! ## §7  Non-vacuity, statement poles and consistency probes

Both headlines are universally quantified implications with existential conclusions.
An unsatisfiable premise bundle would make every consumer vacuous while compiling
green, and a conclusion satisfied by a fixed node would make the existential empty of
content.  Both are probed here.  No parameter schedule may be read out of any witness
below. -/

/-- The abstract legal instance's capacities: a two-node frontier at suffix depths
`1, 1` below width `q_2 = 2^3 = 8`, so `kappa = 4, 4` and Kraft is attained. -/
def probeKappa : Fin 2 → ℕ := ![4, 4]

/-- The abstract legal instance's template masses. -/
def probeH : Fin 2 → ℕ := ![5, 4]

/-- The abstract legal instance's witness masses. -/
def probeZ : Fin 2 → ℕ := ![4, 0]

/-- **Tier 2 -- the legal instance of `lem:abstract-weighted-frontier`, and the
hypothesis-consistency readout of the abstract half.**  At `q = 8`, `H_0 = 8`,
`W_0 = 5`, `S = 1`, `b = 1`, `w = 6`:

* the two classes `{0}` and `{1}` are disjoint and exhaustive;
* `1 <= kappa_v` and `0 <= z_v <= h_v` hold pointwise, and `S <= W_0`;
* both conservation equalities hold, Kraft is **attained** (`sum_v kappa_v = 8 = q`),
  and `eq:isolation-capacity` is **attained** at the isolation node
  (`h_1 + z_1 = 4 = kappa_1`);
* the frozen side conditions hold simultaneously: `q <= H_0 + b` (`8 <= 9`),
  `w <= W_0 + b` (`6 <= 6`) and `4b < w` (`4 < 6`);
* and the conclusion is witnessed at the Alice node `0`
  (`3 kappa_0 = 12 <= 20 = 4 h_0`, `kappa_0 = 4 < 9 = h_0 + z_0`).

So the entire premise bundle is simultaneously satisfiable at values the frozen text
permits, and no `False` follows from it.  Tier 2, not a schedule instance: `q = 2^3`
does not satisfy the full `eq:stage2-structural-gates` (`06:832--847`), which forces
`q_2 >= 6144`; it does not need to, since every statement instantiated here is general
in all six counts. -/
theorem weightedFrontier_legal_instance :
    Disjoint ({0} : Finset (Fin 2)) ({1} : Finset (Fin 2))
      ∧ ({0} : Finset (Fin 2)) ∪ ({1} : Finset (Fin 2)) = Finset.univ
      ∧ (∀ v, 1 ≤ probeKappa v)
      ∧ (∀ v, probeZ v ≤ probeH v)
      ∧ (1 : ℕ) ≤ 5
      ∧ (∑ v, probeH v) = 8 + 1
      ∧ (∑ v, probeZ v) + 1 = 5
      ∧ (∑ v, probeKappa v) = 8
      ∧ (8 : ℕ) ≤ 8 + 1
      ∧ (6 : ℕ) ≤ 5 + 1
      ∧ 4 * 1 < (6 : ℕ)
      ∧ (∀ v ∈ ({1} : Finset (Fin 2)), probeH v + probeZ v ≤ probeKappa v)
      ∧ probeH 1 + probeZ 1 = probeKappa 1
      ∧ (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
      ∧ 3 * probeKappa 0 ≤ 4 * probeH 0
      ∧ probeKappa 0 < probeH 0 + probeZ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- **Tier 2 -- `lem:abstract-weighted-frontier` applied at the legal instance.**  The
frozen principle is asserted at a real point: every hypothesis of
`abstractWeightedFrontier` is discharged at the instance above and a forced Alice node
is produced.  Since the bundle is inhabited, no `False` follows from it, and the
lemma is not quantified over an empty regime. -/
theorem weightedFrontier_at_probe :
    ∃ v ∈ ({0} : Finset (Fin 2)),
      3 * probeKappa v ≤ 4 * probeH v ∧ probeKappa v < probeH v + probeZ v :=
  abstractWeightedFrontier (q := 8) (H₀ := 8) (W₀ := 5) (S := 1) (b := 1) (w := 6)
    ({0} : Finset (Fin 2)) ({1} : Finset (Fin 2)) probeKappa probeH probeZ
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Statement pole (the deliverable is not witnessed by a fixed Alice node).**
A three-node datum satisfying **every** hypothesis of `abstractWeightedFrontier` in
which the Alice node `2` fails **both** conclusions.  So the content of the frozen
existential is that the counted data *force* some node, not that `V_A` is nonempty:
`abstractWeightedFrontier` cannot be strengthened to "every Alice node", and no fixed
index can be exhibited in its place. -/
theorem weightedFrontier_not_at_every_alice_node :
    ∃ (alice iso : Finset (Fin 3)) (κ h z : Fin 3 → ℕ),
      Disjoint alice iso
        ∧ alice ∪ iso = Finset.univ
        ∧ (∀ v, 1 ≤ κ v)
        ∧ (∀ v, z v ≤ h v)
        ∧ (1 : ℕ) ≤ 5
        ∧ (∑ v, h v) = 8 + 1
        ∧ (∑ v, z v) + 1 = 5
        ∧ (∑ v, κ v) ≤ 9
        ∧ (9 : ℕ) ≤ 8 + 1
        ∧ (6 : ℕ) ≤ 5 + 1
        ∧ 4 * 1 < (6 : ℕ)
        ∧ (∀ v ∈ iso, h v + z v ≤ κ v)
        ∧ (2 : Fin 3) ∈ alice
        ∧ ¬ (3 * κ 2 ≤ 4 * h 2)
        ∧ ¬ (κ 2 < h 2 + z 2) := by
  refine ⟨{0, 2}, {1}, ![4, 4, 1], ![5, 4, 0], ![4, 0, 0], ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- **Statement pole (`4b < w` is load-bearing).**  A one-node datum satisfying every
hypothesis of `abstractWeightedFrontier` **except** the selected-branch gap, whose
single Alice node fails the positive-excess conclusion.  So `hgap` -- the frozen
`lem:dense-select-branch` -- cannot be dropped, and the conclusion is not an artefact
of the conservation equalities alone. -/
theorem weightedFrontier_pole_needs_gap :
    ∃ (alice iso : Finset (Fin 1)) (κ h z : Fin 1 → ℕ),
      Disjoint alice iso
        ∧ alice ∪ iso = Finset.univ
        ∧ (∀ v, 1 ≤ κ v)
        ∧ (∀ v, z v ≤ h v)
        ∧ (0 : ℕ) ≤ 0
        ∧ (∑ v, h v) = 1 + 0
        ∧ (∑ v, z v) + 0 = 0
        ∧ (∑ v, κ v) ≤ 1
        ∧ (1 : ℕ) ≤ 1 + 0
        ∧ (0 : ℕ) ≤ 0 + 0
        ∧ ¬ (4 * 0 < (0 : ℕ))
        ∧ (∀ v ∈ iso, h v + z v ≤ κ v)
        ∧ ¬ (∃ v ∈ alice, 3 * κ v ≤ 4 * h v ∧ κ v < h v + z v) := by
  refine ⟨{0}, ∅, ![1], ![1], ![0], ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Statement pole (`eq:isolation-capacity` is load-bearing).**  A one-node datum
satisfying every hypothesis of `abstractWeightedFrontier` **except** the isolation
hypothesis, with an empty Alice class: all the mass hides at the isolation node and no
Alice node exists at all.  So the frozen last line of
`eq:abstract-weighted-frontier-input` -- the line carrying the `08:1036` rendering
defect -- is genuinely consumed, and reading it as anything weaker would break the
lemma. -/
theorem weightedFrontier_pole_needs_isolation :
    ∃ (alice iso : Finset (Fin 1)) (κ h z : Fin 1 → ℕ),
      Disjoint alice iso
        ∧ alice ∪ iso = Finset.univ
        ∧ (∀ v, 1 ≤ κ v)
        ∧ (∀ v, z v ≤ h v)
        ∧ (0 : ℕ) ≤ 4
        ∧ (∑ v, h v) = 4 + 0
        ∧ (∑ v, z v) + 0 = 4
        ∧ (∑ v, κ v) ≤ 4
        ∧ (4 : ℕ) ≤ 4 + 1
        ∧ (5 : ℕ) ≤ 4 + 1
        ∧ 4 * 1 < (5 : ℕ)
        ∧ ¬ (∀ v ∈ iso, h v + z v ≤ κ v)
        ∧ ¬ (∃ v ∈ alice, 3 * κ v ≤ 4 * h v ∧ κ v < h v + z v) := by
  refine ⟨∅, {0}, ![4], ![4], ![4], ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The frontier of the dense legal instance: two prefix-free stopping nodes at suffix
depth `1` below a width `q_2 = 2^3 = 8`, so `kappa = 4, 4`. -/
def probeRoute : Fin 2 → List Bool := ![[false], [true]]

/-- The isolation predicate of the dense legal instance: node `1` is the
coordinate-isolation node, node `0` the Alice node. -/
def probeIso : Fin 2 → Prop := fun v => v = 1

instance decidableProbeIso : DecidablePred probeIso :=
  fun v => (inferInstance : Decidable (v = 1))

/-- The arrivals of the dense legal instance: eight good coordinates, five of them
witnesses, one of those split.  All three frozen outcomes occur. -/
def probeArr : Fin 8 → FrontierArrival (Fin 2) :=
  ![FrontierArrival.unsplit 0, FrontierArrival.unsplit 0, FrontierArrival.unsplit 0,
    FrontierArrival.unsplit 0, FrontierArrival.ordinary 1, FrontierArrival.ordinary 1,
    FrontierArrival.ordinary 1, FrontierArrival.split 0 1]

/-- **Aux (the dense probe frontier is prefix-free).** -/
theorem probeRoute_prefixFree : PrefixFreeFrontier probeRoute := by
  intro v u hvu hpre
  obtain ⟨t, ht⟩ := hpre
  fin_cases v <;> fin_cases u <;> simp [probeRoute] at ht hvu

/-- **Tier 2 -- the legal instance of `lem:dense-weighted-frontier`.**  At `r = 3`
(so `q_2 = 8`), `b = 1`, `w = 6`, on the two-node frontier above, with eight good
coordinates, `|W| = 5` witnesses and `S = 1` split:

* the frontier is prefix-free at suffix depths at most `r`, and Kraft is **attained**;
* the two frozen classes are `V_I = {1}` and `V_A = {0}`, exhaustive and disjoint;
* the conservation equalities hold at those counts, with all three arrival kinds
  occurring and both masses nonzero somewhere;
* `eq:isolation-capacity` holds at the isolation node, **with equality**;
* the two conversions of `eq:selected-mass` and the selected-branch gap hold
  simultaneously: `q_2 <= |H| + b` (`8 <= 9`), `w <= |W| + b` (`6 <= 6`) and
  `4b < w` (`4 < 6`).

So the dense premise bundle is simultaneously satisfiable at values the frozen text
permits.  Tier 2, not a schedule instance: `q_2 = 8` does not satisfy the full
`eq:stage2-structural-gates`, which forces `q_2 >= 6144`, and no parameter value may
be read out of it. -/
theorem denseWeightedFrontier_legal_instance :
    PrefixFreeFrontier probeRoute
      ∧ (∀ v, (probeRoute v).length ≤ 3)
      ∧ (∑ v, stoppingCapacity 3 (probeRoute v).length) = 2 ^ 3
      ∧ Fintype.card (Fin 8) = 8
      ∧ witnessCount probeArr = 5
      ∧ splitCount probeArr = 1
      ∧ isolationNodes probeIso = {1}
      ∧ aliceNodes probeIso = {0}
      ∧ hMass probeArr 0 = 5 ∧ zMass probeArr 0 = 4
      ∧ hMass probeArr 1 = 4 ∧ zMass probeArr 1 = 0
      ∧ (2 ^ 3 : ℕ) ≤ Fintype.card (Fin 8) + 1
      ∧ (6 : ℕ) ≤ witnessCount probeArr + 1
      ∧ 4 * 1 < (6 : ℕ)
      ∧ (∀ v ∈ isolationNodes probeIso,
          hMass probeArr v + zMass probeArr v
            ≤ stoppingCapacity 3 (probeRoute v).length)
      ∧ hMass probeArr 1 + zMass probeArr 1 = stoppingCapacity 3 (probeRoute 1).length := by
  refine ⟨probeRoute_prefixFree, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **Tier 2 -- `lem:dense-weighted-frontier` applied at the legal instance.**  The
headline is asserted at a real point: the hypotheses are discharged from the instance
above and a forced Alice node is produced.  Without this readout the dense lemma could
be quantified over a bundle its own premises force empty. -/
theorem denseWeightedFrontier_at_probe :
    ∃ v ∈ aliceNodes probeIso,
      3 * stoppingCapacity 3 (probeRoute v).length ≤ 4 * hMass probeArr v ∧
        stoppingCapacity 3 (probeRoute v).length < hMass probeArr v + zMass probeArr v := by
  refine denseWeightedFrontier (b := 1) (w := 6) probeArr probeRoute probeIso
    probeRoute_prefixFree (by decide) (by decide) (by decide) (by decide) (by decide)

end EthInapproximability.ParameterizedNP.DenseWeightedFrontier
