import EthInapproximability.ParameterizedNP.DenseRoutingThresholds

/-!
# Parameterized NP route: the fifth block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 878--944** --
  `lem:dense-routing`, the support-routing invariant, with its frozen proof.
  The anchors traced here, in the order the block prints them:
  * `lem:dense-routing` (label 879, statement 878--894): "Tokens can be routed
    through every Bob query of `P_*` so that an ordinary token present at suffix
    depth `d` has quotient support at least `ceil(lambda_d |C_1|)`, and an
    unsplit witness object has support density at least
    `p_root - lambda_0 + lambda_d`.  After it has passed through at least one Bob
    query without splitting, this last inequality is strict.  At every protocol
    node there is at most one routed object carrying any fixed Stage-2
    coordinate.  If a witness is never split, its total support loss is strictly
    less than `lambda_0`";
  * 897--902, the base case and the ordinary step: "At depth zero the witness
    bound is exactly the root certificate from `lem:dense-local-certificates`;
    equality may occur", and "Route an ordinary token to a child containing at
    least half of its current quotient support.  Since
    `lambda_{d+1} = lambda_d/2`, the ordinary invariant is preserved";
  * 904--911, the split rule at `L_{d+1} = ceil(lambda_{d+1}|C_1|)`: "If both
    assigned children contain at least `L_{d+1}` quotient columns, split the
    witness and create one ordinary token in each child.  Otherwise one child has
    at most `L_{d+1} - 1` columns; route the whole witness to its complement";
  * 913--920, the two strictness inputs: `p_root > lambda_0` at the root by
    `eq:routing-slack`, and `p_root - lambda_0 + lambda_d > lambda_d` later;
  * 921--931, the integral estimate and the density recurrence: "the current
    support density is strictly greater than `lambda_d = 2 lambda_{d+1}`.  Its
    integral support size is therefore at least `2 L_{d+1} - 1`.  The complement
    of a side of size at most `L_{d+1} - 1` still has at least `L_{d+1}` columns,
    and the discarded fraction is strictly below `lambda_{d+1}`", closing with
    `lambda_d - lambda_{d+1} = lambda_{d+1}`;
  * 933--935, the uniqueness clause: "There is one object per coordinate
    initially.  A routed object either chooses one child or splits into objects
    in two incomparable children, and protocol branches never merge";
  * 937--944, the total-loss clause: `sum_{d>=0} lambda_{d+1} = lambda_0`, hence
    "a witness routed whole forever loses less than `lambda_0` support and, by
    `eq:routing-slack` and `lem:dense-local-certificates`, retains its bonus
    certificate";
  * 785--789, the Bob-query law this block's assignment structure transcribes
    ("Every later Bob query partitions physical columns.  Within each
    `alpha`-fibre, an underlying pair `(alpha, gamma)` represented in both
    physical children may be assigned to either child; a pair represented in only
    one child is forced there.  These assignments can be made independently for
    different `alpha`-fibres because those fibres are disjoint").
* **Deliberately NOT claimed (the next block's territory).**  The weighted
  stopping count of `sec:dense-weighted-count` (`08:946--954`) and
  `lem:dense-no-leaf` (`08:955--979`) have **no** declaration here, and nothing
  from either is used: no positive token is defined, no stopping rule is stated,
  and nothing here says a token stops at coordinate isolation, before its first
  Alice query, or at suffix depth at most `r`.  Where a later block needs the
  routing facts, it must cite the named results below; where it needs the
  no-leaf facts, those remain **named hypotheses** for it to carry, exactly as
  the deeper inherited certificates are carried here.
* **Predecessor anchors (the handoffs consumed by pin):**
  * `08:811--876` through the banked
    `EthInapproximability.ParameterizedNP.DenseRoutingThresholds`, which supplies
    the threshold sequence `lambdaAt` with `lambdaAt_zero`, `lambdaAt_succ`,
    `lambdaAt_nonneg`, `lambdaAt_antitone`, `lambdaAt_le_lambdaZero`,
    `sum_lambdaAt_succ` and `lambdaAt_nondegenerate`, and the two node-indexed
    certificate readouts `witnessDensity_meets_capacity_columns` and
    `witnessToken_is_Bcap_succ_hard` that `08:941--944` consumes;
  * `08:764--810` through `DenseBranchSelection`, which supplies
    `quotientSupport`, `quotientDensity`, `mem_quotientSupport`,
    `quotientSupport_mono`, `quotientSupport_union`,
    `quotientSupport_fibres_disjoint`, `selectedWitness`, and the routing
    constants `pRoot`, `lambdaZero`, `epsOne`, `omegaRoute` with `pRoot_eq`,
    `omegaRoute_eq`, `lambdaZero_nonneg` and the predicate `RoutingSlack`;
  * `07:617--623` through `RawStageFour.localCapacityGap_le_member`, reached
    only through the banked `witnessToken_is_Bcap_succ_hard`;
  * `08:401` through `DenseStageFourOpening.rhoLoc`, reached only through the
    banked `pRoot`.
  **None of those handoffs is restated here.**
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design and appears
  in no hypothesis of any statement below: this block never touches the
  upper-fibre estimate.  The inherited odd-copy capacity inequality
  `eq:local-capacity-gap` enters `unsplitWitness_retains_bonus` as the named
  hypothesis `hgap`, and the diagonal-scaffold representative choice of
  `08:864--871` enters as the named hypothesis `hwrepr`, **node-indexed and
  density-gated** in exactly the shape the banked `denseLocalCertificates` fixed
  after the `cc-t2l-r1` repair -- which is what made the frozen sentence "retains
  its bonus certificate" (`08:941--944`) formalizable at all, since the
  certificate must be the one the node's own surviving columns cut out.  The
  Stage-1 certificate `eq:stage1-robust-certificate` and the representative
  choice `hrepr` of `08:854--860` are **not** hypotheses here: this block makes
  no ordinary-token hardness claim, and re-stating them would assert more than
  it uses.  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP
  balanced-family axiom -- is **not** imported, and no declaration here is in its
  dependency graph.
* **New vendored-gap work.**  None.  The routing step is `Finset` cardinality
  arithmetic against a real-valued ceiling, the density recurrence is `linarith`
  over the banked geometric sequence, and the uniqueness clause is a statement
  about `Option`-valued families and the prefix order on `List Bool`.
* Proof status: **new** for the assignment structure, the canonical assignment,
  both routing steps, the density recurrence, the frozen lemma, the total-loss
  clause, the retained-bonus corollary and the uniqueness readouts; **inherited
  by pin** for the thresholds, the quotient-support layer, the routing constants
  and both node-indexed certificate readouts.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, the proof outline
of `thm:paper-protected-stage4`.

**This module claims no reader item, deliberately rather than by omission.**  The
41-page reader artifact condenses the whole of `lem:dense-routing` into the single
clause "Quotient-support routing follows every Bob query" (reader line 259), and
that clause was **already assigned** -- to `DenseBranchSelection`'s
`quotientSupport`/`quotientDensity` battery -- in tranche `cc-t2k`.  The
neighbouring clauses are likewise taken: reader lines 253--254 and 258--259
("while the residual protocol is routed through arbitrary later queries") by
`DenseBranchSelection`, reader lines 256--258 ("The Stage--2 lower bounds are
applied to quotient supports, using the same physical balanced family as in
Stage~2") by `DenseRoutingThresholds`, and the remainder of line 259 onwards
("the weighted stopping count records ...") belongs to the next block.  A reader
item may not be assigned twice, and one may not be invented, so this module
claims none and names the prior assignment instead.

The only other reader mentions of this construction are
`01-introduction.tex:100--101` ("It routes arbitrary later queries by quotient
support and a weighted frontier before assigning source witnesses to a surviving
branch") and `02-preliminaries.tex:562--564` ("it handles every later query in
arbitrary order by quotient-support routing and the weighted frontier").  Both
are prose about the method rather than statements of the invariant -- neither
gives the ordinary bound `ceil(lambda_d |C_1|)`, the witness bound
`p_root - lambda_0 + lambda_d`, the split rule, the uniqueness clause or the
total-loss clause -- so neither is cited as a counterpart statement.  This is a
recorded coverage limit of the reader artifact, not of the trace: the proof
source for every declaration below is the frozen autoformalization anchor named
above.

## Candidate encodings of the routed object (`k = 2`, raced)

The novel object of this tranche is the routed object crossing one Bob query.

**Candidate A (landed, SS2).**  Make the novelty the *assignment*, not the
object: `BobRouting rep S₀ S₁ alpha T` carries the two assigned column sets
together with the frozen assignment law of `08:785--789` -- each assigned set is
represented by its own physical child, and together they exhaust the routed
object's current support `T`.  The routed object itself is a plain `Finset` of
quotient columns, its depth is a plain `Nat`, and every bound of `08:880--893` is
a **theorem about** those data rather than a field.  Nothing is stored: no
certificate, no invariant, no hardness claim.  The frozen freedom "a pair
represented in both physical children may be assigned to either child" is the
*absence* of a determination rule, and `bobRouting_assignment_is_a_choice`
exhibits two legal assignments of the same duplicated value; the frozen
constraint "a pair represented in only one child is forced there" is not a field
either -- it is the **derived** `BobRouting.forced_left` / `forced_right`, so no
bundle field restates a telescope its siblings already imply.  10 aux lemmas
proved, and the structure is inhabited *constructively* by `canonicalRouting`.

**Candidate B (rejected, SS10).**  Take the routed object as a record carrying
its own invariant: a depth, a support, and the field
`routingFloor Gamma q2 b1 depth <= support.card`.  3 aux lemmas proved, but it
loses decisively on two counts.  First, it puts the frozen *conclusion* of
`lem:dense-routing` (`08:880--884`) into constructor data, which the mechanical
contract's no-conclusion-in-constructor-data rule forbids outright -- and it is
the exact shape that would make the routing theorem a tautology, since the
conclusion would be available by projection.  Second, it is unfaithful even as
data: `routedToken_needs_no_node` exhibits an inhabitant whose support is not
contained in **any** node's quotient support, so the record describes an object
routed through no protocol at all.  That is the `cc-t2l-r1` defect in a new
place -- node-independence -- and the race is decided on faithfulness, not
length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the routed object's support density, general (5):
  `supportDensity_nonneg`, `supportDensity_le_one`, `supportDensity_mono`,
  `supportDensity_empty`, `supportDensity_quotientSupport` (the round trip
  against the banked `quotientDensity`).
* `A2` the frozen witness bound `p_root - lambda_0 + lambda_d`, general (6):
  `routingBound_zero`, `routingBound_succ`, `routingBound_antitone`,
  `lambdaAt_lt_routingBound`, `omegaRoute_lt_routingBound`,
  `lambdaZero_lt_pRoot`.
* `A3` the integral floor `L_d = ceil(lambda_d |C_1|)`, general (4):
  `routingFloor_le`, `routingFloor_lt_add_one`, `routingFloor_antitone`,
  `routingFloor_succ_le_of_two_mul`.
* `A4` the Bob-query assignment, general (10): `BobRouting.left_subset`,
  `BobRouting.right_subset`, `BobRouting.card_parent_le`,
  `BobRouting.forced_left`, `BobRouting.forced_right`, `BobRouting.symm_left`,
  `BobRouting.symm_right`, `BobRouting.symm_symm`, `bobRouting_nonempty`,
  `exists_child_two_mul`.
* `A5` the ordinary-token step (`08:900--902`) (1): `ordinaryToken_step`.
* `A6` the witness split rule (`08:904--911`, `08:921--925`) (3):
  `witnessSupport_card_ge`, `witnessRoute_whole_card`, `witnessRoute_loss_lt`.
* `A7` the density recurrence (`08:925--931`) (1): `routing_density_step`.
* `A8` the frozen lemma (2): `denseRoutingInvariant`,
  `denseRoutingInvariant_exists`.
* `A9` the total loss and the retained bonus (`08:937--944`) (7):
  `lambdaZero_pos`, `routing_total_loss_le`, `routing_total_loss_lt`,
  `routing_total_loss_lt_pRoot`, `unsplitWitness_density_gt_omega`,
  `unsplitWitness_node_density_gt_omega`, `unsplitWitness_retains_bonus`.
* `A10` the uniqueness clause (`08:890--891`, `08:933--935`) (9):
  `routedFamily_unique`, `rootFamily_eq_some`, `rootFamily_eq_none`,
  `routeLeft_length`, `routeRight_length`, `routeChildren_ne`,
  `routeLeft_not_prefix_routeRight`, `routeRight_not_prefix_routeLeft`,
  `routeChildren_incomparable`.
* Candidate B's own battery (3): `routedToken_nonempty`,
  `routedToken_support_card_ge`, `routedToken_needs_no_node`.

That is **48 battery entries proved plus 3 for the rejected candidate**, with
`0` unproved, alongside **three statement poles**
(`bobRouting_pole_left_child_not_enough`, `ordinaryStep_pole_side_not_fixed`,
`witnessSupport_pole_below_threshold`) and **four non-vacuity / consistency
readouts** -- one for every definition group and for the headline's premise
bundle.  The module has **69** source declarations in all: 11 definitions
(`supportDensity`, `routingBound`, `routingFloor`, `BobRouting`,
`BobRouting.symm`, `canonicalRouting`, `RoutedFamily`, `rootFamily`,
`routeLeft`, `routeRight`, `RoutedToken`) and 58 proved results (48 battery
entries, 3 for the rejected candidate, 3 statement poles, 4 readouts):

* `routingBound_nondegenerate`, the witness bound inhabited **symbolically in
  `q_2`**: for every `q_2 > 0` there is a certified Stage-1 robustness depth at
  which `eq:routing-slack` holds and every `routingBound q_2 b_1 d` lies strictly
  between `omega` and `1`, proved from the banked `lambdaAt_nondegenerate` with
  no tower evaluated, so this reaches the frozen widths `q_2 >= 6144` that no
  evaluable literal reaches;
* `denseRoutingInvariant_hypotheses_consistent`, the **joint** readout: the
  headline's entire premise bundle inhabited at legal values (`q_2 = 2`,
  `b_1 = 5`, `|C_1| = 32`, so `lambda_0 = 1/8`, `L_0 = 4`, `L_1 = 2`,
  `RoutingSlack` holding) by a genuine Bob query -- `S_0` and `S_1` overlap, so
  the assignment is a real choice -- at which the root bound holds with
  **equality** (`routingBound 2 5 0 = supportDensity T = 3/4`, the frozen
  "equality may occur"), the split branch **fails** (`|right| = 1 < L_1 = 2`),
  the route-whole branch therefore **fires** (`|left| = 23 >= L_1`), and its
  strict conclusion `routingBound 2 5 1 = 11/16 < 23/32 = supportDensity left`
  and the bonus gate `omega < supportDensity left` both hold.  Without it the
  witness clause could be quantified over a bundle its own premises force empty
  while the module compiled green;
* `bobRouting_assignment_is_a_choice`, the assignment layer inhabited **twice**
  over the same indices with different assigned sets, so `BobRouting` is not a
  subsingleton determined by `(rep, S_0, S_1, alpha, T)` and the frozen "may be
  assigned to either child" has content;
* `routedFamily_nondegenerate`, the uniqueness carrier inhabited with two
  distinct routed objects at two distinct coordinates and a third coordinate
  carrying none, so the `Option`-valued family is not the constant `none` (which
  would satisfy uniqueness vacuously).

## Honest scope and recorded coverage limits

1. **The routing choice, not the assignment, is what the disjunctions carry.**
   `denseRoutingInvariant` is stated **for every** legal assignment and produces
   a good child, which is strictly stronger than the frozen "Tokens can be routed
   ... so that"; `denseRoutingInvariant_exists` prints the frozen existential
   form, witnessed by `canonicalRouting`, so nothing is weakened by the
   strengthening.  *Why the trivial witness fails*: the degenerate assignment
   "everything to the left child" is **not legal** in general, because
   `left_represented` demands the left child physically represent every value it
   receives -- `bobRouting_pole_left_child_not_enough` exhibits a node whose
   routed support is not contained in the left child's quotient support at all,
   so the existential is not discharged by a fixed side.
2. **No protocol is constructed.**  A node is its surviving physical column set
   `S : Finset Phys`, exactly as in the banked quotient-support layer, and a Bob
   query is the pair `(S_0, S_1)` with `S_0 ∪ S_1 = S`.  Nothing here builds a
   protocol, evaluates one, or asserts that the residual protocol `P_*` has any
   particular query structure; the frozen `cost(P_*) <= D_2` of
   `eq:selected-upper-budget` is the banked `selectedResidual_cost_le` and is not
   restated.
3. **The uniqueness clause is structural, and says so.**  "At every protocol node
   there is at most one routed object carrying any fixed Stage-2 coordinate"
   (`08:890--891`) is represented by making a node's routed objects an
   `Option`-valued family `RoutedFamily`, so uniqueness is a property of the
   representation (`routedFamily_unique`) rather than a proved property of a
   constructed routing.  What the frozen proof actually argues -- "protocol
   branches never merge" (`08:935`) -- is proved as the incomparability of the
   two children of a suffix node in the prefix order
   (`routeChildren_incomparable`).  This module does **not** prove that the
   routing defined by the frozen rules preserves the representation across a
   query; that would need the protocol tree the block deliberately does not
   build, and a later tranche may not cite this module as having supplied it.
4. **The bonus certificate is transported, not established.**
   `unsplitWitness_retains_bonus` derives the frozen `08:941--944` conclusion
   from the invariant, `eq:routing-slack` and the banked node-indexed readouts;
   its two deep inputs stay named hypotheses (`hgap` for `eq:local-capacity-gap`,
   `hwrepr` for the density-gated diagonal scaffold of `08:864--871`).  The
   banked `RawStageFour.localCapacityGap_not_automatic` records why `hgap` is
   genuine inherited content, and the banked `witnessRepr_gate_nonvacuous`
   records why the gated `hwrepr` is not satisfied by never firing.  Nothing here
   inhabits either at a concrete matrix.
5. **The total-loss clause is finite-depth.**  `routing_total_loss_lt` proves
   `sum_{d < n} lambda_{d+1} < lambda_0` for every finite `n`, from the banked
   partial sum `lambda_0 (1 - 2^{-n})`; the frozen display `sum_{d>=0}
   lambda_{d+1} = lambda_0` (`08:938--940`) is the limit of that identity, and
   the strict inequality the proof uses is exactly the finite-depth statement
   proved here.  No infinite series is formed.
6. **`b_1`, `q_2`, `|C_1|` and the depth are binders, not values.**
   `routingFloor` takes the quotient carrier as an explicit type argument and
   `q_2`, `b_1`, `d` as explicit naturals; no parameter schedule may be read out
   of any witness below.  `denseRoutingInvariant_hypotheses_consistent` and the
   three poles are separating probes of the definitions at a deliberately small
   carrier (`|C_1| = 32`) and are **not** schedule instances.
7. **Candidate B is race evidence with a recorded disposition.**  `RoutedToken`
   is consumed by nothing and may not be used to re-encode the routed object of
   `08:878--894` without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseRoutingInvariant

open Finset
open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.StageThreeExactScale
open EthInapproximability.ParameterizedNP.RawStageFour
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseSourceOwners
open EthInapproximability.ParameterizedNP.DenseBranchSelection
open EthInapproximability.ParameterizedNP.DenseRoutingThresholds

/-! ## §1  The support density of a routed object, and the frozen witness bound -/

section Density

variable {Γ : Type*} [Fintype Γ]

/-- The support density of a routed object whose current support is `T`. -/
noncomputable def supportDensity (T : Finset Γ) : ℝ :=
  (T.card : ℝ) / (Fintype.card Γ : ℝ)

theorem supportDensity_nonneg (T : Finset Γ) : 0 ≤ supportDensity T := by
  unfold supportDensity
  positivity

theorem supportDensity_le_one (T : Finset Γ) (hΓ : 0 < Fintype.card Γ) :
    supportDensity T ≤ 1 := by
  have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hΓ
  rw [supportDensity, div_le_one hpos]
  exact_mod_cast Finset.card_le_univ T

theorem supportDensity_mono {T T' : Finset Γ} (h : T ⊆ T') :
    supportDensity T ≤ supportDensity T' := by
  have hcard : (T.card : ℝ) ≤ (T'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h
  have hnn : (0 : ℝ) ≤ ((Fintype.card Γ : ℝ))⁻¹ := by positivity
  simp only [supportDensity, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcard hnn

theorem supportDensity_empty : supportDensity (∅ : Finset Γ) = 0 := by
  simp [supportDensity]

theorem supportDensity_quotientSupport {Phys Coord : Type*} [DecidableEq Coord]
    [DecidableEq Γ] (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord) :
    supportDensity (quotientSupport rep S α) = quotientDensity rep S α := rfl

end Density

/-- The frozen witness bound `p_root - lambda_0 + lambda_d`. -/
noncomputable def routingBound (q₂ b₁ d : ℕ) : ℝ :=
  pRoot - lambdaZero q₂ b₁ + lambdaAt q₂ b₁ d

theorem routingBound_zero (q₂ b₁ : ℕ) : routingBound q₂ b₁ 0 = pRoot := by
  rw [routingBound, lambdaAt_zero]
  ring

theorem routingBound_succ (q₂ b₁ d : ℕ) :
    routingBound q₂ b₁ (d + 1) = routingBound q₂ b₁ d - lambdaAt q₂ b₁ (d + 1) := by
  simp only [routingBound, lambdaAt_succ]
  ring

theorem routingBound_antitone (q₂ b₁ : ℕ) {d d' : ℕ} (h : d ≤ d') :
    routingBound q₂ b₁ d' ≤ routingBound q₂ b₁ d := by
  have := lambdaAt_antitone q₂ b₁ h
  simp only [routingBound]
  linarith

theorem lambdaAt_lt_routingBound (q₂ b₁ d : ℕ) (hslack : RoutingSlack q₂ b₁) :
    lambdaAt q₂ b₁ d < routingBound q₂ b₁ d := by
  have h := hslack.2
  rw [omegaRoute_eq] at h
  simp only [routingBound]
  linarith

theorem omegaRoute_lt_routingBound (q₂ b₁ d : ℕ) (hslack : RoutingSlack q₂ b₁) :
    omegaRoute < routingBound q₂ b₁ d := by
  have h := hslack.2
  have hd := lambdaAt_nonneg q₂ b₁ d
  simp only [routingBound]
  linarith

theorem lambdaZero_lt_pRoot {q₂ b₁ : ℕ} (hslack : RoutingSlack q₂ b₁) :
    lambdaZero q₂ b₁ < pRoot := by
  have h := hslack.2
  rw [omegaRoute_eq] at h
  linarith

/-- The frozen integral floor `L_d = ceil(lambda_d |C_1|)`. -/
noncomputable def routingFloor (Γ : Type*) [Fintype Γ] (q₂ b₁ d : ℕ) : ℕ :=
  ⌈lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ)⌉₊

theorem routingFloor_le (Γ : Type*) [Fintype Γ] (q₂ b₁ d : ℕ) :
    lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ) ≤ (routingFloor Γ q₂ b₁ d : ℝ) :=
  Nat.le_ceil _

theorem routingFloor_lt_add_one (Γ : Type*) [Fintype Γ] (q₂ b₁ d : ℕ) :
    (routingFloor Γ q₂ b₁ d : ℝ) < lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ) + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg (lambdaAt_nonneg q₂ b₁ d) (by positivity))

theorem routingFloor_antitone (Γ : Type*) [Fintype Γ] (q₂ b₁ : ℕ) {d d' : ℕ}
    (h : d ≤ d') : routingFloor Γ q₂ b₁ d' ≤ routingFloor Γ q₂ b₁ d := by
  unfold routingFloor
  exact Nat.ceil_le_ceil
    (mul_le_mul_of_nonneg_right (lambdaAt_antitone q₂ b₁ h) (by positivity))

theorem routingFloor_succ_le_of_two_mul (Γ : Type*) [Fintype Γ] {q₂ b₁ d m k : ℕ}
    (h : routingFloor Γ q₂ b₁ d ≤ m) (h2 : m ≤ 2 * k) :
    routingFloor Γ q₂ b₁ (d + 1) ≤ k := by
  have hA : lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ) ≤ (m : ℝ) := by
    refine le_trans (routingFloor_le Γ q₂ b₁ d) ?_
    exact_mod_cast h
  have hB : (m : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast h2
  unfold routingFloor
  refine Nat.ceil_le.2 ?_
  rw [lambdaAt_succ]
  have hrw : lambdaAt q₂ b₁ d / 2 * (Fintype.card Γ : ℝ)
      = lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ) / 2 := by ring
  rw [hrw]
  linarith

/-! ## §2  The Bob-query assignment (Candidate A) -/

section Assignment

variable {Phys Coord Γ : Type*} [DecidableEq Coord] [DecidableEq Γ]

/-- One Bob query's assignment of a routed object's support. -/
structure BobRouting (rep : Phys → Coord × Γ) (S₀ S₁ : Finset Phys)
    (α : Coord) (T : Finset Γ) where
  left : Finset Γ
  right : Finset Γ
  left_represented : left ⊆ quotientSupport rep S₀ α
  right_represented : right ⊆ quotientSupport rep S₁ α
  assigns : left ∪ right = T

namespace BobRouting

variable {rep : Phys → Coord × Γ} {S₀ S₁ : Finset Phys} {α : Coord} {T : Finset Γ}

theorem left_subset (r : BobRouting rep S₀ S₁ α T) : r.left ⊆ T := by
  intro γ hγ
  rw [← r.assigns]
  exact Finset.mem_union_left _ hγ

theorem right_subset (r : BobRouting rep S₀ S₁ α T) : r.right ⊆ T := by
  intro γ hγ
  rw [← r.assigns]
  exact Finset.mem_union_right _ hγ

theorem card_parent_le (r : BobRouting rep S₀ S₁ α T) :
    T.card ≤ r.left.card + r.right.card := by
  have h : T.card = (r.left ∪ r.right).card := by rw [r.assigns]
  rw [h]
  exact Finset.card_union_le _ _

theorem forced_left (r : BobRouting rep S₀ S₁ α T) {γ : Γ} (hγ : γ ∈ T)
    (hnot : γ ∉ quotientSupport rep S₁ α) : γ ∈ r.left := by
  rw [← r.assigns] at hγ
  rcases Finset.mem_union.1 hγ with h | h
  · exact h
  · exact absurd (r.right_represented h) hnot

theorem forced_right (r : BobRouting rep S₀ S₁ α T) {γ : Γ} (hγ : γ ∈ T)
    (hnot : γ ∉ quotientSupport rep S₀ α) : γ ∈ r.right := by
  rw [← r.assigns] at hγ
  rcases Finset.mem_union.1 hγ with h | h
  · exact absurd (r.left_represented h) hnot
  · exact h

/-- Swapping the two physical children swaps the two assigned sets. -/
def symm (r : BobRouting rep S₀ S₁ α T) : BobRouting rep S₁ S₀ α T where
  left := r.right
  right := r.left
  left_represented := r.right_represented
  right_represented := r.left_represented
  assigns := by rw [Finset.union_comm]; exact r.assigns

@[simp] theorem symm_left (r : BobRouting rep S₀ S₁ α T) : r.symm.left = r.right := rfl

@[simp] theorem symm_right (r : BobRouting rep S₀ S₁ α T) : r.symm.right = r.left := rfl

@[simp] theorem symm_symm (r : BobRouting rep S₀ S₁ α T) : r.symm.symm = r := rfl

end BobRouting

/-- The canonical assignment: duplicated values go left, forced values are forced. -/
def canonicalRouting [DecidableEq Phys] (rep : Phys → Coord × Γ) {S S₀ S₁ : Finset Phys}
    (hS : S₀ ∪ S₁ = S) (α : Coord) (T : Finset Γ)
    (hT : T ⊆ quotientSupport rep S α) : BobRouting rep S₀ S₁ α T where
  left := T ∩ quotientSupport rep S₀ α
  right := T \ quotientSupport rep S₀ α
  left_represented := Finset.inter_subset_right
  right_represented := by
    intro γ hγ
    rw [Finset.mem_sdiff] at hγ
    have h1 : γ ∈ quotientSupport rep S α := hT hγ.1
    rw [mem_quotientSupport] at h1
    obtain ⟨p, hpS, hp⟩ := h1
    rw [← hS, Finset.mem_union] at hpS
    rcases hpS with h | h
    · exact absurd (mem_quotientSupport.2 ⟨p, h, hp⟩) hγ.2
    · exact mem_quotientSupport.2 ⟨p, h, hp⟩
  assigns := by
    ext γ
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

theorem bobRouting_nonempty [DecidableEq Phys] (rep : Phys → Coord × Γ)
    {S S₀ S₁ : Finset Phys} (hS : S₀ ∪ S₁ = S) (α : Coord) (T : Finset Γ)
    (hT : T ⊆ quotientSupport rep S α) : Nonempty (BobRouting rep S₀ S₁ α T) :=
  ⟨canonicalRouting rep hS α T hT⟩

theorem exists_child_two_mul {rep : Phys → Coord × Γ} {S₀ S₁ : Finset Phys}
    {α : Coord} {T : Finset Γ} (r : BobRouting rep S₀ S₁ α T) :
    T.card ≤ 2 * r.left.card ∨ T.card ≤ 2 * r.right.card := by
  have h := r.card_parent_le
  omega

end Assignment

/-! ## §3  The ordinary-token step -/

section Steps

variable {Phys Coord Γ : Type*} [DecidableEq Coord] [DecidableEq Γ] [Fintype Γ]
variable {rep : Phys → Coord × Γ} {S₀ S₁ : Finset Phys} {α : Coord} {T : Finset Γ}

theorem ordinaryToken_step (r : BobRouting rep S₀ S₁ α T) (q₂ b₁ d : ℕ)
    (hT : routingFloor Γ q₂ b₁ d ≤ T.card) :
    routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
      ∨ routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card := by
  rcases exists_child_two_mul r with h | h
  · exact Or.inl (routingFloor_succ_le_of_two_mul Γ hT h)
  · exact Or.inr (routingFloor_succ_le_of_two_mul Γ hT h)

/-! ## §4  The witness split rule -/

omit [DecidableEq Γ] in
theorem witnessSupport_card_ge {q₂ b₁ d : ℕ} (hΓ : 0 < Fintype.card Γ)
    (hdens : lambdaAt q₂ b₁ d < supportDensity T) :
    2 * routingFloor Γ q₂ b₁ (d + 1) ≤ T.card + 1 := by
  have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hΓ
  have hd : lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ) < (T.card : ℝ) := by
    rw [supportDensity, lt_div_iff₀ hpos] at hdens
    exact hdens
  have hL := routingFloor_lt_add_one Γ q₂ b₁ (d + 1)
  rw [lambdaAt_succ] at hL
  have hrw : lambdaAt q₂ b₁ d / 2 * (Fintype.card Γ : ℝ)
      = lambdaAt q₂ b₁ d * (Fintype.card Γ : ℝ) / 2 := by ring
  rw [hrw] at hL
  have hreal : (2 * (routingFloor Γ q₂ b₁ (d + 1)) : ℝ) < (T.card : ℝ) + 2 := by
    linarith
  have hnat : 2 * routingFloor Γ q₂ b₁ (d + 1) < T.card + 2 := by exact_mod_cast hreal
  omega

theorem witnessRoute_whole_card {q₂ b₁ d : ℕ} (r : BobRouting rep S₀ S₁ α T)
    (hbig : 2 * routingFloor Γ q₂ b₁ (d + 1) ≤ T.card + 1)
    (hsmall : r.right.card + 1 ≤ routingFloor Γ q₂ b₁ (d + 1)) :
    routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card := by
  have h := r.card_parent_le
  omega

theorem witnessRoute_loss_lt {q₂ b₁ d : ℕ} (r : BobRouting rep S₀ S₁ α T)
    (hΓ : 0 < Fintype.card Γ)
    (hsmall : r.right.card + 1 ≤ routingFloor Γ q₂ b₁ (d + 1)) :
    supportDensity T - supportDensity r.left < lambdaAt q₂ b₁ (d + 1) := by
  have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hΓ
  have hL := routingFloor_lt_add_one Γ q₂ b₁ (d + 1)
  have hcard : (r.right.card : ℝ) + 1 ≤ (routingFloor Γ q₂ b₁ (d + 1) : ℝ) := by
    exact_mod_cast hsmall
  have hsum : (T.card : ℝ) ≤ (r.left.card : ℝ) + (r.right.card : ℝ) := by
    exact_mod_cast r.card_parent_le
  have hkey : (T.card : ℝ) - (r.left.card : ℝ)
      < lambdaAt q₂ b₁ (d + 1) * (Fintype.card Γ : ℝ) := by linarith
  have hsplit : supportDensity T - supportDensity r.left
      = ((T.card : ℝ) - (r.left.card : ℝ)) / (Fintype.card Γ : ℝ) := by
    simp only [supportDensity]
    ring
  rw [hsplit, div_lt_iff₀ hpos]
  exact hkey

/-! ## §5  The density recurrence -/

omit [DecidableEq Γ] in
theorem routing_density_step {q₂ b₁ d : ℕ} {A : Finset Γ}
    (hinv : routingBound q₂ b₁ d ≤ supportDensity T)
    (hloss : supportDensity T - supportDensity A < lambdaAt q₂ b₁ (d + 1)) :
    routingBound q₂ b₁ (d + 1) < supportDensity A := by
  rw [routingBound_succ]
  linarith

/-! ## §6  The frozen lemma -/

theorem denseRoutingInvariant (r : BobRouting rep S₀ S₁ α T) (q₂ b₁ d : ℕ)
    (hΓ : 0 < Fintype.card Γ) (hslack : RoutingSlack q₂ b₁) :
    (routingFloor Γ q₂ b₁ d ≤ T.card →
        routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
          ∨ routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card)
      ∧ (routingBound q₂ b₁ d ≤ supportDensity T →
          (routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
              ∧ routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card)
            ∨ (routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
                ∧ routingBound q₂ b₁ (d + 1) < supportDensity r.left)
            ∨ (routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card
                ∧ routingBound q₂ b₁ (d + 1) < supportDensity r.right)) := by
  refine ⟨fun hT => ordinaryToken_step r q₂ b₁ d hT, fun hinv => ?_⟩
  have hdens : lambdaAt q₂ b₁ d < supportDensity T :=
    lt_of_lt_of_le (lambdaAt_lt_routingBound q₂ b₁ d hslack) hinv
  have hbig := witnessSupport_card_ge (T := T) (q₂ := q₂) (b₁ := b₁) (d := d) hΓ hdens
  by_cases hL : routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
  · by_cases hR : routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card
    · exact Or.inl ⟨hL, hR⟩
    · have hsmall : r.right.card + 1 ≤ routingFloor Γ q₂ b₁ (d + 1) := by omega
      exact Or.inr (Or.inl ⟨hL, routing_density_step hinv (witnessRoute_loss_lt r hΓ hsmall)⟩)
  · have hsmall : r.left.card + 1 ≤ routingFloor Γ q₂ b₁ (d + 1) := by omega
    have hR : routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card :=
      witnessRoute_whole_card r.symm hbig hsmall
    exact Or.inr (Or.inr ⟨hR, routing_density_step hinv (witnessRoute_loss_lt r.symm hΓ hsmall)⟩)

theorem denseRoutingInvariant_exists [DecidableEq Phys] {S : Finset Phys}
    (hS : S₀ ∪ S₁ = S) (hT : T ⊆ quotientSupport rep S α) (q₂ b₁ d : ℕ)
    (hΓ : 0 < Fintype.card Γ) (hslack : RoutingSlack q₂ b₁) :
    ∃ r : BobRouting rep S₀ S₁ α T,
      (routingFloor Γ q₂ b₁ d ≤ T.card →
          routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
            ∨ routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card)
        ∧ (routingBound q₂ b₁ d ≤ supportDensity T →
            (routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
                ∧ routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card)
              ∨ (routingFloor Γ q₂ b₁ (d + 1) ≤ r.left.card
                  ∧ routingBound q₂ b₁ (d + 1) < supportDensity r.left)
              ∨ (routingFloor Γ q₂ b₁ (d + 1) ≤ r.right.card
                  ∧ routingBound q₂ b₁ (d + 1) < supportDensity r.right)) :=
  ⟨canonicalRouting rep hS α T hT,
    denseRoutingInvariant (canonicalRouting rep hS α T hT) q₂ b₁ d hΓ hslack⟩

end Steps

/-! ## §7  The total loss of a witness routed whole, and the retained bonus -/

theorem lambdaZero_pos {q₂ : ℕ} (b₁ : ℕ) (hq : 0 < q₂) : 0 < lambdaZero q₂ b₁ := by
  have h1 : (0 : ℝ) < 2 * (q₂ : ℝ) := by
    have : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq
    linarith
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  exact div_pos h1 h2

theorem routing_total_loss_le (q₂ b₁ n : ℕ) :
    ∑ d ∈ Finset.range n, lambdaAt q₂ b₁ (d + 1) ≤ lambdaZero q₂ b₁ := by
  rw [sum_lambdaAt_succ]
  have h0 := lambdaZero_nonneg q₂ b₁
  have h2 : (0 : ℝ) < 1 / 2 ^ n := by positivity
  nlinarith [mul_nonneg h0 (le_of_lt h2)]

theorem routing_total_loss_lt {q₂ : ℕ} (b₁ n : ℕ) (hq : 0 < q₂) :
    ∑ d ∈ Finset.range n, lambdaAt q₂ b₁ (d + 1) < lambdaZero q₂ b₁ := by
  rw [sum_lambdaAt_succ]
  have h0 := lambdaZero_pos (q₂ := q₂) b₁ hq
  have h2 : (0 : ℝ) < 1 / 2 ^ n := by positivity
  nlinarith [mul_pos h0 h2]

theorem routing_total_loss_lt_pRoot {q₂ : ℕ} (b₁ n : ℕ) (hq : 0 < q₂)
    (hslack : RoutingSlack q₂ b₁) :
    ∑ d ∈ Finset.range n, lambdaAt q₂ b₁ (d + 1) < pRoot := by
  have h1 := routing_total_loss_lt (q₂ := q₂) b₁ n hq
  have h2 := lambdaZero_lt_pRoot hslack
  linarith

section Bonus

variable {Γ : Type*} [Fintype Γ]

theorem unsplitWitness_density_gt_omega {q₂ b₁ d : ℕ} {T : Finset Γ}
    (hslack : RoutingSlack q₂ b₁) (hinv : routingBound q₂ b₁ d ≤ supportDensity T) :
    omegaRoute < supportDensity T :=
  lt_of_lt_of_le (omegaRoute_lt_routingBound q₂ b₁ d hslack) hinv

theorem unsplitWitness_node_density_gt_omega {Phys Coord : Type*} [DecidableEq Coord]
    [DecidableEq Γ] (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord)
    {q₂ b₁ d : ℕ} {T : Finset Γ} (hT : T ⊆ quotientSupport rep S α)
    (hslack : RoutingSlack q₂ b₁) (hinv : routingBound q₂ b₁ d ≤ supportDensity T) :
    omegaRoute < quotientDensity rep S α := by
  have h1 := unsplitWitness_density_gt_omega hslack hinv
  have h2 := supportDensity_mono hT
  rw [supportDensity_quotientSupport] at h2
  linarith

theorem unsplitWitness_retains_bonus {Phys Coord Xs Ys : Type*}
    [DecidableEq Coord] [DecidableEq Γ] [Fintype Xs] [Fintype Ys]
    (rep : Phys → Coord × Γ) (S : Finset Phys) (U B : Finset Coord) (α : Coord)
    (F : Stage1SlotBinding) (Rsrc : Xs → Ys → Bool) {b₀ Dsrc q₂ b₁ d : ℕ}
    (wrepr : Finset Phys → Coord →
      Finset (Fin (F.q₁ + 3) × Xs) × Finset (Fin (F.q₁ + 3) → Ys))
    {T : Finset Γ}
    (hΓ : 0 < Fintype.card Γ)
    (hT : T ⊆ quotientSupport rep S α)
    (hslack : RoutingSlack q₂ b₁)
    (hinv : routingBound q₂ b₁ d ≤ supportDensity T)
    (hgap : localCapacityGap F Rsrc b₀ Dsrc)
    (hwrepr : ∀ (S' : Finset Phys), ∀ β ∈ selectedWitness U B,
      omegaRoute < quotientDensity rep S' β →
        wrepr S' β ∈ bracketGE Xs Ys (F.q₁ + 3) (xCap F b₀) (9 / 25))
    (hα : α ∈ selectedWitness U B) :
    ⌈(9 : ℝ) / 25 * (Fintype.card Γ : ℝ)⌉₊ ≤ (quotientSupport rep S α).card
      ∧ bCap Dsrc F.a + 1
          ≤ D (subgame (interlaceFun Rsrc (F.q₁ + 3)) (wrepr S α).1 (wrepr S α).2) := by
  have hdens := unsplitWitness_node_density_gt_omega rep S α hT hslack hinv
  exact ⟨witnessDensity_meets_capacity_columns rep S α hΓ hdens,
    witnessToken_is_Bcap_succ_hard F Rsrc (wrepr S α) hgap (hwrepr S α hα hdens)⟩

end Bonus

/-! ## §8  The uniqueness clause -/

section Uniqueness

/-- The routed objects present at one protocol node. -/
abbrev RoutedFamily (Coord Γ : Type*) := Coord → Option (Finset Γ)

variable {Coord Γ : Type*}

theorem routedFamily_unique (f : RoutedFamily Coord Γ) (α : Coord) {T T' : Finset Γ}
    (h : f α = some T) (h' : f α = some T') : T = T' := by
  rw [h] at h'
  exact Option.some.inj h'

/-- One object per coordinate of the good set at the root. -/
def rootFamily [DecidableEq Coord] (H : Finset Coord) (T : Coord → Finset Γ) :
    RoutedFamily Coord Γ := fun α => if α ∈ H then some (T α) else none

theorem rootFamily_eq_some [DecidableEq Coord] (H : Finset Coord) (T : Coord → Finset Γ)
    {α : Coord} (hα : α ∈ H) : rootFamily H T α = some (T α) := by
  simp [rootFamily, hα]

theorem rootFamily_eq_none [DecidableEq Coord] (H : Finset Coord) (T : Coord → Finset Γ)
    {α : Coord} (hα : α ∉ H) : rootFamily H T α = none := by
  simp [rootFamily, hα]

/-- The left child of a suffix node. -/
def routeLeft (p : List Bool) : List Bool := p ++ [false]

/-- The right child of a suffix node. -/
def routeRight (p : List Bool) : List Bool := p ++ [true]

theorem routeLeft_length (p : List Bool) : (routeLeft p).length = p.length + 1 := by
  simp [routeLeft]

theorem routeRight_length (p : List Bool) : (routeRight p).length = p.length + 1 := by
  simp [routeRight]

theorem routeChildren_ne (p : List Bool) : routeLeft p ≠ routeRight p := by
  simp [routeLeft, routeRight]

theorem routeLeft_not_prefix_routeRight (p : List Bool) :
    ¬ (routeLeft p <+: routeRight p) := by
  rintro ⟨t, ht⟩
  have hlen := congrArg List.length ht
  simp only [routeLeft, routeRight, List.length_append, List.length_cons,
    List.length_nil] at hlen
  have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst ht0
  simp [routeLeft, routeRight] at ht

theorem routeRight_not_prefix_routeLeft (p : List Bool) :
    ¬ (routeRight p <+: routeLeft p) := by
  rintro ⟨t, ht⟩
  have hlen := congrArg List.length ht
  simp only [routeLeft, routeRight, List.length_append, List.length_cons,
    List.length_nil] at hlen
  have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst ht0
  simp [routeLeft, routeRight] at ht

theorem routeChildren_incomparable (p : List Bool) :
    ¬ (routeLeft p <+: routeRight p) ∧ ¬ (routeRight p <+: routeLeft p) :=
  ⟨routeLeft_not_prefix_routeRight p, routeRight_not_prefix_routeLeft p⟩

end Uniqueness

/-! ## §9  Non-vacuity, statement poles and consistency probes -/

theorem routingBound_nondegenerate {q₂ : ℕ} (hq : 0 < q₂) :
    ∃ b₁ : ℕ, RoutingSlack q₂ b₁
      ∧ ∀ d : ℕ, omegaRoute < routingBound q₂ b₁ d ∧ routingBound q₂ b₁ d < 1 := by
  obtain ⟨b₁, hrange, _⟩ := lambdaAt_nondegenerate hq
  have h0 : 0 < lambdaZero q₂ b₁ ∧ lambdaZero q₂ b₁ < 1 / 4 := by
    have := hrange 0
    rwa [lambdaAt_zero] at this
  have hslack : RoutingSlack q₂ b₁ := by
    constructor
    · rw [pRoot_eq]; linarith [h0.2]
    · rw [omegaRoute_eq, pRoot_eq]; linarith [h0.2]
  refine ⟨b₁, hslack, fun d => ⟨omegaRoute_lt_routingBound q₂ b₁ d hslack, ?_⟩⟩
  have hle : lambdaAt q₂ b₁ d ≤ lambdaZero q₂ b₁ := lambdaAt_le_lambdaZero q₂ b₁ d
  have hp : pRoot = 3 / 4 := pRoot_eq
  simp only [routingBound, hp]
  linarith

theorem denseRoutingInvariant_hypotheses_consistent :
    ∃ (rep : Fin 32 → Fin 1 × Fin 32) (S S₀ S₁ T : Finset (Fin 32))
      (r : BobRouting rep S₀ S₁ 0 T),
      S₀ ∪ S₁ = S ∧ T ⊆ quotientSupport rep S 0 ∧ RoutingSlack 2 5
        ∧ routingFloor (Fin 32) 2 5 0 ≤ T.card
        ∧ routingBound 2 5 0 = supportDensity T
        ∧ ¬ (routingFloor (Fin 32) 2 5 1 ≤ r.right.card)
        ∧ routingFloor (Fin 32) 2 5 1 ≤ r.left.card
        ∧ routingBound 2 5 1 < supportDensity r.left
        ∧ omegaRoute < supportDensity r.left := by
  classical
  have hfloor0 : routingFloor (Fin 32) 2 5 0 = 4 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  have hfloor1 : routingFloor (Fin 32) 2 5 1 = 2 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  have hslack : RoutingSlack 2 5 := by
    constructor
    · unfold lambdaZero
      rw [pRoot_eq]
      norm_num
    · unfold lambdaZero
      rw [pRoot_eq, omegaRoute_eq]
      norm_num
  set rep : Fin 32 → Fin 1 × Fin 32 := fun p => (0, p) with hrep
  set S : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 24) with hS
  set S₀ : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 23) with hS₀
  set S₁ : Finset (Fin 32) :=
    Finset.univ.filter (fun p => 22 ≤ (p : ℕ) ∧ (p : ℕ) < 24) with hS₁
  set LL : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 23) with hLL
  set RR : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) = 23) with hRR
  have hleft : LL ⊆ quotientSupport rep S₀ 0 := by decide
  have hright : RR ⊆ quotientSupport rep S₁ 0 := by decide
  have hassign : LL ∪ RR = S := by decide
  have hcardT : S.card = 24 := by decide
  have hcardL : LL.card = 23 := by decide
  have hcardR : RR.card = 1 := by decide
  refine ⟨rep, S, S₀, S₁, S, ⟨LL, RR, hleft, hright, hassign⟩, by decide, by decide,
    hslack, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfloor0, hcardT]; norm_num
  · rw [routingBound_zero, pRoot_eq, supportDensity, hcardT]
    norm_num
  · rw [hfloor1]
    change ¬ (2 ≤ RR.card)
    rw [hcardR]
    norm_num
  · rw [hfloor1]
    change (2 : ℕ) ≤ LL.card
    rw [hcardL]
    norm_num
  · change routingBound 2 5 1 < supportDensity LL
    rw [supportDensity, hcardL, routingBound, pRoot_eq]
    unfold lambdaAt lambdaZero
    norm_num
  · change omegaRoute < supportDensity LL
    rw [supportDensity, hcardL, omegaRoute_eq]
    norm_num

theorem bobRouting_assignment_is_a_choice :
    ∃ (rep : Fin 32 → Fin 1 × Fin 32) (S₀ S₁ T : Finset (Fin 32))
      (r r' : BobRouting rep S₀ S₁ 0 T), r.left ≠ r'.left ∧ r.right ≠ r'.right := by
  classical
  set rep : Fin 32 → Fin 1 × Fin 32 := fun p => (0, p) with hrep
  set S₀ : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 23) with hS₀
  set S₁ : Finset (Fin 32) :=
    Finset.univ.filter (fun p => 22 ≤ (p : ℕ) ∧ (p : ℕ) < 24) with hS₁
  set T : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 24) with hT
  set LL : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 23) with hLL
  set RR : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) = 23) with hRR
  set LL' : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 22) with hLL'
  set RR' : Finset (Fin 32) :=
    Finset.univ.filter (fun p => 22 ≤ (p : ℕ) ∧ (p : ℕ) < 24) with hRR'
  exact ⟨rep, S₀, S₁, T,
    ⟨LL, RR, by decide, by decide, by decide⟩,
    ⟨LL', RR', by decide, by decide, by decide⟩,
    by decide, by decide⟩

theorem bobRouting_pole_left_child_not_enough :
    ∃ (rep : Fin 32 → Fin 1 × Fin 32) (S S₀ S₁ T : Finset (Fin 32)),
      S₀ ∪ S₁ = S ∧ T ⊆ quotientSupport rep S 0
        ∧ ¬ (T ⊆ quotientSupport rep S₀ 0) := by
  classical
  set rep : Fin 32 → Fin 1 × Fin 32 := fun p => (0, p) with hrep
  set S : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 24) with hS
  set S₀ : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 23) with hS₀
  set S₁ : Finset (Fin 32) :=
    Finset.univ.filter (fun p => 22 ≤ (p : ℕ) ∧ (p : ℕ) < 24) with hS₁
  exact ⟨rep, S, S₀, S₁, S, by decide, by decide, by decide⟩

theorem ordinaryStep_pole_side_not_fixed :
    ∃ (rep : Fin 32 → Fin 1 × Fin 32) (S₀ S₁ T : Finset (Fin 32))
      (r : BobRouting rep S₀ S₁ 0 T),
      routingFloor (Fin 32) 2 5 0 ≤ T.card
        ∧ ¬ (routingFloor (Fin 32) 2 5 1 ≤ r.left.card)
        ∧ routingFloor (Fin 32) 2 5 1 ≤ r.right.card := by
  classical
  have hfloor0 : routingFloor (Fin 32) 2 5 0 = 4 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  have hfloor1 : routingFloor (Fin 32) 2 5 1 = 2 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  set rep : Fin 32 → Fin 1 × Fin 32 := fun p => (0, p) with hrep
  set S : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 24) with hS
  set LL : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 1) with hLL
  set RR : Finset (Fin 32) :=
    Finset.univ.filter (fun p => 1 ≤ (p : ℕ) ∧ (p : ℕ) < 24) with hRR
  have hcardT : S.card = 24 := by decide
  have hcardL : LL.card = 1 := by decide
  have hcardR : RR.card = 23 := by decide
  refine ⟨rep, S, S, S, ⟨LL, RR, by decide, by decide, by decide⟩, ?_, ?_, ?_⟩
  · rw [hfloor0, hcardT]; norm_num
  · rw [hfloor1]
    change ¬ ((2 : ℕ) ≤ LL.card)
    rw [hcardL]
    norm_num
  · rw [hfloor1]
    change (2 : ℕ) ≤ RR.card
    rw [hcardR]
    norm_num

theorem witnessSupport_pole_below_threshold :
    ∃ T : Finset (Fin 32),
      supportDensity T < lambdaAt 2 5 0
        ∧ ¬ (2 * routingFloor (Fin 32) 2 5 1 ≤ T.card + 1) := by
  classical
  have hfloor1 : routingFloor (Fin 32) 2 5 1 = 2 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  set T : Finset (Fin 32) := Finset.univ.filter (fun p => (p : ℕ) < 2) with hT
  have hcardT : T.card = 2 := by decide
  refine ⟨T, ?_, ?_⟩
  · rw [supportDensity, hcardT]
    unfold lambdaAt lambdaZero
    norm_num
  · rw [hfloor1, hcardT]
    norm_num

theorem routedFamily_nondegenerate :
    ∃ (H : Finset (Fin 3)) (T : Fin 3 → Finset (Fin 4)),
      rootFamily H T 0 = some (T 0) ∧ rootFamily H T 1 = some (T 1)
        ∧ T 0 ≠ T 1 ∧ rootFamily H T 2 = none := by
  classical
  refine ⟨{0, 1}, fun α => if α = 0 then {0} else {1}, ?_, ?_, ?_, ?_⟩
  · exact rootFamily_eq_some _ _ (by decide)
  · exact rootFamily_eq_some _ _ (by decide)
  · decide
  · exact rootFamily_eq_none _ _ (by decide)

/-! ## §10  The rejected candidate -/

/-- Candidate B: a routed token carrying its own invariant as constructor data. -/
structure RoutedToken (Γ : Type*) [Fintype Γ] (q₂ b₁ : ℕ) where
  depth : ℕ
  support : Finset Γ
  invariant : routingFloor Γ q₂ b₁ depth ≤ support.card

theorem routedToken_nonempty : Nonempty (RoutedToken (Fin 32) 2 5) := by
  refine ⟨⟨0, Finset.univ, ?_⟩⟩
  have hfloor0 : routingFloor (Fin 32) 2 5 0 = 4 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  rw [hfloor0]
  simp

theorem routedToken_support_card_ge {Γ : Type*} [Fintype Γ] {q₂ b₁ : ℕ}
    (t : RoutedToken Γ q₂ b₁) :
    lambdaAt q₂ b₁ t.depth * (Fintype.card Γ : ℝ) ≤ (t.support.card : ℝ) := by
  refine le_trans (routingFloor_le Γ q₂ b₁ t.depth) ?_
  exact_mod_cast t.invariant

theorem routedToken_needs_no_node :
    ∃ (t : RoutedToken (Fin 32) 2 5) (rep : Fin 32 → Fin 1 × Fin 32)
      (S : Finset (Fin 32)), ¬ (t.support ⊆ quotientSupport rep S 0) := by
  classical
  have hfloor0 : routingFloor (Fin 32) 2 5 0 = 4 := by
    unfold routingFloor lambdaAt lambdaZero
    norm_num
  have hinv : routingFloor (Fin 32) 2 5 0 ≤ (Finset.univ : Finset (Fin 32)).card := by
    rw [hfloor0]
    simp
  refine ⟨⟨0, Finset.univ, hinv⟩, fun p => (0, p), ∅, ?_⟩
  intro hsub
  have hmem : (0 : Fin 32) ∈ quotientSupport (fun p => ((0 : Fin 1), p))
      (∅ : Finset (Fin 32)) 0 := hsub (Finset.mem_univ 0)
  rw [mem_quotientSupport] at hmem
  obtain ⟨p, hp, _⟩ := hmem
  exact absurd hp (Finset.notMem_empty p)

end EthInapproximability.ParameterizedNP.DenseRoutingInvariant
