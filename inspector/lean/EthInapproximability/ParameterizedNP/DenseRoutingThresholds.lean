import EthInapproximability.ParameterizedNP.DenseBranchSelection

/-!
# Parameterized NP route: the fourth block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 811--876** -- the
  routing threshold, the token bookkeeping device, and
  `lem:dense-local-certificates` with its frozen proof.  The anchors traced
  here, in the order the block prints them:
  * `eq:routing-threshold` (label 815, display 811--816): for suffix depth
    `d >= 0`, `lambda_d = lambda_0 2^{-d} = 2 q_2 2^{-b_1} 2^{-d}`;
  * lines 818--823, the frozen bookkeeping device: "For each coordinate in
    `H`, place one *ordinary token*, representing a `B_cap`-hard one-copy
    restriction of `M_1^T`.  For each coordinate in `W`, attach one additional
    *bonus token* to its ordinary token.  Until the pair is split, it is a
    single weight-two witness object and represents the stronger `B_cap + 1`
    local capacity restriction";
  * `lem:dense-local-certificates` (label 826, statement 825--831, proof
    833--876): "Every ordinary token has root quotient support at least
    `p_root |C_1|`.  Every unsplit witness object remains a valid `B_cap + 1`
    certificate whenever its quotient support density is greater than
    `omega`", with the frozen proof steps
    - 834--838, membership in `H = [q_2] \ B_{j_*}` excludes the diagonal-bad
      set, so at least `ceil((1 - rho_loc)|C_1|)` quotient columns survive,
      together with the frozen caveat "this conclusion is proved only for
      coordinates outside the aggregate-bounded bad set; no uniform
      every-coordinate survival statement is being used";
    - 840--853, the one-coordinate upper-fibre estimate for the
      `(q_2,t_2,eps_2)`-balanced family,
      `|P_alpha|/|Rows(M_1)| >= x_dom/(1+eps_2) >= 98/100 > 3/5`;
    - 854--862, `p_root >= lambda_0 >= 2^{-b_1}`, the choice of one physical
      representative of every retained quotient value and every value in
      `P_alpha`, the resulting membership in
      `[M_1^T, 1, 2^{-b_1}, 3/5]` and the frozen conclusion "The Stage-1
      certificate `eq:stage1-robust-certificate` makes this restriction
      `B_cap`-hard";
    - 864--876, the witness half: template-goodness and the source-owner
      construction supply the `q_1 + 3`-copy restriction used in
      `eq:local-capacity-gap` (`07:617--623`), the full product `C_1` has no
      balancedness loss (`eps_1 = 0`), and "witness support density greater
      than `omega = (1 + eps_1)/2 = 1/2 > 9/25` gives complexity at least
      `B_cap + 1`".
* **Deliberately NOT claimed (the next block's territory).**
  `lem:dense-routing` (`08:878--894`, statement and proof through `08:944`) --
  the support-routing invariant, the split rule, the uniqueness clause and the
  total-loss clause -- has **no** declaration here, and neither does the
  weighted stopping count of `sec:dense-weighted-count` (`08:946--` ) or
  `lem:dense-no-leaf` (`08:955--979`).  Where the frozen proofs of those
  results need arithmetic of the threshold sequence
  (`lambda_{d+1} = lambda_d/2` at `08:902`, `sum_{d>=0} lambda_{d+1} = lambda_0`
  at `08:937--940`, `lambda_r = 2^{1-b_1}` at `08:963--965`), that arithmetic is
  proved here **as a general property of the definition of `lambda_d`** and is
  explicitly *not* a claim about routing: nothing in this module says tokens can
  be routed, that a witness retains its bonus certificate, or that no positive
  token reaches a premature leaf.  A later tranche may cite the arithmetic and
  may **not** cite this module as having supplied any routing statement.
* **Predecessor anchors (the handoffs consumed by pin):**
  * `08:702--810` through the banked
    `EthInapproximability.ParameterizedNP.DenseBranchSelection`, which supplies
    the selected data `selectedGood` (`H`) and `selectedWitness` (`W`) with
    `selectedWitness_subset_selectedGood`, the quotient-support layer
    (`quotientSupport`, `quotientDensity`, `mem_quotientSupport`,
    `quotientSupport_mono`) and the routing constants `pRoot`, `lambdaZero`,
    `epsOne`, `omegaRoute` with `pRoot_eq`, `omegaRoute_eq`,
    `lambdaZero_nonneg` and the predicate `RoutingSlack`;
  * `08:508--700` through `DenseSourceOwners`, which supplies `diagonalBadSet`
    and `mem_diagonalBadSet` -- **the definition `lem:dense-local-certificates`
    reads its first survival bound off** -- and `xCap`;
  * `08:1--328` through `DenseStageFourOpening`, which supplies the pinned
    `rhoLoc = 1/4`, `xDom` and the gate predicate `denseSeparationGates`;
  * `07:617--623` through `StageThreeExactScale.localCapacityGap` and
    `RawStageFour.localCapacityGap_le_member`, the odd-copy capacity inequality
    in its consumption form;
  * `07:209--215` through `StageOneInterlace.stage1RobustCertificate` and
    `StageTwoRelaxed.LambdaGE_le_top_rung`, the three-rung Stage-1 certificate
    and the fact that a `Lambda_3` lower bound is a lower bound on its own top
    rung.
  **None of those handoffs is restated here.**
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design.  It
  reaches this block only through the upper-fibre estimate of `08:846--853`,
  which is transcribed here as the *arithmetic readout* `denseFibre_estimate` of
  the banked gate `denseSeparationGates` -- that readout says only
  `x_dom/(1 + eps_2) >= 98/100 > 3/5`, never that the family exists or that any
  indexed set attains the bound.  The **balanced-family application itself**
  (`08:846--851`, "The indexed set `S_{j_*}` has density at least `x_dom` in
  `C_2`.  The one-coordinate upper-fibre estimate ... therefore gives ...") has
  no declaration here.  Likewise the Stage-1 certificate
  `eq:stage1-robust-certificate` and the odd-copy gap `eq:local-capacity-gap`
  are named hypotheses (`hcert`, `hgap`), and the representative choice of
  `08:854--860` and the diagonal-scaffold construction of `08:864--871` are
  named hypotheses (`hrepr`, `hwrepr`) rather than constructions.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency
  graph.
* **New vendored-gap work.**  None.  The thresholds are a geometric sequence
  over the reals, the token bookkeeping is `Finset` counting, and the two
  hardness readouts are `Nat.sInf_le` against the banked family definitions.
* Proof status: **new** for the threshold sequence, the token bookkeeping, the
  survival readout, the fibre readout and both hardness readouts; **inherited by
  pin** for the selected data, the quotient support, the routing constants, the
  diagonal-bad definition, the odd-copy consumption form and the top-rung bound.
* **Repair record (tranche `cc-t2l-r1`, 5 August 2026).**  The first pass of this
  block was gated `REVISE` on the third conjunct of `denseLocalCertificates`,
  and the finding was confirmed first-hand: the frozen witness half
  (`08:828--830`) is an implication **at each protocol node** -- the columns
  surviving at the node are what place the restriction in the `9/25` bracket
  (`08:871--875`) -- whereas the first pass carried a node-independent family
  `wrepr : Coord -> ...` whose bracket membership was assumed unconditionally,
  ahead of the `S` binder.  The density then did no work for the hardness
  conjunct, and the certified rectangle was tied to no node.  Three changes
  repair it, and nothing else in the block moved:
  * `wrepr` is indexed by the node **and** the coordinate,
    `Finset Phys -> Coord -> ...`;
  * the scaffold hypothesis `hwrepr` is **gated on the density**, so nothing is
    assumed at nodes where the frozen hypothesis fails -- this strictly weakens
    the hypothesis, hence strictly strengthens the theorem;
  * the hardness conclusion is stated at the **node-indexed** rectangle
    `wrepr S alpha`, and the helper `witnessToken_is_Bcap_succ_hard` now takes
    **the rectangle directly** rather than a coordinate-indexed family, so the
    odd-copy readout names no selection, node or density at all.
  Two readouts are added for the repaired shape:
  `witnessCertificate_pole_node_dependent` (the same coordinate is above `omega`
  at one node and below it at another, so the index is load-bearing) and
  `witnessRepr_gate_nonvacuous` (the gated hypothesis is inhabited at a point
  where the gate **fires**, by a `wrepr` that simultaneously **refutes** the
  ungated form).  The remaining 42 declarations are byte-identical to the first
  pass.  This also repairs the interface `lem:dense-routing` (`08:878--944`)
  consumes: a node-indexed certificate can be instantiated by the node's own
  restriction, which is what "retains its bonus certificate" (`08:942--944`)
  needs.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, the proof outline
of `thm:paper-protected-stage4`.  One reader item is claimed, and it was
unclaimed before this tranche: `DenseSynchronisation` claims lines 242--250,
`DenseSourceOwners` claims 250--252, `DenseBranchSelection` claims 253--254,
258--259 and the clause "Quotient-support routing follows every Bob query" of
line 259, and it recorded lines 256--258 as **deliberately unclaimed, belonging
to the routing/token tranche**.

* Reader lines 256--258, the sentence "The Stage--2 lower bounds are applied to
  quotient supports, using the same physical balanced family as in Stage~2" --
  SS3: `denseLocalCertificates` and its component readouts
  (`ordinaryToken_root_support`, `ordinaryToken_root_support_ceiling`,
  `stage1Certificate_le_member`, `ordinaryToken_is_Bcap_hard`,
  `witnessDensity_meets_capacity_columns`, `witnessToken_is_Bcap_succ_hard`).
  The reader sentence condenses the whole of `lem:dense-local-certificates`, and
  this module covers it **partially and says so**: the "applied to quotient
  supports" half is proved (both certificates are transported to the quotient
  support of a coordinate), while the "using the same physical balanced family as
  in Stage~2" half -- the application of the cited
  `(q_2,t_2,eps_2)`-balanced family to `S_{j_*}` at `08:846--851` -- has **no**
  declaration here and remains covered only by the arithmetic readout
  `denseFibre_estimate` (coverage limit 5).  The item is assigned here because
  this is the block the sentence describes; a later tranche completing
  `08:846--851` must cite that gap, not re-claim the reader line.

The first sentence of reader line 256 ("On that branch there is no second
synchronized prefix") is **deliberately not claimed**: it is a statement about
the residual protocol's query structure, which this module does not touch, and
assigning it here would be citing a sentence this block does not state.  The
remainder of line 259 onwards ("the weighted stopping count records ...") is the
next block's.

**SS1 (the routing thresholds), SS2 (the token bookkeeping), SS4 (non-vacuity,
poles and consistency) and SS5 (the rejected candidate) claim no reader item,
deliberately rather than by omission**: the 41-page reader artifact contains no
counterpart for `eq:routing-threshold` or for the ordinary/bonus token device --
it condenses both into the phrase "the weighted stopping count", which belongs
to the next block -- and a reader item may not be invented for them.

## Candidate encodings of the token bookkeeping (`k = 2`, raced)

The novel object of this tranche is the bookkeeping device of `08:818--823`.

**Candidate A (landed, SS2).**  Make a token a *derived weight on the selected
data*: `tokenWeight U B alpha` is `2` on `W` and `1` on the rest of `H`, so the
frozen "attach one additional bonus token to its ordinary token" is literally an
increment of the weight of the object already sitting at `alpha`, and "a single
weight-two witness object" is the value `2`.  Nothing is stored: the device is a
function of the banked `selectedGood`/`selectedWitness`, no certificate is
constructor data, and the frozen total mass `|H| + |W|` of `08:997` is the
*theorem* `sum_tokenWeight`.  7 aux lemmas proved.

**Candidate B (rejected, SS5).**  Take a token as a record carrying its own
certificate: the coordinate, a `bonus` flag, a local capacity, and the field
`B_cap + [bonus] <= capacity`.  3 aux lemmas proved, but it loses decisively on
two counts.  First, it puts the frozen *conclusion* of
`lem:dense-local-certificates` (`08:828--830`) into constructor data, which the
mechanical contract's no-conclusion-in-constructor-data rule forbids outright.
Second, it is unfaithful even as data: `tokenObject_needs_no_good_coordinate`
exhibits an inhabitant whose coordinate is **not** in the good set `H` at all,
so the frozen sentence "For each coordinate in `H`, place one ordinary token"
has no content in it -- the record asserts a `B_cap + 1` certificate at a
coordinate the counting never selected.  The race is decided on faithfulness,
not length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the threshold sequence, general (8): `lambdaAt_zero`, `lambdaAt_succ`,
  `lambdaAt_eq`, `lambdaAt_nonneg`, `lambdaAt_antitone`, `lambdaAt_le_lambdaZero`,
  `sum_lambdaAt_succ`, `lambdaAt_at_depth_log`.
* `A2` the token bookkeeping, general (7): `tokenWeight_eq_two_iff`,
  `tokenWeight_eq_one_iff`, `one_le_tokenWeight`, `tokenWeight_le_two`,
  `tokenWeight_of_no_witness`, `tokenWeight_of_no_bad`, `sum_tokenWeight`.
* `A3` the frozen scalars, general (4): `xSeed_eq_inv_pow`,
  `xSeed_le_lambdaZero`, `xSeed_le_pRoot`, `omegaRoute_gt_capacity_density`.
* `A4` `lem:dense-local-certificates`, ordinary half (5):
  `ordinaryToken_root_support_ceiling`, `ordinaryToken_root_support`,
  `stage1Certificate_le_member`, `stage1Certificate_family_nonempty`,
  `ordinaryToken_is_Bcap_hard`.
* `A5` `lem:dense-local-certificates`, witness half (3):
  `witnessDensity_meets_capacity_columns`, `witnessToken_is_Bcap_succ_hard`,
  `denseFibre_estimate`.
* `A6` the frozen lemma itself (1): `denseLocalCertificates`.
* Candidate B's own battery (3): `tokenObject_nonempty`,
  `tokenObject_capacity_ge`, `tokenObject_needs_no_good_coordinate`.

That is **28 battery entries proved plus 3 for the rejected candidate**, with
`0` unproved, alongside **five statement poles**
(`lambdaAt_pole_strictly_below_root`,
`ordinaryToken_root_support_pole_at_bad_coordinate`,
`witnessColumns_pole_below_omega`, `witnessCertificate_pole_node_dependent`,
`ordinaryToken_hard_pole_at_constant`) and **seven non-vacuity / consistency
readouts** -- one for every definition group and every premise bundle the module
introduces.  The module has **46** source declarations in all: 3 definitions
(`lambdaAt`, `tokenWeight`, `TokenObject`) and 43 proved results (28 battery
entries, 3 for the rejected candidate, 5 statement poles, 7 readouts):

* `lambdaAt_nondegenerate`, the threshold sequence inhabited **symbolically in
  `q_2`**: for every `q_2` the depth `b_1 = q_2 + 4` makes every
  `lambda_d` lie strictly between `0` and `1/4` and makes the sequence strictly
  decreasing, proved from the banked `self_lt_two_pow` with no tower evaluated;
* `tokenWeight_nondegenerate`, a separating probe of the bookkeeping at
  `|Coord| = 8`, `B = {0,1}`, `U = {1,2,3}`: **both** weights actually occur, no
  bonus sits outside `H`, and the frozen total mass is
  `|H| + |W| = 6 + 2 = 8`;
* `ordinaryToken_root_support_hypotheses_consistent`, the full premise bundle of
  the survival readout inhabited with the frozen ceiling **attained** at
  `rho_loc = 1/4`;
* `witnessColumns_hypotheses_consistent`, the full premise bundle of the witness
  readout inhabited with a density **strictly** between `omega` and `1`;
* `witnessRepr_gate_nonvacuous`, the **density-gated scaffold hypothesis** of the
  repaired `denseLocalCertificates` inhabited at a point where the gate actually
  **fires** -- and by a `wrepr` that is *not* a bracket member at the node where
  the gate fails, so the gating is not cosmetic and the ungated form is strictly
  stronger.  Without it a gated premise could be satisfied by never firing and
  the third conjunct would be vacuous while the module compiled green;
* `denseLocalCertificates_selected_data_consistent`, the **joint** readout: one
  coordinate that is simultaneously good (root support `3` = the frozen ceiling,
  attained) and a surviving witness whose density `3/4` is strictly above
  `omega = 1/2` and which therefore meets the odd-copy column floor `2`.
  Without it the witness clause of `denseLocalCertificates` could be quantified
  over a set the other premises force empty while the module compiled green;
* `denseLocalCertificates_hypotheses_consistent`, the **numeric shape** of the
  whole bundle -- both inherited certificates at once, at the frozen floor
  `B_cap >= 3` -- shown simultaneously satisfiable with both frozen conclusions,
  so nothing in the bundle is self-contradictory.

## Honest scope and recorded coverage limits

1. **No routing statement is made.**  The threshold arithmetic of SS1 is
   arithmetic of a geometric sequence.  `lem:dense-routing` (`08:878--894`) is
   not stated, not proved, and not implied by anything here.
2. **The token device is bookkeeping, not construction.**  `tokenWeight` records
   the frozen weights on the banked selected data.  Nothing here asserts that a
   token *has* the certificate it is said to represent; that is exactly what
   `lem:dense-local-certificates` states, and it is proved only in the
   conditional form of SS3.
3. **Both inherited certificates stay named hypotheses.**  The Stage-1
   certificate `eq:stage1-robust-certificate` and the odd-copy capacity
   inequality `eq:local-capacity-gap` are hypotheses (`hcert`, `hgap`); neither
   is asserted, and neither is inhabited here at a concrete matrix.  The
   obstruction is recorded, not hidden: `ordinaryToken_hard_pole_at_constant`
   shows the conclusion **fails** on the constant matrix, so `hcert` is genuine
   inherited content, and `stage1Certificate_family_nonempty` shows the
   certificate cannot be met by an empty bracket family.  This is the same
   coverage limit the banked `StageOneInterlace` records for
   `stage1RobustCertificate` and the banked `RawStageFour` records for
   `localCapacityGap`.
4. **The representative choice is a hypothesis, not a construction.**
   `08:854--860` chooses one physical representative of every retained quotient
   value and of every value in `P_alpha`, and asserts that the result lies in
   `[M_1^T, 1, 2^{-b_1}, 3/5]`.  Performing that choice needs the restriction
   machinery the block does not build, so it enters as `hrepr` (and `hwrepr` for
   the `q_1 + 3`-copy scaffold of `08:864--871`).  A later tranche may not cite
   this module as having supplied either.  `hwrepr` is **node-indexed and
   density-gated** after the `cc-t2l-r1` repair: it asserts the scaffold only at
   the `(node, coordinate)` pairs where the frozen density hypothesis holds, and
   it asserts nothing about *how* the node's surviving columns produce it.  In
   particular this module does **not** prove that a node whose support density
   exceeds `omega` admits such a rectangle -- that is the content of
   `08:864--871`, and it remains a hypothesis.
5. **The upper-fibre estimate is transcribed as arithmetic of the banked gate.**
   `denseFibre_estimate` derives `x_dom/(1 + eps_2) >= 98/100 > 3/5` from the
   fifth clause of the banked `denseSeparationGates`.  The *application* of the
   balanced family to the indexed set `S_{j_*}` (`08:846--851`) has no
   declaration here, and `EXPANDER-001` keeps its status: no Lean declaration,
   no axiom.
6. **`b_1`, `q_2`, `|C_1|` and `B_cap` are binders, not values.**  `lambdaAt`
   takes `q_2` and `b_1` as explicit natural arguments, the quotient carrier
   `Gamma` is a binder standing for `C_1`, and `B_cap` enters as
   `bCap Dsrc a`.  No parameter schedule may be read out of any witness below:
   `tokenWeight_nondegenerate` and the two support probes are separating probes
   of the definitions at deliberately small carriers, and say so.
7. **Candidate B is race evidence with a recorded disposition.**  See the
   disposition note at the end of SS5: `TokenObject` is consumed by nothing and
   may not be used to re-encode the bookkeeping of `08:818--823` without a fresh
   judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseRoutingThresholds

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

/-! ## §1  The routing thresholds `eq:routing-threshold` (`08:811--816`)

"For suffix depth `d >= 0`, define `lambda_d = lambda_0 2^{-d} = 2 q_2 2^{-b_1}
2^{-d}`."  The root value is the banked `lambdaZero`, consumed by pin so that
this sequence and the banked routing slack speak about one object. -/

/-- `lambda_d = lambda_0 2^{-d}` (`08:812--816`), written as a quotient so that
the frozen negative exponent needs no integer exponentiation.  `q_2` and `b_1`
are explicit binders: certifying the Stage-1 robustness depth is Stage-1 work
with no declaration here. -/
noncomputable def lambdaAt (q₂ b₁ d : ℕ) : ℝ := lambdaZero q₂ b₁ / 2 ^ d

/-- **Aux 1 (the root value).**  `lambda_0` is the banked root threshold.
General. -/
theorem lambdaAt_zero (q₂ b₁ : ℕ) : lambdaAt q₂ b₁ 0 = lambdaZero q₂ b₁ := by
  simp [lambdaAt]

/-- **Aux 2 (the halving step).**  `lambda_{d+1} = lambda_d/2`, the frozen
recurrence.  General.

This is arithmetic of the sequence.  It is **not** a routing statement: the
frozen use of it at `08:902` belongs to `lem:dense-routing`, which has no
declaration in this module. -/
theorem lambdaAt_succ (q₂ b₁ d : ℕ) :
    lambdaAt q₂ b₁ (d + 1) = lambdaAt q₂ b₁ d / 2 := by
  simp [lambdaAt, pow_succ, div_div]

/-- **Aux 3 (the frozen closed form).**  `lambda_d = 2 q_2 2^{-(b_1 + d)}`, the
second equality of `eq:routing-threshold`.  General. -/
theorem lambdaAt_eq (q₂ b₁ d : ℕ) :
    lambdaAt q₂ b₁ d = 2 * (q₂ : ℝ) / 2 ^ (b₁ + d) := by
  simp [lambdaAt, lambdaZero, pow_add, div_div]

/-- **Aux 4 (range).**  Every threshold is nonnegative.  General. -/
theorem lambdaAt_nonneg (q₂ b₁ d : ℕ) : 0 ≤ lambdaAt q₂ b₁ d := by
  unfold lambdaAt
  have := lambdaZero_nonneg q₂ b₁
  positivity

/-- **Aux 5 (monotone in the suffix depth).**  The thresholds decrease with
depth.  General. -/
theorem lambdaAt_antitone (q₂ b₁ : ℕ) {d d' : ℕ} (h : d ≤ d') :
    lambdaAt q₂ b₁ d' ≤ lambdaAt q₂ b₁ d := by
  unfold lambdaAt
  have h0 : (0 : ℝ) < 2 ^ d := by positivity
  have h1 : (2 : ℝ) ^ d ≤ 2 ^ d' := pow_le_pow_right₀ (by norm_num) h
  exact div_le_div_of_nonneg_left (lambdaZero_nonneg q₂ b₁) h0 h1

/-- **Aux 6.**  Every threshold is at most the root threshold.  General. -/
theorem lambdaAt_le_lambdaZero (q₂ b₁ d : ℕ) :
    lambdaAt q₂ b₁ d ≤ lambdaZero q₂ b₁ := by
  have := lambdaAt_antitone q₂ b₁ (Nat.zero_le d)
  rwa [lambdaAt_zero] at this

/-- **Aux 7 (the geometric partial sum).**  `sum_{d < n} lambda_{d+1}
= lambda_0 (1 - 2^{-n})`; in particular the tail sums stay strictly below
`lambda_0` at every finite depth.  General.

Again this is arithmetic of the sequence.  The frozen use of the limiting form
`sum_{d >= 0} lambda_{d+1} = lambda_0` at `08:937--940` is a step inside
`lem:dense-routing`, which has no declaration in this module; nothing here says
a witness routed whole forever retains its bonus certificate. -/
theorem sum_lambdaAt_succ (q₂ b₁ n : ℕ) :
    ∑ d ∈ Finset.range n, lambdaAt q₂ b₁ (d + 1)
      = lambdaZero q₂ b₁ * (1 - 1 / 2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, lambdaAt]
      have h : (0 : ℝ) < 2 ^ n := by positivity
      field_simp
      ring

/-- **Aux 8 (the value at the frozen width exponent).**  At `q_2 = 2^r` and
suffix depth `r` the threshold is `2^{1 - b_1}`, written as `2/2^{b_1}`.
General in `r` and `b_1`.

This is the arithmetic identity that `08:963--965` reads off; the surrounding
no-leaf argument (`lem:dense-no-leaf`, `08:955--979`) has no declaration
here. -/
theorem lambdaAt_at_depth_log (r b₁ : ℕ) :
    lambdaAt (2 ^ r) b₁ r = 2 / 2 ^ b₁ := by
  unfold lambdaAt lambdaZero
  have h1 : (0 : ℝ) < 2 ^ r := by positivity
  have h2 : (0 : ℝ) < 2 ^ b₁ := by positivity
  have hc : (((2 : ℕ) ^ r : ℕ) : ℝ) = 2 ^ r := by push_cast; ring
  rw [hc]
  field_simp

/-! ## §2  The token bookkeeping (`08:818--823`, Candidate A)

`08:819--823`: "For each coordinate in `H`, place one *ordinary token*,
representing a `B_cap`-hard one-copy restriction of `M_1^T`.  For each
coordinate in `W`, attach one additional *bonus token* to its ordinary token.
Until the pair is split, it is a single weight-two witness object and represents
the stronger `B_cap + 1` local capacity restriction."

Candidate A makes the device a *derived weight* on the banked selected data.
The frozen "attach one additional bonus token to its ordinary token" is the
increment from `1` to `2`, and "a single weight-two witness object" is the value
`2`.  That the bonus can be attached to an ordinary token at all -- i.e. that
`W` sits inside `H` -- is the banked
`DenseBranchSelection.selectedWitness_subset_selectedGood`, consumed by pin and
never restated. -/

section Tokens

variable {Coord : Type*} [Fintype Coord] [DecidableEq Coord]

/-- The frozen token weight at a good coordinate (`08:819--823`): `2` on a
witness object (ordinary token plus its bonus token) and `1` on a bare ordinary
token.  No certificate is stored: the weight is a function of the banked
selected data. -/
def tokenWeight (U B : Finset Coord) (α : Coord) : ℕ :=
  if α ∈ selectedWitness U B then 2 else 1

omit [Fintype Coord] in
/-- **Aux 9 (round trip, witness side).**  A coordinate carries a weight-two
witness object exactly when it is a surviving witness.  General. -/
theorem tokenWeight_eq_two_iff (U B : Finset Coord) (α : Coord) :
    tokenWeight U B α = 2 ↔ α ∈ selectedWitness U B := by
  unfold tokenWeight
  split <;> simp_all

omit [Fintype Coord] in
/-- **Aux 10 (round trip, ordinary side).**  A coordinate carries a bare
ordinary token exactly when it is not a surviving witness.  General. -/
theorem tokenWeight_eq_one_iff (U B : Finset Coord) (α : Coord) :
    tokenWeight U B α = 1 ↔ α ∉ selectedWitness U B := by
  unfold tokenWeight
  split <;> simp_all

omit [Fintype Coord] in
/-- **Aux 11 (range, lower).**  Every good coordinate carries at least its
ordinary token.  General. -/
theorem one_le_tokenWeight (U B : Finset Coord) (α : Coord) :
    1 ≤ tokenWeight U B α := by
  unfold tokenWeight
  split <;> norm_num

omit [Fintype Coord] in
/-- **Aux 12 (range, upper).**  The frozen device attaches **one** bonus token,
so no object has weight three.  General. -/
theorem tokenWeight_le_two (U B : Finset Coord) (α : Coord) :
    tokenWeight U B α ≤ 2 := by
  unfold tokenWeight
  split <;> norm_num

omit [Fintype Coord] in
/-- **Aux 13 (degenerate end, no witnesses).**  With no surviving witnesses
every object is a bare ordinary token.  General. -/
theorem tokenWeight_of_no_witness (B : Finset Coord) (α : Coord) :
    tokenWeight (∅ : Finset Coord) B α = 1 := by
  rw [tokenWeight_eq_one_iff, selectedWitness]
  simp

omit [Fintype Coord] in
/-- **Aux 14 (degenerate end, no bad coordinates).**  With no bad coordinates
the witness objects sit exactly on `U`.  General. -/
theorem tokenWeight_of_no_bad (U : Finset Coord) (α : Coord) :
    tokenWeight U (∅ : Finset Coord) α = 2 ↔ α ∈ U := by
  rw [tokenWeight_eq_two_iff, selectedWitness_self]

/-- **Aux 15 (the frozen total mass).**  The total token weight carried by the
good set is `|H| + |W|`: one unit for every ordinary token and one more for
every bonus token.  This is the quantity the frozen conservation identity of
`08:997` starts from, and it is a **theorem** about the device rather than a
stored field.  General in `U` and `B`. -/
theorem sum_tokenWeight (U B : Finset Coord) :
    ∑ α ∈ selectedGood B, tokenWeight U B α
      = (selectedGood B).card + (selectedWitness U B).card := by
  classical
  have hsplit : ∀ α : Coord,
      tokenWeight U B α = 1 + (if α ∈ selectedWitness U B then 1 else 0) := by
    intro α
    unfold tokenWeight
    split <;> norm_num
  have hfil : (selectedGood B).filter (fun α => α ∈ selectedWitness U B)
      = selectedWitness U B := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right]
    exact selectedWitness_subset_selectedGood U B
  calc ∑ α ∈ selectedGood B, tokenWeight U B α
      = ∑ α ∈ selectedGood B, (1 + if α ∈ selectedWitness U B then 1 else 0) := by
        exact Finset.sum_congr rfl fun α _ => hsplit α
    _ = (selectedGood B).card
          + ∑ α ∈ selectedGood B, (if α ∈ selectedWitness U B then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ = (selectedGood B).card + (selectedWitness U B).card := by
        rw [← Finset.card_filter, hfil]

end Tokens

/-! ## §3  `lem:dense-local-certificates` (`08:825--876`)

"Every ordinary token has root quotient support at least `p_root |C_1|`.  Every
unsplit witness object remains a valid `B_cap + 1` certificate whenever its
quotient support density is greater than `omega`."

The two halves are transcribed separately and then conjoined.  Following
coverage limits 3--5, the two inherited certificates and the two representative
choices stay named hypotheses. -/

/-! ### The frozen scalars of `08:846--876` -/

/-- **Aux 16.**  The banked `xSeed b_1 = 2^{-b_1}` as a quotient, so that it can
be compared with the routing thresholds without leaving `rpow`.  General. -/
theorem xSeed_eq_inv_pow (b₁ : ℕ) : xSeed b₁ = 1 / 2 ^ b₁ := by
  unfold xSeed
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp [one_div]

/-- **Aux 17 (`08:854`, second inequality).**  `lambda_0 >= 2^{-b_1}` at every
positive width, because `lambda_0 = 2 q_2 2^{-b_1}`.  General. -/
theorem xSeed_le_lambdaZero {q₂ : ℕ} (b₁ : ℕ) (hq : 1 ≤ q₂) :
    xSeed b₁ ≤ lambdaZero q₂ b₁ := by
  rw [xSeed_eq_inv_pow, lambdaZero]
  have hp : (0 : ℝ) < 2 ^ b₁ := by positivity
  have hq' : (1 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq
  rw [div_le_div_iff_of_pos_right hp]
  linarith

/-- **`08:854`, the frozen chain `p_root >= lambda_0 >= 2^{-b_1}`.**  Under the
banked routing slack `eq:routing-slack` (`08:805--810`) -- carried as a
hypothesis, never asserted -- the root density dominates the Stage-1 seed
density.  This is what makes the representative choice of `08:855--860` a
choice at row density at least `2^{-b_1}`.  General. -/
theorem xSeed_le_pRoot {q₂ : ℕ} (b₁ : ℕ) (hq : 1 ≤ q₂) (hslack : RoutingSlack q₂ b₁) :
    xSeed b₁ ≤ pRoot :=
  le_trans (xSeed_le_lambdaZero b₁ hq) hslack.1

/-- **Aux 18 (`08:874`).**  `omega = 1/2 > 9/25`, the frozen comparison that
turns a witness support-density threshold into the column density of
`eq:local-capacity-gap`. -/
theorem omegaRoute_gt_capacity_density : (9 : ℝ) / 25 < omegaRoute := by
  rw [omegaRoute_eq]; norm_num

/-- **`08:846--853`, the arithmetic readout of the upper-fibre estimate.**  The
fifth clause of the banked `eq:dense-separation-gates` is
`49/100 <= (x_dom/2)/(1 + eps_2)`; doubling it gives the frozen
`x_dom/(1 + eps_2) >= 98/100`, which is `> 3/5`.

This is arithmetic of the banked gate **only**.  It does not assert that the
cited `(q_2,t_2,eps_2)`-balanced family exists, that `S_{j_*}` has density at
least `x_dom`, or that any indexed set attains the estimate: the application of
`08:846--851` has no declaration in this module, and `EXPANDER-001` keeps its
status as a cited fact with no Lean declaration.  General. -/
theorem denseFibre_estimate {s bT m₃ : ℕ} {ε₂ : ℝ}
    (hg : denseSeparationGates s bT m₃ ε₂) :
    (98 : ℝ) / 100 ≤ xDom s bT m₃ / (1 + ε₂)
      ∧ (3 : ℝ) / 5 < xDom s bT m₃ / (1 + ε₂) := by
  obtain ⟨-, -, -, -, h⟩ := hg
  have hrw : xDom s bT m₃ / 2 / (1 + ε₂) = xDom s bT m₃ / (1 + ε₂) / 2 := by
    rw [div_div, div_div, mul_comm]
  rw [hrw] at h
  exact ⟨by linarith, by linarith⟩

/-! ### The ordinary half (`08:825--828`, `08:833--862`) -/

section Ordinary

variable {Phys Coord Γ : Type*} [Fintype Coord] [DecidableEq Coord]
  [DecidableEq Γ] [Fintype Γ]

/-- **`lem:dense-local-certificates`, first assertion, ceiling form
(`08:827--828`, proof `08:834--838`).**  "Membership in `H = [q_2] \ B_{j_*}`
excludes the diagonal-bad set.  By its definition, at least
`ceil((1 - rho_loc)|C_1|)` quotient columns survive."

The frozen ceiling is preserved: what is proved is the ceiling bound, and the
real bound `p_root |C_1| <= support` below is its consequence.  `p_root` is the
banked `pRoot = 1 - rho_loc` at the banked pinned `rho_loc`, and the diagonal
filter is the banked `diagonalBadSet`, so the two speak about one object.

The frozen caveat of `08:836--838` is respected by the shape of the statement:
the conclusion is quantified over `alpha` in the **good** set only, and no
uniform every-coordinate survival statement appears.  General. -/
theorem ordinaryToken_root_support_ceiling
    (rep : Phys → Coord × Γ) (S₀ : Finset Phys) (B : Finset Coord)
    (hbad : diagonalBadSet (Fintype.card Γ)
      (fun α => (quotientSupport rep S₀ α).card) ⊆ B)
    {α : Coord} (hα : α ∈ selectedGood B) :
    ⌈pRoot * (Fintype.card Γ : ℝ)⌉₊ ≤ (quotientSupport rep S₀ α).card := by
  rw [mem_selectedGood] at hα
  have hnot : α ∉ diagonalBadSet (Fintype.card Γ)
      (fun α => (quotientSupport rep S₀ α).card) := fun h => hα (hbad h)
  rw [mem_diagonalBadSet] at hnot
  rw [pRoot]
  exact Nat.not_lt.1 hnot

/-- **`lem:dense-local-certificates`, first assertion (`08:827--828`).**  "Every
ordinary token has root quotient support at least `p_root |C_1|`."  The real
form, obtained from the ceiling form by `Nat.le_ceil`.  General. -/
theorem ordinaryToken_root_support
    (rep : Phys → Coord × Γ) (S₀ : Finset Phys) (B : Finset Coord)
    (hbad : diagonalBadSet (Fintype.card Γ)
      (fun α => (quotientSupport rep S₀ α).card) ⊆ B)
    {α : Coord} (hα : α ∈ selectedGood B) :
    pRoot * (Fintype.card Γ : ℝ) ≤ ((quotientSupport rep S₀ α).card : ℝ) := by
  have h := ordinaryToken_root_support_ceiling rep S₀ B hbad hα
  have hceil : pRoot * (Fintype.card Γ : ℝ) ≤ (⌈pRoot * (Fintype.card Γ : ℝ)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hcast : ((⌈pRoot * (Fintype.card Γ : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ ((quotientSupport rep S₀ α).card : ℝ) := by exact_mod_cast h
  linarith

end Ordinary

/-- **`08:861--862`, the consumption form of `eq:stage1-robust-certificate`.**
"The Stage-1 certificate makes this restriction `B_cap`-hard."  A three-rung
lower bound `B_cap <= Lambda_3(M, 1, x, y)` bounds its own top rung (the banked
`StageTwoRelaxed.LambdaGE_le_top_rung`), and the top rung is a `Nat.sInf` over
the bracket family, so **every** member of the family has complexity at least
`B_cap`.  General in the matrix, the densities and the bound.

The Stage-1 certificate itself is **not** asserted here: it is the banked
`StageOneInterlace.stage1RobustCertificate`, whose own three transported rungs
remain named hypotheses there. -/
theorem stage1Certificate_le_member {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) (x y : ℝ) {bc : ℕ} (hcert : bc ≤ LambdaGE M 1 x y)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hRC : RC ∈ bracketGE X Y 1 x y) :
    bc ≤ D (subgame (interlaceFun M 1) RC.1 RC.2) :=
  le_trans (le_trans hcert (LambdaGE_le_top_rung M x y)) (Nat.sInf_le ⟨RC, hRC, rfl⟩)

/-- **The Stage-1 certificate forces a nonempty bracket family.**  `Dfamily` is
a `Nat.sInf` and returns `0` on the empty family, so a family lower bound taken
without nonemptiness would be unsound.  A positive certificate is immune.
General.  (The odd-copy twin of this readout is the banked
`RawStageFour.localCapacityGap_family_nonempty`, consumed by pin.) -/
theorem stage1Certificate_family_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) (x y : ℝ) {bc : ℕ} (hbc : 0 < bc)
    (hcert : bc ≤ LambdaGE M 1 x y) :
    (bracketGE X Y 1 x y).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have htop : LambdaGE M 1 x y ≤ Dfamily (interlaceFun M 1) (bracketGE X Y 1 x y) :=
    LambdaGE_le_top_rung M x y
  rw [hempty, Dfamily_empty] at htop
  omega

/-- **`lem:dense-local-certificates`, the ordinary token's certificate
(`08:820--821`, `08:854--862`).**  An ordinary token "represents a `B_cap`-hard
one-copy restriction of `M_1^T`": once the representative choice of
`08:855--860` has produced a member `repr alpha` of
`[M_1^T, 1, 2^{-b_1}, 3/5]`, the Stage-1 certificate makes that restriction
`B_cap`-hard.

Both deep inputs are named hypotheses: `hcert` carries
`eq:stage1-robust-certificate` and `hrepr` carries the representative choice.
General in the matrix, the carriers, `Dsrc`, `a`, `b_1` and the good set.

*Why the trivial witness fails.*  The conclusion is a lower bound on the
complexity of a **specific** retained subgame, and it is false without `hcert`:
`ordinaryToken_hard_pole_at_constant` exhibits a legal bracket member of a
constant matrix whose subgame has complexity `0 < B_cap`.  So the statement is
not "some number is at most some number"; it is the transported Stage-1
certificate. -/
theorem ordinaryToken_is_Bcap_hard {X Y Coord : Type*} [Fintype X] [Fintype Y]
    [Fintype Coord] [DecidableEq Coord]
    (M1T : X → Y → Bool) {Dsrc a b₁ : ℕ} (B : Finset Coord)
    (repr : Coord → Finset (Fin 1 × X) × Finset (Fin 1 → Y))
    (hcert : bCap Dsrc a ≤ LambdaGE M1T 1 (xSeed b₁) (3 / 5))
    (hrepr : ∀ α ∈ selectedGood B, repr α ∈ bracketGE X Y 1 (xSeed b₁) (3 / 5))
    {α : Coord} (hα : α ∈ selectedGood B) :
    bCap Dsrc a ≤ D (subgame (interlaceFun M1T 1) (repr α).1 (repr α).2) :=
  stage1Certificate_le_member M1T (xSeed b₁) (3 / 5) hcert (hrepr α hα)

/-! ### The witness half (`08:828--830`, `08:864--876`) -/

section Witness

variable {Phys Coord Γ : Type*} [DecidableEq Coord] [DecidableEq Γ] [Fintype Γ]

/-- **`08:872--875`, the density step of the witness certificate.**  "Projection
of the full product `C_1` has no balancedness loss, as recorded by `eps_1 = 0`.
Hence witness support density greater than `omega = (1 + eps_1)/2 = 1/2 > 9/25`
gives complexity at least `B_cap + 1`."

Transcribed is exactly the step that makes the odd-copy bracket applicable: a
quotient support whose density exceeds the banked `omegaRoute` meets the column
floor `ceil((9/25)|C_1|)` of `eq:local-capacity-gap`.  The ceiling is preserved.
General.

*Why the trivial witness fails.*  The floor is a genuine constraint:
`witnessColumns_pole_below_omega` exhibits a support at density `8/25 < omega`
that misses it, so the density hypothesis is load-bearing and the conclusion is
not automatic. -/
theorem witnessDensity_meets_capacity_columns
    (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord)
    (hΓ : 0 < Fintype.card Γ) (hdens : omegaRoute < quotientDensity rep S α) :
    ⌈(9 : ℝ) / 25 * (Fintype.card Γ : ℝ)⌉₊ ≤ (quotientSupport rep S α).card := by
  have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hΓ
  have hgt : (9 : ℝ) / 25 < quotientDensity rep S α :=
    lt_trans omegaRoute_gt_capacity_density hdens
  rw [quotientDensity, lt_div_iff₀ hpos] at hgt
  refine Nat.ceil_le.2 ?_
  linarith

end Witness

/-- **`lem:dense-local-certificates`, the witness object's certificate
(`08:822--823`, `08:864--876`).**  An unsplit witness object "represents the
stronger `B_cap + 1` local capacity restriction": once the diagonal scaffold of
`08:864--871` has produced a member `RC` of the odd-copy bracket
`[R, q_1 + 3, x_cap, 9/25]`, the inherited capacity inequality
`eq:local-capacity-gap` makes **that** restriction `B_cap + 1`-hard.

The inherited inequality is the banked `StageThreeExactScale.localCapacityGap`,
consumed **by pin** through `RawStageFour.localCapacityGap_le_member` and never
restated.  General in the source matrix, the carriers, the slot binding and
`Dsrc`.

*Repair note (tranche `cc-t2l-r1`).*  This helper takes **the rectangle
directly**.  It previously took a `Coord`-indexed family `wrepr` together with
an ungated membership hypothesis, which forced every caller to fix one
node-independent rectangle per coordinate before the protocol node was even
bound; the frozen sentence `08:828--830` certifies the restriction cut out by
the columns surviving **at the node** (`08:871--875`), so the rectangle is
node data and this helper must not name a coordinate at all.  Nothing about
selection, nodes or density belongs in the odd-copy readout: it says only that
a member of the odd-copy bracket is `B_cap + 1`-hard.

*Why the trivial witness fails.*  The banked
`RawStageFour.localCapacityGap_not_automatic` exhibits a legal seed at which the
inherited inequality is **false**, so `hgap` is genuine content and the
conclusion is not a restatement of its own hypothesis. -/
theorem witnessToken_is_Bcap_succ_hard {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Stage1SlotBinding) (Rsrc : X → Y → Bool) {b₀ Dsrc : ℕ}
    (RC : Finset (Fin (F.q₁ + 3) × X) × Finset (Fin (F.q₁ + 3) → Y))
    (hgap : localCapacityGap F Rsrc b₀ Dsrc)
    (hRC : RC ∈ bracketGE X Y (F.q₁ + 3) (xCap F b₀) (9 / 25)) :
    bCap Dsrc F.a + 1
      ≤ D (subgame (interlaceFun Rsrc (F.q₁ + 3)) RC.1 RC.2) := by
  have h := localCapacityGap_le_member F Rsrc b₀ Dsrc hgap hRC
  rw [bCap_eq]
  exact h

/-! ### The frozen lemma -/

/-- **`lem:dense-local-certificates` (`08:825--831`).**

"Every ordinary token has root quotient support at least `p_root |C_1|`.  Every
unsplit witness object remains a valid `B_cap + 1` certificate whenever its
quotient support density is greater than `omega`."

The three conclusions printed here are, in the frozen order: the root survival
bound at the frozen ceiling; the `B_cap`-hardness the ordinary token represents;
and, **at each protocol node `S`**, for a surviving witness whose support density
at that node exceeds `omega`, both the odd-copy column floor and the
`B_cap + 1` hardness of the rectangle cut out at that node.

Every deep input is an explicit named binder and none is an axiom:
`hbad` is the banked diagonal-bad definition applied to the selected bad set;
`hcert` is `eq:stage1-robust-certificate`; `hgap` is `eq:local-capacity-gap`;
`hrepr` and `hwrepr` are the two representative choices of `08:855--860` and
`08:864--871`.  In particular `EXPANDER-001` has no Lean declaration and appears
in no hypothesis of this statement.

*The node index (repair, tranche `cc-t2l-r1`).*  The frozen witness half is an
implication **at each node**: "Every unsplit witness object remains a valid
`B_cap + 1` certificate whenever its quotient support density is greater than
`omega`" (`08:828--830`), and the frozen proof reaches that conclusion through
the columns that survive at the node -- projection of `C_1` has no
balancedness loss, so it is the *current* support density exceeding
`omega = 1/2 > 9/25` that places the *current* restriction in the odd-copy
bracket (`08:871--875`).  Three things therefore sit under the `S` binder:

* `wrepr` is indexed by the node **and** the coordinate, `Finset Phys ->
  Coord -> ...`, because the diagonal scaffold of `08:864--871` is built from
  the columns surviving at `S`;
* the bracket membership `hwrepr` is **gated on the density**, so nothing is
  assumed at nodes where the frozen hypothesis fails -- assuming membership
  unconditionally would assume strictly more than the paper states;
* the hardness conclusion is stated at the **node-indexed** rectangle
  `wrepr S alpha`, so the certified object is the one the node cut out.

`witnessCertificate_pole_node_dependent` shows the index is load-bearing: at one
carrier the same coordinate is above `omega` at one node and below it at
another, so a node-independent `wrepr` cannot be instantiated by the node's own
restriction, and this is exactly the interface `lem:dense-routing`
(`08:878--944`) consumes when it says a witness routed whole "retains its bonus
certificate".

*Consistency.*  The bundle conjoins facts about **one** construction, not two
cases of a promise split: `hcert` and `hgap` are the two inherited certificates
that `08:820--823` names side by side for the two token kinds.
`denseLocalCertificates_hypotheses_consistent` exhibits the whole bundle's
numeric shape as simultaneously satisfiable with both conclusions at the frozen
floor `B_cap >= 3`, so no contradiction follows from it, and
`witnessRepr_gate_nonvacuous` inhabits the gated `hwrepr` at a point where the
density gate actually **fires**, so the third conjunct is not satisfied
vacuously. -/
theorem denseLocalCertificates
    {Phys Coord Γ X Y Xs Ys : Type*} [Fintype Coord] [DecidableEq Coord]
    [DecidableEq Γ] [Fintype Γ] [Fintype X] [Fintype Y] [Fintype Xs] [Fintype Ys]
    (rep : Phys → Coord × Γ) (S₀ : Finset Phys) (U B : Finset Coord)
    (M1T : X → Y → Bool) (F : Stage1SlotBinding) (Rsrc : Xs → Ys → Bool)
    {Dsrc b₀ b₁ : ℕ}
    (repr : Coord → Finset (Fin 1 × X) × Finset (Fin 1 → Y))
    (wrepr : Finset Phys → Coord →
      Finset (Fin (F.q₁ + 3) × Xs) × Finset (Fin (F.q₁ + 3) → Ys))
    (hΓ : 0 < Fintype.card Γ)
    (hbad : diagonalBadSet (Fintype.card Γ)
      (fun α => (quotientSupport rep S₀ α).card) ⊆ B)
    (hcert : bCap Dsrc F.a ≤ LambdaGE M1T 1 (xSeed b₁) (3 / 5))
    (hrepr : ∀ α ∈ selectedGood B, repr α ∈ bracketGE X Y 1 (xSeed b₁) (3 / 5))
    (hgap : localCapacityGap F Rsrc b₀ Dsrc)
    (hwrepr : ∀ (S : Finset Phys), ∀ α ∈ selectedWitness U B,
      omegaRoute < quotientDensity rep S α →
        wrepr S α ∈ bracketGE Xs Ys (F.q₁ + 3) (xCap F b₀) (9 / 25)) :
    (∀ α ∈ selectedGood B,
        ⌈pRoot * (Fintype.card Γ : ℝ)⌉₊ ≤ (quotientSupport rep S₀ α).card
        ∧ pRoot * (Fintype.card Γ : ℝ) ≤ ((quotientSupport rep S₀ α).card : ℝ))
      ∧ (∀ α ∈ selectedGood B,
          bCap Dsrc F.a ≤ D (subgame (interlaceFun M1T 1) (repr α).1 (repr α).2))
      ∧ (∀ (S : Finset Phys), ∀ α ∈ selectedWitness U B,
          omegaRoute < quotientDensity rep S α →
            ⌈(9 : ℝ) / 25 * (Fintype.card Γ : ℝ)⌉₊ ≤ (quotientSupport rep S α).card
            ∧ bCap Dsrc F.a + 1
                ≤ D (subgame (interlaceFun Rsrc (F.q₁ + 3))
                      (wrepr S α).1 (wrepr S α).2)) := by
  refine ⟨fun α hα => ⟨ordinaryToken_root_support_ceiling rep S₀ B hbad hα,
      ordinaryToken_root_support rep S₀ B hbad hα⟩,
    fun α hα => ordinaryToken_is_Bcap_hard M1T B repr hcert hrepr hα, ?_⟩
  intro S α hα hdens
  exact ⟨witnessDensity_meets_capacity_columns rep S α hΓ hdens,
    witnessToken_is_Bcap_succ_hard F Rsrc (wrepr S α) hgap (hwrepr S α hα hdens)⟩

/-! ## §4  Non-vacuity, statement poles and consistency probes

Every predicate transcribed above is a `Prop` the module only consumes, and
every definition is a carrier a later tranche will read.  An unsatisfiable
premise bundle or a degenerate carrier would make every consumer vacuous while
compiling green, so each is probed here.  No parameter schedule may be read out
of any witness below. -/

/-- **Non-vacuity of the threshold sequence, symbolic in the frozen width.**
For **every** `q_2` there is a certified Stage-1 robustness depth at which the
whole sequence `lambda_d` is nondegenerate: strictly positive, strictly below
`1/4`, and strictly decreasing in the suffix depth.  Nothing is evaluated -- the
witness `b_1 = q_2 + 4` runs on the banked `self_lt_two_pow` -- so this reaches
the frozen widths `q_2 >= 6144`, which no evaluable literal reaches.

The strictness needs `0 < q_2`; at `q_2 = 0` the sequence is identically `0`,
which is why the frozen carrier `[q_2]` is nonempty. -/
theorem lambdaAt_nondegenerate {q₂ : ℕ} (hq : 0 < q₂) :
    ∃ b₁ : ℕ, (∀ d : ℕ, 0 < lambdaAt q₂ b₁ d ∧ lambdaAt q₂ b₁ d < 1 / 4)
      ∧ ∀ d : ℕ, lambdaAt q₂ b₁ (d + 1) < lambdaAt q₂ b₁ d := by
  obtain ⟨b₁, hsmall, -⟩ := routingSlack_nondegenerate q₂
  refine ⟨b₁, fun d => ⟨?_, ?_⟩, fun d => ?_⟩
  · have hq' : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq
    have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
    have hd : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    unfold lambdaAt lambdaZero
    positivity
  · exact lt_of_le_of_lt (lambdaAt_le_lambdaZero q₂ b₁ d) hsmall
  · rw [lambdaAt_succ]
    have hpos : 0 < lambdaAt q₂ b₁ d := by
      have hq' : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq
      have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
      have hd : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      unfold lambdaAt lambdaZero
      positivity
    linarith

/-- **Statement pole for the threshold sequence.**  The frozen thresholds are a
*strictly decreasing* sequence at every positive width, so substituting the
constant sequence `lambda_d = lambda_0` for `eq:routing-threshold` would be a
different -- and stronger -- statement.  At `q_2 = 1`, `b_1 = 0` the root value
is `2` while every later value is strictly smaller. -/
theorem lambdaAt_pole_strictly_below_root :
    lambdaAt 1 0 0 = 2 ∧ lambdaAt 1 0 1 = 1 ∧ lambdaAt 1 0 1 < lambdaAt 1 0 0 := by
  have h0 : lambdaAt 1 0 0 = 2 := by
    rw [lambdaAt_zero, lambdaZero]; norm_num
  have h1 : lambdaAt 1 0 1 = 1 := by
    unfold lambdaAt lambdaZero; norm_num
  exact ⟨h0, h1, by rw [h0, h1]; norm_num⟩

/-- **Separating probe of the token bookkeeping.**  At an eight-element
coordinate type with `B = {0,1}` and `U = {1,2,3}` -- the same probe point the
banked `selectedMass_separating_probe` uses -- **both** frozen weights actually
occur: coordinate `2` carries a weight-two witness object and coordinate `4`
carries a bare ordinary token.  No bonus sits outside the good set (coordinate
`1` is bad, hence carries no object at all), and the frozen total mass over `H`
is `|H| + |W| = 6 + 2 = 8`.

This is a probe of the definitions at a deliberately small carrier and is
**not** a schedule instance: the frozen carrier is `[q_2]` with
`q_2 >= 64 s q_1/zeta >= 6144` (`08:681`).  No later tranche may read
`q_2 = 8` as legal. -/
theorem tokenWeight_nondegenerate :
    tokenWeight ({1, 2, 3} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8)) 2 = 2 ∧
    tokenWeight ({1, 2, 3} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8)) 4 = 1 ∧
    (1 : Fin 8) ∉ selectedGood ({0, 1} : Finset (Fin 8)) ∧
    ∑ α ∈ selectedGood ({0, 1} : Finset (Fin 8)),
      tokenWeight ({1, 2, 3} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8)) α = 8 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [sum_tokenWeight]
  decide

/-- **Hypothesis consistency for the root survival readout (legal instance).**
The premise bundle of `ordinaryToken_root_support_ceiling` is satisfiable with
the frozen ceiling **attained**: over a two-element coordinate type and a
four-element `C_1`, the good coordinate `0` retains exactly
`ceil(p_root |C_1|) = ceil((3/4) * 4) = 3` quotient columns while the bad
coordinate `1` retains only `2` and is therefore in the banked diagonal-bad set.
The conclusion is obtained by *applying* `ordinaryToken_root_support_ceiling` to
the witness.

The support is **nondegenerate**: it is neither empty nor all of `C_1`.  This is
a probe of the definitions at a deliberately small carrier and is **not** a
schedule instance. -/
theorem ordinaryToken_root_support_hypotheses_consistent :
    ∃ (rep : Fin 5 → Fin 2 × Fin 4) (S₀ : Finset (Fin 5)) (B : Finset (Fin 2)),
      diagonalBadSet (Fintype.card (Fin 4))
          (fun α => (quotientSupport rep S₀ α).card) ⊆ B ∧
        (0 : Fin 2) ∈ selectedGood B ∧
        (quotientSupport rep S₀ 0).Nonempty ∧
        quotientSupport rep S₀ 0 ≠ Finset.univ ∧
        (quotientSupport rep S₀ 0).card = 3 ∧
        ⌈pRoot * (Fintype.card (Fin 4) : ℝ)⌉₊ ≤ (quotientSupport rep S₀ 0).card := by
  classical
  set rep : Fin 5 → Fin 2 × Fin 4 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)] with hrep
  have hceil : ⌈pRoot * (Fintype.card (Fin 4) : ℝ)⌉₊ = 3 := by
    rw [pRoot_eq, Fintype.card_fin]
    norm_num
  have hsupp0 : (quotientSupport rep Finset.univ (0 : Fin 2)).card = 3 := by decide
  have hsupp1 : (quotientSupport rep Finset.univ (1 : Fin 2)).card = 2 := by decide
  have hthr : ⌈(1 - rhoLoc) * ((Fintype.card (Fin 4) : ℕ) : ℝ)⌉₊ = 3 := by
    have hp : (1 : ℝ) - rhoLoc = pRoot := rfl
    rw [hp, pRoot_eq, Fintype.card_fin]
    norm_num
  have hsub : diagonalBadSet (Fintype.card (Fin 4))
      (fun α => (quotientSupport rep Finset.univ α).card) ⊆ ({1} : Finset (Fin 2)) := by
    have key : ∀ α : Fin 2,
        α ∈ diagonalBadSet (Fintype.card (Fin 4))
            (fun α => (quotientSupport rep Finset.univ α).card) →
          α ∈ ({1} : Finset (Fin 2)) := by
      rw [Fin.forall_fin_two]
      refine ⟨fun h0 => ?_, fun _ => Finset.mem_singleton_self 1⟩
      rw [mem_diagonalBadSet, hthr] at h0
      exact absurd h0 (by rw [hsupp0]; norm_num)
    intro α hα
    exact key α hα
  refine ⟨rep, Finset.univ, {1}, hsub, ?_, ?_, ?_, hsupp0, ?_⟩
  · rw [mem_selectedGood]; decide
  · rw [← Finset.card_pos, hsupp0]; norm_num
  · intro h
    have : (quotientSupport rep Finset.univ (0 : Fin 2)).card = 4 := by
      rw [h, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [hceil, hsupp0]

/-- **Joint consistency of the three frozen clauses (legal instance).**  The
three conclusions of `lem:dense-local-certificates` are not about disjoint
populations, and the module's two separate probes above sit at different
carriers, so this readout inhabits **one** point at which all three premises hold
**simultaneously**: a coordinate that is at once good (excluded from the banked
diagonal-bad set, root support `3 = ceil(p_root |C_1|)`, the ceiling attained)
and a surviving witness (`0 ∈ W ⊆ H`) whose support density `3/4` is **strictly**
above the frozen `omega = 1/2` and which therefore meets the odd-copy column
floor `ceil((9/25)|C_1|) = 2`.

Without this, the witness clause of `denseLocalCertificates` could be vacuous --
quantified over a set the other premises force empty -- while the whole module
compiled green.  It is a probe of the definitions at a deliberately small
carrier and is **not** a schedule instance. -/
theorem denseLocalCertificates_selected_data_consistent :
    ∃ (rep : Fin 5 → Fin 2 × Fin 4) (S₀ : Finset (Fin 5)) (U B : Finset (Fin 2)),
      diagonalBadSet (Fintype.card (Fin 4))
          (fun α => (quotientSupport rep S₀ α).card) ⊆ B ∧
        (0 : Fin 2) ∈ selectedGood B ∧
        (0 : Fin 2) ∈ selectedWitness U B ∧
        ⌈pRoot * (Fintype.card (Fin 4) : ℝ)⌉₊ = (quotientSupport rep S₀ 0).card ∧
        omegaRoute < quotientDensity rep S₀ 0 ∧
        quotientDensity rep S₀ 0 < 1 ∧
        ⌈(9 : ℝ) / 25 * (Fintype.card (Fin 4) : ℝ)⌉₊
          ≤ (quotientSupport rep S₀ 0).card := by
  classical
  set rep : Fin 5 → Fin 2 × Fin 4 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)] with hrep
  have hceil : ⌈pRoot * (Fintype.card (Fin 4) : ℝ)⌉₊ = 3 := by
    rw [pRoot_eq, Fintype.card_fin]
    norm_num
  have hsupp0 : (quotientSupport rep Finset.univ (0 : Fin 2)).card = 3 := by decide
  have hthr : ⌈(1 - rhoLoc) * ((Fintype.card (Fin 4) : ℕ) : ℝ)⌉₊ = 3 := by
    have hp : (1 : ℝ) - rhoLoc = pRoot := rfl
    rw [hp, pRoot_eq, Fintype.card_fin]
    norm_num
  have hsub : diagonalBadSet (Fintype.card (Fin 4))
      (fun α => (quotientSupport rep Finset.univ α).card) ⊆ ({1} : Finset (Fin 2)) := by
    have key : ∀ α : Fin 2,
        α ∈ diagonalBadSet (Fintype.card (Fin 4))
            (fun α => (quotientSupport rep Finset.univ α).card) →
          α ∈ ({1} : Finset (Fin 2)) := by
      rw [Fin.forall_fin_two]
      refine ⟨fun h0 => ?_, fun _ => Finset.mem_singleton_self 1⟩
      rw [mem_diagonalBadSet, hthr] at h0
      exact absurd h0 (by rw [hsupp0]; norm_num)
    intro α hα
    exact key α hα
  have hdens : quotientDensity rep Finset.univ (0 : Fin 2) = 3 / 4 := by
    rw [quotientDensity, hsupp0, Fintype.card_fin]
    norm_num
  refine ⟨rep, Finset.univ, {0}, {1}, hsub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_selectedGood]; decide
  · rw [mem_selectedWitness]; refine ⟨?_, ?_⟩ <;> decide
  · rw [hceil, hsupp0]
  · rw [hdens, omegaRoute_eq]; norm_num
  · rw [hdens]; norm_num
  · have hfloor : ⌈(9 : ℝ) / 25 * (Fintype.card (Fin 4) : ℝ)⌉₊ = 2 := by
      rw [Fintype.card_fin]
      norm_num
    rw [hfloor, hsupp0]
    norm_num

/-- **Statement pole for the root survival readout.**  The good-set membership
is load-bearing: the diagonal-bad coordinate `1` of the probe above retains only
`2 < 3 = ceil(p_root |C_1|)` quotient columns, so dropping `hα` would make the
statement false. -/
theorem ordinaryToken_root_support_pole_at_bad_coordinate :
    ∃ (rep : Fin 5 → Fin 2 × Fin 4),
      ¬ (⌈pRoot * (Fintype.card (Fin 4) : ℝ)⌉₊
          ≤ (quotientSupport rep Finset.univ (1 : Fin 2)).card) := by
  classical
  refine ⟨![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)], ?_⟩
  have hceil : ⌈pRoot * (Fintype.card (Fin 4) : ℝ)⌉₊ = 3 := by
    rw [pRoot_eq, Fintype.card_fin]
    norm_num
  have hsupp : (quotientSupport ![((0 : Fin 2), (0 : Fin 4)), (0, 1), (0, 2), (1, 0), (1, 1)]
      Finset.univ (1 : Fin 2)).card = 2 := by decide
  rw [hceil, hsupp]
  norm_num

/-- **Hypothesis consistency for the witness column floor (legal instance).**
The premise bundle of `witnessDensity_meets_capacity_columns` is satisfiable
with a density **strictly** between the frozen `omega = 1/2` and `1`: over a
`25`-element `C_1` a witness support of size `20` has density `4/5 > 1/2`, and
the frozen column floor `ceil((9/25)|C_1|) = 9` is met with room to spare.  The
conclusion is obtained by *applying* `witnessDensity_meets_capacity_columns` to
the witness.

Neither endpoint is used: the density is neither `0` nor `1`.  This is a probe
of the definitions at a deliberately small carrier and is **not** a schedule
instance. -/
theorem witnessColumns_hypotheses_consistent :
    ∃ (rep : Fin 25 → Fin 1 × Fin 25) (S : Finset (Fin 25)),
      quotientDensity rep S 0 = 4 / 5 ∧
      omegaRoute < quotientDensity rep S 0 ∧
      quotientDensity rep S 0 < 1 ∧
      ⌈(9 : ℝ) / 25 * (Fintype.card (Fin 25) : ℝ)⌉₊
        ≤ (quotientSupport rep S 0).card := by
  classical
  set rep : Fin 25 → Fin 1 × Fin 25 := fun p => (0, p) with hrep
  set S : Finset (Fin 25) := Finset.univ.filter (fun p => (p : ℕ) < 20) with hS
  have hcard : (quotientSupport rep S 0).card = 20 := by decide
  have hdens : quotientDensity rep S 0 = 4 / 5 := by
    rw [quotientDensity, hcard, Fintype.card_fin]
    norm_num
  refine ⟨rep, S, hdens, ?_, ?_, ?_⟩
  · rw [hdens, omegaRoute_eq]; norm_num
  · rw [hdens]; norm_num
  · exact witnessDensity_meets_capacity_columns rep S 0 (by simp) (by
      rw [hdens, omegaRoute_eq]; norm_num)

/-- **Statement pole for the witness column floor.**  The density hypothesis is
load-bearing: over the same `25`-element `C_1` a support of size `8` has density
`8/25 < omega` and **misses** the frozen floor `ceil((9/25)|C_1|) = 9`.  A proof
of `witnessDensity_meets_capacity_columns` that never used `hdens` would
therefore be wrong. -/
theorem witnessColumns_pole_below_omega :
    ∃ (rep : Fin 25 → Fin 1 × Fin 25) (S : Finset (Fin 25)),
      quotientDensity rep S 0 < omegaRoute ∧
      ¬ (⌈(9 : ℝ) / 25 * (Fintype.card (Fin 25) : ℝ)⌉₊
          ≤ (quotientSupport rep S 0).card) := by
  classical
  set rep : Fin 25 → Fin 1 × Fin 25 := fun p => (0, p) with hrep
  set S : Finset (Fin 25) := Finset.univ.filter (fun p => (p : ℕ) < 8) with hS
  have hcard : (quotientSupport rep S 0).card = 8 := by decide
  have hfloor : ⌈(9 : ℝ) / 25 * (Fintype.card (Fin 25) : ℝ)⌉₊ = 9 := by
    rw [Fintype.card_fin]
    norm_num
  refine ⟨rep, S, ?_, ?_⟩
  · rw [quotientDensity, hcard, Fintype.card_fin, omegaRoute_eq]
    norm_num
  · rw [hfloor, hcard]
    norm_num

/-- **Statement pole for the node index of the witness certificate (repair
`cc-t2l-r1`).**

The frozen witness hypothesis -- "whenever its quotient support density is
greater than `omega`" (`08:829--830`) -- is a property **of the protocol node**,
not of the Stage-2 coordinate.  Over one `25`-element `C_1` the *same* witness
coordinate `0` sits strictly above `omega` at the node whose surviving physical
set has `20` elements and strictly below it at the node with `8`.

Hence a node-independent family `wrepr : Coord -> ...` whose bracket membership
is assumed once, ahead of the `S` binder, asserts the diagonal scaffold of
`08:864--871` at nodes where the frozen hypothesis **fails** -- strictly more
than the paper states -- and cannot be instantiated by the node's own
restriction, which is precisely the interface `lem:dense-routing`
(`08:878--944`) consumes when a witness routed whole "retains its bonus
certificate".  This is why `denseLocalCertificates` indexes `wrepr` by the node
and gates `hwrepr` on the density.

This is a probe of the definitions at a deliberately small carrier and is
**not** a schedule instance. -/
theorem witnessCertificate_pole_node_dependent :
    ∃ (rep : Fin 25 → Fin 1 × Fin 25) (S S' : Finset (Fin 25)),
      omegaRoute < quotientDensity rep S 0 ∧
      ¬ (omegaRoute < quotientDensity rep S' 0) := by
  classical
  set rep : Fin 25 → Fin 1 × Fin 25 := fun p => (0, p) with hrep
  set S : Finset (Fin 25) := Finset.univ.filter (fun p => (p : ℕ) < 20) with hS
  set S' : Finset (Fin 25) := Finset.univ.filter (fun p => (p : ℕ) < 8) with hS'
  have hcard : (quotientSupport rep S 0).card = 20 := by decide
  have hcard' : (quotientSupport rep S' 0).card = 8 := by decide
  refine ⟨rep, S, S', ?_, ?_⟩
  · rw [quotientDensity, hcard, Fintype.card_fin, omegaRoute_eq]
    norm_num
  · rw [quotientDensity, hcard', Fintype.card_fin, omegaRoute_eq]
    norm_num

/-- **Non-vacuity of the density-gated scaffold hypothesis (repair
`cc-t2l-r1`), and proof that the gate does real work.**

The repaired `denseLocalCertificates` carries the scaffold membership as the
*gated* hypothesis

```
hwrepr : forall S, forall alpha in W, omega < density rep S alpha ->
           wrepr S alpha in [R, q_1 + 3, x_cap, 9/25].
```

A gated premise can be satisfied by never firing, so this readout inhabits it at
a point where the gate **does** fire, and separates it from the ungated form:
over the same `25`-element `C_1`, at the node `S` the witness coordinate `0` has
density `4/5 > omega` and `wrepr S 0` **is** a bracket member, while at the node
`S'` its density is `8/25 < omega` and the exhibited `wrepr S' 0` is **not** a
bracket member at all.

Two things follow.  First, the third conjunct of `denseLocalCertificates` is not
vacuous: there is a live `(node, coordinate)` pair at which its hypothesis holds
and its conclusion is therefore asserted.  Second, the gating is not cosmetic:
this same `wrepr` refutes the ungated hypothesis, so the repaired statement is
**strictly weaker in hypothesis**, hence strictly stronger as a theorem, than
the node-independent shape it replaces.

The frozen depth guard `a + 1 <= b_0` is what makes `x_cap = 2^{a+1-b_0}` a
density at all, and it is carried explicitly as `hb`; it is the same guard the
banked `RawStageFour.localCapacityGap_not_automatic` carries.  This is a probe
of the definitions at a deliberately small carrier and is **not** a schedule
instance. -/
theorem witnessRepr_gate_nonvacuous (F : Stage1SlotBinding) {b₀ : ℕ}
    (hb : F.a + 1 ≤ b₀) :
    ∃ (rep : Fin 25 → Fin 1 × Fin 25) (S S' : Finset (Fin 25))
      (U B : Finset (Fin 1))
      (wrepr : Finset (Fin 25) → Fin 1 →
        Finset (Fin (F.q₁ + 3) × Bool) × Finset (Fin (F.q₁ + 3) → Bool)),
      (0 : Fin 1) ∈ selectedWitness U B ∧
      omegaRoute < quotientDensity rep S 0 ∧
      ¬ (omegaRoute < quotientDensity rep S' 0) ∧
      (∀ (T : Finset (Fin 25)), ∀ α ∈ selectedWitness U B,
        omegaRoute < quotientDensity rep T α →
          wrepr T α ∈ bracketGE Bool Bool (F.q₁ + 3) (xCap F b₀) (9 / 25)) ∧
      wrepr S 0 ∈ bracketGE Bool Bool (F.q₁ + 3) (xCap F b₀) (9 / 25) ∧
      wrepr S' 0 ∉ bracketGE Bool Bool (F.q₁ + 3) (xCap F b₀) (9 / 25) := by
  classical
  have hx : xCap F b₀ ≤ 1 := by
    have hexp : ((F.a : ℝ) + 1 - (b₀ : ℝ)) ≤ 0 := by
      have hle : ((F.a : ℝ) + 1) ≤ (b₀ : ℝ) := by exact_mod_cast hb
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  obtain ⟨RC, hRC⟩ :=
    bracketGE.nonempty (X := Bool) (Y := Bool) (F.q₁ + 3) (xCap F b₀) (9 / 25)
      hx (by norm_num) (by simp)
  have hempty : ((∅ : Finset (Fin (F.q₁ + 3) × Bool)),
      (∅ : Finset (Fin (F.q₁ + 3) → Bool)))
        ∉ bracketGE Bool Bool (F.q₁ + 3) (xCap F b₀) (9 / 25) := by
    intro hmem
    have hcol : ⌈((Fintype.card Bool : ℝ) ^ (F.q₁ + 3)) * (9 / 25)⌉₊
        ≤ (∅ : Finset (Fin (F.q₁ + 3) → Bool)).card := hmem.2
    rw [Finset.card_empty, Nat.le_zero, Nat.ceil_eq_zero] at hcol
    have hpos : (0 : ℝ) < ((Fintype.card Bool : ℝ) ^ (F.q₁ + 3)) * (9 / 25) := by
      have hc : (0 : ℝ) < (Fintype.card Bool : ℝ) := by simp
      positivity
    linarith
  set rep : Fin 25 → Fin 1 × Fin 25 := fun p => (0, p) with hrep
  set S : Finset (Fin 25) := Finset.univ.filter (fun p => (p : ℕ) < 20) with hS
  set S' : Finset (Fin 25) := Finset.univ.filter (fun p => (p : ℕ) < 8) with hS'
  have hcard : (quotientSupport rep S 0).card = 20 := by decide
  have hcard' : (quotientSupport rep S' 0).card = 8 := by decide
  have hfire : omegaRoute < quotientDensity rep S 0 := by
    rw [quotientDensity, hcard, Fintype.card_fin, omegaRoute_eq]
    norm_num
  have hmiss : ¬ (omegaRoute < quotientDensity rep S' 0) := by
    rw [quotientDensity, hcard', Fintype.card_fin, omegaRoute_eq]
    norm_num
  refine ⟨rep, S, S', Finset.univ, ∅,
    fun T α => if omegaRoute < quotientDensity rep T α then RC
      else ((∅ : Finset (Fin (F.q₁ + 3) × Bool)),
            (∅ : Finset (Fin (F.q₁ + 3) → Bool))),
    ?_, hfire, hmiss, ?_, ?_, ?_⟩
  · rw [mem_selectedWitness]
    exact ⟨Finset.mem_univ 0, by simp⟩
  · intro T α _ hdens
    simpa [hdens] using hRC
  · simpa [hfire] using hRC
  · simpa [hmiss] using hempty

/-- **Statement pole for the ordinary token's certificate.**  The Stage-1
certificate is load-bearing.  At the legal constant seed the bracket family at
row density `x_cap <= 1` and column density `3/5` is nonempty, and every member's
subgame is constant, hence of complexity `0`; so the conclusion of
`ordinaryToken_is_Bcap_hard` fails at any positive `B_cap`.  A proof that never
used `hcert` would be wrong.

This also records the coverage limit honestly: the module does **not** inhabit
`hcert` at a concrete matrix, and this pole is the reason -- the only matrices
whose bracket complexity is computable here are the constant ones, which refute
it. -/
theorem ordinaryToken_hard_pole_at_constant (b₁ : ℕ) :
    ∃ RC : Finset (Fin 1 × Bool) × Finset (Fin 1 → Bool),
      RC ∈ bracketGE Bool Bool 1 (xSeed b₁) (3 / 5) ∧
      D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1) RC.1 RC.2) = 0 ∧
      ¬ (1 ≤ D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
            RC.1 RC.2)) := by
  obtain ⟨RC, hRC⟩ :=
    bracketGE.nonempty (X := Bool) (Y := Bool) 1 (xSeed b₁) (3 / 5)
      (xSeed_le_one b₁) (by norm_num) (by simp)
  have hconst :
      subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1) RC.1 RC.2
        = fun (_ : {x // x ∈ RC.1}) (_ : {y // y ∈ RC.2}) => false := rfl
  have hzero : D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
      RC.1 RC.2) = 0 := by
    rw [hconst]; exact PublicRecords.D_const false
  exact ⟨RC, hRC, hzero, by rw [hzero]; norm_num⟩

/-- **Hypothesis consistency for the whole frozen lemma, at the numeric shape.**
`denseLocalCertificates` conjoins the two inherited certificates `hcert` and
`hgap`.  They are the two certificates `08:820--823` names side by side for the
two token kinds -- not two cases of a promise split -- so conjoining them is
legitimate; and their numeric shape is simultaneously satisfiable with **both**
frozen conclusions at the frozen floor `B_cap >= 3` (`07:501`), at every
`(Dsrc, a)`.  Hence no contradiction follows from the bundle.

This is the same shape of consistency probe the banked
`StageOneInterlace.stage1RobustCertificate_hypotheses_consistent` records for
the Stage-1 certificate, and it is recorded with the same coverage limit:
neither certificate is inhabited here at a concrete matrix
(`ordinaryToken_hard_pole_at_constant` records why the constant matrices cannot
serve). -/
theorem denseLocalCertificates_hypotheses_consistent (Dsrc a : ℕ) (h3 : 3 ≤ Dsrc + a) :
    ∃ dcert dgap dmem₁ dmem₂ : ℕ,
      3 ≤ bCap Dsrc a ∧
      bCap Dsrc a ≤ dcert ∧
      Dsrc + a + 1 ≤ dgap ∧
      dcert ≤ dmem₁ ∧
      dgap ≤ dmem₂ ∧
      bCap Dsrc a ≤ dmem₁ ∧
      bCap Dsrc a + 1 ≤ dmem₂ := by
  simp only [bCap_eq]
  refine ⟨Dsrc + a, Dsrc + a + 1, Dsrc + a, Dsrc + a + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

/-! ## §5  Candidate B (rejected): a token as a record carrying its certificate

The rejected encoding of `08:818--823` stores what the token is said to
*represent*.  It is recorded here as race evidence with its own battery, and it
is consumed by nothing. -/

/-- **Candidate B (rejected).**  A token as a record carrying its own local
capacity certificate. -/
structure TokenObject (Coord : Type*) (bcap : ℕ) where
  /-- The Stage-2 coordinate the token sits at. -/
  coord : Coord
  /-- The good set the frozen device places ordinary tokens on. -/
  good : Finset Coord
  /-- Whether a bonus token is attached (`08:821--823`). -/
  bonus : Bool
  /-- The local capacity the token is said to represent. -/
  capacity : ℕ
  /-- `08:820--823`, the frozen **conclusion** of
  `lem:dense-local-certificates` placed in constructor data, which the
  mechanical contract forbids. -/
  represents : bcap + (if bonus then 1 else 0) ≤ capacity

/-- **Candidate B, aux 1 (inhabitation with the hardest field).**  The record is
inhabited at the frozen floor `B_cap = 3` with the bonus field set, i.e. at the
stronger `B_cap + 1` certificate. -/
theorem tokenObject_nonempty : Nonempty (TokenObject (Fin 8) 3) :=
  ⟨{ coord := 0, good := {0}, bonus := true, capacity := 4,
     represents := by norm_num }⟩

/-- **Candidate B, aux 2 (a derived property).**  Every token, bonus or not,
carries at least the ordinary capacity. -/
theorem tokenObject_capacity_ge {Coord : Type*} {bcap : ℕ} (t : TokenObject Coord bcap) :
    bcap ≤ t.capacity := by
  have h := t.represents
  split at h <;> omega

/-- **Candidate B, aux 3 (the decisive defect).**  The record asserts a
`B_cap + 1` certificate at a coordinate that is **not in the good set at all**,
so the frozen sentence "For each coordinate in `H`, place one ordinary token"
(`08:819--820`) has no content in Candidate B: the device is supposed to be
placed by the selection, and this inhabitant was placed by nobody.

Candidate A cannot do this: `tokenWeight` is a function of the banked
`selectedGood`/`selectedWitness`, and `sum_tokenWeight` sums it over `H` only,
so a weight outside the selected data is not expressible. -/
theorem tokenObject_needs_no_good_coordinate :
    ∃ t : TokenObject (Fin 8) 3, t.coord ∉ t.good ∧ t.bonus = true := by
  refine ⟨{ coord := 7, good := {0}, bonus := true, capacity := 4,
             represents := by norm_num }, ?_, rfl⟩
  decide

/-! ### Disposition of Candidate B (recorded, binding on consumers)

`TokenObject` is race evidence.  It is consumed by nothing in this module or any
other, and it may **not** be used to re-encode the token bookkeeping of
`08:818--823` without a fresh judged tranche.  Its two defects are recorded
above: the frozen conclusion sits in constructor data, and the record is
inhabited at a coordinate the selection never placed a token on. -/

end EthInapproximability.ParameterizedNP.DenseRoutingThresholds
