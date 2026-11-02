import EthInapproximability.ParameterizedNP.DenseSourceOwners

/-!
# Parameterized NP route: the third block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 702--810** -- the
  tail of `sec:dense-bad-sets` from the point where the banked aggregate bound
  stops, plus the opening of `sec:dense-routing`.  The anchors traced here, in
  the order the block prints them:
  * `lem:dense-select-branch` (label 722, statement 721--742, proof 744--755):
    the existence of a dynamic branch `j_*` with `w_{j_*} > 4 b_{j_*}`, the
    frozen counting proof `zeta q_2 <= sum_j w_j <= 4 sum_j b_j < zeta q_2`
    (745--752), the selected data `H = [q_2] \ B_{j_*}`, `W = U_{j_*} \ B_{j_*}`,
    `w = w_{j_*}`, `b = b_{j_*}` (727--734), and `eq:selected-mass`
    (label 740, display 736--741) with its three estimates
    `|H| >= q_2 - b`, `|W| >= w - b`, `|H| + |W| >= q_2 + w - 2b`, proved in the
    frozen way -- "by removing at most `b` coordinates from `[q_2]` and from
    `U_{j_*}`" (753--754);
  * lines 757--761, the frozen remark that this is the first point at which the
    proof fixes a particular branch, and that the selection ties the fixed-block
    object `B_j^{temp}` and the dynamic-branch object `U_j` to the same index;
  * `sec:dense-routing` (label 764) lines 766--771: the residual protocol `P_*`
    below branch `B_{j_*}`, the frozen prefix length `log_2 s`, and
    `eq:selected-upper-budget` (label 770, display 768--771)
    `cost(P_*) <= D_2 = B_cap + log_2 q_2`, read against the alleged budget
    `cost(P) <= C - 1 = log_2 s + D_2` of `08:325` and the frozen identity
    `D_2 = B_cap + log_2 q_2` of `08:152`;
  * lines 773--789: the restriction to the canonical diagonal columns, the
    label-forgetting map to pairs `(alpha, gamma) in [q_2] x C_1` (778--780),
    the definition of the **quotient support** of a coordinate `alpha` at a
    later protocol node and of its **support density** (781--784), the frozen
    Bob-query behaviour "Every later Bob query partitions physical columns.
    Within each `alpha`-fibre, an underlying pair `(alpha, gamma)` represented
    in both physical children may be assigned to either child; a pair
    represented in only one child is forced there" (785--788), and the frozen
    reason "These assignments can be made independently for different
    `alpha`-fibres because those fibres are disjoint" (789);
  * `eq:routing-constants` (label 801, display 791--802): the certified Stage-1
    robustness depth `b_1` for `M_1^T` and the four routing constants
    `p_root = 1 - rho_loc`, `lambda_0 = 2 q_2 2^{-b_1}`, `eps_1 = 0`,
    `omega = (1 + eps_1)/2`, together with the frozen sentence "The equality
    `eps_1 = 0` records that `C_1` is a full product" (803);
  * `eq:routing-slack` (label 809, display 805--810): the schedule-enforced
    slack `p_root >= lambda_0` and `p_root - lambda_0 > omega`, transcribed as a
    predicate and never asserted.
* **Deliberately NOT claimed (the next block's territory).**
  `eq:routing-threshold` (`08:811--816`, the suffix-depth thresholds
  `lambda_d = lambda_0 2^{-d}`), the ordinary/bonus token bookkeeping
  (`08:818--823`) and `lem:dense-local-certificates` (`08:825--831`) have **no**
  declaration here.  They belong to the routing/token tranche, and nothing in
  this module may be cited as having supplied them.
* **Predecessor anchors (the handoffs consumed by pin):**
  * `08:508--700` through the banked
    `EthInapproximability.ParameterizedNP.DenseSourceOwners`, which supplies
    `witnessSets`, `witnessSupply` (`eq:witness-supply`) and `aggregateDefect`
    (`lem:aggregate-defect`) -- **the two inputs `lem:dense-select-branch`
    counts against**, plus `templateBadSet`, `diagonalBadSet` and
    `card_diagonalBad_le`;
  * `08:330--506` through `DenseSynchronisation`, which supplies the Alice
    prefix walk (`aliceResidual`, `IsAlicePrefixAt`,
    `cost_aliceResidual_add_le`), the gate predicate `denseDefectGates`, the
    protected masses `muR` and the counting tool `self_lt_two_pow`;
  * `08:1--328` through `DenseStageFourOpening`, which supplies the pinned local
    fraction `rhoLoc = 1/4` (`08:401`).
  **None of those handoffs is restated here.**
* **Frozen constants consumed from elsewhere in the paper:** the alleged-budget
  identity `C - 1 = log_2 s + D_2` and `D_2 = B_cap + log_2 q_2`
  (`08:152`, `08:325`); `zeta = gamma/24 <= 1/24` (`04:503--509`,
  `08:401--402`); the branch-count floor `s >= 4` (`08:402`).
* **Reader counterparts** (frozen release,
  `reader-facing/sections/A-stage4-details.tex`, the proof outline of
  `thm:paper-protected-stage4`), one per declaration group, none of them shared
  with another module -- the source-owners module's claims stop at reader line
  252 and it deliberately left lines 253--254 unclaimed for this tranche:
  * lines 253--254, "`\Cref{thm:paper-guarded-source}` selects a branch with
    more than four times as many witnesses as bad coordinates" -- SS1 and SS2:
    `denseSelectBranch`, `denseSelectBranch_pinned`,
    `denseSelectBranch_of_banked`, `selectedGood`, `selectedWitness`,
    `selectedMass` and their batteries;
  * lines 258--259, the clause "while the residual protocol is routed through
    arbitrary later queries" -- SS3: `Dtwo` and `selectedResidual_cost_le`;
  * line 259, the **separate** clause "Quotient-support routing follows every
    Bob query" -- SS4: `quotientSupport`, `quotientDensity` and their battery.
  Line 259 carries two clauses and each is assigned once; no clause is
  double-assigned.  The sentence at reader lines 256--258 ("On that branch there
  is no second synchronized prefix.  The Stage--2 lower bounds are applied to
  quotient supports, using the same physical balanced family as in Stage~2") and
  the remainder of line 259 onwards ("the weighted stopping count records ...")
  are **deliberately not claimed**: they are the next block's, and claiming
  either would double-assign a reader item.  The predecessor modules'
  claims stop at reader line 250 (`DenseSynchronisation`, lines 242--250) and
  line 252 (`DenseSourceOwners`, lines 250--252), so lines 253--259 were
  unclaimed before this tranche.  SS5 (the routing
  constants), SS6 (non-vacuity and poles) and SS7 (the rejected candidate) claim
  **no** reader item, deliberately rather than by omission.

## Dependencies, imports and external adapters

* Imports `EthInapproximability.ParameterizedNP.DenseSourceOwners` only, hence
  transitively `DenseSynchronisation`, `DenseStageFourOpening`, `RawStageFour`,
  `StageThreeExactScale`, `StageTwoRelaxed`, `StageOneInterlace`,
  `PublicRecords`, `GuardedSourceSlab`, `GuardedSourceGraph`, `FiniteSlots`,
  `PilotStage3` and the project-axiom-free `LegacyNPCC.Core` /
  `LegacyNPCC.Bridge` facades reached through `EthInapproximability.Prelude`.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency
  graph.
* Banked project interfaces consumed **by pin, never restated**:
  * `DenseSourceOwners.witnessSets`, `DenseSourceOwners.witnessSupply`,
    `DenseSourceOwners.aggregateDefect`;
  * `DenseSynchronisation.aliceResidual`, `DenseSynchronisation.IsAlicePrefixAt`,
    `DenseSynchronisation.cost_aliceResidual_add_le`,
    `DenseSynchronisation.denseDefectGates`, `DenseSynchronisation.muR`,
    `DenseSynchronisation.protectedMasses_agree`,
    `DenseSynchronisation.self_lt_two_pow`, and -- for the SS6 budget readout
    only -- the banked synchronisation witness `DenseSynchronisation.syncWitProto`
    with `DenseSynchronisation.denseSynchronisation_not_automatic`;
  * `DenseStageFourOpening.rhoLoc`.
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design; it reaches
  this block only through the banked `templateDefect`, whose own binders carry
  it, and it enters `denseSelectBranch_of_banked` as the named hypothesis
  `htemp` (one instance of the frozen template bound per branch).
  `thm:guarded-source` reaches this block only through the banked
  `witnessSupply`, whose binder `hwit` carries its S1 output.  Nothing about
  either is asserted here.
* **New vendored-gap work.**  None.  The selection is finite counting over the
  reals; the residual-budget statement runs on the banked prefix walk; the
  quotient support is ordinary `Finset` image/filter combinatorics.
* Proof status: **new** for the branch selection, the selected-mass estimates,
  the selected residual budget, the quotient-support layer and the routing
  constants; **inherited by pin** for the witness supply, the aggregate defect
  bound, the prefix-cost lemma, the gate predicate and the schedule constants.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Candidate encodings of the branch selection (`k = 2`, raced)

The novel object of this tranche is the selection of `08:721--726`: "There is a
dynamic branch `j_* in [s]` such that `w_{j_*} > 4 b_{j_*}`."

**Candidate A (landed, SS1).**  Make the selection a *function of the counted
data*.  `selectedBranch j_0 w b` is the least index maximising the surplus
`w j - 4 b j`; the frozen conclusion is then the theorem
`denseSelectBranch_pinned` about a pinned construction, and the frozen
existential `denseSelectBranch` is a corollary of it -- not the other way round.
Determinism is literal (`Finset.min'`), and the two banked inputs feed it
directly in `denseSelectBranch_of_banked`.  8 aux lemmas proved.

**Candidate B (rejected, SS7).**  Take the selected branch as data: a bundle
carrying `jstar`, the counts `wit`, `bad`, and the field
`4 * bad jstar < wit jstar`.  3 aux lemmas proved, but it loses decisively on
two counts.  First, it puts the frozen *conclusion* `08:725` into constructor
data, which the mechanical contract's no-conclusion-in-constructor-data rule
forbids outright.  Second, it is unfaithful even as data:
`selectedBranchData_needs_no_counting` exhibits an inhabitant at the frozen
`zeta q_2` for which the witness supply `eq:witness-supply` **fails**, so the
frozen sentence "Selection after counting" has no content in it -- the bundle
records a branch with a large surplus without any counting having happened.
The race is decided on faithfulness, not length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the pinned selection, general properties (5): `surplusMaxSet_nonempty`,
  `le_selectedBranch`, `selectedBranch_least`,
  `selectedBranch_basepoint_irrelevant`, `selectedBranch_of_constant`.
* `A2` the frozen selection (3): `denseSelectBranch_pinned`,
  `denseSelectBranch`, `denseSelectBranch_of_banked`.
* `A3` the selected data, general (5): `mem_selectedGood`,
  `mem_selectedWitness`, `selectedWitness_subset_selectedGood`,
  `selectedGood_of_empty`, `selectedWitness_self`.
* `A4` `eq:selected-mass` (3): `card_selectedGood`, `card_selectedWitness_ge`,
  `selectedMass`.
* `A5` the selected residual budget (2): `Dtwo_eq`,
  `selectedResidual_cost_le`.
* `A6` the quotient support, general (7): `mem_quotientSupport`,
  `quotientSupport_mono`, `quotientSupport_union`,
  `quotientSupport_fibres_disjoint`, `card_quotientSupport_le`,
  `quotientDensity_nonneg`, `quotientDensity_le_one`.
* `A7` the routing constants, general (5): `pRoot_eq`, `omegaRoute_eq`,
  `lambdaZero_nonneg`, `lambdaZero_antitone`, `lambdaZero_zero_depth`.
* Candidate B's own battery (3): `selectedBranchData_nonempty`,
  `selectedBranchData_wit_pos`, `selectedBranchData_needs_no_counting`.

That is **30 battery entries proved plus 3 for the rejected candidate** -- with
`0` unproved, alongside **three statement poles**
(`selectBranch_is_not_the_first_index`,
`selectedResidual_prefix_is_load_bearing`, `routingSlack_pole_at_zero_depth`)
and **seven non-vacuity / consistency readouts** -- one for every definition
group and every premise bundle the module introduces.  The module has **58**
source declarations in all: 15 definitions and 43 proved results (30 battery
entries, 3 for the rejected candidate, 3 statement poles, 7 readouts):

* `denseSelectBranch_hypotheses_consistent`, a legal instance at `s = 4`,
  `zeta = 1/24`, `q_2 = 6144` (the module's gate-legal point, inherited from the
  banked `aggregateDefect_hypotheses_consistent`) with **strictly positive**
  data `w_j = 64`, `b_j = 15`, both counting hypotheses **attained or strict**
  (`zeta q_2 = 256 = sum_j w_j`, `sum_j b_j = 60 < 64 = zeta q_2/4`), and the
  frozen conclusion obtained by *applying* `denseSelectBranch` to the witness;
* `denseSelectBranch_of_banked_hypotheses_consistent`, the **full** premise
  bundle of the banked-input form at the same gate-legal point --
  `denseDefectGates 8 1 6144 4 (1/24) 10^{-6}` on the face of the statement, a
  nonempty witness set of the frozen width `q_2 = 6144`, and strictly positive
  defect data `bt_j = 7`, `bd = 1`, `b_j = 8` -- with the conclusion obtained by
  *applying* `denseSelectBranch_of_banked`;
* `denseSelectBranch_excludes_empty_branch_set`, the record that the frozen
  counting itself excludes `s = 0`: at the empty branch set both sums vanish and
  the two counting hypotheses are already contradictory, which is why no
  `0 < s` binder appears on the selection (adding one would be an unused,
  over-strong premise);
* `selectedResidual_cost_le_hypotheses_consistent`, the premise bundle of
  `eq:selected-upper-budget` inhabited on the **banked** synchronisation witness
  at legal frozen values -- `s = 4` so the prefix length is `log_2 s = 2`,
  `B_cap = 3` (the frozen floor `D_2 >= B_cap >= 3` of `07:501`), and
  `log_2 q_2 = 13`, i.e. the legal power-of-two width `q_2 = 8192 >= 6144` --
  with a **nondegenerate** residual (strictly positive cost: it is the frozen
  Stage-3 Bob block of depth `3`, not a leaf) and the conclusion obtained by
  *applying* `selectedResidual_cost_le`;
* `selectedMass_separating_probe`, a separating probe of the selected data at
  `|Coord| = 8` with `b = 2`, `w = 3`: `H` and `W` are both **nonempty**, `W` is
  a **proper** subset of `H`, and the first frozen estimate `|H| >= q_2 - b` is
  **attained**.  It is a probe of the definitions, explicitly **not** a schedule
  instance: the frozen carrier is `[q_2]` with `q_2 >= 64 s q_1/zeta >= 6144`
  (`08:681`);
* `quotientSupport_nondegenerate`, a separating probe of the quotient support:
  the support of a coordinate is **neither empty nor all of `C_1`**, the frozen
  Bob split `quotientSupport (S_0 union S_1) = quotientSupport S_0 union
  quotientSupport S_1` is **strict on each child** (each child sees exactly one
  of the two underlying columns), and the density is strictly between `0` and
  `1`;
* `routingSlack_nondegenerate`, the routing slack `eq:routing-slack` inhabited
  **symbolically in `q_2`**: for every `q_2` the depth `b_1 = q_2 + 4` satisfies
  both frozen clauses, proved from the banked `self_lt_two_pow` with no tower
  evaluated -- so the schedule condition is satisfiable at the frozen widths,
  which no evaluable literal reaches.

## Honest scope and recorded coverage limits

1. **The selection is counting, not construction.**  `lem:dense-select-branch`
   is a pigeonhole over the two banked counts.  Nothing here builds `U_j`,
   `B_j^{temp}` or `B^{diag}` for the active construction, and nothing here
   asserts that the dense Stage-4 construction satisfies the counting
   hypotheses: `witnessSupply` and `aggregateDefect` are consumed as banked
   conditionals and their own binders stay binders.
2. **`eq:selected-mass` is transcribed at the frozen carriers, with `q_2` read
   as `|Coord|`.**  `08:730--734` sets `H = [q_2] \ B_{j_*}` and
   `W = U_{j_*} \ B_{j_*}`; the ambient coordinate type *is* `[q_2]`, so
   `selectedGood` is the `Finset` complement and the frozen `q_2` in
   `eq:selected-mass` is `Fintype.card Coord`.  No width is chosen here.
3. **The residual protocol is the banked prefix walk, not a new object.**
   `08:766--771` takes `P_*` to be the residual below branch `B_{j_*}`.  What is
   transcribed is the frozen *budget* statement: from the alleged
   `cost(P) <= log_2 s + D_2` (`08:325`) and an Alice prefix of length `log_2 s`
   (the banked `IsAlicePrefixAt`), the residual costs at most `D_2`.  That the
   selected branch's prefix is an Alice prefix is the banked
   `lem:dense-synchronisation`; it is a hypothesis here, not a claim.
4. **The quotient support is modelled by the label-forgetting map, not by the
   diagonal restriction.**  `08:773--784` restricts the residual rectangle to
   the canonical diagonal columns and forgets labels, mapping each surviving
   physical column to a pair `(alpha, gamma) in [q_2] x C_1`.  What is
   transcribed is exactly that map (`rep`), the resulting per-coordinate support
   and its density.  Constructing the diagonal restriction itself, and proving
   that it does not change the prefix transcript (`08:773--776`), needs the
   restriction machinery of the later subsections and has **no** declaration
   here; a later tranche may not cite this form as having supplied it.
5. **The Bob-query clause is transcribed as the union law, which is what the
   frozen text uses.**  `08:785--788` says a pair represented in both children
   may go to either and a pair in only one child is forced there; the content
   the routing argument consumes is that the parent's quotient support is the
   union of the children's, which is `quotientSupport_union`, together with the
   fibre disjointness of `08:789` (`quotientSupport_fibres_disjoint`).  No
   assignment rule is postulated.
6. **`b_1` is a binder, not a value.**  `08:791--793` fixes `b_1` as the
   *certified* Stage-1 robustness depth for `M_1^T`.  Certifying it is Stage-1
   work with no declaration here, so `lambdaZero` takes `b_1` as an explicit
   natural-number argument and `RoutingSlack` is a predicate that is never
   asserted.
7. **No parameter schedule may be read out of any witness below.**  The SS6
   witnesses are minimal probes chosen so that every frozen side condition holds
   and nothing else.  `selectedMass_separating_probe` and
   `quotientSupport_nondegenerate` are separating probes of definitions at
   deliberately small carriers and say so; the two counting readouts sit at the
   module's gate-legal point `s = 4`, `q_1 = 1`, `t_2 = 8`, `zeta = 1/24`,
   `q_2 = 6144`, `eta_R = 10^{-6}` inherited from the banked module.
8. **Candidate B is race evidence with a recorded disposition.**  See the
   disposition note at the end of SS7: `SelectedBranchData` is consumed by
   nothing and may not be used to re-encode the selection of `08:721--742`
   without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseBranchSelection

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseSourceOwners

/-! ## §1  Selection after counting (`08:721--761`, Candidate A)

`08:723--726`: "There is a dynamic branch `j_* in [s]` such that
`w_{j_*} > 4 b_{j_*}`", proved at `08:745--752` by the contrapositive count
`zeta q_2 <= sum_j w_j <= 4 sum_j b_j < zeta q_2`.

Candidate A makes the selected index a *function of the counted data*: the least
maximiser of the surplus `w j - 4 b j`.  The frozen conclusion is then a theorem
about a pinned construction (`denseSelectBranch_pinned`), and the frozen
existential is a corollary of it. -/

/-- The selection surplus `w j - 4 b j` of `08:725`.  A branch is admissible for
the frozen selection exactly when its surplus is positive. -/
def surplus {s : ℕ} (w b : Fin s → ℝ) (j : Fin s) : ℝ := w j - 4 * b j

open Classical in
/-- The argmax set of a real-valued branch statistic. -/
noncomputable def surplusMaxSet {s : ℕ} (f : Fin s → ℝ) : Finset (Fin s) :=
  Finset.univ.filter fun j => ∀ k : Fin s, f k ≤ f j

/-- **Aux 1.**  The argmax set of a nonempty index type is nonempty.  General;
the real-valued analogue of the banked `maxSet_nonempty`. -/
theorem surplusMaxSet_nonempty {s : ℕ} (j₀ : Fin s) (f : Fin s → ℝ) :
    (surplusMaxSet f).Nonempty := by
  classical
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin s)) f ⟨j₀, Finset.mem_univ j₀⟩
  refine ⟨j, ?_⟩
  simp only [surplusMaxSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun k => hj k (Finset.mem_univ k)

/-- `j_*` (`08:723`): the least branch maximising the selection surplus.  The
basepoint `j₀` only witnesses that the branch set is nonempty; the value does not
depend on it (`selectedBranch_basepoint_irrelevant`). -/
noncomputable def selectedBranch {s : ℕ} (j₀ : Fin s) (w b : Fin s → ℝ) : Fin s :=
  (surplusMaxSet (surplus w b)).min' (surplusMaxSet_nonempty j₀ (surplus w b))

/-- **Aux 2.**  The selected branch maximises the surplus.  General -- this is
its defining property. -/
theorem le_selectedBranch {s : ℕ} (j₀ : Fin s) (w b : Fin s → ℝ) (k : Fin s) :
    surplus w b k ≤ surplus w b (selectedBranch j₀ w b) := by
  classical
  have hmem :=
    Finset.min'_mem (surplusMaxSet (surplus w b)) (surplusMaxSet_nonempty j₀ (surplus w b))
  simp only [surplusMaxSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem k

/-- **Aux 3 (the deterministic tie-break).**  The selected branch is the *least*
maximiser of the surplus.  General. -/
theorem selectedBranch_least {s : ℕ} (j₀ : Fin s) (w b : Fin s → ℝ) {j : Fin s}
    (hj : ∀ k : Fin s, surplus w b k ≤ surplus w b j) : selectedBranch j₀ w b ≤ j := by
  classical
  refine Finset.min'_le _ _ ?_
  simp only [surplusMaxSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hj

/-- **Aux 4 (the basepoint is inert).**  `selectedBranch` does not depend on the
nonemptiness witness, so the selection really is a function of `w` and `b`. -/
theorem selectedBranch_basepoint_irrelevant {s : ℕ} (j₀ j₁ : Fin s) (w b : Fin s → ℝ) :
    selectedBranch j₀ w b = selectedBranch j₁ w b := rfl

/-- **Aux 5 (identity test).**  On constant counts every branch is a maximiser,
so the tie-break returns the least index.  General. -/
theorem selectedBranch_of_constant {s : ℕ} (j₀ : Fin s) (cw cb : ℝ) (j : Fin s) :
    selectedBranch j₀ (fun _ => cw) (fun _ => cb) ≤ j :=
  selectedBranch_least j₀ _ _ (fun _ => le_refl _)

/-- **`lem:dense-select-branch` (`08:721--726`, pinned form).**  Under the two
frozen counts -- `eq:witness-supply` `zeta q_2 <= sum_j w_j` (`08:604--607`) and
`lem:aggregate-defect` `sum_j b_j < zeta q_2/4` (`08:691--694`) -- the pinned
selection satisfies `w_{j_*} > 4 b_{j_*}`.

The frozen proof is transcribed exactly: if no branch had positive surplus then
`zeta q_2 <= sum_j w_j <= 4 sum_j b_j < zeta q_2` (`08:745--752`).
General in `s`, `zeta`, `q_2`, `w` and `b`.  No `0 < s` binder appears: the
frozen counting already excludes the empty branch set
(`denseSelectBranch_excludes_empty_branch_set`), so adding one would be an
unused, over-strong premise. -/
theorem denseSelectBranch_pinned {s q₂ : ℕ} {ζ : ℝ} (j₀ : Fin s) (w b : Fin s → ℝ)
    (hw : ζ * (q₂ : ℝ) ≤ ∑ j : Fin s, w j)
    (hb : ∑ j : Fin s, b j < ζ * (q₂ : ℝ) / 4) :
    4 * b (selectedBranch j₀ w b) < w (selectedBranch j₀ w b) := by
  by_contra hcon
  rw [not_lt] at hcon
  have hsurp : surplus w b (selectedBranch j₀ w b) ≤ 0 := by
    simp only [surplus]
    linarith
  have hall : ∀ j : Fin s, w j ≤ 4 * b j := by
    intro j
    have := le_selectedBranch j₀ w b j
    simp only [surplus] at this
    linarith
  have h1 : ∑ j : Fin s, w j ≤ ∑ j : Fin s, 4 * b j :=
    Finset.sum_le_sum fun j _ => hall j
  rw [← Finset.mul_sum] at h1
  linarith

/-- **`lem:dense-select-branch` (`08:721--726`), the frozen existential.**
"There is a dynamic branch `j_* in [s]` such that `w_{j_*} > 4 b_{j_*}`."
A corollary of the pinned form, so the selection is exhibited rather than merely
asserted to exist.

*Why the trivial witness fails.*  There is no canonical branch: any **fixed**
index is refuted by `selectBranch_is_not_the_first_index`, which satisfies both
counting hypotheses while the first index has `4 b_0 > w_0`.  The content of the
statement is therefore not the existence of some element of `Fin s` -- it is that
the counted data forces a *positive-surplus* branch. -/
theorem denseSelectBranch {s q₂ : ℕ} {ζ : ℝ} (j₀ : Fin s) (w b : Fin s → ℝ)
    (hw : ζ * (q₂ : ℝ) ≤ ∑ j : Fin s, w j)
    (hb : ∑ j : Fin s, b j < ζ * (q₂ : ℝ) / 4) :
    ∃ j : Fin s, 4 * b j < w j :=
  ⟨selectedBranch j₀ w b, denseSelectBranch_pinned j₀ w b hw hb⟩

/-- **The frozen selection from its two banked inputs.**  `08:744--752` counts
`eq:witness-supply` against `lem:aggregate-defect`.  Both are consumed **by
pin** from the banked source-owners module -- `witnessSupply` for the branchwise
witness counts `w_j = |U_j|` and `aggregateDefect` for `sum_j b_j < zeta q_2/4`
-- and neither is restated.  The deeper dependencies stay named hypotheses:
`hwit` carries the S1 output of `thm:guarded-source`, `htemp` carries the
frozen template bound (hence `EXPANDER-001`, which has no Lean declaration by
design), and `hdiag` carries the diagonal charge. -/
theorem denseSelectBranch_of_banked {Coord : Type*} [DecidableEq Coord]
    {s q₁ q₂ t₂ : ℕ} {ζ ηR : ℝ}
    (Wit : Finset Coord) (assign : Coord → Fin s)
    (bt : Fin s → ℝ) (bd : ℝ) (b : Fin s → ℝ)
    (hs : 0 < s) (hζ : 0 < ζ) (hq₂ : (0 : ℝ) ≤ (q₂ : ℝ))
    (hwit : ζ * (q₂ : ℝ) ≤ (Wit.card : ℝ))
    (hgates : denseDefectGates t₂ q₁ q₂ s ζ ηR)
    (htemp : ∀ j : Fin s, bt j < 8 * (q₁ : ℝ))
    (hdiag : bd ≤ ηR * (q₂ : ℝ) / (rhoLoc * muR))
    (hb : ∀ j : Fin s, b j ≤ bt j + bd) :
    ∃ j : Fin s, 4 * b j < ((witnessSets Wit assign j).card : ℝ) := by
  obtain ⟨j₀⟩ : Nonempty (Fin s) := Fin.pos_iff_nonempty.1 hs
  exact denseSelectBranch j₀ _ b (witnessSupply Wit assign hwit)
    (aggregateDefect bt bd b hs hζ hq₂ hgates htemp hdiag hb)

/-! ## §2  The selected data and `eq:selected-mass` (`08:727--761`)

`08:729--734` defines `H = [q_2] \ B_{j_*}`, `W = U_{j_*} \ B_{j_*}`,
`w = w_{j_*}` and `b = b_{j_*}`; `eq:selected-mass` (`08:736--741`) records the
three estimates, proved at `08:753--754` "by removing at most `b` coordinates
from `[q_2]` and from `U_{j_*}`".

Following coverage limit 2, the ambient coordinate type **is** `[q_2]`, so `H` is
the `Finset` complement and the frozen `q_2` is `Fintype.card Coord`. -/

section Selected

variable {Coord : Type*} [Fintype Coord] [DecidableEq Coord]

/-- `H = [q_2] \ B_{j_*}` (`08:730`). -/
def selectedGood (B : Finset Coord) : Finset Coord := Bᶜ

/-- `W = U_{j_*} \ B_{j_*}` (`08:731`). -/
def selectedWitness (U B : Finset Coord) : Finset Coord := U \ B

/-- **Aux 6 (general).**  Membership in `H` is exactly "not bad". -/
theorem mem_selectedGood {B : Finset Coord} (α : Coord) :
    α ∈ selectedGood B ↔ α ∉ B := by
  simp [selectedGood]

omit [Fintype Coord] in
/-- **Aux 7 (general).**  Membership in `W` is exactly "witnessed and not bad". -/
theorem mem_selectedWitness {U B : Finset Coord} (α : Coord) :
    α ∈ selectedWitness U B ↔ α ∈ U ∧ α ∉ B := by
  simp [selectedWitness]

/-- **Aux 8 (general).**  Every surviving witness is a good coordinate:
`W ⊆ H`.  This is what lets the frozen token bookkeeping attach a bonus token to
an ordinary one rather than to a separate object. -/
theorem selectedWitness_subset_selectedGood (U B : Finset Coord) :
    selectedWitness U B ⊆ selectedGood B := by
  intro α hα
  rw [mem_selectedWitness] at hα
  rw [mem_selectedGood]
  exact hα.2

/-- **Aux 9 (general, degenerate end).**  With no bad coordinates every
coordinate is good. -/
theorem selectedGood_of_empty : selectedGood (∅ : Finset Coord) = Finset.univ := by
  simp [selectedGood]

omit [Fintype Coord] in
/-- **Aux 10 (general, degenerate end).**  With no bad coordinates every witness
survives. -/
theorem selectedWitness_self (U : Finset Coord) :
    selectedWitness U (∅ : Finset Coord) = U := by
  simp [selectedWitness]

/-- **Aux 11 (`08:737`, first estimate).**  `|H| + b = q_2`, so `|H| >= q_2 - b`
with no truncation anywhere.  General. -/
theorem card_selectedGood (B : Finset Coord) :
    (selectedGood B).card + B.card = Fintype.card Coord := by
  rw [selectedGood, Nat.add_comm]
  exact Finset.card_add_card_compl B

omit [Fintype Coord] in
/-- **Aux 12 (`08:738`, second estimate).**  `w <= |W| + b`, the frozen
"removing at most `b` coordinates from `U_{j_*}`".  General. -/
theorem card_selectedWitness_ge (U B : Finset Coord) :
    U.card ≤ (selectedWitness U B).card + B.card := by
  calc U.card ≤ (U ∪ B).card := Finset.card_le_card Finset.subset_union_left
    _ = (selectedWitness U B).card + B.card := (Finset.card_sdiff_add_card U B).symm

/-- **`eq:selected-mass` (`08:736--741`).**  With `q_2 = |Coord|`, `w = |U|` and
`b = |B|`, the three frozen estimates
`|H| >= q_2 - b`, `|W| >= w - b`, `|H| + |W| >= q_2 + w - 2b`.
General in `U` and `B`; the third is the sum of the first two, exactly as the
frozen proof reads it. -/
theorem selectedMass (U B : Finset Coord) :
    ((Fintype.card Coord : ℝ) - (B.card : ℝ) ≤ ((selectedGood B).card : ℝ))
      ∧ ((U.card : ℝ) - (B.card : ℝ) ≤ ((selectedWitness U B).card : ℝ))
      ∧ ((Fintype.card Coord : ℝ) + (U.card : ℝ) - 2 * (B.card : ℝ)
          ≤ ((selectedGood B).card : ℝ) + ((selectedWitness U B).card : ℝ)) := by
  have h1 : ((selectedGood B).card : ℝ) + (B.card : ℝ) = (Fintype.card Coord : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (card_selectedGood B)
  have h2 : (U.card : ℝ) ≤ ((selectedWitness U B).card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast card_selectedWitness_ge U B
  exact ⟨by linarith, by linarith, by linarith⟩

end Selected

/-! ## §3  The selected residual and `eq:selected-upper-budget` (`08:766--771`)

`08:766--771`: "Let `P_*` be the residual protocol below branch `B_{j_*}`.  The
synchronised prefix has length `log_2 s`, so `cost(P_*) <= D_2 = B_cap +
log_2 q_2`."  The alleged total budget is `cost(P) <= C - 1 = log_2 s + D_2`
(`08:325`), and `D_2 = B_cap + log_2 q_2` is the frozen identity of `08:152`.

Following coverage limit 3, the prefix walk is the banked one and the
synchronisation hypothesis stays a binder. -/

/-- `D_2 = B_cap + log_2 q_2` (`08:152`, `08:769`), the frozen residual budget,
written at the two exponents the frozen text names. -/
def Dtwo (bcap lq₂ : ℕ) : ℕ := bcap + lq₂

/-- **Aux 13.**  The frozen identity `D_2 = B_cap + log_2 q_2`. -/
theorem Dtwo_eq (bcap lq₂ : ℕ) : Dtwo bcap lq₂ = bcap + lq₂ := rfl

/-- **`eq:selected-upper-budget` (`08:768--771`).**  If the alleged protocol
spends at most `log_2 s + D_2` bits (`08:325`) and its first `log_2 s` queries
are Alice queries at the row in hand -- the banked `IsAlicePrefixAt`, supplied
by `lem:dense-synchronisation` and carried here as a binder -- then the residual
protocol below the selected branch costs at most `D_2`.
General in the protocol, the row, the prefix length and both exponents. -/
theorem selectedResidual_cost_le {X Y Z : Type*} {P : Protocol X Y Z}
    {ls bcap lq₂ : ℕ} {x : X}
    (hpre : IsAlicePrefixAt P ls x)
    (hbudget : P.cost ≤ ls + Dtwo bcap lq₂) :
    (aliceResidual x ls P).cost ≤ Dtwo bcap lq₂ := by
  have h := cost_aliceResidual_add_le hpre
  simp only [Dtwo] at hbudget ⊢
  omega

/-! ## §4  Quotient supports (`08:773--789`)

`08:773--780`: restricting the selected residual rectangle to the canonical
diagonal columns and forgetting labels maps every remaining physical column to a
pair `(alpha, gamma) in [q_2] x C_1`.  `08:781--784`: the *quotient support* of
`alpha` at a later node is the set of distinct `gamma in C_1` represented by at
least one surviving physical column, and its *support density* is that
cardinality divided by `|C_1|`.

Following coverage limit 4, the label-forgetting map is the transcribed object
(`rep`); the diagonal restriction itself is not constructed here. -/

section Quotient

variable {Phys Coord Γ : Type*} [DecidableEq Coord] [DecidableEq Γ]

/-- The quotient support of coordinate `alpha` at a node whose surviving physical
columns are `S` (`08:781--784`).  `rep` is the label-forgetting map of
`08:776--780`. -/
def quotientSupport (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord) : Finset Γ :=
  (S.filter fun p => (rep p).1 = α).image fun p => (rep p).2

/-- **Aux 14 (round trip).**  `gamma` is in the quotient support of `alpha`
exactly when some surviving physical column represents `(alpha, gamma)` --
the frozen "at least one surviving physical column represents `(alpha, gamma)`".
General. -/
theorem mem_quotientSupport {rep : Phys → Coord × Γ} {S : Finset Phys} {α : Coord}
    {γ : Γ} : γ ∈ quotientSupport rep S α ↔ ∃ p ∈ S, rep p = (α, γ) := by
  simp only [quotientSupport, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hpS, hp1⟩, hp2⟩
    exact ⟨p, hpS, by rw [← hp1, ← hp2]⟩
  · rintro ⟨p, hpS, hp⟩
    exact ⟨p, ⟨hpS, by rw [hp]⟩, by rw [hp]⟩

/-- **Aux 15 (monotone).**  Deleting physical columns never enlarges a quotient
support.  General; this is the direction the routing induction consumes. -/
theorem quotientSupport_mono {rep : Phys → Coord × Γ} {S S' : Finset Phys}
    (h : S ⊆ S') (α : Coord) :
    quotientSupport rep S α ⊆ quotientSupport rep S' α := by
  intro γ hγ
  rw [mem_quotientSupport] at hγ ⊢
  obtain ⟨p, hpS, hp⟩ := hγ
  exact ⟨p, h hpS, hp⟩

/-- **`08:785--788`, the Bob-query law.**  "Every later Bob query partitions
physical columns.  Within each `alpha`-fibre, an underlying pair
`(alpha, gamma)` represented in both physical children may be assigned to either
child; a pair represented in only one child is forced there."  What the routing
argument consumes is exactly that the parent's quotient support is the union of
the two children's -- so no pair is lost, and a pair present in only one child
appears in that child alone.  General; no assignment rule is postulated. -/
theorem quotientSupport_union [DecidableEq Phys] (rep : Phys → Coord × Γ)
    (S₀ S₁ : Finset Phys) (α : Coord) :
    quotientSupport rep (S₀ ∪ S₁) α
      = quotientSupport rep S₀ α ∪ quotientSupport rep S₁ α := by
  ext γ
  simp only [Finset.mem_union, mem_quotientSupport]
  constructor
  · rintro ⟨p, hp, hrep⟩
    rcases hp with h | h
    · exact Or.inl ⟨p, h, hrep⟩
    · exact Or.inr ⟨p, h, hrep⟩
  · rintro (⟨p, hp, hrep⟩ | ⟨p, hp, hrep⟩)
    · exact ⟨p, Or.inl hp, hrep⟩
    · exact ⟨p, Or.inr hp, hrep⟩

omit [DecidableEq Γ] in
/-- **`08:789`.**  "These assignments can be made independently for different
`alpha`-fibres because those fibres are disjoint."  The physical fibres over
distinct coordinates are disjoint.  General. -/
theorem quotientSupport_fibres_disjoint (rep : Phys → Coord × Γ) (S : Finset Phys)
    {α α' : Coord} (h : α ≠ α') :
    Disjoint (S.filter fun p => (rep p).1 = α) (S.filter fun p => (rep p).1 = α') := by
  refine Finset.disjoint_left.2 ?_
  intro p hp hp'
  simp only [Finset.mem_filter] at hp hp'
  exact h (hp.2 ▸ hp'.2 ▸ rfl)

variable [Fintype Γ]

/-- **Aux 16.**  A quotient support never exceeds `|C_1|`.  General. -/
theorem card_quotientSupport_le (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord) :
    (quotientSupport rep S α).card ≤ Fintype.card Γ :=
  Finset.card_le_univ _

/-- The support density of `08:783--784`: the quotient support's cardinality
divided by `|C_1|`. -/
noncomputable def quotientDensity (rep : Phys → Coord × Γ) (S : Finset Phys)
    (α : Coord) : ℝ :=
  ((quotientSupport rep S α).card : ℝ) / (Fintype.card Γ : ℝ)

/-- **Aux 17.**  Densities are nonnegative.  General. -/
theorem quotientDensity_nonneg (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord) :
    0 ≤ quotientDensity rep S α := by
  unfold quotientDensity
  positivity

/-- **Aux 18.**  Densities are at most `1`.  General, given a nonempty `C_1`. -/
theorem quotientDensity_le_one (rep : Phys → Coord × Γ) (S : Finset Phys) (α : Coord)
    (hΓ : 0 < Fintype.card Γ) : quotientDensity rep S α ≤ 1 := by
  have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hΓ
  unfold quotientDensity
  rw [div_le_one hpos]
  exact_mod_cast card_quotientSupport_le rep S α

end Quotient

/-! ## §5  The routing constants (`08:791--810`)

`eq:routing-constants` (`08:791--802`) fixes, for the certified Stage-1
robustness depth `b_1` of `M_1^T`,
`p_root = 1 - rho_loc`, `lambda_0 = 2 q_2 2^{-b_1}`, `eps_1 = 0` and
`omega = (1 + eps_1)/2`; `08:803` records that `eps_1 = 0` says `C_1` is a full
product.  `eq:routing-slack` (`08:805--810`) is the schedule-enforced
`p_root >= lambda_0` and `p_root - lambda_0 > omega`; it is transcribed as a
predicate and never asserted.

Following coverage limit 6, `b_1` is an explicit binder: certifying it is
Stage-1 work with no declaration here.  `rho_loc` is **not** a free binder --
it is the banked `DenseStageFourOpening.rhoLoc`, pinned to `1/4` at `08:401`,
consumed by pin so that `p_root` and the banked diagonal filter speak about one
object. -/

/-- `p_root = 1 - rho_loc` (`08:794`), at the pinned local fraction. -/
noncomputable def pRoot : ℝ := 1 - rhoLoc

/-- `lambda_0 = 2 q_2 2^{-b_1}` (`08:796`), written as a quotient so that the
frozen negative exponent needs no integer exponentiation. -/
noncomputable def lambdaZero (q₂ b₁ : ℕ) : ℝ := 2 * (q₂ : ℝ) / 2 ^ b₁

/-- `eps_1 = 0` (`08:798`).  The frozen sentence at `08:803` records what the
equality means: `C_1` is a full product. -/
noncomputable def epsOne : ℝ := 0

/-- `omega = (1 + eps_1)/2` (`08:800`). -/
noncomputable def omegaRoute : ℝ := (1 + epsOne) / 2

/-- **`eq:routing-slack` (`08:805--810`)**, `p_root >= lambda_0` and
`p_root - lambda_0 > omega`.  Transcribed as a predicate and never asserted. -/
def RoutingSlack (q₂ b₁ : ℕ) : Prop :=
  lambdaZero q₂ b₁ ≤ pRoot ∧ omegaRoute < pRoot - lambdaZero q₂ b₁

/-- **Aux 19.**  `p_root = 3/4` at the pinned `rho_loc = 1/4` (`08:401`). -/
theorem pRoot_eq : pRoot = 3 / 4 := by
  rw [pRoot, rhoLoc]; norm_num

/-- **Aux 20.**  `omega = 1/2`, the frozen readout of `eps_1 = 0`. -/
theorem omegaRoute_eq : omegaRoute = 1 / 2 := by
  rw [omegaRoute, epsOne]; norm_num

/-- **Aux 21.**  `lambda_0 >= 0`.  General. -/
theorem lambdaZero_nonneg (q₂ b₁ : ℕ) : 0 ≤ lambdaZero q₂ b₁ := by
  unfold lambdaZero
  positivity

/-- **Aux 22 (monotone in the certified depth).**  A deeper Stage-1 robustness
certificate gives a smaller root threshold.  General. -/
theorem lambdaZero_antitone (q₂ : ℕ) {b₁ b₁' : ℕ} (h : b₁ ≤ b₁') :
    lambdaZero q₂ b₁' ≤ lambdaZero q₂ b₁ := by
  unfold lambdaZero
  have h1 : (0 : ℝ) < 2 ^ b₁ := by positivity
  have h2 : (0 : ℝ) < 2 ^ b₁' := by positivity
  have h3 : (2 : ℝ) ^ b₁ ≤ 2 ^ b₁' := pow_le_pow_right₀ (by norm_num) h
  have h4 : (0 : ℝ) ≤ 2 * (q₂ : ℝ) := by positivity
  exact div_le_div_of_nonneg_left h4 h1 h3 |>.trans_eq rfl

/-- **Aux 23 (identity test at zero depth).**  With no certified robustness
depth the root threshold is the full `2 q_2`.  General. -/
theorem lambdaZero_zero_depth (q₂ : ℕ) : lambdaZero q₂ 0 = 2 * (q₂ : ℝ) := by
  unfold lambdaZero
  norm_num

/-! ## §6  Non-vacuity, statement poles and consistency probes

Every predicate transcribed above is a `Prop` the module only ever consumes as a
hypothesis, and every definition is a carrier a later tranche will read.  An
unsatisfiable premise bundle or a degenerate carrier would make every consumer
vacuous while compiling green, so each is probed here.  No parameter schedule may
be read out of any witness below. -/

/-- **Hypothesis consistency for the selection (legal instance).**  At the
module's gate-legal point `s = 4` (the frozen branch floor of `08:402`),
`zeta = 1/24` (the frozen maximum of `zeta = gamma/24`) and `q_2 = 6144`
(`= 64 s q_1/zeta` at `q_1 = 1`), the counting bundle of
`lem:dense-select-branch` is satisfied with **strictly positive** data
`w_j = 64`, `b_j = 15`: the witness supply is **attained**
(`zeta q_2 = 256 = sum_j w_j`) and the aggregate bound is strict
(`sum_j b_j = 60 < 64 = zeta q_2/4`).  The frozen conclusion is obtained by
*applying* `denseSelectBranch` to the witness, so the bundle is shown to drive
the theorem rather than to resemble its premises.

*The trivial reading fails.*  `b_j = 0`, under which the frozen inequality
`w > 4b` says nothing, is excluded by `0 < b_j`; and inflating `w_j` to make the
selection vacuously easy is excluded by the attained witness supply. -/
theorem denseSelectBranch_hypotheses_consistent :
    ∃ (q₂ : ℕ) (ζ : ℝ) (w b : Fin 4 → ℝ),
      0 < ζ ∧ ζ ≤ 1 / 24 ∧ (∀ j : Fin 4, 0 < w j) ∧ (∀ j : Fin 4, 0 < b j) ∧
        ζ * (q₂ : ℝ) ≤ ∑ j : Fin 4, w j ∧
        ∑ j : Fin 4, w j ≤ ζ * (q₂ : ℝ) ∧
        ∑ j : Fin 4, b j < ζ * (q₂ : ℝ) / 4 ∧
        ∃ j : Fin 4, 4 * b j < w j := by
  have hsw : ∑ _j : Fin 4, (64 : ℝ) = 256 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hsb : ∑ _j : Fin 4, (15 : ℝ) = 60 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  refine ⟨6144, 1 / 24, (fun _ => 64), (fun _ => 15), by norm_num, by norm_num,
    fun _ => by norm_num, fun _ => by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [hsw]; norm_num
  · rw [hsw]; norm_num
  · rw [hsb]; norm_num
  · exact denseSelectBranch (q₂ := 6144) (ζ := 1 / 24) 0 (fun _ => 64) (fun _ => 15)
      (by rw [hsw]; norm_num) (by rw [hsb]; norm_num)

/-- **Hypothesis consistency for the banked-input form (legal instance).**  The
**full** premise bundle of `denseSelectBranch_of_banked` -- both banked
conditionals at once -- is satisfiable at the module's gate-legal point:
`s = 4`, `q_1 = 1`, `t_2 = 8`, `zeta = 1/24`, `q_2 = 6144`, `eta_R = 10^{-6}`,
with `eq:dense-defect-gates` carried **on the face of the statement** (its first
two clauses at equality, the third at the frozen strict `10^{-6} < 1/565248`),
a witness set of the frozen width `q_2 = 6144`, and **strictly positive** defect
data `bt_j = 7`, `bd = 1`, `b_j = 8`.  The conclusion is obtained by *applying*
`denseSelectBranch_of_banked` to the witness.

The illegal regime is excluded by the statement itself: the gate's floor
`q_2 >= 64 s q_1/zeta` and ceiling `eta_R < rho_loc mu_D zeta/(8s)` pin the
admissible window from both sides, so no reading of this certificate places the
selection at a width or tolerance the schedule never reaches. -/
theorem denseSelectBranch_of_banked_hypotheses_consistent :
    ∃ (Wit : Finset (Fin 6144)) (assign : Fin 6144 → Fin 4)
      (bt b : Fin 4 → ℝ) (bd ζ ηR : ℝ) (q₁ q₂ t₂ : ℕ),
      0 < ζ ∧ 0 < ηR ∧ 0 < bd ∧ (∀ j : Fin 4, 0 < bt j) ∧ (∀ j : Fin 4, 0 < b j) ∧
        Wit.Nonempty ∧
        denseDefectGates t₂ q₁ q₂ 4 ζ ηR ∧
        ζ * (q₂ : ℝ) ≤ (Wit.card : ℝ) ∧
        (∀ j : Fin 4, bt j < 8 * (q₁ : ℝ)) ∧
        bd ≤ ηR * (q₂ : ℝ) / (rhoLoc * muR) ∧
        (∀ j : Fin 4, b j ≤ bt j + bd) ∧
        ∃ j : Fin 4, 4 * b j < ((witnessSets Wit assign j).card : ℝ) := by
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  have hcard : (Finset.univ : Finset (Fin 6144)).card = 6144 := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hgates : denseDefectGates 8 1 6144 4 (1 / 24) (1 / 1000000) := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    rw [rhoLoc, hmu]
    norm_num
  have hwit : (1 / 24 : ℝ) * ((6144 : ℕ) : ℝ)
      ≤ (((Finset.univ : Finset (Fin 6144)).card : ℕ) : ℝ) := by
    rw [hcard]
    norm_num
  have hdiag : (1 : ℝ) ≤ (1 / 1000000 : ℝ) * ((6144 : ℕ) : ℝ) / (rhoLoc * muR) := by
    rw [rhoLoc, hmu]
    norm_num
  refine ⟨Finset.univ, fun α => ⟨α.val % 4, Nat.mod_lt _ (by norm_num)⟩,
    fun _ => 7, fun _ => 8, 1, 1 / 24, 1 / 1000000, 1, 6144, 8,
    by norm_num, by norm_num, by norm_num, fun _ => by norm_num,
    fun _ => by norm_num, ⟨0, Finset.mem_univ 0⟩, hgates, hwit,
    fun _ => by norm_num, hdiag, fun _ => by norm_num, ?_⟩
  exact denseSelectBranch_of_banked (q₁ := 1) (t₂ := 8) (ηR := 1 / 1000000)
    (Finset.univ : Finset (Fin 6144))
    (fun α => ⟨α.val % 4, Nat.mod_lt _ (by norm_num)⟩)
    (fun _ => 7) 1 (fun _ => 8)
    (by norm_num) (by norm_num) (by norm_num) hwit hgates
    (fun _ => by norm_num) hdiag (fun _ => by norm_num)

/-- **The frozen counting excludes the empty branch set.**  This is why
`denseSelectBranch` carries no `0 < s` binder: at `s = 0` both sums vanish, so
the witness supply forces `zeta q_2 <= 0` while the aggregate bound forces
`0 < zeta q_2/4`.  The two counting hypotheses are already contradictory there,
and a `0 < s` premise would be unused and over-strong. -/
theorem denseSelectBranch_excludes_empty_branch_set {q₂ : ℕ} {ζ : ℝ}
    (w b : Fin 0 → ℝ)
    (hw : ζ * (q₂ : ℝ) ≤ ∑ j : Fin 0, w j)
    (hb : ∑ j : Fin 0, b j < ζ * (q₂ : ℝ) / 4) : False := by
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hw hb
  linarith

/-- **Statement pole: no fixed index can replace the selection.**  At `s = 2`,
`zeta = 1`, `q_2 = 100` with counts `w = (0, 100)` and `b = (20, 0)`, both
counting hypotheses hold (`100 <= 100` and `20 < 25`) while the **first** branch
fails the frozen inequality outright (`4 b_0 = 80 > 0 = w_0`) and only the
second satisfies it.  So `lem:dense-select-branch` is not the trivial assertion
that `Fin s` is inhabited: substituting any fixed index for `j_*` would be
wrong, and the pinned `selectedBranch` returns the second branch here. -/
theorem selectBranch_is_not_the_first_index :
    ∃ w b : Fin 2 → ℝ,
      (1 : ℝ) * ((100 : ℕ) : ℝ) ≤ ∑ j : Fin 2, w j ∧
      ∑ j : Fin 2, b j < (1 : ℝ) * ((100 : ℕ) : ℝ) / 4 ∧
      ¬ (4 * b 0 < w 0) ∧
      4 * b 1 < w 1 ∧
      selectedBranch 0 (fun j : Fin 2 => if j = 0 then 0 else 100)
        (fun j : Fin 2 => if j = 0 then 20 else 0) = 1 := by
  refine ⟨fun j => if j = 0 then 0 else 100, fun j => if j = 0 then 20 else 0, ?_, ?_,
    by norm_num, by norm_num, ?_⟩
  · rw [Fin.sum_univ_two]
    norm_num
  · rw [Fin.sum_univ_two]
    norm_num
  · have hmax : ∀ k : Fin 2,
        surplus (fun j : Fin 2 => if j = 0 then (0 : ℝ) else 100)
          (fun j : Fin 2 => if j = 0 then (20 : ℝ) else 0) k
        ≤ surplus (fun j : Fin 2 => if j = 0 then (0 : ℝ) else 100)
            (fun j : Fin 2 => if j = 0 then (20 : ℝ) else 0) 1 := by
      intro k
      fin_cases k <;> (simp only [surplus]; norm_num)
    have hle := selectedBranch_least (0 : Fin 2)
      (fun j : Fin 2 => if j = 0 then (0 : ℝ) else 100)
      (fun j : Fin 2 => if j = 0 then (20 : ℝ) else 0) hmax
    have hne : selectedBranch (0 : Fin 2)
        (fun j : Fin 2 => if j = 0 then (0 : ℝ) else 100)
        (fun j : Fin 2 => if j = 0 then (20 : ℝ) else 0) ≠ 0 := by
      intro h
      have h0 := le_selectedBranch (0 : Fin 2)
        (fun j : Fin 2 => if j = 0 then (0 : ℝ) else 100)
        (fun j : Fin 2 => if j = 0 then (20 : ℝ) else 0) 1
      rw [h] at h0
      simp [surplus] at h0
      norm_num at h0
    omega

/-- **Separating probe of the selected data.**  At an eight-element coordinate
type with `B = {0, 1}` and `U = {1, 2, 3}` -- so `q_2 = 8`, `b = 2`, `w = 3` --
the frozen `H` and `W` are **both nonempty**, `W` is a **proper** subset of `H`,
and the first estimate of `eq:selected-mass` is **attained** (`|H| = 6 = q_2 - b`)
while the second is slack (`|W| = 2 > 1 = w - b`).  So neither `selectedGood` nor
`selectedWitness` collapses to the empty set or to the whole type.

This is a probe of the definitions at a deliberately small carrier and is
**not** a schedule instance: the frozen carrier is `[q_2]` with
`q_2 >= 64 s q_1/zeta >= 6144` (`08:681`).  No later tranche may read
`q_2 = 8` as legal. -/
theorem selectedMass_separating_probe :
    (selectedGood ({0, 1} : Finset (Fin 8))).card = 6 ∧
    (selectedWitness ({1, 2, 3} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8))).card = 2 ∧
    (selectedWitness ({1, 2, 3} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8))).Nonempty ∧
    (selectedGood ({0, 1} : Finset (Fin 8))).Nonempty ∧
    selectedWitness ({1, 2, 3} : Finset (Fin 8)) ({0, 1} : Finset (Fin 8))
      ⊂ selectedGood ({0, 1} : Finset (Fin 8)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  constructor
  · exact selectedWitness_subset_selectedGood _ _
  · decide

/-- **Separating probe of the quotient support.**  Four physical columns over a
two-element coordinate set and a two-element `C_1`, with
`rep = ((0,0), (0,1), (1,0), (1,1))`.  At `S = {0, 1}` the quotient support of
coordinate `0` is **all** of `C_1` while that of coordinate `1` is **empty**, so
the definition separates coordinates.  Splitting `S` into the two singletons --
the frozen Bob-query partition of `08:785--788` -- gives children whose supports
are the two distinct singletons, and the frozen union law recovers the parent
exactly: neither child alone carries the parent's support.  The density at
coordinate `0` is `1` and at coordinate `1` is `0`, so `quotientDensity` is
neither constantly `0` nor bounded away from `1`. -/
theorem quotientSupport_nondegenerate :
    ∃ rep : Fin 4 → Fin 2 × Fin 2,
      quotientSupport rep ({0, 1} : Finset (Fin 4)) 0 = Finset.univ ∧
      quotientSupport rep ({0, 1} : Finset (Fin 4)) 1 = ∅ ∧
      quotientSupport rep ({0} : Finset (Fin 4)) 0 = {0} ∧
      quotientSupport rep ({1} : Finset (Fin 4)) 0 = {1} ∧
      quotientSupport rep (({0} : Finset (Fin 4)) ∪ ({1} : Finset (Fin 4))) 0
        = quotientSupport rep ({0} : Finset (Fin 4)) 0
          ∪ quotientSupport rep ({1} : Finset (Fin 4)) 0 ∧
      quotientDensity rep ({0, 1} : Finset (Fin 4)) 0 = 1 ∧
      quotientDensity rep ({0, 1} : Finset (Fin 4)) 1 = 0 := by
  refine ⟨![(0, 0), (0, 1), (1, 0), (1, 1)], by decide, by decide, by decide,
    by decide, quotientSupport_union _ _ _ _, ?_, ?_⟩
  · unfold quotientDensity
    rw [show quotientSupport ![((0 : Fin 2), (0 : Fin 2)), (0, 1), (1, 0), (1, 1)]
        ({0, 1} : Finset (Fin 4)) 0 = Finset.univ from by decide]
    rw [Finset.card_univ, Fintype.card_fin]
    norm_num
  · unfold quotientDensity
    rw [show quotientSupport ![((0 : Fin 2), (0 : Fin 2)), (0, 1), (1, 0), (1, 1)]
        ({0, 1} : Finset (Fin 4)) 1 = ∅ from by decide]
    simp

/-- **Non-vacuity of `eq:routing-slack`, symbolic in the frozen width.**  For
**every** `q_2` there is a certified Stage-1 robustness depth `b_1` at which both
frozen clauses of `08:805--810` hold -- in particular at the frozen widths
`q_2 >= 6144`, which no evaluable literal reaches.  Nothing is evaluated: the
witness `b_1 = q_2 + 4` runs on the banked `self_lt_two_pow`, and the readout
shows the slack strictly: `lambda_0 < 1/4`, `p_root = 3/4`, `omega = 1/2`. -/
theorem routingSlack_nondegenerate (q₂ : ℕ) :
    ∃ b₁ : ℕ, lambdaZero q₂ b₁ < 1 / 4 ∧ RoutingSlack q₂ b₁ := by
  have hnat : (q₂ : ℝ) < 2 ^ q₂ := by
    have := self_lt_two_pow q₂
    exact_mod_cast this
  have hpowpos : (0 : ℝ) < 2 ^ q₂ := by positivity
  have hpow : (0 : ℝ) < 2 ^ (q₂ + 4) := by positivity
  have hexp : (2 : ℝ) ^ (q₂ + 4) = 2 ^ q₂ * 16 := by
    rw [pow_add]; norm_num
  have hkey : lambdaZero q₂ (q₂ + 4) < 1 / 4 := by
    unfold lambdaZero
    rw [div_lt_iff₀ hpow, hexp]
    nlinarith [hnat, hpowpos]
  refine ⟨q₂ + 4, hkey, ?_, ?_⟩
  · rw [pRoot_eq]
    linarith [lambdaZero_nonneg q₂ (q₂ + 4)]
  · rw [pRoot_eq, omegaRoute_eq]
    linarith

/-- **Statement pole for `eq:routing-slack`.**  The slack is a real constraint on
the certified depth: at `b_1 = 0` the root threshold is the full `2 q_2`, which
already exceeds `p_root = 3/4` at any positive width, so the first frozen clause
fails.  A routing argument that assumed the slack for free would be wrong. -/
theorem routingSlack_pole_at_zero_depth {q₂ : ℕ} (hq : 0 < q₂) :
    ¬ RoutingSlack q₂ 0 := by
  intro h
  have h1 : (1 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq
  have h2 := h.1
  rw [lambdaZero_zero_depth, pRoot_eq] at h2
  linarith

/-- **Hypothesis consistency for `eq:selected-upper-budget` (legal instance).**
The premise bundle of `selectedResidual_cost_le` is satisfiable at legal frozen
values, on the **banked** synchronisation witness: `s = 4` (the frozen branch
floor), so the prefix length is `log_2 s = 2`; `B_cap = 3` (the frozen floor
`D_2 >= B_cap >= 3` of `07:501`); and `log_2 q_2 = 13`, i.e.
`q_2 = 8192 >= 6144 = 64 s q_1/zeta`, a legal power-of-two width.  The alleged
budget `cost(P) = 5 <= 2 + D_2 = 18` holds, every row has the frozen Alice
prefix of length `2` (the banked `denseSynchronisation_not_automatic`), and the
residual is **nondegenerate**: its cost is strictly positive -- it is the frozen
Stage-3 Bob block of depth `3`, not a leaf.  The frozen conclusion is obtained
by *applying* `selectedResidual_cost_le` to the witness. -/
theorem selectedResidual_cost_le_hypotheses_consistent :
    (∀ x : Bool × Bool, IsAlicePrefixAt syncWitProto 2 x) ∧
    syncWitProto.cost ≤ 2 + Dtwo 3 13 ∧
    (∀ x : Bool × Bool, 0 < (aliceResidual x 2 syncWitProto).cost) ∧
    (∀ x : Bool × Bool, (aliceResidual x 2 syncWitProto).cost ≤ Dtwo 3 13) := by
  have hpre : ∀ x : Bool × Bool, IsAlicePrefixAt syncWitProto 2 x :=
    denseSynchronisation_not_automatic.1
  have hbudget : syncWitProto.cost ≤ 2 + Dtwo 3 13 := by
    simp [syncWitProto, witInner, witBobL, witBobR, Protocol.cost, Dtwo]
  refine ⟨hpre, hbudget, ?_, ?_⟩
  · intro x
    by_cases h1 : x.1 <;> by_cases h2 : x.2 <;>
      simp [aliceResidual, aliceStep, syncWitProto, witInner, witBobL, witBobR,
        Protocol.cost, h1, h2]
  · intro x
    exact selectedResidual_cost_le (hpre x) hbudget

/-- The protocol behind the budget pole: a two-level **Bob** tree of cost `2`. -/
def budgetPoleProto : Protocol Bool Bool Bool :=
  Protocol.bNode (fun y => y) (Protocol.leaf false)
    (Protocol.bNode (fun y => y) (Protocol.leaf false) (Protocol.leaf true))

/-- **Statement pole for `eq:selected-upper-budget`.**  The synchronisation
hypothesis is load-bearing.  At `ls = 1`, `B_cap = 0`, `log_2 q_2 = 1` the
alleged budget `cost(P) <= ls + D_2 = 2` holds for a protocol whose first query
is a **Bob** query; the Alice walk then stops, the "residual" is the whole
protocol, and its cost `2` exceeds `D_2 = 1`.  A proof of
`selectedResidual_cost_le` that never used `hpre` would therefore be wrong.

These numbers are a **minimal counterexample probe**, not a schedule instance:
the frozen floor is `D_2 >= B_cap >= 3` (`07:501`) and the frozen prefix length
is `log_2 s >= 2` (`08:402`).  The legal-value readout of the same bundle is
`selectedResidual_cost_le_hypotheses_consistent`. -/
theorem selectedResidual_prefix_is_load_bearing :
    budgetPoleProto.cost ≤ 1 + Dtwo 0 1 ∧
    ¬ ((aliceResidual true 1 budgetPoleProto).cost ≤ Dtwo 0 1) ∧
    ¬ IsAlicePrefixAt budgetPoleProto 1 true := by
  refine ⟨by simp [budgetPoleProto, Protocol.cost, Dtwo], ?_, ?_⟩
  · simp [aliceResidual, aliceStep, budgetPoleProto, Protocol.cost, Dtwo]
  · intro h
    obtain ⟨a, l, r, hp⟩ := h 0 (by norm_num)
    simp [aliceResidual, budgetPoleProto] at hp

/-! ## §7  Candidate B (rejected): the selected branch as constructor data

The rejected encoding of `08:721--726` takes the selected index and the frozen
inequality as one bundle.  It is recorded here as race evidence with its own
battery, and it is consumed by nothing. -/

/-- **Candidate B (rejected).**  The selected branch as a bundle carrying the
frozen conclusion `08:725` as a field. -/
structure SelectedBranchData (s : ℕ) where
  /-- The selected branch `j_*`. -/
  jstar : Fin s
  /-- The branchwise witness counts `w_j`. -/
  wit : Fin s → ℝ
  /-- The branchwise defect counts `b_j`. -/
  bad : Fin s → ℝ
  /-- `08:725`, `w_{j_*} > 4 b_{j_*}` -- a frozen **conclusion** placed in
  constructor data, which the mechanical contract forbids. -/
  dominant : 4 * bad jstar < wit jstar

/-- **Candidate B, aux 1 (inhabitation with the hardest field).**  The bundle is
inhabited at the frozen branch floor `s = 4`. -/
theorem selectedBranchData_nonempty : Nonempty (SelectedBranchData 4) :=
  ⟨{ jstar := 0, wit := fun _ => 100, bad := fun _ => 1, dominant := by norm_num }⟩

/-- **Candidate B, aux 2 (a derived property).**  A nonnegative defect count at
the selected branch forces a positive witness count there. -/
theorem selectedBranchData_wit_pos {s : ℕ} (d : SelectedBranchData s)
    (h : 0 ≤ d.bad d.jstar) : 0 < d.wit d.jstar := by
  have := d.dominant
  linarith

/-- **Candidate B, aux 3 (the decisive defect).**  The bundle records a branch
with a large surplus **without any counting having happened**: this inhabitant
violates `eq:witness-supply` at the frozen `zeta q_2 = 256`, so the frozen
sentence "Selection after counting" (`08:721`) has no content in Candidate B.
Candidate A cannot do this: its selection is a function of `w` and `b`, and its
conclusion is derived from the two counts rather than stored. -/
theorem selectedBranchData_needs_no_counting :
    ∃ d : SelectedBranchData 4,
      ¬ ((1 / 24 : ℝ) * ((6144 : ℕ) : ℝ) ≤ ∑ j : Fin 4, d.wit j) := by
  refine ⟨{ jstar := 0, wit := fun _ => 1, bad := fun _ => 0, dominant := by norm_num }, ?_⟩
  have hs : ∑ _j : Fin 4, (1 : ℝ) = 4 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  change ¬ ((1 / 24 : ℝ) * ((6144 : ℕ) : ℝ) ≤ ∑ _j : Fin 4, (1 : ℝ))
  rw [hs]
  norm_num

/-! ### Disposition of Candidate B (recorded, binding on consumers)

`SelectedBranchData` is race evidence.  It is consumed by nothing in this module
or any other, and it may **not** be used to re-encode the selection of
`08:721--742` without a fresh judged tranche.  Its two defects are recorded
above: the frozen conclusion sits in constructor data, and the bundle is
inhabited with no counting behind it. -/

end EthInapproximability.ParameterizedNP.DenseBranchSelection
