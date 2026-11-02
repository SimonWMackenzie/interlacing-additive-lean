import EthInapproximability.ParameterizedNP.DenseSynchronisation

/-!
# Parameterized NP route: the second block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 508--700** --
  `sec:dense-source-owners` (508--611) and the first half of
  `sec:dense-bad-sets` (613--700).  The anchors traced here, in the order the
  block prints them:
  * lines 511--536: the source-row scale `m = |Rows(R)|`,
    `x_cap = 2^{a+1-b_0}`, `t = ceil(x_cap m)` (513--520),
    `L_src = s(t-1)+1`, `kappa_X = (m - s(t-1))/m` (521--526), the parameter
    gate `eq:dense-source-row-gate` (528--531), and its two consequences
    `s(t-1) < m/2` and `kappa_X > 1/2` (532--536);
  * lines 538--553: the labelled universe `I_c x Rows(R) x [u_c]`, the
    definition of a *source-bad* item, the deletion count
    `m - (L_src - 1) = m - s(t-1) = kappa_X m`, and "one source-bad class-`c`
    item costs more than `m u_c/2` labelled row deletions";
  * lines 555--577: `eq:source-protection-gate` (556--565, label 564), the item
    counts `|I_V| = 4s|V|` and `|I_B| = 4s(s-3)` (566--567), and the charging
    conclusion "fewer than `(s/2) delta_v(G)|V|` and `s/2` vertex and blocker
    items, respectively, are source-bad", together with "These are precisely the
    two deletion allowances in `thm:guarded-source`; the spare factor in
    `eq:source-protection-gate` absorbs the strict inequalities and the bound
    `kappa_X > 1/2`" (568--577);
  * lines 579--594: the ownership construction -- one retained representative
    from each of `L_src` distinct seed rows, the branch counts
    `ell_{i,j}`, the identity `sum_j ell_{i,j} = L_src` (583--585, charged to
    `lem:dense-synchronisation`), "Choose an index `own(i)` maximizing
    `ell_{i,j}`, breaking ties deterministically" (586--587), the readout
    `ell_{i,own(i)} >= ceil(L_src/s) = t` (588--591), and "Consequently `own`
    partitions all nonbad source items among the `s` dynamic transcript
    branches, and every item assigned to a branch has at least `t` distinct
    seed-row representatives in that branch" (592--594);
  * lines 596--611: the witness supply -- one branch chosen per witnessed
    source coordinate with a deterministic tie-break, the disjoint sets
    `U_j ⊆ [q_2]`, `w_j = |U_j|`, and `eq:witness-supply`
    `sum_j w_j >= zeta q_2` (604--607, label 606);
  * lines 616--623: the definition of *template-bad for `j`* -- "if, in at
    least one of the `q_1` Stage-1 blocks, this projection represents fewer
    than `t` distinct seed rows", with the set named `B_j^{temp}`;
  * `lem:template-defect` (label 626, statement 625--631, proof 633--662):
    the deficient-block count `t-1` (634--635), the scale chain
    `t-1 < x_cap m <= m/(2s) <= m/8` (636--640), the one-coordinate projection
    support density `((q_1-1)m + m/8)/(q_1 m) = 1 - 7/(8q_1)` in
    `Rows(M_1) = [q_1] x Rows(R)` (641--646), the supposition of `8q_1`
    template-bad coordinates (647), the width condition `t_2 >= 8q_1` licensing
    the simultaneous upper-fibre estimate (648--649), the lower bound
    `x_dom/(1+eps_2) >= 98/100` on the product support (650--654), and the
    upper bound `(1 - 7/(8q_1))^{8q_1} < e^{-7} < 1/1000` (655--661);
  * lines 664--674: the definition of *diagonal-bad* -- fewer than
    `ceil((1-rho_loc)|C_1|)` underlying columns `gamma in C_1` retain a
    diagonal representative from `D_alpha` -- the name `B^{diag}`, and "That is
    why `B^{diag}` has no branch index" (671--674);
  * `lem:aggregate-defect` (label 677, statement 676--695, proof 697--700 plus
    the continuation of the same proof): `eq:dense-defect-gates` (679--685,
    label 684), `B_j = B_j^{temp} ∪ B^{diag}`, `b_j = |B_j|` (686--690), the
    conclusion `sum_j b_j < zeta q_2/4` (691--694), the template incidence
    `sum_j |B_j^{temp}| < 8 s q_1 <= zeta q_2/8` (698--703), and the diagonal
    charging `|B^{diag}| <= eta_R q_2/(rho_loc mu_D)` with its `s`-fold recharge
    (704 onwards, read from the same frozen proof).
* **Predecessor anchor (the handoff consumed by pin):** `08:330--506` through
  the banked `EthInapproximability.ParameterizedNP.DenseSynchronisation`, which
  supplies `sourceProtectionGate`, `denseDefectGates`, `muR`, `nuSrcR`,
  `nuTempR`, `zetaBound`, `protectedMasses_agree`, `self_lt_two_pow` and
  `two_exponent_le_two_pow`; and `08:1--328` through
  `DenseStageFourOpening`, which supplies `rhoTemp`, `rhoSigma`, `rhoLoc`.
  **None of that handoff is restated here.**
* **Frozen constants consumed from elsewhere in the paper:** `zeta = gamma/24`
  with `0 < gamma <= 1` (`04:503--509`), banked as `GuardedSourceSlab.zeta`; the
  two `RetentionOK` deletion allowances `(s/2) delta_v(G) N` and `s/2`
  (`04:484--495`, `eq:guarded-source-deletion-hypotheses`) and the witness
  supply `|Wit| >= zeta q_2` of `thm:guarded-source` S1 (`04:515--519`).
* **Reader counterparts** (frozen release,
  `reader-facing/sections/A-stage4-details.tex`, the proof outline of
  `thm:paper-protected-stage4`), one per declaration group, none of them shared
  with another module -- the synchronisation module's claims stop at reader
  line 250, so lines 250--253 were unclaimed before this tranche:
  * lines 250--251, "Before choosing a branch, define its template-bad
    coordinates, shared diagonal-bad coordinates, and surviving source
    witnesses" -- §5 and §6: `templateBadSet`, `templateDefect`,
    `diagonalBadSet`, `aggregateDefect` and their batteries;
  * lines 251--252, the clause "Summing the fixed-mass deletion bounds and
    applying" -- §1, §2, §3 and §4: the source-row scale, the two source-bad
    allowances, the ownership construction and the witness supply.
  The remainder of the sentence, reader lines 253--254
  ("`\Cref{thm:paper-guarded-source}` selects a branch with more than four
  times as many witnesses as bad coordinates"), is `lem:dense-select-branch`
  (`08:722`) and is deliberately **not** claimed here: it belongs to the
  branch-selection tranche, and claiming it would double-assign a reader item.
  The §7 non-vacuity group and the §8 rejected-candidate group claim **no**
  reader item, deliberately rather than by omission.

## Dependencies, imports and external adapters

* Imports `EthInapproximability.ParameterizedNP.DenseSynchronisation` only,
  hence transitively `DenseStageFourOpening`, `RawStageFour`,
  `StageThreeExactScale`, `StageTwoRelaxed`, `StageOneInterlace`,
  `PublicRecords`, `GuardedSourceSlab`, `GuardedSourceGraph`, `FiniteSlots`,
  `PilotStage3` and the project-axiom-free `LegacyNPCC.Core` /
  `LegacyNPCC.Bridge` facades reached through `EthInapproximability.Prelude`.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency
  graph.
* Banked project interfaces consumed **by pin, never restated**:
  * `DenseSynchronisation.sourceProtectionGate`,
    `DenseSynchronisation.denseDefectGates`, `DenseSynchronisation.muR`,
    `DenseSynchronisation.nuSrcR`, `DenseSynchronisation.nuTempR`,
    `DenseSynchronisation.protectedMasses_agree`,
    `DenseSynchronisation.two_exponent_le_two_pow`;
  * `DenseStageFourOpening.rhoTemp`, `DenseStageFourOpening.rhoLoc`.
* **Cited external interface, carried as an explicit named hypothesis and never
  as an axiom.**  `EXPANDER-001`, the `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design.  Its one
  use in this block is the *upper-fibre estimate* of `08:648--653`.  In
  `templateDefect` it appears as the two binders `hfibre` (the estimate applied
  simultaneously to a set of at most `t_2` coordinates) and `hxdom` (the frozen
  numeric readout `x_dom/(1+eps_2) >= 98/100`), and the theorem is a closed
  conditional in them.  Nothing about the family is asserted here.
* **New vendored-gap work.**  None: this block is finite combinatorics and real
  arithmetic over the banked constants.  The two general finite-support tools
  (`blockSupp` with its slice and card lemmas, and `card_le_of_deficient_block`)
  are new but are ordinary `Finset` facts, not vendored-layer repairs.
* Proof status: **new** for the source-row scale, the charging arithmetic, the
  ownership construction, the witness supply, the template-defect bound and the
  aggregate-defect bound; **inherited by pin** for the two gate predicates, the
  protected masses and the schedule constants.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Candidate encodings of source ownership (`k = 2`, raced)

The novel object of this tranche is the *owner map* `own` of `08:586--594`:
"Choose an index `own(i)` maximizing `ell_{i,j}`, breaking ties
deterministically."

**Candidate A (landed, §3).**  Derive the owner from the branch counts.  `own`
is a *function of* `ell`: `ownBranch j₀ ell` is the least index of the argmax
set of `ell`.  Nothing is postulated -- the frozen readout
`ell_{i,own(i)} >= t` is then a *theorem* about the pinned construction
(`tScale_le_own_representatives`), and "breaking ties deterministically" is
literally the `Finset.min'` in the definition.  5 aux lemmas proved.

**Candidate B (rejected, §8).**  Take the owner map as data: a bundle carrying
`own : Item -> Fin s`, the counts `reps`, and the field `t <= reps i (own i)`.
3 aux lemmas proved, but it loses decisively on two counts.  First, it puts the
frozen *conclusion* `08:588--591` into constructor data, which mechanical rule
M-`no conclusion in constructor data` forbids outright.  Second, it is
unfaithful even as data: `ownerAssignment_own_need_not_maximize` exhibits an
inhabitant whose `own i` is **not** an argmax of `reps i`, so the frozen
sentence "choose an index maximizing `ell_{i,j}`" is not expressible, and the
deterministic tie-break of `08:586--587` has no content.  Candidate A is also
shorter at the frozen arity.  The race is decided on faithfulness, not length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the source-row scale, general properties (6): `xCap_pos`,
  `one_le_tScale`, `tScale_sub_one_lt`, `s_mul_tScale_pred_lt_half`,
  `kappaX_gt_half`, `kappaX_mul_card`.
* `A2` the frozen `L_src` arithmetic (2): `Lsrc_sub_one`, `ceil_Lsrc_div`.
* `A3` the charging device, general (3): `card_le_of_charged`,
  `badItem_cost_gt_half`, `card_sourceBad_le`.
* `A4` the two frozen allowances (2): `sourceBad_vertex_allowance`,
  `sourceBad_blocker_allowance`.
* `A5` the owner map, general properties (6): `maxSet_nonempty`,
  `le_ownBranch`, `ownBranch_least`, `ownBranch_basepoint_irrelevant`,
  `ownBranch_of_constant`, `sum_le_card_mul_ownBranch`.
* `A6` the frozen ownership readout and partition (2):
  `tScale_le_own_representatives`, `own_partitions`.
* `A7` the witness supply, general (3): `witnessSets_disjoint`,
  `sum_card_witnessSets`, `witnessSupply`.
* `A8` the block-support tools, general (4): `card_blockSlice`,
  `card_blockSupp`, `card_slice_le`, `card_le_of_deficient_block`.
* `A9` the two frozen estimates behind `lem:template-defect` (2):
  `templateBad_density_lt`, `pow_one_sub_lt_thousandth`.
* `A10` the diagonal charge and the general battery of the diagonal-bad set (5):
  `card_diagonalBad_le`, `mem_diagonalBadSet`, `diagonalBadSet_antitone`,
  `diagonalBadSet_eq_empty`, `diagonalBadSet_of_card_zero`.
* The two headline results: `templateDefect`, `aggregateDefect`.
* Candidate B's own battery (3): `ownerAssignment_nonempty`,
  `ownerAssignment_reps_pos`, `ownerAssignment_own_need_not_maximize`.

That is **37 battery entries proved plus 3 for the rejected candidate** -- 35
auxiliary results and the two headline theorems -- with `0` unproved, alongside
**four statement poles** (`sourceRowGate_pole_at_large_xCap`,
`ownBranch_is_not_the_basepoint`, `templateDefect_fibre_is_load_bearing`,
`aggregateDefect_gate_is_load_bearing`) and **nine non-vacuity / consistency
readouts** -- one for every definition and every premise bundle the module
introduces, the diagonal side included:

* `denseSourceRowGate_nondegenerate`, general in the Stage-1 exponent `a` and
  in `s >= 4`, so the gate is satisfiable at the frozen exponent floor
  `a >= 2432` (`06:298--315`) without evaluating any tower;
* `denseSourceRowGate_shape_instance`, a concrete shape-conforming witness at
  `s = 4`, `a = 0`, `b_0 = 4`, `m = 16`, `t = 2`, `L_src = 5`, `kappa_X = 3/4`,
  which is **not** a schedule instance and says so;
* `sourceBad_vertex_hypotheses_consistent`, a *legal* instance at `s = 4`,
  `|V| = 1000`, `delta_v = 1/6`, `eta_C = 2^{-21}/8000 > 0` carrying a
  **nonzero** bad count `nbad = 1` -- so the premise bundle does not force the
  bad set to be empty;
* `sourceBad_blocker_hypotheses_consistent`, a legal instance at `s = 128`,
  `eta_C = 2^{-21}/256000 > 0`, again with a **nonzero** bad count `nbad = 1`
  (the frozen constants make the template clause binding, so the blocker
  charging capacity `2 eta_C |I_B| / nu_B = (s-3)/125` first admits a whole bad
  item at `s = 128`);
* `templateDefect_hypotheses_consistent`, a legal instance at `q_1 = 50`,
  `m = 16`, `t = 2`, `t_2 = 400`, `x_dom/(1+eps_2) = 98/100`, carrying a
  **nonempty** template-bad set -- so the fibre hypothesis and the badness
  hypothesis are not jointly contradictory at the frozen shapes.  The ambient
  coordinate type is `Fin 400`, chosen so that `|Coord| = 8 q_1` exactly: at any
  smaller coordinate type the frozen conclusion `|B_j^{temp}| < 8 q_1` would be
  forced by the cardinality of the type alone and no hypothesis would do any
  work.  The balanced-family clauses are therefore discharged uniformly in the
  subset `S`, not by enumeration, and the final clause is obtained by *applying*
  `templateDefect` to the witness, so the bundle is shown to drive the theorem
  rather than to resemble its premises;
* `diagonalBadSet_nondegenerate`, a *separating* probe of the diagonal filter at
  `|C_1| = 8`, where the pinned `rho_loc = 1/4` makes the frozen threshold
  `ceil((1-rho_loc)|C_1|) = 6` exact: one coordinate is diagonal-bad and one is
  not, so `B^{diag}` is neither empty nor the whole coordinate type;
* `card_diagonalBad_le_hypotheses_consistent`, the premise bundle of the diagonal
  charge **inside** `eq:dense-defect-gates`: the witness carries
  `denseDefectGates t_2 q_1 q_2 s zeta eta_R` as a clause on the face of the
  statement and is taken at the same gate-legal point as
  `aggregateDefect_hypotheses_consistent` -- `s = 4`, `q_1 = 1`, `t_2 = 8`,
  `zeta = 1/24`, `q_2 = 6144`, `eta_R = 10^{-6}` -- with `|C_1| = 8`, `u = 1`,
  `del = 9043968/10^6` and a strictly positive `nbad = 4521984/10^6`.  All three
  charging inequalities are **attained**: both premises of `card_diagonalBad_le`
  and its conclusion `nbad <= eta_R q_2/(rho_loc mu_D)` are recorded together
  with their reverses, and the forward conclusion is obtained by applying
  `card_diagonalBad_le` to the witness.  The gate clause is what makes the
  readout legal: at the earlier probe `eta_R = 1/1000`, `q_2 = 1000` the
  charging bundle alone is satisfiable, but the frozen ceiling
  `eta_R < rho_loc mu_D zeta/(8s) = 1/565248` and the frozen floor
  `q_2 >= 64 s q_1/zeta = 6144` both fail there, so no such point can occur in
  the construction the charge serves;
* `aggregateDefect_hypotheses_consistent`, a legal instance at `s = 4`,
  `q_1 = 1`, `t_2 = 8`, `zeta = 1/24`, `q_2 = 6144`, `eta_R = 10^{-6}` with
  **strictly positive** defect data `bt_j = 7`, `bd = 1`, `b_j = 8` and the
  conclusion `32 < 64`;
* `ownership_legal_instance`, the frozen ownership readout at `s = 4`, `t = 2`,
  `L_src = 5` with the nonuniform branch counts `(2,1,1,1)`, where the bound
  `t <= ell_{own}` is attained exactly.

## Honest scope and recorded coverage limits

1. **The labelled universe is modelled by its cardinalities, not by its
   elements.**  `08:538--553` fixes the universe `I_c x Rows(R) x [u_c]`; what
   the frozen charging argument uses about it is exactly three numbers -- the
   item count `|I_c|`, the seed-row count `m` and the multiplicity `u_c` -- and
   the two inequalities relating the deletion count of a bad item to the
   deletion budget.  §2 therefore transcribes the charging as a real-arithmetic
   conditional in those numbers.  A later tranche that needs the labelled
   universe itself (for instance to *construct* the deletion set) may not cite
   the present form as having supplied it.
2. **`thm:guarded-source` is an explicit named hypothesis.**  `08:596` applies
   it; §4 takes its S1 output `zeta q_2 <= |Wit|` (`04:515--519`) as the binder
   `hwit` and derives only `eq:witness-supply` from it.  The theorem itself is
   banked in `GuardedSourceSlab.guardedSource` and is **not** re-proved, and
   nothing here asserts that the guarded source of the active construction
   satisfies its hypotheses.
3. **`EXPANDER-001` never becomes an axiom.**  See the adapter note above.  In
   particular `templateDefect` proves *nothing* about balanced families; it
   proves that the frozen numeric estimate is incompatible with `8q_1`
   template-bad coordinates.
4. **The Stage-2 projection is modelled by its support, not reconstructed.**
   `08:616--623` obtains `B_j^{temp}` by projecting the branch's retained rows
   `S_j` to the `alpha`-th Stage-2 coordinate.  Building `S_j` and the
   projection needs the restriction machinery of the later subsections, which
   has no Lean declaration yet.  What is transcribed is the *support*
   `supp alpha ⊆ [q_1] x Rows(R)` of that projection together with the frozen
   badness test on its Stage-1 block slices; the density of `supp` is then a
   computed quantity, not a hypothesis.
5. **The diagonal reservoir is modelled by its charging inequality.**
   `08:664--674` defines `B^{diag}` through the retained diagonal columns;
   `diagonalBadSet` transcribes that test, and `card_diagonalBad_le` transcribes
   the frozen charge.  Both speak about **one** object: the local fraction is the
   banked `DenseStageFourOpening.rhoLoc`, pinned to `1/4` at `08:401`, consumed
   by pin in the definition and in the charging lemma alike, and never taken as a
   free binder or re-inlined as a literal.  The reservoir's own mass identity
   `mu_D = mu_Sigma` is consumed from the banked `muR`.  The frozen sentence
   "That is why `B^{diag}`
   has no branch index" is honoured structurally: `aggregateDefect` takes a
   single unindexed `bd`, not a family `bd j`.
6. **`Admissible`, `NoCert` and `LevelStep` still have no Lean declaration**
   and do not appear here: every statement of this module is a closed
   conditional in its own explicit binders.
7. **No parameter schedule may be read out of any witness below.**  The §7
   witnesses are minimal probes chosen so that every frozen side condition
   holds and nothing else.  `denseSourceRowGate_shape_instance` is
   shape-conforming and locally legal only, and says so in its own name and
   docstring, because the frozen schedule pins the Stage-1 exponent `a` above
   every evaluable literal (`06:298--315`).  The magnitude floor is carried
   instead by the symbolic `denseSourceRowGate_nondegenerate`.
8. **Candidate B is race evidence with a recorded disposition.**  See the
   disposition note at the end of §8: `OwnerAssignment` is consumed by nothing
   and may not be used to re-encode the ownership of `08:579--611` without a
   fresh judged tranche.
9. **The template certificate's coordinate width is not a legal `q_2`**
   (advisory `A8`, `cc-t2j-r1`, recorded here and not actioned in `cc-t2j-r2`).
   `templateDefect_hypotheses_consistent` uses the ambient coordinate type
   `Fin 400`, chosen so that `|Coord| = 8 q_1` exactly and the frozen conclusion
   `|B_j^{temp}| < 8 q_1` is therefore **not** forced by the cardinality of the
   type alone.  That is the *minimum non-type-forced size*, not a schedule
   width: the frozen carrier is `[q_2]` with `q_2 >= 64 s q_1/zeta >= 6144`
   (`08:681`, at `s >= 4`, `q_1 >= 1`, `zeta <= 1/24`).  Its proof is uniform in
   the subset `S` and would go through verbatim at `Fin 6144`.  **No later
   tranche may read `q_2 = 400` as legal**, and no schedule instance may be
   recovered from that witness.  The gate-legal diagonal readout of §7,
   `card_diagonalBad_le_hypotheses_consistent`, is the module's record of the
   frozen width `q_2 = 6144`; it carries `denseDefectGates` on its face for
   exactly this reason.
-/

namespace EthInapproximability.ParameterizedNP.DenseSourceOwners

open Finset
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation

/-! ## §1  The source-row scale (`08:511--536`)

`08:513--520` fixes `m = |Rows(R)|`, `x_cap = 2^{a+1-b_0}` and
`t = ceil(x_cap m)`; `08:521--526` defines `L_src = s(t-1)+1` and
`kappa_X = (m - s(t-1))/m`; `08:528--531` is the parameter gate; `08:532--536`
records its two consequences.  Every declaration below is a transcription or a
consequence, never an assertion that the gate holds. -/

/-- `x_cap = 2^{a+1-b_0}` (`08:517`).  Written as a quotient of two powers so
that the frozen exponent difference `a+1-b_0`, which is negative in the frozen
regime, needs no integer exponentiation. -/
noncomputable def xCap (a b₀ : ℕ) : ℝ := (2 : ℝ) ^ (a + 1) / 2 ^ b₀

/-- **`eq:dense-source-row-gate` (`08:528--531`)**, `x_cap <= 1/(2s)`.
Transcribed as a predicate and never asserted. -/
def denseSourceRowGate (a b₀ s : ℕ) : Prop := xCap a b₀ ≤ 1 / (2 * (s : ℝ))

/-- `t = ceil(x_cap m)` (`08:519`), the blockwise seed-row demand. -/
noncomputable def tScale (a b₀ m : ℕ) : ℕ := ⌈xCap a b₀ * (m : ℝ)⌉₊

/-- `L_src = s(t-1)+1` (`08:523`). -/
def Lsrc (s t : ℕ) : ℕ := s * (t - 1) + 1

/-- `kappa_X = (m - s(t-1))/m` (`08:525`).  The subtraction is real, matching
the frozen display; no truncation is introduced. -/
noncomputable def kappaX (s t m : ℕ) : ℝ :=
  ((m : ℝ) - (s : ℝ) * ((t : ℝ) - 1)) / (m : ℝ)

/-- **Aux 1.**  `x_cap > 0`.  General in `a` and `b_0`; no gate needed. -/
theorem xCap_pos (a b₀ : ℕ) : 0 < xCap a b₀ := by
  unfold xCap
  positivity

/-- **Aux 2.**  `t >= 1` whenever there is at least one seed row.  General.
This is what makes `L_src = s(t-1)+1` the frozen count rather than a truncated
one. -/
theorem one_le_tScale {a b₀ m : ℕ} (hm : 0 < m) : 1 ≤ tScale a b₀ m := by
  have hpos : 0 < xCap a b₀ * (m : ℝ) :=
    mul_pos (xCap_pos a b₀) (by exact_mod_cast hm)
  exact Nat.one_le_iff_ne_zero.2 (fun h => by
    have := Nat.ceil_eq_zero.1 (by simpa [tScale] using h)
    linarith)

/-- **Aux 3.**  `t - 1 < x_cap m`, the frozen first inequality of
`08:636--640`.  General; the ceiling is the only input. -/
theorem tScale_sub_one_lt (a b₀ m : ℕ) :
    ((tScale a b₀ m : ℕ) : ℝ) - 1 < xCap a b₀ * (m : ℝ) := by
  have hnn : (0 : ℝ) ≤ xCap a b₀ * (m : ℝ) := by
    have := (xCap_pos a b₀).le
    positivity
  have h : ((tScale a b₀ m : ℕ) : ℝ) < xCap a b₀ * (m : ℝ) + 1 := by
    simpa [tScale] using Nat.ceil_lt_add_one hnn
  linarith

/-- **Aux 4 (`08:532--533`).**  The gate gives `s(t-1) < m/2`.  General in
`a`, `b_0`, `s` and `m`; the only hypotheses are the gate and `0 < s`. -/
theorem s_mul_tScale_pred_lt_half {a b₀ s m : ℕ} (hs : 0 < s)
    (hgate : denseSourceRowGate a b₀ s) :
    (s : ℝ) * (((tScale a b₀ m : ℕ) : ℝ) - 1) < (m : ℝ) / 2 := by
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have h1 : ((tScale a b₀ m : ℕ) : ℝ) - 1 < xCap a b₀ * (m : ℝ) :=
    tScale_sub_one_lt a b₀ m
  have h2 : xCap a b₀ * (m : ℝ) ≤ (1 / (2 * (s : ℝ))) * (m : ℝ) := by
    have := hgate
    unfold denseSourceRowGate at this
    exact mul_le_mul_of_nonneg_right this hm
  have h3 : (s : ℝ) * (((tScale a b₀ m : ℕ) : ℝ) - 1)
      < (s : ℝ) * ((1 / (2 * (s : ℝ))) * (m : ℝ)) := by
    have := lt_of_lt_of_le h1 h2
    exact mul_lt_mul_of_pos_left this hs'
  have h4 : (s : ℝ) * ((1 / (2 * (s : ℝ))) * (m : ℝ)) = (m : ℝ) / 2 := by
    field_simp
  linarith [h3, h4.le, h4.ge]

/-- **Aux 5 (`08:534--536`).**  The gate gives `kappa_X > 1/2`.  General. -/
theorem kappaX_gt_half {a b₀ s m : ℕ} (hs : 0 < s) (hm : 0 < m)
    (hgate : denseSourceRowGate a b₀ s) :
    1 / 2 < kappaX s (tScale a b₀ m) m := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h := s_mul_tScale_pred_lt_half (a := a) (b₀ := b₀) (m := m) hs hgate
  unfold kappaX
  rw [lt_div_iff₀ hm']
  linarith

/-- **Aux 6.**  `kappa_X m = m - s(t-1)`, the frozen identity of `08:549--550`
read from right to left.  General for `0 < m`. -/
theorem kappaX_mul_card {s t m : ℕ} (hm : 0 < m) :
    kappaX s t m * (m : ℝ) = (m : ℝ) - (s : ℝ) * ((t : ℝ) - 1) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold kappaX
  field_simp

/-- **Aux 7.**  `L_src - 1 = s(t-1)`, the middle term of `08:549--550`.
General; note that both subtractions are natural. -/
theorem Lsrc_sub_one (s t : ℕ) : Lsrc s t - 1 = s * (t - 1) := by
  simp [Lsrc]

/-- **Aux 8 (`08:588--591`).**  `ceil(L_src/s) = t`, the frozen readout of the
ownership bound, written with the standard ceiling-division formula.  General
for `0 < s` and `1 <= t`. -/
theorem ceil_Lsrc_div {s t : ℕ} (hs : 0 < s) (ht : 1 ≤ t) :
    (Lsrc s t + s - 1) / s = t := by
  have h : Lsrc s t + s - 1 = s * t := by
    unfold Lsrc
    have h1 : s * (t - 1) + 1 + s - 1 = s * (t - 1) + s := by omega
    have h2 : s * (t - 1) + s = s * (t - 1 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have h3 : t - 1 + 1 = t := by omega
    rw [h1, h2, h3]
  rw [h, Nat.mul_div_cancel_left _ hs]

/-! ## §2  Source-bad items and the two frozen allowances (`08:538--577`)

`08:544--553`: an item of `I_c` is *source-bad* when fewer than `L_src` distinct
seed rows retain a protected representative; making it bad costs
`u_c (m - s(t-1)) = u_c kappa_X m > m u_c/2` labelled row deletions.
`08:566--577`: charging each bad item against its protected reservoir under
`eq:source-protection-gate` leaves fewer than `(s/2) delta_v(G)|V|` bad vertex
items and fewer than `s/2` bad blocker items -- exactly the two `RetentionOK`
allowances of `04:484--495`.

Following coverage limit 1, the labelled universe enters only through
`|I_c|`, `m` and `u_c`. -/

/-- **Aux 9 (the charging device).**  If `nbad` objects each cost at least
`cost > 0` out of a total spend `del` that is capped by `budget`, then
`nbad <= budget/cost`.  Completely general; both frozen charges are instances. -/
theorem card_le_of_charged {nbad cost del budget : ℝ} (hcost : 0 < cost)
    (h1 : nbad * cost ≤ del) (h2 : del ≤ budget) :
    nbad ≤ budget / cost := by
  rw [le_div_iff₀ hcost]
  linarith

/-- **Aux 10 (`08:546--553`).**  Under the source-row gate one source-bad
class-`c` item costs strictly more than `m u_c/2` labelled row deletions:
its cost is `u_c (m - s(t-1)) = u_c kappa_X m` and `kappa_X > 1/2`.
General in `u_c`. -/
theorem badItem_cost_gt_half {a b₀ s m : ℕ} {u : ℝ} (hs : 0 < s)
    (hu : 0 < u) (hgate : denseSourceRowGate a b₀ s) :
    (m : ℝ) * u / 2
      < u * ((m : ℝ) - (s : ℝ) * (((tScale a b₀ m : ℕ) : ℝ) - 1)) := by
  have h := s_mul_tScale_pred_lt_half (a := a) (b₀ := b₀) (m := m) hs hgate
  nlinarith [h, hu]

/-- **Aux 11 (`08:566--568`, the charging step).**  If each of `nbad` bad items
costs at least `m u/2` deletions and the class-`c` deletion spend is capped by
`(eta_C/nu) |I_c| m u` -- the reservoir of mass `nu` receiving an `eta_C`
fraction of the ambient rows -- then `nbad <= 2 eta_C |I_c| / nu`.
General; the frozen `nu` is filled in by the two allowances below. -/
theorem card_sourceBad_le {ηC ν Ic mR u del nbad : ℝ} (hν : 0 < ν)
    (hm : 0 < mR) (hu : 0 < u)
    (hcost : nbad * (mR * u / 2) ≤ del)
    (hbudget : del ≤ ηC / ν * (Ic * mR * u)) :
    nbad ≤ 2 * ηC * Ic / ν := by
  have hc : 0 < mR * u / 2 := by positivity
  have h := card_le_of_charged hc hcost hbudget
  have hrw : ηC / ν * (Ic * mR * u) / (mR * u / 2) = 2 * ηC * Ic / ν := by
    field_simp
  rwa [hrw] at h

/-- **`08:566--577`, the vertex allowance.**  Under `eq:source-protection-gate`
and `|I_V| = 4s|V|`, fewer than `(s/2) delta_v(G) |V|` vertex items are
source-bad -- the first `RetentionOK` allowance of `04:484--489`.  The strict
inequality is exactly the "spare factor" of `08:575--577`: the gate's own
factor `1/2` leaves the proved bound at `(s/4) delta_v |V|`.
General in `eta_C`, `delta_v`, `s`, `|V|`, `m` and `u_V`. -/
theorem sourceBad_vertex_allowance {ηC δv mR u del nbad : ℝ} {s Nv : ℕ}
    (hs : 0 < s) (hδ : 0 < δv) (hN : 0 < Nv)
    (hm : 0 < mR) (hu : 0 < u)
    (hgate : sourceProtectionGate ηC δv s)
    (hcost : nbad * (mR * u / 2) ≤ del)
    (hbudget : del ≤ ηC / nuSrcR * ((4 * (s : ℝ) * (Nv : ℝ)) * mR * u)) :
    nbad < (s : ℝ) / 2 * δv * (Nv : ℝ) := by
  have hν : (0 : ℝ) < nuSrcR := by
    rw [protectedMasses_agree.2.1]; norm_num
  have hbound := card_sourceBad_le hν hm hu hcost hbudget
  -- the gate's second clause
  have hgate2 : ηC ≤ nuSrcR * δv / 32 := by
    have hmin : min (nuTempR * rhoTemp / (s : ℝ))
        (min (nuSrcR * δv / 16) (nuSrcR / (16 * ((s : ℝ) - 3))))
        ≤ nuSrcR * δv / 16 := le_trans (min_le_right _ _) (min_le_left _ _)
    have := hgate
    unfold sourceProtectionGate at this
    linarith
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hN' : (0 : ℝ) < (Nv : ℝ) := by exact_mod_cast hN
  have hkey : ηC * (8 * (s : ℝ) * (Nv : ℝ))
      ≤ (nuSrcR * δv / 32) * (8 * (s : ℝ) * (Nv : ℝ)) :=
    mul_le_mul_of_nonneg_right hgate2 (by positivity)
  have hstep : 2 * ηC * (4 * (s : ℝ) * (Nv : ℝ)) / nuSrcR
      ≤ (s : ℝ) / 4 * δv * (Nv : ℝ) := by
    rw [div_le_iff₀ hν]
    nlinarith [hkey]
  have hp : (0 : ℝ) < (s : ℝ) * δv * (Nv : ℝ) := by positivity
  have hlast : (s : ℝ) / 4 * δv * (Nv : ℝ) < (s : ℝ) / 2 * δv * (Nv : ℝ) := by
    nlinarith [hp]
  linarith

/-- **`08:566--577`, the blocker allowance.**  Under `eq:source-protection-gate`
and `|I_B| = 4s(s-3)`, fewer than `s/2` blocker items are source-bad -- the
second `RetentionOK` allowance of `04:490--493`.  The proved bound is `s/4`;
again the gate's factor `1/2` is the spare factor of `08:575--577`.
The hypothesis `3 < s` is not decoration: the frozen third clause of
`eq:source-protection-gate` has a division pole at `s = 3`, recorded in the
banked `sourceProtectionGate_pole_at_s_three`. -/
theorem sourceBad_blocker_allowance {ηC δv mR u del nbad : ℝ} {s : ℕ}
    (hs : 3 < s) (hm : 0 < mR) (hu : 0 < u)
    (hgate : sourceProtectionGate ηC δv s)
    (hcost : nbad * (mR * u / 2) ≤ del)
    (hbudget : del ≤ ηC / nuSrcR * ((4 * (s : ℝ) * ((s : ℝ) - 3)) * mR * u)) :
    nbad < (s : ℝ) / 2 := by
  have hν : (0 : ℝ) < nuSrcR := by
    rw [protectedMasses_agree.2.1]; norm_num
  have hbound := card_sourceBad_le hν hm hu hcost hbudget
  have hs' : (3 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs3 : (0 : ℝ) < (s : ℝ) - 3 := by linarith
  have hgate3 : ηC ≤ nuSrcR / (32 * ((s : ℝ) - 3)) := by
    have hmin : min (nuTempR * rhoTemp / (s : ℝ))
        (min (nuSrcR * δv / 16) (nuSrcR / (16 * ((s : ℝ) - 3))))
        ≤ nuSrcR / (16 * ((s : ℝ) - 3)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hg := hgate
    unfold sourceProtectionGate at hg
    have : ηC ≤ 1 / 2 * (nuSrcR / (16 * ((s : ℝ) - 3))) := by linarith
    have hrw : 1 / 2 * (nuSrcR / (16 * ((s : ℝ) - 3)))
        = nuSrcR / (32 * ((s : ℝ) - 3)) := by
      field_simp
      ring
    linarith [hrw ▸ this]
  have hstep : 2 * ηC * (4 * (s : ℝ) * ((s : ℝ) - 3)) / nuSrcR ≤ (s : ℝ) / 4 := by
    rw [div_le_iff₀ hν]
    have hηC : ηC * (32 * ((s : ℝ) - 3)) ≤ nuSrcR := by
      rw [← le_div_iff₀ (by positivity : (0:ℝ) < 32 * ((s : ℝ) - 3))]
      exact hgate3
    nlinarith [hηC, hs3]
  have : (0 : ℝ) < (s : ℝ) := by linarith
  linarith

/-! ## §3  Source ownership (`08:579--594`, Candidate A)

`08:586--587` says: "Choose an index `own(i)` maximizing `ell_{i,j}`, breaking
ties deterministically."  Candidate A takes that literally -- `ownBranch` is
the *least* index of the argmax set, so it is a function of `ell` and the
tie-break is the `Finset.min'`.  The frozen readout `ell_{i,own(i)} >= t` of
`08:588--591` is then a theorem, not a field. -/

/-- The argmax set of a branch-count vector.  `08:586`. -/
def maxSet {s : ℕ} (ℓ : Fin s → ℕ) : Finset (Fin s) :=
  Finset.univ.filter fun j => ∀ k : Fin s, ℓ k ≤ ℓ j

/-- **Aux 12.**  The argmax set of a nonempty index type is nonempty.
General. -/
theorem maxSet_nonempty {s : ℕ} (j₀ : Fin s) (ℓ : Fin s → ℕ) :
    (maxSet ℓ).Nonempty := by
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin s)) ℓ ⟨j₀, Finset.mem_univ j₀⟩
  refine ⟨j, ?_⟩
  simp only [maxSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun k => hj k (Finset.mem_univ k)

/-- `own(i)` (`08:586--587`): the least maximizer of the branch counts.  The
basepoint `j₀` only witnesses that `Fin s` is nonempty; the value does not
depend on it (`ownBranch_basepoint_irrelevant`). -/
def ownBranch {s : ℕ} (j₀ : Fin s) (ℓ : Fin s → ℕ) : Fin s :=
  (maxSet ℓ).min' (maxSet_nonempty j₀ ℓ)

/-- **Aux 13.**  `own` is a maximizer: every branch count is at most the count
at `own`.  General -- this is the defining property of `08:586`. -/
theorem le_ownBranch {s : ℕ} (j₀ : Fin s) (ℓ : Fin s → ℕ) (k : Fin s) :
    ℓ k ≤ ℓ (ownBranch j₀ ℓ) := by
  have hmem := Finset.min'_mem (maxSet ℓ) (maxSet_nonempty j₀ ℓ)
  simp only [maxSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem k

/-- **Aux 14 (the deterministic tie-break of `08:586--587`).**  `own` is the
*least* maximizer.  General. -/
theorem ownBranch_least {s : ℕ} (j₀ : Fin s) (ℓ : Fin s → ℕ) {j : Fin s}
    (hj : ∀ k : Fin s, ℓ k ≤ ℓ j) : ownBranch j₀ ℓ ≤ j := by
  refine Finset.min'_le _ _ ?_
  simp only [maxSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hj

/-- **Aux 15 (the basepoint is inert).**  `ownBranch` does not depend on the
nonemptiness witness, so the tie-break really is a function of `ell` alone. -/
theorem ownBranch_basepoint_irrelevant {s : ℕ} (j₀ j₁ : Fin s) (ℓ : Fin s → ℕ) :
    ownBranch j₀ ℓ = ownBranch j₁ ℓ := rfl

/-- **Aux 16 (identity test).**  On a constant count vector every index is a
maximizer, so the tie-break returns the least index of `Fin s`.  General. -/
theorem ownBranch_of_constant {s : ℕ} (j₀ : Fin s) (c : ℕ) (j : Fin s) :
    ownBranch j₀ (fun _ => c) ≤ j :=
  ownBranch_least j₀ _ (fun _ => le_refl c)

/-- **Aux 17 (pigeonhole).**  `sum_j ell_j <= s * ell_{own}`.  General. -/
theorem sum_le_card_mul_ownBranch {s : ℕ} (j₀ : Fin s) (ℓ : Fin s → ℕ) :
    ∑ j : Fin s, ℓ j ≤ s * ℓ (ownBranch j₀ ℓ) := by
  have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin s)) ℓ
    (ℓ (ownBranch j₀ ℓ)) (fun k _ => le_ownBranch j₀ ℓ k)
  simpa [Finset.card_univ, smul_eq_mul] using h

/-- **`08:588--591`, the frozen ownership readout.**  If the retained
representatives of an item split over the `s` branches with
`sum_j ell_j = L_src = s(t-1)+1` -- the identity `08:583--585` charged to
`lem:dense-synchronisation` -- then the owning branch carries at least `t` of
them, which is `ceil(L_src/s) = t` (`ceil_Lsrc_div`).
General in `s`, `t` and `ell`; a claim about the pinned `ownBranch`, not an
existential. -/
theorem tScale_le_own_representatives {s t : ℕ} (j₀ : Fin s) (ℓ : Fin s → ℕ)
    (ht : 1 ≤ t) (hsum : ∑ j : Fin s, ℓ j = Lsrc s t) :
    t ≤ ℓ (ownBranch j₀ ℓ) := by
  rcases Nat.lt_or_ge (ℓ (ownBranch j₀ ℓ)) t with hcon | hok
  case inr => exact hok
  exfalso
  have hle : ℓ (ownBranch j₀ ℓ) ≤ t - 1 := by omega
  have h1 : ∑ j : Fin s, ℓ j ≤ s * (t - 1) :=
    le_trans (sum_le_card_mul_ownBranch j₀ ℓ) (Nat.mul_le_mul_left s hle)
  rw [hsum] at h1
  unfold Lsrc at h1
  omega

/-- **`08:592--594`, the partition.**  The fibres of `own` partition any finite
set of nonbad source items among the `s` dynamic transcript branches.  General;
this is the frozen "Consequently `own` partitions all nonbad source items among
the `s` dynamic transcript branches". -/
theorem own_partitions {Item : Type*} {s : ℕ}
    (I : Finset Item) (own : Item → Fin s) :
    I.card = ∑ j : Fin s, (I.filter fun i => own i = j).card :=
  Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (own i))

/-! ## §4  The witness supply (`08:596--611`)

`08:596--599`: for each witnessed source coordinate choose one branch, breaking
ties deterministically, and let `U_j` be the set assigned to branch `j`.  The
`U_j` are disjoint by construction, and `eq:witness-supply` `sum_j w_j >= zeta
q_2` is the S1 output of `thm:guarded-source` read through that partition.

The assignment is modelled exactly as the frozen text describes it: a function
from witnessed coordinates to branches, with `U_j` its fibres.  Disjointness is
then a theorem, never a hypothesis. -/

/-- `U_j` (`08:598--602`): the witnessed coordinates assigned to branch `j`. -/
def witnessSets {Coord : Type*} [DecidableEq Coord] {s : ℕ} (Wit : Finset Coord)
    (assign : Coord → Fin s) (j : Fin s) : Finset Coord :=
  Wit.filter fun α => assign α = j

/-- **Aux 18 (`08:599`).**  "The sets `U_j` are disjoint."  General. -/
theorem witnessSets_disjoint {Coord : Type*} [DecidableEq Coord] {s : ℕ}
    (Wit : Finset Coord) (assign : Coord → Fin s) {j j' : Fin s} (h : j ≠ j') :
    Disjoint (witnessSets Wit assign j) (witnessSets Wit assign j') := by
  refine Finset.disjoint_left.2 ?_
  intro α hα hα'
  simp only [witnessSets, Finset.mem_filter] at hα hα'
  exact h (hα.2 ▸ hα'.2.symm ▸ rfl)

/-- **Aux 19.**  `sum_j w_j = |Wit|`.  General; the frozen text needs only the
`>=` direction, but the exact identity is what makes the partition honest. -/
theorem sum_card_witnessSets {Coord : Type*} [DecidableEq Coord] {s : ℕ}
    (Wit : Finset Coord) (assign : Coord → Fin s) :
    ∑ j : Fin s, (witnessSets Wit assign j).card = Wit.card :=
  (Finset.card_eq_sum_card_fiberwise (fun α _ => Finset.mem_univ (assign α))).symm

/-- **`eq:witness-supply` (`08:604--607`).**  From the S1 output of
`thm:guarded-source` (`04:515--519`), `zeta q_2 <= |Wit|`, the branchwise
witness counts sum to at least `zeta q_2`.  `thm:guarded-source` itself is the
explicit named hypothesis `hwit`; it is banked separately as
`GuardedSourceSlab.guardedSource` and is not re-proved here.
General in `zeta`, `q_2`, `Wit` and the assignment. -/
theorem witnessSupply {Coord : Type*} [DecidableEq Coord] {s q₂ : ℕ} {ζ : ℝ}
    (Wit : Finset Coord) (assign : Coord → Fin s)
    (hwit : ζ * (q₂ : ℝ) ≤ (Wit.card : ℝ)) :
    ζ * (q₂ : ℝ) ≤ ∑ j : Fin s, ((witnessSets Wit assign j).card : ℝ) := by
  have h : ∑ j : Fin s, ((witnessSets Wit assign j).card : ℝ)
      = ((∑ j : Fin s, (witnessSets Wit assign j).card : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [h, sum_card_witnessSets]
  exact hwit

/-! ## §5  Template-bad coordinates and `lem:template-defect` (`08:616--662`)

`08:616--623` calls a coordinate `alpha` *template-bad for `j`* when, in at
least one of the `q_1` Stage-1 blocks, the projection of the branch's retained
rows represents fewer than `t` distinct seed rows.  Following coverage limit 4,
the projection enters through its support
`supp alpha ⊆ [q_1] x Rows(R) = Rows(M_1)`, whose Stage-1 block slices carry the
frozen badness test; the density of `08:641--646` is then computed, not
assumed. -/

section BlockSupport

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw] {q₁ : ℕ}

/-- The support of a one-coordinate projection in `Rows(M_1) = [q_1] x Rows(R)`
(`08:641--642`), given blockwise by its Stage-1 slices. -/
def blockSupp (g : Fin q₁ → Finset Rw) : Finset (Fin q₁ × Rw) :=
  Finset.univ.filter fun p => p.2 ∈ g p.1

/-- **Aux 20.**  The Stage-1 block slice of `blockSupp g` at `β` is
`{β} × g β`.  General. -/
theorem card_blockSlice (g : Fin q₁ → Finset Rw) (β : Fin q₁) :
    ((blockSupp g).filter fun p => p.1 = β).card = (g β).card := by
  have hset : ((blockSupp g).filter fun p => p.1 = β)
      = ({β} : Finset (Fin q₁)) ×ˢ g β := by
    ext ⟨b, r⟩
    simp only [blockSupp, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, rfl⟩
      exact ⟨rfl, hr⟩
    · rintro ⟨rfl, hr⟩
      exact ⟨hr, rfl⟩
  rw [hset, Finset.card_product, Finset.card_singleton, one_mul]

/-- **Aux 21.**  `|blockSupp g| = sum_β |g β|`.  General. -/
theorem card_blockSupp (g : Fin q₁ → Finset Rw) :
    (blockSupp g).card = ∑ β : Fin q₁, (g β).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : Fin q₁ × Rw => p.1) (t := Finset.univ)
    (fun p _ => Finset.mem_univ p.1)]
  exact Finset.sum_congr rfl fun β _ => card_blockSlice g β

omit [DecidableEq Rw] in
/-- **Aux 22.**  Every Stage-1 block slice of any support has at most
`m = |Rows(R)|` elements.  General. -/
theorem card_slice_le (supp : Finset (Fin q₁ × Rw)) (β : Fin q₁) :
    (supp.filter fun p => p.1 = β).card ≤ Fintype.card Rw := by
  classical
  refine Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) ?_
  intro p hp p' hp' hsnd
  simp only [Finset.mem_coe, Finset.mem_filter] at hp hp'
  exact Prod.ext (hp.2.trans hp'.2.symm) hsnd

omit [DecidableEq Rw] in
/-- **Aux 23 (`08:634--642`).**  If one of the `q_1` Stage-1 block slices of a
support has at most `tm` elements, the whole support has at most
`(q_1 - 1) m + tm` elements.  General; this is the counting behind the frozen
density display. -/
theorem card_le_of_deficient_block (supp : Finset (Fin q₁ × Rw)) (β : Fin q₁)
    {tm : ℕ} (h : (supp.filter fun p => p.1 = β).card ≤ tm) :
    supp.card ≤ (q₁ - 1) * Fintype.card Rw + tm := by
  classical
  have hsplit : supp.card
      = ∑ b : Fin q₁, (supp.filter fun p => p.1 = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)
  have herase : (supp.filter fun p => p.1 = β).card
      + ∑ b ∈ (Finset.univ : Finset (Fin q₁)).erase β,
          (supp.filter fun p => p.1 = b).card
      = ∑ b : Fin q₁, (supp.filter fun p => p.1 = b).card :=
    Finset.add_sum_erase (Finset.univ : Finset (Fin q₁))
      (fun b => (supp.filter fun p => p.1 = b).card) (Finset.mem_univ β)
  have hrest : ∑ b ∈ (Finset.univ : Finset (Fin q₁)).erase β,
      (supp.filter fun p => p.1 = b).card ≤ (q₁ - 1) * Fintype.card Rw := by
    have hcard : ((Finset.univ : Finset (Fin q₁)).erase β).card = q₁ - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ β), Finset.card_univ,
        Fintype.card_fin]
    have := Finset.sum_le_card_nsmul ((Finset.univ : Finset (Fin q₁)).erase β)
      (fun b => (supp.filter fun p => p.1 = b).card) (Fintype.card Rw)
      (fun b _ => card_slice_le supp b)
    simpa [hcard, smul_eq_mul] using this
  omega

end BlockSupport

/-- The template-bad set `B_j^{temp}` (`08:616--623`): the coordinates whose
one-coordinate projection support has some Stage-1 block representing fewer
than `t` distinct seed rows. -/
def templateBadSet {Coord Rw : Type*} [Fintype Coord] [DecidableEq Coord]
    [Fintype Rw] [DecidableEq Rw] {q₁ : ℕ} (t : ℕ)
    (supp : Coord → Finset (Fin q₁ × Rw)) : Finset Coord :=
  Finset.univ.filter fun α => ∃ β : Fin q₁,
    ((supp α).filter fun p => p.1 = β).card < t

/-- **Aux 24 (`08:641--646`).**  The frozen density display: a support whose
total size is at most `(q_1 - 1) m + tm`, with `tm < m/8`, has density strictly
below `1 - 7/(8 q_1)` in `Rows(M_1) = [q_1] x Rows(R)`.  General in `q_1 >= 1`,
`m > 0` and `tm`. -/
theorem templateBad_density_lt {q₁ : ℕ} {m tm : ℝ} (hq : 1 ≤ (q₁ : ℝ))
    (hm : 0 < m) (ht : tm < m / 8) :
    (((q₁ : ℝ) - 1) * m + tm) / ((q₁ : ℝ) * m) < 1 - 7 / (8 * (q₁ : ℝ)) := by
  have hq0 : (0 : ℝ) < (q₁ : ℝ) := by linarith
  have hden : (0 : ℝ) < (q₁ : ℝ) * m := mul_pos hq0 hm
  rw [div_lt_iff₀ hden]
  have hrw : (1 - 7 / (8 * (q₁ : ℝ))) * ((q₁ : ℝ) * m)
      = ((q₁ : ℝ) - 1) * m + m / 8 := by
    field_simp
    ring
  rw [hrw]
  linarith

/-- **Aux 25 (`08:655--660`).**  `(1 - 7/(8 q_1))^{8 q_1} < e^{-7} < 1/1000`.
General in `q_1 >= 1`; the exponential comparison is the only analytic step in
the whole block. -/
theorem pow_one_sub_lt_thousandth {q₁ : ℕ} (hq : 1 ≤ q₁) :
    (1 - 7 / (8 * (q₁ : ℝ))) ^ (8 * q₁) < 1 / 1000 := by
  have hq1 : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q₁ : ℝ) := by linarith
  have h8 : (0 : ℝ) < 8 * (q₁ : ℝ) := by linarith
  have hfrac : 7 / (8 * (q₁ : ℝ)) ≤ 7 / 8 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hbase0 : (0 : ℝ) ≤ 1 - 7 / (8 * (q₁ : ℝ)) := by linarith
  have hexp : 1 - 7 / (8 * (q₁ : ℝ)) ≤ Real.exp (-(7 / (8 * (q₁ : ℝ)))) := by
    have := Real.add_one_le_exp (-(7 / (8 * (q₁ : ℝ))))
    linarith
  have hpow : (1 - 7 / (8 * (q₁ : ℝ))) ^ (8 * q₁)
      ≤ (Real.exp (-(7 / (8 * (q₁ : ℝ))))) ^ (8 * q₁) :=
    pow_le_pow_left₀ hbase0 hexp (8 * q₁)
  have hcollapse : (Real.exp (-(7 / (8 * (q₁ : ℝ))))) ^ (8 * q₁)
      = Real.exp (-7) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hexp7 : (1000 : ℝ) < Real.exp 7 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : ((2.7182818283 : ℝ)) ^ (7 : ℕ) ≤ (Real.exp 1) ^ (7 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 7
    have h3 : (Real.exp 1) ^ (7 : ℕ) = Real.exp 7 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h4 : (1000 : ℝ) < ((2.7182818283 : ℝ)) ^ (7 : ℕ) := by norm_num
    linarith [h3 ▸ h2]
  have hneg : Real.exp (-7) < 1 / 1000 := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 7) (by norm_num)]
    · linarith
  linarith [hcollapse ▸ hpow]

/-- **`lem:template-defect` (`08:625--662`), the template-defect bound.**
Fewer than `8 q_1` coordinates are template-bad.

The cited `(q_2,t_2,eps_2)`-balanced family (`EXPANDER-001`,
`lem:cited-expander-family`) has no Lean declaration by design; its one use
here, the simultaneous upper-fibre estimate of `08:648--653`, is the explicit
named hypothesis `hfibre`, together with the frozen numeric readout `hxdom`.
`hcontain` is the frozen "the same product": the product support of a set of
coordinates sits inside the product of the one-coordinate supports.

The other hypotheses are the frozen ones: `hq₁` and `hm` are nondegeneracy of
the Stage-1 block structure, `ht` is the scale chain `t-1 < x_cap m <= m/8` of
`08:636--640`, `hwidth` is the width condition `t_2 >= 8 q_1` of `08:648`, and
`hdens` pins `dens` to the computed density of `08:641--642`. -/
theorem templateDefect {Coord Rw : Type*} [Fintype Coord] [DecidableEq Coord]
    [Fintype Rw] [DecidableEq Rw] {q₁ t₂ t : ℕ} {ε₂ xdom : ℝ}
    (supp : Coord → Finset (Fin q₁ × Rw))
    (dens : Coord → ℝ) (prodDens : Finset Coord → ℝ)
    (hq₁ : 1 ≤ q₁) (hm : 0 < Fintype.card Rw)
    (ht : ((t : ℝ) - 1) < (Fintype.card Rw : ℝ) / 8)
    (hdens : ∀ α, dens α
      = ((supp α).card : ℝ) / ((q₁ : ℝ) * (Fintype.card Rw : ℝ)))
    (hdens0 : ∀ α, 0 ≤ dens α)
    (hwidth : 8 * q₁ ≤ t₂)
    (hcontain : ∀ S : Finset Coord, prodDens S ≤ ∏ α ∈ S, dens α)
    (hfibre : ∀ S : Finset Coord, S.card ≤ t₂ → xdom / (1 + ε₂) ≤ prodDens S)
    (hxdom : 98 / 100 ≤ xdom / (1 + ε₂)) :
    (templateBadSet t supp).card < 8 * q₁ := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · -- `t = 0`: no block can represent fewer than `0` rows, so the set is empty.
    have : templateBadSet 0 supp = ∅ := by
      ext α
      simp [templateBadSet]
    rw [this, Finset.card_empty]
    omega
  rcases Nat.lt_or_ge (templateBadSet t supp).card (8 * q₁) with hlt | hcon
  case inl => exact hlt
  exfalso
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (le_trans (le_refl (8 * q₁)) hcon)
  have hq1R : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq₁
  have hq0R : (0 : ℝ) < (q₁ : ℝ) := by linarith
  have hmR : (0 : ℝ) < (Fintype.card Rw : ℝ) := by exact_mod_cast hm
  -- each selected coordinate has small one-coordinate density
  have hsmall : ∀ α ∈ S, dens α < 1 - 7 / (8 * (q₁ : ℝ)) := by
    intro α hα
    have hbad := hSsub hα
    simp only [templateBadSet, Finset.mem_filter, Finset.mem_univ, true_and] at hbad
    obtain ⟨β, hβ⟩ := hbad
    have hle : ((supp α).filter fun p => p.1 = β).card ≤ t - 1 := by omega
    have hcard := card_le_of_deficient_block (supp α) β hle
    have hcardR : ((supp α).card : ℝ)
        ≤ ((q₁ : ℝ) - 1) * (Fintype.card Rw : ℝ) + ((t : ℝ) - 1) := by
      have h1 : (((q₁ - 1) * Fintype.card Rw + (t - 1) : ℕ) : ℝ)
          = ((q₁ : ℝ) - 1) * (Fintype.card Rw : ℝ) + ((t : ℝ) - 1) := by
        push_cast [Nat.cast_sub hq₁, Nat.cast_sub ht0]
        ring
      calc ((supp α).card : ℝ) ≤ (((q₁ - 1) * Fintype.card Rw + (t - 1) : ℕ) : ℝ) := by
            exact_mod_cast hcard
        _ = _ := h1
    rw [hdens α]
    calc ((supp α).card : ℝ) / ((q₁ : ℝ) * (Fintype.card Rw : ℝ))
        ≤ (((q₁ : ℝ) - 1) * (Fintype.card Rw : ℝ) + ((t : ℝ) - 1))
            / ((q₁ : ℝ) * (Fintype.card Rw : ℝ)) := by
          gcongr
      _ < 1 - 7 / (8 * (q₁ : ℝ)) := templateBad_density_lt hq1R hmR ht
  -- the product over the selected coordinates is tiny
  have hprod : ∏ α ∈ S, dens α ≤ (1 - 7 / (8 * (q₁ : ℝ))) ^ (8 * q₁) := by
    calc ∏ α ∈ S, dens α ≤ ∏ _α ∈ S, (1 - 7 / (8 * (q₁ : ℝ))) := by
          refine Finset.prod_le_prod (fun α _ => hdens0 α) ?_
          exact fun α hα => (hsmall α hα).le
      _ = (1 - 7 / (8 * (q₁ : ℝ))) ^ (8 * q₁) := by
          rw [Finset.prod_const, hScard]
  have htiny := pow_one_sub_lt_thousandth hq₁
  have hbig := hfibre S (by omega)
  have := hcontain S
  linarith

/-! ## §6  Diagonal-bad coordinates and `lem:aggregate-defect` (`08:664--700`)

`08:664--674`: a coordinate is *diagonal-bad* when fewer than
`ceil((1 - rho_loc)|C_1|)` underlying columns retain a diagonal representative.
The frozen sentence "That is why `B^{diag}` has no branch index" is honoured
structurally below: the aggregate bound takes one unindexed diagonal count. -/

/-- The diagonal-bad set `B^{diag}` (`08:665--671`).  `ret alpha` is the number
of underlying columns of `C_1` that retain a diagonal representative from
`D_alpha`, and `alpha` is diagonal-bad when *fewer than*
`ceil((1 - rho_loc)|C_1|)` of them do -- the frozen strict "fewer than", never
`<=`.

The local fraction is **not** a free binder.  `08:401` pins
`rho_loc = 1/4`, and the charging lemma `card_diagonalBad_le` below is stated at
the banked `DenseStageFourOpening.rhoLoc`; taking a free `ρloc` here would make
the definition and its charging lemma speak about two different objects.  The
constant is therefore consumed by pin and never re-minted or inlined as a
literal. -/
noncomputable def diagonalBadSet {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    (c₁ : ℕ) (ret : Coord → ℕ) : Finset Coord :=
  Finset.univ.filter fun α => ret α < ⌈(1 - rhoLoc) * (c₁ : ℝ)⌉₊

/-- **Aux 26 (`08:704--` , the diagonal charge).**  Making one coordinate
diagonal-bad costs the deletion of all labelled representatives of more than a
`rho_loc` fraction of its `|C_1|` underlying diagonal columns; against a
diagonal reservoir of mass `mu_D` this bounds the number of diagonal-bad
coordinates by `eta_R q_2/(rho_loc mu_D)`.  General in `c₁`, `u` and `q_2`. -/
theorem card_diagonalBad_le {ηR q₂ c₁ u del nbad : ℝ}
    (hc : 0 < c₁) (hu : 0 < u)
    (hcost : nbad * (rhoLoc * c₁ * u) ≤ del)
    (hbudget : del ≤ ηR / muR * (q₂ * c₁ * u)) :
    nbad ≤ ηR * q₂ / (rhoLoc * muR) := by
  have hρ : (0 : ℝ) < rhoLoc := by rw [rhoLoc]; norm_num
  have hμ : (0 : ℝ) < muR := by rw [protectedMasses_agree.2.2]; norm_num
  have hcpos : 0 < rhoLoc * c₁ * u := by positivity
  have h := card_le_of_charged hcpos hcost hbudget
  have hrw : ηR / muR * (q₂ * c₁ * u) / (rhoLoc * c₁ * u)
      = ηR * q₂ / (rhoLoc * muR) := by
    field_simp
  rwa [hrw] at h

/-! The general battery for the repaired `diagonalBadSet`.  It is placed after
the charging lemma so that `card_diagonalBad_le` keeps its position and its
numbering; mathematically it belongs with the definition. -/

/-- **Aux 27 (general).**  Membership in `B^{diag}` is exactly the frozen strict
test of `08:665--668`.  The round-trip characterisation of the definition;
general in `Coord`, `c₁` and `ret`. -/
theorem mem_diagonalBadSet {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {c₁ : ℕ} {ret : Coord → ℕ} (α : Coord) :
    α ∈ diagonalBadSet c₁ ret ↔ ret α < ⌈(1 - rhoLoc) * (c₁ : ℝ)⌉₊ := by
  simp [diagonalBadSet]

/-- **Aux 28 (general).**  Retaining more diagonal representatives never creates
diagonal-badness: `B^{diag}` is antitone in the retention counts.  General. -/
theorem diagonalBadSet_antitone {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {c₁ : ℕ} {ret ret' : Coord → ℕ} (h : ∀ α, ret α ≤ ret' α) :
    diagonalBadSet c₁ ret' ⊆ diagonalBadSet c₁ ret := by
  intro α hα
  rw [mem_diagonalBadSet] at hα ⊢
  exact lt_of_le_of_lt (h α) hα

/-- **Aux 29 (general).**  If every coordinate retains at least the frozen
threshold, none is diagonal-bad.  General; this is the complement of the
separating probe in §7. -/
theorem diagonalBadSet_eq_empty {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {c₁ : ℕ} {ret : Coord → ℕ}
    (h : ∀ α, ⌈(1 - rhoLoc) * (c₁ : ℝ)⌉₊ ≤ ret α) :
    diagonalBadSet c₁ ret = ∅ := by
  ext α
  simp only [mem_diagonalBadSet]
  simp [not_lt.mpr (h α)]

/-- **Aux 30 (general).**  With no underlying diagonal columns the frozen
threshold `ceil((1 - rho_loc)|C_1|)` is `0`, and the strict test makes no
coordinate diagonal-bad.  The definition degenerates the right way: nothing is
charged when there is nothing to retain. -/
theorem diagonalBadSet_of_card_zero {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    (ret : Coord → ℕ) : diagonalBadSet 0 ret = ∅ := by
  refine diagonalBadSet_eq_empty ?_
  intro α
  simp

/-- **`lem:aggregate-defect` (`08:676--700`), the aggregate defect bound.**
Under `eq:dense-defect-gates` the branchwise defect counts
`b_j = |B_j^{temp} ∪ B^{diag}|` satisfy `sum_j b_j < zeta q_2/4`.

The frozen proof is transcribed step for step: `sum_j |B_j^{temp}| < 8 s q_1`
from `lem:template-defect` (hypothesis `htemp`, one instance of the banked
`templateDefect` per branch), `8 s q_1 <= zeta q_2/8` from the middle gate,
`|B^{diag}| <= eta_R q_2/(rho_loc mu_D)` from `card_diagonalBad_le`
(hypothesis `hdiag`), and `s eta_R q_2/(rho_loc mu_D) < zeta q_2/8` from the
last gate.  `bd` is unindexed, matching `08:671--674`.
General in `s`, `q_1`, `q_2`, `t_2`, `zeta` and `eta_R`. -/
theorem aggregateDefect {s q₁ q₂ t₂ : ℕ} {ζ ηR : ℝ}
    (bt : Fin s → ℝ) (bd : ℝ) (b : Fin s → ℝ)
    (hs : 0 < s) (hζ : 0 < ζ) (hq₂ : (0 : ℝ) ≤ (q₂ : ℝ))
    (hgates : denseDefectGates t₂ q₁ q₂ s ζ ηR)
    (htemp : ∀ j : Fin s, bt j < 8 * (q₁ : ℝ))
    (hdiag : bd ≤ ηR * (q₂ : ℝ) / (rhoLoc * muR))
    (hb : ∀ j : Fin s, b j ≤ bt j + bd) :
    ∑ j : Fin s, b j < ζ * (q₂ : ℝ) / 4 := by
  have hρ : (0 : ℝ) < rhoLoc := by rw [rhoLoc]; norm_num
  have hμ : (0 : ℝ) < muR := by rw [protectedMasses_agree.2.2]; norm_num
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.1 hs
  -- template half
  have hsumbt : ∑ j : Fin s, bt j < (s : ℝ) * (8 * (q₁ : ℝ)) := by
    have := Finset.sum_lt_sum_of_nonempty hne (fun j _ => htemp j)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hmid : 64 * (s : ℝ) * (q₁ : ℝ) / ζ ≤ (q₂ : ℝ) := hgates.2.1
  have htempbound : (s : ℝ) * (8 * (q₁ : ℝ)) ≤ ζ * (q₂ : ℝ) / 8 := by
    rw [div_le_iff₀ hζ] at hmid
    linarith
  -- diagonal half
  have hlast : ηR < rhoLoc * muR * ζ / (8 * (s : ℝ)) := hgates.2.2
  have hdiagbound : (s : ℝ) * bd ≤ ζ * (q₂ : ℝ) / 8 := by
    have hstep : (s : ℝ) * bd ≤ (s : ℝ) * (ηR * (q₂ : ℝ) / (rhoLoc * muR)) := by
      exact mul_le_mul_of_nonneg_left hdiag hs'.le
    have hηR : ηR * (8 * (s : ℝ)) ≤ rhoLoc * muR * ζ := by
      rw [← le_div_iff₀ (by positivity : (0:ℝ) < 8 * (s : ℝ))]
      exact hlast.le
    have hpm : (0 : ℝ) < rhoLoc * muR := by positivity
    have hform : (s : ℝ) * (ηR * (q₂ : ℝ) / (rhoLoc * muR))
        = (ηR * (8 * (s : ℝ))) * (q₂ : ℝ) / (8 * (rhoLoc * muR)) := by
      field_simp
    have hfin : (s : ℝ) * (ηR * (q₂ : ℝ) / (rhoLoc * muR)) ≤ ζ * (q₂ : ℝ) / 8 := by
      rw [hform, div_le_iff₀ (by positivity : (0:ℝ) < 8 * (rhoLoc * muR))]
      nlinarith [mul_le_mul_of_nonneg_right hηR hq₂]
    linarith
  -- assemble
  have hsumb : ∑ j : Fin s, b j ≤ ∑ j : Fin s, (bt j + bd) :=
    Finset.sum_le_sum fun j _ => hb j
  have hsplit : ∑ j : Fin s, (bt j + bd) = (∑ j : Fin s, bt j) + (s : ℝ) * bd := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  linarith

/-! ## §7  Non-vacuity and statement poles

Every gate transcribed above is a `Prop` that the module only ever consumes as
a hypothesis.  An unsatisfiable premise bundle would make every consumer vacuous
while compiling green, so each is inhabited here, under the two-tier standard
already used by the banked synchronisation module: a *symbolic* witness general
in the frozen schedule quantities, plus a *shape-conforming* concrete probe that
is explicitly not a schedule instance. -/

/-- **Non-vacuity (symbolic, legal at the frozen Stage-1 exponent floor).**
For every `s >= 4` and every Stage-1 exponent `a` -- in particular at the frozen
floor `a >= 2432` of `06:298--315`, which no evaluable literal reaches -- there
is a Stage-2 depth `b_0 > a+1` at which `eq:dense-source-row-gate` holds with a
strictly positive `x_cap`.  Nothing is evaluated: the witness `b_0 = a+1+s` uses
only the banked `two_exponent_le_two_pow`. -/
theorem denseSourceRowGate_nondegenerate {s : ℕ} (hs : 4 ≤ s) (a : ℕ) :
    ∃ b₀ : ℕ, a + 1 < b₀ ∧ 0 < xCap a b₀ ∧ denseSourceRowGate a b₀ s := by
  refine ⟨a + 1 + s, by omega, xCap_pos _ _, ?_⟩
  unfold denseSourceRowGate xCap
  have hpow : 2 * (s : ℝ) ≤ (2 : ℝ) ^ s := by
    have h := two_exponent_le_two_pow (k := s) hs
    have h2 : (2 * (s + 2) : ℕ) ≤ 2 ^ s := h
    have : ((2 * (s + 2) : ℕ) : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith
  have hs' : (0 : ℝ) < (s : ℝ) := by
    have : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hrw : (2 : ℝ) ^ (a + 1) / 2 ^ (a + 1 + s) = 1 / 2 ^ s := by
    rw [pow_add]
    field_simp
    ring
  rw [hrw]
  exact one_div_le_one_div_of_le (by linarith) hpow

/-- **Non-vacuity (concrete, shape-conforming only).**  A locally legal probe of
the whole §1 scale at `s = 4`, `a = 0`, `b_0 = 4`, `m = 16`:
`x_cap = 1/8 = 1/(2s)` (the gate at equality), `t = 2`, `L_src = 5`,
`kappa_X = 3/4 > 1/2`.  This is **not** a schedule instance -- the frozen
schedule pins the Stage-1 exponent `a` above every evaluable literal
(`06:298--315`) -- and it is not claimed to be one.  What it establishes is that
the frozen scale is satisfiable at the frozen shapes with a *nondegenerate*
`t = 2 > 1`, so `L_src > 1` and the ownership readout is not trivial. -/
theorem denseSourceRowGate_shape_instance :
    denseSourceRowGate 0 4 4 ∧ xCap 0 4 = 1 / 8 ∧ tScale 0 4 16 = 2 ∧
      Lsrc 4 (tScale 0 4 16) = 5 ∧ kappaX 4 (tScale 0 4 16) 16 = 3 / 4 := by
  have hx : xCap 0 4 = 1 / 8 := by
    unfold xCap; norm_num
  have ht : tScale 0 4 16 = 2 := by
    unfold tScale
    rw [hx]
    norm_num
  refine ⟨?_, hx, ht, ?_, ?_⟩
  · unfold denseSourceRowGate
    rw [hx]; norm_num
  · rw [ht]; unfold Lsrc; norm_num
  · rw [ht]; unfold kappaX; norm_num

/-- **Statement pole for §1.**  The source-row gate is a real constraint: at
`x_cap = 1/2` and `s = 4` it fails, so no consumer of
`denseSourceRowGate` is quantifying over a trivially true predicate.  Concretely
`b_0 = a + 2` is illegal at every `s >= 1`. -/
theorem sourceRowGate_pole_at_large_xCap (a : ℕ) : ¬ denseSourceRowGate a (a + 2) 4 := by
  unfold denseSourceRowGate xCap
  have hrw : (2 : ℝ) ^ (a + 1) / 2 ^ (a + 2) = 1 / 2 := by
    rw [pow_succ]
    field_simp
    ring
  rw [hrw]
  norm_num

/-- **Hypothesis consistency for the vertex allowance (legal instance).**
At `s = 4`, `|V| = 1000`, `delta_v = 1/6`, `eta_C = 2^{-21}/8000`, `m = 16`,
`u_V = 1`, the whole premise bundle of `sourceBad_vertex_allowance` is
satisfied with a **nonzero** bad count `nbad = 1`.  So the bundle does not force
the source-bad set to be empty, and no `False` follows from it.  All frozen side
conditions hold: `s >= 4`, `delta_v > 0`, `eta_C > 0`, and
`eq:source-protection-gate` is met with the template clause tight. -/
theorem sourceBad_vertex_hypotheses_consistent :
    ∃ (ηC δv mR u del nbad : ℝ) (s Nv : ℕ),
      4 ≤ s ∧ 0 < δv ∧ 0 < Nv ∧ 0 < ηC ∧ 0 < nbad ∧ 0 < mR ∧ 0 < u ∧
        sourceProtectionGate ηC δv s ∧
        nbad * (mR * u / 2) ≤ del ∧
        del ≤ ηC / nuSrcR * ((4 * (s : ℝ) * (Nv : ℝ)) * mR * u) ∧
        nbad < (s : ℝ) / 2 * δv * (Nv : ℝ) := by
  refine ⟨1 / (2 ^ 21 * 8000), 1 / 6, 16, 1, 8, 1, 4, 1000, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num,
    ?_, by norm_num⟩
  · unfold sourceProtectionGate
    rw [protectedMasses_agree.1, protectedMasses_agree.2.1, rhoTemp]
    norm_num
  · rw [protectedMasses_agree.2.1]
    norm_num

/-- **Hypothesis consistency for the blocker allowance (legal instance).**
At `s = 128`, `delta_v = 1/6`, `eta_C = 2^{-21}/256000`, `m = 16`, `u_B = 1`,
the premise bundle of `sourceBad_blocker_allowance` is satisfied with a
**nonzero** bad count `nbad = 1`.  The frozen constants make the template clause
of `eq:source-protection-gate` the binding one, so the charging capacity
`2 eta_C |I_B| / nu_B = (s-3)/125` only admits a whole bad blocker item once
`s >= 128`; the witness is taken there, and `s = 128` is a power of two above
the frozen floor `4` and keeps the third clause off its `s = 3` pole. -/
theorem sourceBad_blocker_hypotheses_consistent :
    ∃ (ηC δv mR u del nbad : ℝ) (s : ℕ),
      3 < s ∧ 0 < ηC ∧ 0 < nbad ∧ 0 < mR ∧ 0 < u ∧
        sourceProtectionGate ηC δv s ∧
        nbad * (mR * u / 2) ≤ del ∧
        del ≤ ηC / nuSrcR * ((4 * (s : ℝ) * ((s : ℝ) - 3)) * mR * u) ∧
        nbad < (s : ℝ) / 2 := by
  refine ⟨1 / (2 ^ 21 * 256000), 1 / 6, 16, 1, 8, 1, 128, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, by norm_num, ?_, by norm_num⟩
  · unfold sourceProtectionGate
    rw [protectedMasses_agree.1, protectedMasses_agree.2.1, rhoTemp]
    norm_num
  · rw [protectedMasses_agree.2.1]
    norm_num

/-- **Statement pole for `ownBranch`.**  The owner is not the basepoint and not
the least index: at `s = 2` with counts `ell 0 = 0`, `ell 1 = 1`, the frozen
"index maximizing `ell`" is `1`, so a consumer that substituted a fixed index
for `own` would violate `08:588--591`. -/
theorem ownBranch_is_not_the_basepoint :
    ownBranch (0 : Fin 2) (fun j => if j = 0 then 0 else 1) = 1 := by
  have hmax : ∀ k : Fin 2,
      (fun j : Fin 2 => if j = 0 then 0 else 1) k
        ≤ (fun j : Fin 2 => if j = 0 then 0 else 1) 1 := by decide
  have hle := ownBranch_least (0 : Fin 2) (fun j => if j = 0 then 0 else 1) hmax
  have hne : ownBranch (0 : Fin 2) (fun j => if j = 0 then 0 else 1) ≠ 0 := by
    intro h
    have := le_ownBranch (0 : Fin 2) (fun j : Fin 2 => if j = 0 then 0 else 1) 1
    rw [h] at this
    simp at this
  omega

/-- **Hypothesis consistency for `templateDefect` (legal instance, nonempty bad
set, conclusion *not* forced by the coordinate type).**  `q_1 = 50`, `m = 16`,
`t = 2`, `t_2 = 400 = 8 q_1`, `x_dom/(1+eps_2) = 98/100`.  The coordinate `0` is
genuinely template-bad -- its Stage-1 block `0` represents a single seed row, one
short of `t = 2` -- and the conclusion `1 < 400` holds.  So the fibre estimate
and the badness hypothesis are *not* jointly contradictory at the frozen shapes,
and `templateDefect` is not vacuous.  Note `1 - 7/(8 q_1) = 1 - 7/400 = 0.9825`
while the bad coordinate's density is `785/800 = 0.98125`: strictly below the
badness threshold and still above the fibre floor `0.98`.

**Why the ambient coordinate type is `Fin 400` and not something smaller.**  The
frozen conclusion of `lem:template-defect` is `|B_j^{temp}| < 8 q_1 = 400`.  A
witness whose coordinate type has fewer than `400` inhabitants proves nothing:
`|B_j^{temp}| <= |Coord| < 400` would then hold for *every* `supp`, and no
hypothesis of `templateDefect` would do any work.  The ambient type is therefore
taken with `|Coord| = 400 = 8 q_1` exactly, so that `card < 400` fails precisely
when every coordinate is template-bad and the conclusion has content.  The clause
`8 * 50 <= Fintype.card (Fin 400)` records that on the face of the statement.

At that size the balanced-family clauses cannot be discharged by enumerating the
`2^400` subsets.  They are proved instead from two general facts about the
witness -- the density is `1` off the single bad coordinate, and `785/800` on it
-- so the product over an arbitrary `S` is `785/800` or `1`, both above the
frozen floor `98/100`.

**The clauses are the hypotheses, not a paraphrase of them.**  The final clause
is obtained by *applying* `templateDefect` to this witness at
`q_1 = 50`, `t = 2`, `t_2 = 400`, `eps_2 = 0`, `x_dom = 98/100`, so the bundle is
demonstrated to drive the theorem rather than merely to resemble its premises.

**The trivial witness fails.**  `supp = fun _ => univ` makes `templateBadSet`
empty and defeats the `Nonempty` clause; conversely `supp = fun _ => empty`
makes every coordinate bad, so `card = 400` defeats the last clause, and its
densities are `0`, defeating the fibre floor `98/100 <= prodDens S`.  The
`prodDens` slot admits no cheap witness either: it is squeezed between
`prodDens S <= prod dens` above and `98/100 <= prodDens S` below, so the constant
`0` and the constant `1` are both excluded. -/
theorem templateDefect_hypotheses_consistent :
    ∃ (supp : Fin 400 → Finset (Fin 50 × Fin 16)) (dens : Fin 400 → ℝ)
      (prodDens : Finset (Fin 400) → ℝ) (xdom ε₂ : ℝ),
      1 ≤ 50 ∧ 0 < Fintype.card (Fin 16) ∧
      (((2 : ℕ) : ℝ) - 1 < (Fintype.card (Fin 16) : ℝ) / 8) ∧ 8 * 50 ≤ 400 ∧
      8 * 50 ≤ Fintype.card (Fin 400) ∧
      (templateBadSet 2 supp).Nonempty ∧
      (∀ α, dens α
        = ((supp α).card : ℝ) / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ))) ∧
      (∀ α, 0 ≤ dens α) ∧
      (∀ S : Finset (Fin 400), prodDens S ≤ ∏ α ∈ S, dens α) ∧
      (∀ S : Finset (Fin 400), S.card ≤ 400 → xdom / (1 + ε₂) ≤ prodDens S) ∧
      (98 / 100 : ℝ) ≤ xdom / (1 + ε₂) ∧
      (templateBadSet 2 supp).card < 8 * 50 := by
  classical
  set g : Fin 50 → Finset (Fin 16) := fun β => if β = 0 then {0} else Finset.univ with hg
  set supp : Fin 400 → Finset (Fin 50 × Fin 16) :=
    fun α => if α = 0 then blockSupp g else Finset.univ with hsupp
  have hg0 : (g 0).card = 1 := by simp [hg]
  have hgβ : ∀ β : Fin 50, β ≠ 0 → (g β).card = 16 := by
    intro β hβ; simp [hg, hβ]
  have hcard0 : (blockSupp g).card = 785 := by
    rw [card_blockSupp]
    have hsplit : (g 0).card
        + ∑ β ∈ (Finset.univ : Finset (Fin 50)).erase 0, (g β).card
        = ∑ β : Fin 50, (g β).card :=
      Finset.add_sum_erase (Finset.univ : Finset (Fin 50))
        (fun β => (g β).card) (Finset.mem_univ 0)
    have hconst : ∀ β ∈ (Finset.univ : Finset (Fin 50)).erase 0, (g β).card = 16 :=
      fun β hβ => hgβ β (Finset.ne_of_mem_erase hβ)
    rw [← hsplit, Finset.sum_congr rfl hconst, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, hg0]
  have hs0 : supp 0 = blockSupp g := by simp [hsupp]
  have hsα : ∀ α : Fin 400, α ≠ 0 → supp α = Finset.univ := by
    intro α hα; simp [hsupp, hα]
  have hc0 : (supp 0).card = 785 := by rw [hs0, hcard0]
  have hcα : ∀ α : Fin 400, α ≠ 0 → (supp α).card = 800 := by
    intro α hα
    rw [hsα α hα, Finset.card_univ]
    simp
  have hslice0 : ((supp 0).filter fun p => p.1 = 0).card = 1 := by
    rw [hs0, card_blockSlice, hg0]
  have hsliceUniv : ∀ β : Fin 50,
      ((Finset.univ : Finset (Fin 50 × Fin 16)).filter fun p => p.1 = β).card = 16 := by
    intro β
    have heq : ((Finset.univ : Finset (Fin 50 × Fin 16)).filter fun p => p.1 = β)
        = ({β} : Finset (Fin 50)) ×ˢ (Finset.univ : Finset (Fin 16)) := by
      ext ⟨b, r⟩
      simp [eq_comm]
    rw [heq, Finset.card_product]
    simp
  have hbad : templateBadSet 2 supp = {0} := by
    ext α
    simp only [templateBadSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      by_contra hα
      obtain ⟨β, hβ⟩ := h
      rw [hsα α hα, hsliceUniv β] at hβ
      omega
    · rintro rfl
      exact ⟨0, by rw [hslice0]; norm_num⟩
  have hne : (templateBadSet 2 supp).Nonempty := by
    rw [hbad]
    exact Finset.singleton_nonempty 0
  -- the frozen fibre floor, proved uniformly in `S` rather than by enumeration
  have hdenom : ((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ) = 800 := by
    norm_num [Fintype.card_fin]
  have hone : ∀ α : Fin 400, α ≠ 0 →
      ((supp α).card : ℝ) / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)) = 1 := by
    intro α hα
    rw [hcα α hα, hdenom]
    norm_num
  have hkey : ∀ S : Finset (Fin 400), (98 / 100 : ℝ)
      ≤ ∏ α ∈ S, ((supp α).card : ℝ)
          / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)) := by
    intro S
    by_cases h0 : (0 : Fin 400) ∈ S
    · have herase : ∏ α ∈ S.erase 0, ((supp α).card : ℝ)
          / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)) = 1 :=
        Finset.prod_eq_one fun α hα => hone α (Finset.ne_of_mem_erase hα)
      rw [← Finset.mul_prod_erase _ _ h0, herase, hc0, hdenom]
      norm_num
    · have hall : ∏ α ∈ S, ((supp α).card : ℝ)
          / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)) = 1 :=
        Finset.prod_eq_one fun α hα => hone α (fun h => h0 (h ▸ hα))
      rw [hall]
      norm_num
  have hnonneg : ∀ α : Fin 400,
      0 ≤ ((supp α).card : ℝ) / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)) := by
    intro α
    exact div_nonneg (Nat.cast_nonneg _) (by rw [hdenom]; norm_num)
  have hfibre : ∀ S : Finset (Fin 400), S.card ≤ 400 →
      (98 / 100 : ℝ) / (1 + 0) ≤ ∏ α ∈ S, ((supp α).card : ℝ)
          / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)) := by
    intro S _
    rw [add_zero, div_one]
    exact hkey S
  -- the conclusion is obtained by *applying* the headline theorem to this witness
  have hconc : (templateBadSet 2 supp).card < 8 * 50 :=
    templateDefect (q₁ := 50) (t₂ := 400) (t := 2) (ε₂ := 0) (xdom := 98 / 100)
      supp
      (fun α => ((supp α).card : ℝ) / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)))
      (fun S => ∏ α ∈ S, ((supp α).card : ℝ)
        / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)))
      (by norm_num) (by norm_num [Fintype.card_fin])
      (by norm_num [Fintype.card_fin]) (fun _ => rfl) hnonneg (by norm_num)
      (fun _ => le_refl _) hfibre (by norm_num)
  refine ⟨supp,
    fun α => ((supp α).card : ℝ) / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)),
    fun S => ∏ α ∈ S, ((supp α).card : ℝ)
      / (((50 : ℕ) : ℝ) * (Fintype.card (Fin 16) : ℝ)),
    98 / 100, 0,
    by norm_num, by norm_num [Fintype.card_fin], by norm_num [Fintype.card_fin],
    by norm_num, by norm_num [Fintype.card_fin],
    hne, fun _ => rfl, hnonneg, fun _ => le_refl _, hfibre, by norm_num, hconc⟩

/-- **Non-vacuity of the ownership readout (legal instance).**  At `s = 4`,
`t = 2`, `L_src = s(t-1)+1 = 5`, the branch counts `(2,1,1,1)` sum to `L_src`,
and `tScale_le_own_representatives` returns a branch carrying at least `t = 2`
representatives.  Nondegenerate: `t = 2 > 1`, the split is not uniform, and the
bound is attained exactly, so no slack is being hidden. -/
theorem ownership_legal_instance :
    (∑ j : Fin 4, (if j = 0 then (2 : ℕ) else 1)) = Lsrc 4 2 ∧
      2 ≤ (fun j : Fin 4 => if j = 0 then (2 : ℕ) else 1)
            (ownBranch (0 : Fin 4) (fun j : Fin 4 => if j = 0 then 2 else 1)) := by
  have hsum : (∑ j : Fin 4, (if j = 0 then (2 : ℕ) else 1)) = Lsrc 4 2 := by decide
  exact ⟨hsum, tScale_le_own_representatives (0 : Fin 4) _ (by norm_num) hsum⟩

/-- **Non-vacuity for `diagonalBadSet` (legal instance, separating).**
At `|C_1| = 8` the pinned `rho_loc = 1/4` makes the frozen threshold
`ceil((1 - rho_loc)|C_1|) = ceil(6) = 6` exact, so the filter can be probed on
both sides without any ceiling slack.  With retention counts `ret 0 = 5` and
`ret 1 = 6`, the coordinate `0` **is** diagonal-bad and the coordinate `1` is
**not**: `B^{diag}` is neither empty nor all of the coordinate type.  That is the
content of the non-vacuity check -- a witness on which every coordinate is bad
(or none is) would separate nothing and would leave the frozen strict "fewer
than" of `08:665--668` untested.

**The trivial witness fails.**  `ret = fun _ => 0` puts *every* coordinate in
`B^{diag}`, so it violates both `(1 : Fin 2) ∉ diagonalBadSet c₁ ret` and
`card = 1`; `ret = fun _ => c₁` puts none in, violating
`(0 : Fin 2) ∈ diagonalBadSet c₁ ret`.  The threshold clause
`ceil((1 - rho_loc)|C_1|) = 6` in turn forbids collapsing `c₁` to `0`, where the
filter is empty for every `ret`. -/
theorem diagonalBadSet_nondegenerate :
    ∃ (c₁ : ℕ) (ret : Fin 2 → ℕ),
      0 < c₁ ∧ ⌈(1 - rhoLoc) * (c₁ : ℝ)⌉₊ = 6 ∧ ret 0 < 6 ∧ 6 ≤ ret 1 ∧
        (0 : Fin 2) ∈ diagonalBadSet c₁ ret ∧
        (1 : Fin 2) ∉ diagonalBadSet c₁ ret ∧
        (diagonalBadSet c₁ ret).card = 1 := by
  classical
  have hthr : ⌈(1 - rhoLoc) * ((8 : ℕ) : ℝ)⌉₊ = 6 := by
    have h : (1 - rhoLoc) * ((8 : ℕ) : ℝ) = 6 := by
      rw [rhoLoc]; norm_num
    rw [h]
    norm_num
  have hset : diagonalBadSet 8 (fun α : Fin 2 => if α = 0 then 5 else 6) = {0} := by
    ext α
    simp only [diagonalBadSet, Finset.mem_filter, Finset.mem_univ, true_and,
      hthr, Finset.mem_singleton]
    fin_cases α <;> norm_num
  refine ⟨8, fun α : Fin 2 => if α = 0 then 5 else 6, by norm_num, hthr, by norm_num,
    by norm_num, ?_, ?_, ?_⟩
  · rw [hset]; exact Finset.mem_singleton_self 0
  · rw [hset]; simp
  · rw [hset, Finset.card_singleton]

/-- **Hypothesis consistency for `card_diagonalBad_le` (gate-legal instance, all
three inequalities attained).**  The diagonal charge is one half of
`lem:aggregate-defect`, and the frozen text only ever applies it under
`eq:dense-defect-gates` (`08:679--685`).  A witness for the charging bundle
alone is therefore not enough: it could sit at a `(zeta, q_2, eta_R)` point the
gates forbid, and a green build would not see that.  So the gate bundle is
carried **on the face of this statement** and the witness is taken at the same
gate-legal point as `aggregateDefect_hypotheses_consistent`:

* `s = 4`, `q_1 = 1`, `t_2 = 8`, `zeta = 1/24` (the frozen maximum of
  `zeta = gamma/24`, `08:402`), `q_2 = 6144` and `eta_R = 10^{-6}`.  The first
  two gate clauses hold with **equality** (`8 q_1 = 8 = t_2` and
  `64 s q_1/zeta = 6144 = q_2`); the third holds with the frozen strict
  inequality, `10^{-6} < rho_loc mu_D zeta/(8s) = 1/565248`.
* `|C_1| = 8`, multiplicity `u = 1`, deletion count `del = 9043968/10^6` and a
  **strictly positive** bad count `nbad = 4521984/10^6`, at the pinned
  `rho_loc = 1/4` and the banked `mu_D = mu_Sigma = 1/184`.

All three charging inequalities are attained.  The cost side is
`nbad (rho_loc |C_1| u) = 2 nbad = 9043968/10^6 = del`; the budget side is
`(eta_R/mu_D)(q_2 |C_1| u) = 184 * 49152/10^6 = 9043968/10^6 = del`; and the
frozen conclusion `nbad <= eta_R q_2/(rho_loc mu_D)` reads
`4521984/10^6 <= 6144 * 736/10^6` with both sides equal.  Each of the three is
recorded together with its reverse, so nothing is left with hidden slack, and
the forward conclusion is obtained by *applying* `card_diagonalBad_le` to the
witness, so the lemma is exercised rather than merely resembled.

**The trivial witness fails.**  `nbad = 0` -- the reading under which the frozen
charge says nothing -- is excluded by `0 < nbad`; inflating `eta_R` or `q_2` to
make the bound vacuously loose is excluded twice over, by the reverse inequality
`eta_R q_2/(rho_loc mu_D) <= nbad` and now by the gate clause itself, whose
ceiling `eta_R < rho_loc mu_D zeta/(8s)` and floor `q_2 >= 64 s q_1/zeta` pin
the admissible window from both sides; `del` arbitrarily large is excluded by
the budget pair and `del = 0` by the cost pair together with `0 < nbad`; and
`zeta = 0`, which would make the gates degenerate, is excluded by `0 < zeta`.
The branch count carries the frozen floor `4 <= s` -- asserted at `08:402`
exactly where `eq:dense-defect-gates` is applied, and fixed eight times over in
Section 04 -- rather than the weaker `0 < s`, which gate 3 already implies from
`0 < eta_R`; a certificate existentially quantifying `s` behind `0 < s` would
not have shown the charge legal at any branch count the construction uses. -/
theorem card_diagonalBad_le_hypotheses_consistent :
    ∃ (t₂ q₁ q₂ s : ℕ) (ζ ηR c₁ u del nbad : ℝ),
      4 ≤ s ∧ 0 < ζ ∧ 0 < c₁ ∧ 0 < u ∧ 0 < ηR ∧ 0 < (q₂ : ℝ) ∧ 0 < nbad ∧
        denseDefectGates t₂ q₁ q₂ s ζ ηR ∧
        nbad * (rhoLoc * c₁ * u) ≤ del ∧
        del ≤ nbad * (rhoLoc * c₁ * u) ∧
        del ≤ ηR / muR * ((q₂ : ℝ) * c₁ * u) ∧
        ηR / muR * ((q₂ : ℝ) * c₁ * u) ≤ del ∧
        nbad ≤ ηR * (q₂ : ℝ) / (rhoLoc * muR) ∧
        ηR * (q₂ : ℝ) / (rhoLoc * muR) ≤ nbad := by
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  have hcost : (4521984 / 1000000 : ℝ) * (rhoLoc * 8 * 1) ≤ 9043968 / 1000000 := by
    rw [rhoLoc]; norm_num
  have hbudget : (9043968 / 1000000 : ℝ)
      ≤ 1 / 1000000 / muR * (((6144 : ℕ) : ℝ) * 8 * 1) := by
    rw [hmu]; norm_num
  refine ⟨8, 1, 6144, 4, 1 / 24, 1 / 1000000, 8, 1, 9043968 / 1000000,
    4521984 / 1000000, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, hcost, ?_, hbudget, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_⟩
    rw [rhoLoc, hmu]
    norm_num
  · rw [rhoLoc]; norm_num
  · rw [hmu]; norm_num
  · exact card_diagonalBad_le (by norm_num) (by norm_num) hcost hbudget
  · rw [rhoLoc, hmu]; norm_num

/-- **Hypothesis consistency for `aggregateDefect` (legal instance).**
At `s = 4`, `q_1 = 1`, `t_2 = 8`, `zeta = 1/24` (the frozen maximum of
`zeta = gamma/24`), `q_2 = 6144 = 64 s q_1/zeta` and `eta_R = 10^{-6}`, the whole
premise bundle of `aggregateDefect` is satisfied with **strictly positive**
defect data: `bt_j = 7 > 0`, `bd = 1 > 0`, `b_j = 8 > 0`, and the conclusion
reads `32 < 64`.  So `eq:dense-defect-gates` together with the template and
diagonal bounds is consistent, and the aggregate bound is not vacuous.
Both gate margins are visible: the first two clauses hold with equality, and the
third has `10^{-6} < 1/565248`. -/
theorem aggregateDefect_hypotheses_consistent :
    ∃ (bt b : Fin 4 → ℝ) (bd ζ ηR : ℝ) (q₁ q₂ t₂ : ℕ),
      0 < ζ ∧ 0 < ηR ∧ 0 < bd ∧ (∀ j : Fin 4, 0 < bt j) ∧
        denseDefectGates t₂ q₁ q₂ 4 ζ ηR ∧
        (∀ j : Fin 4, bt j < 8 * (q₁ : ℝ)) ∧
        bd ≤ ηR * (q₂ : ℝ) / (rhoLoc * muR) ∧
        (∀ j : Fin 4, b j ≤ bt j + bd) ∧
        ∑ j : Fin 4, b j < ζ * (q₂ : ℝ) / 4 := by
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  refine ⟨fun _ => 7, fun _ => 8, 1, 1 / 24, 1 / 1000000, 1, 6144, 8,
    by norm_num, by norm_num, by norm_num, fun _ => by norm_num, ?_,
    fun _ => by norm_num, ?_, fun _ => by norm_num, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_⟩
    rw [rhoLoc, hmu]
    norm_num
  · rw [rhoLoc, hmu]
    norm_num
  · simp
    norm_num

/-- **Statement pole for `templateDefect`.**  The fibre hypothesis is
load-bearing: without it the conclusion is false.  At `q_1 = 1`, `t = 1` and a
support that is empty in the single Stage-1 block, *every* coordinate of an
eight-element coordinate type is template-bad, so the bad count reaches
`8 = 8 q_1`.  A proof of `templateDefect` that never used `hfibre` would
therefore be wrong. -/
theorem templateDefect_fibre_is_load_bearing :
    ¬ ((templateBadSet 1 (fun _ : Fin 8 => (∅ : Finset (Fin 1 × Fin 16)))).card
        < 8 * 1) := by
  have h : templateBadSet 1 (fun _ : Fin 8 => (∅ : Finset (Fin 1 × Fin 16)))
      = Finset.univ := by
    ext α
    simp only [templateBadSet, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    exact ⟨0, by simp⟩
  rw [h, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **Statement pole for `aggregateDefect`.**  The middle gate
`q_2 >= 64 s q_1/zeta` of `eq:dense-defect-gates` is load-bearing.  At `s = 1`,
`q_1 = 1`, `zeta = 1`, `q_2 = 1` -- where that gate fails -- the defect data
`b_j = 7`, `bt_j = 7`, `bd = 0` satisfies every *other* hypothesis of
`aggregateDefect`, including the template bound `b_j < 8 q_1`, and yet
`sum_j b_j = 7` is far above `zeta q_2/4 = 1/4`.  A proof that never used the
middle gate would therefore be wrong. -/
theorem aggregateDefect_gate_is_load_bearing :
    ∃ (bt b : Fin 1 → ℝ) (bd ζ : ℝ) (q₁ q₂ : ℕ),
      0 < ζ ∧ 0 ≤ bd ∧
      (∀ j : Fin 1, bt j < 8 * (q₁ : ℝ)) ∧
      (∀ j : Fin 1, b j ≤ bt j + bd) ∧
      ¬ (64 * (1 : ℝ) * (q₁ : ℝ) / ζ ≤ (q₂ : ℝ)) ∧
      ¬ (∑ j : Fin 1, b j < ζ * (q₂ : ℝ) / 4) := by
  refine ⟨fun _ => 7, fun _ => 7, 0, 1, 1, 1, by norm_num, le_refl 0,
    fun _ => by norm_num, fun _ => by norm_num, by norm_num, ?_⟩
  simp
  norm_num


/-! ## §8  Candidate B (rejected): ownership as constructor data

The rejected encoding of `08:586--594` takes the owner map, the branch counts
and the frozen readout as one bundle.  It is recorded here as race evidence with
its own battery, and it is consumed by nothing. -/

/-- **Candidate B (rejected).**  The owner map as data, with the frozen
conclusion `08:588--591` as a *field*.  Two things are wrong with it.  First,
the field `own_rich` puts the conclusion into constructor data, which the
mechanical contract forbids.  Second, `own` is unconstrained relative to `reps`:
nothing forces it to maximize, so the frozen sentence "choose an index
maximizing `ell_{i,j}`, breaking ties deterministically" is inexpressible. -/
structure OwnerAssignment (Item : Type*) (s t : ℕ) where
  /-- the alleged owner of each item -/
  own : Item → Fin s
  /-- the branch counts `ell_{i,j}` -/
  reps : Item → Fin s → ℕ
  /-- the frozen readout, illegally carried as data -/
  own_rich : ∀ i, t ≤ reps i (own i)

/-- **Candidate B, aux 1.**  The bundle is inhabited with its hardest field. -/
theorem ownerAssignment_nonempty : Nonempty (OwnerAssignment (Fin 3) 4 2) :=
  ⟨⟨fun _ => 0, fun _ _ => 2, fun _ => le_refl 2⟩⟩

/-- **Candidate B, aux 2.**  Every owned branch carries a positive count
whenever `t >= 1`. -/
theorem ownerAssignment_reps_pos {Item : Type*} {s t : ℕ} (ht : 1 ≤ t)
    (A : OwnerAssignment Item s t) (i : Item) : 0 < A.reps i (A.own i) :=
  lt_of_lt_of_le ht (A.own_rich i)

/-- **Candidate B, aux 3 (the decisive faithfulness failure).**  There is an
inhabitant whose `own` is *not* a maximizer of `reps`: the branch `1` carries
strictly more representatives than the declared owner `0`.  Under Candidate A
this is impossible by `le_ownBranch`. -/
theorem ownerAssignment_own_need_not_maximize :
    ∃ A : OwnerAssignment (Fin 1) 2 2, ∃ i : Fin 1,
      A.reps i (A.own i) < A.reps i 1 := by
  refine ⟨⟨fun _ => 0, fun _ j => if j = 0 then 2 else 5, fun _ => by norm_num⟩,
    0, ?_⟩
  norm_num

/-! **Disposition of Candidate B.**  `OwnerAssignment` is race evidence only.
It is consumed by no declaration in this module and by no downstream module, and
it may not be used to re-encode the ownership construction of `08:579--611`
without a fresh judged tranche.  The landed encoding is Candidate A: `ownBranch`
together with `tScale_le_own_representatives` and `own_partitions`. -/

end EthInapproximability.ParameterizedNP.DenseSourceOwners
