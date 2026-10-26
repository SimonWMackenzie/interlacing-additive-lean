import EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-!
# Parameterized NP route: the first block of the dense Stage-4 lemma battery

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 330--506** -- the
  proof-spine subsection, `sec:dense-synchronisation`, and the
  branch-to-block matching subsection.  The anchors traced here, in the order
  the block prints them:
  * lines 330--346 (`Proof spine and quantifier order`): "the first
    `log_2 s` actual bits are Bob bits; after transposition they are Alice
    bits", "These bits create `s` protocol-dependent transcript branches",
    "The construction itself contains `s` fixed Stage-3 blocks", and "A
    counting argument proves a bijection from transcript branches to their
    dominant fixed blocks";
  * lines 378--385: the fixed notation `j` for a dynamic transcript branch,
    `d(j)` for its dominant fixed Stage-3 block;
  * lines 390--399: "Transpose `N'`, and swap the names of the two players in
    `P`, obtaining a protocol `P_A` for a retained submatrix `A'` of `A`", and
    the first tolerance comparison
    `eta_C <= nu_T rho_temp/(2s) < nu_T rho_temp/s`, charged through
    `eq:source-protection-gate` (label line 564, display 556--565);
  * lines 400--409: the second tolerance comparison
    `eta_R < rho_loc mu_D zeta/(8s) <= mu_Sigma/3072 < mu_Sigma rho_Sigma`,
    under `mu_D = mu_Sigma`, `rho_loc = 1/4`, `zeta = gamma/24 <= 1/24` and
    `s >= 4`, charged through `eq:dense-defect-gates` (label line 684,
    display 679--685);
  * lines 410--418: "Consequently the protected template rows and selector
    columns of `A'` contain a member of `bracket(S_2; s, x_3, y_3)`", "The
    first inequality is charged separately against each of the `s` equal
    template reservoirs; the second is charged against the selector
    reservoir", and "This is why the two deletion parameters swap roles when
    `N'` is transposed";
  * lines 420--423: the induced protocol -- "At every node, suppress an actual
    query if it is fixed on the current restricted rectangle.  The remaining
    queries form the *induced protocol*.  A suppressed query still costs one
    bit in `P_A`; it is absent only from the induced transcript";
  * the **proof** of `lem:dense-synchronisation` (label line 426, statement
    425--432, proof 434--464).  What this module derives is the proof's own
    steps at lines 444--463: the budget contradiction 444--457 (`log_2 s + 1`
    spent bits against the alleged budget `log_2 s + D_2`) and the leaf count
    plus source-branch readout 459--463.  The four-clause statement 425--432 is
    **not** claimed: the separation-theorem output 438--439 and the frozen
    derived completeness 459--461 are carried in as the two conjuncts of the
    single `hsync` binder and are never handed back as conclusions.  The
    separation-theorem input list 435--443 is recorded here for provenance, not
    as something proved;
  * lines 466--470: "The transcript branches ... are determined by `P_A`.  They
    must not be identified with the `s` fixed Stage-3 blocks in the
    construction", the branch names `B_j`, and `d(j)` "the unique dominant
    fixed block supplied by the separation theorem";
  * lines 472--476: `T_p^{sel}`, "the `T_0^{aux}` template rows used by the
    separation theorem";
  * `lem:dense-dominant-bijection` (label line 479, statement 478--481) and its
    proof 483--502 -- the absent-label supposition, the branchwise bound
    `|B_j n T_p^{sel}| < T_3^{aux}`, the partition identity
    `T_0^{aux} = sum_j |B_j n T_p^{sel}| < s T_3^{aux}`, the contradiction with
    `eq:dense-separation-gates`, and "therefore bijective because both its
    domain and codomain have size `s`";
  * lines 504--506: "The distinction between `j` and `d(j)` will be maintained
    below.  Source ownership is defined using the dynamic branch `j`, whereas
    template damage is measured relative to the fixed block `d(j)`."
* **Predecessor anchor (the handoff consumed by pin):**
  `08-dense-stage4.tex` lines 1--328 through the banked
  `EthInapproximability.ParameterizedNP.DenseStageFourOpening`, whose §1
  supplies the complexity-transport device (`precompProto`,
  `cost_precompProto`, `eval_precompProto`), whose §2 supplies the protected
  masses (`muMass`, `nuTemp`, `nuSrc`), and whose §5 supplies
  `rhoTemp`, `rhoSigma`, `rhoLoc`, `denseSeparationGates` and
  `stageTwoAuxCertificate`.  **None of that handoff is restated here.**
* **Frozen constants consumed from elsewhere in the paper:**
  `zeta = gamma/24` with `0 < gamma <= 1` is `04-guarded-source.tex:503--509`
  (also `05-public-records.tex:117`), banked as
  `GuardedSourceSlab.zeta` and consumed by pin.
* **Reader counterparts** (frozen release,
  `reader-facing/sections/A-stage4-details.tex`, the proof outline of
  `thm:paper-protected-stage4`), one per declaration group, none of them shared
  with another module -- the opening module's claims stop at reader line 233,
  so lines 241--292 were unclaimed before this tranche:
  * lines 242--243, "The proof is the companion no-waste proof with every
    possible deletion charged to one of the fixed reservoirs" -- §1:
    `sourceProtectionGate`, `denseDefectGates`, `zetaBound`,
    `etaC_lt_template_allowance`, `etaR_lt_selector_allowance`,
    `protectedMasses_agree`;
  * lines 246--248, the sentence "Fix one retained matrix and one alleged
    protocol of cost at most `C-1`.  The protected template reservoir lets the
    Stage--3 separation theorem synchronise the first `log s` actual bits" --
    §2 and §3: the Alice-prefix device (`aliceStep`, `aliceBit`,
    `aliceResidual`, `aliceBranch`, `IsANode`, `IsAlicePrefixAt`,
    `IsAlicePrefix`) with its battery, `SynchronisedPrefix`,
    `no_fixed_query_in_prefix`, `denseSynchronisation` and its two readouts;
  * lines 248--250, the *separate* sentence "Dominant-block counting gives a
    bijection between the resulting transcript branches and the fixed Stage--3
    blocks" -- §4: `denseDominantBijection` and `dominantBlock_surjective`.
  The §5 non-vacuity group (both §5.1 and §5.2) and the §6 rejected-candidate
  group claim **no** reader item, deliberately rather than by omission: they add
  no reader content, and recording them against lines 242--250 would
  double-assign a reader item, which the crosswalk forbids.

## Dependencies, imports and external adapters

* Imports `EthInapproximability.ParameterizedNP.DenseStageFourOpening` only,
  hence transitively `RawStageFour`, `StageThreeExactScale`, `StageTwoRelaxed`,
  `StageOneInterlace`, `PublicRecords`, `GuardedSourceSlab`,
  `GuardedSourceGraph`, `FiniteSlots`, `PilotStage3` and the
  project-axiom-free `LegacyNPCC.Core` / `LegacyNPCC.Bridge` facades reached
  through `EthInapproximability.Prelude`.  `LegacyNPCC.Stage12` -- whose closure
  reaches the cited AGHP balanced-family axiom -- is **not** imported, and no
  declaration here is in its dependency graph.
* Banked project interfaces consumed **by pin, never restated**:
  * `DenseStageFourOpening.precompProto`, `cost_precompProto`,
    `eval_precompProto`, `muMass`, `nuTemp`, `nuSrc`, `rhoTemp`, `rhoSigma`,
    `rhoLoc`;
  * `GuardedSourceSlab.zeta`.
* Vendored interfaces consumed **by pin, never restated**:
  `Workspace.Types.Protocol.Protocol`, `Protocol.cost`, `Protocol.eval`,
  `Protocol.Computes`, `Workspace.Types.CommComplexity.AchievableCosts`,
  `NPCC.D`.
* **New vendored-gap work.**  The vendored layer has no notion of the *prefix*
  of a protocol: it exposes `cost` and `eval` on the whole tree only.  §2 adds
  the Alice-prefix walk (`aliceStep`, `aliceResidual`, `aliceBranch`) together
  with the two facts the frozen budget argument needs -- an all-Alice prefix of
  depth `k` costs `k` bits on top of its residual, and the residual depends
  only on the branch, so it computes the whole row class.
* Proof status: **new** for the Alice-prefix device, the two tolerance
  comparisons, the synchronisation assembly and the dominant-block bijection;
  **inherited by pin** for the protected masses, the schedule constants and the
  complexity-transport device.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only, and the purely
  combinatorial results of §2 need strictly less.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Candidate encodings of the synchronised prefix (`k = 2`, raced)

The novel object of this tranche is the *transcript branch*: the frozen text
says the first `log_2 s` actual queries of `P_A` are Alice queries and their
`s` leaves are the branches `B_j`.

**Candidate A (landed).**  Derive the branch from the protocol: walk the tree
taking the Alice edge selected by the row, and read the `k`-bit transcript
`aliceBranch k P x : Fin k -> Bool`.  Nothing is postulated -- the branch is a
*function of `P` and the row*, and "the first `k` queries are Alice queries" is
the predicate `IsAlicePrefix P k` about the same walk.  7 aux lemmas proved.

**Candidate B (rejected, §6).**  Take the branch map as data:
a bundle carrying `branch : Rw -> Fin k -> Bool` plus its surjectivity.  3 aux
lemmas proved, but it loses decisively on faithfulness: a consumer may
instantiate it with a map having **no relation to `P_A`**, so the frozen
sentence "these bits create `s` protocol-dependent transcript branches"
(`08:335--337`) is not expressible, and the budget argument of `08:444--457`
-- which is about the *cost* of the actual prefix -- cannot even be stated.
Candidate A is also shorter at the frozen arity.  The race is therefore decided
on faithfulness, not on length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the protected masses and the frozen `zeta` (2): `protectedMasses_agree`,
  `zetaBound`.
* `A2` the two tolerance comparisons (2): `etaC_lt_template_allowance`,
  `etaR_lt_selector_allowance`.
* `A3` the Alice-prefix walk, general properties (11):
  `aliceResidual_succ'`, `cost_aliceStep_succ_le`, `cost_aliceResidual_add_le`,
  `depth_le_cost_of_alicePrefix`, `eval_aliceResidual`,
  `aliceStep_eq_of_bit_eq`, `aliceResidual_eq_of_branch_eq`,
  `card_aliceBranch`, and -- added in `cc-t2i-r2` -- `cost_aliceStep_le`,
  `cost_aliceResidual_le` (monotonicity without a prefix hypothesis) and
  `aliceResidual_stationary` (the walk is the identity past a leaf or Bob
  node, which is what makes the depth-`d_2` Bob block of the synchronisation
  witness the residual at every later depth).
* `A4` the restriction bound (2): `D_branch_restriction_le`,
  `residual_cost_ge_of_restriction`.
* `A5` the frozen budget step (4): `no_fixed_query_in_prefix`,
  `denseSynchronisation`, `sync_branch_count`, `sync_no_source_only_branch`.
* `A6` the dominant-block bijection (2): `dominantBlock_surjective`,
  `denseDominantBijection`.
* `A7` the two gate bundles are inhabited on their frozen domains, general in
  `s`, `delta_v` and `zeta` (2): `sourceProtectionGate_nondegenerate`,
  `denseDefectGates_nondegenerate`; with the three shape arithmetic lemmas the
  latter runs on (3, added in `cc-t2i-r2`, all general and all proved without
  evaluating any tower): `self_lt_two_pow`, `sixteen_dvd_two_pow`,
  `two_exponent_le_two_pow`.
* Candidate B's own battery (3): `card_AbstractBranching`,
  `AbstractBranching_fiber_nonempty`, `abstractBranching_of_protocol`.

That is **28 battery entries proved plus 3 for the rejected candidate** -- 24
carrying an `Aux` label, the two headline results `denseSynchronisation` and
`denseDominantBijection`, and the two general gate-inhabitation lemmas -- with
`0` unproved, alongside **five statement poles**
(`denseSynchronisation_not_automatic`, `dominantBijection_gate_is_load_bearing`,
`aliceBranch_is_not_the_row`, `sourceProtectionGate_pole_at_s_three` and
`hres_is_a_real_constraint`) and **four non-vacuity / consistency readouts**,
three of them at legal parameter values and one -- deliberately and by name --
only shape-conforming:

* `denseSynchronisation_hypotheses_consistent` at `s = 4`, `ws = 2`, and the
  **frozen Stage-3 depth floor** `d_2 = 3` (`07:442`, `07:472`, `07:501`:
  `2 <= D_2` and `D_2 >= B_cap >= 3`), budget `ws + d_2 = 5 = cost(P)`, which
  is the frozen `log_2 s + D_2` of `08:325` at `s = 4`;
* `dominantBijection_legal_instance` at `s = 4`, `T_0^{aux} = 5`,
  `T_3^{aux} = 1`, where the bijection landed is the nontrivial four-cycle, not
  the identity;
* `sourceProtectionGate_legal_instance` at `s = 4`, `delta_v = 1/6`,
  `eta_C = 2^{-34} > 0`;
* `denseDefectGates_shape_instance` at `s = 4`, the pinned `zeta 1 = 1/24`,
  `q_1 = 2 = 2^2 - 2`, `t_2 = 32 = 2^5` (divisible by `16`),
  `q_2 = 16384 = 2^{14}`, `eta_R = 2^{-20} > 0`.  This one is **not** called
  legal, and it is not a schedule instance: `06:766` floors `k_2` at `2^{19}`,
  so no evaluable literal `t_2` is a schedule value.  What it does establish is
  that the frozen inequality system is satisfiable at the frozen *shapes*
  (`06:314--315`, `06:321--322`, `06:770`, `06:824`, `06:124`) and *local*
  comparisons (`06:180`, `06:835`).  Both magnitude floors are carried instead
  by the symbolic `denseDefectGates_nondegenerate`, which puts `2^{19} <= k_2`
  inside the existential and takes the Stage-1 exponent floor `a >= 2432`
  (`06:298--315`) as a hypothesis with `q_1 = 2^a - 2`.  This two-tier standard
  is stated in full at §5.1.

## Honest scope and recorded coverage limits

1. **The induced/actual distinction is modelled only through the budget.**
   The frozen `08:420--423` defines the induced protocol by suppressing queries
   *fixed on the current restricted rectangle*; "fixed on a rectangle" needs the
   restriction machinery of the later subsections and has no Lean declaration
   yet.  What is transcribed here is the frozen *consequence* proved at
   `08:444--457`: under the alleged budget, the all-Alice prefix cannot be one
   step deeper than `log_2 s`.  A later tranche that needs the suppression
   bookkeeping itself may not cite the present form as having supplied it.
2. **The separation theorem is an explicit named hypothesis, and only its own
   output is attributed to it.**  `08:435--443` invokes "the inherited
   classical near-exact separation theorem".  The one output of it used in this
   module is `08:438--439`, "It forces the first `log_2 s` nonfixed queries to
   be Alice queries", which is the *first* conjunct of the `hsync` binder of
   `denseSynchronisation`; its dominance output is the binder `hdom` of
   `denseDominantBijection`.  The *second* conjunct of `hsync`, completeness of
   the prefix, is **not** a separation-theorem output: it is the frozen derived
   sentence `08:459--461`, whose own premise (a query being nonfixed on the
   current template rectangle) needs the restriction machinery of the later
   subsections and has no Lean declaration here.  It is therefore carried in as
   a hypothesis anchored at `08:459--461` and, unlike in the parked shape of
   this module, is **not re-exported as a conclusion**.  Neither binder is ever
   a silent axiom.
2b. **The residual estimate is guarded by the frozen supposition.**  `hres` is
   `08:448--454` "at the resulting node", and the node exists only under the
   supposition of `08:444--446`.  Since `aliceStep` is the identity at a leaf
   and at a Bob node, `aliceResidual x (ws + 1) P` is still a well-typed term
   when the walk has stopped, so the binder is conditionalised on
   `IsAlicePrefixAt P (ws + 1) x` at **both** call sites,
   `no_fixed_query_in_prefix` and `denseSynchronisation`.  The guard does not
   trivialise the binder: `hres_is_a_real_constraint` exhibits a protocol whose
   guard holds at every row and whose estimate fails.
3. **The bracket containment of `08:410--414` is not proved.**  What is proved
   is the pair of tolerance comparisons `08:394--409` that the frozen text
   charges against the template and selector reservoirs.  Turning those into
   "the protected template rows and selector columns of `A'` contain a member
   of `bracket(S_2; s, x_3, y_3)`" needs the reservoir-restriction machinery and
   is carried downstream as a hypothesis, never asserted here.
4. **`Admissible`, `NoCert` and `LevelStep` still have no Lean declaration**
   and do not appear here at all: every statement of this module is a closed
   conditional in its own explicit binders.
5. **The gate predicates are transcribed, never asserted -- but they are
   inhabited, under a two-tier standard.**  `sourceProtectionGate` and
   `denseDefectGates` are `Prop`-valued transcriptions of
   `eq:source-protection-gate` and `eq:dense-defect-gates`; the module only ever
   consumes them as hypotheses.  Because an unsatisfiable premise bundle would
   make every consumer vacuous while compiling green, §5.1 proves both
   inhabited on their frozen domains (`s >= 4`, `delta_v > 0`,
   `0 < zeta <= 1/24`) with **strictly positive** tolerances `eta_C`, `eta_R`.
   `sourceProtectionGate`'s parameters are Section-8 quantities, so its witness
   is legal outright at `s = 4`, `delta_v = 1/6`.  `denseDefectGates`'s
   parameters `t_2`, `q_1`, `q_2` are **schedule** quantities pinned by
   `06:766` and `06:308--315` above every evaluable literal, so its non-vacuity
   is split: `denseDefectGates_nondegenerate` carries the frozen shapes *and*
   both magnitude floors symbolically -- `2^{19} <= k_2` and the Stage-1
   exponent floor `a >= 2432`, from which `2 <= q_1` (`06:197`, strictly
   stronger than the `0 < q_1` the parked shape advertised) is *derived* rather
   than assumed -- while `denseDefectGates_shape_instance` is a concrete
   shape-conforming, locally legal satisfiability witness that is **not**
   claimed to be a schedule instance.  `sourceProtectionGate_pole_at_s_three`
   records why the domain starts at `s = 4`: the frozen third clause
   `nu_B/(16(s-3))` has a division pole at `s = 3`, where the gate forces
   `eta_C <= 0`.
6. **`denseDominantBijection` is proved for the frozen counting only.**  The
   frozen proof needs exactly: the branches partition the selected template
   rows, every nondominant block contributes fewer than `T_3^{aux}` of them,
   `|T_p^{sel}| = T_0^{aux}`, and `s T_3^{aux} < T_0^{aux}`.  The `x_dom` row
   density of the dominant block (`08:441--442`) is **not** used and is
   therefore **not** a hypothesis: adding it would be an over-strong premise
   that typechecks and hides which gate is load-bearing.
7. **No parameter schedule may be read out of any witness below.**  The
   witnesses of §5 are minimal instances chosen so that every frozen side
   condition (`s >= 4` a power of two, `s T_3^{aux} < T_0^{aux}`, a budget
   `log_2 s + D_2` at the frozen depth floor `D_2 >= B_cap >= 3` of `07:501`,
   `0 < zeta <= 1/24`, `delta_v > 0`) holds and nothing else.  They are probes,
   not choices.  Three of them are legal outright; the fourth,
   `denseDefectGates_shape_instance`, is shape-conforming and locally legal
   only, and says so in its own name and docstring, because the frozen schedule
   pins `t_2` and `q_1` above every evaluable literal (`06:766`,
   `06:308--315`).
8. **Candidate B is race evidence with a recorded disposition.**  See the
   disposition note at the end of §6: `AbstractBranching` is consumed by
   nothing and may not be used to re-encode the branch families of
   `08:613--1346` without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseSynchronisation

open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-! ## §1  The two tolerance comparisons (`08:390--418`)

`08:390--393` transposes `N'` and swaps the players, so that the row-deletion
tolerance `eta_R` of `N` acts on **columns** of `A'` and `eta_C` acts on its
**rows** -- the fixed orientation convention of `08:154--156`, banked in the
opening module.  The frozen text then charges each tolerance against a
protected reservoir.  Both comparisons are pure arithmetic in the frozen
constants and are proved here. -/

/-- `nu_T = 2^{-21}` (`08:136`) as a real, for comparison with the real
tolerances.  The rational value is the banked `nuTemp`; nothing is recomputed. -/
noncomputable def nuTempR : ℝ := ((nuTemp : ℚ) : ℝ)

/-- `nu_V = nu_B = 2^{-22}` (`08:137`) as a real. -/
noncomputable def nuSrcR : ℝ := ((nuSrc : ℚ) : ℝ)

/-- `mu_Sigma = mu_D = 1/184` (`08:134`) as a real.  The frozen step at
`08:400--401` uses precisely the identity `mu_D = mu_Sigma`, which is why one
symbol carries both. -/
noncomputable def muR : ℝ := ((muMass : ℚ) : ℝ)

/-- **Aux 1 (the three protected masses, read in `ℝ`).**  The real readouts of
the banked rational masses are the frozen values, so no comparison below
silently changes the constant it is charged against.  General. -/
theorem protectedMasses_agree :
    nuTempR = 1 / 2 ^ 21 ∧ nuSrcR = 1 / 2 ^ 22 ∧ muR = 1 / 184 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [nuTempR, nuSrcR, muR, nuTemp, nuSrc, muMass]

/-- **Aux 2 (`zeta = gamma/24 <= 1/24`, `08:402`).**  The frozen bound on the
witness-supply constant is not an assumption of this block: it follows from the
guarded source's own range `0 < gamma <= 1` (`04:503--509`) applied to the
banked `zeta`.  General in `gamma`. -/
theorem zetaBound {γ : ℚ} (h0 : 0 < γ) (h1 : γ ≤ 1) :
    0 < ((zeta γ : ℚ) : ℝ) ∧ ((zeta γ : ℚ) : ℝ) ≤ 1 / 24 := by
  have h0' : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast h0
  have h1' : (γ : ℝ) ≤ 1 := by exact_mod_cast h1
  constructor
  · simp only [zeta, Rat.cast_div]
    push_cast
    linarith
  · simp only [zeta, Rat.cast_div]
    push_cast
    linarith

/-- **`eq:source-protection-gate` (`08:556--565`)**, the row-deletion parameter
choice
`eta_C <= (1/2) min { nu_T rho_temp/s, nu_V delta_v(G)/16, nu_B/(16(s-3)) }`.
Transcribed as a predicate and never asserted; `nu_V = nu_B = nuSrcR` is the
frozen identity of `08:137`. -/
def sourceProtectionGate (ηC δv : ℝ) (s : ℕ) : Prop :=
  ηC ≤ (1 / 2) *
    min (nuTempR * rhoTemp / (s : ℝ))
      (min (nuSrcR * δv / 16) (nuSrcR / (16 * ((s : ℝ) - 3))))

/-- **`eq:dense-defect-gates` (`08:679--685`)**, `t_2 >= 8 q_1`,
`q_2 >= 64 s q_1/zeta`, `eta_R < rho_loc mu_D zeta/(8s)`.  The display belongs
to the deeper battery (`lem:aggregate-defect`); it is transcribed here because
`08:403` charges the third clause inside the synchronisation preamble.
Transcribed as a predicate and never asserted. -/
def denseDefectGates (t₂ q₁ q₂ s : ℕ) (ζ ηR : ℝ) : Prop :=
  8 * q₁ ≤ t₂ ∧
    64 * (s : ℝ) * (q₁ : ℝ) / ζ ≤ (q₂ : ℝ) ∧
    ηR < rhoLoc * muR * ζ / (8 * (s : ℝ))

/-- **Aux 3 (`08:394--399`: the template-reservoir comparison).**  From
`eq:source-protection-gate`, `eta_C <= nu_T rho_temp/(2s)`, and this is
*strictly* below the per-reservoir allowance `nu_T rho_temp/s` that the frozen
text charges "separately against each of the `s` equal template reservoirs".
The strictness is the content: it is what leaves room for the spare factor of
`08:576--577`.  General in `eta_C`, `delta_v` and `s`. -/
theorem etaC_lt_template_allowance {ηC δv : ℝ} {s : ℕ} (hs : 0 < s)
    (h : sourceProtectionGate ηC δv s) :
    ηC ≤ nuTempR * rhoTemp / (2 * (s : ℝ)) ∧ ηC < nuTempR * rhoTemp / (s : ℝ) := by
  have hnu : nuTempR = 1 / 2 ^ 21 := protectedMasses_agree.1
  have hpos : (0 : ℝ) < nuTempR * rhoTemp := by
    rw [hnu, rhoTemp]; norm_num
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hmin : min (nuTempR * rhoTemp / (s : ℝ))
      (min (nuSrcR * δv / 16) (nuSrcR / (16 * ((s : ℝ) - 3))))
      ≤ nuTempR * rhoTemp / (s : ℝ) := min_le_left _ _
  have hhalf : ηC ≤ (1 / 2) * (nuTempR * rhoTemp / (s : ℝ)) := by
    have := h
    simp only [sourceProtectionGate] at this
    linarith
  have hrw : (1 / 2) * (nuTempR * rhoTemp / (s : ℝ))
      = nuTempR * rhoTemp / (2 * (s : ℝ)) := by
    field_simp
  have hhalf' : ηC ≤ nuTempR * rhoTemp / (2 * (s : ℝ)) := by rw [← hrw]; exact hhalf
  refine ⟨hhalf', ?_⟩
  have hpos2 : 0 < nuTempR * rhoTemp / (2 * (s : ℝ)) := div_pos hpos (by linarith)
  have hgap : nuTempR * rhoTemp / (s : ℝ) - nuTempR * rhoTemp / (2 * (s : ℝ))
      = nuTempR * rhoTemp / (2 * (s : ℝ)) := by
    field_simp
    ring
  linarith

/-- **Aux 4 (`08:400--409`: the selector-reservoir comparison).**  From
`eq:dense-defect-gates`, and using `mu_D = mu_Sigma`, `rho_loc = 1/4`,
`zeta <= 1/24` and the frozen `s >= 4`,
`eta_R < rho_loc mu_D zeta/(8s) <= mu_Sigma/3072 < mu_Sigma rho_Sigma`,
so the whole diagonal-defect allowance sits strictly inside the selector
reservoir's own allowance.  The chain is tight: at `s = 4` and `zeta = 1/24`
the middle inequality is an equality, so neither the `s >= 4` nor the
`zeta <= 1/24` hypothesis can be dropped.  General. -/
theorem etaR_lt_selector_allowance {t₂ q₁ q₂ s : ℕ} {ζ ηR : ℝ}
    (hs : 4 ≤ s) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 24)
    (h : denseDefectGates t₂ q₁ q₂ s ζ ηR) :
    ηR < muR / 3072 ∧ ηR < muR * rhoSigma := by
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  have hs' : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have h8s : (0 : ℝ) < 8 * (s : ℝ) := by linarith
  have hkey : rhoLoc * muR * ζ / (8 * (s : ℝ)) ≤ muR / 3072 := by
    rw [div_le_iff₀ h8s, hmu, rhoLoc]
    linarith
  have hstep : ηR < muR / 3072 := lt_of_lt_of_le h.2.2 hkey
  refine ⟨hstep, ?_⟩
  have : muR / 3072 < muR * rhoSigma := by
    rw [hmu, rhoSigma]; norm_num
  linarith

/-! ## §2  The Alice prefix of a protocol (Candidate A)

`08:334--337`: "On the original `N` orientation, the first `log_2 s` actual bits
are Bob bits; after transposition they are Alice bits.  These bits create `s`
protocol-dependent transcript branches."  The vendored `Protocol` type exposes
`cost` and `eval` on the whole tree only, so the prefix walk is new work.

The walk below is a *function of the protocol and the row*.  That is the whole
reason Candidate A wins the race: the frozen branches are protocol-dependent,
and here they cannot be anything else. -/

variable {X Y Z : Type*}

/-- The node reached is an Alice node.  Stated existentially so that a case
split on it produces the three fields of `Protocol.aNode` directly. -/
def IsANode (P : Protocol X Y Z) : Prop :=
  ∃ (a : X → Bool) (l r : Protocol X Y Z), P = Protocol.aNode a l r

/-- One step of the Alice walk: at an Alice node, descend along the edge that
Alice's own input selects; at any other node the walk stops, so the step is the
identity.  The stopping convention is what makes `IsAlicePrefix` a genuine
constraint rather than a naming device. -/
def aliceStep (x : X) : Protocol X Y Z → Protocol X Y Z
  | Protocol.aNode a l r => if a x then r else l
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.bNode b l r => Protocol.bNode b l r

/-- The bit Alice sends at the current node, `false` at a stopped walk. -/
def aliceBit (x : X) : Protocol X Y Z → Bool
  | Protocol.aNode a _ _ => a x
  | Protocol.leaf _ => false
  | Protocol.bNode _ _ _ => false

/-- The residual protocol after `k` steps of the Alice walk. -/
def aliceResidual (x : X) : ℕ → Protocol X Y Z → Protocol X Y Z
  | 0, P => P
  | (k + 1), P => aliceResidual x k (aliceStep x P)

/-- **The transcript branch of a row** (`08:336--337`, `08:468`): the `k`-bit
string Alice sends along the prefix.  The frozen `B_j` is the fibre of this
map. -/
def aliceBranch (k : ℕ) (P : Protocol X Y Z) (x : X) : Fin k → Bool :=
  fun i => aliceBit x (aliceResidual x i.1 P)

/-- "The first `k` queries are Alice queries", at one row. -/
def IsAlicePrefixAt (P : Protocol X Y Z) (k : ℕ) (x : X) : Prop :=
  ∀ i : ℕ, i < k → IsANode (aliceResidual x i P)

/-- "The first `k` queries are Alice queries" (`08:427--428`). -/
def IsAlicePrefix (P : Protocol X Y Z) (k : ℕ) : Prop :=
  ∀ x : X, IsAlicePrefixAt P k x

/-- **Aux 5 (the walk commutes with its last step).**  General. -/
theorem aliceResidual_succ' (x : X) (k : ℕ) (P : Protocol X Y Z) :
    aliceResidual x (k + 1) P = aliceStep x (aliceResidual x k P) := by
  induction k generalizing P with
  | zero => rfl
  | succ n ih => simpa [aliceResidual] using ih (aliceStep x P)

/-- **Aux 6 (an Alice step costs one bit).**  General. -/
theorem cost_aliceStep_succ_le (x : X) (P : Protocol X Y Z) (h : IsANode P) :
    (aliceStep x P).cost + 1 ≤ P.cost := by
  obtain ⟨a, l, r, rfl⟩ := h
  have hl : l.cost ≤ max l.cost r.cost := le_max_left _ _
  have hr : r.cost ≤ max l.cost r.cost := le_max_right _ _
  by_cases ha : a x = true
  · have h1 : aliceStep x (Protocol.aNode a l r) = r := by simp [aliceStep, ha]
    rw [h1]
    simp only [Protocol.cost]
    omega
  · have h1 : aliceStep x (Protocol.aNode a l r) = l := by simp [aliceStep, ha]
    rw [h1]
    simp only [Protocol.cost]
    omega

/-- **Aux 7 (`08:446--447`: an all-Alice prefix of depth `k` really spends `k`
bits).**  "Immediately after that induced query, the actual transcript would
have spent at least `log_2 s + 1` bits."  The residual protocol keeps whatever
depth it has *on top of* those `k` bits.  General. -/
theorem cost_aliceResidual_add_le {P : Protocol X Y Z} {k : ℕ} {x : X}
    (h : IsAlicePrefixAt P k x) : (aliceResidual x k P).cost + k ≤ P.cost := by
  induction k generalizing P with
  | zero => simp [aliceResidual]
  | succ n ih =>
      have h0 : IsANode P := by simpa [aliceResidual] using h 0 (Nat.succ_pos n)
      have hstep : IsAlicePrefixAt (aliceStep x P) n x := by
        intro i hi
        have := h (i + 1) (by omega)
        simpa [aliceResidual] using this
      have hrec := ih hstep
      have hcost := cost_aliceStep_succ_le x P h0
      change (aliceResidual x n (aliceStep x P)).cost + (n + 1) ≤ P.cost
      omega

/-- **Aux 8 (the prefix depth is a lower bound on the cost).**  General. -/
theorem depth_le_cost_of_alicePrefix {P : Protocol X Y Z} {k : ℕ} {x : X}
    (h : IsAlicePrefixAt P k x) : k ≤ P.cost := by
  have := cost_aliceResidual_add_le h
  omega

/-- **Aux 9 (the residual computes the same value for its own row).**  General. -/
theorem eval_aliceResidual {P : Protocol X Y Z} {k : ℕ} {x : X}
    (h : IsAlicePrefixAt P k x) (y : Y) :
    (aliceResidual x k P).eval x y = P.eval x y := by
  induction k generalizing P with
  | zero => rfl
  | succ n ih =>
      have h0 : IsANode P := by simpa [aliceResidual] using h 0 (Nat.succ_pos n)
      have hstep : IsAlicePrefixAt (aliceStep x P) n x := by
        intro i hi
        have := h (i + 1) (by omega)
        simpa [aliceResidual] using this
      have hrec := ih hstep
      obtain ⟨a, l, r, rfl⟩ := h0
      have hres : aliceResidual x (n + 1) (Protocol.aNode a l r)
          = aliceResidual x n (aliceStep x (Protocol.aNode a l r)) := rfl
      rw [hres, hrec]
      by_cases ha : a x <;> simp [aliceStep, Protocol.eval, ha]

/-- **Aux 9b (one step of the walk depends on the row only through the bit it
sends).**  General. -/
theorem aliceStep_eq_of_bit_eq {x x' : X} (P : Protocol X Y Z)
    (h : aliceBit x P = aliceBit x' P) : aliceStep x P = aliceStep x' P := by
  cases P with
  | leaf z => rfl
  | bNode b l r => rfl
  | aNode a l r =>
      simp only [aliceBit] at h
      simp only [aliceStep, h]

/-- **Aux 10 (`08:466--468`: the branch determines the residual).**  Two rows
that send the same `k` bits reach the same node, so the frozen `B_j` really is a
*node* of the protocol and not merely a set of rows.  This is what lets the
budget argument speak about "the resulting node".  General. -/
theorem aliceResidual_eq_of_branch_eq (k : ℕ) (P : Protocol X Y Z) (x x' : X)
    (h : aliceBranch k P x = aliceBranch k P x') :
    aliceResidual x k P = aliceResidual x' k P := by
  have hbit : ∀ i : ℕ, i < k →
      aliceBit x (aliceResidual x i P) = aliceBit x' (aliceResidual x' i P) := by
    intro i hi
    exact congrFun h ⟨i, hi⟩
  clear h
  induction k with
  | zero => rfl
  | succ n ih =>
      have hstep := ih (fun i hi => hbit i (by omega))
      have hb := hbit n (by omega)
      rw [aliceResidual_succ', aliceResidual_succ', hstep]
      exact aliceStep_eq_of_bit_eq _ (by rw [← hstep] at hb ⊢; exact hb)

/-- **Aux 11 (`08:460--461`: the prefix has exactly `2^k` leaves).**  General. -/
theorem card_aliceBranch (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by
  simp

/-- **Aux 11a (a step never costs more than the node it left).**  General.
Added in `cc-t2i-r2`; nothing above it is changed. -/
theorem cost_aliceStep_le (x : X) (P : Protocol X Y Z) :
    (aliceStep x P).cost ≤ P.cost := by
  cases P with
  | leaf z => exact le_refl _
  | bNode b l r => exact le_refl _
  | aNode a l r =>
      have hl : l.cost ≤ max l.cost r.cost := le_max_left _ _
      have hr : r.cost ≤ max l.cost r.cost := le_max_right _ _
      by_cases ha : a x = true
      · have h1 : aliceStep x (Protocol.aNode a l r) = r := by simp [aliceStep, ha]
        rw [h1]; simp only [Protocol.cost]; omega
      · have h1 : aliceStep x (Protocol.aNode a l r) = l := by simp [aliceStep, ha]
        rw [h1]; simp only [Protocol.cost]; omega

/-- **Aux 11b (monotonicity of the walk: the residual never costs more than the
protocol).**  General; unlike `cost_aliceResidual_add_le` this needs no prefix
hypothesis, because the stopping convention makes the step non-increasing at
every node.  Added in `cc-t2i-r2`. -/
theorem cost_aliceResidual_le (x : X) (k : ℕ) (P : Protocol X Y Z) :
    (aliceResidual x k P).cost ≤ P.cost := by
  induction k generalizing P with
  | zero => exact le_refl _
  | succ n ih =>
      have h := ih (aliceStep x P)
      have h2 := cost_aliceStep_le x P
      change (aliceResidual x n (aliceStep x P)).cost ≤ P.cost
      omega

/-- **Aux 11c (the walk is stationary once it has stopped).**  At a leaf and at
a Bob node the walk is the identity, so the residual at *every* later depth is
the node itself.  This is the general fact behind the guard on `hres`
(`08:447--449` produces a node only under its own supposition) and behind the
depth-`d_2` Bob block of the synchronisation witness: its cost is the residual
cost at every depth past the Alice prefix.  General; added in `cc-t2i-r2`. -/
theorem aliceResidual_stationary {P : Protocol X Y Z} (x : X) (k : ℕ)
    (h : ¬ IsANode P) : aliceResidual x k P = P := by
  have hstep : aliceStep x P = P := by
    cases P with
    | leaf z => rfl
    | bNode b l r => rfl
    | aNode a l r => exact absurd ⟨a, l, r, rfl⟩ h
  induction k with
  | zero => rfl
  | succ n ih => rw [aliceResidual_succ', ih, hstep]

/-- **Aux 12 (`08:448--451`: what survives at the resulting node).**  If every
row of a finite row set `S` follows the same branch, then the residual protocol
at that node computes the whole restriction of the game to `S`, so the
restriction's deterministic complexity is at most the residual cost.

This is the step that makes the frozen sentence "The dominant block at the
resulting node, together with the unchanged selector columns, contains an
`x_dom`-by-`y_3` restriction of `S_2`" usable: the restriction is a *game the
residual protocol solves*, not a separate object.  The transport device is the
banked `precompProto`; nothing of it is restated.  General. -/
theorem D_branch_restriction_le {Rw Cl : Type*} [Fintype Cl]
    (f : Rw → Cl → Bool) (P : Protocol Rw Cl Bool) (hP : Protocol.Computes P f)
    (k : ℕ) (S : Finset Rw) (x₀ : Rw)
    (hpre : ∀ x ∈ S, IsAlicePrefixAt P k x)
    (hS : ∀ x ∈ S, aliceBranch k P x = aliceBranch k P x₀) :
    D (fun (r : {x : Rw // x ∈ S}) (c : Cl) => f r.val c)
      ≤ (aliceResidual x₀ k P).cost := by
  refine Nat.sInf_le ⟨precompProto (fun r : {x : Rw // x ∈ S} => r.val)
    (fun c : Cl => c) (aliceResidual x₀ k P), cost_precompProto _ _ _, ?_⟩
  intro r c
  rw [eval_precompProto]
  have hres : aliceResidual r.val k P = aliceResidual x₀ k P :=
    aliceResidual_eq_of_branch_eq k P r.val x₀ (hS r.val r.2)
  rw [← hres, eval_aliceResidual (hpre r.val r.2)]
  exact hP r.val c

/-- **Aux 13 (`08:452--454`: the residual cost inherits the frozen lower
bound).**  "By `eq:dense-separation-gates`, monotonicity, and the auxiliary
robustness of `S_2`, this restriction has complexity at least `comp(S_2) =
D_2`."  Composing that with Aux 12 gives the residual-cost bound the budget
argument consumes -- so the `hres` binder of `denseSynchronisation` is a
*derived* shape, not an invented one.  General. -/
theorem residual_cost_ge_of_restriction {Rw Cl : Type*} [Fintype Cl]
    (f : Rw → Cl → Bool) (P : Protocol Rw Cl Bool) (hP : Protocol.Computes P f)
    (k d₂ : ℕ) (S : Finset Rw) (x₀ : Rw)
    (hpre : ∀ x ∈ S, IsAlicePrefixAt P k x)
    (hS : ∀ x ∈ S, aliceBranch k P x = aliceBranch k P x₀)
    (hlb : d₂ ≤ D (fun (r : {x : Rw // x ∈ S}) (c : Cl) => f r.val c)) :
    d₂ ≤ (aliceResidual x₀ k P).cost :=
  le_trans hlb (D_branch_restriction_le f P hP k S x₀ hpre hS)

/-! ## §3  `lem:dense-synchronisation` (`08:425--464`) -/

/-- **The frozen conclusion of `lem:dense-synchronisation`, clauses 2--4**
(`08:427--431`): the first `k` actual queries of the protocol are Alice
queries, and the prefix is complete -- every one of the `2^k` transcript
branches still contains a selected template row.

Clause "every retained source row belongs to one of these branches" is
deliberately **not** a field: it is a consequence of the first conjunct (the
walk is total), and is proved as `sync_no_source_only_branch` in its sharp
frozen form ("no separate source-only branch is created during the prefix").
Restating a derived telescope as a field is exactly what the mechanical
contract forbids. -/
def SynchronisedPrefix {Rw Cl : Type*} (P : Protocol Rw Cl Bool) (k : ℕ)
    (Tmpl : Finset Rw) : Prop :=
  IsAlicePrefix P k ∧ ∀ β : Fin k → Bool, ∃ x ∈ Tmpl, aliceBranch k P x = β

/-- **Aux 14 (`08:444--457`: no fixed actual query occurs during the induced
prefix).**  "Suppose an actual query fixed on the current template restriction
occurred before the `log_2 s`-th induced query.  Immediately after that induced
query, the actual transcript would have spent at least `log_2 s + 1` bits.  The
dominant block at the resulting node ... has complexity at least `comp(S_2) =
D_2`.  But the alleged total budget is `log_2 s + D_2`, so at most `D_2 - 1`
bits remain.  This is impossible."

Stated at one row, which is all the frozen contradiction uses.

The residual estimate is **conditional on the node existing**.  `08:447--449`
speaks of "the resulting node", i.e. the node reached *after* the supposed
extra query; `aliceStep` is the identity at a leaf and at a Bob node, so
`aliceResidual x (ws + 1) P` is a well-typed term even when the walk has
already stopped, and an unconditional `d₂ ≤ ...` would assert the frozen
estimate at a node the frozen text never produces.  The binder is therefore
guarded by `IsAlicePrefixAt P (ws + 1) x`, which is exactly the frozen
supposition.  General. -/
theorem no_fixed_query_in_prefix {Rw Cl : Type*} (P : Protocol Rw Cl Bool)
    (ws d₂ : ℕ) (x : Rw) (hbudget : P.cost ≤ ws + d₂)
    (hres : IsAlicePrefixAt P (ws + 1) x →
      d₂ ≤ (aliceResidual x (ws + 1) P).cost) :
    ¬ IsAlicePrefixAt P (ws + 1) x := by
  intro h
  have hcost := cost_aliceResidual_add_le h
  have hd := hres h
  omega

/-- **The frozen budget step of `lem:dense-synchronisation` (`08:444--463`).**

*What this result is, stated exactly.*  It is **not** the four-clause lemma of
`08:425--432`.  Two of those four clauses are supplied to it, in the single
binder `hsync`, and neither is re-exported as a conclusion.  What is derived
here is precisely the part of the frozen proof that this tranche can carry:

* the budget contradiction of `08:444--457` -- "Suppose an actual query fixed
  on the current template restriction occurred before the `log_2 s`-th induced
  query. ... at most `D_2 - 1` bits remain.  This is impossible.  Hence no
  fixed actual query occurs during the induced prefix" -- landed as
  `¬ IsAlicePrefix P (ws + 1)`;
* the leaf count of `08:460--461`, "The prefix therefore has exactly
  `2^{log_2 s} = s` nonempty leaves", landed as
  `Fintype.card (Fin ws → Bool) = s`, together with `2 ≤ ws`, the discriminator
  against the trivial reading (at `ws = 0` there is one branch and the
  completeness clause would hold of any single row, which is why the frozen
  schedule keeps `s >= 4`);
* the source-branch readout of `08:461--463`, "Each retained source row follows
  one of the same actual transcripts, and that transcript also contains
  template rows; no separate source-only branch is created during the prefix".

*What `hsync` is, and which anchor each conjunct comes from.*  `hsync` is the
prefix data this tranche does not prove.

* Its first conjunct `IsAlicePrefix P ws` is the separation-theorem output of
  `08:438--439`, "It forces the first `log_2 s` nonfixed queries to be Alice
  queries".
* Its second conjunct, completeness, is **not** a separation-theorem output.
  It is the frozen *derived* sentence `08:459--461`, "Every query in the prefix
  is nonfixed on the current template rectangle, so both children contain
  template rows".  Its own premise -- a query being nonfixed on the current
  template rectangle -- needs the restriction machinery of the later
  subsections, which has no Lean declaration in this tranche, so the frozen
  conclusion enters here as a hypothesis attributed to `08:459--461`.  It is
  carried in and **never** handed back as a conclusion; a later tranche that
  discharges the restriction bookkeeping may not cite this result as having
  supplied it.

The binder `hres` is the frozen `08:448--454` estimate at "the resulting
node", guarded by the frozen supposition that the node exists; its derived
shape is `residual_cost_ge_of_restriction`.  Neither binder is a silent axiom,
and `EXPANDER-001` has no Lean declaration by design and none is introduced.

The frozen side conditions `s = 2^{log_2 s}` and `s >= 4` are carried
explicitly. -/
theorem denseSynchronisation {Rw Cl : Type*} (P : Protocol Rw Cl Bool)
    (ws d₂ s : ℕ) (Tmpl : Finset Rw)
    (hs : s = 2 ^ ws) (hs4 : 4 ≤ s)
    (hbudget : P.cost ≤ ws + d₂)
    (hsync : SynchronisedPrefix P ws Tmpl)
    (hres : ∀ x : Rw, IsAlicePrefixAt P (ws + 1) x →
      d₂ ≤ (aliceResidual x (ws + 1) P).cost) :
    ¬ IsAlicePrefix P (ws + 1)
      ∧ (Fintype.card (Fin ws → Bool) = s ∧ 2 ≤ ws)
      ∧ ∀ x : Rw, ∃ y ∈ Tmpl, aliceBranch ws P y = aliceBranch ws P x := by
  obtain ⟨x₀, -, -⟩ := hsync.2 (fun _ => false)
  have hws : 2 ≤ ws := by
    by_contra hc
    have hlt : ws < 2 := Nat.lt_of_not_le hc
    interval_cases ws <;> · norm_num at hs; omega
  refine ⟨?_, ⟨?_, hws⟩, ?_⟩
  · intro hbad
    exact no_fixed_query_in_prefix P ws d₂ x₀ hbudget (hres x₀) (hbad x₀)
  · rw [card_aliceBranch, hs]
  · exact fun x => hsync.2 (aliceBranch ws P x)

/-- **Aux 15 (`08:460--461`: exactly `s` nonempty transcript branches).**  The
prefix is complete, so the branch map hits every one of the `2^{log_2 s} = s`
bit strings, and `s >= 4` of them are genuinely present.  General. -/
theorem sync_branch_count {Rw Cl : Type*} (P : Protocol Rw Cl Bool) (ws s : ℕ)
    (Tmpl : Finset Rw) (hs : s = 2 ^ ws) (hs4 : 4 ≤ s)
    (hsync : SynchronisedPrefix P ws Tmpl) :
    Fintype.card (Fin ws → Bool) = s ∧ 4 ≤ Fintype.card (Fin ws → Bool) ∧
      ∀ β : Fin ws → Bool, ∃ x ∈ Tmpl, aliceBranch ws P x = β := by
  have h := card_aliceBranch ws
  refine ⟨by rw [h, hs], ?_, hsync.2⟩
  rw [h, ← hs]
  exact hs4

/-- **Aux 16 (`08:461--463`: no separate source-only branch).**  "Each retained
source row follows one of the same actual transcripts, and that transcript also
contains template rows; no separate source-only branch is created during the
prefix."  Sharp form: *every* row -- source rows included -- shares its branch
with a selected template row.  General. -/
theorem sync_no_source_only_branch {Rw Cl : Type*} (P : Protocol Rw Cl Bool)
    (ws : ℕ) (Tmpl : Finset Rw) (hsync : SynchronisedPrefix P ws Tmpl)
    (x : Rw) : ∃ y ∈ Tmpl, aliceBranch ws P y = aliceBranch ws P x :=
  hsync.2 (aliceBranch ws P x)

/-! ## §4  `lem:dense-dominant-bijection` (`08:472--506`)

`08:466--470` is emphatic that the dynamic transcript branches "must not be
identified with the `s` fixed Stage-3 blocks in the construction".  The two
index sets are therefore two **different types** below, both of cardinality
`s`, and `d` is a map between them.  Collapsing them into one type would make
the lemma trivial and would erase the distinction `08:504--506` says must be
maintained. -/

/-- **Aux 17 (`08:483--499`: the dominant map is surjective).**  If a fixed
block label `p` were absent from the image of `d`, block `p` would be
nondominant in every dynamic branch, so each branch would take fewer than
`T_3^{aux}` of its selected template rows; the branches partition
`T_p^{sel}`, so `T_0^{aux} < s T_3^{aux}`, contradicting
`eq:dense-separation-gates`.

`Tsel p` is the frozen `T_p^{sel}`, "the `T_0^{aux}` template rows used by the
separation theorem" (`08:474--476`), and `br` is the branch each such row
follows.  General in the row, branch and block types. -/
theorem dominantBlock_surjective {Row Br Bl : Type*} [Fintype Br]
    [DecidableEq Br] {s T₀ T₃ : ℕ} (Tsel : Bl → Finset Row) (br : Row → Br)
    (d : Br → Bl) (hcardBr : Fintype.card Br = s) (hs : 0 < s)
    (hT₀ : ∀ p : Bl, (Tsel p).card = T₀)
    (hdom : ∀ (j : Br) (p : Bl), p ≠ d j →
      ((Tsel p).filter (fun x => br x = j)).card < T₃)
    (hgate : s * T₃ < T₀) :
    Function.Surjective d := by
  classical
  intro p
  by_contra hcon
  have hp : ∀ j : Br, d j ≠ p := fun j hj => hcon ⟨j, hj⟩
  have hne : (Finset.univ : Finset Br).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, hcardBr]
    exact hs
  have hpart : (Tsel p).card
      = ∑ j ∈ (Finset.univ : Finset Br), ((Tsel p).filter (fun x => br x = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (br x))
  have hlt : ∑ j ∈ (Finset.univ : Finset Br),
      ((Tsel p).filter (fun x => br x = j)).card
      < ∑ _j ∈ (Finset.univ : Finset Br), T₃ :=
    Finset.sum_lt_sum_of_nonempty hne (fun j _ => hdom j p (fun h => hp j h.symm))
  rw [Finset.sum_const, Finset.card_univ, hcardBr, smul_eq_mul] at hlt
  rw [hT₀ p] at hpart
  omega

/-- **`lem:dense-dominant-bijection` (`08:478--502`).**  "The map
`d : [s] -> [s]` is a bijection."  Surjectivity is `dominantBlock_surjective`;
the upgrade to a bijection is the frozen closing sentence, "therefore bijective
because both its domain and codomain have size `s`".

Note which hypotheses are absent.  The frozen proof does **not** use the
dominant block's `x_dom` row density (`08:441--442`); adding it would be an
over-strong premise that typechecks perfectly while hiding that the load-bearing
input is the counting gate `s T_3^{aux} < T_0^{aux}`.  General. -/
theorem denseDominantBijection {Row Br Bl : Type*} [Fintype Br] [Fintype Bl]
    [DecidableEq Br] {s T₀ T₃ : ℕ} (Tsel : Bl → Finset Row) (br : Row → Br)
    (d : Br → Bl) (hcardBr : Fintype.card Br = s) (hcardBl : Fintype.card Bl = s)
    (hs : 0 < s) (hT₀ : ∀ p : Bl, (Tsel p).card = T₀)
    (hdom : ∀ (j : Br) (p : Bl), p ≠ d j →
      ((Tsel p).filter (fun x => br x = j)).card < T₃)
    (hgate : s * T₃ < T₀) :
    Function.Bijective d := by
  refine (Fintype.bijective_iff_surjective_and_card d).2
    ⟨dominantBlock_surjective Tsel br d hcardBr hs hT₀ hdom hgate, ?_⟩
  rw [hcardBr, hcardBl]

/-! ## §5  Non-vacuity, statement poles and consistency probes (LANE-GATE 3)

Every construction above is inhabited by a **nondegenerate** witness, and every
statement is checked against its trivial reading.  This includes the two
`Prop`-valued gate transcriptions of §1: a premise bundle that no parameter
tuple satisfies would make every consumer of it vacuous while compiling green.

Witnesses whose parameters are Section-8 quantities are at **legal** values.
Witnesses whose parameters are **schedule** quantities cannot be, because the
frozen schedule pins those above every evaluable literal; those are handled by
the two-tier standard stated before `denseDefectGates_nondegenerate`, and the
word "legal" is withheld from the concrete tier by name. -/

/-! ### §5.1  The two gate bundles are inhabited -/

/-- **Non-vacuity for `eq:source-protection-gate` (`08:556--565`).**  On the
frozen domain -- `s >= 4` and a strictly positive public deletion fraction
`delta_v(G)`, which `04:311--320` guarantees since
`delta_v(G;gamma,Delta) = gamma m/(2 Delta N) >= gamma/(4 Delta) > 0` -- the
gate admits a **strictly positive** row-deletion tolerance.  Positivity is the
whole content: `eta_C = 0` satisfies the inequality trivially and would make
every downstream deletion budget empty.  General in `s` and `delta_v`. -/
theorem sourceProtectionGate_nondegenerate {δv : ℝ} {s : ℕ} (hs : 4 ≤ s)
    (hδ : 0 < δv) : ∃ ηC : ℝ, 0 < ηC ∧ sourceProtectionGate ηC δv s := by
  have hnuT : nuTempR = 1 / 2 ^ 21 := protectedMasses_agree.1
  have hnuS : nuSrcR = 1 / 2 ^ 22 := protectedMasses_agree.2.1
  have hs' : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hnuSpos : (0 : ℝ) < nuSrcR := by rw [hnuS]; norm_num
  have h1 : 0 < nuTempR * rhoTemp / (s : ℝ) := by
    refine div_pos ?_ (by linarith)
    rw [hnuT, rhoTemp]; norm_num
  have h2 : 0 < nuSrcR * δv / 16 := div_pos (mul_pos hnuSpos hδ) (by norm_num)
  have h3 : 0 < nuSrcR / (16 * ((s : ℝ) - 3)) := div_pos hnuSpos (by linarith)
  refine ⟨(1 / 2) * min (nuTempR * rhoTemp / (s : ℝ))
      (min (nuSrcR * δv / 16) (nuSrcR / (16 * ((s : ℝ) - 3)))), ?_, ?_⟩
  · have hmin : 0 < min (nuTempR * rhoTemp / (s : ℝ))
        (min (nuSrcR * δv / 16) (nuSrcR / (16 * ((s : ℝ) - 3)))) :=
      lt_min h1 (lt_min h2 h3)
    linarith
  · simp only [sourceProtectionGate]
    exact le_refl _

/-- **A fully concrete legal instance of `eq:source-protection-gate`**, and the
`etaC_lt_template_allowance` readout it produces.  Frozen minimum `s = 4`; a
legal `delta_v(G) = 1/6` (the value of `04:314--317` at `gamma = 1`,
`Delta = 3`, `m = N`); tolerance `eta_C = 2^{-34} > 0`.  No parameter schedule
may be read out of this witness: it is a legality probe, not a choice. -/
theorem sourceProtectionGate_legal_instance :
    sourceProtectionGate (1 / 2 ^ 34) (1 / 6) 4 ∧
      (1 / 2 ^ 34 : ℝ) ≤ nuTempR * rhoTemp / (2 * ((4 : ℕ) : ℝ)) ∧
      (1 / 2 ^ 34 : ℝ) < nuTempR * rhoTemp / ((4 : ℕ) : ℝ) := by
  have hgate : sourceProtectionGate (1 / 2 ^ 34) (1 / 6) 4 := by
    simp only [sourceProtectionGate, nuTempR, nuSrcR, nuTemp, nuSrc, rhoTemp]
    norm_num
  exact ⟨hgate, (etaC_lt_template_allowance (by norm_num) hgate).1,
    (etaC_lt_template_allowance (by norm_num) hgate).2⟩

/-- **Statement pole: the `s = 3` division pole is real, which is why the frozen
domain is `s >= 4`.**  The third clause of `eq:source-protection-gate` is
`nu_B/(16(s-3))`.  At `s = 3` its denominator vanishes, the Lean convention
`x / 0 = 0` collapses the minimum to `0`, and the gate then forces
`eta_C <= 0` -- no strictly positive tolerance exists.  So
`sourceProtectionGate_nondegenerate` genuinely needs its `4 <= s` hypothesis,
and a witness offered at `s = 3` would be degenerate rather than legal. -/
theorem sourceProtectionGate_pole_at_s_three {ηC δv : ℝ}
    (h : sourceProtectionGate ηC δv 3) : ηC ≤ 0 := by
  simp only [sourceProtectionGate] at h
  have hz : nuSrcR / (16 * (((3 : ℕ) : ℝ) - 3)) = 0 := by norm_num
  rw [hz] at h
  have hle : min (nuTempR * rhoTemp / (((3 : ℕ) : ℝ)))
      (min (nuSrcR * δv / 16) 0) ≤ 0 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  linarith

/-! #### The two-tier standard for `eq:dense-defect-gates`

`t_2`, `q_1` and `q_2` are **schedule** parameters, and the frozen schedule pins
them at magnitudes no numeric literal can reach: `06:766` and `06:770` fix
`t_2 = 2^{k_2}` with `k_2 >= max{4, 2^{19}, m_HS}`, so `t_2 >= 2^{2^{19}}`, and
`06:314--315` fix `q_1 = 2^a - 2` with `a = C_0 (log_2 A_*)^2` at the Stage-1
gate `06:308--310`.  No tuple a decision procedure can evaluate is therefore a
*schedule instance*, and calling one "legal" without qualification is a false
claim about the frozen source.  Non-vacuity is discharged at two separated
tiers instead, and each is named for exactly what it establishes.

* **Tier 1, `denseDefectGates_shape_instance`** -- a fully concrete tuple that
  satisfies every clause of `eq:dense-defect-gates` (`08:679--685`), together
  with the frozen *shape* clauses (`q_1 = 2^a - 2` and `q_1 + 2` a power of two,
  `06:314--315`/`06:321--322`; `t_2` a power of two, `06:770`, divisible by
  `16`, `06:824`; `q_2` a power of two, `06:124`) and the frozen *local*
  comparisons (`4 t_2 <= q_2`, `06:835`; `t_2 >= 2 log_2 q_2`, `06:180`).  It is
  **shape-conforming and locally legal, and it is not a schedule instance**:
  its `k_2 = 5` is below the `06:766` floor `2^{19}`.
* **Tier 2, `denseDefectGates_nondegenerate`** -- the general claim, carrying
  **both** *magnitude* floors and proved symbolically: `2^{19} <= k_2`
  (`06:766`) sits inside the existential, and the Stage-1 exponent floor
  `a >= 2432` (`06:298--315`, through the positive-integer `C_0` of
  `06:056--064`) is taken as a hypothesis with `q_1 = 2^a - 2`.  Neither
  `2^{2^{19}}` nor `2^{2432}` is evaluated, and the one clause where the two
  floors interact -- `t_2 >= 8 q_1` (`08:680`, `06:834`) -- is therefore
  discharged at schedule magnitude rather than at a trivial `q_1`.

Neither tier permits a parameter schedule to be read out of it. -/

/-- **Aux 18 (a natural number is below its own power of two).**  General;
used to choose an exponent dominating a real bound without evaluating it. -/
theorem self_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih =>
      have hstep : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega

/-- **Aux 19 (`06:824`: a power of two past the fourth is divisible by `16`).**
General. -/
theorem sixteen_dvd_two_pow {k : ℕ} (hk : 4 ≤ k) : (16 : ℕ) ∣ 2 ^ k := by
  have h : (2 : ℕ) ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hk
  norm_num at h
  exact h

/-- **Aux 20 (`06:180`: the local comparison `t_2 >= 2 log_2 q_2` is free once
`q_2 = 4 t_2`).**  For `4 <= k`, `2 (k + 2) <= 2^k`, so a power-of-two `q_2`
sitting exactly two doublings above `t_2 = 2^k` still satisfies the frozen
`t_2 >= 2 log_2 q_2`.  General, and proved without evaluating `2^k`. -/
theorem two_exponent_le_two_pow {k : ℕ} (hk : 4 ≤ k) : 2 * (k + 2) ≤ 2 ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  clear hk
  induction m with
  | zero => norm_num
  | succ n ih =>
      have hstep : 2 ^ (n + 1 + 4) = 2 * 2 ^ (n + 4) := by ring
      omega

/-- **Non-vacuity for `eq:dense-defect-gates` (`08:679--685`), tier 2: the
symbolic shape lemma.**  On the frozen domain -- `s >= 4` and `zeta > 0`, the
latter discharged by `zetaBound` from `0 < gamma` -- the three gate clauses are
simultaneously satisfiable **at the frozen shapes and at both frozen magnitude
floors**, not merely at some numbers:

* `q_1 = 2^a - 2` (`06:314--315`, `06:321--322`) at the Stage-1 exponent floor
  `a >= 2432`, which is taken as a hypothesis; the load-bearing "Since
  `q_1 >= 2`" of `06:197` -- what gives `q_1^{t_2} >= 2^{t_2} >= q_2^2` -- is
  then a *consequence* of the floor rather than a separate assumption;
* `t_2 = 2^{k}` with `2^{19} <= k` (`06:766`, `06:770`) and `16 | t_2`
  (`06:824`);
* `q_2 = 2^{e}` a power of two (`06:124`) with the structural conditions
  `4 t_2 <= q_2` (`06:835`) and `2 e <= t_2`, i.e. `t_2 >= 2 log_2 q_2`
  (`06:180`);
* a **strictly positive** diagonal-defect tolerance `eta_R` (`eta_R = 0` is not
  a deletion allowance).

*Where the floor `a >= 2432` comes from.*  `06:056--064` reads `C_0` off the
universal configuration field as a **positive integer**; `06:308--310` requires
`2401(C_0 - 2) > 360{,}000`, and `2401 * 149 = 357{,}749` fails that bound while
`2401 * 150 = 360{,}150` clears it, so `C_0 - 2 >= 150` and `C_0 >= 152`.
`06:298--305` makes `A_*` a power of two at least `16`, so `(log_2 A_*)^2 >= 16`.
Hence `a = C_0 (log_2 A_*)^2 >= 152 * 16 = 2432` (`06:314`), the quantity being
an integer by `06:321--322`.

The proof is symbolic and evaluates no tower: `k` is taken at
`max{2^{19}, a + 3, c}`, where `c` is whatever ceiling `zeta` forces, and
`e = k + 2`, so neither `2^{2^{19}}` nor `2^{2432}` is ever computed.  The joint
clause `t_2 >= 8 q_1` of `08:680` -- restated structurally at `06:834`, and the
one place where the two magnitude floors interact -- is therefore discharged
**at schedule magnitude**, via `8 q_1 = 8(2^a - 2) < 2^{a+3} <= 2^k`, and not at
a trivial `q_1`.  "Least" in `06:124` and in `06:763` is the schedule's own
global choice and is not required of a non-vacuity witness.  Every floor enters
as a hypothesis or as an existential clause, so nothing here permits a parameter
schedule to be read out.  General in `s`, `zeta` and `a`. -/
theorem denseDefectGates_nondegenerate {s : ℕ} {ζ : ℝ} (hs : 4 ≤ s)
    (hζ0 : 0 < ζ) (a : ℕ) (ha : 2432 ≤ a) :
    ∃ (k e t₂ q₁ q₂ : ℕ) (ηR : ℝ),
      q₁ = 2 ^ a - 2 ∧ 2 ≤ q₁ ∧
      t₂ = 2 ^ k ∧ 2 ^ 19 ≤ k ∧ (16 : ℕ) ∣ t₂ ∧
      q₂ = 2 ^ e ∧ 4 * t₂ ≤ q₂ ∧ 2 * e ≤ t₂ ∧
      0 < ηR ∧ denseDefectGates t₂ q₁ q₂ s ζ ηR := by
  classical
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  have hs' : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlocpos : (0 : ℝ) < rhoLoc * muR := by rw [hmu, rhoLoc]; norm_num
  have hnum : (0 : ℝ) < rhoLoc * muR * ζ := mul_pos hlocpos hζ0
  have h8 : (0 : ℝ) < 8 * (s : ℝ) := by linarith
  have h16 : (0 : ℝ) < 16 * (s : ℝ) := by linarith
  -- `q_1 = 2^a - 2` at the Stage-1 floor; `2^a >= 2^2` already gives `2 <= q_1`.
  have hpow4 : (4 : ℕ) ≤ 2 ^ a := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : (2 : ℕ) ≤ 2 ^ a - 2 := by omega
  -- The exponent `k` clears the frozen `t_2` floor `2^19`, the joint clause
  -- `t_2 >= 8 q_1` (through `a + 3`), and whatever ceiling `zeta` forces.
  set c : ℕ := ⌈64 * (s : ℝ) * ((2 ^ a - 2 : ℕ) : ℝ) / ζ⌉₊ with hc
  set k : ℕ := max (2 ^ 19) (max (a + 3) c) with hk
  have hk19 : 2 ^ 19 ≤ k := le_max_left _ _
  have hka : a + 3 ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
  have hkc : c ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
  have hk4 : 4 ≤ k := le_trans (by norm_num) hk19
  refine ⟨k, k + 2, 2 ^ k, 2 ^ a - 2, 2 ^ (k + 2),
    rhoLoc * muR * ζ / (16 * (s : ℝ)),
    rfl, hq1, rfl, hk19, sixteen_dvd_two_pow hk4, rfl, ?_, ?_,
    div_pos hnum h16, ?_, ?_, ?_⟩
  · -- `4 t_2 <= q_2` (`06:835`), an identity at `e = k + 2`.
    have : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
    omega
  · -- `2 e <= t_2`, i.e. `t_2 >= 2 log_2 q_2` (`06:180`).
    exact two_exponent_le_two_pow hk4
  · -- `t_2 >= 8 q_1` (`08:680`) at schedule magnitude:
    -- `8(2^a - 2) < 8 * 2^a = 2^(a+3) <= 2^k`, with no tower evaluated.
    have hpa : (2 : ℕ) ^ (a + 3) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hka
    have hea : (2 : ℕ) ^ (a + 3) = 8 * 2 ^ a := by ring
    omega
  · -- `q_2 >= 64 s q_1 / zeta` (`08:681`), through the ceiling and `c < 2^c`.
    have hceil : 64 * (s : ℝ) * ((2 ^ a - 2 : ℕ) : ℝ) / ζ ≤ (c : ℝ) := Nat.le_ceil _
    have hcpow : c < 2 ^ c := self_lt_two_pow c
    have hmono : (2 : ℕ) ^ c ≤ 2 ^ (k + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hchain : (c : ℝ) ≤ ((2 ^ (k + 2) : ℕ) : ℝ) := by
      have : c ≤ 2 ^ (k + 2) := le_trans (le_of_lt hcpow) hmono
      exact_mod_cast this
    calc 64 * (s : ℝ) * ((2 ^ a - 2 : ℕ) : ℝ) / ζ ≤ (c : ℝ) := hceil
      _ ≤ ((2 ^ (k + 2) : ℕ) : ℝ) := hchain
  · -- `eta_R < rho_loc mu_D zeta/(8 s)` (`08:683`).
    exact div_lt_div_of_pos_left hnum h8 (by linarith)

/-- **Non-vacuity for `eq:dense-defect-gates` (`08:679--685`), tier 1: a fully
concrete shape-conforming, locally legal satisfiability witness**, and the
`etaR_lt_selector_allowance` readout it produces.

*What this witness is, stated exactly.*  It is **not** a schedule instance, and
the word "legal" is deliberately absent from its name.  `06:766` forces
`k_2 >= 2^{19}`, hence `t_2 >= 2^{2^{19}}`, and `06:308--315` force
`q_1 = 2^a - 2` at a Stage-1 exponent far above `2`; no evaluable literal meets
either magnitude floor.  What the witness does establish, at
`s = 4` (the frozen Section-8 minimum, `08:402`) and the pinned
`zeta 1 = gamma/24` at `gamma = 1` (`04:503--509`), is that the frozen
inequality system is genuinely satisfiable **at the frozen shapes**:

* `q_1 = 2 = 2^2 - 2`, so `q_1 + 2 = 4` is a power of two (`06:314--315`,
  `06:321--322`) and `2 <= q_1` (`06:197`);
* `t_2 = 32 = 2^5`, a power of two (`06:770`) divisible by `16` (`06:824`);
* `q_2 = 16384 = 2^{14}`, a power of two (`06:124`);
* the local comparisons `4 t_2 = 128 <= 16384 = q_2` (`06:835`) and
  `2 log_2 q_2 = 28 <= 32 = t_2` (`06:180`);
* all three clauses of `eq:dense-defect-gates`: `8 q_1 = 16 <= 32`,
  `64 s q_1/zeta = 12288 <= 16384`, and `eta_R = 2^{-20}` strictly below the
  frozen `rho_loc mu_D zeta/(8s) = 1/565248`.

Its `k_2 = 5` is below the `06:766` floor, which is precisely why it is called
a shape instance and not a legal one; the magnitude floor is carried by
`denseDefectGates_nondegenerate` instead.  No parameter schedule may be read
out of either tier. -/
theorem denseDefectGates_shape_instance :
    (2 : ℕ) = 2 ^ 2 - 2 ∧ (32 : ℕ) = 2 ^ 5 ∧ (16 : ℕ) ∣ (32 : ℕ) ∧
      (16384 : ℕ) = 2 ^ 14 ∧ 4 * 32 ≤ (16384 : ℕ) ∧ 2 * 14 ≤ (32 : ℕ) ∧
      denseDefectGates 32 2 16384 4 ((zeta 1 : ℚ) : ℝ) (1 / 2 ^ 20) ∧
      (1 / 2 ^ 20 : ℝ) < muR / 3072 ∧ (1 / 2 ^ 20 : ℝ) < muR * rhoSigma := by
  have hzeta : ((zeta 1 : ℚ) : ℝ) = 1 / 24 := by
    simp only [zeta]
    norm_num
  have hgate : denseDefectGates 32 2 16384 4 ((zeta 1 : ℚ) : ℝ) (1 / 2 ^ 20) := by
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [hzeta]; norm_num
    · rw [hzeta]
      simp only [muR, muMass, rhoLoc]
      norm_num
  have hζ0 : (0 : ℝ) < ((zeta 1 : ℚ) : ℝ) := by rw [hzeta]; norm_num
  have hζ1 : ((zeta 1 : ℚ) : ℝ) ≤ 1 / 24 := by rw [hzeta]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, hgate,
    (etaR_lt_selector_allowance (by norm_num) hζ0 hζ1 hgate).1,
    (etaR_lt_selector_allowance (by norm_num) hζ0 hζ1 hgate).2⟩

/-! ### §5.2  The synchronisation and bijection witnesses -/

/-- A Bob subtree of cost exactly `3`.  It has two jobs.  It makes the witness
protocol's Alice prefix stop after exactly two levels, and it supplies the
frozen Stage-3 depth floor `D_2 >= B_cap >= 3` (`07:501`, with `2 <= D_2` at
`07:442` and `07:472`): the residual reached at depth `ws + 1` must be able to
carry `d_2 = 3`, so a one-node Bob subtree would sit at an excluded `d_2`. -/
def witBobL : Protocol (Bool × Bool) Bool Bool :=
  Protocol.bNode (fun y => y)
    (Protocol.bNode (fun y => y)
      (Protocol.bNode (fun y => y) (Protocol.leaf false) (Protocol.leaf true))
      (Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf false)))
    (Protocol.bNode (fun y => y)
      (Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf false))
      (Protocol.bNode (fun y => y) (Protocol.leaf false) (Protocol.leaf true)))

/-- The mirrored Bob subtree of cost exactly `3`, so the witness protocol is not
constant. -/
def witBobR : Protocol (Bool × Bool) Bool Bool :=
  Protocol.bNode (fun y => y)
    (Protocol.bNode (fun y => y)
      (Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf false))
      (Protocol.bNode (fun y => y) (Protocol.leaf false) (Protocol.leaf true)))
    (Protocol.bNode (fun y => y)
      (Protocol.bNode (fun y => y) (Protocol.leaf false) (Protocol.leaf true))
      (Protocol.bNode (fun y => y) (Protocol.leaf true) (Protocol.leaf false)))

/-- The second Alice level of the witness protocol. -/
def witInner : Protocol (Bool × Bool) Bool Bool :=
  Protocol.aNode (fun x => x.2) witBobL witBobR

/-- **The synchronisation witness at legal values**: two Alice levels
(`ws = 2`, hence `s = 2^2 = 4`, the frozen minimum) over a Bob block of depth
`3`, total cost `5 = ws + d_2` at `d_2 = 3`, which is the frozen budget
`log_2 s + D_2` of `08:325` at the frozen Stage-3 depth floor
`D_2 >= B_cap >= 3` (`07:501`).  Every hypothesis of `denseSynchronisation`
holds and its conclusions are nondegenerate: the prefix genuinely stops at
depth `2`, and all four branches occur. -/
def syncWitProto : Protocol (Bool × Bool) Bool Bool :=
  Protocol.aNode (fun x => x.1) witInner witInner

/-- **Non-vacuity + hypothesis consistency for `denseSynchronisation`.**  The
full hypothesis bundle of the landed result -- in its own binder order --
is satisfiable at legal parameter values: `s = 4` (a power of two, `>= 4`),
`ws = 2`, `d_2 = 3`, budget `ws + d_2 = 5 = cost(P)`.  Hence no `False` is
derivable from the bundle, and the result is not vacuously true.

`d_2` is the frozen `D_2 = comp(S_2)` of `08:453`, and the frozen Stage-3 block
fixes `2 <= D_2` (`07:442`, restated as a standing guard at `07:472`) and
`D_2 >= B_cap >= 3` (`07:501`).  So the witness runs at the frozen *depth
floor* `d_2 = 3`, and the frozen budget `log_2 s + D_2` of `08:325` reads
`2 + 3 = 5` here.  A witness at `d_2 = 1` would sit at a value the frozen
source excludes.

The witness is nondegenerate in both places it could have been cheap.  The
completeness conjunct of `hsync` is discharged by exhibiting a row for each of
the four branches, not by an empty index type.  And the guarded `hres` is
discharged from the *unguarded* bound `3 ≤ cost` at every row -- the depth-`3`
residual is a genuine Bob block of cost `3` -- so the guard is not what makes
it true, and `hres` is not satisfied by a zero bound. -/
theorem denseSynchronisation_hypotheses_consistent :
    (4 : ℕ) = 2 ^ 2 ∧ 4 ≤ 4 ∧
      syncWitProto.cost ≤ 2 + 3 ∧
      SynchronisedPrefix syncWitProto 2 (Finset.univ : Finset (Bool × Bool)) ∧
      (∀ x : Bool × Bool, IsAlicePrefixAt syncWitProto (2 + 1) x →
        3 ≤ (aliceResidual x (2 + 1) syncWitProto).cost) := by
  refine ⟨by norm_num, le_refl 4, ?_, ⟨?_, ?_⟩, ?_⟩
  · simp [syncWitProto, witInner, witBobL, witBobR, Protocol.cost]
  · intro x i hi
    interval_cases i
    · exact ⟨_, _, _, rfl⟩
    · refine ⟨fun x => x.2, witBobL, witBobR, ?_⟩
      by_cases h : x.1 <;> simp [aliceResidual, aliceStep, syncWitProto, witInner, h]
  · intro β
    refine ⟨(β 0, β 1), Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i
    · rfl
    · by_cases h : β 0 <;>
        simp [aliceBranch, aliceBit, aliceResidual, aliceStep, syncWitProto,
          witInner, h]
  · intro x _
    by_cases h1 : x.1 <;> by_cases h2 : x.2 <;>
      simp [aliceResidual, aliceStep, syncWitProto, witInner, witBobL, witBobR,
        Protocol.cost, h1, h2]

/-- **Statement pole for `lem:dense-synchronisation`.**  The clause
`¬ IsAlicePrefix P (ws + 1)` is not automatic: the very same witness protocol
has an Alice prefix of depth `2`, so a protocol whose budget allowed one more
Alice level would have one.  The clause is bought by the budget hypothesis at
`08:455--457`, and by nothing else. -/
theorem denseSynchronisation_not_automatic :
    IsAlicePrefix syncWitProto 2 ∧ ¬ IsAlicePrefix syncWitProto 3 := by
  refine ⟨denseSynchronisation_hypotheses_consistent.2.2.2.1.1, ?_⟩
  intro h
  obtain ⟨a, l, r, hEq⟩ := h (false, false) 2 (by omega)
  simp [aliceResidual, aliceStep, syncWitProto, witInner, witBobL] at hEq

/-- A three-Alice-level protocol whose third level is a constant query, so the
walk reaches a **leaf** after exactly three steps.  Used only for the `hres`
statement pole below. -/
def hresPoleProto : Protocol (Bool × Bool) Bool Bool :=
  Protocol.aNode (fun x => x.1)
    (Protocol.aNode (fun x => x.2)
      (Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true))
      (Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true)))
    (Protocol.aNode (fun x => x.2)
      (Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true))
      (Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true)))

/-- **Statement pole for the guarded `hres` binder.**  Conditionalising the
frozen residual estimate on `IsAlicePrefixAt P (ws + 1) x` does **not** turn it
into `True`.  Here the guard holds at every row -- the protocol really has three
Alice levels -- and the estimate `1 <= cost` nevertheless fails, because the
node reached is a leaf of cost `0`.  So the guarded binder is a real constraint,
while the *unguarded* form would additionally have asserted the frozen
`08:448--454` estimate at rows whose walk has already stopped, where
`aliceStep` is the identity and the frozen text produces no node at all. -/
theorem hres_is_a_real_constraint :
    (∀ x : Bool × Bool, IsAlicePrefixAt hresPoleProto (2 + 1) x)
      ∧ ¬ (∀ x : Bool × Bool, IsAlicePrefixAt hresPoleProto (2 + 1) x →
            1 ≤ (aliceResidual x (2 + 1) hresPoleProto).cost) := by
  have hpre : ∀ x : Bool × Bool, IsAlicePrefixAt hresPoleProto (2 + 1) x := by
    intro x i hi
    interval_cases i
    · exact ⟨_, _, _, rfl⟩
    · refine ⟨fun x => x.2,
        Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true),
        Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true),
        ?_⟩
      by_cases h : x.1 <;> simp [aliceResidual, aliceStep, hresPoleProto, h]
    · refine ⟨fun _ => false, Protocol.leaf false, Protocol.leaf true, ?_⟩
      by_cases h1 : x.1 <;> by_cases h2 : x.2 <;>
        simp [aliceResidual, aliceStep, hresPoleProto, h1, h2]
  refine ⟨hpre, ?_⟩
  intro h
  have := h (false, false) (hpre (false, false))
  simp [aliceResidual, aliceStep, hresPoleProto, Protocol.cost] at this

/-- **Statement pole for the branch map.**  The transcript branch is genuinely
*protocol-dependent* (`08:336`): it is not a relabelling of the row.  Two
different rows of the witness share a branch as soon as the prefix is one level
short, so a candidate encoding that identified branches with rows would be
wrong. -/
theorem aliceBranch_is_not_the_row :
    aliceBranch 1 syncWitProto (false, false) = aliceBranch 1 syncWitProto (false, true)
      ∧ ((false, false) : Bool × Bool) ≠ (false, true) := by
  refine ⟨?_, by decide⟩
  funext i
  fin_cases i
  rfl

/-- **Non-vacuity for `lem:dense-dominant-bijection` at legal values.**  Frozen
minimum `s = 4`; four fixed blocks each holding `T_0^{aux} = 5` selected
template rows; `T_3^{aux} = 1`, so the gate `s T_3^{aux} = 4 < 5 = T_0^{aux}`
holds.  Each block's rows all follow one branch, and the resulting dominant map
is the **four-cycle** `j ↦ j + 1`, not the identity: the lemma is inhabited by a
nontrivial bijection. -/
theorem dominantBijection_legal_instance :
    Function.Bijective (fun j : Fin 4 => j + 1) := by
  refine denseDominantBijection (Row := Fin 4 × Fin 5) (Br := Fin 4) (Bl := Fin 4)
    (s := 4) (T₀ := 5) (T₃ := 1)
    (fun p => (Finset.univ : Finset (Fin 4 × Fin 5)).filter (fun x => x.1 = p))
    (fun x => x.1 - 1) (fun j => j + 1) (by simp) (by simp) (by norm_num)
    ?_ ?_ (by norm_num)
  · decide
  · decide

/-- **Statement pole for `lem:dense-dominant-bijection`.**  The counting gate
`s T_3^{aux} < T_0^{aux}` is load-bearing: drop it and every other hypothesis
of the lemma can hold while `d` is constant, hence not surjective.  Here all
four selected sets are empty, so every nondominance bound holds trivially. -/
theorem dominantBijection_gate_is_load_bearing :
    (∀ (j : Fin 4) (p : Fin 4), p ≠ (fun _ : Fin 4 => (0 : Fin 4)) j →
        (((fun _ : Fin 4 => (∅ : Finset (Fin 4))) p).filter
          (fun x => (fun y : Fin 4 => y) x = j)).card < 1)
      ∧ ¬ Function.Surjective (fun _ : Fin 4 => (0 : Fin 4)) := by
  refine ⟨by decide, ?_⟩
  intro h
  obtain ⟨j, hj⟩ := h 1
  have hzero : (0 : Fin 4) = 1 := hj
  exact absurd hzero (by decide)

/-! ## §6  Candidate B, the rejected encoding

Recorded as race evidence with its own proved battery, exactly as the opening
module recorded its rejected carrier encoding. -/

/-- **Candidate B**: the branch map taken as data rather than derived from the
protocol. -/
structure AbstractBranching (Rw : Type*) (k : ℕ) where
  /-- The claimed transcript branch of each row. -/
  branch : Rw → Fin k → Bool
  /-- The claimed completeness of the prefix. -/
  onto : Function.Surjective branch

/-- **Candidate B, Aux 1**: the branch count. -/
theorem card_AbstractBranching {Rw : Type*} (k : ℕ) (_ : AbstractBranching Rw k) :
    Fintype.card (Fin k → Bool) = 2 ^ k := by
  simp

/-- **Candidate B, Aux 2**: every branch is inhabited. -/
theorem AbstractBranching_fiber_nonempty {Rw : Type*} {k : ℕ}
    (A : AbstractBranching Rw k) (β : Fin k → Bool) : ∃ x : Rw, A.branch x = β :=
  A.onto β

/-- **Candidate B, Aux 3**: Candidate A refines Candidate B.  Any synchronised
prefix in the landed encoding yields an abstract branching, so nothing of
Candidate B's content is lost by landing Candidate A -- while the converse fails,
because an abstract branching carries no link to the protocol at all. -/
noncomputable def abstractBranching_of_protocol {Rw Cl : Type*}
    (P : Protocol Rw Cl Bool) (k : ℕ) (Tmpl : Finset Rw)
    (hsync : SynchronisedPrefix P k Tmpl) : AbstractBranching Rw k where
  branch := aliceBranch k P
  onto := fun β => by
    obtain ⟨x, _, hx⟩ := hsync.2 β
    exact ⟨x, hx⟩

/-! ### Disposition of Candidate B (recorded, binding on consumers)

`AbstractBranching` is race evidence only.  It defines no branch family of its
own, it is consumed by nothing in the active route, and it may **not** be used
to encode the branchwise defect and witness families of `08:613--1346` without a
fresh judged tranche: the frozen `B_j^{temp}`, `B^{diag}` and `U_j` are all
defined by reference to the dynamic branches of `P_A`, which Candidate B cannot
name. -/

end EthInapproximability.ParameterizedNP.DenseSynchronisation
