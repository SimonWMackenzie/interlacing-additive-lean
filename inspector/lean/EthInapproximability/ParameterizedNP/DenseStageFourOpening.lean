import EthInapproximability.ParameterizedNP.RawStageFour

/-!
# Parameterized NP route: the Section-8 opening block

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 1--328** -- the
  opening block of `sec:dense-stage4`, from the subsection head through the
  `thm:dense-stage4` statement territory and the contradiction setup that
  opens its proof.  The anchors traced here, in the order the block prints
  them:
  * lines 17--31: `B = M_4`, `Omega = Cols(B)`,
    `Rows(B) = T u W_V u W_B` with `T = u_{p in [s]} T_p`,
    `W_V = I_V x Rows(R)`, `W_B = I_B x Rows(R)`, and "They are duplications
    of existing rows and columns, not new gadgets";
  * lines 33--47: `y_0 = min Y_R`, the constant selector
    `k_0 : [s+1] -> Y_R`, "constructor data derived from the public order, not
    a proof-time choice", `tail_{s+1}(gamma)(r) = gamma(kappa_1(r))`, and
    `Sigma = {k_0} x Rows(M_2)^s`;
  * lines 48--65: `d_{alpha,gamma}(p) = (alpha,gamma)`, `D_alpha`,
    `D_diag = ⨆_{alpha in [q_2]} D_alpha`, and "Consequently every displayed
    pair is an actual column of `B`";
  * `eq:protected-raw-cardinality-abbreviations` (label line 78, display
    68--77): `M_0, S_0, D_0, X_0, T_raw, V_raw, B_raw`;
  * `eq:protected-labelled-carriers` (label line 94, display 81--93): the
    three labelled column reservoirs and the four labelled row reservoirs;
  * lines 96--97: "The value of `A` ignores the reservoir label and
    multiplicity index and is the corresponding entry of `B`";
  * `eq:protected-multiplicities` (label line 108, display 98--107):
    `w_0 = 182 S_0 D_0`, `w_Sigma = M_0 D_0`, `w_D = M_0 S_0`,
    `u_0 = (2^{22}-4) T_raw V_raw B_raw`, `u_temp = 2 X_0 V_raw B_raw`,
    `u_V = X_0 T_raw B_raw`, `u_B = X_0 T_raw V_raw`;
  * `eq:protected-carrier-cardinalities` (label line 121, display 111--120):
    `|Cols(A)| = 184 M_0 S_0 D_0` and
    `|Rows(A)| = 2^{22} X_0 T_raw V_raw B_raw`;
  * lines 123--138: the exact column masses `91/92, 1/184, 1/184`, the exact
    row masses `1 - 2^{-20}, 2^{-21}, 2^{-22}, 2^{-22}`, and the abbreviations
    `tau, mu_Sigma, mu_D, sigma, nu_T, nu_V, nu_B`;
  * lines 139--144: "Selecting one representative of every underlying row and
    column projects `A` to `B`, while a protocol for `B` computes `A` after the
    labels are forgotten.  Hence `comp(A) = comp(B)`";
  * lines 145--156: `N = A^T`, `C = D + a + log_2 q_2 + log_2 s + 1 =
    D_2 + log_2 s + 1`, `D_2 = B_cap + log_2 q_2`, and the fixed orientation
    convention "the row-deletion tolerance `eta_R` for `N` therefore acts on
    columns of `A`, whereas `eta_C` acts on rows of `A`";
  * lines 161--182: the low-row profile schedule `x_N = 1/16`,
    `x_T = 2^{-b_T}`, `I_j = s/2^j`, `p_j = 9 I_j/16`, `x_j = I_j x_T`,
    `h_j^{raw} = 2^{-2^{0.49 sqrt(log_2 I_j)}}`,
    `r_j = (y/2^j - sigma)/(1 - sigma)` and `beta_j^{raw}`;
  * `eq:raw-low-gates` (label line 190, display 184--191): the two finite
    comparisons;
  * `lem:raw-low-profile` (label line 194, statement 193--216) with its
    ambient predicate `Admissible(Public, Pi, T_lev)` and `NoCert(Public)`,
    and its proof 218--257 -- in particular the density chain 223--227, the
    elementary extremal bound 234--239, the hard-seed rung 240--251, and the
    closing "Taking the minimum over `j = 0, 1, 2`" at 252--256;
  * lines 259--275: `S_2 = M_2^T`, `m_3`, `x_3 = 1 - rho_temp`,
    `y_3 = 1 - rho_Sigma`, `T_0^{aux}`, `T_3^{aux}`, `x_dom`, and
    `rho_temp = 1/1000`, `rho_Sigma = 1/100`, `rho_loc = 1/4`;
  * `eq:dense-separation-gates` (label line 285, display 276--286);
  * `eq:stage2-aux-certificate` (label line 295, display 290--296):
    `comp(S_2) = D_2`, `Lambda_{S_2}(1, x_T, y) >= D_2`, `x_T = 2^{-b_T}`,
    and the sentence "The same **physical** matrix `S_2` has the auxiliary
    `(1/10, b_T)`-robustness certificate established at Stage 2";
  * `thm:dense-stage4` (label line 299, statement 298--319);
  * lines 321--328: "Fix an arbitrary retained member `N'` ... and fix an
    arbitrary protocol `P` computing `N'`.  Assume for contradiction that
    `cost(P) <= C - 1 = log_2 s + D_2`."
* **Mandatory predecessor anchor:** `06-parameter-schedule.tex`, **line 124**,
  "The source theorem then fixes `q_2 = the least power of two at least
  `12 s N_E`" -- the schedule identification the banked `RawStageFour` module
  explicitly declined (its coverage limit 4) and this module discharges first.
  Also consumed from Section 6: `eq:fixed-protected-masses` (label 138) for
  the protected constants, and `06:228` for the tolerance chain
  `0 < eta_R <= eta_C/2 < tau < x_N`.
* **Predecessor anchor (the handoff consumed by pin):**
  `07-one-level-construction.tex` lines 512--680 through the banked
  `EthInapproximability.ParameterizedNP.RawStageFour`, whose §4 supplies the
  Section-8 row destructuring (`guardedRowsSplit`, `TemplateRows`), the
  selector reservoir (`constSelector`, `sigmaCol`) and the diagonal reservoir
  (`diagTuple`, `diagCol`), and whose §5 supplies the budget identities
  (`raw_budget_identities`) and the postponed `NO` value (`rawNoExact`).
  **None of that handoff is restated here.**
* **Reader counterparts** (frozen release,
  `reader-facing/sections/A-stage4-details.tex`, subsection "Protected
  duplication" and `thm:paper-protected-stage4`), one per declaration group,
  none of them shared with another module:
  * lines 164--178 (the row partition, `Omega`, the canonical `Sigma` and
    `D_diag` "with no promise-dependent choices", and the seven abbreviations
    `M_0, S_0, D_0, X_0, T_0, V_0, B_0`) -- `Omega`, `SelCar`, `DiagCar`,
    `RowsB`, `TempCar`, `VertCar`, `BlockCar`, `selIncl`, `diagIncl`,
    `tempIncl`, `vertIncl`, `blockIncl`, and the three injectivity lemmas that
    make the `⊔` a disjoint union;
  * lines 180--181 ("a labelled duplicate `A` of `B` with three column
    reservoirs and four row reservoirs") -- `ProtCols`, `ProtRows`,
    `card_ProtCols`, `card_ProtRows`;
  * lines 182--194 (the two multiplicity displays) -- `wBase`, `wSel`,
    `wDiag`, `uBase`, `uTemp`, `uVert`, `uBlock`, with
    `protected_cols_card_identity` and `protected_rows_card_identity`;
  * line 195 ("The value of `A` ignores labels and multiplicity indices and
    evaluates the underlying entry of `B`") -- `protectedDup` and
    `protectedDup_ignores_labels`;
  * lines 196--199 (the four exact mass readouts) -- `protected_col_masses`
    and `protected_row_masses`;
  * lines 199--204 ("Forgetting labels gives entry-preserving surjections ...
    their fibre sizes may vary with the protected category.  Choosing the
    least representative in every nonempty fibre gives sections whose image is
    a copy of `B`.  A protocol for `B` pulls back to `A`, while the sections
    realize `B` as a restriction of `A`") -- `colForget`, `rowForget`,
    `colSection`, `rowSection`, `D_precomp_le`, `D_forget_eq`,
    `sectionOf_injective`;
  * `eq:paper-protected-complexity-preservation` (label line 207, display
    line 206) -- `D_protectedDup` and `D_protectedA`;
  * line 209 ("Set `N = A^T`") -- `transposeN`, `transposeN_apply`,
    `D_transposeN`;
  * lines 213--216 (the display `C = D + a + log q_2 + log s + 1`) --
    `cBlock`, `dTwoBlock`, `cBlock_eq`, `cBlock_pred`;
  * `eq:paper-protected-dense` **first clause** (line 220,
    `D_N(1; 1-eta_R, 1-eta_C) >= C`) -- `DenseStageFourConclusion` and
    `denseStageFour`;
  * `eq:paper-protected-dense` **second clause** (line 221, `comp N = C`) --
    `transposedA_comp_chain`;
  * `eq:paper-protected-low` (label line 227, display line 226) --
    `rawLowProfile`.  The reader pins `y = 3/5`; the frozen autoformalization
    leaves `y` a binder at `08:175` and `08:213`, and the **frozen** reading is
    what is transcribed, with `y` explicit.
  The **§3b pinned-instance group** (`protectedAFrozen`,
  `protectedA_at_frozen_multiplicities`, the two count-positivity lemmas, the
  two base-multiplicity positivity lemmas, `protectedAFrozen_apply`,
  `protectedAFrozen_restricts_to_B`, `card_ProtColsFrozen`,
  `card_ProtRowsFrozen`, `card_protectedAFrozen_carriers`, `D_protectedAFrozen`,
  `protectedAFrozen_col_masses`, `protectedAFrozen_row_masses`,
  `protectedAFrozen_carriers_nondegenerate`) claims **no** reader item, and this
  is deliberate rather than an omission: the reader states the duplicate and its
  seven multiplicities in one locus, lines 179--194, already assigned above to
  the carrier group and the multiplicity group.  §3b adds no further reader
  content -- it is the step that makes those two already-assigned assignments
  facts about **one built object** instead of about a free-width family.
  Recording it as a second claimant of lines 179--194 would double-assign a
  reader item, which the crosswalk forbids.
  Three further reader loci are **declined rather than taken silently**, on the
  `CLOCK-001` / `cc-t1x` / `cc-t1y-r1` precedent recorded in the crosswalk:
  * `eq:paper-guarded-q2` (line 34) is **already assigned** to the banked
    `GuardedSourceSlab.q2` by `SOURCE-SLAB-001`, and line 35 to `card_le_q2` /
    `q2_lt`; so `schedule_q2` and `schedule_q2_unique` claim **no** reader
    item, and the schedule identification is recorded against the frozen
    `06:124` alone;
  * `eq:paper-reference-profile` (label line 233) -- the explicitly ordered
    all-column submatrix `G_0` -- is `cor:exact-protected-stage4`
    (`08:1327`), outside this block, and **nothing here claims it**;
  * lines 150--160 (the reader's protocol obstruction: "a claim of the form
    `D_W(1; theta, 1) >= C` is impossible in this orientation") is a statement
    about a **different**, all-column claim; it is recorded in the coverage
    limits below and is **not** proved here.

## Dependencies, imports and external adapters

* Imports `EthInapproximability.ParameterizedNP.RawStageFour` only, hence
  transitively `StageThreeExactScale`, `StageTwoRelaxed`, `StageOneInterlace`,
  `PublicRecords`, `GuardedSourceSlab`, `GuardedSourceGraph`, `FiniteSlots`,
  `PilotStage3` and the project-axiom-free `LegacyNPCC.Core` /
  `LegacyNPCC.Bridge` facades reached through `EthInapproximability.Prelude`.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency
  graph.
* Banked project interfaces consumed **by pin, never restated**:
  * `GuardedSourceSlab.q2`, `q2_isPowTwo`, `card_le_q2`, `q2_le_of_le`,
    `SlabRow`; `GuardedSourceGraph.EndpointGraph`, `card_edge_pos`;
  * `RawStageFour.RawRows`, `RawCols`, `RowsTwo`, `TemplateRows`,
    `guardedRowsSplit`, `constSelector`, `sigmaCol`, `diagTuple`, `diagCol`,
    `p₀`, `raw_budget_identities`, `rawNoExact`;
  * `FiniteSlots.Stage1SlotBinding` and `Slot`;
  * `StageOneInterlace.bCap`, `Stage1Cols`;
  * `StageTwoRelaxed.dTwo`, `StageTwoWidths`, `bobBit`;
  * `StageThreeExactScale.outerBudget`, `StageThreeScale`;
  * `PublicRecords.D_const`;
  * `TwoCopyLadder.le_LambdaGE_iff` (the three-rung unfolding).
* Vendored interfaces consumed **by pin, never restated**: `NPCC.D`,
  `NPCC.Dfamily`, `NPCC.subgame`, `NPCC.bracketGE`, `NPCC.bracketGE.nonempty`,
  `NPCC.LambdaGE`, `NPCC.comp_transpose`, `NPCC.one_le_D_of_two_values`,
  `Workspace.Types.Interlace.interlaceFun`,
  `Workspace.UpperBound.AchievableCosts_nonempty`, `EthBridge.le_Dfamily`.
* **New vendored-gap work.** `NPCC` supplies complexity invariance only along
  **equivalences** (`D_equiv_invariance`).  The protected duplication is a
  non-injective surjection with fibres of unequal size, so `precompProto`,
  `cost_precompProto`, `eval_precompProto` and `D_precomp_le` are new and are
  the vehicle for both directions of `08:139--144`.
* Proof status: **new** for the labelled duplication, its carriers, its exact
  cardinalities and masses, the complexity-preservation theorem, and the
  low-profile schedule arithmetic; **adapted** for the `C`/`D_2` identities,
  which are the block's own reading of the banked budgets; **inherited by pin**
  for the Section-8 reservoirs and the Section-6 width.
* Axiom surface (`#print axioms`, run on every named result of this module,
  including the whole §3b pinned-instance group):
  `propext`, `Classical.choice`, `Quot.sound` only -- and several results
  (`protected_cols_card_identity`, `protected_rows_card_identity`,
  `selIncl_injective`, `cBlock_eq`, `cBlock_pred`, `block_budget_identities`,
  `diagIncl_injective`, `rowIncl_injective`) need strictly less.  No project
  axiom, no unproved placeholder, no new opaque certificate.

## Candidate encodings of `eq:protected-labelled-carriers` (`k = 2`, raced)

See §7 for the full statement of the race.  Summary: **Candidate A**, a tagged
sum of products in which each frozen reservoir is a literal summand, is landed
(6 aux lemmas proved, exactly reproduces the frozen `⊔` displays, no per-label
instance needed); **Candidate B**, one dependent sigma type over a named label
type, is recorded with its own 3 proved aux lemmas and loses on faithfulness at
the frozen arity and on length.  The §1 complexity machinery is
encoding-independent and applies to both, so the race is decided purely on the
carrier display.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the schedule identification (2): `schedule_q2_unique`,
  `schedule_q2_not_every_power`.
* `A2` complexity transport (3): `D_precomp_le`, `D_forget_eq`,
  `sectionOf_injective`.
* `A3` the labelled carriers (7): `protectedDup_ignores_labels`,
  `card_ProtCols`, `card_ProtRows`, the two nonemptiness instances,
  `colSection_injective`, `rowSection_injective`.
* `A4` the frozen counts and masses (5): `protected_cols_card_identity`,
  `protected_rows_card_identity`, `card_protected_carriers`,
  `protected_col_masses`, `protected_row_masses`.
* `A5` the Section-8 pin (4): `selIncl_injective`, `diagIncl_injective`,
  `rowIncl_injective`, `D_protectedA`.
* `A5b` the **pinned instance** at `eq:protected-multiplicities` (11):
  `section8_col_counts_pos`, `section8_row_counts_pos`,
  `protectedA_at_frozen_multiplicities`, `wBaseF_pos`, `uBaseF_pos`,
  `protectedAFrozen_multiplicities_pos`, `protectedAFrozen_apply`,
  `protectedAFrozen_restricts_to_B`, `card_ProtColsFrozen`,
  `card_ProtRowsFrozen`, `D_protectedAFrozen`, with the two mass restatements
  `protectedAFrozen_col_masses` and `protectedAFrozen_row_masses`.
* `A6` the transpose and the block constants (6): `transposeN_apply`,
  `D_transposeN`, `cBlock_eq`, `cBlock_pred`, `block_budget_identities`,
  `transposedA_comp_chain`, plus `massConstants_agree`.
* `A7` the low-row profile (5): `widthI_rungs`, `hRawSchedule_antitone`,
  `rawLowGates_cover_rungs`, `block_count_of_extremal`,
  `lowProfile_of_frozen_rungs`.
* `A8` the dense statement (3): `member_bound_of_no_cheap_protocol`,
  `denseFamily_nonempty`, `denseSeparationGates_force_depth`.
* Candidate B's own battery (3): `card_Labelled`, `nonempty_Labelled`,
  `forgetLabel_apply`.

That is **45 labelled `Aux` items proved plus 3 for the rejected candidate**,
with `0` unproved, alongside four statement poles
(`rawLowProfile_not_automatic`, `denseStageFour_not_automatic`,
`unit_multiplicities_break_the_masses`,
`protectedAFrozen_pin_is_load_bearing`), three consistency probes
(`tolerance_chain_consistent`, `denseSeparationGates_satisfiable`,
`denseStageFour_hypotheses_consistent`), and seven non-vacuity readouts at
legal parameter values -- five for the generic device and two
(`Fwit_schedule_legal`, `protectedAFrozen_legal_instance`) for the pinned
instance, the latter at `a = 3`, `s = 4`, `q_2 = 64`, which is literally the
`06:124` width at `N_E = 1`.

## Honest scope and recorded coverage limits

1. **`thm:dense-stage4` is landed as a statement, not as a proof.**  The whole
   of `08:330--1346` -- synchronisation, the dominant-block bijection, the
   branchwise defect and witness families, the selection `w > 4 b`, the
   weighted routing, the weighted frontier and the two closure lemmas -- is the
   single named hypothesis `hnoProtocol` of `denseStageFour`.  What is proved
   here is the passage from that per-member contradiction to the family bound,
   which needs `0 < C` and the nonemptiness of the bracket family; the latter
   is not a formality, since `Dfamily` is a `Nat.sInf` returning `0` on the
   empty family.
2. **`lem:raw-low-profile` is landed as a statement with its rung hypotheses.**
   The per-rung construction of `08:240--251` -- projection to `p_j` blocks
   followed by the inherited General Hard Seed Lemma at width `I_j` -- is the
   named hypothesis `hrung`.  What is proved here is the frozen closing step
   `08:252--256` together with the two genuinely arithmetic steps of the proof:
   `rawLowGates_cover_rungs` (the density chain `08:223--227`) and
   `block_count_of_extremal` (the elementary extremal bound `08:234--239`).
3. **`Admissible`, `NoCert` and `LevelStep` have no Lean declaration yet** and
   are carried throughout as **explicit propositional binders**.  They are
   never silent axioms and never premise bundles with derived fields.
4. **No complexity claim about `B` is asserted.**  `rawNoExact` remains the
   banked transcribed predicate; `transposedA_comp_chain` is a closed
   conditional carrying it as a hypothesis.
5. **The gate predicates are transcribed, never asserted.**  `rawLowGates`,
   `denseSeparationGates` and `stageTwoAuxCertificate` are `Prop`-valued
   transcriptions.  `denseSeparationGates_satisfiable` shows the five
   comparisons are jointly realizable at legal public values, and
   `denseSeparationGates_force_depth` records the derived constraint
   `s < 2^{b_T}`; the schedule's additional tie
   `b_T = 2^{j_49(log_2(s/4))}` (`06:237--243`) is a **Section-6 obligation**
   outside this block and is **not** discharged here.
6. **The reader's protocol obstruction is not formalized.**  Reader lines
   150--160 argue that an all-column claim `D_W(1; theta, 1) >= C` is
   impossible in this orientation; that is why `thm:dense-stage4` uses the
   common-threshold pair `(1 - eta_R, 1 - eta_C)` with **both** tolerances
   positive.  The obstruction itself is not proved in Lean, and no consumer may
   read a `eta_C = 0` strengthening out of this module.
7. **The masses hold at two levels, and the difference is recorded.**
   `protected_col_masses` / `protected_row_masses` are exact rational identities
   at abstract counts; `protectedAFrozen_col_masses` /
   `protectedAFrozen_row_masses` restate them **at the pinned instance**, with
   the denominator the actual `Fintype.card` of the carrier `protectedAFrozen`
   is defined on.  What is still *not* claimed is a closed-form value for the
   guarded source's seven cardinalities: `M_0, S_0, D_0, X_0, T_raw, V_raw,
   B_raw` enter only through `Fintype.card` and their positivity, which
   `section8_col_counts_pos` / `section8_row_counts_pos` discharge from carrier
   inhabitedness, `0 < q_2` and the frozen `s >= 4`.
8. No parameter schedule may be read out of any witness below; `RowsWit`,
   `ColsWit` and `BmatWit` are minimal legal counts chosen so that every frozen
   multiplicity is positive, and nothing else.  The one exception is deliberate
   and is itself schedule-checked: `Fwit`, `q = 64` and the `Bool` carriers of
   `protectedAFrozen_legal_instance` are legal *because* `Fwit_schedule_legal`
   proves the `06:124` clauses for them, and nothing else may be read out of
   them either.
9. **The `Nat.ceil` reading of `eq:raw-low-gates` is a hypothesis-side
   weakening only.**  `betaRaw` and `rawLowGates` use `Nat.ceil` where the
   frozen `⌈·⌉` is the integer ceiling.  At legal parameters (`r_j >= 0`) the
   two agree; where they could differ, `Nat.ceil` makes `rawLowGates` -- which
   this module only ever consumes as a **hypothesis** -- strictly easier to
   satisfy, so every theorem carrying it is weakened, never strengthened.  Any
   later tranche that needs `eq:raw-low-gates` as a **conclusion** must revisit
   this and is barred from citing the present form.  Recorded in the route
   ledger under `STAGE4-PROTECTED-OPENING-001`, the row that owns this module.
10. **Candidate B is race evidence with a recorded disposition.**  See the
   disposition note at the end of §7: `Labelled` and its battery define no
   second `A`, are consumed by nothing, and may not be used to re-encode
   Section 8 without a fresh judged tranche.
-/

namespace EthInapproximability.ParameterizedNP.DenseStageFourOpening

open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.StageThreeExactScale
open EthInapproximability.ParameterizedNP.RawStageFour

/-! ## §0  Mandatory first step: the `06:124` schedule identification

`07-one-level-construction.tex` leaves the Stage-2 coordinate width `q` a free
binder, and the banked `RawStageFour` module records that decision as its
coverage limit 4 ("the schedule identification `q_2 = q2(G,s)` ... is **not**
transcribed").  Section 8 may not inherit that freedom: every carrier of
`eq:protected-labelled-carriers` is counted, so the width has to be the one the
schedule fixes.  The frozen sentence is `06-parameter-schedule.tex:122--125`,

>  Thus `s` is a public power of two.  The source theorem then fixes
>  `q_2 = the least power of two at least 12 s N_E`.

with `N_E = m_G = |E|`.  The three clauses below are the banked
`GuardedSourceSlab` facts, consumed **by pin**; what is new is the uniqueness
statement, which is what turns the frozen sentence into an identification. -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The `06:124` schedule identification.**  The banked `q2 G s` *is* "the
least power of two at least `12 s N_E`": it is a power of two, it clears the
bound, and it lies below every power of two that clears the bound.  Nothing is
recomputed -- the three conjuncts are `q2_isPowTwo`, `card_le_q2` and
`q2_le_of_le`, consumed by pin.  General in `G` and `s`. -/
theorem schedule_q2 (G : EndpointGraph V E) (s : ℕ) :
    (∃ r : ℕ, q2 G s = 2 ^ r) ∧
      12 * s * Fintype.card E ≤ q2 G s ∧
      (∀ r : ℕ, 12 * s * Fintype.card E ≤ 2 ^ r → q2 G s ≤ 2 ^ r) :=
  ⟨q2_isPowTwo G s, card_le_q2 G s, fun _ h => q2_le_of_le G s h⟩

/-- **Aux 1 (the schedule value is forced, not chosen).**  Any public width
satisfying the three clauses of `06:124` equals the banked `q2 G s` on the
nose.  This is what licenses Section 8 to write one symbol `q_2` for the
Stage-2 coordinate width and for the guarded source's width: the identification
is a theorem about the schedule, not a naming convention, and no consumer may
substitute a different minimal power of two.  General. -/
theorem schedule_q2_unique (G : EndpointGraph V E) (s q : ℕ)
    (hpow : ∃ r : ℕ, q = 2 ^ r)
    (hge : 12 * s * Fintype.card E ≤ q)
    (hmin : ∀ r : ℕ, 12 * s * Fintype.card E ≤ 2 ^ r → q ≤ 2 ^ r) :
    q = q2 G s := by
  obtain ⟨r, hr⟩ := q2_isPowTwo G s
  obtain ⟨r', hr'⟩ := hpow
  refine le_antisymm ?_ ?_
  · have h := hmin r (by rw [← hr]; exact card_le_q2 G s)
    rwa [← hr] at h
  · have h : q2 G s ≤ 2 ^ r' := q2_le_of_le G s (by rw [← hr']; exact hge)
    rwa [← hr'] at h

/-- **Aux 2 (the identification is a genuine constraint on the width).**  The
schedule clauses are not satisfied by every public power of two: at every
positive `s` the width `1 = 2^0` fails the lower clause, because the frozen
graph has a nonempty edge set.  So `schedule_q2_unique` is not vacuously
applicable, and a Section-8 declaration that took an arbitrary `q` would be
strictly weaker than the frozen text.  General. -/
theorem schedule_q2_not_every_power (G : EndpointGraph V E) {s : ℕ} (hs : 0 < s) :
    ¬ (12 * s * Fintype.card E ≤ 1) := by
  have hE : 0 < Fintype.card E := G.card_edge_pos
  have h : 12 ≤ 12 * s * Fintype.card E := by
    calc (12 : ℕ) = 12 * 1 * 1 := by norm_num
      _ ≤ 12 * s * Fintype.card E := Nat.mul_le_mul (Nat.mul_le_mul_left 12 hs) hE
  omega

/-! ## §1  Complexity transport along a forgetful map

`08:139--144` asserts `comp(A) = comp(B)` from two directions: "a protocol for
`B` computes `A` after the labels are forgotten" and "Selecting one
representative of every underlying row and column projects `A` to `B`".  Both
are instances of one general fact -- precomposing a game with arbitrary maps on
the two input carriers cannot increase its complexity -- which the vendored
layer supplies only for **equivalences** (`NPCC.D_equiv_invariance`).  The
duplication is not an equivalence: the reader's counterpart records that "their
fibre sizes may vary with the protected category".  So the general map version
is proved here. -/

/-- Precompose a protocol with arbitrary maps on the two input carriers,
transporting each node predicate and preserving the tree shape verbatim. -/
def precompProto {A B A' B' Z : Type*} (u : A' → A) (v : B' → B) :
    Protocol A B Z → Protocol A' B' Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x => a (u x)) (precompProto u v l) (precompProto u v r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y => b (v y)) (precompProto u v l) (precompProto u v r)

/-- Precomposition preserves the tree depth: only node predicates change. -/
theorem cost_precompProto {A B A' B' Z : Type*} (u : A' → A) (v : B' → B)
    (P : Protocol A B Z) : (precompProto u v P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [precompProto, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp only [precompProto, Protocol.cost, ihl, ihr]

/-- The precomposed protocol evaluates at the transported point. -/
theorem eval_precompProto {A B A' B' Z : Type*} (u : A' → A) (v : B' → B)
    (P : Protocol A B Z) (x : A') (y : B') :
    (precompProto u v P).eval x y = P.eval (u x) (v y) := by
  induction P generalizing x y with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [precompProto, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr => simp only [precompProto, Protocol.eval, ihl, ihr]

/-- **Aux 3 (the transport half of `08:139--144`).**  Precomposing a game with
arbitrary maps on the two input carriers cannot increase its deterministic
communication complexity.  The vendored `NPCC.D_equiv_invariance` is the
special case of two equivalences; the duplication needs the general map form,
because forgetting labels is a **non-injective** surjection with fibres of
unequal size.  General in all four carriers. -/
theorem D_precomp_le {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A']
    [Fintype B'] (f : A → B → Bool) (u : A' → A) (v : B' → B) :
    D (fun a b => f (u a) (v b)) ≤ D f := by
  have hsub : AchievableCosts f ⊆ AchievableCosts (fun a b => f (u a) (v b)) := by
    rintro c ⟨P, hcost, hcomp⟩
    exact ⟨precompProto u v P, by rw [cost_precompProto]; exact hcost,
      fun x y => by rw [eval_precompProto]; exact hcomp (u x) (v y)⟩
  have hne : (AchievableCosts f).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty f
  have hmem : sInf (AchievableCosts f) ∈ AchievableCosts f := Nat.sInf_mem hne
  exact Nat.sInf_le (hsub hmem)

/-- **Aux 4 (`08:139--144`, the general `comp(A) = comp(B)`).**  Let `u`, `v`
forget the labels and let `σ`, `ρ` select one representative of every
underlying row and column.  Then the labelled matrix has *exactly* the
complexity of the matrix it duplicates.

The two directions are the two frozen sentences, and both go through
`D_precomp_le`.  The right-inverse hypotheses `hσ`, `hρ` are what the frozen
"selecting one representative" supplies; they force `σ` and `ρ` to be
**injective** (`sectionOf_injective` below), which is why the second direction
exhibits `B` as a restriction of `A` rather than a merge.  General. -/
theorem D_forget_eq {Base Base' A B : Type*} [Fintype Base] [Fintype Base']
    [Fintype A] [Fintype B] (f : Base → Base' → Bool) (u : A → Base)
    (v : B → Base') (σ : Base → A) (ρ : Base' → B)
    (hσ : ∀ b, u (σ b) = b) (hρ : ∀ b, v (ρ b) = b) :
    D (fun r c => f (u r) (v c)) = D f := by
  refine le_antisymm (D_precomp_le f u v) ?_
  have hle := D_precomp_le (fun (r : A) (c : B) => f (u r) (v c)) σ ρ
  have hfun : (fun (b : Base) (b' : Base') => f (u (σ b)) (v (ρ b'))) = f := by
    funext b b'
    rw [hσ b, hρ b']
  rwa [hfun] at hle

/-- **Aux 5 (a representative selector is injective).**  Any right inverse of a
forgetful map is injective.  Injectivity is recorded explicitly because every
complexity claim of this block runs through it. -/
theorem sectionOf_injective {Base A : Type*} (u : A → Base) (σ : Base → A)
    (hσ : ∀ b, u (σ b) = b) : Function.Injective σ :=
  Function.LeftInverse.injective (g := u) hσ

/-! ## §2  The protected duplication `A` (`eq:protected-labelled-carriers`)

`08:80--95` builds `A` from `B` by three labelled column reservoirs and four
labelled row reservoirs, each of the frozen shape
`{label} x carrier x [multiplicity]`.  The carriers below are the **landed
Candidate A** encoding: a tagged sum of products, in which the frozen labels
`base`, `sel`, `diag` and `base`, `temp`, `src-v`, `src-b` are the summand
injections and the frozen `[w]`, `[u]` are literal `Fin` blocks.  The rejected
Candidate B is recorded in §7. -/

/-- **The labelled column carrier of `eq:protected-labelled-carriers`**,
`({base} x Omega x [w_0]) u ({sel} x Sigma x [w_Sigma]) u
({diag} x D_diag x [w_D])`.  General in the three reservoir carriers and the
three multiplicities. -/
abbrev ProtCols (Om Sg Dg : Type*) (w₀ wSg wD : ℕ) : Type _ :=
  (Om × Fin w₀) ⊕ ((Sg × Fin wSg) ⊕ (Dg × Fin wD))

/-- **The labelled row carrier of `eq:protected-labelled-carriers`**,
`({base} x Rows(B) x [u_0]) u ({temp} x T x [u_temp]) u
({src-v} x W_V x [u_V]) u ({src-b} x W_B x [u_B])`.  General. -/
abbrev ProtRows (Xr Tm Wv Wb : Type*) (u₀ uT uV uB : ℕ) : Type _ :=
  (Xr × Fin u₀) ⊕ ((Tm × Fin uT) ⊕ ((Wv × Fin uV) ⊕ (Wb × Fin uB)))

/-- Forgetting the column reservoir label and the multiplicity index
(`08:96--97`).  `iSg` and `iD` are the frozen inclusions of the selector and
diagonal reservoirs into `Omega = Cols(B)`. -/
def colForget {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} (iSg : Sg → Om) (iD : Dg → Om) :
    ProtCols Om Sg Dg w₀ wSg wD → Om
  | Sum.inl z => z.1
  | Sum.inr (Sum.inl z) => iSg z.1
  | Sum.inr (Sum.inr z) => iD z.1

/-- Forgetting the row reservoir label and the multiplicity index
(`08:96--97`).  `iT`, `iV`, `iB` are the frozen inclusions of the template,
vertex-source and blocker-source reservoirs into `Rows(B)`. -/
def rowForget {Xr Tm Wv Wb : Type*} {u₀ uT uV uB : ℕ} (iT : Tm → Xr)
    (iV : Wv → Xr) (iB : Wb → Xr) : ProtRows Xr Tm Wv Wb u₀ uT uV uB → Xr
  | Sum.inl z => z.1
  | Sum.inr (Sum.inl z) => iT z.1
  | Sum.inr (Sum.inr (Sum.inl z)) => iV z.1
  | Sum.inr (Sum.inr (Sum.inr z)) => iB z.1

/-- "Selecting one representative of every underlying column" (`08:139`): the
base reservoir at multiplicity index `0`.  The frozen positive multiplicity is
what the hypothesis `0 < w_0` records. -/
def colSection {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} (hw : 0 < w₀) :
    Om → ProtCols Om Sg Dg w₀ wSg wD :=
  fun z => Sum.inl (z, ⟨0, hw⟩)

/-- "Selecting one representative of every underlying row" (`08:139`). -/
def rowSection {Xr Tm Wv Wb : Type*} {u₀ uT uV uB : ℕ} (hu : 0 < u₀) :
    Xr → ProtRows Xr Tm Wv Wb u₀ uT uV uB :=
  fun z => Sum.inl (z, ⟨0, hu⟩)

@[simp] theorem colForget_colSection {Om Sg Dg : Type*} {w₀ wSg wD : ℕ}
    (iSg : Sg → Om) (iD : Dg → Om) (hw : 0 < w₀) (z : Om) :
    colForget (w₀ := w₀) (wSg := wSg) (wD := wD) iSg iD (colSection hw z) = z := rfl

@[simp] theorem rowForget_rowSection {Xr Tm Wv Wb : Type*} {u₀ uT uV uB : ℕ}
    (iT : Tm → Xr) (iV : Wv → Xr) (iB : Wb → Xr) (hu : 0 < u₀) (z : Xr) :
    rowForget (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) iT iV iB
      (rowSection hu z) = z := rfl

/-- **The labelled duplicate `A` of the raw Stage-4 matrix `B`** (`08:96--97`):
"The value of `A` ignores the reservoir label and multiplicity index and is the
corresponding entry of `B`."  General in every carrier, inclusion and
multiplicity. -/
def protectedDup {Xr Tm Wv Wb Om Sg Dg : Type*} {u₀ uT uV uB w₀ wSg wD : ℕ}
    (Bmat : Xr → Om → Bool) (iT : Tm → Xr) (iV : Wv → Xr) (iB : Wb → Xr)
    (iSg : Sg → Om) (iD : Dg → Om) :
    ProtRows Xr Tm Wv Wb u₀ uT uV uB → ProtCols Om Sg Dg w₀ wSg wD → Bool :=
  fun r c => Bmat (rowForget iT iV iB r) (colForget iSg iD c)

/-- **Aux 6 (`08:96`: the value ignores the label and the multiplicity
index).**  Two labelled rows over one and the same row of `B` are identical
rows of `A`, and likewise for columns.  This is the defining sentence of the
duplication, stated as a general congruence rather than assumed. -/
theorem protectedDup_ignores_labels {Xr Tm Wv Wb Om Sg Dg : Type*}
    {u₀ uT uV uB w₀ wSg wD : ℕ} (Bmat : Xr → Om → Bool) (iT : Tm → Xr)
    (iV : Wv → Xr) (iB : Wb → Xr) (iSg : Sg → Om) (iD : Dg → Om)
    (r r' : ProtRows Xr Tm Wv Wb u₀ uT uV uB)
    (c c' : ProtCols Om Sg Dg w₀ wSg wD)
    (hr : rowForget iT iV iB r = rowForget iT iV iB r')
    (hc : colForget iSg iD c = colForget iSg iD c') :
    protectedDup Bmat iT iV iB iSg iD r c = protectedDup Bmat iT iV iB iSg iD r' c' := by
  simp only [protectedDup, hr, hc]

/-- **Aux 7 (`M7`/`M10`: the exact labelled column count).**  Each summand is a
`Fintype.card` of a tagged carrier times its frozen multiplicity.  General. -/
theorem card_ProtCols (Om Sg Dg : Type*) [Fintype Om] [Fintype Sg] [Fintype Dg]
    (w₀ wSg wD : ℕ) :
    Fintype.card (ProtCols Om Sg Dg w₀ wSg wD) =
      Fintype.card Om * w₀ + (Fintype.card Sg * wSg + Fintype.card Dg * wD) := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **Aux 8 (`M7`/`M10`: the exact labelled row count).**  General. -/
theorem card_ProtRows (Xr Tm Wv Wb : Type*) [Fintype Xr] [Fintype Tm]
    [Fintype Wv] [Fintype Wb] (u₀ uT uV uB : ℕ) :
    Fintype.card (ProtRows Xr Tm Wv Wb u₀ uT uV uB) =
      Fintype.card Xr * u₀ +
        (Fintype.card Tm * uT +
          (Fintype.card Wv * uV + Fintype.card Wb * uB)) := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **Aux 9 (`M7`: the labelled carriers are nonempty).**  Nonemptiness
propagates from the base reservoir together with the positivity of its
multiplicity; this is what the frozen positive multiplicities of
`eq:protected-multiplicities` are carried for. -/
instance protCols_nonempty {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} [Nonempty Om]
    [NeZero w₀] : Nonempty (ProtCols Om Sg Dg w₀ wSg wD) :=
  ⟨Sum.inl (Classical.arbitrary Om, ⟨0, Nat.pos_of_ne_zero (NeZero.ne w₀)⟩)⟩

instance protRows_nonempty {Xr Tm Wv Wb : Type*} {u₀ uT uV uB : ℕ} [Nonempty Xr]
    [NeZero u₀] : Nonempty (ProtRows Xr Tm Wv Wb u₀ uT uV uB) :=
  ⟨Sum.inl (Classical.arbitrary Xr, ⟨0, Nat.pos_of_ne_zero (NeZero.ne u₀)⟩)⟩

/-- **Aux 10 (`08:139--144`, `comp(A) = comp(B)` at the labelled carriers).**
The protected duplicate has exactly the complexity of the raw matrix it
duplicates, for **every** choice of reservoir carriers, inclusions and
multiplicities with positive base multiplicities.

Both frozen sentences are discharged, and the **injectivity of the two
representative selectors is part of the conclusion**, not a side remark: the
frozen "projects `A` to `B`" is a restriction only because the selectors do not
merge two underlying rows or columns. -/
theorem D_protectedDup {Xr Tm Wv Wb Om Sg Dg : Type*}
    {u₀ uT uV uB w₀ wSg wD : ℕ} [Fintype Xr] [Fintype Tm] [Fintype Wv]
    [Fintype Wb] [Fintype Om] [Fintype Sg] [Fintype Dg]
    (Bmat : Xr → Om → Bool) (iT : Tm → Xr) (iV : Wv → Xr) (iB : Wb → Xr)
    (iSg : Sg → Om) (iD : Dg → Om) (hu : 0 < u₀) (hw : 0 < w₀) :
    Function.Injective
        (rowSection (Xr := Xr) (Tm := Tm) (Wv := Wv) (Wb := Wb) (u₀ := u₀)
          (uT := uT) (uV := uV) (uB := uB) hu) ∧
      Function.Injective
        (colSection (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀) (wSg := wSg)
          (wD := wD) hw) ∧
      D (protectedDup (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) (w₀ := w₀)
        (wSg := wSg) (wD := wD) Bmat iT iV iB iSg iD) = D Bmat :=
  ⟨sectionOf_injective
      (rowForget (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) iT iV iB) _
      (fun _ => rfl),
    sectionOf_injective (colForget (w₀ := w₀) (wSg := wSg) (wD := wD) iSg iD) _
      (fun _ => rfl),
    D_forget_eq Bmat (rowForget (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) iT iV iB)
      (colForget (w₀ := w₀) (wSg := wSg) (wD := wD) iSg iD) (rowSection hu)
      (colSection hw) (fun _ => rfl) (fun _ => rfl)⟩

theorem colSection_injective {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} (iSg : Sg → Om)
    (iD : Dg → Om) (hw : 0 < w₀) :
    Function.Injective (colSection (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
      (wSg := wSg) (wD := wD) hw) :=
  sectionOf_injective (colForget (w₀ := w₀) (wSg := wSg) (wD := wD) iSg iD) _
    (fun _ => rfl)

theorem rowSection_injective {Xr Tm Wv Wb : Type*} {u₀ uT uV uB : ℕ}
    (iT : Tm → Xr) (iV : Wv → Xr) (iB : Wb → Xr) (hu : 0 < u₀) :
    Function.Injective (rowSection (Xr := Xr) (Tm := Tm) (Wv := Wv) (Wb := Wb)
      (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) hu) :=
  sectionOf_injective (rowForget (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) iT iV iB)
    _ (fun _ => rfl)

/-! ### The frozen multiplicities and the exact carrier cardinalities -/

/-- `w_0 = 182 S_0 D_0` (`eq:protected-multiplicities`). -/
def wBase (S₀ D₀ : ℕ) : ℕ := 182 * S₀ * D₀

/-- `w_Sigma = M_0 D_0` (`eq:protected-multiplicities`). -/
def wSel (M₀ D₀ : ℕ) : ℕ := M₀ * D₀

/-- `w_D = M_0 S_0` (`eq:protected-multiplicities`). -/
def wDiag (M₀ S₀ : ℕ) : ℕ := M₀ * S₀

/-- `u_0 = (2^{22} - 4) T_raw V_raw B_raw` (`eq:protected-multiplicities`). -/
def uBase (T₀ V₀ B₀ : ℕ) : ℕ := (2 ^ 22 - 4) * T₀ * V₀ * B₀

/-- `u_temp = 2 X_0 V_raw B_raw` (`eq:protected-multiplicities`). -/
def uTemp (X₀ V₀ B₀ : ℕ) : ℕ := 2 * X₀ * V₀ * B₀

/-- `u_V = X_0 T_raw B_raw` (`eq:protected-multiplicities`). -/
def uVert (X₀ T₀ B₀ : ℕ) : ℕ := X₀ * T₀ * B₀

/-- `u_B = X_0 T_raw V_raw` (`eq:protected-multiplicities`). -/
def uBlock (X₀ T₀ V₀ : ℕ) : ℕ := X₀ * T₀ * V₀

/-- **Aux 11 (`eq:protected-carrier-cardinalities`, column half).**
`M_0 w_0 + S_0 w_Sigma + D_0 w_D = 184 M_0 S_0 D_0`, exactly as displayed.
General in the three raw counts. -/
theorem protected_cols_card_identity (M₀ S₀ D₀ : ℕ) :
    M₀ * wBase S₀ D₀ + (S₀ * wSel M₀ D₀ + D₀ * wDiag M₀ S₀) =
      184 * (M₀ * S₀ * D₀) := by
  simp only [wBase, wSel, wDiag]
  ring

/-- **Aux 12 (`eq:protected-carrier-cardinalities`, row half).**
`X_0 u_0 + T_raw u_temp + V_raw u_V + B_raw u_B = 2^{22} X_0 T_raw V_raw B_raw`,
exactly as displayed.  General in the four raw counts; the frozen split
`X_0 = T_raw + V_raw + B_raw` is **not** needed for this identity and is
therefore not smuggled in as a hypothesis. -/
theorem protected_rows_card_identity (X₀ T₀ V₀ B₀ : ℕ) :
    X₀ * uBase T₀ V₀ B₀ +
        (T₀ * uTemp X₀ V₀ B₀ + (V₀ * uVert X₀ T₀ B₀ + B₀ * uBlock X₀ T₀ V₀)) =
      2 ^ 22 * (X₀ * T₀ * V₀ * B₀) := by
  simp only [uBase, uTemp, uVert, uBlock]
  norm_num
  ring

/-- **Aux 13 (`eq:protected-carrier-cardinalities` at the labelled carriers).**
The two frozen cardinalities hold for the actual `Fintype.card` of the two
labelled carriers, at the frozen multiplicities, whenever the reservoir counts
are read off the carriers themselves.  General. -/
theorem card_protected_carriers (Om Sg Dg Xr Tm Wv Wb : Type*) [Fintype Om]
    [Fintype Sg] [Fintype Dg] [Fintype Xr] [Fintype Tm] [Fintype Wv]
    [Fintype Wb] :
    Fintype.card
        (ProtCols Om Sg Dg (wBase (Fintype.card Sg) (Fintype.card Dg))
          (wSel (Fintype.card Om) (Fintype.card Dg))
          (wDiag (Fintype.card Om) (Fintype.card Sg))) =
      184 * (Fintype.card Om * Fintype.card Sg * Fintype.card Dg) ∧
    Fintype.card
        (ProtRows Xr Tm Wv Wb
          (uBase (Fintype.card Tm) (Fintype.card Wv) (Fintype.card Wb))
          (uTemp (Fintype.card Xr) (Fintype.card Wv) (Fintype.card Wb))
          (uVert (Fintype.card Xr) (Fintype.card Tm) (Fintype.card Wb))
          (uBlock (Fintype.card Xr) (Fintype.card Tm) (Fintype.card Wv))) =
      2 ^ 22 *
        (Fintype.card Xr * Fintype.card Tm * Fintype.card Wv * Fintype.card Wb) := by
  constructor
  · rw [card_ProtCols]
    exact protected_cols_card_identity _ _ _
  · rw [card_ProtRows]
    exact protected_rows_card_identity _ _ _ _

/-! ### The exact protected masses (`08:123--138`) -/

/-- `tau = 1/92` (`08:133`), the total protected non-base column mass. -/
def tauMass : ℚ := 1 / 92

/-- `mu_Sigma = mu_D = 1/184` (`08:134`). -/
def muMass : ℚ := 1 / 184

/-- `sigma = 2^{-20}` (`08:135`), the total protected non-base row mass. -/
def sigmaMass : ℚ := 1 / 2 ^ 20

/-- `nu_T = 2^{-21}` (`08:136`). -/
def nuTemp : ℚ := 1 / 2 ^ 21

/-- `nu_V = nu_B = 2^{-22}` (`08:137`). -/
def nuSrc : ℚ := 1 / 2 ^ 22

/-- **Aux 14 (`08:123--126`: the exact column masses).**  At the frozen
multiplicities the base, selector and diagonal column masses of `A` are exactly
`91/92`, `1/184`, `1/184`, and the two protected reservoirs together carry
exactly `tau = 1/92`.  Positivity of the three raw counts is required and is
supplied by the nonemptiness facts of the raw carriers. -/
theorem protected_col_masses {M₀ S₀ D₀ : ℕ} (hM : 0 < M₀) (hS : 0 < S₀)
    (hD : 0 < D₀) :
    ((M₀ * wBase S₀ D₀ : ℕ) : ℚ) / ((184 * (M₀ * S₀ * D₀) : ℕ) : ℚ) = 91 / 92 ∧
      ((S₀ * wSel M₀ D₀ : ℕ) : ℚ) / ((184 * (M₀ * S₀ * D₀) : ℕ) : ℚ) = muMass ∧
      ((D₀ * wDiag M₀ S₀ : ℕ) : ℚ) / ((184 * (M₀ * S₀ * D₀) : ℕ) : ℚ) = muMass ∧
      ((S₀ * wSel M₀ D₀ + D₀ * wDiag M₀ S₀ : ℕ) : ℚ) /
          ((184 * (M₀ * S₀ * D₀) : ℕ) : ℚ) = tauMass := by
  have hM' : (M₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hS' : (S₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hD' : (D₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  simp only [wBase, wSel, wDiag, muMass, tauMass]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **Aux 15 (`08:127--130`: the exact row masses).**  At the frozen
multiplicities the base, template, vertex-source and blocker-source row masses
of `A` are exactly `1 - 2^{-20}`, `2^{-21}`, `2^{-22}`, `2^{-22}`, and the
three protected reservoirs together carry exactly `sigma = 2^{-20}`. -/
theorem protected_row_masses {X₀ T₀ V₀ B₀ : ℕ} (hX : 0 < X₀) (hT : 0 < T₀)
    (hV : 0 < V₀) (hB : 0 < B₀) :
    ((X₀ * uBase T₀ V₀ B₀ : ℕ) : ℚ) /
          ((2 ^ 22 * (X₀ * T₀ * V₀ * B₀) : ℕ) : ℚ) = 1 - sigmaMass ∧
      ((T₀ * uTemp X₀ V₀ B₀ : ℕ) : ℚ) /
          ((2 ^ 22 * (X₀ * T₀ * V₀ * B₀) : ℕ) : ℚ) = nuTemp ∧
      ((V₀ * uVert X₀ T₀ B₀ : ℕ) : ℚ) /
          ((2 ^ 22 * (X₀ * T₀ * V₀ * B₀) : ℕ) : ℚ) = nuSrc ∧
      ((B₀ * uBlock X₀ T₀ V₀ : ℕ) : ℚ) /
          ((2 ^ 22 * (X₀ * T₀ * V₀ * B₀) : ℕ) : ℚ) = nuSrc ∧
      ((T₀ * uTemp X₀ V₀ B₀ + (V₀ * uVert X₀ T₀ B₀ + B₀ * uBlock X₀ T₀ V₀) : ℕ) : ℚ) /
          ((2 ^ 22 * (X₀ * T₀ * V₀ * B₀) : ℕ) : ℚ) = sigmaMass := by
  have hX' : (X₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hX.ne'
  have hT' : (T₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hV' : (V₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hV.ne'
  have hB' : (B₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  simp only [uBase, uTemp, uVert, uBlock, sigmaMass, nuTemp, nuSrc]
  norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ## §3  The Section-8 pin: the frozen reservoirs of `08:17--65`

The three column reservoirs and the four row reservoirs are **not** new
objects.  They are the banked `RawStageFour` §4 handoff, consumed by pin:
`guardedRowsSplit` for the frozen row destructuring `Rows(B) = T u W_V u W_B`,
`sigmaCol` for the selector reservoir `Sigma = {k_0} x Rows(M_2)^s`, and
`diagCol` for the diagonal reservoir
`D_diag = ⨆_alpha {(tail_{s+1}(gamma), d_{alpha,gamma}) : gamma in C_1}`.
Nothing of that handoff is restated here. -/

/-- `Omega = Cols(B)` (`08:20`), the frozen raw Stage-4 column carrier. -/
abbrev Omega (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) : Type _ := RawCols F q Y

/-- The selector reservoir carrier.  `Sigma = {k_0} x Rows(M_2)^s` (`08:46`) is
indexed by its second factor alone, because `k_0` is the single
lexicographically least selector value of `08:33--38`. -/
abbrev SelCar (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) : Type _ :=
  Slot F.s → RowsTwo F q Y

/-- The diagonal reservoir carrier.  `D_diag = ⨆_{alpha in [q_2]} D_alpha`
(`08:62--63`) is a **disjoint** union over `alpha`, and each `D_alpha` is
indexed by `gamma in C_1`, so the carrier is `[q_2] x C_1`. -/
abbrev DiagCar (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) : Type _ :=
  Slot q × Stage1Cols F Y

/-- `Rows(B)` at the guarded source (`08:21`). -/
abbrev RowsB (F : Stage1SlotBinding) (V X L₂ : Type*) : Type _ :=
  RawRows F (SlabRow V F.s) X L₂

/-- `T = ⨆_{p in [s]} T_p` (`08:22`), the template reservoir carrier. -/
abbrev TempCar (F : Stage1SlotBinding) (L₂ : Type*) : Type _ := TemplateRows F L₂

/-- `W_V = I_V x Rows(R)` (`08:23`) with `I_V = [4s] x V`. -/
abbrev VertCar (F : Stage1SlotBinding) (V X : Type*) : Type _ :=
  (Fin (4 * F.s) × V) × X

/-- `W_B = I_B x Rows(R)` (`08:24`) with `I_B = [4s] x [s-3]`. -/
abbrev BlockCar (F : Stage1SlotBinding) (X : Type*) : Type _ :=
  (Fin (4 * F.s) × Fin (F.s - 3)) × X

/-- The selector reservoir's inclusion into `Omega`, the banked
`RawStageFour.sigmaCol` at the frozen constant selector `k_0 = const y_0`. -/
def selIncl (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (y₀ : Y) :
    SelCar F q Y → Omega F q Y := fun d => sigmaCol F y₀ d

/-- The diagonal reservoir's inclusion into `Omega`, the banked
`RawStageFour.diagCol`. -/
def diagIncl (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} :
    DiagCar F q Y → Omega F q Y := fun z => diagCol F z.1 z.2

/-- The template reservoir's inclusion into `Rows(B)`, the banked
`RawStageFour.guardedRowsSplit` read backwards. -/
def tempIncl (F : Stage1SlotBinding) (V X L₂ : Type*) :
    TempCar F L₂ → RowsB F V X L₂ :=
  fun t => (guardedRowsSplit V F X L₂).symm (Sum.inl t)

/-- The vertex-source reservoir's inclusion into `Rows(B)`. -/
def vertIncl (F : Stage1SlotBinding) (V X L₂ : Type*) :
    VertCar F V X → RowsB F V X L₂ :=
  fun w => (guardedRowsSplit V F X L₂).symm (Sum.inr (Sum.inl w))

/-- The blocker-source reservoir's inclusion into `Rows(B)`. -/
def blockIncl (F : Stage1SlotBinding) (V X L₂ : Type*) :
    BlockCar F X → RowsB F V X L₂ :=
  fun w => (guardedRowsSplit V F X L₂).symm (Sum.inr (Sum.inr w))

/-- **Aux 16 (the selector reservoir is a genuine subfamily of `Omega`).**
`08:46` writes `Sigma` as a *set* of columns of `B`, so its cardinality `S_0`
is the cardinality of its index carrier only if the inclusion is injective.
Injectivity is therefore carried explicitly, not assumed.  General. -/
theorem selIncl_injective (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (y₀ : Y) :
    Function.Injective (selIncl (q := q) F y₀) := by
  intro d d' h
  exact congrArg Prod.snd h

/-- **Aux 17 (the diagonal reservoir is a genuine subfamily of `Omega`).**  The
frozen `⨆_alpha` of `08:62--63` is a disjoint union, so `D_0 = q_2 |C_1|` only
because `(alpha, gamma) |-> (tail_{s+1}(gamma), d_{alpha,gamma})` is injective.
The proof reads the pair back off the zeroth bin, which exists because the
banked slot binding carries `s > 0`.  General. -/
theorem diagIncl_injective (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} :
    Function.Injective (diagIncl (q := q) (Y := Y) F) := by
  rintro ⟨α, γ⟩ ⟨α', γ'⟩ h
  have h2 : (diagIncl (q := q) (Y := Y) F (α, γ)).2 (p₀ F) =
      (diagIncl (q := q) (Y := Y) F (α', γ')).2 (p₀ F) := by rw [h]
  simpa [diagIncl, diagCol, diagTuple, Prod.ext_iff] using h2

/-- **Aux 18 (the three row reservoirs are genuine subfamilies of
`Rows(B)`).**  `08:20--24` writes the row carrier as a **disjoint** union, so
`X_0 = T_raw + V_raw + B_raw` counts each reservoir once; that is exactly the
injectivity of the three inclusions, recorded here rather than assumed.
General. -/
theorem rowIncl_injective (F : Stage1SlotBinding) (V X L₂ : Type*) :
    Function.Injective (tempIncl F V X L₂) ∧
      Function.Injective (vertIncl F V X L₂) ∧
      Function.Injective (blockIncl F V X L₂) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a b h
  · exact Sum.inl_injective ((guardedRowsSplit V F X L₂).symm.injective h)
  · exact Sum.inl_injective
      (Sum.inr_injective ((guardedRowsSplit V F X L₂).symm.injective h))
  · exact Sum.inr_injective
      (Sum.inr_injective ((guardedRowsSplit V F X L₂).symm.injective h))

/-- **The generic protected duplicate at the frozen carriers of `08:17--65`**,
with the seven multiplicities still explicit binders.  This is *not yet* the
`A` of `eq:protected-labelled-carriers`: the frozen `A` is this construction at
the seven numbers of `eq:protected-multiplicities` (`08:98--108`), which §3b
below pins as `protectedAFrozen`, with the pinning itself recorded by
`protectedA_at_frozen_multiplicities` and every carrier-cardinality, complexity
and mass fact restated there **about the pinned object**.  No consumer may read
the frozen masses off this free-width form: `unit_multiplicities_break_the_masses`
exhibits multiplicities at which they fail.  Consumes the banked `RawStageFour`
handoff by pin and adds no new construction. -/
def protectedA {F : Stage1SlotBinding} {q : ℕ} {V X L₂ Y : Type*}
    {u₀ uT uV uB w₀ wSg wD : ℕ}
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) (y₀ : Y) :
    ProtRows (RowsB F V X L₂) (TempCar F L₂) (VertCar F V X) (BlockCar F X)
        u₀ uT uV uB →
      ProtCols (Omega F q Y) (SelCar F q Y) (DiagCar F q Y) w₀ wSg wD → Bool :=
  protectedDup Bmat (tempIncl F V X L₂) (vertIncl F V X L₂) (blockIncl F V X L₂)
    (selIncl F y₀) (diagIncl F)

/-- **Aux 19 (`08:139--144` at the frozen carriers): `comp(A) = comp(B)`.**
The complexity-preservation display `eq:paper-protected-complexity-preservation`
holds for the pinned protected matrix as soon as the two base multiplicities
are positive, which `eq:protected-multiplicities` guarantees.  The injectivity
of the two representative selectors is again part of the conclusion.  General
in the seed, template and item carriers. -/
theorem D_protectedA {F : Stage1SlotBinding} {q : ℕ} {V X L₂ Y : Type*}
    [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] {u₀ uT uV uB w₀ wSg wD : ℕ}
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) (y₀ : Y) (hu : 0 < u₀)
    (hw : 0 < w₀) :
    Function.Injective
        (rowSection (Xr := RowsB F V X L₂) (Tm := TempCar F L₂)
          (Wv := VertCar F V X) (Wb := BlockCar F X) (u₀ := u₀) (uT := uT)
          (uV := uV) (uB := uB) hu) ∧
      Function.Injective
        (colSection (Om := Omega F q Y) (Sg := SelCar F q Y) (Dg := DiagCar F q Y)
          (w₀ := w₀) (wSg := wSg) (wD := wD) hw) ∧
      D (protectedA (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) (w₀ := w₀)
        (wSg := wSg) (wD := wD) Bmat y₀) = D Bmat :=
  D_protectedDup Bmat _ _ _ _ _ hu hw

/-! ## §3b  The pinned instance: `eq:protected-multiplicities` at the frozen
Section-8 reservoirs

`protectedA` above is the *generic* labelled duplication device: its seven
multiplicities are free.  `eq:protected-multiplicities` (`08:98--108`) does not
leave them free.  It fixes each one as a product of the raw cardinality
abbreviations of `eq:protected-raw-cardinality-abbreviations` (`08:68--78`),

>  `w_0 = 182 S_0 D_0`, `w_Sigma = M_0 D_0`, `w_D = M_0 S_0`,
>  `u_0 = (2^{22} - 4) T_raw V_raw B_raw`, `u_temp = 2 X_0 V_raw B_raw`,
>  `u_V = X_0 T_raw B_raw`, `u_B = X_0 T_raw V_raw`,

with **each multiplicity omitting its own reservoir's count** -- `w_0` carries
no `M_0`, `u_temp` carries no `T_raw`, and so on.  That omission is the whole
arithmetic content: it is what makes the two totals collapse to
`184 M_0 S_0 D_0` and `2^{22} X_0 T_raw V_raw B_raw` and the masses come out at
`91/92, 1/184, 1/184` and `1 - 2^{-20}, 2^{-21}, 2^{-22}, 2^{-22}`.

Everything below instantiates `protectedA` at exactly those seven numbers, read
off the **actual** Section-8 carriers of `08:17--65` by `Fintype.card`, and
restates the carrier cardinalities, the complexity preservation and the masses
as facts about *that* object.  No new mathematics enters: every statement is a
lemma of §2--§3 specialised, and the two base-multiplicity positivity side
conditions of `D_protectedA` are **discharged** from the reservoirs'
inhabitedness at legal parameters, never assumed. -/

/-- **Aux 19a (the three column reservoir counts are positive).**  `M_0`, `S_0`,
`D_0` of `eq:protected-raw-cardinality-abbreviations` are positive as soon as
the seed carrier is inhabited and the Stage-2 coordinate width is positive --
and `06:124` fixes `q_2` as a power of two at least `12 s N_E`, with
`card_edge_pos` giving `N_E > 0`, so `0 < q_2` is a consequence of the schedule
and not an extra demand.  General in `Y` and `q`. -/
theorem section8_col_counts_pos (F : Stage1SlotBinding) {q : ℕ} {Y : Type*}
    [Fintype Y] (hq : 0 < q) (y₀ : Y) :
    0 < Fintype.card (Omega F q Y) ∧
      0 < Fintype.card (SelCar F q Y) ∧
      0 < Fintype.card (DiagCar F q Y) :=
  ⟨Fintype.card_pos_iff.mpr ⟨(fun _ => y₀, fun _ => (⟨0, hq⟩, fun _ => y₀))⟩,
    Fintype.card_pos_iff.mpr ⟨fun _ => (⟨0, hq⟩, fun _ => y₀)⟩,
    Fintype.card_pos_iff.mpr ⟨(⟨0, hq⟩, fun _ => y₀)⟩⟩

/-- **Aux 19b (the four row reservoir counts are positive).**  `X_0`, `T_raw`,
`V_raw`, `B_raw` are positive as soon as the item, seed and Stage-2 column
carriers are inhabited and the bin count clears the frozen `s >= 4` of
`08:402`.  The `s >= 4` is genuinely needed and is not decoration: `W_B` is
indexed by `I_B = [4s] x [s-3]`, which is empty at `s <= 3`.  General. -/
theorem section8_row_counts_pos (F : Stage1SlotBinding) {V X L₂ : Type*}
    [Fintype V] [Fintype X] [Fintype L₂] (hs : 4 ≤ F.s) (v₀ : V) (x₀ : X)
    (l₀ : L₂) :
    0 < Fintype.card (RowsB F V X L₂) ∧
      0 < Fintype.card (TempCar F L₂) ∧
      0 < Fintype.card (VertCar F V X) ∧
      0 < Fintype.card (BlockCar F X) := by
  have hs4 : 0 < 4 * F.s := by omega
  have hs3 : 0 < F.s - 3 := by omega
  exact ⟨Fintype.card_pos_iff.mpr ⟨Sum.inl (⟨0, F.s_pos⟩, l₀)⟩,
    Fintype.card_pos_iff.mpr ⟨(⟨0, F.s_pos⟩, l₀)⟩,
    Fintype.card_pos_iff.mpr ⟨((⟨0, hs4⟩, v₀), x₀)⟩,
    Fintype.card_pos_iff.mpr ⟨((⟨0, hs4⟩, ⟨0, hs3⟩), x₀)⟩⟩

/-- `w_0 = 182 S_0 D_0` at the Section-8 column reservoirs (`08:99`). -/
abbrev wBaseF (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) [Fintype Y] : ℕ :=
  wBase (Fintype.card (SelCar F q Y)) (Fintype.card (DiagCar F q Y))

/-- `w_Sigma = M_0 D_0` at the Section-8 column reservoirs (`08:99`). -/
abbrev wSelF (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) [Fintype Y] : ℕ :=
  wSel (Fintype.card (Omega F q Y)) (Fintype.card (DiagCar F q Y))

/-- `w_D = M_0 S_0` at the Section-8 column reservoirs (`08:99`). -/
abbrev wDiagF (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) [Fintype Y] : ℕ :=
  wDiag (Fintype.card (Omega F q Y)) (Fintype.card (SelCar F q Y))

/-- `u_0 = (2^{22} - 4) T_raw V_raw B_raw` at the Section-8 row reservoirs
(`08:102`). -/
abbrev uBaseF (F : Stage1SlotBinding) (V X L₂ : Type*) [Fintype V] [Fintype X]
    [Fintype L₂] : ℕ :=
  uBase (Fintype.card (TempCar F L₂)) (Fintype.card (VertCar F V X))
    (Fintype.card (BlockCar F X))

/-- `u_temp = 2 X_0 V_raw B_raw` at the Section-8 row reservoirs (`08:103`). -/
abbrev uTempF (F : Stage1SlotBinding) (V X L₂ : Type*) [Fintype V] [Fintype X]
    [Fintype L₂] : ℕ :=
  uTemp (Fintype.card (RowsB F V X L₂)) (Fintype.card (VertCar F V X))
    (Fintype.card (BlockCar F X))

/-- `u_V = X_0 T_raw B_raw` at the Section-8 row reservoirs (`08:105`). -/
abbrev uVertF (F : Stage1SlotBinding) (V X L₂ : Type*) [Fintype V] [Fintype X]
    [Fintype L₂] : ℕ :=
  uVert (Fintype.card (RowsB F V X L₂)) (Fintype.card (TempCar F L₂))
    (Fintype.card (BlockCar F X))

/-- `u_B = X_0 T_raw V_raw` at the Section-8 row reservoirs (`08:106`). -/
abbrev uBlockF (F : Stage1SlotBinding) (V X L₂ : Type*) [Fintype V] [Fintype X]
    [Fintype L₂] : ℕ :=
  uBlock (Fintype.card (RowsB F V X L₂)) (Fintype.card (TempCar F L₂))
    (Fintype.card (VertCar F V X))

/-- `Cols(A)` of `eq:protected-labelled-carriers` at the pinned multiplicities. -/
abbrev ProtColsFrozen (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) [Fintype Y] :
    Type _ :=
  ProtCols (Omega F q Y) (SelCar F q Y) (DiagCar F q Y) (wBaseF F q Y)
    (wSelF F q Y) (wDiagF F q Y)

/-- `Rows(A)` of `eq:protected-labelled-carriers` at the pinned multiplicities. -/
abbrev ProtRowsFrozen (F : Stage1SlotBinding) (V X L₂ : Type*) [Fintype V]
    [Fintype X] [Fintype L₂] : Type _ :=
  ProtRows (RowsB F V X L₂) (TempCar F L₂) (VertCar F V X) (BlockCar F X)
    (uBaseF F V X L₂) (uTempF F V X L₂) (uVertF F V X L₂) (uBlockF F V X L₂)

/-- **The protected matrix `A` of `eq:protected-labelled-carriers`**, at the
frozen carriers of `08:17--65` **and** at the frozen multiplicities of
`eq:protected-multiplicities` (`08:98--108`).  This -- not `protectedA` -- is
the object `N = A^T` of `08:147` transposes and `thm:dense-stage4` speaks
about.  Nothing new is constructed: it is `protectedA` at the seven pinned
numbers. -/
def protectedAFrozen {F : Stage1SlotBinding} {q : ℕ} {V X L₂ Y : Type*}
    [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) (y₀ : Y) :
    ProtRowsFrozen F V X L₂ → ProtColsFrozen F q Y → Bool :=
  protectedA (u₀ := uBaseF F V X L₂) (uT := uTempF F V X L₂)
    (uV := uVertF F V X L₂) (uB := uBlockF F V X L₂) (w₀ := wBaseF F q Y)
    (wSg := wSelF F q Y) (wD := wDiagF F q Y) Bmat y₀

/-- **The pinning promised by `protectedA`: `eq:protected-multiplicities`
spelled out at the Section-8 reservoirs.**  Each of the seven pinned widths is
literally the frozen formula of `08:99--107` evaluated at the reservoir counts
of `eq:protected-raw-cardinality-abbreviations`, and each omits its own
reservoir's count -- `w_0` has no `M_0` factor, `w_Sigma` no `S_0`, `w_D` no
`D_0`, `u_0` no `X_0`, `u_temp` no `T_raw`, `u_V` no `V_raw`, `u_B` no `B_raw`.
Stated so that a reader can check the seven products against the frozen display
without unfolding a definition.  General. -/
theorem protectedA_at_frozen_multiplicities (F : Stage1SlotBinding) (q : ℕ)
    (V X L₂ Y : Type*) [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] :
    wBaseF F q Y =
        182 * Fintype.card (SelCar F q Y) * Fintype.card (DiagCar F q Y) ∧
      wSelF F q Y =
        Fintype.card (Omega F q Y) * Fintype.card (DiagCar F q Y) ∧
      wDiagF F q Y =
        Fintype.card (Omega F q Y) * Fintype.card (SelCar F q Y) ∧
      uBaseF F V X L₂ =
        (2 ^ 22 - 4) * Fintype.card (TempCar F L₂) *
          Fintype.card (VertCar F V X) * Fintype.card (BlockCar F X) ∧
      uTempF F V X L₂ =
        2 * Fintype.card (RowsB F V X L₂) * Fintype.card (VertCar F V X) *
          Fintype.card (BlockCar F X) ∧
      uVertF F V X L₂ =
        Fintype.card (RowsB F V X L₂) * Fintype.card (TempCar F L₂) *
          Fintype.card (BlockCar F X) ∧
      uBlockF F V X L₂ =
        Fintype.card (RowsB F V X L₂) * Fintype.card (TempCar F L₂) *
          Fintype.card (VertCar F V X) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Aux 19c (the pinned base column multiplicity is positive).**  Discharged,
not assumed: `w_0 = 182 S_0 D_0` and both reservoir counts are positive at legal
parameters. -/
theorem wBaseF_pos (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} [Fintype Y]
    (hq : 0 < q) (y₀ : Y) : 0 < wBaseF F q Y := by
  obtain ⟨-, hS, hD⟩ := section8_col_counts_pos F hq y₀
  exact Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 182) hS) hD

/-- **Aux 19d (the pinned base row multiplicity is positive).**  Discharged,
not assumed: `u_0 = (2^{22} - 4) T_raw V_raw B_raw` with all three reservoir
counts positive and `2^{22} - 4 > 0`. -/
theorem uBaseF_pos (F : Stage1SlotBinding) {V X L₂ : Type*} [Fintype V]
    [Fintype X] [Fintype L₂] (hs : 4 ≤ F.s) (v₀ : V) (x₀ : X) (l₀ : L₂) :
    0 < uBaseF F V X L₂ := by
  obtain ⟨-, hT, hV, hB⟩ := section8_row_counts_pos F hs v₀ x₀ l₀
  have h4 : 0 < 2 ^ 22 - 4 := by norm_num
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos h4 hT) hV) hB

/-- **Aux 19e (all seven pinned multiplicities are positive).**  The frozen
`A` is a genuine duplication at legal parameters: every reservoir really is
copied, so no labelled block of `eq:protected-labelled-carriers` is empty and
the mass readouts below are readouts of a nonempty carrier. -/
theorem protectedAFrozen_multiplicities_pos (F : Stage1SlotBinding) {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂) :
    0 < wBaseF F q Y ∧ 0 < wSelF F q Y ∧ 0 < wDiagF F q Y ∧
      0 < uBaseF F V X L₂ ∧ 0 < uTempF F V X L₂ ∧ 0 < uVertF F V X L₂ ∧
      0 < uBlockF F V X L₂ := by
  obtain ⟨hM, hS, hD⟩ := section8_col_counts_pos F hq y₀
  obtain ⟨hX, hT, hV, hB⟩ := section8_row_counts_pos (V := V) (X := X) (L₂ := L₂)
    F hs v₀ x₀ l₀
  exact ⟨wBaseF_pos F hq y₀, Nat.mul_pos hM hD, Nat.mul_pos hM hS,
    uBaseF_pos F hs v₀ x₀ l₀,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) hX) hV) hB,
    Nat.mul_pos (Nat.mul_pos hX hT) hB, Nat.mul_pos (Nat.mul_pos hX hT) hV⟩

/-- **Aux 19f (`08:96--97` at the pinned instance).**  The pinned `A` still
ignores the reservoir label and the multiplicity index: its value at a labelled
row and a labelled column is the entry of `B` at the forgotten pair.  Pinning
the widths changes the carriers, never the rule. -/
@[simp] theorem protectedAFrozen_apply {F : Stage1SlotBinding} {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) (y₀ : Y)
    (r : ProtRowsFrozen F V X L₂) (c : ProtColsFrozen F q Y) :
    protectedAFrozen Bmat y₀ r c =
      Bmat (rowForget (tempIncl F V X L₂) (vertIncl F V X L₂) (blockIncl F V X L₂) r)
        (colForget (selIncl F y₀) (diagIncl F) c) := rfl

/-- **Aux 19g (`08:139`: the pinned `A` restricts to `B` on the nose).**  The
two base-reservoir representatives, at multiplicity index `0`, carry exactly the
entries of `B` -- so "selecting one representative of every underlying row and
column projects `A` to `B`" is an equation about the pinned object, not only
about the generic device.  The positivity the sections need is the discharged
`uBaseF_pos` / `wBaseF_pos`, not a binder. -/
theorem protectedAFrozen_restricts_to_B {F : Stage1SlotBinding} {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂)
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) (r : RowsB F V X L₂)
    (c : Omega F q Y) :
    protectedAFrozen Bmat y₀
        (rowSection (Xr := RowsB F V X L₂) (Tm := TempCar F L₂)
          (Wv := VertCar F V X) (Wb := BlockCar F X) (uT := uTempF F V X L₂)
          (uV := uVertF F V X L₂) (uB := uBlockF F V X L₂)
          (uBaseF_pos F hs v₀ x₀ l₀) r)
        (colSection (Om := Omega F q Y) (Sg := SelCar F q Y)
          (Dg := DiagCar F q Y) (wSg := wSelF F q Y) (wD := wDiagF F q Y)
          (wBaseF_pos F hq y₀) c) = Bmat r c := rfl

/-- **Aux 19h (`eq:protected-carrier-cardinalities` at the pinned instance).**
The two frozen totals `|Cols(A)| = 184 M_0 S_0 D_0` and
`|Rows(A)| = 2^{22} X_0 T_raw V_raw B_raw` (`08:110--122`) are facts about the
`Fintype.card` of the carriers `protectedAFrozen` is actually defined on.
Obtained from the already-general `card_protected_carriers`; nothing is
recomputed. -/
theorem card_ProtColsFrozen (F : Stage1SlotBinding) (q : ℕ) (Y : Type*)
    [Fintype Y] :
    Fintype.card (ProtColsFrozen F q Y) =
      184 * (Fintype.card (Omega F q Y) * Fintype.card (SelCar F q Y) *
        Fintype.card (DiagCar F q Y)) := by
  rw [card_ProtCols]
  exact protected_cols_card_identity _ _ _

theorem card_ProtRowsFrozen (F : Stage1SlotBinding) (V X L₂ : Type*) [Fintype V]
    [Fintype X] [Fintype L₂] :
    Fintype.card (ProtRowsFrozen F V X L₂) =
      2 ^ 22 * (Fintype.card (RowsB F V X L₂) * Fintype.card (TempCar F L₂) *
        Fintype.card (VertCar F V X) * Fintype.card (BlockCar F X)) := by
  rw [card_ProtRows]
  exact protected_rows_card_identity _ _ _ _

theorem card_protectedAFrozen_carriers (F : Stage1SlotBinding) (q : ℕ)
    (V X L₂ Y : Type*) [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] :
    Fintype.card (ProtColsFrozen F q Y) =
        184 * (Fintype.card (Omega F q Y) * Fintype.card (SelCar F q Y) *
          Fintype.card (DiagCar F q Y)) ∧
      Fintype.card (ProtRowsFrozen F V X L₂) =
        2 ^ 22 * (Fintype.card (RowsB F V X L₂) * Fintype.card (TempCar F L₂) *
          Fintype.card (VertCar F V X) * Fintype.card (BlockCar F X)) :=
  ⟨card_ProtColsFrozen F q Y, card_ProtRowsFrozen F V X L₂⟩

/-- **Aux 19i (`08:139--144` at the pinned instance): `comp(A) = comp(B)` with
the side conditions discharged.**  `D_protectedA` needed `0 < u_0` and
`0 < w_0` as binders; at the pinned multiplicities both are theorems, so the
complexity preservation of `eq:paper-protected-complexity-preservation` holds
for the frozen `A` outright at legal parameters.  The injectivity of the two
representative selectors is again part of the conclusion. -/
theorem D_protectedAFrozen {F : Stage1SlotBinding} {q : ℕ} {V X L₂ Y : Type*}
    [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s)
    (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂)
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) :
    Function.Injective
        (rowSection (Xr := RowsB F V X L₂) (Tm := TempCar F L₂)
          (Wv := VertCar F V X) (Wb := BlockCar F X) (uT := uTempF F V X L₂)
          (uV := uVertF F V X L₂) (uB := uBlockF F V X L₂)
          (uBaseF_pos F hs v₀ x₀ l₀)) ∧
      Function.Injective
        (colSection (Om := Omega F q Y) (Sg := SelCar F q Y)
          (Dg := DiagCar F q Y) (wSg := wSelF F q Y) (wD := wDiagF F q Y)
          (wBaseF_pos F hq y₀)) ∧
      D (protectedAFrozen Bmat y₀) = D Bmat :=
  D_protectedA Bmat y₀ (uBaseF_pos F hs v₀ x₀ l₀) (wBaseF_pos F hq y₀)

/-- **Aux 19j (`08:123--126`: the exact column masses of the pinned `A`).**
The base, selector and diagonal column masses of the **built** object -- each
reservoir's labelled column count divided by `Fintype.card (Cols(A))` -- are
exactly `91/92`, `1/184`, `1/184`, and the two protected reservoirs together
carry exactly `tau = 1/92` (`08:133`, cross-pinned to `eq:fixed-protected-masses`
at `06:130--137` by `massConstants_agree`).  Nothing here is at abstract
cardinalities: the denominator is the cardinality of the carrier
`protectedAFrozen` is defined on. -/
theorem protectedAFrozen_col_masses (F : Stage1SlotBinding) {q : ℕ} {Y : Type*}
    [Fintype Y] (hq : 0 < q) (y₀ : Y) :
    ((Fintype.card (Omega F q Y) * wBaseF F q Y : ℕ) : ℚ) /
          ((Fintype.card (ProtColsFrozen F q Y) : ℕ) : ℚ) = 91 / 92 ∧
      ((Fintype.card (SelCar F q Y) * wSelF F q Y : ℕ) : ℚ) /
          ((Fintype.card (ProtColsFrozen F q Y) : ℕ) : ℚ) = muMass ∧
      ((Fintype.card (DiagCar F q Y) * wDiagF F q Y : ℕ) : ℚ) /
          ((Fintype.card (ProtColsFrozen F q Y) : ℕ) : ℚ) = muMass ∧
      ((Fintype.card (SelCar F q Y) * wSelF F q Y +
            Fintype.card (DiagCar F q Y) * wDiagF F q Y : ℕ) : ℚ) /
          ((Fintype.card (ProtColsFrozen F q Y) : ℕ) : ℚ) = tauMass := by
  obtain ⟨hM, hS, hD⟩ := section8_col_counts_pos F hq y₀
  rw [card_ProtColsFrozen F q Y]
  exact protected_col_masses hM hS hD

/-- **Aux 19k (`08:127--130`: the exact row masses of the pinned `A`).**  The
base, template, vertex-source and blocker-source row masses of the **built**
object are exactly `1 - 2^{-20}`, `2^{-21}`, `2^{-22}`, `2^{-22}`, and the three
protected reservoirs together carry exactly `sigma = 2^{-20}` (`08:135`).
Denominator again the actual `Fintype.card (Rows(A))`. -/
theorem protectedAFrozen_row_masses (F : Stage1SlotBinding) {V X L₂ : Type*}
    [Fintype V] [Fintype X] [Fintype L₂] (hs : 4 ≤ F.s) (v₀ : V) (x₀ : X)
    (l₀ : L₂) :
    ((Fintype.card (RowsB F V X L₂) * uBaseF F V X L₂ : ℕ) : ℚ) /
          ((Fintype.card (ProtRowsFrozen F V X L₂) : ℕ) : ℚ) = 1 - sigmaMass ∧
      ((Fintype.card (TempCar F L₂) * uTempF F V X L₂ : ℕ) : ℚ) /
          ((Fintype.card (ProtRowsFrozen F V X L₂) : ℕ) : ℚ) = nuTemp ∧
      ((Fintype.card (VertCar F V X) * uVertF F V X L₂ : ℕ) : ℚ) /
          ((Fintype.card (ProtRowsFrozen F V X L₂) : ℕ) : ℚ) = nuSrc ∧
      ((Fintype.card (BlockCar F X) * uBlockF F V X L₂ : ℕ) : ℚ) /
          ((Fintype.card (ProtRowsFrozen F V X L₂) : ℕ) : ℚ) = nuSrc ∧
      ((Fintype.card (TempCar F L₂) * uTempF F V X L₂ +
            (Fintype.card (VertCar F V X) * uVertF F V X L₂ +
              Fintype.card (BlockCar F X) * uBlockF F V X L₂) : ℕ) : ℚ) /
          ((Fintype.card (ProtRowsFrozen F V X L₂) : ℕ) : ℚ) = sigmaMass := by
  obtain ⟨hX, hT, hV, hB⟩ := section8_row_counts_pos F hs v₀ x₀ l₀
  rw [card_ProtRowsFrozen F V X L₂]
  exact protected_row_masses hX hT hV hB

/-- **Non-vacuity 1b (the pinned carriers are nondegenerate at legal
parameters).**  `eq:protected-carrier-cardinalities` forces at least `184`
labelled columns and at least `2^{22}` labelled rows, so the pinned `A` is not
inhabited at a collapsed instance: the protection really is a `184`-fold and a
`2^{22}`-fold blow-up of the raw carriers, which is what the frozen masses
`1/184` and `2^{-22}` mean. -/
theorem protectedAFrozen_carriers_nondegenerate (F : Stage1SlotBinding) {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y]
    (hq : 0 < q) (hs : 4 ≤ F.s) (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂) :
    184 ≤ Fintype.card (ProtColsFrozen F q Y) ∧
      2 ^ 22 ≤ Fintype.card (ProtRowsFrozen F V X L₂) := by
  obtain ⟨hM, hS, hD⟩ := section8_col_counts_pos F hq y₀
  obtain ⟨hX, hT, hV, hB⟩ := section8_row_counts_pos (V := V) (X := X) (L₂ := L₂)
    F hs v₀ x₀ l₀
  obtain ⟨hc, hr⟩ := card_protectedAFrozen_carriers F q V X L₂ Y
  constructor
  · rw [hc]
    exact Nat.le_mul_of_pos_right 184
      (Nat.mul_pos (Nat.mul_pos hM hS) hD)
  · rw [hr]
    exact Nat.le_mul_of_pos_right (2 ^ 22)
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hX hT) hV) hB)

/-! ### The transposed protected matrix `N`, and the block constants -/

/-- `N = A^T` (`08:147`).  The row-deletion tolerance `eta_R` for `N`
therefore acts on **columns** of `A`, whereas `eta_C` acts on **rows** of `A`;
`08:154--156` fixes that convention for the whole section, and
`transposeN_orientation` below is where it is recorded. -/
def transposeN {Rw Cl : Type*} (Amat : Rw → Cl → Bool) : Cl → Rw → Bool :=
  fun c r => Amat r c

/-- **Aux 20 (`08:154--156`: the fixed orientation convention).**  Transposing
exchanges the two carriers on the nose, so a row of `N` is a column of `A` and
a column of `N` is a row of `A`.  Recorded as an equation rather than as prose,
because every density in `thm:dense-stage4` is read through it. -/
@[simp] theorem transposeN_apply {Rw Cl : Type*} (Amat : Rw → Cl → Bool)
    (c : Cl) (r : Rw) : transposeN Amat c r = Amat r c := rfl

/-- **Aux 21 (`08:143`: transposition preserves complexity).**  `comp(N)` and
`comp(A)` agree, so the frozen `comp(A) = comp(B)` transports to `N` without a
second argument.  Proved from the vendored `NPCC.comp_transpose`
(`lem:transposeComp`), consumed by pin. -/
theorem D_transposeN {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Amat : Rw → Cl → Bool) : D (transposeN Amat) = D Amat :=
  comp_transpose Amat

/-- `D_2 = B_cap + log_2 q_2` (`08:152`), with `B_cap = D + a` (`07:156`).
Both are the banked public integers, consumed by pin. -/
def dTwoBlock (Dsrc a r₂ : ℕ) : ℕ := dTwo (bCap Dsrc a) r₂

/-- `C = D + a + log_2 q_2 + log_2 s + 1 = D_2 + log_2 s + 1` (`08:149--152`),
the exact `NO`-case complexity target of `thm:dense-stage4`. -/
def cBlock (Dsrc a r₂ wS : ℕ) : ℕ := dTwoBlock Dsrc a r₂ + wS + 1

/-- **Aux 22 (`08:149--152`: the two frozen readings of `C` agree).**  The
displayed chain `C = D + a + log_2 q_2 + log_2 s + 1 = D_2 + log_2 s + 1` is an
identity of public integers, and it is the banked `outerBudget` reading of
`07:665` (`C = D + K + 1`) on the nose, so `rawNoExact` and `cBlock` name the
same number.  General. -/
theorem cBlock_eq (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) (Dsrc : ℕ) :
    cBlock Dsrc F.a W.r₂ S.wS = Dsrc + F.a + W.r₂ + S.wS + 1 ∧
      cBlock Dsrc F.a W.r₂ S.wS = Dsrc + outerBudget F W S + 1 ∧
      cBlock Dsrc F.a W.r₂ S.wS = dTwoBlock Dsrc F.a W.r₂ + S.wS + 1 := by
  refine ⟨?_, ?_, rfl⟩ <;>
    · simp only [cBlock, dTwoBlock, dTwo, bCap, outerBudget]
      try omega

/-- **Aux 23 (`08:325`: the contradiction hypothesis's exact value).**  The
frozen proof of `thm:dense-stage4` assumes `cost(P) <= C - 1 = log_2 s + D_2`;
this records that `C - 1` is that number, with no truncated subtraction, and
that `C` is positive so the subtraction is exact.  General. -/
theorem cBlock_pred (Dsrc a r₂ wS : ℕ) :
    0 < cBlock Dsrc a r₂ wS ∧
      cBlock Dsrc a r₂ wS - 1 = wS + dTwoBlock Dsrc a r₂ ∧
      cBlock Dsrc a r₂ wS = (cBlock Dsrc a r₂ wS - 1) + 1 := by
  simp only [cBlock, dTwoBlock, dTwo, bCap]
  refine ⟨by omega, by omega, by omega⟩

/-- **Aux 24 (the block's budget identities, consumed by pin).**  The two
promise budgets `exp:E-06-yes` and `exp:E-06-no-upper` that Section 8 inherits
are the banked `RawStageFour.raw_budget_identities`; nothing is restated, and
the `NO` value they produce is `cBlock`.  General in `Y` and `D`. -/
theorem block_budget_identities (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) (Yb Dsrc : ℕ) :
    (Yb + F.a + W.r₂ + S.wS = Yb + outerBudget F W S ∧
        Dsrc + (F.a + 1) + W.r₂ + S.wS = Dsrc + outerBudget F W S + 1) ∧
      Dsrc + outerBudget F W S + 1 = cBlock Dsrc F.a W.r₂ S.wS :=
  ⟨raw_budget_identities F W S Yb Dsrc, (cBlock_eq F W S Dsrc).2.1.symm⟩

/-- **Aux 25 (`08:143` transported: the whole `comp` chain of the block).**
`comp(N) = comp(A) = comp(B)`, so the `NO`-case exact value the block is
charged with proving about `N` is literally the postponed `rawNoExact` of
`07:665` about `B`.  Nothing here asserts that value: it is a conditional. -/
theorem transposedA_comp_chain {F : Stage1SlotBinding} {q : ℕ}
    {V X L₂ Y : Type*} [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] {u₀ uT uV uB w₀ wSg wD : ℕ}
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) (y₀ : Y) (hu : 0 < u₀)
    (hw : 0 < w₀) (W : StageTwoWidths) (S : StageThreeScale) (Dsrc : ℕ)
    (hno : rawNoExact Bmat Dsrc (outerBudget F W S)) :
    D (transposeN (protectedA (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB)
        (w₀ := w₀) (wSg := wSg) (wD := wD) Bmat y₀)) =
      cBlock Dsrc F.a W.r₂ S.wS := by
  rw [D_transposeN, (D_protectedA Bmat y₀ hu hw).2.2]
  rw [show D Bmat = Dsrc + outerBudget F W S + 1 from hno]
  exact (cBlock_eq F W S Dsrc).2.1.symm

/-! ## §4  The low-row, one-bit-down profile (`sec:raw-low-profile`)

`08:161--191` fixes the schedule of `lem:raw-low-profile` and `08:184--191`
its two finite comparisons; `08:193--216` states the lemma and `08:218--257`
proves it.  Everything below is at the frozen values, with `y` left an explicit
binder exactly as `08:175` and `08:213` leave it (the reader instantiates
`y = 3/5`).  Real exponents are written with natural powers, so
`2^{-b} = 1 / 2^b` on the nose and no `rpow` enters where the frozen text uses
an integer exponent. -/

/-- `x_N = 1/16` (`08:164`), also `06:131`. -/
noncomputable def xN : ℝ := 1 / 16

/-- `x_T = 2^{-b_T}` (`08:166`), the auxiliary Stage-3 depth density. -/
noncomputable def xTdepth (bT : ℕ) : ℝ := 1 / 2 ^ bT

/-- `tau = 1/92` in `ℝ` (`08:133`), the protected non-base column mass. -/
noncomputable def tauR : ℝ := 1 / 92

/-- `sigma = 2^{-20}` in `ℝ` (`08:135`), the protected non-base row mass. -/
noncomputable def sigmaR : ℝ := 1 / 2 ^ 20

/-- **Aux 26 (the two mass constants agree with `§2`).**  The `ℝ` constants used
by the profile schedule are the casts of the `ℚ` masses proved exact in
`protected_col_masses` / `protected_row_masses`; there are not two `tau`s. -/
theorem massConstants_agree : ((tauMass : ℚ) : ℝ) = tauR ∧ ((sigmaMass : ℚ) : ℝ) = sigmaR := by
  constructor <;> simp [tauMass, sigmaMass, tauR, sigmaR]

/-- `I_j = s / 2^j` (`08:170`), the Stage-3 width at rung `j`. -/
noncomputable def widthI (s j : ℕ) : ℝ := (s : ℝ) / 2 ^ j

/-- `p_j = 9 I_j / 16` (`08:171`), the number of blocks the rung must retain. -/
noncomputable def blockTarget (s j : ℕ) : ℝ := 9 * widthI s j / 16

/-- `x_j = I_j x_T` (`08:172`), the row density at rung `j`. -/
noncomputable def rowDensity (s j bT : ℕ) : ℝ := widthI s j * xTdepth bT

/-- `h_j^{raw} = 2^{-2^{0.49 sqrt(log_2 I_j)}}` (`08:173--174`), written as a
function of the width so that the rung comparison is a monotonicity statement
rather than three separate numbers.  The two outer powers are real exponents,
so both are `rpow`; the frozen text uses the real square root here and only
here. -/
noncomputable def hRawSchedule (I : ℝ) : ℝ :=
  (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (Real.logb 2 I))))

/-- `r_j = (y/2^j - sigma)/(1 - sigma)` (`08:175`), the residual column density
after the protected non-base row reservoirs are discarded. -/
noncomputable def rTail (y : ℝ) (j : ℕ) : ℝ := (y / 2 ^ j - sigmaR) / (1 - sigmaR)

/-- `beta_j^{raw} = (ceil(r_j (|T| + |W_V| + |W_B|)) - |W_V| - |W_B|)/|T|`
(`08:176--181`), the density left among raw template rows in the worst case in
which every protected row survives. -/
noncomputable def betaRaw (rj : ℝ) (T₀ V₀ B₀ : ℕ) : ℝ :=
  ((⌈rj * ((T₀ : ℝ) + (V₀ : ℝ) + (B₀ : ℝ))⌉₊ : ℝ) - (V₀ : ℝ) - (B₀ : ℝ)) / (T₀ : ℝ)

/-- **`eq:raw-low-gates` (`08:184--191`)**, the two finite comparisons the
admissibility predicate binds for `lem:raw-low-profile`.  Transcribed as a
predicate and never asserted. -/
def rawLowGates (s bT T₀ V₀ B₀ : ℕ) (y : ℝ) : Prop :=
  hRawSchedule (widthI s 2) ≤ (xN - tauR) / (1 - tauR) ∧
    ∀ j : ℕ, j ≤ 2 →
      blockTarget s j ≤
        (⌈(s : ℝ) * (betaRaw (rTail y j) T₀ V₀ B₀ - rowDensity s j bT) /
          (1 - rowDensity s j bT)⌉₊ : ℝ)

/-- **Aux 27 (the rung widths decrease).**  `I_2 ≤ I_j` for `j ≤ 2`, and
`1 ≤ I_2` as soon as `4 ≤ s`.  General. -/
theorem widthI_rungs {s : ℕ} (hs : 4 ≤ s) {j : ℕ} (hj : j ≤ 2) :
    1 ≤ widthI s 2 ∧ widthI s 2 ≤ widthI s j := by
  have hs' : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ 2 := by
    apply pow_le_pow_right₀ (by norm_num) hj
  have hjpos : (0 : ℝ) < 2 ^ j := by positivity
  constructor
  · rw [widthI, le_div_iff₀ (by norm_num : (0:ℝ) < 2 ^ 2)]
    norm_num
    linarith
  · rw [widthI, widthI, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2 ^ 2) hjpos]
    have : (0:ℝ) ≤ (s:ℝ) := by linarith
    nlinarith

/-- **Aux 28 (`08:223--227`: the rung densities are antitone in the width).**
`h^{raw}` is antitone on `[1, ∞)`, which is exactly why the single gate at
`I_2` covers all three rungs.  General in the two widths. -/
theorem hRawSchedule_antitone {I I' : ℝ} (hI : 1 ≤ I) (hII : I ≤ I') :
    hRawSchedule I' ≤ hRawSchedule I := by
  have h0 : (0 : ℝ) < I := lt_of_lt_of_le zero_lt_one hI
  have hlog : Real.logb 2 I ≤ Real.logb 2 I' :=
    Real.logb_le_logb_of_le (by norm_num) h0 hII
  have hsqrt : Real.sqrt (Real.logb 2 I) ≤ Real.sqrt (Real.logb 2 I') :=
    Real.sqrt_le_sqrt hlog
  have hmul : (49 / 100 : ℝ) * Real.sqrt (Real.logb 2 I) ≤
      (49 / 100 : ℝ) * Real.sqrt (Real.logb 2 I') := by linarith
  have hexp : (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (Real.logb 2 I)) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (Real.logb 2 I')) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hmul
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr (by linarith)

/-- **Aux 29 (`08:223--227`: the first gate covers every rung).**  The single
comparison `(x_N - tau)/(1 - tau) >= h_2^{raw}` of `eq:raw-low-gates` gives
`(x_N - tau)/(1 - tau) >= h_j^{raw}` for `j = 0, 1, 2`, which is the frozen
chain `>= h_2^{raw} >= h_j^{raw}`.  Requires `4 <= s`, the frozen power-of-two
floor at which `I_2 = s/4` is still a legal width. -/
theorem rawLowGates_cover_rungs {s bT T₀ V₀ B₀ : ℕ} (hs : 4 ≤ s) {y : ℝ}
    (hg : rawLowGates s bT T₀ V₀ B₀ y) {j : ℕ} (hj : j ≤ 2) :
    hRawSchedule (widthI s j) ≤ (xN - tauR) / (1 - tauR) :=
  le_trans (hRawSchedule_antitone (widthI_rungs hs hj).1 (widthI_rungs hs hj).2) hg.1

/-- **Aux 30 (`08:234--239`: the elementary extremal bound).**  If `g` of the
`s` Stage-3 blocks retain at least an `x` fraction of their rows, the extremal
bound `beta <= (g + (s-g)x)/s` together with the frozen ceiling gate
`p <= ceil(s(beta - x)/(1-x))` forces `g >= p`.  This is the block's own
arithmetic, proved in full generality in `s`, `g`, `beta`, `x` and `p`; it is
the step at which the schedule turns a density statement into a **count** of
blocks. -/
theorem block_count_of_extremal {s g : ℕ} (hs : 0 < s) {β x p : ℝ} (hx1 : x < 1)
    (hextremal : β ≤ ((g : ℝ) + ((s : ℝ) - (g : ℝ)) * x) / (s : ℝ))
    (hgate : p ≤ (⌈(s : ℝ) * (β - x) / (1 - x)⌉₊ : ℝ)) :
    p ≤ (g : ℝ) := by
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h1 : β * (s : ℝ) ≤ (g : ℝ) + ((s : ℝ) - (g : ℝ)) * x :=
    (le_div_iff₀ hs').mp hextremal
  have hx0 : (0 : ℝ) < 1 - x := by linarith
  have h3 : (s : ℝ) * (β - x) / (1 - x) ≤ (g : ℝ) := by
    rw [div_le_iff₀ hx0]
    nlinarith
  have h4 : (⌈(s : ℝ) * (β - x) / (1 - x)⌉₊ : ℝ) ≤ (g : ℝ) := by
    exact_mod_cast Nat.ceil_le.mpr h3
  linarith

/-- **Aux 31 (`08:252--256`: taking the minimum over `j = 0, 1, 2`).**  The
three frozen rung bounds `j + comp<N, 1, x_N, y/2^j> >= n` are exactly the
three-rung readout `n <= Lambda_N(1, x_N, y)`.  Proved through the banked
`TwoCopyLadder.le_LambdaGE_iff`, consumed by pin.  General in the matrix, the
row density and `y`. -/
theorem lowProfile_of_frozen_rungs {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (n : ℕ) (x y : ℝ)
    (hrung : ∀ j : ℕ, j ≤ 2 →
      n ≤ j + Dfamily (interlaceFun Nmat 1) (bracketGE Rw Cl 1 x (y / 2 ^ j))) :
    n ≤ LambdaGE Nmat 1 x y := by
  rw [TwoCopyLadder.le_LambdaGE_iff]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hrung 0 (by norm_num)
  · simpa using hrung 1 (by norm_num)
  · have h := hrung 2 (by norm_num)
    norm_num at h ⊢
    exact h

/-- **`lem:raw-low-profile` (`08:193--216`), as a statement with its hypothesis
battery.**

The frozen lemma reads: under `Admissible(Public, Pi, T_lev)` and
`NoCert(Public)` -- which bind "the power and divisibility data for `s` and
every comparison in `eq:raw-low-gates`", and through which the Stage-1 and
Stage-2 lemmas supply `eq:stage1-robust-certificate` and
`eq:stage2-two-depth-certificate` -- the transposed protected matrix satisfies
`Lambda_N(1, x_N, y) >= C - 1`.

`Admissible`, `NoCert` and `LevelStep` have no Lean declaration yet, so they
are carried as **explicit propositional binders**, never as silent axioms and
never as a premise bundle with derived fields.  The three deeper rung outputs
of `08:240--251` -- the projection to `p_j` blocks followed by the inherited
General Hard Seed Lemma at width `I_j` -- are the named hypothesis `hrung`.
What this theorem itself supplies is the frozen closing step `08:252--256`,
"Taking the minimum over `j = 0, 1, 2`".

The `4 <= s` and gate hypotheses are not decoration: `rawLowGates_cover_rungs`
is exactly the frozen first paragraph of the proof, and it is what the caller
must discharge before `hrung` is even meaningful at `j = 0, 1`. -/
theorem rawLowProfile {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (Cval s bT T₀ V₀ B₀ : ℕ) (y : ℝ)
    (Admissible NoCert : Prop) (_hAdm : Admissible) (_hNo : NoCert)
    (_hs : 4 ≤ s) (_hgates : rawLowGates s bT T₀ V₀ B₀ y)
    (hrung : Admissible → NoCert → ∀ j : ℕ, j ≤ 2 →
      Cval - 1 ≤ j + Dfamily (interlaceFun Nmat 1) (bracketGE Rw Cl 1 xN (y / 2 ^ j))) :
    Cval - 1 ≤ LambdaGE Nmat 1 xN y :=
  lowProfile_of_frozen_rungs Nmat (Cval - 1) xN y (hrung _hAdm _hNo)

/-- **Statement pole for `lem:raw-low-profile`.**  The conclusion is not
automatic: at the legal constant matrix over two-element carriers the whole
three-rung readout is `0`, so `Lambda >= C - 1` fails for every `C >= 2`.  The
lower bound therefore has to come from the rung hypotheses; it cannot be read
off the shape of `Lambda`. -/
theorem rawLowProfile_not_automatic :
    LambdaGE (fun (_ : Bool) (_ : Bool) => false) 1 xN (3 / 5) = 0 := by
  have hzero : ∀ z : ℝ, 0 < z → z ≤ 1 →
      Dfamily (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
        (bracketGE Bool Bool 1 xN z) = 0 := by
    intro z _ hz1
    obtain ⟨RC, hRC⟩ :=
      bracketGE.nonempty (X := Bool) (Y := Bool) 1 xN z (by norm_num [xN]) hz1
        (by simp)
    have hle : Dfamily (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
        (bracketGE Bool Bool 1 xN z) ≤
          D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
            RC.1 RC.2) := Nat.sInf_le ⟨RC, hRC, rfl⟩
    have hconst : D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
        RC.1 RC.2) = 0 := PublicRecords.D_const false
    omega
  unfold LambdaGE
  rw [hzero (3 / 5) (by norm_num) (by norm_num),
    hzero (3 / 5 / 2) (by norm_num) (by norm_num),
    hzero (3 / 5 / 4) (by norm_num) (by norm_num)]
  norm_num

/-! ## §5  `thm:dense-stage4` (`08:298--328`), as a statement

The frozen theorem is stated at `08:298--319` and its proof opens at
`08:321--328` by fixing "an arbitrary retained member `N'` of the bracket
family" and "an arbitrary protocol `P` computing `N'`", then assuming
`cost(P) <= C - 1 = log_2 s + D_2` for contradiction.  This section lands the
statement together with the exact reduction of the family bound to that
per-member contradiction; the deeper subsections `08:330--1346` are the named
hypothesis. -/

/-- **The frozen conclusion of `thm:dense-stage4` (`08:317`)**,
`comp<N, 1, 1 - eta_R, 1 - eta_C> >= C`.  The tolerances are read in the `N`
orientation, i.e. `eta_R` on rows of `N` = columns of `A`, per `08:154--156`. -/
def DenseStageFourConclusion {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (ηR ηC : ℝ) (Cval : ℕ) : Prop :=
  Cval ≤ Dfamily (interlaceFun Nmat 1) (bracketGE Rw Cl 1 (1 - ηR) (1 - ηC))

/-- **Aux 32 (`08:321--328`: one member, one protocol, one contradiction).**
"Fix an arbitrary retained member `N'` ... and fix an arbitrary protocol `P`
computing `N'`.  Assume for contradiction that `cost(P) <= C - 1`."  Refuting
that for every protocol is exactly a lower bound `C <= comp(N')` on that
member, provided `C` is positive so that `C - 1` is not truncated.  General in
the game. -/
theorem member_bound_of_no_cheap_protocol {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) {Cval : ℕ} (hC : 0 < Cval)
    (h : ∀ P : Protocol A B Bool, Protocol.Computes P g → Cval - 1 < P.cost) :
    Cval ≤ D g := by
  have hne : (AchievableCosts g).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty g
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem hne
  have hlt : Cval - 1 < P.cost := h P hcomp
  have : Cval - 1 < D g := by
    simpa [D, hcost] using hlt
  omega

/-- **Aux 33 (the family bound needs the family to be nonempty).**  `Dfamily`
is a `Nat.sInf` and returns `0` on the empty family, so the frozen
`comp<N, 1, 1-eta_R, 1-eta_C> >= C` is **not** implied by a per-member bound
alone.  The nonemptiness side condition is discharged from the vendored
`NPCC.bracketGE.nonempty` at the frozen tolerances, which are positive and at
most one.  General. -/
theorem denseFamily_nonempty {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {ηR ηC : ℝ} (hηR : 0 ≤ ηR) (hηC : 0 ≤ ηC)
    (hcard : 1 ≤ Fintype.card Rw) :
    (bracketGE Rw Cl 1 (1 - ηR) (1 - ηC)).Nonempty := by
  classical
  exact bracketGE.nonempty 1 (1 - ηR) (1 - ηC) (by linarith) (by linarith) hcard

/-- **`thm:dense-stage4` (`08:298--319`), as a statement with its hypothesis
battery.**

The frozen hypotheses are `Admissible(Public, Pi, T_lev)` and `NoCert(Public)`,
under which "all Stage-1--Stage-3 certificates derived earlier under the same
`NO` certificate, the auxiliary certificate `eq:stage2-aux-certificate`, and
every Dense and ExtensionCoverage gate of `def:admissibility-groups` are
available with their printed types"; the conclusion is `comp(bracket) >= C`.

`Admissible`, `NoCert` and `LevelStep` are Lean pending and are therefore
**explicit propositional binders**, never silent axioms.  The whole content of
`08:330--1346` -- synchronisation, the dominant-block bijection, the branchwise
defect and witness families, the selection `w > 4b`, the weighted routing and
the two closure lemmas -- is the single named hypothesis `hnoProtocol`, in
exactly the frozen shape "for every retained member and every alleged protocol
of cost at most `C - 1`, contradiction".

What this theorem supplies is the passage from that per-member statement to the
family bound: the positivity of `C` that makes `C - 1` exact, and the
nonemptiness of the bracket family without which the `Nat.sInf` convention
would make the conclusion unsound. -/
theorem denseStageFour {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (ηR ηC : ℝ) (Cval : ℕ)
    (Admissible NoCert : Prop) (hAdm : Admissible) (hNo : NoCert)
    (hηR : 0 < ηR) (hηC : 0 < ηC) (hcard : 1 ≤ Fintype.card Rw)
    (hC : 0 < Cval)
    (hnoProtocol : Admissible → NoCert →
      ∀ RC ∈ bracketGE Rw Cl 1 (1 - ηR) (1 - ηC),
        ∀ P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool,
          Protocol.Computes P (subgame (interlaceFun Nmat 1) RC.1 RC.2) →
            Cval - 1 < P.cost) :
    DenseStageFourConclusion Nmat ηR ηC Cval :=
  EthBridge.le_Dfamily (interlaceFun Nmat 1)
    (bracketGE Rw Cl 1 (1 - ηR) (1 - ηC)) Cval
    (denseFamily_nonempty hηR.le hηC.le hcard)
    (fun RC hRC =>
      member_bound_of_no_cheap_protocol _ hC (hnoProtocol hAdm hNo RC hRC))

/-- **Statement pole for `thm:dense-stage4`.**  The conclusion is not
automatic: at the legal constant matrix over two-element carriers the family
complexity is `0` at every legal pair of tolerances, so `>= C` fails for every
`C >= 1`.  The lower bound is genuine content of `08:330--1346`. -/
theorem denseStageFour_not_automatic {ηR ηC : ℝ} (hηR : 0 ≤ ηR) (_hηR1 : ηR ≤ 1)
    (hηC : 0 ≤ ηC) (_hηC1 : ηC ≤ 1) :
    ¬ DenseStageFourConclusion (fun (_ : Bool) (_ : Bool) => false) ηR ηC 1 := by
  intro h
  obtain ⟨RC, hRC⟩ :=
    bracketGE.nonempty (X := Bool) (Y := Bool) 1 (1 - ηR) (1 - ηC) (by linarith)
      (by linarith) (by simp)
  have hle : Dfamily (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
      (bracketGE Bool Bool 1 (1 - ηR) (1 - ηC)) ≤
        D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
          RC.1 RC.2) := Nat.sInf_le ⟨RC, hRC, rfl⟩
  have hconst : D (subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
      RC.1 RC.2) = 0 := PublicRecords.D_const false
  have h1 : (1 : ℕ) ≤ Dfamily (interlaceFun (fun (_ : Bool) (_ : Bool) => false) 1)
      (bracketGE Bool Bool 1 (1 - ηR) (1 - ηC)) := h
  omega

/-! ### The block's separation gates and auxiliary certificate
(`08:259--296`) -/

/-- `rho_temp = 1/1000`, `rho_Sigma = 1/100`, `rho_loc = 1/4` (`08:273--275`,
also `06:129--131`). -/
noncomputable def rhoTemp : ℝ := 1 / 1000

noncomputable def rhoSigma : ℝ := 1 / 100

noncomputable def rhoLoc : ℝ := 1 / 4

/-- `x_3 = 1 - rho_temp` (`08:266`). -/
noncomputable def xThree : ℝ := 1 - rhoTemp

/-- `y_3 = 1 - rho_Sigma` (`08:266`). -/
noncomputable def yThree : ℝ := 1 - rhoSigma

/-- `T_0^{aux} = ceil(x_3 m_3)` (`08:267`). -/
noncomputable def tZeroAux (m₃ : ℕ) : ℕ := ⌈xThree * (m₃ : ℝ)⌉₊

/-- `T_3^{aux} = ceil(2^{1-b_T} m_3)` (`08:268`). -/
noncomputable def tThreeAux (bT m₃ : ℕ) : ℕ := ⌈(2 : ℝ) / 2 ^ bT * (m₃ : ℝ)⌉₊

/-- `x_dom = (T_0^{aux} - (s-1) T_3^{aux})/m_3` (`08:269--270`). -/
noncomputable def xDom (s bT m₃ : ℕ) : ℝ :=
  ((tZeroAux m₃ : ℝ) - ((s : ℝ) - 1) * (tThreeAux bT m₃ : ℝ)) / (m₃ : ℝ)

/-- **`eq:dense-separation-gates` (`08:276--286`)**, the five comparisons the
parameter schedule enforces for `thm:dense-stage4`.  Transcribed as a predicate
and never asserted. -/
def denseSeparationGates (s bT m₃ : ℕ) (ε₂ : ℝ) : Prop :=
  (s : ℝ) * (1 / 2 ^ bT) ≤ xThree ∧
    s * tThreeAux bT m₃ < tZeroAux m₃ ∧
    (18 / 25 : ℝ) ≤ yThree ∧
    xTdepth bT ≤ xDom s bT m₃ ∧
    (49 / 100 : ℝ) ≤ xDom s bT m₃ / 2 / (1 + ε₂)

/-- **`eq:stage2-aux-certificate` (`08:290--296`)**, the part of the auxiliary
`(1/10, b_T)`-robustness certificate of the *same physical matrix* `S_2` that
Section 8 consumes: `comp(S_2) = D_2` and `Lambda_{S_2}(1, x_T, y) >= D_2` at
`x_T = 2^{-b_T}`.  Transcribed as a predicate and never asserted -- the
certificate is Stage-2 content, not this block's. -/
def stageTwoAuxCertificate {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (S₂ : Rw → Cl → Bool) (dTwoVal bT : ℕ) (y : ℝ) : Prop :=
  D S₂ = dTwoVal ∧ dTwoVal ≤ LambdaGE S₂ 1 (xTdepth bT) y

/-- **Aux 34 (the separation gates force a deep auxiliary Stage-3 depth).**  The
first gate alone gives `s < 2^{b_T}`.  This is recorded because the block's own
gates are stated in terms of a free `b_T`, whereas the schedule
(`06:237--243`) additionally ties `b_T = 2^{j_49(log_2(s/4))}`; the derived
inequality is the point at which those two facts have to be reconciled, and it
is a genuine constraint rather than a formality. -/
theorem denseSeparationGates_force_depth {s bT m₃ : ℕ} {ε₂ : ℝ}
    (hg : denseSeparationGates s bT m₃ ε₂) : (s : ℝ) < 2 ^ bT := by
  have h := hg.1
  have hp : (0 : ℝ) < 2 ^ bT := by positivity
  rw [xThree, rhoTemp] at h
  rw [mul_one_div, div_le_iff₀ hp] at h
  nlinarith

/-! ## §6  Non-vacuity, statement poles and consistency probes (LANE-GATE 3)

Every construction above is inhabited at **legal** values by a **nondegenerate**
witness, and every statement is checked against its trivial reading. -/

/-- Witness reservoir carriers: three underlying rows split as one template,
one vertex-source and one blocker-source row (`X_0 = T_raw + V_raw + B_raw`
with all four counts positive), and two underlying columns with one selector
and one diagonal column.  These are the smallest counts at which every frozen
multiplicity is positive and the mass identities are stated. -/
abbrev RowsWit : Type := Fin 3

abbrev ColsWit : Type := Bool

/-- The witness raw matrix: nonconstant, so nothing below is inhabited at a
degenerate point. -/
def BmatWit : RowsWit → ColsWit → Bool := fun _ y => y

/-- The witness protected duplicate, at the frozen multiplicities computed from
the witness counts `M_0 = 2`, `S_0 = D_0 = 1`, `X_0 = 3`,
`T_raw = V_raw = B_raw = 1`. -/
def protectedDupWit :
    ProtRows RowsWit (Fin 1) (Fin 1) (Fin 1) (uBase 1 1 1) (uTemp 3 1 1)
        (uVert 3 1 1) (uBlock 3 1 1) →
      ProtCols ColsWit (Fin 1) (Fin 1) (wBase 1 1) (wSel 2 1) (wDiag 2 1) →
      Bool :=
  protectedDup BmatWit (fun _ => 0) (fun _ => 1) (fun _ => 2) (fun _ => false)
    (fun _ => true)

/-- **Non-vacuity 1 (the frozen multiplicities are positive at legal counts).**
Every one of the seven multiplicities is positive, which is what the base
sections and the nonemptiness instances need. -/
theorem protectedDupWit_multiplicities_pos :
    0 < wBase 1 1 ∧ 0 < wSel 2 1 ∧ 0 < wDiag 2 1 ∧
      0 < uBase 1 1 1 ∧ 0 < uTemp 3 1 1 ∧ 0 < uVert 3 1 1 ∧ 0 < uBlock 3 1 1 := by
  simp only [wBase, wSel, wDiag, uBase, uTemp, uVert, uBlock]
  norm_num

/-- **Non-vacuity 2 (`eq:protected-carrier-cardinalities` at legal counts).**
The two labelled carriers have exactly `184 M_0 S_0 D_0 = 368` columns and
`2^{22} X_0 T_raw V_raw B_raw = 12582912` rows. -/
theorem protectedDupWit_carriers :
    Fintype.card
        (ProtCols ColsWit (Fin 1) (Fin 1) (wBase 1 1) (wSel 2 1) (wDiag 2 1)) = 368 ∧
      Fintype.card
        (ProtRows RowsWit (Fin 1) (Fin 1) (Fin 1) (uBase 1 1 1) (uTemp 3 1 1)
          (uVert 3 1 1) (uBlock 3 1 1)) = 12582912 := by
  constructor
  · rw [card_ProtCols]
    simp only [wBase, wSel, wDiag]
    norm_num
  · rw [card_ProtRows]
    simp only [uBase, uTemp, uVert, uBlock]
    norm_num

/-- **Non-vacuity 3 (the duplicate is nondegenerate).**  The witness protected
matrix takes both Boolean values, at two labelled columns lying in **different**
reservoirs; so the duplication neither collapses the matrix nor makes the
reservoir labels invisible to the entries. -/
theorem protectedDupWit_nondegenerate :
    protectedDupWit (Sum.inl (0, ⟨0, by simp [uBase]⟩))
        (Sum.inl (true, ⟨0, by simp [wBase]⟩)) = true ∧
      protectedDupWit (Sum.inl (0, ⟨0, by simp [uBase]⟩))
        (Sum.inr (Sum.inl (0, ⟨0, by simp [wSel]⟩))) = false := by
  constructor <;> rfl

/-- **Non-vacuity 4 (`comp(A) = comp(B)` at legal values, with both sides
nontrivial).**  The witness duplicate has exactly the complexity of the witness
raw matrix, and that complexity is at least one -- so the equality is not being
verified at a constant matrix where both sides are `0`. -/
theorem protectedDupWit_complexity :
    D protectedDupWit = D BmatWit ∧ 1 ≤ D BmatWit := by
  refine ⟨?_, ?_⟩
  · exact (D_protectedDup BmatWit _ _ _ _ _ (by simp [uBase]) (by simp [wBase])).2.2
  · exact one_le_D_of_two_values BmatWit (a₁ := 0) (a₂ := 0) (b₁ := false)
      (b₂ := true) (by decide)

/-- **Non-vacuity 5 (the exact masses at legal counts).**  At the witness counts
the four displayed column and row masses of `08:123--130` come out exactly. -/
theorem protectedDupWit_masses :
    ((2 * wBase 1 1 : ℕ) : ℚ) / ((184 * (2 * 1 * 1) : ℕ) : ℚ) = 91 / 92 ∧
      ((1 * wSel 2 1 : ℕ) : ℚ) / ((184 * (2 * 1 * 1) : ℕ) : ℚ) = muMass ∧
      ((3 * uBase 1 1 1 : ℕ) : ℚ) / ((2 ^ 22 * (3 * 1 * 1 * 1) : ℕ) : ℚ) =
        1 - sigmaMass ∧
      ((1 * uTemp 3 1 1 : ℕ) : ℚ) / ((2 ^ 22 * (3 * 1 * 1 * 1) : ℕ) : ℚ) = nuTemp :=
  ⟨(protected_col_masses (M₀ := 2) (S₀ := 1) (D₀ := 1) (by norm_num) (by norm_num)
      (by norm_num)).1,
    (protected_col_masses (M₀ := 2) (S₀ := 1) (D₀ := 1) (by norm_num) (by norm_num)
      (by norm_num)).2.1,
    (protected_row_masses (X₀ := 3) (T₀ := 1) (V₀ := 1) (B₀ := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).1,
    (protected_row_masses (X₀ := 3) (T₀ := 1) (V₀ := 1) (B₀ := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).2.1⟩

/-! ### The pinned instance at legal public values

`protectedDupWit` above inhabits the **generic** device.  The pinned
`protectedAFrozen` needs its own inhabitant, at values that are legal for the
*schedule*, not merely type-correct: `a = 3` is the compiler's floor (`M1`,
`sec:one-level`), `s = 4` is the smallest power of two clearing the frozen
`s >= 4` of `08:402`, and `q = 64` is then literally `06:124`'s "least power of
two at least `12 s N_E`" at `N_E = 1` (`12 * 4 * 1 = 48`, and `64 = 2^6` is the
least power of two above it).  A degenerate width such as `q = 1` would be
type-correct and is deliberately **not** used: it violates `06:124`, since
`card_edge_pos` gives `N_E >= 1` and therefore `q_2 >= 48`. -/

/-- The smallest legal slot binding: `a = 3` (`M1`) and `s = 4` (`08:402`). -/
def Fwit : Stage1SlotBinding := ⟨3, 4, le_refl 3, by norm_num⟩

@[simp] theorem Fwit_s : Fwit.s = 4 := rfl

@[simp] theorem Fwit_a : Fwit.a = 3 := rfl

/-- **Non-vacuity 6 (the parameter constraints of §3b are jointly legal).**  The
general facts of §3b are stated under `0 < q`, `4 <= s`, and inhabited seed,
item and Stage-2 column carriers.  Those constraints are not vacuous and are not
satisfied only at schedule-illegal points: at `a = 3` (`M1`'s floor) and
`s = 2^2 = 4` (a public power of two clearing `08:402`), the width `q = 64` is
**exactly** what `06:124` fixes -- it is a power of two, it clears
`12 s N_E = 48` at `N_E = 1`, and it is the least power of two that does.  A
degenerate `q = 1` is deliberately not used: `card_edge_pos` gives `N_E >= 1`,
so the schedule forces `q_2 >= 48`. -/
theorem Fwit_schedule_legal :
    3 ≤ Fwit.a ∧ 4 ≤ Fwit.s ∧ Fwit.s = 2 ^ 2 ∧
      12 * 4 * 1 ≤ (64 : ℕ) ∧ (64 : ℕ) = 2 ^ 6 ∧
      ∀ r : ℕ, 12 * 4 * 1 ≤ 2 ^ r → 64 ≤ 2 ^ r := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr
  have h6 : 6 ≤ r := by
    by_contra hlt
    have hlt' : r < 6 := Nat.lt_of_not_le hlt
    interval_cases r <;> norm_num at hr
  calc (64 : ℕ) = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h6

/-- **Non-vacuity 7 (the pinned `A` is built and nondegenerate at those legal
values).**  At `a = 3`, `s = 4`, `q_2 = 64` of `Fwit_schedule_legal`, with
two-element seed, item and Stage-2 column carriers, every one of the seven
multiplicities of `eq:protected-multiplicities` is positive and the two labelled
carriers really are blown up by the frozen factors: at least `184` labelled
columns and at least `2^{22}` labelled rows.  Since these are exactly the
hypotheses of `protectedAFrozen_col_masses` and `protectedAFrozen_row_masses`,
those two mass readouts are readouts at an inhabited, schedule-legal,
nondegenerate instance -- not statements over an empty regime. -/
theorem protectedAFrozen_legal_instance :
    (0 < wBaseF Fwit 64 Bool ∧ 0 < wSelF Fwit 64 Bool ∧ 0 < wDiagF Fwit 64 Bool ∧
        0 < uBaseF Fwit Bool Bool Bool ∧ 0 < uTempF Fwit Bool Bool Bool ∧
        0 < uVertF Fwit Bool Bool Bool ∧ 0 < uBlockF Fwit Bool Bool Bool) ∧
      184 ≤ Fintype.card (ProtColsFrozen Fwit 64 Bool) ∧
      2 ^ 22 ≤ Fintype.card (ProtRowsFrozen Fwit Bool Bool Bool) := by
  have hq : (0 : ℕ) < 64 := by norm_num
  have hs : 4 ≤ Fwit.s := by norm_num
  exact ⟨protectedAFrozen_multiplicities_pos (V := Bool) (X := Bool) (L₂ := Bool)
      Fwit hq hs true true true true,
    (protectedAFrozen_carriers_nondegenerate (V := Bool) (X := Bool) (L₂ := Bool)
      Fwit hq hs true true true true).1,
    (protectedAFrozen_carriers_nondegenerate (Y := Bool) (q := 64) Fwit hq hs
      true true true true).2⟩

/-- **Statement pole for the pinned instance.**  The pin is not decoration: at
the *same* Section-8 carriers, replacing the seven frozen numbers by `1` gives
an object that still satisfies `protectedDup_ignores_labels` and
`D_protectedDup` verbatim, yet whose base column mass is
`M_0 / (M_0 + S_0 + D_0)` -- and at the witness counts of
`unit_multiplicities_break_the_masses` that is `1/2`, not `91/92`.  So no
consumer may substitute "some labelled duplicate at these carriers" for
`protectedAFrozen`; only the pinned widths carry `08:123--137`. -/
theorem protectedAFrozen_pin_is_load_bearing :
    ∃ w₀ wSg wD : ℕ, 0 < w₀ ∧ 0 < wSg ∧ 0 < wD ∧
      ((2 * w₀ : ℕ) : ℚ) / ((2 * w₀ + (1 * wSg + 1 * wD) : ℕ) : ℚ) ≠ 91 / 92 :=
  ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Statement pole for the protected duplication.**  "Some labelled duplicate
whose value ignores labels" is not the frozen object.  A duplicate with all
multiplicities equal to `1` satisfies `dupMat_ignores_labels` and
`D_protectedDup` verbatim, yet at the witness counts its base column mass is
`1/2`, not the frozen `91/92`.  So `eq:protected-multiplicities` carries the
content of `08:98--130`, and no consumer may replace it by "any duplication". -/
theorem unit_multiplicities_break_the_masses :
    ((2 * 1 : ℕ) : ℚ) / ((2 * 1 + (1 * 1 + 1 * 1) : ℕ) : ℚ) = 1 / 2 ∧
      ((1 : ℚ) / 2 ≠ 91 / 92) := by
  constructor
  · norm_num
  · norm_num

/-- **Consistency probe 1 (the frozen tolerance chain).**  `06:228` fixes
`0 < eta_R <= eta_C/2 < tau < x_N`; the chain is satisfiable at legal public
rationals, and both tolerances are legal densities, so the hypotheses
`0 < eta_R`, `0 < eta_C` of `denseStageFour` are not in tension with the
schedule.  No `False` is derivable from the bundle at these values. -/
theorem tolerance_chain_consistent :
    ∃ ηR ηC : ℝ, 0 < ηR ∧ 0 < ηC ∧ ηR ≤ ηC / 2 ∧ ηC / 2 < tauR ∧ tauR < xN ∧
      ηR ≤ 1 ∧ ηC ≤ 1 := by
  refine ⟨1 / 1000, 1 / 100, by norm_num, by norm_num, by norm_num, ?_, ?_,
    by norm_num, by norm_num⟩
  · rw [tauR]; norm_num
  · rw [tauR, xN]; norm_num

/-- **Consistency probe 2 (`eq:dense-separation-gates` is satisfiable).**  The
five comparisons of `08:276--286` hold simultaneously at the legal public
values `s = 4`, `b_T = 16`, `m_3 = 2^{20}`, `eps_2 = 1/100`.  So the gate
bundle is not self-contradictory, and `thm:dense-stage4` is not stated over an
empty parameter regime.

**Recorded limit.**  This probe fixes only the constraints the *block* states.
The schedule additionally ties `b_T = 2^{j_49(log_2(s/4))}` (`06:237--243`),
which at `s = 4` would force `b_T = 1`; by `denseSeparationGates_force_depth`
the block's own first gate then forces `s < 2^{b_T}`, so the joint system is
satisfiable only at large `s`.  That reconciliation is a **schedule**
obligation of Section 6, outside this block, and is not claimed here. -/
theorem denseSeparationGates_satisfiable :
    denseSeparationGates 4 16 1048576 (1 / 100) := by
  have hT0 : tZeroAux 1048576 = 1047528 := by
    rw [tZeroAux, xThree, rhoTemp]
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor <;> push_cast <;> norm_num
  have hT3 : tThreeAux 16 1048576 = 32 := by
    rw [tThreeAux]
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor <;> push_cast <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [xThree, rhoTemp]; norm_num
  · rw [hT0, hT3]; norm_num
  · rw [yThree, rhoSigma]; norm_num
  · rw [xTdepth, xDom, hT0, hT3]; push_cast; norm_num
  · rw [xDom, hT0, hT3]; push_cast; norm_num

/-- **Consistency probe 3 (the `thm:dense-stage4` hypothesis bundle is
satisfiable, with the conclusion true and nontrivial).**  Every hypothesis of
`denseStageFour` is discharged at legal values: two-element carriers, the
banked nonconstant `bobBit`, tolerances `eta_R = eta_C = 1/4`, and `C = 1`.  At
these tolerances the bracket thresholds force the full row and column sets, so
the unique retained member is the whole matrix and no protocol of cost `0`
computes it.  Hence `hnoProtocol` is realizable and the conclusion holds -- the
theorem is not vacuous, and no `False` follows from the bundle. -/
theorem denseStageFour_hypotheses_consistent :
    DenseStageFourConclusion bobBit (1 / 4) (1 / 4) 1 := by
  classical
  refine denseStageFour bobBit (1 / 4) (1 / 4) 1 True True trivial trivial
    (by norm_num) (by norm_num) (by simp) (by norm_num) ?_
  intro _ _ RC hRC P hP
  have hrow : RC.1 = Finset.univ := by
    have h := hRC.1 0 (Finset.mem_univ 0)
    have hthr : ⌈(Fintype.card Bool : ℝ) * (1 - 1 / 4)⌉₊ = 2 := by
      simp only [Fintype.card_bool]
      rw [Nat.ceil_eq_iff (by norm_num)]
      constructor <;> norm_num
    rw [hthr] at h
    have hsub : (RC.1.filter (fun p : Fin 1 × Bool => p.1 = 0)) ⊆ RC.1 :=
      Finset.filter_subset _ _
    have hcard : 2 ≤ RC.1.card := le_trans h (Finset.card_le_card hsub)
    refine Finset.eq_univ_of_card _ ?_
    have : RC.1.card ≤ Fintype.card (Fin 1 × Bool) := Finset.card_le_univ _
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this ⊢
    omega
  have hcol : RC.2 = Finset.univ := by
    have h := hRC.2
    have hthr : ⌈((Fintype.card Bool : ℝ) ^ 1) * (1 - 1 / 4)⌉₊ = 2 := by
      simp only [Fintype.card_bool]
      rw [Nat.ceil_eq_iff (by norm_num)]
      constructor <;> norm_num
    rw [hthr] at h
    refine Finset.eq_univ_of_card _ ?_
    have hle : RC.2.card ≤ Fintype.card (Fin 1 → Bool) := Finset.card_le_univ _
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hle ⊢
    omega
  have hmem₁ : ((0 : Fin 1), true) ∈ RC.1 := by rw [hrow]; exact Finset.mem_univ _
  have hmemF : (fun _ : Fin 1 => false) ∈ RC.2 := by
    rw [hcol]; exact Finset.mem_univ _
  have hmemT : (fun _ : Fin 1 => true) ∈ RC.2 := by
    rw [hcol]; exact Finset.mem_univ _
  have hone : 1 ≤ D (subgame (interlaceFun bobBit 1) RC.1 RC.2) :=
    one_le_D_of_two_values _ (a₁ := ⟨((0 : Fin 1), true), hmem₁⟩)
      (a₂ := ⟨((0 : Fin 1), true), hmem₁⟩)
      (b₁ := ⟨(fun _ : Fin 1 => false), hmemF⟩)
      (b₂ := ⟨(fun _ : Fin 1 => true), hmemT⟩) (by exact Bool.false_ne_true)
  have hle : D (subgame (interlaceFun bobBit 1) RC.1 RC.2) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  omega

/-! ## §7  Candidate B, the rejected encoding

Two encodings of `eq:protected-labelled-carriers` were raced.

* **Candidate A (landed).**  `ProtCols` / `ProtRows`: a tagged sum of products
  in which each frozen reservoir `{label} x carrier x [multiplicity]` is a
  literal summand and the frozen labels are the summand injections.
* **Candidate B (below).**  One dependent sigma type
  `(l : L) x carrier(l) x [mult(l)]` over a named label type, with the three
  column reservoirs and the four row reservoirs instantiated at `L = Fin 3` and
  `L = Fin 4`.

Candidate B is more uniform: one carrier definition covers both arities.  Its
general battery is proved below, so it is a real candidate and not a strawman.
It loses on **faithfulness at the frozen arity** and on **length**:
`eq:protected-labelled-carriers` prints a three-fold and a four-fold `⊔`, which
Candidate A reproduces on the nose while Candidate B reproduces a
`Finset.sum` that must be expanded before it is the frozen display; and every
Section-8 use would additionally need a per-label `Fintype` instance produced
by a case split, which Candidate A gets from instance synthesis.  Aux lemmas
proved: A `6`, B `3`; faithfulness: A; length: A. -/

/-- Candidate B's labelled carrier, `(l : L) x carrier(l) x [mult(l)]`. -/
abbrev Labelled {L : Type*} (car : L → Type*) (mult : L → ℕ) : Type _ :=
  (l : L) × car l × Fin (mult l)

/-- Candidate B's forgetful map. -/
def forgetLabel {L Base : Type*} {car : L → Type*} {mult : L → ℕ}
    (incl : ∀ l, car l → Base) : Labelled car mult → Base :=
  fun z => incl z.1 z.2.1

/-- **Candidate-B aux 1 (`M7`/`M10`: the exact labelled cardinality).** -/
theorem card_Labelled {L : Type*} [Fintype L] (car : L → Type*)
    [∀ l, Fintype (car l)] (mult : L → ℕ) :
    Fintype.card (Labelled car mult) = ∑ l : L, Fintype.card (car l) * mult l := by
  simp [Labelled, Fintype.card_sigma, Fintype.card_prod]

/-- **Candidate-B aux 2 (`M7`: nonemptiness from one positive reservoir).** -/
theorem nonempty_Labelled {L : Type*} {car : L → Type*} {mult : L → ℕ} (l₀ : L)
    (c₀ : car l₀) (hm : 0 < mult l₀) : Nonempty (Labelled car mult) :=
  ⟨⟨l₀, c₀, ⟨0, hm⟩⟩⟩

/-- **Candidate-B aux 3 (`08:96`: the value ignores label and index).**  Two
labelled points over the same underlying element are identified by the
forgetful map, so the general `D_forget_eq` applies to Candidate B unchanged --
the complexity machinery of §1 is encoding-independent, and the race is decided
purely on the carrier display. -/
theorem forgetLabel_apply {L Base : Type*} {car : L → Type*} {mult : L → ℕ}
    (incl : ∀ l, car l → Base) (l : L) (c : car l) (k : Fin (mult l)) :
    forgetLabel (mult := mult) incl ⟨l, c, k⟩ = incl l c := rfl

/-! ### Disposition of Candidate B (recorded, binding on consumers)

`Labelled`, `forgetLabel`, `card_Labelled`, `nonempty_Labelled` and
`forgetLabel_apply` are **race evidence, not construction**.  Their disposition
is fixed here so that no later tranche has to re-decide it:

1. **They are not a second `A`.**  `Labelled` is a generic sigma-typed carrier
   shape.  It is never applied to the Section-8 reservoirs, carries no
   multiplicity pin, and no declaration in this module or downstream of it
   consumes it.  The frozen `A` of `eq:protected-labelled-carriers` is
   `protectedAFrozen` and nothing else; the frozen `N` of `08:147` is its
   transpose.
2. **They are retained, not deleted.**  The `k = 2` encoding race is part of the
   module's record: Candidate A won on faithfulness at the frozen three-fold and
   four-fold `⊔` arity and on length, and the losing candidate is kept with its
   own proved battery so the comparison can be re-audited rather than taken on
   trust.  Deleting it would leave the §7 race unfalsifiable.
3. **They assert nothing.**  All three Candidate-B lemmas are general facts
   about a sigma type (cardinality, an inhabitation constructor, and a
   projection equation).  None mentions complexity, density, a multiplicity
   formula, or any Section-8 object, so no consumer can read a mass, a carrier
   cardinality, or a `comp` claim out of them.
4. **Bar.**  A downstream tranche that wants the labelled duplication must
   consume `protectedAFrozen` (or, for the generic device, `protectedDup`) by
   pin.  Re-encoding Section 8 through `Labelled` would reopen the race and
   needs a fresh judged tranche, not a local decision. -/

end EthInapproximability.ParameterizedNP.DenseStageFourOpening
