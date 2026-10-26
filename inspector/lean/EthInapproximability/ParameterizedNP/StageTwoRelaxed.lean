import EthInapproximability.ParameterizedNP.StageOneInterlace

/-!
# Parameterized NP route: the Stage-2 relaxed interlace and its two-depth certificate

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `sec:one-level`, subsection
  *The four stages*, in the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/07-one-level-construction.tex`,
  **lines 217--433** (the Stage-2 block).  The anchors traced here are
  * lines 217--220, "Stage 2 is a relaxed interlace of `M_1^T`", and the
    indexed `(q_2, t_2, eps_2)`-balanced family
    `C_2 = (c^{(l)})_{l in L_2}` in `Rows(M_1)^{q_2}` with
    `c^{(l)} : [q_2] -> Rows(M_1)`;
  * `eq:stage2-relaxed-value` (label line 228, display lines 221--229), the
    Stage-2 universes and value equation
    `Rows(M_2) = [q_2] x C_1`, `Cols(M_2) = L_2`,
    `M_2((alpha, gamma), l) = M_1(c^{(l)}(alpha), gamma)`, together with the
    shorthand sentence of lines 230--231;
  * `eq:stage2-two-depth-comparisons` (label line 242, display lines
    234--243), the two literal Extension comparisons the schedule verifies for
    each `h in {2^{-b_2}, 2^{-b_T}}`;
  * `eq:stage2-one-depth-data` (label line 259, display lines 247--260), the
    one-depth data `p_2^seed = (9/16) t_2`,
    `h_2^seed = 2^{-2^{(49/100) sqrt(log_2 t_2)}}`, `K_j = q_2/2^j`,
    `r_j = K_j/t_2`, `beta_j = (3/5)/2^j`, `xi_j = K_j 2^{-b_1}`, and the
    integrality sentence of lines 261--263 (`16 | t_2`, and `4 t_2 <= q_2`
    makes each `r_j` a positive power of two);
  * `lem:stage2-one-depth` (label line 266, statement lines 265--311) with its
    four displays: the base `eq:stage2-one-depth-base` (label line 273), the
    power/depth/balance clauses `eq:stage2-balance-ceilings` (label line 288),
    the Extension comparisons `eq:stage2-one-depth-extension` (label line
    301), and the output `eq:stage2-one-depth-output` (label line 309);
  * the proof, lines 313--392: the exponent dictionary
    `M = M_1^T`, `x = 2^{-b_1}`, `T = k_2 = log_2 t_2`,
    `R = log_2(q_2/t_2)`, `q_2 = 2^{R+T}`; the General Hard Seed call
    `eq:stage2-one-depth-seed` (label line 326) at `(j, delta, m) = (5, 1/10, k_2)`
    with its literal ranges `x <= t_2 x <= 1` and
    `t_2 <= 2 p_2^seed <= 2 t_2` (lines 328--330); the column-loss-resilience
    verification of lines 332--352 with `y_c = (h 2^{-c}/(1+eps_2))^{1/t_2}`;
    the block-balancing / Localized Extension transport of lines 354--384 with
    binders `(T, R, R_loc) = (k_2, log_2(q_2/t_2), log_2(K_j/t_2))`, `a = 0`,
    represented capacity `2^{R_loc + T} = K_j`, and `|Q_j| = r_j p_2^seed
    = 9 K_j/16`; and the closing selector step of lines 385--391, "Since
    `q_2 = 2^{r_2}`, apply `lem:indexed-selector-protocol` with index type
    `L_2` and `c(l) = c^{(l)}`.  It sends exactly `r_2 = log_2 q_2` bits and
    then computes `M`";
  * the once-and-for-all balancing verification of lines 394--416: `q >= 2^16`,
    `q_2 2^{-b_1} <= 1/(2 v_max) <= 1/(2q) <= 1/131072`, hence
    `0 < xi_j <= 1/131072`, while
    `beta_j - 9/(16 * 2^j) = 3/(80 * 2^j) >= 3/320 > 1/131072`, so
    `(beta_j - xi_j)/(1 - xi_j) >= beta_j - xi_j > 9/(16 * 2^j)`, and because
    `9 K_j/16` is an integer this proves every ceiling in
    `eq:stage2-balance-ceilings`;
  * lines 418--422, the two calls of `lem:stage2-one-depth` at `h = 2^{-b_2}`
    and `h = 2^{-b_T}`, and `eq:stage2-two-depth-certificate` (label line 429,
    display lines 423--430) with `D_2 = B_cap + log_2 q_2`;
  * lines 431--433, "The ordinary depth `b_2` controls Stage 3.  The auxiliary
    depth `b_T` is used only in the deletion-stable and scale-alignment parts
    of the adapted Stage 4.  Both certificates refer to the same physical
    balanced family."

  The Stage-2 *numerals* named but **not** transcribed here come from
  `sections/06-parameter-schedule.tex`: `eq:b2-choice` (label line 426),
  `eq:t2-search` (label line 772), `eq:k2-tested-endpoint` (label line 779),
  `eq:stage2-structural-gates` (label line 848) and `eq:epsilon-product`
  (label line 857).  Exactly **two** clauses from that file are carried as
  data:
  * the frozen consequence `2 v_max q_2 2^{-b_1} <= 1` of
    `eq:stage2-structural-gates` in the form the balancing paragraph actually
    uses, `q_2 2^{-b_1} <= 1/131072` (`07:398--401`), as the
    `StageTwoWidths.depth_gate` field; and
  * the balancedness accuracy `eps_2 = 1/(100 t_2)` of `eq:epsilon-product`
    (display lines 851--857), as the derived scalar `epsTwo`, used **only** to
    inhabit the Stage-2 gates at a legal, strictly positive error.  The
    product error `eps_prod` and its `< 1/50` bound are Stage-4 data and are
    not transcribed.

  The typed definitional layer is `03-preliminaries.tex`:
  `def:balanced-family` (label line 277), `def:relaxed-interlace` (label line
  295), `lem:indexed-selector-protocol` (label line 125), `def:bracket`
  (label line 167), and the column-loss-resilience definition of lines
  313--331 -- the display `y_c(h) = (h 2^{-c}/(1+eps))^{1/t}` of lines
  317--319, the two clauses `eq:column-loss-i`/`eq:column-loss-ii` (labels
  lines 323 and 325), the legal index ranges `0 <= k <= comp M` and
  `0 <= c <= log_2 t + k` (lines 326--327), and the closing sentence "This is
  exactly the definition consumed by the inherited Extension theorem"
  (lines 327--328).  That definition is **not** transcribed here.  It is the
  vendored `NPCC.IsColumnLossResilient`, which
  `D-inherited-contracts.tex:653--655` names outright ("the literal predicate
  `NPCC.IsColumnLossResilient`(f,b,eps,Q,T,h)") as `eq:contract-column-loss`
  (display lines 656--665, natural-subtraction guard 665--666), over the
  `y_c` of `eq:contract-yloss` (display lines 647--651) of which `D:650--651`
  says "This is `NPCC.yLoss`".  Both are consumed by pin; both clauses are
  discharged at the Stage-2 call site by `columnLossResilience_holds`, at the
  exponent binders `(Q, T) = (r_2, k_2)` of `07:348--349`.
  The inherited endpoints named by the frozen Stage-2 proof are
  `sections/D-inherited-contracts.tex`: `eq:contract-balanced` (label line
  547), `eq:contract-block-balancing` (label line 572),
  `eq:contract-relaxed-transfer-input`/`-output` (labels lines 591 and 596),
  `eq:contract-hard-seed` (label line 486) with its fixed `j = 5`,
  `delta = 1/10` convention (lines 494--495) and the threshold names
  `eq:contract-hard-seed-threshold-names` (label line 512), the Extension
  / Localized Extension row of the interface index (`03:404--409`), and the
  Localized Extension paragraph itself (`D:718--757`): its extra binders
  `a, R_loc` with the guards `a <= 1` and `R_loc <= R` (lines 721--722), the
  replaced rectangle clause `eq:contract-localized-rectangle` (label line
  735) whose column clause is `h 2^{-a} L <= |C|`, the conclusion
  `eq:contract-localized-output` (label line 744), and the four exponent
  equalities `eq:contract-extension-exponents` (label line 754) together with
  the sentence "Recording only `t_2 | q_amb` and `t_2 | K` does not discharge
  [them]" (lines 755--757).

* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`
  `03-parameterized-construction.tex`).  Each was opened and checked to state
  the same fact; no reader item is assigned to two declarations, and none of
  them was claimed by any earlier ledger row (grep of the ledger, the
  crosswalk and `src/` for `paper-M2`, `paper-stage2` and `paper-b2-choice`
  returns nothing before this module):
  * `eq:paper-M2-definition` (label line 297, display lines 290--297)
    -> `stageTwo`, with `stageTwo_apply` as its value equation and
    `stageTwo_rows_card` / `stageTwo_cols_card` as its two carriers;
  * `eq:paper-stage2-one-depth-data` (label line 325, display lines
    318--326) -> the one-depth scalars `pSeedTwo`, `hSeedTwo`, `Kseed`,
    `rSeed`, `xiSeed` (the reader writes them `p_*`, `h_seed`, `q_j`, `r_j`,
    `alpha_j`; `beta_j` is the banked `StageOneInterlace.betaSeed`, which is
    not reclaimed);
  * `eq:paper-stage2-block-gates` (label line 335, display lines 329--336)
    -> `balanceCeilings_hold`;
  * `eq:paper-stage2-extension-gates` (label line 345, display lines
    338--346) -> `extensionComparisons`;
  * `eq:paper-stage2-one-depth-conclusion` (label line 353, display lines
    348--354) -> `dTwo` and `stageTwoOneDepth_output`;
  * `lem:paper-stage2-one-depth` (label line 307, statement lines 306--358)
    -> `stageTwoOneDepth`;
  * `eq:paper-M2-depth-gates` (label line 428, display lines 417--429)
    -> `twoDepthComparisons`;
  * `eq:paper-M2-exact` (label line 434, display lines 431--435)
    -> `stageTwo_scale_eq_dTwo`;
  * `eq:paper-M2-robust` (label line 440, display lines 437--441) together
    with `eq:paper-M2-aux-robust` (label line 448, display lines 444--449)
    -> `stageTwoTwoDepthCertificate`, whose two `Lambda` conjuncts are exactly
    those two displays and whose single `Pr` argument is the frozen "same
    physical balanced family".

  **Reader items deliberately declined, with the reason recorded.**
  * `eq:paper-b2-choice` (label line 279) is **not** claimed: this module does
    not transcribe the formula `b_2 = ceil(log_2(32 s q_1 m_R)) + c_b`, and
    the depth `b` enters every statement here as an explicit parameter.
  * `StageTwoWidths` and its gate theorems claim **no** reader item.  The
    reader prints the power/divisibility clauses only inside the hypothesis
    *prose* of `lem:paper-stage2-one-depth` (lines 310--317: "Let `q, t` be
    powers of two such that ... `16 | t`, `4t <= q`, `t <= 2^{b_1}`"), and
    prose is never cited as a statement; the `q_2 2^{-b_1} <= 1/131072`
    clause has no reader display at all.
  * the six `yLoss` range lemmas, `columnLossResilience_holds`,
    `columnLossResilience_at_endpoint_binders` and the two
    density-monotonicity lemmas claim **no** reader item.  The reader
    compresses that whole verification into the *unlabelled* implication of
    lines 365--375 plus the sentence "so the required one-copy and three-rung
    bounds follow from the robust certificate of `M` and monotonicity" -- that
    sentence is exactly clauses (i) and (ii), but it is prose, and prose is
    never cited as a statement.  Those declarations therefore trace the
    autoformalization anchors `03-preliminaries.tex:313--331` and
    `D-inherited-contracts.tex:645--666` alone.
  * `pSeedTwo_eq_hardSeed_copyCount`, the exponent-binder dictionary
    `localizedExtension_binders`, `localizedExtension_guards`,
    `localizedExtensionShift`, `stageTwo_ambient_lower`, the seed-call range
    lemmas, the non-vacuity witnesses, the consistency probes and the
    statement poles are verification apparatus with no counterpart in either
    document.
  * `epsTwo` claims **no** reader item: the reader does not print
    `eq:epsilon-product`.  It traces `06-parameter-schedule.tex:851--857` and
    is used only to inhabit the gates at a legal error.
  * `Slot`, `inc`, `Stage1SlotBinding`, `stageOne`, `stageOneT`, `bCap`,
    `betaSeed`, `xSeed`, `hSeed`, `pSeed`, `Dfamily_const` and `LevelParams`
    are **banked** (`SLOTS-001`, `STAGE1-001`, `RECORD-LAYER-001`) and are
    consumed by pin; their reader items stay with those rows and are not
    reclaimed.

## Dependencies, imports, adapters

* `EthInapproximability.ParameterizedNP.StageOneInterlace` (banked, consumed
  by pin) for `stageOne`, `stageOneT`, `Stage1Rows`, `Stage1Cols`, `bCap`,
  `betaSeed` and its three rung identities, `xSeed`, `hSeed`, `pSeed`,
  `pSeed_eq_nine_sixteenths`, `two_rpow_neg_natCast`, `Dfamily_const`,
  `stage1Legal` and `witnessSource`.  Through it,
  `EthInapproximability.ParameterizedNP.FiniteSlots` (`SLOTS-001`) for `Slot`
  and `Stage1SlotBinding`, `EthInapproximability.ParameterizedNP.PilotStage3`
  for the kernel-checked `relaxedInterlace_selector_upper`
  (`lem:indexed-selector-protocol` at the exact indexed `Fin L` interface),
  and `EthInapproximability.ParameterizedNP.PublicRecords`
  (`RECORD-LAYER-001`) for `LevelParams`, the typed `def:level-parameters`
  record whose single stored field `c_2 : Fin N_2 -> Fin q_2 -> Rows(M_1)` is
  the frozen indexed family `C_2`.  Also
  `EthInapproximability.ParameterizedNP.OneLevelCompletion` (banked, consumed
  by pin) for `D_aliceBit` and `one_le_D_of_no_const_value`, used only by the
  column-loss inhabitant.  Nothing from any of them is restated.
* Through that chain, `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported anywhere in this chain, so the cited AGHP balanced-family
  axiom of `NPCC.Axioms` is **not** in the closure of any declaration here.
  That is deliberate: see the cited-fact discipline below.
* Vendored declarations *consumed, never re-proved*: `NPCC.relaxedInterlace`
  (`def:relaxed-interlace`), `NPCC.IsBalancedFamily` (`eq:contract-balanced`,
  the *predicate* only), `NPCC.yLoss` (`eq:contract-yloss`),
  `NPCC.IsColumnLossResilient` (`eq:contract-column-loss`), `NPCC.Dfamily`,
  `NPCC.bracketGE`, `NPCC.bracketGE.nonempty`, `NPCC.LambdaGE`,
  `NPCC.comp_transpose`, and `Workspace.Types.CommComplexity.D`.  No local
  declaration here shadows any of them: the two that round 1 did shadow
  (`NPCC.yLoss` as `yFun`/`zFun`, `NPCC.IsColumnLossResilient` as a local
  structure) are deleted, and the lemmas that remain about them
  (`yLoss_ratio_*`, `yLoss_antitone_in_c`, `yLoss_pos_of_pos`,
  `yLoss_le_one_of_le_one`, `yLoss_one_zero`, `columnLossResilient_*`) are
  *properties* of the vendored definitions, stated over the vendored names.
* **External theorem adapters: none is taken as an axiom.**  Of the endpoints
  the frozen Stage-2 argument calls,
  * **two are consumed by pin**: the indexed selector protocol, banked as
    `PilotStage3.relaxedInterlace_selector_upper`, which makes the upper half
    `comp(M_2) <= comp(M_1^T) + log_2 q_2` a **proved theorem**
    (`stageTwo_selector_upper`); and the family-vs-ambient comparison
    `PilotStage3.familyComplexity_le_ambient` together with
    `PilotStage3.interlace_selector_upper` at `p = 1`, which make the ambient
    lower bound `07:386` a **proved theorem** (`stageTwo_ambient_lower`).
  * **density monotonicity is proved here**, not assumed: raising the retained
    column density shrinks the `>=`-bracket family, so `comp` rises
    (`Dfamily_mono_in_density`, `LambdaGE_mono_in_density`).  This is what lets
    both clauses of the column-loss contract be discharged.
  * **the block-balancing gates are proved here** (`balanceCeilings_hold`,
    the frozen paragraph `07:394--416`).
  * **the General Hard Seed corollary and Localized Extension enter as
    explicit named binders** on the theorems that use them (`hardSeed`;
    `rung₀`, `rung₁`, `rung₂`, and their auxiliary-depth twins), never as
    silent axioms and never as bundle fields.  The relaxed-to-classical
    transfer theorem is not invoked at this interface.
* **The cited balanced family is a named hypothesis, never an axiom.**  The
  *existence* of an indexed `(q_2, t_2, eps_2)`-balanced family is the AGHP
  citation of `03-preliminaries.tex:291--293` (`alon1992simple`); in the
  vendored development it is an axiom of `NPCC.Axioms`, reachable only
  through the opt-in `LegacyNPCC.Stage12` facade.  This module therefore
  never asserts existence: the family is the stored field `Pr.c_2` of the
  banked `LevelParams` record, and its balancedness enters every statement as
  the explicit binder `hbal : NPCC.IsBalancedFamily W.t₂ Pr.c₂ ε₂`.  So no
  declaration here has the AGHP axiom in its closure, and
  `stageTwo_balancedness_is_not_a_field` checks in the kernel that
  balancedness is not derivable from the record.
* Proof status of every declaration below: **new** (first transcription of
  the frozen Stage-2 block).

## Coverage limits, binding on every consumer

These are the honest scope of the module.  A consumer that reads more than
this out of a green build is reading something that is not here.

1. **`stageTwoOneDepth` does not prove `lem:stage2-one-depth`.**  What *is*
   proved outright: the upper half of the scale (`stageTwo_selector_upper`,
   from the banked indexed selector protocol plus `clog_q₂`); the whole
   balancing paragraph `07:394--416` (`balanceCeilings_hold`); the ambient
   lower bound `07:386` from the `j = 0` rung (`stageTwo_ambient_lower`); both
   clauses of the inherited column-loss-resilience input -- the vendored
   `NPCC.IsColumnLossResilient` itself, at the named exponent binders
   `(Q, T, b) = (r_2, k_2, b_1)` of `07:348--349`
   (`columnLossResilience_holds`, using the *proved* density monotonicity) --
   and the hard-seed call legality (`stageTwoSeedCall_legal`).  What remains a
   **named binder** is exactly the *three Localized Extension endpoints* of
   `07:354--384`, one per rung `j = 0, 1, 2`.  Nothing else.
   **Positive scope fact, checked rather than asserted.**  The column-loss
   input produced here *does* typecheck into the Appendix-D endpoints:
   `NPCC.extension_theorem` (`Transfer.lean:807`) and
   `NPCC.localized_extension` (`:839`) bind
   `hres : IsColumnLossResilient f b eps (R + T) T h`, and
   `columnLossResilience_at_endpoint_binders` produces exactly that value at
   `R = r_2 - k_2`, `T = k_2`.  So the residual gap at the endpoints is the
   *rest* of their hypothesis lists, not the resilience input.
2. The three rung binders are the frozen Localized Extension conclusions and
   are **not** discharged here.  `localizedExtension_binders` supplies the
   complete call record demanded by `eq:contract-extension-exponents`
   (including both guards `R_loc <= R` and `a = 0`), and `balanceCeilings_hold`
   supplies the `EquipGE` gates, but the endpoint itself is an external
   theorem consumed by hypothesis, exactly as `EXPANDER-001` would be.
3. **The hypotheses `hbal`, `hext`, `hthree`, `hh0` and `hε` of
   `stageTwoOneDepth` are carried without being consumed** by the Lean
   derivation of its conclusion, which consumes `hbase`, `hh1` and the three
   rungs.  They are carried because the frozen lemma states them and because
   they are what the *human* proof feeds into the three endpoints.  What they
   buy is checked, non-trivially and separately, by
   `stageTwoOneDepth_carried_hypotheses_fire`.  The unused-variable linter is
   switched off for `stageTwoOneDepth` and `stageTwoTwoDepthCertificate` for
   that reason, and for no other.
4. `b_2`, `b_T`, `eps_2`, `t_2` and `q_2` are carried as explicit parameters,
   as `StageTwoWidths` numerals, or (for `eps_2`) as the single derived scalar
   `epsTwo`.  The straight-line program of `sec:parameters` that computes them
   is **not** transcribed, so **no parameter schedule may be read out of this
   module**: in particular the `eq:t2-search` clause `k_2 >= 2^19` is not
   asserted anywhere here (see `widthsWitness`, `bigWidths`), and
   `depthTwoWitness = 40` / `depthAuxWitness = 60` are *illustrative positive
   depths*, not the values `eq:b2-choice` computes.
5. No `Robust(M_2^T, ...)` predicate is stated here.  The frozen Stage-3
   input is `eq:stage2-two-depth-certificate`; deriving an ordinary
   robustness predicate from it is Stage-3 input and is not claimed.
6. **`stageTwoTwoDepthCertificate` is an assembly, not an existence claim.**
   It applies `stageTwoOneDepth` twice over one record `Pr`, one `ε` and one
   `hbal`, so it inherits limits 1--3 twice over: six rung binders remain, and
   nothing here asserts that any of them holds for any concrete matrix.
7. **The existence of the balanced family is never asserted.**  `hbal` is a
   named hypothesis at every use site.  `isBalancedFamily_satisfiable` shows
   only that the predicate is not self-contradictory at a positive accuracy;
   existence at the frozen Stage-2 carriers is the AGHP citation and stays
   behind the opt-in `LegacyNPCC.Stage12` facade, out of this module's axiom
   closure.
8. **Round-1 repair scope.**  This generation repairs five confirmed
   statement defects of the parked draft (`hlower` assumed rather than
   derived; the two-depth certificate assuming its own conclusion; clause (i)
   of the column-loss contract omitted; the Localized Extension guards
   `R_loc <= R` and `a = 0` dropped; `twoDepthComparisons` uninhabited, its
   component witnessed only at the illegal `h = 1`, `eps = 0`).  It does
   **not** widen the traced range: the anchors are still `07:215--435` plus
   the cited `03` and `D` definitions.
9. **Round-2 repair scope.**  This generation repairs one further confirmed
   defect: round 1 restated two pinned vendored interfaces (`NPCC.yLoss` as
   `zFun`/`yFun`, `NPCC.IsColumnLossResilient` as a local structure at general
   *values* `q t : ℕ` with the exponents recovered by `Nat.log`).  Both local
   declarations are deleted; the contract is consumed at the named exponent
   binders; the A3 battery is restated at those binders; and the contract is
   given a nondegenerate inhabitant at legal parameter values
   (`columnLossResilient_inhabited`) so that it is not merely derived from the
   unwitnessed Stage-1 premises.  The traced range is unchanged apart from
   *naming* the two Appendix-D anchors the round-1 header already cited in
   substance: `eq:contract-yloss` (`D:645--651`) and `eq:contract-column-loss`
   (`D:653--666`).  No statement was weakened, and every group the round-1
   judge cleared is byte-identical except where deleting `zFun`/`yFun` forced
   a change of spelling with no change of content
   (`extensionComparisons`, `columnLossResilience_inputs`,
   `extensionComparisons_monotone_in_h`, `two_rpow_le_yLoss_ratio_xSeed`,
   `yLoss_one_zero`, `extensionComparisons_of_depth_gates`).
   `bobBit` and its four supporting lemmas are the inhabitant and are **not**
   Stage-2 objects: nothing about `M_2` may be read off them.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M1`/`M2`/`M4`: **no complexity, robustness, promise or lower-bound field
  appears in any structure here.**  The one new structure, `StageTwoWidths`,
  carries four numerals (`k₂`, `r₂`, `b₁`, `mHS`) and exactly the four frozen
  numeric side conditions that are **not** derivable from the others:
  `5 <= m_HS` (`D-inherited-contracts.tex:496`), `k_2 >= m_HS`
  (`eq:stage2-balance-ceilings`), `4 t_2 <= q_2` (same display), and the
  balancing-paragraph gate `q_2 2^{-b_1} <= 1/131072` (`07:398--401`) in its
  cleared-denominator form.  `gates_are_numeric` checks in the kernel that
  the field bundle alone never produces a complexity claim.
* `M3`: the remaining clauses of `eq:stage2-balance-ceilings` are
  **theorems**, never fields, because they are derived telescopes --
  `16 | t_2` is `five_le_mHS` + `mHS_le_k₂` `=>` `5 <= k_2` `=>` `16 | 2^k₂`
  (`sixteen_dvd_t₂`); `t_2 | q_2` is `four_t₂_le_q₂` (`t₂_dvd_q₂`);
  `t_2 <= 2^{b_1}` is `four_t₂_le_q₂` + `depth_gate` (`t₂_le_two_pow_b₁`);
  and `0 < xi_j < beta_j < 1` together with all three ceilings is
  `balanceCeilings_hold`.  `t₂`, `q₂`, `pSeedTwo`, `Kseed`, `rSeed`,
  `xiSeed`, `hSeedTwo`, `dTwo` are derived definitions, not fields, and
  `beta_j` is the banked `betaSeed`, re-exported rather than restated.
* `M5`/`M8`: this module is upstream of the bridge's interlace layer; the
  widths `q` and `Q` do **not** appear here at all.  The three widths that do
  are kept provably distinct: `q₂_ne_q₁` and `q₂_ne_L₁` at the declared
  bindings, and `t₂_lt_q₂` in general.
* `M7`: nonemptiness is preserved -- `stageTwo_rows_nonempty`,
  `stageTwo_cols_nonempty` (the latter is exactly what the frozen
  `0 < N_2` structural field of `def:level-parameters` is carried for), and
  `Kseed_pos`, `rSeed_pos`, `pSeedTwo_pos`.
* `M9`: the two promise branches are never merged.  `dTwo` mentions no
  matrix, and the `NO`-case reading enters `stageTwo_scale_eq_dTwo` as the
  named hypothesis `hbase`; `dTwo_is_not_a_complexity_claim` exhibits a legal
  binding and a legal matrix where `comp(M_2) < D_2`.
* `M10`: every count is a `Fintype.card` or a `Nat.ceil` of a real density,
  and *repeated tuples in `C_2` remain distinct indexed columns* --
  `stageTwo_repeated_columns_stay_distinct` is `def:balanced-family`'s
  sentence "Repeated tuples are allowed and are treated as distinct indexed
  columns" made checkable.

## Candidate encodings of `eq:stage2-relaxed-value`

Two encodings of `M_2` were built and raced.

* **Candidate A (landed).**  `stageTwo` is the banked vendored relaxed
  interlace `NPCC.relaxedInterlace (stageOneT F R) Pr.c₂`, typed at the frozen
  carriers directly: rows `[q_2] x C_1`, columns `L_2 = [N_2]`.  Both frozen
  universes are the *types* of the declaration, so `eq:stage2-relaxed-value`
  holds by `rfl` (`stageTwo_apply`, `stageTwo_rows_card`,
  `stageTwo_cols_card`), and the banked
  `relaxedInterlace_selector_upper` applies by pin.
* **Candidate B (rejected).**  `M_2` with its column carrier taken to be the
  *image* `Set.range Pr.c₂` of the family -- i.e. repeated tuples merged into
  one column -- with the value equation read off the representative.

`stageTwo_eq_candidateB_on_range` records that the two agree pointwise
wherever B is defined, so nothing is lost by keeping B.  Candidate B is
rejected on the discriminating battery item: `def:balanced-family`
(`03:288`) and `eq:contract-balanced` (`D:547`) both say outright that
the probability is over *indices*, so repeated tuples remain distinct
columns, and `candidateB_column_count_is_wrong` proves in the kernel that at
the declared legal binding a constant family with `N_2 = 2` gives B one
column where the frozen `Cols(M_2) = L_2` has two.  Under B the frozen
`|Cols(M_2)| = N_2` is therefore false, balancedness (a statement about index
frequencies) is not expressible, and the selector protocol's `log_2 q_2`
accounting loses its index type.  Ranking (aux lemmas proved, faithfulness,
length): A wins all three.

## Concrete bindings declared here

`widthsWitness` (`k_2 = 5`, `r_2 = 7`, `b_1 = 24`, `m_HS = 5`, hence
`t_2 = 32`, `q_2 = 128`) is the **only** concrete `StageTwoWidths` this
module introduces, and it is the componentwise-least one: every one of its
four gates is discharged **at its boundary** (`5 <= 5`, `5 <= 5`,
`4 * 32 = 128 <= 128`, `131072 * 128 = 2^24 <= 2^24`).  It is **not** the
tuple the compiler computes -- `eq:t2-search` (`06:766`) forces
`k_2 >= 2^19` through the search clause `k_2 >= max{4, 2^19, m_HS}`, so the
scheduled `t_2` is astronomically larger -- and coverage limit 3 forbids
reading any parameter schedule out of this module.

For the same reason `widthsWitness` is **not** claimed to be jointly legal
with the Stage-1 illustrative binding `StageOneInterlace.stage1Legal`
(`a = 7`, `s = 64`).  The two illustrative bindings pin `b_1` from opposite
sides: `twentyFour_le_b₁` proves that the frozen Stage-2 balancing gate
forces `b_1 >= 24` at **every** legal `StageTwoWidths`, whereas at the
illustrative `a = 7` the Stage-1 scale `eq:stage1-scales` would give
`b_1 = 2^{j_49(5)} = 2`.  That is a property of the two *illustrative*
choices, not of the frozen text, whose actual `a` is
`C_0 (log_2 A_*)^2` and whose actual `k_2` is at least `2^19`; it is recorded
here so that no consumer reads a joint schedule out of the pair.  Only the
slot binding `stage1Legal` is reused below, and only for the carriers
`q_1 = 126` and `L_1 = 191`, never for a depth.
-/

namespace EthInapproximability.ParameterizedNP.StageTwoRelaxed

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.PublicRecords (LevelParams)

variable {X Y : Type*}

/-! ## §0  The Stage-2 width record

`eq:stage2-balance-ceilings` (`07-one-level-construction.tex:276--289`) prints
the power, depth and balance conditions of `lem:stage2-one-depth`
simultaneously for `j = 0, 1, 2`.  Only the clauses that are *not* consequences
of the rest are fields (`M3`); everything else is a theorem below. -/

/-- **The Stage-2 width record.**  Four numerals and the four frozen numeric
side conditions of `eq:stage2-balance-ceilings` and `07:398--401` that are not
derivable from the others.

`t_2 = 2^{k_2}` and `q_2 = 2^{r_2}` are the frozen power-of-two forms
(`07:278--279`), so they are *derived* accessors rather than stored widths.

*Honest scope (`M2`/`M4`).*  This record is not a certificate that any Stage-2
call succeeded and it asserts nothing about any matrix: `gates_are_numeric`
checks that the field bundle is decidable from `(k_2, r_2, b_1, m_HS)` alone.
The inherited theorems' conclusions are supplied to the theorems below as
explicit binders, so no complexity claim can be read out of constructor data.

**SUPERSEDED-PENDING-MIGRATION (`STAGE2-DERIVED-WIDTH-001`, staged-migration
round 1).**  This record stores `r_2`, hence stores `q_2 = 2^{r_2}` as free
constructor data.  The frozen source does **not** leave `q_2` free.  Its
defining display is `04-guarded-source.tex:391`
(`def:guarded-source-constructor`), `q_2 = min{2^r : 12 s |E| <= 2^r}`, at the
floor `s >= 4` of `04:389`; the schedule restates it at
`06-parameter-schedule.tex:122--124` ("Thus `s` is a public power of two.  The
source theorem then fixes `q_2 = the least power of two at least 12 s N_E`").
And `05-public-records.tex:188--189` says of the one-level parameter record
that "there are **no stored width**, tolerance, multiplicity, capacity,
ceiling, or output-size fields", while `05:186--188` puts admissibility
*after* the construction ("the balancedness formula remains a
post-construction admissibility proposition; it is not a proof field of
`Pi`").  A stored `r_2` is therefore an authoring defect on two counts: it
assigns a source-*defined* quantity, and it carries its four gates as
constructor proof fields.

The correction is section 12 below.  There the width is the **derived**
`GuardedSourceSlab.q2 G s`, consumed by pin from the intake `(G, s)` that
`def:level-trace` clause `T1` (`05:235--240`) fixes, with `r₂Of` as its
exponent; `DerivedWidthCoherent` states the migration hypothesis, and
`stored_width_is_not_derived` proves in the kernel that the hypothesis is a
genuine restriction on this record.

**Migration plan (recorded in the route ledger, row
`STAGE2-DERIVED-WIDTH-001`).**  Round 1 (this one) adds the derived width and
the coherence bridge alongside, and touches no consumer.  The downstream half
of the same ledger row supplies **no corrected carrier**, and none is promised
here: `02:85--88` fixes that derived quantities are "recomputed from the
constructed object", so a record bundling `k_2`, `b_1`, `m_HS` and `q_2`
together with equations pinning each to its own chain would be a provable
singleton that constructs nothing.  What lands downstream is an **accessor
surface**: `Section5Admissibility` Part 12 reads each of those quantities off
a `ScheduleContext` by evaluating that quantity's own defining display
(`eq:t2-search` `06:763--772`, `eq:stage1-scales` `06:317`,
`eq:contract-hard-seed-threshold-names` `D:507--513`, and `04:386--391` for
`q_2`), states the Stage-2 numeric gates over that surface as `WidthGateCore`,
and maps a gated context back into *this* record through `toStoredAt`.  Those
displays cannot be evaluated in this module, because `ParameterSchedule` and
`Section5Admissibility` both import it; that is why the surface is downstream,
and it is why this record is bridged rather than rebuilt.  Later rounds move
consumers across one module at a time, from `toStoredAt` to the context
accessors directly.  This record deletes **last**, and only
after the final consumer has moved.  Until then it stays exactly as it is:
nothing here is renamed, reordered, weakened, or retyped, so every banked
consumer keeps its byte-identical interface. -/
structure StageTwoWidths where
  /-- `t_2 = 2^{k_2}` (`07:278`). -/
  k₂ : ℕ
  /-- `q_2 = 2^{r_2}` (`07:279`). -/
  r₂ : ℕ
  /-- The Stage-1 output depth `b_1` of `eq:stage1-scales`, which fixes
  `x_1 = 2^{-b_1}`; Stage 2 reads it through `t_2 <= 2^{b_1}` and through the
  balancing gate below. -/
  b₁ : ℕ
  /-- The hard-seed exponent threshold `m_HS` of
  `eq:contract-hard-seed-threshold-names`; no numeral is required. -/
  mHS : ℕ
  /-- `5 <= m_HS`, the first conjunct of the tail predicate `HSThreshold`
  (`D-inherited-contracts.tex:496`). -/
  five_le_mHS : 5 ≤ mHS
  /-- `k_2 >= m_HS` (`eq:stage2-balance-ceilings`, `07:281`), the clause that
  makes the General Hard Seed call at exponent `k_2` legal. -/
  mHS_le_k₂ : mHS ≤ k₂
  /-- `4 t_2 <= q_2` (`eq:stage2-balance-ceilings`, `07:280`), the clause the
  frozen text says "makes each `r_j` a positive power of two". -/
  four_t₂_le_q₂ : 4 * 2 ^ k₂ ≤ 2 ^ r₂
  /-- `q_2 2^{-b_1} <= 1/131072` (`07:398--401`), the frozen consequence of
  `eq:stage2-structural-gates` that the balancing paragraph actually uses,
  cleared of its denominator.  `depth_gate_density` restores the displayed
  real form. -/
  depth_gate : 131072 * 2 ^ r₂ ≤ 2 ^ b₁

namespace StageTwoWidths

variable (W : StageTwoWidths)

/-- The Stage-2 independence width `t_2 = 2^{k_2}`. -/
def t₂ : ℕ := 2 ^ W.k₂

/-- The Stage-2 ambient copy count `q_2 = 2^{r_2}`. -/
def q₂ : ℕ := 2 ^ W.r₂

@[simp] theorem t₂_eq : W.t₂ = 2 ^ W.k₂ := rfl

@[simp] theorem q₂_eq : W.q₂ = 2 ^ W.r₂ := rfl

theorem t₂_pos : 0 < W.t₂ := Nat.one_le_two_pow

theorem q₂_pos : 0 < W.q₂ := Nat.one_le_two_pow

/-- `5 <= k_2`: the two threshold fields compose. -/
theorem five_le_k₂ : 5 ≤ W.k₂ := le_trans W.five_le_mHS W.mHS_le_k₂

/-- `k_2 + 2 <= r_2`, the exponent form of the frozen `4 t_2 <= q_2`. -/
theorem k₂_add_two_le_r₂ : W.k₂ + 2 ≤ W.r₂ := by
  have h := W.four_t₂_le_q₂
  have h' : (2:ℕ) ^ (W.k₂ + 2) ≤ 2 ^ W.r₂ := by
    calc (2:ℕ) ^ (W.k₂ + 2) = 4 * 2 ^ W.k₂ := by ring
      _ ≤ 2 ^ W.r₂ := h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h'

theorem k₂_le_r₂ : W.k₂ ≤ W.r₂ := le_trans (by omega) W.k₂_add_two_le_r₂

theorem seven_le_r₂ : 7 ≤ W.r₂ := by
  have h1 := W.five_le_k₂
  have h2 := W.k₂_add_two_le_r₂
  omega

/-- **Derived telescope (`M3`), not a field.**  `16 | t_2`
(`eq:stage2-balance-ceilings`, `07:280`) follows from `5 <= m_HS <= k_2`. -/
theorem sixteen_dvd_t₂ : 16 ∣ W.t₂ := by
  have h := W.five_le_k₂
  refine ⟨2 ^ (W.k₂ - 4), ?_⟩
  simp only [t₂]
  rw [show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_add]
  congr 1
  omega

/-- **Derived telescope (`M3`), not a field.**  `t_2 | q_2`
(`eq:stage2-balance-ceilings`, `07:278`) follows from `4 t_2 <= q_2`. -/
theorem t₂_dvd_q₂ : W.t₂ ∣ W.q₂ := pow_dvd_pow 2 W.k₂_le_r₂

/-- **Width separation (`M5`).**  `t_2 < q_2`: the independence width and the
ambient copy count can never be silently identified. -/
theorem t₂_lt_q₂ : W.t₂ < W.q₂ :=
  Nat.pow_lt_pow_right (by norm_num) (by have := W.k₂_add_two_le_r₂; omega)

/-- **Derived telescope (`M3`), not a field.**  `t_2 <= 2^{b_1}`
(`eq:stage2-balance-ceilings`, `07:281`) follows from `4 t_2 <= q_2` and the
balancing gate. -/
theorem t₂_le_two_pow_b₁ : W.t₂ ≤ 2 ^ W.b₁ := by
  have h1 : W.t₂ ≤ W.q₂ := le_of_lt W.t₂_lt_q₂
  have h2 := W.depth_gate
  simp only [q₂] at h1
  omega

/-- `b_1 >= 24` at **every** legal width record: the frozen balancing gate
`q_2 2^{-b_1} <= 1/131072 = 2^{-17}` together with `q_2 >= 2^7` forces it.
This is the frozen `07:398--401` calculation read as a lower bound on the
depth, and it is the reason no illustrative Stage-1 depth may be reused here
(see the module header). -/
theorem twentyFour_le_b₁ : 24 ≤ W.b₁ := by
  have h7 := W.seven_le_r₂
  have hq : (2:ℕ) ^ 24 ≤ 131072 * 2 ^ W.r₂ := by
    calc (2:ℕ) ^ 24 = 131072 * 2 ^ 7 := by norm_num
      _ ≤ 131072 * 2 ^ W.r₂ := by
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h7)
  have h : (2:ℕ) ^ 24 ≤ 2 ^ W.b₁ := le_trans hq W.depth_gate
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

/-- `log_2 t_2 = k_2` and `log_2 q_2 = r_2`: the two logarithms the frozen
Stage-2 bookkeeping writes are exact, not estimates. -/
theorem log_t₂ : Nat.log 2 W.t₂ = W.k₂ := Nat.log_pow (by norm_num) _

theorem log_q₂ : Nat.log 2 W.q₂ = W.r₂ := Nat.log_pow (by norm_num) _

/-- The **selector width** of the closing step of `lem:stage2-one-depth`
(`07:386--390`): "Since `q_2 = 2^{r_2}` ... it sends exactly
`r_2 = log_2 q_2` bits". -/
theorem clog_q₂ : Nat.clog 2 W.q₂ = W.r₂ := Nat.clog_pow 2 _ (by norm_num)

/-- The displayed real form of the balancing gate,
`q_2 2^{-b_1} <= 1/131072` (`07:399--400`). -/
theorem depth_gate_density : (W.q₂ : ℝ) * xSeed W.b₁ ≤ 1 / 131072 := by
  have hpow : (0:ℝ) < 2 ^ W.b₁ := by positivity
  have hcast : ((131072 * 2 ^ W.r₂ : ℕ) : ℝ) ≤ ((2 ^ W.b₁ : ℕ) : ℝ) :=
    Nat.cast_le.2 W.depth_gate
  push_cast at hcast
  rw [xSeed, two_rpow_neg_natCast, q₂_eq]
  push_cast
  rw [mul_one_div, div_le_iff₀ hpow]
  linarith

/-- **`M2`/`M4` check.**  The whole field bundle is decidable from the four
numerals alone; no matrix, protocol, promise certificate or complexity value
enters it. -/
theorem gates_are_numeric :
    5 ≤ W.mHS ∧ W.mHS ≤ W.k₂ ∧ 4 * 2 ^ W.k₂ ≤ 2 ^ W.r₂ ∧
      131072 * 2 ^ W.r₂ ≤ 2 ^ W.b₁ :=
  ⟨W.five_le_mHS, W.mHS_le_k₂, W.four_t₂_le_q₂, W.depth_gate⟩

end StageTwoWidths

/-! ## §1  The Stage-2 universes and value equation

`eq:stage2-relaxed-value` (`07-one-level-construction.tex:221--229`):
```
Rows(M_2)            = [q_2] x C_1
Cols(M_2)            = L_2
M_2((alpha, gamma), l) = M_1(c^{(l)}(alpha), gamma)
```
The indexed family is the single stored field `c_2` of the banked
`def:level-parameters` record, consumed by pin, and the Stage-1 matrix is the
banked `stageOne`.  Nothing is restated. -/

/-- **The Stage-2 relaxed interlace `M_2`** of `eq:stage2-relaxed-value`
(`07:221--229`), reader `eq:paper-M2-definition`
(`03-parameterized-construction.tex:290--297`).

The frozen sentence is "Stage 2 is a relaxed interlace of `M_1^T`", and that
is literally the definition: `NPCC.relaxedInterlace` applied to `stageOneT`
with the stored indexed family, whose row set is `[q_2] x Cols(M_1)`, whose
column set is the *index* type `L_2 = [N_2]`, and whose value is
`M_1^T(gamma, c^{(l)}(alpha)) = M_1(c^{(l)}(alpha), gamma)`. -/
def stageTwo (F : Stage1SlotBinding) (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂) :
    Slot W.q₂ × Stage1Cols F Y → Slot Pr.N₂ → Bool :=
  relaxedInterlace (stageOneT F R) Pr.c₂

/-- The transposed Stage-2 matrix `M_2^T`, the object whose three-rung
certificates `eq:stage2-two-depth-certificate` are the Stage-3 and Stage-4
inputs. -/
def stageTwoT (F : Stage1SlotBinding) (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂) :
    Slot Pr.N₂ → Slot W.q₂ × Stage1Cols F Y → Bool :=
  fun ℓ p => stageTwo F R W Pr p ℓ

/-- The frozen value equation, definitionally. -/
@[simp] theorem stageTwo_apply (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (α : Slot W.q₂) (γ : Stage1Cols F Y) (ℓ : Slot Pr.N₂) :
    stageTwo F R W Pr (α, γ) ℓ = stageOne F R (Pr.c₂ ℓ α) γ := rfl

@[simp] theorem stageTwoT_apply (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (ℓ : Slot Pr.N₂) (p : Slot W.q₂ × Stage1Cols F Y) :
    stageTwoT F R W Pr ℓ p = stageTwo F R W Pr p ℓ := rfl

/-- The frozen value equation in its fully expanded form: the Stage-1 entry
read at the family's `alpha`-th coordinate.  `07:225--226` plus `07:230--231`
("`c_alpha^{(l)}` is shorthand for the typed evaluation `c^{(l)}(alpha)`"). -/
theorem stageTwo_eq_stageOne_at_family (F : Stage1SlotBinding)
    (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (α : Slot W.q₂) (γ : Stage1Cols F Y) (ℓ : Slot Pr.N₂) :
    stageTwo F R W Pr (α, γ) ℓ = R (Pr.c₂ ℓ α).2 (γ (F.iota₁ (Pr.c₂ ℓ α).1)) :=
  rfl

/-! ## §2  Aux-lemma battery A1: the frozen carriers (`M7`, `M10`)

Every lemma in this battery is general in `F`, `R`, `W`, `Pr`, `X`, `Y`. -/

/-- **Aux 1 (row carrier).**  `|Rows(M_2)| = q_2 |C_1| = q_2 n_R^{L_1}`, the
literal `[q_2] x C_1` of `eq:stage2-relaxed-value` line 1. -/
theorem stageTwo_rows_card (F : Stage1SlotBinding) (W : StageTwoWidths)
    (Y : Type*) [Fintype Y] :
    Fintype.card (Slot W.q₂ × Stage1Cols F Y) = W.q₂ * Fintype.card Y ^ F.L₁ := by
  rw [Fintype.card_prod, Fintype.card_fin, stageOne_cols_card F Y]

/-- **Aux 2 (column carrier).**  `|Cols(M_2)| = |L_2| = N_2`: the columns are
the family *indices*, so repeated tuples are counted
(`def:balanced-family`, `03:288`). -/
theorem stageTwo_cols_card (Pr : LevelParams (Stage1Rows F X) w) :
    Fintype.card (Slot Pr.N₂) = Pr.N₂ := Fintype.card_fin _

/-- **Aux 3 (nonempty rows).**  `q_2 > 0` is banked in `StageTwoWidths`, and
the Stage-1 column carrier is nonempty whenever the source one is. -/
instance stageTwo_rows_nonempty (F : Stage1SlotBinding) (W : StageTwoWidths)
    (Y : Type*) [Nonempty Y] : Nonempty (Slot W.q₂ × Stage1Cols F Y) :=
  ⟨(⟨0, W.q₂_pos⟩, fun _ => Classical.arbitrary Y)⟩

/-- **Aux 4 (nonempty columns).**  This is exactly what the frozen structural
field `0 < N_2` of `def:level-parameters` (`05:183--186`) is carried for. -/
instance stageTwo_cols_nonempty (Pr : LevelParams (Stage1Rows F X) w) :
    Nonempty (Slot Pr.N₂) := ⟨⟨0, Pr.N₂pos⟩⟩

/-- **Aux 5 (the family is read one coordinate at a time).**  Two family
indices whose tuples agree give the same `M_2` column.  General. -/
theorem stageTwo_column_congr (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    {ℓ ℓ' : Slot Pr.N₂} (h : Pr.c₂ ℓ = Pr.c₂ ℓ') :
    (fun p => stageTwo F R W Pr p ℓ) = fun p => stageTwo F R W Pr p ℓ' := by
  funext p
  simp only [stageTwo, relaxedInterlace, h]

/-- **Aux 6 (`M10`: repeated tuples stay distinct columns).**  The frozen
sentence of `def:balanced-family` (`03:288`), "Repeated tuples are
allowed and are treated as distinct indexed columns", made checkable: at a
*constant* family the two columns of `M_2` are equal as Boolean functions,
yet the column carrier still has `N_2` elements.  General in `F`, `R`, `W`
and in the row carrier. -/
theorem stageTwo_repeated_columns_stay_distinct (F : Stage1SlotBinding)
    (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (hconst : ∀ ℓ ℓ' : Slot Pr.N₂, Pr.c₂ ℓ = Pr.c₂ ℓ') :
    (∀ ℓ ℓ' : Slot Pr.N₂,
        (fun p => stageTwo F R W Pr p ℓ) = fun p => stageTwo F R W Pr p ℓ') ∧
      Fintype.card (Slot Pr.N₂) = Pr.N₂ :=
  ⟨fun ℓ ℓ' => stageTwo_column_congr F R W Pr (hconst ℓ ℓ'),
    stageTwo_cols_card Pr⟩

/-- **Aux 7 (transpose invariance).**  `comp(M_2^T) = comp(M_2)`, by direct
consumption of the checked inherited `NPCC.comp_transpose`
(`eq:contract-comp-transpose`, `D-inherited-contracts.tex:284`).  Nothing is
re-proved. -/
theorem D_stageTwoT (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype Y] :
    D (stageTwoT F R W Pr) = D (stageTwo F R W Pr) :=
  NPCC.comp_transpose (stageTwo F R W Pr)

/-! ## §3  The one-depth data of `eq:stage2-one-depth-data`

`07-one-level-construction.tex:247--260`:
```
p_2^seed = (9/16) t_2,      h_2^seed = 2^{-2^{(49/100) sqrt(log_2 t_2)}},
K_j      = q_2/2^j,         r_j      = K_j/t_2,
beta_j   = (3/5)/2^j,       xi_j     = K_j 2^{-b_1}      (j = 0,1,2).
```
Reader `eq:paper-stage2-one-depth-data`
(`03-parameterized-construction.tex:318--326`), where the same six scalars are
written `p_*`, `h_seed`, `q_j`, `r_j`, `beta_j`, `alpha_j`.  `beta_j` is the
banked `StageOneInterlace.betaSeed` and is re-exported, not restated. -/

/-- `p_2^seed = (9/16) t_2`, written in the copy-count form of the inherited
contract `eq:contract-hard-seed` (`D-inherited-contracts.tex:482`) at its
frozen `j = 5`, so that the call's legality is visible in the definition. -/
def pSeedTwo (k₂ : ℕ) : ℕ := 18 * 2 ^ (k₂ - 5)

/-- `h_2^seed = 2^{-2^{(49/100) sqrt(log_2 t_2)}}` at `log_2 t_2 = k_2`.  This
is the retained **column** density of the hard-seed call; the orientation
`D-inherited-contracts.tex:488--492` forbids reversing is preserved. -/
noncomputable def hSeedTwo (k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (k₂ : ℕ))))

/-- `K_j = q_2/2^j`, the branch-local capacity of rung `j`. -/
def Kseed (W : StageTwoWidths) (j : ℕ) : ℕ := 2 ^ (W.r₂ - j)

/-- `r_j = K_j/t_2`, a positive power of two by the frozen `4 t_2 <= q_2`. -/
def rSeed (W : StageTwoWidths) (j : ℕ) : ℕ := 2 ^ (W.r₂ - W.k₂ - j)

/-- `xi_j = K_j 2^{-b_1}`, the within-fibre density at which block balancing
is applied. -/
noncomputable def xiSeed (W : StageTwoWidths) (j : ℕ) : ℝ :=
  (Kseed W j : ℝ) * xSeed W.b₁

/-! ### Aux-lemma battery A2: frozen identities of the one-depth scalars -/

/-- **Aux 8 (the frozen closed form).**  `p_2^seed = (9/16) t_2` whenever the
hard-seed exponent threshold `5 <= k_2` holds.  Proved by pin from the banked
`pSeed_eq_nine_sixteenths` at rung `0`. -/
theorem pSeedTwo_eq_nine_sixteenths {k₂ : ℕ} (h : 5 ≤ k₂) :
    (pSeedTwo k₂ : ℝ) = 9 / 16 * ((2 : ℕ) ^ k₂ : ℕ) := by
  have hp : pSeedTwo k₂ = pSeed k₂ 0 := rfl
  have hw : wSeed k₂ 0 = (2 : ℕ) ^ k₂ := rfl
  have := pSeed_eq_nine_sixteenths k₂ 0 (by simpa [mSeed] using h)
  rw [hp, this, hw]

/-- **Aux 9 (the inherited call is at `j = 5`).**  `p_2^seed` is *literally*
the copy count `(2^{j-1}+2) 2^{m-j}` of `eq:contract-hard-seed` at the frozen
`j = 5` and exponent `m = k_2` (`D-inherited-contracts.tex:495`, "Every active
call fixes `j = 5` and `delta = 1/10`"). -/
theorem pSeedTwo_eq_hardSeed_copyCount (k₂ : ℕ) :
    pSeedTwo k₂ = (2 ^ (5 - 1) + 2) * 2 ^ (k₂ - 5) := by norm_num [pSeedTwo]

/-- **Aux 10 (alignment with the banked Stage-1 seed column density).**  The
Stage-2 hard-seed column density is the banked `hSeed` at exponent `k_2`:
the two frozen displays are the same function of their exponent. -/
theorem hSeedTwo_eq_hSeed (k₂ : ℕ) : hSeedTwo k₂ = hSeed k₂ 0 := rfl

theorem hSeedTwo_pos (k₂ : ℕ) : 0 < hSeedTwo k₂ := by
  rw [hSeedTwo_eq_hSeed]; exact hSeed_pos k₂ 0

theorem hSeedTwo_le_one (k₂ : ℕ) : hSeedTwo k₂ ≤ 1 := by
  rw [hSeedTwo_eq_hSeed]; exact hSeed_le_one k₂ 0

theorem pSeedTwo_pos (k₂ : ℕ) : 0 < pSeedTwo k₂ :=
  Nat.mul_pos (by norm_num) Nat.one_le_two_pow

theorem Kseed_pos (W : StageTwoWidths) (j : ℕ) : 0 < Kseed W j :=
  Nat.one_le_two_pow

theorem rSeed_pos (W : StageTwoWidths) (j : ℕ) : 0 < rSeed W j :=
  Nat.one_le_two_pow

/-- **Aux 11 (`K_0 = q_2`).**  Rung `0` is the ambient copy count. -/
@[simp] theorem Kseed_zero (W : StageTwoWidths) : Kseed W 0 = W.q₂ := rfl

/-- **Aux 12 (the rung offset).**  `log_2 K_j = log_2 q_2 - j`, which is the
exact bookkeeping of the frozen conclusion
`B_cap + log_2 K_j = B_cap + log_2 q_2 - j` (`07:383`). -/
theorem log_Kseed (W : StageTwoWidths) (j : ℕ) :
    Nat.log 2 (Kseed W j) = W.r₂ - j := Nat.log_pow (by norm_num) _

/-- **Aux 13 (`r_j t_2 = K_j`).**  The frozen factorization `K_j = r_j t_2`
holds for every `j <= 2`, which is what makes the Localized Extension call's
`q = r t` datum literal. -/
theorem rSeed_mul_t₂ (W : StageTwoWidths) {j : ℕ} (hj : j ≤ 2) :
    rSeed W j * W.t₂ = Kseed W j := by
  have h := W.k₂_add_two_le_r₂
  simp only [rSeed, Kseed, StageTwoWidths.t₂, ← pow_add]
  congr 1
  omega

/-- **Aux 14 (`|Q_j| = r_j p_2^seed = 9 K_j / 16`).**  The exact coordinate
count returned by block balancing (`07:359--362`), in closed form. -/
theorem rSeed_mul_pSeedTwo (W : StageTwoWidths) {j : ℕ} (hj : j ≤ 2) :
    rSeed W j * pSeedTwo W.k₂ = 9 * 2 ^ (W.r₂ - j - 4) := by
  have h1 := W.k₂_add_two_le_r₂
  have h2 := W.five_le_k₂
  simp only [rSeed, pSeedTwo]
  rw [show (18:ℕ) = 9 * 2 by norm_num]
  rw [show 9 * 2 * 2 ^ (W.k₂ - 5) = 9 * 2 ^ (W.k₂ - 4) by
    rw [mul_assoc, ← pow_succ']
    congr 2
    omega]
  rw [← mul_assoc, mul_comm (2 ^ (W.r₂ - W.k₂ - j)) 9, mul_assoc, ← pow_add]
  congr 2
  omega

/-- **Aux 15 (the frozen integrality remark).**  `9 K_j/16` really is an
integer, which is the step `07:413--414` ("Because `9 K_j/16` is an integer,
this proves every ceiling") relies on. -/
theorem rSeed_mul_pSeedTwo_real (W : StageTwoWidths) {j : ℕ} (hj : j ≤ 2) :
    ((rSeed W j * pSeedTwo W.k₂ : ℕ) : ℝ) = 9 / 16 * (Kseed W j : ℝ) := by
  have h1 := W.k₂_add_two_le_r₂
  have h2 := W.five_le_k₂
  rw [rSeed_mul_pSeedTwo W hj]
  simp only [Kseed]
  have hsplit : (2:ℕ) ^ (W.r₂ - j) = 2 ^ (W.r₂ - j - 4) * 16 := by
    rw [show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    congr 1
    omega
  rw [hsplit]
  push_cast
  ring

/-- **Aux 16 (`t_2 <= 2 p_2^seed <= 2 t_2`).**  The frozen sentence "the row
and copy ranges in Extension are literal" (`07:328--330`). -/
theorem pSeedTwo_range (W : StageTwoWidths) :
    W.t₂ ≤ 2 * pSeedTwo W.k₂ ∧ 2 * pSeedTwo W.k₂ ≤ 2 * W.t₂ := by
  have h := W.five_le_k₂
  have hsplit : (2:ℕ) ^ W.k₂ = 2 ^ (W.k₂ - 5) * 32 := by
    rw [show (32:ℕ) = 2 ^ 5 by norm_num, ← pow_add]
    congr 1
    omega
  constructor <;> simp only [StageTwoWidths.t₂, pSeedTwo, hsplit] <;> omega

/-- **Aux 17 (`x <= t_2 x <= 1`).**  The other half of `07:328`, at
`x = x_1 = 2^{-b_1}`. -/
theorem xSeed_scaled_range (W : StageTwoWidths) :
    xSeed W.b₁ ≤ (W.t₂ : ℝ) * xSeed W.b₁ ∧ (W.t₂ : ℝ) * xSeed W.b₁ ≤ 1 := by
  have hx : 0 < xSeed W.b₁ := xSeed_pos W.b₁
  have h1 : (1:ℝ) ≤ (W.t₂ : ℝ) := by
    exact_mod_cast W.t₂_pos
  refine ⟨by nlinarith, ?_⟩
  have hcast : ((W.t₂ : ℕ) : ℝ) ≤ ((2 ^ W.b₁ : ℕ) : ℝ) :=
    Nat.cast_le.2 W.t₂_le_two_pow_b₁
  push_cast at hcast
  have hpow : (0:ℝ) < 2 ^ W.b₁ := by positivity
  rw [xSeed, two_rpow_neg_natCast]
  rw [mul_one_div, div_le_one hpow]
  exact hcast

/-! ## §4  The balancing verification of `07:394--416`, proved

The frozen text verifies the balance ceilings of `eq:stage2-balance-ceilings`
"once, independently of the requested depth", from
`q_2 2^{-b_1} <= 1/131072` alone.  That whole paragraph is a theorem here, not
a hypothesis.  Reader `eq:paper-stage2-block-gates`
(`03-parameterized-construction.tex:329--336`). -/

/-- **Aux 18 (the frozen margin).**  `beta_j - 9/(16 * 2^j) = 3/(80 * 2^j)`,
and for `j <= 2` this is at least `3/320`, which exceeds `1/131072`.  This is
the displayed calculation of `07:402--406`. -/
theorem betaSeed_margin {j : ℕ} (hj : j ≤ 2) :
    betaSeed j - 9 / 16 / 2 ^ j = 3 / 80 / 2 ^ j ∧
      (1 : ℝ) / 131072 < 3 / 80 / 2 ^ j := by
  have hpow : (2:ℝ) ^ j ≤ 4 := by
    calc (2:ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj
      _ = 4 := by norm_num
  have hpos : (0:ℝ) < 2 ^ j := by positivity
  constructor
  · unfold betaSeed
    rw [div_sub_div_same]
    norm_num
  · rw [div_div, lt_div_iff₀ (by positivity)]
    nlinarith

/-- `0 < xi_j` and `xi_j <= 1/131072` at every legal width record: the frozen
line `0 < xi_j <= 1/131072` (`07:402`). -/
theorem xiSeed_bounds (W : StageTwoWidths) (j : ℕ) :
    0 < xiSeed W j ∧ xiSeed W j ≤ 1 / 131072 := by
  have hx : 0 < xSeed W.b₁ := xSeed_pos W.b₁
  have hK : (0:ℝ) < (Kseed W j : ℝ) := by exact_mod_cast Kseed_pos W j
  refine ⟨mul_pos hK hx, ?_⟩
  have hle : (Kseed W j : ℝ) ≤ (W.q₂ : ℝ) := by
    have : Kseed W j ≤ W.q₂ := by
      simp only [Kseed, StageTwoWidths.q₂]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  calc xiSeed W j = (Kseed W j : ℝ) * xSeed W.b₁ := rfl
    _ ≤ (W.q₂ : ℝ) * xSeed W.b₁ := by nlinarith
    _ ≤ 1 / 131072 := W.depth_gate_density

/-- **`eq:stage2-balance-ceilings`, the density and ceiling clauses, PROVED.**

`07:394--416` verbatim: the strict density chain `0 < xi_j < beta_j < 1` and
the block-balancing ceiling
`ceil(q_2 (beta_j - xi_j)/(1 - xi_j)) >= r_j p_2^seed = 9 K_j/16`,
for every `j <= 2` and at every legal `StageTwoWidths`.  No depth `h` and no
matrix enters, which is exactly the frozen claim that this holds
"independently of the requested depth".

Reader `eq:paper-stage2-block-gates`
(`03-parameterized-construction.tex:329--336`). -/
theorem balanceCeilings_hold (W : StageTwoWidths) {j : ℕ} (hj : j ≤ 2) :
    0 < xiSeed W j ∧ xiSeed W j < betaSeed j ∧ betaSeed j < 1 ∧
      rSeed W j * pSeedTwo W.k₂ ≤
        ⌈(W.q₂ : ℝ) * ((betaSeed j - xiSeed W j) / (1 - xiSeed W j))⌉₊ := by
  obtain ⟨hξpos, hξle⟩ := xiSeed_bounds W j
  obtain ⟨hmargin, hgap⟩ := betaSeed_margin hj
  have hpowj : (0:ℝ) < 2 ^ j := by positivity
  have hβ : betaSeed j = 3 / 5 / 2 ^ j := by unfold betaSeed; ring
  have hβpos : 0 < betaSeed j := betaSeed_pos j
  -- `beta_j >= 3/20 > 1/131072 >= xi_j`
  have hβlow : 3 / 20 ≤ betaSeed j := by
    have hpow : (2:ℝ) ^ j ≤ 4 := by
      calc (2:ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj
        _ = 4 := by norm_num
    rw [hβ, le_div_iff₀ hpowj]
    nlinarith
  have hξβ : xiSeed W j < betaSeed j := by
    have : (1:ℝ) / 131072 < 3 / 20 := by norm_num
    linarith
  have hβ1 : betaSeed j < 1 := by
    have hone : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [hβ, div_lt_one hpowj]
    nlinarith
  refine ⟨hξpos, hξβ, hβ1, ?_⟩
  -- The frozen chain: `(beta - xi)/(1 - xi) >= beta - xi >= (9/16)/2^j`.
  have hξ1 : xiSeed W j < 1 := by
    have : (1:ℝ) / 131072 < 1 := by norm_num
    linarith
  have hdiff : 0 < betaSeed j - xiSeed W j := by linarith
  have hdivge : betaSeed j - xiSeed W j
      ≤ (betaSeed j - xiSeed W j) / (1 - xiSeed W j) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  -- `beta_j - xi_j >= 9/(16 * 2^j)` because the margin `3/(80 * 2^j)` beats `xi_j`.
  have hkey : 9 / 16 / (2:ℝ) ^ j ≤ betaSeed j - xiSeed W j := by
    have h1 : (1:ℝ) / 131072 < 3 / 80 / 2 ^ j := hgap
    linarith [hmargin]
  -- Turn the density bound into the frozen coordinate count.
  have hKreal : ((rSeed W j * pSeedTwo W.k₂ : ℕ) : ℝ) = 9 / 16 * (Kseed W j : ℝ) :=
    rSeed_mul_pSeedTwo_real W hj
  have hKq : (Kseed W j : ℝ) * (2:ℝ) ^ j = (W.q₂ : ℝ) := by
    have hjr : j ≤ W.r₂ := le_trans hj (by have := W.seven_le_r₂; omega)
    simp only [Kseed, StageTwoWidths.q₂]
    rw [show (2:ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) by push_cast; ring]
    rw [show ((2 ^ (W.r₂ - j) : ℕ) : ℝ) = ((2 ^ (W.r₂ - j) : ℕ) : ℝ) from rfl]
    rw [← Nat.cast_mul, ← pow_add]
    congr 2
    omega
  have hbound : ((rSeed W j * pSeedTwo W.k₂ : ℕ) : ℝ)
      ≤ (W.q₂ : ℝ) * ((betaSeed j - xiSeed W j) / (1 - xiSeed W j)) := by
    rw [hKreal, ← hKq]
    have hq2 : (0:ℝ) < (Kseed W j : ℝ) := by exact_mod_cast Kseed_pos W j
    calc 9 / 16 * (Kseed W j : ℝ)
        = (Kseed W j : ℝ) * (2:ℝ) ^ j * (9 / 16 / (2:ℝ) ^ j) := by
          field_simp
      _ ≤ (Kseed W j : ℝ) * (2:ℝ) ^ j * (betaSeed j - xiSeed W j) := by
          have : (0:ℝ) ≤ (Kseed W j : ℝ) * (2:ℝ) ^ j := by positivity
          nlinarith
      _ ≤ (Kseed W j : ℝ) * (2:ℝ) ^ j
            * ((betaSeed j - xiSeed W j) / (1 - xiSeed W j)) := by
          have : (0:ℝ) ≤ (Kseed W j : ℝ) * (2:ℝ) ^ j := by positivity
          nlinarith
  exact Nat.cast_le.1 (le_trans hbound (Nat.le_ceil _))

/-! ## §5  Column-loss resilience: the `y_c` analysis of `07:332--352`

The frozen proof declines to hide this behind "apply Extension" and writes out
`y_c(h) = (h 2^{-c}/(1 + eps_2))^{1/t_2}`, its monotonicity in `c`, its range,
and the two clauses `eq:column-loss-i`/`eq:column-loss-ii` of `03:313--331`.

*Repair note (round 1).*  The parked draft carried the frozen "density
monotonicity" step of `07:340` as an explicit binder and stated only clause
(ii).  Both are fixed here: density monotonicity is **proved** below
(`Dfamily_mono_in_density`, `LambdaGE_mono_in_density`) because at fixed row
density the `>=`-bracket family shrinks as the retained column density rises,
and **both** frozen clauses are now discharged by `columnLossResilience_holds`.

*Repair note (round 2).*  Round 1 wrote `y_c` and its inner ratio as two local
definitions `yFun`/`zFun`.  `eq:contract-yloss`
(`D-inherited-contracts.tex:645--651`) says of that display, in terms, "This is
`NPCC.yLoss`", so a local copy restated a pinned interface.  Both local
definitions are **deleted**: `y_c` is now the vendored
`NPCC.yLoss ε (2^T) h c` (`vendor/npc-cc/NPCC/Transfer.lean:30`), and its inner
ratio is written out literally -- which is also the literal shape of the
`hbridge` argument of `NPCC.extension_theorem` (`Transfer.lean:810`).  The six
range lemmas below are *properties* of the vendored definition, proved here;
they restate nothing. -/

/-- **The inner ratio of `eq:contract-yloss` is positive.**  `03:317--319` and
`07:335` write `y_c(h)` as the `1/t`-th power of `h 2^{-c}/(1 + eps)`; that
ratio is also the literal `hbridge` argument of `NPCC.extension_theorem`
(`vendor/npc-cc/NPCC/Transfer.lean:810`).  Stated over the expression itself,
so that no vendored definition is duplicated by a local name. -/
theorem yLoss_ratio_pos {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (c : ℕ) :
    0 < h * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
  have h2 : (0:ℝ) < (2:ℝ) ^ (-(c:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hd : (0:ℝ) < 1 + ε := by linarith
  positivity

/-- The inner ratio of `eq:contract-yloss` never exceeds `1` at `h in (0,1]`. -/
theorem yLoss_ratio_le_one {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (c : ℕ) : h * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) ≤ 1 := by
  have h2 : (2:ℝ) ^ (-(c:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.2 (Nat.cast_nonneg c))
  have h2pos : (0:ℝ) < (2:ℝ) ^ (-(c:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hd : (0:ℝ) < 1 + ε := by linarith
  rw [div_le_one hd]
  nlinarith

/-- **Aux 19 (`y_c` decreases with `c`).**  `07:338`, at the level of the inner
ratio of `eq:contract-yloss`. -/
theorem yLoss_ratio_antitone {h ε : ℝ} (hh0 : 0 ≤ h) (hε : 0 ≤ ε) {c c' : ℕ}
    (hc : c ≤ c') :
    h * (2 : ℝ) ^ (-(c' : ℝ)) / (1 + ε) ≤ h * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
  have hd : (0:ℝ) < 1 + ε := by linarith
  have hmono : (2:ℝ) ^ (-(c':ℝ)) ≤ (2:ℝ) ^ (-(c:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (c:ℝ) ≤ (c':ℝ) := by exact_mod_cast hc
      linarith)
  gcongr

/-- **Aux 19' (`NPCC.yLoss` decreases with `c`).**  `07:338` for the vendored
`y_c` itself: the `1/t`-th power is monotone on the nonnegatives. -/
theorem yLoss_antitone_in_c {h ε : ℝ} (hh0 : 0 < h) (hε : 0 ≤ ε) (t : ℕ)
    {c c' : ℕ} (hc : c ≤ c') : yLoss ε t h c' ≤ yLoss ε t h c := by
  unfold yLoss
  exact Real.rpow_le_rpow (le_of_lt (yLoss_ratio_pos hh0 hε c'))
    (yLoss_ratio_antitone (le_of_lt hh0) hε hc) (by positivity)

/-- `0 < y_c(h)` for the vendored `NPCC.yLoss`. -/
theorem yLoss_pos_of_pos {h ε : ℝ} (hh0 : 0 < h) (hε : 0 ≤ ε) (t c : ℕ) :
    0 < yLoss ε t h c :=
  Real.rpow_pos_of_pos (yLoss_ratio_pos hh0 hε c) _

/-- `y_c(h) <= 1` for the vendored `NPCC.yLoss` at `h in (0,1]`. -/
theorem yLoss_le_one_of_le_one {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (t c : ℕ) : yLoss ε t h c ≤ 1 :=
  Real.rpow_le_one (le_of_lt (yLoss_ratio_pos hh0 hε c))
    (yLoss_ratio_le_one hh0 hh1 hε c) (by positivity)

/-! ### Density monotonicity, PROVED

`07:340--341` reads the two column-loss clauses off "density monotonicity and
`eq:stage2-one-depth-base`".  Density monotonicity is *not* an inherited
endpoint at this interface: raising the retained column density `y` strictly
tightens the second defining clause of `NPCC.bracketGE`
(`⌈n^p y⌉₊ ≤ |C|`, `NPCC/Defs.lean:50--55`), so the family at the larger `y`
is a **subset** of the family at the smaller one, and `comp` -- an infimum over
the family -- can only rise.  The only side condition is that the tighter
family be nonempty, which is `bracketGE.nonempty` at `y' ≤ 1`. -/

/-- **Aux 19a (density monotonicity of `comp<M,1,x,y>`), PROVED.**  At fixed
row density `x` the bracket family is antitone in the retained column density,
so its complexity is monotone.  General in `M`, `x`, `y`, `y'`. -/
theorem Dfamily_mono_in_density {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (M : X' → Y' → Bool) {x y y' : ℝ} (hx1 : x ≤ 1) (hy : y ≤ y') (hy1 : y' ≤ 1)
    (hX : 1 ≤ Fintype.card X') :
    Dfamily (interlaceFun M 1) (bracketGE X' Y' 1 x y)
      ≤ Dfamily (interlaceFun M 1) (bracketGE X' Y' 1 x y') := by
  classical
  have hsub : bracketGE X' Y' 1 x y' ⊆ bracketGE X' Y' 1 x y :=
    bracketGE.anti_mono_params 1 (le_refl x) hy
  have hne : (bracketGE X' Y' 1 x y').Nonempty :=
    bracketGE.nonempty 1 x y' hx1 hy1 hX
  have hS'ne :
      {d : ℕ | ∃ RC ∈ bracketGE X' Y' 1 x y',
          d = D (subgame (interlaceFun M 1) RC.1 RC.2)}.Nonempty := by
    obtain ⟨RC, hRC⟩ := hne
    exact ⟨_, RC, hRC, rfl⟩
  obtain ⟨RC, hRC, hval⟩ := Nat.sInf_mem hS'ne
  exact le_trans (Nat.sInf_le ⟨RC, hsub hRC, hval⟩) (le_refl _)

/-- **Aux 19b (density monotonicity of the three-rung quantity), PROVED.**
`Lambda_3` is a minimum of three bracket complexities at the coupled densities
`y, y/2, y/4`, each of which is monotone by `Dfamily_mono_in_density`. -/
theorem LambdaGE_mono_in_density {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (M : X' → Y' → Bool) {x y y' : ℝ} (hx1 : x ≤ 1) (hy : y ≤ y') (hy1 : y' ≤ 1)
    (hX : 1 ≤ Fintype.card X') :
    LambdaGE M 1 x y ≤ LambdaGE M 1 x y' := by
  unfold LambdaGE
  refine min_le_min (Dfamily_mono_in_density M hx1 hy hy1 hX)
    (min_le_min (Nat.add_le_add_left ?_ 1) (Nat.add_le_add_left ?_ 2))
  · exact Dfamily_mono_in_density M hx1 (by linarith) (by linarith) hX
  · exact Dfamily_mono_in_density M hx1 (by linarith) (by linarith) hX

/-- **Aux 19c (`Lambda_3` bounds its own top rung).**  `Lambda_3` is a minimum
whose first argument is `comp<M,1,x,y>`, so any lower bound on `Lambda_3` is a
lower bound on that bracket complexity.  This is the step `07:340--341` uses to
read clause (i) off `eq:stage2-one-depth-base`. -/
theorem LambdaGE_le_top_rung {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (M : X' → Y' → Bool) (x y : ℝ) :
    LambdaGE M 1 x y ≤ Dfamily (interlaceFun M 1) (bracketGE X' Y' 1 x y) :=
  min_le_left _ _

/-! ## §6  The Extension comparisons of `eq:stage2-one-depth-extension`

`07:293--302`, and `eq:stage2-two-depth-comparisons` (`07:232--243`), which is
the same pair of comparisons instantiated at the two scheduled depths.  Reader
`eq:paper-stage2-extension-gates` (`03-parameterized-construction.tex:338--346`)
and `eq:paper-M2-depth-gates` (`03-parameterized-construction.tex:417--429`). -/

/-- **`eq:stage2-one-depth-extension`.**  The two literal Extension
comparisons at retained column density `h` and balancedness error `eps`:
```
( h 2^{-(log_2 q_2 + B_cap)} / (1 + eps_2) )^{1/t_2}  >=  3/5,
  h 2^{-(log_2 t_2 + B_cap)} / (1 + eps_2)            >=  h_2^seed.
```
`log_2 q_2 = r_2` and `log_2 t_2 = k_2` are exact
(`StageTwoWidths.log_q₂`, `StageTwoWidths.log_t₂`). -/
def extensionComparisons (W : StageTwoWidths) (bCapVal : ℕ) (h ε : ℝ) : Prop :=
  3 / 5 ≤ yLoss ε W.t₂ h (W.r₂ + bCapVal) ∧
    hSeedTwo W.k₂ ≤ h * (2 : ℝ) ^ (-((W.k₂ + bCapVal : ℕ) : ℝ)) / (1 + ε)

/-- **`eq:stage2-two-depth-comparisons`** (`07:232--243`): the schedule
verifies the pair for each `h in {2^{-b_2}, 2^{-b_T}}`, with *all other data,
including the indexed family, unchanged* (`07:420--421`).  Reader
`eq:paper-M2-depth-gates`. -/
def twoDepthComparisons (W : StageTwoWidths) (bCapVal : ℕ) (ε : ℝ) (b₂ bT : ℕ) :
    Prop :=
  extensionComparisons W bCapVal (xSeed b₂) ε ∧
    extensionComparisons W bCapVal (xSeed bT) ε

/-- **Aux 20 (the two calls differ only in the depth).**  The frozen sentence
"all other data, including the indexed family `C_2`, are unchanged"
(`07:421`) is typed: `twoDepthComparisons` mentions one `W`, one
`bCapVal` and one `ε`, and its two conjuncts are the *same* predicate at two
depths. -/
theorem twoDepthComparisons_iff (W : StageTwoWidths) (bCapVal : ℕ) (ε : ℝ)
    (b₂ bT : ℕ) :
    twoDepthComparisons W bCapVal ε b₂ bT ↔
      (∀ b : ℕ, b = b₂ ∨ b = bT → extensionComparisons W bCapVal (xSeed b) ε) := by
  constructor
  · rintro ⟨h₂, hT⟩ b (rfl | rfl)
    · exact h₂
    · exact hT
  · intro h
    exact ⟨h b₂ (Or.inl rfl), h bT (Or.inr rfl)⟩

/-- **The frozen column-loss-resilience input, PROVED from the first
comparison.**

`07:337--340`: "The first comparison says `y_{log_2 q_2 + B_cap} >= 3/5`.
Since `y_c` decreases with `c`, every `c <= T + k`, `k <= B_cap`, also
satisfies `y_c >= 3/5`; moreover `0 < y_c <= 1`."  Here `T = k_2`, and
`k_2 <= r_2` is banked, so `c <= k_2 + k <= r_2 + B_cap`. -/
theorem columnLossResilience_inputs (W : StageTwoWidths) (bCapVal : ℕ)
    {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (hext : extensionComparisons W bCapVal h ε)
    {c k : ℕ} (hk : k ≤ bCapVal) (hc : c ≤ W.k₂ + k) :
    3 / 5 ≤ yLoss ε W.t₂ h c ∧ 0 < yLoss ε W.t₂ h c ∧ yLoss ε W.t₂ h c ≤ 1 := by
  refine ⟨?_, yLoss_pos_of_pos hh0 hε _ _, yLoss_le_one_of_le_one hh0 hh1 hε _ _⟩
  have hcle : c ≤ W.r₂ + bCapVal := by
    have := W.k₂_le_r₂
    omega
  exact le_trans hext.1 (yLoss_antitone_in_c hh0 hε W.t₂ hcle)

/-- **Both frozen clauses of the INHERITED contract, PROVED at the Stage-2 call
site** (`07:332--349`).

The predicate is the vendored `NPCC.IsColumnLossResilient`
(`vendor/npc-cc/NPCC/Transfer.lean:41`), which is `eq:contract-column-loss`
(`D-inherited-contracts.tex:653--666`) literally:
```
(i)   comp<M, 1, 2^{-b}, y_{Q + comp M}(h)>  >=  1,
(ii)  Lambda_3(M, 1, 2^{-b}, y_c(h))         >=  comp M - k
      for all  k <= comp M  and  c <= T + k.
```
Nothing is transcribed here: the predicate is consumed by pin, and what this
declaration does is *discharge* it.

**Exponent binders, named rather than recovered.**  `07:348--349` closes the
verification with "These are exactly clauses (i) and (ii) of the inherited
column-loss-resilience predicate with exponent binders `(R + T, T)`", and the
frozen dictionary of `07:314--319` is `T = k_2`, `R = log_2(q_2/t_2)`,
`q_2 = 2^{R+T}`.  So `Q = R + T = r_2`, `T = k_2`, `b = b_1`, and those three
naturals are passed *as exponents*, never recovered from `q_2`, `t_2` by
`Nat.log`.  `D-inherited-contracts.tex:755--757` is explicit that recording
divisibility instead of naming the exponents does not discharge the contract.

The frozen derivation is: the first Extension comparison gives
`y_{log_2 q_2 + B_cap} >= 3/5`; `y_c` decreases in `c`, so every legal `c`
also has `y_c >= 3/5`; then "density monotonicity and
`eq:stage2-one-depth-base`" give the two clauses.  Every one of those steps is
a theorem here -- `columnLossResilience_inputs`, `Dfamily_mono_in_density`,
`LambdaGE_mono_in_density`, `LambdaGE_le_top_rung` -- so the contract is
discharged with **no** binder beyond the frozen base clauses `hbase`,
`hthree`, `hrobust` and the frozen comparison `hext`. -/
theorem columnLossResilience_holds (W : StageTwoWidths) (bCapVal : ℕ)
    {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (hext : extensionComparisons W bCapVal h ε)
    (F : Stage1SlotBinding) (R : X → Y → Bool) [Fintype X] [Fintype Y]
    (hcard : 1 ≤ Fintype.card (Stage1Cols F Y))
    (hbase : D (stageOneT F R) = bCapVal) (hthree : 3 ≤ bCapVal)
    (hrobust : bCapVal ≤ LambdaGE (stageOneT F R) 1 (xSeed W.b₁) (3 / 5)) :
    NPCC.IsColumnLossResilient (stageOneT F R) (W.b₁ : ℝ) ε W.r₂ W.k₂ h := by
  have hx1 : xSeed W.b₁ ≤ 1 := xSeed_le_one W.b₁
  have clauseI : 1 ≤ Dfamily (interlaceFun (stageOneT F R) 1)
      (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed W.b₁)
        (yLoss ε W.t₂ h (W.r₂ + D (stageOneT F R)))) := by
    rw [hbase]
    have hy : (3 : ℝ) / 5 ≤ yLoss ε W.t₂ h (W.r₂ + bCapVal) := hext.1
    have hy1 : yLoss ε W.t₂ h (W.r₂ + bCapVal) ≤ 1 :=
      yLoss_le_one_of_le_one hh0 hh1 hε _ _
    have hmono := Dfamily_mono_in_density (stageOneT F R) (x := xSeed W.b₁)
      (y := 3 / 5) (y' := yLoss ε W.t₂ h (W.r₂ + bCapVal)) hx1 hy hy1 hcard
    have htop := LambdaGE_le_top_rung (stageOneT F R) (xSeed W.b₁) (3 / 5)
    omega
  have clauseII : ∀ k ≤ D (stageOneT F R), ∀ c ≤ W.k₂ + k,
      D (stageOneT F R) - k ≤
        LambdaGE (stageOneT F R) 1 (xSeed W.b₁) (yLoss ε W.t₂ h c) := by
    intro k hk c hc
    rw [hbase] at hk ⊢
    obtain ⟨hy, -, hy1⟩ :=
      columnLossResilience_inputs W bCapVal hh0 hh1 hε hext hk hc
    have hmono := LambdaGE_mono_in_density (stageOneT F R) (x := xSeed W.b₁)
      (y := 3 / 5) (y' := yLoss ε W.t₂ h c) hx1 hy hy1 hcard
    omega
  exact And.intro clauseI clauseII

/-- **The same contract in the exact shape the Appendix-D endpoints bind.**

`NPCC.extension_theorem` (`vendor/npc-cc/NPCC/Transfer.lean:807`) and
`NPCC.localized_extension` (`:839`) both bind
`hres : IsColumnLossResilient f b eps (R + T) T h`, with `R` the *row* exponent
of the ambient width.  At the Stage-2 call site `07:314--319` fixes
`T = k_2` and `R = log_2(q_2/t_2) = r_2 - k_2`, so `R + T = r_2` on the nose --
using the width record's `k_2 + 2 <= r_2` to make the natural subtraction
exact.  This corollary is what turns "the column-loss input typechecks into the
inherited endpoints" from prose into a theorem; without it the claim would be
unchecked (that was the round-1 defect).  Nothing else changes: it is
`columnLossResilience_holds` with `Q` written in `(R + T)` form. -/
theorem columnLossResilience_at_endpoint_binders (W : StageTwoWidths)
    (bCapVal : ℕ) {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (hext : extensionComparisons W bCapVal h ε)
    (F : Stage1SlotBinding) (R : X → Y → Bool) [Fintype X] [Fintype Y]
    (hcard : 1 ≤ Fintype.card (Stage1Cols F Y))
    (hbase : D (stageOneT F R) = bCapVal) (hthree : 3 ≤ bCapVal)
    (hrobust : bCapVal ≤ LambdaGE (stageOneT F R) 1 (xSeed W.b₁) (3 / 5)) :
    NPCC.IsColumnLossResilient (stageOneT F R) (W.b₁ : ℝ) ε
      ((W.r₂ - W.k₂) + W.k₂) W.k₂ h := by
  have hRT : (W.r₂ - W.k₂) + W.k₂ = W.r₂ := by
    have := W.k₂_add_two_le_r₂
    omega
  rw [hRT]
  exact columnLossResilience_holds W bCapVal hh0 hh1 hε hext F R hcard hbase
    hthree hrobust

/-! ## §7  The General Hard Seed call `eq:stage2-one-depth-seed`

`07:319--330`.  The call is at `(j, delta, m) = (5, 1/10, k_2)`, "legal because
`k_2 >= m_HS`, `T <= b_1`, and `B_cap >= 3`". -/

/-- **The three legality clauses of the hard-seed call, PROVED from the width
record and the frozen base clause `B_cap >= 3`** (`07:320--321`).  `T = k_2`,
and `T <= b_1` is the derived `t₂_le_two_pow_b₁` read at exponents. -/
theorem stageTwoSeedCall_legal (W : StageTwoWidths) {bCapVal : ℕ}
    (hthree : 3 ≤ bCapVal) : W.mHS ≤ W.k₂ ∧ W.k₂ ≤ W.b₁ ∧ 3 ≤ bCapVal := by
  refine ⟨W.mHS_le_k₂, ?_, hthree⟩
  have h : (2:ℕ) ^ W.k₂ ≤ 2 ^ W.b₁ := W.t₂_le_two_pow_b₁
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

/-- **`eq:stage2-one-depth-seed`, read off from one legal width record.**

The inherited General Hard Seed corollary `eq:contract-hard-seed` is the named
binder `hardSeed`; the content here is the frozen *identification* of its
conclusion with `B_cap + T = B_cap + log_2 t_2` (`07:325`), which is where the
independence width enters the Stage-2 bookkeeping. -/
theorem stageTwoSeedCall_conclusion {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (W : StageTwoWidths) (M : X' → Y' → Bool) (bCapVal : ℕ)
    (hardSeed : bCapVal + W.k₂ ≤
      Dfamily (interlaceFun M (pSeedTwo W.k₂))
        (bracketGE X' Y' (pSeedTwo W.k₂) ((W.t₂ : ℝ) * xSeed W.b₁)
          (hSeedTwo W.k₂))) :
    bCapVal + Nat.log 2 W.t₂ ≤
      Dfamily (interlaceFun M (pSeedTwo W.k₂))
        (bracketGE X' Y' (pSeedTwo W.k₂) ((W.t₂ : ℝ) * xSeed W.b₁)
          (hSeedTwo W.k₂)) := by
  rwa [W.log_t₂]

/-- The frozen Localized Extension column shift `a = 0` of `07:376`.  The
inherited contract binds `a` with the guard `a <= 1`
(`D-inherited-contracts.tex:722`); the Stage-2 call fixes it at `0`, which is
what makes the contract's column clause `h 2^{-a} L <= |C|`
(`eq:contract-localized-rectangle`, `D:733`) literal rather than lossy. -/
def localizedExtensionShift : ℕ := 0

/-- **`a = 0` makes the localized column clause literal.**  With the frozen
shift the contract's `h 2^{-a} L` is `h L` on the nose, so no column density
is silently spent at the call. -/
@[simp] theorem localizedExtension_column_shift_literal (h : ℝ) :
    h * (2 : ℝ) ^ (-((localizedExtensionShift : ℕ) : ℝ)) = h := by
  simp [localizedExtensionShift]

/-- **The complete Localized Extension call record** of `07:370--379`, with
*both* guards the parked draft dropped.

`eq:contract-extension-exponents` (`D-inherited-contracts.tex:747--754`)
demands, at every active call with independence width `t_2`, ambient width
`q_amb` and represented capacity `K`, named naturals `(T, R, R_loc)` with
```
t_2 = 2^T,     q_amb = 2^{R+T},     K = 2^{R_loc+T},     R_loc <= R,
```
and `D:755--757` says outright that recording only `t_2 | q_amb` and
`t_2 | K` does **not** discharge it.  `07:370--376` names
`(T, R, R_loc) = (k_2, log_2(q_2/t_2), log_2(K_j/t_2))` and `a = 0`, and
`D:721--722` binds `a <= 1`.

All seven clauses are exact at every legal width record and every `j <= 2`.
The last two are the frozen *represented-capacity* readings
`2^{R+T} = q_2` and `2^{R_loc+T} = K_j` in exponent form (`07:377--378`). -/
theorem localizedExtension_binders (W : StageTwoWidths) {j : ℕ} (hj : j ≤ 2) :
    W.t₂ = 2 ^ W.k₂ ∧
      2 ^ ((W.r₂ - W.k₂) + W.k₂) = W.q₂ ∧
        2 ^ ((W.r₂ - W.k₂ - j) + W.k₂) = Kseed W j ∧
          W.r₂ - W.k₂ - j ≤ W.r₂ - W.k₂ ∧
            localizedExtensionShift = 0 ∧ localizedExtensionShift ≤ 1 ∧
              (W.r₂ - W.k₂) + W.k₂ = W.r₂ ∧
                (W.r₂ - W.k₂ - j) + W.k₂ = W.r₂ - j := by
  have h := W.k₂_add_two_le_r₂
  refine ⟨rfl, ?_, ?_, by omega, rfl, by norm_num [localizedExtensionShift],
    by omega, by omega⟩
  · simp only [StageTwoWidths.q₂]; congr 1; omega
  · simp only [Kseed]; congr 1; omega

/-- **The two dropped guards, isolated.**  Stated on their own so that a
consumer can see that `R_loc <= R` is a *strict* consequence of the rung
offset (`R_loc = R - j`) and that the frozen shift really is `0`, not merely
`<= 1`.  At `j = 0` the localized call degenerates to the ambient one, which
is the frozen `K_0 = q_2` reading. -/
theorem localizedExtension_guards (W : StageTwoWidths) {j : ℕ} (hj : j ≤ 2) :
    W.r₂ - W.k₂ - j ≤ W.r₂ - W.k₂ ∧ localizedExtensionShift ≤ 1 ∧
      (j = 0 → W.r₂ - W.k₂ - j = W.r₂ - W.k₂) ∧
      (1 ≤ j → j ≤ W.r₂ - W.k₂ → W.r₂ - W.k₂ - j < W.r₂ - W.k₂) := by
  have h := W.k₂_add_two_le_r₂
  exact ⟨by omega, by norm_num [localizedExtensionShift], by omega, by omega⟩

/-! ## §8  The selector upper bound and the certified Stage-2 scale

`07:386--390` and `eq:stage2-one-depth-output` (`07:304--310`).  Reader
`eq:paper-M2-exact` (`03-parameterized-construction.tex:431--435`). -/

/-- The Stage-2 certified scale `D_2 = B_cap + log_2 q_2`
(`eq:stage2-two-depth-certificate`, `07:422`).

Like `bCap`, it is a function of two public integers alone: no matrix, no
promise certificate and no protocol enters its definition (`M9`). -/
def dTwo (bCapVal r₂ : ℕ) : ℕ := bCapVal + r₂

@[simp] theorem dTwo_eq (bCapVal r₂ : ℕ) : dTwo bCapVal r₂ = bCapVal + r₂ := rfl

/-- **The upper half of the Stage-2 scale, PROVED.**
`comp(M_2) <= comp(M_1^T) + log_2 q_2`.

Nothing here is a hypothesis: the banked `lem:indexed-selector-protocol`
(`PilotStage3.relaxedInterlace_selector_upper`) is consumed by pin at the
index type `L_2` and the accessor `c(l) = c^{(l)}`, and
`StageTwoWidths.clog_q₂` turns the selector's `ceil(log_2 q_2)` into the
frozen `r_2`, which is the exact bit count of `07:389--390`. -/
theorem stageTwo_selector_upper (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype X] [Fintype Y] :
    D (stageTwo F R W Pr) ≤ D (stageOneT F R) + W.r₂ := by
  have h := relaxedInterlace_selector_upper (stageOneT F R) W.q₂_pos Pr.c₂
  rw [W.clog_q₂] at h
  exact h

/-- **The ambient lower bound of `07:386`, PROVED from the `j = 0` rung.**

The frozen sentence is "The rung `j = 0` lower-bounds the full matrix by
`B_cap + log_2 q_2`".  It is a *derivation*, not an assumption: the rung is a
bound on `comp<M_2^T, 1, h, beta_0>`, the infimum over a **nonempty** family
of restrictions of the one-copy interlace of `M_2^T`; that infimum is at most
the ambient `comp` of the interlace (`PilotStage3.familyComplexity_le_ambient`),
which is at most `comp(M_2^T)` itself (`PilotStage3.interlace_selector_upper`
at `p = 1`, where `clog_2 1 = 0`); and `comp(M_2^T) = comp(M_2)` by the checked
`NPCC.comp_transpose`.

*Repair note (round 1).*  The parked draft carried this conclusion as the
binder `hlower` on `stageTwoOneDepth`, which duplicated that theorem's own
first conjunct.  It is now discharged, and `hh1 : h <= 1` -- the tell that the
parked derivation used nothing -- is exactly what the nonemptiness of the
bracket family needs. -/
theorem stageTwo_ambient_lower (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype Y] (bCapVal : ℕ) {h : ℝ} (hh1 : h ≤ 1)
    (rung₀ : bCapVal + (W.r₂ - 0) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 0))) :
    bCapVal + W.r₂ ≤ D (stageTwo F R W Pr) := by
  classical
  have hcard : 1 ≤ Fintype.card (Slot Pr.N₂) := by
    rw [stageTwo_cols_card Pr]; exact Pr.N₂pos
  have hβ : betaSeed 0 ≤ 1 := by rw [betaSeed_zero]; norm_num
  have hne : (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y)
      1 h (betaSeed 0)).Nonempty :=
    bracketGE.nonempty 1 h (betaSeed 0) hh1 hβ hcard
  have hfam := familyComplexity_le_ambient (interlaceFun (stageTwoT F R W Pr) 1) hne
  have hone : D (interlaceFun (stageTwoT F R W Pr) 1) ≤ D (stageTwoT F R W Pr) := by
    have h1 := interlace_selector_upper (stageTwoT F R W Pr) 1 (le_refl 1)
    rwa [Nat.clog_one_right, Nat.add_zero] at h1
  have hT := D_stageTwoT F R W Pr
  omega

/-- **`eq:stage2-one-depth-output` line 1 and `eq:paper-M2-exact`.**

`comp(M_2) = B_cap + log_2 q_2`.

The upper half is proved (`stageTwo_selector_upper`).  Exactly **two** named
binders remain, and neither is an axiom:

* `hbase` -- the frozen base clause `comp(M_1^T) = B_cap` of
  `eq:stage2-one-depth-base` (`07:269`);
* `hlower` -- the frozen line 357, "The rung `j = 0` lower-bounds the full
  matrix by `B_cap + log_2 q_2`", which is the Localized Extension endpoint at
  `j = 0` promoted to the ambient matrix.

What this theorem contributes beyond the two halves is the exact arithmetic of
`07:389--390`: the selector's `ceil(log_2 q_2)` is *equal* to `r_2`, so the two
halves close with no slack at all. -/
theorem stageTwo_scale_eq_dTwo (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype X] [Fintype Y] (bCapVal : ℕ)
    (hbase : D (stageOneT F R) = bCapVal)
    (hlower : bCapVal + W.r₂ ≤ D (stageTwo F R W Pr)) :
    D (stageTwo F R W Pr) = dTwo bCapVal W.r₂ := by
  have hupper := stageTwo_selector_upper F R W Pr
  rw [hbase] at hupper
  exact Nat.le_antisymm hupper hlower

/-- **Statement pole for the `YES` side (`M9`).**  `D_2` is *not* a claim
about `comp(M_2)`: at the declared legal bindings and the legal constant
source matrix, `comp(M_2) = 0` while `D_2 = 7`.  So the lower-bound hypothesis
of `stageTwo_scale_eq_dTwo` is genuine content and can fail off the `NO`
branch, exactly as the Stage-1 caveat of `07:158` says of `B_cap`. -/
theorem dTwo_is_not_a_complexity_claim (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows stage1Legal Bool) W.q₂) :
    D (stageTwo stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr) = 0 ∧
      dTwo 0 7 = 7 := by
  refine ⟨?_, rfl⟩
  have hconst : (stageTwo stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
      = fun (_ : Slot W.q₂ × Stage1Cols stage1Legal Bool)
            (_ : Slot Pr.N₂) => false := rfl
  rw [hconst]
  exact PublicRecords.D_const false

/-! ## §9  The one-depth Stage-2 certificate `lem:stage2-one-depth`

`07-one-level-construction.tex:265--311`, reader
`lem:paper-stage2-one-depth` (`03-parameterized-construction.tex:306--358`). -/

/-- **Aux 21 (no theorem adds bits).**  The frozen bookkeeping of `07:383`
made checkable: the `Lambda_3` offsets `+1` and `+2` exactly cancel the losses
`-1` and `-2` of the rungs `j = 1, 2`, so all three transported bounds land on
the *same* value `D_2 = B_cap + log_2 q_2`. -/
theorem noBitsAddedTwo (bCapVal r₂ : ℕ) (hr : 2 ≤ r₂) :
    bCapVal + (r₂ - 0) = dTwo bCapVal r₂ ∧
      1 + (bCapVal + (r₂ - 1)) = dTwo bCapVal r₂ ∧
        2 + (bCapVal + (r₂ - 2)) = dTwo bCapVal r₂ := by
  refine ⟨by simp [dTwo], ?_, ?_⟩ <;> simp only [dTwo] <;> omega

/-- **`eq:stage2-one-depth-output` line 2.**

From the three *independently transported* target-rung bounds of `07:354--384`,
```
comp <M_2^T, 1, h, beta_j>  >=  B_cap + log_2 K_j = B_cap + log_2 q_2 - j
```
for `j = 0, 1, 2`, the three-rung quantity satisfies
`Lambda_3(M_2^T, 1, h, 3/5) >= D_2`.

The three hypotheses are **named binders**: each is the endpoint of one
Localized Extension call (`07:369--379`), whose `EquipGE` witness is supplied by block
balancing at within-fibre density `xi_j` -- and the gates that call needs are
the *proved* `balanceCeilings_hold`, not further hypotheses.  The column
densities `beta_j` are matched to the `Lambda_3` rungs `y, y/2, y/4` at
`y = 3/5` by the banked `betaSeed_one`/`betaSeed_two`.

Reader `eq:paper-stage2-one-depth-conclusion`
(`03-parameterized-construction.tex:348--354`). -/
theorem stageTwoOneDepth_output (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype Y] (bCapVal : ℕ) (h : ℝ)
    (rung₀ : bCapVal + (W.r₂ - 0) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 0)))
    (rung₁ : bCapVal + (W.r₂ - 1) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 1)))
    (rung₂ : bCapVal + (W.r₂ - 2) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 2))) :
    dTwo bCapVal W.r₂ ≤ LambdaGE (stageTwoT F R W Pr) 1 h (3 / 5) := by
  have hr : 2 ≤ W.r₂ := by have := W.seven_le_r₂; omega
  obtain ⟨e₀, e₁, e₂⟩ := noBitsAddedTwo bCapVal W.r₂ hr
  have h₀ : dTwo bCapVal W.r₂ ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (3 / 5)) := by
    rw [← e₀, ← betaSeed_zero]; exact rung₀
  have h₁ : dTwo bCapVal W.r₂ ≤
      1 + Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (3 / 5 / 2)) := by
    rw [← e₁]
    have hb : (3 / 5 / 2 : ℝ) = betaSeed 1 := by rw [betaSeed_one, betaSeed_zero]
    rw [hb]
    omega
  have h₂ : dTwo bCapVal W.r₂ ≤
      2 + Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (3 / 5 / 4)) := by
    rw [← e₂]
    have hb : (3 / 5 / 4 : ℝ) = betaSeed 2 := by rw [betaSeed_two, betaSeed_zero]
    rw [hb]
    omega
  unfold LambdaGE
  exact le_min h₀ (le_min h₁ h₂)

set_option linter.unusedVariables false in
/-- **`lem:stage2-one-depth`** (`07-one-level-construction.tex:265--311`),
reader `lem:paper-stage2-one-depth`
(`03-parameterized-construction.tex:306--358`).

The frozen hypothesis set is carried in full and in the frozen order:
`h in (0,1]`; the base `eq:stage2-one-depth-base`; the power, depth and
balance conditions `eq:stage2-balance-ceilings` (as the width record `W`,
whose remaining clauses are the *proved* `balanceCeilings_hold`); the
statement that `C_2` is the indexed `(q_2, t_2, eps_2)`-balanced family
defining `M_2` through `eq:stage2-relaxed-value`; and the two Extension
comparisons `eq:stage2-one-depth-extension`.  The conclusion is
`eq:stage2-one-depth-output` verbatim.

*Scope, restated here because a green build cannot show it.*  The Lean
derivation of the conclusion consumes `hbase`, `hh1` and the three rung
binders.  `hcard` is the frozen standing assumption that the source column
carrier is inhabited.  `hbal`, `hext`, `hthree`, `hh0` and `hε` are carried
because the frozen lemma states them and because the three rung binders are
exactly the endpoints those hypotheses feed in the *human* proof; what they
buy in Lean is checked separately and non-trivially by
`stageTwoOneDepth_carried_hypotheses_fire`, which turns them into the complete
inherited column-loss-resilience record and the hard-seed call legality.  The
unused-variable linter is switched off for this declaration for that reason,
and for no other.

*Repair note (round 1).*  The parked draft additionally carried
`hlower : B_cap + log_2 q_2 <= comp(M_2)`, which is the first conjunct of its
own conclusion.  `07:386--389` derives that from the `j = 0` rung, and
`stageTwo_ambient_lower` now does so here, consuming `hh1` in the process.

*Trivial-witness pole.*  The `Lambda_3` half is a lower bound on a `min`, so
it is not satisfiable by a degenerate reading:
`stageTwoOneDepth_not_automatic` exhibits a legal binding and a legal matrix
at which `Lambda_3(M_2^T, 1, h, 3/5) = 0 < D_2`, so the three rung binders do
real work; `stageTwoOneDepth_tight` shows the bound is attained, so none of
them is over-strong. -/
theorem stageTwoOneDepth (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype X] [Fintype Y] [DecidableEq X] (bCapVal : ℕ) (h ε : ℝ)
    -- `h in (0,1]` and the balancedness error is a legal tolerance
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    -- the source column carrier is inhabited (`03:167--172`, the standing
    -- finiteness convention that makes every bracket family nonempty)
    (hcard : 1 ≤ Fintype.card (Stage1Cols F Y))
    -- `eq:stage2-one-depth-base` (`07:268--274`)
    (hbase : D (stageOneT F R) = bCapVal)
    (hrobust : bCapVal ≤ LambdaGE (stageOneT F R) 1 (xSeed W.b₁) (3 / 5))
    (hthree : 3 ≤ bCapVal)
    -- "`C_2` is the indexed `(q_2, t_2, eps_2)`-balanced family defining
    -- `M_2` through `eq:stage2-relaxed-value`" (`07:290--292`)
    (hbal : IsBalancedFamily W.t₂ Pr.c₂ ε)
    -- `eq:stage2-one-depth-extension` (`07:293--302`)
    (hext : extensionComparisons W bCapVal h ε)
    -- the three Localized Extension endpoints of `07:354--384`
    (rung₀ : bCapVal + (W.r₂ - 0) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 0)))
    (rung₁ : bCapVal + (W.r₂ - 1) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 1)))
    (rung₂ : bCapVal + (W.r₂ - 2) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (betaSeed 2))) :
    D (stageTwo F R W Pr) = dTwo bCapVal W.r₂ ∧
      dTwo bCapVal W.r₂ ≤ LambdaGE (stageTwoT F R W Pr) 1 h (3 / 5) :=
  ⟨stageTwo_scale_eq_dTwo F R W Pr bCapVal hbase
      (stageTwo_ambient_lower F R W Pr bCapVal hh1 rung₀),
    stageTwoOneDepth_output F R W Pr bCapVal h rung₀ rung₁ rung₂⟩

/-- **What the carried hypotheses of `stageTwoOneDepth` buy.**

`hh0`, `hh1`, `hε`, `hext`, `hbase`, `hthree`, `hrobust` and `hcard` produce
the *complete* inherited column-loss-resilience contract of `03:313--331` /
`eq:contract-column-loss` -- both clauses, in the shape
`NPCC.extension_theorem` and `NPCC.localized_extension` bind -- and the three
legality clauses of the General Hard Seed call at
`(j, delta, m) = (5, 1/10, k_2)`.  Those are precisely the two inputs the
frozen proof verifies "rather than hiding [them] behind `apply Extension`"
(`07:332--333`, `07:319--321`), so no carried hypothesis is decorative. -/
theorem stageTwoOneDepth_carried_hypotheses_fire (F : Stage1SlotBinding)
    (R : X → Y → Bool) (W : StageTwoWidths) [Fintype X] [Fintype Y]
    (bCapVal : ℕ) {h ε : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (hcard : 1 ≤ Fintype.card (Stage1Cols F Y))
    (hbase : D (stageOneT F R) = bCapVal) (hthree : 3 ≤ bCapVal)
    (hrobust : bCapVal ≤ LambdaGE (stageOneT F R) 1 (xSeed W.b₁) (3 / 5))
    (hext : extensionComparisons W bCapVal h ε) :
    NPCC.IsColumnLossResilient (stageOneT F R) (W.b₁ : ℝ) ε
        ((W.r₂ - W.k₂) + W.k₂) W.k₂ h ∧
      (W.mHS ≤ W.k₂ ∧ W.k₂ ≤ W.b₁ ∧ 3 ≤ bCapVal) :=
  ⟨columnLossResilience_at_endpoint_binders W bCapVal hh0 hh1 hε hext F R hcard
      hbase hthree hrobust,
    stageTwoSeedCall_legal W hthree⟩

/-! ### Aux-lemma battery A3: general properties of `NPCC.IsColumnLossResilient`

Five properties, all general in the matrix and in every parameter, all proved.
Each is stated **at the contract's own exponent binders** `Q T : ℕ` and its own
real `b`, `eps` -- so each is a fact about `eq:contract-column-loss`
(`D-inherited-contracts.tex:653--666`) itself, not about a look-alike.

*Repair note (round 2).*  Round 1 stated this battery over a local record at
general *values* `q t : ℕ`, recovering the exponents by `Nat.log 2 q`,
`Nat.log 2 t`.  At general values those two are not the contract's `Q`, `T`, so
the battery was not testing the inherited definition.  Restated here at the
binders; no property was dropped. -/

/-- **Aux B1 (clause (ii) at the top rung).**  Instantiating `(k, c) = (0, 0)`
recovers `comp M <= Lambda_3(M, 1, 2^{-b}, y_0)`: the contract always carries
the full, unweakened three-rung bound at the entering density.  General. -/
theorem columnLossResilient_top_rung {X' Y' : Type*} [Fintype X'] [Fintype Y']
    {M : X' → Y' → Bool} {b ε : ℝ} {Q T : ℕ} {h : ℝ}
    (hres : NPCC.IsColumnLossResilient M b ε Q T h) :
    D M ≤ LambdaGE M 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h 0) := by
  obtain ⟨-, hii⟩ := hres
  have := hii 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  simpa using this

/-- **Aux B2 (clause (ii) weakens as `k` grows).**  The frozen bound
`comp M - k` is antitone in `k`, so the `k`-indexed family of clauses is a
genuine descending ladder and not a repetition.  General. -/
theorem columnLossResilient_clause_ii_antitone {X' Y' : Type*} [Fintype X']
    [Fintype Y'] {M : X' → Y' → Bool} {b ε : ℝ} {Q T : ℕ} {h : ℝ}
    (hres : NPCC.IsColumnLossResilient M b ε Q T h) {k k' c : ℕ} (hkk : k ≤ k')
    (hk' : k' ≤ D M) (hc : c ≤ T + k) :
    D M - k' ≤ LambdaGE M 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h c) := by
  obtain ⟨-, hii⟩ := hres
  have hcle : c ≤ T + k' := by omega
  exact hii k' hk' c hcle

/-- **Aux B3 (clause (i) is independent of clause (ii)).**  When `comp M = 0`
every instance of clause (ii) is trivial, yet clause (i) still asserts
`comp<M, 1, 2^{-b}, y_{Q + comp M}> >= 1`.  So the contract is *not*
equivalent to its second clause, which is exactly why `eq:contract-column-loss`
prints both and why omitting clause (i) weakens the input.  General. -/
theorem columnLossResilient_clause_ii_trivial_at_zero {X' Y' : Type*}
    [Fintype X'] [Fintype Y'] {M : X' → Y' → Bool} (b ε : ℝ) (T : ℕ) (h : ℝ)
    (hM : D M = 0) :
    ∀ k ≤ D M, ∀ c ≤ T + k,
      D M - k ≤ LambdaGE M 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h c) := by
  intro k _ c _
  rw [hM]
  omega

/-- **Aux B4 (clause (i) fails on a constant matrix).**  Together with B3 this
exhibits, in the kernel, a matrix at which clause (ii) holds for every legal
pair and clause (i) fails: the constant matrix has `comp = 0` on every
restriction, so its bracket complexity is `0 < 1`.  Hence the contract is
non-vacuous and its first clause carries content.  General in the carriers and
in every parameter. -/
theorem columnLossResilient_fails_on_constant {X' Y' : Type*} [Fintype X']
    [Fintype Y'] (v : Bool) (b ε : ℝ) (Q T : ℕ) (h : ℝ) :
    ¬ NPCC.IsColumnLossResilient (fun (_ : X') (_ : Y') => v) b ε Q T h := by
  intro hres
  obtain ⟨hzero, -⟩ := hres
  have hI : interlaceFun (fun (_ : X') (_ : Y') => v) 1
      = fun (_ : Fin 1 × X') (_ : Fin 1 → Y') => v := rfl
  rw [hI, Dfamily_const] at hzero
  omega

/-- **Aux B5 (the contract transports along equal matrices).**  A round-trip
property: `NPCC.IsColumnLossResilient` depends on the matrix only through its
values, so replacing it by a pointwise-equal matrix preserves it.  General. -/
theorem columnLossResilient_congr {X' Y' : Type*} [Fintype X'] [Fintype Y']
    {M M' : X' → Y' → Bool} (hMM : M = M') {b ε : ℝ} {Q T : ℕ} {h : ℝ}
    (hres : NPCC.IsColumnLossResilient M b ε Q T h) :
    NPCC.IsColumnLossResilient M' b ε Q T h := by
  subst hMM
  exact hres

/-! ### A nondegenerate inhabitant of the inherited contract (LANE-GATE 3)

`columnLossResilience_holds` discharges `eq:contract-column-loss` *relative to*
the Stage-1 premises `hbase`, `hrobust`, `hthree`, none of which is witnessed
at a concrete matrix anywhere in this module (coverage limit 1).  A green
derivation from unwitnessed premises is not a non-vacuity check, so the
contract is separately **inhabited outright** below, at a concrete matrix and
at parameter values that satisfy every range condition the vendored docstring
lists as a use-site hypothesis (`Transfer.lean:16--18`) --
`1 <= b`, `t = 2^T <= 2^b`, `q = 2^Q >= t`, `h in (0,1]`, `0 <= eps` -- with a
**strictly positive** balancedness error and a **strictly positive** depth, so
it is not the degenerate `h = 1`, `eps = 0` corner.

The inhabitant is deliberately *not* a Stage-2 object: it certifies that the
inherited predicate is satisfiable, not that Stage 2 satisfies it.  Reading it
as a Stage-2 fact would be reading something that is not here. -/

/-- Bob's projection on `Bool`, the one-bit source used by the inhabitant.  Its
column carrier is what the contract's density clause constrains, which is why
this and not Alice's projection: at a legal row density `2^{-b}` with `b >= 1`
the row condition of `def:bracket` keeps only *some* row, while the column
condition at `y > 1/2` keeps *both* column tuples. -/
def bobBit : Bool → Bool → Bool := fun _ y => y

/-- `comp` of Bob's projection is exactly `1`, by transposing the banked
`OneLevelCompletion.D_aliceBit` through the vendored `NPCC.comp_transpose`. -/
theorem D_bobBit : D bobBit = 1 := by
  show D (fun (_ : Bool) (y : Bool) => y) = 1
  exact (comp_transpose (fun x _ : Bool => x)).trans
    EthInapproximability.ParameterizedNP.OneLevelCompletion.D_aliceBit

/-- **The one-copy family of `bobBit` is nontrivial above column density
`1/2`.**  At `y > 1/2` the column threshold `⌈2y⌉₊ >= 2` forces every bracket
member to keep two distinct column tuples of `Fin 1 -> Bool`, which differ at
the unique coordinate; the row threshold `⌈2x⌉₊ >= 1` at `x > 0` keeps the row
set nonempty.  So every induced subgame reads both Boolean values and is
nonconstant.  Nonemptiness of the family is taken from `bracketGE.nonempty`
first, because `Dfamily` is a `Nat.sInf` and would report `0` on the empty
family.  General in both densities. -/
theorem one_le_Dfamily_bobBit {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : 1 / 2 < y) (hy1 : y ≤ 1) :
    1 ≤ Dfamily (interlaceFun bobBit 1) (bracketGE Bool Bool 1 x y) := by
  classical
  have hne : (bracketGE Bool Bool 1 x y).Nonempty :=
    bracketGE.nonempty 1 x y hx1 hy1 (by simp)
  have hall : ∀ RC ∈ bracketGE Bool Bool 1 x y,
      1 ≤ D (subgame (interlaceFun bobBit 1) RC.1 RC.2) := by
    rintro ⟨Rs, Cs⟩ hRC
    obtain ⟨hrow, hcol⟩ := hRC
    simp only at hrow hcol
    have hrow0 := hrow (0 : Fin 1) (Finset.mem_univ _)
    have hthrR : 1 ≤ ⌈(Fintype.card Bool : ℝ) * x⌉₊ := by
      have hpos : ((0 : ℕ) : ℝ) < (Fintype.card Bool : ℝ) * x := by
        rw [Fintype.card_bool]
        push_cast
        linarith
      have := Nat.lt_ceil.2 hpos
      omega
    have hRne : Rs.Nonempty := by
      have h1 : 0 < (Rs.filter (fun p => p.1 = (0 : Fin 1))).card := by omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp h1
      exact ⟨r, (Finset.mem_filter.mp hr).1⟩
    have hthrC : 2 ≤ ⌈((Fintype.card Bool : ℝ) ^ 1) * y⌉₊ := by
      have hpos : ((1 : ℕ) : ℝ) < ((Fintype.card Bool : ℝ) ^ 1) * y := by
        rw [Fintype.card_bool, pow_one]
        push_cast
        linarith
      have := Nat.lt_ceil.2 hpos
      omega
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne12⟩ :=
      Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) (le_trans hthrC hcol))
    obtain ⟨r, hr⟩ := hRne
    refine EthInapproximability.ParameterizedNP.OneLevelCompletion.one_le_D_of_no_const_value
      _ ?_
    rintro ⟨z, hz⟩
    have h1 : γ₁ r.1 = z := hz ⟨r, hr⟩ ⟨γ₁, hγ₁⟩
    have h2 : γ₂ r.1 = z := hz ⟨r, hr⟩ ⟨γ₂, hγ₂⟩
    refine hne12 (funext fun i => ?_)
    have hi : i = r.1 := Subsingleton.elim i r.1
    rw [hi, h1, h2]
  obtain ⟨RC0, hRC0⟩ := hne
  have hSne : {n : ℕ | ∃ RC ∈ bracketGE Bool Bool 1 x y,
      n = D (subgame (interlaceFun bobBit 1) RC.1 RC.2)}.Nonempty :=
    ⟨_, RC0, hRC0, rfl⟩
  obtain ⟨RC1, hRC1, hEq⟩ := Nat.sInf_mem hSne
  change 1 ≤ sInf _
  rw [hEq]
  exact hall RC1 hRC1

/-- The three-rung form of the previous lemma: `Lambda_3` is a minimum whose
two shifted rungs are `>= 1` for free. -/
theorem one_le_LambdaGE_bobBit {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : 1 / 2 < y) (hy1 : y ≤ 1) :
    1 ≤ LambdaGE bobBit 1 x y := by
  unfold LambdaGE
  exact le_min (one_le_Dfamily_bobBit hx0 hx1 hy hy1)
    (le_min (by omega) (by omega))

/-- **`y_c(h) > 1/2` reduces to one integer-free real comparison.**  The map
`z |-> z^{1/t}` is strictly monotone on the nonnegatives, so `y_c(h) > 1/2`
holds exactly when the inner ratio of `eq:contract-yloss` exceeds `(1/2)^t`.
General in `h`, `eps`, `t`, `c`. -/
theorem half_lt_yLoss_of_pow {h ε : ℝ} (hh0 : 0 < h) (hε : 0 ≤ ε) {t : ℕ}
    (ht : 0 < t) {c : ℕ}
    (hgap : (1 / 2 : ℝ) ^ t < h * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε)) :
    1 / 2 < yLoss ε t h c := by
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  have key : ((1 / 2 : ℝ) ^ t) ^ ((1 : ℝ) / (t : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) t,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2), mul_one_div,
      div_self (ne_of_gt htR), Real.rpow_one]
  unfold yLoss
  calc (1 / 2 : ℝ) = ((1 / 2 : ℝ) ^ t) ^ ((1 : ℝ) / (t : ℝ)) := key.symm
    _ < (h * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε)) ^ ((1 : ℝ) / (t : ℝ)) :=
        Real.rpow_lt_rpow (by positivity) hgap (div_pos (by norm_num) htR)

/-- The one numeric fact the inhabitant needs: at `t = 2^4 = 16`,
`h = 2^{-1}` and `eps = 1/100`, every column-loss depth `c <= 5` still leaves
`y_c(h) > 1/2`.  The gap is wide -- the comparison reduces to
`1 + 1/100 < 2^{10}`. -/
theorem half_lt_yLoss_witness {c : ℕ} (hc : c ≤ 5) :
    1 / 2 < yLoss (1 / 100 : ℝ) (2 ^ 4) (1 / 2 : ℝ) c := by
  refine lt_of_lt_of_le ?_
    (yLoss_antitone_in_c (by norm_num) (by norm_num) (2 ^ 4) hc)
  refine half_lt_yLoss_of_pow (by norm_num) (by norm_num) (by norm_num) ?_
  rw [two_rpow_neg_natCast]
  norm_num

/-- **LANE-GATE 3 inhabitant of `eq:contract-column-loss`**, in the kernel.

The vendored `NPCC.IsColumnLossResilient` holds of `bobBit` at
```
b = 4,  eps = 1/100,  Q = 4,  T = 4,  h = 2^{-1} = 1/2,
```
i.e. at `q = t = 2^4 = 16 <= 2^4 = 2^b`, a strictly positive balancedness
error and a strictly positive depth.  Every side condition the vendored
docstring lists is met, and nothing degenerates: `comp bobBit = 1 > 0`, so
clause (i) is a real nontriviality demand at the seed density `y_5`, and
clause (ii) at `k = 0` is a real three-rung demand at every `c <= 4`.

Contrast `columnLossResilient_fails_on_constant`: the same predicate at the
same parameters is **false** for a constant matrix.  So the contract separates
matrices, and neither clause is vacuously satisfiable. -/
theorem columnLossResilient_inhabited :
    NPCC.IsColumnLossResilient bobBit ((4 : ℕ) : ℝ) (1 / 100) 4 4 (1 / 2) := by
  have hx0 : (0:ℝ) < (2 : ℝ) ^ (-((4 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : (2 : ℝ) ^ (-((4 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.2 (Nat.cast_nonneg 4))
  have hy1 : ∀ c : ℕ, yLoss (1 / 100 : ℝ) (2 ^ 4) (1 / 2 : ℝ) c ≤ 1 := fun c =>
    yLoss_le_one_of_le_one (by norm_num) (by norm_num) (by norm_num) _ _
  have clauseI : 1 ≤ Dfamily (interlaceFun bobBit 1)
      (bracketGE Bool Bool 1 ((2 : ℝ) ^ (-((4 : ℕ) : ℝ)))
        (yLoss (1 / 100 : ℝ) (2 ^ 4) (1 / 2 : ℝ) (4 + D bobBit))) := by
    rw [D_bobBit]
    exact one_le_Dfamily_bobBit hx0 hx1 (half_lt_yLoss_witness (by norm_num))
      (hy1 _)
  have clauseII : ∀ k ≤ D bobBit, ∀ c ≤ 4 + k,
      D bobBit - k ≤ LambdaGE bobBit 1 ((2 : ℝ) ^ (-((4 : ℕ) : ℝ)))
        (yLoss (1 / 100 : ℝ) (2 ^ 4) (1 / 2 : ℝ) c) := by
    intro k hk c hc
    rw [D_bobBit] at hk ⊢
    have hc5 : c ≤ 5 := by omega
    have := one_le_LambdaGE_bobBit (x := (2 : ℝ) ^ (-((4 : ℕ) : ℝ)))
      (y := yLoss (1 / 100 : ℝ) (2 ^ 4) (1 / 2 : ℝ) c) hx0 hx1
      (half_lt_yLoss_witness hc5) (hy1 c)
    omega
  exact And.intro clauseI clauseII

/-- **Tightness pole for `stageTwoOneDepth`.**  If the three rungs hold with
*equality* -- which is what the Localized Extension conclusion of `07:383`
delivers, since it is exact -- then the three-rung quantity is exactly `D_2`.
So no rung hypothesis is stronger than the frozen text supplies, and no bit is
silently gained. -/
theorem stageTwoOneDepth_tight (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype Y] (bCapVal : ℕ) (h : ℝ)
    (eq₀ : Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (3 / 5))
      = bCapVal + (W.r₂ - 0))
    (eq₁ : Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (3 / 5 / 2))
      = bCapVal + (W.r₂ - 1))
    (eq₂ : Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 h (3 / 5 / 4))
      = bCapVal + (W.r₂ - 2)) :
    LambdaGE (stageTwoT F R W Pr) 1 h (3 / 5) = dTwo bCapVal W.r₂ := by
  have hr : 2 ≤ W.r₂ := by have := W.seven_le_r₂; omega
  obtain ⟨e₀, e₁, e₂⟩ := noBitsAddedTwo bCapVal W.r₂ hr
  unfold LambdaGE
  rw [eq₀, eq₁, eq₂, e₀, e₁, e₂]
  simp

/-! ## §10  The two-depth certificate `eq:stage2-two-depth-certificate`

`07:418--433`: "Apply `lem:stage2-one-depth` first with `h = 2^{-b_2}`, then
with `h = 2^{-b_T}`.  ...  Both certificates refer to the same physical
balanced family."  Reader `eq:paper-M2-robust` and `eq:paper-M2-aux-robust`
(`03-parameterized-construction.tex:437--449`). -/

set_option linter.unusedVariables false in
/-- **`eq:stage2-two-depth-certificate`** (`07:423--430`), assembled by **two
real applications of `lem:stage2-one-depth`**.

The frozen instruction is literal: "Apply `lem:stage2-one-depth` first with
`h = 2^{-b_2}`, then with `h = 2^{-b_T}`.  Equation
`eq:stage2-two-depth-comparisons` supplies `eq:stage2-one-depth-extension` in
the two calls, and all other data, including the indexed family `C_2`, are
unchanged" (`07:418--421`).  This theorem does exactly that:

* `stageTwoOneDepth` is invoked twice, at `h = xSeed b₂` and `h = xSeed b_T`;
* `hcomp : twoDepthComparisons W bCapVal ε b₂ bT` is destructured to supply
  the `hext` argument of each call, so the certificate genuinely consumes
  `eq:stage2-two-depth-comparisons`;
* **the sharing is pinned by construction**: there is one `Pr`, one `ε` and
  **one** `hbal : IsBalancedFamily W.t₂ Pr.c₂ ε` binder, and that single
  hypothesis term is passed to both calls.  A second family would need a
  second `Pr`, hence a second matrix `stageTwo F R W Pr'` and a second
  balancedness hypothesis, and the conclusion could not be stated.  See
  `twoDepth_family_sharing_is_content` for the kernel-checked reason this
  matters.

Only the three rung endpoints are still binders, six in total, three per
depth, exactly as `stageTwoOneDepth` leaves them.  The exact scale is *not* a
hypothesis: it is the first component of the `h = xSeed b₂` call.

*Repair note (round 1).*  The parked draft took `certAt`, which was its own
conclusion, and consumed neither `twoDepthComparisons` nor `stageTwoOneDepth`.

The two `Lambda` conjuncts are the reader displays `eq:paper-M2-robust`
(ordinary depth `b_2`, which controls Stage 3) and `eq:paper-M2-aux-robust`
(auxiliary depth `b_T`, used only by the deletion-stable and scale-alignment
parts of the adapted Stage 4). -/
theorem stageTwoTwoDepthCertificate (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype X] [Fintype Y] [DecidableEq X] (bCapVal b₂ bT : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hcard : 1 ≤ Fintype.card (Stage1Cols F Y))
    -- `eq:stage2-one-depth-base` (`07:268--274`), shared by both calls
    (hbase : D (stageOneT F R) = bCapVal)
    (hrobust : bCapVal ≤ LambdaGE (stageOneT F R) 1 (xSeed W.b₁) (3 / 5))
    (hthree : 3 ≤ bCapVal)
    -- the ONE physical balanced family of `07:433`
    (hbal : IsBalancedFamily W.t₂ Pr.c₂ ε)
    -- `eq:stage2-two-depth-comparisons` (`07:232--243`)
    (hcomp : twoDepthComparisons W bCapVal ε b₂ bT)
    -- the three Localized Extension endpoints at the ordinary depth `b_2`
    (rung₀ : bCapVal + (W.r₂ - 0) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 (xSeed b₂)
          (betaSeed 0)))
    (rung₁ : bCapVal + (W.r₂ - 1) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 (xSeed b₂)
          (betaSeed 1)))
    (rung₂ : bCapVal + (W.r₂ - 2) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 (xSeed b₂)
          (betaSeed 2)))
    -- the same three endpoints at the auxiliary depth `b_T`
    (rungT₀ : bCapVal + (W.r₂ - 0) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 (xSeed bT)
          (betaSeed 0)))
    (rungT₁ : bCapVal + (W.r₂ - 1) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 (xSeed bT)
          (betaSeed 1)))
    (rungT₂ : bCapVal + (W.r₂ - 2) ≤
      Dfamily (interlaceFun (stageTwoT F R W Pr) 1)
        (bracketGE (Slot Pr.N₂) (Slot W.q₂ × Stage1Cols F Y) 1 (xSeed bT)
          (betaSeed 2))) :
    D (stageTwo F R W Pr) = dTwo bCapVal W.r₂ ∧
      dTwo bCapVal W.r₂ ≤ LambdaGE (stageTwoT F R W Pr) 1 (xSeed b₂) (3 / 5) ∧
        dTwo bCapVal W.r₂ ≤ LambdaGE (stageTwoT F R W Pr) 1 (xSeed bT) (3 / 5) := by
  -- the first call: `h = 2^{-b_2}`
  have callTwo :=
    stageTwoOneDepth F R W Pr bCapVal (xSeed b₂) ε (xSeed_pos b₂)
      (xSeed_le_one b₂) hε hcard hbase hrobust hthree hbal hcomp.1
      rung₀ rung₁ rung₂
  -- the second call: `h = 2^{-b_T}`, with the SAME `Pr`, `ε` and `hbal`
  have callAux :=
    stageTwoOneDepth F R W Pr bCapVal (xSeed bT) ε (xSeed_pos bT)
      (xSeed_le_one bT) hε hcard hbase hrobust hthree hbal hcomp.2
      rungT₀ rungT₁ rungT₂
  exact ⟨callTwo.1, callTwo.2, callAux.2⟩

/-- **The certificate degenerates without the shared family, in the abstract.**
If the auxiliary certificate were allowed its own record `Pr'`, its `Lambda`
conjunct would be about `stageTwoT F R W Pr'`.  This lemma records the only
circumstance under which the two conjuncts are about the same object, namely
that the stored families agree coordinatewise, and it is *not* automatic: see
`twoDepth_family_sharing_is_content` in §13, which exhibits two legal records
at the same width and the same `N_2` whose Stage-2 matrices differ.

*Repair note (round 1).*  The parked `twoDepth_same_family` was `⟨rfl, rfl⟩`
beta-reduction of a lambda applied to two depths and pinned nothing. -/
theorem twoDepth_same_family (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr Pr' : LevelParams (Stage1Rows F X) W.q₂)
    (hN : Pr.N₂ = Pr'.N₂)
    (hfam : ∀ ℓ : Slot Pr.N₂, Pr.c₂ ℓ = Pr'.c₂ (hN ▸ ℓ)) :
    ∀ (p : Slot W.q₂ × Stage1Cols F Y) (ℓ : Slot Pr.N₂),
      stageTwo F R W Pr p ℓ = stageTwo F R W Pr' p (hN ▸ ℓ) := by
  intro p ℓ
  simp only [stageTwo, relaxedInterlace, hfam ℓ]

/-! ## §11  Statement poles

`Lambda_3(-, 1, h, 3/5) >= D_2` fails for a constant matrix, so the three
transported rungs of `stageTwoOneDepth_output` are genuine content and cannot
be dropped. -/

/-- **Statement pole.**  At the declared legal bindings and the legal constant
source matrix the three-rung quantity is `0`, while `D_2 = 0 + r_2 >= 7`.  So
`stageTwoOneDepth_output` cannot hold with its hypotheses removed. -/
theorem stageTwoOneDepth_not_automatic (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows stage1Legal Bool) W.q₂) (h : ℝ) :
    LambdaGE (stageTwoT stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
        1 h (3 / 5) = 0 ∧
      ¬ dTwo 0 W.r₂ ≤
        LambdaGE (stageTwoT stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
          1 h (3 / 5) := by
  have hconst :
      (stageTwoT stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
        = fun (_ : Slot Pr.N₂)
              (_ : Slot W.q₂ × Stage1Cols stage1Legal Bool) => false := rfl
  have hzero : LambdaGE
      (stageTwoT stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
      1 h (3 / 5) = 0 := by
    rw [hconst]
    unfold LambdaGE
    have hI : ∀ k : ℕ, interlaceFun
        (fun (_ : Slot Pr.N₂)
             (_ : Slot W.q₂ × Stage1Cols stage1Legal Bool) => false) k
        = fun (_ : Fin k × Slot Pr.N₂)
              (_ : Fin k → Slot W.q₂ × Stage1Cols stage1Legal Bool) => false :=
      fun _ => rfl
    rw [hI 1, Dfamily_const, Dfamily_const, Dfamily_const]
    norm_num
  refine ⟨hzero, ?_⟩
  rw [hzero]
  have := W.seven_le_r₂
  simp only [dTwo, Nat.zero_add, not_le]
  omega

/-- **The cited balanced family is not a field.**  `def:level-parameters`
(`05:183--189`) says outright that "the balancedness formula remains a
post-construction admissibility proposition; it is not a proof field of `Pi`",
and the banked `PublicRecords.levelParams_admits_unbalanced_family` exhibits a
legal record whose stored family is constant.  Consequently balancedness
cannot be projected out of `Pr`, which is why every statement above carries it
as the explicit binder `hbal` -- and why no declaration in this module reaches
the AGHP existence axiom. -/
theorem stageTwo_balancedness_is_not_a_field (w : ℕ) (hw : 0 < w) :
    ∃ Pr : LevelParams Bool w,
      (∀ ℓ ℓ' : Fin Pr.N₂, Pr.c₂ ℓ = Pr.c₂ ℓ') ∧
        ((Finset.univ.filter fun ℓ : Fin Pr.N₂ =>
            Pr.c₂ ℓ ⟨0, hw⟩ = false).card = Pr.N₂) ∧
        ((Finset.univ.filter fun ℓ : Fin Pr.N₂ =>
            Pr.c₂ ℓ ⟨0, hw⟩ = true).card = 0) :=
  PublicRecords.levelParams_admits_unbalanced_family w hw

/-! ## §12  Candidate B, kept as refuted evidence

Candidate B replaces the frozen *index* column carrier `L_2 = [N_2]` by the
image of the family, merging repeated tuples.  The presentation agrees with
`M_2` wherever it is defined, but it contradicts the frozen counting
convention. -/

/-- Candidate B's matrix: columns are the *distinct tuples* in the range of
the family, and the value is read off the representative. -/
def candidateB (F : Stage1SlotBinding) (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂) :
    Slot W.q₂ × Stage1Cols F Y → Set.range Pr.c₂ → Bool :=
  fun p c => stageOne F R (c.1 p.1) p.2

/-- Candidate B agrees with `M_2` at every family index, so nothing is lost by
recording it: the two differ only in *how many columns they count*. -/
theorem stageTwo_eq_candidateB_on_range (F : Stage1SlotBinding)
    (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (p : Slot W.q₂ × Stage1Cols F Y) (ℓ : Slot Pr.N₂) :
    stageTwo F R W Pr p ℓ = candidateB F R W Pr p ⟨Pr.c₂ ℓ, ⟨ℓ, rfl⟩⟩ := rfl

/-- The width record used by the candidate battery and by every non-vacuity
witness below: `k_2 = 5`, `r_2 = 7`, `b_1 = 24`, `m_HS = 5`, hence
`t_2 = 32` and `q_2 = 128`.

Every one of the four frozen gates is discharged **at its boundary**:
`5 <= m_HS = 5` (`D-inherited-contracts.tex:496`), `m_HS = 5 <= k_2 = 5`
(`07:293`), `4 t_2 = 128 <= q_2 = 128` (`07:292`), and
`131072 q_2 = 2^24 <= 2^{b_1} = 2^24` (`07:371--372`).  It is therefore the
componentwise-least legal record, which is the LANE-GATE-3 requirement.

*Honest scope, and a recorded coverage limit.*  This is **not** the tuple the
compiler computes: `eq:t2-search` (`06-parameter-schedule.tex:766`) forces
`k_2 >= max{4, 2^19, m_HS}`, so the scheduled `t_2` is at least `2^{2^19}`.
That search is deliberately not transcribed (coverage limit 3), and `k_2 = 5`
is used only as the smallest value at which the literal Stage-2 gate
comparisons of this module can be exhibited non-vacuously.  **No parameter
schedule may be read out of `widthsWitness`**, and in particular its `b_1`
must not be composed with the Stage-1 illustrative binding's `a = 7`. -/
def widthsWitness : StageTwoWidths where
  k₂ := 5
  r₂ := 7
  b₁ := 24
  mHS := 5
  five_le_mHS := le_refl 5
  mHS_le_k₂ := le_refl 5
  four_t₂_le_q₂ := by norm_num
  depth_gate := by norm_num

@[simp] theorem widthsWitness_t₂ : widthsWitness.t₂ = 32 := rfl

@[simp] theorem widthsWitness_q₂ : widthsWitness.q₂ = 128 := rfl

/-- **Width separation (`M5`), at the declared bindings.**  The Stage-2
ambient copy count is distinct from both Stage-1 widths, so `q_2`, `q_1` and
`L_1` can never be silently identified: `128 != 126 != 191`. -/
theorem q₂_ne_q₁_ne_L₁ :
    widthsWitness.q₂ ≠ stage1Legal.q₁ ∧ widthsWitness.q₂ ≠ stage1Legal.L₁ ∧
      stage1Legal.q₁ ≠ stage1Legal.L₁ := by
  refine ⟨by decide, by decide, by decide⟩

/-- The parameter record used by the candidate battery: a **constant** family
at `N_2 = 2`, which is legal (`levelParams_admits_unbalanced_family`) and is
the extremal case the frozen counting convention is about. -/
def candidateBParams :
    LevelParams (Stage1Rows stage1Legal Bool) widthsWitness.q₂ where
  K := PublicRecords.levelConfigWitness
  N₂ := 2
  N₂pos := by norm_num
  c₂ := fun _ _ => (⟨0, stage1Legal.q₁_pos⟩, true)

@[simp] theorem candidateBParams_N₂ : candidateBParams.N₂ = 2 := rfl

/-- **The discriminating battery item, in the kernel.**  At the declared legal
binding and a constant family with `N_2 = 2`, the frozen column carrier
`Cols(M_2) = L_2` has **two** elements, while Candidate B's carrier is the
range of the family, which here is a *singleton*.  So Candidate B falsifies
the frozen `|Cols(M_2)| = N_2` and the counting convention of
`def:balanced-family` (`03:287--288`), and it is rejected. -/
theorem candidateB_column_count_is_wrong :
    Fintype.card (Slot candidateBParams.N₂) = 2 ∧
      Set.range candidateBParams.c₂ =
        {fun _ : Slot widthsWitness.q₂ =>
          ((⟨0, stage1Legal.q₁_pos⟩, true) : Stage1Rows stage1Legal Bool)} ∧
      (Set.range candidateBParams.c₂).Subsingleton := by
  refine ⟨rfl, ?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨ℓ, rfl⟩; rfl
    · rintro rfl
      exact ⟨⟨0, candidateBParams.N₂pos⟩, rfl⟩
  · rintro a ⟨ℓ, rfl⟩ b ⟨ℓ', rfl⟩
    rfl

/-! ## §13  Non-vacuity witnesses (LANE-GATE 3)

Every new structure and every new definition above is inhabited at *legal*
parameter values by a **nondegenerate** witness. -/

/-- A nondegenerate parameter record at the declared legal width: `N_2 = 2`
and a family that is **not** constant, so the Stage-2 witness is not inhabited
only at a degenerate family. -/
def paramsWitnessTwo :
    LevelParams (Stage1Rows stage1Legal Bool) widthsWitness.q₂ where
  K := PublicRecords.levelConfigWitness
  N₂ := 2
  N₂pos := by norm_num
  c₂ := fun ℓ α => (⟨0, stage1Legal.q₁_pos⟩, decide ((ℓ : ℕ) ≤ (α : ℕ)))

@[simp] theorem paramsWitnessTwo_N₂ : paramsWitnessTwo.N₂ = 2 := rfl

/-- The two legal family indices of the witness record. -/
def idx₀ : Slot paramsWitnessTwo.N₂ := ⟨0, show (0:ℕ) < 2 by norm_num⟩

/-- The second legal family index of the witness record. -/
def idx₁ : Slot paramsWitnessTwo.N₂ := ⟨1, show (1:ℕ) < 2 by norm_num⟩

/-- The zeroth Stage-2 outer coordinate at the declared legal width. -/
def coord₀ : Slot widthsWitness.q₂ := ⟨0, show (0:ℕ) < 128 by norm_num⟩

theorem paramsWitnessTwo_nonconstant :
    paramsWitnessTwo.c₂ idx₀ ≠ paramsWitnessTwo.c₂ idx₁ := by
  intro hEq
  have h := congrArg (fun f => (f coord₀).2) hEq
  simp [paramsWitnessTwo, idx₀, idx₁, coord₀] at h

/-- **The "same physical family" pole, with content** (`07:433`).

"Both certificates refer to the same physical balanced family" is a constraint
only if a *different* family would give a different matrix.  That is checked
here in the kernel: two legal `LevelParams` records at the same declared legal
width and the same `N_2 = 2`, one with a constant family and one without, give
provably **different** Stage-2 matrices.

So the single `Pr` binder of `stageTwoTwoDepthCertificate` -- and the single
`hbal` binder passed to both of its calls -- is genuine sharing: replacing the
record at the auxiliary depth would replace the object the auxiliary
certificate speaks about, and the conjunction would no longer be a statement
about one Stage-2 construction. -/
theorem twoDepth_family_sharing_is_content :
    stageTwo stage1Legal witnessSource widthsWitness paramsWitnessTwo ≠
      stageTwo stage1Legal witnessSource widthsWitness candidateBParams := by
  intro hEq
  have h := congrFun (congrFun hEq (coord₀, fun _ => true)) idx₁
  simp [stageTwo, relaxedInterlace, paramsWitnessTwo, candidateBParams,
    stageOneT, stageOne, witnessSource, idx₁, coord₀] at h

/-- The Stage-2 matrix at the declared legal bindings, over the banked
nonconstant Stage-1 source `witnessSource = AND`. -/
def stageTwoWitness :
    Slot widthsWitness.q₂ × Stage1Cols stage1Legal Bool →
      Slot paramsWitnessTwo.N₂ → Bool :=
  stageTwo stage1Legal witnessSource widthsWitness paramsWitnessTwo

/-- **Non-vacuity 1 (the matrix is nondegenerate).**  The witness takes both
Boolean values at the *same* row, so it is neither constant nor
column-independent, and both frozen carriers have the frozen sizes
`q_2 |C_1| = 128 * 2^191` and `|L_2| = N_2 = 2`. -/
theorem stageTwoWitness_nondegenerate :
    stageTwoWitness (coord₀, fun _ => true) idx₀ = true ∧
      stageTwoWitness (coord₀, fun _ => true) idx₁ = false ∧
      Fintype.card
          (Slot widthsWitness.q₂ × Stage1Cols stage1Legal Bool) = 128 * 2 ^ 191 ∧
        Fintype.card (Slot paramsWitnessTwo.N₂) = 2 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  rw [stageTwo_rows_card stage1Legal widthsWitness Bool]
  rfl

/-- **Non-vacuity 2 (the family is genuinely read).**  The witness's two
columns are *different* Boolean functions, so `M_2` really depends on the
stored family and not only on `M_1`. -/
theorem stageTwoWitness_columns_differ :
    (fun p => stageTwoWitness p idx₀) ≠ fun p => stageTwoWitness p idx₁ := by
  intro hEq
  have := congrFun hEq (coord₀, fun _ => true)
  simp [stageTwoWitness, stageTwo, relaxedInterlace, paramsWitnessTwo,
    stageOneT, stageOne, witnessSource, idx₀, idx₁, coord₀] at this

/-- **Non-vacuity 3 (the width record).**  The four-field bundle is inhabited,
so no contradiction follows from it, and all its derived accessors take their
frozen values at the least legal point. -/
theorem stageTwoWidths_bundle_consistent : Nonempty StageTwoWidths :=
  ⟨widthsWitness⟩

/-- **Non-vacuity 4 (the one-depth scalars).**  At the least legal width
record the six one-depth scalars of `eq:stage2-one-depth-data` are distinct,
positive and integral where the frozen text says they are:
`p_2^seed = 18 = (9/16) * 32`, and for `j = 0, 1, 2`
`K_j = 128, 64, 32`, `r_j = 4, 2, 1`, with `r_j p_2^seed = 72, 36, 18`. -/
theorem oneDepthData_values :
    pSeedTwo widthsWitness.k₂ = 18 ∧
      Kseed widthsWitness 0 = 128 ∧ Kseed widthsWitness 1 = 64 ∧
        Kseed widthsWitness 2 = 32 ∧
      rSeed widthsWitness 0 = 4 ∧ rSeed widthsWitness 1 = 2 ∧
        rSeed widthsWitness 2 = 1 ∧
      rSeed widthsWitness 0 * pSeedTwo widthsWitness.k₂ = 72 ∧
        rSeed widthsWitness 1 * pSeedTwo widthsWitness.k₂ = 36 ∧
        rSeed widthsWitness 2 * pSeedTwo widthsWitness.k₂ = 18 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Non-vacuity 5 (the balancing gates fire at the least legal record).**
`balanceCeilings_hold` is not vacuous: at `widthsWitness` all three rungs
satisfy the frozen strict density chain and the ceiling gate. -/
theorem balanceCeilings_fire :
    (0 < xiSeed widthsWitness 0 ∧ xiSeed widthsWitness 0 < betaSeed 0) ∧
      (0 < xiSeed widthsWitness 1 ∧ xiSeed widthsWitness 1 < betaSeed 1) ∧
        (0 < xiSeed widthsWitness 2 ∧ xiSeed widthsWitness 2 < betaSeed 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(balanceCeilings_hold widthsWitness (by norm_num)).1,
      (balanceCeilings_hold widthsWitness (by norm_num)).2.1⟩
  · exact ⟨(balanceCeilings_hold widthsWitness (by norm_num : (1:ℕ) ≤ 2)).1,
      (balanceCeilings_hold widthsWitness (by norm_num : (1:ℕ) ≤ 2)).2.1⟩
  · exact ⟨(balanceCeilings_hold widthsWitness (le_refl 2)).1,
      (balanceCeilings_hold widthsWitness (le_refl 2)).2.1⟩

/-- **Non-vacuity 6 (`xi_j` is not degenerate).**  At the least legal record
`xi_0 = q_2 2^{-b_1} = 2^{-17}` is strictly positive and strictly below the
frozen bound `1/131072`, met here with equality, so the balancing paragraph's
extremal case is exercised rather than avoided. -/
theorem xiSeed_witness_value :
    xiSeed widthsWitness 0 = 1 / 131072 := by
  have hb : widthsWitness.b₁ = 24 := rfl
  have hr : widthsWitness.r₂ = 7 := rfl
  have hx : xSeed widthsWitness.b₁ = 1 / 2 ^ 24 := by
    rw [hb, xSeed, two_rpow_neg_natCast]
  simp only [xiSeed, Kseed, hx, hr]
  norm_num

/-! ## §14  Consistency probes (HYPOTHESIS-CONSISTENCY RULE)

Each headline statement's hypothesis bundle is checked to be satisfiable at
the frozen side conditions, so that no theorem above is green-but-vacuous. -/

/-- **Consistency probe 1, `stageTwo_scale_eq_dTwo`.**  Given the proved upper
half, its remaining hypothesis `hlower` is *equivalent* to the single frozen
equation `comp(M_2) = comp(M_1^T) + log_2 q_2` of `eq:stage2-one-depth-output`
line 1.  So it is contradictory only if that equation is, and nothing stronger
than the frozen text is assumed. -/
theorem scale_hypothesis_iff (F : Stage1SlotBinding) (R : X → Y → Bool)
    (W : StageTwoWidths) (Pr : LevelParams (Stage1Rows F X) W.q₂)
    [Fintype X] [Fintype Y] :
    (D (stageOneT F R) + W.r₂ ≤ D (stageTwo F R W Pr)) ↔
      D (stageTwo F R W Pr) = D (stageOneT F R) + W.r₂ := by
  constructor
  · intro h; exact Nat.le_antisymm (stageTwo_selector_upper F R W Pr) h
  · intro h; exact le_of_eq h.symm

/-- **Consistency probe 2, `stageTwoOneDepth_output`.**  The three rung
hypotheses are the three conclusions of **one** construction (frozen `07:348`,
"Fix `j in {0,1,2}` and an arbitrary member ..."), not two cases of a promise
split, so conjoining them is legitimate; and their numeric shape is
satisfiable *simultaneously with* the frozen conclusion at every
`(B_cap, r_2)`.  No contradiction follows from the bundle. -/
theorem stageTwoOneDepth_hypotheses_consistent (bCapVal r₂ : ℕ) :
    ∃ d₀ d₁ d₂ : ℕ,
      bCapVal + (r₂ - 0) ≤ d₀ ∧ bCapVal + (r₂ - 1) ≤ d₁ ∧
        bCapVal + (r₂ - 2) ≤ d₂ ∧
          dTwo bCapVal r₂ ≤ min d₀ (min (1 + d₁) (2 + d₂)) := by
  refine ⟨bCapVal + r₂, bCapVal + r₂, bCapVal + r₂, by omega, by omega, by omega, ?_⟩
  simp only [dTwo]
  exact le_min (le_refl _) (le_min (by omega) (by omega))

/-- **Consistency probe 3, the Extension comparisons.**  The pair
`extensionComparisons` is *not* contradictory: at any legal width record and
any `B_cap`, taking the balancedness error `eps = 0` and a retained column
density `h` at which the first comparison holds is consistent with the second,
because both comparisons are monotone increasing in `h` and the two right-hand
sides `3/5` and `h_2^seed` are fixed positive constants below `1`.  The probe
records the monotonicity, which is the direction a contradiction would have to
violate. -/
theorem extensionComparisons_monotone_in_h (W : StageTwoWidths) (bCapVal : ℕ)
    {h h' ε : ℝ} (hh0 : 0 < h) (hh' : h ≤ h') (hε : 0 ≤ ε) :
    h * (2 : ℝ) ^ (-((W.k₂ + bCapVal : ℕ) : ℝ)) / (1 + ε)
        ≤ h' * (2 : ℝ) ^ (-((W.k₂ + bCapVal : ℕ) : ℝ)) / (1 + ε) ∧
      yLoss ε W.t₂ h (W.r₂ + bCapVal) ≤ yLoss ε W.t₂ h' (W.r₂ + bCapVal) := by
  have hd : (0:ℝ) < 1 + ε := by linarith
  have h2 : (0:ℝ) < (2:ℝ) ^ (-((W.k₂ + bCapVal : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2' : (0:ℝ) < (2:ℝ) ^ (-((W.r₂ + bCapVal : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hz : h * (2 : ℝ) ^ (-((W.k₂ + bCapVal : ℕ) : ℝ)) / (1 + ε)
      ≤ h' * (2 : ℝ) ^ (-((W.k₂ + bCapVal : ℕ) : ℝ)) / (1 + ε) := by
    gcongr
  have hz' : h * (2 : ℝ) ^ (-((W.r₂ + bCapVal : ℕ) : ℝ)) / (1 + ε)
      ≤ h' * (2 : ℝ) ^ (-((W.r₂ + bCapVal : ℕ) : ℝ)) / (1 + ε) := by
    gcongr
  refine ⟨hz, ?_⟩
  unfold yLoss
  exact Real.rpow_le_rpow (le_of_lt (yLoss_ratio_pos hh0 hε _)) hz' (by positivity)

/-- **Coverage limit, binding on every consumer.**  Neither the ambient lower
bound nor the three rung bounds is *inhabited* here at a concrete matrix.  The
obstruction is exactly the four inherited endpoints named in the module
header, and this theorem records that the failure is a *missing lower bound*,
not an inconsistency: the proved upper half holds on the constant matrix with
room to spare, so the missing side is one-directional. -/
theorem scale_upper_half_alone_holds (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows stage1Legal Bool) W.q₂) :
    D (stageTwo stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
        ≤ D (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false)) + W.r₂ ∧
      ¬ (D (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false)) + W.r₂
          ≤ D (stageTwo stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)) := by
  have hzero : D (stageTwo stage1Legal (fun (_ : Bool) (_ : Bool) => false) W Pr)
      = 0 := (dTwo_is_not_a_complexity_claim W Pr).1
  have hT : D (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false)) = 0 := by
    have hconst : (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false))
        = fun (_ : Stage1Cols stage1Legal Bool)
              (_ : Stage1Rows stage1Legal Bool) => false := rfl
    rw [hconst]
    exact PublicRecords.D_const false
  refine ⟨stageTwo_selector_upper _ _ _ _, ?_⟩
  rw [hzero, hT]
  have := W.seven_le_r₂
  omega

/-- **Consistency probe 5, the balancedness binder.**  `hbal` is carried by
`stageTwoOneDepth` and `stageTwoTwoDepthCertificate` but not consumed by their
Lean derivations, so a green build cannot show it is satisfiable at all -- and
an unsatisfiable `hbal` would make both theorems vacuous.  The predicate is
therefore checked here to be consistent at a positive accuracy: over a
one-element column alphabet every indexed family with `L > 0` is exactly
balanced, so `IsBalancedFamily t S eps` holds for every `t` and every
`eps >= 0`.  No contradiction follows from the predicate.

*Coverage limit, binding.*  This says nothing about existence at the frozen
Stage-2 carriers, which is the AGHP citation `alon1992simple`
(`03-preliminaries.tex:291--293`).  That existence is deliberately **not**
asserted anywhere in this module: it lives behind the opt-in
`LegacyNPCC.Stage12` facade as an axiom of `NPCC.Axioms`, which is not in the
closure of any declaration here. -/
theorem isBalancedFamily_satisfiable {q L : ℕ} (t : ℕ) (hL : 0 < L) {ε : ℝ}
    (hε : 0 ≤ ε) :
    IsBalancedFamily t (fun (_ : Fin L) (_ : Fin q) => ()) ε := by
  refine ⟨hL, ?_⟩
  intro J _ a
  have hfilter :
      (Finset.univ.filter (fun j : Fin L => ∀ γ ∈ J, () = a γ))
        = (Finset.univ : Finset (Fin L)) := by
    ext j
    simp
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hL
  rw [hfilter, Finset.card_univ, Fintype.card_fin]
  simp only [Fintype.card_unit, Nat.cast_one, one_pow, div_one]
  rw [div_self (ne_of_gt hLR)]
  simpa using hε

/-! ## §15  The Extension comparisons are inhabited at LEGAL schedule values

`stageTwoOneDepth` conjoins a real-valued pair (`hext`) with a numeric width
record and a real depth `h in (0,1]`, and `stageTwoTwoDepthCertificate`
conjoins two such pairs (`twoDepthComparisons`) at the two scheduled depths
over one balanced family.  A green build cannot show that any of this is
satisfiable, so it is checked here.

*Repair note (round 1).*  The parked draft inhabited `extensionComparisons`
only at `h = 1` and `eps = 0`, and left `twoDepthComparisons` with no
inhabitant at all.  Neither of those is a legal schedule value: `h = 2^{-b}`
with `b = 0` is not a depth (the frozen densities are `h_2 = 2^{-b_2}` of
`eq:b2-choice` and the auxiliary `2^{-b_T}`, both with a positive depth), and
`eq:epsilon-product` (`06-parameter-schedule.tex:851--857`) fixes
`eps_2 = 1/(100 t_2) > 0`, so a zero-error family is not one the schedule ever
builds.  The generalized gate `extensionComparisons_of_depth_gates` below runs
at an arbitrary positive depth and an arbitrary `eps in [0,1]`, and
`twoDepthComparisons_at_legal_values` inhabits the two-depth predicate at
`eps = eps_2 = 1/(100 t_2)` and two distinct positive depths.

**Finding, recorded because it is frozen content rather than an artefact.**
No gate here is satisfiable at the componentwise-least `widthsWitness`: the
second comparison needs `b + k_2 + B_cap + 1 <= 2^{(49/100) sqrt(k_2)}`, and at
`k_2 = 5` the right side is below `2^{1.1} < 3`.  That is exactly why
`eq:t2-search` (`06-parameter-schedule.tex:764--772`) makes its third clause
`2^{j_49(k_2)} >= L_h + B_cap + k_2 + 4` and forces
`k_2 >= max{4, 2^19, m_HS}`.  The record `bigWidths` below is the smallest
*round* exponent at which the frozen gate can be exhibited without
transcribing `j_49`, and it confirms the frozen search's direction rather than
replacing it. -/

/-- **`eps_2 = 1/(100 t_2)`**, the balancedness error the schedule fixes in
`eq:epsilon-product` (`06-parameter-schedule.tex:851--857`).  It is carried
here only as the legal value at which the Stage-2 gates are inhabited; the
product error `eps_prod` and its `< 1/50` bound are Stage-4 data and are not
transcribed (coverage limit 3). -/
noncomputable def epsTwo (W : StageTwoWidths) : ℝ := 1 / (100 * (W.t₂ : ℝ))

theorem epsTwo_pos (W : StageTwoWidths) : 0 < epsTwo W := by
  have ht : (0:ℝ) < (W.t₂ : ℝ) := by exact_mod_cast W.t₂_pos
  unfold epsTwo
  positivity

theorem epsTwo_le_one (W : StageTwoWidths) : epsTwo W ≤ 1 := by
  have ht : (1:ℝ) ≤ (W.t₂ : ℝ) := by exact_mod_cast W.t₂_pos
  unfold epsTwo
  rw [div_le_one (by linarith)]
  linarith

/-- `y_c` and its inner ratio at the boundary depth `h = 1` and zero
balancedness error: the ratio is `2^{-c}`.  A general identity of
`eq:contract-yloss`, kept as an aux-battery item; it is **not** a legal
schedule point (see the section note). -/
theorem yLoss_ratio_one_zero (c : ℕ) :
    (1 : ℝ) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + 0) = (2 : ℝ) ^ (-(c : ℝ)) := by
  norm_num

/-- `y_c(1, 0) = 2^{-c/t}`.  General identity of `NPCC.yLoss`. -/
theorem yLoss_one_zero (t c : ℕ) (ht : 0 < t) :
    yLoss 0 t 1 c = (2 : ℝ) ^ (-((c : ℝ) / (t : ℝ))) := by
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  unfold yLoss
  rw [yLoss_ratio_one_zero, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  field_simp

/-- `3/5 <= 2^{-1/2}`: the frozen right-hand side of the first comparison sits
strictly below the value the exponent gate delivers. -/
theorem three_fifths_le_two_rpow_neg_half :
    (3 / 5 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 ≤ 5 / 3 := by
    have h : Real.sqrt 2 ≤ Real.sqrt ((5 / 3 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5 / 3)] at h
  have hrw : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow]
  rw [hrw]
  have hinv : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 := inv_mul_cancel₀ (ne_of_gt h2)
  nlinarith [inv_pos.2 h2]

/-- **The inner ratio at a real depth, lower-bounded.**  At `h = 2^{-b}` and
balancedness error `eps in [0, 1]`,
```
z_c(2^{-b}, eps) = 2^{-(b+c)}/(1 + eps)  >=  2^{-(b+c+1)},
```
because `1 + eps <= 2`.  This is the one step where a *positive* `eps` costs
anything at all, and it costs exactly one bit. -/
theorem two_rpow_le_yLoss_ratio_xSeed (b c : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    (2 : ℝ) ^ (-((b + c + 1 : ℕ) : ℝ))
      ≤ xSeed b * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
  have hd : (0:ℝ) < 1 + ε := by linarith
  have hsplit : xSeed b * (2 : ℝ) ^ (-(c : ℝ)) = (2 : ℝ) ^ (-((b + c : ℕ) : ℝ)) := by
    unfold xSeed
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    push_cast
    ring
  have hstep : (2 : ℝ) ^ (-((b + c + 1 : ℕ) : ℝ)) * 2
      = (2 : ℝ) ^ (-((b + c : ℕ) : ℝ)) := by
    calc (2 : ℝ) ^ (-((b + c + 1 : ℕ) : ℝ)) * 2
        = (2 : ℝ) ^ (-((b + c + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (-((b + c + 1 : ℕ) : ℝ) + 1) :=
          (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
      _ = (2 : ℝ) ^ (-((b + c : ℕ) : ℝ)) := by congr 1; push_cast; ring
  have hpos : (0:ℝ) < (2 : ℝ) ^ (-((b + c + 1 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [hsplit, le_div_iff₀ hd]
  nlinarith

/-- **The two Extension comparisons at an arbitrary legal depth and error.**

`eq:stage2-one-depth-extension` at `h = 2^{-b}` and `eps in [0,1]` follows
from two integer gates:
```
2(b + r_2 + B_cap + 1) <= t_2,
b + k_2 + B_cap + 1    <= 2^{(49/100) sqrt(k_2)}.
```
The second is exactly the shape of the third clause of `eq:t2-search`.  Unlike
the parked draft's helper this fixes neither the depth nor the error, so it can
be fired at the scheduled `eps_2 = 1/(100 t_2) > 0` and at any positive depth. -/
theorem extensionComparisons_of_depth_gates (W : StageTwoWidths)
    (bCapVal b : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfirst : 2 * (b + W.r₂ + bCapVal + 1) ≤ W.t₂)
    (hsecond : ((b + W.k₂ + bCapVal + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (W.k₂ : ℕ))) :
    extensionComparisons W bCapVal (xSeed b) ε := by
  have htpos : (0:ℝ) < (W.t₂ : ℝ) := by exact_mod_cast W.t₂_pos
  constructor
  · -- first comparison
    have hz := two_rpow_le_yLoss_ratio_xSeed b (W.r₂ + bCapVal) hε0 hε1
    have hstep : (2 : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ((2 : ℝ) ^ (-((b + (W.r₂ + bCapVal) + 1 : ℕ) : ℝ))) ^
            ((1 : ℝ) / (W.t₂ : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hN : ((b + (W.r₂ + bCapVal) + 1 : ℕ) : ℝ) * 2 ≤ (W.t₂ : ℝ) := by
        have h : (2 * (b + (W.r₂ + bCapVal) + 1) : ℕ) ≤ W.t₂ := by omega
        have h' : ((2 * (b + (W.r₂ + bCapVal) + 1) : ℕ) : ℝ) ≤ (W.t₂ : ℝ) :=
          Nat.cast_le.2 h
        push_cast at h' ⊢
        linarith
      rw [neg_mul, neg_le_neg_iff, mul_one_div, div_le_iff₀ htpos]
      linarith
    refine le_trans three_fifths_le_two_rpow_neg_half (le_trans hstep ?_)
    unfold yLoss
    exact Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hz
      (by positivity)
  · -- second comparison
    refine le_trans ?_ (two_rpow_le_yLoss_ratio_xSeed b (W.k₂ + bCapVal) hε0 hε1)
    rw [hSeedTwo]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : ((b + (W.k₂ + bCapVal) + 1 : ℕ) : ℝ)
        = ((b + W.k₂ + bCapVal + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, neg_le_neg_iff]
    exact hsecond

/-- A legal width record at which the Extension comparisons of
`eq:stage2-one-depth-extension` can be exhibited: `k_2 = 1024`, `r_2 = 1026`,
`b_1 = 1043`, `m_HS = 5`, hence `t_2 = 2^1024` and `q_2 = 2^1026`.  Every gate
is again discharged at its boundary (`4 t_2 = q_2` and
`131072 q_2 = 2^{b_1}`).

`k_2 = 1024` is chosen only because `sqrt(1024) = 32` is exact, which keeps
the second exponent gate checkable without transcribing `j_49`.  It is still
far below the frozen `eq:t2-search` value `k_2 >= 2^19`, and coverage limit 3
continues to forbid reading any parameter schedule out of it. -/
def bigWidths : StageTwoWidths where
  k₂ := 1024
  r₂ := 1026
  b₁ := 1043
  mHS := 5
  five_le_mHS := le_refl 5
  mHS_le_k₂ := by norm_num
  four_t₂_le_q₂ := by
    have h : (2:ℕ) ^ 1026 = 4 * 2 ^ 1024 := by
      rw [show (1026:ℕ) = 1024 + 2 from rfl, pow_add]; ring
    omega
  depth_gate := by
    have h : (2:ℕ) ^ 1043 = 131072 * 2 ^ 1026 := by
      rw [show (1043:ℕ) = 1026 + 17 from rfl, pow_add]; ring
    omega

/-- The ordinary Stage-2 proof depth `b_2` used by the witnesses below.  It is
a *legal* value in the only sense this module fixes -- a positive integer, so
that `h_2 = 2^{-b_2}` lies strictly inside `(0, 1)` -- and it is **not** the
value `eq:b2-choice` computes from `32 s q_1 m_R`, which is not transcribed
(coverage limit 3). -/
def depthTwoWitness : ℕ := 40

/-- The auxiliary Stage-2 depth `b_T`, distinct from `b_2` and again positive.
`07:431--433`: "The ordinary depth `b_2` controls Stage 3.  The auxiliary
depth `b_T` is used only in the deletion-stable and scale-alignment parts of
the adapted Stage 4." -/
def depthAuxWitness : ℕ := 60

/-- **The two depths are genuinely two.**  At the declared witnesses the
ordinary and auxiliary depths are distinct and both nonzero, so `2^{-b_2}` and
`2^{-b_T}` are distinct retained column densities strictly inside `(0, 1)`.
This is the degeneracy the parked draft's `h = 1` witness collapsed. -/
theorem twoDepth_depths_are_distinct :
    depthTwoWitness ≠ depthAuxWitness ∧ 0 < depthTwoWitness ∧
      0 < depthAuxWitness ∧
      xSeed depthAuxWitness < xSeed depthTwoWitness ∧
      xSeed depthTwoWitness < 1 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · unfold xSeed
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by
      norm_num [depthTwoWitness, depthAuxWitness])
  · unfold xSeed
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    norm_num [depthTwoWitness]

/-- The second exponent gate at `bigWidths`, discharged once and reused at both
depths: `2^{(49/100) sqrt(1024)} = 2^{15.68} >= 32768`. -/
theorem bigWidths_hardSeed_exponent :
    (32768 : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (bigWidths.k₂ : ℕ)) := by
  have hk : ((bigWidths.k₂ : ℕ) : ℝ) = 1024 := by norm_num [bigWidths]
  have hsqrt : Real.sqrt ((bigWidths.k₂ : ℕ) : ℝ) = 32 := by
    rw [hk, show (1024:ℝ) = 32 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 32)]
  rw [hsqrt]
  have h15 : (2:ℝ) ^ ((15:ℕ) : ℝ) ≤ (2:ℝ) ^ ((49 / 100 : ℝ) * 32) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hval : (2:ℝ) ^ ((15:ℕ) : ℝ) = 32768 := by
    rw [Real.rpow_natCast]; norm_num
  linarith [hval ▸ h15]

/-- `t_2 = 2^1024` dwarfs both first gates. -/
theorem bigWidths_first_gate (b : ℕ) (hb : b ≤ 60) :
    2 * (b + bigWidths.r₂ + 3 + 1) ≤ bigWidths.t₂ := by
  have ht : (4096:ℕ) ≤ 2 ^ 1024 := by
    calc (4096:ℕ) = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hr : bigWidths.r₂ = 1026 := rfl
  have htt : bigWidths.t₂ = 2 ^ 1024 := rfl
  omega

/-- **Consistency probe 4 / LANE-GATE 3 inhabitant: `extensionComparisons` at
a LEGAL depth and the scheduled balancedness error.**

`bCapVal = 3` is the frozen base clause `B_cap >= 3` of
`eq:stage2-one-depth-base` at its boundary; `b` is a positive depth; and the
error is the scheduled `eps_2 = 1/(100 t_2)`, which is **strictly positive**,
so this is not the zero-error degeneracy. -/
theorem extensionComparisons_at_legal_values (b : ℕ) (hb : b ≤ 60) :
    extensionComparisons bigWidths 3 (xSeed b) (epsTwo bigWidths) := by
  refine extensionComparisons_of_depth_gates bigWidths 3 b
    (le_of_lt (epsTwo_pos bigWidths)) (epsTwo_le_one bigWidths)
    (bigWidths_first_gate b hb) ?_
  have hbound : ((b + bigWidths.k₂ + 3 + 1 : ℕ) : ℝ) ≤ 32768 := by
    have hk : bigWidths.k₂ = 1024 := rfl
    have h : (b + bigWidths.k₂ + 3 + 1 : ℕ) ≤ 32768 := by omega
    exact_mod_cast h
  exact le_trans hbound bigWidths_hardSeed_exponent

/-- **LANE-GATE 3 inhabitant for `twoDepthComparisons`.**

The two-depth predicate of `eq:stage2-two-depth-comparisons` is inhabited at
a legal width record, the frozen base value `B_cap = 3`, the scheduled
balancedness error `eps_2 = 1/(100 t_2) > 0`, and **two distinct positive
depths**.  The conjunction records, in the kernel, that the error is strictly
positive and the two depths are distinct and nonzero, so no clause of the
predicate is being satisfied by a degenerate reading.

*Repair note (round 1).*  This declaration did not exist in the parked draft:
`twoDepthComparisons` had no inhabitant at all, and its component predicate was
witnessed only at `h = 1` (depth `0`) and `eps = 0`. -/
theorem twoDepthComparisons_at_legal_values :
    twoDepthComparisons bigWidths 3 (epsTwo bigWidths)
        depthTwoWitness depthAuxWitness ∧
      0 < epsTwo bigWidths ∧ depthTwoWitness ≠ depthAuxWitness ∧
      0 < depthTwoWitness ∧ 0 < depthAuxWitness :=
  ⟨⟨extensionComparisons_at_legal_values depthTwoWitness (by decide),
      extensionComparisons_at_legal_values depthAuxWitness (by decide)⟩,
    epsTwo_pos bigWidths, by decide, by decide, by decide⟩

/-- **Consistency probe 6, the two-depth certificate's full numeric bundle.**

`stageTwoTwoDepthCertificate` conjoins the frozen base clause `B_cap >= 3`,
the scheduled balancedness error, `eq:stage2-two-depth-comparisons` at two
depths, and six rung endpoints.  Those are not two cases of a promise split:
they are the outputs of **one** construction read at two depths
(`07:418--421`, "all other data, including the indexed family `C_2`, are
unchanged"), so conjoining them is legitimate.  This probe exhibits the whole
numeric shell simultaneously satisfied at the frozen boundary `B_cap = 3`, at
a legal width record, at the scheduled `eps_2 > 0`, and at two distinct
positive depths, so no contradiction follows from the bundle. -/
theorem twoDepthCertificate_hypotheses_consistent :
    3 ≤ 3 ∧ 0 < epsTwo bigWidths ∧
      twoDepthComparisons bigWidths 3 (epsTwo bigWidths)
        depthTwoWitness depthAuxWitness ∧
      (∃ d₀ d₁ d₂ e₀ e₁ e₂ : ℕ,
        3 + (bigWidths.r₂ - 0) ≤ d₀ ∧ 3 + (bigWidths.r₂ - 1) ≤ d₁ ∧
          3 + (bigWidths.r₂ - 2) ≤ d₂ ∧
        3 + (bigWidths.r₂ - 0) ≤ e₀ ∧ 3 + (bigWidths.r₂ - 1) ≤ e₁ ∧
          3 + (bigWidths.r₂ - 2) ≤ e₂ ∧
        dTwo 3 bigWidths.r₂ ≤ min d₀ (min (1 + d₁) (2 + d₂)) ∧
        dTwo 3 bigWidths.r₂ ≤ min e₀ (min (1 + e₁) (2 + e₂))) := by
  obtain ⟨hcomp, hε, -, -, -⟩ := twoDepthComparisons_at_legal_values
  refine ⟨le_refl 3, hε, hcomp, ?_⟩
  obtain ⟨d₀, d₁, d₂, h₀, h₁, h₂, hmin⟩ :=
    stageTwoOneDepth_hypotheses_consistent 3 bigWidths.r₂
  exact ⟨d₀, d₁, d₂, d₀, d₁, d₂, h₀, h₁, h₂, h₀, h₁, h₂, hmin, hmin⟩

/-- **The recorded finding**, in the kernel: the second Extension comparison
*fails* at the componentwise-least `widthsWitness` even at the most generous
depth `b = 0`, because `0 + k_2 + B_cap + 1 = 9` while
`2^{(49/100) sqrt 5} < 4`.  So `extensionComparisons` is genuine content that
the frozen `eq:t2-search` search is there to secure, and it is not silently
satisfied by every legal width record. -/
theorem exponent_gate_fails_at_widthsWitness :
    ¬ (((0 + widthsWitness.k₂ + 3 + 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (widthsWitness.k₂ : ℕ))) := by
  have hk : ((widthsWitness.k₂ : ℕ) : ℝ) = 5 := by norm_num [widthsWitness]
  have hcast : ((0 + widthsWitness.k₂ + 3 + 1 : ℕ) : ℝ) = 9 := by
    norm_num [widthsWitness]
  have hs : Real.sqrt ((widthsWitness.k₂ : ℕ) : ℝ) ≤ 5 / 2 := by
    rw [hk]
    have h : Real.sqrt 5 ≤ Real.sqrt ((5 / 2 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5 / 2)] at h
  have hle : (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((widthsWitness.k₂ : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ ((2:ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      push_cast
      nlinarith [Real.sqrt_nonneg ((widthsWitness.k₂ : ℕ) : ℝ)])
  have hval : (2 : ℝ) ^ ((2:ℕ) : ℝ) = 4 := by rw [Real.rpow_natCast]; norm_num
  rw [hval] at hle
  rw [hcast]
  linarith

/-! ## §12  The derived Stage-2 width: the `q_2`-only intake-indexed view

### What this section is, and what it deliberately is not

`StageTwoWidths` (section 0) stores the exponent `r_2`, hence stores the
Stage-2 ambient width `q_2 = 2^{r_2}` as free constructor data, and carries
its four numeric gates as constructor *proof* fields.  Both are authoring
defects against the frozen text:

* **`q_2` is source-DEFINED, not free.**  The defining display is
  `04-guarded-source.tex:391` inside `def:guarded-source-constructor`,
  `q_2 = min{2^r : 12 s |E| <= 2^r}`, taken at the floor `s >= 4` of
  `04:389`.  The schedule restates it at `06-parameter-schedule.tex:122--124`
  ("Thus `s` is a public power of two.  The source theorem then fixes
  `q_2 = the least power of two at least 12 s N_E`"), `06:192` reuses it in
  the exact cancellation `N_src <= 4s(2 N_E + N_E) = 12 s N_E <= q_2`
  (`eq:source-template-count-cancellation`), and `06:2073` prints the matching
  upper bound `q_2 < 24 s |E(G)|`.  That display is already reified and banked
  as `EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2`
  (`q2 G s = 2 ^ clog_2 (12 s |E|)`), together with `card_le_q2`,
  `q2_le_of_le` (minimality) and `q2_lt`.  It is consumed here **by pin**;
  nothing about it is restated.
* **Admissibility is post-construction, never a field.**
  `05-public-records.tex:172--190` (`def:level-parameters`) fixes the shape of
  the one-level record: `Pi = (K, N_2, c_2)` with
  `c_2 : L_2 -> Rows(M_1(Public,K))^{q_2}` (`05:176--182`), and then says
  outright that positivity of `N_2` "is structural data ... because
  `LevelStep` must return nonempty communication carriers ... *before
  admissibility is checked*" (`05:183--186`), that "the balancedness formula
  remains a post-construction admissibility proposition; it is not a proof
  field of `Pi`" (`05:186--188`), and that "there are **no stored width**,
  tolerance, multiplicity, capacity, ceiling, or output-size fields"
  (`05:188--189`).  `q_2` occurs in that definition only inside the *type* of
  `c_2`, i.e. as a derived accessor of the intake -- which is exactly how it
  occurs below.

`05:167--170` is the sentence that makes this legal at this layer: "In
particular, the Stage-1 matrix `M_1(Public,K)` is already determined by these
accessors and the equations in `sec:one-level`; it is available when the type
of the balanced family is formed."

### The intake, and why it is `(G, s)` here

`def:level-trace` clause `T1` (`05:235--240`) fixes the source intake
literally: "`S = GuardedSource(G,s)` ... Here `G` is passed directly as the
endpoint-map graph from `Public` ... No conversion, quotient, or existential
relabelling occurs at this boundary."  The derived width is therefore a
function of that pair, in exactly the position the banked
`PublicRecords.LevelTrace (G : EndpointGraph V E) (s : ℕ)` and every banked
`GuardedSourceSlab` declaration already bind it.  No new binder is created:
`G` and `s` enter only as the two arguments the banked `q2` interface already
takes, at the guarded-source constructor's own reading of them
(`04:386--391`, "Let `G = (V,E,bd_0,bd_1)` be an ordered endpoint graph.  Let
`s >= 4` be a power of two, let `q_2 = min{2^r : 12 s |E| <= 2^r}`").  The
schedule's own choice of `s` is `eq:s-choice` (`06:118--120`); pinning this
module's `s` to it is the registered downstream obligation
`s = Section5Admissibility.sOf C` of ledger row `STAGE2-DERIVED-WIDTH-001`,
and **no parameter schedule may be read out of this module.**

### Honest scope of this round: `q_2` only, and the split

This section corrects **`q_2` only**, and it introduces **no new carrier**.
The three other numerals the Stage-2 gates mention -- `k_2`, `b_1`, `m_HS` --
are source-defined too (`eq:t2-search` `06:763--771`, `eq:stage1-scales`
`06:317`, and the `m_HS` display `06:250--255`), and their defining displays
evaluate through `ParameterSchedule` / `Section5Admissibility`, **both of
which import this module**.  They cannot be pinned here without an import
cycle, so a carrier holding them as free fields would only relocate the defect
this round exists to remove.  They therefore do not appear here as binders or
fields at all: they are read off the *banked* `StageTwoWidths` record, whose
own status as stored data is the pre-existing debt of `STAGE2-MODULE-001` and
is unchanged by this round.  The **registered downstream half** of ledger row
`STAGE2-DERIVED-WIDTH-001` is not a corrected carrier either, and nothing here
promises one: it is an **accessor surface** over
`Section5Admissibility.ScheduleContext`, on which each of those quantities
evaluates its own defining chain, the Stage-2 numeric gates are stated as
`WidthGateCore`, and `toStoredAt` bridges a gated context back into *this*
record for the consumers that have not moved yet.  Introducing a record that
bundled the four quantities with equations pinning each to its own chain would
contradict `02:85--88` ("recomputed from the constructed object"): it would be
a provable singleton constructing nothing.

The frozen name `Admissible` is deliberately **not** used here.
`def:admissible-parameters` (`05:719--735`) defines
`Admissible(Public, Pi, T)` as the nine-group conjunction
`WF /\ Source /\ Stage1 /\ Stage2 /\ Stage3 /\ Dense /\ Wrapper /\ Direct /\
ExtensionCoverage`, of which the Stage-2 numeric gates are one part of one
group; naming a four-conjunct numeric predicate `Admissible` would claim that
whole definition.  What is stated below is the migration hypothesis
`DerivedWidthCoherent` and the frozen Stage-2 gates read against the derived
width, nothing more.

**No consumer is touched.**  Nothing above this section changes except the
supersession label on the `StageTwoWidths` docstring.  `StageTwoWidths`
deletes last.

### Canonical inhabitation: REGISTERED AND DEFERRED

The paper's own instance of this intake is the scheduled `(G, s)` of a real
`LevelStep` call.  That construction is the OPEN ledger row `S5-LEVEL-STEP`
(`06:859--887`), so the canonical-inhabitation obligation for
`DerivedWidthCoherent` is **registered in `STAGE2-DERIVED-WIDTH-001` and
deferred**, to be discharged when `LevelStep` lands.  `auditStoredWidths`
below is an interim **NON-FIDELITY / BEYOND-PAPER AUDIT** probe and is
labelled as such at its own declaration: it audits *our* encoding at a point
the frozen text never visits, and it is never a substitute for the paper's
instance.

### Reader counterparts

This section claims **no** reader item, and the reason is recorded.  The
reader's one display of the derived width is `eq:paper-guarded-q2`
(`reader-facing/sections/A-stage4-details.tex:33--37`, label at line 36),
`q_2 = min{2^r : 12 s m_G <= 2^r}` with `12 s m_G <= q_2 < 24 s m_G`, which is
already claimed by the banked `GuardedSourceSlab.q2` under `SOURCE-SLAB-001`
and is **not** reclaimed here.  The other place the reader states the intake
is inside the hypothesis *prose* of `thm:parameterized-one-bit`
(`03-parameterized-construction.tex:60--62`, "form the public guarded source
`S(G,s)`, and let `q_2` be its width from `eq:paper-guarded-q2`"), and prose
is never cited as a statement.  The coherence bridge, the audit probe and the
supersession theorems are verification apparatus with no counterpart in either
document. -/

section DerivedWidth

open EthInapproximability.ParameterizedNP.GuardedSourceGraph (EndpointGraph)
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
  (q2 card_le_q2 q2_le_of_le q2_lt)
open EthInapproximability.ParameterizedNP.PublicRecords (publicInputYes)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### §12.1  The derived width and its exponent -/

/-- `log_2 q_2`, as an **accessor of the banked width itself** rather than a
second copy of the `04:391` display: `r_2 = log_2 (q_2(G,s))`.

The frozen text writes `log_2 q_2` constantly (`06:180`, `06:301`, `06:432`,
`06:2055`, `06:2075`, and the Stage-2 selector step `07:386--390`), so the
exponent needs a name; `r₂Of_eq_clog` proves that this name agrees with the
exponent the banked `q2` actually uses, so there is exactly one copy of the
display in the development.

**Cross-module pin (`cc-t6s-r3` reconciliation).**  This is the canonical home
of the intake-level exponent for the whole tranche: the downstream context
specialization `Section5Admissibility.DerivedWidths.r2At` consumes it and no
longer reifies `Nat.log 2 (q2 ...)` a second time.

*Registered residual, outside this tranche's edit licence.*  The banked tree
already carries the same reading twice more, both **strictly downstream** of
this module in the import DAG:
`AmbientWidthReadout.widthExp q₂ = Nat.log 2 q₂` (`09:937`, so
`r₂Of G s = widthExp (q2 G s)` definitionally) and
`AmbientWidthReadout.rTwoSched G s = Nat.clog 2 (12 s |E|)` (`11:70--71`,
equal by `r₂Of_eq_clog`).  `AmbientWidthReadout` imports this module through
`CertifiedLocalizedExtension -> ... -> StageThreeExactScale -> StageTwoRelaxed`,
so consuming them here would close an import cycle; unifying them requires
relocating the banked reification upstream, which is a separate round. -/
def r₂Of (G : EndpointGraph V E) (s : ℕ) : ℕ := Nat.log 2 (q2 G s)

/-- **Aux 12.1.**  The exponent accessor agrees with the banked width's own
exponent.  General in `G` and `s`.

**Cross-module pin (`cc-t6s-r3` reconciliation).**  The identity
`log_2 q_2 = clog_2(12 s |E|)` is already banked as `PublicRecords.log_q2`
(`PublicRecords.lean:1061`), so it is *consumed* here rather than re-proved;
this declaration only names the accessor form. -/
theorem r₂Of_eq_clog (G : EndpointGraph V E) (s : ℕ) :
    r₂Of G s = Nat.clog 2 (12 * s * Fintype.card E) :=
  PublicRecords.log_q2 G s

/-- **Aux 12.2.**  `q_2 = 2^{r_2}`: the derived width is the power of two its
exponent names.  This is the identity that replaces the superseded record's
*stored* `q_2 = 2^{r_2}`.  General in `G` and `s`. -/
theorem two_pow_r₂Of (G : EndpointGraph V E) (s : ℕ) :
    (2 : ℕ) ^ r₂Of G s = q2 G s := by
  rw [r₂Of_eq_clog]
  rfl

/-- **Aux 12.3 (monotonicity).**  The derived width is monotone in the slab
scale `s`, by the banked minimality `q2_le_of_le` against the banked lower
bound `card_le_q2`.  General in `G`, `s`, `s'`; nothing about the schedule is
used. -/
theorem q2_mono_in_s (G : EndpointGraph V E) {s s' : ℕ} (h : s ≤ s') :
    q2 G s ≤ q2 G s' := by
  have hchain : 12 * s * Fintype.card E ≤ 2 ^ r₂Of G s' := by
    rw [two_pow_r₂Of]
    exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) (card_le_q2 G s')
  have hle := q2_le_of_le G s hchain
  rwa [two_pow_r₂Of] at hle

/-- **Aux 12.4 (the rounded and the exact exponent agree).**  The frozen text
carries the exponent of `q_2` in two distinct displays, and this theorem is
exactly the statement that at the derived width they coincide.  Each side is
attributed to its own display; neither anchor covers both.

* **Left side, the rounded reading `ceil(log_2 q_2)`: `06:2055`.**  The `C7`
  auxiliary-output list of `thm:eff-ledger` carries `ceil(log_2 q_2)`
  next to `ceil(log_2 N_2)`, and `06:2057--2058` records that it "contains
  neither raw `q_2` nor raw `N_2`".  That ceiling is the left-hand side here,
  `Nat.clog 2 (q2 G s)`.
* **Right side, the exact reading `r_2 = log_2 q_2`: `07:390`.**  The closing
  selector step of `lem:stage2-one-depth` reads "Since `q_2 = 2^{r_2}`, apply
  `lem:indexed-selector-protocol` ... It sends exactly `r_2 = log_2 q_2`
  bits" (`07:387--390`), with no ceiling; that exponent is `r₂Of` of §12.1,
  the right-hand side here.  The same unrounded form is what `06:2075` bounds
  (`log_2 q_2 <= E_{c_{i+1}}(n)`).

Because the derived `q_2` is a power of two (`two_pow_r₂Of`) the rounding
costs nothing, so the ledger's rounded charge is the selector's exact one.
Unconditional: no gate is needed.  General in `G` and `s`. -/
theorem clog_q₂Of (G : EndpointGraph V E) (s : ℕ) :
    Nat.clog 2 (q2 G s) = r₂Of G s := by
  rw [← two_pow_r₂Of G s, Nat.clog_pow 2 _ (by norm_num)]

/-- **Aux 12.5 (monotonicity, exponent form).**  The derived exponent is
monotone in the slab scale, by injectivity of `2^(.)` against `q2_mono_in_s`.
General. -/
theorem r₂Of_mono_in_s (G : EndpointGraph V E) {s s' : ℕ} (h : s ≤ s') :
    r₂Of G s ≤ r₂Of G s' := by
  have h2 : (2 : ℕ) ^ r₂Of G s ≤ 2 ^ r₂Of G s' := by
    rw [two_pow_r₂Of, two_pow_r₂Of]
    exact q2_mono_in_s G h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

/-- **Aux 12.6 (nondegeneracy at the frozen floor).**  At the guarded-source
constructor's own floor `s >= 4` (`04:389`) the derived exponent is at least
`6`, so the derived width never collapses to a small carrier.

The `6` is **evaluated**, not chosen: `|E| >= 1` for an endpoint graph, so the
frozen count of `04:391` satisfies `12 s |E| >= 12 * 4 * 1 = 48`, while
`2^5 = 32 < 48 <= 2^{r_2}`.  General in `G` and `s`. -/
theorem six_le_r₂Of (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) :
    6 ≤ r₂Of G s := by
  have hE : 0 < Fintype.card E := G.card_edge_pos
  have h48 : 48 ≤ 12 * s * Fintype.card E := by nlinarith
  have hq : 48 ≤ (2 : ℕ) ^ r₂Of G s := by
    rw [two_pow_r₂Of]
    exact le_trans h48 (card_le_q2 G s)
  by_contra hcon
  have hle : (2 : ℕ) ^ r₂Of G s ≤ 2 ^ 5 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hle
  omega

/-! ### §12.2  The migration hypothesis, and its statement pole -/

/-- **The coherence hypothesis of the staged migration.**  A superseded
`StageTwoWidths` is coherent with the intake `(G, s)` exactly when its
*stored* width equals the width the frozen source *derives* from that intake,
`q_2 = min{2^r : 12 s |E| <= 2^r}` (`04:391`, restated `06:122--124`).

One clause, and it is the whole content of the correction:
`stored_width_is_not_derived` proves that it is a genuine restriction (it
fails at every stored record whose width is below the frozen count
`12 s N_E`), and `auditStoredWidths_coherent` proves it is satisfiable.

*Not a duplicate of the downstream coherence relation.*  The registered
downstream half of `STAGE2-DERIVED-WIDTH-001` states a strictly stronger
relation, over a *scheduled* intake: it additionally ties the three exponent
numerals `k_2`, `b_1`, `m_HS` to their defining displays, which requires the
schedule context and therefore the modules that import this one.  What is
defined here is the general intake-only width clause -- the one fact about an
arbitrary `(G, s)` that the downstream relation specializes at the scheduled
pair -- and it is the only part of the correction expressible without an
import cycle. -/
def DerivedWidthCoherent (W : StageTwoWidths) (G : EndpointGraph V E)
    (s : ℕ) : Prop :=
  W.q₂ = q2 G s

/-- **Aux 12.7.**  Coherence pins the exponent too, by injectivity of `2^(.)`:
a coherent record's stored `r_2` is the derived `r₂Of`.  So under coherence
every `log_2 q_2` the frozen bookkeeping writes (`06:180`, `07:387--390`) has
one and the same value, whichever carrier it is read from.  General. -/
theorem coherent_r₂_eq {W : StageTwoWidths} {G : EndpointGraph V E} {s : ℕ}
    (hc : DerivedWidthCoherent W G s) : W.r₂ = r₂Of G s := by
  have h : (2 : ℕ) ^ W.r₂ = 2 ^ r₂Of G s := by
    rw [two_pow_r₂Of]
    exact hc
  exact Nat.pow_right_injective (le_refl 2) h

/-- **`M3` check, in the kernel: the width is determined by the intake.**  Any
two coherent records over the same intake agree on `q_2` and on `r_2`,
whatever their other fields say.  This is the property the superseded record
does *not* have on its own, and it is why the corrected reading carries no
stored width.  General. -/
theorem coherent_unique_width {W W' : StageTwoWidths} {G : EndpointGraph V E}
    {s : ℕ} (hc : DerivedWidthCoherent W G s)
    (hc' : DerivedWidthCoherent W' G s) : W.q₂ = W'.q₂ ∧ W.r₂ = W'.r₂ :=
  ⟨hc.trans hc'.symm, (coherent_r₂_eq hc).trans (coherent_r₂_eq hc').symm⟩

/-- **The statement pole of the coherence hypothesis, in the kernel.**
Coherence is *not* free: at any intake whose frozen count `12 s N_E` exceeds
the stored width, the record is coherent with **no** intake-derived width at
all.  So the migration hypothesis has content, and the supersession is
substantive rather than cosmetic.

The trivial witness fails this: one cannot discharge coherence by choosing a
convenient derived width, because the derived width does not depend on the
record at all -- it is `q2 G s`, fixed by the intake, and bounded below by
`12 s N_E` through the banked `card_le_q2` (`06:192`).  General. -/
theorem stored_width_is_not_derived (W : StageTwoWidths)
    (G : EndpointGraph V E) {s : ℕ}
    (hlt : W.q₂ < 12 * s * Fintype.card E) : ¬ DerivedWidthCoherent W G s := by
  intro hc
  have hge : 12 * s * Fintype.card E ≤ q2 G s := card_le_q2 G s
  rw [hc] at hlt
  omega

/-! ### §12.3  The frozen Stage-2 gates, read against the derived width

These are the post-construction gates of `05:186--188`: they are checked
*after* the width exists, against the width the intake derives, and none of
them is constructor data of anything introduced here. -/

/-- **The frozen Stage-2 numeric gates over the derived width.**  The four
side conditions of `eq:stage2-balance-ceilings` (`07:280--281`: `4 t_2 <= q_2`
and `k_2 >= m_HS`), the tail-predicate clause `5 <= m_HS`
(`D-inherited-contracts.tex:496`) and the balancing gate `07:398--401` in its
cleared-denominator form, all stated against `q2 G s` rather than against a
stored width.

*Honest scope (`M2`/`M4`).*  This is decidable arithmetic in the record's
three exponent numerals and the derived width; no matrix, protocol, promise
certificate or complexity value enters it, and it is not constructor data. -/
theorem gates_at_derived_width {W : StageTwoWidths} {G : EndpointGraph V E}
    {s : ℕ} (hc : DerivedWidthCoherent W G s) :
    5 ≤ W.mHS ∧ W.mHS ≤ W.k₂ ∧ 4 * 2 ^ W.k₂ ≤ q2 G s ∧
      131072 * q2 G s ≤ 2 ^ W.b₁ := by
  refine ⟨W.five_le_mHS, W.mHS_le_k₂, ?_, ?_⟩
  · rw [← hc]
    exact W.four_t₂_le_q₂
  · rw [← hc]
    exact W.depth_gate

/-- The displayed real form of the balancing gate, `q_2 2^{-b_1} <= 1/131072`
(`07:399--400`), over the derived width. -/
theorem depth_gate_density_at_derived_width {W : StageTwoWidths}
    {G : EndpointGraph V E} {s : ℕ} (hc : DerivedWidthCoherent W G s) :
    ((q2 G s : ℕ) : ℝ) * xSeed W.b₁ ≤ 1 / 131072 := by
  rw [← hc]
  exact W.depth_gate_density

/-- **The frozen lower bound, now available on the record (`06:192`).**  Under
coherence the stored width dominates the exact source count
`N_src <= 4s(2 N_E + N_E) = 12 s N_E <= q_2` that
`eq:source-template-count-cancellation` closes the source-to-template
comparison with.  No stored record has this on its own. -/
theorem card_le_stored_q₂ {W : StageTwoWidths} {G : EndpointGraph V E} {s : ℕ}
    (hc : DerivedWidthCoherent W G s) : 12 * s * Fintype.card E ≤ W.q₂ := by
  rw [hc]
  exact card_le_q2 G s

/-- **The frozen upper bound, now available on the record (`06:2073`).**
`q_2 < 24 s |E(G)|`, at the guarded source's own floor `s >= 4` (`04:389`). -/
theorem stored_q₂_lt_card {W : StageTwoWidths} {G : EndpointGraph V E} {s : ℕ}
    (hc : DerivedWidthCoherent W G s) (hs : 4 ≤ s) :
    W.q₂ < 24 * s * Fintype.card E := by
  rw [hc]
  exact q2_lt G hs

/-- **The balancing gate as a depth floor over the derived exponent.**
`17 + r_2 <= b_1`: the cleared-denominator form `131072 q_2 <= 2^{b_1}` of
`07:398--401` is `2^{17} q_2 <= 2^{b_1}`, so under coherence the Stage-1
output depth of `eq:stage1-scales` is bounded below by the *intake's* own
exponent.  The `17` is evaluated, not chosen: `131072 = 2^{17}`. -/
theorem seventeen_add_r₂Of_le_b₁ {W : StageTwoWidths} {G : EndpointGraph V E}
    {s : ℕ} (hc : DerivedWidthCoherent W G s) : 17 + r₂Of G s ≤ W.b₁ := by
  have hr := coherent_r₂_eq hc
  have h2 : (2 : ℕ) ^ (17 + W.r₂) ≤ 2 ^ W.b₁ := by
    calc (2 : ℕ) ^ (17 + W.r₂) = 131072 * 2 ^ W.r₂ := by rw [pow_add]; norm_num
      _ ≤ 2 ^ W.b₁ := W.depth_gate
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

/-- **The balancing gate read entirely on the intake.**  Composing the frozen
lower bound `12 s N_E <= q_2` (`06:192`) with the balancing gate
(`07:398--401`) bounds the Stage-1 depth below by a quantity of the intake
alone.  This is the statement the superseded record cannot make: its stored
width is unrelated to `s` and `N_E`. -/
theorem intake_depth_bound {W : StageTwoWidths} {G : EndpointGraph V E}
    {s : ℕ} (hc : DerivedWidthCoherent W G s) :
    131072 * (12 * s * Fintype.card E) ≤ 2 ^ W.b₁ := by
  refine le_trans (Nat.mul_le_mul_left _ (card_le_stored_q₂ hc)) ?_
  exact W.depth_gate

/-! ### §12.4  Inhabitation

**NON-FIDELITY / BEYOND-PAPER AUDIT.**  The paper's own instance of this
intake is the scheduled `(G, s)` of a real `LevelStep` call, and that
construction is the OPEN ledger row `S5-LEVEL-STEP` (`06:859--887`).  The
canonical-inhabitation obligation is therefore registered in
`STAGE2-DERIVED-WIDTH-001` and deferred; the probe below discharges nothing of
it.  Its exponent numerals are self-chosen and it makes **no legality claim**:
at this intake `s - 3 <= N_E` (`06:179`) reads `61 <= 3` and fails, `k_2 = 9`
is far below the `eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}`
(`06:766`), and `b_1 = 29` is not of the form `2^{j_49(a-2)}` that
`eq:stage1-scales` (`06:317`) requires.  It audits exactly one thing: that the
coherence hypothesis is *reachable by evaluating the guarded-source chain*,
nondegenerately, at some point.  **No route parameter may be read out of
it.** -/

/-- **BEYOND-PAPER AUDIT probe.**  A superseded record over the audit intake
`(publicInputYes.G, 64)` whose stored exponent is **not written down**: it is
`r₂Of publicInputYes.G 64`, evaluated through the banked chain, so the probe
assigns no numeral to the width and is coherent by construction
(`auditStoredWidths_coherent`).  Its two width gates are proved from
`card_le_q2` and `q2_le_of_le`, never from a chosen width.

CROSS-MODULE PIN (cc-t6s-r4 reconciliation).  The intake graph is the banked
`PublicRecords.publicInputYes.G` -- itself the banked
`GuardedSourceGraph.K3` -- consumed **by pin** at every occurrence.  The
predecessor's one-line alias `auditIntakeGraph := publicInputYes.G` added no
content over the banked field projection and is removed: it was a third name
for one banked object, and the audit's `T1` provenance (the intake graph is the
public record's *own* `G`) is carried more directly by the projection itself.

The exponents `k_2 = 9`, `b_1 = 29`, `m_HS = 5` and the scale `64` are
self-chosen and claim **no** legality; see the section note. -/
def auditStoredWidths : StageTwoWidths where
  k₂ := 9
  r₂ := r₂Of publicInputYes.G 64
  b₁ := 29
  mHS := 5
  five_le_mHS := le_refl 5
  mHS_le_k₂ := by norm_num
  four_t₂_le_q₂ := by
    rw [two_pow_r₂Of]
    exact le_trans (by norm_num [Fintype.card_fin])
      (card_le_q2 publicInputYes.G 64)
  depth_gate := by
    rw [two_pow_r₂Of]
    calc 131072 * q2 publicInputYes.G 64
        ≤ 131072 * 2 ^ 12 :=
          Nat.mul_le_mul_left _
            (q2_le_of_le publicInputYes.G 64 (by norm_num [Fintype.card_fin]))
      _ ≤ 2 ^ 29 := by norm_num

/-- **Non-vacuity of the coherence hypothesis (BEYOND-PAPER AUDIT).**  The
hypothesis is satisfiable, and satisfied by evaluating the definitional chain
rather than by choosing a width: the probe's stored exponent *is* the derived
one, so coherence is exactly `2^{r₂Of} = q2`, i.e. `two_pow_r₂Of`.
`stored_width_is_not_derived` supplies the other half. -/
theorem auditStoredWidths_coherent :
    DerivedWidthCoherent auditStoredWidths publicInputYes.G 64 :=
  two_pow_r₂Of publicInputYes.G 64

/-- **BEYOND-PAPER AUDIT.**  The probe is nondegenerate: the independence
width is a genuine multiple of `16`, strictly below the derived ambient width,
the derived width is pinned between the frozen count `12 s N_E` and the next
power of two, and the depth clears the frozen `b_1 >= 24` floor.  Nothing here
collapses.

The numerals `2304` and `4096` in this statement are the **evaluations** of
`12 * 64 * 3` and `2^{12}` at the audit intake, so they are BEYOND-PAPER AUDIT
numerals exactly as the intake is.

CITATION REPAIR (cc-t6s-r4, Sol's cc-t6s-r3 FINDING 2, verbatim: this prose
"attributes both `16` and `24` to frozen Stage-2 displays.  `16` is the printed
divisibility constant; `24 <= b_1` is an evaluated banked consequence, namely
the previous `7+17` derivation, not a printed frozen constant").  Corrected:
`16` is the printed divisibility constant of `eq:stage2-balance-ceilings`
(`07:280`).

PROSE REPAIR (cc-t6s-r6, Sol's r5 finding 12: the r4 sentence "falsely
describes the proof of `StageTwoWidths.twentyFour_le_b₁`", there being **no**
banked `17 + r_2 <= b_1` theorem at the `StageTwoWidths` layer -- that exponent
form is `seventeen_add_r₂Of_le_b₁`, one layer up at the derived accessors).
`24` is **not** printed anywhere, and `StageTwoWidths.twentyFour_le_b₁` derives
it from the record's own two fields: the banked `seven_le_r₂` (itself
`five_le_k₂` composed with `k₂_add_two_le_r₂`) supplies `7 <= r_2`; the
arithmetic identity `2^24 = 131072 * 2^7` then chains
`2^24 <= 131072 * 2^{r_2}`; and the `depth_gate` field -- the denominator-cleared
form of the balancing consequence `q_2 2^{-b_1} <= 1/131072` of `07:398--401` --
carries that to `2^24 <= 2^{b_1}`, from which base-2 injectivity strips the
power.  So `24` is evaluated arithmetic over two frozen inputs, obtained
without any exponent-form lemma.  No route parameter may be read out of
this. -/
theorem auditStoredWidths_nondegenerate :
    16 ∣ auditStoredWidths.t₂ ∧ auditStoredWidths.t₂ < auditStoredWidths.q₂ ∧
      2304 ≤ auditStoredWidths.q₂ ∧ auditStoredWidths.q₂ ≤ 4096 ∧
      24 ≤ auditStoredWidths.b₁ := by
  refine ⟨auditStoredWidths.sixteen_dvd_t₂, auditStoredWidths.t₂_lt_q₂, ?_, ?_,
    auditStoredWidths.twentyFour_le_b₁⟩
  · have h := card_le_stored_q₂ auditStoredWidths_coherent
    rw [Fintype.card_fin] at h
    omega
  · rw [auditStoredWidths_coherent]
    have h : q2 publicInputYes.G 64 ≤ 2 ^ 12 :=
      q2_le_of_le publicInputYes.G 64 (by norm_num [Fintype.card_fin])
    norm_num at h
    exact h

/-- **The recorded `cc-t6r` defect, in the kernel.**  The superseded module's
own componentwise-least record `widthsWitness` stores `q_2 = 128`, which is
below the frozen count `12 * 64 * 3 = 2304` at the audit intake, so it is
coherent with that intake's derived width for **no** reason of arithmetic:
`stored_width_is_not_derived` refutes it outright.  This is precisely the
failure mode the staged migration exists to remove -- a stored width that the
intake's own defining display contradicts.

The intake this is exhibited at is the **BEYOND-PAPER AUDIT** one, so the `64`
is a self-chosen numeral claiming no legality; the general statement, at every
intake, is `stored_width_is_not_derived`. -/
theorem widthsWitness_not_coherent_at_audit_intake :
    ¬ DerivedWidthCoherent widthsWitness publicInputYes.G 64 := by
  refine stored_width_is_not_derived widthsWitness publicInputYes.G ?_
  have hq : widthsWitness.q₂ = 128 := rfl
  rw [hq, Fintype.card_fin]
  norm_num

end DerivedWidth

end EthInapproximability.ParameterizedNP.StageTwoRelaxed
