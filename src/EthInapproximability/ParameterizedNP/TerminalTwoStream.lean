import EthInapproximability.ParameterizedNP.TerminalStateRealization

/-!
# Parameterized NP route: the terminal two-stream lemma

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8a54aaa6f0e60eaeb31ac1719cd696b169d5a845381fbd810a18a86c6b2a24e5`),
  **lines 834--1183** -- `lem:terminal-two-stream` together with its proof,
  opening immediately after `lem:terminal-state-realization`'s proof (whose
  last line `09:832` the predecessor module discharges) and stopping at the
  `readingwarning` box `09:1176--1182`.  The anchors traced here, in the order
  the frozen block prints them:
  * `lem:terminal-two-stream` (label `09:835`, statement `09:834--860`):
    * `eq:terminal-entry` (label `09:843`, display `09:838--844`)
      `q_2 >= 16`, `lambda_0 <= 1/8`, `delta' >= lambda_0 + 5 eps + 2/q_2`;
    * `eq:terminal-seed-inputs` (label `09:852`, display `09:846--853`)
      `Lambda_{M_1^T}(1, 2^{-b_1}, y) >= B_cap`,
      `Lambda_{S_2}(1, x_T, y) >= D_2`, `log_2 s < b_T`, with
      `S_2 = M_2^T` and `D_2 = B_cap + log_2 q_2` (`09:854--855`);
    * `09:856--858`, "the fixed-width hypotheses of Localized Extension for the
      `C_2 x C_2` product family, as listed for call (ii) in
      `sec:extension-call-ledger`" -- the call ledger's description of that
      family is `06:1116--1123` (`M^_v` is the relaxed interlace represented by
      the `v`-fold Cartesian product of the physical family `C_2`; ambient copy
      count `q_amb = v q_2`, independence width **still `t_2`**, balancedness
      error `eps_2` at `v = 1` and at most `eps_prod` otherwise), and
      `06:1163--1166` lists "the product balancedness error" among the four
      items the gates verify;
    * `09:858--859`, the conclusion "Then the state has communication
      complexity at least `C`", at `C = D_2 + log_2 s + 1` (`09:1038`,
      `09:1777`).
  * the Stage-2 calculation `09:871--1033`:
    * `eq:terminal-averages` (label `09:878`, display `09:874--879`);
    * the three counting sets `H, F, Z` and the counts `b, w` (`09:880--889`);
    * `eq:terminal-bw` (label `09:899`, display `09:895--900`) with its two
      frozen justifications at `09:890--894`;
    * `eq:terminal-excess` (label `09:911`, display `09:902--912`), including
      `|Z| >= w - b` (`09:901`) and the closing `> 2`;
    * `09:913--914`, "`delta' <= 1` and `eq:terminal-entry` imply `eps < 1/5`";
    * `09:928--930`, the Bob support threshold `lambda_d = lambda_0 2^{-d}`,
      **consumed by pin** from the banked `DenseRoutingThresholds.lambdaAt`
      (`08:812--816`) and never restated;
    * `09:937--942`, `r_2 = log_2 q_2` and `lambda_d >= lambda_{r_2} =
      2^{1-b_1}`;
    * `09:953--965`, the isolation capacity `kappa_v = 2^{r_2-d_v}`, the
      capacity-one case `kappa_v = 1 => d_v = r_2`, and the residual budget
      `D_2 - r_2 = B_cap` (`09:960--962`);
    * `09:967--978`, `lambda_{r_2+1} = 2^{-b_1}` and
      `D_2 - (r_2+1) = B_cap - 1` (`09:974--976`);
    * `eq:terminal-first-alice` (label `09:993`, display `09:989--994`);
    * `eq:terminal-stage2-budget` (label `09:1001`, display `09:998--1002`);
    * `09:1009--1012`, the post-query typed density `49/128 > 9/25`;
    * `09:1014--1019`, the Extension call (ii) substitution -- ambient width
      `2 q_2`, represented capacity `kappa_v`, post-query column density
      `49/128`, `9 kappa_v/16` selected coordinates;
    * `eq:terminal-fixed-bin` (label `09:1032`, display `09:1030--1033`).
  * the Stage-3 lift `09:1036--1173`:
    * `09:1037--1038`, `C - 1 = D_2 + log_2 s` and `r_3 = log_2 s`;
    * `09:1049--1053`, the Alice row threshold `tau_d = 2 s x_T 2^{-d}`;
    * `09:1068--1076`, `sum_{d >= 0} tau_{d+1} = tau_0` and the transferred
      typed density `49/64`;
    * `09:1086--1095`, the column density `1 - eps > 4/5 > 3/5` and the row
      floor `tau_d >= tau_{r_3} = 2 x_T`;
    * `09:1097--1110`, the isolation capacity `kappa_v = 2^{r_3-d_v}` and the
      two exclusions;
    * `eq:terminal-first-bob` (label `09:1122`, display `09:1118--1123`);
    * `eq:terminal-bob-child-density` (label `09:1131`, display
      `09:1129--1132`);
    * `eq:terminal-stage3-two-copy` (label `09:1142`) and
      `eq:terminal-stage3-odd-copy` (label `09:1146`), the `ell = 1` and
      `ell = log_2 kappa` instances of `lem:certified-row-ladder`;
    * `09:1148--1150`, the scale guard `H >= 2` and the row-density legality
      `kappa <= s < 2^{b_T}`;
    * `09:1152--1156`, `kappa >= 4 => h_v >= 3 kappa/4 >= kappa/2 + 1`;
    * `eq:terminal-stage3-budget` (label `09:1170`, display `09:1167--1171`)
      and the closing contradiction `09:1172--1173`.
* **Predecessor anchor for the Extension call row:**
  `06-parameter-schedule.tex`, `sec:extension-call-ledger` (label `06:1103`):
  `eq:extension-common-binders` (label `06:1113`, display `06:1107--1114`),
  the ambient/independence/capacity conventions `06:1115--1130`, row **(ii)**
  `06:1140--1145`, and the uniform closing conditions `06:1161--1162`.
* **Anchors for the two checked-identity pins:** `x_T = 2^{-b_T}` at
  `06-parameter-schedule.tex` **line 243** (the Stage-3 depth block
  `k_T = log_2(s/4)`, `b_T = 2^{j_49(k_T)}`, `x_T = 2^{-b_T}`), restated at
  `08-dense-stage4.tex` **line 166**; `y = 3/5` at `05-public-records.tex`
  **line 542** (`ExtensionCoverage`, the common branch-neutral binders) and
  `09:1137` (`z = y = 3/5`, where the certified row ladder is applied).
* **Anchor for the Extension call's frozen domain:** `09:1013--1016` --
  "If `kappa_v >= t_2`, select `9 kappa_v/16` ordinary coordinates ... and
  invoke Localized Extension at the fixed physical width `t_2`.  This is
  exactly call (ii) ... If `2 <= kappa_v < t_2`, the inherited two-copy and
  odd-copy bounds give the same target.  If `kappa_v = 1`, the positive excess
  ... supplies either an unsplit attached pair or two ordinary coordinates."
* **Width conditions carried by the banked record:** `eq:stage2-balance-ceilings`
  (`07-one-level-construction.tex`, display `07:277--288`, lines `07:278--281`)
  -- all seven of `t_2 = 2^{k_2}`, `t_2 | q_2`, `q_2 = 2^{r_2}`, `16 | t_2`,
  `4 t_2 <= q_2`, `k_2 >= m_HS`, `t_2 <= 2^{b_1}` -- consumed by pin as
  `StageTwoRelaxed.StageTwoWidths`.
* **Anchors for the call-(ii) fixed-width hypotheses:**
  `eq:epsilon-product` (`06:851--857`), the product-application majorants
  `06:938--940`, `eq:all-extension-gates` (label `06:950`, display
  `06:941--951`), the call table's closing sentences `06:1161--1167`, and
  `eq:certified-E1`/`eq:certified-E2` (`A:130--137`).
* **Anchors for the `C_2 x C_2` product family** (repair r3): the call ledger's
  description `06:1116--1123` (`M^_v` is the relaxed interlace represented by the
  `v`-fold Cartesian product of `C_2`; `q_amb = v q_2`; independence width still
  `t_2`; error `eps_2` at `v = 1`, at most `eps_prod` otherwise), the gate
  content sentence `06:1163--1166`, the checked inherited definition
  `eq:contract-balanced` (`D:534--548`, which *is* `NPCC.IsBalancedFamily`), the
  transcription contract `eq:contract-product-family` /
  `eq:contract-product-error` (`D:620--632`), the frozen human proof
  `lem:product-balancedness` (`A:333--356`) with its reboot-bridge status
  (`03:333--337`, `D:604--638`), and the exactly-balanced inhabitant clause
  `A:120--122`.

## Repair r3 (this generation)

The r2 generation was **parked, not banked**: 95 of its 97 declarations were
CLEAR and are preserved byte-for-byte here; its statement gate returned REVISE
on a single mathematical defect, repaired below and nowhere else.

**F-4 (the fixed-width binder pinned the errors but bound them to no family).**
`ExtensionCallTwoFixedWidth` took `(W) (bcap Lh vmax : ℕ) (eps2 epsProd : ℝ)`
and **no family argument at all**.  Its first conjuncts pinned `eps_2` and
`eps_prod` to closed formulas in `t_2`, so they were determined reals; but
nothing asserted that the headline's own `cFam` is a `(q_2,t_2,eps_2)`-balanced
family, or that its `2`-fold product has error at most `eps_prod`.  So `cFam`
was arbitrary -- the constant family was admissible -- and the two inherited
column-loss inequalities were stated *in* an error that constrained nothing
about the construction.  `09:856--858` says the fixed-width hypotheses are
assumed "for the `C_2 x C_2` **product family**", and `06:1116--1123` is the
call ledger's own description of that family; `06:1163--1166` lists "the
product balancedness error" among the four items the gates verify, so it is
gate content, not an aside.  As stated, the r2 headline was therefore strictly
**stronger** than `lem:terminal-two-stream`: it asserted the terminal bound for
constructions in which the Localized Extension call of `09:1014--1019` has no
licence to fire.

The repair is one binder plus its threading, and no new mathematics:
`ExtensionCallTwoFixedWidth` now takes the family, and carries the two clauses
of `06:1116--1123` as fields 10 and 11 -- `IsBalancedFamily t_2 (C_2) eps_2` and
`IsBalancedFamily t_2 (C_2 x C_2) eps_prod`, both at the vendored
`NPCC.IsBalancedFamily` and both at the independence width `t_2` (`06:1121`
keeps that width fixed; only the ambient copy count moves to `q_amb = 2 q_2`).
The headline threads its **own** `cFam` into the binder and gains
`[DecidableEq Rone]`, exactly as `TwoStreamState` already carries
`[DecidableEq Cone]`.  Adding hypotheses *weakens* the statement toward the
frozen lemma, which is the correct direction.  Both new fields are discharged
at a nondegenerate model in this same tranche
(`extProbe_fixedWidth_holds`): `A:120--122`'s exact full product over a
two-letter column alphabet, proved exactly balanced by
`isBalancedFamily_zero_of_bijective` and transported to the schedule tolerances
by `isBalancedFamily_mono`.  No axiom cost is incurred: a hypothesis binder
needs a model, not the AGHP existence statement `EXPANDER-001`, which remains a
cited external input with no Lean declaration (see GAP-EXPOSED 6).

Everything else in the module is the r2 content unchanged.  In particular
`extensionCallTwo` and its four lemmas are untouched (r1 F-2), and the entire
F-3 repair -- `certifiedRowLadder_of_base` and its five consumers -- is retained
as it stood.

## Repair r2 (the predecessor generation)

The r1 generation was **parked, not banked**: its statement gate
returned REVISE on two mathematical defects, both repaired then and nowhere
else.

**F-1 (width conditions and the fixed-width Extension hypotheses).**  The
headline bound three of the seven frozen width conditions of `07:277--281` by
hand -- `q_2 = 2^{r_2}`, `t_2 = 2^{k_2}`, `16 | t_2` -- and dropped `t_2 | q_2`,
`4 t_2 <= q_2`, `k_2 >= m_HS`, `t_2 <= 2^{b_1}`.  The dropped `4 t_2 <= q_2` is
load-bearing: without it the reached-capacity Extension binder is satisfied
vacuously, since at `t_2 > q_2 = 2^{r_2}` no `stoppingCapacity r_2 d = 2^{r_2-d}`
ever meets its guard.  The headline now takes the **banked**
`StageTwoRelaxed.StageTwoWidths` record, which carries all seven (four as
fields, four as derived telescopes) and additionally the balancing gate
`07:398--401`; no width binder is hand-rolled.  Separately, `09:856--858`
assumes "the fixed-width hypotheses of Localized Extension ... as listed for
call (ii)", of which the predecessor transcribed **none**; they are now the
explicit binder `ExtensionCallTwoFixedWidth`.

**F-3 (the certified row ladder had no inhabitant).**  `CertifiedRowLadder` was
carried as an unwitnessed hypothesis of the four Stage-3 lemmas, and its
legality guard `2^ell x <= 1` is empty at any `x > 1/2`, so the hypothesis was
satisfiable by vacuity and the four consequences established nothing
(LANE-GATE 3).  `lem:certified-row-ladder` (`A:148--162`) is now **PROVED**, as
`certifiedRowLadder_of_base`, from its own frozen antecedents, by the frozen
proof `A:163--198`: the inherited two-copy ladder for the base case, bracket
monotonicity plus the row-step contract for the induction step.
`certifiedRowLadder_of_seedInputs` then discharges the hypothesis from
`eq:terminal-seed-inputs`' own second conjunct together with `scale_guard`, and
`stage3_two_copy_of_seedInputs` / `stage3_odd_copy_of_seedInputs` restate the
two Stage-3 instances with the hypothesis removed.

Machine evidence for repair r2, as recorded by that generation
(`scratch/CCT2YR2Probes.lean`, disposable, three `example`s each expected to
fail; probes 1 and 2 are re-run in this generation's probe file and still
fail at the same steps):
* probe 1, the r0 countermodel against the repaired reached-capacity binder --
  **fails**, stuck at the unprovable guard `2^{k_2} <= 1`;
* probe 2, the r1 vacuity construction for `CertifiedRowLadder` at the pinned
  `x_T` -- **fails**, stuck at `1 < 2^ell x_T`, i.e. the guard demonstrably
  fires at `ell <= b_T = 8`;
* probe 3, `False` from the full r2 hypothesis bundle (the width record, the
  entry conditions at `eps = 1/100`, `delta' = 1/10`, `delta' <= 1`, both pins,
  `log_2 s < b_T`, the fixed-width binder and the `forall`-form capacity binder)
  -- **fails**, with every arithmetic consequence already in context.

## Repair r1 (the predecessor generation)

The predecessor generation of this module was **parked, not banked**: its
headline's sixth binder was `forall K, 1 <= K -> K <= 2 q_2 ->
extensionCallTwo q_2 t_2 K`, and `extensionCallTwo` then carried both `t_2 | K`
and `16 | t_2`.  Instantiating at `K = 1` forces `t_2 = 1` and then `16 | 1`, so
that hypothesis bundle was *self-contradictory* and the headline was provable
for arbitrary `Nmat`, `X_Z`, `Y_Z` with no complexity content whatever.  Four
things changed, and nothing else:

1. **The Extension binder is requantified over the reached dyadic capacities.**
   `09:1013` makes call (ii) only in the branch `kappa_v >= t_2`, at the
   isolation capacities `kappa_v = stoppingCapacity r_2 d` banked in
   `DenseWeightedCount`; `2 q_2` was never a quantifier range but the *ambient*
   width `q_amb = v q_2` of `06:1120--1123`, and it survives only inside
   `r = q_amb/t_2` in `extensionCallTwo`.  `t_2 = 2^{k_2}` and `16 | t_2` are
   now separate width binders (`07:278--280`), not per-capacity clauses.
   `repaired_extension_binder_avoids_unit_capacity` proves the guard can fire
   only at capacities `>= 16`, so the refuted discharge is unavailable;
   `legacy_extension_binder_is_self_contradictory` preserves the refuted shape
   as an exact machine-checked witness.
2. **`x_T` and `y` are pinned by checked-identity binders.**  `x_T = 2^{-b_T}`
   and `y = 3/5` were carried free, which left `row_density_legal` (stated at
   `xTdepth bT`) and the two Stage-3 ladder instances (hardwired at `3/5`)
   unable to compose with the headline at all.  `row_density_legal` is re-sited
   through `row_density_legal_at_capacity` / `two_xT_le_one`, and
   `stage3_ladder_at_reached_capacity` / `stage3_ladder_two_copy_at_pins`
   perform the composition that the predecessor could not.
3. **The repaired bundle is inhabited in this same tranche.**  Section 9 fixes
   the Stage-3 probe scalars and discharges every arithmetic binder of the
   repaired headline simultaneously, including the `forall`-form Extension
   binder, with `probeExtensionDomain_nonempty` showing that domain is
   nonempty (so the binder is not satisfied by vacuity).
4. **The consistency lemma is restated at the actual `forall` form** with a
   docstring that says what it does and does not establish.  The predecessor's
   version listed the pointwise `extensionCallTwo ... 32` while the headline
   bound a `forall`, so its claim did not describe the statement it accompanied.

Machine evidence for the repair, re-run this generation
(`scratch/CCT2YR3Probes.lean`, disposable):
* probe 1, the r0 countermodel against the **repaired** reached-capacity
  binder -- fails, at the predicted step, the guard
  `t_2 <= stoppingCapacity r_2 r_2 = 1` (residual goal `2^{k_2} <= 1`);
* probe 2, the r1 vacuity construction for `CertifiedRowLadder` at the pinned
  `x_T = 1/256` -- fails, at the predicted step, the `absurd` on the legality
  guard (residual goal `1 < 2^ell/256`, false for `ell <= 8`);
* probe 3, the F-4 asymmetry, in two halves at *identical* widths and
  *identical* schedule numerals: 3a discharges the r2 (family-free) bundle
  shape at the constant family and **succeeds**, reproducing the defect state;
  3b attempts the same discharge against the repaired bundle and **fails**, at
  the predicted step, the first `06:1116--1123` field
  (`IsBalancedFamily t_2 (familyOnIndices (fun _ _ => false)) eps_2`).  That the
  failure is genuine and not an elaboration accident is proved in the library by
  `constant_family_not_balanced` and `extProbe_constantFamily_fails`;
* probe 4, `False` from the full r3 bundle at the paper-mandated side
  conditions (`delta' <= 1`, the three dyadic conventions, both pins,
  `eq:terminal-entry`, `log_2 s < b_T`, the fixed-width binder *including* both
  balancedness fields, the `forall`-form Extension binder) -- fails, with every
  arithmetic consequence of the bundle already in context.

## Predecessor modules consumed **by pin**, never restated

* `EthInapproximability.ParameterizedNP.TwoStreamState` (SHA-256
  `1dd7eaf859765fec9d99fcbfed3841e581ea41e09e5150fd0e9b2b08ba378530`):
  `TwoStreamState` itself and its derived readouts `streamImage`,
  `fibreDensity`, `meanFibreDensity`, `outer_width_pos`,
  `fibreDensity_mem_Icc`, `lambdaZero_pos`.  `def:two-stream-state` is
  **never restated**: `lem:terminal-two-stream` takes the banked record as a
  binder, exactly as `09:836--837` does.
* `EthInapproximability.ParameterizedNP.TerminalStateRealization` (SHA-256
  `944677087ebbb38f1c362386b3a4f291979e37930d7486df64b294f572c496a4`):
  the realization theorem is what *produces* the record this lemma consumes.
  Nothing from it is re-proved here; the import is what makes the two frozen
  blocks speak about one object.
* `DenseRoutingThresholds.lambdaAt` (`08:812--816`) -- `09:928--930`
  reintroduces `lambda_d = lambda_0 2^{-d}`; the frozen text repeats the
  definition, this module does not.
* `DenseBranchSelection.lambdaZero` (`08:796`) and `.Dtwo` (`08:152`,
  `08:769`) -- `lambda_0` and `D_2 = B_cap + log_2 q_2` of `09:479`,
  `09:854--855` and `09:864--866`.
* `DenseWeightedCount.stoppingCapacity` (`08:1113`) -- `kappa_v = 2^{r-d_v}`
  is the *same* object at the Stage-2 exponent `r_2` and at the Stage-3
  exponent `r_3`; both occurrences below are that pin at two widths.
* `StageOneInterlace.xSeed` (`09:477`) and `DenseStageFourOpening.xTdepth`
  (`08:166`) -- `x = 2^{-b_1}` and `x_T = 2^{-b_T}`.
* `WrapperProjectionCovers.tauZero` (`09:376`, `09:609`) -- `tau_0 = 2 s x_T`,
  the root of the Stage-3 Alice ladder `09:1049--1053`.
* `StageTwoRelaxed.StageTwoWidths` (`07:278--281`, `07:398--401`) -- **the
  headline's width binder** (repair r2): all seven frozen width conditions plus
  the depth gate.  Two clauses of `eq:terminal-entry` are **discharged** from it
  rather than assumed (`terminalEntry_of_stageTwoWidths`), and so is the legal
  row range of `06:1164` (`extensionCallTwo_row_range`).
* `StageTwoRelaxed.hSeedTwo` (`07:288--293`) -- the frozen hard-seed column
  density `h_{t_2} = 2^{-2^{0.49 sqrt(log_2 t_2)}}` that `eq:certified-E2`
  compares against; consumed by pin, never restated.
* `NPCC.yLoss` (`D:653--666`) -- the frozen column-loss density
  `y_c(h) = (h 2^{-c}/(1+eps))^{1/t}` in which `eq:certified-E1` is stated.
* `TwoCopyLadder.lambdaTwoCopy` (`D:338--340`, the inherited two-copy ladder),
  `ThreeCopyRowStep.rowStep` (`eq:contract-row-step`, `D:377--389`) and
  `InheritedContracts.bracketMonotonicity` (`eq:contract-monotonicity`,
  `D:157--172`) -- the three checked inherited contracts the frozen proof of
  `lem:certified-row-ladder` cites, consumed by pin and composed, never
  restated or re-proved.
* `NPCC.LambdaGE`, `NPCC.Dfamily`, `NPCC.bracketGE`,
  `Workspace.Types.CommComplexity.D`, `NPCC.subgame`,
  `Workspace.Types.Interlace.interlaceFun` -- the vendored, project-axiom-free
  complexity interface reached through `LegacyNPCC.Core`.  `LegacyNPCC.Stage12`
  is **not** imported and `EXPANDER-001` occurs in no hypothesis here.
* `NPCC.IsBalancedFamily` (`def:balanced-family`, `vendor/npc-cc/NPCC/Relaxed.lean:19`)
  -- the balancedness predicate of `06:1116--1123`, consumed by pin for repair r3
  (F-4) in the same shape as the banked `hbal` binders of
  `StageTwoRelaxed.stageTwoOneDepth` (`StageTwoRelaxed.lean:1592`) and
  `.stageTwoTwoDepthCertificate` (`:1955`).  `Relaxed.lean` imports only
  `Mathlib` and `NPCC.Defs`, so the AGHP existence axiom of `NPCC.Axioms` stays
  outside this module's closure: `EXPANDER-001` is an *existence* statement at
  the frozen Stage-2 carriers, and a hypothesis binder needs a model, not an
  existence theorem.  The model used is `A:120--122`'s exact full product.

## GAP-EXPOSED (what this module deliberately does not claim)

1. **The lemma itself is not proved.**  `TerminalTwoStream` is landed as a
   named claim about the pinned construction (the frozen statement, letter
   exact) and is *stated only*.  No declaration below has it as a conclusion,
   and in particular there is no theorem deriving it from an assumed routing
   conclusion: an "assume the frontier verdict" hypothesis would typecheck and
   prove nothing, which is exactly the statement pole this module refuses.
2. **The protocol-side phases are not modelled.**  The token routing
   (`09:924--935`), the split-or-route support rule, the isolation-node
   uniqueness count (`09:953--965`), the two premature-leaf exclusions
   (`09:967--978`, `09:1107--1110`), the appeal to `lem:dense-weighted-frontier`
   at `09:980--994` and `09:1112--1123`, the Alice/Bob child selections, and
   the Localized Extension invocation itself are **not** declared.  What is
   landed is every *arithmetic* phase those steps consume or produce, at the
   frozen constants, plus the two counting estimates that are pure measure
   theory on the banked record.
3. **`lem:certified-row-ladder` (`A:148--162`) is PROVED here** (repair r2), as
   `certifiedRowLadder_of_base`, from the three checked inherited contracts its
   frozen proof cites; it is *not* an axiom and no longer an unwitnessed
   hypothesis.  `CertifiedRowLadder` survives as the predicate the four Stage-3
   lemmas quantify, `certifiedRowLadder_is_not_free` still shows the predicate
   has content, and `certifiedRowLadder_guard_is_live` shows its legality guard
   fires at the pinned scalars.  Its reader counterpart
   `lem:paper-certified-row-ladder` (`02:244--256`) is claimed here and by no
   other module.  What is *not* claimed is the certified-scale **stopping**
   theorem `thm:certified-localized-extension` (`A:108--147`), which is a
   different statement and remains untranscribed.
4. **`sec:wrapper-projection-covers` is untouched.**  This block **feeds**
   `hDenseRung` and neither discharges nor narrows it; the ranges
   `09:1184--1366`, `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly
   as `ScaleAlignOpening` records them, and **no route completion is claimed**.
5. **The Localized Extension corollary's *conclusion* is not asserted.**  What
   is landed is the call table's row (ii) substitution (`06:1140--1145`), its
   uniform per-call legality conditions (`06:1161--1162`, as `extensionCallTwo`,
   *discharged* at the frozen dyadic widths by `extensionCallTwo_of_widths`),
   and -- new in r2 -- the fixed-width hypothesis list of `06:1163--1167`
   (`ExtensionCallTwoFixedWidth`).  The corollary
   `thm:certified-localized-extension`'s conclusion `eq:certified-E3` is
   asserted nowhere, and neither is the frozen claim of `06:952--953` that
   `eq:all-extension-gates` *implies* the literal fixed-width hypotheses: both
   inherited column-loss inequalities are therefore carried in the binder
   alongside the two gates rather than derived from them.
6. **The *existence* of a balanced family at the frozen Stage-2 carriers is not
   claimed** (repair r3 closes the predecessor generation's F-4 here).
   `06:859--860` constructs "the one indexed `(q_2,t_2,eps_2)`-balanced family
   `C_2`", and that *existence* is the cited AGHP input (`EXPANDER-001`), which
   has no Lean declaration by design; `LegacyNPCC.Stage12` remains unimported and
   nothing here reaches `NPCC.Axioms`.  What the predecessor generation wrongly
   concluded from this was that balancedness could be *omitted* from the
   headline: it pinned `eps_2 = 1/(100 t_2)` and `eps_prod < 1/50` as numerals
   and bound them to no family, which left `cFam` arbitrary and made the
   headline strictly **stronger** than `lem:terminal-two-stream` -- the wrong
   direction.  The two clauses of `06:1116--1123` are now explicit fields of
   `ExtensionCallTwoFixedWidth`, about the headline's own `cFam`, exactly as
   `09:857` demands ("for the `C_2 x C_2` product family"), and they are
   discharged at a nondegenerate model (`A:120--122`'s exact full product over a
   two-letter column alphabet, `extProbe_fixedWidth_holds`).  A binder needs a
   model, not an existence theorem at the frozen carriers, so no axiom cost is
   incurred.  Still **not** claimed: that such a family exists at the frozen
   Stage-2 carriers `L_2 = [N_2]`, `q_2`, `t_2` with the frozen `eps_2` -- that
   is `EXPANDER-001` and it stays a cited external input with no Lean
   declaration.
7. **`lem:product-balancedness` (`A:333--356`) is not proved here.**  The frozen
   paper proves that a `(q,t,eps_0)`-balanced family's `v`-fold Cartesian
   product is `(vq,t,eps_*)`-balanced, but `03:333--337` and `D:604--638` record
   that its Lean transcription is a **required reboot bridge**, explicitly not
   an importable checked dependency ("a proved human lemma but still a missing
   Lean declaration").  This module accordingly transcribes the product family
   by the exact contract `eq:contract-product-family` (`D:620--624`) as
   `productFamily`, and carries the product's balancedness as the field
   `09:856--858` states it to be -- it does **not** derive field 11 from field
   10.  Discharging `D:620--632` (and with it the reader's
   `lem:paper-product-balancedness`, `02:401--411`, which no module claims) is a
   separate obligation, deliberately left open.

## Reader counterparts

Frozen release, `reader-facing/`, opened first-hand for this round.

* `lem:paper-certified-row-ladder`, `sections/02-preliminaries.tex`
  **lines 244--256** (statement and `eq:paper-certified-row-ladder`) --
  `CertifiedRowLadder`, `certifiedRowLadder_of_base` (the r2 proof of exactly
  this reader statement), `certifiedRowLadder_of_seedInputs`,
  `terminal_stage3_two_copy`, `terminal_stage3_odd_copy`,
  `stage3_two_copy_of_seedInputs`, `stage3_odd_copy_of_seedInputs`,
  `certifiedRowLadder_is_not_free`, `certifiedRowLadder_guard_is_live`.
  Verified first-hand this round: the reader lemma states exactly
  `Lambda_W(2^{ell-1}+1, 2^ell x, z^2) >= H + ell` for `H >= 2`, `0 < x`,
  `0 < z <= 1`, `ell >= 1`, `2^ell x <= 1`, which is what the Lean predicate
  quantifies.  This reader item is claimed by **no other module**.
* `sections/A-stage4-details.tex` **line 391**, "Its small-capacity and
  final-node closures use the certified row ladder
  `Cref{lem:paper-certified-row-ladder}`" -- the sentence that assigns the
  ladder to *this* frozen block rather than to `08`'s; recorded as
  navigation, not claimed as a statement counterpart.
* `lem:paper-product-balancedness`, `sections/02-preliminaries.tex`
  **lines 401--411**, and the reader's balancedness definition at **383--390**:
  the reader-level statements behind the two fields repair r3 adds.  Opened
  first-hand this round and confirmed to state the frozen
  `lem:product-balancedness` (`(q,t,eps_0)`-balanced `S`, `eps_* = max{...}`,
  conclusion `(vq,t,eps_*)`-balanced).  Recorded here as **provenance only and
  explicitly NOT claimed**: this module *assumes* the product clause and proves
  nothing of the sort, so both reader items stay unassigned and available to the
  obligation that discharges `D:620--632`.  No module currently claims either.

Everything else in this block has **no reader counterpart**, and that is a
finding about the reader artifact, not an omission here.  Searched first-hand
across the whole reader artifact: `eq:terminal-entry`'s constants (`q_2 >= 16`,
`lambda_0 <= 1/8`, `delta' >= lambda_0 + 5 eps + 2/q_2`) occur **nowhere**;
`49/128` occurs **nowhere**; `9/25` occurs **nowhere** in the terminal sense;
the Stage-3 selector root `tau_0 = 2 s x_T` occurs **nowhere** (the reader's
`tau_k` at `sections/05-iteration.tex` **lines 318--357** is the unrelated
iteration halting-time sequence, not this ladder); the two frozen budget
displays
`eq:terminal-stage2-budget` and `eq:terminal-stage3-budget` occur **nowhere**.
The reader's own sentence at `396--399` records that the owner--donor count
"is expanded line by line in the ultra-explicit companion", which is exactly
the frozen `09:834--1183` this module traces.  Citing the reader's prose at
`319--322` or `387--390` would be citing prose as a statement, which the
reader-counterpart discipline bars; those two lines were already recorded as
unclaimed prose by `TwoStreamState` and are **not** reclaimed here.  Reader
lines `361--368` remain assigned to `WrapperLowRungs.wrapperLowRungs`, and
`374` / `396--399` remain the unclaimed prose `WrapperProjectionCovers`
recorded.  No reader item is assigned twice.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the frozen entry conditions, general (6): `terminalTarget_sub_one`,
  `terminalTarget_pos`, `terminalEntry_of_stageTwoWidths`,
  `terminalEntry_is_satisfiable`, `eps_lt_fifth`,
  `terminalEntry_forces_scale_guard`.
* `B` the Stage-2 counting phases, general in the density vector (5):
  `bad_count_le`, `wit_count_ge`, `zone_card_ge`, `excess_gt_two`,
  `stage2_zone_excess`.
* `C` the Stage-2 ladder and budgets, general (7):
  `lambdaAt_stage2_frontier`, `lambdaAt_stage2_beyond`,
  `stage2_residual_budget`, `stage2_premature_budget`,
  `stage2_capacity_one_iff`, `stage2_budget`, `post_alice_density_gt`.
* `D` the Stage-3 selector ladder and densities, general (6): `tauAt_zero`,
  `tauAt_succ`, `tauAt_stage3_frontier`, `tauAt_partial_loss_lt`,
  `ordinary_column_density`, `bob_child_density`.
* `E` the certified row ladder, the certified-scale instances, the pinned-scale
  compositions and the closing budget, general (18): `Dfamily_mono_copies_rows`,
  `certifiedRowLadder_of_base`, `LambdaGE_le_Dfamily`,
  `terminal_stage3_two_copy`, `terminal_stage3_odd_copy`, `scale_guard`,
  `row_density_legal`, `row_density_legal_at_capacity`, `two_xT_le_one`,
  `stage3_ladder_at_reached_capacity`, `stage3_ladder_two_copy_at_pins`,
  `certifiedRowLadder_of_seedInputs`, `stage3_two_copy_of_seedInputs`,
  `stage3_odd_copy_of_seedInputs`, `odd_copy_selection`, `stage3_budget`,
  `lambdaZero_le_of_widths`, `half_le_logb_five_thirds`.
* `F` the contradiction skeletons, the Extension row, the frozen width
  conditions and the call-(ii) fixed-width list, general (11):
  `one_bit_above_of_not_shallow`, `stage3_contradiction`,
  `extensionCallTwo_block_count`, `extensionCallTwo_post_query_density`,
  `extensionWidth_pos`, `extensionWidth_four_le`, `extensionCallTwo_of_widths`,
  `le_yLoss_of_pow_le`, `epsProd_lt_fiftieth`,
  `extensionCallTwoFixedWidth_epsProd_bound`, `extensionCallTwo_row_range`.
* `G` the `C_2 x C_2` product family and the vendored balancedness predicate,
  general (9) -- new in repair r3: `productFamilyEquiv_apply`,
  `productFamily_block`, `productFamily_const`, `productFamily_bijective`,
  `familyOnIndices_bijective`, `isBalancedFamily_reindex`,
  `isBalancedFamily_mono`, `card_agree`,
  `isBalancedFamily_zero_of_bijective`.

That is **62 general battery entries proved**, with `0` unproved, alongside
**seven statement poles** (`certifiedRowLadder_is_not_free`,
`terminalTwoStream_is_not_trivial`,
`legacy_extension_binder_is_self_contradictory`,
`repaired_extension_binder_avoids_unit_capacity`,
`repaired_extension_binder_domain_is_inhabited`,
`constant_family_not_balanced`,
`fixedWidth_family_content_is_exactly_the_two_clauses`) and **twenty-four
non-vacuity / consistency readouts** at the two probe width records
`probeWidths` and `extProbeWidths`, at the exact-full-product family
`extProbeFamily`, and at the Stage-3 probe scalars (`probeWidths_dyadic_readout`,
`probeEntry_holds`, `probeLambdaZero`, `probeEntry_is_nondegenerate`,
`bankedProbeWidth_is_not_a_terminal_entry_width`,
`probeExtensionDomain_nonempty`, `probeExtensionCallTwo`,
`probeExtensionCallTwo_block_count`,
`terminalTwoStream_arith_hypotheses_consistent`,
`probePins_are_nondegenerate`, `extProbeEpsProd_range`,
`logb_one_add_epsProd_le_one`, `twoPow_certified_exponent_ge`,
`extProbe_sqrt_k₂`, `extProbe_casts`, `extProbe_gate_one_rhs`,
`extProbeFamily_bijective`, `extProbeFamily_isBalanced`,
`extProbeFamily_prod_isBalanced`, `extProbeEps2_nonneg`,
`extProbe_fixedWidth_holds`, `extProbe_constantFamily_fails`,
`extProbeExtensionDomain_nonempty`,
`terminalTwoStream_r2_hypotheses_consistent`), plus
`certifiedRowLadder_guard_is_live`.

**What "at legal values" does and does not mean for those readouts
(`cc-t7p`, the `extProbeWidths` legality sweep).**  The predecessor wording
"the two LANE-GATE 3 inhabitants" is WITHDRAWN and reads "the two probe width
records" above.  Both records inhabit the *relaxed* Lean carrier
`StageTwoRelaxed.StageTwoWidths` -- whose four proof fields are
`4 t_2 <= q_2` (`07:280`), `k_2 >= m_HS` (`07:281`), `5 <= m_HS` (the first
conjunct of the inherited tail predicate `HSThreshold`, `D:496`) and the
structural depth gate `q_2 2^{-b_1} <= 1/131072` (`07:398--401`), the other
three of the seven `07:278--281` conditions holding as theorems -- at
nondegenerate values, and every readout listed above is exactly that much.
Neither record meets the frozen **schedule** floor for the same exponent:
`eq:t2-search` (`06:763--770`) fixes `k_2` as the least integer
with `k_2 >= max{4, 2^{19}, m_HS}` at `06:766`, `2^{19} = 524288`, and
`extProbeWidths.k₂ = 576` while `probeWidths.k₂ = 5`.  So these are readouts
about **our encoding**, not evidence at the paper's parameter values; the
`extProbeWidths` half of that is stated in full at the record's own definition
and at `extensionGatesFixedWidth_at_extProbe`, and the `probeWidths` half is
registered (not repaired here) as ledger item `(b14)` under
`S5-CUTOFF-ITEMS-DEFERRED`.

## HYPOTHESIS-CONSISTENCY note on the headline statement

`TerminalTwoStream` conjoins the banked `StageTwoRelaxed.StageTwoWidths` record
(hence all seven frozen width conditions), the remaining dyadic convention
`s = 2^{r_3}`, the two checked-identity pins, `eq:terminal-entry`,
`eq:terminal-seed-inputs`, the call-(ii) fixed-width binder
`ExtensionCallTwoFixedWidth` -- now including the two `06:1116--1123`
balancedness clauses about the statement's own `cFam` -- and the `forall`-form
reached-capacity Extension binder.

What is *established* here, and not merely asserted:
`terminalTwoStream_r2_hypotheses_consistent` exhibits the whole **arithmetic**
sub-bundle simultaneously at the **gate-firing** width record `extProbeWidths`
(the `cc-t7p` term; the predecessor "certified-regime width record" is
WITHDRAWN -- see the record's own definition for the `06:766` violation that
puts it outside the paper's schedule regime)
and the Stage-3 probe scalars, at a nondegenerate `eps = 1/100`,
`delta' = 1/10`, **including the fixed-width binder in full -- both balancedness
fields discharged at the exact full product over a two-letter column alphabet --
and the reached-capacity binder in its `forall` form** rather than pointwise
instances of them.  The balancedness fields are not satisfied by vacuity:
`constant_family_not_balanced` and `extProbe_constantFamily_fails` show that at
the *same* numerals the constant family is refuted by them.  (The r1
readout `terminalTwoStream_arith_hypotheses_consistent` is retained at
`probeWidths`; it covers the r1 binder set only, and its widths are outside the
gate-firing regime -- `extensionGatesFixedWidth_fails_at_balance_minimum`
refutes `eq:all-extension-gates` there outright.)
A satisfiable collection cannot yield `False`, so no derivation of `False` from
these binders can go through; the scratch probe that attempts that derivation is
recorded above and does not typecheck.  Supporting this,
`terminalEntry_forces_scale_guard` shows the entry conditions *imply* -- rather
than contradict -- the `H >= 2` guard the certified-scale instances need, and
`probePins_are_nondegenerate` shows the pinned `x_T` is strictly positive, so the
row-density guards are not satisfied by the degenerate `x_T = 0`.

What is *not* established: the two `Lambda` clauses of
`eq:terminal-seed-inputs` are the inherited Stage-1 and Stage-2 certificates
`09:847` and `09:849`, about two different matrices; the frozen text states them
as two separate certificates and they are carried that way, never conjoined as
cases of one construction, but this module does not exhibit a pair of matrices
realizing them.  Nor does it exhibit a `TwoStreamState` record inside the
terminal regime: `bankedProbeWidth_is_not_a_terminal_entry_width` records that
neither banked inhabitant meets `eq:terminal-entry` (both sit at `q_2 = 2`), so
the inhabitation of `def:two-stream-state` is **not** evidence that this lemma's
full bundle is inhabited, and this module does not pretend otherwise.
-/

namespace EthInapproximability.ParameterizedNP.TerminalTwoStream

open Finset
open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.TwoStreamState

/-! ## Section 1  The frozen entry conditions (`09:836--859`)

`eq:terminal-entry` and `eq:terminal-seed-inputs` are transcribed here at the
banked constants; `lambda_0`, `x = 2^{-b_1}`, `D_2` and `tau_0` are consumed by
pin and none of them is redefined. -/

/-- **`eq:terminal-entry` (label `09:843`, display `09:838--844`).**
`q_2 >= 16`, `lambda_0 <= 1/8`, `delta' >= lambda_0 + 5 eps + 2/q_2`, at the
banked `lambda_0 = 2 q_2 2^{-b_1}`.  General in the two widths and the two
reals. -/
def terminalEntry (q₂ b₁ : ℕ) (ε δ' : ℝ) : Prop :=
  16 ≤ q₂
    ∧ DenseBranchSelection.lambdaZero q₂ b₁ ≤ 1 / 8
    ∧ DenseBranchSelection.lambdaZero q₂ b₁ + 5 * ε + 2 / (q₂ : ℝ) ≤ δ'

/-- **`eq:terminal-seed-inputs` (label `09:852`, display `09:846--853`) with
`09:854--855`.**  `Lambda_{M_1^T}(1, 2^{-b_1}, y) >= B_cap`,
`Lambda_{S_2}(1, x_T, y) >= D_2` at `S_2 = M_2^T` and
`D_2 = B_cap + log_2 q_2`, and `log_2 s < b_T`.  The exponents `r_2 = log_2 q_2`
and `r_3 = log_2 s` are the frozen dyadic logarithms, carried as the exponents
themselves so that no `Nat.log` enters where the frozen text writes a width.
General. -/
def terminalSeedInputs {Cone Rone Ltwo Jtwo : Type*} [Fintype Cone] [Fintype Rone]
    [Fintype Ltwo] [Fintype Jtwo] (M1T : Cone → Rone → Bool)
    (S2 : Ltwo → Jtwo → Bool) (b₁ bcap r₂ r₃ bT : ℕ) (xT y : ℝ) : Prop :=
  bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) y
    ∧ DenseBranchSelection.Dtwo bcap r₂ ≤ LambdaGE S2 1 xT y
    ∧ r₃ < bT

/-- **`09:858--859` with `09:1038` and `09:1777`.**  The terminal target
`C = D_2 + log_2 s + 1`, written at the frozen exponents.  `D_2` is the banked
`DenseBranchSelection.Dtwo`; nothing new is defined for it. -/
def terminalTarget (bcap r₂ r₃ : ℕ) : ℕ :=
  DenseBranchSelection.Dtwo bcap r₂ + r₃ + 1

/-- **Aux A1 (`09:1038`).**  `C - 1 = D_2 + log_2 s`, the alleged budget the
Stage-3 contradiction spends.  General. -/
theorem terminalTarget_sub_one (bcap r₂ r₃ : ℕ) :
    terminalTarget bcap r₂ r₃ - 1 = DenseBranchSelection.Dtwo bcap r₂ + r₃ := by
  simp [terminalTarget]

/-- **Aux A2.**  The terminal target is positive, so the frozen conclusion
`comp Z >= C` is not the empty bound `comp Z >= 0`.  General. -/
theorem terminalTarget_pos (bcap r₂ r₃ : ℕ) : 0 < terminalTarget bcap r₂ r₃ := by
  simp [terminalTarget]

/-- **Aux A3 (two clauses of `eq:terminal-entry` are *discharged*, not
assumed).**  At the banked Stage-2 widths of `StageTwoRelaxed.StageTwoWidths`
(`07:278--281`, `07:398--401`) the first two clauses of `eq:terminal-entry`
hold outright: `k_2 >= 5` and `4 t_2 <= q_2` give `q_2 >= 128 >= 16`, and the
depth gate `131072 q_2 <= 2^{b_1}` gives
`lambda_0 = 2 q_2 2^{-b_1} <= 2/131072 <= 1/8`.  So the only genuine hypothesis
of `eq:terminal-entry` is its third clause, which is the one the frontier
supplies.  General in the width record. -/
theorem terminalEntry_of_stageTwoWidths (W : StageTwoRelaxed.StageTwoWidths) :
    16 ≤ W.q₂ ∧ DenseBranchSelection.lambdaZero W.q₂ W.b₁ ≤ 1 / 8 := by
  have hk : 5 ≤ W.k₂ := le_trans W.five_le_mHS W.mHS_le_k₂
  have h32 : (32 : ℕ) ≤ 2 ^ W.k₂ := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ W.k₂ := Nat.pow_le_pow_right (by norm_num) hk
  have hq : 128 ≤ W.q₂ := by
    have := W.four_t₂_le_q₂
    simp only [StageTwoRelaxed.StageTwoWidths.q₂]
    omega
  refine ⟨by omega, ?_⟩
  have hgate : (131072 : ℝ) * (W.q₂ : ℝ) ≤ (2 : ℝ) ^ W.b₁ := by
    have := W.depth_gate
    have h : ((131072 * 2 ^ W.r₂ : ℕ) : ℝ) ≤ ((2 ^ W.b₁ : ℕ) : ℝ) := by exact_mod_cast this
    simpa [StageTwoRelaxed.StageTwoWidths.q₂] using h
  have hpow : (0 : ℝ) < (2 : ℝ) ^ W.b₁ := by positivity
  have hq0 : (0 : ℝ) ≤ (W.q₂ : ℝ) := Nat.cast_nonneg _
  rw [DenseBranchSelection.lambdaZero, div_le_iff₀ hpow]
  nlinarith

/-- **Aux A4 (LANE-GATE 3: the entry bundle is consistent).**  At any width
record, `eps = 0` and `delta' = 1` satisfy all three clauses of
`eq:terminal-entry` -- the third one because `lambda_0 <= 1/8` and
`2/q_2 <= 2/128`.  This is the HYPOTHESIS-CONSISTENCY check: no pair of clauses
of `eq:terminal-entry` is contradictory at the frozen widths, so the lemma is
not quantified over an empty regime.  General in the width record. -/
theorem terminalEntry_is_satisfiable (W : StageTwoRelaxed.StageTwoWidths) :
    terminalEntry W.q₂ W.b₁ 0 1 := by
  obtain ⟨h16, hlam⟩ := terminalEntry_of_stageTwoWidths W
  have hk : 5 ≤ W.k₂ := le_trans W.five_le_mHS W.mHS_le_k₂
  have h32 : (32 : ℕ) ≤ 2 ^ W.k₂ := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ W.k₂ := Nat.pow_le_pow_right (by norm_num) hk
  have hq : 128 ≤ W.q₂ := by
    have := W.four_t₂_le_q₂
    simp only [StageTwoRelaxed.StageTwoWidths.q₂]
    omega
  have hqR : (128 : ℝ) ≤ (W.q₂ : ℝ) := by exact_mod_cast hq
  refine ⟨h16, hlam, ?_⟩
  have hq0 : (0 : ℝ) < (W.q₂ : ℝ) := by linarith
  have : (2 : ℝ) / (W.q₂ : ℝ) ≤ 2 / 128 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hqR
  linarith

/-- **Aux A5 (`09:913--914`).**  "Also `delta' <= 1` and `eq:terminal-entry`
imply `eps < 1/5`."  The frozen deduction uses only positivity of `lambda_0`
and of `2/q_2`.  General. -/
theorem eps_lt_fifth {q₂ b₁ : ℕ} {ε δ' : ℝ} (h : terminalEntry q₂ b₁ ε δ')
    (hδ : δ' ≤ 1) : ε < 1 / 5 := by
  obtain ⟨h16, _, hthird⟩ := h
  have hq : 0 < q₂ := by omega
  have hlam : 0 < DenseBranchSelection.lambdaZero q₂ b₁ :=
    TwoStreamState.lambdaZero_pos b₁ hq
  have hqR : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq
  have hinv : (0 : ℝ) < 2 / (q₂ : ℝ) := by positivity
  linarith

/-! ## Section 2  The Stage-2 counting phases (`09:871--914`)

`eq:terminal-averages`, `eq:terminal-bw` and `eq:terminal-excess`.  These are
pure counting statements about a density vector on `[q_2]`, so they are proved
*general in the vector* and only afterwards read off the banked record. -/

/-- **`09:883--884`.**  `H = {alpha : r_alpha >= lambda_0}`, and with the
foreign fractions substituted, `F = {alpha : f_alpha >= lambda_0}`.  One
definition serves both, exactly as the frozen display uses one threshold. -/
noncomputable def highSet {q₂ : ℕ} (r : Slot q₂ → ℝ) (lam : ℝ) : Finset (Slot q₂) :=
  Finset.univ.filter (fun α => lam ≤ r α)

/-- **`09:885--887`.**  `Z = H cap F`. -/
noncomputable def zoneSet {q₂ : ℕ} (r f : Slot q₂ → ℝ) (lam : ℝ) : Finset (Slot q₂) :=
  highSet r lam ∩ highSet f lam

/-- **`09:886`.**  `b = q_2 - |H|`, written as the cardinality of the
complement so that no natural subtraction enters. -/
noncomputable def badSet {q₂ : ℕ} (r : Slot q₂ → ℝ) (lam : ℝ) : Finset (Slot q₂) :=
  Finset.univ \ highSet r lam

/-- **Aux B1 (`eq:terminal-bw`, the bad half, `09:890--891` and `09:896`).**
"Every coordinate outside `H` contributes more than `1 - lambda_0` to the
baseline deficit.  Hence `b <= eps q_2/(1 - lambda_0)`."  General in the
density vector; only `r_alpha <= 1` and the mean bound are used. -/
theorem bad_count_le {q₂ : ℕ} (r : Slot q₂ → ℝ) {lam ε : ℝ}
    (hr1 : ∀ α, r α ≤ 1) (hlam : lam < 1)
    (hmean : (1 - ε) * (q₂ : ℝ) ≤ ∑ α, r α) :
    ((badSet r lam).card : ℝ) ≤ ε * (q₂ : ℝ) / (1 - lam) := by
  classical
  have hlam0 : (0 : ℝ) < 1 - lam := by linarith
  have hsum_all : ∑ α : Slot q₂, (1 - r α) = (q₂ : ℝ) - ∑ α : Slot q₂, r α := by
    rw [Finset.sum_sub_distrib]
    simp
  have hsub : (badSet r lam) ⊆ (Finset.univ : Finset (Slot q₂)) := Finset.subset_univ _
  have hnonneg : ∀ α ∈ (Finset.univ : Finset (Slot q₂)), α ∉ badSet r lam → 0 ≤ 1 - r α := by
    intro α _ _
    linarith [hr1 α]
  have hlow : ∀ α ∈ badSet r lam, 1 - lam ≤ 1 - r α := by
    intro α hα
    have hlt : r α < lam := by simpa [badSet, highSet] using hα
    linarith
  have hstep : ((badSet r lam).card : ℝ) * (1 - lam) ≤ ∑ α ∈ badSet r lam, (1 - r α) := by
    calc ((badSet r lam).card : ℝ) * (1 - lam)
        = ∑ _α ∈ badSet r lam, (1 - lam) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ α ∈ badSet r lam, (1 - r α) := Finset.sum_le_sum hlow
  have hbig : ∑ α ∈ badSet r lam, (1 - r α) ≤ ∑ α : Slot q₂, (1 - r α) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hfin : ((badSet r lam).card : ℝ) * (1 - lam) ≤ ε * (q₂ : ℝ) := by
    have := hstep.trans (hbig.trans (le_of_eq hsum_all))
    linarith
  rw [le_div_iff₀ hlam0]
  exact hfin

/-- **Aux B2 (`eq:terminal-bw`, the witness half, `09:891--894` and `09:898`).**
"The average foreign mass is maximised, for a fixed `w`, by placing density one
on `F` and density `lambda_0` elsewhere.  Hence
`w >= q_2(delta' - lambda_0)/(1 - lambda_0)`."  General in the density
vector. -/
theorem wit_count_ge {q₂ : ℕ} (f : Slot q₂ → ℝ) {lam δ : ℝ}
    (hf1 : ∀ α, f α ≤ 1) (hlam : lam < 1)
    (hmean : δ * (q₂ : ℝ) ≤ ∑ α, f α) :
    (q₂ : ℝ) * (δ - lam) / (1 - lam) ≤ ((highSet f lam).card : ℝ) := by
  classical
  have hlam0 : (0 : ℝ) < 1 - lam := by linarith
  set F : Finset (Slot q₂) := highSet f lam with hF
  have hsub : F ⊆ (Finset.univ : Finset (Slot q₂)) := Finset.subset_univ _
  have hsplit : ∑ α ∈ (Finset.univ : Finset (Slot q₂)) \ F, f α + ∑ α ∈ F, f α
      = ∑ α : Slot q₂, f α := Finset.sum_sdiff hsub
  have hin : ∑ α ∈ F, f α ≤ (F.card : ℝ) := by
    calc ∑ α ∈ F, f α ≤ ∑ _α ∈ F, (1 : ℝ) := Finset.sum_le_sum (fun α _ => hf1 α)
      _ = (F.card : ℝ) := by simp
  have hout : ∑ α ∈ (Finset.univ : Finset (Slot q₂)) \ F, f α
      ≤ (((Finset.univ : Finset (Slot q₂)) \ F).card : ℝ) * lam := by
    calc ∑ α ∈ (Finset.univ : Finset (Slot q₂)) \ F, f α
        ≤ ∑ _α ∈ (Finset.univ : Finset (Slot q₂)) \ F, lam := by
          refine Finset.sum_le_sum ?_
          intro α hα
          have hlt : f α < lam := by simpa [hF, highSet] using hα
          exact hlt.le
      _ = (((Finset.univ : Finset (Slot q₂)) \ F).card : ℝ) * lam := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcards : ((Finset.univ : Finset (Slot q₂)) \ F).card + F.card = q₂ := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    simpa [Finset.card_univ] using h
  have hcardR : (((Finset.univ : Finset (Slot q₂)) \ F).card : ℝ) = (q₂ : ℝ) - (F.card : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcards
    push_cast at h
    linarith
  have hkey : δ * (q₂ : ℝ) ≤ (F.card : ℝ) + ((q₂ : ℝ) - (F.card : ℝ)) * lam := by
    rw [← hcardR]
    linarith [hmean, hsplit, hin, hout]
  rw [div_le_iff₀ hlam0]
  nlinarith [hkey]

/-- **Aux B3 (`09:901`).**  "Since `|Z| >= w - b`".  Pure counting: `F` is
covered by `H cap F` together with the complement of `H`.  General. -/
theorem zone_card_ge {q₂ : ℕ} (r f : Slot q₂ → ℝ) (lam : ℝ) :
    ((highSet f lam).card : ℝ) - ((badSet r lam).card : ℝ)
      ≤ ((zoneSet r f lam).card : ℝ) := by
  classical
  have hcov : highSet f lam ⊆ zoneSet r f lam ∪ badSet r lam := by
    intro α hα
    by_cases hH : α ∈ highSet r lam
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hH, hα⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hH⟩)
  have h1 : (highSet f lam).card ≤ (zoneSet r f lam).card + (badSet r lam).card := by
    calc (highSet f lam).card ≤ (zoneSet r f lam ∪ badSet r lam).card :=
          Finset.card_le_card hcov
      _ ≤ (zoneSet r f lam).card + (badSet r lam).card := Finset.card_union_le _ _
  have := (Nat.cast_le (α := ℝ)).mpr h1
  push_cast at this
  linarith

/-- **Aux B4 (`eq:terminal-excess`, `09:902--912`).**  The frozen chain
`|Z| - 4b >= w - 5b >= (q_2(delta' - lambda_0) - 5 eps q_2)/(1 - lambda_0)
>= 2/(1 - lambda_0) > 2`, as real arithmetic on the two counts.  General in
`w, b, z`. -/
theorem excess_gt_two {q₂ : ℕ} {lam ε δ w b z : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 8) (hq : 0 < (q₂ : ℝ))
    (hentry : lam + 5 * ε + 2 / (q₂ : ℝ) ≤ δ)
    (hw : (q₂ : ℝ) * (δ - lam) / (1 - lam) ≤ w)
    (hb : b ≤ ε * (q₂ : ℝ) / (1 - lam)) (_hb0 : 0 ≤ b)
    (hz : w - b ≤ z) :
    2 / (1 - lam) ≤ w - 5 * b ∧ 2 < z - 4 * b := by
  have hlam1 : (0 : ℝ) < 1 - lam := by linarith
  have h1 : 5 * ε + 2 / (q₂ : ℝ) ≤ δ - lam := by linarith
  have h2 : (q₂ : ℝ) * (5 * ε + 2 / (q₂ : ℝ)) ≤ (q₂ : ℝ) * (δ - lam) :=
    mul_le_mul_of_nonneg_left h1 hq.le
  have h3 : (q₂ : ℝ) * (5 * ε + 2 / (q₂ : ℝ)) = 5 * ε * (q₂ : ℝ) + 2 := by
    field_simp
  have hnum : (2 : ℝ) ≤ (q₂ : ℝ) * (δ - lam) - 5 * (ε * (q₂ : ℝ)) := by
    rw [h3] at h2; linarith
  have hdiv : (2 : ℝ) / (1 - lam)
      ≤ ((q₂ : ℝ) * (δ - lam) - 5 * (ε * (q₂ : ℝ))) / (1 - lam) := by
    gcongr
  have hexp : ((q₂ : ℝ) * (δ - lam) - 5 * (ε * (q₂ : ℝ))) / (1 - lam)
      = (q₂ : ℝ) * (δ - lam) / (1 - lam) - 5 * (ε * (q₂ : ℝ) / (1 - lam)) := by
    field_simp
  have hstep : (2 : ℝ) / (1 - lam) ≤ w - 5 * b := by
    rw [hexp] at hdiv
    have : 5 * (ε * (q₂ : ℝ) / (1 - lam)) ≥ 5 * b := by linarith
    linarith
  refine ⟨hstep, ?_⟩
  have htwo : (2 : ℝ) < 2 / (1 - lam) := by
    rw [lt_div_iff₀ hlam1]
    linarith
  linarith

/-- **Aux B5 (`eq:terminal-averages` .. `eq:terminal-excess`, at the banked
record).**  The composed Stage-2 phase: from a `TwoStreamState` and
`eq:terminal-entry`, the frozen excess `|Z| - 4b > 2` holds at the two banked
fibre-density vectors and the banked threshold `lambda_0`.  This is the point
at which the general counting above bites on the frozen construction.
General in the state. -/
theorem stage2_zone_excess {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw]
    [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone]
    [Fintype Ltwo] [DecidableEq Ltwo]
    {q s q₂ mT dT b₁ : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
    {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
    {RG RSig RD : Finset Rw} {omg : Rw → Om} {rho : Slot s → Om → Slot q₂ × Cone}
    {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
    {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)} {lamT eps2 xT ε δ' : ℝ}
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hentry : terminalEntry q₂ b₁ ε δ') :
    2 < ((zoneSet
            (fibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG))
            (fibreDensity (streamImage omg rho st.pFor XZ st.iFor st.Rfor))
            (DenseBranchSelection.lambdaZero q₂ b₁)).card : ℝ)
        - 4 * ((badSet
            (fibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG))
            (DenseBranchSelection.lambdaZero q₂ b₁)).card : ℝ) := by
  classical
  obtain ⟨h16, hlam18, hthird⟩ := hentry
  set lam := DenseBranchSelection.lambdaZero q₂ b₁ with hlamdef
  set rOrd := fibreDensity (streamImage omg rho st.pOrd XZ st.iOrd RG) with hrdef
  set fFor := fibreDensity (streamImage omg rho st.pFor XZ st.iFor st.Rfor) with hfdef
  have hq : 0 < q₂ := by omega
  have hqR : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq
  have hlam0 : 0 < lam := TwoStreamState.lambdaZero_pos b₁ hq
  have hlam1 : lam < 1 := by linarith
  -- the two averages of `eq:terminal-averages`, cleared of the `1/q_2`
  have hmeanOrd : (1 - ε) * (q₂ : ℝ) ≤ ∑ α, rOrd α := by
    have h := st.ordinary_density
    rw [meanFibreDensity] at h
    have := mul_le_mul_of_nonneg_right h (le_of_lt hqR)
    calc (1 - ε) * (q₂ : ℝ) ≤ (1 / (q₂ : ℝ) * ∑ α, rOrd α) * (q₂ : ℝ) := this
      _ = ∑ α, rOrd α := by field_simp
  have hmeanFor : δ' * (q₂ : ℝ) ≤ ∑ α, fFor α := by
    have h := st.foreign_density
    rw [meanFibreDensity] at h
    have := mul_le_mul_of_nonneg_right h (le_of_lt hqR)
    calc δ' * (q₂ : ℝ) ≤ (1 / (q₂ : ℝ) * ∑ α, fFor α) * (q₂ : ℝ) := this
      _ = ∑ α, fFor α := by field_simp
  have hr1 : ∀ α, rOrd α ≤ 1 := fun α => (fibreDensity_mem_Icc _ α).2
  have hf1 : ∀ α, fFor α ≤ 1 := fun α => (fibreDensity_mem_Icc _ α).2
  have hb := bad_count_le rOrd hr1 hlam1 hmeanOrd
  have hw := wit_count_ge fFor hf1 hlam1 hmeanFor
  have hz := zone_card_ge rOrd fFor lam
  have hb0 : (0 : ℝ) ≤ ((badSet rOrd lam).card : ℝ) := Nat.cast_nonneg _
  exact (excess_gt_two hlam0 hlam18 hqR hthird hw hb hb0 (by linarith)).2

/-! ## Section 3  The Stage-2 support ladder and budgets (`09:928--1033`)

`lambda_d = lambda_0 2^{-d}` is the banked `DenseRoutingThresholds.lambdaAt`
(`08:812--816`), consumed by pin; the two evaluations below are what `09:941`
and `09:970` add, and the budget identities are `09:960--962`, `09:974--976`
and `eq:terminal-stage2-budget`. -/

/-- **Aux C1 (`09:937--942`).**  "Put `r_2 = log_2 q_2` ... at every depth
`d <= r_2` before such a stop, `lambda_d >= lambda_{r_2} = 2^{1-b_1}`."  The
evaluation of the banked ladder at the Stage-2 frontier, at the frozen dyadic
width `q_2 = 2^{r_2}`.  General in both exponents. -/
theorem lambdaAt_stage2_frontier (r₂ b₁ : ℕ) :
    DenseRoutingThresholds.lambdaAt (2 ^ r₂) b₁ r₂ = 2 / 2 ^ b₁ := by
  rw [DenseRoutingThresholds.lambdaAt, DenseBranchSelection.lambdaZero]
  have h : ((2 ^ r₂ : ℕ) : ℝ) = (2 : ℝ) ^ r₂ := by push_cast; ring
  rw [h]
  have hne : ((2 : ℝ) ^ r₂) ≠ 0 := by positivity
  field_simp

/-- **Aux C2 (`09:967--971`).**  "Nor can a token first reach depth `r_2 + 1`.
Its support would still have density at least `lambda_{r_2+1} = 2^{-b_1}`."
General in both exponents. -/
theorem lambdaAt_stage2_beyond (r₂ b₁ : ℕ) :
    DenseRoutingThresholds.lambdaAt (2 ^ r₂) b₁ (r₂ + 1) = 1 / 2 ^ b₁ := by
  rw [DenseRoutingThresholds.lambdaAt_succ, lambdaAt_stage2_frontier]
  ring

/-- **Aux C3 (`09:959--963`).**  "`P_2` has at most `D_2 - r_2 = B_cap` bits
remaining", the residual budget at the Stage-2 frontier.  General. -/
theorem stage2_residual_budget (bcap r₂ : ℕ) :
    DenseBranchSelection.Dtwo bcap r₂ - r₂ = bcap := by
  simp [DenseBranchSelection.Dtwo]

/-- **Aux C4 (`09:973--976`).**  "the alleged protocol `P_2` would leave at most
`D_2 - (r_2 + 1) = B_cap - 1` further bits."  General. -/
theorem stage2_premature_budget (bcap r₂ : ℕ) :
    DenseBranchSelection.Dtwo bcap r₂ - (r₂ + 1) = bcap - 1 := by
  simp [DenseBranchSelection.Dtwo]
  omega

/-- **Aux C5 (`09:956--958`).**  "An unsplit attached pair ... can occur only
when `kappa_v >= 2`: if `kappa_v = 1`, then `d_v = r_2`."  The banked
`stoppingCapacity` at the Stage-2 exponent; the frozen equivalence needs the
frozen `d_v <= r_2`.  General. -/
theorem stage2_capacity_one_iff {r₂ d : ℕ} (hd : d ≤ r₂) :
    DenseWeightedCount.stoppingCapacity r₂ d = 1 ↔ d = r₂ := by
  constructor
  · intro h
    rw [DenseWeightedCount.stoppingCapacity_eq] at h
    have : r₂ - d = 0 := by
      by_contra hne
      have : 2 ^ (r₂ - d) ≥ 2 := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r₂ - d) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  · intro h
    subst h
    simp [DenseWeightedCount.stoppingCapacity]

/-- **Aux C6 (`eq:terminal-stage2-budget`, `09:998--1002`).**  "After taking the
Alice child, the alleged protocol has at most `D_2 - d_v - 1 =
B_cap + log_2 kappa_v - 1` bits left", at `kappa_v = 2^{r_2-d_v}`, i.e.
`log_2 kappa_v = r_2 - d_v`.  General. -/
theorem stage2_budget (bcap r₂ d : ℕ) (hd : d ≤ r₂) :
    DenseBranchSelection.Dtwo bcap r₂ - d - 1 = bcap + (r₂ - d) - 1 := by
  simp only [DenseBranchSelection.Dtwo]
  omega

/-- **Aux C7 (`09:1009--1012`).**  "Following the denser Alice child leaves
typed density at least `49/128 > 9/25`", the frozen strict comparison the
Extension call's column-density guard consumes. -/
theorem post_alice_density_gt : (9 : ℝ) / 25 < 49 / 128 := by norm_num

/-! ## Section 4  The Stage-3 selector ladder (`09:1049--1132`) -/

/-- **`09:1049--1053`.**  `tau_d = 2 s x_T 2^{-d}`, the Alice row-support
ladder of the Stage-3 lift.  Its root is the banked
`WrapperProjectionCovers.tauZero = 2 s x_T`, consumed by pin so that this
sequence and `def:two-stream-state` clause (iv) speak about one object. -/
noncomputable def tauAt (s : ℕ) (xT : ℝ) (d : ℕ) : ℝ :=
  WrapperProjectionCovers.tauZero s xT / 2 ^ d

/-- **Aux D1 (the root value).**  `tau_0` is the banked selector loss. -/
theorem tauAt_zero (s : ℕ) (xT : ℝ) :
    tauAt s xT 0 = WrapperProjectionCovers.tauZero s xT := by
  simp [tauAt]

/-- **Aux D2 (the halving step).**  `tau_{d+1} = tau_d/2`, the frozen
recurrence at `09:1052`.  General. -/
theorem tauAt_succ (s : ℕ) (xT : ℝ) (d : ℕ) : tauAt s xT (d + 1) = tauAt s xT d / 2 := by
  simp [tauAt, pow_succ, div_div]

/-- **Aux D3 (`09:1089--1092`).**  "For `d <= r_3`, its row support is at least
`tau_d >= tau_{r_3} = 2 x_T`", at the frozen dyadic width `s = 2^{r_3}`.
General. -/
theorem tauAt_stage3_frontier (r₃ : ℕ) (xT : ℝ) : tauAt (2 ^ r₃) xT r₃ = 2 * xT := by
  rw [tauAt, WrapperProjectionCovers.tauZero]
  have h : ((2 ^ r₃ : ℕ) : ℝ) = (2 : ℝ) ^ r₃ := by push_cast; ring
  rw [h]
  have hne : ((2 : ℝ) ^ r₃) ≠ 0 := by positivity
  field_simp

/-- **Aux D4 (`09:1068--1073`).**  "an attached object that remains unsplit
loses strictly less than `sum_{d >= 0} tau_{d+1} = tau_0` of its typed physical
support."  Landed as the frozen *strict* statement over every finite prefix,
which is the content the routing consumes: the exact partial sum is
`tau_0 (1 - 2^{-n})`.  General. -/
theorem tauAt_partial_loss_lt {s : ℕ} {xT : ℝ}
    (hpos : 0 < WrapperProjectionCovers.tauZero s xT) (n : ℕ) :
    ∑ d ∈ Finset.range n, tauAt s xT (d + 1)
      = WrapperProjectionCovers.tauZero s xT * (1 - 1 / 2 ^ n)
    ∧ ∑ d ∈ Finset.range n, tauAt s xT (d + 1)
      < WrapperProjectionCovers.tauZero s xT := by
  have hsum : ∑ d ∈ Finset.range n, tauAt s xT (d + 1)
      = WrapperProjectionCovers.tauZero s xT * (1 - 1 / 2 ^ n) := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, tauAt]
      have hne : ((2 : ℝ) ^ k) ≠ 0 := by positivity
      field_simp
      ring
  refine ⟨hsum, ?_⟩
  rw [hsum]
  have hlt : (0 : ℝ) < 1 / 2 ^ n := by positivity
  nlinarith

/-- **Aux D5 (`09:1086--1089`).**  "Since `delta' <= 1` and `eq:terminal-entry`
imply `eps < 1/5`, specified-coordinate projection gives every ordinary object
column density at least `1 - eps > 4/5 > 3/5`."  General. -/
theorem ordinary_column_density {ε : ℝ} (h : ε < 1 / 5) :
    (4 : ℝ) / 5 < 1 - ε ∧ (3 : ℝ) / 5 < 4 / 5 := ⟨by linarith, by norm_num⟩

/-- **Aux D6 (`eq:terminal-bob-child-density`, `09:1129--1132`).**  "After
projection to any selected collection of ordinary bins, this child has column
density at least `(1 - eps)/2 > 2/5 > 9/25`."  General. -/
theorem bob_child_density {ε : ℝ} (h : ε < 1 / 5) :
    (2 : ℝ) / 5 < (1 - ε) / 2 ∧ (9 : ℝ) / 25 < 2 / 5 := ⟨by linarith, by norm_num⟩

/-! ## Section 5  The certified-scale instances (`09:1135--1150`)

`lem:certified-row-ladder` (`A:148--162`) has **no Lean declaration**.  It is
carried below as the explicit named hypothesis `CertifiedRowLadder`, never as
an axiom; `certifiedRowLadder_is_not_free` records that the hypothesis has
content. -/

/-- **`lem:certified-row-ladder` (`A:148--162`), reader
`lem:paper-certified-row-ladder` (`02:244--256`), as an explicit named
hypothesis.**  "Let `M` be a Boolean matrix with nonempty row and column
carriers, let `H >= 2`, and let `0 < x`, `0 < z <= 1`.  Assume
`Lambda_M(1, x, z) >= H`.  For every `ell >= 1` with `2^ell x <= 1`,
`Lambda_M(2^{ell-1}+1, 2^ell x, z^2) >= H + ell`."  The frozen antecedents
`H >= 2`, `Lambda_M(1,x,z) >= H` and the carrier nonemptiness are *not* folded
in: they are separate binders at every use site, so the predicate below is
exactly the frozen conclusion schema and nothing stronger. -/
def CertifiedRowLadder {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) (H : ℕ) (x z : ℝ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → (2 : ℝ) ^ ℓ * x ≤ 1 →
    H + ℓ ≤ LambdaGE M (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ℓ * x) (z ^ 2)

/-- **Aux E0a (`eq:contract-monotonicity`, `D:157--172`, in the typed
readout).**  Bracket complexity is monotone in the copy count and in the
retained row density simultaneously.  The vendored contract
(`InheritedContracts.bracketMonotonicity`) is stated for the flattened
`DSet (bracket M p x z)` readout; the engine-transfer equality
`NPCC.Dfamily_eq_DSet` (`vendor/npc-cc/NPCC/Twin.lean:927`) moves it to the
typed `Dfamily`/`bracketGE` readout that `LambdaGE` is built from.  Nothing new
is assumed: the presentation matrix is the tautological one on
`Fin |X| x Fin |Y|`, so the two checked interfaces are *composed*, not
extended.

This is the step `A:181--185` performs -- "Since `p+1 <= 2p`, bracket
monotonicity `eq:contract-monotonicity`, first in copy count and then in row
density" -- and it is the only ingredient of `lem:certified-row-ladder` that
was missing from the typed layer.  General in the matrix, both copy counts,
both row densities and the column density. -/
theorem Dfamily_mono_copies_rows {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {p' p : ℕ} {x' x z : ℝ}
    (hp' : 1 ≤ p') (hpp : p' ≤ p) (hx'0 : 0 < x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hz0 : 0 < z) (hz1 : z ≤ 1) (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f p') (bracketGE X Y p' x' z)
      ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x z) := by
  classical
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with heX
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm with heY
  set M : Workspace.Types.BoolMat.BoolMat :=
    ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩ with hM
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  rw [Dfamily_eq_DSet f M eX eY he hx'0 (le_trans hx'x hx1) hz0 hz1 hX,
    Dfamily_eq_DSet f M eX eY he (lt_of_lt_of_le hx'0 hx'x) hx1 hz0 hz1 hX]
  exact InheritedContracts.bracketMonotonicity M p' p x' x z z hp' hpp hx'0 hx'x
    hx1 hz0 le_rfl hz1

/-- **`lem:certified-row-ladder` (`A:148--162`), PROVED.**

"Let `M` be a Boolean matrix with nonempty row and column carriers, let
`H in N` satisfy `H >= 2`, and let `0 < x`, `0 < z <= 1`.  Assume
`Lambda_M(1, x, z) >= H`.  For every `ell in N` satisfying `ell >= 1` and
`2^ell x <= 1`, `Lambda_M(2^{ell-1}+1, 2^ell x, z^2) >= H + ell`."

**Repair r2 (F-3).**  The predecessor generation carried this lemma as the
*unwitnessed* hypothesis `CertifiedRowLadder`, and the four Stage-3
consequences below were conditionals on it.  Since the predicate's legality
guard `2^ell x <= 1` is empty at any `x > 1/2`, the hypothesis was satisfiable
by vacuity and the four consequences established nothing (LANE-GATE 3).  This
declaration removes the defect at its root: the frozen lemma is *derived*, from
its own frozen antecedents, using exactly the two inherited contracts its
frozen proof cites.

The proof is the frozen one, `A:163--199`, step for step:

* **Base `ell = 1` (`A:164--171`).**  "the hypothesis on `Lambda` is exactly
  the three input rungs of the inherited two-copy ladder at levels
  `H, H-1, H-2`.  The guard `1 < H` follows from `H >= 2`, and `2x <= 1`
  supplies its row-density guard.  Its three conclusions are precisely
  `Lambda_M(2, 2x, z^2) >= H+1`."  That is the banked
  `TwoCopyLadder.lambdaTwoCopy` at `C_W = H + 1`, whose guard `3 <= C_W` is
  `H >= 2` and whose input `C_W - 1 <= Lambda_M(1, x, z)` is the frozen
  `eq:certified-base` hypothesis.
* **Step (`A:173--198`).**  With `p = 2^{ell-1}` and `x_ell = 2^ell x`, the
  bottom rung of the induction hypothesis gives
  `comp<M, p+1, x_ell, z^2/4> >= H + ell - 2 >= 1`; bracket monotonicity
  (`Dfamily_mono_copies_rows`) raises it to
  `comp<M, 2p, 2 x_ell, z^2/4> >= 1`, which is exactly the seed guard of the
  row-step contract; and `ThreeCopyRowStep.rowStep` at `sigma = 1` yields
  `Lambda_M(2p+1, 2 x_ell, z^2) >= 1 + Lambda_M(p+1, x_ell, z^2) >= H+ell+1`.
  The identities `2p+1 = 2^ell+1` and `2 x_ell = 2^{ell+1} x` close it.

The two carrier-nonemptiness hypotheses are the frozen `A:150` ones ("nonempty
row and column carriers"); `1 <= |X|` is the guard of the engine-transfer
equality inside bracket monotonicity, and `1 <= |Y|` is carried because the
frozen statement carries it.  No axiom is introduced: both ingredients are
project-axiom-free vendored declarations reached through `LegacyNPCC.Core`.
General in the matrix, the scale, and both densities. -/
theorem certifiedRowLadder_of_base {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) {H : ℕ} {x z : ℝ}
    (hX : 1 ≤ Fintype.card X) (_hY : 1 ≤ Fintype.card Y)
    (hH : 2 ≤ H) (hx0 : 0 < x) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (hbase : H ≤ LambdaGE M 1 x z) :
    CertifiedRowLadder M H x z := by
  have hz2pos : (0 : ℝ) < z ^ 2 := by positivity
  have hz2one : z ^ 2 ≤ 1 := by nlinarith
  -- the frozen induction, indexed so that `ell = n + 1`
  have key : ∀ n : ℕ, (2 : ℝ) ^ (n + 1) * x ≤ 1 →
      H + (n + 1) ≤ LambdaGE M (2 ^ n + 1) ((2 : ℝ) ^ (n + 1) * x) (z ^ 2) := by
    intro n
    induction n with
    | zero =>
        intro hlegal
        have h2x : 2 * x ≤ 1 := by simpa using hlegal
        have hstep :=
          TwoCopyLadder.lambdaTwoCopy M (H + 1) (by omega) hx0 h2x hz0 hz1
            (by simpa using hbase)
        simpa using hstep
    | succ n ih =>
        intro hlegal
        -- `2^{n+1} x <= 2^{n+2} x`, so the induction hypothesis is available
        have hmono : (2 : ℝ) ^ (n + 1) * x ≤ (2 : ℝ) ^ (n + 1 + 1) * x := by
          have : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1 + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith
        have hih := ih (le_trans hmono hlegal)
        set p : ℕ := 2 ^ n with hp
        set xl : ℝ := (2 : ℝ) ^ (n + 1) * x with hxl
        have hppos : 1 ≤ p := Nat.one_le_two_pow
        have hxl0 : 0 < xl := by
          rw [hxl]; positivity
        have htwoxl : 2 * xl = (2 : ℝ) ^ (n + 1 + 1) * x := by
          rw [hxl]; ring
        have hxlhalf : xl ≤ 1 / 2 := by
          have : 2 * xl ≤ 1 := by rw [htwoxl]; exact hlegal
          linarith
        -- bottom rung of the induction hypothesis (`A:179--182`)
        have hbot : H + (n + 1) ≤
            2 + Dfamily (interlaceFun M (p + 1))
              (bracketGE X Y (p + 1) xl (z ^ 2 / 4)) :=
          le_trans hih (TwoCopyLadder.LambdaGE_le_rungs M (p + 1) xl (z ^ 2)).2.2
        have hone : 1 ≤ Dfamily (interlaceFun M (p + 1))
            (bracketGE X Y (p + 1) xl (z ^ 2 / 4)) := by omega
        -- monotonicity in copy count and row density (`A:183--187`)
        have hseed : 1 ≤ Dfamily (interlaceFun M (2 * p))
            (bracketGE X Y (2 * p) (2 * xl) (z ^ 2 / 4)) := by
          refine le_trans hone ?_
          refine Dfamily_mono_copies_rows M (by omega) (by omega) hxl0
            (by linarith) (by rw [htwoxl]; exact hlegal) (by positivity)
            (by linarith) hX
        -- the row-step contract at `sigma = 1` (`A:188--193`)
        have hrow := ThreeCopyRowStep.rowStep M p 1 hppos le_rfl hxl0 hxlhalf
          hz2pos hz2one hseed
        have hcopy : 2 * p + 1 = 2 ^ (n + 1) + 1 := by
          rw [hp]; ring
        rw [hcopy, htwoxl] at hrow
        omega
  intro ℓ hℓ hlegal
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  simpa using key n hlegal

/-- **Aux E1 (`Lambda` bounds `comp`).**  The frozen displays
`eq:terminal-stage3-two-copy` and `eq:terminal-stage3-odd-copy` are stated with
`comp{bracket{...}}`, while `lem:certified-row-ladder` concludes about
`Lambda`; the vendored `Lambda` is the minimum of three rungs whose first is
that `comp`, so the transfer is `min_le_left` and nothing is assumed.
General. -/
theorem LambdaGE_le_Dfamily {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) (p : ℕ) (x y : ℝ) :
    LambdaGE M p x y ≤ Dfamily (interlaceFun M p) (bracketGE X Y p x y) := by
  unfold LambdaGE
  exact min_le_left _ _

/-- **Aux E2 (`eq:terminal-stage3-two-copy`, `09:1141--1142`).**  "Its `ell = 1`
instance gives `comp{bracket{S_2}{2}{2 x_T}{9/25}} >= D_2 + 1`", at
`M = S_2`, `H = D_2`, `x = x_T`, `z = 3/5`.  General in the selector matrix and
in both exponents. -/
theorem terminal_stage3_two_copy {Ltwo Jtwo : Type*} [Fintype Ltwo] [Fintype Jtwo]
    (S2 : Ltwo → Jtwo → Bool) {bcap r₂ : ℕ} {xT : ℝ}
    (hlad : CertifiedRowLadder S2 (DenseBranchSelection.Dtwo bcap r₂) xT (3 / 5))
    (hx : 2 * xT ≤ 1) :
    DenseBranchSelection.Dtwo bcap r₂ + 1
      ≤ Dfamily (interlaceFun S2 2) (bracketGE Ltwo Jtwo 2 (2 * xT) (9 / 25)) := by
  have hlegal : (2 : ℝ) ^ (1 : ℕ) * xT ≤ 1 := by simpa using hx
  have h := hlad 1 le_rfl hlegal
  have hcopy : (2 : ℕ) ^ (1 - 1) + 1 = 2 := by norm_num
  have hrow : (2 : ℝ) ^ (1 : ℕ) * xT = 2 * xT := by norm_num
  have hcol : ((3 : ℝ) / 5) ^ 2 = 9 / 25 := by norm_num
  rw [hcopy, hrow, hcol] at h
  exact le_trans h (LambdaGE_le_Dfamily S2 2 (2 * xT) (9 / 25))

/-- **Aux E3 (`eq:terminal-stage3-odd-copy`, `09:1143--1146`).**  "its instance
`ell = log_2 kappa` for every dyadic `kappa >= 4` gives
`comp{bracket{S_2}{kappa/2 + 1}{kappa x_T}{9/25}} >= D_2 + log_2 kappa`", at
`kappa = 2^ell` and `ell >= 2`.  The copy count is written as the frozen
`kappa/2 + 1`; `2^ell/2 = 2^{ell-1}` on the nose.  General. -/
theorem terminal_stage3_odd_copy {Ltwo Jtwo : Type*} [Fintype Ltwo] [Fintype Jtwo]
    (S2 : Ltwo → Jtwo → Bool) {bcap r₂ ℓ : ℕ} {xT : ℝ} (hℓ : 2 ≤ ℓ)
    (hlad : CertifiedRowLadder S2 (DenseBranchSelection.Dtwo bcap r₂) xT (3 / 5))
    (hx : (2 : ℝ) ^ ℓ * xT ≤ 1) :
    DenseBranchSelection.Dtwo bcap r₂ + ℓ
      ≤ Dfamily (interlaceFun S2 (2 ^ ℓ / 2 + 1))
          (bracketGE Ltwo Jtwo (2 ^ ℓ / 2 + 1) ((2 : ℝ) ^ ℓ * xT) (9 / 25)) := by
  have h := hlad ℓ (by omega) hx
  have hcopy : (2 : ℕ) ^ (ℓ - 1) + 1 = 2 ^ ℓ / 2 + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    simp [pow_succ]
  have hcol : ((3 : ℝ) / 5) ^ 2 = 9 / 25 := by norm_num
  rw [hcopy, hcol] at h
  exact le_trans h (LambdaGE_le_Dfamily S2 (2 ^ ℓ / 2 + 1) ((2 : ℝ) ^ ℓ * xT) (9 / 25))

/-- **Aux E4 (`09:1148--1149`).**  "The scale guard `H >= 2` holds because
`D_2 = B_cap + log_2 q_2` and `q_2 >= 16`."  General. -/
theorem scale_guard (bcap r₂ : ℕ) (h : 16 ≤ 2 ^ r₂) :
    2 ≤ DenseBranchSelection.Dtwo bcap r₂ := by
  have hr : 2 ≤ r₂ := by
    by_contra hcon
    have hlt : r₂ < 2 := Nat.lt_of_not_le hcon
    have : (2 : ℕ) ^ r₂ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  simp only [DenseBranchSelection.Dtwo]
  omega

/-- **Aux E5 (`09:1149--1150`).**  "Their requested row densities are legal
because `kappa <= s < 2^{b_T}`", at the banked `x_T = 2^{-b_T}`.  General. -/
theorem row_density_legal {κ s bT : ℕ} (hκs : κ ≤ s) (hs : s < 2 ^ bT) :
    (κ : ℝ) * DenseStageFourOpening.xTdepth bT ≤ 1 := by
  have hκ : (κ : ℝ) ≤ (2 : ℝ) ^ bT := by
    have h : κ ≤ 2 ^ bT := le_trans hκs (le_of_lt hs)
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    exact this
  have hpow : (0 : ℝ) < (2 : ℝ) ^ bT := by positivity
  rw [DenseStageFourOpening.xTdepth]
  rw [mul_one_div, div_le_one hpow]
  exact hκ

/-- **Aux E5b (`09:1149--1150`, re-sited at the headline's pinned `x_T`).**
The frozen legality `kappa <= s < 2^{b_T}` at the frozen dyadic `s = 2^{r_3}`
and the reached capacity `kappa = stoppingCapacity r_3 d = 2^{r_3-d}`, phrased
in the shape `lem:certified-row-ladder` actually consumes, namely
`2^ell x_T <= 1` at `ell = log_2 kappa = r_3 - d`.

**Repair note (r1).**  The predecessor round stated this only at the abstract
pair `(kappa, s)` while the headline carried `x_T` free, so the lemma could not
be applied inside the headline's binder set at all.  With `x_T` pinned to
`2^{-b_T}` by a checked-identity binder (`06:243`, `08:166`) the third clause
of `eq:terminal-seed-inputs`, `log_2 s < b_T`, is exactly what makes the two
Stage-3 ladder instances legal.  General. -/
theorem row_density_legal_at_capacity {r₃ d bT : ℕ} {xT : ℝ}
    (hxT : xT = DenseStageFourOpening.xTdepth bT) (hr : r₃ < bT) :
    ((DenseWeightedCount.stoppingCapacity r₃ d : ℕ) : ℝ) * xT ≤ 1
      ∧ (2 : ℝ) ^ (r₃ - d) * xT ≤ 1 := by
  subst hxT
  have hs : (2 : ℕ) ^ r₃ < 2 ^ bT := Nat.pow_lt_pow_right (by norm_num) hr
  have hκs : DenseWeightedCount.stoppingCapacity r₃ d ≤ 2 ^ r₃ :=
    DenseWeightedCount.stoppingCapacity_le_width r₃ d
  have h := row_density_legal hκs hs
  refine ⟨h, ?_⟩
  rw [DenseWeightedCount.stoppingCapacity_eq] at h
  push_cast at h
  exact h

/-- **Aux E5c (`06:243`, `08:166`).**  At the pinned `x_T = 2^{-b_T}` the
`ell = 1` row density `2 x_T` is legal as soon as `b_T >= 1`, which
`log_2 s < b_T` supplies.  General. -/
theorem two_xT_le_one {bT : ℕ} {xT : ℝ}
    (hxT : xT = DenseStageFourOpening.xTdepth bT) (hbT : 1 ≤ bT) : 2 * xT ≤ 1 := by
  subst hxT
  have hnat : (2 : ℕ) ^ 1 ≤ 2 ^ bT := Nat.pow_le_pow_right (by norm_num) hbT
  have hR : (2 : ℝ) ≤ (2 : ℝ) ^ bT := by exact_mod_cast hnat
  rw [DenseStageFourOpening.xTdepth, mul_one_div, div_le_one (by positivity)]
  exact hR

/-- **Aux E5d (`09:1134--1147`, the ladder fires inside the headline's binder
set).**  With `x_T` and `y` pinned by the headline's checked-identity binders,
`eq:terminal-stage3-odd-copy` is available at *every* reached Stage-3 capacity
`kappa = stoppingCapacity r_3 d` with `kappa >= 4`, its row density being legal
by `row_density_legal_at_capacity`.  This is the composition the predecessor
round could not perform, because `y` was free where `09:1137` writes
`z = y = 3/5` and `x_T` was free where `06:243` writes `x_T = 2^{-b_T}`.
General in the selector matrix and in all four exponents. -/
theorem stage3_ladder_at_reached_capacity {Ltwo Jtwo : Type*} [Fintype Ltwo]
    [Fintype Jtwo] (S2 : Ltwo → Jtwo → Bool) {bcap r₂ r₃ d bT : ℕ} {xT y : ℝ}
    (hxT : xT = DenseStageFourOpening.xTdepth bT) (hy : y = 3 / 5) (hr : r₃ < bT)
    (hcap : 2 ≤ r₃ - d)
    (hlad : CertifiedRowLadder S2 (DenseBranchSelection.Dtwo bcap r₂) xT y) :
    DenseBranchSelection.Dtwo bcap r₂ + (r₃ - d)
      ≤ Dfamily (interlaceFun S2 (DenseWeightedCount.stoppingCapacity r₃ d / 2 + 1))
          (bracketGE Ltwo Jtwo (DenseWeightedCount.stoppingCapacity r₃ d / 2 + 1)
            ((2 : ℝ) ^ (r₃ - d) * xT) (9 / 25)) := by
  subst hy
  have hx := (row_density_legal_at_capacity (d := d) hxT hr).2
  have h := terminal_stage3_odd_copy S2 hcap hlad hx
  simpa [DenseWeightedCount.stoppingCapacity_eq] using h

/-- **Aux E5e (`09:1141--1142` inside the headline's binder set).**  The
`ell = 1` instance `eq:terminal-stage3-two-copy` likewise fires at the pinned
scalars, its row density `2 x_T` being legal by `two_xT_le_one` from the frozen
`log_2 s < b_T`.  General. -/
theorem stage3_ladder_two_copy_at_pins {Ltwo Jtwo : Type*} [Fintype Ltwo]
    [Fintype Jtwo] (S2 : Ltwo → Jtwo → Bool) {bcap r₂ r₃ bT : ℕ} {xT y : ℝ}
    (hxT : xT = DenseStageFourOpening.xTdepth bT) (hy : y = 3 / 5) (hr : r₃ < bT)
    (hlad : CertifiedRowLadder S2 (DenseBranchSelection.Dtwo bcap r₂) xT y) :
    DenseBranchSelection.Dtwo bcap r₂ + 1
      ≤ Dfamily (interlaceFun S2 2) (bracketGE Ltwo Jtwo 2 (2 * xT) (9 / 25)) := by
  subst hy
  exact terminal_stage3_two_copy S2 hlad (two_xT_le_one hxT (by omega))

/-- **Aux E5f (F-3, the ladder hypothesis is *supplied* by the headline's own
binders).**  `lem:certified-row-ladder`'s frozen antecedent
`Lambda_M(1, x, z) >= H` is, at the terminal substitution
`M = S_2 = M_2^T`, `H = D_2`, `x = x_T`, `z = y`, *literally the second
conjunct of* `eq:terminal-seed-inputs` (`09:849`), and its scale guard
`H >= 2` is `09:1148--1149` (`scale_guard`).  So the certified row ladder is
not an extra hypothesis of `lem:terminal-two-stream` at all: it follows from
the data the frozen statement already assumes.

This is the F-3 repair.  In the predecessor generation the four Stage-3
consequences below took `CertifiedRowLadder` as an unwitnessed binder, and
because its legality guard `2^ell x <= 1` is empty at any `x > 1/2` that binder
was satisfiable by vacuity.  With `certifiedRowLadder_of_base` proved, this
corollary *discharges* it from `terminalSeedInputs` + the entry conditions, and
the four consequences become theorems about the pinned construction.
General in the two matrices and in all five exponents. -/
theorem certifiedRowLadder_of_seedInputs {Cone Rone Ltwo Jtwo : Type*}
    [Fintype Cone] [Fintype Rone] [Fintype Ltwo] [Fintype Jtwo]
    (M1T : Cone → Rone → Bool) (S2 : Ltwo → Jtwo → Bool)
    {b₁ bcap r₂ r₃ bT : ℕ} {xT y : ℝ}
    (hL : 1 ≤ Fintype.card Ltwo) (hJ : 1 ≤ Fintype.card Jtwo)
    (hq : 16 ≤ 2 ^ r₂) (hxT0 : 0 < xT) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hseed : terminalSeedInputs M1T S2 b₁ bcap r₂ r₃ bT xT y) :
    CertifiedRowLadder S2 (DenseBranchSelection.Dtwo bcap r₂) xT y :=
  certifiedRowLadder_of_base S2 hL hJ (scale_guard bcap r₂ hq) hxT0 hy0 hy1
    hseed.2.1

/-- **Aux E5g (`eq:terminal-stage3-two-copy`, `09:1141--1142`, unconditional).**
The `ell = 1` Stage-3 instance with the ladder hypothesis *removed*: every
input is a binder of `lem:terminal-two-stream` itself.  The frozen
`q_2 >= 16` of `eq:terminal-entry` supplies the scale guard, and `log_2 s < b_T`
of `eq:terminal-seed-inputs` supplies the row-density legality.  General. -/
theorem stage3_two_copy_of_seedInputs {Cone Rone Ltwo Jtwo : Type*}
    [Fintype Cone] [Fintype Rone] [Fintype Ltwo] [Fintype Jtwo]
    (M1T : Cone → Rone → Bool) (S2 : Ltwo → Jtwo → Bool)
    {q₂ b₁ bcap r₂ r₃ bT : ℕ} {xT y ε δ' : ℝ}
    (hL : 1 ≤ Fintype.card Ltwo) (hJ : 1 ≤ Fintype.card Jtwo)
    (hdy : q₂ = 2 ^ r₂) (hxT : xT = DenseStageFourOpening.xTdepth bT)
    (hy : y = 3 / 5) (hentry : terminalEntry q₂ b₁ ε δ')
    (hseed : terminalSeedInputs M1T S2 b₁ bcap r₂ r₃ bT xT y) :
    DenseBranchSelection.Dtwo bcap r₂ + 1
      ≤ Dfamily (interlaceFun S2 2) (bracketGE Ltwo Jtwo 2 (2 * xT) (9 / 25)) := by
  have hq : 16 ≤ 2 ^ r₂ := by
    obtain ⟨h16, -, -⟩ := hentry
    omega
  have hxT0 : 0 < xT := by
    rw [hxT, DenseStageFourOpening.xTdepth]; positivity
  have hlad := certifiedRowLadder_of_seedInputs M1T S2 hL hJ hq hxT0
    (by rw [hy]; norm_num) (by rw [hy]; norm_num) hseed
  exact stage3_ladder_two_copy_at_pins S2 hxT hy hseed.2.2 hlad

/-- **Aux E5h (`eq:terminal-stage3-odd-copy`, `09:1143--1146`,
unconditional).**  The odd-copy Stage-3 instance at every reached capacity
`kappa = stoppingCapacity r_3 d >= 4`, again with the ladder hypothesis removed.
General. -/
theorem stage3_odd_copy_of_seedInputs {Cone Rone Ltwo Jtwo : Type*}
    [Fintype Cone] [Fintype Rone] [Fintype Ltwo] [Fintype Jtwo]
    (M1T : Cone → Rone → Bool) (S2 : Ltwo → Jtwo → Bool)
    {q₂ b₁ bcap r₂ r₃ d bT : ℕ} {xT y ε δ' : ℝ}
    (hL : 1 ≤ Fintype.card Ltwo) (hJ : 1 ≤ Fintype.card Jtwo)
    (hdy : q₂ = 2 ^ r₂) (hxT : xT = DenseStageFourOpening.xTdepth bT)
    (hy : y = 3 / 5) (hcap : 2 ≤ r₃ - d) (hentry : terminalEntry q₂ b₁ ε δ')
    (hseed : terminalSeedInputs M1T S2 b₁ bcap r₂ r₃ bT xT y) :
    DenseBranchSelection.Dtwo bcap r₂ + (r₃ - d)
      ≤ Dfamily (interlaceFun S2 (DenseWeightedCount.stoppingCapacity r₃ d / 2 + 1))
          (bracketGE Ltwo Jtwo (DenseWeightedCount.stoppingCapacity r₃ d / 2 + 1)
            ((2 : ℝ) ^ (r₃ - d) * xT) (9 / 25)) := by
  have hq : 16 ≤ 2 ^ r₂ := by
    obtain ⟨h16, -, -⟩ := hentry
    omega
  have hxT0 : 0 < xT := by
    rw [hxT, DenseStageFourOpening.xTdepth]; positivity
  have hlad := certifiedRowLadder_of_seedInputs M1T S2 hL hJ hq hxT0
    (by rw [hy]; norm_num) (by rw [hy]; norm_num) hseed
  exact stage3_ladder_at_reached_capacity S2 hxT hy hseed.2.2 hcap hlad

/-- **Aux E6 (`09:1152--1155`).**  "If `kappa >= 4`, then
`h_v >= 3 kappa/4 >= kappa/2 + 1`; select that many ordinary objects."  Written
at `kappa = 2 m` with `m >= 2`, which is the frozen dyadic shape, so that the
integer halving is exact.  General. -/
theorem odd_copy_selection {m h : ℕ} (hm : 2 ≤ m) (hforced : 3 * (2 * m) ≤ 4 * h) :
    m + 1 ≤ h := by omega

/-- **Aux E7 (`eq:terminal-stage3-budget`, `09:1166--1171`).**  "The suffix of
`P_3` below that child has depth at most `(C - 1) - d - 1 =
D_2 + log_2 kappa - 1`", at `kappa = 2^{r_3-d}`, i.e. `log_2 kappa = r_3 - d`.
General. -/
theorem stage3_budget (bcap r₂ r₃ d : ℕ) (hd : d ≤ r₃) :
    terminalTarget bcap r₂ r₃ - 1 - d - 1
      = DenseBranchSelection.Dtwo bcap r₂ + (r₃ - d) - 1 := by
  simp only [terminalTarget, DenseBranchSelection.Dtwo]
  omega

/-! ## Section 6  The two contradiction skeletons and the Extension row -/

/-- **Aux F1 (`eq:terminal-fixed-bin`, `09:1028--1033`).**  "Consequently the
fixed-bin state has complexity at least `D_2 + 1`."  The frozen "suppose for
contradiction that the resulting matrix has a protocol `P_2` of depth at most
`D_2`" turns a refuted shallow protocol into the displayed one-bit-above bound;
that step is this arithmetic, and nothing else.  General. -/
theorem one_bit_above_of_not_shallow {c d : ℕ} (h : ¬ c ≤ d) : d + 1 ≤ c :=
  Nat.lt_of_not_le h

/-- **Aux F2 (`09:1161--1173`).**  "the selected Bob child has complexity at
least `D_2 + log_2 kappa`.  The suffix of `P_3` below that child has depth at
most `D_2 + log_2 kappa - 1`, a contradiction."  General. -/
theorem stage3_contradiction {a b : ℕ} (ha : 1 ≤ a) (hbudget : b ≤ a - 1)
    (hcomp : a ≤ b) : False := by omega

/-- **Call (ii) of `sec:extension-call-ledger`, the *per-call* row conditions
of `06:1161--1162`.**  At `v = 2` the ambient copy count is `q_amb = 2 q_2`
(`06:1120--1123`, instantiated at `09:1018`) and the represented capacity is
`K = kappa_v`; the theorem's remaining integer binders are `r = q_amb/t_2` and
`r' = K/t_2` (`06:1122--1124`), and the frozen closing conditions are exactly
"`K` is a multiple of `t_2`" and "`1 <= r' <= r`".

**Repair note (r1).**  The width conditions `t_2 = 2^{k_2}` and `16 | t_2` are
`eq:stage2-balance-ceilings` (`07:278--281`) and belong to the *width record*,
not to a per-capacity row; carrying them inside this predicate and then
quantifying it over every `K <= 2 q_2` made the bundle self-contradictory at
`K = 1` (`t_2 | 1` forces `t_2 = 1`, which `16 | t_2` refutes).  They are now
separate binders of the headline, and this predicate is the frozen row and
nothing else.  The frozen `h = 49/64`, `a^sharp = 1` and the selected block
count `9K/16` are recorded by the readouts below rather than as opaque data.
General in the three widths. -/
def extensionCallTwo (q₂ t₂ K : ℕ) : Prop :=
  t₂ ∣ K ∧ 1 ≤ K / t₂ ∧ K / t₂ ≤ 2 * q₂ / t₂

/-- **Aux F3 (`06:1126--1130` and `06:1162`).**  "The consuming branch
constructs the branch-local support set `Q_s` and proves the exact output-size
equation `|Q_s| = r' p_seed = 9K/16`", at `p_seed = 9 t_2/16`
(`eq:extension-common-binders`, `06:1111`).  This is the frozen exactness, and
`09:1014` is its instance "select `9 kappa_v/16` ordinary coordinates".  The
two width facts it needs are the frozen `07:280` ones, passed explicitly.
General. -/
theorem extensionCallTwo_block_count {q₂ t₂ K : ℕ} (ht0 : 0 < t₂) (h16 : 16 ∣ t₂)
    (h : extensionCallTwo q₂ t₂ K) :
    (K / t₂) * (9 * t₂ / 16) = 9 * K / 16 := by
  obtain ⟨⟨c, hc⟩, _, _⟩ := h
  obtain ⟨e, he⟩ := h16
  subst hc
  subst he
  have h16 : (0 : ℕ) < 16 := by norm_num
  rw [Nat.mul_div_cancel_left _ ht0]
  have h1 : 9 * (16 * e) / 16 = 9 * e := by omega
  rw [h1]
  have h2 : 9 * (16 * e * c) / 16 = 9 * e * c := by
    have : 9 * (16 * e * c) = 16 * (9 * e * c) := by ring
    rw [this, Nat.mul_div_cancel_left _ h16]
  rw [h2]
  ring

/-- **Aux F4 (`06:1142--1145` and `09:1019`).**  "Here `v = 2`, `K = kappa_v`,
`h = 49/64`, and `a^sharp = 1` ... the chosen Alice child has column density at
least `49/128 = h 2^{-a^sharp}`."  The frozen identity between the call table's
`h 2^{-a^sharp}` and the Section-9 post-query density. -/
theorem extensionCallTwo_post_query_density :
    (49 : ℝ) / 64 * ((2 : ℝ) ^ (1 : ℕ))⁻¹ = 49 / 128 := by norm_num

/-- **Aux F5 (`07:278`).**  The Stage-2 independence width is a positive dyadic
number.  General. -/
theorem extensionWidth_pos {t₂ k₂ : ℕ} (hdy : t₂ = 2 ^ k₂) : 0 < t₂ := by
  subst hdy
  positivity

/-- **Aux F6 (`07:278` with `07:280`).**  `t_2 = 2^{k_2}` and `16 | t_2` force
`k_2 >= 4`; equivalently the two frozen width conditions are the single
exponent condition, which is why they belong to the width binder and not to a
per-capacity row.  General. -/
theorem extensionWidth_four_le {t₂ k₂ : ℕ} (hdy : t₂ = 2 ^ k₂) (h16 : 16 ∣ t₂) :
    4 ≤ k₂ := by
  subst hdy
  by_contra hcon
  have hlt : k₂ < 4 := Nat.lt_of_not_le hcon
  have hle : (2 : ℕ) ^ k₂ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < (2 : ℕ) ^ k₂ := by positivity
  have := Nat.le_of_dvd hpos h16
  omega

/-- **Aux F7 (`09:1013--1014` with `06:1161--1162`, the repaired
quantification).**  The frozen text invokes call (ii) exactly at the *reached*
isolation capacities and only when `kappa_v >= t_2`: "If `kappa_v >= t_2`,
select `9 kappa_v/16` ordinary coordinates ... and invoke Localized Extension
at the fixed physical width `t_2`.  ...  If `2 <= kappa_v < t_2`, the inherited
two-copy and odd-copy bounds give the same target.  If `kappa_v = 1`, the
positive excess ... supplies either an unsplit attached pair or two ordinary
coordinates."  So the call's domain is `{kappa_v = stoppingCapacity r_2 d :
t_2 <= kappa_v}`, never all of `[1, 2 q_2]`; `2 q_2` enters only as the
*ambient* width `q_amb = v q_2` of `06:1120--1123`, i.e. inside `r = q_amb/t_2`.

At the frozen dyadic widths this row is then *discharged* by the schedule
rather than assumed, which is exactly what `06:1161--1162` asserts
("Equations ... verify the legal row range ... uniformly over these four
substitutions").  General in the four exponents. -/
theorem extensionCallTwo_of_widths {q₂ t₂ k₂ r₂ d : ℕ} (hq : q₂ = 2 ^ r₂)
    (hdy : t₂ = 2 ^ k₂) (hK : t₂ ≤ DenseWeightedCount.stoppingCapacity r₂ d) :
    extensionCallTwo q₂ t₂ (DenseWeightedCount.stoppingCapacity r₂ d) := by
  subst hq
  subst hdy
  simp only [DenseWeightedCount.stoppingCapacity_eq] at hK ⊢
  have hk : k₂ ≤ r₂ - d := (Nat.pow_le_pow_iff_right (by norm_num)).1 hK
  refine ⟨pow_dvd_pow 2 hk, ?_, ?_⟩
  · exact (Nat.one_le_div_iff (by positivity)).2 hK
  · have h1 : (2 : ℕ) ^ (r₂ - d) ≤ 2 ^ r₂ :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ r₂ ≤ 2 * 2 ^ r₂ := by omega
    exact Nat.div_le_div_right (le_trans h1 h2)

/-! ### The call-(ii) *fixed-width* hypotheses (repair r2, F-1)

`09:856--858` assumes "the fixed-width hypotheses of Localized Extension for
the `C_2 x C_2` product family, as listed for call (ii) in
`sec:extension-call-ledger`", and `06:1161--1167` is that list:  the per-call
row conditions (`extensionCallTwo`, above), and then

> Equations `eq:stage2-structural-gates` and `eq:all-extension-gates` verify
> the legal row range, both inherited column-loss inequalities, the product
> balancedness error, and the hard-seed comparison uniformly over these four
> substitutions.

The predecessor generation transcribed **none** of this.  What follows lands
the frozen displays those two sentences name, at the call-(ii) substitution
`v = 2`, `K = kappa_v`, `h = 49/64`, `a^sharp = 1` (`06:1140--1145`). -/

/-- **Aux F8 (`eq:certified-E1` in its `t`-th-power form).**  The frozen
column-loss inequality is a `t`-th root comparison; for a nonnegative left side
it is equivalent to the polynomial form, and only the direction used below is
needed.  This is the same rewriting `WrapperLowRungs` records at the reference
call, performed rather than assumed.  General in the density, the error, the
width and the spent-bit count. -/
theorem le_yLoss_of_pow_le {ε h yStar : ℝ} {t c : ℕ} (ht : 0 < t)
    (hy0 : 0 ≤ yStar)
    (hpow : yStar ^ t ≤ h * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε)) :
    yStar ≤ yLoss ε t h c := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hroot : (yStar ^ t) ^ (1 / (t : ℝ)) = yStar := by
    rw [← Real.rpow_natCast yStar t, ← Real.rpow_mul hy0, mul_one_div,
      div_self (ne_of_gt htR), Real.rpow_one]
  unfold yLoss
  calc yStar = (yStar ^ t) ^ (1 / (t : ℝ)) := hroot.symm
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hy0 t) hpow (by positivity)

/-- **Aux F9 (`eq:epsilon-product`, `06:851--857`), PROVED.**  The frozen
display *asserts* that at `eps_2 = 1/(100 t_2)` the product balancedness error
`eps_prod = max{(1+eps_2)^{t_2} - 1, 1 - (1-eps_2)^{t_2}}` is smaller than
`1/50`.  That assertion is a uniform arithmetic fact about every positive
width, and it is discharged here rather than carried: the lower branch is
Bernoulli (`1 - (1-a)^t <= t a = 1/100`) and the upper branch is Bernoulli
applied to `1/(1-a)` (`(1+a)^t <= (1-a)^{-t} <= 1/(1-ta) = 100/99`).  General in
the width. -/
theorem epsProd_lt_fiftieth {t : ℕ} (ht : 0 < t) :
    max ((1 + 1 / (100 * (t : ℝ))) ^ t - 1) (1 - (1 - 1 / (100 * (t : ℝ))) ^ t)
      < 1 / 50 := by
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  set a : ℝ := 1 / (100 * (t : ℝ)) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hta : (t : ℝ) * a = 1 / 100 := by rw [ha]; field_simp
  have ha1 : a ≤ 1 / 100 := by nlinarith
  -- Bernoulli at `-a`: `1 - t a <= (1 - a)^t`
  have hbern : 1 - (t : ℝ) * a ≤ (1 - a) ^ t := by
    have h := one_add_mul_le_pow (a := -a) (by linarith) t
    have hrw : (1 : ℝ) + -a = 1 - a := by ring
    rw [hrw] at h
    calc 1 - (t : ℝ) * a = 1 + (t : ℝ) * (-a) := by ring
      _ ≤ (1 - a) ^ t := h
  rw [hta] at hbern
  have hpow0 : (0 : ℝ) < (1 - a) ^ t := by linarith
  -- the upper branch
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hstep : (1 + a) ≤ 1 / (1 - a) := by
    rw [le_div_iff₀ h1a]; nlinarith
  have hup : (1 + a) ^ t ≤ 1 / (1 - a) ^ t := by
    calc (1 + a) ^ t ≤ (1 / (1 - a)) ^ t :=
          pow_le_pow_left₀ (by linarith) hstep t
      _ = 1 / (1 - a) ^ t := by rw [div_pow, one_pow]
  have hup2 : 1 / (1 - a) ^ t ≤ 100 / 99 := by
    rw [div_le_div_iff₀ hpow0 (by norm_num)]
    nlinarith
  refine max_lt ?_ ?_
  · linarith
  · linarith

/-! ### The `C_2 x C_2` product family (repair r3, F-4)

`09:856--858` assumes the fixed-width hypotheses "for the `C_2 x C_2` product
family", and `06:1116--1123` is the call ledger's own description of that
object:

> For an integer `v >= 1`, let `M^_v` denote the relaxed interlace of `M`
> represented by the `v`-fold Cartesian product of the physical family `C_2`.
> Its ambient copy count is `q_amb = v q_2`, its independence width is still
> `t_2`, and its balancedness error is `eps_2` when `v = 1` and at most
> `eps_prod` otherwise.

`06:1163--1166` then lists "the product balancedness error" among the four
items the gates verify, so it is gate *content*, not an aside.  The predecessor
generation pinned the two numerals `eps_2` and `eps_prod` but bound them to no
family, which left the headline quantifying over an arbitrary `cFam` -- strictly
*stronger* than `lem:terminal-two-stream`, since at an unbalanced family the
Extension call of `09:1014--1019` has no licence to fire.

What follows supplies the missing object and the two clauses.  Balancedness is
consumed from the **vendored, project-axiom-free** predicate
`NPCC.IsBalancedFamily` (`vendor/npc-cc/NPCC/Relaxed.lean:19`), in exactly the
shape the banked `hbal` binders of `StageTwoRelaxed.stageTwoOneDepth`
(`StageTwoRelaxed.lean:1592`) and `.stageTwoTwoDepthCertificate` (`:1955`) use,
and for exactly the reason `stageTwo_balancedness_is_not_a_field` (`:2065`)
records: `def:level-parameters` (`05:183--189`) says the balancedness formula
"remains a post-construction admissibility proposition; it is not a proof
field", so it must be an explicit binder and can never be projected out of a
record.  Note the width at which the predicate is applied: the independence
width is **still `t_2`** (`06:1121`), never `q_2` and never `2 q_2`; only the
ambient copy count moves, from `q_2` to `q_amb = 2 q_2`.

`LegacyNPCC.Stage12` stays unimported and the AGHP existence axiom
(`EXPANDER-001`) is reached by nothing here.  A *binder* needs a model, not an
existence theorem at the frozen Stage-2 carriers, and `A:120--122` supplies one
outright: `M^` may be formed "either from a `(q,t,eps)`-balanced family with
`0 < eps < 1`, or from the exact full product, in which case `eps = 0`".  The
exact full product is the inhabitant used below, so the LANE-GATE 3 witness for
the two new fields runs at a genuine two-letter column alphabet rather than at
a one-point alphabet where balancedness has no content.

**Why the product clause is a binder and not a derivation here.**  The frozen
paper *does* prove it, at `lem:product-balancedness` (`A:333--356`): a
`(q,t,eps_0)`-balanced family's `v`-fold Cartesian product is
`(vq,t,eps_*)`-balanced with `eps_* = max{(1+eps_0)^t-1, 1-(1-eps_0)^t}`.  But
`03:333--337` and `D:604--638` are explicit that its **Lean** transcription is a
*required reboot bridge*, not an inherited endpoint: "No theorem in the frozen
dependency certifies the product families used by the active Localized Extension
calls ... they may be cited in this manuscript, but not imported as a checked
dependency theorem."  So this module transcribes the product family by the exact
contract `D:620--624` and carries the product's balancedness as the hypothesis
`09:856--858` states it to be; deriving it is a separate obligation and is
**not** claimed here (GAP-EXPOSED 7).

Reader provenance, opened first-hand: `lem:paper-product-balancedness`
(`reader-facing/sections/02-preliminaries.tex:401--411`) is the reader-level
statement of `lem:product-balancedness`, and `02:383--390` is the reader's
`(q,t,eps)`-balancedness definition.  Neither is **claimed** as a proved
counterpart by any declaration here -- this module assumes the clause, it does
not prove it -- so both stay available to the future obligation that discharges
`D:620--632`.  The reader artifact carries no extension-call ledger, so the rest
of this subsection has no reader counterpart at all. -/

/-- **Aux F18 (`eq:contract-product-family`, `D:620--624`): the `v`-fold
Cartesian product of the physical family.**  The frozen inherited-contract
appendix fixes this transcription exactly -- the explicit equivalences
`[vq] ~= [v] x [q]` and `[L^v] ~= ([v] -> [L])`, and then
`S^{(x)v}(J)(r,i) := S(J(r))(i)`.  Both equivalences are taken from Mathlib
(`finProdFinEquiv`, `finFunctionFinEquiv`) so that no second, silently
different, indexing convention can enter.  At `v = 2` this is the
`C_2 x C_2` product family of `06:1119--1120`, with ambient copy count
`q_amb = 2 q_2` and index carrier `L_2^2`.  General in `v`, the alphabet, the
ambient width and the index count. -/
def productFamily (v : ℕ) {Y : Type*} {q L : ℕ} (S : Fin L → Fin q → Y) :
    Fin (L ^ v) → Fin (v * q) → Y :=
  fun J i => S (finFunctionFinEquiv.symm J (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2

/-- **Aux F19 (the product of an enumerating family, as an equivalence).**
Packaging `eq:contract-product-family` as an `Equiv` when the physical family is
one; this is what makes the product's index count exactly `L^v`.  General. -/
def productFamilyEquiv (v : ℕ) {Y : Type*} {q L : ℕ} (e : Fin L ≃ (Fin q → Y)) :
    Fin (L ^ v) ≃ (Fin (v * q) → Y) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.arrowCongr (Equiv.refl (Fin v)) e).trans
      ((Equiv.curry (Fin v) (Fin q) Y).symm.trans
        (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Y))))

/-- **Aux F20 (the equivalence *is* the product family).**  Unit test tying
`productFamilyEquiv` back to `productFamily`.  General. -/
theorem productFamilyEquiv_apply (v : ℕ) {Y : Type*} {q L : ℕ}
    (e : Fin L ≃ (Fin q → Y)) :
    ⇑(productFamilyEquiv v e) = productFamily v (⇑e) := rfl

/-- **Aux F21 (`eq:contract-product-family` at explicit block coordinates).**
Unit test: at the ambient coordinate carrying block index `r` and within-block
index `i`, the product family reads factor `r` of the index tuple at
coordinate `i` -- letter for letter the frozen `S^{(x)v}(J)(r,i) = S(J(r))(i)`.
General. -/
theorem productFamily_block (v : ℕ) {Y : Type*} {q L : ℕ} (S : Fin L → Fin q → Y)
    (J : Fin (L ^ v)) (r : Fin v) (i : Fin q) :
    productFamily v S J (finProdFinEquiv (r, i))
      = S (finFunctionFinEquiv.symm J r) i := by
  simp [productFamily]

/-- **Aux F22 (the product of a constant family is constant).**  Unit test, and
the reason the F-4 probe fails at the *first* balancedness field rather than
accidentally at the second: a constant physical family produces a constant
product family, so neither field can rescue it.  General. -/
theorem productFamily_const (v : ℕ) {Y : Type*} {q L : ℕ} (y : Y) :
    productFamily v (fun (_ : Fin L) (_ : Fin q) => y)
      = fun (_ : Fin (L ^ v)) (_ : Fin (v * q)) => y := rfl

/-- **Aux F23 (the product of an enumerating family enumerates).**  If the
physical family enumerates every ambient `q`-tuple exactly once then its
`v`-fold Cartesian product enumerates every ambient `vq`-tuple exactly once.
General. -/
theorem productFamily_bijective (v : ℕ) {Y : Type*} {q L : ℕ}
    {S : Fin L → Fin q → Y} (hS : Function.Bijective S) :
    Function.Bijective (productFamily v S) := by
  have hE : productFamily v S = ⇑(productFamilyEquiv v (Equiv.ofBijective S hS)) := rfl
  rw [hE]
  exact (productFamilyEquiv v (Equiv.ofBijective S hS)).bijective

/-- **Aux F24 (the physical family on the vendored index carrier).**
`NPCC.IsBalancedFamily` is stated for a family indexed by `Fin L`; the headline's
`cFam` is indexed by the abstract finite carrier `Ltwo` of `def:two-stream-state`.
This is the transport along `Fintype.equivFin`, and it is the only reindexing
performed anywhere below.  General. -/
noncomputable def familyOnIndices {Ltwo Rone : Type*} [Fintype Ltwo] {q : ℕ}
    (cFam : Ltwo → Slot q → Rone) : Fin (Fintype.card Ltwo) → Slot q → Rone :=
  fun j => cFam ((Fintype.equivFin Ltwo).symm j)

/-- **Aux F25 (the transport preserves bijectivity).**  Unit test: reindexing
along an equivalence changes nothing about whether the family enumerates the
ambient tuples.  General. -/
theorem familyOnIndices_bijective {Ltwo Rone : Type*} [Fintype Ltwo] {q : ℕ}
    {cFam : Ltwo → Slot q → Rone} (h : Function.Bijective cFam) :
    Function.Bijective (familyOnIndices cFam) :=
  h.comp (Fintype.equivFin Ltwo).symm.bijective

/-- **Aux F26 (balancedness does not depend on how the index carrier is
enumerated).**  `familyOnIndices` transports along `Fintype.equivFin`, which is
*some* enumeration of `Ltwo` and not a canonical one; this is the check that the
two fields added below therefore say the same thing whichever enumeration is
picked -- `eq:contract-balanced` counts a filter over the whole index carrier,
so reindexing is invisible to it.  Without this the fields would be well-typed
but not well-defined as statements about `cFam`.  General. -/
theorem isBalancedFamily_reindex {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L L' t : ℕ} (e : Fin L' ≃ Fin L) {S : Fin L → Fin q → Y} {ε : ℝ}
    (h : IsBalancedFamily t S ε) :
    IsBalancedFamily t (fun j => S (e j)) ε := by
  classical
  have hLL : L' = L := by
    simpa using Fintype.card_congr e
  refine ⟨by rw [hLL]; exact h.1, ?_⟩
  intro J hJ a
  have hcount : (Finset.univ.filter (fun j : Fin L' => ∀ γ ∈ J, S (e j) γ = a γ)).card
      = (Finset.univ.filter (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
  rw [hcount, hLL]
  exact h.2 J hJ a

/-- **Aux F27 (balancedness is monotone in the error).**  `06:1121--1123` says
the product family's error is "**at most** `eps_prod`", so the field below is
the predicate *at* `eps_prod`; this is the lemma that makes that reading the
right one, and it is what lets an exactly balanced family (`eps = 0`,
`A:120--122`) discharge a field stated at a positive tolerance.  General. -/
theorem isBalancedFamily_mono {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε ε' : ℝ} (hεε : ε ≤ ε')
    (h : IsBalancedFamily t S ε) : IsBalancedFamily t S ε' := by
  refine ⟨h.1, ?_⟩
  intro J hJ a
  refine le_trans (h.2 J hJ a) ?_
  have hc : (0 : ℝ) ≤ ((Fintype.card Y : ℝ) ^ J.card)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right hεε hc
  simpa [div_eq_mul_inv] using hmul

/-- **Aux F28 (the columns agreeing with a pattern on `J`).**  Fixing a total
pattern on `J` and leaving the complement free is an equivalence with the
functions on the complement.  This is the counting step behind exact
balancedness.  General. -/
def agreeEquiv {Y : Type*} {q : ℕ} [DecidableEq (Fin q)] (J : Finset (Fin q))
    (a : Fin q → Y) :
    {s : Fin q → Y // ∀ γ ∈ J, s γ = a γ} ≃ ({γ : Fin q // γ ∉ J} → Y) where
  toFun s := fun γ => s.1 γ.1
  invFun f := ⟨fun γ => if h : γ ∈ J then a γ else f ⟨γ, h⟩, by
    intro γ hγ; simp [hγ]⟩
  left_inv := by
    intro s
    apply Subtype.ext
    funext γ
    by_cases h : γ ∈ J
    · simp [h, s.2 γ h]
    · simp [h]
  right_inv := by
    intro f
    funext γ
    simp [γ.2]

/-- **Aux F29 (the exact count of agreeing columns).**  `|Y|^{q - |J|}` columns
of the full product agree with a given pattern on `J`.  General. -/
theorem card_agree {Y : Type*} [DecidableEq Y] [Fintype Y] {q : ℕ}
    (J : Finset (Fin q)) (a : Fin q → Y) :
    Fintype.card {s : Fin q → Y // ∀ γ ∈ J, s γ = a γ}
      = Fintype.card Y ^ (q - J.card) := by
  rw [Fintype.card_congr (agreeEquiv J a), Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp [Fintype.card_coe]

/-- **Aux F30 (`A:120--122`: the exact full product is exactly balanced).**
The frozen certified-stopping theorem permits `M^` to be formed "from the exact
full product, in which case `eps = 0`".  Here that clause is *proved* rather
than assumed: a family enumerating every ambient tuple exactly once meets the
`def:balanced-family` inequality with error `0`, at every independence width
`t`.  This is the LANE-GATE 3 model for the two fields added below, and it is
what makes them binders with content rather than binders no model satisfies.
General in the alphabet, the ambient width and the index count. -/
theorem isBalancedFamily_zero_of_bijective {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L : ℕ} (t : ℕ) (hY : 0 < Fintype.card Y) {S : Fin L → Fin q → Y}
    (hS : Function.Bijective S) : IsBalancedFamily t S 0 := by
  classical
  have hL : L = Fintype.card Y ^ q := by
    have hcard := Fintype.card_of_bijective hS
    simpa [Fintype.card_fun] using hcard
  have hLpos : 0 < L := by
    rw [hL]; exact Nat.pow_pos hY
  refine ⟨hLpos, ?_⟩
  intro J hJ a
  have hJq : J.card ≤ q := by simpa using (Finset.card_le_univ J)
  have hcount : (Finset.univ.filter (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ)).card
      = Fintype.card Y ^ (q - J.card) := by
    rw [← Fintype.card_subtype, ← card_agree J a]
    exact Fintype.card_congr
      (Equiv.subtypeEquiv (Equiv.ofBijective S hS) (fun _ => Iff.rfl))
  rw [hcount, hL]
  have hYR : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hsplit : (Fintype.card Y : ℝ) ^ q
      = (Fintype.card Y : ℝ) ^ (q - J.card) * (Fintype.card Y : ℝ) ^ J.card := by
    rw [← pow_add]; congr 1; omega
  have hkey : ((Fintype.card Y : ℝ) ^ (q - J.card)) / ((Fintype.card Y : ℝ) ^ q)
      = 1 / (Fintype.card Y : ℝ) ^ J.card := by
    rw [hsplit]; field_simp
  push_cast
  rw [hkey]
  simp

/-- **Statement pole 6 (the balancedness binder excludes the constant family).**
The r2 defect was that `cFam` was constrained by nothing, so the *constant*
family -- which `PublicRecords.levelParams_admits_unbalanced_family` shows a
legal level record may carry -- was admissible.  With the binder present it is
not: at any two-letter or larger alphabet and any positive ambient width, a
constant family fails `def:balanced-family` for every error below `1`, because
the singleton pattern set `J = {0}` at a letter the family never takes has
empirical frequency `0` against target `1/|Y|`.  Since the schedule fixes
`eps_2 = 1/(100 t_2) < 1` (`06:852`), the new field is a genuine restriction and
not a decoration.  General. -/
theorem constant_family_not_balanced {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} (hq : 0 < q) (ht : 0 < t) (y y' : Y) (hne : y ≠ y') {ε : ℝ}
    (h : IsBalancedFamily t (fun (_ : Fin L) (_ : Fin q) => y) ε) : 1 ≤ ε := by
  classical
  have hYpos : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨y⟩
  have hYR : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hYpos
  set J : Finset (Fin q) := {(⟨0, hq⟩ : Fin q)} with hJdef
  have hJcard : J.card = 1 := by rw [hJdef]; simp
  have hbound := h.2 J (by rw [hJcard]; omega) (fun _ => y')
  have hempty : (Finset.univ.filter
      (fun _ : Fin L => ∀ γ ∈ J, y = y')) = (∅ : Finset (Fin L)) := by
    apply Finset.filter_false_of_mem
    intro j _ hall
    exact hne (hall (⟨0, hq⟩ : Fin q) (by rw [hJdef]; simp))
  rw [hempty, hJcard] at hbound
  simp only [Finset.card_empty, Nat.cast_zero, zero_div, zero_sub, pow_one,
    abs_neg] at hbound
  rw [abs_of_nonneg (by positivity)] at hbound
  rw [div_le_div_iff₀ hYR hYR] at hbound
  nlinarith

/-- **The call-(ii) fixed-width hypotheses of Localized Extension
(`09:856--858`), transcribed (repair r2, F-1; family attached in repair r3,
F-4).**

At call (ii) the substitution is `v = 2`, `K = kappa_v`, `h = 49/64`,
`a^sharp = 1` (`06:1140--1145`), on the common binders `M = M_1^T`,
`H = B_cap`, `x = 2^{-b_1}`, `y = 3/5`, `t = t_2`, `p_seed = 9 t_2/16`
(`eq:extension-common-binders`, `06:1107--1114`).  The eleven conjuncts are, in
the frozen order (nine arithmetic, then the two family clauses repair r3 adds):

1--3. `eq:epsilon-product` (`06:851--857`): `eps_2 = 1/(100 t_2)`, the product
error `eps_prod = max{(1+eps_2)^{t_2}-1, 1-(1-eps_2)^{t_2}}`, and the frozen
bound `eps_prod < 1/50`.  This is the "product balancedness error" of
`06:1165`.  `epsProd_lt_fiftieth` shows the third conjunct is a *consequence*
of the first two, so the bundle is not over-determined.

4--5. The two schedule majorants of `06:938--940`: call (ii) has ambient width
`2 q_2`, so `2 <= v_max`; and its row density is `x = 2^{-b_1}`
(`06:1110`), so its inverse row density `2^{b_1}` is at most `2^{L_h}`, i.e.
`b_1 <= L_h`.

6--7. `eq:all-extension-gates` (`06:941--951`), both lines, verbatim.  These
are the two displays `06:1163--1166` names as verifying the legal row range,
both inherited column-loss inequalities, the product balancedness error and
the hard-seed comparison.

8--9. The two inherited column-loss inequalities themselves, `eq:certified-E1`
(`A:130--134`) and `eq:certified-E2` (`A:135--136`), at the call-(ii)
substitution: `log_2 q_amb = log_2(2 q_2) = r_2 + 1`, `log_2 t_2 = k_2`,
`H = B_cap`, `h = 49/64`, `eps = eps_prod`, `y_* = 3/5`, and the frozen
hard-seed column density `h_{t_2} = h_2^seed` consumed by pin from
`StageTwoRelaxed.hSeedTwo` (`07:288--293`).  They are carried in *addition* to
the gates because `06:952--953` claims only that the gates are "stronger than
the literal Localized Extension hypotheses"; that implication is not proved
here, so the literal inequalities are transcribed rather than inferred.

10--11 (repair r3, F-4). The two clauses of `06:1116--1123` that say *which
family* the numerals `eps_2` and `eps_prod` are errors **of**.  `09:857` fixes
that family: the hypotheses are assumed "for the `C_2 x C_2` product family".
So the physical family `C_2 = cFam` is `(q_2, t_2, eps_2)`-balanced, and its
`2`-fold Cartesian product -- ambient copy count `q_amb = 2 q_2`, independence
width **still `t_2`** -- has balancedness error at most `eps_prod`.  Both are
`NPCC.IsBalancedFamily` at width `W.t₂`, in the shape of the banked `hbal`
binders, on the transported family `familyOnIndices cFam`; "at most `eps_prod`"
is the predicate *at* `eps_prod`, which `isBalancedFamily_mono` justifies.
Without these two clauses the preceding nine conjuncts pin two reals with no
referent and the headline quantifies over an arbitrary, possibly constant,
family -- strictly stronger than the frozen lemma.  `constant_family_not_balanced`
and `extProbe_constantFamily_fails` record that the clauses genuinely bite, and
`fixedWidth_family_content_is_exactly_the_two_clauses` records that they are the
only place the family argument acts.

The product family is `productFamily 2 (familyOnIndices cFam)`, i.e. the exact
frozen contract `eq:contract-product-family` (`D:620--624`) at `v = 2`.  Field 11
is **not** derived from field 10: the frozen derivation is
`lem:product-balancedness` (`A:333--356`), whose Lean transcription `D:604--638`
declares a required reboot bridge that "may be cited in this manuscript, but not
imported as a checked dependency theorem" -- so both clauses are carried exactly
as `09:856--858` states them, and the derivation stays GAP-EXPOSED (item 7).

The "legal row range" is **discharged**, not assumed: it is `t_2 x <= 1`, i.e.
the frozen `t_2 <= 2^{b_1}` of `07:281`, which the banked width record proves
(`StageTwoWidths.t₂_le_two_pow_b₁`).  The remaining per-call conditions of
`06:1161--1162` are `extensionCallTwo`, bound separately by the headline over
the reached capacities.

General in the width record, the two column carriers, the family, the three
integer schedule parameters and the two errors. -/
def ExtensionCallTwoFixedWidth {Ltwo Rone : Type*} [Fintype Ltwo] [Fintype Rone]
    [DecidableEq Rone] (W : StageTwoRelaxed.StageTwoWidths)
    (cFam : Ltwo → Slot W.q₂ → Rone)
    (bcap Lh vmax : ℕ) (eps2 epsProd : ℝ) : Prop :=
  eps2 = 1 / (100 * (W.t₂ : ℝ))
    ∧ epsProd = max ((1 + eps2) ^ W.t₂ - 1) (1 - (1 - eps2) ^ W.t₂)
    ∧ epsProd < 1 / 50
    ∧ 2 ≤ vmax
    ∧ W.b₁ ≤ Lh
    ∧ (Lh : ℝ) + Real.logb 2 ((vmax : ℝ) * (W.q₂ : ℝ)) + (bcap : ℝ)
        + Real.logb 2 (1 + epsProd)
        ≤ (W.t₂ : ℝ) * Real.logb 2 (5 / 3)
    ∧ (Lh : ℝ) + (W.k₂ : ℝ) + (bcap : ℝ) + Real.logb 2 (1 + epsProd)
        ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (W.k₂ : ℝ))
    ∧ 3 / 5 ≤ yLoss epsProd W.t₂ (49 / 64) (W.r₂ + 1 + bcap)
    ∧ StageTwoRelaxed.hSeedTwo W.k₂
        ≤ (49 / 64) * (2 : ℝ) ^ (-((W.k₂ + bcap : ℕ) : ℝ)) / (1 + epsProd)
    ∧ IsBalancedFamily W.t₂ (familyOnIndices cFam) eps2
    ∧ IsBalancedFamily W.t₂ (productFamily 2 (familyOnIndices cFam)) epsProd

/-! ### `eq:all-extension-gates` factored at its home (`cc-t7o-r2`, THE HOMING)

**Autoformalization anchor:** `eq:all-extension-gates` (`06:941--951`), opened
first-hand in the frozen release named by
`routes/parameterized-np/CURRENT_VERSION` and quoted at the bytes:

```
06:941 \begin{equation}
06:942 \begin{aligned}
06:943     t_2\log_2(5/3)
06:944        &\ge L_h+\log_2(v_{\max}q_2)+\Bcap
06:945           +\log_2(1+\eps_{\mathrm{prod}}),\\
06:946     2^{0.49\sqrt{\log_2t_2}}
06:947        &\ge L_h+\log_2t_2+\Bcap
06:948           +\log_2(1+\eps_{\mathrm{prod}}).
06:949 \end{aligned}
06:950 \label{eq:all-extension-gates}
06:951 \end{equation}
```

**Why this block is in this file and not downstream.**  These two rows already
existed here, as conjuncts 6--7 of `ExtensionCallTwoFixedWidth` (`:1970`) --
that declaration's own docstring says so in those words ("6--7.
`eq:all-extension-gates` (`06:941--951`), both lines, verbatim").  `cc-t7o`
wrote a fresh copy of them into a downstream `Prop` at the `ScheduleContext`;
`cc-t7o-r1` moved that copy to a downstream *factored* surface and proved a
projection into it.  The `cc-t7o-r1` Sol gate refuted both shapes at statement
level -- "moving the duplicate downstream and adding a projection does not
constitute factoring at the owner's home" -- and prescribed the named factor at
**this** module.  That refactor is the licence this block is written under.

**The factor is placed BESIDE the bundle, never substituted into it.**
`ExtensionCallTwoFixedWidth` is byte-identical across this edit.  Substituting a
two-conjunct name into its flat right-nested eleven-conjunct chain would
re-associate the chain -- `(a /\ b) /\ c` is not `a /\ (b /\ c)` -- and break the
positional hypothesis destructurers `OwnerTransferFamily`,
`OwnerIndexedTransferFamily`, `OwnerMassTransfer`, `OwnerFamilyToPigeonhole` and
`MassRedistributionTail`.  That is the `(a4)` defect class that cost `cc-t7m`
three rounds.  Owner beside the untouched chain, plus the projection
`extensionCallTwoFixedWidth_supplies_extensionGates`, is the licensed `(a4)`
shape -- the same one `Stage2StructuralGates`/`PhysicalStage4Gates` take beside
`Section5Admissibility.Stage2Group`.

**Body count after the homing, stated at the bytes rather than forecast.**  The
two rows occur as three comment-stripped bodies in `src/`: the named owner
below; conjuncts 6--7 of `ExtensionCallTwoFixedWidth` in this file, which the
projection below connects to it; and conjuncts 26--27 of
`Section5Admissibility.Stage2Group`, the frozen group's own span.  Both spans
are frozen conjunct spans of frozen bundles, which is the permitted
configuration; what `cc-t7o-r1` carried and this round removes is the fourth
body -- a *standalone* downstream copy.  The count is **still three** after
`cc-t7o-r3`: a projection adds no body.

**How the downstream span reaches this owner (`cc-t7o-r3`).**  `cc-t7o-r2` left
the group's span connected to nothing but the pole
`EffectiveCutoffCertificate.stage2Group_forces_Lh_le`, which reads conjunct
**26 only**, and justified the absence of a bridge with the claim that one
"would have to re-derive the schedule pins".  That claim is **false at the
bytes** and is withdrawn: `Stage2Group`'s conjuncts 26--27 are already written
at the schedule's own accessors, so instantiating this owner's binders at
`C.W`, `bCapOf C`, `LhOf C`, `vMaxOf C`, `epsProd C.W` reproduces them term for
term.  `Section5Admissibility.stage2Group_supplies_extensionGatesFixedWidth`
(PART A'') is that projection, and
`Section5Admissibility.stage2Group_forces_exponent_gate` is the receipt that
conjunct **27** -- reached by nothing at the `cc-t7o-r2` bytes -- is now
consumed.

**Reader counterpart: DECLINED** for every declaration in this block, and
re-swept at the bytes this round across the whole of
`routes/parameterized-np/reader-facing/` by fixed string: `all-extension`,
`v_{\max}`, `eps_{\mathrm{prod}}` and `ExtensionCallTwoFixedWidth` have **zero**
occurrences each.  The 41-page reader artifact prints no enumeration of
parameter conditions, so there is no reader item for this display and inventing
one is forbidden. -/

/-- **`eq:all-extension-gates`** (`06:941--951`; the `equation` opens at
`06:941`, the `aligned` body runs `06:943--948` and the `\label` is `06:950`),
the display-level owner, at its home module and at the frozen bundle's own
signature.

The binders are the bundle's own, in the bundle's own order and with its own
names, so the projection below is a substitution and not a translation:
`W : StageTwoWidths`, `bcap`, `Lh`, `vmax : ℕ`, `epsProd : ℝ`.  The other four
arguments of the bundle -- the two index carriers, the family and `eps2` -- do
not occur in either row, which is why the display factors out of it at all.

The frozen `>=` of the display is written as the same comparison with the sides
exchanged, exactly as the bundle prints it.  `log_2 t_2` is `W.k₂`, not a
numeral and not a recomputation: `t_2 = 2^{k_2}` is the frozen `07:278` shape of
`StageTwoRelaxed.StageTwoWidths`, and `StageTwoWidths.log_t₂` proves
`Nat.log 2 t_2 = k_2` outright.  `06:938--940` fixes what the two rows are
*about*: "every product-family application has ambient width at most
`v_max q_2`, inverse row density at most `2^{L_h}`, and balancedness error at
most `eps_prod`".

General in the width record, the two integer capacities, the ambient width
majorant and the product error. -/
def ExtensionGatesFixedWidth (W : StageTwoRelaxed.StageTwoWidths)
    (bcap Lh vmax : ℕ) (epsProd : ℝ) : Prop :=
  (Lh : ℝ) + Real.logb 2 ((vmax : ℝ) * (W.q₂ : ℝ)) + (bcap : ℝ)
      + Real.logb 2 (1 + epsProd)
      ≤ (W.t₂ : ℝ) * Real.logb 2 (5 / 3)
    ∧ (Lh : ℝ) + (W.k₂ : ℝ) + (bcap : ℝ) + Real.logb 2 (1 + epsProd)
        ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (W.k₂ : ℝ))

/-- **The pin (Aux F9a): the fixed-width bundle supplies the factored display.**

`06:1163--1166` names `eq:all-extension-gates` among the conditions the
fixed-width Localized Extension call (ii) verifies, and
`ExtensionCallTwoFixedWidth` (`:1970`) carries the two rows verbatim as its
conjuncts 6--7.  This theorem is that projection, so nothing is re-proved and
nothing is re-stated; the relation between the owner and the bundle is
kernel-checked rather than asserted in prose.

The converse does **not** hold and is not claimed: the bundle's other nine
conjuncts fix `eps_2`, `eps_prod`, the ambient-width and inverse-row-density
majorants of `06:938--940`, the two inherited column-loss inequalities and the
two balanced-family clauses, none of which follows from the two gate rows.  The
one-directional statement is therefore the honest one.

General in the two index carriers, the family, the width record, the three
integer parameters and the two errors. -/
theorem extensionCallTwoFixedWidth_supplies_extensionGates
    {Ltwo Rone : Type*} [Fintype Ltwo] [Fintype Rone] [DecidableEq Rone]
    {W : StageTwoRelaxed.StageTwoWidths}
    {cFam : Ltwo → Slot W.q₂ → Rone}
    {bcap Lh vmax : ℕ} {eps2 epsProd : ℝ}
    (h : ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd) :
    ExtensionGatesFixedWidth W bcap Lh vmax epsProd :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- **Aux F9b (statement pole: the second row is an exponential demand on the
Stage-2 exponent all by itself).**

Dropping the three nonnegative summands `L_h`, `B_cap` and
`log_2(1 + eps_prod)` from the second row leaves `log_2 t_2 <=
2^{0.49 sqrt(log_2 t_2)}`, i.e. `k_2 <= 2^{0.49 sqrt k_2}` on the record's own
exponent (`t_2 = 2^{k_2}`, `07:278`).  That comparison **fails at the exhibited
small exponent `k_2 = 5`** -- `extensionGatesFixedWidth_fails_at_balance_minimum`
refutes it there -- and holds again once `k_2` is large, which is why the display
is a gate on the schedule and not a decoration: no cardinality-free
instantiation supplies it.

**Prose repaired at `cc-t7o-r3` (Sol verify-seat finding V4; the earlier reading
"*false* for every small `k_2`" is WITHDRAWN as overbroad, matching the same
withdrawal made at `Section5Admissibility.stage2Group_forces_exponent_gate`).**
The comparison does hold at the two smallest exponents -- `k_2 = 0` gives
`0 <= 2^0 = 1` and `k_2 = 1` gives `1 <= 2^{0.49} ~ 1.404` -- and first fails at
`k_2 = 2` (`2 <= 2^{0.49 sqrt 2} ~ 1.617` is false).  Only the exhibited failure
at `k_2 = 5` is claimed here, and only it is kernel-checked.

`L_h` and `B_cap` are naturals, and
`log_2(1 + eps_prod) >= 0` needs only `eps_prod >= 0`, which
`extensionCallTwoFixedWidth_epsProd_bound` derives at the bundle from the two
`eq:epsilon-product` identities rather than assuming it.  General. -/
theorem extensionGatesFixedWidth_forces_exponent_gate
    {W : StageTwoRelaxed.StageTwoWidths} {bcap Lh vmax : ℕ} {epsProd : ℝ}
    (he : 0 ≤ epsProd) (h : ExtensionGatesFixedWidth W bcap Lh vmax epsProd) :
    (W.k₂ : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (W.k₂ : ℝ)) := by
  obtain ⟨-, hrow⟩ := h
  have hL : (0 : ℝ) ≤ (Lh : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ (bcap : ℝ) := Nat.cast_nonneg _
  have hlog : (0 : ℝ) ≤ Real.logb 2 (1 + epsProd) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  linarith

/-- **Aux F9c (the display is an upper bound on the inverse row density, and
behaves like one).**  `06:939` reads the `L_h` of both rows as the exponent of
the inverse row density `2^{L_h}`, so a schedule that meets the gates at one
`L_h` meets them at every smaller one.  This is the monotonicity sanity check
for the factored surface: it would fail outright if either row had been
transcribed with the comparison sides exchanged in only one place.  General. -/
theorem extensionGatesFixedWidth_antitone_Lh
    {W : StageTwoRelaxed.StageTwoWidths} {bcap Lh Lh' vmax : ℕ} {epsProd : ℝ}
    (hle : Lh' ≤ Lh) (h : ExtensionGatesFixedWidth W bcap Lh vmax epsProd) :
    ExtensionGatesFixedWidth W bcap Lh' vmax epsProd := by
  obtain ⟨h1, h2⟩ := h
  have hc : (Lh' : ℝ) ≤ (Lh : ℝ) := by exact_mod_cast hle
  exact ⟨by linarith, by linarith⟩

/-- **Aux F10 (the frozen `eps_prod < 1/50` is a consequence, not an extra
demand).**  The third conjunct of `ExtensionCallTwoFixedWidth` follows from its
first two at every legal width record, by `epsProd_lt_fiftieth`.  This is the
check that the bundle does not silently strengthen `eq:epsilon-product`.
General. -/
theorem extensionCallTwoFixedWidth_epsProd_bound
    (W : StageTwoRelaxed.StageTwoWidths) {eps2 epsProd : ℝ}
    (h2 : eps2 = 1 / (100 * (W.t₂ : ℝ)))
    (hp : epsProd = max ((1 + eps2) ^ W.t₂ - 1) (1 - (1 - eps2) ^ W.t₂)) :
    0 ≤ epsProd ∧ epsProd < 1 / 50 := by
  subst h2
  subst hp
  refine ⟨le_trans ?_ (le_max_left _ _), epsProd_lt_fiftieth W.t₂_pos⟩
  have h0 : (0 : ℝ) < 1 / (100 * (W.t₂ : ℝ)) := by
    have : (0 : ℝ) < (W.t₂ : ℝ) := by exact_mod_cast W.t₂_pos
    positivity
  have : (1 : ℝ) ≤ (1 + 1 / (100 * (W.t₂ : ℝ))) ^ W.t₂ :=
    one_le_pow₀ (by linarith)
  linarith

/-- **Aux F11 (the legal row range is discharged by the width record).**
`06:1164` lists "the legal row range" among the fixed-width items; at call (ii)
that is the frozen `t x <= 1` of `A:118` at `x = 2^{-b_1}`, i.e.
`t_2 <= 2^{b_1}` (`07:281`).  The banked record proves it, so the headline does
not assume it.  General in the width record. -/
theorem extensionCallTwo_row_range (W : StageTwoRelaxed.StageTwoWidths) :
    (W.t₂ : ℝ) * StageOneInterlace.xSeed W.b₁ ≤ 1 := by
  have h := W.t₂_le_two_pow_b₁
  have hR : (W.t₂ : ℝ) ≤ (2 : ℝ) ^ W.b₁ := by exact_mod_cast h
  rw [StageOneInterlace.xSeed, Real.rpow_neg (by norm_num), Real.rpow_natCast 2 W.b₁]
  rw [mul_inv_le_iff₀ (by positivity), one_mul]
  simpa using hR

/-! ## Section 7  `lem:terminal-two-stream` (`09:834--860`), stated

The frozen statement is transcribed as a named claim about the pinned
construction.  It is **not proved** in this tranche -- see GAP-EXPOSED 1 and 2
-- and no declaration below derives it.  What the sections above land is the
whole arithmetic spine its proof runs on. -/

set_option linter.dupNamespace false in
/-- **`lem:terminal-two-stream` (label `09:835`, statement `09:834--860`),
transcribed.**

"Let `Z` be an `(eps, delta')`-two-stream terminal state in the sense of
`def:two-stream-state`.  Assume `eq:terminal-entry`.  Assume also
`eq:terminal-seed-inputs`, where `S_2 = M_2^T` and `D_2 = B_cap + log_2 q_2`.
Assume also the fixed-width hypotheses of Localized Extension for the
`C_2 x C_2` product family, as listed for call (ii) in
`sec:extension-call-ledger`.  Then the state has communication complexity at
least `C`."

**Width binders (repair r2, F-1).**  The Stage-2 widths are taken as the
**banked record** `StageTwoRelaxed.StageTwoWidths`, not as a loose numeric
prefix.  That record *is* `eq:stage2-balance-ceilings` (`07:277--281`): its
four fields plus four derived telescopes carry all seven frozen width
conditions --
`t_2 = 2^{k_2}` (`t₂_eq`), `t_2 | q_2` (`t₂_dvd_q₂`), `q_2 = 2^{r_2}`
(`q₂_eq`), `16 | t_2` (`sixteen_dvd_t₂`), `4 t_2 <= q_2` (`four_t₂_le_q₂`),
`k_2 >= m_HS` (`mHS_le_k₂`), `t_2 <= 2^{b_1}` (`t₂_le_two_pow_b₁`) --
together with the balancing gate `07:398--401`.  The predecessor generation
bound only three of the seven by hand, dropping `t_2 | q_2`, `4 t_2 <= q_2`,
`k_2 >= m_HS` and `t_2 <= 2^{b_1}`; without `4 t_2 <= q_2` the Extension binder
below collapses to `True`, because at `t_2 > q_2 = 2^{r_2}` no reached capacity
`stoppingCapacity r_2 d = 2^{r_2-d}` ever meets its guard.  `m_HS` stays
symbolic: no numeral is imposed on the hard-seed threshold.

The one remaining dyadic convention `s = 2^{r_3}` (`09:1038`) stays an explicit
binder, because `r_3` is the frozen logarithm `log_2 s` and without it
`C - 1 = D_2 + log_2 s` would compare a width with an unrelated exponent.

`x_T` and `y` are **checked-identity binders**, not free reals: the frozen
schedule fixes `x_T = 2^{-b_T}` (`06:243`, restated `08:166`) and every
Localized Extension call is made at `y = 3/5` (`eq:extension-common-binders`,
`05:542`), which `09:1137` reuses as `z = y = 3/5` when it applies the certified
row ladder.  Carrying them free -- as the predecessor round did -- left
`row_density_legal` and both Stage-3 ladder instances unable to compose with
this statement at all.

The record `TwoStreamState` is consumed **by pin** as one binder; it is never
restated.  The conclusion is `comp Z >= C` at `Z = extract(U, X_Z, Y_Z)`,
`U = Interlace(N, q)`, i.e. `C <= D (subgame (interlaceFun N q) X_Z Y_Z)` in the
vendored, project-axiom-free complexity interface.

**Extension binder (repair r1).**  `09:1013--1014` invokes call (ii) exactly at
the reached isolation capacities `kappa_v = stoppingCapacity r_2 d`, and only in
the branch `kappa_v >= t_2`; the two smaller branches (`2 <= kappa_v < t_2` and
`kappa_v = 1`) are closed by the inherited two-copy/odd-copy bounds and by the
positive excess instead.  The binder below is therefore quantified over exactly
that domain.  The predecessor round instead bound `forall K, 1 <= K -> K <= 2 q_2`,
which is not a frozen quantifier at all -- `2 q_2` is the *ambient width*
`q_amb = v q_2` of `06:1120--1123` -- and at `K = 1` that bundle was
self-contradictory, so the headline was provable for arbitrary `N`, `X_Z`,
`Y_Z` with no complexity content.  `extensionCallTwo_of_widths` shows the
repaired binder is *satisfied* at the frozen dyadic widths rather than empty,
which is what `06:1161--1162` asserts; consequently this clause contributes no
strength and the statement is no weaker than the frozen one.

**Fixed-width Extension binder (repair r2, F-1).**  `09:856--858` assumes "the
fixed-width hypotheses of Localized Extension for the `C_2 x C_2` product
family, as listed for call (ii)".  The predecessor generation transcribed none
of them; they are now the explicit binder `ExtensionCallTwoFixedWidth`
(`eq:epsilon-product` `06:851--857`, the two schedule majorants `06:938--940`,
`eq:all-extension-gates` `06:941--951`, and both inherited column-loss
inequalities `eq:certified-E1`/`E2` at the call-(ii) substitution).  The legal
row range is *discharged* from the width record
(`extensionCallTwo_row_range`), and the per-call row conditions of
`06:1161--1162` remain the separate `extensionCallTwo` binder over the reached
capacities.

**The family the fixed-width binder is about (repair r3, F-4).**  The r2
generation pinned `eps_2` and `eps_prod` as numerals but attached them to no
family, so `cFam` -- the very family `def:two-stream-state` stores and
`09:857` names -- was left arbitrary, and the constant family was admissible.
`ExtensionCallTwoFixedWidth` now takes **this statement's own `cFam`** as an
argument and carries the two clauses of `06:1116--1123`: `C_2` is
`(q_2,t_2,eps_2)`-balanced, and the `C_2 x C_2` product family (ambient copy
count `2 q_2`, independence width still `t_2`) has error at most `eps_prod`.
Adding them **weakens** this statement toward `lem:terminal-two-stream`, which
is the correct direction: the r2 shape was strictly *stronger* than the frozen
lemma.  `[DecidableEq Rone]` joins the instance prefix for the same reason
`TwoStreamState` already carries `[DecidableEq Cone]` -- the vendored
`NPCC.IsBalancedFamily` counts agreement patterns over the column alphabet.
The AGHP existence axiom is **not** reached: a binder needs a model, and
`A:120--122`'s exact full product supplies one (`extProbe_fixedWidth_holds`).

The `dupNamespace` linter is disabled for this one declaration only: the module
namespace and the frozen lemma's name coincide because the file is named after
`lem:terminal-two-stream`, and renaming either would break the
one-module-per-frozen-block convention. -/
def TerminalTwoStream {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo]
    [DecidableEq Ltwo] [Fintype Rone] [DecidableEq Rone]
    (W : StageTwoRelaxed.StageTwoWidths)
    (q s mT dT bcap r₃ bT Lh vmax : ℕ) (Nmat : Rw → Cl → Bool)
    (Mmat : Cone → Rone → Bool) (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (rho : Slot s → Om → Slot W.q₂ × Cone) (YT : Slot s → Finset Cl)
    (zeta : Slot s → Cl → Ltwo) (XZ : Finset (Slot q × Rw))
    (YZ : Finset (Slot q → Cl)) (lamT eps2 epsProd xT y ε δ' : ℝ) : Prop :=
  s = 2 ^ r₃ →
    xT = DenseStageFourOpening.xTdepth bT →
    y = 3 / 5 →
    TwoStreamState.TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD omg rho
      YT zeta XZ YZ lamT eps2 xT ε δ' →
    terminalEntry W.q₂ W.b₁ ε δ' →
    terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT y →
    ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd →
    (∀ d : ℕ, d ≤ W.r₂ → W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
        extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ d)) →
    terminalTarget bcap W.r₂ r₃ ≤ D (subgame (interlaceFun Nmat q) XZ YZ)

/-! ## Section 8  Statement poles

A green build sees neither of the two failure modes these record. -/

/-- **Statement pole 1 (`CertifiedRowLadder` is not free).**  The predicate is
not vacuously true: at `H = 1`, `x = 1/2`, `z = 1` and a matrix whose
`Lambda` at every rung is `0`, the `ell = 1` instance demands `2 <= 0`.  So
carrying `lem:certified-row-ladder` as a hypothesis genuinely defers content
rather than smuggling a triviality, and the two instances above are not
provable without it.

The witness is the one-by-one all-`false` matrix on `Unit x Unit`: its
`bracketGE` families at copy count `2` contain the pair `(univ, univ)`, whose
subgame is a constant function and therefore has `D = 0`, so `Dfamily = 0` and
`LambdaGE = 0`. -/
theorem certifiedRowLadder_is_not_free :
    ¬ CertifiedRowLadder (fun _ _ : Unit => false) 1 (1 / 2) 1 := by
  classical
  have hzeroD : ∀ (p : ℕ) (R : Finset (Fin p × Unit)) (C : Finset (Fin p → Unit)),
      D (subgame (interlaceFun (fun _ _ : Unit => false) p) R C) = 0 := by
    intro p R C
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    exact Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.leaf false, rfl, by intro a b; rfl⟩
  have hD : ∀ (p : ℕ) (x y : ℝ), x ≤ 1 → y ≤ 1 →
      Dfamily (interlaceFun (fun _ _ : Unit => false) p) (bracketGE Unit Unit p x y) = 0 := by
    intro p x y hx hy
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    refine Nat.sInf_le ⟨(Finset.univ, Finset.univ), ?_, (hzeroD p _ _).symm⟩
    exact bracketGE.anti_mono_params p hx hy (bracketGE.self_mem p)
  intro h
  have hlegal : (2 : ℝ) ^ (1 : ℕ) * (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hinst := h 1 le_rfl hlegal
  have hzero : LambdaGE (fun _ _ : Unit => false) (2 ^ (1 - 1) + 1)
      ((2 : ℝ) ^ (1 : ℕ) * (1 / 2 : ℝ)) ((1 : ℝ) ^ 2) = 0 := by
    unfold LambdaGE
    rw [hD _ _ _ (by norm_num) (by norm_num), hD _ _ _ (by norm_num) (by norm_num),
      hD _ _ _ (by norm_num) (by norm_num)]
    simp
  rw [hzero] at hinst
  omega

/-- **Statement pole 2 (the frozen conclusion is not automatic).**  For any
existential-free deliverable the pole is the trivial bound.  Here the frozen
conclusion is `C <= comp Z` with `C = D_2 + log_2 s + 1 >= 1`, and `comp` of a
constant subgame is `0`; so the conclusion fails on a constant matrix and is
therefore not a consequence of the ambient shape alone.  Any restatement that
weakened `C` to `0` would be exactly this triviality. -/
theorem terminalTwoStream_is_not_trivial (bcap r₂ r₃ : ℕ) :
    ¬ (terminalTarget bcap r₂ r₃
        ≤ D (subgame (fun _ _ : Unit => false) (Finset.univ : Finset Unit)
              (Finset.univ : Finset Unit))) := by
  have hzero : D (subgame (fun _ _ : Unit => false) (Finset.univ : Finset Unit)
      (Finset.univ : Finset Unit)) = 0 := by
    apply Nat.le_antisymm _ (Nat.zero_le _)
    exact Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.leaf false, rfl, by intro a b; rfl⟩
  rw [hzero]
  have := terminalTarget_pos bcap r₂ r₃
  omega

/-- **Statement pole 3 (the predecessor binder was refutable -- preserved
witness).**  The shape the previous round bound, `forall K, 1 <= K -> K <= 2 q_2`
applied to a predicate carrying both `t_2 | K` and `16 | t_2`, is
*self-contradictory*: instantiating at `K = 1` forces `t_2 = 1`, which `16 | t_2`
refutes.  A headline with that hypothesis was therefore provable for arbitrary
matrices and carriers, touching no complexity content.  The refuted shape is
recorded here as an exact machine-checked witness rather than deleted, per the
repository's failed-route discipline.  General. -/
theorem legacy_extension_binder_is_self_contradictory {q₂ t₂ : ℕ}
    (h16 : 16 ∣ t₂) (hq : 1 ≤ 2 * q₂)
    (hlegacy : ∀ K : ℕ, 1 ≤ K → K ≤ 2 * q₂ → t₂ ∣ K) : False := by
  have hone : t₂ ∣ 1 := hlegacy 1 le_rfl hq
  have ht1 : t₂ = 1 := Nat.dvd_one.1 hone
  subst ht1
  have := Nat.le_of_dvd (by norm_num) h16
  omega

/-- **Statement pole 4 (the repaired binder is not reachable at unit capacity,
so the countermodel above no longer discharges).**  Under the frozen width
binders `t_2 = 2^{k_2}` and `16 | t_2`, the guard `t_2 <= stoppingCapacity r_2 d`
of the repaired Extension binder can only fire at capacities of at least `16`,
hence never at `kappa_v = 1` and never at `kappa_v < t_2`; and it forces
`d + 4 <= r_2`, i.e. the depth is at least four rungs above the Stage-2
frontier.  This is exactly the frozen branch condition `kappa_v >= t_2` of
`09:1013`, and it is what makes `legacy_extension_binder_is_self_contradictory`
inapplicable to the repaired headline.  General. -/
theorem repaired_extension_binder_avoids_unit_capacity {t₂ k₂ r₂ d : ℕ}
    (hdy : t₂ = 2 ^ k₂) (h16 : 16 ∣ t₂)
    (hguard : t₂ ≤ DenseWeightedCount.stoppingCapacity r₂ d) :
    16 ≤ DenseWeightedCount.stoppingCapacity r₂ d ∧ d + 4 ≤ r₂ := by
  have hk : 4 ≤ k₂ := extensionWidth_four_le hdy h16
  have ht16 : 16 ≤ t₂ := by
    subst hdy
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by norm_num) hk
  refine ⟨le_trans ht16 hguard, ?_⟩
  subst hdy
  simp only [DenseWeightedCount.stoppingCapacity_eq] at hguard
  have := (Nat.pow_le_pow_iff_right (by norm_num)).1 hguard
  omega

/-- **Statement pole 5 (the repaired binder is not a disguised falsehood
either).**  The complementary check: at legal widths the guard *does* fire, so
`repaired_extension_binder_avoids_unit_capacity` is not vacuously true by an
empty domain.  General in the width record, at the Stage-2 root depth `d = 0`,
where `stoppingCapacity r_2 0 = q_2` and `t_2 <= q_2` is the frozen
`4 t_2 <= q_2`. -/
theorem repaired_extension_binder_domain_is_inhabited
    (W : StageTwoRelaxed.StageTwoWidths) :
    W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ 0 := by
  simp only [DenseWeightedCount.stoppingCapacity_eq, Nat.sub_zero,
    StageTwoRelaxed.StageTwoWidths.t₂]
  exact Nat.pow_le_pow_right (by norm_num) W.k₂_le_r₂

/-! ## Section 9  LANE-GATE 3: a nondegenerate inhabitant at the relaxed
carrier's four proof fields

*WITHDRAWN at `cc-t7p` (ledger item `(b11)`).*  This header previously read
"a nondegenerate inhabitant at legal values", and claimed that every predicate
below is "inhabited at *schedule-checked* values -- never at values the frozen
schedule forbids".  Both sentences are **false**, of both probe records, and
they are withdrawn here rather than quietly edited.  `eq:t2-search`
(`06:763--770`) fixes `k_2` as the least integer with
`k_2 >= max{4, 2^{19}, m_HS}` (`06:766`), and `2^{19} = 524288`, whereas
`probeWidths.k_2 = 5` and `extProbeWidths.k_2 = 576`.  Both records therefore
sit at exactly the kind of value the frozen schedule forbids.

What is true, and all that is claimed below: every predicate introduced above
is inhabited at values satisfying the **four proof fields** of
`StageTwoRelaxed.StageTwoWidths` (`07:281` with `D:496`, `07:280`,
`07:398--401`) -- never at a degenerate width.  Schedule legality is neither
claimed nor established at either record; the residual unqualified "legal"
sentences elsewhere in the route are registered, not discharged, under ledger
item `(b14)`. -/

/-- A `StageTwoWidths` record at the smallest values that carrier's **four
proof fields** permit: `k_2 = 5` (the `5 <= m_HS <= k_2` chain of `D:496` and
`07:281`), `r_2 = 7` (so `q_2 = 128`, the least dyadic width with
`4 t_2 <= q_2`, `07:280`), and `b_1 = 24` (the least exponent with
`131072 * 128 <= 2^{b_1}`, `07:398--401`).  Nothing here is a degenerate choice
*for those four gates*: all three widths are their minima.

**Scope, stated at `cc-t7p` (the sweep round; the unqualified "the frozen
minima" reading is WITHDRAWN).**  These are the minima of the **relaxed**
Lean carrier, not of the frozen schedule.  `eq:t2-search` (`06:763--770`) fixes
`k_2` as the least integer with `k_2 >= max{4, 2^{19}, m_HS}` (`06:766`) and
`t_2 = 2^{k_2}` (`06:770`), and `2^{19} = 524288 > 5`, so this record sits far
below the scheduled `k_2` and is not a legal schedule width.  That is why
`Section5Admissibility.stage2Group_refuted_at_balance_minimum` can refute the
fourth admissibility group at it outright, and why nothing here is offered as a
witness at the paper's parameter values.

**Census status, written at `cc-t7q-r2` after both repair rounds (ledger item
`(b14)`).**  The banked prose that still called this record "legal" without that
qualification was the ten-site census the `cc-t7p` verify seat corrected to ten
(finding F-8).  The ten sites are repaired across **two** rounds, not one.
`cc-t7q` attempted all ten; its judge CLEARed nine and returned site (10), the
`TwoStreamState.lean` Section 7 header, REVISE (finding F-1), because that
repair's own new denial ("Nothing about the probe below is a legality claim")
contradicted the proved gate-scoped `TwoStreamState.probeState_is_legal`.  That
round was therefore parked and never banked.  Site (10) is repaired at
`cc-t7q-r2`, the round that also withdraws this sentence's predecessor, "All ten
are repaired this round", which was premature when it was written.  Each repair
sits in the file that carried it and each is written as a withdrawal rather than
an edit-in-silence: `Stage3ProtocolRouting.lean` (2),
`TerminalStageThreeLift.lean` (2), `TerminalFixedBin.lean` (2),
`TerminalCertificateInputs.lean` (2), `OwnerMassTransfer.lean` (1) and
`TwoStreamState.lean` (1, the header, repaired at `cc-t7q` and again at
`cc-t7q-r2`).  Every repair is comment prose; **no statement, hypothesis,
conclusion or proof term is touched by any of it**, and nothing that was open is
discharged: canonical inhabitation of the call-(ii) bundle stays REGISTERED and
DEFERRED under `S5-CUTOFF-ITEMS-DEFERRED` / `S5-LEVEL-STEP` exactly as before.
Removing a false legality claim discharges no mathematics. -/
def probeWidths : StageTwoRelaxed.StageTwoWidths where
  k₂ := 5
  r₂ := 7
  b₁ := 24
  mHS := 5
  five_le_mHS := le_rfl
  mHS_le_k₂ := le_rfl
  four_t₂_le_q₂ := by norm_num
  depth_gate := by norm_num

/-- **Non-vacuity 1 (dyadic readout; RENAMED at `cc-t7p` from
`probeWidths_are_legal`, which over-suggested schedule legality).**

Exactly three facts, all read off the record: `q_2 = 2^{r_2} = 128`,
`t_2 = 2^{k_2} = 32`, and the structural outer-width floor `16 <= q_2` that
`09:1671` reads off the structural gates and that `terminalEntry`'s first clause
demands.

**What this does NOT say.**  It does not say `probeWidths` is a legal *schedule*
width record, and the withdrawn name did: `probeWidths.k₂ = 5` fails the
`eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}` (`06:766`), reified
independently in this repository as `ParameterSchedule.k2Floor`.  The three
conjuncts below are unaffected by that -- they are readouts, not gates. -/
theorem probeWidths_dyadic_readout :
    probeWidths.q₂ = 128 ∧ probeWidths.t₂ = 32 ∧ 16 ≤ probeWidths.q₂ := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Non-vacuity 2 (`eq:terminal-entry` fires).**  All three clauses hold at
the probe widths with `eps = 0`, `delta' = 1`. -/
theorem probeEntry_holds : terminalEntry probeWidths.q₂ probeWidths.b₁ 0 1 :=
  terminalEntry_is_satisfiable probeWidths

/-- **Non-vacuity 3a.**  The probe root threshold is the exact frozen value
`lambda_0 = 2 q_2 2^{-b_1} = 256/2^24 = 1/65536`, comfortably inside the
`eq:terminal-entry` bound `1/8` and strictly positive -- so the inhabitant is
not a `lambda_0 = 0` degeneracy. -/
theorem probeLambdaZero :
    DenseBranchSelection.lambdaZero probeWidths.q₂ probeWidths.b₁ = 1 / 65536 := by
  have hq : probeWidths.q₂ = 128 := by decide
  have hb : probeWidths.b₁ = 24 := rfl
  rw [DenseBranchSelection.lambdaZero, hq, hb]
  norm_num

/-- **Non-vacuity 3 (the entry conditions are not met at the boundary only).**
`eq:terminal-entry` still fires at a *positive* `eps` and a `delta'` strictly
below `1`, so the inhabitant above is not the degenerate corner of the regime:
`eps = 1/100` and `delta' = 1/10` are legal **for `eq:terminal-entry`**, and
`eps < 1/5` follows, exactly
as `09:913--914` requires.  That scalar legality says nothing about the width
record carrying it: `probeWidths` is **not** a legal schedule width record
(`k_2 = 5` against the `eq:t2-search` floor `06:766`).  (Qualification added at
`cc-t7q` alongside ledger item `(b14)`; this site is a *scalar*-legality use, a
different class from the ten `(b14)` sites, and is disclosed rather than counted
among them.) -/
theorem probeEntry_is_nondegenerate :
    terminalEntry probeWidths.q₂ probeWidths.b₁ (1 / 100) (1 / 10)
      ∧ (1 : ℝ) / 100 < 1 / 5 := by
  have hq : probeWidths.q₂ = 128 := by decide
  refine ⟨⟨by rw [hq]; norm_num, ?_, ?_⟩, by norm_num⟩
  · rw [probeLambdaZero]; norm_num
  · rw [probeLambdaZero, hq]; norm_num

/-- **HYPOTHESIS-CONSISTENCY 1 (the dyadic binder makes the entry conditions
bite).**  With the frozen `q_2 = 2^{r_2}`, `eq:terminal-entry`'s first clause
forces `r_2 >= 4`, hence `D_2 >= 4 >= 2`: the scale guard of `09:1148--1149` is
a *consequence* of the entry conditions, not an extra assumption, and no
instance of the lemma sits at an exponent where `lem:certified-row-ladder` would
be inapplicable.  This is the check that `r_2` really means `log_2 q_2`: without
the dyadic binder the same statement would be unprovable, since `r_2` could be
`0` at `q_2 = 16`.  General. -/
theorem terminalEntry_forces_scale_guard {q₂ b₁ r₂ bcap : ℕ} {ε δ' : ℝ}
    (hdy : q₂ = 2 ^ r₂) (h : terminalEntry q₂ b₁ ε δ') :
    4 ≤ r₂ ∧ 2 ≤ DenseBranchSelection.Dtwo bcap r₂ := by
  obtain ⟨h16, _, _⟩ := h
  subst hdy
  have hr : 4 ≤ r₂ := by
    by_contra hcon
    have hlt : r₂ < 4 := Nat.lt_of_not_le hcon
    have : (2 : ℕ) ^ r₂ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨hr, scale_guard bcap r₂ (by omega)⟩

/-- **HYPOTHESIS-CONSISTENCY 2 (the banked inhabitants are *outside* this
lemma's regime, and that is a finding, not a defect).**  The banked
`TwoStreamState.probeState` and `TerminalStateRealization.schedState` both live
at the Stage-2 outer width `q_2 = 2`, which `eq:terminal-entry` rejects: no
choice of `b_1`, `eps`, `delta'` makes `terminalEntry 2 b_1 eps delta'` true.
So the terminal lemma quantifies over a strictly narrower regime than
`def:two-stream-state`, exactly as `09:838--844` intends, and the fact that the
record is inhabited is *not* by itself evidence that this lemma's hypothesis
bundle is inhabited.  General. -/
theorem bankedProbeWidth_is_not_a_terminal_entry_width (b₁ : ℕ) (ε δ' : ℝ) :
    ¬ terminalEntry 2 b₁ ε δ' := by
  rintro ⟨h16, -, -⟩
  omega

/-! ### The Stage-3 probe scalars

The headline's remaining binders are the Stage-3 exponent `r_3 = log_2 s`, the
Stage-3 depth `b_T`, and the two pinned reals.  The probe takes `r_3 = 3` (so
`s = 8`) and `b_T = 8`, which satisfies the frozen third clause of
`eq:terminal-seed-inputs`, `log_2 s < b_T`, with room to spare, and leaves
`r_3 - d >= 2` available at `d = 0` and `d = 1` so that the odd-copy ladder
instance is reached at a *non*-boundary capacity. -/

/-- Probe Stage-3 exponent `r_3 = 3`, i.e. `s = 8`. -/
def probeR₃ : ℕ := 3

/-- Probe Stage-3 depth `b_T = 8`; `log_2 s = 3 < 8`. -/
def probeBT : ℕ := 8

/-- Probe row scale, at the frozen identity `x_T = 2^{-b_T}` (`06:243`,
`08:166`).  Not a free real. -/
noncomputable def probeXT : ℝ := DenseStageFourOpening.xTdepth probeBT

/-- Probe column scale, at the frozen `y = 3/5` (`05:542`, `09:1137`). -/
noncomputable def probeY : ℝ := 3 / 5

/-- **Non-vacuity 4 (the repaired Extension binder has a nonempty domain).**
At the probe widths the guard `t_2 <= stoppingCapacity r_2 d` of the headline's
Extension binder is *met* at `d = 0, 1, 2` -- capacities `128, 64, 32`, all at
least `t_2 = 32` -- so the binder is a genuine hypothesis about genuinely
reached capacities rather than a vacuous quantification.  At `d = 3` the guard
first fails (capacity `16 < 32`), which is precisely the frozen branch
`2 <= kappa_v < t_2` that `09:1015--1016` closes by the inherited two-copy and
odd-copy bounds instead of by call (ii). -/
theorem probeExtensionDomain_nonempty :
    DenseWeightedCount.stoppingCapacity probeWidths.r₂ 0 = 128
      ∧ DenseWeightedCount.stoppingCapacity probeWidths.r₂ 2 = 32
      ∧ probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ 2
      ∧ ¬ probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ 3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Non-vacuity 5 (Extension call (ii) fires at every reached capacity).**
The repaired `forall`-form binder itself, discharged at the probe widths through
`extensionCallTwo_of_widths`.  The predecessor round exhibited only the
*pointwise* instance at `K = 32` while the headline bound a `forall`, so its
consistency claim did not describe the statement it accompanied. -/
theorem probeExtensionCallTwo :
    ∀ d : ℕ, d ≤ probeWidths.r₂ →
      probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ d →
      extensionCallTwo probeWidths.q₂ probeWidths.t₂
        (DenseWeightedCount.stoppingCapacity probeWidths.r₂ d) := by
  intro d _ hd
  exact extensionCallTwo_of_widths (StageTwoRelaxed.StageTwoWidths.q₂_eq probeWidths)
    (StageTwoRelaxed.StageTwoWidths.t₂_eq probeWidths) hd

/-- **Non-vacuity 6 (the block-count readout survives the split).**  With the
two width facts now supplied separately, `06:1126--1130`'s exact output-size
equation still holds at a reached probe capacity: `|Q_s| = r' p_seed = 9K/16`
at `K = 32`, `t_2 = 32`, giving `1 * 18 = 18`. -/
theorem probeExtensionCallTwo_block_count :
    (DenseWeightedCount.stoppingCapacity probeWidths.r₂ 2 / probeWidths.t₂)
        * (9 * probeWidths.t₂ / 16)
      = 9 * DenseWeightedCount.stoppingCapacity probeWidths.r₂ 2 / 16 := by
  refine extensionCallTwo_block_count (q₂ := probeWidths.q₂) probeWidths.t₂_pos
    probeWidths.sixteen_dvd_t₂ ?_
  exact probeExtensionCallTwo 2 (by decide) (by decide)

/-- **HYPOTHESIS-CONSISTENCY 3 (the repaired bundle, at the `forall`-form the
headline actually binds).**

This lemma exhibits, simultaneously and at one set of values, **every** binder
of `TerminalTwoStream` except the banked `TwoStreamState` record and the two
inherited `Lambda` certificates of `eq:terminal-seed-inputs`:

* the three dyadic conventions `q_2 = 2^{r_2}`, `s = 2^{r_3}`, `t_2 = 2^{k_2}`;
* the frozen width condition `16 | t_2`;
* the two checked-identity pins `x_T = 2^{-b_T}` and `y = 3/5`;
* `eq:terminal-entry` at a nondegenerate `eps = 1/100`, `delta' = 1/10`;
* the third clause `log_2 s < b_T` of `eq:terminal-seed-inputs`;
* the Extension binder **in its `forall` form**, universally quantified over the
  reached capacities exactly as the headline states it.

The docstring is truthful about what this does and does not establish.  It does
*not* claim the two `Lambda` certificates are simultaneously realizable -- they
are inherited Stage-1 and Stage-2 hardness inputs (`09:847`, `09:849`) about two
different matrices, carried as two separate certificates and never conjoined as
cases of one construction.  What it does establish is that no *arithmetic*
sub-collection of the headline's binders is contradictory, so a derivation of
`False` from them cannot go through; the accompanying scratch probe, which
attempts exactly that derivation, does not typecheck.

The predecessor round's version of this lemma asserted the same thing while
listing the pointwise `extensionCallTwo ... 32`, i.e. it did not mention the
quantifier that carried the defect; that is the specific untruth this
restatement removes. -/
theorem terminalTwoStream_arith_hypotheses_consistent :
    probeWidths.q₂ = 2 ^ probeWidths.r₂
      ∧ (8 : ℕ) = 2 ^ probeR₃
      ∧ probeWidths.t₂ = 2 ^ probeWidths.k₂
      ∧ 16 ∣ probeWidths.t₂
      ∧ probeXT = DenseStageFourOpening.xTdepth probeBT
      ∧ probeY = 3 / 5
      ∧ terminalEntry probeWidths.q₂ probeWidths.b₁ (1 / 100) (1 / 10)
      ∧ probeR₃ < probeBT
      ∧ (∀ d : ℕ, d ≤ probeWidths.r₂ →
          probeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity probeWidths.r₂ d →
          extensionCallTwo probeWidths.q₂ probeWidths.t₂
            (DenseWeightedCount.stoppingCapacity probeWidths.r₂ d)) := by
  refine ⟨StageTwoRelaxed.StageTwoWidths.q₂_eq probeWidths, by decide,
    StageTwoRelaxed.StageTwoWidths.t₂_eq probeWidths, probeWidths.sixteen_dvd_t₂,
    rfl, rfl, probeEntry_is_nondegenerate.1, by decide, probeExtensionCallTwo⟩

/-- **HYPOTHESIS-CONSISTENCY 4 (the pinned scalars clear the ladder's
row-density guard, and are not degenerate).**
At the probe pins the two Stage-3 row densities the ladder requests are legal
**for that guard** (the banked `row_density_legal` sense) --
`2 x_T <= 1` for the `ell = 1` instance and `2^{r_3-d} x_T <= 1` for the
odd-copy instance at every depth -- and `x_T` is strictly positive, so the pin
is not the degenerate `x_T = 0` that would make every row-density guard hold
vacuously.  No schedule legality is claimed here for anything, the width record
included.  (Qualification added at `cc-t7q` alongside ledger item `(b14)`; a
*scalar*-legality use, disclosed rather than counted among the ten.) -/
theorem probePins_are_nondegenerate :
    0 < probeXT ∧ 2 * probeXT ≤ 1
      ∧ (2 : ℝ) ^ (probeR₃ - 0) * probeXT ≤ 1
      ∧ probeXT = 1 / 256 := by
  have hx : probeXT = 1 / 256 := by
    rw [probeXT, DenseStageFourOpening.xTdepth, probeBT]
    norm_num
  refine ⟨by rw [hx]; norm_num, ?_, ?_, hx⟩
  · exact two_xT_le_one (bT := probeBT) rfl (by decide)
  · exact (row_density_legal_at_capacity (r₃ := probeR₃) (d := 0) (bT := probeBT)
      rfl (by decide)).2

/-! ### The call-(ii) probe (repair r2, F-1): a width record at which the
*fixed-width* Extension hypotheses fire

`probeWidths` above is the smallest record the balance gates permit, and it is
the right witness for `eq:terminal-entry` and for the reached-capacity domain of
the Extension binder.  It is deliberately **not** offered as a witness for
`ExtensionCallTwoFixedWidth`: `eq:all-extension-gates` (`06:946--948`) demands
`2^{0.49 sqrt(log_2 t_2)} >= L_h + log_2 t_2 + B_cap + log_2(1+eps_prod)`, and at
`t_2 = 32` the left side is below `3` while the right side is at least
`b_1 >= 24`.  That is a finding about the *schedule*, not a defect in either
side: the frozen `t_2` is far above the balance minimum because `eq:t2-search`
(`06:763--770`) fixes `k_2 >= max{4, 2^{19}, m_HS}` at `06:766` and
`t_2 = 2^{k_2}` at `06:770`.

**Repaired at `cc-t7p` (ledger item `(b11)`; two withdrawals).**  (1) The
predecessor sentence here appealed to `eq:t2-growth` (`06:820--824`) and to
`t_2 >= t_cert` (`A:117`) for that lower bound; both appeals are WITHDRAWN --
`eq:t2-growth` is an asymptotic **upper** growth statement and `A:117` is an
additional call-site premise, exactly as
`Section5Admissibility.stage2Group_refuted_at_balance_minimum` already records.
`eq:t2-search` is the correct and only lower bound cited.  (2) The predecessor
sentence "the record below is the LANE-GATE 3 inhabitant at a width where every
frozen gate fires at once, so the new binder is inhabited at legal -- not
degenerate -- parameter values" is WITHDRAWN as false.  The record below fires
`eq:all-extension-gates` and the two inherited column-loss substitutions, which
is why it is useful here, but it does **not** fire every frozen gate: its own
`k_2 = 576` is below the `06:766` floor `2^{19} = 524288`.  It is a
**BEYOND-PAPER** record, its binder is inhabited at *nondegenerate* values of
the relaxed carrier and at no legal schedule value, and canonical inhabitation
of the call-(ii) bundle stays REGISTERED and DEFERRED under
`S5-CUTOFF-ITEMS-DEFERRED` / `S5-LEVEL-STEP`. -/

/-- **BEYOND-PAPER AUDIT record (relabelled at `cc-t7p`, ledger item `(b11)`;
the `cc-t7o-r2` reading "a legal Stage-2 width record inside the **certified**
regime" is WITHDRAWN).**

*The violation, stated first.*  `eq:t2-search` (`06:763--770`) fixes `k_2` as
the least integer satisfying a list whose first row (`06:766`) is
`k_2 >= max{4, 2^{19}, m_HS}`.  Here `k_2 = 576` and `2^{19} = 524288`, so the
record **fails the frozen floor** by a factor of about `910`; this repository's
own reification agrees independently, `ParameterSchedule.k2Floor` being
`max (max 4 (2 ^ 19)) mHS` and the first conjunct of
`ParameterSchedule.K2Pred` being `k2Floor <= k`.  So this is **not** a legal
schedule width record, and no statement instantiated at it is evidence about
the paper's construction.

*What the fields are, and in what sense they are minimal.*  `k_2 = 576` is a
perfect square, so the frozen exponent `0.49 sqrt(log_2 t_2)` is exactly
`11.76`; `r_2 = 578` is the least dyadic width with `4 t_2 <= q_2` (`07:280`);
`b_1 = 595` is the least exponent with `131072 q_2 <= 2^{b_1}` (`07:398--401`);
and `m_HS = 5` is the floor of the inherited tail predicate `HSThreshold`
(`D:496`), left symbolic in the record's own statement.  **Given `k_2`**, every
other field is minimal *for the four proof fields of the relaxed carrier* --
which is the whole of the minimality claim, and is not minimality against the
schedule.

*What it is for.*  The record fires `eq:all-extension-gates` (`06:941--951`)
-- which the balance-minimum record `probeWidths` provably does **not**, by
`extensionGatesFixedWidth_fails_at_balance_minimum` -- together with the two
inherited column-loss substitutions; call the widths at which
`eq:all-extension-gates` holds the **gate-firing** regime.  Gate-firing is a
fact about our encoding, not about legality, and canonical inhabitation of the
call-(ii) bundle stays REGISTERED and DEFERRED under
`S5-CUTOFF-ITEMS-DEFERRED` / `S5-LEVEL-STEP` -- the paper's own instance is
the schedule `Compile(c)` emits, behind unbuilt machinery. -/
def extProbeWidths : StageTwoRelaxed.StageTwoWidths where
  k₂ := 576
  r₂ := 578
  b₁ := 595
  mHS := 5
  five_le_mHS := le_rfl
  mHS_le_k₂ := by norm_num
  four_t₂_le_q₂ := by
    refine le_of_eq ?_
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  depth_gate := by
    refine le_of_eq ?_
    rw [show (131072 : ℕ) = 2 ^ 17 by norm_num, ← pow_add]

/-- The frozen Stage-2 balancedness error at the call-(ii) probe,
`eps_2 = 1/(100 t_2)` (`06:852`).  Not a free real. -/
noncomputable def extProbeEps2 : ℝ := 1 / (100 * (extProbeWidths.t₂ : ℝ))

/-- The frozen product balancedness error at the call-(ii) probe
(`06:854--856`).  Not a free real. -/
noncomputable def extProbeEpsProd : ℝ :=
  max ((1 + extProbeEps2) ^ extProbeWidths.t₂ - 1)
    (1 - (1 - extProbeEps2) ^ extProbeWidths.t₂)

/-- **Non-vacuity 7 (the probe error is in the frozen range).**  `eps_prod` is
nonnegative and strictly below `1/50`, by the proved `epsProd_lt_fiftieth`. -/
theorem extProbeEpsProd_range : 0 ≤ extProbeEpsProd ∧ extProbeEpsProd < 1 / 50 :=
  extensionCallTwoFixedWidth_epsProd_bound extProbeWidths rfl rfl

/-- **Aux F12 (the column-bit factor is at most one bit).**  `log_2(1+eps_prod)`
never exceeds `1` in the frozen range, so the two gates of
`eq:all-extension-gates` may be discharged against an explicit integer
majorant. -/
theorem logb_one_add_epsProd_le_one : Real.logb 2 (1 + extProbeEpsProd) ≤ 1 := by
  obtain ⟨h0, h50⟩ := extProbeEpsProd_range
  have hle : (1 : ℝ) + extProbeEpsProd ≤ 2 := by linarith
  have hmono : Real.logb 2 (1 + extProbeEpsProd) ≤ Real.logb 2 2 :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hle
  simpa [Real.logb_self_eq_one] using hmono

/-- **Aux F13 (`log_2(5/3) >= 1/2`).**  The frozen gate `06:943--945` is stated
with the irrational `log_2(5/3)`; the only property used below is the rational
comparison `(5/3)^2 = 25/9 >= 2`.  General arithmetic. -/
theorem half_le_logb_five_thirds : (1 : ℝ) / 2 ≤ Real.logb 2 (5 / 3) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : Real.log ((5 : ℝ) / 3 * (5 / 3)) = 2 * Real.log (5 / 3) := by
    rw [Real.log_mul (by norm_num) (by norm_num)]; ring
  have hmono : Real.log 2 ≤ Real.log ((5 : ℝ) / 3 * (5 / 3)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [hsq] at hmono
  rw [Real.logb, le_div_iff₀ hlog2]
  linarith

/-- **Aux F14 (`2^{0.49 sqrt(log_2 t_2)} >= 2048` at the call-(ii) probe
record).**
`k_2 = 576` is a perfect square, so `sqrt(log_2 t_2) = 24` exactly and the
frozen left side of `eq:all-extension-gates`' second line is `2^{11.76}`, which
exceeds `2^{11}`.  Recorded on its own because both `eq:all-extension-gates`
and `eq:certified-E2` consume it. -/
theorem twoPow_certified_exponent_ge :
    (2048 : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * (24 : ℝ)) := by
  have hexp : (2 : ℝ) ^ ((11 : ℝ)) = 2048 := by
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hmono : (2 : ℝ) ^ ((11 : ℝ)) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * (24 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [hexp] at hmono
  exact hmono

/-- **Aux F15 (the exact square root of the probe exponent).** -/
theorem extProbe_sqrt_k₂ : Real.sqrt ((extProbeWidths.k₂ : ℕ) : ℝ) = 24 := by
  have h : ((extProbeWidths.k₂ : ℕ) : ℝ) = (24 : ℝ) ^ 2 := by
    change (((576 : ℕ)) : ℝ) = (24 : ℝ) ^ 2
    norm_num
  rw [h]
  exact Real.sqrt_sq (by norm_num)

/-- **Aux F16 (the probe widths in real power form).** -/
theorem extProbe_casts :
    ((extProbeWidths.q₂ : ℕ) : ℝ) = (2 : ℝ) ^ (578 : ℕ)
      ∧ ((extProbeWidths.t₂ : ℕ) : ℝ) = (2 : ℝ) ^ (576 : ℕ) := by
  constructor
  · change (((2 : ℕ) ^ (578 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ (578 : ℕ)
    push_cast
    ring
  · change (((2 : ℕ) ^ (576 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ (576 : ℕ)
    push_cast
    ring

/-- **Aux F17 (the right side of `eq:all-extension-gates`' first line at the
call-(ii) probe record).**  `t_2 log_2(5/3) >= 4096/2 = 2048`, from `t_2 >= 2^{12}` and
`log_2(5/3) >= 1/2`.  Kept separate so that the enormous dyadic width never
enters a linear-arithmetic context. -/
theorem extProbe_gate_one_rhs :
    (2048 : ℝ) ≤ ((extProbeWidths.t₂ : ℕ) : ℝ) * Real.logb 2 (5 / 3) := by
  have hbig : (4096 : ℝ) ≤ ((extProbeWidths.t₂ : ℕ) : ℝ) := by
    have h : ((extProbeWidths.t₂ : ℕ) : ℝ) = (2 : ℝ) ^ (576 : ℕ) := extProbe_casts.2
    rw [h]
    calc (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (576 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hmul : (4096 : ℝ) * (1 / 2)
      ≤ ((extProbeWidths.t₂ : ℕ) : ℝ) * Real.logb 2 (5 / 3) :=
    mul_le_mul hbig half_le_logb_five_thirds (by norm_num) (Nat.cast_nonneg _)
  linarith

/-! #### The LANE-GATE 3 family for the two balancedness fields (repair r3)

`A:120--122` permits `M^` to be formed "from the exact full product, in which
case `eps = 0`", so the frozen source itself supplies a model for the two new
fields.  The probe takes the column alphabet to be `Bool` -- **two** letters, so
`def:balanced-family` has genuine content here, unlike at a one-point alphabet
where every family is exactly balanced for trivial reasons -- and the index
carrier to be *all* ambient `q_2`-tuples, with `C_2` the tautological
enumeration.  Nothing about this is degenerate: `q_2 = 2^{578}` is the
gate-firing regime's ambient width and `t_2 = 2^{576}` its independence width,
both carried by `extProbeWidths` -- which is a fact about our encoding, not a
legality claim (`extProbeWidths` fails the `06:766` floor; see `(b11)`). -/

/-- The exact full-product index carrier at the call-(ii) probe record: every ambient
`q_2`-tuple over the two-letter column alphabet, exactly once. -/
abbrev extProbeColumns : Type := Slot extProbeWidths.q₂ → Bool

/-- The exact full product as a physical family (`A:120--122`). -/
def extProbeFamily : extProbeColumns → Slot extProbeWidths.q₂ → Bool := fun s => s

/-- **Non-vacuity 7b (the probe family enumerates the ambient tuples exactly
once).**  This is what makes it "the exact full product" rather than an
arbitrary list. -/
theorem extProbeFamily_bijective :
    Function.Bijective (familyOnIndices extProbeFamily) :=
  familyOnIndices_bijective Function.bijective_id

/-- **Non-vacuity 7c (the probe family is exactly balanced).**  `eps = 0` at
every independence width, by `A:120--122` as proved in
`isBalancedFamily_zero_of_bijective`. -/
theorem extProbeFamily_isBalanced (t : ℕ) :
    IsBalancedFamily t (familyOnIndices extProbeFamily) 0 :=
  isBalancedFamily_zero_of_bijective t (by simp) extProbeFamily_bijective

/-- **Non-vacuity 7d (the `C_2 x C_2` product family is exactly balanced too).**
The `2`-fold Cartesian product of the exact full product is again an exact full
product, now at ambient copy count `q_amb = 2 q_2` and the **same** independence
width. -/
theorem extProbeFamily_prod_isBalanced (t : ℕ) :
    IsBalancedFamily t (productFamily 2 (familyOnIndices extProbeFamily)) 0 :=
  isBalancedFamily_zero_of_bijective t (by simp)
    (productFamily_bijective 2 extProbeFamily_bijective)

/-- **Aux F31 (the schedule error is a nonnegative tolerance).**
`eps_2 = 1/(100 t_2)`
is nonnegative at the probe, so an exactly balanced family discharges a field
stated at `eps_2`.  The predecessor wording "a legal tolerance" is WITHDRAWN: the
proved fact is nonnegativity, and the record it is read at, `extProbeWidths`, is
a BEYOND-PAPER record that fails the `eq:t2-search` floor `06:766`, so no
legality of any kind may be read off this declaration.  (Qualification added at
`cc-t7q` alongside ledger item `(b14)`; a *scalar*-legality use, disclosed rather
than counted among the ten.) -/
theorem extProbeEps2_nonneg : (0 : ℝ) ≤ extProbeEps2 := by
  rw [extProbeEps2]
  have ht : (0 : ℝ) < (extProbeWidths.t₂ : ℝ) := by
    exact_mod_cast extProbeWidths.t₂_pos
  positivity

set_option maxRecDepth 10000 in
/-- **Non-vacuity 8 (the call-(ii) fixed-width hypotheses of Localized Extension
are simultaneously satisfiable at a nondegenerate BEYOND-PAPER record).**

**Relabelled at `cc-t7p` (ledger item `(b11)`).**  The `cc-t7o-r2` title
"LANE-GATE 3 for the new binder ... hold at legal, nondegenerate values" is
WITHDRAWN: the record below fails the `eq:t2-search` floor `06:766`
(`k_2 = 576 < 2^{19}`), so "legal" is false of it and this is satisfiability
evidence about our encoding, not a witness at the paper's parameter values.
Nondegeneracy is unaffected and still claimed: the family is the exact full
product over the two-letter column alphabet, and the constant family is refuted
at the same numerals by `extProbe_constantFamily_fails`, so the balancedness
fields are not met by vacuity.

At the **gate-firing** record `extProbeWidths`, the schedule parameters
`B_cap = 3` (the frozen floor `B_cap >= 3` of `eq:stage2-one-depth-base`,
`07:272`), `L_h = b_1 = 595` and `v_max = 2` discharge **every** conjunct of
`ExtensionCallTwoFixedWidth`: the two `eq:epsilon-product` identities and the
frozen `eps_prod < 1/50`, the two schedule majorants, both lines of
`eq:all-extension-gates`, and both inherited column-loss inequalities
`eq:certified-E1`/`E2` at the call-(ii) substitution.

**Repair r3 (F-4).**  The bundle now also carries the two clauses of
`06:1116--1123`, and they are discharged at the *same* schedule numerals by the
exact full product of `A:120--122` over the two-letter column alphabet: the
physical family is balanced with error `0 <= eps_2`, and so is its `C_2 x C_2`
product with error `0 <= eps_prod`.  So the witness covers **every** binder of
the enlarged bundle, not just its arithmetic part. -/
theorem extProbe_fixedWidth_holds :
    ExtensionCallTwoFixedWidth extProbeWidths extProbeFamily 3 595 2 extProbeEps2
      extProbeEpsProd := by
  obtain ⟨hε0, hε50⟩ := extProbeEpsProd_range
  have hlog1 := logb_one_add_epsProd_le_one
  obtain ⟨hqR, htR⟩ := extProbe_casts
  have hb : extProbeWidths.b₁ = 595 := rfl
  have hk : extProbeWidths.k₂ = 576 := rfl
  have hr : extProbeWidths.r₂ = 578 := rfl
  refine ⟨rfl, rfl, hε50, le_rfl, le_rfl, ?_, ?_, ?_, ?_,
    isBalancedFamily_mono extProbeEps2_nonneg (extProbeFamily_isBalanced _),
    isBalancedFamily_mono hε0 (extProbeFamily_prod_isBalanced _)⟩
  · -- `eq:all-extension-gates`, first line (`06:943--945`)
    have hone : Real.logb 2 (2 : ℝ) = 1 := by simp
    have hb' : ((extProbeWidths.b₁ : ℕ) : ℝ) = 595 := by rw [hb]; norm_num
    have hlogq : Real.logb 2 (((2 : ℕ) : ℝ) * ((extProbeWidths.q₂ : ℕ) : ℝ))
        = 579 := by
      rw [hqR, show (((2 : ℕ) : ℝ)) = (2 : ℝ) from by norm_num,
        Real.logb_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
        Real.logb_pow, hone]
      norm_num
    have hlhs : ((extProbeWidths.b₁ : ℕ) : ℝ)
        + Real.logb 2 (((2 : ℕ) : ℝ) * ((extProbeWidths.q₂ : ℕ) : ℝ))
        + ((3 : ℕ) : ℝ) + Real.logb 2 (1 + extProbeEpsProd) ≤ 2048 := by
      rw [hb', hlogq]
      push_cast
      linarith
    exact le_trans hlhs extProbe_gate_one_rhs
  · -- `eq:all-extension-gates`, second line (`06:946--948`)
    have hb' : ((extProbeWidths.b₁ : ℕ) : ℝ) = 595 := by rw [hb]; norm_num
    have hk' : ((extProbeWidths.k₂ : ℕ) : ℝ) = 576 := by rw [hk]; norm_num
    have hlhs : ((extProbeWidths.b₁ : ℕ) : ℝ) + ((extProbeWidths.k₂ : ℕ) : ℝ)
        + ((3 : ℕ) : ℝ) + Real.logb 2 (1 + extProbeEpsProd) ≤ 2048 := by
      rw [hb', hk']
      push_cast
      linarith
    have hrhs : (2048 : ℝ)
        ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((extProbeWidths.k₂ : ℕ) : ℝ)) := by
      rw [extProbe_sqrt_k₂]
      exact twoPow_certified_exponent_ge
    exact le_trans hlhs hrhs
  · -- `eq:certified-E1` (`A:130--134`) at the call-(ii) substitution
    refine le_yLoss_of_pow_le extProbeWidths.t₂_pos (by norm_num) ?_
    have hcast : ((extProbeWidths.r₂ + 1 + 3 : ℕ) : ℝ) = ((582 : ℕ) : ℝ) := by
      rw [hr]
    have hpow582 : (2 : ℝ) ^ (-(((582 : ℕ) : ℝ))) = ((1 : ℝ) / 2) ^ (582 : ℕ) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    have hexp : (1166 : ℕ) ≤ extProbeWidths.t₂ := by
      change (1166 : ℕ) ≤ 2 ^ 576
      calc (1166 : ℕ) ≤ 2 ^ 11 := by norm_num
        _ ≤ 2 ^ 576 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have hstep1 : ((3 : ℝ) / 5) ^ extProbeWidths.t₂ ≤ ((3 : ℝ) / 5) ^ (1166 : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
    have hstep2 : ((3 : ℝ) / 5) ^ (1166 : ℕ) ≤ ((1 : ℝ) / 2) ^ (583 : ℕ) := by
      rw [show (1166 : ℕ) = 2 * 583 by norm_num, pow_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      norm_num
    have hhalf : (0 : ℝ) < ((1 : ℝ) / 2) ^ (582 : ℕ) := by positivity
    have hfac : ((1 : ℝ) / 2) * (1 + extProbeEpsProd) ≤ 49 / 64 := by linarith
    have hprod := mul_le_mul_of_nonneg_left hfac (le_of_lt hhalf)
    have hrhs : ((1 : ℝ) / 2) ^ (583 : ℕ)
        ≤ 49 / 64 * ((1 : ℝ) / 2) ^ (582 : ℕ) / (1 + extProbeEpsProd) := by
      rw [le_div_iff₀ (by linarith), pow_succ]
      nlinarith [hprod]
    rw [hcast, hpow582]
    linarith
  · -- `eq:certified-E2` (`A:135--136`) at the call-(ii) substitution
    have hseed : StageTwoRelaxed.hSeedTwo extProbeWidths.k₂
        ≤ (2 : ℝ) ^ (-(2048 : ℝ)) := by
      rw [StageTwoRelaxed.hSeedTwo, extProbe_sqrt_k₂]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := twoPow_certified_exponent_ge; linarith)
    have hcast : ((extProbeWidths.k₂ + 3 : ℕ) : ℝ) = ((579 : ℕ) : ℝ) := by
      rw [hk]
    have hsmall : (2 : ℝ) ^ (-(2048 : ℝ)) ≤ (2 : ℝ) ^ (-(580 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hsplit : (2 : ℝ) ^ (-(580 : ℝ))
        = (2 : ℝ) ^ (-(((579 : ℕ) : ℝ))) * (1 / 2) := by
      rw [show (-(580 : ℝ)) = -(((579 : ℕ) : ℝ)) + (-1 : ℝ) by push_cast; ring,
        Real.rpow_add (by norm_num)]
      congr 1
      rw [show (-1 : ℝ) = (((-1 : ℤ)) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    have hpos579 : (0 : ℝ) < (2 : ℝ) ^ (-(((579 : ℕ) : ℝ))) := by positivity
    have hfac : ((1 : ℝ) / 2) * (1 + extProbeEpsProd) ≤ 49 / 64 := by linarith
    have hprod := mul_le_mul_of_nonneg_left hfac (le_of_lt hpos579)
    have hrhs : (2 : ℝ) ^ (-(((579 : ℕ) : ℝ))) * (1 / 2)
        ≤ 49 / 64 * (2 : ℝ) ^ (-(((579 : ℕ) : ℝ))) / (1 + extProbeEpsProd) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [hprod]
    rw [hcast]
    calc StageTwoRelaxed.hSeedTwo extProbeWidths.k₂
        ≤ (2 : ℝ) ^ (-(2048 : ℝ)) := hseed
      _ ≤ (2 : ℝ) ^ (-(580 : ℝ)) := hsmall
      _ = (2 : ℝ) ^ (-(((579 : ℕ) : ℝ))) * (1 / 2) := hsplit
      _ ≤ _ := hrhs

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY (relabelled at `cc-t7o-r3`; the
`cc-t7o-r2` "Non-vacuity 8b" label is WITHDRAWN).**

**This lemma audits OUR encoding at a width record the paper never visits, and
it is excluded from every fidelity and non-vacuity witness count in this route.**

*The violation, stated exactly.*  `06:763--770` (`eq:t2-search`) fixes `k_2` as
"the least integer satisfying" a list whose first row (`06:766`) is
`k_2 >= max{4, 2^{19}, m_{HS}}`.  `extProbeWidths.k₂ = 576` and
`2^{19} = 524288`, so `576 < 2^{19}`: the record **fails the frozen floor**, by
a factor of about `910`.  This repository's own reification says the same thing
independently -- `ParameterSchedule.k2Floor` is
`max (max 4 (2 ^ 19)) mHS`, so `k2Floor >= 524288 > 576 = extProbeWidths.k₂` --
and the reified predicate `ParameterSchedule.K2Pred`
(`ParameterSchedule.lean:1543`) has `k2Floor <= k` as its first conjunct.  (The
`cc-t7o-r3` citation to `ParameterSchedule.k2Search` is WITHDRAWN: no such
declaration exists anywhere in `src/`.  Only the name was wrong; the claim about
the floor is true at the bytes.)  `extProbeWidths` is
therefore **not** a legal schedule width record, and no statement instantiated
at it may be read as evidence about the paper's construction.

*What it does establish, which is strictly weaker.*  That
`ExtensionGatesFixedWidth` is not the empty predicate on the `StageTwoWidths`
carrier, and that the projection
`extensionCallTwoFixedWidth_supplies_extensionGates` composes with the banked
`extProbe_fixedWidth_holds`.  Both are facts about OUR Lean encoding.  The three
numerals are read off `extProbe_fixedWidth_holds` directly above rather than
chosen here (`B_cap = 3`, `L_h = 595`, `v_max = 2`), but a numeral inherited
from a beyond-paper record is beyond-paper too, and this docstring no longer
claims otherwise: the `cc-t7o-r2` wording "inhabited at exactly the legal,
nondegenerate values", "certified-regime widths" and "the frozen floor of
`eq:stage2-one-depth-base`" over-claimed legality for the whole tuple and is
replaced, not extended.

*Canonical inhabitation stays REGISTERED and is not touched by this.*  The
paper's own instance of the display is the schedule `Compile(c)` emits, which
depends on construction machinery that is not built; the obligation stays open
under `S5-CUTOFF-ITEMS-DEFERRED` / `S5-LEVEL-STEP` and is discharged when the
construction lands -- never by this probe, and (after this relabel) never by
anything that cites this probe.

*The registration this paragraph carried is now DISCHARGED (`cc-t7p`, ledger
item `(b11)`).*  At `cc-t7o-r3` this paragraph recorded that the banked
`extProbeWidths` docstring and its call-(ii) probe block still described the
record as "inside the **certified** regime" and as "a width where every frozen
gate fires at once", and that repairing them was out of that round's arc.  Both
sentences are WITHDRAWN at their own sites in this file, and every **live** use
of "certified regime" is replaced by the **gate-firing** regime (with its
meaning fixed at the record's definition: the widths at which
`eq:all-extension-gates` holds), across this module and the three downstream
modules that inherited the term (`TerminalFixedBin`, `TerminalStageThreeLift`,
`Stage3ProtocolRouting`), together with this module's own header.

*Scope of that sweep, stated exactly rather than as a completeness claim
(`cc-t7p` verify seat, finding F-4).*  It covers **live** uses only.  The
retired string is deliberately retained inside withdrawal notes, which must
name the term they retire; those occurrences are not defects and are not
swept.  The sweep is **not** a repository-wide guarantee about the separate
unqualified-"legal" wording, which `cc-t7p` left registered OPEN under `(b14)`.
*That separate census is now repaired at `cc-t7q`* -- all ten sites, listed at
the `probeWidths` definition above -- again as comment prose only.  Its two
hyphenated `certified-regime` variants (this file, the `extProbeWidths`
consistency note and the `cc-t7o-r3` paragraph above) were re-read at the bytes
that round and both sit **inside withdrawal prose** that names the retired
string on purpose, so neither is a live use and neither is swept.
Nothing mathematical moved; every edit of that sweep is comment prose, with the
single disclosed exception of the `(b15)` rename
`probeWidths_are_legal -> probeWidths_dyadic_readout`, whose statement type and
proof term are byte-identical. -/
theorem extensionGatesFixedWidth_at_extProbe :
    ExtensionGatesFixedWidth extProbeWidths 3 595 2 extProbeEpsProd :=
  extensionCallTwoFixedWidth_supplies_extensionGates extProbe_fixedWidth_holds

/-- **Rejection probe (the display genuinely bites, and the trivial witness
fails it).**  At the *balance-minimum* record `probeWidths` -- the smallest
width record the frozen balance gates permit, `k_2 = 5` and `t_2 = 32` -- the
factored display is unsatisfiable at **every** choice of `B_cap`, `L_h`,
`v_max` and every legal `eps_prod >= 0`, because its second row alone demands
`k_2 <= 2^{0.49 sqrt k_2}` and `2^{0.49 sqrt 5} <= 2^{2} = 4 < 5`.

This claims **no legality** for its own values -- it is the refutation form -- and
it is the kernel check of the prose observation recorded above at the call-(ii)
probe block, which stated in words that `probeWidths` is deliberately not
offered as an `ExtensionCallTwoFixedWidth` witness.  It also answers the
statement-pole question directly: the trivial witness fails, so the display is
not a decoration.  General in the three integer parameters and the error. -/
theorem extensionGatesFixedWidth_fails_at_balance_minimum
    (bcap Lh vmax : ℕ) {epsProd : ℝ} (he : 0 ≤ epsProd) :
    ¬ ExtensionGatesFixedWidth probeWidths bcap Lh vmax epsProd := by
  intro h
  have hk := extensionGatesFixedWidth_forces_exponent_gate he h
  have hk5 : ((probeWidths.k₂ : ℕ) : ℝ) = 5 := by
    change ((5 : ℕ) : ℝ) = 5
    norm_num
  have hsq9 : Real.sqrt (9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hsqrt : Real.sqrt ((probeWidths.k₂ : ℕ) : ℝ) ≤ 3 := by
    rw [hk5, ← hsq9]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hfour : (2 : ℝ) ^ ((2 : ℝ)) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hrhs : (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((probeWidths.k₂ : ℕ) : ℝ))
      ≤ 4 := by
    rw [← hfour]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [hk5] at hk hrhs
  linarith

/-- **Non-vacuity 9 (the reached-capacity domain is nonempty at the gate-firing
probe too).**  Exactly as at `probeWidths`: the guard
`t_2 <= stoppingCapacity r_2 d` of the headline's Extension binder fires at
`d = 0, 1, 2` and first fails at `d = 3`, which is the frozen branch
`2 <= kappa_v < t_2` that `09:1015--1016` closes by the inherited two-copy and
odd-copy bounds instead of by call (ii). -/
theorem extProbeExtensionDomain_nonempty :
    extProbeWidths.t₂ ≤ DenseWeightedCount.stoppingCapacity extProbeWidths.r₂ 2
      ∧ ¬ extProbeWidths.t₂
          ≤ DenseWeightedCount.stoppingCapacity extProbeWidths.r₂ 3 := by
  constructor
  · rw [DenseWeightedCount.stoppingCapacity_eq]
    change (2 : ℕ) ^ (576 : ℕ) ≤ 2 ^ (578 - 2)
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · rw [DenseWeightedCount.stoppingCapacity_eq, not_le]
    change (2 : ℕ) ^ (578 - 3) < 2 ^ (576 : ℕ)
    exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)

/-- **Aux A3b (`07:398--401` sharpened).**  The frozen balancing gate bounds the
root threshold far below the `1/8` that `eq:terminal-entry` demands:
`lambda_0 = 2 q_2 2^{-b_1} <= 2/131072` at **every** legal width record.  This
is the quantitative form `terminalEntry_of_stageTwoWidths` throws away, and it
is what makes the third clause of `eq:terminal-entry` hold at a nondegenerate
`eps` and `delta'`.  General in the width record. -/
theorem lambdaZero_le_of_widths (W : StageTwoRelaxed.StageTwoWidths) :
    DenseBranchSelection.lambdaZero W.q₂ W.b₁ ≤ 2 / 131072 := by
  have hgate : (131072 : ℝ) * (W.q₂ : ℝ) ≤ (2 : ℝ) ^ W.b₁ := by
    have h := W.depth_gate
    have h' : ((131072 * 2 ^ W.r₂ : ℕ) : ℝ) ≤ ((2 ^ W.b₁ : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [StageTwoRelaxed.StageTwoWidths.q₂] using h'
  have hpow : (0 : ℝ) < (2 : ℝ) ^ W.b₁ := by positivity
  have hq0 : (0 : ℝ) ≤ (W.q₂ : ℝ) := Nat.cast_nonneg _
  rw [DenseBranchSelection.lambdaZero, div_le_iff₀ hpow]
  nlinarith

/-- **HYPOTHESIS-CONSISTENCY 5 (the repaired bundle, at the r2 binder set).**

This is the r1 consistency lemma re-landed against the *enlarged* hypothesis
set of repair r2.  It exhibits, simultaneously and at one set of values, every
binder of `TerminalTwoStream` except the banked `TwoStreamState` record and the
two inherited `Lambda` certificates of `eq:terminal-seed-inputs`:

* the banked width record itself -- so all seven frozen width conditions of
  `07:277--281` hold, not the three the predecessor bound;
* the remaining dyadic convention `s = 2^{r_3}`;
* the two checked-identity pins `x_T = 2^{-b_T}` and `y = 3/5`;
* `eq:terminal-entry` at a nondegenerate `eps = 1/100`, `delta' = 1/10`;
* the third clause `log_2 s < b_T` of `eq:terminal-seed-inputs`;
* **the new call-(ii) fixed-width Extension binder**, in full -- including, as
  of repair r3, the two `06:1116--1123` balancedness clauses about the
  headline's own family;
* the reached-capacity Extension binder in its `forall` form.

A satisfiable collection cannot yield `False`, so no derivation of `False` from
these binders can go through.  What it does *not* claim is unchanged from r1:
the two `Lambda` certificates are inherited Stage-1 and Stage-2 hardness inputs
about two different matrices, and no pair of matrices realizing them is
exhibited here. -/
theorem terminalTwoStream_r2_hypotheses_consistent :
    (8 : ℕ) = 2 ^ probeR₃
      ∧ probeXT = DenseStageFourOpening.xTdepth probeBT
      ∧ probeY = 3 / 5
      ∧ terminalEntry extProbeWidths.q₂ extProbeWidths.b₁ (1 / 100) (1 / 10)
      ∧ probeR₃ < probeBT
      ∧ ExtensionCallTwoFixedWidth extProbeWidths extProbeFamily 3 595 2
          extProbeEps2 extProbeEpsProd
      ∧ (∀ d : ℕ, d ≤ extProbeWidths.r₂ →
          extProbeWidths.t₂
            ≤ DenseWeightedCount.stoppingCapacity extProbeWidths.r₂ d →
          extensionCallTwo extProbeWidths.q₂ extProbeWidths.t₂
            (DenseWeightedCount.stoppingCapacity extProbeWidths.r₂ d)) := by
  refine ⟨by decide, rfl, rfl, ?_, by decide, extProbe_fixedWidth_holds, ?_⟩
  · obtain ⟨h16, hlam⟩ := terminalEntry_of_stageTwoWidths extProbeWidths
    refine ⟨h16, hlam, ?_⟩
    have hsharp := lambdaZero_le_of_widths extProbeWidths
    have hq : (128 : ℝ) ≤ (extProbeWidths.q₂ : ℝ) := by
      have h : (128 : ℕ) ≤ extProbeWidths.q₂ := by
        change (128 : ℕ) ≤ 2 ^ (578 : ℕ)
        calc (128 : ℕ) = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ 578 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      exact_mod_cast h
    have hdiv : (2 : ℝ) / (extProbeWidths.q₂ : ℝ) ≤ 2 / 128 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
    linarith
  · intro d _ hd
    exact extensionCallTwo_of_widths
      (StageTwoRelaxed.StageTwoWidths.q₂_eq extProbeWidths)
      (StageTwoRelaxed.StageTwoWidths.t₂_eq extProbeWidths) hd

/-- **Statement pole 7 (the family binder is exactly what the family swap
moves).**  Given that the bundle holds at one family, it holds at *any* other
family over the same widths and the same schedule numerals **if and only if**
that other family satisfies the two `06:1116--1123` clauses.  So the nine
arithmetic conjuncts are family-blind -- which is precisely why the predecessor
generation's bundle constrained no family at all -- and everything the family
argument contributes is located in the two fields repair r3 adds.  General in
both carriers and both families. -/
theorem fixedWidth_family_content_is_exactly_the_two_clauses
    {Ltwo Rone Ltwo' Rone' : Type*} [Fintype Ltwo] [Fintype Rone] [DecidableEq Rone]
    [Fintype Ltwo'] [Fintype Rone'] [DecidableEq Rone']
    (W : StageTwoRelaxed.StageTwoWidths) (cFam : Ltwo → Slot W.q₂ → Rone)
    (cFam' : Ltwo' → Slot W.q₂ → Rone') (bcap Lh vmax : ℕ) (eps2 epsProd : ℝ)
    (h : ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd) :
    ExtensionCallTwoFixedWidth W cFam' bcap Lh vmax eps2 epsProd
      ↔ (IsBalancedFamily W.t₂ (familyOnIndices cFam') eps2
          ∧ IsBalancedFamily W.t₂
              (productFamily 2 (familyOnIndices cFam')) epsProd) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := h
  constructor
  · rintro ⟨-, -, -, -, -, -, -, -, -, hb1, hb2⟩
    exact ⟨hb1, hb2⟩
  · rintro ⟨hb1, hb2⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hb1, hb2⟩

/-- **PROBE (repair r3, F-4): the new binder genuinely changes what is
provable.**  At the *same* width record and the *same* schedule numerals
`B_cap = 3`, `L_h = 595`, `v_max = 2`, `eps_2`, `eps_prod` that
`extProbe_fixedWidth_holds` discharges, the constant family -- the family the r2
generation left admissible -- **fails** the bundle.  By
`fixedWidth_family_content_is_exactly_the_two_clauses` the failure can be
nowhere but the two new fields, and by `constant_family_not_balanced` it is at
the first of them: the singleton pattern set `J = {0}` at the letter the
constant family never takes has empirical frequency `0` against target `1/2`,
which no error below `1` tolerates, while the schedule fixes
`eps_2 = 1/(100 t_2) <= 1/100`.  Deleting the two fields would restore the r2
state in which this same constant family is admissible; that asymmetry is the
whole content of F-4. -/
theorem extProbe_constantFamily_fails :
    ¬ ExtensionCallTwoFixedWidth extProbeWidths
        (fun (_ : Fin 1) (_ : Slot extProbeWidths.q₂) => false) 3 595 2
        extProbeEps2 extProbeEpsProd := by
  intro h
  have hbal := h.2.2.2.2.2.2.2.2.2.1
  have hconst : familyOnIndices (fun (_ : Fin 1) (_ : Slot extProbeWidths.q₂) => false)
      = fun (_ : Fin (Fintype.card (Fin 1))) (_ : Slot extProbeWidths.q₂) => false := rfl
  rw [hconst] at hbal
  have hone : (1 : ℝ) ≤ extProbeEps2 :=
    constant_family_not_balanced extProbeWidths.q₂_pos extProbeWidths.t₂_pos
      false true (by simp) hbal
  have ht1 : (1 : ℝ) ≤ (extProbeWidths.t₂ : ℝ) := by
    have h1 : (1 : ℕ) ≤ extProbeWidths.t₂ := extProbeWidths.t₂_pos
    exact_mod_cast h1
  have hsmall : extProbeEps2 ≤ 1 / 100 := by
    rw [extProbeEps2]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- **Non-vacuity 10 (the certified row ladder's legality guard is *live*).**

The r1 generation's `CertifiedRowLadder` binder was satisfiable by vacuity: at
any `x > 1/2` the guard `2^ell x <= 1` fails for every `ell >= 1`, so the
predicate held of every matrix and the four Stage-3 consequences were empty.
Two facts close that hole.  First, `certifiedRowLadder_of_base` now *proves* the
predicate from its own frozen antecedents, so it is no longer an assumption at
all.  Second, at the pinned scalars the guard is genuinely live: it fires at
`ell = b_T = 8` and first fails at `ell = 9`, whereas the r1 vacuity
construction `x = 1` fails it already at `ell = 1`. -/
theorem certifiedRowLadder_guard_is_live :
    (2 : ℝ) ^ (8 : ℕ) * probeXT ≤ 1 ∧ ¬ ((2 : ℝ) ^ (9 : ℕ) * probeXT ≤ 1)
      ∧ ¬ ((2 : ℝ) ^ (1 : ℕ) * (1 : ℝ) ≤ 1) := by
  have hx : probeXT = 1 / 256 := by
    rw [probeXT, DenseStageFourOpening.xTdepth, probeBT]
    norm_num
  refine ⟨by rw [hx]; norm_num, by rw [hx]; norm_num, by norm_num⟩


end EthInapproximability.ParameterizedNP.TerminalTwoStream
