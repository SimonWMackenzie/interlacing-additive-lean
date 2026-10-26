import EthInapproximability.ParameterizedNP.HardSeedFacade

/-!
# Parameterized NP route: the opening block of the scale-alignment section

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 1--273** -- the
  opening block of `sec:first-wrapper`, up to and including the statement of
  `thm:first-wrapper` and stopping immediately before
  `sec:wrapper-low-rungs` (`09:274`).  The anchors traced here, in the order the
  frozen block prints them:
  * `09:14--23`, the output contract of the whole section: "Its output is a
    matrix `W` satisfying, at one common row threshold `theta`",
    `eq:common-exact` (`comp W = C_W`, label `09:17`), `eq:common-dense`
    (`comp<W,1,theta,1-delta_U> >= C_W`, label `09:19`) and `eq:common-low`
    (`Lambda_3(W,1,theta,y) >= C_W - 1`, label `09:21`), followed by "The next
    section consumes only these three statements" (`09:23`);
  * `def:regular-finite-map` (label `09:55`, statement `09:54--67`) and
    `lem:regular-density-transfer` (label `09:70`, statement `09:69--87`, proof
    `09:89--103`) -- **consumed by pin**, see below;
  * `09:105--108`: "Let `q = 2^r` be the scale-alignment width and set
    `U = Int_q(N)`";
  * `09:109--119`: "Write `m = |Rows(N)|`.  The base-column reservoir of `A`
    becomes a uniformly duplicated row family of `N`; define
    `R_G = {base} x Omega x [w_0] subseteq Rows(N)`,
    `G = N|_{R_G x Cols(N)}`, `m_G = |Rows(G)|`, `g = m_G/m = 91/92`";
  * `eq:reference-all-columns` (label `09:123`, display `09:121--124`,
    `Cols(G) = Cols(N)`) with its motivation at `09:125--127`: "This equality is
    why the reference can follow every actual Bob restriction of the
    scale-alignment protocol: no auxiliary projection or reduced column alphabet
    is involved";
  * `09:129--131`: "Let `Y_T subseteq Cols(G)` be the template columns and put
    `lambda_T = |Y_T|/|Cols(G)|`.  The duplication schedule gives
    `lambda_T >= 99/100`";
  * `09:131--149`: the rung scalars `I_j = s/2^j`, `p_j = 9 I_j/16`,
    `x_j = I_j x_T` recalled from `08:170--172`, the new
    `hat beta_j = (y/2^j + lambda_T - 1)/lambda_T` (`09:138--141`), and
    `eq:reference-profile-gates` (label `09:148`, display `09:143--149`), the
    three exact balancing conditions
    `ceil(s(hat beta_j - x_j)/(1 - x_j)) >= p_j`, `j = 0,1,2`;
  * `lem:wrapper-reference` (label `09:152`, statement `09:151--162`): "Under
    `eq:hard-seed-width-gates` and `eq:reference-profile-gates`, assume the exact
    protected Stage-4 identity `comp N = C` from `cor:exact-protected-stage4`.
    In the `NO` case, `comp G = C`, `Lambda_3(G,1,x_T,y) >= C - 1`";
  * its frozen proof `09:164--236`, of which the first paragraph
    (`09:165--172`, "For a base row labelled by a raw Stage-4 column `c`, and a
    column labelled by a raw Stage-4 row `x`, the entry is `G(c,x) = B(x,c)`.
    Thus `G` is `B^T`, with uniform row duplication and harmless column
    duplication.  Since labelled duplication and transposition preserve
    complexity, `comp B = comp N = C`, and therefore `comp G = C`") is
    **proved outright** below, the regularity of the two forgetful maps
    `phi_R`, `phi_C` (`09:174--185`) is discharged from the banked regular-map
    layer, the `hat beta_j` bounds of `09:186--195` are proved, and the
    inherited hard-seed call of `09:196--235` is threaded through the banked
    facade with its two open binders named;
  * `thm:first-wrapper` (label `09:239`, statement `09:238--272`): the
    hypothesis list of `09:240--258`, the three conclusions
    `eq:wrapper-u-exact` (label `09:261`), `eq:wrapper-u-dense` (label `09:263`)
    and `eq:wrapper-u-low` (label `09:266`), and the closing sentence
    `09:268--271`: "Consequently, for `W = U^T` and `C_W = C + r`,
    `eq:common-exact`--`eq:common-low` hold.  In the `YES` case, the standard
    interlace protocol adds exactly `r` bits to the protocol for `N`";
  * `09:1782--1806`, the frozen proof of `thm:first-wrapper`, which is what
    fixes how the three `U`-clauses combine: "The three one-bit-down clauses
    were proved in `sec:wrapper-low-rungs`, and the full-strength clause was
    just proved.  The standard interlace protocol identifies the outer
    coordinate in `r` bits and then runs an optimal protocol for `N`, so
    `comp U <= C + r`.  Applying `eq:wrapper-u-dense` to the full matrix gives
    the reverse inequality and proves `eq:wrapper-u-exact`.  Finally set
    `W = U^T` and `C_W = C + r`.  Transposition exchanges the row and column
    restrictions in each one-copy bracket."  This passage is cited **only** as
    the proof recipe for the two derivations landed here; nothing between
    `09:274` and `09:1781` is claimed.
* **The regular-map layer is consumed by pin, not re-authored.**  The frozen
  `def:regular-finite-map` and `lem:regular-density-transfer` are already banked,
  in full and at these exact anchors, as
  `EthInapproximability.ParameterizedNP.RawLowProfileBody.IsFibreBounded`,
  `.IsFibreBounded.surjective` (the derived `09:64--65`), `.IsFibreBounded.mono`,
  `.fibreBounded_density_transfer` (`eq:fibre-bounded-density-transfer`),
  `.regular_density_transfer` (`eq:regular-density-transfer`),
  `.isFibreBounded_id`, `.isFibreBounded_fst` and `.isFibreBounded_prod` (the
  product clause `09:87--88`).  Not one of them is restated here.  The single
  authored addition is the fibre shape the frozen text uses at `09:181--184` and
  that the banked roster does **not** contain: `phi_C` forgets *which of two
  reservoirs over the same base carrier* a labelled column came from, and "every
  fibre has cardinality `u_0 + u_temp`" -- a sum, not a product.  That is
  `isFibreBounded_sumForget`, proved from the banked `isFibreBounded_fst`.
* **Predecessor anchors (consumed by pin, never restated):**
  * the banked `EthInapproximability.ParameterizedNP.DenseStageFourOpening`,
    which supplies the labelled carriers `ProtCols` / `ProtRows`, the forgetful
    maps `colForget` / `rowForget` with their sections `colSection` /
    `rowSection`, the complexity transport `D_precomp_le` / `D_forget_eq` /
    `sectionOf_injective`, `protectedDup`, the pinned `protectedAFrozen` with
    `protectedAFrozen_col_masses` (whose first clause **is** the frozen
    `g = 91/92` of `09:117`), `transposeN`, the public integers `dTwoBlock` and
    `cBlock`, the rung scalars `widthI`, `blockTarget`, `rowDensity`,
    `xTdepth`, and `lowProfile_of_frozen_rungs` (the "taking the minimum" step);
  * the banked `EthInapproximability.ParameterizedNP.RawLowProfileBody`, which
    supplies the whole regular-map layer above, `RungSeedWitness`,
    `Dfamily_ge_of_seed_witnesses`, `rung_schedule_identity` and
    `widthI_eq_two_pow`;
  * the banked `EthInapproximability.ParameterizedNP.HardSeedFacade`, which
    supplies `mHS`, `RungLanding` and
    `rungSeedWitness_of_landing_and_certificate` -- the complete inherited
    General Hard Seed call at the substitution
    `(M, b, t, j_seed) = (M_2^T, b_T, I_j, 5)` that `09:205--218` prints, with
    the same `p_j = 9 I_j/16`, `x_j = I_j x_T`, `h_j^raw` scalars;
  * the banked `EthInapproximability.ParameterizedNP.PilotStage3`, whose
    `powerOfTwoInterlace_upper` is the frozen "the standard interlace protocol
    identifies the outer coordinate in `r` bits" of `09:1789--1792`, and whose
    `familyComplexity_le_ambient` / `interlace_selector_upper` are the two steps
    of "applying `eq:wrapper-u-dense` to the full matrix" (`09:1794--1796`);
  * the vendored `NPCC.comp_transpose` (`lem:transposeComp`) and
    `EthBridge.dfamily_one_transpose` (one-copy transpose symmetry for the
    bracket family), which are exactly the frozen "Transposition exchanges the
    row and column restrictions in each one-copy bracket" of `09:1798--1800`.
* **Cited external interfaces, carried as explicit named hypotheses and never as
  axioms.**  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design and appears
  in no hypothesis below.  The deep inputs of this block are named binders at the
  exact gates the frozen text states them:
  * the Stage-2 `(1/10, b_T)`-robustness certificate of
    `eq:stage2-aux-certificate` -- the frozen `09:211--213` "The Stage-2
    certificate gives that `M_2^T` is `(1/10, b_T)`-robust and has complexity
    `D_2 >= 3`" -- is `hrob` and `hD3`, passed straight to the banked facade and
    never re-proved;
  * the geometric landing of `09:196--204` ("Condition
    `eq:reference-profile-gates` therefore supplies `p_j` Stage-3 bins ...
    Project a retained base-row set of density `x_T` to these bins and keep one
    representative of each projected tuple.  After transposing and relabelling,
    the resulting matrix is a member of `<M_2^T, p_j, x_j, x_T>`") is the banked
    `RungLanding` binder `hland`, at row density `x_T` rather than the `x_N` of
    the Section-8 call;
  * `cor:exact-protected-stage4`'s `comp N = C` is the binder `hN`;
  * the two deferred halves of `thm:first-wrapper` are the binders `hDenseRung`
    and `hLowRungs`, with the GAP-EXPOSED ranges recorded below.
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, and no declaration here is in its dependency
  graph.
* **New work.**  The reference construction `R_G`, `G` and their frozen readouts
  (`eq:reference-all-columns`, `g = 91/92`, `comp G = C`); the template density
  `lambda_T`, the new constant `hat beta_j` of `09:138--141` with the three
  frozen bounds `59/99, 29/99, 14/99` of `09:189--195` proved from
  `lambda_T >= 99/100`; `eq:reference-profile-gates` transcribed with a proved
  sufficient condition and a legal inhabitant; the conditional
  `lem:wrapper-reference`; and, for `thm:first-wrapper`, the two derivations the
  frozen proof performs on top of the deferred blocks -- `eq:wrapper-u-exact`
  from `eq:wrapper-u-dense` plus the interlace upper bound, and the entire
  output contract `eq:common-exact`--`eq:common-low` from the three `U`-clauses
  by one-copy transpose symmetry.
* Proof status: **new** for everything named in the previous item except the
  regular-map layer, which is **inherited by pin**; **conditional** (with named,
  documented open binders) for the three-rung half of `lem:wrapper-reference`
  and for the two deferred halves of `thm:first-wrapper`.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, opened first-hand
for this tranche.  Three items are claimed, each clause **once**, and each was
previously unclaimed:

* `eq:paper-reference-profile` (label line 233, display lines 230--234), whose
  three clauses are assigned separately:
  * `Cols(G_0) = Cols(N)` (line 231, first clause) -- `referenceG_follows_bob`,
    with `refIncl_not_surjective` as its separating probe;
  * `comp G_0 = C` (line 231, second clause) -- `D_referenceG`, and its pinned
    instantiation `D_referenceG_frozen`;
  * `Lambda_{G_0}(1, x_T, 3/5) >= C - 1` (line 232) --
    `wrapperReference_rungs`, and `wrapperReference` which conjoins it with the
    exact identity.
  `DenseStageFourOpening`'s header records that this item is "outside this
  block, and **nothing here claims it**", and `RawLowProfileBody`'s header
  records that reader line 315 onward "is scale-alignment territory, out of
  scope here".  This is that territory.
* `def:paper-adapted-stage4` (label line 325, statement lines 326--331), "The
  output `Adapt_4(R, M_2, S(G,s))` is the matrix `W = Int_q(N)^T`" -- the two
  definitions `wrapperU` and `wrapperW` together, with `wrapperW_apply` the
  readout that the second really is the transpose of the first.
* `eq:paper-adapted-stage4-interface` (label line 345, display lines 339--346),
  whose three clauses are assigned separately, all to
  `commonThreshold_of_wrapper`'s three conjuncts and to nothing else:
  `comp W = C_W` (line 340), `D_W(1; theta, 1 - delta_U) >= C_W` (line 342),
  `Lambda_W(1, theta, 3/5) >= C_W - 1` (line 344).

**Deliberately not claimed**, to avoid a double assignment:

* `A-stage4-details.tex` lines 305--311, the fibre display, is **already
  assigned** to the banked `RawLowProfileBody.regular_density_transfer` by its
  own row; the sentence at line 312 ("Products of such maps again have equal
  fibres") is likewise already carried by `isFibreBounded_prod`.  Nothing here
  reclaims either, and `isFibreBounded_sumForget` claims **no** reader item: the
  reader states no sum-of-reservoirs fibre count.
* Lines 361--368 (the reader's rung display `D_U(1; 3/(5.2^j), theta) >= C + r_q
  - 1 - j`) and lines 370 onward (the near-full rung outline) are the deferred
  blocks' content; they are cited in the GAP-EXPOSED list as *what the binders
  stand for*, and are **not** claimed as statements by any declaration here.
* The reader's YES clause (lines 347--350, `comp W <= Y + a + log q_2 + log s +
  r_q`) is the one-level assembly's, not this block's; `wrapperU_yes_upper` is
  the generic interlace bound of `09:1789--1792` and carries the
  autoformalization anchor alone.
* Lines 351--355 (`|Rows(W)| = n_N^q`, `|Cols(W)| = q m_N`) belong to the
  carrier-recurrence row and are not touched here.

## Candidate encodings of the all-column reference (`k = 2`, raced)

The novel object of this tranche is the *all-column reference* `G`: the
restriction of `N` to the base-column reservoir of `A`, with **every** column of
`N` retained.

**Candidate A (landed).**  `G` is the *row-restricted matrix along a named
injection*: `refIncl = Sum.inl : Om x Fin w_0 -> ProtCols ...` names `R_G`, and
`referenceG N = fun b c => N (refIncl b) c` is `G`.  The column carrier is
**syntactically unchanged**, so `eq:reference-all-columns` is not an extra
hypothesis, not a coercion, and not a proof obligation: it is the statement that
`referenceG_follows_bob` reads off by `rfl`, and no Bob restriction can fail to
transport.  `refIncl_not_surjective` shows the row restriction is nonetheless
proper, so `G` is not `N` in disguise.

**Candidate B (rejected).**  Carry `G` as a pair `(Finset (Rows N), Finset
(Cols N))` and take `subgame N R_G Finset.univ`.  This typechecks and is
provably the same game, but it destroys the very property the frozen text is
buying: the column carrier becomes `{c // c in Finset.univ}`, a *different type*
from `Cols(N)`, so every consumer that wants "the reference follows this Bob
restriction literally" must transport along an equivalence -- exactly the
"auxiliary projection" that `09:125--127` says is not involved.
`referenceG_is_the_subgame` records that the two agree entrywise, so the
rejection costs nothing mathematically and is decided on faithfulness.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the authored fibre shape of `09:181--184`, general (2):
  `isFibreBounded_sumForget`, `isFibreBounded_sumForget_nondegenerate`.
* `A2` the reference construction, general (5): `referenceG_apply`,
  `referenceG_follows_bob`, `refIncl_injective`, `refIncl_not_surjective`,
  `card_refRows`.
* `A3` the pinned reference readouts (3): `referenceG_row_mass` (the frozen
  `g = 91/92`), `D_referenceG`, `D_referenceG_frozen`.
* `A4` the template density, general (3): `lambdaTemplate_nonneg`,
  `lambdaTemplate_le_one`, `lambdaTemplate_ge_of_card`.
* `A5` the new constant `hat beta_j`, general (3): `betaHat_frozen_values`,
  `betaHat_mono_lambda`, `betaHat_ge_frozen`.
* `A6` `eq:reference-profile-gates` (2): `referenceProfileGates_of_margins`,
  `referenceProfileGates_legal_instance`.
* `A7` the wrapper matrices, general (4): `wrapperU_eq_interlace_at_width`,
  `wrapperW_apply`, `D_wrapperW`, `wrapperU_yes_upper`.
* `A8` the subtraction-free reading of the frozen rung display, general (1):
  `wrapperLow_subtraction_free`.
* `A9` `lem:wrapper-reference` (4): `xTdepth_mem`,
  `wrapperReference_bracket_nonempty` (the nonemptiness side condition
  discharged outright rather than carried as a binder), `wrapperReference_rungs`,
  `wrapperReference`.
* `A10` `thm:first-wrapper` (4): `wrapperU_exact_of_dense`,
  `firstWrapper_dense_is_saturated`, `commonThreshold_of_wrapper`,
  `firstWrapper`.

* `A11` the schedule layer of `06:530--533` and `06:547` (3):
  `scheduleTheta_antitone`, `scheduleTheta_guards`, `scheduleDeltaU_guards` --
  general in the schedule data, so the density guards of `thm:first-wrapper` are
  discharged over the whole admissible range and not at one numeral.

That is **35 battery entries proved**, with `0` unproved, alongside **three
statement poles** (`refIncl_not_surjective`, `firstWrapper_not_automatic`,
`betaHat_rung2_margin`), **four non-vacuity / consistency readouts**
(`referenceProfileGates_legal_instance`, `wrapperReference_fires_at_banked_tier`,
`firstWrapper_hypotheses_consistent`, `firstWrapper_fires_at_scheduled_pair`)
and the race readout `referenceG_is_the_subgame`.

The module has **50** source declarations in all: 8 definitions
(`scaleAlignWidth`, `refIncl`, `referenceG`, `lambdaTemplate`, `betaHat`,
`referenceProfileGates`, `wrapperU`, `wrapperW`) and 42 proved results.  All 50
are registered in `tools/AxiomAudit.lean`.  Four of the proved results are the
schedule layer added by the repair round: `scheduleTheta_antitone`,
`scheduleTheta_guards` and `scheduleDeltaU_guards` discharge the density guards
of `thm:first-wrapper` over the whole range the frozen schedule admits
(`eq:Q-theta-choice`, `06:530--533`; the finite gate `06:547`), and
`firstWrapper_fires_at_scheduled_pair` drives one schedule-legal pair through
`firstWrapper` to its three output-contract clauses.

## Why the deliverables are not satisfied by a trivial witness

Neither headline is existential, so the pole takes the other admissible form:
each conclusion is exhibited as *refutable at a legal-shaped instance*, so it
cannot be read off the shape of the statement.

* `firstWrapper`'s exact clause `comp U = C + r` fails at the constant matrix:
  `firstWrapper_not_automatic` computes `comp(Int_{2^r}(0)) = 0`, which misses
  `C + r >= 3` for every legal `C >= 3`.  So the value comes from the two
  deferred family bounds and from `hN`, not from the interlace shape.
* `wrapperReference`'s three-rung clause fails whenever the rung binders fail:
  the banked `RawLowProfileBody.seed_witness_trivial_fails` (consumed by pin)
  already shows the empty restriction never reaches a positive rung value, and
  `HardSeedFacade.rungValue_pos` shows the rung value here is at least `8`.
* `eq:reference-profile-gates` is not automatic: `betaHat_rung2_margin` computes
  the `j = 2` numerator margin exactly, `hat beta_2 - 9/64 = 5/6336`, so the
  gate is a real finite comparison and `j = 2` is the binding rung -- which is
  precisely why `06:924--933` schedules `q x_T <= 4/25025 < 5/6336`.  That
  margin drives the *sufficient* condition used here; the frozen paper's exact
  admissible bound on `x_2` is the larger `1/1089` (`06:918--920`), so the
  reading taken here is the conservative one.
* `firstWrapper`'s dense binder is not an over-demand either:
  `firstWrapper_dense_is_saturated` shows it forces the bracket family value to
  be *exactly* `C + r`, the largest value the ambient matrix admits.  A separate
  scratch probe attempted to derive `False` from the whole bundle over the
  schedule-legal regime (`C = 3`; an arbitrary `theta` with
  `0 < theta <= (1/10)/(16 * 128)`, the unconditional ceiling
  `eq:Q-theta-choice` forces because `8/delta = 80` is a term of `Q_0` at
  `delta = 1/10`, `06:530--533` with `06:539`, so `Q >= 128`;
  `delta_U = 1/200`, the finite gate of `06:547`; `y = 3/5`) and could not: the
  arithmetic core is satisfiable and the bundle fires, producing all six
  conclusions.  The in-library `firstWrapper_fires_at_scheduled_pair` records
  the firing half of that probe, over the same `theta`-range and not at a
  point.

## Three-tier witness legality

* **Tier 1 -- symbolic in the frozen parameters.**  Every result about
  `referenceG`, `betaHat`, `lambdaTemplate`, `wrapperU`, `wrapperW`,
  `wrapperReference_rungs`, `wrapperReference`, `wrapperU_exact_of_dense`,
  `commonThreshold_of_wrapper` and `firstWrapper` is general in the carriers, in
  the matrices, in `r`, `C`, `s`, `b_T`, and in the real parameters
  `delta_U, theta, y, lambda_T`.  Nothing is evaluated.
* **Tier 2 -- a fully instantiated legal instance of the block's regime.**
  `referenceProfileGates_legal_instance` exhibits the three exact ceiling
  comparisons of `eq:reference-profile-gates` at `s = 2^340`, `b_T = 512`,
  `y = 3/5`, `lambda_T = 99/100`, i.e. at the frozen `y`, at the frozen floor of
  the template density, and at the **same** tier
  `wrapperReference_fires_at_banked_tier` already uses.  Both **computable**
  clauses of `eq:hard-seed-width-gates` (`06:264--268`) hold at it --
  `16 | (s/4) = 2^338` and `log_2 s = 340 < 512 = b_T` -- and the pair also
  respects the *definition* `b_T = 2^{j_49(k_T)}` (`06:238--242`, not a gate
  clause), `512` being `2^9`.  The gate's remaining clause
  `k_T = log_2(s/4) >= m_HS` is not checkable (`m_HS` is the `Nat.sInf` of
  `06:250--253`, never evaluated in the frozen paper) and is deferred to the
  abstract hypothesis `hmHS : mHS <= 338` of
  `wrapperReference_fires_at_banked_tier`, not asserted here.
  `firstWrapper_hypotheses_consistent` exhibits the whole numeric side of
  `thm:first-wrapper`'s bundle simultaneously at the frozen `y = 3/5`, at
  `delta_U = 1/200` (the finite gate of `06:547` verbatim), at `C = 3` (the
  frozen floor of `09:240`), and for an **arbitrary** `theta` in the range
  `eq:Q-theta-choice` (`06:530--533`) makes unconditional,
  `0 < theta <= (1/10)/(16 * 128)`: with `delta = 1/10` (`06:539`) the term
  `8/delta = 80` of `Q_0` forces `Q >= 128`, and the remaining term
  `8 bout/(delta delta_U)` depends on the instance datum `bout`, so **no**
  numeral is an admissible value of `theta` for every input and none is pinned.
  `firstWrapper_fires_at_scheduled_pair` drives that same range through
  `firstWrapper` to its three output-contract clauses, with `theta` quantified
  identically in its two family hypotheses and its three conclusions.  The
  general lemmas `scheduleTheta_antitone`, `scheduleTheta_guards` and
  `scheduleDeltaU_guards` cover the admissible range rather than any point of
  it.  The gate instance is not a **schedule** instance in the remaining data --
  the real schedule forces `s = 2^{ceil(B_s u^2)}` and `b_T = 2^{j_49(k_T)}` --
  and no parameter may be read out of either witness.
* **Tier 3 -- separating probes at deliberately small carriers.**
  `refIncl_not_surjective`, `isFibreBounded_sumForget_nondegenerate`,
  `firstWrapper_not_automatic` and `betaHat_rung2_margin` are probes of one
  named clause at a minimal carrier or at one rung, and are cited only for what
  they separate.

## Honest scope, GAP-EXPOSED, and recorded coverage limits

1. **GAP-EXPOSED (the six later blocks of Section 9).**  `thm:first-wrapper` is
   landed as a *closed conditional*: the two clauses whose proofs live after
   `09:273` are named binders, and the frozen ranges they stand for are
   * `hLowRungs` <- `sec:wrapper-low-rungs`, **`09:274--334`** (the three
     one-bit-down rungs; frozen conclusion at `09:330--333`,
     `comp<U,1,y_*/2^j,theta> >= C + log_2 q - 1 - j`);
   * `hDenseRung` <- the five blocks that jointly prove `eq:wrapper-u-dense`:
     `sec:wrapper-projection-covers` **`09:335--460`**
     (`lem:product-projection-cover`), the terminal two-stream block
     **`09:461--1183`** (`lem:owner-donor-realization`,
     `lem:terminal-two-stream`), `sec:wrapper-dense-frontier`
     **`09:1184--1366`** (`lem:no-bob-prefix-completion`,
     `lem:final-node-uniqueness`), `sec:wrapper-early-protected-mass`
     **`09:1367--1511`** (`lem:template-coordinate-extraction`,
     `lem:early-protected-closure`) and `sec:wrapper-mass-redistribution`
     **`09:1512--1781`**, whose last line (`09:1781`) is "We have proved
     `eq:wrapper-u-dense`".

   The frozen proof of `thm:first-wrapper` (`09:1783--1806`) cites exactly these
   two deliverables plus the interlace upper bound, so exactly two binders --
   not six -- appear in the signature.  Manufacturing four further hypotheses
   for the intermediate lemmas would invent statements the frozen theorem does
   not use; the six ranges are recorded here instead, and each remains a
   separate future tranche.
2. **`lem:wrapper-reference` is conditional, and every deferred binder is named
   here.**  `wrapperReference` carries five: `hrob` (the Stage-2 `(1/10, b_T)`
   certificate, ledger `STAGE2-MODULE-001`), `hD2`, `hD3`, `hland` (the
   geometric landing of `09:196--204`) -- all open exactly as they are in the
   banked Section-8 threading, and nothing here narrows them -- and `hDG`, the
   exact clause, which `wrapperReference` passes straight through to its own
   conclusion.  The exact half `comp G = comp B` **is** proved outright, by
   `D_referenceG` and `D_referenceG_frozen`; what is *not* discharged is the
   wiring that would feed `D_referenceG_frozen` into `hDG` at the construction,
   because that composition needs `cor:exact-protected-stage4`, which is outside
   this block.  That wire is owed, and is recorded as owed in the ledger row --
   it is **not** a proof of `hDG`.
3. **`eq:hard-seed-width-gates` enters only through its consequences.**  The
   frozen gate `06:264--269` is consumed as the two arithmetic clauses the
   banked facade demands, `mHS + 2 <= w_S` and `w_S <= b_T`; the gate itself is
   `06`'s and is not restated here.
4. **`lambda_T >= 99/100` is a hypothesis, never derived.**  Its derivation is
   `eq:lambda-template-exact` (`06:145--155`), outside this block;
   `lambdaTemplate_ge_of_card` converts a cardinality bound into it, and
   `betaHat_ge_frozen` consumes it.  No declaration here asserts it.
5. **No routing, protocol or frontier is constructed.**  `U` and `W` are the
   interlace and its transpose, nothing more; every complexity claim about them
   is conditional on the binders above.
6. **Nothing after `09:273` is proved, and no route completion is claimed.**
   The construction and machine layers of the route remain unlanded.
7. **`r`, `C`, `s`, `b_T` and the real parameters are binders, not values.**  No
   parameter schedule may be read out of any witness below; the tier labelling
   above is binding on consumers.
-/

namespace EthInapproximability.ParameterizedNP.ScaleAlignOpening

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.RawStageFour
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.RawLowProfileBody
open EthInapproximability.ParameterizedNP.HardSeedFacade

/-! ## §1  The regular-map layer (`09:53--103`), consumed by pin

`def:regular-finite-map` and `lem:regular-density-transfer` are banked in
`RawLowProfileBody` at these exact anchors and are **not** restated.  The one
fibre shape the frozen proof uses at `09:181--184` and that the banked roster
lacks is authored here. -/

/-- **Aux A1a (`09:182--184`, the two-reservoir fibre count).**

"On the template columns `Y_T`, let `phi_C` forget whether the copy came from
the base or the template reservoir and forget its repetition label. ... every
fibre has cardinality `u_0 + u_temp`."

The banked roster has the *product* fibre shape (`isFibreBounded_fst`,
`isFibreBounded_prod`); this is the *sum* shape, and it is the one `phi_C`
actually has.  General in the base carrier and in the two multiplicities, and
proved from the banked `isFibreBounded_fst` rather than by a second fibre
computation. -/
theorem isFibreBounded_sumForget {A : Type*} [Fintype A] [DecidableEq A]
    (a b : ℕ) :
    IsFibreBounded
      (fun z : (A × Fin a) ⊕ (A × Fin b) => Sum.elim Prod.fst Prod.fst z)
      (a + b) (a + b) := by
  classical
  intro x
  have hsplit :
      (Finset.univ.filter fun z : (A × Fin a) ⊕ (A × Fin b) =>
          Sum.elim Prod.fst Prod.fst z = x)
        = ((Finset.univ.filter fun p : A × Fin a => p.1 = x).disjSum
            (Finset.univ.filter fun p : A × Fin b => p.1 = x)) := by
    ext z
    cases z with
    | inl p => simp
    | inr p => simp
  have ha := isFibreBounded_fst (A := A) (B := Fin a) x
  have hb := isFibreBounded_fst (A := A) (B := Fin b) x
  rw [Fintype.card_fin] at ha
  rw [Fintype.card_fin] at hb
  rw [hsplit, Finset.card_disjSum]
  omega

/-- **Aux A1b (the authored fibre shape is nondegenerate).**  At `a = 2`,
`b = 3` over a two-element base the forgetful map is regular of degree
`5 > 1` and is not injective, so the sum shape is genuinely outside the
degree-one case; and the banked `regular_density_transfer` fires at it. -/
theorem isFibreBounded_sumForget_nondegenerate :
    IsFibreBounded
        (fun z : (Bool × Fin 2) ⊕ (Bool × Fin 3) => Sum.elim Prod.fst Prod.fst z)
        5 5
      ∧ 1 < 5
      ∧ ¬ Function.Injective
          (fun z : (Bool × Fin 2) ⊕ (Bool × Fin 3) =>
            Sum.elim Prod.fst Prod.fst z) := by
  refine ⟨by simpa using isFibreBounded_sumForget (A := Bool) 2 3, by norm_num, ?_⟩
  intro hinj
  have h : (Sum.inl (true, (0 : Fin 2)) : (Bool × Fin 2) ⊕ (Bool × Fin 3))
      = Sum.inr (true, (0 : Fin 3)) := hinj rfl
  simp at h

/-! ## §2  The reference construction (`09:105--127`)

`q = 2^r`, `U = Int_q(N)`, and the all-column reference `G` on the base-column
reservoir `R_G` of `A`. -/

/-- **`09:105`.**  `q = 2^r` is the scale-alignment width.  A name for the
frozen power of two; the interlace calls below use `2 ^ r` literally so that the
banked `powerOfTwoInterlace_upper` applies without a rewrite. -/
def scaleAlignWidth (r : ℕ) : ℕ := 2 ^ r

@[simp] theorem scaleAlignWidth_def (r : ℕ) : scaleAlignWidth r = 2 ^ r := rfl

theorem scaleAlignWidth_pos (r : ℕ) : 0 < scaleAlignWidth r :=
  pow_pos (by norm_num) r

/-- **`09:113--114`.**  `R_G = {base} x Omega x [w_0] subseteq Rows(N)`.  Since
`N = A^T`, a row of `N` is a column of `A`, and the base column reservoir of
`eq:protected-labelled-carriers` is the first summand of `ProtCols`.  The
inclusion is named so that "`R_G subseteq Rows(N)`" is a map with a carrier of
its own rather than a `Finset` with a forgotten type. -/
def refIncl {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} :
    Om × Fin w₀ → ProtCols Om Sg Dg w₀ wSg wD :=
  Sum.inl

/-- **Aux A2a.**  `R_G` really is a subset of `Rows(N)`: the inclusion is
injective, so the reference has exactly `m_G = |Omega| w_0` rows and no two of
them are identified. -/
theorem refIncl_injective {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} :
    Function.Injective (refIncl (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
      (wSg := wSg) (wD := wD)) := by
  intro x y h
  exact Sum.inl_injective h

/-- **Statement pole (`R_G` is a proper subset).**  As soon as the selector
reservoir is inhabited with positive multiplicity, `refIncl` misses a row of
`N`, so `G` is a genuine restriction and not a relabelling of `N`.  This is what
makes `comp G = C` a theorem about a **submatrix** rather than a tautology. -/
theorem refIncl_not_surjective {Om Sg Dg : Type*} {w₀ wSg wD : ℕ} (s : Sg)
    (hw : 0 < wSg) :
    ¬ Function.Surjective (refIncl (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
      (wSg := wSg) (wD := wD)) := by
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj (Sum.inr (Sum.inl (s, ⟨0, hw⟩)))
  simp [refIncl] at hz

/-- **Aux A2b (`09:117`).**  `m_G = |Rows(G)| = |Omega| w_0`.  General. -/
theorem card_refRows (Om : Type*) [Fintype Om] (w₀ : ℕ) :
    Fintype.card (Om × Fin w₀) = Fintype.card Om * w₀ := by
  simp

/-- **`09:115--117`.**  `G = N|_{R_G x Cols(N)}`, the all-column reference.

The column carrier `Cl` is **unchanged**: this is `eq:reference-all-columns`
built into the type, not asserted about it.  General in the reservoir carriers,
the multiplicities, the column carrier and `N`. -/
def referenceG {Om Sg Dg Cl : Type*} {w₀ wSg wD : ℕ}
    (Nmat : ProtCols Om Sg Dg w₀ wSg wD → Cl → Bool) :
    Om × Fin w₀ → Cl → Bool :=
  fun b c => Nmat (refIncl b) c

@[simp] theorem referenceG_apply {Om Sg Dg Cl : Type*} {w₀ wSg wD : ℕ}
    (Nmat : ProtCols Om Sg Dg w₀ wSg wD → Cl → Bool) (b : Om × Fin w₀) (c : Cl) :
    referenceG Nmat b c = Nmat (refIncl b) c := rfl

/-- **`eq:reference-all-columns` (`09:121--127`).**

"`Cols(G) = Cols(N)`.  This equality is why the reference can follow every
actual Bob restriction of the scale-alignment protocol: no auxiliary projection
or reduced column alphabet is involved."

Read as what it is used for: for **every** Bob restriction `C` of `Cols(N)` and
every reference row set `R`, the extracted reference game evaluates `N` at the
*same* column element `c.1 : Cl` -- no projection, no coercion, no reduced
alphabet.  The proof is `rfl`, which is the point: with any column map in the
encoding it would not be. -/
theorem referenceG_follows_bob {Om Sg Dg Cl : Type*} {w₀ wSg wD : ℕ}
    (Nmat : ProtCols Om Sg Dg w₀ wSg wD → Cl → Bool)
    (R : Finset (Om × Fin w₀)) (C : Finset Cl)
    (b : {x // x ∈ R}) (c : {x // x ∈ C}) :
    subgame (referenceG Nmat) R C b c = Nmat (refIncl b.1) c.1 := rfl

/-- **Race readout (Candidate B agrees entrywise).**  Presenting `G` as the
subgame of `N` on `(R_G, univ)` gives the same entries; the rejection of
Candidate B is about the *type* of the column carrier, not about the
mathematics. -/
theorem referenceG_is_the_subgame {Om Sg Dg Cl : Type*} [Fintype Cl]
    [DecidableEq Om] [DecidableEq Sg] [DecidableEq Dg] {w₀ wSg wD : ℕ}
    (Nmat : ProtCols Om Sg Dg w₀ wSg wD → Cl → Bool)
    (R : Finset (Om × Fin w₀)) (b : {x // x ∈ R}) (c : {x // x ∈ (Finset.univ : Finset Cl)}) :
    subgame (referenceG Nmat) R Finset.univ b c
      = subgame Nmat (R.image refIncl) Finset.univ
          ⟨refIncl b.1, Finset.mem_image_of_mem _ b.2⟩ c := rfl

/-- **`09:117`, the frozen `g = m_G/m = 91/92`, at the pinned protected
instance.**

The reference row mass is read off the **built** object: the numerator is the
cardinality of `Rows(G) = Omega x [w_0]` and the denominator the cardinality of
`Rows(N) = Cols(A) = ProtColsFrozen`.  Nothing new is computed -- this is the
banked `protectedAFrozen_col_masses` first clause, consumed by pin, with the
numerator rewritten as the cardinality of the reference carrier. -/
theorem referenceG_row_mass (F : Stage1SlotBinding) {q : ℕ} {Y : Type*}
    [Fintype Y] (hq : 0 < q) (y₀ : Y) :
    ((Fintype.card (Omega F q Y × Fin (wBaseF F q Y)) : ℕ) : ℚ) /
        ((Fintype.card (ProtColsFrozen F q Y) : ℕ) : ℚ) = 91 / 92 := by
  rw [card_refRows]
  exact (protectedAFrozen_col_masses F hq y₀).1

/-! ## §3  `comp G = C` (`09:164--172`), proved

"For a base row labelled by a raw Stage-4 column `c`, and a column labelled by a
raw Stage-4 row `x`, the entry is `G(c,x) = B(x,c)`.  Thus `G` is `B^T`, with
uniform row duplication and harmless column duplication.  Since labelled
duplication and transposition preserve complexity, `comp B = comp N = C`, and
therefore `comp G = C`."

Both frozen ingredients are banked: `D_forget_eq` (the duplication half) and
`NPCC.comp_transpose` (the transposition half). -/

/-- **`09:165--172` (`comp G = comp B`), general.**

`G` is `B^T` precomposed with two forgetful maps: on rows, forget the base
multiplicity index (`Prod.fst`); on columns, forget the row reservoir label and
its multiplicity index (`rowForget`).  Both have the frozen sections, so
`D_forget_eq` applies verbatim, and `comp_transpose` turns `comp(B^T)` into
`comp B`.  General in every carrier, inclusion and multiplicity, with the two
base multiplicities positive exactly as `eq:protected-multiplicities`
guarantees. -/
theorem D_referenceG {Xr Tm Wv Wb Om Sg Dg : Type*}
    {u₀ uT uV uB w₀ wSg wD : ℕ} [Fintype Xr] [Fintype Tm] [Fintype Wv]
    [Fintype Wb] [Fintype Om]
    (Bmat : Xr → Om → Bool) (iT : Tm → Xr) (iV : Wv → Xr) (iB : Wb → Xr)
    (iSg : Sg → Om) (iD : Dg → Om) (hu : 0 < u₀) (hw : 0 < w₀) :
    D (referenceG (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀) (wSg := wSg)
        (wD := wD)
        (transposeN (protectedDup (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB)
          (w₀ := w₀) (wSg := wSg) (wD := wD) Bmat iT iV iB iSg iD)))
      = D Bmat := by
  have hshape :
      (referenceG (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀) (wSg := wSg)
        (wD := wD)
        (transposeN (protectedDup (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB)
          (w₀ := w₀) (wSg := wSg) (wD := wD) Bmat iT iV iB iSg iD)))
        = fun (b : Om × Fin w₀)
            (c : ProtRows Xr Tm Wv Wb u₀ uT uV uB) =>
              (fun (o : Om) (x : Xr) => Bmat x o) (Prod.fst b)
                (rowForget (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) iT iV iB c) := rfl
  rw [hshape]
  rw [D_forget_eq (fun (o : Om) (x : Xr) => Bmat x o) (Prod.fst)
      (rowForget (u₀ := u₀) (uT := uT) (uV := uV) (uB := uB) iT iV iB)
      (fun o => (o, ⟨0, hw⟩)) (rowSection hu) (fun _ => rfl) (fun _ => rfl)]
  exact comp_transpose Bmat

/-- **`09:165--172` at the pinned protected instance.**

`comp G = comp B` for the reference of the *frozen* `N = A^T`, with both base
multiplicity positivity side conditions **discharged** from the reservoirs'
inhabitedness at legal parameters (`uBaseF_pos`, `wBaseF_pos`), never assumed.
Together with the banked `D_protectedAFrozen` this is the frozen chain
`comp G = comp B = comp N = C`. -/
theorem D_referenceG_frozen {F : Stage1SlotBinding} {q : ℕ} {V X L₂ Y : Type*}
    [Fintype V] [Fintype X] [Fintype L₂] [Fintype Y] (hq : 0 < q) (hs : 4 ≤ F.s)
    (y₀ : Y) (v₀ : V) (x₀ : X) (l₀ : L₂)
    (Bmat : RowsB F V X L₂ → Omega F q Y → Bool) :
    D (referenceG (transposeN (protectedAFrozen Bmat y₀))) = D Bmat :=
  D_referenceG Bmat (tempIncl F V X L₂) (vertIncl F V X L₂) (blockIncl F V X L₂)
    (selIncl F y₀) (diagIncl F) (uBaseF_pos F hs v₀ x₀ l₀) (wBaseF_pos F hq y₀)

/-! ## §4  The template columns and the new constant `hat beta_j`
(`09:129--149`) -/

/-- **`09:130`.**  `lambda_T = |Y_T|/|Cols(G)|`, the template column density.
By `eq:reference-all-columns` the denominator is `|Cols(N)|`, which is why the
carrier here is the ambient column type and not a reduced alphabet. -/
noncomputable def lambdaTemplate {Cl : Type*} [Fintype Cl] (YT : Finset Cl) : ℝ :=
  (YT.card : ℝ) / (Fintype.card Cl : ℝ)

/-- **Aux A4a.**  A density is nonnegative.  General. -/
theorem lambdaTemplate_nonneg {Cl : Type*} [Fintype Cl] (YT : Finset Cl) :
    0 ≤ lambdaTemplate YT := by
  unfold lambdaTemplate
  positivity

/-- **Aux A4b.**  A density is at most one.  General. -/
theorem lambdaTemplate_le_one {Cl : Type*} [Fintype Cl] (YT : Finset Cl) :
    lambdaTemplate YT ≤ 1 := by
  unfold lambdaTemplate
  rcases Nat.eq_zero_or_pos (Fintype.card Cl) with h | h
  · simp [h]
  · have hpos : (0 : ℝ) < (Fintype.card Cl : ℝ) := by exact_mod_cast h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_univ YT
/-- **Aux A4c (`09:131`, the schedule clause as a readout).**  "The duplication
schedule gives `lambda_T >= 99/100`."  The derivation is
`eq:lambda-template-exact` (`06:145--155`), outside this block; what is proved
here is only that a cardinality bound on `Y_T` is the same thing as the density
bound the gates consume.  General in the carrier and in the threshold. -/
theorem lambdaTemplate_ge_of_card {Cl : Type*} [Fintype Cl] (YT : Finset Cl)
    {c : ℝ} (hcard : c * (Fintype.card Cl : ℝ) ≤ (YT.card : ℝ))
    (hpos : 0 < Fintype.card Cl) :
    c ≤ lambdaTemplate YT := by
  have hposR : (0 : ℝ) < (Fintype.card Cl : ℝ) := by exact_mod_cast hpos
  unfold lambdaTemplate
  rw [le_div_iff₀ hposR]
  exact hcard

/-- **`09:138--141`.**  `hat beta_j = (y/2^j + lambda_T - 1)/lambda_T`, the
relative template density forced on an arbitrary column set of `G` of density
`y/2^j`.  General in `y`, `lambda_T` and the rung index. -/
noncomputable def betaHat (y lamT : ℝ) (j : ℕ) : ℝ :=
  (y / 2 ^ j + lamT - 1) / lamT

/-- **Aux A5a (`09:189--195` at the schedule floor, exactly).**  At the frozen
`y = 3/5` and at `lambda_T = 99/100` the three values are exactly the frozen
`59/99`, `29/99`, `14/99` -- equalities, not estimates. -/
theorem betaHat_frozen_values :
    betaHat (3 / 5) (99 / 100) 0 = 59 / 99
      ∧ betaHat (3 / 5) (99 / 100) 1 = 29 / 99
      ∧ betaHat (3 / 5) (99 / 100) 2 = 14 / 99 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold betaHat; norm_num

/-- **Aux A5b (`hat beta_j` is monotone in the template density).**  Writing
`hat beta_j = 1 + (y/2^j - 1)/lambda_T`, the numerator is nonpositive as soon as
`y/2^j <= 1`, so raising `lambda_T` raises `hat beta_j`.  This is the direction
the frozen bound needs: `09:131` gives only `lambda_T >= 99/100`, and
`09:189--195` reads off the value **at** `99/100`.  General. -/
theorem betaHat_mono_lambda {y lamT lamT' : ℝ} {j : ℕ}
    (hy : y / 2 ^ j ≤ 1) (h0 : 0 < lamT) (h : lamT ≤ lamT') :
    betaHat y lamT j ≤ betaHat y lamT' j := by
  have h0' : 0 < lamT' := lt_of_lt_of_le h0 h
  have hnum : y / 2 ^ j - 1 ≤ 0 := by linarith
  have key : (y / 2 ^ j - 1) / lamT ≤ (y / 2 ^ j - 1) / lamT' := by
    rw [div_le_div_iff₀ h0 h0']
    nlinarith
  have e1 : betaHat y lamT j = 1 + (y / 2 ^ j - 1) / lamT := by
    unfold betaHat
    field_simp
    ring
  have e2 : betaHat y lamT' j = 1 + (y / 2 ^ j - 1) / lamT' := by
    unfold betaHat
    field_simp
    ring
  rw [e1, e2]
  linarith

/-- **`09:186--195`, the three frozen lower bounds.**

"An arbitrary column set of `G` of density `y/2^j` has relative template density
at least `hat beta_j`, where `hat beta_j >= 59/99` (`j=0`), `29/99` (`j=1`),
`14/99` (`j=2`)."

Proved from the single schedule clause `lambda_T >= 99/100` of `09:131` by
`betaHat_mono_lambda` plus the exact values, at the frozen `y = 3/5`. -/
theorem betaHat_ge_frozen {lamT : ℝ} (hlam : 99 / 100 ≤ lamT) :
    59 / 99 ≤ betaHat (3 / 5) lamT 0
      ∧ 29 / 99 ≤ betaHat (3 / 5) lamT 1
      ∧ 14 / 99 ≤ betaHat (3 / 5) lamT 2 := by
  obtain ⟨e0, e1, e2⟩ := betaHat_frozen_values
  refine ⟨?_, ?_, ?_⟩
  · rw [← e0]
    exact betaHat_mono_lambda (by norm_num) (by norm_num) hlam
  · rw [← e1]
    exact betaHat_mono_lambda (by norm_num) (by norm_num) hlam
  · rw [← e2]
    exact betaHat_mono_lambda (by norm_num) (by norm_num) hlam

/-- **Statement pole (the `j = 2` rung is the binding one).**  The margin of the
`j = 2` *numerator* comparison is exactly `hat beta_2 - 9/64 = 5/6336 < 1/1267`,
and the scheduled `q x_T <= 4/25025` of `06:924--933` sits strictly below it, so
`eq:reference-profile-gates` at `j = 2` is a genuine finite comparison and not a
formality.

Two conventions are kept apart here.  `5/6336` is the margin driving the
*sufficient* condition `referenceProfileGates_of_margins` (which replaces
`(b - x)/(1 - x)` by `b - x`), **not** the exact admissible bound on `x_2`: the
frozen paper's own exact bound is `1/1089` (`06:918--920`, "the smallest of the
three admissible upper bounds on `x_j` is `1/1089 > 4/25025`, attained when
`j = 2`"), and `5/6336 ~ 7.89e-4 < 1/1089 ~ 9.18e-4`.  So the direction taken
here is the conservative one: a larger `x_2` breaks the sufficient condition
first and the frozen gate only later, and nothing is over-claimed.  `j = 2` is
the binding rung under both conventions. -/
theorem betaHat_rung2_margin :
    betaHat (3 / 5) (99 / 100) 2 - 9 / 64 = 5 / 6336
      ∧ (4 : ℝ) / 25025 < 5 / 6336 := by
  refine ⟨?_, by norm_num⟩
  simp only [betaHat]
  norm_num

/-- **`eq:reference-profile-gates` (`09:143--149`).**

"Impose the exact balancing conditions `ceil(s(hat beta_j - x_j)/(1 - x_j)) >=
p_j`, `j = 0,1,2`", with `p_j = blockTarget s j` and `x_j = rowDensity s j b_T`
the banked rung scalars of `08:170--172`.  Transcribed as a predicate and never
asserted.  The ceiling is `Nat.ceil`, matching the banked `rawLowGates`
convention (a weakening of the frozen integer ceiling on negative arguments and
an equality on the legal range). -/
def referenceProfileGates (s bT : ℕ) (y lamT : ℝ) : Prop :=
  ∀ j : ℕ, j ≤ 2 →
    blockTarget s j ≤
      (⌈(s : ℝ) * (betaHat y lamT j - rowDensity s j bT) /
        (1 - rowDensity s j bT)⌉₊ : ℝ)

/-- **Aux A6a (a proved sufficient condition for the gates).**

If at every rung the frozen fraction `9/(16 . 2^j)` clears the row loss `x_j`
inside `hat beta_j`, then the exact ceiling comparison holds.  This is the
elementary step `(b - x)/(1 - x) >= b - x` for `0 <= x < 1`, followed by
`Nat.le_ceil`; it is what makes the frozen slack computation of `09:189--195`
into a check, and it is general in `s`, `b_T`, `y` and `lambda_T`. -/
theorem referenceProfileGates_of_margins {s bT : ℕ} {y lamT : ℝ}
    (hx0 : ∀ j : ℕ, j ≤ 2 → 0 ≤ rowDensity s j bT)
    (hx1 : ∀ j : ℕ, j ≤ 2 → rowDensity s j bT < 1)
    (hm : ∀ j : ℕ, j ≤ 2 →
      9 / (16 * 2 ^ j) + rowDensity s j bT ≤ betaHat y lamT j) :
    referenceProfileGates s bT y lamT := by
  intro j hj
  have hx0' := hx0 j hj
  have hx1' := hx1 j hj
  have hmj := hm j hj
  have hpos : (0 : ℝ) < 1 - rowDensity s j bT := by linarith
  have h9 : (0 : ℝ) < 9 / (16 * 2 ^ j) := by positivity
  have hbx : 9 / (16 * 2 ^ j) ≤ betaHat y lamT j - rowDensity s j bT := by linarith
  have hdiv : 9 / (16 * 2 ^ j)
      ≤ (betaHat y lamT j - rowDensity s j bT) / (1 - rowDensity s j bT) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hbt : blockTarget s j = (s : ℝ) * (9 / (16 * 2 ^ j)) := by
    unfold blockTarget widthI
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    field_simp
  have hstep : blockTarget s j
      ≤ (s : ℝ) * ((betaHat y lamT j - rowDensity s j bT) / (1 - rowDensity s j bT)) := by
    rw [hbt]
    exact mul_le_mul_of_nonneg_left hdiv hs0
  refine le_trans hstep ?_
  refine le_trans (le_of_eq ?_) (Nat.le_ceil _)
  ring

/-- **Non-vacuity (tier 2): the frozen gates are inhabited at the banked legal
tier.**

`eq:reference-profile-gates` holds at `s = 2^340`, `b_T = 512`, at the frozen
`y = 3/5` and at the frozen template floor `lambda_T = 99/100`.  All three
ceiling comparisons are checked, and the site is the **same** legal tier the
reference-lemma probe `wrapperReference_fires_at_banked_tier` already uses
(`w_S = 340`, `b_T = 512`), so no second parameter regime is introduced.

Both **computable** clauses of `eq:hard-seed-width-gates` (`06:264--268`) are
met at this pair, and it also respects the defining shape of `b_T`, which is
what makes the tier legal rather than merely convenient:

* `16 | (s/4)` -- the second gate clause -- holds because `s/4 = 2^338`;
* `log_2 s < b_T` -- the third gate clause -- is `340 < 512`;
* separately from the gate, `b_T = 2^{j_49(k_T)}` (`06:238--242`, the
  *definition* of `b_T` and **not** a clause of `eq:hard-seed-width-gates`) is
  a **power of two**, and `512 = 2^9` is one -- the discipline a value such as
  `40` silently breaks.

The gate's remaining clause `k_T = log_2(s/4) >= m_HS` is **not** met here and
cannot be checked at all: `m_HS` is the `Nat.sInf` of `06:250--253`, which the
frozen paper deliberately never evaluates.  It is therefore deferred, exactly
where it belongs, to the abstract hypothesis `hmHS : mHS <= 338` of the sibling
probe `wrapperReference_fires_at_banked_tier`, and is not asserted by this
instance.

The instance is **not** degenerate: the three row losses
`x_j = (s/2^j) 2^{-b_T} = 2^{-172-j}` are strictly positive, so the ceiling
comparisons are genuine.  The margin computation is carried out through the
explicit bound `x_j <= 2^{-20}` rather than by evaluating `2^512`: the smallest
frozen slack is `hat beta_2 - 9/64 = 5/6336` (`betaHat_rung2_margin`), which
`2^{-20}` clears by a factor above `800`.  No parameter may be
read out of the instance: the schedule fixes `s` and `b_T` by
`s = 2^{ceil(B_s u^2)}` and `b_T = 2^{j_49(k_T)}`, not by this choice. -/
theorem referenceProfileGates_legal_instance :
    referenceProfileGates (2 ^ 340) 512 (3 / 5) (99 / 100)
      ∧ (340 : ℕ) < 512
      ∧ 0 < rowDensity (2 ^ 340) 2 512 := by
  have hcast : ((2 ^ 340 : ℕ) : ℝ) = (2 : ℝ) ^ 340 := by push_cast; ring
  have hkey : (2 : ℝ) ^ 340 * (1 / 2 ^ 512) ≤ 1 / 2 ^ 20 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (2 : ℝ) ^ 340 * 2 ^ 20 = 2 ^ 360 := by rw [← pow_add]
    have h2 : (2 : ℝ) ^ 360 ≤ 2 ^ 512 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    rw [h1, one_mul]
    exact h2
  have hrow : ∀ j : ℕ, rowDensity (2 ^ 340) j 512 ≤ 1 / 2 ^ 20 := by
    intro j
    have hjpos : (0 : ℝ) < 2 ^ j := by positivity
    have hj1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hstep : (2 : ℝ) ^ 340 / 2 ^ j ≤ 2 ^ 340 := by
      rw [div_le_iff₀ hjpos]
      exact le_mul_of_one_le_right (by positivity) hj1
    have hmono : (2 : ℝ) ^ 340 / 2 ^ j * (1 / 2 ^ 512)
        ≤ (2 : ℝ) ^ 340 * (1 / 2 ^ 512) :=
      mul_le_mul_of_nonneg_right hstep (by positivity)
    unfold rowDensity widthI xTdepth
    rw [hcast]
    exact le_trans hmono hkey
  have hpos : ∀ j : ℕ, (0 : ℝ) < rowDensity (2 ^ 340) j 512 := by
    intro j
    unfold rowDensity widthI xTdepth
    rw [hcast]
    positivity
  have hsmall : (1 : ℝ) / 2 ^ 20 = 1 / 1048576 := by norm_num
  refine ⟨?_, by norm_num, hpos 2⟩
  obtain ⟨e0, e1, e2⟩ := betaHat_frozen_values
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  rw [hsmall] at h0 h1 h2
  refine referenceProfileGates_of_margins (fun j _ => (hpos j).le) (fun j _ => ?_)
    (fun j hj => ?_)
  · have := hrow j
    have hlt : (1 : ℝ) / 2 ^ 20 < 1 := by norm_num
    linarith
  · interval_cases j
    · rw [e0]
      have hc : (9 : ℝ) / (16 * 2 ^ (0 : ℕ)) = 9 / 16 := by norm_num
      rw [hc]
      linarith
    · rw [e1]
      have hc : (9 : ℝ) / (16 * 2 ^ (1 : ℕ)) = 9 / 32 := by norm_num
      rw [hc]
      linarith
    · rw [e2]
      have hc : (9 : ℝ) / (16 * 2 ^ (2 : ℕ)) = 9 / 64 := by norm_num
      rw [hc]
      linarith

/-! ## §5  `lem:wrapper-reference` (`09:151--236`)

The exact half is `D_referenceG` above.  The three-rung half is the same
inherited General Hard Seed call the Section-8 block makes, at row density `x_T`
instead of `x_N`; the banked facade is consumed by pin and the two binders it
leaves open stay open. -/

/-- **Aux A9a (`08:166`: the auxiliary Stage-3 density is a legal density).**
`x_T = 2^{-b_T} in (0, 1]` for every depth `b_T`.  General; needed because the
bracket family is only defined at legal densities. -/
theorem xTdepth_mem (bT : ℕ) : 0 < xTdepth bT ∧ xTdepth bT ≤ 1 := by
  unfold xTdepth
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

/-- **Aux A9b (the three rung bracket families are nonempty).**

`Dfamily` is a `Nat.sInf` and collapses to `0` on the empty family, so every
family lower bound in this section carries a nonemptiness side condition.  At
the reference row density `x_T` and at any legal `y` it is discharged outright
from the banked `bracketGE.nonempty`: a nonempty row carrier is all it takes.
General in both carriers, in `b_T` and in `y`. -/
theorem wrapperReference_bracket_nonempty {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (bT : ℕ) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) :
    ∀ j : ℕ, j ≤ 2 → (bracketGE Rw Cl 1 (xTdepth bT) (y / 2 ^ j)).Nonempty := by
  classical
  haveI : DecidableEq Rw := Classical.decEq _
  intro j _
  have hz1 : y / 2 ^ j ≤ 1 := by
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    exact le_trans (div_le_self (le_of_lt hy0) hp) hy1
  exact bracketGE.nonempty 1 (xTdepth bT) (y / 2 ^ j) (xTdepth_mem bT).2 hz1 hRw

/-- **`lem:wrapper-reference`, second clause (`09:174--235`), conditional.**

"Applying `eq:regular-density-transfer` to `phi_R` and `phi_C`, and then using
transpose symmetry, yields `comp<G,1,x_T,y/2^j> >= D_2 + log_2 I_j = C-1-j`.
The parameter schedule checks `eq:reference-profile-gates` for all three values
of `j`.  Taking the minimum proves the claim."

Every hypothesis is the one the banked Section-8 threading carries, at row
density `x_T = xTdepth b_T`:

* `hwS`, `hwSbT` are the two arithmetic consequences of
  `eq:hard-seed-width-gates` (`06:264--269`) that the facade demands;
* `hD2` is the Stage-2 exact-complexity certificate `D_2 = comp(M_2^T)`;
* `hrob`, `hD3` are the frozen `09:211--213` -- "The Stage-2 certificate gives
  that `M_2^T` is `(1/10, b_T)`-robust and has complexity `D_2 >= 3`" -- and are
  **open** (ledger `STAGE2-MODULE-001`);
* `hne` is the bracket nonemptiness the family infimum needs (`Dfamily` is an
  `sInf` over `ℕ` and returns `0` on the empty family);
* `hland` is the geometric landing of `09:196--204`, **open**, and is the only
  place the reference geometry enters.

Nothing of the facade is restated: the rung call, the three rung
identifications, and the passage to the family infimum are all consumed. -/
theorem wrapperReference_rungs {Rw Cl Rw₂ Cl₂ : Type u} [Fintype Rw] [Fintype Cl]
    [Fintype Rw₂] [Fintype Cl₂]
    (Gmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    (Dsrc a r₂ wS bT : ℕ) (y : ℝ)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE Rw Cl 1 (xTdepth bT) (y / 2 ^ j)).Nonempty)
    (hland : ∀ jr : ℕ, jr ≤ 2 → RungLanding Gmat M2T wS jr bT (xTdepth bT) y) :
    cBlock Dsrc a r₂ wS - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) y := by
  have h5 : 5 ≤ mHS.{u} := five_le_mHS.{u}
  refine lowProfile_of_frozen_rungs Gmat (cBlock Dsrc a r₂ wS - 1) (xTdepth bT) y ?_
  intro j hj
  obtain ⟨hjw, hm, hmb, hb⟩ :=
    rungCall_side_conditions (wS := wS) (bT := bT) hwS hwSbT hj
  have hwit := rungSeedWitness_of_landing_and_certificate Gmat M2T
    (wS := wS) (jr := j) (bT := bT) (x := xTdepth bT) (y := y)
    hjw hm hrob hb hD3 hmb (hland j hj)
  have hfam := Dfamily_ge_of_seed_witnesses Gmat (hne j hj) hwit
  have hid := (rung_schedule_identity Dsrc a r₂ wS j hjw).2
  rw [← hD2] at hfam
  omega

/-- **`lem:wrapper-reference` (`09:151--162`), both clauses.**

"Under `eq:hard-seed-width-gates` and `eq:reference-profile-gates`, assume the
exact protected Stage-4 identity `comp N = C` from
`cor:exact-protected-stage4`.  In the `NO` case, `comp G = C`,
`Lambda_3(G,1,x_T,y) >= C - 1`."

The exact clause is supplied as the binder `hDG`, because at the construction it
is the **theorem** `D_referenceG_frozen` composed with the banked
`D_protectedAFrozen` and `cor:exact-protected-stage4`, and stating it abstractly
here would fix a carrier this general statement does not have.  The three-rung
clause is `wrapperReference_rungs`. -/
theorem wrapperReference {Rw Cl Rw₂ Cl₂ : Type u} [Fintype Rw] [Fintype Cl]
    [Fintype Rw₂] [Fintype Cl₂]
    (Gmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    (Dsrc a r₂ wS bT : ℕ) (y : ℝ)
    (hDG : D Gmat = cBlock Dsrc a r₂ wS)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE Rw Cl 1 (xTdepth bT) (y / 2 ^ j)).Nonempty)
    (hland : ∀ jr : ℕ, jr ≤ 2 → RungLanding Gmat M2T wS jr bT (xTdepth bT) y) :
    D Gmat = cBlock Dsrc a r₂ wS
      ∧ cBlock Dsrc a r₂ wS - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) y :=
  ⟨hDG, wrapperReference_rungs Gmat M2T Dsrc a r₂ wS bT y hwS hwSbT hD2 hrob hD3
    hne hland⟩

/-- **Non-vacuity: `lem:wrapper-reference` fires at the banked legal tier.**

The strongest available form of the consistency check for the reference lemma:
every hypothesis of `wrapperReference` *except* the ones open by design (`hDG`,
which at the construction is the theorem `D_referenceG_frozen` composed with
`cor:exact-protected-stage4`; `hD2`; `hrob`/`hD3`; and the geometric landing
`hland`) is discharged here at the banked tier `w_S = 340`, `b_T = 512`, at the
frozen `y = 3/5` and on carriers of cardinality `2^340`, and the conclusion is
produced.  So the bundle is not merely unrefuted: it is jointly satisfiable, and
the lemma is not green-because-vacuous.

The single abstract clause `mHS <= 338` is the scale hypothesis the schedule's
own hard-seed window supplies (`eq:hard-seed-width-gates`, `06:264--269`:
`k_T = log_2(s/4) >= m_HS`, and `log_2(2^340/4) = 338`); it is the same clause
the banked Section-8 threading probe carries, and it is *not* a numeric claim
about `m_HS`. -/
theorem wrapperReference_fires_at_banked_tier
    (Gmat : Fin (2 ^ 340) → Fin (2 ^ 340) → Bool)
    {Rw₂ Cl₂ : Type} [Fintype Rw₂] [Fintype Cl₂] (M2T : Rw₂ → Cl₂ → Bool)
    (Dsrc a r₂ : ℕ)
    (hmHS : mHS.{0} ≤ 338)
    (hDG : D Gmat = cBlock Dsrc a r₂ 340)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((512 : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding Gmat M2T 340 jr 512 (xTdepth 512) (3 / 5 : ℝ)) :
    D Gmat = cBlock Dsrc a r₂ 340
      ∧ cBlock Dsrc a r₂ 340 - 1 ≤ LambdaGE Gmat 1 (xTdepth 512) (3 / 5 : ℝ) := by
  have hcard : 1 ≤ Fintype.card (Fin (2 ^ 340)) := by
    rw [Fintype.card_fin]
    exact Nat.one_le_two_pow
  exact wrapperReference Gmat M2T Dsrc a r₂ 340 512 (3 / 5 : ℝ) hDG (by omega)
    (by norm_num) hD2 hrob hD3
    (wrapperReference_bracket_nonempty 512 (by norm_num) (by norm_num) hcard)
    hland

/-! ## §6  `thm:first-wrapper` (`09:238--272`), with its two deferred halves
named -/

/-- **`09:107`.**  `U = Int_q(N)` at the scale-alignment width `q = 2^r`. -/
def wrapperU {Rw Cl : Type*} (Nmat : Rw → Cl → Bool) (r : ℕ) :
    Fin (2 ^ r) × Rw → (Fin (2 ^ r) → Cl) → Bool :=
  interlaceFun Nmat (2 ^ r)

/-- **`09:268`.**  `W = U^T`, the common-threshold matrix; this is the vendored
`EthBridge.Rnext` at the inner width, so the banked one-copy transpose transport
applies to it unchanged. -/
def wrapperW {Rw Cl : Type*} (Nmat : Rw → Cl → Bool) (r : ℕ) :
    (Fin (2 ^ r) → Cl) → Fin (2 ^ r) × Rw → Bool :=
  EthBridge.Rnext Nmat (2 ^ r)

/-- **Aux A7a.**  `U` is the interlace at the named width `q = 2^r`. -/
theorem wrapperU_eq_interlace_at_width {Rw Cl : Type*} (Nmat : Rw → Cl → Bool)
    (r : ℕ) : wrapperU Nmat r = interlaceFun Nmat (scaleAlignWidth r) := rfl

/-- **Aux A7b (`09:268`: `W` really is the transpose of `U`).**  Entrywise, and
by `rfl`: no relabelling of either carrier is inserted between them. -/
@[simp] theorem wrapperW_apply {Rw Cl : Type*} (Nmat : Rw → Cl → Bool) (r : ℕ)
    (c : Fin (2 ^ r) → Cl) (b : Fin (2 ^ r) × Rw) :
    wrapperW Nmat r c b = wrapperU Nmat r b c := rfl

/-- **`eq:common-exact` from `eq:wrapper-u-exact`, the transposition half.**
`comp W = comp U`, by the vendored `lem:transposeComp` consumed by pin. -/
theorem D_wrapperW {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r : ℕ) :
    D (wrapperW Nmat r) = D (wrapperU Nmat r) :=
  comp_transpose (wrapperU Nmat r)

/-- **`09:1789--1792`, the `YES`-side interlace bound.**  "The standard interlace
protocol identifies the outer coordinate in `r` bits and then runs an optimal
protocol for `N`, so `comp U <= C + r`", and `09:270--271`, "the standard
interlace protocol adds exactly `r` bits to the protocol for `N`".  The banked
`powerOfTwoInterlace_upper` is exactly this selector, at the power-of-two width;
consumed by pin, general in `N` and `r`. -/
theorem wrapperU_yes_upper {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r : ℕ) :
    D (wrapperU Nmat r) ≤ D Nmat + r :=
  powerOfTwoInterlace_upper Nmat r

/-- **Aux A8 (the frozen rung display is transcribed without truncation).**

`eq:wrapper-u-low` prints `>= C + r - 1 - j`.  Two things are checked, and the
frozen side conditions `3 <= C_W` (`09:240`) and `j <= 2` are what make the
second one true: the printed form is *equivalent* to the subtraction-free
`C_W <= j + 1 + d` used below, and the double subtraction is **exact**, i.e.
`(C_W - 1 - j) + (1 + j) = C_W`, so no natural subtraction is being taken
outside its legal range and no clause is weakened.  General in `C_W`, `j`,
`d`. -/
theorem wrapperLow_subtraction_free {CW j d : ℕ} (h3 : 3 ≤ CW) (hj : j ≤ 2) :
    ((CW - 1 - j ≤ d) ↔ (CW ≤ j + 1 + d)) ∧ CW - 1 - j + (1 + j) = CW := by
  omega

/-- **`eq:wrapper-u-exact` (`09:261`), derived (`09:1793--1796`).**

"Applying `eq:wrapper-u-dense` to the full matrix gives the reverse inequality
and proves `eq:wrapper-u-exact`."

Both directions are proved here.  Upper: the interlace selector
(`wrapperU_yes_upper`) together with `comp N = C`.  Lower: `Dfamily` is a
minimum over members, the full matrix is a member of the one-copy bracket family
(banked `bracketGE.nonempty` supplies it), and the one-copy interlace costs
nothing extra (`interlace_selector_upper` at `p = 1`, `clog 2 1 = 0`).  So
`eq:wrapper-u-dense` is a lower bound on `comp U` itself. -/
theorem wrapperU_exact_of_dense {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ : ℝ}
    (hN : D Nmat = C) (hθ1 : θ ≤ 1) (hδ1 : 1 - δU ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw)
    (hdense : C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)) :
    D (wrapperU Nmat r) = C + r := by
  classical
  haveI : DecidableEq (Fin (2 ^ r) × Rw) := Classical.decEq _
  have hcard : 1 ≤ Fintype.card (Fin (2 ^ r) × Rw) := by
    have hq : 0 < 2 ^ r := pow_pos (by norm_num) r
    have : Nonempty Rw := Fintype.card_pos_iff.mp hRw
    exact Fintype.card_pos_iff.mpr ⟨(⟨0, hq⟩, Classical.arbitrary Rw)⟩
  have hne := bracketGE.nonempty (X := Fin (2 ^ r) × Rw) (Y := Fin (2 ^ r) → Cl)
    1 (1 - δU) θ hδ1 hθ1 hcard
  have hfam := familyComplexity_le_ambient (interlaceFun (wrapperU Nmat r) 1) hne
  have hone : D (interlaceFun (wrapperU Nmat r) 1) ≤ D (wrapperU Nmat r) := by
    have h1 := interlace_selector_upper (wrapperU Nmat r) 1 (le_refl 1)
    rwa [Nat.clog_one_right, Nat.add_zero] at h1
  have hlower : C + r ≤ D (wrapperU Nmat r) :=
    le_trans hdense (le_trans hfam hone)
  have hupper : D (wrapperU Nmat r) ≤ C + r := by
    have := wrapperU_yes_upper Nmat r
    rwa [hN] at this
  omega

/-- **Anti-over-strength readout: `eq:wrapper-u-dense` is saturated, not
excessive.**

Under the same hypotheses, the dense binder does not demand more than the
ambient matrix can supply -- it demands exactly the maximum: the bracket family
complexity is *equal* to `C + r`.  This is the check that a hypothesis bundle
whose green build proves nothing would fail: `Dfamily` is a minimum over
members, so it is bounded above by `comp U`, which `hN` and the interlace
selector pin at `C + r`.  Consequently `hDenseRung` and `hN` cannot be jointly
contradictory for a magnitude reason, and the frozen `eq:wrapper-u-dense` is a
saturation statement about the interlace rather than an over-demand. -/
theorem firstWrapper_dense_is_saturated {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ : ℝ}
    (hN : D Nmat = C) (hθ1 : θ ≤ 1) (hδ1 : 1 - δU ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw)
    (hdense : C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)) :
    Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ) = C + r := by
  classical
  haveI : DecidableEq (Fin (2 ^ r) × Rw) := Classical.decEq _
  have hexact := wrapperU_exact_of_dense Nmat r C hN hθ1 hδ1 hRw hdense
  have hcard : 1 ≤ Fintype.card (Fin (2 ^ r) × Rw) := by
    have hq : 0 < 2 ^ r := pow_pos (by norm_num) r
    have : Nonempty Rw := Fintype.card_pos_iff.mp hRw
    exact Fintype.card_pos_iff.mpr ⟨(⟨0, hq⟩, Classical.arbitrary Rw)⟩
  have hne := bracketGE.nonempty (X := Fin (2 ^ r) × Rw) (Y := Fin (2 ^ r) → Cl)
    1 (1 - δU) θ hδ1 hθ1 hcard
  have hfam := familyComplexity_le_ambient (interlaceFun (wrapperU Nmat r) 1) hne
  have hone : D (interlaceFun (wrapperU Nmat r) 1) ≤ D (wrapperU Nmat r) := by
    have h1 := interlace_selector_upper (wrapperU Nmat r) 1 (le_refl 1)
    rwa [Nat.clog_one_right, Nat.add_zero] at h1
  omega

/-- **`eq:common-exact`--`eq:common-low` (`09:14--23`) from the three
`U`-clauses (`09:1798--1804`).**

"Finally set `W = U^T` and `C_W = C + r`.  Transposition exchanges the row and
column restrictions in each one-copy bracket.  Therefore `eq:wrapper-u-dense`
becomes `comp<W,1,theta,1-delta_U> >= C_W`, while the three clauses in
`eq:wrapper-u-low` become `Lambda_3(W,1,theta,y) >= C_W - 1`.  Together with
`comp W = C_W`, these are `eq:common-exact`--`eq:common-low`."

All three are proved here.  The exchange of restrictions is the vendored
one-copy transpose transport `EthBridge.dfamily_one_transpose`, consumed by pin
at each of the four densities the frozen display needs, and the passage from the
three transported rungs to `Lambda_3` is the banked
`lowProfile_of_frozen_rungs`.  The orientation is preserved literally: the
`U`-side bracket carries `(1 - delta_U, theta)` and the `W`-side bracket
`(theta, 1 - delta_U)`, i.e. the row slot of one is the column slot of the
other. -/
theorem commonThreshold_of_wrapper {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r CW : ℕ) {δU θ y : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hexact : D (wrapperU Nmat r) = CW)
    (hdense : CW ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ))
    (hlow : ∀ j : ℕ, j ≤ 2 → CW ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ)) :
    D (wrapperW Nmat r) = CW
      ∧ CW ≤ Dfamily (interlaceFun (wrapperW Nmat r) 1)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 1 θ (1 - δU))
      ∧ CW - 1 ≤ LambdaGE (wrapperW Nmat r) 1 θ y := by
  classical
  have hqpos : 0 < 2 ^ r := pow_pos (by norm_num) r
  have hRwne : Nonempty Rw := Fintype.card_pos_iff.mp hRw
  have hClne : Nonempty Cl := Fintype.card_pos_iff.mp hCl
  have hcardRow : 1 ≤ Fintype.card (Fin (2 ^ r) × Rw) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, hqpos⟩, Classical.arbitrary Rw)⟩
  have hcardCol : 1 ≤ Fintype.card (Fin (2 ^ r) → Cl) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Classical.arbitrary Cl⟩
  -- the transpose transport, at an arbitrary legal column density
  have htrans : ∀ z : ℝ, 0 < z → z ≤ 1 →
      Dfamily (interlaceFun (wrapperW Nmat r) 1)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 1 θ z)
        = Dfamily (interlaceFun (wrapperU Nmat r) 1)
          (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 z θ) := by
    intro z hz0 hz1
    exact EthBridge.dfamily_one_transpose (wrapperU Nmat r) hz0 hz1 hθ0 hθ1
      hcardRow hcardCol
  refine ⟨by rw [D_wrapperW, hexact], ?_, ?_⟩
  · rw [htrans (1 - δU) hδ0 hδ1]
    exact hdense
  · refine lowProfile_of_frozen_rungs (wrapperW Nmat r) (CW - 1) θ y ?_
    intro j hj
    have hz0 : 0 < y / 2 ^ j := by positivity
    have hz1 : y / 2 ^ j ≤ 1 := by
      have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hle : y / 2 ^ j ≤ y := div_le_self (le_of_lt hy0) hp
      exact le_trans hle hy1
    rw [htrans (y / 2 ^ j) hz0 hz1]
    have := hlow j hj
    omega

/-- **`thm:first-wrapper` (`09:238--272`), as a closed conditional.**

Hypotheses, in the frozen order of `09:240--258`:

* `hC : 3 <= C` -- the frozen "Assume `C >= 3`" of `09:240`;
* `hN : comp N = C` -- "the exact identity `comp N = C`" (`09:242`), i.e.
  `cor:exact-protected-stage4`;
* the density guards, which are the scheduled positivity of `eq:q-deltaU` and
  `eq:Q-theta-choice` (`0 < theta <= 1`, `0 < 1 - delta_U <= 1`) and the frozen
  `y = 3/5 in (0,1]`;
* the carrier nonemptiness the bracket families need;
* `hDenseRung` -- `eq:wrapper-u-dense`, whose proof is the five blocks
  `09:335--1781` (GAP-EXPOSED 1);
* `hLowRungs` -- `eq:wrapper-u-low`, whose proof is `sec:wrapper-low-rungs`,
  `09:274--334` (GAP-EXPOSED 1), in the subtraction-free reading certified by
  `wrapperLow_subtraction_free`.

Conclusions: the three `U`-clauses `eq:wrapper-u-exact`, `eq:wrapper-u-dense`,
`eq:wrapper-u-low`, and then the three output-contract clauses
`eq:common-exact`, `eq:common-dense`, `eq:common-low` at `C_W = C + r` -- which
is exactly what `09:23` says the next section consumes.  Of these six, the first
and the last three are **derived** here; the second and third are the two named
binders, returned so that the theorem is the frozen statement and not a
fragment. -/
theorem firstWrapper {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ y : ℝ}
    (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hDenseRung : C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ))
    (hLowRungs : ∀ j : ℕ, j ≤ 2 →
      C + r ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat r) 1)
        (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ)) :
    D (wrapperU Nmat r) = C + r
      ∧ C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
          (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)
      ∧ (∀ j : ℕ, j ≤ 2 →
          C + r ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat r) 1)
            (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ))
      ∧ (∀ j : ℕ, j ≤ 2 →
          C + r - 1 - j ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
            (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ))
      ∧ D (wrapperW Nmat r) = C + r
      ∧ C + r ≤ Dfamily (interlaceFun (wrapperW Nmat r) 1)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 1 θ (1 - δU))
      ∧ C + r - 1 ≤ LambdaGE (wrapperW Nmat r) 1 θ y := by
  have hexact : D (wrapperU Nmat r) = C + r :=
    wrapperU_exact_of_dense Nmat r C hN hθ1 hδ1 hRw hDenseRung
  obtain ⟨h1, h2, h3⟩ :=
    commonThreshold_of_wrapper Nmat r (C + r) hθ0 hθ1 hδ0 hδ1 hy0 hy1 hRw hCl
      hexact hDenseRung hLowRungs
  refine ⟨hexact, hDenseRung, hLowRungs, ?_, h1, h2, h3⟩
  intro j hj
  exact ((wrapperLow_subtraction_free (CW := C + r) (by omega) hj).1).2
    (hLowRungs j hj)

/-- **Statement pole for `thm:first-wrapper`.**  The exact clause is not
automatic: at the legal constant matrix over two-element carriers the whole
interlace is constant, so `comp U = 0`, which misses `C + r >= 3` for every
legal `C >= 3`.  The value therefore comes from `hN` and the two deferred family
bounds, and cannot be read off the interlace shape. -/
theorem firstWrapper_not_automatic (r : ℕ) :
    D (wrapperU (fun (_ : Bool) (_ : Bool) => false) r) = 0 := by
  have hconst : wrapperU (fun (_ : Bool) (_ : Bool) => false) r
      = fun _ _ => false := rfl
  rw [hconst]
  exact D_const false

/-- **Schedule arithmetic (i): the row threshold of `eq:Q-theta-choice` is
antitone in the interlace count `Q`.**

The frozen schedule sets `theta = delta/(16 Q)` (`06:533`) at `delta = 1/10`
(`06:539`).  Nothing else about `Q` is used here: as a function of a positive
real `Q` the scheduled threshold is antitone, so a *larger* admissible `Q`
produces a *smaller* `theta`.  This is the lemma that converts any **lower**
bound on the admissible `Q` into an **upper** bound on the scheduled `theta`;
it fixes no such bound itself, and in particular asserts no schedule floor.
The floor the frozen schedule actually forces is recorded in
`scheduleTheta_guards`.  Proved in general rather than checked at one
numeral. -/
theorem scheduleTheta_antitone {Q Q' : ℝ} (hQ : 0 < Q) (hQQ' : Q ≤ Q') :
    (1 : ℝ) / 10 / (16 * Q') ≤ 1 / 10 / (16 * Q) := by
  have hQ' : (0 : ℝ) < Q' := lt_of_lt_of_le hQ hQQ'
  rw [div_div, div_div, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **Schedule arithmetic (ii): every scheduled `theta` clears the density
guards of `thm:first-wrapper`, under the weakest bound on `Q` the frozen
maximum makes unconditional.**

`eq:Q-theta-choice` (`06:530--533`) fixes
`Q_0 = max{8 bout/(delta delta_U), 8/delta, 16}` and takes `Q` to be the least
power of two at least `Q_0`.  The constant `16` is one term of that maximum, so
the hypothesis `16 <= Q` used here holds for **every** admissible schedule
whatever the remaining data -- which is exactly why it, and not a larger
number, is the hypothesis.

`16` is **not** the schedule floor, and `1/2560` is **not** an attained value of
`theta`.  With `delta = 1/10` (`06:539`) the term `8/delta = 80` of the same
maximum already gives `Q_0 >= 80`, so the least power of two at least `Q_0`
satisfies `Q >= 128` unconditionally; and `bout` is instance data, not a
constant, so the first term pushes `Q` higher still on any actual input.  The
bound `(1/10)/(16 * 16) = 1/2560` proved below is therefore a **ceiling no
admissible schedule reaches**.  The usable instantiation of this lemma is at
`Q >= 128`, where `scheduleTheta_antitone` turns it into
`theta <= (1/10)/(16 * 128)`; that is the bound the consistency and firing
probes below carry, and neither of them pins a value of `theta`.

Both guards `0 < theta` and `theta <= 1` that `firstWrapper` demands follow for
every admissible `Q`. -/
theorem scheduleTheta_guards {Q : ℝ} (hQ : 16 ≤ Q) :
    0 < (1 : ℝ) / 10 / (16 * Q)
      ∧ (1 : ℝ) / 10 / (16 * Q) ≤ 1 / 10 / (16 * 16)
      ∧ (1 : ℝ) / 10 / (16 * 16) = 1 / 2560
      ∧ (1 : ℝ) / 10 / (16 * Q) ≤ 1 := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hfloor : (1 : ℝ) / 10 / (16 * Q) ≤ 1 / 10 / (16 * 16) :=
    scheduleTheta_antitone (by norm_num) hQ
  have hval : (1 : ℝ) / 10 / (16 * 16) = 1 / 2560 := by norm_num
  refine ⟨div_pos (by norm_num) (by linarith), hfloor, hval, ?_⟩
  rw [hval] at hfloor
  linarith

/-- **Schedule arithmetic (iii): the finite gate of `06:547` clears the
`delta_U` guards.**

The frozen text imposes the finite gate `delta_U <= 1/200` (`06:547`), and
`eq:q-deltaU` (`06:517`) sets `delta_U = eta_R/(16 q)`, which is positive
because the mass schedule fixes `0 < eta_R` (`06:228`).  For every
`delta_U` in that range the two guards `0 < 1 - delta_U` and `1 - delta_U <= 1`
that `firstWrapper` demands hold; again this is proved for the whole admissible
range, not at one numeral. -/
theorem scheduleDeltaU_guards {δU : ℝ} (hpos : 0 < δU) (hgate : δU ≤ 1 / 200) :
    0 < 1 - δU ∧ 1 - δU ≤ 1 := ⟨by linarith, by linarith⟩

/-- **Hypothesis-consistency probe for `thm:first-wrapper` (tier 2).**

Every *numeric* hypothesis of `firstWrapper` holds simultaneously in a regime
the **frozen parameter schedule** admits -- read off `06-parameter-schedule.tex`,
never off the reader artifact.

`theta` is a **binder**, not a value.  `eq:Q-theta-choice` (`06:530--533`) sets
`theta = delta/(16 Q)` with `Q` the least power of two at least
`Q_0 = max{8 bout/(delta delta_U), 8/delta, 16}`; with `delta = 1/10`
(`06:539`) the term `8/delta = 80` forces `Q_0 >= 80` and hence `Q >= 128`
unconditionally, so by `scheduleTheta_antitone` *every* admissible schedule
satisfies `theta <= (1/10)/(16 * 128)`.  That inequality, together with
positivity, is the whole `theta` hypothesis here -- no numeral is pinned,
because the remaining term `8 bout/(delta delta_U)` depends on `bout`, which is
instance data and can force `Q`, and therefore `theta`, arbitrarily far past any
fixed number.  Pinning a numeral would assert a schedule point that no instance
need realise.

The remaining values are the ones the frozen text fixes outright and that were
never in question: `delta_U = 1/200`, the finite gate of `06:547` verbatim ("We
also impose the finite gate `delta_U <= 1/200`"), at its extremal admissible
value; `C = 3`, the floor of `09:240`; `y = 3/5` (`03:216--219`); and both
carriers `Bool`, of cardinality `2 >= 1`.  So the bundle is not contradictory on
its arithmetic side, and the theorem is not green-because-vacuous.

The admissible `theta`-range is itself nonempty -- the second conjunct records
`0 < (1/10)/(16 * 128)`, so the hypotheses of this lemma are satisfiable and it
is not vacuously true of an empty binder.

The two family binders `hDenseRung` and `hLowRungs` are statements about `N`
alone; the bundle contains **no** upper bound on any complexity -- `hN` fixes
`comp N` but the deferred clauses bound *bracket* complexities of the interlace
from below, and `wrapperU_yes_upper` shows the two are compatible whenever
`C + r <= comp N + r`, which `hN` makes an equality.  So no `False` is
derivable from the bundle in this regime. -/
theorem firstWrapper_hypotheses_consistent {θ : ℝ} (hθ0 : 0 < θ)
    (hθQ : θ ≤ 1 / 10 / (16 * 128)) :
    (3 : ℕ) ≤ 3
      ∧ (0 : ℝ) < 1 / 10 / (16 * 128)
      ∧ 0 < θ ∧ θ ≤ 1
      ∧ (0 : ℝ) < 1 - 1 / 200 ∧ (1 : ℝ) - 1 / 200 ≤ 1
      ∧ (0 : ℝ) < 3 / 5 ∧ (3 : ℝ) / 5 ≤ 1
      ∧ 1 ≤ Fintype.card Bool
      ∧ (∀ j : ℕ, j ≤ 2 →
          ((((3 : ℕ) - 1 - j ≤ 5) ↔ ((3 : ℕ) ≤ j + 1 + 5))
            ∧ (3 : ℕ) - 1 - j + (1 + j) = 3)) := by
  obtain ⟨hQpos, -, -, hQle⟩ := scheduleTheta_guards (Q := 128) (by norm_num)
  obtain ⟨hδpos, hδle⟩ :=
    scheduleDeltaU_guards (δU := 1 / 200) (by norm_num) le_rfl
  refine ⟨by norm_num, hQpos, hθ0, le_trans hθQ hQle, hδpos, hδle,
    by norm_num, by norm_num, by simp, ?_⟩
  exact fun j hj =>
    wrapperLow_subtraction_free (CW := 3) (j := j) (d := 5) (by norm_num) hj

/-- **Non-vacuity: the whole bundle of `thm:first-wrapper` fires throughout the
schedule-legal regime.**

The tier-2 probe above checks the arithmetic side in isolation; this checks that
the same regime actually drives `firstWrapper` to its conclusions.  The
quantification over `theta` is **identical** to the probe's -- an arbitrary
positive `theta` bounded by the unconditional schedule ceiling
`(1/10)/(16 * 128)` of `eq:Q-theta-choice` (`06:530--533` with `delta = 1/10`
at `06:539`, whose term `8/delta = 80` forces `Q >= 128`) -- and the binder
appears in both family hypotheses and in all three conclusions, so no clause is
stated at a `theta` that another clause does not use.

Pinned, because the frozen text pins them: `C = 3` (`09:240`),
`delta_U = 1/200` (`06:547`) and `y = 3/5` (`03:216--219`).  At those, the two
deferred family binders yield the three output-contract clauses
`eq:common-exact`--`eq:common-low` of `09:14--23` at `C_W = 3 + r`.  Nothing is
evaluated: the carriers, the matrix, `r` and `theta` all stay general, so this
is an instantiation of the frozen theorem in its scheduled regime and not a
numerical special case of it. -/
theorem firstWrapper_fires_at_scheduled_pair {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Nmat : Rw → Cl → Bool) (r : ℕ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθQ : θ ≤ 1 / 10 / (16 * 128)) (hN : D Nmat = 3)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hDenseRung : 3 + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - 1 / 200) θ))
    (hLowRungs : ∀ j : ℕ, j ≤ 2 →
      3 + r ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat r) 1)
        (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 ((3 : ℝ) / 5 / 2 ^ j)
          θ)) :
    D (wrapperW Nmat r) = 3 + r
      ∧ 3 + r ≤ Dfamily (interlaceFun (wrapperW Nmat r) 1)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 1 θ (1 - 1 / 200))
      ∧ 3 + r - 1 ≤ LambdaGE (wrapperW Nmat r) 1 θ ((3 : ℝ) / 5) := by
  obtain ⟨-, -, -, hQle⟩ := scheduleTheta_guards (Q := 128) (by norm_num)
  obtain ⟨hδpos, hδle⟩ :=
    scheduleDeltaU_guards (δU := 1 / 200) (by norm_num) le_rfl
  obtain ⟨-, -, -, -, h4, h5, h6⟩ :=
    firstWrapper Nmat r 3 le_rfl hN hθ0 (le_trans hθQ hQle) hδpos hδle
      (by norm_num) (by norm_num) hRw hCl hDenseRung hLowRungs
  exact ⟨h4, h5, h6⟩

end EthInapproximability.ParameterizedNP.ScaleAlignOpening
