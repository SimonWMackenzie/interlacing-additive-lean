import EthInapproximability.ParameterizedNP.ScaleAlignOpening
import EthInapproximability.ParameterizedNP.DenseAliceClosure

/-!
# Parameterized NP route: the three one-bit-down rungs of the scale-alignment section

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 274--334** --
  `sec:wrapper-low-rungs`, "The three one-bit-down rungs", opening immediately
  after the statement of `thm:first-wrapper` (`09:273`) and stopping immediately
  before `sec:wrapper-projection-covers` (`09:335`).  The anchors traced here, in
  the order the frozen block prints them:
  * `09:277--283`: "The lower bounds in `eq:wrapper-u-low` do not use
    protected-mass routing.  Fix `j in {0,1,2}`, and put
    `kappa_j = q/2^j`, `beta_j = (y/2^j - (1-g))/g`";
  * `09:284--287`: "Take an arbitrary member of `<U,1,y/2^j,theta>`.  After
    discarding every nonreference row, the retained reference rows have
    normalized density at least `beta_j` among the `q` copies of `G`";
  * `eq:wrapper-reference-count` (label `09:291`, display `09:288--292`) with its
    justification `09:287--295`: "If fewer than
    `ceil(q(beta_j - kappa_j x_T)/(1 - kappa_j x_T))` outer coordinates had
    reference density at least `kappa_j x_T`, the total reference density would
    be below `beta_j`.  Thus `eq:wrapper-reference-count` is a valid lower bound
    on their number";
  * `09:297--302`, the exact margins at `g = 91/92`:
    `beta_0 = 271/455`, `beta_0 - 9/16 = 241/7280`;
    `beta_1 = 19/65`,  `beta_1 - 9/32 = 23/2080`;
    `beta_2 = 64/455`, `beta_2 - 9/64 = 1/29120`;
  * `eq:wrapper-low-simple-gate` (label `09:306`, display `09:304--307`) with
    `09:303` and `09:308--309`: "The single sufficient condition
    `q x_T <= 4/25025` implies, together with the exact ceiling checks retained
    by the construction, that `eq:wrapper-reference-count` is at least
    `9 kappa_j/16`".  Its schedule twin is `eq:wrapper-low-rung-gates`
    (`06:927--934`, label `06:933`), which prints the same two clauses --
    the three exact ceiling comparisons and `q x_T <= 4/25025` -- at the frozen
    `beta_j = ((3/5)/2^j - 1/92)/(91/92)` of `06:922--925`;
  * `09:311--313`: "Project the retained outer column set to any `9 kappa_j/16`
    such coordinates.  Its normalized density remains at least `theta`, by
    specified-coordinate projection";
  * `09:313--324`: "Apply the certified-scale reference stopping lemma,
    `thm:certified-localized-extension`, using its fixed `y_* = 3/5` and the
    substitutions `M = G`, `H = C-1`, `x = x_T`, `t = t_ref`, `r = q/t_ref`,
    `r' = kappa_j/t_ref`, `eps = 0`, `h = theta`, `a^sharp = 0`";
  * `09:325--327`: "The equality `eq:reference-all-columns` verifies the
    orientation; the reference restriction is a full product, so its
    balancedness error is exactly zero; and `q/4 >= t_ref` makes all three values
    of `r'` legal";
  * `09:328--333`: "The conclusion is precisely
    `comp<U,1,y_*/2^j,theta> >= C + log_2 q - 1 - j`.  This proves
    `eq:wrapper-u-low`."
* **Second autoformalization anchor (`cc-t7r`, §9): the schedule paragraph
  `06:889--936`.**  The frozen text prints the *two* low-rung gate blocks
  together -- the raw one at `eq:raw-low-rung-gates` (display `06:891--901`,
  label `06:900`) and the wrapped one at `eq:wrapper-low-rung-gates` (display
  `06:927--934`, label `06:933`) -- and closes at `06:935--936` with "Thus the
  raw and wrapped row calculations use exact ceilings, rather than an asymptotic
  appeal to *sufficient density*".  §5 owns the wrapped block; §9 owns the raw
  one, at these anchors:
  * `06:889--890`: "The exact low-rung row losses are also checked here.  For
    `x_j = (s/2^j) x_T`, `j = 0,1,2`, require";
  * `06:891--901`: the display `x_j <= gamma_j/(1 - 9/(16 . 2^j))` with the
    three printed rationals `gamma_0 = 27787089/830471792`,
    `gamma_1 = 19398081/1660943584`, `gamma_2 = 2620065/3321887168`
    (`06:896--898`);
  * `06:902--907`: "These rational margins imply
    `(beta_j^raw - x_j)/(1 - x_j) >= 9/(16 . 2^j)`, which is precisely the row
    density needed for the three raw lower rungs in `sec:dense-stage4`";
  * `06:917--918`, the two bounds the sufficiency argument uses: `s <= q` and
    `q x_T <= 4/25025`.

  This display was the last **GENUINELY-FRESH** display of the item-(v) roster
  range `06:1219--1220` -- registered exact under `S5-CUTOFF-ITEMS-DEFERRED`
  (b3) and never authored until `cc-t7r`.  It is stated here, and not in
  `RawLowProfileBody` or `DenseStageFourOpening`, because this is the module
  that already owns its printed twin and because both of those modules lie in
  this one's import closure, so `x_j` (the banked
  `DenseStageFourOpening.rowDensity`) and the consequence step (the banked
  `RawLowProfileBody.rawLow_gate_of_margin`) are consumed by pin rather than
  restated.
* **Inherited endpoint, entered as a named contract binder and never as an
  axiom.**  `thm:certified-localized-extension` (`A-certified-stopping.tex`,
  statement `A:109--146`, label `A:110`) is the binder `hLocEx` of
  `wrapperLowExtension`, in the exact implication shape the frozen theorem has:
  its **full antecedent set** in, its conclusion `H + log_2(r' t)` out.  This is
  the standing `cc-t2e` discipline the banked
  `DenseAliceClosure.denseExtensionClosure` already follows for the same
  endpoint: Localized Extension endpoints stay named binders, are never
  re-proved, never assumed unconditionally, and never turned into an axiom.  The
  antecedent set is carried item by item, with each item either **discharged
  here** or **named as a hypothesis with its frozen anchor**:

  * `M`, a nonempty Boolean matrix (`A:111`) <- `G`, the all-column reference;
    the carrier hypothesis `hGne`, passed straight to the endpoint.
  * `H >= 2`, an integer (`A:111`) <- `C - 1`; **proved** from `3 <= C`
    (`09:240`).
  * `0 < x <= 1` (`A:112`) <- `x_T`; hypotheses `hxT0`, `hxT1`.
  * `eq:certified-base` (`A:113--116`) <- `Lambda_3(G,1,x_T,3/5) >= C-1`; the
    binder `hbase`, which **is** the second clause of the banked
    `lem:wrapper-reference`.
  * `t >= t_cert` (`A:117`) <- `t_ref`; the binder `htcert`
    (`eq:tref-search`, `06:558--572`, is `06`'s).
  * `t` a power of two divisible by `16` (`A:117--118`) <- `t_ref = 2^k`; the
    exponent form `4 <= k`, hypothesis `hk`.
  * `t x <= 1` (`A:118`) <- `t_ref x_T <= 1`; **proved** from
    `eq:wrapper-low-simple-gate`.
  * `p_t = 9t/16` (`A:120`) <- `9 t_ref/16`; inside the block-count identity.
  * `r, r'` positive powers of two, `r' <= r`, `q = r t` (`A:125`) <-
    `q/t_ref`, `kappa_j/t_ref`; **proved** from `q/4 >= t_ref` (`09:327`).
  * `eps = 0`, the exact full product (`A:126--128`) <- `09:326`, "the
    reference restriction is a full product, so its balancedness error is
    exactly zero"; **proved** as the substitution.
  * `h in (0,1]` (`A:128`) <- `theta`; hypotheses `hθ0`, `hθ1`.
  * `a^sharp in {0,1}` (`A:129`) <- `0`; **proved** as the substitution.
  * `eq:certified-E1` (`A:130--134`) at `eps = 0`, `h = theta`, `H = C-1`,
    `q = 2^r` <- the binder `hE1` (`eq:tref-search` row two).
  * `eq:certified-E2` (`A:135--136`) at `eps = 0`, `h = theta`, `H = C-1`,
    `t = 2^k` <- the binder `hE2` (`eq:tref-search` row three).
  * exactly `r' p_t` represented outer blocks (`A:138--139`) <-
    `9 kappa_j/16`; **proved**, the identity from the banked
    `extensionSelectedBlocks` and the availability from
    `eq:wrapper-reference-count`.
  * at least `ceil(r' t x m)` rows per represented block (`A:139--141`) <-
    reference density `>= kappa_j x_T`; **proved** as the selected-coordinate
    predicate of `wrapperReferenceCount_ge`.
  * column density at least `h 2^{-a^sharp}` (`A:141`) <- `theta`
    (`09:311--313`); the binder `hcol`, the specified-coordinate projection.
  * the conclusion `H + log_2(r' t)` (`A:142--144`) <-
    `C - 1 + log_2 kappa_j`; **proved** equal to `C + r - 1 - j`.

  `EXPANDER-001`, the cited `(q_2,t_2,eps_2)`-balanced family of
  `lem:cited-expander-family`, has **no** Lean declaration by design; it does not
  appear in any hypothesis below, because the frozen substitution takes the
  *exact full product* branch of `A:126--128` (`eps = 0`) and not the balanced
  branch.  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP
  balanced-family axiom -- is **not** imported, and no declaration here is in its
  dependency graph.
* **Predecessor anchors (consumed by pin, never restated):**
  * `EthInapproximability.ParameterizedNP.ScaleAlignOpening` -- `wrapperU`,
    `wrapperW`, `firstWrapper` (whose `hLowRungs` binder this module retires),
    `wrapperLow_subtraction_free` (the subtraction-free reading of the frozen
    rung display), `betaHat` and `betaHat_frozen_values` (cited **only** to keep
    the two constants apart, see the statement pole `betaLow_ne_betaHat`), and
    `xTdepth_mem`;
  * `EthInapproximability.ParameterizedNP.DenseAliceClosure` --
    `extensionSelectedBlocks`, the frozen `r' p_t = 9 kappa/16` seed-count
    identity of the *same* inherited endpoint at the same `4 <= k` guard.  It is
    consumed, not restated: the two blocks make the same substitution arithmetic
    at different `(r', t)`;
  * `EthInapproximability.ParameterizedNP.HardSeedFacade.hardSeedColumnDensity`
    -- the frozen `2^{-2^{0.49 sqrt m}}`, which at `m = log_2 t_ref = k` is the
    `h_t` of `eq:certified-pt-ht` (`A:122`).  Consumed by pin so that `hE2` is
    stated at the frozen function and not at a fresh opaque real;
  * the vendored `EthBridge.le_Dfamily` -- the per-member-to-family transport
    that `wrapperLowRungs` uses, and `NPCC.Dfamily` / `NPCC.bracketGE` /
    `NPCC.LambdaGE` themselves.
* **New work.**  The outer rung scalars `kappa_j`, `beta_j` of `09:280--282`,
  kept syntactically apart from the banked `betaHat_j`; the retained-reference
  density step of `09:285--287` proved as a general finite-set inequality; the
  averaging argument behind `eq:wrapper-reference-count` (`09:287--295`) proved
  in general; the six exact `g = 91/92` margins of `09:297--302` recomputed at
  the frozen numbers; `eq:wrapper-low-rung-gates` (`06:927--934`) transcribed
  with the frozen sufficient condition `q x_T <= 4/25025` **proved** to imply the
  three exact ceiling comparisons, and proved *tight* at `j = 2`; the whole
  `09:313--331` substitution into `thm:certified-localized-extension` discharged
  clause by clause against the binder; and the wiring of `09:333` -- the family
  lift of the per-member rung bound, and its composition into the banked
  `firstWrapper` with the `hLowRungs` binder retired.  **`cc-t7r` adds §9**:
  `eq:raw-low-rung-gates` (`06:891--901`) transcribed -- the three printed
  rationals as `gammaRawLow` and the comparison as `rawLowRungGates` at the
  banked `rowDensity` -- composed into the rung clause of the banked
  `eq:raw-low-gates`, derived from the wrapped twin's own sufficient condition
  under `s <= q`, and given a NON-FIDELITY inhabitant at the route's banked
  `(2^340, 512)` tier.  **`cc-t7r-r1` closes the frozen consequence
  `06:902--906`**: at `r0` that sentence was carried with an *undischarged*
  binder `hbeta` asserting `gamma_j + 9/(16 . 2^j) <= beta_j^raw` -- an extra
  hypothesis where the paper states a consequence -- and the round was
  correctly refused on it.  The repair removes the binder from both consumers,
  states the conclusion about the pinned `betaRaw (rTail (3/5) j)`, and derives
  the lower bound through `rTail_le_one` and `betaRaw_ge_of_reservoir_ratio`
  from the reservoir data alone.  The remaining schedule input -- the
  reservoir-to-template ratio -- is discharged at its frozen value `beta_T`
  (`06:159`) in `EffectiveCutoffCertificate`, which is the nearest module that
  can pin the banked `ScheduleTemplateResidue.betaT` without an import cycle.
* Proof status: **new** for everything named in the previous item; **conditional**
  (with named, documented open binders) for the endpoint invocation, whose open
  binders are listed in the table above and again in the honest-scope list below.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, opened first-hand
for this tranche.  One item is claimed, and it was left explicitly unclaimed by
the predecessor module:

* the reader's rung display at lines 361--368,
  `D_U(1; 3/(5 . 2^j), theta) >= C + r_q - 1 - j` for `j = 0,1,2` -- claimed by
  `wrapperLowRungs`, and by nothing else.  The reader's surrounding prose (lines
  361--364: "retain the reference portion of each outer copy and use block
  balancing ... the scheduled gates leave the hard-seed fraction `9(q/2^j)/16`
  of the copies.  Localized Extension applied to `eq:paper-reference-profile`
  yields") is the proof recipe, cited in `wrapperLowExtension`'s docstring as
  such and **not** claimed as a statement by any declaration.  `ScaleAlignOpening`'s header records
  that "Lines 361--368 ... are the deferred blocks' content; they are cited in
  the GAP-EXPOSED list as *what the binders stand for*, and are **not** claimed
  as statements by any declaration here."  This is that content, and this module
  is where the reader row moves from GAP-EXPOSED to claimed.

**Deliberately not claimed**, to avoid a double assignment:

* `eq:paper-reference-profile` (reader line 233) in all three clauses, and
  `eq:paper-adapted-stage4-interface` (reader line 345) in all three clauses, are
  **already assigned** to `ScaleAlignOpening`'s `referenceG_follows_bob`,
  `D_referenceG`, `wrapperReference_rungs`, `wrapperReference` and
  `commonThreshold_of_wrapper`.  Nothing here reclaims any of them:
  `firstWrapperOfLowRungs` re-exports `commonThreshold_of_wrapper`'s conjuncts
  as the *output* of a composition and carries the autoformalization anchor
  `09:333` alone.
* reader lines 370 onward (the near-full rung outline) remain the dense rung's
  content and are untouched; `hDenseRung` stays a binder.
* The reader states no counterpart for `eq:wrapper-reference-count`, for the six
  exact margins, or for `q x_T <= 4/25025`; those declarations carry the
  autoformalization and parameter-schedule anchors alone and claim no reader
  item.
* **§9 claims no reader item either.**  The reader-facing release was searched
  first-hand for this tranche across all ten section files for the three
  `gamma_j` numerals, for `25025`, for `x_j` and for "low-rung": all four
  searches return **nothing**, and the reader prints no schedule margin display
  at all.  The reader does carry other `\gamma`s, and the `cc-t7r` finding R2
  corrects the earlier, overstated census here: besides the ETH gap constant
  `gamma_eps` (`06-eth.tex:24--25,52,150,188,212`) there is the bare
  source-graph soundness parameter `\gamma` of
  `03-parameterized-construction.tex:56` and `A-stage4-details.tex:15,71,72,80,
  122,128,135`, and the token `\gamma_j` used as a *vector coordinate* in
  `05-iteration.tex:35,48`.  None of them is a low-rung margin, so only the
  narrower conclusion holds -- and it is the one this module relies on.  The
  reader's one nearby line,
  `A-stage4-details.tex:361--368`, is the rung *conclusion* and is already
  claimed by `wrapperLowRungs`; assigning it a second time would be the
  double-assignment defect.  So every §9 declaration carries the
  parameter-schedule anchor alone.
* The five §8 receipts are about the shape of `A:112` as an antecedent of the
  assumed endpoint implication, and claim **no** reader item.  The reader does
  carry a Localized Extension statement, but it is a **different** one: the
  Section-2 corollary `cor:paper-localized-extension` (reader
  `02-preliminaries.tex:512--527`, opened first-hand for this round), which is
  the *uncertified* form -- no `t >= t_cert`, no `h_t`, no `eq:certified-E1/E2`
  -- and whose density hypothesis is inherited from `thm:paper-extension`
  (reader `02-preliminaries.tex:485--509`) in the **stronger** shape
  `2^{-b} <= x_seed <= 1`, not the frozen `A:112` shape `0 < x <= 1`.  The two
  are neither the same statement nor the same hypothesis, so citing the reader
  corollary here would be a false counterpart; all five therefore carry the
  `A-certified-stopping.tex` anchor alone.  In particular none of them touches
  the rung display at reader lines 361--368, which stays `wrapperLowRungs`'.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the outer rung scalars, general (6): `kappaLow_def`, `kappaLow_pos`,
  `kappaLow_cast`, `kappaLow_mul_tRef`, `betaLow_apply`, `betaLow_mono_g`.
* `A2` the frozen `g = 91/92` readouts (2): `betaLow_frozen_values`,
  `betaLow_frozen_margins`.
* `A3` the retained-reference density of `09:285--287`, general (2):
  `reference_density_after_discard`,
  `reference_density_after_discard_nondegenerate`.
* `A4` `eq:wrapper-reference-count`, general (3): `referenceCount_mono_beta`,
  `referenceCount_le_card`, `referenceCount_le_card_of_nat`.
* `A5` `eq:wrapper-low-rung-gates` (3): `wrapperLowRungGates_of_simple_gate`,
  `simple_gate_forces_tRef_row_legality`, `wrapperLowRungGates_legal_instance`.
* `A6` the `09:317--323` substitution, general (4): `refExtensionExponents`,
  `refExtensionBlocks`, `refExtensionOutput`, `wrapperReferenceCount_ge`.
* `A7` the endpoint invocation and the wiring (4): `wrapperLowExtension`,
  `wrapperLowRungs`, `wrapperLowRungs_not_over_demanded`,
  `firstWrapperOfLowRungs`.
* `A8` the `A:112` repair battery of §8 (3): `locEx_strict_of_nonstrict`,
  `simple_gate_forces_strict_tRef_row_legality`,
  `strict_xT_membership_at_banked_tier`.

* `A9` `eq:raw-low-rung-gates` (`06:891--901`), the `cc-t7r` section, with the
  `r1` margin close (11): `gammaRawLow_frozen_values`, `rawLowRungBound_pos`,
  `rawLowRungGates_rowDensity_lt_one`, `rawLowRungGates_of_simple_gate`,
  `rawLowRungGates_of_wrapperGate`, `rawLowRungGates_mono`, `rTail_le_one`,
  `betaRaw_ge_of_reservoir_ratio`, `rawLowRung_margin_of_gates`,
  `rawLowRungGates_supply_rawLowRungClause`, `gammaRawLow_below_rTail`.

That is **38 battery entries proved**, with `0` unproved, alongside **six
statement poles** (`betaLow_ne_betaHat`, `wrapperLowRung_gate_is_tight`,
`wrapperLowRungs_not_automatic`, `locEx_strict_strictly_weaker`,
`zero_xT_refutes_endpoint_conclusion`,
`rawLowRungGates_refuted_at_full_width`) and **four non-vacuity /
specialization readouts** (`wrapperLowRungGates_legal_instance` and
`strict_xT_membership_at_banked_tier`, already counted in `A5` and `A8`,
`wrapperLowExtension_fires_at_legal_tier`, and the NON-FIDELITY
`rawLowRungGates_at_banked_tier`).

The module has **52** source declarations in all: 6 definitions (`kappaLow`,
`betaLow`, `referenceCount`, `wrapperLowRungGates`, `gammaRawLow`,
`rawLowRungGates`) and 46 proved results.  All 52 are registered in
`tools/AxiomAudit.lean`.

## §9 statement-numeral screen and binder provenance (`cc-t7r`)

*Numerals in §9 declaration statements* (proof bodies excluded), each classified:

| occurrence | classification |
| --- | --- |
| `gammaRawLow`: `27787089`, `830471792`, `19398081`, `1660943584`, `2620065`,
  `3321887168` (and the same six in `gammaRawLow_frozen_values`) |
  CANONICAL-FORM at `06:896--898`.  The display *defines* `gamma_0, gamma_1,
  gamma_2` by these literals, so they are the paper's own closed form at that
  anchor, not values chosen or derived here |
| `gammaRawLow`: the guards `0`, `1`, `2` and the out-of-range value `0` |
  CANONICAL-FORM at `06:890` (`j = 0,1,2`): the paper defines the symbol at
  exactly three indices.  The out-of-range `0` is inert -- no statement of this
  module evaluates `gammaRawLow` outside `j <= 2` |
| `rawLowRungGates`, `rawLowRungBound_pos`, `rawLowRung_margin_of_gates`,
  `rawLowRungGates_supply_rawLowRungClause`, `gammaRawLow_below_rTail`:
  `9`, `16`, `2`, and the rung bound `2` in `j <= 2` | CANONICAL-FORM at
  `06:890--893`: the displayed denominator is `1 - 9/(16 . 2^j)` and the
  displayed range is `j = 0,1,2` |
| `rawLowRungGates_of_simple_gate`: `4 / 25025` | CANONICAL-FORM at `06:918`
  (`q x_T <= 4/25025`), the same constant `06:932` prints as the second clause
  of `eq:wrapper-low-rung-gates` and `wrapperLowRungGates` already carries |
| `gammaRawLow_below_rTail`, `rawLowRung_margin_of_gates`,
  `rawLowRungGates_supply_rawLowRungClause`: `3 / 5` | CANONICAL-FORM at the
  frozen **application anchors** `05:541--542`, `06:1110` and `09:1137`, which
  print `y = 3/5` literally.  `08:175` and `08:213` are *not* cited for it:
  both leave `y` symbolic, and the earlier row that cited them (and called the
  value "reader-pinned") was the `cc-t7r` finding R7 and is corrected here --
  all three supporting anchors are autoformalization anchors, none is a reader
  anchor.  `rTail` and `sigmaR` are consumed by pin and no `sigma` numeral is
  written here |
| `rTail_le_one`: the `1` of `y <= 1` and of the conclusion | Structural
  comparison constants (a density bound), of the same kind as the `0`/`1` in
  `rawLowRungBound_pos`; no source-defined quantity stands here |
| `betaRaw_ge_of_reservoir_ratio`: the `1` in `r <= 1` and in `r(1 + rho)` |
  CANONICAL-FORM at `08:176--181`: `1 + rho` is the frozen
  `(|T| + |W_V| + |W_B|)/|T|` written over the ratio, and `r <= 1` is the
  legality of a residual density.  No numeral stands where `beta_T`, `r_j` or
  `gamma_j` belongs -- `rho` is a binder, discharged downstream at the banked
  `ScheduleTemplateResidue.betaT` |
| `rawLowRungGates_at_banked_tier`: `2 ^ 340`, `512` | EVALUATED by pin.  The
  route's banked witness tier: `s = 2^340` is the scale
  `ScaleAlignOpening.referenceProfileGates_legal_instance` and
  `RawLowProfileBody.rawLowGates_inhabited` already use, and `512` is **forced**
  from it, not chosen -- `RawLowProfileBody.witness_bT_checked` computes
  `b_T = 2^{j_49(log_2(s/4))} = 2^{j_49(338)} = 2^9`.  The same pair already
  appears in this module at `strict_xT_membership_at_banked_tier`, from which
  this theorem's gate hypothesis is taken |
| `rawLowRungGates_refuted_at_full_width`: `2 ^ bT` (no literal) and the `0`
  rung index | The probe **claims no legality**: `s = 2^{b_T}` is the excluded
  boundary of `06:271--273` (`I_j < 2^{b_T}`), and the rung index `0` is the
  display's own first rung |

No BEYOND-PAPER numeral is introduced in §9, and no numeral stands where a
source-defined quantity belongs: `x_j`, `I_j` and `x_T` are the banked
`rowDensity`, `widthI` and `xTdepth`, never re-expressed.

*Free binders in §9 statements* (no `structure` and no premise bundle is minted
here, so there are no fields to classify):

| binder | provenance |
| --- | --- |
| `j : ℕ` with `j <= 2` | GENUINELY-FREE -- the display's own rung index,
  quantified by the frozen text itself at `06:890` |
| `beta : ℝ` in `rawLowRung_margin_of_gates` | **RECLASSIFIED at `cc-t7r-r1`:
  SOURCE-DEFINED, and therefore REMOVED.**  The earlier table called this
  binder GENUINELY-FREE; that was the round's blocking defect.  `beta_j^raw` is
  **defined** by the frozen chain -- `beta_j^raw` at `08:176--181` (the ceiling
  quotient over `|T|`, `|W_V|`, `|W_B|`), `r_j` at `08:175`, the reservoir
  ratio ceiling `beta_T` at `06:159`, and the window `99/100 <= lambda_T` at
  `06:174` that forces `(|W_V| + |W_B|)/|T| <= beta_T`.  A source-defined
  quantity never enters as a free binder, so the repaired theorem states its
  conclusion about the pinned `DenseStageFourOpening.betaRaw (rTail (3/5) j)`
  and derives the lower bound instead of assuming it |
| `T₀ V₀ B₀ : ℕ` in `rawLowRung_margin_of_gates` /
  `rawLowRungGates_supply_rawLowRungClause` / `betaRaw_ge_of_reservoir_ratio` |
  GENUINELY-FREE at this site: `08:176--181` leaves the three reservoir
  cardinalities open.  (Corrected at `cc-t7r-r1`: the residual is NOT the
  duplication multiplicity table -- the Section-8 multiplicity carriers
  `wBase`/`wSel`/`wDiag`/`uBase`/`uTemp`/`uVert`/`uBlock` and the mass theorems
  `protected_row_masses`/`protected_col_masses` are banked at
  `DenseStageFourOpening`.  Those carriers are *parameterized by* `T₀ V₀ B₀`
  rather than fixing them, so the classification is unchanged; what is still
  unwired is the materialized-Stage-2 / source-ratio canonical boundary.)  They
  are the **banked**
  binders of `RawLowProfileBody.rawLow_gate_of_margin` /
  `DenseStageFourOpening.betaRaw`, passed straight through and never
  re-quantified |
| `y : ℝ` in `rawLowRungGates_supply_rawLowRungClause` | **REMOVED at
  `cc-t7r-r1`.**  It was a free binder; the frozen text instantiates `y = 3/5`
  at `05:541--542`, `06:1110` and `09:1137`, so the theorem is now stated at
  that value.  `08:175`/`08:213` leave `y` symbolic and anchor nothing |
| `ρ : ℝ` in `rawLowRung_margin_of_gates` /
  `rawLowRungGates_supply_rawLowRungClause` / `betaRaw_ge_of_reservoir_ratio` |
  GENUINELY-FREE **in this module only**, and discharged in the same tranche.
  It is the reservoir-to-template ratio bound; the schedule *defines* its
  frozen value as `beta_T` (`06:159`), banked as
  `ScheduleTemplateResidue.betaT`, which cannot be pinned here because
  `ScheduleTemplateResidue` transitively imports this module.  The closed
  instances at `rho = beta_T` are
  `EffectiveCutoffCertificate.rawLowRung_margin_at_templateWindow` and
  `.rawLowRungClause_at_templateWindow`; the general `rho` binder exists so the
  arithmetic can be stated upstream of the constant, not because the source
  leaves the ratio open |
| `s bT : ℕ` in `rawLowRungGates` and everything consuming it | **Not free in
  the schedule sense, and not classified as such**: they are the *parameters of
  the banked interface this predicate is stated over* -- exactly the binder list
  `DenseStageFourOpening.rawLowGates (s bT T₀ V₀ B₀ : ℕ)` and
  `rowDensity (s j bT : ℕ)` already carry -- and both are source-defined
  (`eq:s-choice` for `s`; `06:238--242` with `j_49` for `b_T`, which
  `RawLowProfileBody.witness_bT_checked` evaluates).  They are therefore never
  instantiated at a chosen value here: the one unconditional instance,
  `rawLowRungGates_at_banked_tier`, evaluates them at the banked tier with
  `b_T` forced from `s`, and the one probe that picks a relation between them
  claims no legality |
| `r : ℕ` in `rawLowRungGates_of_simple_gate` / `_of_wrapperGate` |
  Same status, and the same binder `wrapperLowRungGates (r : ℕ)` already uses
  for `q = 2^r`; it enters only through the frozen bound `s <= q` of `06:917`
  and is pinned at `340` in the banked-tier instance |

## The `A:112` repair (rounds `r1`, `r2`)

The first judged round of this module carried `A:112` as `0 <= x` -- both as
`wrapperLowExtension`'s binder `hxT0` and, decisively, as the **third antecedent
of the assumed implication `hLocEx`**.  The frozen theorem prints
`0 < x \le 1` (`A:112`), and relaxing an antecedent of an assumed implication
*strengthens* the assumption: the parked `hLocEx` asserted the Localized
Extension conclusion at `x = 0`, where `thm:certified-localized-extension` says
nothing and where the conclusion is in fact false -- at `x = 0` the row demand
`ceil(r' t x m)` is `0`, so the empty restriction, of complexity `0`, is
admissible, and it cannot meet `H + log_2(r' t) >= 2`.  Three edits restore the
frozen form: the binder, that antecedent in `wrapperLowExtension`, and the same
antecedent in `wrapperLowExtension_fires_at_legal_tier` (discharged there by
`positivity` at the tier value).  Where the non-strict fact is still consumed --
`simple_gate_forces_tRef_row_legality`, which keeps its **own** `0 <= xT` binder
because it is this block's gate arithmetic and not a transcription of `A:112` --
it is threaded as `le_of_lt hxT0`.  No other statement in the module moved: the
remaining 30 declarations are unchanged apart from that threading at the two
call sites, and apart from two docstring-fidelity corrections
(`reference_density_after_discard_nondegenerate`, whose statement is untouched,
and `wrapperLowExtension_fires_at_legal_tier`, likewise).

Round `r2` adds the five receipts of §8, one per role, which make the repair
auditable inside the kernel instead of only in this prose.  They are stated
about the **hypothesis form** and construct no restriction of `G`:

* `locEx_strict_of_nonstrict` -- the *weakens receipt*: the frozen strict form
  is implied by the `r0` non-strict form, so the repair loses no consequence;
* `locEx_strict_strictly_weaker` -- the pole showing the receipt has **no**
  converse, so the repair is a genuine restriction of the assumption and not a
  rename; the separating point is exactly `x = 0`;
* `simple_gate_forces_strict_tRef_row_legality` -- the strict transport of
  `A:112` through the `t = t_ref` substitution into `A:118`, giving
  `0 < t_ref x_T <= 1` where the banked lemma gave only the upper half;
* `strict_xT_membership_at_banked_tier` -- the non-vacuity witness: the strict
  membership, the frozen gate, `eq:wrapper-low-rung-gates` and the strict row
  legality all hold at the **banked** tier `w_S = 340`, `b_T = 512`, so the
  repaired hypothesis is satisfied at legal parameter values already used
  elsewhere in the route rather than at invented ones;
* `zero_xT_refutes_endpoint_conclusion` -- the `r0` defect preserved as a
  kernel-visible countermodel: at `x = 0` the row demand `ceil(r' t x m)` is
  `0`, a matrix of complexity `0` exists, and `H + log_2(r' t) <= 0` is false
  at `H = C - 1 >= 2`.

None of the five claims a reader item, and none narrows `hLocEx`, `hbase`,
`htcert`, `hE1`, `hE2` or `hcol`.

## Why the deliverables are not satisfied by a trivial witness

Neither headline is existential, so each is exhibited as *refutable at a
legal-shaped instance*:

* `wrapperLowRungs`' conclusion fails at the constant matrix:
  `wrapperLowRungs_not_automatic` computes
  `comp<Int_{2^r}(0), 1, y/2^j, theta> = 0` for the whole one-copy bracket family
  over the constant game, which misses `C + r - 1 - j` for every legal `C >= 3`.
  So the value comes from `hmem`, i.e. from the endpoint, and not from the
  bracket shape.
* `eq:wrapper-low-rung-gates` is not automatic, and its constant is not slack:
  `wrapperLowRung_gate_is_tight` computes the exact admissible bound on
  `kappa_2 x_T` -- namely `(64 beta_2 - 9)/55 = 1/25025` -- and shows that
  `kappa_2 x_T > 1/25025` **falsifies** the `j = 2` comparison.  Since
  `kappa_2 x_T = q x_T/4`, the frozen `q x_T <= 4/25025` is exactly the largest
  constant that works: it is a boundary, not a margin.
* `eq:raw-low-rung-gates` is not automatic either, and it is not vacuous:
  `rawLowRungGates_refuted_at_full_width` refutes it at `s = 2^{b_T}` for every
  `b_T` -- so no proof of it can come from the shape of `rowDensity` alone --
  while `rawLowRungGates_at_banked_tier` satisfies it at the route's banked
  legal tier.  A gate predicate with only one of those two properties would be
  either unsatisfiable or empty; §9 exhibits both.  What §9 does **not** claim
  is that the *paper's own* instance inhabits it: that instance is the condition
  list the schedule compiler emits, which is unbuilt, so canonical inhabitation
  stays registered and deferred.
* The discarding step's conclusion is not the trivial `0 <= _`:
  `reference_density_after_discard_nondegenerate` is a **separating probe at a
  degenerate point** (`g = 1`, `y = 1`, `S = R = univ` on a two-element carrier),
  chosen only because it forces `betaLow` to the value `1`, so a `0 <= _`
  reading of `reference_density_after_discard` is refuted.  It is *outside* the
  block's frozen regime (`g = 91/92`, `y = 3/5`) and must not be read as a legal
  instance of it; the legal-regime content is carried by
  `betaLow_frozen_values`/`betaLow_frozen_margins`, which compute
  `beta_0 = 271/455 > 0` at exactly the frozen mass.
* The endpoint binder carries the bound, not the shape:
  `wrapperLowExtension_fires_at_legal_tier` **specializes** `wrapperLowExtension`
  at the legal tier `x_T = 1/(2^rE . 65536)`, discharging exactly the antecedents
  this block owns (`hxT0`, `hxT1`, `hgate`); and `hLocEx` is the only place a
  complexity value is produced.  It exhibits **no** inhabitant of `hLocEx`,
  `hbase`, `hE1`, `hE2` or `hcol`, so joint satisfiability of the full bundle is
  *not* claimed anywhere in this module -- see the `A:112`/`eq:tref-search` note
  on that theorem.

## Three-tier witness legality

* **Tier 1 -- symbolic in the frozen parameters.**  Every result about
  `kappaLow`, `betaLow`, `referenceCount`, `reference_density_after_discard`,
  `wrapperLowExtension`, `wrapperLowRungs` and `firstWrapperOfLowRungs` is
  general in the carriers, in the matrices, in `r`, `C`, `k`, and in the real
  parameters `x_T, theta, y, g`.  Nothing is evaluated.
* **Tier 2 -- the block-owned antecedents instantiated in the legal range.**
  `wrapperLowRungGates_legal_instance` (which *does* prove its gate predicate
  outright) and `wrapperLowExtension_fires_at_legal_tier` (which *specializes*,
  discharging only `hxT0`, `hxT1`, `hgate`) are stated for **arbitrary** `k, rE`
  in the range the frozen gates force (`4 <= k`, `k + 2 <= rE`, the second being
  `q/4 >= t_ref` of `09:327` in exponent form), at
  `x_T = 1/(2^rE . 65536)`, which satisfies `q x_T = 1/65536 <= 4/25025`.  The
  point of quantifying rather than pinning is that `eq:tref-search`
  (`06:558--572`) forces `k = k_ref >= 2^19`, so **no** small numeral is a legal
  value of `k` and none is pinned; `x_T = 2^{-b_T}` likewise, with `b_T` fixed by
  `06:238--242`.  The witness fixes `q x_T` and nothing else, and no parameter
  may be read out of it.

  `strict_xT_membership_at_banked_tier` is the one tier-2 result that *does* pin
  numerals, and it pins only numerals the route has already banked:
  `w_S = 340`, `b_T = 512` are `ScaleAlignOpening`'s
  `referenceProfileGates_legal_instance` pair, and `k = 9` is forced to be some
  legal exponent by `4 <= k` and `k + 2 <= 340`, with `512 = 2^9` the frozen
  `t_ref` shape.  It is a satisfiability check on the block-owned strict
  antecedent, not a parameter choice; `eq:tref-search` still forces
  `k_ref >= 2^19` and nothing here may be read as fixing `k_ref`.

  `rawLowRungGates_at_banked_tier` (§9) is tier 2 at the **same** pair, and it
  pins nothing new: its gate hypothesis *is*
  `strict_xT_membership_at_banked_tier`'s third clause, and `b_T = 512` is
  forced from `s = 2^340` by `RawLowProfileBody.witness_bT_checked` rather than
  chosen.  It is a satisfiability check on the display, and **not** canonical
  inhabitation -- the paper's own instance is the compiler's emitted condition
  list, which is unbuilt and stays registered.
* **Tier 3 -- separating probes at deliberately small carriers.**
  `betaLow_ne_betaHat`, `wrapperLowRung_gate_is_tight`,
  `reference_density_after_discard_nondegenerate` and
  `wrapperLowRungs_not_automatic` are probes of one named clause at a minimal
  carrier or at one rung, cited only for what they separate.
  `locEx_strict_strictly_weaker` and `zero_xT_refutes_endpoint_conclusion` are
  probes of the same kind at the **excluded boundary** `x = 0`: they are
  deliberately *outside* the frozen regime `0 < x <= 1` and must never be read
  as instances of it -- their whole content is that the frozen regime excludes
  the point at which they hold.  `rawLowRungGates_refuted_at_full_width` (§9) is
  the same kind at the boundary `s = 2^{b_T}`, which `06:271--273` excludes by
  `I_j < 2^{b_T}`: it claims no legality and concludes a negation.

## Honest scope, GAP-EXPOSED, and recorded coverage limits

1. **The Localized Extension endpoint is not discharged, and this module builds
   no restriction of `G`.**  `09:311--331` is *carried out at the level of its
   antecedent set*: what is proved is that the frozen data of this block
   discharge every antecedent the block owns, and that the endpoint's conclusion
   is exactly `eq:wrapper-u-low`.  The endpoint itself is `hLocEx`.  No consumer
   may read this module as having proved
   `thm:certified-localized-extension`.
2. **Three antecedents are `06`'s and stay binders:** `htcert`
   (`t_ref >= t_cert`, carried as `tcert <= 2^k` for the *fixed frozen integer*
   `t_cert` of `A:104--107`, a parameter of the statement and never a claim
   about all naturals), `hE1` and `hE2` (`eq:certified-E1`/`E2`).
   `06:574--578` records that these are exactly what `eq:tref-search`
   (`06:558--572`) verifies -- "The `clog_2(t_0(3/5))` term verifies the
   sufficiently-large-width hypothesis in `thm:certified-localized-extension`;
   the remaining parts of the first two inequalities verify the width and
   column-loss hypotheses for the full-product reference family, while the third
   verifies its hard-seed comparison" -- and the parameter schedule is not this
   block's territory.  Nothing here narrows them.
3. **`eq:certified-E1` is stated in its `t`-th-power form.**  The frozen display
   `A:130--134` is `(h 2^{-(H+log_2 q)}/(1+eps))^{1/t} >= y_*`.  At `eps = 0` and
   for nonnegative arguments that is *equivalent* to
   `h 2^{-(H+log_2 q)} >= y_*^t`, which is what `hE1` states.  The rewriting is
   recorded here rather than performed silently, and it neither strengthens nor
   weakens the antecedent.
4. **The geometry of `09:284--313` is not constructed.**  The per-outer-coordinate
   reference densities `d` are *given* data; what is proved is the averaging
   inequality they satisfy (`referenceCount_le_card`) and the gate arithmetic
   that turns it into `9 kappa_j/16` (`wrapperReferenceCount_ge`).  The
   specified-coordinate projection of `09:312--313` -- "Its normalized density
   remains at least `theta`" -- is the binder `hcol`, stated on a *given* column
   density `colDens` as the frozen `h 2^{-a^sharp} <= colDens` at
   `a^sharp = 0`, since projecting a member of the bracket family is exactly the
   restriction-building this block does not do.  `hcol` is therefore a real
   hypothesis about given data and not a shape identity.
5. **`hDenseRung` is untouched.**  `firstWrapperOfLowRungs` retires `hLowRungs`
   and carries `hDenseRung` forward verbatim; the five blocks `09:335--1781` that
   prove `eq:wrapper-u-dense` remain GAP-EXPOSED exactly as `ScaleAlignOpening`
   records them, and each remains a separate future tranche.
6. **`theta` stays a binder and is never a numeral.**  Every statement below
   quantifies it, and the schedule lemmas that bound it
   (`ScaleAlignOpening.scheduleTheta_guards`) are consumed, not re-derived.
7. **`g = 91/92` enters as the pinned mass, never as an assumption about `G`.**
   `ScaleAlignOpening.referenceG_row_mass` is the theorem that the reference row
   mass *is* `91/92` at the pinned protected instance; `betaLow` is general in
   `g`, and only the gate and the margins instantiate it at `91/92`, exactly as
   `06:924` does.
8. **No route completion is claimed.**  The construction and machine layers of
   the route remain unlanded.
9. **§9 owns one display and closes one attribution remainder -- nothing
   larger.**  `eq:raw-low-rung-gates` now has a Lean carrier, so item (v)'s
   fourteen displays all have display-level owners; **item (v) itself stays
   NONE-YET and registered open**, because writing it as pins over one shared
   context additionally requires a context instantiating all fourteen owners at
   once, and none is formed.  Nothing in §9 states, weakens or re-associates any
   other gate, and `beta_j^raw`'s own lower bound -- which `08:176--181` makes
   depend on reservoir cardinalities -- stays an explicit binder rather than
   being asserted at a value.
-/

namespace EthInapproximability.ParameterizedNP.WrapperLowRungs

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.HardSeedFacade
open EthInapproximability.ParameterizedNP.DenseAliceClosure
open EthInapproximability.ParameterizedNP.ScaleAlignOpening

/-! ## §1  The outer rung scalars (`09:278--283`)

"Fix `j in {0,1,2}`, and put `kappa_j = q/2^j`, `beta_j = (y/2^j - (1-g))/g`."

Both are **outer** scalars, over the `q` copies of the reference `G`.  They are
not the inner `x_j`, `hat beta_j` of `09:132--141`: the statement pole
`betaLow_ne_betaHat` keeps the two apart at the frozen numbers, and nothing
below ever substitutes one for the other. -/

/-- **`09:280`.**  `kappa_j = q/2^j` at the scale-alignment width `q = 2^r`.

Written on the exponent so that the frozen division is exact and no natural
truncation is taken: for `j <= r` this is literally `2^r/2^j`, which
`kappaLow_cast` reads off. -/
def kappaLow (r j : ℕ) : ℕ := 2 ^ (r - j)

@[simp] theorem kappaLow_def (r j : ℕ) : kappaLow r j = 2 ^ (r - j) := rfl

/-- **Aux A1a.**  `kappa_j` is positive.  General. -/
theorem kappaLow_pos (r j : ℕ) : 0 < kappaLow r j := pow_pos (by norm_num) _

/-- **Aux A1b (`09:280` as a real identity).**  For `j <= r` the frozen quotient
is exact: `kappa_j = q/2^j` with `q = 2^r`.  General; this is the only place the
natural subtraction in `kappaLow` is unfolded, and it is legal exactly because
`j <= 2 <= r` holds under the block's gate. -/
theorem kappaLow_cast {r j : ℕ} (hj : j ≤ r) :
    ((kappaLow r j : ℕ) : ℝ) = (2 : ℝ) ^ r / 2 ^ j := by
  have h : (2 : ℝ) ^ (r - j) * 2 ^ j = 2 ^ r := by
    rw [← pow_add]
    congr 1
    omega
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [kappaLow_def]
  push_cast
  field_simp
  linarith [h]

/-- **Aux A1c (`09:320--321`, the two width substitutions multiply back).**
`r' t = (kappa_j/t_ref) t_ref = kappa_j`, in exponent form, under the frozen
legality `q/4 >= t_ref` (`09:327`) written as `k + 2 <= r` and `j <= 2`.
General; this is the identity that makes the endpoint's output
`H + log_2(r' t)` equal to `C - 1 + log_2 kappa_j`. -/
theorem kappaLow_mul_tRef {r j k : ℕ} (hj : j ≤ 2) (hq4 : k + 2 ≤ r) :
    2 ^ (r - j - k) * 2 ^ k = kappaLow r j := by
  rw [kappaLow_def, ← pow_add]
  congr 1
  omega

/-- **`09:282`.**  `beta_j = (y/2^j - (1-g))/g`, the **outer** relative reference
density: the density, among the `q` copies of `G`, that the retained reference
rows of a member of `<U,1,y/2^j,theta>` are forced to have.  General in `y`, in
the reference row mass `g`, and in the rung index. -/
noncomputable def betaLow (y g : ℝ) (j : ℕ) : ℝ := (y / 2 ^ j - (1 - g)) / g

@[simp] theorem betaLow_apply (y g : ℝ) (j : ℕ) :
    betaLow y g j = (y / 2 ^ j - (1 - g)) / g := rfl

/-- **Aux A1d (`beta_j` is monotone in the reference mass).**  Writing
`beta_j = 1 + (y/2^j - 1)/g`, the numerator is nonpositive as soon as
`y/2^j <= 1`, so a *larger* reference mass gives a *larger* forced density.
This is the direction the block needs: `g = 91/92` is the pinned mass of
`09:117`, and a construction retaining more of `N` in `G` only helps.
General. -/
theorem betaLow_mono_g {y g g' : ℝ} {j : ℕ}
    (hy : y / 2 ^ j ≤ 1) (h0 : 0 < g) (h : g ≤ g') :
    betaLow y g j ≤ betaLow y g' j := by
  have h0' : 0 < g' := lt_of_lt_of_le h0 h
  have hnum : y / 2 ^ j - 1 ≤ 0 := by linarith
  have key : (y / 2 ^ j - 1) / g ≤ (y / 2 ^ j - 1) / g' := by
    rw [div_le_div_iff₀ h0 h0']
    nlinarith
  have e1 : betaLow y g j = 1 + (y / 2 ^ j - 1) / g := by
    rw [betaLow_apply]
    field_simp
    ring
  have e2 : betaLow y g' j = 1 + (y / 2 ^ j - 1) / g' := by
    rw [betaLow_apply]
    field_simp
    ring
  rw [e1, e2]
  linarith

/-! ## §2  The frozen `g = 91/92` readouts (`09:297--302`) -/

/-- **`09:297--302`, the three exact values at the pinned mass.**

"The fixed value `g = 91/92` gives the exact margins `beta_0 = 271/455`,
`beta_1 = 19/65`, `beta_2 = 64/455`", at the frozen `y = 3/5` of `03:216--219`
(the same instantiation `06:924` prints).  Equalities, not estimates. -/
theorem betaLow_frozen_values :
    betaLow (3 / 5) (91 / 92) 0 = 271 / 455
      ∧ betaLow (3 / 5) (91 / 92) 1 = 19 / 65
      ∧ betaLow (3 / 5) (91 / 92) 2 = 64 / 455 := by
  refine ⟨?_, ?_, ?_⟩ <;> · rw [betaLow_apply]; norm_num

/-- **`09:298--302`, the three exact margins.**

"`beta_0 - 9/16 = 241/7280`, `beta_1 - 9/32 = 23/2080`,
`beta_2 - 9/64 = 1/29120`."  Recomputed here at the frozen numbers, and the
third is the one the gate is calibrated against: it is the smallest of the
three by a factor above `300`. -/
theorem betaLow_frozen_margins :
    betaLow (3 / 5) (91 / 92) 0 - 9 / 16 = 241 / 7280
      ∧ betaLow (3 / 5) (91 / 92) 1 - 9 / 32 = 23 / 2080
      ∧ betaLow (3 / 5) (91 / 92) 2 - 9 / 64 = 1 / 29120
      ∧ (1 : ℝ) / 29120 < 23 / 2080
      ∧ (23 : ℝ) / 2080 < 241 / 7280 := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;> · rw [betaLow_apply]; norm_num

/-- **Statement pole (the outer `beta_j` is not the inner `hat beta_j`).**

`09:139--141` defines `hat beta_j = (y/2^j + lambda_T - 1)/lambda_T` on the
*template column* density `lambda_T >= 99/100`; `09:282` defines
`beta_j = (y/2^j - (1-g))/g` on the *reference row* mass `g = 91/92`.  They are
different functions of different data, and at the frozen numbers they take
different values at every rung -- so a proof that silently reused one for the
other would be caught here.

The `j = 2` margins separate them too, and in the direction that matters: the
outer slack `1/29120` is **strictly smaller** than the banked inner slack
`5/6336` (`ScaleAlignOpening.betaHat_rung2_margin`).  The opening's slack is
therefore never reusable here; this block's gate must be, and is, calibrated
against `1/29120`. -/
theorem betaLow_ne_betaHat :
    betaLow (3 / 5) (91 / 92) 0 ≠ betaHat (3 / 5) (99 / 100) 0
      ∧ betaLow (3 / 5) (91 / 92) 1 ≠ betaHat (3 / 5) (99 / 100) 1
      ∧ betaLow (3 / 5) (91 / 92) 2 ≠ betaHat (3 / 5) (99 / 100) 2
      ∧ (1 : ℝ) / 29120 < 5 / 6336 := by
  obtain ⟨e0, e1, e2⟩ := betaLow_frozen_values
  obtain ⟨f0, f1, f2⟩ := betaHat_frozen_values
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [e0, f0]; norm_num
  · rw [e1, f1]; norm_num
  · rw [e2, f2]; norm_num

/-! ## §3  Discarding the nonreference rows (`09:285--287`)

"After discarding every nonreference row, the retained reference rows have
normalized density at least `beta_j` among the `q` copies of `G`." -/

/-- **`09:285--287`, proved in general.**

Let `S` be a row set of density at least `z` in a finite carrier, and let `R` be
the reference rows, of mass exactly `g`.  Then the retained reference rows
`S ∩ R` have density at least `(z - (1-g))/g = betaLow` *inside* `R`.

This is the only content of the discarding step, and it is elementary:
`|S ∩ R| >= |S| + |R| - |A|`.  General in the carrier, in `S`, in `R`, in `z`
and in `g`; nothing about the reference construction is used beyond its mass, so
the pinned `g = 91/92` of `ScaleAlignOpening.referenceG_row_mass` plugs straight
in. -/
theorem reference_density_after_discard {A : Type*} [Fintype A] [DecidableEq A]
    (S R : Finset A) {y g : ℝ} (j : ℕ)
    (hg : (R.card : ℝ) = g * (Fintype.card A : ℝ)) (hg0 : 0 < g)
    (hcard : 0 < Fintype.card A)
    (hz : (y / 2 ^ j) * (Fintype.card A : ℝ) ≤ (S.card : ℝ)) :
    betaLow y g j ≤ ((S ∩ R).card : ℝ) / (R.card : ℝ) := by
  have hm : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hcard
  have hRpos : (0 : ℝ) < (R.card : ℝ) := by rw [hg]; positivity
  -- `|S ∪ R| + |S ∩ R| = |S| + |R|` and `|S ∪ R| <= |A|`
  have hunion : ((S ∪ R).card : ℝ) + ((S ∩ R).card : ℝ)
      = (S.card : ℝ) + (R.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_union_add_card_inter S R)
  have hle : ((S ∪ R).card : ℝ) ≤ (Fintype.card A : ℝ) := by
    exact_mod_cast Finset.card_le_univ (S ∪ R)
  have hinter : (S.card : ℝ) + (R.card : ℝ) - (Fintype.card A : ℝ)
      ≤ ((S ∩ R).card : ℝ) := by linarith
  have hkey : (y / 2 ^ j - (1 - g)) * (Fintype.card A : ℝ) ≤ ((S ∩ R).card : ℝ) := by
    rw [hg] at hinter
    nlinarith
  rw [betaLow_apply, div_le_div_iff₀ hg0 hRpos, hg]
  nlinarith

/-- **Aux A3b (the discarding step's conclusion is not the trivial `0 <= _`).**
At a two-element carrier with `S = R = univ`, `g = 1` and `y = 1` the retained
density is `1`, and the bound it must clear is `betaLow 1 1 0 = 1`, so the
inequality is an equality.

**Degenerate on purpose, and outside the frozen regime.**  `g = 1` and `y = 1`
are *not* the block's values (`09:282` runs at `g = 91/92`, `y = 3/5`); the point
`(1, 1, 0)` is chosen only because it is the one where `betaLow` evaluates to
`1`, which is what refutes a `0 <= _` reading of the conclusion.  This probe
therefore certifies **nothing** about the frozen instance -- no legal-instance
claim, no strict positivity of retained density at `g = 91/92` -- and must not be
cited as one.  The legal-regime positivity is `betaLow_frozen_values`
(`beta_0 = 271/455`, `beta_1 = 19/65`, `beta_2 = 64/455`, all positive) together
with `betaLow_frozen_margins`. -/
theorem reference_density_after_discard_nondegenerate :
    betaLow (1 : ℝ) 1 0
        ≤ (((Finset.univ : Finset Bool) ∩ (Finset.univ : Finset Bool)).card : ℝ)
          / ((Finset.univ : Finset Bool).card : ℝ)
      ∧ betaLow (1 : ℝ) 1 0 = 1 := by
  have hval : betaLow (1 : ℝ) 1 0 = 1 := by
    rw [betaLow_apply]; norm_num
  refine ⟨?_, hval⟩
  rw [hval]
  simp

/-! ## §4  `eq:wrapper-reference-count` (`09:288--295`)

"If fewer than `ceil(q(beta_j - kappa_j x_T)/(1 - kappa_j x_T))` outer
coordinates had reference density at least `kappa_j x_T`, the total reference
density would be below `beta_j`.  Thus `eq:wrapper-reference-count` is a valid
lower bound on their number." -/

/-- **`eq:wrapper-reference-count` (`09:288--292`).**  The frozen count
`ceil(q(beta - tau)/(1 - tau))`, with `tau = kappa_j x_T`.  The ceiling is
`Nat.ceil`, matching the banked `rawLowGates` and `referenceProfileGates`
convention (a weakening of the frozen integer ceiling on negative arguments and
an equality on the legal range). -/
noncomputable def referenceCount (q : ℕ) (β τ : ℝ) : ℕ :=
  ⌈(q : ℝ) * (β - τ) / (1 - τ)⌉₊

/-- **Aux A4a.**  The frozen count is monotone in the forced density `beta`.
General; this is what lets the block work with a *lower bound* on `beta_j`
rather than its exact value. -/
theorem referenceCount_mono_beta {q : ℕ} {β β' τ : ℝ} (hτ : τ < 1)
    (h : β ≤ β') : referenceCount q β τ ≤ referenceCount q β' τ := by
  have hpos : (0 : ℝ) < 1 - τ := by linarith
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hmul : (q : ℝ) * (β - τ) ≤ (q : ℝ) * (β' - τ) :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  refine Nat.ceil_le_ceil ?_
  rw [div_le_div_iff₀ hpos hpos]
  nlinarith [mul_nonneg (sub_nonneg.mpr hmul) (le_of_lt hpos)]

/-- **`09:287--295`, the averaging argument, proved in general.**

Given per-outer-coordinate reference densities `d i in [0,1]` whose average is at
least `beta`, the number of coordinates with `d i >= tau` is at least
`ceil(q(beta - tau)/(1 - tau))`.

The frozen contrapositive is exactly the computation performed: the coordinates
below threshold contribute at most `tau` each and the others at most `1` each, so
`beta q <= |S| + (q - |S|) tau`, i.e. `|S|(1 - tau) >= q(beta - tau)`.  Since
`|S|` is a natural, the ceiling may be taken.  General in `q`, `d`, `beta` and
`tau`. -/
theorem referenceCount_le_card {q : ℕ} (d : Fin q → ℝ) {β τ : ℝ}
    (hd1 : ∀ i, d i ≤ 1) (hτ1 : τ < 1)
    (havg : β * (q : ℝ) ≤ ∑ i, d i) :
    referenceCount q β τ ≤ (Finset.univ.filter fun i => τ ≤ d i).card := by
  classical
  have hpos : (0 : ℝ) < 1 - τ := by linarith
  set S := Finset.univ.filter (fun i : Fin q => τ ≤ d i) with hSdef
  set T := Finset.univ.filter (fun i : Fin q => ¬ τ ≤ d i) with hTdef
  have hsplit : (∑ i ∈ S, d i) + ∑ i ∈ T, d i = ∑ i, d i := by
    rw [hSdef, hTdef]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ d
  have hS1 : ∑ i ∈ S, d i ≤ (S.card : ℝ) := by
    calc ∑ i ∈ S, d i ≤ ∑ _i ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hd1 i)
      _ = (S.card : ℝ) := by simp
  have hT1 : ∑ i ∈ T, d i ≤ (T.card : ℝ) * τ := by
    calc ∑ i ∈ T, d i ≤ ∑ _i ∈ T, τ := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [hTdef, Finset.mem_filter] at hi
          exact le_of_not_ge hi.2
      _ = (T.card : ℝ) * τ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcards : S.card + T.card = q := by
    rw [hSdef, hTdef]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin q))) (p := fun i : Fin q => τ ≤ d i)
    simpa using this
  have hTcast : (T.card : ℝ) = (q : ℝ) - (S.card : ℝ) := by
    have : (S.card : ℝ) + (T.card : ℝ) = (q : ℝ) := by exact_mod_cast hcards
    linarith
  have hmain : β * (q : ℝ) ≤ (S.card : ℝ) + ((q : ℝ) - (S.card : ℝ)) * τ := by
    rw [← hTcast]
    linarith [hsplit, havg, hS1, hT1]
  have hfinal : (q : ℝ) * (β - τ) / (1 - τ) ≤ (S.card : ℝ) := by
    rw [div_le_iff₀ hpos]
    nlinarith
  exact Nat.ceil_le.mpr hfinal

/-- **Aux A4c (the same count from integer retained masses).**  The form the
block actually consumes: the retained reference rows of outer coordinate `i` are
`ret i` out of `m_G`, and a coordinate is "dense" when `ret i >= tau m_G`.
General in `q`, `ret`, `m_G`, `beta` and `tau`; obtained from
`referenceCount_le_card` by normalizing, with no second averaging computation. -/
theorem referenceCount_le_card_of_nat {q mG : ℕ} (ret : Fin q → ℕ) {β τ : ℝ}
    (hmG : 0 < mG) (hret : ∀ i, ret i ≤ mG) (hτ1 : τ < 1)
    (havg : β * (q : ℝ) * (mG : ℝ) ≤ ∑ i, (ret i : ℝ)) :
    referenceCount q β τ
      ≤ (Finset.univ.filter fun i => τ * (mG : ℝ) ≤ (ret i : ℝ)).card := by
  classical
  have hmGpos : (0 : ℝ) < (mG : ℝ) := by exact_mod_cast hmG
  have hfilter :
      (Finset.univ.filter fun i : Fin q => τ * (mG : ℝ) ≤ (ret i : ℝ))
        = Finset.univ.filter fun i : Fin q => τ ≤ (ret i : ℝ) / (mG : ℝ) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h; rw [le_div_iff₀ hmGpos]; linarith
    · intro h; rw [le_div_iff₀ hmGpos] at h; linarith
  rw [hfilter]
  refine referenceCount_le_card (fun i => (ret i : ℝ) / (mG : ℝ)) (fun i => ?_) hτ1 ?_
  · rw [div_le_one hmGpos]
    exact_mod_cast hret i
  · have hsum : ∑ i, ((ret i : ℝ) / (mG : ℝ)) = (∑ i, (ret i : ℝ)) / (mG : ℝ) :=
      (Finset.sum_div _ _ _).symm
    rw [hsum, le_div_iff₀ hmGpos]
    exact havg

/-! ## §5  `eq:wrapper-low-rung-gates` (`09:303--309` = `06:927--934`)

"The single sufficient condition `q x_T <= 4/25025` implies, together with the
exact ceiling checks retained by the construction, that
`eq:wrapper-reference-count` is at least `9 kappa_j/16`." -/

/-- **`eq:wrapper-low-rung-gates` (`06:927--934`), transcribed.**

Both frozen clauses: the three exact ceiling comparisons
`ceil(q(beta_j - kappa_j x_T)/(1 - kappa_j x_T)) >= (9/16) kappa_j`, and the
single sufficient condition `q x_T <= 4/25025`.  The comparison is stated in `ℝ`,
so the frozen rational `(9/16) kappa_j` is exact and no natural division
truncates it.  Stated as a predicate and never asserted. -/
def wrapperLowRungGates (r : ℕ) (xT : ℝ) : Prop :=
  (∀ j : ℕ, j ≤ 2 →
      9 * ((kappaLow r j : ℕ) : ℝ) / 16
        ≤ ((referenceCount (2 ^ r) (betaLow (3 / 5) (91 / 92) j)
              (((kappaLow r j : ℕ) : ℝ) * xT) : ℕ) : ℝ))
    ∧ ((2 : ℝ) ^ r) * xT ≤ 4 / 25025

/-- **`09:303--309`, the sufficient condition proved sufficient.**

From `q x_T <= 4/25025` (and `x_T >= 0`, `2 <= r`) all three exact ceiling
comparisons follow, hence the whole of `eq:wrapper-low-rung-gates`.  The three
rung computations are the frozen margins cleared of denominators:

* `j = 0`: `(beta_0 - tau)/(1 - tau) >= 9/16` iff `tau <= 241/3185`;
* `j = 1`: `(beta_1 - tau)/(1 - tau) >= 9/32` iff `tau <= 1/65`;
* `j = 2`: `(beta_2 - tau)/(1 - tau) >= 9/64` iff `tau <= 1/25025`,

and `tau = kappa_j x_T = q x_T/2^j`, so the gate gives `4/25025`, `2/25025` and
`1/25025` at the three rungs.  The third is an **equality** at the boundary --
see `wrapperLowRung_gate_is_tight`.  General in `r` and `x_T`. -/
theorem wrapperLowRungGates_of_simple_gate {r : ℕ} {xT : ℝ}
    (hr : 2 ≤ r) (hxT0 : 0 ≤ xT) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025) :
    wrapperLowRungGates r xT := by
  obtain ⟨e0, e1, e2⟩ := betaLow_frozen_values
  refine ⟨fun j hj => ?_, hgate⟩
  have hjr : j ≤ r := le_trans hj hr
  have hq : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hA : (0 : ℝ) ≤ (2 : ℝ) ^ r * xT := by positivity
  have hjp : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hj1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hκ : ((kappaLow r j : ℕ) : ℝ) = (2 : ℝ) ^ r / 2 ^ j := kappaLow_cast hjr
  set τ : ℝ := ((kappaLow r j : ℕ) : ℝ) * xT with hτdef
  have hτeq : τ = (2 : ℝ) ^ r * xT / 2 ^ j := by rw [hτdef, hκ]; ring
  have hτ0 : 0 ≤ τ := by rw [hτeq]; positivity
  have hτle : τ ≤ 4 / 25025 / 2 ^ j := by
    rw [hτeq, div_le_div_iff₀ hjp hjp]
    nlinarith
  have hτsmall : τ ≤ 4 / 25025 := by
    have : (4 : ℝ) / 25025 / 2 ^ j ≤ 4 / 25025 := div_le_self (by norm_num) hj1
    linarith
  have hτ1 : τ < 1 := by linarith
  have hpos : (0 : ℝ) < 1 - τ := by linarith
  -- the frozen per-rung margin comparison, cleared of denominators
  have hmargin : 9 / (16 * 2 ^ j) * (1 - τ) ≤ betaLow (3 / 5) (91 / 92) j - τ := by
    interval_cases j
    · rw [e0]
      have h : τ ≤ 4 / 25025 := by simpa using hτle
      norm_num
      linarith
    · rw [e1]
      have h : τ ≤ 4 / 25025 / 2 := by simpa using hτle
      norm_num
      linarith
    · rw [e2]
      have h : τ ≤ 4 / 25025 / 4 := by
        have h2 : (4 : ℝ) / 25025 / 2 ^ (2 : ℕ) = 4 / 25025 / 4 := by norm_num
        rw [h2] at hτle; exact hτle
      norm_num
      linarith
  have hdiv : 9 / (16 * 2 ^ j) ≤ (betaLow (3 / 5) (91 / 92) j - τ) / (1 - τ) := by
    rw [le_div_iff₀ hpos]
    exact hmargin
  -- multiply by `q = 2^r >= 0` and take the ceiling
  have hcast : (((2 : ℕ) ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r := by push_cast; ring
  have hstep : 9 * ((kappaLow r j : ℕ) : ℝ) / 16
      ≤ ((2 ^ r : ℕ) : ℝ) * (betaLow (3 / 5) (91 / 92) j - τ) / (1 - τ) := by
    rw [hcast]
    have hleft : 9 * ((kappaLow r j : ℕ) : ℝ) / 16
        = (2 : ℝ) ^ r * (9 / (16 * 2 ^ j)) := by
      rw [hκ]; field_simp
    have hright : (2 : ℝ) ^ r * (betaLow (3 / 5) (91 / 92) j - τ) / (1 - τ)
        = (2 : ℝ) ^ r * ((betaLow (3 / 5) (91 / 92) j - τ) / (1 - τ)) := by
      ring
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hdiv (le_of_lt hq)
  exact le_trans hstep (Nat.le_ceil _)

/-- **Statement pole (`4/25025` is a boundary, not a margin).**

The exact admissible bound on `kappa_2 x_T` is `(64 beta_2 - 9)/55 = 1/25025`
precisely, and the frozen `q x_T <= 4/25025` gives `kappa_2 x_T = q x_T/4
<= 1/25025` with equality attainable.  The second conjunct shows the comparison
**fails** as soon as `kappa_2 x_T` exceeds that value, so no larger constant than
`4/25025` would do and the gate is doing real work at `j = 2`.

This is why `j = 2` is the binding rung here, exactly as `j = 2` is the binding
rung for the *inner* gate in the banked opening -- but at the strictly smaller
slack `1/29120`, which is why the opening's margin may not be reused. -/
theorem wrapperLowRung_gate_is_tight :
    (64 * betaLow (3 / 5) (91 / 92) 2 - 9) / 55 = 1 / 25025
      ∧ ∀ τ : ℝ, 1 / 25025 < τ → τ < 1 →
          (betaLow (3 / 5) (91 / 92) 2 - τ) / (1 - τ) < 9 / 64 := by
  obtain ⟨-, -, e2⟩ := betaLow_frozen_values
  refine ⟨by rw [e2]; norm_num, fun τ hτ hτ1 => ?_⟩
  have hpos : (0 : ℝ) < 1 - τ := by linarith
  rw [e2, div_lt_iff₀ hpos]
  nlinarith

/-- **`09:327` in exponent form, and the guard `A:118` discharged.**

"`q/4 >= t_ref` makes all three values of `r'` legal", and `A:118`'s guard
`t x <= 1`.  With `q = 2^r` and `t_ref = 2^k` the first is `k + 2 <= r`; the
second then follows from the block's own gate, because
`t_ref x_T <= q x_T <= 4/25025 <= 1`.  So the endpoint's row-request legality is
**not** an extra assumption here -- it is a consequence of
`eq:wrapper-low-simple-gate`.  General. -/
theorem simple_gate_forces_tRef_row_legality {r k : ℕ} {xT : ℝ}
    (hq4 : k + 2 ≤ r) (hxT0 : 0 ≤ xT) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025) :
    ((2 : ℝ) ^ k) * xT ≤ 1 := by
  have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

/-- **Non-vacuity (tier 2): the frozen gates hold throughout the legal range.**

`eq:wrapper-low-rung-gates` is exhibited for **every** pair `(k, r)` the frozen
gates allow -- `4 <= k` (the endpoint's "power of two divisible by `16`",
`A:117--118`) and `k + 2 <= r` (`q/4 >= t_ref`, `09:327`) -- at
`x_T = 1/(2^r . 65536)`, for which `q x_T = 1/65536 <= 4/25025`.

No numeral is pinned for `k`, `r` or `x_T`, and none could be:
`eq:tref-search` (`06:558--572`) forces `k = k_ref >= 2^19`, so every small value
of `k` is *illegal*, and `x_T = 2^{-b_T}` with `b_T` fixed by `06:238--242`.
What the witness fixes is the single ratio `q x_T` that the gate constrains, and
nothing else; no parameter may be read out of it. -/
theorem wrapperLowRungGates_legal_instance (k r : ℕ) (hk : 4 ≤ k)
    (hq4 : k + 2 ≤ r) :
    wrapperLowRungGates r (1 / ((2 : ℝ) ^ r * 65536))
      ∧ 0 < 1 / ((2 : ℝ) ^ r * 65536)
      ∧ ((2 : ℝ) ^ r) * (1 / ((2 : ℝ) ^ r * 65536)) = 1 / 65536 := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hval : ((2 : ℝ) ^ r) * (1 / ((2 : ℝ) ^ r * 65536)) = 1 / 65536 := by
    field_simp
  refine ⟨?_, by positivity, hval⟩
  refine wrapperLowRungGates_of_simple_gate (by omega) (by positivity) ?_
  rw [hval]
  norm_num

/-! ## §6  The `09:311--331` substitution into `thm:certified-localized-extension`

"Project the retained outer column set to any `9 kappa_j/16` such coordinates.
Its normalized density remains at least `theta`, by specified-coordinate
projection.  Apply the certified-scale reference stopping lemma,
`thm:certified-localized-extension`, using its fixed `y_* = 3/5` and the
substitutions `M = G`, `H = C-1`, `x = x_T`, `t = t_ref`, `r = q/t_ref`,
`r' = kappa_j/t_ref`, `eps = 0`, `h = theta`, `a^sharp = 0`." -/

/-- **Aux A6a (`A:125`: `r` and `r'` are positive powers of two with `r' <= r`).**

In exponent form under `q/4 >= t_ref` (`09:327`): `r = 2^{rExp - k}`,
`r'_j = 2^{rExp - j - k}`, the exponents are honest naturals (their subtractions
do not truncate), `r'_j <= r`, and both are positive.  This is exactly what
`09:327` says "makes all three values of `r'` legal".  General. -/
theorem refExtensionExponents {r j k : ℕ} (hj : j ≤ 2) (hq4 : k + 2 ≤ r) :
    (r - j - k) + k = r - j
      ∧ r - j - k ≤ r - k
      ∧ 0 < (2 : ℕ) ^ (r - j - k)
      ∧ (2 : ℕ) ^ (r - j - k) ≤ 2 ^ (r - k) := by
  refine ⟨by omega, by omega, pow_pos (by norm_num) _, ?_⟩
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Aux A6b (`A:138--139`: exactly `r' p_t` represented outer blocks).**

`r'_j p_{t_ref} = (kappa_j/t_ref)(9 t_ref/16) = 9 kappa_j/16`, exactly and
without rounding, because `t_ref` is a power of two divisible by `16`
(`A:117--118`, in exponent form `4 <= k`).  The identity is the banked
`DenseAliceClosure.extensionSelectedBlocks` -- the *same* substitution
arithmetic for the *same* inherited endpoint -- consumed by pin at
`(rho', k_2) = (r - j - k, k)`; only the closing rewrite to `kappaLow` is new. -/
theorem refExtensionBlocks {r j k : ℕ} (hj : j ≤ 2) (hk : 4 ≤ k)
    (hq4 : k + 2 ≤ r) :
    2 ^ (r - j - k) * (9 * 2 ^ k / 16) = 9 * kappaLow r j / 16 := by
  have h := extensionSelectedBlocks (ρ' := r - j - k) (k₂ := k) hk
  rw [h]
  congr 2
  rw [kappaLow_def]
  congr 1
  omega

/-- **Aux A6c (`A:142--144`: the endpoint's output is the frozen rung value).**

`H + log_2(r' t) = (C-1) + log_2 kappa_j = C + log_2 q - 1 - j`, which is
`09:330--331` verbatim.  The identity is on exponents, so nothing is recovered
by `Nat.log`; and the double natural subtraction is exact, which is what
`ScaleAlignOpening.wrapperLow_subtraction_free` certifies and this lemma
re-checks in the present indices.  General. -/
theorem refExtensionOutput {r j k C : ℕ} (hj : j ≤ 2) (hq4 : k + 2 ≤ r)
    (hC : 3 ≤ C) :
    (C - 1) + (r - j) = C + r - 1 - j
      ∧ ((C - 1) + (r - j) ≤ C + r - 1 - j)
      ∧ (C + r - 1 - j) + (1 + j) = C + r := by
  refine ⟨by omega, by omega, by omega⟩

/-- **`09:288--313` composed: at least `9 kappa_j/16` outer coordinates carry the
requested reference density.**

The three frozen steps in one statement: `09:285--287` supplies the average
(hypothesis `havg`, the output of `reference_density_after_discard` at the pinned
`g = 91/92`), `09:288--295` turns it into the count
`eq:wrapper-reference-count` (`referenceCount_le_card`), and `09:303--309`
turns the count into `9 kappa_j/16` (the gate).  General in `r`, `j`, the
densities `d` and `x_T`. -/
theorem wrapperReferenceCount_ge {r j : ℕ} (d : Fin (2 ^ r) → ℝ) {xT : ℝ}
    (hj : j ≤ 2) (hr : 2 ≤ r) (hxT0 : 0 ≤ xT)
    (hgate : wrapperLowRungGates r xT)
    (hd1 : ∀ i, d i ≤ 1)
    (havg : betaLow (3 / 5) (91 / 92) j * (((2 : ℕ) ^ r : ℕ) : ℝ) ≤ ∑ i, d i) :
    9 * ((kappaLow r j : ℕ) : ℝ) / 16
      ≤ ((Finset.univ.filter fun i => ((kappaLow r j : ℕ) : ℝ) * xT ≤ d i).card : ℝ) := by
  classical
  obtain ⟨hceil, hsimple⟩ := hgate
  have hjr : j ≤ r := le_trans hj hr
  have hκ : ((kappaLow r j : ℕ) : ℝ) = (2 : ℝ) ^ r / 2 ^ j := kappaLow_cast hjr
  have hjp : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hj1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hA : (0 : ℝ) ≤ (2 : ℝ) ^ r * xT := by positivity
  set τ : ℝ := ((kappaLow r j : ℕ) : ℝ) * xT with hτdef
  have hτeq : τ = (2 : ℝ) ^ r * xT / 2 ^ j := by rw [hτdef, hκ]; ring
  have hτ0 : 0 ≤ τ := by rw [hτeq]; positivity
  have hτ1 : τ < 1 := by
    have hle : τ ≤ (2 : ℝ) ^ r * xT := by rw [hτeq]; exact div_le_self hA hj1
    linarith
  have hcount := referenceCount_le_card d hd1 hτ1 havg
  have hcast : ((referenceCount (2 ^ r) (betaLow (3 / 5) (91 / 92) j) τ : ℕ) : ℝ)
      ≤ (((Finset.univ.filter fun i => τ ≤ d i).card : ℕ) : ℝ) := by
    exact_mod_cast hcount
  exact le_trans (hceil j hj) hcast

/-- **`09:313--331`: the certified Localized Extension applied at the frozen
substitution.**

`thm:certified-localized-extension` (`A:109--146`) is the named binder `hLocEx`,
in the exact implication shape the frozen theorem has.  Its antecedents appear
below **in the order `A:110--147` prints them**, at the `09:317--323`
substitution `M = G`, `H = C-1`, `x = x_T`, `t = t_ref = 2^k`,
`r = q/t_ref = 2^{rExp-k}`, `r' = kappa_j/t_ref = 2^{rExp-j-k}`, `eps = 0`,
`h = theta`, `a^sharp = 0`, `y_* = 3/5`.

Discharged here, from this block's own data:

* `H >= 2`, i.e. `2 <= C - 1`, from the frozen `C >= 3` of `09:240`;
* the guard `t x <= 1` (`A:118`), from `eq:wrapper-low-simple-gate`
  (`simple_gate_forces_tRef_row_legality`);
* `r'` legality (`A:125`), from `q/4 >= t_ref` (`refExtensionExponents`);
* the represented-block identity `r' p_t = 9 kappa_j/16` (`A:138--139`,
  `refExtensionBlocks`);
* the represented-block **availability** `9 kappa_j/16 <= |{dense coordinates}|`,
  which is `eq:wrapper-reference-count` plus the gate (hypothesis `hcount`,
  produced by `wrapperReferenceCount_ge`);
* `eps = 0` and `a^sharp = 0`, the two substitution choices of `09:322`,
  passed as the literal equalities the endpoint's branch selection needs
  (`09:326`: "the reference restriction is a full product, so its balancedness
  error is exactly zero");
* the output arithmetic `H + log_2(r' t) = C + log_2 q - 1 - j`
  (`refExtensionOutput`).

Left as named hypotheses, because they belong to `06`, not to this block:
`htcert` (`t_ref >= t_cert`, `A:117`), `hE1` and `hE2` (`eq:certified-E1`,
`eq:certified-E2`), all three discharged by `eq:tref-search` per `06:574--578`;
`hbase` (`eq:certified-base`, which **is** the second clause of the banked
`lem:wrapper-reference`); `hcol`, the specified-coordinate projection of
`09:312--313`; and the carrier/parameter guards.

`hE1` is stated in its `t`-th-power form: at `eps = 0` the frozen
`(h 2^{-(H+log_2 q)})^{1/t} >= y_*` is equivalent, for nonnegative arguments, to
`h 2^{-(H+log_2 q)} >= y_*^t`.  The rewriting is recorded, not performed
silently.

General in the member type, in its cost, in `C`, `r`, `k`, `j`, and in the real
parameters `x_T`, `theta`. -/
theorem wrapperLowExtension {Mem : Type*} (memCost : Mem → ℕ) (mem : Mem)
    {C r k j tcert selCard : ℕ} {xT θ colDens : ℝ}
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool)
    (hj : j ≤ 2) (hk : 4 ≤ k) (hq4 : k + 2 ≤ r) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hcount : 9 * ((kappaLow r j : ℕ) : ℝ) / 16 ≤ (selCard : ℝ))
    -- `eq:certified-base` (`A:113--116`), the banked `lem:wrapper-reference`
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    -- `A:117`, the certified width floor; `eq:tref-search` (`06:558--572`)
    (htcert : tcert ≤ 2 ^ k)
    -- `eq:certified-E1` (`A:130--134`) at `eps = 0`, in `t`-th-power form
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    -- `eq:certified-E2` (`A:135--136`) at `eps = 0`, at the frozen `h_t`
    (hE2 : hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    -- `A:141` at `a^sharp = 0`: the projected column density of `09:312--313`
    (hcol : θ / 2 ^ (0 : ℕ) ≤ colDens)
    (hLocEx :
      -- `A:111`, `M` a nonempty Boolean matrix, and `H >= 2`
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      -- `A:112`, `0 < x <= 1` -- **strict** on the left, exactly as the frozen
      -- theorem prints it; weakening this antecedent would strengthen the
      -- assumed implication past `thm:certified-localized-extension`
      0 < xT → xT ≤ 1 →
      -- `A:113--116`, `eq:certified-base`
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      -- `A:117--118`, `t >= t_cert`, a power of two divisible by `16`, `t x <= 1`
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      -- `A:125`, `r, r'` positive powers of two with `r' <= r`, `q = r t`
      0 < (2 : ℕ) ^ (r - j - k) →
      (2 : ℕ) ^ (r - j - k) ≤ 2 ^ (r - k) →
      2 ^ (r - j - k) * 2 ^ k = kappaLow r j →
      -- `A:126--128`, the exact full product: `eps = 0`
      (0 : ℝ) = 0 →
      -- `A:128--129`, `h in (0,1]` and `a^sharp = 0`
      0 < θ → θ ≤ 1 → θ / 2 ^ (0 : ℕ) ≤ colDens →
      -- `eq:certified-E1`, `eq:certified-E2`
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      -- `A:138--139`, exactly `r' p_t` represented outer blocks, and enough of them
      2 ^ (r - j - k) * (9 * 2 ^ k / 16) = 9 * kappaLow r j / 16 →
      9 * ((kappaLow r j : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
      -- `A:142--144`, the conclusion `H + log_2(r' t)`
      (C - 1) + (r - j) ≤ memCost mem) :
    C + r ≤ j + 1 + memCost mem := by
  have hguard : ((2 : ℝ) ^ k) * xT ≤ 1 :=
    simple_gate_forces_tRef_row_legality hq4 (le_of_lt hxT0) hgate
  obtain ⟨hexp, hle, hpos, hpow⟩ := refExtensionExponents (r := r) hj hq4
  have hmul : 2 ^ (r - j - k) * 2 ^ k = kappaLow r j := kappaLow_mul_tRef hj hq4
  have hblocks : 2 ^ (r - j - k) * (9 * 2 ^ k / 16) = 9 * kappaLow r j / 16 :=
    refExtensionBlocks hj hk hq4
  have hout := hLocEx hGne (by omega) hxT0 hxT1 hbase htcert hk hguard hpos hpow hmul
    rfl hθ0 hθ1 hcol hE1 hE2 hblocks hcount
  obtain ⟨h1, -, -⟩ := refExtensionOutput (r := r) (j := j) (k := k) hj hq4 hC
  omega

/-- **`wrapperLowExtension` specialized at the legal tier
`x_T = 1/(2^r . 65536)`.**

This is a **specialization, not a satisfiability witness.**  It discharges
exactly the three antecedents this block owns at that tier -- `hxT0`
(`0 < x_T`, `by positivity`, the strict `A:112` form), `hxT1` (`x_T <= 1`) and
`hgate` (`q x_T = 1/65536 <= 4/25025`) -- for an arbitrary pair `(k, r)` in the
legal range (`4 <= k`, `k + 2 <= r`), and carries `hbase`, `htcert`, `hE1`,
`hE2`, `hcol` and `hLocEx` through unchanged as binders.

**It exhibits no inhabitant of `hLocEx`, `hbase`, `hE1`, `hE2` or `hcol`, and
therefore establishes no joint satisfiability of the full bundle.**  Nor could a
small numeral be used to try: at the small end of the quantified range `hE1` and
`hE2` are in fact *unsatisfiable* -- at `k = 4`, `C = 3` they would need
`2^{0.49 sqrt k} >= C - 1 + k`, i.e. `1.97 >= 6` -- which is precisely why
`eq:tref-search` (`06:558--572`) forces `k_ref >= 2^19`.  That is also why `k`
and `r` are quantified and not pinned: no small numeral is a legal value of `k`,
and `x_T = 2^{-b_T}` with `b_T` fixed by `06:238--242`.  What this theorem does
establish is that the block-owned side of the antecedent set is simultaneously
satisfiable in the legal range, so those three binders are not silently
contradictory. -/
theorem wrapperLowExtension_fires_at_legal_tier {Mem : Type*}
    (memCost : Mem → ℕ) (mem : Mem) {C r k j tcert selCard : ℕ} {θ colDens : ℝ}
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool)
    (hj : j ≤ 2) (hk : 4 ≤ k) (hq4 : k + 2 ≤ r) (hC : 3 ≤ C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hGne : 1 ≤ Fintype.card Rw)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (1 / ((2 : ℝ) ^ r * 65536)) (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcol : θ / 2 ^ (0 : ℕ) ≤ colDens)
    (hcount : 9 * ((kappaLow r j : ℕ) : ℝ) / 16 ≤ (selCard : ℝ))
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < (1 : ℝ) / ((2 : ℝ) ^ r * 65536) → (1 : ℝ) / ((2 : ℝ) ^ r * 65536) ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (1 / ((2 : ℝ) ^ r * 65536)) (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * (1 / ((2 : ℝ) ^ r * 65536)) ≤ 1 →
      0 < (2 : ℕ) ^ (r - j - k) →
      (2 : ℕ) ^ (r - j - k) ≤ 2 ^ (r - k) →
      2 ^ (r - j - k) * 2 ^ k = kappaLow r j →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (0 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ (r - j - k) * (9 * 2 ^ k / 16) = 9 * kappaLow r j / 16 →
      9 * ((kappaLow r j : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
      (C - 1) + (r - j) ≤ memCost mem) :
    C + r ≤ j + 1 + memCost mem := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hval : ((2 : ℝ) ^ r) * (1 / ((2 : ℝ) ^ r * 65536)) = 1 / 65536 := by
    field_simp
  refine wrapperLowExtension memCost mem Gmat hj hk hq4 hC (by positivity) ?_ hθ0
    hθ1 hGne ?_ hcount hbase htcert hE1 hE2 hcol hLocEx
  · rw [div_le_one (by positivity)]
    nlinarith
  · rw [hval]; norm_num

/-! ## §7  The wiring (`09:333`): `eq:wrapper-u-low` discharged and composed

"This proves `eq:wrapper-u-low`."  The per-member rung bound is lifted to the
bracket family through the vendored `EthBridge.le_Dfamily`, and the result is
handed to the banked `ScaleAlignOpening.firstWrapper` in the exact shape its
`hLowRungs` binder demands, retiring that binder. -/

/-- **`eq:wrapper-u-low` (`09:264--266`), in the banked `firstWrapper` shape.**

The frozen conclusion of `sec:wrapper-low-rungs` is
`comp<U,1,y/2^j,theta> >= C + log_2 q - 1 - j` for `j = 0,1,2`
(`09:330--333`).  What is proved here is the passage from the per-member bound
`hmem` -- the output of `wrapperLowExtension` at each member of the bracket
family -- to the family bound, which is the vendored `EthBridge.le_Dfamily`
consumed by pin, together with the subtraction-free reading certified by the
banked `ScaleAlignOpening.wrapperLow_subtraction_free`.

`Dfamily` is a `Nat.sInf` and returns `0` on the empty family, so the
nonemptiness side condition `hne` is carried explicitly and never assumed away.

General in the carriers, in `N`, in `r`, `C`, and in the real parameters `y` and
`theta`. -/
theorem wrapperLowRungs {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {y θ : ℝ} (hC : 3 ≤ C)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2)) :
    ∀ j : ℕ, j ≤ 2 →
      C + r ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat r) 1)
        (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ) := by
  intro j hj
  have hfam : C + r - 1 - j
      ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
          (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ) := by
    refine EthBridge.le_Dfamily _ _ (C + r - 1 - j) (hne j hj) (fun RC hRC => ?_)
    have := hmem j hj RC hRC
    omega
  have hshape := (wrapperLow_subtraction_free (CW := C + r) (j := j)
    (d := Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ))
    (by omega) hj).1
  exact hshape.mp hfam

/-- **Statement pole for `wrapperLowRungs`.**

The rung conclusion is not automatic.  At the constant matrix over two-element
carriers the whole interlace is constant, so every member of every bracket family
has complexity `0`, hence the family complexity is `0` -- which misses
`C + r - 1 - j >= 1` for every legal `C >= 3` and `j <= 2`.  The value therefore
comes from `hmem`, i.e. from the inherited endpoint, and cannot be read off the
bracket shape.

The probe is stated on the per-member hypothesis directly, which is where the
content sits: at the constant matrix `hmem` itself is **false** at every
member. -/
theorem wrapperLowRungs_not_automatic (r : ℕ)
    (RC : Finset (Fin 1 × (Fin (2 ^ r) × Bool))
      × Finset (Fin 1 → (Fin (2 ^ r) → Bool))) :
    D (subgame (interlaceFun (wrapperU (fun (_ : Bool) (_ : Bool) => false) r) 1)
        RC.1 RC.2) = 0 := by
  have hconst : subgame (interlaceFun
      (wrapperU (fun (_ : Bool) (_ : Bool) => false) r) 1) RC.1 RC.2
      = fun _ _ => false := rfl
  rw [hconst]
  exact D_const false

/-- **Anti-over-strength readout: the rung binder is not an over-demand.**

`Dfamily` is a minimum over members, so it is bounded above by the complexity of
the ambient interlace, which `hN` and the banked interlace selector pin at
`C + r`.  The value `eq:wrapper-u-low` demands is `C + r - 1 - j <= C + r`, so
the demanded bound never exceeds what the ambient matrix can supply and
`hmem` cannot be contradictory with `hN` for a magnitude reason.  The second
conjunct records that the double natural subtraction is exact at the frozen side
conditions `C >= 3` and `j <= 2`, so nothing is silently truncated.

This is the check a hypothesis bundle whose green build proves nothing would
fail, and it is the low-rung twin of the banked
`ScaleAlignOpening.firstWrapper_dense_is_saturated`.  General. -/
theorem wrapperLowRungs_not_over_demanded {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C j : ℕ) {y θ : ℝ} (hj : j ≤ 2) (hC : 3 ≤ C)
    (hN : D Nmat = C) (hθ1 : θ ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) :
    Dfamily (interlaceFun (wrapperU Nmat r) 1)
        (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ) ≤ C + r
      ∧ (C + r - 1 - j) + (1 + j) = C + r := by
  classical
  haveI : DecidableEq (Fin (2 ^ r) × Rw) := Classical.decEq _
  have hqpos : 0 < 2 ^ r := pow_pos (by norm_num) r
  have hRwne : Nonempty Rw := Fintype.card_pos_iff.mp hRw
  have hcard : 1 ≤ Fintype.card (Fin (2 ^ r) × Rw) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, hqpos⟩, Classical.arbitrary Rw)⟩
  have hz1 : y / 2 ^ j ≤ 1 := by
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    exact le_trans (div_le_self (le_of_lt hy0) hp) hy1
  have hne := bracketGE.nonempty (X := Fin (2 ^ r) × Rw) (Y := Fin (2 ^ r) → Cl)
    1 (y / 2 ^ j) θ hz1 hθ1 hcard
  have hfam := familyComplexity_le_ambient (interlaceFun (wrapperU Nmat r) 1) hne
  have hone : D (interlaceFun (wrapperU Nmat r) 1) ≤ D (wrapperU Nmat r) := by
    have h1 := interlace_selector_upper (wrapperU Nmat r) 1 (le_refl 1)
    rwa [Nat.clog_one_right, Nat.add_zero] at h1
  have hupper : D (wrapperU Nmat r) ≤ C + r := by
    have := wrapperU_yes_upper Nmat r
    rwa [hN] at this
  exact ⟨le_trans hfam (le_trans hone hupper), by omega⟩


/-- **`thm:first-wrapper` with the `hLowRungs` binder retired (`09:333`).**

The banked `ScaleAlignOpening.firstWrapper` carries two deferred binders; this
composition discharges one of them from `sec:wrapper-low-rungs` and returns the
same seven conclusions.  The remaining binder set is carried honestly and in
full:

* `hDenseRung` -- `eq:wrapper-u-dense`, whose proof is the five blocks
  `09:335--1781`, unchanged and still GAP-EXPOSED;
* `hne` and `hmem` -- the bracket nonemptiness and the per-member rung bound, the
  latter being what `wrapperLowExtension` produces from the inherited endpoint
  binder `hLocEx` plus the `06`-owned `htcert`, `hE1`, `hE2` and the projection
  `hcol`.

Nothing here weakens `firstWrapper`: `theta` is quantified exactly as it is
there, `y` is quantified exactly as it is there, and the seven conclusions are
returned verbatim.  In particular the three output-contract clauses
`eq:common-exact`--`eq:common-low` of `09:14--23` -- which `09:23` says are all
the next section consumes -- now depend on **one** deferred half of
`thm:first-wrapper` instead of two. -/
theorem firstWrapperOfLowRungs {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ y : ℝ}
    (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hDenseRung : C + r ≤ Dfamily (interlaceFun (wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ))
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame (interlaceFun (wrapperU Nmat r) 1) RC.1 RC.2)) :
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
      ∧ C + r - 1 ≤ LambdaGE (wrapperW Nmat r) 1 θ y :=
  firstWrapper Nmat r C hC hN hθ0 hθ1 hδ0 hδ1 hy0 hy1 hRw hCl hDenseRung
    (wrapperLowRungs Nmat r C hC hne hmem)

/-! ## §8  The `A:112` repair battery

`thm:certified-localized-extension` prints its density hypothesis as
`0 < x \le 1` (`A:112`, inside the statement `A:109--146` labelled `A:110`).
The `r0` round of this module carried it as `0 \le x`, both as
`wrapperLowExtension`'s binder and -- decisively -- as the **third antecedent of
the assumed implication `hLocEx`**.  Relaxing an antecedent of an *assumed*
implication strengthens the assumption, so the `r0` `hLocEx` asserted the
Localized Extension conclusion at `x = 0`, where the frozen theorem says nothing
and where the conclusion is in fact false.

The five results below are the receipts for that repair, one per role.  They are
about the **hypothesis form**, not about the geometry: none of them constructs a
restriction of `G`, none discharges the endpoint, and none claims a reader item
-- the reader's `A-stage4-details.tex` rung display at lines 361--368 is claimed
by `wrapperLowRungs` and by nothing else, and the reader states no counterpart
for the antecedent bookkeeping, so every declaration here carries its
autoformalization anchor alone. -/

/-- **Battery N1 (the weakens receipt).**

The repair loses nothing: whatever the `r0` non-strict form of an assumed
implication delivered, the frozen strict form of `A:112` delivers too.  Stated
in general on the antecedent position itself -- an arbitrary real `xT`, an
arbitrary remaining antecedent block `Pre`, an arbitrary conclusion `Concl` --
because that is the whole content: `0 < xT` implies `0 <= xT`, so an assumption
quantified over the larger antecedent set specialises to the smaller one.

Consequences for this module, both discharged: `wrapperLowExtension` may still
be applied wherever the `r0` shape would have applied, and every downstream
consumer of `firstWrapperOfLowRungs` is unaffected.  The converse direction does
**not** hold -- see `locEx_strict_strictly_weaker` -- which is precisely why the
repair is a real change of statement and not a rename. -/
theorem locEx_strict_of_nonstrict {xT : ℝ} {Pre Concl : Prop}
    (hr0 : 0 ≤ xT → Pre → Concl) : 0 < xT → Pre → Concl :=
  fun hpos hpre => hr0 (le_of_lt hpos) hpre

/-- **Battery N2 (statement pole: the repaired hypothesis is *strictly* weaker).**

`locEx_strict_of_nonstrict` alone would be satisfied by a cosmetic change, so
this pole exhibits data at which the receipt has **no converse**: the strict form
holds while the non-strict form fails.  At `xT = 0` the strict antecedent
`0 < xT` is unsatisfiable, so the strict implication is vacuously true; the
non-strict antecedent `0 <= xT` is satisfied, so the non-strict implication
asserts its conclusion outright, and at a false conclusion that is a refutation.

**Why the trivial witness fails.**  The existential is over `(xT, Pre, Concl)`
and a lazy witness would take `Concl := True`: that satisfies the first conjunct
but makes the second conjunct false, since `0 <= xT -> Pre -> True` is provable.
Symmetrically `Concl := False` with `xT := 1` satisfies the second conjunct and
fails the first.  Only a witness that pins `xT` at the boundary `0` -- the exact
point the frozen `A:112` excludes and the `r0` shape admitted -- satisfies both,
which is the content: the two hypothesis forms differ *only* at `x = 0`, and
they do differ there.

Not a claim about `thm:certified-localized-extension`; a claim about the two
antecedent shapes. -/
theorem locEx_strict_strictly_weaker :
    ∃ xT : ℝ, ∃ Pre Concl : Prop,
      (0 < xT → Pre → Concl) ∧ ¬ (0 ≤ xT → Pre → Concl) := by
  refine ⟨0, True, False, ?_, ?_⟩
  · intro h
    exact absurd h (lt_irrefl 0)
  · intro h
    exact h le_rfl trivial

/-- **Battery N3 (`A:118` under the repaired `A:112`): the strict row-legality
transport.**

`simple_gate_forces_tRef_row_legality` keeps its own `0 <= xT` binder, because it
is this block's gate arithmetic (`eq:wrapper-low-simple-gate`, `09:304--307`) and
not a transcription of `A:112`.  What the repair needs in addition is that the
strictness *survives the substitution* `t = t_ref = 2^k` of `09:319`: the
endpoint's guard `t x <= 1` (`A:118`) is consumed together with `A:112`, and if
`t_ref x_T` could vanish the guard would be met by the same degenerate data the
repair excludes.

Both clauses at once, therefore: `0 < t_ref x_T` and `t_ref x_T <= 1`, from
`q/4 >= t_ref` (`09:327`, in exponent form `k + 2 <= r`) and the frozen gate.
The second conjunct is the banked non-strict transport, threaded through
`le_of_lt` exactly as `wrapperLowExtension` threads it; the first is new and is
what makes the strict form propagate.  General in `r`, `k` and `xT`. -/
theorem simple_gate_forces_strict_tRef_row_legality {r k : ℕ} {xT : ℝ}
    (hq4 : k + 2 ≤ r) (hxT0 : 0 < xT) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025) :
    0 < ((2 : ℝ) ^ k) * xT ∧ ((2 : ℝ) ^ k) * xT ≤ 1 :=
  ⟨by positivity,
    simple_gate_forces_tRef_row_legality hq4 (le_of_lt hxT0) hgate⟩

/-- **Battery N4 (non-vacuity, tier 2): the *strict* `A:112` membership is
inhabited at the banked legal tier.**

A repaired hypothesis that no legal parameter value satisfies would compile green
and prove nothing, so the strict form is exhibited at the **banked** tier
`w_S = 340`, `b_T = 512` -- the same pair `ScaleAlignOpening`'s
`referenceProfileGates_legal_instance` and `wrapperReference_fires_at_banked_tier`
already use, so no second parameter regime is introduced and no numeral is
invented here.  At that tier `q = 2^340` and
`x_T = xTdepth 512 = 2^{-512}` (`06:238--242`, the defining shape of `b_T`), and
`t_ref = 2^k` at `k = 9`, which is legal for this block: `4 <= 9` is `A:117`'s
"divisible by `16`" in exponent form and `9 + 2 <= 340` is `q/4 >= t_ref`
(`09:327`).

Five clauses, all proved: the strict `A:112` pair `0 < x_T` and `x_T <= 1`, taken
from the banked `ScaleAlignOpening.xTdepth_mem` and not re-derived; the frozen
gate `q x_T <= 4/25025`, which holds with room since `q x_T = 2^{-172}`; the
whole of `eq:wrapper-low-rung-gates` at the tier; and the strict row-legality
transport `0 < t_ref x_T <= 1` of `N3`.

**Not degenerate, and not a satisfiability claim for the full bundle.**  The row
loss `q x_T = 2^{-172}` is strictly positive, so the ceiling comparisons behind
`eq:wrapper-reference-count` are genuine rather than met by a vanishing demand --
contrast `zero_xT_refutes_endpoint_conclusion`, which is what the excluded
`x_T = 0` would give.  What is **not** exhibited is any inhabitant of `hLocEx`,
`hbase`, `htcert`, `hE1`, `hE2` or `hcol`: those stay `06`'s and the endpoint's,
exactly as `wrapperLowExtension_fires_at_legal_tier` records.  The margin is
computed through the explicit split `2^512 = 2^340 . 2^172` and the bound
`2^13 <= 2^172` rather than by evaluating `2^512`, following the banked probe. -/
theorem strict_xT_membership_at_banked_tier :
    0 < DenseStageFourOpening.xTdepth 512
      ∧ DenseStageFourOpening.xTdepth 512 ≤ 1
      ∧ ((2 : ℝ) ^ (340 : ℕ)) * DenseStageFourOpening.xTdepth 512 ≤ 4 / 25025
      ∧ wrapperLowRungGates 340 (DenseStageFourOpening.xTdepth 512)
      ∧ 0 < ((2 : ℝ) ^ (9 : ℕ)) * DenseStageFourOpening.xTdepth 512
      ∧ ((2 : ℝ) ^ (9 : ℕ)) * DenseStageFourOpening.xTdepth 512 ≤ 1 := by
  obtain ⟨hpos, hle1⟩ := xTdepth_mem 512
  have hx : DenseStageFourOpening.xTdepth 512 = 1 / (2 : ℝ) ^ (512 : ℕ) := rfl
  have h172 : (0 : ℝ) < 2 ^ (172 : ℕ) := by positivity
  have hsplit : (2 : ℝ) ^ (512 : ℕ) = 2 ^ (340 : ℕ) * 2 ^ (172 : ℕ) := by
    rw [← pow_add]
  have hval : ((2 : ℝ) ^ (340 : ℕ)) * DenseStageFourOpening.xTdepth 512
      = 1 / 2 ^ (172 : ℕ) := by
    rw [hx, hsplit]
    field_simp
  have hbig : (8192 : ℝ) ≤ 2 ^ (172 : ℕ) :=
    calc (8192 : ℝ) = (2 : ℝ) ^ (13 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (172 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hgate : ((2 : ℝ) ^ (340 : ℕ)) * DenseStageFourOpening.xTdepth 512
      ≤ 4 / 25025 :=
    calc ((2 : ℝ) ^ (340 : ℕ)) * DenseStageFourOpening.xTdepth 512
        = 1 / 2 ^ (172 : ℕ) := hval
      _ ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hbig
      _ ≤ 4 / 25025 := by norm_num
  have hrow := simple_gate_forces_strict_tRef_row_legality
    (r := 340) (k := 9) (xT := DenseStageFourOpening.xTdepth 512)
    (by omega) hpos hgate
  exact ⟨hpos, hle1, hgate,
    wrapperLowRungGates_of_simple_gate (by omega) (le_of_lt hpos) hgate,
    hrow.1, hrow.2⟩

/-- **Battery N5 (statement pole: the `r0` defect preserved as a kernel-visible
countermodel).**

Why `0 <= x` was not a harmless relaxation, kept in the module rather than only
in prose.  At `x = 0` the frozen per-block row demand of `A:139--141`,
`ceil(r' t x m)`, is **zero** for every choice of `r'`, `t` and `m`; a
restriction is then required to have *at least zero* rows in each represented
block, which no data can violate.  A Boolean matrix of communication complexity
exactly `0` exists -- the constant matrix, through the banked
`PublicRecords.D_const` -- and `0` misses the endpoint's conclusion
`H + log_2(r' t)` of `A:142--144`, because `H = C - 1 >= 2` at the frozen
`C >= 3` (`09:240`) and `log_2(r' t) >= 0`.

So the `r0` `hLocEx`, whose third antecedent admitted `x = 0`, asserted at that
point a statement `thm:certified-localized-extension` does not make and which the
constant matrix refutes.  Three clauses, all computed: the vanishing row demand,
the existence of the zero-cost object, and the failure of the conclusion at it.

**Why the trivial reading fails.**  The third clause is a *negation*, so it
cannot be met by weakening: `C - 1 + (r - j)` is a natural number and the claim
is that it is not `<= 0`, which needs `C >= 3` and would be false at `C <= 1`.
The frozen side condition is therefore load-bearing, and the pole is a statement
about the excluded boundary point and not about the frozen regime, where
`strict_xT_membership_at_banked_tier` exhibits the strict membership instead.
General in `C`, `r`, `j` and in the endpoint's `r'`, `t`, `m`. -/
theorem zero_xT_refutes_endpoint_conclusion (C r j rp t m : ℕ) (hC : 3 ≤ C) :
    Nat.ceil ((rp : ℝ) * (t : ℝ) * (0 : ℝ) * (m : ℝ)) = 0
      ∧ D (fun (_ : Bool) (_ : Bool) => false) = 0
      ∧ ¬ ((C - 1) + (r - j) ≤ D (fun (_ : Bool) (_ : Bool) => false)) := by
  refine ⟨by simp, PublicRecords.D_const false, ?_⟩
  rw [PublicRecords.D_const false]
  omega

/-! ## §9  `eq:raw-low-rung-gates` (`06:889--907`), the raw twin of §5

The frozen block, read at the bytes:

* `06:889--890`: "The exact low-rung row losses are also checked here.  For
  `x_j = (s/2^j) x_T`, `j = 0,1,2`, require";
* `eq:raw-low-rung-gates` (display `06:891--901`, label `06:900`):
  `x_j <= gamma_j/(1 - 9/(16 . 2^j))`, at the three printed rationals
  `gamma_0 = 27787089/830471792`, `gamma_1 = 19398081/1660943584`,
  `gamma_2 = 2620065/3321887168` (`06:896--898`);
* `06:902--907`: "These rational margins imply
  `(beta_j^raw - x_j)/(1 - x_j) >= 9/(16 . 2^j)`, which is precisely the row
  density needed for the three raw lower rungs in `sec:dense-stage4`."

**Why this display is stated here.**  It is the *raw* twin of the display §5
already owns: `06:889--934` prints the two low-rung gate blocks in one
paragraph, the raw one at `06:891--901` and the wrapped one at `06:927--934`,
and closes at `06:935--936` with "the raw and wrapped row calculations use exact
ceilings".  §5 owns the wrapped one; this section owns the raw one, and the two
are tied by `rawLowRungGates_of_wrapperGate`, which derives the raw gates from
the *frozen sufficient condition of the wrapped display* once `s <= q`
(`06:917`).  Everything the raw display speaks about is consumed by pin and
restated nowhere: `x_j` is the banked `DenseStageFourOpening.rowDensity`
(`08:172`, `x_j = I_j x_T`, itself `widthI * xTdepth`), the block target and the
residual column density are `blockTarget` and `rTail`, and the rung clause the
margin feeds is the banked `RawLowProfileBody.rawLow_gate_of_margin`.

**What was fresh, and what is now owned.**  Before this section, this display
had no Lean carrier anywhere: no predicate stated the comparison and the six
`gamma_j` numerals occurred in no declaration statement or proof term across
`src/`.  It was the single GENUINELY-FRESH display of the item-(v) roster range
`06:1219--1220`, registered exact under `S5-CUTOFF-ITEMS-DEFERRED` (b3) and
never authored.  `gammaRawLow` and `rawLowRungGates` are that display and
nothing more; the item-(v) partition is re-derived over the classifier at these
bytes in `EffectiveCutoffCertificate` Part 7, and **item (v)'s aggregate is
still not formed** -- ownership of every display of the range is necessary for
it and is not sufficient, since the aggregate would have to be written as pins
over one shared context.

**Nothing here is asserted.**  `rawLowRungGates` is a predicate; the only
unconditional instance is the NON-FIDELITY `rawLowRungGates_at_banked_tier`, at
the tier `ScaleAlignOpening` and `RawLowProfileBody` already bank (`w_S = 340`,
`b_T = 512`, the `b_T` *forced* from `s` by
`RawLowProfileBody.witness_bT_checked`), and it is obtained from the banked
`strict_xT_membership_at_banked_tier` rather than from a fresh numeral.

**The `r1` margin close, and what it does not settle.**  The `r0` form of this
section carried the frozen consequence `06:902--906` under an undischarged
binder `hbeta : gamma_j + 9/(16 . 2^j) <= beta`, and no record of this module
may say that sentence was closed before this round: it was not.  The repair
derives that bound rather than assuming it, through the schedule's own chain --
`lambda_T >= 99/100` (`06:174`) forces `(|W_V| + |W_B|)/|T| <= beta_T`
(`06:159`), the ceiling of `08:176--181` gives
`beta_j^raw >= r_j(1 + rho) - rho`, and `r_j <= 1` (`08:175`, `rTail_le_one`)
makes that antitone in `rho`.  At `rho = beta_T` the value `r_j(1 + beta_T) -
beta_T` equals `gamma_j + 9/(16 . 2^j)` **exactly** at all three rungs; that
identity is `EffectiveCutoffCertificate.rawLowRungRatio_at_betaT`, and it is
what the three printed `gamma_j` of `06:896--898` are.  What this does *not*
settle: item (v) is an **aggregate**, and no theorem of this module or of the
classifier states it.  Display-level ownership -- including this display's --
is necessary and not sufficient, and the roster's `NONE-YET` status for the
item has no kernel-checked counterweight; reading
`EffectiveCutoffCertificate.itemVEveryDisplayIsOwned` as "item (v) is done"
is exactly the inference the ledger row forbids. -/

/-- **The three frozen rational margins of `eq:raw-low-rung-gates`
(`06:896--898`).**

Transcribed exactly as printed: the paper *defines* `gamma_0`, `gamma_1`,
`gamma_2` by these three literals inside the display itself, so the numerals are
the display's own closed form and not values chosen or derived here.

The paper defines the symbol at `j = 0, 1, 2` only (`06:890`, "`j = 0,1,2`"),
and `rawLowRungGates` quantifies over exactly that range; the `0` returned
outside it is an inert default and **asserts nothing** -- in particular it is
not a claim that any fourth margin vanishes.  `gammaRawLow_frozen_values`
records the three values, their positivity, and that they are strictly
decreasing in `j`. -/
noncomputable def gammaRawLow (j : ℕ) : ℝ :=
  if j = 0 then 27787089 / 830471792
  else if j = 1 then 19398081 / 1660943584
  else if j = 2 then 2620065 / 3321887168
  else 0

/-- **`eq:raw-low-rung-gates` (`06:891--901`), transcribed.**

`x_j <= gamma_j/(1 - 9/(16 . 2^j))` for `j = 0, 1, 2`, with `x_j` the banked
`DenseStageFourOpening.rowDensity s j bT` -- i.e. `(s/2^j) x_T` at
`x_T = 2^{-b_T}`, which is exactly the `x_j` the frozen sentence `06:889--890`
fixes for this display.  The comparison is stated in `ℝ`, so the frozen
rationals are exact and no natural division truncates them.

Stated as a predicate and **never asserted**.  The paper's own instance of it
is the condition list the schedule compiler `Compile(c)` emits, which has no
Lean declaration on this route and stays ledger-deferred;
`rawLowRungGates_at_banked_tier` is a **NON-FIDELITY** smoke inhabitant at the
route's banked witness tier and is not that instance. -/
def rawLowRungGates (s bT : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ 2 →
    DenseStageFourOpening.rowDensity s j bT ≤ gammaRawLow j / (1 - 9 / (16 * 2 ^ j))

/-- **Battery R1 (the frozen readouts).**  The three printed values of
`06:896--898`, together with two general facts about the reified symbol: each is
strictly positive, and they are strictly decreasing in `j` -- which is the shape
the display needs, since the admissible density `x_j = (s/2^j) x_T` also
halves with `j` while the target `9/(16 . 2^j)` halves with it. -/
theorem gammaRawLow_frozen_values :
    gammaRawLow 0 = 27787089 / 830471792
      ∧ gammaRawLow 1 = 19398081 / 1660943584
      ∧ gammaRawLow 2 = 2620065 / 3321887168
      ∧ 0 < gammaRawLow 2 ∧ gammaRawLow 2 < gammaRawLow 1
      ∧ gammaRawLow 1 < gammaRawLow 0 ∧ gammaRawLow 0 < 1 := by
  refine ⟨by norm_num [gammaRawLow], by norm_num [gammaRawLow],
    by norm_num [gammaRawLow], ?_, ?_, ?_, ?_⟩ <;> norm_num [gammaRawLow]

/-- **Battery R2 (the displayed bound is a legal density bound).**

For every rung of the frozen range the denominator `1 - 9/(16 . 2^j)` is
strictly positive -- so the right-hand side of the display is well formed --
the bound itself is strictly positive, and it is strictly below `1`.  The last
clause is what makes the display a *row-loss* gate rather than a vacuous
comparison: any `x_j` satisfying it is a legal density, `x_j < 1`.

The three bounds are `27787089/363331409`, `19398081/1193803201` and
`524013/570949357`, so the binding rung is `j = 2`, exactly as it is for the
wrapped twin (`wrapperLowRung_gate_is_tight`). -/
theorem rawLowRungBound_pos {j : ℕ} (hj : j ≤ 2) :
    0 < 1 - 9 / (16 * (2 : ℝ) ^ j)
      ∧ 0 < gammaRawLow j / (1 - 9 / (16 * (2 : ℝ) ^ j))
      ∧ gammaRawLow j / (1 - 9 / (16 * (2 : ℝ) ^ j)) < 1 := by
  interval_cases j <;> norm_num [gammaRawLow]

/-- **Battery R3 (the gate supplies its own side condition).**

Every consumer of the raw rung arithmetic needs `x_j < 1` (`06:271--273`
through `RawLowProfileBody.rowDensity_lt_one`).  The display already gives it:
its right-hand side is below `1` at every rung, so a gate-satisfying `x_j` is
automatically a legal density and the side condition never has to be assumed
twice.  General in `s`, `b_T` and `j`. -/
theorem rawLowRungGates_rowDensity_lt_one {s bT : ℕ} (h : rawLowRungGates s bT)
    {j : ℕ} (hj : j ≤ 2) : DenseStageFourOpening.rowDensity s j bT < 1 :=
  lt_of_le_of_lt (h j hj) (rawLowRungBound_pos hj).2.2

/-- **Battery R4 (the frozen simple gate is sufficient for the raw display).**

From `s <= q` (`06:917`) and `q x_T <= 4/25025` (`06:918`, the frozen
sufficient condition printed again as the second clause of
`eq:wrapper-low-rung-gates` at `06:932`) the whole of `eq:raw-low-rung-gates`
follows: `x_j = (s/2^j)x_T <= s x_T <= q x_T <= 4/25025`, and `4/25025` is below
all three displayed bounds -- the smallest being `524013/570949357` at `j = 2`,
which is larger than `4/25025` by a factor of about `5.7`.

This is the raw analogue of the argument `06:916--920` prints for the
first-wrapper comparisons; it is **proved here**, not transcribed, and the
paper is not cited as having stated it.  General in `s`, `r` and `b_T`. -/
theorem rawLowRungGates_of_simple_gate {s r bT : ℕ} (hs : s ≤ 2 ^ r)
    (hgate : ((2 : ℝ) ^ r) * DenseStageFourOpening.xTdepth bT ≤ 4 / 25025) :
    rawLowRungGates s bT := by
  intro j hj
  have hxT0 : (0 : ℝ) ≤ DenseStageFourOpening.xTdepth bT := by
    simp only [DenseStageFourOpening.xTdepth]
    positivity
  have hsr : (s : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast hs
  have hw : DenseStageFourOpening.widthI s j ≤ (s : ℝ) := by
    simp only [DenseStageFourOpening.widthI]
    exact div_le_self (Nat.cast_nonneg s) (one_le_pow₀ (by norm_num))
  have hstep : DenseStageFourOpening.rowDensity s j bT ≤ 4 / 25025 := by
    simp only [DenseStageFourOpening.rowDensity]
    calc DenseStageFourOpening.widthI s j * DenseStageFourOpening.xTdepth bT
        ≤ (s : ℝ) * DenseStageFourOpening.xTdepth bT :=
          mul_le_mul_of_nonneg_right hw hxT0
      _ ≤ (2 : ℝ) ^ r * DenseStageFourOpening.xTdepth bT :=
          mul_le_mul_of_nonneg_right hsr hxT0
      _ ≤ 4 / 25025 := hgate
  refine le_trans hstep ?_
  interval_cases j <;> norm_num [gammaRawLow]

/-- **Battery R5 (the two low-rung displays, tied at the pin).**

`06:889--936` prints the raw and the wrapped low-rung gates in one paragraph,
and the second clause of the wrapped display *is* the sufficient condition the
raw one needs.  So the banked `wrapperLowRungGates` of §5, plus `s <= q`
(`06:917`), gives `eq:raw-low-rung-gates` outright -- the wrapped predicate is
consumed by pin and nothing of it is restated here. -/
theorem rawLowRungGates_of_wrapperGate {s r bT : ℕ} (hs : s ≤ 2 ^ r)
    (hg : wrapperLowRungGates r (DenseStageFourOpening.xTdepth bT)) :
    rawLowRungGates s bT :=
  rawLowRungGates_of_simple_gate hs hg.2

/-- **Battery R6 (monotonicity: the gate survives a smaller width and a deeper
seed).**

`x_j = (s/2^j) 2^{-b_T}` is monotone in `s` and antitone in `b_T`, so a schedule
that clears the display at `(s, b_T)` clears it at every `s' <= s` and every
`b_T' >= b_T`.  This is the round-trip property the display must have to be a
row-*loss* condition: shrinking the Stage-3 width or deepening the auxiliary
seed can only reduce the loss.  General in all four parameters. -/
theorem rawLowRungGates_mono {s s' bT bT' : ℕ} (hss : s' ≤ s) (hbb : bT ≤ bT')
    (h : rawLowRungGates s bT) : rawLowRungGates s' bT' := by
  intro j hj
  refine le_trans ?_ (h j hj)
  have hjpos : (0 : ℝ) < 2 ^ j := by positivity
  have hbpos : (0 : ℝ) < 2 ^ bT := by positivity
  have hb'pos : (0 : ℝ) < 2 ^ bT' := by positivity
  have hs' : (s' : ℝ) ≤ (s : ℝ) := by exact_mod_cast hss
  have hpow : ((2 : ℝ)) ^ bT ≤ (2 : ℝ) ^ bT' := pow_le_pow_right₀ (by norm_num) hbb
  simp only [DenseStageFourOpening.rowDensity, DenseStageFourOpening.widthI,
    DenseStageFourOpening.xTdepth]
  have hA : (s' : ℝ) / 2 ^ j ≤ (s : ℝ) / 2 ^ j := by
    rw [div_le_div_iff₀ hjpos hjpos]
    nlinarith
  have hB : (1 : ℝ) / 2 ^ bT' ≤ 1 / 2 ^ bT := by
    rw [div_le_div_iff₀ hb'pos hbpos]
    nlinarith
  exact mul_le_mul hA hB (by positivity) (by positivity)

/-- **Battery R7a (the residual column density never exceeds one).**

`r_j = (y/2^j - sigma)/(1 - sigma)` (`08:175`) with `sigma = 2^{-20}`
(`06:134`, in the display labelled `eq:fixed-protected-masses` at `06:138`).
For any column mass `y <= 1` and any
rung index, `r_j <= 1`: the numerator is at most `1 - sigma` and the
denominator is exactly `1 - sigma`.

This is the monotonicity input of the frozen chain behind `06:902--906` --
`beta_j^raw >= r_j(1 + rho) - rho` is *antitone* in the reservoir ratio `rho`
precisely because `r_j - 1 <= 0` -- and it is stated in general, for an
arbitrary `y <= 1` and an arbitrary rung, rather than only at the schedule's
`y = 3/5`.  `sigmaR` and `rTail` are consumed by pin; no mass numeral is
written here. -/
theorem rTail_le_one {y : ℝ} (hy : y ≤ 1) (j : ℕ) :
    DenseStageFourOpening.rTail y j ≤ 1 := by
  have hsig : (0 : ℝ) < 1 - DenseStageFourOpening.sigmaR := by
    simp only [DenseStageFourOpening.sigmaR]; norm_num
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hy2 : y / 2 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  rw [DenseStageFourOpening.rTail, div_le_one hsig]
  linarith

/-- **Battery R7b (the reservoir ratio bounds the raw density from below).**

The frozen `beta_j^raw` of `08:176--181` is
`(ceil(r_j(|T| + |W_V| + |W_B|)) - |W_V| - |W_B|)/|T|`.  Writing
`rho = (|W_V| + |W_B|)/|T|` for the reservoir-to-template ratio, discarding the
ceiling downwards through the banked `RawLowProfileBody.betaRaw_lower` gives
`beta_j^raw >= r_j(1 + rho') - rho'` for the *exact* ratio `rho'`, and the map
`rho |-> r_j(1 + rho) - rho = r_j + rho(r_j - 1)` is non-increasing in `rho`
because `r_j <= 1` (`rTail_le_one`).  Hence any upper bound `rho` on the true
ratio -- supplied here in the cleared form `|W_V| + |W_B| <= rho . |T|`, which
needs no division -- propagates to a lower bound on `beta_j^raw`.

This is the whole content of the step the schedule sentence `06:902--906`
leaves implicit, and it is proved, not assumed.  General in the rung ratio `r`,
the bound `rho` and the three cardinalities; `betaRaw` and `betaRaw_lower` are
consumed by pin and neither is restated. -/
theorem betaRaw_ge_of_reservoir_ratio {T₀ V₀ B₀ : ℕ} {r ρ : ℝ} (hT : 0 < T₀)
    (hr1 : r ≤ 1) (hres : (V₀ : ℝ) + (B₀ : ℝ) ≤ ρ * (T₀ : ℝ)) :
    r * (1 + ρ) - ρ ≤ DenseStageFourOpening.betaRaw r T₀ V₀ B₀ := by
  have hT' : (0 : ℝ) < (T₀ : ℝ) := by exact_mod_cast hT
  refine le_trans ?_ (RawLowProfileBody.betaRaw_lower hT)
  rw [le_div_iff₀ hT']
  nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hres)]

/-- **Battery R7 (`06:902--906`: the rational margins do imply the row
density), with no premise about `beta_j^raw`.**

The frozen sentence after the display is "These rational margins imply
`(beta_j^raw - x_j)/(1 - x_j) >= 9/(16 . 2^j)`".  The paper presents that lower
bound as a consequence the schedule already supplies, so this theorem takes no
hypothesis about `beta_j^raw` at all: the conclusion is stated about the frozen
`beta_j^raw` itself, at the paper's own residual density
`r_j = rTail (3/5) j`, and the bound on it is *derived* through
`betaRaw_ge_of_reservoir_ratio` from the schedule's reservoir data.

The two remaining hypotheses are schedule *inputs*, not statements about the
construction's output:

* `hres`, the reservoir bound `|W_V| + |W_B| <= rho . |T|`;
* `hrho`, that the rung's margin fits under `r_j(1 + rho) - rho` at that ratio.

Both are discharged in this tranche at the frozen template ratio
`rho = beta_T` (`06:159`) by
`EffectiveCutoffCertificate.rawLowRungRatio_at_betaT`, where `hrho` holds with
**equality** at all three rungs -- that identity is what the three printed
`gamma_j` are.  The discharge cannot be written in this module: `beta_T` is
banked as `ScheduleTemplateResidue.betaT` and must be consumed by pin, but
`ScheduleTemplateResidue` reaches this module through its own import chain
(`ScheduleTemplateResidue -> ParameterSchedule -> WrapperProtectedEarly -> ... ->
WrapperProjectionCovers -> WrapperLowRungs`), so importing it here is a cycle
and re-minting the constant would be a fixed-interface violation.  The closed
theorems therefore live downstream, in `EffectiveCutoffCertificate`, and this
one carries the general arithmetic.

The density computation is the display's own: from
`x_j <= gamma_j/(1 - 9/(16 . 2^j))` and `1 - 9/(16 . 2^j) > 0` we get
`x_j(1 - 9/(16 . 2^j)) <= gamma_j`, and with
`gamma_j + 9/(16 . 2^j) <= beta_j^raw` this clears the positive denominator
`1 - x_j` -- positive by `rawLowRungGates_rowDensity_lt_one`, so that side
condition is supplied by the gate and not assumed.  General in `s`, `b_T`, `j`,
`rho` and the three cardinalities. -/
theorem rawLowRung_margin_of_gates {s bT T₀ V₀ B₀ j : ℕ} {ρ : ℝ} (hj : j ≤ 2)
    (h : rawLowRungGates s bT) (hT : 0 < T₀)
    (hres : (V₀ : ℝ) + (B₀ : ℝ) ≤ ρ * (T₀ : ℝ))
    (hrho : gammaRawLow j + 9 / (16 * 2 ^ j)
      ≤ DenseStageFourOpening.rTail (3 / 5) j * (1 + ρ) - ρ) :
    9 / (16 * 2 ^ j)
      ≤ (DenseStageFourOpening.betaRaw (DenseStageFourOpening.rTail (3 / 5) j) T₀ V₀ B₀
            - DenseStageFourOpening.rowDensity s j bT)
          / (1 - DenseStageFourOpening.rowDensity s j bT) := by
  have hden := (rawLowRungBound_pos hj).1
  have hx1 : DenseStageFourOpening.rowDensity s j bT < 1 :=
    rawLowRungGates_rowDensity_lt_one h hj
  have hpos : (0 : ℝ) < 1 - DenseStageFourOpening.rowDensity s j bT := by linarith
  have hclear : DenseStageFourOpening.rowDensity s j bT * (1 - 9 / (16 * 2 ^ j))
      ≤ gammaRawLow j := (le_div_iff₀ hden).mp (h j hj)
  have hbeta : gammaRawLow j + 9 / (16 * 2 ^ j)
      ≤ DenseStageFourOpening.betaRaw (DenseStageFourOpening.rTail (3 / 5) j) T₀ V₀ B₀ :=
    le_trans hrho
      (betaRaw_ge_of_reservoir_ratio hT (rTail_le_one (by norm_num) j) hres)
  rw [le_div_iff₀ hpos]
  nlinarith

/-- **Battery R8 (the display feeds the rung clause of `eq:raw-low-gates`).**

`06:907` says the margin is "precisely the row density needed for the three raw
lower rungs in `sec:dense-stage4`", and the banked
`RawLowProfileBody.rawLow_gate_of_margin` is the step from that margin to the
ceiling comparison of `eq:raw-low-gates` (`08:184--191`).  Composing it with
the repaired `rawLowRung_margin_of_gates` closes the frozen chain
`eq:raw-low-rung-gates -> margin -> rung clause` at the bytes, with that banked
result consumed by pin and not restated.

**No premise about `beta_j^raw` survives**, and the column mass is no longer a
free binder: it is the paper's own `y = 3/5`, instantiated at the frozen
application anchors `05:541--542`, `06:1110` and `09:1137`.  What is left is the
schedule input pair of `rawLowRung_margin_of_gates`, discharged at the frozen
template ratio in `EffectiveCutoffCertificate`.  General in `s`, `b_T`, `j`,
`rho` and the three cardinalities. -/
theorem rawLowRungGates_supply_rawLowRungClause {s bT T₀ V₀ B₀ j : ℕ} {ρ : ℝ}
    (hj : j ≤ 2) (h : rawLowRungGates s bT) (hT : 0 < T₀)
    (hres : (V₀ : ℝ) + (B₀ : ℝ) ≤ ρ * (T₀ : ℝ))
    (hrho : gammaRawLow j + 9 / (16 * 2 ^ j)
      ≤ DenseStageFourOpening.rTail (3 / 5) j * (1 + ρ) - ρ) :
    DenseStageFourOpening.blockTarget s j
      ≤ (⌈(s : ℝ)
            * (DenseStageFourOpening.betaRaw
                  (DenseStageFourOpening.rTail (3 / 5) j) T₀ V₀ B₀
              - DenseStageFourOpening.rowDensity s j bT)
          / (1 - DenseStageFourOpening.rowDensity s j bT)⌉₊ : ℝ) :=
  RawLowProfileBody.rawLow_gate_of_margin
    (rawLowRung_margin_of_gates hj h hT hres hrho)

/-- **Battery R9 (the margins sit below the frozen residual density).**

`gamma_j + 9/(16 . 2^j)` is below `r_j = (y/2^j - sigma)/(1 - sigma)`
(`08:175`) and the frozen `sigma = 2^{-20}` (`08:135`), for each of the three
rungs: `0.595960 < 0.600000`, `0.292929 < 0.299999`, `0.141414 < 0.149999`.

**Provenance of `y = 3/5`.**  `08:175` and `08:213` leave `y` symbolic, so
neither anchors the value.  The frozen text instantiates it at its application
sites -- `05:541--542` (`... x=2^{-b_1},\quad y=3/5,\quad t=t_2, ...`),
`06:1110` (`x=2^{-b_1},\qquad y=3/5`) and `09:1137` (`x=x_T`, and `z=y=3/5`) --
and those three autoformalization anchors are the provenance.  The reader
release is *not* the source of this value and is not cited for it.

Two things follow, and only these two.  The strict gap `r_j - (gamma_j + t_j)`
is exactly what the reservoir loss of `08:176--181` is allowed to consume:
`R7`'s derived bound on `beta_j^raw` is not a demand no schedule could meet,
since `beta_j^raw` starts from `r_j` before any reservoir is subtracted.  And
the three printed `gamma_j` are visibly the margins the frozen text calls them:
each leaves the whole gap between the rung target `9/(16 . 2^j)` and the
residual density.

It does **not** follow, and is not claimed, that `beta_j^raw` itself clears the
bound: `beta_j^raw` is `r_j` after the protected reservoirs are subtracted
(`08:176--181`), and how much is lost depends on cardinalities this display
does not mention. -/
theorem gammaRawLow_below_rTail {j : ℕ} (hj : j ≤ 2) :
    gammaRawLow j + 9 / (16 * 2 ^ j) ≤ DenseStageFourOpening.rTail (3 / 5) j := by
  interval_cases j <;>
    norm_num [gammaRawLow, DenseStageFourOpening.rTail, DenseStageFourOpening.sigmaR]

/-- **Battery R10 (NON-VACUITY, tier 2): the display holds at the banked
tier.**

`rawLowRungGates (2^340) 512`: the Stage-3 width `s = 2^340` and the auxiliary
depth `b_T = 512` of the route's banked witness tier, where `b_T` is not chosen
but **forced** from `s` by `RawLowProfileBody.witness_bT_checked`
(`b_T = 2^{j_49(log_2(s/4))} = 2^{j_49(338)} = 2^9`), and where
`RawLowProfileBody.rawLowGates_inhabited` already exhibits the Section-8 raw-low
gates at the same `(s, b_T)`.  A gate predicate no legal parameter value
satisfies would compile green and prove nothing; this one is satisfied at the
tier the route already banks.

Obtained from the banked `strict_xT_membership_at_banked_tier` -- whose third
clause is `q x_T <= 4/25025` at `q = 2^340`, `x_T = xTdepth 512` -- through
`R4` at `s = q = 2^340` (`06:917` prints `s <= q`, so equality is admissible).
No numeral is introduced here that the route had not already banked, and the
margin is not tight: `x_0 = 2^{-172}`, far below the displayed bound
`27787089/363331409`.

**NON-FIDELITY -- not canonical inhabitation.**  The paper's own instance of
this display is the condition list the schedule compiler `Compile(c)` emits
(`thm:eff-ledger`, `sec:effective-cutoff`), which has no Lean declaration on
this route.  This theorem is the interim synthetic probe required to be
labelled **NON-FIDELITY** by the canonical-inhabitation rule: it shows our
predicate is satisfiable at legal parameter values and nothing more.  The
canonical-inhabitation obligation stays registered and deferred, exactly as for
the other roster displays, and is discharged when the compiler lands -- never
by this witness. -/
theorem rawLowRungGates_at_banked_tier : rawLowRungGates (2 ^ 340) 512 :=
  rawLowRungGates_of_simple_gate (r := 340) le_rfl
    strict_xT_membership_at_banked_tier.2.2.1

/-- **Battery R11 (statement pole / rejection probe: the display is not
automatic).**

At `s = 2^{b_T}` the rung-`0` density is `x_0 = 2^{b_T} . 2^{-b_T} = 1`, which
**fails** the displayed bound `27787089/363331409 < 1`, so `rawLowRungGates` is
refuted there for every `b_T`.  The predicate is therefore doing real work: it
is not satisfied by every pair `(s, b_T)`, and a proof of it cannot come from
the shape of `rowDensity` alone.

`s = 2^{b_T}` **claims no legality** -- it is exactly the excluded boundary of
`06:271--273`, which requires `I_j < 2^{b_T}` and hence `s < 2^{b_T}` at
`j = 0`.  The probe exists to exhibit the guard firing on input the schedule
forbids, and must never be read as a parameter regime of the route.  General in
`b_T`. -/
theorem rawLowRungGates_refuted_at_full_width (bT : ℕ) :
    ¬ rawLowRungGates (2 ^ bT) bT := by
  intro h
  have h0 := h 0 (by norm_num)
  have hx : DenseStageFourOpening.rowDensity (2 ^ bT) 0 bT = 1 := by
    have h2 : ((2 : ℝ) ^ bT) ≠ 0 := by positivity
    simp only [DenseStageFourOpening.rowDensity, DenseStageFourOpening.widthI,
      DenseStageFourOpening.xTdepth, pow_zero, div_one, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [hx] at h0
  norm_num [gammaRawLow] at h0

end EthInapproximability.ParameterizedNP.WrapperLowRungs
