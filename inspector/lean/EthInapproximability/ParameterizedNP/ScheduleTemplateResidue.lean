import EthInapproximability.ParameterizedNP.ParameterSchedule
import EthInapproximability.ParameterizedNP.ScaleAlignOpening
import EthInapproximability.ParameterizedNP.GuardedSourceSlab
import EthInapproximability.ParameterizedNP.MassRedistributionTail

/-!
# Parameterized NP route: the ten open template/growth displays of Section 6

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/06-parameter-schedule.tex`, `sec:parameters`.

  This module is a **residue tranche**: it lands the ten Section-6 displays
  that the banked `SCHEDULE-001` row (`ParameterSchedule.lean`) explicitly left
  open, each stated as *its own equation* at its exact frozen anchor, with every
  quantity routed through a banked accessor or through a reification of its own
  defining display.  The ten anchors, in frozen print order, are:

  1. `eq:lambda-template-exact` (label `06:155`, display `06:150--156`), the
     exact template density
     `lambda_T = (1 - 2^{-20}) T_raw/(T_raw + S_raw) + 2^{-21}`, together with
     `06:145--148` (`X_0 = T_raw + S_raw`, `S_raw = V_raw + B_raw`);
  2. `eq:template-source-ratio` (label `06:166`, display `06:162--167`),
     `(1 + eps_2) N_src <= beta_T s q_1^{t_2} |Rows(R)|^{t_2 - 1}`, with the
     constant `beta_T = (1/100 - 2^{-21})/(99/100 - 2^{-21})` of `06:157--160`
     and the three simpler comparisons of `06:177--201` that discharge it;
  3. `eq:lambda-template-window` (label `06:175`, display `06:173--176`),
     `99/100 <= lambda_T <= 1 - 2^{-21}`, with the derivation `06:168--172`
     ("Balancedness gives ... Therefore `eq:template-source-ratio` implies");
  4. `eq:source-template-count-cancellation` (label `06:194`, display
     `06:188--195`), `N_src = 4s(N_V + s - 3) <= 4s(2 N_E + N_E) = 12 s N_E
     <= q_2`, with the two premises `06:183--187`
     (`AUX.PRE.SOURCE.S_MINUS3_LE_NE` and the public no-isolates inequality
     `N_V <= 2 N_E`);
  5. `eq:hard-seed-width-gates` (label `06:268`, display `06:264--269`), all
     **three** rows `k_T = log_2(s/4) >= m_HS`, `16 | (s/4)` and
     `log_2 s < b_T`, together with the auxiliary Stage-3 depth `06:237--244`
     (`k_T`, `b_T = 2^{j_49(k_T)}`, `x_T = 2^{-b_T}`) and the consequence
     `06:271--273` ("each `I_j = s/2^j`, `j = 0,1,2` ... satisfies
     `I_j < 2^{b_T}`");
  6. `eq:b2-choice` (label `06:426`, display `06:423--427`),
     `b_2 = ceil(log_2(32 s q_1 m_R)) + c_b` and `h_2 = 2^{-b_2}`, with
     `06:422` (`m_R = |Rows(R)|`) and the configuration floor `c_b >= 6` of
     `06:62`;
  7. `eq:P0-growth` (label `06:498`, display `06:494--499`),
     `P_0 <= (C_0 + 3) A_*` and `L_P <= log_2 A_* + bl(C_0 + 3)`, with the whole
     recorded chain `06:473--497` ("The certificate does not treat the relation
     between `L_P` and `A_*` as a primitive coefficient leaf.  It records the
     following chain.");
  8. `eq:LP-PA-literal-dominance` (label `06:507`, display `06:502--508`), the
     "deliberately weaker integer consequence"
     `P_0 <= 2^{(3 + bl(C_0 + 5)) A_*}` and `L_P <= (3 + bl(C_0 + 5)) A_*`;
  9. `eq:tref-growth` (label `06:583`, display `06:580--584`),
     `log_2 t_ref = O(L_P^2)`, landed in the only exact form the frozen text
     supplies for it -- the explicit-constant bound at the tested endpoint
     `k_ref^* = 100 L_P^2` of `eq:kref-tested-endpoint` (`06:588`);
  10. `eq:cover-instance-tested-endpoints` (label `06:692`, display
      `06:682--693`), all **three** literal instances
      `B_ref^* = 25 bl(den theta)`, `B_sing^* = den(1 - eta_C) bl(den theta)`
      and `B_pair^* = 100 bl(den theta)`, with `bl(v) = clog_2(v + 1)` of
      `06:665`.

  Supporting defining displays reified here because a consumer would otherwise
  have to bind a source-defined quantity freely: `06:49` (`B_pub = max{D, Y}`),
  `06:51--54` (`z_R`), `06:296` (`U_0 = max{2, b_out/eta_R}`),
  `eq:Astar-choice` (label `06:304`, display `06:299--305`, `A_*` as the least
  power of two at least the displayed six-branch maximum -- the `ASTAR` row of
  the instance table `06:1271--1278`), the `a` row of `eq:stage1-scales`
  (label `06:320`, display `06:312--320`: `a = C_0 (log_2 A_*)^2`) with the
  `q_1` row (`q_1 = 2^a - 2`), `07:156` (`B_cap := D + a`) and `eq:Ccert`
  (label `06:433`, display `06:430--434`).

* **Modules consumed by pin, never restated.**
  * `ParameterSchedule.sScale`, `.sScale_eq_pow`, `.sScale_floor`
    (`SCHEDULE-001`) -- the `eq:s-choice` chain that `eq:hard-seed-width-gates`
    and `eq:b2-choice` read `s` from.  No numeral is assigned to `s` anywhere
    below except in the two labelled rejection probes.
  * `ParameterSchedule.j49` and its three eliminators (`SCHEDULE-001`) -- the
    integer primitive `b_T = 2^{j_49(k_T)}` of `06:241` is built from it and
    `j_49` is not redefined.
  * `ParameterSchedule.leastPowTwoExp`, `.leastPowTwoGe`, `.le_leastPowTwoGe`
    (`SCHEDULE-001`) -- the `ASTAR` row of `06:1271--1278` and the ceiling
    logarithm `ceil(log_2 U_0)` of `06:303` are this one accessor.
  * `ParameterSchedule.P0sched`, `.LPwidth`, `.cSeed` (`SCHEDULE-001`) --
    `eq:P0-growth` and `eq:LP-PA-literal-dominance` are stated *about* the
    banked `P_0` and `L_P`, never about a second copy of them.
  * `ParameterSchedule.kref`, `.krefStar`, `.jrefStar`, `.tref`,
    `.kref_le_star` (`SCHEDULE-001`) -- `eq:tref-growth` is a readout of the
    banked least search at the banked tested endpoint.
  * `ParameterSchedule.theta`, `.Bref_le_tested`, `.Bpair_le_tested`,
    `.cover_tested_endpoint` and `WrapperProjectionCovers.coverExponent`,
    `.coverExponent_le`, `.rhoSmall`, `.rhoPair`
    (`SCHEDULE-001`, `WRAPPER-PROJECTION-COVERS-001`) -- the three cover
    searches and the generic Bernoulli endpoint.
  * `ParameterSchedule.etaC`, `.one_sub_etaC_legal`, `.etaR` (`SCHEDULE-001`)
    -- the singleton cover base `1 - eta_C` and the tolerance feeding `U_0`.
  * `EntryGates.Qwidth` (`BRIDGE-ENTRY-001`) -- the bridge width `Q` at which
    `06:539` evaluates `den(theta) = 160 Q`.
  * `GuardedSourceSlab.SlabRow`, `.card_slabRow`, `.q2`, `.card_le_q2`
    (`SOURCE-SLAB-001`) -- the guarded source's own row count `4s(N + s - 3)`
    of `04:526` and the coordinate width `q_2`.  `eq:source-template-count-
    cancellation` is proved **on the paper's own object**, not on a copy.
  * `DenseStageFourOpening.sigmaMass` and `DenseSynchronisation.nuTempR`,
    `.protectedMasses_agree` (`STAGE4-PROTECTED-OPENING-001`, `DENSE-SYNC-001`)
    -- the fixed protected masses `sigma = 2^{-20}` and `nu_T = 2^{-21}` that
    the coefficients of `eq:lambda-template-exact` are.
  * `ScaleAlignOpening.lambdaTemplate` (`SCALE-ALIGN-001`) -- the Section-9
    template column density `|Y_T|/|Cols(G)|`.  `eq:lambda-template-exact` is
    the *value* the row multiplicities substitute into it, so the two are
    related here by a checked equation carried as an explicit hypothesis, never
    by a silent redefinition.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/`.  Each cited item was opened
and checked to state the same fact; **no reader item is claimed twice** here or
by any earlier row.

* `A-stage4-details.tex:86--91`, the display `eq:paper-guarded-size`,
  "`|I(G,s)| = 4s(N_G + s - 3)`, `|Q_real(G,s)| = 12 s m_G`" ->
  `source_template_count_cancellation` and its scheduled-scale instance.  (The
  neighbouring `A-stage4-details.tex:34--35`, `q_2 = min{2^r : 12 s m_G <= 2^r}`,
  is held by `SOURCE-SLAB-001` and is *not* re-claimed; the item taken here is
  the size display at 88--89, which no row claims.)
* `03-parameterized-construction.tex:68`, "Assume `log_2 s < b_T`." -> the
  third row of `hardSeedWidthGates`, its `kT`/`bT` reifications and
  `interlaceWidth_lt_two_pow_bT`.  (The reader's own display of `k_T`, `b_T`,
  `x_T` at `03:64--67` is held by `SCHEDULE-001` for `j49`; line 68 is the next
  sentence and is a different reader item, the only place the reader *states*
  a hard-seed width gate.)
* `03-parameterized-construction.tex:276--279`, the display `eq:paper-b2-choice`
  "`b_2 = ceil(log_2(32 s q_1 m_R)) + c_b`" together with its preceding sentence
  "Write `m_R = |Rows(R)|`.  The total schedule fixes an integer rounding margin
  `c_b >= 6` and defines" -> `b2`, `h2` and their aux battery.
  `StageTwoRelaxed.lean:151` records that `STAGE2-RELAXED-001` deliberately does
  **not** claim `eq:paper-b2-choice`, so the item is free.

**Reader items deliberately declined, with the reason recorded** (precedent:
`CLOCK-001`/`cc-t1x`, `SOURCE-SLAB-001`/`cc-t2b`, `SCHEDULE-001`/`cc-t3c`):

* `lambdaTexact`, `betaT`, `templateSourceRatio` and the window theorems claim
  **no** reader item.  The strings `lambda_T` and `beta_T` were searched for
  across all ten reader section files and appear in **none** of them; the
  reader's only template-density locus, `A-stage4-details.tex:197`
  ("the base, template, ..."), is a mass table already held by another row and
  states no density formula.  There is no reader sentence stating the same
  fact, so none is cited.
* `astarThreshold`, `astarExp`, `astar`, `q1Stage1`,
  `Ccert`, `Bpub`, `zRpub`, `U0sched` and the two growth theorems claim
  **no** reader item.  `A_*`, `P_0`, `L_P`, `C_0` and `c_seed` appear in no
  reader section file (the only `P_0` in the reader, at
  `B-bridge-details.tex:20--23`, is a block of a partition and a different
  object entirely); the reader compresses the whole finite gate list behind
  `thm:paper-effective-level` and prints none of these thresholds.  Citing that
  compiler theorem's summary would be citing prose as a statement.
* `tref_growth_at_tested_endpoint` claims **no** reader item: `t_ref`,
  `k_ref` and the certified reference width appear nowhere in the reader.
* `BrefStar`, `BsingStar`, `BpairStar` and the cover-endpoint theorems claim
  **no** reader item: `B_ref`, `B_sing`, `B_pair` and the projection-cover
  searches appear nowhere in the reader.

Crosswalk row: `READER_CROSSWALK.md`, "Simultaneous parameters and size".

## Status and dependencies

* Ledger row: **`SCHEDULE-TEMPLATE-RESIDUE-001`**, in
  `routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`.  The row
  banked with this tranche registers this module's 74 landed declarations and
  carries the deferred paper-instance canonical-inhabitation obligation for
  `lambdaTemplate` described below.  Nothing in this source comment registers
  any further obligation.
* Proof status: **new (elementary)** throughout.  Every declaration is either a
  plain transcription of a frozen defining display, a general property of one of
  those transcriptions, or one of the section's own displayed derivations
  (`06:168--176`, `06:177--201`, `06:188--195`, `06:271--273`, `06:473--508`,
  `06:610--629`, `06:671--693`) carried out in the kernel.  No communication-
  complexity lemma is introduced, adapted, or re-proved.
* Imports: `ParameterSchedule`, `ScaleAlignOpening`, `GuardedSourceSlab`, hence
  transitively `EthInapproximability.Prelude`, `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not**
  imported, so the AGHP balanced-family axiom is not in scope.
* External adapters: none.  Nothing here is axiomatized.  `EXPANDER-001` has no
  Lean declaration by design and is not touched; `C_0`, `c_b`, `B_s`, `Y`, `D`
  stay **explicit binders**, exactly as `06:56--69` requires ("The mathematical
  one-level theorem treats these integers as explicit input data").
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **No synthetic tuple.**  There is no `structure` here.  The two `Prop`
  abbreviations `hardSeedWidthGates` and `templateSourceRatio` are exactly the
  conjunction / inequality the paper displays, certified by their `_iff`
  lemmas, and each is shown **refutable** at an explicit point, so neither is a
  free bundle carrying a desired conclusion.
* **Ceilings and truncations are preserved.**  `b_2` keeps the frozen
  `ceil(log_2 .)` as `Nat.clog 2`; `s - 3` is taken in `ℕ` exactly as the
  banked `card_slabRow` computes it, and `t_2 - 1` likewise; `s/4` is the
  frozen natural quotient.
* **Both interlace widths are kept apart.**  Nothing here mentions the
  scale-alignment width `q` of `eq:q-deltaU`; the only width used is the bridge
  width `Q = EntryGates.Qwidth` of `eq:Q-theta-choice`, and only where `06:539`
  evaluates `den(theta) = 160 Q`.
* **Use-sites are never definitions.**  `beta_T` is read from its defining
  display `06:157--160`, not from the `beta_T s q_2 >= 1 + eps_2` comparison
  that consumes it at `06:181`; `B_cap` is read from its defining display
  `07:156` (`B_cap := D + a`), not from the passing use at `06:486`.
* **No conclusion in constructor data.**  No definition below mentions a
  complexity, robustness, or admissibility conclusion.

## Canonical inhabitation

Three of the ten displays are landed **on the paper's own object**, with no
synthetic stand-in:

* `eq:source-template-count-cancellation` is proved on the banked guarded
  source `GuardedSourceSlab.SlabRow` / `.q2` -- the very carrier `04:526`
  counts -- at the schedule's own scale `sScale` in
  `source_template_count_cancellation_at_scheduled_scale`;
* the divisibility row of `eq:hard-seed-width-gates` is proved at the schedule's
  own `s = 2^{ceil(B_s u^2)}` in `sScale_divisibility_row`, off `sScale_floor`;
* rows one and three of `eq:cover-instance-tested-endpoints` are proved at the
  schedule's own row threshold `theta(Q)` with `Q` the banked bridge width, in
  `cover_instance_tested_endpoints`.

Every other display carries a **pinned instance** in which each source-defined
input is supplied by its own defining chain rather than by a free binder or a
numeral:

* `eq:template-source-ratio` -> `templateSourceRatio_at_guarded_source`, with
  `N_src` and `q_2` the banked guarded source, `s` the `eq:s-choice` value,
  `q_1` the `eq:stage1-scales` value at the reified `a`, and `t_2` the banked
  Stage-2 least search; the count premise `N_src <= q_2` is *proved* there;
* `eq:hard-seed-width-gates` -> `hardSeedWidthGates_at_scheduled_scale`, at
  `s = sScale B_s u` and the banked exponent threshold
  `HardSeedFacade.mHS`;
* `eq:b2-choice` -> `b2_at_scheduled_point`, at `s = sScale` and
  `q_1 = 2^a - 2`;
* `eq:P0-growth` and `eq:LP-PA-literal-dominance` ->
  `P0_growth_at_scheduled_point`, where `B_pub`, `z_R`, `s`, `log_2 q_2`
  (through the banked `GuardedSourceSlab.q2`), `ceil(log_2 U_0)`, `A_*`, `a`,
  `B_cap` and `C_cert` are each the value of their own defining chain, leaving
  only the public inputs `D`, `Y`, `m_R`, `n_R`, `b_out`, the configuration
  fields `C_0`, `B_s` and the auxiliary depth `u` symbolic;
* `eq:tref-growth` -> `tref_growth_at_scheduled_width`, at
  `L_P = clog_2(P_0)`;
* the middle row of `eq:cover-instance-tested-endpoints` ->
  `BsingStar_tested_at_bridge_width`, at `Q = EntryGates.Qwidth`.

Only `eq:lambda-template-exact` and `eq:lambda-template-window` have **no**
paper instance here, because the paper's own instance needs the Stage-4
duplication multiplicities and the materialized Stage-2 family; that obligation
is deferred and is recorded here for the (not yet created) ledger row, and
`lambdaTexact_window_probe` is a labelled **NON-FIDELITY** probe that does not
discharge it.

## GAP-EXPOSED

* **`eq:lambda-template-exact` is a value, not an identification.**  `06:149`
  obtains the display "by direct substitution in the row multiplicities"; those
  row multiplicities are `eq:protected-multiplicities` (`08:98--109`) of
  `sec:dense-duplication` (`08:15`).
  **Provenance repaired at `cc-t7t`, comment-only.**  The earlier reading here
  -- that the multiplicity table "is not formalized" -- was **stale at the
  bytes** and is withdrawn: `DenseStageFourOpening` reifies all seven
  multiplicities (`wBase`, `wSel`, `wDiag`, `uBase`, `uTemp`, `uVert`,
  `uBlock`, with the frozen `*F` abbreviations) and pins them at
  `protectedA_at_frozen_multiplicities` (`08:99--107`).  What is unlanded is
  the **substitution step itself** -- no declaration on this route carries
  `06:149`'s computation from those multiplicities through to the Section-9
  template density -- which is exactly how
  `lambdaTemplate_window_of_substitution` already states the gap at its own
  docstring.  Accordingly `lambdaTexact` is the frozen right-hand side and
  nothing here proves it equals the banked Section-9 density
  `ScaleAlignOpening.lambdaTemplate`; that bridge carries the identification as
  an **explicit named hypothesis** `hsub`.  The deferred paper-instance
  canonical-inhabitation obligation is carried by
  `SCHEDULE-TEMPLATE-RESIDUE-001` and is to be discharged when the substitution
  step lands.  `lambdaTexact_window_probe` is a
  **NON-FIDELITY** smoke probe and never satisfies that obligation.
* **`eq:template-source-ratio` is not asserted at the schedule point.**  Its
  three premises -- balancedness `|C_2| >= (q_1 m_R)^{t_2}/(1 + eps_2)`,
  `T_raw = s |C_2|` and `S_raw = N_src |Rows(R)|` (`06:168--171`) -- are the
  materialized Stage-2 family, which is not built here; they enter
  `sraw_le_betaT_mul_traw` as explicit named hypotheses.  Likewise the three
  simpler comparisons of `06:177--182` enter
  `templateSourceRatio_of_comparisons` as hypotheses: the first,
  `s - 3 <= N_E`, is the auxiliary persistent row
  `AUX.PRE.SOURCE.S_MINUS3_LE_NE` that `06:183--185` proves elsewhere and
  states "is not a target gate".
* **Two of the three rows of `eq:hard-seed-width-gates` are not proved.**
  `k_T >= m_HS` and `log_2 s < b_T` are what `06:264` calls "The finite search
  fixing `B_s`", a source-scale search that belongs to `sec:effective-cutoff`
  (`PARAM-001`, Lean pending).  They are stated as the first and third
  conjuncts of `hardSeedWidthGates` and consumed as hypotheses; only the
  divisibility row is discharged.
* **`eq:P0-growth` needs `D <= B_pub`.**  `06:480` reads it from `06:49`
  (`B_pub = max{D, Y}`); the reification `Bpub` makes it a `le_max_left`, so at
  the scheduled point it is discharged rather than assumed, but the general
  theorem keeps it an explicit hypothesis because a consumer may supply another
  public bound.
* **`eq:tref-growth` is landed only in its explicit-constant form.**  The
  asymptotic assertion `log_2 t_ref = O(L_P^2)` is, by `06:578--579`, the output
  of "the symbolic-`A_wrap` cutoff proof in `thm:eff-ledger`" -- unlanded.  What
  is proved here is the exact integer bound at the frozen tested endpoint,
  `log_2 t_ref <= k_ref^* = c_seed L_P^2`, and the four
  `eq:kref-fixed-persistence` conclusions (`KREF-LOWER-2P19`, `KREF-LOWER-T0`,
  `KREF-EXP-WIDTH`, `KREF-J49-WIDTH`) remain **explicit named hypotheses**,
  exactly as the banked `kref_le_star` leaves them.  `06:628--629`: "Neither the
  returned value nor a growth assertion about it proves termination."
* **The middle row of `eq:cover-instance-tested-endpoints` needs a denominator
  code.**  `den(1 - eta_C)` is not a fixed numeral -- `eta_C` depends on `s` and
  on `delta_v(G)` -- so `BsingStar_tested` carries the reduced-fraction datum
  `1 - eta_C = a/b` with `0 < a < b` as explicit hypotheses.  The banked
  `one_sub_etaC_legal` certifies `0 < 1 - eta_C < 1`, so that datum is
  consistent, but this module does not compute it; the coefficient row that
  would is part of the literal coefficient pass of `sec:effective-cutoff`.
* Nothing about `thm:eff-ledger`, route completion, or any complexity or
  robustness conclusion is claimed.
-/

universe u

namespace EthInapproximability.ParameterizedNP.ScheduleTemplateResidue

open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.RawLowProfileBody
open EthInapproximability.ParameterizedNP.HardSeedFacade
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.ParameterSchedule

/-! ## Section 0  One exponent fact

**The binary length `bl` is not reified here -- and is not reified anywhere on
this route.**  `02:282` fixes `bl(x) = clog2N(x + 1)` with
`clog2N(x) = min{r : x <= 2^r}`.  That display has **no** named Lean home: the
three abbreviations the schedule-residue tranche briefly carried (one here, one
in `SchedulePhysicalResidue`, one in `ScheduleMajorantResidue`) were all deleted
under a binding judged prescription, and the resolution is the **inline frozen
expression**.  Every occurrence below is therefore written inline as
`Nat.clog 2 (x + 1)`, exactly as the banked `SCHEDULE-001` row already writes it
(`cover_tested_endpoint`, `Bref_le_tested`, `Bpair_le_tested`).  Every
`bl`-bearing display below -- `eq:P0-growth` (`06:494--499`),
`eq:LP-PA-literal-dominance` (`06:502--508`) and
`eq:cover-instance-tested-endpoints` (`06:682--693`, whose `06:665` reads "Put
`r = bl(v) = clog_2(v + 1)`") -- therefore carries the inline expression in its
own statement.

`n < 2^n` is likewise not restated here: it is the banked
`DenseSynchronisation.self_lt_two_pow`, consumed below by fully qualified
pin. -/

/-- **Aux B5.**  `n^2 <= 2^n` for `n >= 4`.  This is the arithmetic content of
`06:483`, "`(log_2 A_*)^2 <= A_*`", at the exponent floor `4` that the branch
`16 <= A_*` of `eq:Astar-choice` (`06:301`) forces.  General for `4 <= n`. -/
theorem sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hlin : 2 * n + 1 ≤ n ^ 2 := by nlinarith
      have hstep : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
      have hsum : n ^ 2 + (2 * n + 1) ≤ 2 ^ n + 2 ^ n :=
        Nat.add_le_add ih (le_trans hlin ih)
      have hpow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega

/-! ## Section 1  `eq:lambda-template-exact` (`06:150--156`)

`06:143--149`: "The source-to-template ratio must also make the physical
template alphabet large.  If `X_0 = T_raw + S_raw`, `S_raw = V_raw + B_raw`,
then direct substitution in the row multiplicities gives ..." -/

/-- **`X_0 = T_raw + S_raw`** (`06:146`), the raw row total. -/
noncomputable def Xzero (Traw Sraw : ℝ) : ℝ := Traw + Sraw

/-- **`S_raw = V_raw + B_raw`** (`06:147`), the raw source total split into its
vertex and blocker halves. -/
noncomputable def SrawOf (Vraw Braw : ℝ) : ℝ := Vraw + Braw

/-- **`lambda_T = (1 - 2^{-20}) T_raw/(T_raw + S_raw) + 2^{-21}`**
(`eq:lambda-template-exact`, `06:150--156`).

The frozen right-hand side, in the frozen spelling, over the raw totals of
`06:145--148`.  This is the **value** the row multiplicities substitute into the
Section-9 template density; it is deliberately *not* stated to equal
`ScaleAlignOpening.lambdaTemplate`, because that identification is the
**substitution step** of `06:149` and is unlanded (see GAP-EXPOSED).  The
multiplicity table it substitutes, `eq:protected-multiplicities` (`08:98--109`)
of `sec:dense-duplication`, is itself banked at
`DenseStageFourOpening.protectedA_at_frozen_multiplicities`; provenance
corrected at `cc-t7t`, comment-only, and the gap is unchanged. -/
noncomputable def lambdaTexact (Traw Sraw : ℝ) : ℝ :=
  (1 - 1 / 2 ^ 20) * (Traw / (Traw + Sraw)) + 1 / 2 ^ 21

/-- **Pin (`eq:fixed-protected-masses`, `06:127--139`).**  The two coefficients
of `eq:lambda-template-exact` are the banked protected masses `sigma = 2^{-20}`
and `nu_T = 2^{-21}`, recorded as a checked equation rather than as an editorial
remark, so that the display's constants are not free numerals. -/
theorem lambdaTexact_coefficients_are_frozen_masses :
    (1 : ℝ) / 2 ^ 20 = ((sigmaMass : ℚ) : ℝ) ∧ (1 : ℝ) / 2 ^ 21 = nuTempR := by
  constructor
  · rw [sigmaMass]; norm_num
  · rw [protectedMasses_agree.1]

/-- **Aux L1 (a density is nonnegative).**  General for nonnegative raw
totals. -/
theorem lambdaTexact_nonneg {Traw Sraw : ℝ} (hT : 0 ≤ Traw) (hS : 0 ≤ Sraw) :
    0 ≤ lambdaTexact Traw Sraw := by
  have hquot : 0 ≤ Traw / (Traw + Sraw) := by positivity
  rw [lambdaTexact]
  nlinarith

/-- **Aux L2 (the upper half of `eq:lambda-template-window`, `06:174`).**
`lambda_T <= 1 - 2^{-21}`, from `T_raw/(T_raw + S_raw) <= 1` alone: the frozen
arithmetic `1 - 2^{-20} + 2^{-21} = 1 - 2^{-21}`.  No ratio hypothesis is
needed, which is the display's own asymmetry.  General for a positive row
total. -/
theorem lambdaTexact_le_one_sub {Traw Sraw : ℝ} (hT : 0 ≤ Traw) (hS : 0 ≤ Sraw)
    (hpos : 0 < Traw + Sraw) :
    lambdaTexact Traw Sraw ≤ 1 - 1 / 2 ^ 21 := by
  have hquot : Traw / (Traw + Sraw) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  rw [lambdaTexact]
  nlinarith

/-! ## Section 2  `beta_T` and `eq:template-source-ratio` (`06:157--201`) -/

/-- **`beta_T = (1/100 - 2^{-21})/(99/100 - 2^{-21})`** (`06:157--160`).

The frozen closed form, read from its **defining** display and not from the
comparison `beta_T s q_2 >= 1 + eps_2` at `06:181` that consumes it. -/
noncomputable def betaT : ℝ := (1 / 100 - 1 / 2 ^ 21) / (99 / 100 - 1 / 2 ^ 21)

/-- **Aux R1.**  `0 < beta_T`.  General; no side condition. -/
theorem betaT_pos : 0 < betaT := by rw [betaT]; norm_num

/-- **Aux R2.**  `beta_T < 1`.  This is what makes the ratio gate a genuine
restriction: a value at least one would let every `S_raw` pass.  General. -/
theorem betaT_lt_one : betaT < 1 := by rw [betaT]; norm_num

/-- **Pin (`eq:fixed-protected-masses`).**  The two `2^{-21}` occurrences in
`beta_T` are **not** the same mass: the numerator's is the gap
`sigma - nu_T = 2^{-20} - 2^{-21}` left by `eq:lambda-template-exact`, while the
denominator's is `nu_T`.  Recording the reading as a checked equation keeps the
distinction visible. -/
theorem betaT_eq_frozen_masses :
    betaT = (1 / 100 - (((sigmaMass : ℚ) : ℝ) - nuTempR)) / (99 / 100 - nuTempR) := by
  rw [betaT, sigmaMass, protectedMasses_agree.1]
  norm_num

/-- **`eq:template-source-ratio`** (`06:162--167`):
`(1 + eps_2) N_src <= beta_T s q_1^{t_2} |Rows(R)|^{t_2 - 1}`.

`06:161`: "After the Stage-2 family has been materialised, we check".  A `Prop`
abbreviation for exactly that one inequality -- never a bundle of derived facts,
and never a conclusion.  The truncating `t_2 - 1` is the frozen natural
exponent. -/
noncomputable def templateSourceRatio (eps2 Nsrc : ℝ) (s q1 mR t2 : ℕ) : Prop :=
  (1 + eps2) * Nsrc
    ≤ betaT * (s : ℝ) * (q1 : ℝ) ^ t2 * (mR : ℝ) ^ (t2 - 1)

/-- **Aux R3.**  The gate is exactly that inequality and nothing more. -/
theorem templateSourceRatio_iff (eps2 Nsrc : ℝ) (s q1 mR t2 : ℕ) :
    templateSourceRatio eps2 Nsrc s q1 mR t2 ↔
      (1 + eps2) * Nsrc
        ≤ betaT * (s : ℝ) * (q1 : ℝ) ^ t2 * (mR : ℝ) ^ (t2 - 1) :=
  Iff.rfl

/-- **Aux R4 (the gate is not free) --- BEYOND-PAPER AUDIT (rejection probe).**

At the degenerate source scale `s = 0` the right side collapses to zero while
the left side is positive, so the ratio check fails for **every** choice of the
remaining parameters.  The scale `0` is illegal for the schedule -- `sScale`
never returns it, by `sScale_floor` -- and this declaration claims no legality:
it audits our encoding at a point the paper never visits, purely to show that
`templateSourceRatio` is refutable. -/
theorem templateSourceRatio_refuted_at_zero_scale {eps2 : ℝ} (heps : 0 ≤ eps2)
    (q1 mR t2 : ℕ) : ¬ templateSourceRatio eps2 1 0 q1 mR t2 := by
  rw [templateSourceRatio]
  push_neg
  have : betaT * ((0 : ℕ) : ℝ) * (q1 : ℝ) ^ t2 * (mR : ℝ) ^ (t2 - 1) = 0 := by
    push_cast; ring
  rw [this]
  linarith

/-- **`06:177--201`, the three simpler comparisons.**

"The check itself follows from the three simpler comparisons `s - 3 <= N_E`,
`t_2 >= 2 log_2 q_2`, `beta_T s q_2 >= 1 + eps_2`. ... Since `q_1 >= 2`, the
second comparison gives `q_1^{t_2} >= 2^{t_2} >= q_2^2`.  Hence the right side
of `eq:template-source-ratio` is at least `beta_T s q_2^2 >= (1 + eps_2) q_2`,
which is at least its left side by
`eq:source-template-count-cancellation`."

The frozen derivation in the kernel.  The power-of-two status of `q_2` is
supplied in the frozen shape `q_2 = 2^r` (the banked `q2_isPowTwo`), so the step
`2^{t_2} >= q_2^2` is proved rather than assumed, and the count bound
`N_src <= q_2` is exactly the conclusion of
`source_template_count_cancellation`. -/
theorem templateSourceRatio_of_comparisons {eps2 Nsrc : ℝ} {q2v s q1 mR t2 r : ℕ}
    (hq1 : 2 ≤ q1) (hq2 : q2v = 2 ^ r) (ht2r : 2 * r ≤ t2) (ht2 : 1 ≤ t2)
    (hmR : 1 ≤ mR) (heps : 0 ≤ eps2)
    (hbeta : 1 + eps2 ≤ betaT * (s : ℝ) * (q2v : ℝ))
    (hcount : Nsrc ≤ (q2v : ℝ)) :
    templateSourceRatio eps2 Nsrc s q1 mR t2 := by
  have hq2pos : (0 : ℝ) < (q2v : ℝ) := by
    rw [hq2]; positivity
  have hbetaS : (0 : ℝ) ≤ betaT * (s : ℝ) := by
    have := betaT_pos; positivity
  -- `q_1^{t_2} >= 2^{t_2} >= q_2^2`
  have hq1pow : (2 : ℝ) ^ t2 ≤ (q1 : ℝ) ^ t2 := by
    have h2 : (2 : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hq1
    exact pow_le_pow_left₀ (by norm_num) h2 t2
  have hq2sq : (q2v : ℝ) ^ 2 ≤ (2 : ℝ) ^ t2 := by
    have hcast : (q2v : ℝ) ^ 2 = (2 : ℝ) ^ (2 * r) := by
      rw [hq2]; push_cast; rw [← pow_mul]; ring_nf
    rw [hcast]
    exact pow_le_pow_right₀ (by norm_num) ht2r
  have hchain : (q2v : ℝ) ^ 2 ≤ (q1 : ℝ) ^ t2 := le_trans hq2sq hq1pow
  -- `m_R^{t_2 - 1} >= 1`
  have hmRpow : (1 : ℝ) ≤ (mR : ℝ) ^ (t2 - 1) := by
    have h1 : (1 : ℝ) ≤ (mR : ℝ) := by exact_mod_cast hmR
    exact one_le_pow₀ h1
  -- assemble
  have hstep1 : betaT * (s : ℝ) * (q2v : ℝ) ^ 2
      ≤ betaT * (s : ℝ) * (q1 : ℝ) ^ t2 :=
    mul_le_mul_of_nonneg_left hchain hbetaS
  have hstep2 : betaT * (s : ℝ) * (q1 : ℝ) ^ t2
      ≤ betaT * (s : ℝ) * (q1 : ℝ) ^ t2 * (mR : ℝ) ^ (t2 - 1) := by
    have hpos : (0 : ℝ) ≤ betaT * (s : ℝ) * (q1 : ℝ) ^ t2 := by positivity
    nlinarith
  have hstep3 : (1 + eps2) * (q2v : ℝ) ≤ betaT * (s : ℝ) * (q2v : ℝ) ^ 2 := by
    nlinarith
  have hstep4 : (1 + eps2) * Nsrc ≤ (1 + eps2) * (q2v : ℝ) := by
    nlinarith
  rw [templateSourceRatio]
  linarith

/-! ## Section 3  `eq:lambda-template-window` (`06:168--176`) -/

/-- **`06:168--172`, the balancedness substitution.**

"Balancedness gives `|C_2| >= (q_1 |Rows(R)|)^{t_2}/(1 + eps_2)`, while
`T_raw = s |C_2|` and `S_raw = N_src |Rows(R)|`.  Therefore
`eq:template-source-ratio` implies ..." --- the exact intermediate the window
needs, namely `S_raw <= beta_T T_raw`.

The three quoted facts are the materialized Stage-2 family and enter as
**explicit named hypotheses**: nothing here builds that family. -/
theorem sraw_le_betaT_mul_traw {eps2 Nsrc C2 Traw Sraw : ℝ} {s q1 mR t2 : ℕ}
    (hratio : templateSourceRatio eps2 Nsrc s q1 mR t2)
    (hbal : ((q1 : ℝ) * (mR : ℝ)) ^ t2 / (1 + eps2) ≤ C2)
    (hT : Traw = (s : ℝ) * C2)
    (hS : Sraw = Nsrc * (mR : ℝ))
    (heps : 0 < 1 + eps2) (ht2 : 1 ≤ t2) (hmR : 0 < mR) :
    Sraw ≤ betaT * Traw := by
  have hbetaS : (0 : ℝ) ≤ betaT * (s : ℝ) := by
    have := betaT_pos; positivity
  have hmRpos : (0 : ℝ) < (mR : ℝ) := by exact_mod_cast hmR
  rw [templateSourceRatio] at hratio
  -- multiply the ratio gate by `m_R` and fold the exponent back up
  have hsplit : (mR : ℝ) ^ (t2 - 1) * (mR : ℝ) = (mR : ℝ) ^ t2 := by
    have ht : t2 - 1 + 1 = t2 := by omega
    rw [← pow_succ, ht]
  have hprod : ((q1 : ℝ) * (mR : ℝ)) ^ t2 = (q1 : ℝ) ^ t2 * (mR : ℝ) ^ t2 :=
    mul_pow _ _ _
  have hmul : (1 + eps2) * Nsrc * (mR : ℝ)
      ≤ betaT * (s : ℝ) * (q1 : ℝ) ^ t2 * (mR : ℝ) ^ (t2 - 1) * (mR : ℝ) :=
    mul_le_mul_of_nonneg_right hratio (le_of_lt hmRpos)
  have hrewrite : betaT * (s : ℝ) * (q1 : ℝ) ^ t2 * (mR : ℝ) ^ (t2 - 1) * (mR : ℝ)
      = betaT * (s : ℝ) * (((q1 : ℝ) * (mR : ℝ)) ^ t2) := by
    rw [hprod, ← hsplit]; ring
  rw [hrewrite] at hmul
  -- divide by `1 + eps_2` and use balancedness
  have hdiv : Nsrc * (mR : ℝ)
      ≤ betaT * (s : ℝ) * (((q1 : ℝ) * (mR : ℝ)) ^ t2 / (1 + eps2)) := by
    rw [← mul_div_assoc, le_div_iff₀ heps]
    have hcomm : Nsrc * (mR : ℝ) * (1 + eps2)
        = (1 + eps2) * Nsrc * (mR : ℝ) := by ring
    rw [hcomm]
    exact hmul
  have hbalmul : betaT * (s : ℝ) * (((q1 : ℝ) * (mR : ℝ)) ^ t2 / (1 + eps2))
      ≤ betaT * (s : ℝ) * C2 :=
    mul_le_mul_of_nonneg_left hbal hbetaS
  rw [hS, hT]
  calc Nsrc * (mR : ℝ)
      ≤ betaT * (s : ℝ) * (((q1 : ℝ) * (mR : ℝ)) ^ t2 / (1 + eps2)) := hdiv
    _ ≤ betaT * (s : ℝ) * C2 := hbalmul
    _ = betaT * ((s : ℝ) * C2) := by ring

/-- **`eq:lambda-template-window`, lower row** (`06:173--176`):
`99/100 <= lambda_T`.

The frozen constant `beta_T` is exactly the ratio at which this becomes an
equality: `(1 - 2^{-20})/(1 + beta_T) = 99/100 - 2^{-21}`.  So the window is
tight at `S_raw = beta_T T_raw`, and no slack is invented. -/
theorem lambdaTexact_ge {Traw Sraw : ℝ} (hT : 0 < Traw) (hS : 0 ≤ Sraw)
    (h : Sraw ≤ betaT * Traw) :
    99 / 100 ≤ lambdaTexact Traw Sraw := by
  have hden : 0 < Traw + Sraw := by linarith
  have hb : (0 : ℝ) < betaT := betaT_pos
  have hkey : (1 : ℝ) / (1 + betaT) ≤ Traw / (Traw + Sraw) := by
    rw [div_le_div_iff₀ (by linarith) hden]
    nlinarith
  have hcoef : (0 : ℝ) ≤ 1 - 1 / 2 ^ 20 := by norm_num
  have hmul : (1 - 1 / 2 ^ 20 : ℝ) * (1 / (1 + betaT))
      ≤ (1 - 1 / 2 ^ 20 : ℝ) * (Traw / (Traw + Sraw)) :=
    mul_le_mul_of_nonneg_left hkey hcoef
  have hval : (1 - 1 / 2 ^ 20 : ℝ) * (1 / (1 + betaT)) = 99 / 100 - 1 / 2 ^ 21 := by
    rw [betaT]; norm_num
  rw [lambdaTexact]
  linarith

/-- **`eq:lambda-template-window`** (`06:173--176`), both rows:
`99/100 <= lambda_T <= 1 - 2^{-21}`. -/
theorem lambdaTemplateWindow {Traw Sraw : ℝ} (hT : 0 < Traw) (hS : 0 ≤ Sraw)
    (h : Sraw ≤ betaT * Traw) :
    99 / 100 ≤ lambdaTexact Traw Sraw ∧
      lambdaTexact Traw Sraw ≤ 1 - 1 / 2 ^ 21 :=
  ⟨lambdaTexact_ge hT hS h,
    lambdaTexact_le_one_sub (le_of_lt hT) hS (by linarith)⟩

/-- **`06:172--176`, the implication the section states.**

"Therefore `eq:template-source-ratio` implies `eq:lambda-template-window`."  The
composite of `sraw_le_betaT_mul_traw` with `lambdaTemplateWindow`, at the
balancedness data of `06:168--171`. -/
theorem template_source_ratio_implies_window
    {eps2 Nsrc C2 Traw Sraw : ℝ} {s q1 mR t2 : ℕ}
    (hratio : templateSourceRatio eps2 Nsrc s q1 mR t2)
    (hbal : ((q1 : ℝ) * (mR : ℝ)) ^ t2 / (1 + eps2) ≤ C2)
    (hT : Traw = (s : ℝ) * C2)
    (hS : Sraw = Nsrc * (mR : ℝ))
    (heps : 0 < 1 + eps2) (ht2 : 1 ≤ t2) (hmR : 0 < mR)
    (hTpos : 0 < Traw) (hSnn : 0 ≤ Sraw) :
    99 / 100 ≤ lambdaTexact Traw Sraw ∧
      lambdaTexact Traw Sraw ≤ 1 - 1 / 2 ^ 21 :=
  lambdaTemplateWindow hTpos hSnn
    (sraw_le_betaT_mul_traw hratio hbal hT hS heps ht2 hmR)

/-- **The bridge to the banked Section-9 density --- GAP-EXPOSED.**

`09:131` records "The duplication schedule gives `lambda_T >= 99/100`" and
`ScaleAlignOpening.lambdaTemplate_ge_of_card` converts a cardinality bound into
it; the *derivation* is `eq:lambda-template-exact`, whose substitution step
(`06:149`, "direct substitution in the row multiplicities") is unlanded.  That
substitution is therefore carried here as the **explicit named hypothesis**
`hsub`, and no consumer may read the identification off this module. -/
theorem lambdaTemplate_window_of_substitution {Cl : Type*} [Fintype Cl]
    (YT : Finset Cl) {Traw Sraw : ℝ}
    (hsub : EthInapproximability.ParameterizedNP.ScaleAlignOpening.lambdaTemplate YT
      = lambdaTexact Traw Sraw)
    (hT : 0 < Traw) (hS : 0 ≤ Sraw) (h : Sraw ≤ betaT * Traw) :
    99 / 100 ≤ EthInapproximability.ParameterizedNP.ScaleAlignOpening.lambdaTemplate YT ∧
      EthInapproximability.ParameterizedNP.ScaleAlignOpening.lambdaTemplate YT
        ≤ 1 - 1 / 2 ^ 21 := by
  rw [hsub]
  exact lambdaTemplateWindow hT hS h

/-- **NON-FIDELITY smoke probe (BEYOND-PAPER AUDIT).**

The window is inhabited, and inhabited *at its extreme point*: taking the raw
totals in the frozen ratio `S_raw = beta_T T_raw` makes the lower row an
equality, so the probe is not a degenerate interior point.  It is nevertheless
**not** the paper's instance -- that one needs the materialized Stage-2 family
and the duplication multiplicities -- and it does not discharge the deferred
paper-instance canonical-inhabitation obligation carried by
`SCHEDULE-TEMPLATE-RESIDUE-001`. -/
theorem lambdaTexact_window_probe :
    99 / 100 ≤ lambdaTexact 1 betaT ∧ lambdaTexact 1 betaT ≤ 1 - 1 / 2 ^ 21 :=
  lambdaTemplateWindow (by norm_num) (le_of_lt betaT_pos) (by rw [mul_one])

/-! ## Section 4  `eq:source-template-count-cancellation` (`06:188--195`)

`06:186--187`: "The guarded-source count and the public no-isolates inequality
`N_V <= 2 N_E` then give the exact cancellation".  Both inputs are banked:
the count is `GuardedSourceSlab.card_slabRow` (the carrier of `04:526`) and the
width comparison is `GuardedSourceSlab.card_le_q2`. -/

/-- **`eq:source-template-count-cancellation`** (`06:188--195`):

`N_src = 4s(N_V + s - 3) <= 4s(2 N_E + N_E) = 12 s N_E <= q_2`.

All three steps of the frozen chain, on the **paper's own guarded source**: the
first is the banked row count, the middle is the two premises of `06:183--187`,
and the last is the banked least-power-of-two width bound.  `06:196--197`: "This
auxiliary row is consumed only by this source-to-template cancellation.  It is
not included among the candidate target gates." -/
theorem source_template_count_cancellation {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (s : ℕ)
    (hminus : s - 3 ≤ Fintype.card E)
    (hiso : Fintype.card V ≤ 2 * Fintype.card E) :
    Fintype.card (SlabRow V s) = 4 * s * (Fintype.card V + (s - 3)) ∧
      4 * s * (Fintype.card V + (s - 3)) ≤ 12 * s * Fintype.card E ∧
      12 * s * Fintype.card E ≤ q2 G s := by
  refine ⟨card_slabRow V s, ?_, card_le_q2 G s⟩
  have hsum : Fintype.card V + (s - 3) ≤ 3 * Fintype.card E := by omega
  calc 4 * s * (Fintype.card V + (s - 3))
      ≤ 4 * s * (3 * Fintype.card E) := Nat.mul_le_mul_left _ hsum
    _ = 12 * s * Fintype.card E := by ring

/-- **Canonical inhabitation (`eq:source-template-count-cancellation` at the
schedule's own scale).**

The same chain with `s` supplied by the frozen `eq:s-choice` chain
(`sScale (uAux (Apre ...))` evaluated through `sScale_eq_pow`), so **no numeral
is assigned to `s`**.  The two premises of `06:183--187` remain explicit
hypotheses: `s - 3 <= N_E` is the auxiliary persistent row
`AUX.PRE.SOURCE.S_MINUS3_LE_NE` proved elsewhere (`06:183--185`), and
`N_V <= 2 N_E` is the banked public no-isolates inequality
`PublicRecords.publicInput_card_vertex_le`. -/
theorem source_template_count_cancellation_at_scheduled_scale {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (Bs u : ℕ)
    (hminus : sScale Bs u - 3 ≤ Fintype.card E)
    (hiso : Fintype.card V ≤ 2 * Fintype.card E) :
    Fintype.card (SlabRow V (sScale Bs u))
        = 4 * sScale Bs u * (Fintype.card V + (sScale Bs u - 3)) ∧
      4 * sScale Bs u * (Fintype.card V + (sScale Bs u - 3))
        ≤ 12 * sScale Bs u * Fintype.card E ∧
      12 * sScale Bs u * Fintype.card E ≤ q2 G (sScale Bs u) :=
  source_template_count_cancellation G (sScale Bs u) hminus hiso

/-! ## Section 5  `eq:hard-seed-width-gates` (`06:237--273`)

`06:237--244` fixes the auxiliary Stage-3 depth `k_T = log_2(s/4)`,
`b_T = 2^{j_49(k_T)}`, `x_T = 2^{-b_T}`; `06:264--269` is the three-row gate the
finite search fixing `B_s` enforces; `06:271--273` is its consequence for the
three hard-seed widths `I_j = s/2^j`. -/

/-- **`k_T = log_2(s/4)`** (`06:239`).  The frozen natural quotient `s/4` is
kept, and the logarithm is the exact integer one; `06:122` makes `s` a power of
two, so the value is exact at every legal scale (`kT_at_pow_two`). -/
def kT (s : ℕ) : ℕ := Nat.log 2 (s / 4)

/-- **`b_T = 2^{j_49(k_T)}`** (`06:241`), built from the banked integer
primitive `ParameterSchedule.j49` --- which is *not* redefined here. -/
def bT (s : ℕ) : ℕ := 2 ^ j49 (kT s)

/-! **`x_T = 2^{-b_T}`**, the General Hard Seed column density at width `s/4`
(`06:274--276`), is **not** reified here.  Its single Lean home on this route is
the **banked** `DenseStageFourOpening.xTdepth`, which the banked
`TerminalTwoStream.probeXT` already consumes; this module writes it at the
Stage-3 depth of `06:241` as `xTdepth (bT s)` and carries no second copy.

Anchor record, checked first-hand against both files this round: the banked
docstring cites **`08:166` only**.  `06:243` is a genuine second printing of the
same display -- the frozen `06:238--243` sets `k_T = log_2(s/4)`,
`b_T = 2^{j_49(k_T)}`, `x_T = 2^{-b_T}` in one aligned display -- but the banked
declaration does **not** cite it, and an earlier version of this comment claimed
it did.  That claim is withdrawn; adding the second anchor to the banked
docstring would be an edit to a banked module and is not done here. -/

/-- **`eq:hard-seed-width-gates`** (`06:264--269`):
`k_T = log_2(s/4) >= m_HS`, `16 | (s/4)`, `log_2 s < b_T`.

All three rows, in the frozen print order, as one `Prop` with three conjuncts.
`06:270`: "These are fixed source-scale conditions: after increasing `B_s` once,
they hold for every admissible public input."  The exponent threshold `m_HS` is
the banked `HardSeedFacade.mHS` at the consumer's universe and is never assigned
a numeral. -/
def hardSeedWidthGates (s mHSv : ℕ) : Prop :=
  mHSv ≤ kT s ∧ 16 ∣ s / 4 ∧ Nat.log 2 s < bT s

/-- **Aux H1.**  The gate is exactly that conjunction and nothing more. -/
theorem hardSeedWidthGates_iff (s mHSv : ℕ) :
    hardSeedWidthGates s mHSv ↔
      (mHSv ≤ kT s ∧ 16 ∣ s / 4 ∧ Nat.log 2 s < bT s) :=
  Iff.rfl

/-- **Aux H2 (`06:239` evaluated on the frozen power-of-two scale).**
`k_T = e - 2` at `s = 2^e`, `e >= 2`.  General. -/
theorem kT_at_pow_two {e : ℕ} (he : 2 ≤ e) : kT (2 ^ e) = e - 2 := by
  have hsplit : (2 : ℕ) ^ e = 4 * 2 ^ (e - 2) := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add]
    congr 1
    omega
  have hdiv : (2 : ℕ) ^ e / 4 = 2 ^ (e - 2) := by
    rw [hsplit, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  rw [kT, hdiv, Nat.log_pow (by norm_num)]

/-- **The divisibility row of `eq:hard-seed-width-gates`, discharged at the
schedule's own scale.**

`16 | (s/4)` at `s = 2^{ceil(B_s u^2)}`, read off the banked `sScale_floor`
(`64 | s`, the form `06:975` records: "The penultimate comparison uses `64 | s`,
hence `s >= 64`").  No numeral is assigned to `s`. -/
theorem sScale_divisibility_row {Bs u : ℕ} (hBs : 1 ≤ Bs) (hu : 3 ≤ u) :
    16 ∣ sScale Bs u / 4 := by
  obtain ⟨-, c, hc⟩ := sScale_floor hBs hu
  refine ⟨c, ?_⟩
  rw [hc]
  have h : (64 : ℕ) * c = 4 * (16 * c) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]

/-- **`06:271--273`, the consequence for the three hard-seed widths.**

"Consequently each `I_j = s/2^j`, `j = 0,1,2`, is a legal hard-seed width and
satisfies `I_j < 2^{b_T}`."  Proved from the third row alone, at the frozen
power-of-two scale.  General in the rung index. -/
theorem interlaceWidth_lt_two_pow_bT {e j : ℕ}
    (h : Nat.log 2 (2 ^ e) < bT (2 ^ e)) :
    2 ^ e / 2 ^ j < 2 ^ bT (2 ^ e) := by
  have hlog : Nat.log 2 ((2 : ℕ) ^ e) = e := Nat.log_pow (by norm_num) e
  have hdiv : (2 : ℕ) ^ e / 2 ^ j ≤ 2 ^ e := Nat.div_le_self _ _
  have hlt : (2 : ℕ) ^ e < 2 ^ bT (2 ^ e) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- **Canonical inhabitation (`eq:hard-seed-width-gates` at the schedule's own
scale and the banked exponent threshold).**

All three rows at `s = 2^{ceil(B_s u^2)}` and `m_HS = HardSeedFacade.mHS`, so
neither the scale nor the threshold is a free binder and neither is assigned a
numeral (`06:256--261`: `m_HS` "is fixed once, before any source instance or
compiler input", and no numeral for it is printed).  The divisibility row is
**discharged** off `sScale_floor`; the other two rows are precisely what
`06:264` defers to "The finite search fixing `B_s`" and enter as explicit named
hypotheses (see GAP-EXPOSED). -/
theorem hardSeedWidthGates_at_scheduled_scale {Bs uA : ℕ} (hBs : 1 ≤ Bs)
    (hu : 3 ≤ uA)
    (hthr : mHS.{u} ≤ kT (sScale Bs uA))
    (hbT : Nat.log 2 (sScale Bs uA) < bT (sScale Bs uA)) :
    hardSeedWidthGates (sScale Bs uA) mHS.{u} :=
  ⟨hthr, sScale_divisibility_row hBs hu, hbT⟩

/-- **Aux H3.**  `0 < x_T`: the auxiliary column density is a genuine density,
so the Stage-3 calls of `06:274--278` are made at a legal threshold.  General. -/
theorem xT_pos (s : ℕ) : 0 < xTdepth (bT s) := by
  rw [xTdepth]; positivity

/-- **Aux H4.**  `x_T <= 1`.  General. -/
theorem xT_le_one (s : ℕ) : xTdepth (bT s) ≤ 1 := by
  have h : (1 : ℝ) ≤ 2 ^ bT s := one_le_pow₀ (by norm_num)
  rw [xTdepth, div_le_one (by positivity)]
  exact h

/-- **Aux H5 (the gate is not free) --- BEYOND-PAPER AUDIT (rejection probe).**

At `s = 64` --- the smallest scale the divisibility `64 | s` of `06:975` allows,
and strictly below the value `sScale` actually returns (evaluating the defining
chain `sScale Bs u = 2 ^ (Bs * u ^ 2)` at `1 <= Bs` and `3 <= u` puts the
exponent at `9` or above; the exported `sScale_floor` statement itself gives
only `3 < sScale Bs u` and `64 | sScale Bs u`) --- the third row fails
outright: `k_T = 4`,
`j_49(4) = 0`, so `b_T = 1` while `log_2 s = 6`.  Hence
`hardSeedWidthGates 64 m` is false for **every** `m`, and no bundle inhabits the
gate merely by choosing a small scale.  This declaration claims no legality; it
audits our encoding at a point the schedule never reaches. -/
theorem hardSeedWidthGates_refuted_at_sixty_four (mHSv : ℕ) :
    ¬ hardSeedWidthGates 64 mHSv := by
  rintro ⟨-, -, h3⟩
  have h64 : (64 : ℕ) / 4 = 2 ^ 4 := by norm_num
  have hk : kT 64 = 4 := by
    rw [kT, h64, Nat.log_pow (by norm_num)]
  have hj : j49 4 = 0 := by
    rw [j49]
    decide
  have hb : bT 64 = 1 := by
    rw [bT, hk, hj]
    norm_num
  have hlog : Nat.log 2 64 = 6 := by
    have h : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [h, Nat.log_pow (by norm_num)]
  rw [hb, hlog] at h3
  omega

/-! ## Section 6  `eq:b2-choice` (`06:422--427`)

`06:422`: "Writing `m_R = |Rows(R)|`, define the ordinary Stage-2 proof depth
by".  `06:428--429`: "This is the row density used by the unchanged Stage-2 and
Stage-3 analysis.  It is fixed before `t_2`." -/

/-! **`a = C_0 (log_2 A_*)^2`** (`eq:stage1-scales`, `06:314`) is **not** reified
here.  Its single Lean home on this route is the **banked**
`MassRedistributionTail.aStage1`, which states the same row over the same two
binders (`C_0` and the exponent `log_2 A_*`); this module consumes that accessor
by fully qualified pin and carries no second copy.  `log_2 A_*` is the exponent
of the power of two `A_*`, i.e. the `astarExp` of Section 7 below.  The
remaining rows of that display, `t_1`, `b_1` and `x_1`, are stated in neither
place here: `b_1` and `x_1` are likewise banked in
`MassRedistributionTail` (`b1`, `x1Stage1`). -/

/-- **`q_1 = 2^a - 2`** (`eq:stage1-scales`, `06:315`).  `06:321--322`: "`q_1 + 2`
is a power of two." -/
def q1Stage1 (av : ℕ) : ℕ := 2 ^ av - 2

/-- **`b_2 = ceil(log_2(32 s q_1 m_R)) + c_b`** (`eq:b2-choice`, `06:423--425`;
reader `03-parameterized-construction.tex:276--279`).

The frozen ceiling is **kept** as the exact integer primitive `clog_2` of
`06:75--76`; `c_b` is the universal configuration field of `06:56--62` and stays
an explicit binder, with only its frozen floor `c_b >= 6` used below. -/
def b2 (s q1 mR cb : ℕ) : ℕ := Nat.clog 2 (32 * s * q1 * mR) + cb

/-- **`h_2 = 2^{-b_2}`** (`eq:b2-choice`, `06:425`), the ordinary Stage-2 row
density. -/
noncomputable def h2 (b2v : ℕ) : ℝ := 1 / 2 ^ b2v

/-- **Aux D1 (the defining ceiling property).**  `32 s q_1 m_R <= 2^{b_2}`, in
the frozen `clog_2` sense `min{j >= 0 : z <= 2^j}`.  This is the content the
Stage-2 analysis consumes, and it survives the `+ c_b` margin.  General. -/
theorem b2_spec (s q1 mR cb : ℕ) : 32 * s * q1 * mR ≤ 2 ^ b2 s q1 mR cb := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (32 * s * q1 * mR)
  have hmono : (2 : ℕ) ^ Nat.clog 2 (32 * s * q1 * mR) ≤ 2 ^ b2 s q1 mR cb :=
    Nat.pow_le_pow_right (by norm_num) (by rw [b2]; omega)
  exact le_trans h hmono

/-- **Aux D2 (`06:62`, the configuration floor).**  `6 <= b_2` whenever
`6 <= c_b`, so the Stage-2 depth is never degenerate.  General. -/
theorem six_le_b2 {cb : ℕ} (hcb : 6 ≤ cb) (s q1 mR : ℕ) : 6 ≤ b2 s q1 mR cb := by
  rw [b2]; omega

/-- **Aux D3 (monotone in the rounding margin).**  Raising the frozen margin
`c_b` never lowers the depth.  General. -/
theorem b2_mono_cb {cb cb' : ℕ} (h : cb ≤ cb') (s q1 mR : ℕ) :
    b2 s q1 mR cb ≤ b2 s q1 mR cb' := by
  rw [b2, b2]; omega

/-- **Aux D4.**  `0 < h_2`: the Stage-2 row density is positive.  General. -/
theorem h2_pos (b2v : ℕ) : 0 < h2 b2v := by rw [h2]; positivity

/-- **Aux D5.**  `h_2 <= 1`.  General. -/
theorem h2_le_one (b2v : ℕ) : h2 b2v ≤ 1 := by
  have h : (1 : ℝ) ≤ 2 ^ b2v := one_le_pow₀ (by norm_num)
  rw [h2, div_le_one (by positivity)]
  exact h

/-- **Canonical inhabitation (`eq:b2-choice` at the schedule point).**

Both source-defined arguments are supplied by their own definitional chains --
`s` by `eq:s-choice` through the banked `sScale_eq_pow`, and `q_1` by the `q_1`
row of `eq:stage1-scales` at the reified `a` -- so **no numeral is assigned to
either**.  `m_R = |Rows(R)|` (`06:422`) and `c_b` (`06:56--62`) are the only
free inputs and stay symbolic. -/
theorem b2_at_scheduled_point (Bs u C0 lA mR cb : ℕ) :
    b2 (sScale Bs u) (q1Stage1 (MassRedistributionTail.aStage1 C0 lA)) mR cb
      = Nat.clog 2 (32 * 2 ^ (Bs * u ^ 2) * (2 ^ (C0 * lA ^ 2) - 2) * mR) + cb := by
  rw [b2, sScale_eq_pow, q1Stage1, MassRedistributionTail.aStage1]

/-- **Canonical inhabitation (`eq:template-source-ratio` on the paper's own
guarded source).**

The composition `06:196--201` performs, with every source-defined input
supplied by its own defining chain instead of by a free binder: `N_src` is the
banked row count of the guarded source (`04:526`), `q_2` is the banked
coordinate width, `s` is `eq:s-choice` evaluated, `q_1` is the `q_1` row of
`eq:stage1-scales` at the reified `a`, and `t_2` is the banked Stage-2 least
search `ParameterSchedule.t2`.  The count premise `N_src <= q_2` is **proved**
here, off `source_template_count_cancellation`, rather than assumed.

The three remaining hypotheses are exactly the frozen gates: `q_1 >= 2`
(`06:197`), `t_2 >= 2 log_2 q_2` (`06:180`, in the power-of-two form
`q_2 = 2^r`, `2r <= t_2`), and `beta_T s q_2 >= 1 + eps_2` (`06:181`).
`m_R = |Rows(R)|` and `eps_2` stay symbolic: the first is a public input
(`06:422`) and the second is the balanced-family parameter the Stage-2 search
returns. -/
theorem templateSourceRatio_at_guarded_source {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E] (G : EndpointGraph V E)
    {eps2 : ℝ} {Bs uA C0 lA mR r Lh Bc Hm : ℕ}
    (hminus : sScale Bs uA - 3 ≤ Fintype.card E)
    (hiso : Fintype.card V ≤ 2 * Fintype.card E)
    (hq1 : 2 ≤ q1Stage1 (MassRedistributionTail.aStage1 C0 lA))
    (hq2 : q2 G (sScale Bs uA) = 2 ^ r)
    (ht2r : 2 * r ≤ ParameterSchedule.t2.{u} Lh Bc Hm)
    (ht2 : 1 ≤ ParameterSchedule.t2.{u} Lh Bc Hm)
    (hmR : 1 ≤ mR) (heps : 0 ≤ eps2)
    (hbeta : 1 + eps2
      ≤ betaT * (sScale Bs uA : ℝ) * ((q2 G (sScale Bs uA) : ℕ) : ℝ)) :
    templateSourceRatio eps2 ((Fintype.card (SlabRow V (sScale Bs uA)) : ℕ) : ℝ)
      (sScale Bs uA) (q1Stage1 (MassRedistributionTail.aStage1 C0 lA)) mR
      (ParameterSchedule.t2.{u} Lh Bc Hm) := by
  obtain ⟨hcard, hmid, hq⟩ :=
    source_template_count_cancellation G (sScale Bs uA) hminus hiso
  have hnat : Fintype.card (SlabRow V (sScale Bs uA)) ≤ q2 G (sScale Bs uA) :=
    hcard.le.trans (hmid.trans hq)
  have hcount : ((Fintype.card (SlabRow V (sScale Bs uA)) : ℕ) : ℝ)
      ≤ ((q2 G (sScale Bs uA) : ℕ) : ℝ) := by exact_mod_cast hnat
  exact templateSourceRatio_of_comparisons hq1 hq2 ht2r ht2 hmR heps hbeta hcount

/-! ## Section 7  `eq:P0-growth` and `eq:LP-PA-literal-dominance`
(`06:462--508`)

`06:473--475`: "The certificate does not treat the relation between `L_P` and
`A_*` as a primitive coefficient leaf.  It records the following chain.  Each of
the six entries in the maximum defining the threshold for `A_*` is at most
`A_*`."  `06:509--512`: "The registry decomposes this calculation into the six
maximum projections and named rows for `D`, `(log_2 A_*)^2`, `a`, `B_cap`,
`log_2 s + 1`, `C_cert`, `P_0`, and `L_P`; the final row is not an opaque
dominance assertion." -/

/-- **`B_pub = max{D, Y}`** (`06:49`). -/
def Bpub (D Y : ℕ) : ℕ := max D Y

/-- **`z_R = max{ceil(log_2 |Rows(R)|), ceil(log_2 |Cols(R)|)}`**
(`06:51--54`), with the frozen ceilings read as the exact integer `clog_2`. -/
def zRpub (mR nR : ℕ) : ℕ := max (Nat.clog 2 mR) (Nat.clog 2 nR)

/-- **`U_0 = max{2, b_out/eta_R}`** (`06:296`), the requested-output-depth
threshold that `eq:Astar-choice` takes a ceiling logarithm of. -/
noncomputable def U0sched (bout : ℕ) (eR : ℝ) : ℝ := max 2 ((bout : ℝ) / eR)

/-- **The threshold of `eq:Astar-choice`** (`06:299--305`):
`max{16, B_pub, z_R, log_2 q_2, s, ceil(log_2 U_0)}`, the six branches in the
frozen print order. -/
def astarThreshold (Bpubv zR lq2 s clU0 : ℕ) : ℕ :=
  max (max (max (max (max 16 Bpubv) zR) lq2) s) clU0

/-- **The exponent of `A_*`** (`eq:Astar-choice`, `06:298--305`: "let `A_*` be
the least power of two at least" the displayed maximum).

This is the `ASTAR` row of the least-power-of-two instance table
`06:1271--1278`, served by the banked accessor `leastPowTwoExp` -- the schedule
does not open a second search. -/
noncomputable def astarExp (t : ℕ) : ℕ := leastPowTwoExp (t : ℝ)

/-- **`A_*`** (`eq:Astar-choice`, `06:298--305`). -/
noncomputable def astar (t : ℕ) : ℕ := leastPowTwoGe (t : ℝ)

/-! **`B_cap := D + a`** (`07:156`) is **not** reified here.  Its single Lean
home on this route is the **banked** `StageOneInterlace.bCap`, which is read
from the same **defining** display in `sec:one-level` and not from the passing
use `B_cap = D + a <= (C_0 + 1) A_*` at `06:486`; this module consumes that
accessor by fully qualified pin and carries no second copy. -/

/-- **`C_cert = B_cap + log_2 q_2 + log_2 s + 1`** (`eq:Ccert`, `06:430--434`).

`06:435--437`: "This is a public integer in both promise cases.  In a NO
instance it equals the exact complexity `C` of the protected Stage-4 transpose;
in a YES instance it is only a certified target used to choose later widths."
No promise-case conclusion is carried in the definition. -/
def Ccert (Bcapv lq2 ls : ℕ) : ℕ := Bcapv + lq2 + ls + 1

/-- **Aux P1 (`06:298`).**  `A_* = 2^{log_2 A_*}`: the returned width really is
a power of two, which `06:480` uses. -/
theorem astar_eq_two_pow (t : ℕ) : astar t = 2 ^ astarExp t := rfl

/-- **Aux P2 (`06:475--478`, the six maximum projections).**  Every entry of
the displayed threshold is at most `A_*`, because the threshold itself is.
General. -/
theorem le_astar (t : ℕ) : t ≤ astar t := by
  have h := le_leastPowTwoGe (t : ℝ)
  exact_mod_cast h

/-- **Aux P3 (`06:301`, the first branch).**  `16 <= ` the `A_*` threshold.
General. -/
theorem sixteen_le_astarThreshold (Bpubv zR lq2 s clU0 : ℕ) :
    16 ≤ astarThreshold Bpubv zR lq2 s clU0 := by
  unfold astarThreshold
  omega

/-- **Aux P4 (`06:481`, "`A_*` is a power of two, and `A_* >= 16`").**
`4 <= log_2 A_*` at any threshold at least `16`.  Derived from the branch, never
chosen.  General. -/
theorem four_le_astarExp {t : ℕ} (h : 16 ≤ t) : 4 ≤ astarExp t := by
  by_contra hc
  push_neg at hc
  have hle : astar t ≤ 2 ^ 3 := by
    rw [astar_eq_two_pow]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have := le_astar t
  norm_num at hle
  omega

/-- **Aux P5 (the six branch projections, one by one).**  General. -/
theorem astarThreshold_branches (Bpubv zR lq2 s clU0 : ℕ) :
    16 ≤ astarThreshold Bpubv zR lq2 s clU0 ∧
      Bpubv ≤ astarThreshold Bpubv zR lq2 s clU0 ∧
      zR ≤ astarThreshold Bpubv zR lq2 s clU0 ∧
      lq2 ≤ astarThreshold Bpubv zR lq2 s clU0 ∧
      s ≤ astarThreshold Bpubv zR lq2 s clU0 ∧
      clU0 ≤ astarThreshold Bpubv zR lq2 s clU0 := by
  unfold astarThreshold
  omega

/-- **`eq:P0-growth`, first row** (`06:495`): `P_0 <= (C_0 + 3) A_*`.

The recorded chain of `06:473--493`, carried out step by step on the banked
`P0sched`: the six maximum projections, `D <= B_pub <= A_*`,
`(log_2 A_*)^2 <= A_*`, `a <= C_0 A_*`, `B_cap <= (C_0 + 1) A_*`,
`log_2 s + 1 <= A_*`, and finally the unfolding of `eq:Ccert`.  Every binder is
pinned to its own defining chain by an equation hypothesis, so no source-defined
quantity enters free. -/
theorem P0_le_mul_astar {C0 D Bpubv zR lq2 ls clU0 lA A P0v : ℕ}
    (hD : D ≤ Bpubv)
    (hA : A = astar (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hlA : lA = astarExp (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hP0 : P0v = P0sched
      (Ccert (StageOneInterlace.bCap D (MassRedistributionTail.aStage1 C0 lA))
        lq2 ls) (2 ^ ls) lq2 clU0 zR) :
    P0v ≤ (C0 + 3) * A := by
  set T := astarThreshold Bpubv zR lq2 (2 ^ ls) clU0 with hT
  obtain ⟨h16, hBp, hzR, hlq2, hs, hclU0⟩ := astarThreshold_branches Bpubv zR lq2 (2 ^ ls) clU0
  have hTA : T ≤ A := by rw [hA]; exact le_astar T
  have hApow : A = 2 ^ lA := by rw [hA, hlA, astar_eq_two_pow]
  have h4 : 4 ≤ lA := by
    rw [hlA]
    exact four_le_astarExp (le_trans h16 (le_refl T))
  -- `(log_2 A_*)^2 <= A_*`
  have hsq : lA ^ 2 ≤ A := by rw [hApow]; exact sq_le_two_pow h4
  -- `log_2 s + 1 <= A_*`
  have hpow_le : (2 : ℕ) ^ ls ≤ A := le_trans hs hTA
  have hls : ls ≤ lA := by
    rw [hApow] at hpow_le
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow_le
  have hlA1 : lA + 1 ≤ A := by
    have := DenseSynchronisation.self_lt_two_pow lA
    rw [hApow]
    omega
  have hls1 : ls + 1 ≤ A := by omega
  -- the remaining branches
  have hBpA : Bpubv ≤ A := le_trans hBp hTA
  have hzRA : zR ≤ A := le_trans hzR hTA
  have hlq2A : lq2 ≤ A := le_trans hlq2 hTA
  have hclU0A : clU0 ≤ A := le_trans hclU0 hTA
  have h16A : 16 ≤ A := le_trans h16 hTA
  have hDA : D ≤ A := le_trans hD hBpA
  -- `a <= C_0 A_*` and `B_cap <= (C_0 + 1) A_*`
  have haA : MassRedistributionTail.aStage1 C0 lA ≤ C0 * A := by
    rw [MassRedistributionTail.aStage1]
    exact Nat.mul_le_mul_left C0 hsq
  have hBcapA : StageOneInterlace.bCap D (MassRedistributionTail.aStage1 C0 lA) ≤ (C0 + 1) * A := by
    rw [StageOneInterlace.bCap]
    have : C0 * A + A = (C0 + 1) * A := by ring
    omega
  -- unfolding `eq:Ccert`
  have hCcertA : Ccert (StageOneInterlace.bCap D
      (MassRedistributionTail.aStage1 C0 lA)) lq2 ls ≤ (C0 + 3) * A := by
    rw [Ccert]
    have hexp : (C0 + 1) * A + A + A = (C0 + 3) * A := by ring
    omega
  -- every branch of `P_0`
  have hAmul : A ≤ (C0 + 3) * A := Nat.le_mul_of_pos_left A (by omega)
  have hbound : ∀ K : ℕ, 16 ≤ K → Ccert (StageOneInterlace.bCap D
        (MassRedistributionTail.aStage1 C0 lA)) lq2 ls ≤ K →
      (2 : ℕ) ^ ls ≤ K → lq2 ≤ K → clU0 ≤ K → zR ≤ K →
      P0sched (Ccert (StageOneInterlace.bCap D
        (MassRedistributionTail.aStage1 C0 lA)) lq2 ls) (2 ^ ls) lq2 clU0 zR ≤ K := by
    intro K k1 k2 k3 k4 k5 k6
    unfold P0sched
    omega
  rw [hP0]
  exact hbound ((C0 + 3) * A) (le_trans h16A hAmul) hCcertA
    (le_trans hpow_le hAmul) (le_trans hlq2A hAmul) (le_trans hclU0A hAmul)
    (le_trans hzRA hAmul)

/-- **The exponential form of `eq:P0-growth`.**

`P_0 <= 2^{log_2 A_* + bl(C_0 + 3)}`, the intermediate that both the second row
of `eq:P0-growth` and the whole of `eq:LP-PA-literal-dominance` are read off.
Uses only `C_0 + 3 < 2^{bl(C_0 + 3)}` -- the `02:282` inline
`Nat.clog 2 (C0 + 3 + 1)` together with `Nat.le_pow_clog` -- and
`A_* = 2^{log_2 A_*}`. -/
theorem P0_le_two_pow {C0 D Bpubv zR lq2 ls clU0 lA A P0v : ℕ}
    (hD : D ≤ Bpubv)
    (hA : A = astar (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hlA : lA = astarExp (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hP0 : P0v = P0sched
      (Ccert (StageOneInterlace.bCap D (MassRedistributionTail.aStage1 C0 lA))
        lq2 ls) (2 ^ ls) lq2 clU0 zR) :
    P0v ≤ 2 ^ (lA + Nat.clog 2 (C0 + 3 + 1)) := by
  have hmul := P0_le_mul_astar hD hA hlA hP0
  have hApow : A = 2 ^ lA := by rw [hA, hlA, astar_eq_two_pow]
  have hC0 : C0 + 3 ≤ 2 ^ Nat.clog 2 (C0 + 3 + 1) := by
    have h : C0 + 3 + 1 ≤ 2 ^ Nat.clog 2 (C0 + 3 + 1) :=
      Nat.le_pow_clog (by norm_num) _
    omega
  have hstep : (C0 + 3) * A ≤ 2 ^ Nat.clog 2 (C0 + 3 + 1) * 2 ^ lA := by
    rw [hApow]
    exact Nat.mul_le_mul_right _ hC0
  have hcomb : (2 : ℕ) ^ Nat.clog 2 (C0 + 3 + 1) * 2 ^ lA
      = 2 ^ (lA + Nat.clog 2 (C0 + 3 + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  omega

/-- **`eq:P0-growth`** (`06:494--499`), both rows:

`P_0 <= (C_0 + 3) A_*` and `L_P <= log_2 A_* + bl(C_0 + 3)`.

`06:500`: "Thus `P_0 = A_*^{O(1)}` and `L_P = O(log_2 A_*)`" --- the asymptotic
gloss is *not* claimed; the two exact integer rows are. -/
theorem P0_growth {C0 D Bpubv zR lq2 ls clU0 lA A P0v : ℕ}
    (hD : D ≤ Bpubv)
    (hA : A = astar (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hlA : lA = astarExp (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hP0 : P0v = P0sched
      (Ccert (StageOneInterlace.bCap D (MassRedistributionTail.aStage1 C0 lA))
        lq2 ls) (2 ^ ls) lq2 clU0 zR) :
    P0v ≤ (C0 + 3) * A ∧ LPwidth P0v ≤ lA + Nat.clog 2 (C0 + 3 + 1) := by
  refine ⟨P0_le_mul_astar hD hA hlA hP0, ?_⟩
  rw [LPwidth]
  exact Nat.clog_le_of_le_pow (P0_le_two_pow hD hA hlA hP0)

/-- **`eq:LP-PA-literal-dominance`** (`06:502--508`):

`P_0 <= 2^{(3 + bl(C_0 + 5)) A_*}` and `L_P <= (3 + bl(C_0 + 5)) A_*`.

`06:500--502`: "For the literal coefficient row the checker uses the
deliberately weaker integer consequence".  Weaker it is: the exponent bound is
`log_2 A_* + bl(C_0 + 3) <= (3 + bl(C_0 + 5)) A_*`, using `log_2 A_* <= A_*`,
`bl(C_0 + 3) <= bl(C_0 + 5)` and `A_* >= 1`. -/
theorem LP_PA_literal_dominance {C0 D Bpubv zR lq2 ls clU0 lA A P0v : ℕ}
    (hD : D ≤ Bpubv)
    (hA : A = astar (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hlA : lA = astarExp (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hP0 : P0v = P0sched
      (Ccert (StageOneInterlace.bCap D (MassRedistributionTail.aStage1 C0 lA))
        lq2 ls) (2 ^ ls) lq2 clU0 zR) :
    P0v ≤ 2 ^ ((3 + Nat.clog 2 (C0 + 5 + 1)) * A) ∧
      LPwidth P0v ≤ (3 + Nat.clog 2 (C0 + 5 + 1)) * A := by
  have hApow : A = 2 ^ lA := by rw [hA, hlA, astar_eq_two_pow]
  have hlAA : lA ≤ A := by
    have := DenseSynchronisation.self_lt_two_pow lA
    rw [hApow]
    omega
  have hApos : 1 ≤ A := by
    rw [hApow]
    exact Nat.one_le_two_pow
  have hblen : Nat.clog 2 (C0 + 3 + 1) ≤ Nat.clog 2 (C0 + 5 + 1) :=
    Nat.clog_mono_right 2 (by omega)
  have hexp : lA + Nat.clog 2 (C0 + 3 + 1) ≤ (3 + Nat.clog 2 (C0 + 5 + 1)) * A := by
    have h1 : Nat.clog 2 (C0 + 5 + 1) ≤ Nat.clog 2 (C0 + 5 + 1) * A :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (3 + Nat.clog 2 (C0 + 5 + 1)) * A
        = 3 * A + Nat.clog 2 (C0 + 5 + 1) * A := by ring
    omega
  have hpow := P0_le_two_pow hD hA hlA hP0
  have hmono : (2 : ℕ) ^ (lA + Nat.clog 2 (C0 + 3 + 1))
      ≤ 2 ^ ((3 + Nat.clog 2 (C0 + 5 + 1)) * A) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  refine ⟨le_trans hpow hmono, ?_⟩
  rw [LPwidth]
  exact Nat.clog_le_of_le_pow (le_trans hpow hmono)

/-- **Canonical inhabitation (`eq:P0-growth` and
`eq:LP-PA-literal-dominance` at the fully evaluated schedule point).**

Every source-defined input is supplied by its own defining chain and none by a
numeral or a free binder: `B_pub` by `06:49`, `z_R` by `06:51--54`, `s` by
`eq:s-choice` -- the exponent `ls = B_s u^2` is exactly the banked
`sScale_eq_pow` readout of `06:118`, so `2^{ls} = sScale B_s u` -- `log_2 q_2`
by the banked guarded-source width `GuardedSourceSlab.q2`, `ceil(log_2 U_0)` by
`06:296` through the banked least-power-of-two exponent, `A_*` by
`eq:Astar-choice`, `a` by `eq:stage1-scales`, `B_cap` by `07:156` and `C_cert`
by `eq:Ccert`.  Only the public inputs `D`, `Y`, `m_R`, `n_R`, `b_out`, the
configuration fields `C_0`, `B_s`, the auxiliary depth `u` and the source
scalars inside `eta_R` remain symbolic --- exactly the freedom `06:56--69`
grants.  The premise `D <= B_pub` of `06:480` is **discharged** here rather than
assumed. -/
theorem P0_growth_at_scheduled_point {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E)
    {C0 D Y mR nR Bs uA bout : ℕ} {eR : ℝ}
    {Bpubv zR lq2 ls clU0 lA A P0v : ℕ}
    (hBpubv : Bpubv = Bpub D Y)
    (hzRv : zR = zRpub mR nR)
    (hlsv : ls = Bs * uA ^ 2)
    (hlq2v : lq2 = Nat.log 2 (q2 G (sScale Bs uA)))
    (hclU0v : clU0 = leastPowTwoExp (U0sched bout eR))
    (hA : A = astar (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hlA : lA = astarExp (astarThreshold Bpubv zR lq2 (2 ^ ls) clU0))
    (hP0 : P0v = P0sched
      (Ccert (StageOneInterlace.bCap D (MassRedistributionTail.aStage1 C0 lA))
        lq2 ls) (2 ^ ls) lq2 clU0 zR) :
    P0v ≤ (C0 + 3) * A ∧ LPwidth P0v ≤ lA + Nat.clog 2 (C0 + 3 + 1) := by
  refine P0_growth ?_ hA hlA hP0
  rw [hBpubv, Bpub]
  exact le_max_left D Y

/-! ## Section 8  `eq:tref-growth` (`06:580--584`) -/

/-- **Aux T1 (`eq:tref-search`, `06:569`).**  `log_2 t_ref = k_ref`: the width
returned by the banked least search is `2^{k_ref}`, so its exponent readout is
exact.  General. -/
theorem log_tref_eq_kref (cseed LP t0clog Ccertv lq Lth : ℕ) :
    Nat.log 2 (tref cseed LP t0clog Ccertv lq Lth)
      = kref cseed LP t0clog Ccertv lq Lth := by
  rw [tref, Nat.log_pow (by norm_num)]

/-- **Aux T2 (`06:610--612`).**  "Since `c_seed = 100`, the middle lower bound
`c_seed L_P^2` in `eq:tref-search` equals `k_ref^*`."  The identification as a
checked equation. -/
theorem krefStar_eq_cSeed_mul (LP : ℕ) : krefStar LP = cSeed * LP ^ 2 := rfl

/-- **`eq:tref-growth`** (`06:580--584`), in the only exact form the frozen text
supplies for it:

`log_2 t_ref <= k_ref^* = c_seed L_P^2`.

`06:578--579`: "The fixed choice `c_seed = 100`, together with the
symbolic-`A_wrap` cutoff proof in `thm:eff-ledger`, gives `log_2 t_ref =
O(L_P^2)`."  The asymptotic assertion needs that cutoff proof and is **not**
claimed; what is claimed is the explicit-constant bound at the tested endpoint
`eq:kref-tested-endpoint`, obtained from the banked `kref_le_star`.

The four conclusions of `eq:kref-fixed-persistence` (`06:598--608`) enter as
**explicit named hypotheses** --- the persistent-cutoff records
`KREF-LOWER-2P19`, `KREF-LOWER-T0`, `KREF-EXP-WIDTH`, `KREF-J49-WIDTH`, whose
own derivations belong to `sec:effective-cutoff`.  `06:628--629`: "Neither the
returned value nor a growth assertion about it proves termination." -/
theorem tref_growth_at_tested_endpoint {LP t0clog Ccertv lq Lth : ℕ}
    (hrec1 : (2 : ℕ) ^ 19 ≤ krefStar LP)
    (hrec2 : t0clog ≤ krefStar LP)
    (hrec3 : Ccertv - 1 + lq + Lth ≤ 2 ^ (krefStar LP - 1))
    (hrec4 : Ccertv - 1 + krefStar LP + Lth ≤ 2 ^ jrefStar LP) :
    Nat.log 2 (tref cSeed LP t0clog Ccertv lq Lth) ≤ krefStar LP := by
  rw [log_tref_eq_kref]
  exact kref_le_star hrec1 hrec2 hrec3 hrec4

/-- **Canonical inhabitation (`eq:tref-growth` at the schedule's own width
exponent).**

The same bound with `L_P` supplied by its defining display `06:471`
(`L_P = clog_2(P_0)`, the banked `LPwidth`) rather than as a free natural, so
the growth statement is about the schedule's own `L_P` and not about an
arbitrary exponent.  The four persistence records remain named hypotheses. -/
theorem tref_growth_at_scheduled_width {P0v t0clog Ccertv lq Lth : ℕ}
    (hrec1 : (2 : ℕ) ^ 19 ≤ krefStar (LPwidth P0v))
    (hrec2 : t0clog ≤ krefStar (LPwidth P0v))
    (hrec3 : Ccertv - 1 + lq + Lth ≤ 2 ^ (krefStar (LPwidth P0v) - 1))
    (hrec4 : Ccertv - 1 + krefStar (LPwidth P0v) + Lth
      ≤ 2 ^ jrefStar (LPwidth P0v)) :
    Nat.log 2 (tref cSeed (LPwidth P0v) t0clog Ccertv lq Lth)
      ≤ krefStar (LPwidth P0v) :=
  tref_growth_at_tested_endpoint hrec1 hrec2 hrec3 hrec4

/-! ## Section 9  `eq:cover-instance-tested-endpoints` (`06:682--693`)

`06:694--696`: "Their numerator/denominator binary-length rows and their
coefficient-pass majorant IDs are part of `L_sched(c)`; a search row without all
three fields is rejected."  The three stored endpoint *values* are named here;
the generic Bernoulli proof they instantiate is the banked
`cover_tested_endpoint`. -/

/-- **`B_ref^* = 25 bl(den theta)`** (`eq:cover-instance-tested-endpoints`,
first row, `06:684--685`), at the reference base `18/25 = rho_small`. -/
def BrefStar (denTheta : ℕ) : ℕ := 25 * Nat.clog 2 (denTheta + 1)

/-- **`B_sing^* = den(1 - eta_C) bl(den theta)`**
(`eq:cover-instance-tested-endpoints`, second row, `06:686--688`), at the
singleton base `1 - eta_C` of `06:698--700`.  The denominator code of the base
is an **explicit binder**: `eta_C` depends on `s` and `delta_v(G)`, so it is not
a fixed numeral (see GAP-EXPOSED). -/
def BsingStar (denBase denTheta : ℕ) : ℕ := denBase * Nat.clog 2 (denTheta + 1)

/-- **`B_pair^* = 100 bl(den theta)`** (`eq:cover-instance-tested-endpoints`,
third row, `06:689--690`), at the pair base `99/100 = rho_pair`. -/
def BpairStar (denTheta : ℕ) : ℕ := 100 * Nat.clog 2 (denTheta + 1)

/-- **Aux C1 (the endpoints are nondegenerate).**  Each stored endpoint is at
least one, which is the third row of `eq:cover-tested-endpoint` (`06:669`) that
the banked `SCHEDULE-001` row deliberately does not export.  General for a
positive denominator code and a threshold denominator at least one. -/
theorem one_le_BrefStar {denTheta : ℕ} (h : 1 ≤ denTheta) : 1 ≤ BrefStar denTheta := by
  have hc : 0 < Nat.clog 2 (denTheta + 1) := Nat.clog_pos (by norm_num) (by omega)
  rw [BrefStar]
  omega

/-- **Aux C2.**  Likewise for the pair endpoint.  General. -/
theorem one_le_BpairStar {denTheta : ℕ} (h : 1 ≤ denTheta) : 1 ≤ BpairStar denTheta := by
  have hc : 0 < Nat.clog 2 (denTheta + 1) := Nat.clog_pos (by norm_num) (by omega)
  rw [BpairStar]
  omega

/-- **Aux C3.**  Likewise for the singleton endpoint, at a legal denominator
code.  General. -/
theorem one_le_BsingStar {denBase denTheta : ℕ} (hb : 1 ≤ denBase)
    (h : 1 ≤ denTheta) : 1 ≤ BsingStar denBase denTheta := by
  have hc : 0 < Nat.clog 2 (denTheta + 1) := Nat.clog_pos (by norm_num) (by omega)
  rw [BsingStar]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- **Canonical inhabitation (`eq:cover-instance-tested-endpoints`, rows one and
three, at the schedule's own row threshold).**

`06:539`: "Here `1/theta = 160 Q` is an integer because `delta = 1/10`", so
`den(theta) = 160 Q` at the banked bridge width `Q = Qwidth`.  Both numeric-base
rows fire there, with the two cover numbers the banked `coverExponent` at the
frozen bases `rho_small = 18/25` and `rho_pair = 99/100`.  No numeral is
assigned to `Q`. -/
theorem cover_instance_tested_endpoints (bout : ℕ) (δU : ℝ) :
    coverExponent rhoSmall (theta (Qwidth bout δU))
        ≤ BrefStar (160 * Qwidth bout δU) ∧
      coverExponent rhoPair (theta (Qwidth bout δU))
        ≤ BpairStar (160 * Qwidth bout δU) := by
  have hQ : 0 < Qwidth bout δU := Nat.two_pow_pos _
  exact ⟨Bref_le_tested hQ, Bpair_le_tested hQ⟩

/-- **`eq:cover-instance-tested-endpoints`, middle row (`06:686--688`)
--- GAP-EXPOSED.**

`B_sing^* = den(1 - eta_C) bl(den theta)` really is a tested endpoint for the
singleton least search, *given* the reduced-fraction datum for the base.  Since
`den(1 - eta_C)` is not a fixed numeral, that datum is an explicit hypothesis:
`1 - eta_C = a/b` with `0 < a < b`.  The banked `one_sub_etaC_legal` certifies
`0 < 1 - eta_C < 1`, so the hypothesis is consistent; computing `a` and `b` is
the literal coefficient pass of `sec:effective-cutoff` and is not done here. -/
theorem BsingStar_tested {a b Q : ℕ} {eC : ℝ} (ha : 0 < a) (hab : a < b)
    (hQ : 0 < Q) (hbase : (1 : ℝ) - eC = (a : ℝ) / (b : ℝ)) :
    coverExponent (1 - eC) (theta Q) ≤ BsingStar b (160 * Q) := by
  have hclog : 0 < Nat.clog 2 (160 * Q + 1) := Nat.clog_pos (by norm_num) (by omega)
  have hθ : theta Q = (1 : ℝ) / ((160 * Q : ℕ) : ℝ) := by
    rw [theta_eq_delta, deltaFixed_eq]
    push_cast
    field_simp
    norm_num
  have hend := cover_tested_endpoint (a := a) (b := b) (u := 1) (v := 160 * Q)
    ha hab (le_refl 1) (by omega)
  refine coverExponent_le ?_ ?_
  · exact one_le_BsingStar (by omega) (by omega)
  · rw [hbase, hθ, BsingStar]
    simpa using hend

/-- **Canonical inhabitation (the middle row at the schedule's own bridge
width).**

`Q` is supplied by the banked `EntryGates.Qwidth` -- "the least power of two at
least `Q_0`" of `eq:Q-theta-choice` (`06:532`) -- rather than as a free natural,
so `den(theta) = 160 Q` is the schedule's own denominator and the positivity of
the width is discharged rather than assumed. -/
theorem BsingStar_tested_at_bridge_width {a b : ℕ} {eC : ℝ} (bout : ℕ) (δU : ℝ)
    (ha : 0 < a) (hab : a < b)
    (hbase : (1 : ℝ) - eC = (a : ℝ) / (b : ℝ)) :
    coverExponent (1 - eC) (theta (Qwidth bout δU))
      ≤ BsingStar b (160 * Qwidth bout δU) :=
  BsingStar_tested ha hab (Nat.two_pow_pos _) hbase

/-! **The legality premises of the middle row are not restated here.**

`06:658--661` requires `0 < 1 - eta_C < 1` before the singleton least search may
run at the base `rho_* = 1 - eta_C` (`06:698--700`), so the reduced-fraction
datum `BsingStar_tested` asks for is consistent rather than vacuous.  That fact
is the banked `ParameterSchedule.one_sub_etaC_legal` at the frozen side
conditions `3 < s` and `0 < delta_v(G)`; a consumer takes it from there by
fully qualified pin, and this module does not wrap it. -/

end EthInapproximability.ParameterizedNP.ScheduleTemplateResidue
