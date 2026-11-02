import EthInapproximability.ParameterizedNP.WrapperLowRungAssembly

/-!
# Parameterized NP route: the reference construction at the `09:311--327` call

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:109--119`, the reference row family and the reference matrix.**
      "Write `m = |Rows(N)|`.  The base-column reservoir of `A` becomes a
      uniformly duplicated row family of `N`; define
      `R_G = {base} x Omega x [w_0] subseteq Rows(N)`,
      `G = N|_{R_G x Cols(N)}`, `m_G = |Rows(G)|`, `g = m_G/m = 91/92`."
      Built already, as `ScaleAlignOpening.refIncl` and `.referenceG`, and
      consumed here **by pin**.
    * **`eq:reference-all-columns` (label `09:123`, display `09:121--124`),**
      `Cols(G) = Cols(N)`, with its motivation `09:125--127`: "This equality is
      why the reference can follow every actual Bob restriction of the
      scale-alignment protocol: no auxiliary projection or reduced column
      alphabet is involved."  This is the clause `09:325` cites to verify the
      orientation of the certified call, and in Lean it is the *type* of
      `referenceG`, not a hypothesis about it.
    * **`lem:wrapper-reference` (label `09:152`, statement `09:151--162`).**
      "Under `eq:hard-seed-width-gates` and `eq:reference-profile-gates`, assume
      the exact protected Stage-4 identity `comp N = C` from
      `cor:exact-protected-stage4`.  In the `NO` case, `comp G = C`,
      `Lambda_3(G,1,x_T,y) >= C - 1`."  Its three-rung clause, at the schedule's
      own `y`, is the banked `ScaleAlignOpening.wrapperReference_rungs`; §2 below
      fires it at `y = y_*` and discharges its nonemptiness side condition, which
      is what turns it into `eq:certified-base`.
    * **`09:241`**, inside `thm:first-wrapper`'s hypothesis list: "the exact
      identity `comp N = C`" -- the reading of `C` used throughout, and the one
      `eq:Ccert` (`06:430--437`) identifies with `C_cert` in the `NO` case.
    * **`09:240`**, "Assume `C >= 3`" -- the ambient guard supplying `A:111`'s
      `H >= 2` at `H = C - 1`.
    * **`09:277--283`**, "Fix `j in {0,1,2}`, and put `kappa_j = q/2^j`" -- the
      frozen rung range and the frozen capacity, consumed by pin from the banked
      `WrapperLowRungs.kappaLow`.
    * **`09:311--313`**, "Project the retained outer column set to any
      `9 kappa_j/16` such coordinates.  Its normalized density remains at least
      `theta`, by specified-coordinate projection." -- the block count of the
      restriction the call is made at.  `refBlockCount_eq_certifiedPt_kappa`
      proves that `A:138`'s demand `r' p_{t_ref}` *is* that number.
    * **`09:313--323`, the substitution display** (`M = G` on `09:318`,
      `t = t_ref` on `09:319`, `r = q/t_ref` on `09:320`,
      `r' = kappa_j/t_ref` on `09:321`, `eps = 0, h = theta, a^sharp = 0` on
      `09:322`), registered in Lean as the banked
      `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall` and consumed
      here **by pin**; §1 reifies its three width quantities.
    * **`09:325--327`, the legality paragraph.**  "The equality
      `eq:reference-all-columns` verifies the orientation; the reference
      restriction is a full product, so its balancedness error is exactly zero;
      and `q/4 >= t_ref` makes all three values of `r'` legal."  All three
      clauses are derived in §5, in that order.
    * `09:328--331`, "The conclusion is precisely
      `comp<U,1,y_*/2^j,theta> >= C + log_2 q - 1 - j`", and `09:333`, "This
      proves `eq:wrapper-u-low`" -- the target §6 composes into.
    * `eq:wrapper-low-simple-gate` (label `09:306`, display `09:304--307`),
      `q x_T <= 4/25025`.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    * **`eq:certified-base` (label `A:115`, display `A:113--116`),**
      `Lambda_3(M,1,x,y_*) >= H` -- the clause §2 lands at the reference
      construction, at `M = G`, `x = x_T`, `H = C - 1`.
    * `A:111--112` (the ambient guards), `A:117--118` (the width binder),
      `A:120` (`p_t = 9t/16`), `A:125` (the copy binders), `A:126--128` (the
      family clause, whose `eps = 0` branch `09:326` selects), `A:128--129`
      (`h in (0,1]`, `a^sharp in {0,1}`), `A:138--141` (the restriction bundle)
      and `eq:certified-E3` (`A:142--145`).  **Nothing here restates any of
      them**: the whole interface is the banked
      `CertifiedLocalizedExtension.CertifiedExtensionEndpoint`, entered only
      through `CanonicalReferenceStoppingCall`.
    * `A:16--18` (`y_* = 3/5`) and `A:104--107` (`t_0(3/5)` means the single
      integer `t_cert`), consumed by pin as `CertifiedLocalizedExtension.yStar`
      and `.tCert`.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    * **`eq:tref-search` (display `06:557--572`, label `06:571`)**, whose closing
      clause `06:568--569` is the **defining display of the reference width**,
      `t_ref = 2^{k_ref}`.  `tRef` reifies exactly that display.  Its first
      clause `06:561--563` is the floor term `clog_2(t_0(3/5)) <= k_ref` carried
      as `hfloor`; its second and third clauses `06:564--567` are the two side
      legs, already authored as `WrapperLowRungAssembly.certifiedE1_of_trefSearch`
      and `.certifiedE2_of_trefSearch` and consumed here by pin.
    * **`06:908--920`**, the wrapper's own substitution of the schedule's `y`:
      "For the first wrapper put `hat beta_j = ((3/5)/2^j + lambda_T - 1)/lambda_T`",
      and **`06:921--924`**, "For the outer wrapper put `kappa_j = q/2^j`,
      `beta_j = ((3/5)/2^j - 1/92)/(91/92)`".  These are the displays that fix
      the wrapper's `y` to the literal `3/5`, i.e. to `A:18`'s `y_*`; that is why
      §2 may fire the `y`-general `wrapperReference_rungs` at `yStar` and obtain
      `eq:certified-base` rather than a neighbouring statement.  `09:314--315`
      ("using its fixed `y_* = 3/5`") and `09:330` (the conclusion at
      `y_*/2^j`) are the same identification read at the call.
    * `eq:Ccert` (`06:430--433`) with `06:435--437`, "In a `NO` instance it
      equals the exact complexity `C` of the protected Stage-4 transpose" -- the
      identification that lets the two schedule legs be stated at the single
      natural `C`, recorded rather than performed silently.
    * `eq:kref-tested-endpoint` (`06:586--590`), `k_ref^* = 100 L_P^2`,
      `j_ref^* = 4 L_P` -- the paper's own **closed-form** tested endpoint, the
      only values at which the joint non-vacuity instance of §7 is exhibited.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`),
    `08:166`, the defining display `x_T = 2^{-b_T}` of the auxiliary Stage-2
    depth density (`08:288`, "the auxiliary `(1/10,b_T)`-robustness certificate
    established at Stage~2"; likewise `09:211--212`) -- banked as
    `DenseStageFourOpening.xTdepth` and consumed by
    pin.  No numeral is ever put in its place.
  * `02-mechanical-contract.tex`
    (SHA-256 `019209B4EDF21015507148310EFBED757A83FD7709CF3880E178A4C535097A3D`),
    `02:852--858`, the paper's own use of the `j_49` eliminator at the tested
    endpoint.  The paper prints that arithmetic twice -- here and at
    `eq:kref-j49-candidate` (`06:615--621`) -- and the Lean owner takes the `06`
    print: it is the banked `ParameterSchedule.kref_j49_candidate`
    (`ParameterSchedule.lean:1360`) over `krefStar` / `jrefStar` (`:1349`,
    `:1353`), stated in the banked predicate `RawLowProfileBody.J49Feasible` and
    consumed by pin.  (`WrapperLowRungAssembly`'s parallel
    `j49Feasible_at_tested_endpoint` was a statement-identical duplicate of that
    owner and was deleted at the `cc-t7z-r1` gate.)
* **Cited external interfaces.**  `EXPANDER-001` (`lem:cited-expander-family`)
  has **no** Lean declaration by design and occurs in no hypothesis here:
  `A:126--128`'s balanced family enters only through the `eps` legality
  disjunction, and `09:326` selects its *other* branch -- the exact full product,
  `eps = 0` -- which is why `referenceEps_is_the_full_product_branch` is a proof
  and not an assumption.  `LegacyNPCC.Stage12`, whose closure reaches the cited
  AGHP balanced-family axiom, is **not** imported, directly or transitively.  No
  new `axiom`, no opaque certificate, no unproved placeholder.

## What is consumed by pin, and what is authored

**Consumed by pin, never restated:**

* `ScaleAlignOpening.referenceG`, `.refIncl`, `.referenceG_follows_bob`,
  `.card_refRows`, `.wrapperReference_rungs`, `.wrapperReference_bracket_nonempty`,
  `.xTdepth_mem` -- the reference construction and `lem:wrapper-reference`.
* `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall`, `.CertifiedE3`,
  `.tCert`, `.yStar`, `.clog_two_tCert`, `.epsBranch_bounds`,
  `.canonicalCall_gates` -- the registered `09:313--323` substitution and its
  integer legality.
* `WrapperLowRungAssembly.certifiedE3_at_lowRung`,
  `.wrapperLowRungs_of_canonicalCall`, `.certifiedE1_of_trefSearch`,
  `.certifiedE2_of_trefSearch` -- the block wiring and the two schedule legs.
  The `j_49` feasibility predicate itself is the banked
  `RawLowProfileBody.J49Feasible` (`06:88--90`), consumed by pin, and its
  tested-endpoint inhabitation is the banked
  `ParameterSchedule.kref_j49_candidate` (`eq:kref-j49-candidate`,
  `06:615--621`); the former parallel `WrapperLowRungAssembly.IsJ49Candidate`
  was a statement-identical duplicate of the predicate and has been excised, its
  name barred, and the former parallel
  `WrapperLowRungAssembly.j49Feasible_at_tested_endpoint` was a
  statement-identical duplicate of the inhabitation owner and has been deleted.
* `WrapperLowRungs.kappaLow`, `.kappaLow_mul_tRef`.
* `RestrictionDatum.RestrictionDatum`, `.certifiedPt`, `.certifiedRowFloor`,
  `.certifiedColFloor`, `.representedBlocks`, `.sixteen_mul_certifiedPt`,
  `.sixteen_dvd_two_pow`, `.certifiedPt_pos`, `.certifiedRowFloor_le`,
  `.nonempty_restrictionDatum`.
* `DenseStageFourOpening.xTdepth`, `.cBlock`, `.dTwoBlock`.

**Authored here** (and nowhere else in `src/`):

1. the three width quantities of the substitution display -- `tRef`
   (`06:568--569`), `refOuterCopies` (`09:320`), `refRungCopies` (`09:321`) --
   reified as definitions tracing their defining displays, with the two identities
   `q = r t_ref` and `r' t_ref = kappa_j` that make the endpoint's output exponent
   the frozen `log_2 kappa_j`;
2. **`eq:certified-base` at the reference construction** -- `referenceCertifiedBase`
   -- `lem:wrapper-reference`'s three-rung clause fired at the schedule's own
   `y = 3/5 = y_*`, with the bracket nonemptiness discharged outright;
3. **the reference restriction as an explicit full product** (`09:326`) --
   `productRestriction` and its four readouts, plus `referenceRestriction`, the
   same object at the canonical indices `r' = kappa_j/t_ref`, `t = t_ref`,
   `a^sharp = 0`, `x = x_T`, `h = theta`;
4. the block-count identity `r' p_{t_ref} = p_{kappa_j} = 9 kappa_j/16` of
   `09:311`, and the row floor read at `m_G` rather than at a free natural;
5. the three legality clauses of `09:325--327`, each derived;
6. the canonical instance: `certifiedE3_at_referenceConstruction` and
   `wrapperLowRungs_at_referenceConstruction`, in which every antecedent of the
   endpoint except the endpoint implication itself is *proved* at the built data.

## What is NOT done here, stated exactly

* **The endpoint implication is not proved, and no route completion is claimed.**
  `CanonicalReferenceStoppingCall G C k_q k_ref j x_T theta Dat val` unfolds to
  `CertifiedExtensionEndpoint ...`, which is the *conditional*
  `A:111--141 -> eq:certified-E3`.  Inhabiting it outright is proving
  `thm:certified-localized-extension` (`A:109--146`) at this data, i.e. the whole
  of `A:147` onward, which is a separate obligation and is untouched.  It
  therefore remains a **named binder** (`hcall`) in every headline below.  What
  this tranche removes is the *other* half of the deferral: the ledger recorded
  that inhabitation "needs `G`, `x_T`, `theta` and the routed restriction of the
  reference family, none of which is built".  `G` and `x_T` are now the banked
  construction, `theta` is the schedule's own real carried with `A:128`'s guards,
  the restriction is *built* as `09:326`'s full product, and `eq:certified-base`
  -- the one hypothesis of the endpoint that is a statement about `G` itself --
  is **proved** rather than assumed.
* **The canonical-inhabitation obligation on
  `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall` stays REGISTERED
  and DEFERRED**, against `CERTIFIED-LOCALIZED-EXTENSION-001`, and is narrowed by
  this tranche to exactly one residue: the frozen appendix proof.  It is not
  discharged, and no probe stands in for it.  No declaration below inhabits the
  call, and none is labelled as doing so.
* **The routing is not built.**  `09:326` says the reference restriction is a
  full product, and that is the object `referenceRestriction` is; the *selection*
  of which outer coordinates and which reference rows the frontier routing hands
  the call at a given member of `<U,1,y/2^j,theta>` is the content of
  `sec:wrapper-dense-frontier` and after, and enters here only as the data
  arguments `S`, `T`, `K` and as the still-open `hrung` binder of §6.
* **`hDenseRung` is untouched.**  `eq:wrapper-u-dense` (`09:262--263`) is the
  content of `09:335--1781`; nothing here concludes it, weakens it, or feeds it.
* **Branch 1 of the terminal two-stream dispatch is not touched.**  `09:1014--1019`
  invokes the *inherited* Localized Extension corollary at the fixed physical
  width `t_2`, which `A:4--8` records is a different theorem; it is stated
  nowhere here.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/A-stage4-details.tex`
(SHA-256 `5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`),
opened first-hand this tranche.  **No reader item is claimed here**, and the
survey that establishes that is:

* `eq:paper-reference-profile` (label line 233, display lines 230--234) is the
  reader's one numbered statement about the all-column reference, and all three
  of its clauses are **already assigned**: `Cols(G_0) = Cols(N)` (line 231) to
  `ScaleAlignOpening.referenceG_follows_bob`, `comp G_0 = C` (line 231) to
  `.D_referenceG` with `.D_referenceG_frozen`, and
  `Lambda_{G_0}(1,x_T,3/5) >= C - 1` (line 232) to `.wrapperReference_rungs` and
  `.wrapperReference`.  `referenceCertifiedBase` is a *firing* of the third of
  those at `y = y_*`, not a second statement of it, so reclaiming line 232 here
  would be a double assignment, which the reader-counterpart rule bars.
* Line 229 ("There is an explicitly ordered all-column submatrix `G_0 ⊆ N`
  with") and line 235 ("where `x_T = 2^{-b_T}` is the auxiliary Stage-2 depth")
  are unnumbered connective prose around that display; citing prose as a
  statement counterpart is barred, and `x_T`'s defining display is in any case
  the autoformalization's `08:166`, already carried by the banked
  `DenseStageFourOpening.xTdepth`.
* Lines 361--368 (the reader's rung display
  `D_U(1; 3/(5.2^j), theta) >= C + r_q - 1 - j`) are the reader counterpart of
  `eq:wrapper-u-low` and are **already assigned** to
  `WrapperLowRungs.wrapperLowRungs`; `WrapperLowRungAssembly`,
  `DenseWrapperFrontier`, `TwoStreamState`, `TerminalFixedBin`,
  `TerminalStageThreeLift`, `TerminalTwoStream` and `Stage3ProtocolRouting` all
  record the same assignment.  Lines 361--364 ("retain the reference portion of
  each outer copy and use block balancing ... Localized Extension applied to
  `eq:paper-reference-profile` yields") are the proof recipe, unnumbered prose
  inside a proof body; `FirstWrapperAssembly` already records line 363 as a
  declined near miss on exactly those grounds.
* Lines 371--373 ("the all-column reference follows every Bob query and its
  one-bit-down certificate prevents an early cheap termination") are the dense
  rung's proof prose, barred on the same ground and in any case the content of
  `hDenseRung`, which is untouched.
* The reader's own Localized Extension statement,
  `cor:paper-localized-extension`
  (`reader-facing/sections/02-preliminaries.tex:512--527`), is the
  **uncertified** corollary -- no `t >= t_cert`, no `h_t`, no
  `eq:certified-E1/E2` -- and `WrapperLowRungs` already records why citing it for
  the certified endpoint would be a false counterpart.  The same reasoning
  applies verbatim here.
* The reader prints no `t_ref`, no `k_ref`, no `p_t`, no restriction datum, no
  block count and no full-product clause at all, so the declarations below carry
  their autoformalization anchors alone.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the three width quantities of `09:319--321`, general (5): `tRef_pos`,
  `refOuterCopies_mul_tRef`, `refRungCopies_mul_tRef`,
  `refRungCopies_le_refOuterCopies`, `refBlockCount_eq_certifiedPt_kappa`; plus
  the three `rfl` reification readouts `tRef_eq`, `refOuterCopies_eq`,
  `refRungCopies_eq`, which certify that each definition is its defining display
  and nothing else.
* `B` `eq:certified-base` at the reference thread, general (2): `yStar_mem`,
  `referenceCertifiedBase`.
* `C` the full-product restriction of `09:326`, general (5):
  `representedBlocks_product`, `productRestriction_selCard`,
  `productRestriction_rowsPerBlock`, `productRestriction_colDens`,
  `referenceRowFloor_at_mG`.
* `D` the three legality clauses of `09:325--327`, general (3):
  `referenceEps_is_the_full_product_branch`, `referenceEps_denominator_bounds`,
  `referenceRung_legality_at_all_three`.
* `E` the canonical instance, general (3): `certifiedE3_at_referenceConstruction`,
  `wrapperLowRungs_at_referenceConstruction`, `certifiedE3_at_referenceG`.
* `F` statement poles (3): `productRestriction_rejects_empty_rows`,
  `refBlockCount_needs_the_width_divisibility`,
  `referenceCertifiedBase_is_not_free`.
* `G` LANE-GATE 3 non-vacuity at paper-derived values (4):
  `simple_gate_at_xTdepth`, `exists_lTheta_for_density`,
  `referenceRestriction_nonempty`, `referenceCall_full_gate_set_is_satisfiable`.

That is **25 battery entries proved** plus the three reification readouts, with
`0` unproved, of which three are statement poles and four are non-vacuity
results at paper-derived values -- two of them stated over a *range* rather than
at a point, because the quantities involved (`b_T`, `theta`) are ones the frozen
schedule defines, and the last putting the restriction, the integer gates, the
density leg and both schedule legs at **one** reference width, at the paper's own
closed-form tested endpoint `k_ref^* = 100 L_P^2`, `j_ref^* = 4 L_P`.

The module has **33** source declarations in all: 5 definitions (`tRef`,
`refOuterCopies`, `refRungCopies`, `productRestriction`, `referenceRestriction`,
none of them `noncomputable`) and 28 theorems, with **0** `structure`s, **0**
`inductive`s, **0** `abbrev`s, **0** `instance`s and **0** `axiom`s.

## Canonical inhabitation

**No new `structure` is declared here**, so this tranche creates no new
inhabitation obligation.  The types it *builds into* are two, and both are
handled explicitly:

* `RestrictionDatum.RestrictionDatum` at the `09:313--323` indices.  The paper
  does instantiate it -- `09:311--312` and `09:326` describe exactly this object
  -- and `referenceRestriction` is that instantiation as a term, with
  `referenceRestriction_nonempty` showing the index tuple is inhabited at legal
  parameters and `refBlockCount_eq_certifiedPt_kappa` showing its block count is
  the frozen `9 kappa_j/16` rather than a number of ours.  The banked
  `RestrictionDatum.datum_consistent_with_frozen_side_conditions` is at the *other*
  certified site (`09:1272--1273`, `a^sharp = 1`) and is not reused for this one.
* `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall`.  Its inhabitation
  is the frozen appendix theorem and stays **registered and deferred**, as set
  out above.  Nothing below is a probe for it: it appears only as the binder
  `hcall`, and there is no synthetic inhabitant and no conditional shell dressed
  up as a discharge.

## Proof status and axiom surface

Adapted (the frozen construction, in the frozen order) plus new (the full-product
restriction and the `y = y_*` firing).  Imports:
`EthInapproximability.ParameterizedNP.WrapperLowRungAssembly` alone, whose
closure carries `CertifiedLocalizedExtension`, `WrapperLowRungs`,
`ScaleAlignOpening`, `HardSeedFacade`, `DenseStageFourOpening` and
`RestrictionDatum`.  `#print axioms` on every declaration below is recorded in
`tools/AxiomAudit.lean`; the surface is `propext`, `Classical.choice`,
`Quot.sound` only.

## HYPOTHESIS-CONSISTENCY note

The headline `certifiedE3_at_referenceConstruction` conjoins only hypotheses the
frozen text states about **one** case of **one** construction: `thm:first-wrapper`'s
`NO`-case guards (`09:240`, `09:241`, `09:259`), `lem:wrapper-reference`'s own
open binders at the reference row density (`09:151--162` with `09:196--218`),
`eq:wrapper-low-simple-gate` (`09:304--307`), `09:327`'s width legality, and the
three `eq:tref-search` clauses (`06:561--567`).  It is not the three branches of
the terminal dispatch and not the two promise cases; nothing assumes both a `YES`
and a `NO` clause.  Joint satisfiability is machine-checked at one width by
`referenceCall_full_gate_set_is_satisfiable`, which puts the restriction's
existence, `A:117`'s width gates, `09:327`'s legality, `eq:wrapper-low-simple-gate`
and both `eq:tref-search` side clauses at the paper's own tested endpoint
simultaneously.
-/

namespace EthInapproximability.ParameterizedNP.WrapperReferenceConstruction

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.HardSeedFacade
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension
open EthInapproximability.ParameterizedNP.WrapperLowRungAssembly

/-! ## §1  The three width quantities of the substitution display (`09:319--321`)

All three are quantities the frozen source **defines** -- `t_ref` by
`eq:tref-search`'s closing clause `06:568--569`, and the two copy counts by the
substitution display itself -- so all three are reified as Lean definitions
tracing their defining displays.  None is ever replaced by a numeral, and no
value below is obtained by searching for something that fits the locally visible
constraints. -/

section Widths

/-- **`t_ref = 2^{k_ref}` (`06:568--569`), reified.**

The closing clause of `eq:tref-search` is the *defining display* of the certified
reference width: after the three integer comparisons of `06:561--567` select
`k_ref`, the width is `t_ref = 2^{k_ref}`.  Every occurrence of the endpoint's
`t` at the `09:311--327` call is this expression, never an assigned numeral --
and none could be, since `A:117` forces `t_ref >= t_cert = 2^{2^20}`. -/
def tRef (kref : ℕ) : ℕ := 2 ^ kref

@[simp] theorem tRef_eq (kref : ℕ) : tRef kref = 2 ^ kref := rfl

/-- **`r = q/t_ref` (`09:320`), reified.**

At `q = 2^{k_q}` and `t_ref = 2^{k_ref}` the frozen quotient is the exponent
difference.  The natural subtraction is exact under `09:327`'s legality
`k_ref + 2 <= k_q`, which is where every consumer below fires it. -/
def refOuterCopies (kq kref : ℕ) : ℕ := 2 ^ (kq - kref)

@[simp] theorem refOuterCopies_eq (kq kref : ℕ) :
    refOuterCopies kq kref = 2 ^ (kq - kref) := rfl

/-- **`r' = kappa_j/t_ref` (`09:321`), reified.**

At the frozen capacity `kappa_j = q/2^j` (`09:280`) this is
`2^{k_q - j - k_ref}`; `09:327` ("`q/4 >= t_ref` makes all three values of `r'`
legal") is exactly the condition making the two natural subtractions exact for
every `j in {0,1,2}`. -/
def refRungCopies (kq kref j : ℕ) : ℕ := 2 ^ (kq - j - kref)

@[simp] theorem refRungCopies_eq (kq kref j : ℕ) :
    refRungCopies kq kref j = 2 ^ (kq - j - kref) := rfl

/-- **Aux A1 (the reference width is a positive natural).**  Needed wherever
`A:120`'s `p_t = 9t/16` must be positive and wherever the row floor is compared
with a carrier size.  General. -/
theorem tRef_pos (kref : ℕ) : 0 < tRef kref := pow_pos (by norm_num) kref

/-- **Aux A2 (`A:125`'s `q = r t` at the substitution), PROVED.**

`A:125` closes "put `q = rt`", and `09:319--320` substitutes `t = t_ref`,
`r = q/t_ref`.  The two therefore multiply back to the scale-alignment width
`q = 2^{k_q}` of `09:105--108` **identically**, not approximately.  The
hypothesis is the exact range in which the natural subtraction of
`refOuterCopies` is honest.  General in `k_q` and `k_ref`. -/
theorem refOuterCopies_mul_tRef {kq kref : ℕ} (h : kref ≤ kq) :
    refOuterCopies kq kref * tRef kref = 2 ^ kq := by
  rw [refOuterCopies_eq, tRef_eq, ← pow_add]
  congr 1
  omega

/-- **Aux A3 (`09:321` multiplies back to the frozen capacity), PROVED.**

`r' t_ref = (kappa_j/t_ref) t_ref = kappa_j`, in exponent form, under `09:327`'s
legality.  This is the identity that makes `eq:certified-E3`'s output exponent
`log_2(r' t)` the frozen `log_2 kappa_j` of `09:330--331`.  The banked
`WrapperLowRungs.kappaLow_mul_tRef` is the exponent computation and is consumed
by pin; what is added is that it is a statement about the two *reified*
substitution quantities.  General in `k_q`, `k_ref` and the rung index. -/
theorem refRungCopies_mul_tRef {kq kref j : ℕ} (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) :
    refRungCopies kq kref j * tRef kref = kappaLow kq j := by
  rw [refRungCopies_eq, tRef_eq]
  exact kappaLow_mul_tRef hj hq4

/-- **Aux A4 (`A:125`'s `r' <= r` at the substitution), PROVED.**

The rung copy count never exceeds the outer copy count, because `kappa_j <= q`.
General; no legality hypothesis is needed, since the natural subtraction only
shrinks the exponent further. -/
theorem refRungCopies_le_refOuterCopies (kq kref j : ℕ) :
    refRungCopies kq kref j ≤ refOuterCopies kq kref := by
  rw [refRungCopies_eq, refOuterCopies_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`09:311--312` as an identity: `A:138`'s demand is the frozen
`9 kappa_j/16`, PROVED.**

"Project the retained outer column set to any `9 kappa_j/16` such coordinates."
`A:138--139` demands exactly `r' p_t` represented outer blocks, and at the
`09:319--321` substitution that number **is** `p_{kappa_j} = 9 kappa_j/16`:
`r' p_{t_ref} = r' . 9 t_ref/16 = 9 (r' t_ref)/16 = 9 kappa_j/16`, with both
natural divisions exact because `16 | t_ref` and `16 | kappa_j` in the frozen
range.

So the block count of the restriction below is not a number chosen here; it is
the frozen count of `09:311`, reached by evaluating the substitution.  General in
`k_q`, `k_ref` and `j` at the frozen ranges. -/
theorem refBlockCount_eq_certifiedPt_kappa {kq kref j : ℕ} (hk : 4 ≤ kref)
    (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) :
    refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref)
      = RestrictionDatum.certifiedPt (kappaLow kq j) := by
  have hPt : RestrictionDatum.certifiedPt ((2 : ℕ) ^ kref) = 9 * 2 ^ (kref - 4) := by
    have hP : 16 * RestrictionDatum.certifiedPt ((2 : ℕ) ^ kref) = 9 * 2 ^ kref :=
      RestrictionDatum.sixteen_mul_certifiedPt (RestrictionDatum.sixteen_dvd_two_pow hk)
    have hsplit : (2 : ℕ) ^ kref = 16 * 2 ^ (kref - 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  have hPtK : RestrictionDatum.certifiedPt (kappaLow kq j) = 9 * 2 ^ (kq - j - 4) := by
    have hP : 16 * RestrictionDatum.certifiedPt (kappaLow kq j) = 9 * 2 ^ (kq - j) := by
      rw [kappaLow_def]
      exact RestrictionDatum.sixteen_mul_certifiedPt
        (RestrictionDatum.sixteen_dvd_two_pow (by omega))
    have hsplit : (2 : ℕ) ^ (kq - j) = 16 * 2 ^ (kq - j - 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  have hexp : (2 : ℕ) ^ (kq - j - kref) * 2 ^ (kref - 4) = 2 ^ (kq - j - 4) := by
    rw [← pow_add]
    congr 1
    omega
  rw [refRungCopies_eq, tRef_eq, hPt, hPtK, ← hexp]
  ring

end Widths

/-! ## §2  `eq:certified-base` at the reference construction (`A:113--116` at
`09:318`)

`A:113--116` is the one hypothesis of `thm:certified-localized-extension` that is
a statement about the matrix `M` itself, and at `09:318` that matrix is `G`.  The
frozen source proves it: `lem:wrapper-reference` (`09:151--162`) delivers
`Lambda_3(G,1,x_T,y) >= C - 1` at the schedule's `y`, and `06:908--924` fixes that
`y` to the literal `3/5`, which `A:16--18` names `y_*`.  So the base clause is not
assumed here; it is obtained by evaluating the banked chain at the schedule's own
value. -/

section Base

/-- **Aux B1 (`A:16--18`: `y_*` is a legal column density).**  `y_* = 3/5` lies in
`(0,1]`, which is what the bracket family needs before any member of it can be
formed.  Recorded separately because §2 discharges the nonemptiness side
condition of `lem:wrapper-reference` from it rather than carrying it. -/
theorem yStar_mem : 0 < yStar ∧ yStar ≤ 1 := by
  rw [yStar_eq]
  constructor <;> norm_num

/-- **`eq:certified-base` (`A:113--116`) at the reference construction, PROVED.**

`Lambda_3(G,1,x_T,y_*) >= C - 1`, i.e. `A:113--116` at the `09:318` substitution
`M = G`, `H = C - 1`, `x = x_T`.

Two things happen here that the banked `wrapperReference_rungs` does not do.

* The `y`-general banked statement is fired at the schedule's own value.  The
  wrapper's `y` is not free: `06:908--911` puts
  `hat beta_j = ((3/5)/2^j + lambda_T - 1)/lambda_T` and `06:921--924` puts
  `beta_j = ((3/5)/2^j - 1/92)/(91/92)`, so the literal `3/5` is what the
  schedule substitutes into the wrapper's own displays; `A:18` names that real
  `y_*`, `09:315` calls the certified lemma "using its fixed `y_* = 3/5`", and
  `09:330` states the conclusion at `y_*/2^j`.  Firing at `yStar` is therefore
  evaluating the definitional chain, not choosing a value.
* The bracket nonemptiness binder `hne` is **discharged outright** from
  `yStar_mem` and a nonempty row carrier, through the banked
  `wrapperReference_bracket_nonempty`, instead of being passed on.

Everything else is exactly the frozen threading of `09:196--235` and stays open
exactly as it is there: `hwS`, `hwSbT` (the two arithmetic consequences of
`eq:hard-seed-width-gates` the facade demands), `hD2` (the Stage-2 exact
complexity), `hrob` and `hD3` (the frozen `09:211--213` certificate, ledger
`STAGE2-MODULE-001`), and `hland` (the geometric landing of `09:196--204`).
Nothing here narrows any of them and nothing here proves any of them.

`C` is the banked public integer `cBlock` of `08:149--152`, so the `H = C - 1` of
`09:318` is formed from the schedule's own reading of `C` and not from a free
natural.  General in both matrix pairs, in `D_src`, `a`, `r_2`, `w_S` and
`b_T`. -/
theorem referenceCertifiedBase {Rw Cl Rw₂ Cl₂ : Type u} [Fintype Rw] [Fintype Cl]
    [Fintype Rw₂] [Fintype Cl₂]
    (Gmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    (Dsrc a r₂ wS bT : ℕ)
    (hRw : 1 ≤ Fintype.card Rw)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding Gmat M2T wS jr bT (xTdepth bT) yStar) :
    cBlock Dsrc a r₂ wS - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) yStar :=
  wrapperReference_rungs Gmat M2T Dsrc a r₂ wS bT yStar hwS hwSbT hD2 hrob hD3
    (wrapperReference_bracket_nonempty bT yStar_mem.1 yStar_mem.2 hRw) hland

end Base

/-! ## §3  The reference restriction as a full product (`09:326`)

"The reference restriction is a full product, so its balancedness error is
exactly zero."  A full product is a rectangle `S x T` on the interlace row set,
together with a retained indexed column set `K`; this section builds exactly that
object as a `RestrictionDatum`, so that `A:138--141` are three *proved* fields
rather than three assumptions. -/

section Product

variable {Blk Row Col : Type*}

/-- **Aux C1 (the represented blocks of a product are its block side).**

`A:138`'s census applied to a rectangle: `S x T` represents exactly the blocks of
`S`, provided the row side is nonempty.  General in the three carriers. -/
theorem representedBlocks_product [DecidableEq Blk] {S : Finset Blk} {T : Finset Row}
    (hT : T.Nonempty) :
    RestrictionDatum.representedBlocks (S ×ˢ T) = S := by
  ext i
  simp only [RestrictionDatum.mem_representedBlocks, Finset.mem_product]
  constructor
  · rintro ⟨z, hz, -⟩
    exact hz
  · intro hi
    obtain ⟨z, hz⟩ := hT
    exact ⟨z, hi, hz⟩

/-- **`09:326`, the full-product restriction, BUILT.**

The restriction the certified call is made at: the rectangle `S x T` inside the
interlace row set `[q] x Rows(G)`, together with the retained indexed column set
`K`.  `S` is the set of represented outer coordinates, `T` the retained reference
rows in each of them, and `K` the retained columns; the three frozen clauses
become the three fields:

* `A:138--139` (exactly `r' p_t` represented outer blocks) is `hS`, through
  `representedBlocks_product`;
* `A:139--140` (at least `ceil(r' t x m)` rows in each represented block) is
  `hrow`, and holds in *every* represented block with the same count, which is
  precisely what "full product" means -- the fibres are literally equal, so the
  balancedness error is `0` and not merely small;
* `A:141` (column density at least `h 2^{-a^sharp}`) is `hcol`.

`A:128--129`'s parameter conditions are the remaining three binders.

Kept general in `r'`, `t`, `a^sharp`, `x`, `h` and in all three carriers: the
`09:311--327` indices are substituted only in `referenceRestriction` below, so
this constructor is reusable at the second certified site without carrying that
site's numerals. -/
def productRestriction [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {r' t aSharp : ℕ} {x h : ℝ}
    (S : Finset Blk) (T : Finset Row) (K : Finset Col) (hT : T.Nonempty)
    (hS : S.card = r' * RestrictionDatum.certifiedPt t)
    (hrow : RestrictionDatum.certifiedRowFloor r' t x (Fintype.card Row) ≤ T.card)
    (hcol : RestrictionDatum.certifiedColFloor h aSharp
      ≤ (K.card : ℝ) / (Fintype.card Col : ℝ))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    RestrictionDatum.RestrictionDatum Blk Row Col r' t aSharp x h where
  rowSet := S ×ˢ T
  colSet := K
  h_pos := hh0
  h_le_one := hh1
  aSharp_le_one := ha
  block_count := by rw [representedBlocks_product hT, hS]
  row_floor := by
    intro i hi
    rw [representedBlocks_product hT] at hi
    have hset : (S ×ˢ T).filter (fun p => p.1 = i) = ({i} : Finset Blk) ×ˢ T := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by rw [h1]; exact hi, h2⟩, h1⟩
    rw [hset, Finset.card_product, Finset.card_singleton, one_mul]
    exact hrow
  col_floor := hcol

/-- **Aux C2 (`A:138`'s census readout of the product).**  The banked `selCard`
readout returns the frozen count on the nose.  General. -/
@[simp] theorem productRestriction_selCard [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {r' t aSharp : ℕ} {x h : ℝ}
    (S : Finset Blk) (T : Finset Row) (K : Finset Col) (hT : T.Nonempty)
    (hS : S.card = r' * RestrictionDatum.certifiedPt t)
    (hrow : RestrictionDatum.certifiedRowFloor r' t x (Fintype.card Row) ≤ T.card)
    (hcol : RestrictionDatum.certifiedColFloor h aSharp
      ≤ (K.card : ℝ) / (Fintype.card Col : ℝ))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    (productRestriction S T K hT hS hrow hcol hh0 hh1 ha).selCard
      = r' * RestrictionDatum.certifiedPt t := by
  change (RestrictionDatum.representedBlocks (S ×ˢ T)).card = _
  rw [representedBlocks_product hT, hS]

/-- **Aux C3 (`A:139--140`'s per-block readout of the product, and why `eps = 0`).**

The banked `rowsPerBlock` readout is the *minimum* fibre size over the represented
blocks; on a full product every fibre is `T` itself, so the minimum equals the
common value `|T|`.  That equality is the Lean content of `09:326`'s "the
reference restriction is a full product, so its balancedness error is exactly
zero": the fibres do not merely all exceed a floor, they all have the same size.
General; the hypothesis is that at least one outer coordinate is represented. -/
theorem productRestriction_rowsPerBlock [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {r' t aSharp : ℕ} {x h : ℝ}
    (S : Finset Blk) (T : Finset Row) (K : Finset Col) (hT : T.Nonempty)
    (hS : S.card = r' * RestrictionDatum.certifiedPt t)
    (hrow : RestrictionDatum.certifiedRowFloor r' t x (Fintype.card Row) ≤ T.card)
    (hcol : RestrictionDatum.certifiedColFloor h aSharp
      ≤ (K.card : ℝ) / (Fintype.card Col : ℝ))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) (hSne : S.Nonempty) :
    (productRestriction S T K hT hS hrow hcol hh0 hh1 ha).rowsPerBlock = T.card := by
  classical
  have hrep : RestrictionDatum.representedBlocks
      ((productRestriction S T K hT hS hrow hcol hh0 hh1 ha).rowSet) = S := by
    change RestrictionDatum.representedBlocks (S ×ˢ T) = S
    exact representedBlocks_product hT
  have hfib : ∀ i ∈ S,
      ((productRestriction S T K hT hS hrow hcol hh0 hh1 ha).fibre i).card = T.card := by
    intro i hi
    change ((S ×ˢ T).filter (fun p => p.1 = i)).card = T.card
    have hset : (S ×ˢ T).filter (fun p => p.1 = i) = ({i} : Finset Blk) ×ˢ T := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by rw [h1]; exact hi, h2⟩, h1⟩
    rw [hset, Finset.card_product, Finset.card_singleton, one_mul]
  have hne : (RestrictionDatum.representedBlocks
      ((productRestriction S T K hT hS hrow hcol hh0 hh1 ha).rowSet)).Nonempty := by
    rw [hrep]; exact hSne
  rw [RestrictionDatum.RestrictionDatum.rowsPerBlock, dif_pos hne]
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := hSne
    have hiMem : i ∈ RestrictionDatum.representedBlocks
        ((productRestriction S T K hT hS hrow hcol hh0 hh1 ha).rowSet) := by
      rw [hrep]; exact hi
    exact le_of_le_of_eq (Finset.inf'_le _ hiMem) (hfib i hi)
  · refine Finset.le_inf' hne _ ?_
    intro i hi
    rw [hrep] at hi
    exact le_of_eq (hfib i hi).symm

/-- **Aux C4 (`A:141`'s density readout of the product).**  The banked `colDens`
readout is the retained fraction of the indexed columns, and on the product it is
the fraction determined by `K`.  General; recorded because it is the readout the
endpoint compares with `theta 2^{-a^sharp}`. -/
@[simp] theorem productRestriction_colDens [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {r' t aSharp : ℕ} {x h : ℝ}
    (S : Finset Blk) (T : Finset Row) (K : Finset Col) (hT : T.Nonempty)
    (hS : S.card = r' * RestrictionDatum.certifiedPt t)
    (hrow : RestrictionDatum.certifiedRowFloor r' t x (Fintype.card Row) ≤ T.card)
    (hcol : RestrictionDatum.certifiedColFloor h aSharp
      ≤ (K.card : ℝ) / (Fintype.card Col : ℝ))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    (productRestriction S T K hT hS hrow hcol hh0 hh1 ha).colDens
      = (K.card : ℝ) / (Fintype.card Col : ℝ) := rfl

end Product

/-! ## §4  The restriction at the `09:313--323` indices

The same object at the substitution's own values -- `r' = kappa_j/t_ref`,
`t = t_ref`, `a^sharp = 0`, `x = x_T`, `h = theta` -- so that its type is
literally the one `CanonicalReferenceStoppingCall` demands. -/

section Canonical

/-- **The reference restriction at the canonical substitution, BUILT.**

`productRestriction` at the `09:319--322` indices.  Its block count is `A:138`'s
`r' p_{t_ref}`, which `refBlockCount_eq_certifiedPt_kappa` identifies with the
frozen `9 kappa_j/16` of `09:311`; its row floor is `A:139--140`'s
`ceil(r' t_ref x_T m)` with `m` the row count of `G`; and its column floor is
`A:141` at `a^sharp = 0` (`09:322`), i.e. plainly `theta`.

The three data arguments are the restriction the routing hands the call at a
given member: `S` the selected outer coordinates, `T` the retained reference
rows, `K` the retained columns.  They are **arguments**, not choices made here --
which routed triple the frontier produces at a given member of
`<U,1,y/2^j,theta>` is the content of the later blocks of Section 9 and is not
decided in this tranche. -/
def referenceRestriction {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row]
    [Fintype Col] (kq kref j : ℕ) {xT θ : ℝ}
    (S : Finset Blk) (T : Finset Row) (K : Finset Col) (hT : T.Nonempty)
    (hS : S.card = refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref))
    (hrow : RestrictionDatum.certifiedRowFloor (refRungCopies kq kref j) (tRef kref)
      xT (Fintype.card Row) ≤ T.card)
    (hcol : θ ≤ (K.card : ℝ) / (Fintype.card Col : ℝ))
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    RestrictionDatum.RestrictionDatum Blk Row Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ :=
  productRestriction S T K hT hS hrow
    (by
      have hden : RestrictionDatum.certifiedColFloor θ 0 = θ := by
        rw [RestrictionDatum.certifiedColFloor]
        norm_num
      rw [hden]
      exact hcol)
    hθ0 hθ1 (by norm_num)

/-- **`A:139--140`'s row floor is read at `m_G`, PROVED.**

`A:111` fixes `m` as the row count of the matrix the endpoint is invoked on, and
at `09:318` that matrix is `G`, whose row carrier is `Omega x [w_0]` (`09:113`).
So the per-block floor of the reference restriction is
`ceil(kappa_j x_T m_G)` with `m_G = |Omega| w_0` (`09:113` with `09:116`) -- **not** a free
natural, and **not** `m = |Rows(N)|`.  The banked `ScaleAlignOpening.card_refRows`
supplies the cardinality and `refRungCopies_mul_tRef` collapses `r' t_ref` to the
frozen capacity.

General in the reservoir carrier, the base multiplicity, `k_q`, `k_ref`, `j` and
`x_T`, at `09:327`'s legality range. -/
theorem referenceRowFloor_at_mG (Om : Type*) [Fintype Om] (w₀ : ℕ)
    {kq kref j : ℕ} {xT : ℝ} (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) :
    RestrictionDatum.certifiedRowFloor (refRungCopies kq kref j) (tRef kref) xT
        (Fintype.card (Om × Fin w₀))
      = ⌈((kappaLow kq j : ℕ) : ℝ) * xT * ((Fintype.card Om * w₀ : ℕ) : ℝ)⌉₊ := by
  rw [RestrictionDatum.certifiedRowFloor, card_refRows Om w₀,
    refRungCopies_mul_tRef hj hq4]

end Canonical

/-! ## §5  The three legality clauses of `09:325--327`, derived

"The equality `eq:reference-all-columns` verifies the orientation; the reference
restriction is a full product, so its balancedness error is exactly zero; and
`q/4 >= t_ref` makes all three values of `r'` legal."

The first clause is structural and needs no derivation: `ScaleAlignOpening.referenceG`
has the ambient column carrier `Cl` in its *type*, so at the call the endpoint's
column axis is `Cols(N)` with no transport, and the banked
`referenceG_follows_bob` reads that off by `rfl`.  Nothing is restated here.  The
second and third clauses are the two derivations below. -/

section Legality

/-- **`09:326`, second clause: the family clause is met on the `eps = 0` branch,
PROVED.**

`A:126--128` offers two branches -- a `(q,t,eps)`-balanced family with
`0 < eps < 1`, or the exact full product with `eps = 0`.  `09:326` selects the
second: "the reference restriction is a full product, so its balancedness error
is exactly zero".  So the legality disjunction is discharged at `eps = 0` without
any appeal to the cited expander family, which is why `EXPANDER-001` occurs in no
hypothesis of this module.

*What this declaration does and does not carry.*  As a Lean proposition it is a
tautology -- `Or.inr rfl` closes it -- and it is recorded as such: its content is
the **branch selection**, that `09:326` puts the reference call on `A:126--128`'s
`eps = 0` alternative rather than on the balanced-family alternative, which is
what keeps `EXPANDER-001` out of every hypothesis here.  The non-tautologous
content of `09:326` -- that the restriction really is a full product, so its
balancedness error is exactly zero -- is carried in §3 by
`productRestriction_rowsPerBlock`, which proves every fibre of the product equals
`T.card` exactly rather than merely clearing a floor.  The banked
`epsBranch_bounds` and `epsBranch_rejects_neg_one` record that the disjunction
constrains `1 + eps` on both sides and excludes reals, but they are properties of
the banked branch predicate, not of this statement. -/
theorem referenceEps_is_the_full_product_branch :
    (0 < (0 : ℝ) ∧ (0 : ℝ) < 1) ∨ (0 : ℝ) = 0 := Or.inr rfl

/-- **Aux D2 (the denominator of `eq:certified-E1`/`E2` at the reference call).**

On the branch `09:326` selects, the `1 + eps` that both certified side
inequalities divide by is `1`; the banked `epsBranch_bounds` is fired at that
branch so the two displays are well-posed and cannot be satisfied by inflating
`eps`. -/
theorem referenceEps_denominator_bounds : 0 < 1 + (0 : ℝ) ∧ 1 + (0 : ℝ) < 2 :=
  epsBranch_bounds referenceEps_is_the_full_product_branch

/-- **`09:327`, third clause: all three values of `r'` are legal, PROVED.**

"`q/4 >= t_ref` makes all three values of `r'` legal."  In exponent form the
hypothesis is `k_ref + 2 <= k_q`, and the frozen range of the rung index is
`09:277--278`'s `j in {0,1,2}`; the conclusion is that the whole integer gate list
of `A:117` and `A:125` holds **for every one of the three rungs at once**, which
is the reading `09:327` states and which the banked per-rung `canonicalCall_gates`
does not give (it takes `k_ref + j <= k_q` as its own hypothesis, one `j` at a
time).

The last conjunct is the exponent identity `log_2(r' t_ref) = log_2 kappa_j`; it
is what makes `eq:certified-E3`'s output the frozen `09:330--331`.  General in
`k_q` and `k_ref`. -/
theorem referenceRung_legality_at_all_three {kq kref : ℕ}
    (hfloor : Nat.clog 2 tCert ≤ kref) (hq4 : kref + 2 ≤ kq) :
    ∀ j : ℕ, j ≤ 2 →
      tCert ≤ tRef kref
        ∧ 16 ∣ tRef kref
        ∧ refRungCopies kq kref j ≤ refOuterCopies kq kref
        ∧ (2 : ℕ) ^ kq = refOuterCopies kq kref * tRef kref
        ∧ (kq - j - kref) + kref = kq - j := by
  intro j hj
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    canonicalCall_gates (kq := kq) (kref := kref) (j := j) hfloor (by omega)
  exact ⟨h1, h2, h3, h4, h5⟩

end Legality

/-! ## §6  The canonical instance: every antecedent but the endpoint itself

`certifiedE3_at_lowRung` (banked) takes eleven hypotheses plus `hcall`.  Six of
them are `sec:wrapper-low-rungs`' own and it already discharges them.  Of the
remaining five, this section discharges **four** at the reference construction --
`hxT0` from the banked `x_T` membership, `hbase` from §2, `hE1` and `hE2` from
the two `eq:tref-search` side clauses -- leaving the carrier nonemptiness (a
property of the construction's carriers) and the restriction datum, which §4
builds.

What is left is `hcall`, and only `hcall`: the frozen appendix theorem itself. -/

section Instance

/-- **`eq:certified-E3` at the reference construction (`09:311--331`), PROVED
modulo the endpoint implication.**

Every quantity is here at its banked definitional value: `C = cBlock` of
`08:149--152`, `x_T = xTdepth b_T` of `08:166`, `t_ref = 2^{k_ref}` of
`06:568--569`, `H = C - 1` of `09:318`, and `eq:certified-base` is the *theorem*
`referenceCertifiedBase` rather than a binder.  Nothing is assigned a numeral.

The hypothesis groups, and where each comes from:

* `hj`, `hq4`, `hC`, `hfloor`, `hgate` -- the block's own gates
  (`09:277--278`, `09:327`, `09:240`, `06:561--563`, `09:304--307`);
* `hRw`, `hCl` -- `A:111`'s two nonemptiness clauses for `G`;
* `hwS`, `hwSbT`, `hD2`, `hrob`, `hD3`, `hland` -- `lem:wrapper-reference`'s own
  open binders, passed to §2 unchanged and narrowed nowhere;
* `hcand`, `hsched1`, `hsched2`, `hθL` -- the second and third clauses of
  `eq:tref-search` (`06:564--567`) plus `06:535`'s `2^{-L_theta} <= theta`, fed
  to the two banked side legs;
* `Dat` -- the restriction, which `referenceRestriction` builds;
* `hcall` -- **the endpoint implication, the one residue**, i.e.
  `thm:certified-localized-extension` at this substitution.  It is a binder here
  and is not proved anywhere in `src/`.

*Why the trivial witness fails.*  The conclusion is
`CertifiedE3 (C-1) (k_q - j) val`, i.e. `(C-1) + (k_q - j) <= val`; at the frozen
`C >= 3` that number is at least `2`, so the readout `val = 0` -- the complexity
of a constant subgame, which the banked
`WrapperLowRungs.wrapperLowRungs_not_automatic` exhibits as an actual member
readout -- is refuted outright (banked `certifiedE3_at_lowRung_is_not_free`).  So
the bound cannot be read off the shape of the statement.

General in both matrix pairs, in the restriction carriers, and in every schedule
integer and real. -/
theorem certifiedE3_at_referenceConstruction {Rw Cl Rw₂ Cl₂ : Type u}
    [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (Gmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {Dsrc a r₂ wS bT kq kref j jcand val : ℕ} {θ Lθ : ℝ}
    (Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ)
    (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ cBlock Dsrc a r₂ wS)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hgate : ((2 : ℝ) ^ kq) * xTdepth bT ≤ 4 / 25025)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding Gmat M2T wS jr bT (xTdepth bT) yStar)
    (hcand : RawLowProfileBody.J49Feasible kref jcand)
    (hsched1 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kq : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (kref - 1))
    (hsched2 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kref : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (jcand : ℕ))
    (hθL : (2 : ℝ) ^ (-Lθ) ≤ θ)
    (hcall : CanonicalReferenceStoppingCall Gmat (cBlock Dsrc a r₂ wS) kq kref j
      (xTdepth bT) θ Dat val) :
    CertifiedE3 (cBlock Dsrc a r₂ wS - 1) (kq - j) val := by
  have hk1 : 1 ≤ kref := by
    have h20 : (2 : ℕ) ^ 20 ≤ kref := clog_two_tCert ▸ hfloor
    have hpos : (0 : ℕ) < 2 ^ 20 := by norm_num
    omega
  exact certifiedE3_at_lowRung Gmat Dat hj hq4 hC hfloor (xTdepth_mem bT).1 hgate hCl
    (referenceCertifiedBase Gmat M2T Dsrc a r₂ wS bT hRw hwS hwSbT hD2 hrob hD3 hland)
    (certifiedE1_of_trefSearch hk1 (by omega) hsched1 hθL)
    (certifiedE2_of_trefSearch hcand hsched2 hθL) hcall

/-- **`eq:wrapper-u-low` (`09:264--266`) at the reference construction, PROVED
modulo the endpoint implication (`09:333`).**

The same discharge carried through the banked
`WrapperLowRungAssembly.wrapperLowRungs_of_canonicalCall`: its `hbase`, `hE1` and
`hE2` binders are supplied here from `lem:wrapper-reference` and from
`eq:tref-search`, so what is left of that theorem's hypothesis list is the block's
own gates, the bracket nonemptiness `hne`, and the per-member canonical call
`hrung`.

`hrung` remains a **binder**, and this declaration does not inhabit it.  It is the
per-member form of `09:311--327`: at each member of `<U,1,y/2^j,theta>` the
construction retains the reference rows, projects to `9 kappa_j/16` outer
coordinates, and applies the certified-scale reference stopping lemma at the
`09:317--323` substitution.  §4 builds the restriction such a member needs and §5
derives its legality; what is not built is the *routing* that selects the triple
`(S, T, K)` at a given member, nor the appendix theorem the call asserts.

*Why the trivial witness fails.*  The deliverable is a lower bound on a
`Nat.sInf`, and at the constant matrix that infimum is `0` while the demanded
value `C + k_q - 1 - j` is at least `2`; the banked
`WrapperLowRungs.wrapperLowRungs_not_automatic` exhibits exactly that member.

General in the carriers, in `N`, `G`, `M_2^T`, and in every schedule integer and
real. -/
theorem wrapperLowRungs_at_referenceConstruction {Rw Cl Rw₂ Cl₂ : Type u}
    [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (Nmat : Rw → Cl → Bool) (Gmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {Dsrc a r₂ wS bT kq kref jcand : ℕ} {θ Lθ y : ℝ}
    (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ cBlock Dsrc a r₂ wS)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hgate : ((2 : ℝ) ^ kq) * xTdepth bT ≤ 4 / 25025)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding Gmat M2T wS jr bT (xTdepth bT) yStar)
    (hcand : RawLowProfileBody.J49Feasible kref jcand)
    (hsched1 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kq : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (kref - 1))
    (hsched2 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kref : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (jcand : ℕ))
    (hθL : (2 : ℝ) ^ (-Lθ) ≤ θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hrung : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ,
        ∃ Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
            (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ,
          CanonicalReferenceStoppingCall Gmat (cBlock Dsrc a r₂ wS) kq kref j
            (xTdepth bT) θ Dat
            (D (subgame (interlaceFun (wrapperU Nmat kq) 1) RC.1 RC.2))) :
    ∀ j : ℕ, j ≤ 2 →
      cBlock Dsrc a r₂ wS + kq ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat kq) 1)
        (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ) := by
  have hk1 : 1 ≤ kref := by
    have h20 : (2 : ℕ) ^ 20 ≤ kref := clog_two_tCert ▸ hfloor
    have hpos : (0 : ℕ) < 2 ^ 20 := by norm_num
    omega
  exact wrapperLowRungs_of_canonicalCall Nmat Gmat hq4 hC hfloor (xTdepth_mem bT).1
    hgate hCl
    (referenceCertifiedBase Gmat M2T Dsrc a r₂ wS bT hRw hwS hwSbT hD2 hrob hD3 hland)
    (certifiedE1_of_trefSearch hk1 (by omega) hsched1 hθL)
    (certifiedE2_of_trefSearch hcand hsched2 hθL) hne hrung

/-- **The same instance at the built reference matrix `G` (`09:115`).**

`certifiedE3_at_referenceConstruction` fired at `Gmat = referenceG N`, i.e. at the
object `09:115` defines rather than at an arbitrary matrix.  Two things become
structural rather than assumed at this instantiation, and both are the frozen
`09:325` clause "the equality `eq:reference-all-columns` verifies the
orientation":

* the endpoint's column axis is the **ambient** `Cl = Cols(N)`, because that is
  the column carrier in `referenceG`'s type -- no projection, no coercion, no
  reduced alphabet, exactly as `09:125--127` requires; so `A:111`'s column
  nonemptiness for `G` is the ambient one and needs no transport;
* the endpoint's `m` (`A:111`) is `m_G = |Omega| w_0` (`09:113` with `09:116`), and
  `referenceRowFloor_at_mG` records that `A:139--140`'s per-block floor is read
  there.

General in the reservoir carriers, the multiplicities, `N`, and every schedule
parameter. -/
theorem certifiedE3_at_referenceG {Om Sg Dg Cl Rw₂ Cl₂ : Type u}
    [Fintype Om] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂] {w₀ wSg wD : ℕ}
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (Nmat : ProtCols Om Sg Dg w₀ wSg wD → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {Dsrc a r₂ wS bT kq kref j jcand val : ℕ} {θ Lθ : ℝ}
    (Dat : RestrictionDatum.RestrictionDatum Blk (Om × Fin w₀) Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ)
    (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ cBlock Dsrc a r₂ wS)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hgate : ((2 : ℝ) ^ kq) * xTdepth bT ≤ 4 / 25025)
    (hmG : 1 ≤ Fintype.card Om * w₀) (hCl : 1 ≤ Fintype.card Cl)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding (referenceG Nmat) M2T wS jr bT (xTdepth bT) yStar)
    (hcand : RawLowProfileBody.J49Feasible kref jcand)
    (hsched1 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kq : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (kref - 1))
    (hsched2 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kref : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (jcand : ℕ))
    (hθL : (2 : ℝ) ^ (-Lθ) ≤ θ)
    (hcall : CanonicalReferenceStoppingCall (referenceG Nmat) (cBlock Dsrc a r₂ wS)
      kq kref j (xTdepth bT) θ Dat val) :
    CertifiedE3 (cBlock Dsrc a r₂ wS - 1) (kq - j) val := by
  have hRw : 1 ≤ Fintype.card (Om × Fin w₀) := by
    rw [card_refRows Om w₀]
    exact hmG
  exact certifiedE3_at_referenceConstruction (referenceG Nmat) M2T Dat hj hq4 hC
    hfloor hgate hRw hCl hwS hwSbT hD2 hrob hD3 hland hcand hsched1 hsched2 hθL hcall

end Instance

/-! ## §7  Statement poles and LANE-GATE 3 non-vacuity

A green build sees none of the three failure modes guarded against here: a
constructor whose clauses are met by a degenerate restriction, a block-count
identity that silently truncates, and a base clause that holds for free. -/

section Poles

/-- **Statement pole (the product constructor rejects an empty row side).**

`productRestriction`'s `hT : T.Nonempty` is load-bearing, not decoration: with an
empty row side the rectangle represents **no** outer block, so `A:138`'s census
returns `0` while the frozen demand `r' p_t` is positive in the whole legal range
(`A:125` makes `r'` a positive power of two and `A:117` makes `t` a power of two
divisible by `16` with `t >= t_cert`, so `p_t > 0`).  The datum would then be
inhabited by a restriction retaining nothing.

*Why the trivial witness fails.*  The statement is a refutation, so there is
nothing to exhibit; what it rules out is the degenerate rectangle.  General in
the carriers and in `S`. -/
theorem productRestriction_rejects_empty_rows {Blk Row : Type*} [DecidableEq Blk]
    {r' t : ℕ} (S : Finset Blk) (hpos : 0 < r' * RestrictionDatum.certifiedPt t) :
    (RestrictionDatum.representedBlocks (S ×ˢ (∅ : Finset Row))).card
      ≠ r' * RestrictionDatum.certifiedPt t := by
  intro hcon
  have hempty : RestrictionDatum.representedBlocks (S ×ˢ (∅ : Finset Row))
      = (∅ : Finset Blk) := by
    ext i
    simp [RestrictionDatum.representedBlocks]
  rw [hempty, Finset.card_empty] at hcon
  omega

/-- **Statement pole (`A:117`'s divisibility cannot be dropped from the block
count).**

`refBlockCount_eq_certifiedPt_kappa` says `r' p_{t_ref} = p_{kappa_j}`, and the
proof runs through `A:120`'s natural division being exact, which is what
`A:117`'s "divisible by `16`" buys.  Off that range the identity fails: at
`t = 8`, `r' = 2` the left side is `2 . p_8 = 2 . (72/16) = 2 . 4 = 8` while the
right side is `p_16 = 144/16 = 9`.  The identity is therefore a consequence of
the frozen width gate and not an arithmetic accident.

*Why the trivial witness fails.*  The existential asks for a pair at which the
identity is **false**; any pair inside `A:117`'s range would make it true, so the
exhibited pair must sit outside it -- and it does, `16` not dividing `8`. -/
theorem refBlockCount_needs_the_width_divisibility :
    ∃ r' t : ℕ, ¬ (16 ∣ t)
      ∧ r' * RestrictionDatum.certifiedPt t ≠ RestrictionDatum.certifiedPt (r' * t) := by
  refine ⟨2, 8, by omega, ?_⟩
  rw [RestrictionDatum.certifiedPt, RestrictionDatum.certifiedPt]
  norm_num

/-- **Statement pole (`eq:certified-base` is not satisfied by the shape of the
statement).**

`referenceCertifiedBase` concludes `C - 1 <= Lambda_3(G,1,x_T,y_*)`, and the
worry is that this could hold for free.  It cannot: at the frozen `C >= 3` of
`09:240` the clause **forces** the readout to be at least `2`, so it is refuted
outright by the value `0` -- which is a value `LambdaGE` actually takes, being a
minimum of three `Nat.sInf`s over families that contain constant subgames (the
banked `WrapperLowRungs.wrapperLowRungs_not_automatic` exhibits exactly such a
member readout).  So the value comes from `lem:wrapper-reference`'s open binders
-- the Stage-2 certificate and the geometric landing -- and not from the bracket
shape.

*Why the trivial witness fails.*  There is no witness to find: the statement is
the forcing direction, and `v = 0` is exactly what it excludes.  General in `C`
at the frozen floor and in the readout. -/
theorem referenceCertifiedBase_is_not_free {C v : ℕ} (hC : 3 ≤ C) (h : C - 1 ≤ v) :
    2 ≤ v := by
  omega

/-- **LANE-GATE 3 (the canonical restriction is inhabited at legal parameters),
PROVED.**

The `09:313--323` index tuple -- `r' = kappa_j/t_ref`, `t = t_ref`,
`a^sharp = 0`, `x = x_T`, `h = theta` -- carries a restriction datum at the
frozen carriers: the block carrier `[q] = Fin (2^{k_q})` of `A:125` (whose
identification with `09:105`'s scale-alignment width is forced by the
substitution `q = r t = (q/t_ref) t_ref`), a general row carrier (`A:111`'s `m` is
an input, not a size the clause bundle fixes), and the indexed column carrier
`[L]` of `03:297--299`, kept general in `1 <= L` because on the `eps = 0` branch
`L = |Y|^q` is source-DEFINED and assigning it a numeral would be assigning a
value to a defined quantity.

Every hypothesis is a frozen gate: `06:561--563`'s floor term, `09:277--278`'s
rung range, `09:327`'s legality, `eq:wrapper-low-simple-gate`, and `A:128`'s
`0 < theta <= 1`.  The first conjunct records that the demanded block count is
**positive** there, so the datum is not inhabited by an empty restriction.

This is **not** canonical inhabitation of the *call*: it exhibits a restriction,
not a proof of `thm:certified-localized-extension`.  That obligation stays
registered and deferred. -/
theorem referenceRestriction_nonempty {Row : Type*} [Fintype Row]
    {kq kref j L : ℕ} {xT θ : ℝ}
    (hfloor : Nat.clog 2 tCert ≤ kref) (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq)
    (hRow : 1 ≤ Fintype.card Row) (hL : 1 ≤ L)
    (hxT0 : 0 < xT) (hgate : ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref)
      ∧ Nonempty (RestrictionDatum.RestrictionDatum (Fin (2 ^ kq)) Row (Fin L)
          (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ) := by
  have hk4 : 4 ≤ kref := by
    have h20 : (2 : ℕ) ^ 20 ≤ kref := clog_two_tCert ▸ hfloor
    have hsmall : (4 : ℕ) ≤ 2 ^ 20 := by norm_num
    omega
  have hcount : refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref)
      = RestrictionDatum.certifiedPt (kappaLow kq j) :=
    refBlockCount_eq_certifiedPt_kappa hk4 hj hq4
  have hpos : 0 < refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref) := by
    rw [hcount, kappaLow_def]
    exact RestrictionDatum.certifiedPt_pos
      (RestrictionDatum.sixteen_dvd_two_pow (by omega)) (pow_pos (by norm_num) _)
  refine ⟨hpos, ?_⟩
  -- `r' t_ref = kappa_j = 2^{k_q - j}` and the row request is legal there
  have hmul : (2 : ℕ) ^ (kq - j - kref) * 2 ^ kref = 2 ^ (kq - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hcast : (((2 ^ (kq - j - kref) * 2 ^ kref : ℕ)) : ℝ) = (2 : ℝ) ^ (kq - j) := by
    rw [hmul]; push_cast; ring
  have hpowle : ((2 : ℝ) ^ (kq - j)) ≤ (2 : ℝ) ^ kq :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hrowgate : ((2 : ℝ) ^ (kq - j)) * xT ≤ 1 := by nlinarith [le_of_lt hxT0]
  -- the block carrier is large enough: `r' p_{t_ref} = 9 . 2^{k_q - j - 4} <= 2^{k_q}`
  have hblk : (2 : ℕ) ^ (kq - j - kref) * RestrictionDatum.certifiedPt ((2 : ℕ) ^ kref)
      ≤ Fintype.card (Fin (2 ^ kq)) := by
    have hstep : (2 : ℕ) ^ (kq - j - kref) * RestrictionDatum.certifiedPt ((2 : ℕ) ^ kref)
        = RestrictionDatum.certifiedPt (kappaLow kq j) := by
      rw [← hcount, refRungCopies_eq, tRef_eq]
    have hPtK : RestrictionDatum.certifiedPt (kappaLow kq j) ≤ 2 ^ (kq - j) := by
      have hP : 16 * RestrictionDatum.certifiedPt (kappaLow kq j) = 9 * 2 ^ (kq - j) := by
        rw [kappaLow_def]
        exact RestrictionDatum.sixteen_mul_certifiedPt
          (RestrictionDatum.sixteen_dvd_two_pow (by omega))
      omega
    have hfin : (2 : ℕ) ^ (kq - j) ≤ 2 ^ kq := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Fintype.card_fin, hstep]
    exact le_trans hPtK hfin
  refine RestrictionDatum.nonempty_restrictionDatum hθ0 hθ1 hblk ?_ hRow ?_ (by norm_num)
  · refine RestrictionDatum.certifiedRowFloor_le ?_
    rw [hcast]
    exact hrowgate
  · simpa using hL

/-- **Aux G1 (`eq:wrapper-low-simple-gate` is suppliable at the PINNED `x_T`),
PROVED.**

`09:304--307` states the gate `q x_T <= 4/25025` about the *defined* row density
`x_T = 2^{-b_T}` (`08:166`), not about a free real, and the banked non-vacuity
instances state it about a free real instead.  This closes that half: at
`x_T = xTdepth b_T` the gate holds for **every** auxiliary depth at or above
`k_q + 16`, since there `q x_T <= 2^{-16} = 1/65536 <= 4/25025`.

Stated as a range and not at a value, deliberately.  `b_T` is a quantity the
frozen schedule **defines** -- `06:238--242` puts `k_T = log_2(s/4)`,
`b_T = 2^{j_49(k_T)}` -- so exhibiting a numeral for it would be assigning a
value to a defined quantity; what may honestly be shown is that the gate is not
unsatisfiable at the pinned density, over the whole range the schedule's own
derivation has to land in.  General in `k_q` and `b_T`. -/
theorem simple_gate_at_xTdepth {kq bT : ℕ} (h : kq + 16 ≤ bT) :
    0 < xTdepth bT ∧ ((2 : ℝ) ^ kq) * xTdepth bT ≤ 4 / 25025 ∧ xTdepth bT ≤ 1 := by
  have hpos : 0 < xTdepth bT := (xTdepth_mem bT).1
  refine ⟨hpos, ?_, (xTdepth_mem bT).2⟩
  have hsplit : (2 : ℝ) ^ bT = 2 ^ kq * 2 ^ (bT - kq) := by
    rw [← pow_add]
    congr 1
    omega
  have h16 : (2 : ℝ) ^ 16 ≤ 2 ^ (bT - kq) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hval : ((2 : ℝ) ^ kq) * xTdepth bT = 1 / (2 : ℝ) ^ (bT - kq) := by
    rw [xTdepth, hsplit]
    field_simp
  have hstep : (1 : ℝ) / (2 : ℝ) ^ (bT - kq) ≤ 1 / (2 : ℝ) ^ 16 :=
    one_div_le_one_div_of_le (by positivity) h16
  have hnum : (1 : ℝ) / (2 : ℝ) ^ 16 ≤ 4 / 25025 := by norm_num
  rw [hval]
  linarith

/-- **Aux G2 (`06:535`'s leg is suppliable at every legal density), PROVED.**

`eq:Q-theta-choice` closes with `L_theta = clog_2(1/theta)` (`06:535`), and the
two banked side legs consume it only through `2^{-L_theta} <= theta`.  This
records that the leg is not an extra constraint on `theta`: for **every** density
`A:128` admits, some integer `L_theta` supplies it.  Without this, the joint
non-vacuity instance below would have to pin a numeral for `theta`, which
`eq:Q-theta-choice` forbids -- its value depends on the instance datum `bout`.
General in `theta`. -/
theorem exists_lTheta_for_density {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℝ)) ≤ θ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hθ0 (show (1 : ℝ) / 2 < 1 by norm_num)
  refine ⟨n, ?_⟩
  have hid : ((1 : ℝ) / 2) ^ n = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [← hid]
  exact le_of_lt hn

/-- **LANE-GATE 3 for the WHOLE gate set of the reference call, at ONE width,
PROVED.**

The strongest available joint consistency check short of the appendix theorem:
at a single reference width every gate the reference call needs holds
simultaneously -- `A:117`'s two width gates, `09:327`'s legality for all three
rungs, `eq:wrapper-low-simple-gate` with `A:112`'s upper bound derived from it,
both `eq:tref-search` side clauses in the form the two banked legs consume, and
the existence of the restriction datum itself at the canonical indices.

Every exhibited value is the paper's own, taken as a closed form:

* `k_ref` and the `j_49` candidate at `eq:kref-tested-endpoint`'s
  `k_ref^* = 100 L_P^2`, `j_ref^* = 4 L_P` (`06:586--590`), through the banked
  `WrapperLowRungAssembly.trefSearch_tested_endpoint_is_satisfiable`, which
  clears the `clog_2(t_0(3/5))` floor because `L_P` is taken past the
  `02:865--868` cutoff;
* `k_q = k_ref + 2`, the boundary of `09:327`;
* `x_T` from the banked `WrapperLowRungs.wrapperLowRungGates_legal_instance`,
  which fixes only the single ratio `q x_T` that `eq:wrapper-low-simple-gate`
  constrains, and from which no parameter may be read out;
* `theta` an arbitrary real in `A:128`'s range, quantified rather than pinned,
  since `eq:Q-theta-choice`'s value depends on the instance datum `bout`; the
  matching `L_theta` is produced by `exists_lTheta_for_density` rather than
  assumed, so the density leg of the two side inequalities is part of the joint
  claim and not carried outside it.

Still **not** canonical inhabitation of the call: no `hcall`, no appendix proof.
What it rules out is the failure mode a green build cannot see -- a hypothesis
bundle with no legal model at all. -/
theorem referenceCall_full_gate_set_is_satisfiable (Ccert : ℕ) {Row : Type}
    [Fintype Row] (hRow : 1 ≤ Fintype.card Row) {L : ℕ} (hL : 1 ≤ L)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ (kref kq jcand Ltheta : ℕ) (xT : ℝ),
      Nat.clog 2 tCert ≤ kref ∧ kref + 2 ≤ kq
        ∧ tCert ≤ tRef kref ∧ 16 ∣ tRef kref
        ∧ RawLowProfileBody.J49Feasible kref jcand
        ∧ 0 < xT ∧ ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025 ∧ xT ≤ 1
        ∧ (2 : ℝ) ^ (-(Ltheta : ℝ)) ≤ θ
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kq : ℝ) + (Ltheta : ℝ) ≤ (2 : ℝ) ^ (kref - 1))
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kref : ℝ) + (Ltheta : ℝ) ≤ (2 : ℝ) ^ (jcand : ℕ))
        ∧ (∀ j : ℕ, j ≤ 2 →
            0 < refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref)
              ∧ Nonempty (RestrictionDatum.RestrictionDatum (Fin (2 ^ kq)) Row (Fin L)
                  (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ)) := by
  obtain ⟨Ltheta, hLtheta⟩ := exists_lTheta_for_density hθ0
  obtain ⟨kref, kq, jcand, xT, hfloor, hq4, hk4, hcand, hxT0, hgate, hxT1,
    hsched1, hsched2⟩ := lowRung_full_gate_set_is_satisfiable Ccert Ltheta
  obtain ⟨hw1, hw2⟩ := certifiedWidthGates_of_kRefFloor hfloor
  exact ⟨kref, kq, jcand, Ltheta, xT, hfloor, hq4, hw1, hw2, hcand, hxT0, hgate, hxT1,
    hLtheta, hsched1, hsched2,
    fun j hj => referenceRestriction_nonempty hfloor hj hq4 hRow hL hxT0 hgate hθ0 hθ1⟩

end Poles

end EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
