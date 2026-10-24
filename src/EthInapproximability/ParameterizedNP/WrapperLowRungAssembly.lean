import EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension

/-!
# Parameterized NP route: the `09:311--327` low-rung assembly

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:311--327`, this module's target.**  "Project the retained outer
      column set to any `9 kappa_j/16` such coordinates.  Its normalized density
      remains at least `theta`, by specified-coordinate projection.  Apply the
      certified-scale reference stopping lemma,
      `thm:certified-localized-extension`, using its fixed `y_* = 3/5` and the
      substitutions `M = G`, `H = C-1`, `x = x_T`, `t = t_ref`,
      `r = q/t_ref`, `r' = kappa_j/t_ref`, `eps = 0`, `h = theta`,
      `a^sharp = 0`.  The equality `eq:reference-all-columns` verifies the
      orientation; the reference restriction is a full product, so its
      balancedness error is exactly zero; and `q/4 >= t_ref` makes all three
      values of `r'` legal."
    * **`09:328--331`, the conclusion consumed here**: "The conclusion is
      precisely `comp<U,1,y_*/2^j,theta> >= C + log_2 q - 1 - j`."
    * **`09:333`, the deliverable**: "This proves `eq:wrapper-u-low`."
    * `eq:wrapper-u-low` itself, `09:264--266` (label `09:266`), inside
      `thm:first-wrapper` (`09:238--272`): "`comp<U,1,y/2^j,theta> >= C + r - 1 - j`
      `(j = 0,1,2)`".
    * `09:277--283`, "Fix `j in {0,1,2}`, and put `kappa_j = q/2^j`" -- the
      frozen range of `j` and the frozen capacity, both consumed by pin from the
      banked `WrapperLowRungs.kappaLow`.
    * `eq:wrapper-low-simple-gate` (label `09:306`, display `09:304--307`),
      `q x_T <= 4/25025`, the block-owned gate from which the endpoint's
      `A:118` guard `t x <= 1` and the `A:112` guard `x <= 1` are **derived**
      here rather than assumed.
    * `09:240`, "Assume `C >= 3`" -- the frozen ambient guard that supplies
      `A:111`'s `H >= 2` at `H = C - 1`.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    * `A:109--146` (`thm:certified-localized-extension`, label `A:110`), with
      the ambient guards `A:111--112`, the width binder `A:117--118`, the copy
      binders `A:125`, the family clause `A:126--128`, the parameter clause
      `A:128--129`, `eq:certified-E1` (`A:131--134`), `eq:certified-E2`
      (`A:135--136`), the restriction bundle `A:138--141`, and the conclusion
      `eq:certified-E3` (`A:142--145`).  **Nothing in this module restates any
      of it**: the whole interface is consumed by pin from the banked
      `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall` and
      `CertifiedLocalizedExtension.certifiedE3_at_canonicalCall`.
    * `A:16--18` (`y_* = 3/5`) and `A:104--107` (`t_0(3/5)` means `t_cert`),
      consumed by pin as `CertifiedLocalizedExtension.yStar` and `.tCert`.
    * `A:122`, `h_t = 2^{-2^{0.49 sqrt(log_2 t)}}`, consumed by pin as
      `HardSeedFacade.hardSeedColumnDensity` at `log_2 t`.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    * **`06:557--572` (`eq:tref-search`, label `06:571`), the three-clause
      certified-reference search**, whose second and third clauses are the two
      displays this module turns into `eq:certified-E1` and `eq:certified-E2`:
      "`k_ref >= max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}`,
      `2^{k_ref-1} >= C_cert - 1 + log_2 q + L_theta`,
      `2^{j_49(k_ref)} >= C_cert - 1 + k_ref + L_theta`,
      `t_ref = 2^{k_ref}`", with `06:573--578`: "The `clog_2(t_0(3/5))` term
      verifies the sufficiently-large-width hypothesis ...; the remaining parts
      of the first two inequalities verify the width and column-loss hypotheses
      for the full-product reference family, while the third verifies its
      hard-seed comparison."
    * **`06:533--535` (`eq:Q-theta-choice`, label `06:537`), the defining
      display of `L_theta`**: "`theta = c_theta/(2Q) = delta/(16Q)`,
      `L_theta = clog_2(1/theta)`", with `06:539` "Here `1/theta = 160Q` is an
      integer because `delta = 1/10`".  `lTheta` reifies that display; no
      numeral is assigned in its place.
    * **`06:71--78`, the defining display of `j_49`**: "No real logarithm or
      square root is evaluated by the reduction.  For a rational `z >= 1` and
      integer `k >= 0`, define `clog_2(z) = min{j >= 0 : z <= 2^j}`,
      `j_49(k) = max{j >= 0 : 10000 j^2 <= 2401 k}`", together with
      `eq:j49-window` (`06:82--85`), `j_49(k) <= 0.49 sqrt k < j_49(k)+1`,
      `06:89` (`P_k(j) <=> 10000 j^2 <= 2401 k`), `eq:j49-search-data`
      (`06:92--98`), and `06:101--103`: "zero proves nonemptiness, `k` is an
      explicit finite-support bound, and **any lower bound on `j_49(k)` used
      below must come from a displayed feasible candidate followed by that
      eliminator**".  `P_k(j)` is reified once, by the banked owner
      `RawLowProfileBody.J49Feasible`, which is consumed here by pin (see the
      DUPLICATE EXCISION note below), and the E2 leg below follows exactly that
      protocol.
    * `eq:kref-tested-endpoint` (`06:586--590`), "`k_ref^* = 100 L_P^2`,
      `j_ref^* = 4 L_P`" -- the paper's own **closed-form** tested endpoint of
      the reference search, which is the value the non-vacuity instance below
      is exhibited at (never a numeral of ours).
    * `eq:Ccert` (`06:430--433`), `C_cert = B_cap + log_2 q_2 + log_2 s + 1`,
      with `06:435--437`: "In a `NO` instance it equals the exact complexity
      `C` of the protected Stage-4 transpose; in a `YES` instance it is only a
      certified target used to choose later widths."  `thm:first-wrapper`'s
      lower bounds are the `NO`-case ones (`09:259`), so `C_cert = C` there;
      the two legs below are therefore stated at the **single natural `C`**, and
      the identification is recorded in §3 rather than performed silently.
  * `02-mechanical-contract.tex`
    (SHA-256 `019209B4EDF21015507148310EFBED757A83FD7709CF3880E178A4C535097A3D`):
    * `02:852--858`, the paper's own use of the `j_49` eliminator at the tested
      endpoint: "For the candidate `k^* = 100 L_P^2`, the exact comparison
      `10000(4L_P)^2 = 160000 L_P^2 <= 240100 L_P^2 = 2401 k^*` gives
      `j_49(k^*) >= 4 L_P`", and `02:858--866`, "after a particular `X` is
      fixed, the two exponential rows `2^{k^*-1} >= C_cert - 1 + X L_P^2 +
      L_theta`, `2^{j_49(k^*)} >= C_cert - 1 + k^* + L_theta` and the fixed
      lower bounds in `eq:tref-search` hold beyond cutoffs returned by the
      integer persistence rules".  This is the exact shape of the non-vacuity
      instance below.

## What is consumed by pin, and what is authored

**Consumed by pin, never restated:**

* `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall` -- the frozen
  `09:313--323` substitution.  It appears here only as a hypothesis; this module
  writes no second copy of it and no second copy of
  `CertifiedExtensionEndpoint`.
* `CertifiedLocalizedExtension.certifiedE3_at_canonicalCall` -- the only route
  from the substitution to `eq:certified-E3`, fired in actual proof terms by
  `certifiedE3_at_lowRung`.
* `CertifiedLocalizedExtension.canonicalCall_matches_low_rung` -- the identity
  `(C-1) + (k_q - j) = C + k_q - 1 - j` reconciling `09:329--331` with
  `eq:wrapper-u-low`.
* `CertifiedLocalizedExtension.tCert`, `.yStar`, `.CertifiedE3`,
  `HardSeedFacade.hardSeedColumnDensity`, and
  `RestrictionDatum.RestrictionDatum`.
* `WrapperLowRungs.simple_gate_forces_tRef_row_legality` -- `A:118` derived from
  `eq:wrapper-low-simple-gate`; `WrapperLowRungs.wrapperLowRungs` -- the
  per-member-to-family passage of `09:333`; `WrapperLowRungs.firstWrapperOfLowRungs`
  -- the `hLowRungs` retirement inside `thm:first-wrapper`.

**Authored here** (and nowhere else in `src/`): the two schedule-side legs, i.e.
`eq:certified-E1` and `eq:certified-E2` derived from the second and third
clauses of `eq:tref-search`; the reification of `L_theta` (`06:535`); and the
low-rung wiring that carries `09:329--331` into `eq:wrapper-u-low` at the family
level.  The `j_49` feasibility predicate `P_k(j)` (`06:89`) is **not** reified
here -- it is the banked `RawLowProfileBody.J49Feasible`, consumed by pin since
the `cc-t7z` excision -- and neither is its tested-endpoint inhabitation, which
is the banked `ParameterSchedule.kref_j49_candidate`.

## What is NOT done here

* **The canonical instance stays deferred to the construction.**  Inhabiting
  `CanonicalReferenceStoppingCall` needs `G`, `x_T`, `theta` and the routed
  restriction of the reference family, none of which is built, and `A:117`
  forces `t_ref >= t_cert = 2^{2^20}`, so no legal instance is `decide`-computable.
  Every declaration below therefore takes the call as a **named binder**; there
  is no probe standing in for it, no synthetic inhabitant, and no conditional
  shell dressed up as a discharge.  The canonical-inhabitation obligation stays
  ledger-registered against `CERTIFIED-LOCALIZED-EXTENSION-001` and is
  discharged only when the reference construction lands.
* **`hDenseRung` is neither discharged nor fed.**  `eq:wrapper-u-dense`
  (`09:262--263`) is the content of `09:335--1781` and remains a binder of
  `firstWrapper_of_canonicalCall`, exactly as it is a binder of the banked
  `WrapperLowRungs.firstWrapperOfLowRungs`.  Nothing here concludes it, weakens
  it, or supplies data to it.
* **Branch 1 of the terminal two-stream dispatch stays owed the inherited
  interface.**  `09:1014--1019` invokes the *inherited* Localized Extension
  corollary at the fixed physical width `t_2` -- call (ii) of `06:1140--1145` --
  which `A:4--8` records is a **different theorem** from
  `thm:certified-localized-extension`.  It is stated nowhere in this module and
  is not affected by anything proved here.
* No route completion is claimed.  `thm:first-wrapper` is not proved; one of its
  two deferred halves is wired to a registered, still-uninhabited interface.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/A-stage4-details.tex`
(SHA-256 `5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`),
opened first-hand this tranche.  **No reader item is claimed here**, and the
survey that establishes that is:

* The reader's rung display at lines `361--368`
  (`D_U(1; 3/(5.2^j), theta) >= C + r_q - 1 - j`) is the reader counterpart of
  `eq:wrapper-u-low`, and it is **already assigned** to
  `WrapperLowRungs.wrapperLowRungs`.  Reassigning it here would be a double
  assignment, which the reader-counterpart rule bars.  `DenseWrapperFrontier`,
  `WrapperProjectionCovers`, `TwoStreamState`, `TerminalFixedBin`,
  `TerminalStageThreeLift`, `TerminalTwoStream` and `Stage3ProtocolRouting` all
  already record the same assignment.
* Lines `361--364` ("retain the reference portion of each outer copy and use
  block balancing ... Localized Extension applied to
  `eq:paper-reference-profile` yields") are the proof recipe.  They are
  unnumbered prose inside a proof body, and citing prose as a statement
  counterpart is barred; `FirstWrapperAssembly` already records line `363` as a
  declined near miss on exactly those grounds.
* The reader's own Localized Extension statement,
  `cor:paper-localized-extension` (`reader-facing/sections/02-preliminaries.tex:512--527`),
  is the **uncertified** corollary -- no `t >= t_cert`, no `h_t`, no
  `eq:certified-E1/E2` -- and `WrapperLowRungs` already records why citing it
  for the certified endpoint would be a false counterpart.  The same reasoning
  applies verbatim to the E1/E2 legs below.
* **Scoped, and corrected at the bytes.**  `A-stage4-details.tex` -- the reader
  file this survey is scoped to -- prints no `t_ref`, no `k_ref`, no `L_theta`,
  no `C_cert`, no `eq:tref-search` and no schedule search at all.  The reader
  *does* print `j_49`, in a **different** file: `eq:paper-j49-definition`
  (`reader-facing/sections/03-parameterized-construction.tex:42--46`,
  `j_49(k) := max{j in N : 10000 j^2 <= 2401 k}`) and its two uses at `03:64`
  and `03:66`.  That display is **already assigned**, to `ParameterSchedule.j49`
  (`docs/BANKED_SURFACE_INDEX.md`, `eq:paper-j49-definition`), so claiming it
  here would be a double assignment; and the following sentence "`j_49(k)` is
  the largest integer at most `(49/100) sqrt k`" (`03:47--48`) is **unnumbered
  prose**, which this module's own recorded rule bars from being cited as a
  statement counterpart.  No reader item is claimed here on those grounds, not
  on a route-wide absence of `j_49`.  The schedule declarations below therefore
  carry their autoformalization and parameter-schedule anchors alone.
* Reader lines `370` onward are the near-full rung outline; they remain the
  dense rung's content and are untouched here.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the schedule scalar `L_theta` (`06:535`), general (3): `lTheta_two_pow`,
  `lTheta_mono`, `two_rpow_neg_lTheta_le`.
* `B` the `j_49` feasibility predicate (`06:89`, `06:92--98`), **consumed by pin
  from the banked owner** `RawLowProfileBody.J49Feasible` -- see the DUPLICATE
  EXCISION note below.  The two frozen search-certificate clauses `P_k(0)` and
  `P_k(j) => j <= k` are the owner's `J49Feasible.zero` and
  `J49Feasible.le_index` and are **not** restated here.  Authored here, general
  (2): `j49Feasible_le_sqrt`, `j49Feasible_two_rpow_le`.  The canonical
  inhabitation at the tested endpoint is likewise **consumed by pin**, from
  `ParameterSchedule.kref_j49_candidate`; see the REMOVED-DECLARATIONS note in
  §1 below.
* `C` the descent lemma the two side legs share, general (1):
  `two_rpow_neg_le_mul_of_floor`.
* `D` the two certified side inequalities at the canonical substitution and
  their joint satisfiability, general (4): `certifiedE1_of_trefSearch`,
  `certifiedE2_of_trefSearch`, `tested_endpoint_quartic_bound`,
  `trefSearch_tested_endpoint_is_satisfiable`.
* `E` the low-rung wiring, general (4): `certifiedE3_at_lowRung`,
  `lowRungMember_of_certifiedE3`, `wrapperLowRungs_of_canonicalCall`,
  `firstWrapper_of_canonicalCall`.
* `F` statement poles (3) and the gate-set non-vacuity (2):
  `certifiedE3_at_lowRung_is_not_free`, `lowRung_needs_the_width_legality`,
  `lTheta_floor_is_not_free`, `lowRung_block_gates_are_satisfiable`,
  `lowRung_full_gate_set_is_satisfiable`.

That is **19 battery entries proved**, with `0` unproved, of which three are
statement poles and three are LANE-GATE 3 non-vacuity instances at paper-derived
values (the last of them putting the whole gate set at **one** reference width).
No canonical-inhabitation lemma is authored here any more: that instance is
consumed by pin.  The module has **20** source declarations in all: 1 definition
(`lTheta`) and 19 theorems, with **0** `structure`s, **0** `inductive`s,
**0** `abbrev`s, **0** `instance`s and **0** `axiom`s.  (The battery count is
`20 - 1` because `lTheta` is the one definition and every remaining declaration
is a battery entry.)

## DUPLICATE EXCISION (`IsJ49Candidate`, class `S`)

This module previously carried a second reification of the frozen `P_k(j)`
display, `def IsJ49Candidate (k j : Nat) : Prop := 10000 * j ^ 2 <= 2401 * k`,
together with `isJ49Candidate_zero` and `isJ49Candidate_le`.  Those three
declarations were **statement-identical** to the earlier banked owner
`RawLowProfileBody.J49Feasible` (same frozen display `06:88--90`, same Lean
body, byte for byte) and its `J49Feasible.zero` / `J49Feasible.le_index`.  They
are **deleted**; every consumer in `src/` now pins the owner.

Direction of the pin is *forced*, not chosen: `RawLowProfileBody` is already in
this module's import closure (through `CertifiedLocalizedExtension`), so the pin
adds **no** import and **no** axiom surface, while the opposite direction --
pinning the wrapper name from `RawLowProfileBody` -- would create an import
cycle.  The owner additionally carries `J49Feasible.mono`, which the deleted
copy never had, so the pin is a strict gain.

**The name `IsJ49Candidate` is BARRED.**  It must not be reintroduced in `src/`,
in `tools/AxiomAudit.lean`, or in a card; the `j_49` feasibility predicate has
exactly one Lean owner and it is `RawLowProfileBody.J49Feasible`.  The two
lemmas this module still authors over that predicate are renamed to
`j49Feasible_*` so the barred name survives nowhere in the surface.

## Canonical inhabitation

This module introduces **no type at all** after the excision: `lTheta` is a
definition, not a structure, and its paper instance is `06:535` at `1/theta`,
recorded by `lTheta_two_pow`.

The canonical inhabitation of the pinned predicate is **consumed here, not
owned**.  The paper prints the same arithmetic twice -- at `02:852--858` inside
the mechanical contract and at `eq:kref-j49-candidate` (`06:615--621`) inside the
schedule -- and the `06` print is already banked as
`ParameterSchedule.kref_j49_candidate` (`ParameterSchedule.lean:1360`) over the
schedule's own `krefStar` / `jrefStar` (`:1349`, `:1353`).  The `cc-t7z-r1` gate
ruled this module's re-proof from the `02` print a statement-identical duplicate
of that owner; it is deleted, and `trefSearch_tested_endpoint_is_satisfiable`
takes the owner by pin.

No new `structure` is declared here, so no further inhabitation obligation is
created.  The **inherited** deferred obligation -- canonical inhabitation of
`CanonicalReferenceStoppingCall` -- is unchanged and stays registered.

## Proof status and axiom surface

Adapted (the frozen argument, in the frozen order) plus new (the two schedule
legs).  Imports: `EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension`
alone, whose closure carries `WrapperLowRungs`, `ScaleAlignOpening`,
`HardSeedFacade` and `RestrictionDatum`.  `LegacyNPCC.Stage12` is **not**
entered, so the cited AGHP balanced-family axiom is outside this module's
closure.  `#print axioms` on every declaration below is recorded in
`tools/AxiomAudit.lean`; the surface is `propext`, `Classical.choice`,
`Quot.sound` only.  No project axiom, no unproved placeholder, no new opaque
certificate.

## HYPOTHESIS-CONSISTENCY note

The headline deliverables `wrapperLowRungs_of_canonicalCall` and
`firstWrapper_of_canonicalCall` conjoin only hypotheses the frozen text states
about **one** case of **one** construction: `thm:first-wrapper`'s `NO`-case
guards (`09:240`, `09:259`), `eq:wrapper-low-simple-gate` (`09:304--307`),
`09:327`'s width legality, the `eq:tref-search` floor, and the two side legs.
They are not the three branches of the terminal dispatch and not the two promise
cases; nothing here assumes both a `YES` and a `NO` clause.  Their joint
satisfiability at the integer half is the banked
`CertifiedLocalizedExtension.canonicalCall_gates_nonvacuous`, at the schedule
half it is `trefSearch_tested_endpoint_is_satisfiable`, and at **one shared
reference width** -- integer, schedule and density gates together -- it is
`lowRung_full_gate_set_is_satisfiable`.
-/

namespace EthInapproximability.ParameterizedNP.WrapperLowRungAssembly

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.HardSeedFacade
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension

/-! ## §1  The two schedule scalars: `L_theta` (`06:535`) and `P_k(j)` (`06:89`)

Both are quantities the frozen source **defines**, so both are reified as Lean
definitions tracing their defining displays; neither is ever replaced by a
numeral, and no value below is obtained by searching for something that fits the
locally visible constraints. -/

section Schedule

/-- **`L_theta = clog_2(1/theta)` (`06:535`), reified.**

`eq:Q-theta-choice` (`06:525--538`) closes with the defining display
`L_theta = clog_2(1/theta)`, and `06:539` records that "`1/theta = 160Q` is an
integer because `delta = 1/10`", so the argument of `clog_2` is a natural number
and Mathlib's `Nat.clog 2` is the frozen `clog_2(z) = min{j >= 0 : z <= 2^j}` of
`06:75--76` on the nose.

This is a *definition*, not a bound: every occurrence of `L_theta` below is this
expression evaluated at `1/theta`, never an assigned numeral. -/
def lTheta (n : ℕ) : ℕ := Nat.clog 2 n

/-- **Aux A1 (the round-trip fact certifying the reification).**  The frozen
`clog_2(z) = min{j >= 0 : z <= 2^j}` of `06:75--76` must return `n` at `z = 2^n`,
and Mathlib's `Nat.clog 2` does, which is the check that `lTheta` is that display
and not some neighbouring rounding.  This is a *general* round-trip identity at
exact powers of two; it is **not** claimed to fire at the schedule's own
`1/theta = 160Q` (`06:539`), which is `2^{a+5} . 5` and so not a power of two.
General in the exponent. -/
@[simp] theorem lTheta_two_pow (n : ℕ) : lTheta (2 ^ n) = n :=
  Nat.clog_pow 2 n (by norm_num)

/-- **Aux A2 (monotone in the reciprocal density).**  A smaller `theta` means a
larger `1/theta` and hence a larger `L_theta`; the schedule displays
`06:564--567` subtract `L_theta` from an exponential budget, so this is the
direction in which the search gets harder.  General. -/
theorem lTheta_mono {m n : ℕ} (h : m ≤ n) : lTheta m ≤ lTheta n :=
  Nat.clog_mono_right 2 h

/-- **Aux A3 (`06:535` as the inequality the two side legs consume), PROVED.**

The only property of `L_theta` that `eq:certified-E1` and `eq:certified-E2` use
is `2^{-L_theta} <= theta`, and it is a *consequence* of the defining display,
not an extra assumption: `clog_2` is the least exponent with `1/theta <= 2^j`,
so `1/theta <= 2^{L_theta}` and hence `2^{-L_theta} <= theta`.

The hypothesis `(n : R) = 1/theta` is the frozen `06:539` integrality; nothing
here assumes anything about `Q` or `delta`.  General in `n` and `theta`. -/
theorem two_rpow_neg_lTheta_le {n : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hn : (n : ℝ) = 1 / θ) :
    (2 : ℝ) ^ (-((lTheta n : ℕ) : ℝ)) ≤ θ := by
  have hle : (n : ℕ) ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have hcast : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 n) := by exact_mod_cast hle
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 n) := by positivity
  have hrw : (2 : ℝ) ^ (-((lTheta n : ℕ) : ℝ)) = ((2 : ℝ) ^ (Nat.clog 2 n))⁻¹ := by
    rw [lTheta, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hmul : 1 ≤ (2 : ℝ) ^ (Nat.clog 2 n) * θ := by
    have hstep := mul_le_mul_of_nonneg_right hcast (le_of_lt hθ0)
    rw [hn, one_div, inv_mul_cancel₀ (ne_of_gt hθ0)] at hstep
    exact hstep
  rw [hrw, inv_eq_one_div, div_le_iff₀ hpos]
  linarith [hmul]

/-! ### The `j_49` feasibility predicate: pinned, never re-reified

**DUPLICATE EXCISION (class `S`).**  `P_k(j)` (`06:88--90`) has exactly one Lean
owner, the banked `RawLowProfileBody.J49Feasible`, whose declaration transcribes
the same frozen display and whose `J49Feasible.zero` (`06:93`) and
`J49Feasible.le_index` (`06:94`, justified at `06:99--100`) are the first two
clauses of `eq:j49-search-data`.  This module's former `IsJ49Candidate`,
`isJ49Candidate_zero` and `isJ49Candidate_le` were byte-identical restatements of
those three and have been **deleted**; the owner is consumed by pin below and the
name `IsJ49Candidate` is **barred**.  `06:101--103` still fixes the only legal way
to use the predicate downwards -- "any lower bound on `j_49(k)` used below must
come from a displayed feasible candidate followed by that eliminator" -- and a
*feasible candidate* is exactly an inhabitant of the pinned owner.
-/

/-- **Aux B3 (`eq:j49-window` (`06:82--85`) at a feasible candidate), PROVED.**

`j_49(k) <= 0.49 sqrt k`, and by the `06:95` eliminator every feasible candidate
is at most `j_49(k)`, so every feasible candidate satisfies the same real bound.
This is the single place where the frozen `0.49 = 49/100` and a real square root
meet the integer predicate; `06:86` records that "the square root appears only in
the analysis of this exact integer predicate".  General. -/
theorem j49Feasible_le_sqrt {k j : ℕ} (h : RawLowProfileBody.J49Feasible k j) :
    (j : ℝ) ≤ (49 / 100 : ℝ) * Real.sqrt (k : ℝ) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0
  have hs0 : (0 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hnat : 10000 * j ^ 2 ≤ 2401 * k := h
  have hcast : 10000 * (j : ℝ) ^ 2 ≤ 2401 * (k : ℝ) := by exact_mod_cast hnat
  nlinarith [hsq, hs0, hj0, hcast, sq_nonneg ((j : ℝ) - 49 / 100 * Real.sqrt (k : ℝ))]

/-- **Aux B4 (the candidate exponent is dominated by the frozen `h_t` exponent),
PROVED.**

`A:122` writes the certified hard-seed density at the *real* exponent
`2^{0.49 sqrt(log_2 t)}`, while `eq:tref-search`'s third clause is checked at the
*integer* `2^{j_49(k_ref)}`.  `06:1249` records the bridge, "`2^{0.49 sqrt k_2}
>= 2^{j_49(k_2)}`"; this is that bridge at an arbitrary feasible candidate, which
is the form `06:101--103` permits.  General. -/
theorem j49Feasible_two_rpow_le {k j : ℕ} (h : RawLowProfileBody.J49Feasible k j) :
    ((2 : ℝ) ^ (j : ℕ)) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (k : ℝ)) := by
  have hle := j49Feasible_le_sqrt h
  have hstep : (2 : ℝ) ^ ((j : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
  rwa [Real.rpow_natCast] at hstep

/-! ### Two declarations REMOVED by the `cc-t7z-r1` gate, and what replaces them

* `j49Feasible_two_rpow_le_of_le` -- the `A:122` bridge at every index below a
  displayed candidate, obtained from the owner's `RawLowProfileBody.J49Feasible.mono`.
  It was **externally unwired** (zero consumers anywhere in `src/`) and it
  contains `j49Feasible_two_rpow_le` above as its `i := j` specialization, so as
  a *published* surface it republished a banked statement.  Deleted on the gate's
  ruling.  It is **strictly stronger** than the surviving lemma and is **not**
  derivable from it (its proof consumes `.mono`), so the direction is not lost:
  the ledger records it as re-proposable **with** a consumer, and a genuinely
  needed strict-descent interface would instead assume `i < j`.

* `j49Feasible_at_tested_endpoint` -- the canonical inhabitation at the paper's
  closed form.  It was a name-distinct, **statement-identical** duplicate of the
  banked owner `ParameterSchedule.kref_j49_candidate` (`ParameterSchedule.lean:1360`,
  `eq:kref-j49-candidate`, `06:615--621`), whose statement
  `J49Feasible (krefStar LP) (jrefStar LP)` unfolds -- `krefStar LP = 100 * LP^2`
  (`:1349`), `jrefStar LP = 4 * LP` (`:1353`), both plain `def`s -- to exactly the
  statement this module re-proved from the `02:852--858` print of the same
  arithmetic.  `ParameterSchedule` is already in this module's import closure, so
  the owner is **consumed by pin** at the one site that used it,
  `trefSearch_tested_endpoint_is_satisfiable` below.  The module's canonical
  inhabitation of `J49Feasible` at the tested endpoint is therefore **consumed,
  not owned**.
-/

/-- **Statement pole (the `L_theta` floor is not free).**

`two_rpow_neg_lTheta_le` would be worthless if `2^{-L}` were below every positive
real for every `L`; the content is that `L_theta` is the *least* such exponent,
so lowering it by one already fails at the frozen shape.  Exhibited at
`1/theta = 2^{n+1}`, where `L_theta = n+1` and the candidate `n` gives
`2^{-n} = 2/theta . theta^2 > theta` for the frozen `theta < 1`.

*Why the trivial witness fails.*  The claim is an inequality that is **false**,
so no witness makes it true; that is exactly the point.  General in `n`. -/
theorem lTheta_floor_is_not_free (n : ℕ) :
    ¬ ((2 : ℝ) ^ (-((n : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ (n + 1 : ℕ))⁻¹) := by
  intro hcon
  have h1 : (2 : ℝ) ^ (-((n : ℕ) : ℝ)) = ((2 : ℝ) ^ (n : ℕ))⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) := by positivity
  rw [h1, pow_succ] at hcon
  rw [inv_le_inv₀ hpos (by positivity)] at hcon
  nlinarith [hpos]

end Schedule

/-! ## §2  The descent lemma the two certified side legs share -/

section Descent

/-- **Aux C1 (the shared descent step), PROVED.**

Both `eq:certified-E1` and `eq:certified-E2` have the shape "a power `2^{-E}` is
below `theta . 2^{-A}`", and in both the schedule supplies exactly
`A + L_theta <= E`.  Splitting `2^{-(A+L)} = 2^{-L} . 2^{-A}` and using
`2^{-L_theta} <= theta` (Aux A3) closes both.  Stated on bare reals, general in
`A`, `E`, `L` and `theta`, so neither leg re-derives it. -/
theorem two_rpow_neg_le_mul_of_floor {A E L θ : ℝ} (hsum : A + L ≤ E)
    (hθ : (2 : ℝ) ^ (-L) ≤ θ) : (2 : ℝ) ^ (-E) ≤ θ * (2 : ℝ) ^ (-A) := by
  have h1 : (2 : ℝ) ^ (-E) ≤ (2 : ℝ) ^ (-(A + L)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(A + L)) = (2 : ℝ) ^ (-L) * (2 : ℝ) ^ (-A) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have h3 : (0 : ℝ) < (2 : ℝ) ^ (-A) := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : (2 : ℝ) ^ (-L) * (2 : ℝ) ^ (-A) ≤ θ * (2 : ℝ) ^ (-A) :=
    mul_le_mul_of_nonneg_right hθ (le_of_lt h3)
  rw [h2] at h1
  linarith

end Descent

/-! ## §3  `eq:certified-E1` and `eq:certified-E2` at the `09:313--323` substitution

`06:573--578` assigns the two exponential clauses of `eq:tref-search` to exactly
these two hypotheses of `thm:certified-localized-extension`.  Both legs are
stated at the substitution `H = C-1`, `t = t_ref = 2^{k_ref}`,
`r = q/t_ref = 2^{k_q-k_ref}`, `h = theta`, `eps = 0` of `09:317--323`, i.e. in
the exact shape `CertifiedLocalizedExtension.certifiedE3_at_canonicalCall`
demands, so that no rewriting happens at the call site.

The schedule writes `C_cert` where the wrapper writes `C`.  `06:435--437` is the
identification -- "In a `NO` instance it equals the exact complexity `C` of the
protected Stage-4 transpose; in a `YES` instance it is only a certified target
used to choose later widths" -- and `thm:first-wrapper`'s lower bounds are the
`NO`-case ones (`09:259`), which is the only case `sec:wrapper-low-rungs` argues
in.  The two legs are therefore stated at the single natural `C`, and the
identification is **recorded here rather than performed silently**: in the `YES`
case `C_cert` is not a complexity and these legs must not be fired at it. -/

section SideLegs

/-- **`eq:certified-E1` (`A:131--134`) from `eq:tref-search`'s second clause,
PROVED.**

`06:564--565` is `2^{k_ref-1} >= C_cert - 1 + log_2 q + L_theta`.  With
`C_cert = C` (`06:435--437`, the `NO` case of `09:259`), `log_2 q = k_q`, and
`2^{-L_theta} <= theta` (Aux A3), this gives the frozen `eq:certified-E1` at
`eps = 0` in its `t`-th power form,
`y_*^{t_ref} <= theta . 2^{-(H + log_2 q)}/(1+eps)`.

The single numeric step is the frozen one: `y_*^2 = 9/25 <= 1/2`, i.e.
`log_2(5/3) >= 1/2`, which is exactly why `2^{k_ref-1}` -- rather than
`t_ref log_2(5/3)` -- is the quantity the schedule checks.  Nothing is rounded:
`t_ref = 2^{k_ref} = 2 . 2^{k_ref-1}` exactly, at `k_ref >= 1`.

General in `C`, `k_q`, `k_ref`, `theta` and the exponent `L`. -/
theorem certifiedE1_of_trefSearch {C kq kref : ℕ} {θ L : ℝ}
    (hk1 : 1 ≤ kref) (hkq : kref ≤ kq)
    (hsched : ((C - 1 : ℕ) : ℝ) + (kq : ℝ) + L ≤ (2 : ℝ) ^ (kref - 1))
    (hθ : (2 : ℝ) ^ (-L) ≤ θ) :
    yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + ((kq - kref : ℕ) : ℝ) + (kref : ℝ)))
        / (1 + (0 : ℝ)) := by
  set N : ℕ := 2 ^ (kref - 1) with hN
  have hsplit : (2 : ℕ) ^ kref = 2 * N := by
    rw [hN, ← pow_succ']
    congr 1
    omega
  -- the frozen numeric step `y_*^2 = 9/25 <= 1/2`
  have hbase : yStar ^ ((2 : ℕ) ^ kref) ≤ ((1 : ℝ) / 2) ^ N := by
    rw [hsplit, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    rw [yStar_eq]
    norm_num
  have hhalf : ((1 : ℝ) / 2) ^ N = (2 : ℝ) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  -- the exponent identity of the substitution
  have hexp : ((kq - kref : ℕ) : ℝ) + (kref : ℝ) = (kq : ℝ) := by
    have : (kq - kref) + kref = kq := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  have hNle : ((C - 1 : ℕ) : ℝ) + (kq : ℝ) + L ≤ (N : ℝ) := by
    rw [hN]
    push_cast
    exact_mod_cast hsched
  have hmain := two_rpow_neg_le_mul_of_floor
    (A := ((C - 1 : ℕ) : ℝ) + (kq : ℝ)) (E := (N : ℝ)) (L := L) (θ := θ)
    (by linarith) hθ
  have hfinal : yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kq : ℝ))) :=
    le_trans (hbase.trans_eq hhalf) hmain
  calc yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kq : ℝ))) := hfinal
    _ = θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + ((kq - kref : ℕ) : ℝ) + (kref : ℝ)))
          / (1 + (0 : ℝ)) := by
        rw [add_assoc, hexp]
        norm_num

/-- **`eq:certified-E2` (`A:135--136`) from `eq:tref-search`'s third clause,
PROVED.**

`06:566--567` is `2^{j_49(k_ref)} >= C_cert - 1 + k_ref + L_theta`, and
`06:101--103` fixes how a lower bound on `j_49` is supplied: by a displayed
feasible candidate plus the eliminator.  So the hypothesis here is a feasible
candidate `j` (`RawLowProfileBody.J49Feasible k_ref j`, the pinned owner)
together with the schedule display
checked at `2^j`, which is exactly the mechanical protocol `02:855--858` runs.

The conclusion is the frozen `h_t <= h 2^{-(H+log_2 t)}/(1+eps)` at
`h_t = HardSeedFacade.hardSeedColumnDensity k_ref` (`A:122`, consumed by pin),
`h = theta`, `H = C-1`, `log_2 t = k_ref`, `eps = 0`.

General in `C`, `k_ref`, the candidate `j`, `theta` and `L`. -/
theorem certifiedE2_of_trefSearch {C kref j : ℕ} {θ L : ℝ}
    (hcand : RawLowProfileBody.J49Feasible kref j)
    (hsched : ((C - 1 : ℕ) : ℝ) + (kref : ℝ) + L ≤ (2 : ℝ) ^ (j : ℕ))
    (hθ : (2 : ℝ) ^ (-L) ≤ θ) :
    hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) / (1 + (0 : ℝ)) := by
  have hbridge := j49Feasible_two_rpow_le hcand
  have hfloor : ((C - 1 : ℕ) : ℝ) + (kref : ℝ) + L
      ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (kref : ℝ)) := le_trans hsched hbridge
  have hmain := two_rpow_neg_le_mul_of_floor
    (A := ((C - 1 : ℕ) : ℝ) + (kref : ℝ))
    (E := (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (kref : ℝ))) (L := L) (θ := θ)
    hfloor hθ
  rw [hardSeedColumnDensity_eq_ht kref]
  calc (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (kref : ℝ))))
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) := hmain
    _ = θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) / (1 + (0 : ℝ)) := by
        norm_num

/-- **Aux D3 (the cutoff of `02:865--868`, made explicit), PROVED.**

"the two exponential rows ... hold beyond cutoffs returned by the integer
persistence rules".  This is that cutoff, as an inequality rather than as a
promise: once `L_P` exceeds `103 + C_cert + L_theta`, the quantity
`2^{4 L_P} = 2^{j_ref^*}` already dominates `C_cert + 100 L_P^2 + L_theta + 2`,
and `100 L_P^2 = k_ref^*`.  Only two facts are used, both elementary and both
frozen-free: `m < 2^m`, and `103 m^2 <= m^3` at `m >= 103`.  General. -/
theorem tested_endpoint_quartic_bound {Ccert Ltheta m : ℕ}
    (hm : 103 + Ccert + Ltheta ≤ m) :
    Ccert + 100 * m ^ 2 + Ltheta + 2 ≤ 2 ^ (4 * m) := by
  have hm1 : 1 ≤ m := by omega
  have hs : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm1
  have hCL : Ccert + Ltheta ≤ m ^ 2 := by
    have h1 : Ccert + Ltheta ≤ m := by omega
    have h2 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
    omega
  have h1 : Ccert + 100 * m ^ 2 + Ltheta + 2 ≤ 103 * m ^ 2 := by omega
  have h2 : 103 * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have h3 : m * m ^ 2 ≤ m ^ 4 := by
    have he : m * m ^ 2 = m ^ 3 := by ring
    rw [he]
    exact Nat.pow_le_pow_right hm1 (by norm_num)
  have hlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hpow : m ^ 4 ≤ (2 ^ m) ^ 4 := Nat.pow_le_pow_left (le_of_lt hlt) 4
  have hpow4 : (2 ^ m) ^ 4 = 2 ^ (4 * m) := by
    rw [← pow_mul]; ring_nf
  omega

/-- **LANE-GATE 3 non-vacuity: the three `eq:tref-search` clauses are jointly
satisfiable, at the paper's own tested endpoint, PROVED.**

`certifiedE1_of_trefSearch` and `certifiedE2_of_trefSearch` would compile green
and prove nothing if their schedule hypotheses were jointly unsatisfiable
alongside `A:117`'s floor and `09:327`'s width legality.  They are not, and the
values exhibited are the paper's own closed forms, not numerals of ours:

* `k_ref = k_ref^* = 100 L_P^2` and `j = j_ref^* = 4 L_P` --
  `eq:kref-tested-endpoint` (`06:586--590`), used with the eliminator exactly as
  `02:852--858` uses it;
* `k_q = k_ref + 2` -- the boundary of `09:327`'s "`q/4 >= t_ref` makes all three
  values of `r'` legal", the same paper-derived value the banked
  `canonicalCall_gates_nonvacuous` takes.

`02:865--868` records that these rows "hold beyond cutoffs returned by the
integer persistence rules", and the cutoff is what the `L_P` chosen here makes
explicit: it is a function of the two schedule inputs `C_cert` and `L_theta`, and
of nothing else.

This exhibits **no** restriction datum, no matrix and no real parameters, so it
is *not* canonical inhabitation of the reference stopping call, which remains
ledger-registered and deferred. -/
theorem trefSearch_tested_endpoint_is_satisfiable (Ccert Ltheta : ℕ) :
    ∃ LP kref kq j : ℕ,
      kref = 100 * LP ^ 2 ∧ j = 4 * LP ∧ kq = kref + 2
        ∧ Nat.clog 2 tCert ≤ kref
        ∧ RawLowProfileBody.J49Feasible kref j
        ∧ 1 ≤ kref
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kq : ℝ) + (Ltheta : ℝ) ≤ (2 : ℝ) ^ (kref - 1))
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kref : ℝ) + (Ltheta : ℝ) ≤ (2 : ℝ) ^ (j : ℕ)) := by
  classical
  set m : ℕ := 103 + Ccert + Ltheta with hm
  -- the feasible-candidate clause is the banked owner, consumed by pin:
  -- `ParameterSchedule.kref_j49_candidate` (`:1360`, `eq:kref-j49-candidate`,
  -- `06:615--621`) at `k_ref^* = krefStar m = 100 m^2`, `j_ref^* = jrefStar m = 4 m`
  -- (`ParameterSchedule.lean:1349`, `:1353`).  The two `def`s are unfolded locally
  -- so the pin meets this statement's spelling; nothing is re-proved here.
  have hcand : RawLowProfileBody.J49Feasible (100 * m ^ 2) (4 * m) :=
    ParameterSchedule.kref_j49_candidate m
  refine ⟨m, 100 * m ^ 2, 100 * m ^ 2 + 2, 4 * m, rfl, rfl, rfl, ?_,
    hcand, ?_, ?_, ?_⟩
  · -- `clog_2 t_cert = 2^20 <= 100 m^2`, since `m >= 103`
    have h20 : Nat.clog 2 tCert = 2 ^ 20 := clog_two_tCert
    have hm103 : 103 ≤ m := by omega
    have : (2 : ℕ) ^ 20 ≤ 100 * m ^ 2 := by nlinarith
    omega
  · nlinarith [hm]
  · -- `2^{k_ref-1} >= 2^{4m} >= m^4 >= 100 m^2 + C_cert + L_theta + 2`
    have hquart : Ccert + 100 * m ^ 2 + Ltheta + 2 ≤ 2 ^ (4 * m) :=
      tested_endpoint_quartic_bound (by omega)
    have hmono : (2 : ℕ) ^ (4 * m) ≤ 2 ^ (100 * m ^ 2 - 1) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have hmm : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
      have hm103 : 103 ≤ m := by omega
      omega
    have hnat : (Ccert - 1) + (100 * m ^ 2 + 2) + Ltheta ≤ 2 ^ (100 * m ^ 2 - 1) := by
      have := le_trans hquart hmono
      omega
    exact_mod_cast hnat
  · have hquart : Ccert + 100 * m ^ 2 + Ltheta + 2 ≤ 2 ^ (4 * m) :=
      tested_endpoint_quartic_bound (by omega)
    have hnat : (Ccert - 1) + 100 * m ^ 2 + Ltheta ≤ 2 ^ (4 * m) := by omega
    exact_mod_cast hnat

end SideLegs

/-! ## §4  The wiring: `09:329--331` carried into `eq:wrapper-u-low` (`09:333`)

Three steps, in the frozen order.  First `certifiedE3_at_lowRung` fires the
banked `certifiedE3_at_canonicalCall` at the low-rung indices, discharging from
this block's own data the three antecedents `sec:wrapper-low-rungs` owns:
`A:111`'s `H >= 2` from `09:240`'s `C >= 3`, `A:112`'s `x <= 1` and `A:118`'s
`t x <= 1` from `eq:wrapper-low-simple-gate`, and `09:327`'s exponent legality
`k_ref + j <= k_q` from `q/4 >= t_ref`.  Then `lowRungMember_of_certifiedE3`
rewrites `09:329--331` into the shape `eq:wrapper-u-low` is stated in.  Finally
the two banked compositions lift one member to the family and retire the
`hLowRungs` binder of `thm:first-wrapper`. -/

section Wiring

/-- **`eq:certified-E3` at the low rung (`09:311--331`), PROVED.**

The canonical `09:313--323` substitution enters as the named binder `hcall` and
is **not** restated: `CanonicalReferenceStoppingCall` is the banked registration
of that substitution, and `certifiedE3_at_canonicalCall` is the banked route from
it to `eq:certified-E3`.  What this declaration adds is the discharge, from
`sec:wrapper-low-rungs`' own data, of every antecedent the block owns:

* `2 <= C - 1` (`A:111`), from the frozen `C >= 3` of `09:240`;
* `k_ref + j <= k_q` (`A:125`'s `r' <= r`, i.e. `09:327`'s "`q/4 >= t_ref` makes
  all three values of `r'` legal"), from `k_ref + 2 <= k_q` and `j <= 2`;
* `x_T <= 1` (`A:112`), from `eq:wrapper-low-simple-gate` -- since `2^{k_q} >= 1`
  and `x_T > 0`, `x_T <= q x_T <= 4/25025 <= 1`;
* `t_ref x_T <= 1` (`A:118`), from the same gate through the banked
  `WrapperLowRungs.simple_gate_forces_tRef_row_legality`.

Left as named binders, because they belong to `06` and to the reference
construction, not to this block: `hfloor` (the `eq:tref-search` floor term,
`06:561--563`), `hbase` (`eq:certified-base`, the banked `lem:wrapper-reference`),
`hE1` and `hE2` (supplied by §3), the carrier nonemptiness `A:111`, and the
restriction datum itself.

General in the two matrix carriers, in the restriction carriers, in `C`, `k_q`,
`k_ref`, `j`, `x_T`, `theta` and the readout `val`. -/
theorem certifiedE3_at_lowRung {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (G : Rw → Cl → Bool) {C kq kref j val : ℕ} {xT θ : ℝ}
    (Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ)
    (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ C)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hxT0 : 0 < xT)
    (hgate : ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025)
    (hCl : 1 ≤ Fintype.card Cl)
    (hbase : C - 1 ≤ LambdaGE G 1 xT yStar)
    (hE1 : yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + ((kq - kref : ℕ) : ℝ) + (kref : ℝ)))
        / (1 + (0 : ℝ)))
    (hE2 : hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) / (1 + (0 : ℝ)))
    (hcall : CanonicalReferenceStoppingCall G C kq kref j xT θ Dat val) :
    CertifiedE3 (C - 1) (kq - j) val := by
  -- `A:112`, the upper half, from `eq:wrapper-low-simple-gate`
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ kq := one_le_pow₀ (by norm_num)
  have hx1 : xT ≤ 1 := by nlinarith
  -- `A:118`, from the same gate, through the banked block lemma
  have hguard : ((2 : ℝ) ^ kref) * xT ≤ 1 :=
    simple_gate_forces_tRef_row_legality hq4 (le_of_lt hxT0) hgate
  have htx : (((2 : ℕ) ^ kref : ℕ) : ℝ) * xT ≤ 1 := by
    push_cast
    exact hguard
  exact certifiedE3_at_canonicalCall G Dat hfloor (by omega) hCl (by omega) hxT0 hx1
    hbase htx hE1 hE2 hcall

/-- **`09:329--331` in the shape `eq:wrapper-u-low` is stated in, PROVED.**

`eq:certified-E3` at the canonical substitution reads `(C-1) + (k_q - j) <= val`,
and `09:330--331` states the same number as `C + log_2 q - 1 - j`.  The banked
`CertifiedLocalizedExtension.canonicalCall_matches_low_rung` is the identity
between the two spellings and is consumed by pin here.  What remains is the
subtraction-free rearrangement into the frozen `eq:wrapper-u-low` shape
`C + r <= j + 1 + .`, which is the shape the banked
`WrapperLowRungs.wrapperLowRungs` demands of each member.

Both natural subtractions are exact at the frozen side conditions `C >= 3`
(`09:240`) and `j <= k_q`, so nothing is silently truncated.  General. -/
theorem lowRungMember_of_certifiedE3 {C kq j val : ℕ} (hC : 3 ≤ C) (hj : j ≤ kq)
    (h : CertifiedE3 (C - 1) (kq - j) val) : C + kq ≤ j + 1 + val := by
  have hid : (C - 1) + (kq - j) = C + kq - 1 - j :=
    canonicalCall_matches_low_rung (by omega) hj
  have hun : (C - 1) + (kq - j) ≤ val := h
  omega

/-- **`eq:wrapper-u-low` (`09:264--266`) from the canonical reference stopping
call, PROVED (`09:333`).**

"This proves `eq:wrapper-u-low`."  The per-member hypothesis `hrung` is the
frozen `09:311--327` step, member by member: at each member of
`<U,1,y/2^j,theta>` the construction retains the reference rows, projects to
`9 kappa_j/16` outer coordinates, and applies the certified-scale reference
stopping lemma at the `09:317--323` substitution -- which is precisely the
statement that *some* restriction datum of the reference family carries the
canonical call at that member's own complexity readout.  Everything else is
discharged: the ambient guards by `certifiedE3_at_lowRung`, the arithmetic by
`lowRungMember_of_certifiedE3`, and the passage from members to the family by
the banked `WrapperLowRungs.wrapperLowRungs` (whose `Dfamily` is a `Nat.sInf`,
so the nonemptiness binder `hne` is carried explicitly and never assumed away).

**Nothing here inhabits the call.**  `hrung` is a binder; the reference
construction that would discharge it is unbuilt, and its canonical-inhabitation
obligation stays ledger-registered.

*Why the trivial witness fails.*  The deliverable is a lower bound on a
`Nat.sInf`, and at the constant matrix that infimum is `0` while the demanded
value `C + k_q - 1 - j` is at least `2` -- the banked
`WrapperLowRungs.wrapperLowRungs_not_automatic` exhibits exactly that member.  So
the bound cannot be read off the bracket shape and must come from `hrung`.

General in the carriers, in `N`, `G`, `C`, `k_q`, `k_ref`, and in `x_T`, `theta`
and `y`. -/
theorem wrapperLowRungs_of_canonicalCall {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (Nmat : Rw → Cl → Bool) (G : Rw → Cl → Bool) {C kq kref : ℕ} {xT θ y : ℝ}
    (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ C)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hxT0 : 0 < xT)
    (hgate : ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025)
    (hCl : 1 ≤ Fintype.card Cl)
    (hbase : C - 1 ≤ LambdaGE G 1 xT yStar)
    (hE1 : yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + ((kq - kref : ℕ) : ℝ) + (kref : ℝ)))
        / (1 + (0 : ℝ)))
    (hE2 : hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) / (1 + (0 : ℝ)))
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hrung : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ,
        ∃ Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
            (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ,
          CanonicalReferenceStoppingCall G C kq kref j xT θ Dat
            (D (subgame (interlaceFun (wrapperU Nmat kq) 1) RC.1 RC.2))) :
    ∀ j : ℕ, j ≤ 2 →
      C + kq ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat kq) 1)
        (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ) := by
  refine wrapperLowRungs Nmat kq C hC hne ?_
  intro j hj RC hRC
  obtain ⟨Dat, hcall⟩ := hrung j hj RC hRC
  exact lowRungMember_of_certifiedE3 hC (by omega)
    (certifiedE3_at_lowRung G Dat hj hq4 hC hfloor hxT0 hgate hCl hbase hE1 hE2 hcall)

/-- **`thm:first-wrapper` with `hLowRungs` retired from the canonical call.**

The banked `WrapperLowRungs.firstWrapperOfLowRungs` already retires the
`hLowRungs` binder of `ScaleAlignOpening.firstWrapper` from a per-member rung
bound; this composition supplies that per-member bound from the canonical
reference stopping call instead of from an abstract endpoint implication, and
returns the same seven conclusions verbatim.

The remaining binder set is carried honestly and in full:

* **`hDenseRung`** -- `eq:wrapper-u-dense` (`09:262--263`), whose proof is the
  five blocks `09:335--1781`.  It is neither discharged nor fed here; it is
  passed straight through.
* `hne` and `hrung` -- bracket nonemptiness and the per-member canonical call,
  the latter still awaiting the reference construction.
* `hN` (`comp N = C`, `09:241`), the carrier nonemptiness, and the density
  guards, exactly as `firstWrapperOfLowRungs` states them.

Nothing is weakened: `y`, `theta` and `delta_U` are quantified exactly as they
are there, and the seven conclusions -- including
`eq:common-exact`--`eq:common-low` for `W = U^T` -- are returned unchanged.  This
is a **composition**, not a proof of `thm:first-wrapper`: one of its two deferred
halves now depends on a registered, still-uninhabited interface rather than on an
abstract implication binder, and the other half is untouched. -/
theorem firstWrapper_of_canonicalCall {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (Nmat : Rw → Cl → Bool) (G : Rw → Cl → Bool) {C kq kref : ℕ} {δU xT θ y : ℝ}
    (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < 1 - δU) (hδ1 : 1 - δU ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hxT0 : 0 < xT)
    (hgate : ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE G 1 xT yStar)
    (hE1 : yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + ((kq - kref : ℕ) : ℝ) + (kref : ℝ)))
        / (1 + (0 : ℝ)))
    (hE2 : hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) / (1 + (0 : ℝ)))
    (hDenseRung : C + kq ≤ Dfamily (interlaceFun (wrapperU Nmat kq) 1)
      (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (1 - δU) θ))
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hrung : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ,
        ∃ Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
            (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ,
          CanonicalReferenceStoppingCall G C kq kref j xT θ Dat
            (D (subgame (interlaceFun (wrapperU Nmat kq) 1) RC.1 RC.2))) :
    D (wrapperU Nmat kq) = C + kq
      ∧ C + kq ≤ Dfamily (interlaceFun (wrapperU Nmat kq) 1)
          (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (1 - δU) θ)
      ∧ (∀ j : ℕ, j ≤ 2 →
          C + kq ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat kq) 1)
            (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ))
      ∧ (∀ j : ℕ, j ≤ 2 →
          C + kq - 1 - j ≤ Dfamily (interlaceFun (wrapperU Nmat kq) 1)
            (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ))
      ∧ D (wrapperW Nmat kq) = C + kq
      ∧ C + kq ≤ Dfamily (interlaceFun (wrapperW Nmat kq) 1)
          (bracketGE (Fin (2 ^ kq) → Cl) (Fin (2 ^ kq) × Rw) 1 θ (1 - δU))
      ∧ C + kq - 1 ≤ LambdaGE (wrapperW Nmat kq) 1 θ y :=
  firstWrapperOfLowRungs Nmat kq C hC hN hθ0 hθ1 hδ0 hδ1 hy0 hy1 hRw hCl hDenseRung
    hne (fun j hj RC hRC => by
      obtain ⟨Dat, hcall⟩ := hrung j hj RC hRC
      exact lowRungMember_of_certifiedE3 hC (by omega)
        (certifiedE3_at_lowRung G Dat hj hq4 hC hfloor hxT0 hgate hCl hbase hE1 hE2
          hcall))

end Wiring

/-! ## §5  Statement poles

A green build sees neither of the two failure modes these guard against: a
conclusion that holds for a trivial reason, and an index convention that
silently truncates. -/

section Poles

/-- **Statement pole (the rung conclusion has content at every legal `C`).**

`certifiedE3_at_lowRung` delivers `CertifiedE3 (C-1) (k_q - j) val`, and the
worry is that this could be satisfied by the smallest possible readout.  It
cannot: at the frozen `C >= 3` of `09:240` the target `(C-1) + (k_q - j)` is at
least `2`, so `val = 0` -- the complexity of any constant subgame, which the
banked `WrapperLowRungs.wrapperLowRungs_not_automatic` exhibits as an actual
member readout -- is refuted outright.

*Why the trivial witness fails.*  The statement is a refutation, so there is no
witness to find; what it rules out is the readout a degenerate member supplies.
General in `C`, `k_q`, `j`. -/
theorem certifiedE3_at_lowRung_is_not_free {C kq j : ℕ} (hC : 3 ≤ C) :
    ¬ CertifiedE3 (C - 1) (kq - j) 0 := by
  intro hcon
  have h : (C - 1) + (kq - j) ≤ 0 := hcon
  omega

/-- **Statement pole (`09:327`'s width legality cannot be dropped).**

The canonical substitution sets `r' = kappa_j/t_ref = 2^{k_q - j - k_ref}`, and
its conclusion exponent is `log_2(r' t_ref) = (k_q - j - k_ref) + k_ref`.  That
equals the frozen `log_2 kappa_j = k_q - j` **only** when `k_ref + j <= k_q`,
which is exactly what `09:327` supplies ("`q/4 >= t_ref` makes all three values
of `r'` legal").  Outside that range the natural subtraction truncates and the
identity fails, so the hypothesis is load-bearing and not decoration.

*Why the trivial witness fails.*  The existential asks for indices at which the
identity is **false**; a witness satisfying `k_ref + j <= k_q` would make it
true, so the exhibited triple must violate the legality condition -- and it
does. -/
theorem lowRung_needs_the_width_legality :
    ∃ kq kref j : ℕ, ¬ (kref + j ≤ kq) ∧ (kq - j - kref) + kref ≠ kq - j :=
  ⟨0, 1, 0, by omega, by omega⟩

/-- **LANE-GATE 3 non-vacuity for the block-owned half of the bundle, PROVED.**

`certifiedE3_at_lowRung` conjoins five hypotheses that `sec:wrapper-low-rungs`
owns outright -- `09:240`'s `C >= 3`, the `eq:tref-search` floor term
(`06:561--563`), `09:327`'s width legality, `A:112`'s strict positivity, and
`eq:wrapper-low-simple-gate` -- and a green build would not notice if they were
jointly unsatisfiable.  They are not, and every value exhibited is paper-derived:

* `C = 3`, the frozen floor of `09:240`;
* `k_ref = clog_2(t_0(3/5))`, `eq:tref-search`'s own floor term as a closed form
  (`06:563` with `A:104--107`), the same value the banked
  `CertifiedLocalizedExtension.canonicalCall_gates_nonvacuous` takes;
* `k_q = k_ref + 2`, the boundary of `09:327`;
* `x_T` from the banked `WrapperLowRungs.wrapperLowRungGates_legal_instance`,
  which fixes only the single ratio `q x_T` that `eq:wrapper-low-simple-gate`
  constrains and from which no parameter may be read out.

The `x_T` upper bound `A:112` is *derived* from that tier rather than assumed,
which is the same derivation `certifiedE3_at_lowRung` performs.  This exhibits no
restriction datum, no matrix and no reference family, so it is **not** canonical
inhabitation; that obligation stays registered and deferred. -/
theorem lowRung_block_gates_are_satisfiable :
    ∃ (C kq kref : ℕ) (xT : ℝ),
      3 ≤ C ∧ Nat.clog 2 tCert ≤ kref ∧ kref + 2 ≤ kq ∧ 0 < xT
        ∧ ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025 ∧ xT ≤ 1 := by
  have hstep : ∀ r : ℕ, ∀ x : ℝ, 0 < x → ((2 : ℝ) ^ r) * x = 1 / 65536 → x ≤ 1 := by
    intro r x hx hxv
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    nlinarith
  have h4 : 4 ≤ Nat.clog 2 tCert := by
    rw [clog_two_tCert]
    norm_num
  obtain ⟨hgates, hpos, hval⟩ :=
    wrapperLowRungGates_legal_instance (Nat.clog 2 tCert) (Nat.clog 2 tCert + 2) h4
      le_rfl
  exact ⟨3, Nat.clog 2 tCert + 2, Nat.clog 2 tCert, _, le_rfl, le_rfl, le_rfl, hpos,
    hgates.2, hstep _ _ hpos hval⟩

/-- **LANE-GATE 3 non-vacuity for the WHOLE gate set, at ONE width, PROVED.**

`lowRung_block_gates_are_satisfiable` and
`trefSearch_tested_endpoint_is_satisfiable` each cover half of what
`certifiedE3_at_lowRung` assumes, and "each half separately satisfiable" is not
"jointly satisfiable" -- the two halves share `k_ref` and `k_q`.  This closes
that gap: at **one** reference width, every integer, schedule and density gate
of `09:311--327` holds simultaneously.

The width is the paper's own tested endpoint `k_ref = k_ref^* = 100 L_P^2` with
its feasible `j_49` candidate `j = j_ref^* = 4 L_P` (`06:586--590`,
`02:852--858`), which clears `eq:tref-search`'s `clog_2(t_0(3/5))` floor because
`L_P` is taken past the `02:865--868` cutoff; `k_q = k_ref + 2` is `09:327`'s
boundary; and `x_T` is the banked `wrapperLowRungGates_legal_instance` tier at
that `k_q`, from which `A:112`'s upper bound is again derived rather than
assumed.

Still **not** canonical inhabitation: no restriction datum, no matrix, no
reference family, no `theta` and no `eq:certified-base`.  What it rules out is
the failure mode a green build cannot see -- a hypothesis bundle with no legal
model at all. -/
theorem lowRung_full_gate_set_is_satisfiable (Ccert Ltheta : ℕ) :
    ∃ (kref kq j : ℕ) (xT : ℝ),
      Nat.clog 2 tCert ≤ kref ∧ kref + 2 ≤ kq ∧ 4 ≤ kref
        ∧ RawLowProfileBody.J49Feasible kref j
        ∧ 0 < xT ∧ ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025 ∧ xT ≤ 1
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kq : ℝ) + (Ltheta : ℝ) ≤ (2 : ℝ) ^ (kref - 1))
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kref : ℝ) + (Ltheta : ℝ)
            ≤ (2 : ℝ) ^ (j : ℕ)) := by
  have hstep : ∀ r : ℕ, ∀ x : ℝ, 0 < x → ((2 : ℝ) ^ r) * x = 1 / 65536 → x ≤ 1 := by
    intro r x hx hxv
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    nlinarith
  have hclog : 4 ≤ Nat.clog 2 tCert := by
    rw [clog_two_tCert]
    norm_num
  obtain ⟨LP, kref, kq, j, hkref, hj, hkq, hfloor, hcand, -, hE1sched, hE2sched⟩ :=
    trefSearch_tested_endpoint_is_satisfiable Ccert Ltheta
  have h4 : 4 ≤ kref := le_trans hclog hfloor
  have hq4 : kref + 2 ≤ kq := by omega
  obtain ⟨hgates, hpos, hval⟩ := wrapperLowRungGates_legal_instance kref kq h4 hq4
  exact ⟨kref, kq, j, _, hfloor, hq4, h4, hcand, hpos, hgates.2,
    hstep _ _ hpos hval, hE1sched, hE2sched⟩

end Poles

end EthInapproximability.ParameterizedNP.WrapperLowRungAssembly
