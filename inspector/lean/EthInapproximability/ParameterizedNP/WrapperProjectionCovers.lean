import EthInapproximability.ParameterizedNP.WrapperLowRungs

/-!
# Parameterized NP route: the Section-9 projection-covers block

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 335--460** --
  `sec:wrapper-projection-covers`, "Projection covers for the dense rung",
  opening immediately after `sec:wrapper-low-rungs` (whose last line `09:333`
  the predecessor module discharges) and stopping immediately before
  `sec:terminal-two-stream` (`09:461`).  The anchors traced here, in the order
  the frozen block prints them:
  * `09:338--340`: "The dense proof repeatedly needs a small exceptional set of
    outer coordinates outside which specified projections are dense.  The
    following elementary form is convenient";
  * `lem:product-projection-cover` (label `09:343`, statement `09:342--353`):
    "Let `S subseteq Y^q` have density at least `theta`.  Fix an integer
    `k >= 1`, a number `rho in (0,1)`, and let `B` be a positive integer with
    `rho^B < theta`.  Call a `k`-set `J subseteq [q]` poor if the projection of
    `S` to `J` has density below `rho`.  There is a set `E subseteq [q]`, with
    `|E| <= k(B-1)`, that meets every poor `k`-set";
  * its frozen proof (`09:355--362`): "Choose a maximal family of pairwise
    disjoint poor `k`-sets.  If it had `B` members, then `S` would be contained
    in the product of their projection supports, times the unrestricted
    coordinates, and hence would have density below `rho^B < theta`, a
    contradiction.  There are at most `B-1` members.  Their union meets every
    poor `k`-set by maximality and has size at most `k(B-1)`";
  * `09:364--372`: "Let `Y = Cols(N)` be the one-coordinate column alphabet of
    the outer interlace.  Its uniformly duplicated template part is
    `Y_T = bigsqcup_{p in [s]} Y_{T,p}`, `|Y_{T,p}| = m_T`,
    `lambda_T = |Y_T|/|Y|`";
  * `09:373--385`, the four block constants: `tau_0 = 2 s x_T`,
    `rho_sing = (|Y| - m_T + ceil(tau_0 m_T))/|Y|`, `rho_pair = 99/100`,
    `a_min = (rho_pair + lambda_T^2 - 1)/lambda_T^2`;
  * `eq:wrapper-template-gates` (label `09:394`, display `09:387--395`), the six
    atomic clauses `lambda_T >= 99/100`, `eps_2 <= 1/100`, `0 < tau_0`,
    `tau_0 <= 1/100`, `2 ceil(tau_0 m_T) <= m_T`,
    `(a_min - tau_0)/(1+eps_2)^2 >= 49/64`;
  * `09:396--402`: "For reference, the first three numerical bounds imply
    `a_min >= 9701/9801`, `(a_min - tau_0)/(1+eps_2)^2 >= 96029900/99980001 >
    49/64`";
  * `09:404--412`: "For a retained outer column set of density at least
    `theta`, define `rho_* = max{rho_sing, 1 - eta_C}`,
    `B_* = min{B >= 1 : rho_*^B < theta}`,
    `B_pair = min{B >= 1 : rho_pair^B < theta}`";
  * `09:413--417`: "Applying `lem:product-projection-cover` with `k = 1` removes
    at most `B_* - 1` singleton-poor coordinates.  Every remaining coordinate
    has total projection density at least `1 - eta_C`, and every template bin
    retains at least `ceil(tau_0 m_T)` symbols: even concentrating all missing
    symbols in one bin cannot remove more";
  * `09:419--426`: "Applying the lemma with `k = 2` removes at most
    `2(B_pair - 1)` further coordinates so that every remaining pair has
    projection density at least `rho_pair`.  If `P subseteq Y^2` is such a pair
    projection, then `|P cap (Y_T x Y_T)| >= (rho_pair + lambda_T^2 - 1)|Y|^2`";
  * `09:427--432`: "Average over the `s^2` ordered pairs of fixed Stage-3 bins.
    Some ordered pair retains relative density at least `a_min`; its first
    coordinate is then restricted to the first chosen bin and its second
    coordinate to the second.  The Stage-3 route loses less than `tau_0`, and
    balanced transfer loses at most a factor `(1+eps_2)^2`; hence
    `eq:wrapper-template-gates` leaves density at least `49/64`";
  * `09:434--441`: "For the small-capacity calls put `rho = 2y^2 = 18/25`,
    `u_2 = 2`, `u_kappa = kappa/2 + 1` (`4 <= kappa < t_ref`)";
  * `09:442--451`: "For every dyadic `2 <= kappa < t_ref`, take one
    maximal-matching cover of the coordinate sets of size `u_kappa` whose
    projection density is below `rho`.  These are exactly the covers consumed by
    the certified-scale row ladder `lem:certified-row-ladder`: its `l = 1` case
    has `u_2 = 2`, while `l = log_2 kappa >= 2` has `u_kappa = kappa/2 + 1`.
    Let `E_0` be the union of all singleton, pair, and small-copy covers, and put
    `e_0 = |E_0|`";
  * `09:452--453`: "The construction records an explicit deterministic upper
    bound `e_0 <= e_0^max`";
  * `09:458--459`: "The proof below uses the exact finite covers and their exact
    cardinalities; this asymptotic display is only an orientation aid."
* **Cross-anchors in the parameter schedule, opened first-hand for this
  tranche** (`06-parameter-schedule.tex`), because `09:452--453` names
  `e_0^max` without printing it and the schedule is where it is fixed:
  * `eq:cover-bounds` (label `06:653`, display `06:639--654`) --
    `B_ref = min{B >= 1 : (18/25)^B < theta}`,
    `B_sing = min{B >= 1 : (1 - eta_C)^B < theta}`,
    `B_pair = min{B >= 1 : (99/100)^B < theta}`, and
    `e_0^max = (B_ref - 1)(t_ref/2 + log_2 t_ref - 2) + (B_sing - 1)
    + 2(B_pair - 1)`.  The frozen coefficient `t_ref/2 + log_2 t_ref - 2` is
    exactly `sum_{l=1}^{k-1} u_{2^l}` at `t_ref = 2^k`, and that identity is
    **proved** here (`smallCopyWidth_sum`) rather than assumed -- it is the only
    place the `09` small-capacity widths and the `06` cover budget are made to
    agree;
  * `06:697--713` -- "Once the physical Stage-4 matrix is materialised, the
    singleton cover in the proof has contraction factor
    `rho_* = max{rho_sing, 1 - eta_C} = 1 - eta_C`.  Indeed, the finite gates
    `lambda_T >= 99/100`, `2 s x_T <= 1/100`, and `m_T >= 100` imply
    `1 - rho_sing >= (98/100)(lambda_T/s) >= 9702/(10000 s) > 2^{-21}/(2000 s)
    >= eta_C`."  The first inequality of that chain is proved here
    (`one_sub_rhoSing_ge`); the last two compare `eta_C` against
    `eq:eta-choice` and are `06`'s, not this block's.
* **A cross-reference that is deliberately *not* a Lean dependency.**
  `lem:certified-row-ladder` (`A-certified-stopping.tex`, statement
  `A:148--162`, label `A:149`) is what `09:444--447` says consumes these covers.
  It has **no** Lean declaration in this repository, and none is created here.
  What is checked is only the arithmetic identification the frozen sentence
  makes: the ladder's copy count is `2^{l-1} + 1` (`A:158`), and
  `smallCopyWidth_dyadic` proves `u_{2^l} = 2^{l-1} + 1` for every `l >= 1` --
  so the frozen split into "`u_2 = 2`" and "`u_kappa = kappa/2 + 1`" is one
  uniform formula, `u_kappa = kappa/2 + 1`, and the `l = 1` case is not a special
  case at all.  Nothing about the ladder's *conclusion* is assumed or asserted.
* **The dense machinery is not consumed here.**  The frozen block `09:335--460`
  points at `lem:product-projection-cover`, `eq:wrapper-template-gates`,
  `lem:certified-row-ladder`, and `eq:cover-bounds`.  It points at **none** of
  the dense Stage-4 frontier apparatus, so **no** declaration below mentions
  `DenseAliceClosure` or `DenseWeightedCount`.  They are in the transitive import
  closure only because the sequential predecessor `WrapperLowRungs` imports
  `DenseAliceClosure` for its own frozen reason (`extensionSelectedBlocks`); that
  is a pin held by that module, not a consumption by this one.  The standing
  consumption bars therefore apply vacuously here.
* **Predecessor anchors (consumed by pin, never restated):**
  * `EthInapproximability.ParameterizedNP.ScaleAlignOpening.lambdaTemplate` --
    the banked `lambda_T = |Y_T|/|Cols(G)|` of `09:130`, which is the same
    `lambda_T` `09:371` names; `pair_template_intersection` is stated at that
    banked definition and does not re-define the template density;
  * `EthInapproximability.ParameterizedNP.DenseStageFourOpening.xTdepth` -- the
    banked `x_T = 2^{-b_T}` (`06:238--242`), used only inside the tier-2
    non-vacuity witness so that `tau_0 = 2 s x_T` is evaluated at a banked
    parameter pair and not at an invented one.
* **New work.**  `lem:product-projection-cover` transcribed letter-exact and
  **proved** by the frozen argument, including the product-support counting step
  (`card_le_prod_projSet_mul`), which is proved for an *arbitrary* family and
  needs disjointness only in the cardinality bookkeeping; the four block
  constants; `eq:wrapper-template-gates` as a checked transcription with the
  `09:396--402` reference numerics proved at the exact frozen rationals; the
  cover numbers as `Nat.sInf` least searches with their existence, minimality
  and a strictness readout; the `06:702--710` singleton contraction bound; the
  `09:413--417` bin-retention step; the `09:419--426` intersection bound; the
  `09:427--429` averaging over the `s^2` ordered bin pairs proved from a genuine
  disjoint decomposition; the `09:430--432` loss arithmetic with the two losses
  as named binders; the small-capacity widths with the row-ladder identification
  and the `eq:cover-bounds` coefficient identity; and the assembled
  `E_0` / `e_0 <= e_0^max` deliverable.
* Proof status: **new** for everything named above.  **Conditional** (with named,
  documented binders) only where the frozen text itself supplies the datum from
  another block -- the Stage-3 route loss and the balanced-transfer factor of
  `09:430--431`, and the bin decomposition of `09:367`.
* Axiom surface (`#print axioms`, run on every named result of this module):
  `propext`, `Classical.choice`, `Quot.sound` only.  No project axiom, no
  unproved placeholder, no new opaque certificate.  `LegacyNPCC.Stage12` -- whose
  closure reaches the cited AGHP balanced-family axiom -- is **not** imported,
  and no declaration here is in its dependency graph.  `EXPANDER-001`, the cited
  `(q_2,t_2,eps_2)`-balanced family, has no Lean declaration by design and
  appears in no hypothesis below: `eps_2` enters this block only as a *bare real
  parameter* of `eq:wrapper-template-gates`, never as a claim about an expander.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, opened first-hand
for this tranche.  **No reader item is claimed by any declaration in this
module**, and that is a finding about the reader artifact rather than an
omission here.  The reader mentions this block's content in exactly two places,
both **prose inside the proof** of `thm:paper-adapted-stage4-interface` and
neither a statement:

* line 374, "The fixed masses and the certified cover bounds ensure that either
  an early protected reservoir already gives a hard restriction or one terminal
  owner receives enough protected mass from a donor";
* lines 396--399, "The complete owner--donor count is finite: it uses only the
  fixed reservoir masses above, the two source deletion tolerances, and the exact
  cover and ceiling inequalities certified by the parameter compiler.  It is
  expanded line by line in the ultra-explicit companion."

The reader states no product-projection cover lemma, no template gate display, no
`rho_sing` / `rho_pair` / `a_min`, no `B_*` / `B_pair` / `B_ref`, and no `e_0`.
Its own sentence at 398--399 says the expansion lives in the ultra-explicit
companion, which is the frozen `09:335--460` this module traces.  Citing either
line as a counterpart would be citing prose as a statement, which the
`READER-COUNTERPART` discipline bars; every declaration below therefore carries
its autoformalization (and, where named, parameter-schedule) anchor alone.  The
neighbouring reader rung display at lines 361--368 is **already assigned** to
`WrapperLowRungs.wrapperLowRungs` and is not reclaimed here; reader lines 370
onward remain the dense rung's content and stay untouched.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the projection encoding, general (6): `mem_projSet`, `projSet_card_le`,
  `projSet_mono`, `projSet_card_le_card`, `projSet_nonempty`, `projSet_univ`.
* `A2` the poorness predicate, general (2): `not_poorProjection_univ`,
  `poorProjection_mono_rho`.
* `A3` the counting core and the headline (3): `card_le_prod_projSet_mul`,
  `density_le_pow_of_disjoint_poor`, `productProjectionCover`.
* `A4` the block constants, general (6): `tauZero_pos`, `aMin_apply`,
  `aMin_eq_one_sub`, `aMin_mono_lambda`, `aMin_frozen_value`, `aMin_ge_frozen`.
* `A5` the template gates (2): `templateGates_reference_margins`,
  `wrapperTemplateGates_of_numerics`.
* `A6` the cover numbers, general (5): `coverExponent_setNonempty`,
  `coverExponent_spec`, `coverExponent_le`, `two_le_coverExponent`,
  `rhoStar_eq_one_sub_etaC`.
* `A7` the singleton step (4): `one_sub_rhoSing_ge`, `rhoSing_lt_one`,
  `singleton_bin_retention`, `rhoSing_density_to_card`.
* `A8` the pair step (3): `pair_template_intersection`, `exists_bin_pair_dense`,
  `pair_density_after_losses`.
* `A9` the small-capacity calls and `e_0` (7): `rhoSmall_eq_two_y_sq`,
  `smallCopyWidth_two`, `one_le_smallCopyWidth`, `smallCopyWidth_dyadic`,
  `smallCopyWidth_sum`, `e0_le_e0Max`, `exists_initial_exceptional_set`.

That is **38 battery entries proved**, with `0` unproved, alongside **two
statement poles** (`templateGates_last_clause_needs_lambda`,
`productProjectionCover_witness_is_nonempty`) and **four non-vacuity /
consistency readouts** (`wrapperTemplateGates_legal_instance`,
`productProjectionCover_probe_is_legal`,
`exists_initial_exceptional_set_fires_at_probe`, and `two_le_coverExponent`, the
last already counted in `A6`).

The module has **55** source declarations in all: 12 definitions (`projSet`,
`PoorProjection`, `tauZero`, `rhoSing`, `rhoPair`, `aMin`, `rhoStar`,
`wrapperTemplateGates`, `coverExponent`, `rhoSmall`, `smallCopyWidth`, `e0Max`)
and 43 proved results.  All 55 are registered in `tools/AxiomAudit.lean`.

**Hypothesis consistency (checked, no `False`).**  The full binder bundle of
`exists_initial_exceptional_set` was tested by *applying* the theorem at
`Y = Bool`, `q = 1`, `k = 1`, `S = {const true}`, `theta = 1/2`, `rho_* = 3/4`:
`exists_initial_exceptional_set_fires_at_probe` is that application, so all six
hypotheses hold simultaneously in the kernel and no clause of the bundle
contradicts another.  `productProjectionCover`'s bundle is the same six minus
`hk`-at-`1` and is certified by `productProjectionCover_probe_is_legal`.  The
frozen side conditions were **not** conjoined across cases: `09:413`, `09:419`
and `09:442` are three separate applications of one lemma at three different
`(k, rho)` pairs, and they are formalized as three separate applications, never
as one bundle demanding all three densities of the same coordinate set.

## Why the deliverables are not satisfied by a trivial witness

Both headlines are existential, so each gets an explicit refutation of the
trivial witness.

* `productProjectionCover` delivers `E` with `|E| <= k(B-1)`.  The trivial
  witness is `E = empty`, which is the *smallest* admissible cardinality and
  would satisfy the bound outright.  `productProjectionCover_witness_is_nonempty`
  refutes it at a legal instance: over `Y = Bool`, `q = 1`,
  `S = {const true}`, the singleton `J = {0}` has projection density
  `1/2 < 3/4`, so it is poor, so **every** admissible `E` must contain `0`.
  `productProjectionCover_probe_is_legal` certifies that this probe really does
  satisfy the theorem's hypotheses -- `theta |Y|^q = 1 <= |S|` at `theta = 1/2`,
  `(3/4)^3 = 27/64 < 1/2` at `B = 3`, `0 < 3/4 < 1`, `0 < |Bool|` -- so the
  refutation is of the theorem's own existential and not of a strengthened one.
  It is a **tier-3 separating probe at a deliberately minimal carrier**, cited
  only for what it separates; no parameter of the route may be read out of it.
* `exists_initial_exceptional_set` delivers `E_0` with
  `e_0 <= e_0^max`.  The same refutation applies verbatim through its first
  clause (the `k = 1` singleton clause is literally the conclusion of
  `productProjectionCover` at `rho = rho_*`), so `E_0 = empty` is refuted at the
  same probe.  In the other direction the cardinality clause is not free either:
  it is `e0Max` of `eq:cover-bounds`, which grows only with the three least
  searches and the width exponent, so `E_0 = univ` is inadmissible as soon as
  `q` exceeds that budget.
* `eq:wrapper-template-gates` is not automatic and its fifth clause is a genuine
  constraint on `lambda_T`, not a formality:
  `templateGates_last_clause_needs_lambda` computes
  `a_min(rho_pair, 1/10) = 0`, so the frozen quotient is **negative** there and
  the `49/64` comparison fails.  The gate is therefore doing work, and
  `wrapperTemplateGates_legal_instance` shows the work is satisfiable at the
  banked tier.

## Three-tier witness legality

* **Tier 1 -- symbolic in the frozen parameters.**  Every result about
  `projSet`, `PoorProjection`, `card_le_prod_projSet_mul`,
  `density_le_pow_of_disjoint_poor`, `productProjectionCover`, `aMin`,
  `coverExponent`, `rhoSing`, `pair_template_intersection`,
  `exists_bin_pair_dense`, `smallCopyWidth`, `e0Max` and
  `exists_initial_exceptional_set` is general in the alphabet `Y`, in the width
  `q`, in `k`, `B`, `s`, `m_T`, and in the real parameters
  `theta, rho, tau_0, lambda_T, eps_2, eta_C`.  Nothing is evaluated.
* **Tier 2 -- the block-owned gates instantiated in the legal range.**
  `wrapperTemplateGates_legal_instance` fires
  `eq:wrapper-template-gates` at `m_T = 100` (the frozen floor of `06:703`),
  `lambda_T = 99/100` (the frozen floor of `09:389`), `eps_2 = 1/100` (the frozen
  ceiling of `09:389`), and `tau_0 = 2 s x_T` evaluated at the **banked** tier
  `s = 2^340`, `b_T = 512` -- the same pair `ScaleAlignOpening`'s
  `referenceProfileGates_legal_instance` and `WrapperLowRungs`'
  `strict_xT_membership_at_banked_tier` already use, so no numeral is invented.
  There `tau_0 = 2^{-171}`, strictly positive and far inside `1/100`, and
  `ceil(tau_0 m_T) = 1`, so `2 ceil(tau_0 m_T) = 2 <= 100 = m_T` holds with the
  ceiling at its smallest **nonzero** value: the instance is not degenerate in
  the direction that would matter (a `tau_0 = 0` reading would make
  `ceil(tau_0 m_T) = 0` and the bin-retention conclusion of `09:416` empty).
  No parameter may be read out of the instance: `eq:tref-search` still forces
  `k_ref >= 2^19`, and `s`, `b_T`, `m_T` are fixed by the schedule and not by
  this choice.
* **Tier 3 -- separating probes at deliberately small carriers.**
  `productProjectionCover_witness_is_nonempty`,
  `productProjectionCover_probe_is_legal` and
  `templateGates_last_clause_needs_lambda` are probes of one named clause at a
  minimal carrier or at one illegal parameter value, cited only for what they
  separate.  The last is deliberately **outside** the frozen regime
  `lambda_T >= 99/100` and must never be read as an instance of it -- its whole
  content is that the frozen regime excludes the point at which it holds.

## Honest scope, GAP-EXPOSED, and recorded coverage limits

1. **The asymptotic display `09:453--457` is GAP-EXPOSED, by the paper's own
   instruction.**  "Since `1 - rho_sing` and `eta_C` are both of order `1/s`,
   `e_0 = O((s + t_ref) log(1/theta))`" is not transcribed and not proved:
   `09:458--459` says in terms that "the proof below uses the exact finite covers
   and their exact cardinalities; this asymptotic display is only an orientation
   aid."  What is landed instead is the exact bound the proof actually uses,
   `e_0 <= e_0^max` at the `eq:cover-bounds` value.  This is the one named
   GAP-EXPOSED range of the block: **`09:453--457`**.
2. **`lem:certified-row-ladder` is not formalized and not assumed.**  `A:148--162`
   has no Lean declaration anywhere in this repository.  `09:444--447` is honoured
   only as the copy-count identification `u_{2^l} = 2^{l-1} + 1`
   (`smallCopyWidth_dyadic`); the ladder's `Lambda_3` conclusion `eq:certified-
   row-ladder` is neither stated nor used, and no consumer may read this module
   as having supplied it.
3. **The Stage-3 route loss and the balanced-transfer factor stay binders.**
   `09:430--431` says "The Stage-3 route loses less than `tau_0`, and balanced
   transfer loses at most a factor `(1+eps_2)^2`".  Those are facts of the
   Stage-3 block and of the balanced-transfer contract, not of this block;
   `pair_density_after_losses` carries them as the explicit hypotheses `hroute`
   and `htransfer` and proves exactly the arithmetic `09:432` claims -- that
   `eq:wrapper-template-gates` then leaves density at least `49/64`.  Nothing
   here derives either loss.
4. **The Stage-3 bin decomposition is given data, not constructed.**  `09:367`
   fixes `Y_T = bigsqcup_{p in [s]} Y_{T,p}` with `|Y_{T,p}| = m_T`; the bins are
   an input of `exists_bin_pair_dense` (`bins`, `hdisj`), and `Y_T` is their
   union.  This block does not build the duplication schedule that produces them.
5. **`eta_C` is never evaluated and `rho_* = 1 - eta_C` is not asserted.**
   `09:407` defines `rho_* = max{rho_sing, 1 - eta_C}`; `06:700` *evaluates* that
   maximum, and the evaluation depends on `eq:eta-choice`, which is `06`'s.
   `rhoStar_eq_one_sub_etaC` is therefore an implication from the comparison, and
   `one_sub_rhoSing_ge` proves only the first inequality of the `06:704--709`
   chain.  The two remaining links, `9702/(10000 s) > 2^{-21}/(2000 s)` and
   `2^{-21}/(2000 s) >= eta_C`, are not claimed here.
6. **`theta` stays a binder and is never a numeral**, outside the tier-3 probe.
   Every cover number is `Nat.sInf` of the frozen least search, with existence
   supplied by `0 < theta` and `rho < 1` and *nothing else*; no value of any
   `B_*`, `B_pair`, `B_ref` is computed, and `eq:cover-tested-endpoint`
   (`06:666--693`), which is how the compiler certifies these searches without
   evaluating them, is `06`'s territory and is not transcribed here.
7. **`e_0^max` is `eq:cover-bounds`', not this block's invention.**  `09:452--453`
   says only that "the construction records an explicit deterministic upper
   bound"; the value is `06:647--651`, and `e0Max` is that value verbatim.  The
   agreement of its first coefficient with the `09:434--447` small-capacity
   widths is **proved** (`smallCopyWidth_sum`) and is the load-bearing check of
   this section: had the frozen `t_ref/2 + log_2 t_ref - 2` disagreed with
   `sum_l u_{2^l}`, the two sections would be inconsistent.
8. **No route completion is claimed**, and `hDenseRung` is neither discharged nor
   narrowed.  This module *feeds* the dense rung: it is the first of the blocks
   `09:335--1781` that jointly prove `eq:wrapper-u-dense`, and it lands the covers
   the later blocks consume.  The remaining blocks `09:461--1781` stay
   GAP-EXPOSED exactly as `ScaleAlignOpening` and `WrapperLowRungs` record them.
   The construction and machine layers of the route remain unlanded.
-/

namespace EthInapproximability.ParameterizedNP.WrapperProjectionCovers

open Finset

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {q : ℕ}

/-- **`09:346--347`.**  "the projection of `S` to `J`".  The projection of a set of
outer column tuples `S subseteq Y^q` to the coordinate set `J`, as a finite set
of functions `J -> Y`; its ambient type has exactly `|Y|^{|J|}` elements, which
is the denominator the frozen density uses.  General in the alphabet and in `q`. -/
def projSet (J : Finset (Fin q)) (S : Finset (Fin q → Y)) : Finset (↥J → Y) :=
  S.image (fun f i => f i.1)

omit [Fintype Y] in
/-- **Aux A1a.**  Every member of `S` projects into `projSet J S`.  General. -/
theorem mem_projSet {J : Finset (Fin q)} {S : Finset (Fin q → Y)} {f : Fin q → Y}
    (hf : f ∈ S) : (fun i : ↥J => f i.1) ∈ projSet J S :=
  Finset.mem_image_of_mem _ hf

/-- **`09:346--347`.**  "Call a `k`-set `J subseteq [q]` poor if the projection of
`S` to `J` has density below `rho`."  Written multiplicatively against
`|Y|^{|J|}` so that no division is taken and the empty-alphabet case is not
silently excluded.  General in `rho`, `J` and `S`. -/
def PoorProjection (ρ : ℝ) (J : Finset (Fin q)) (S : Finset (Fin q → Y)) : Prop :=
  ((projSet J S).card : ℝ) < ρ * (Fintype.card Y : ℝ) ^ J.card

/-- **Aux A3a (the counting core of the frozen proof, `09:356--359`).**

"`S` would be contained in the product of their projection supports, times the
unrestricted coordinates."  Formally: for **any** family `F` of coordinate sets,
the map sending `f` to its tuple of `F`-projections together with its restriction
to the complement of `bigcup F` is injective, so
`|S| <= (prod_{J in F} |proj_J S|) . |Y|^{|(bigcup F)^c|}`.

Disjointness of `F` is **not** needed for this inequality -- it is needed only to
evaluate `|bigcup F|` as `k|F|` -- so it is deliberately not a hypothesis here.
General in the alphabet, in `q`, and in the family. -/
theorem card_le_prod_projSet_mul (S : Finset (Fin q → Y))
    (F : Finset (Finset (Fin q))) :
    S.card ≤ (∏ J ∈ F, (projSet J S).card)
      * Fintype.card Y ^ ((F.biUnion id)ᶜ).card := by
  classical
  set A : Finset (Fin q) := F.biUnion id with hA
  set T : Finset (((J : {x // x ∈ F}) → (↥(J.1) → Y)) × (↥(Aᶜ) → Y)) :=
    (Fintype.piFinset (fun J : {x // x ∈ F} => projSet J.1 S)) ×ˢ Finset.univ with hT
  have hmap : ∀ f ∈ S,
      ((fun (J : {x // x ∈ F}) (i : ↥(J.1)) => f i.1),
        (fun i : ↥(Aᶜ) => f i.1)) ∈ T := by
    intro f hf
    rw [hT, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Fintype.mem_piFinset]
    intro J
    exact mem_projSet hf
  have hinj : Set.InjOn
      (fun f : Fin q → Y =>
        ((fun (J : {x // x ∈ F}) (i : ↥(J.1)) => f i.1),
          (fun i : ↥(Aᶜ) => f i.1))) (S : Set (Fin q → Y)) := by
    intro f _ g _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    funext i
    by_cases hi : i ∈ A
    · rw [hA, Finset.mem_biUnion] at hi
      obtain ⟨J, hJF, hiJ⟩ := hi
      have := congrFun h1 ⟨J, hJF⟩
      have := congrFun this ⟨i, hiJ⟩
      exact this
    · have hic : i ∈ Aᶜ := Finset.mem_compl.mpr hi
      have := congrFun h2 ⟨i, hic⟩
      exact this
  have hcard := Finset.card_le_card_of_injOn _ hmap hinj
  refine le_trans hcard (le_of_eq ?_)
  rw [hT, Finset.card_product, Fintype.card_piFinset]
  congr 1
  · exact Finset.prod_coe_sort F (fun J => (projSet J S).card)
  · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe]

/-- **Aux A3b (`09:356--359`, the density reading).**

"...and hence would have density below `rho^B`."  A pairwise disjoint family of
`|F|` poor `k`-sets forces `theta <= rho^{|F|}` on any `S` of density at least
`theta`.  The frozen sentence says *below*; the non-strict form proved here is
all the contradiction needs (`theta <= rho^n <= rho^B < theta`) and avoids a
spurious positivity hypothesis on the projection cardinalities.  General. -/
theorem density_le_pow_of_disjoint_poor (S : Finset (Fin q → Y))
    (F : Finset (Finset (Fin q))) {k : ℕ} {ρ θ : ℝ}
    (hY : 0 < Fintype.card Y)
    (hdisj : ∀ J ∈ F, ∀ J' ∈ F, J ≠ J' → Disjoint J J')
    (hk : ∀ J ∈ F, J.card = k)
    (hpoor : ∀ J ∈ F, PoorProjection ρ J S)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ)) :
    θ ≤ ρ ^ F.card := by
  classical
  set A : Finset (Fin q) := F.biUnion id with hA
  have hYR : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hAcard : A.card = k * F.card := by
    rw [hA, Finset.card_biUnion (by intro x hx y hy hxy; exact hdisj x hx y hy hxy)]
    simp only [id_eq]
    rw [Finset.sum_congr rfl (fun J hJ => hk J hJ)]
    simp [Finset.sum_const, mul_comm]
  have hAle : A.card ≤ q := by
    have := Finset.card_le_univ A
    simpa using this
  have hcompl : (Aᶜ).card = q - k * F.card := by
    rw [Finset.card_compl, hAcard]
    simp
  -- the counting bound, cast to the reals
  have hcount : (S.card : ℝ)
      ≤ (∏ J ∈ F, ((projSet J S).card : ℝ))
        * (Fintype.card Y : ℝ) ^ (q - k * F.card) := by
    have := card_le_prod_projSet_mul S F
    rw [hcompl] at this
    calc (S.card : ℝ)
        ≤ (((∏ J ∈ F, (projSet J S).card)
              * Fintype.card Y ^ (q - k * F.card) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (∏ J ∈ F, ((projSet J S).card : ℝ))
              * (Fintype.card Y : ℝ) ^ (q - k * F.card) := by push_cast; ring
  -- each factor is below `ρ |Y|^k`
  have hfac : ∏ J ∈ F, ((projSet J S).card : ℝ)
      ≤ ∏ _J ∈ F, (ρ * (Fintype.card Y : ℝ) ^ k) := by
    refine Finset.prod_le_prod (fun J _ => by positivity) ?_
    intro J hJ
    have hp := hpoor J hJ
    rw [PoorProjection, hk J hJ] at hp
    exact le_of_lt hp
  have hprod : ∏ _J ∈ F, (ρ * (Fintype.card Y : ℝ) ^ k)
      = ρ ^ F.card * (Fintype.card Y : ℝ) ^ (k * F.card) := by
    rw [Finset.prod_const, mul_pow, ← pow_mul, mul_comm k F.card]
  have hsplit : (Fintype.card Y : ℝ) ^ (k * F.card)
      * (Fintype.card Y : ℝ) ^ (q - k * F.card) = (Fintype.card Y : ℝ) ^ q := by
    rw [← pow_add]
    congr 1
    omega
  have hchain : θ * (Fintype.card Y : ℝ) ^ q
      ≤ ρ ^ F.card * (Fintype.card Y : ℝ) ^ q := by
    refine le_trans hS (le_trans hcount ?_)
    have hpos : (0 : ℝ) ≤ (Fintype.card Y : ℝ) ^ (q - k * F.card) := by positivity
    calc (∏ J ∈ F, ((projSet J S).card : ℝ)) * (Fintype.card Y : ℝ) ^ (q - k * F.card)
        ≤ (∏ _J ∈ F, (ρ * (Fintype.card Y : ℝ) ^ k))
            * (Fintype.card Y : ℝ) ^ (q - k * F.card) :=
          mul_le_mul_of_nonneg_right hfac hpos
      _ = ρ ^ F.card * ((Fintype.card Y : ℝ) ^ (k * F.card)
            * (Fintype.card Y : ℝ) ^ (q - k * F.card)) := by rw [hprod]; ring
      _ = ρ ^ F.card * (Fintype.card Y : ℝ) ^ q := by rw [hsplit]
  have hqpos : (0 : ℝ) < (Fintype.card Y : ℝ) ^ q := by positivity
  exact le_of_mul_le_mul_right (by linarith [hchain]) hqpos

/-- **`lem:product-projection-cover` (`09:342--353`), proved by the frozen argument
(`09:355--362`).**

"Let `S subseteq Y^q` have density at least `theta`.  Fix an integer `k >= 1`, a
number `rho in (0,1)`, and let `B` be a positive integer with `rho^B < theta`.
Call a `k`-set `J subseteq [q]` poor if the projection of `S` to `J` has density
below `rho`.  There is a set `E subseteq [q]`, with `|E| <= k(B-1)`, that meets
every poor `k`-set."

The proof is the frozen one and nothing else: a family of pairwise disjoint poor
`k`-sets of **maximum cardinality** exists because the ambient type of families
is finite; `density_le_pow_of_disjoint_poor` bounds its size by `B-1`; its union
has size `k|F| <= k(B-1)`; and maximality forces every poor `k`-set to meet that
union, since otherwise the family could be extended.  The carrier nonemptiness
`0 < |Y|` is carried explicitly (`hY`) rather than assumed away.

The deliverable is existential; `productProjectionCover_witness_is_nonempty`
refutes the trivial witness `E = empty` at a legal instance. -/
theorem productProjectionCover (S : Finset (Fin q → Y)) {k B : ℕ} {ρ θ : ℝ}
    (hY : 0 < Fintype.card Y)
    (hk : 1 ≤ k) (hB : 1 ≤ B)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hBρ : ρ ^ B < θ)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ)) :
    ∃ E : Finset (Fin q), E.card ≤ k * (B - 1) ∧
      ∀ J : Finset (Fin q), J.card = k → PoorProjection ρ J S → (E ∩ J).Nonempty := by
  classical
  set Valid : Finset (Finset (Fin q)) → Prop := fun F =>
    (∀ J ∈ F, J.card = k) ∧ (∀ J ∈ F, PoorProjection ρ J S) ∧
      (∀ J ∈ F, ∀ J' ∈ F, J ≠ J' → Disjoint J J') with hValidDef
  set 𝒢 : Finset (Finset (Finset (Fin q))) := Finset.univ.filter Valid with hGdef
  have hne : 𝒢.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hGdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp [hValidDef]⟩
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_max_image 𝒢 Finset.card hne
  have hFvalid : Valid F := (Finset.mem_filter.mp (by rw [← hGdef]; exact hFmem)).2
  obtain ⟨hFk, hFpoor, hFdisj⟩ := hFvalid
  have hFcard : F.card ≤ B - 1 := by
    by_contra hcon
    push Not at hcon
    have hBle : B ≤ F.card := by omega
    have hθ := density_le_pow_of_disjoint_poor S F hY hFdisj hFk hFpoor hS
    have hmono : ρ ^ F.card ≤ ρ ^ B :=
      pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1) hBle
    linarith
  refine ⟨F.biUnion id, ?_, ?_⟩
  · have hAcard : (F.biUnion id).card = k * F.card := by
      rw [Finset.card_biUnion (by intro x hx y hy hxy; exact hFdisj x hx y hy hxy)]
      simp only [id_eq]
      rw [Finset.sum_congr rfl (fun J hJ => hFk J hJ)]
      simp [Finset.sum_const, mul_comm]
    rw [hAcard]
    exact Nat.mul_le_mul_left k hFcard
  · intro J hJcard hJpoor
    by_contra hcon
    have hempty : (F.biUnion id) ∩ J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcon
    have hsub : ∀ J' ∈ F, ∀ a ∈ J', a ∉ J := by
      intro J' hJ' a haJ' haJ
      have : a ∈ (F.biUnion id) ∩ J :=
        Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨J', hJ', haJ'⟩, haJ⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty a)
    have hJnotF : J ∉ F := by
      intro hJF
      have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hJne
      exact hsub J hJF a ha ha
    have hins : insert J F ∈ 𝒢 := by
      rw [hGdef, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · intro J' hJ'
        rcases Finset.mem_insert.mp hJ' with h | h
        · exact h ▸ hJcard
        · exact hFk J' h
      · intro J' hJ'
        rcases Finset.mem_insert.mp hJ' with h | h
        · exact h ▸ hJpoor
        · exact hFpoor J' h
      · intro J₁ h₁ J₂ h₂ hne12
        rcases Finset.mem_insert.mp h₁ with e₁ | e₁ <;>
          rcases Finset.mem_insert.mp h₂ with e₂ | e₂
        · exact absurd (e₁.trans e₂.symm) hne12
        · subst e₁
          exact Finset.disjoint_right.mpr (fun a ha => hsub J₂ e₂ a ha)
        · subst e₂
          exact Finset.disjoint_left.mpr (fun a ha => hsub J₁ e₁ a ha)
        · exact hFdisj J₁ e₁ J₂ e₂ hne12
    have := hFmax _ hins
    rw [Finset.card_insert_of_notMem hJnotF] at this
    omega


/-! ## Section 2  The template alphabet and the block constants -/

/-- **`09:376`.**  `tau_0 = 2 s x_T`, the Stage-3 route loss allowance.  General in
the bin count `s` and in `x_T`; the banked `DenseStageFourOpening.xTdepth` is
substituted only inside the tier-2 witness. -/
noncomputable def tauZero (s : ℕ) (xT : ℝ) : ℝ := 2 * s * xT

/-- **`09:378--379`.**  `rho_sing = (|Y| - m_T + ceil(tau_0 m_T))/|Y|`, the
singleton contraction factor.  `n` is `|Y|`.  The ceiling is `Nat.ceil`, matching
the banked convention of `rawLowGates`. -/
noncomputable def rhoSing (n mT : ℕ) (tau0 : ℝ) : ℝ :=
  ((n : ℝ) - mT + (⌈tau0 * (mT : ℝ)⌉₊ : ℝ)) / (n : ℝ)

/-- **`09:380`.**  `rho_pair = 99/100`, the pair contraction factor. -/
noncomputable def rhoPair : ℝ := 99 / 100

/-- **`09:382--383`.**  `a_min = (rho_pair + lambda_T^2 - 1)/lambda_T^2`, the
relative density the averaging step retains on some ordered bin pair.  General in
both arguments. -/
noncomputable def aMin (rp lamT : ℝ) : ℝ := (rp + lamT ^ 2 - 1) / lamT ^ 2

/-- **`09:407`.**  `rho_* = max{rho_sing, 1 - eta_C}`.  The evaluation `= 1 - eta_C`
is `06:700`'s and is available here only as the implication
`rhoStar_eq_one_sub_etaC`. -/
noncomputable def rhoStar (n mT : ℕ) (tau0 etaC : ℝ) : ℝ :=
  max (rhoSing n mT tau0) (1 - etaC)

/-- **Aux A4a (`09:390`, the `0 < tau_0` clause as a readout).**  `tau_0 = 2 s x_T`
is positive as soon as the bin count and `x_T` are.  General. -/
theorem tauZero_pos {s : ℕ} {xT : ℝ} (hs : 0 < s) (hx : 0 < xT) :
    0 < tauZero s xT := by
  have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  unfold tauZero
  positivity

/-- **Aux A4b.**  The defining equation of `a_min`, exposed so that consumers need
not unfold.  General. -/
theorem aMin_apply (rp lamT : ℝ) : aMin rp lamT = (rp + lamT ^ 2 - 1) / lamT ^ 2 := rfl

/-- **Aux A4c.**  `a_min = 1 - (1 - rho_pair)/lambda_T^2`, the form that makes the
monotonicity in `lambda_T` visible.  General. -/
theorem aMin_eq_one_sub {rp lamT : ℝ} (h : lamT ≠ 0) :
    aMin rp lamT = 1 - (1 - rp) / lamT ^ 2 := by
  unfold aMin
  field_simp
  ring

/-- **Aux A4d.**  `a_min` is monotone in the template density whenever
`rho_pair <= 1`.  This is the direction the frozen bound needs: `09:389` gives
only `lambda_T >= 99/100`, and `09:398` reads the value off **at** `99/100`.
General. -/
theorem aMin_mono_lambda {rp lamT lamT' : ℝ} (hrp : rp ≤ 1)
    (h0 : 0 < lamT) (h : lamT ≤ lamT') :
    aMin rp lamT ≤ aMin rp lamT' := by
  have h0' : 0 < lamT' := lt_of_lt_of_le h0 h
  rw [aMin_eq_one_sub (ne_of_gt h0), aMin_eq_one_sub (ne_of_gt h0')]
  have hsq : lamT ^ 2 ≤ lamT' ^ 2 := by nlinarith
  have hkey : (1 - rp) / lamT' ^ 2 ≤ (1 - rp) / lamT ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 1 - rp)]
  linarith

/-- **Aux A4e (`09:398` at the schedule floor, exactly).**  At `lambda_T = 99/100`
the value is exactly `9701/9801` -- an equality, not an estimate. -/
theorem aMin_frozen_value : aMin rhoPair (99 / 100) = 9701 / 9801 := by
  unfold aMin rhoPair
  norm_num

/-- **`09:396--398`, the first frozen readout.**  "the first three numerical bounds
imply `a_min >= 9701/9801`."  Proved from `lambda_T >= 99/100` alone, by
`aMin_mono_lambda` plus the exact value. -/
theorem aMin_ge_frozen {lamT : ℝ} (hlam : 99 / 100 ≤ lamT) :
    9701 / 9801 ≤ aMin rhoPair lamT := by
  rw [← aMin_frozen_value]
  exact aMin_mono_lambda (by unfold rhoPair; norm_num) (by norm_num) hlam

/-! ## Section 3  The scale-alignment template gates -/

/-- **`eq:wrapper-template-gates` (`09:387--395`), transcribed and never asserted.**

"The scale-alignment schedule imposes `lambda_T >= 99/100`, `eps_2 <= 1/100`,
`0 < tau_0 <= 1/100`, `2 ceil(tau_0 m_T) <= m_T`,
`(a_min - tau_0)/(1+eps_2)^2 >= 49/64`."

All six atomic clauses, in the frozen order, at the frozen constants.  `eps_2`
enters as a bare real parameter: no expander claim is made or needed, because the
frozen display constrains only its size. -/
def wrapperTemplateGates (mT : ℕ) (lamT eps2 tau0 : ℝ) : Prop :=
  99 / 100 ≤ lamT ∧ eps2 ≤ 1 / 100 ∧ 0 < tau0 ∧ tau0 ≤ 1 / 100
    ∧ 2 * ⌈tau0 * (mT : ℝ)⌉₊ ≤ mT
    ∧ 49 / 64 ≤ (aMin rhoPair lamT - tau0) / (1 + eps2) ^ 2

/-- **`09:396--402`, the reference numerics, proved at the exact frozen rationals.**

"For reference, the first three numerical bounds imply `a_min >= 9701/9801`,
`(a_min - tau_0)/(1+eps_2)^2 >= 96029900/99980001 > 49/64`."

The middle constant is exactly `(9701/9801 - 1/100)/(101/100)^2`, and the strict
comparison with `49/64` is checked outright.  `0 <= eps_2` is carried as an
explicit hypothesis and is **not** added to `wrapperTemplateGates`: the frozen
display does not print it, and the balancedness error's nonnegativity is
`03`/`06` data (`StageTwoRelaxed.epsTwo` is a positive quotient by
construction).  General in all three parameters. -/
theorem templateGates_reference_margins {lamT eps2 tau0 : ℝ}
    (hlam : 99 / 100 ≤ lamT) (he0 : 0 ≤ eps2) (he1 : eps2 ≤ 1 / 100)
    (ht0 : 0 < tau0) (ht1 : tau0 ≤ 1 / 100) :
    9701 / 9801 ≤ aMin rhoPair lamT
      ∧ 96029900 / 99980001 ≤ (aMin rhoPair lamT - tau0) / (1 + eps2) ^ 2
      ∧ (49 : ℝ) / 64 < 96029900 / 99980001 := by
  have ha := aMin_ge_frozen hlam
  refine ⟨ha, ?_, by norm_num⟩
  have hnum : (960299 : ℝ) / 980100 ≤ aMin rhoPair lamT - tau0 := by linarith
  have hden : (0 : ℝ) < (1 + eps2) ^ 2 := by nlinarith
  have hden' : (1 + eps2) ^ 2 ≤ (101 / 100) ^ 2 := by nlinarith
  rw [le_div_iff₀ hden]
  nlinarith

/-- **`09:396--402` as a sufficient condition for the whole gate.**  The three
numerical bounds of `09:389--390` plus the bin clause `09:391` **prove** the
fifth clause `09:392`; nothing about `lambda_T` beyond its floor is used.  So the
gate is not six independent assumptions but four plus a derived comparison, which
is exactly what `09:396` asserts.  General. -/
theorem wrapperTemplateGates_of_numerics {mT : ℕ} {lamT eps2 tau0 : ℝ}
    (hlam : 99 / 100 ≤ lamT) (he0 : 0 ≤ eps2) (he1 : eps2 ≤ 1 / 100)
    (ht0 : 0 < tau0) (ht1 : tau0 ≤ 1 / 100)
    (hbin : 2 * ⌈tau0 * (mT : ℝ)⌉₊ ≤ mT) :
    wrapperTemplateGates mT lamT eps2 tau0 := by
  obtain ⟨_, h2, h3⟩ := templateGates_reference_margins hlam he0 he1 ht0 ht1
  exact ⟨hlam, he1, ht0, ht1, hbin, le_trans (le_of_lt h3) h2⟩

/-! ## Section 4  The cover numbers -/

/-- **`09:408--410` and `eq:cover-bounds` (`06:641--646`).**  `min{B >= 1 : rho^B <
theta}`, as `Nat.sInf` of the frozen least-search set.  One definition serves all
three searches -- `B_*` at `rho_*`, `B_pair` at `99/100`, `B_ref` at `18/25` --
because the frozen displays differ only in the base. -/
noncomputable def coverExponent (rho theta : ℝ) : ℕ :=
  sInf {B : ℕ | 1 ≤ B ∧ rho ^ B < theta}

/-- **Aux A6a.**  The least search is over a nonempty set whenever `0 <= rho < 1` and
`0 < theta`, which is what makes `Nat.sInf` meaningful rather than the default
`0`.  General. -/
theorem coverExponent_setNonempty {rho theta : ℝ}
    (h0 : 0 ≤ rho) (h1 : rho < 1) (ht : 0 < theta) :
    {B : ℕ | 1 ≤ B ∧ rho ^ B < theta}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht h1
  refine ⟨max n 1, ⟨le_max_right n 1, ?_⟩⟩
  exact lt_of_le_of_lt (pow_le_pow_of_le_one h0 (le_of_lt h1) (le_max_left n 1)) hn

/-- **Aux A6b (the defining property of the three searches).**  `1 <= B` and
`rho^B < theta` at the returned value.  General. -/
theorem coverExponent_spec {rho theta : ℝ}
    (h0 : 0 ≤ rho) (h1 : rho < 1) (ht : 0 < theta) :
    1 ≤ coverExponent rho theta ∧ rho ^ coverExponent rho theta < theta :=
  Nat.sInf_mem (coverExponent_setNonempty h0 h1 ht)

/-- **Aux A6c (least-search minimality).**  Any tested endpoint `B` with `1 <= B` and
`rho^B < theta` bounds the returned value -- the property `06:666--693` uses to
certify the searches without evaluating them.  General. -/
theorem coverExponent_le {rho theta : ℝ} {B : ℕ} (hB : 1 ≤ B) (h : rho ^ B < theta) :
    coverExponent rho theta ≤ B :=
  Nat.sInf_le ⟨hB, h⟩

/-- **`06:702--707`, the first link of the frozen chain.**

"the finite gates `lambda_T >= 99/100`, `2 s x_T <= 1/100`, and `m_T >= 100`
imply `1 - rho_sing >= (98/100)(lambda_T/s)`."

Proved from `ceil(tau_0 m_T) < tau_0 m_T + 1 <= m_T/100 + 1 <= 2 m_T/100`, which
is where `m_T >= 100` is used, together with `lambda_T |Y| = s m_T` (the
`09:367--371` template decomposition read as a cardinality identity).  The two
remaining links of the `06:705--709` chain compare against `eta_C` through
`eq:eta-choice` and are not claimed here.  General. -/
theorem one_sub_rhoSing_ge {n mT s : ℕ} {tau0 lamT : ℝ}
    (hn : 0 < n) (hs : 0 < s) (hmT : 100 ≤ mT)
    (ht0 : 0 < tau0) (ht1 : tau0 ≤ 1 / 100)
    (hlam : lamT * (n : ℝ) = (s : ℝ) * (mT : ℝ)) :
    98 / 100 * (lamT / (s : ℝ)) ≤ 1 - rhoSing n mT tau0 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hmR : (100 : ℝ) ≤ (mT : ℝ) := by exact_mod_cast hmT
  have hceil : (⌈tau0 * (mT : ℝ)⌉₊ : ℝ) < tau0 * (mT : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hstep : (⌈tau0 * (mT : ℝ)⌉₊ : ℝ) ≤ 2 / 100 * (mT : ℝ) := by
    nlinarith
  have hrw : 1 - rhoSing n mT tau0
      = ((mT : ℝ) - (⌈tau0 * (mT : ℝ)⌉₊ : ℝ)) / (n : ℝ) := by
    unfold rhoSing
    field_simp
    ring
  rw [hrw]
  have hlam' : lamT / (s : ℝ) = (mT : ℝ) / (n : ℝ) := by
    field_simp
    linear_combination hlam
  rw [hlam']
  have hkey : 98 / 100 * (mT : ℝ) ≤ (mT : ℝ) - (⌈tau0 * (mT : ℝ)⌉₊ : ℝ) := by
    nlinarith
  calc 98 / 100 * ((mT : ℝ) / (n : ℝ)) = 98 / 100 * (mT : ℝ) / (n : ℝ) := by ring
    _ ≤ ((mT : ℝ) - (⌈tau0 * (mT : ℝ)⌉₊ : ℝ)) / (n : ℝ) := by gcongr

/-- **Aux A7b.**  `rho_sing < 1` under the same gates -- the hypothesis
`coverExponent` needs at `rho_sing`, and the reason `rho_*` is a legal base for
the singleton least search.  General. -/
theorem rhoSing_lt_one {n mT s : ℕ} {tau0 lamT : ℝ}
    (hn : 0 < n) (hs : 0 < s) (hmT : 100 ≤ mT)
    (ht0 : 0 < tau0) (ht1 : tau0 ≤ 1 / 100)
    (hlam : lamT * (n : ℝ) = (s : ℝ) * (mT : ℝ)) (hlam0 : 0 < lamT) :
    rhoSing n mT tau0 < 1 := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have := one_sub_rhoSing_ge hn hs hmT ht0 ht1 hlam
  have hpos : (0 : ℝ) < 98 / 100 * (lamT / (s : ℝ)) := by positivity
  linarith

/-! ## Section 5  The singleton step -/

/-- **`09:414--417`.**

"Every remaining coordinate has total projection density at least `1 - eta_C`,
and every template bin retains at least `ceil(tau_0 m_T)` symbols: even
concentrating all missing symbols in one bin cannot remove more."

The worst case is exactly the counting one: the projection misses at most
`|Y| - (|Y| - m_T + c) = m_T - c` symbols in total, so a bin of size `m_T` keeps
at least `c`.  Stated in cardinalities, general in the bin and in `c`; the real
density form is `rhoSing_density_to_card`. -/
theorem singleton_bin_retention {Yc : Type*} [Fintype Yc] [DecidableEq Yc]
    (P YTp : Finset Yc) {mT c : ℕ}
    (hbin : YTp.card = mT)
    (hP : Fintype.card Yc - mT + c ≤ P.card) :
    c ≤ (P ∩ YTp).card := by
  classical
  have hmTle : mT ≤ Fintype.card Yc := by
    rw [← hbin]; simpa using Finset.card_le_univ YTp
  have hPle : P.card ≤ Fintype.card Yc := by simpa using Finset.card_le_univ P
  have hsplit : (YTp ∩ P).card + (YTp \ P).card = YTp.card :=
    Finset.card_inter_add_card_sdiff YTp P
  have hsub : YTp \ P ⊆ Pᶜ := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    exact Finset.mem_compl.mpr ha.2
  have hcompl : (Pᶜ).card = Fintype.card Yc - P.card := Finset.card_compl P
  have hle : (YTp \ P).card ≤ Fintype.card Yc - P.card := by
    rw [← hcompl]; exact Finset.card_le_card hsub
  have hcomm : (P ∩ YTp).card = (YTp ∩ P).card := by rw [Finset.inter_comm]
  omega

/-- **Aux A7d.**  The bridge from the frozen density form of `09:379` to the
cardinality hypothesis `singleton_bin_retention` consumes: a projection of
density at least `rho_sing` has at least `|Y| - m_T + ceil(tau_0 m_T)` symbols.
General. -/
theorem rhoSing_density_to_card {Yc : Type*} [Fintype Yc] [DecidableEq Yc]
    (P : Finset Yc) {mT : ℕ} {tau0 : ℝ}
    (hY : 0 < Fintype.card Yc) (hmT : mT ≤ Fintype.card Yc)
    (hP : rhoSing (Fintype.card Yc) mT tau0 * (Fintype.card Yc : ℝ) ≤ (P.card : ℝ)) :
    Fintype.card Yc - mT + ⌈tau0 * (mT : ℝ)⌉₊ ≤ P.card := by
  have hYR : (0 : ℝ) < (Fintype.card Yc : ℝ) := by exact_mod_cast hY
  have hexp : rhoSing (Fintype.card Yc) mT tau0 * (Fintype.card Yc : ℝ)
      = (Fintype.card Yc : ℝ) - (mT : ℝ) + (⌈tau0 * (mT : ℝ)⌉₊ : ℝ) := by
    unfold rhoSing
    field_simp
  rw [hexp] at hP
  have hcast : ((Fintype.card Yc - mT + ⌈tau0 * (mT : ℝ)⌉₊ : ℕ) : ℝ)
      = (Fintype.card Yc : ℝ) - (mT : ℝ) + (⌈tau0 * (mT : ℝ)⌉₊ : ℝ) := by
    have : (((Fintype.card Yc - mT : ℕ)) : ℝ) = (Fintype.card Yc : ℝ) - (mT : ℝ) := by
      rw [Nat.cast_sub hmT]
    push_cast [this]
    ring
  have : ((Fintype.card Yc - mT + ⌈tau0 * (mT : ℝ)⌉₊ : ℕ) : ℝ) ≤ (P.card : ℝ) := by
    rw [hcast]; exact hP
  exact_mod_cast this

/-! ## Section 6  The pair step -/

/-- **`09:421--426`.**

"If `P subseteq Y^2` is such a pair projection, then
`|P cap (Y_T x Y_T)| >= (rho_pair + lambda_T^2 - 1)|Y|^2`."

Elementary inclusion--exclusion against the ambient `|Y|^2`, stated at the banked
`ScaleAlignOpening.lambdaTemplate` so the template density is not redefined.
General in `rho_pair` and in the template set. -/
theorem pair_template_intersection {Yc : Type*} [Fintype Yc] [DecidableEq Yc]
    (P : Finset (Yc × Yc)) (YT : Finset Yc) {rp : ℝ}
    (hY : 0 < Fintype.card Yc)
    (hP : rp * (Fintype.card Yc : ℝ) ^ 2 ≤ (P.card : ℝ)) :
    (rp + ScaleAlignOpening.lambdaTemplate YT ^ 2 - 1) * (Fintype.card Yc : ℝ) ^ 2
      ≤ ((P ∩ (YT ×ˢ YT)).card : ℝ) := by
  classical
  have hYR : (0 : ℝ) < (Fintype.card Yc : ℝ) := by exact_mod_cast hY
  have hQ : (YT ×ˢ YT).card = YT.card * YT.card := Finset.card_product YT YT
  have hunion : (P ∪ (YT ×ˢ YT)).card ≤ Fintype.card (Yc × Yc) := by
    simpa using Finset.card_le_univ (P ∪ (YT ×ˢ YT))
  have hcardprod : Fintype.card (Yc × Yc) = Fintype.card Yc * Fintype.card Yc :=
    Fintype.card_prod Yc Yc
  have hkey : (P ∩ (YT ×ˢ YT)).card + (P ∪ (YT ×ˢ YT)).card
      = P.card + (YT ×ˢ YT).card := Finset.card_inter_add_card_union P (YT ×ˢ YT)
  have hnat : P.card + YT.card * YT.card
      ≤ (P ∩ (YT ×ˢ YT)).card + Fintype.card Yc * Fintype.card Yc := by
    rw [hQ] at hkey
    omega
  have hcast : (P.card : ℝ) + (YT.card : ℝ) * (YT.card : ℝ)
      ≤ ((P ∩ (YT ×ˢ YT)).card : ℝ) + (Fintype.card Yc : ℝ) * (Fintype.card Yc : ℝ) := by
    exact_mod_cast hnat
  have hlam : ScaleAlignOpening.lambdaTemplate YT ^ 2 * (Fintype.card Yc : ℝ) ^ 2
      = (YT.card : ℝ) * (YT.card : ℝ) := by
    unfold ScaleAlignOpening.lambdaTemplate
    field_simp
  nlinarith [hcast, hP, hlam]

/-- **`09:427--429`.**

"Average over the `s^2` ordered pairs of fixed Stage-3 bins.  Some ordered pair
retains relative density at least `a_min`."

The `s^2` ordered bin products decompose `Y_T x Y_T` disjointly, so the
intersection cardinalities sum to the whole, and averaging produces one pair at
or above the mean.  The bins themselves are **given data** (`bins`, `hdisj`):
this block does not construct the duplication schedule.  General in `a`. -/
theorem exists_bin_pair_dense {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {s mT : ℕ}
    (bins : Fin s → Finset Yc)
    (hdisj : ∀ p p' : Fin s, p ≠ p' → Disjoint (bins p) (bins p'))
    (P : Finset (Yc × Yc)) {a : ℝ} (hs : 0 < s)
    (hP : a * ((s : ℝ) * (mT : ℝ)) ^ 2
        ≤ ((P ∩ ((Finset.univ.biUnion bins) ×ˢ (Finset.univ.biUnion bins))).card : ℝ)) :
    ∃ p p' : Fin s, a * (mT : ℝ) ^ 2 ≤ ((P ∩ (bins p ×ˢ bins p')).card : ℝ) := by
  classical
  have hdecomp : P ∩ ((Finset.univ.biUnion bins) ×ˢ (Finset.univ.biUnion bins))
      = (Finset.univ : Finset (Fin s × Fin s)).biUnion
          (fun pp => P ∩ (bins pp.1 ×ˢ bins pp.2)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hx, ⟨p, hp⟩, ⟨p', hp'⟩⟩
      exact ⟨(p, p'), hx, hp, hp'⟩
    · rintro ⟨pp, hx, h1, h2⟩
      exact ⟨hx, ⟨pp.1, h1⟩, ⟨pp.2, h2⟩⟩
  have hpieces : ∀ pp ∈ (Finset.univ : Finset (Fin s × Fin s)),
      ∀ pp' ∈ (Finset.univ : Finset (Fin s × Fin s)), pp ≠ pp' →
      Disjoint (P ∩ (bins pp.1 ×ˢ bins pp.2)) (P ∩ (bins pp'.1 ×ˢ bins pp'.2)) := by
    intro pp _ pp' _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_inter, Finset.mem_product] at hx hx'
    obtain ⟨-, hx1, hx2⟩ := hx
    obtain ⟨-, hx1', hx2'⟩ := hx'
    have h1 : pp.1 = pp'.1 := by
      by_contra hc
      exact (Finset.disjoint_left.mp (hdisj _ _ hc)) hx1 hx1'
    have h2 : pp.2 = pp'.2 := by
      by_contra hc
      exact (Finset.disjoint_left.mp (hdisj _ _ hc)) hx2 hx2'
    exact hne (Prod.ext h1 h2)
  have hsum : (P ∩ ((Finset.univ.biUnion bins) ×ˢ (Finset.univ.biUnion bins))).card
      = ∑ pp ∈ (Finset.univ : Finset (Fin s × Fin s)),
          (P ∩ (bins pp.1 ×ˢ bins pp.2)).card := by
    rw [hdecomp, Finset.card_biUnion hpieces]
  have hne : (Finset.univ : Finset (Fin s × Fin s)).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨(⟨0, hs⟩, ⟨0, hs⟩)⟩
  have hconst : ∑ _pp ∈ (Finset.univ : Finset (Fin s × Fin s)), a * (mT : ℝ) ^ 2
      ≤ ∑ pp ∈ (Finset.univ : Finset (Fin s × Fin s)),
          ((P ∩ (bins pp.1 ×ˢ bins pp.2)).card : ℝ) := by
    have hcard : (Finset.univ : Finset (Fin s × Fin s)).card = s * s := by
      simp [Finset.card_univ]
    rw [Finset.sum_const, hcard]
    have hcast : ((∑ pp ∈ (Finset.univ : Finset (Fin s × Fin s)),
        (P ∩ (bins pp.1 ×ˢ bins pp.2)).card : ℕ) : ℝ)
        = ∑ pp ∈ (Finset.univ : Finset (Fin s × Fin s)),
            ((P ∩ (bins pp.1 ×ˢ bins pp.2)).card : ℝ) := by push_cast; ring
    rw [← hcast, ← hsum]
    calc (s * s) • (a * (mT : ℝ) ^ 2)
        = a * ((s : ℝ) * (mT : ℝ)) ^ 2 := by
          simp only [nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := hP
  obtain ⟨pp, -, hpp⟩ := Finset.exists_le_of_sum_le hne hconst
  exact ⟨pp.1, pp.2, hpp⟩

/-- **`09:430--432`.**

"The Stage-3 route loses less than `tau_0`, and balanced transfer loses at most a
factor `(1+eps_2)^2`; hence `eq:wrapper-template-gates` leaves density at least
`49/64`."

The two losses are the named binders `hroute` and `htransfer` -- they are facts of
the Stage-3 block and of the balanced-transfer contract, not of this block -- and
what is proved is exactly the arithmetic step the frozen sentence makes from the
gate's fifth clause.  General. -/
theorem pair_density_after_losses {a tau0 eps2 dRoute dFinal : ℝ}
    (hroute : a - tau0 ≤ dRoute)
    (heps : 0 ≤ eps2)
    (htransfer : dRoute ≤ dFinal * (1 + eps2) ^ 2)
    (hgate : 49 / 64 ≤ (a - tau0) / (1 + eps2) ^ 2) :
    49 / 64 ≤ dFinal := by
  have hpos : (0 : ℝ) < (1 + eps2) ^ 2 := by nlinarith
  rw [le_div_iff₀ hpos] at hgate
  nlinarith

/-! ## Section 7  The small-capacity calls and the exceptional set -/

/-- **`09:436`.**  `rho = 2y^2 = 18/25`, the small-capacity contraction factor, at
the frozen `y = 3/5`. -/
noncomputable def rhoSmall : ℝ := 18 / 25

/-- **Aux A9a (`09:436` as a check).**  `2 (3/5)^2 = 18/25`: the frozen display's two
readings of the same constant agree. -/
theorem rhoSmall_eq_two_y_sq : 2 * ((3 : ℝ) / 5) ^ 2 = rhoSmall := by
  unfold rhoSmall; norm_num

/-- **`09:438--440`.**  `u_2 = 2`, `u_kappa = kappa/2 + 1` for `4 <= kappa < t_ref`.
Written as the single formula `kappa/2 + 1`, which `smallCopyWidth_two` checks
reproduces the frozen `u_2 = 2` -- so the frozen split is presentational. -/
def smallCopyWidth (kappa : ℕ) : ℕ := kappa / 2 + 1

/-- **Aux A9b (`09:438`).**  `u_2 = 2`, from the uniform formula. -/
theorem smallCopyWidth_two : smallCopyWidth 2 = 2 := rfl

/-- **Aux A9c.**  Every small-capacity width is at least `1`, which is the `k >= 1`
hypothesis of `lem:product-projection-cover`.  General. -/
theorem one_le_smallCopyWidth (kappa : ℕ) : 1 ≤ smallCopyWidth kappa := by
  unfold smallCopyWidth; omega

/-- **`09:444--447`, the row-ladder identification.**

"These are exactly the covers consumed by the certified-scale row ladder
`lem:certified-row-ladder`: its `l = 1` case has `u_2 = 2`, while
`l = log_2 kappa >= 2` has `u_kappa = kappa/2 + 1`."

The ladder's copy count at level `l` is `2^{l-1} + 1` (`A:158`), and that is
`u_{2^l}` for **every** `l >= 1`, including `l = 1`.  Only this arithmetic
identification is checked; `lem:certified-row-ladder` has no Lean declaration and
its conclusion is neither stated nor used. -/
theorem smallCopyWidth_dyadic {l : ℕ} (h : 1 ≤ l) :
    smallCopyWidth (2 ^ l) = 2 ^ (l - 1) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  unfold smallCopyWidth
  simp [pow_succ]

/-- **The `eq:cover-bounds` coefficient identity (`06:648--649`), proved.**

At `t_ref = 2^k` the frozen coefficient `t_ref/2 + log_2 t_ref - 2` is exactly
`2^{k-1} + k - 2`, and that is the sum of the small-capacity widths
`sum_{l=1}^{k-1} u_{2^l}` over the dyadic `2 <= kappa < t_ref` of `09:442`.  This
is the load-bearing consistency check between `09:434--447` and `06:639--654`:
had the two disagreed, the `09` covers would not fit the `06` budget. -/
theorem smallCopyWidth_sum {k : ℕ} (hk : 1 ≤ k) :
    ∑ l ∈ Finset.Ico 1 k, smallCopyWidth (2 ^ l) = 2 ^ (k - 1) + k - 2 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih, smallCopyWidth_dyadic hn]
      have h1 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
      simp only [Nat.add_sub_cancel]
      omega

/-- **`eq:cover-bounds` (`06:647--651`), verbatim, at `t_ref = 2^k`.**
`e_0^max = (B_ref - 1)(t_ref/2 + log_2 t_ref - 2) + (B_sing - 1) + 2(B_pair - 1)`.
`09:452--453` says only that "the construction records an explicit deterministic
upper bound `e_0 <= e_0^max`"; the value is the schedule's, not this block's. -/
def e0Max (Bref Bsing Bpair k : ℕ) : ℕ :=
  (Bref - 1) * (2 ^ (k - 1) + k - 2) + (Bsing - 1) + 2 * (Bpair - 1)

/-- **`09:448--453`.**

"Let `E_0` be the union of all singleton, pair, and small-copy covers, and put
`e_0 = |E_0|`.  The construction records an explicit deterministic upper bound
`e_0 <= e_0^max`."

Proved from the three per-cover cardinality bounds of
`lem:product-projection-cover` (`1 . (B_sing - 1)`, `2 . (B_pair - 1)`, and
`u_{2^l} . (B_ref - 1)` for each dyadic level), the union bound, and
`smallCopyWidth_sum`.  General in the three cover numbers and in `k`. -/
theorem e0_le_e0Max {Bref Bsing Bpair k : ℕ} (hk : 1 ≤ k)
    (Esing Epair : Finset (Fin q)) (Esmall : ℕ → Finset (Fin q))
    (hsing : Esing.card ≤ 1 * (Bsing - 1))
    (hpair : Epair.card ≤ 2 * (Bpair - 1))
    (hsmall : ∀ l ∈ Finset.Ico 1 k,
      (Esmall l).card ≤ smallCopyWidth (2 ^ l) * (Bref - 1)) :
    (Esing ∪ Epair ∪ (Finset.Ico 1 k).biUnion Esmall).card
      ≤ e0Max Bref Bsing Bpair k := by
  classical
  have hb : ((Finset.Ico 1 k).biUnion Esmall).card
      ≤ ∑ l ∈ Finset.Ico 1 k, (Esmall l).card := Finset.card_biUnion_le
  have hsum : ∑ l ∈ Finset.Ico 1 k, (Esmall l).card
      ≤ ∑ l ∈ Finset.Ico 1 k, smallCopyWidth (2 ^ l) * (Bref - 1) :=
    Finset.sum_le_sum hsmall
  have hfac : ∑ l ∈ Finset.Ico 1 k, smallCopyWidth (2 ^ l) * (Bref - 1)
      = (2 ^ (k - 1) + k - 2) * (Bref - 1) := by
    rw [← Finset.sum_mul, smallCopyWidth_sum hk]
  have hu1 : (Esing ∪ Epair ∪ (Finset.Ico 1 k).biUnion Esmall).card
      ≤ Esing.card + Epair.card + ((Finset.Ico 1 k).biUnion Esmall).card :=
    le_trans (Finset.card_union_le _ _)
      (by exact Nat.add_le_add_right (Finset.card_union_le _ _) _)
  unfold e0Max
  have hbound : ((Finset.Ico 1 k).biUnion Esmall).card
      ≤ (Bref - 1) * (2 ^ (k - 1) + k - 2) := by
    refine le_trans hb (le_trans hsum ?_)
    rw [hfac, Nat.mul_comm]
  calc (Esing ∪ Epair ∪ (Finset.Ico 1 k).biUnion Esmall).card
      ≤ Esing.card + Epair.card + ((Finset.Ico 1 k).biUnion Esmall).card := hu1
    _ ≤ 1 * (Bsing - 1) + 2 * (Bpair - 1) + (Bref - 1) * (2 ^ (k - 1) + k - 2) :=
        Nat.add_le_add (Nat.add_le_add hsing hpair) hbound
    _ = (Bref - 1) * (2 ^ (k - 1) + k - 2) + (Bsing - 1) + 2 * (Bpair - 1) := by ring

/-! ## Section 8  The assembled exceptional set -/

/-- **The assembled deliverable of `sec:wrapper-projection-covers`
(`09:404--453`).**

For a retained outer column set `S` of density at least `theta`, there is a single
exceptional set `E_0` with `e_0 = |E_0| <= e_0^max` that meets **every** poor
singleton at `rho_*`, **every** poor pair at `rho_pair = 99/100`, and **every**
poor coordinate set of size `u_kappa` at `rho = 18/25`, for every dyadic
`2 <= kappa < t_ref = 2^k`.  This is exactly what the later blocks of the dense
rung consume, and `e0Max` is the `eq:cover-bounds` value.

The deliverable is existential.  Its first clause is literally
`productProjectionCover`'s conclusion at `k = 1`, so
`productProjectionCover_witness_is_nonempty` refutes `E_0 = empty` at the same
legal probe; and the cardinality clause bars `E_0 = univ` as soon as `q` exceeds
the schedule budget.

This **feeds** `hDenseRung` and does not discharge or narrow it: the remaining
blocks `09:461--1781` stay GAP-EXPOSED. -/
theorem exists_initial_exceptional_set (S : Finset (Fin q → Y)) {k : ℕ}
    {rstar theta : ℝ}
    (hY : 0 < Fintype.card Y) (hk : 1 ≤ k)
    (hr0 : 0 < rstar) (hr1 : rstar < 1) (hth : 0 < theta)
    (hS : theta * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ)) :
    ∃ E : Finset (Fin q),
      E.card ≤ e0Max (coverExponent rhoSmall theta) (coverExponent rstar theta)
          (coverExponent rhoPair theta) k
        ∧ (∀ J : Finset (Fin q), J.card = 1 →
            PoorProjection rstar J S → (E ∩ J).Nonempty)
        ∧ (∀ J : Finset (Fin q), J.card = 2 →
            PoorProjection rhoPair J S → (E ∩ J).Nonempty)
        ∧ (∀ l ∈ Finset.Ico 1 k, ∀ J : Finset (Fin q),
            J.card = smallCopyWidth (2 ^ l) →
            PoorProjection rhoSmall J S → (E ∩ J).Nonempty) := by
  classical
  have hp0 : (0 : ℝ) < rhoPair := by unfold rhoPair; norm_num
  have hp1 : rhoPair < 1 := by unfold rhoPair; norm_num
  have hs0 : (0 : ℝ) < rhoSmall := by unfold rhoSmall; norm_num
  have hs1 : rhoSmall < 1 := by unfold rhoSmall; norm_num
  obtain ⟨hB1star, hBstar⟩ := coverExponent_spec (le_of_lt hr0) hr1 hth
  obtain ⟨hB1pair, hBpair⟩ := coverExponent_spec (le_of_lt hp0) hp1 hth
  obtain ⟨hB1ref, hBref⟩ := coverExponent_spec (le_of_lt hs0) hs1 hth
  obtain ⟨Esing, hsing, hsingmeet⟩ :=
    productProjectionCover S hY (le_refl 1) hB1star hr0 hr1 hBstar hS
  obtain ⟨Epair, hpair, hpairmeet⟩ :=
    productProjectionCover (k := 2) S hY (by norm_num) hB1pair hp0 hp1 hBpair hS
  have hsm : ∀ l : ℕ, ∃ E : Finset (Fin q),
      E.card ≤ smallCopyWidth (2 ^ l) * (coverExponent rhoSmall theta - 1) ∧
      ∀ J : Finset (Fin q), J.card = smallCopyWidth (2 ^ l) →
        PoorProjection rhoSmall J S → (E ∩ J).Nonempty := by
    intro l
    exact productProjectionCover S hY (one_le_smallCopyWidth _) hB1ref hs0 hs1 hBref hS
  choose Esmall hsmallcard hsmallmeet using hsm
  refine ⟨Esing ∪ Epair ∪ (Finset.Ico 1 k).biUnion Esmall, ?_, ?_, ?_, ?_⟩
  · exact e0_le_e0Max hk Esing Epair Esmall hsing hpair (fun l _ => hsmallcard l)
  · intro J hJ hpoor
    obtain ⟨a, ha⟩ := hsingmeet J hJ hpoor
    rw [Finset.mem_inter] at ha
    exact ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_union_left _
      (Finset.mem_union_left _ ha.1), ha.2⟩⟩
  · intro J hJ hpoor
    obtain ⟨a, ha⟩ := hpairmeet J hJ hpoor
    rw [Finset.mem_inter] at ha
    exact ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_union_left _
      (Finset.mem_union_right _ ha.1), ha.2⟩⟩
  · intro l hl J hJ hpoor
    obtain ⟨a, ha⟩ := hsmallmeet l J hJ hpoor
    rw [Finset.mem_inter] at ha
    exact ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨l, hl, ha.1⟩), ha.2⟩⟩

/-! ## Section 9  Aux-lemma battery, non-vacuity witnesses, statement poles -/

/-- **Aux A1b.**  A projection to `J` has at most `|Y|^{|J|}` elements -- the frozen
density's denominator is an actual upper bound.  General. -/
theorem projSet_card_le (J : Finset (Fin q)) (S : Finset (Fin q → Y)) :
    (projSet J S).card ≤ Fintype.card Y ^ J.card := by
  classical
  have h := Finset.card_le_univ (projSet J S)
  rw [Fintype.card_fun, Fintype.card_coe] at h
  exact h

omit [Fintype Y] in
/-- **Aux A1c (monotonicity).**  Projection is monotone in the projected set.
General. -/
theorem projSet_mono {J : Finset (Fin q)} {S S' : Finset (Fin q → Y)} (h : S ⊆ S') :
    projSet J S ⊆ projSet J S' := Finset.image_subset_image h

omit [Fintype Y] in
/-- **Aux A1d.**  A projection never has more elements than the set projected.
General. -/
theorem projSet_card_le_card (J : Finset (Fin q)) (S : Finset (Fin q → Y)) :
    (projSet J S).card ≤ S.card := Finset.card_image_le

omit [Fintype Y] in
/-- **Aux A1e (nonemptiness is preserved).**  General. -/
theorem projSet_nonempty {J : Finset (Fin q)} {S : Finset (Fin q → Y)}
    (h : S.Nonempty) : (projSet J S).Nonempty := Finset.Nonempty.image h _

/-- **Aux A1f (the identity case).**  The projection of the *full* cube is the full
projection cube, for every `J`.  This is the round-trip fact that makes the
density normalization correct: extend any `g : J -> Y` by a constant off `J`.
Requires a nonempty alphabet, carried explicitly. -/
theorem projSet_univ (J : Finset (Fin q)) (hY : 0 < Fintype.card Y) :
    projSet J (Finset.univ : Finset (Fin q → Y)) = Finset.univ := by
  classical
  obtain ⟨y0⟩ : Nonempty Y := Fintype.card_pos_iff.mp hY
  refine Finset.eq_univ_of_forall ?_
  intro g
  refine Finset.mem_image.mpr ⟨fun i => if h : i ∈ J then g ⟨i, h⟩ else y0,
    Finset.mem_univ _, ?_⟩
  funext i
  simp

/-- **Aux A2a (the identity case is never poor).**  For `rho <= 1`, the full cube has
no poor coordinate set -- so poorness is a genuine restriction on `S` and not a
shape artefact of the definition.  General. -/
theorem not_poorProjection_univ {ρ : ℝ} (J : Finset (Fin q)) (hY : 0 < Fintype.card Y)
    (hρ : ρ ≤ 1) : ¬ PoorProjection ρ J (Finset.univ : Finset (Fin q → Y)) := by
  classical
  unfold PoorProjection
  rw [projSet_univ J hY, Finset.card_univ, Fintype.card_fun, Fintype.card_coe]
  push Not
  push_cast
  have hpos : (0 : ℝ) < (Fintype.card Y : ℝ) ^ J.card := by
    have : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
    positivity
  nlinarith

/-- **Aux A2b (monotonicity in the threshold).**  Raising `rho` can only create more
poor sets, which is why `rho_* = max{rho_sing, 1 - eta_C}` of `09:407` is the
right combination: the cover at the larger base covers both.  General. -/
theorem poorProjection_mono_rho {ρ ρ' : ℝ} {J : Finset (Fin q)} {S : Finset (Fin q → Y)}
    (hY : 0 < Fintype.card Y) (h : ρ ≤ ρ') (hp : PoorProjection ρ J S) :
    PoorProjection ρ' J S := by
  unfold PoorProjection at hp ⊢
  have hpos : (0 : ℝ) < (Fintype.card Y : ℝ) ^ J.card := by
    have : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
    positivity
  nlinarith

/-- **Aux A6d (the searches are not trivial).**  If `theta <= rho` then the returned
exponent is at least `2`, so `B - 1 >= 1` and the frozen cover bound `k(B-1)` is
not vacuously `0`.  General. -/
theorem two_le_coverExponent {rho theta : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1)
    (ht : 0 < theta) (hge : theta ≤ rho) : 2 ≤ coverExponent rho theta := by
  obtain ⟨hB1, hB⟩ := coverExponent_spec h0 h1 ht
  rcases Nat.lt_or_ge (coverExponent rho theta) 2 with hlt | hge2
  · have : coverExponent rho theta = 1 := by omega
    rw [this, pow_one] at hB
    linarith
  · exact hge2

/-- **`06:700` as an implication, not an assertion.**  "the singleton cover in the
proof has contraction factor `rho_* = max{rho_sing, 1 - eta_C} = 1 - eta_C`."
The evaluation holds exactly when `rho_sing <= 1 - eta_C`, which `06:704--709`
derives from `eq:eta-choice`; that derivation is `06`'s and is not claimed here. -/
theorem rhoStar_eq_one_sub_etaC {n mT : ℕ} {tau0 etaC : ℝ}
    (h : rhoSing n mT tau0 ≤ 1 - etaC) : rhoStar n mT tau0 etaC = 1 - etaC :=
  max_eq_right h

/-- **Statement pole (the fifth gate clause is a genuine constraint on
`lambda_T`).**  At `lambda_T = 1/10` one has `a_min = 0`, so
`(a_min - tau_0)/(1+eps_2)^2` is **negative** and the frozen `49/64` comparison
fails.  `eq:wrapper-template-gates` therefore does real work, and
`wrapperTemplateGates_of_numerics` is not a tautology.

A **tier-3 probe outside the frozen regime** `lambda_T >= 99/100`: its whole
content is that the frozen regime excludes the point at which it holds, and it
must never be read as an instance of the gates. -/
theorem templateGates_last_clause_needs_lambda :
    ¬ ((49 : ℝ) / 64 ≤ (aMin rhoPair (1 / 10) - 1 / 100) / (1 + 1 / 100) ^ 2) := by
  unfold aMin rhoPair
  norm_num

/-- **Non-vacuity (tier 2): the frozen gates are inhabited at the banked legal
tier.**

`eq:wrapper-template-gates` holds at `m_T = 100` (the frozen floor of `06:703`),
`lambda_T = 99/100` and `eps_2 = 1/100` (the frozen floor and ceiling of
`09:389`), and `tau_0 = 2 s x_T` evaluated at the **banked** tier `s = 2^340`,
`b_T = 512` -- the pair already used by
`ScaleAlignOpening.referenceProfileGates_legal_instance` and by
`WrapperLowRungs.strict_xT_membership_at_banked_tier`, so no numeral is invented.

The instance is **not degenerate in the direction that matters**: `tau_0 =
2^{-171}` is strictly positive, so `ceil(tau_0 m_T) = 1` rather than `0`, and the
bin clause `2 ceil(tau_0 m_T) = 2 <= 100 = m_T` is a genuine comparison.  A
`tau_0 = 0` reading would make `09:416`'s retention conclusion empty.

No parameter may be read out of the instance: `eq:tref-search` still forces
`k_ref >= 2^19`, and `s`, `b_T`, `m_T` are fixed by the schedule. -/
theorem wrapperTemplateGates_legal_instance :
    0 < tauZero (2 ^ 340) (DenseStageFourOpening.xTdepth 512)
      ∧ tauZero (2 ^ 340) (DenseStageFourOpening.xTdepth 512) ≤ 1 / 100
      ∧ wrapperTemplateGates 100 (99 / 100) (1 / 100)
          (tauZero (2 ^ 340) (DenseStageFourOpening.xTdepth 512)) := by
  set t0 : ℝ := tauZero (2 ^ 340) (DenseStageFourOpening.xTdepth 512) with ht0def
  have hval : t0 = 2 * (2 : ℝ) ^ 340 * (1 / 2 ^ 512) := by
    rw [ht0def]
    unfold tauZero DenseStageFourOpening.xTdepth
    push_cast
    ring
  have hbig : (200 : ℝ) * 2 ^ 340 ≤ 2 ^ 512 := by
    have h1 : (200 : ℝ) ≤ 2 ^ 172 := by norm_num
    have h2 : (0 : ℝ) < (2 : ℝ) ^ 340 := by positivity
    calc (200 : ℝ) * 2 ^ 340 ≤ 2 ^ 172 * 2 ^ 340 :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
      _ = 2 ^ 512 := by rw [← pow_add]
  have hpos : 0 < t0 := by rw [hval]; positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ 512 := by positivity
  have hle : t0 ≤ 1 / 100 := by
    rw [hval, show (2 : ℝ) * 2 ^ 340 * (1 / 2 ^ 512) = 2 * 2 ^ 340 / 2 ^ 512 from by ring,
      div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 100)]
    calc (2 : ℝ) * 2 ^ 340 * 100 = 200 * 2 ^ 340 := by ring
      _ ≤ 2 ^ 512 := hbig
      _ = 1 * 2 ^ 512 := by ring
  refine ⟨hpos, hle, ?_⟩
  refine wrapperTemplateGates_of_numerics (by norm_num) (by norm_num) (by norm_num)
    hpos hle ?_
  have hceil : ⌈t0 * ((100 : ℕ) : ℝ)⌉₊ ≤ 1 := by
    refine Nat.ceil_le.mpr ?_
    push_cast
    have hrw : 2 * (2 : ℝ) ^ 340 * (1 / 2 ^ 512) * 100 = 200 * 2 ^ 340 / 2 ^ 512 := by
      ring
    rw [hval, hrw, div_le_one hden]
    exact hbig
  omega

/-- **Statement pole (the existential is not satisfied by the trivial witness).**

Over `Y = Bool`, `q = 1`, `S = {const true}`, the singleton `J = {0}` projects
onto one of the two symbols, i.e. density `1/2 < 3/4`, so it is poor at
`rho = 3/4`.  Hence **every** set `E` meeting all poor singletons is nonempty --
in particular `E = empty`, the smallest set satisfying the cardinality clause
`|E| <= 1 . (3-1)`, is refuted.

A **tier-3 separating probe at a minimal carrier**, cited only for what it
separates.  `productProjectionCover_probe_is_legal` certifies that the probe
satisfies the theorem's own hypotheses, so this refutes the frozen existential
and not a strengthened one. -/
theorem productProjectionCover_witness_is_nonempty :
    ∀ E : Finset (Fin 1),
      (∀ J : Finset (Fin 1), J.card = 1 →
        PoorProjection (3 / 4 : ℝ) J ({fun _ => true} : Finset (Fin 1 → Bool)) →
        (E ∩ J).Nonempty) → E.Nonempty := by
  intro E h
  have hJ : ({0} : Finset (Fin 1)).card = 1 := rfl
  have hpoor : PoorProjection (3 / 4 : ℝ) ({0} : Finset (Fin 1))
      ({fun _ => true} : Finset (Fin 1 → Bool)) := by
    unfold PoorProjection projSet
    rw [Finset.image_singleton, hJ]
    norm_num
  obtain ⟨a, ha⟩ := h _ hJ hpoor
  exact ⟨a, (Finset.mem_inter.mp ha).1⟩

/-- **Legality receipt for the pole above.**  At `theta = 1/2`, `rho = 3/4`, `B = 3`,
`k = 1`, `q = 1`, `Y = Bool`: `theta |Y|^q = 1 <= |S|`, `(3/4)^3 = 27/64 < 1/2`,
`0 < 3/4 < 1`, and `0 < |Bool|`.  Every hypothesis of `productProjectionCover` is
met, so the probe is an instance of the frozen lemma. -/
theorem productProjectionCover_probe_is_legal :
    ((1 : ℝ) / 2) * (Fintype.card Bool : ℝ) ^ (1 : ℕ)
        ≤ ((({fun _ => true} : Finset (Fin 1 → Bool)).card : ℕ) : ℝ)
      ∧ ((3 : ℝ) / 4) ^ 3 < 1 / 2
      ∧ (0 : ℝ) < 3 / 4 ∧ (3 : ℝ) / 4 < 1 ∧ 0 < Fintype.card Bool := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Hypothesis consistency, made kernel-visible.**

The full binder bundle of `exists_initial_exceptional_set` -- `hY`, `hk`, `hr0`,
`hr1`, `hth`, `hS` -- is simultaneously satisfiable, and the theorem *fires*: at
`Y = Bool`, `q = 1`, `k = 1`, `S = {const true}`, `theta = 1/2`,
`rho_* = 3/4`, all six hypotheses hold and the assembled exceptional set exists.
No `False` is derivable from the bundle, so the assembled deliverable is not
vacuous.

This is the same **tier-3** probe as the pole above and carries the same warning:
it is a minimal-carrier separating instance, and no route parameter may be read
out of it.  In particular `k = 1` makes the small-capacity index range
`Ico 1 1` empty, which is the honest reading of "`2 <= kappa < t_ref`" at
`t_ref = 2`; the tier-2 legality of the *gates* is
`wrapperTemplateGates_legal_instance`, not this. -/
theorem exists_initial_exceptional_set_fires_at_probe :
    ∃ E : Finset (Fin 1),
      E.card ≤ e0Max (coverExponent rhoSmall (1 / 2)) (coverExponent (3 / 4) (1 / 2))
          (coverExponent rhoPair (1 / 2)) 1
        ∧ (∀ J : Finset (Fin 1), J.card = 1 →
            PoorProjection (3 / 4) J ({fun _ => true} : Finset (Fin 1 → Bool)) →
            (E ∩ J).Nonempty)
        ∧ (∀ J : Finset (Fin 1), J.card = 2 →
            PoorProjection rhoPair J ({fun _ => true} : Finset (Fin 1 → Bool)) →
            (E ∩ J).Nonempty)
        ∧ (∀ l ∈ Finset.Ico 1 1, ∀ J : Finset (Fin 1),
            J.card = smallCopyWidth (2 ^ l) →
            PoorProjection rhoSmall J ({fun _ => true} : Finset (Fin 1 → Bool)) →
            (E ∩ J).Nonempty) :=
  exists_initial_exceptional_set _ (by norm_num) (le_refl 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end EthInapproximability.ParameterizedNP.WrapperProjectionCovers
