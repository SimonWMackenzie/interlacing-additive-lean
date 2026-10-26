import EthInapproximability.ParameterizedNP.ProtectedEarlyClosure

/-!
# Parameterized NP route: the Bob-heavy donor count `e_B`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines `09:1535--1547`**,
  inside `sec:wrapper-mass-redistribution`.  Opened first-hand this tranche, in
  print order:
  * **`09:1535--1539`**, the definition: "Call a clean donor `j` *Bob-heavy* if
    `sum_{v: first-Bob frontier node} P_v({j}) > eta_R/4`";
  * **`09:1540--1541`**, "where mass is normalized by `m`, as in the definition of
    `P_v`.  Their number `e_B` satisfies";
  * **`eq:wrapper-bob-heavy-count`** (display `09:1542--1547`, label `09:1546`):
    `e_B <= 512 mu_P B_theta L_q s e_0 / ((1-vartheta) eta_R)`;
  * **`09:1548`**, "Let `J_good` be the other clean donors" -- the *next* frozen
    sentence, whose counting consequence is already banked and is **not**
    re-derived here.
* **Cross-anchors opened first-hand this tranche:**
  * `eq:wrapper-total-early-mass` (display `09:1526--1534`, label `09:1533`), the
    input of this display: `P_B < 128 mu_P B_theta L_q s K_B <= 128 mu_P B_theta
    L_q s e_0/(1-vartheta)`;
  * `09:1519--1525`, `J_clean` and the contrapositive call with `J_0 = J_clean`,
    which is why the donor set of the count below is
    `RoutedSystem.cleanFinal` and not a free `Finset`;
  * `09:1370--1376`, the two protected reservoirs of mass `mu_P = 1/184` and the
    definition of `P_v(J_0)` "normalized by `m`" -- the readout that makes the
    per-donor mass nonnegative;
  * `09:450` (`e_0 = |E_0|`) together with **`09:453`**, "The construction records
    an explicit deterministic upper bound `e_0 <= e_0^max`";
  * **`eq:terminal-uniform-bounds`** (display `06:716--731`, label `06:730`),
    whose `06:720--722` line **defines**
    `E_B = ceil(512 mu_P B_theta L_q s e_0^max / ((1-vartheta) eta_R))`, and whose
    `06:732--733` sentence reads "The counting in `sec:first-wrapper` then gives
    at most `E_B` Bob-heavy clean sources";
  * `eq:eta-choice` (display `06:204--219`) with `06:227--233`
    (`0 < eta_R <= eta_C/2 < tau < x_N`), the **defining** display of `eta_R`;
  * `09:1719--1726`, the derived good-donor count
    `|J_good| = c - e_B >= q - ceil(e_0^max/(1-vartheta)) - E_B = q - E_T`, which
    is the consumer of `e_B <= E_B`;
  * `09:1268` (`vartheta = 9/16`) and `06:718` (`vartheta = 9/16` again) -- the
    **`vartheta` twins**, see below;
  * `09:1250--1259` (`kappa_v = 2^{r-d_v}`, `kappa_v >= 2` at a first-Bob node,
    `kappa_v = 1` at a final Alice node) -- the **two-kappa trap**, see below.
* **Reader counterpart: NONE is claimable, inherited unchanged.**
  `routes/parameterized-np/reader-facing/sections/A-stage4-details.tex:370--399`
  was opened first-hand this tranche and remains the only reader passage covering
  this material.  It is running prose ("The complete owner--donor count is finite:
  it uses only the fixed reservoir masses above ...  It is expanded line by line
  in the ultra-explicit companion"), and its single displayed endpoint
  (`A-stage4-details.tex:394`) is `eq:wrapper-u-dense`, which this module does not
  state.  The reader artifact contains **no** occurrence of "Bob-heavy" at all
  (checked this tranche across all reader sections).  The READER-COUNTERPART rule
  forbids citing prose and forbids reusing an item already assigned to another
  declaration, so none is cited rather than one invented.  This matches the
  inherited `PROTECTED-EARLY-CLOSURE-001` and `FRONTIER-SUM-ASSEMBLY-001`
  outcomes and re-decides nothing.

## Census first: what was already banked, and what this tranche adds

The declared range `09:1535--1547` was censused line by line against the banked
tree before a single line was written.  Everything in the following list is
consumed **by pin** and **nothing of it is restated**:

* `09:1535--1539`, the Bob-heavy threshold.  **BANKED** as
  `WrapperMassRedistribution.BobHeavy` (`eta_R/4 < mass`) and, at a routed
  system, `MassRedistributionCounting.bobHeavyDonors` with its membership
  readout, its `cleanFinal` subset lemma and its antitone lemma.
* `09:1537`, the per-donor aggregation `sum_{v first-Bob} P_v({j})`.  **BANKED**
  as `MassRedistributionCounting.firstBobMass`, with the singleton readout
  `donorMass_singleton` and `firstBobMass_eq_sum_donorMass_singleton`.
* The exchange of summation orders between `09:1526` and `09:1537`.  **BANKED**
  as `MassRedistributionCounting.earlyMass_eq_sum_firstBobMass`.
* `eq:wrapper-bob-heavy-count` as *arithmetic*.  **BANKED** as
  `WrapperMassRedistribution.card_le_of_lower_bounds` and
  `WrapperMassRedistribution.wrapperBobHeavyCount`.
* `eq:wrapper-bob-heavy-count` as an *engine*.  **BANKED** as
  `MassRedistributionCounting.wrapperBobHeavyCount_engine`, with **both** of its
  inputs -- the per-donor nonnegativity `hnonneg` and the total-mass bound
  `htot` -- carried as binders.
* `eq:wrapper-total-early-mass` at the canonical routed system.  **BANKED** as
  `ProtectedEarlyClosure.canonical_wrapperTotalEarlyMass`.
* `E_B` (`06:720--722`).  **BANKED** as `ParameterSchedule.EB`, ceiling
  preserved.
* `09:1719--1726`'s good-donor arithmetic.  **BANKED** as
  `WrapperMassRedistribution.goodDonorCount_ge`, which carries `e_B <= E_B` as
  its binder `heB`.

**The gap this tranche closes is exactly the two binders of the banked count
engine, plus the schedule bridge that `heB` names.**  Concretely:

1. `hnonneg` is **obtained** from the frozen reservoir readout of `09:1370--1376`
   (Section 1) rather than assumed: `P_v(\{j\}) = mu_P (d_0 + d_1)` with the two
   retained densities in `[0,1]`, so the per-donor first-Bob mass of `09:1537` is
   nonnegative as a *theorem*;
2. `htot` is **obtained** at the canonical routed system by consuming
   `ProtectedEarlyClosure.canonical_wrapperTotalEarlyMass` in an actual proof
   term at the frozen donor set `J_0 = J_clean` of `09:1521` (Section 3);
3. `e_B <= E_B` (`06:732--733`), the bridge from `eq:wrapper-bob-heavy-count` to
   the schedule constant, is **proved** from `09:453`'s `e_0 <= e_0^max` and the
   frozen ceiling (Section 2).  This is a **supply**, not a discharge: no proof
   term below composes Section 2 with `goodDonorCount_ge`, whose `heB` is stated
   over the reals, so one `le_trans` and one `Nat.cast_le` remain at the
   consumer.  `heB` is therefore still a binder of that banked lemma.

Both retirements happen at the site that consumes them, which is the only place a
binder can be retired.

## What is asserted, and what is not

`eq:wrapper-bob-heavy-count` **is** asserted at the canonical routed system, in
its frozen direction (non-strict `<=`) and at the frozen right-hand side
`512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)` with **every schedule quantity
pedigreed**:

| symbol | status | frozen defining display | Lean pedigree |
| --- | --- | --- | --- |
| `mu_P` | DEFINED `= 1/184` | `09:1370--1373` | `WrapperProtectedEarly.muP` |
| `B_theta` | DEFINED (cover) | `09:1378--1384`, `06:718` | `WrapperProtectedEarly.Btheta` |
| `L_q` | DEFINED `= ceil(log_2 2q)+1` | `09:1380--1382`, `06:719` | `WrapperProtectedEarly.Lq` |
| `s` | DEFINED `= 2^{h_s}` | `06:1864--1894` | carried as the dyadic `2^{r_3}` |
| `e_0` | DEFINED `= |E_0|` | `09:450` | `(E0.card : R)`, evaluated |
| `e_0^max` | DEFINED (cover search) | `06:639--653`, at `09:453` | `ParameterSchedule` arg `e0m` |
| `vartheta` | DEFINED `= 9/16` | `09:1268` (and `06:718`) | `DenseWrapperFrontier.vartheta` |
| `eta_R` | DEFINED by `eq:eta-choice` | `06:204--219` | `ParameterSchedule.etaR` |
| `E_B` | DEFINED (ceiling) | `06:720--722` | `ParameterSchedule.EB` |

No numeral is assigned to any of them anywhere below; each arrives by evaluating
the banked definitional chain.  The **only** free real of the spine is `eta_R`,
and it is never given a value on the spine either: the frozen counting step needs
`eta_R > 0` and nothing more, so `hetaR` is an explicit binder, exactly as the
banked arithmetic lemma's own docstring records.  Section 5's probe does not pick
an `eta_R` either -- it evaluates `ParameterSchedule.etaR` and uses the schedule's
own derived ceiling `eta_R <= 1/36800`.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:262--263`) is
neither stated nor implied.  `09:1548--1781` -- `J_good`, the exceptional-final
count, the four-category table, the terminal pigeonhole, call (iv), and the final
contradiction -- remains **OPEN**, and nothing below touches it.

### The `vartheta` twins

`vartheta = 9/16` is declared twice in this development, from two different frozen
displays: `DenseWrapperFrontier.vartheta` (`09:1268`, the frontier weight
threshold, which is the one `eq:wrapper-clean-count` and
`eq:wrapper-total-early-mass` use, and therefore the one the count's right-hand
side inherits) and `ParameterSchedule.vartheta` (`eq:terminal-uniform-bounds`,
`06:718`, the schedule constant inside `E_B`).  Section 2 is the seam where the
two meet, because its hypothesis carries the `09:1268` twin and its conclusion is
about `ParameterSchedule.EB`; it therefore consumes the banked
`FrontierSumAssembly.vartheta_twins_agree` **by pin** rather than assuming the two
names denote one number.  Nothing below declares a `vartheta`.

### The two-kappa trap

`kappa_v` takes exactly two kinds of value on the frozen frontier: `kappa_v >= 2`
at a first-Bob node (`09:1259`) and `kappa_v = 1` at a final Alice node
(`09:1250--1252`), and the banked
`FrontierSumAssembly.two_kappa_trap_at_the_final_nodes` is the check that
conflating them makes the weight bound contradict the frozen final-node
classification.  The trap reaches this module through the *index set of the
count*: `09:1537` sums `P_v({j})` over **first-Bob** frontier nodes only, and the
banked `firstBobMass` sums over `bobNodes` and no wider.  Widening that sum to the
whole frontier would silently add the final-Alice column -- the very column whose
`kappa_v = 1` the trap forbids treating like a first-Bob node -- and would import
mass that `eq:wrapper-total-early-mass` does **not** bound, since `P_B` is also a
`bobNodes` sum.  Section 4's `firstBobMass_congr_on_bobNodes` and
`bobHeavyDonors_congr_on_bobNodes` are the count-side checks that both the mass
and the Bob-heavy set are functions of the first-Bob column alone.  The banked
trap lemma is cited, never restated.

## GAP-EXPOSED, explicitly

1. **`hLocEx` in both bundles.**  `thm:certified-localized-extension`
   (`A:109--146`), the entry point of **EXPANDER-001**, survives as an explicit
   named binder in both halves of Section 3's bundle -- `hLocExCC` in the
   clean-count half and `hLocExEP` in the protected-closure half -- inherited
   verbatim from the banked
   `ProtectedEarlyClosure.canonical_wrapperTotalEarlyMass`.  It is never an
   `axiom`, never a premise-bundle field, never an opaque certificate.
2. **`hfinal`** (`09:1346--1350`, licensed by `lem:final-reference-uniqueness`
   `09:1315--1318`) likewise stays an explicit binder, as do `halleged`, `hcost`,
   `hres`, `hE1cc`, `hE2cc`, `hE1ep`, `hE2ep`, `htcert`, `htcertEP`, `hQuery`,
   `hBlocks`, `hbase` and `hbaseEP`.  **Full-bundle satisfiability is NOT
   claimed** anywhere in this module.
3. **`09:1548--1564` is not landed here.**  `J_good`, the owner injectivity and
   `eq:wrapper-exceptional-count` are banked as engines
   (`MassRedistributionCounting.goodDonors`, `card_exceptionalFinal`,
   `wrapperExceptionalCount_engine`) whose remaining inputs are the owner
   uniqueness `huniq` and the clean-count `hclean`.  *Next round:* discharge
   `huniq` at the canonical system from the banked
   `RoutedCertificateSystem.RoutedSystem.owner_injOn` (whose own input is
   `WrapperMassRedistribution.owner_injOn_of_unique_clean`), then compose
   Section 3 with `wrapperExceptionalCount_engine` to land
   `eq:wrapper-exceptional-count` at the canonical system.
4. **The canonical composition of Sections 2 and 3 is deliberately not stated.**
   Section 2 is general in `e_B` because the schedule bridge is arithmetic and
   holds for every count bound; instantiating it at Section 3's conclusion is one
   `le_trans` at the consumer, and stating that composition here would duplicate a
   sixty-binder bundle without adding a proof step.

## Axiom surface

The single import is `ProtectedEarlyClosure`, whose transitive closure reaches
`FrontierSumAssembly`, `MassRedistributionCounting`, `ClosureSelectSupply`,
`FrontierIndexing`, `DenseWrapperFrontier`, `WrapperProtectedEarly`,
`WrapperMassRedistribution`, `SplitFirstBobInstance`, `FirstBobFrontierInstance`
and `ParameterSchedule`.  `LegacyNPCC.Stage12` is **not** in that closure, so the
cited AGHP balanced-family axiom is unreachable from every declaration here.  No
`axiom`, no opaque certificate, no premise bundle, no new `structure`, `abbrev` or
`instance` is declared; the only `def`s are the four Section-5 probe data, all
labelled NON-FIDELITY.

## Canonical inhabitation

**REGISTERED and DEFERRED, inherited unchanged.**  This module declares no new
type, so it opens no new inhabitation obligation.  The inherited one cannot be
discharged as mathematics: the paper's own instance of every statement below is a
function of the **alleged** protocol of `09:1187--1193`, whose non-existence is
the conclusion of the whole subsection, so the frozen paper exhibits no routed
instance by construction.  Section 5's probe is explicitly **NON-FIDELITY** and is
not offered as a fidelity witness; it exists to show that Section 1's supply and
the Bob-heavy threshold are jointly satisfiable at a nondegenerate point
(`e_B >= 1`), at the schedule's **own** `eta_R` rather than at a value of ours.
-/

namespace EthInapproximability.ParameterizedNP.BobHeavyDonorCount

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.AliceOnlyHdensSupply
open EthInapproximability.ParameterizedNP.SelectEmbedComposition
open EthInapproximability.ParameterizedNP.FirstBobLightClosure
open EthInapproximability.ParameterizedNP.ClosureSelectSupply
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.ProtectedEarlyClosure

/-! ## §1  The per-donor mass of `09:1537` is nonnegative (`09:1370--1376`)

"Each outer coordinate contains two protected row reservoirs, each of mass
`mu_P = 1/184` relative to the `m` rows of one copy of `N`.  For a first-Bob node
`v` and a donor set `J_0 subseteq [q]`, let `P_v(J_0)` denote, normalized by `m`,
the protected mass from those donors reaching `v`."

The banked count engine carries `hnonneg : 0 <= sum_{v first-Bob} P_v({j})` as a
binder.  It is not an assumption of the frozen text: `09:1370--1376` says the mass
*is* `mu_P` times retained reservoir densities, and `09:1434--1436` names those
densities `d_j in [0,1]`.  So the sign is a theorem, and this section proves it at
the same `hres`/`hd_0`/`hd_1` interface the banked
`ProtectedEarlyClosure.canonical_wrapperTotalEarlyMass` already carries -- which
is why Section 3 can retire the binder without adding a single hypothesis to the
bundle. -/

section Nonnegativity

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V]

/-- **`09:1370--1376` and `09:1537`: the per-donor first-Bob mass is
nonnegative.**

`sum_{v first-Bob} P_v({j}) >= 0` for every donor `j` of `J_0`, from the frozen
reservoir readout `P_v({j}) = mu_P (d_0(donor j) + d_1(donor j))` and the frozen
range `d in [0,1]` of `09:1434--1436` (only its lower half is used, so the
statement demands strictly less than the paper supplies).

This is the `hnonneg` slot of the banked
`MassRedistributionCounting.wrapperBobHeavyCount_engine`, produced rather than
assumed.  `mu_P > 0` is the banked `WrapperProtectedEarly.muP_pos`, consumed by
pin; `mu_P = 1/184` is never re-fixed here.

General in the routed system, the donor index, the node type and the width. -/
theorem firstBobMass_nonneg_of_reservoirs {q : ℕ}
    (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ) (J₀ : Finset ι)
    (donor : ι → Fin q) (d₀ d₁ : V → Fin q → ℝ)
    (hres : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j)))
    (hd₀0 : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀.image donor, 0 ≤ d₀ v j)
    (hd₁0 : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j ∈ J₀.image donor, 0 ≤ d₁ v j) :
    ∀ j ∈ J₀, 0 ≤ firstBobMass S Pv j := by
  classical
  intro j hj
  have himg : donor j ∈ J₀.image donor := Finset.mem_image_of_mem donor hj
  rw [firstBobMass]
  refine Finset.sum_nonneg fun v hv => ?_
  have h0 := hd₀0 v hv _ himg
  have h1 := hd₁0 v hv _ himg
  have hmu := muP_pos
  rw [hres v hv j hj]
  nlinarith

end Nonnegativity

/-! ## §2  `e_B <= E_B`: the schedule bridge (`06:720--722`, `06:732--733`)

`eq:terminal-uniform-bounds` **defines**
`E_B = ceil(512 mu_P B_theta L_q s e_0^max/((1-vartheta) eta_R))`, and `06:732--733`
reads: "The counting in `sec:first-wrapper` then gives at most `E_B` Bob-heavy
clean sources."  That sentence is the composition of
`eq:wrapper-bob-heavy-count` with `09:453`'s deterministic bound
`e_0 <= e_0^max` and the frozen ceiling.

The consumer is `09:1719--1726` -- "The size of `J_good` is not a schedule input.
It is a derived fact: ... `|J_good| = c - e_B >= q - ceil(e_0^max/(1-vartheta)) -
E_B = q - E_T`" -- whose banked arithmetic
`WrapperMassRedistribution.goodDonorCount_ge` carries `e_B <= E_B` as its binder
`heB`, over the reals.  This section is that binder, at the integer counts the
frozen text uses; `Nat.cast_le` is the only step between the two, and it is left
to the consumer rather than pre-applied here. -/

section ScheduleBridge

/-- **`06:732--733` ("at most `E_B` Bob-heavy clean sources"), proved.**

From `eq:wrapper-bob-heavy-count`'s real bound at `e_0` and `09:453`'s
`e_0 <= e_0^max`, the integer count is at most the frozen ceiling
`ParameterSchedule.EB`.  Two frozen steps and no more: monotonicity of the
right-hand side in `e_0` (the coefficient `512 mu_P B_theta L_q s` is
nonnegative), and `Nat.le_ceil` at the preserved ceiling of `06:720--722`.

*The `vartheta` seam.*  The hypothesis carries the `09:1268` twin
(`DenseWrapperFrontier.vartheta`, the one `eq:wrapper-total-early-mass` and hence
`eq:wrapper-bob-heavy-count` inherit) while `ParameterSchedule.EB` carries the
`06:718` twin.  The banked `FrontierSumAssembly.vartheta_twins_agree` is consumed
**by pin** to cross the seam; neither name is re-declared and neither is assumed
to be the other.

*Why the trivial witness fails.*  The conclusion is an inequality between two
fixed naturals, not an existential; and `E_B` is not vacuously large, since
`Nat.le_ceil` is applied to the *same* expression the hypothesis bounds, with only
`e_0 -> e_0^max` moved.

`eta_R > 0` is the binder `eq:eta-choice` licenses (`06:228`,
`0 < eta_R <= eta_C/2`) and is load-bearing: see
`bobHeavyCount_needs_positive_etaR`.  General in every schedule quantity; no
value is assigned to any of them. -/
theorem bobHeavyCount_le_EB {Bt Lqv sv e0m eB : ℕ} {e0 etaR : ℝ}
    (hetaR : 0 < etaR) (he0 : e0 ≤ (e0m : ℝ))
    (hcount : (eB : ℝ)
      ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0 / ((1 - vartheta) * etaR)) :
    eB ≤ ParameterSchedule.EB Bt Lqv sv e0m etaR := by
  have hv : (1 : ℝ) - vartheta = 7 / 16 := one_sub_vartheta
  have hden : (0 : ℝ) < (1 - vartheta) * etaR := by rw [hv]; positivity
  have hcoef : (0 : ℝ) ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) := by
    have := muP_pos
    positivity
  have hnum : 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0
      ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * (e0m : ℝ) :=
    mul_le_mul_of_nonneg_left he0 hcoef
  rw [le_div_iff₀ hden] at hcount
  have hreal : (eB : ℝ)
      ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * (e0m : ℝ) / ((1 - vartheta) * etaR) := by
    rw [le_div_iff₀ hden]
    linarith
  have hceil : 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * (e0m : ℝ)
        / ((1 - vartheta) * etaR)
      ≤ ((ParameterSchedule.EB Bt Lqv sv e0m etaR : ℕ) : ℝ) := by
    rw [ParameterSchedule.EB, ← FrontierSumAssembly.vartheta_twins_agree]
    exact Nat.le_ceil _
  exact_mod_cast le_trans hreal hceil

end ScheduleBridge

/-! ## §3  `eq:wrapper-bob-heavy-count` at the canonical routed system
(`09:1535--1547`)

`e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)`.

The banked `MassRedistributionCounting.wrapperBobHeavyCount_engine` divides the
total by the threshold; both of its inputs are supplied here rather than assumed:

* `hnonneg` from Section 1, at the reservoir readout the bundle already carries;
* `htot` from `ProtectedEarlyClosure.canonical_wrapperTotalEarlyMass`, consumed in
  an actual proof term at the frozen donor set `J_0 = J_clean` of `09:1521` --
  which is the banked `RoutedSystem.cleanFinal`, `09:1519--1520`'s "the `c` outer
  coordinates whose clean reference certificates reach final Alice nodes", and is
  exactly the index set `09:1535`'s "clean donor" ranges over.

The strict-to-non-strict step is the frozen one: `09:1529` is strict and
`09:1543` is not, and the banked engine's `htot` slot is stated with `<=`, so
`le_of_lt` is applied once, in the direction the paper prints. -/

section FrozenDisplay

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-bob-heavy-count` (`09:1542--1547`) at the canonical system.**

"Call a clean donor `j` *Bob-heavy* if `sum_{v: first-Bob frontier node} P_v({j})
> eta_R/4` ...  Their number `e_B` satisfies
`e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)`."

*What is derived rather than assumed.*  Both slots of the banked
`MassRedistributionCounting.wrapperBobHeavyCount_engine`:

* `hnonneg` is Section 1 fired at the bundle's own `hres`, `hd_0` and `hd_1`;
* `htot` is `ProtectedEarlyClosure.canonical_wrapperTotalEarlyMass` fired at
  `J_0 = J_clean`, i.e. `eq:wrapper-total-early-mass` at the canonical system.

The counting itself -- the division of the total by the threshold `eta_R/4` and
the frozen factor four that turns `128` into `512` -- is the banked
`WrapperMassRedistribution.wrapperBobHeavyCount` reached through the engine, and
is restated nowhere.

*What is still a binder.*  `hLocExCC` and `hLocExEP` (the two call sites of
`thm:certified-localized-extension`, `A:109--146`, the entry point of
**EXPANDER-001**), `hfinal`, `halleged`, `hcost`, `hres`, and the analytic members
of the protected-closure bundle, all inherited **verbatim** from the banked
canonical endpoint -- no hypothesis is added to it and none is weakened.  `hne` is
the banked engine's own nonemptiness binder.  `hetaR` is new and is the only
addition: `eq:eta-choice` (`06:204--219`) with `06:228` licenses it, and the
frozen counting step needs nothing else about `eta_R`.
**Full-bundle satisfiability is not claimed.**

*Why the trivial witness fails.*  The conclusion is an inequality between two
fixed reals, not an existential.  It is not vacuous either: the right-hand side is
the frozen expression whose ceiling **defines** `E_B` at `e_0^max`
(`06:720--722`), so a bound that degraded to nothing would make the schedule's own
`E_B` meaningless; and the left-hand side is a genuine cardinality, positive at a
nondegenerate point by Section 5.

*No route completion.*  `eq:wrapper-u-dense` (`09:262--263`) is neither stated nor
implied; `09:1548--1781` remains open. -/
theorem canonical_wrapperBobHeavyCount {RwN : Type*} [Fintype RwN]
    {r bT kref tcert : ℕ} {E0 : Finset (Fin q)} {xU θ etaR : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
    -- the protected-closure data, per first-Bob node
    {k₂ b₁ r₂ r₃ bcap tcertEP selCard rowsPerBlock : ℕ} {lamT epsProd : ℝ}
    (isRestrEP : Protocol X (Fin q → Yc) Bool → ℕ → ℕ → ℝ → Prop)
    (Scol : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Finset (Fin q → Yc))
    (YT : Finset Yc)
    (Pv : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    (donor : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Fin q)
    (d₀ d₁ : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Fin q → ℝ)
    (ell : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℕ)
    (bsel : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → Bool)
    (hdepth : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ((canonicalSystem hcomp hR).node v).length + ell v = r)
    -- `09:1521`: the donor set is `J_clean`, the banked `cleanFinal`
    (hinj : ∀ i ∈ (canonicalSystem hcomp hR).cleanFinal,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal, donor i = donor j → i = j)
    (hres : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j)))
    -- the alleged protocol (`09:1187--1193`) at the frozen `C` (`09:855`, `09:1038`)
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    -- the clean-count bundle, verbatim
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1
      ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1cc : (3 / 5 : ℝ) ^ (2 ^ kref)
      ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + r)))
    (hE2cc : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + kref)))
    (hLocExCC :
      ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (Sblk : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ Sblk T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1
        ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref)
        ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((TerminalTwoStream.terminalTarget bcap r₂ r₃ : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (TerminalTwoStream.terminalTarget bcap r₂ r₃ - 1) + (r - v.val.length)
        ≤ (descend P (v.val ++ [c])).cost)
    {Scover : Finset (Fin q → Yc)}
    (hcover : ∀ l ∈ Finset.Ico 1 kref, ∀ K : Finset (Fin q),
      K.card = smallCopyWidth (2 ^ l) → PoorProjection rhoSmall K Scover →
      (E0 ∩ K).Nonempty)
    (B : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → Finset X)
    (hB : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ⌈(Fintype.card X : ℝ)
          * (((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
            * xTdepth bT)⌉₊
        ≤ (B v j).card)
    (plc : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      StartedCoord E0 → X → X)
    (hblock : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ j ∈ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v,
      ∀ a ∈ B v j, plc v j a ∈ rowsAt P (R j) v.val)
    (hplace : ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      ∀ (j : StartedCoord E0) (a : X), ∀ c ∈ Scover,
      g (plc v j a) c = interlaceFun Nmat q (startedIdx j, ιR a) c)
    (hfinal : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.finalNodes,
      frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
        ≤ finalWeight (certOpt v))
    -- the protected-closure bundle (`lem:early-protected-closure`), per node
    (hqpos : 0 < q)
    (hk₂ : 4 ≤ k₂)
    (hk₂le : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      k₂ ≤ r₃ + ell v + r₂)
    (hbcap : 2 ≤ bcap)
    (hd₀0 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, 0 ≤ d₀ v j)
    (hd₀1 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, d₀ v j ≤ 1)
    (hd₁0 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, 0 ≤ d₁ v j)
    (hd₁1 : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ ((canonicalSystem hcomp hR).cleanFinal).image donor, d₁ v j ≤ 1)
    (hGateEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ((2 : ℝ) ^ (r₃ + ell v + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hYT0 : 0 < YT.card)
    (hSep : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      θ * (Fintype.card Yc : ℝ) ^ q ≤ ((Scol v).card : ℝ))
    (hYT : lamT * (Fintype.card Yc : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (u : ℕ) (J : Finset (Fin q)), J.card = u →
        ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Yc)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ (Scol v))
    (hBlocks : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < xTdepth bT) (hx1 : xTdepth bT ≤ 1)
    (htx : ((2 : ℝ) ^ k₂) * xTdepth bT ≤ 1)
    (hMne : 1 ≤ Fintype.card RwN)
    (hbaseEP : bcap ≤ NPCC.LambdaGE Nmat 1 (xTdepth bT) (3 / 5))
    (htcertEP : tcertEP ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1ep : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e Rex : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        Rex + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((Rex : ℝ) + k₂)))) / (1 + epsProd))
    (hE2ep : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ⌈((2 : ℝ) ^ (r₃ + ell v + r₂ - k₂)) * 2 ^ k₂ * xTdepth bT
          * (Fintype.card RwN)⌉₊ ≤ rowsPerBlock)
    -- `09:1499--1504`, the round-`r4` selection binder at every first-Bob node
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- The extraction re-gate is forwarded verbatim from the banked
    -- `WrapperProtectedEarly.earlyProtectedClosure`: the `09:1499` selection fires
    -- only on `ExtractionOutput`, the deliverable of `09:1458--1471`, so the
    -- density chain stays load-bearing through this application too.
    (hSelectEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      earlyMassCoeff θ q (2 ^ r₃)
          * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)
          ≤ donorMass Pv ((canonicalSystem hcomp hR).cleanFinal) v →
        ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ (ell v) θ e dcls →
          ExtractionOutput (Scol v) YT e →
          isRestrEP (descendStep (descend P ((canonicalSystem hcomp hR).node v)) (bsel v))
            ((2 : ℕ) ^ (r₃ + ell v + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
              (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocExEP : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ (e Rex Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ)
        (w : Protocol X (Fin q → Yc) Bool),
        ExtensionCallThree k₂ Rex Rloc b₁ e r₂ r₃ (ell v) dcls colDens →
        1 ≤ Fintype.card RwN → 2 ≤ bcap →
        0 < xTdepth bT → xTdepth bT ≤ 1 →
        bcap ≤ NPCC.LambdaGE Nmat 1 (xTdepth bT) (3 / 5) →
        tcertEP ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * xTdepth bT ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ Rex →
        (2 : ℕ) ^ Rex * 2 ^ k₂ = 2 ^ (Rex + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((Rex : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        isRestrEP w blocks rowsEach colDens →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * xTdepth bT * (Fintype.card RwN)⌉₊ ≤ rowsEach →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ w.cost)
    (hne : ((canonicalSystem hcomp hR).toWrapperFrontier.bobNodes).Nonempty)
    -- `eq:eta-choice` (`06:204--219`) with `06:228`: the tolerance is positive
    (hetaR : 0 < etaR) :
    ((bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ≤ 512 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) * (E0.card : ℝ)
          / ((1 - vartheta) * etaR) := by
  refine MassRedistributionCounting.wrapperBobHeavyCount_engine (canonicalSystem hcomp hR)
    Pv hetaR
    (firstBobMass_nonneg_of_reservoirs (canonicalSystem hcomp hR) Pv
      ((canonicalSystem hcomp hR).cleanFinal) donor d₀ d₁ hres hd₀0 hd₁0) ?_
  exact le_of_lt (canonical_wrapperTotalEarlyMass Nmat Gmat ιR hsub halleged hcomp hR certOpt
    isRestrEP Scol YT Pv ((canonicalSystem hcomp hR).cleanFinal) donor d₀ d₁ ell bsel hdepth
    hinj hres
    hC hcost hq hmem hk hq4 hX hYc hθ0 hθ1 hgate hbase htcert hE1cc hE2cc hLocExCC hcover
    B hB plc hblock hplace hfinal hqpos hk₂ hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0
    hSep hYT hgap hQuery hBlocks hx0 hx1 htx hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep
    hrows hSelectEP hLocExEP hne)

end FrozenDisplay

/-! ## §4  Aux-lemma battery

Five general checks on the count.  **Canonical inhabitation is INHERITED,
REGISTERED and DEFERRED** per the header: this module declares no new type, so it
opens no new obligation, and the inherited one cannot be discharged because the
paper's own instance of every statement above is a function of the alleged
protocol of `09:1187--1193`, which does not exist.  Nothing in this section
evaluates a schedule parameter or carries a numeral of its own. -/

section Battery

/-- **Battery 1 (the count reads the first-Bob column, and only it).**

`09:1537` sums `P_v({j})` over **first-Bob** frontier nodes.  This is the
count-side face of the **two-kappa trap** (banked as
`FrontierSumAssembly.two_kappa_trap_at_the_final_nodes`, cited and not restated):
the final Alice nodes have `kappa_v = 1` and carry the clean certificates
themselves, and importing their column into the sum would both contradict the
frozen weight classification and add mass that `eq:wrapper-total-early-mass` --
itself a `bobNodes` sum -- does not bound.

The check: the per-donor mass depends on the mass family only through its values
on `bobNodes`.  General in the routed system and both index types. -/
theorem firstBobMass_congr_on_bobNodes {X Y Z : Type*} {Coord ι V : Type*}
    {P : Protocol X Y Z} {r A0 : ℕ} [Fintype V]
    (S : RoutedSystem P Coord ι V r A0) (Pv Qv : V → ι → ℝ) (j : ι)
    (h : ∀ v ∈ S.toWrapperFrontier.bobNodes, Pv v j = Qv v j) :
    firstBobMass S Pv j = firstBobMass S Qv j := by
  rw [firstBobMass, firstBobMass]
  exact Finset.sum_congr rfl h

/-- **Battery 2 (the Bob-heavy set reads the first-Bob column, and only it).**

The same locality one level up: two mass families agreeing on the first-Bob
column determine the *same* set of Bob-heavy clean donors, hence the same `e_B`.
General in the routed system and both index types. -/
theorem bobHeavyDonors_congr_on_bobNodes {X Y Z : Type*} {Coord ι V : Type*}
    {P : Protocol X Y Z} {r A0 : ℕ} [Fintype V] [Fintype ι]
    (S : RoutedSystem P Coord ι V r A0) (Pv Qv : V → ι → ℝ) (etaR : ℝ)
    (h : ∀ v ∈ S.toWrapperFrontier.bobNodes, ∀ j, Pv v j = Qv v j) :
    bobHeavyDonors S Pv etaR = bobHeavyDonors S Qv etaR := by
  classical
  ext j
  rw [mem_bobHeavyDonors, mem_bobHeavyDonors,
    firstBobMass_congr_on_bobNodes S Pv Qv j fun v hv => h v hv j]

/-- **Battery 3 (the bound is monotone in `e_0`).**

`e_0` enters `eq:wrapper-bob-heavy-count` only through the numerator, with a
nonnegative coefficient, so a larger `e_0` gives a weaker bound.  This is the
direction Section 2 needs to replace `e_0` by `09:453`'s `e_0^max`, and it is the
reason that replacement is a legal weakening rather than a change of statement.
General; `mu_P > 0` is the banked `muP_pos`. -/
theorem bobHeavyBound_mono_in_e0 {Bt Lqv sv : ℕ} {e0 e0' etaR : ℝ}
    (hetaR : 0 < etaR) (h : e0 ≤ e0') :
    512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0 / ((1 - vartheta) * etaR)
      ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0' / ((1 - vartheta) * etaR) := by
  have hv : (1 : ℝ) - vartheta = 7 / 16 := one_sub_vartheta
  have hden : (0 : ℝ) < (1 - vartheta) * etaR := by rw [hv]; positivity
  have hcoef : (0 : ℝ) ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) := by
    have := muP_pos
    positivity
  rw [div_le_div_iff_of_pos_right hden]
  exact mul_le_mul_of_nonneg_left h hcoef

/-- **Battery 4 (the bound is antitone in the tolerance `eta_R`).**

Raising the Bob-heavy threshold can only shrink the set of Bob-heavy donors -- the
banked `MassRedistributionCounting.bobHeavyDonors_antitone`, cited and not
restated -- and it lowers the frozen bound as well.  The two directions agree, so
the display does not degrade in the direction the set improves.  General. -/
theorem bobHeavyBound_antitone_in_etaR {Bt Lqv sv : ℕ} {e0 etaR etaR' : ℝ}
    (he0 : 0 ≤ e0) (hetaR : 0 < etaR) (hle : etaR ≤ etaR') :
    512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0 / ((1 - vartheta) * etaR')
      ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0 / ((1 - vartheta) * etaR) := by
  have hv : (1 : ℝ) - vartheta = 7 / 16 := one_sub_vartheta
  have hden : (0 : ℝ) < (1 - vartheta) * etaR := by rw [hv]; positivity
  have hden' : (0 : ℝ) < (1 - vartheta) * etaR' := by
    rw [hv]
    have : (0 : ℝ) < etaR' := lt_of_lt_of_le hetaR hle
    positivity
  have hnum : (0 : ℝ) ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0 := by
    have := muP_pos
    positivity
  rw [le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hden', hv]
  nlinarith

/-- **Battery 5 (the bound is not secretly negative).**

A green build cannot see whether a conclusion is satisfiable only because its
hypothesis bundle is contradictory.  Here is the check for Section 3: at every
legal input the frozen right-hand side is **nonnegative**, so
`e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)` is a constraint a genuine
cardinality can satisfy, not a disguised `card < 0` that only an inconsistent
bundle could prove.  Together with `probe_reservoir_count_pos` (`e_B >= 1` at a
nondegenerate point) this pins the display between two live values.
General; `mu_P > 0` is the banked `muP_pos` and `B_theta`, `L_q` are naturals. -/
theorem bobHeavyBound_nonneg {θ : ℝ} {qw sv : ℕ} {e0 etaR : ℝ}
    (he0 : 0 ≤ e0) (hetaR : 0 < etaR) :
    0 ≤ 512 * muP * (Btheta θ : ℝ) * (Lq qw : ℝ) * (sv : ℝ) * e0
        / ((1 - vartheta) * etaR) := by
  have hv : (1 : ℝ) - vartheta = 7 / 16 := one_sub_vartheta
  have hmu := muP_pos
  rw [hv]
  positivity

end Battery

/-! ## §5  Statement pole and the nondegenerate probe

The pole is a genuine one: it exhibits an input at which the conclusion of Section
3 is **false**, so `hetaR` is load-bearing rather than decorative.  The probe that
follows is **NON-FIDELITY** and claims no legality for the routed system it uses;
what it does claim is that Section 1's supply and the frozen Bob-heavy threshold
are jointly satisfiable at a nondegenerate point, at the schedule's **own**
`eta_R`. -/

section Probe

/-- The outer coordinate of a live certificate: `09:1519`'s reading of a clean
donor as an outer coordinate, at the audit instance's three started coordinates.
**NON-FIDELITY** -- part of the probe data, not of the construction. -/
def probeReservoirDonor : CertIndex liveProtocol liveRows 1 2 → Fin 3 := fun x => x.1

/-- The first retained reservoir density of the probe: full on the coordinate-`0`
donor, empty elsewhere.  Legal as a *density* (`09:1434--1436` requires
`d in [0,1]`), and **NON-FIDELITY** as a model of the routing's output. -/
def probeReservoirD0 : FrontierNode liveProtocol liveRows 1 2 → Fin 3 → ℝ :=
  fun _ j => if j = 0 then 1 else 0

/-- The second retained reservoir density of the probe: empty.  **NON-FIDELITY**;
the frozen halving of `09:1433--1439` is not modelled, only its range. -/
def probeReservoirD1 : FrontierNode liveProtocol liveRows 1 2 → Fin 3 → ℝ :=
  fun _ _ => 0

/-- `P_v` in the frozen reservoir shape of `09:1370--1376`:
`P_v({j}) = mu_P (d_0(donor j) + d_1(donor j))`.

Unlike the banked `MassRedistributionCounting.probeMass`, this one is built
*through* the reservoir readout, so it exercises Section 1 rather than bypassing
it.  **NON-FIDELITY:** the paper's own `P_v` is the routing's output on the
protected reservoirs of the alleged protocol, which does not exist. -/
noncomputable def probeReservoirMass :
    FrontierNode liveProtocol liveRows 1 2 → CertIndex liveProtocol liveRows 1 2 → ℝ :=
  fun v x => muP * (probeReservoirD0 v (probeReservoirDonor x)
    + probeReservoirD1 v (probeReservoirDonor x))

/-- `09:1537` evaluated at the probe: the coordinate-`0` donor sends exactly one
reservoir's worth of mass, `mu_P`, to the single first-Bob node of the audit
instance (`FirstBobFrontierInstance.live_bobNodes`). -/
theorem probe_reservoir_firstBobMass :
    firstBobMass liveSystem probeReservoirMass probeDonorZero = muP := by
  rw [firstBobMass, live_bobNodes]
  simp [probeReservoirMass, probeReservoirD0, probeReservoirD1, probeReservoirDonor,
    probeDonorZero]

/-- **Section 1 exercised, not bypassed.**  The probe's mass satisfies the frozen
reservoir readout with densities in range, so the derived nonnegativity fires and
the banked engine's `hnonneg` slot is filled by a theorem at this instance too. -/
theorem probe_reservoir_nonneg :
    ∀ j ∈ liveSystem.cleanFinal, 0 ≤ firstBobMass liveSystem probeReservoirMass j := by
  refine firstBobMass_nonneg_of_reservoirs liveSystem probeReservoirMass
    liveSystem.cleanFinal probeReservoirDonor probeReservoirD0 probeReservoirD1
    (fun _ _ _ _ => rfl) ?_ ?_
  · intro v _ j _
    simp only [probeReservoirD0]
    split <;> norm_num
  · intro v _ j _
    simp [probeReservoirD1]

/-- **`e_B >= 1` at the schedule's own tolerance -- NON-FIDELITY, and no legality
is claimed for the routed system.**

The coordinate-`0` donor is Bob-heavy at `eta_R = ParameterSchedule.etaR s dv
zeta`, i.e. at `eq:eta-choice` (`06:204--219`) **evaluated**, not at a value of
ours: the schedule's own derived ceiling `eta_R <= 1/36800`
(`ParameterSchedule.etaR_le_bound`, consumed by pin) puts the frozen threshold
`eta_R/4` below `mu_P = 1/184`, so a donor carrying one whole reservoir clears it.
No side condition on `s`, `delta_v(G)` or `zeta` is needed, so the statement holds
at **every** schedule input.

What this establishes is that Section 3's conclusion is not satisfied vacuously by
an empty Bob-heavy set: at a nondegenerate point the count is at least one, and
the bound is a real constraint. -/
theorem probe_reservoir_bobHeavy {sS : ℕ} {dv zeta : ℝ} :
    probeDonorZero ∈ bobHeavyDonors liveSystem probeReservoirMass
      (ParameterSchedule.etaR sS dv zeta) := by
  rw [mem_bobHeavyDonors]
  refine ⟨probe_mem_cleanFinal_zero, ?_⟩
  rw [BobHeavy, probe_reservoir_firstBobMass]
  have h := ParameterSchedule.etaR_le_bound sS dv zeta
  have hmu : muP = 1 / 184 := rfl
  rw [hmu]
  linarith

/-- The nondegenerate count: `e_B >= 1` at the probe, for every schedule input. -/
theorem probe_reservoir_count_pos {sS : ℕ} {dv zeta : ℝ} :
    1 ≤ (bobHeavyDonors liveSystem probeReservoirMass
      (ParameterSchedule.etaR sS dv zeta)).card :=
  Finset.card_pos.mpr ⟨probeDonorZero, probe_reservoir_bobHeavy⟩

/-- **Statement pole: `hetaR` is load-bearing.**

At the illegal `eta_R = 0` -- excluded by `06:228`'s `0 < eta_R` -- the frozen
right-hand side collapses to `0` (division by zero), while the Bob-heavy set is
still inhabited, since every donor of positive mass clears the threshold `0/4`.
So the **display shape** of Section 3 is false at `eta_R = 0`, exhibited here at
the NON-FIDELITY audit instance `liveSystem` -- not at the canonical system,
which is not inhabited.  The guard is therefore load-bearing and the binder is
not decoration.

`eta_R = 0` is **ours** and is exhibited only to make a guard fire: this is a
non-legality-claiming rejection probe, not a witness.  The statement is general in
`theta`, `q`, `s` and `e_0`, so no schedule quantity is instantiated. -/
theorem bobHeavyCount_needs_positive_etaR (θ : ℝ) (qw sv : ℕ) (e0 : ℝ) :
    ¬ (((bobHeavyDonors liveSystem probeReservoirMass 0).card : ℝ)
        ≤ 512 * muP * (Btheta θ : ℝ) * (Lq qw : ℝ) * (sv : ℝ) * e0
            / ((1 - vartheta) * 0)) := by
  intro hcon
  rw [mul_zero, div_zero] at hcon
  have hmem : probeDonorZero ∈ bobHeavyDonors liveSystem probeReservoirMass 0 := by
    rw [mem_bobHeavyDonors]
    refine ⟨probe_mem_cleanFinal_zero, ?_⟩
    rw [BobHeavy, probe_reservoir_firstBobMass]
    have : muP = 1 / 184 := rfl
    rw [this]
    norm_num
  have hpos : 1 ≤ (bobHeavyDonors liveSystem probeReservoirMass 0).card :=
    Finset.card_pos.mpr ⟨probeDonorZero, hmem⟩
  have hposR : (1 : ℝ) ≤ ((bobHeavyDonors liveSystem probeReservoirMass 0).card : ℝ) := by
    exact_mod_cast hpos
  linarith

end Probe

end EthInapproximability.ParameterizedNP.BobHeavyDonorCount
