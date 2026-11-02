import EthInapproximability.ParameterizedNP.BobHeavyDonorCount

/-!
# Parameterized NP route: the exceptional final-node count `e_T`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines `09:1550--1564`**,
  inside `sec:wrapper-mass-redistribution`.  Opened first-hand this tranche, in
  print order:
  * **`09:1550--1552`**, "Every clean reference certificate has a unique final
    node, its *owner*.  Distinct clean donors have distinct owners because a final
    node contains at most one clean certificate";
  * **`09:1552`**, "Let `n_T` be the total number of final nodes";
  * **`09:1553--1554`**, "All final nodes not owned by `J_good` are called
    exceptional; their number is";
  * **`eq:wrapper-exceptional-count`** (display `09:1555--1563`, label `09:1562`):
    `e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`;
  * **`09:1564`**, "Here we used `K_B + n_T <= q` and `eq:wrapper-clean-count`".
* **Second frozen anchor of this tranche (the MANDATED closure):**
  **`09:1718--1726`**, "The size of `J_good` is not a schedule input.  It is a
  derived fact: by `eq:wrapper-clean-count`, `eq:wrapper-bob-heavy-count`,
  `eq:cover-bounds`, and `eq:terminal-uniform-bounds`,
  `|J_good| = c - e_B >= q - ceil(e_0^max/(1-vartheta)) - E_B = q - E_T`."
* **Cross-anchors opened first-hand this tranche:**
  * **`lem:final-reference-uniqueness`** (`09:1315--1319`) with its proof
    `09:1321--1344`: two certificates at one final node descend from distinct
    outer coordinates, the pair avoids the `u_2 = 2` small-copy cover, no Bob
    query has occurred on the route, `lem:certified-row-ladder` is invoked at
    `M = G`, `H = C-1`, `x = x_T`, `z = y`, `ell = 1`, the resulting two-copy
    restriction has complexity at least `C`, "But the suffix below a node reached
    after `r` Alice bits in the alleged `(C+r-1)`-bit protocol has depth at most
    `C-1`, a contradiction";
  * **`09:1346--1350`**, "Thus every final Alice node contains either one clean
    certificate, one half-weight descendant of a split certificate, or none.  Let
    `K_B` be the sum of `kappa_v` over first-Bob nodes, let `c` be the number of
    final nodes with one clean certificate, and let `ell` be the number with one
    split certificate";
  * **`eq:wrapper-clean-count`** (display `09:1352--1357`, label `09:1356`),
    `c >= q - e_0/(1-vartheta)` and `K_B + ell <= e_0/(1-vartheta)`, with its
    frozen derivation `09:1358--1365`;
  * **`09:1519--1520`**, "Let `J_clean` be the `c` outer coordinates whose clean
    reference certificates reach final Alice nodes" -- the sentence that reads the
    node count `c` of `09:1348--1349` as a *donor* count;
  * `09:1548`, "Let `J_good` be the other clean donors";
  * **`eq:terminal-uniform-bounds`** (display `06:716--731`, label `06:730`),
    whose `06:723` line **defines**
    `E_T = ceil(e_0^max/(1-vartheta)) + E_B` and whose `06:720--722` line defines
    `E_B`;
  * `09:450` (`e_0 = |E_0|`) with **`09:452--453`**, "The construction records an
    explicit deterministic upper bound `e_0 <= e_0^max`";
  * `09:1268` (`vartheta = 9/16`) and `06:718` (`vartheta = 9/16` again) -- the
    **`vartheta` twins**, crossed through the two banked `one_sub_vartheta`
    evaluations, with `FrontierSumAssembly.vartheta_twins_agree` reached
    transitively through `BobHeavyDonorCount.bobHeavyCount_le_EB`;
  * `09:1250--1259` (`kappa_v = 2^{r-d_v}`, `kappa_v >= 2` at a first-Bob node,
    `kappa_v = 1` at a final Alice node) -- the **two-kappa trap**.
* **Reader counterpart: NONE is claimable, inherited unchanged.**
  `routes/parameterized-np/reader-facing/sections/A-stage4-details.tex:370--399`
  was opened first-hand this tranche and remains the only reader passage covering
  this material.  It is running prose ("The complete owner--donor count is finite:
  it uses only the fixed reservoir masses above ...  It is expanded line by line
  in the ultra-explicit companion", `396--399`), and its single displayed endpoint
  (`A-stage4-details.tex:393--395`) is `eq:wrapper-u-dense`, which this module does
  **not** state.  The reader artifact was searched this tranche for `exceptional`,
  `owner`, `good donor` and `J_good`: the only hits are `376`, `386`, `396` and
  `410`, all unnumbered proof prose, and there is **no** occurrence of
  "exceptional" or "`J_good`" at all.  The READER-COUNTERPART rule forbids citing
  prose and forbids reusing an item already assigned to another declaration, so
  none is cited rather than one invented.  This re-confirms the inherited
  `BOB-HEAVY-DONOR-COUNT-001`, `PROTECTED-EARLY-CLOSURE-001` and
  `FRONTIER-SUM-ASSEMBLY-001` outcomes and re-decides nothing.

## Census first: what was already banked, and what this tranche adds

The declared range `09:1550--1564` and the closure anchor `09:1718--1726` were
censused line by line against the banked tree before a single line was written.
Everything in the following list is consumed **by pin** and **nothing of it is
restated**:

* `09:1550`, the owner map.  **BANKED** as
  `RoutedCertificateSystem.RoutedSystem.owner`, with `owner_isFinal` and
  `cert_route_eq_owner`.
* `09:1551--1552`, owner injectivity from final-node uniqueness.  **BANKED** as
  `WrapperMassRedistribution.owner_injOn_of_unique_clean` and, on the protocol
  object, `RoutedCertificateSystem.RoutedSystem.owner_injOn`.
* `09:1321--1344`, the ladder route to that uniqueness.  **BANKED** as
  `RoutedCertificateSystem.RoutedSystem.owner_injOn_of_ladder`, whose `hbudget`
  step is the derived `final_residual_budget` and whose contradiction is the
  banked `finalNode_budget_contradiction`.
* `09:1553`, the exceptional set.  **BANKED** as
  `MassRedistributionCounting.exceptionalFinal`, with
  `goodDonors_image_owner_subset`.
* `09:1557--1558`, `e_T = n_T - |J_good|`.  **BANKED** as
  `MassRedistributionCounting.card_exceptionalFinal`.
* `09:1548`, `|J_good| = c - e_B`.  **BANKED** as
  `MassRedistributionCounting.card_goodDonors_add_card_bobHeavy`.
* `09:1564`, `K_B + n_T <= q`.  **BANKED** as
  `MassRedistributionCounting.bobCapacity_add_card_finalNodes_le`.
* `eq:wrapper-exceptional-count` as *arithmetic*.  **BANKED** as
  `WrapperMassRedistribution.wrapperExceptionalCount`.
* `eq:wrapper-exceptional-count` as an *engine*.  **BANKED** as
  `MassRedistributionCounting.wrapperExceptionalCount_engine`, with **both** of
  its remaining inputs -- the owner uniqueness `huniq` and the clean-count
  `hclean` read at `J_clean` -- carried as binders.
* `eq:wrapper-clean-count` at the canonical system with `hlight` retired.
  **BANKED** as `FrontierSumAssembly.canonical_cleanCount_of_reference_construction`.
* `eq:wrapper-bob-heavy-count` at the canonical system.  **BANKED** as
  `BobHeavyDonorCount.canonical_wrapperBobHeavyCount`.
* `e_B <= E_B` (`06:732--733`).  **BANKED** as
  `BobHeavyDonorCount.bobHeavyCount_le_EB`.
* `09:1718--1726`'s arithmetic.  **BANKED** as
  `WrapperMassRedistribution.goodDonorCount_ge`, carrying `e_B <= E_B` as its
  binder `heB`, over the reals.
* `E_T`, ceiling preserved.  **BANKED** as `ParameterSchedule.ET`.

**The gap this tranche closes is exactly the two binders of the banked
exceptional-count engine, plus the twice-deferred `heB` composition.**
Concretely:

1. `huniq` is **obtained** rather than assumed, through the banked owner chain:
   `owner_injOn_of_ladder` (the frozen `09:1321--1344` argument, whose ladder call
   `lem:certified-row-ladder` stays the named binder it is) gives injectivity on
   `J_clean`, and Section 1's general converse turns injectivity into the fibre
   form the engine wants.  Section 1 also records that the two forms are
   *equivalent*, the reverse direction being the banked
   `owner_injOn_of_unique_clean`, so nothing is lost in the translation.
2. `hclean` at `J_clean` is **obtained** from the banked clean count: Section 2's
   bridge turns the node count `c = |cleanNodes|` of `09:1348--1349` into the
   donor count `|J_clean|` of `09:1519--1520` through the owner map, and
   `FrontierSumAssembly.canonical_cleanCount_of_reference_construction` supplies
   the count itself at the canonical system.  This retires GAP-EXPOSED item 2 of
   `MassRedistributionCounting`'s header **in the `<=` direction the consumer
   needs**, at the price of the single structural binder `hhost` below.
3. `09:1718--1726` is **composed**: `bobHeavyCount_le_EB` and `goodDonorCount_ge`
   meet at one `le_trans` and one `Nat.cast_le` (Section 4), and the composition
   is then fired at the canonical routed system (Section 5), where `hcount` is
   discharged by `canonical_wrapperBobHeavyCount` and `hclean` by Section 2.
   This is the closure twice deferred by `FRONTIER-SUM-ASSEMBLY-001` and
   `BOB-HEAVY-DONOR-COUNT-001`; it is **not** deferred again.

Both retirements happen at the site that consumes them, which is the only place a
binder can be retired.

## What is asserted, and what is not

`eq:wrapper-exceptional-count` **is** asserted at the canonical routed system, in
its frozen shape (both clauses, both non-strict) and at the frozen right-hand
sides `q - c + e_B` and `e_0/(1-vartheta) + e_B`.  `09:1718--1726`'s
`|J_good| >= q - E_T` **is** asserted at the canonical routed system, with `E_T`
the banked `ParameterSchedule.ET` and its ceiling preserved.

Every schedule quantity is pedigreed and no numeral is assigned to any of them:

| symbol | status | frozen defining display | Lean pedigree |
| --- | --- | --- | --- |
| `vartheta` | DEFINED `= 9/16` | `09:1268` (and `06:718`) | `DenseWrapperFrontier.vartheta` |
| `e_0` | DEFINED `= |E_0|` | `09:450` | `(E0.card : R)`, evaluated |
| `e_0^max` | DEFINED (cover search) | `06:639--653`, at `09:452--453` | `ParameterSchedule` arg |
| `mu_P` | DEFINED `= 1/184` | `09:1370--1373` | `WrapperProtectedEarly.muP` |
| `B_theta` | DEFINED (cover) | `09:1378--1384`, `06:718` | `WrapperProtectedEarly.Btheta` |
| `L_q` | DEFINED `= ceil(log_2 2q)+1` | `09:1380--1382`, `06:719` | `WrapperProtectedEarly.Lq` |
| `s` | DEFINED `= 2^{h_s}` | `06:1864--1894` | carried as the dyadic `2^{r_3}` |
| `E_B` | DEFINED (ceiling) | `06:720--722` | `ParameterSchedule.EB` |
| `E_T` | DEFINED (ceiling) | `06:723` | `ParameterSchedule.ET` |
| `q` | DEFINED `= 2^r` | `09:105` | binder `hq`, as the banked spine takes it |

The only free real of the spine is `eta_R`, and it is never given a value: the
frozen counting steps need `eta_R > 0` and nothing more, so `hetaR` is an explicit
binder.  Section 6's probes do not pick an `eta_R` either.

**No route completion is claimed.**  `eq:wrapper-u-dense` (`09:262--263`,
`09:1780--1781`) is neither stated nor implied.  `09:1566--1718` -- the
four-category loss table, `eq:wrapper-mass-leaves-owner`, the owner-to-owner
transfer bound, `eq:wrapper-good-to-good`, the terminal pigeonhole and
`eq:wrapper-terminal-density` -- and `09:1727--1781` remain **OPEN**, and nothing
below touches them.

### The `vartheta` seam

`vartheta = 9/16` is declared twice in this development, from two different frozen
displays: `DenseWrapperFrontier.vartheta` (`09:1268`, the frontier weight
threshold, which is the one `eq:wrapper-clean-count` and
`eq:wrapper-exceptional-count` use) and `ParameterSchedule.vartheta`
(`eq:terminal-uniform-bounds`, `06:718`, the schedule constant inside `E_B` and
`E_T`).  Section 4 is the only seam where the two meet, and it crosses it through
the two banked evaluations `one_sub_vartheta` and
`ParameterSchedule.one_sub_vartheta` (each twin equals `9/16` by its own banked
lemma, so `1 - vartheta = 7/16` on both sides and nothing is assumed).  The banked
`FrontierSumAssembly.vartheta_twins_agree` is reached **only transitively**, through
`BobHeavyDonorCount.bobHeavyCount_le_EB` for `E_B`; no proof term here names it.
Nothing below declares a `vartheta`.

### The two-kappa trap

`kappa_v` takes exactly two kinds of value on the frozen frontier: `kappa_v >= 2`
at a first-Bob node (`09:1259`) and `kappa_v = 1` at a final Alice node
(`09:1250--1252`), and the banked
`FrontierSumAssembly.two_kappa_trap_at_the_final_nodes` is the check that
conflating them makes the weight bound contradict the frozen final-node
classification.  The trap reaches this module through the *carrier of the count*:
`e_T` and `n_T` are counts of **final** nodes and `J_clean`, `J_good` are sets of
donors whose certificates stop at final nodes, so every set below is cut out of
`finalNodes` or of `cleanFinal` and never out of the whole frontier.  Widening
`exceptionalFinal` to the whole frontier would import the first-Bob column, whose
`kappa_v >= 2` the banked `bobCapacity_add_card_finalNodes_le` charges to `K_B`
and not to `n_T`, and `09:1564`'s `K_B + n_T <= q` would be double-counted.  The
banked trap lemma is cited, never restated.  Sums over `bobNodes` occur in this
module only inside the inherited `firstBobMass` of the Bob-heavy count, and
nowhere else.

## GAP-EXPOSED, explicitly

1. **`hladder` (`09:1334--1338`).**  `lem:certified-row-ladder` invoked at
   `M = G`, `H = C-1`, `x = x_T`, `z = y`, `ell = 1` is the mathematical content
   of `lem:final-reference-uniqueness`, and it survives as the explicit named
   binder `hladder` of Section 1's supply, together with `residual` and
   `hresidual`.  Re-siting the ladder at the owner rectangle is the inherited
   GAP-EXPOSED item of `RoutedCertificateSystem`; it is never an `axiom`, never a
   premise-bundle field, never an opaque certificate.  What Section 1 does add is
   that the frozen *suffix budget* step of `09:1341--1343` is already derived on
   the protocol object by the banked `final_residual_budget`, so only the ladder
   call remains external.
2. **`hhost` (`09:1346--1347`).**  "Thus every final Alice node contains either
   one clean certificate, one half-weight descendant of a split certificate, or
   none."  Read at the clean column, this says a node the classification calls
   clean really hosts a clean certificate.  The classification `certOpt` is free
   data at the banked canonical clean count -- the routed record deliberately does
   not carry a node classification -- so the link between it and the certificates
   is the explicit structural binder `hhost`.  It is strictly weaker than a
   bijection: only the surjective half is asked for, and only onto the clean
   column.  `hosting_is_load_bearing` (Section 6) exhibits a banked routed system
   at which an over-generous classification makes the bridge false, so `hhost` is
   not decoration.
3. **`hLocEx` in both bundles.**  `thm:certified-localized-extension`
   (`A:109--146`), the entry point of **EXPANDER-001**, survives as an explicit
   named binder in Section 3 (`hLocExCC`) and in both halves of Section 5's bundle
   (`hLocExCC`, `hLocExEP`), inherited verbatim from the banked canonical
   endpoints.  It is never an `axiom`.
4. **`hfinal`** (`09:1346--1350`, licensed by `lem:final-reference-uniqueness`)
   likewise stays an explicit binder, as do `halleged`, `hcost`, `hres`, `hE1cc`,
   `hE2cc`, `hE1ep`, `hE2ep`, `htcert`, `htcertEP`, `hQuery`, `hBlocks`, `hbase`,
   `hbaseEP` and `hinj`.  **Full-bundle satisfiability is NOT claimed** anywhere
   in this module.
5. **`09:1566--1615` is not landed here.**  The four-category loss table and
   `eq:wrapper-mass-leaves-owner` are banked as arithmetic
   (`WrapperMassRedistribution.wrapperMassLeavesOwner`,
   `fourCategory_coefficients`) and as the first three engine lines
   (`MassRedistributionCounting`), and their fourth line consumes hardness rather
   than counting.  *Next round:* supply the engine retention
   `1 - (L1+L2+L3+L4) <= retained` at the owner rectangle and feed
   `wrapperMassLeavesOwner` with the banked deletion-stable endpoint.

## Axiom surface

The single import is `BobHeavyDonorCount`, whose transitive closure reaches
`ProtectedEarlyClosure`, `FrontierSumAssembly`, `MassRedistributionCounting`,
`ClosureSelectSupply`, `FrontierIndexing`, `DenseWrapperFrontier`,
`WrapperProtectedEarly`, `WrapperMassRedistribution`, `RoutedCertificateSystem`,
`SplitFirstBobInstance`, `FirstBobFrontierInstance` and `ParameterSchedule`.
`LegacyNPCC.Stage12` is **not** in that closure, so the cited AGHP balanced-family
axiom is unreachable from every declaration here.  No `axiom`, no opaque
certificate, no premise bundle, no new `structure`, `abbrev`, `instance` or `def`
is declared: this module contains theorems only.

## Canonical inhabitation

**REGISTERED and DEFERRED, inherited unchanged.**  This module declares no new
type, so it opens no new inhabitation obligation.  The inherited one cannot be
discharged as mathematics: the paper's own instance of every statement below is a
function of the **alleged** protocol of `09:1187--1193`, whose non-existence is
the conclusion of the whole subsection, so the frozen paper exhibits no routed
instance by construction.  Section 6's probes are explicitly **NON-FIDELITY** and
are not offered as fidelity witnesses; they exercise the two new supplies at the
banked live and split audit instances, and they exhibit the pole at which `hhost`
fails.
-/

namespace EthInapproximability.ParameterizedNP.WrapperExceptionalCount

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
open EthInapproximability.ParameterizedNP.BobHeavyDonorCount

/-! ## §1  `huniq`: owner uniqueness through the banked owner chain
(`09:1550--1552`, `09:1321--1344`)

The banked `MassRedistributionCounting.card_exceptionalFinal` and
`wrapperExceptionalCount_engine` take the frozen `09:1551--1552` in *fibre* form
-- "a final node contains at most one clean certificate" -- while the banked
protocol-object derivation
`RoutedCertificateSystem.RoutedSystem.owner_injOn_of_ladder` produces it in
*injectivity* form -- "distinct clean donors have distinct owners".  The two are
the same frozen sentence read in its two directions, and this section supplies the
translation the engine needs, so that `huniq` arrives from the ladder argument of
`09:1321--1344` rather than as a postulate. -/

section OwnerUniqueness

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}

/-- **`09:1551--1552`, injectivity form to fibre form.**

"Distinct clean donors have distinct owners because a final node contains at most
one clean certificate."  Read left to right, the frozen sentence says injectivity
*follows from* the fibre bound; the banked
`WrapperMassRedistribution.owner_injOn_of_unique_clean` is that direction.  This
is the converse, which is what the banked counting engine consumes: if the owner
map is injective on the clean donors then no final node carries two of them.

Elementary and general in both index types; nothing frozen is re-derived, only
transported.  It exists so that Section 1's ladder supply can be plugged into
`MassRedistributionCounting.wrapperExceptionalCount_engine` without weakening its
statement. -/
theorem ownerFibre_card_le_one_of_injOn {ι V : Type*} [DecidableEq V]
    (Jclean : Finset ι) (own : ι → V)
    (hinj : ∀ i ∈ Jclean, ∀ j ∈ Jclean, own i = own j → i = j) :
    ∀ v : V, (Jclean.filter fun j => own j = v).card ≤ 1 := by
  intro v
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  rw [Finset.mem_filter] at ha hb
  exact hinj a ha.1 b hb.1 (ha.2.trans hb.2.symm)

/-- **`lem:final-reference-uniqueness` (`09:1315--1344`) in the shape the engine
consumes.**

"Every final Alice-frontier node in the routed certificate system above contains
at most one reference certificate", proved at `09:1321--1344` by the certified row
ladder against the suffix budget of the alleged `(C+r-1)`-bit protocol.

The banked `RoutedSystem.owner_injOn_of_ladder` carries that whole argument on the
protocol object: the frozen `09:1341--1343` budget step is *derived* there by
`final_residual_budget` and the contradiction is the banked
`finalNode_budget_contradiction`; only the ladder call itself
(`lem:certified-row-ladder` at `M = G`, `H = C-1`, `x = x_T`, `z = y`, `ell = 1`,
`09:1334--1338`) stays external, as the named binder `hladder`.  This declaration
adds nothing to that argument -- it composes it with the fibre translation above,
so that `huniq` is *supplied* to the exceptional-count engine instead of assumed.

*Why the trivial witness fails.*  The conclusion is a universally quantified
bound on cardinalities, not an existential.  It is not vacuous either: the bound
is `<= 1`, not `<= |J_clean|`, and it genuinely fails for a map that sends two
clean donors to one node -- which is exactly the configuration the frozen proof
refutes, and exactly what `hladder` rules out.

General in the routed system, the coordinate type, the donor type, the node type
and the residual family; `C` is the frozen complexity target and is a binder, not
a value. -/
theorem ownerUniqueness_of_ladder {C : ℕ} [Fintype ι] [DecidableEq V]
    (S : RoutedSystem P Coord ι V r A0)
    (hC : 3 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (residual : ι → ι → ℕ)
    (hresidual : ∀ i j, residual i j ≤ (descend P (S.node (S.owner i))).cost)
    (hladder : ∀ i ∈ S.cleanFinal, ∀ j ∈ S.cleanFinal,
      S.owner i = S.owner j → (S.cert i).coord ≠ (S.cert j).coord → C ≤ residual i j) :
    ∀ v : V, (S.cleanFinal.filter fun i => S.owner i = v).card ≤ 1 :=
  ownerFibre_card_le_one_of_injOn S.cleanFinal S.owner
    (S.owner_injOn_of_ladder hC hcost residual hresidual hladder)

end OwnerUniqueness

/-! ## §2  `hclean` at `J_clean`: from the node count to the donor count
(`09:1348--1349`, `09:1519--1520`)

`09:1348--1349` defines `c` as "the number of final nodes with one clean
certificate", and `eq:wrapper-clean-count` bounds *that* number below.
`09:1519--1520` then reads the same `c` as `|J_clean|`, "the `c` outer coordinates
whose clean reference certificates reach final Alice nodes", and the banked
counting engine works at the donor side throughout (`RoutedSystem.cleanFinal`).

The identification is the frozen owner bijection.  Its injective half is banked
(`09:1551--1552`); the half needed *here* is the surjective one -- every node the
classification calls clean really hosts a clean certificate -- which is
`09:1346--1347` read at the clean column.  That is the binder `hhost`; everything
else is cardinality arithmetic. -/

section CleanDonorCount

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [Fintype ι]

/-- **`09:1346--1349` with `09:1519--1520`: the clean node count is at most the
clean donor count.**

The nodes of `cleanNodes` are owned by clean donors (that is `hhost`), so they lie
in the image of `J_clean` under the owner map, and an image is never larger than
its source.  No injectivity is used in this direction: two clean nodes with the
same owner would only make the inequality easier.

General in the routed system, the classification and both index types. -/
theorem cleanNodes_card_le_cleanFinal_card
    (S : RoutedSystem P Coord ι V r A0) (certOpt : V → Option CertKind)
    (hhost : ∀ v ∈ S.toWrapperFrontier.cleanNodes certOpt,
      ∃ i ∈ S.cleanFinal, S.owner i = v) :
    (S.toWrapperFrontier.cleanNodes certOpt).card ≤ S.cleanFinal.card := by
  classical
  have hsub : S.toWrapperFrontier.cleanNodes certOpt ⊆ S.cleanFinal.image S.owner := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := hhost v hv
    exact Finset.mem_image_of_mem _ hi
  calc (S.toWrapperFrontier.cleanNodes certOpt).card
      ≤ (S.cleanFinal.image S.owner).card := Finset.card_le_card hsub
    _ ≤ S.cleanFinal.card := Finset.card_image_le

/-- **`eq:wrapper-clean-count`, first clause, transported to `J_clean`.**

`c >= q - e_0/(1-vartheta)` is proved by the banked spine at the *node* count of
`09:1348--1349`; the banked counting engine reads `c` at the *donor* set of
`09:1519--1520`.  This is that transport, and it is the `hclean` slot of
`MassRedistributionCounting.wrapperExceptionalCount_engine`, produced rather than
assumed.

*Why the trivial witness fails.*  The conclusion is an inequality between two
fixed reals, not an existential, and it is not a formal truth: its left-hand side
is positive at the frozen parameters (the banked
`FirstBobFrontierInstance.live_cleanCount_positive_lhs` exhibits `q - e_0/(1 -
vartheta) = 12/7 > 0` at a live routed system), so it genuinely constrains
`|J_clean|`.  `hhost` is load-bearing: see `hosting_is_load_bearing`.

General in the routed system, the classification, both index types and both
reals. -/
theorem cleanCount_at_cleanFinal
    (S : RoutedSystem P Coord ι V r A0) (certOpt : V → Option CertKind)
    (hhost : ∀ v ∈ S.toWrapperFrontier.cleanNodes certOpt,
      ∃ i ∈ S.cleanFinal, S.owner i = v)
    {q e0 : ℝ}
    (hcc : q - e0 / (1 - vartheta)
      ≤ ((S.toWrapperFrontier.cleanNodes certOpt).card : ℝ)) :
    q - e0 / (1 - vartheta) ≤ (S.cleanFinal.card : ℝ) := by
  have hcard : ((S.toWrapperFrontier.cleanNodes certOpt).card : ℝ)
      ≤ (S.cleanFinal.card : ℝ) := by
    exact_mod_cast cleanNodes_card_le_cleanFinal_card S certOpt hhost
  linarith

end CleanDonorCount

/-! ## §3  `eq:wrapper-exceptional-count` at the canonical routed system
(`09:1550--1564`)

`e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`.

The banked `MassRedistributionCounting.wrapperExceptionalCount_engine` already
proves both clauses from `09:1548`'s split, the banked Kraft consequence
`K_B + n_T <= q` and the two binders this tranche discharges:

* `huniq` from Section 1, at the ladder route of `09:1321--1344`;
* `hclean` from Section 2, at the banked
  `FrontierSumAssembly.canonical_cleanCount_of_reference_construction` -- i.e.
  `eq:wrapper-clean-count` at the canonical system with `hlight` already retired.

`e_0` is the evaluated `(E0.card : R)` of `09:450`, never a free real. -/

section FrozenDisplay

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`eq:wrapper-exceptional-count` (`09:1555--1563`) at the canonical system.**

"All final nodes not owned by `J_good` are called exceptional; their number is
`e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`.  Here we used
`K_B + n_T <= q` and `eq:wrapper-clean-count`."

*What is derived rather than assumed.*  Both remaining slots of the banked
`MassRedistributionCounting.wrapperExceptionalCount_engine`:

* `huniq` is `ownerUniqueness_of_ladder` fired at the canonical system, i.e.
  `lem:final-reference-uniqueness` through the banked
  `RoutedSystem.owner_injOn_of_ladder`;
* `hclean` is `cleanCount_at_cleanFinal` fired at the first conjunct of
  `FrontierSumAssembly.canonical_cleanCount_of_reference_construction`.

The counting itself -- `e_T = n_T - |J_good|`, `|J_good| = c - e_B`, and
`K_B + n_T <= q` -- is the banked engine and is restated nowhere.

*What is still a binder.*  `hladder` with `residual`/`hresidual` (GAP-EXPOSED
item 1), `hhost` (item 2), `hLocExCC` (item 3, the **EXPANDER-001** entry point),
`hfinal`, `halleged`, `hcost`, `hmem`, `hcover`, `hbase`, `htcert`, `hE1cc`,
`hE2cc`, `hB`, `hblock`, `hplace` -- all inherited **verbatim** from the banked
clean count, with no hypothesis added to it and none weakened.
**Full-bundle satisfiability is not claimed.**

*Why the trivial witness fails.*  The conclusion is a conjunction of two
inequalities between fixed reals, not an existential.  Neither clause is vacuous:
the banked `MassRedistributionCounting.exceptionalCount_engine_hypotheses_consistent`
exhibits a routed instance where `e_T = 1`, `n_T = 2`, `c = 2` and `e_B = 1`, so
both clauses are checked against positive quantities rather than against zero, and
the banked `card_exceptionalFinal_needs_owner_injectivity` shows the first clause
fails outright without `huniq`.

*No route completion.*  `eq:wrapper-u-dense` is neither stated nor implied;
`09:1566--1781` remains open.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet `Yc`,
the Alice carrier `X`, in `q`, `r`, `b_T`, `k_ref`, `C`, `t_cert`, `E_0`, the mass
family, the tolerance, the classification, the residual family and the two real
parameters `x_U` and `theta`. -/
theorem canonical_wrapperExceptionalCount {RwN : Type*}
    {r bT kref C tcert : ℕ} {E0 : Finset (Fin q)} {xU θ etaR : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
    (Pv : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    -- the clean-count bundle, verbatim
    (hq : (q : ℝ) = (2 : ℝ) ^ r)
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → (Fin q → Yc))}
    (hmem : RC ∈ bracketGE X (Fin q → Yc) 1 xU θ)
    (hk : 4 ≤ kref) (hq4 : kref + 2 ≤ r)
    (hX : 0 < Fintype.card X) (hYc : 0 < Fintype.card Yc)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 3 ≤ C)
    (hgate : ((2 : ℝ) ^ r) * xTdepth bT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5))
    (htcert : tcert ≤ 2 ^ kref)
    (hE1cc : (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2cc : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)))
    (hcost : P.cost ≤ C + r - 1)
    (hLocExCC :
      ∀ v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r,
      (canonicalSystem hcomp hR).firstBob v = true →
      ∀ (Sblk : Finset (StartedCoord E0)) (T : Finset X) (c : Bool)
      (htr : RoutedTriple (Blk := StartedCoord E0) (Row := X) (Col := Fin q → Yc)
        (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ Sblk T
        (retainedCols P (rootColumnSet RC.2) (v.val ++ [c]))),
      1 ≤ Fintype.card X →
      2 ≤ C - 1 →
      0 < xTdepth bT → xTdepth bT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 (xTdepth bT) (3 / 5) →
      tcert ≤ 2 ^ kref →
      4 ≤ kref →
      ((2 : ℝ) ^ kref) * xTdepth bT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) ≤ 2 ^ (r - kref) →
      (2 : ℕ) ^ ((r - v.val.length) - kref) * 2 ^ kref = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 →
      θ / 2 ^ (1 : ℕ) ≤ (paperFrontierRestriction htr hθ0 hθ1).colDens →
      (3 / 5 : ℝ) ^ (2 ^ kref) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity kref
        ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + kref)) →
      2 ^ ((r - v.val.length) - kref) * (9 * 2 ^ kref / 16)
        = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ ((paperFrontierRestriction htr hθ0 hθ1).selCard : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ)⌉₊
        ≤ (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ (descend P (v.val ++ [c])).cost)
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
    -- `09:1321--1344`: the ladder route to owner uniqueness
    (residual : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℕ)
    (hresidual : ∀ i j, residual i j
      ≤ (descend P ((canonicalSystem hcomp hR).node
          ((canonicalSystem hcomp hR).owner i))).cost)
    (hladder : ∀ i ∈ (canonicalSystem hcomp hR).cleanFinal,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal,
      (canonicalSystem hcomp hR).owner i = (canonicalSystem hcomp hR).owner j →
      ((canonicalSystem hcomp hR).cert i).coord ≠ ((canonicalSystem hcomp hR).cert j).coord →
      C ≤ residual i j)
    -- `09:1346--1347`: a clean-classified final node hosts a clean certificate
    (hhost : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.cleanNodes certOpt,
      ∃ i ∈ (canonicalSystem hcomp hR).cleanFinal,
        (canonicalSystem hcomp hR).owner i = v) :
    ((exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
        ≤ (q : ℝ) - ((canonicalSystem hcomp hR).cleanFinal.card : ℝ)
            + ((bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ∧ (q : ℝ) - ((canonicalSystem hcomp hR).cleanFinal.card : ℝ)
            + ((bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
        ≤ (E0.card : ℝ) / (1 - vartheta)
            + ((bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ) := by
  have hcc := FrontierSumAssembly.canonical_cleanCount_of_reference_construction
    Nmat Gmat ιR hsub halleged hcomp hR certOpt hq hmem hk hq4 hX hYc hθ0 hθ1 hC hgate
    hbase htcert hE1cc hE2cc hcost hLocExCC hcover B hB plc hblock hplace hfinal
  exact wrapperExceptionalCount_engine (canonicalSystem hcomp hR) Pv etaR
    (ownerUniqueness_of_ladder (canonicalSystem hcomp hR) hC hcost residual hresidual hladder)
    hq (cleanCount_at_cleanFinal (canonicalSystem hcomp hR) certOpt hhost hcc.1)

end FrozenDisplay

/-! ## §4  The MANDATED `heB` closure (`09:1718--1726`)

"The size of `J_good` is not a schedule input.  It is a derived fact: by
`eq:wrapper-clean-count`, `eq:wrapper-bob-heavy-count`, `eq:cover-bounds`, and
`eq:terminal-uniform-bounds`,
`|J_good| = c - e_B >= q - ceil(e_0^max/(1-vartheta)) - E_B = q - E_T`."

`BobHeavyDonorCount` banked the schedule bridge `e_B <= E_B` over the naturals and
recorded that "one `le_trans` and one `Nat.cast_le` remain at the consumer".
`WrapperMassRedistribution.goodDonorCount_ge` banked the arithmetic with `heB` as
a real binder.  This section is that consumer: the two meet, and the frozen
right-hand side is `ParameterSchedule.ET` with both ceilings preserved.

Three frozen inputs and no more: `09:1548`'s split (an identity of cardinalities),
`09:452--453`'s `e_0 <= e_0^max` under the monotonicity of `x -> x/(1-vartheta)`, and
`Nat.le_ceil` at the preserved ceiling of `06:723`. -/

section ScheduleClosure

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [Fintype ι] [DecidableEq ι]

/-- **`09:1718--1726`, `|J_good| >= q - E_T`, at a routed system.**

The twice-deferred composition, performed: `BobHeavyDonorCount.bobHeavyCount_le_EB`
turns `eq:wrapper-bob-heavy-count` into the natural-number bound `e_B <= E_B`,
`Nat.cast_le` moves it to the reals where
`WrapperMassRedistribution.goodDonorCount_ge` states its `heB` slot, and one
`le_trans` inside that lemma finishes.  The `ceil(e_0^max/(1-vartheta))` summand of
`E_T` is reached from `hclean` by `09:452--453`'s `e_0 <= e_0^max` and `Nat.le_ceil`.

*The `vartheta` seam.*  `hclean` carries the `09:1268` twin
(`DenseWrapperFrontier.vartheta`, the one `eq:wrapper-clean-count` uses) while
`ParameterSchedule.ET` carries the `06:718` twin.  The seam is crossed here by the
two banked evaluations `one_sub_vartheta` and `ParameterSchedule.one_sub_vartheta`,
which give `1 - vartheta = 7/16` on both sides; the banked
`FrontierSumAssembly.vartheta_twins_agree` reaches this proof **only transitively**,
through `bobHeavyCount_le_EB` for `E_B`.  Neither name is re-declared.

*Why the trivial witness fails.*  The conclusion is an inequality between two
fixed reals, not an existential, and it is not vacuously weak: `E_T >= 1` at every
legal input (the banked `WrapperMassRedistribution.one_le_ET_of_e0Max_pos` at
`09:1727--1731`), so `q - E_T` is strictly below `q` and the bound is not the
trivial `|J_good| >= q - q`.  It is also not vacuously strong: `heB` is
load-bearing, see `goodDonorCount_needs_heB`.

General in the routed system, the mass family, both index types and every schedule
quantity; no value is assigned to any of them. -/
theorem goodDonorCount_ge_q_sub_ET
    (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ)
    {Bt Lqv sv e0m : ℕ} {q e0 etaR : ℝ}
    (hetaR : 0 < etaR) (he0 : e0 ≤ (e0m : ℝ))
    (hclean : q - e0 / (1 - vartheta) ≤ (S.cleanFinal.card : ℝ))
    (hcount : ((bobHeavyDonors S Pv etaR).card : ℝ)
      ≤ 512 * muP * (Bt : ℝ) * (Lqv : ℝ) * (sv : ℝ) * e0 / ((1 - vartheta) * etaR)) :
    q - ((ParameterSchedule.ET e0m (ParameterSchedule.EB Bt Lqv sv e0m etaR) : ℕ) : ℝ)
      ≤ ((goodDonors S Pv etaR).card : ℝ) := by
  have hv : (1 : ℝ) - vartheta = 7 / 16 := one_sub_vartheta
  have hvP : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
    ParameterSchedule.one_sub_vartheta
  -- `06:732--733`: the schedule bridge, then the cast the banked arithmetic needs
  have heB : ((bobHeavyDonors S Pv etaR).card : ℝ)
      ≤ ((ParameterSchedule.EB Bt Lqv sv e0m etaR : ℕ) : ℝ) := by
    exact_mod_cast bobHeavyCount_le_EB hetaR he0 hcount
  -- `09:1548`: the split, as an identity of cardinalities
  have hsplit := card_goodDonors_add_card_bobHeavy S Pv etaR
  have hjgood : ((goodDonors S Pv etaR).card : ℝ)
      = (S.cleanFinal.card : ℝ) - ((bobHeavyDonors S Pv etaR).card : ℝ) := by
    have hcast : (((goodDonors S Pv etaR).card + (bobHeavyDonors S Pv etaR).card : ℕ) : ℝ)
        = (S.cleanFinal.card : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hsplit
    push_cast at hcast
    linarith
  -- `09:452--453` and `Nat.le_ceil` at the preserved ceiling of `06:723`
  have hceilBase := Nat.le_ceil ((e0m : ℝ) / (1 - ParameterSchedule.vartheta))
  have hstep : e0 / (1 - vartheta) ≤ (e0m : ℝ) / (1 - ParameterSchedule.vartheta) := by
    rw [hv, hvP]
    linarith
  have hc : q - ((⌈(e0m : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ : ℕ) : ℝ)
      ≤ (S.cleanFinal.card : ℝ) := by
    linarith
  have hmain := goodDonorCount_ge hjgood hc heB
  rw [ParameterSchedule.ET]
  push_cast
  push_cast at hmain
  linarith

end ScheduleClosure

/-! ## §5  `|J_good| >= q - E_T` at the canonical routed system

Section 4 fired at the canonical system, with **both** of its analytic inputs
discharged rather than assumed:

* `hcount` is `BobHeavyDonorCount.canonical_wrapperBobHeavyCount`, i.e.
  `eq:wrapper-bob-heavy-count` at the canonical system;
* `hclean` is Section 2 fired at
  `FrontierSumAssembly.canonical_cleanCount_of_reference_construction`, i.e.
  `eq:wrapper-clean-count` at the canonical system.

The only new binders relative to the banked Bob-heavy endpoint are `he0`
(`09:452--453`, `e_0 <= e_0^max`, the deterministic bound the construction records) and
`hhost` (`09:1346--1347`, GAP-EXPOSED item 2).  Owner uniqueness is **not**
needed here: `|J_good|` is a donor count, and `09:1548`'s split is an identity of
cardinalities that does not pass through the owner map. -/

section CanonicalClosure

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`09:1718--1726` at the canonical routed system.**

`|J_good| >= q - E_T`, with `E_T = ceil(e_0^max/(1-vartheta)) + E_B` the banked
`ParameterSchedule.ET` at `E_B = ParameterSchedule.EB B_theta L_q s e_0^max eta_R`
and every argument evaluated through the definitional chain:
`B_theta = WrapperProtectedEarly.Btheta theta`, `L_q = WrapperProtectedEarly.Lq q`
and `s = 2^{r_3}` are the same expressions
`BobHeavyDonorCount.canonical_wrapperBobHeavyCount` prints on the right-hand side
of `eq:wrapper-bob-heavy-count`.  No numeral is assigned to any of them.

*What is still a binder.*  `hLocExCC` and `hLocExEP` (**EXPANDER-001**), `hfinal`,
`halleged`, `hcost`, `hres`, `hinj`, `hhost` and the analytic members of the
protected-closure bundle, all inherited **verbatim**; no hypothesis is added to the
banked endpoints and none is weakened.  `he0` is `09:452--453` and is new.
**Full-bundle satisfiability is not claimed.**

*Why the trivial witness fails.*  Not an existential; and not vacuous, since
`E_T >= 1` at legal inputs (`WrapperMassRedistribution.one_le_ET_of_e0Max_pos`)
makes `q - E_T < q` a genuine constraint, while `q > 0` is derived at the frozen
gates rather than assumed.  The frozen consumer of this conclusion is
`eq:wrapper-terminal-donor-gate` (`09:1732--1741`), whose banked arithmetic
`wrapperTerminalDonorGate` takes exactly `q - E_T <= |J_good|` as its `hjgood`
slot; that consumer is **not** fired here, and no route completion is claimed. -/
theorem canonical_goodDonorCount_ge_q_sub_ET {RwN : Type*} [Fintype RwN]
    {r bT kref tcert e0m : ℕ} {E0 : Finset (Fin q)} {xU θ etaR : ℝ}
    (Nmat : RwN → Yc → Bool) (Gmat : X → Yc → Bool) (ιR : X → RwN)
    (hsub : ∀ a c, Gmat a c = Nmat (ιR a) c)
    {P : Protocol X (Fin q → Yc) Bool} {g : X → (Fin q → Yc) → Bool}
    (halleged : Protocol.Computes P g)
    (hcomp : CompletedNoBob P r) {R : StartedCoord E0 → Finset X}
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (certOpt : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      Option CertKind)
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
    (hinj : ∀ i ∈ (canonicalSystem hcomp hR).cleanFinal,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal, donor i = donor j → i = j)
    (hres : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.bobNodes,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal,
      Pv v j = muP * (d₀ v (donor j) + d₁ v (donor j)))
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hcost : P.cost ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
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
    (hetaR : 0 < etaR)
    -- `09:452--453`: the construction records `e_0 <= e_0^max`
    (he0 : (E0.card : ℝ) ≤ (e0m : ℝ))
    -- `09:1346--1347`: a clean-classified final node hosts a clean certificate
    (hhost : ∀ v ∈ (canonicalSystem hcomp hR).toWrapperFrontier.cleanNodes certOpt,
      ∃ i ∈ (canonicalSystem hcomp hR).cleanFinal,
        (canonicalSystem hcomp hR).owner i = v) :
    (q : ℝ) - ((ParameterSchedule.ET e0m
          (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) : ℕ) : ℝ)
      ≤ ((goodDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ) := by
  have hcc := FrontierSumAssembly.canonical_cleanCount_of_reference_construction
    Nmat Gmat ιR hsub halleged hcomp hR certOpt hq hmem hk hq4 hX hYc hθ0 hθ1 hC hgate
    hbase htcert hE1cc hE2cc hcost hLocExCC hcover B hB plc hblock hplace hfinal
  have hclean := cleanCount_at_cleanFinal (canonicalSystem hcomp hR) certOpt hhost hcc.1
  have hcount := canonical_wrapperBobHeavyCount Nmat Gmat ιR hsub halleged hcomp hR certOpt
    isRestrEP Scol YT Pv donor d₀ d₁ ell bsel hdepth hinj hres hC hcost hq hmem hk hq4 hX hYc
    hθ0 hθ1
    hgate hbase htcert hE1cc hE2cc hLocExCC hcover B hB plc hblock hplace hfinal hqpos hk₂
    hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0 hSep hYT hgap hQuery hBlocks hx0 hx1 htx
    hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep hrows hSelectEP hLocExEP hne hetaR
  exact goodDonorCount_ge_q_sub_ET (canonicalSystem hcomp hR) Pv hetaR he0 hclean hcount

end CanonicalClosure

/-! ## §6  Aux-lemma battery

Five general checks on the exceptional count and on the two supplies.
**Canonical inhabitation is INHERITED, REGISTERED and DEFERRED** per the header:
this module declares no new type, so it opens no new obligation, and the inherited
one cannot be discharged because the paper's own instance of every statement above
is a function of the alleged protocol of `09:1187--1193`, which does not exist.
Nothing in this section evaluates a schedule parameter or carries a numeral of its
own. -/

section Battery

variable {X Y Z : Type*} {Coord ι V : Type*} {P : Protocol X Y Z} {r A0 : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- **Battery 1 (the exceptional nodes are final nodes, and only final nodes).**

`09:1553` cuts the exceptional set out of the final nodes, so `e_T <= n_T` is
structural.  This is the **two-kappa trap** on the count side: the first-Bob
column, whose `kappa_v >= 2` (`09:1259`) the banked
`bobCapacity_add_card_finalNodes_le` charges to `K_B`, is never counted in `e_T`,
and `09:1564`'s `K_B + n_T <= q` is therefore not double-counted.  General. -/
theorem exceptionalFinal_subset_finalNodes
    (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ) (etaR : ℝ) :
    exceptionalFinal S Pv etaR ⊆ S.toWrapperFrontier.finalNodes :=
  Finset.sdiff_subset

/-- **Battery 2 (the exceptional count is antitone in the tolerance).**

Raising the Bob-heavy threshold shrinks the Bob-heavy set (the banked
`MassRedistributionCounting.bobHeavyDonors_antitone`, cited and not restated),
hence enlarges `J_good`, hence enlarges the owned nodes, hence shrinks the
exceptional set.  So `e_T` moves in the direction the frozen text needs: a larger
`eta_R` gives both a smaller `e_B` and a smaller `e_T`, which is why
`eq:wrapper-exceptional-count`'s two `e_B` terms do not fight the tolerance.
General. -/
theorem exceptionalFinal_antitone_in_etaR
    (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ) {etaR etaR' : ℝ}
    (h : etaR ≤ etaR') :
    exceptionalFinal S Pv etaR' ⊆ exceptionalFinal S Pv etaR := by
  classical
  have hgood : goodDonors S Pv etaR ⊆ goodDonors S Pv etaR' := by
    intro j hj
    rw [goodDonors, Finset.mem_sdiff] at hj ⊢
    exact ⟨hj.1, fun hmem => hj.2 (bobHeavyDonors_antitone S Pv h hmem)⟩
  refine Finset.sdiff_subset_sdiff (Finset.Subset.refl _) ?_
  exact Finset.image_subset_image hgood

/-- **Battery 3 (the two readings of `09:1551--1552` are equivalent).**

The frozen sentence "Distinct clean donors have distinct owners because a final
node contains at most one clean certificate" is used in this development in two
forms: the fibre bound the counting engine consumes, and the injectivity the
protocol-object derivation produces.  Section 1 supplies one direction and the
banked `WrapperMassRedistribution.owner_injOn_of_unique_clean` the other, so the
translation loses nothing -- an important check, because a one-way translation
could silently strengthen the hypothesis of every consumer.  General. -/
theorem ownerUniqueness_iff_ownerInjOn {ι V : Type*} [DecidableEq V]
    (Jclean : Finset ι) (own : ι → V) :
    (∀ v : V, (Jclean.filter fun j => own j = v).card ≤ 1)
      ↔ (∀ i ∈ Jclean, ∀ j ∈ Jclean, own i = own j → i = j) :=
  ⟨owner_injOn_of_unique_clean Jclean own, ownerFibre_card_le_one_of_injOn Jclean own⟩

/-- **Battery 4 (`E_T` is monotone in `e_0^max`).**

`09:452--453` records a deterministic *upper* bound `e_0 <= e_0^max`, and `06:723`
builds `E_T` from it through a ceiling.  A consumer that knows only a weaker bound
must get a weaker conclusion, and this is that direction: enlarging `e_0^max`
enlarges `E_T`, hence lowers the `q - E_T` floor of `09:1725`.  This is what makes
Section 4's replacement of `e_0` by `e_0^max` a legal weakening rather than a
change of statement.  General; `1 - vartheta = 7/16 > 0` is the banked
`ParameterSchedule.one_sub_vartheta`. -/
theorem ET_mono_in_e0max {e0m e0m' EBv : ℕ} (h : e0m ≤ e0m') :
    ParameterSchedule.ET e0m EBv ≤ ParameterSchedule.ET e0m' EBv := by
  have hvP : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
    ParameterSchedule.one_sub_vartheta
  have hR : (e0m : ℝ) ≤ (e0m' : ℝ) := by exact_mod_cast h
  have hdiv : (e0m : ℝ) / (1 - ParameterSchedule.vartheta)
      ≤ (e0m' : ℝ) / (1 - ParameterSchedule.vartheta) := by
    rw [hvP]; linarith
  rw [ParameterSchedule.ET, ParameterSchedule.ET]
  exact Nat.add_le_add_right (Nat.ceil_le_ceil hdiv) _

/-- **Battery 5 (`e_T = 0` exactly when the good donors own everything).**

`09:1702` spends the case `e_T = 0` ("If `e_T = 0`, this is already a
contradiction"), so the vanishing case has to be a genuine, checkable condition
rather than an accident of the encoding: the exceptional set is empty precisely
when every final node is owned by a good donor.  Both directions, from the frozen
set difference of `09:1553`.  General. -/
theorem exceptionalFinal_eq_empty_iff
    (S : RoutedSystem P Coord ι V r A0) (Pv : V → ι → ℝ) (etaR : ℝ) :
    exceptionalFinal S Pv etaR = ∅
      ↔ S.toWrapperFrontier.finalNodes ⊆ (goodDonors S Pv etaR).image S.owner := by
  rw [exceptionalFinal, Finset.sdiff_eq_empty_iff_subset]

end Battery

/-! ## §7  Live firings and statement poles

The probes below are **NON-FIDELITY** and claim no legality for the routed systems
they use: the paper's own instance is the routing of the alleged protocol, which
does not exist.  What they establish is that the two new supplies fire at banked
live instances, and that `hhost` is a real hypothesis rather than decoration. -/

section Probes

/-- **`09:1346--1347` holds at the live audit instance.**

Both final Alice nodes of `FirstBobFrontierInstance.liveSystem` host a clean
certificate, so the hosting binder of Section 2 is satisfied there by computation
at the classification `09:1348--1349` uses (`fun _ => some clean`, the one
`live_cleanNodes_card` and `live_cleanCount` are stated at).

**NON-FIDELITY**, per `FirstBobFrontierInstance`'s own BEYOND-PAPER AUDIT label. -/
theorem probe_hosting_live :
    ∀ v ∈ liveSystem.toWrapperFrontier.cleanNodes (fun _ => some CertKind.clean),
      ∃ i ∈ liveSystem.cleanFinal, liveSystem.owner i = v := by decide

/-- **Section 2 fired at the live instance.**

`eq:wrapper-clean-count`'s first clause, banked at the *node* count by
`FirstBobFrontierInstance.live_cleanCount`, transported to the *donor* count
`|J_clean|` the counting engine reads.  The transported bound is live rather than
vacuous: its left-hand side `4 - 1/(1-vartheta) = 12/7` is positive
(`live_cleanCount_positive_lhs`, consumed by pin) and `|J_clean| = 2`.

**NON-FIDELITY**; `q = 4` is DERIVED from `09:105` at `r = 2` and `e_0 = 1` is
inherited under the audit label. -/
theorem probe_cleanCount_at_cleanFinal_live :
    (4 : ℝ) - 1 / (1 - vartheta) ≤ (liveSystem.cleanFinal.card : ℝ) :=
  cleanCount_at_cleanFinal liveSystem (fun _ => some CertKind.clean) probe_hosting_live
    live_cleanCount.1

/-- **Statement pole: `hhost` is load-bearing.**

`SplitFirstBobInstance.splitSystem` has two final Alice nodes, one carrying a
clean certificate and one carrying the half-weight descendant of a split
certificate -- exactly the trichotomy of `09:1346--1347`.  Classify **both** as
clean, and the node count of `09:1348--1349` becomes `2` while the donor count
`|J_clean|` of `09:1519--1520` is still `1`: the bridge of Section 2 is then
false, and so is the `hclean` slot it feeds.

The over-generous classification is **ours** and is exhibited only to make the
guard fire: this is a non-legality-claiming rejection probe, not a witness.  What
it shows is that `hhost` cannot be dropped, and that the frozen `09:1346--1347`
trichotomy is doing work rather than being a restatement. -/
theorem hosting_is_load_bearing :
    ¬ ((splitSystem.toWrapperFrontier.cleanNodes (fun _ => some CertKind.clean)).card
        ≤ splitSystem.cleanFinal.card) := by decide

/-- **Section 1 fired at a banked live instance.**

The banked `RoutedCertificateSystem.ladderSystem_owner_injOn` proves the
injectivity form of `09:1551--1552` at the all-final frame-legal system, for every
`C >= 3` and every width; Section 1's translation turns it into the fibre form the
exceptional-count engine consumes, and the banked
`MassRedistributionCounting.card_exceptionalFinal` then fires there.

**NON-FIDELITY**, and the banked instance's own caveat is preserved: at the ladder
system the `hladder` obligation of `owner_injOn_of_ladder` is discharged
vacuously, so what this probe exercises is the *translation*, not the ladder
call. -/
theorem probe_ownerUniqueness_ladderSystem {Xp Yp Zp : Type*}
    (a : Xp → Bool) (z : Zp) {rwid C : ℕ} (hC : 3 ≤ C) (A0 : ℕ) :
    ∀ v : Fin rwid → Bool,
      ((ladderSystem (X := Xp) (Y := Yp) a z rwid A0).cleanFinal.filter
        fun i => (ladderSystem (X := Xp) (Y := Yp) a z rwid A0).owner i = v).card ≤ 1 :=
  ownerFibre_card_le_one_of_injOn _ _
    (ladderSystem_owner_injOn (X := Xp) (Y := Yp) a z (C := C) hC A0)

/-- **Hypothesis consistency for the two binders this tranche introduces.**

A green build cannot see whether `hhost` and `huniq` are jointly satisfiable, nor
whether they are satisfiable *alongside* a nonempty exceptional set -- and a
tranche whose two new binders silently excluded each other would compile and prove
nothing.  Here they are met together at one routed instance, with the clean count
transported through Section 2 and the exceptional count positive.

What this adds to the banked
`MassRedistributionCounting.exceptionalCount_engine_hypotheses_consistent` is
exactly the part that tranche could not state: that instance supplies `hclean` by
computation and does not mention `hhost` at all, because Section 2 did not exist.
Here `hclean` arrives **through the bridge**, from the banked node count
`FirstBobFrontierInstance.live_cleanCount`, with `hhost` and `huniq` holding at the
same system and `e_T > 0`.

**BEYOND-PAPER AUDIT values -- explicitly NOT legal ones**, inherited unchanged
from `FirstBobFrontierInstance` and `MassRedistributionCounting`: `q = 4` is
DERIVED from `09:105` at `r = 2`; `r`, `A_0` and `e_0 = 1` carry that module's own
label; `eta_R = 1` is **ours** and is illegal by a wide margin (`eq:eta-choice`
forces `eta_R <= 1/36800`).  No legality is claimed, and this is not a canonical
inhabitant. -/
theorem newBinders_consistent_at_the_live_instance :
    (∀ v ∈ liveSystem.toWrapperFrontier.cleanNodes (fun _ => some CertKind.clean),
        ∃ i ∈ liveSystem.cleanFinal, liveSystem.owner i = v)
      ∧ (∀ v : FrontierNode liveProtocol liveRows 1 2,
        (liveSystem.cleanFinal.filter fun i => liveSystem.owner i = v).card ≤ 1)
      ∧ (4 : ℝ) - 1 / (1 - vartheta) ≤ (liveSystem.cleanFinal.card : ℝ)
      ∧ 0 < (exceptionalFinal liveSystem probeMass 1).card :=
  ⟨probe_hosting_live, probe_owner_unique, probe_cleanCount_at_cleanFinal_live, by
    rw [probe_counts.2.2]; norm_num⟩

/-- **Statement pole: `heB` is load-bearing in `09:1718--1726`.**

The frozen derivation replaces `e_B` by its schedule majorant `E_B` before
subtracting.  Without that majorant step the conclusion is false: at `c = 2`,
`e_B = 2` (so `|J_good| = 0`) with `q = 4`, `ceil(e_0^max/(1-vartheta)) = 1` and
`E_B = 1`, the frozen right-hand side reads `4 - (1 + 1) = 2` and the derived left
reads `0`.

The four reals are **ours** and are exhibited only to make the guard fire: this is
a non-legality-claiming rejection probe on the shape of `goodDonorCount_ge`, not a
witness for any schedule.  It shows that Section 4's `Nat.cast_le` of
`bobHeavyCount_le_EB` is a real step and not bookkeeping. -/
theorem goodDonorCount_needs_heB :
    ¬ ((4 : ℝ) - ((1 : ℝ) + 1) ≤ (2 : ℝ) - 2) := by norm_num

end Probes

end EthInapproximability.ParameterizedNP.WrapperExceptionalCount
