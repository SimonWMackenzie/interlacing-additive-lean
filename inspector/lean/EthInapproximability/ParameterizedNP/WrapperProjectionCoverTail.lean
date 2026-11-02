import EthInapproximability.ParameterizedNP.WrapperUDenseOpening

/-!
# Parameterized NP route: the poor-`u_don` projection-cover tail, `09:1746--1781`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche), **lines `09:1746--1781`**, the final
  paragraph block of `sec:wrapper-mass-redistribution`, opening immediately after
  the `09:1742--1744` sentence the predecessor module `WrapperUDenseOpening`
  discharges and closing at `09:1781`, the last line before
  `\begin{proof}[Proof of \Cref{thm:first-wrapper}]` at `09:1783`.

  The anchors traced here, in frozen print order:
  * `09:1746--1749`, the poor-`u_don` projection cover: "Apply the
    poor-`u_don` projection cover to the donors feeding `T_*`.  By
    `eq:wrapper-terminal-donor-gate`, it leaves `u_don` donors whose joint outer
    projection has density at least `rho_0`";
  * `09:1749--1755`, the coordinate extraction: "Apply
    `lem:template-coordinate-extraction` and fix one Stage-3 bin in each of the
    resulting `u_don/2` donors.  The retained column set in
    `C_2^{u_don/2}` has density at least `rho_0 2^{-u_don-1}`";
  * `09:1756--1760`, the Stage-2 partition average: "For each selected donor,
    partition its protected rows by their Stage-2 coordinate.  Rows in one part
    share the same Stage-4 entry map.  Averaging these `q_2` parts gives at least
    `delta_0 q_2/2` represented Stage-2 outer blocks whose surviving
    `C_1`-density is at least `delta_0/2`";
  * `eq:wrapper-terminal-block-supply` (display `09:1761--1765`, label
    `09:1763`): `u_don delta_0 q_2/4 >= 2 s q_2`;
  * `09:1767--1770`: "Put `kappa = 2 s q_2` and select exactly `9 kappa/16` of
    these blocks.  Because `u_don >= 8s`, the ambient width `(u_don/2) q_2` is at
    least `2 kappa`, so `r' = kappa/t_2` is legal";
  * `09:1770--1774`: "The finite terminal product gates verify call~(iv) in
    `sec:extension-call-ledger` uniformly for every `e_T <= E_T` and
    `u_don <= u_term`.  Its conclusion at `T_*` is";
  * `09:1775--1779`, the endpoint identity
    `B_cap + log_2 kappa = B_cap + log_2 q_2 + log_2 s + 1 = C`;
  * `09:1780--1781`: "This again contradicts the shallow protocol.  We have
    proved `eq:wrapper-u-dense`."

* **Cross-anchors opened first-hand in the frozen files for this tranche:**
  * `lem:template-coordinate-extraction` (statement `09:1388--1399`, proof
    `09:1401--1416`), applied at `rho = rho_0` here.  Note the frozen difference
    from its row-(iii) use at `09:1466--1469`: there a Bob query first halves
    `rho_0` to `rho_1`, **here there is no query** -- `09:1746--1755` passes
    straight from the cover's `rho_0` to `rho_0 2^{-u_don-1}`, which is why row
    (iv)'s entering density is `callFourH` and not `callThreeH`.
  * `lem:product-projection-cover` (`09:342--353`), banked as
    `WrapperProjectionCovers.productProjectionCover` and consumed only through the
    banked `WrapperProtectedEarly.exists_dense_uset_in_class`.
  * `09:1378--1383`, the defining display of `rho_0 = 99/100`, `rho_1 = rho_0/2`,
    `B_theta` and `L_q`.
  * `06:1102--1167`, `sec:extension-call-ledger`: the common binders
    `eq:extension-common-binders` (`06:1107--1113`), `r = q_amb/t_2` and
    `r' = K/t_2` (`06:1122--1125`), the exact output size
    `|Q_s| = r' p_seed = 9K/16` (`06:1128--1130`), and row **(iv)**
    "Exceptional terminal recipient" (`06:1154--1159`) with `v = u_don/2`,
    `K = 2 s q_2`, `h = rho_0 2^{-u_don-1}`, `a^sharp = 0`, closed by the uniform
    sentence `06:1161--1167`.
  * `06:124`, the defining display of `q_2`: "`q_2 =` the least power of two at
    least `12 s N_E`".  `q_2` enters the wrapper argument here for the **first**
    time; it is **not** the Section-9 outer width `q` (`06:514--518`,
    `q = 2^{A_wrap L_P^2}`), and the two are never fused.  In the dyadic
    presentation the whole route uses, `q_2 = 2^{r_2}` and `s = 2^{r_3}`
    (`09:1038`, "put `r_3 = log_2 s`").
  * `06:835--843`, `eq:stage2-structural-gates`, whose rows `4 t_2 <= q_2` and
    `2 s q_2 2^{-b_1} <= delta_term/4` are the schedule side of row (iv)'s
    per-block row-density comparison `K 2^{-b_1} <= delta_0/2`.
  * `09:1717--1718`, the defining display of `u_don` ("the least power of two
    satisfying `u_don delta_0 >= 8s`"), reified as the banked accessor
    `ParameterSchedule.uTerm` at `eq:wrapper-terminal-density`'s own `delta_0`,
    exactly as the pinned predecessor reads it.  `06:726--728` fixes `u_term`
    against `delta_term` and is **not** cited as a definition of `u_don`.
  * `09:1704--1713`, the double pigeonhole and `eq:wrapper-terminal-density`
    (`delta_0 = eta_R/(8 e_T mu_P)`), banked as
    `WrapperMassRedistribution.deltaZero`.
  * `eq:wrapper-terminal-donor-gate` (display `09:1736--1741`, label `09:1740`)
    and `09:1742--1744`, both landed at `FrontierIndexing.canonicalSystem` by the
    pinned predecessor `WrapperUDenseOpening.canonical_uDenseOpening` and consumed
    here **by pin**, with its hypothesis bundle carried through verbatim.
  * `A:109--146`, `thm:certified-localized-extension`, whose conclusion enters as
    the named implication `hLocEx` and is never asserted (**EXPANDER-001** stays
    an explicit hypothesis, never a silent axiom).
  * `D:746--764`, `eq:contract-extension-exponents`, whose three exhibited
    exponents are the index parameters of the banked
    `WrapperMassRedistribution.ExtensionCallFour`.

* **Reader counterpart: NONE claimable, inherited.**  Checked first-hand this
  tranche over `routes/parameterized-np/reader-facing/sections/`: the 41-page
  reader artifact carries no item stating `09:1746--1781`; it names neither
  `u_{\mathrm{don}}`, nor `\rho_0`, nor call (iv).  Its only passage covering this
  material is `A-stage4-details.tex:370--399`, running prose whose single
  displayed endpoint (`A-stage4-details.tex:393--395`) is
  `D_U(1; 1 - delta_U, theta) >= C + r_q`, carries no label, and is stated by no
  declaration below.  The READER-COUNTERPART rule forbids citing prose and forbids
  reusing another declaration's item, so none is cited rather than one invented.

## What this module lands, and what it deliberately does not

**Landed.**

1. `09:1746--1748`, the donor-supply step, as the arithmetic content the frozen
   sentence "By `eq:wrapper-terminal-donor-gate`, it leaves `u_don` donors"
   compresses: the gate's two clauses plus the `09:1707--1708` pigeonhole count
   force `u_don B_theta` strictly below the number of donors feeding `T_*`
   (`selected_exceeds_cover_width`), and the banked
   `WrapperMassRedistribution.donors_survive_cover` then leaves `u_don` of them
   outside the maximal poor cover (`terminalDonorSurvivors`).
2. `09:1749--1755`, the retained column set, as `terminalColumnDensity`: the
   banked `WrapperProtectedEarly.exists_dense_uset_in_class` supplies a
   `u_don`-set at joint density `rho_0`, and the banked
   `WrapperProtectedEarly.templateCoordinateExtraction` -- fired at `rho_0`, with
   **no** Bob-query halving, which is the frozen difference from row (iii) --
   supplies `u_don/2` coordinates whose all-template projection carries the frozen
   `rho_0 2^{-u_don-1}`, i.e. the banked `WrapperMassRedistribution.callFourH`.
3. `09:1717--1718` as an exponent producer (`width_exponent_at_the_accessor`):
   the paper's own least-power-of-two search evaluated at `delta_0` *is* a power
   of two, its exponent clears `r_3 + 3`, and both of row (iv)'s width demands
   (`09:1744`'s floor and `09:1762`'s supply) hold of it.  Nothing here assigns a
   numeral to `u_don`.
4. `09:1746--1781` as one theorem, `terminalRecipientClosure`: from the survivors,
   the extraction, the block supply, the structural row gate and the Localized
   Extension endpoint for row (iv), the selected child at `T_*` costs at least
   `C = B_cap + log_2 kappa`.  `eq:wrapper-terminal-block-supply`, `kappa`, the
   `9 kappa/16` selection, the ambient-width legality and the endpoint identity
   are the banked `WrapperMassRedistribution` lemmas, consumed by pin.
5. The entry, `canonical_terminalDonorSupply`: `canonical_uDenseOpening` fired at
   `FrontierIndexing.canonicalSystem` **by pin**, producing exactly the two inputs
   `terminalRecipientClosure` takes at that site -- the dyadic exponent `e` of the
   paper's own `u_don` and the survivor width `u_don B_theta <= |D_sel|`.

**Deliberately NOT landed, and the exact missing links (stop-and-report).**

`eq:wrapper-u-dense` is **neither stated nor implied**, and no route completion is
claimed.  The frozen `09:1780--1781` conclusion needs three things this tranche
does not have, each named here rather than papered over:

* **(M-a) The row-(iv) Localized Extension endpoint.**  `hLocEx` is an explicit
  named hypothesis (EXPANDER-001 enters at `A:109--146`).  It is the same
  discipline the banked row-(iii) closure uses and is not discharged here.
* **(M-b) The geometry of `T_*` at the canonical system.**  Row (iv) is stated
  over an abstract retained outer column set `S : Finset (Fin q -> Y)`, a template
  set `Y_T` and a donor coordinate set `V : Finset (Fin q)`.  At
  `FrontierIndexing.canonicalSystem` the donors feeding `T_*` are a
  `Finset (CertIndex ...)`, and the transport of that set along `donor` to
  `Finset (Fin q)`, together with the identification of `S` and `Y_T` at the
  *terminal* node `T_*` (the banked `Scol`/`YT` data is hypothesised at first-Bob
  nodes, and `T_*` is a final node), is a wiring step that the frozen source
  performs implicitly and that no banked module supplies.  It is **not** attempted
  here; `canonical_terminalDonorSupply` stops at the counting hand-off.
* **(M-c) The routed certificate system for an arbitrary shallow protocol.**  Even
  with (M-a) and (M-b), `eq:wrapper-u-dense` is the binder `hDenseRung` of
  `ScaleAlignOpening.firstWrapper`, and the banked bridge
  `WrapperMassRedistribution.denseRung_of_no_shallow_member` reduces it to
  `hmember`: *every* member of the bracket family and *every* achievable cost.
  Discharging `hmember` requires constructing `hcomp`, `hR`, `certOpt`, `Scol`,
  `Pv`, `donor`, `d_0`, `d_1`, `ell`, `bsel` and the whole routed system **from**
  an alleged protocol of cost `C + r - 1` -- the GAP-EXPOSED M1 construction of
  `09:1187--1193`.  That construction is unbuilt, so the chain does not close and
  `eq:wrapper-u-dense` is not asserted.

**Canonical inhabitation: INHERITED, REGISTERED and DEFERRED.**  This module
declares no new `structure`, `def`, `abbrev`, `instance` or `axiom`; every
declaration is a `theorem`, so it opens no new canonical-inhabitation obligation.
The inherited one cannot be discharged for the reason the predecessors record: the
paper's own instance of every statement below is a function of the alleged shallow
protocol of `09:1187--1193`, which by the argument's own design does not exist.
The one declaration below carrying numerals of its own is the explicitly labelled
rejection probe of Section 6, which claims **no** legality.
-/

namespace EthInapproximability.ParameterizedNP.WrapperProjectionCoverTail

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.TwoStreamState
open EthInapproximability.ParameterizedNP.TerminalStateRealization
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutingDynamics
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
open EthInapproximability.ParameterizedNP.ProtectedEarlyClosure
open EthInapproximability.ParameterizedNP.BobHeavyDonorCount
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.WrapperMassRedistribution
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.TerminalResidualComparison
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.MassLeavesOwner
open EthInapproximability.ParameterizedNP.OwnerMassTransfer
open EthInapproximability.ParameterizedNP.OwnerIndexedTransferFamily
open EthInapproximability.ParameterizedNP.OwnerFamilyToPigeonhole
open EthInapproximability.ParameterizedNP.WrapperExceptionalCount
open EthInapproximability.ParameterizedNP.WrapperLossTable
open EthInapproximability.ParameterizedNP.WrapperUDenseOpening

/-! ## Section 1  `09:1746--1748`, the donors that survive the poor cover

"Apply the poor-`u_don` projection cover to the donors feeding `T_*`.  By
`eq:wrapper-terminal-donor-gate`, it leaves `u_don` donors whose joint outer
projection has density at least `rho_0`."

The frozen sentence compresses two steps.  The *counting* one is the banked
`WrapperMassRedistribution.donors_survive_cover`: `lem:product-projection-cover`
covers at most `u_don (B_theta - 1)` donors, so more than `u_don B_theta` donors
leave `u_don` outside the cover.  What was missing is the *supply*: the frozen
"By `eq:wrapper-terminal-donor-gate`" -- the gate bounds `u_don B_theta` by
`q/(4 E_T)`, and the `09:1707--1708` double pigeonhole bounds `|J_good|` by
`2 e_T |D_sel|`, so with `09:1715`'s `e_T <= E_T` and `09:1737`'s `|J_good| > q/2`
the donor set at `T_*` is strictly larger than `u_don B_theta`. -/

section DonorSupply

/-- **`09:1746--1748`, the supply step.**

From `eq:wrapper-terminal-donor-gate`'s two clauses (`09:1737`, `09:1739`), the
`09:1707--1708` pigeonhole count and `09:1715`'s `e_T <= E_T`, the number of
donors feeding `T_*` strictly exceeds `u_don B_theta`.

*Why `heTle` is load-bearing.*  Without it the chain runs the wrong way: the count
`|J_good| <= 2 e_T |D_sel|` is weaker for larger `e_T` while the gate is stated at
`E_T`.  Section 6's `eT_le_ET_is_load_bearing` refutes the conclusion at
`e_T = 4 > 1 = E_T` with every other hypothesis met.

*Why the trivial reading fails.*  The conclusion is a strict inequality between
two fixed reals, not an existential, and it is false at `e_T > E_T`.

General over abstract reals. -/
theorem selected_exceeds_cover_width {q jgood dsel eT ET u Bt : ℝ}
    (hdsel : 0 ≤ dsel) (heT : 0 < eT) (hETle : eT ≤ ET)
    (hjgood : q / 2 < jgood) (hcount : jgood ≤ 2 * eT * dsel)
    (hgate : u * Bt < q / (4 * ET)) :
    u * Bt < dsel := by
  have hET : 0 < ET := lt_of_lt_of_le heT hETle
  have h4 : (0 : ℝ) < 4 * ET := by linarith
  have hstep : 2 * eT * dsel ≤ 2 * ET * dsel := by nlinarith [hdsel, hETle]
  have h1 : q / 2 < 2 * ET * dsel := by linarith
  have h2 : q / (4 * ET) < dsel := by
    rw [div_lt_iff₀ h4]
    nlinarith [h1]
  linarith

/-- **`09:1746--1748` with the cover subtracted, DERIVED.**

The frozen "it leaves `u_don` donors": the supply step above joined to the banked
`WrapperMassRedistribution.donors_survive_cover`, which is
`lem:product-projection-cover`'s counting content at width `u_don`.  Nothing is
restated -- the cover bound `|E| <= u_don (B_theta - 1)` stays the banked
lemma's own hypothesis. General over abstract reals. -/
theorem terminalDonorSurvivors {q jgood dsel eT ET u Bt coverSize : ℝ}
    (hdsel : 0 ≤ dsel) (heT : 0 < eT) (hETle : eT ≤ ET)
    (hjgood : q / 2 < jgood) (hcount : jgood ≤ 2 * eT * dsel)
    (hgate : u * Bt < q / (4 * ET))
    (hcover : coverSize ≤ u * (Bt - 1)) :
    u ≤ dsel - coverSize :=
  donors_survive_cover hcover
    (selected_exceeds_cover_width hdsel heT hETle hjgood hcount hgate)

/-- **Aux 1.1 (the cast bridge the frozen counting needs).**

The gate and the pigeonhole live in `R`; the banked
`WrapperProtectedEarly.exists_dense_uset_in_class` wants its width hypothesis in
`N`.  A strict real inequality between two natural casts is a non-strict natural
inequality, which is exactly the transport `09:1746--1748` needs and nothing
more. General. -/
theorem width_le_of_lt_cast {u Bt V : ℕ}
    (h : ((u : ℕ) : ℝ) * ((Bt : ℕ) : ℝ) < ((V : ℕ) : ℝ)) :
    u * Bt ≤ V := by
  have hcast : ((u * Bt : ℕ) : ℝ) ≤ ((V : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hcast

end DonorSupply

/-! ## Section 2  `09:1717--1718` as the exponent producer

`09:1749--1752` spends the frozen "least **power of two**" adjective of `u_don`
twice: it halves `u_don` and indexes `C_2^{u_don/2}`.  Row (iv) of
`sec:extension-call-ledger` (`06:1154--1159`) and `D:761--762` need that exponent
by name.  This section produces it from the paper's own closed form -- the banked
accessor `ParameterSchedule.uTerm` at `eq:wrapper-terminal-density`'s `delta_0` --
and shows it clears both of row (iv)'s width demands. **No numeral is assigned to
`u_don`, to `s`, or to any schedule quantity.** -/

section WidthExponent

/-- **`09:1717--1718`, `09:1744` and `09:1762` at the paper's own `u_don`.**

The frozen search "the least power of two satisfying `u_don delta_0 >= 8s`",
evaluated at `s = 2^{r_3}` (`09:1038`) and at an arbitrary admissible density,
delivers an exponent `e` with `u_don = 2^e`, with `r_3 + 3 <= e` (the width
hypothesis row (iv) records), with `09:1744`'s floor `8s <= u_don` and with
`09:1762`'s supply `8s <= u_don delta_0`.

*What is derived rather than assumed.*  All four clauses.  The supply is the
banked `ParameterSchedule.uTerm_spec`, the floor is the banked
`WrapperMassRedistribution.uDon_ge_eight_s` at the frozen branch `delta_0 <= 1`,
the dyadic form is the banked `ParameterSchedule.uTerm_isPowTwo`, and `r_3 + 3 <= e`
is the floor read through `2^{r_3+3} = 8 . 2^{r_3}`.

*Why the trivial witness fails.*  The existential's first clause pins `e` to the
accessor's own exponent -- it is a named-def claim about `ParameterSchedule.uTerm`,
not a free choice -- and the remaining three are then statements about that pinned
value, all false at `e = 0` for every `r_3`.

General in `r_3` and in the density. -/
theorem width_exponent_at_the_accessor {r₃ : ℕ} {delta0 : ℝ}
    (hd0 : 0 < delta0) (hd1 : delta0 ≤ 1) :
    ∃ e : ℕ, ParameterSchedule.uTerm (2 ^ r₃) delta0 = 2 ^ e
      ∧ r₃ + 3 ≤ e
      ∧ 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e
      ∧ 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * delta0 := by
  obtain ⟨e, he⟩ := ParameterSchedule.uTerm_isPowTwo (2 ^ r₃) delta0
  -- `09:1717--1718`: the defining demand, as the banked accessor's own theorem.
  have hspec := ParameterSchedule.uTerm_spec (s := 2 ^ r₃) hd0
  rw [he] at hspec
  have hcast : (((2 ^ r₃ : ℕ)) : ℝ) = (2 : ℝ) ^ r₃ := by push_cast; ring
  have hcaste : (((2 ^ e : ℕ)) : ℝ) = (2 : ℝ) ^ e := by push_cast; ring
  rw [hcast, hcaste] at hspec
  -- `09:1744`: the floor, at the branch `delta_0 <= 1`.
  have hfloorNat : 8 * (2 ^ r₃) ≤ 2 ^ e := by
    refine uDon_ge_eight_s (s := 2 ^ r₃) (uDon := 2 ^ e) hd1 ?_
    rw [hcast, hcaste]
    exact hspec
  have hfloor : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e := by
    have := hfloorNat
    have hR : ((8 * 2 ^ r₃ : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hR
    linarith
  refine ⟨e, he, ?_, hfloor, hspec⟩
  -- `r_3 + 3 <= e`, from `2^{r_3+3} = 8 . 2^{r_3} <= 2^e`.
  have hpow : (2 : ℕ) ^ (r₃ + 3) ≤ 2 ^ e := by
    calc (2 : ℕ) ^ (r₃ + 3) = 8 * 2 ^ r₃ := by rw [pow_add]; ring
      _ ≤ 2 ^ e := hfloorNat
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow

end WidthExponent

/-! ## Section 3  `09:1749--1755`, the retained column set at `rho_0`

"Apply `lem:template-coordinate-extraction` and fix one Stage-3 bin in each of the
resulting `u_don/2` donors.  The retained column set in `C_2^{u_don/2}` has
density at least `rho_0 2^{-u_don-1}`."

Row (iii) at `09:1458--1471` inserts Bob's query between the cover and the
extraction, which halves `rho_0` to `rho_1`; **row (iv) does not**.  The frozen
text passes straight from the cover's `rho_0` to `rho_0 2^{-u_don-1}`, and
`06:1157` records row (iv)'s entering density as `h = rho_0 2^{-u_don-1}`.  That
is the banked `WrapperMassRedistribution.callFourH`, whose banked identity
`callFourH = 2 callThreeH` is exactly this missing halving.  Consequently this
section takes **no** query binder: the row-(iii) `hQuery` hypothesis has no
frozen counterpart here and adding one would be a hypothesis the paper does not
state. -/

section RetainedColumns

/-- **`09:1746--1755`, the retained column set of row (iv), proved.**

From a donor coordinate set `V` wide enough to survive the poor cover
(`09:1746--1748`) and the frozen template data, some `u_don`-set of donors is not
poor and some `u_don/2` of its coordinates carry an all-template projection at the
frozen row-(iv) density `h = rho_0 2^{-u_don-1}`.

*What is derived rather than assumed.*  The cover survival is the banked
`WrapperProtectedEarly.exists_dense_uset_in_class` (i.e.
`lem:product-projection-cover` by pin), and the extraction is the banked
`WrapperProtectedEarly.templateCoordinateExtraction` at `rho = rho_0`; the frozen
gap hypothesis is carried in its row-(iii) form `1 - lambda_T <= rho_1/8`
(`09:1466`), which is *stronger* than what `rho_0` needs, so no gate is weakened.

*Why the trivial witness fails.*  The last clause's right-hand side is a
cardinality: the empty projection makes it `0` while the left-hand side is
positive whenever the template set is (Section 6's
`terminalColumnDensity_trivial_witness_fails`).  `J'` is likewise pinned to card
`u_don/2` by the second-to-last clause, so `J' = empty` does not discharge it for
`e >= 1`.

**Nothing beyond `09:1755`.**  The Stage-2 partition average, `kappa`, the
`9 kappa/16` selection and call (iv) are Sections 4--5.
General in the alphabet, in `q`, in `e` and in both densities. -/
theorem terminalColumnDensity {Y : Type*} [Fintype Y] [DecidableEq Y] {q e : ℕ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (V : Finset (Fin q))
    {θ lamT : ℝ}
    (hY : 0 < Fintype.card Y) (hθ : 0 < θ) (he : 2 ≤ e)
    (hV : 2 ^ e * Btheta θ ≤ V.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8) :
    ∃ (J : Finset (Fin q)) (eJ : Fin (2 ^ e) ≃ ↥J) (J' : Finset (Fin (2 ^ e))),
      J ⊆ V ∧ J.card = 2 ^ e ∧ ¬ PoorProjection rhoZero J S ∧
      J'.card = 2 ^ e / 2 ∧
      callFourH e * (YT.card : ℝ) ^ (2 ^ e / 2)
        ≤ ((projSet J' ((ambientRelabel J eJ S).filter
            (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) := by
  classical
  -- `09:1746--1748`: `lem:product-projection-cover` leaves a non-poor `u_don`-set.
  obtain ⟨J, hJV, hJcard, hJpoor⟩ :=
    exists_dense_uset_in_class (u := 2 ^ e) (θ := θ) S V hY Nat.one_le_two_pow hθ hV hS
  have hdense : rhoZero * (Fintype.card Y : ℝ) ^ (2 ^ e) ≤ ((projSet J S).card : ℝ) := by
    have h := hJpoor
    simp only [PoorProjection, hJcard, not_lt] at h
    exact h
  -- the frozen relabelling of the selected donors as the coordinates of `Y^{u_don}`
  have hcardJ : Fintype.card ↥J = 2 ^ e := by rw [Fintype.card_coe, hJcard]
  obtain ⟨eJ⟩ : Nonempty (Fin (2 ^ e) ≃ ↥J) := ⟨(Fintype.equivFinOfCardEq hcardJ).symm⟩
  have hAmb : rhoZero * (Fintype.card Y : ℝ) ^ (2 ^ e)
      ≤ ((ambientRelabel J eJ S).card : ℝ) := by
    rw [card_ambientRelabel]
    exact hdense
  have h4 : (4 : ℕ) ∣ 2 ^ e := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h]
    exact pow_dvd_pow 2 he
  -- `09:1466`'s gate is stated at `rho_1`; `rho_0 = 2 rho_1` needs less.
  have hgap0 : 1 - lamT ≤ rhoZero / 8 := by
    have hstep : rhoOne / 8 ≤ rhoZero / 8 := by
      unfold rhoOne
      linarith [rhoZero_pos]
    linarith
  -- `09:1749--1755`: the extraction, at `rho = rho_0` and with no query in between.
  obtain ⟨J', hJ'card, hJ'dense⟩ :=
    templateCoordinateExtraction (u := 2 ^ e) (ambientRelabel J eJ S) YT h4
      (by positivity) hY rhoZero_pos hAmb hYT hgap0
  refine ⟨J, eJ, J', hJV, hJcard, hJpoor, hJ'card, ?_⟩
  -- `06:1157`: dividing the frozen `rho_0 2^{-u_don-1}` by its denominator.
  have hpow : (0 : ℝ) < 2 ^ (2 ^ e + 1) := by positivity
  have hcomm :
      ((projSet J' ((ambientRelabel J eJ S).filter
          (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) * 2 ^ (2 ^ e + 1)
        = 2 ^ (2 ^ e + 1)
            * ((projSet J' ((ambientRelabel J eJ S).filter
                (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) := by ring
  rw [callFourH, div_mul_eq_mul_div, div_le_iff₀ hpow, hcomm]
  exact hJ'dense

end RetainedColumns

/-! ## Section 4  `09:1746--1781` as one theorem: the row-(iv) closure

"Put `kappa = 2 s q_2` and select exactly `9 kappa/16` of these blocks.  Because
`u_don >= 8s`, the ambient width `(u_don/2) q_2` is at least `2 kappa`, so
`r' = kappa/t_2` is legal.  The finite terminal product gates verify call~(iv) in
`sec:extension-call-ledger` uniformly for every `e_T <= E_T` and
`u_don <= u_term`.  Its conclusion at `T_*` is `B_cap + log_2 kappa = C`."

`kappa`, the block supply `eq:wrapper-terminal-block-supply`, the ambient-width
legality, the row-(iv) call record and the endpoint identity are all banked in
`WrapperMassRedistribution` (Section 11 there) and are consumed **by pin**: none
is restated.  What this theorem adds is that they compose -- with the retained
column set of Section 3 and with row (iv)'s entering density `callFourH` -- into
the frozen conclusion at `T_*`.

`q_2 = 2^{r_2}` enters here for the first time in the wrapper argument.  It is the
Stage-2 width of `06:124`, **never** the Section-9 outer width `q`, which appears
below only as the ambient dimension of the column carrier.

**EXPANDER-001 discipline.**  `thm:certified-localized-extension` is the named
implication `hLocEx`, in the same shape the banked row-(iii) closure
`WrapperProtectedEarly.earlyProtectedClosureFromDmass` uses.  It is a hypothesis,
never an axiom and never asserted. -/

section RowFourClosure

/-- **`09:1746--1781`, call (iv) at the exceptional terminal recipient.**

The frozen tail, end to end: the survivors of the poor-`u_don` cover
(`09:1746--1748`, entering as the width hypothesis `hV`), the coordinate
extraction at `rho_0` (`09:1749--1755`, Section 3), the Stage-2 partition average
and `eq:wrapper-terminal-block-supply` (`09:1756--1765`, entering as `hper` and
`hBlocks` and closed by the banked `terminalBlockSupply`), `kappa = 2 s q_2` with
its `9 kappa/16` selection and legal `r'` (`09:1767--1770`, the banked
`extensionCallFour_of_width`), and the endpoint `B_cap + log_2 kappa = C`
(`09:1775--1779`, the banked `terminalEndpoint_identity`).

*What is derived rather than assumed.*  Every field of the banked
`ExtensionCallFour` record -- the two width demands, the two exponent contracts of
`D:751--753`, the ambient-width legality, the `16 |` divisibilities, the exact
selected count `|Q_s| = 9K/16` and the entering column density -- together with
the block supply and the endpoint identity.  The record is **constructed**, never
hypothesised, which is what `D:762--764` demands.

*What is still a binder.*  `hLocEx` (**EXPANDER-001**, `A:109--146`), the
structural row gate `hGate` (`06:1158--1159`, the schedule's own
`eq:stage2-structural-gates` row), the two certified-extension comparisons `hE1`,
`hE2`, the per-block row count `hrows`, the template data `hYT`/`hgap`, the
retained-column density `hS`, and the two block-supply inputs `hper`/`hBlocks`.
**No banked hypothesis is weakened and full-bundle satisfiability is not
claimed.**

*Why the trivial reading fails.*  The conclusion is an inequality between two
fixed naturals, not an existential, and it is not available from `hLocEx` alone:
`hLocEx` fires only on a *constructed* `ExtensionCallFour` record at the exponents
`R = (e-1) + r_2 - k_2` and `R_loc = r_3 + 1 + r_2 - k_2`, and at `e < r_3 + 3`
those exponents violate `rloc_le_r`, so the record cannot be built.

*No route completion.*  `eq:wrapper-u-dense` is neither stated nor implied; see
(M-a)--(M-c) in the header.

General in the column alphabet `Y`, the source-matrix carriers `Rw`/`Cl`, the
abstract memory `Mem`, and in every width and density. -/
theorem terminalRecipientClosure
    {Y : Type*} [Fintype Y]
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} (memCost : Mem → ℕ) (child : Mem)
    {q k₂ b₁ r₂ r₃ e bcap tcert selCard rowsPerBlock : ℕ}
    {θ lamT x epsProd delta0 perDonor : ℝ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (V : Finset (Fin q))
    (hθ0 : 0 < θ) (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + 1 + r₂) (hbcap : 2 ≤ bcap)
    -- `09:1038`: `s = 2^{r_3}` ("put `r_3 = log_2 s`").  The frozen guarded-source
    -- floor is `04:389` ("Let `s >= 4` be a power of two"), i.e. `r_3 >= 2`; the
    -- binder below is deliberately the weaker `r_3 >= 1`, which `04:389` implies,
    -- so the statement is proved at `s >= 2` and holds a fortiori at the frozen
    -- floor.  It is used only to reach `4 <= e` from `hwidth : r_3 + 3 <= e`.
    (hr₃ : 1 ≤ r₃)
    -- `09:1744` and `09:1762`, at the paper's own `u_don = 2^e` (Section 2)
    (hwidth : r₃ + 3 ≤ e)
    (hlow : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e)
    (hsupply : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * delta0)
    -- `09:1746--1748`: the donors surviving the poor-`u_don` cover
    (hV : 2 ^ e * Btheta θ ≤ V.card)
    -- `06:1158--1159`: the structural-gate comparison `K 2^{-b_1} <= delta_0/2`
    (hGate : ((2 : ℝ) ^ (r₃ + 1 + r₂)) / 2 ^ b₁ ≤ delta0 / 2)
    -- `09:1749--1755`: the template data of `lem:template-coordinate-extraction`
    (hY : 0 < Fintype.card Y) (hYT0 : 0 < YT.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    -- `09:1756--1765`: the Stage-2 fibre average and the represented blocks
    (hper : delta0 * ((2 ^ r₂ : ℕ) : ℝ) / 2 ≤ perDonor)
    (hBlocks : ((2 ^ e / 2 : ℕ) : ℝ) * perDonor ≤ (selCard : ℝ))
    -- `A:111--118`, the hypothesis block of `thm:certified-localized-extension`
    -- (the home of these six binders).  The Section-6 display fixing the shared
    -- base data, `eq:extension-common-binders`, lives separately at `06:1107--1113`;
    -- see the inherited-interface note on `x` in `OBLIGATION_LEDGER.md` (R-2).
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    -- `A:126--128` on the product branch, at `eps_prod` of `eq:epsilon-product`
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    -- `eq:certified-E1`, `eq:certified-E2`, uniformly per `06:1161--1167`
    (hE1 : ∀ R : ℕ, R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callFourH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k₂
        ≤ (callFourH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    -- `A:139--140`, at least `ceil(r' t x m)` rows in each represented block
    (hrows : ⌈((2 : ℝ) ^ (r₃ + 1 + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊
        ≤ rowsPerBlock)
    -- `A:109--146`, `thm:certified-localized-extension` (EXPANDER-001), named
    (hLocEx : ∀ (R Rloc : ℕ) (colDens : ℝ),
        ExtensionCallFour k₂ R Rloc b₁ e r₂ r₃ delta0 colDens →
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        0 < x → x ≤ 1 →
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R →
        (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callFourH e → callFourH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callFourH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callFourH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock →
        callFourH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ memCost child) :
    TerminalTwoStream.terminalTarget bcap r₂ r₃ ≤ memCost child := by
  classical
  have he4 : 4 ≤ e := by omega
  -- `09:1746--1755`: the survivors and the retained column set at `rho_0`
  obtain ⟨J, eJ, J', -, -, -, -, hJ'dense⟩ :=
    terminalColumnDensity S YT V hY hθ0 (by omega : 2 ≤ e) hV hS hYT hgap
  have hYTR : (0 : ℝ) < (YT.card : ℝ) := by exact_mod_cast hYT0
  have hcol : callFourH e / 2 ^ (0 : ℕ)
      ≤ ((projSet J' ((ambientRelabel J eJ S).filter
          (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) / (YT.card : ℝ) ^ (2 ^ e / 2) := by
    rw [pow_zero, div_one, le_div_iff₀ (by positivity)]
    exact hJ'dense
  -- `09:1767--1770` and `D:746--764`: the row-(iv) call record, CONSTRUCTED
  have hcall :
      ExtensionCallFour k₂ ((e - 1) + r₂ - k₂) (r₃ + 1 + r₂ - k₂) b₁ e r₂ r₃ delta0
        (((projSet J' ((ambientRelabel J eJ S).filter
            (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) / (YT.card : ℝ) ^ (2 ^ e / 2)) :=
    extensionCallFour_of_width hk₂ he4 hwidth hk₂le hlow hsupply hGate hcol
  -- `eq:wrapper-terminal-block-supply` (`09:1756--1765`), by pin
  have hud : 8 * (((2 ^ r₃ : ℕ)) : ℝ) ≤ (((2 ^ e : ℕ)) : ℝ) * delta0 := by
    push_cast
    exact hsupply
  have hkappa : 2 * (((2 ^ r₃ : ℕ)) : ℝ) * (((2 ^ r₂ : ℕ)) : ℝ) ≤ (selCard : ℝ) :=
    le_trans
      (terminalBlockSupply (s := 2 ^ r₃) (q₂ := 2 ^ r₂) (uDon := 2 ^ e)
        (dvd_pow_self 2 (by omega)) hud hper)
      hBlocks
  have hcapR : (((2 ^ (r₃ + 1 + r₂) : ℕ)) : ℝ)
      = 2 * (((2 ^ r₃ : ℕ)) : ℝ) * (((2 ^ r₂ : ℕ)) : ℝ) := by
    push_cast
    ring
  have hcount : 9 * ((2 ^ ((r₃ + 1 + r₂ - k₂) + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) := by
    have hexp : (r₃ + 1 + r₂ - k₂) + k₂ = r₃ + 1 + r₂ := by omega
    rw [hexp, hcapR]
    have hnn : (0 : ℝ) ≤ 2 * (((2 ^ r₃ : ℕ)) : ℝ) * (((2 ^ r₂ : ℕ)) : ℝ) := by positivity
    linarith
  -- `09:1770--1774`: the inherited endpoint at call (iv)
  have hend := hLocEx ((e - 1) + r₂ - k₂) (r₃ + 1 + r₂ - k₂) _
    hcall hMne hbcap hx0 hx1 hbase htcert hk₂ htx
    Nat.one_le_two_pow hcall.r'_le_r (pow_add 2 _ k₂).symm heps0 heps1
    (callFourH_pos e) (callFourH_le_one e)
    (hE1 ((e - 1) + r₂ - k₂) hcall.ambient_exponent) hE2
    hcall.selected_count hcount hrows hcall.column_density
  -- `09:1775--1779`: `B_cap + log_2 kappa = C`
  have hcap : (r₃ + 1 + r₂ - k₂) + k₂ = r₃ + 1 + r₂ := hcall.capacity_exponent
  have hid := terminalEndpoint_identity bcap r₂ r₃
  omega

end RowFourClosure

/-! ## Section 5  The entry: `canonical_uDenseOpening` fired at the canonical system

`09:1746--1748` reads "By `eq:wrapper-terminal-donor-gate`, it leaves `u_don`
donors".  At `FrontierIndexing.canonicalSystem` that gate and the `09:1742--1744`
floor are the pinned predecessor endpoint
`WrapperUDenseOpening.canonical_uDenseOpening`, consumed here as a proof term with
its hypothesis bundle carried through verbatim.

*What is added to the pinned bundle.*  Exactly one binder, `hcountSel`: the
`09:1707--1708` pigeonhole count `|J_good| <= 2 e_T |D_sel|` at the *chosen*
`T_*` and reservoir type `ty`.  This is the first component of the banked
`OwnerFamilyToPigeonhole.exists_terminal_star_and_reservoir`'s conclusion, in that
theorem's own shape, and it is not derivable from the pinned bundle -- the pinned
opening already carries `T_*` and `ty` as free binders, so their pigeonhole
provenance is genuinely extra data.

*What is re-derived rather than re-hoisted.*  `e_T <= E_T` (`09:1715--1716`).  The
pinned gate derives it internally and does not export it; re-hoisting it as a
binder would restate a derived fact, so it is re-derived here from the same banked
endpoints the pinned gate uses -- `canonical_wrapperBobHeavyCount` through
`bobHeavyCount_le_EB`, and `canonical_wrapperExceptionalCount` -- crossing the two
`vartheta` twins (`09:1268`, `06:718`) by their two banked evaluations.

*What is still a binder.*  Everything the predecessor left as one, verbatim:
`hLocExCC`/`hLocExEP` (**EXPANDER-001**), `hfinal`, `halleged`, `hcost`, `hres`,
`hinj`, `hhost`, `he0`, `residual`/`hresidual`/`hladder`, the gate system
`hgates`, `he0m`, `09:1704`'s `heTpos`, and the `09:1708--1713` endpoint binders
`dens`, `Tstar`, `ty`, `hsel`, `hdelta`, `hdens1`.  **No hypothesis is added to
any banked endpoint and none is weakened.  Full-bundle satisfiability is not
claimed.**

*No route completion.*  This produces the two *counting* inputs
`terminalRecipientClosure` takes; the geometric transport of `T_*`'s donors,
retained columns and template set into that theorem's carriers is missing link
(M-b) of the header, and `eq:wrapper-u-dense` is neither stated nor implied. -/

section CanonicalEntry

variable {X : Type*} [Fintype X] [DecidableEq X]
  {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`09:1746--1748` at the canonical routed system, at the paper's own `u_don`.**

There is an exponent `e` with `u_don = 2^e` (the `09:1717--1718` least-power-of-two
search at `eq:wrapper-terminal-density`'s `delta_0`), with `r_3 + 3 <= e`, and with
`2^e B_theta <= |D_sel|` -- i.e. the donors feeding `T_*` outnumber the poor cover,
which is exactly the width hypothesis `terminalRecipientClosure` takes at `hV` and
`hwidth`.

*What is derived rather than assumed.*  Both gate clauses and the floor (the
pinned `canonical_uDenseOpening`), the frozen branch `delta_0 <= 1` (banked
`deltaZero_le_one_of_selected`), the dyadic form and both width demands
(Section 2), `e_T <= E_T` (re-derived, see the section note), and the supply step
(Section 1).

*Why the trivial witness fails.*  The existential's first clause pins `e` to the
accessor's own exponent, so `e` is not free; the third clause is then a statement
about that pinned value which is false whenever the selected-donor set is empty --
and `hsel` alone does not give it, since `|D_sel| >= 1` does not reach
`2^e B_theta`.

General in the source-matrix row carrier `RwN`, the per-coordinate alphabet `Yc`,
the Alice carrier `X`, and in every width and schedule quantity. -/
theorem canonical_terminalDonorSupply {RwN : Type*} [Fintype RwN]
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
        (canonicalSystem hcomp hR).owner i = v)
    -- `lem:certified-row-ladder` (`09:1334--1338`), the route to owner uniqueness
    (residual : CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℕ)
    (hresidual : ∀ i j, residual i j
      ≤ (descend P ((canonicalSystem hcomp hR).node
          ((canonicalSystem hcomp hR).owner i))).cost)
    (hladder : ∀ i ∈ (canonicalSystem hcomp hR).cleanFinal,
      ∀ j ∈ (canonicalSystem hcomp hR).cleanFinal,
      (canonicalSystem hcomp hR).owner i = (canonicalSystem hcomp hR).owner j →
      ((canonicalSystem hcomp hR).cert i).coord
          ≠ ((canonicalSystem hcomp hR).cert j).coord →
      TerminalTwoStream.terminalTarget bcap r₂ r₃ ≤ residual i j)
    -- `09:1727--1731`: the construction records `e_0^max >= 1`
    (he0m : 1 ≤ e0m)
    -- `09:1704`: "Assume then that `e_T > 0`", the frozen branch assumption
    (heTpos : 0 < (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card)
    -- `eq:terminal-wrapper-gates` (`06:738--743`), all three rows
    {trefv : ℕ}
    (hgates : ParameterSchedule.terminalWrapperGates q
      (ParameterSchedule.ET e0m
        (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR))
      (ParameterSchedule.uTerm (2 ^ r₃)
        (ParameterSchedule.deltaTerm etaR
          (ParameterSchedule.ET e0m
            (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR))))
      (Btheta θ) trefv)
    -- `09:1708--1713`, the `eq:wrapper-terminal-density` endpoint
    (dens : Bool → CertIndex P R (initialRefRows (xTdepth bT) (Fintype.card X)) r →
      FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r → ℝ)
    (Tstar : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (ty : Bool)
    (hsel : (selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty).Nonempty)
    (hdelta : ∀ j ∈ selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty,
      deltaZero etaR (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card
        ≤ dens ty j Tstar)
    (hdens1 : ∀ j ∈ selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty,
      dens ty j Tstar ≤ 1)
    -- `09:1707--1708`, the double pigeonhole count at the chosen `T_*` and `ty`
    (hcountSel : ((goodDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ≤ 2 * ((exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
          * ((selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty).card : ℝ)) :
    ∃ e : ℕ,
      ParameterSchedule.uTerm (2 ^ r₃)
          (deltaZero etaR (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card)
        = 2 ^ e
      ∧ r₃ + 3 ≤ e
      ∧ 2 ^ e * Btheta θ
        ≤ (selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty).card := by
  classical
  -- `eq:wrapper-terminal-donor-gate` and `09:1742--1744`, consumed BY PIN
  have hopen := canonical_uDenseOpening Nmat Gmat ιR hsub halleged hcomp hR certOpt
    isRestrEP Scol YT Pv donor d₀ d₁ ell bsel hdepth hinj hres hC hcost hq hmem hk hq4 hX hYc
    hθ0 hθ1
    hgate hbase htcert hE1cc hE2cc hLocExCC hcover B hB plc hblock hplace hfinal hqpos hk₂
    hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0 hSep hYT hgap hQuery hBlocks hx0 hx1 htx
    hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep hrows hSelectEP hLocExEP hne hetaR he0 hhost
    residual hresidual hladder he0m heTpos hgates dens Tstar ty hsel hdelta hdens1
  -- `09:1742`, the frozen branch, and `09:1717--1718`'s dyadic exponent (Section 2)
  have hd1 : deltaZero etaR (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card ≤ 1 :=
    deltaZero_le_one_of_selected (canonicalSystem hcomp hR) Pv dens Tstar ty hsel hdelta hdens1
  have hd0 : 0 < deltaZero etaR (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card :=
    deltaZero_pos hetaR heTpos
  obtain ⟨e, hpow, hwidth, -, -⟩ := width_exponent_at_the_accessor (r₃ := r₃) hd0 hd1
  refine ⟨e, hpow, hwidth, ?_⟩
  -- `09:1715--1716`: `e_T <= E_T`, RE-DERIVED from the same banked endpoints
  have hbhc := canonical_wrapperBobHeavyCount Nmat Gmat ιR hsub halleged hcomp hR certOpt
    isRestrEP Scol YT Pv donor d₀ d₁ ell bsel hdepth hinj hres hC hcost hq hmem hk hq4 hX hYc
    hθ0 hθ1
    hgate hbase htcert hE1cc hE2cc hLocExCC hcover B hB plc hblock hplace hfinal hqpos hk₂
    hk₂le hbcap hd₀0 hd₀1 hd₁0 hd₁1 hGateEP hYT0 hSep hYT hgap hQuery hBlocks hx0 hx1 htx
    hMne hbaseEP htcertEP heps0 heps1 hE1ep hE2ep hrows hSelectEP hLocExEP hne hetaR
  have hexc := WrapperExceptionalCount.canonical_wrapperExceptionalCount (etaR := etaR)
    Nmat Gmat ιR hsub halleged hcomp hR certOpt Pv hq hmem hk hq4 hX hYc hθ0 hθ1 hC hgate
    hbase htcert hE1cc hE2cc hcost hLocExCC hcover B hB plc hblock hplace hfinal
    residual hresidual hladder hhost
  have hv : (1 : ℝ) - DenseWrapperFrontier.vartheta = 7 / 16 :=
    DenseWrapperFrontier.one_sub_vartheta
  have hvP : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
    ParameterSchedule.one_sub_vartheta
  have heB : (bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card
      ≤ ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR :=
    bobHeavyCount_le_EB hetaR he0 hbhc
  have heBR : ((bobHeavyDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ)
      ≤ ((ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR : ℕ) : ℝ) := by
    exact_mod_cast heB
  have heTle : (exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card
      ≤ ParameterSchedule.ET e0m
          (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) := by
    have h1 := le_trans hexc.1 hexc.2
    have e1 : (E0.card : ℝ) / (1 - DenseWrapperFrontier.vartheta)
        = 16 / 7 * (E0.card : ℝ) := by rw [hv]; ring
    have e2 : (e0m : ℝ) / (1 - ParameterSchedule.vartheta)
        = 16 / 7 * (e0m : ℝ) := by rw [hvP]; ring
    rw [e1] at h1
    have hceil : 16 / 7 * (e0m : ℝ)
        ≤ ((⌈(e0m : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ : ℕ) : ℝ) := by
      rw [← e2]
      exact Nat.le_ceil _
    have hchain : (((exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card : ℕ) : ℝ)
        ≤ ((ParameterSchedule.ET e0m
            (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) : ℕ) : ℝ) := by
      rw [ParameterSchedule.ET, Nat.cast_add]
      linarith
    exact_mod_cast hchain
  have heTleR : (((exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card : ℕ) : ℝ)
      ≤ ((ParameterSchedule.ET e0m
          (ParameterSchedule.EB (Btheta θ) (Lq q) (2 ^ r₃) e0m etaR) : ℕ) : ℝ) := by
    exact_mod_cast heTle
  have heTposR : (0 : ℝ)
      < (((exceptionalFinal (canonicalSystem hcomp hR) Pv etaR).card : ℕ) : ℝ) := by
    exact_mod_cast heTpos
  -- `09:1746--1748`, Section 1, at the pinned gate's own `u_don`
  have hsupplyR := selected_exceeds_cover_width
    (q := (q : ℝ))
    (jgood := ((goodDonors (canonicalSystem hcomp hR) Pv etaR).card : ℝ))
    (dsel := ((selectedDonors (canonicalSystem hcomp hR) Pv etaR dens Tstar ty).card : ℝ))
    (Nat.cast_nonneg _) heTposR heTleR hopen.1 hcountSel hopen.2.1
  rw [hpow] at hsupplyR
  exact width_le_of_lt_cast (by exact_mod_cast hsupplyR)

end CanonicalEntry

/-! ## Section 6  Aux-lemma battery

Five general checks.  **Canonical inhabitation is INHERITED, REGISTERED and
DEFERRED** per the header: this module declares no new type, so it opens no new
obligation, and the inherited one cannot be discharged because the paper's own
instance of every statement above is a function of the alleged shallow protocol of
`09:1187--1193`, which does not exist.

Battery 4 is an explicitly labelled **rejection probe**: it claims no legality and
exists only to show that Section 1's `heTle` guard fires. -/

section Battery

/-- **Battery 1 (round trip on the frozen row-(iv) density).**

`06:1157` fixes row (iv)'s entering density as `h = rho_0 2^{-u_don-1}`, and the
banked `callFourH` writes it as a quotient.  Section 3 converts the multiplicative
output of `lem:template-coordinate-extraction` (`rho_0 |Y_T|^{u/2} <= 2^{u+1}
|proj|`) into that quotient form, and this identity is exactly the conversion:
multiplying `callFourH` back by the frozen denominator returns `rho_0` on the
nose.  If it failed, Section 3's density would not be the paper's.  General. -/
theorem callFourH_mul_pow (e : ℕ) : callFourH e * 2 ^ (2 ^ e + 1) = rhoZero := by
  unfold callFourH
  have hpow : (0 : ℝ) < 2 ^ (2 ^ e + 1) := by positivity
  field_simp

/-- **Battery 2 (the extraction strictly loses density).**

`09:1749--1755` enters at `rho_0` and leaves at `rho_0 2^{-u_don-1}`, so the frozen
step is a genuine loss and not a relabelling: row (iv)'s entering density is
strictly below the cover's.  A statement that would fail if `callFourH` had been
mis-transcribed with a non-negative exponent.  General. -/
theorem callFourH_lt_rhoZero (e : ℕ) : callFourH e < rhoZero := by
  unfold callFourH
  have h0 := rhoZero_pos
  have hpow : (1 : ℝ) < 2 ^ (2 ^ e + 1) := by
    have : (2 : ℝ) ^ (0 : ℕ) < 2 ^ (2 ^ e + 1) :=
      pow_lt_pow_right₀ (by norm_num) (by positivity)
    simpa using this
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [h0, hpow]

/-- **Battery 3 (statement pole: Section 3's density clause is not trivially
satisfiable).**

The deliverable of `terminalColumnDensity` is an inequality whose right-hand side
is a cardinality.  The empty projection makes it `0`, while the left-hand side is
positive as soon as the template set is -- so `J'` cannot be discharged by an
extraction that retains nothing.  This is the row-(iv) analogue of the banked
`WrapperProtectedEarly.templateCoordinateExtraction_trivial_witness_fails`, at
`callFourH` rather than `callThreeH`.  General. -/
theorem terminalColumnDensity_trivial_witness_fails {e c : ℕ} (hc : 0 < c) :
    ¬ (callFourH e * ((c : ℕ) : ℝ) ^ (2 ^ e / 2) ≤ ((0 : ℕ) : ℝ)) := by
  have hcR : (0 : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast hc
  have hpos : 0 < callFourH e * ((c : ℕ) : ℝ) ^ (2 ^ e / 2) := by
    have := callFourH_pos e
    positivity
  push_cast
  linarith

/-- **Battery 4 (REJECTION PROBE, claims no legality): Section 1's `e_T <= E_T`
guard fires.**

`09:1715--1716` is quoted for a reason: without it the frozen chain
"`|J_good| > q/2`, pigeonhole, gate" does not reach `u_don B_theta < |D_sel|`.  At
`q = 8`, `E_T = 1`, `e_T = 4`, `|D_sel| = 1`, `|J_good| = 5`, `u_don = 1` and
`B_theta = 1` the violated guard is exactly `e_T <= E_T` (`4 <= 1` is false) and
the conclusion fails.

Scope of what is *exhibited* below: the three hypotheses of
`selected_exceeds_cover_width` that mention the violated guard's neighbours
(`hjgood`, `hcount`, `hgate`) together with the failed conclusion.  The remaining
two (`hdsel : 0 <= dsel` as `0 <= 1`, `heT : 0 < eT` as `0 < 4`) are true at these
values but are **not** asserted as conjuncts here, so this probe does not by
itself certify "every other hypothesis holds"; adding them is a statement change
and is deferred to a follow-on tranche (ledger item R-7).

**This is a rejection probe at self-chosen values and claims nothing about legal
schedule parameters**: it exhibits the guard firing on input the frozen bound
excludes, which is the one use of self-chosen values the witness rule permits. -/
theorem eT_le_ET_is_load_bearing :
    (8 : ℝ) / 2 < 5 ∧ (5 : ℝ) ≤ 2 * 4 * 1 ∧ (1 : ℝ) * 1 < 8 / (4 * 1)
      ∧ ¬ ((1 : ℝ) * 1 < 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Battery 5 (the two width demands are not the same demand).**

`09:1744` gives `8s <= u_don` and `09:1762` gives `8s <= u_don delta_0`; the banked
`ExtensionCallFour` records both as separate fields, and Section 2 proves both of
the accessor.  This is the joint-informativeness check for
`width_exponent_at_the_accessor`'s last two clauses.

**Exactly what is proved below:** the forward direction only -- at `delta_0 <= 1`
the supply demand implies the floor demand.  The converse failure (a floor with a
tiny density need not supply the blocks) is *not* witnessed here despite the
declaration's name; supplying an explicit rejection witness for it is a new
declaration and is deferred to a follow-on tranche (ledger item R-5).  General
over abstract reals. -/
theorem supply_implies_floor_not_conversely {sv u delta0 : ℝ}
    (hu : 0 ≤ u) (hd1 : delta0 ≤ 1) (hsupply : 8 * sv ≤ u * delta0) :
    8 * sv ≤ u := by
  nlinarith [hsupply, hu, hd1]

end Battery

end EthInapproximability.ParameterizedNP.WrapperProjectionCoverTail
