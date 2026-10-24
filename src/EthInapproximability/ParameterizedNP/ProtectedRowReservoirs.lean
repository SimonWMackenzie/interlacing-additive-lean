import EthInapproximability.ParameterizedNP.RetentionSupply
import EthInapproximability.ParameterizedNP.ProtectedEarlyClosure

/-!
# Parameterized NP route: the protected row reservoirs and `P_v(J_0)`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche).
* **The exact frozen lines traced here**, in print order:
  * **`09:1370--1374`**, the reservoirs and their mass: "Each outer coordinate
    contains two protected row reservoirs, each of mass `mu_P = 1/184` relative
    to the `m` rows of one copy of `N`."  (The display `09:1371--1373` carries
    `mu_P`; the clause "relative to the `m` rows of one copy of `N`" is on
    `09:1374`, so the quoted sentence spans `1370--1374`.)
  * **`09:1374--1376`**, the mass functional: "For a first-Bob node `v` and a
    donor set `J_0 subseteq [q]`, let `P_v(J_0)` denote, normalized by `m`, the
    protected mass from those donors reaching `v`."
  * **`09:1433--1436`**, the reservoir densities the frozen proof of
    `lem:early-protected-closure` opens with: "One of the two protected
    reservoir types contributes at least half of
    `eq:protected-early-threshold`.  Let `d_j in [0,1]` be the retained relative
    density of this type from donor `j`, and write `D_mass = sum_j d_j`."
  * **`09:490--495`**, inside `def:two-stream-state`, which is where the frozen
    text *names* the two reservoirs as row sets of `N`: "Besides the base
    reservoir `R_G`, put `R_Sigma = {sel} x Sigma x [w_Sigma]`,
    `R_D = {diag} x D_diag x [w_D] subseteq Rows(N)`."  This is the defining
    display for the objects `09:1370` counts, and it is read from there rather
    than reconstructed from the consuming block (USE-AS-DEFINITION BAN).
  * **`09:112--118`**, the base reservoir in the same carrier:
    "`R_G = {base} x Omega x [w_0] subseteq Rows(N)`".
  * **`09:105--109`**: "Let `q = 2^r` be the scale-alignment width and set
    `U = Int_q(N)`.  Write `m = |Rows(N)|`."  So `m` -- the normalizer of
    `P_v` -- is the row count of **one copy** of `N`, and the rows of `U` are
    `Fin q x Rows(N)` with the frozen outer coordinate the first component.
  * **`09:1238--1240`**, the transport (paraphrase, not a quotation): the rows a
    certificate holds at a node -- "At remaining selector capacity `2^k`, a
    certificate consists of at least `A_k` reference rows in one outer
    coordinate.  At an Alice query, route it to a child containing at least" --
    banked as `RoutingDynamics.rowsAt`.  This is the protocol-side half
    of "reaching `v`" in `09:1375`.
  * **`09:1519--1520`**, the donor reindexing: "Let `J_clean` be the `c` outer
    coordinates whose clean reference certificates reach final Alice nodes" --
    consumed through the banked `ProtectedEarlyClosure.donorMass_eq_reservoirs`,
    never restated.
* **Cross-anchors opened first-hand in the frozen files for this tranche:**
  * `08-dense-stage4.tex` (SHA-256
    `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`):
    `08:80--95` (`eq:protected-labelled-carriers`, the three labelled column
    reservoirs of `A`), `08:98--109` (`eq:protected-multiplicities`),
    `08:110--122` (`eq:protected-carrier-cardinalities`,
    `|Cols(A)| = 184 M_0 S_0 D_0`), `08:123--126` ("the base, selector, and
    diagonal column masses of `A` are exactly `91/92`, `1/184`, `1/184`"),
    `08:131--137` (`tau = 1/92`, `mu_Sigma = mu_D = 1/184`), and `08:147`
    (`N = A^T`, so a **row** of `N` is a **column** of `A`; `08:154--156` fixes
    that orientation for the whole section).
  * `06-parameter-schedule.tex` (SHA-256
    `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `06:126--139` (`eq:fixed-protected-masses`, where `mu_Sigma = mu_D = mu_P`
    is fixed at `1/184` and `tau = 1/92`), and `06:140--141` ("The
    multiplicities in `sec:dense-duplication` realise these masses exactly"),
    which is exactly why the masses below are **theorems about the built
    carriers** rather than assignments.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the two imports are `RetentionSupply` and
  `ProtectedEarlyClosure`, and the union of their import closures was
  enumerated mechanically this tranche and contains neither `LegacyNPCC.Stage12`
  nor `NPCC.Stage2`.  **No opt-in ledger note is owed.**
* **Proof status:** new.  Every declaration is either a transcription of one of
  the frozen displays above, a general property of one of those transcriptions,
  or a composition of two banked interfaces.  No mathematics is added, no
  schedule inequality is asserted, and **no numeral is assigned to any schedule
  quantity**: `mu_P` is the banked `WrapperProtectedEarly.muP`, `mu_Sigma`,
  `mu_D` are the banked `DenseStageFourOpening.muMass`, `tau` is the banked
  `tauMass`, and each reservoir's mass is *computed* from the banked
  multiplicities `wSelF`, `wDiagF` through the banked
  `protectedAFrozen_col_masses`.

## Reader counterpart: NONE claimable, and why

`routes/parameterized-np/reader-facing/sections/` was searched first-hand this
tranche for "reservoir", "protected mass", "1/184" and "donor", and every hit was
opened.  The 41-page reader artifact carries **no** item stating `09:490--495`,
`09:1370--1376` or `09:1434--1435`, and every passage that comes close is
**already assigned** to another declaration, which the READER-COUNTERPART rule
forbids re-citing.

* `reader A-stage4-details.tex:180--194` is the reader's protected-duplication
  paragraph -- the seven multiplicities -- and is already recorded (by
  `CoefficientTraversal.lean:172`) as what the banked `DenseStageFourOpening`
  transcribes.  Its follow-on sentence `:197` (the exact column masses
  `91/92, 1/184, 1/184`) is already assigned to `WRAPPER-PROTECTED-EARLY-001`.
  Neither may be re-cited here, and neither names `R_Sigma`, `R_D` as *row* sets
  of `N` in any case: the reader states the masses on the columns of `A` and
  never transposes them.
* `reader A-stage4-details.tex:370--399` is unnumbered proof prose whose
  sentence `374--376` ("The fixed masses and the certified cover bounds ensure
  that either an early protected reservoir already gives a hard restriction or
  one terminal owner receives enough protected mass from a donor") is the only
  place the reader mentions protected mass reaching a node; it is already the
  cited counterpart of six banked declarations
  (`FrontierSumAssembly`, `ProtectedEarlyClosure`, `BobHeavyDonorCount`,
  `MassLeavesOwner`, `MassRedistributionCounting`, `OwnerFamilyToPigeonhole`),
  and it is prose, not a statement.
* `reader 03-parameterized-construction.tex:599--602` mentions "deletion losses
  charged to fixed reservoirs" as a remark about the companion reduction; it
  states no reservoir, no mass and no `P_v`.

So no reader item is cited rather than one invented, and the absence is recorded
as a finding about the reader artifact.

## What this tranche lands, and what it does not

`RoutedCertificateConstruction` records, as **GAP-EXPOSED item 2**, that "the
reservoirs are not constructed (`09:1367--1384`, `09:1418--1531`) ... The
reservoirs are a *matrix-side* object (rows of the protected duplication inside
`N`), not a protocol-side one; their mass accounting is banked in
`WrapperProtectedEarly` and `ProtectedEarlyClosure` and enters this arc as the
binders `Pv`, `donor`, `d_0`, `d_1`.  Nothing below constructs them".  Its
prescription is, verbatim, *"define the reservoir row sets on the protected
duplication and transport them along `RoutingDynamics.rowsAt` to the frontier,
which is the protocol-side half of `P_v(J_0)`."*  That is precisely and only
what this module does, in three steps.

1. **The row sets** (Section 1).  `selReservoir` and `diagReservoir` are
   `R_Sigma` and `R_D` of `09:492--495` inside the frozen protected column
   carrier `Rows(N) = Cols(A) = ProtCols` of `08:83--87` -- the second and third
   summand of that carrier, as `Finset.map`s of injections, beside the base
   summand `R_G` that the banked `ScaleAlignOpening.refIncl` already names.
   They are pairwise disjoint and their three cardinalities add up to the whole
   carrier, so `Rows(N)` really is partitioned by the frozen reservoirs.
2. **The mass `mu_P`** (Section 2).  At the frozen carriers and multiplicities,
   each reservoir's cardinality divided by `|Rows(N)|` is *computed* to be
   `mu_Sigma = mu_D = 1/184`, consumed by pin from the banked
   `protectedAFrozen_col_masses`, and the two together carry exactly `tau`.
   The frozen `mu_P` of `09:1372` is identified with that constant through
   `muP_eq_muR`, so `09:1370--1374` becomes a **theorem about the built
   reservoirs** instead of an assumption about abstract row sets.
3. **`P_v(J_0)`** (Sections 3--4).  `reservoirDensity` is the `d_j in [0,1]` of
   `09:1434--1435` and `protectedMassAt` is `P_v(J_0)` of `09:1374--1376`, both
   built by transporting a coordinate's reservoir copy along the banked
   `RoutingDynamics.rowsAt`.  The frozen reservoir readout
   `P_v({j}) = mu_P (d_0 + d_1)` -- which every banked consumer
   (`ProtectedEarlyClosure.donorMass_eq_reservoirs`,
   `.firstBobMass_eq_reservoirs`, `BobHeavyDonorCount`) takes as the binder
   `hres` -- is then **proved**, from the Section-2 mass alone, and the two
   banked consumers are re-exported with that binder discharged.

**What is NOT landed, and is not implied.**  `eq:wrapper-u-dense` (`09:1188`,
`09:1780--1781`) is neither stated nor implied, and **no route completion is
claimed.**  In particular `lem:early-protected-closure` itself (`09:1418--1510`)
is *not* re-proved here: its arithmetic is the banked
`WrapperProtectedEarly.earlyProtectedClosure`, consumed by pin nowhere in this
module, and what this module supplies is only the object its threshold
`eq:protected-early-threshold` is a threshold *on*.

**OBS-1 is honoured.**  `RETENTION-SUPPLY-001` records that the `RetentionSupply`
audit runs at `delta_U = 1/640` while a chain-legal `eta_R < tau = 1/92` forces
`delta_U < 1/2944`, so that audit's satisfiability does **not** transfer to the
legal `delta_U`.  No declaration of this module consumes any `RetentionSupply`
audit declaration, and `delta_U`, `eta_R` and `bracketGE` occur in no
declaration statement and in no proof term of this module (they appear only in
prose, here and at the `Spine` section header, describing what is *not*
stated): the only `RetentionSupply` interfaces consumed are `refBlock`,
`retainedRefRows` and their general counting lemmas, which mention no schedule
constant.  Nothing here may be read as strengthening or reusing that audit.

## GAP-EXPOSED (named ranges, with the next-round prescription)

1. **The `u`-set selection of `09:1441--1471` is not built.**  The dyadic
   classification, the poor-`u`-set cover and the template-coordinate extraction
   of the frozen proof are banked as *arithmetic* in `WrapperProtectedEarly`
   (`exists_protected_dyadic_class`, `exists_dense_uset_in_class`,
   `templateCoordinateExtraction`); nothing here connects them to the reservoir
   row sets just built.  *Next round:* feed `reservoirDensity` into
   `exists_protected_dyadic_class` at `d := fun i => reservoirDensity ...` and
   discharge its `D_mass` hypothesis from `donorMass_systemPv`.
2. **`09:1473--1483` is not built**: "In a protected reservoir, all rows
   carrying a fixed Stage-2 coordinate have the same Stage-4 entry map", and the
   count `K_int = s kappa q_2` of represented Stage-2 outer blocks.  This is a
   statement about the *entries* of `protectedAFrozen` on the reservoir rows,
   not about their cardinality, and no declaration below mentions an entry.
   *Next round:* prove the fibre-constancy from `protectedDup_ignores_labels` on
   the `sel`/`diag` summands and bridge to `WrapperProtectedEarly.Kint`.
3. **`09:1512--1531` (`sec:wrapper-mass-redistribution`) is not entered.**
   `P_B`, `J_clean`, `J_good`, the Bob-heavy classification and
   `eq:wrapper-total-early-mass` remain the banked abstract-`Pv` statements of
   `ProtectedEarlyClosure` and `BobHeavyDonorCount`; this module supplies their
   `Pv` and `hres`, and stops there.  *Next round:* instantiate
   `canonical_wrapperTotalEarlyMass` and `bobHeavyCount_le_EB` at `systemPv`.
4. **The canonical inhabitation of `P_v` is REGISTERED and DEFERRED** (see
   Section 5).  The reservoir half of the paper's instance is landed -- Section 2
   runs at the paper's own carriers and multiplicities -- but the alleged
   protocol, the retained matrix `U'` and the frontier of `09:1188--1193` at the
   schedule's *materialized* parameters need machinery that is not built
   (MATERIALIZE-001 on the Lean side).  The Section-5 probe is labelled
   **NON-FIDELITY** and never discharges that obligation.
-/

namespace EthInapproximability.ParameterizedNP.ProtectedRowReservoirs

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RetentionSupply
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.MassRedistributionCounting
open EthInapproximability.ParameterizedNP.ProtectedEarlyClosure

/-! ## Section 1  The two protected row reservoirs as row sets of `N`

`09:490--495`: "Besides the base reservoir `R_G`, put
`R_Sigma = {sel} x Sigma x [w_Sigma]`, `R_D = {diag} x D_diag x [w_D]
subseteq Rows(N)`."

`N = A^T` (`08:147`), so a row of `N` is a column of `A`, and
`eq:protected-labelled-carriers` (`08:83--87`) makes `Cols(A)` the tagged sum

    ({base} x Omega x [w_0]) u ({sel} x Sigma x [w_Sigma])
      u ({diag} x D_diag x [w_D]),

banked as `DenseStageFourOpening.ProtCols`.  The three frozen labels are the
three summand injections; the base one is already banked as
`ScaleAlignOpening.refIncl`, and the other two are named here for the first
time.  Nothing about the reservoirs is *asserted*: every property below is read
off the summand structure. -/

section Inclusions

variable {Om Sg Dg : Type*} {w₀ wSg wD : ℕ}

/-- **`09:492`, the selector reservoir's inclusion into `Rows(N)`.**
`R_Sigma = {sel} x Sigma x [w_Sigma]` is the second summand of
`eq:protected-labelled-carriers`; the inclusion is named so that
"`R_Sigma subseteq Rows(N)`" is a map with a carrier of its own, exactly as the
banked `refIncl` does for `R_G`. -/
def selResIncl : Sg × Fin wSg → ProtCols Om Sg Dg w₀ wSg wD :=
  fun z => Sum.inr (Sum.inl z)

/-- **`09:493--495`, the diagonal reservoir's inclusion into `Rows(N)`.**
`R_D = {diag} x D_diag x [w_D]`, the third summand of
`eq:protected-labelled-carriers`. -/
def diagResIncl : Dg × Fin wD → ProtCols Om Sg Dg w₀ wSg wD :=
  fun z => Sum.inr (Sum.inr z)

/-- **Aux I1.**  The selector reservoir is a faithful copy of `Sigma x [w_Sigma]`
inside `Rows(N)`: no two labelled rows are identified.  General. -/
theorem selResIncl_injective :
    Function.Injective (selResIncl (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
      (wSg := wSg) (wD := wD)) := by
  intro x y h
  exact Sum.inl_injective (Sum.inr_injective h)

/-- **Aux I2.**  The same for the diagonal reservoir.  General. -/
theorem diagResIncl_injective :
    Function.Injective (diagResIncl (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
      (wSg := wSg) (wD := wD)) := by
  intro x y h
  exact Sum.inr_injective (Sum.inr_injective h)

/-- The selector reservoir's inclusion as an embedding, so the reservoir itself
can be a `Finset.map` and needs no decidability hypothesis on `Rows(N)`. -/
def selResEmb : (Sg × Fin wSg) ↪ ProtCols Om Sg Dg w₀ wSg wD :=
  ⟨selResIncl, selResIncl_injective⟩

/-- The diagonal reservoir's inclusion as an embedding. -/
def diagResEmb : (Dg × Fin wD) ↪ ProtCols Om Sg Dg w₀ wSg wD :=
  ⟨diagResIncl, diagResIncl_injective⟩

/-- The base reservoir's inclusion as an embedding, built from the **banked**
`ScaleAlignOpening.refIncl` and `refIncl_injective`; `R_G` itself is not
redefined here. -/
def baseResEmb : (Om × Fin w₀) ↪ ProtCols Om Sg Dg w₀ wSg wD :=
  ⟨refIncl, refIncl_injective⟩

end Inclusions

section Reservoirs

/-- **`09:112--114`, `R_G` as a row set of `N`.**  The base reservoir
`{base} x Omega x [w_0]`, the banked `refIncl`'s image.  Present so that
Section 1's partition can be stated; the reference *geometry* is banked in
`ScaleAlignOpening` and is not restated. -/
def baseReservoir (Om : Type*) [Fintype Om] (Sg Dg : Type*) (w₀ wSg wD : ℕ) :
    Finset (ProtCols Om Sg Dg w₀ wSg wD) :=
  Finset.map (baseResEmb (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
    (wSg := wSg) (wD := wD)) Finset.univ

/-- **`09:492`, `R_Sigma` as a row set of `N`.** -/
def selReservoir (Om : Type*) (Sg : Type*) [Fintype Sg] (Dg : Type*)
    (w₀ wSg wD : ℕ) : Finset (ProtCols Om Sg Dg w₀ wSg wD) :=
  Finset.map (selResEmb (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
    (wSg := wSg) (wD := wD)) Finset.univ

/-- **`09:493--495`, `R_D` as a row set of `N`.** -/
def diagReservoir (Om Sg : Type*) (Dg : Type*) [Fintype Dg] (w₀ wSg wD : ℕ) :
    Finset (ProtCols Om Sg Dg w₀ wSg wD) :=
  Finset.map (diagResEmb (Om := Om) (Sg := Sg) (Dg := Dg) (w₀ := w₀)
    (wSg := wSg) (wD := wD)) Finset.univ

variable {Om Sg Dg : Type*} {w₀ wSg wD : ℕ}

/-- **Aux R1a (membership in the base reservoir).**  General. -/
@[simp] theorem mem_baseReservoir [Fintype Om]
    {c : ProtCols Om Sg Dg w₀ wSg wD} :
    c ∈ baseReservoir Om Sg Dg w₀ wSg wD ↔ ∃ z, refIncl z = c := by
  simp [baseReservoir, baseResEmb]

/-- **Aux R1b (membership in the selector reservoir).**  General. -/
@[simp] theorem mem_selReservoir [Fintype Sg]
    {c : ProtCols Om Sg Dg w₀ wSg wD} :
    c ∈ selReservoir Om Sg Dg w₀ wSg wD ↔ ∃ z, selResIncl z = c := by
  simp [selReservoir, selResEmb]

/-- **Aux R1c (membership in the diagonal reservoir).**  General. -/
@[simp] theorem mem_diagReservoir [Fintype Dg]
    {c : ProtCols Om Sg Dg w₀ wSg wD} :
    c ∈ diagReservoir Om Sg Dg w₀ wSg wD ↔ ∃ z, diagResIncl z = c := by
  simp [diagReservoir, diagResEmb]

/-- **`08:100--102` read on `R_G`.**  `|R_G| = M_0 w_0`.  General. -/
theorem card_baseReservoir [Fintype Om] :
    (baseReservoir Om Sg Dg w₀ wSg wD).card = Fintype.card Om * w₀ := by
  simp [baseReservoir]

/-- **`08:100--102` read on `R_Sigma`.**  `|R_Sigma| = S_0 w_Sigma`: the frozen
reservoir carries its carrier's cardinality times its own multiplicity, which is
the numerator of the mass `mu_Sigma` in `08:123--126`.  General. -/
theorem card_selReservoir [Fintype Sg] :
    (selReservoir Om Sg Dg w₀ wSg wD).card = Fintype.card Sg * wSg := by
  simp [selReservoir]

/-- **`08:100--102` read on `R_D`.**  `|R_D| = D_0 w_D`.  General. -/
theorem card_diagReservoir [Fintype Dg] :
    (diagReservoir Om Sg Dg w₀ wSg wD).card = Fintype.card Dg * wD := by
  simp [diagReservoir]

/-- **Aux R2a (`08:83--87`: the labels really separate).**  `R_G` and `R_Sigma`
are disjoint, because the frozen labels `base` and `sel` are distinct summand
injections.  General. -/
theorem baseReservoir_disjoint_selReservoir [Fintype Om] [Fintype Sg] :
    Disjoint (baseReservoir Om Sg Dg w₀ wSg wD) (selReservoir Om Sg Dg w₀ wSg wD) := by
  rw [Finset.disjoint_left]
  rintro c hb hs
  rw [mem_baseReservoir] at hb
  rw [mem_selReservoir] at hs
  obtain ⟨z, rfl⟩ := hb
  obtain ⟨z', hz'⟩ := hs
  simp [selResIncl, refIncl] at hz'

/-- **Aux R2b.**  `R_G` and `R_D` are disjoint.  General. -/
theorem baseReservoir_disjoint_diagReservoir [Fintype Om] [Fintype Dg] :
    Disjoint (baseReservoir Om Sg Dg w₀ wSg wD) (diagReservoir Om Sg Dg w₀ wSg wD) := by
  rw [Finset.disjoint_left]
  rintro c hb hd
  rw [mem_baseReservoir] at hb
  rw [mem_diagReservoir] at hd
  obtain ⟨z, rfl⟩ := hb
  obtain ⟨z', hz'⟩ := hd
  simp [diagResIncl, refIncl] at hz'

/-- **`09:1370`, "**two** protected row reservoirs".**  `R_Sigma` and `R_D` are
disjoint, so the frozen sentence counts two *distinct* reservoirs and the
two-term readout of `P_v` below is not a double count of one of them.
General. -/
theorem selReservoir_disjoint_diagReservoir [Fintype Sg] [Fintype Dg] :
    Disjoint (selReservoir Om Sg Dg w₀ wSg wD) (diagReservoir Om Sg Dg w₀ wSg wD) := by
  rw [Finset.disjoint_left]
  rintro c hs hd
  rw [mem_selReservoir] at hs
  rw [mem_diagReservoir] at hd
  obtain ⟨z, rfl⟩ := hs
  obtain ⟨z', hz'⟩ := hd
  simp [selResIncl, diagResIncl] at hz'

/-- **`eq:protected-carrier-cardinalities` (`08:110--122`) as a partition of
`Rows(N)`.**  The three frozen reservoirs exhaust the row carrier: their
cardinalities add up to `|Rows(N)| = |Cols(A)|`.  Together with the three
disjointness lemmas this is what makes "mass" in `08:123--126` and `09:1370--1374`
a genuine relative frequency rather than a ratio of unrelated integers.
General. -/
theorem reservoirs_card_add [Fintype Om] [Fintype Sg] [Fintype Dg] :
    (baseReservoir Om Sg Dg w₀ wSg wD).card + (selReservoir Om Sg Dg w₀ wSg wD).card
        + (diagReservoir Om Sg Dg w₀ wSg wD).card
      = Fintype.card (ProtCols Om Sg Dg w₀ wSg wD) := by
  rw [card_baseReservoir, card_selReservoir, card_diagReservoir, card_ProtCols]
  ring

/-- **Aux R2d (`09:105--109` transports disjointness to one outer coordinate).**
Disjoint row sets of `N` have disjoint copies inside a single outer coordinate of
`U = Int_q(N)`, because a copy fixes the outer index and keeps the inner row.
Stated on the banked `RetentionSupply.refBlock`, which is the general "`i`-th
copy of a row set of `N`" and is consumed rather than re-defined.  General. -/
theorem refBlock_disjoint_of_disjoint {Rw : Type*} [Fintype Rw] [DecidableEq Rw]
    {q : ℕ} {R₁ R₂ : Finset Rw} (h : Disjoint R₁ R₂) (i : Fin q) :
    Disjoint (refBlock R₁ i) (refBlock R₂ i) := by
  rw [Finset.disjoint_left]
  intro a h1 h2
  simp only [refBlock, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  exact (Finset.disjoint_left.mp h h1.2) h2.2

/-- **Aux R3 (nondegeneracy of the selector reservoir).**  As soon as the frozen
carrier `Sigma` is inhabited and its multiplicity `w_Sigma` is positive -- both
of which `eq:protected-multiplicities` supplies -- `R_Sigma` is a nonempty set of
rows.  General. -/
theorem selReservoir_nonempty [Fintype Sg] (z : Sg) (hw : 0 < wSg) :
    (selReservoir Om Sg Dg w₀ wSg wD).Nonempty :=
  ⟨selResIncl (z, ⟨0, hw⟩), mem_selReservoir.mpr ⟨_, rfl⟩⟩

/-- **Aux R4 (nondegeneracy of the diagonal reservoir).**  General. -/
theorem diagReservoir_nonempty [Fintype Dg] (z : Dg) (hw : 0 < wD) :
    (diagReservoir Om Sg Dg w₀ wSg wD).Nonempty :=
  ⟨diagResIncl (z, ⟨0, hw⟩), mem_diagReservoir.mpr ⟨_, rfl⟩⟩

end Reservoirs

/-! ## Section 2  The frozen mass `mu_P = 1/184` (`09:1370--1374`)

"Each outer coordinate contains two protected row reservoirs, each of mass
`mu_P = 1/184` relative to the `m` rows of one copy of `N`."

`06:140--141` says why this is a theorem and not a definition: "The
multiplicities in `sec:dense-duplication` realise these masses exactly."  So the
mass is *computed* from the built carriers -- `card_selReservoir` supplies the
numerator `S_0 w_Sigma`, the banked `card_ProtColsFrozen` the denominator, and
the banked `protectedAFrozen_col_masses` (`08:123--126`) the ratio.  No numeral
is written in this section. -/

section FrozenMasses

variable (F : FiniteSlots.Stage1SlotBinding) (q₂ : ℕ) (Y : Type*) [Fintype Y]

/-- `R_G` at the frozen carriers and multiplicities of `08:83--109`. -/
abbrev baseReservoirF : Finset (ProtColsFrozen F q₂ Y) :=
  baseReservoir (Omega F q₂ Y) (SelCar F q₂ Y) (DiagCar F q₂ Y) (wBaseF F q₂ Y)
    (wSelF F q₂ Y) (wDiagF F q₂ Y)

/-- `R_Sigma` at the frozen carriers and multiplicities of `08:83--109`. -/
abbrev selReservoirF : Finset (ProtColsFrozen F q₂ Y) :=
  selReservoir (Omega F q₂ Y) (SelCar F q₂ Y) (DiagCar F q₂ Y) (wBaseF F q₂ Y)
    (wSelF F q₂ Y) (wDiagF F q₂ Y)

/-- `R_D` at the frozen carriers and multiplicities of `08:83--109`. -/
abbrev diagReservoirF : Finset (ProtColsFrozen F q₂ Y) :=
  diagReservoir (Omega F q₂ Y) (SelCar F q₂ Y) (DiagCar F q₂ Y) (wBaseF F q₂ Y)
    (wSelF F q₂ Y) (wDiagF F q₂ Y)

/-- **`08:100--102` at the frozen instance.**  `|R_Sigma| = S_0 w_Sigma`, which is
literally the numerator of the second clause of `protectedAFrozen_col_masses`. -/
theorem card_selReservoirF :
    (selReservoirF F q₂ Y).card = Fintype.card (SelCar F q₂ Y) * wSelF F q₂ Y :=
  card_selReservoir

/-- **`08:100--102` at the frozen instance.**  `|R_D| = D_0 w_D`. -/
theorem card_diagReservoirF :
    (diagReservoirF F q₂ Y).card = Fintype.card (DiagCar F q₂ Y) * wDiagF F q₂ Y :=
  card_diagReservoir

/-- **`09:1370--1374` for `R_Sigma`, PROVED at the built carriers.**  The
selector reservoir's mass relative to the `m` rows of one copy of `N` is exactly
`mu_Sigma = 1/184` (`08:125`, `08:134`), the banked `muMass`.  Consumed by pin
from `protectedAFrozen_col_masses`; nothing is recomputed and no numeral is
written. -/
theorem selReservoirF_row_mass (hq : 0 < q₂) (y₀ : Y) :
    (((selReservoirF F q₂ Y).card : ℕ) : ℚ)
        / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = muMass := by
  rw [card_selReservoirF]
  exact (protectedAFrozen_col_masses F hq y₀).2.1

/-- **`09:1370--1374` for `R_D`, PROVED at the built carriers.**  `mu_D = 1/184`
(`08:125`, `08:134`). -/
theorem diagReservoirF_row_mass (hq : 0 < q₂) (y₀ : Y) :
    (((diagReservoirF F q₂ Y).card : ℕ) : ℚ)
        / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = muMass := by
  rw [card_diagReservoirF]
  exact (protectedAFrozen_col_masses F hq y₀).2.2.1

/-- **`08:133`, `06:132`: the two protected reservoirs together carry `tau`.**
`tau = 1/92 = 2 mu_P` is what the frozen low-row profile discards at `08:221--227`,
and it is a *consequence* of the two reservoir masses rather than a third
constant.  Consumed by pin from the fourth clause of
`protectedAFrozen_col_masses`. -/
theorem protectedReservoirsF_row_mass (hq : 0 < q₂) (y₀ : Y) :
    ((((selReservoirF F q₂ Y).card + (diagReservoirF F q₂ Y).card : ℕ)) : ℚ)
        / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = tauMass := by
  rw [card_selReservoirF, card_diagReservoirF]
  exact (protectedAFrozen_col_masses F hq y₀).2.2.2

/-- **Aux M1 (the row carrier is nonempty at legal parameters).**  `m > 0`, so
"normalized by `m`" in `09:1375` is a legitimate division.  Read off
`card_ProtColsFrozen` and the banked `section8_col_counts_pos`. -/
theorem card_ProtColsFrozen_pos (hq : 0 < q₂) (y₀ : Y) :
    0 < Fintype.card (ProtColsFrozen F q₂ Y) := by
  obtain ⟨hM, hS, hD⟩ := section8_col_counts_pos F hq y₀
  rw [card_ProtColsFrozen]
  exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.mul_pos hM hS) hD)

end FrozenMasses

section MuPin

/-- **The cross-constant pin of `09:1372` against `06:133` and `08:134`.**
`eq:fixed-protected-masses` fixes `mu_Sigma = mu_D = mu_P` at one and the same
value, so the `mu_P` of `09:1372` -- banked as `WrapperProtectedEarly.muP` in
`ℝ` -- is the real image of the `mu_Sigma = mu_D` of `08:134`, banked as
`DenseSynchronisation.muR = ((muMass : ℚ) : ℝ)`.  Without this identity the
Section-2 masses (stated in `ℚ` against `muMass`) and the banked reservoir
readout (stated in `ℝ` against `muP`) would be about two unrelated constants.
General; nothing is assigned. -/
theorem muP_eq_muR : muP = muR := by
  rw [muR, muMass, muP]
  norm_num

/-- **Aux M2.**  The same pin in the direction Section 3 uses: the rational mass
of Section 2, cast to `ℝ`, is the banked `muP`.  General. -/
theorem cast_muMass_eq_muP : ((muMass : ℚ) : ℝ) = muP := (muP_eq_muR).symm

end MuPin

section FrozenMassReal

variable (F : FiniteSlots.Stage1SlotBinding) (q₂ : ℕ) (Y : Type*) [Fintype Y]

/-- **`09:1370--1374` in the form Section 3 consumes.**  `|R_Sigma| = mu_P m` as
an identity of reals, obtained from the rational mass of `selReservoirF_row_mass`
by clearing the (positive) denominator and applying the constant pin.  This is
the *only* form in which the frozen mass enters `P_v`, and it is a theorem about
the built reservoir at the paper's own carriers. -/
theorem selReservoirF_card_eq_muP_mul (hq : 0 < q₂) (y₀ : Y) :
    (((selReservoirF F q₂ Y).card : ℕ) : ℝ)
      = muP * ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℝ) := by
  have hpos : (0 : ℚ) < ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) := by
    exact_mod_cast card_ProtColsFrozen_pos F q₂ Y hq y₀
  have hQ := selReservoirF_row_mass F q₂ Y hq y₀
  have hQ' : (((selReservoirF F q₂ Y).card : ℕ) : ℚ)
      = muMass * ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) := by
    field_simp at hQ
    linarith [hQ]
  have := congrArg (fun x : ℚ => (x : ℝ)) hQ'
  push_cast at this
  rw [this, cast_muMass_eq_muP]

/-- **`09:1370--1374` for `R_D` in the same form.**  `|R_D| = mu_P m`. -/
theorem diagReservoirF_card_eq_muP_mul (hq : 0 < q₂) (y₀ : Y) :
    (((diagReservoirF F q₂ Y).card : ℕ) : ℝ)
      = muP * ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℝ) := by
  have hpos : (0 : ℚ) < ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) := by
    exact_mod_cast card_ProtColsFrozen_pos F q₂ Y hq y₀
  have hQ := diagReservoirF_row_mass F q₂ Y hq y₀
  have hQ' : (((diagReservoirF F q₂ Y).card : ℕ) : ℚ)
      = muMass * ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) := by
    field_simp at hQ
    linarith [hQ]
  have := congrArg (fun x : ℚ => (x : ℝ)) hQ'
  push_cast at this
  rw [this, cast_muMass_eq_muP]

end FrozenMassReal

/-! ## Section 3  `P_v(J_0)` and the densities `d_j` (`09:1374--1376`,
`09:1434--1435`)

"For a first-Bob node `v` and a donor set `J_0 subseteq [q]`, let `P_v(J_0)`
denote, normalized by `m`, the protected mass from those donors reaching `v`."

Three frozen conventions are being obeyed here and each is cited where it is
used.

* **The donor index is the outer coordinate** (`09:1375`, `J_0 subseteq [q]`),
  and `09:105--109` makes the rows of `U = Int_q(N)` the pairs
  `Fin q x Rows(N)`, so a coordinate's copy of a reservoir is the banked
  `RetentionSupply.refBlock` of that reservoir -- the *same* general definition
  the reference block uses, applied to a different row set of `N`.
* **"Reaching `v`"** is `09:1238--1240` (paraphrased, not quoted: the frozen
  lines read "At remaining selector capacity `2^k`, a certificate consists of at
  least `A_k` reference rows in one outer coordinate.  At an Alice query, route
  it to a child containing at least"), banked as `RoutingDynamics.rowsAt`:
  the rows a certificate holds at the node addressed by `p` are its initial rows
  cut by Alice's answers along `p`.
* **"Normalized by `m`"** is `09:105--109`'s `m = |Rows(N)|`, the row count of
  **one** copy of `N` -- not of `U`, whose row count is `q m`.  The normalizer is
  therefore carried as an explicit natural number, never inferred from a
  carrier. -/

section MassFunctional

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}

/-- **`09:1434--1435`, `d_j`.**  "Let `d_j in [0,1]` be the retained relative
density of this type from donor `j`": the fraction of one coordinate's copy of
one protected reservoir that is still held at the node addressed by `p`.

Numerator: the retained reservoir rows of coordinate `i` transported along the
route by the banked `rowsAt`.  Denominator: the reservoir's own size, since the
frozen quantity is a density *of that type*, and a coordinate's copy has exactly
`|Res|` rows (banked `refBlock_card`). -/
noncomputable def reservoirDensity (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (i : Fin q) (p : List Bool) : ℝ :=
  ((rowsAt P (retainedRefRows Rset Res i) p).card : ℝ) / (Res.card : ℝ)

/-- **`09:1374--1376`, `P_v(J_0)`.**  The protected mass from the donors `J_0`
reaching the node addressed by `p`, normalized by `m`.

"The protected mass" is the mass of **both** reservoir types (`09:1370`, "two
protected row reservoirs"), which is why the summand has two terms; `09:1433`'s
"one of the two protected reservoir types contributes at least half" is a
statement *about* this two-term sum and is banked, not restated. -/
noncomputable def protectedMassAt (P : Protocol {a // a ∈ Rset} Yc Zc)
    (RSig RD : Finset Rw) (m : ℕ) (J₀ : Finset (Fin q)) (p : List Bool) : ℝ :=
  (∑ i ∈ J₀, (((rowsAt P (retainedRefRows Rset RSig i) p).card : ℝ)
      + ((rowsAt P (retainedRefRows Rset RD i) p).card : ℝ))) / (m : ℝ)

/-- **Aux D1 (`09:1434`, `d_j >= 0`).**  General. -/
theorem reservoirDensity_nonneg (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (i : Fin q) (p : List Bool) :
    0 ≤ reservoirDensity P Res i p := by
  unfold reservoirDensity
  positivity

/-- **Aux D2a (a coordinate's retained reservoir rows are at most the reservoir).**

`09:105--109` makes an outer coordinate's copy of a row set of `N` a *copy*: the
outer index is fixed and the `Fin 1` interlace slot is unique, so the inner row
determines the labelled row.  Hence the retained part of the copy injects into
the reservoir.  General; stated without a `Fintype` on the row carrier, because
nothing here enumerates `Rows(N)`. -/
theorem retainedRefRows_card_le (Rset : Finset (Fin 1 × (Fin q × Rw)))
    (Res : Finset Rw) (i : Fin q) :
    (retainedRefRows Rset Res i).card ≤ Res.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun a => a.val.2.2) (fun a ha => ?_)
    (fun a ha b hb hab => ?_)
  · exact (mem_retainedRefRows.mp ha).2
  · simp only [Finset.mem_coe, mem_retainedRefRows] at ha hb
    refine Subtype.ext ?_
    have h1 : a.val.1 = b.val.1 := Subsingleton.elim _ _
    have h2 : a.val.2.1 = b.val.2.1 := ha.1.trans hb.1.symm
    have h3 : a.val.2.2 = b.val.2.2 := hab
    calc a.val = (a.val.1, a.val.2.1, a.val.2.2) := rfl
      _ = (b.val.1, b.val.2.1, b.val.2.2) := by rw [h1, h2, h3]
      _ = b.val := rfl

/-- **Aux D2 (`09:1434`, `d_j <= 1`).**  The frozen bracket `d_j in [0,1]` is a
theorem, not a hypothesis: the rows still held at a node are a subset of the
coordinate's retained reservoir rows (banked `rowsAt_subset`), which are at most
the reservoir's own rows.  General. -/
theorem reservoirDensity_le_one (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (i : Fin q) (p : List Bool) :
    reservoirDensity P Res i p ≤ 1 := by
  rcases Nat.eq_zero_or_pos Res.card with h | h
  · unfold reservoirDensity
    rw [h]
    simp
  · have hsub : (rowsAt P (retainedRefRows Rset Res i) p).card ≤ Res.card :=
      le_trans (Finset.card_le_card (rowsAt_subset _ _ _))
        (retainedRefRows_card_le Rset Res i)
    have hR : (0 : ℝ) < (Res.card : ℝ) := by exact_mod_cast h
    unfold reservoirDensity
    rw [div_le_one hR]
    exact_mod_cast hsub

/-- **Aux D3 (the root readout).**  At the root of the alleged protocol every
retained reservoir row is still held, so `d_j` is the coordinate's retained
fraction.  This is the banked `rowsAt_nil` applied to the reservoir.
General. -/
theorem reservoirDensity_nil (P : Protocol {a // a ∈ Rset} Yc Zc)
    (Res : Finset Rw) (i : Fin q) :
    reservoirDensity P Res i ([] : List Bool)
      = ((retainedRefRows Rset Res i).card : ℝ) / (Res.card : ℝ) := by
  rw [reservoirDensity, rowsAt_nil]

/-- **Aux P1 (`P_v` is a mass).**  General. -/
theorem protectedMassAt_nonneg (P : Protocol {a // a ∈ Rset} Yc Zc)
    (RSig RD : Finset Rw) (m : ℕ) (J₀ : Finset (Fin q)) (p : List Bool) :
    0 ≤ protectedMassAt P RSig RD m J₀ p := by
  unfold protectedMassAt
  apply div_nonneg _ (Nat.cast_nonneg m)
  exact Finset.sum_nonneg fun i _ => by positivity

/-- **Aux P2 (no donors, no mass).**  General. -/
@[simp] theorem protectedMassAt_empty (P : Protocol {a // a ∈ Rset} Yc Zc)
    (RSig RD : Finset Rw) (m : ℕ) (p : List Bool) :
    protectedMassAt P RSig RD m (∅ : Finset (Fin q)) p = 0 := by
  simp [protectedMassAt]

/-- **Aux P3 (`P_v` is additive over donors).**  `09:1375`'s "the protected mass
from *those donors*" is a sum over `J_0`, so `P_v(J_0)` splits into the frozen
singletons `P_v({j})` that `09:1537` and the banked
`MassRedistributionCounting.donorMass` are written on.  General. -/
theorem protectedMassAt_eq_sum_singletons (P : Protocol {a // a ∈ Rset} Yc Zc)
    (RSig RD : Finset Rw) (m : ℕ) (J₀ : Finset (Fin q)) (p : List Bool) :
    protectedMassAt P RSig RD m J₀ p
      = ∑ i ∈ J₀, protectedMassAt P RSig RD m ({i} : Finset (Fin q)) p := by
  simp [protectedMassAt, Finset.sum_div]

/-- **Aux P4 (monotone in the donor set).**  Adding donors can only add mass --
the property that makes `09:1521--1522`'s "with `J_0 = J_clean`" an admissible
restriction of the full donor set.  General. -/
theorem protectedMassAt_mono (P : Protocol {a // a ∈ Rset} Yc Zc)
    (RSig RD : Finset Rw) (m : ℕ) {J₀ J₁ : Finset (Fin q)} (h : J₀ ⊆ J₁)
    (p : List Bool) :
    protectedMassAt P RSig RD m J₀ p ≤ protectedMassAt P RSig RD m J₁ p := by
  have key : ∀ x y : ℝ, x ≤ y → x / (m : ℝ) ≤ y / (m : ℝ) := by
    intro x y hxy
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr (Nat.cast_nonneg m))
  exact key _ _ (Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => by positivity)

/-- **THE FROZEN RESERVOIR READOUT `P_v({j}) = mu_P (d_0 + d_1)`, PROVED.**

`09:1370--1376` read together: each of the two reservoirs has mass `mu_P`
relative to `m`, and `d_0`, `d_1` are the *relative* densities inside them
(`09:1434--1435`), so the absolute mass of donor `j` reaching the node is
`mu_P d_0 + mu_P d_1`.

This is exactly the hypothesis `hres` that every banked consumer of `P_v` takes
as a binder -- `ProtectedEarlyClosure.donorMass_eq_reservoirs`,
`.donorMass_singleton_reservoirs`, `.firstBobMass_eq_reservoirs`, and through
them `BobHeavyDonorCount` -- and which, in the banked modules' own words, "enters
this arc as the binders `Pv`, `donor`, `d_0`, `d_1`".  Here it is discharged.

*The two mass hypotheses are the paper's, not free parameters.*  `hSig` and `hD`
are `09:1370--1374` at the built reservoirs, supplied at the paper's own carriers
by `selReservoirF_card_eq_muP_mul` and `diagReservoirF_card_eq_muP_mul`; they are
carried as explicit binders (never a premise bundle) so that this lemma stays
general in the row carrier.

*Why the trivial witness fails.*  The conclusion is an equation between two named
quantities and is not `rfl`: the left side divides by `m`, the right by the two
reservoir cardinalities.  Delete the mass hypotheses and the identity is false --
`protectedMass_readout_needs_the_mass` below exhibits the arithmetic separation
`(1 + 1)/2 != mu_P * (1 + 1)` at explicit cardinalities -- so the frozen `mu_P`
is genuinely load-bearing rather than decorative.  That pole is a rejection
probe at self-chosen numbers and claims **no** schedule legality for them
(category (3) of the defined-vs-free rule); it is not an instantiation of this
lemma with a hypothesis deleted.

General in the row carrier, the width, the alleged protocol, the donor and the
route. -/
theorem protectedMassAt_singleton_readout (P : Protocol {a // a ∈ Rset} Yc Zc)
    {RSig RD : Finset Rw} {m : ℕ} (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ))
    (i : Fin q) (p : List Bool) :
    protectedMassAt P RSig RD m ({i} : Finset (Fin q)) p
      = muP * (reservoirDensity P RSig i p + reservoirDensity P RD i p) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmu : (0 : ℝ) < muP := muP_pos
  simp only [protectedMassAt, reservoirDensity, Finset.sum_singleton]
  rw [hSig, hD]
  field_simp

end MassFunctional

/-! ## Section 4  Composition with the banked counting spine

The banked `MassRedistributionCounting.donorMass` and `.firstBobMass` are the
aggregates `09:1524--1528` and `09:1537` sum, and `ProtectedEarlyClosure` proved
their reservoir readouts *given* `hres`.  With Section 3's `hres` discharged,
those two readouts hold outright for the built `P_v`. -/

section Spine

variable {Rw : Type*} [DecidableEq Rw] {q : ℕ}
  {Rset : Finset (Fin 1 × (Fin q × Rw))} {Yc Zc : Type*}
  {Coord ι V : Type*}

/-- **`09:1374--1376` at a routed system's frontier.**  `P_v` as the banked
consumers type it: a function of a frontier node and a certificate index, where
`node` is the system's address map (`09:1250--1253`, where the frozen text stops
each routed branch at its first Bob query and addresses a frontier node by its
count `d_v` of preceding Alice queries) and `donor` is the reindexing of
`09:1519--1520` ("the `c` outer coordinates whose clean reference certificates
reach final Alice nodes").

Deliberately **not** data: `donor`'s injectivity, which is a property of the
system and is supplied by the caller exactly where the banked
`donorMass_eq_reservoirs` spends it. -/
noncomputable def systemPv (P : Protocol {a // a ∈ Rset} Yc Zc)
    (node : V → List Bool) (donor : ι → Fin q) (RSig RD : Finset Rw) (m : ℕ) :
    V → ι → ℝ :=
  fun v j => protectedMassAt P RSig RD m ({donor j} : Finset (Fin q)) (node v)

/-- **The frozen singleton readout at the frontier**, i.e. the exact `hres` shape
that `ProtectedEarlyClosure.donorMass_eq_reservoirs` and
`.firstBobMass_eq_reservoirs` take.  General. -/
theorem systemPv_readout (P : Protocol {a // a ∈ Rset} Yc Zc)
    (node : V → List Bool) (donor : ι → Fin q) {RSig RD : Finset Rw} {m : ℕ}
    (hm : 0 < m) (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ)) (v : V) (j : ι) :
    systemPv P node donor RSig RD m v j
      = muP * (reservoirDensity P RSig (donor j) (node v)
          + reservoirDensity P RD (donor j) (node v)) :=
  protectedMassAt_singleton_readout P hm hSig hD (donor j) (node v)

/-- **`09:1519--1520` composed with `09:1370--1376`, with `hres` DISCHARGED.**

The banked `ProtectedEarlyClosure.donorMass_eq_reservoirs` reads: `donorMass`
of an abstract `Pv` equals `mu_P (sum d_0 + sum d_1)` *provided* the reservoir
readout holds at every donor of `J_0`.  At the built `P_v` that proviso is
Section 3, so the banked identity now holds with no hypothesis about `Pv` at all;
what remains is `09:1519--1520`'s injectivity, which is a fact about the routed system
and is correctly still a binder.

`D_mass = sum_j d_j` of `09:1436` is therefore, for the built reservoirs, the
right-hand side's two sums -- which is the input the banked
`WrapperProtectedEarly.earlyProtectedClosure` consumes.  Nothing about that
lemma's conclusion is asserted here.

General in the row carrier, the donor index, the node type and the width. -/
theorem donorMass_systemPv (P : Protocol {a // a ∈ Rset} Yc Zc)
    (node : V → List Bool) (donor : ι → Fin q) {RSig RD : Finset Rw} {m : ℕ}
    (hm : 0 < m) (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ)) (J₀ : Finset ι) (v : V)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j) :
    donorMass (systemPv P node donor RSig RD m) J₀ v
      = muP * ((∑ i ∈ J₀.image donor, reservoirDensity P RSig i (node v))
          + (∑ i ∈ J₀.image donor, reservoirDensity P RD i (node v))) :=
  donorMass_eq_reservoirs (systemPv P node donor RSig RD m) donor
    (fun i => reservoirDensity P RSig i (node v))
    (fun i => reservoirDensity P RD i (node v)) J₀ v hinj
    (fun j _ => systemPv_readout P node donor hm hSig hD v j)

/-- **`09:1537` at the built reservoirs, with `hres` DISCHARGED.**

`sum_{v : first-Bob frontier node} P_v({j})` -- the quantity the Bob-heavy
threshold `eta_R/4` of `09:1538` is compared against -- read through the built
reservoirs.  The banked `ProtectedEarlyClosure.firstBobMass_eq_reservoirs`
supplies the sum; Section 3 supplies its per-node hypothesis.

**No inequality is stated**: `eta_R` does not occur, no donor is classified
Bob-heavy, and `eq:wrapper-bob-heavy-count` (`09:1541--1547`) is untouched. -/
theorem firstBobMass_systemPv [Fintype V] {P : Protocol {a // a ∈ Rset} Yc Zc}
    {r A0 : ℕ} (S : RoutedSystem P Coord ι V r A0) (donor : ι → Fin q)
    {RSig RD : Finset Rw} {m : ℕ} (hm : 0 < m)
    (hSig : ((RSig.card : ℕ) : ℝ) = muP * (m : ℝ))
    (hD : ((RD.card : ℕ) : ℝ) = muP * (m : ℝ)) (j : ι) :
    firstBobMass S (systemPv P S.node donor RSig RD m) j
      = ∑ v ∈ S.toWrapperFrontier.bobNodes,
          muP * (reservoirDensity P RSig (donor j) (S.node v)
            + reservoirDensity P RD (donor j) (S.node v)) :=
  firstBobMass_eq_reservoirs S (systemPv P S.node donor RSig RD m) donor
    (fun v i => reservoirDensity P RSig i (S.node v))
    (fun v i => reservoirDensity P RD i (S.node v)) j
    (fun v _ => systemPv_readout P S.node donor hm hSig hD v j)

end Spine

/-! ## Section 5  Inhabitation

**Sections 1--2 ARE the paper's own instance and claim so.**  `R_Sigma` and `R_D`
are constructed at the frozen carriers `Sigma`, `D_diag` and the frozen
multiplicities `w_Sigma`, `w_D` of `eq:protected-labelled-carriers` and
`eq:protected-multiplicities`, and their mass is *computed* to be the paper's
`mu_P` at every legal `(F, q_2, Y)` -- no numeral, no self-chosen width, no
synthetic carrier.  So the canonical-inhabitation obligation **for the
reservoirs** is discharged, not deferred, by `reservoirsF_are_the_paper_objects`.

**The canonical inhabitation of `P_v` is REGISTERED and DEFERRED.**  The paper's
own instance of `protectedMassAt` is the mass functional of `09:1374--1376` at
the retained matrix `U'` of `09:1188--1191`, the alleged protocol of
`09:1192--1193`, and the frontier of `09:1250--1259`, all at the schedule's
**materialized** parameters.  Two halves block it: the materialization itself
(`06:859--862`, MATERIALIZE-001 on the Lean side) and the schedule's own gate
discharge (`06:875--887`).  The obligation is registered here and is discharged
when the materialization lands; it is **never** satisfied by the probe below. -/

/-- Decidable equality on the frozen protected row carrier
`Rows(N) = Cols(A) = ProtColsFrozen` (`08:83--87` for the three-summand shape,
`08:147` for the orientation).  Spelled out because the nested sum-of-products
defeats the default instance search; it carries no mathematical content and is
`scoped`, so it is inherited only by a consumer that opens this namespace --
which the next tranche must do anyway to state
`donorMass_at_the_paper_reservoirs`. -/
scoped instance instDecEqProtColsFrozenRes (F : FiniteSlots.Stage1SlotBinding)
    (q₂ : ℕ) (Y : Type*) [Fintype Y] [DecidableEq Y] :
    DecidableEq (ProtColsFrozen F q₂ Y) :=
  @instDecidableEqSum _ _ _ (@instDecidableEqSum _ _ _ _)

section Inhabitation

/-- **CANONICAL INHABITATION of Sections 1--2 (not a probe).**

At every legal `(F, q_2, Y)` -- `q_2 > 0` is `06:124`, and `Y` inhabited is
`08:33`'s "Because `Y_R = [n_R]` is nonempty" -- the two constructed reservoirs
are simultaneously: nonempty, disjoint from each other, of exactly the frozen
mass `mu_P` each, and jointly of exactly the frozen `tau`; and the three
reservoirs partition `Rows(N)`.

Every quantity here is the paper's own: the carriers are
`eq:protected-labelled-carriers`, the multiplicities are
`eq:protected-multiplicities`, and the masses are read out of them rather than
assigned.  So this is the paper's instance of the Section-1 objects, not a
synthetic inhabitant of the Section-1 types. -/
theorem reservoirsF_are_the_paper_objects (F : FiniteSlots.Stage1SlotBinding)
    {q₂ : ℕ} {Y : Type*} [Fintype Y] (hq : 0 < q₂) (y₀ : Y)
    (z₀ : SelCar F q₂ Y) (d₀ : DiagCar F q₂ Y) :
    (selReservoirF F q₂ Y).Nonempty ∧ (diagReservoirF F q₂ Y).Nonempty ∧
      Disjoint (selReservoirF F q₂ Y) (diagReservoirF F q₂ Y) ∧
      (((selReservoirF F q₂ Y).card : ℕ) : ℚ)
          / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = muMass ∧
      (((diagReservoirF F q₂ Y).card : ℕ) : ℚ)
          / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = muMass ∧
      ((((selReservoirF F q₂ Y).card + (diagReservoirF F q₂ Y).card : ℕ)) : ℚ)
          / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = tauMass ∧
      (baseReservoirF F q₂ Y).card + (selReservoirF F q₂ Y).card
          + (diagReservoirF F q₂ Y).card
        = Fintype.card (ProtColsFrozen F q₂ Y) := by
  obtain ⟨hM, hS, hD⟩ := section8_col_counts_pos F hq y₀
  refine ⟨selReservoir_nonempty z₀ ?_, diagReservoir_nonempty d₀ ?_,
    selReservoir_disjoint_diagReservoir, selReservoirF_row_mass F q₂ Y hq y₀,
    diagReservoirF_row_mass F q₂ Y hq y₀,
    protectedReservoirsF_row_mass F q₂ Y hq y₀, reservoirs_card_add⟩
  · exact Nat.mul_pos hM hD
  · exact Nat.mul_pos hM hS

/-- **`09:1370`, "Each outer coordinate contains two protected row reservoirs",
transcribed per coordinate.**

At every outer coordinate `i in [q]` of `U = Int_q(N)` (`09:105--109`) the two
copies are disjoint, and each carries exactly its reservoir's row count -- so
"two ... each of mass `mu_P` relative to the `m` rows of one copy of `N`" is
literally true of the built objects at each coordinate, not only globally.  The
per-coordinate counts are the banked `RetentionSupply.refBlock_card`, consumed by
pin. -/
theorem reservoirBlocks_at_each_coordinate (F : FiniteSlots.Stage1SlotBinding)
    (q₂ : ℕ) (Y : Type*) [Fintype Y] [DecidableEq Y] {q : ℕ} (i : Fin q) :
    (refBlock (selReservoirF F q₂ Y) i).card = (selReservoirF F q₂ Y).card ∧
      (refBlock (diagReservoirF F q₂ Y) i).card = (diagReservoirF F q₂ Y).card ∧
      Disjoint (refBlock (selReservoirF F q₂ Y) i)
        (refBlock (diagReservoirF F q₂ Y) i) :=
  ⟨refBlock_card _ i, refBlock_card _ i,
    refBlock_disjoint_of_disjoint selReservoir_disjoint_diagReservoir i⟩

/-- **HYPOTHESIS CONSISTENCY, and the readout FIRING at the paper's reservoirs.**

The three binders of `protectedMassAt_singleton_readout` -- `0 < m` and the two
frozen masses `|R| = mu_P m` -- are not merely jointly satisfiable in principle:
at the paper's own carriers and multiplicities they are simultaneously
**theorems** (`card_ProtColsFrozen_pos`, `selReservoirF_card_eq_muP_mul`,
`diagReservoirF_card_eq_muP_mul`), for every legal `(F, q_2, Y)`.

So the frozen reservoir readout `P_v({j}) = mu_P (d_0 + d_1)` holds at the
paper's reservoirs for an **arbitrary** alleged protocol, an **arbitrary**
retained row set and an **arbitrary** frontier route -- no hypothesis of the
readout has to be assumed by a consumer, and no pair of them is contradictory.

The remaining generality (`Rset`, `P`, `p` arbitrary) is exactly the deferred
half of the canonical-inhabitation obligation: the paper's *own* `Rset` and `P`
are the retained matrix `U'` and the alleged protocol of `09:1188--1193` at the
materialized schedule, which are not built. -/
theorem readout_fires_at_the_paper_reservoirs
    (F : FiniteSlots.Stage1SlotBinding) {q₂ : ℕ} {Y : Type*} [Fintype Y]
    [DecidableEq Y] (hq : 0 < q₂) (y₀ : Y) {q : ℕ} {Yc Zc : Type*}
    {Rset : Finset (Fin 1 × (Fin q × ProtColsFrozen F q₂ Y))}
    (P : Protocol {a // a ∈ Rset} Yc Zc) (i : Fin q) (p : List Bool) :
    protectedMassAt P (selReservoirF F q₂ Y) (diagReservoirF F q₂ Y)
        (Fintype.card (ProtColsFrozen F q₂ Y)) ({i} : Finset (Fin q)) p
      = muP * (reservoirDensity P (selReservoirF F q₂ Y) i p
          + reservoirDensity P (diagReservoirF F q₂ Y) i p) :=
  protectedMassAt_singleton_readout P (card_ProtColsFrozen_pos F q₂ Y hq y₀)
    (selReservoirF_card_eq_muP_mul F q₂ Y hq y₀)
    (diagReservoirF_card_eq_muP_mul F q₂ Y hq y₀) i p

/-- **The counting spine's `donorMass` at the paper's reservoirs.**

`ProtectedEarlyClosure.donorMass_eq_reservoirs` with **all three** of its mass
binders discharged at the frozen carriers; only `09:1519--1520`'s injectivity of the
donor reindexing survives, which is a fact about the routed system and not about
the reservoirs.  This is the exact form the banked
`WrapperProtectedEarly.earlyProtectedClosure` reads its `D_mass = sum_j d_j`
from, and no inequality of that lemma is asserted here. -/
theorem donorMass_at_the_paper_reservoirs
    (F : FiniteSlots.Stage1SlotBinding) {q₂ : ℕ} {Y : Type*} [Fintype Y]
    [DecidableEq Y] (hq : 0 < q₂) (y₀ : Y) {q : ℕ} {Yc Zc ι V : Type*}
    {Rset : Finset (Fin 1 × (Fin q × ProtColsFrozen F q₂ Y))}
    (P : Protocol {a // a ∈ Rset} Yc Zc) (node : V → List Bool)
    (donor : ι → Fin q) (J₀ : Finset ι) (v : V)
    (hinj : ∀ i ∈ J₀, ∀ j ∈ J₀, donor i = donor j → i = j) :
    donorMass
        (systemPv P node donor (selReservoirF F q₂ Y) (diagReservoirF F q₂ Y)
          (Fintype.card (ProtColsFrozen F q₂ Y))) J₀ v
      = muP * ((∑ i ∈ J₀.image donor,
            reservoirDensity P (selReservoirF F q₂ Y) i (node v))
          + (∑ i ∈ J₀.image donor,
            reservoirDensity P (diagReservoirF F q₂ Y) i (node v))) :=
  donorMass_systemPv P node donor (card_ProtColsFrozen_pos F q₂ Y hq y₀)
    (selReservoirF_card_eq_muP_mul F q₂ Y hq y₀)
    (diagReservoirF_card_eq_muP_mul F q₂ Y hq y₀) J₀ v hinj

end Inhabitation

section Probe

/-- **NON-FIDELITY SMOKE PROBE (BEYOND-PAPER on its protocol half).**

*What is the paper's, and what is ours.*  The reservoir half is the paper's:
`R_Sigma`, `R_D`, their carriers, their multiplicities and their mass `mu_P` are
Sections 1--2 at the frozen instance, and the two mass hypotheses of Section 3
are discharged here by *theorems* rather than assigned.  The protocol half is
ours and the paper never visits it: the alleged protocol is a leaf, the retained
row set is everything, and the node is the root.  It is therefore **not** the
paper's instance of `protectedMassAt` and never discharges the deferred
canonical-inhabitation obligation registered above.

*What it does establish.*  That `protectedMassAt` is not vacuous or identically
zero at legal reservoir data, and that its value at full retention is exactly
what `08:133`'s `tau = 2 mu_P` predicts for `|J_0|` donors: the mass functional
and the frozen mass constants agree numerically at a point where both can be
evaluated.

*Non-degeneracy of the parameter values.*  Nothing is chosen to make the
arithmetic work: `q_2 > 0` and the two carrier witnesses are the same legality
inputs Section 2 needs, and no numeral appears in the statement. -/
theorem protectedMass_probe_full_retention (F : FiniteSlots.Stage1SlotBinding)
    {q₂ : ℕ} {Y : Type*} [Fintype Y] [DecidableEq Y] (hq : 0 < q₂) (y₀ : Y)
    {q : ℕ} (i : Fin q) (z : Bool) :
    protectedMassAt
        (Protocol.leaf (X := {a // a ∈ (Finset.univ :
            Finset (Fin 1 × (Fin q × ProtColsFrozen F q₂ Y)))}) (Y := Unit) z)
        (selReservoirF F q₂ Y) (diagReservoirF F q₂ Y)
        (Fintype.card (ProtColsFrozen F q₂ Y)) ({i} : Finset (Fin q))
        ([] : List Bool)
      = muP + muP := by
  classical
  have hm : 0 < Fintype.card (ProtColsFrozen F q₂ Y) :=
    card_ProtColsFrozen_pos F q₂ Y hq y₀
  have hmR : (0 : ℝ) < ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℝ) := by
    exact_mod_cast hm
  have hSig := selReservoirF_card_eq_muP_mul F q₂ Y hq y₀
  have hD := diagReservoirF_card_eq_muP_mul F q₂ Y hq y₀
  have hcount : ∀ Res : Finset (ProtColsFrozen F q₂ Y),
      (rowsAt
          (Protocol.leaf (X := {a // a ∈ (Finset.univ :
              Finset (Fin 1 × (Fin q × ProtColsFrozen F q₂ Y)))}) (Y := Unit) z)
          (retainedRefRows Finset.univ Res i) ([] : List Bool)).card
        = Res.card := by
    intro Res
    rw [rowsAt_nil, retainedRefRows_card_eq, Finset.univ_inter, refBlock_card]
  rw [protectedMassAt, Finset.sum_singleton, hcount, hcount, hSig, hD]
  field_simp

end Probe

/-! ## Section 6  Statement poles

A green build sees neither of these.  Each records that a hypothesis or a
conclusion of the sections above is load-bearing. -/

section Poles

variable {Om Sg Dg : Type*} {w₀ wSg wD : ℕ}

/-- **Statement pole (`R_Sigma` is a proper subset of `Rows(N)`).**  As soon as
the base reservoir is inhabited with positive multiplicity -- which
`eq:protected-multiplicities` supplies -- the selector reservoir misses a row of
`N`.  So "mass `mu_P`" in `09:1372` is a statement about a genuine *part* of the
row carrier, and an encoding in which `R_Sigma` were all of `Rows(N)` would be
excluded here rather than pass silently.  General. -/
theorem selReservoir_ne_univ [Fintype Om] [Fintype Sg] [Fintype Dg] (z : Om)
    (hw : 0 < w₀) :
    selReservoir Om Sg Dg w₀ wSg wD
      ≠ (Finset.univ : Finset (ProtCols Om Sg Dg w₀ wSg wD)) := by
  intro h
  have hmem : refIncl (z, (⟨0, hw⟩ : Fin w₀))
      ∈ selReservoir Om Sg Dg w₀ wSg wD := by
    rw [h]
    exact Finset.mem_univ _
  rw [mem_selReservoir] at hmem
  obtain ⟨z', hz'⟩ := hmem
  simp [selResIncl, refIncl] at hz'

/-- **Statement pole (the frozen mass is load-bearing in the readout).**

`protectedMassAt_singleton_readout` needs `|R| = mu_P m` for *both* reservoirs.
Drop it and the readout is false: at a donor whose reservoir rows are all
retained, the left-hand side is `(|R_Sigma| + |R_D|)/m` while the right-hand side
is `2 mu_P`, and those differ as soon as the reservoirs do not have the frozen
mass.  This exhibits the failure at the cleanest such point -- a single reservoir
row per type against a two-row copy of `N` -- so the hypothesis cannot be
weakened to "some positive mass".

Stated as an inequality between the two *expressions* of the readout at explicit
cardinalities; it is a rejection probe and claims **no** schedule legality for
its numbers (category (3) of the defined-vs-free rule). -/
theorem protectedMass_readout_needs_the_mass :
    ((1 : ℝ) + 1) / 2 ≠ muP * (1 + 1) := by
  have hmu : muP = 1 / 184 := rfl
  rw [hmu]
  norm_num

end Poles

end EthInapproximability.ParameterizedNP.ProtectedRowReservoirs
