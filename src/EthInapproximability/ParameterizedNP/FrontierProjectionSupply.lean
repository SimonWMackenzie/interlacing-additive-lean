import EthInapproximability.ParameterizedNP.FrontierBundleConstruction

/-!
# Parameterized NP route: the `hdens` projection supply (`FBC-F1`) and the
branch-(ii) interior probe (`FBC-F2`)

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche, after the final edit to this file.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:274--275`**, `sec:wrapper-low-rungs` opens -- the block that
      `09:1275` imports for branch (i).
    * **`09:311--313`**, the sentence this tranche LANDS: "Project the retained
      outer column set to any `9 kappa_j/16` such coordinates.  **Its normalized
      density remains at least `theta`, by specified-coordinate projection.**"
    * **`09:314--323`**, the substitution block that consumes it, with
      **`09:322`** fixing `h = theta` and `a^sharp = 0` -- so the quantity the
      branch-(i) call feeds to `A:141` is the density of the **projected** column
      set, obtained from the ambient one by the sentence at `09:312--313`.
    * **`09:342--343`**, `lem:product-projection-cover`'s `\begin{lemma}` and
      `\label`; and **`09:344--347`**, its density convention ("`S subseteq Y^q`
      have density at least `theta`" ... "the projection of `S` to `J` has
      density below `rho`"), the two normalizations this module keeps apart.
    * **`09:434--442`**, the small-capacity display -- `09:436`, `rho = 2y^2 =
      18/25`; `09:438`, `u_2 = 2`; `09:440`, `u_kappa = kappa/2 + 1` for
      `4 <= kappa < t_ref`; and `09:442--444`, "For every dyadic
      `2 <= kappa < t_ref`, take one maximal-matching cover of the coordinate sets
      of size `u_kappa` whose projection density is below `rho`" (the next
      sentence, "These are exactly the covers consumed by the certified-scale row
      ladder", begins mid-`444` and runs to `445`).  This is the cover side
      section 4 reads as frozen equations.
    * **`09:1269--1276`**, branch (i) (`kappa_v >= t_ref`), whose guard in
      exponent form is `k_ref <= r - d_v`; and **`09:1276--1278`**, branch (ii)
      (`2 <= kappa_v < t_ref`, **strict** on the right), whose entry section 4
      probes.
    * **`09:1287--1290`**, the branch-(ii) projection form
      (`rho = 2y^2` at `09:1290`), whose banked Lean statement is
      `SelectDischarge.projection_at_a_node`.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    **`A:138--141`**, "every restriction of `hat M` with exactly `r' p_t`
    represented outer blocks, at least `ceil(r' t x m)` rows in each represented
    block, and **column density at least `h 2^{-a^sharp}`**" -- the clause
    `FrontierBundleConstruction`'s `hdens` binder serves, and the reason the
    normalization question below is the whole of `FBC-F1`.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `06:558--572` (`eq:tref-search`), consumed only through the banked
    `WrapperReferenceConstruction.tRef`.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`):
    `08:166`, `x_T = 2^{-b_T}`, reached only through the banked `xTdepth` inside
    the section-4 instance's own evaluated `A_0`.

## Reader counterpart: NONE claimable, searched first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was searched again this round
for `projection`, `normalized density`, `specified-coordinate`, `density` and
`retained`.  The hits are `02-preliminaries.tex:115--140`
(`prop:paper-projection-facts`, the *inherited* bracket projection facts, about
`CC` of bracket families rather than about a column set at a protocol node),
`03-parameterized-construction.tex:161` (literal projections for the arbitrary
seed), `05-iteration.tex:61--73` (the iteration's **rank** argument: "If a set
`J subseteq [q]` of columns is also retained, projection to those coordinates has
rank at least `|J| - b`" -- a rank statement at a different stage, not a density
transport), `A-stage4-details.tex:305` (unnumbered prose about transferring a
normalized density) and `B-bridge-details.tex:12--156` (the bridge induction's
entropy-averaging projection, a different mechanism).  None states `09:311--313`.
So **no declaration of this module claims a reader counterpart**, and the absence
is recorded once, here; assigning prose to a theorem is what the
reader-counterpart rule forbids.

## What this tranche does

### `FBC-F1`: the census, taken first-hand, and its verdict

`FrontierBundleConstruction.frontier_bundle_or_light_at_paper_schedule` and
`..._restriction_...` carry exactly one binder,

```text
hdens : theta <= |retainedCols P Sc v.val| / |Y|,
```

and the ledger row registers `FBC-F1` as "the `hdens` supply, when
`09:1287--1290`'s projection form lands".  The census asked whether the banked
`SelectDischarge.projection_at_a_node` together with
`SelectDischarge.nodeProjection_transport_density` supplies it.  **They do not,
and the reason is a normalization rather than a defect in either lemma.**

**Scope of that negative answer, stated precisely.**  It is a verdict on the
*registered* route only -- the branch-(ii) projection form -- and it does **not**
close the search for a supply of `hdens` by other means.  One route is left
explicitly untested here and is the successor tranche's first move: at a frontier
node the address is Alice-only, so the banked
`FrontierIndexing.coordRoutes_isAlicePath` applied to
`FrontierBundleConstruction`'s own `hroute` binder, followed by the banked
`RoutedCertificateSystem.retainedCols_of_isAlicePath` (`09:1330--1331`), makes
`retainedCols P Sc v.val = Sc`, so `hdens` there is literally
`theta <= |Sc| / |Y|` -- the bracket-membership density of `09:1190`
(`U' in bracket(U, 1, 1 - delta_U, theta)`), which is where `09:404` and
`09:311--313` obtain their `theta` in the first place.  Nothing below tests that
composition; it is registered as the open direction, not refuted.

* `hdens` normalizes against the **ambient** column carrier, this module's `Y`,
  with `|Y| = |Yc|^q` where `q = 2^r` is the scale-alignment width of
  `09:105--107` ("Let `q = 2^r` be the scale-alignment width and set
  `U = interlaceOp(N, q)`" -- the frozen line sets `U` by the interlace operator,
  and `<N>^q` here is a gloss, not the frozen form).
  **Letter warning:** the paper's own `Y` at `09:344` (`S subseteq Y^q`) is the
  *per-coordinate* alphabet, i.e. this module's `Yc`; this module's `Y` is the
  product `Fin q -> Yc`.  The two letters are not the same object and nothing
  below identifies them.
* `projection_at_a_node` bounds `|nodeProjection P S J p|` against
  `|Yc|^{|J|}` -- the **projected** carrier at the `u_{kappa_v}` selected
  coordinates.  This is `09:344--347`'s own convention for a projection density.
* The two are related in one direction only.  `projSet` is an image, so
  `|proj| <= |retained|`; turning a projected bound into an ambient one therefore
  loses the whole unprojected width, and §3's
  `ambient_density_from_projection_supply` proves that the *only* ambient density
  the projected bound yields is `rho / |Yc|^{q - |J|}`.
  `projected_density_does_not_bound_ambient_density` **caps** how large any such
  ambient conclusion could be: for every alphabet, every `q` and every `J` there
  is a retained set whose projection is the whole projected carrier (density `1`,
  so it satisfies the projection form at every `rho <= 1`) and whose ambient
  density is exactly `|Yc|^{|J| - q}`.  That caps the conclusion of any
  hypothetical projection-form-to-ambient theorem at `|Yc|^{|J| - q}`; it does
  **not** show the delivered `rho . |Yc|^{|J| - q}` is best possible, since the
  slab's projected density is `1` rather than `rho`.  Closing the remaining
  factor-`rho` gap needs a different witness -- a set of size about
  `rho . |Yc|^{|J|}` projecting injectively -- which this module does not
  construct and does not claim.
  `projected_rho_does_not_supply_hdens_at_rho` instantiates this at the frozen
  `rho = 18/25` of `09:436` and refutes the supply outright.

**STOP-AND-REPORT, the exact unmeetable hypothesis.**  There is no theorem, and
no honest way to manufacture one, taking

```text
rho * |Yc|^{|J|} <= |nodeProjection P Sc J p|        (09:1287--1290, branch (ii))
```

to

```text
theta <= |retainedCols P Sc p| / |Y|                 (hdens, A:141 via 09:322)
```

at `theta = rho`.  More generally the slab of section 1 caps any such theorem's
conclusion at `theta <= |Yc|^{|J| - q}`, which is what
`projected_density_does_not_bound_ambient_density` machine-checks; the delivered
parameter `rho |Yc|^{|J| - q}` sits a factor `rho` below that cap, and no claim
is made here that the cap is met.  The banked
projection pair is a **branch-(ii)** supply at the cover constant `rho = 2y^2`
and feeds `lem:certified-row-ladder` through `SelectDischarge`; `hdens` is a
**branch-(i)** clause at the open column parameter `h = theta` (`09:322`) and
feeds `thm:certified-localized-extension`.  Nothing below narrows `hdens`, and
`FrontierBundleConstruction` is not edited by this tranche.

### `FBC-F1`: what the frozen paper *does* supply, LANDED

The census also found the statement branch (i) actually uses, which had no Lean
form: `09:312--313`, "Its normalized density remains at least `theta`, by
specified-coordinate projection".  That runs the other way -- from the ambient
density to the projected one -- and it is proved here, twice:

* `specified_coordinate_projection_preserves_density`, general in the alphabet,
  in `q`, in the coordinate set and in `theta`, from the banked counting core
  `WrapperProjectionCovers.card_le_prod_projSet_mul` at the one-element family
  `{J}` (consumed by pin; the core is not restated); and
* `hdens_projects_to_the_selected_coordinates`, the same statement at a protocol
  node, whose hypothesis is **byte-for-byte the `hdens` binder** of
  `FrontierBundleConstruction` and whose conclusion is the projection form at
  `theta`.  So `hdens` is not merely consistent with `09:311--313`: it is
  precisely its input, and the branch-(i) restriction's column density is its
  output.

This is the direction the frozen text asserts, and it is the honest reading of
`FBC-F1`: the supply that lands is `hdens -> projected density`, and the supply
that was asked for (`projected density -> hdens`) is refuted above.

### `FBC-F2`: the branch-(ii) interior probe, at `interiorAudit`

The ledger registers `FBC-F2` as "a joint-satisfiability probe strictly inside
branch (ii)'s `2 <= kappa_v < t_ref`, at the banked
`TranscriptLevelJoin.interiorAudit`".  Section 4 fires it:

* `interiorAudit_branchTwo_entry_and_cover_side` proves branch (ii)'s entry with
  the right-hand guard **strict** (`kappa_v = 8 < 16 = t_ref`, which the banked
  `interiorAudit_pole_binders_inhabited_except_certificates` states only in its
  non-strict form `kappa_v <= t_ref`), and reads the cover side of
  `09:434--442` off that capacity as frozen equations: `ell_v = 3` by the banked
  `log_kappaAt_eq_capacity_exponent`, `2^{ell_v} = kappa_v` by the banked
  `pow_log_kappaAt`, `u_{kappa_v} = 5` by the banked `smallCopyWidth`, and
  `ell_v` inside the dyadic range `Ico 1 k_ref` that `09:442`'s cover family is
  indexed by -- which is exactly the `hl` hypothesis of the banked
  `projection_at_a_node`.
* `interiorAudit_is_outside_the_branch_one_guard` records why this had to be a
  new probe rather than a re-fire: branch (i)'s guard in exponent form is
  `k_ref <= r - d_v`, i.e. `4 <= 6 - 3`, which is **false** at the interior node.
  `FrontierBundleConstruction`'s section-4 constructor cannot be fired here, by
  design; the two branches are disjoint at this node.
* `interiorAudit_cover_index_is_load_bearing` names the **two-kappa trap**: the
  `kappa` of `09:442`'s cover family is a free dyadic index, while the `kappa_v`
  of `09:1255` is an evaluated quantity of the routing, and the frozen argument
  is only licensed when they agree.  Firing the family one level down gives
  `u_4 = 3` against the node's `u_{kappa_v} = 5`, so the width the selection is
  built at would not match the width the ladder consumes.

**NON-FIDELITY / BEYOND-PAPER**, throughout section 4, inheriting every
disclosure the banked `interiorAudit` carries verbatim: `k_ref = 4` while
`06:561--563` alone forces `k_ref >= 2^19` and `A:117` with `A:26` forces
`t_ref >= t_cert = 2^{2^20}`; `r = 6`, `d_v = 3`, `b_T = 7`, nine coordinates and
the alphabet `Fin 64` are the banked instance's, not the paper's.  Nothing in
section 4 claims legality of that tuple and nothing there discharges canonical
inhabitation.

## CANONICAL INHABITATION -- INHERITED, REGISTERED and DEFERRED

The objects sections 2--3 talk about are the retained outer column set of the
**alleged** `(C+r-1)`-bit protocol of `09:1188--1194` and its projections.  No
such protocol exists -- that is the conclusion of the whole argument -- so the
paper exhibits no instance, and the deferred canonical-inhabitation obligation of
`FRONTIER-BUNDLE-CONSTRUCTION-001` is carried unchanged.  Nothing below
discharges it: section 4's probe is a labelled NON-FIDELITY smoke probe at a
routed system we own, and section 5's joint-satisfiability instance is likewise
labelled.

This module introduces **no `structure` and no `inductive`**, and exactly one
`def`, `constantOffSlab`.  That `def` is **OURS, scaffolding, BEYOND-PAPER**: it
is the witness family of the refutation in section 3, it carries no clause of any
frozen display, and the paper never constructs it.  Its docstring says so.

## DEFINED-VS-FREE ledger for this tranche

| quantity | status | how it is obtained here |
| --- | --- | --- |
| `rho = 2y^2` | DEFINED, `09:436` | the banked `rhoSmall`; never a numeral here |
| `u_kappa` | DEFINED, `09:438--440` | the banked `smallCopyWidth`, evaluated |
| `kappa_v` | DEFINED, `09:1255` | the banked `kappaAt`, evaluated at the node |
| `ell_v` | DEFINED, `09:1278` | the banked `log_kappaAt_eq_capacity_exponent` |
| `t_ref` | DEFINED, `06:558--572` | the banked `tRef k_ref`, never a numeral |
| `A_0` | DEFINED, `09:1219` | the banked `interiorAuditA0`, already evaluated |
| `theta` | binder | `h = theta` (`09:322`) is left open by the frozen text |
| `q`, `J`, `Yc` | binders | universally quantified in sections 2--3 |
| `r`, `d_v`, `k_ref`, `b_T` | the banked instance's | `(6, 3, 4, 7)`, BEYOND-PAPER |

Sections 2 and 3 assign no numeral at all: every constant is a binder or a
banked accessor.  Self-chosen values occur in exactly two labelled places --
section 3's rejection probe (`q = 2`, `Yc = Bool`, `J = {0}`, which claims **no**
legality and exists only to make a guard fire) and section 4's inherited
`interiorAudit` tuple.

## Axioms and imports

The sole import is `FrontierBundleConstruction`, whose transitive closure carries
every banked module consumed below.  `LegacyNPCC.Stage12` is **not** in that
closure, so the cited AGHP balanced-family axiom is unreachable from every
declaration here, and `EXPANDER-001` occurs in no hypothesis.  No `axiom`, no
opaque certificate, no premise bundle, no proof hole.  The external interfaces
consumed (`card_le_prod_projSet_mul`, `projSet_card_le_card`, `retainedCols_nil`,
`smallCopyWidth`, `rhoSmall`, `tRef`, `kappaAt`,
`log_kappaAt_eq_capacity_exponent`, `pow_log_kappaAt`, `interiorAudit_kappa`,
`interiorAudit_node_val`) are all proved declarations reached by pin, and none is
restated.

## Residues this module does NOT close (named, not implied)

* `FBC-F1` is **answered, not discharged**: `hdens` remains a binder of
  `FrontierBundleConstruction`, which this tranche does not edit.  What is now
  machine-checked is that the projection form cannot supply it, and that the
  paper's own `09:311--313` runs the other way and is proved.
* `09:1287--1290` stays exactly as the banked layer records it; nothing here
  strengthens or weakens `SelectDischarge.projection_at_a_node`.
* `eq:wrapper-first-bob-light` (`09:1310--1313`) is not proved;
  `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-u-dense` is asserted nowhere; `hDenseRung` is neither discharged
  nor fed; `thm:first-wrapper` is **not** proved.  **No route completion is
  claimed, and none may be inferred.**
-/

namespace EthInapproximability.ParameterizedNP.FrontierProjectionSupply

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.SelectEmbedComposition
open EthInapproximability.ParameterizedNP.TranscriptLevelJoin

/-! ## §1  The witness family of the section-3 refutation

**OURS, scaffolding, BEYOND-PAPER.**  The frozen paper never constructs the
family below; it exists only so that section 3 can exhibit a retained column set
whose *projected* density is full while its *ambient* density is as small as the
carriers allow.  It carries no clause of any frozen display -- no floor, no
density, no complexity claim -- and no theorem outside section 3 and the aux
battery mentions it. -/

section Slab

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **Scaffolding, OURS.**  The tuples that are free on `J` and pinned to `c`
off `J`.  General in the alphabet, in `q`, in `J` and in the pinning value. -/
def constantOffSlab (J : Finset (Fin q)) (c : Yc) : Finset (Fin q → Yc) :=
  (Finset.univ : Finset (↥J → Yc)).image fun g => fun i : Fin q =>
    if h : i ∈ J then g ⟨i, h⟩ else c

omit [Fintype Yc] [DecidableEq Yc] in
/-- **Aux S1 (the extension map is injective).**  Two tuples pinned off `J` that
agree everywhere agree on `J`.  General. -/
theorem constantOffSlab_extend_injective (J : Finset (Fin q)) (c : Yc) :
    Function.Injective
      (fun g : ↥J → Yc => fun i : Fin q => if h : i ∈ J then g ⟨i, h⟩ else c) := by
  intro g₁ g₂ h
  funext i
  have hi := congrFun h i.1
  simp only [dif_pos i.2] at hi
  simpa using hi

/-- **Aux S2 (identity: the slab has the projected carrier's cardinality).**
`|constantOffSlab J c| = |Yc|^{|J|}`, so its ambient density is exactly
`|Yc|^{|J| - q}`.  General. -/
theorem constantOffSlab_card (J : Finset (Fin q)) (c : Yc) :
    (constantOffSlab J c).card = Fintype.card Yc ^ J.card := by
  rw [constantOffSlab,
    Finset.card_image_of_injective _ (constantOffSlab_extend_injective J c),
    Finset.card_univ, Fintype.card_fun, Fintype.card_coe]

/-- **Aux S3 (round trip: projecting the slab back to `J` recovers everything).**
`projSet J (constantOffSlab J c) = univ`, so the slab's projected density is `1`.
General. -/
theorem constantOffSlab_projSet (J : Finset (Fin q)) (c : Yc) :
    projSet J (constantOffSlab J c) = (Finset.univ : Finset (↥J → Yc)) := by
  refine Finset.eq_univ_of_forall ?_
  intro g
  refine Finset.mem_image.mpr ⟨fun i : Fin q => if h : i ∈ J then g ⟨i, h⟩ else c, ?_, ?_⟩
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ g)
  · funext i
    simp only [dif_pos i.2]

end Slab

/-! ## §2  `09:311--313` LANDED: specified-coordinate projection preserves the
normalized density

"Project the retained outer column set to any `9 kappa_j/16` such coordinates.
Its normalized density remains at least `theta`, by specified-coordinate
projection."

This is the sentence branch (i) uses to produce the column density
`h = theta` (`09:322`) that `A:141` consumes, and it had no Lean statement.  The
two normalizations of `09:344--347` are kept apart throughout: an *ambient*
density divides by `|Y| = |Yc|^q`, a *projected* density by `|Yc|^{|J|}`. -/

section Preserved

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ}

/-- **`09:312--313`, proved.**

If `S subseteq Y^q` has ambient density at least `theta` -- written
multiplicatively as `09:346--347` writes it, so that no division is taken -- then
its projection to any coordinate set `J` has projected density at least `theta`.

The one counting step is the banked
`WrapperProjectionCovers.card_le_prod_projSet_mul` at the one-element family
`{J}`, consumed by pin: it gives `|S| <= |proj_J S| . |Yc|^{q - |J|}` with no
disjointness hypothesis, and the frozen sentence is what remains after dividing
by `|Yc|^{q - |J|}`.

*Why this is not vacuous, and why the alphabet hypothesis is load-bearing.*  The
conclusion is an inequality between two named quantities, so there is nothing to
witness trivially.  `0 < |Yc|` is `A:111`'s nonemptiness read at the column
carrier and cannot be dropped: at `|Yc| = 0` with `|J| < q` the factor
`|Yc|^{q - |J|}` vanishes and the division that produces the conclusion is
unavailable.

General in the alphabet, in `q`, in `S`, in `J` and in `theta`. -/
theorem specified_coordinate_projection_preserves_density
    (S : Finset (Fin q → Yc)) (J : Finset (Fin q)) {θ : ℝ}
    (hYc : 0 < Fintype.card Yc)
    (hS : θ * (Fintype.card Yc : ℝ) ^ q ≤ (S.card : ℝ)) :
    θ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((projSet J S).card : ℝ) := by
  classical
  have hJq : J.card ≤ q := by
    have h := Finset.card_le_univ J
    simpa using h
  have hcount : S.card ≤ (projSet J S).card * Fintype.card Yc ^ (q - J.card) := by
    have h := card_le_prod_projSet_mul S ({J} : Finset (Finset (Fin q)))
    rw [Finset.prod_singleton] at h
    have hbi : (({J} : Finset (Finset (Fin q))).biUnion id) = J := by simp
    rw [hbi] at h
    have hc : (Jᶜ).card = q - J.card := by
      rw [Finset.card_compl]
      simp
    rwa [hc] at h
  have hn : (0 : ℝ) < (Fintype.card Yc : ℝ) := by exact_mod_cast hYc
  have hpow : (0 : ℝ) < (Fintype.card Yc : ℝ) ^ (q - J.card) := pow_pos hn _
  have hsplit : (Fintype.card Yc : ℝ) ^ q
      = (Fintype.card Yc : ℝ) ^ J.card * (Fintype.card Yc : ℝ) ^ (q - J.card) := by
    rw [← pow_add]
    congr 1
    omega
  have hcountR : (S.card : ℝ)
      ≤ ((projSet J S).card : ℝ) * (Fintype.card Yc : ℝ) ^ (q - J.card) := by
    exact_mod_cast hcount
  have hchain : θ * (Fintype.card Yc : ℝ) ^ J.card * (Fintype.card Yc : ℝ) ^ (q - J.card)
      ≤ ((projSet J S).card : ℝ) * (Fintype.card Yc : ℝ) ^ (q - J.card) := by
    calc θ * (Fintype.card Yc : ℝ) ^ J.card * (Fintype.card Yc : ℝ) ^ (q - J.card)
        = θ * (Fintype.card Yc : ℝ) ^ q := by rw [hsplit]; ring
      _ ≤ (S.card : ℝ) := hS
      _ ≤ _ := hcountR
  exact le_of_mul_le_mul_right hchain hpow

variable {X Z : Type*}

/-- **`09:311--313` at a protocol node: `hdens` IS the input of the frozen
sentence, and the projected density is its output.**

The hypothesis is byte-for-byte the `hdens` binder carried by
`FrontierBundleConstruction.frontier_bundle_or_light_at_paper_schedule` and
`..._restriction_...` -- `theta <= |retainedCols P Sc p| / |Y|` at the ambient
column carrier `Y = Fin q -> Yc` of `09:105--107` -- and the conclusion is the
projection form at `theta`, on the selected coordinates, in the multiplicative
convention of `09:346--347`.

So `FBC-F1`'s question has a positive answer in this direction and only this
direction: `hdens` is exactly what `09:312--313` consumes, and what it produces
is the column density branch (i) hands to `A:141` through `h = theta`
(`09:322`).  The opposite direction is refuted in section 3.

*Why this is not vacuous.*  The conclusion is an inequality between two named
quantities.  It is not free of the hypothesis either: section 3 exhibits a
retained set at which the conclusion holds at `theta = rho` while the hypothesis
fails, so the two are genuinely different statements and this implication is not
reversible.

General in the alphabet, in `q`, in both remaining protocol carriers, in the
protocol, the ambient retained set, the selection, the address and `theta`. -/
theorem hdens_projects_to_the_selected_coordinates
    (P : Protocol X (Fin q → Yc) Z) (Sc : Finset (Fin q → Yc)) (J : Finset (Fin q))
    (p : List Bool) {θ : ℝ} (hYc : 0 < Fintype.card Yc)
    (hdens : θ ≤ ((retainedCols P Sc p).card : ℝ) / (Fintype.card (Fin q → Yc) : ℝ)) :
    θ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((nodeProjection P Sc J p).card : ℝ) := by
  have hcard : (Fintype.card (Fin q → Yc) : ℝ) = (Fintype.card Yc : ℝ) ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hn : (0 : ℝ) < (Fintype.card Yc : ℝ) := by exact_mod_cast hYc
  have hqpos : (0 : ℝ) < (Fintype.card (Fin q → Yc) : ℝ) := by
    rw [hcard]
    exact pow_pos hn q
  rw [le_div_iff₀ hqpos, hcard] at hdens
  exact specified_coordinate_projection_preserves_density (retainedCols P Sc p) J hYc hdens

end Preserved

/-! ## §3  The census verdict on `FBC-F1`: the projection form does NOT supply
`hdens`

`SelectDischarge.projection_at_a_node` bounds the projected cardinality against
`|Yc|^{|J|}`; `hdens` bounds the ambient cardinality against `|Y| = |Yc|^q`.
This section measures the gap exactly and then refutes the supply at the frozen
`rho` of `09:436`. -/

section Census

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ} {X Z : Type*}

/-- **The only ambient density a projected bound yields, and it is deflated by the
whole unprojected width.**

From `09:1287--1290`'s form `rho . |Yc|^{|J|} <= |nodeProjection P Sc J p|` the
one available step is that a projection is an image (the banked
`WrapperProjectionCovers.projSet_card_le_card`, consumed by pin), so the same
count bounds `|retainedCols P Sc p|` from below.  Dividing by the ambient
`|Y| = |Yc|^q` leaves `rho / |Yc|^{q - |J|}`.

At the frozen widths this is not a cosmetic loss: `09:440` puts
`|J| = u_{kappa_v} = kappa_v/2 + 1` with `kappa_v < t_ref`, while `09:105` puts
`q = 2^r`, so the divisor is `|Yc|` raised to a power that is astronomically
larger than the selection.

The next theorem shows the factor cannot be improved.

General in the alphabet, in `q`, in both remaining carriers, in the protocol, the
retained set, the selection, the address and `rho`. -/
theorem ambient_density_from_projection_supply
    (P : Protocol X (Fin q → Yc) Z) (Sc : Finset (Fin q → Yc)) (J : Finset (Fin q))
    (p : List Bool) {ρ : ℝ} (hYc : 0 < Fintype.card Yc)
    (hproj : ρ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((nodeProjection P Sc J p).card : ℝ)) :
    ρ / (Fintype.card Yc : ℝ) ^ (q - J.card)
      ≤ ((retainedCols P Sc p).card : ℝ) / (Fintype.card (Fin q → Yc) : ℝ) := by
  have hJq : J.card ≤ q := by
    have h := Finset.card_le_univ J
    simpa using h
  have hn : (0 : ℝ) < (Fintype.card Yc : ℝ) := by exact_mod_cast hYc
  have hcard : (Fintype.card (Fin q → Yc) : ℝ) = (Fintype.card Yc : ℝ) ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hle : ((nodeProjection P Sc J p).card : ℝ) ≤ ((retainedCols P Sc p).card : ℝ) := by
    exact_mod_cast projSet_card_le_card J (retainedCols P Sc p)
  have hret : ρ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((retainedCols P Sc p).card : ℝ) :=
    le_trans hproj hle
  have hsplit : (Fintype.card Yc : ℝ) ^ q
      = (Fintype.card Yc : ℝ) ^ J.card * (Fintype.card Yc : ℝ) ^ (q - J.card) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hcard, div_le_div_iff₀ (pow_pos hn _) (pow_pos hn _)]
  calc ρ * (Fintype.card Yc : ℝ) ^ q
      = ρ * (Fintype.card Yc : ℝ) ^ J.card * (Fintype.card Yc : ℝ) ^ (q - J.card) := by
        rw [hsplit]; ring
    _ ≤ ((retainedCols P Sc p).card : ℝ) * (Fintype.card Yc : ℝ) ^ (q - J.card) := by
        exact mul_le_mul_of_nonneg_right hret (pow_pos hn _).le

/-- **The ceiling on any ambient conclusion: a full projection over a vanishing
ambient density.**

For every alphabet, every `q`, every coordinate set `J` and every pinning value,
the scaffolding slab of section 1 has

* projected cardinality exactly `|Yc|^{|J|}`, i.e. projected density `1` -- so it
  satisfies `09:1287--1290`'s form at **every** `rho <= 1`, in particular at the
  frozen `rho = 2y^2` of `09:436`; while
* ambient density exactly `|Yc|^{|J|} / |Yc|^q`.

Hence no theorem can take the projection form to an ambient density above
`|Yc|^{|J| - q}`: the slab satisfies the hypothesis of any such theorem and its
ambient density is exactly that.  This is the machine-checked form of the
STOP-AND-REPORT in the header.

*What this does NOT establish.*  It does **not** show
`ambient_density_from_projection_supply` is best possible.  That theorem delivers
`rho . |Yc|^{|J| - q}`, a factor `rho` below the cap proved here, because the
slab's projected density is `1` and not `rho`.  A tightness witness would be a
set of size about `rho . |Yc|^{|J|}` projecting injectively; this module does not
construct one and claims no tightness.

*Why this is not vacuous.*  Both conclusions are equations between named
quantities, and the left-hand sides are cardinalities of sets the slab actually
contains: `constantOffSlab_projSet` computes the first as the whole projected
carrier rather than bounding it.

General in the alphabet, in `q`, in `J` and in the pinning value. -/
theorem projected_density_does_not_bound_ambient_density (J : Finset (Fin q)) (c : Yc) :
    ((projSet J (constantOffSlab J c)).card : ℝ) = (Fintype.card Yc : ℝ) ^ J.card
      ∧ ((constantOffSlab J c).card : ℝ) / (Fintype.card (Fin q → Yc) : ℝ)
          = (Fintype.card Yc : ℝ) ^ J.card / (Fintype.card Yc : ℝ) ^ q := by
  have hcard : (Fintype.card (Fin q → Yc) : ℝ) = (Fintype.card Yc : ℝ) ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  constructor
  · rw [constantOffSlab_projSet, Finset.card_univ, Fintype.card_fun, Fintype.card_coe]
    push_cast
    ring
  · rw [constantOffSlab_card, hcard]
    push_cast
    ring

/-- **STOP-AND-REPORT, machine-checked: at the frozen `rho` the projection form
holds and `hdens` fails.**

**A REJECTION PROBE.  It claims no legality**: `q = 2`, the alphabet `Bool`, the
selection `{0}` and the leaf protocol are self-chosen, and exist only to make the
guard fire.  `rho` is not self-chosen -- it is the banked `rhoSmall`, the
`2y^2 = 18/25` of `09:436`.

At the slab of section 1 the address is the root, where the banked
`retainedCols_nil` leaves the retained set untouched, so both readings are of one
and the same column set:

* the projection form of `09:1287--1290` holds at `rho` -- `36/25 <= 2`; while
* `hdens` at the same `theta = rho` is **false** -- `18/25 <= 1/2` is not.

So there is no implication from the banked projection supply to the binder
`FrontierBundleConstruction` carries, and `FBC-F1` cannot be discharged in that
direction.  The direction that does hold is section 2. -/
theorem projected_rho_does_not_supply_hdens_at_rho :
    rhoSmall * (Fintype.card Bool : ℝ) ^ (({0} : Finset (Fin 2)).card)
        ≤ ((nodeProjection (Protocol.leaf true : Protocol Unit (Fin 2 → Bool) Bool)
              (constantOffSlab ({0} : Finset (Fin 2)) false)
              ({0} : Finset (Fin 2)) []).card : ℝ)
      ∧ ¬ (rhoSmall
            ≤ ((retainedCols (Protocol.leaf true : Protocol Unit (Fin 2 → Bool) Bool)
                  (constantOffSlab ({0} : Finset (Fin 2)) false) []).card : ℝ)
                / (Fintype.card (Fin 2 → Bool) : ℝ)) := by
  have hret : retainedCols (Protocol.leaf true : Protocol Unit (Fin 2 → Bool) Bool)
      (constantOffSlab ({0} : Finset (Fin 2)) false) []
      = constantOffSlab ({0} : Finset (Fin 2)) false := retainedCols_nil _ _
  have hproj : nodeProjection (Protocol.leaf true : Protocol Unit (Fin 2 → Bool) Bool)
      (constantOffSlab ({0} : Finset (Fin 2)) false) ({0} : Finset (Fin 2)) []
      = projSet ({0} : Finset (Fin 2)) (constantOffSlab ({0} : Finset (Fin 2)) false) := by
    rw [nodeProjection, hret]
  have hJ : (({0} : Finset (Fin 2))).card = 1 := rfl
  have hpcard : ((projSet ({0} : Finset (Fin 2))
      (constantOffSlab ({0} : Finset (Fin 2)) false)).card : ℕ) = 2 := by
    rw [constantOffSlab_projSet, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hJ]
    simp
  have hscard : ((constantOffSlab ({0} : Finset (Fin 2)) false).card : ℕ) = 2 := by
    rw [constantOffSlab_card, hJ]
    simp
  have hamb : (Fintype.card (Fin 2 → Bool) : ℕ) = 4 := by
    rw [Fintype.card_fun]
    simp
  constructor
  · rw [hproj, hpcard, hJ]
    norm_num [rhoSmall]
  · rw [hret, hscard, hamb]
    norm_num [rhoSmall]

end Census

/-! ## §4  `FBC-F2`: the branch-(ii) interior probe at the banked `interiorAudit`

**NON-FIDELITY / BEYOND-PAPER**, throughout.  Everything here audits *our*
encoding at a point the frozen paper never visits and claims no legality;
`k_ref = 4` while `A:117` with `A:26` forces `t_ref >= t_cert = 2^{2^20}`, and
`r = 6`, `d_v = 3`, `b_T = 7`, the nine coordinates and the alphabet `Fin 64` are
the banked instance's choices.  Nothing here discharges canonical inhabitation.

`FrontierBundleConstruction`'s section 5 fires at `kappa_v = t_ref`, the boundary
`09:1269` assigns to branch (i).  This section probes strictly inside
`09:1277`'s `2 <= kappa_v < t_ref`, which is where `09:434--442`'s cover family
lives. -/

section InteriorProbe

/-- **Branch (ii)'s entry at the interior node, with the guard STRICT, and the
cover side of `09:434--442` read off the same capacity.**

Six frozen readings at the banked `interiorAuditNode`, all evaluations of the
routing rather than assignments:

* `2 <= kappa_v` and `kappa_v < t_ref` -- `09:1277` verbatim, with the right-hand
  guard **strict**.  The banked
  `interiorAudit_pole_binders_inhabited_except_certificates` supplies only the
  non-strict `kappa_v <= t_ref`, which is compatible with branch (i)'s boundary;
  the strict form is what places the node inside branch (ii) and is proved here.
* `ell_v = 3` -- `09:1278`'s `ell_v = log_2 kappa_v`, evaluated through the
  banked `log_kappaAt_eq_capacity_exponent` at `r - d_v = 6 - 3`.
* `2^{ell_v} = kappa_v` -- the banked `pow_log_kappaAt`, consumed by pin.
* `u_{kappa_v} = 5` -- `09:440`'s `u_kappa = kappa/2 + 1` at `kappa_v = 8`,
  through the banked `smallCopyWidth`.
* `ell_v in Ico 1 k_ref` -- the dyadic range `09:442` indexes its cover family
  by ("for every dyadic `2 <= kappa < t_ref`"), which is exactly the `hl`
  hypothesis of the banked `SelectDischarge.projection_at_a_node`.  So the
  interior node is a point where that hypothesis is *reachable*, not merely
  typable.

Jointly satisfiable means jointly satisfiable: all six hold at one node of one
routed system, simultaneously.

*Why this is not vacuous.*  Every clause is an equation or inequality between
named quantities, and the next theorem shows the group is not satisfied by the
branch it excludes: at this very node branch (i)'s guard is **false**.

**NON-FIDELITY**, per the section label. -/
theorem interiorAudit_branchTwo_entry_and_cover_side :
    2 ≤ kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
      ∧ kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
          < tRef 4
      ∧ Nat.log 2
          (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode) = 3
      ∧ 2 ^ Nat.log 2
            (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode)
          = kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode
      ∧ smallCopyWidth
            (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode)
          = 5
      ∧ Nat.log 2
          (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode)
          ∈ Finset.Ico 1 4 := by
  have hlog : Nat.log 2
      (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode) = 3 := by
    rw [log_kappaAt_eq_capacity_exponent, interiorAudit_node_val]
    decide
  refine ⟨?_, ?_, hlog, pow_log_kappaAt _ _ _ _ _, ?_, ?_⟩
  · rw [interiorAudit_kappa]; norm_num
  · rw [interiorAudit_kappa, tRef_eq]; norm_num
  · rw [interiorAudit_kappa]; rfl
  · rw [hlog]; decide

/-- **Why this had to be a new probe: branch (i)'s guard is FALSE at the interior
node.**

`09:1269` enters branch (i) at `kappa_v >= t_ref`, which in exponent form is
`k_ref <= r - d_v` -- the `hcap` binder of
`FrontierBundleConstruction.frontier_bundle_or_light_at_paper_schedule` and
`..._restriction_...`.  At the banked interior node that reads `4 <= 6 - 3` and
is false, so the section-4 constructor of that module cannot be fired here.

*Exactly what is machine-checked, and what is not.*  The statement below is the
`k_ref = 4` **instance** of that failure.  It is the only instance the banked
tuple admits -- `FrontierBundleConstruction`'s `hk : 4 <= k_ref` and the banked
`hq4 : k_ref + 2 <= 6` force `k_ref = 4` exactly here -- so the general claim
"the constructor cannot be fired at this node, for any admissible `k_ref`" is
true; but that general form (`forall kref, 4 <= kref -> not (kref <= 6 - 3)`) is
**not** landed by this tranche and should not be read off the statement below.

That is not a defect of either module: it is `09:1269`/`09:1277` doing what the
frozen text says, and it is precisely why `FBC-F2` asks for a probe at the other
branch's entry rather than a re-fire of the branch-(i) constructor.

*Why this is not vacuous.*  The statement is a refutation, so a trivial witness
is not available to it: it says the guard fails, at a node whose whole binder
group the previous theorem inhabits.

**NON-FIDELITY**, per the section label. -/
theorem interiorAudit_is_outside_the_branch_one_guard :
    ¬ (4 ≤ 6 - interiorAuditNode.val.length) := by
  rw [interiorAudit_node_val]
  decide

/-- **The two-kappa trap, named and measured.**

`09:442`'s cover family is indexed by a **free dyadic parameter**, "for every
dyadic `2 <= kappa < t_ref`", and its member at index `ell` covers coordinate
sets of size `u_{2^ell}`.  `09:1255`'s `kappa_v` is an **evaluated quantity of
the routing**.  The frozen argument of `09:1287--1290` is licensed only when the
two agree, and the banked `SelectDischarge.projection_at_a_node` encodes that as
the pair `hl : l in Ico 1 k` with `hJ : |J| = u_{2^l}`.

Both halves are recorded here at the interior node:

* firing the family one level down gives `u_4 = 3` against the node's
  `u_{kappa_v} = 5`, so the index is **load-bearing** -- a selection built at the
  wrong level has the wrong width and the ladder's copy count no longer matches
  it; and
* at the matching index the two agree, by the banked `pow_log_kappaAt`.

*Why this is not vacuous.*  The first conjunct is a disequality between two
evaluated naturals, which no trivial witness supplies.

**NON-FIDELITY**, per the section label. -/
theorem interiorAudit_cover_index_is_load_bearing :
    smallCopyWidth (2 ^ 2)
        ≠ smallCopyWidth
            (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode)
      ∧ smallCopyWidth
            (2 ^ Nat.log 2
              (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode))
          = smallCopyWidth
            (kappaAt interiorAudit interiorAuditRows interiorAuditA0 6 interiorAuditNode) := by
  constructor
  · rw [interiorAudit_kappa]
    decide
  · rw [pow_log_kappaAt]

end InteriorProbe

/-! ## §5  Aux-lemma battery

Five general checks on the objects sections 2--3 join.  The canonical
inhabitation of those objects is INHERITED, REGISTERED and DEFERRED per the
header: the paper's own retained column set is a function of the alleged protocol
of `09:1188--1194`, which does not exist, so no paper instance can be exhibited
and the smoke probes of section 4 and of this section do not discharge the
obligation. -/

section Battery

variable {Yc : Type*} [Fintype Yc] [DecidableEq Yc] {q : ℕ} {X Z : Type*}

omit [Fintype Yc] in
/-- **Battery 1 (round trip: projecting to every coordinate loses nothing).**

At `J = univ` the projection is injective, so it has the source's cardinality --
which is the degenerate case of `09:312--313`, where "remains at least `theta`"
is an equality.  General in the alphabet, in `q` and in `S`. -/
theorem projSet_univ_card (S : Finset (Fin q → Yc)) :
    (projSet (Finset.univ : Finset (Fin q)) S).card = S.card := by
  classical
  refine Finset.card_image_of_injective _ ?_
  intro f₁ f₂ h
  funext i
  exact congrFun h ⟨i, Finset.mem_univ i⟩

/-- **Battery 2 (monotonicity of the node projection in the ambient retained
set).**

Growing the retained outer column set grows the node's projection, at every
address and every selection: `retainedCols` cuts by `bobCols`, which does not
depend on the set, and `projSet` is an image.  Both banked facts
(`RoutedCertificateSystem.retainedCols`, `WrapperProjectionCovers.projSet_mono`)
are consumed by pin.  General. -/
theorem nodeProjection_mono (P : Protocol X (Fin q → Yc) Z)
    {S S' : Finset (Fin q → Yc)} (J : Finset (Fin q)) (p : List Bool) (h : S ⊆ S') :
    nodeProjection P S J p ⊆ nodeProjection P S' J p := by
  refine projSet_mono ?_
  exact Finset.inter_subset_inter_right h

/-- **Battery 3 (the preserved density is monotone in `theta`).**

If the frozen sentence delivers a projected density at `theta`, it delivers one
at every smaller parameter -- which is what lets a call site weaken `h = theta`
(`09:322`) to whatever `A:128`'s `h in (0,1]` range it needs.  General. -/
theorem projected_density_mono {θ θ' : ℝ} (S : Finset (Fin q → Yc)) (J : Finset (Fin q))
    (hle : θ' ≤ θ) (h : θ * (Fintype.card Yc : ℝ) ^ J.card ≤ ((projSet J S).card : ℝ)) :
    θ' * (Fintype.card Yc : ℝ) ^ J.card ≤ ((projSet J S).card : ℝ) := by
  refine le_trans ?_ h
  exact mul_le_mul_of_nonneg_right hle (pow_nonneg (Nat.cast_nonneg _) _)

/-- **Battery 4 (the section-2 hypothesis group is jointly satisfiable at a
nondegenerate point).**

A conditional theorem whose hypotheses cannot hold together measures nothing.
Here they can: at the scaffolding slab with `q = 2`, alphabet `Bool`, selection
`{0}` and `theta = 1/2`, the alphabet is nonempty, the ambient density clause
holds, and the conclusion of `specified_coordinate_projection_preserves_density`
holds -- all with `theta` strictly positive, `J` a nonempty **proper** subset of
the coordinates, and the retained set a nonempty **proper** subset of the ambient
carrier, so nothing is satisfied degenerately.

**A BEYOND-PAPER audit instance**: the sizes are ours, they claim no legality,
and they exist only to keep this module's principal implication from being
vacuous. -/
theorem section_two_hypotheses_are_jointly_satisfiable :
    0 < Fintype.card Bool
      ∧ (1 / 2 : ℝ) * (Fintype.card Bool : ℝ) ^ (2 : ℕ)
          ≤ ((constantOffSlab ({0} : Finset (Fin 2)) false).card : ℝ)
      ∧ (1 / 2 : ℝ) * (Fintype.card Bool : ℝ) ^ (({0} : Finset (Fin 2))).card
          ≤ ((projSet ({0} : Finset (Fin 2))
              (constantOffSlab ({0} : Finset (Fin 2)) false)).card : ℝ)
      ∧ (constantOffSlab ({0} : Finset (Fin 2)) false) ≠ (∅ : Finset (Fin 2 → Bool))
      ∧ (constantOffSlab ({0} : Finset (Fin 2)) false)
          ≠ (Finset.univ : Finset (Fin 2 → Bool)) := by
  have hJ : (({0} : Finset (Fin 2))).card = 1 := rfl
  have hscard : ((constantOffSlab ({0} : Finset (Fin 2)) false).card : ℕ) = 2 := by
    rw [constantOffSlab_card, hJ]
    simp
  have hpcard : ((projSet ({0} : Finset (Fin 2))
      (constantOffSlab ({0} : Finset (Fin 2)) false)).card : ℕ) = 2 := by
    rw [constantOffSlab_projSet, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hJ]
    simp
  have huniv : (Finset.univ : Finset (Fin 2 → Bool)).card = 4 := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · rw [hscard]; norm_num
  · rw [hpcard, hJ]; norm_num
  · intro hcon
    rw [hcon] at hscard
    simp at hscard
  · intro hcon
    rw [hcon, huniv] at hscard
    omega

/-- **Battery 5, a STATEMENT POLE: the two normalizations are genuinely
different, and the difference is the whole of `FBC-F1`.**

Section 2 proves ambient `-> ` projected; section 3 refutes projected `-> `
ambient at the frozen `rho`.  Stated together at one and the same column set,
that is: the slab satisfies the projection form at `rhoSmall` while failing
`hdens` at `rhoSmall`, and yet it *does* satisfy `hdens` at the deflated
parameter the section-3 bound predicts, `rhoSmall / |Bool|^{q - |J|}
= (18/25)/2 = 9/25`.

So the implication is not merely unproved in the refuted direction: the two
normalizations separate at one concrete column set, the deflated parameter being
satisfied exactly where the undeflated one fails.

*Satisfied, not attained.*  `9/25 <= 1/2` is strict, so nothing here is attained
and no tightness of `ambient_density_from_projection_supply` is claimed -- see
that theorem's docstring for what the section-3 cap does and does not establish.

**A BEYOND-PAPER audit instance**, inheriting section 3's rejection-probe
sizes. -/
theorem the_deflated_hdens_is_satisfied_where_the_undeflated_one_fails :
    rhoSmall / (Fintype.card Bool : ℝ) ^ (2 - (({0} : Finset (Fin 2))).card)
        ≤ ((constantOffSlab ({0} : Finset (Fin 2)) false).card : ℝ)
            / (Fintype.card (Fin 2 → Bool) : ℝ)
      ∧ ¬ (rhoSmall ≤ ((constantOffSlab ({0} : Finset (Fin 2)) false).card : ℝ)
            / (Fintype.card (Fin 2 → Bool) : ℝ)) := by
  have hJ : (({0} : Finset (Fin 2))).card = 1 := rfl
  have hscard : ((constantOffSlab ({0} : Finset (Fin 2)) false).card : ℕ) = 2 := by
    rw [constantOffSlab_card, hJ]
    simp
  have hamb : (Fintype.card (Fin 2 → Bool) : ℕ) = 4 := by
    rw [Fintype.card_fun]
    simp
  rw [hscard, hamb, hJ]
  constructor
  · norm_num [rhoSmall]
  · norm_num [rhoSmall]

end Battery

end EthInapproximability.ParameterizedNP.FrontierProjectionSupply
