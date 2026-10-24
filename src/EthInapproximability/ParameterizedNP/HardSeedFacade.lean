import EthInapproximability.ParameterizedNP.RawLowProfileBody

/-!
# Parameterized NP route: the General Hard Seed facade, and the rung threading

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchors (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/`.
  * `sections/D-inherited-contracts.tex`, paragraph "Checked inherited
    declaration: general hard seed" (**lines 461--528**), read line by line:
    * `D:462--471` `eq:contract-hard-seed-quantifiers` -- the quantifier order
      `forall j, 2 <= j; forall delta, 0 < delta < 1/2; exists m_0, j <= m_0;
      forall m >= m_0`, "followed uniformly by all finite types `X, Y`, all
      games `f`, and all reals `b`" -> `hardSeed`;
    * `D:474--477` -- the hypothesis battery `Robust(f, delta, b)`, `1 <= b`,
      `3 <= D(f)`, `(m : R) <= b` -> the four explicit binders of `hardSeed`;
    * `D:479--487` `eq:contract-hard-seed` -- the conclusion
      `D(f) + m <= D_f((2^{j-1}+2) 2^{m-j}, 2^m 2^{-b},
      2^{-2^{(49/100) sqrt m}})` -> `hardSeedCopies`, `hardSeedRowDensity`,
      `hardSeedColumnDensity` and the conclusion of `hardSeed`;
    * `D:488--492` -- "The second argument ... is the retained *row* density.
      The third argument ... is the retained *column* density.  This
      orientation is part of the typed `D_f(p,x,z)` interface and must not be
      reversed in a compiler gate or call record." -> the two separate
      definitions and the orientation pole
      `hardSeedDensities_not_interchangeable`;
    * `D:493--495` -- "The natural subtraction `m - j` is harmless because
      `eq:contract-hard-seed-quantifiers` gives `m >= m_0 >= j`.  Every active
      call fixes `j = 5` and `delta = 1/10`." -> `contractJ`, `contractDelta`,
      `hardSeed_natSub_legal`, and the `j = 5, delta = 1/10` pin throughout;
    * `D:495--504` -- the full tail predicate `HSThreshold(r)` -> `HSThreshold`,
      with `D:504--505` ("Equation `eq:contract-hard-seed-quantifiers` proves
      that this predicate holds for at least one natural number") ->
      `hsThreshold_exists`;
    * `D:506--515` `eq:contract-hard-seed-threshold-names` -- the canonical
      fixed choice `m_HS = min{r : HSThreshold(r)}`, `t_HS = 2^{m_HS}`, and
      "Thus `m_HS` is the exponent threshold and `t_HS` is its corresponding
      width; they are not interchangeable" -> `mHS`, `tHS`, `mHS_spec`,
      `mHS_least`, `mHS_lt_tHS`;
    * `D:516--517` -- "No numerical value is required.  The least-witness
      definition pins one global constant before any game, depth, source
      instance, or promise branch is chosen." -> no numeral for `mHS` or `tHS`
      appears anywhere in this module;
    * `D:518--519` -- "At width `2^m`, the copy count in
      `eq:contract-hard-seed` is exactly `9 * 2^m / 16`." ->
      `hardSeedCopies_five_identity` and `hardSeedCopies_five_cast`;
    * `D:527--528` -- "`eq:contract-power-two` and `eq:contract-hard-seed`
      remain the ordinary-robustness endpoints used elsewhere", which is why
      the hypothesis battery here is the *ordinary* `NPCC.IsRobust` of
      `eq:contract-robust` (`D:129--147`) and not a certified-scale variant.
  * `sections/08-dense-stage4.tex`, `08:241--251` -- "Project the retained base
    columns to any `p_j` such blocks. ... The inherited General Hard Seed
    Lemma, instantiated at width `I_j`, therefore leaves a member of
    `<M_2^T, p_j, x_j, h_j^raw>` of complexity at least `D_2 + log_2 I_j`."
    -> the whole threading section: `rungSeedFamilyBound`, `RungLanding`,
    `rungSeedWitness_of_landing`, `rawLowProfile_of_landing_and_certificate`.
    The rung scalars `I_j = s/2^j`, `p_j = 9 I_j/16`, `x_j = I_j x_T`,
    `h_j^raw = 2^{-2^{0.49 sqrt(log_2 I_j)}}` are `08:168--174`, consumed by
    pin from the banked `widthI`, `blockTarget`, `rowDensity`,
    `hRawSchedule`.
  * `sections/07-one-level-construction.tex`, `eq:stage2-two-depth-certificate`
    (label line 429, display 423--430) -- `comp(M_2) = D_2`,
    `Lambda_3(M_2^T, 1, 2^{-b_2}, 3/5) >= D_2`,
    `Lambda_3(M_2^T, 1, 2^{-b_T}, 3/5) >= D_2`, with `07:431--433` ("The
    auxiliary depth `b_T` is used only in the deletion-stable and
    scale-alignment parts of the adapted Stage 4").  `07:457--462` says
    outright that the exact-complexity plus three-rung pair "say precisely that
    `Robust(f, 1/10, b_2)`" for `f = M_2^T`; the same reading at the auxiliary
    depth is the `(1/10, b_T)`-robustness certificate.  That certificate is
    **open in Lean** (ledger row `STAGE2-MODULE-001`, tranche `cc-t2e`:
    "construction layer kernel checked; neither certificate is proved"), so it
    enters here as the explicit named binder `hrob` and is never assumed
    silently.

* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`):
  * `02-preliminaries.tex` line 341, `eq:paper-hard-seed-corollary` (display
    lines 331--342): "for every power of two `t >= t_HS` divisible by `16`,
    and every robust `M` with `D = CC(M) >= 3` and `t <= 2^b`,
    `CC(B(M; 9t/16, t 2^{-b}, 2^{-2^{0.49 sqrt(log t)}})) >= D + log t`"
    -> **`hardSeedAtPin`**.  Opened and checked: it states the same fact as
    `eq:contract-hard-seed` at the pinned `j = 5` (`9t/16` is the copy count,
    `t 2^{-b}` the row density, `2^{-2^{0.49 sqrt(log t)}}` the column
    density, `D + log t` the value at `t = 2^m`).  No earlier ledger row cites
    it.
  * `02-preliminaries.tex` lines 326--328, "Fix a power of two
    `t_HS >= 16` from which the resulting fixed-surplus corollary is valid"
    -> **`tHS`** and `sixteen_le_tHS`.  This is a different item from the
    display above -- it fixes the threshold, the display states the
    conclusion -- so no reader item is assigned twice.
  * Everything else in this module (`hardSeed`, `HSThreshold`,
    `hsThreshold_exists`, `mHS`, `mHS_spec`, `mHS_least`, the copy-count and
    orientation lemmas, the rung identifications, `RungLanding`,
    `rungSeedFamilyBound`, `rungSeedWitness_of_landing`,
    `rawLowProfile_of_landing_and_certificate`, the aux battery, the
    orientation pole and the consistency probes) claims **no** reader item: the
    reader compresses
    the threading into the four prose sentences of `A-stage4-details.tex`
    lines 283--291, which the banked `RawLowProfileBody` already records as
    proof *prose* and never cites as a statement.  In particular the Stage-4
    reader display `eq:paper-protected-low` stays assigned to `rawLowProfile`
    (`STAGE4-PROTECTED-OPENING-001`) and is not reclaimed.

## What this module does, and what it deliberately does not

**Does (facade section).**  It exposes the kernel-checked vendored declaration
`NPCC.hard_seed` (`vendor/npc-cc/NPCC/Engine.lean:1724`) at the typed
`D_f(p,x,z)` interface of `D:462--487`, **consumed by pin**: the body of
`hardSeed` is exactly the inherited term, so the axiom surface is unchanged and
the statement is never re-proved and never re-axiomatized.  On top of it the
module transcribes the tail predicate `HSThreshold`, proves that it holds of at
least one natural number, and defines the canonical least witness `m_HS` and
its width `t_HS`.  **No numeral is ever chosen for either**: every consumer
takes `mHS <= m` as a hypothesis.

**Does (threading section).**  It identifies the inherited conclusion at
exponent `m = w_S - j` with the *rung bracket* of `08:244--250` on the nose --
copy count `p_j`, row density `x_j`, column density `h_j^raw` -- and then
supplies the banked `RungSeedWitness` binder of `RawLowProfileBody` from that
identification plus one named geometric binder, closing with the composed
`rawLowProfile_of_landing_and_certificate`.

**Does not.**  Two things are *not* discharged, and are carried as explicit
named binders on every theorem that needs them:

1. `hrob`, the Stage-2 `(1/10, b_T)`-robustness certificate for `M_2^T`
   (`eq:stage2-two-depth-certificate`).  Open in Lean, ledger row
   `STAGE2-MODULE-001`.
2. `RungLanding`, the *geometric* output of the discard/projection chain
   `08:220--242`: that after discarding the protected selector and diagonal
   columns, discarding the protected nonbase row reservoirs and the raw source
   rows, and projecting to `p_j` retained Stage-3 blocks, the surviving data of
   an arbitrary member of `<N,1,x_N,y/2^j>` contains a member of
   `<M_2^T, p_j, x_j, h_j^raw>` no harder than a restriction of that member.
   The banked `RawLowProfileBody` `§1`--`§3` prove the three *density*
   transports that make such a landing legal, and the two bridges
   `col_floor_of_density` / `row_floor_of_density` below convert those
   densities into the exact bracket floors; the remaining content -- the actual
   identification of the surviving carriers with a bracket member of the
   Stage-2 transpose -- needs the Stage-4 duplication geometry of
   `sec:dense-duplication`, which is not yet in Lean.  So `RungLanding` is a
   hypothesis at every use site, never an axiom, never a structure field, and
   is nowhere inhabited here.

Consequently **nothing in this module claims `lem:raw-low-profile` proved**:
`rawLowProfile_of_landing_and_certificate` is a conditional theorem whose two
open binders are named in its signature.

**Nothing banked is restated.**  `RungSeedWitness`, `rawLowProfile_body`,
`Dfamily_ge_of_seed_witnesses`, `rawLowGates_inhabited`,
`rawLowProfile_body_side_conditions_consistent`,
`widthI_eq_two_pow` are consumed **by pin** from `RawLowProfileBody`; the two
banked results this module *cites but does not consume as terms* --
`RawLowProfileBody.rung_value_eq_log_width` (`:676`, the rung-value readout) and
`RawLowProfileBody.seed_witness_trivial_fails` (`:728`, the threading pole) --
are referred to by name in the docstrings below and have **no** local
counterpart here;
`widthI`, `blockTarget`, `rowDensity`, `xTdepth`, `hRawSchedule`, `xN`,
`cBlock`, `dTwoBlock`, `rawLowGates` from `DenseStageFourOpening`; `mSeed`,
`pSeed`, `wSeed`, `alphaSeed`, `hSeed`, `HardSeedRung` from
`StageOneInterlace`; `pSeedTwo`, `hSeedTwo`, `xSeed` from `StageTwoRelaxed`;
`IsRobust`, `Dfamily`, `bracketGE`, `subgame`, `interlaceFun`, `LambdaGE`,
`D` and `NPCC.hard_seed` itself from the vendored layer.

## Repair note (round `r1`) -- roster and count

This module carries **55** declarations, every one of them registered in
`tools/AxiomAudit.lean`.  Three declarations of the first drafting round were
deleted rather than repaired, and **no replacement was authored**:

* `rungLanding_gives_subsets` -- vacuous.  Both of its hypotheses were dead: the
  conclusion `∃ R' ⊆ RC.1, ∃ C' ⊆ RC.2, R' ⊆ RC.1 ∧ C' ⊆ RC.2` is discharged by
  the empty-Finset witness with no hypotheses at all, so it tested nothing about
  `RungLanding`.  The genuine shape content of the landing binder is carried by
  `rungLanding_of_dominating_member` (`§T5`), which is *not* vacuous.
* `rungValue_eq_log_width` -- an alpha-identical restatement of the banked
  `RawLowProfileBody.rung_value_eq_log_width` (`:676`).  Fixed-interface
  discipline: banked results are consumed by pin, never restated.
* `rungLanding_trivial_restriction_fails` -- a character-identical restatement
  of the banked `RawLowProfileBody.seed_witness_trivial_fails` (`:728`).  That
  banked declaration remains **the** citable threading pole, and the docstrings
  of `RungLanding`, `rungLanding_of_dominating_member` and `rungValue_pos` cite
  it directly.

Nothing else changed: the facade section, the `D:461--528` contract
transcription, the least-witness `m_HS` / `t_HS`, the rung identifications, the
landing binder, the conditional `hseed` discharge and the two consistency probes
stand exactly as first certified.  The `Aux N` labels of `§T5` are the original
ones and are deliberately **not** renumbered, so the surviving statements remain
byte-identical to the round they were certified in; the gaps at `Aux 13` and
`Aux 14` are the two deletions above.

## Mechanical-rule notes (frozen `sections/02-mechanical-contract.tex`)

* **M1/M4.**  The three new non-propositional definitions `hardSeedCopies`,
  `hardSeedRowDensity`, `hardSeedColumnDensity` are pure arithmetic in their
  numeric arguments: no matrix, no protocol, no promise certificate, no
  complexity or robustness conclusion.  `mHS` and `tHS` are naturals defined by
  a least-witness clause and carry no conclusion.  `HSThreshold` and
  `RungLanding` are *statements*, written as `def : Prop` only so that one
  binder can be named once and reused; both are hypotheses at every use site.
* **M2.**  No conclusion is smuggled into constructor data: there is no new
  structure in this module at all, and the two propositional definitions are
  never fields of anything.
* **M3.**  No bundle field restates a derived telescope; the rung side
  conditions of `rungCall_side_conditions` are *derived* from `mHS + 2 <= w_S`
  and `w_S <= b_T`, not assumed one by one.
* **M10 (weakening only).**  Where the frozen text writes a real power the Lean
  uses `Real.rpow`, and where it writes a natural power the Lean uses `Monoid.npow`,
  exactly as the vendored declaration does; the ceiling floors of `bracketGE`
  are inherited unchanged.

## Axiom surface

Imports `EthInapproximability.ParameterizedNP.RawLowProfileBody` and, through
it, `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported anywhere in
this chain, so the cited AGHP balanced-family axiom is not in the closure of any
declaration here.  `NPCC.hard_seed` lives in `NPCC.Engine`, which is reachable
through `NPCC.Transfer` inside `LegacyNPCC.Core`; Appendix D lines 30--35 record
its audited surface as `propext`, `Classical.choice`, `Quot.sound`.  No new
`axiom` is introduced and no opaque certificate carries a conclusion.
-/

namespace EthInapproximability.ParameterizedNP.HardSeedFacade

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.RawLowProfileBody

universe u

/-! # FACADE SECTION

The Appendix-D contract `D:461--528`, transcribed and consumed by pin. -/

/-! ## §F1  The three displayed arguments of `eq:contract-hard-seed` -/

/-- The copy count `(2^{j-1}+2) 2^{m-j}` -- the **first** argument of
`D_f(p,x,z)` in `eq:contract-hard-seed` (`D:482`).

`M1`/`M4`: pure arithmetic in two naturals.  The natural subtraction `m - j` is
the frozen one; `D:493--494` records why it is harmless
(`hardSeed_natSub_legal` below). -/
def hardSeedCopies (j m : ℕ) : ℕ := (2 ^ (j - 1) + 2) * 2 ^ (m - j)

/-- The retained **row** density `2^m 2^{-b}` -- the **second** argument of
`D_f(p,x,z)` in `eq:contract-hard-seed` (`D:483`), explicitly named as the row
density by `D:488--489`. -/
noncomputable def hardSeedRowDensity (m : ℕ) (b : ℝ) : ℝ :=
  (2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b)

/-- The retained **column** density `2^{-2^{(49/100) sqrt m}}` -- the **third**
argument of `D_f(p,x,z)` in `eq:contract-hard-seed` (`D:484`), explicitly named
as the column density by `D:489--490`.  Both outer powers are real exponents,
so both are `Real.rpow`. -/
noncomputable def hardSeedColumnDensity (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ))))

/-! ## §F2  The checked inherited declaration, consumed by pin -/

/-- **Checked inherited declaration: general hard seed**
(`sections/D-inherited-contracts.tex`, paragraph at line 461; quantifier order
`eq:contract-hard-seed-quantifiers` at line 470, hypothesis battery at lines
474--477, conclusion `eq:contract-hard-seed` at line 486).

Route-named facade for `NPCC.hard_seed`
(`vendor/npc-cc/NPCC/Engine.lean:1724`).  The vendored declaration is
*consumed*: the body is exactly the inherited term, so the axiom surface is
unchanged and nothing here is re-proved or re-axiomatized.

The quantifier order is the frozen one and is **not** rearranged: `j` and
`delta` first, then the *existential* threshold `m_0` with `j <= m_0`, then
`m >= m_0`, and only then -- "followed uniformly", `D:472--473` -- all finite
types `X, Y`, all games `f`, and all reals `b`.  Hoisting the type quantifiers
outside `m_0` would be a strictly weaker statement; hoisting `delta` inside
`m_0` is the rendering the vendored docstring records as *unprovable*. -/
theorem hardSeed (j : ℕ) (hj : 2 ≤ j) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∃ m₀ : ℕ, j ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ (X Y : Type u) [Fintype X] [Fintype Y]
        (f : X → Y → Bool) (b : ℝ),
        IsRobust f δ b → 1 ≤ b → 3 ≤ D f → (m : ℝ) ≤ b →
        D f + m ≤ Dfamily (interlaceFun f (hardSeedCopies j m))
          (bracketGE X Y (hardSeedCopies j m) (hardSeedRowDensity m b)
            (hardSeedColumnDensity m)) :=
  NPCC.hard_seed.{u} j hj δ hδ0 hδ

/-- **`D:493--494`, the natural subtraction is the honest one.**  "The natural
subtraction `m - j` is harmless because `eq:contract-hard-seed-quantifiers`
gives `m >= m_0 >= j`."  Derived, never assumed. -/
theorem hardSeed_natSub_legal {j m₀ m : ℕ} (hjm₀ : j ≤ m₀) (hm : m₀ ≤ m) :
    j ≤ m ∧ (m - j) + j = m :=
  ⟨le_trans hjm₀ hm, Nat.sub_add_cancel (le_trans hjm₀ hm)⟩

/-! ## §F3  The active-call pin `j = 5`, `delta = 1/10` (`D:495`) -/

/-- The contract index `j` fixed by **every active call** (`D:495`).  This is
the *contract* `j`, not a rung index; see `contract_j_ne_rung_index`. -/
def contractJ : ℕ := 5

/-- The contract robustness margin `delta` fixed by every active call
(`D:495`). -/
noncomputable def contractDelta : ℝ := 1 / 10

@[simp] theorem contractJ_eq : contractJ = 5 := rfl

@[simp] theorem contractDelta_eq : contractDelta = 1 / 10 := rfl

/-- `contractJ` is legal for `hardSeed`: `2 <= 5`. -/
theorem two_le_contractJ : 2 ≤ contractJ := by norm_num [contractJ]

/-- `contractDelta` is legal for `hardSeed`: `0 < 1/10 < 1/2`. -/
theorem contractDelta_mem : 0 < contractDelta ∧ contractDelta < 1 / 2 := by
  constructor <;> norm_num [contractDelta]

/-! ## §F4  The tail predicate `HSThreshold` and the least witness `m_HS`

`D:495--515`.  "Let `HSThreshold(r)` denote the full tail predicate: `5 <= r`,
and for every `m >= r`, every finite `X, Y`, every Boolean game `f`, and every
real `b`, the hypotheses `Robust(f, 1/10, b)`, `1 <= b`, `3 <= D(f)`,
`(m : R) <= b` imply `eq:contract-hard-seed` with `(j, delta) = (5, 1/10)`."

Transcribed literally, at the universe `u` of the finite carriers; the frozen
"every finite `X, Y`" is the universally quantified type pair inside the
predicate, so the predicate -- and hence the constant it defines -- is
universe polymorphic exactly as the inherited declaration is. -/
def HSThreshold (r : ℕ) : Prop :=
  5 ≤ r ∧
    ∀ m : ℕ, r ≤ m →
      ∀ (X Y : Type u) [Fintype X] [Fintype Y]
        (f : X → Y → Bool) (b : ℝ),
        IsRobust f (1 / 10 : ℝ) b → 1 ≤ b → 3 ≤ D f → (m : ℝ) ≤ b →
        D f + m ≤ Dfamily (interlaceFun f (hardSeedCopies 5 m))
          (bracketGE X Y (hardSeedCopies 5 m) (hardSeedRowDensity m b)
            (hardSeedColumnDensity m))

/-- **`D:504--505`, existence.**  "Equation `eq:contract-hard-seed-quantifiers`
proves that this predicate holds for at least one natural number."  Proved --
not assumed -- by instantiating `hardSeed` at the pinned `j = 5`,
`delta = 1/10`, whose threshold `m_0` satisfies `5 <= m_0` by the contract's own
`j <= m_0` clause. -/
theorem hsThreshold_exists : ∃ r : ℕ, HSThreshold.{u} r := by
  obtain ⟨m₀, hjm₀, hcond⟩ :=
    hardSeed.{u} 5 (by norm_num) (1 / 10 : ℝ) (by norm_num) (by norm_num)
  exact ⟨m₀, hjm₀, hcond⟩

/-- **`eq:contract-hard-seed-threshold-names` (`D:508--510`), the exponent
threshold.**  `m_HS = min{r : HSThreshold(r)}`.

`D:516--517`: "No numerical value is required.  The least-witness definition
pins one global constant before any game, depth, source instance, or promise
branch is chosen."  Accordingly **no numeral for `mHS` appears anywhere in this
module**, and every consumer takes `mHS <= m` as a hypothesis. -/
noncomputable def mHS : ℕ := sInf {r : ℕ | HSThreshold.{u} r}

/-- **`eq:contract-hard-seed-threshold-names` (`D:511`), the corresponding
width.**  `t_HS = 2^{m_HS}`.  `D:514--515`: "`m_HS` is the exponent threshold
and `t_HS` is its corresponding width; they are not interchangeable"
(`mHS_lt_tHS`). -/
noncomputable def tHS : ℕ := 2 ^ mHS.{u}

/-- The least witness really is a witness. -/
theorem mHS_spec : HSThreshold.{u} (mHS.{u}) :=
  Nat.sInf_mem (hsThreshold_exists.{u})

/-- The least witness really is least. -/
theorem mHS_least {r : ℕ} (h : HSThreshold.{u} r) : mHS.{u} ≤ r :=
  Nat.sInf_le h

/-- The first conjunct of the tail predicate, at the canonical constant
(`D:496`). -/
theorem five_le_mHS : 5 ≤ mHS.{u} := (mHS_spec.{u}).1

@[simp] theorem tHS_eq_two_pow : tHS.{u} = 2 ^ mHS.{u} := rfl

/-- **`D:514--515`: the exponent and the width are not interchangeable.**
`m_HS < t_HS` strictly, at every value the least-witness definition can take. -/
theorem mHS_lt_tHS : mHS.{u} < tHS.{u} := by
  rw [tHS_eq_two_pow]
  exact Nat.lt_two_pow_self

/-- **Reader `02-preliminaries.tex:326--328`.**  "Fix a power of two
`t_HS >= 16` from which the resulting fixed-surplus corollary is valid."  The
canonical width clears the reader's floor, because `5 <= m_HS`. -/
theorem sixteen_le_tHS : 16 ≤ tHS.{u} := by
  rw [tHS_eq_two_pow]
  calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ mHS.{u} := Nat.pow_le_pow_right (by norm_num) (by
        have := five_le_mHS.{u}; omega)

/-- **The active call (`D:495`), as a directly usable endpoint.**

Reader counterpart: `eq:paper-hard-seed-corollary`
(`reader-facing/sections/02-preliminaries.tex`, label line 341).

At the pinned `(j, delta) = (5, 1/10)` and any exponent `m` above the canonical
threshold `m_HS`, the four hypotheses of `D:474--477` give the conclusion
`eq:contract-hard-seed` in the exact `D_f(p,x,z)` orientation. -/
theorem hardSeedAtPin {X Y : Type u} [Fintype X] [Fintype Y]
    (m : ℕ) (hm : mHS.{u} ≤ m) (f : X → Y → Bool) (b : ℝ)
    (hrob : IsRobust f (1 / 10 : ℝ) b) (hb : 1 ≤ b) (hD : 3 ≤ D f)
    (hmb : (m : ℝ) ≤ b) :
    D f + m ≤ Dfamily (interlaceFun f (hardSeedCopies 5 m))
      (bracketGE X Y (hardSeedCopies 5 m) (hardSeedRowDensity m b)
        (hardSeedColumnDensity m)) :=
  (mHS_spec.{u}).2 m hm X Y f b hrob hb hD hmb

/-! ## §F5  Aux-lemma battery for the facade

General properties of the three displayed arguments and of the tail predicate.
Each is a statement about arbitrary parameters, not about a pinned instance. -/

/-- **Aux 1 (general, the copy count is positive).**  Every hard-seed call has
at least one copy, so the bracket it names is not the empty interlace. -/
theorem hardSeedCopies_pos (j m : ℕ) : 0 < hardSeedCopies j m :=
  Nat.mul_pos (by positivity) Nat.one_le_two_pow

/-- **Aux 2 (`D:518--519`, the copy-count identity).**  "At width `2^m`, the
copy count in `eq:contract-hard-seed` is exactly `9 * 2^m / 16`."  Stated
without division, so that it is an identity of naturals rather than a rounding
claim.  General in `m` above the pinned `j = 5`. -/
theorem hardSeedCopies_five_identity {m : ℕ} (hm : 5 ≤ m) :
    16 * hardSeedCopies 5 m = 9 * 2 ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
  simp only [hardSeedCopies, Nat.add_sub_cancel, pow_add]
  norm_num
  ring

/-- **Aux 3 (`D:518--519` in `ℝ`).**  The same identity in the form the
Stage-4 rung schedule uses, `p = 9 * 2^m / 16`. -/
theorem hardSeedCopies_five_cast {m : ℕ} (hm : 5 ≤ m) :
    ((hardSeedCopies 5 m : ℕ) : ℝ) = 9 * 2 ^ m / 16 := by
  have h : ((16 * hardSeedCopies 5 m : ℕ) : ℝ) = ((9 * 2 ^ m : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (hardSeedCopies_five_identity hm)
  push_cast at h
  linarith

/-- **Aux 4 (general, the row density is positive).**  At every exponent and
every depth: the second argument of `D_f` is a legal (strictly positive)
density. -/
theorem hardSeedRowDensity_pos (m : ℕ) (b : ℝ) : 0 < hardSeedRowDensity m b := by
  unfold hardSeedRowDensity
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (m : ℕ) := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

/-- **Aux 5 (general, the column density is a legal density).**  `0 < h <= 1`
at every exponent -- the guard shape `bracketGE` needs, and the reason the
column floor `ceil(|Y|^p h)` is meaningful. -/
theorem hardSeedColumnDensity_mem (m : ℕ) :
    0 < hardSeedColumnDensity m ∧ hardSeedColumnDensity m ≤ 1 := by
  constructor
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : (0 : ℝ) < (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith

/-- **Aux 6 (`D:488--492`, the orientation is load-bearing).**

"The second argument ... is the retained *row* density.  The third argument ...
is the retained *column* density.  This orientation is part of the typed
`D_f(p,x,z)` interface and must not be reversed in a compiler gate or call
record."

The two arguments are **not** interchangeable: at the legal parameters
`m = 5`, `b = 5` the row density is exactly `1` while the column density is
strictly below `1`, so swapping the second and third slots produces a different
bracket family.  A facade that transposed them would typecheck perfectly and be
wrong; this lemma is the check that it did not. -/
theorem hardSeedDensities_not_interchangeable :
    hardSeedRowDensity 5 (5 : ℝ) = 1 ∧
      hardSeedColumnDensity 5 < 1 ∧
      hardSeedColumnDensity 5 ≠ hardSeedRowDensity 5 (5 : ℝ) := by
  have hrow : hardSeedRowDensity 5 (5 : ℝ) = 1 := by
    unfold hardSeedRowDensity
    rw [Real.rpow_neg (by norm_num), show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  have hcol : hardSeedColumnDensity 5 < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have : (0 : ℝ) < (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((5 : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith
  exact ⟨hrow, hcol, by rw [hrow]; exact ne_of_lt hcol⟩

/-- **Aux 7 (general, the tail predicate is upward closed).**  If `HSThreshold`
holds at `r` it holds at every `r' >= r`.  This is the unit test that makes
"the least witness" the same thing as "the smallest legal threshold": an
encoding whose quantifier `∀ m >= r` pointed the other way would be *downward*
closed and this would fail. -/
theorem HSThreshold.mono {r r' : ℕ} (h : HSThreshold.{u} r) (hr : r ≤ r') :
    HSThreshold.{u} r' :=
  ⟨le_trans h.1 hr, fun m hm => h.2 m (le_trans hr hm)⟩

/-- **Aux 8 (general, the canonical constant dominates every legal record
field).**  The Stage-1 and Stage-2 records of the banked modules carry `m_HS`
as an *abstract* field; as soon as that field genuinely satisfies the tail
predicate, the canonical least witness sits below it, so a threshold clause
stated against the record's field implies the one stated against `mHS`. -/
theorem mHS_le_of_threshold_field {r m : ℕ} (h : HSThreshold.{u} r) (hm : r ≤ m) :
    mHS.{u} ≤ m :=
  le_trans (mHS_least.{u} h) hm

/-- **Aux 9 (`D:495`, the two `j`s are distinct).**

The contract binder `j = 5` of `eq:contract-hard-seed` and the Stage-4 rung
index `j ∈ {0,1,2}` of `08:168` are different symbols with different roles, and
the frozen text uses the same letter for both.  At no legal rung index do they
coincide, so a facade that conflated them would be calling the contract at an
illegal `j` (indeed at `j < 2`, outside `eq:contract-hard-seed-quantifiers`). -/
theorem contract_j_ne_rung_index {jr : ℕ} (hjr : jr ≤ 2) :
    jr ≠ contractJ ∧ 2 ≤ contractJ ∧ ¬ (contractJ ≤ 2) := by
  simp only [contractJ]
  omega

/-! ## §F6  The facade fires at the two banked open `hardSeed` binders

`StageOneInterlace.hardSeedRung_conclusion` and
`StageTwoRelaxed.stageTwoSeedCall_conclusion` each take the inherited hard-seed
conclusion as an explicit named binder, because no vendored declaration was
available at their shape.  The facade *is* that declaration, and the three
displayed arguments of the two call records are literally
`hardSeedCopies 5 m`, `hardSeedRowDensity m b`, `hardSeedColumnDensity m`.  The
identifications below are proved, and the two discharges follow.

These are consumers and non-vacuity witnesses of the facade; they claim no
reader item of their own. -/

/-- The Stage-1 copy count is the contract copy count at `j = 5`. -/
theorem pSeed_eq_hardSeedCopies (a j : ℕ) :
    pSeed a j = hardSeedCopies 5 (mSeed a j) := by
  norm_num [pSeed, hardSeedCopies]

/-- The Stage-1 retained row density is the contract row density. -/
theorem alphaSeed_eq_hardSeedRowDensity (a b₀ j : ℕ) :
    alphaSeed a b₀ j = hardSeedRowDensity (mSeed a j) ((b₀ : ℕ) : ℝ) := by
  unfold alphaSeed hardSeedRowDensity wSeed
  norm_num

/-- The Stage-1 retained column density is the contract column density. -/
theorem hSeed_eq_hardSeedColumnDensity (a j : ℕ) :
    hSeed a j = hardSeedColumnDensity (mSeed a j) := rfl

/-- **Aux 10 (non-vacuity: the facade discharges the Stage-1 binder).**

`StageOneInterlace.hardSeedRung_conclusion` binds
`hardSeed : Dsrc + S.m <= Dfamily (interlaceFun R S.p) (bracketGE X Y S.p S.α S.h)`.
This theorem *produces* that binder at `Dsrc = D R`, from the facade alone, for
every legal `HardSeedRung` whose exponent clears the canonical threshold. -/
theorem stageOne_hardSeed_discharge {X Y : Type u} [Fintype X] [Fintype Y]
    (S : HardSeedRung) (R : X → Y → Bool)
    (hm : mHS.{u} ≤ S.m) (hrob : IsRobust R (1 / 10 : ℝ) ((S.b₀ : ℕ) : ℝ))
    (hb : 1 ≤ ((S.b₀ : ℕ) : ℝ)) (hD : 3 ≤ D R)
    (hmb : ((S.m : ℕ) : ℝ) ≤ ((S.b₀ : ℕ) : ℝ)) :
    D R + S.m ≤
      Dfamily (interlaceFun R S.p) (bracketGE X Y S.p S.α S.h) := by
  have h := hardSeedAtPin (X := X) (Y := Y) S.m hm R ((S.b₀ : ℕ) : ℝ) hrob hb hD hmb
  have hp : S.p = hardSeedCopies 5 S.m := pSeed_eq_hardSeedCopies S.a S.j
  have hα : S.α = hardSeedRowDensity S.m ((S.b₀ : ℕ) : ℝ) :=
    alphaSeed_eq_hardSeedRowDensity S.a S.b₀ S.j
  have hh : S.h = hardSeedColumnDensity S.m := hSeed_eq_hardSeedColumnDensity S.a S.j
  rw [hp, hα, hh]
  exact h

/-- The Stage-2 copy count is the contract copy count at `j = 5`. -/
theorem pSeedTwo_eq_hardSeedCopies (k₂ : ℕ) :
    pSeedTwo k₂ = hardSeedCopies 5 k₂ := by
  norm_num [pSeedTwo, hardSeedCopies]

/-- The Stage-2 retained column density is the contract column density. -/
theorem hSeedTwo_eq_hardSeedColumnDensity (k₂ : ℕ) :
    hSeedTwo k₂ = hardSeedColumnDensity k₂ := rfl

/-- The Stage-2 retained row density `t_2 x_1` is the contract row density at
exponent `log_2 t_2 = k_2`. -/
theorem stageTwoRowDensity_eq {t₂ k₂ b₁ : ℕ} (ht₂ : t₂ = 2 ^ k₂) :
    ((t₂ : ℕ) : ℝ) * xSeed b₁ = hardSeedRowDensity k₂ ((b₁ : ℕ) : ℝ) := by
  subst ht₂
  unfold xSeed hardSeedRowDensity
  norm_num

/-- **Aux 11 (non-vacuity: the facade discharges the Stage-2 binder).**

`StageTwoRelaxed.stageTwoSeedCall_conclusion` binds
`hardSeed : bCapVal + k_2 <= Dfamily (interlaceFun M (pSeedTwo k_2))
(bracketGE X' Y' (pSeedTwo k_2) (t_2 x_1) (hSeedTwo k_2))`.
This theorem *produces* that binder at `bCapVal = D M`, from the facade
alone. -/
theorem stageTwo_hardSeed_discharge {X Y : Type u} [Fintype X] [Fintype Y]
    (M : X → Y → Bool) (t₂ k₂ b₁ : ℕ) (ht₂ : t₂ = 2 ^ k₂)
    (hm : mHS.{u} ≤ k₂) (hrob : IsRobust M (1 / 10 : ℝ) ((b₁ : ℕ) : ℝ))
    (hb : 1 ≤ ((b₁ : ℕ) : ℝ)) (hD : 3 ≤ D M)
    (hmb : ((k₂ : ℕ) : ℝ) ≤ ((b₁ : ℕ) : ℝ)) :
    D M + k₂ ≤
      Dfamily (interlaceFun M (pSeedTwo k₂))
        (bracketGE X Y (pSeedTwo k₂) (((t₂ : ℕ) : ℝ) * xSeed b₁) (hSeedTwo k₂)) := by
  have h := hardSeedAtPin (X := X) (Y := Y) k₂ hm M ((b₁ : ℕ) : ℝ) hrob hb hD hmb
  rwa [← pSeedTwo_eq_hardSeedCopies k₂, ← stageTwoRowDensity_eq ht₂,
    ← hSeedTwo_eq_hardSeedColumnDensity k₂] at h

/-! # THREADING SECTION

`08:241--251` at the Stage-4 rung: the inherited call at width `I_j`, the
identification of its three displayed arguments with the rung scalars
`(p_j, x_j, h_j^raw)`, and the supply of the banked `RungSeedWitness` binder.

**The two `j`s.**  Throughout this section `jr ∈ {0,1,2}` is the *rung* index
of `08:168`, and the *contract* index is the pinned `5` of `D:495`
(`contract_j_ne_rung_index`).  The contract exponent `m` instantiates as
`m = w_S - jr`, so the contract width `2^m` is the rung width
`I_jr = s/2^{jr} = 2^{w_S - jr}` at the frozen power-of-two scale `s = 2^{w_S}`
(`widthI_eq_two_pow`, consumed by pin). -/

/-! ## §T1  The rung identification: `(p_j, x_j, h_j^raw)` is the contract call -/

/-- **`08:170--171` and `D:518--519` agree.**  The contract copy count at
exponent `m = w_S - jr` is exactly the rung block target
`p_jr = 9 I_jr / 16`.

This is the identity that makes "instantiated at width `I_j`" literal: the
number of copies the inherited lemma produces is the number of Stage-3 blocks
the projection step retains, with nothing to spare and nothing to trim. -/
theorem rungCopies_eq_blockTarget {wS jr : ℕ} (hjw : jr ≤ wS)
    (hm : 5 ≤ wS - jr) :
    ((hardSeedCopies 5 (wS - jr) : ℕ) : ℝ) = blockTarget (2 ^ wS) jr := by
  rw [blockTarget, widthI_eq_two_pow wS jr hjw, hardSeedCopies_five_cast hm]

/-- **`08:172` is the contract row density.**  `x_jr = I_jr x_T = 2^{w_S-jr} 2^{-b_T}`
is the second argument of `eq:contract-hard-seed` at `m = w_S - jr`, `b = b_T`.

The orientation of `D:488--492` is preserved: this is the *row* slot on both
sides. -/
theorem rungRowDensity_eq {wS jr bT : ℕ} (hjw : jr ≤ wS) :
    hardSeedRowDensity (wS - jr) ((bT : ℕ) : ℝ) = rowDensity (2 ^ wS) jr bT := by
  unfold hardSeedRowDensity rowDensity xTdepth
  rw [widthI_eq_two_pow wS jr hjw, Real.rpow_neg (by norm_num),
    show ((bT : ℕ) : ℝ) = ((bT : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  ring

/-- **`08:173--174` is the contract column density.**
`h_jr^raw = 2^{-2^{0.49 sqrt(log_2 I_jr)}}` is the third argument of
`eq:contract-hard-seed` at `m = w_S - jr`, because `log_2 I_jr = w_S - jr`.

The orientation of `D:488--492` is preserved: this is the *column* slot on both
sides. -/
theorem rungColumnDensity_eq {wS jr : ℕ} (hjw : jr ≤ wS) :
    hardSeedColumnDensity (wS - jr) = hRawSchedule (widthI (2 ^ wS) jr) := by
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hself : Real.logb 2 2 = 1 := by rw [Real.logb, div_self hl2]
  have hlog : Real.logb 2 ((2 : ℝ) ^ (wS - jr)) = ((wS - jr : ℕ) : ℝ) := by
    rw [Real.logb_pow, hself, mul_one]
  rw [hRawSchedule, widthI_eq_two_pow wS jr hjw, hlog, hardSeedColumnDensity]

/-- **The inherited call at width `I_jr` (`08:242--250`), PROVED from the
facade and the Stage-2 robustness certificate.**

"The inherited General Hard Seed Lemma, instantiated at width `I_j`, therefore
leaves a member of `<M_2^T, p_j, x_j, h_j^raw>` of complexity at least
`D_2 + log_2 I_j`."

The three displayed arguments are the rung scalars on the nose
(`rungCopies_eq_blockTarget`, `rungRowDensity_eq`, `rungColumnDensity_eq`), and
`D_2 = comp(M_2^T)` is the exact-complexity half of
`eq:stage2-two-depth-certificate`, so the value is `D_2 + (w_S - jr)
= D_2 + log_2 I_jr`.

The robustness hypothesis is the **open** `(1/10, b_T)`-certificate of
`eq:stage2-two-depth-certificate` (ledger `STAGE2-MODULE-001`, tranche
`cc-t2e`), carried here as the named binder `hrob`. -/
theorem rungSeedFamilyBound {Rw₂ Cl₂ : Type u} [Fintype Rw₂] [Fintype Cl₂]
    (M2T : Rw₂ → Cl₂ → Bool) (wS jr bT : ℕ)
    (hjw : jr ≤ wS) (hm : mHS.{u} ≤ wS - jr)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hb : 1 ≤ ((bT : ℕ) : ℝ)) (hD : 3 ≤ D M2T)
    (hmb : ((wS - jr : ℕ) : ℝ) ≤ ((bT : ℕ) : ℝ)) :
    D M2T + (wS - jr) ≤
      Dfamily (interlaceFun M2T (hardSeedCopies 5 (wS - jr)))
        (bracketGE Rw₂ Cl₂ (hardSeedCopies 5 (wS - jr))
          (rowDensity (2 ^ wS) jr bT) (hRawSchedule (widthI (2 ^ wS) jr))) := by
  have h := hardSeedAtPin (X := Rw₂) (Y := Cl₂) (wS - jr) hm M2T ((bT : ℕ) : ℝ)
    hrob hb hD hmb
  rwa [rungRowDensity_eq hjw, rungColumnDensity_eq hjw] at h

/-! ## §T2  From `§1`--`§3` densities to bracket floors

The banked `§1`--`§3` of `RawLowProfileBody` deliver *normalized densities*:
`rawLow_column_transport` gives a surviving column density at least
`h_jr^raw`, `rawLow_block_count_of_block_densities` gives a count of blocks
retaining an `x_jr` fraction of their rows, and `regular_density_transfer`
gives that the projection does not decrease a normalized density.  `bracketGE`
membership, by contrast, is stated with the two *ceiling floors*
`ceil(|X| x)` and `ceil(|Y|^p z)`.  The two general bridges below are what
converts one into the other; they are the reason the `§1`--`§3` densities are
the right currency for the landing binder. -/

/-- **The column bridge, general.**  A normalized column density at least `z`
meets the bracket column floor `ceil(|Y|^p z)`.  General in the carrier, in the
column set, in `p` and in `z`. -/
theorem col_floor_of_density {Y : Type*} [Fintype Y] {p : ℕ} {z : ℝ}
    {C : Finset (Fin p → Y)}
    (h : ((Fintype.card Y : ℝ) ^ p) * z ≤ (C.card : ℝ)) :
    ⌈((Fintype.card Y : ℝ) ^ p) * z⌉₊ ≤ C.card :=
  Nat.ceil_le.mpr h

/-- **The row bridge, general.**  A per-copy row count meeting the real target
`|X| x` meets the bracket row floor `ceil(|X| x)`.  General in the carrier, in
the row set, in `p`, in the copy index and in `x`. -/
theorem row_floor_of_density {X : Type*} [Fintype X] {p : ℕ} {x : ℝ}
    {R : Finset (Fin p × X)}
    (h : ∀ q : Fin p, (Fintype.card X : ℝ) * x ≤
      ((R.filter fun r => r.1 = q).card : ℝ)) :
    IsEquipartitionedGE R (Finset.univ : Finset (Fin p))
      ⌈(Fintype.card X : ℝ) * x⌉₊ :=
  fun q _ => Nat.ceil_le.mpr (h q)

/-- **A member of a family bounds the family infimum from above.**  `Dfamily`
is a `Nat.sInf`, so any member is an upper bound for it; this is the step that
turns the inherited *family* lower bound into a bound on the complexity of the
particular member the landing produces.  General. -/
theorem Dfamily_le_of_mem {A B : Type*} (f : A → B → Bool)
    (Φ : Set (Finset A × Finset B))
    {RC : Finset A × Finset B} (h : RC ∈ Φ) :
    Dfamily f Φ ≤ D (subgame f RC.1 RC.2) :=
  Nat.sInf_le ⟨RC, h, rfl⟩

/-! ## §T3  The landing binder, and the `RungSeedWitness` construction -/

/-- **The geometric output of the discard/projection chain `08:220--242`, as a
named hypothesis.**

"Fix `j in {0,1,2}`, take an arbitrary member of `<N,1,x_N,y/2^j>`, and
transpose it.  First discard all protected selector and diagonal columns of
`A`. ... Next discard the protected nonbase row reservoirs and all raw source
rows. ... Project the retained base columns to any `p_j` such blocks."

`RungLanding` says exactly what that chain *delivers*: for every member `RC` of
the rung family of `N`, a restriction `(R', C')` of `RC` and a member `SC` of
the rung bracket `<M_2^T, p_jr, x_jr, h_jr^raw>` with
`comp(SC) <= comp(R', C')`.

`M1`/`M2`: a *statement* about the pinned pair of matrices, not constructor
data; it is a hypothesis at every use site and is nowhere inhabited in this
module.  It carries no complexity *lower* bound -- the lower bound is the
inherited `rungSeedFamilyBound`, supplied separately -- so no conclusion is
smuggled in.

The trivial witness fails it in the direction that matters: see the banked pole
`RawLowProfileBody.seed_witness_trivial_fails`, consumed by pin. -/
def RungLanding {Rw Cl Rw₂ Cl₂ : Type u} [Fintype Rw] [Fintype Cl]
    [Fintype Rw₂] [Fintype Cl₂]
    (Nmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    (wS jr bT : ℕ) (x y : ℝ) : Prop :=
  ∀ RC ∈ bracketGE Rw Cl 1 x (y / 2 ^ jr),
    ∃ R' ⊆ RC.1, ∃ C' ⊆ RC.2,
      ∃ SC ∈ bracketGE Rw₂ Cl₂ (hardSeedCopies 5 (wS - jr))
          (rowDensity (2 ^ wS) jr bT) (hRawSchedule (widthI (2 ^ wS) jr)),
        D (subgame (interlaceFun M2T (hardSeedCopies 5 (wS - jr))) SC.1 SC.2)
          ≤ D (subgame (interlaceFun Nmat 1) R' C')

/-- **`08:242--251` composed: the landing plus the inherited call give the
banked `RungSeedWitness` binder.**

This is the whole content of the frozen sentence "The inherited General Hard
Seed Lemma, instantiated at width `I_j`, therefore leaves a member of
`<M_2^T, p_j, x_j, h_j^raw>` of complexity at least `D_2 + log_2 I_j`", read as
a statement about the *member of `<N,1,x_N,y/2^j>` we started from*: the
inherited bound is a bound on the family infimum, the produced `SC` is a member
of that family, and the landing compares it with a restriction of `RC`.

General in the two matrices, the rung index, the scale and the densities. -/
theorem rungSeedWitness_of_landing {Rw Cl Rw₂ Cl₂ : Type u}
    [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
    (Nmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {wS jr bT : ℕ} {x y : ℝ}
    (hland : RungLanding Nmat M2T wS jr bT x y)
    (hbound : D M2T + (wS - jr) ≤
      Dfamily (interlaceFun M2T (hardSeedCopies 5 (wS - jr)))
        (bracketGE Rw₂ Cl₂ (hardSeedCopies 5 (wS - jr))
          (rowDensity (2 ^ wS) jr bT) (hRawSchedule (widthI (2 ^ wS) jr)))) :
    RungSeedWitness Nmat (D M2T + (wS - jr)) jr x y := by
  intro RC hRC
  obtain ⟨R', hR', C', hC', SC, hSC, hle⟩ := hland RC hRC
  refine ⟨R', hR', C', hC', ?_⟩
  exact le_trans (le_trans hbound (Dfamily_le_of_mem _ _ hSC)) hle

/-- **`08:242--251` end to end at one rung**, with the two open binders named.

`hrob` is the Stage-2 `(1/10, b_T)`-robustness certificate
(`eq:stage2-two-depth-certificate`, open in Lean); `hland` is the geometric
landing.  Everything else is proved. -/
theorem rungSeedWitness_of_landing_and_certificate {Rw Cl Rw₂ Cl₂ : Type u}
    [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
    (Nmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {wS jr bT : ℕ} {x y : ℝ}
    (hjw : jr ≤ wS) (hm : mHS.{u} ≤ wS - jr)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hb : 1 ≤ ((bT : ℕ) : ℝ)) (hD : 3 ≤ D M2T)
    (hmb : ((wS - jr : ℕ) : ℝ) ≤ ((bT : ℕ) : ℝ))
    (hland : RungLanding Nmat M2T wS jr bT x y) :
    RungSeedWitness Nmat (D M2T + (wS - jr)) jr x y :=
  rungSeedWitness_of_landing Nmat M2T hland
    (rungSeedFamilyBound M2T wS jr bT hjw hm hrob hb hD hmb)

/-! ## §T4  The composed conditional low-row profile

`rawLowProfile_body` (banked) reduces `lem:raw-low-profile` to the three rung
binders `hseed`.  With the threading above, those binders are supplied from the
facade, the landing, and the Stage-2 certificate.  **The result is a
conditional theorem, and is not a proof of `lem:raw-low-profile`**: the two open
binders `hrob` and `hland` appear in its signature. -/

/-- **`lem:raw-low-profile` (`08:193--216`), with the seed binder threaded.**

Every hypothesis of the banked `rawLowProfile_body` other than `hseed` is passed
through unchanged.  `hseed` itself is now *constructed*, from:

* the facade `hardSeedAtPin` at the pinned `(j, delta) = (5, 1/10)` and the
  exponent `m = w_S - jr` (`rungSeedFamilyBound`);
* the rung identifications `rungCopies_eq_blockTarget`, `rungRowDensity_eq`,
  `rungColumnDensity_eq`, which say that the contract's three displayed
  arguments *are* `(p_jr, x_jr, h_jr^raw)`;
* the Stage-2 exact-complexity certificate, as the named identity
  `hD2 : D_2 = comp(M_2^T)` (the first clause of
  `eq:stage2-two-depth-certificate`);
* the Stage-2 `(1/10, b_T)`-robustness certificate `hrob` (**open**);
* the geometric landing `hland` (**open**).

The rung side conditions `jr <= w_S` and `mHS <= w_S - jr` are derived from the
single scale hypothesis `hwS : mHS + 2 <= w_S`, not assumed three times. -/
theorem rawLowProfile_of_landing_and_certificate {Rw Cl Rw₂ Cl₂ : Type u}
    [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
    (Nmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    (Dsrc a r₂ wS s bT T₀ V₀ B₀ : ℕ) (y : ℝ)
    (Admissible NoCert : Prop) (hAdm : Admissible) (hNo : NoCert)
    (hpow : s = 2 ^ wS) (hdiv : 64 ∣ s)
    (hgates : rawLowGates s bT T₀ V₀ B₀ y)
    (hne : ∀ j : ℕ, j ≤ 2 → (bracketGE Rw Cl 1 xN (y / 2 ^ j)).Nonempty)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 → RungLanding Nmat M2T wS jr bT xN y) :
    cBlock Dsrc a r₂ wS - 1 ≤ LambdaGE Nmat 1 xN y := by
  have h5 : 5 ≤ mHS.{u} := five_le_mHS.{u}
  refine rawLowProfile_body Nmat Dsrc a r₂ wS s bT T₀ V₀ B₀ y
    Admissible NoCert hAdm hNo hpow hdiv hgates hne ?_
  intro _ _ jr hjr
  have hjw : jr ≤ wS := by omega
  have hm : mHS.{u} ≤ wS - jr := by omega
  have hbTpos : (1 : ℝ) ≤ ((bT : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ bT := by omega
    exact_mod_cast this
  have hmb : ((wS - jr : ℕ) : ℝ) ≤ ((bT : ℕ) : ℝ) := by
    have : wS - jr ≤ bT := by omega
    exact_mod_cast this
  have hwit := rungSeedWitness_of_landing_and_certificate Nmat M2T
    (wS := wS) (jr := jr) (bT := bT) (x := xN) (y := y)
    hjw hm hrob hbTpos hD3 hmb (hland jr hjr)
  rwa [← hD2] at hwit

/-! ## §T5  Aux-lemma battery for the threading section -/

/-- **Aux 12 (general, the rung side conditions are one hypothesis, not
three).**  From the single scale clause `mHS + 2 <= w_S` and the depth clause
`w_S <= b_T`, every side condition the rung call needs holds at every rung
index -- the copy-count legality `jr <= w_S`, the threshold clause
`mHS <= w_S - jr`, the depth comparison `(w_S - jr : R) <= b_T`, and the
contract guard `1 <= b_T`.  General in `w_S` and `b_T`, and stated over the
whole legal region rather than at one tier. -/
theorem rungCall_side_conditions {wS bT : ℕ} (hwS : mHS.{u} + 2 ≤ wS)
    (hwSbT : wS ≤ bT) {jr : ℕ} (hjr : jr ≤ 2) :
    jr ≤ wS ∧ mHS.{u} ≤ wS - jr ∧
      ((wS - jr : ℕ) : ℝ) ≤ ((bT : ℕ) : ℝ) ∧ (1 : ℝ) ≤ ((bT : ℕ) : ℝ) := by
  have h5 : 5 ≤ mHS.{u} := five_le_mHS.{u}
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have : wS - jr ≤ bT := by omega
    exact_mod_cast this
  · have : (1 : ℕ) ≤ bT := by omega
    exact_mod_cast this

/-- **Aux 16 (general, the landing binder is not over-strong).**

LANE-GATE 3 in the direction that matters for a *hypothesis*: a binder no
instance can satisfy would make every theorem above vacuous.  `RungLanding` is
implied by the single domination clause below, with the improper restriction
`R' = RC.1`, `C' = RC.2`, so it is satisfiable as soon as one legal member of
the rung bracket is dominated by every member of the `N`-side family -- no
appeal to the Stage-4 geometry is needed to see that the binder is inhabitable.

The clause is exactly the content the frozen chain `08:219--242` has to
produce, so this lemma is *not* a cheap inhabitation: it does not weaken the
demand, it isolates it.  In particular the trivial choice `R' = C' = ∅` still
fails the composed statement (the banked pole
`RawLowProfileBody.seed_witness_trivial_fails`, consumed by pin, together with
`rungValue_pos`), because the inherited call forces the rung value to be at
least `8`. -/
theorem rungLanding_of_dominating_member {Rw Cl Rw₂ Cl₂ : Type u}
    [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
    (Nmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {wS jr bT : ℕ} {x y : ℝ}
    {SC : Finset (Fin (hardSeedCopies 5 (wS - jr)) × Rw₂) ×
          Finset (Fin (hardSeedCopies 5 (wS - jr)) → Cl₂)}
    (hSC : SC ∈ bracketGE Rw₂ Cl₂ (hardSeedCopies 5 (wS - jr))
      (rowDensity (2 ^ wS) jr bT) (hRawSchedule (widthI (2 ^ wS) jr)))
    (hdom : ∀ RC ∈ bracketGE Rw Cl 1 x (y / 2 ^ jr),
      D (subgame (interlaceFun M2T (hardSeedCopies 5 (wS - jr))) SC.1 SC.2)
        ≤ D (subgame (interlaceFun Nmat 1) RC.1 RC.2)) :
    RungLanding Nmat M2T wS jr bT x y :=
  fun RC hRC => ⟨RC.1, subset_rfl, RC.2, subset_rfl, SC, hSC, hdom RC hRC⟩

/-- **Aux 15 (general, the rung value is positive at every legal rung).**  The
value fed to `RungSeedWitness` is at least `3 + 5 > 0`, because the contract
demands `3 <= D(M_2^T)` and the threshold gives `5 <= mHS <= w_S - jr`.  This is
what makes the banked pole `RawLowProfileBody.seed_witness_trivial_fails` bite
at every legal instance rather than at a hand-picked one: that pole rules out
the empty restriction whenever the value is positive, and this lemma supplies
the positivity uniformly over the legal region. -/
theorem rungValue_pos {Rw₂ Cl₂ : Type u} [Fintype Rw₂] [Fintype Cl₂]
    {M2T : Rw₂ → Cl₂ → Bool} {wS jr : ℕ}
    (hD : 3 ≤ D M2T) (hm : mHS.{u} ≤ wS - jr) :
    5 ≤ wS - jr ∧ 8 ≤ D M2T + (wS - jr) ∧ 0 < D M2T + (wS - jr) := by
  have h5 := five_le_mHS.{u}
  refine ⟨by omega, by omega, by omega⟩

/-! ## §T6  Non-vacuity and hypothesis consistency

LANE-GATE 3 and the hypothesis-consistency rule.  The facade's own non-vacuity
is `stageOne_hardSeed_discharge` / `stageTwo_hardSeed_discharge`: it fires, at
legal parameters, exactly at the two shapes the banked Stage-1 and Stage-2
modules left as open binders, so it is not a statement that nothing can use.

For the composed `rawLowProfile_of_landing_and_certificate` the question is
whether its hypothesis bundle is *simultaneously* satisfiable.  The banked
`rawLowProfile_body_side_conditions_consistent` already exhibits the schedule
half at one legal tier (`s = 2^340`, `w_S = 340`, `b_T = 512` forced by
`witness_bT_checked`, protected reservoirs nonempty, `y = 3/5`), over carriers
of cardinality `2^340` chosen so that the rung values the seed binder demands
are not cardinality-refuted.  The theorem below adds the two clauses this
tranche introduces -- the scale clause `mHS + 2 <= w_S` and the depth clause
`w_S <= b_T` -- at that same tier, and derives every rung side condition from
them.

The scale clause is stated *conditionally* on `mHS <= 338`, because `mHS` is a
least-witness constant with **no numeral**: the frozen text refuses to fix its
value (`D:516`), so no theorem here may assert a numeric bound on it.  The
conditional form is the honest one, and it is exactly the shape a caller
supplies from the schedule's own hard-seed window gates
(`eq:hard-seed-width-gates`, `06:264--269`: `k_T = log_2(s/4) >= m_HS`).

The remaining binders cannot be refuted by this bundle: `hD2` is an equation
between two naturals that nothing here constrains; `hrob` and `hD3` are
statements about `M_2^T` alone and no clause in the bundle bounds `D(M_2^T)`
from above or mentions its entries; `hland` is an existential-producing
statement about the pair `(N, M_2^T)`, and the bundle contains no upper bound on
any complexity, so no contradiction can be assembled. -/

/-- **Hypothesis-consistency probe for `rawLowProfile_of_landing_and_certificate`.**

At the banked legal tier, and under the abstract scale clause `mHS <= 338`,
every numeric hypothesis of the composed theorem holds *simultaneously*, and the
rung side conditions it derives hold at every rung.  So the theorem is not
green-because-vacuous. -/
theorem rawLowProfile_threading_hypotheses_consistent (hmHS : mHS.{u} ≤ 338) :
    ((2 ^ 340 : ℕ) = 2 ^ (340 : ℕ) ∧ (64 ∣ (2 ^ 340 : ℕ)))
      ∧ rawLowGates (2 ^ 340) 512 (2 ^ 346) (2 ^ 300) (2 ^ 300) (3 / 5)
      ∧ (mHS.{u} + 2 ≤ 340 ∧ (340 : ℕ) ≤ 512)
      ∧ (∀ jr : ℕ, jr ≤ 2 →
          jr ≤ 340 ∧ mHS.{u} ≤ 340 - jr ∧
            ((340 - jr : ℕ) : ℝ) ≤ ((512 : ℕ) : ℝ) ∧
            (1 : ℝ) ≤ ((512 : ℕ) : ℝ))
      ∧ (∀ jr : ℕ, jr ≤ 2 →
          (bracketGE (Fin (2 ^ 340)) (Fin (2 ^ 340)) 1 xN
            ((3 / 5 : ℝ) / 2 ^ jr)).Nonempty) := by
  have hbank := rawLowProfile_body_side_conditions_consistent
  refine ⟨⟨rfl, hbank.1.2.1⟩, rawLowGates_inhabited, ⟨by omega, by norm_num⟩, ?_,
    hbank.2.2.1⟩
  intro jr hjr
  exact rungCall_side_conditions (wS := 340) (bT := 512) (by omega) (by norm_num) hjr

/-- **The composed theorem actually fires at the banked legal tier.**

The strongest form of the consistency check: every hypothesis of
`rawLowProfile_of_landing_and_certificate` *except* the three that are open by
design (`hD2`, `hrob`/`hD3`, `hland`) is discharged here at the banked tier
(`s = 2^340`, `w_S = 340`, `b_T = 512`, `|T| = 2^346`,
`|W_V| = |W_B| = 2^300`, `y = 3/5`, carriers of cardinality `2^340`), and the
conclusion is produced.  So the hypothesis bundle is not merely
"unrefuted": it is jointly satisfiable, and the theorem is not
green-because-vacuous.

The single abstract clause `mHS <= 338` is the scale hypothesis the schedule's
own hard-seed window gate supplies (`eq:hard-seed-width-gates`, `06:264--269`:
`k_T = log_2(s/4) >= m_HS`, and `log_2(2^340/4) = 338`); it is *not* a numeric
claim about `m_HS`, which `D:516` forbids. -/
theorem rawLowProfile_threading_fires_at_banked_tier
    (Nmat : Fin (2 ^ 340) → Fin (2 ^ 340) → Bool)
    {Rw₂ Cl₂ : Type} [Fintype Rw₂] [Fintype Cl₂] (M2T : Rw₂ → Cl₂ → Bool)
    (Dsrc a r₂ : ℕ)
    (hmHS : mHS.{0} ≤ 338)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((512 : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding Nmat M2T 340 jr 512 xN (3 / 5 : ℝ)) :
    cBlock Dsrc a r₂ 340 - 1 ≤ LambdaGE Nmat 1 xN (3 / 5 : ℝ) :=
  rawLowProfile_of_landing_and_certificate Nmat M2T Dsrc a r₂ 340 (2 ^ 340) 512
    (2 ^ 346) (2 ^ 300) (2 ^ 300) (3 / 5 : ℝ) True True trivial trivial rfl
    rawLowGates_inhabited_nondegenerate.2.1 rawLowGates_inhabited
    rawLowProfile_body_side_conditions_consistent.2.2.1 (by omega) (by norm_num)
    hD2 hrob hD3 hland

end EthInapproximability.ParameterizedNP.HardSeedFacade
