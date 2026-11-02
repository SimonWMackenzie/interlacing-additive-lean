import EthInapproximability.ParameterizedNP.IteratedCanonicalChaining

/-!
# Parameterized NP route: the canonical bracket invariance and the certificate transport

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`CANONICAL-BRACKET-INVARIANCE-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened in the
same change as this module as the **external consumer module** that discharges
**GAP-EXPOSED 1 of `ITERATED-CANONICAL-CHAINING-001`**: the bracket half of
`lem:canonical-reindexing-invariance`, frozen `12:146--165`, together with the
depth-`b_{i+1}` certificate transport that half licenses at frozen `12:295`.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchors (proof source).**
  `sections/12-iteration-specification.tex`:
  * `lem:canonical-reindexing-invariance` (label line 140), **bracket half,
    lines 146--165**.  Lines 146--153: "For every integer `p >= 1` and every
    `x,z in (0,1]`, the increasing equivalences induce a cardinality-preserving
    bijection between the extraction data in `bracket(Can(M),p,x,z)` and
    `bracket(M,p,x,z)`."  Lines 154--156: "Corresponding extracted matrices are
    related by row and column equivalences and therefore have equal
    deterministic communication complexity."  `eq:canonical-bracket-invariance`
    (label line 163, display lines 157--164):
    `comp(bracket(Can(M),p,x,z)) = comp(bracket(M,p,x,z))` and
    `Lambda_3(Can(M),p,x,z) = Lambda_3(M,p,x,z)`.  Line 165: "The same
    conclusions hold for `Can_{m,n}(M)`."
  * The frozen **proof**, lines 168--180: "For the `p`-fold interlace, the row
    equivalence is the product of the identity on `[p]` with `e_X`, and the
    column equivalence applies `e_Y` in every one of the `p` coordinates.  These
    maps preserve entries, fibre cardinalities, and total column cardinalities.
    They therefore carry every legal bracket extraction to a unique legal
    extraction with the same retained cardinalities, and conversely.
    Transporting protocols on each extracted matrix proves the first equality in
    `eq:canonical-bracket-invariance`; applying it at column densities
    `z, z/2, z/4` proves the displayed three-rung equality."  Every declaration
    of Parts 1--4 below is one clause of that sentence.
  * The **consumption site**, frozen lines 341--350 inside the proof of
    `thm:fixed-level-gap-size`: "The `NO` clause C3 gives both the exact equality
    and the depth-`b_{i+1}` certificate for `R_i^+`.  Equations
    `eq:canonical-complexity-invariance`--`eq:canonical-bracket-invariance` and
    the canonical chaining equation transport both statements to `R_{i+1}`,
    proving `eq:fixed-level-no-induction`."  The transported pair is the frozen
    display `eq:fixed-level-no-induction` (label line 296), whose **second**
    conclusion is `Lambda_3(R_j,1,2^{-b_j},3/5) >= D_j` at **line 295**.
  * The frozen **application site**, lines 360--379: `R_0 = Can(F_{B(n)})` at
    line 363, and the display 374--378 whose second conclusion is
    `Lambda_3(R_0,1,2^{-B(n)},3/5) >= D_0` at **line 377**, justified at line 379
    "by `lem:full-cube-seed, lem:canonical-reindexing-invariance`".
* **Supporting frozen anchors.**
  * `def:bracket` (`sections/03-preliminaries.tex`, label line 167, lines
    167--173): the bracket family is the set of submatrices of the `p`-fold
    interlace retaining at least `ceil(m x)` rows in **every outer block** and at
    least `ceil(n^p z)` columns.  Lines 194--197 forbid silently restoring an
    internal equipartition, which is why the row clause below stays a per-block
    fibre condition and is never replaced by a total row count.
  * `def:lambda` (`sections/03-preliminaries.tex`, label line 224, display lines
    226--231): `Lambda_3(M,p,x,z) = min_{j in {0,1,2}} (j + comp(bracket(M,p,x,z/2^j)))`.
  * `def:robust-seed` (`sections/03-preliminaries.tex`, label line 243, lines
    243--251): robust at depth `b` is `comp R >= 1` together with
    `Lambda_3(R,1,2^{-b},y) >= comp R`, at `y = 3/5` fixed at lines 215--220.
  * `conv:finite-slots` (`sections/02-mechanical-contract.tex:14--18`): zero-based
    slots, `[m]` is `Fin m`.

* **Banked modules consumed by pin, never restated.**
  * `IteratedCanonicalChaining.reindex`, `.Can`, `.canonEquiv`,
    `.IsCanonicalReindex`, `.isCanonicalReindex_eq_Can`,
    `.CanonicalChain` with `.isCanonicalReindex`, `.paperSeedReindexed` with
    `.paperSeedReindexed_isCanonical` and `.paperSeedReindexed_nondegenerate`.
    Nothing that module proves is re-proved here; in particular the **complexity
    half** `eq:canonical-complexity-invariance` is never re-derived.  That row
    states it as `.canonicalReindexing_invariance` /
    `.isCanonicalReindex_complexity`; the two pins **this** module actually
    consumes are its downstream forms
    `.CanonicalChain.chain_complexity` (once, inside `chain_certificate_transport`)
    and `.reindex_complexity` (once, inside `reindex_noReading`).  Neither
    `canonicalReindexing_invariance` nor `isCanonicalReindex_complexity` occurs
    in any proof term below.
  * `CommonPadding.precomposition_no_increase`, the route facade for the
    kernel-checked vendored `Workspace.ProofLemmas.SublemmaPrecompNoIncrease`;
    it is the only protocol-level fact used, and it is used exactly where the
    frozen proof says "Transporting protocols on each extracted matrix".
  * `OneLevelCompletion.SeedInterface` with `.noReading` and `.noReading_iff`,
    and `DirectOutputLower.xOut` (`x = 2^{-b}`).  The certificate predicate is
    **not** re-declared here.
  * `NPCC.bracketGE`, `NPCC.IsEquipartitionedGE`, `NPCC.Dfamily`,
    `NPCC.subgame`, `NPCC.LambdaGE` and `Workspace.Types.Interlace.interlaceFun`
    through `LegacyNPCC.Core`.
  * `FixedLevelCarriers.seedMatrix`, `.qSeed`, `.aSeed_spec` and
    `IterationAssembly.depthB` for the paper's own application point.

* **Imports.**  `EthInapproximability.ParameterizedNP.IteratedCanonicalChaining`
  only, hence transitively `OneLevelCompletion`, `DirectOutputLower`,
  `StageThreeExactScale`, `FinalOnlyDuplication`, `DepthThread`, `CommonPadding`,
  `BudgetThreadWiring`, `SizeThreadWiring`, `FixedLevelCarriers`,
  `IterationAssembly`, `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  Of these, the ones this module
  actually consumes are `IteratedCanonicalChaining`, `OneLevelCompletion`
  (`SeedInterface`, `.noReading_iff`, `fullCube`,
  `fullCubeSeed_realizes_noReading`), `DirectOutputLower` (`xOut`),
  `StageThreeExactScale` (`LambdaGE_le_D`), `CommonPadding`
  (`precomposition_no_increase`), `FixedLevelCarriers` and `IterationAssembly`;
  `FinalOnlyDuplication`, `DepthThread`, `BudgetThreadWiring` and
  `SizeThreadWiring` are closure members only and are not referenced below.
  **`LegacyNPCC.Stage12` is not in
  this module's import closure**, so the cited AGHP balanced-family axiom of
  `EXPANDER-001` stays outside it and no opt-in ledger note is owed.

* **Proof status.**  Every declaration below is **new**.  None is an inherited
  facade and none re-proves a banked fact.

## What this module lands

1. **The two induced equivalences of the frozen proof** (frozen `12:171--173`):
   `rowMap` is "the product of the identity on `[p]` with `e_X`" and `colMap`
   "applies `e_Y` in every one of the `p` coordinates"; `interlaceFun_transport`
   is the frozen "These maps preserve entries".
2. **The cardinality-preserving bijection on extraction data** (frozen
   `12:146--153` and `12:174--176`): `transportData` is the pinned bijection,
   `transportData_card` and `transportRows_filter_card` are the frozen "preserve
   ... fibre cardinalities, and total column cardinalities", and
   `transportData_bijOn` is the frozen "carry every legal bracket extraction to a
   unique legal extraction with the same retained cardinalities, and conversely".
3. **The transported protocol** (frozen `12:154--155`, `12:177`):
   `subgame_transport_complexity`, equality of the deterministic communication
   complexities of corresponding extracted matrices.
4. **`eq:canonical-bracket-invariance`** (frozen label line 163):
   `bracket_transport_complexity` is the first equality,
   `lambda_transport` the three-rung one (frozen lines 178--179, "applying it at column
   densities `z, z/2, z/4`"), and `canonicalBracketInvariance` states both at
   `Can_{m,n}(M)`, which is frozen line 165's "The same conclusions hold for
   `Can_{m,n}(M)`".
5. **The depth-`b_{i+1}` certificate transport** (frozen `12:341--350`, landing
   the second conclusion of `eq:fixed-level-no-induction` at frozen line 295):
   `chain_lambda`, `chain_certificate_transport` and
   `chain_noReading_transport` move the exact equality **and** the depth-`b`
   certificate from the level output `R_i^+` onto the canonically reindexed
   `R_{i+1}` of `eq:iterated-canonical-chaining`.  The certificate is expressed
   in the banked `OneLevelCompletion.SeedInterface.noReading` shape, i.e. in the
   very predicate the next level is invoked with; no new certificate predicate is
   declared.  `reindex_noReading` is the same transport without a chain -- the
   form the frozen application site of lines 360--379 needs -- and
   `chain_certificate_saturation` shows the transported bundle is a **saturation**
   (`Lambda_3 = D_{i+1}` exactly), so it is never an over-demand and the two
   frozen `NO`-side outputs of clause C3 are consistent when conjoined, which is
   how frozen `12:343--345` states them.
6. **The paper's own instance** (frozen `12:363` and `12:377`):
   `paperSeed_lambda` transports `Lambda_3` onto `R_0 = Can(F_{B(n)})`, and
   `paperSeed_certificate_at_scheduled_depth` delivers frozen line 377 from the
   `lem:full-cube-seed` input at the scheduled depth.  This is the
   `lem:canonical-reindexing-invariance` half of frozen line 379's two-lemma
   justification; the `lem:full-cube-seed` half stays owed (GAP-EXPOSED 3).
7. **A firing with every hypothesis discharged**:
   `fullCubeSeed_noReading_transported` runs the whole three-conjunct certificate
   transport on the route's banked depth-zero `def:robust-seed` inhabitant
   `OneLevelCompletion.fullCubeSeed_realizes_noReading`, and `qSeed_zero`
   **evaluates** the width that inhabitant carries through the banked least-integer
   accessor of frozen `12:16--21` (`q_seed(0) = 2^{a_seed(0)} - 2 = 126`), so no
   numeral below is this module's choice.

## Non-vacuity, and why the equalities are not the empty-family artefact

`NPCC.Dfamily` is a `Nat.sInf`, so it collapses to `0` on an empty family and an
equality between two `Dfamily` values would be content-free if both families were
empty.  `bracketGE_univ_mem` rules that out **generally** at every legal density
pair `x,z <= 1` -- the full row and column sets are always a legal extraction --
and `paperSeed_bracket_nonempty` runs it at the paper's own application point
`p = 1`, `x = 2^{-B(n)}`, `z = 3/5`, on carriers that
`IteratedCanonicalChaining.paperSeedReindexed_nondegenerate` shows are far larger
than one point.  So both sides of `canonicalBracketInvariance` are infima over
genuinely inhabited families at the paper's own parameters.

## Statement poles

* **`transportData_bijOn` is a claim about a pinned construction, not an
  existential.**  A trivial witness cannot satisfy it: the map must land in the
  *target* family, and membership constrains the **per-outer-block** fibre
  cardinalities (frozen `def:bracket`, `03:171`) and the total column count
  (`03:172`) simultaneously.  `transportRows_filter_card` is exactly the fibre
  clause, and it is the clause a map that merely permuted rows globally, or that
  forgot the first coordinate, would fail; the frozen warning at `03:194--197`
  ("Nothing in `def:bracket` silently restores an internal equipartition") is why
  that clause cannot be weakened to a total row count.
* **`subgame_transport_complexity` transports an equality, not an inequality.**
  One direction alone would be enough for a monotonicity statement and would be
  useless at frozen line 295, where the certificate must be *regenerated* at the
  next level rather than merely bounded.  Both directions are proved, each by one
  precomposition along the corresponding equivalence.
* **`lambda_transport` is not implied by its top rung.**  `Lambda_3` is a minimum
  over three coupled densities `z, z/2, z/4` (`def:lambda`), so an encoding that
  transported only `comp(bracket(., p, x, z))` would leave the two lower rungs
  free; the proof rewrites at all three, which is frozen lines 178--179 verbatim.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M1`/`M2`/`M4`: **no structure is declared in this module.**  The five new
  `def`s are the two induced equivalences, their two `Finset` transports and the
  pinned bijection on extraction data; none carries a complexity, budget, depth,
  density, robustness or promise field, and none bundles a derived telescope.
  Every conclusion is a theorem about those pinned constructions.
* `M3`: every schedule quantity runs through a banked definition -- `B(n)` is
  `IterationAssembly.depthB`, `q_seed` is `FixedLevelCarriers.qSeed`, `F_b` is
  `FixedLevelCarriers.seedMatrix`, `2^{-b}` is `DirectOutputLower.xOut`, and the
  three-rung density `3/5` is the frozen literal of `03-preliminaries.tex:219`
  read through the banked `SeedInterface.noReading`.  **No numeral is assigned to
  any scheduled quantity**, and the seed carriers are *evaluated* through
  `n -> depthB n -> aSeed -> qSeed -> (2^{q_seed}, q_seed)`.
* `M6`: zero-based finite slots throughout (`conv:finite-slots`); the reindexed
  side always lives on `Fin m`, `Fin n`.
* `M9`: the interlace width `p` is a free binder of the frozen lemma and is
  carried as such; the two level widths `q_i`, `Q_i` do **not** occur in this
  module at all, so no conflation of them is possible here.
* The frozen side conditions `p >= 1` and `x,z in (0,1]` of line 146 are **not**
  imposed as hypotheses: the transport uses only that the two maps are
  equivalences, so demanding them would be an over-strong hypothesis the frozen
  proof never uses.  Precisely **two** of them reappear, and only where they
  carry content -- nonemptiness of the family: the *upper* bounds `x <= 1` and
  `z <= 1`, as the two hypotheses of `bracketGE_univ_mem`.  `p >= 1` and the
  strict-positivity halves `x > 0`, `z > 0` appear **nowhere** in this module and
  are needed by no declaration in it.

## Reader counterparts

**No declaration in this module claims a reader item**, and the sweep behind that
statement was run first-hand this tranche over
`routes/parameterized-np/reader-facing/sections/`:

* The reader's only statement of canonical-reindexing invariance is
  `05-iteration.tex:152--154`, "Relabelling the finite row and column carriers by
  initial segments changes neither protocols nor retained densities" -- and it
  sits **inside the proof environment** of `thm:paper-finite-iteration`
  (`\begin{proof}` at line 146, `\end{proof}` at line 155).  Proof-internal prose
  is a navigation locus and not a claimable reader item, by the precedent
  `EFFECTIVE-MAIN-001`, `cc-t1x`, `FINAL-ONLY-DUPLICATION-001` and
  `ITERATED-CANONICAL-CHAINING-001` record; it is named here and claimed nowhere.
* `05-iteration.tex:140`, `Lambda_{R_j}(1,2^{-b_j},3/5) >= D_j` -- the robustness
  half of `thm:paper-finite-iteration`'s `NO` line -- is the reader counterpart of
  the frozen `12:295` conclusion, and `IterationAssembly`'s own header records it
  as deliberately **unclaimed at the `k`-level scale**.  It stays unclaimed: this
  module lands the **single-successor transport** of frozen `12:341--350`, not the
  `k`-level induction that reader line asserts, and claiming it here would be an
  overclaim of exactly the kind that partition was drawn to prevent.  See
  GAP-EXPOSED 2.
* `C-effectivity-details.tex:104--106` ("record the exact budgets, carrier
  equivalences, forgetful maps, least-representative sections, and the canonical
  reindexing used as the next seed") is an unlabelled item of a descriptive
  enumerate in the reader appendix, already surveyed and left unclaimed by
  `ITERATED-CANONICAL-CHAINING-001`; it stays unclaimed, being prose rather than a
  statement.
* `A-stage4-details.tex:302--313` (equal-fibre maps and normalized densities) was
  read and is a **different** fact -- it is about surjections with equal positive
  fibres inside the Stage-4 analysis, not about the increasing equivalences of
  `sec:canonical-reindexing` -- and is not cited.
* `02-preliminaries.tex:453--465` (`lem:paper-relaxed-transfer`) prints a
  "canonically isomorphic" restriction of a *relaxed* interlace; it is the reader
  form of an inherited Stage-2 transfer and is already outside this row's scope.

The canonical bracket invariance is therefore **autoformalization-only content**,
in the same sense as the canonical reindexing itself.

## GAP-EXPOSED

1. **The frozen bijection is landed as a bijection of extraction data, not as a
   claim about "the extracted matrices" as objects.**  Frozen lines 146--153
   speak of a bijection between *the extraction data in* the two bracket
   families, and `def:bracket` records a member by its extraction pair `(R,C)`
   (banked reading, `NPCC.bracketGE`); `transportData_bijOn` is that bijection at
   that reading.  What is **not** asserted is any statement about a quotient of
   submatrices up to isomorphism, which the frozen text does not state either.
2. **The collapsed-induction disclosure of
   `ITERATED-CANONICAL-CHAINING-001` GAP-EXPOSED 4 stays disclosed, and this row
   neither narrows nor discharges it.**  That row records that the banked
   `ITER-001` inductions take the *difference* form `cc (i+1) <= cc i + H i` and
   `cc (i+1) = cc i + H i + 1`, not the frozen certificate-guarded clause C2/C3
   shape of frozen `12:336--345`, and that `chainNoFold` therefore claims **only**
   the first display of `eq:fixed-level-no-induction`.  This module supplies the
   *transport half* of what the second display needs -- exactly the step frozen
   lines 345--348 name -- and nothing else: it does **not** supply clause C3, it
   does **not** turn `chainNoFold` into a certificate-carrying induction, and it
   does **not** state `eq:fixed-level-no-induction` at the `k`-level scale for any
   `j`.  Assembling the two into the frozen `NO` induction needs `thm:one-level`
   C3 in Lean (`ONELEVEL-001`) plus a fold that carries the certificate alongside
   the complexity; that fold is not written here and stays owed by `ITER-001`.
3. **The seed's certificate at the scheduled depth is an input, not an output.**
   Frozen line 377 concludes `Lambda_3(R_0,1,2^{-B(n)},3/5) >= D_0` from the two
   lemmas of line 379.  `paperSeed_certificate_at_scheduled_depth` supplies the
   `lem:canonical-reindexing-invariance` factor **outright** and takes the
   `lem:full-cube-seed` factor as an explicit named hypothesis, because the
   complexity and robustness displays of `lem:full-cube-seed` are banked only at
   requested depth `b = 0` and not at the scheduled depth `B(n)` -- the boundary
   `FixedLevelCarriers.seedAnchored_carriers` and
   `ITERATED-CANONICAL-CHAINING-001` GAP-EXPOSED 5 already record.  `D_0` is
   likewise a binder here, since the budget identity of frozen line 370 is that
   same row's GAP-EXPOSED 5 and is not claimed.
4. **Canonical inhabitation of the chain-level transport is REGISTERED AS
   DEFERRED.**  `chain_certificate_transport` and `chain_noReading_transport` are
   stated for an arbitrary `IteratedCanonicalChaining.CanonicalChain`, whose own
   canonical inhabitation that row registers as deferred (its GAP-EXPOSED 3): the
   paper's chain has `R_i^+` equal to the level-`i` constructor output, needing
   the unbuilt Stage-1--4 chain.  The paper's own instance **is** discharged for
   Parts 1--4 and 6, at the seed `R_0 = Can(F_{B(n)})` of frozen line 363
   (`paperSeed_lambda`, `paperSeed_certificate_at_scheduled_depth`,
   `paperSeed_bracket_nonempty`); the chain-level pair inherits the deferral and
   is not silently satisfied by `probeChain`, which is that row's NON-FIDELITY
   probe.
5. **The recursive canonical orders are still not transcribed.**  Inherited
   verbatim from `ITERATED-CANONICAL-CHAINING-001` GAP-EXPOSED 2: the carrier's
   order is an instance argument.  The mitigation extends: every theorem of Parts
   1--4 below is stated for an *arbitrary pair of equivalences* and only
   specialized to `canonEquiv` afterwards, so no conclusion of this module depends
   on which linear order the carrier is given.
6. **No route completion is claimed.**  The construction layer and the machine
   layer are both unlanded; this row discharges one lemma's bracket half and the
   single-successor certificate transport it licenses, and nothing else.
-/

namespace EthInapproximability.ParameterizedNP.CanonicalBracketInvariance

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.IteratedCanonicalChaining

/-! ## Part 1: the two induced equivalences (`12:171--173`) -/

/-- **The row equivalence of the frozen proof** --
`12-iteration-specification.tex:171--172`: "the row equivalence is the product of
the identity on `[p]` with `e_X`".

The `p`-fold interlace has row type `Fin p x A` (banked
`Workspace.Types.Interlace.interlaceFun`), so the frozen product is literally
`Equiv.prodCongr (Equiv.refl (Fin p)) eX`.  General in the two carriers, the
equivalence and the copy count.  Claims no reader item. -/
def rowMap {A B : Type*} (p : ℕ) (eX : A ≃ B) : Fin p × A ≃ Fin p × B :=
  Equiv.prodCongr (Equiv.refl (Fin p)) eX

/-- **Aux 1a (the row equivalence, read at a point).**  General. -/
theorem rowMap_apply {A B : Type*} (p : ℕ) (eX : A ≃ B) (r : Fin p × A) :
    rowMap p eX r = (r.1, eX r.2) := rfl

/-- **Aux 1b (the outer block index is untouched).**

This is the "identity on `[p]`" factor of frozen line 172, isolated because it is
the *only* reason the per-block fibre condition of `def:bracket`
(`03-preliminaries.tex:171`) survives the transport.  General. -/
theorem rowMap_fst {A B : Type*} (p : ℕ) (eX : A ≃ B) (r : Fin p × A) :
    (rowMap p eX r).1 = r.1 := rfl

/-- **The column equivalence of the frozen proof** --
`12-iteration-specification.tex:172--173`: "the column equivalence applies `e_Y`
in every one of the `p` coordinates".

The interlace has column type `Fin p -> C` (the paper's `Y^p`), so the frozen map
is `Equiv.piCongrRight`.  General in the two carriers, the equivalence and the
copy count.  Claims no reader item. -/
def colMap {C E : Type*} (p : ℕ) (eY : C ≃ E) : (Fin p → C) ≃ (Fin p → E) :=
  Equiv.piCongrRight fun _ => eY

/-- **Aux 1c (the column equivalence, read at one coordinate).**  General. -/
theorem colMap_apply {C E : Type*} (p : ℕ) (eY : C ≃ E) (c : Fin p → C) (i : Fin p) :
    colMap p eY c i = eY (c i) := rfl

/-- **Aux 2 (the two maps preserve entries)** --
`12-iteration-specification.tex:174`: "These maps preserve entries".

The reindexed matrix's interlace, read at `(r,c)`, is the original matrix's
interlace read at the transported pair.  This is the identity property of the
whole transport: everything below is a consequence of it plus the two Finset
bookkeeping lemmas.

Stated for the bare transported matrix `fun a c => M (eX a) (eY c)`, which is
`IteratedCanonicalChaining.reindex eX eY M` on the nose when `A = Fin m`,
`C = Fin n`; the banked definition is therefore consumed, not restated.  General
in everything, including the output type.  Claims no reader item. -/
theorem interlaceFun_transport {A B C E : Type*} (p : ℕ) (eX : A ≃ B) (eY : C ≃ E)
    (M : B → E → Bool) (r : Fin p × A) (c : Fin p → C) :
    interlaceFun (fun a c' => M (eX a) (eY c')) p r c
      = interlaceFun M p (rowMap p eX r) (colMap p eY c) := rfl

/-! ## Part 2: the bijection on extraction data (`12:146--153`, `12:174--176`) -/

/-- **The transported row set.**  `def:bracket` records a bracket member by its
extraction data (banked `NPCC.bracketGE`), and the row half of that datum is a
`Finset` of interlace rows; the frozen row equivalence moves it.  General. -/
def transportRows {A B : Type*} (p : ℕ) (eX : A ≃ B) (R : Finset (Fin p × A)) :
    Finset (Fin p × B) :=
  R.map (rowMap p eX).toEmbedding

/-- **The transported column set.**  General. -/
def transportCols {C E : Type*} (p : ℕ) (eY : C ≃ E) (S : Finset (Fin p → C)) :
    Finset (Fin p → E) :=
  S.map (colMap p eY).toEmbedding

/-- **The bijection on extraction data** --
`12-iteration-specification.tex:146--153`: "the increasing equivalences induce a
cardinality-preserving bijection between the extraction data in
`bracket(Can(M),p,x,z)` and `bracket(M,p,x,z)`".

The map is pinned, not existentially quantified: it is the product of the two
`Finset` transports, which is the frozen sentence's own "induced by" reading.
That it *restricts* to a bijection between the two bracket families is
`transportData_bijOn`; that it is *cardinality preserving* is
`transportData_card` together with `transportRows_filter_card`.  General in the
four carriers, the two equivalences and the copy count.  Claims no reader item. -/
def transportData {A B C E : Type*} (p : ℕ) (eX : A ≃ B) (eY : C ≃ E) :
    Finset (Fin p × A) × Finset (Fin p → C) ≃
      Finset (Fin p × B) × Finset (Fin p → E) :=
  Equiv.prodCongr (rowMap p eX).finsetCongr (colMap p eY).finsetCongr

/-- **Aux 3 (the bijection, read component by component).**  General. -/
theorem transportData_apply {A B C E : Type*} (p : ℕ) (eX : A ≃ B) (eY : C ≃ E)
    (RC : Finset (Fin p × A) × Finset (Fin p → C)) :
    transportData p eX eY RC = (transportRows p eX RC.1, transportCols p eY RC.2) := rfl

/-- **Aux 4 (the bijection is cardinality preserving)** --
`12-iteration-specification.tex:147` ("cardinality-preserving") and `:174--175`
("total column cardinalities").  General. -/
theorem transportData_card {A B C E : Type*} (p : ℕ) (eX : A ≃ B) (eY : C ≃ E)
    (RC : Finset (Fin p × A) × Finset (Fin p → C)) :
    (transportData p eX eY RC).1.card = RC.1.card ∧
      (transportData p eX eY RC).2.card = RC.2.card :=
  ⟨Finset.card_map _, Finset.card_map _⟩

/-- **Aux 5 (identity law).**  Along the identity equivalences the transport does
nothing.  This is the extraction-data half of
`IteratedCanonicalChaining.Can_fin_id`: on the slot types themselves the frozen
relabelling is trivial, which is why the frozen chaining is applied to the level
*output carriers* and not to the slot types.  General. -/
theorem transportData_refl {A C : Type*} (p : ℕ)
    (RC : Finset (Fin p × A) × Finset (Fin p → C)) :
    transportData p (Equiv.refl A) (Equiv.refl C) RC = RC := by
  refine Prod.ext ?_ ?_
  · change transportRows p (Equiv.refl A) RC.1 = RC.1
    refine Finset.ext fun a => ?_
    simp [transportRows, rowMap]
  · change transportCols p (Equiv.refl C) RC.2 = RC.2
    refine Finset.ext fun c => ?_
    simp [transportCols, colMap]

/-- **Aux 6 (round trip).**  Transporting along the inverse pair inverts the
transport, which is the frozen "and conversely" of line 176.  General. -/
theorem transportData_symm_apply {A B C E : Type*} (p : ℕ) (eX : A ≃ B) (eY : C ≃ E)
    (ST : Finset (Fin p × B) × Finset (Fin p → E)) :
    (transportData p eX eY).symm ST
      = (transportRows p eX.symm ST.1, transportCols p eY.symm ST.2) := by
  have hrow : (rowMap p eX).symm = rowMap p eX.symm := Equiv.ext fun _ => rfl
  have hcol : (colMap p eY).symm = colMap p eY.symm := Equiv.ext fun _ => rfl
  refine Prod.ext ?_ ?_
  · change ST.1.map ((rowMap p eX).symm).toEmbedding = transportRows p eX.symm ST.1
    rw [hrow]
    rfl
  · change ST.2.map ((colMap p eY).symm).toEmbedding = transportCols p eY.symm ST.2
    rw [hcol]
    rfl

/-- **Aux 7 (monotonicity).**  The row transport preserves inclusion of extraction
data.  General. -/
theorem transportRows_subset {A B : Type*} (p : ℕ) (eX : A ≃ B)
    {R R' : Finset (Fin p × A)} (h : R ⊆ R') :
    transportRows p eX R ⊆ transportRows p eX R' :=
  Finset.map_subset_map.2 h

/-- **The transport commutes with the outer-block fibre** --
`12-iteration-specification.tex:174`: "These maps preserve ... fibre
cardinalities".

The frozen bracket row condition of `def:bracket` (`03-preliminaries.tex:171`) is
per outer block: "at least `ceil(mx)` rows in every outer block".  Because the row
equivalence is the identity on `[p]` (`rowMap_fst`), the block-`q` fibre of the
transported row set is the transport of the block-`q` fibre.  General. -/
theorem transportRows_filter {A B : Type*} (p : ℕ) (eX : A ≃ B)
    (R : Finset (Fin p × A)) (q : Fin p) :
    (transportRows p eX R).filter (fun r => r.1 = q)
      = transportRows p eX (R.filter (fun r => r.1 = q)) := by
  refine Finset.ext fun a => ?_
  constructor
  · intro ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    obtain ⟨r, hr, hra⟩ := Finset.mem_map.1 ha1
    refine Finset.mem_map.2 ⟨r, Finset.mem_filter.2 ⟨hr, ?_⟩, hra⟩
    have hra' : rowMap p eX r = a := hra
    have hq : (rowMap p eX r).1 = q := by rw [hra']; exact ha2
    rwa [rowMap_fst] at hq
  · intro ha
    obtain ⟨r, hr, hra⟩ := Finset.mem_map.1 ha
    obtain ⟨hr', hq⟩ := Finset.mem_filter.1 hr
    refine Finset.mem_filter.2 ⟨Finset.mem_map.2 ⟨r, hr', hra⟩, ?_⟩
    have hra' : rowMap p eX r = a := hra
    rw [← hra', rowMap_fst]
    exact hq

/-- **Aux 8 (equal fibre cardinalities).**  The numeric form of
`transportRows_filter`, which is what the frozen row clause compares against a
ceiling.  General. -/
theorem transportRows_filter_card {A B : Type*} (p : ℕ) (eX : A ≃ B)
    (R : Finset (Fin p × A)) (q : Fin p) :
    ((transportRows p eX R).filter (fun r => r.1 = q)).card
      = (R.filter (fun r => r.1 = q)).card := by
  rw [transportRows_filter, transportRows, Finset.card_map]

/-- **The transported row set is equipartitioned exactly when the original is** --
the row clause of `def:bracket` (`03-preliminaries.tex:171`) under the frozen row
equivalence, at the banked `NPCC.IsEquipartitionedGE` reading over
`Q = Finset.univ`.

The threshold `T` is held fixed here; that the two *ceilings* agree is the
cardinality equation supplied at the use site
(`transportData_mem_bracket_iff`).  General. -/
theorem transportRows_isEquipartitionedGE_iff {A B : Type*} (p : ℕ) (eX : A ≃ B)
    (R : Finset (Fin p × A)) (T : ℕ) :
    IsEquipartitionedGE (transportRows p eX R) (Finset.univ : Finset (Fin p)) T
      ↔ IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T := by
  constructor
  · intro h q hq
    have := h q hq
    rwa [transportRows_filter_card] at this
  · intro h q hq
    have := h q hq
    rwa [transportRows_filter_card]

/-- **Legality is transported in both directions** --
`12-iteration-specification.tex:175--176`: the two maps "carry every legal bracket
extraction to a unique legal extraction with the same retained cardinalities, and
conversely".

Both bracket thresholds are computed from carrier cardinalities, and the two
equivalences make those cardinalities equal, so the *same* pair of ceilings is
compared on both sides.  General in the four carriers, the two equivalences, the
copy count and the two densities.  Claims no reader item. -/
theorem transportData_mem_bracket_iff {A B C E : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Fintype E] (p : ℕ) (eX : A ≃ B) (eY : C ≃ E) (x z : ℝ)
    (RC : Finset (Fin p × A) × Finset (Fin p → C)) :
    transportData p eX eY RC ∈ bracketGE B E p x z ↔ RC ∈ bracketGE A C p x z := by
  have hA : Fintype.card B = Fintype.card A := (Fintype.card_congr eX).symm
  have hE : Fintype.card E = Fintype.card C := (Fintype.card_congr eY).symm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hA] at h1
      exact (transportRows_isEquipartitionedGE_iff p eX RC.1 _).1 h1
    · rw [hE] at h2
      rwa [transportData_apply, transportCols, Finset.card_map] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hA]
      exact (transportRows_isEquipartitionedGE_iff p eX RC.1 _).2 h1
    · rw [hE, transportData_apply, transportCols, Finset.card_map]
      exact h2

/-- **The frozen bijection between the two families** --
`12-iteration-specification.tex:146--153` and `:175--176`.

`transportData` restricts to a bijection from `bracket(M', p, x, z)` on the
reindexed carriers onto `bracket(M, p, x, z)` on the original ones, where `M'` is
the transported matrix.  Injectivity and surjectivity both come from the pinned
`Equiv`, so nothing is chosen: this is the frozen "unique legal extraction".

Statement pole (why a trivial witness fails): membership in the *target* family
constrains the per-outer-block fibre cardinalities and the total column count at
once, so a map forgetting the outer coordinate, or permuting rows across blocks,
lands outside `bracketGE` as soon as the frozen row ceiling is not met in every
block -- the frozen `03:194--197` warning that `def:bracket` never silently
restores an internal equipartition is exactly this.  General.  Claims no reader
item. -/
theorem transportData_bijOn {A B C E : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Fintype E] (p : ℕ) (eX : A ≃ B) (eY : C ≃ E) (x z : ℝ) :
    Set.BijOn (transportData p eX eY) (bracketGE A C p x z) (bracketGE B E p x z) := by
  refine ⟨fun RC hRC => (transportData_mem_bracket_iff p eX eY x z RC).2 hRC,
    fun a _ b _ hab => (transportData p eX eY).injective hab, fun ST hST => ?_⟩
  refine ⟨(transportData p eX eY).symm ST, ?_, (transportData p eX eY).apply_symm_apply ST⟩
  rw [← transportData_mem_bracket_iff p eX eY x z, (transportData p eX eY).apply_symm_apply]
  exact hST

/-! ## Part 3: the transported protocol (`12:154--155`, `12:177`) -/

/-- **Corresponding extracted matrices have equal complexity** --
`12-iteration-specification.tex:154--155`: "Corresponding extracted matrices are
related by row and column equivalences and therefore have equal deterministic
communication complexity", proved at `:177` by "Transporting protocols on
each extracted matrix".

Both directions are precomposition, consumed by pin through
`CommonPadding.precomposition_no_increase` -- the route facade for the
kernel-checked vendored `Workspace.ProofLemmas.SublemmaPrecompNoIncrease`.  It is
not re-exported here.

Statement pole: the frozen sentence transports an *equality*, and the certificate
regeneration at frozen line 295 needs the equality; one inequality alone would
only give monotonicity.  General in the four carriers, the two equivalences, the
copy count, the output type and both extraction sets.  Claims no reader item. -/
theorem subgame_transport_complexity {A B C E : Type*} (p : ℕ) (eX : A ≃ B)
    (eY : C ≃ E) (M : B → E → Bool) (R : Finset (Fin p × A)) (S : Finset (Fin p → C)) :
    D (subgame (interlaceFun (fun a c => M (eX a) (eY c)) p) R S)
      = D (subgame (interlaceFun M p) (transportRows p eX R) (transportCols p eY S)) := by
  have hrow : ∀ r ∈ R, rowMap p eX r ∈ transportRows p eX R := fun _ hr =>
    Finset.mem_map_of_mem _ hr
  have hcol : ∀ c ∈ S, colMap p eY c ∈ transportCols p eY S := fun _ hc =>
    Finset.mem_map_of_mem _ hc
  have hmemR : ∀ a ∈ transportRows p eX R, (rowMap p eX).symm a ∈ R := fun _ ha =>
    Finset.mem_map_equiv.1 ha
  have hmemC : ∀ c ∈ transportCols p eY S, (colMap p eY).symm c ∈ S := fun _ hc =>
    Finset.mem_map_equiv.1 hc
  refine le_antisymm ?_ ?_
  · have hL : subgame (interlaceFun (fun a c => M (eX a) (eY c)) p) R S
        = fun u v =>
          subgame (interlaceFun M p) (transportRows p eX R) (transportCols p eY S)
            ⟨rowMap p eX u.1, hrow u.1 u.2⟩ ⟨colMap p eY v.1, hcol v.1 v.2⟩ := rfl
    rw [hL]
    exact CommonPadding.precomposition_no_increase _ _ _
  · have hR : subgame (interlaceFun M p) (transportRows p eX R) (transportCols p eY S)
        = fun u v =>
          subgame (interlaceFun (fun a c => M (eX a) (eY c)) p) R S
            ⟨(rowMap p eX).symm u.1, hmemR u.1 u.2⟩
            ⟨(colMap p eY).symm v.1, hmemC v.1 v.2⟩ := by
      funext u v
      change interlaceFun M p u.1 v.1
        = interlaceFun (fun a c => M (eX a) (eY c)) p _ _
      rw [interlaceFun_transport p eX eY M ((rowMap p eX).symm u.1)
        ((colMap p eY).symm v.1), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hR]
    exact CommonPadding.precomposition_no_increase _ _ _

/-! ## Part 4: `eq:canonical-bracket-invariance` (`12:157--165`) -/

/-- **The first equality of `eq:canonical-bracket-invariance`** --
`12-iteration-specification.tex`, label line 163:
`comp(bracket(Can(M),p,x,z)) = comp(bracket(M,p,x,z))`, here in the frozen
generality of the proof (an arbitrary pair of equivalences).  The frozen text
that carries that generality is lines **171--173**, which name the two induced
maps for the interlace without constraining `e_X`, `e_Y`; lines 169--170 state
the *complexity* half `eq:canonical-complexity-invariance` and do not themselves
assert arbitrariness.  Stating this for an arbitrary pair is strictly stronger
than the frozen lemma and is specialized back to `canonEquiv` at
`canonicalBracketInvariance` (GAP-EXPOSED 5).

The two `Nat.sInf`s are taken over the *same* set of integers: the frozen
bijection `transportData_bijOn` matches members up, and
`subgame_transport_complexity` matches the values.  General in the four carriers,
the two equivalences, the copy count, the matrix and the two densities.  Claims no
reader item. -/
theorem bracket_transport_complexity {A B C E : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Fintype E] (p : ℕ) (eX : A ≃ B) (eY : C ≃ E) (M : B → E → Bool)
    (x z : ℝ) :
    Dfamily (interlaceFun (fun a c => M (eX a) (eY c)) p) (bracketGE A C p x z)
      = Dfamily (interlaceFun M p) (bracketGE B E p x z) := by
  have hset :
      {d : ℕ | ∃ RC ∈ bracketGE A C p x z,
          d = D (subgame (interlaceFun (fun a c => M (eX a) (eY c)) p) RC.1 RC.2)}
        = {d : ℕ | ∃ ST ∈ bracketGE B E p x z,
          d = D (subgame (interlaceFun M p) ST.1 ST.2)} := by
    refine Set.ext fun d => ?_
    constructor
    · rintro ⟨RC, hRC, rfl⟩
      exact ⟨transportData p eX eY RC, (transportData_mem_bracket_iff p eX eY x z RC).2 hRC,
        subgame_transport_complexity p eX eY M RC.1 RC.2⟩
    · rintro ⟨ST, hST, rfl⟩
      refine ⟨(transportData p eX eY).symm ST, ?_, ?_⟩
      · rw [← transportData_mem_bracket_iff p eX eY x z,
          (transportData p eX eY).apply_symm_apply]
        exact hST
      · have hst := (transportData p eX eY).apply_symm_apply ST
        have h1 : transportRows p eX ((transportData p eX eY).symm ST).1 = ST.1 :=
          congrArg Prod.fst hst
        have h2 : transportCols p eY ((transportData p eX eY).symm ST).2 = ST.2 :=
          congrArg Prod.snd hst
        have h := subgame_transport_complexity p eX eY M
          ((transportData p eX eY).symm ST).1 ((transportData p eX eY).symm ST).2
        rw [h1, h2] at h
        exact h.symm
  unfold Dfamily
  rw [hset]

/-- **The three-rung equality of `eq:canonical-bracket-invariance`** --
`12-iteration-specification.tex`, label line 163, second display, proved at
lines **178--179**: "applying it at column densities `z, z/2, z/4` proves the
displayed three-rung equality".  (Frozen line 181 is empty; the sentence ends at
179 and the proof closes at 180.)

`Lambda_3` is the banked `NPCC.LambdaGE`, the minimum of `def:lambda`
(`03-preliminaries.tex:226--231`) over the three coupled rungs; the proof is the
first equality applied at each of the three densities and nothing else.

Statement pole: transporting only the top rung would leave the two lower rungs
free, and `def:robust-seed` reads all three; so the three rewrites are content,
not repetition.  General.  Claims no reader item. -/
theorem lambda_transport {A B C E : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype E] (p : ℕ) (eX : A ≃ B) (eY : C ≃ E) (M : B → E → Bool) (x z : ℝ) :
    LambdaGE (fun a c => M (eX a) (eY c)) p x z = LambdaGE M p x z := by
  unfold LambdaGE
  rw [bracket_transport_complexity p eX eY M x z,
    bracket_transport_complexity p eX eY M x (z / 2),
    bracket_transport_complexity p eX eY M x (z / 4)]

/-- **`eq:canonical-bracket-invariance` at the general reindexing** --
the banked `IteratedCanonicalChaining.reindex` is definitionally the transported
matrix of Parts 1--4, so both frozen equalities hold for it verbatim.  General.
Claims no reader item. -/
theorem reindex_bracket_invariance {X Y : Type*} [Fintype X] [Fintype Y] {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Bool) (p : ℕ) (x z : ℝ) :
    Dfamily (interlaceFun (reindex eX eY M) p) (bracketGE (Fin m) (Fin n) p x z)
        = Dfamily (interlaceFun M p) (bracketGE X Y p x z) ∧
      LambdaGE (reindex eX eY M) p x z = LambdaGE M p x z :=
  ⟨bracket_transport_complexity p eX eY M x z, lambda_transport p eX eY M x z⟩

/-- **`eq:canonical-bracket-invariance`** --
`12-iteration-specification.tex`, label line 163, at the canonical reindexing
`Can_{m,n}(M)` of `def:canonical-reindexing`, which is frozen line 165's "The
same conclusions hold for `Can_{m,n}(M)`":

```
comp(bracket(Can(M),p,x,z)) = comp(bracket(M,p,x,z)),
Lambda_3(Can(M),p,x,z)      = Lambda_3(M,p,x,z).
```

This is the deliverable of this row: the bracket half that
`ITERATED-CANONICAL-CHAINING-001` records as its GAP-EXPOSED 1.  The complexity
half `eq:canonical-complexity-invariance` is **not** restated -- it is that row's
`canonicalReindexing_invariance`, and where this module needs it below it is
consumed by pin through that theorem's downstream forms
`CanonicalChain.chain_complexity` and `reindex_complexity`.

The frozen side conditions `p >= 1`, `x,z in (0,1]` (line 146) are absent by
design: the frozen proof uses only that the two maps are equivalences, so imposing
them would be an over-strong hypothesis.  Where two of them carry content --
nonemptiness of the family -- see `bracketGE_univ_mem`, which assumes the upper
bounds `x <= 1`, `z <= 1` and nothing else.

General in the carriers, their orders, the slot counts, the matrix, the copy count
and the two densities.  Claims no reader item. -/
theorem canonicalBracketInvariance {X Y : Type*} [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y] {m n : ℕ} (hm : Fintype.card X = m)
    (hn : Fintype.card Y = n) (M : X → Y → Bool) (p : ℕ) (x z : ℝ) :
    Dfamily (interlaceFun (Can hm hn M) p) (bracketGE (Fin m) (Fin n) p x z)
        = Dfamily (interlaceFun M p) (bracketGE X Y p x z) ∧
      LambdaGE (Can hm hn M) p x z = LambdaGE M p x z :=
  reindex_bracket_invariance (canonEquiv X hm) (canonEquiv Y hn) M p x z

/-- **The invariance, read through the frozen typed assertion** --
the form every consumer of `eq:iterated-canonical-chaining` actually needs:
whatever satisfies the typed assertion of frozen lines 127--136 for `M` has `M`'s
bracket complexities and `M`'s `Lambda_3`.

The banked `IteratedCanonicalChaining.isCanonicalReindex_eq_Can` is consumed by
pin; nothing it proves is restated.  General.  Claims no reader item. -/
theorem isCanonicalReindex_bracket {X Y : Type*} [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y] {m n : ℕ} {M : X → Y → Bool}
    {R : Fin m → Fin n → Bool} (h : IsCanonicalReindex M m n R) (p : ℕ) (x z : ℝ) :
    Dfamily (interlaceFun R p) (bracketGE (Fin m) (Fin n) p x z)
        = Dfamily (interlaceFun M p) (bracketGE X Y p x z) ∧
      LambdaGE R p x z = LambdaGE M p x z := by
  obtain ⟨hm, hn, hEq⟩ := isCanonicalReindex_eq_Can h
  rw [hEq]
  exact canonicalBracketInvariance hm hn M p x z

/-! ## Part 5: non-vacuity of the two families -/

/-- **Every legal density pair admits a bracket extraction** (LANE-GATE 3).

`NPCC.Dfamily` is a `Nat.sInf` and collapses to `0` on the empty family, so an
equality between two `Dfamily` values would be content-free if both families were
empty.  They never are: the full row set is equipartitioned at every ceiling
`ceil(|A| x)` with `x <= 1` (its block-`q` fibre is all of `{q} x A`), and the
full column set meets every ceiling `ceil(|C|^p z)` with `z <= 1`.

This is the place -- and the only place -- where any of the frozen side conditions
of line 146 has content.  What appears here as an explicit hypothesis is exactly
the pair of **upper** bounds `x <= 1`, `z <= 1`; the frozen `p >= 1` and the
strict-positivity halves `x > 0`, `z > 0` are not assumed here either, since the
`(univ, univ)` witness meets both ceilings without them.

**Relation to the vendored fact.**  `NPCC.bracketGE.nonempty`
(`vendor/npc-cc/NPCC/DefsAux.lean:139--142`) already proves nonemptiness with the
same `(Finset.univ, Finset.univ)` witness and the same fibre step.  This lemma is
**strictly stronger** in two ways and is landed for those deltas, not as a
restatement: it drops the vendored `hX : 1 <= Fintype.card X` and the
`[DecidableEq X]` instance, and it **pins the member** rather than asserting
`.Nonempty`, which is what LANE-GATE 3 and `transportData_mem_bracket_iff` need.
`bracket_nonempty_iff` then transports inhabitation along the bijection.

General in the two carriers, the copy count and the two
densities.  Claims no reader item. -/
theorem bracketGE_univ_mem {A C : Type*} [Fintype A] [Fintype C] (p : ℕ) {x z : ℝ}
    (hx : x ≤ 1) (hz : z ≤ 1) :
    ((Finset.univ : Finset (Fin p × A)), (Finset.univ : Finset (Fin p → C)))
      ∈ bracketGE A C p x z := by
  refine ⟨fun q _ => ?_, ?_⟩
  · have hfilter : (Finset.univ : Finset (Fin p × A)).filter (fun r => r.1 = q)
        = (Finset.univ : Finset A).map
            ⟨fun a : A => (q, a), fun _ _ h => congrArg Prod.snd h⟩ := by
      refine Finset.ext fun r => ?_
      constructor
      · intro hr
        have hq : r.1 = q := (Finset.mem_filter.1 hr).2
        exact Finset.mem_map.2 ⟨r.2, Finset.mem_univ _, Prod.ext hq.symm rfl⟩
      · intro hr
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hr
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
    rw [hfilter, Finset.card_map, Finset.card_univ]
    refine Nat.ceil_le.2 ?_
    have hnn : (0 : ℝ) ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
    nlinarith
  · rw [Finset.card_univ]
    have hcard : Fintype.card (Fin p → C) = Fintype.card C ^ p := by
      rw [Fintype.card_fun, Fintype.card_fin]
    rw [hcard]
    refine Nat.ceil_le.2 ?_
    have hnn : (0 : ℝ) ≤ (Fintype.card C : ℝ) ^ p := by positivity
    push_cast
    nlinarith

/-- **Aux 9 (nonemptiness transports).**  A corollary of the frozen bijection: the
two families of `eq:canonical-bracket-invariance` are simultaneously inhabited, so
neither side of the equality is the empty-family artefact while the other is a
genuine minimum.  General.  Claims no reader item. -/
theorem bracket_nonempty_iff {A B C E : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype E] (p : ℕ) (eX : A ≃ B) (eY : C ≃ E) (x z : ℝ) :
    (bracketGE A C p x z).Nonempty ↔ (bracketGE B E p x z).Nonempty := by
  constructor
  · rintro ⟨RC, hRC⟩
    exact ⟨transportData p eX eY RC, (transportData_mem_bracket_iff p eX eY x z RC).2 hRC⟩
  · rintro ⟨ST, hST⟩
    refine ⟨(transportData p eX eY).symm ST, ?_⟩
    rw [← transportData_mem_bracket_iff p eX eY x z,
      (transportData p eX eY).apply_symm_apply]
    exact hST

/-! ## Part 6: the depth-`b_{i+1}` certificate transport (`12:341--350`, landing the
second conclusion of `eq:fixed-level-no-induction` at `12:295`) -/

/-- **The bracket invariance along the canonical chain** --
`12-iteration-specification.tex:345--348`: "Equations
`eq:canonical-complexity-invariance`--`eq:canonical-bracket-invariance` and the
canonical chaining equation transport both statements to `R_{i+1}`."

At every level of an `IteratedCanonicalChaining.CanonicalChain` the relabelled
matrix `R_{i+1}` has the bracket complexities and the `Lambda_3` of the level
output `R_i^+` it relabels.  The chaining equation enters only through that row's
`CanonicalChain.isCanonicalReindex`, consumed by pin.

General in the specification, the chain, the level, the copy count and the two
densities.  Claims no reader item. -/
theorem chain_lambda {S : FixedLevelCarriers.LevelCarrierSpec} (C : CanonicalChain S)
    (i p : ℕ) (x z : ℝ) :
    Dfamily (interlaceFun (C.lev (i + 1)) p)
          (bracketGE (Fin (S.rowCarrier (i + 1))) (Fin (S.colCarrier (i + 1))) p x z)
        = Dfamily (interlaceFun (C.out i) p) (bracketGE (C.Row i) (C.Col i) p x z) ∧
      LambdaGE (C.lev (i + 1)) p x z = LambdaGE (C.out i) p x z :=
  isCanonicalReindex_bracket (C.isCanonicalReindex i) p x z

/-- **The depth-`b_{i+1}` certificate transport** --
`12-iteration-specification.tex:341--350`, delivering the second conclusion of
`eq:fixed-level-no-induction` at **frozen line 295** for one successor index.

Frozen text: "The `NO` clause C3 gives both the exact equality and the depth-
`b_{i+1}` certificate for `R_i^+`.  Equations ... and the canonical chaining
equation transport both statements to `R_{i+1}`."  That is exactly this theorem:
the hypotheses are C3's two outputs *on the level output*, and the conclusions are
the same two statements *on the chained level matrix*, at the same integer and the
same depth.

`x = 2^{-b}` is the banked `DirectOutputLower.xOut`, and the column density is the
frozen literal `3/5` fixed at `03-preliminaries.tex:215--220`; the complexity half
is the banked `CanonicalChain.chain_complexity`, consumed by pin.

**Scope (GAP-EXPOSED 2).**  This is the *transport* of frozen lines 345--348 at one
successor index.  It is not clause C3 (`ONELEVEL-001`), and it is not the
`k`-level `NO` induction of `eq:fixed-level-no-induction`: assembling it into that
induction needs a fold carrying the certificate alongside the complexity, which
`chainNoFold` deliberately does not do.

General in the specification, the chain, the level, the depth and the scale.
Claims no reader item. -/
theorem chain_certificate_transport {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (i b Dnext : ℕ)
    (hcomp : D (C.out i) = Dnext)
    (hcert : Dnext ≤ LambdaGE (C.out i) 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5)) :
    D (C.lev (i + 1)) = Dnext ∧
      Dnext ≤ LambdaGE (C.lev (i + 1)) 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5) := by
  refine ⟨(C.chain_complexity i).trans hcomp, ?_⟩
  rw [(chain_lambda C i 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5)).2]
  exact hcert

/-- **The same transport, in the banked interface shape the next level receives** --
`12-iteration-specification.tex:341--350` read through
`OneLevelCompletion.SeedInterface.noReading`, which is the route's transcription of
`def:robust-seed` (`03-preliminaries.tex:243--251`) at a public scale.

The frozen sentence's point is that the next public record carries `R_{i+1}` and
nothing construction-specific (frozen `12:380--382`), so the certificate must
arrive at the *reindexed* matrix in the very predicate the next invocation reads.
This theorem moves the whole three-conjunct reading -- exact complexity, depth-`b`
three-rung bound, and the `comp >= 1` clause of `def:robust-seed` -- from the level
output onto the chained level matrix, at the same three integers.

No certificate predicate is declared here: `SeedInterface` and `.noReading` are
banked and are consumed by pin through `OneLevelCompletion.noReading_iff`.

General in the specification, the chain, the level and the three public integers.
Claims no reader item. -/
theorem chain_noReading_transport {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (i c y b : ℕ)
    (h : (OneLevelCompletion.SeedInterface.mk (C.out i) c y b).noReading) :
    (OneLevelCompletion.SeedInterface.mk (C.lev (i + 1)) c y b).noReading := by
  obtain ⟨h1, h2, h3⟩ := OneLevelCompletion.noReading_iff (C.out i) c y b |>.1 h
  refine OneLevelCompletion.noReading_iff (C.lev (i + 1)) c y b |>.2 ⟨?_, ?_, h3⟩
  · exact (chain_certificate_transport C i b c h1 h2).1
  · exact (chain_certificate_transport C i b c h1 h2).2

/-- **The same transport at the bare reindexing, without a chain** --
`12-iteration-specification.tex:345--348` applied to a single matrix rather than
to a level of `eq:iterated-canonical-chaining`.

This is the form the frozen application site of lines 360--379 needs (there is no
chain there, only the seed), and it is the form the non-vacuity firing of Part 8
uses.  It is a strictly more general statement than `chain_noReading_transport`,
which specializes it along the chaining equation.

General in the carriers, the slot counts, the two equivalences, the matrix and the
three public integers.  Claims no reader item. -/
theorem reindex_noReading {X Y : Type*} [Fintype X] [Fintype Y] {m n : ℕ}
    (eX : Fin m ≃ X) (eY : Fin n ≃ Y) (M : X → Y → Bool) (c y b : ℕ)
    (h : (OneLevelCompletion.SeedInterface.mk M c y b).noReading) :
    (OneLevelCompletion.SeedInterface.mk (reindex eX eY M) c y b).noReading := by
  obtain ⟨h1, h2, h3⟩ := (OneLevelCompletion.noReading_iff M c y b).1 h
  refine (OneLevelCompletion.noReading_iff _ c y b).2 ⟨?_, ?_, h3⟩
  · rw [reindex_complexity]
    exact h1
  · have hl := lambda_transport 1 eX eY M (DirectOutputLower.xOut b) ((3 : ℝ) / 5)
    change c ≤ LambdaGE (fun u v => M (eX u) (eY v)) 1 (DirectOutputLower.xOut b)
      ((3 : ℝ) / 5)
    rw [hl]
    exact h2

/-- **Hypothesis consistency for the certificate transport: the bundle is a
saturation, never an over-demand.**

The two hypotheses of `chain_certificate_transport` are `comp(R_i^+) = D_{i+1}`
and `Lambda_3(R_i^+,1,2^{-b},3/5) >= D_{i+1}`.  Because the banked
`StageThreeExactScale.LambdaGE_le_D` bounds `Lambda_3` above by the ambient
complexity at every legal density pair, the bundle forces
`Lambda_3(R_i^+,1,2^{-b},3/5) = D_{i+1}` exactly -- so it can never demand more
than the frozen text does, and **no `False` follows from conjoining the two
frozen `NO`-side outputs of clause C3**, which frozen `12:343--345` states as the
simultaneous output of one certificate rather than as two promise cases.

The row-carrier nonemptiness the bound needs is **derived**, not assumed: it is the
banked `FixedLevelCarriers.carriers_two_le_succ` read through the chain's own
`rowCard` field.  The row density is the banked `DirectOutputLower.xOut`, whose
`<= 1` is proved here from `xOut b = (2^b)⁻¹` rather than assigned.

General in the specification, the chain, the level, the depth and the scale.
Claims no reader item. -/
theorem chain_certificate_saturation {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (i b Dnext : ℕ)
    (hcomp : D (C.out i) = Dnext)
    (hcert : Dnext ≤ LambdaGE (C.out i) 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5)) :
    LambdaGE (C.out i) 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5) = Dnext ∧
      LambdaGE (C.lev (i + 1)) 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5) = Dnext := by
  have hx : DirectOutputLower.xOut b ≤ 1 := by
    rw [DirectOutputLower.xOut, inv_le_one_iff₀]
    exact Or.inr (one_le_pow₀ (by norm_num))
  have hrow : 1 ≤ Fintype.card (C.Row i) := by
    rw [C.rowCard i]
    have := (FixedLevelCarriers.carriers_two_le_succ S i).1
    omega
  have hle := StageThreeExactScale.LambdaGE_le_D (C.out i) hx
    (by norm_num : ((3 : ℝ) / 5) ≤ 1) hrow
  have hsat : LambdaGE (C.out i) 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5) = Dnext := by
    omega
  refine ⟨hsat, ?_⟩
  rw [(chain_lambda C i 1 (DirectOutputLower.xOut b) ((3 : ℝ) / 5)).2]
  exact hsat

/-! ## Part 7: the paper's own instance (`12:363`, `12:374--379`)

The frozen lexicographic order on the seed row carrier `{0,1}^{q_seed}`
(`12:96--97`) is the banked `IteratedCanonicalChaining.seedRowOrder`, made a local
instance here for the same reason that row makes it one: Part 7 is a fidelity
claim about the paper's own object, so the carrier's order is supplied rather than
taken as a binder.  It is local and is not exported. -/

attribute [local instance] seedRowOrder

/-- **Canonical inhabitation: the bracket invariance at the paper's own `R_0`** --
`12-iteration-specification.tex:363`, `R_0 = Can(F_{B(n)})`.

The instance is the banked `IteratedCanonicalChaining.paperSeedReindexed`, i.e. the
paper's own object at the paper's own application site with the paper's own
lexicographic carrier order, whose defining data are *evaluated* through the banked
chain `n -> depthB n -> aSeed -> qSeed -> (2^{q_seed}, q_seed)`; **no numeral is
assigned to anything**.  So this is the paper's instance inhabiting the transport,
not a synthetic probe.

General in the source size, the copy count and the two densities.  Claims no reader
item. -/
theorem paperSeed_lambda (n p : ℕ) (x z : ℝ) :
    LambdaGE (paperSeedReindexed n) p x z
      = LambdaGE (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n)) p x z :=
  (isCanonicalReindex_bracket (paperSeedReindexed_isCanonical n).1 p x z).2

/-- **The bracket-complexity half at the paper's own `R_0`.**  The companion of
`paperSeed_lambda` at a single rung.  General.  Claims no reader item. -/
theorem paperSeed_bracket_complexity (n p : ℕ) (x z : ℝ) :
    Dfamily (interlaceFun (paperSeedReindexed n) p)
        (bracketGE (Fin (2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n)))
          (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n))) p x z)
      = Dfamily
          (interlaceFun (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n)) p)
          (bracketGE (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n)) → Bool)
            (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n))) p x z) :=
  (isCanonicalReindex_bracket (paperSeedReindexed_isCanonical n).1 p x z).1

/-- **Frozen line 377 at the paper's own seed** --
`12-iteration-specification.tex:374--379`:

```
comp(R_0) = D_0,   Lambda_3(R_0, 1, 2^{-B(n)}, 3/5) >= D_0
```
"by `lem:full-cube-seed, lem:canonical-reindexing-invariance`".

This theorem supplies the **second** of those two lemmas outright, at the frozen
scheduled depth `B(n) = IterationAssembly.depthB n` read through the banked
`DirectOutputLower.xOut` and at the frozen column density `3/5`: whatever
`lem:full-cube-seed` delivers on `F_{B(n)}` at that depth is delivered on
`R_0 = Can(F_{B(n)})`.  It is the conclusion
`ITERATED-CANONICAL-CHAINING-001` GAP-EXPOSED 1 records its Part 7 as **not**
delivering.

**The `lem:full-cube-seed` factor stays a hypothesis** (GAP-EXPOSED 3): the seed's
complexity and robustness displays are banked only at requested depth `b = 0`, not
at the scheduled depth `B(n)`; and `D_0` is a binder, because the budget identity
of frozen line 370 is that row's GAP-EXPOSED 5 and is not claimed here.

General in the source size and the public scale.  Claims no reader item. -/
theorem paperSeed_certificate_at_scheduled_depth (n D0 : ℕ)
    (hseed : D0 ≤ LambdaGE (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n))
      1 (DirectOutputLower.xOut (IterationAssembly.depthB n)) ((3 : ℝ) / 5)) :
    D0 ≤ LambdaGE (paperSeedReindexed n) 1
      (DirectOutputLower.xOut (IterationAssembly.depthB n)) ((3 : ℝ) / 5) := by
  rw [paperSeed_lambda n 1 (DirectOutputLower.xOut (IterationAssembly.depthB n))
    ((3 : ℝ) / 5)]
  exact hseed

/-- **The paper's application point is nondegenerate** (LANE-GATE 3).

Two things are checked at the paper's own parameters `p = 1`,
`x = 2^{-B(n)} <= 1`, `z = 3/5 <= 1`.  First, both bracket families of
`paperSeed_bracket_complexity` are **inhabited** there, so neither `Dfamily` is the
`sInf` of an empty set and the transported equality is a statement about genuine
minima.  Second, the carriers are not points: the banked
`IteratedCanonicalChaining.paperSeedReindexed_nondegenerate` -- itself the banked
`FixedLevelCarriers.aSeed_spec` of frozen `12:16--21` -- gives
`q_seed >= 64(B(n)+1)`, so both `2^{q_seed}` and `q_seed` exceed one and the
relabelling being transported is not the trivial one on a one-element carrier.

The row density bound `xOut (B n) <= 1` is derived inline below from
`xOut b = (2^b)⁻¹`.  **Record note (cc-t3x verify):** the banked
`DirectOutputLower.xOut_le_one` (`DirectOutputLower.lean:362`) *is* available and
is the pin used elsewhere in the route (`DirectOutputLower.lean:1029`,
`EntryAssembly.lean:421,536,579,616`); an earlier draft of this docstring claimed
otherwise, which was false.  The two inline re-derivations here and in
`chain_certificate_saturation` are therefore redundant rather than necessary.
Replacing them with the banked pin is a **proof** edit and is deferred to a
follow-up tranche, not made under the verify seat's record-only boundary.  No
numeral is assigned to `B(n)`, which stays the banked
`IterationAssembly.depthB`.

General in the source size.  Claims no reader item. -/
theorem paperSeed_bracket_nonempty (n : ℕ) :
    (bracketGE (Fin (2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n)))
        (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n))) 1
        (DirectOutputLower.xOut (IterationAssembly.depthB n)) ((3 : ℝ) / 5)).Nonempty ∧
      (bracketGE (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n)) → Bool)
        (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n))) 1
        (DirectOutputLower.xOut (IterationAssembly.depthB n)) ((3 : ℝ) / 5)).Nonempty ∧
      1 < 2 ^ FixedLevelCarriers.qSeed (IterationAssembly.depthB n) ∧
      1 < FixedLevelCarriers.qSeed (IterationAssembly.depthB n) := by
  have hx : DirectOutputLower.xOut (IterationAssembly.depthB n) ≤ 1 := by
    rw [DirectOutputLower.xOut]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (IterationAssembly.depthB n) :=
      one_le_pow₀ (by norm_num)
    have h0 : (0 : ℝ) < (2 : ℝ) ^ (IterationAssembly.depthB n) := by positivity
    rw [inv_le_one_iff₀]
    exact Or.inr h1
  have hz : ((3 : ℝ) / 5) ≤ 1 := by norm_num
  obtain ⟨-, hq2, hq1⟩ := paperSeedReindexed_nondegenerate n
  exact ⟨⟨_, bracketGE_univ_mem 1 hx hz⟩, ⟨_, bracketGE_univ_mem 1 hx hz⟩, hq1, hq2⟩

/-! ## Part 8: the certificate transport fires, with every hypothesis discharged

Parts 6 and 7 transport a certificate that some *other* obligation must produce:
on the chain it is clause C3 (`ONELEVEL-001`), and at the scheduled depth `B(n)`
it is `lem:full-cube-seed` (GAP-EXPOSED 3).  A transport theorem whose antecedent
were nowhere available would be untested, so this part runs the whole three-conjunct
transport at the **one** point of the route where a `def:robust-seed` certificate
is already banked outright: the depth-zero full-cube inhabitant
`OneLevelCompletion.fullCubeSeed_realizes_noReading`.

Nothing here is a numeral of this module's choosing.  The width `126`, the scale
`8` and the depth `0` are the banked inhabitant's own values, and `qSeed_zero`
proves that the width is exactly the paper's own evaluated seed width
`q_seed(0) = 2^{a_seed(0)} - 2` of frozen `12:16--21`, computed through the banked
least-integer accessor `FixedLevelCarriers.aSeed`. -/

/-- **The paper's seed width at requested depth zero, evaluated** --
`12-iteration-specification.tex:16--21`, "Let `a_seed >= 3` be the least integer
for which `q_seed = 2^{a_seed} - 2 >= 64(b+1)`".

The value is **evaluated through the banked least-integer accessor**
`FixedLevelCarriers.aSeed`, not assigned: at `b = 0` the rule selects
`a_seed = 7` (since `2^3-2 = 6`, `2^4-2 = 14`, `2^5-2 = 30` and `2^6-2 = 62` all
fall short of `64(0+1) = 64`, while `2^7-2 = 126` clears it), whence
`q_seed = 126`, which is the width the banked depth-zero inhabitant of Part 8
carries.  Recorded so that the `126` appearing below is visibly a schedule value
and not a numeral of this module (`M3`).

**Scope.**  Frozen line **16** opens "Fix a requested depth `b >= 1`", so the
frozen display does not itself range over `b = 0`.  What is evaluated here is the
banked *total* accessor `FixedLevelCarriers.aSeed` at `0`, which is the value the
banked depth-zero inhabitant already carries -- not an extension of the frozen
minimality rule to a depth the paper excludes.  The same boundary is stated at
`fullCubeSeed_noReading_transported` below, which is an instance of
`def:robust-seed` (no lower bound on `b`) and explicitly **not** of
`lem:full-cube-seed`.

Claims no reader item. -/
theorem qSeed_zero : FixedLevelCarriers.qSeed 0 = 126 := by
  have h : FixedLevelCarriers.aSeed 0 = 7 := by
    rw [FixedLevelCarriers.aSeed, Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro m hm
    interval_cases m <;> norm_num
  rw [FixedLevelCarriers.qSeed, h]
  norm_num

/-- **The frozen lexicographic order on the depth-zero seed row carrier.**

`12-iteration-specification.tex:96--97`: "finite function spaces use lexicographic
order in increasing coordinate order".  This is the same construction as the
banked `IteratedCanonicalChaining.seedRowOrder`, at the *literal* carrier
`{0,1}^126` that the banked depth-zero inhabitant lives on; it is supplied
explicitly at the one use site below rather than registered as an instance, so
that no instance ambiguity with `seedRowOrder` can arise.  Scaffolding: not
exported as an instance.  Claims no reader item. -/
@[reducible] noncomputable def fullCubeSeedRowOrder :
    LinearOrder (Fin 126 → Bool) :=
  (inferInstance : LinearOrder (Lex (Fin 126 → Bool)))

/-- **The certificate transport fires at the banked depth-zero inhabitant, with
every hypothesis discharged** (LANE-GATE 3).

`OneLevelCompletion.fullCubeSeed_realizes_noReading` is the route's banked
inhabitant of `SeedInterface.noReading` -- i.e. of `def:robust-seed`
(`03-preliminaries.tex:243--251`), which imposes no lower bound on the depth -- at
`noComplexity = 8`, depth `0`, on the frozen full-cube matrix of width `126`.
Applying `reindex_noReading` to it produces the same three-conjunct certificate on
`Can_{2^126,126}(F_0)`, the canonical reindexing of that matrix along the frozen
increasing equivalences with the frozen lexicographic row order.

So the antecedent of the transport is not hypothetical: at the one point of the
route where a `def:robust-seed` certificate is banked outright, the exact
complexity, the depth-`b` three-rung bound and the `comp >= 1` clause all survive
the canonical reindexing simultaneously, at a nondegenerate scale (`8 >= 3`, the
frozen entry floor) on a `2^126`-row carrier.

**Scope.**  This is an instance of the autoformalization `def:robust-seed`, **not**
of `lem:full-cube-seed`, whose minimality rule is stated for requested depth
`b >= 1` -- exactly the boundary `OneLevelCompletion` records for the inhabitant it
consumes.  It therefore does **not** discharge GAP-EXPOSED 3, which is about the
*scheduled* depth `B(n)`.

Claims no reader item. -/
theorem fullCubeSeed_noReading_transported :
    (OneLevelCompletion.SeedInterface.mk
      (@Can (Fin 126 → Bool) (Fin 126) Bool _ fullCubeSeedRowOrder _ _ (2 ^ 126) 126
        (by simp) (by simp) (OneLevelCompletion.fullCube 126)) 8 8 0).noReading := by
  obtain ⟨S, htable, hdepth, hno, hyes, hread, -, -, -⟩ :=
    OneLevelCompletion.fullCubeSeed_realizes_noReading
  have hS : S
      = OneLevelCompletion.SeedInterface.mk (OneLevelCompletion.fullCube 126) 8 8 0 := by
    cases S
    simp_all
  rw [hS] at hread
  exact reindex_noReading _ _ _ 8 8 0 hread

end EthInapproximability.ParameterizedNP.CanonicalBracketInvariance
