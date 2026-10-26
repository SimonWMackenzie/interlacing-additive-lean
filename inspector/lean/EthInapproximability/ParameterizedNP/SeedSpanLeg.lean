import EthInapproximability.ParameterizedNP.SeedAnchoredFold

/-!
# Parameterized NP route: the span leg of `lem:full-cube-seed`

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`SEED-SPAN-LEG-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened in the
same change as this module to discharge the one leg
`SEED-ANCHORED-FOLD-001` left standing: the row-density span argument of the
frozen proof of `lem:full-cube-seed`, frozen `12:55--60` together with the
one-output-indicator identification `12:69--70`, at every requested depth
`b >= 1`.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

**No route-completion claim is made or implied.**  The construction layer
(`STAGE1-001 .. WRAP-001`) and the machine layer (`MATERIALIZE-001`) are
unlanded, and `ITER-001`'s canonical inhabitation of the fold stays REGISTERED AS
DEFERRED.  What this module does is strictly local: it removes one named
hypothesis from three banked conditionals.

## What lands, and what it does to the standing conditional statuses

The banked `SeedAnchoredFold` reduced the second display of `lem:full-cube-seed`
to a single named hypothesis `hrank`, the frozen sentence "the restricted matrix
has rank at least `|J| - b`", and recorded it as `GAP-EXPOSED 1` of both
`SEED-ANCHORED-FOLD-001` and `CERTIFICATE-CARRYING-FOLD-001`.  Here that
hypothesis is **proved**, from the frozen span argument, at every requested depth
and every retained pair.  Consequently:

* `seedMatrix_lambda` is the second display of `lem:full-cube-seed`,
  `Lambda_3(F_b,1,2^{-b},3/5) >= a_seed + 1` (frozen `12:38--41`),
  **unconditional at every `b >= 1`**;
* `seedMatrix_certifiedAt` is the frozen `NO`-side pair of `12:34--41`,
  unconditional;
* `paperSeed_certifiedAt_unconditional` carries it to `R_0 = Can(F_{B(n)})`
  (frozen `12:363`, `12:374--379`) at the scheduled depth, so
  `CERTIFICATE-CARRYING-FOLD-001`'s `paperSeed_certifiedAt` is no longer
  conditional at the paper's own application site, and
  `SEED-ANCHORED-FOLD-001` `GAP-EXPOSED 1` and
  `CERTIFICATE-CARRYING-FOLD-001` `GAP-EXPOSED 1` are **retired**;
* the base slot the seed-anchored fold reads, `def:robust-seed` at the paper's
  own `R_0` and scheduled depth, is delivered unconditionally by
  `paperSeed_noReading`.

`SEED-001`'s "still pending" sentence is thereby reduced to its remaining two
items only -- the `O(b+1)` side-length claim (frozen `12:42`, proof `12:77--81`)
and `def:reduced-protocol` itself -- neither of which is claimed here.

**`CANONICAL-BRACKET-INVARIANCE-001` `GAP-EXPOSED 3`, exactly one of whose two
halves moves.**  That item records (i) that the `lem:full-cube-seed` factor of
frozen line 379 is an explicit named hypothesis of
`paperSeed_certificate_at_scheduled_depth`, "banked only at requested depth
`b = 0` and not at the scheduled depth `B(n)`", and (ii) that `D_0` is a binder
there.  Half (i) is **retired**: `seedMatrix_certifiedAt` supplies that factor at
every `b >= 1`, in particular at `B(n)`.  Half (ii) is untouched -- the budget
identity of frozen line 370 belongs to `ITERATED-CANONICAL-CHAINING-001`
`GAP-EXPOSED 5` and was pinned by
`SeedAnchoredFold.seedState_budgets_are_seed_complexity`, not here.

## Provenance

* **Autoformalization anchors (proof source).**
  `sections/12-iteration-specification.tex`
  (SHA-256 `a846bfced8bfab2df70b16b46eba8ebe244a0d2ec89b03fc7a00b2a8007160ac`):
  * The frozen span leg, lines **55--60**: "Now retain any row set `A` of density
    at least `2^{-b}`.  It contains at least `2^{q_seed - b}` Boolean vectors, so
    its real linear span has dimension at least `q_seed - b`: a `d`-dimensional
    subspace of `R^{q_seed}` contains at most `2^d` Boolean vectors.  After also
    retaining a column set `J`, the restricted matrix has rank at least
    `|J| - b`."  The parenthetical counting principle -- **a `d`-dimensional
    subspace of `R^{q}` contains at most `2^d` Boolean vectors** -- is the frozen
    proof's own justification and is landed here as
    `card_boolVec_le_two_pow_finrank`; the two conclusions of the leg are
    `fullCube_rankFloor`.
  * Lines **69--70**, "The one-output indicator of the retained matrix is the
    same zero--one matrix viewed over `R`, so its rank is at least `|J| - b`":
    the identification the leg is consumed through.  It is landed as
    `subgame_indR_eq_boolVec`, an entrywise equality, not assumed.
  * The minimality rule `16--21` and the matrix `eq:full-cube-seed`
    (label 29, display 23--30), consumed through the banked
    `FixedLevelCarriers.aSeed`, `.qSeed`, `.seedMatrix`.
  * `lem:full-cube-seed` (label 32) with its second display at **38--41**, and
    the application site `360--379` (the schedule `b_i = B(n) = E_2(n)` at
    360--361, `R_0 = Can(F_{B(n)})` at 363, `D_0 = Y_0 = comp F_{B(n)}` at 370,
    the seed conditions display at 374--378).
* `sections/03-preliminaries.tex`: the **Section-03 rank toolkit** --
  `1_{M=beta}` (lines 63--64), `cor:fixed-output-rank` (label line 67, statement
  66--74) and `lem:fixed-output-leaves` (label 46), all consumed through the
  banked `OneLevelCompletion.indR` / `.fixedOutputRank` and never restated;
  `def:bracket`'s **row clause** (lines 170--172, "retain at least `ceil(m x)`
  rows in every outer block"), which is the frozen "density at least `2^{-b}`"
  hypothesis of `12:55` and is read here through the vendored
  `NPCC.IsEquipartitionedGE`; `def:lambda` (label 224, display 226--231) and the
  column density `y = 3/5` (215--220).
* `sections/02-mechanical-contract.tex`: `conv:finite-slots` (lines 14--18) and
  the mechanical rules (`M\arabic*` enumerate opens at line 74), in particular
  **M3** (lines 85--88, derived quantities are recomputed -- no numeral is
  assigned to `a_seed` or `q_seed` anywhere below) and **M5** (lines 95--99, the
  least-solution search licence the reified accessors rely on).

* **Reader counterpart.**  `sections/05-iteration.tex`
  `lem:paper-full-cube-seed` (label line 27, statement lines 28--44) is
  **`SEED-001`'s reader item**, and the crosswalk records that no declaration of
  any row has claimed a line of it.  Exactly **one** line is claimed here, by
  exactly one declaration: **line 41**, `Lambda_{F_b}(1,2^{-b},3/5) >= a + 1`, to
  `seedMatrix_lambda`, which states that inequality and nothing else.  Reader
  line 39 (`CC(F_b) = a + 1`) and line 43 (`z(F_b) = q = O(b+1)`) are **not**
  claimed: the first is the display the banked `SeedAnchoredFold.seedMatrix_D`
  already proves without claiming a reader item, the second is not proved
  anywhere in this route.  Every other declaration in this module claims no
  reader item.

* **Banked declarations consumed by pin, never restated.**
  * `SeedAnchoredFold.seedMatrix_lambda_of_rankFloor`,
    `.seedMatrix_certifiedAt_of_rankFloor`, `.paperSeed_certifiedAt_of_rankFloor`,
    `.seedMatrix_D`, `.seedDepthStream`, `.seedDepthStream_ge`,
    `.seedAnchoredNoFold`, `.seedMatrix_certifiedAt_saturates`,
    `.seedBracket_nonempty`.
  * `CertificateCarryingFold.CertifiedAt`, `.LevelCertified`,
    `.OutputCertified`.
  * `OneLevelCompletion.indR`, `.fullCube`, `.fin1_fun_ext`.
  * `FixedLevelCarriers.aSeed`, `.qSeed`, `.seedMatrix`, `.aSeed_spec`;
    `IterationAssembly.depthB`, `.depthB_ge`;
    `IteratedCanonicalChaining.CanonicalChain`, `.paperSeedReindexed`;
    `DirectOutputLower.xOut`; and `NPCC.bracketGE` / `.IsEquipartitionedGE` /
    `.Dfamily` / `.subgame` / `.LambdaGE` with
    `Workspace.Types.Interlace.interlaceFun` through `LegacyNPCC.Core`.
  * External Mathlib adapters, all pinned at Mathlib `v4.30.0`:
    `exists_linearIndependent'`, `LinearIndependent.fintype_card_le_finrank`,
    `Module.finrank_linearMap_self`, `Matrix.rank_transpose`,
    `Matrix.rank_eq_finrank_span_cols`, `Finset.card_le_card_of_injOn`,
    `Finset.card_image_of_injOn`, `Finset.card_compl`.  No project axiom is
    introduced and `LegacyNPCC.Stage12` is **not** imported, so the AGHP
    balanced-family axiom stays outside this module's closure.

## Non-vacuity, hypothesis consistency, and the statement poles

* **Canonical inhabitation.**  `card_boolVec_le_two_pow_finrank` and
  `fullCube_rankFloor` are theorems about arbitrary retained pairs, not new
  types, so the inhabitation question is asked of their consumers.  The
  consumers' instance is the **paper's own**: `paperSeed_certifiedAt_unconditional`
  is read at the seed the application site constructs, `R_0 = Can(F_{B(n)})` at
  the scheduled depth `B(n) = E_2(n)`, whose legality (`b >= 1`, frozen `12:16`)
  is the banked `IterationAssembly.depthB_ge`, not an assumption.  The one type
  this module introduces, `boolVec`, is a coercion and is scaffolding; its
  docstring says so.
* **The premise family is never empty.**  `SeedAnchoredFold.seedBracket_nonempty`
  is consumed by pin: the bracket family the rank floor quantifies over is
  nonempty at all three frozen rungs and at every requested depth, so
  `fullCube_rankFloor` is not a statement about an empty family, and the
  `Dfamily` infimum it feeds is a genuine minimum rather than the `Nat.sInf`
  default `0`.
* **Hypothesis consistency.**  `fullCube_rankFloor` takes exactly one
  hypothesis, bracket membership, and that hypothesis is inhabited (previous
  item), so no `False` derives from it.  The unconditional
  `seedMatrix_lambda` inherits the consistency check already landed as
  `SeedAnchoredFold.seedMatrix_certifiedAt_saturates`: the two displays of
  `lem:full-cube-seed` force `Lambda_3 = a_seed + 1` **exactly**, which is
  re-run here without hypotheses as `seedMatrix_lambda_eq`.  A statement whose
  two halves pin one integer cannot be an over-demand.
* **Statement pole for `fullCube_rankFloor`.**  The conclusion is a lower bound
  on a rank, so the trivial-witness question is whether a weaker floor would do.
  It would not: at `b = 0` the floor is the full `|J|`, which is exactly the
  banked depth-zero statement, and the frozen `- b` slack is *necessary* -- the
  retained row set may be a subcube of codimension `b`, on which the restricted
  matrix genuinely loses `b` dimensions.  Replacing `|J| - b` by `|J|` is
  therefore false at every `b >= 1`, and dropping the row-density hypothesis
  altogether is false at `R = {}` (rank `0`, `|J|` arbitrary).
* **Statement pole for `card_boolVec_le_two_pow_finrank`.**  The bound is tight
  at `V = R^ι`: `2^{card ι}` Boolean vectors lie in it.  A bound of `2^d - 1`, or
  one dropping the hypothesis that the vectors are Boolean, is false (the second
  by scaling a single vector).

## GAP-EXPOSED

1. **The `O(b+1)` side-length sentence of `lem:full-cube-seed` (frozen `12:42`,
   proof `12:77--81`) is still not claimed.**  Nothing here asserts an asymptotic
   side-length bound for the seed; reader line 43 is deliberately unclaimed.
2. **`def:reduced-protocol` (frozen `03:35`) is still replaced**, by the banked
   `OneLevelCompletion.protocol_indR_rank_bound`, exactly as `SEED-001` records.
   This module consumes `cor:fixed-output-rank` through
   `SeedAnchoredFold.fullCube_bracket_ge_of_rankFloor` and changes nothing about
   that substitution.
3. **Canonical inhabitation of the *fold* stays REGISTERED AS DEFERRED**,
   inherited verbatim from `CERTIFICATE-CARRYING-FOLD-001` `GAP-EXPOSED 2` and
   `SEED-ANCHORED-FOLD-001` `GAP-EXPOSED 3`: the paper's own level chain needs
   the unbuilt Stage-1--4 constructor chain.  `paperSeed_noReading` inhabits the
   fold's **base slot** at the paper's seed and says nothing about the chain or
   the step hypothesis; it is not an inhabitation of the fold.
4. **No route completion is claimed** (see the head of this file).
-/

namespace EthInapproximability.ParameterizedNP.SeedSpanLeg

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.IteratedCanonicalChaining
open EthInapproximability.ParameterizedNP.CertificateCarryingFold
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.SeedAnchoredFold

/-! ## Part 1: Boolean vectors over the reals (`12:57--58`)

The frozen span leg is a statement about *Boolean* vectors read over `R`.  This
part reifies that reading and proves the counting principle the frozen proof
states as its own justification. -/

/-- **A zero--one vector read over the reals** -- the reading
`12-iteration-specification.tex:69--70` performs, "the same zero--one matrix
viewed over `R`", one row at a time.

**Scaffolding.**  The frozen paper never names this map; it is the coercion its
sentences take for granted, and it exists here only so that the counting
principle of `12:57--58` can be stated about a `Finset` of Boolean vectors rather
than about an unnamed subset of `R^iota`.  It carries no complexity, robustness or
promise content (`M1`, `M2`).

General in the index carrier.  Claims no reader item. -/
def boolVec {ι : Type*} (f : ι → Bool) : ι → ℝ := fun i => if f i then 1 else 0

/-- **Aux 1 (readout).**  `boolVec` is the entrywise indicator and nothing else.
General in the index carrier.  Claims no reader item. -/
theorem boolVec_apply {ι : Type*} (f : ι → Bool) (i : ι) :
    boolVec f i = if f i then (1 : ℝ) else 0 := rfl

/-- **Aux 2 (the reading loses nothing).**  Distinct Boolean vectors stay
distinct over `R`, so a count of real vectors is a count of Boolean ones.  This
is what lets `12:57--58` be applied to the retained rows rather than to their
images.

General in the index carrier.  Claims no reader item. -/
theorem boolVec_injective {ι : Type*} : Function.Injective (boolVec (ι := ι)) := by
  intro f g h
  funext i
  have hi : (if f i then (1 : ℝ) else 0) = (if g i then (1 : ℝ) else 0) := congrFun h i
  cases hf : f i <;> cases hg : g i <;> simp_all

set_option linter.unusedFintypeInType false in
/-- **The counting principle of the frozen span leg** --
`12-iteration-specification.tex:57--58`, "a `d`-dimensional subspace of
`R^{q_seed}` contains at most `2^d` Boolean vectors".

Stated in the frozen direction and at an arbitrary finite index carrier: any
`Finset` of Boolean vectors whose real readings all lie in a subspace `V` has at
most `2^{dim V}` members.

The proof is the standard coordinate-selection argument, run with the Mathlib
adapters pinned in the header: the coordinate functionals `v |-> v i` restricted
to `V` are thinned to a linearly independent subfamily indexed by a set of
coordinates `a(kappa)` spanning the same subspace of the dual, so every
coordinate functional is a combination of those; two Boolean vectors in `V` that
agree on `a(kappa)` therefore agree everywhere, and `card kappa <= dim V` because
`V` and its dual have the same dimension.

The bound is attained at `V = R^iota`, so nothing stronger is provable
(statement pole).

General in the index carrier, the subspace and the vector set.  Claims no reader
item. -/
theorem card_boolVec_le_two_pow_finrank {ι : Type*} [Fintype ι]
    (V : Submodule ℝ (ι → ℝ)) (T : Finset (ι → Bool))
    (hT : ∀ f ∈ T, boolVec f ∈ V) :
    T.card ≤ 2 ^ Module.finrank ℝ V := by
  classical
  set L : ι → (V →ₗ[ℝ] ℝ) := fun i => (LinearMap.proj i).comp V.subtype with hLdef
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ L
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ ≤ Module.finrank ℝ V := by
    have h := hli.fintype_card_le_finrank
    rwa [Module.finrank_linearMap_self] at h
  have hkey : ∀ f ∈ T, ∀ g ∈ T,
      (fun k : κ => f (a k)) = (fun k : κ => g (a k)) → f = g := by
    intro f hf g hg hfg
    have hv : boolVec f - boolVec g ∈ V := V.sub_mem (hT f hf) (hT g hg)
    set vv : V := ⟨boolVec f - boolVec g, hv⟩ with hvv
    set ev : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun ℓ => ℓ vv
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } with hev
    have hzero : ∀ k : κ, (L (a k)) vv = 0 := by
      intro k
      have hk : f (a k) = g (a k) := congrFun hfg k
      simp [hLdef, hvv, boolVec, hk]
    have hker : Submodule.span ℝ (Set.range (L ∘ a)) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simpa [hev, LinearMap.mem_ker] using hzero k
    have hall : ∀ i : ι, (L i) vv = 0 := by
      intro i
      have hmem : L i ∈ Submodule.span ℝ (Set.range (L ∘ a)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      simpa [hev, LinearMap.mem_ker] using hker hmem
    have hsub : boolVec f - boolVec g = 0 := by
      funext i
      simpa [hLdef, hvv] using hall i
    exact boolVec_injective (sub_eq_zero.mp hsub)
  calc T.card ≤ (Finset.univ : Finset (κ → Bool)).card :=
        Finset.card_le_card_of_injOn (fun f k => f (a k))
          (fun _ _ => Finset.mem_univ _)
          (fun f hf g hg h => hkey f hf g hg h)
    _ = 2 ^ Fintype.card κ := by
        simp [Finset.card_univ]
    _ ≤ 2 ^ Module.finrank ℝ V := Nat.pow_le_pow_right (by norm_num) hcard

set_option linter.unusedFintypeInType false in
/-- **Aux 3 (unit test at the trivial subspace).**

The counting principle read at `V = 0`: at most **one** Boolean vector has zero
real reading.  This is a general property of the encoding, not of the seed, and
it is the test that fixes `boolVec`: a reading that collapsed `true` and `false`
to the same real -- or that returned a constant -- would satisfy the frozen
sentence's *shape* while making this false as soon as `iota` is nonempty and `T`
has two members.

General in the index carrier and the vector set.  Claims no reader item. -/
theorem card_boolVec_eq_zero_le_one {ι : Type*} [Fintype ι] (T : Finset (ι → Bool))
    (hT : ∀ f ∈ T, boolVec f = 0) : T.card ≤ 1 := by
  have h := card_boolVec_le_two_pow_finrank (⊥ : Submodule ℝ (ι → ℝ)) T
    (fun f hf => by rw [hT f hf]; exact Submodule.zero_mem _)
  rw [finrank_bot] at h
  simpa using h

/-! ## Part 2: the span leg itself (`12:55--60` with `12:69--70`)

The frozen leg is stated about the retained matrix of a bracket member.  Both
frozen fragments are landed: the entrywise identification `12:69--70`, and the
rank floor `|J| - b` of `12:55--60`. -/

/-- **The one-output indicator of a retained full-cube matrix, entry by entry** --
`12-iteration-specification.tex:69--70`, "The one-output indicator of the
retained matrix is the same zero--one matrix viewed over `R`".

At `beta = 1` the identification is the identity on entries, and the frozen
sentence is exactly that: each row of `1_{M=1}` is the real reading of the
Boolean row `j |-> gamma(j)` restricted to the retained columns.  It is landed
rather than folded in silently, because it is the fragment the rank floor is
consumed through.

General in the width, the retained row and column sets, and the retained row.
Claims no reader item. -/
theorem subgame_indR_eq_boolVec {q : ℕ} (R : Finset (Fin 1 × (Fin q → Bool)))
    (C : Finset (Fin 1 → Fin q)) (x : {x // x ∈ R}) :
    indR (subgame (interlaceFun (fullCube q) 1) R C) true x
      = boolVec (fun c : {c // c ∈ C} => x.val.2 (c.val 0)) := by
  funext c
  have hx : x.val.1 = 0 := Subsingleton.elim _ _
  simp [indR, subgame, interlaceFun, fullCube, hx, boolVec]

/-- **The frozen span leg** --
`12-iteration-specification.tex:55--60`, "Now retain any row set `A` of density
at least `2^{-b}`.  It contains at least `2^{q_seed - b}` Boolean vectors, so its
real linear span has dimension at least `q_seed - b` ... After also retaining a
column set `J`, the restricted matrix has rank at least `|J| - b`", read through
the identification `12:69--70` and written without a truncated subtraction.

This is the hypothesis `hrank` of `SeedAnchoredFold.fullCube_bracket_ge_of_rankFloor`,
`GAP-EXPOSED 1` of `SEED-ANCHORED-FOLD-001`, now proved.

**The frozen argument, in the frozen order.**  The row clause of `def:bracket`
(`03-preliminaries.tex:170--172`) at `p = 1` gives `2^q x_out(b) <= |R|`, i.e.
`2^q <= 2^b |R|` -- the frozen "density at least `2^{-b}`", read through the
vendored `NPCC.IsEquipartitionedGE` over the single outer block.  Each retained
row restricts to a Boolean vector on the retained columns, and rows sharing one
restriction are determined by their values off those `|J|` coordinates, of which
there are `q - |J|`; so `|R| <= (number of distinct restrictions) * 2^{q - |J|}`.
The distinct restrictions are Boolean vectors lying in the real row span of the
retained matrix, whose dimension is the matrix's rank, so
`card_boolVec_le_two_pow_finrank` bounds their number by `2^{rank}`.  Chaining,
`2^q <= 2^{b + rank + q - |J|}`, and `|J| <= q` gives the frozen floor.

The column density `y` is a binder and plays no role: the frozen leg uses only
the *row* clause, which is why it holds at all three rungs of `def:lambda` at
once.

General in the width, the requested depth, the column density and the retained
pair.  Claims no reader item. -/
theorem fullCube_rankFloor (q b : ℕ) (y : ℝ)
    (RC : Finset (Fin 1 × (Fin q → Bool)) × Finset (Fin 1 → Fin q))
    (hRC : RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut b) y) :
    (RC.2).card
      ≤ b + (indR (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2) true).rank := by
  classical
  obtain ⟨R, C⟩ := RC
  obtain ⟨hrow, -⟩ := hRC
  simp only at hrow ⊢
  set A : Matrix {a // a ∈ R} {c // c ∈ C} ℝ :=
    indR (subgame (interlaceFun (fullCube q) 1) R C) true with hA
  -- The frozen row density, `12:55`: `2^q <= 2^b |R|`.
  have hfil : R.filter (fun p => p.1 = 0) = R :=
    Finset.filter_true_of_mem (fun x _ => Subsingleton.elim _ _)
  have hrow0 : ⌈(Fintype.card (Fin q → Bool) : ℝ) * xOut b⌉₊ ≤ R.card := by
    have h := hrow 0 (Finset.mem_univ 0)
    rwa [hfil] at h
  have hcardX : Fintype.card (Fin q → Bool) = 2 ^ q := by simp
  have hdensity : (2 : ℕ) ^ q ≤ 2 ^ b * R.card := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
    have hceil : ((Fintype.card (Fin q → Bool) : ℝ) * xOut b) ≤ (R.card : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast hrow0
    have hceil2 : ((2 : ℝ) ^ q) * ((2 : ℝ) ^ b)⁻¹ ≤ (R.card : ℝ) := by
      rw [hcardX, xOut] at hceil
      push_cast at hceil
      exact hceil
    have h2 : ((2 : ℝ) ^ q) ≤ (2 : ℝ) ^ b * (R.card : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hceil2 (le_of_lt hpos)
      calc ((2 : ℝ) ^ q) = (2 : ℝ) ^ b * (((2 : ℝ) ^ q) * ((2 : ℝ) ^ b)⁻¹) := by
            field_simp
        _ ≤ (2 : ℝ) ^ b * (R.card : ℝ) := hmul
    exact_mod_cast h2
  -- The retained coordinates.
  set S : Finset (Fin q) := C.image (fun c => c 0) with hS
  have hSC : S.card = C.card := by
    refine Finset.card_image_of_injOn ?_
    intro c _ c' _ h
    exact fin1_fun_ext h
  have hSle : S.card ≤ q := by simpa using Finset.card_le_univ S
  -- The retained rows, as Boolean vectors.
  set R' : Finset (Fin q → Bool) := R.image Prod.snd with hR'
  have hR'card : R'.card = R.card := by
    refine Finset.card_image_of_injOn ?_
    rintro ⟨x1, x2⟩ _ ⟨z1, z2⟩ _ h
    simp only at h
    subst h
    rw [Subsingleton.elim x1 z1]
  set β : (Fin q → Bool) → ({c // c ∈ C} → Bool) :=
    fun γ c => γ (c.val 0) with hβ
  set Bimg : Finset ({c // c ∈ C} → Bool) := R'.image β with hBimg
  -- Each restriction is a row of the retained matrix, hence lies in its row span.
  have hArow : ∀ f ∈ Bimg, boolVec f ∈ Submodule.span ℝ (Set.range A) := by
    intro f hf
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
    refine Submodule.subset_span ⟨⟨x, hx⟩, ?_⟩
    rw [hA]
    exact subgame_indR_eq_boolVec R C ⟨x, hx⟩
  -- `12:57--58` applied to those restrictions.
  have hrankSpan : Module.finrank ℝ (Submodule.span ℝ (Set.range A)) = A.rank := by
    have hcol : (Matrix.transpose A).col = A := rfl
    have h := Matrix.rank_eq_finrank_span_cols (Matrix.transpose A)
    rw [hcol] at h
    rw [← h, Matrix.rank_transpose]
  have hBcard : Bimg.card ≤ 2 ^ A.rank := by
    have h := card_boolVec_le_two_pow_finrank
      (Submodule.span ℝ (Set.range A)) Bimg hArow
    rwa [hrankSpan] at h
  -- Rows with the same restriction differ only off the retained coordinates.
  have hfibre : R'.card ≤ Bimg.card * 2 ^ (q - S.card) := by
    have hinj : Set.InjOn
        (fun γ : Fin q → Bool => (β γ, fun j : {j // j ∈ Sᶜ} => γ j.val))
        (R' : Set (Fin q → Bool)) := by
      intro γ _ γ' _ h
      have h1 : β γ = β γ' := congrArg Prod.fst h
      have h2 : (fun j : {j // j ∈ Sᶜ} => γ j.val)
          = (fun j : {j // j ∈ Sᶜ} => γ' j.val) := congrArg Prod.snd h
      funext j
      by_cases hj : j ∈ S
      · obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hj
        have := congrFun h1 ⟨c, hc⟩
        simpa [hβ, hcj] using this
      · exact congrFun h2 ⟨j, Finset.mem_compl.mpr hj⟩
    have hmaps : ∀ γ ∈ R', (β γ, fun j : {j // j ∈ Sᶜ} => γ j.val)
        ∈ Bimg ×ˢ (Finset.univ : Finset ({j // j ∈ Sᶜ} → Bool)) := by
      intro γ hγ
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem β hγ, Finset.mem_univ _⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    have hcompl : Fintype.card ({j // j ∈ Sᶜ} → Bool) = 2 ^ (q - S.card) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl,
        Fintype.card_fin]
    have hprod : (Bimg ×ˢ (Finset.univ : Finset ({j // j ∈ Sᶜ} → Bool))).card
        = Bimg.card * 2 ^ (q - S.card) := by
      rw [Finset.card_product, Finset.card_univ, hcompl]
    rw [hprod] at hle
    exact hle
  -- The frozen chain, `12:59--60`.
  have hchain : (2 : ℕ) ^ q ≤ 2 ^ (b + (A.rank + (q - S.card))) := by
    have h1 : (2 : ℕ) ^ b * R.card ≤ 2 ^ b * (2 ^ A.rank * 2 ^ (q - S.card)) := by
      refine Nat.mul_le_mul_left _ ?_
      rw [← hR'card]
      exact le_trans hfibre (Nat.mul_le_mul_right _ hBcard)
    have h2 : (2 : ℕ) ^ b * (2 ^ A.rank * 2 ^ (q - S.card))
        = 2 ^ (b + (A.rank + (q - S.card))) := by
      rw [pow_add, pow_add]
    rw [← h2]
    exact le_trans hdensity h1
  have hexp : q ≤ b + (A.rank + (q - S.card)) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hchain
  omega

/-! ## Part 3: the three banked conditionals at the proved floor

Nothing below adds a hypothesis; each declaration is the banked conditional with
`hrank` supplied by Part 2. -/

/-- **The span leg at the reified seed width** --
`12-iteration-specification.tex:55--60` read at `eq:full-cube-seed`'s own carrier
`F_b` (label 29), i.e. at the banked `FixedLevelCarriers.seedMatrix b`, which is
`OneLevelCompletion.fullCube` at the reified `q_seed` of the minimality rule
`12:16--21`.

No numeral is assigned to `a_seed` or `q_seed` (`M3`): the width is the accessor
itself.

General in the requested depth, the rung index and the retained pair.  Claims no
reader item. -/
theorem seedMatrix_rankFloor (b t : ℕ)
    (RC : Finset (Fin 1 × (Fin (FixedLevelCarriers.qSeed b) → Bool))
      × Finset (Fin 1 → Fin (FixedLevelCarriers.qSeed b)))
    (hRC : RC ∈ bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
      (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t)) :
    (RC.2).card
      ≤ b + (indR (subgame
          (interlaceFun (FixedLevelCarriers.seedMatrix b) 1) RC.1 RC.2) true).rank :=
  fullCube_rankFloor (FixedLevelCarriers.qSeed b) b ((3 : ℝ) / 5 / 2 ^ t) RC hRC

/-- **The second display of `lem:full-cube-seed`, unconditional at every
requested depth `b >= 1`** -- `12-iteration-specification.tex:38--41`,
`Lambda_3(F_b,1,2^{-b},3/5) >= a_seed + 1`.

`SeedAnchoredFold.seedMatrix_lambda_of_rankFloor` consumed by pin with its single
hypothesis discharged by Part 2.  The frozen depth binder `hb : 1 <= b` of
`12:16` is carried, so no consumer can read this outside the range the frozen
subsection ranges over.

**Reader counterpart: `05-iteration.tex:41`**, the second display of
`lem:paper-full-cube-seed`, `Lambda_{F_b}(1,2^{-b},3/5) >= a + 1`.  This is the
only reader line claimed in this module, and it is claimed by this declaration
alone.

General in the requested depth. -/
theorem seedMatrix_lambda (b : ℕ) (hb : 1 ≤ b) :
    FixedLevelCarriers.aSeed b + 1
      ≤ LambdaGE (FixedLevelCarriers.seedMatrix b) 1 (xOut b) ((3 : ℝ) / 5) :=
  seedMatrix_lambda_of_rankFloor b hb (fun t _ RC hRC => seedMatrix_rankFloor b t RC hRC)

/-- **The frozen `NO`-side pair for the seed, unconditional** --
`12-iteration-specification.tex:34--41` read as
`CertificateCarryingFold.CertifiedAt`, at the seed's own evaluated budget
`D_0 = a_seed + 1` (frozen `12:370`).

`SeedAnchoredFold.seedMatrix_certifiedAt_of_rankFloor` consumed by pin.  Claims
no reader item: the two displays are claimed separately, and only the second is
claimed at all (by `seedMatrix_lambda`).

General in the requested depth. -/
theorem seedMatrix_certifiedAt (b : ℕ) (hb : 1 ≤ b) :
    CertifiedAt (FixedLevelCarriers.seedMatrix b) (FixedLevelCarriers.aSeed b + 1) b :=
  seedMatrix_certifiedAt_of_rankFloor b hb
    (fun t _ RC hRC => seedMatrix_rankFloor b t RC hRC)

/-- **Aux 4 (the two displays pin one integer -- hypothesis consistency, now
unconditional).**

`SeedAnchoredFold.seedMatrix_certifiedAt_saturates` consumed by pin at the proved
floor: `Lambda_3(F_b,1,2^{-b},3/5)` is not merely at least `a_seed + 1`, it
*equals* it.  So the pair of displays frozen `12:33--41` states is exactly
saturated and carries no hidden over-demand; a `False` cannot follow from them.

General in the requested depth.  Claims no reader item. -/
theorem seedMatrix_lambda_eq (b : ℕ) (hb : 1 ≤ b) :
    LambdaGE (FixedLevelCarriers.seedMatrix b) 1 (xOut b) ((3 : ℝ) / 5)
      = FixedLevelCarriers.aSeed b + 1 :=
  seedMatrix_certifiedAt_saturates b hb
    (fun t _ RC hRC => seedMatrix_rankFloor b t RC hRC)

/-- **The frozen seed conditions on `R_0 = Can(F_{B(n)})`, unconditional** --
`12-iteration-specification.tex:360--379`, display lines 374--378, at the
schedule `b_i = B(n) = E_2(n)` of lines 360--361 and the evaluated budget
`D_0 = Y_0 = comp F_{B(n)} = a_seed + 1` of line 370.

`SeedAnchoredFold.paperSeed_certifiedAt_of_rankFloor` consumed by pin with its
hypothesis discharged.  This is the **canonical inhabitation point** of Part 3:
the requested depth is not a binder but the paper's own scheduled value, obtained
by evaluating the banked chain `n -> ellN n -> envE 2 n`, and its legality
(`b >= 1`, frozen `12:16`) is `IterationAssembly.depthB_ge`, not an assumption.

General in `n >= 1`.  Claims no reader item. -/
theorem paperSeed_certifiedAt_unconditional (n : ℕ) (hn : 1 ≤ n) :
    CertifiedAt (paperSeedReindexed n)
      (FixedLevelCarriers.aSeed (IterationAssembly.depthB n) + 1)
      (IterationAssembly.depthB n) :=
  paperSeed_certifiedAt_of_rankFloor n hn
    (fun t _ RC hRC => seedMatrix_rankFloor (IterationAssembly.depthB n) t RC hRC)

/-- **Aux 5 (round trip: the paper's `R_0` is a `def:robust-seed` certificate at
the scheduled depth, unconditionally).**

`03-preliminaries.tex:243--251` read through the banked
`CertificateCarryingFold.certifiedAt_noReading_iff`, which is the shape the base
slot of the fold (`SeedAnchoredFold.seedAnchoredNoFold_of_noReading`) consumes.
The `comp >= 1` conjunct that `def:robust-seed` adds to the certified pair is
discharged from the seed's own evaluated budget `a_seed + 1`, not assumed.

Round trip in the strict sense: the certified pair produced by Part 3 is mapped
into the certificate predicate and the banked equivalence maps it back, so no
content is added or lost in the conversion.

**Scope.**  This inhabits the *base slot*.  Canonical inhabitation of the
**fold** stays REGISTERED AS DEFERRED (`GAP-EXPOSED 3`): the chain and the step
hypothesis are untouched.

General in `n >= 1` and the `YES` slot.  Claims no reader item. -/
theorem paperSeed_noReading (n : ℕ) (hn : 1 ≤ n) (y : ℕ) :
    (SeedInterface.mk (paperSeedReindexed n)
      (FixedLevelCarriers.aSeed (IterationAssembly.depthB n) + 1) y
      (IterationAssembly.depthB n)).noReading :=
  (certifiedAt_noReading_iff (paperSeedReindexed n)
      (FixedLevelCarriers.aSeed (IterationAssembly.depthB n) + 1) y
      (IterationAssembly.depthB n)).2
    ⟨paperSeed_certifiedAt_unconditional n hn, Nat.le_add_left 1 _⟩

/-- **Aux 6 (the floor bites: the discharged premise is not vacuously true).**

`SeedAnchoredFold.seedBracket_nonempty` records that the family Part 2 ranges over
is non-empty; this says more, at the vendored family's own witness
`(univ, univ)` (`NPCC.bracketGE.self_mem` lowered by `.anti_mono_params`).  At
that member the retained column set is the whole of `[q_seed]`, so the frozen
floor **forces** a rank of at least `64(b+1) - b`, i.e. at least `64` -- it is a
genuine constraint on the matrix, not a bound satisfiable by the zero rank.  The
width is the reified accessor and the `64(b+1)` is the frozen minimality rule
`12:19--21` consumed through `FixedLevelCarriers.aSeed_spec`; no numeral is
assigned to `q_seed` (`M3`).

Together with Aux 3 this brackets the counting principle from both sides: it
cannot be weakened (Aux 3) and it is not vacuous (here).

General in the requested depth and the rung index.  Claims no reader item. -/
theorem seedRung_floor_bites (b t : ℕ) :
    ((Finset.univ : Finset (Fin 1 × (Fin (FixedLevelCarriers.qSeed b) → Bool))),
        (Finset.univ : Finset (Fin 1 → Fin (FixedLevelCarriers.qSeed b))))
          ∈ bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
              (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t)
      ∧ 64 * (b + 1) - b
          ≤ (indR (subgame (interlaceFun (FixedLevelCarriers.seedMatrix b) 1)
              Finset.univ Finset.univ) true).rank := by
  have hy1 : (3 : ℝ) / 5 / 2 ^ t ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have h0 : (0 : ℝ) < 2 ^ t := by positivity
    rw [div_le_one h0]
    linarith
  have hmem := bracketGE.anti_mono_params
    (X := Fin (FixedLevelCarriers.qSeed b) → Bool) (Y := Fin (FixedLevelCarriers.qSeed b))
    1 (xOut_le_one b) hy1 (bracketGE.self_mem 1)
  refine ⟨hmem, ?_⟩
  have h := seedMatrix_rankFloor b t
    ((Finset.univ : Finset (Fin 1 × (Fin (FixedLevelCarriers.qSeed b) → Bool))),
      (Finset.univ : Finset (Fin 1 → Fin (FixedLevelCarriers.qSeed b)))) hmem
  have hcard : (Finset.univ : Finset (Fin 1 → Fin (FixedLevelCarriers.qSeed b))).card
      = FixedLevelCarriers.qSeed b := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]
  simp only at h
  rw [hcard] at h
  have hq := (FixedLevelCarriers.aSeed_spec b).2
  omega

end EthInapproximability.ParameterizedNP.SeedSpanLeg
