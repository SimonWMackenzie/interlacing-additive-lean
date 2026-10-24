import EthInapproximability.ParameterizedNP.CanonicalBracketInvariance
import EthInapproximability.ParameterizedNP.OneLevelTheorem

/-!
# Parameterized NP route: the certificate-carrying `NO` fold

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`CERTIFICATE-CARRYING-FOLD-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened in the
same change as this module as the **external consumer module** that closes the
two regeneration halves the iteration layer still owed:

* **`ITER-001`'s certificate-carrying `NO` fold.**  `IteratedCanonicalChaining`'s
  `chainNoFold` records two GAP-EXPOSED items -- its GAP-EXPOSED 1, "the
  regenerated depth-`b_j` robustness certificate ... is deliberately absent", and
  its GAP-EXPOSED 4, "the banked difference form, not the frozen
  certificate-guarded clause C3".  Both are removed here: the fold below carries
  the per-level certificate stream through the chain, and its per-level clause is
  the frozen guarded one.
* **`ONELEVEL-001`'s clause-C3 bracket half, transported.**
  `CanonicalBracketInvariance` states its Part 6 scope as "the *transport* of
  frozen lines 345--348 at one successor index.  It is not clause C3
  (`ONELEVEL-001`), and it is not the `k`-level `NO` induction".  Both joins are
  made here, **in actual proof terms**: `clauseC3_transported` composes the banked
  `OneLevelAssembly.oneLevelAssembly_no` with the banked
  `IteratedCanonicalChaining.isCanonicalReindex_complexity` and
  `CanonicalBracketInvariance.isCanonicalReindex_bracket`, and the fold consumes
  `CanonicalBracketInvariance.chain_certificate_transport`,
  `.chain_certificate_saturation` and `.chain_noReading_transport`.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

**No route-completion claim is made or implied.**  The construction layer
(`STAGE1-001 .. WRAP-001`) and the machine layer (`MATERIALIZE-001`) are unlanded,
and the canonical inhabitation of `IteratedCanonicalChaining.CanonicalChain` by the
paper's own chain stays REGISTERED AS DEFERRED; see Part 6.

## Provenance

* **Autoformalization anchors (proof source).**
  `sections/12-iteration-specification.tex`:
  * `thm:fixed-level-gap-size` (label line 192, theorem opener line 191), clause
    **(iv)**, statement lines
    **279--297**.  Its hypotheses are the fixed gap-colouring statement (lines
    279--284) together with the two seed conditions of lines 285--290,
    `comp R_0 = D_0` and `Lambda_3(R_0,1,2^{-b_0},3/5) >= D_0`; its conclusion is
    the display `eq:fixed-level-no-induction` (label line 296, display lines
    291--297), holding "simultaneously for every `0 <= j <= k`" (line 291; line
    290 is the closing bracket of the *hypothesis* display):
    `comp R_j = D_j` at **line 293** and
    `Lambda_3(R_j,1,2^{-b_j},3/5) >= D_j` at **line 295**.
  * The frozen **proof** of that clause, lines 341--350: "For the `NO` induction,
    the fixed gap-colouring statement, the equality `comp R_i = D_i`, and the
    depth-`b_i` certificate together form `NoCert(Public_i)`.  The `NO` clause C3
    gives both the exact equality and the depth-`b_{i+1}` certificate for
    `R_i^+`.  Equations `eq:canonical-complexity-invariance`--%
    `eq:canonical-bracket-invariance` and the canonical chaining equation
    transport both statements to `R_{i+1}`, proving
    `eq:fixed-level-no-induction`.  Thus the two required facts are regenerated
    together at every successor index."  Every declaration of Parts 2 and 3 below
    is one clause of that paragraph, and the closing sentence -- "regenerated
    together" -- is why the fold carries a *pair* and never a complexity alone.
  * Clause **F2** (lines 201--204) and clause **F3** (lines 205--211), which fix
    the level family `0 <= i < k` and the per-level public record carrying
    `D_i, Y_i, b_i, b_{i+1}`, and `eq:iterated-budgets` (label line 239) whose
    `NO` half is `D_{i+1} = D_i + H_i + 1` at content line 238.
  * The `k = 0` reading, lines 320--323: "the family indexed by `0 <= i < k` is
    empty ... All conclusions reduce to their stated hypotheses at `R_0`."
  * The **application site**, lines 360--379: `b_i = B(n) = E_2(n)` for every `i`
    (lines 360--361), `R_0 = Can(F_{B(n)})` (line 363), and the display 374--378
    whose second conclusion `Lambda_3(R_0,1,2^{-B(n)},3/5) >= D_0` is at **line
    377**, justified at line 379 "by
    `lem:full-cube-seed, lem:canonical-reindexing-invariance`".
  * `lem:full-cube-seed` (label line 32, statement lines 33--43), whose two
    displays are `comp F_b = a_seed + 1` (lines 34--36) and
    `Lambda_3(F_b,1,2^{-b},3/5) >= a_seed + 1` (lines 38--41), under the
    subsection's opening "Fix a requested depth `b >= 1`" (line 16), and its proof
    at lines 45--82.  See Part 5 for the GAP-EXPOSED range.
  * `lem:canonical-reindexing-invariance` (label line 140):
    `eq:canonical-complexity-invariance` (label line 144) and
    `eq:canonical-bracket-invariance` (label line 163).  Neither is re-derived
    here; both are consumed by pin.
* `sections/07-one-level-construction.tex`: `thm:one-level` (label line 37),
  clause **C3**, lines **60--67**: "If `NoCert(Public)`, then
  `comp R+ = D + H + 1`, `Lambda_3(R+,1,2^{-b_out},3/5) >= D + H + 1`."  The
  overhead field `H = a + log_2 q_2 + log_2 s + log_2 q + log_2 Q` is line 43.
* `sections/13-iteration-assembly.tex`: `step:I-04`'s depth interface, lines
  **418--428**: "Since `beta_i = beta_{i+1} = B(n)`, the output certificate of
  level `i` has exactly the depth used as the input certificate of level `i+1`.
  No density-monotonicity conversion and no rounding of the exponent occurs at
  this interface."  This is why the fold's depth argument is one banked sequence
  read at `i` and at `i+1`, never two.
* `sections/03-preliminaries.tex`: `def:lambda` (label line 224, display lines
  226--231) and `def:robust-seed` (label line 243, lines 243--251), with the
  column density `3/5` fixed at lines 215--220.
* `sections/02-mechanical-contract.tex`: `conv:finite-slots` (lines 14--18),
  zero-based slots; and the mechanical rules M1--M10, in particular M2/M4 (no
  field beyond the frozen ones), M3 (schedule quantities never numerals) and M9
  (the two widths `q` and `Q` stay distinct).

* **Reader counterpart.**  `routes/parameterized-np/.../reader-facing/sections/05-iteration.tex`,
  `thm:paper-finite-iteration` (label line 120): **line 140**,
  `Lambda_{R_j}(1,2^{-b_j},3/5) >= D_j`, the robustness half of that theorem's
  `NO` line.  That item is the one both `ITER-001` and
  `CANONICAL-BRACKET-INVARIANCE-001` record as deliberately **unclaimed at the
  `k`-level scale** -- `ITER-001` because its fold carries no certificate, and
  `CANONICAL-BRACKET-INVARIANCE-001` because it lands the single-successor
  transport only.  It is claimed here, by `certificateCarryingNoFold` and by no
  other declaration in this module.  Reader lines **123--127** (the two seed
  conditions) are named as a **navigation locus only** and are claimed by nothing
  here.  Every other declaration below claims no reader item.

* **Banked modules consumed by pin, never restated.**
  * `CanonicalBracketInvariance.chain_certificate_transport`,
    `.chain_certificate_saturation`, `.chain_noReading_transport`,
    `.isCanonicalReindex_bracket`, `.paperSeed_certificate_at_scheduled_depth`.
    These are the "designated endpoints"; each occurs in a proof term below.
  * `IteratedCanonicalChaining.CanonicalChain`, `.isCanonicalReindex`,
    `.isCanonicalReindex_complexity`, `.Can`, `.Can_isCanonicalReindex`,
    `.IsCanonicalReindex`, `.chainNoFold`, `.paperSeedReindexed`,
    `.paperSeedReindexed_isCanonical`, `.paperSeedReindexed_nondegenerate`.
  * `OneLevelAssembly.oneLevelAssembly_no` -- clause C3 itself, applied once.
  * `OneLevelCompletion.SeedInterface`, `.noReading`, `.noReading_iff`,
    `.fullCube`, `.fullCubeSeed_D`, `.fullCubeSeed_lambda`, `.levelOutput`,
    `.levelOverhead`, `.alignedMatrix`, `.alignedExact`.
  * `StageThreeExactScale.LambdaGE_le_D` and `DirectOutputLower.xOut`,
    `.xOut_le_one` -- the banked pin, so no `x <= 1` derivation is repeated here.
  * `BudgetThreadWiring.realizedD`, `.realizedBudgets_are_the_banked_ladders`;
    `EffectiveMaterialization.realizedOverhead`; `DepthThread.realizedDepth`;
    `IterationAssembly.budgetD`, `.budgetD_succ`; `PublicRecords.D_const`;
    `FixedLevelCarriers.LevelCarrierSpec`, `.seedMatrix`.
  * `NPCC.LambdaGE`, `NPCC.Dfamily`, `NPCC.bracketGE` and
    `Workspace.Types.Interlace.interlaceFun` through `LegacyNPCC.Core`.

* **Imports.**  `CanonicalBracketInvariance` and `OneLevelTheorem` only.  Those
  two pull in a transitive closure of which the following is a **partial list, not
  the closure** -- it names the modules whose declarations are consumed below, and
  omits further intermediate modules: `IteratedCanonicalChaining`,
  `OneLevelAssembly`, `OneLevelCompletion`, `PublicRecords`, `DirectOutputLower`,
  `StageThreeExactScale`, `EntryGates`, `DepthThread`, `BudgetThreadWiring`,
  `EffectiveMaterialization`, `FixedLevelCarriers`, `IterationAssembly`,
  `SuccessorMajorant` (opened below for `LevelState`, `seedState`),
  `DoubleInterlaceRecurrence` (a direct import of `OneLevelTheorem`),
  `FinalOnlyDuplication` (a direct import of `IteratedCanonicalChaining`), and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  **`LegacyNPCC.Stage12` is not in this module's import
  closure** -- `EthInapproximability.Prelude` imports `LegacyNPCC.Core` and
  `LegacyNPCC.Bridge` only, and no module in the closure imports it -- so the
  cited AGHP balanced-family axiom of `EXPANDER-001` stays outside it and no
  opt-in ledger note is owed.

* **Proof status.**  Every declaration below is new, and none is an inherited
  facade.  The complexity invariance, the bracket invariance, the
  single-successor transport, clause C3 and the two budget ladders are all
  consumed by pin, never re-derived.  **One exemption, stated rather than
  glossed:** `fullCubeSeed_certifiedAt_at_canonical` is, modulo
  `certifiedAt_noReading_iff`, logically the same fact as the banked
  `CanonicalBracketInvariance.fullCubeSeed_noReading_transported` at the
  byte-identical `@Can ... (fullCube 126)` term, reached here by an independent
  route.  The duplication is deliberate: it is what exercises **this module's**
  `certifiedAt_transport` at an instance whose antecedent is banked outright,
  which the banked `reindex_noReading` route cannot do.  It is a firing of this
  module's transport, not a re-proof of the banked endpoint.

## What this module lands

1. **`CertifiedAt`** -- the frozen `NO`-side *pair* as one named predicate:
   `comp M = d` together with `Lambda_3(M,1,2^{-b},3/5) >= d`.  It is exactly the
   conclusion of clause C3 (`07:62--66`), exactly the seed hypothesis of
   `12:286--289`, and exactly one index of `eq:fixed-level-no-induction`.  Five
   general aux lemmas are proved about it (Part 1).
2. **The chain step** (Part 2): the pair moves from `R_i^+` to `R_{i+1}` through
   the banked transport, in the plain form, in the saturated form, and in the
   `def:robust-seed` interface form the next public record reads.
3. **The certificate-carrying `NO` fold** (Part 3): frozen clause (iv) with both
   conclusions, at the frozen ranges, from the frozen guarded per-level clause --
   plus the banked `NO` budget update at a successor (Aux 6), the proof that the
   depth stream is one level-independent slot so the two certificate scopes cannot
   drift (Aux 7), its wiring at the banked budget and depth ladders, and the proof
   that it *entails* the banked difference-form hypothesis of
   `IteratedCanonicalChaining.chainNoFold` and reproduces that theorem's
   conclusion.
4. **Clause C3 transported** (Part 4): `ONELEVEL-001`'s `NO` clause composed with
   the canonical chaining equation, as a free-standing general statement.  This
   is a **proved discharge of the fold's per-level premise at a one-level call
   site**, not a discharge of that premise inside the fold: no declaration below
   instantiates `certificateCarryingNoFold`'s `hstep` with `clauseC3_transported`,
   and in all four fold forms the per-level premise remains an explicit
   hypothesis.  Wiring the two together needs the unbuilt constructor chain that
   connects `C.out i` to `levelOutput N wq b_out delta_U`, which is the deferred
   canonical inhabitation of **GAP-EXPOSED 2** and Part 6.
5. **The seed** (Part 5): the conditional base at the paper's own
   `R_0 = Can(F_{B(n)})`, with `lem:full-cube-seed` at the *scheduled* depth left
   as an explicit named hypothesis -- **GAP-EXPOSED 1** below -- and the banked
   depth-zero inhabitant firing the transport at a nondegenerate scale.
6. **Non-vacuity and hypothesis consistency** (Part 6): the free-stream bundle
   fires at every level count, the strictly stronger ladder-wired bundle fires at
   the frozen `k = 0` reading, and the fold's own output is a saturation at every
   level, so no `False` follows from conjoining the two conclusions of
   `eq:fixed-level-no-induction`.

## GAP-EXPOSED

1. **`lem:full-cube-seed` at the scheduled depth `B(n)`.**  Frozen `12:33--43`
   gives `comp F_b = a_seed + 1` (lines 34--36) and
   `Lambda_3(F_b,1,2^{-b},3/5) >= a_seed + 1` (lines 38--41) for every requested
   depth `b >= 1` (line 16).  In Lean only the **`b = 0`** instance is banked
   (`OneLevelCompletion.fullCubeSeed_D`, `.fullCubeSeed_lambda`, both at
   `xOut 0 = 1`), because the general-`b` proof needs the row-density leg of
   frozen lines 55--64 -- "a `d`-dimensional subspace of `R^{q_seed}` contains at
   most `2^d` Boolean vectors" -- which is not in the route's Lean layer.  The
   **named deferred range is frozen `12:38--41` with its proof leg `12:55--76`, at
   every `b >= 1`, and in particular at `b = B(n)`.**  Accordingly Part 5 lands a
   **conditional** base:
   `paperSeed_certifiedAt` takes the seed's own certified pair as an explicit
   hypothesis and produces it on `R_0`.  Nothing here asserts the antecedent at
   `B(n)`, and `fullCubeSeed_certifiedAt` is explicitly **not** an instance of
   `lem:full-cube-seed` (its `b = 0` lies outside that lemma's frozen range).
2. **Canonical inhabitation of the fold is REGISTERED AS DEFERRED.**  The paper's
   own chain needs the unbuilt Stage-1--4 constructor chain
   (`STAGE1-001 .. WRAP-001`, `MATERIALIZE-001`), exactly as
   `IteratedCanonicalChaining`'s own GAP-EXPOSED 3 records for `CanonicalChain`.
   Part 6 therefore lands a smoke probe explicitly labelled **NON-FIDELITY**; it
   does not discharge the obligation, which is discharged only when the
   construction lands.
3. **The source-side gap-colouring statement is a `Prop` binder.**  Frozen F1
   fixes one source tuple for all levels, so the colouring hypothesis of lines
   279--284 enters the fold as a single level-independent `Prop` with a proof,
   never as a per-level hypothesis and never as a bundle field.  Its
   `def:level-public-input` content belongs to `SOURCE-001` and is not encoded
   here.
4. **The two linear orders on the output carriers are instance arguments**, as in
   `IteratedCanonicalChaining` (its GAP-EXPOSED 2): the frozen recursive order of
   `12:93--98` is not transcribed, and by
   `IteratedCanonicalChaining.Can_complexity_indep_of_order` the complexity half
   of every conclusion below is independent of the choice.
-/

namespace EthInapproximability.ParameterizedNP.CertificateCarryingFold

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.IteratedCanonicalChaining
open EthInapproximability.ParameterizedNP.CanonicalBracketInvariance
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.DirectOutputLower
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.SuccessorMajorant

/-! ## Part 1: the frozen `NO`-side pair, and its general properties

`eq:fixed-level-no-induction` (`12:291--297`), clause C3 (`07:60--67`) and the
seed hypothesis (`12:286--289`) are **the same two-conjunct statement** read at
three different matrices.  It is named once here so that the fold below transports
a single object and so that "regenerated together" (frozen `12:349--350`) is
visible in the type. -/

/-- **The frozen `NO`-side pair at one matrix** --
`12-iteration-specification.tex`, `eq:fixed-level-no-induction` (label line 296)
read at one index:

```
comp M = d,   Lambda_3(M, 1, 2^{-b}, 3/5) >= d.
```

The row density is the banked `DirectOutputLower.xOut` (`x = 2^{-b}`), the copy
count is the frozen `1`, and the column density is the frozen literal `3/5` fixed
at `03-preliminaries.tex:215--220`.  The **one** integer `d` occupies both slots,
which is the frozen "the equality and the robustness lower bound use the same
integer" (`11-one-level-assembly.tex:784`) and is what makes the pair a
regeneration rather than two unrelated bounds.

**Fields, and nothing else** (`M2`/`M4`): this is a `Prop` abbreviation of a
frozen display, not a record.  No budget ladder, no overhead, no carrier, no
promise certificate and no complexity *conclusion* about any other matrix is part
of it; in particular it does **not** restate the derived telescope
`Lambda_3 = d`, which is a theorem (`certifiedAt_saturates`).

General in both carriers, the matrix, the budget and the depth.  Claims no reader
item. -/
def CertifiedAt {A B : Type*} [Fintype A] [Fintype B] (M : A → B → Bool)
    (d b : ℕ) : Prop :=
  D M = d ∧ d ≤ LambdaGE M 1 (xOut b) ((3 : ℝ) / 5)

/-- **Aux 1 (readout).**  The pair read conjunct by conjunct, so consumers never
unfold the definition by hand.  General. -/
theorem certifiedAt_iff {A B : Type*} [Fintype A] [Fintype B] (M : A → B → Bool)
    (d b : ℕ) :
    CertifiedAt M d b ↔ (D M = d ∧ d ≤ LambdaGE M 1 (xOut b) ((3 : ℝ) / 5)) :=
  Iff.rfl

/-- **Aux 2 (the certified budget is unique, at any two depths).**

Identity property: a matrix certifies at most one integer, because the first
conjunct pins it to `comp M`.  This is the formal reason the fold can carry a
*sequence* `D_j` and never a family of unrelated bounds, and it is why the frozen
`eq:iterated-budgets` update `D_{i+1} = D_i + H_i + 1` determines the stream.

General in both carriers, the matrix, the two budgets and the two depths.  Claims
no reader item. -/
theorem certifiedAt_value_unique {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) {d d' b b' : ℕ} (h : CertifiedAt M d b)
    (h' : CertifiedAt M d' b') : d = d' :=
  h.1.symm.trans h'.1

/-- **Aux 3 (the pair saturates: it can never demand more than the frozen text).**

The banked `StageThreeExactScale.LambdaGE_le_D` bounds `Lambda_3` above by the
ambient complexity at every legal density pair, so the two conjuncts force
`Lambda_3(M,1,2^{-b},3/5) = d` exactly.  Hence **no `False` follows from
conjoining the two frozen `NO`-side outputs**, which frozen `12:343--345` states
as the simultaneous output of one certificate rather than as two promise cases.
This is the hypothesis-consistency check for every premise bundle in this module;
`CanonicalBracketInvariance.chain_certificate_saturation` is the same statement at
one chain level and is consumed rather than restated in Part 2.

The row density bound is the banked `DirectOutputLower.xOut_le_one` consumed by
pin -- not an inline re-derivation.  The row-carrier nonemptiness is an explicit
hypothesis here because this lemma is general in the carrier; on a chain it is
derived (see `chainStep_saturation`).

General in both carriers, the matrix, the budget and the depth.  Claims no reader
item. -/
theorem certifiedAt_saturates {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) {d b : ℕ} (hA : 1 ≤ Fintype.card A)
    (h : CertifiedAt M d b) :
    LambdaGE M 1 (xOut b) ((3 : ℝ) / 5) = d := by
  obtain ⟨hD, hL⟩ := h
  have hle := StageThreeExactScale.LambdaGE_le_D M (xOut_le_one b)
    (by norm_num : ((3 : ℝ) / 5) ≤ 1) hA
  omega

/-- **Aux 4 (the pair transports along the canonical reindexing).**

`12-iteration-specification.tex:345--348`, "Equations
`eq:canonical-complexity-invariance`--`eq:canonical-bracket-invariance` and the
canonical chaining equation transport both statements to `R_{i+1}`", stated for a
single matrix and its canonical reindexing.

Both banked halves are consumed by pin in this one proof term and neither is
re-derived: `IteratedCanonicalChaining.isCanonicalReindex_complexity` for the
complexity conjunct and `CanonicalBracketInvariance.isCanonicalReindex_bracket`
for the `Lambda_3` conjunct.  This is the general form of the "bracket-half
transport" that Parts 2 and 4 specialize.

General in both carriers, their orders, the two slot counts, the matrix, the
reindexed matrix, the budget and the depth.  Claims no reader item. -/
theorem certifiedAt_transport {A B : Type*} [Fintype A] [LinearOrder A]
    [Fintype B] [LinearOrder B] {m n : ℕ} {M : A → B → Bool}
    {R : Fin m → Fin n → Bool} {d b : ℕ}
    (h : IsCanonicalReindex M m n R) (hM : CertifiedAt M d b) :
    CertifiedAt R d b := by
  refine ⟨?_, ?_⟩
  · rw [isCanonicalReindex_complexity h]; exact hM.1
  · rw [(isCanonicalReindex_bracket h 1 (xOut b) ((3 : ℝ) / 5)).2]; exact hM.2

/-- **Aux 5 (round trip with the banked interface predicate).**

`def:robust-seed` (`03-preliminaries.tex:243--251`) is the frozen `NO`-side pair
together with `comp R >= 1`; the route's transcription is the banked
`OneLevelCompletion.SeedInterface.noReading`.  This lemma is the exact
correspondence, field by field, through the banked `noReading_iff` consumed by
pin: **no certificate predicate is declared in this module.**

The extra conjunct is `1 <= d` and not something stronger; the frozen entry floor
`3 <= D` of `step:L-03` belongs to clause C3's guard and is not part of
`def:robust-seed`.

General in both carriers, the matrix, the budget, the `YES` slot and the depth.
Claims no reader item. -/
theorem certifiedAt_noReading_iff {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (d y b : ℕ) :
    (SeedInterface.mk M d y b).noReading ↔ (CertifiedAt M d b ∧ 1 ≤ d) := by
  rw [noReading_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩

/-! ## Part 2: the certificate stream on a typed chain (`12:341--350`)

The chain is the banked `IteratedCanonicalChaining.CanonicalChain`, whose three
fields are `eq:iterated-canonical-chaining` (`12:222--230`).  Nothing of that
record is restated; the two names below are the frozen pair read at its two
matrix families. -/

variable {S : FixedLevelCarriers.LevelCarrierSpec}

/-- **The frozen pair at level `j` of the chain** -- `eq:fixed-level-no-induction`
(`12:291--297`) at `R_j`, with the budget stream `D_j` and the depth stream `b_j`
supplied as sequences.

Both streams are arguments, never fields: frozen clause F2 (`12:201--204`)
quantifies `D_i` and `b_i` before either promise condition is imposed, and the
wiring corollary of Part 3 instantiates them at the banked ladders (`M3`).

General in the specification, the chain, the two streams and the level.  Claims no
reader item. -/
def LevelCertified (C : CanonicalChain S) (Dseq bseq : ℕ → ℕ) (j : ℕ) : Prop :=
  CertifiedAt (C.lev j) (Dseq j) (bseq j)

/-- **The frozen pair at the level-`i` output** -- clause C3's two conclusions
(`07-one-level-construction.tex:60--67`) on `R_i^+`, at the successor budget
`D_{i+1}` and the **outgoing** depth `b_{i+1}`.

The depth index is `i+1` and not `i`: frozen C3 concludes at `2^{-b_out}`, and
frozen F3 (`12:205--211`) puts `b_{i+1}` in the level-`i` public record as the
outgoing depth.  `13-iteration-assembly.tex:421--428` is the sentence that makes
this the same integer the next level reads.

General in the specification, the chain, the two streams and the level.  Claims no
reader item. -/
def OutputCertified (C : CanonicalChain S) (Dseq bseq : ℕ → ℕ) (i : ℕ) : Prop :=
  CertifiedAt (C.out i) (Dseq (i + 1)) (bseq (i + 1))

/-- **The single-successor regeneration** -- `12-iteration-specification.tex:345--348`.

The frozen sentence's own content: whatever clause C3 certifies on `R_i^+` is
certified on `R_{i+1}`, at the same integer and the same depth.  The banked
`CanonicalBracketInvariance.chain_certificate_transport` is consumed by pin in
this proof term and nothing it proves is restated -- this declaration exists to
put the transport into the fold's own vocabulary, which is what lets Part 3 be an
induction on the *pair* rather than on the complexity alone.

Statement pole: the trivial reading would transport the complexity conjunct only,
which is the banked `CanonicalChain.chain_complexity` and is already available; the
content here is that the *second* conjunct survives, and it survives because the
bracket families on the two carriers are in cardinality-preserving bijection, not
because `Lambda_3` is monotone in anything.

General in the specification, the chain, the two streams and the level.  Claims no
reader item. -/
theorem chainStep_certificate (C : CanonicalChain S) (Dseq bseq : ℕ → ℕ) (i : ℕ)
    (h : OutputCertified C Dseq bseq i) : LevelCertified C Dseq bseq (i + 1) :=
  chain_certificate_transport C i (bseq (i + 1)) (Dseq (i + 1)) h.1 h.2

/-- **The regeneration is a saturation on both sides of the step.**

`CanonicalBracketInvariance.chain_certificate_saturation` consumed by pin: the
frozen pair forces `Lambda_3 = D_{i+1}` exactly, both on the level output and on
the chained level matrix.  So the step's premise bundle never demands more than
frozen C3 delivers, and the fold of Part 3 cannot be an over-demand at any level.

The row-carrier nonemptiness that `certifiedAt_saturates` takes as a hypothesis is
**derived** inside the banked endpoint, from the chain's own `rowCard` field and
`FixedLevelCarriers.carriers_two_le_succ`; it is not assumed here.

General in the specification, the chain, the two streams and the level.  Claims no
reader item. -/
theorem chainStep_saturation (C : CanonicalChain S) (Dseq bseq : ℕ → ℕ) (i : ℕ)
    (h : OutputCertified C Dseq bseq i) :
    LambdaGE (C.out i) 1 (xOut (bseq (i + 1))) ((3 : ℝ) / 5) = Dseq (i + 1) ∧
      LambdaGE (C.lev (i + 1)) 1 (xOut (bseq (i + 1))) ((3 : ℝ) / 5)
        = Dseq (i + 1) :=
  chain_certificate_saturation C i (bseq (i + 1)) (Dseq (i + 1)) h.1 h.2

/-- **The regeneration in the shape the next public record reads** --
`12-iteration-specification.tex:379--382`, "The construction-specific fields inside
`T_i` are discarded after producing `R_{i+1}`; the next public record carries only
the new matrix, budgets, and depths."

`CanonicalBracketInvariance.chain_noReading_transport` consumed by pin, restated in
this module's vocabulary through `certifiedAt_noReading_iff`.  The `1 <= D_{i+1}`
conjunct of `def:robust-seed` is an explicit hypothesis rather than a derived
fact, because `def:robust-seed` states it separately (`03-preliminaries.tex:244`)
and the frozen entry floor that would imply it lives in clause C3's guard.

General in the specification, the chain, the two streams, the level and the `YES`
slot.  Claims no reader item. -/
theorem chainStep_noReading (C : CanonicalChain S) (Dseq bseq : ℕ → ℕ) (i y : ℕ)
    (hpos : 1 ≤ Dseq (i + 1)) (h : OutputCertified C Dseq bseq i) :
    (SeedInterface.mk (C.lev (i + 1)) (Dseq (i + 1)) y (bseq (i + 1))).noReading :=
  chain_noReading_transport C i (Dseq (i + 1)) y (bseq (i + 1))
    ((certifiedAt_noReading_iff (C.out i) (Dseq (i + 1)) y (bseq (i + 1))).2
      ⟨h, hpos⟩)

/-! ## Part 3: the certificate-carrying `NO` fold (`12:279--297`) -/

/-- **Frozen clause (iv) of `thm:fixed-level-gap-size`, with both conclusions** --
`12-iteration-specification.tex`, statement lines 279--297, proof lines 341--350.

```
comp R_j = D_j,   Lambda_3(R_j, 1, 2^{-b_j}, 3/5) >= D_j      (0 <= j <= k)
```

This is the half `ITER-001` records as owed: `IteratedCanonicalChaining.chainNoFold`
delivers the first conclusion only and states in its own docstring that the second
"is deliberately absent (GAP-EXPOSED 1)" and that its per-level clause is "the
banked difference form, not the frozen certificate-guarded clause C3
(GAP-EXPOSED 4)".  Both are repaired here: the induction carries the pair, and the
per-level hypothesis is the frozen guarded implication.

**The hypotheses are the frozen ones, in the frozen ranges.**

* `hgap` is the fixed gap-colouring statement of lines 279--284.  Frozen F1
  (`12:195--199`) fixes **one** source tuple for the whole family, so it is one
  level-independent `Prop` with one proof and never a per-level hypothesis
  (GAP-EXPOSED 3).
* `hbase` is the pair of seed conditions of lines 285--290, at `R_0`.
* `hstep` is the frozen `NoCert(Public_i) => C3` implication of lines 341--345:
  "the fixed gap-colouring statement, the equality `comp R_i = D_i`, and the
  depth-`b_i` certificate together form `NoCert(Public_i)`.  The `NO` clause C3
  gives both the exact equality and the depth-`b_{i+1}` certificate for `R_i^+`."
  Its range is frozen F3's own `0 <= i < k` (line 205) and **not** a global
  `forall i`: `IteratedCanonicalChaining.chainedFold_hypotheses_consistent`
  records why the bounded range is what makes `k = 0` non-vacuous.
* the chaining enters only through `chainStep_certificate`, i.e. through the
  banked transport.

**Statement pole.**  This is not an existential deliverable, so the pole is the
weakening direction.  Dropping the second conjunct gives exactly the banked
`chainNoFold` -- already available, and provably implied by this theorem
(`certificateFold_reproduces_chainNoFold`), so it is strictly weaker.  Replacing
the depth stream `b_j` by a level-dependent *larger* depth would weaken the
robustness conclusion to a smaller row density and would no longer be re-usable as
the next level's input, which frozen `13:421--428` forbids: "No
density-monotonicity conversion and no rounding of the exponent occurs at this
interface."  And conjoining this clause with clause (iii) would be vacuous, which
`IteratedCanonicalChaining.chainedPromiseCases_exclusive` proves; the two stay
separate implications about the same matrix.

General in the specification, the chain, the two streams, the colouring statement,
the level count and the level.

Reader counterpart: `05-iteration.tex:140`,
`Lambda_{R_j}(1,2^{-b_j},3/5) >= D_j`, the robustness half of the `NO` line of
`thm:paper-finite-iteration` -- the item `ITER-001` and
`CANONICAL-BRACKET-INVARIANCE-001` both left deliberately unclaimed at the
`k`-level scale.  Reader lines 123--127 are a navigation locus only. -/
theorem certificateCarryingNoFold (C : CanonicalChain S) (Dseq bseq : ℕ → ℕ)
    (GapColouring : Prop) (hgap : GapColouring) (k : ℕ)
    (hbase : LevelCertified C Dseq bseq 0)
    (hstep : ∀ i, i < k → GapColouring → LevelCertified C Dseq bseq i →
      OutputCertified C Dseq bseq i)
    (j : ℕ) (hj : j ≤ k) : LevelCertified C Dseq bseq j := by
  revert hj
  induction j with
  | zero => intro _; exact hbase
  | succ t ih =>
    intro ht
    exact chainStep_certificate C Dseq bseq t
      (hstep t (by omega) hgap (ih (by omega)))

/-- **Aux 6 (the banked `NO` budget ladder, read at a successor).**

`eq:iterated-budgets` (`12`, label line 239), `NO` half `D_{i+1} = D_i + H_i + 1`
at content line 238,
read off the realized chain.  The two banked deliverables are consumed by pin --
`BudgetThreadWiring.realizedBudgets_are_the_banked_ladders` and
`IterationAssembly.budgetD_succ` -- so the ladder is *evaluated* here and never
restated, and `H_i` stays the banked
`EffectiveMaterialization.realizedOverhead` (`M3`).

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level.  Claims no reader item. -/
theorem realizedD_succ (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ (i + 1) =
      BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ i
        + EffectiveMaterialization.realizedOverhead S aE q2E sE i + 1 := by
  rw [(BudgetThreadWiring.realizedBudgets_are_the_banked_ladders S aE q2E sE
      auxW invT robD S₀ (i + 1)).2,
    (BudgetThreadWiring.realizedBudgets_are_the_banked_ladders S aE q2E sE
      auxW invT robD S₀ i).2,
    IterationAssembly.budgetD_succ]

/-- **Aux 7 (the fold's depth stream is one level-independent slot).**

`13-iteration-assembly.tex:421--428`: "Since `beta_i = beta_{i+1} = B(n)`, the
output certificate of level `i` has exactly the depth used as the input
certificate of level `i+1`.  No density-monotonicity conversion and no rounding of
the exponent occurs at this interface."

`OutputCertified` certifies at `b_{i+1}` and `LevelCertified` consumes at `b_i`, so
the fold would silently rot if those two slots could drift.  They cannot: the two
banked pins `DepthThread.realizedDepth_succ` and `.realizedDepth_const` are
consumed here and neither is restated.  The identity holds at **every** level and
depends on the base state alone, which is `DepthThread`'s own
`realizedDepth_ignores_every_arrow_datum`.

General in the specification, the three exponent families, the three `AuxOut`
families, the base state and the level.  Claims no reader item -- `05-iteration.tex:272`
is `IterationAssembly.depthB`'s. -/
theorem foldDepthStream_constant (S : FixedLevelCarriers.LevelCarrierSpec)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState) (i : ℕ) :
    DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ i
        = DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ (i + 1) ∧
      DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ i = S₀.depth :=
  ⟨DepthThread.realizedDepth_succ S aE q2E sE auxW invT robD S₀ i,
    DepthThread.realizedDepth_const S aE q2E sE auxW invT robD S₀ i⟩

/-- **The fold at the banked budget and depth ladders.**

Frozen clause (iv) with every schedule quantity supplied by a banked definition
and no numeral anywhere (`M3`): `D_j` is `BudgetThreadWiring.realizedD`, the
frozen public complexity budget of `12:238`, and `b_j` is
`DepthThread.realizedDepth`, the frozen common depth of `14:1649` (= `12:546--548`).
By the banked `DepthThread.realizedDepth_const` the depth stream is **constant and
equal to the base state's own depth slot** at every level, which is exactly the
level-independence `13:421--428` needs at the interface -- so no
density-monotonicity conversion can hide in this instantiation.  **The *value* of
that slot is not pinned here**: `S₀` is a free binder, so nothing in this
declaration identifies `S₀.depth` with `IterationAssembly.depthB n`.  The frozen
`b_i = B(n) = E_2(n)` of lines 360--361 is what a *seed-anchored* base state would
supply, and pinning the stream to it awaits that base state; the statement below
is correspondingly more general.

This is an instantiation of `certificateCarryingNoFold` and re-proves nothing.

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the base state, the colouring statement, the level count and
the level.  Claims no reader item (its reader locus is the one already claimed by
`certificateCarryingNoFold`). -/
theorem certificateCarryingNoFold_at_realized
    (S : FixedLevelCarriers.LevelCarrierSpec) (C : CanonicalChain S)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (GapColouring : Prop) (hgap : GapColouring) (k : ℕ)
    (hbase : CertifiedAt (C.lev 0)
      (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ 0)
      (DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ 0))
    (hstep : ∀ i, i < k → GapColouring →
      CertifiedAt (C.lev i)
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ i)
        (DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ i) →
      CertifiedAt (C.out i)
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ (i + 1))
        (DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ (i + 1)))
    (j : ℕ) (hj : j ≤ k) :
    CertifiedAt (C.lev j)
      (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ j)
      (DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀ j) :=
  certificateCarryingNoFold C
    (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀)
    (DepthThread.realizedDepth S aE q2E sE auxW invT robD S₀)
    GapColouring hgap k hbase hstep j hj

/-- **The frozen guarded clause entails the banked difference form.**

`IteratedCanonicalChaining.chainNoFold` takes the *difference-form* per-level
hypothesis `comp R_i^+ = comp R_i + H_i + 1`, which its own docstring records as
GAP-EXPOSED 4 relative to the frozen certificate-guarded clause C3.  This theorem
is the un-collapsing statement, proved rather than asserted: **the guarded clause
implies the difference form** at every level of the frozen range, once the budget
stream is the banked ladder, because the fold supplies `comp R_i = D_i` at level
`i` and the guarded clause supplies `comp R_i^+ = D_{i+1}`, and `Aux 6` is the
frozen budget update between them.

**The converse is not claimed and does not hold in this shape**: the difference
form mentions no `Lambda_3` at all, so it cannot deliver the second conjunct of
`eq:fixed-level-no-induction`.  That asymmetry is the whole content of GAP-EXPOSED
1 and 4, and it is the reason this module exists.

General in the specification, the chain, the three exponent families, the three
`AuxOut` families, the base state, the depth stream, the colouring statement, the
level count and the level.  Claims no reader item. -/
theorem guardedStep_gives_difference_form
    (S : FixedLevelCarriers.LevelCarrierSpec) (C : CanonicalChain S)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (bseq : ℕ → ℕ) (GapColouring : Prop) (hgap : GapColouring) (k : ℕ)
    (hbase : LevelCertified C
      (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq 0)
    (hstep : ∀ i, i < k → GapColouring →
      LevelCertified C
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq i →
      OutputCertified C
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq i)
    (i : ℕ) (hi : i < k) :
    D (C.out i) =
      D (C.lev i) + EffectiveMaterialization.realizedOverhead S aE q2E sE i + 1 := by
  have hlev := certificateCarryingNoFold C
    (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq
    GapColouring hgap k hbase hstep i (le_of_lt hi)
  have hout := hstep i hi hgap hlev
  rw [hout.1, hlev.1, realizedD_succ]

/-- **The certificate-carrying fold reproduces the banked complexity fold.**

Cross-check, in the kernel: feeding this module's hypotheses to the banked
`IteratedCanonicalChaining.chainNoFold` -- through
`guardedStep_gives_difference_form` -- returns that theorem's own conclusion
`comp R_j = D_j` at the banked ladder.  So the new fold neither re-derives nor
contradicts the banked one; it strictly extends it by the second conjunct, which
`certificateCarryingNoFold` supplies simultaneously.

Nothing is re-proved: `chainNoFold` is applied once, by pin.

General in the same arguments as `guardedStep_gives_difference_form`.  Claims no
reader item -- `05-iteration.tex:138` is `ITER-001`'s. -/
theorem certificateFold_reproduces_chainNoFold
    (S : FixedLevelCarriers.LevelCarrierSpec) (C : CanonicalChain S)
    (aE q2E sE : ℕ → ℕ) (auxW invT robD : ℕ → List ℕ) (S₀ : LevelState)
    (bseq : ℕ → ℕ) (GapColouring : Prop) (hgap : GapColouring) (k : ℕ)
    (hbase : LevelCertified C
      (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq 0)
    (hstep : ∀ i, i < k → GapColouring →
      LevelCertified C
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq i →
      OutputCertified C
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀) bseq i)
    (j : ℕ) (hj : j ≤ k) :
    D (C.lev j) = BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD S₀ j := by
  have hD0 : D (C.lev 0) = S₀.budgetD := hbase.1
  exact chainNoFold S C aE q2E sE auxW invT robD S₀ j hD0
    (fun i hij =>
      guardedStep_gives_difference_form S C aE q2E sE auxW invT robD S₀ bseq
        GapColouring hgap k hbase hstep i (lt_of_lt_of_le hij hj))

/-! ## Part 4: clause C3, transported (`ONELEVEL-001` x `12:345--348`) -/

/-- **Clause C3's two conclusions, as one certified pair** --
`07-one-level-construction.tex:60--67`, `05-public-records.tex:814--822`,
`step:L-12` (`11-one-level-assembly.tex`, label line 766).

The banked `OneLevelAssembly.oneLevelAssembly_no` is applied once and nothing it
proves is restated; the only content added is that its two conclusions are read as
one `CertifiedAt` at the single integer `D + H + 1`, which is frozen line 784's
"the equality and the robustness lower bound use the same integer, as required in
clause C3".

Every hypothesis is the banked endpoint's own, in the same order and with the same
meaning: the four guarded inputs are what `step:L-10` hands the bridge
(`11:642--643`, "the direct bridge consumes only `exp:E-10-common`"), and the unguarded
binders are the structural legality facts of `thm:direct-robustification`
(`10-direct-bridge.tex:38--41,53--56`).  The overhead is the banked
`OneLevelCompletion.levelOverhead` at the banked outer exponent `rQ b_out delta_U`,
so `H` is never a numeral and the two widths stay distinct (`M3`, `M9`).

General in the two pre-wrapper carriers, the pre-wrapper matrix, the source
budget, the four exponents, the outgoing depth, the two real parameters and the
promise statement.  Claims no reader item -- `04-bridge.tex:171--172` is
`ONELEVEL-001`'s. -/
theorem clauseC3_certifiedAt {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc a w2 ws wq bout : ℕ) {δU θ : ℝ} (NoCert : Prop)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hb : 1 ≤ bout) (hgates : directEntryGates bout δU θ (3 / 5))
    (hEntry : NoCert → 3 ≤ Dsrc)
    (hCW : NoCert → D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hNear : NoCert → alignedExact Dsrc a w2 ws wq
      ≤ Dfamily (interlaceFun (alignedMatrix N wq) 1)
          (bracketGE (Fin (2 ^ wq) → Y) (Fin (2 ^ wq) × X) 1 θ (1 - δU)))
    (hInput : NoCert → alignedExact Dsrc a w2 ws wq - 1
      ≤ LambdaGE (alignedMatrix N wq) 1 θ (3 / 5))
    (hc : NoCert) :
    CertifiedAt (levelOutput N wq bout δU)
      (Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1) bout :=
  oneLevelAssembly_no N Dsrc a w2 ws wq bout NoCert hX hY hδ0 hδ1 hθ0 hθ1 hb
    hgates hEntry hCW hNear hInput hc

/-- **Clause C3 composed with the canonical chaining equation** --
`12-iteration-specification.tex:341--348` in full, at one successor index:

> "The `NO` clause C3 gives both the exact equality and the depth-`b_{i+1}`
> certificate for `R_i^+`.  Equations `eq:canonical-complexity-invariance`--%
> `eq:canonical-bracket-invariance` and the canonical chaining equation transport
> both statements to `R_{i+1}`."

This is the second regeneration half `ONELEVEL-001` owed: the C3 endpoint is not
merely available beside the transport, it is **fed through it in a proof term**.
`clauseC3_certifiedAt` supplies the antecedent and `certifiedAt_transport` --
hence the banked `isCanonicalReindex_bracket` and
`isCanonicalReindex_complexity` -- supplies the conclusion.

The chaining hypothesis is the frozen typed assertion
`R_{i+1} = Can_{m_{i+1},n_{i+1}}(R_i^+)` of lines 127--136, taken as
`IteratedCanonicalChaining.IsCanonicalReindex` and never as a heterogeneous
equality; on a `CanonicalChain` it is that record's own
`CanonicalChain.isCanonicalReindex` field-derived theorem, so this statement and
`chainStep_certificate` are the two readings of one frozen sentence.

The two linear orders on the output carriers are instance arguments
(GAP-EXPOSED 4 of this module).

General in the two pre-wrapper carriers, the pre-wrapper matrix, the source
budget, the four exponents, the outgoing depth, the two real parameters, the
promise statement, the two output orders, the two successor slot counts and the
successor matrix.  Claims no reader item. -/
theorem clauseC3_transported {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dsrc a w2 ws wq bout : ℕ) {δU θ : ℝ} (NoCert : Prop)
    [LinearOrder (Fin (Qwidth bout δU) → Fin (2 ^ wq) × X)]
    [LinearOrder (Fin (Qwidth bout δU) × (Fin (2 ^ wq) → Y))]
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δU) (hδ1 : δU < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hb : 1 ≤ bout) (hgates : directEntryGates bout δU θ (3 / 5))
    (hEntry : NoCert → 3 ≤ Dsrc)
    (hCW : NoCert → D (alignedMatrix N wq) = alignedExact Dsrc a w2 ws wq)
    (hNear : NoCert → alignedExact Dsrc a w2 ws wq
      ≤ Dfamily (interlaceFun (alignedMatrix N wq) 1)
          (bracketGE (Fin (2 ^ wq) → Y) (Fin (2 ^ wq) × X) 1 θ (1 - δU)))
    (hInput : NoCert → alignedExact Dsrc a w2 ws wq - 1
      ≤ LambdaGE (alignedMatrix N wq) 1 θ (3 / 5))
    {mNext nNext : ℕ} {Rnext : Fin mNext → Fin nNext → Bool}
    (hchain : IsCanonicalReindex (levelOutput N wq bout δU) mNext nNext Rnext)
    (hc : NoCert) :
    CertifiedAt Rnext (Dsrc + levelOverhead a w2 ws wq (rQ bout δU) + 1) bout :=
  certifiedAt_transport hchain
    (clauseC3_certifiedAt N Dsrc a w2 ws wq bout NoCert hX hY hδ0 hδ1 hθ0 hθ1 hb
      hgates hEntry hCW hNear hInput hc)

/-! ## Part 5: the seed (`12:360--379`), conditional on the scheduled-depth
full-cube display

Frozen line 379 justifies the two seed conditions "by `lem:full-cube-seed`,
`lem:canonical-reindexing-invariance`".  The second factor is banked; the first is
**GAP-EXPOSED 1** of this module at the scheduled depth, so the base clause is
landed conditionally, with the missing display as an explicit named hypothesis and
never as an axiom. -/

/-- **The frozen seed conditions on `R_0 = Can(F_{B(n)})`, conditional on
`lem:full-cube-seed` at the scheduled depth** --
`12-iteration-specification.tex:360--379`, display lines 374--378.

The `lem:canonical-reindexing-invariance` factor of line 379 is supplied outright,
by two banked pins in one proof term: the complexity half is
`IteratedCanonicalChaining.paperSeedReindexed_isCanonical`'s second conjunct and
the bracket half is
`CanonicalBracketInvariance.paperSeed_certificate_at_scheduled_depth`.

The `lem:full-cube-seed` factor is the **hypothesis** `h`, at exactly the frozen
scheduled depth `B(n) = IterationAssembly.depthB n` and the frozen column density
`3/5`.  It is not asserted anywhere in this module, and `D_0` stays a binder
because the budget identity of frozen line 370 is `ITERATED-CANONICAL-CHAINING-001`'s
GAP-EXPOSED 5 and is not claimed here either.

Every quantity is evaluated through the banked chain
`n -> depthB n -> aSeed -> qSeed -> (2^{q_seed}, q_seed)`; **no numeral is
assigned to anything** (`M3`), and by
`IteratedCanonicalChaining.paperSeedReindexed_nondegenerate` the two carriers
exceed one at the frozen parameters, so this is the paper's own object and not a
point.

General in the source size and the public budget.  Claims no reader item. -/
theorem paperSeed_certifiedAt (n D0 : ℕ)
    (h : CertifiedAt (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n))
      D0 (IterationAssembly.depthB n)) :
    CertifiedAt (paperSeedReindexed n) D0 (IterationAssembly.depthB n) :=
  ⟨(paperSeedReindexed_isCanonical n).2.trans h.1,
    paperSeed_certificate_at_scheduled_depth n D0 h.2⟩

/-- **The one point of the route where the antecedent is banked outright** --
the depth-zero full cube.

`OneLevelCompletion.fullCubeSeed_D` gives `comp F = 8` and `.fullCubeSeed_lambda`
gives `Lambda_3(F,1,x_out(0),3/5) >= 8` on `fullCube 126`; together they are the
certified pair at budget `8` and depth `0`.  The width `126` is not a numeral of
this module: `CanonicalBracketInvariance.qSeed_zero` proves it is the paper's own
evaluated `q_seed(0) = 2^{a_seed(0)} - 2` through the banked least-integer
accessor, and `8 = a_seed(0) + 1`.

**Scope, and why this does not discharge GAP-EXPOSED 1.**  `sec:full-cube-seed`
opens "Fix a requested depth `b >= 1`" (frozen `12:16`), so `b = 0` is outside
`lem:full-cube-seed`'s frozen range; what is consumed here is a self-contained
banked statement about `fullCube 126` at `x_out 0 = 1`, not an instance of that
lemma.  It is an instance of `def:robust-seed`, which imposes no lower bound on
the depth.  The scheduled-depth display at `b = B(n)` remains owed.

Claims no reader item. -/
theorem fullCubeSeed_certifiedAt : CertifiedAt (fullCube 126) 8 0 :=
  ⟨fullCubeSeed_D, fullCubeSeed_lambda⟩

/-- **The banked depth-zero pair survives the canonical reindexing** (LANE-GATE 3).

`certifiedAt_transport` fired with every hypothesis discharged, at the one point of
the route where a `def:robust-seed` certificate is banked outright.  So the
transport of Part 1 -- and with it the chain step of Part 2 and the C3 composition
of Part 4 -- is not an implication whose antecedent is nowhere available: the exact
complexity **and** the three-rung depth bound both survive simultaneously, at a
nondegenerate scale (`8 >= 3`, the frozen entry floor) on a `2^126`-row carrier.

The carrier's order is an instance argument here (GAP-EXPOSED 4); the concrete
firing at the frozen lexicographic order of `12:96--97` is
`fullCubeSeed_certifiedAt_at_canonical` below, which supplies
`CanonicalBracketInvariance.fullCubeSeedRowOrder`.

General in the order, the two slot counts and the reindexed matrix.  Claims no
reader item. -/
theorem fullCubeSeed_certifiedAt_transported [LinearOrder (Fin 126 → Bool)]
    {m n : ℕ} {Rnext : Fin m → Fin n → Bool}
    (h : IsCanonicalReindex (fullCube 126) m n Rnext) :
    CertifiedAt Rnext 8 0 :=
  certifiedAt_transport h fullCubeSeed_certifiedAt

/-- **The same firing at the frozen lexicographic carrier order.**

`12-iteration-specification.tex:96--97`, "finite function spaces use lexicographic
order in increasing coordinate order", supplied through the banked
`CanonicalBracketInvariance.fullCubeSeedRowOrder` and given explicitly at the use
site so that no instance ambiguity can arise -- the same discipline that module
uses for `fullCubeSeed_noReading_transported`.

Claims no reader item. -/
theorem fullCubeSeed_certifiedAt_at_canonical :
    CertifiedAt
      (@Can (Fin 126 → Bool) (Fin 126) Bool _ fullCubeSeedRowOrder _ _ (2 ^ 126) 126
        (by simp) (by simp) (fullCube 126)) 8 0 :=
  @fullCubeSeed_certifiedAt_transported fullCubeSeedRowOrder (2 ^ 126) 126 _
    (@Can_isCanonicalReindex (Fin 126 → Bool) (Fin 126) Bool _ fullCubeSeedRowOrder
      _ _ (2 ^ 126) 126 (by simp) (by simp) (fullCube 126))

/-! ## Part 6: non-vacuity, hypothesis consistency, and the deferred canonical
inhabitation

**Canonical inhabitation is REGISTERED AS DEFERRED.**  The paper's own instance of
`certificateCarryingNoFold` is the chain of frozen `12:360--379` at
`k = L(n)`, whose level matrices are the outputs of the unbuilt Stage-1--4
constructor chain; `IteratedCanonicalChaining` records the same obligation for
`CanonicalChain` itself (its GAP-EXPOSED 3).  The probe below is therefore
**NON-FIDELITY** and does not satisfy that obligation, which is discharged only
when the construction lands. -/

/-- **A constant chain -- NON-FIDELITY probe carrier.**

The three frozen equations of `eq:iterated-canonical-chaining` at every banked
`LevelCarrierSpec`, with the constant matrix at every level: `Can` of a constant is
that constant, so the chaining equation holds definitionally.

**It is explicitly not the paper's chain**, and its certified budget is `0`, which
is below the frozen entry floor `3 <= D` of `step:L-03`.  It exists only to show
that the fold's premise bundle is simultaneously satisfiable **with a non-empty
per-level range**, i.e. that `certificateCarryingNoFold` is not true merely because
its step hypothesis can never fire.  The nondegenerate firing of the *transport*
that the fold is built from is `fullCubeSeed_certifiedAt_at_canonical`, at budget
`8` on a `2^126`-row carrier.

General in the specification.  Claims no reader item. -/
noncomputable def probeConstChain (S : FixedLevelCarriers.LevelCarrierSpec) :
    CanonicalChain S where
  Row := fun i => Fin (S.rowCarrier (i + 1))
  Col := fun i => Fin (S.colCarrier (i + 1))
  rowFintype := fun _ => inferInstance
  rowOrder := fun _ => inferInstance
  colFintype := fun _ => inferInstance
  colOrder := fun _ => inferInstance
  lev := fun _ _ _ => false
  out := fun _ _ _ => false
  rowCard := fun _ => Fintype.card_fin _
  colCard := fun _ => Fintype.card_fin _
  chain := fun _ => rfl

/-- **The fold fires, with a non-empty per-level range -- NON-FIDELITY**
(LANE-GATE 3).

Every hypothesis of `certificateCarryingNoFold` is discharged at the probe chain,
at **every** level count `k` and hence in particular at `k >= 1`, where the frozen
family `0 <= i < k` is non-empty and the step hypothesis genuinely fires.  So the
fold is not vacuously true, and the induction of Part 3 runs rather than collapsing
to its base case.

The certified budget is the constant `0`, through the banked
`PublicRecords.D_const`; the depth stream is an arbitrary sequence, which is legal
because the frozen theorem quantifies `b_i` in clause F2 before either promise
condition.  Both facts are why this probe is labelled NON-FIDELITY: at the frozen
entry floor `3 <= D` no such chain is a legal level family.

General in the specification, the depth stream, the level count and the level.
Claims no reader item. -/
theorem certificateCarryingNoFold_fires (S : FixedLevelCarriers.LevelCarrierSpec)
    (bseq : ℕ → ℕ) (k j : ℕ) (hj : j ≤ k) :
    LevelCertified (probeConstChain S) (fun _ => 0) bseq j := by
  refine certificateCarryingNoFold (probeConstChain S) (fun _ => 0) bseq True trivial k
    ⟨PublicRecords.D_const false, Nat.zero_le _⟩
    (fun i _ _ _ => ⟨PublicRecords.D_const false, Nat.zero_le _⟩) j hj

/-- **Hypothesis consistency for the ladder-wired forms, at the frozen `k = 0`
reading -- NON-FIDELITY.**

`guardedStep_gives_difference_form` and `certificateFold_reproduces_chainNoFold`
wire the budget stream to the banked ladder, and that bundle is **strictly
stronger** than the free-stream one: at `k >= 1` it forces
`comp R_{i+1} = comp R_i + H_i + 1`, so the constant probe chain of
`certificateCarryingNoFold_fires` cannot satisfy it.  An implication whose
antecedent is nowhere satisfiable would be vacuously true, so the bundle is fired
here at the frozen `k = 0` reading of lines 320--323 -- "the family indexed by
`0 <= i < k` is empty ... All conclusions reduce to their stated hypotheses at
`R_0`" -- which is exactly the precedent
`IteratedCanonicalChaining.chainedFold_hypotheses_consistent` sets for the banked
complexity fold.

**No value is invented.**  The base state is the paper's own
`SuccessorMajorant.seedState n scales` with only the two budget slots overwritten
by the probe's own complexity, `0`, exactly as that banked precedent overwrites
them by `comp R_0`; every other slot is the banked seed value.

**Non-vacuity at `k >= 1` with a non-zero certified budget is precisely the
deferred canonical inhabitation** (GAP-EXPOSED 2): it needs a chain whose level
complexities climb the ladder, i.e. the unbuilt constructor chain.  The
nondegenerate witness this module *can* exhibit is at the matrix level,
`fullCubeSeed_certifiedAt_at_canonical`, at budget `8` on a `2^126`-row carrier.

General in the specification, the three exponent families, the three `AuxOut`
families, the source size, the public scale list and the depth stream.  Claims no
reader item. -/
theorem certificateFold_ladder_hypotheses_consistent
    (S : FixedLevelCarriers.LevelCarrierSpec) (aE q2E sE : ℕ → ℕ)
    (auxW invT robD : ℕ → List ℕ) (n : ℕ) (scales : List ℕ) (bseq : ℕ → ℕ) :
    LevelCertified (probeConstChain S)
        (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD
          { seedState n scales with budgetD := 0, budgetY := 0 }) bseq 0 ∧
      (∀ i, i < 0 → True →
        LevelCertified (probeConstChain S)
            (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD
              { seedState n scales with budgetD := 0, budgetY := 0 }) bseq i →
        OutputCertified (probeConstChain S)
            (BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD
              { seedState n scales with budgetD := 0, budgetY := 0 }) bseq i) ∧
      D ((probeConstChain S).lev 0)
        = BudgetThreadWiring.realizedD S aE q2E sE auxW invT robD
            { seedState n scales with budgetD := 0, budgetY := 0 } 0 := by
  refine ⟨⟨PublicRecords.D_const false, Nat.zero_le _⟩, ?_, PublicRecords.D_const false⟩
  intro i hi
  omega

/-- **Hypothesis consistency: the fold's conclusion is a saturation at every
level, never an over-demand.**

The full hypothesis bundle of `certificateCarryingNoFold`, run at the frozen
regime, yields at every `j <= k` the *equality*
`Lambda_3(R_j,1,2^{-b_j},3/5) = D_j` -- so no `False` is derivable from the two
conjuncts of `eq:fixed-level-no-induction`, at any level, and the frozen display's
`>=` is exactly tight.  This is `certifiedAt_saturates` applied to the fold's own
output, with the row-carrier nonemptiness derived from the banked
`FixedLevelCarriers.carriers_two_le_succ` rather than assumed.

The level index is `j + 1` because `carriers_two_le_succ` speaks about successor
carriers; at `j = 0` the corresponding fact belongs to the seed and is
`FixedLevelCarriers.SeedAnchored`'s business, not this module's.

General in the specification, the chain, the two streams, the colouring statement,
the level count and the level.  Claims no reader item. -/
theorem certificateCarryingNoFold_saturates (C : CanonicalChain S)
    (Dseq bseq : ℕ → ℕ) (GapColouring : Prop) (hgap : GapColouring) (k : ℕ)
    (hbase : LevelCertified C Dseq bseq 0)
    (hstep : ∀ i, i < k → GapColouring → LevelCertified C Dseq bseq i →
      OutputCertified C Dseq bseq i)
    (j : ℕ) (hj : j + 1 ≤ k) :
    LambdaGE (C.lev (j + 1)) 1 (xOut (bseq (j + 1))) ((3 : ℝ) / 5)
      = Dseq (j + 1) := by
  have hrow : 1 ≤ Fintype.card (Fin (S.rowCarrier (j + 1))) := by
    rw [Fintype.card_fin]
    have := (FixedLevelCarriers.carriers_two_le_succ S j).1
    omega
  exact certifiedAt_saturates (C.lev (j + 1)) hrow
    (certificateCarryingNoFold C Dseq bseq GapColouring hgap k hbase hstep (j + 1) hj)

end EthInapproximability.ParameterizedNP.CertificateCarryingFold
