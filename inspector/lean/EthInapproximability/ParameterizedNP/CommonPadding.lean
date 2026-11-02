import EthInapproximability.ParameterizedNP.PaddingAndClock

/-!
# Parameterized NP route: common padding (`step:I-11`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`CLOCK-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 134),
"Total computable nondecreasing unbounded slow diagonal tied to the same
machine/compiler, with **final-only padding** and subexponential table size",
recorded there as human **proved** / Lean **partially landed**, with the
explicit remainder "**`step:I-11` in full** -- the representative maps, the
duplication argument and the preservation of communication complexity under
padding".  This module is exactly that remainder.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## Provenance

* **Autoformalization anchors (proof source).**
  * `step:I-11` *Common padding*,
    `sections/13-iteration-assembly.tex`, label line 809, body lines
    809--884.  Its headline is "The final padding uses explicit representative
    maps, one common square exponent, and preserves deterministic
    communication complexity exactly."
  * The carrier bounds of lines 815--818,
    `|X_{n,I}| <= 2^{g(n)}` and `|Y_{n,I}| <= 2^{g(n)}`, and the fitting
    sentence of line 825, "Then `g(n) <= e(n)`, so both carriers have at most
    `S_n` elements".
  * The enumerations `e_X`, `e_Y` of lines 829--834, the surjections
    `pi_X`, `pi_Y` of lines 835--847, the nonemptiness sentence of line 848,
    the inverse indices `iota_X`, `iota_Y` of lines 849--852, the round-trip
    identities of lines 853--856, and the duplicate-slot count of lines
    857--858.
  * The padded square matrix of lines 860--864, the restriction sentence of
    lines 865--866, the two complexity directions of lines 866--872, and
    `expi:E-11-D` (label line 875, display lines 873--876).
  * The scope sentences of lines 878--884.
  * `sec:common-padding` in `sections/12-iteration-specification.tex`
    (label line 565), specifically the duplication paragraph at lines
    630--636: "Duplicate existing rows and columns until both sides have
    exactly `S_n` elements.  Duplication preserves communication complexity:
    the original matrix is a restriction of the padded one, and a protocol for
    the original matrix computes every duplicate after mapping it to its
    representative.  The resulting square matrix is the truth table of a
    function on two `e(n)`-bit inputs.  Its length depends only on `n`", with
    `eq:common-size` (label line 628) supplying `e`, `S_n`, `T_n`.
  * `conv:finite-slots` in `sections/02-mechanical-contract.tex` fixes the
    zero-based reading of `[S_n] = {0, ..., S_n - 1}` used throughout, and is
    already transcribed in `FiniteSlots.lean`.

* **Banked endpoints** (all from
  `src/EthInapproximability/ParameterizedNP/PaddingAndClock.lean`, tranche
  `cc-t1t-r1`; all names below were grep-verified in that file before use).
  *Actually consumed:* `commonSizeParameters` (in
  `carrierFitsCommonSquare`), `gMaj_spec` and `zhat` (in
  `carrierFitsCommonSquare_of_zhat`), and the definitions `gMaj`, `eCommon`,
  `sCommon`, `tCommon` throughout Part 4; in Part 6 additionally `slowIndex`,
  `zhat`, `zSeed`, `qSeed` and `aSeed_spec`, used **only** to discharge the
  frozen carrier bounds of one pinned consistency witness, never inside a
  landed `step:I-11` statement.  *Verified present but **not** consumed,
  because `step:I-11` runs strictly after the clock and the seed and needs
  neither:* `slowIndex_safePrefix`, `seedCeiling`, `seedBudgetRow`,
  `zhat_sublinear`, `zhat_zero_branch`.  Manufacturing a dependence on those
  five would be a fabricated hypothesis, not a trace.  Nothing any of them
  states is restated here: `commonSizeParameters` is the frozen statement
  about the **numbers** `e`, `S`, `T`, and this module is the first in the
  route to say anything about a **matrix**.

* **Banked route object consumed by Part 6 only** (from
  `src/EthInapproximability/ParameterizedNP/OneLevelCompletion.lean`, tranche
  `cc-t1p-r2`, ledger row `SEED-001`): the full cube `fullCube` and its
  deterministic communication complexity `fullCube_D_eq`.  `fullCube` is banked
  as a **depth-zero instance of the autoformalization `def:robust-seed` only**
  and is read here in exactly that way -- the sole property used is the
  depth-free `comp F = a + 1` under the frozen sandwich `2^{a-1} < q <= 2^{a}`.
  **It is never read as `lem:full-cube-seed`**, whose minimality rule is stated
  for requested depth `b >= 1` (`12-iteration-specification.tex:16`); no
  bracket, `Lambda`, robustness certificate, requested depth or seed interface
  enters this module.

* **Vendored interfaces consumed through the facades** (no port, no copy):
  `Workspace.Types.Protocol.Protocol` with its `cost`, `eval` and `Computes`,
  `Workspace.Types.CommComplexity.AchievableCosts` and `D`, and the
  kernel-checked
  `Workspace.ProofLemmas.SublemmaPrecompNoIncrease`
  (`vendor/npc-cc/Workspace/ProofLemmas/SublemmaPrecompNoIncrease.lean`),
  re-exported below under the route name `precomposition_no_increase`.  This
  is the same consumption pattern `InheritedContracts.lean` uses for
  `NPCC.coord_projection` and `Workspace.BracketLemmas.monotonicity`.  Nothing
  is transcribed from `C:/lean/npc-cc/EthProof`, which traced the older
  fixed-width manuscript and is not a trace or style source here.

* **Imports.**  `EthInapproximability.ParameterizedNP.PaddingAndClock` and,
  through it, `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the cited AGHP balanced-family axiom stays outside this
  module's closure, and no ledger note for it is needed.

* **Proof status.**  Every declaration below is **new**.  One declaration is a
  named **facade** for an inherited vendored theorem
  (`precomposition_no_increase`); it re-exports and does not re-prove.

## What this module lands

1. **The representative maps** (frozen lines 829--856).  `PadEnum` is the
   per-side enumeration datum `e_X : [|X|] -> X` together with the two facts
   the frozen text needs to define `pi_X`: nonemptiness of the carrier
   (line 848) and the fitting bound `|X| <= S_n` (line 825).  `PadEnum.rep`
   is `pi_X` with **both** branches of the exhaustive formula of lines
   841--847 named (`rep_of_lt`, `rep_of_ge`); `PadEnum.idx` is `iota_X`;
   `rep_idx` is the frozen round trip `pi_X . iota_X = id`; `rep_surjective`
   is the word "surjections" of line 835.
2. **The duplicate-slot count** (frozen lines 857--858, "precisely
   `S_n - |X_{n,I}|` row slots ... are filled by duplicates"), as
   `duplicateSlots` and `duplicateSlots_card`, with `mem_range_iff` proving
   that the slot is a duplicate exactly when it is beyond the enumeration.
3. **The common square** (frozen lines 820--825, 860--864).  `CommonPadding`
   forces **one** `S` on both sides -- that is the content of the word
   *common* -- and `paddedMatrix` is `R^(u,v) = R(pi_X(u), pi_Y(v))`.
   `paddedMatrix_restrict` is the frozen sentence of lines 865--866.
4. **Preservation of deterministic communication complexity** (frozen lines
   866--876; `12-iteration-specification.tex:630--636`), as three theorems in
   the frozen order: `complexity_le_padded` (the restriction direction),
   `padded_le_complexity` (the local-computation direction) and the headline
   `paddedComplexity`, which is `expi:E-11-D` with equality, not an
   inequality.
5. **The frozen common square exponent** (frozen lines 815--825), as
   `carrierFitsCommonSquare`, `carrierFitsCommonSquare_of_zhat`,
   `frozenPadEnum`, `frozenCommonPadding`, `frozenPaddedComplexity` and
   `frozenPaddedEntryCount`, all at `S = sCommon V n` of the banked
   `eq:common-size`.  The carrier bounds `|X| <= 2^{g(n)}` are **named
   hypotheses**, because frozen line 815 derives them from `step:I-07` and the
   definition of `g`, and `step:I-07` is not landed in this module; the
   *definition of `g`* half of that sentence **is** landed, as
   `carrierFitsCommonSquare_of_zhat`, through the banked `gMaj_spec`.
6. **Hypothesis consistency at a banked route object** (Part 6).  `seedPadding`
   instantiates the frozen padding at the carriers of the banked `fullCube`,
   `seedPadding_D` transports its banked complexity through `expi:E-11-D`, and
   `witnessSeedPadding` / `witnessSeedPadding_D` /
   `witnessSeedPadding_duplicates` discharge the *whole* premise bundle of
   `frozenPaddedComplexity` simultaneously, at a genuine frozen `S_n` of a
   pinned clock, with real duplication.  Part 5's toy carriers do not answer
   that question; a bundle can be inhabited at toy values and contradictory at
   frozen ones.

## Reader counterparts

The reader counterparts are in
`routes/parameterized-np/reader-facing/sections/06-eth.tex`, subsection "A
common truth-table length".  **That file was opened first-hand this tranche
and every cited item read to confirm it states the same fact.**  `CLOCK-001`
already claims lines 281, 283, 284, 288, 298--302, 304, 317, 318 and 319 of
that file for the seed and size parameters; the items below are disjoint from
those, and no item below is assigned to two declarations.

* line 322, "Both carrier sizes of every branch output are at most
  `2^{g(n)}`" -- to `carrierFitsCommonSquare`.  The `cc-t1t-r1` ledger cell
  listed this line as unclaimed; this tranche claims it, and the ledger row is
  updated in the same change.  `eq:paper-g-little-o` (label line 312) stays
  unclaimed, as it did before.
* lines 325--329, the displayed fallback maps `u^flat` and `v^flat` -- to
  `PadEnum.rep`.  One reader display, one declaration: the row and column
  halves are the *same* Lean map applied to the two sides, which is why this
  item is not split.  The reader display is **one-based** (`u <= m`, fallback
  `1`); the frozen autoformalization at lines 841--847 is **zero-based**
  (`u < |X|`, fallback `e_X(0)`) under `conv:finite-slots`.  The
  autoformalization is the proof source, and
  `oneBasedGuard_is_not_the_frozen_guard` makes the shift checkable in the
  kernel.
* line 330, `R^_n(u,v) = R_{L(n)}(u^flat, v^flat)` -- to `paddedMatrix`.
* lines 332--333, "The original matrix is the restriction to the first `m`
  rows and first `r` columns" -- to `paddedMatrix_restrict`.
* lines 333--334, "while a protocol for it computes every duplicate after the
  parties apply the two fallback maps locally" -- to `padded_le_complexity`.
* `eq:paper-padding-invariance` (label line 338, display lines 336--337),
  `CC(R^_n) = CC(R_{L(n)})` -- to `paddedComplexity`.
* lines 340--341, "every branch has the same truth-table length `T_n`" -- to
  `frozenPaddedEntryCount`.

**Claiming no reader item** (autoformalization-only content -- the reader
prints neither the enumerations, nor the inverse index, nor the duplicate
count, nor the surjectivity word): `PadEnum` and its fields, `PadEnum.idx`,
`rep_of_lt`, `rep_of_ge`, `idx_val_lt`, `rep_idx`, `idx_rep`,
`rep_surjective`, `idx_injective`, `mem_range_iff`, `duplicateSlots`,
`duplicateSlots_eq`, `duplicateSlots_card`, `CommonPadding`,
`complexity_le_padded`, `precomposition_no_increase`,
`carrierFitsCommonSquare_of_zhat`, `frozenPadEnum`,
`frozenCommonPadding`, `frozenPaddedComplexity`, and every declaration of
Parts 5 and 6.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: `PadEnum` carries the enumeration and its two frozen side
  conditions and **nothing else**; `CommonPadding` carries two `PadEnum`s and
  **nothing else**.  No complexity value, no protocol, no robustness
  certificate, no promise certificate and no `D`-equation is a field of
  either.  `expi:E-11-D` is a theorem about the pinned construction, and
  `surjectivityField_would_be_redundant` records in the kernel that the
  tempting extra field "`pi_X` is surjective" would restate a derived
  telescope.
* `M7`: nonemptiness is preserved as the explicit field `PadEnum.pos`, which
  is exactly the frozen sentence of line 848 ("Nonemptiness of
  communication-matrix carriers makes both fallback values defined"); it is
  **not** derivable from the enumeration, since the empty carrier admits the
  empty enumeration.
* `M9`: the representative map is defined by the frozen **exhaustive**
  two-branch formula, and both branches are named
  (`rep_of_lt`, `rep_of_ge`); neither is left implicit.
* Zero-based slots (`conv:finite-slots`) are used throughout: `[S_n]` is
  `Fin S`, and the fallback index is `0`, not `1`.
* Both interlace widths `q` and `Q` are untouched here: `step:I-11` runs
  strictly after the last level, so no interlace appears in this module and
  none is renamed or re-derived.

## GAP-EXPOSED (what this module deliberately does not claim)

1. **The machine layer is out of scope, explicitly.**  Nothing here models the
   canonical environment `M_*`, the machines `A_cert` / `A_raw`, the running
   time `tau_k`, `thm:canonical-machine-environment`,
   `thm:effective-materialization`, `cor:realized-effective-prefix`, or
   `eq:total-construction-time`
   (`12-iteration-specification.tex:645--655`).  In particular **no
   computability or runtime claim is made about `pi_X`, `pi_Y`, the padded
   matrix, or the emitted truth table**, and the frozen sentence
   "By `thm:eff-ledger`, both `zhat` and `g` are polynomial-time computable"
   (`12-iteration-specification.tex:617--618`) is not landed.
2. **No claim that duplication preserves the robustness certificate.**  Frozen
   lines 878--882 are emphatic that the argument "makes no claim that
   duplication preserves the density-sensitive robustness certificate needed
   as input to another level".  This module honours that boundary, and
   `paddingDestroysRowDistinctness` exhibits in the kernel a
   density-sensitive property that padding really does destroy, so the
   restriction to communication complexity is not decorative.
3. **The canonical order is data, not a derivation.**  Frozen lines 827--834
   fix `e_X` as the *unique increasing* enumeration in the canonical order of
   `def:level-public-input` and `def:level-trace`.  Those definitions are not
   in this module's scope, so the enumeration enters as a `PadEnum` field, and
   **no uniqueness or monotonicity of `e_X` is claimed**.  Every theorem below
   holds for an arbitrary enumeration, so it holds in particular for the
   canonical one.
4. **The matrix is arbitrary.**  Nothing below asserts that `R` is the level
   `L(n)` output `R_k(I)` of the iteration; that identification belongs to
   `ITER-001` and `SIZE-001`.  The carrier bounds `|X| <= 2^{g(n)}` of frozen
   lines 815--818 are therefore named hypotheses of
   `carrierFitsCommonSquare`, `frozenPadEnum` and `frozenCommonPadding`, never
   axioms and never structure fields.
5. **`step:I-12` is not landed here.**  The banked `commonSizeParameters`
   already carries `T_n = 2^{2 e(n)}` as a statement about numbers; the only
   step:I-12-adjacent fact added here is `frozenPaddedEntryCount`, which
   counts the entries of the **padded matrix**.  `expi:E-12-log`, the ceiling
   estimate of frozen lines 899--903 and `log_2 T_n = o(n)` are **not**
   claimed, and no `Filter.Tendsto` or asymptotic order relation appears
   anywhere in this module.
6. **No route completion is claimed.**  `step:I-11` is one mechanical step of
   Section 13; the headline theorem of the route is not in Lean.

## Reading notes

* **N1 (equality, not two inequalities).**  Frozen lines 866--876 prove two
  inequalities and conclude with the equality `expi:E-11-D`.  Both
  inequalities are landed separately and in the frozen order, and
  `paddedComplexity` is their conjunction as an equality.  The weaker
  one-sided spelling is not what the frozen display says and is not landed as
  the headline.
* **N2 (one general precomposition principle, used twice).**  The frozen proof
  runs the *same* argument twice, once along `pi` and once along `iota`: a
  protocol is transported by precomposing each party's local predicates.  The
  vendored `SublemmaPrecompNoIncrease` is exactly that principle, so both
  directions are instances of it -- the `iota` direction after rewriting along
  the round trip.  This is the frozen argument, not a shortcut around it:
  frozen line 869, "Alice locally computes `pi_X(u)`, Bob locally computes
  `pi_Y(v)`", *is* precomposition, and frozen lines 865--867, "Restricting
  `R^_n(I)` to `iota_X(X) x iota_Y(Y)` recovers `R_k(I)`", is precomposition
  along `iota` after `paddedMatrix_restrict`.
* **N3 (generality in the output type).**  The frozen matrix is Boolean.  `D`
  is vendored at an arbitrary output type `Z`, and every theorem below is
  stated at arbitrary `Z`, which **strengthens** rather than weakens the
  frozen statement; the Boolean case is the instance `Z = Bool` and is the one
  exercised by the witnesses in Part 5.

## Candidate encodings and ranking (NOVEL-concept protocol)

Two encodings of the representative maps were written and run against the same
aux-lemma battery before landing.

* **Candidate A (landed).**  Bundled per-side datum `PadEnum X S` with
  `enum : Fin (Fintype.card X) ~= X`, `pos`, `fits`, and a `CommonPadding`
  pairing two of them over one `S`.
* **Candidate B (rejected).**  Fully unbundled: every declaration takes
  `{m S : Nat}`, `e : Fin m ~= X`, `hpos : 0 < m`, `hle : m <= S` as separate
  binders, with no structure at all.

Ranking.  Battery: A proved 5/5 (inhabitation with the hardest field,
round trip, partial inverse, surjectivity, duplicate-slot count); B proved
3/5 -- it cannot state the duplicate-slot count or any `D`-theorem without
first importing `[Fintype X]` and transporting along `m = Fintype.card X`.
Faithfulness: frozen line 831 writes `e_X : [|X_{n,I}|] -> X_{n,I}`, so the
enumeration length **is** the carrier cardinality; A pins that, while B admits
a spurious length parameter that is forced anyway (the rejected candidate's
own `m = Fintype.card X` lemma proves it).  Length: A takes one binder per
side at every use site, B takes four.  Candidate A wins on all three axes and
is landed; `padEnumLengthIsForced` keeps B's decisive lemma in the kernel as
the record of why.
-/

namespace EthInapproximability.ParameterizedNP.CommonPadding

open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.PaddingAndClock

/-! ## Part 1: the representative maps of `step:I-11` -/

/-- **The per-side enumeration datum of `step:I-11`**
(`13-iteration-assembly.tex:827--848`).

Frozen lines 829--834: "Let `e_X : [|X_{n,I}|] -> X_{n,I}` ... be the unique
increasing enumerations in those canonical orders."  Frozen line 848:
"Nonemptiness of communication-matrix carriers makes both fallback values
defined."  Frozen line 825: "so both carriers have at most `S_n` elements."

Those are exactly the three fields, and nothing else is a field: no protocol,
no complexity value, no robustness or promise certificate, and no output
matrix (`M4`).  The enumeration length is `Fintype.card X` because frozen
line 831 writes the domain as `[|X_{n,I}|]`.

The *increasing* and *unique* clauses of line 834 are **not** claimed
(GAP-EXPOSED 3): the canonical order lives in `def:level-public-input` and
`def:level-trace`, outside this module, so `enum` is arbitrary data and every
theorem below therefore covers the canonical enumeration as one instance.

Claims no reader item: the reader states the fallback maps but never names an
enumeration. -/
structure PadEnum (X : Type u) [Fintype X] (S : ℕ) where
  /-- `e_X : [|X|] -> X`, the enumeration of the carrier in its canonical
  order (frozen line 831). -/
  enum : Fin (Fintype.card X) ≃ X
  /-- Nonemptiness of the carrier (frozen line 848), which is what makes the
  fallback value `e_X(0)` defined.  It is not derivable from `enum`: the empty
  carrier carries the empty enumeration. -/
  pos : 0 < Fintype.card X
  /-- `|X| <= S_n` (frozen line 825). -/
  fits : Fintype.card X ≤ S

namespace PadEnum

variable {X : Type u} [Fintype X] {S : ℕ}

/-- **`pi_X : [S_n] -> X_{n,I}`** -- `13-iteration-assembly.tex:835--847`,
the exhaustive two-branch formula

```
pi_X(u) = e_X(u)   if u < |X_{n,I}|,
          e_X(0)   if u >= |X_{n,I}|.
```

Zero-based throughout (`conv:finite-slots`): the slot type is `Fin S`, the
guard is the strict `u < |X|`, and the fallback index is `0`.

Reader counterpart: the displayed fallback maps `u^flat`, `v^flat` at
`06-eth.tex:325--329`, whose one-based spelling is refuted as a transcription
by `oneBasedGuard_is_not_the_frozen_guard`. -/
def rep (p : PadEnum X S) (u : Fin S) : X :=
  if h : (u : ℕ) < Fintype.card X then p.enum ⟨(u : ℕ), h⟩ else p.enum ⟨0, p.pos⟩

/-- **`iota_X(x) = e_X^{-1}(x)`, "viewing the returned index in the initial
segment of `[S_n]`"** -- `13-iteration-assembly.tex:849--852`.  The view into
`[S_n]` is the `fits` field, used here and nowhere else in the definition.

Claims no reader item: the reader never prints an inverse index. -/
def idx (p : PadEnum X S) (x : X) : Fin S :=
  ⟨((p.enum.symm x : Fin (Fintype.card X)) : ℕ),
    lt_of_lt_of_le (p.enum.symm x).isLt p.fits⟩

/-- **Aux 1a (the first branch of the frozen exhaustive formula).**  General
in the carrier, the enumeration datum and the slot. -/
theorem rep_of_lt (p : PadEnum X S) (u : Fin S) (h : (u : ℕ) < Fintype.card X) :
    p.rep u = p.enum ⟨(u : ℕ), h⟩ := by
  simp only [rep]
  rw [dif_pos h]

/-- **Aux 1b (the second branch of the frozen exhaustive formula, the
fallback).**  This is the branch that makes the padding a *duplication*:
every slot beyond the enumeration is sent to the single value `e_X(0)`.
General in the carrier, the enumeration datum and the slot. -/
theorem rep_of_ge (p : PadEnum X S) (u : Fin S) (h : Fintype.card X ≤ (u : ℕ)) :
    p.rep u = p.enum ⟨0, p.pos⟩ := by
  simp only [rep]
  rw [dif_neg (by omega)]

/-- **Aux 2 (the inverse index lands in the initial segment).**  The frozen
phrase "viewing the returned index in the initial segment of `[S_n]`"
(line 851) as a checkable inequality. -/
theorem idx_val_lt (p : PadEnum X S) (x : X) :
    ((p.idx x : Fin S) : ℕ) < Fintype.card X := (p.enum.symm x).isLt

/-- **The frozen round trip `pi_X . iota_X = id_{X_{n,I}}`** --
`13-iteration-assembly.tex:853--856`.

This is the identity the whole duplication argument rests on: it is what makes
the unpadded matrix a restriction of the padded one.  General in the carrier,
the enumeration datum and the element. -/
theorem rep_idx (p : PadEnum X S) (x : X) : p.rep (p.idx x) = x := by
  rw [p.rep_of_lt (p.idx x) (p.idx_val_lt x)]
  simp [idx]

/-- **Aux 3 (the partial inverse in the other order).**  On the initial
segment -- and only there -- the two maps are mutually inverse; beyond it the
fallback destroys the information, which is exactly the duplication.  General
in the carrier, the datum and the slot. -/
theorem idx_rep (p : PadEnum X S) (u : Fin S) (h : (u : ℕ) < Fintype.card X) :
    p.idx (p.rep u) = u := by
  rw [p.rep_of_lt u h]
  simp [idx]

/-- **`pi_X` is a surjection** -- the word "surjections" of frozen line 835,
made a theorem rather than a definition.

Statement pole: the trivial witness for a map `[S_n] -> X_{n,I}` is a constant
map, and a constant map fails surjectivity as soon as `|X_{n,I}| >= 2`; the
pinned witness `witnessRows` has `|X| = 3`, so this is not a statement every
map satisfies.  General in the carrier and the datum.

`surjectivityField_would_be_redundant` records that adding this as a `PadEnum`
field would restate a derived telescope (`M4`). -/
theorem rep_surjective (p : PadEnum X S) : Function.Surjective p.rep :=
  fun x => ⟨p.idx x, p.rep_idx x⟩

/-- **Aux 4 (`iota_X` is injective).**  Immediate from the round trip, and the
reason "restricting to `iota_X(X) x iota_Y(Y)`" (frozen line 866) recovers the
whole unpadded matrix rather than a quotient of it. -/
theorem idx_injective (p : PadEnum X S) : Function.Injective p.idx :=
  Function.LeftInverse.injective p.rep_idx

/-- **Aux 5 (a slot carries an original row exactly when it is inside the
enumeration).**  The exact frontier between original and duplicated slots,
which is what turns the frozen sentence of lines 857--858 into a count. -/
theorem mem_range_iff (p : PadEnum X S) (u : Fin S) :
    (∃ x, p.idx x = u) ↔ (u : ℕ) < Fintype.card X := by
  constructor
  · rintro ⟨x, rfl⟩
    exact p.idx_val_lt x
  · intro h
    refine ⟨p.enum ⟨(u : ℕ), h⟩, ?_⟩
    simp [idx]

/-- **The duplicated slots of `step:I-11`** -- the slots of `[S_n]` that carry
no original row (respectively column), i.e. those "filled by duplicates" in
the sense of `13-iteration-assembly.tex:857--858`.

Claims no reader item; the reader gives no count. -/
def duplicateSlots (p : PadEnum X S) : Finset (Fin S) :=
  Finset.univ.filter fun u => ¬ (∃ x, p.idx x = u)

/-- **Aux 6 (the duplicated slots are exactly the tail slots).**  General in
the carrier, the datum and `S`. -/
theorem duplicateSlots_eq (p : PadEnum X S) :
    p.duplicateSlots = Finset.univ.filter fun u : Fin S => Fintype.card X ≤ (u : ℕ) := by
  ext u
  simp only [duplicateSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [p.mem_range_iff u]
  omega

/-- **"Precisely `S_n - |X_{n,I}|` row slots ... are filled by duplicates"**
-- `13-iteration-assembly.tex:857--858`, with `precisely` read as an equality
of cardinalities and not as a bound.

General in the carrier, the enumeration datum and `S`.  Claims no reader item.
-/
theorem duplicateSlots_card (p : PadEnum X S) :
    p.duplicateSlots.card = S - Fintype.card X := by
  have himg : (Finset.univ.filter fun u : Fin S => (u : ℕ) < Fintype.card X)
      = Finset.image (Fin.castLE p.fits) Finset.univ := by
    ext u
    constructor
    · intro hu
      have h : (u : ℕ) < Fintype.card X := by simpa using hu
      refine Finset.mem_image.mpr ⟨⟨(u : ℕ), h⟩, Finset.mem_univ _, ?_⟩
      simp
    · intro hu
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hu
      simp [Fin.castLE]
  have hcard : (Finset.univ.filter fun u : Fin S => (u : ℕ) < Fintype.card X).card
      = Fintype.card X := by
    rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective p.fits)]
    simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin S)))
    (p := fun u : Fin S => (u : ℕ) < Fintype.card X)
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  have hdup : p.duplicateSlots.card
      = (Finset.univ.filter fun u : Fin S => ¬ ((u : ℕ) < Fintype.card X)).card := by
    rw [p.duplicateSlots_eq]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  omega

end PadEnum

/-! ## Part 2: the common square and the padded matrix -/

set_option linter.dupNamespace false in
/-- **The common padding datum of `step:I-11`**
(`13-iteration-assembly.tex:809--864`).

The single parameter `S` shared by both sides is the whole content of the word
*common* in "one common square exponent" (frozen headline, line 811) and in
"Because `e(n)` and `S_n` depend only on `n`, every source instance with that
size parameter has the same square dimensions" (frozen lines 883--884); in
Lean that last sentence is enforced by the **type**, since the padded matrix
below has index type `Fin S` with `S` independent of the carriers.

Constructor data only (`M4`): two enumeration data.  No matrix, no protocol,
no complexity value, no certificate.  Claims no reader item. -/
structure CommonPadding (X : Type u) (Y : Type v) [Fintype X] [Fintype Y]
    (S : ℕ) where
  /-- The row-side enumeration datum, `e_X` with its two side conditions. -/
  rows : PadEnum X S
  /-- The column-side enumeration datum, `e_Y` with its two side conditions. -/
  cols : PadEnum Y S

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] {S : ℕ} {Z : Type w}

/-- **The padded square matrix** -- `13-iteration-assembly.tex:860--864`,

```
R^_n(I)(u,v) = R_k(I)(pi_X(u), pi_Y(v))     (u, v in [S_n]).
```

Both index types are `Fin S`: the matrix is square by construction, which is
the frozen "padded square matrix".  The output type is arbitrary (reading note
N3); the frozen Boolean case is `Z = Bool`.

Reader counterpart: `06-eth.tex:330`,
`R^_n(u,v) = R_{L(n)}(u^flat, v^flat)`. -/
def paddedMatrix (C : CommonPadding X Y S) (R : X → Y → Z) : Fin S → Fin S → Z :=
  fun u v => R (C.rows.rep u) (C.cols.rep v)

/-- **Aux 7 (the defining equation of the padded matrix).**  General in
everything; recorded so that consumers never unfold `paddedMatrix` by hand. -/
theorem paddedMatrix_apply (C : CommonPadding X Y S) (R : X → Y → Z)
    (u v : Fin S) : paddedMatrix C R u v = R (C.rows.rep u) (C.cols.rep v) := rfl

/-- **"Restricting `R^_n(I)` to `iota_X(X_{n,I}) x iota_Y(Y_{n,I})` recovers
`R_k(I)`"** -- `13-iteration-assembly.tex:865--866`.

The restriction is written as the composite rather than as a set-theoretic
restriction, which is the same statement and is the form the two complexity
directions consume.  General in the carriers, the padding datum, the output
type and the matrix.

Reader counterpart: `06-eth.tex:332--333`, "The original matrix is the
restriction to the first `m` rows and first `r` columns". -/
theorem paddedMatrix_restrict (C : CommonPadding X Y S) (R : X → Y → Z)
    (x : X) (y : Y) :
    paddedMatrix C R (C.rows.idx x) (C.cols.idx y) = R x y := by
  simp only [paddedMatrix, PadEnum.rep_idx]

/-- **Aux 8 (the two duplicate-slot counts of the common square).**  The frozen
sentence of lines 857--858 for both sides at once, at the one common `S`.
General in the carriers and the padding datum. -/
theorem duplicateSlot_counts (C : CommonPadding X Y S) :
    C.rows.duplicateSlots.card = S - Fintype.card X ∧
      C.cols.duplicateSlots.card = S - Fintype.card Y :=
  ⟨C.rows.duplicateSlots_card, C.cols.duplicateSlots_card⟩

/-! ## Part 3: preservation of deterministic communication complexity -/

/-- **Route-named facade for the vendored precomposition principle.**

`Workspace.ProofLemmas.SublemmaPrecompNoIncrease`
(`vendor/npc-cc/Workspace/ProofLemmas/SublemmaPrecompNoIncrease.lean`), which
is kernel-checked in the frozen vendored tree and is consumed here through the
`LegacyNPCC.Core` facade.  It is the formal content of frozen line 869 --
"Alice locally computes `pi_X(u)`, Bob locally computes `pi_Y(v)`, and they
run an optimal protocol" -- for arbitrary local maps: precomposing each
party's input with a local map transports a protocol at the same cost, so the
complexity does not increase.

Inherited, not re-proved; re-exported under a route name so that the two
directions below read as the frozen argument (reading note N2). -/
theorem precomposition_no_increase {A B A' B' : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (g : A → B → Z) (α : A' → A) (β : B' → B) :
    D (fun u v => g (α u) (β v)) ≤ D g :=
  Workspace.ProofLemmas.SublemmaPrecompNoIncrease g α β

/-- **The restriction direction** -- `13-iteration-assembly.tex:865--868`:
"Restricting `R^_n(I)` to `iota_X(X_{n,I}) x iota_Y(Y_{n,I})` recovers
`R_k(I)`.  Therefore every protocol for `R^_n(I)` restricts to one for
`R_k(I)`, and `D(R_k(I)) <= D(R^_n(I))`."

The restriction of a protocol is precomposition along `iota_X`, `iota_Y`,
followed by the frozen round trip (`paddedMatrix_restrict`).  General in the
carriers, the padding datum, the output type and the matrix.  Claims no reader
item; the reader compresses both directions into one sentence, which is
assigned to `padded_le_complexity`. -/
theorem complexity_le_padded (C : CommonPadding X Y S) (R : X → Y → Z) :
    D R ≤ D (paddedMatrix C R) := by
  have h := precomposition_no_increase (paddedMatrix C R) C.rows.idx C.cols.idx
  have hfun : (fun x y => paddedMatrix C R (C.rows.idx x) (C.cols.idx y)) = R := by
    funext x y
    exact paddedMatrix_restrict C R x y
  rwa [hfun] at h

/-- **The local-computation direction** --
`13-iteration-assembly.tex:868--872`: "Conversely, on input `(u,v)`, Alice
locally computes `pi_X(u)`, Bob locally computes `pi_Y(v)`, and they run an
optimal protocol for `R_k(I)`.  This uses no communication beyond that
protocol, so `D(R^_n(I)) <= D(R_k(I))`."

Precomposition along `pi_X`, `pi_Y`; "uses no communication beyond that
protocol" is the cost-preservation half of the vendored principle.  General in
the carriers, the padding datum, the output type and the matrix.

Reader counterpart: `06-eth.tex:333--334`, "while a protocol for it computes
every duplicate after the parties apply the two fallback maps locally". -/
theorem padded_le_complexity (C : CommonPadding X Y S) (R : X → Y → Z) :
    D (paddedMatrix C R) ≤ D R :=
  precomposition_no_increase R C.rows.rep C.cols.rep

/-- **`expi:E-11-D`** -- `13-iteration-assembly.tex`, label line 875, display
lines 873--876:

```
D(R^_n(I)) = D(R_k(I)).
```

An **equality**, as the frozen display writes it, obtained from the two frozen
directions in the frozen order (reading note N1); neither one-sided form is
landed as the headline.

Frozen lines 878--882 fix the scope of this transport and are honoured:
padding runs only after the last unpadded level, and **no** claim is made that
duplication preserves the density-sensitive robustness certificate
(GAP-EXPOSED 2, with `paddingDestroysRowDistinctness` showing the boundary is
real).

General in the carriers, the padding datum, the output type and the matrix.

Reader counterpart: `eq:paper-padding-invariance` (`06-eth.tex`, label line
338, display lines 336--337). -/
theorem paddedComplexity (C : CommonPadding X Y S) (R : X → Y → Z) :
    D (paddedMatrix C R) = D R :=
  le_antisymm (padded_le_complexity C R) (complexity_le_padded C R)

/-! ## Part 4: the padding at the frozen common square exponent -/

/-- **"Then `g(n) <= e(n)`, so both carriers have at most `S_n` elements"** --
`13-iteration-assembly.tex:815--825`, consuming the banked
`commonSizeParameters` for `g(n) <= e(n)`.

The hypothesis `|X| <= 2^{g(n)}` is the frozen display of lines 816--818,
which comes from `step:I-07` and the definition of `g`; neither is landed in
this module, so it stays a **named hypothesis** (GAP-EXPOSED 4).  General in
the clock, the source size and the carrier.

Reader counterpart: `06-eth.tex:322`, "Both carrier sizes of every branch
output are at most `2^{g(n)}`". -/
theorem carrierFitsCommonSquare (V : ℕ → ℕ) (n : ℕ)
    (hX : Fintype.card X ≤ 2 ^ gMaj V n) :
    Fintype.card X ≤ sCommon V n := by
  have hge : gMaj V n ≤ eCommon V n := (commonSizeParameters V n).1
  have : (2 : ℕ) ^ gMaj V n ≤ 2 ^ eCommon V n :=
    Nat.pow_le_pow_right (by norm_num) hge
  simpa [sCommon] using le_trans hX this

/-- **The "definition of `g`" half of frozen line 815**
(`13-iteration-assembly.tex:815`, "Step~`step:I-07` and the definition of `g`
give ...", with `eq:uniform-size-majorant`,
`12-iteration-specification.tex`, label line 597).

`g` is the prefix maximum `max_{1 <= m <= n} zhat(m)`, so a carrier bound
stated at the **pointwise** majorant `zhat(n)` -- which is the form
`step:I-07` delivers at the single source size `n` -- lifts to the prefix
maximum and then to the common square.  The banked `gMaj_spec` is what does
the lifting, and its frozen lower index guard `1 <= n` is live here rather
than dropped: the fold starts at `m = 1`, so `gMaj V 0` claims nothing about
`zhat V 0`.

General in the clock, the source size `n >= 1` and the carrier.  Claims no
reader item: the reader compresses this to line 322, which is
`carrierFitsCommonSquare`'s item. -/
theorem carrierFitsCommonSquare_of_zhat (V : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hX : Fintype.card X ≤ 2 ^ zhat V n) :
    Fintype.card X ≤ sCommon V n := by
  have hmaj : zhat V n ≤ gMaj V n := (gMaj_spec V).1 n n hn le_rfl
  refine carrierFitsCommonSquare V n (le_trans hX ?_)
  exact Nat.pow_le_pow_right (by norm_num) hmaj

/-- **The row (or column) enumeration datum at the frozen `S_n`** --
`13-iteration-assembly.tex:820--825` with `eq:common-size`
(`12-iteration-specification.tex`, label line 628).

Nothing is invented: `enum` and `pos` are the frozen enumeration and the
frozen nonemptiness of line 848, the frozen size bound is the named hypothesis
`hX`, and the fitting field is `carrierFitsCommonSquare`.  General in the
clock, the source size, the carrier and the enumeration.  Claims no reader
item. -/
def frozenPadEnum (V : ℕ → ℕ) (n : ℕ) (e : Fin (Fintype.card X) ≃ X)
    (hpos : 0 < Fintype.card X) (hX : Fintype.card X ≤ 2 ^ gMaj V n) :
    PadEnum X (sCommon V n) where
  enum := e
  pos := hpos
  fits := carrierFitsCommonSquare V n hX

/-- **The common padding at the frozen common square exponent** --
`step:I-11` instantiated at `S = S_n = sCommon V n` of `eq:common-size`.

Both sides receive the **same** `S_n`, and `S_n` depends only on the clock and
`n`, which is the frozen sentence of lines 883--884 read off the type.
General in the clock, the source size, both carriers, both enumerations and
both size bounds.  Claims no reader item. -/
def frozenCommonPadding (V : ℕ → ℕ) (n : ℕ)
    (eX : Fin (Fintype.card X) ≃ X) (eY : Fin (Fintype.card Y) ≃ Y)
    (hXpos : 0 < Fintype.card X) (hYpos : 0 < Fintype.card Y)
    (hX : Fintype.card X ≤ 2 ^ gMaj V n) (hY : Fintype.card Y ≤ 2 ^ gMaj V n) :
    CommonPadding X Y (sCommon V n) where
  rows := frozenPadEnum V n eX hXpos hX
  cols := frozenPadEnum V n eY hYpos hY

/-- **`expi:E-11-D` at the frozen common square exponent.**

The frozen transport, at the frozen `S_n`, on the frozen hypotheses -- which
is the form `step:I-11` is consumed in by the final gap (frozen lines
881--882, "Since no further level is run, `expi:E-11-D` is exactly the
transport required for the final gap").  General in the clock, the source
size, both carriers, both enumerations, both size bounds, the output type and
the matrix.  Claims no reader item; the reader statement is
`eq:paper-padding-invariance`, which `paddedComplexity` carries. -/
theorem frozenPaddedComplexity (V : ℕ → ℕ) (n : ℕ)
    (eX : Fin (Fintype.card X) ≃ X) (eY : Fin (Fintype.card Y) ≃ Y)
    (hXpos : 0 < Fintype.card X) (hYpos : 0 < Fintype.card Y)
    (hX : Fintype.card X ≤ 2 ^ gMaj V n) (hY : Fintype.card Y ≤ 2 ^ gMaj V n)
    (R : X → Y → Z) :
    D (paddedMatrix (frozenCommonPadding V n eX eY hXpos hYpos hX hY) R) = D R :=
  paddedComplexity _ R

/-- **"Its length depends only on `n`"** --
`12-iteration-specification.tex:635--636`, with `T_n = S_n^2` of
`eq:common-size` (label line 628).

The entry count of the padded matrix at the frozen square exponent is exactly
the banked `tCommon V n`, for **every** instance: the right-hand side mentions
neither carrier.  This is the first statement in the route about the entry
count of an actual matrix; the banked `commonSizeParameters` states
`T_n = 2^{2 e(n)}` about the numbers only, and that identity is not restated
here (GAP-EXPOSED 5).

General in the clock and the source size.  Reader counterpart:
`06-eth.tex:340--341`, "every branch has the same truth-table length `T_n`".
-/
theorem frozenPaddedEntryCount (V : ℕ → ℕ) (n : ℕ) :
    Fintype.card (Fin (sCommon V n) × Fin (sCommon V n)) = tCommon V n := by
  simp [tCommon, pow_two]

/-! ## Part 5: non-vacuity, statement poles, and refuted candidates -/

/-- **A nondegenerate row datum at legal parameter values** (LANE-GATE 3).

`|X| = 3`, `S = 4`.  Legal: `S_n = 2^{e(n)}` is a power of two and `4 = 2^2`,
and the frozen constraint on the carrier is `|X| <= S_n`, satisfied strictly.
Nondegenerate in the sense that matters here: the inequality is **strict**, so
the fallback branch of `rep` is actually taken and the padding really
duplicates -- see `witnessRows_rep_not_injective` and
`witnessRows_duplicate_card`.  A datum with `|X| = S` would compile green and
exercise nothing. -/
def witnessRows : PadEnum (Fin 3) 4 where
  enum := finCongr (by simp)
  pos := by simp
  fits := by simp

/-- **A nondegenerate column datum at legal parameter values**, `|Y| = 2`,
`S = 4`, strictly below the common square side, and of a **different** size
from the row side, so that the two duplicate counts are genuinely different
numbers. -/
def witnessCols : PadEnum (Fin 2) 4 where
  enum := finCongr (by simp)
  pos := by simp
  fits := by simp

/-- **A nondegenerate inhabitant of `CommonPadding` at legal parameter
values** (LANE-GATE 3): one common `S = 4` over two carriers of different
sizes, both strictly smaller than `S`. -/
def witnessPadding : CommonPadding (Fin 3) (Fin 2) 4 where
  rows := witnessRows
  cols := witnessCols

/-- **The premise bundle of every theorem in Parts 2--3 is inhabited at legal
values** (hypothesis-consistency gate).  `CommonPadding` is the only bundle
those theorems take, and it is inhabited, so no `False` is derivable from
their hypotheses. -/
theorem commonPadding_hypotheses_consistent :
    Nonempty (CommonPadding (Fin 3) (Fin 2) 4) := ⟨witnessPadding⟩

/-- **The duplication is real on both sides**: at the pinned witness exactly
one row slot and exactly two column slots are filled by duplicates, matching
`S - |X| = 4 - 3` and `S - |Y| = 4 - 2` of frozen lines 857--858. -/
theorem witnessPadding_duplicate_card :
    witnessRows.duplicateSlots.card = 1 ∧ witnessCols.duplicateSlots.card = 2 := by
  constructor
  · rw [witnessRows.duplicateSlots_card]; simp
  · rw [witnessCols.duplicateSlots_card]; simp

/-- **The representative map is genuinely non-injective at legal values.**

This refutes the tempting encoding in which `pi_X` is asked to be a bijection
`[S_n] ~= X_{n,I}`: the frozen map is a *surjection* with a fallback branch,
and demanding a bijection would force `S_n = |X_{n,I}|`, which the frozen
construction never has.  A structure demanding that would be inhabited only at
degenerate parameter values. -/
theorem witnessRows_rep_not_injective : ¬ Function.Injective witnessRows.rep := by
  intro h
  have h3 : witnessRows.rep (3 : Fin 4) = witnessRows.enum ⟨0, witnessRows.pos⟩ :=
    witnessRows.rep_of_ge 3 (by simp)
  have h0 : witnessRows.rep (0 : Fin 4) = witnessRows.enum ⟨0, witnessRows.pos⟩ := by
    rw [witnessRows.rep_of_lt 0 (by simp)]
    norm_num
  have : (3 : Fin 4) = (0 : Fin 4) := h (by rw [h3, h0])
  exact absurd this (by decide)

/-- **A genuinely non-constant Boolean matrix on the pinned carriers**, used to
exercise the padding transport on something the trivial matrix would not
distinguish. -/
def witnessMatrix : Fin 3 → Fin 2 → Bool := fun x y => decide ((x : ℕ) = (y : ℕ))

/-- **`expi:E-11-D` fires on the pinned nondegenerate instance**: a
`4 x 4` padded matrix built from a `3 x 2` matrix by real duplication on both
sides has exactly the deterministic communication complexity of the original.
This is the headline instantiated where duplication genuinely occurs, not at a
padding that changes nothing. -/
theorem witnessPadding_preserves_complexity :
    D (paddedMatrix witnessPadding witnessMatrix) = D witnessMatrix :=
  paddedComplexity witnessPadding witnessMatrix

/-- **The frozen common square strictly exceeds a singleton carrier, for every
clock and every source size.**

`e(n) = g(n) + ceil(log_2(n+2)) >= 1`, so `S_n >= 2`.  Hence the frozen
padding at `S_n` is never the empty padding for a small carrier: at least one
slot is a duplicate.  This inhabits the `Part 4` construction at the genuine
frozen parameters rather than at an invented `S`. -/
theorem two_le_sCommon (V : ℕ → ℕ) (n : ℕ) : 2 ≤ sCommon V n := by
  have hclog : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by norm_num) (by omega)
  have h1 : 1 ≤ eCommon V n := by
    simp only [eCommon]
    omega
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ eCommon V n := Nat.pow_le_pow_right (by norm_num) h1
    _ = sCommon V n := rfl

/-- **The frozen construction of Part 4 is inhabited at the genuine frozen
parameters, with real duplication** (LANE-GATE 3 at the frozen values).

A one-element carrier satisfies the frozen size bound `|X| <= 2^{g(n)}` for
every clock and every `n`, and `two_le_sCommon` makes the fitting inequality
strict, so `S_n - |X| >= 1` slots are duplicates.  The premise bundle of
`frozenPaddedComplexity` is therefore consistent at the frozen side
conditions, for every `V` and every `n`.

Statement pole: the trivial witness for "there is a common padding" is one
with `S = |X| = |Y|`, which duplicates nothing; it fails the second conjunct,
since its duplicate-slot count is `0`.  That conjunct is exactly what stops
this existential from being satisfiable by a padding that pads nothing. -/
theorem frozenCommonPadding_inhabited_nondegenerate (V : ℕ → ℕ) (n : ℕ) :
    ∃ C : CommonPadding (Fin 1) (Fin 1) (sCommon V n),
      1 ≤ C.rows.duplicateSlots.card := by
  have hpos : 0 < Fintype.card (Fin 1) := by simp
  have hle : Fintype.card (Fin 1) ≤ 2 ^ gMaj V n := by
    simpa using Nat.one_le_two_pow
  refine ⟨frozenCommonPadding V n (finCongr (by simp)) (finCongr (by simp))
    hpos hpos hle hle, ?_⟩
  have hcard := (frozenPadEnum V n (X := Fin 1) (finCongr (by simp))
    hpos hle).duplicateSlots_card
  have h2 := two_le_sCommon V n
  simp only [Fintype.card_fin] at hcard
  change 1 ≤ (frozenPadEnum V n (X := Fin 1) (finCongr (by simp)) hpos hle
    ).duplicateSlots.card
  omega

/-- **Refuted candidate 1: the reader's one-based guard is not the frozen
guard.**

The reader writes the fallback as `u^flat = u` when `u <= m`
(`06-eth.tex:326`), in the one-based convention `[d] = {1, ..., d}` of the
reader's preliminaries.  Transcribing that guard literally into the zero-based
slots of `conv:finite-slots` is out of range: at `|X| = 1` and `S = 2` the
slot `u = 1` satisfies `u <= |X|` and is **not** a legal index of the
enumeration.  The frozen autoformalization guard at lines 842--846 is the
strict `u < |X|`, and that is what `rep` uses. -/
theorem oneBasedGuard_is_not_the_frozen_guard :
    ¬ ∀ (c S : ℕ) (u : Fin S), c ≤ S → (u : ℕ) ≤ c → (u : ℕ) < c := by
  intro h
  have := h 1 2 ⟨1, by norm_num⟩ (by norm_num) (by norm_num)
  simp at this

/-- **Refuted candidate 2: padding does not preserve density-sensitive
properties.**

Frozen lines 878--882 restrict the transport to communication complexity and
say explicitly that the argument "makes no claim that duplication preserves
the density-sensitive robustness certificate needed as input to another
level".  That restriction is not decorative: the pinned witness has pairwise
distinct rows, and its padded version does not, because slot `3` is a
duplicate of slot `0`.  Any encoding that let a certificate ride through the
padding would be refuted by this pair. -/
theorem paddingDestroysRowDistinctness :
    Function.Injective witnessMatrix ∧
      ¬ Function.Injective (paddedMatrix witnessPadding witnessMatrix) := by
  refine ⟨by decide, ?_⟩
  intro h
  have h3 : witnessPadding.rows.rep (3 : Fin 4)
      = witnessPadding.rows.enum ⟨0, witnessPadding.rows.pos⟩ :=
    witnessPadding.rows.rep_of_ge 3 (by simp)
  have h0 : witnessPadding.rows.rep (0 : Fin 4)
      = witnessPadding.rows.enum ⟨0, witnessPadding.rows.pos⟩ := by
    rw [witnessPadding.rows.rep_of_lt 0 (by simp)]
    norm_num
  have hrow : paddedMatrix witnessPadding witnessMatrix (3 : Fin 4)
      = paddedMatrix witnessPadding witnessMatrix (0 : Fin 4) := by
    funext v
    simp only [paddedMatrix, h3, h0]
  exact absurd (h hrow) (by decide)

/-- **`M4` check: surjectivity of `pi_X` would be a redundant field.**

`rep_surjective` derives it from `enum`, `pos` and `fits`, so adding it to
`PadEnum` would restate a derived telescope, exactly as
`persistence_field_would_be_redundant` records for the clock module. -/
theorem surjectivityField_would_be_redundant (p : PadEnum X S) :
    Function.Surjective p.rep := p.rep_surjective

/-- **The rejected candidate's decisive lemma, kept in the kernel.**

Candidate B parameterized the enumeration by an independent length `m`.  That
parameter is forced: any `Fin m ~= X` over a `Fintype` has `m = Fintype.card X`.
So candidate B's extra binder buys nothing and costs a transport at every use
site, which is why candidate A is landed. -/
theorem padEnumLengthIsForced {m : ℕ} (e : Fin m ≃ X) : m = Fintype.card X := by
  simpa using Fintype.card_congr e

/-! ## Part 6: hypothesis consistency at a banked route object

Parts 2--4 are consistent at the toy carriers of Part 5, but a toy carrier does
not answer the question the hypothesis-consistency gate actually asks: can the
premise bundle of `frozenPaddedComplexity` -- both frozen carrier bounds, both
nonemptiness facts, the frozen `S_n`, and a matrix the route has actually
built -- hold *simultaneously*?  Part 6 answers it by instantiating the frozen
padding at the only matrix this repository has both built and computed a
deterministic communication complexity for: the banked full cube `fullCube` of
`OneLevelCompletion.lean`.

**Scope, stated before the declarations, so no consumer can over-read them.**
`fullCube` is banked under `SEED-001` as a **depth-zero instance of the
autoformalization `def:robust-seed` only**, never as `lem:full-cube-seed`
(whose minimality rule is stated for requested depth `b >= 1`,
`12-iteration-specification.tex:16`).  Nothing below reads it as that lemma:
the only property of `fullCube` used is `fullCube_D_eq`, whose content is the
depth-free `comp F = a + 1` under the frozen sandwich `2^{a-1} < q <= 2^{a}`.
No robustness, no bracket, no `Lambda`, no requested depth and no seed
interface enters Part 6, which is also why nothing here contradicts
GAP-EXPOSED 2 -- `step:I-11` still transports `D` and nothing else. -/

/-- **The frozen common padding of `step:I-11`, applied to the carriers of the
banked full cube.**

Rows are the cube `Fin q -> Bool` (`2^q` of them) and columns are the
coordinate index `Fin q`, which are the carriers of
`OneLevelCompletion.fullCube q`.  Both frozen carrier bounds of
`13-iteration-assembly.tex:816--818` are named hypotheses here exactly as they
are in `frozenCommonPadding` (GAP-EXPOSED 4); the enumerations are arbitrary
(GAP-EXPOSED 3), so `Fintype.equivFin` is used and nothing is claimed about the
canonical order.  Claims no reader item. -/
noncomputable def seedPadding (V : ℕ → ℕ) (n q : ℕ) (hq : 1 ≤ q)
    (hX : (2 : ℕ) ^ q ≤ 2 ^ gMaj V n) (hY : q ≤ 2 ^ gMaj V n) :
    CommonPadding (Fin q → Bool) (Fin q) (sCommon V n) :=
  frozenCommonPadding V n
    (Fintype.equivFin (Fin q → Bool)).symm (Fintype.equivFin (Fin q)).symm
    Fintype.card_pos (by simpa using hq)
    (by simpa using hX) (by simpa using hY)

/-- **`expi:E-11-D` on a matrix the route has actually built.**

Padding the banked full cube to the frozen common square `S_n` leaves its
deterministic communication complexity at the banked value `a + 1`.  This is
`paddedComplexity` composed with `OneLevelCompletion.fullCube_D_eq`, so it
uses **only** the depth-free half of the seed record (see the Part 6 scope
note): `fullCube` is consumed here as a depth-zero instance of
`def:robust-seed`, never as `lem:full-cube-seed`.

General in the clock, the source size, the cube width `q` and the exponent `a`
under the frozen sandwich.  Claims no reader item. -/
theorem seedPadding_D (V : ℕ → ℕ) (n q a : ℕ) (ha : 1 ≤ a)
    (hlo : 2 ^ (a - 1) < q) (hhi : q ≤ 2 ^ a) (hq : 1 ≤ q)
    (hX : (2 : ℕ) ^ q ≤ 2 ^ gMaj V n) (hY : q ≤ 2 ^ gMaj V n) :
    D (paddedMatrix (seedPadding V n q hq hX hY)
        (EthInapproximability.ParameterizedNP.OneLevelCompletion.fullCube q))
      = a + 1 := by
  rw [paddedComplexity]
  exact EthInapproximability.ParameterizedNP.OneLevelCompletion.fullCube_D_eq
    q a ha hlo hhi

/-- **The clock of the consistency witness.**  A constant gate `V k = 2` is
never feasible at source size `n = 1`, so `slowIndex` takes its frozen
zero value and `zhat` its frozen seed branch.  This is a witness clock, not a
route object: no `SlowClockGateSet` is claimed for it. -/
def witnessClock : ℕ → ℕ := fun _ => 2

/-- The witness clock has slow index `0` at `n = 1`: no `k` in the frozen
search range satisfies `V k <= n`. -/
theorem witnessClock_slowIndex : slowIndex witnessClock 1 = 0 := by
  rw [slowIndex, Nat.findGreatest_eq_zero_iff]
  intro m _ _
  simp [witnessClock]

/-- **The witness clock's size majorant clears the frozen seed floor.**

At `n = 1` the majorant is the seed value `z_seed(1) = q_seed(1) + a_seed(1)`,
and the banked `aSeed_spec` forces `2^{a_seed(1)} >= 66`, hence
`q_seed(1) >= 64` and `z_seed(1) >= 67`.  Only the floor is needed below. -/
theorem witnessClock_gMaj : 67 ≤ gMaj witnessClock 1 := by
  have hz : zhat witnessClock 1 = zSeed 1 := by
    rw [zhat, if_pos witnessClock_slowIndex]
  obtain ⟨h3, hsize⟩ := aSeed_spec 1
  have hq : 64 ≤ qSeed 1 := by
    have : (66 : ℕ) ≤ 2 ^ aSeed 1 := le_trans (by omega) hsize
    simp only [qSeed]
    omega
  have hg : gMaj witnessClock 1 = zhat witnessClock 1 := by
    simp [gMaj]
  rw [hg, hz, zSeed]
  omega

/-- The row-side frozen carrier bound of the witness: `|X| = 2^2 <= 2^{g(1)}`. -/
theorem witnessClock_rows_fit : (2 : ℕ) ^ 2 ≤ 2 ^ gMaj witnessClock 1 :=
  Nat.pow_le_pow_right (by norm_num) (by have := witnessClock_gMaj; omega)

/-- The column-side frozen carrier bound of the witness: `|Y| = 2 <= 2^{g(1)}`. -/
theorem witnessClock_cols_fit : (2 : ℕ) ≤ 2 ^ gMaj witnessClock 1 := by
  have h := witnessClock_rows_fit
  omega

/-- **The pinned consistency instance**: the frozen `step:I-11` padding of the
banked full cube of width `2`, at the genuine frozen common square
`S_1 = sCommon witnessClock 1`.

Named rather than existential (statement pole): an existential "there is a
common padding of the cube" is satisfied by the padding with
`S = |X| = |Y|`, which duplicates nothing and transports nothing interesting.
`witnessSeedPadding_duplicates` is stated about **this** construction, at the
frozen `S_n`, so that trivial witness is not available. -/
noncomputable def witnessSeedPadding :
    CommonPadding (Fin 2 → Bool) (Fin 2) (sCommon witnessClock 1) :=
  seedPadding witnessClock 1 2 (by norm_num)
    witnessClock_rows_fit witnessClock_cols_fit

/-- **The whole premise bundle of Part 4 is consistent at a banked route
object.**

`fullCube 2` satisfies the frozen sandwich at `a = 1` (`2^0 = 1 < 2 <= 2^1`),
so the padded cube has deterministic communication complexity `2` -- the banked
value of the unpadded cube, transported by `expi:E-11-D`.  No `False` follows
from the hypotheses of `frozenPaddedComplexity`: they are all discharged here
simultaneously, at the frozen `S_n` of a clock, on a matrix the route built. -/
theorem witnessSeedPadding_D :
    D (paddedMatrix witnessSeedPadding
        (EthInapproximability.ParameterizedNP.OneLevelCompletion.fullCube 2))
      = 2 :=
  seedPadding_D witnessClock 1 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) witnessClock_rows_fit witnessClock_cols_fit

/-- **The consistency instance genuinely duplicates.**

`|X| = 4` while `S_1 = 2^{e(1)} >= 2^{67}`, so at least one row slot -- in fact
almost all of them -- carries a duplicate.  This is what rules out reading
`witnessSeedPadding_D` as a statement about a padding that pads nothing. -/
theorem witnessSeedPadding_duplicates :
    1 ≤ witnessSeedPadding.rows.duplicateSlots.card := by
  have hcard := witnessSeedPadding.rows.duplicateSlots_card
  have hX : Fintype.card (Fin 2 → Bool) = 4 := by simp
  have hS : (8 : ℕ) ≤ sCommon witnessClock 1 := by
    have hg := witnessClock_gMaj
    have h1 : 3 ≤ eCommon witnessClock 1 := by
      simp only [eCommon]
      omega
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ eCommon witnessClock 1 := Nat.pow_le_pow_right (by norm_num) h1
      _ = sCommon witnessClock 1 := rfl
  omega

end EthInapproximability.ParameterizedNP.CommonPadding
