import EthInapproximability.ParameterizedNP.DefectInduction

/-!
# Parameterized NP route: the two-copy ladder step of the direct bridge

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-TWOCOPY-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, line 112),
opened by the `cc-t1d` statement gate as the one step that
`BRIDGE-DEFECT-001` currently carries as the unproved binder `hTwoCopy`.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`:
  * `eq:direct-input` (label line 11), **second clause** at line 10 —
    `Λ_W(1, θ, y) ≥ C_W - 1`;
  * the applicability sentence at lines 19--21, "Whenever `C_W ≥ 3` and
    `2θ ≤ 1`, the complete guard list in §Preliminaries makes the inherited
    two-copy ladder applicable to the second clause of `eq:direct-input`,
    giving";
  * `eq:direct-two-copy` (label line 24) — the deliverable
    `Λ_W(2, 2θ, y²) ≥ C_W`;
  * line 26, "Its bottom rung has complexity at least `C_W - 2`".
* `sections/03-preliminaries.tex`:
  * `def:lambda` (label line 224) — `Λ_M(p,x,z) = min_{j ∈ {0,1,2}}
    (j + comp⟨M,p,x,z/2^j⟩)`;
  * lines 234--240, the displayed unfolding of `Λ_M(1,x,y) ≥ H` into the three
    rungs `comp(y) ≥ H`, `comp(y/2) ≥ H-1`, `comp(y/4) ≥ H-2`;
  * lines 253--265, the integer-level specialization of the inherited ladder
    and the sentence "The lower bound `2 ≤ H` is the literal inherited guard
    `1 < H`, not an implicit consequence of the three-rung notation."
* `sections/D-inherited-contracts.tex`, paragraph "Checked inherited
  declaration: two-copy ladder" (line 317):
  * guards `eq:contract-two-copy-input` (label line 327);
  * conclusions `eq:contract-two-copy-output` (label line 336);
  * the substitution note at lines 338--340, "In the direct bridge the
    substitution is `H = C_W - 1`; the active assumption `C_W ≥ 3` proves this
    guard."

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex`,
`lem:bridge-base-estimates` (label line 31, statement lines 30--40): its
**first** inequality `Λ_W(2, 2θ, y²) ≥ C_W` of `eq:bridge-base-estimates`
(label line 38).  The file was opened and the item checked: it states the same
fact as `eq:direct-two-copy`, under the reader's hypotheses `C_W ≥ 3`,
`0 < θ ≤ 1/4`, and the second estimate of `eq:bridge-common-input` (label line
15, statement line 14, `Λ_W(1, θ, 3/5) ≥ C_W - 1`).  The reader lemma bundles
that inequality with the three-copy row step `D_W(3; 4θ, y²) ≥ C_W + 1`; only
the two-copy half is claimed here, exactly as `BRIDGE-TWOCOPY-001` records.
No other declaration in this development is assigned this reader item, and no
reader prose is cited as a statement.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **inherited** for `twoCopyLadder` (a re-export of the
  kernel-checked vendored `NPCC.two_copy_ladder`,
  `vendor/npc-cc/NPCC/Engine.lean:43`), and **new (elementary)** for
  `lambdaTwoCopy`, which is the frozen section's own two sentences at lines
  19--25: the `Λ`-unfolding of `def:lambda` in both directions around a single
  application of that declaration at `H = C_W - 1`.  No further
  communication-complexity lemma and no witness choice is introduced.
* Imports: `EthInapproximability.ParameterizedNP.DefectInduction` only, hence
  `InheritedContracts.lean` and `EthInapproximability.Prelude`, hence
  `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  `LegacyNPCC.Stage12` is **not** imported, so the AGHP balanced-family axiom
  is not in scope, and there is no contact with `EXPANDER-001` (which by design
  has no Lean declaration and would have to remain a named hypothesis).
* External adapters: none.  Nothing here is axiomatized; the inherited
  declaration is consumed, never re-proved and never widened.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

Two encodings of the derivation were written out before landing.

**Candidate A (landed).** Keep the paper's own `Λ` form on both sides:
hypothesis `C_W - 1 ≤ Λ_W(1, θ, y)` over `ℕ`, conclusion
`C_W ≤ Λ_W(2, 2θ, y²)` over `ℕ`, with the guards `3 ≤ C_W`, `0 < θ`,
`2θ ≤ 1`, `0 < y`, `y ≤ 1` spelled as the frozen lines 19 and 322 spell them,
and the ladder reached directly through `NPCC.two_copy_ladder` at
`H = (C_W : ℝ) - 1`.

**Candidate B (rejected).** Consume the vendored assembly
`EthBridge.two_copy_bundle_of_rungs` (`vendor/npc-cc/EthBridge/TwoCopySource.lean:632`),
whose conclusion `TwoCopyBundle W C x y` already unfolds to
`C ≤ LambdaGE W 2 (2x) (y²)`.  Its guard is `hC4 : 4 ≤ C`.  The frozen section
assumes only `C_W ≥ 3` (line 19, and `thm:direct-robustification` line 40), and
Appendix D lines 338--340 says explicitly that `C_W ≥ 3` is what proves the
`1 < H` guard.  Candidate B therefore silently strengthens the paper's
hypothesis by one bit — an over-strong hypothesis typechecks perfectly and a
green build would not see it.  It is disqualified by the aux battery: the
firing witness `lambdaTwoCopy_fires`, stated at the paper's own boundary value
`C_W = 3`, is **not provable** from `two_copy_bundle_of_rungs`.

Ranking (aux lemmas proved, faithfulness, length): A = 7/7 aux lemmas proved,
`Λ` on both sides exactly as `eq:direct-input` clause two and
`eq:direct-two-copy` write them, and it discharges the consumer's `hTwoCopy`
binder verbatim; B fails one aux lemma outright and is less faithful.  A landed.

## Faithfulness notes (mechanical rules M1--M10)

* `twoCopyLadder` restates the vendored type **verbatim**: the same binder
  order `f`, `hH`, `hx0`, `hx`, `hz0`, `hz1`, `h4`, `h2`, `h1`, the same real
  level `H`, the same `ℝ`-casts on all six complexity readouts, the same
  densities `z/4, z/2, z` in and `z²/4, z²/2, z²` out, and the same row scale
  `2x` out.  That is the exact printed content of
  `eq:contract-two-copy-input` and `eq:contract-two-copy-output`.
* `lambdaTwoCopy` writes the row guard as `2 * θ ≤ 1`, which is line 19's own
  spelling, not the contract's equivalent `θ ≤ 1/2`; the conversion is one
  `linarith` step inside the proof and is not pushed onto the caller.
* The level substitution is `H = C_W - 1` over `ℝ` (lines 338--339), never
  over `ℕ`: the hypothesis keeps the paper's `ℕ` subtraction `C_W - 1`, which
  is exact under `3 ≤ C_W`, and the cast to `(C_W : ℝ) - 1` is discharged once
  by `natCast_sub_one`.
* `Λ` is **not** redefined.  It is the vendored `NPCC.LambdaGE`
  (`Engine.lean:299`), which is literally `def:lambda`'s
  `min (comp z) (min (1 + comp (z/2)) (2 + comp (z/4)))`.  Introducing a second
  `Λ` would be a duplicate definition of a frozen quantity.
* No complexity or robustness conclusion is placed in constructor data: this
  module introduces **no structure and no premise bundle at all**, only
  theorems with explicit binders, so no derived telescope is restated as a
  field.
* Interlace widths are untouched: the copy counts here are the frozen `1` and
  `2` of `eq:direct-input` and `eq:direct-two-copy`; neither `q` nor `Q`
  appears.
* Trivial-conclusion pole.  The deliverable is a universally quantified
  implication, not an existential, so the pole is a vacuous conclusion rather
  than a trivial witness.  `C_W ≤ Λ_W(2, 2θ, y²)` would be free if the
  right-hand side were unconstrained; `lambdaTwoCopy_conclusion_nontrivial`
  proves the conclusion is **false** whenever the column alphabet is empty, so
  it is a real constraint on `W`.
* Vacuous-hypothesis pole.  `ladderInput_forces_nonempty_cols` proves the
  hypothesis is likewise false for an empty column alphabet, and
  `ladderInput_forces_top_rung` proves it already forces a two-bit lower bound
  on the top rung; so the premise genuinely constrains `W` and is not met by
  degenerate carriers.
* Non-vacuity of the parameters, and abstract quantification elsewhere.
  `lambdaTwoCopy_guards_legal` discharges every purely numeric guard at the
  route's own globally fixed values `θ = 1/4`, `y = 3/5` (`03-preliminaries.tex`
  lines 216--219) and at the boundary `C_W = 3`, and additionally records that
  the substituted level fails the inherited guard at `C_W = 2` — so `C_W ≥ 3`
  is necessary, exactly as line 338 says.  The **semantic** premise
  `Λ_W(1, θ, y) ≥ C_W - 1` has **no exhibited inhabitant** anywhere in this
  development, and none can be exhibited until Stages 1--4 land in Lean; it is
  therefore carried by abstract quantification over `X`, `Y`, `W`, and
  `lambdaTwoCopy_fires` is stated at universally quantified `X`, `Y`, `W` with
  only the numeric parameters pinned.

## GAP-EXPOSED

`eq:direct-input` itself is **not** discharged here: both of its clauses are
construction outputs of Sections 8--9 and remain named hypotheses.  The second
inequality of the reader's `lem:bridge-base-estimates`, the three-copy row step
`eq:direct-three-copy` (`10-direct-bridge.tex:31`), is **not** claimed, and
neither is `thm:direct-robustification` (line 35).  Nothing about route
completion is claimed.
-/

namespace EthInapproximability.ParameterizedNP.TwoCopyLadder

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction

/-! ## The re-exported inherited contract

`sections/D-inherited-contracts.tex:317`. -/

/-- **Checked inherited declaration: two-copy ladder.**

Route-named facade for `NPCC.two_copy_ladder`
(`vendor/npc-cc/NPCC/Engine.lean:43`), restating
`eq:contract-two-copy-input` (label line 327) and
`eq:contract-two-copy-output` (label line 336) of
`sections/D-inherited-contracts.tex` verbatim: a real level `H` with the guards
`1 < H`, `0 < x ≤ 1/2`, `0 < z ≤ 1` and the three one-copy rungs at densities
`z/4, z/2, z` and levels `H-2, H-1, H`, concluding the three two-copy rungs at
row scale `2x`, densities `z²/4, z²/2, z²`, and levels `H-1, H, H+1`.

The vendored declaration is *consumed*: the body is exactly the inherited term,
so the axiom surface is unchanged. -/
theorem twoCopyLadder {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {x z H : ℝ}
    (hH : 1 < H) (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h4 : H - 2 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 4)) : ℝ))
    (h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)) : ℝ))
    (h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z) : ℝ)) :
    H - 1 ≤
        (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (z ^ 2 / 4)) : ℝ) ∧
      H ≤
        (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (z ^ 2 / 2)) : ℝ) ∧
      H + 1 ≤
        (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (z ^ 2)) : ℝ) :=
  NPCC.two_copy_ladder f hH hx0 hx hz0 hz1 h4 h2 h1

/-! ## Aux-lemma battery

General properties of the three-rung readout `Λ = NPCC.LambdaGE`
(`def:lambda`, `03-preliminaries.tex:224`) and of the ladder-input premise.
Each is a statement about arbitrary `X`, `Y`, `W`, copy count and parameters,
not about the pinned construction. -/

/-- **Aux 1 (unfolding, `ℕ`).** `def:lambda` is a minimum of three terms, so a
lower bound on `Λ` is exactly the conjunction of three lower bounds.  This is
the displayed unfolding of `03-preliminaries.tex:234--240`, kept on the
complexity side (`1 + comp`, `2 + comp`) so that no truncated `ℕ` subtraction
is introduced. -/
lemma le_LambdaGE_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) (n : ℕ) :
    n ≤ LambdaGE f p x z ↔
      n ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x z) ∧
      n ≤ 1 + Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 2)) ∧
      n ≤ 2 + Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 4)) := by
  unfold LambdaGE
  rw [le_min_iff, le_min_iff]

/-- **Aux 2 (round trip, `ℝ`).** The same unfolding in the `ℝ`-cast, shifted
form in which the inherited contract speaks: `Λ ≥ n` is exactly
`comp(z) ≥ n`, `comp(z/2) ≥ n-1`, `comp(z/4) ≥ n-2`.  Both directions are
proved, so folding the rungs back into `Λ` recovers the original bound; this is
the encoding-correctness test for using `LambdaGE` as the paper's `Λ`. -/
lemma le_LambdaGE_iff_real {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) (n : ℕ) :
    n ≤ LambdaGE f p x z ↔
      ((n : ℝ) ≤ (Dfamily (interlaceFun f p) (bracketGE X Y p x z) : ℝ) ∧
        (n : ℝ) - 1 ≤
          (Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 2)) : ℝ) ∧
        (n : ℝ) - 2 ≤
          (Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 4)) : ℝ)) := by
  rw [le_LambdaGE_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by exact_mod_cast h1, ?_, ?_⟩
    · have h2' : (n : ℝ) ≤
          1 + (Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 2)) : ℝ) := by
        exact_mod_cast h2
      linarith
    · have h3' : (n : ℝ) ≤
          2 + (Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 4)) : ℝ) := by
        exact_mod_cast h3
      linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by exact_mod_cast h1, ?_, ?_⟩
    · have h2' : (n : ℝ) ≤
          1 + (Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 2)) : ℝ) := by
        linarith
      exact_mod_cast h2'
    · have h3' : (n : ℝ) ≤
          2 + (Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 4)) : ℝ) := by
        linarith
      exact_mod_cast h3'

/-- **Aux 3 (the minimum is a lower estimate).** `Λ` never exceeds any of its
three rungs.  In particular `Λ_M(p,x,z) ≤ comp⟨M,p,x,z⟩`, which is what makes
`Λ ≥ H` strictly stronger than the top-rung bound alone. -/
lemma LambdaGE_le_rungs {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) :
    LambdaGE f p x z ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x z) ∧
      LambdaGE f p x z ≤
        1 + Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 2)) ∧
      LambdaGE f p x z ≤
        2 + Dfamily (interlaceFun f p) (bracketGE X Y p x (z / 4)) :=
  ⟨min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (min_le_right _ _)⟩

/-- **Aux 4 (degeneracy).** With no columns the three-rung readout collapses to
`0`.  This is the `Λ`-level form of `NPCC.Dfamily_zero_degenerate`
(`vendor/npc-cc/NPCC/Twin.lean:813`) and is what makes every `Λ ≥ H` premise
with `H ≥ 1` a genuine constraint rather than a formality. -/
lemma LambdaGE_eq_zero_of_card_cols_zero {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {p : ℕ} {x z : ℝ} (hp : 0 < p) (hx1 : x ≤ 1)
    (hz1 : z ≤ 1) (hX : 1 ≤ Fintype.card X) (hY : Fintype.card Y = 0) :
    LambdaGE f p x z = 0 := by
  have htop : Dfamily (interlaceFun f p) (bracketGE X Y p x z) = 0 :=
    NPCC.Dfamily_zero_degenerate f hx1 hz1 hX (Or.inr ⟨hp, hY⟩)
  unfold LambdaGE
  rw [htop]
  exact Nat.min_eq_zero_iff.mpr (Or.inl rfl)

/-- **Aux 5 (the level cast).** The paper's `H = C_W - 1` is a **real**
substitution (`D-inherited-contracts.tex:339`), while the premise keeps the
paper's `ℕ` subtraction.  Under `1 ≤ C_W` the two agree; this is the single
place the cast is discharged. -/
lemma natCast_sub_one {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ) := Nat.cast_sub hn
  simpa using h

/-- **Aux 6 (the input has content).** The ladder-input premise already forces a
two-bit lower bound on its own top rung, for every `W` and every parameter
choice.  So it is not a bookkeeping hypothesis: it asserts a real
communication lower bound, which is why it stays a named hypothesis here rather
than becoming an axiom. -/
lemma ladderInput_forces_top_rung {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hCW : 3 ≤ CW)
    (hInput : CW - 1 ≤ LambdaGE W 1 θ y) :
    2 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ y) := by
  have h := le_trans hInput (LambdaGE_le_rungs W 1 θ y).1
  omega

/-- **Aux 7 (vacuous-hypothesis pole).** The ladder-input premise is **false**
whenever the column alphabet is empty.  Any inhabitant of the premise therefore
carries a nonempty column alphabet; the premise is not satisfied by a
degenerate carrier. -/
lemma ladderInput_forces_nonempty_cols {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hCW : 3 ≤ CW) (hθ1 : θ ≤ 1)
    (hy1 : y ≤ 1) (hX : 1 ≤ Fintype.card X)
    (hInput : CW - 1 ≤ LambdaGE W 1 θ y) :
    1 ≤ Fintype.card Y := by
  by_contra hcon
  have hY : Fintype.card Y = 0 := by omega
  rw [LambdaGE_eq_zero_of_card_cols_zero W (p := 1) (by norm_num) hθ1 hy1 hX hY]
    at hInput
  omega

/-! ## The deliverable

`eq:direct-two-copy` (`10-direct-bridge.tex:24`), derived from
`eq:direct-input` clause two (line 10) by the frozen section's own two
sentences at lines 19--25. -/

/-- **`eq:direct-two-copy`** (`10-direct-bridge.tex:24`; reader
`lem:bridge-base-estimates`, `04-bridge.tex:31`, first inequality).

From the second clause of `eq:direct-input`, `Λ_W(1, θ, y) ≥ C_W - 1`, under
the frozen guards `C_W ≥ 3` and `2θ ≤ 1` of line 19 together with the ambient
`0 < θ` and `0 < y ≤ 1` of `sec:preliminaries`, the inherited two-copy ladder
gives `Λ_W(2, 2θ, y²) ≥ C_W`.

The derivation is exactly the paper's: unfold the hypothesis into its three
rungs by `def:lambda`, apply `NPCC.two_copy_ladder` at the substitution
`H = (C_W : ℝ) - 1` — whose guard `1 < H` is proved by `C_W ≥ 3`, per
`D-inherited-contracts.tex:338--340` — and fold the three returned rungs
`H-1, H, H+1` at densities `y²/4, y²/2, y²` back into `Λ`.  No further lemma
is used; `y` is left abstract rather than pinned to the global `3/5`, since
lines 19--25 use only `0 < y ≤ 1`. -/
theorem lambdaTwoCopy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) {θ y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ) (hθ : 2 * θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hInput : CW - 1 ≤ LambdaGE W 1 θ y) :
    CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2) := by
  -- the row guard of the contract, from line 19's own spelling
  have hx : θ ≤ 1 / 2 := by linarith
  -- the substitution `H = C_W - 1` and its guard `1 < H`
  have hCr : (3 : ℝ) ≤ (CW : ℝ) := by exact_mod_cast hCW
  have hH : (1 : ℝ) < (CW : ℝ) - 1 := by linarith
  -- the three one-copy rungs of `eq:direct-input` clause two
  obtain ⟨r1, r2, r4⟩ := (le_LambdaGE_iff_real W 1 θ y (CW - 1)).mp hInput
  rw [natCast_sub_one (by omega : 1 ≤ CW)] at r1 r2 r4
  -- the checked inherited ladder
  obtain ⟨c4, c2, c1⟩ :=
    twoCopyLadder W (H := (CW : ℝ) - 1) hH hθ0 hx hy0 hy1
      (by linarith) (by linarith) (by linarith)
  -- fold the three two-copy rungs back into `Λ`
  exact (le_LambdaGE_iff_real W 2 (2 * θ) (y ^ 2) CW).mpr
    ⟨by linarith, by linarith, by linarith⟩

/-- **Composition: the `hTwoCopy` binder of `lem:defect-induction` is
discharged from `eq:direct-input` clause two.**

`BRIDGE-DEFECT-001` (`DefectInduction.lean`) carries `eq:direct-two-copy` as
the unproved binder `hTwoCopy`, which makes its lemma weaker than the paper's.
This corollary replaces that binder by the frozen input `Λ_W(1, θ, y) ≥ C_W-1`,
so `lem:defect-induction` now reads off exactly the two clauses of
`eq:direct-input` (line 10) that the frozen section actually assumes.

`2θ ≤ 1` is *derived* from the consumer's own guard `θ ≤ 1/4` rather than
re-assumed, so no new hypothesis is added.  The banked module is imported and
consumed; nothing in it is edited. -/
theorem defectInduction_ofLadderInput {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW p a : ℕ) (θ y lam : ℝ)
    (hp : 2 ^ a < 2 * p)
    (hlevel : (2 : ℝ) ^ a * θ ≤ 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hNear : CW ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 θ (Real.exp (-lam))))
    (hInput : CW - 1 ≤ LambdaGE W 1 θ y)
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y))
    (hK : K.Nonempty)
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p))
      (rowFloor (Fintype.card X) θ a))
    (hdefect : columnDefect K ≤ excessCopies a p * lam) :
    CW + a ≤ D (subgame (interlaceFun W p) R K) :=
  defectInduction W CW p a θ y lam hp hlevel hθ0 hθ hy0 hy1 hlam hX hY hCW
    hmargin hNear
    (lambdaTwoCopy W CW hCW hθ0 (by linarith) hy0 hy1 hInput) R K hK hrows
    hdefect

/-! ## Non-vacuity and the statement poles -/

/-- **Non-vacuity (i): every numeric guard is legal, and `C_W ≥ 3` is
necessary.**

The first six conjuncts discharge all purely numeric guards of `lambdaTwoCopy`
at the route's globally fixed constants `θ = 1/4` and `y = 3/5`
(`03-preliminaries.tex:216--219`) and at the frozen boundary value `C_W = 3`
(line 19); the fourth also meets the consumer's stronger `θ ≤ 1/4`.  The
seventh checks that the substituted level `H = (C_W : ℝ) - 1` clears the
inherited guard `1 < H` there.  The eighth is the reading check demanded by
`D-inherited-contracts.tex:338`, "The guard `1 < H` is necessary": at
`C_W = 2` the substituted level is exactly `1` and **fails** the guard, so the
frozen `C_W ≥ 3` cannot be relaxed to `C_W ≥ 2`.

This statement contains no `W`, so it is not by itself a witness for the
premise bundle. -/
theorem lambdaTwoCopy_guards_legal :
    3 ≤ (3 : ℕ) ∧ (0 : ℝ) < 1 / 4 ∧ 2 * (1 / 4 : ℝ) ≤ 1 ∧
      (1 / 4 : ℝ) ≤ 1 / 4 ∧ (0 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) ≤ 1 ∧
      (1 : ℝ) < ((3 : ℕ) : ℝ) - 1 ∧ ¬ ((1 : ℝ) < ((2 : ℕ) : ℝ) - 1) := by
  refine ⟨le_refl 3, by norm_num, by norm_num, le_refl _, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- **Non-vacuity (ii): the derivation fires at the pinned route constants.**

The same statement as `lambdaTwoCopy` with every numeric parameter pinned to
the frozen route values `C_W = 3`, `θ = 1/4`, `y = 3/5`, and with `X`, `Y`, `W`
left universally quantified — deliberately, since the semantic premise
`Λ_W(1, θ, y) ≥ C_W - 1` has no exhibited inhabitant in Lean and cannot have
one until Stages 1--4 land.  It is the witness that Candidate B fails: the
vendored `EthBridge.two_copy_bundle_of_rungs` needs `4 ≤ C`, so it cannot
produce this bound at the paper's `C_W = 3`. -/
theorem lambdaTwoCopy_fires {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool)
    (hInput : (3 : ℕ) - 1 ≤ LambdaGE W 1 (1 / 4) (3 / 5)) :
    (3 : ℕ) ≤ LambdaGE W 2 (2 * (1 / 4)) ((3 / 5 : ℝ) ^ 2) :=
  lambdaTwoCopy W 3 (le_refl 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hInput

/-- **Non-vacuity (iii): trivial-conclusion pole.**

The deliverable `C_W ≤ Λ_W(2, 2θ, y²)` is not a formality: it is **false** for
every `W` over an empty column alphabet, at every legal parameter assignment.
So the conclusion constrains `W`, and `lambdaTwoCopy` is not proving something
that holds for free. -/
theorem lambdaTwoCopy_conclusion_nontrivial {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hCW : 3 ≤ CW)
    (hθ : 2 * θ ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : 1 ≤ Fintype.card X)
    (hY : Fintype.card Y = 0) :
    ¬ (CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) := by
  rw [LambdaGE_eq_zero_of_card_cols_zero W (p := 2) (by norm_num) hθ
    (by nlinarith) hX hY]
  omega

end EthInapproximability.ParameterizedNP.TwoCopyLadder
