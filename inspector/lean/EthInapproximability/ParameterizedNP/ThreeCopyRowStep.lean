import EthInapproximability.ParameterizedNP.TwoCopyLadder

/-!
# Parameterized NP route: the three-copy row step of the direct bridge

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-THREECOPY-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened by
the `cc-t1e` tranche as the step that `BRIDGE-TWOCOPY-001` explicitly left
open: the *second* inequality of the reader's `lem:bridge-base-estimates`.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

* `sections/10-direct-bridge.tex`:
  * line 26, "Its bottom rung has complexity at least `C_W - 2`, which is
    positive in every application";
  * lines 27--28, "Whenever the row request is legal, `4θ ≤ 1`, the inherited
    row-step lemma therefore also gives";
  * `eq:direct-three-copy` (label line 31) — the deliverable
    `comp⟨W, 3, 4θ, y²⟩ ≥ C_W + 1`;
  * `eq:direct-two-copy` (label line 24) — the input `Λ_W(2, 2θ, y²) ≥ C_W`,
    landed in `BRIDGE-TWOCOPY-001`;
  * `eq:direct-input` (label line 11), **second clause** at line 10 —
    `Λ_W(1, θ, y) ≥ C_W - 1`, the start of the composition corollary;
  * line 60, "The first inequality and `Q_0 ≥ 16` imply `4θ ≤ δ/Q_0 < 1`, so
    the invocation `eq:direct-three-copy` is legal."
* `sections/D-inherited-contracts.tex`, paragraph "Checked inherited
  declaration: row step" (line 377):
  * the exact type of `NPCC.row_step`, guards at lines 381--383 and conclusion
    `eq:contract-row-step` (label line 389);
  * lines 391--393, "Section `sec:direct-bridge` uses
    `(p, σ, x, z) = (1, 1, 2θ, y²)`.  The bottom output of
    `eq:contract-two-copy-output` supplies the nontriviality hypothesis."
* `sections/D-inherited-contracts.tex`, `eq:contract-two-copy-output`
  (label line 336) — the bottom output used above.
* `sections/03-preliminaries.tex`:
  * `def:lambda` (label line 224);
  * lines 199--201, "We repeatedly use four inherited structural facts.
    Bracket complexity is monotone in the copy count and retained densities;
    ..." — the row-retention monotonicity used by `Dfamily_mono_rowScale`;
  * lines 216--219, the globally fixed `δ = 1/10`, `y = 1/2 + δ = 3/5`.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex`,
`lem:bridge-base-estimates` (label line 31, statement lines 30--40): its
**second** inequality `D_W(3; 4θ, y²) ≥ C_W + 1` of `eq:bridge-base-estimates`
(label line 38).  The file was opened and the item checked: it states the same
fact as `eq:direct-three-copy`, under the reader's hypotheses `C_W ≥ 3`,
`0 < θ ≤ 1/4`, and `eq:bridge-common-input` (label line 15).  Its proof lines
45--47 read "The bottom rung remains positive because `C_W ≥ 3`; the bundled
row step therefore gives the second inequality.  The condition `4θ ≤ 1` makes
its row request legal."

The **first** inequality of that same reader lemma is already assigned to
`BRIDGE-TWOCOPY-001` (`TwoCopyLadder.lean`) and is **not** re-claimed here;
the two rows carry the two different inequalities of one bundled reader
statement, and no reader item is assigned twice.  No reader prose is cited as
a statement.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Trace note (row scale of the seed)

`D-inherited-contracts.tex:392--393` says the row-step nontriviality
hypothesis is supplied by the bottom output of
`eq:contract-two-copy-output`.  Read literally at the frozen instantiation,
those two quantities sit at *different* row scales: the two-copy output is
taken at `x = θ` (`eq:direct-two-copy`, line 24), so its bottom rung is
`comp⟨W, 2, 2θ, y²/4⟩ ≥ C_W - 2`, while the row step at
`(p, σ, x, z) = (1, 1, 2θ, y²)` requests `comp⟨W, 2p, 2x, z/4⟩`, i.e.
`comp⟨W, 2, 4θ, y²/4⟩`.  The two are joined by exactly one application of the
first of the four inherited structural facts listed at
`03-preliminaries.tex:199--201` — bracket complexity is monotone in the
retained row density — which is transcribed here as the general lemma
`Dfamily_mono_rowScale`.  This is a paper-anchored step, not an invented one;
it is recorded because the frozen sentence compresses it.

## Status and dependencies

* Proof status: **inherited** for `rowStep` (a re-export of the
  kernel-checked vendored `NPCC.row_step`,
  `vendor/npc-cc/NPCC/Engine.lean:782`), and **new (elementary)** for the aux
  battery (`Dfamily_mono_rowScale`, `LambdaGE_mono_rowScale`, the row-side
  degeneracy pair `Dfamily_eq_zero_of_card_rows_zero` /
  `LambdaGE_eq_zero_of_card_rows_zero`, the two carrier-forcing lemmas), the
  seed derivation, and `lambdaThreeCopy` / `directThreeCopy`, which are the
  frozen section's own two sentences at lines 26--31 around a single
  application of that declaration at the frozen instantiation.  No further
  communication-complexity lemma and no witness choice is introduced.
* Imports: `EthInapproximability.ParameterizedNP.TwoCopyLadder` only, hence
  `DefectInduction.lean`, `InheritedContracts.lean` and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported, so the
  AGHP balanced-family axiom is not in scope, and there is no contact with
  `EXPANDER-001` (which by design has no Lean declaration and would have to
  remain a named hypothesis).
* External adapters: none.  Nothing here is axiomatized; the inherited
  declarations are consumed, never re-proved and never widened.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

Two encodings of the derivation were written out before landing.

**Candidate A (landed).** Keep the paper's own `Λ` form as the row-step
output, `C_W + 1 ≤ Λ_W(3, 4θ, y²)`, and publish `eq:direct-three-copy` in its
literal `comp` form as the named corollary `directThreeCopy`, reading the top
rung off with `LambdaGE_le_rungs`.  The row-step seed is *derived* from the
landed `eq:direct-two-copy` through the bottom rung and one row-retention
monotonicity step, exactly as the trace note above records.

**Candidate B (rejected).** Avoid the monotonicity step by applying the
two-copy ladder one scale higher, at `x = 2θ`, so that its bottom output
already sits at row scale `4θ`.  That variant needs
`Λ_W(1, 2θ, y) ≥ C_W - 1` as its input.  The frozen `eq:direct-input`
(line 10) and the reader's `eq:bridge-common-input` (line 14) both state the
three-rung estimate at the row threshold `θ`, and the bridge's whole point
(lines 13--17) is that the two clauses hold *at the same row threshold* `θ`.
Candidate B therefore silently strengthens the frozen input — an over-strong
hypothesis typechecks perfectly and a green build would not see it.  It is
disqualified by the aux battery: the composition corollary
`bridgeBaseEstimates`, which runs the whole chain from
`eq:direct-input` clause two at the paper's own `θ`, is **not** derivable
under Candidate B.

Ranking (aux lemmas proved, faithfulness, length): A = 9/9 aux lemmas proved,
`Λ` and `comp` written exactly as `eq:direct-two-copy` and
`eq:direct-three-copy` write them, and it composes with the landed
`lambdaTwoCopy` over the frozen input; B fails the composition outright and is
less faithful.  A landed.

## Faithfulness notes (mechanical rules M1--M10)

* `rowStep` restates the vendored type **verbatim**: the same binder order
  `f`, `p`, `σ`, `hp`, `hσ`, `hx0`, `hx`, `hz0`, `hz1`, `h1`, the same guards
  `1 ≤ p`, `σ ≤ 1`, `0 < x ≤ 1/2`, `0 < z ≤ 1`, the same seed family
  `⟨f, 2p, 2x, z/4⟩` at level `1`, and the same conclusion
  `1 + Λ_f(p+σ, x, z) ≤ Λ_f(2p+σ, 2x, z)`.  That is the exact printed content
  of `D-inherited-contracts.tex:381--388`.
* The instantiation is the frozen `(p, σ, x, z) = (1, 1, 2θ, y²)` of line 391
  and nothing else; `rowStep_instantiation_arithmetic` checks the three index
  identities `1 + 1 = 2`, `2·1 + 1 = 3`, `2·(2θ) = 4θ` that turn the contract's
  generic conclusion into `eq:direct-three-copy`'s copy count `3` and row
  scale `4θ`.
* The row guard is written `4 * θ ≤ 1`, which is line 27's own spelling, not
  the contract's equivalent `2θ ≤ 1/2`; the conversion is one `linarith` step
  inside the proof and is not pushed onto the caller.
* `Λ` is **not** redefined.  It is the vendored `NPCC.LambdaGE`
  (`Engine.lean:299`), which is literally `def:lambda`.  `comp` is the
  vendored `NPCC.Dfamily` over `NPCC.bracketGE`, as in the sibling module.
* No complexity or robustness conclusion is placed in constructor data: this
  module introduces **no structure and no premise bundle at all**, only
  theorems with explicit binders, so no derived telescope is restated as a
  field.  In particular the row-step seed `1 ≤ comp⟨W, 2, 4θ, y²/4⟩` is
  **derived** (`rowStepSeed_of_twoCopy`) rather than carried as a binder,
  which is why it does not appear in the signature of `lambdaThreeCopy`.
* Finite carriers and nonemptiness: `1 ≤ |X|` is **not** a hypothesis of any
  deliverable, because it is **not** a hypothesis of `eq:direct-three-copy`.
  The monotonicity step does need the bracket family at the larger row scale
  to be nonempty (`NPCC.bracketGE.nonempty`), since `NPCC.Dfamily` is an
  infimum and collapses to `0` on an empty family; but that side condition is
  *derived* from the frozen premise by `threeCopyInput_forces_nonempty_rows`
  (Aux 5), which is why it appears as a binder only on the general
  monotonicity aux lemmas and never on `lambdaThreeCopy`, `directThreeCopy` or
  `bridgeBaseEstimates`.  The row-side collapse lemma feeding that derivation
  had to be re-proved here (`Dfamily_eq_zero_of_card_rows_zero`) from the
  public `NPCC.D_zero_of_empty`, because the vendored row-side statement
  (`Engine.lean:748`) is `private` and the vendored public one
  (`NPCC.Dfamily_zero_degenerate`) covers only the column side and itself
  assumes `1 ≤ |X|`.  Carrying `1 ≤ |X|` as a binder instead would have made
  every deliverable strictly weaker than the frozen line 31 while still
  compiling green.
* Interlace widths are untouched: the copy counts here are the frozen `2` and
  `3` of `eq:direct-two-copy` and `eq:direct-three-copy`; neither `q` nor `Q`
  appears.
* Trivial-conclusion pole.  The deliverable is a universally quantified
  implication, not an existential, so the pole is a vacuous conclusion rather
  than a trivial witness.  `C_W + 1 ≤ comp⟨W, 3, 4θ, y²⟩` would be free if the
  right-hand side were unconstrained; `directThreeCopy_conclusion_nontrivial`
  proves the conclusion is **false** whenever the column alphabet is empty, so
  it is a real constraint on `W`.
* Vacuous-hypothesis pole.  `threeCopyInput_forces_nonempty_cols` proves the
  input `eq:direct-two-copy` is likewise false for an empty column alphabet,
  so the premise genuinely constrains `W`.
* Non-vacuity of the parameters, and abstract quantification elsewhere.
  `lambdaThreeCopy_guards_legal` discharges every purely numeric guard at the
  route's globally fixed `y = 3/5` (`03-preliminaries.tex:216--219`), at the
  boundary `C_W = 3` (line 19) and at the boundary row threshold `θ = 1/4`,
  where `4θ ≤ 1` is tight; it also records that the two-copy guard `2θ ≤ 1`
  alone does **not** make the row request legal, since `4θ ≤ 1` fails at
  `θ = 3/8`.  The **semantic** premise `Λ_W(2, 2θ, y²) ≥ C_W` has **no
  exhibited inhabitant** anywhere in this development, and none can be
  exhibited until Stages 1--4 land in Lean; it is therefore carried by
  abstract quantification over `X`, `Y`, `W`, and `lambdaThreeCopy_fires` is
  stated at universally quantified `X`, `Y`, `W` with only the numeric
  parameters pinned.

## GAP-EXPOSED

`eq:direct-input` itself is **not** discharged here: both of its clauses are
construction outputs of Sections 8--9 and remain named hypotheses.
`thm:direct-robustification` (`10-direct-bridge.tex:35`) is **not** claimed,
and neither is the canonical `Q`, the exact bit recovery, the selector upper
bound, nor the output robustness it asserts.  Nothing about route completion
is claimed.
-/

namespace EthInapproximability.ParameterizedNP.ThreeCopyRowStep

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts
open EthInapproximability.ParameterizedNP.DefectInduction
open EthInapproximability.ParameterizedNP.TwoCopyLadder

/-! ## The re-exported inherited contract

`sections/D-inherited-contracts.tex:377`. -/

/-- **Checked inherited declaration: row step.**

Route-named facade for `NPCC.row_step`
(`vendor/npc-cc/NPCC/Engine.lean:782`), restating the guard list at
`sections/D-inherited-contracts.tex:381--383` and the conclusion
`eq:contract-row-step` (label line 389) verbatim: natural numbers `p, σ` with
`1 ≤ p`, `σ ≤ 1`, reals `0 < x ≤ 1/2`, `0 < z ≤ 1`, and the seed bound
`1 ≤ comp⟨f, 2p, 2x, z/4⟩`, concluding
`1 + Λ_f(p+σ, x, z) ≤ Λ_f(2p+σ, 2x, z)`.

The vendored declaration is *consumed*: the body is exactly the inherited
term, so the axiom surface is unchanged. -/
theorem rowStep {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p σ : ℕ) (hp : 1 ≤ p) (hσ : σ ≤ 1) {x z : ℝ}
    (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : 1 ≤ Dfamily (interlaceFun f (2 * p))
        (bracketGE X Y (2 * p) (2 * x) (z / 4))) :
    1 + LambdaGE f (p + σ) x z ≤ LambdaGE f (2 * p + σ) (2 * x) z :=
  NPCC.row_step f p σ hp hσ hx0 hx hz0 hz1 h1

/-! ## Aux-lemma battery

General properties of the bracket readout in its row parameter, of the
two-copy bottom rung, and of the frozen instantiation.  Each is a statement
about arbitrary `X`, `Y`, `W` and parameters, not about a pinned
construction. -/

/-- **Aux 1 (row-retention monotonicity).**  The first of the four inherited
structural facts of `03-preliminaries.tex:199--201`: bracket complexity is
monotone in the retained row density.  Raising the row parameter from `x` to
`x'` shrinks the bracket family (`NPCC.bracketGE.anti_mono_params`), and
`NPCC.Dfamily` is antitone in the family (`NPCC.Dfamily.anti_mono`), so the
infimum can only rise.  The nonemptiness side condition of the antitone lemma
is met at the *larger* scale by `NPCC.bracketGE.nonempty`, which is why
`x' ≤ 1`, `z ≤ 1` and `1 ≤ |X|` appear. -/
lemma Dfamily_mono_rowScale {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) {x x' z : ℝ} (hxx : x ≤ x') (hx1 : x' ≤ 1)
    (hz1 : z ≤ 1) (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x z) ≤
      Dfamily (interlaceFun f p) (bracketGE X Y p x' z) := by
  classical
  have hsub : bracketGE X Y p x' z ⊆ bracketGE X Y p x z :=
    bracketGE.anti_mono_params p hxx (le_refl z)
  have hne : (bracketGE X Y p x' z).Nonempty :=
    bracketGE.nonempty p x' z hx1 hz1 hX
  exact Dfamily.anti_mono (interlaceFun f p) hsub hne

/-- **Aux 2 (the same monotonicity at the `Λ` level).**  `def:lambda` is a
minimum of three bracket readouts that share the row parameter, so Aux 1 lifts
to `Λ` termwise.  Recorded as a general property of the encoding: it is the
statement that the three-rung quantity is monotone in the retained row
density, in the same direction as each rung. -/
lemma LambdaGE_mono_rowScale {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) {x x' z : ℝ} (hxx : x ≤ x') (hx1 : x' ≤ 1)
    (hz1 : z ≤ 1) (hX : 1 ≤ Fintype.card X) :
    LambdaGE f p x z ≤ LambdaGE f p x' z := by
  have h0 := Dfamily_mono_rowScale f p (x := x) (x' := x') (z := z) hxx hx1
    hz1 hX
  have h1 := Dfamily_mono_rowScale f p (x := x) (x' := x') (z := z / 2) hxx
    hx1 (by linarith) hX
  have h2 := Dfamily_mono_rowScale f p (x := x) (x' := x') (z := z / 4) hxx
    hx1 (by linarith) hX
  rw [le_LambdaGE_iff]
  exact ⟨le_trans (LambdaGE_le_rungs f p x z).1 h0,
    le_trans (LambdaGE_le_rungs f p x z).2.1 (by omega),
    le_trans (LambdaGE_le_rungs f p x z).2.2 (by omega)⟩

/-- **Aux 3 (empty rows collapse the bracket readout).**  With no rows the
infimum defining `comp` is `0`: either the bracket family is empty, in which
case `Nat.sInf ∅ = 0`, or any member has an empty row party and
`NPCC.D_zero_of_empty` (`vendor/npc-cc/NPCC/Twin.lean:800`) sends its subgame
to `0`.  This is the row-side companion of the vendored
`NPCC.Dfamily_zero_degenerate`, which covers only the column side and itself
*assumes* `1 ≤ |X|`; the vendored row-side statement
(`Engine.lean:748`) is `private` and therefore not importable, so it is
re-derived here from public parts.  It carries no parameter guards at all. -/
lemma Dfamily_eq_zero_of_card_rows_zero {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) (hX : Fintype.card X = 0) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x z) = 0 := by
  classical
  have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
  have hrows : IsEmpty (Fin p × X) := by
    constructor
    rintro ⟨_, xx⟩
    exact hXempty.false xx
  unfold Dfamily
  rw [Nat.sInf_eq_zero]
  by_cases hne : (bracketGE X Y p x z).Nonempty
  · left
    obtain ⟨RC, hRC⟩ := hne
    have hsub : IsEmpty {a // a ∈ RC.1} :=
      Subtype.isEmpty_of_false (fun a => (hrows.false a).elim)
    exact ⟨RC, hRC, (NPCC.D_zero_of_empty _ (Or.inl hsub)).symm⟩
  · right
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨RC, hRC, _⟩
    exact hne ⟨RC, hRC⟩

/-- **Aux 4 (the same collapse at the `Λ` level).**  `def:lambda` is a minimum
whose first rung is the top bracket readout, so Aux 3 sends the whole
three-rung quantity to `0`.  The row-side analogue of the landed
`TwoCopyLadder.LambdaGE_eq_zero_of_card_cols_zero`. -/
lemma LambdaGE_eq_zero_of_card_rows_zero {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x z : ℝ) (hX : Fintype.card X = 0) :
    LambdaGE f p x z = 0 := by
  unfold LambdaGE
  rw [Dfamily_eq_zero_of_card_rows_zero f p x z hX]
  exact Nat.min_eq_zero_iff.mpr (Or.inl rfl)

/-- **Aux 5 (the input forces a nonempty row carrier).**  `1 ≤ |X|` is **not** a
hypothesis of `eq:direct-three-copy`, and it is not assumed here: the frozen
input `eq:direct-two-copy` already forces it, because by Aux 4 an empty row
carrier would make `Λ_W(2, 2θ, y²) = 0` while `C_W ≥ 3`
(`10-direct-bridge.tex:19`).  This is what keeps the nonemptiness side
condition of the monotonicity step out of the deliverable's signature.  It
needs no parameter guards. -/
lemma threeCopyInput_forces_nonempty_rows {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hCW : 3 ≤ CW)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    1 ≤ Fintype.card X := by
  by_contra hcon
  have hX : Fintype.card X = 0 := by omega
  rw [LambdaGE_eq_zero_of_card_rows_zero W 2 (2 * θ) (y ^ 2) hX] at hTwo
  omega

/-- **Aux 6 (the two-copy bottom rung).**  `10-direct-bridge.tex:26`, "Its
bottom rung has complexity at least `C_W - 2`", read off `eq:direct-two-copy`
by the third component of `LambdaGE_le_rungs`.  Kept on the complexity side
(`C_W ≤ 2 + comp`) so that no truncated `ℕ` subtraction is introduced.
General in `W`, `C_W` and the parameters. -/
lemma bottomRung_of_lambdaTwoCopy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ}
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    CW ≤ 2 + Dfamily (interlaceFun W 2)
        (bracketGE X Y 2 (2 * θ) (y ^ 2 / 4)) :=
  le_trans hTwo (LambdaGE_le_rungs W 2 (2 * θ) (y ^ 2)).2.2

/-- **Aux 7 (the row-step seed).**  `D-inherited-contracts.tex:392--393`, "The
bottom output of `eq:contract-two-copy-output` supplies the nontriviality
hypothesis", made exact.  Aux 6 puts the bottom rung at row scale `2θ` and
`C_W ≥ 3` makes it positive (`10-direct-bridge.tex:26`, "which is positive in
every application"); Aux 1 transports it up to the row scale `4θ` at which the
row step requests its seed, its nonemptiness side condition being supplied by
Aux 5 rather than assumed.  This is the derivation that keeps the seed out of
the signature of `lambdaThreeCopy`. -/
lemma rowStepSeed_of_twoCopy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hCW : 3 ≤ CW) (hθ0 : 0 < θ)
    (hθ : 4 * θ ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    1 ≤ Dfamily (interlaceFun W 2)
        (bracketGE X Y 2 (4 * θ) (y ^ 2 / 4)) := by
  have hX : 1 ≤ Fintype.card X := threeCopyInput_forces_nonempty_rows W hCW hTwo
  have hbot := bottomRung_of_lambdaTwoCopy W hTwo
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hmono := Dfamily_mono_rowScale W 2 (x := 2 * θ) (x' := 4 * θ)
    (z := y ^ 2 / 4) (by linarith) hθ (by linarith) hX
  omega

/-- **Aux 8 (the frozen instantiation is arithmetically what the paper says).**
`D-inherited-contracts.tex:391` fixes `(p, σ, x, z) = (1, 1, 2θ, y²)`.  Under
that substitution the generic conclusion `eq:contract-row-step` reads
`1 + Λ_f(2, 2θ, y²) ≤ Λ_f(3, 4θ, y²)`, which is the shape of
`eq:direct-three-copy`.  The three identities below are exactly the index and
scale computations that make that so; they are checked rather than assumed,
because a copy count or row scale off by one would typecheck and prove the
wrong statement. -/
lemma rowStep_instantiation_arithmetic (θ : ℝ) :
    (1 : ℕ) + 1 = 2 ∧ 2 * 1 + 1 = 3 ∧ (2 : ℝ) * (2 * θ) = 4 * θ :=
  ⟨rfl, rfl, by ring⟩

/-- **Aux 9 (vacuous-hypothesis pole).**  The input `eq:direct-two-copy` is
**false** whenever the column alphabet is empty, so any inhabitant of the
premise carries a nonempty column alphabet.  Proved from the landed
`TwoCopyLadder.LambdaGE_eq_zero_of_card_cols_zero`, its own `1 ≤ |X|` side
condition being supplied by Aux 5; the premise is not satisfied by a
degenerate carrier on either side. -/
lemma threeCopyInput_forces_nonempty_cols {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hCW : 3 ≤ CW)
    (hθ : 2 * θ ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    1 ≤ Fintype.card Y := by
  have hX : 1 ≤ Fintype.card X := threeCopyInput_forces_nonempty_rows W hCW hTwo
  by_contra hcon
  have hY : Fintype.card Y = 0 := by omega
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  rw [LambdaGE_eq_zero_of_card_cols_zero W (p := 2) (by norm_num) hθ hy2 hX hY]
    at hTwo
  omega

/-! ## The deliverable

`eq:direct-three-copy` (`10-direct-bridge.tex:31`), derived from
`eq:direct-two-copy` (line 24) by the frozen section's own sentences at lines
26--31. -/

/-- **The row-step output at the frozen instantiation.**

From `eq:direct-two-copy`, `Λ_W(2, 2θ, y²) ≥ C_W`, under the frozen guards
`C_W ≥ 3` and `4θ ≤ 1` of lines 19 and 27 together with the ambient `0 < θ`
and `0 < y ≤ 1` of `sec:preliminaries` and the nonempty row carrier, the
inherited row step at `(p, σ, x, z) = (1, 1, 2θ, y²)`
(`D-inherited-contracts.tex:391`) gives `Λ_W(3, 4θ, y²) ≥ C_W + 1`.

This is the `Λ`-strength form of `eq:direct-three-copy`; the paper publishes
the top rung of it, which `directThreeCopy` reads off.  The derivation is
exactly the paper's: put the bottom rung of the two-copy output at the
requested row scale (`rowStepSeed_of_twoCopy`), invoke the row step, and add
the returned bit to the two-copy bound. -/
theorem lambdaThreeCopy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) {θ y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ) (hθ : 4 * θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    CW + 1 ≤ LambdaGE W 3 (4 * θ) (y ^ 2) := by
  -- the frozen scale identity of the instantiation `x = 2θ`
  have hscale : (2 : ℝ) * (2 * θ) = 4 * θ := by ring
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hy20 : (0 : ℝ) < y ^ 2 := by positivity
  -- the nontriviality hypothesis, supplied by the two-copy bottom output
  have hseed : 1 ≤ Dfamily (interlaceFun W (2 * 1))
      (bracketGE X Y (2 * 1) (2 * (2 * θ)) (y ^ 2 / 4)) := by
    rw [hscale]
    exact rowStepSeed_of_twoCopy W hCW hθ0 hθ hy0 hy1 hTwo
  -- the checked inherited row step at `(p, σ, x, z) = (1, 1, 2θ, y²)`
  have hstep : 1 + LambdaGE W 2 (2 * θ) (y ^ 2)
      ≤ LambdaGE W 3 (4 * θ) (y ^ 2) := by
    have h := rowStep W 1 1 (le_refl 1) (le_refl 1) (by linarith)
      (by linarith) hy20 hy2 hseed
    rw [hscale] at h
    exact h
  omega

/-- **`eq:direct-three-copy`** (`10-direct-bridge.tex:31`; reader
`lem:bridge-base-estimates`, `04-bridge.tex:31`, **second** inequality).

`comp⟨W, 3, 4θ, y²⟩ ≥ C_W + 1`, the literal form the paper publishes, obtained
from `lambdaThreeCopy` by the top rung of `def:lambda`. -/
theorem directThreeCopy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) {θ y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ) (hθ : 4 * θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    CW + 1 ≤ Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2)) :=
  le_trans (lambdaThreeCopy W CW hCW hθ0 hθ hy0 hy1 hTwo)
    (LambdaGE_le_rungs W 3 (4 * θ) (y ^ 2)).1

/-- **Composition: the whole reader lemma `lem:bridge-base-estimates` from
`eq:direct-input` clause two.**

Chains the landed `TwoCopyLadder.lambdaTwoCopy` through the row step: from the
single frozen input `Λ_W(1, θ, y) ≥ C_W - 1` (`eq:direct-input` clause two,
`10-direct-bridge.tex:10`; reader `eq:bridge-common-input` second estimate,
`04-bridge.tex:14`) under `C_W ≥ 3` and `4θ ≤ 1`, it returns **both**
`eq:direct-two-copy` and `eq:direct-three-copy`, i.e. both inequalities of
`eq:bridge-base-estimates` (`04-bridge.tex:38`).

`2θ ≤ 1`, the two-copy guard of line 19, is *derived* from `4θ ≤ 1` rather
than re-assumed, so no hypothesis is added.  The hypothesis list is exactly the
reader lemma's `C_W ≥ 3`, `0 < θ ≤ 1/4` and `eq:bridge-common-input`, with
nothing about the carriers: the row carrier is forced nonempty by Aux 5.  The
banked module is imported and consumed; nothing in it is edited. -/
theorem bridgeBaseEstimates {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) {θ y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ) (hθ : 4 * θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hInput : CW - 1 ≤ LambdaGE W 1 θ y) :
    CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2) ∧
      CW + 1 ≤
        Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2)) := by
  have hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2) :=
    lambdaTwoCopy W CW hCW hθ0 (by linarith) hy0 hy1 hInput
  exact ⟨hTwo, directThreeCopy W CW hCW hθ0 hθ hy0 hy1 hTwo⟩

/-! ## Non-vacuity and the statement poles -/

/-- **Non-vacuity (i): every numeric guard is legal, and the two-copy guard
alone is not enough.**

The first five conjuncts discharge all purely numeric guards of
`lambdaThreeCopy` at the boundary row threshold `θ = 1/4`, at the route's
globally fixed `y = 3/5` (`03-preliminaries.tex:216--219`) and at the frozen
boundary value `C_W = 3` (line 19); the sixth records that the contract's own
row guard `x = 2θ ≤ 1/2` (`D-inherited-contracts.tex:380`) is then tight.  The
seventh is the reading check demanded by `10-direct-bridge.tex:27` and by the
reader's line 47, "The condition `4θ ≤ 1` makes its row request legal": at
`θ = 3/8` the two-copy guard `2θ ≤ 1` of line 19 still holds while `4θ ≤ 1`
**fails**, so the row-step guard is a strictly stronger condition and cannot
be inherited from the two-copy step.

This statement contains no `W`, so it is not by itself a witness for the
premise bundle. -/
theorem lambdaThreeCopy_guards_legal :
    3 ≤ (3 : ℕ) ∧ (0 : ℝ) < 1 / 4 ∧ 4 * (1 / 4 : ℝ) ≤ 1 ∧
      (0 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) ≤ 1 ∧
      2 * (1 / 4 : ℝ) ≤ 1 / 2 ∧
      (2 * (3 / 8 : ℝ) ≤ 1 ∧ ¬ (4 * (3 / 8 : ℝ) ≤ 1)) := by
  refine ⟨le_refl 3, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- **Non-vacuity (ii): the derivation fires at pinned constants.**

The same statement as `directThreeCopy` with every numeric parameter pinned to
`C_W = 3`, `θ = 1/4`, `y = 3/5`, and with `X`, `Y`, `W` left universally
quantified — deliberately, since the semantic premise `Λ_W(2, 2θ, y²) ≥ C_W`
has no exhibited inhabitant in Lean and cannot have one until Stages 1--4
land.  There is **no** carrier hypothesis: the premise itself is the only
assumption, so the witness cannot be accused of importing a side condition. -/
theorem lambdaThreeCopy_fires {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool)
    (hTwo : (3 : ℕ) ≤ LambdaGE W 2 (2 * (1 / 4)) ((3 / 5 : ℝ) ^ 2)) :
    (3 : ℕ) + 1 ≤ Dfamily (interlaceFun W 3)
      (bracketGE X Y 3 (4 * (1 / 4)) ((3 / 5 : ℝ) ^ 2)) :=
  directThreeCopy W 3 (le_refl 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hTwo

/-- **Non-vacuity (iii): trivial-conclusion pole.**

The deliverable `C_W + 1 ≤ comp⟨W, 3, 4θ, y²⟩` is not a formality: it is
**false** for every `W` over an empty column alphabet, at every legal
parameter assignment.  So the conclusion constrains `W`, and `directThreeCopy`
is not proving something that holds for free. -/
theorem directThreeCopy_conclusion_nontrivial {X Y : Type*} [Fintype X]
    [Fintype Y] (W : X → Y → Bool) {CW : ℕ} {θ y : ℝ} (hθ : 4 * θ ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : 1 ≤ Fintype.card X)
    (hY : Fintype.card Y = 0) :
    ¬ (CW + 1 ≤
        Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2))) := by
  have hzero : Dfamily (interlaceFun W 3)
      (bracketGE X Y 3 (4 * θ) (y ^ 2)) = 0 :=
    NPCC.Dfamily_zero_degenerate W hθ (by nlinarith) hX
      (Or.inr ⟨by norm_num, hY⟩)
  rw [hzero]
  omega

end EthInapproximability.ParameterizedNP.ThreeCopyRowStep
