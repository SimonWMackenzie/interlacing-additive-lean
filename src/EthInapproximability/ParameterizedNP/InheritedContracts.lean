import EthInapproximability.Prelude

/-!
# Parameterized NP route: inherited-contract facade for maximum projection

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).

Autoformalization anchors (frozen release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`):

* `sections/D-inherited-contracts.tex`, `app:contract-projection` (line 150),
  paragraph "Checked inherited declaration: typed maximum projection"
  (line 179):
  * guards `eq:contract-member-max-projection-guards`  (line 202);
  * conclusion `eq:contract-member-max-projection`     (line 216);
  * defect corollary `eq:contract-defect-projection`   (line 244).
* `sections/10-direct-bridge.tex`, `sec:defect-induction` (line 189); the
  logarithmic defect `Def(K) = ln (n^p / |K|)` is fixed at line 96 of that
  file and is transcribed here as `columnDefect`.

Reader counterparts (`routes/parameterized-np/reader-facing/`):

* `sections/02-preliminaries.tex`, §"The inherited classical engine" (line
  111), `prop:paper-projection-facts` (line 120) — the projection facts;
* `sections/04-bridge.tex`, `thm:near-to-robust` (line 82) — the consumer.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **inherited** for `memberMaxProjection` (a re-export of the
  kernel-checked vendored declaration `EthBridge.member_max_projection`,
  `vendor/npc-cc/EthBridge/Induction.lean:569`), and **new (elementary)** for
  `defectProjection`, which is derived from a *single* application of that
  declaration and introduces no further projection lemma or witness choice.
* Imports: `EthInapproximability.Prelude` only, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the AGHP balanced-family axiom is not in scope.
* External adapters: none.  Nothing here is axiomatized; the inherited
  declaration is consumed, never re-proved and never widened.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  `propext`, `Classical.choice`, `Quot.sound`.
* Ledger row: `INHERIT-001` (`OBLIGATION_LEDGER.md`), whose Lean column this
  module discharges for the projection contract; consumed by `BRIDGE-001`.

## Faithfulness notes (mechanical rules M1–M10)

* `memberMaxProjection` restates the vendored type **verbatim**: the same
  binder order `W p ℓ T y`, the same guards `1 ≤ ℓ`, `ℓ ≤ p`, `0 < y`,
  `y ≤ 1`, `1 ≤ |X|`, `1 ≤ |Y|`, `EquipGE R univ T`, `|Y|^p * y ≤ |C|`, the
  same *integer* row floor `T` on both sides, `Real.rpow` at the real ratio
  `(ℓ : ℝ) / (p : ℝ)` (so the equality case `ℓ = p` is covered), and the
  complexity inequality in the lower-bound direction
  `D(child) ≤ D(parent)` for the *fixed* parent sets `R`, `C`.
* No complexity or robustness conclusion is placed in constructor data:
  `columnDensity` and `columnDefect` are plain real-valued readouts of a
  column carrier, carrying no hypotheses.
* Trivial-witness pole for the existential deliverable: `R' = ∅` is excluded
  by `IsEquipartitionedGE R' univ T` whenever `1 ≤ ℓ` and `1 ≤ T`
  (`empty_rows_not_equipartitionedGE`), and `C' = ∅` is excluded by the
  cardinality clause, whose right-hand side is strictly positive
  (`nonempty_of_columns_bound`).  So neither conclusion is satisfiable by the
  empty witness.
-/

namespace EthInapproximability.ParameterizedNP.InheritedContracts

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## The re-exported inherited contract -/

/-- **Checked inherited declaration: typed maximum projection.**

Route-named facade for `EthBridge.member_max_projection`
(`vendor/npc-cc/EthBridge/Induction.lean:569`), restating
`eq:contract-member-max-projection-guards` and
`eq:contract-member-max-projection` of
`sections/D-inherited-contracts.tex` (`app:contract-projection`) verbatim.

The vendored declaration is *consumed*: the body is exactly the inherited
term, so the axiom surface is unchanged (`propext`, `Classical.choice`,
`Quot.sound`). -/
theorem memberMaxProjection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (p ℓ : ℕ) (T : ℕ) (y : ℝ)
    (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ ≤ p) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T)
    (hcols : ((Fintype.card Y : ℝ) ^ p) * y ≤ (C.card : ℝ)) :
    ∃ (R' : Finset (Fin ℓ × X)) (C' : Finset (Fin ℓ → Y)),
      IsEquipartitionedGE R' (Finset.univ : Finset (Fin ℓ)) T ∧
      ((Fintype.card Y : ℝ) ^ ℓ) * Real.rpow y ((ℓ : ℝ) / (p : ℝ)) ≤
        (C'.card : ℝ) ∧
      D (subgame (interlaceFun W ℓ) R' C') ≤
        D (subgame (interlaceFun W p) R C) :=
  EthBridge.member_max_projection W p ℓ T y hℓ1 hℓp hy0 hy1 hX hY R C hrows hcols

/-! ## Normalized column density and logarithmic column defect -/

/-- The normalized column density `y_C = |C| / n^k` with `n = |Y|`, as used in
the derivation of `eq:contract-defect-projection`
(`sections/D-inherited-contracts.tex:236`). -/
noncomputable def columnDensity {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) : ℝ :=
  (C.card : ℝ) / (Fintype.card Y : ℝ) ^ k

/-- The logarithmic column defect `Def(C) = ln (n^k / |C|)` with `n = |Y|`,
fixed at `sections/10-direct-bridge.tex:96` and used in
`eq:contract-defect-projection`. -/
noncomputable def columnDefect {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) : ℝ :=
  Real.log (((Fintype.card Y : ℝ) ^ k) / (C.card : ℝ))

/-! ## Aux-lemma battery

General sanity properties of the two readouts and of the guard/conclusion
shape.  These are the unit tests for the encoding: each is a statement about
arbitrary carriers, not about the pinned construction. -/

/-- **Aux 1 (range).** The normalized density is nonnegative. -/
lemma columnDensity_nonneg {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) : 0 ≤ columnDensity C := by
  unfold columnDensity
  positivity

/-- **Aux 2 (range).** The normalized density of any column carrier is at most
`1` — this is the `y_C ≤ 1` half of the guard `0 < y_C ≤ 1` that the defect
corollary feeds back into the inherited contract. -/
lemma columnDensity_le_one {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) : columnDensity C ≤ 1 := by
  classical
  have hnat : C.card ≤ Fintype.card Y ^ k := by
    have h := Finset.card_le_univ C
    simpa [Finset.card_univ, Fintype.card_fun] using h
  have hcard : (C.card : ℝ) ≤ (Fintype.card Y : ℝ) ^ k := by exact_mod_cast hnat
  unfold columnDensity
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (Fintype.card Y : ℝ) ^ k) with
    hz | hpos
  · rw [← hz, div_zero]
    norm_num
  · rw [div_le_one hpos]
    exact hcard

/-- **Aux 3 (identity).** `Def(C) = -ln (y_C)`: the defect is the negated
logarithm of the normalized density.  This is the identity that turns the
inherited density conclusion into the defect conclusion, and it holds with no
side conditions. -/
lemma columnDefect_eq_neg_log_columnDensity {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) :
    columnDefect C = -Real.log (columnDensity C) := by
  unfold columnDefect columnDensity
  rw [← Real.log_inv, inv_div]

/-- **Aux 4 (sign).** The logarithmic defect is nonnegative, for every column
carrier. -/
lemma columnDefect_nonneg {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) : 0 ≤ columnDefect C := by
  rw [columnDefect_eq_neg_log_columnDensity, neg_nonneg]
  exact Real.log_nonpos (columnDensity_nonneg C) (columnDensity_le_one C)

/-- **Aux 5 (calibration).** The full column carrier has defect exactly `0`;
equivalently, `Def` measures the loss relative to `Y^{[k]}`. -/
lemma columnDefect_univ (Y : Type*) [Fintype Y] (k : ℕ) :
    columnDefect (Finset.univ : Finset (Fin k → Y)) = 0 := by
  classical
  have hcard : ((Finset.univ : Finset (Fin k → Y)).card : ℝ)
      = (Fintype.card Y : ℝ) ^ k := by
    have : (Finset.univ : Finset (Fin k → Y)).card = Fintype.card Y ^ k := by
      simp [Finset.card_univ]
    exact_mod_cast this
  unfold columnDefect
  rw [hcard]
  rcases eq_or_ne ((Fintype.card Y : ℝ) ^ k) 0 with hz | hne
  · rw [hz]
    norm_num
  · rw [div_self hne, Real.log_one]

/-- **Aux 6 (monotonicity).** `Def` is antitone in the column carrier: a
larger column set has a smaller defect. -/
lemma columnDefect_antitone {Y : Type*} [Fintype Y] {k : ℕ}
    {C C' : Finset (Fin k → Y)} (hY : 1 ≤ Fintype.card Y)
    (hC : C.Nonempty) (hsub : C ⊆ C') :
    columnDefect C' ≤ columnDefect C := by
  have hn : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k := by
    have : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
    positivity
  have hCpos : (0 : ℝ) < (C.card : ℝ) := by
    have : 0 < C.card := Finset.card_pos.mpr hC
    exact_mod_cast this
  have hC'pos : (0 : ℝ) < (C'.card : ℝ) := by
    have : 0 < C'.card := Finset.card_pos.mpr (hC.mono hsub)
    exact_mod_cast this
  have hle : (C.card : ℝ) ≤ (C'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  unfold columnDefect
  refine Real.log_le_log (by positivity) ?_
  exact div_le_div_of_nonneg_left (le_of_lt hn) hCpos hle

/-- **Aux 7 (trivial-witness pole, rows).** With a legal row floor `1 ≤ T` and
a nonempty copy index (`1 ≤ ℓ`), the empty row set is *not* equipartitioned,
so the empty witness cannot satisfy the conclusion of
`eq:contract-member-max-projection`. -/
lemma empty_rows_not_equipartitionedGE (X : Type*) (ℓ T : ℕ)
    (hℓ : 1 ≤ ℓ) (hT : 1 ≤ T) :
    ¬ IsEquipartitionedGE (∅ : Finset (Fin ℓ × X))
        (Finset.univ : Finset (Fin ℓ)) T := by
  classical
  intro h
  have hpos : 0 < ℓ := hℓ
  have := h ⟨0, hpos⟩ (Finset.mem_univ _)
  simp at this
  omega

/-- **Aux 8 (general nonemptiness).** Any `(Q,T)`-equipartitioned row set with
`1 ≤ T` over a nonempty index carrier is nonempty. -/
lemma nonempty_of_equipartitionedGE {ι X : Type*} [DecidableEq ι]
    {R : Finset (ι × X)} {Q : Finset ι} {T : ℕ}
    (hT : 1 ≤ T) (hQ : Q.Nonempty) (h : IsEquipartitionedGE R Q T) :
    R.Nonempty := by
  classical
  obtain ⟨q, hq⟩ := hQ
  have hcard : T ≤ (R.filter (fun r => r.1 = q)).card := h q hq
  have hpos : 0 < (R.filter (fun r => r.1 = q)).card := lt_of_lt_of_le hT hcard
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  exact ⟨r, (Finset.mem_filter.mp hr).1⟩

/-- **Aux 9 (trivial-witness pole, columns).** The cardinality clause of
`eq:contract-member-max-projection` has a strictly positive right-hand side
whenever `1 ≤ |Y|` and `0 < y`, so it forces the projected column carrier to
be nonempty. -/
lemma nonempty_of_columns_bound {Y : Type*} [Fintype Y] {ℓ : ℕ}
    {C' : Finset (Fin ℓ → Y)} {y r : ℝ}
    (hY : 1 ≤ Fintype.card Y) (hy0 : 0 < y)
    (h : ((Fintype.card Y : ℝ) ^ ℓ) * Real.rpow y r ≤ (C'.card : ℝ)) :
    C'.Nonempty := by
  have hn : (0 : ℝ) < (Fintype.card Y : ℝ) ^ ℓ := by
    have : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
    positivity
  have hrpow : (0 : ℝ) < Real.rpow y r := Real.rpow_pos_of_pos hy0 r
  have hpos : (0 : ℝ) < (C'.card : ℝ) := lt_of_lt_of_le (by positivity) h
  have : 0 < C'.card := by exact_mod_cast hpos
  exact Finset.card_pos.mp this

/-! ## The elementary defect conversion -/

/-- **Defect form of the fixed-parent maximum projection**
(`eq:contract-defect-projection`,
`sections/D-inherited-contracts.tex:244`).

Put `n = |Y|` and assume `C ≠ ∅`.  Applying `memberMaxProjection` at the
*actual* normalized density `y_C = |C| / n^p` — which the guards permit because
`C ⊆ Y^{[p]}` and `n ≥ 1` give `0 < y_C ≤ 1` — returns a projected column
carrier of normalized density at least `y_C^{ℓ/p}`; monotonicity of `ln`
followed by `ln (rpow y_C (ℓ/p)) = (ℓ/p) ln y_C` yields

`Def(C') ≤ (ℓ/p) * Def(C)`.

This conversion introduces no additional projection lemma and no additional
choice of witnesses: the row set, the column set, and the fixed-parent
complexity comparison all come from the single application of the inherited
declaration. -/
theorem defectProjection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (p ℓ : ℕ) (T : ℕ)
    (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ ≤ p)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T)
    (hC : C.Nonempty) :
    ∃ (R' : Finset (Fin ℓ × X)) (C' : Finset (Fin ℓ → Y)),
      IsEquipartitionedGE R' (Finset.univ : Finset (Fin ℓ)) T ∧
      C'.Nonempty ∧
      columnDefect C' ≤ ((ℓ : ℝ) / (p : ℝ)) * columnDefect C ∧
      D (subgame (interlaceFun W ℓ) R' C') ≤
        D (subgame (interlaceFun W p) R C) := by
  classical
  have hn : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnp : (0 : ℝ) < (Fintype.card Y : ℝ) ^ p := by positivity
  have hnl : (0 : ℝ) < (Fintype.card Y : ℝ) ^ ℓ := by positivity
  have hCpos : (0 : ℝ) < (C.card : ℝ) := by
    have : 0 < C.card := Finset.card_pos.mpr hC
    exact_mod_cast this
  -- The actual normalized density `y_C`, and its guard bounds.
  set y : ℝ := columnDensity C with hy_def
  have hy0 : 0 < y := by
    rw [hy_def]
    unfold columnDensity
    exact div_pos hCpos hnp
  have hy1 : y ≤ 1 := columnDensity_le_one C
  have hcols : ((Fintype.card Y : ℝ) ^ p) * y ≤ (C.card : ℝ) := by
    rw [hy_def]
    unfold columnDensity
    rw [mul_div_cancel₀ _ (ne_of_gt hnp)]
  obtain ⟨R', C', hR', hC'card, hD⟩ :=
    memberMaxProjection W p ℓ T y hℓ1 hℓp hy0 hy1 hX hY R C hrows hcols
  have hC'ne : C'.Nonempty := nonempty_of_columns_bound hY hy0 hC'card
  refine ⟨R', C', hR', hC'ne, ?_, hD⟩
  -- Density of the child dominates `y ^ (ℓ / p)`.
  have hrpow_eq : Real.rpow y ((ℓ : ℝ) / (p : ℝ)) = y ^ ((ℓ : ℝ) / (p : ℝ)) := rfl
  have hdens : y ^ ((ℓ : ℝ) / (p : ℝ)) ≤ columnDensity C' := by
    unfold columnDensity
    rw [le_div_iff₀ hnl, mul_comm, ← hrpow_eq]
    exact hC'card
  have hrpow_pos : (0 : ℝ) < y ^ ((ℓ : ℝ) / (p : ℝ)) :=
    Real.rpow_pos_of_pos hy0 _
  have hlog := Real.log_le_log hrpow_pos hdens
  rw [Real.log_rpow hy0] at hlog
  -- Convert both sides to defects.
  rw [columnDefect_eq_neg_log_columnDensity, columnDefect_eq_neg_log_columnDensity,
    ← hy_def]
  linarith

end EthInapproximability.ParameterizedNP.InheritedContracts

/-! ## Non-vacuity witness

LANE-GATE 3: the guard bundle of `eq:contract-member-max-projection-guards` is
exhibited at **legal, nondegenerate** parameter values — a strict projection
`ℓ = 1 < 2 = p` (so the `ℓ = p` equality case is not what is being tested), a
row floor `T = 2 ≥ 1` that genuinely constrains each copy, a density
`y = 1/2` strictly inside `(0, 1]`, and carriers with `|X| = |Y| = 2 ≥ 1`.
The consequent is nondegenerate too: both returned carriers are nonempty.

The same discipline is applied to `defectProjection` separately, because a
witness at `C = univ` would be degenerate for *that* statement even though it
is legal for the guard bundle: there `Def(C) = 0` (`columnDefect_univ`), the
conclusion collapses to `Def(C') ≤ 0`, and the load-bearing coefficient `ℓ/p`
multiplies zero.  `defectProjection_nondegenerate` therefore pins the strict
sub-carrier `lowColumns = {c ∈ Bool^{[2]} | c 0 = false}`, for which
`Def(lowColumns) = ln 2 > 0` is carried as an explicit conjunct, so the
inequality it asserts is `Def(C') ≤ (1/2) ln 2`, a nonvacuous real bound. -/

namespace EthInapproximability.ParameterizedNP.InheritedContracts

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-- Every copy of the full two-copy row carrier over `Bool` has a fibre of
size `2`, so the row floor `T = 2` is met (and is not vacuous). -/
lemma univRows_equipartitionedGE :
    IsEquipartitionedGE (Finset.univ : Finset (Fin 2 × Bool))
      (Finset.univ : Finset (Fin 2)) 2 := by
  intro q _
  fin_cases q <;> decide

/-- **Aux 10 (non-vacuity).** The inherited contract fires at legal,
nondegenerate parameters and returns nonempty witnesses. -/
theorem memberMaxProjection_nondegenerate :
    ∃ (R' : Finset (Fin 1 × Bool)) (C' : Finset (Fin 1 → Bool)),
      IsEquipartitionedGE R' (Finset.univ : Finset (Fin 1)) 2 ∧
      R'.Nonempty ∧ C'.Nonempty ∧
      D (subgame (interlaceFun (fun a b : Bool => a && b) 1) R' C') ≤
        D (subgame (interlaceFun (fun a b : Bool => a && b) 2)
            (Finset.univ : Finset (Fin 2 × Bool))
            (Finset.univ : Finset (Fin 2 → Bool))) := by
  classical
  have hcardY : Fintype.card Bool = 2 := by simp
  have hcardC : (Finset.univ : Finset (Fin 2 → Bool)).card = 4 := by
    simp [Finset.card_univ]
  have hrows := univRows_equipartitionedGE
  have hcols : ((Fintype.card Bool : ℝ) ^ 2) * (1 / 2 : ℝ) ≤
      ((Finset.univ : Finset (Fin 2 → Bool)).card : ℝ) := by
    rw [hcardY, hcardC]
    norm_num
  obtain ⟨R', C', hR', hC'card, hD⟩ :=
    memberMaxProjection (fun a b : Bool => a && b) 2 1 2 (1 / 2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp) (by simp)
      (Finset.univ : Finset (Fin 2 × Bool))
      (Finset.univ : Finset (Fin 2 → Bool)) hrows hcols
  refine ⟨R', C', hR', ?_, ?_, hD⟩
  · exact nonempty_of_equipartitionedGE (by norm_num) ⟨0, Finset.mem_univ _⟩ hR'
  · exact nonempty_of_columns_bound (by simp) (by norm_num) hC'card

/-! ### Non-vacuity witness for the defect conversion

`defectProjection` is an existential deliverable whose *content* lives in the
real inequality `Def(C') ≤ (ℓ/p) Def(C)`.  A witness at `C = Y^{[p]}` would
satisfy the statement while testing nothing: `Def(univ) = 0`, so the asserted
bound degenerates to `Def(C') ≤ 0` and the coefficient `ℓ/p` is unwitnessed.
The witness below therefore uses a *strict* sub-carrier with positive defect. -/

/-- The pinned strict column sub-carrier `{c ∈ Bool^{[2]} | c 0 = false}`.
It is a proper subset of `Y^{[p]}` at `Y = Bool`, `p = 2`, so its normalized
density is `2/4 = 1/2` and its logarithmic defect is `ln 2 > 0`. -/
def lowColumns : Finset (Fin 2 → Bool) :=
  Finset.univ.filter (fun c => c 0 = false)

/-- The pinned sub-carrier has exactly two columns (the free coordinate is
slot `1`), hence normalized density `1/2` against `|Bool|^2 = 4`. -/
lemma lowColumns_card : lowColumns.card = 2 := by decide

lemma lowColumns_nonempty : lowColumns.Nonempty :=
  Finset.card_pos.mp (by rw [lowColumns_card]; norm_num)

/-- The pinned sub-carrier has **strictly positive** defect, `Def = ln 2`.
This is the conjunct that makes `defectProjection_nondegenerate` a real test of
the coefficient `ℓ/p` rather than a restatement of `0 ≤ 0`. -/
lemma lowColumns_defect_pos : 0 < columnDefect lowColumns := by
  have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
  have hc : ((lowColumns.card : ℕ) : ℝ) = 2 := by
    rw [lowColumns_card]; norm_num
  unfold columnDefect
  rw [hY, hc]
  have h4 : ((2 : ℝ) ^ (2 : ℕ)) / 2 = 2 := by norm_num
  rw [h4]
  exact Real.log_pos (by norm_num)

/-- **Aux 11 (non-vacuity, defect form).** `defectProjection` fires at legal,
nondegenerate parameters — strict projection `ℓ = 1 < 2 = p`, row floor
`T = 2`, `|X| = |Y| = 2`, parent rows `R = univ` and parent columns the strict
sub-carrier `lowColumns` — and the parent defect appearing on the right-hand
side is strictly positive, so the asserted bound is `Def(C') ≤ (1/2) ln 2`. -/
theorem defectProjection_nondegenerate :
    ∃ (R' : Finset (Fin 1 × Bool)) (C' : Finset (Fin 1 → Bool)),
      IsEquipartitionedGE R' (Finset.univ : Finset (Fin 1)) 2 ∧
      R'.Nonempty ∧ C'.Nonempty ∧
      0 < columnDefect lowColumns ∧
      columnDefect C' ≤ ((1 : ℝ) / (2 : ℝ)) * columnDefect lowColumns ∧
      D (subgame (interlaceFun (fun a b : Bool => a && b) 1) R' C') ≤
        D (subgame (interlaceFun (fun a b : Bool => a && b) 2)
            (Finset.univ : Finset (Fin 2 × Bool)) lowColumns) := by
  classical
  obtain ⟨R', C', hR', hC'ne, hdef, hD⟩ :=
    defectProjection (fun a b : Bool => a && b) 2 1 2
      (by norm_num) (by norm_num) (by simp) (by simp)
      (Finset.univ : Finset (Fin 2 × Bool)) lowColumns
      univRows_equipartitionedGE lowColumns_nonempty
  refine ⟨R', C', hR', ?_, hC'ne, lowColumns_defect_pos, ?_, hD⟩
  · exact nonempty_of_equipartitionedGE (by norm_num) ⟨0, Finset.mem_univ _⟩ hR'
  · simpa using hdef

end EthInapproximability.ParameterizedNP.InheritedContracts

/-! # Extension: specified-coordinate projection and bracket monotonicity

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).

This block extends the `INHERIT-001` facade of `app:contract-projection` with
the two remaining *checked inherited declarations* of that subsection.  Every
statement above this line is unchanged.

Autoformalization anchors (frozen release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`):

* `sections/D-inherited-contracts.tex`, `app:contract-projection` (line 150):
  * paragraph "Checked inherited declaration: bracket monotonicity"
    (line 157), guards **and** conclusion at `eq:contract-monotonicity`
    (line 172) — transcribed as `bracketMonotonicity`;
  * paragraph "Checked inherited declaration: specified-coordinate
    projection" (line 250), guards and conclusion at lines 250--265 —
    transcribed as `coordProjection`.  The two provenance sentences at
    lines 262--265 ("Every row in `R'` comes from the corresponding
    `e`-coordinate fibre of `R`, and every column in `C'` is the
    `e`-projection of an actual column in `C`.  These provenance clauses are
    part of the conclusion.") are **conclusion content**: they are carried
    here as the second and third conjuncts and are never droppable.
* `sections/D-inherited-contracts.tex`, `app:contract-notation` (line 45),
  lines 76--81, fixes the flattened readout
  `D_M(p,x,z) := DSet (bracket M p x z)` used by
  `eq:contract-monotonicity`, and lines 113--119 fix
  `EquipGE(R,Q,T) := NPCC.IsEquipartitionedGE R Q T`.
* Consumers in the frozen paper: `sections/10-direct-bridge.tex` line 121
  ("the inherited specified-coordinate projection lemma preserves its
  normalized density"), and `sections/03-preliminaries.tex` line 378, the
  `sec:inherited-interfaces` index row naming `lem:mono` and
  `lem:coord-projection`.

Reader counterparts (`routes/parameterized-np/reader-facing/`):

* `bracketMonotonicity`: `sections/02-preliminaries.tex`, §"The inherited
  classical engine" (line 111), `prop:paper-projection-facts` (line 120),
  **item 2** (lines 126--131).  That proposition has exactly three items —
  one-copy transpose, this monotonicity, and the *maximum* projection — and
  item 2 is the reader form of `eq:contract-monotonicity`.  None of its items
  is the specified-coordinate projection; item 3 is already the reader
  counterpart of the separately banked `memberMaxProjection`, so no reader
  item is shared between two declarations.
* `coordProjection`: `sections/B-bridge-details.tex`, `app:bridge-details`
  (line 2), §"Defect and projection" (line 12), lines 18--21 — "Projection to
  a specified coordinate set does not increase defect.  For every
  \(1\le p'\le p\), entropy averaging supplies a \(p'\)-coordinate projection
  of defect at most \((p'/p)\Delta_p(K)\)" — together with the
  least-representative and literal-smaller-interlace sentences at lines
  29--32.  The reader states the *defect* consequence of the projection; the
  autoformalization paragraph at `D-inherited-contracts.tex:250` states the
  underlying extraction-data contract that this facade transcribes.
* `sections/04-bridge.tex`, `thm:near-to-robust` (line 82) — the consumer.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Status and dependencies

* Proof status: **inherited** for both `coordProjection` (a re-export of the
  kernel-checked vendored declaration `NPCC.coord_projection`,
  `vendor/npc-cc/NPCC/CoordProjection.lean:26`) and `bracketMonotonicity` (a
  re-export of `Workspace.BracketLemmas.monotonicity`,
  `vendor/npc-cc/Workspace/BracketLemmas.lean:890`).  Both vendored terms are
  *consumed*, never re-proved and never widened.  The surrounding aux lemmas
  and non-vacuity witnesses are **new (elementary)**.
* Imports: unchanged — `EthInapproximability.Prelude` only.
  `Workspace.BracketLemmas` is already transitively in scope through
  `LegacyNPCC.Core` (`NPCC.Transfer` -> `NPCC.Engine` -> `Workspace.Appendix`),
  and `NPCC.CoordProjection` through `LegacyNPCC.Bridge`
  (`EthBridge.Entry`).  `LegacyNPCC.Stage12` is still **not** imported, so the
  AGHP balanced-family axiom stays out of scope.
* External adapters: none.  Nothing here is axiomatized.
* Axiom surface (Appendix D lines 30--35, and `#print axioms` in
  `tools/AxiomAudit.lean`): `propext`, `Classical.choice`, `Quot.sound`.
* Ledger row: `INHERIT-001`; consumed by `BRIDGE-001`.

## Faithfulness notes (mechanical rules M1--M10)

* `bracketMonotonicity` restates the vendored type verbatim: binder order
  `M p' p x' x z' z`, the three guard pairs `1 <= p' <= p`,
  `0 < x' <= x <= 1`, `0 < z' <= z <= 1`, and the conclusion
  `D_M(p',x',z') <= D_M(p,x,z)` in the flattened `DSet`/`bracket` readout that
  `app:contract-notation` pins.  The paper's column-density letter is `z`; the
  vendored declaration spells it `y`.  Only the letter differs — the facade
  passes its `z'`, `z` into the vendored `y'`, `y` slots positionally.
* `coordProjection` restates the vendored type verbatim: the guard `0 < r`,
  the coordinate set `Q` with the *explicit* equivalence
  `e : Fin r ≃ {q // q ∈ Q}` (whose existence pins `r = |Q|`), the three
  hypotheses `EquipGE(R,Q,T)`, `⌈|Y|^p z⌉ <= |C|`, `⌈|X| x⌉ <= T` in the
  paper's order, and the exact three-conjunct conclusion.  The implicit
  binders of the vendored statement are made explicit here; nothing is added,
  dropped, or reordered.
* No complexity or robustness conclusion is placed in constructor data:
  `frontQ`, `frontEquiv`, `frontRows`, and `andMat` are plain finite data with
  no hypotheses attached.
* Trivial-witness poles.  For `coordProjection` the deliverable is an
  existential whose last two conjuncts are universally quantified over the
  returned carriers, so an *empty* `RC'` would satisfy them vacuously; the
  bracket-membership conjunct is what excludes that, and
  `bracketGE_rows_nonempty` / `bracketGE_cols_nonempty` turn it into explicit
  nonemptiness at legal parameters.  For `bracketMonotonicity` the pole is the
  degenerate matrix: the vendored proof returns `DSet = sInf ∅ = 0` on the
  left whenever `M.m = 0` or `M.n = 0`, so a witness must pin a matrix with
  `m, n >= 1` *and* exhibit a member of the left bracket.
-/

namespace EthInapproximability.ParameterizedNP.InheritedContracts

open NPCC
open Workspace.Types.BoolMat
open Workspace.Types.Bracket
open Workspace.Types.Extract
open Workspace.Types.Interlace
open Workspace.Types.Equipartition
open Workspace.Types.MatComplexity

/-! ## Re-export 1: bracket monotonicity (`eq:contract-monotonicity`) -/

/-- **Checked inherited declaration: bracket monotonicity**
(`sections/D-inherited-contracts.tex`, paragraph at line 157, guards and
conclusion `eq:contract-monotonicity` at line 172).

Route-named facade for `Workspace.BracketLemmas.monotonicity`
(`vendor/npc-cc/Workspace/BracketLemmas.lean:890`).  The flattened readout
`D_M(p,x,z) = DSet (bracket M p x z)` is the one fixed at
`sections/D-inherited-contracts.tex:76-81`.

The vendored declaration is *consumed*: the body is exactly the inherited
term, so the axiom surface is unchanged. -/
theorem bracketMonotonicity (M : BoolMat) (p' p : ℕ) (x' x z' z : ℝ)
    (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hx'0 : 0 < x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hz'0 : 0 < z') (hz'z : z' ≤ z) (hz1 : z ≤ 1) :
    DSet (bracket M p' x' z') ≤ DSet (bracket M p x z) :=
  Workspace.BracketLemmas.monotonicity M p' p x' x z' z
    hp' hpp hx'0 hx'x hx1 hz'0 hz'z hz1

/-! ## Re-export 2: specified-coordinate projection -/

/-- **Checked inherited declaration: specified-coordinate projection**
(`sections/D-inherited-contracts.tex`, paragraph at line 250; guards at lines
256--260, conclusion with its two provenance clauses at lines 261--265).

Route-named facade for `NPCC.coord_projection`
(`vendor/npc-cc/NPCC/CoordProjection.lean:26`).

The paper's sentence "These provenance clauses are part of the conclusion"
is honoured literally: the second conjunct says every returned row `(j, v)`
arises from the ambient row `((e j).val, v)` of `R` — i.e. from the
`e`-coordinate fibre of `R` — and the third says every returned column agrees,
on all of `Q` read through `e`, with an actual column of `C`.  Neither may be
dropped, and neither may be weakened to a cardinality statement.

The vendored declaration is *consumed*: the body is exactly the inherited
term.  Only the implicit/explicit status of the binders differs, and the
column-density letter is the paper's `z` rather than the vendored `y`. -/
theorem coordProjection {X Y : Type*} [Fintype X] [Fintype Y]
    (p r : ℕ) (hr : 0 < r) (Q : Finset (Fin p)) (e : Fin r ≃ {q // q ∈ Q})
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y)) (T : ℕ) (x z : ℝ)
    (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ p) * z⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T) :
    ∃ RC' : Finset (Fin r × X) × Finset (Fin r → Y),
      RC' ∈ bracketGE X Y r x z ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c' ∈ RC'.2, ∃ c ∈ C, ∀ j : Fin r, c' j = c (e j).val) :=
  NPCC.coord_projection hr e hrow hcol hxT

/-! ## Aux-lemma battery for the extension

General properties of the bracket-membership conjunct and of the two
provenance conjuncts, plus the two derived monotonicity specializations.  Each
is a statement about arbitrary carriers, not about the pinned witnesses. -/

/-- **Aux 12 (general, nonemptiness of the returned row set).**  Bracket
membership forces a nonempty row carrier once the row floor is at least one
and there is at least one copy.  This is what stops the row-provenance
conjunct of `coordProjection` from being vacuously true. -/
lemma bracketGE_rows_nonempty {X Y : Type*} [Fintype X] [Fintype Y] {r : ℕ}
    {RC : Finset (Fin r × X) × Finset (Fin r → Y)} {x z : ℝ}
    (hr : 0 < r) (hx : 1 ≤ ⌈(Fintype.card X : ℝ) * x⌉₊)
    (h : RC ∈ bracketGE X Y r x z) : RC.1.Nonempty :=
  nonempty_of_equipartitionedGE hx ⟨⟨0, hr⟩, Finset.mem_univ _⟩ h.1

/-- **Aux 13 (general, nonemptiness of the returned column set).**  Bracket
membership forces a nonempty column carrier once the column floor is at least
one.  This is what stops the column-provenance conjunct of `coordProjection`
from being vacuously true. -/
lemma bracketGE_cols_nonempty {X Y : Type*} [Fintype X] [Fintype Y] {r : ℕ}
    {RC : Finset (Fin r × X) × Finset (Fin r → Y)} {x z : ℝ}
    (hz : 1 ≤ ⌈((Fintype.card Y : ℝ) ^ r) * z⌉₊)
    (h : RC ∈ bracketGE X Y r x z) : RC.2.Nonempty :=
  Finset.card_pos.mp (lt_of_lt_of_le hz h.2)

/-- **Aux 14 (general, row provenance is an inclusion).**  The row-provenance
conjunct of `coordProjection` says exactly that the `e`-relabelling of the
returned row set lands inside the parent row set `R`.  Proving this equivalence
is the unit test that the conjunct means what the paper's sentence at
`sections/D-inherited-contracts.tex:262` says. -/
lemma coordProjection_rows_subset_image {X : Type*} {p r : ℕ}
    {Q : Finset (Fin p)} (e : Fin r ≃ {q // q ∈ Q})
    {R : Finset (Fin p × X)} {Rows : Finset (Fin r × X)}
    (h : ∀ a ∈ Rows, ((e a.1).val, a.2) ∈ R) :
    (fun a : Fin r × X => (((e a.1).val : Fin p), a.2)) ''
        (Rows : Set (Fin r × X)) ⊆ (R : Set (Fin p × X)) := by
  rintro b ⟨a, ha, rfl⟩
  exact Finset.mem_coe.mpr (h a (Finset.mem_coe.mp ha))

/-- **Aux 15 (general, column provenance is an inclusion).**  The
column-provenance conjunct of `coordProjection` says exactly that the returned
column set is contained in the `e`-projection image of the parent column set
`C`.  Same unit-test role as Aux 14, for the sentence at
`sections/D-inherited-contracts.tex:263`. -/
lemma coordProjection_cols_subset_image {Y : Type*} {p r : ℕ}
    {Q : Finset (Fin p)} (e : Fin r ≃ {q // q ∈ Q})
    {C : Finset (Fin p → Y)} {Cols : Finset (Fin r → Y)}
    (h : ∀ c' ∈ Cols, ∃ c ∈ C, ∀ j : Fin r, c' j = c (e j).val) :
    (Cols : Set (Fin r → Y)) ⊆
      (fun (c : Fin p → Y) (j : Fin r) => c (e j).val) ''
        (C : Set (Fin p → Y)) := by
  intro c' hc'
  obtain ⟨c, hc, hagree⟩ := h c' (Finset.mem_coe.mp hc')
  exact ⟨c, Finset.mem_coe.mpr hc, (funext fun j => (hagree j).symm)⟩

/-- **Aux 16 (general, copy-count specialization).**  The pure copy-count half
of `eq:contract-monotonicity`, which the frozen paper notes is *private* in the
dependency (`sections/D-inherited-contracts.tex:174-176`).  It is recovered
here from the public two-sided statement at fixed densities. -/
lemma bracketMonotonicity_copies (M : BoolMat) (p' p : ℕ) (x z : ℝ)
    (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    DSet (bracket M p' x z) ≤ DSet (bracket M p x z) :=
  bracketMonotonicity M p' p x x z z hp' hpp hx0 le_rfl hx1 hz0 le_rfl hz1

/-- **Aux 17 (general, same-copy density weakening).**  The density half of
`eq:contract-monotonicity` at a fixed copy count. -/
lemma bracketMonotonicity_density (M : BoolMat) (p : ℕ) (x' x z' z : ℝ)
    (hp : 1 ≤ p) (hx'0 : 0 < x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hz'0 : 0 < z') (hz'z : z' ≤ z) (hz1 : z ≤ 1) :
    DSet (bracket M p x' z') ≤ DSet (bracket M p x z) :=
  bracketMonotonicity M p p x' x z' z hp le_rfl hx'0 hx'x hx1 hz'0 hz'z hz1

/-- **Aux 18 (general, composition).**  Two monotonicity steps compose, with
the intermediate guards derived rather than assumed.  This is the round-trip
test that the guard bundle of `eq:contract-monotonicity` is closed under
chaining, which is how the defect induction uses it. -/
lemma bracketMonotonicity_trans (M : BoolMat) (p'' p' p : ℕ)
    (x'' x' x z'' z' z : ℝ)
    (hp'' : 1 ≤ p'') (hp''p' : p'' ≤ p') (hp'p : p' ≤ p)
    (hx''0 : 0 < x'') (hx''x' : x'' ≤ x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hz''0 : 0 < z'') (hz''z' : z'' ≤ z') (hz'z : z' ≤ z) (hz1 : z ≤ 1) :
    DSet (bracket M p'' x'' z'') ≤ DSet (bracket M p x z) :=
  le_trans
    (bracketMonotonicity M p'' p' x'' x' z'' z' hp'' hp''p' hx''0 hx''x'
      (le_trans hx'x hx1) hz''0 hz''z' (le_trans hz'z hz1))
    (bracketMonotonicity M p' p x' x z' z (le_trans hp'' hp''p') hp'p
      (lt_of_lt_of_le hx''0 hx''x') hx'x hx1
      (lt_of_lt_of_le hz''0 hz''z') hz'z hz1)

/-! ## Non-vacuity witness 1: specified-coordinate projection

LANE-GATE 3.  The witness is taken at a **proper-subset** instance in every
slot that the contract can degenerate on:

* the coordinate set is `Q = {0} ⊊ [2]`, so the projection genuinely forgets
  copy `1` (a witness at `Q = [p]` would test no coordinate selection at all);
* the parent row set is `frontRows = {(0, false)} ⊊ [2] × Bool`, so the row
  provenance conjunct is *restrictive*: it forces `a.2 = false` on every
  returned row, which the trivial "all rows" witness violates;
* the parent column set is `lowColumns = {c ∈ Bool^{[2]} : c 0 = false}`, a
  proper subset of `Bool^{[2]}`, and `Q = {0}` reads exactly the pinned
  coordinate, so the column provenance conjunct is restrictive too: it forces
  `c' 0 = false` on every returned column, which the trivial "all columns"
  witness violates;
* both returned carriers are proved **nonempty**, so neither universally
  quantified provenance conjunct is vacuously satisfied.

All guard values are legal: `r = 1 > 0`, `T = 1`, `x = z = 1/2 ∈ (0,1]`,
`|X| = |Y| = 2 ≥ 1`, `⌈|Y|^2 z⌉ = 2 ≤ |lowColumns| = 2`, and
`⌈|X| x⌉ = 1 ≤ T = 1` — both ceiling guards are tight rather than slack. -/

/-- The pinned coordinate set `Q = {0}`, a **proper** subset of the two
ambient copies `[2]`. -/
def frontQ : Finset (Fin 2) := {0}

/-- `frontQ` is a proper subset of `[2]`: copy `1` is not selected. -/
lemma one_not_mem_frontQ : (1 : Fin 2) ∉ frontQ := by decide

/-- The explicit equivalence `[1] ≃ frontQ` that
`sections/D-inherited-contracts.tex:252-255` demands (its existence pins
`r = |Q| = 1`). -/
def frontEquiv : Fin 1 ≃ {q : Fin 2 // q ∈ frontQ} where
  toFun := fun _ => ⟨0, by decide⟩
  invFun := fun _ => 0
  left_inv := by intro j; fin_cases j; rfl
  right_inv := by
    rintro ⟨q, hq⟩
    have hq0 : q = 0 := by simpa [frontQ] using hq
    subst hq0
    rfl

@[simp] lemma frontEquiv_apply (j : Fin 1) : (frontEquiv j).val = (0 : Fin 2) :=
  rfl

/-- The pinned parent row set `{(0, false)}`, a **proper** subset of
`[2] × Bool` that lives entirely over copy `0` and uses only one of the two
`X`-values. -/
def frontRows : Finset (Fin 2 × Bool) := {(0, false)}

/-- The pinned parent row set is `(Q, 1)`-equipartitioned, at the tight floor
`T = 1`. -/
lemma frontRows_equipartitionedGE : IsEquipartitionedGE frontRows frontQ 1 := by
  intro q hq
  have hq0 : q = 0 := by simpa [frontQ] using hq
  subst hq0
  decide

/-- **Aux 19 (non-vacuity, specified-coordinate projection).**
`coordProjection` fires at legal, nondegenerate parameters and returns
**nonempty** carriers whose provenance conjuncts are genuinely restrictive:
every returned row carries `X`-value `false` (because the parent row set is
the proper subset `frontRows`), and every returned column reads `false` at the
selected coordinate (because the parent column set is the proper subset
`lowColumns` and `Q = {0}`). -/
theorem coordProjection_nondegenerate :
    ∃ RC' : Finset (Fin 1 × Bool) × Finset (Fin 1 → Bool),
      RC' ∈ bracketGE Bool Bool 1 (1 / 2 : ℝ) (1 / 2 : ℝ) ∧
      RC'.1.Nonempty ∧ RC'.2.Nonempty ∧
      (∀ a ∈ RC'.1, ((frontEquiv a.1).val, a.2) ∈ frontRows) ∧
      (∀ c' ∈ RC'.2, ∃ c ∈ lowColumns,
        ∀ j : Fin 1, c' j = c (frontEquiv j).val) ∧
      (∀ a ∈ RC'.1, a.2 = false) ∧
      (∀ c' ∈ RC'.2, c' 0 = false) := by
  classical
  have hcardY : (Fintype.card Bool : ℝ) = 2 := by simp
  have hcol : ⌈((Fintype.card Bool : ℝ) ^ 2) * (1 / 2 : ℝ)⌉₊ ≤ lowColumns.card := by
    rw [Nat.ceil_le, lowColumns_card, hcardY]
    norm_num
  have hxT : ⌈(Fintype.card Bool : ℝ) * (1 / 2 : ℝ)⌉₊ ≤ 1 := by
    rw [Nat.ceil_le, hcardY]
    norm_num
  obtain ⟨RC', hmem, hrows, hcols⟩ :=
    coordProjection (X := Bool) (Y := Bool) 2 1 (by norm_num) frontQ frontEquiv
      frontRows lowColumns 1 (1 / 2 : ℝ) (1 / 2 : ℝ)
      frontRows_equipartitionedGE hcol hxT
  have hrowfloor : 1 ≤ ⌈(Fintype.card Bool : ℝ) * (1 / 2 : ℝ)⌉₊ := by
    have : (0 : ℕ) < ⌈(Fintype.card Bool : ℝ) * (1 / 2 : ℝ)⌉₊ :=
      Nat.lt_ceil.mpr (by rw [hcardY]; norm_num)
    omega
  have hcolfloor : 1 ≤ ⌈((Fintype.card Bool : ℝ) ^ 1) * (1 / 2 : ℝ)⌉₊ := by
    have : (0 : ℕ) < ⌈((Fintype.card Bool : ℝ) ^ 1) * (1 / 2 : ℝ)⌉₊ :=
      Nat.lt_ceil.mpr (by rw [hcardY]; norm_num)
    omega
  refine ⟨RC', hmem,
    bracketGE_rows_nonempty (by norm_num) hrowfloor hmem,
    bracketGE_cols_nonempty hcolfloor hmem,
    hrows, hcols, ?_, ?_⟩
  · intro a ha
    have hmemR := hrows a ha
    rw [frontRows, Finset.mem_singleton] at hmemR
    simpa using congrArg Prod.snd hmemR
  · intro c' hc'
    obtain ⟨c, hc, hagree⟩ := hcols c' hc'
    have hc0 : c 0 = false := by
      rw [lowColumns, Finset.mem_filter] at hc
      exact hc.2
    rw [hagree 0, frontEquiv_apply]
    exact hc0

/-! ## Non-vacuity witness 2: bracket monotonicity

LANE-GATE 3.  The pole for `eq:contract-monotonicity` is not the guard bundle
(which is satisfiable at `p' = p`, `x' = x`, `z' = z`, where the conclusion is
a reflexivity) but the **degenerate matrix**: the vendored proof's first two
branches return `DSet (bracket M p' x' z') = sInf ∅ = 0` whenever `M.m = 0` or
`M.n = 0`, and then the inequality holds for the empty reason `0 ≤ n`.

The witness below is therefore taken at a **strict** instance with a
nondegenerate matrix, and carries the facts that make it strict and
nondegenerate as explicit conjuncts:

* `p' = 1 < 2 = p`, `x' = 1/4 < 1/2 = x`, `z' = 1/4 < 1/2 = z` — all three
  guard pairs are strict, so no side of the inequality is a copy of the other;
* `andMat` is a `2 × 2` matrix (so neither degenerate branch of the vendored
  proof applies) and is *nonconstant*, so it is not the trivial all-zero game;
* the left bracket is **nonempty**, so `DSet` on the left is an infimum over a
  nonempty achievable-cost set rather than the `sInf ∅ = 0` degeneracy. -/

/-- The pinned nondegenerate parent matrix: the `2 × 2` AND matrix. -/
def andMat : BoolMat where
  m := 2
  n := 2
  e := fun i j => decide (i = 1 ∧ j = 1)

@[simp] lemma andMat_m : andMat.m = 2 := rfl

@[simp] lemma andMat_n : andMat.n = 2 := rfl

/-- `andMat` is nonconstant, hence not the trivial game whose complexity
readout carries no information. -/
lemma andMat_nonconstant :
    ∃ i j i' j' : Fin 2, andMat.e i j ≠ andMat.e i' j' := by
  exact ⟨1, 1, 0, 0, by decide⟩

/-- The one ceiling readout used by the pinned monotonicity witness:
`⌈m x'⌉ = ⌈n^{p'} z'⌉ = ⌈1/2⌉ = 1` at `m = n = 2`, `p' = 1`,
`x' = z' = 1/4`. -/
lemma ceil_one_half : ⌈(1 / 2 : ℝ)⌉₊ = 1 := by
  have h1 : ⌈(1 / 2 : ℝ)⌉₊ ≤ 1 := Nat.ceil_le.mpr (by norm_num)
  have h2 : (0 : ℕ) < ⌈(1 / 2 : ℝ)⌉₊ := Nat.lt_ceil.mpr (by norm_num)
  omega

/-- **Aux 20 (non-vacuity, left bracket inhabited).**  The left-hand bracket of
the pinned monotonicity instance is nonempty: `R = {0}` retains
`⌈m x'⌉ = 1` row in the single block and `C = {0}` retains
`⌈n^{p'} z'⌉ = 1` column.  Hence `DSet` on the left is a genuine minimum, not
`sInf ∅`. -/
lemma andMat_left_bracket_nonempty :
    (bracket andMat 1 (1 / 4 : ℝ) (1 / 4 : ℝ)).Nonempty := by
  refine ⟨extract (interlace andMat 1) {0} {0},
    {0}, {0}, ?_, ?_, ?_, ?_, rfl⟩
  · decide
  · intro γ hγ
    interval_cases γ
    have hT : ⌈((andMat.m : ℝ) * (1 / 4 : ℝ))⌉₊ = 1 := by
      have : ((andMat.m : ℝ) * (1 / 4 : ℝ)) = (1 / 2 : ℝ) := by
        simp only [andMat_m]
        norm_num
      rw [this, ceil_one_half]
    rw [hT]
    decide
  · decide
  · have h : (((andMat.n ^ 1 : ℕ) : ℝ) * (1 / 4 : ℝ)) = (1 / 2 : ℝ) := by
      simp only [andMat_n]
      norm_num
    rw [h, ceil_one_half]
    decide

/-- **Aux 21 (non-vacuity, bracket monotonicity).**  `bracketMonotonicity`
fires at a **strict** legal instance over a nondegenerate matrix, with the
left-hand bracket inhabited. -/
theorem bracketMonotonicity_nondegenerate :
    (bracket andMat 1 (1 / 4 : ℝ) (1 / 4 : ℝ)).Nonempty ∧
    (1 : ℕ) < 2 ∧ (1 / 4 : ℝ) < 1 / 2 ∧
    (∃ i j i' j' : Fin 2, andMat.e i j ≠ andMat.e i' j') ∧
    DSet (bracket andMat 1 (1 / 4 : ℝ) (1 / 4 : ℝ)) ≤
      DSet (bracket andMat 2 (1 / 2 : ℝ) (1 / 2 : ℝ)) := by
  refine ⟨andMat_left_bracket_nonempty, by norm_num, by norm_num,
    andMat_nonconstant, ?_⟩
  exact bracketMonotonicity andMat 1 2 (1 / 4 : ℝ) (1 / 2 : ℝ)
    (1 / 4 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end EthInapproximability.ParameterizedNP.InheritedContracts
