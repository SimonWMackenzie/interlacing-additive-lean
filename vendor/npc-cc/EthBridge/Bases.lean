import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.ComplexityAux
import NPCC.Engine
import EthBridge.Arith
import EthBridge.Defs
import EthBridge.Hypotheses

/-! # EthBridge terminal / base lower bounds (Tranche E1)

Statement-only (`sorry`) signatures for the three E1 obligations from
`eth-obligations.json`, drafted for faithfulness sign-off BEFORE any proving:

* `three_copy_base` / `three_copy_base_top_rung`  — `eth:lem-three-copy-base`
    (note (9)/(Three));
* `terminal_a0`                                   — `eth:lem-terminal-a0`
    (note §4 "Main statement: terminal level");
* `nonconstant`                                   — `eth:lem-nonconstant`
    (note §4 "every positive-target state … is nonconstant").

All three are hypothesis-conditional on `NearFull` / `TwoCopyBundle`
(`EthBridge.Hypotheses`). Every ambiguity is flagged `JUDGE FLAG`.
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## `eth:lem-three-copy-base` — note (9)/(Three): `Λ_W(3,4x,y²) ≥ C+1`

Recipe (scout report / note §3.2): present `W` as a `BoolMat`; discharge the
`lemma_A3_row_ladder_step` (Appendix.lean:814) side condition
`comp(bracket(W,2,4x,y²/4)) ≥ 1` from `(Two)`'s bottom rung `C-2 ≥ 1`
(needs `C ≥ 3`) plus row-parameter monotonicity `2x ≤ 4x`
(`bracketGE.anti_mono_params` + `Dfamily.anti_mono`); apply the row-step
lemma at `p := 1`, `δ := 1`, row `2x`, lemma-`y := y²`; transfer with
`LambdaGE_eq_Lambda`. Standing side conditions of the row-step lemma become,
with lemma-`x = 2x`: `0 < 2x`, `2x ≤ 1/2` (⟺ `x ≤ 1/4`), `0 < y²`, `y² ≤ 1`.

JUDGE FLAGS.
* `hC : 3 ≤ C` is REQUIRED (the side condition uses `C-2 ≥ 1`); the note fixes
  `C ≥ 3` globally.
* `hx : x ≤ 1/4` is the note's global bound and is exactly what the row-step
  lemma's `2x ≤ 1/2` needs; `4x ≤ 1` (bracket nonemptiness at `a = 2`) also
  follows.
* `bracketGE.nonempty` (needed to discharge the `Dfamily.anti_mono`
  nonemptiness obligation in the side-condition transfer) wants `[DecidableEq X]`;
  the proof supplies it with `classical` rather than carrying it in the type.
-/

/-- **Note (9)/(Three), bundled form.** From `(Two)` (with `C ≥ 3`) and the row
scale conditions, the three-copy bundle `Λ_W(3,4x,y²) ≥ C+1`. -/
theorem three_copy_base {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (x y : ℝ)
    (hC : 3 ≤ C)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X)
    (hTwo : TwoCopyBundle W C x y) :
    C + 1 ≤ LambdaGE W 3 (4 * x) (y ^ 2) := by
  classical
  have h2x0 : 0 < 2 * x := by linarith
  have h2x1 : 2 * x ≤ 1 := by linarith
  have h2xhalf : 2 * x ≤ 1 / 2 := by linarith
  have h4x0 : 0 < 4 * x := by linarith
  have h4x1 : 4 * x ≤ 1 := by linarith
  have hy2_0 : 0 < y ^ 2 := by positivity
  have hy2_1 : y ^ 2 ≤ 1 := by nlinarith
  have hy2d4_0 : 0 < y ^ 2 / 4 := by positivity
  have hy2d4_1 : y ^ 2 / 4 ≤ 1 := by nlinarith
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  set M : Workspace.Types.BoolMat.BoolMat :=
    ⟨Fintype.card X, Fintype.card Y, fun i j => W (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = W (eX i) (eY j) := fun _ _ => rfl
  have hLam2 : C ≤ Workspace.Types.Lambda.Lambda M 2 (2 * x) (y ^ 2) := by
    rw [← NPCC.LambdaGE_eq_Lambda W M eX eY he h2x0 h2x1 hy2_0 hy2_1 hX]
    exact hTwo
  have hbottom :
      C ≤ 2 + Workspace.Types.MatComplexity.DSet
        (Workspace.Types.Bracket.bracket M 2 (2 * x) (y ^ 2 / 4)) := by
    calc
      C ≤ Workspace.Types.Lambda.Lambda M 2 (2 * x) (y ^ 2) := hLam2
      _ ≤ 2 + Workspace.Types.MatComplexity.DSet
          (Workspace.Types.Bracket.bracket M 2 (2 * x) (y ^ 2 / 4)) := by
        unfold Workspace.Types.Lambda.Lambda
        exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hseed :
      1 ≤ Workspace.Types.MatComplexity.DSet
        (Workspace.Types.Bracket.bracket M 2 (2 * x) (y ^ 2 / 4)) := by
    omega
  have hside :
      1 ≤ Workspace.Types.MatComplexity.DSet
        (Workspace.Types.Bracket.bracket M (2 * 1) (2 * (2 * x)) (y ^ 2 / 4)) := by
    have hmono := Workspace.BracketLemmas.monotonicity M 2 (2 * 1)
      (2 * x) (2 * (2 * x)) (y ^ 2 / 4) (y ^ 2 / 4)
      (by norm_num) (by norm_num) h2x0 (by nlinarith) (by nlinarith)
      hy2d4_0 (le_refl _) hy2d4_1
    exact le_trans hseed hmono
  have hstep := Workspace.Appendix.lemma_A3_row_ladder_step M 1 (by norm_num) 1
    (by norm_num) (2 * x) (y ^ 2) ⟨h2x0, h2xhalf, hy2_0, hy2_1⟩ hside
  have hLam3 : C + 1 ≤ Workspace.Types.Lambda.Lambda M 3 (4 * x) (y ^ 2) := by
    have hbase :
        C + 1 ≤ Workspace.Types.Lambda.Lambda M (2 * 1 + 1) (2 * (2 * x)) (y ^ 2) := by
      calc
        C + 1 = 1 + C := by omega
        _ ≤ 1 + Workspace.Types.Lambda.Lambda M 2 (2 * x) (y ^ 2) :=
          Nat.add_le_add_left hLam2 1
        _ ≤ Workspace.Types.Lambda.Lambda M (2 * 1 + 1) (2 * (2 * x)) (y ^ 2) :=
          hstep
    convert hbase using 1 <;> norm_num <;> ring
  rw [NPCC.LambdaGE_eq_Lambda W M eX eY he h4x0 h4x1 hy2_0 hy2_1 hX]
  exact hLam3

/-- **Note (Three), top rung.** The top rung of (9): the pure three-copy
one-density lower bound `comp(bracket(W,3,4x,y²)) ≥ C+1` (the form the E2
one-bit-down base `eth:lem-obd-base` consumes). Obtained from `three_copy_base`
by `min_le_left` on `LambdaGE`. -/
theorem three_copy_base_top_rung {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (x y : ℝ)
    (hC : 3 ≤ C)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X)
    (hTwo : TwoCopyBundle W C x y) :
    C + 1 ≤ Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * x) (y ^ 2)) := by
  exact le_trans (three_copy_base W C x y hC hx0 hx hy0 hy1 hX hTwo)
    (min_le_left _ _)

private theorem dfamily_extended_projection
    {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (p ℓ : ℕ) (x y : ℝ)
    (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ ≤ p)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun W ℓ)
        (bracketGE X Y ℓ x (Real.rpow y ((ℓ : ℝ) / (p : ℝ)))) ≤
      Dfamily (interlaceFun W p) (bracketGE X Y p x y) := by
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : Workspace.Types.BoolMat.BoolMat :=
    ⟨Fintype.card X, Fintype.card Y, fun i j ↦ W (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = W (eX i) (eY j) := fun _ _ ↦ rfl
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega) hℓp)
  have hratio0 : 0 ≤ (ℓ : ℝ) / (p : ℝ) := by positivity
  have hyr0 : 0 < Real.rpow y ((ℓ : ℝ) / (p : ℝ)) :=
    Real.rpow_pos_of_pos hy0 _
  have hyr1 : Real.rpow y ((ℓ : ℝ) / (p : ℝ)) ≤ 1 :=
    Real.rpow_le_one hy0.le hy1 hratio0
  rw [NPCC.Dfamily_eq_DSet W M eX eY he hx0 hx1 hyr0 hyr1 hX,
    NPCC.Dfamily_eq_DSet W M eX eY he hx0 hx1 hy0 hy1 hX]
  exact Workspace.BracketLemmas.extended_maximum_projection
    M p ℓ x y hℓ1 hℓp hy0

/-! ## `eth:lem-terminal-a0` — note §4 terminal level (`a = 0`)

Recipe (note §4 "Main statement: terminal level"): a Theorem-1 state at level
`a = 0` with `p ≥ 1` has, by maximum projection to ONE coordinate
(`extended_maximum_projection`, BracketLemmas.lean:1142, `ℓ = 1`), column
defect at most `Def(K)/p ≤ ((p - 1/2)/p)·λ < λ`, hence projected column density
strictly above `exp(-λ)`, with at least `A_0 = ⌈m·x⌉` rows. The near-full base
`(Near)` then gives complexity at least `C`.

Conclusion phrased in the Theorem-1 family form (`stateComp = Dfamily over
stateDensity`), matching Theorem 1's `comp ≥ C+a` at `a = 0`.

JUDGE FLAGS.
* Stated over `stateDensity` (the positive-target / `|C|>0` working form the
  ledger pins provisionally). Nonemptiness of the family at `a = 0` (needed so
  the `Dfamily` min is not the empty-set `sInf = 0`) follows from `(univ,univ)`
  membership under `x ≤ 1` and `0 ≤ c_0(p)·λ` — a proof obligation, not a
  hypothesis here.
* Minimal density-side hypothesis is `x ≤ 1` (so `A_0 = ⌈m·x⌉ ≤ m`); the note's
  global `x ≤ 1/4` is stronger. Stated with `x ≤ 1` and flagged.
* `0 < lam` is the note's deletion tolerance; it is what makes
  `((p-1/2)/p)λ < λ` strict, hence density `> exp(-λ)`. -/

/-- **Note §4, terminal `a = 0`.** `(Near)` + a level-`0` state ⇒ complexity
`≥ C`. -/
theorem terminal_a0 {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (p : ℕ) (x lam : ℝ)
    (hp : 1 ≤ p) (hx0 : 0 < x) (hx1 : x ≤ 1) (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X)
    (hNear : NearFull W C x lam) :
    C ≤ stateComp X Y W p 0 x lam := by
  classical
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  have hc0 : cExcess 0 p = (p : ℝ) - 1 / 2 := by
    rw [cExcess]
    norm_num [zpow_neg_one]
  have hc0_nonneg : 0 ≤ cExcess 0 p := by rw [hc0]; linarith
  have hc0_le : cExcess 0 p ≤ (p : ℝ) := by rw [hc0]; norm_num
  let y0 : ℝ := Real.exp (-(cExcess 0 p * lam))
  have hy0_pos : 0 < y0 := Real.exp_pos _
  have hy0_one : y0 ≤ 1 := by
    dsimp [y0]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hc0_nonneg hlam.le)
  have hfull_y0 : Real.exp (-((p : ℝ) * lam)) ≤ y0 := by
    dsimp [y0]
    rw [Real.exp_le_exp]
    nlinarith
  let y1 : ℝ := Real.rpow y0 (1 / (p : ℝ))
  have hratio0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hy1_pos : 0 < y1 := Real.rpow_pos_of_pos hy0_pos _
  have hy1_one : y1 ≤ 1 := Real.rpow_le_one hy0_pos.le hy0_one hratio0
  have hroot : Real.exp (-lam) ≤ y1 := by
    have hpow := Real.rpow_le_rpow (Real.exp_pos _).le hfull_y0 hratio0
    have heq :
        Real.rpow (Real.exp (-((p : ℝ) * lam))) (1 / (p : ℝ)) =
          Real.exp (-lam) := by
      change (Real.exp (-((p : ℝ) * lam))) ^ (1 / (p : ℝ)) =
        Real.exp (-lam)
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp
    exact heq ▸ hpow
  have hstate :
      stateDensity X Y p 0 x lam = bracketGE X Y p x y0 := by
    ext RC
    simp only [stateDensity, bracketGE, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hrows, hcols⟩
      refine ⟨?_, Nat.ceil_le.mpr hcols⟩
      simpa [rowThreshold] using hrows
    · rintro ⟨hrows, hcols⟩
      refine ⟨?_, Nat.ceil_le.mp hcols⟩
      simpa [rowThreshold] using hrows
  have hmono :
      Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (Real.exp (-lam))) ≤
        Dfamily (interlaceFun W 1) (bracketGE X Y 1 x y1) := by
    exact Dfamily.anti_mono _
      (bracketGE.anti_mono_params 1 (le_refl x) hroot)
      (bracketGE.nonempty 1 x y1 hx1 hy1_one hX)
  have hproj :
      Dfamily (interlaceFun W 1) (bracketGE X Y 1 x y1) ≤
        Dfamily (interlaceFun W p) (bracketGE X Y p x y0) := by
    simpa [y1] using
      (dfamily_extended_projection W p 1 x y0 (by omega) hp
        hx0 hx1 hy0_pos hy0_one hX)
  unfold NearFull at hNear
  unfold stateComp
  rw [hstate]
  exact le_trans hNear (le_trans hmono hproj)

/-! ## `eth:lem-nonconstant` — note §4 "every positive-target state … is nonconstant"

DESIGN FREEDOM (flagged to judge). The note uses nonconstancy only to grant a
state "a first protocol bit" so the Alice/Bob case split is legitimate.
"Nonconstant" ⟺ deterministic complexity `≥ 1`. Several faithful encodings
exist; the weakest broadly-usable one is chosen:

  PER-MEMBER form: every extraction `RC` in the level-`a` state family has
  induced-subgame complexity `≥ 1`.

Rationale for the PER-MEMBER (not family-min) form: it needs no nonemptiness
side condition and matches the note's per-state usage ("the state is
nonconstant"). Mechanism: maximum projection to ONE coordinate lands in the
near-full one-copy base; because `c_a(p) = p - 2^(a-1) ≤ p` (as `2^(a-1) > 0`)
the one-coordinate projected density is `exp(-(c_a(p)/p)λ) ≥ exp(-λ)`, so
`(Near)` applies at EVERY level `a ≥ 0` and gives `≥ C ≥ 1`.

JUDGE FLAGS.
* `main_nonconstant` covers the MAIN-state nonconstancy the note invokes for
  `a = 1` and `a ≥ 2` ("nonconstant by maximum projection to the near-full
  one-copy base"): for a main state `c_a(p) ≤ p` gives projected density
  `≥ exp(-λ)`, so `(Near)` applies at every level via one-coordinate projection.
* `nonconstant` (JUDGE REVISE, added) is the ONE-BIT-DOWN `(12)`-state form the
  note ALSO requires ("the same projection also shows that every positive-target
  state satisfying (12) is nonconstant") and which the E2 induction consumes. Its
  column budget carries the extra `Bdef p` term (the `(12)` one-bit-down slack),
  and the state is given by its defining `(12)` conjuncts (row equipartition
  `hrows` + column count `hcols`) rather than membership in `stateDensity`.
* `hC : 1 ≤ C` is all that is used for `main_nonconstant` (nonconstancy, not the
  full `≥ C`); the `(12)` form uses `hC : 3 ≤ C` and `hTwo` (the note's global
  regime). -/

/-- **Note §4, MAIN-state nonconstancy (per-member form).** Every member of a
level-`a` positive-target MAIN state is nonconstant (`D ≥ 1`), via one-coordinate
projection to `(Near)` (`c_a(p) ≤ p`). -/
theorem main_nonconstant {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (p a : ℕ) (x lam : ℝ)
    (hp : 1 ≤ p) (hx0 : 0 < x) (hx1 : x ≤ 1) (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hC : 1 ≤ C)
    (hNear : NearFull W C x lam)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p a x lam) :
    1 ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ a := by
    exact_mod_cast Nat.one_le_pow a 2 (by omega : 0 < (2 : ℕ))
  let xa : ℝ := min ((2 : ℝ) ^ a * x) 1
  have hx_scale : x ≤ (2 : ℝ) ^ a * x := by nlinarith
  have hx_xa : x ≤ xa := le_min hx_scale hx1
  have hxa_pos : 0 < xa := lt_min (mul_pos (pow_pos (by norm_num) _) hx0) (by norm_num)
  have hxa_one : xa ≤ 1 := min_le_right _ _
  have hc_le : cExcess a p ≤ (p : ℝ) := by
    have hzpos : 0 < (2 : ℝ) ^ ((a : ℤ) - 1) := zpow_pos (by norm_num) _
    unfold cExcess
    linarith
  let ya : ℝ := Real.exp (-(cExcess a p * lam))
  let ya' : ℝ := min ya 1
  have hya_pos : 0 < ya := Real.exp_pos _
  have hyap_pos : 0 < ya' := lt_min hya_pos (by norm_num)
  have hyap_one : ya' ≤ 1 := min_le_right _ _
  have hfull_ya : Real.exp (-((p : ℝ) * lam)) ≤ ya := by
    dsimp [ya]
    rw [Real.exp_le_exp]
    nlinarith
  have hfull_one : Real.exp (-((p : ℝ) * lam)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hp0.le hlam.le)
  have hfull_yap : Real.exp (-((p : ℝ) * lam)) ≤ ya' :=
    le_min hfull_ya hfull_one
  let y1 : ℝ := Real.rpow ya' (1 / (p : ℝ))
  have hratio0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hy1_pos : 0 < y1 := Real.rpow_pos_of_pos hyap_pos _
  have hy1_one : y1 ≤ 1 := Real.rpow_le_one hyap_pos.le hyap_one hratio0
  have hroot : Real.exp (-lam) ≤ y1 := by
    have hpow := Real.rpow_le_rpow (Real.exp_pos _).le hfull_yap hratio0
    have heq :
        Real.rpow (Real.exp (-((p : ℝ) * lam))) (1 / (p : ℝ)) =
          Real.exp (-lam) := by
      change (Real.exp (-((p : ℝ) * lam))) ^ (1 / (p : ℝ)) =
        Real.exp (-lam)
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp
    exact heq ▸ hpow
  change IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin p))
      (rowThreshold (Fintype.card X) x a) ∧
    ((Fintype.card Y : ℝ) ^ p) * Real.exp (-(cExcess a p * lam)) ≤
      (RC.2.card : ℝ) at hmem
  rcases hmem with ⟨hrows, hcols⟩
  have hRC : RC ∈ bracketGE X Y p xa ya' := by
    constructor
    · intro q hq
      refine le_trans ?_ (hrows q hq)
      unfold rowThreshold
      apply Nat.ceil_le_ceil
      calc
        (Fintype.card X : ℝ) * xa ≤
            (Fintype.card X : ℝ) * ((2 : ℝ) ^ a * x) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
        _ = (Fintype.card X : ℝ) * (2 : ℝ) ^ a * x := by ring
    · apply Nat.ceil_le.mpr
      calc
        ((Fintype.card Y : ℝ) ^ p) * ya' ≤
            ((Fintype.card Y : ℝ) ^ p) * ya :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
        _ ≤ (RC.2.card : ℝ) := by simpa [ya] using hcols
  have hmono :
      Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (Real.exp (-lam))) ≤
        Dfamily (interlaceFun W 1) (bracketGE X Y 1 xa y1) := by
    exact Dfamily.anti_mono _
      (bracketGE.anti_mono_params 1 hx_xa hroot)
      (bracketGE.nonempty 1 xa y1 hxa_one hy1_one hX)
  have hproj :
      Dfamily (interlaceFun W 1) (bracketGE X Y 1 xa y1) ≤
        Dfamily (interlaceFun W p) (bracketGE X Y p xa ya') := by
    simpa [y1] using
      (dfamily_extended_projection W p 1 xa ya' (by omega) hp
        hxa_pos hxa_one hyap_pos hyap_one hX)
  have hmember :
      Dfamily (interlaceFun W p) (bracketGE X Y p xa ya') ≤
        Dfamily (interlaceFun W p) {RC} := by
    exact Dfamily.anti_mono _ (Set.singleton_subset_iff.mpr hRC)
      (Set.singleton_nonempty RC)
  unfold NearFull at hNear
  calc
    1 ≤ C := hC
    _ ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (Real.exp (-lam))) := hNear
    _ ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 xa y1) := hmono
    _ ≤ Dfamily (interlaceFun W p) (bracketGE X Y p xa ya') := hproj
    _ ≤ Dfamily (interlaceFun W p) {RC} := hmember
    _ = D (subgame (interlaceFun W p) RC.1 RC.2) := Dfamily.singleton _ _

/-- **Note §4, ONE-BIT-DOWN `(12)`-state nonconstancy (JUDGE REVISE).** Every
positive-target state satisfying the `(12)` one-bit-down conditions — row
equipartition at threshold `A_a` (`hrows`) and column count at least
`n^p · exp(-(c_a(p)·λ + B(p)))` (`hcols`, the `+B(p)` one-bit-down budget) — is
nonconstant (`D ≥ 1`). Same one-coordinate maximum projection as
`main_nonconstant`, now with the extra `Bdef p` slack absorbed by the margin
`hmargin : 3λ + (7/5)·log 2 ≤ -2·log y`. Consumed by the E2 one-bit-down
induction (`eth:lem-obd-base`). -/
theorem nonconstant {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x y lam : ℝ)
    (ha : 2 ≤ a) (hp : 2 ^ (a - 1) < p)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam) (hX : 1 ≤ Fintype.card X) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwo : TwoCopyBundle W C x y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hrows : IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin p))
      (rowThreshold (Fintype.card X) x a))
    (hcols : ((Fintype.card Y : ℝ) ^ p) *
      Real.exp (-(cExcess a p * lam + Bdef p)) ≤ (RC.2.card : ℝ)) :
    1 ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  have ha1 : 1 ≤ a - 1 := by omega
  have hpow_lower : 2 ≤ 2 ^ (a - 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by omega) ha1
  have hp3 : 3 ≤ p := by omega
  have hp2 : 2 ≤ p := by omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  have hcast_exp : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
  have hc_pos : 0 < cExcess a p := by
    have hp_cast : (2 : ℝ) ^ (a - 1) < (p : ℝ) := by exact_mod_cast hp
    unfold cExcess
    rw [hcast_exp, zpow_natCast]
    linarith
  have hc_le : cExcess a p ≤ (p : ℝ) := by
    have hzpos : 0 < (2 : ℝ) ^ ((a : ℤ) - 1) := zpow_pos (by norm_num) _
    unfold cExcess
    linarith
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB_pos : 0 < Bdef p := lt_of_lt_of_le hlog_pos (Bdef_ge_log2 p hp2)
  let yp : ℝ := Real.exp (-(cExcess a p * lam + Bdef p))
  have hyp_pos : 0 < yp := Real.exp_pos _
  have hyp_one : yp ≤ 1 := by
    dsimp [yp]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (add_nonneg (mul_nonneg hc_pos.le hlam.le) hB_pos.le)
  have hpow_two_nat : 2 ≤ 2 ^ a := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow_two : (2 : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast hpow_two_nat
  let xa : ℝ := min ((2 : ℝ) ^ a * x) 1
  have h2x_scale : 2 * x ≤ (2 : ℝ) ^ a * x := by nlinarith
  have h2x_one : 2 * x ≤ 1 := by nlinarith
  have h2x_xa : 2 * x ≤ xa := le_min h2x_scale h2x_one
  have hxa_pos : 0 < xa := lt_min (mul_pos (pow_pos (by norm_num) _) hx0) (by norm_num)
  have hxa_one : xa ≤ 1 := min_le_right _ _
  let y2 : ℝ := Real.rpow yp (2 / (p : ℝ))
  have hratio0 : 0 ≤ 2 / (p : ℝ) := by positivity
  have hy2_pos : 0 < y2 := Real.rpow_pos_of_pos hyp_pos _
  have hy2_one : y2 ≤ 1 := Real.rpow_le_one hyp_pos.le hyp_one hratio0
  have hy2_eq :
      y2 = Real.exp (-(cExcess a p * lam + Bdef p) * (2 / (p : ℝ))) := by
    dsimp [y2, yp]
    change (Real.exp (-(cExcess a p * lam + Bdef p))) ^ (2 / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hc_scaled : (2 / (p : ℝ)) * cExcess a p ≤ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp0).2
    nlinarith
  have hratio23 : 2 / (p : ℝ) ≤ 3 / (p : ℝ) := by
    exact (div_le_div_iff_of_pos_right hp0).2 (by norm_num)
  have hscaled :
      (2 / (p : ℝ)) * (cExcess a p * lam + Bdef p) ≤
        3 * lam + (7 / 5) * Real.log 2 := by
    calc
      (2 / (p : ℝ)) * (cExcess a p * lam + Bdef p) =
          ((2 / (p : ℝ)) * cExcess a p) * lam +
            (2 / (p : ℝ)) * Bdef p := by ring
      _ ≤ 2 * lam + (3 / (p : ℝ)) * Bdef p :=
        add_le_add (mul_le_mul_of_nonneg_right hc_scaled hlam.le)
          (mul_le_mul_of_nonneg_right hratio23 hB_pos.le)
      _ ≤ 3 * lam + (7 / 5) * Real.log 2 :=
        add_le_add (by linarith) (Bdef_three p hp3)
  have hbudget :
      (2 / (p : ℝ)) * (cExcess a p * lam + Bdef p) ≤
        -2 * Real.log y := le_trans hscaled hmargin
  have hexponent :
      2 * Real.log y ≤ -(cExcess a p * lam + Bdef p) * (2 / (p : ℝ)) := by
    calc
      2 * Real.log y ≤
          -((2 / (p : ℝ)) * (cExcess a p * lam + Bdef p)) := by linarith
      _ = -(cExcess a p * lam + Bdef p) * (2 / (p : ℝ)) := by ring
  have hy_sq_exp : y ^ 2 = Real.exp (2 * Real.log y) := by
    calc
      y ^ 2 = (Real.exp (Real.log y)) ^ 2 := by rw [Real.exp_log hy0]
      _ = Real.exp (2 * Real.log y) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hy_sq_y2 : y ^ 2 ≤ y2 := by
    rw [hy_sq_exp, hy2_eq, Real.exp_le_exp]
    exact hexponent
  have hRC : RC ∈ bracketGE X Y p xa yp := by
    constructor
    · intro q hq
      refine le_trans ?_ (hrows q hq)
      unfold rowThreshold
      apply Nat.ceil_le_ceil
      calc
        (Fintype.card X : ℝ) * xa ≤
            (Fintype.card X : ℝ) * ((2 : ℝ) ^ a * x) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
        _ = (Fintype.card X : ℝ) * (2 : ℝ) ^ a * x := by ring
    · apply Nat.ceil_le.mpr
      simpa [yp] using hcols
  have htop :
      C ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) := by
    exact le_trans hTwo (min_le_left _ _)
  have hmono :
      Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) ≤
        Dfamily (interlaceFun W 2) (bracketGE X Y 2 xa y2) := by
    exact Dfamily.anti_mono _
      (bracketGE.anti_mono_params 2 h2x_xa hy_sq_y2)
      (bracketGE.nonempty 2 xa y2 hxa_one hy2_one hX)
  have hproj :
      Dfamily (interlaceFun W 2) (bracketGE X Y 2 xa y2) ≤
        Dfamily (interlaceFun W p) (bracketGE X Y p xa yp) := by
    simpa [y2] using
      (dfamily_extended_projection W p 2 xa yp (by omega) hp2
        hxa_pos hxa_one hyp_pos hyp_one hX)
  have hmember :
      Dfamily (interlaceFun W p) (bracketGE X Y p xa yp) ≤
        Dfamily (interlaceFun W p) {RC} := by
    exact Dfamily.anti_mono _ (Set.singleton_subset_iff.mpr hRC)
      (Set.singleton_nonempty RC)
  calc
    1 ≤ C := by omega
    _ ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) := htop
    _ ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 xa y2) := hmono
    _ ≤ Dfamily (interlaceFun W p) (bracketGE X Y p xa yp) := hproj
    _ ≤ Dfamily (interlaceFun W p) {RC} := hmember
    _ = D (subgame (interlaceFun W p) RC.1 RC.2) := Dfamily.singleton _ _

end EthBridge
