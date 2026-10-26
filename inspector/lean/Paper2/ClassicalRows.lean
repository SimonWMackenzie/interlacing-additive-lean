import Paper2.InterlaceRank
import NPCC.Engine

/-!
# Classical row estimates with a lower-bound parameter

Frozen source: v12 Appendix A, `cl:restriction-notation`,
`cl:classical-row-inputs`, `cl:row-ladder`, and `cl:small-capacities`.

This module uses the uniform indexed carriers and exact integer ceilings of
the appendix. The transparent definitions below reuse `NPCC.bracketGE`,
`Dfamily`, and `LambdaGE`, whose protocols are the existing concrete binary
trees. The inherited `NPCC.two_copy_ladder` permits an arbitrary lower bound
strictly above one; it does not require that bound to equal `D F`.
`NPCC.row_step` supplies the bundled copy-halving estimate. Both imports were
checked at their exact types and have only standard Lean axioms. General
rational-law transport is a separate step, not an implicit change of model.
-/

namespace Paper2.ClassicalRows

open Workspace.Types.CommComplexity Workspace.Types.Interlace

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The actual retained row/column pairs, with the required row count in
every outer block and the required total column count. -/
abbrev restrictions (p : ℕ) (x z : ℝ) := NPCC.bracketGE X Y p x z

/-- The minimum cost over the indicated actual restrictions. -/
noncomputable abbrev restrictionCost (F : X → Y → Bool) (p : ℕ) (x z : ℝ) : ℕ :=
  NPCC.Dfamily (interlaceFun F p) (restrictions (X := X) (Y := Y) p x z)

/-- The three-rung minimum of `cl:restriction-notation`. -/
noncomputable abbrev lambda (F : X → Y → Bool) (p : ℕ) (x z : ℝ) : ℕ :=
  NPCC.LambdaGE F p x z

theorem lambda_eq (F : X → Y → Bool) (p : ℕ) (x z : ℝ) :
    lambda F p x z = min (restrictionCost F p x z)
      (min (1 + restrictionCost F p x (z / 2))
        (2 + restrictionCost F p x (z / 4))) := rfl

theorem le_lambda_iff (F : X → Y → Bool) (p H : ℕ) (x z : ℝ) :
    H ≤ lambda F p x z ↔
      H ≤ restrictionCost F p x z ∧
      H ≤ 1 + restrictionCost F p x (z / 2) ∧
      H ≤ 2 + restrictionCost F p x (z / 4) := by
  rw [lambda_eq]
  exact le_min_iff.trans (and_congr_right fun _ => le_min_iff)

theorem restrictions_nonempty [Nonempty X] (p : ℕ) (x z : ℝ)
    (hx : x ≤ 1) (hz : z ≤ 1) :
    (restrictions (X := X) (Y := Y) p x z).Nonempty := by
  classical
  exact NPCC.bracketGE.nonempty p x z hx hz Fintype.card_pos

/-- A family lower bound applies to each particular retained matrix. -/
theorem restrictionCost_le_member (F : X → Y → Bool) (p : ℕ) (x z : ℝ)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hRC : (R, C) ∈ restrictions (X := X) (Y := Y) p x z) :
    restrictionCost F p x z ≤ D (NPCC.subgame (interlaceFun F p) R C) := by
  exact Nat.sInf_le ⟨(R, C), hRC, rfl⟩

/-- The top and bottom rungs used in the row-amplification induction. -/
theorem lambda_le_top (F : X → Y → Bool) (p : ℕ) (x z : ℝ) :
    lambda F p x z ≤ restrictionCost F p x z := min_le_left _ _

theorem lambda_le_bottom (F : X → Y → Bool) (p : ℕ) (x z : ℝ) :
    lambda F p x z ≤ 2 + restrictionCost F p x (z / 4) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- First assertion of `cl:classical-row-inputs`, for any lower bound H. -/
theorem two_copy (F : X → Y → Bool) (H : ℕ) {x z : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hx : x ≤ 1 / 2)
    (hz0 : 0 < z) (hz : z ≤ 1) (hbase : H ≤ lambda F 1 x z) :
    H + 1 ≤ lambda F 2 (2 * x) (z ^ 2) := by
  obtain ⟨h0, h1, h2⟩ := (le_lambda_iff F 1 H x z).mp hbase
  have h0R : (H : ℝ) ≤ (restrictionCost F 1 x z : ℝ) := by exact_mod_cast h0
  have h1R : (H : ℝ) ≤ 1 + (restrictionCost F 1 x (z / 2) : ℝ) := by
    exact_mod_cast h1
  have h2R : (H : ℝ) ≤ 2 + (restrictionCost F 1 x (z / 4) : ℝ) := by
    exact_mod_cast h2
  have hHR : (1 : ℝ) < H := by exact_mod_cast (by omega : 1 < H)
  obtain ⟨a, b, c⟩ := NPCC.two_copy_ladder F hHR hx0 hx hz0 hz
    (by linarith : (H : ℝ) - 2 ≤ (restrictionCost F 1 x (z / 4) : ℝ))
    (by linarith : (H : ℝ) - 1 ≤ (restrictionCost F 1 x (z / 2) : ℝ)) h0R
  apply (le_lambda_iff F 2 (H + 1) (2 * x) (z ^ 2)).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast c
  · have hb : (H : ℝ) + 1 ≤ 1 +
        (restrictionCost F 2 (2 * x) (z ^ 2 / 2) : ℝ) := by linarith
    exact_mod_cast hb
  · have ha : (H : ℝ) + 1 ≤ 2 +
        (restrictionCost F 2 (2 * x) (z ^ 2 / 4) : ℝ) := by linarith
    exact_mod_cast ha

/-- Second assertion of `cl:classical-row-inputs`. The nonconstant-family
premise is retained exactly, including its quarter-density threshold. -/
theorem copy_halving (F : X → Y → Bool) (p σ : ℕ)
    (hp : 1 ≤ p) (hσ : σ ≤ 1) {x z : ℝ}
    (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hz0 : 0 < z) (hz : z ≤ 1)
    (hnonconstant : 1 ≤ restrictionCost F (2 * p) (2 * x) (z / 4)) :
    1 + lambda F (p + σ) x z ≤ lambda F (2 * p + σ) (2 * x) z :=
  NPCC.row_step F p σ hp hσ hx0 hx hz0 hz hnonconstant

/-- Uniform family monotonicity, by the checked exact typed-to-matrix
identification. Selected columns remain actual inputs, not independent ones. -/
theorem restrictionCost_mono [Nonempty X] (F : X → Y → Bool)
    (p' p : ℕ) (x' x z' z : ℝ) (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hx'0 : 0 < x') (hxx : x' ≤ x) (hx : x ≤ 1)
    (hz'0 : 0 < z') (hzz : z' ≤ z) (hz : z ≤ 1) :
    restrictionCost F p' x' z' ≤ restrictionCost F p x z := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : Workspace.Types.BoolMat.BoolMat :=
    ⟨Fintype.card X, Fintype.card Y, fun i j => F (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = F (eX i) (eY j) := fun _ _ => rfl
  rw [restrictionCost, NPCC.Dfamily_eq_DSet F M eX eY he
    hx'0 (hxx.trans hx) hz'0 (hzz.trans hz) Fintype.card_pos]
  rw [restrictionCost, NPCC.Dfamily_eq_DSet F M eX eY he
    (hx'0.trans_le hxx) hx (hz'0.trans_le hzz) hz Fintype.card_pos]
  exact Workspace.BracketLemmas.monotonicity M p' p x' x z' z
    hp' hpp hx'0 hxx hx hz'0 hzz hz

/-- `cl:row-ladder`, expressed with natural powers of two. H remains only
a lower bound throughout the induction; no upper bound for `D F` is used. -/
theorem row_ladder [Nonempty X] (F : X → Y → Bool) (H : ℕ) {x z : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hz0 : 0 < z) (hz : z ≤ 1)
    (hbase : H ≤ lambda F 1 x z) :
    ∀ l : ℕ, 1 ≤ l → (2 : ℝ) ^ l * x ≤ 1 →
      H + l ≤ lambda F (2 ^ (l - 1) + 1) ((2 : ℝ) ^ l * x) (z ^ 2) := by
  intro l
  induction l using Nat.case_strong_induction_on with
  | hz => intro hl; omega
  | hi k ih =>
    intro hl hscale
    by_cases hk : k = 0
    · subst k
      have hx : x ≤ 1 / 2 := by norm_num at hscale; linarith
      simpa using two_copy F H hH hx0 hx hz0 hz hbase
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hpow : (2 : ℝ) ^ (k + 1) * x = 2 * ((2 : ℝ) ^ k * x) := by
        rw [pow_succ]
        ring
      have hu0 : 0 < (2 : ℝ) ^ k * x := by positivity
      have huhalf : (2 : ℝ) ^ k * x ≤ 1 / 2 := by rw [hpow] at hscale; linarith
      have hprev := ih k (Nat.le_refl _) hk1 (by linarith : (2 : ℝ) ^ k * x ≤ 1)
      let p := 2 ^ (k - 1)
      have hp : 1 ≤ p := by dsimp [p]; exact Nat.one_le_two_pow
      have hprev' : H + k ≤ lambda F (p + 1) ((2 : ℝ) ^ k * x) (z ^ 2) := hprev
      have hbottom := hprev.trans (lambda_le_bottom F (p + 1)
        ((2 : ℝ) ^ k * x) (z ^ 2))
      have hnonconst : 1 ≤ restrictionCost F (p + 1)
          ((2 : ℝ) ^ k * x) (z ^ 2 / 4) := by omega
      have hzsq0 : 0 < z ^ 2 := by positivity
      have hzsq : z ^ 2 ≤ 1 := by nlinarith
      have hmono := restrictionCost_mono F (p + 1) (2 * p)
        ((2 : ℝ) ^ k * x) (2 * ((2 : ℝ) ^ k * x))
        (z ^ 2 / 4) (z ^ 2 / 4) (by omega) (by omega)
        hu0 (by linarith) (by linarith) (by positivity) le_rfl (by linarith)
      have hstep := copy_halving F p 1 hp (by decide) hu0 huhalf hzsq0 hzsq
        (hnonconst.trans hmono)
      have hpEq : 2 * p = 2 ^ k := by
        dsimp [p]
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]
      have hresult : H + (k + 1) ≤ lambda F (2 * p + 1)
          (2 * ((2 : ℝ) ^ k * x)) (z ^ 2) := by omega
      simpa only [Nat.add_sub_cancel, hpEq, ← hpow] using hresult

/-- The concrete retained-matrix form of the large-power-of-two case of
`cl:small-capacities`. Here `K = 2^l`, with `l >= 2`. -/
theorem small_capacity_power [Nonempty X] (F : X → Y → Bool)
    (H l p : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx0 : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hbase : H ≤ lambda F 1 x (3 / 5)) (hp : 2 ^ (l - 1) + 1 ≤ p)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hRC : (R, C) ∈ restrictions (X := X) (Y := Y) p
      ((2 : ℝ) ^ l * x) (9 / 25)) :
    H + l ≤ D (NPCC.subgame (interlaceFun F p) R C) := by
  have h := row_ladder F H hH hx0 (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 : ℝ) / 5 ≤ 1) hbase l (by omega) hscale
  have hzsq : ((3 : ℝ) / 5) ^ 2 = 9 / 25 := by norm_num
  rw [hzsq] at h
  have htop := h.trans (lambda_le_top F (2 ^ (l - 1) + 1)
    ((2 : ℝ) ^ l * x) (9 / 25))
  have hmono := restrictionCost_mono F (2 ^ (l - 1) + 1) p
    ((2 : ℝ) ^ l * x) ((2 : ℝ) ^ l * x) (9 / 25) (9 / 25)
    (Nat.le_add_left 1 _) hp (by positivity) le_rfl hscale (by norm_num) le_rfl (by norm_num)
  exact (htop.trans hmono).trans (restrictionCost_le_member F p _ _ R C hRC)

/-- The two-block assertion used for both `K = 1` and `K = 2`. It does not
claim a one-copy bound at the original row threshold. -/
theorem small_capacity_two (F : X → Y → Bool) (H : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hscale : 2 * x ≤ 1)
    (hbase : H ≤ lambda F 1 x (3 / 5))
    (R : Finset (Fin 2 × X)) (C : Finset (Fin 2 → Y))
    (hRC : (R, C) ∈ restrictions (X := X) (Y := Y) 2 (2 * x) (9 / 25)) :
    H + 1 ≤ D (NPCC.subgame (interlaceFun F 2) R C) := by
  have h := two_copy F H hH hx0 (by linarith) (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 : ℝ) / 5 ≤ 1) hbase
  have hzsq : ((3 : ℝ) / 5) ^ 2 = 9 / 25 := by norm_num
  rw [hzsq] at h
  exact (h.trans (lambda_le_top F 2 (2 * x) (9 / 25))).trans
    (restrictionCost_le_member F 2 _ _ R C hRC)

end Paper2.ClassicalRows
