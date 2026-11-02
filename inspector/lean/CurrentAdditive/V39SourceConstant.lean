import CurrentAdditive.V38Schedule

/-! Uniform source-constant bounds for the v39 public full schedule.
The exact v39 source Appendix `parameters.tex` is mathematically identical
to the reviewed v38 Appendix. These are arithmetic consequences of the graph
promise; no construction, cutoff, or execution theorem is assumed. -/

namespace V39PublicSchedule

open V38Schedule

/-- A strictly positive lower bound depending only on the fixed graph promise. -/
def publicConstantFloor (γ : ℚ) (Δ : ℕ) : ℚ :=
  min 1 (min (γ / (4 * Δ)) (sourceZeta γ / 256))

theorem publicConstantFloor_exact (γ : ℚ) (Δ : ℕ) :
    publicConstantFloor γ Δ =
      min 1 (min (γ / (4 * Δ)) (γ / (24 * 256))) := by
  unfold publicConstantFloor sourceZeta
  congr 2
  ring

theorem sourceDeltaV_lower (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hnm : n ≤ 2 * m) :
    γ / (4 * Δ) ≤ sourceDeltaV γ Δ n m := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hΔQ : (0 : ℚ) < Δ := by exact_mod_cast hΔ
  have hnmQ : (n : ℚ) ≤ 2 * m := by exact_mod_cast hnm
  unfold sourceDeltaV
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 4 * Δ)
    (by positivity : (0 : ℚ) < 2 * Δ * n)).2
  have h := mul_le_mul_of_nonneg_left hnmQ
    (show (0 : ℚ) ≤ 2 * γ * Δ by positivity)
  nlinarith only [h]

theorem publicConstantFloor_pos (γ : ℚ) (Δ : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) :
    0 < publicConstantFloor γ Δ := by
  have hΔQ : (0 : ℚ) < Δ := by exact_mod_cast hΔ
  unfold publicConstantFloor sourceZeta
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem publicConstantFloor_le_fullConstant (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hnm : n ≤ 2 * m) :
    publicConstantFloor γ Δ ≤ fullConstant γ Δ n m := by
  unfold publicConstantFloor fullConstant
  exact min_le_min le_rfl (min_le_min
    (sourceDeltaV_lower γ Δ n m hγ hΔ hn hnm) le_rfl)

theorem fullConstant_upper (γ : ℚ) (Δ n m : ℕ) :
    fullConstant γ Δ n m ≤ 1 ∧
    fullConstant γ Δ n m ≤ sourceDeltaV γ Δ n m ∧
    fullConstant γ Δ n m ≤ sourceZeta γ / 256 := by
  unfold fullConstant
  exact ⟨min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

theorem publicConstantFloor_le_zeta (γ : ℚ) (Δ : ℕ)
    (hγ : 0 ≤ γ) : publicConstantFloor γ Δ ≤ sourceZeta γ := by
  have hz : (0 : ℚ) ≤ sourceZeta γ := by unfold sourceZeta; positivity
  have hmin : publicConstantFloor γ Δ ≤ sourceZeta γ / 256 :=
    (min_le_right _ _).trans (min_le_right _ _)
  linarith

theorem fullConstant_interval (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hnm : n ≤ 2 * m) :
    0 < publicConstantFloor γ Δ ∧
    publicConstantFloor γ Δ ≤ fullConstant γ Δ n m ∧
    fullConstant γ Δ n m ≤ min 1
      (min (sourceDeltaV γ Δ n m) (sourceZeta γ / 256)) ∧
    0 < sourceZeta γ ∧ publicConstantFloor γ Δ ≤ sourceZeta γ := by
  exact ⟨publicConstantFloor_pos γ Δ hγ hΔ,
    publicConstantFloor_le_fullConstant γ Δ n m hγ hΔ hn hnm,
    le_rfl, by unfold sourceZeta; positivity,
    publicConstantFloor_le_zeta γ Δ hγ.le⟩

#print axioms publicConstantFloor_exact
#print axioms sourceDeltaV_lower
#print axioms publicConstantFloor_pos
#print axioms publicConstantFloor_le_fullConstant
#print axioms fullConstant_upper
#print axioms publicConstantFloor_le_zeta
#print axioms fullConstant_interval

end V39PublicSchedule
