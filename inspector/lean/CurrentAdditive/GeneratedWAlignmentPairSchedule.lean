import CurrentAdditive.GeneratedWAlignmentSchedule

/-! Public parameter inequalities for the fixed-E owner-to-owner receipt
bound on the generated source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open CurrentAdditive.DeterministicParameters

theorem indexed_pair_public_numeric
    (L Δ n m C : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hadm : Admissible L Δ n m C γ) :
    2 * (s L : ℝ) * (x L : ℝ) ≤
      1 - (η L Δ γ : ℝ) * s L / (2 * (255/256 : ℝ)) ∧
    49/64 + 2 * (s L : ℝ) * (x L : ℝ) <
      ((99/100 : ℝ) + (255/256 : ℝ)^2 - 1) /
        (255/256 : ℝ)^2 ∧
    2 * (s L : ℝ) * (x L : ℝ) ≤ 1/8 ∧
    2 * (q₂ L : ℝ) * (x L : ℝ) ≤ 1/8 := by
  have hs : 2 * (s L : ℝ) * (x L : ℝ) ≤ 1/1000 := by
    have h : (((2 * (s L : ℚ) * x L : ℚ) : ℝ)) ≤
        ((1/1000 : ℚ) : ℝ) := Rat.cast_le.mpr hadm.double_s_x
    norm_num at h ⊢
    exact h
  have hq : 2 * (q₂ L : ℝ) * (x L : ℝ) ≤ 1/8 := by
    have h : (((2 * (q₂ L : ℚ) * x L : ℚ) : ℝ)) ≤
        ((1/8 : ℚ) : ℝ) := Rat.cast_le.mpr hadm.double_q₂_x
    norm_num at h ⊢
    exact h
  have hconst := fixed_numeric_guards Δ γ
  have hmiddle :
      (49/64 : ℝ) + 1/1000 <
      ((99/100 : ℝ) + (255/256 : ℝ)^2 - 1) /
        (255/256 : ℝ)^2 := by
    have h : (((((99/100 + (255/256 : ℚ)^2 - 1) /
        (255/256 : ℚ)^2) - 1/1000 : ℚ) : ℝ)) >
        ((49/64 : ℚ) : ℝ) := Rat.cast_lt.mpr hconst.2.1
    norm_num at h ⊢
  have hfloor :
      1/1000 < 1 - (η L Δ γ : ℝ) * s L / (2 * (255/256 : ℝ)) := by
    have h : (((1 - c Δ γ / (2 * (255/256 : ℚ)) : ℚ) : ℝ)) >
        ((1/1000 : ℚ) : ℝ) := Rat.cast_lt.mpr hconst.2.2
    have hηs : (η L Δ γ : ℝ) * s L = (c Δ γ : ℝ) := by
      have hq : η L Δ γ * s L = c Δ γ := by
        unfold η
        have hspos : (0 : ℚ) < s L := by exact_mod_cast s_pos L
        field_simp
      exact_mod_cast hq
    norm_num at h ⊢
    rw [hηs]
    nlinarith
  refine ⟨hs.trans hfloor.le, ?_, hs.trans (by norm_num), hq⟩
  linarith

#print axioms indexed_pair_public_numeric

end CurrentAdditive.DeterministicIndexedMatrix.Sources
