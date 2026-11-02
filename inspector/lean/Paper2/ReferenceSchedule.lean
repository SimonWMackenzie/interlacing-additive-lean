import Paper2.ReferenceCertificateTree

/-!
# Globally halving reference-certificate floor

The runner requires a floor defined and halving at every natural depth.
Within the actual prefix depth it is the paper's dyadic capacity floor.
-/

namespace Paper2.ReferenceSchedule

noncomputable def floor (w : ℕ) (x : ℝ) (d : ℕ) : ℝ :=
  2 * w * x / (2 : ℝ) ^ d

theorem floor_zero (w : ℕ) (x : ℝ) : floor w x 0 = 2 * w * x := by
  simp [floor]

theorem floor_half (w : ℕ) (x : ℝ) (d : ℕ) :
    floor w x d = 2 * floor w x (d + 1) := by
  unfold floor
  rw [pow_succ]
  have h : (0 : ℝ) ≠ 2 ^ d := by positivity
  field_simp

theorem floor_dyadic {w r d : ℕ} (x : ℝ)
    (hw : w = 2 ^ r) (hd : d ≤ r) :
    floor w x d = 2 * (2 : ℝ) ^ (r - d) * x := by
  unfold floor
  rw [hw]
  have hpow : (2 : ℝ) ^ (r - d) = (2 : ℝ) ^ r / (2 : ℝ) ^ d := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num : (2 : ℝ) ≠ 0) hd]
    ring
  rw [hpow]
  push_cast
  ring

end Paper2.ReferenceSchedule

#print axioms Paper2.ReferenceSchedule.floor_half
#print axioms Paper2.ReferenceSchedule.floor_dyadic
