import CurrentAdditive.GeneratedWAlignmentScalar
import CurrentAdditive.DeterministicParameters

/-! Cast the public Appendix I schedule's mass guards to the real-valued
physical owner accounting theorem. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open CurrentAdditive.DeterministicParameters
open scoped BigOperators

theorem indexed_alignment_public_scalar_bounds
    {Owners : Type*} [Fintype Owners]
    (L Δ n m C : ℕ) (γ : ℚ)
    [NeZero (q₂ L)] (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hadm : Admissible L Δ n m C γ)
    (defect : Owners → ℝ)
    (hcard : Fintype.card Owners ≤ w L)
    (hdefect : Finset.univ.sum defect ≤
      (η L Δ γ : ℝ) / (8 * (127/128 : ℝ))) :
    4 * ownerException L Δ γ ≤ w L ∧
    (Kstar L : ℝ) * ownerException L Δ γ ≤
      (η L Δ γ : ℝ) * w L / 16 ∧
    2 * (1/256 : ℝ) * w L *
      (Finset.univ.sum (fun v : Owners =>
        2 * q₂ L * (x L : ℝ) + 5 * defect v + 2 / q₂ L)) ≤
      3 * (η L Δ γ : ℝ) * w L / 32 := by
  have hη : (0 : ℝ) ≤ (η L Δ γ : ℝ) := by
    exact_mod_cast (eta_pos L Δ γ hΔ hγ).le
  have hx : (0 : ℝ) ≤ (x L : ℝ) := (x_real_pos L).le
  have hq : 0 < q₂ L := NeZero.pos _
  have hloss1 : 4 * (1/256 : ℝ) * w L * q₂ L * (x L : ℝ) ≤
      (η L Δ γ : ℝ) / 32 := by
    have h : (((4 * (1/256 : ℚ) * w L * q₂ L * x L : ℚ) : ℝ)) ≤
        ((η L Δ γ / 32 : ℚ) : ℝ) := Rat.cast_le.mpr hadm.loss1
    norm_num at h ⊢
    exact h
  have hloss2 : 4 * (1/256 : ℝ) * w L / q₂ L ≤
      (η L Δ γ : ℝ) / 32 := by
    have h : (((4 * (1/256 : ℚ) * w L / q₂ L : ℚ) : ℝ)) ≤
        ((η L Δ γ / 32 : ℚ) : ℝ) := Rat.cast_le.mpr hadm.loss2
    norm_num at h ⊢
    exact h
  have hmass : (Kstar L : ℝ) * ownerException L Δ γ ≤
      (η L Δ γ : ℝ) * w L / 16 := by
    exact_mod_cast hadm.owner_mass
  exact ⟨hadm.owner_reserve, hmass,
    indexed_pair_receipt_scalar (w L) (q₂ L) (x L : ℝ)
      (η L Δ γ : ℝ) defect hη hx hq hcard hdefect hloss1 hloss2⟩

#print axioms indexed_alignment_public_scalar_bounds

end CurrentAdditive.DeterministicIndexedMatrix.Sources
