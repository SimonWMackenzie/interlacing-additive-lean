import CurrentAdditive.FiniteV35
import CurrentAdditive.ScheduleCeilingV35

namespace FiniteV35Schedule

open Paper2.RestorationCoverParameters
open Paper2.ProductProjections

noncomputable def paperB1 (Q : ℕ) (η : ℝ) : ℕ :=
  Nat.ceil (((paperBTheta Q + 1 : ℕ) : ℝ) / η)

noncomputable def paperB2 (Q : ℕ) : ℕ := 100 * (paperBTheta Q + 1)

noncomputable def paperTStar (Q : ℕ) : ℕ :=
  Paper2.SourcePadding.powTwoCeil (1024 * (paperBTheta Q + 1))

noncomputable def paperMStar (Q : ℕ) : ℕ := paperTStar Q / 4 + 1

noncomputable def paperE0 (Q : ℕ) (η : ℝ) : ℕ :=
  (paperB1 Q η - 1) + paperMStar Q * (paperB2 Q - 1)

noncomputable def paperEExc (Q : ℕ) (η : ℝ) : ℕ :=
  Nat.ceil ((16 * (paperE0 Q η : ℝ)) / 7)

theorem paperB1_eq_B1 {Q : ℕ} (hQ : 0 < Q) (η : ℝ) :
    paperB1 Q η = B1 Q η := by
  simp [paperB1, B1, paperBTheta_eq_b hQ]

theorem paperB2_eq_B2 {Q : ℕ} (hQ : 0 < Q) :
    paperB2 Q = B2 Q := by
  simp [paperB2, B2, paperBTheta_eq_b hQ]

theorem paperTStar_eq_tStar {Q : ℕ} (hQ : 0 < Q) :
    paperTStar Q = tStar Q := by
  simp [paperTStar, tStar, paperBTheta_eq_b hQ]

theorem paperMStar_eq_manySize {Q : ℕ} (hQ : 0 < Q) :
    paperMStar Q = FiniteV35.manySize Q := by
  simp [paperMStar, FiniteV35.manySize, paperTStar_eq_tStar hQ]

theorem paperE0_eq_ownerBudget {Q : ℕ} (hQ : 0 < Q) (η : ℝ) :
    paperE0 Q η = FiniteV35.ownerBudget Q η := by
  simp [paperE0, FiniteV35.ownerBudget, paperB1_eq_B1 hQ,
    paperB2_eq_B2 hQ, paperMStar_eq_manySize hQ]

theorem paperEExc_eq_destinationBudget {Q : ℕ} (hQ : 0 < Q)
    (η : ℝ) :
    paperEExc Q η = FiniteV35.destinationBudget Q η := by
  simp [paperEExc, FiniteV35.destinationBudget,
    paperE0_eq_ownerBudget hQ]

theorem paperThetaHalfStar {Q : ℕ} (hQ : 0 < Q) :
    (2 : ℝ)^(-((paperTStar Q : ℝ)/1024)) ≤ theta Q/2 := by
  simpa only [paperTStar_eq_tStar hQ] using
    FiniteV35.theta_half_ge_star hQ

theorem paperB1Gap {Q : ℕ} (hQ : 0 < Q)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    (1-η)^paperB1 Q η < theta Q := by
  simpa only [paperB1_eq_B1 hQ] using B1_gap hQ hη hη1

theorem paperB2Gap {Q : ℕ} (hQ : 0 < Q) :
    (99/100 : ℝ)^paperB2 Q < theta Q := by
  simpa only [paperB2_eq_B2 hQ] using B2_gap hQ

theorem paperNonownerBudget {Q : ℕ} (hQ : 0 < Q)
    (η : ℝ) (n : ℕ)
    (hdeficit : (7/16 : ℝ)*(n : ℝ) ≤ paperE0 Q η) :
    n ≤ paperEExc Q η := by
  rw [paperE0_eq_ownerBudget hQ] at hdeficit
  simpa only [paperEExc_eq_destinationBudget hQ] using
    FiniteV35.nonowner_count_le_destinationBudget Q η n hdeficit

/-- The owner-projection conclusion with every budget written from the
paper's real-log ceiling, rather than the implementation's `Nat.clog`. -/
theorem paperOwnerProjections {K : Type*} [Fintype K]
    (κ : Paper2.FiniteLaw K) (w Q : ℕ) (hQ : 0 < Q)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (Y' : Set (Fin w → K))
    (hY : theta Q ≤ (κ.iid w).prob (· ∈ Y')) :
    ∃ E : Finset (Fin w), E.card ≤ paperE0 Q η ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E →
        1-η ≤ projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card ≤ paperMStar Q →
        Disjoint S E →
        (99/100 : ℝ) ≤ projectionMass (fun _ => κ) (· ∈ Y') S) := by
  simpa only [paperE0_eq_ownerBudget hQ,
    paperMStar_eq_manySize hQ] using
      FiniteV35.owner_projections κ w Q hQ η hη hη1 Y' hY

#print axioms paperB1_eq_B1
#print axioms paperB2_eq_B2
#print axioms paperTStar_eq_tStar
#print axioms paperMStar_eq_manySize
#print axioms paperE0_eq_ownerBudget
#print axioms paperEExc_eq_destinationBudget
#print axioms paperThetaHalfStar
#print axioms paperB1Gap
#print axioms paperB2Gap
#print axioms paperNonownerBudget
#print axioms paperOwnerProjections

end FiniteV35Schedule
