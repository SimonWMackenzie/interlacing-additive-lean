import CurrentAdditive.NextClockStages

/-! The dimension preparation clock, charged against literal public source
cells and then bounded by encoded source length. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper
open CurrentAdditive.SmallBias
open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly

set_option maxHeartbeats 2000000

theorem dimensionCopyCost_eq {t : ℕ} (x : YaoSource t) (u : ℕ) :
    CopyFill.fillCost (dimensionJobs t) (sourceFieldOutput x u) =
      (2*x.1+2) +
      (2*(paddedEdgeCount x.2.1)^(2^(t-1))+2) +
      (2*paddedEdgeCount x.2.1+2) +
      (2*((2^publicFieldDegree (paddedEdgeBits x.2.1) t)^2)+2) := by
  obtain ⟨_, _, hv, _, hH, _, _, hcap, hR2⟩ :=
    sourceFieldOutput_public x u
  simp [CopyFill.fillCost, dimensionJobs, hv, hcap, hH, hR2,
    Nat.add_assoc]

def dimensionBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  let H := paddedEdgeCount x.2.1
  let cap := H^(2^(t-1))
  let q := 2^publicFieldDegree (paddedEdgeBits x.2.1) t
  ((2*x.1+2)+(2*cap+2)+(2*H+2)+(2*q^2+2)) + 1 +
    (2^(t-1)+1) + 1 +
    (MatrixAddressMachine.exactTime x.1 cap 0 +
     MatrixAddressMachine.exactTime (2^(t-1)) H 0 +
     MatrixAddressMachine.exactTime ((2^(t-1))*H) (q^2) 0+2)+1

theorem dimension_steps_le_budget {t : ℕ} (x : YaoSource t)
    (u v : ℕ)
    (hv : v ≤
      CopyFill.fillCost (dimensionJobs t) (sourceFieldOutput x u) + 1 +
      (2^(t-1)+1) + 1 +
      (MatrixAddressMachine.exactTime x.1
        ((paddedEdgeCount x.2.1)^(2^(t-1))) 0 +
       MatrixAddressMachine.exactTime (2^(t-1))
         (paddedEdgeCount x.2.1) 0 +
       MatrixAddressMachine.exactTime
         ((2^(t-1))*(paddedEdgeCount x.2.1))
         ((2^publicFieldDegree (paddedEdgeBits x.2.1) t)^2) 0+2)+1) :
    v ≤ dimensionBudget x := by
  rw [dimensionCopyCost_eq] at hv
  exact hv

theorem poly_dimensionBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (dimensionBudget (t := t)) := by
  have hv := poly_v (t := t)
  have hH := poly_H (t := t)
  have hcap := poly_public_cap t
  have hq := poly_public_order t ht
  unfold dimensionBudget MatrixAddressMachine.exactTime
  repeat' poly_step

def sourceDimensionsBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  sourceFieldBudget x + dimensionBudget x + 1

theorem poly_sourceDimensionsBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (sourceDimensionsBudget (t := t)) := by
  unfold sourceDimensionsBudget
  exact poly_add
    (poly_add (poly_sourceFieldBudget t ht) (poly_dimensionBudget t ht))
    (poly_const 1)

#print axioms dimensionCopyCost_eq
#print axioms dimension_steps_le_budget
#print axioms poly_dimensionBudget
#print axioms poly_sourceDimensionsBudget

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
