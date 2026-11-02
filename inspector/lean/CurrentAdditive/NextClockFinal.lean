import CurrentAdditive.NextClockHeader

/-! One polynomial envelope for every physical stage on valid encoded Yao
sources. The all-input timeout wrapper is a separate boundary. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper
open CurrentAdditive.SmallBias
open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

set_option maxHeartbeats 2000000

theorem thresholdWriterClock_eq_budget {t : ℕ} (x : YaoSource t)
    (u c : ℕ)
    (hpacked : sourceFieldOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1))) :
    thresholdWriterClock x u c = thresholdWriterBudget x := by
  unfold thresholdWriterClock writerAfterThresholdClock thresholdWriterBudget
  dsimp only
  rw [writerCopyCost_eq x u c hpacked]
  rw [headerCopyCost_eq x u c]
  rfl

def rendererBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  sourceDimensionsBudget x + thresholdWriterBudget x + 1

theorem poly_rendererBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (rendererBudget (t := t)) := by
  unfold rendererBudget
  exact poly_add
    (poly_add (poly_sourceDimensionsBudget t ht)
      (poly_thresholdWriterBudget t ht))
    (poly_const 1)

theorem renderer_steps_le_budget {t : ℕ} (x : YaoSource t)
    (c u v steps : ℕ)
    (hu : u ≤ CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime
        (publicFieldDegree (paddedEdgeBits x.2.1) t)
        (paddedEdgeCount x.2.1*(arity t+1)) +
      55*2^publicFieldDegree (paddedEdgeBits x.2.1) t *
        2^(publicFieldDegree (paddedEdgeBits x.2.1) t/2) *
        (publicFieldDegree (paddedEdgeBits x.2.1) t+1)^2 + 2 +
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1)))
    (hv : v ≤
      CopyFill.fillCost (dimensionJobs t) (sourceFieldOutput x u) + 1 +
      (2^(t-1)+1) + 1 +
      (MatrixAddressMachine.exactTime x.1
        ((paddedEdgeCount x.2.1)^(2^(t-1))) 0 +
       MatrixAddressMachine.exactTime (2^(t-1))
         (paddedEdgeCount x.2.1) 0 +
       MatrixAddressMachine.exactTime
         ((2^(t-1))*(paddedEdgeCount x.2.1))
         ((2^publicFieldDegree (paddedEdgeBits x.2.1) t)^2) 0+2)+1)
    (hpacked : sourceFieldOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1)))
    (hsteps : steps ≤ sourceDimensionsClock x u v +
      thresholdWriterClock x u c + 1) :
    steps ≤ rendererBudget x := by
  have hu' := field_steps_le_budget x c u hu
  have hv' := dimension_steps_le_budget x u v hv
  have hw := thresholdWriterClock_eq_budget x u c hpacked
  have hf : sourceFieldClock x u ≤
      sourceFieldClock x (fieldBudget x) := by
    unfold sourceFieldClock
    dsimp only
    omega
  have hs : sourceDimensionsClock x u v ≤
      sourceDimensionsBudget x := by
    unfold sourceDimensionsClock sourceDimensionsBudget sourceFieldBudget
    omega
  rw [hw] at hsteps
  unfold rendererBudget
  omega

#print axioms thresholdWriterClock_eq_budget
#print axioms poly_rendererBudget
#print axioms renderer_steps_le_budget

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
