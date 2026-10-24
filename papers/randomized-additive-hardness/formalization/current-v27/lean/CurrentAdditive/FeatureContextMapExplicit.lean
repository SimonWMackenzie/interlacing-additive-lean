import CurrentAdditive.FeatureContextMap
import CurrentAdditive.FeatureMapClock

namespace CurrentAdditive.FeatureContextMap

open EthInapproximability.CurrentPaper
open CurrentAdditive.FeatureMapPairLoader

noncomputable section

def totalBudget (M : BitMachine.Machine) (framed : Bool)
 (context : List Bool) (xs : List (List Bool))
 (f : List Bool → List Bool) (b : List Bool → Nat) : Nat :=
 FeatureMapInitialize.budget framed context xs +
 FeatureMapClock.sumCap M framed context (FeatureMapHeaders.output framed xs.length)
   f b [] xs + 1

theorem sumClock_le_totalBudget (M : BitMachine.Machine) (framed : Bool)
 (context : List Bool) (xs : List (List Bool))
 (f : List Bool → List Bool) (b : List Bool → Nat)
 (hM : ∀ w∈xs,M.OutputsWithin (packet context w) (f w) (b w)) :
 sumClock M framed context xs f b hM ≤ totalBudget M framed context xs f b := by
 classical
 have h := FeatureMapClock.remaining_le M framed context
   (FeatureMapHeaders.output framed xs.length) f b xs hM [] xs (by simp)
 exact Nat.add_le_add_right (Nat.add_le_add_left h _) 1

theorem outputs_explicit (M : BitMachine.Machine) (framed : Bool)
 (context : List Bool) (xs : List (List Bool))
 (f : List Bool → List Bool) (b : List Bool → Nat)
 (hM : ∀ w∈xs,M.OutputsWithin (packet context w) (f w) (b w)) :
 (machine M framed).OutputsWithin (packet context (SourceListEncoding.encode xs))
   (result framed xs f) (totalBudget M framed context xs f b) :=
 BitMachine.outputsWithin_mono (machine M framed)
   (outputs M framed context xs f b hM)
   (sumClock_le_totalBudget M framed context xs f b hM)

#print axioms outputs_explicit

end
end CurrentAdditive.FeatureContextMap
