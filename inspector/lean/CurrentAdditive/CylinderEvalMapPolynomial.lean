import CurrentAdditive.FeatureContextMapExplicit
import CurrentAdditive.FeatureContextMapPolynomial

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CurrentAdditive.CylinderEvalMapPolynomial

open EthInapproximability.CurrentPaper
open CurrentAdditive.FeatureMapPairLoader

theorem sumCap_eq (M : BitMachine.Machine) (framed : Bool) (context header : List Bool)
    (f : List Bool → List Bool) (b : List Bool → ℕ)
    (pre suf : List (List Bool)) :
    ContextMapClockModel.sumCap M framed context header f b pre suf =
      FeatureMapClock.sumCap M framed context header f b pre suf := by
  induction suf generalizing pre with
  | nil => rfl
  | cons w tail ih =>
    simp only [ContextMapClockModel.sumCap,FeatureMapClock.sumCap]
    rw [ih]
    rfl

theorem totalBudget_eq (M : BitMachine.Machine) (framed : Bool) (context : List Bool)
    (xs : List (List Bool)) (f : List Bool → List Bool) (b : List Bool → ℕ) :
    FeatureContextMapPolynomial.totalBudget M framed context xs f b =
      FeatureContextMap.totalBudget M framed context xs f b := by
  unfold FeatureContextMapPolynomial.totalBudget FeatureContextMap.totalBudget
  rw [sumCap_eq]

theorem budget_le_uniform (M : BitMachine.Machine) (framed : Bool)
    (context : List Bool) (xs : List (List Bool))
    (f : List Bool → List Bool) (b : List Bool → ℕ) (P Q : ℕ)
    (hP : ∀w∈xs,b w≤P) (hQ : ∀w∈xs,(f w).length≤Q) :
    FeatureContextMap.totalBudget M framed context xs f b ≤
      FeatureContextMapPolynomial.coefficient M framed*
        ((packet context (SourceListEncoding.encode xs)).length+P+Q+1)^
          FeatureContextMapPolynomial.exponent M framed := by
  simpa only [totalBudget_eq,FeatureMapSizeBounds.inputSize] using
    FeatureContextMapPolynomial.budget_le_uniform M framed context xs f b P Q hP hQ

theorem uniform_from_callback (M : BitMachine.Machine) (framed : Bool) (a e : ℕ) :
    ∃ K E : ℕ,∀ (context : List Bool) (xs : List (List Bool))
      (f : List Bool → List Bool) (b : List Bool → ℕ),
      (∀w∈xs,M.OutputsWithin (packet context w) (f w) (b w)) →
      (∀w∈xs,b w≤a*((packet context w).length+1)^e) →
      FeatureContextMap.totalBudget M framed context xs f b ≤
        K*((packet context (SourceListEncoding.encode xs)).length+1)^E := by
  obtain ⟨K,E,h⟩ := FeatureContextMapPolynomial.uniform_from_callback M framed a e
  refine ⟨K,E,?_⟩
  intro context xs f b hM hb
  simpa only [totalBudget_eq,FeatureMapSizeBounds.inputSize] using h context xs f b hM hb

end CurrentAdditive.CylinderEvalMapPolynomial

#print axioms CurrentAdditive.CylinderEvalMapPolynomial.uniform_from_callback
