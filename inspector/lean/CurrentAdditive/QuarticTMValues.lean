import CurrentAdditive.QuarticTMFront

namespace Paper2.CurrentAdditive.QuarticNumericFront.TM27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule

theorem source_dims_of_MFacts (n m L Δ k : ℕ) (γ : ℚ)
    (FM : TMFront.MK → List Bool)
    (hMF : TMFront.MFacts
      (TMFront.thrVal k (vector27 n m L Δ γ)) k L FM) :
    FM 10 = List.replicate
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) true ∧
    FM 13 = List.replicate
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) true := by
  have hsample := sample_values27 n m L Δ k γ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hm10, -, -, hm13, -⟩ := hMF
  constructor
  · change FM 10 = List.replicate
      (FullFront.mYV (TMFront.thrVal k (vector27 n m L Δ γ)) k) true at hm10
    rw [hsample.2] at hm10
    exact hm10
  · change FM 13 = List.replicate
      (FullFront.mXV (TMFront.thrVal k (vector27 n m L Δ γ)) k L) true at hm13
    rw [hsample.1] at hm13
    exact hm13

end
end Paper2.CurrentAdditive.QuarticNumericFront.TM27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.TM27.source_dims_of_MFacts
