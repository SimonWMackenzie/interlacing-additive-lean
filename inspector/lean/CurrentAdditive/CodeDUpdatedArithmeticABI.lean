import CurrentAdditive.CodeDUpdatedEntryClockV2

/-!
The exact arithmetic input to the physical pair-list writer. For each source
position i, the new weight is old weight minus the selected minimum ratio
times the Gauss dependence coefficient at i. This is the same executable
array computed by SequentialCode.eliminateWeights.
-/

namespace CurrentAdditive.CodeDUpdatedArithmeticABI

open SequentialCode

def candidateWeights {α : Type*} (source : Array (α × ℚ))
    (coeff : Array ℚ) (ratio : ℚ) : Array ℚ :=
  Array.ofFn (n := (source.map Prod.snd).size) (fun i =>
    (source.map Prod.snd)[i] - ratio * (coeff[i.val]?.getD 0))

theorem eliminateWeights_eq_candidate {α : Type*}
    (source : Array (α × ℚ)) (coeff : Array ℚ)
    (ratio : ℚ) (updated : Array ℚ)
    (hratio : minimumRatio (source.map Prod.snd) coeff = some ratio)
    (helim : eliminateWeights (source.map Prod.snd) coeff = some updated) :
    updated = candidateWeights source coeff ratio := by
  simpa [candidateWeights, eliminateWeights, hratio] using helim.symm

theorem pairItems_eliminate {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (ratio : ℚ) (updated : Array ℚ)
    (hratio : minimumRatio (source.map Prod.snd) coeff = some ratio)
    (helim : eliminateWeights (source.map Prod.snd) coeff = some updated) :
    CodeDUpdatedEntryList.pairItems source updated =
      CodeDUpdatedEntryList.pairItems source
        (candidateWeights source coeff ratio) := by
  rw [eliminateWeights_eq_candidate source coeff ratio updated hratio helim]

#print axioms eliminateWeights_eq_candidate
#print axioms pairItems_eliminate

end CurrentAdditive.CodeDUpdatedArithmeticABI
