import CurrentAdditive.DeterministicFixedPhysicalIndexedFront

/-! The fixed-gap front's clock is totalized from canonical large formulas.
Malformed and small inputs are physically routed before the main call, so no
source clock claim is needed on those inputs. -/

namespace CurrentAdditive.DeterministicFixedPhysicalIndexedTotalClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicFixedPhysicalIndexedFront

def totalMainTime (cutoff : ℕ) (Tmain : List Bool → ℕ)
    (w : List Bool) : ℕ :=
  match EncodedCNF.decode w with
  | none => 0
  | some f => if cutoff ≤ f.variables then Tmain w else 0

theorem totalMainTime_large (cutoff : ℕ) (Tmain : List Bool → ℕ)
    (f : EncodedCNF.Formula) (hf : f.Valid)
    (hlarge : cutoff ≤ f.variables) :
    totalMainTime cutoff Tmain (EncodedCNF.encode f) =
      Tmain (EncodedCNF.encode f) := by
  simp [totalMainTime, EncodedCNF.decode_encode f hf, hlarge]

theorem totalMainTime_global_bound (cutoff K d : ℕ)
    (Tmain : List Bool → ℕ)
    (hlargeClock : ∀ f : EncodedCNF.Formula, f.Valid →
      cutoff ≤ f.variables →
        Tmain (EncodedCNF.encode f) ≤
          K*((EncodedCNF.encode f).length+1)^d)
    (w : List Bool) :
    totalMainTime cutoff Tmain w ≤ K*(w.length+1)^d := by
  unfold totalMainTime
  cases hdecode : EncodedCNF.decode w with
  | none => simp
  | some f =>
      by_cases hcut : cutoff ≤ f.variables
      · simp only [if_pos hcut]
        have hf := EncodedCNF.decode_valid hdecode
        have hw := EncodedCNF.decode_sound hdecode
        rw [← hw]
        exact hlargeClock f hf hcut
      · simp [hcut]

theorem np_subset_p_of_canonical_main
    (hard : EncodedComplexity.NPHard EncodedCNF.Language)
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (K d : ℕ)
    (hlargeClock : ∀ f : EncodedCNF.Formula, f.Valid →
      cutoff ≤ f.variables →
        Tmain (EncodedCNF.encode f) ≤
          K*((EncodedCNF.encode f).length+1)^d) :
    ∀ L, EncodedComplexity.InNP L →
      ComplexityReductionClosure.InP L := by
  apply np_subset_p_of_main hard cutoff hcutoff producer Me u
    (totalMainTime cutoff Tmain) ?_ K d
    (totalMainTime_global_bound cutoff K d Tmain hlargeClock)
  intro f hf hlarge
  rw [totalMainTime_large cutoff Tmain f hf hlarge]
  exact hmain f hf hlarge

#print axioms totalMainTime_global_bound
#print axioms np_subset_p_of_canonical_main

end CurrentAdditive.DeterministicFixedPhysicalIndexedTotalClock
