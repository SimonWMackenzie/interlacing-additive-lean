import CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain
import CurrentAdditive.DeterministicETHPhysicalFront
import CurrentAdditive.DeterministicFixedDecision

/-! The indexed-seed fixed-gap main under the inherited physical all-input
validator and finite-formula arm. The main premise covers every valid large
formula, matching the fixed-gap endpoint's actual quantifier. -/

namespace CurrentAdditive.DeterministicFixedPhysicalIndexedFront

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicETHPhysicalFront (frontClock frontClock_polynomial_absorption)

noncomputable def fullMachine (cutoff : ℕ)
    (producer Me : BitMachine.Machine) (u : ℝ) : BitMachine.Machine :=
  Front.front cutoff
    (CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain.machine producer Me u)

theorem fullMachine_outputs (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (w : List Bool) :
    (fullMachine cutoff producer Me u).OutputsWithin w
      [EncodedETHTail.satAnswer w] (frontClock cutoff Tmain w) := by
  exact Front.front_outputs hcutoff
    (CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain.machine producer Me u)
    Tmain hmain w

theorem fullMachine_polytime (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (K d : ℕ)
    (hmainClock : ∀ w, Tmain w ≤ K * (w.length+1)^d) :
    BitMachine.Polytime (fun w => [EncodedETHTail.satAnswer w]) := by
  let C := K + 263 + 2*((Front.phi cutoff true).length+
    (Front.phi cutoff false).length) +
    Tmain (Front.phi cutoff true) + Tmain (Front.phi cutoff false)
  refine ⟨fullMachine cutoff producer Me u, C, d+3, ?_⟩
  intro w
  have hr := fullMachine_outputs cutoff hcutoff producer Me u Tmain hmain w
  have hb := frontClock_polynomial_absorption cutoff K 1 1 d Tmain w
    (by omega) (by simpa using hmainClock w)
  exact BitMachine.outputsWithin_mono _ hr (by simpa [C] using hb)

theorem np_subset_p_of_main
    (hard : EncodedComplexity.NPHard EncodedCNF.Language)
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (K d : ℕ)
    (hmainClock : ∀ w, Tmain w ≤ K * (w.length+1)^d) :
    ∀ L, EncodedComplexity.InNP L →
      ComplexityReductionClosure.InP L := by
  apply CurrentAdditive.DeterministicFixedDecision.np_subset_p_of_canonical_decider
    hard EncodedETHTail.satAnswer
    (fullMachine_polytime cutoff hcutoff producer Me u Tmain hmain K d hmainClock)
  · intro f hf
    simp only [EncodedETHTail.satAnswer, decide_eq_true_eq]
    exact EncodedCNF.encode_mem_iff f hf
  · intro w hw
    simp [EncodedETHTail.satAnswer, EncodedCNF.malformed_not_mem hw]

#print axioms fullMachine_outputs
#print axioms fullMachine_polytime
#print axioms np_subset_p_of_main

end CurrentAdditive.DeterministicFixedPhysicalIndexedFront
