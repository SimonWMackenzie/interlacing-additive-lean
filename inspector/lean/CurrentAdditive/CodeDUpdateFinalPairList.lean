import CurrentAdditive.CodeDUpdateRequestABI
import CurrentAdditive.CodeDUpdateFinalPairJoin
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! Physical ordered map from per-position requests to old-entry/new-weight pairs. -/

namespace CurrentAdditive.CodeDUpdateFinalPairList

open EthInapproximability.CurrentPaper
open CodeDUpdateRequestABI

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine CodeDUpdateFinalPairJoin.machine

noncomputable def result (requests : List (List Bool)) : List Bool :=
  CodeDCodecV2.encodeItems (requests.map CodeDUpdateFinalPairJoin.output)

noncomputable def clock (requests : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine CodeDUpdateFinalPairJoin.machine)
    requests
    (SourceListMachineOuterFramed.framedOutput CodeDUpdateFinalPairJoin.output)
    (SourceListMachineOuterFramed.framedBound
      CodeDUpdateFinalPairJoin.output CodeDUpdateFinalPairJoin.clock)

theorem outputs (requests : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems requests)
      (result requests) (clock requests) := by
  have h := SourceListMachineOuterFramed.outputsWithin
    CodeDUpdateFinalPairJoin.machine requests
    CodeDUpdateFinalPairJoin.output CodeDUpdateFinalPairJoin.clock
    (by intro x _; exact CodeDUpdateFinalPairJoin.outputs x)
  simpa only [machine, result, clock, CodeDCodecV2.encodeItems] using h

def expectedPairs {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) : List (List Bool) :=
  (List.range source.size).filterMap (fun i =>
    (source[i]?).map (fun old =>
      CodeDUpdatedEntryFields.pairPacket
        (CodeDCanonicalSourceV2.canonicalEntry old)
        (old.2 - lambda * (coeff[i]?.getD 0))))

theorem request_map_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    (requestItems source coeff lambda).map CodeDUpdateFinalPairJoin.output =
      expectedPairs source coeff lambda := by
  unfold requestItems expectedPairs
  simp only [List.map_filterMap]
  apply List.filterMap_congr
  intro i hi
  cases hs : source[i]? with
  | none => simp
  | some old =>
      simp [CodeDUpdateFinalPairJoin.output_request,
        CodeDCanonicalSourceV2.canonicalEntry,
        CodeDCanonicalSourceV2.rawOfRat_valid,
        CodeDCanonicalSourceV2.rawOfRat_value]

theorem writes_expected_pairs {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    machine.OutputsWithin (requestPacketList source coeff lambda)
      (CodeDCodecV2.encodeItems (expectedPairs source coeff lambda))
      (clock (requestItems source coeff lambda)) := by
  have h := outputs (requestItems source coeff lambda)
  simp only [result, requestPacketList] at h ⊢
  rw [request_map_exact] at h
  exact h

theorem expectedPairs_eq_pairItems {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    expectedPairs source coeff lambda =
      CodeDUpdatedEntryList.pairItems source
        (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda) := by
  unfold expectedPairs CodeDUpdatedEntryList.pairItems
  have hsize :
      (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).size =
        source.size := by
    simp [CodeDUpdatedArithmeticABI.candidateWeights]
  rw [hsize]
  apply List.filterMap_congr
  intro i hi
  have hi : i < source.size := List.mem_range.mp hi
  cases hs : source[i]? with
  | none => simp [hs]
  | some old =>
      have hget : source[i] = old := by
        simpa [Array.getElem?_eq_getElem hi] using hs
      simp [hs, CodeDUpdatedArithmeticABI.candidateWeights, hi,
        CodeDCanonicalSourceV2.canonicalEntry, hget]

theorem writes_pairItems {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    machine.OutputsWithin (requestPacketList source coeff lambda)
      (CodeDCodecV2.encodeItems
        (CodeDUpdatedEntryList.pairItems source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))
      (clock (requestItems source coeff lambda)) := by
  rw [← expectedPairs_eq_pairItems]
  exact writes_expected_pairs source coeff lambda

#print axioms outputs
#print axioms request_map_exact
#print axioms writes_expected_pairs
#print axioms expectedPairs_eq_pairItems
#print axioms writes_pairItems

end CurrentAdditive.CodeDUpdateFinalPairList
