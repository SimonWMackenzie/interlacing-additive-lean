import CurrentAdditive.CodeDUpdateRequestABI
import CurrentAdditive.CodeDUpdateSubtractPairJoin
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! Physical ordered map from source requests to subtraction operand packets. -/

namespace CurrentAdditive.CodeDUpdateSubtractPairList

open EthInapproximability.CurrentPaper
open CodeDUpdateRequestABI

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine CodeDUpdateSubtractPairJoin.machine

noncomputable def result (requests : List (List Bool)) : List Bool :=
  CodeDCodecV2.encodeItems (requests.map CodeDUpdateSubtractPairJoin.output)

noncomputable def clock (requests : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine CodeDUpdateSubtractPairJoin.machine)
    requests
    (SourceListMachineOuterFramed.framedOutput CodeDUpdateSubtractPairJoin.output)
    (SourceListMachineOuterFramed.framedBound
      CodeDUpdateSubtractPairJoin.output CodeDUpdateSubtractPairJoin.clock)

theorem outputs (requests : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems requests)
      (result requests) (clock requests) := by
  have h := SourceListMachineOuterFramed.outputsWithin
    CodeDUpdateSubtractPairJoin.machine requests
    CodeDUpdateSubtractPairJoin.output CodeDUpdateSubtractPairJoin.clock
    (by intro x _; exact CodeDUpdateSubtractPairJoin.outputs x)
  simpa only [machine, result, clock, CodeDCodecV2.encodeItems] using h

theorem request_map_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    (requestItems source coeff lambda).map CodeDUpdateSubtractPairJoin.output =
    (List.range source.size).filterMap (fun i =>
      (source[i]?).map (fun old =>
        CodeDPairProductTargetV2.pairBytes
          (CodeDCanonicalSourceV2.rawOfRat old.2)
          (CodeDCanonicalSourceV2.rawOfRat
            (lambda * (coeff[i]?.getD 0))))) := by
  unfold requestItems
  simp only [List.map_filterMap]
  apply List.filterMap_congr
  intro i hi
  cases hs : source[i]? with
  | none => simp
  | some old =>
      simp [CodeDUpdateSubtractPairJoin.output_request,
        CodeDCanonicalSourceV2.canonicalEntry]

theorem writes_subtract_requests {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    machine.OutputsWithin (requestPacketList source coeff lambda)
      (CodeDCodecV2.encodeItems
        ((List.range source.size).filterMap (fun i =>
          (source[i]?).map (fun old =>
            CodeDPairProductTargetV2.pairBytes
              (CodeDCanonicalSourceV2.rawOfRat old.2)
              (CodeDCanonicalSourceV2.rawOfRat
                (lambda * (coeff[i]?.getD 0)))))))
      (clock (requestItems source coeff lambda)) := by
  have h := outputs (requestItems source coeff lambda)
  simp only [result, requestPacketList] at h ⊢
  rw [request_map_exact] at h
  exact h

#print axioms outputs
#print axioms request_map_exact
#print axioms writes_subtract_requests

end CurrentAdditive.CodeDUpdateSubtractPairList
