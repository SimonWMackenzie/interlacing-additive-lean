import CurrentAdditive.CodeDUpdateRequestABI
import CurrentAdditive.CodeDUpdateProductPairJoin
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! Physical ordered map from source-position requests to λ/coefficient packets. -/

namespace CurrentAdditive.CodeDUpdateProductPairList

open EthInapproximability.CurrentPaper
open CodeDUpdateRequestABI

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine CodeDUpdateProductPairJoin.machine

def result (requests : List (List Bool)) : List Bool :=
  CodeDCodecV2.encodeItems (requests.map CodeDUpdateProductPairJoin.output)

noncomputable def clock (requests : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine CodeDUpdateProductPairJoin.machine)
    requests
    (SourceListMachineOuterFramed.framedOutput CodeDUpdateProductPairJoin.output)
    (SourceListMachineOuterFramed.framedBound
      CodeDUpdateProductPairJoin.output CodeDUpdateProductPairJoin.clock)

theorem outputs (requests : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems requests)
      (result requests) (clock requests) := by
  have h := SourceListMachineOuterFramed.outputsWithin
    CodeDUpdateProductPairJoin.machine requests
    CodeDUpdateProductPairJoin.output CodeDUpdateProductPairJoin.clock
    (by intro x _; exact CodeDUpdateProductPairJoin.outputs x)
  simpa only [machine, result, clock, CodeDCodecV2.encodeItems] using h

theorem request_map_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    (requestItems source coeff lambda).map CodeDUpdateProductPairJoin.output =
    (List.range source.size).filterMap (fun i =>
      (source[i]?).map (fun _ =>
        CodeDPairProductTargetV2.pairBytes
          (CodeDCanonicalSourceV2.rawOfRat lambda)
          (CodeDCanonicalSourceV2.rawOfRat (coeff[i]?.getD 0)))) := by
  unfold requestItems
  simp only [List.map_filterMap]
  apply List.filterMap_congr
  intro i hi
  cases hs : source[i]? with
  | none => simp [hs]
  | some old =>
      simp [hs, CodeDUpdateProductPairJoin.output,
        CodeDUpdateProductPairFields.fields_request]

theorem writes_product_requests {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    machine.OutputsWithin (requestPacketList source coeff lambda)
      (CodeDCodecV2.encodeItems
        ((List.range source.size).filterMap (fun i =>
          (source[i]?).map (fun _ =>
            CodeDPairProductTargetV2.pairBytes
              (CodeDCanonicalSourceV2.rawOfRat lambda)
              (CodeDCanonicalSourceV2.rawOfRat (coeff[i]?.getD 0))))))
      (clock (requestItems source coeff lambda)) := by
  have h := outputs (requestItems source coeff lambda)
  simp only [result, requestPacketList] at h ⊢
  rw [request_map_exact] at h
  exact h

#print axioms outputs
#print axioms request_map_exact
#print axioms writes_product_requests

end CurrentAdditive.CodeDUpdateProductPairList
