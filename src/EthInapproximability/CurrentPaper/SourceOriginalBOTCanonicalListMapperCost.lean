import EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapper
import EthInapproximability.CurrentPaper.SourceListMachineWork

/-! Per-branch, original-n runtime envelope for the generic canonical mapper. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapper

open BitMachine BitMachineEncoding EncodedCommunication

variable {k : ℕ} (B : EncodedETHSource.BOTReduction k)

def inputEnvelope (originalN wordCap : ℕ) : ℕ :=
  2*(originalN+wordCap)+2

noncomputable def callbackEnvelope (originalN wordCap : ℕ) : ℕ :=
  SourceOriginalBOTListMapper.coefficient B *
    (inputEnvelope originalN wordCap+3)^SourceOriginalBOTListMapper.exponent B

noncomputable def outputEnvelope (originalN wordCap : ℕ) : ℕ :=
  inputEnvelope originalN wordCap + callbackEnvelope B originalN wordCap *
    (SourceBOTNormalizedPacketMachine.machine B).pushBound

noncomputable def framedEnvelope (originalN wordCap : ℕ) : ℕ :=
  3*outputEnvelope B originalN wordCap+1

noncomputable def framedTimeEnvelope (originalN wordCap : ℕ) : ℕ :=
  callbackEnvelope B originalN wordCap +
    2*outputEnvelope B originalN wordCap+2 +
    (UnaryBinaryEncoding.coefficient+7)*
      (outputEnvelope B originalN wordCap+1)^2

noncomputable def itemEnvelope (originalN wordCap : ℕ) : ℕ :=
  let F := SourceListMachineOuterFramed.itemMachine
    (SourceBOTNormalizedPacketMachine.machine B)
  let L := inputEnvelope originalN wordCap
  let R := framedEnvelope B originalN wordCap
  let T := framedTimeEnvelope B originalN wordCap
  20*(L+1)*(L+1)+T+4*L+R+
    F.stackCount*(L+T*F.pushBound+1)+9

theorem input_length_le (originalN wordCap : ℕ)
    (g : EncodedETHSource.ValidFormula)
    (hg : (EncodedCNF.encode g.val).length ≤ wordCap) :
    (SourceOriginalBranchPackets.sparsePacket originalN g).length ≤
      inputEnvelope originalN wordCap := by
  rw [SourceOriginalBranchPackets.sparsePacket,
    SourceOriginalBranchPackets.packet_length]
  unfold inputEnvelope
  omega

theorem callback_bound_le (originalN wordCap : ℕ)
    (g : EncodedETHSource.ValidFormula)
    (hg : (EncodedCNF.encode g.val).length ≤ wordCap) :
    SourceOriginalBOTListMapper.itemBound B
      (SourceOriginalBranchPackets.sparsePacket originalN g) ≤
      callbackEnvelope B originalN wordCap := by
  have hi := input_length_le originalN wordCap g hg
  have hp := Nat.pow_le_pow_left (show
    (SourceOriginalBranchPackets.sparsePacket originalN g).length+3 ≤
      inputEnvelope originalN wordCap+3 by omega)
    (SourceOriginalBOTListMapper.exponent B)
  unfold SourceOriginalBOTListMapper.itemBound callbackEnvelope
  exact Nat.mul_le_mul_left _ hp

theorem output_length_le (originalN wordCap : ℕ)
    (g : EncodedETHSource.ValidFormula)
    (hg : (EncodedCNF.encode g.val).length ≤ wordCap) :
    (SourceOriginalBOTListMapper.itemOutput B
      (SourceOriginalBranchPackets.sparsePacket originalN g)).length ≤
      outputEnvelope B originalN wordCap := by
  rw [SourceOriginalBOTListMapper.itemOutput_eq B g originalN]
  have ho := BitMachine.output_length_bound
    (SourceBOTNormalizedPacketMachine.machine B)
    (SourceOriginalBOTListMapper.item_run B g originalN)
  have hi := input_length_le originalN wordCap g hg
  have ht := callback_bound_le B originalN wordCap g hg
  unfold outputEnvelope
  have hp := Nat.mul_le_mul_right
    (SourceBOTNormalizedPacketMachine.machine B).pushBound ht
  omega

theorem framed_length_le (originalN wordCap : ℕ)
    (g : EncodedETHSource.ValidFormula)
    (hg : (EncodedCNF.encode g.val).length ≤ wordCap) :
    (SourceListMachineOuterFramed.framedOutput
      (SourceOriginalBOTListMapper.itemOutput B)
      (SourceOriginalBranchPackets.sparsePacket originalN g)).length ≤
      framedEnvelope B originalN wordCap := by
  have ho := output_length_le B originalN wordCap g hg
  have hf := EncodedGraph.natField_length_upper
    (SourceOriginalBOTListMapper.itemOutput B
      (SourceOriginalBranchPackets.sparsePacket originalN g)).length
  unfold SourceListMachineOuterFramed.framedOutput framedEnvelope
  simp only [List.length_append]
  omega

theorem framed_bound_le (originalN wordCap : ℕ)
    (g : EncodedETHSource.ValidFormula)
    (hg : (EncodedCNF.encode g.val).length ≤ wordCap) :
    SourceListMachineOuterFramed.framedBound
      (SourceOriginalBOTListMapper.itemOutput B)
      (SourceOriginalBOTListMapper.itemBound B)
      (SourceOriginalBranchPackets.sparsePacket originalN g) ≤
      framedTimeEnvelope B originalN wordCap := by
  have ho := output_length_le B originalN wordCap g hg
  have ht := callback_bound_le B originalN wordCap g hg
  have hp := Nat.pow_le_pow_left
    (show (SourceOriginalBOTListMapper.itemOutput B
      (SourceOriginalBranchPackets.sparsePacket originalN g)).length+1 ≤
        outputEnvelope B originalN wordCap+1 by omega) 2
  unfold SourceListMachineOuterFramed.framedBound framedTimeEnvelope
  have hmul := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+7) hp
  omega

theorem inputList_length_le (originalN wordCap : ℕ)
    (xs : List EncodedETHSource.ValidFormula)
    (hword : ∀ g ∈ xs, (EncodedCNF.encode g.val).length ≤ wordCap) :
    (inputList originalN xs).length ≤
      3*xs.length*(inputEnvelope originalN wordCap+1)+1 := by
  exact SourceListEncoding.encode_map_length_le xs
    (SourceOriginalBranchPackets.sparsePacket originalN)
    (inputEnvelope originalN wordCap)
    (fun g hg => input_length_le originalN wordCap g (hword g hg))

theorem outputList_length_le (originalN wordCap : ℕ)
    (xs : List EncodedETHSource.ValidFormula)
    (hword : ∀ g ∈ xs, (EncodedCNF.encode g.val).length ≤ wordCap) :
    (outputList B originalN xs).length ≤
      3*xs.length*(outputEnvelope B originalN wordCap+1)+1 := by
  have h := SourceListEncoding.encode_map_length_le xs
    (SourceOriginalBOTListMapper.normalizedPacket B originalN)
    (outputEnvelope B originalN wordCap) ?_
  · exact h
  · intro g hg
    rw [← SourceOriginalBOTListMapper.itemOutput_eq B g originalN]
    exact output_length_le B originalN wordCap g (hword g hg)

/-- This requires only a uniform encoded branch-word cap. The branch count
appears as a single multiplier, outside every item polynomial. -/
theorem mapTime_le_count (originalN wordCap : ℕ)
    (xs : List EncodedETHSource.ValidFormula)
    (hword : ∀ g ∈ xs, (EncodedCNF.encode g.val).length ≤ wordCap) :
    mapTime B originalN xs ≤
      5*xs.length.bits.length+7 +
      (xs.length*itemEnvelope B originalN wordCap +
        xs.length*(4*xs.length.bits.length+7)) +
      (4*xs.length.bits.length+(natField xs.length).length+
        xs.length*framedEnvelope B originalN wordCap+9) := by
  let F := SourceListMachineOuterFramed.itemMachine
    (SourceBOTNormalizedPacketMachine.machine B)
  have hitem : ∀ x ∈ inputItems originalN xs,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput
          (SourceOriginalBOTListMapper.itemOutput B) x)
        (SourceListMachineOuterFramed.framedBound
          (SourceOriginalBOTListMapper.itemOutput B)
          (SourceOriginalBOTListMapper.itemBound B) x) ≤
      itemEnvelope B originalN wordCap := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      (inputEnvelope originalN wordCap)
      (framedEnvelope B originalN wordCap)
      (framedTimeEnvelope B originalN wordCap)
      (input_length_le originalN wordCap g (hword g hg))
      (framed_length_le B originalN wordCap g (hword g hg))
      (framed_bound_le B originalN wordCap g (hword g hg))
  have hout : ∀ x ∈ inputItems originalN xs,
      (SourceListMachineOuterFramed.framedOutput
        (SourceOriginalBOTListMapper.itemOutput B) x).length ≤
        framedEnvelope B originalN wordCap := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact framed_length_le B originalN wordCap g (hword g hg)
  have h := SourceListMachineOuter.canonicalBound_le_count F
    (inputItems originalN xs)
    (SourceListMachineOuterFramed.framedOutput
      (SourceOriginalBOTListMapper.itemOutput B))
    (SourceListMachineOuterFramed.framedBound
      (SourceOriginalBOTListMapper.itemOutput B)
      (SourceOriginalBOTListMapper.itemBound B))
    (itemEnvelope B originalN wordCap)
    (framedEnvelope B originalN wordCap) hitem hout
  simpa only [mapTime, inputItems, List.length_map, F] using h

end EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapper
