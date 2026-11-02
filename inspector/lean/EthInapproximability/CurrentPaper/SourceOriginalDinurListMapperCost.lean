import EthInapproximability.CurrentPaper.SourceOriginalDinurListMapper
import EthInapproximability.CurrentPaper.SourceListMachineWork

/-! Original-n and per-branch cost of the physical Dinur packet-list map. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalDinurListMapper

open BitMachine BitMachineEncoding EncodedCommunication

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)
  (D : EncodedETHSource.DinurReduction)

def inputEnvelope (n : ℕ) : ℕ :=
  2*(n+(8*S.density+3)*n*(n.size+1))+2

noncomputable def callbackEnvelope (n : ℕ) : ℕ :=
  coefficient D*(inputEnvelope S n+3)^exponent D

noncomputable def outputEnvelope (n : ℕ) : ℕ :=
  inputEnvelope S n + callbackEnvelope S D n *
    (SourceDinurPacketMachine.machine D).pushBound

noncomputable def framedEnvelope (n : ℕ) : ℕ :=
  3*outputEnvelope S D n+1

noncomputable def framedTimeEnvelope (n : ℕ) : ℕ :=
  callbackEnvelope S D n + 2*outputEnvelope S D n+2 +
    (UnaryBinaryEncoding.coefficient+7)*(outputEnvelope S D n+1)^2

noncomputable def itemEnvelope (n : ℕ) : ℕ :=
  let F := SourceListMachineOuterFramed.itemMachine
    (SourceDinurPacketMachine.machine D)
  let L := inputEnvelope S n
  let R := framedEnvelope S D n
  let T := framedTimeEnvelope S D n
  20*(L+1)*(L+1)+T+4*L+R+
    F.stackCount*(L+T*F.pushBound+1)+9

theorem input_length_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) (g : EncodedETHSource.ValidFormula)
    (hg : g ∈ S.branches f) :
    (SourceOriginalBranchPackets.sparsePacket f.val.variables g).length ≤
      inputEnvelope S f.val.variables := by
  exact SourceOriginalBranchPackets.sparsePacket_length S f hn g hg

theorem callback_bound_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) (g : EncodedETHSource.ValidFormula)
    (hg : g ∈ S.branches f) :
    itemBound D (SourceOriginalBranchPackets.sparsePacket f.val.variables g) ≤
      callbackEnvelope S D f.val.variables := by
  have hp := Nat.pow_le_pow_left (show
    (SourceOriginalBranchPackets.sparsePacket f.val.variables g).length+3 ≤
      inputEnvelope S f.val.variables+3 by
        have hi := input_length_le S f hn g hg
        omega) (exponent D)
  unfold itemBound callbackEnvelope
  exact Nat.mul_le_mul_left _ hp

theorem output_length_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) (g : EncodedETHSource.ValidFormula)
    (hg : g ∈ S.branches f) :
    (itemOutput D (SourceOriginalBranchPackets.sparsePacket f.val.variables g)).length ≤
      outputEnvelope S D f.val.variables := by
  rw [itemOutput_eq D g f.val.variables]
  have ho := BitMachine.output_length_bound
    (SourceDinurPacketMachine.machine D) (item_run D g f.val.variables)
  have hi := input_length_le S f hn g hg
  have ht := callback_bound_le S D f hn g hg
  unfold outputEnvelope
  have hp := Nat.mul_le_mul_right
    (SourceDinurPacketMachine.machine D).pushBound ht
  omega

theorem framed_length_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) (g : EncodedETHSource.ValidFormula)
    (hg : g ∈ S.branches f) :
    (SourceListMachineOuterFramed.framedOutput (itemOutput D)
      (SourceOriginalBranchPackets.sparsePacket f.val.variables g)).length ≤
      framedEnvelope S D f.val.variables := by
  have ho := output_length_le S D f hn g hg
  have hf := EncodedGraph.natField_length_upper
    (itemOutput D (SourceOriginalBranchPackets.sparsePacket f.val.variables g)).length
  unfold SourceListMachineOuterFramed.framedOutput framedEnvelope
  simp only [List.length_append]
  omega

theorem framed_bound_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) (g : EncodedETHSource.ValidFormula)
    (hg : g ∈ S.branches f) :
    SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D)
      (SourceOriginalBranchPackets.sparsePacket f.val.variables g) ≤
      framedTimeEnvelope S D f.val.variables := by
  have ho := output_length_le S D f hn g hg
  have ht := callback_bound_le S D f hn g hg
  have hp := Nat.pow_le_pow_left
    (show (itemOutput D
      (SourceOriginalBranchPackets.sparsePacket f.val.variables g)).length+1 ≤
        outputEnvelope S D f.val.variables+1 by omega) 2
  unfold SourceListMachineOuterFramed.framedBound framedTimeEnvelope
  have hmul := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+7) hp
  omega

theorem outputList_length_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) :
    (outputList S D f).length ≤
      3*(S.branches f).length*(outputEnvelope S D f.val.variables+1)+1 := by
  have h := SourceListEncoding.encode_map_length_le (S.branches f)
    (cspPacket D f.val.variables)
    (outputEnvelope S D f.val.variables) ?_
  · exact h
  · intro g hg
    rw [← itemOutput_eq D g f.val.variables]
    exact output_length_le S D f hn g hg

theorem mapTime_le_count (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) :
    mapTime S D f ≤
      5*(S.branches f).length.bits.length+7 +
      ((S.branches f).length*itemEnvelope S D f.val.variables +
        (S.branches f).length*(4*(S.branches f).length.bits.length+7)) +
      (4*(S.branches f).length.bits.length+
        (natField (S.branches f).length).length+
        (S.branches f).length*framedEnvelope S D f.val.variables+9) := by
  let F := SourceListMachineOuterFramed.itemMachine
    (SourceDinurPacketMachine.machine D)
  have hitem : ∀ x ∈ inputItems S f,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput (itemOutput D) x)
        (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D) x) ≤
      itemEnvelope S D f.val.variables := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      (inputEnvelope S f.val.variables)
      (framedEnvelope S D f.val.variables)
      (framedTimeEnvelope S D f.val.variables)
      (input_length_le S f hn g hg)
      (framed_length_le S D f hn g hg)
      (framed_bound_le S D f hn g hg)
  have hout : ∀ x ∈ inputItems S f,
      (SourceListMachineOuterFramed.framedOutput (itemOutput D) x).length ≤
        framedEnvelope S D f.val.variables := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact framed_length_le S D f hn g hg
  have h := SourceListMachineOuter.canonicalBound_le_count F
    (inputItems S f)
    (SourceListMachineOuterFramed.framedOutput (itemOutput D))
    (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D))
    (itemEnvelope S D f.val.variables)
    (framedEnvelope S D f.val.variables) hitem hout
  simpa only [mapTime, inputItems, List.length_map, F] using h

end EthInapproximability.CurrentPaper.SourceOriginalDinurListMapper
