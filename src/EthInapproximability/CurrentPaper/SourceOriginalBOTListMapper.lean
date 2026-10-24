import EthInapproximability.CurrentPaper.SourceBOTNormalizedPacketMachine
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! Auxiliary direct sparse-CNF packet list to original-n BOT graph packets.
The final source route first requires Dinur and CSP-to-Boolean conversion. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalBOTListMapper

variable {η : ℚ} {k : ℕ}
  (B : EncodedETHSource.BOTReduction k)

noncomputable def coefficient : ℕ :=
  (SourceBOTNormalizedPacketMachine.machine_outputs B).choose

noncomputable def exponent : ℕ :=
  (SourceBOTNormalizedPacketMachine.machine_outputs B).choose_spec.choose

noncomputable def itemBound (word : List Bool) : ℕ :=
  coefficient B * (word.length + 3) ^ exponent B

noncomputable def itemOutput (word : List Bool) : List Bool :=
  let M := SourceBOTNormalizedPacketMachine.machine B
  (M.run (itemBound B word) (M.init word)).stk M.output

def inputItems (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : List (List Bool) :=
  (S.branches f).map (SourceOriginalBranchPackets.sparsePacket f.val.variables)

def normalizedPacket (n : ℕ) (g : EncodedETHSource.ValidFormula) : List Bool :=
  SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (B.output g.val g.property n))

def outputItems (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : List (List Bool) :=
  (S.branches f).map (normalizedPacket B f.val.variables)

def outputList (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : List Bool :=
  SourceListEncoding.encode (outputItems B S f)

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine (SourceBOTNormalizedPacketMachine.machine B)

noncomputable def mapTime (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : ℕ :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine (SourceBOTNormalizedPacketMachine.machine B))
    (inputItems S f)
    (SourceListMachineOuterFramed.framedOutput (itemOutput B))
    (SourceListMachineOuterFramed.framedBound (itemOutput B) (itemBound B))

theorem item_run (g : EncodedETHSource.ValidFormula) (n : ℕ) :
    (SourceBOTNormalizedPacketMachine.machine B).OutputsWithin
      (SourceOriginalBranchPackets.sparsePacket n g)
      (normalizedPacket B n g)
      (itemBound B (SourceOriginalBranchPackets.sparsePacket n g)) := by
  have h := (SourceBOTNormalizedPacketMachine.machine_outputs B).choose_spec.choose_spec
    g.val g.property n
  simpa only [SourceOriginalBranchPackets.sparsePacket,
    normalizedPacket, itemBound, coefficient, exponent] using h

theorem itemOutput_eq (g : EncodedETHSource.ValidFormula) (n : ℕ) :
    itemOutput B (SourceOriginalBranchPackets.sparsePacket n g) =
      normalizedPacket B n g := by
  exact (BitMachine.outputsWithin_at_bound _ (item_run B g n)).2

theorem mapped_outputs (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) :
    (machine B).OutputsWithin
      (SourceOriginalBranchPackets.packetList S f)
      (outputList B S f) (mapTime B S f) := by
  have hitem : ∀ x ∈ inputItems S f,
      (SourceBOTNormalizedPacketMachine.machine B).OutputsWithin x
        (itemOutput B x) (itemBound B x) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    rw [itemOutput_eq B g f.val.variables]
    exact item_run B g f.val.variables
  have h := SourceListMachineOuterFramed.outputsWithin
    (SourceBOTNormalizedPacketMachine.machine B)
    (inputItems S f) (itemOutput B) (itemBound B) hitem
  have hmap : (inputItems S f).map (itemOutput B) = outputItems B S f := by
    simp only [inputItems, outputItems, List.map_map]
    apply List.map_congr_left
    intro g hg
    exact itemOutput_eq B g f.val.variables
  rw [hmap] at h
  simpa only [machine, SourceOriginalBranchPackets.packetList,
    inputItems, outputList, mapTime] using h

end EthInapproximability.CurrentPaper.SourceOriginalBOTListMapper
