import EthInapproximability.CurrentPaper.SourceDinurPacketMachine
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed
import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets

/-! Physical canonical sparse-CNF packet list to original-n Dinur CSP packets. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalDinurListMapper

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)
  (D : EncodedETHSource.DinurReduction)

noncomputable def coefficient : ℕ :=
  (SourceDinurPacketMachine.machine_outputs D).choose

noncomputable def exponent : ℕ :=
  (SourceDinurPacketMachine.machine_outputs D).choose_spec.choose

noncomputable def itemBound (word : List Bool) : ℕ :=
  coefficient D * (word.length+3)^exponent D

noncomputable def itemOutput (word : List Bool) : List Bool :=
  let M := SourceDinurPacketMachine.machine D
  (M.run (itemBound D word) (M.init word)).stk M.output

def inputItems (f : EncodedETHSource.ValidFormula) : List (List Bool) :=
  (S.branches f).map (SourceOriginalBranchPackets.sparsePacket f.val.variables)

def cspPacket (originalN : ℕ) (g : EncodedETHSource.ValidFormula) : List Bool :=
  SourceOriginalBranchPackets.packet originalN
    (EncodedETHSource.constraintBits (D.reduce g))

def outputItems (f : EncodedETHSource.ValidFormula) : List (List Bool) :=
  (S.branches f).map (cspPacket D f.val.variables)

def outputList (f : EncodedETHSource.ValidFormula) : List Bool :=
  SourceListEncoding.encode (outputItems S D f)

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine (SourceDinurPacketMachine.machine D)

noncomputable def mapTime (f : EncodedETHSource.ValidFormula) : ℕ :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine (SourceDinurPacketMachine.machine D))
    (inputItems S f)
    (SourceListMachineOuterFramed.framedOutput (itemOutput D))
    (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D))

theorem item_run (g : EncodedETHSource.ValidFormula) (originalN : ℕ) :
    (SourceDinurPacketMachine.machine D).OutputsWithin
      (SourceOriginalBranchPackets.sparsePacket originalN g)
      (cspPacket D originalN g)
      (itemBound D (SourceOriginalBranchPackets.sparsePacket originalN g)) := by
  have h := (SourceDinurPacketMachine.machine_outputs D).choose_spec.choose_spec
    g originalN
  simpa only [SourceOriginalBranchPackets.sparsePacket,
    cspPacket, itemBound, coefficient, exponent] using h

theorem itemOutput_eq (g : EncodedETHSource.ValidFormula) (originalN : ℕ) :
    itemOutput D (SourceOriginalBranchPackets.sparsePacket originalN g) =
      cspPacket D originalN g := by
  exact (BitMachine.outputsWithin_at_bound _ (item_run D g originalN)).2

theorem mapped_outputs (f : EncodedETHSource.ValidFormula) :
    (machine D).OutputsWithin
      (SourceOriginalBranchPackets.packetList S f)
      (outputList S D f) (mapTime S D f) := by
  have hitem : ∀ x ∈ inputItems S f,
      (SourceDinurPacketMachine.machine D).OutputsWithin x
        (itemOutput D x) (itemBound D x) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    rw [itemOutput_eq D g f.val.variables]
    exact item_run D g f.val.variables
  have h := SourceListMachineOuterFramed.outputsWithin
    (SourceDinurPacketMachine.machine D)
    (inputItems S f) (itemOutput D) (itemBound D) hitem
  have hmap : (inputItems S f).map (itemOutput D) = outputItems S D f := by
    simp only [inputItems, outputItems, List.map_map]
    apply List.map_congr_left
    intro g hg
    exact itemOutput_eq D g f.val.variables
  rw [hmap] at h
  simpa only [machine, SourceOriginalBranchPackets.packetList,
    inputItems, outputList, mapTime] using h

end EthInapproximability.CurrentPaper.SourceOriginalDinurListMapper
