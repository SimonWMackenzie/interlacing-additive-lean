import EthInapproximability.CurrentPaper.SourceOriginalBOTListMapper

/-! Physical BOT normalization over any canonical list of valid CNF packets. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapper

variable {k : ℕ} (B : EncodedETHSource.BOTReduction k)

def inputItems (originalN : ℕ)
    (xs : List EncodedETHSource.ValidFormula) : List (List Bool) :=
  xs.map (SourceOriginalBranchPackets.sparsePacket originalN)

def inputList (originalN : ℕ)
    (xs : List EncodedETHSource.ValidFormula) : List Bool :=
  SourceListEncoding.encode (inputItems originalN xs)

def outputItems (originalN : ℕ)
    (xs : List EncodedETHSource.ValidFormula) : List (List Bool) :=
  xs.map (SourceOriginalBOTListMapper.normalizedPacket B originalN)

def outputList (originalN : ℕ)
    (xs : List EncodedETHSource.ValidFormula) : List Bool :=
  SourceListEncoding.encode (outputItems B originalN xs)

noncomputable def machine : BitMachine.Machine :=
  SourceOriginalBOTListMapper.machine B

noncomputable def mapTime (originalN : ℕ)
    (xs : List EncodedETHSource.ValidFormula) : ℕ :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine (SourceBOTNormalizedPacketMachine.machine B))
    (inputItems originalN xs)
    (SourceListMachineOuterFramed.framedOutput (SourceOriginalBOTListMapper.itemOutput B))
    (SourceListMachineOuterFramed.framedBound
      (SourceOriginalBOTListMapper.itemOutput B)
      (SourceOriginalBOTListMapper.itemBound B))

/-- The actual fixed controller maps each packet with the cited BOT machine.
The clock is the controller's literal sum of individual machine and framing
costs, with no polynomial applied to the number of packets. -/
theorem mapped_outputs (originalN : ℕ)
    (xs : List EncodedETHSource.ValidFormula) :
    (machine B).OutputsWithin (inputList originalN xs)
      (outputList B originalN xs) (mapTime B originalN xs) := by
  have hitem : ∀ x ∈ inputItems originalN xs,
      (SourceBOTNormalizedPacketMachine.machine B).OutputsWithin x
        (SourceOriginalBOTListMapper.itemOutput B x)
        (SourceOriginalBOTListMapper.itemBound B x) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    rw [SourceOriginalBOTListMapper.itemOutput_eq B g originalN]
    exact SourceOriginalBOTListMapper.item_run B g originalN
  have h := SourceListMachineOuterFramed.outputsWithin
    (SourceBOTNormalizedPacketMachine.machine B)
    (inputItems originalN xs)
    (SourceOriginalBOTListMapper.itemOutput B)
    (SourceOriginalBOTListMapper.itemBound B) hitem
  have hmap : (inputItems originalN xs).map
      (SourceOriginalBOTListMapper.itemOutput B) = outputItems B originalN xs := by
    simp only [inputItems, outputItems, List.map_map]
    apply List.map_congr_left
    intro g hg
    exact SourceOriginalBOTListMapper.itemOutput_eq B g originalN
  rw [hmap] at h
  simpa only [machine, inputList, outputList, mapTime] using h

end EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapper
