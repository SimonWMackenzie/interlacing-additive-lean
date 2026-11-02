import EthInapproximability.CurrentPaper.SourceGenericConverterMachine
import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCost
import EthInapproximability.CurrentPaper.SourceOriginalDinurListMapperCost
import EthInapproximability.CurrentPaper.SourceOriginalBOTSourceTarget

/-!
# Physical Boolean CSP-to-three-CNF packet-list map (the ledger's middle stage)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE, alphabet `D.alphabet` (arbitrary fixed positive; never 2).

The fixed generic converter machine (`ConverterMachine.machine` at
`(D.alphabet, D.arity)`) is lifted over the second field of each retained
original-`n` packet by the admitted `SourceOriginalPacketLiftMachine.liftMachine`,
and the admitted framed list controller `SourceListMachineOuterFramed.machine`
runs it once per branch. The input list is literally the admitted Dinur-stage
output `SourceOriginalDinurListMapper.outputList S D f`; the output list is
literally the admitted BOT-stage input `SourceOriginalBOTSourceTarget.booleanPacketList
S D f`. Only proved-valid Dinur outputs enter the converter.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.BooleanListMapper

open BitMachine BitMachineEncoding EncodedCommunication
open SourceGenericComposite.Converter

variable (D : EncodedETHSource.DinurReduction)

noncomputable def convMachine : BitMachine.Machine :=
  ConverterMachine.machine D.alphabet D.arity D.arity_pos

noncomputable def itemMachine : BitMachine.Machine :=
  SourceOriginalPacketLiftMachine.liftMachine (convMachine D)

/-- Per-packet clock, a fixed function of the packet length. -/
noncomputable def itemBound (x : List Bool) : Nat :=
  7 * (x.length + 2) +
    (1 + 4 * (convMachine D).pushBound) *
      (convC D.alphabet D.arity * (x.length + 1) ^ 27)

noncomputable def itemOutput (x : List Bool) : List Bool :=
  let M := itemMachine D
  (M.run (itemBound D x) (M.init x)).stk M.output

/-- The Boolean-stage packet of one branch: original `n` retained. -/
def boolPacket (originalN : Nat) (g : EncodedETHSource.ValidFormula) : List Bool :=
  SourceOriginalBranchPackets.sparsePacket originalN
    (EncodedETHSourceComposition.booleanFormula D g)

theorem item_run (originalN : Nat) (g : EncodedETHSource.ValidFormula) :
    (itemMachine D).OutputsWithin
      (SourceOriginalDinurListMapper.cspPacket D originalN g)
      (boolPacket D originalN g)
      (itemBound D (SourceOriginalDinurListMapper.cspPacket D originalN g)) := by
  have h := SourceOriginalPacketLiftCost.outputs_charged (convMachine D) originalN
    (EncodedETHSource.constraintBits (D.reduce g))
    (EncodedCNF.encode (EncodedETHSourceComposition.booleanFormula D g).val)
    _ (ConverterMachine.machine_dinur D g)
  apply BitMachine.outputsWithin_mono _ h
  have hlen : (EncodedETHSource.constraintBits (D.reduce g)).length ≤
      (SourceOriginalBranchPackets.packet originalN
        (EncodedETHSource.constraintBits (D.reduce g))).length := by
    rw [SourceOriginalBranchPackets.packet_length]
    omega
  show _ ≤ 7 * ((SourceOriginalBranchPackets.packet originalN
        (EncodedETHSource.constraintBits (D.reduce g))).length + 2) +
      (1 + 4 * (convMachine D).pushBound) *
        (convC D.alphabet D.arity * ((SourceOriginalBranchPackets.packet originalN
          (EncodedETHSource.constraintBits (D.reduce g))).length + 1) ^ 27)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 27))) _

theorem itemOutput_eq (originalN : Nat) (g : EncodedETHSource.ValidFormula) :
    itemOutput D (SourceOriginalDinurListMapper.cspPacket D originalN g) =
      boolPacket D originalN g :=
  (BitMachine.outputsWithin_at_bound _ (item_run D originalN g)).2

/-! ## The list stage over any canonical list of valid branches -/

def inputItems (originalN : Nat) (xs : List EncodedETHSource.ValidFormula) :
    List (List Bool) :=
  xs.map (SourceOriginalDinurListMapper.cspPacket D originalN)

def outputItems (originalN : Nat) (xs : List EncodedETHSource.ValidFormula) :
    List (List Bool) :=
  xs.map (boolPacket D originalN)

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine (itemMachine D)

noncomputable def listTime (originalN : Nat) (xs : List EncodedETHSource.ValidFormula) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine (itemMachine D))
    (inputItems D originalN xs)
    (SourceListMachineOuterFramed.framedOutput (itemOutput D))
    (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D))

theorem list_outputs (originalN : Nat) (xs : List EncodedETHSource.ValidFormula) :
    (machine D).OutputsWithin
      (SourceListEncoding.encode (inputItems D originalN xs))
      (SourceListEncoding.encode (outputItems D originalN xs))
      (listTime D originalN xs) := by
  have hitem : ∀ x ∈ inputItems D originalN xs,
      (itemMachine D).OutputsWithin x (itemOutput D x) (itemBound D x) := by
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    rw [itemOutput_eq D originalN g]
    exact item_run D originalN g
  have h := SourceListMachineOuterFramed.outputsWithin (itemMachine D)
    (inputItems D originalN xs) (itemOutput D) (itemBound D) hitem
  have hmap : (inputItems D originalN xs).map (itemOutput D) =
      outputItems D originalN xs := by
    simp only [inputItems, outputItems, List.map_map]
    apply List.map_congr_left
    intro g _
    exact itemOutput_eq D originalN g
  rw [hmap] at h
  simpa only [machine, listTime] using h

/-! ## The actual sparse-branch list of one original formula -/

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)

theorem input_is_dinur_output (f : EncodedETHSource.ValidFormula) :
    SourceListEncoding.encode (inputItems D f.val.variables (S.branches f)) =
      SourceOriginalDinurListMapper.outputList S D f := rfl

theorem output_is_bot_input (f : EncodedETHSource.ValidFormula) :
    SourceListEncoding.encode (outputItems D f.val.variables (S.branches f)) =
      SourceOriginalBOTSourceTarget.booleanPacketList S D f := by
  simp only [outputItems, SourceOriginalBOTSourceTarget.booleanPacketList,
    SourceOriginalBOTCanonicalListMapper.inputList,
    SourceOriginalBOTCanonicalListMapper.inputItems,
    EncodedETHSourceComposition.booleanBranches, List.map_map]
  rfl

noncomputable def mapTime (f : EncodedETHSource.ValidFormula) : Nat :=
  listTime D f.val.variables (S.branches f)

/-- Dinur-stage packet list to BOT-stage packet list, one fixed machine. -/
theorem mapped_outputs (f : EncodedETHSource.ValidFormula) :
    (machine D).OutputsWithin
      (SourceOriginalDinurListMapper.outputList S D f)
      (SourceOriginalBOTSourceTarget.booleanPacketList S D f)
      (mapTime D S f) := by
  rw [← input_is_dinur_output, ← output_is_bot_input]
  exact list_outputs D f.val.variables (S.branches f)

#print axioms item_run
#print axioms itemOutput_eq
#print axioms list_outputs
#print axioms output_is_bot_input
#print axioms mapped_outputs

end EthInapproximability.CurrentPaper.SourceGenericComposite.BooleanListMapper
