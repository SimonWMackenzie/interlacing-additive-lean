import EthInapproximability.CurrentPaper.SourceOriginalSparsificationMachine
import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerEnvelope
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Fixed physical sequential controller from original CNF to original-size branch packets. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)

abbrev SourceStack := SourceOriginalSparsificationMachine.Stack S
abbrev PacketStack := SourceOriginalListPacketizer.Stack
abbrev Stack := SourceStack S ⊕ PacketStack

def sourceSlots : SourceStack S ↪ Stack S where
  toFun := Sum.inl
  inj' := Sum.inl_injective

noncomputable def packetSlotFn (k : PacketStack) : Stack S :=
  if k = .inl SourceOriginalPacketFraming.nStack then
    .inl (SourceOriginalSparsificationMachine.outputSlots S 0)
  else if k = .inr 0 then
    .inl (SourceOriginalSparsificationMachine.outputSlots S 1)
  else .inr k

noncomputable def packetSlots : PacketStack ↪ Stack S where
  toFun := packetSlotFn S
  inj' := by
    intro a b h
    by_cases han : a = .inl SourceOriginalPacketFraming.nStack
    · by_cases hbn : b = .inl SourceOriginalPacketFraming.nStack
      · exact han.trans hbn.symm
      · by_cases hbs : b = (.inr 0 : PacketStack)
        · have hh : SourceOriginalSparsificationMachine.outputSlots S 0 =
              SourceOriginalSparsificationMachine.outputSlots S 1 := by
            have he : (Sum.inl (SourceOriginalSparsificationMachine.outputSlots S 0) : Stack S) =
                .inl (SourceOriginalSparsificationMachine.outputSlots S 1) := by
              simpa [packetSlotFn, han, hbn, hbs] using h
            exact Sum.inl.inj he
          exact False.elim ((by decide : (0 : Fin 2) ≠ 1)
            ((SourceOriginalSparsificationMachine.outputSlots S).injective hh))
        · have : False := by
            simpa [packetSlotFn, han, hbn, hbs] using h
          exact this.elim
    · by_cases has : a = (.inr 0 : PacketStack)
      · by_cases hbn : b = .inl SourceOriginalPacketFraming.nStack
        · have hh : SourceOriginalSparsificationMachine.outputSlots S 1 =
              SourceOriginalSparsificationMachine.outputSlots S 0 := by
            have he : (Sum.inl (SourceOriginalSparsificationMachine.outputSlots S 1) : Stack S) =
                .inl (SourceOriginalSparsificationMachine.outputSlots S 0) := by
              simpa [packetSlotFn, han, has, hbn] using h
            exact Sum.inl.inj he
          exact False.elim ((by decide : (1 : Fin 2) ≠ 0)
            ((SourceOriginalSparsificationMachine.outputSlots S).injective hh))
        · by_cases hbs : b = (.inr 0 : PacketStack)
          · exact has.trans hbs.symm
          · have : False := by
              simpa [packetSlotFn, han, has, hbn, hbs] using h
            exact this.elim
      · by_cases hbn : b = .inl SourceOriginalPacketFraming.nStack
        · have : False := by
            simpa [packetSlotFn, han, has, hbn] using h
          exact this.elim
        · by_cases hbs : b = (.inr 0 : PacketStack)
          · have : False := by
              simpa [packetSlotFn, han, has, hbn, hbs] using h
            exact this.elim
          · have he : (Sum.inr a : Stack S) = .inr b := by
              simpa [packetSlotFn, han, has, hbn, hbs] using h
            exact Sum.inr.inj he

def emptyBank : Stack S → List Bool := fun _ => []

abbrev SourceLabel := BitMachineRawSequence.Label
  SourceOriginalVariableCapture.Label (Fin S.machine.labelCount)
abbrev SourceControl := BitMachineRawSequence.Control
  SourceOriginalVariableCapture.Control (Fin S.machine.controlCount)

def sourceOn (l : SourceLabel S) :
    TM2.Stmt (fun _ : Stack S => Bool) (SourceLabel S) (SourceControl S) :=
  stackStmt (sourceSlots S) (SourceOriginalSparsificationMachine.program S l)

noncomputable def packetOn (l : SourceOriginalListPacketizer.Label) :
    TM2.Stmt (fun _ : Stack S => Bool)
      SourceOriginalListPacketizer.Label SourceOriginalListPacketizer.Control :=
  stackStmt (packetSlots S) (SourceOriginalListPacketizer.program l)

noncomputable def program := BitMachineRawSequence.program (sourceOn S) (packetOn S)
  (SourceOriginalListPacketizer.adminLabel .startInit)
  (none, S.machine.initial) SourceOriginalListPacketizer.initialControl

end EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer
