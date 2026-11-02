import CurrentAdditive.RationalSubtractSpec
import CurrentAdditive.RationalNestedFlatClosure
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A literal fixed suffix writer from a twelve-field packet to a 32-field packet. -/

namespace EthInapproximability.CurrentPaper.RationalFlatPad32

set_option maxRecDepth 4096

open Turing Turing.TM2.Stmt BitMachineEncoding

def padProgram : Fin 21 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 21) Unit :=
  fun i => if h : i.val < 20 then
    push 1 (fun _ => false) (goto (fun _ => ⟨i.val + 1, by omega⟩))
  else halt

abbrev Label := BitMachineRawSequence.Label (Fin 21) BitMachineCopy.Label
abbrev Control := BitMachineRawSequence.Control Unit (Option Bool)

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control :=
  BitMachineRawSequence.program padProgram BitMachineCopy.program
    .scan () none

def start : Label := BitMachineRawSequence.leftLabel 0
def initial : Control := ((), none)

def bank (source output saved : List Bool) : Fin 3 → List Bool :=
  BitMachineCopy.stackContents source output saved

private theorem pad_run (input : List Bool) :
    ((advance padProgram)^[21])
      (⟨some 0, (), bank input [] []⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 21) Unit) =
      ⟨none, (), bank input (List.replicate 20 false) []⟩ := by
  simp [Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, padProgram, bank, BitMachineCopy.stackContents]
  funext k
  fin_cases k <;> rfl

theorem local_run (input : List Bool) :
    ∃ t ≤ 21 + (2*input.length+2) + 1,
      ((advance program)^[t])
        (⟨some start, initial, bank input [] []⟩ :
          TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) =
      ⟨none, initial, bank input
        (input ++ List.replicate 20 false) []⟩ := by
  have ha := pad_run input
  have hb : ((advance BitMachineCopy.program)^[2*input.length+2])
      (⟨some .scan, none, bank input (List.replicate 20 false) []⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, bank input (input ++ List.replicate 20 false) []⟩ := by
    simpa [BitMachineCopy.run, BitMachineCopy.cfg, bank] using
      BitMachineCopy.run_correct none input (List.replicate 20 false)
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs padProgram
    BitMachineCopy.program 0 .scan () () none none
    (bank input [] []) (bank input (List.replicate 20 false) [])
    (bank input (input ++ List.replicate 20 false) [])
    21 (2*input.length+2) ha hb
  exact ⟨t, ht, by simpa only [program, start, initial] using hr⟩

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 1 start initial program

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (input ++ List.replicate 20 false)
      (2*input.length+24) := by
  obtain ⟨t,ht,hr⟩ := local_run input
  have hi : rawInit (0 : Fin 3) start initial input =
      (⟨some start, initial, bank input [] []⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) := by
    unfold rawInit bank BitMachineCopy.stackContents
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 3) 1 start initial program
    input (input ++ List.replicate 20 false) t _ (by omega)
  · rw [hi]
    rw [hr]
  · rw [hi]
    rw [hr]
    rfl

theorem polytime : BitMachine.Polytime
    (fun input : List Bool => input ++ List.replicate 20 false) := by
  refine ⟨machine, 24, 1, ?_⟩
  intro input
  apply BitMachine.outputsWithin_mono machine (outputs input)
  simp only [pow_one]
  omega

def extendedFlatBank (x y : CurrentAdditive.CodeDCodec.RawRat) :
    BitMachineBankCodec.Bank 32 := fun i =>
  if h : i.val < 12 then
    RationalProductNestedFlat.flatBank x y ⟨i.val, h⟩
  else []

theorem extendedFlat_bytes (x y : CurrentAdditive.CodeDCodec.RawRat) :
    BitMachineBankCodec.encode (extendedFlatBank x y) =
      RationalProductNestedFlat.flatBytes x y ++ List.replicate 20 false := by
  simp [BitMachineBankCodec.encode, BitMachineBankCodec.encodeFrom,
    extendedFlatBank, RationalProductNestedFlat.flatBytes,
    EncodedCommunication.field, List.replicate, List.append_assoc]

theorem nested_pair_to_extended (x y : CurrentAdditive.CodeDCodec.RawRat) :
    (BitMachineComposition.composition
      RationalProductNestedFlat.machine machine).OutputsWithin
        (CurrentAdditive.CodeDPairProductTargetV2.pairBytes x y)
        (BitMachineBankCodec.encode (extendedFlatBank x y))
        (40*((CurrentAdditive.CodeDPairProductTargetV2.pairBytes x y).length+1) +
          2*(RationalProductNestedFlat.flatBytes x y).length+2 +
          (2*(RationalProductNestedFlat.flatBytes x y).length+24)) := by
  rw [extendedFlat_bytes]
  exact BitMachineComposition.composition_outputsWithin
    RationalProductNestedFlat.machine machine
    (RationalNestedFlatClosure.pair_outputs x y)
    (outputs (RationalProductNestedFlat.flatBytes x y))

end EthInapproximability.CurrentPaper.RationalFlatPad32
