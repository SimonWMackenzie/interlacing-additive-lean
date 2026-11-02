import EthInapproximability.CurrentPaper.SamplerWriterPayloadFrame
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Physical reset between the first and second sampler calls

The first call leaves its selected modulus and unary row length in spare
writer cells 36 and 47. This fixed controller physically clears those two
cells. The second raw degree word and second unary row length are retained in
two additional input stacks, which are untouched by the reset. Subsequent
source-preserving copies into cells 36/47 are a separate stage.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterSecondInit

open Turing BitMachineEncoding

abbrev Stack := SamplerWriterPayloadFrame.WriterStack ⊕ Fin 2
abbrev Label := Fin 4
abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def degreeCell : Stack := .inl SamplerWriterPayloadFrame.modulusCell
def lengthCell : Stack := .inl SamplerWriterPayloadFrame.lengthCell
def nextDegree : Stack := .inr 0
def nextLength : Stack := .inr 1

def clearing : Fin 2 ↪ Stack :=
  ⟨![degreeCell, lengthCell], by decide⟩

def labels : Fin 3 → Label := ![0, 1, 2]

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  match l with
  | 0 => BitMachineClearBank.clearStep degreeCell 0 1
  | 1 => BitMachineClearBank.clearStep lengthCell 1 2
  | 2 => BitMachineClearBank.finishStep id 3
  | _ => .halt

theorem run_clear (S : Stack → List Bool) :
    ((advance program)^[(S degreeCell).length + (S lengthCell).length + 3])
      (⟨some 0, ((), none), S⟩ : Config) =
    ⟨some 3, ((), none), BitMachineClearBank.cleared clearing S⟩ := by
  have h := BitMachineClearBank.clear_bank_run program id 3 2 clearing
    clearing.injective labels (by intro i; fin_cases i <;> rfl)
    (by rfl) () S
  simpa [Fin.sum_univ_two, clearing, labels] using h

theorem run_halt (S : Stack → List Bool) :
    ((advance program)^[(S degreeCell).length + (S lengthCell).length + 4])
      (⟨some 0, ((), none), S⟩ : Config) =
    ⟨none, ((), none), BitMachineClearBank.cleared clearing S⟩ := by
  rw [show (S degreeCell).length + (S lengthCell).length + 4 =
      1 + ((S degreeCell).length + (S lengthCell).length + 3) by omega,
    Function.iterate_add_apply, run_clear]
  rfl

theorem cleared_degree (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearing S degreeCell = [] := by
  exact BitMachineClearBank.cleared_bank clearing S 0

theorem cleared_length (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearing S lengthCell = [] := by
  exact BitMachineClearBank.cleared_bank clearing S 1

theorem retained_next_degree (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearing S nextDegree = S nextDegree := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> decide

theorem retained_next_length (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearing S nextLength = S nextLength := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> decide

theorem retained_first (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearing S (.inl SamplerWriterPayloadFrame.firstCell) =
      S (.inl SamplerWriterPayloadFrame.firstCell) := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> decide

theorem retained_source (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearing S (.inl SamplerWriterPayloadFrame.sourceCell) =
      S (.inl SamplerWriterPayloadFrame.sourceCell) := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> decide

end EthInapproximability.CurrentPaper.SamplerWriterSecondInit
