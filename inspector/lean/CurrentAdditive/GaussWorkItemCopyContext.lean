import CurrentAdditive.GaussStateMatrixContext
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! One fixed three-copy program prepares disposable matrix, free-index and
current-index banks for one work-item serializer, preserving every original
context bank.  The current index is an explicit prepared unary bank. -/

namespace CurrentAdditive.GaussWorkItemCopyContext

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussStateMatrixContext.Bank

def matrixSlots : Fin 3 ↪ Bank :=
  ⟨![⟨4, by omega⟩, ⟨9, by omega⟩, ⟨12, by omega⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def freeSlots : Fin 3 ↪ Bank :=
  ⟨![⟨1, by omega⟩, ⟨10, by omega⟩, ⟨12, by omega⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def indexSlots : Fin 3 ↪ Bank :=
  ⟨![⟨5, by omega⟩, ⟨11, by omega⟩, ⟨12, by omega⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

noncomputable def firstTwo :=
  BitMachineRawSequence.program
    (ExactParameterBranchInstall.copyProgram matrixSlots)
    (ExactParameterBranchInstall.copyProgram freeSlots)
    BitMachineCopy.Label.scan none none

noncomputable def program :=
  BitMachineRawSequence.program firstTwo
    (ExactParameterBranchInstall.copyProgram indexSlots)
    BitMachineCopy.Label.scan (none, none) none

theorem physical_copies (S : Bank → List Bool)
    (matrix free index : List Bool)
    (hmat : S ⟨4, by omega⟩ = matrix)
    (hfree : S ⟨1, by omega⟩ = free)
    (hindex : S ⟨5, by omega⟩ = index)
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = []) :
    ∃ t ≤ (2*matrix.length+2)+(2*free.length+2)+
        (2*index.length+2)+2,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), none), S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, ((none, none), none),
          Function.update
            (Function.update
              (Function.update S ⟨9, by omega⟩ matrix)
              ⟨10, by omega⟩ free)
              ⟨11, by omega⟩ index⟩ := by
  let S1 := Function.update S ⟨9, by omega⟩ matrix
  let S2 := Function.update S1 ⟨10, by omega⟩ free
  let S3 := Function.update S2 ⟨11, by omega⟩ index
  obtain ⟨a, ha, hrun1⟩ :=
    ExactParameterBranchInstall.copy_run matrixSlots S matrix
      (by simpa [matrixSlots] using hmat)
      (by simpa [matrixSlots] using h9)
      (by simpa [matrixSlots] using h12)
  have hfree1 : S1 (freeSlots 0) = free := by
    simp [S1, freeSlots, hfree]
  have h10_1 : S1 (freeSlots 1) = [] := by
    simp [S1, freeSlots, h10]
  have h12_1 : S1 (freeSlots 2) = [] := by
    simp [S1, freeSlots, h12]
  obtain ⟨b, hb, hrun2⟩ :=
    ExactParameterBranchInstall.copy_run freeSlots S1 free
      hfree1 h10_1 h12_1
  obtain ⟨ab, hab, hrun12⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram matrixSlots)
    (ExactParameterBranchInstall.copyProgram freeSlots)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none S S1 S2 a b
    (by simpa [matrixSlots, S1] using hrun1)
    (by simpa [freeSlots, S2] using hrun2)
  have hindex2 : S2 (indexSlots 0) = index := by
    simp [S2, S1, indexSlots, hindex]
  have h11_2 : S2 (indexSlots 1) = [] := by
    simp [S2, S1, indexSlots, h11]
  have h12_2 : S2 (indexSlots 2) = [] := by
    simp [S2, S1, indexSlots, h12]
  obtain ⟨c, hc, hrun3⟩ :=
    ExactParameterBranchInstall.copy_run indexSlots S2 index
      hindex2 h11_2 h12_2
  obtain ⟨abc, habc, hrun123⟩ := BitMachineRawSequence.runs
    firstTwo (ExactParameterBranchInstall.copyProgram indexSlots)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan (none, none) (none, none) none none
    S S2 S3 ab c
    (by simpa [firstTwo] using hrun12)
    (by simpa [indexSlots, S3] using hrun3)
  refine ⟨abc, ?_, ?_⟩
  · omega
  · simpa [program, S3, S2, S1] using hrun123

#print axioms physical_copies

end CurrentAdditive.GaussWorkItemCopyContext
