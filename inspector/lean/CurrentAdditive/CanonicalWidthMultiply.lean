import CurrentAdditive.CanonicalFieldBankBridge
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary

/-! A physical three-stage unary program computes the field-word width
`H*(K+1)` from unary H and K, preserving both inputs. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalWidthMultiply

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def copyPlace : Fin 3 ↪ Fin 8 := ⟨![1, 2, 4], by decide⟩
def mulPlace : Fin 6 ↪ Fin 8 := ⟨![0, 2, 5, 6, 7, 3], by decide⟩

def mulProgram := MatrixStage4ScalarPreparationOps.multiplyProgram mulPlace
def appendAndMul := BitMachineRawSequence.program
  (SourceClauseFixedUnary.program (2 : Fin 8) 1) mulProgram
  MatrixAddressMachine.Label.outer () false
def widthProgram := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.copyProgram copyPlace) appendAndMul
  (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 1))
  (none : Option Bool) ((), false)

def initial (H K : ℕ) : Fin 8 → List Bool :=
  (![List.replicate H true, List.replicate K true, [], [], [], [], [], []] :
    Fin 8 → List Bool)

theorem physical_width (H K : ℕ) :
    ∃ steps ≤ (2 * K + 2) + 2 +
        MatrixAddressMachine.exactTime H (K + 1) 0 + 2,
      ((advance widthProgram)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ((), false)), initial H K⟩ :
          TM2.Cfg (fun _ : Fin 8 => Bool) _ _) =
        ⟨none, (none, ((), false)),
          Function.update (Function.update (initial H K) 2
            (List.replicate (K + 1) true)) 3
            (List.replicate (H * (K + 1)) true)⟩ := by
  let S := initial H K
  have hcopy := MatrixStage4ScalarPreparationOps.copy_run copyPlace S (by rfl)
  let S1 := Function.update S 2 (List.replicate K true)
  have hcopy' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram copyPlace))^[2*K+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Fin 8 => Bool) _ _) =
      ⟨none, none, S1⟩ := by
    simpa [copyPlace, S, S1, initial] using hcopy
  let S2 := Function.update S1 2 (List.replicate (K+1) true)
  have hpush := SourceClauseFixedUnary.run_from (2 : Fin 8) S1
    (0 : SourceClauseFixedUnary.Label 1) 1 (by decide)
    (List.replicate K true)
  have hpush' : ((advance (SourceClauseFixedUnary.program (2 : Fin 8) 1))^[2])
      (⟨some (0 : SourceClauseFixedUnary.Label 1), (), S1⟩ :
        TM2.Cfg (fun _ : Fin 8 => Bool) _ _) =
      ⟨none, (), S2⟩ := by
    simpa [SourceClauseFixedUnary.state, S1, S2, S, initial, List.replicate_succ]
      using hpush
  have hmul := MatrixStage4ScalarPreparationOps.multiply_run mulPlace S2 H (K+1)
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
  have hmul' : ((advance mulProgram)^[MatrixAddressMachine.exactTime H (K+1) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, S2⟩ :
        TM2.Cfg (fun _ : Fin 8 => Bool) _ _) =
      ⟨none, false, Function.update S2 3
        (List.replicate (H*(K+1)) true)⟩ := by
    simpa [mulProgram, mulPlace, S2, S1, S, initial] using hmul
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (2 : Fin 8) 1) mulProgram
    (0 : SourceClauseFixedUnary.Label 1) MatrixAddressMachine.Label.outer
    () () false false S1 S2 _ 2
    (MatrixAddressMachine.exactTime H (K+1) 0) hpush' hmul'
  obtain ⟨steps, hsteps, hfinal⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram copyPlace) appendAndMul
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 1))
    none none ((), false) ((), false) S S1 _ (2*K+2) u hcopy' hrun
  exact ⟨steps, by omega, by simpa [S2, S1, S] using hfinal⟩

#print axioms physical_width

end CurrentAdditive.FiniteFieldConstructor.CanonicalWidthMultiply
