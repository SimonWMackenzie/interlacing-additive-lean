import Paper2.CodeRowsLiteralPrefix
import EthInapproximability.CurrentPaper.BitMachineCopy

/-! A fixed three-arm serializer. It copies source words third, second,
first onto the output stack, then physically prefixes the fixed branch tag
and absolute unary fields. Sources are restored and scratch is cleared. -/

namespace Paper2.CodeRowsBranchAssembly

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorSerialization
open Paper2.GeneratorCode
open Paper2.CodeRowsArmA
open Paper2.CodeRowsLiteralPrefix

def wordIndex (source : FinalBank)
    (hout : source ≠ 29) (hscratch : source ≠ 30) :
    Fin 3 ↪ FinalBank where
  toFun i := ![source,29,30] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all

def wordCopyProgram (source : FinalBank)
    (hout : source ≠ 29) (hscratch : source ≠ 30) :
    BitMachineCopy.Label →
    TM2.Stmt (fun _ : FinalBank => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt
    (wordIndex source hout hscratch) (BitMachineCopy.program l)

theorem word_initial_bank (source : FinalBank)
    (hout : source ≠ 29) (hscratch : source ≠ 30)
    (B : FinalBank → List Bool) (hblank : B 30 = []) :
    BitMachineStackEmbedding.bank
      (wordIndex source hout hscratch) B
      (BitMachineCopy.cfg (some .scan) none
        (B source) (B 29) []).stk = B := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · rfl
  · rfl
  · exact hblank.symm

theorem word_result_bank (source : FinalBank)
    (hout : source ≠ 29) (hscratch : source ≠ 30)
    (B : FinalBank → List Bool) (hblank : B 30 = []) :
    BitMachineStackEmbedding.bank
      (wordIndex source hout hscratch) B
      (BitMachineCopy.cfg none none
        (B source) (B source ++ B 29) []).stk =
    Function.update B 29 (B source ++ B 29) := by
  have hstk :
      (BitMachineCopy.cfg none none
        (B source) (B source ++ B 29) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (B source) (B 29) []).stk
        (1 : Fin 3) (B source ++ B 29) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    word_initial_bank source hout hscratch B hblank]
  rfl

theorem word_copy_run (source : FinalBank)
    (hout : source ≠ 29) (hscratch : source ≠ 30)
    (B : FinalBank → List Bool) (hblank : B 30 = []) :
    ((advance (wordCopyProgram source hout hscratch))^[2*(B source).length+2])
      (⟨some .scan, none, B⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update B 29 (B source ++ B 29)⟩ := by
  have h := BitMachineStackRun.run
    (wordIndex source hout hscratch) B BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none
      (B source) (B 29) []) (2*(B source).length+2)
  rw [← BitMachineCopy.run,
    BitMachineCopy.run_correct none (B source) (B 29)] at h
  simpa only [wordCopyProgram, BitMachineStackEmbedding.stackCfg,
    word_initial_bank source hout hscratch B hblank,
    word_result_bank source hout hscratch B hblank] using h

def copyThirdProgram := wordCopyProgram 24 (by decide) (by decide)
def copySecondProgram := wordCopyProgram 23 (by decide) (by decide)
def copyFirstProgram := wordCopyProgram 22 (by decide) (by decide)

def afterThird (B : FinalBank → List Bool) : FinalBank → List Bool :=
  Function.update B 29 (B 24 ++ B 29)

def afterSecond (B : FinalBank → List Bool) : FinalBank → List Bool :=
  Function.update B 29 (B 23 ++ B 24 ++ B 29)

def afterFirst (B : FinalBank → List Bool) : FinalBank → List Bool :=
  Function.update B 29 (B 22 ++ B 23 ++ B 24 ++ B 29)

theorem third_run (B : FinalBank → List Bool) (hblank : B 30 = []) :
    ((advance copyThirdProgram)^[2*(B 24).length+2])
      (⟨some .scan, none, B⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterThird B⟩ :=
  word_copy_run 24 (by decide) (by decide) B hblank

theorem second_run (B : FinalBank → List Bool) (hblank : B 30 = []) :
    ((advance copySecondProgram)^[2*(B 23).length+2])
      (⟨some .scan, none, afterThird B⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterSecond B⟩ := by
  have hblank' : afterThird B 30 = [] := by
    simp [afterThird, hblank]
  have h := word_copy_run 23 (by decide) (by decide)
    (afterThird B) hblank'
  simpa [copySecondProgram, afterThird, afterSecond,
    Function.update_of_ne, List.append_assoc] using h

theorem first_run (B : FinalBank → List Bool) (hblank : B 30 = []) :
    ((advance copyFirstProgram)^[2*(B 22).length+2])
      (⟨some .scan, none, afterSecond B⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterFirst B⟩ := by
  have hblank' : afterSecond B 30 = [] := by
    simp [afterSecond, hblank]
  have h := word_copy_run 22 (by decide) (by decide)
    (afterSecond B) hblank'
  simpa [copyFirstProgram, afterSecond, afterFirst,
    Function.update_of_ne, List.append_assoc] using h

def threeCopiesProgram :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program copyThirdProgram copySecondProgram
      BitMachineCopy.Label.scan none none)
    copyFirstProgram BitMachineCopy.Label.scan
    ((none,none) : BitMachineRawSequence.Control (Option Bool) (Option Bool))
    none

theorem three_copies_run (B : FinalBank → List Bool)
    (hblank : B 30 = []) :
    ∃ t ≤ 2*((B 24).length+(B 23).length+(B 22).length)+8,
      ((advance threeCopiesProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none), B⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none, ((none,none),none), afterFirst B⟩ := by
  obtain ⟨tab,htab,hab⟩ := BitMachineRawSequence.runs
    copyThirdProgram copySecondProgram BitMachineCopy.Label.scan
    BitMachineCopy.Label.scan none none none none
    B (afterThird B) (afterSecond B)
    (2*(B 24).length+2) (2*(B 23).length+2)
    (third_run B hblank) (second_run B hblank)
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program copyThirdProgram copySecondProgram
      BitMachineCopy.Label.scan none none)
    copyFirstProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan
    (none,none) (none,none) none none
    B (afterSecond B) (afterFirst B) tab (2*(B 22).length+2)
    hab (first_run B hblank)
  exact ⟨t, by omega, hr⟩

def branchAssembleProgram :=
  BitMachineRawSequence.program threeCopiesProgram
    CodeRowsLiteralPrefix.program
    CodeRowsLiteralPrefix.Label.write
    (((none,none),none) :
      BitMachineRawSequence.Control
        (BitMachineRawSequence.Control (Option Bool) (Option Bool))
        (Option Bool)) ()

theorem branch_assemble_run (B : FinalBank → List Bool)
    (hblank : B 30 = []) :
    ∃ t ≤ 2*((B 24).length+(B 23).length+(B 22).length)+11,
      ((advance branchAssembleProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none,none),none),()), B⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none, (((none,none),none),()),
          Function.update B 29
            (branchPrefix ++ B 22 ++ B 23 ++ B 24 ++ B 29)⟩ := by
  obtain ⟨tc,htc,hc⟩ := three_copies_run B hblank
  have hp := CodeRowsLiteralPrefix.run (afterFirst B)
  have hresult :
      Function.update (afterFirst B) 29
        (branchPrefix ++ afterFirst B 29) =
      Function.update B 29
        (branchPrefix ++ B 22 ++ B 23 ++ B 24 ++ B 29) := by
    simp [afterFirst, Function.update, List.append_assoc]
  rw [hresult] at hp
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    threeCopiesProgram CodeRowsLiteralPrefix.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    CodeRowsLiteralPrefix.Label.write
    ((none,none),none) ((none,none),none) () ()
    B (afterFirst B)
    (Function.update B 29
      (branchPrefix ++ B 22 ++ B 23 ++ B 24 ++ B 29))
    tc 2 hc hp
  exact ⟨t, by omega, hr⟩

theorem branch_prefix_exact (first second third : Code) :
    branchPrefix ++ encodeCode first ++ encodeCode second ++
      encodeCode third =
    encodeCode (.branch3 512 510 511 first second third) := by
  simp [branchPrefix, encodeCode, List.append_assoc]

end Paper2.CodeRowsBranchAssembly
