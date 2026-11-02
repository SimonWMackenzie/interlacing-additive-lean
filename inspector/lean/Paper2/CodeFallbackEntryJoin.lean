import Paper2.CodeFallbackEntryBank

/-! Fixed physical compiler, sample assembler, interpreter-code loader, and
fallback-writer dimension loader, stopping just before interpreter execution. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeFallbackEntryJoin

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeFallbackDimensionLoader

abbrev Stack := CodeFallbackDimensionLoader.Stack

def sourceSlots : CodeSampleInterpreterJoin.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

theorem source_bank (S : CodeSampleInterpreterJoin.Stack → List Bool) :
    bank sourceSlots (fun _ : Stack => []) S = initialBank S := by
  funext j
  cases j with
  | inl j =>
    simpa only [sourceSlots, initialBank, Sum.elim_inl] using
      (bank_at sourceSlots (fun _ : Stack => []) S j)
  | inr j =>
    simpa only [initialBank, Sum.elim_inr] using
      (bank_outside sourceSlots (fun _ : Stack => []) S (.inr j)
        (by rintro ⟨k,h⟩; cases h))

noncomputable def sourceProgram := fun l =>
  stackStmt sourceSlots (CodeSampleInterpreterJoin.program l)
def sourceControl :=
  (CodeSampleInterpreterJoin.sampleControl,
    CodeSampleInterpreterJoin.copyControl)
def copyControl : Option Bool := none

noncomputable def firstProgram :=
  BitMachineRawSequence.program sourceProgram xProgram .scan
    sourceControl copyControl
noncomputable def program :=
  BitMachineRawSequence.program firstProgram yProgram .scan
    (sourceControl,copyControl) copyControl

noncomputable def initial (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) : Stack → List Bool :=
  initialBank
    (CodeSampleInterpreterJoin.initial n p s q₁ q₂ w Q k mX mY
      tape B R)

noncomputable def finalBank (n s q₁ q₂ w Q k mX mY : Nat)
    (row col : Code) (tape : List Bool) (B R : Nat) : Stack → List Bool :=
  afterY
    (CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
      row col tape B R) mX mY

noncomputable def clock (n p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  CodeSampleInterpreterJoin.clock n p s q₁ q₂ w Q k mX mY +
    (2*mX+2) + (2*mY+2) + 2

theorem source_run (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ CodeSampleInterpreterJoin.clock n p s q₁ q₂ w Q k mX mY,
      let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
      ((advance sourceProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                CodeGeneratorSampleJoin.compilerStart))),
          sourceControl,
          initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,sourceControl,
          initialBank (CodeSampleInterpreterJoin.finalBank
            n s q₁ q₂ w Q k mX mY c.1 c.2 tape B R)⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeSampleInterpreterJoin.run
    n p s q₁ q₂ w Q k mX mY tape B R hs
  have h := BitMachineStackRun.run sourceSlots (fun _ : Stack => [])
    CodeSampleInterpreterJoin.program
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            CodeGeneratorSampleJoin.compilerStart))),
      sourceControl,
      CodeSampleInterpreterJoin.initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
        TM2.Cfg (fun _ : CodeSampleInterpreterJoin.Stack => Bool) _ _) t
  change ((advance CodeSampleInterpreterJoin.program)^[t])
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            CodeGeneratorSampleJoin.compilerStart))),
      sourceControl,
      CodeSampleInterpreterJoin.initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
        TM2.Cfg (fun _ : CodeSampleInterpreterJoin.Stack => Bool) _ _) =
    ⟨none,sourceControl,
      CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
        (GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k).1
        (GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k).2 tape B R⟩ at hr
  rw [hr] at h
  exact ⟨t,ht,by
    simpa only [sourceProgram, initial, source_bank, stackCfg]
      using h⟩

theorem run (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ clock n p s q₁ q₂ w Q k mX mY,
      let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    CodeGeneratorSampleJoin.compilerStart))))),
          ((sourceControl,copyControl),copyControl),
          initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((sourceControl,copyControl),copyControl),
          finalBank n s q₁ q₂ w Q k mX mY c.1 c.2 tape B R⟩ := by
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  let S := CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
    c.1 c.2 tape B R
  obtain ⟨ts,hts,hsr⟩ := source_run n p s q₁ q₂ w Q k mX mY
    tape B R hs
  obtain ⟨_,_,_,_,hx,hy⟩ := CodeSampleInterpreterResult.run_ready
    n p s q₁ q₂ w Q k mX mY tape B R hs
  have hscr := CodeFallbackEntryBank.source_scratch
    n s q₁ q₂ w Q k mX mY c.1 c.2 tape B R
  have hxrun := x_run S mX hx hscr
  have hyrun := y_run S mX mY hy hscr
  obtain ⟨tx,htx,hxj⟩ := BitMachineRawSequence.runs
    sourceProgram xProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          CodeGeneratorSampleJoin.compilerStart))) .scan
    sourceControl sourceControl copyControl copyControl
    (initial n p s q₁ q₂ w Q k mX mY tape B R)
    (initialBank S) (afterX S mX)
    ts (2*mX+2) hsr hxrun
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    firstProgram yProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            CodeGeneratorSampleJoin.compilerStart)))) .scan
    (sourceControl,copyControl) (sourceControl,copyControl)
    copyControl copyControl
    (initial n p s q₁ q₂ w Q k mX mY tape B R)
    (afterX S mX) (afterY S mX mY)
    tx (2*mY+2) (by simpa only [firstProgram] using hxj) hyrun
  exact ⟨t,by
    change t ≤ CodeSampleInterpreterJoin.clock n p s q₁ q₂ w Q k mX mY +
      (2*mX+2)+(2*mY+2)+2
    omega,
    by simpa only [program, finalBank, S, c] using hr⟩

#print axioms source_run
#print axioms run

end Paper2.CodeFallbackEntryJoin
