import CurrentAdditive.V39DeadSampleResult
import CurrentAdditive.V39DeadTaggedMachine

/-! One fixed finite controller builds the exact current row-first sample
Code from literal public raw counts and unary level fuel. Its complete final
bank is explicit. This file does not execute the generated sample Code. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000

namespace CurrentAdditive.V39CurrentCodeConstructor

open Paper2
open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open V39DeadTaggedCompiler

abbrev Stack := V39DeadSampleJoin.Stack
abbrev CompilerLabel := BitMachineRawSequence.Label
  V39DeadCodeComplete.SeedLabel V39DeadCodeLoop.Label
abbrev TransferLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
      CodeGeneratorSampleTransfer.TermLabel) BitMachineCopy.Label)
  BitMachineCopy.Label
abbrev AssemblyLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label CodeCopiesMachine.Label CodeCopiesMachine.Label)
  CodeConstructorMachine.Label
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label CompilerLabel TransferLabel) AssemblyLabel
abbrev CompilerControl := V39DeadCodeComplete.SeedControl × V39DeadCodeLoop.Control
abbrev TransferControl := ((((Option Bool × Option Bool) × Unit) × Option Bool) × Option Bool)
abbrev AssemblyControl := ((Option Bool × Option Bool) × Option Bool)
abbrev Control := (CompilerControl × TransferControl) × AssemblyControl

def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel V39DeadSampleJoin.compilerStart)
def control : Control :=
  ((V39DeadSampleJoin.compilerControl,V39DeadSampleJoin.transferControl),
    V39DeadSampleJoin.assemblyControl)

noncomputable def finalBank (n p q₁ q₂ s w Q k m : Nat) : Stack → List Bool :=
  let pair := deadCodes n p q₁ q₂ s w Q k
  V39DeadSampleJoin.afterAssembly
    (V39DeadCodeLoop.finished n s q₁ q₂ w Q pair.1 pair.2).stk
    m m pair.1 pair.2

theorem seedCodes_eq (n p q₁ q₂ s w Q k : Nat) :
    V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k =
      deadCodes n p q₁ q₂ s w Q k :=
  V39DeadGenericCode.seed_eq n p q₁ q₂ s w Q k

theorem final_output (n p q₁ q₂ s w Q k m : Nat) :
    finalBank n p q₁ q₂ s w Q k m (CodeGeneratorSampleTransfer.sample 10) =
      encodeCode (deadSampleCode n p q₁ q₂ s w Q k m) := by
  exact V39DeadSampleJoin.output_exact _ m m _ _

theorem physical_construct (n p q₁ q₂ s w Q k m : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m,
      ((advance V39DeadSampleJoin.program)^[t])
        (⟨some start,control,V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,control,finalBank n p q₁ q₂ s w Q k m⟩ := by
  obtain ⟨t,ht,hr⟩ := V39DeadSampleJoin.run n p s q₁ q₂ w Q k m m hs
  rw [seedCodes_eq] at hr
  exact ⟨t,ht,hr⟩

noncomputable section

private noncomputable opaque finiteStacks : Fintype Stack := inferInstance
private noncomputable opaque finiteLabels : Fintype Label := inferInstance
private noncomputable opaque finiteControls : Fintype Control := inferInstance

local instance : Fintype Stack := finiteStacks
local instance : Fintype Label := finiteLabels
local instance : Fintype Control := finiteControls

noncomputable def machine := ofFinite (.inl (0 : Fin 65) : Stack)
  (CodeGeneratorSampleTransfer.sample 10) start control V39DeadSampleJoin.program

theorem machine_construct (n p q₁ q₂ s w Q k m : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m,
      machine.run t
        (renameCfg (Fintype.equivFin Stack) (Fintype.equivFin Label) (Fintype.equivFin Control)
          (⟨some start,control,V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control)) =
        renameCfg (Fintype.equivFin Stack) (Fintype.equivFin Label) (Fintype.equivFin Control)
          (⟨none,control,finalBank n p q₁ q₂ s w Q k m⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) := by
  obtain ⟨t,ht,hr⟩ := physical_construct n p q₁ q₂ s w Q k m hs
  refine ⟨t,ht,?_⟩
  exact (ofFinite_run (.inl (0 : Fin 65) : Stack)
    (CodeGeneratorSampleTransfer.sample 10) start control V39DeadSampleJoin.program
    (⟨some start,control,V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) t).trans
    (congrArg (renameCfg (Fintype.equivFin Stack) (Fintype.equivFin Label)
      (Fintype.equivFin Control)) hr)

#print axioms final_output
#print axioms physical_construct
#print axioms machine_construct

end

end CurrentAdditive.V39CurrentCodeConstructor
