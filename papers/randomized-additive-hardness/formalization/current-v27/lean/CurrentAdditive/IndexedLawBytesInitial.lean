import CurrentAdditive.IndexedLawBytesPrimitives
import CurrentAdditive.IndexedLawBytesBounds
import CurrentAdditive.OrdinaryBankFork
import CurrentAdditive.FeatureMapListCount
import CurrentAdditive.WeightedIterationDriver

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec PhysicalProducer

def initialLayout : Producer := CodeDPacketRouting.bank2
  (CodeDPacketRouting.bank3 (projection (0 : Fin 2)) DynamicGetterPrimitives.empty DynamicGetterPrimitives.empty)
  (projection (1 : Fin 2))

def initialMachine : BitMachine.Machine := BitMachineComposition.composition
  (OrdinaryBankFork.machine identity.machine FeatureMapListCount.machine) initialLayout.machine

theorem initialLayout_result (xs : List (List Bool)) :
    initialLayout.result (OrdinaryBankFork.packet (SourceListEncoding.encode xs) (List.replicate xs.length true))=
      WeightedIterationDriver.input (state xs 0) xs.length := by
  unfold initialLayout
  rw [CodeDPacketRouting.bank2_result,CodeDPacketRouting.bank3_result]
  simp only [projection,DynamicGetterPrimitives.empty,OrdinaryBankFork.packet,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,
    state,fieldsAt_zero,List.replicate_zero,WeightedIterationDriver.input,WeightedIterationLoader.packet]

theorem initial_uniform : ∃ C E : Nat,∀xs : List (List Bool),
    initialMachine.OutputsWithin (SourceListEncoding.encode xs)
      (WeightedIterationDriver.input (state xs 0) xs.length)
      (C*((SourceListEncoding.encode xs).length+1)^E) := by
  let F := OrdinaryBankFork.machine identity.machine FeatureMapListCount.machine
  let a := OrdinaryBankFork.coefficient identity.machine FeatureMapListCount.machine 2 20
  let d := OrdinaryBankFork.degree 1 1
  refine ⟨DynamicGetterOrdinary.composeCoefficient F a initialLayout.coefficient initialLayout.degree,
    DynamicGetterOrdinary.composeDegree d initialLayout.degree,?_⟩
  intro xs
  have hcopy := identity.outputs (SourceListEncoding.encode xs)
  have hc := FeatureMapListCount.outputs xs.length (SourceListEncoding.fields xs)
  have hb := FeatureMapListCount.bound_le xs.length (SourceListEncoding.encode xs) (inputSize xs)
    (count_le xs) le_rfl
  have hcount : FeatureMapListCount.machine.OutputsWithin (SourceListEncoding.encode xs)
      (List.replicate xs.length true) (20*((SourceListEncoding.encode xs).length+1)^1) :=
    BitMachine.outputsWithin_mono _ hc (by simpa only [pow_one] using hb)
  have hfork := OrdinaryBankFork.outputsWithin identity.machine FeatureMapListCount.machine hcopy hcount
  have hfork' := BitMachine.outputsWithin_mono _ hfork
    (OrdinaryBankFork.clock_le_polynomial identity.machine FeatureMapListCount.machine
      (SourceListEncoding.encode xs).length 2 1 20 1)
  have hl := initialLayout.outputs (OrdinaryBankFork.packet (SourceListEncoding.encode xs) (List.replicate xs.length true))
  rw [initialLayout_result] at hl
  exact DynamicGetterOrdinary.compose_outputs _ _ _ _ _ a d initialLayout.coefficient initialLayout.degree hfork' hl

#print axioms initial_uniform
end CurrentAdditive.IndexedLawBytes
