import CurrentAdditive.IndexedLawBytesLoop

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec PhysicalProducer

def finalProducer : Producer := concat (compose (compose (projection (1 : Fin 3)) unaryBinary) field)
  (projection (2 : Fin 3))

theorem final_result (xs : List (List Bool)) :
    finalProducer.result (state xs xs.length)=output xs := by
  simp only [finalProducer,concat,compose,projection,Function.comp_apply,state,
    BankFieldProjection.result_encode,Matrix.cons_val_one,Matrix.cons_val_two,unaryBinary,
    List.length_replicate,field]
  change EncodedCommunication.field (List.replicate xs.length true).length.bits++fieldsAt xs xs.length=output xs
  rw [List.length_replicate]
  change EncodedCommunication.natField xs.length++fieldsAt xs xs.length=output xs
  rw [fieldsAt_final]
  simp only [output,SourceListEncoding.encode,outputItems_length]

def machine : BitMachine.Machine := BitMachineComposition.composition
  (BitMachineComposition.composition initialMachine loopMachine) finalProducer.machine

/-- One fixed machine physically generates every position label, including
positions with equal records. No semantic or run premise occurs here. -/
theorem uniform : ∃ C E : Nat,∀xs : List (List Bool),
    machine.OutputsWithin (SourceListEncoding.encode xs) (output xs)
      (C*((SourceListEncoding.encode xs).length+1)^E) := by
  obtain ⟨a,d,hA⟩ := initial_uniform
  obtain ⟨b,e,hB⟩ := loop_uniform
  let c := DynamicGetterOrdinary.composeCoefficient initialMachine a b e
  let f := DynamicGetterOrdinary.composeDegree d e
  refine ⟨DynamicGetterOrdinary.composeCoefficient (BitMachineComposition.composition initialMachine loopMachine)
    c finalProducer.coefficient finalProducer.degree,
    DynamicGetterOrdinary.composeDegree f finalProducer.degree,?_⟩
  intro xs
  have hB' := BitMachine.outputsWithin_mono _ (hB xs)
    (Nat.mul_le_mul_left b (Nat.pow_le_pow_left (Nat.add_le_add_right (loopInput_contains_source xs) 1) e))
  have hAB := DynamicGetterOrdinary.compose_outputs _ _ _ _ _ a d b e (hA xs) hB'
  have hC := finalProducer.outputs (state xs xs.length)
  rw [final_result] at hC
  exact DynamicGetterOrdinary.compose_outputs _ _ _ _ _ c f finalProducer.coefficient finalProducer.degree hAB hC

#print axioms uniform
end CurrentAdditive.IndexedLawBytes
