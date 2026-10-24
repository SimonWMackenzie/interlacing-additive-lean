import CurrentAdditive.IndexedLawBytesPrimitives
import CurrentAdditive.ContextualInvokePolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec PhysicalProducer

def preRequest : Producer := CodeDPacketRouting.bank2 (projection (0 : Fin 3))
  (compose (projection (1 : Fin 3)) unaryBinary)

def pre : Producer := CodeDPacketRouting.bank2 identity preRequest

def ctx (i : Fin 3) : Producer := compose (projection (0 : Fin 2)) (projection i)

def selectedWeight : Producer := compose (projection (1 : Fin 2)) (projection (1 : Fin 2))

def indexedEntry : Producer := CodeDPacketRouting.bank2 (compose (ctx 1) unaryBinary) selectedWeight

def post : Producer := CodeDPacketRouting.bank3 (ctx 0) (compose (ctx 1) unarySucc)
  (concat (ctx 2) (compose indexedEntry item))

theorem pre_result (xs : List (List Bool)) (i : Nat) :
    pre.result (state xs i)=ContextualInvoke.packet (state xs i) (DynamicGetterOrdinary.packet xs i.bits) := by
  unfold pre preRequest
  rw [CodeDPacketRouting.bank2_result,CodeDPacketRouting.bank2_result]
  simp only [identity,id_eq,projection,compose,Function.comp_apply,state,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,
    unaryBinary,List.length_replicate,ContextualInvoke.packet,DynamicGetterOrdinary.packet]

theorem ctx_result (xs : List (List Bool)) (i : Nat) (word : List Bool) (k : Fin 3) :
    (ctx k).result (ContextualInvoke.output (state xs i) word)=
      (![SourceListEncoding.encode xs,List.replicate i true,fieldsAt xs i] : Fin 3 → List Bool) k := by
  simp only [ctx,compose,projection,Function.comp_apply,ContextualInvoke.output,state,
    BankFieldProjection.result_encode,Matrix.cons_val_zero]

theorem selectedWeight_result (context word : List Bool) :
    selectedWeight.result (ContextualInvoke.output context word)=weightWord word := by
  simp only [selectedWeight,compose,projection,Function.comp_apply,ContextualInvoke.output,
    BankFieldProjection.result_encode,Matrix.cons_val_one,Matrix.cons_val_zero,weightWord]

theorem indexedEntry_result (xs : List (List Bool)) (i : Nat) (word : List Bool) :
    indexedEntry.result (ContextualInvoke.output (state xs i) word)=indexedWord i word := by
  unfold indexedEntry
  rw [CodeDPacketRouting.bank2_result]
  simp only [compose,Function.comp_apply,ctx_result,Matrix.cons_val_one,Matrix.cons_val_zero,
    unaryBinary,List.length_replicate,selectedWeight_result,indexedWord]

theorem post_result (xs : List (List Bool)) (i : Nat) (hi : i<xs.length) :
    post.result (ContextualInvoke.output (state xs i) xs[i])=state xs (i+1) := by
  unfold post
  rw [CodeDPacketRouting.bank3_result]
  simp only [compose,concat,Function.comp_apply,ctx_result,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,unarySucc,indexedEntry_result,item]
  change encode ![SourceListEncoding.encode xs,true::List.replicate i true,
    fieldsAt xs i++SourceListMachineWriter.result true (indexedWord i xs[i])]=state xs (i+1)
  rw [← fieldsAt_succ_get xs i hi]
  simp only [state,List.replicate_succ]

/-- Its program depends only on fixed machines, never on a selected source
position, source length, successful-run witness, or generated labels. -/
def stepMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition pre.machine (ContextualInvoke.machine DynamicGetterOrdinary.machine)) post.machine

attribute [local irreducible] stepMachine

theorem step_uniform : ∃ C E : Nat, ∀ (xs : List (List Bool)) (i : Nat), i<xs.length →
    stepMachine.OutputsWithin (state xs i) (state xs (i+1)) (C*((state xs i).length+1)^E) := by
  obtain ⟨a,e,hgetter⟩ := DynamicGetterOrdinary.uniform
  let cc := ContextualInvoke.polynomialCoefficient DynamicGetterOrdinary.machine a
  let cd := e+1
  let bc := DynamicGetterOrdinary.composeCoefficient pre.machine pre.coefficient cc cd
  let bd := DynamicGetterOrdinary.composeDegree pre.degree cd
  refine ⟨DynamicGetterOrdinary.composeCoefficient
      (BitMachineComposition.composition pre.machine (ContextualInvoke.machine DynamicGetterOrdinary.machine))
      bc post.coefficient post.degree,
    DynamicGetterOrdinary.composeDegree bd post.degree,?_⟩
  intro xs i hi
  have hA := pre.outputs (state xs i)
  have hB := ContextualInvoke.outputs_polynomial DynamicGetterOrdinary.machine a e
    (state xs i) (DynamicGetterOrdinary.packet xs i.bits) xs[i] (hgetter xs i hi)
  rw [← pre_result] at hB
  have hAB := DynamicGetterOrdinary.compose_outputs _ _ _ _ _
    pre.coefficient pre.degree cc cd hA hB
  have hC' := post.outputs (ContextualInvoke.output (state xs i) xs[i])
  rw [post_result xs i hi] at hC'
  unfold stepMachine
  exact DynamicGetterOrdinary.compose_outputs _ _ _ _ _ bc bd post.coefficient post.degree hAB hC'

#print axioms step_uniform
end CurrentAdditive.IndexedLawBytes
