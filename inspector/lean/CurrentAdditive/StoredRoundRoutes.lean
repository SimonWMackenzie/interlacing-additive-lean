import CurrentAdditive.StoredRoundData
import CurrentAdditive.DynamicGetterOrdinary

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundRoutes
open Paper2 EthInapproximability.CurrentPaper PhysicalProducer
open V39GeneratedConstruction
noncomputable section

def saved : Producer := projection (0 : Fin 8)
def context : Producer := compose saved (projection (0 : Fin 2))
def old : Producer := compose saved (projection (1 : Fin 2))
def publicField (j : Fin 7) : Producer := compose context (projection j)
def oldSlot (j : Fin 3) : Producer := compose old (projection j)
def oldRow : Producer := oldSlot 1
def oldColumn : Producer := oldSlot 2
def previous (i : Fin 7) : Producer := projection (⟨i.val+1,by have:=i.isLt;omega⟩ : Fin 8)
def phase (i : Fin 7) : Producer := compose (previous i) (projection (1 : Fin 2))
def phaseLaw (i : Fin 7) : Producer := compose (phase i) (projection (1 : Fin 3))
def one : Producer := V40SeedProducer.constant [true]
def gammaQ : Producer := concat (concat (publicField 0) (publicField 2)) one

theorem saved_result (a : StoredRoundData.Data) (k : Nat) :
    saved.result (StoredRoundData.state a k)=StoredRoundData.input a :=
  StoredRoundData.state_input a k

theorem context_result (a : StoredRoundData.Data) (k : Nat) :
    context.result (StoredRoundData.state a k)=StoredStepContext.context
      a.parameters.q₁ a.parameters.w a.parameters.Q a.parameters.μI a.activity := by
  simp only [context,compose,Function.comp_apply,projection,saved_result,StoredRoundData.input,
    StoredStepContext.packet_context]

theorem public_result (a : StoredRoundData.Data) (k : Nat) (j : Fin 7) :
    (publicField j).result (StoredRoundData.state a k)=
      (![List.replicate a.parameters.q₁ true,List.replicate a.parameters.q₂ true,
        List.replicate a.parameters.s true,List.replicate a.parameters.w true,
        List.replicate a.parameters.Q true,StoredWeightedState.lawBytes a.parameters.μI,
        StoredStepContext.activityWords a.activity] : Fin 7 → List Bool) j := by
  simp only [publicField,compose,Function.comp_apply,projection,context_result,
    StoredStepContext.context,BankFieldProjection.result_encode]

theorem old_result (a : StoredRoundData.Data) (k : Nat) :
    old.result (StoredRoundData.state a k)=StoredWeightedState.encode a.parameters.R := by
  simp only [old,compose,Function.comp_apply,projection,saved_result,StoredRoundData.input,
    StoredStepContext.packet_state]

theorem oldRow_result (a : StoredRoundData.Data) (k : Nat) :
    oldRow.result (StoredRoundData.state a k)=StoredWeightedState.lawBytes a.parameters.R.rowLaw := by
  simp [oldRow,oldSlot,compose,projection,old_result,StoredWeightedState.encode]

theorem oldColumn_result (a : StoredRoundData.Data) (k : Nat) :
    oldColumn.result (StoredRoundData.state a k)=StoredWeightedState.lawBytes a.parameters.R.colLaw := by
  simp [oldColumn,oldSlot,compose,projection,old_result,StoredWeightedState.encode]

theorem previous_result (a : StoredRoundData.Data) (i : Fin 7) (k : Nat) (hi : i.val<k) :
    (previous i).result (StoredRoundData.state a k)=StoredRoundData.record a i :=
  StoredRoundData.state_record a i k hi

theorem phaseLaw_result (a : StoredRoundData.Data) (i : Fin 7) (k : Nat) (hi : i.val<k) :
    (phaseLaw i).result (StoredRoundData.state a k)=StoredSourcePhase.lawBytes (StoredRoundData.call a i) := by
  simp [phaseLaw,phase,compose,Function.comp_apply,projection,previous_result a i k hi,
    StoredRoundData.record,StoredSourcePhase.output]

theorem gammaLaw_result (a : StoredRoundData.Data) (k : Nat) (hk : 0<k) :
    (phaseLaw 0).result (StoredRoundData.state a k)=
      StoredWeightedState.lawBytes (StoredRoundData.src a).gamma.law := by
  rw [phaseLaw_result a 0 k hk]
  rfl

theorem innerLaw_result (a : StoredRoundData.Data) (k : Nat) (hk : 1<k) :
    (phaseLaw 1).result (StoredRoundData.state a k)=
      StoredWeightedState.lawBytes (StoredRoundData.src a).inner.law := by
  rw [phaseLaw_result a 1 k hk]
  rfl

theorem outerLaw_result (a : StoredRoundData.Data) (k : Nat) (hk : 2<k) :
    (phaseLaw 2).result (StoredRoundData.state a k)=
      StoredWeightedState.lawBytes (StoredRoundData.src a).outer.law := by
  rw [phaseLaw_result a 2 k hk]
  rfl

theorem gammaQ_result (a : StoredRoundData.Data) (k : Nat) :
    gammaQ.result (StoredRoundData.state a k)=List.replicate (a.parameters.q₁+a.parameters.s+1) true := by
  simp only [gammaQ,concat,public_result,Matrix.cons_val_zero,Matrix.cons_val_succ,
    one,V40SeedProducer.constant]
  change (List.replicate a.parameters.q₁ true++List.replicate a.parameters.s true)++[true]=_
  simp only [List.replicate_add,List.replicate_one]

def request (i : Fin 7) : Producer := match i.val with
  | 0 => DynamicGetterOrdinary.bankFields [gammaQ,oldColumn]
  | 1 => DynamicGetterOrdinary.bankFields [publicField 1,publicField 0,oldRow]
  | 2 => DynamicGetterOrdinary.bankFields [publicField 2,publicField 1,phaseLaw 0]
  | 3 => DynamicGetterOrdinary.bankFields [publicField 3,publicField 2,publicField 5]
  | 4 => DynamicGetterOrdinary.bankFields [publicField 3,oldRow]
  | 5 => DynamicGetterOrdinary.bankFields [publicField 3,phaseLaw 1]
  | _ => DynamicGetterOrdinary.bankFields [publicField 4,publicField 3,publicField 1,phaseLaw 2,phaseLaw 0]

theorem request_result (a : StoredRoundData.Data) (i : Fin 7) :
    (request i).result (StoredRoundData.state a i.val)=V40ActualSevenRequests.input a.parameters i := by
  fin_cases i
  all_goals
    simp [request,DynamicGetterOrdinary.bankFields_result,List.flatMap_cons,List.flatMap_nil,
      gammaQ_result,public_result,oldColumn_result,oldRow_result,
      gammaLaw_result,innerLaw_result,outerLaw_result,
      V40ActualSevenRequests.input,V40ActualSevenRequests.gammaData,V40ActualSevenRequests.innerData,
      V40ActualSevenRequests.outerData,V40ActualSevenRequests.metadataData,V40ActualSevenRequests.baseData,
      V40ActualSevenRequests.selectorData,V40ActualSevenRequests.finalData,
      V40DirectLawRequest.input,V40UniformLawJobs.input,V40FinalSourceRequest.input,
      V40LawJobsClock.packet_eq,BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.ofFn_zero,
      StoredRoundData.src,Matrix.cons_val_zero,Matrix.cons_val_succ,List.append_nil]

theorem request_outputs (a : StoredRoundData.Data) (i : Fin 7) :
    (request i).machine.OutputsWithin (StoredRoundData.state a i.val)
      (V40ActualSevenRequests.input a.parameters i)
      ((request i).coefficient*((StoredRoundData.state a i.val).length+1)^(request i).degree) := by
  simpa only [request_result] using (request i).outputs (StoredRoundData.state a i.val)

end
end CurrentAdditive.StoredRoundRoutes

#print axioms CurrentAdditive.StoredRoundRoutes.request_result
#print axioms CurrentAdditive.StoredRoundRoutes.request_outputs
