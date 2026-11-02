import CurrentAdditive.V40SeedProducer
import CurrentAdditive.WeightedIterationDriver
import CurrentAdditive.StoredWeightedState

/-! An actual ordered uniform-law loop. Its evolving word contains only the
unary index, retained unary size, and the bytes already printed. -/
namespace CurrentAdditive.V40UniformLawLoop
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineBankCodec EncodedCommunication PhysicalProducer

def entries (n j : Nat) : List (List Bool) :=
  (List.range j).map (fun i => CodeDTargetV2.alphabetEntry (i,(n:ℚ)⁻¹))

def accumulator (n j : Nat) : List Bool := natField n ++ SourceListEncoding.fields (entries n j)

def state (n j : Nat) : List Bool :=
  encode ![List.replicate j true,List.replicate n true,accumulator n j]

def entryInput : Producer :=
  concat (compose (projection (0:Fin 3)) PhysicalProducer.field)
    (compose (projection (1:Fin 3)) PhysicalProducer.field)

def nextIndex : Producer := concat (V40SeedProducer.constant [true]) (projection (0:Fin 3))
def appended : Producer :=
  concat (projection (2:Fin 3))
    (compose (compose entryInput V40SeedProducer.entry) item)

def body : Producer :=
  concat (compose nextIndex PhysicalProducer.field)
    (concat (compose (projection (1:Fin 3)) PhysicalProducer.field)
      (compose appended PhysicalProducer.field))

theorem fields_append (a b : List (List Bool)) :
    SourceListEncoding.fields (a++b)=SourceListEncoding.fields a++SourceListEncoding.fields b := by
  induction a with
  | nil => simp [SourceListEncoding.fields]
  | cons a as ih => simp [SourceListEncoding.fields,ih,List.append_assoc]

theorem accumulator_succ (n j : Nat) :
    accumulator n (j+1)=accumulator n j++
      SourceListMachineWriter.result true (CodeDTargetV2.alphabetEntry (j,(n:ℚ)⁻¹)) := by
  simp [accumulator,entries,List.range_succ,List.map_append,fields_append,
    SourceListEncoding.fields,SourceListMachineWriter.result,List.append_assoc]

theorem body_result (n j : Nat) (hn : 0<n) : body.result (state n j)=state n (j+1) := by
  have he : entryInput.result (state n j)=encode ![List.replicate j true,List.replicate n true] := by
    simp only [entryInput,concat,compose,projection,PhysicalProducer.field,state,
      Function.comp_apply,BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp [encode,encodeFrom]
  have ha : appended.result (state n j)=accumulator n (j+1) := by
    simp only [appended,concat,compose,projection,Function.comp_apply,
      state,BankFieldProjection.result_encode,Matrix.cons_val_two]
    change accumulator n j ++ item.result (V40SeedProducer.entry.result
      (entryInput.result (state n j)))=accumulator n (j+1)
    rw [he,V40SeedProducer.entry_result j n hn]
    exact (accumulator_succ n j).symm
  simp only [body,concat,compose,Function.comp_apply]
  rw [ha]
  simp only [nextIndex,concat,V40SeedProducer.constant,projection,PhysicalProducer.field,
    state,BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,
    List.singleton_append,List.replicate_succ]
  simp [encode,encodeFrom]

def identity : Producer := compose V40SeedProducer.reverse V40SeedProducer.reverse
def unaryField : Producer where
  machine := SourceFieldWriter.unaryFieldMachine
  result := fun input => natField input.length
  coefficient := UnaryBinaryEncoding.coefficient+10
  degree := 2
  outputs := SourceFieldWriter.unary_field_outputs

def prepare : Producer :=
  concat (V40SeedProducer.constant (field []))
    (concat PhysicalProducer.field (compose unaryField PhysicalProducer.field))

def withFuel : Producer := concat (compose prepare PhysicalProducer.field) PhysicalProducer.field

theorem prepare_result (n : Nat) : prepare.result (List.replicate n true)=state n 0 := by
  simp [prepare,concat,V40SeedProducer.constant,compose,unaryField,PhysicalProducer.field,
    state,accumulator,entries,SourceListEncoding.fields,encode,encodeFrom]

theorem withFuel_result (n : Nat) :
    withFuel.result (List.replicate n true)=WeightedIterationDriver.input (state n 0) n := by
  simp only [withFuel,concat,compose,Function.comp_apply,PhysicalProducer.field]
  rw [prepare_result]
  simp [WeightedIterationDriver.input,WeightedIterationLoader.packet,encode,encodeFrom]

def stepClock (n j : Nat) := body.coefficient*((state n j).length+1)^body.degree

theorem step_outputs (n j : Nat) (hn : 0<n) :
    body.machine.OutputsWithin (state n j) (state n (j+1)) (stepClock n j) := by
  simpa only [body_result n j hn,stepClock] using body.outputs (state n j)

def loopMachine := WeightedIterationDriver.machine body.machine
def loopClock (n : Nat) := WeightedIterationDriver.clock body.machine (state n) (stepClock n) n

theorem loop_outputs (n : Nat) (hn : 0<n) :
    loopMachine.OutputsWithin (WeightedIterationDriver.input (state n 0) n)
      (state n n) (loopClock n) :=
  WeightedIterationDriver.outputs body.machine (state n) (stepClock n) n
    (fun j _ => step_outputs n j hn)

theorem final_projection (n : Nat) :
    BankFieldProjection.result (2:Fin 3) (state n n)=SourceListEncoding.encode (entries n n) := by
  simp [state,BankFieldProjection.result_encode,accumulator,SourceListEncoding.encode,entries]

#print axioms body_result
#print axioms loop_outputs
end
end CurrentAdditive.V40UniformLawLoop
