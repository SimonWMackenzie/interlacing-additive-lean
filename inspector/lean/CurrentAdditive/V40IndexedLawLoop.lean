import CurrentAdditive.V40SourceContextSpec
import CurrentAdditive.V40SourceLocal
import CurrentAdditive.D22ArithmeticGrowth
import CurrentAdditive.WeightedIterationDriver

namespace CurrentAdditive.V40IndexedLawLoop
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open BitMachineBankCodec EncodedCommunication D22PolynomialExpression
open V40SourceContextSpec V40SourceLocal D22PacketPrimitives
abbrev P := V40SourceLocal.Producer
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

def add (a b : Term) : Term := .binary (.old .add) a b
def mul (a b : Term) : Term := .binary (.old .mul) a b
def quot (a b : Term) : Term := .binary .quot a b
def le (a b : Term) : Term := .binary .le a b
def aux : Term := .pred (.pred (.pred (.var 2)))
def divisor : Term := add (.var 1) aux
def lower : Term := quot (.var 0) divisor
def upper : Term := quot (add (.var 0) aux) divisor
def denTerm : Term := mul (mul (.const 8) (.var 2))
  (add (mul (.var 1) (le upper lower)) (mul aux (le (add lower (.const 1)) upper)))

theorem denTerm_eval (i n s : Nat) : denTerm.eval i n s=denominator s n i := by
  simp only [denTerm,add,mul,le,quot,upper,lower,divisor,aux,Term.eval,Term.expr,
    D22NatExpression.Expr.eval,D22NatExpression.Binary.value,V22UnaryExpression.Binary.value,
    V22UnaryExpression.Unary.value,D22NatExpression.values,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,denominator,vertexFlag,auxiliaryFlag,blockSize,auxiliaryCount]
  change 8*s*(n*(if (i+(s-1-1-1))/(n+(s-1-1-1)) ≤ i/(n+(s-1-1-1)) then 1 else 0)+
    (s-1-1-1)*(if i/(n+(s-1-1-1))+1 ≤ (i+(s-1-1-1))/(n+(s-1-1-1)) then 1 else 0))=_
  have h : s-1-1-1=s-3 := by omega
  rw [h]
  rfl

theorem denTerm_pure : D22ArithmeticGrowth.Pure denTerm := by decide

def count (s n : Nat) := 4*s*(n+(s-3))
def accumulator (s n j : Nat) := natField (count s n)++SourceListEncoding.fields (entries s n j)
def state (s n j : Nat) := encode ![List.replicate j true,List.replicate n true,
  List.replicate s true,List.replicate (count s n) true,accumulator s n j]
def input (s n : Nat) := encode ![List.replicate n true,List.replicate s true,
  List.replicate (count s n) true]

def den : P := scalar (0:Fin 5) 1 2 denTerm
def entryInput : P := serialise ![project (0:Fin 5),den]
def entry : P := V40SourceLocal.compose entryInput (physical V40SeedProducer.entry)
def newItem : P := V40SourceLocal.compose entry (physical PhysicalProducer.item)
def nextIndex : P := append (constant [true]) (project (0:Fin 5))
def nextAccumulator : P := append (project (4:Fin 5)) newItem
def bodyFields : Fin 5 → P :=
  ![nextIndex,project (1:Fin 5),project (2:Fin 5),project (3:Fin 5),nextAccumulator]
def body : P := serialise bodyFields

theorem den_result (s n j : Nat) : den.result (state s n j)=List.replicate (denominator s n j) true := by
  simp [den,scalar,state,BankFieldProjection.result_encode,denTerm_eval]
theorem entryInput_result (s n j : Nat) :
    entryInput.result (state s n j)=encode ![List.replicate j true,
      List.replicate (denominator s n j) true] := by
  rw [entryInput,serialise_result]
  congr 1
  funext k
  fin_cases k
  · simp [project,state,BankFieldProjection.result_encode]
  · exact den_result s n j
theorem entry_result (s n j : Nat) (hd : 0<denominator s n j) :
    entry.result (state s n j)=CodeDTargetV2.alphabetEntry (j,((denominator s n j:Nat):ℚ)⁻¹) := by
  change V40SeedProducer.entry.result (entryInput.result (state s n j))=_
  rw [entryInput_result,V40SeedProducer.entry_result j _ hd]

theorem fields_append (a b : List (List Bool)) :
    SourceListEncoding.fields (a++b)=SourceListEncoding.fields a++SourceListEncoding.fields b := by
  induction a with
  | nil => simp [SourceListEncoding.fields]
  | cons a as ih => simp [SourceListEncoding.fields,ih,List.append_assoc]
theorem accumulator_succ (s n j : Nat) :
    accumulator s n (j+1)=accumulator s n j++SourceListMachineWriter.result true
      (CodeDTargetV2.alphabetEntry (j,((denominator s n j:Nat):ℚ)⁻¹)) := by
  simp [accumulator,entries,List.range_succ,List.map_append,fields_append,
    SourceListEncoding.fields,SourceListMachineWriter.result,List.append_assoc]
theorem body_result (s n j : Nat) (hd : 0<denominator s n j) :
    body.result (state s n j)=state s n (j+1) := by
  rw [body,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k
  · simp [bodyFields,nextIndex,append,constant,physical,V40SeedProducer.constant,project,
      state,BankFieldProjection.result_encode,List.replicate_succ]
  · simp [bodyFields,project,state,BankFieldProjection.result_encode]
  · simp [bodyFields,project,state,BankFieldProjection.result_encode]
  · simp [bodyFields,project,state,BankFieldProjection.result_encode]
  · change nextAccumulator.result (state s n j)=accumulator s n (j+1)
    simp only [nextAccumulator,append,project,state,BankFieldProjection.result_encode]
    change accumulator s n j++SourceListMachineWriter.result true (entry.result (state s n j))=_
    rw [entry_result s n j hd]
    exact (accumulator_succ s n j).symm

theorem den_outputs (s n j : Nat) :
    den.machine.OutputsWithin (state s n j) (den.result (state s n j)) (den.clock (state s n j)) := by
  apply scalar_outputs (0:Fin 5) 1 2 denTerm _ j n s <;>
    simp [state,BankFieldProjection.result_encode]
theorem entry_outputs (s n j : Nat) :
    entry.machine.OutputsWithin (state s n j) (entry.result (state s n j)) (entry.clock (state s n j)) := by
  apply compose_outputs
  · apply serialise_outputs
    intro k
    fin_cases k
    · exact project_outputs _ _
    · exact den_outputs s n j
  · exact physical_outputs _ _
theorem body_outputs (s n j : Nat) :
    body.machine.OutputsWithin (state s n j) (body.result (state s n j)) (body.clock (state s n j)) := by
  apply serialise_outputs
  intro k
  fin_cases k
  · exact append_outputs _ _ _ (constant_outputs _ _) (project_outputs _ _)
  · exact project_outputs _ _
  · exact project_outputs _ _
  · exact project_outputs _ _
  · exact append_outputs _ _ _ (project_outputs _ _)
      (compose_outputs _ _ _ (entry_outputs s n j) (physical_outputs _ _))

def initial : P := serialise ![constant [],project (0:Fin 3),project (1:Fin 3),
  project (2:Fin 3),V40SourceLocal.compose (project (2:Fin 3)) unaryField]
def withFuel : P := serialise ![initial,project (2:Fin 3)]
theorem initial_result (s n : Nat) : initial.result (input s n)=state s n 0 := by
  rw [initial,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k <;> simp [constant,physical,V40SeedProducer.constant,project,input,
    V40SourceLocal.compose,unaryField,BankFieldProjection.result_encode,state,accumulator,
    entries,SourceListEncoding.fields]
theorem withFuel_result (s n : Nat) :
    withFuel.result (input s n)=WeightedIterationDriver.input (state s n 0) (count s n) := by
  rw [withFuel,serialise_result]
  rw [show WeightedIterationDriver.input (state s n 0) (count s n)=
    encode ![state s n 0,List.replicate (count s n) true] from rfl]
  apply congrArg encode
  funext k
  fin_cases k
  · exact initial_result s n
  · simp [project,input,BankFieldProjection.result_encode]
theorem withFuel_outputs (x : List Bool) :
    withFuel.machine.OutputsWithin x (withFuel.result x) (withFuel.clock x) := by
  apply serialise_outputs
  intro k
  fin_cases k
  · apply serialise_outputs
    intro k
    fin_cases k
    · exact constant_outputs _ _
    · exact project_outputs _ _
    · exact project_outputs _ _
    · exact project_outputs _ _
    · exact compose_outputs _ _ _ (project_outputs _ _) (unaryField_outputs _)
  · exact project_outputs _ _

def loopMachine := WeightedIterationDriver.machine body.machine
def loopClock (s n : Nat) := WeightedIterationDriver.clock body.machine (state s n)
  (fun j => body.clock (state s n j)) (count s n)
theorem loop_outputs (s n : Nat) (hs : 4 ≤ s) (hn : 0<n) :
    loopMachine.OutputsWithin (WeightedIterationDriver.input (state s n 0) (count s n))
      (state s n (count s n)) (loopClock s n) := by
  apply WeightedIterationDriver.outputs
  intro j hj
  have hd:=denominator_pos s n hs hn ⟨j,hj⟩
  simpa only [body_result s n j hd] using body_outputs s n j

def machine := BitMachineComposition.composition
  (BitMachineComposition.composition withFuel.machine loopMachine) (BankFieldProjection.machine (4:Fin 5))
def clock (s n : Nat) := withFuel.clock (input s n)+2*(withFuel.result (input s n)).length+2+
  loopClock s n+2*(state s n (count s n)).length+2+14*((state s n (count s n)).length+1)

theorem outputs (s n : Nat) (hs : 4 ≤ s) (hn : 0<n) :
    machine.OutputsWithin (input s n) (StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw s n hs hn))
      (clock s n) := by
  have hl:=loop_outputs s n hs hn
  rw [←withFuel_result] at hl
  have h:=BitMachineComposition.composition_outputsWithin _ _ (withFuel_outputs (input s n)) hl
  have hp:=BankFieldProjection.outputs (4:Fin 5) (state s n (count s n))
  have hh:=BitMachineComposition.composition_outputsWithin _ _ h hp
  have he : BankFieldProjection.result (4:Fin 5) (state s n (count s n))=
      StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw s n hs hn) := by
    rw [lawBytes_eq]
    simp [state,BankFieldProjection.result_encode,accumulator,SourceListEncoding.encode,entries,count]
  simpa only [machine,clock,he] using hh

#print axioms outputs
end
end CurrentAdditive.V40IndexedLawLoop
