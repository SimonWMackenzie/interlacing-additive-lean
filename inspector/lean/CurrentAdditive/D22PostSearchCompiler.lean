import CurrentAdditive.D22PacketWordExpression

namespace D22PostSearchCompiler
open EthInapproximability.CurrentPaper
open CurrentAdditive D22PacketPrimitives D22PacketWordExpression D22PostSearchPacket
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def join {q : ℕ} : List (WExpr q) → WExpr q
  | [] => .empty | a::rest => .append a (join rest)
theorem join_result {q : ℕ} (l : List (WExpr q)) (a b c : Fin q) (x : List Bool) :
    ((join l).producer a b c).result x=l.flatMap (fun e => (e.producer a b c).result x) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [join,WExpr.producer,D22PacketPrimitives.append,List.flatMap_cons,ih]

def fieldExpr (i : Fin 12) : WExpr 5 := .frame (
  if h : i.val<5 then .proj ⟨i.val,h⟩
  else .scalar (terms ⟨i.val-5,by omega⟩))
def expression : WExpr 5 := join (List.ofFn fieldExpr)
noncomputable def machine : BitMachine.Machine := (expression.producer 1 2 3).machine
noncomputable def clockCoefficient := expression.timeCoefficient
def clockDegree := expression.timeDegree
def sizeCoefficient := expression.sizeCoefficient
def sizeDegree := expression.sizeDegree

theorem field_result (graph : List Bool) (n m L K : ℕ) (i : Fin 12) :
    ((fieldExpr i).producer 1 2 3).result (input graph n m L K)=
      EncodedCommunication.field (words graph n m L K i) := by
  fin_cases i <;>
    simp [fieldExpr,WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project,
      D22PacketPrimitives.scalar,input,rawWords,words,BankFieldProjection.result_encode,
      terms_eval,values]

theorem result_eq (graph : List Bool) (n m L K : ℕ) :
    (expression.producer 1 2 3).result (input graph n m L K)=output graph n m L K := by
  rw [expression,join_result,output,BitMachineBankCodec.encode_eq_list]
  have he : (fun i => ((fieldExpr i).producer 1 2 3).result (input graph n m L K))=
      (fun i => EncodedCommunication.field (words graph n m L K i)) := by
    funext i
    exact field_result graph n m L K i
  have hmap := congrArg List.ofFn he
  have hmap' : (List.ofFn fieldExpr).map (fun e => (e.producer 1 2 3).result (input graph n m L K))=
      (List.ofFn (words graph n m L K)).map EncodedCommunication.field := by
    simpa only [List.map_ofFn] using hmap
  simpa only [List.flatMap] using congrArg List.flatten hmap'

/-- Actual post-search computation of every generated scalar. The unchanged
graph and supplied n,m,L,K survive as the first five output fields. -/
theorem outputs (graph : List Bool) (n m L K : ℕ) :
    machine.OutputsWithin (input graph n m L K) (output graph n m L K)
      (clockCoefficient*(2^L+(input graph n m L K).length+1)^clockDegree) := by
  have h := expression.outputs_polynomial (1 : Fin 5) 2 3 (input graph n m L K) n m L
    (by simp [input,rawWords]) (by simp [input,rawWords]) (by simp [input,rawWords])
  simpa only [machine,clockCoefficient,clockDegree,D22PacketWordExpression.measure,result_eq] using h

theorem output_length (graph : List Bool) (n m L K : ℕ) :
    (output graph n m L K).length ≤ sizeCoefficient*(2^L+(input graph n m L K).length+1)^sizeDegree := by
  have h := (expression.bounds (1 : Fin 5) 2 3 (input graph n m L K) n m L
    (by simp [input,rawWords]) (by simp [input,rawWords]) (by simp [input,rawWords])).1
  simpa only [sizeCoefficient,sizeDegree,D22PacketWordExpression.measure,result_eq] using h

theorem raw_preserved (graph : List Bool) (n m L K : ℕ) (i : Fin 5) :
    BankFieldProjection.result (⟨i.val,by omega⟩ : Fin 12) (output graph n m L K)=rawWords graph n m L K i := by
  fin_cases i <;> simp [output,words,rawWords]

#print axioms outputs
#print axioms output_length
#print axioms raw_preserved
end
end D22PostSearchCompiler
