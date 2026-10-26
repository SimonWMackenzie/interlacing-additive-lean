import CurrentAdditive.D22StepContextAssembly
import CurrentAdditive.V42Schedule

/-! Actual scalar compiler for the fixed v42 generated recipe. The input
contains graph bytes and unary n,m,k,K. It computes every public width,
the activity repetition, the item count, and the seed logarithm 4*k.
Neither a source table nor a machine run is supplied as input. -/
namespace CurrentAdditive.V42RuntimePacket
open EthInapproximability.CurrentPaper
open D22PolynomialExpression D22GeneratedTerms D22PacketWordExpression
open D22PostSearchCompiler V42Schedule
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def rawWords (graph : List Bool) (n m k K : ℕ) : Fin 5 → List Bool :=
  ![graph,List.replicate n true,List.replicate m true,List.replicate k true,List.replicate K true]
def input (graph : List Bool) (n m k K : ℕ) := BitMachineBankCodec.encode (rawWords graph n m k K)
def repetition (k m : ℕ) := q₂ k (4*k) / V38Schedule.pow2Ceil (4*s k*m)
def ni (n k : ℕ) := 4*s k*(n+(s k-3))
def words (graph : List Bool) (n m k K : ℕ) : Fin 12 → List Bool :=
  ![graph,List.replicate n true,List.replicate m true,List.replicate (4*k) true,List.replicate K true,
    List.replicate (q₁ k) true,List.replicate (q₂ k (4*k)) true,List.replicate (s k) true,
    List.replicate (w k) true,List.replicate (Q k) true,List.replicate (repetition k m) true,
    List.replicate (ni n k) true]
def output (graph : List Bool) (n m k K : ℕ) := BitMachineBankCodec.encode (words graph n m k K)
def withSourceWords (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) : Fin 14 → List Bool :=
  ![graph,List.replicate n true,List.replicate m true,List.replicate (4*k) true,List.replicate K true,
    List.replicate (q₁ k) true,List.replicate (q₂ k (4*k)) true,List.replicate (s k) true,
    List.replicate (w k) true,List.replicate (Q k) true,List.replicate (repetition k m) true,
    List.replicate (ni n k) true,law,activity]
def withSource (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) :=
  BitMachineBankCodec.encode (withSourceWords graph n m k K law activity)
def context (k : ℕ) (law activity : List Bool) := BitMachineBankCodec.encode
  ![List.replicate (q₁ k) true,List.replicate (q₂ k (4*k)) true,List.replicate (s k) true,
    List.replicate (w k) true,List.replicate (Q k) true,law,activity]
def envelope (k K : ℕ) (law activity : List Bool) := BitMachineBankCodec.encode
  ![List.replicate (4*k) true,List.replicate K true,context k law activity]

def sTerm : Term := .dyadic 1 0 1
def q1Term : Term := .pred (.pred sTerm)
def q2Term : Term := .dyadic 6 0 1
def wTerm : Term := .dyadic 8 0 1
def QTerm : Term := .dyadic 24 0 1
def repetitionTerm : Term := quot q2Term (.powCeil (mul (mul (.const 4) sTerm) (.var 1)))
def niTerm : Term := mul (mul (.const 4) sTerm) (add (.var 0) (.pred (.pred (.pred sTerm))))
def terms : Fin 7 → Term := ![q1Term,q2Term,sTerm,wTerm,QTerm,repetitionTerm,niTerm]
def values (n m k : ℕ) : Fin 7 → ℕ := ![q₁ k,q₂ k (4*k),s k,w k,Q k,repetition k m,ni n k]

theorem eval_sTerm (n m k : ℕ) : sTerm.eval n m k=V42Schedule.s k := by simp [sTerm,V42Schedule.s]
theorem eval_q2Term (n m k : ℕ) : q2Term.eval n m k=q₂ k (4*k) := by
  simp [q2Term,q₂]; congr 1; omega
theorem terms_eval (n m k : ℕ) (i : Fin 7) : (terms i).eval n m k=values n m k i := by
  fin_cases i <;> simp [terms,values,q1Term,wTerm,QTerm,repetitionTerm,niTerm,
    eval_sTerm,eval_q2Term,q₁,V42Schedule.w,V42Schedule.Q,repetition,ni,D22NatExpression.values]
  all_goals omega

def fieldExpr (i : Fin 12) : WExpr 5 := .frame (
  if h : i.val<5 then
    if i.val=3 then .scalar (mul (.const 4) (.var 2)) else .proj ⟨i.val,h⟩
  else .scalar (terms ⟨i.val-5,by omega⟩))
def expression : WExpr 5 := join (List.ofFn fieldExpr)
def machine := (expression.producer 1 2 3).machine
def coefficient := expression.timeCoefficient
def degree := expression.timeDegree
def sizeCoefficient := expression.sizeCoefficient
def sizeDegree := expression.sizeDegree

theorem field_result (graph : List Bool) (n m k K : ℕ) (i : Fin 12) :
    ((fieldExpr i).producer 1 2 3).result (input graph n m k K)=
      EncodedCommunication.field (words graph n m k K i) := by
  fin_cases i <;> simp [fieldExpr,WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project,
    D22PacketPrimitives.scalar,input,rawWords,words,BankFieldProjection.result_encode,
    terms_eval,values,D22NatExpression.values]

theorem result_eq (graph : List Bool) (n m k K : ℕ) :
    (expression.producer 1 2 3).result (input graph n m k K)=output graph n m k K := by
  rw [expression,join_result,output,BitMachineBankCodec.encode_eq_list]
  have he : (fun i => ((fieldExpr i).producer 1 2 3).result (input graph n m k K))=
      (fun i => EncodedCommunication.field (words graph n m k K i)) := by
    funext i
    exact field_result graph n m k K i
  have hmap := congrArg List.ofFn he
  have hmap' : (List.ofFn fieldExpr).map (fun e => (e.producer 1 2 3).result (input graph n m k K))=
      (List.ofFn (words graph n m k K)).map EncodedCommunication.field := by
    simpa only [List.map_ofFn] using hmap
  simpa only [List.flatMap] using congrArg List.flatten hmap'

theorem outputs (graph : List Bool) (n m k K : ℕ) :
    machine.OutputsWithin (input graph n m k K) (output graph n m k K)
      (coefficient*(2^k+(input graph n m k K).length+1)^degree) := by
  have h := expression.outputs_polynomial (1 : Fin 5) 2 3 (input graph n m k K) n m k
    (by simp [input,rawWords]) (by simp [input,rawWords]) (by simp [input,rawWords])
  simpa only [machine,coefficient,degree,D22PacketWordExpression.measure,result_eq] using h

theorem output_length (graph : List Bool) (n m k K : ℕ) :
    (output graph n m k K).length ≤ sizeCoefficient*(2^k+(input graph n m k K).length+1)^sizeDegree := by
  have h := (expression.bounds (1 : Fin 5) 2 3 (input graph n m k K) n m k
    (by simp [input,rawWords]) (by simp [input,rawWords]) (by simp [input,rawWords])).1
  simpa only [sizeCoefficient,sizeDegree,D22PacketWordExpression.measure,result_eq] using h

#print axioms outputs
#print axioms output_length
end
end CurrentAdditive.V42RuntimePacket
