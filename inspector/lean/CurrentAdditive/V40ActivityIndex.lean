import CurrentAdditive.V40IndexedLawLoop
import CurrentAdditive.D22UnaryDivision

/-! Physical item-index decoding in the original numbered order. The
division program's actual remainder stack supplies the local item value;
an arithmetic zero/one flag supplies the item kind. -/
namespace CurrentAdditive.V40ActivityIndex
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open D22PolynomialExpression D22NatExpression V40IndexedLawLoop V40SourceContextSpec
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

def remainderMachine : BitMachine.Machine :=
  ofFinite (6:Fin 7) 3 D22UnaryDivision.start (false,false) D22UnaryDivision.program
theorem remainder_outputs (a b : Nat) :
    remainderMachine.OutputsWithin (MatrixUnaryArithmetic.encodeInput a b)
      (List.replicate (a%b) true) (9*a+4*b+7) := by
  obtain ⟨t,ht,he⟩:=D22UnaryDivision.divide_run a b
  obtain ⟨u,hu,hr⟩:=BitMachineRawSequence.runs D22UnaryDivision.parse D22UnaryDivision.divide .first .start
    false false false false
    (D22UnaryDivision.cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk
    (D22UnaryDivision.parsed a b) (D22UnaryDivision.divided a b) (a+b+2) t
    (D22UnaryDivision.parse_run a b) he
  change ((advance D22UnaryDivision.program)^[u])
    (⟨some D22UnaryDivision.start,(false,false),
      (D22UnaryDivision.cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk⟩ :
      TM2.Cfg (fun _ : Fin 7=>Bool) _ _)=⟨none,(false,false),D22UnaryDivision.divided a b⟩ at hr
  have hi : rawInit (6:Fin 7) D22UnaryDivision.start (false,false) (MatrixUnaryArithmetic.encodeInput a b)=
      (⟨some D22UnaryDivision.start,(false,false),
        (D22UnaryDivision.cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 7=>Bool) _ _) := by
    unfold rawInit D22UnaryDivision.cfg
    congr 1
    funext j
    fin_cases j <;> simp
  apply outputsWithin_of_raw_run (6:Fin 7) 3 D22UnaryDivision.start (false,false) D22UnaryDivision.program
    (MatrixUnaryArithmetic.encodeInput a b) (List.replicate (a%b) true) u _
    (by have htime:=MatrixUnaryDivision.totalTime_bound a b; omega)
  · rw [hi]
    exact congrArg (fun c=>c.l) hr
  · rw [hi,hr]
    change D22UnaryDivision.divided a b (D22UnaryDivision.divSlots 3)=_
    rw [D22UnaryDivision.divided,BitMachineStackEmbedding.bank_at]
    rfl

def kindTerm : Term:=le (add lower (.const 1)) upper
def shiftedTerm : Term:=add (.var 0) (mul aux kindTerm)
def group (s n i : Nat):=i/blockSize s n
def kind (s n i : Nat):=auxiliaryFlag s n i
def value (s n i : Nat):=(i+auxiliaryCount s*kind s n i)%blockSize s n
theorem lower_eval (i n s : Nat) : lower.eval i n s=group s n i := by
  simp [lower,quot,divisor,add,aux,Term.eval,Term.expr,Expr.eval,Binary.value,
    V22UnaryExpression.Binary.value,V22UnaryExpression.Unary.value,values,group,blockSize,auxiliaryCount]
  congr 2 <;> omega
theorem kindTerm_eval (i n s : Nat) : kindTerm.eval i n s=kind s n i := by
  have h : s-1-1-1=s-3:=by omega
  simp [kindTerm,le,add,lower,quot,upper,divisor,aux,Term.eval,Term.expr,Expr.eval,Binary.value,
    V22UnaryExpression.Binary.value,V22UnaryExpression.Unary.value,values,kind,auxiliaryFlag,blockSize,auxiliaryCount,h]
theorem shiftedTerm_eval (i n s : Nat) : shiftedTerm.eval i n s=i+auxiliaryCount s*kind s n i := by
  change i+(s-1-1-1)*kindTerm.eval i n s=_
  rw [kindTerm_eval]
  have h : s-1-1-1=s-3:=by omega
  rw [h]
  rfl
theorem divisor_eval (i n s : Nat) : divisor.eval i n s=blockSize s n := by
  change n+(s-1-1-1)=_
  unfold blockSize auxiliaryCount
  omega

def forkMachine:=V22UnaryFork.machine shiftedTerm.expr.machine divisor.expr.machine
def forkClock (i n s : Nat):=4*(D22NatExpression.input i n s).length+shiftedTerm.expr.clock i n s+
  divisor.expr.clock i n s+3*shiftedTerm.eval i n s+3*divisor.eval i n s+17
def machine:=BitMachineComposition.composition forkMachine remainderMachine
def clock (i n s : Nat):=forkClock i n s+2*(MatrixUnaryArithmetic.encodeInput
  (shiftedTerm.eval i n s) (divisor.eval i n s)).length+2+
  9*shiftedTerm.eval i n s+4*divisor.eval i n s+7
theorem outputs (i n s : Nat) : machine.OutputsWithin (D22NatExpression.input i n s)
    (List.replicate (value s n i) true) (clock i n s) := by
  have hf:=V22UnaryFork.outputs shiftedTerm.expr.machine divisor.expr.machine (D22NatExpression.input i n s)
    (shiftedTerm.eval i n s) (divisor.eval i n s) _ _ (shiftedTerm.expr.outputs i n s) (divisor.expr.outputs i n s)
  have hh:=BitMachineComposition.composition_outputsWithin forkMachine remainderMachine hf
    (remainder_outputs (shiftedTerm.eval i n s) (divisor.eval i n s))
  simpa only [machine,clock,forkClock,shiftedTerm_eval,divisor_eval,value,Nat.add_assoc] using hh

theorem vertex (s n : Nat) (hn : 0<n) (g : Fin (4*s)) (v : Fin n) :
    group s n (LiteralEdgeEncoder.itemNumber s n (g,.inl v)).val=g.val ∧
    kind s n (LiteralEdgeEncoder.itemNumber s n (g,.inl v)).val=0 ∧
    value s n (LiteralEdgeEncoder.itemNumber s n (g,.inl v)).val=v.val := by
  obtain ⟨h0,h1⟩:=quot_vertex s n hn g v
  have hk : kind s n (LiteralEdgeEncoder.itemNumber s n (g,.inl v)).val=0 := by
    unfold kind auxiliaryFlag
    rw [h0,h1]
    simp
  refine ⟨h0,hk,?_⟩
  rw [value,hk]
  simp only [Nat.mul_zero,Nat.add_zero,LiteralEdgeEncoder.itemNumber_vertex]
  change (v.val+blockSize s n*g.val)%blockSize s n=v.val
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by unfold blockSize; omega)]

theorem auxiliary (s n : Nat) (hn : 0<n) (g : Fin (4*s)) (a : Fin (s-3)) :
    group s n (LiteralEdgeEncoder.itemNumber s n (g,.inr a)).val=g.val ∧
    kind s n (LiteralEdgeEncoder.itemNumber s n (g,.inr a)).val=1 ∧
    value s n (LiteralEdgeEncoder.itemNumber s n (g,.inr a)).val=a.val := by
  obtain ⟨h0,h1⟩:=quot_auxiliary s n hn g a
  have hk : kind s n (LiteralEdgeEncoder.itemNumber s n (g,.inr a)).val=1 := by
    unfold kind auxiliaryFlag
    rw [h0,h1]
    simp
  refine ⟨h0,hk,?_⟩
  rw [value,hk]
  simp only [Nat.mul_one,LiteralEdgeEncoder.itemNumber_auxiliary]
  rw [show n+a.val+(n+(s-3))*g.val+auxiliaryCount s=a.val+blockSize s n*(g.val+1) by
    unfold blockSize auxiliaryCount
    ring]
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by unfold blockSize auxiliaryCount; omega)]

#print axioms outputs
#print axioms vertex
#print axioms auxiliary
end
end CurrentAdditive.V40ActivityIndex
