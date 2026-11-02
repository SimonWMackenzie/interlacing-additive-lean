import CurrentAdditive.D22PolynomialExpression

/-! A fixed list of natural comparisons is executed by physical arithmetic
and comparators, its zero/one verdicts are multiplied, then one actual bit is
written. The uniform clock constants depend only on the fixed syntax. -/
namespace D22PredicateCompiler
open D22NatExpression D22PolynomialExpression
open EthInapproximability.CurrentPaper BitMachineComposition
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def allTerm : List (Term×Term) → Term
  | [] => .const 1
  | (a,b)::rest => .binary (.old .mul) (.binary .le a b) (allTerm rest)
def pass (tests : List (Term×Term)) (n m L : ℕ) : Bool :=
  tests.all (fun ab => decide (ab.1.eval n m L≤ab.2.eval n m L))

theorem eval_allTerm (tests : List (Term×Term)) (n m L : ℕ) :
    (allTerm tests).eval n m L=(if pass tests n m L then 1 else 0) := by
  induction tests with
  | nil => rfl
  | cons ab rest ih =>
    rcases ab with ⟨a,b⟩
    change (if a.eval n m L≤b.eval n m L then 1 else 0)*(allTerm rest).eval n m L=_
    rw [ih]
    change (if a.eval n m L≤b.eval n m L then 1 else 0)*(if pass rest n m L then 1 else 0)=
      (if (decide (a.eval n m L≤b.eval n m L) && pass rest n m L) then 1 else 0)
    by_cases h : a.eval n m L≤b.eval n m L <;>
      cases hr : pass rest n m L <;> simp [hr,h]

noncomputable def machine (tests : List (Term×Term)) : BitMachine.Machine :=
  composition (allTerm tests).expr.machine D22UnaryLe.bitMachine
noncomputable def clock (tests : List (Term×Term)) (n m L : ℕ) :=
  (allTerm tests).expr.clock n m L+2*(if pass tests n m L then 1 else 0)+3
noncomputable def coefficient (tests : List (Term×Term)) := (allTerm tests).clockCoefficient+5
def degree (tests : List (Term×Term)) := (allTerm tests).clockDegree

theorem outputs (tests : List (Term×Term)) (n m L : ℕ) :
    (machine tests).OutputsWithin (input n m L) [pass tests n m L] (clock tests n m L) := by
  have ha := (allTerm tests).expr.outputs n m L
  change (allTerm tests).expr.machine.OutputsWithin (input n m L)
    (List.replicate ((allTerm tests).eval n m L) true) _ at ha
  rw [eval_allTerm] at ha
  have hc := composition_outputsWithin (allTerm tests).expr.machine D22UnaryLe.bitMachine
    ha (D22UnaryLe.bit_outputs (pass tests n m L))
  simpa only [machine,clock,List.length_replicate,Nat.add_assoc] using hc

theorem clock_polynomial (tests : List (Term×Term)) (n m L : ℕ) :
    clock tests n m L≤coefficient tests*(base n m L)^degree tests := by
  have hbase := base_pos n m L
  have hpow : 1≤(base n m L)^degree tests := one_le_pow₀ hbase
  change 1≤(base n m L)^(allTerm tests).clockDegree at hpow
  have hc := (allTerm tests).clock_polynomial n m L
  unfold clock coefficient degree
  split <;> nlinarith

theorem outputs_polynomial (tests : List (Term×Term)) (n m L : ℕ) :
    (machine tests).OutputsWithin (input n m L) [pass tests n m L]
      (coefficient tests*(base n m L)^degree tests) :=
  BitMachine.outputsWithin_mono _ (outputs tests n m L) (clock_polynomial tests n m L)

#print axioms outputs_polynomial
end
end D22PredicateCompiler
