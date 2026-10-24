import CurrentAdditive.V22UnaryFork
import CurrentAdditive.V22UnaryLeaf
import CurrentAdditive.V22UnaryMax
import EthInapproximability.CurrentPaper.ExactParameterMachineLog
import EthInapproximability.CurrentPaper.MatrixUnaryPower

/-! Syntax-directed physical arithmetic on two supplied unary inputs.
Each operation expands into the separately checked finite stack programs.
No expression is evaluated by the machine's finite control. -/
namespace V22UnaryExpression
open EthInapproximability.CurrentPaper
open BitMachineComposition
inductive Unary where | pred | clog | pow2
  deriving DecidableEq
inductive Binary where | add | mul | max
  deriving DecidableEq
def Unary.value : Unary → ℕ → ℕ
  | .pred,a => a-1 | .clog,a => Nat.clog 2 a | .pow2,a => 2^a
noncomputable def Unary.machine : Unary → BitMachine.Machine
  | .pred => ExactParameterMachineLog.predecessorMachine
  | .clog => ExactParameterMachineLog.machine
  | .pow2 => MatrixUnaryPower.machine
noncomputable def Unary.clock : Unary → ℕ → ℕ
  | .pred,_ => 1
  | .clog,a => (UnaryBinaryEncoding.coefficient+6)*(a+1)^2
  | .pow2,a => 16*2^a
theorem Unary.outputs (u : Unary) (a : ℕ) :
    u.machine.OutputsWithin (List.replicate a true)
      (List.replicate (u.value a) true) (u.clock a) := by
  cases u with
  | pred =>
      have h := ExactParameterMachineLog.predecessor_outputs (List.replicate a true)
      have he : (List.replicate a true).tail = List.replicate (a-1) true := by
        cases a <;> rfl
      simpa only [he] using h
  | clog => exact ExactParameterMachineLog.outputs a
  | pow2 => simpa only [List.length_replicate] using MatrixUnaryPower.outputs (List.replicate a true)
def Binary.value : Binary → ℕ → ℕ → ℕ
  | .add,a,b => a+b | .mul,a,b => a*b | .max,a,b => Nat.max a b
noncomputable def Binary.machine : Binary → BitMachine.Machine
  | .add => V22UnaryLeaf.machine .sum
  | .mul => MatrixUnaryArithmetic.bitMachine
  | .max => V22UnaryMax.machine
def Binary.clock : Binary → ℕ → ℕ → ℕ
  | .add,a,b => a+b+2
  | .mul,a,b => 2*(a+b+2)^2
  | .max,a,b => 2*a+b+3
theorem Binary.outputs (u : Binary) (a b : ℕ) :
    u.machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput a b)
      (List.replicate (u.value a b) true) (u.clock a b) := by
  cases u with
  | add => exact V22UnaryLeaf.outputs .sum a b
  | mul =>
      have h := MatrixUnaryArithmetic.bitMachine_outputs a b
      simpa [MatrixUnaryArithmetic.encodeInput] using h
  | max => exact V22UnaryMax.outputs a b

inductive Expr where
  | vertex | iteration | const (c : ℕ)
  | unary (op : Unary) (a : Expr)
  | binary (op : Binary) (a b : Expr)
  deriving DecidableEq
def Expr.eval : Expr → ℕ → ℕ → ℕ
  | .vertex,n,_ => n
  | .iteration,_,k => k
  | .const c,_,_ => c
  | .unary u a,n,k => u.value (a.eval n k)
  | .binary u a b,n,k => u.value (a.eval n k) (b.eval n k)
noncomputable def Expr.machine : Expr → BitMachine.Machine
  | .vertex => V22UnaryLeaf.machine .first
  | .iteration => V22UnaryLeaf.machine .second
  | .const c => V22UnaryLeaf.constant c
  | .unary u a => composition a.machine u.machine
  | .binary u a b => composition (V22UnaryFork.machine a.machine b.machine) u.machine
noncomputable def Expr.clock : Expr → ℕ → ℕ → ℕ
  | .vertex,n,k => n+k+2
  | .iteration,n,k => n+k+2
  | .const _,_,_ => 1
  | .unary u a,n,k => a.clock n k + 2*a.eval n k+2+u.clock (a.eval n k)
  | .binary u a b,n,k =>
      4*(n+k+1)+a.clock n k+b.clock n k+3*a.eval n k+3*b.eval n k+17+
      2*(a.eval n k+b.eval n k+1)+2+u.clock (a.eval n k) (b.eval n k)

theorem Expr.outputs (e : Expr) (n k : ℕ) :
    e.machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput n k)
      (List.replicate (e.eval n k) true) (e.clock n k) := by
  induction e with
  | vertex => exact V22UnaryLeaf.outputs .first n k
  | iteration => exact V22UnaryLeaf.outputs .second n k
  | const c => exact V22UnaryLeaf.constant_outputs c _
  | unary u a ih =>
      have h := composition_outputsWithin a.machine u.machine ih (u.outputs (a.eval n k))
      simpa only [Expr.machine,Expr.clock,Expr.eval,List.length_replicate] using h
  | binary u a b iha ihb =>
      have h := V22UnaryFork.outputs a.machine b.machine
        (MatrixUnaryArithmetic.encodeInput n k)
        (a.eval n k) (b.eval n k) (a.clock n k) (b.clock n k) iha ihb
      have hc := composition_outputsWithin (V22UnaryFork.machine a.machine b.machine)
        u.machine h (u.outputs (a.eval n k) (b.eval n k))
      simpa [Expr.machine,Expr.clock,Expr.eval,MatrixUnaryArithmetic.encodeInput,
        Nat.add_assoc] using hc

#print axioms Expr.outputs
end V22UnaryExpression
