import CurrentAdditive.D22UnaryDivision
import CurrentAdditive.D22UnaryLe
import CurrentAdditive.V22ExpressionClock
import EthInapproximability.CurrentPaper.BankFieldProjection

/-! Three physical unary input fields n,m,L. Each fixed expression expands
to literal finite Boolean-stack programs; no expression evaluation is an
instruction in the machine's finite control. -/
namespace D22NatExpression
open EthInapproximability.CurrentPaper BitMachineComposition
open V22UnaryExpression
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384

def values (n m L : ℕ) : Fin 3 → ℕ := ![n,m,L]
def input (n m L : ℕ) : List Bool :=
  BitMachineBankCodec.encode (fun j => List.replicate (values n m L j) true)
def inputLength (n m L : ℕ) := (input n m L).length

inductive Binary where | old (b : V22UnaryExpression.Binary) | quot | le
  deriving DecidableEq
def Binary.value : Binary → ℕ → ℕ → ℕ
  | .old b,a,c => b.value a c
  | .quot,a,c => a/c
  | .le,a,c => if a≤c then 1 else 0
noncomputable def Binary.machine : Binary → BitMachine.Machine
  | .old b => b.machine
  | .quot => D22UnaryDivision.machine
  | .le => D22UnaryLe.machine
def Binary.clock : Binary → ℕ → ℕ → ℕ
  | .old b,a,c => b.clock a c
  | .quot,a,c => 9*a+4*c+7
  | .le,a,c => 3*(a+c+3)
theorem Binary.outputs (b : Binary) (a c : ℕ) :
    b.machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput a c)
      (List.replicate (b.value a c) true) (b.clock a c) := by
  cases b with
  | old b => exact b.outputs a c
  | quot => exact D22UnaryDivision.outputs a c
  | le => exact D22UnaryLe.outputs a c

inductive Expr where
  | var (j : Fin 3) | const (c : ℕ)
  | unary (u : V22UnaryExpression.Unary) (a : Expr)
  | binary (b : Binary) (a c : Expr)
  deriving DecidableEq

def Expr.eval : Expr → ℕ → ℕ → ℕ → ℕ
  | .var j,n,m,L => values n m L j
  | .const c,_,_,_ => c
  | .unary u a,n,m,L => u.value (a.eval n m L)
  | .binary b a c,n,m,L => b.value (a.eval n m L) (c.eval n m L)
noncomputable def Expr.machine : Expr → BitMachine.Machine
  | .var j => BankFieldProjection.machine j
  | .const c => V22UnaryLeaf.constant c
  | .unary u a => composition a.machine u.machine
  | .binary b a c => composition (V22UnaryFork.machine a.machine c.machine) b.machine
noncomputable def Expr.clock : Expr → ℕ → ℕ → ℕ → ℕ
  | .var _,n,m,L => 10*(inputLength n m L+1)
  | .const _,_,_,_ => 1
  | .unary u a,n,m,L => a.clock n m L+2*a.eval n m L+2+u.clock (a.eval n m L)
  | .binary b a c,n,m,L =>
      4*inputLength n m L+a.clock n m L+c.clock n m L+3*a.eval n m L+3*c.eval n m L+17+
      2*(a.eval n m L+c.eval n m L+1)+2+b.clock (a.eval n m L) (c.eval n m L)

theorem Expr.outputs (e : Expr) (n m L : ℕ) :
    e.machine.OutputsWithin (input n m L)
      (List.replicate (e.eval n m L) true) (e.clock n m L) := by
  induction e with
  | var j =>
      simpa only [Expr.machine,Expr.eval,Expr.clock,inputLength,input,
        BankFieldProjection.result_encode] using BankFieldProjection.outputs j (input n m L)
  | const c => exact V22UnaryLeaf.constant_outputs c _
  | unary u a ih =>
      have h := composition_outputsWithin a.machine u.machine ih (u.outputs (a.eval n m L))
      simpa only [Expr.machine,Expr.clock,Expr.eval,List.length_replicate] using h
  | binary b a c iha ihc =>
      have h := V22UnaryFork.outputs a.machine c.machine (input n m L)
        (a.eval n m L) (c.eval n m L) (a.clock n m L) (c.clock n m L) iha ihc
      have hc := composition_outputsWithin (V22UnaryFork.machine a.machine c.machine)
        b.machine h (b.outputs (a.eval n m L) (c.eval n m L))
      simpa [Expr.machine,Expr.clock,Expr.eval,inputLength,MatrixUnaryArithmetic.encodeInput,
        Nat.add_assoc] using hc

def Expr.peak : Expr → ℕ → ℕ → ℕ → ℕ
  | .var j,n,m,L => values n m L j
  | .const c,_,_,_ => c
  | .unary u a,n,m,L => max (u.value (a.eval n m L)) (a.peak n m L)
  | .binary b a c,n,m,L => max (b.value (a.eval n m L) (c.eval n m L))
      (max (a.peak n m L) (c.peak n m L))
noncomputable def Expr.coefficient : Expr → ℕ
  | .var _ => 10 | .const _ => 1
  | .unary _ a => a.coefficient+V22UnaryExpression.primitiveCoefficient+4
  | .binary _ a c => a.coefficient+c.coefficient+60
theorem Expr.eval_le_peak (e : Expr) (n m L : ℕ) : e.eval n m L≤e.peak n m L := by
  cases e <;> simp [Expr.eval,Expr.peak]
theorem Binary.clock_le (b : Binary) (a c M : ℕ) (ha : a≤M) (hc : c≤M) :
    b.clock a c≤20*(M+1)^2 := by
  cases b with
  | old b => exact (V22UnaryExpression.Binary.clock_le b a c M ha hc).trans (by nlinarith)
  | quot => simp only [Binary.clock]; nlinarith
  | le => simp only [Binary.clock]; nlinarith

theorem Expr.clock_le_of_peak (e : Expr) (n m L M : ℕ) (hpeak : e.peak n m L≤M) :
    e.clock n m L≤e.coefficient*(inputLength n m L+M+2)^2 := by
  let W := inputLength n m L+M+2
  have hW : 1≤W := by dsimp [W]; omega
  have hWM : M+1≤W := by dsimp [W]; omega
  have hMW : M≤W := by omega
  have hW2 : W≤W^2 := by nlinarith
  have hM2 : (M+1)^2≤W^2 := Nat.pow_le_pow_left hWM 2
  induction e with
  | var j => change 10*(inputLength n m L+1)≤10*W^2; dsimp [W] at *; nlinarith
  | const c => change 1≤1*W^2; nlinarith
  | unary u a ih =>
      change max (u.value (a.eval n m L)) (a.peak n m L)≤M at hpeak
      obtain ⟨hv,hp⟩ := max_le_iff.mp hpeak
      have ha := (a.eval_le_peak n m L).trans hp
      have hc := ih hp
      change a.clock n m L≤a.coefficient*W^2 at hc
      have hu := (u.clock_le (a.eval n m L) M ha hv).trans (Nat.mul_le_mul_left _ hM2)
      change a.clock n m L+2*a.eval n m L+2+u.clock (a.eval n m L)≤
        (a.coefficient+V22UnaryExpression.primitiveCoefficient+4)*W^2
      nlinarith
  | binary b a c iha ihc =>
      change max (b.value (a.eval n m L) (c.eval n m L)) (max (a.peak n m L) (c.peak n m L))≤M at hpeak
      obtain ⟨_,hab⟩ := max_le_iff.mp hpeak
      obtain ⟨hpa,hpc⟩ := max_le_iff.mp hab
      have ha := (a.eval_le_peak n m L).trans hpa
      have hc := (c.eval_le_peak n m L).trans hpc
      have hca := iha hpa
      have hcc := ihc hpc
      change a.clock n m L≤a.coefficient*W^2 at hca
      change c.clock n m L≤c.coefficient*W^2 at hcc
      have hu := (b.clock_le (a.eval n m L) (c.eval n m L) M ha hc).trans
        (Nat.mul_le_mul_left 20 hM2)
      have hi : inputLength n m L≤W := by dsimp [W]; omega
      change 4*inputLength n m L+a.clock n m L+c.clock n m L+3*a.eval n m L+3*c.eval n m L+17+
        2*(a.eval n m L+c.eval n m L+1)+2+b.clock (a.eval n m L) (c.eval n m L)≤
        (a.coefficient+c.coefficient+60)*W^2
      nlinarith

#print axioms Expr.outputs
#print axioms Expr.clock_le_of_peak
end D22NatExpression
