import CurrentV43.PowerMachine
import CurrentAdditive.V22UnaryExpression

/-! Physical construction of `(n+2)^(C*(K+1))` from two encoded unary
inputs. `C` is a fixed program parameter; `n` and `K` are data on the input
stack. The result does not assume an input-polynomial producer, since the
output itself may have superpolynomial length. -/
namespace CurrentV43.PowerMachine
noncomputable section
open EthInapproximability.CurrentPaper V22UnaryExpression BitMachineComposition

def resourceBaseExpr : Expr := .binary .add .vertex (.const 2)
def resourceExponentExpr (C : ℕ) : Expr :=
  .binary .mul (.const C) (.binary .add .iteration (.const 1))

@[simp] theorem resourceBase_eval (n K : ℕ) : resourceBaseExpr.eval n K=n+2 := rfl
@[simp] theorem resourceExponent_eval (C n K : ℕ) :
    (resourceExponentExpr C).eval n K=C*(K+1) := rfl

def resourceSeparatedMachine (C : ℕ) : BitMachine.Machine :=
  composition (V22UnaryFork.machine resourceBaseExpr.machine (resourceExponentExpr C).machine)
    separatedMachine
def resourceSeparatedClock (C n K : ℕ) :=
  4*(n+K+1)+resourceBaseExpr.clock n K+(resourceExponentExpr C).clock n K+
    6*(n+2)+6*(C*(K+1))+24+MatrixWeightedPower.powerBound (n+2) (C*(K+1))

theorem resourceSeparated_outputs (C n K : ℕ) :
    (resourceSeparatedMachine C).OutputsWithin (MatrixUnaryArithmetic.encodeInput n K)
      (List.replicate ((n+2)^(C*(K+1))) true) (resourceSeparatedClock C n K) := by
  have hp := V22UnaryFork.outputs resourceBaseExpr.machine (resourceExponentExpr C).machine
    (MatrixUnaryArithmetic.encodeInput n K) (n+2) (C*(K+1))
    (resourceBaseExpr.clock n K) ((resourceExponentExpr C).clock n K)
    (resourceBaseExpr.outputs n K) ((resourceExponentExpr C).outputs n K)
  have h := composition_outputsWithin _ separatedMachine hp
    (separated_outputs (n+2) (C*(K+1)))
  have heq : 4*(MatrixUnaryArithmetic.encodeInput n K).length+
      resourceBaseExpr.clock n K+(resourceExponentExpr C).clock n K+3*(n+2)+3*(C*(K+1))+17+
      2*(MatrixUnaryArithmetic.encodeInput (n+2) (C*(K+1))).length+2+
      separatedClock (n+2) (C*(K+1)) = resourceSeparatedClock C n K := by
    simp only [resourceSeparatedClock,separatedClock,MatrixUnaryArithmetic.encodeInput,
      List.length_append,List.length_cons,List.length_replicate]
    ring
  rw [heq] at h
  exact h

def resourceMachine (C : ℕ) : BitMachine.Machine :=
  composition unpair (resourceSeparatedMachine C)
def resourceClock (C n K : ℕ) :=
  unpairClock n K+2*(n+K+1)+2+resourceSeparatedClock C n K

theorem resource_outputs (C n K : ℕ) :
    (resourceMachine C).OutputsWithin (input n K)
      (List.replicate ((n+2)^(C*(K+1))) true) (resourceClock C n K) := by
  have h := composition_outputsWithin unpair (resourceSeparatedMachine C)
    (unpair_outputs n K) (resourceSeparated_outputs C n K)
  simpa only [resourceClock,MatrixUnaryArithmetic.encodeInput,List.length_append,
    List.length_cons,List.length_replicate] using h

theorem resourceClock_eq (C n K : ℕ) : resourceClock C n K =
    75*n+74*K+5*C+6*(C*(K+1))+226+2*(C+K+3)^2+
      MatrixWeightedPower.powerBound (n+2) (C*(K+1)) := by
  simp only [resourceClock,resourceSeparatedClock,unpairClock,input_length,
    resourceBaseExpr,resourceExponentExpr,Expr.clock,Expr.eval,Binary.value,Binary.clock]
  ring

theorem resourceClock_le (C n K : ℕ) :
    resourceClock C n K≤512*(n+K+C+(n+2)^(C*(K+1))+1)^3 := by
  let p := (n+2)^(C*(K+1))
  let e := C*(K+1)
  let W := n+K+C+p+1
  have hW : 1≤W := by dsimp [W]; omega
  have hn : n≤W := by dsimp [W]; omega
  have hK : K≤W := by dsimp [W]; omega
  have hC : C≤W := by dsimp [W]; omega
  have hp : p+1≤2*W := by dsimp [W]; omega
  have hb : n+2≤2*W := by dsimp [W]; omega
  have he : e≤p := (Nat.lt_two_pow_self (n:=e)).le.trans
    (Nat.pow_le_pow_left (show 2≤n+2 by omega) e)
  have he' : e+1≤2*W := by dsimp [W]; omega
  have hW2 : W≤W^2 := by nlinarith
  have hW3 : W≤W^3 := by nlinarith [Nat.mul_le_mul_right W hW2]
  have hW23 : W^2≤W^3 := by nlinarith [Nat.mul_le_mul_right W hW2]
  have hprod : (p+1)*(n+2)≤4*W^2 := by
    have h := Nat.mul_le_mul hp hb
    nlinarith
  have hinner : 3*(p+1)*(n+2)+5*(p+1)+7≤29*W^2 := by nlinarith
  have hpower : MatrixWeightedPower.powerBound (n+2) e≤58*W^3 := by
    calc
      MatrixWeightedPower.powerBound (n+2) e≤
          (e+1)*(3*(p+1)*(n+2)+5*(p+1)+7) :=
        MatrixWeightedPower.powerBound_polynomial (n+2) e
      _ ≤ (2*W)*(29*W^2) := Nat.mul_le_mul he' hinner
      _ = 58*W^3 := by ring
  have hquad : (C+K+3)^2≤9*W^2 := by
    have h := Nat.pow_le_pow_left (show C+K+3≤3*W by dsimp [W]; omega) 2
    nlinarith
  have hlin : 75*n+74*K+5*C+6*e+226≤386*W := by
    have hep : e≤W := by dsimp [W]; omega
    nlinarith
  change resourceClock C n K≤512*W^3
  rw [resourceClock_eq]
  change 75*n+74*K+5*C+6*e+226+2*(C+K+3)^2+
    MatrixWeightedPower.powerBound (n+2) e≤512*W^3
  nlinarith

theorem resourceClock_le_power (C n K : ℕ) (hC : 1≤C) :
    resourceClock C n K≤(n+2)^((3*C+16)*(K+1)) := by
  let b := n+2
  let e := C*(K+1)
  let p := b^e
  have hb : 2≤b := by dsimp [b]; omega
  have hb0 : 0<b := by omega
  have he1 : 1≤e := by dsimp [e]; nlinarith
  have hbase : b≤p := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb0 he1
  have he : e≤p := (Nat.lt_two_pow_self (n:=e)).le.trans (Nat.pow_le_pow_left hb e)
  have hCK : C≤e ∧ K≤e := by dsimp [e]; constructor <;> nlinarith
  have hn : n≤p := by dsimp [b] at hbase; omega
  have hp : 1≤p := by omega
  have hsum : n+K+C+p+1≤5*p := by omega
  have hcoeff : 64000≤b^16 := by
    calc
      64000 ≤ 2^16 := by norm_num
      _ ≤ b^16 := Nat.pow_le_pow_left hb 16
  calc
    resourceClock C n K≤512*(n+K+C+p+1)^3 := resourceClock_le C n K
    _ ≤ 512*(5*p)^3 := Nat.mul_le_mul_left 512 (Nat.pow_le_pow_left hsum 3)
    _ = 64000*b^(3*e) := by dsimp [p]; rw [mul_pow,←pow_mul]; ring
    _ ≤ b^16*b^(3*e) := Nat.mul_le_mul_right _ hcoeff
    _ = b^(3*e+16) := by rw [←pow_add]; congr 1; omega
    _ ≤ b^((3*C+16)*(K+1)) := Nat.pow_le_pow_right hb0 (by dsimp [e]; nlinarith)

theorem resource_outputs_power (C n K : ℕ) (hC : 1≤C) :
    (resourceMachine C).OutputsWithin (input n K)
      (List.replicate ((n+2)^(C*(K+1))) true) ((n+2)^((3*C+16)*(K+1))) :=
  BitMachine.outputsWithin_mono _ (resource_outputs C n K) (resourceClock_le_power C n K hC)

#print axioms resource_outputs
#print axioms resourceClock_le
#print axioms resourceClock_le_power
#print axioms resource_outputs_power
end
end CurrentV43.PowerMachine
