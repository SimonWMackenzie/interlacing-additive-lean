import CurrentAdditive.V40UniformLawMachine

/-! The bound below is a literal polynomial expression in the unary size.
The expression compiler here only proves elementary arithmetic inequalities;
it is not used as a machine or an execution certificate. -/
namespace CurrentAdditive.V40ClockPolynomial
inductive Expr where
  | constant (c : Nat) | input | add (a b : Expr) | mul (a b : Expr) | pow (a : Expr) (d : Nat)

noncomputable def Expr.eval (e : Expr) (n : Nat) : Nat :=
  Expr.rec (motive:=fun _ => Nat) (fun c => c) n
    (fun _ _ a b => a+b) (fun _ _ a b => a*b) (fun _ d a => a^d) e

theorem Expr.bound (e : Expr) : ∃ C d : Nat, ∀ n, e.eval n≤C*(n+1)^d := by
  induction e with
  | constant c => exact ⟨c,0,by simp [Expr.eval]⟩
  | input => exact ⟨1,1,by intro n;simp [Expr.eval]⟩
  | add a b ia ib =>
      obtain ⟨A,r,ha⟩ := ia
      obtain ⟨B,s,hb⟩ := ib
      refine ⟨A+B,r+s,?_⟩
      intro n
      have h1 : 1≤n+1 := by omega
      have hpa := Nat.pow_le_pow_right h1 (show r≤r+s by omega)
      have hpb := Nat.pow_le_pow_right h1 (show s≤r+s by omega)
      calc
        _ ≤ A*(n+1)^r+B*(n+1)^s := Nat.add_le_add (ha n) (hb n)
        _ ≤ A*(n+1)^(r+s)+B*(n+1)^(r+s) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hpa) (Nat.mul_le_mul_left _ hpb)
        _ = _ := by ring
  | mul a b ia ib =>
      obtain ⟨A,r,ha⟩ := ia
      obtain ⟨B,s,hb⟩ := ib
      refine ⟨A*B,r+s,?_⟩
      intro n
      calc
        _ ≤ (A*(n+1)^r)*(B*(n+1)^s) := Nat.mul_le_mul (ha n) (hb n)
        _ = _ := by rw [pow_add];ring
  | pow a d ia =>
      obtain ⟨A,r,ha⟩ := ia
      refine ⟨A^d,r*d,?_⟩
      intro n
      calc
        _ ≤ (A*(n+1)^r)^d := Nat.pow_le_pow_left (ha n) _
        _ = _ := by rw [mul_pow,←pow_mul]
end CurrentAdditive.V40ClockPolynomial

namespace CurrentAdditive.V40UniformLaw
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper V40UniformLawLoop V40ClockPolynomial

def sizePolynomial : Expr := .mul (.constant 100) (.pow (.add .input (.constant 1)) 2)
def timePolynomial : Expr := .mul (.constant body.coefficient)
  (.pow (.add sizePolynomial (.constant 1)) body.degree)
def roundPolynomial : Expr := .add
  (.add timePolynomial (.mul (.constant (body.machine.stackCount+2))
    (.add sizePolynomial (.mul timePolynomial (.constant body.machine.pushBound)))))
  (.constant (body.machine.stackCount+4))
def packetPolynomial : Expr := .add
  (.mul (.constant 2) (.add sizePolynomial .input)) (.constant 2)
def boundPolynomial : Expr :=
  .add (.add
    (.add (.mul (.constant withFuel.coefficient) (.pow (.add .input (.constant 1)) withFuel.degree))
      (.mul (.constant 7) packetPolynomial))
    (.mul .input roundPolynomial))
    (.add (.mul (.constant 12) sizePolynomial) (.constant 21))

theorem clock_le_expression (n : Nat) (hn : 0<n) : clock n≤boundPolynomial.eval n := by
  have hs := state_length n n hn le_rfl
  have h0 := state_length n 0 hn (by omega)
  have hp : (prepared n).length≤2*(sizeCap n+n)+2 := by
    have he : (prepared n).length=2*((state n 0).length+n)+2 := by
      simp only [prepared,WeightedIterationDriver.input,WeightedIterationLoader.packet,
        BitMachineBankCodec.encode_length]
      simp [Fin.sum_univ_succ]
    rw [he]
    omega
  have he : roundPolynomial.eval n=
      BitMachineIteration.roundBound body.machine (sizeCap n) (timeCap n) := by
    simp only [roundPolynomial,timePolynomial,sizePolynomial,Expr.eval,
      sizeCap,timeCap,BitMachineIteration.roundBound]
    omega
  simp only [boundPolynomial,packetPolynomial,sizePolynomial,Expr.eval]
  change clock n≤withFuel.coefficient*(n+1)^withFuel.degree+
    7*(2*(sizeCap n+n)+2)+n*(roundPolynomial.eval n)+(12*sizeCap n+21)
  rw [he]
  change clock n≤withFuel.coefficient*(n+1)^withFuel.degree+
    7*(2*(sizeCap n+n)+2)+n*BitMachineIteration.roundBound body.machine (sizeCap n) (timeCap n)+
    (12*sizeCap n+21)
  dsimp only [clock,middleClock,initializationClock,loopBound,prepared] at *
  omega

theorem clock_polynomial : ∃ C d : Nat, ∀ n, 0<n → clock n≤C*(n+1)^d := by
  obtain ⟨C,d,h⟩ := boundPolynomial.bound
  exact ⟨C,d,fun n hn => (clock_le_expression n hn).trans (h n)⟩

theorem outputs_polynomial : ∃ C d : Nat, ∀ n, ∀ hn : 0<n,
    machine.OutputsWithin (List.replicate n true)
      (StoredWeightedState.lawBytes (@Paper2.PositiveRationalLaw.uniform (Fin n) _
        (by exact ⟨⟨0,hn⟩⟩))) (C*(n+1)^d) := by
  obtain ⟨C,d,h⟩ := clock_polynomial
  refine ⟨C,d,?_⟩
  intro n hn
  letI : NeZero n := ⟨by omega⟩
  exact BitMachine.outputsWithin_mono _ (outputs n) (h n hn)

#print axioms clock_polynomial
#print axioms outputs_polynomial
end
end CurrentAdditive.V40UniformLaw
