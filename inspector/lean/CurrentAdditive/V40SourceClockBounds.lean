import CurrentAdditive.V40SourceLocal
import CurrentAdditive.D22ArithmeticGrowth

/-! Pure polynomial bounds for the metadata of existing physical source
components. Every coefficient and degree is fixed before the input word.
The actual source-table loops and their execution proofs remain with the
source-context owner. -/
namespace CurrentAdditive.V40SourceClockBounds
noncomputable section
open EthInapproximability.CurrentPaper
open D22PacketPrimitives D22PolynomialExpression
open V40SourceLocal
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

def Envelope (A : V40SourceLocal.Producer) (C d : Nat) : Prop :=
  ∀ x, A.clock x+(A.result x).length ≤ C*(x.length+1)^d

def HasPolynomialEnvelope (A : V40SourceLocal.Producer) : Prop :=
  ∃ C d, Envelope A C d

theorem project_envelope {q : Nat} (j : Fin q) :
    Envelope (project j) (2*q+5) 1 := by
  intro x
  have h:=BankFieldProjection.result_length j x
  change (2*q+4)*(x.length+1)+(BankFieldProjection.result j x).length ≤ _
  simp only [pow_one]
  nlinarith

theorem frame_envelope {A : V40SourceLocal.Producer} {C d : Nat} (h : Envelope A C d) :
    Envelope (frame A) (8*C+7) d := by
  intro x
  have hx:=h x
  have hp : 1 ≤ (x.length+1)^d:=one_le_pow₀ (by omega)
  change A.clock x+6*(A.result x).length+6+(EncodedCommunication.field (A.result x)).length ≤ _
  rw [EncodedCommunication.field_length]
  nlinarith

theorem append_envelope {A B : V40SourceLocal.Producer} {CA CB dA dB : Nat}
    (ha : Envelope A CA dA) (hb : Envelope B CB dB) :
    Envelope (append A B) (3*CA+3*CB+11) (dA+dB+1) := by
  intro x
  let P:=(x.length+1)^(dA+dB+1)
  have hx : 1 ≤ x.length+1:=by omega
  have hp : 1 ≤ P:=one_le_pow₀ hx
  have hxp : x.length+1 ≤ P:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by omega : 1 ≤ dA+dB+1)
  have ha' := (ha x).trans (Nat.mul_le_mul_left CA
    (Nat.pow_le_pow_right hx (by omega : dA ≤ dA+dB+1)))
  have hb' := (hb x).trans (Nat.mul_le_mul_left CB
    (Nat.pow_le_pow_right hx (by omega : dB ≤ dA+dB+1)))
  change A.clock x+(A.result x).length ≤ CA*P at ha'
  change B.clock x+(B.result x).length ≤ CB*P at hb'
  change _ ≤ (3*CA+3*CB+11)*P
  simp only [append,PhysicalConcatLocal.clock,List.length_append]
  nlinarith

theorem compose_envelope {A B : V40SourceLocal.Producer} {CA CB dA dB : Nat}
    (ha : Envelope A CA dA) (hb : Envelope B CB dB) :
    Envelope (V40SourceLocal.compose A B)
      (2*CA+2+CB*(CA+1)^dB) (dA+dA*dB) := by
  intro x
  let X:=x.length+1
  let P:=X^(dA+dA*dB)
  have hX : 1 ≤ X:=by dsimp [X]; omega
  have hpow : 1 ≤ X^dA:=one_le_pow₀ hX
  have hp : 1 ≤ P:=one_le_pow₀ hX
  have ha0:=ha x
  change A.clock x+(A.result x).length ≤ CA*X^dA at ha0
  have hlen : (A.result x).length+1 ≤ (CA+1)*X^dA:=by nlinarith
  have hb0:=hb (A.result x)
  have hb1 : B.clock (A.result x)+(B.result (A.result x)).length ≤
      (CB*(CA+1)^dB)*X^(dA*dB) := by
    calc
      _ ≤ CB*((A.result x).length+1)^dB:=hb0
      _ ≤ CB*((CA+1)*X^dA)^dB:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
      _=(CB*(CA+1)^dB)*X^(dA*dB):=by rw [mul_pow,←pow_mul]; ring
  have hpa : X^dA ≤ P:=Nat.pow_le_pow_right hX (by omega)
  have hpb : X^(dA*dB) ≤ P:=Nat.pow_le_pow_right hX (by omega)
  have haa:=Nat.mul_le_mul_left CA hpa
  have hbb:=Nat.mul_le_mul_left (CB*(CA+1)^dB) hpb
  change A.clock x+2*(A.result x).length+2+B.clock (A.result x)+
    (B.result (A.result x)).length ≤ (2*CA+2+CB*(CA+1)^dB)*P
  nlinarith

theorem constant_envelope (w : List Bool) :
    Envelope (V40SourceLocal.constant w) (w.length+1) 0 := by
  intro x
  simp [V40SourceLocal.constant,physical,V40SeedProducer.constant,Nat.add_comm]

theorem physical_envelope (A : PhysicalProducer.Producer) :
    Envelope (physical A) (A.coefficient*(A.machine.pushBound+1)+1) (A.degree+1) := by
  intro x
  have hlen:=BitMachine.output_length_bound A.machine (A.outputs x)
  have hx : 1 ≤ x.length+1:=by omega
  have hp : x.length+1 ≤ (x.length+1)^(A.degree+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by omega : 1 ≤ A.degree+1)
  have hd : (x.length+1)^A.degree ≤ (x.length+1)^(A.degree+1):=
    Nat.pow_le_pow_right hx (by omega)
  have hc:=Nat.mul_le_mul_left (A.coefficient*(A.machine.pushBound+1)) hd
  change A.coefficient*(x.length+1)^A.degree+(A.result x).length ≤ _
  nlinarith

def serialiseCoefficient : {k : Nat} → (Fin k → Nat) → Nat
  | 0,_ => 1
  | k+1,C => 3*(8*C 0+7)+3*serialiseCoefficient (fun i : Fin k=>C i.succ)+11

def serialiseDegree : {k : Nat} → (Fin k → Nat) → Nat
  | 0,_ => 0
  | k+1,d => d 0+serialiseDegree (fun i : Fin k=>d i.succ)+1

theorem serialise_envelope {k : Nat} (A : Fin k → V40SourceLocal.Producer) (C d : Fin k → Nat)
    (h : ∀ i, Envelope (A i) (C i) (d i)) :
    Envelope (serialise A) (serialiseCoefficient C) (serialiseDegree d) := by
  induction k with
  | zero => simpa only [serialise,serialiseCoefficient,serialiseDegree,List.length_nil,Nat.zero_add]
      using constant_envelope []
  | succ k ih =>
    exact append_envelope (frame_envelope (h 0))
      (ih (fun i=>A i.succ) (fun i=>C i.succ) (fun i=>d i.succ) (fun i=>h i.succ))

noncomputable def scalarCoefficient (q : Nat) (t : Term) :=
  100*(q+1)+20+t.clockCoefficient*3^t.clockDegree+t.coefficient

def scalarDegree (t : Term) := t.clockDegree+t.degree+1

theorem scalar_envelope {q : Nat} (a b c : Fin q) (t : Term) (ht : D22ArithmeticGrowth.Pure t) :
    Envelope (scalar a b c t) (scalarCoefficient q t) (scalarDegree t) := by
  intro x
  let n:=(BankFieldProjection.result a x).length
  let m:=(BankFieldProjection.result b x).length
  let L:=(BankFieldProjection.result c x).length
  let X:=x.length+1
  let P:=X^(scalarDegree t)
  have hX : 1 ≤ X:=by dsimp [X]; omega
  have hn : n ≤ x.length:=BankFieldProjection.result_length a x
  have hm : m ≤ x.length:=BankFieldProjection.result_length b x
  have hL : L ≤ x.length:=BankFieldProjection.result_length c x
  have hsum : n+m+L+1 ≤ 3*X:=by dsimp [X]; omega
  have hclock:=D22ArithmeticGrowth.clock_bound t ht n m L
  have hclock' : t.expr.clock n m L ≤ (t.clockCoefficient*3^t.clockDegree)*X^t.clockDegree := by
    calc
      _ ≤ t.clockCoefficient*(n+m+L+1)^t.clockDegree:=hclock
      _ ≤ t.clockCoefficient*(3*X)^t.clockDegree:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum _)
      _=(t.clockCoefficient*3^t.clockDegree)*X^t.clockDegree:=by rw [mul_pow]; ring
  have hsize:= (t.expr.eval_le_peak n m L).trans
    (D22ArithmeticGrowth.peak_bound t ht n m L X hX (by dsimp [X]; omega)
      (by dsimp [X]; omega) (by dsimp [X]; omega))
  have hfr:=framer_clock a b c x
  have hfl:=framer_length a b c x
  have hpc : X^t.clockDegree ≤ P:=Nat.pow_le_pow_right hX (by unfold scalarDegree; omega)
  have hps : X^t.degree ≤ P:=Nat.pow_le_pow_right hX (by unfold scalarDegree; omega)
  have hpx : X ≤ P:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (by unfold scalarDegree; omega : 1 ≤ scalarDegree t)
  have hP : 1 ≤ P:=one_le_pow₀ hX
  have hc:=Nat.mul_le_mul_left (t.clockCoefficient*3^t.clockDegree) hpc
  have hs:=Nat.mul_le_mul_left t.coefficient hps
  have hf:=Nat.mul_le_mul_left (100*(q+1)+20) hpx
  change (framer a b c).clock x+2*((framer a b c).result x).length+2+t.expr.clock n m L+
    (List.replicate (t.eval n m L) true).length ≤ scalarCoefficient q t*P
  rw [List.length_replicate]
  change t.eval n m L ≤ t.coefficient*X^t.degree at hsize
  unfold scalarCoefficient
  change (framer a b c).clock x ≤ 100*(q+1)*X at hfr
  change ((framer a b c).result x).length ≤ 9*X at hfl
  nlinarith

/-- Metadata for the literal configuration after a fixed polynomial number
of actual steps. There is no halting or desired-output premise. -/
def finiteRun (M : BitMachine.Machine) (C d : Nat) : V40SourceLocal.Producer :=
  ⟨M,fun x=>(M.run (C*(x.length+1)^d) (M.init x)).stk M.output,
    fun x=>C*(x.length+1)^d⟩

theorem finite_run_envelope (M : BitMachine.Machine) (C d : Nat) :
    Envelope (finiteRun M C d) (C*(M.pushBound+1)+1) (d+1) := by
  intro x
  have hrun:=BitMachine.run_length M (M.init x) M.output (C*(x.length+1)^d)
  have hi : ((M.init x).stk M.output).length ≤ x.length:=by
    simp only [BitMachine.Machine.init]
    split <;> simp
  have hlen:=hrun.trans (Nat.add_le_add_right hi _)
  have hx : 1 ≤ x.length+1:=by omega
  have hp : x.length+1 ≤ (x.length+1)^(d+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by omega : 1 ≤ d+1)
  have hd : (x.length+1)^d ≤ (x.length+1)^(d+1):=Nat.pow_le_pow_right hx (by omega)
  have hc:=Nat.mul_le_mul_left (C*(M.pushBound+1)) hd
  change C*(x.length+1)^d+((M.run (C*(x.length+1)^d) (M.init x)).stk M.output).length ≤ _
  nlinarith

theorem unary_field_envelope :
    Envelope unaryField ((UnaryBinaryEncoding.coefficient+10)*(unaryField.machine.pushBound+1)+1) 3 := by
  intro x
  have hlen:=BitMachine.output_length_bound unaryField.machine (unaryField_outputs x)
  change (unaryField.result x).length ≤ x.length+
    ((UnaryBinaryEncoding.coefficient+10)*(x.length+1)^2)*unaryField.machine.pushBound at hlen
  have hx : 1 ≤ x.length+1:=by omega
  have hp : x.length+1 ≤ (x.length+1)^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by omega : 1 ≤ 3)
  have hd : (x.length+1)^2 ≤ (x.length+1)^3:=Nat.pow_le_pow_right hx (by omega)
  have hc:=Nat.mul_le_mul_left ((UnaryBinaryEncoding.coefficient+10)*(unaryField.machine.pushBound+1)) hd
  change (UnaryBinaryEncoding.coefficient+10)*(x.length+1)^2+(unaryField.result x).length ≤ _
  nlinarith

theorem project_polynomial {q : Nat} (j : Fin q) : HasPolynomialEnvelope (project j) :=
  ⟨_,_,project_envelope j⟩

theorem frame_polynomial {A : V40SourceLocal.Producer} (h : HasPolynomialEnvelope A) :
    HasPolynomialEnvelope (frame A) := by
  obtain ⟨C,d,h⟩:=h
  exact ⟨_,_,frame_envelope h⟩

theorem append_polynomial {A B : V40SourceLocal.Producer}
    (ha : HasPolynomialEnvelope A) (hb : HasPolynomialEnvelope B) :
    HasPolynomialEnvelope (append A B) := by
  obtain ⟨CA,dA,ha⟩:=ha
  obtain ⟨CB,dB,hb⟩:=hb
  exact ⟨_,_,append_envelope ha hb⟩

theorem compose_polynomial {A B : V40SourceLocal.Producer}
    (ha : HasPolynomialEnvelope A) (hb : HasPolynomialEnvelope B) :
    HasPolynomialEnvelope (V40SourceLocal.compose A B) := by
  obtain ⟨CA,dA,ha⟩:=ha
  obtain ⟨CB,dB,hb⟩:=hb
  exact ⟨_,_,compose_envelope ha hb⟩

theorem constant_polynomial (w : List Bool) : HasPolynomialEnvelope (V40SourceLocal.constant w) :=
  ⟨_,_,constant_envelope w⟩

theorem physical_polynomial (A : PhysicalProducer.Producer) : HasPolynomialEnvelope (physical A) :=
  ⟨_,_,physical_envelope A⟩

theorem scalar_polynomial {q : Nat} (a b c : Fin q) (t : Term) (ht : D22ArithmeticGrowth.Pure t) :
    HasPolynomialEnvelope (scalar a b c t) := ⟨_,_,scalar_envelope a b c t ht⟩

theorem serialise_polynomial {k : Nat} (A : Fin k → V40SourceLocal.Producer)
    (h : ∀ i, HasPolynomialEnvelope (A i)) : HasPolynomialEnvelope (serialise A) := by
  induction k with
  | zero => exact constant_polynomial []
  | succ k ih =>
    exact append_polynomial (frame_polynomial (h 0))
      (ih (fun i=>A i.succ) (fun i=>h i.succ))

theorem finite_run_polynomial (M : BitMachine.Machine) (C d : Nat) :
    HasPolynomialEnvelope (finiteRun M C d) := ⟨_,_,finite_run_envelope M C d⟩

theorem unary_field_polynomial : HasPolynomialEnvelope unaryField :=
  ⟨_,_,unary_field_envelope⟩

#print axioms scalar_envelope
#print axioms serialise_envelope
#print axioms physical_envelope
end
end CurrentAdditive.V40SourceClockBounds
