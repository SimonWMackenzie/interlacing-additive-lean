import CurrentAdditive.V40DeterministicSourcePack
import CurrentAdditive.D22PolynomialExpression

/-! A literal polynomial-time dyadic substitute for the rational-power gap
schedule. Every operation is an existing finite Boolean-stack machine.
The fixed naturals a,b are parameters of the machine, never oracle inputs.
No integer-root runtime assumption is used. -/
namespace CurrentAdditive.V43PowerSchedule
noncomputable section
open EthInapproximability.CurrentPaper PhysicalProducer V40StoredOutputPrimitives
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def numerator (a b N : Nat) : Nat := 2^((a*Nat.clog 2 N)/b)
def gap (a b N : Nat) : Nat := numerator a b N / Nat.clog 2 N

def lengthUnary : UnaryProducer where
  value w := w.length
  producer := normalizer
  result_eq _ := rfl

def logUnary : UnaryProducer := UnaryProducer.clog lengthUnary
def exponentUnary (a b : Nat) : UnaryProducer := UnaryProducer.binary .quot
  (UnaryProducer.binary .mul (UnaryProducer.constant a) logUnary)
  (UnaryProducer.constant b)

theorem exponent_value (a b : Nat) (x : List Bool) :
    (exponentUnary a b).value x = (a*Nat.clog 2 x.length)/b := rfl

/-- A polynomial bound on all intermediate exponential outputs. This
bound also covers N=0 and b=0, so totality is independent of promises. -/
theorem numerator_bound (a b N : Nat) :
    numerator a b N ≤ 2^a*(N+1)^a := by
  calc
    numerator a b N ≤ 2^(a*Nat.clog 2 N) :=
      Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
    _ = (2^(Nat.clog 2 N))^a := by rw [Nat.mul_comm a _,pow_mul]
    _ ≤ (2*(N+1))^a := Nat.pow_le_pow_left (D22PolynomialExpression.pow_clog_bound N) a
    _ = 2^a*(N+1)^a := mul_pow _ _ _

def boundedPower (E : UnaryProducer) (c d : Nat)
    (hbound : ∀ x, 2^(E.value x) ≤ c*(x.length+1)^d) : UnaryProducer where
  value x := 2^(E.value x)
  producer := {
    machine := BitMachineComposition.composition E.producer.machine MatrixUnaryPower.machine
    result := fun x => List.replicate (2^(E.value x)) true
    coefficient := E.producer.coefficient+
      2*(E.producer.coefficient*E.producer.machine.pushBound+1)+16*c
    degree := E.producer.degree+d+1
    outputs x := by
      let P := E.producer
      have hpower := MatrixUnaryPower.outputs (P.result x)
      have he : (P.result x).length = E.value x := by
        change (E.producer.result x).length = _
        rw [E.result_eq,List.length_replicate]
      rw [he] at hpower
      apply BitMachine.outputsWithin_mono _
        (BitMachineComposition.composition_outputsWithin P.machine MatrixUnaryPower.machine
          (P.outputs x) hpower)
      have hlen := BitMachine.output_length_bound P.machine (P.outputs x)
      have hbase : 1 ≤ x.length+1 := by omega
      let D := P.degree+d+1
      have hED : (x.length+1)^P.degree ≤ (x.length+1)^D :=
        Nat.pow_le_pow_right hbase (by dsimp [D]; omega)
      have haD : (x.length+1)^d ≤ (x.length+1)^D :=
        Nat.pow_le_pow_right hbase (by dsimp [D]; omega)
      have hD : 1 ≤ (x.length+1)^D := one_le_pow₀ hbase
      have hD1 : x.length+1 ≤ (x.length+1)^D := by
        simpa only [pow_one] using Nat.pow_le_pow_right hbase
          (show 1 ≤ D by dsimp [D]; omega)
      have hnum := (hbound x).trans (Nat.mul_le_mul_left c haD)
      have hclock := Nat.mul_le_mul_left P.coefficient hED
      have hout : (P.result x).length ≤
          x.length+P.coefficient*P.machine.pushBound*(x.length+1)^D := by
        calc
          _ ≤ x.length+P.coefficient*(x.length+1)^P.degree*P.machine.pushBound := hlen
          _ = x.length+P.coefficient*P.machine.pushBound*(x.length+1)^P.degree := by ring
          _ ≤ x.length+P.coefficient*P.machine.pushBound*(x.length+1)^D :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hED) _
      change P.coefficient*(x.length+1)^P.degree + 2*(P.result x).length+2+
          16*2^(E.value x) ≤
        (P.coefficient+2*(P.coefficient*P.machine.pushBound+1)+16*c)*
          (x.length+1)^D
      nlinarith }
  result_eq _ := rfl

def powerUnary (a b : Nat) : UnaryProducer := boundedPower (exponentUnary a b) (2^a) a
  (by intro x; rw [exponent_value]; exact numerator_bound a b x.length)

def unary (a b : Nat) : UnaryProducer := UnaryProducer.binary .quot (powerUnary a b) logUnary

theorem unary_value (a b : Nat) (x : List Bool) :
    (unary a b).value x = gap a b x.length := rfl

theorem unary_outputs (a b N : Nat) :
    (unary a b).producer.machine.OutputsWithin (List.replicate N true)
      (List.replicate (gap a b N) true)
      ((unary a b).producer.coefficient*(N+1)^(unary a b).producer.degree) := by
  have h := (unary a b).producer.outputs (List.replicate N true)
  rw [(unary a b).result_eq,unary_value] at h
  simpa only [List.length_replicate] using h

def formula (a b : Nat) : Producer :=
  compose V40DeterministicSourcePack.originalVariables (unary a b).producer

theorem formula_result (a b : Nat) (Φ : EncodedCNF.Formula) :
    (formula a b).result (EncodedCNF.encode Φ)=List.replicate (gap a b Φ.variables) true := by
  change (unary a b).producer.result
    (V40DeterministicSourcePack.originalVariables.result (EncodedCNF.encode Φ)) = _
  rw [V40DeterministicSourcePack.original_result,(unary a b).result_eq,unary_value]
  simp only [List.length_replicate]

theorem formula_outputs (a b : Nat) (Φ : EncodedCNF.Formula) :
    (formula a b).machine.OutputsWithin (EncodedCNF.encode Φ)
      (List.replicate (gap a b Φ.variables) true)
      ((formula a b).coefficient*((EncodedCNF.encode Φ).length+1)^(formula a b).degree) := by
  simpa only [formula_result] using (formula a b).outputs (EncodedCNF.encode Φ)

#print axioms numerator_bound
#print axioms powerUnary
#print axioms formula_outputs
end
end CurrentAdditive.V43PowerSchedule
