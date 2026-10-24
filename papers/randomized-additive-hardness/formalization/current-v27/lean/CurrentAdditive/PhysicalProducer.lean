import CurrentAdditive.PhysicalConcat
import EthInapproximability.CurrentPaper.SourceListMachineWriter
import CurrentAdditive.RationalCanonicalCallback
import CurrentAdditive.FeatureCountFieldSuccessor
import CurrentAdditive.CodeDStripHeaderV2
import EthInapproximability.CurrentPaper.SourceFieldWriter
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition

namespace CurrentAdditive.PhysicalProducer
open EthInapproximability.CurrentPaper

/-- An implementation with a literal finite machine and a uniform all-input
clock. This packages actual execution proofs, not a host-language oracle. -/
structure Producer where
  machine : BitMachine.Machine
  result : List Bool → List Bool
  coefficient : Nat
  degree : Nat
  outputs : ∀ x, machine.OutputsWithin x (result x)
    (coefficient * (x.length+1)^degree)

noncomputable section

def Producer.polytime (A : Producer) : BitMachine.Polytime A.result :=
  ⟨A.machine,A.coefficient,A.degree,A.outputs⟩

def localProducer (A : Producer) : PhysicalConcat.Producer :=
  ⟨A.machine,A.result,fun x => A.coefficient*(x.length+1)^A.degree,A.outputs⟩

def concat (A B : Producer) : Producer where
  machine := PhysicalConcat.machine (A := localProducer A) (B := localProducer B)
  result := fun x => A.result x ++ B.result x
  coefficient := 10 + A.coefficient * (1+2*A.machine.pushBound) +
    B.coefficient * (1+2*B.machine.pushBound)
  degree := A.degree+B.degree+1
  outputs x := by
    have h := PhysicalConcat.outputs (A := localProducer A) (B := localProducer B) x
    apply BitMachine.outputsWithin_mono _ h
    have ha := BitMachine.output_length_bound A.machine (A.outputs x)
    have hb := BitMachine.output_length_bound B.machine (B.outputs x)
    let p := (x.length+1)^(A.degree+B.degree+1)
    have hbase : 1 ≤ x.length+1 := by omega
    have hp : 1 ≤ p := Nat.one_le_pow _ _ hbase
    have hpa : (x.length+1)^A.degree ≤ p :=
      Nat.pow_le_pow_right hbase (by omega)
    have hpb : (x.length+1)^B.degree ≤ p :=
      Nat.pow_le_pow_right hbase (by omega)
    have hpx : x.length+1 ≤ p := by
      simpa only [pow_one] using Nat.pow_le_pow_right hbase
        (show 1 ≤ A.degree+B.degree+1 by omega)
    have hma := Nat.mul_le_mul_left
      (A.coefficient*(1+2*A.machine.pushBound)) hpa
    have hmb := Nat.mul_le_mul_left
      (B.coefficient*(1+2*B.machine.pushBound)) hpb
    change 2*x.length+2+1+A.coefficient*(x.length+1)^A.degree+1+
      B.coefficient*(x.length+1)^B.degree+
      2*(B.result x).length+2+2*(A.result x).length+2+1 ≤ _
    change _ ≤ (10+A.coefficient*(1+2*A.machine.pushBound)+
      B.coefficient*(1+2*B.machine.pushBound))*p
    nlinarith

def compose (A B : Producer) : Producer where
  machine := BitMachineComposition.composition A.machine B.machine
  result := B.result ∘ A.result
  coefficient := A.coefficient + 2*(A.coefficient*A.machine.pushBound+1)+
    B.coefficient*(A.coefficient*A.machine.pushBound+1)^B.degree
  degree := (A.degree+1)*(B.degree+1)
  outputs x := by
    apply BitMachine.outputsWithin_mono _
      (BitMachineComposition.composition_outputsWithin A.machine B.machine
        (A.outputs x) (B.outputs (A.result x)))
    exact BitMachineCompositionArithmetic.composition_time_bound
      x.length A.coefficient A.degree B.coefficient B.degree
      A.machine.pushBound (A.result x).length
      (BitMachine.output_length_bound A.machine (A.outputs x))

def projection {K : Nat} (j : Fin K) : Producer where
  machine := BankFieldProjection.machine j
  result := BankFieldProjection.result j
  coefficient := 2*K+4
  degree := 1
  outputs x := by simpa only [pow_one] using BankFieldProjection.outputs j x

def field : Producer where
  machine := SourceFieldWriter.fieldMachine
  result := EncodedCommunication.field
  coefficient := 4
  degree := 1
  outputs x := by simpa only [pow_one, Nat.mul_add, Nat.mul_one] using
    SourceFieldWriter.field_outputs x

def item : Producer where
  machine := SourceListMachineWriter.framingMachine true
  result := SourceListMachineWriter.result true
  coefficient := UnaryBinaryEncoding.coefficient+7
  degree := 2
  outputs := SourceListMachineWriter.outputs true

def countSuccessor : Producer where
  machine := FeatureCountFieldSuccessor.machine
  result := FeatureCountFieldSuccessor.result
  coefficient := 6
  degree := 1
  outputs x := by simpa only [pow_one] using FeatureCountFieldSuccessor.outputsWithin x

def stripHeader : Producer where
  machine := CodeDStripHeaderV2.machine
  result := CodeDStripHeaderV2.result
  coefficient := 7
  degree := 1
  outputs x := by
    apply BitMachine.outputsWithin_mono _ (CodeDStripHeaderV2.outputs_total x)
    simp only [pow_one]
    omega

def rationalProduct : Producer where
  machine := RationalCanonicalCallback.productMachine
  result := RationalCanonicalCallback.productResult
  coefficient := Classical.choose RationalCanonicalCallback.product_outputs_all
  degree := 96
  outputs := Classical.choose_spec RationalCanonicalCallback.product_outputs_all

#print axioms concat
#print axioms compose
#print axioms rationalProduct
end
end CurrentAdditive.PhysicalProducer
