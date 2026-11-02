import CurrentAdditive.PhysicalProducer
import CurrentAdditive.V22UnaryExpression
import CurrentAdditive.D22UnaryDivision
import Paper2.AFrontTransducer

namespace CurrentAdditive.V40StoredOutputPrimitives
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding EncodedCommunication PhysicalProducer AFront.Transducer

def normalizeSpec : Spec Unit where
  step _ _ _ := ()
  emit _ _ := [true]
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le _ _ := by simp
  fin_le _ := by simp

theorem normalize_out (w : List Bool) : normalizeSpec.out () 0 w=List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      change true::normalizeSpec.out () 0 w=List.replicate (w.length+1) true
      rw [List.replicate_succ,ih]

def normalizer : Producer where
  machine := AFront.Transducer.machine normalizeSpec ()
  result := fun w => List.replicate w.length true
  coefficient := 3
  degree := 1
  outputs w := by simpa only [normalize_out,pow_one] using AFront.Transducer.machine_outputs_linear normalizeSpec () w

inductive HeaderPhase | tag | bit | done deriving DecidableEq,Fintype

def headerSpec : Spec HeaderPhase where
  step s b _ := match s with
    | .tag => if b then .bit else .done
    | .bit => .tag
    | .done => .done
  emit s b := match s with | .done => [] | _ => [b]
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> simp
  fin_le _ := by simp

def header : Producer where
  machine := AFront.Transducer.machine headerSpec .tag
  result := headerSpec.out .tag 0
  coefficient := 3
  degree := 1
  outputs w := by simpa only [pow_one] using AFront.Transducer.machine_outputs_linear headerSpec .tag w

theorem header_done (rest : List Bool) : headerSpec.out .done 0 rest=[] := by
  induction rest with
  | nil => rfl
  | cons b rest ih => rw [Spec.out_cons]; simpa [headerSpec,Spec.next] using ih

theorem header_field (bits rest : List Bool) : header.result (field bits++rest)=field bits := by
  change headerSpec.out .tag 0 (field bits++rest)=field bits
  induction bits with
  | nil =>
      change false::headerSpec.out .done 0 rest=[false]
      rw [header_done]
  | cons b bits ih =>
      change true::b::headerSpec.out .tag 0 (EncodedCommunication.field bits++rest)=
        true::b::EncodedCommunication.field bits
      rw [ih]
def falseProgram : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit :=
  fun _ => .push 1 (fun _ => false) .halt

def separator : Producer where
  machine := ofFinite (0 : Fin 2) 1 () () falseProgram
  result := fun _ => [false]
  coefficient := 1
  degree := 0
  outputs w := by
    apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () falseProgram w [false] 1 1 (by simp)
    · rfl
    · rfl

structure UnaryProducer where
  value : List Bool → Nat
  producer : Producer
  result_eq : ∀ x,producer.result x=List.replicate (value x) true

/-- Restricted composition is instantiated below only with actual native
arithmetic on its physically produced canonical unary words. -/
def liftUnary (A : Producer) (M : BitMachine.Machine) (value : List Bool → Nat)
    (c d : Nat) (h : ∀ x,M.OutputsWithin (A.result x) (List.replicate (value x) true)
      (c*((A.result x).length+1)^d)) : UnaryProducer where
  value := value
  producer := {
    machine := BitMachineComposition.composition A.machine M
    result := fun x => List.replicate (value x) true
    coefficient := A.coefficient+2*(A.coefficient*A.machine.pushBound+1)+
      c*(A.coefficient*A.machine.pushBound+1)^d
    degree := (A.degree+1)*(d+1)
    outputs x := by
      apply BitMachine.outputsWithin_mono _ (BitMachineComposition.composition_outputsWithin _ _ (A.outputs x) (h x))
      exact BitMachineCompositionArithmetic.composition_time_bound x.length A.coefficient A.degree c d
        A.machine.pushBound (A.result x).length (BitMachine.output_length_bound A.machine (A.outputs x)) }
  result_eq _ := rfl

namespace UnaryProducer

def input {N : Nat} (j : Fin N) : UnaryProducer where
  value x := (BankFieldProjection.result j x).length
  producer := compose (projection j) normalizer
  result_eq _ := rfl

def constant (n : Nat) : UnaryProducer where
  value _ := n
  producer := {
    machine := V22UnaryLeaf.constant n
    result := fun _ => List.replicate n true
    coefficient := 1
    degree := 0
    outputs := fun x => V22UnaryLeaf.constant_outputs n x }
  result_eq _ := rfl

def clog (A : UnaryProducer) : UnaryProducer := liftUnary A.producer
  ExactParameterMachineLog.machine (fun x => Nat.clog 2 (A.value x))
  (UnaryBinaryEncoding.coefficient+6) 2 (by
    intro x
    rw [A.result_eq]
    simpa only [List.length_replicate] using ExactParameterMachineLog.outputs (A.value x))

inductive Binary | add | mul | quot deriving DecidableEq

def Binary.value : Binary → Nat → Nat → Nat
  | .add,a,b => a+b | .mul,a,b => a*b | .quot,a,b => a/b

def Binary.machine : Binary → BitMachine.Machine
  | .add => V22UnaryLeaf.machine .sum
  | .mul => MatrixUnaryArithmetic.bitMachine
  | .quot => D22UnaryDivision.machine

theorem Binary.outputs (op : Binary) (a b : Nat) :
    op.machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput a b)
      (List.replicate (op.value a b) true) (20*(a+b+2)^2) := by
  cases op with
  | add =>
      apply BitMachine.outputsWithin_mono _ (V22UnaryLeaf.outputs .sum a b)
      nlinarith [sq_nonneg (a+b+2 : Int)]
  | mul =>
      apply BitMachine.outputsWithin_mono _ (MatrixUnaryArithmetic.bitMachine_outputs a b)
      simp only [MatrixUnaryArithmetic.encodeInput,List.length_append,List.length_cons,List.length_replicate]
      nlinarith
  | quot =>
      apply BitMachine.outputsWithin_mono _ (D22UnaryDivision.outputs a b)
      nlinarith [sq_nonneg (a+b+2 : Int)]

def fork (A B : UnaryProducer) : Producer := concat A.producer (concat separator B.producer)

theorem fork_result (A B : UnaryProducer) (x : List Bool) :
    (fork A B).result x=MatrixUnaryArithmetic.encodeInput (A.value x) (B.value x) := by
  simp only [fork,concat,separator,A.result_eq,B.result_eq,MatrixUnaryArithmetic.encodeInput]
  rfl

def binary (op : Binary) (A B : UnaryProducer) : UnaryProducer :=
  liftUnary (fork A B) op.machine (fun x => op.value (A.value x) (B.value x)) 20 2 (by
    intro x
    rw [fork_result]
    simpa only [MatrixUnaryArithmetic.encodeInput,List.length_append,List.length_cons,List.length_replicate]
      using op.outputs (A.value x) (B.value x))

end UnaryProducer
#print axioms header_field
#print axioms normalizer
#print axioms UnaryProducer.binary
end
end CurrentAdditive.V40StoredOutputPrimitives
