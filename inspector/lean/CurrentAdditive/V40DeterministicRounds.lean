import CurrentAdditive.V40DeterministicRequest
import CurrentAdditive.V39RuntimeETHNumerics

/-! Actual finite unary arithmetic for the deterministic growing round.
The input is a native unary word, and no precomputed logarithm is supplied. -/
namespace CurrentAdditive.V40DeterministicRounds
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V40StoredOutputPrimitives PhysicalProducer AFront.Transducer
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

private def predSpec : Spec Bool where
  step _ _ _ := true
  emit seen _ := if seen then [true] else []
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le b x := by cases b <;> simp
  fin_le b := by simp

private theorem pred_true (w : List Bool) : predSpec.out true 0 w=List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change true::predSpec.out true 0 w=List.replicate (w.length+1) true
    rw [List.replicate_succ,ih]

private theorem pred_out (w : List Bool) : predSpec.out false 0 w=List.replicate (w.length-1) true := by
  cases w with
  | nil => rfl
  | cons b w => simpa only [List.length_cons,Nat.add_sub_cancel] using pred_true w

def predMachine := AFront.Transducer.machine predSpec false

def lengthUnary : UnaryProducer where
  value w := w.length
  producer := normalizer
  result_eq _ := rfl

def successor := UnaryProducer.binary .add lengthUnary (UnaryProducer.constant 1)
def logSuccessor := UnaryProducer.clog successor

def logFloor : UnaryProducer := liftUnary logSuccessor.producer predMachine
  (fun w => logSuccessor.value w-1) 3 1 (by
    intro w
    rw [logSuccessor.result_eq]
    have h:=AFront.Transducer.machine_outputs_linear predSpec false
      (List.replicate (logSuccessor.value w) true)
    rw [pred_out] at h
    simpa only [predMachine,List.length_replicate,pow_one,predSpec] using h)

theorem clog_succ_pred (n : ℕ) : Nat.clog 2 (n+1)-1=Nat.log 2 n := by
  by_cases hn : n=0
  · subst n; simp
  · have hupper : Nat.clog 2 (n+1) ≤ Nat.log 2 n+1 :=
      (Nat.clog_le_iff_le_pow (by decide)).2 (Nat.lt_pow_succ_log_self (by decide) n)
    have hlower : Nat.log 2 n < Nat.clog 2 (n+1) :=
      (Nat.lt_clog_iff_pow_lt (by decide)).2 (by
        have h:=Nat.pow_log_le_self 2 hn
        omega)
    omega

theorem logFloor_value (w : List Bool) : logFloor.value w=Nat.log 2 w.length := by
  exact clog_succ_pred w.length

def roundUnary (amp : ℕ) := UnaryProducer.binary .quot logFloor
  (UnaryProducer.constant (2*V39RuntimeETHNumerics.amplificationLog amp))

theorem round_value (amp : ℕ) (w : List Bool) :
    (roundUnary amp).value w=V39RuntimeETHNumerics.rounds amp w.length := by
  change logFloor.value w / (2*V39RuntimeETHNumerics.amplificationLog amp)=_
  rw [logFloor_value]
  rfl

theorem outputs (amp N : ℕ) :
    (roundUnary amp).producer.machine.OutputsWithin (List.replicate N true)
      (List.replicate (V39RuntimeETHNumerics.rounds amp N) true)
      ((roundUnary amp).producer.coefficient*(N+1)^(roundUnary amp).producer.degree) := by
  have h:=(roundUnary amp).producer.outputs (List.replicate N true)
  rw [(roundUnary amp).result_eq,round_value] at h
  simpa only [List.length_replicate] using h

#print axioms round_value
#print axioms outputs
end
end CurrentAdditive.V40DeterministicRounds
