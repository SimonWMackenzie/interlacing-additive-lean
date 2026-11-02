import CurrentAdditive.V40RawSearchClock
import CurrentAdditive.OrdinaryBankFork

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CurrentAdditive.V40ContextFirstPassingSearch

open EthInapproximability.CurrentPaper V39GeneratedConstruction

noncomputable section

attribute [local irreducible] D22GeneratedTestMachine.testMachine
  D22GeneratedTestMachine.clockCoefficient D22GeneratedTestMachine.clockDegree
  V40RawFirstPassingSearch.machine

def input (context : List Bool) (floor n m : Nat) : List Bool :=
  OrdinaryBankFork.packet context (V40SearchInitialization.input floor n m)

def output (context : List Bool) (L : Nat) : List Bool :=
  OrdinaryBankFork.packet context (List.replicate L true)

def contextMachine : BitMachine.Machine := BankFieldProjection.machine (0 : Fin 2)
def answerMachine (p : SourceConstants) : BitMachine.Machine :=
  BitMachineComposition.composition (BankFieldProjection.machine (1 : Fin 2))
    (V40RawFirstPassingSearch.machine p)
def machine (p : SourceConstants) : BitMachine.Machine :=
  OrdinaryBankFork.machine contextMachine (answerMachine p)

theorem input_length (context : List Bool) (floor n m : Nat) :
    (input context floor n m).length =
      2 * context.length + 2 * (V40SearchInitialization.input floor n m).length + 2 := by
  simp [input, OrdinaryBankFork.packet, BitMachineBankCodec.encode_length, Fin.sum_univ_succ]
  ring

/-- Preserve an arbitrary graph/floor/round context while replacing the
raw count request by the physically computed selected exponent. -/
theorem outputs_polynomial (p : SourceConstants) :
    ∃ C e : Nat, ∀ context floor n m (hn : 0 < n) (hlow : n ≤ 2 * m)
      (hdegree : 2 * m ≤ p.degree * n),
      (machine p).OutputsWithin (input context floor n m)
        (output context (publicLogFrom p floor n m hn hlow hdegree))
        (C * ((input context floor n m).length + 1) ^ e) := by
  obtain ⟨Cs, es, hCs⟩ := V40RawFirstPassingSearch.outputs_polynomial p
  refine ⟨OrdinaryBankFork.coefficient contextMachine (answerMachine p) 10 (Cs + 12),
    OrdinaryBankFork.degree 1 (es + 1), ?_⟩
  intro context floor n m hn hlow hdegree
  let x := input context floor n m
  let y := V40SearchInitialization.input floor n m
  let Z := x.length + 1
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hy : y.length + 1 ≤ Z := by dsimp [Z, x, y]; rw [input_length]; omega
  have hproj0 : contextMachine.OutputsWithin x context (10 * Z) := by
    apply BitMachine.outputsWithin_mono _ ?_ (by omega : 8 * Z ≤ 10 * Z)
    simpa [contextMachine, Z, x, input, OrdinaryBankFork.packet] using
      BankFieldProjection.outputs (0 : Fin 2) x
  have hproj1 : (BankFieldProjection.machine (1 : Fin 2)).OutputsWithin x y (10 * Z) := by
    apply BitMachine.outputsWithin_mono _ ?_ (by omega : 8 * Z ≤ 10 * Z)
    simpa [Z, x, input, OrdinaryBankFork.packet, y] using BankFieldProjection.outputs (1 : Fin 2) x
  have hraw := hCs floor n m hn hlow hdegree
  have hanswer := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (1 : Fin 2)) (V40RawFirstPassingSearch.machine p) hproj1 hraw
  have hpower : Z ^ es ≤ Z ^ (es + 1) := Nat.pow_le_pow_right hZ (by omega)
  have hZpow : Z ≤ Z ^ (es + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hZ (by omega : 1 ≤ es + 1)
  have hyPow : (y.length + 1) ^ es ≤ Z ^ (es + 1) :=
    (Nat.pow_le_pow_left hy es).trans hpower
  have hmul := Nat.mul_le_mul_left Cs hyPow
  have hanswer' : (answerMachine p).OutputsWithin x
      (List.replicate (publicLogFrom p floor n m hn hlow hdegree) true)
      ((Cs + 12) * Z ^ (es + 1)) := by
    apply BitMachine.outputsWithin_mono _ hanswer
    change 10 * Z + 2 * y.length + 2 + Cs * (y.length + 1) ^ es ≤ _
    nlinarith only [hy, hZpow, hmul]
  have h := OrdinaryBankFork.outputsWithin contextMachine (answerMachine p) hproj0 hanswer'
  apply BitMachine.outputsWithin_mono _ h
  simpa only [pow_one, Z, x] using OrdinaryBankFork.clock_le_polynomial contextMachine (answerMachine p) x.length 10 1
    (Cs + 12) (es + 1)

end
end CurrentAdditive.V40ContextFirstPassingSearch
