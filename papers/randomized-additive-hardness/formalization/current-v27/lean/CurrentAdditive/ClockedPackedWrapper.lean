import CurrentAdditive.ClockedFlagGate

/-! A fixed bounded TM2 simulation followed by a physical timeout gate.
The budget is a unary prefix of the ordinary input, so constructing that
prefix from an unframed input remains a separate, charged operation. -/

namespace CurrentAdditive.ClockedPackedWrapper

open EthInapproximability.CurrentPaper
open BitMachine BoundedBitMachine FlaggedBoundedBitMachine

noncomputable def machine (M : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition
    (FlaggedBoundedBitMachine.machine M) ClockedFlagGate.machine

noncomputable def result (M : BitMachine.Machine) (input : List Bool) : List Bool :=
  let report := FlaggedBoundedBitMachine.report M input
  if report.headD false then report.tail else []

theorem gate_report (M : BitMachine.Machine) (input : List Bool) :
    ClockedFlagGate.machine.OutputsWithin
      (FlaggedBoundedBitMachine.report M input) (result M input)
      ((FlaggedBoundedBitMachine.report M input).length+1) := by
  let flag := FlaggedBoundedBitMachine.completionFlag M
    ((BoundedBitMachine.machine M).run (2*(input.length+1))
      ((BoundedBitMachine.machine M).init input)).var
  let payload := BoundedBitMachine.result M input
  change ClockedFlagGate.machine.OutputsWithin (flag :: payload)
    (if flag then payload else []) ((flag :: payload).length+1)
  cases flag
  · exact BitMachine.outputsWithin_mono _ (ClockedFlagGate.outputs_false payload)
      (by simp)
  · exact BitMachine.outputsWithin_mono _ (ClockedFlagGate.outputs_true payload)
      (by simp)

/-- Every bitstring terminates with the source output if its bounded run
halted, or with the literal empty default otherwise. -/
theorem outputs_all (M : BitMachine.Machine) (input : List Bool) :
    (machine M).OutputsWithin input (result M input)
      ((2*(input.length+1)+1) +
        2*(FlaggedBoundedBitMachine.report M input).length+2+
        ((FlaggedBoundedBitMachine.report M input).length+1)) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (FlaggedBoundedBitMachine.outputs_all M input)
    (gate_report M input)

noncomputable def clockCoefficient (M : BitMachine.Machine) : ℕ :=
  20 * ((FlaggedBoundedBitMachine.machine M).pushBound+1)

theorem outputs_all_linear (M : BitMachine.Machine) (input : List Bool) :
    (machine M).OutputsWithin input (result M input)
      (clockCoefficient M * (input.length+1)) := by
  have h := outputs_all M input
  have hlen := BitMachine.output_length_bound
    (FlaggedBoundedBitMachine.machine M)
    (FlaggedBoundedBitMachine.outputs_all M input)
  apply BitMachine.outputsWithin_mono _ h
  dsimp [clockCoefficient]
  have hp : (FlaggedBoundedBitMachine.machine M).pushBound ≤
      (FlaggedBoundedBitMachine.machine M).pushBound * (input.length+1) := by
    have hh := Nat.mul_le_mul_left
      (FlaggedBoundedBitMachine.machine M).pushBound
      (show 1 ≤ input.length+1 by omega)
    simpa using hh
  nlinarith

theorem result_packed (M : BitMachine.Machine) (n : ℕ)
    (bits : List Bool) :
    result M (BoundedBitMachine.packed n bits) =
      if (M.run n (M.init bits)).l = none then
        (M.run n (M.init bits)).stk M.output else [] := by
  unfold result
  rw [FlaggedBoundedBitMachine.report_packed]
  by_cases h : (M.run n (M.init bits)).l = none <;> simp [h]

/-- A proved source run within the supplied unary prefix survives exactly;
the physical wrapper still halts on every packed or malformed input. -/
theorem outputs_packed_success (M : BitMachine.Machine)
    (n : ℕ) (bits output : List Bool)
    (h : M.OutputsWithin bits output n) :
    (machine M).OutputsWithin (BoundedBitMachine.packed n bits) output
      (clockCoefficient M * ((BoundedBitMachine.packed n bits).length+1)) := by
  have hh := BitMachine.outputsWithin_at_bound M h
  have hr := outputs_all_linear M (BoundedBitMachine.packed n bits)
  rw [result_packed, hh.1, if_pos rfl, hh.2] at hr
  exact hr

#print axioms outputs_all_linear
#print axioms outputs_packed_success

end CurrentAdditive.ClockedPackedWrapper
