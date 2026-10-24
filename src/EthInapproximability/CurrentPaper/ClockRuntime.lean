import EthInapproximability.CurrentPaper.ClockPacketState
import EthInapproximability.CurrentPaper.ClockStepSemantics
import EthInapproximability.CurrentPaper.ClockIterationDriver
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.CutoffBitMachine

/-!
# Polynomial-time execution of the bounded prefix clock

Source: frozen v8 `05-iteration.tex`, `eq:paper-slow-clock`. For every fixed
source machine, the actual driver takes a physical word of length n and
returns the encoded state after n bounded probes. Its counter is exactly
the consecutive-success prefix length. No termination or runtime assumption
on the source machine is needed: each probe is physically clocked.
-/

namespace EthInapproximability.CurrentPaper.ClockRuntime

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable (M : BitMachine.Machine)

def state (input : List Bool) (j : ℕ) : SlowClockPrefixLoop.State :=
  SlowClockPrefixLoop.stateAt (SlowClock.succeeds (CutoffBitMachine.clock M) input.length) j

def packetAt (input : List Bool) (j : ℕ) : List Bool :=
  ClockPacketState.packet M [(state M input j).active] input (state M input j).accepted.bits

theorem packetAt_zero (input : List Bool) :
    packetAt M input 0 = ClockIterationInput.packet (ClockStepMachine.tempCount M) input :=
  ClockPacketState.packet_initial M input

theorem packetAt_step (input : List Bool) (j : ℕ) :
    ClockStepEncoded.result M (packetAt M input j) = packetAt M input (j+1) := by
  rw [packetAt,ClockPacketState.result_packet]
  change BitMachineBankCodec.encode (ClockStepEncoded.toBank M
      (ClockStepMachine.result M [(SlowClockPrefixLoop.stateAt _ j).active] input
        (SlowClockPrefixLoop.stateAt _ j).accepted.bits)) = _
  rw [ClockStepSemantics.stateAt_step]
  rfl

def lengthBound (n : ℕ) : ℕ := 4*n + ClockStepEncoded.width M + 2

theorem packetAt_length (input : List Bool) (j : ℕ) (hj : j ≤ input.length) :
    (packetAt M input j).length ≤ lengthBound M input.length := by
  rw [packetAt,ClockPacketState.packet_length]
  have hc := ClockStepSemantics.stateAt_counter_length M input j
  change (state M input j).accepted.bits.length ≤ j at hc
  simp only [List.length_cons,List.length_nil]
  unfold lengthBound
  omega

noncomputable def machine : BitMachine.Machine :=
  ClockIterationDriver.machine (ClockStepEncoded.machine M) (ClockStepMachine.tempCount M)

def output (input : List Bool) : List Bool := packetAt M input input.length

def time (n : ℕ) : ℕ :=
  2*n + ClockStepMachine.tempCount M + 7 + n * BitMachineIteration.roundBound
    (ClockStepEncoded.machine M) (lengthBound M n)
    (ClockStepEncoded.timeConstant M*(lengthBound M n+1)^2)

theorem outputs (input : List Bool) :
    (machine M).OutputsWithin input (output M input) (time M input.length) := by
  apply ClockIterationDriver.outputs (ClockStepEncoded.machine M) (ClockStepMachine.tempCount M)
    input (packetAt M input) (lengthBound M input.length)
    (ClockStepEncoded.timeConstant M*(lengthBound M input.length+1)^2) (packetAt_zero M input)
  · intro j hj
    have h := ClockStepEncoded.outputs_all M (packetAt M input j)
    rw [packetAt_step] at h
    apply BitMachine.outputsWithin_mono _ h
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (packetAt_length M input j (by omega)) 1) 2
  · intro j hj
    exact packetAt_length M input j (by omega)

def lengthCoefficient : ℕ := ClockStepEncoded.width M + 7
def stepCoefficient : ℕ := ClockStepEncoded.timeConstant M * lengthCoefficient M ^ 2
def roundCoefficient : ℕ :=
  stepCoefficient M + ((ClockStepEncoded.machine M).stackCount+2) *
    (lengthCoefficient M + stepCoefficient M * (ClockStepEncoded.machine M).pushBound) +
      (ClockStepEncoded.machine M).stackCount+4
def timeCoefficient : ℕ := ClockStepMachine.tempCount M+9+roundCoefficient M

theorem time_polynomial (n : ℕ) : time M n ≤ timeCoefficient M*(n+1)^3 := by
  have hx : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hlin : n+1 ≤ (n+1)^2 := by nlinarith
  have hl : lengthBound M n+1 ≤ lengthCoefficient M*(n+1) := by
    unfold lengthBound lengthCoefficient
    nlinarith
  have hl' : lengthBound M n ≤ lengthCoefficient M*(n+1)^2 := by
    have h := Nat.mul_le_mul_left (lengthCoefficient M) hlin
    omega
  have ht : ClockStepEncoded.timeConstant M*(lengthBound M n+1)^2 ≤ stepCoefficient M*(n+1)^2 := by
    have h := Nat.mul_le_mul_left (ClockStepEncoded.timeConstant M) (Nat.pow_le_pow_left hl 2)
    simpa only [stepCoefficient,mul_pow,Nat.mul_assoc] using h
  have hr : BitMachineIteration.roundBound (ClockStepEncoded.machine M) (lengthBound M n)
      (ClockStepEncoded.timeConstant M*(lengthBound M n+1)^2) ≤ roundCoefficient M*(n+1)^2 := by
    have htp := Nat.mul_le_mul_right (ClockStepEncoded.machine M).pushBound ht
    have hs := Nat.mul_le_mul_left ((ClockStepEncoded.machine M).stackCount+2) (Nat.add_le_add hl' htp)
    have hc := Nat.mul_le_mul_left ((ClockStepEncoded.machine M).stackCount+4) hx
    unfold BitMachineIteration.roundBound roundCoefficient
    nlinarith
  have hpre : 2*n+ClockStepMachine.tempCount M+7 ≤
      (ClockStepMachine.tempCount M+9)*(n+1)^3 := by
    have hpow : n+1 ≤ (n+1)^3 := Nat.le_self_pow (by omega) _
    have h := Nat.mul_le_mul_left (ClockStepMachine.tempCount M+9) hpow
    nlinarith
  have hr' := Nat.mul_le_mul_left n hr
  have hn : n*(roundCoefficient M*(n+1)^2) ≤ (n+1)*(roundCoefficient M*(n+1)^2) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold time timeCoefficient
  nlinarith

theorem packet_polytime : BitMachine.Polytime (output M) :=
  ⟨machine M,timeCoefficient M,3,fun input =>
    BitMachine.outputsWithin_mono _ (outputs M input) (time_polynomial M input.length)⟩

theorem output_counter (input : List Bool) :
    output M input = ClockPacketState.packet M [(state M input input.length).active] input
      (SlowClock.repetitions (CutoffBitMachine.clock M) input.length).bits := rfl

def counterField : Fin (ClockStepEncoded.width M) := ⟨2,by unfold ClockStepEncoded.width; omega⟩

def value (input : List Bool) : List Bool :=
  (SlowClock.repetitions (CutoffBitMachine.clock M) input.length).bits

theorem project_output (input : List Bool) :
    BankFieldProjection.result (counterField M) (output M input) = value M input := by
  rw [output_counter,ClockPacketState.packet,BankFieldProjection.result_encode]
  exact ClockPacketState.packet_counter M _ _ _

/-- The final ordinary-output clock, including physical counter extraction.
Its input length is the numerical simulation budget, not a binary encoding
whose logarithmic length is silently substituted for that budget. -/
theorem value_polytime : BitMachine.Polytime (value M) := by
  have h := BitMachineComposition.polytime_comp (packet_polytime M)
    (BankFieldProjection.polytime (counterField M))
  have he : (fun input => BankFieldProjection.result (counterField M) (output M input)) = value M :=
    funext (project_output M)
  change BitMachine.Polytime (fun input => BankFieldProjection.result (counterField M) (output M input)) at h
  rw [he] at h
  exact h

theorem actualClock_polytime (c A d : ℕ) :
    BitMachine.Polytime (fun input : List Bool =>
      (SlowClock.repetitions (CutoffBitMachine.actualClock c A d) input.length).bits) :=
  value_polytime (CutoffBitMachine.actualMachine c A d)

end
end EthInapproximability.CurrentPaper.ClockRuntime
