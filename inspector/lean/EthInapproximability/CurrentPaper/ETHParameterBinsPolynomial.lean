import EthInapproximability.CurrentPaper.ETHParameterBinsActual
import EthInapproximability.CurrentPaper.ETHParameterScalePolynomial

/-! The bin stage is polynomial in the length of the unary input together
with its *produced* unary bin word, not polynomial in the unary input alone.
This is a bounded construction lemma, not a claim about the entire compiler. -/

namespace EthInapproximability.CurrentPaper.ETHBinsOutputClockScratch

open ETHBinsStandaloneScratch ETHBinsSourcePreservingScratch

noncomputable section

def outputSize (n : ℕ) : ℕ := n + ETHBinsStandaloneScratch.bins n + 1
def coefficient : ℕ := UnaryBinaryEncoding.coefficient + 50000

private theorem aux_le (n : ℕ) : ETHBinsStandaloneScratch.aux n ≤ n := by
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

private theorem time_formula (n : ℕ) :
    ETHBinsSourcePreservingScratch.totalTime n =
      (UnaryBinaryEncoding.coefficient+6)*(n+1)^2 +
      40014*(ETHBinsStandaloneScratch.aux n)^2 +
      24*ETHBinsStandaloneScratch.aux n + 2*n + 28 +
      16*ETHBinsStandaloneScratch.bins n := by
  dsimp [ETHBinsSourcePreservingScratch.totalTime,
    ETHBinsStandaloneScratch.totalTime,
    ETHBinsStandaloneScratch.exponentTime,
    ETHBinsStandaloneScratch.logTime,
    ETHBinsStandaloneScratch.squareTime,
    ETHBinsStandaloneScratch.exponent,
    ETHBinsCoefficientScratch.time,
    MatrixAddressMachine.exactTime]
  ring

/-- A degree-two upper bound in input plus actual unary output length.
The exponential output is expressly included in `outputSize`. -/
theorem totalTime_output_poly (n : ℕ) :
    ETHBinsSourcePreservingScratch.totalTime n ≤
      coefficient * (outputSize n)^2 := by
  let H := outputSize n
  have hn : n+1 ≤ H := by dsimp [H,outputSize]; omega
  have hu : ETHBinsStandaloneScratch.aux n ≤ H :=
    (aux_le n).trans (by omega)
  have hb : ETHBinsStandaloneScratch.bins n ≤ H := by
    dsimp [H,outputSize]; omega
  have hpos : 1 ≤ H := by omega
  have hsqn : (n+1)^2 ≤ H^2 := Nat.pow_le_pow_left hn 2
  have hsqu : (ETHBinsStandaloneScratch.aux n)^2 ≤ H^2 :=
    Nat.pow_le_pow_left hu 2
  have hlin : H ≤ H^2 := by nlinarith
  have hone : 1 ≤ H^2 := by nlinarith
  have hlog := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+6) hsqn
  rw [time_formula]
  dsimp [coefficient]
  nlinarith

theorem bins_run_output_poly (n : ℕ) :
    ∃ t ≤ coefficient * (outputSize n)^2,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
        ∃ F : ETHBinsSourcePreservingScratch.Stack → List Bool,
          ((BitMachineEncoding.advance ETHBinsSourcePreservingScratch.program)^[t])
            (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
              (none,ETHBinsStandaloneScratch.machine.initial),
              ETHBinsSourcePreservingScratch.initialBank n⟩ :
              Turing.TM2.Cfg
                (fun _ : ETHBinsSourcePreservingScratch.Stack => Bool)
                ETHBinsSourcePreservingScratch.Label
                ETHBinsSourcePreservingScratch.Control) =
            ⟨none,(none,v),F⟩ ∧
          F ETHBinsSourcePreservingScratch.sourceKey =
            ETHBinsStandaloneScratch.unary n ∧
          F ETHBinsSourcePreservingScratch.outputKey =
            ETHBinsStandaloneScratch.unary (ETHBinsStandaloneScratch.bins n) := by
  obtain ⟨t,ht,v,F,hr,hs,hb⟩ := ETHBinsSourcePreservingScratch.bins_run n
  exact ⟨t,ht.trans (totalTime_output_poly n),v,F,hr,hs,hb⟩

def joinedOutputClock (i : Parameters.Input) : ℕ :=
  ETHScalePolynomialClock.polynomialClock (ETHScalePolynomialClock.width i) +
    coefficient * (outputSize (Parameters.scale i))^2 + 1

theorem joinedBound_le_output_clock (i : Parameters.Input) :
    ETHBinsJoinedScratch.totalBound i ≤ joinedOutputClock i := by
  have hs := ETHScalePolynomialClock.totalBound_le_polynomial i
  have hb := totalTime_output_poly (Parameters.scale i)
  dsimp [ETHBinsJoinedScratch.totalBound,joinedOutputClock]
  omega

/-- Same joined physical program, now bounded by the raw-word polynomial
plus a quadratic in scale input and the actually produced unary bin word. -/
theorem actual_bins_run_output_clock (i : Parameters.Input) :
    ∃ t ≤ joinedOutputClock i,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
        ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
          ((BitMachineEncoding.advance ETHBinsJoinedScratch.program)^[t])
            (⟨some (BitMachineRawSequence.leftLabel ETHBinsJoinedScratch.scaleStart),
              (ETHBinsJoinedScratch.scaleControl,ETHBinsJoinedScratch.binsControl),
              ETHBinsJoinedScratch.initialBank i⟩ :
              Turing.TM2.Cfg (fun _ : ETHBinsJoinedScratch.Stack => Bool)
                ETHBinsJoinedScratch.Label ETHBinsJoinedScratch.Control) =
            ⟨none,(ETHBinsJoinedScratch.scaleControl,(none,v)),F⟩ ∧
          F (.inr ETHBinsSourcePreservingScratch.outputKey) =
            List.replicate (Parameters.bins i) true ∧
          F (.inl (.inr ScaleFinalScratch.answerKey)) =
            List.replicate (Parameters.scale i) true ∧
          (∀ j : Fin 6,
            F (.inl (.inl (ETHScaleGlobalLog.raw j))) =
              ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨t,ht,v,F,hr,hb,hs,hraw⟩ := ETHBinsJoinedScratch.actual_bins_run i
  exact ⟨t,ht.trans (joinedBound_le_output_clock i),v,F,hr,hb,hs,hraw⟩


end
end EthInapproximability.CurrentPaper.ETHBinsOutputClockScratch
