import EthInapproximability.CurrentPaper.ExactParameterMachineCutoff
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.ExactParameters

/-!
# Physical power-of-two branches of the exact parameter compiler

From the source exponent `s`, the actual scalar definitions require
`r=2^s` and `d=2^r`. This module composes the literal unary power-of-two
program twice with the literal source-exponent program. Transfer costs are
counted by the concrete Boolean-stack composition theorem.

Source: frozen v8 `E-exact-details.tex`, `eq:exact-parameters` and the
padding formula in `03-exact-hardness.tex`.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachinePower

open BitMachineComposition

noncomputable def rMachine : BitMachine.Machine :=
  composition ExactParameterMachineCutoff.sourceExponentMachine MatrixUnaryPower.machine

theorem r_outputs (edges : ℕ) :
    ∃ T, rMachine.OutputsWithin (List.replicate edges true)
      (List.replicate (ExactParameters.dimensionLog
        (ExactSourcePadding.paddedExponent edges)) true) T := by
  obtain ⟨T, h⟩ := ExactParameterMachineCutoff.sourceExponent_outputs edges
  have hp : MatrixUnaryPower.machine.OutputsWithin
      (List.replicate (ExactSourcePadding.paddedExponent edges) true)
      (List.replicate (ExactParameters.dimensionLog
        (ExactSourcePadding.paddedExponent edges)) true)
      (16 * ExactParameters.dimensionLog (ExactSourcePadding.paddedExponent edges)) := by
    simpa only [List.length_replicate, ExactParameters.dimensionLog] using
      MatrixUnaryPower.outputs (List.replicate (ExactSourcePadding.paddedExponent edges) true)
  exact ⟨_, composition_outputsWithin ExactParameterMachineCutoff.sourceExponentMachine
    MatrixUnaryPower.machine h hp⟩

noncomputable def dMachine : BitMachine.Machine :=
  composition rMachine MatrixUnaryPower.machine

theorem d_outputs (edges : ℕ) :
    ∃ T, dMachine.OutputsWithin (List.replicate edges true)
      (List.replicate (ExactSourcePadding.paddedDimension edges) true) T := by
  obtain ⟨T, h⟩ := r_outputs edges
  have hp : MatrixUnaryPower.machine.OutputsWithin
      (List.replicate (ExactParameters.dimensionLog
        (ExactSourcePadding.paddedExponent edges)) true)
      (List.replicate (ExactSourcePadding.paddedDimension edges) true)
      (16 * ExactSourcePadding.paddedDimension edges) := by
    simpa only [List.length_replicate, ExactParameters.dimensionLog,
      ExactSourcePadding.paddedDimension] using
      MatrixUnaryPower.outputs (List.replicate
        (ExactParameters.dimensionLog (ExactSourcePadding.paddedExponent edges)) true)
  exact ⟨_, composition_outputsWithin rMachine MatrixUnaryPower.machine
    h hp⟩

end EthInapproximability.CurrentPaper.ExactParameterMachinePower
