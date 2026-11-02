import CurrentAdditive.RoundedCodeProgramBridge

namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorPositive
open CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000

def interpreterCoefficient : ℕ :=
  RoundedCodeStep.cleanupCoefficient * (13 + RoundedLoadedClock.coefficient + 81) +
    RoundedCodeReset.clearCount + 4

theorem stepBudget_quadratic (R b : ℕ) :
    stepBudget R b ≤ interpreterCoefficient * (R + b + 3) ^ 2 := by
  let X := R + b + 3
  have h1 : (R + 3) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by dsimp [X]; omega) 2
  have h2 : (R + b + 2) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by dsimp [X]; omega) 2
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hp : 1 ≤ X ^ 2 := by simpa using Nat.pow_le_pow_left hx 2
  have hx2 : X ≤ X ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_left X hx
  have hRX : R + 1 ≤ X := by dsimp [X]; omega
  have hR : R + 1 ≤ X ^ 2 := hRX.trans hx2
  have hl : 70 * (R + 1) + 11 ≤ 81 * X ^ 2 := by omega
  have hm1 := Nat.mul_le_mul_left 13 h1
  have hm2 := Nat.mul_le_mul_left RoundedLoadedClock.coefficient h2
  have hcore : 13 * (R + 3) ^ 2 + 1 +
      RoundedLoadedClock.coefficient * (R + b + 2) ^ 2 + 70 * (R + 1) + 10 ≤
      (13 + RoundedLoadedClock.coefficient + 81) * X ^ 2 := by nlinarith
  have hclear : RoundedCodeReset.clearCount + 4 ≤
      (RoundedCodeReset.clearCount + 4) * X ^ 2 := by nlinarith
  calc
    stepBudget R b ≤ RoundedCodeStep.cleanupCoefficient *
        ((13 + RoundedLoadedClock.coefficient + 81) * X ^ 2) +
          (RoundedCodeReset.clearCount + 4) * X ^ 2 := by
      unfold stepBudget
      have hmul := Nat.mul_le_mul_left RoundedCodeStep.cleanupCoefficient hcore
      omega
    _ = interpreterCoefficient * (R + b + 3) ^ 2 := by unfold interpreterCoefficient; dsimp [X]; ring

theorem physical_initialProgram_polynomial {A : ℕ} (c : Code) (hc : Positive c) (b N : ℕ)
    (hA : (meaning c).maxAlphabet ≤ A) (hN : (meaning c).maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ interpreterCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2,
      run t (start (Paper2.GeneratorCode.initial c) (tapeWord b N bits ++ suffix) b) =
        ⟨none, RoundedCodeStep.finalControl true,
          (RoundedCodeAdmin.start
            ⟨[], CurrentAdditive.RoundedProgram.runProgram b N ⟨meaning c, hA⟩ hN bits⟩
            ((execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b).stk⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_initialProgram c hc b N hA hN bits suffix
  refine ⟨t, ht.trans ?_, hr⟩
  have hm := Nat.mul_le_mul_left (N + 1) (stepBudget_quadratic (codeSize c) b)
  calc
    (N + 1) * stepBudget (codeSize c) b ≤
        (N + 1) * (interpreterCoefficient * (codeSize c + b + 3) ^ 2) := hm
    _ = _ := by ring

#print axioms stepBudget_quadratic
#print axioms physical_initialProgram_polynomial

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
