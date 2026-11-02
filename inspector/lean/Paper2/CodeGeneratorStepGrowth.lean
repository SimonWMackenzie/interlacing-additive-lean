import Paper2.CodeGeneratorReentryBound
import Paper2.CodeRecursiveStepClock

/-! Every temporary syntax word of a one-level physical compiler is
bounded by its input bank plus the charged number of executed transitions. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000

namespace Paper2.CodeGeneratorStepGrowth

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRecursiveColumn Paper2.CodeRecursiveRow
open Paper2.CodeRecursiveStep Paper2.CodeRecursiveRound
open Paper2.CodeGeneratorReentryBound

def stepPush : Nat :=
  BitMachineStackGrowth.perStep CodeRecursiveStep.program

theorem afterRow_length_le (n s q₁ q₂ w Q : Nat)
    (row col : Code) (hs : 3 ≤ s) (i : Stack) :
    (afterRow n s q₁ q₂ w Q row col i).length ≤
      (initial n s q₁ q₂ w Q row col i).length +
        stepPush * CodeRecursiveStep.clockBound
          n s q₁ q₂ w Q row col := by
  obtain ⟨t,ht,hr⟩ := CodeRecursiveStep.run_exact
    n s q₁ q₂ w Q row col hs
  let c : TM2.Cfg (fun _ : Stack => Bool)
      CodeRecursiveRound.StepLabel CodeRecursiveRound.StepControl :=
    ⟨some CodeRecursiveRound.stepStart,
      CodeRecursiveRound.stepControl,
      initial n s q₁ q₂ w Q row col⟩
  have hg := BitMachineStackGrowth.run_growth
    CodeRecursiveStep.program c t i
  have hrun : ((advance CodeRecursiveStep.program)^[t]) c =
      ⟨none, CodeRecursiveRound.stepControl,
        afterRow n s q₁ q₂ w Q row col⟩ := by
    simpa only [c, CodeRecursiveRound.stepStart,
      CodeRecursiveRound.stepControl] using hr
  rw [hrun] at hg
  dsimp [c] at hg
  change (afterRow n s q₁ q₂ w Q row col i).length ≤
    (initial n s q₁ q₂ w Q row col i).length + stepPush * t at hg
  have hm : stepPush*t ≤ stepPush*
      CodeRecursiveStep.clockBound n s q₁ q₂ w Q row col :=
    Nat.mul_le_mul_left _ ht
  omega

theorem afterRow_max_le (n s q₁ q₂ w Q : Nat)
    (row col : Code) (hs : 3 ≤ s) :
    maxLength (afterRow n s q₁ q₂ w Q row col) ≤
      maxLength (initial n s q₁ q₂ w Q row col) +
        stepPush * CodeRecursiveStep.clockBound
          n s q₁ q₂ w Q row col := by
  unfold maxLength
  apply Finset.sup_le
  intro i _
  have h := afterRow_length_le n s q₁ q₂ w Q row col hs i
  have hi := length_le_max (initial n s q₁ q₂ w Q row col) i
  dsimp [maxLength] at hi
  omega

def inputCap (n s q₁ q₂ w Q : Nat) (row col : Code) : Nat :=
  n+s+q₁+q₂+w+Q+codeSize row+codeSize col+1

theorem initial_length_le (n s q₁ q₂ w Q : Nat)
    (row col : Code) (i : Stack) :
    (initial n s q₁ q₂ w Q row col i).length ≤
      inputCap n s q₁ q₂ w Q row col := by
  by_cases hi : i ∈ CodeRecursiveReentry.keepAfter
  · simp only [CodeRecursiveReentry.keepAfter,
      CodeRecursiveReentry.publicCells, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · rcases h with h | h | h | h | h | h
      · subst i
        rw [CodeRecursiveInitialLayout.initial_core_at
          n s q₁ q₂ w Q row col 12 (by decide)]
        change (CodeRowsGraphCompiler.initialBank n s q₁ q₂ row 12).length ≤ _
        rw [CodeRowsGraphCompiler.initial_q₂]
        simp only [List.length_replicate]
        dsimp [inputCap]; omega
      · subst i
        rw [CodeRecursiveInitialLayout.initial_core_at
          n s q₁ q₂ w Q row col 16 (by decide)]
        change (CodeRowsGraphCompiler.initialBank n s q₁ q₂ row 16).length ≤ _
        rw [CodeRowsGraphCompiler.initial_q₁]
        simp only [List.length_replicate]
        dsimp [inputCap]; omega
      · subst i
        rw [CodeRecursiveInitialLayout.initial_core_at
          n s q₁ q₂ w Q row col 17 (by decide)]
        change (CodeRowsGraphCompiler.initialBank n s q₁ q₂ row 17).length ≤ _
        rw [CodeRowsGraphCompiler.initial_s]
        simp only [List.length_replicate]
        dsimp [inputCap]; omega
      · subst i
        rw [CodeRecursiveInitialLayout.initial_core_at
          n s q₁ q₂ w Q row col 18 (by decide)]
        change (CodeRowsGraphCompiler.initialBank n s q₁ q₂ row 18).length ≤ _
        rw [CodeRowsGraphCompiler.initial_n]
        simp only [List.length_replicate]
        dsimp [inputCap]; omega
      · subst i
        rw [initial, CodeRecursiveColumn.foreign_at w Q col _ 31 (by decide)]
        simp only [CodeRecursiveColumn.foreignWords,
          ite_true, List.length_replicate]
        dsimp [inputCap]; omega
      · subst i
        rw [initial, CodeRecursiveColumn.foreign_at w Q col _ 32 (by decide)]
        change (List.replicate Q true).length ≤ _
        simp only [List.length_replicate]
        dsimp [inputCap]; omega
    · rcases h with h | h
      · subst i
        rw [CodeRecursiveInitialLayout.initial_core_at
          n s q₁ q₂ w Q row col 2 (by decide)]
        change (CodeRowsGraphCompiler.initialBank n s q₁ q₂ row 2).length ≤ _
        rw [CodeRowsGraphCompiler.initial_child,
          encodeCode_length]
        dsimp [inputCap]; omega
      · subst i
        rw [initial, CodeRecursiveColumn.foreign_at w Q col _ 33 (by decide)]
        change (encodeCode col).length ≤ _
        rw [encodeCode_length]
        dsimp [inputCap]; omega
  · rw [CodeRecursiveInitialLayout.initial_other_blank
      n s q₁ q₂ w Q row col i hi]
    simp

theorem initial_max_le (n s q₁ q₂ w Q : Nat)
    (row col : Code) :
    maxLength (initial n s q₁ q₂ w Q row col) ≤
      inputCap n s q₁ q₂ w Q row col := by
  unfold maxLength
  apply Finset.sup_le
  intro i _
  exact initial_length_le n s q₁ q₂ w Q row col i

theorem round_clock_le (n s q₁ q₂ w Q : Nat)
    (row col : Code) (hs : 3 ≤ s) :
    CodeRecursiveRound.clock n s q₁ q₂ w Q row col ≤
      CodeRecursiveStep.clockBound n s q₁ q₂ w Q row col +
        CodeGeneratorReentryBound.factor *
          (inputCap n s q₁ q₂ w Q row col +
            stepPush * CodeRecursiveStep.clockBound
              n s q₁ q₂ w Q row col + 1) + 11 := by
  have hr := reentry_clock_le
    (afterRow n s q₁ q₂ w Q row col)
  have hm := afterRow_max_le n s q₁ q₂ w Q row col hs
  have hi := initial_max_le n s q₁ q₂ w Q row col
  dsimp [CodeRecursiveRound.clock]
  have hmul := Nat.mul_le_mul_left
    CodeGeneratorReentryBound.factor
    (show maxLength (afterRow n s q₁ q₂ w Q row col)+1 ≤
      inputCap n s q₁ q₂ w Q row col +
        stepPush * CodeRecursiveStep.clockBound
          n s q₁ q₂ w Q row col + 1 by omega)
  omega

def roundPoly (n s q₁ q₂ w Q r c : Nat) : Nat :=
  let step := CodeRecursiveStepClock.polynomialClock n s q₁ q₂ w Q r c
  let input := n+s+q₁+q₂+w+Q+r+c+1
  step + CodeGeneratorReentryBound.factor *
    (input + stepPush*step + 1) + 11

theorem round_clock_le_poly (n s q₁ q₂ w Q : Nat)
    (row col : Code) (hs : 3 ≤ s) :
    CodeRecursiveRound.clock n s q₁ q₂ w Q row col ≤
      roundPoly n s q₁ q₂ w Q (codeSize row) (codeSize col) := by
  have hr := round_clock_le n s q₁ q₂ w Q row col hs
  have hp := CodeRecursiveStepClock.clock_le_polynomial
    n s q₁ q₂ w Q row col hs
  have hmul := Nat.mul_le_mul_left CodeGeneratorReentryBound.factor
    (show inputCap n s q₁ q₂ w Q row col +
        stepPush * CodeRecursiveStep.clockBound n s q₁ q₂ w Q row col + 1 ≤
      inputCap n s q₁ q₂ w Q row col +
        stepPush * CodeRecursiveStepClock.polynomialClock n s q₁ q₂ w Q
          (codeSize row) (codeSize col) + 1 by
      have := Nat.mul_le_mul_left stepPush hp
      omega)
  dsimp [roundPoly, inputCap] at *
  omega

#print axioms round_clock_le
#print axioms round_clock_le_poly

end Paper2.CodeGeneratorStepGrowth
