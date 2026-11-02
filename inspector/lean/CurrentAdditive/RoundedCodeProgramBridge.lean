import CurrentAdditive.RoundedCodeExecution
import CurrentAdditive.RoundedProgram

namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorStateSize
open Paper2.GeneratorSerialization Paper2.RecursiveSamplingProgram
open Paper2.RecursiveSamplingCapped CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem programRun_eq_runState {A : ℕ} (b N : ℕ)
    (s : Paper2.RecursiveSamplingCapped.State (List Bool) A) (bits : BitBlocks b N) :
    programRun b N s.val bits = (CurrentAdditive.RoundedProgram.runState b N s bits).val := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      exact ih (stateStep s (draw (stateDenominator s) (2 ^ b) (stateDenominator_pos s)
        (by positivity) (Paper2.CappedSampler.bitsTicketEquiv b bits.1))) bits.2

theorem execute_output_eq_runProgram {A : ℕ} (b N : ℕ) (s : Paper2.GeneratorCode.State)
    (hp : PositiveState s) (hA : (stateMeaning s).maxAlphabet ≤ A)
    (hN : (stateMeaning s).maxDraws ≤ N) (bits : BitBlocks b N) :
    (execute b N s bits).1.output =
      CurrentAdditive.RoundedProgram.runProgram b N ⟨stateMeaning s, hA⟩ hN bits := by
  have hd := execute_done b N s hp hN bits
  have hleaf : stateMeaning (execute b N s bits).1 =
      .pure (execute b N s bits).1.output := by
    simp [stateMeaning, hd, stackMeaning]
  have hstate : (CurrentAdditive.RoundedProgram.runState b N ⟨stateMeaning s, hA⟩ bits).val =
      .pure (execute b N s bits).1.output :=
    (programRun_eq_runState b N ⟨stateMeaning s, hA⟩ bits).symm.trans
      ((execute_meaning b N s bits).symm.trans hleaf)
  exact (CurrentAdditive.RoundedProgram.leafValue_of_eq_pure _ _ _ hstate).symm

/-- A single fixed banked bit machine realizes rounded Program execution.
The semantic alphabet/draw bounds supply only finite resource parameters;
the actual machine run and its clock are proved from encoded Code syntax. -/
theorem physical_runProgram {A : ℕ} (root : Code) (b N : ℕ)
    (s : Paper2.GeneratorCode.State) (hp : PositiveState s) (ht : Trace root s)
    (hA : (stateMeaning s).maxAlphabet ≤ A) (hN : (stateMeaning s).maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ (N + 1) * stepBudget (codeSize root) b,
      run t (start s (tapeWord b N bits ++ suffix) b) =
        ⟨none, RoundedCodeStep.finalControl true,
          (RoundedCodeAdmin.start
            ⟨[], CurrentAdditive.RoundedProgram.runProgram b N ⟨stateMeaning s, hA⟩ hN bits⟩
            ((execute b N s bits).2 ++ suffix) b).stk⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_execute root b N s hp ht hN bits suffix
  exact ⟨t, ht, by simpa only [execute_output_eq_runProgram b N s hp hA hN bits] using hr⟩

theorem initial_meaning (c : Code) : stateMeaning (Paper2.GeneratorCode.initial c) = meaning c := by
  simp [stateMeaning, Paper2.GeneratorCode.initial, stackMeaning, concat_pure_nil_right]
  exact Paper2.EncodedSamplerAlgebra.Program.map_id (meaning c)

theorem physical_initialProgram {A : ℕ} (c : Code) (hc : Positive c) (b N : ℕ)
    (hA : (meaning c).maxAlphabet ≤ A) (hN : (meaning c).maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ (N + 1) * stepBudget (codeSize c) b,
      run t (start (Paper2.GeneratorCode.initial c) (tapeWord b N bits ++ suffix) b) =
        ⟨none, RoundedCodeStep.finalControl true,
          (RoundedCodeAdmin.start
            ⟨[], CurrentAdditive.RoundedProgram.runProgram b N ⟨meaning c, hA⟩ hN bits⟩
            ((execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b).stk⟩ := by
  have ha : (stateMeaning (Paper2.GeneratorCode.initial c)).maxAlphabet ≤ A := by
    simpa only [initial_meaning] using hA
  have hn : (stateMeaning (Paper2.GeneratorCode.initial c)).maxDraws ≤ N := by
    simpa only [initial_meaning] using hN
  simpa only [initial_meaning] using physical_runProgram c b N
    (Paper2.GeneratorCode.initial c) (positive_initial c hc) Trace.initial ha hn bits suffix

#print axioms execute_output_eq_runProgram
#print axioms physical_initialProgram

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
