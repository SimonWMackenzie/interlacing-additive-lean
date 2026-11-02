import CurrentAdditive.RoundedCodeSemantics

namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorStateSize
open Paper2.GeneratorSerialization CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

/-- Every physical instruction is charged, including the last deterministic
normalization and every scratch clear. The initial Code length controls all
administrative work through Trace; the draw count only controls repetitions.
Unused reserved blocks and the arbitrary caller suffix remain on tape. -/
theorem physical_execute (root : Code) (b N : ℕ) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (hN : (stateMeaning s).maxDraws ≤ N) (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ (N + 1) * stepBudget (codeSize root) b,
      run t (start s (tapeWord b N bits ++ suffix) b) =
        ⟨none, RoundedCodeStep.finalControl true,
          (RoundedCodeAdmin.start ⟨[], (execute b N s bits).1.output⟩
            ((execute b N s bits).2 ++ suffix) b).stk⟩ := by
  induction N generalizing s with
  | zero =>
      have hd := no_draws_done s hp (by omega)
      obtain ⟨t, htime, hr⟩ := stopped_step root s hp ht b suffix hd
      exact ⟨t, by simpa using htime, by simpa [execute, tapeWord] using hr⟩
  | succ N ih =>
      by_cases hd : (Paper2.GeneratorCode.normalize s).todo = []
      · obtain ⟨t, htime, hr⟩ := stopped_step root s hp ht b (tapeWord b (N+1) bits ++ suffix) hd
        refine ⟨t, htime.trans ?_, ?_⟩
        · nlinarith [Nat.zero_le (N * stepBudget (codeSize root) b)]
        · simpa only [execute, hd, ↓reduceIte] using hr
      · have hnext : (stateMeaning (roundedNext s b bits.1)).maxDraws ≤ N := by
          have hn := next_draws_le s b bits.1
          omega
        obtain ⟨u, hu, hur⟩ := draw_step root s hp ht b bits.1
          (tapeWord b N bits.2 ++ suffix) hd
        obtain ⟨v, hv, hvr⟩ := ih (roundedNext s b bits.1)
          (roundedNext_positive s hp b bits.1) (roundedNext_trace root s ht b bits.1)
          hnext bits.2
        refine ⟨u + v, ?_, ?_⟩
        · nlinarith
        · simpa only [execute, hd, ↓reduceIte, tapeWord, List.append_assoc] using
            (join_run hur v).trans hvr

theorem physical_code (c : Code) (hc : Positive c) (b N : ℕ)
    (hN : (meaning c).maxDraws ≤ N) (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ (N + 1) * stepBudget (codeSize c) b,
      run t (start (Paper2.GeneratorCode.initial c) (tapeWord b N bits ++ suffix) b) =
        ⟨none, RoundedCodeStep.finalControl true,
          (RoundedCodeAdmin.start
            ⟨[], (execute b N (Paper2.GeneratorCode.initial c) bits).1.output⟩
            ((execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b).stk⟩ := by
  apply physical_execute c b N _ (positive_initial c hc) Trace.initial _ bits suffix
  simpa [stateMeaning, Paper2.GeneratorCode.initial, stackMeaning,
    concat_pure_nil_right] using hN

#print axioms physical_execute
#print axioms physical_code

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
