import CurrentAdditive.RoundedCodeLoop

namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorStateSize
open Paper2.GeneratorPositive
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def stepBudget (R b : ℕ) : ℕ :=
  RoundedCodeStep.cleanupCoefficient *
    (13 * (R + 3) ^ 2 + 1 + RoundedLoadedClock.coefficient * (R + b + 2) ^ 2 +
      70 * (R + 1) + 10) + RoundedCodeReset.clearCount + 4

def roundedTicket (s : State) (b : ℕ) (bits : Fin b → Bool) :
    Fin (request (Paper2.GeneratorCode.normalize s)) :=
  CurrentAdditive.RoundedDraw.draw _ (2 ^ b) (request_pos _) (by positivity)
    (Paper2.CappedSampler.bitsTicketEquiv b bits)

def roundedNext (s : State) (b : ℕ) (bits : Fin b → Bool) : State :=
  Paper2.GeneratorCode.advance (Paper2.GeneratorCode.normalize s) (roundedTicket s b bits).val

private theorem state_eta (s : State) : s = ⟨s.todo, s.output⟩ := by cases s; rfl

private theorem todo_length (cs : List Code) :
    (Paper2.CodeAdminNormalization.todoWord cs).length = codesSize cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simpa [Paper2.CodeAdminNormalization.todoWord, codesSize, encodeCode_length]
        using congrArg (fun n => codeSize c + n) ih

private theorem draw_budget (R b a action : ℕ) (ha : a ≤ R)
    (hact : action ≤ 70 * (R + 1) + 8) :
    RoundedCodeStep.cleanupCoefficient *
      (13 * (R + 3) ^ 2 + 1 + RoundedLoadedClock.coefficient * (a + b + 2) ^ 2 +
        action + 1) + RoundedCodeReset.clearCount + 3 + 1 ≤ stepBudget R b := by
  have hsq : (a + b + 2) ^ 2 ≤ (R + b + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hd := Nat.mul_le_mul_left RoundedLoadedClock.coefficient hsq
  have hi : 13 * (R + 3) ^ 2 + 1 +
      RoundedLoadedClock.coefficient * (a + b + 2) ^ 2 + action + 1 ≤
      13 * (R + 3) ^ 2 + 1 + RoundedLoadedClock.coefficient * (R + b + 2) ^ 2 +
        70 * (R + 1) + 10 := by omega
  have hm := Nat.mul_le_mul_left RoundedCodeStep.cleanupCoefficient hi
  unfold stepBudget
  omega

theorem stopped_step (root : Code) (s : State) (hp : PositiveState s) (ht : Trace root s)
    (b : ℕ) (tape : List Bool) (hn : (Paper2.GeneratorCode.normalize s).todo = []) :
    ∃ t ≤ stepBudget (codeSize root) b, run t (start s tape b) =
      ⟨none, RoundedCodeStep.finalControl true,
        (RoundedCodeAdmin.start ⟨[], (Paper2.GeneratorCode.normalize s).output⟩ tape b).stk⟩ := by
  have hs : Paper2.GeneratorCode.normalize s =
      ⟨[], (Paper2.GeneratorCode.normalize s).output⟩ := by
    rw [state_eta (Paper2.GeneratorCode.normalize s), hn]
  obtain ⟨t, ht', hr⟩ := source_stop s _ tape b _
    (RoundedCodeStep.done_step root s hp ht _ tape b hs)
  refine ⟨t, ht'.trans ?_, hr⟩
  have hi : 13 * (codeSize root + 3) ^ 2 + 2 ≤
      13 * (codeSize root + 3) ^ 2 + 1 +
        RoundedLoadedClock.coefficient * (codeSize root + b + 2) ^ 2 +
        70 * (codeSize root + 1) + 10 := by omega
  have hm := Nat.mul_le_mul_left RoundedCodeStep.cleanupCoefficient hi
  unfold stepBudget
  omega

theorem draw_step (root : Code) (s : State) (hp : PositiveState s) (ht : Trace root s)
    (b : ℕ) (bits : Fin b → Bool) (suffix : List Bool)
    (hne : (Paper2.GeneratorCode.normalize s).todo ≠ []) :
    ∃ t ≤ stepBudget (codeSize root) b,
      run t (start s (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) b) =
        start (roundedNext s b bits) suffix b := by
  have hready := normalize_ready s
  have hpositive := normalize_positive s hp
  obtain ⟨c, cs, hc, hdraw⟩ := ready_positive_draw _ hpositive hready hne
  let out := (Paper2.GeneratorCode.normalize s).output
  have hs : Paper2.GeneratorCode.normalize s = ⟨c :: cs, out⟩ := by
    conv_lhs => rw [state_eta (Paper2.GeneratorCode.normalize s)]
    rw [hc]
  have hsize := trace_potential_le root _ (trace_normalize root s ht)
  rw [hs] at hsize
  cases c with
  | emit word => simp [DrawHead] at hdraw
  | append left right => simp [DrawHead] at hdraw
  | ticket a =>
      cases a with
      | zero => simp [DrawHead] at hdraw
      | succ a =>
          have ha : a + 1 ≤ codeSize root := by
            dsimp [potential, codesSize, codeSize] at hsize
            omega
          obtain ⟨t, htime, hr⟩ := source_again s _ _ suffix b _
            (RoundedCodeStep.ticket_step root s hp ht (a+1) b (by omega) cs out hs bits suffix)
          refine ⟨t, htime.trans (draw_budget _ _ _ _ ha (by omega)), ?_⟩
          simpa [roundedNext, roundedTicket, CurrentAdditive.RoundedDraw.draw, hs, request, Paper2.GeneratorCode.advance,
            Paper2.RecursiveLabelCodecScratch.finCodec] using hr
  | bit =>
      have ha : 2 ≤ codeSize root := (by have := codeSize_ge_three root; omega)
      obtain ⟨t, htime, hr⟩ := source_again s _ _ suffix b _
        (RoundedCodeStep.bit_step root s hp ht b cs out hs bits suffix)
      refine ⟨t, htime.trans (draw_budget _ _ _ _ ha (by omega)), ?_⟩
      simpa [roundedNext, roundedTicket, CurrentAdditive.RoundedDraw.draw, hs, request, Paper2.GeneratorCode.advance] using hr
  | branch3 a cut₁ cut₂ first second third =>
      cases a with
      | zero => simp [DrawHead] at hdraw
      | succ a =>
          have ha : a + 1 ≤ codeSize root := by
            dsimp [potential, codesSize, codeSize] at hsize
            omega
          have hsel : 1 + 70 * (a + 1 + cut₁ + cut₂ +
              (Paper2.BranchSelection.inputWord first second third
                (Paper2.CodeAdminNormalization.todoWord cs)).length + 1) ≤
                  70 * (codeSize root + 1) + 8 := by
            have hword : (Paper2.BranchSelection.inputWord first second third
                (Paper2.CodeAdminNormalization.todoWord cs)).length =
                codeSize first + codeSize second + codeSize third + codesSize cs := by
              simp only [Paper2.BranchSelection.inputWord, List.length_append,
                encodeCode_length, todo_length]
            rw [hword]
            dsimp [potential, codesSize, codeSize] at hsize
            omega
          obtain ⟨t, htime, hr⟩ := source_again s _ _ suffix b _
            (RoundedCodeStep.branch_step root s hp ht (a+1) b (by omega) cut₁ cut₂
              first second third cs out hs bits suffix)
          refine ⟨t, htime.trans (draw_budget _ _ _ _ ha hsel), ?_⟩
          simpa [roundedNext, roundedTicket, CurrentAdditive.RoundedDraw.draw, hs, request, Paper2.GeneratorCode.advance] using hr

#print axioms stopped_step
#print axioms draw_step

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
