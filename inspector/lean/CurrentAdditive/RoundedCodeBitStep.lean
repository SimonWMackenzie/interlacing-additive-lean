import CurrentAdditive.RoundedCodeTicketStep

namespace EthInapproximability.CurrentPaper.RoundedCodeStep

open Turing BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
noncomputable section

private theorem bit_reset_bank (S : RoundedCodeDraw.OldStack → List Bool)
    (b : ℕ) (input suffix ticket : List Bool) (bit : Bool)
    (cs : List Code) (out : List Bool)
    (hCode : S (Paper2.CodeHeaderDraw.h 0) = Paper2.CodeAdminNormalization.todoWord cs) :
    RoundedCodeReset.resetBank
      (RoundedCodeHandle.framedOutput (RoundedCodeDraw.resultBank S 2 b input suffix ticket)
        (Paper2.CodeDrawOutput.cfg none none [] (bit :: out.reverse))).stk =
      (RoundedCodeAdmin.start ⟨cs, out ++ [bit]⟩ suffix b).stk := by
  let T := RoundedCodeDraw.resultBank S 2 b input suffix ticket
  let c := Paper2.CodeDrawOutput.cfg none none [] (bit :: out.reverse)
  apply RoundedCodeCanonical.reset_bank
  · rw [RoundedCodeHandle.framed_output_other T c RoundedCodeReset.code]
    · change RoundedCodeDraw.resultBank S 2 b input suffix ticket
        (.inl (Paper2.CodeHeaderDraw.h 0)) = Paper2.CodeAdminNormalization.todoWord cs
      rw [RoundedCodeDraw.result_other_old S 2 b input suffix ticket (Paper2.CodeHeaderDraw.h 0)]
      · exact hCode
      all_goals simp [RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth,
        RoundedCodeDraw.oldTape, RoundedCodeDraw.oldResult,
        Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d]
    all_goals simp [RoundedCodeReset.code, RoundedCodeReset.output,
      RoundedCodeDraw.oldResult, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d,
      Paper2.CodeHeaderDraw.output]
  · rw [RoundedCodeHandle.framed_output_value]
    simp [c, Paper2.CodeDrawOutput.cfg, Paper2.CodeDrawOutput.bank, List.reverse_append]
  · rw [RoundedCodeHandle.framed_output_other T c RoundedCodeReset.tape]
    · exact RoundedCodeDraw.result_tape S 2 b input suffix ticket
    all_goals simp [RoundedCodeReset.tape, RoundedCodeReset.output,
      RoundedCodeDraw.oldTape, RoundedCodeDraw.oldResult,
      Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]
  · rw [RoundedCodeHandle.framed_output_other T c RoundedCodeReset.width]
    · exact RoundedCodeDraw.result_width S 2 b input suffix ticket
    all_goals simp [RoundedCodeReset.width, RoundedCodeReset.output,
      RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldResult,
      Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]

theorem bit_step (root : Code) (s : State) (hp : PositiveState s) (ht : Trace root s)
    (b : ℕ) (cs : List Code) (out : List Bool)
    (hs : Paper2.GeneratorCode.normalize s = ⟨.bit :: cs, out⟩)
    (bits : Fin b → Bool) (suffix : List Bool) :
    let q := CurrentAdditive.RoundedDraw.draw 2 (2 ^ b) (by decide) (by positivity)
      (Paper2.CappedSampler.bitsTicketEquiv b bits)
    let bit := decide (q.val = 1)
    ∃ t ≤ cleanupCoefficient *
        (13 * (codeSize root + 3) ^ 2 + 1 +
          RoundedLoadedClock.coefficient * (2 + b + 2) ^ 2 + 5 + 1) +
            RoundedCodeReset.clearCount + 3,
      run t (start s (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) b) =
        ⟨none, finalControl false, (RoundedCodeAdmin.start ⟨cs, out ++ [bit]⟩ suffix b).stk⟩ := by
  let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
  let q := CurrentAdditive.RoundedDraw.draw 2 (2 ^ b) (by decide) (by positivity)
    (Paper2.CappedSampler.bitsTicketEquiv b bits)
  let ticket := (Paper2.RecursiveLabelCodecScratch.finCodec 2).encode q
  let bit := decide (q.val = 1)
  let S := RoundedCodeAdmin.bitOldBank cs out input b
  obtain ⟨u, hu, hur⟩ := RoundedCodeAdmin.normalize_run root s hp ht input b
  rw [hs] at hur
  obtain ⟨v, hv, hvr⟩ := RoundedCodeAdmin.bit_from_ready b cs out bits suffix
  let d : RoundedCodeAdmin.Config :=
    ⟨none, (RoundedCodeAdmin.kindControl .bit, RoundedLoadedDraw.initial),
      RoundedCodeDraw.resultBank S 2 b input suffix ticket⟩
  have hadmin : RoundedCodeAdmin.run (u + v) (RoundedCodeAdmin.start s input b) = d := by
    rw [RoundedCodeAdmin.run, Nat.add_comm u v, Function.iterate_add_apply]
    change RoundedCodeAdmin.run v (RoundedCodeAdmin.run u _) = _
    rw [hur]
    exact hvr
  have hi : d.stk (.inl RoundedCodeDraw.oldResult) = ticket :=
    RoundedCodeDraw.result_word S 2 b input suffix ticket
  have ho : d.stk (.inl Paper2.CodeHeaderDraw.output) = out.reverse := by
    change RoundedCodeDraw.resultBank S 2 b input suffix ticket (.inl Paper2.CodeHeaderDraw.output) = _
    rw [RoundedCodeDraw.result_other_old S 2 b input suffix ticket Paper2.CodeHeaderDraw.output]
    · rfl
    all_goals simp [RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth,
      RoundedCodeDraw.oldTape, RoundedCodeDraw.oldResult,
      Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]
  obtain ⟨w, hw, hwr⟩ := RoundedCodeHandle.bit_run d.stk q out.reverse hi ho
  let e := RoundedCodeHandle.framedOutput d.stk
    (Paper2.CodeDrawOutput.cfg none none [] (bit :: out.reverse))
  obtain ⟨t, htime, hrun⟩ := compose_source_success_clock s input b d (u + v) hadmin rfl
    .bit rfl e w hwr rfl
  have hbank : RoundedCodeReset.resetBank e.stk =
      (RoundedCodeAdmin.start ⟨cs, out ++ [bit]⟩ suffix b).stk :=
    bit_reset_bank S b input suffix ticket bit cs out (by rfl)
  refine ⟨t, ?_, ?_⟩
  · have hbase : u + v + w + 1 ≤
        13 * (codeSize root + 3) ^ 2 + 1 +
          RoundedLoadedClock.coefficient * (2 + b + 2) ^ 2 + 5 + 1 := by
      have hq := q.isLt
      omega
    exact htime.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left cleanupCoefficient hbase) _) _)
  · simpa only [hbank] using hrun

#print axioms bit_step

end
end EthInapproximability.CurrentPaper.RoundedCodeStep
