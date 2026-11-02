import CurrentAdditive.RoundedCodeStepClock
import CurrentAdditive.RoundedCodeHandleReadback

namespace EthInapproximability.CurrentPaper.RoundedCodeStep

open Turing BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
noncomputable section

private theorem admin_join {c d : RoundedCodeAdmin.Config} {u : ℕ}
    (h : RoundedCodeAdmin.run u c = d) (v : ℕ) :
    RoundedCodeAdmin.run (u + v) c = RoundedCodeAdmin.run v d := by
  rw [Nat.add_comm u v]
  simp only [RoundedCodeAdmin.run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-- A complete physical ticket step from the encoded source state, including
normalization, full-block rounding, unary output append and complete reset.
The returned bank is exactly the canonical next source state; no scratch-size
or prepared endpoint premise occurs. -/
theorem ticket_step (root : Code) (s : State) (hp : PositiveState s) (ht : Trace root s)
    (a b : ℕ) (ha : 0 < a) (cs : List Code) (out : List Bool)
    (hs : Paper2.GeneratorCode.normalize s = ⟨.ticket a :: cs, out⟩)
    (bits : Fin b → Bool) (suffix : List Bool) :
    let q := CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
      (Paper2.CappedSampler.bitsTicketEquiv b bits)
    let word := (Paper2.RecursiveLabelCodecScratch.finCodec a).encode q
    ∃ t ≤ cleanupCoefficient *
        (13 * (codeSize root + 3) ^ 2 + 1 +
          RoundedLoadedClock.coefficient * (a + b + 2) ^ 2 + (a + 2) + 1) +
            RoundedCodeReset.clearCount + 3,
      run t (start s (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) b) =
        ⟨none, finalControl false, (RoundedCodeAdmin.start ⟨cs, out ++ word⟩ suffix b).stk⟩ := by
  let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
  let q := CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
    (Paper2.CappedSampler.bitsTicketEquiv b bits)
  let word := (Paper2.RecursiveLabelCodecScratch.finCodec a).encode q
  let S := RoundedCodeAdmin.readyOldBank ⟨.ticket a :: cs, out⟩ input b
  obtain ⟨u, hu, hur⟩ := RoundedCodeAdmin.normalize_run root s hp ht input b
  rw [hs] at hur
  obtain ⟨v, hv, hvr⟩ := RoundedCodeAdmin.ticket_from_ready a b ha cs out bits suffix
  let d : RoundedCodeAdmin.Config :=
    ⟨none, (RoundedCodeAdmin.kindControl .ticket, RoundedLoadedDraw.initial),
      RoundedCodeDraw.resultBank S a b input suffix word⟩
  have hadmin : RoundedCodeAdmin.run (u + v) (RoundedCodeAdmin.start s input b) = d :=
    (admin_join hur v).trans hvr
  have hi : d.stk (.inl RoundedCodeDraw.oldResult) = word :=
    RoundedCodeDraw.result_word S a b input suffix word
  have ho : d.stk (.inl Paper2.CodeHeaderDraw.output) = out.reverse := by
    change RoundedCodeDraw.resultBank S a b input suffix word (.inl Paper2.CodeHeaderDraw.output) = _
    rw [RoundedCodeDraw.result_other_old S a b input suffix word Paper2.CodeHeaderDraw.output]
    · rfl
    all_goals simp [RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth,
      RoundedCodeDraw.oldTape, RoundedCodeDraw.oldResult,
      Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]
  obtain ⟨w, hw, hwr⟩ := RoundedCodeHandle.ticket_run d.stk word out.reverse hi ho
  let e := RoundedCodeHandle.framedOutput d.stk
    (Paper2.CodeDrawOutput.cfg none none [] (word.reverse ++ out.reverse))
  obtain ⟨t, htime, hrun⟩ := compose_source_success_clock s input b d (u + v) hadmin rfl
    .ticket rfl e w hwr rfl
  have hbank : RoundedCodeReset.resetBank e.stk =
      (RoundedCodeAdmin.start ⟨cs, out ++ word⟩ suffix b).stk :=
    RoundedCodeHandle.ticket_reset_bank S a b input suffix word cs out (by rfl)
  have hlen := (Paper2.RecursiveLabelCodecScratch.finCodec a).length_le q
  change word.length ≤ a at hlen
  refine ⟨t, ?_, ?_⟩
  · have hbase : u + v + w + 1 ≤
        13 * (codeSize root + 3) ^ 2 + 1 +
          RoundedLoadedClock.coefficient * (a + b + 2) ^ 2 + (a + 2) + 1 := by omega
    exact htime.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left cleanupCoefficient hbase) _) _)
  · simpa only [hbank] using hrun

#print axioms ticket_step

end
end EthInapproximability.CurrentPaper.RoundedCodeStep
