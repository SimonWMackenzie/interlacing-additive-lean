import CurrentAdditive.RoundedCodeBranchReadback
import CurrentAdditive.RoundedCodeStepClock

namespace EthInapproximability.CurrentPaper.RoundedCodeStep

open Turing BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
noncomputable section

theorem branch_step (root : Code) (s : State) (hp : PositiveState s) (ht : Trace root s)
    (a b : ℕ) (ha : 0 < a) (cut₁ cut₂ : ℕ) (first second third : Code)
    (cs : List Code) (out : List Bool)
    (hs : Paper2.GeneratorCode.normalize s =
      ⟨.branch3 a cut₁ cut₂ first second third :: cs, out⟩)
    (bits : Fin b → Bool) (suffix : List Bool) :
    let q := CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
      (Paper2.CappedSampler.bitsTicketEquiv b bits)
    let selected := if q.val < cut₁ then first else if q.val < cut₂ then second else third
    ∃ t ≤ cleanupCoefficient *
        (13 * (codeSize root + 3) ^ 2 + 1 +
          RoundedLoadedClock.coefficient * (a + b + 2) ^ 2 +
          (1 + 70 * (a + cut₁ + cut₂ +
            (Paper2.BranchSelection.inputWord first second third
              (Paper2.CodeAdminNormalization.todoWord cs)).length + 1)) + 1) +
            RoundedCodeReset.clearCount + 3,
      run t (start s (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) b) =
        ⟨none, finalControl false, (RoundedCodeAdmin.start ⟨selected :: cs, out⟩ suffix b).stk⟩ := by
  let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
  let q := CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
    (Paper2.CappedSampler.bitsTicketEquiv b bits)
  let ticket := (Paper2.RecursiveLabelCodecScratch.finCodec a).encode q
  let head := Code.branch3 a cut₁ cut₂ first second third
  let S := RoundedCodeAdmin.readyOldBank ⟨head :: cs, out⟩ input b
  let T := RoundedCodeDraw.resultBank S a b input suffix ticket
  obtain ⟨u, hu, hur⟩ := RoundedCodeAdmin.normalize_run root s hp ht input b
  rw [hs] at hur
  obtain ⟨v, hv, hvr⟩ := RoundedCodeAdmin.branch_from_ready a b ha cut₁ cut₂
    first second third cs out bits suffix
  let d : RoundedCodeAdmin.Config :=
    ⟨none, (RoundedCodeAdmin.kindControl .branch3, RoundedLoadedDraw.initial), T⟩
  have hadmin : RoundedCodeAdmin.run (u + v) (RoundedCodeAdmin.start s input b) = d := by
    rw [RoundedCodeAdmin.run, Nat.add_comm u v, Function.iterate_add_apply]
    change RoundedCodeAdmin.run v (RoundedCodeAdmin.run u _) = _
    rw [hur]
    exact hvr
  have hsource : (Paper2.CodeBranchAdapter.initial RoundedCodeHandle.successBase
      (fun k => T (.inl k)) (List.replicate a true) out.reverse q.val cut₁ cut₂
      first second third (Paper2.CodeAdminNormalization.todoWord cs)).stk =
      fun k => T (.inl k) :=
    RoundedCodeHandle.current_branch_initial a b cut₁ cut₂ q first second third cs out input suffix
  obtain ⟨w, hw, hwr⟩ := RoundedCodeHandle.branch_from_bank T (List.replicate a true)
    out.reverse q.val cut₁ cut₂ first second third
    (Paper2.CodeAdminNormalization.todoWord cs) hsource
  let e := RoundedCodeHandle.framedBranch T
    (Paper2.CodeBranchAdapter.final RoundedCodeHandle.successBase (fun k => T (.inl k))
      (List.replicate a true) out.reverse q.val cut₁ cut₂ first second third
      (Paper2.CodeAdminNormalization.todoWord cs))
  obtain ⟨t, htime, hrun⟩ := compose_source_success_clock s input b d (u + v) hadmin rfl
    .branch3 rfl e w hwr rfl
  have hbank : RoundedCodeReset.resetBank e.stk =
      (RoundedCodeAdmin.start
        ⟨(if q.val < cut₁ then first else if q.val < cut₂ then second else third) :: cs, out⟩ suffix b).stk :=
    RoundedCodeHandle.branch_reset_bank T a b cut₁ cut₂ q.val first second third cs out suffix
      (RoundedCodeDraw.result_tape S a b input suffix ticket)
      (RoundedCodeDraw.result_width S a b input suffix ticket)
  refine ⟨t, ?_, ?_⟩
  · have hq := q.isLt
    have hselector : w ≤ 1 + 70 * (a + cut₁ + cut₂ +
        (Paper2.BranchSelection.inputWord first second third
          (Paper2.CodeAdminNormalization.todoWord cs)).length + 1) := by omega
    have hbase : u + v + w + 1 ≤
        13 * (codeSize root + 3) ^ 2 + 1 +
          RoundedLoadedClock.coefficient * (a + b + 2) ^ 2 +
          (1 + 70 * (a + cut₁ + cut₂ +
            (Paper2.BranchSelection.inputWord first second third
              (Paper2.CodeAdminNormalization.todoWord cs)).length + 1)) + 1 := by omega
    exact htime.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left cleanupCoefficient hbase) _) _)
  · simpa only [hbank] using hrun

#print axioms branch_step

end
end EthInapproximability.CurrentPaper.RoundedCodeStep
