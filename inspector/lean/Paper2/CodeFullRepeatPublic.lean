import Paper2.CodeFullRepeatPath
import Paper2.CodeRawStepPublicBound
import Mathlib.Tactic

/-! A same-witness public cap for one successful reentry or terminal stop.
The constructor-specific raw clock cap is supplied by the frozen public-bound
module; no independent reset-bank witness is chosen. -/

namespace Paper2.CodeFullRepeatPublic

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize

noncomputable section

def repeatStepCap (root : Code) (B R : Nat) : Nat :=
  CodeFullCleanBound.publicStepCap
    (CodeRawStepPublicBound.rawStepCap root B R) + 1

theorem reenter_public_from_reached (root : Code)
    (s next : State) (tape residual : List Bool) (B R : Nat)
    (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (ht : t ≤ CodeRawStepPublicBound.rawStepCap root B R)
    (hs : CodeFullRepeat.success ((d.var,none) : CodeFullRepeat.Control) = true)
    (hbank : (CodeInterpreterReset.final d.var d.stk).stk =
      (CodeAdminBranchJoin.start next residual B R).stk) :
    ∃ u ≤ repeatStepCap root B R,
      CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
        CodeFullRepeat.start next residual B R := by
  obtain ⟨u,hu,hru⟩ := CodeFullRepeat.reenter_from_reached
    s next tape residual B R d t hr hd hs hbank
  have hc := CodeUniformResetBound.raw_terminal_clock_mono
    s tape B R t (CodeRawStepPublicBound.rawStepCap root B R) d hr ht
  refine ⟨u,?_,hru⟩
  unfold repeatStepCap CodeFullCleanBound.publicStepCap
  omega

theorem stop_public_from_reached (root : Code)
    (s : State) (tape : List Bool) (B R : Nat)
    (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (ht : t ≤ CodeRawStepPublicBound.rawStepCap root B R)
    (hs : CodeFullRepeat.success ((d.var,none) : CodeFullRepeat.Control) = false) :
    ∃ u ≤ repeatStepCap root B R,
      CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
        ⟨none,(d.var,none),CodeInterpreterReset.resetBank d.stk⟩ := by
  obtain ⟨u,hu,hru⟩ := CodeFullRepeat.stop_from_reached
    s tape B R d t hr hd hs
  have hc := CodeUniformResetBound.raw_terminal_clock_mono
    s tape B R t (CodeRawStepPublicBound.rawStepCap root B R) d hr ht
  refine ⟨u,?_,hru⟩
  unfold repeatStepCap CodeFullCleanBound.publicStepCap
  omega

theorem accepted_run_public {root : Code} {B R : Nat}
    {s s' : State} {tape tape' : List Bool}
    (h : CodeFullRepeatPath.Accepted root B R s tape s' tape') :
    ∃ u ≤ repeatStepCap root B R,
      CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
        CodeFullRepeat.start s' tape' B R := by
  cases h with
  | ticket hp ht D hD cs out hstate N hB tape q hq =>
      obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.ticket_public
        root _ hp ht D hD cs out hstate B R N hB tape q hq
      let raw := CodeAdminDraw.drawResult D B R N hB tape .ticket
        (CodeAdminNormalization.todoWord cs) (List.replicate D true)
        [] [] out F
      let handled := CodeDrawResultHandler.framed raw.var raw.stk
        (CodeDrawOutput.cfg none none []
          (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ out))
      let joined := CodeAdminResultJoin.resultCfg handled
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
      have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape
        .ticket (CodeAdminNormalization.todoWord cs)
        (List.replicate D true) [] [] out F).1
      have hs : CodeFullRepeat.success ((endpoint.var,none) :
          CodeFullRepeat.Control) = true := by
        change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
        rw [hsraw,hq]; rfl
      have hbank := CodeFullCleanMeaning.ticket_ready_bank D B R N hD hB
        tape cs out.reverse F q
      have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
          (CodeAdminBranchJoin.start
            (GeneratorCode.advance ⟨.ticket D::cs,out.reverse⟩ q.val)
            (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
        simpa [raw,handled,joined,endpoint] using hbank
      exact reenter_public_from_reached root _ _ _ _ B R endpoint t
        hr rfl ht0 hs hbank'

  | bit hp ht cs out hstate N hB tape q hq =>
      obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.bit_public
        root _ hp ht cs out hstate B R N hB tape q hq
      let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
        (CodeAdminNormalization.todoWord cs) [] [] [] out F
      let handled := CodeDrawResultHandler.framed raw.var raw.stk
        (CodeDrawOutput.cfg none none [] (decide (q.val=1)::out))
      let joined := CodeAdminResultJoin.resultCfg handled
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
      have hsraw := (CodeDrawResultHandler.result_status 2 B R N hB tape
        .bit (CodeAdminNormalization.todoWord cs) [] [] [] out F).1
      have hs : CodeFullRepeat.success ((endpoint.var,none) :
          CodeFullRepeat.Control) = true := by
        change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
        rw [hsraw,hq]; rfl
      have hbank := CodeFullCleanMeaning.bit_ready_bank B R N hB
        tape cs out.reverse F q
      have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
          (CodeAdminBranchJoin.start
            (GeneratorCode.advance ⟨.bit::cs,out.reverse⟩ q.val)
            (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
        simpa [raw,handled,joined,endpoint] using hbank
      exact reenter_public_from_reached root _ _ _ _ B R endpoint t
        hr rfl ht0 hs hbank'

  | branch hp ht D a b hD f g h cs out hstate N hB tape q hq =>
      obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.branch_public
        root _ hp ht D a b hD f g h cs out hstate B R N hB tape q hq
      let tail := BranchSelection.inputWord f g h
        (CodeAdminNormalization.todoWord cs)
      let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3 tail
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F
      let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3 tail
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F
      let joined : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
      let selected := CodeBranchAdapter.final base.var base.stk
        (List.replicate D true) out q.val a b f g h
        (CodeAdminNormalization.todoWord cs)
      let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
      have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape
        .branch3 tail (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).1
      have hs : CodeFullRepeat.success ((endpoint.var,none) :
          CodeFullRepeat.Control) = true := by
        change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
        rw [hsraw,hq]; rfl
      have hbank := CodeFullCleanMeaning.branch_ready_bank D a b B R N
        hD hB tape f g h cs out.reverse F q
      have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
          (CodeAdminBranchJoin.start
            (GeneratorCode.advance
              ⟨.branch3 D a b f g h::cs,out.reverse⟩ q.val)
            (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
        simpa [tail,base,raw,joined,selected,endpoint] using hbank
      exact reenter_public_from_reached root _ _ _ _ B R endpoint t
        hr rfl ht0 hs hbank'

private theorem run_add (a b : Nat) (c : CodeFullRepeat.Config) :
    CodeFullRepeat.run (a+b) c =
      CodeFullRepeat.run b (CodeFullRepeat.run a c) := by
  change ((advance CodeFullRepeat.program)^[a+b]) c =
    ((advance CodeFullRepeat.program)^[b])
      (((advance CodeFullRepeat.program)^[a]) c)
  rw [Nat.add_comm a b,Function.iterate_add_apply]

theorem path_run_public {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (h : CodeFullRepeatPath.Path root B R s tape last tapeLast) :
    ∃ u ≤ h.length * repeatStepCap root B R,
      CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
        CodeFullRepeat.start last tapeLast B R := by
  induction h with
  | refl s tape =>
      exact ⟨0,by simp [CodeFullRepeatPath.Path.length],rfl⟩
  | cons head tail ih =>
      obtain ⟨a,ha,hra⟩ := accepted_run_public head
      obtain ⟨b,hb,hrb⟩ := ih
      refine ⟨a+b,?_,?_⟩
      · simp only [CodeFullRepeatPath.Path.length,Nat.add_mul]
        omega
      · rw [run_add a b,hra,hrb]

#print axioms reenter_public_from_reached
#print axioms stop_public_from_reached
#print axioms accepted_run_public
#print axioms path_run_public

end
end Paper2.CodeFullRepeatPublic
