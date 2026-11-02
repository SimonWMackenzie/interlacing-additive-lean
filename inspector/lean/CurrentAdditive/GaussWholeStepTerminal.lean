import CurrentAdditive.GaussWholeStepProgram

namespace CurrentAdditive.GaussWholeStepTerminal
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram

theorem old_start_bank {m k : Nat} (s : GaussControlTrace.State m k) :
    (GaussGuardedFront64.initial s).stk=(fun i : Fin 64 =>
      if i=30 then GaussControlTrace.statePacket s else []) := by
  change BitMachineStackEmbedding.bank GaussPivotPrepHigh64.low GaussPivotPrepHigh64.blank
    (GaussPivotInputCopy32.startBank (GaussControlTrace.statePacket s))=_
  funext i
  by_cases hi : ∃ j,GaussPivotPrepHigh64.low j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [BitMachineStackEmbedding.bank_at]
    simp only [GaussPivotInputCopy32.startBank]
    by_cases hj : j=30
    · subst j; rfl
    · have hn : GaussPivotPrepHigh64.low j≠30 := by
        intro he
        apply hj
        apply Fin.ext
        have hv := congrArg (fun z : Fin 64 => z.val) he
        exact hv
      simp [hj,hn]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hi]
    have hn : i≠30 := by intro he; subst i; exact hi ⟨30,rfl⟩
    simp [GaussPivotPrepHigh64.blank,hn]

theorem initial_frame {m k : Nat} (s : GaussControlTrace.State m k) :
    initial (GaussControlTrace.statePacket s)=
      (⟨some start,control,frame (GaussGuardedFront64.initial s).stk⟩ : Config) := by
  unfold initial rawInit
  congr 1
  rw [old_start_bank]
  funext z
  by_cases hz : ∃ i,low i=z
  · obtain ⟨i,rfl⟩ := hz
    rw [GaussSearchGridInvoke.frame_at]
    by_cases hi : i=30
    · subst i; simp
    · have hn : low i≠low 30 := fun he => hi (low.injective he)
      simp [hi,hn]
  · unfold GaussSearchGridInvoke.frame
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hz]
    have hn : z≠low 30 := fun he => hz ⟨30,he.symm⟩
    simp [hn]

def terminalClock {m k : Nat} (s : GaussControlTrace.State m k) : Nat :=
  GaussPreparedGuard64.clock s+2*(GaussControlTrace.statePacket s).length+7

/-- Exhausted rows take the actual preserving guard and terminal-copy path
of the same complete step program. They return the original state word. -/
theorem terminal_outputs {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : ¬s.r < m) :
    machine.OutputsWithin (GaussControlTrace.statePacket s) (GaussControlTrace.statePacket s)
      (terminalClock s) := by
  obtain ⟨a,ha,hfront,hout⟩ := GaussGuardedFront64.terminal_run s hr
  let S := GaussGuardedFront64.terminalResult s
  have hhalt : ((advance GaussGuardedFront64.program)^[a+1])
      (GaussGuardedFront64.initial s)=
      ⟨none,GaussGuardedFront64.eTerminal ((),none),S⟩ := by
    rw [Function.iterate_succ_apply',←GaussGuardedFront64.run,hfront]
    rfl
  obtain ⟨b,hb,hwide⟩ := BitMachineStackEmbedding.outputs low (fun _ : Bank => []) id id id
    (fun _ => rfl) none GaussGuardedFront64.program frontProgram (fun _ => rfl)
    (GaussGuardedFront64.initial s) (a+1) (by rw [hhalt])
  rw [hhalt] at hwide
  have hwide' : ((advance frontProgram)^[b])
      (⟨some (.base (BitMachineRawSequence.leftLabel (.copy .scan))),frontInit,
        frame (GaussGuardedFront64.initial s).stk⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=
      ⟨none,GaussGuardedFront64.eTerminal ((),none),frame S⟩ := hwide
  obtain ⟨c,hc,hglobal⟩ := BitMachineInline.outputs Label.front eFront Prod.fst
    (fun _ => rfl) (some .afterFront) frontProgram program (fun _ => rfl)
    (⟨some (.base (BitMachineRawSequence.leftLabel (.copy .scan))),frontInit,
      frame (GaussGuardedFront64.initial s).stk⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)
    b (by rw [hwide'])
  rw [hwide'] at hglobal
  have hrun : run c (initial (GaussControlTrace.statePacket s))=
      ⟨some .afterFront,eFront (GaussGuardedFront64.eTerminal ((),none)),frame S⟩ := by
    rw [initial_frame]
    exact hglobal
  have hfinal : run (c+1+1) (initial (GaussControlTrace.statePacket s))=
      ⟨none,eFront (GaussGuardedFront64.eTerminal ((),none)),frame S⟩ := by
    rw [show c+1+1=c+(1+1) by omega,run_add hrun (1+1)]
    rw [run_add (terminal_dispatch (frame S)) 1]
    rfl
  apply outputsWithin_of_raw_run (low 30) (low 62) start GaussWholeStepProgram.control program
    (GaussControlTrace.statePacket s) (GaussControlTrace.statePacket s) (c+1+1) _
    (by unfold terminalClock; omega)
  · change (run (c+1+1) (initial (GaussControlTrace.statePacket s))).l=none
    rw [hfinal]
  · change (run (c+1+1) (initial (GaussControlTrace.statePacket s))).stk (low 62)=_
    rw [hfinal]
    change frame S (low 62)=_
    rw [GaussSearchGridInvoke.frame_at]
    exact hout

#print axioms initial_frame
#print axioms terminal_outputs
end
end CurrentAdditive.GaussWholeStepTerminal
