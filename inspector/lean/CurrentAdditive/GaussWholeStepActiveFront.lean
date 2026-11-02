import CurrentAdditive.GaussWholeStepTerminal
import CurrentAdditive.GaussGuardedFrontFields64

namespace CurrentAdditive.GaussWholeStepActiveFront
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram

theorem active_front {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) :
    ∃ t≤GaussPreparedGuard64.clock s+GaussGuardedFront64.activeClock s+2,
      ∃ vf,∃ Sf : Fin 32 → List Bool,
      run t (initial (GaussControlTrace.statePacket s))=
        ⟨some .afterFront,eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)),
          frame (GaussPivotSearchHigh64.searched s Sf)⟩ ∧
      GaussGuardedFrontFields64.SearchFields s hc Sf := by
  obtain ⟨a,ha,vf,Sf,hfront,hfields⟩ := GaussGuardedFrontFields64.active_run_fields s hr hc
  let S := GaussPivotSearchHigh64.searched s Sf
  have hhalt : ((advance GaussGuardedFront64.program)^[a+1])
      (GaussGuardedFront64.initial s)=
      ⟨none,GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf),S⟩ := by
    rw [Function.iterate_succ_apply',←GaussGuardedFront64.run,hfront]
    rfl
  obtain ⟨b,hb,hwide⟩ := BitMachineStackEmbedding.outputs low (fun _ : Bank => []) id id id
    (fun _ => rfl) none GaussGuardedFront64.program frontProgram (fun _ => rfl)
    (GaussGuardedFront64.initial s) (a+1) (by rw [hhalt])
  rw [hhalt] at hwide
  have hwide' : ((advance frontProgram)^[b])
      (⟨some (.base (BitMachineRawSequence.leftLabel (.copy .scan))),frontInit,
        frame (GaussGuardedFront64.initial s).stk⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=
      ⟨none,GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf),frame S⟩ := hwide
  obtain ⟨c,hc',hglobal⟩ := BitMachineInline.outputs Label.front eFront Prod.fst
    (fun _ => rfl) (some .afterFront) frontProgram program (fun _ => rfl)
    (⟨some (.base (BitMachineRawSequence.leftLabel (.copy .scan))),frontInit,
      frame (GaussGuardedFront64.initial s).stk⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)
    b (by rw [hwide'])
  rw [hwide'] at hglobal
  refine ⟨c,by omega,vf,Sf,?_,hfields⟩
  rw [GaussWholeStepTerminal.initial_frame]
  exact hglobal

theorem no_pivot_tag {m k : Nat} (s : GaussControlTrace.State m k) (hc : s.c < k)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=none) :
    (GaussFlagSearch.firstHit ((List.finRange m).map
      (fun i => decide (s.B i ⟨s.c,hc⟩≠0))) s.r).1=false := by
  have h := GaussPivotSearchSemantic.selected_pivot_val s.B ⟨s.c,hc⟩ s.r
  rw [hp] at h
  cases he : GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (s.B i ⟨s.c,hc⟩≠0))) s.r with
  | mk found index =>
    cases found
    · rfl
    · change none=GaussFlagSearch.selected
        ((List.finRange m).map (fun i => decide (s.B i ⟨s.c,hc⟩≠0))) s.r at h
      unfold GaussFlagSearch.selected at h
      rw [he] at h
      simp at h

#print axioms active_front
#print axioms no_pivot_tag
end
end CurrentAdditive.GaussWholeStepActiveFront
