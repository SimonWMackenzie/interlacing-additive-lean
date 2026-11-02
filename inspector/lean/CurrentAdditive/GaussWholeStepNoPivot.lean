import CurrentAdditive.GaussWholeStepActiveFront
import CurrentAdditive.GaussWholeStepFieldsFinish

namespace CurrentAdditive.GaussWholeStepNoPivot
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram

/-- The fixed whole-step machine actually finds that no pivot remains in the
current column, bypasses the matrix rewrite, increments the column, and emits
the exact next state word. This is execution correctness; a uniform clock for
the complete step is recorded separately. -/
theorem detailed_noPivot {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=none) :
    ∃ a≤GaussPreparedGuard64.clock s+GaussGuardedFront64.activeClock s+2,
      ∃vf,∃Sf : Fin 32 → List Bool,
      run a (initial (GaussControlTrace.statePacket s))=
        ⟨some .afterFront,eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)),
          frame (GaussPivotSearchHigh64.searched s Sf)⟩ ∧
      ∃T≤a+2+GaussNextStateFieldsFrame64.noPivotClock s
        (GaussPivotSearchHigh64.searched s Sf) ((GaussPivotSearchHigh64.searched s Sf) 22)+
        ((GaussPivotSearchHigh64.searched s Sf) 62).length+
        2*(GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s)).length+8,
        machine.OutputsWithin (GaussControlTrace.statePacket s)
          (GaussControlTrace.statePacket (GaussControlTrace.step s)) T := by
  obtain ⟨a,ha,vf,Sf,hfront,hfacts⟩ := GaussWholeStepActiveFront.active_front s hr hc
  let S := GaussPivotSearchHigh64.searched s Sf
  have htag : S 20=[false] := by
    simpa only [GaussWholeStepActiveFront.no_pivot_tag s hc hp] using hfacts.found
  have hdispatch := active_dispatch vf (frame S)
  have hchoice := choose_pivot false
    (eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)))
    (frame S) (by rw [GaussSearchGridInvoke.frame_at,htag])
  simp only [Bool.false_eq_true,↓reduceIte] at hchoice
  have hprefix : run (a+1+1) (initial (GaussControlTrace.statePacket s))=
      ⟨some (.fields GaussNextStateFields64.start),eFields GaussNextStateFields64.control,frame S⟩ := by
    rw [show a+1+1=a+(1+1) by omega,run_add hfront (1+1),run_add hdispatch 1]
    exact hchoice
  obtain ⟨b,hb,v,T,hfields,h14,hframe⟩ :=
    GaussNextStateFieldsFrame64.physical_noPivot_framed s S (S 22) hfacts.original htag rfl
      (GaussSearchGridInvoke.searched_scratch63 s Sf)
  obtain ⟨c,hc',w,U,hfinish,hout⟩ := GaussWholeStepFieldsFinish.physical_finish S T b v
    (GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s)) hfields h14
    (hframe 62 (by decide))
    ((hframe 63 (by decide)).trans (GaussSearchGridInvoke.searched_scratch63 s Sf))
  have hfinal : run (a+1+1+c) (initial (GaussControlTrace.statePacket s))=⟨none,w,U⟩ := by
    rw [run_add hprefix c]
    exact hfinish
  have hstep : GaussControlTrace.step s=GaussBranchFields32.noPivotState s := by
    simp [GaussControlTrace.step,hr,hc,hp,GaussBranchFields32.noPivotState]
  refine ⟨a,ha,vf,Sf,hfront,a+1+1+c,?_,?_⟩
  · dsimp only [S] at hb hc'
    omega
  apply outputsWithin_of_raw_run (low 30) (low 62) start GaussWholeStepProgram.control program
    (GaussControlTrace.statePacket s) (GaussControlTrace.statePacket (GaussControlTrace.step s))
    (a+1+1+c) _ le_rfl
  · change (run (a+1+1+c) (initial (GaussControlTrace.statePacket s))).l=none
    rw [hfinal]
  · change (run (a+1+1+c) (initial (GaussControlTrace.statePacket s))).stk (low 62)=_
    rw [hfinal]
    exact hout.trans (congrArg GaussControlTrace.statePacket hstep.symm)

theorem outputs_noPivot {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=none) :
    ∃ T : Nat,machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s)) T := by
  obtain ⟨a,ha,vf,Sf,hfront,T,hT,hout⟩:=detailed_noPivot s hr hc hp
  exact ⟨T,hout⟩

#print axioms detailed_noPivot
#print axioms outputs_noPivot
end
end CurrentAdditive.GaussWholeStepNoPivot
