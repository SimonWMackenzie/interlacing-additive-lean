import CurrentAdditive.GaussWholeStepActiveFront
import CurrentAdditive.GaussWholeStepFieldsFinish

namespace CurrentAdditive.GaussWholeStepPivot
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram

theorem finalBank_frame (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool) (answer : List Bool) :
    GaussSearchGridInvoke.finalBank S sf answer=
      frame (Function.update (GaussSearchGridInvoke.serialized64 S sf) 22 answer) := by
  exact (BitMachineStackEmbedding.bank_update low (fun _ : Bank => [])
    (GaussSearchGridInvoke.serialized64 S sf) 22 answer).symm

/-- The whole-step machine finds its own pivot, constructs the serialized
grid operands, invokes the actual complete matrix rewrite, rebuilds the
ordered pivot/state packet, and transfers that exact state to its output.
No pivot tag, rewrite matrix or prepared intermediate bank is supplied. -/
theorem detailed_pivot {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=some pivot)
    (hcount : s.r=s.pivots.length) :
    ∃ a≤GaussPreparedGuard64.clock s+GaussGuardedFront64.activeClock s+2,
      ∃vf,∃Sf : Fin 32 → List Bool,
      let S:=GaussPivotSearchHigh64.searched s Sf
      run a (initial (GaussControlTrace.statePacket s))=
        ⟨some .afterFront,eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)),frame S⟩ ∧
      ∃d≤GaussSearchGridInvoke.clock S,∃sf : Fin 4 → List Bool,
      let R:=Function.update (GaussSearchGridInvoke.serialized64 S sf) 22
        (GaussGridPreparedInput.answer s.B ⟨s.r,hr⟩ pivot ⟨s.c,hc⟩)
      run d ⟨some (.rewrite GaussSearchGridInvoke.start),eRewrite GaussSearchGridInvoke.control,frame S⟩=
        ⟨some .afterRewrite,eRewrite GaussSearchGridInvoke.control,frame R⟩ ∧
      ∃T≤a+2+d+1+GaussNextStateFields64.pivotClock s R hr hc+(R 62).length+
        2*(GaussControlTrace.statePacket (GaussControlTrace.step s)).length+8,
        machine.OutputsWithin (GaussControlTrace.statePacket s)
          (GaussControlTrace.statePacket (GaussControlTrace.step s)) T := by
  obtain ⟨a,ha,vf,Sf,hfront,hfacts⟩ := GaussWholeStepActiveFront.active_front s hr hc
  let S := GaussPivotSearchHigh64.searched s Sf
  let r : Fin m := ⟨s.r,hr⟩
  let c : Fin k := ⟨s.c,hc⟩
  have hhit := GaussSearchGridBridge64.firstHit_pivot s hc pivot hp
  change GaussFlagSearch.firstHit ((List.finRange m).map
    (fun i => decide (s.B i ⟨s.c,hc⟩≠0))) s.r=(true,pivot.val) at hhit
  have htag : S 20=[true] := by simpa only [S,hhit] using hfacts.found
  have hselected : S 19=List.replicate pivot.val true := by simpa only [S,hhit] using hfacts.selected
  have hpacket : GaussSearchGridInput64.packet S=
      BitMachineBankCodec.encode (GaussGridPreparedInput.rawWords s.B r pivot c) := by
    exact GaussSearchGridBridge64.packet_exact s S pivot.val hfacts.matrix hfacts.row
      hselected hfacts.column
  have hn : s.B pivot c≠0 := (SequentialTotality.pivotTyped_spec s.B s.r c pivot hp).2
  have hdispatch := active_dispatch vf (frame S)
  have hchoice := choose_pivot true
    (eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)))
    (frame S) (by rw [GaussSearchGridInvoke.frame_at,htag])
  simp only [↓reduceIte] at hchoice
  have hprefix : run (a+1+1) (initial (GaussControlTrace.statePacket s))=
      ⟨some (.rewrite GaussSearchGridInvoke.start),eRewrite GaussSearchGridInvoke.control,frame S⟩ := by
    rw [show a+1+1=a+(1+1) by omega,run_add hfront (1+1),run_add hdispatch 1]
    exact hchoice
  obtain ⟨b,hb,sf,hrewrite⟩ := GaussSearchGridInvoke.physical_rewrite s.B r pivot c hn S hpacket
    (GaussSearchGridBridge64.searched_scratch_empty s Sf 60 (by decide) (by decide))
    (GaussSearchGridBridge64.searched_scratch_empty s Sf 61 (by decide) (by decide))
    (GaussSearchGridBridge64.searched_scratch_empty s Sf 62 (by decide) (by decide))
    (GaussSearchGridInvoke.searched_scratch63 s Sf)
  let answer := GaussGridPreparedInput.answer s.B r pivot c
  let R := Function.update (GaussSearchGridInvoke.serialized64 S sf) 22 answer
  have hmatrix : answer=GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B := by
    simp [answer,GaussGridPreparedInput.answer,GaussControlTrace.step,hr,hc,hp,r,c,
      MaterializedGauss.materialize_eq]
  rw [finalBank_frame] at hrewrite
  obtain ⟨d,hd,hrewGlobal⟩ := BitMachineInline.outputs Label.rewrite eRewrite readRewrite
    (fun _ => rfl) (some .afterRewrite) GaussSearchGridInvoke.program program (fun _ => rfl)
    (⟨some GaussSearchGridInvoke.start,GaussSearchGridInvoke.control,frame S⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _) b (by rw [hrewrite])
  rw [hrewrite] at hrewGlobal
  have hrew : run d
      ⟨some (.rewrite GaussSearchGridInvoke.start),eRewrite GaussSearchGridInvoke.control,frame S⟩=
      ⟨some .afterRewrite,eRewrite GaussSearchGridInvoke.control,frame R⟩ := hrewGlobal
  have hafter : run 1 ⟨some .afterRewrite,eRewrite GaussSearchGridInvoke.control,frame R⟩=
      ⟨some (.fields GaussNextStateFields64.start),eFields GaussNextStateFields64.control,frame R⟩ := rfl
  have hR20 : R 20=[true] := by
    simp only [R,Function.update_of_ne (by decide : (20 : Fin 64)≠22)]
    rw [GaussSearchGridInvoke.serialized_other S sf 20 (by decide),htag]
  have hR56 : R 56=GaussControlTrace.statePacket s := by
    simp only [R,Function.update_of_ne (by decide : (56 : Fin 64)≠22)]
    rw [GaussSearchGridInvoke.serialized_other S sf 56 (by decide)]
    exact hfacts.original
  have hR63 : R 63=[] := by
    simp only [R,Function.update_of_ne (by decide : (63 : Fin 64)≠22)]
    rw [GaussSearchGridInvoke.serialized_other S sf 63 (by decide)]
    exact GaussSearchGridInvoke.searched_scratch63 s Sf
  have hR22 : R 22=GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B := by simp [R,hmatrix]
  obtain ⟨e,he,v,T,hfields,h14,hframe⟩ := GaussNextStateFieldsFrame64.physical_pivot_framed s
    hr hc pivot hp hcount R hR56 hR20 hR22 hR63
  obtain ⟨f,hf,w,U,hfinish,hout⟩ := GaussWholeStepFieldsFinish.physical_finish R T e v
    (GaussControlTrace.statePacket (GaussControlTrace.step s)) hfields h14
    (hframe 62 (by decide)) ((hframe 63 (by decide)).trans hR63)
  have hfinal : run (a+1+1+d+1+f) (initial (GaussControlTrace.statePacket s))=⟨none,w,U⟩ := by
    rw [show a+1+1+d+1+f=(a+1+1)+(d+(1+f)) by omega,run_add hprefix (d+(1+f)),
      run_add hrew (1+f),run_add hafter f]
    exact hfinish
  refine ⟨a,ha,vf,Sf,hfront,d,hd.trans hb,sf,hrew,a+1+1+d+1+f,?_,?_⟩
  · dsimp only [R,answer,r,c,S] at he hf
    omega
  apply outputsWithin_of_raw_run (low 30) (low 62) start GaussWholeStepProgram.control program
    (GaussControlTrace.statePacket s) (GaussControlTrace.statePacket (GaussControlTrace.step s))
    (a+1+1+d+1+f) _ le_rfl
  · change (run (a+1+1+d+1+f) (initial (GaussControlTrace.statePacket s))).l=none
    rw [hfinal]
  · change (run (a+1+1+d+1+f) (initial (GaussControlTrace.statePacket s))).stk (low 62)=_
    rw [hfinal]
    exact hout

theorem outputs_pivot {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=some pivot)
    (hcount : s.r=s.pivots.length) :
    ∃ T : Nat,machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s)) T := by
  obtain ⟨a,ha,vf,Sf,hfront,d,hd,sf,hrew,T,hT,hout⟩:=detailed_pivot s hr hc pivot hp hcount
  exact ⟨T,hout⟩

#print axioms detailed_pivot
#print axioms outputs_pivot
end
end CurrentAdditive.GaussWholeStepPivot
