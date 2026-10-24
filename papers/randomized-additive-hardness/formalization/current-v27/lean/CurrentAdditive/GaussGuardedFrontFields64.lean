import CurrentAdditive.GaussGuardedFront64

/-! Additive output-field re-export for the unchanged guarded front program.
The original theorem discarded these fields when destructuring its actual
search execution. All facts below come from that execution, not premises. -/

namespace CurrentAdditive.GaussGuardedFrontFields64
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussGuardedFront64

structure SearchFields {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) (Sf : Fin 32 → List Bool) : Prop where
  selected : GaussPivotSearchHigh64.searched s Sf 19=
    List.replicate (GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (s.B i ⟨s.c,hc⟩≠0))) s.r).2 true
  found : GaussPivotSearchHigh64.searched s Sf 20=
    [(GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (s.B i ⟨s.c,hc⟩≠0))) s.r).1]
  matrix : GaussPivotSearchHigh64.searched s Sf 8=GaussPhysical.encodeTypedMatrix s.B
  row : GaussPivotSearchHigh64.searched s Sf 53=List.replicate s.r true
  column : GaussPivotSearchHigh64.searched s Sf 55=List.replicate s.c true
  original : GaussPivotSearchHigh64.searched s Sf 56=GaussControlTrace.statePacket s
  count : GaussPivotSearchHigh64.searched s Sf 58=List.replicate m true

theorem active_from_prepared_fields {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) :
    ∃ t ≤ activeClock s, ∃ vf, ∃ Sf : Fin 32 → List Bool,
      ((advance activeProgram)^[t])
        (⟨some activeStart,activeInit,GaussPivotPrepHigh64.prepared s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,(copyInit,.choose vf),GaussPivotSearchHigh64.searched s Sf⟩ ∧
      SearchFields s hc Sf := by
  obtain ⟨a,ha,hcopy⟩ := GaussPivotPrepSave64.copy_run s
  obtain ⟨b,hb,vf,Sf,hsearch,h19,h20,h8,h53,h55,h56,h58⟩ :=
    GaussPhysicalSearchClock.physical_search_clock s hc
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    GaussPivotPrepSave64.copyProgram GaussPivotSearchHigh64.program
    copyStart GaussPivotPrepSearchHigh64.searchLabel
    copyInit copyInit searchInit (.choose vf)
    (GaussPivotPrepHigh64.prepared s) (GaussPivotPrepSave64.saved s)
    (GaussPivotSearchHigh64.searched s Sf) a b
    (by simpa only [copyStart,copyInit] using hcopy)
    (by simpa only [GaussPivotPrepSearchHigh64.searchLabel,searchInit,
      GaussPivotPrepSearchHigh64.searchControl] using hsearch)
  refine ⟨t,by dsimp [activeClock]; omega,vf,Sf,?_,?_⟩
  · simpa only [activeProgram,activeStart,activeInit] using he
  · exact ⟨h19,h20,h8,h53,h55,h56,h58⟩

/-- The same actual guard/copy/search instruction table returns every
physical field needed by the next grid/branch consumers at its same clock. -/
theorem active_run_fields {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) :
    ∃ t ≤ GaussPreparedGuard64.clock s + 1 + activeClock s,
      ∃ vf, ∃ Sf : Fin 32 → List Bool,
        run t (initial s) =
          ⟨some .doneActive,eActive (copyInit,.choose vf),
            GaussPivotSearchHigh64.searched s Sf⟩ ∧ SearchFields s hc Sf := by
  obtain ⟨a,ha,hguard⟩ := guard_phase s
  have hb := branch_active s hr
  obtain ⟨c,hc',vf,Sf,hsearch,hfields⟩ := active_from_prepared_fields s hc
  obtain ⟨d,hd,he⟩ := BitMachineInline.outputs
    Label.active eActive (fun v => v.2.1) (by intro v; rfl)
    (some .doneActive) activeProgram program (by intro l; rfl)
    (⟨some activeStart,activeInit,GaussPivotPrepHigh64.prepared s⟩)
    c (by rw [hsearch])
  change run d _ = BitMachineInline.cfg Label.active eActive
    (some .doneActive) _ at he
  rw [hsearch] at he
  have hactive : run d
      ⟨some (.active activeStart),eActive activeInit,GaussPivotPrepHigh64.prepared s⟩ =
      ⟨some .doneActive,eActive (copyInit,.choose vf),
        GaussPivotSearchHigh64.searched s Sf⟩ := by
    simpa only [BitMachineInline.cfg] using he
  refine ⟨a+1+d,by omega,vf,Sf,?_,hfields⟩
  rw [show a+1+d=a+(1+d) by omega,run_add hguard (1+d),run_add hb d]
  exact hactive

#print axioms active_from_prepared_fields
#print axioms active_run_fields
end
end CurrentAdditive.GaussGuardedFrontFields64
