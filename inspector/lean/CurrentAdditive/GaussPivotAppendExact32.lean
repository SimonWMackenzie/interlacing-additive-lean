import CurrentAdditive.GaussStepWriterResetRun32

/-! Exact endpoint of the checked pivot-body append, exposing untouched banks. -/

namespace CurrentAdditive.GaussPivotAppendExact32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32

def stageTarget (body payload : List Bool) (S : Stack → List Bool) :
    CurrentAdditive.CodeDAppendAtEnd15.Stack → List Bool :=
  let B := GaussPivotAppend32.localBank S
  Function.update (Function.update (Function.update B 9 []) 5 []) 9
    (body++payload)

theorem stage_exact (body payload : List Bool)
    (S : Stack → List Bool)
    (h27 : S 27 = body) (h26 : S 26 = payload)
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ 4*body.length+2*payload.length+7,
      GaussPivotAppend32.run t
        ⟨some (.append .saveScan),((),none),S⟩ =
      GaussPivotAppend32.appendFrame S
        ⟨none,((),none),stageTarget body payload S⟩ := by
  let B := GaussPivotAppend32.localBank S
  have h11 : B 11 = [] := by
    simpa [B,GaussPivotAppend32.localBank,
      GaussPivotAppend32.appendSlot] using h24
  have h14 : B 14 = [] := by
    simpa [B,GaussPivotAppend32.localBank,
      GaussPivotAppend32.appendSlot] using h31
  have hinit := GaussPivotAppend32.local_initial_eq S body payload h27 h26
  have hcore := CurrentAdditive.CodeDAppendAtEnd15.append_run
    B body payload h11 h14
  rw [hinit] at hcore
  have hhalt : CurrentAdditive.CodeDAppendAtEnd15.run
      (4*body.length+2*payload.length+7)
      ⟨some .saveScan,((),none),B⟩ =
      ⟨none,((),none),stageTarget body payload S⟩ := by
    rw [show 4*body.length+2*payload.length+7 =
      (4*body.length+2*payload.length+6)+1 by omega]
    rw [CurrentAdditive.CodeDAppendAtEnd15.run]
    rw [Nat.add_comm,Function.iterate_add_apply]
    change CurrentAdditive.CodeDAppendAtEnd15.run 1
      (CurrentAdditive.CodeDAppendAtEnd15.run
        (4*body.length+2*payload.length+6)
        ⟨some .saveScan,((),none),B⟩) = _
    rw [hcore]
    rfl
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    GaussPivotAppend32.appendSlot S GaussPivotAppend32.Label.append
    id id (by intro q; rfl) (some .done)
    CurrentAdditive.CodeDAppendAtEnd15.program
    GaussPivotAppend32.program (by intro l; rfl)
    (⟨some .saveScan,((),none),B⟩ :
      CurrentAdditive.CodeDAppendAtEnd15.Config)
    (4*body.length+2*payload.length+7)
    (by
      change (CurrentAdditive.CodeDAppendAtEnd15.run
        (4*body.length+2*payload.length+7)
        ⟨some .saveScan,((),none),B⟩).l = none
      rw [hhalt])
  refine ⟨u,hu,?_⟩
  change GaussPivotAppend32.run u
      (GaussPivotAppend32.appendFrame S _) =
    GaussPivotAppend32.appendFrame S
      (CurrentAdditive.CodeDAppendAtEnd15.run _ _) at hr
  rw [hhalt] at hr
  simp only [B] at hr
  rw [GaussPivotAppend32.appendFrame_start] at hr
  exact hr

theorem stage_preserves (body payload : List Bool)
    (S : Stack → List Bool) (j : Stack)
    (hj : ¬ ∃ q : CurrentAdditive.CodeDAppendAtEnd15.Stack,
      GaussPivotAppend32.appendSlot q = j) :
    (GaussPivotAppend32.appendFrame S
      ⟨none,((),none),stageTarget body payload S⟩).stk j = S j := by
  change (BitMachineStackEmbedding.bank GaussPivotAppend32.appendSlot
    S (stageTarget body payload S)) j = S j
  exact BitMachineStackEmbedding.bank_outside _ _ _ j hj

theorem extend_exact (body payload : List Bool)
    (S : Stack → List Bool)
    (h23 : S 23 = body) (h26 : S 26 = payload)
    (h27 : S 27 = []) (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (2*body.length+3)+
        (4*body.length+2*payload.length+7),
      GaussPivotAppend32.run t
        ⟨some (.copyBodyDirect .scan),((),none),S⟩ =
      GaussPivotAppend32.appendFrame
        (GaussPivotAppend32.afterBody body S)
        ⟨none,((),none),
          stageTarget body payload
            (GaussPivotAppend32.afterBody body S)⟩ := by
  let S1 := GaussPivotAppend32.afterBody body S
  have hS127 : S1 27 = body := by
    have h := SourceClausePreservingBroadcast.target_written
      (23 : Stack) 31 [27] (by simp) (by simp) (by decide)
      body S 27 (by simp)
    simpa [S1,GaussPivotAppend32.afterBody,h27] using h
  have hS126 : S1 26 = payload := by
    have h := SourceClausePreservingBroadcast.other_preserved
      (23 : Stack) 31 [27] body S 26
      (by decide) (by decide) (by simp)
    simpa [S1,GaussPivotAppend32.afterBody] using h.trans h26
  have hS124 : S1 24 = [] := by
    have h := SourceClausePreservingBroadcast.other_preserved
      (23 : Stack) 31 [27] body S 24
      (by decide) (by decide) (by simp)
    simpa [S1,GaussPivotAppend32.afterBody] using h.trans h24
  have hS131 : S1 31 = [] :=
    SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
  obtain ⟨a,ha,hcopy⟩ :=
    GaussPivotAppend32.copy_body_direct body S h23 h31
  obtain ⟨b,hb,hstage⟩ :=
    stage_exact body payload S1 hS127 hS126 hS124 hS131
  exact ⟨a+b,by omega,
    (GaussPivotAppend32.run_add hcopy b).trans hstage⟩

theorem extend_preserves (body payload : List Bool)
    (S : Stack → List Bool) (j : Stack)
    (h23 : j ≠ 23) (h27 : j ≠ 27) (h31 : j ≠ 31)
    (hj : ¬ ∃ q : CurrentAdditive.CodeDAppendAtEnd15.Stack,
      GaussPivotAppend32.appendSlot q = j) :
    (GaussPivotAppend32.appendFrame
      (GaussPivotAppend32.afterBody body S)
      ⟨none,((),none),
        stageTarget body payload
          (GaussPivotAppend32.afterBody body S)⟩).stk j = S j := by
  rw [stage_preserves body payload _ j hj]
  exact SourceClausePreservingBroadcast.other_preserved
    (23 : Stack) 31 [27] body S j h23 h31
      (by simpa using h27)

#print axioms stage_exact
#print axioms stage_preserves
#print axioms extend_exact
#print axioms extend_preserves

end
end CurrentAdditive.GaussPivotAppendExact32
