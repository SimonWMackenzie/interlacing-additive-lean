import CurrentAdditive.GaussStepParseRun32

/-! The active Gauss controller physically reads the pivot-search tag. -/

namespace CurrentAdditive.GaussStepTagRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def tagged (S : Stack → List Bool) (tag : Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result 20 31 [25] [tag] S

def afterActive (S : Stack → List Bool) (tag : Bool) :
    Stack → List Bool := Function.update (tagged S tag) 20 []

theorem active_entry (S : Stack → List Bool) (tag : Bool)
    (h20 : S 20 = [tag]) (h31 : S 31 = []) :
    ∃ t ≤ 9,
      run t ⟨some (.afterParse false),eParse none,S⟩ =
        ⟨some (.branch (.copy
          (if tag then .pivot else .noPivot) 0 .scan)),
          eBranch ((),none),afterActive S tag⟩ := by
  have htag :
      ((advance (SourceClausePreservingBroadcast.program
        (20 : Stack) 31 [25]))^[5])
        (⟨some .scan,((),none),S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SourceClausePreservingBroadcast.Label
            GaussBranchFields32.Control) =
      ⟨none,((),none),tagged S tag⟩ := by
    simpa [tagged] using SourceClausePreservingBroadcast.run_halt
      (20 : Stack) 31 [25] (by decide) (by decide)
      (by decide) (by decide) [tag] S h20 h31
  obtain ⟨u,hu,hglobal⟩ := GaussStepPhaseLift32.tag_lift
    (⟨some .scan,((),none),S⟩) 5 (by rw [htag])
  have h0 : run 1 ⟨some (.afterParse false),eParse none,S⟩ =
      ⟨some (.saveTag .scan),eBranch ((),none),S⟩ := by rfl
  have h1 : run 1 ⟨some .afterSaveTag,eBranch ((),none),
        tagged S tag⟩ =
      ⟨some (.branch .active),eBranch ((),none),tagged S tag⟩ := by
    rfl
  have h2 : run 1 ⟨some (.branch .active),eBranch ((),none),
        tagged S tag⟩ =
      ⟨some (.branch (.copy
          (if tag then .pivot else .noPivot) 0 .scan)),
        eBranch ((),none),afterActive S tag⟩ := by
    have hsource : tagged S tag 20 = [tag] := by
      exact SourceClausePreservingBroadcast.source_restored
        (20 : Stack) 31 [25] (by decide) [tag] S
    cases tag <;>
      simp [run,program,BitMachineInline.stmt,
        GaussBranchFields32.program,advance,TM2.step,TM2.stepAux,
        afterActive,hsource,eBranch,defaultControl]
  have hs : run u ⟨some (.saveTag .scan),eBranch ((),none),S⟩ =
      ⟨some .afterSaveTag,eBranch ((),none),tagged S tag⟩ := by
    simpa [BitMachineInline.cfg,htag] using hglobal
  refine ⟨1+u+1+1, by omega, ?_⟩
  rw [show 1+u+1+1 = 1+(u+(1+1)) by omega,
    run_add h0 (u+(1+1)), run_add hs (1+1),
    run_add h1 1]
  exact h2

theorem afterActive_preserves (S : Stack → List Bool) (tag : Bool)
    (j : Stack) (hj20 : j ≠ 20) (hj25 : j ≠ 25)
    (hj31 : j ≠ 31) :
    afterActive S tag j = S j := by
  rw [afterActive, Function.update_of_ne hj20]
  exact SourceClausePreservingBroadcast.other_preserved
    (20 : Stack) 31 [25] [tag] S j hj20 hj31
      (by simpa using hj25)

theorem afterActive_scratch (S : Stack → List Bool) (tag : Bool) :
    afterActive S tag 31 = [] := by
  rw [afterActive, Function.update_of_ne (by decide : (31 : Stack) ≠ 20)]
  exact SourceClausePreservingBroadcast.temp_empty
    (20 : Stack) 31 [25] [tag] S

theorem afterActive_parsed {m k : Nat}
    (s : GaussControlTrace.State m k)
    (S : Stack → List Bool) (tag : Bool)
    (hs : GaussBranchFields32.ParsedState s S) :
    GaussBranchFields32.ParsedState s (afterActive S tag) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [afterActive_preserves S tag 16 (by decide) (by decide)
      (by decide)]
    exact hs.matrix
  · rw [afterActive_preserves S tag 17 (by decide) (by decide)
      (by decide)]
    exact hs.row
  · rw [afterActive_preserves S tag 18 (by decide) (by decide)
      (by decide)]
    exact hs.column
  · rw [afterActive_preserves S tag 19 (by decide) (by decide)
      (by decide)]
    exact hs.pivots
  · intro p
    rw [afterActive_preserves S tag (GaussBranchFields32.dest p)
      (by fin_cases p <;> decide) (by fin_cases p <;> decide)
      (by fin_cases p <;> decide)]
    exact hs.destinations p
  · exact afterActive_scratch S tag

#print axioms active_entry
#print axioms afterActive_parsed

end
end CurrentAdditive.GaussStepTagRun32
