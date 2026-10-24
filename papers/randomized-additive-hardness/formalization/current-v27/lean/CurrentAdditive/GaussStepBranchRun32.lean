import CurrentAdditive.GaussStepPhaseLift32

/-! The exact branch-copy phase inside the fixed Gauss field controller. -/

namespace CurrentAdditive.GaussStepBranchRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def adjusted (b : GaussBranchFields32.Branch)
    (S : Stack → List Bool) : Stack → List Bool :=
  match b with
  | .halted => GaussBranchFields32.after3 b S
  | .noPivot =>
      Function.update (GaussBranchFields32.after3 b S) 6
        (true :: (GaussBranchFields32.after3 b S) 6)
  | .pivot =>
      Function.update
        (Function.update (GaussBranchFields32.after3 b S) 5
          (true :: (GaussBranchFields32.after3 b S) 5)) 6
        (true :: (GaussBranchFields32.after3 b S) 6)

theorem adjusted25 (b : GaussBranchFields32.Branch)
    (S : Stack → List Bool) : adjusted b S 25 = S 25 := by
  cases b <;>
    simp [adjusted,GaussBranchFields32.after3,
      GaussBranchFields32.after2,GaussBranchFields32.after1,
      GaussBranchFields32.after0,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend,
      GaussBranchFields32.source,
      GaussBranchFields32.dest,
      GaussBranchFields32.temp]

theorem branch_copy (b : GaussBranchFields32.Branch)
    (S : Stack → List Bool) (hs : S 31 = []) :
    ∃ t ≤ GaussBranchFields32.copyClock b S + 4,
      run t ⟨some (.branch (.copy b 0 .scan)), eBranch ((),none), S⟩ =
        ⟨some .afterBranch, eBranch ((),none), adjusted b S⟩ := by
  obtain ⟨u, hu, hcopy⟩ := GaussBranchFields32.physical_copy_fields b S hs
  let Sa := GaussBranchFields32.after3 b S
  have hstep : ∃ d ≤ 2,
      GaussBranchFields32.run d
        ⟨some (.adjust b), ((),none), Sa⟩ =
      ⟨some (if b = .pivot then .pivotAppend else .done),
        ((),none), adjusted b S⟩ := by
    cases b
    · exact ⟨1, by omega, by
        simpa [adjusted, Sa] using
          GaussBranchFields32.adjust_halted Sa ((),none)⟩
    · exact ⟨1, by omega, by
        simpa [adjusted, Sa] using
          GaussBranchFields32.adjust_noPivot Sa ((),none)⟩
    · exact ⟨1, by omega, by
        simpa [adjusted, Sa] using
          GaussBranchFields32.adjust_pivot Sa ((),none)⟩
  obtain ⟨d, hd, hstep⟩ := hstep
  have hfinish : GaussBranchFields32.run 2
      ⟨some (if b = .pivot then .pivotAppend else .done),
        ((),none), adjusted b S⟩ =
      ⟨none, ((),none), adjusted b S⟩ := by
    cases b <;> rfl
  have hlocal : GaussBranchFields32.run (u+d+2)
      ⟨some (.copy b 0 .scan), ((),none), S⟩ =
      ⟨none, ((),none), adjusted b S⟩ := by
    rw [show u+d+2 = u+(d+2) by omega,
      GaussBranchFields32.run_add hcopy (d+2)]
    exact (GaussBranchFields32.run_add hstep 2).trans hfinish
  obtain ⟨v, hv, hglobal⟩ :=
    GaussStepPhaseLift32.branch_lift
      (⟨some (.copy b 0 .scan), ((),none), S⟩) (u+d+2)
      (by rw [hlocal])
  refine ⟨v, by omega, ?_⟩
  simpa [BitMachineInline.cfg, hlocal] using hglobal

theorem halted_prepared {m k : Nat}
    (s : GaussControlTrace.State m k) (S : Stack → List Bool)
    (hs : GaussBranchFields32.ParsedState s S) :
    ∃ t ≤ GaussBranchFields32.copyClock .halted S + 4,
      run t ⟨some (.branch (.copy .halted 0 .scan)),
        eBranch ((),none), S⟩ =
        ⟨some .afterBranch, eBranch ((),none), adjusted .halted S⟩ ∧
      GaussBranchFields32.preparedBank (adjusted .halted S) =
        GaussControlTrace.stateBank s := by
  obtain ⟨t, ht, hr⟩ := branch_copy .halted S hs.scratch
  exact ⟨t, ht, hr,
    GaussBranchFields32.halted_prepared_bank s S hs⟩

theorem noPivot_prepared {m k : Nat}
    (s : GaussControlTrace.State m k) (S : Stack → List Bool)
    (hs : GaussBranchFields32.ParsedState s S) :
    ∃ t ≤ GaussBranchFields32.copyClock .noPivot S + 4,
      run t ⟨some (.branch (.copy .noPivot 0 .scan)),
        eBranch ((),none), S⟩ =
        ⟨some .afterBranch, eBranch ((),none), adjusted .noPivot S⟩ ∧
      GaussBranchFields32.preparedBank (adjusted .noPivot S) =
        GaussControlTrace.stateBank
          (GaussBranchFields32.noPivotState s) := by
  obtain ⟨t, ht, hr⟩ := branch_copy .noPivot S hs.scratch
  exact ⟨t, ht, hr,
    GaussBranchFields32.noPivot_prepared_bank s S hs⟩

theorem pivot_counters_prepared {m k : Nat}
    (s : GaussControlTrace.State m k)
    (B' : Fin m → Fin k → ℚ) (S : Stack → List Bool)
    (hs : GaussBranchFields32.ParsedState s S)
    (h22 : S 22 = GaussPhysical.encodeTypedMatrix B') :
    ∃ t ≤ GaussBranchFields32.copyClock .pivot S + 4,
      run t ⟨some (.branch (.copy .pivot 0 .scan)),
        eBranch ((),none), S⟩ =
        ⟨some .afterBranch, eBranch ((),none), adjusted .pivot S⟩ ∧
      (adjusted .pivot S) 4 = GaussPhysical.encodeTypedMatrix B' ∧
      (adjusted .pivot S) 5 = List.replicate (s.r+1) true ∧
      (adjusted .pivot S) 6 = List.replicate (s.c+1) true := by
  obtain ⟨t, ht, hr⟩ := branch_copy .pivot S hs.scratch
  obtain ⟨hm,hrc,hcc⟩ :=
    GaussPivotPrepared32.pivot_fields_before_join s B' S hs h22
  exact ⟨t, ht, hr, by simpa [adjusted,
    GaussPivotPrepared32.afterCounters] using hm,
    by simpa [adjusted,
      GaussPivotPrepared32.afterCounters] using hrc,
    by simpa [adjusted,
      GaussPivotPrepared32.afterCounters] using hcc⟩

#print axioms branch_copy
#print axioms adjusted25
#print axioms halted_prepared
#print axioms noPivot_prepared
#print axioms pivot_counters_prepared

end
end CurrentAdditive.GaussStepBranchRun32
