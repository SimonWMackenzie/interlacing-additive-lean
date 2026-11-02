import CurrentAdditive.GaussStepTagRun32

/-! Raw Bank4 to active branch fields in the fixed Fin32 controller. -/

namespace CurrentAdditive.GaussStepActiveRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

theorem raw_noPivot_fields {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (htag : foreign 20 = [false]) :
    ∃ t ≤ 9*((GaussControlTrace.statePacket s).length+1)+1+9+
        (GaussBranchFields32.copyClock .noPivot
          (GaussStepTagRun32.afterActive
            (GaussStepParseRun32.parsed s foreign).stk false)+4),
      run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign)) =
        ⟨some .afterBranch,eBranch ((),none),
          GaussStepBranchRun32.adjusted .noPivot
            (GaussStepTagRun32.afterActive
              (GaussStepParseRun32.parsed s foreign).stk false)⟩ ∧
      GaussBranchFields32.preparedBank
        (run t (BitMachineInline.cfg (Label.parse false) eParse
          (some (.afterParse false))
          (GaussStepParseRun32.raw s foreign))).stk =
        GaussControlTrace.stateBank
          (GaussBranchFields32.noPivotState s) := by
  let S := (GaussStepParseRun32.parsed s foreign).stk
  let T := GaussStepTagRun32.afterActive S false
  obtain ⟨a,ha,hparse⟩ := GaussStepParseRun32.parse_entry
    s foreign false
  have hS20 : S 20 = [false] := by
    have h := GaussParsedState32.parsed_ambient s foreign 20 (by decide)
    exact h.trans htag
  have hS31 : S 31 = [] :=
    (GaussStepParseRun32.parsed_fields s foreign hblank).scratch
  obtain ⟨b,hb,htagrun⟩ :=
    GaussStepTagRun32.active_entry S false hS20 hS31
  obtain ⟨c,hc,hbranch,hbank⟩ :=
    GaussStepBranchRun32.noPivot_prepared s T
      (GaussStepTagRun32.afterActive_parsed s S false
        (GaussStepParseRun32.parsed_fields s foreign hblank))
  have hfull : run (a+b+c)
      (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign)) =
      ⟨some .afterBranch,eBranch ((),none),
        GaussStepBranchRun32.adjusted .noPivot T⟩ := by
    rw [show a+b+c = a+(b+c) by omega,
      run_add hparse (b+c), run_add htagrun c]
    exact hbranch
  refine ⟨a+b+c, ?_, ?_, ?_⟩
  · change a+b+c ≤ 9*((GaussControlTrace.statePacket s).length+1)+1+9+
      (GaussBranchFields32.copyClock .noPivot T+4)
    omega
  · exact hfull
  · rw [hfull]
    exact hbank

theorem raw_pivot_counters {m k : Nat}
    (s : GaussControlTrace.State m k)
    (B' : Fin m → Fin k → ℚ)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (htag : foreign 20 = [true])
    (h22 : foreign 22 = GaussPhysical.encodeTypedMatrix B') :
    ∃ t ≤ 9*((GaussControlTrace.statePacket s).length+1)+1+9+
        (GaussBranchFields32.copyClock .pivot
          (GaussStepTagRun32.afterActive
            (GaussStepParseRun32.parsed s foreign).stk true)+4),
      run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign)) =
        ⟨some .afterBranch,eBranch ((),none),
          GaussStepBranchRun32.adjusted .pivot
            (GaussStepTagRun32.afterActive
              (GaussStepParseRun32.parsed s foreign).stk true)⟩ ∧
      let S := (run t (BitMachineInline.cfg
        (Label.parse false) eParse (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk
      S 4 = GaussPhysical.encodeTypedMatrix B' ∧
      S 5 = List.replicate (s.r+1) true ∧
      S 6 = List.replicate (s.c+1) true := by
  let S := (GaussStepParseRun32.parsed s foreign).stk
  let T := GaussStepTagRun32.afterActive S true
  obtain ⟨a,ha,hparse⟩ := GaussStepParseRun32.parse_entry
    s foreign false
  have hS20 : S 20 = [true] := by
    have h := GaussParsedState32.parsed_ambient s foreign 20 (by decide)
    exact h.trans htag
  have hS22 : S 22 = GaussPhysical.encodeTypedMatrix B' := by
    have h := GaussParsedState32.parsed_ambient s foreign 22 (by decide)
    exact h.trans h22
  have hT22 : T 22 = GaussPhysical.encodeTypedMatrix B' := by
    change GaussStepTagRun32.afterActive S true 22 = _
    rw [GaussStepTagRun32.afterActive_preserves S true 22
      (by decide) (by decide) (by decide)]
    exact hS22
  have hS31 : S 31 = [] :=
    (GaussStepParseRun32.parsed_fields s foreign hblank).scratch
  obtain ⟨b,hb,htagrun⟩ :=
    GaussStepTagRun32.active_entry S true hS20 hS31
  obtain ⟨c,hc,hbranch,hm,hr,hcol⟩ :=
    GaussStepBranchRun32.pivot_counters_prepared s B' T
      (GaussStepTagRun32.afterActive_parsed s S true
        (GaussStepParseRun32.parsed_fields s foreign hblank)) hT22
  have hfull : run (a+b+c)
      (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign)) =
      ⟨some .afterBranch,eBranch ((),none),
        GaussStepBranchRun32.adjusted .pivot T⟩ := by
    rw [show a+b+c = a+(b+c) by omega,
      run_add hparse (b+c), run_add htagrun c]
    exact hbranch
  refine ⟨a+b+c, ?_, ?_, ?_⟩
  · change a+b+c ≤ 9*((GaussControlTrace.statePacket s).length+1)+1+9+
      (GaussBranchFields32.copyClock .pivot T+4)
    omega
  · exact hfull
  · simp only [hfull]
    exact ⟨hm,hr,hcol⟩

#print axioms raw_noPivot_fields
#print axioms raw_pivot_counters

end
end CurrentAdditive.GaussStepActiveRun32
