import CurrentAdditive.GaussStepInactiveDispatch32

/-! Exact raw-to-raw Gauss packets for terminal and no-pivot steps. -/

namespace CurrentAdditive.GaussStepInactivePacket32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private theorem parsed25 {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) :
    (GaussStepParseRun32.parsed s foreign).stk 25 = foreign 25 := by
  exact GaussParsedState32.parsed_ambient s foreign 25 (by decide)

theorem terminal_packet {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (h25 : foreign 25 = []) :
    ∃ t,
      (run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket s := by
  let S := (GaussStepParseRun32.parsed s foreign).stk
  let W := GaussStepBranchRun32.adjusted .halted S
  obtain ⟨a,ha,hbranch,hbank⟩ :=
    GaussStepParseRun32.raw_terminal_fields s foreign hblank
  have hW25 : W 25 = [] := by
    change GaussStepBranchRun32.adjusted .halted S 25 = []
    rw [GaussStepBranchRun32.adjusted25,
      show S 25 = foreign 25 from parsed25 s foreign,h25]
  obtain ⟨ctrl,hdispatch⟩ :=
    GaussStepInactiveDispatch32.inactive_dispatch W (Or.inl hW25)
  have hbank' : GaussBranchFields32.preparedBank
      (Function.update W 25 []) = GaussControlTrace.stateBank s := by
    rw [GaussStepInactiveDispatch32.prepared_clear25]
    simpa [hbranch] using hbank
  obtain ⟨b,hb,hend,hpacket⟩ :=
    GaussStepFinish32.finish_state s (Function.update W 25 [])
      ctrl hbank'
  have hfull : run (a+1+b)
      (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign)) =
      run b ⟨some .afterJoin,ctrl,Function.update W 25 []⟩ := by
    rw [show a+1+b = a+(1+b) by omega,
      run_add hbranch (1+b),run_add hdispatch b]
  exact ⟨a+1+b, by rw [hfull]; exact hend,
    by rw [hfull]; exact hpacket⟩

theorem noPivot_packet {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (htag : foreign 20 = [false])
    (h25 : foreign 25 = []) :
    ∃ t,
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket
          (GaussBranchFields32.noPivotState s) := by
  let S := (GaussStepParseRun32.parsed s foreign).stk
  let T := GaussStepTagRun32.afterActive S false
  let W := GaussStepBranchRun32.adjusted .noPivot T
  obtain ⟨a,ha,hbranch,hbank⟩ :=
    GaussStepActiveRun32.raw_noPivot_fields s foreign hblank htag
  have hT25 : T 25 = [false] := by
    change Function.update (GaussStepTagRun32.tagged S false) 20 [] 25 = _
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 20)]
    have ht := SourceClausePreservingBroadcast.target_written
      (20 : Stack) 31 [25] (by decide) (by decide) (by decide)
      [false] S 25 (by simp)
    change SourceClausePreservingBroadcast.result 20 31 [25]
      [false] S 25 = _
    rw [ht, show S 25 = foreign 25 from parsed25 s foreign,h25]
    rfl
  have hW25 : W 25 = [false] := by
    change GaussStepBranchRun32.adjusted .noPivot T 25 = _
    rw [GaussStepBranchRun32.adjusted25]
    exact hT25
  obtain ⟨ctrl,hdispatch⟩ :=
    GaussStepInactiveDispatch32.inactive_dispatch W (Or.inr hW25)
  have hbank' : GaussBranchFields32.preparedBank
      (Function.update W 25 []) =
      GaussControlTrace.stateBank
        (GaussBranchFields32.noPivotState s) := by
    rw [GaussStepInactiveDispatch32.prepared_clear25]
    simpa [hbranch] using hbank
  obtain ⟨b,hb,hend,hpacket⟩ :=
    GaussStepFinish32.finish_state
      (GaussBranchFields32.noPivotState s)
      (Function.update W 25 []) ctrl hbank'
  have hfull : run (a+1+b)
      (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign)) =
      run b ⟨some .afterJoin,ctrl,Function.update W 25 []⟩ := by
    rw [show a+1+b = a+(1+b) by omega,
      run_add hbranch (1+b),run_add hdispatch b]
  exact ⟨a+1+b, by rw [hfull]; exact hend,
    by rw [hfull]; exact hpacket⟩

#print axioms terminal_packet
#print axioms noPivot_packet

end
end CurrentAdditive.GaussStepInactivePacket32
