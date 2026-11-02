import CurrentAdditive.GaussStepInactivePacket32

namespace CurrentAdditive.GaussNoPivotClock32
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open EthInapproximability.CurrentPaper Turing BitMachineEncoding
open GaussStepFields32

def prefixClock {m k : Nat} (s : GaussControlTrace.State m k) (foreign : Stack → List Bool) : Nat :=
  9*((GaussControlTrace.statePacket s).length+1)+1+9+
    (GaussBranchFields32.copyClock .noPivot
      (GaussStepTagRun32.afterActive (GaussStepParseRun32.parsed s foreign).stk false)+4)

def finishClock {m k : Nat} (s : GaussControlTrace.State m k) (S : Stack → List Bool) : Nat :=
  1+(GaussAssemblerReset32.clock S+1)+1+
    (GaussStateAssemble16.clock (GaussControlTrace.stateBank s)+1+
      2*(GaussControlTrace.statePacket s).length+2)

def clock {m k : Nat} (s : GaussControlTrace.State m k) (foreign : Stack → List Bool) : Nat :=
  prefixClock s foreign+1+finishClock (GaussBranchFields32.noPivotState s)
    (Function.update (GaussStepBranchRun32.adjusted .noPivot
      (GaussStepTagRun32.afterActive (GaussStepParseRun32.parsed s foreign).stk false)) 25 [])

private theorem parsed25 {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) :
    (GaussStepParseRun32.parsed s foreign).stk 25 = foreign 25 := by
  exact GaussParsedState32.parsed_ambient s foreign 25 (by decide)

theorem noPivot_packet_clock {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (htag : foreign 20 = [false])
    (h25 : foreign 25 = []) :
    ∃ t≤clock s foreign,
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
  refine ⟨a+1+b,?_,by rw [hfull]; exact hend,
    by rw [hfull]; exact hpacket⟩
  change a≤prefixClock s foreign at ha
  change b≤finishClock (GaussBranchFields32.noPivotState s) (Function.update W 25 []) at hb
  unfold clock
  dsimp only [W,T,S] at hb
  omega

#print axioms noPivot_packet_clock
end
end CurrentAdditive.GaussNoPivotClock32
