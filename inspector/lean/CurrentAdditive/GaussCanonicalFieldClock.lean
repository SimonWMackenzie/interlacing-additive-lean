import CurrentAdditive.GaussNextFieldsPrepare64
import CurrentAdditive.GaussNoPivotClock32
import CurrentAdditive.GaussPivotInputCharge32

/-! Bounds on the actual canonical Fin32 field controller, charged to
the old encoded state and rewritten matrix bytes. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace CurrentAdditive.GaussCanonicalFieldClock
noncomputable section

open EthInapproximability.CurrentPaper
open BitMachineEncoding
open GaussStepFields32

abbrev foreign := GaussNextFieldsPrepare64.foreign

theorem raw_canonical {m k : Nat} (s : GaussControlTrace.State m k)
    (tag : Bool) (matrix : List Bool) (j : Stack) :
    (GaussStepParseRun32.raw s (foreign [tag] matrix)).stk j =
      if j=30 then GaussControlTrace.statePacket s else
      if j=20 then [tag] else if j=22 then matrix else [] := by
  change BitMachineStackEmbedding.bank GaussParsedState32.locate (foreign [tag] matrix)
    (BitMachineBankCodec.parserCfg (K := 4) (some (.scan 0)) none (fun _ => [])
      (GaussControlTrace.statePacket s) [] []).stk j = _
  by_cases hj : ∃ q, GaussParsedState32.locate q=j
  · obtain ⟨q,rfl⟩ := hj
    rw [BitMachineStackEmbedding.bank_at]
    cases q with
    | inl q => fin_cases q <;> simp [GaussParsedState32.locate,
        BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr q => fin_cases q <;> simp [GaussParsedState32.locate,
        BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hj]
    have h30 : j≠30 := by
      intro h
      apply hj
      exact ⟨.inr 0,h.symm⟩
    simp [foreign,GaussNextFieldsPrepare64.foreign,h30]

theorem inputBytes_canonical {m k : Nat} (s : GaussControlTrace.State m k)
    (tag : Bool) (matrix : List Bool) :
    GaussPivotInputBytes32.inputBytes s (foreign [tag] matrix) =
      (GaussControlTrace.statePacket s).length+matrix.length+1 := by
  unfold GaussPivotInputBytes32.inputBytes GaussPivotRawClock32.inputBankCharge
  simp only [raw_canonical]
  simp [Fin.sum_univ_succ]
  omega

theorem byteCharge_canonical {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (hcount : s.r = s.pivots.length) :
    GaussPivotByteSize32.byteCharge s
      (foreign [true] (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)) hr hc ≤
      100*((GaussControlTrace.statePacket s).length+
        (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B).length+2) := by
  have h := GaussPivotInputCharge32.byteCharge_le_input s
    (foreign [true] (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B))
    hr hc hcount (by intro q; fin_cases q <;>
      simp [foreign,GaussNextFieldsPrepare64.foreign,GaussBranchFields32.dest])
    (by simp [foreign,GaussNextFieldsPrepare64.foreign])
  rw [inputBytes_canonical] at h
  simpa [Nat.add_assoc] using h

theorem byteCharge_canonical_linear {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (hcount : s.r = s.pivots.length) :
    GaussPivotByteSize32.byteCharge s
      (foreign [true] (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)) hr hc ≤
      200*((GaussControlTrace.statePacket s).length+
        (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B).length+1) := by
  have h := byteCharge_canonical s hr hc hcount
  omega

theorem noPivot_copyClock {m k : Nat} (s : GaussControlTrace.State m k)
    (matrix : List Bool) :
    GaussBranchFields32.copyClock .noPivot
      (GaussStepTagRun32.afterActive
        (GaussStepParseRun32.parsed s (foreign [false] matrix)).stk false) =
      (GaussControlTrace.statePacket s).length+8 := by
  have hp := GaussStepTagRun32.afterActive_parsed s
    (GaussStepParseRun32.parsed s (foreign [false] matrix)).stk false
    (GaussStepParseRun32.parsed_fields s (foreign [false] matrix)
      (by intro q; fin_cases q <;>
        simp [foreign,GaussNextFieldsPrepare64.foreign,GaussBranchFields32.dest]))
  simp only [GaussBranchFields32.copyClock]
  rw [show GaussBranchFields32.source .noPivot 0 = 16 from rfl,
    show GaussBranchFields32.source .noPivot 1 = 17 from rfl,
    show GaussBranchFields32.source .noPivot 2 = 18 from rfl,
    show GaussBranchFields32.source .noPivot 3 = 19 from rfl]
  rw [hp.matrix,hp.row,hp.column,hp.pivots]
  simp only [List.length_replicate,GaussControlTrace.statePacket_length]
  omega

theorem noPivot_adjusted_reset_eq (S : Stack → List Bool) (j : Fin 12) :
    GaussStepBranchRun32.adjusted .noPivot S (GaussAssemblerReset32.bank j) =
      S (GaussAssemblerReset32.bank j) := by
  fin_cases j <;>
    simp [GaussStepBranchRun32.adjusted,GaussBranchFields32.after3,
      GaussBranchFields32.after2,GaussBranchFields32.after1,GaussBranchFields32.after0,
      SourceClausePreservingBroadcast.result,BitMachineBroadcast.prepend,
      GaussBranchFields32.source,GaussBranchFields32.dest,GaussBranchFields32.temp,
      GaussAssemblerReset32.bank]

theorem noPivot_resetClock {m k : Nat} (s : GaussControlTrace.State m k)
    (matrix : List Bool) :
    GaussAssemblerReset32.clock
      (Function.update (GaussStepBranchRun32.adjusted .noPivot
        (GaussStepTagRun32.afterActive
          (GaussStepParseRun32.parsed s (foreign [false] matrix)).stk false)) 25 []) = 13 := by
  have hblank (j : Fin 12) :
      (Function.update (GaussStepBranchRun32.adjusted .noPivot
        (GaussStepTagRun32.afterActive
          (GaussStepParseRun32.parsed s (foreign [false] matrix)).stk false)) 25 [])
          (GaussAssemblerReset32.bank j) = [] := by
    rw [Function.update_of_ne (by fin_cases j <;> decide)]
    rw [noPivot_adjusted_reset_eq]
    rw [GaussStepTagRun32.afterActive_preserves _ false _
      (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
    have hp := GaussParsedState32.parsed_ambient s (foreign [false] matrix)
      (GaussAssemblerReset32.bank j) (by fin_cases j <;> decide)
    change (GaussStepParseRun32.parsed s (foreign [false] matrix)).stk
      (GaussAssemblerReset32.bank j) = foreign [false] matrix (GaussAssemblerReset32.bank j) at hp
    rw [hp]
    fin_cases j <;> simp [foreign,GaussNextFieldsPrepare64.foreign,GaussAssemblerReset32.bank]
  simp only [GaussAssemblerReset32.clock,hblank,List.length_nil,Finset.sum_const_zero,Nat.zero_add]

theorem noPivot_packet_length {m k : Nat} (s : GaussControlTrace.State m k) :
    (GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s)).length =
      (GaussControlTrace.statePacket s).length+2 := by
  simp only [GaussControlTrace.statePacket_length,GaussBranchFields32.noPivotState]
  omega

theorem noPivot_clock_eq {m k : Nat} (s : GaussControlTrace.State m k)
    (matrix : List Bool) :
    GaussNoPivotClock32.clock s (foreign [false] matrix) =
      13*(GaussControlTrace.statePacket s).length+65 := by
  unfold GaussNoPivotClock32.clock GaussNoPivotClock32.prefixClock GaussNoPivotClock32.finishClock
  rw [noPivot_copyClock,noPivot_resetClock]
  rw [GaussPivotByteSize32.assemblyClock_eq]
  rw [GaussPivotInputBytes32.assembly_bytes_eq]
  rw [noPivot_packet_length]
  simp only [GaussBranchFields32.noPivotState]
  have hs := GaussControlTrace.statePacket_length s
  omega

theorem noPivot_clock_linear {m k : Nat} (s : GaussControlTrace.State m k)
    (matrix : List Bool) :
    GaussNoPivotClock32.clock s (foreign [false] matrix) ≤
      100*((GaussControlTrace.statePacket s).length+matrix.length+1) := by
  rw [noPivot_clock_eq]
  omega

end
#print axioms raw_canonical
#print axioms inputBytes_canonical
#print axioms byteCharge_canonical
#print axioms byteCharge_canonical_linear
#print axioms noPivot_clock_linear
end CurrentAdditive.GaussCanonicalFieldClock
