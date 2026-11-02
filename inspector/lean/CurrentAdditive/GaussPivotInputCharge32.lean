import CurrentAdditive.GaussPivotPacketLengths32

namespace CurrentAdditive.GaussPivotInputCharge32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

noncomputable section

set_option maxHeartbeats 0

theorem byteCharge_le_input {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hr : s.r < m) (hc : s.c < k)
    (hcount : s.r = s.pivots.length)
    (hblank : ∀ q : Fin 4,
      foreign (GaussBranchFields32.dest q) = [])
    (h22 : foreign 22 = GaussPhysical.encodeTypedMatrix
      (GaussControlTrace.step s).B) :
    GaussPivotByteSize32.byteCharge s foreign hr hc ≤
      100*(GaussPivotInputBytes32.inputBytes s foreign+1) := by
  let I := GaussPivotInputBytes32.inputBytes s foreign
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  let ps' := s.pivots ++ [p]
  let pair := GaussControlTrace.pivotPacket p
  let successor : GaussControlTrace.State m k :=
    ⟨(GaussControlTrace.step s).B,ps'.length,s.c+1,ps'⟩
  have hpairid : pair.length =
      (GaussControlTrace.pivotPacket p).length := rfl
  have hpsLen : ps'.length = s.r+1 := by
    simp [ps',hcount]
  have hs := GaussPivotInputBytes32.state_packet_le_input s foreign
  have hm := GaussPivotInputBytes32.foreign22_le_input s foreign
  have hsizes : s.r+s.c+
      (GaussControlTrace.pivotsPacket s.pivots).length ≤ I := by
    have he := GaussControlTrace.statePacket_length s
    dsimp [I] at hs ⊢
    omega
  have hcopy : GaussPivotByteSize32.copyBytes
      (GaussStepTagRun32.afterActive
        (GaussStepParseRun32.parsed s foreign).stk true) ≤ 2*I := by
    rw [GaussPivotInputBytes32.copy_bytes_eq s foreign hblank]
    omega
  have hbits : s.pivots.length.bits.length ≤ I := by
    have hb := UnaryBinaryEncoding.bits_length_le s.pivots.length
    omega
  have hpair : pair.length ≤ 2*I+2 := by
    have hp := GaussControlTrace.pivotPacket_length p
    dsimp [pair,p] at hp ⊢
    omega
  have hpairFrame : (SourceListMachineWriter.result true pair).length ≤
      6*I+7 := by
    have hf := SourceListMachineWriter.result_length true pair
    omega
  have holdBody : (SourceListEncoding.fields
      (s.pivots.map GaussControlTrace.pivotPacket)).length ≤ I := by
    have hb := GaussPivotPacketLengths32.fields_le_encode
      (s.pivots.map GaussControlTrace.pivotPacket)
    change (SourceListEncoding.fields
      (s.pivots.map GaussControlTrace.pivotPacket)).length ≤ _ at hb
    have hp : (GaussControlTrace.pivotsPacket s.pivots).length ≤ I := by
      omega
    exact hb.trans hp
  have hpayload : (natField pair.length ++ pair).length ≤ 6*I+7 := by
    have hn := EncodedGraph.natField_length_upper pair.length
    simp only [List.length_append]
    omega
  have hcount' : ps'.length ≤ I+1 := by
    simp only [ps',List.length_append,List.length_singleton]
    omega
  have hcountFrame :
      (SourceListMachineWriter.result false
        (List.replicate ps'.length true)).length ≤ 3*I+4 := by
    have hf := SourceListMachineWriter.result_length false
      (List.replicate ps'.length true)
    simp only [List.length_replicate] at hf
    omega
  have hcountField : (natField ps'.length).length ≤ 2*I+3 := by
    have hn := EncodedGraph.natField_length_upper ps'.length
    omega
  have hnewBody : (SourceListEncoding.fields
      (ps'.map GaussControlTrace.pivotPacket)).length ≤ 7*I+7 := by
    have hb := GaussPivotPacketLengths32.appended_fields_length s.pivots p
    change (SourceListEncoding.fields
      (ps'.map GaussControlTrace.pivotPacket)).length ≤ _ at hb
    omega
  have hnewPacket : (GaussControlTrace.pivotsPacket ps').length ≤
      9*I+10 := by
    have hb := GaussPivotPacketLengths32.appended_packet_length s.pivots p
    change (GaussControlTrace.pivotsPacket ps').length ≤ _ at hb
    omega
  have hassembly : GaussPivotByteSize32.assemblyBytes
      (GaussControlTrace.stateBank successor) ≤ 12*I+12 := by
    rw [GaussPivotInputBytes32.assembly_bytes_eq]
    change (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B).length+
      ps'.length+(s.c+1)+(GaussControlTrace.pivotsPacket ps').length ≤ _
    rw [← h22]
    omega
  have hpacket : (GaussControlTrace.statePacket successor).length ≤
      24*I+28 := by
    rw [GaussPivotInputBytes32.state_packet_twice_assembly]
    omega
  have hparts : GaussPivotByteSize32.byteCharge s foreign hr hc =
      I + (GaussControlTrace.statePacket s).length +
      GaussPivotByteSize32.copyBytes
        (GaussStepTagRun32.afterActive
          (GaussStepParseRun32.parsed s foreign).stk true) +
      (GaussControlTrace.pivotsPacket s.pivots).length +
      s.pivots.length.bits.length + pair.length +
      (SourceListMachineWriter.result true pair).length +
      (SourceListEncoding.fields
        (s.pivots.map GaussControlTrace.pivotPacket)).length +
      (natField pair.length ++ pair).length + ps'.length +
      (SourceListMachineWriter.result false
        (List.replicate ps'.length true)).length +
      (natField ps'.length).length +
      (SourceListEncoding.fields
        (ps'.map GaussControlTrace.pivotPacket)).length +
      GaussPivotByteSize32.assemblyBytes
        (GaussControlTrace.stateBank successor) +
      (GaussControlTrace.statePacket successor).length := rfl
  rw [hparts]
  omega

#print axioms byteCharge_le_input

end
end CurrentAdditive.GaussPivotInputCharge32
