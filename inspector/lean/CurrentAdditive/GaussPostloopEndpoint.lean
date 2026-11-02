import CurrentAdditive.GaussPostloopMachine
import CurrentAdditive.GaussPostloopClock

namespace CurrentAdditive.GaussPostloopEndpoint
noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open GaussFirstFreeCandidate GaussCertificateVectorABI GaussPostloopSerialized

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

theorem packet_bounds {m k : Nat} (s : GaussControlTrace.State m k) :
    let n:=(packet (GaussControlTrace.statePacket s) k).length
    (GaussControlTrace.statePacket s).length ≤ n ∧
      (GaussPhysical.encodeTypedMatrix s.B).length ≤ n ∧ m ≤ n ∧ k ≤ n := by
  let n:=(packet (GaussControlTrace.statePacket s) k).length
  have hs : (GaussControlTrace.statePacket s).length ≤ n := by
    simpa [packet,words] using BitMachineBankCodec.word_length_le_encode
      (words (GaussControlTrace.statePacket s) k) (0:Fin 2)
  have hk : k ≤ n := by
    simpa [packet,words] using BitMachineBankCodec.word_length_le_encode
      (words (GaussControlTrace.statePacket s) k) (1:Fin 2)
  have hB:=(GaussActualWorkListClock.matrix_length_le_statePacket s).trans hs
  exact ⟨hs,hB,(GaussInitialByteDimensions.rows_le_initial_bytes s.B).trans hB,hk⟩

theorem actual_clock_le {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j,A i j=0 ∨ A i j=1) (f : Fin k) :
    let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
    GaussAnyWidthVector.totalClock s f ≤
      GaussPostloopClock.bodyCap (packet (GaussControlTrace.statePacket s) k).length := by
  let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
  let n:=(packet (GaussControlTrace.statePacket s) k).length
  obtain ⟨hstate,hB,hm,hk⟩:=packet_bounds s
  have hs : (GaussControlTrace.statePacket s).length ≤ GaussActualWorkListClock.stateCap m k := by
    simpa [s,GaussActualWorkListClock.stateCap,GaussPivotPrefixClock.stateCap] using
      GaussControlTrace.actual_statePacket_length A h01 k (by omega)
  have hBcap := GaussActualWorkListClock.actual_matrix_length A h01
  have hlist:=GaussActualWorkListClock.totalClock_le s.B f hBcap
  have hsel:=GaussActualWorkListClock.uniformBound_mono GaussStateMatrixContext.Sel
    (xs:=GaussControlTrace.statePacket s)
    (ys:=List.replicate (GaussActualWorkListClock.stateCap m k) true)
    (a:=GaussPivotPrefixClock.prefixClock m k) (b:=GaussPivotPrefixClock.prefixClock m k)
    (by simpa using hs) le_rfl
  have hproj:=GaussActualWorkListClock.uniformBound_mono GaussStateMatrixContext.Proj
    (xs:=GaussControlTrace.statePacket s)
    (ys:=List.replicate (GaussActualWorkListClock.stateCap m k) true)
    (a:=12*((GaussControlTrace.statePacket s).length+1))
    (b:=12*(GaussActualWorkListClock.stateCap m k+1))
    (by simpa using hs) (by omega)
  have hbase : MachineInvokeFull.uniformBound GaussStateMatrixContext.Sel
      (GaussControlTrace.statePacket s) (GaussPivotPrefixClock.prefixClock m k)+
      MachineInvokeFull.uniformBound GaussStateMatrixContext.Proj
        (GaussControlTrace.statePacket s) (12*((GaussControlTrace.statePacket s).length+1))+1+
      GaussWorkListComplete.totalClock s.B f+1 ≤ GaussActualWorkListClock.clock m k := by
    unfold GaussActualWorkListClock.clock
    omega
  have hwork:=GaussPostloopClock.workCap_mono hm hk
  change GaussActualWorkListClock.clock m k ≤ GaussPostloopClock.workCap n at hwork
  have hvtime:=GaussPostloopClock.vectorClock_le s.B f n hB hk
  have hvbytes:=GaussPostloopClock.workBytes_le s.B f n hB hk
  have hv:=GaussActualWorkListClock.uniformBound_mono GaussWideVectorInvoke.VectorMachine
    (xs:=SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f))
    (ys:=List.replicate (GaussPostloopClock.workBytes n) true)
    (a:=GaussAnyWidthVector.vectorClock s.B f) (b:=GaussPostloopClock.vectorCap n)
    (by simpa using hvbytes) hvtime
  change GaussAnyWidthVector.totalClock s f ≤ GaussPostloopClock.bodyCap n
  unfold GaussAnyWidthVector.totalClock GaussPostloopClock.bodyCap
  omega

/-- One fixed coefficient and exponent precede every matrix and both
dimensions. The input is the actual serialized Bank2 packet, not an assumed
prepared bank. Coefficients retain their original column positions. -/
theorem uniform_outputs : ∃ C e : Nat,
    ∀ {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
      (h01 : ∀ i j,A i j=0 ∨ A i j=1),
      SequentialTotality.typedFree (GaussControlTrace.after (fun i j => (A i j:ℚ)) k).pivots ≠ none →
      let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
      ∃ (f : Fin k) (hf : f.val ≤ m),
        SequentialTotality.typedFree s.pivots=some f ∧
        postloopPacket s.B s.pivots=some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) ∧
        GaussPostloopMachine.machine.OutputsWithin (packet (GaussControlTrace.statePacket s) k)
          (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
          (C*((packet (GaussControlTrace.statePacket s) k).length+1)^e) := by
  obtain ⟨C,e,hpoly⟩:=GaussPostloopClock.clock_polynomial
  refine ⟨C,e,?_⟩
  intro m k A h01 hdependent
  obtain ⟨f,hf,hfree,hcert,hout⟩:=GaussPostloopMachine.actual_outputs A h01 hdependent
  refine ⟨f,hf,hfree,hcert,BitMachine.outputsWithin_mono _ hout ?_⟩
  have hclock:=actual_clock_le A h01 f
  have hp:=hpoly 0 (packet (GaussControlTrace.statePacket
    (GaussControlTrace.after (fun i j => (A i j:ℚ)) k)) k).length
  simp only [Nat.zero_add] at hp
  exact (show _ ≤ GaussPostloopClock.clock (packet (GaussControlTrace.statePacket
    (GaussControlTrace.after (fun i j => (A i j:ℚ)) k)) k).length from by
      unfold GaussPostloopClock.clock
      omega).trans hp

#print axioms actual_clock_le
#print axioms uniform_outputs

end
end CurrentAdditive.GaussPostloopEndpoint
