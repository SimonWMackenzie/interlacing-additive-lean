import CurrentAdditive.GaussPivotQuadraticClock32

namespace CurrentAdditive.GaussPivotInputBytes32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

noncomputable section

def inputBytes {m k : Nat} (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) : Nat :=
  GaussPivotRawClock32.inputBankCharge s foreign

theorem state_packet_le_input {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) :
    (GaussControlTrace.statePacket s).length ≤ inputBytes s foreign := by
  have hb := GaussPivotRawInput32.bank_le_charge s foreign (30 : Stack)
  have hbank : (GaussStepParseRun32.raw s foreign).stk 30 =
      GaussControlTrace.statePacket s := by
    unfold GaussStepParseRun32.raw GaussParsedState32.frame
    change BitMachineStackEmbedding.bank GaussParsedState32.locate foreign
      (fun _ => _) 30 = _
    simpa [GaussParsedState32.locate] using
      (BitMachineStackEmbedding.bank_at GaussParsedState32.locate foreign
        (fun _ => _) (.inr (0 : Fin 3)))
  simpa [inputBytes,hbank] using hb

theorem foreign22_le_input {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) :
    (foreign 22).length ≤ inputBytes s foreign := by
  have hb := GaussPivotRawInput32.bank_le_charge s foreign (22 : Stack)
  have hbank : (GaussStepParseRun32.raw s foreign).stk 22 = foreign 22 := by
    unfold GaussStepParseRun32.raw GaussParsedState32.frame
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨q,hq⟩
    cases q with
    | inl q => fin_cases q <;> simp [GaussParsedState32.locate] at hq
    | inr q => fin_cases q <;> simp [GaussParsedState32.locate] at hq
  simpa [inputBytes,hbank] using hb

theorem copy_bytes_eq {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ q : Fin 4,
      foreign (GaussBranchFields32.dest q) = []) :
    GaussPivotByteSize32.copyBytes
      (GaussStepTagRun32.afterActive
        (GaussStepParseRun32.parsed s foreign).stk true) =
      (foreign 22).length + s.r + s.c +
        (GaussControlTrace.pivotsPacket s.pivots).length := by
  let T := GaussStepTagRun32.afterActive
    (GaussStepParseRun32.parsed s foreign).stk true
  have hp := GaussStepTagRun32.afterActive_parsed s
    (GaussStepParseRun32.parsed s foreign).stk true
    (GaussStepParseRun32.parsed_fields s foreign hblank)
  have h22 : T 22 = foreign 22 := by
    change (GaussStepTagRun32.afterActive
      (GaussStepParseRun32.parsed s foreign).stk true) 22 = _
    rw [GaussStepTagRun32.afterActive_preserves _ true 22
      (by decide) (by decide) (by decide)]
    exact GaussParsedState32.parsed_ambient s foreign 22
      ⟨by decide,by decide,by decide,by decide,
        by decide,by decide,by decide⟩
  have h17 : T 17 = List.replicate s.r true := hp.row
  have h18 : T 18 = List.replicate s.c true := hp.column
  have h19 : T 19 = GaussControlTrace.pivotsPacket s.pivots := hp.pivots
  change (∑ q : Fin 4, (T (GaussBranchFields32.source .pivot q)).length) = _
  simp [Fin.sum_univ_succ,GaussBranchFields32.source,
    h22,h17,h18,h19]
  omega

theorem assembly_bytes_eq {m k : Nat}
    (s : GaussControlTrace.State m k) :
    GaussPivotByteSize32.assemblyBytes (GaussControlTrace.stateBank s) =
      (GaussPhysical.encodeTypedMatrix s.B).length + s.r + s.c +
        (GaussControlTrace.pivotsPacket s.pivots).length := by
  simp [GaussPivotByteSize32.assemblyBytes,
    GaussControlTrace.stateBank,Fin.sum_univ_succ]
  omega

theorem state_packet_twice_assembly {m k : Nat}
    (s : GaussControlTrace.State m k) :
    (GaussControlTrace.statePacket s).length =
      2*GaussPivotByteSize32.assemblyBytes (GaussControlTrace.stateBank s)+4 := by
  rw [GaussControlTrace.statePacket_length,assembly_bytes_eq]

#print axioms state_packet_le_input
#print axioms foreign22_le_input
#print axioms copy_bytes_eq
#print axioms assembly_bytes_eq

end
end CurrentAdditive.GaussPivotInputBytes32
