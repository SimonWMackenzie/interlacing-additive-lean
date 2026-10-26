import CurrentAdditive.GaussPivotAppendToFinish32
import CurrentAdditive.GaussStepPivotPairRun32
import CurrentAdditive.GaussStepPivotPayloadExactRun32

/-! The fixed Fin32 pivot-field controller serializes the selected (r,c)
pair, frames it as one V2 item, appends it to the old list, then outputs the
exact updated Bank4 state. The matrix bytes are already in bank 4. -/

namespace CurrentAdditive.GaussPivotPairToFinish32

noncomputable section

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

private theorem pair_preserves {m k : Nat}
    (p : Fin m × Fin k) (S : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) (j : Stack)
    (hj17 : j ≠ 17) (hj18 : j ≠ 18) (hj28 : j ≠ 28)
    (hj29 : j ≠ 29) (hj30 : j ≠ 30) :
    (GaussStepPivotPairRun32.result p S S').stk j = S j :=
  GaussStepPivotPairRun32.result_preserves p S S' j
    hj17 hj18 hj28 hj29 hj30

theorem pair_to_packet {m k : Nat}
    (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (S : Stack → List Bool)
    (h4 : S 4 = GaussPhysical.encodeTypedMatrix B')
    (h5 : S 5 = List.replicate (ps ++ [p]).length true)
    (h6 : S 6 = List.replicate c true)
    (h23 : S 23 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket))
    (h24 : S 24 = []) (h26 : S 26 = []) (h27 : S 27 = [])
    (h17 : S 17 = List.replicate p.1.val true)
    (h18 : S 18 = List.replicate p.2.val true)
    (h28 : S 28 = []) (h29 : S 29 = [])
    (h30 : S 30 = []) (h31 : S 31 = [])
    (hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t,
      (run t ⟨some (.pair (.inl (.emit 0))),ePair none,S⟩).l =
        some .done ∧
      (run t ⟨some (.pair (.inl (.emit 0))),ePair none,S⟩).stk 14 =
        GaussControlTrace.statePacket
          (⟨B',(ps ++ [p]).length,c,ps ++ [p]⟩ :
            GaussControlTrace.State m k) := by
  let pair := GaussControlTrace.pivotPacket p
  let start : Config :=
    ⟨some (.pair (.inl (.emit 0))),ePair none,S⟩
  obtain ⟨a,ha,U,hpair⟩ :=
    GaussStepPivotPairRun32.pair_phase p S h17 h18 h29 h30 h28
  let P := GaussStepPivotPairRun32.result p S U
  have hrunP : run a start = P := hpair
  have hnextP : run 1 P =
      ⟨some (.payload (.copyIn .scan)),
        ePayload (((),none),
          (SourceListMachineWriter.framingMachine true).initial),P.stk⟩ := by
    change run 1 (GaussStepPivotPairRun32.result p S U) = _
    rfl
  have h28P : P.stk 28 = pair :=
    GaussStepPivotPairRun32.result_pair p S U
  have h31P : P.stk 31 = [] :=
    (pair_preserves p S U 31 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h31
  have hemptyP : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      P.stk (GaussPivotFraming32.locate j) = [] := by
    intro j
    rw [pair_preserves p S U (GaussPivotFraming32.locate j)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)]
    exact hempty j
  obtain ⟨b,hb,V,hpayload⟩ :=
    GaussStepPivotPayloadExactRun32.payload_exact pair P.stk
      h28P h31P hemptyP
  let Q := GaussStepPivotPayloadExactRun32.result pair P.stk V
  have hrunQ : run b
      ⟨some (.payload (.copyIn .scan)),
        ePayload (((),none),
          (SourceListMachineWriter.framingMachine true).initial),P.stk⟩ = Q :=
    hpayload
  have hnextQ : run 1 Q =
      ⟨some (.append (.copyBodyDirect .scan)),eAppend ((),none),Q.stk⟩ := by
    change run 1 (GaussStepPivotPayloadExactRun32.result pair P.stk V) = _
    rfl
  have hp4 : P.stk 4 = GaussPhysical.encodeTypedMatrix B' :=
    (pair_preserves p S U 4 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h4
  have hp5 : P.stk 5 = List.replicate (ps ++ [p]).length true :=
    (pair_preserves p S U 5 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h5
  have hp6 : P.stk 6 = List.replicate c true :=
    (pair_preserves p S U 6 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h6
  have hp23 : P.stk 23 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket) :=
    (pair_preserves p S U 23 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h23
  have hp24 : P.stk 24 = [] :=
    (pair_preserves p S U 24 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h24
  have hp26 : P.stk 26 = [] :=
    (pair_preserves p S U 26 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h26
  have hp27 : P.stk 27 = [] :=
    (pair_preserves p S U 27 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h27
  have hp30 : P.stk 30 = [] :=
    GaussStepPivotPairRun32.result30_empty p S U
  have hq4 : Q.stk 4 = GaussPhysical.encodeTypedMatrix B' :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 4
      (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hp4
  have hq5 : Q.stk 5 = List.replicate (ps ++ [p]).length true :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 5
      (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hp5
  have hq6 : Q.stk 6 = List.replicate c true :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 6
      (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hp6
  have hq23 : Q.stk 23 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket) :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 23
      (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans hp23
  have hq24 : Q.stk 24 = [] :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 24
      (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans hp24
  have hq26 : Q.stk 26 = natField pair.length ++ pair := by
    rw [GaussStepPivotPayloadExactRun32.result26 pair P.stk V hp26]
    rfl
  have hq27 : Q.stk 27 = [] :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 27
      (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans hp27
  have hq30 : Q.stk 30 = [] :=
    (GaussStepPivotPayloadExactRun32.result_preserves pair P.stk V 30
      (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans hp30
  have hq31 : Q.stk 31 = [] :=
    GaussStepPivotPayloadExactRun32.result31 pair P.stk V
  obtain ⟨d,hdone,hpacket⟩ :=
    GaussPivotAppendToFinish32.append_to_packet B' c ps p Q.stk
      hq4 hq5 hq6 hq23 hq26 hq27 hq24 hq30 hq31
  refine ⟨a+1+b+1+d, ?_, ?_⟩
  · rw [show a+1+b+1+d = a+(1+(b+(1+d))) by omega,
      run_add hrunP (1+(b+(1+d))),run_add hnextP (b+(1+d)),
      run_add hrunQ (1+d),run_add hnextQ d]
    exact hdone
  · rw [show a+1+b+1+d = a+(1+(b+(1+d))) by omega,
      run_add hrunP (1+(b+(1+d))),run_add hnextP (b+(1+d)),
      run_add hrunQ (1+d),run_add hnextQ d]
    exact hpacket

#print axioms pair_to_packet

end
end CurrentAdditive.GaussPivotPairToFinish32
