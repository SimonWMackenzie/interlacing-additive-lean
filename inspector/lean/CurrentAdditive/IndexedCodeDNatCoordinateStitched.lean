import CurrentAdditive.IndexedCodeDRecordPacketStitched

/-! The packet builder retains the exact scratch, target, and private cells
needed for the following physical coordinate getter. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open Turing

noncomputable def numericCoordinateProgram :=
  BitMachineRawSequence.program recordPacketProgram
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
      coordinateSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
      coordinateSlots)
    ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        recordSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        wordSlots),
     ((((), none), ((), none)), none))
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      coordinateSlots)

theorem packet_final_coordinate_ready
    (S : StackN contextTwoSize → List Bool)
    (record word : List Bool) (p : ℕ)
    (Sf : BitMachineBankSerialize.Bank 10)
    (h2 : S (2 : StackN contextTwoSize) = [])
    (h6 : S (6 : StackN contextTwoSize) = [])
    (hblank : ∀ k, S (recordSlots.machine k) = []) :
    let S2 := recordWordFinal S record word
    let T := packetBuilderFinal contextTwoSize S2 word p Sf
    T coordinateSlots.target = [] ∧
    T coordinateSlots.scratch = [] ∧
    (∀ k, T (coordinateSlots.machine k) = []) := by
  dsimp only
  let S2 := recordWordFinal S record word
  let T := packetBuilderFinal contextTwoSize S2 word p Sf
  constructor
  · change T (packetAmbient contextTwoSize (6 : packetStack)) = []
    change packetBuilderFinal contextTwoSize S2 word p Sf
      (packetAmbient contextTwoSize 6) = []
    rw [packetBuilderFinal_at_two_six contextTwoSize S2 word p Sf 6
      (Or.inr rfl)]
    change recordWordFinal S record word
      (6 : StackN contextTwoSize) = []
    rw [recordWordFinal_other S record word 6 (by decide) (by decide)]
    exact h6
  constructor
  · change T (packetAmbient contextTwoSize (2 : packetStack)) = []
    change packetBuilderFinal contextTwoSize S2 word p Sf
      (packetAmbient contextTwoSize 2) = []
    rw [packetBuilderFinal_at_two_six contextTwoSize S2 word p Sf 2
      (Or.inl rfl)]
    change recordWordFinal S record word
      (2 : StackN contextTwoSize) = []
    rw [recordWordFinal_other S record word 2 (by decide) (by decide)]
    exact h2
  · intro k
    have hk : 32 ≤ (coordinateSlots.machine k).val := by
      dsimp [coordinateSlots, recordSlots]
      omega
    change packetBuilderFinal contextTwoSize S2 word p Sf
      (coordinateSlots.machine k) = []
    rw [packetBuilderFinal_at_private contextTwoSize S2 word p Sf
      (coordinateSlots.machine k) hk]
    have hne1 : coordinateSlots.machine k ≠ (1 : StackN contextTwoSize) := by
      intro h
      have hv := congrArg Fin.val h
      change (coordinateSlots.machine k).val = 1 at hv
      omega
    have hne3 : coordinateSlots.machine k ≠ (3 : StackN contextTwoSize) := by
      intro h
      have hv := congrArg Fin.val h
      change (coordinateSlots.machine k).val = 3 at hv
      omega
    change recordWordFinal S record word (coordinateSlots.machine k) = []
    rw [recordWordFinal_other S record word
      (coordinateSlots.machine k) hne1 hne3]
    exact hblank k

theorem numeric_coordinate_stitched {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) (S : StackN contextTwoSize → List Bool)
    (hsource : S recordSlots.source =
      codeDGetterPacket (encodedSource out) j.val)
    (htarget1 : S recordSlots.target = [])
    (htarget2 : S wordSlots.target = [])
    (hscratch : S recordSlots.scratch = [])
    (hblank1 : ∀ k, S (recordSlots.machine k) = [])
    (hblank2 : ∀ k, S (wordSlots.machine k) = [])
    (hindex : S (packetAmbient contextTwoSize 4) =
      List.replicate p.val true)
    (h17 : S (packetAmbient contextTwoSize 17) = [])
    (h18 : S (packetAmbient contextTwoSize 18) = [])
    (h22 : S (packetAmbient contextTwoSize 22) = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetAmbient contextTwoSize (packetLocate (.inl i))) = [])
    (h21 : S (packetAmbient contextTwoSize 21) = [])
    (h5 : S (packetAmbient contextTwoSize 5) = [])
    (h6 : S (packetAmbient contextTwoSize 6) = []) :
    let pre := (codeDRecords out).take j.val
    let selected := (codeDRecords out)[codeDRecordIndex out j]
    let suffix := (codeDRecords out).drop (j.val + 1)
    let source := encodedSource out
    let input := codeDGetterPacket source j.val
    let finalBank := codeDGetterFinalBank source suffix selected
    let packed := BitMachineBankCodec.encode finalBank
    let getterClock := (2*10+1)*(input.length+1) +
      (2*source.length+5+
        (4*(pre ++ selected :: suffix).length.bits.length+6+
          IndexedFieldProgram.fieldCost (pre ++ [selected]))) +
      2*packed.length+4
    let T1 := getterClock + 2*packed.length+2 + (2*10+4)*(packed.length+1)
    let record := encodeEntry (canonicalEntry out[j])
    let word := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
    let T2 := (2*2+4)*(record.length+1)
    let B1 := uniformBound codeDSelectedRecordMachine input T1 +
      uniformBound codeDWordFieldMachine record T2 + 1
    let B2 := (2*word.length+4 + (2*p.val+4) + 1) +
      (2*(codeDGetterPacket word p.val).length+4) + 1
    let coordPre := (canonicalEntry out[j]).word.take p.val
    let coordWord := (out[j].1 p).bits
    let coordSuffix := (canonicalEntry out[j]).word.drop (p.val + 1)
    let coordInput := codeDGetterPacket word p.val
    let coordFinalBank := codeDGetterFinalBank word coordSuffix coordWord
    let coordPacked := BitMachineBankCodec.encode coordFinalBank
    let coordClock := (2*10+1)*(coordInput.length+1) +
      (2*word.length+5+
        (4*(coordPre ++ coordWord :: coordSuffix).length.bits.length+6+
          IndexedFieldProgram.fieldCost (coordPre ++ [coordWord]))) +
      2*coordPacked.length+4
    let T3 := coordClock + 2*coordPacked.length+2 +
      (2*10+4)*(coordPacked.length+1)
    let B3 := uniformBound codeDSelectedRecordMachine coordInput T3
    let S2 := recordWordFinal S record word
    ∃ t ≤ (B1+B2+1)+B3+1,
      ∃ Sf : BitMachineBankSerialize.Bank 10,
      let T := packetBuilderFinal contextTwoSize S2 word p.val Sf
      ((advance numericCoordinateProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
                recordSlots)))),
          (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots),
            ((((), none), ((), none)), none)),
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              coordinateSlots), S⟩ :
          TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
        ⟨none,
          (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots),
            ((((), none), ((), none)), none)),
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              coordinateSlots),
          Function.update T coordinateSlots.target (out[j].1 p).bits⟩ := by
  dsimp only
  let record := encodeEntry (canonicalEntry out[j])
  let word := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
  let S2 := recordWordFinal S record word
  obtain ⟨trp, htrp, Sf, hrrp, hpacket⟩ :=
    record_packet_stitched out j p S hsource htarget1 htarget2 hscratch
      hblank1 hblank2 hindex h17 h18 h22 hblank h21 h5
  let T := packetBuilderFinal contextTwoSize S2 word p.val Sf
  have hready := packet_final_coordinate_ready S record word p.val Sf
    hscratch h6 hblank1
  change T coordinateSlots.target = [] ∧
    T coordinateSlots.scratch = [] ∧
    (∀ k, T (coordinateSlots.machine k) = []) at hready
  rcases hready with ⟨htarget, hscratch', hblank'⟩
  have hpacket' : T coordinateSlots.source =
      codeDGetterPacket word p.val := by
    change T (packetAmbient contextTwoSize 5) = _
    exact hpacket
  obtain ⟨tc, htc, hrc⟩ := codeD_coordinate_context_run
    out j p T hpacket' htarget hscratch' hblank'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    recordPacketProgram
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
      coordinateSlots)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
          recordSlots)))
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
      coordinateSlots)
    ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        recordSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        wordSlots),
     ((((), none), ((), none)), none))
    ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        recordSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        wordSlots),
     ((((), none), ((), none)), none))
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      coordinateSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      coordinateSlots)
    S T (Function.update T coordinateSlots.target (out[j].1 p).bits)
    trp tc hrrp hrc
  exact ⟨t, by omega, Sf, hr⟩

#print axioms packet_final_coordinate_ready
#print axioms numeric_coordinate_stitched

end CurrentAdditive.IndexedExecutableStepRecovery
