import CurrentAdditive.IndexedCodeDPacketBuilderExact

/-! The actual numeric Code D record selector, word-field extractor, and
packet builder run as one fixed physical program. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open Turing

noncomputable def recordWordFinal (S : StackN contextTwoSize → List Bool)
    (record word : List Bool) :=
  Function.update (Function.update S recordSlots.target record)
    wordSlots.target word

theorem recordWordFinal_at_word
    (S : StackN contextTwoSize → List Bool)
    (record word : List Bool) :
    recordWordFinal S record word (3 : StackN contextTwoSize) = word := by
  change recordWordFinal S record word wordSlots.target = word
  simp [recordWordFinal]

theorem recordWordFinal_other
    (S : StackN contextTwoSize → List Bool)
    (record word : List Bool) (i : StackN contextTwoSize)
    (h1 : i ≠ (1 : StackN contextTwoSize))
    (h3 : i ≠ (3 : StackN contextTwoSize)) :
    recordWordFinal S record word i = S i := by
  change (Function.update
    (Function.update S (1 : StackN contextTwoSize) record)
    (3 : StackN contextTwoSize) word) i = S i
  simp [h1, h3]

noncomputable def recordPacketProgram :=
  BitMachineRawSequence.program recordWordProgram
    (packetBuilderProgram contextTwoSize)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (Sum.inl SourceClausePreservingBroadcast.Label.scan)))
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control recordSlots,
     CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control wordSlots)
    ((((), none), ((), none)), none)

theorem recordWordFinal_at_low_other
    (S : StackN contextTwoSize → List Bool)
    (record word : List Bool) (i : packetStack)
    (h1 : i ≠ 1) (h3 : i ≠ 3) :
    recordWordFinal S record word (packetAmbient contextTwoSize i) =
      S (packetAmbient contextTwoSize i) := by
  apply recordWordFinal_other
  · intro h
    have hv := congrArg Fin.val h
    dsimp [packetAmbient] at hv
    apply h1
    apply Fin.ext
    simpa using hv
  · intro h
    have hv := congrArg Fin.val h
    dsimp [packetAmbient] at hv
    apply h3
    apply Fin.ext
    simpa using hv

theorem recordWordFinal_packet_ready
    (S : StackN contextTwoSize → List Bool)
    (record word : List Bool) (p : ℕ)
    (hindex : S (packetAmbient contextTwoSize 4) =
      List.replicate p true)
    (h17 : S (packetAmbient contextTwoSize 17) = [])
    (h18 : S (packetAmbient contextTwoSize 18) = [])
    (h22 : S (packetAmbient contextTwoSize 22) = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetAmbient contextTwoSize (packetLocate (.inl i))) = [])
    (h21 : S (packetAmbient contextTwoSize 21) = [])
    (h5 : S (packetAmbient contextTwoSize 5) = []) :
    let T := recordWordFinal S record word
    T (packetAmbient contextTwoSize 3) = word ∧
    T (packetAmbient contextTwoSize 4) = List.replicate p true ∧
    T (packetAmbient contextTwoSize 17) = [] ∧
    T (packetAmbient contextTwoSize 18) = [] ∧
    T (packetAmbient contextTwoSize 22) = [] ∧
    (∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      T (packetAmbient contextTwoSize (packetLocate (.inl i))) = []) ∧
    T (packetAmbient contextTwoSize 21) = [] ∧
    T (packetAmbient contextTwoSize 5) = [] := by
  dsimp only
  constructor
  · change recordWordFinal S record word (3 : StackN contextTwoSize) = word
    exact recordWordFinal_at_word S record word
  constructor
  · rw [recordWordFinal_at_low_other S record word 4
      (by decide) (by decide)]
    exact hindex
  constructor
  · rw [recordWordFinal_at_low_other S record word 17
      (by decide) (by decide)]
    exact h17
  constructor
  · rw [recordWordFinal_at_low_other S record word 18
      (by decide) (by decide)]
    exact h18
  constructor
  · rw [recordWordFinal_at_low_other S record word 22
      (by decide) (by decide)]
    exact h22
  constructor
  · intro i hi7 hi8
    have hne1 : packetLocate (.inl i) ≠ (1 : packetStack) := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [packetLocate] at hv
      omega
    have hne3 : packetLocate (.inl i) ≠ (3 : packetStack) := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [packetLocate] at hv
      omega
    rw [recordWordFinal_at_low_other S record word
      (packetLocate (.inl i)) hne1 hne3]
    exact hblank i hi7 hi8
  constructor
  · rw [recordWordFinal_at_low_other S record word 21
      (by decide) (by decide)]
    exact h21
  · rw [recordWordFinal_at_low_other S record word 5
      (by decide) (by decide)]
    exact h5

theorem record_packet_stitched {q : ℕ}
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
    (h5 : S (packetAmbient contextTwoSize 5) = []) :
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
    let S2 := recordWordFinal S record word
    ∃ t ≤ B1 + B2 + 1,
      ∃ Sf : BitMachineBankSerialize.Bank 10,
      ((advance recordPacketProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
              recordSlots))),
          ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots),
           ((((), none), ((), none)), none)), S⟩ :
          TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
        ⟨none,
          ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots),
           ((((), none), ((), none)), none)),
          packetBuilderFinal contextTwoSize S2 word p.val Sf⟩ ∧
      packetBuilderFinal contextTwoSize S2 word p.val Sf
        (packetAmbient contextTwoSize 5) =
        codeDGetterPacket word p.val := by
  dsimp only
  let record := encodeEntry (canonicalEntry out[j])
  let word := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
  let S2 := recordWordFinal S record word
  obtain ⟨tr, htr, hrr⟩ := codeD_record_word_stitched out j S
    hsource htarget1 htarget2 hscratch hblank1 hblank2
  have hready := recordWordFinal_packet_ready S record word p.val
    hindex h17 h18 h22 hblank h21 h5
  change S2 (packetAmbient contextTwoSize 3) = word ∧
    S2 (packetAmbient contextTwoSize 4) = List.replicate p.val true ∧
    S2 (packetAmbient contextTwoSize 17) = [] ∧
    S2 (packetAmbient contextTwoSize 18) = [] ∧
    S2 (packetAmbient contextTwoSize 22) = [] ∧
    (∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S2 (packetAmbient contextTwoSize (packetLocate (.inl i))) = []) ∧
    S2 (packetAmbient contextTwoSize 21) = [] ∧
    S2 (packetAmbient contextTwoSize 5) = [] at hready
  rcases hready with ⟨hw, hi, h17', h18', h22', hb, h21', h5'⟩
  obtain ⟨tp, htp, Sf, hrp, hout⟩ := packet_builder_stitched_exact
    contextTwoSize S2 word p.val hw hi h17' h18' h22' hb h21' h5'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    recordWordProgram (packetBuilderProgram contextTwoSize)
    (BitMachineRawSequence.leftLabel
      (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
        recordSlots))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inl .scan)))
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      recordSlots,
     CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      wordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      recordSlots,
     CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      wordSlots)
    ((((), none), ((), none)), none)
    ((((), none), ((), none)), none)
    S S2 (packetBuilderFinal contextTwoSize S2 word p.val Sf)
    tr tp hrr hrp
  dsimp only [word] at htp
  exact ⟨t, by omega, Sf, hr, hout⟩

#print axioms recordWordFinal_at_word
#print axioms recordWordFinal_other
#print axioms recordWordFinal_packet_ready
#print axioms record_packet_stitched

end CurrentAdditive.IndexedExecutableStepRecovery
