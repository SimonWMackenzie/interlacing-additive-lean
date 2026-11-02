import CurrentAdditive.IndexedCodeDPacketSerializeHalted

/-! A fixed physical program copies a retained word and unary coordinate,
then prints the exact V2 getter packet in the ambient scheduler bank. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

def packetBuilderProgram (N : ℕ) :=
  BitMachineRawSequence.program (packetCopyProgram N)
    (ambientSerializeProgram N)
    (Sum.inl (Sum.inl (BitMachineBankSerialize.Label.emit 0)))
    (((), none), ((), none)) none

theorem packet_builder_stitched (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool) (p : ℕ)
    (hword : S (packetAmbient N 3) = word)
    (hindex : S (packetAmbient N 4) = List.replicate p true)
    (h17 : S (packetAmbient N 17) = [])
    (h18 : S (packetAmbient N 18) = [])
    (h22 : S (packetAmbient N 22) = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetAmbient N (packetLocate (.inl i))) = [])
    (h21 : S (packetAmbient N 21) = [])
    (h5 : S (packetAmbient N 5) = []) :
    ∃ t ≤ (2*word.length+4 + (2*p+4) + 1) +
      (2*(codeDGetterPacket word p).length+4) + 1,
      ∃ T : StackN N → List Bool,
        ((advance (packetBuilderProgram N))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.inl .scan))),
            ((((), none), ((), none)), none), S⟩ :
            TM2.Cfg (fun _ : StackN N => Bool) _ _) =
          ⟨none, ((((), none), ((), none)), none), T⟩ ∧
        T (packetAmbient N 5) = codeDGetterPacket word p := by
  let low := fun k : packetStack => S (packetAmbient N k)
  let S1 := (ambientPacketFrame S
    (⟨none, ((), none), packetWordCopied low word⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk
  let low1 := fun k : packetStack => S1 (packetAmbient N k)
  let S2 := (ambientPacketFrame S1
    (⟨none, ((), none), packetIndexCopied low1
      (List.replicate p true)⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk
  have hlow1 (k : packetStack) :
      low1 k = packetWordCopied low word k := by
    change (BitMachineStackEmbedding.bank (packetAmbient N) S
      (packetWordCopied low word)) (packetAmbient N k) = _
    exact BitMachineStackEmbedding.bank_at (packetAmbient N) S
      (packetWordCopied low word) k
  have hready (k : packetStack) :
      S2 (packetAmbient N k) =
        packetIndexCopied (packetWordCopied low word)
          (List.replicate p true) k := by
    change (BitMachineStackEmbedding.bank (packetAmbient N) S1
      (packetIndexCopied low1 (List.replicate p true)))
        (packetAmbient N k) = _
    rw [BitMachineStackEmbedding.bank_at]
    rw [show low1 = packetWordCopied low word from funext hlow1]
  obtain ⟨tc, htc, hrc⟩ := packet_copy_stitched N S word
    (List.replicate p true) hword hindex h22
  have htc' : tc ≤ 2*word.length+4 + (2*p+4) + 1 := by
    simpa only [List.length_replicate] using htc
  have hword' : low 3 = word := hword
  have hindex' : low 4 = List.replicate p true := hindex
  have h17' : low 17 = [] := h17
  have h18' : low 18 = [] := h18
  have h22' : low 22 = [] := h22
  have hblank' : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      low (packetLocate (.inl i)) = [] := hblank
  have h21' : low 21 = [] := h21
  have h5' : low 5 = [] := h5
  obtain ⟨ts, hts, Sf, hrs, hout⟩ := ambient_serializer_halted
    N low S2 word p hword' hindex' h17' h18' h22'
    hblank' h21' h5' hready
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (packetCopyProgram N) (ambientSerializeProgram N)
    (BitMachineRawSequence.leftLabel (.inl .scan))
    (.inl (.inl (.emit 0)))
    (((), none), ((), none)) (((), none), ((), none)) none none
    S S2 _ tc ts hrc hrs
  exact ⟨t, by omega, _, hr, hout⟩

#print axioms packet_builder_stitched

end CurrentAdditive.IndexedExecutableStepRecovery
