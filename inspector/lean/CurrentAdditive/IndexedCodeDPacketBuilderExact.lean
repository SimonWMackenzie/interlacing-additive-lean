import CurrentAdditive.IndexedCodeDPacketBuilderStitched

/-! A fixed physical program copies a retained word and unary coordinate,
then prints the exact V2 getter packet in the ambient scheduler bank. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

noncomputable def packetAfterCopies (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool) (p : ℕ) :
    StackN N → List Bool :=
  let low := fun k : packetStack => S (packetAmbient N k)
  let S1 := (ambientPacketFrame S
    (⟨none, ((), none), packetWordCopied low word⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk
  let low1 := fun k : packetStack => S1 (packetAmbient N k)
  (ambientPacketFrame S1
    (⟨none, ((), none), packetIndexCopied low1
      (List.replicate p true)⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk

noncomputable def packetBuilderFinal (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool) (p : ℕ)
    (Sf : BitMachineBankSerialize.Bank 10) :
    StackN N → List Bool :=
  let low := fun k : packetStack => S (packetAmbient N k)
  let A := packetAfterCopies N S word p
  (ambientPacketFrame A
    (⟨none, none,
      (packetFrame
        (packetIndexCopied (packetWordCopied low word)
          (List.replicate p true))
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p))).stk⟩ : PacketConfig)
    (some (.inr ()))).stk

theorem packet_builder_stitched_exact (N : ℕ)
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
      ∃ Sf : BitMachineBankSerialize.Bank 10,
        ((advance (packetBuilderProgram N))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.inl .scan))),
            ((((), none), ((), none)), none), S⟩ :
            TM2.Cfg (fun _ : StackN N => Bool) _ _) =
          ⟨none, ((((), none), ((), none)), none),
            packetBuilderFinal N S word p Sf⟩ ∧
        packetBuilderFinal N S word p Sf (packetAmbient N 5) =
          codeDGetterPacket word p := by
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
  exact ⟨t, by omega, Sf, hr, hout⟩

theorem packetBuilderFinal_at_untouched_low (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool) (p : ℕ)
    (Sf : BitMachineBankSerialize.Bank 10)
    (i : packetStack)
    (h3 : i ≠ 3) (h4 : i ≠ 4) (h17 : i ≠ 17)
    (h18 : i ≠ 18) (h22 : i ≠ 22)
    (hlocate : ¬ ∃ k : BitMachineBankSerialize.Stack 10,
      packetLocate k = i) :
    packetBuilderFinal N S word p Sf (packetAmbient N i) =
      S (packetAmbient N i) := by
  let low := fun k : packetStack => S (packetAmbient N k)
  let index := List.replicate p true
  let copied := packetIndexCopied (packetWordCopied low word) index
  change (BitMachineStackEmbedding.bank (packetAmbient N)
    (packetAfterCopies N S word p)
    (BitMachineStackEmbedding.bank packetLocate copied
      (BitMachineBankSerialize.contents Sf [] []
        (codeDGetterPacket word p))))
      (packetAmbient N i) = _
  rw [BitMachineStackEmbedding.bank_at]
  rw [BitMachineStackEmbedding.bank_outside packetLocate copied _ i hlocate]
  exact packet_other_preserved low word index i
    h3 h4 h17 h18 h22

theorem packetBuilderFinal_at_private (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool) (p : ℕ)
    (Sf : BitMachineBankSerialize.Bank 10)
    (i : StackN N) (hi : 32 ≤ i.val) :
    packetBuilderFinal N S word p Sf i = S i := by
  have hout : ¬ ∃ k : packetStack, packetAmbient N k = i := by
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    dsimp [packetAmbient] at hv
    omega
  let low := fun k : packetStack => S (packetAmbient N k)
  let S1 := (ambientPacketFrame S
    (⟨none, ((), none), packetWordCopied low word⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk
  change (BitMachineStackEmbedding.bank (packetAmbient N)
    (packetAfterCopies N S word p) _) i = S i
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout]
  change (BitMachineStackEmbedding.bank (packetAmbient N) S1 _) i = S i
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout]
  change (BitMachineStackEmbedding.bank (packetAmbient N) S _) i = S i
  exact BitMachineStackEmbedding.bank_outside _ _ _ _ hout

theorem packetLocate_away_from_two_six
    (i : packetStack) (hi : i = 2 ∨ i = 6) :
    ¬ ∃ k : BitMachineBankSerialize.Stack 10,
      packetLocate k = i := by
  rintro ⟨k, hk⟩
  cases k with
  | inl j =>
      have hv := congrArg Fin.val hk
      dsimp [packetLocate] at hv
      rcases hi with rfl | rfl <;> omega
  | inr j =>
      fin_cases j <;> rcases hi with rfl | rfl <;>
        simp [packetLocate] at hk

theorem packetBuilderFinal_at_two_six (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool) (p : ℕ)
    (Sf : BitMachineBankSerialize.Bank 10)
    (i : packetStack) (hi : i = 2 ∨ i = 6) :
    packetBuilderFinal N S word p Sf (packetAmbient N i) =
      S (packetAmbient N i) := by
  have hne (n : packetStack) (hn : n = 3 ∨ n = 4 ∨ n = 17 ∨
      n = 18 ∨ n = 22) : i ≠ n := by
    rcases hi with hi | hi <;> rcases hn with hn | hn | hn | hn | hn <;>
      simp [hi, hn]
  exact packetBuilderFinal_at_untouched_low N S word p Sf i
    (hne 3 (Or.inl rfl))
    (hne 4 (Or.inr (Or.inl rfl)))
    (hne 17 (Or.inr (Or.inr (Or.inl rfl))))
    (hne 18 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (hne 22 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    (packetLocate_away_from_two_six i hi)

#print axioms packetBuilderFinal_at_untouched_low
#print axioms packetBuilderFinal_at_private
#print axioms packetBuilderFinal_at_two_six

#print axioms packet_builder_stitched_exact

end CurrentAdditive.IndexedExecutableStepRecovery
