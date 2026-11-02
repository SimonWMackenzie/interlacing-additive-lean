import CurrentAdditive.IndexedCodeDCoordinatePacketSerialize

/-! Joining the two preserving copy runs to the literal ten-field serializer.
The only data initially present are the retained encoded word and unary index;
the packet output cell and serializer work cells are blank. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

theorem packet_other_preserved (S : packetStack → List Bool)
    (word index : List Bool) (x : packetStack)
    (h3 : x ≠ 3) (h4 : x ≠ 4) (h17 : x ≠ 17)
    (h18 : x ≠ 18) (h22 : x ≠ 22) :
    packetIndexCopied (packetWordCopied S word) index x = S x := by
  rw [packetIndexCopied,
    SourceClausePreservingBroadcast.other_preserved
      (4 : packetStack) 22 [17] index (packetWordCopied S word) x
      h4 h22 (by simpa using h17),
    packetWordCopied,
    SourceClausePreservingBroadcast.other_preserved
      (3 : packetStack) 22 [18] word S x
      h3 h22 (by simpa using h18)]

theorem coordinatePacketBank_other (word : List Bool) (p : ℕ)
    (i : Fin 10) (h7 : i ≠ 7) (h8 : i ≠ 8) :
    coordinatePacketBank word p i = [] := by
  fin_cases i <;> simp_all [coordinatePacketBank,
    PreservingV2Program.initialBank]

theorem coordinate_packet_loaded
    (S : packetStack → List Bool) (word : List Bool) (p : ℕ)
    (hword : S 3 = word)
    (hindex : S 4 = List.replicate p true)
    (h17 : S 17 = []) (h18 : S 18 = []) (h22 : S 22 = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetLocate (.inl i)) = [])
    (h21 : S 21 = []) (h5 : S 5 = []) :
    let S2 := packetIndexCopied
      (packetWordCopied S word) (List.replicate p true)
    ∀ k : BitMachineBankSerialize.Stack 10,
      (BitMachineBankSerialize.contents
        (coordinatePacketBank word p) [] [] []) k =
        S2 (packetLocate k) := by
  dsimp only
  let index := List.replicate p true
  let S2 := packetIndexCopied (packetWordCopied S word) index
  have hcopies := coordinate_packet_copy_runs S word index
    hword hindex h18 h17 h22
  change _ ∧ _ ∧ S2 3 = word ∧ S2 4 = index ∧
    S2 18 = word ∧ S2 17 = index at hcopies
  obtain ⟨_, _, _, _, hwordcopy, hindexcopy⟩ := hcopies
  intro k
  cases k with
  | inl i =>
    by_cases h7 : i = 7
    · subst i
      change index = S2 17
      exact hindexcopy.symm
    · by_cases h8 : i = 8
      · subst i
        change word = S2 18
        exact hwordcopy.symm
      · have hx3 : packetLocate (.inl i) ≠ (3 : packetStack) := by
          intro h; have hv := congrArg Fin.val h; dsimp [packetLocate] at hv; omega
        have hx4 : packetLocate (.inl i) ≠ (4 : packetStack) := by
          intro h; have hv := congrArg Fin.val h; dsimp [packetLocate] at hv; omega
        have hx17 : packetLocate (.inl i) ≠ (17 : packetStack) := by
          intro h; have hv := congrArg Fin.val h; dsimp [packetLocate] at hv
          apply h7
          apply Fin.ext
          omega
        have hx18 : packetLocate (.inl i) ≠ (18 : packetStack) := by
          intro h; have hv := congrArg Fin.val h; dsimp [packetLocate] at hv
          apply h8
          apply Fin.ext
          omega
        have hx22 : packetLocate (.inl i) ≠ (22 : packetStack) := by
          intro h; have hv := congrArg Fin.val h; dsimp [packetLocate] at hv; omega
        have hp := packet_other_preserved S word index
          (packetLocate (.inl i)) hx3 hx4 hx17 hx18 hx22
        have hz := hblank i h7 h8
        have hb := coordinatePacketBank_other word p i h7 h8
        change S2 (packetLocate (.inl i)) =
          S (packetLocate (.inl i)) at hp
        change coordinatePacketBank word p i =
          S2 (packetLocate (.inl i))
        rw [hb, hp, hz]
  | inr i =>
    fin_cases i
    · have hx : S2 21 = [] := by
        rw [show S2 21 = S 21 from packet_other_preserved S word index 21
          (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact h21
      simpa [BitMachineBankSerialize.contents, packetLocate] using hx.symm
    · have hx : S2 22 = [] := by
        simp [S2, packetIndexCopied,
          SourceClausePreservingBroadcast.result]
      simpa [BitMachineBankSerialize.contents, packetLocate] using hx.symm
    · have hx : S2 5 = [] := by
        rw [show S2 5 = S 5 from packet_other_preserved S word index 5
          (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact h5
      simpa [BitMachineBankSerialize.contents, packetLocate] using hx.symm

theorem coordinate_packet_serialized_from_sources
    (S : packetStack → List Bool) (word : List Bool) (p : ℕ)
    (hword : S 3 = word)
    (hindex : S 4 = List.replicate p true)
    (h17 : S 17 = []) (h18 : S 18 = []) (h22 : S 22 = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetLocate (.inl i)) = [])
    (h21 : S 21 = []) (h5 : S 5 = []) :
    let S2 := packetIndexCopied
      (packetWordCopied S word) (List.replicate p true)
    ∃ t ≤ 2*(codeDGetterPacket word p).length+2,
      ∃ Sf : BitMachineBankSerialize.Bank 10,
        packetSerializeRun t
          (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig) =
        packetFrame S2
          (BitMachineBankSerialize.cfg none none Sf [] []
            (codeDGetterPacket word p)) := by
  dsimp only
  let S2 := packetIndexCopied
    (packetWordCopied S word) (List.replicate p true)
  have hloaded := coordinate_packet_loaded S word p
    hword hindex h17 h18 h22 hblank h21 h5
  change ∀ k : BitMachineBankSerialize.Stack 10,
    (BitMachineBankSerialize.contents
      (coordinatePacketBank word p) [] [] []) k =
      S2 (packetLocate k) at hloaded
  have hbank := BitMachineStackEmbedding.bank_eq_self
    packetLocate S2
    (BitMachineBankSerialize.contents
      (coordinatePacketBank word p) [] [] []) hloaded
  have hstart : packetFrame S2
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (coordinatePacketBank word p) [] [] []) =
      (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig) := by
    simp only [packetFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      BitMachineBankSerialize.cfg, hbank]
    rfl
  obtain ⟨t, ht, Sf, hr⟩ := coordinate_packet_serialize
    word p S2 []
  refine ⟨t, ht, Sf, ?_⟩
  rw [hstart] at hr
  simpa only [List.append_nil] using hr

theorem coordinate_packet_output_cell (S : packetStack → List Bool)
    (word : List Bool) (p : ℕ)
    (Sf : BitMachineBankSerialize.Bank 10) :
    (packetFrame S (BitMachineBankSerialize.cfg none none Sf [] []
      (codeDGetterPacket word p))).stk 5 = codeDGetterPacket word p := by
  change BitMachineStackEmbedding.bank packetLocate S
    (BitMachineBankSerialize.contents Sf [] []
      (codeDGetterPacket word p)) (packetLocate (.inr (2 : Fin 3))) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

#print axioms packet_other_preserved
#print axioms coordinate_packet_loaded
#print axioms coordinate_packet_serialized_from_sources
#print axioms coordinate_packet_output_cell

end CurrentAdditive.IndexedExecutableStepRecovery
