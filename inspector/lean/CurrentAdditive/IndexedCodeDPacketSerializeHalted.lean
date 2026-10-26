import CurrentAdditive.IndexedCodeDPacketCopyStitched

/-! The ambient serializer has an exact halted full-bank output, so it can be
joined to the two physical copy phases by raw program sequencing. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

theorem ambient_serializer_halted (N : ℕ)
    (S : packetStack → List Bool)
    (A : StackN N → List Bool)
    (word : List Bool) (p : ℕ)
    (hword : S 3 = word)
    (hindex : S 4 = List.replicate p true)
    (h17 : S 17 = []) (h18 : S 18 = []) (h22 : S 22 = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetLocate (.inl i)) = [])
    (h21 : S 21 = []) (h5 : S 5 = [])
    (hready : ∀ k : packetStack,
      A (packetAmbient N k) =
        packetIndexCopied (packetWordCopied S word)
          (List.replicate p true) k) :
    ∃ t ≤ 2*(codeDGetterPacket word p).length+4,
      ∃ Sf : BitMachineBankSerialize.Bank 10,
      let S2 := packetIndexCopied (packetWordCopied S word)
        (List.replicate p true)
      let T := (ambientPacketFrame A
        (⟨none, none,
          (packetFrame S2
            (BitMachineBankSerialize.cfg none none Sf [] []
              (codeDGetterPacket word p))).stk⟩ : PacketConfig)
        (some (.inr ()))).stk
      ((advance (ambientSerializeProgram N))^[t])
        (⟨some (.inl (.inl (.emit 0))), none, A⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, none, T⟩ ∧
      T (packetAmbient N 5) = codeDGetterPacket word p := by
  let S2 := packetIndexCopied (packetWordCopied S word)
    (List.replicate p true)
  obtain ⟨s, hs, Sf, hr⟩ := coordinate_packet_serialized_from_sources
    S word p hword hindex h17 h18 h22 hblank h21 h5
  have hr' : ((advance packetSerializeProgram)^[s])
      (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig) =
      packetFrame S2
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p)) := by
    simpa only [packetSerializeRun] using hr
  have hhalt : (((advance packetSerializeProgram)^[s+1])
      (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig)).l = none := by
    rw [Function.iterate_succ_apply', hr']
    rfl
  obtain ⟨u, hu, hsim⟩ := BitMachineStackEmbedding.outputs
    (packetAmbient N) A Sum.inl id id (by intro v; rfl)
    (some (.inr ())) packetSerializeProgram
    (ambientSerializeProgram N) (by intro l; rfl)
    (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig)
    (s+1) hhalt
  have hlow : S2 = fun k : packetStack => A (packetAmbient N k) := by
    funext k
    exact (hready k).symm
  have hstart : ambientPacketFrame A
      (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig)
      (some (.inr ())) =
      (⟨some (.inl (.inl (.emit 0))), none, A⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) _ _) := by
    rw [show (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig) =
      ⟨some (.inl (.emit 0)), none,
        fun k : packetStack => A (packetAmbient N k)⟩ by
        simp [hlow]]
    exact ambientPacketFrame_initial A
      (Sum.inl (BitMachineBankSerialize.Label.emit 0) : PacketLabel) none
      (some (.inr ()))
  let T := (ambientPacketFrame A
    (⟨none, none,
      (packetFrame S2
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p))).stk⟩ : PacketConfig)
    (some (.inr ()))).stk
  refine ⟨u+1, by omega, Sf, ?_⟩
  dsimp only
  constructor
  · rw [Function.iterate_succ_apply', ← hstart]
    change advance (ambientSerializeProgram N)
      (((advance (ambientSerializeProgram N))^[u])
        (BitMachineStackEmbedding.cfg (packetAmbient N) A Sum.inl id
          (some (.inr ()))
          (⟨some (.inl (.emit 0)), none, S2⟩ : PacketConfig))) = _
    rw [hsim, Function.iterate_succ_apply', hr']
    rfl
  · change BitMachineStackEmbedding.bank (packetAmbient N) A
      (packetFrame S2
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p))).stk
        (packetAmbient N 5) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact coordinate_packet_output_cell S2 word p Sf

#print axioms ambient_serializer_halted

end CurrentAdditive.IndexedExecutableStepRecovery
