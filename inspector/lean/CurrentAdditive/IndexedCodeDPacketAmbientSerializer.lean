import CurrentAdditive.IndexedCodeDPacketAmbientIndex

/-! The literal V2 packet serializer runs inside the same extended scheduler
bank after its two data-preserving copy phases. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

def ambientSerializeProgram (N : ℕ) :=
  fun l : PacketLabel ⊕ Unit =>
    match l with
    | .inl l => BitMachineStackEmbedding.stmt
        (packetAmbient N) Sum.inl id id (some (.inr ()))
        (packetSerializeProgram l)
    | .inr () => (TM2.Stmt.halt :
        TM2.Stmt (fun _ : StackN N => Bool)
          (PacketLabel ⊕ Unit) PacketControl)

theorem ambient_coordinate_packet_serialize_run (N : ℕ)
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
    ∃ u ≤ 2*(codeDGetterPacket word p).length+3,
      let final := ((advance (ambientSerializeProgram N))^[u])
        (⟨some (.inl (.inl (.emit 0))), none, A⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _)
      final.stk (packetAmbient N 5) = codeDGetterPacket word p := by
  let S2 := packetIndexCopied (packetWordCopied S word)
    (List.replicate p true)
  obtain ⟨t, ht, Sf, hr⟩ := coordinate_packet_serialized_from_sources
    S word p hword hindex h17 h18 h22 hblank h21 h5
  let c : PacketConfig := ⟨some (.inl (.emit 0)), none, S2⟩
  have hr' : ((advance packetSerializeProgram)^[t]) c =
      packetFrame S2
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p)) := by
    simpa only [packetSerializeRun] using hr
  have hhalt : (((advance packetSerializeProgram)^[t+1]) c).l = none := by
    rw [Function.iterate_succ_apply', hr']
    rfl
  obtain ⟨u, hu, hsim⟩ := BitMachineStackEmbedding.outputs
    (packetAmbient N) A Sum.inl id id (by intro v; rfl)
    (some (.inr ())) packetSerializeProgram
    (ambientSerializeProgram N) (by intro l; rfl)
    c (t+1) hhalt
  have hlow : S2 = fun k : packetStack => A (packetAmbient N k) := by
    funext k
    exact (hready k).symm
  have hstart : ambientPacketFrame A c (some (.inr ())) =
      (⟨some (.inl (.inl (.emit 0))), none, A⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) _ _) := by
    rw [show c = (⟨some (.inl (.emit 0)), none,
      fun k : packetStack => A (packetAmbient N k)⟩ : PacketConfig) by
        simp [c, hlow]]
    exact ambientPacketFrame_initial A
      (Sum.inl (BitMachineBankSerialize.Label.emit 0) : PacketLabel) none
      (some (.inr ()))
  refine ⟨u, by omega, ?_⟩
  dsimp only
  rw [← hstart]
  change (((advance (ambientSerializeProgram N))^[u])
    (BitMachineStackEmbedding.cfg (packetAmbient N) A Sum.inl id
      (some (.inr ())) c)).stk (packetAmbient N 5) = _
  rw [hsim]
  rw [Function.iterate_succ_apply', hr']
  change (ambientPacketFrame A
    (advance packetSerializeProgram
      (packetFrame S2
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p)))) (some (.inr ()))).stk
      (packetAmbient N 5) = _
  rw [show advance packetSerializeProgram
      (packetFrame S2
        (BitMachineBankSerialize.cfg none none Sf [] []
          (codeDGetterPacket word p))) =
      ⟨none, none,
        (packetFrame S2
          (BitMachineBankSerialize.cfg none none Sf [] []
            (codeDGetterPacket word p))).stk⟩ from rfl]
  change BitMachineStackEmbedding.bank (packetAmbient N) A
    (packetFrame S2
      (BitMachineBankSerialize.cfg none none Sf [] []
        (codeDGetterPacket word p))).stk
    (packetAmbient N 5) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact coordinate_packet_output_cell S2 word p Sf

#print axioms ambient_coordinate_packet_serialize_run

end CurrentAdditive.IndexedExecutableStepRecovery
