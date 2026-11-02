import CurrentAdditive.IndexedCodeDPacketBuilderExact
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! Physical framing of the outer Code D record request. The source and
unary index begin in distinct scheduler cells. The fixed serializer writes
the packet in cell 5, and a fixed preserving broadcast installs it in the
record getter's input cell 0. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

theorem packetBuilderFinal_scratch_empty
    (S : StackN contextTwoSize → List Bool) (word : List Bool)
    (p : ℕ) (Sf : BitMachineBankSerialize.Bank 10) :
    packetBuilderFinal contextTwoSize S word p Sf
      (22 : StackN contextTwoSize) = [] := by
  change (BitMachineStackEmbedding.bank (packetAmbient contextTwoSize)
      (packetAfterCopies contextTwoSize S word p)
      (BitMachineStackEmbedding.bank packetLocate
        (packetIndexCopied
          (packetWordCopied
            (fun k : packetStack => S (packetAmbient contextTwoSize k)) word)
          (List.replicate p true))
        (BitMachineBankSerialize.contents Sf [] []
          (codeDGetterPacket word p))))
        (packetAmbient contextTwoSize 22) = []
  rw [BitMachineStackEmbedding.bank_at]
  change (BitMachineStackEmbedding.bank packetLocate _ _)
    (packetLocate (.inr (1 : Fin 3))) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem outer_packet_framed {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (S : StackN contextTwoSize → List Bool)
    (hword : S (packetAmbient contextTwoSize 3) = encodedSource out)
    (hindex : S (packetAmbient contextTwoSize 4) =
      List.replicate j.val true)
    (h17 : S (packetAmbient contextTwoSize 17) = [])
    (h18 : S (packetAmbient contextTwoSize 18) = [])
    (h22 : S (packetAmbient contextTwoSize 22) = [])
    (hblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetAmbient contextTwoSize (packetLocate (.inl i))) = [])
    (h21 : S (packetAmbient contextTwoSize 21) = [])
    (h5 : S (packetAmbient contextTwoSize 5) = [])
    (h0 : S (0 : StackN contextTwoSize) = []) :
    ∃ t ≤ ((2*(encodedSource out).length+4 + (2*j.val+4) + 1) +
      (2*(codeDGetterPacket (encodedSource out) j.val).length+4) + 1) +
      (2*(codeDGetterPacket (encodedSource out) j.val).length+3) + 1,
      ∃ Sf : BitMachineBankSerialize.Bank 10,
      let T := packetBuilderFinal contextTwoSize S (encodedSource out) j.val Sf
      let U := SourceClausePreservingBroadcast.result
        (5 : StackN contextTwoSize) 22 [0]
        (codeDGetterPacket (encodedSource out) j.val) T
      ((advance (BitMachineRawSequence.program
        (packetBuilderProgram contextTwoSize)
        (SourceClausePreservingBroadcast.program
          (5 : StackN contextTwoSize) 22 [0])
        SourceClausePreservingBroadcast.Label.scan
        ((((), none), ((), none)), none) ((), none)))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.inl .scan)))),
            (((((), none), ((), none)), none), ((), none)), S⟩ :
            TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
        ⟨none, (((((), none), ((), none)), none), ((), none)), U⟩ ∧
      U (0 : StackN contextTwoSize) =
        codeDGetterPacket (encodedSource out) j.val := by
  let word := encodedSource out
  let packet := codeDGetterPacket word j.val
  obtain ⟨tb, htb, Sf, hbuilder, hpacket⟩ :=
    packet_builder_stitched_exact contextTwoSize S word j.val
      hword hindex h17 h18 h22 hblank h21 h5
  let T := packetBuilderFinal contextTwoSize S word j.val Sf
  have htemp : T (22 : StackN contextTwoSize) = [] :=
    packetBuilderFinal_scratch_empty S word j.val Sf
  have hzero : T (0 : StackN contextTwoSize) = [] := by
    have haway : ¬ ∃ k : BitMachineBankSerialize.Stack 10,
        packetLocate k = (0 : packetStack) := by
      rintro ⟨k, hk⟩
      cases k with
      | inl i =>
          have hv := congrArg Fin.val hk
          dsimp [packetLocate] at hv
          omega
      | inr i => fin_cases i <;> simp [packetLocate] at hk
    have hz := packetBuilderFinal_at_untouched_low contextTwoSize
      S word j.val Sf 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) haway
    simpa only [T] using hz.trans h0
  have hb := SourceClausePreservingBroadcast.run_halt
    (5 : StackN contextTwoSize) 22 [0]
    (by decide) (by decide) (by decide) (by decide)
    packet T hpacket htemp
  let U := SourceClausePreservingBroadcast.result
    (5 : StackN contextTwoSize) 22 [0] packet T
  have hout : U (0 : StackN contextTwoSize) = packet := by
    have ht := SourceClausePreservingBroadcast.target_written
      (5 : StackN contextTwoSize) 22 [0]
      (by decide) (by decide) (by decide)
      packet T 0 (by simp)
    simpa [U, hzero] using ht
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (packetBuilderProgram contextTwoSize)
    (SourceClausePreservingBroadcast.program
      (5 : StackN contextTwoSize) 22 [0])
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inl .scan)))
    SourceClausePreservingBroadcast.Label.scan
    ((((), none), ((), none)), none)
    ((((), none), ((), none)), none)
    ((), none) ((), none) S T U tb (2*packet.length+3)
    hbuilder hb
  refine ⟨t, ?_, Sf, hr, hout⟩
  dsimp [word, packet] at htb ht ⊢
  omega

#print axioms packetBuilderFinal_scratch_empty
#print axioms outer_packet_framed

end CurrentAdditive.IndexedExecutableStepRecovery
