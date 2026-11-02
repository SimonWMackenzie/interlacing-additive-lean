import CurrentAdditive.OuterPacketPhysicalJoin

/-! The framing run does not overwrite the next unary coordinate or private
machine region. This is the missing state invariant needed before cleanup. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore

theorem outer_packet_result_retains_coordinate {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (S : StackN contextTwoSize → List Bool)
    (Sf : BitMachineBankSerialize.Bank 10) :
    let T := packetBuilderFinal contextTwoSize S (encodedSource out) j.val Sf
    let U := SourceClausePreservingBroadcast.result
      (5 : StackN contextTwoSize) 22 [0]
      (codeDGetterPacket (encodedSource out) j.val) T
    U 6 = S 6 ∧
    (∀ k : StackN contextTwoSize, 32 ≤ k.val → U k = S k) := by
  dsimp only
  constructor
  · rw [SourceClausePreservingBroadcast.other_preserved
      (5 : StackN contextTwoSize) 22 [0]
      (codeDGetterPacket (encodedSource out) j.val)
      (packetBuilderFinal contextTwoSize S (encodedSource out) j.val Sf)
      6 (by decide) (by decide) (by decide)]
    exact packetBuilderFinal_at_two_six contextTwoSize S
      (encodedSource out) j.val Sf 6 (Or.inr rfl)
  · intro k hk
    have h5 : k ≠ (5 : StackN contextTwoSize) := by
      intro h
      have hv := congrArg Fin.val h
      simp [StackN, Nat.mod_eq_of_lt
        (by omega : 5 < 32 + contextTwoSize)] at hv
      omega
    have h22 : k ≠ (22 : StackN contextTwoSize) := by
      intro h
      have hv := congrArg Fin.val h
      simp [StackN, Nat.mod_eq_of_lt
        (by omega : 22 < 32 + contextTwoSize)] at hv
      omega
    have h0 : k ∉ ([0] : List (StackN contextTwoSize)) := by
      simp only [List.mem_singleton]
      intro h
      have hv := congrArg Fin.val h
      have hval0 : (0 : StackN contextTwoSize).val = 0 := by
        simp [StackN]
      rw [hval0] at hv
      omega
    rw [SourceClausePreservingBroadcast.other_preserved
      (5 : StackN contextTwoSize) 22 [0]
      (codeDGetterPacket (encodedSource out) j.val)
      (packetBuilderFinal contextTwoSize S (encodedSource out) j.val Sf)
      k h5 h22 h0]
    exact packetBuilderFinal_at_private contextTwoSize S
      (encodedSource out) j.val Sf k hk

#print axioms outer_packet_result_retains_coordinate

end CurrentAdditive.IndexedExecutableStepRecovery
