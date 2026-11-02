import CurrentAdditive.RoundedLoadedDraw
import CurrentAdditive.RoundedCleanClock

namespace EthInapproximability.CurrentPaper.RoundedLoadedClock

noncomputable section

def coefficient : ℕ := UnaryBinaryEncoding.coefficient + 10 +
  4 * RoundedCleanClock.coefficient

theorem clock_quadratic (a b : ℕ) :
    RoundedLoadedDraw.clock a b ≤ coefficient * (a + b + 2) ^ 2 := by
  let Q := a + b + 2
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hQQ : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have hbits := UnaryBinaryEncoding.bits_length_le a
  have h1 : a + 1 ≤ Q := by dsimp [Q]; omega
  have h1sq : (a + 1) ^ 2 ≤ Q ^ 2 := by gcongr
  have h2 : a.bits.length + (List.replicate b false).length +
      EncodedCommunication.bitsValue a.bits + 2 ≤ 2 * Q := by
    simp only [List.length_replicate, EncodedCommunication.bitsValue_bits]
    dsimp [Q]
    omega
  have h2sq : (a.bits.length + (List.replicate b false).length +
      EncodedCommunication.bitsValue a.bits + 2) ^ 2 ≤ 4 * Q ^ 2 := by
    calc
      _ ≤ (2 * Q) ^ 2 := by gcongr
      _ = _ := by ring
  have hc := (RoundedCleanClock.clock_quadratic a.bits (List.replicate b false)).trans
    (Nat.mul_le_mul_left RoundedCleanClock.coefficient h2sq)
  have hp : 4 * a + 2 * b + 6 + (2 * a.bits.length + 3) ≤ 9 * Q ^ 2 := by
    dsimp [Q] at hQQ ⊢
    omega
  have hu := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient h1sq
  change RoundedPrepare.clock a b +
    RoundedCleanDraw.clock a.bits (List.replicate b false) + 1 ≤ coefficient * Q ^ 2
  have hprepare : RoundedPrepare.clock a b ≤
      (UnaryBinaryEncoding.coefficient + 9) * Q ^ 2 := by
    unfold RoundedPrepare.clock
    nlinarith
  calc
    _ ≤ (UnaryBinaryEncoding.coefficient + 9) * Q ^ 2 +
        RoundedCleanClock.coefficient * (4 * Q ^ 2) + Q ^ 2 := by omega
    _ = coefficient * Q ^ 2 := by unfold coefficient; ring

theorem physical_finCodec (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ coefficient * (a + b + 2) ^ 2,
      RoundedLoadedDraw.run t
        (RoundedLoadedDraw.start a b (Paper2.CappedTicketMachine.ticketWord bits ++ suffix)) =
        ⟨none, RoundedLoadedDraw.initial, RoundedLoadedDraw.finalBank a b
          (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) suffix
          ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
            (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
              (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  obtain ⟨t, ht, hr⟩ := RoundedLoadedDraw.physical_finCodec a b ha bits suffix
  have ht' : t ≤ RoundedLoadedDraw.clock a b := by
    simpa only [RoundedLoadedDraw.clock, RoundedCleanDraw.clock, RoundedCleanDraw.drawClock,
      Paper2.CappedTicketMachine.ticketWord_length, List.length_replicate] using ht
  exact ⟨t, ht'.trans (clock_quadratic a b), hr⟩

#print axioms clock_quadratic
#print axioms physical_finCodec

end
end EthInapproximability.CurrentPaper.RoundedLoadedClock
