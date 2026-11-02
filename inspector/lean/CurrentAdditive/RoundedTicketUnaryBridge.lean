import CurrentAdditive.RoundedTicketUnary
import CurrentAdditive.RoundedMachineBridge
import Paper2.CappedTicketMachine

/-! Physical fixed-block rounded draw followed by the existing unary label codec. -/

namespace EthInapproximability.CurrentPaper.RoundedTicketUnary

open EthInapproximability.CurrentPaper.EncodedCommunication (bitsValue)

theorem physical_finCodec (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t c,
      t ≤ RoundedMachine.clock a.bits
          (Paper2.CappedTicketMachine.ticketWord bits) +
        (a + 1) *
          (4 * (RoundedMachine.outputWord a.bits
            (Paper2.CappedTicketMachine.ticketWord bits)).length + 5) + 1 ∧
      run t (start a.bits (Paper2.CappedTicketMachine.ticketWord bits)
        suffix a) = c ∧
      c.l = none ∧
      c.stk (.inr 2) =
        (Paper2.RecursiveLabelCodecScratch.finCodec a).encode
          (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
            (Paper2.CappedSampler.bitsTicketEquiv b bits)) ∧
      c.stk (.inl (.inr 1)) = suffix := by
  have hsource : bitsValue a.bits = a :=
    EncodedCommunication.bitsValue_bits a
  obtain ⟨t, c, ht, hr, hl, ho, hs⟩ := physical_unary a.bits
    (Paper2.CappedTicketMachine.ticketWord bits) suffix (by simpa [hsource] using ha)
  refine ⟨t, c, ?_, ?_, hl, ?_, hs⟩
  · simpa only [hsource] using ht
  · simpa only [hsource] using hr
  · rw [ho, RoundedMachine.output_matches_draw a b ha bits]
    rfl

#print axioms physical_finCodec

end EthInapproximability.CurrentPaper.RoundedTicketUnary
