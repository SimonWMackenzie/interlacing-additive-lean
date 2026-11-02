import CurrentAdditive.RoundedMachine
import CurrentAdditive.RoundedDraw
import Paper2.CappedTicketMachine

/-! The private physical/finite-law join for one fixed-bit rounded draw. -/

namespace EthInapproximability.CurrentPaper.RoundedMachine

open EthInapproximability.CurrentPaper.EncodedCommunication (bitsValue)

theorem output_matches_draw (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) :
    bitsValue (outputWord a.bits (Paper2.CappedTicketMachine.ticketWord bits)) =
      (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
        (Paper2.CappedSampler.bitsTicketEquiv b bits)).val := by
  rw [output_value, EncodedCommunication.bitsValue_bits,
    Paper2.CappedTicketMachine.bitsValue_ofFn]
  simp only [Paper2.CappedTicketMachine.ticketWord_length]
  rfl

theorem physical_ticket (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ clock a.bits (Paper2.CappedTicketMachine.ticketWord bits),
      run t (cfg (some .load) initial (mulStart a.bits [])
        (List.replicate b true)
        (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) []) =
        cfg none initial
          (productBank a.bits (outputWord a.bits
            (Paper2.CappedTicketMachine.ticketWord bits))) [] suffix [] ∧
      bitsValue (outputWord a.bits (Paper2.CappedTicketMachine.ticketWord bits)) =
        (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
          (Paper2.CappedSampler.bitsTicketEquiv b bits)).val := by
  obtain ⟨t, ht, hr⟩ := physical_run a.bits
    (Paper2.CappedTicketMachine.ticketWord bits) suffix
  refine ⟨t, ht, ?_, output_matches_draw a b ha bits⟩
  simpa only [Paper2.CappedTicketMachine.ticketWord_length] using hr

#print axioms output_matches_draw
#print axioms physical_ticket
#print axioms physical_run
#print axioms output_value
#print axioms output_legal
#print axioms clock_quadratic

end EthInapproximability.CurrentPaper.RoundedMachine
