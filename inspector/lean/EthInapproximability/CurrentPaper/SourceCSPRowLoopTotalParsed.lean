import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalReject
import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCombined

/-!
# Exact parsed-row decision bank in the corrected loop

For an arbitrary successfully parsed canonical row prefix, the physical
controller exposes exact query/range status and unread suffix at `.yield`.
No typed CSP row or desired list is supplied to this operational theorem.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalParsed

open Turing BitMachineEncoding SourceCSPRowLoopController

theorem parsed_row_yield (q H : Nat) (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (L : Nat) (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length)
    (hword : ∀ j : Fin q, (bank j).length ≤ L)
    (hcap : cap.length ≤ L) :
    ∃ t v U b,
      t ≤ 1 + (q * (2 * input.length + 4) + 2 * H + 3 +
        q * (100 * (L + 1) ^ 2) + 2) ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨some (adminLabel .yield), queryControl v,
          Sum.elim U (Function.update E 0 count)⟩ ∧
      U (.inr 0) = rest.drop H ∧
      U (.inr 2) = true :: rest.take H ∧
      U (.inr 4) = [b] ∧
      (b = true ↔ ∀ j : Fin q,
        EncodedCommunication.bitsValue (bank j) ≤ cap.length) := by
  obtain ⟨t, v, U, b, ht, hr, hsource, hparser, hstatus, hb⟩ :=
    SourceCSPRowLoopTotalCombined.combined_success input cap bank rest L
      hparse htable hword hcap
  have hrun : ((advance (SourceCSPRowQueryFrame.combinedProgram q H))^[t])
      (⟨some (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H)), queryStart,
        SourceCSPRowQueryFrame.initial input cap⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (QueryLabel q H) QueryControl) =
        ⟨none, ((none, none), v), U⟩ := by
    simpa only [queryStart] using hr
  obtain ⟨u, hu, hquery⟩ := SourceCSPRowLoopTotalOne.query_lift q H
    (SourceCSPRowQueryFrame.initial input cap) U
    (Function.update E 0 count) ((none, none), v) t hrun
  have hcheck : advance (SourceCSPRowLoopTotalController.program q H)
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
      ⟨some (queryLabel (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H))),
        initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial input cap)
          (Function.update E 0 count)⟩ := by
    rw [SourceCSPRowLoopTotalController.check_positive q H _ count
      (by simpa only [Sum.elim_inr] using hcount)]
    simp only [SourceCSPRowLoopIteration.update_outer]
  refine ⟨1 + u, ((none, none), v), U, b, by omega, ?_,
    hsource, hparser, hstatus, hb⟩
  rw [show 1 + u = u + 1 by omega, Function.iterate_add_apply,
    Function.iterate_one, hcheck, hquery]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalParsed
