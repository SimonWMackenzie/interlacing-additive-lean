import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalQuery

/-!
# Arbitrary successfully parsed row through the physical query checker

The row parser and range checker are one raw-sequence program on the shared
bank. The theorem retains both parser and range flags and the exact unread
suffix, so an enclosing controller can reject either failure before reset.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCombined

open Turing BitMachineEncoding SourceCSPRowQueryFrame

theorem combined_success {q H : Nat} (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (L : Nat)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length)
    (hword : ∀ j : Fin q, (bank j).length ≤ L)
    (hcap : cap.length ≤ L) :
    ∃ t v S b,
      t ≤ q * (2 * input.length + 4) + 2 * H + 3 +
        q * (100 * (L + 1) ^ 2) + 2 ∧
      ((advance (combinedProgram q H))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (.start 0 : SourceCSPRowController.Label q H)),
          ((none, none), (((none, none), (none, false)), none)),
          initial input cap⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPRowController.Label q H)
              (SourceCSPQueryBank.Label q))
            (SourceCSPRowController.Control × SourceCSPQueryBank.Control)) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inr 0) = rest.drop H ∧
      S (.inr 2) = true :: rest.take H ∧
      S (.inr 4) = [b] ∧
      (b = true ↔ ∀ j : Fin q,
        EncodedCommunication.bitsValue (bank j) ≤ cap.length) := by
  obtain ⟨tr, htr, hrunr⟩ :=
    SourceCSPRowLoopTotalRowSuccess.parser_success input cap bank rest hparse htable
  obtain ⟨tq, vq, Sq, b, htq, hrunq, hstatus, hsource, hparser, hb⟩ :=
    SourceCSPRowLoopTotalQuery.query_run_preserved bank input cap
      (rest.drop H) [] (true :: rest.take H) L hword hcap
  let Srow := parsed (initial input cap) bank (rest.drop H) [] (true :: rest.take H)
  have hr : ((advance (rowProgram (q := q) (H := H)))^[tr])
      (⟨some (.start 0), (none, none), initial input cap⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPRowController.Label q H)
          SourceCSPRowController.Control) = ⟨none, (none, none), Srow⟩ := by
    simpa only [rowRun, Srow] using hrunr
  have hq : ((advance (queryProgram (q := q)))^[tq])
      (⟨some (.start 0), (((none, none), (none, false)), none), Srow⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, vq, Sq⟩ := by
    simpa only [queryRun, Srow] using hrunq
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (rowProgram (q := q) (H := H)) (queryProgram (q := q))
    (.start 0 : SourceCSPRowController.Label q H)
    (.start 0 : SourceCSPQueryBank.Label q)
    ((none, none) : SourceCSPRowController.Control) (none, none)
    ((((none, none), (none, false)), none) : SourceCSPQueryBank.Control) vq
    (initial input cap) Srow Sq tr tq hr hq
  refine ⟨t, vq, Sq, b, by omega, ?_, hsource, hparser, hstatus, hb⟩
  simpa only [combinedProgram] using hrun

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCombined
