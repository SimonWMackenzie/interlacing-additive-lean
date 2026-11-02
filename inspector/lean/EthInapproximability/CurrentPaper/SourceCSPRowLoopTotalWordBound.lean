import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalNext

/-!
# Derived word-size bound for a successful arbitrary row parse

The numeric query words used by the range checker are written by the
physical parser. Their lengths are bounded from that actual run and the
parser's input length, not supplied as a complexity premise.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalWordBound

open Turing BitMachineEncoding SourceCSPRowQueryFrame

theorem parsed_words_bounded {q H : Nat} (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length) :
    (∀ j : Fin q, (bank j).length ≤
      SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap) ∧
    cap.length ≤ SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap := by
  obtain ⟨tr, htr, hrun⟩ :=
    SourceCSPRowLoopTotalRowSuccess.parser_success input cap bank rest
      hparse htable
  constructor
  · intro j
    have hg := BitMachineStackGrowth.run_growth
      (rowProgram (q := q) (H := H))
      (⟨some (.start 0), (none, none), initial input cap⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPRowController.Label q H)
          SourceCSPRowController.Control) tr (.inl (j, 0))
    change ((rowRun tr
      (⟨some (.start 0), (none, none), initial input cap⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPRowController.Label q H)
          SourceCSPRowController.Control)).stk (.inl (j, 0))).length ≤ _ at hg
    rw [hrun] at hg
    change (parsed (initial input cap) bank (rest.drop H) []
      (true :: rest.take H) (.inl (j, 0))).length ≤ _ at hg
    rw [parsed_query] at hg
    simp only [initial, Sum.elim_inl, List.length_nil, Nat.zero_add] at hg
    dsimp only [SourceCSPRowLoopTotalCombinedAll.wordBound]
    have htime : tr ≤ SourceCSPRowLoopTotalCombinedAll.parserBound q H input := htr
    exact le_trans hg (by nlinarith [htime])
  · unfold SourceCSPRowLoopTotalCombinedAll.wordBound
    omega

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalWordBound
