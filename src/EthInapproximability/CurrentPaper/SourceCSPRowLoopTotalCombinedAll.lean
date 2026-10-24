import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRawQuery
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# All-input physical row parsing and range checking

The parser and range checker halt on every row suffix. The query-word size
bound is derived from the actual parser run by finite-program stack growth;
it is not assumed as an input or supplied intermediate bank.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCombinedAll

open Turing BitMachineEncoding SourceCSPRowQueryFrame

def parserBound (q H : Nat) (input : List Bool) : Nat :=
  q * (2 * input.length + 4) + 2 * H + 3

def wordBound (q H : Nat) (input cap : List Bool) : Nat :=
  cap.length +
    BitMachineStackGrowth.perStep (rowProgram (q := q) (H := H)) *
      parserBound q H input

def totalBound (q H : Nat) (input cap : List Bool) : Nat :=
  parserBound q H input +
    q * (100 * (wordBound q H input cap + 1) ^ 2) + 2

theorem combined_total (q H : Nat) (input cap : List Bool) :
    ∃ t v S b,
      t ≤ totalBound q H input cap ∧
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
      S (.inr 2) = SourceCSPRowController.rowResult q H input ∧
      S (.inr 4) = [b] := by
  obtain ⟨tr, vr, Sr, htr, hrunr, hmarker, hcap, hstatus, hwork⟩ :=
    SourceCSPRowLoopTotalRow.parser_total (q := q) (H := H) input cap
  let P := parserBound q H input
  let L := wordBound q H input cap
  have htime : tr ≤ P := htr
  have hword : ∀ j : Fin q, (Sr (.inl (j, 0))).length ≤ L := by
    intro j
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
    rw [hrunr] at hg
    simp only [initial, Sum.elim_inl, List.length_nil, Nat.zero_add] at hg
    dsimp only [L, wordBound]
    exact le_trans hg (by nlinarith [htime])
  have hcapLength : cap.length ≤ L := by
    dsimp only [L, wordBound]
    omega
  obtain ⟨tq, vq, Sq, b, htq, hrunq, hqstatus, hsource, hout, hb⟩ :=
    SourceCSPRowLoopTotalRawQuery.query_total Sr cap L hcap hstatus hwork
      hword hcapLength
  have hr : ((advance (rowProgram (q := q) (H := H)))^[tr])
      (⟨some (.start 0), (none, none), initial input cap⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPRowController.Label q H)
          SourceCSPRowController.Control) = ⟨none, vr, Sr⟩ := by
    simpa only [rowRun] using hrunr
  have hq : ((advance (queryProgram (q := q)))^[tq])
      (⟨some (.start 0), (((none, none), (none, false)), none), Sr⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, vq, Sq⟩ := by
    simpa only [queryRun] using hrunq
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (rowProgram (q := q) (H := H)) (queryProgram (q := q))
    (.start 0 : SourceCSPRowController.Label q H)
    (.start 0 : SourceCSPQueryBank.Label q)
    ((none, none) : SourceCSPRowController.Control) vr
    ((((none, none), (none, false)), none) : SourceCSPQueryBank.Control) vq
    (initial input cap) Sr Sq tr tq hr hq
  refine ⟨t, vq, Sq, b, ?_, ?_, ?_, hqstatus⟩
  · dsimp only [totalBound, P, L] at *
    omega
  · simpa only [combinedProgram] using hrun
  · exact hout.trans hmarker

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCombinedAll
