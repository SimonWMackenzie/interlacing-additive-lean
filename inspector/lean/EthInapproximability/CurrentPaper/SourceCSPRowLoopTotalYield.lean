import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalOne
import EthInapproximability.CurrentPaper.SourceCSPRowLoopIteration

/-!
# Every arbitrary row reaches the corrected controller's decision point

The physical unary counter is popped once, then the all-input parser/query
sequence runs on the same shared bank. At `.yield` the parser marker and
range flag are both still present for the corrected instruction to inspect.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalYield

open Turing BitMachineEncoding SourceCSPRowLoopController

theorem raw_row_yield (q H : Nat) (input cap : List Bool)
    (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count) :
    ∃ t v U b,
      t ≤ 1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨some (adminLabel .yield), queryControl v,
          Sum.elim U (Function.update E 0 count)⟩ ∧
      U (.inr 2) = SourceCSPRowController.rowResult q H input ∧
      U (.inr 4) = [b] := by
  obtain ⟨t, v, U, b, ht, hr, hmarker, hstatus⟩ :=
    SourceCSPRowLoopTotalCombinedAll.combined_total q H input cap
  have hrun : ((advance (SourceCSPRowQueryFrame.combinedProgram q H))^[t])
      (⟨some (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H)), queryStart,
        SourceCSPRowQueryFrame.initial input cap⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (QueryLabel q H) QueryControl) = ⟨none, ((none, none), v), U⟩ := by
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
    rw [SourceCSPRowLoopTotalController.other_step q H (adminLabel .check)
      (by simp [adminLabel]) _ rfl]
    rw [check_positive q H _ count (by simpa only [Sum.elim_inr] using hcount)]
    simp only [SourceCSPRowLoopIteration.update_outer]
  refine ⟨1 + u, ((none, none), v), U, b, by omega, ?_, hmarker, hstatus⟩
  rw [show 1 + u = u + 1 by omega, Function.iterate_add_apply,
    Function.iterate_one, hcheck, hquery]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalYield
