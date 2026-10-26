import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalHaltCompare

/-!
# Physical rejection of a malformed or truncated source row

At a positive unary row count, any failure of the canonical query parser or
short truth table reaches `.yield` with a false parser marker. The corrected
controller tests that marker and halts with rejection before reset.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalReject

open Turing BitMachineEncoding SourceCSPRowLoopController

theorem parse_bad_rejects (q H : Nat) (input cap : List Bool)
    (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hbad : ¬ SourceCSPRowLoopTotalRowResult.ParseGood q H input) :
    ∃ t S v,
      t ≤ SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap + 3 ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨none, (v, some false), S⟩ := by
  obtain ⟨ty, v, U, b, hty, hyield, hparser, hquery⟩ :=
    SourceCSPRowLoopTotalYield.raw_row_yield q H input cap E count hcount
  let S : Stack q → List Bool := Sum.elim U (Function.update E 0 count)
  have hfail : (S (.inl (.inr 2))).head? ≠ some true := by
    change (U (.inr 2)).head? ≠ some true
    rw [hparser]
    intro he
    exact hbad ((SourceCSPRowLoopTotalRowResult.rowResult_good_iff q H input).mp he)
  have hstep := SourceCSPRowLoopTotalController.yield_parser_failure q H S v hfail
  have hreject := SourceCSPRowLoopTotalController.reject_step q H S
    ((v, resetStart), (S (.inl (.inr 2))).head?)
  refine ⟨ty + 2, (S), (v, resetStart), by omega, ?_⟩
  rw [show ty + 2 = 2 + ty by omega, Function.iterate_add_apply, hyield]
  change advance (SourceCSPRowLoopTotalController.program q H)
    (advance (SourceCSPRowLoopTotalController.program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H)) = _
  rw [hstep, hreject]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalReject
