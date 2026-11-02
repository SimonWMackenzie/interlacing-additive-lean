import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalParsed

/-!
# Physical rejection of an out-of-range parsed source row

Canonical numeric fields and a full table do not suffice: every query must
be below the declared vertex count. Here the actual bounded-unary checker
finds a failure, and the corrected yield instruction halts before reset.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRangeReject

open Turing BitMachineEncoding SourceCSPRowLoopController

theorem range_bad_rejects (q H : Nat) (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (L : Nat) (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length)
    (hword : ∀ j : Fin q, (bank j).length ≤ L)
    (hcap : cap.length ≤ L)
    (hbad : ¬ ∀ j : Fin q,
      EncodedCommunication.bitsValue (bank j) ≤ cap.length) :
    ∃ t S v,
      t ≤ q * (2 * input.length + 4) + 2 * H + 3 +
        q * (100 * (L + 1) ^ 2) + 5 ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨none, (v, some false), S⟩ := by
  obtain ⟨ty, v, U, b, hty, hyield, hsource, hparser, hquery, hb⟩ :=
    SourceCSPRowLoopTotalParsed.parsed_row_yield q H input cap bank rest L E count
      hcount hparse htable hword hcap
  have hbfalse : b = false := by
    cases b with
    | false => rfl
    | true => exact False.elim (hbad (hb.mp rfl))
  let S : Stack q → List Bool := Sum.elim U (Function.update E 0 count)
  have htableS : S (.inl (.inr 2)) = true :: rest.take H := hparser
  have hqueryS : S (.inl (.inr 4)) = [false] := by
    simpa only [hbfalse] using hquery
  have hstep := SourceCSPRowLoopTotalController.yield_query_false q H S v
    (rest.take H) htableS hqueryS
  have hreject := SourceCSPRowLoopTotalController.reject_step q H S
    ((v, resetStart), some false)
  refine ⟨ty + 2, S, (v, resetStart), by omega, ?_⟩
  rw [show ty + 2 = 2 + ty by omega, Function.iterate_add_apply, hyield]
  change advance (SourceCSPRowLoopTotalController.program q H)
    (advance (SourceCSPRowLoopTotalController.program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H)) = _
  rw [hstep, hreject]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRangeReject
