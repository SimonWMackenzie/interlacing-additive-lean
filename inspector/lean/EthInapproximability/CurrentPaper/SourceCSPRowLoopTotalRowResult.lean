import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalYield

/-!
# Exact all-input parser success flag

The literal leading parser bit is true exactly when all canonical numeric
query fields parse and the fixed-size truth table is present.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRowResult

def ParseGood (q H : Nat) (input : List Bool) : Prop :=
  ∃ bank rest,
    SourceCSPRowController.readQueriesFrom (q := q) 0 input
      (fun _ => []) = some (bank, rest) ∧ H ≤ rest.length

theorem rowResult_good_iff (q H : Nat) (input : List Bool) :
    (SourceCSPRowController.rowResult q H input).head? = some true ↔
      ParseGood q H input := by
  unfold SourceCSPRowController.rowResult ParseGood
  cases hp : SourceCSPRowController.readQueriesFrom (q := q) 0 input
      (fun _ => []) with
  | none => simp [hp]
  | some pair =>
      obtain ⟨bank, rest⟩ := pair
      by_cases hlen : H ≤ rest.length
      · simp [hp, SourceCSPRowMachine.result, hlen]
      · simp [hp, SourceCSPRowMachine.result, hlen]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRowResult
