import EthInapproximability.CurrentPaper.SourceListMachineItemClearBank
import EthInapproximability.CurrentPaper.SourceListMachineItemClearForeign

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

open Turing BitMachine BitMachineEncoding

theorem clearCount_foreign_bank (M : Machine)
    (source count accumulator : List Bool) :
    Function.update
      (Sum.elim (fun _ : Fin M.stackCount => [])
        (foreign source count [] [] accumulator))
      (.inr (5 : Fin 8)) [] =
    Sum.elim (fun _ : Fin M.stackCount => [])
      (foreign source [] [] [] accumulator) := by
  rw [Sum.update_elim_inr, clearCount_foreign]

end EthInapproximability.CurrentPaper.SourceListMachineItem
