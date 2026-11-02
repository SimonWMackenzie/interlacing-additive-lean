import EthInapproximability.CurrentPaper.SourceListMachineItemDone
import EthInapproximability.CurrentPaper.SourceListMachineItemClearGeneric

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

open Turing BitMachine BitMachineEncoding

theorem clearCount_bank (M : Machine)
    (v : SourceListMachineFields.Control × Fin M.controlCount)
    (S : Stack M → List Bool) :
    ((advance (program M))^[(S (.inr (5 : Fin 8))).length + 2])
      (⟨some (outer M .clearCount), (v, none), S⟩ : Config M) =
    ⟨none, ((SourceListMachineFields.initialControl, M.initial), some true),
      Function.update S (.inr (5 : Fin 8)) []⟩ :=
  SourceListMachineItemClearGeneric.clear_then_halt
    (program M) (.inr (5 : Fin 8))
    (outer M .clearCount) (outer M .done) (clearCount_program M)
    (fun _ => (SourceListMachineFields.initialControl, M.initial))
    (done_step M) v S

end EthInapproximability.CurrentPaper.SourceListMachineItem
