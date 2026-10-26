import EthInapproximability.CurrentPaper.SourceListMachineItemPrefix

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

open Turing BitMachine BitMachineEncoding

theorem done_step (M : Machine)
    (v : SourceListMachineFields.Control × Fin M.controlCount)
    (S : Stack M → List Bool) :
    advance (program M)
      (⟨some (outer M .done), (v, none), S⟩ : Config M) =
    ⟨none, ((SourceListMachineFields.initialControl, M.initial), some true), S⟩ := rfl

end EthInapproximability.CurrentPaper.SourceListMachineItem
