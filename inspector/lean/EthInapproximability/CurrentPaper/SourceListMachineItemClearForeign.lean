import EthInapproximability.CurrentPaper.SourceListMachineItemPrefix

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

theorem clearCount_foreign (source count accumulator : List Bool) :
    Function.update (foreign source count [] [] accumulator)
      (5 : Fin 8) [] = foreign source [] [] [] accumulator := by
  funext k
  fin_cases k <;> rfl

end EthInapproximability.CurrentPaper.SourceListMachineItem
