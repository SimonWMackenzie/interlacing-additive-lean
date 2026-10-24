import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! A bank-agnostic pop-loop followed by one terminal control transition. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineItemClearGeneric

open Turing BitMachineEncoding

theorem clear_then_halt {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source : K) (again done : L)
    (hp : P again = BitMachineClearBank.clearStep source again done)
    (reset : V → V)
    (hdone : ∀ (v : V) (S : K → List Bool),
      advance P (⟨some done, (v, none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) L (V × Option Bool)) =
      ⟨none, (reset v, some true), S⟩)
    (v : V) (S : K → List Bool) :
    ((advance P)^[(S source).length + 2])
      (⟨some again, (v, none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) L (V × Option Bool)) =
      ⟨none, (reset v, some true), Function.update S source []⟩ := by
  have hc := BitMachineClearBank.clear_one_run P source again done hp v S
  rw [show (S source).length + 2 = 1 + ((S source).length + 1) by omega,
    Function.iterate_add_apply, hc]
  exact hdone v (Function.update S source [])

end EthInapproximability.CurrentPaper.SourceListMachineItemClearGeneric
