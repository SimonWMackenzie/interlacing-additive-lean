import EthInapproximability.CurrentPaper.SourceListMachineItemClearProjection

/-!
# Charged count-stack cleanup for a source-list item

The loop pops the unary count one bit per transition and tests the empty
stack once more. One final `.done` instruction resets control and halts.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

open Turing TM2.Stmt BitMachine BitMachineEncoding
open SourceListMachineFields hiding cfg run run_add program outer

variable (M : Machine)

theorem clearCount_run (source count accumulator : List Bool)
    (v : SourceListMachineFields.Control × Fin M.controlCount) :
    run M (count.length + 2)
      (cfg M (some (outer M .clearCount)) (v, none) (fun _ => [])
        (foreign source count [] [] accumulator)) =
      cfg M none ((SourceListMachineFields.initialControl, M.initial), some true)
        (fun _ => []) (foreign source [] [] [] accumulator) := by
  let bank : Stack M → List Bool :=
    Sum.elim (fun _ : Fin M.stackCount => [])
      (foreign source count [] [] accumulator)
  have hsource : bank (.inr (5 : Fin 8)) = count := rfl
  have h := clearCount_bank M v bank
  rw [hsource, clearCount_foreign_bank M source count accumulator] at h
  change ((advance (program M))^[count.length + 2])
    (⟨some (outer M .clearCount), (v, none), bank⟩ : Config M) =
    ⟨none, ((SourceListMachineFields.initialControl, M.initial), some true),
      Sum.elim (fun _ : Fin M.stackCount => [])
        (foreign source [] [] [] accumulator)⟩
  exact h

end EthInapproximability.CurrentPaper.SourceListMachineItem
