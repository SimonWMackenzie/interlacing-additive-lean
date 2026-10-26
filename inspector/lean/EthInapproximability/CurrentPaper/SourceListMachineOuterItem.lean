import EthInapproximability.CurrentPaper.SourceListMachineOuterCounter
import EthInapproximability.CurrentPaper.SourceListMachineItem
import EthInapproximability.CurrentPaper.SourceListMachineWork

/-! Physically embedded per-item callback in the binary-count outer loop. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding

variable (M : Machine)

noncomputable def itemFrame (S : Stack M → List Bool)
    (c : SourceListMachineItem.Config M) : Config M :=
  BitMachineStackEmbedding.cfg (itemStack M) S
    (itemLabel M) (itemControl M) (some (adminLabel M .afterItem)) c

theorem itemFrame_initial (S : Stack M → List Bool) (source accumulator : List Bool)
    (h : ∀ k : SourceListMachineItem.Stack M,
      (SourceListMachineItem.ready M source accumulator).stk k = S (itemStack M k)) :
    itemFrame M S (SourceListMachineItem.ready M source accumulator) =
      ⟨some (itemLabel M (SourceListMachineItem.fieldLabel M (.inl .scan))),
        itemControl M
          (SourceListMachineItem.fieldControl M SourceListMachineFields.initialControl), S⟩ := by
  unfold itemFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self (itemStack M) _ _ h]
  rfl

theorem item_embedded (S : Stack M → List Bool)
    (input output source accumulator : List Bool) (bound : Nat)
    (hM : M.OutputsWithin input output bound) :
    ∃ t ≤ SourceListMachineWork.itemCost M input output bound,
      run M t (itemFrame M S (SourceListMachineItem.ready M
        (EncodedCommunication.natField input.length ++ (input ++ source)) accumulator)) =
        itemFrame M S (SourceListMachineItem.success M source
          (output.reverse ++ accumulator)) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineItem.item_encoded M input output source accumulator
    bound hM
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs (itemStack M) S
    (itemLabel M) (itemControl M) (fun v => v.1.1.1)
    (by intro v; rfl) (some (adminLabel M .afterItem))
    (SourceListMachineItem.program M) (program M) (fun _ => rfl)
    (SourceListMachineItem.ready M
      (EncodedCommunication.natField input.length ++ (input ++ source)) accumulator) t
    (by change (SourceListMachineItem.run M t _).l = none; rw [he]; rfl)
  change run M u (itemFrame M S _) = itemFrame M S (SourceListMachineItem.run M t _) at hr
  rw [he] at hr
  exact ⟨u, hu.trans ht, hr⟩

theorem counter_preserves_item (S : Stack M → List Bool)
    (T : SourceListMachineCounter.Stack → List Bool)
    (k : SourceListMachineItem.Stack M) :
    BitMachineStackEmbedding.bank (counterStack M) S T (itemStack M k) =
      S (itemStack M k) := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨j,hj⟩
  fin_cases j <;> cases hj

theorem item_preserves_counter (S : Stack M → List Bool)
    (T : SourceListMachineItem.Stack M → List Bool)
    (k : SourceListMachineCounter.Stack) :
    BitMachineStackEmbedding.bank (itemStack M) S T (counterStack M k) =
      S (counterStack M k) := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨j,hj⟩
  fin_cases k <;> cases hj

theorem counter_preserves_final (S : Stack M → List Bool)
    (T : SourceListMachineCounter.Stack → List Bool) :
    BitMachineStackEmbedding.bank (counterStack M) S T (.inr 2) = S (.inr 2) := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨j,hj⟩
  fin_cases j <;> cases hj

theorem item_preserves_final (S : Stack M → List Bool)
    (T : SourceListMachineItem.Stack M → List Bool) :
    BitMachineStackEmbedding.bank (itemStack M) S T (.inr 2) = S (.inr 2) := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨j,hj⟩
  cases hj

theorem item_success_stacks (source accumulator : List Bool) :
    (SourceListMachineItem.success M source accumulator).stk =
      (SourceListMachineItem.ready M source accumulator).stk := rfl

theorem itemFrame_halted (S : Stack M → List Bool) (source accumulator : List Bool) :
    itemFrame M S (SourceListMachineItem.success M source accumulator) =
      ⟨some (adminLabel M .afterItem),
        itemControl M
          ((SourceListMachineFields.initialControl,M.initial),some true),
        BitMachineStackEmbedding.bank (itemStack M) S
          (SourceListMachineItem.success M source accumulator).stk⟩ := rfl

theorem afterCounter_positive (S : Stack M → List Bool) :
    advance (program M)
      ⟨some (adminLabel M .afterCounter),
        counterControl M (SourceListMachineCounter.doneControl true), S⟩ =
      ⟨some (itemLabel M (SourceListMachineItem.fieldLabel M (.inl .scan))),
        itemControl M
          (SourceListMachineItem.fieldControl M SourceListMachineFields.initialControl), S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]
  rfl

theorem afterItem_success (S : Stack M → List Bool) :
    advance (program M)
      ⟨some (adminLabel M .afterItem),
        itemControl M ((SourceListMachineFields.initialControl,M.initial),some true), S⟩ =
      ⟨some (counterLabel M (.inr .scan)),
        counterControl M SourceListMachineCounter.initialControl, S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]
  rfl

end EthInapproximability.CurrentPaper.SourceListMachineOuter
