import EthInapproximability.CurrentPaper.SourceListMachineOuterItem

/-! One fully charged positive binary-counter/list-item iteration. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding

variable (M : Machine)

def loopCfg (S : Stack M → List Bool) : Config M :=
  ⟨some (counterLabel M (.inr .scan)),
    counterControl M SourceListMachineCounter.initialControl, S⟩

structure LoopInvariant (S : Stack M → List Bool)
    (source q accumulator : List Bool) : Prop where
  item : ∀ k : SourceListMachineItem.Stack M,
    (SourceListMachineItem.ready M source accumulator).stk k = S (itemStack M k)
  count : S (.inr 0) = q
  temp : S (.inr 1) = []
  final : S (.inr 2) = []

theorem counter_bank_invariant (S : Stack M → List Bool)
    (source q q' accumulator : List Bool) (v : SourceListMachineCounter.Control)
    (h : LoopInvariant M S source q accumulator) :
    LoopInvariant M
      (BitMachineStackEmbedding.bank (counterStack M) S
        (SourceListMachineCounter.cfg none v q' []).stk)
      source q' accumulator := by
  constructor
  · intro k
    rw [counter_preserves_item M]
    exact h.item k
  · exact BitMachineStackEmbedding.bank_at (counterStack M) _ _ 0
  · exact BitMachineStackEmbedding.bank_at (counterStack M) _ _ 1
  · exact (counter_preserves_final M S _).trans h.final

theorem item_bank_invariant (S : Stack M → List Bool)
    (framed source q accumulator output : List Bool)
    (h : LoopInvariant M S framed q accumulator) :
    LoopInvariant M
      (BitMachineStackEmbedding.bank (itemStack M) S
        (SourceListMachineItem.success M source (output.reverse ++ accumulator)).stk)
      source q (output.reverse ++ accumulator) := by
  constructor
  · intro k
    rw [BitMachineStackEmbedding.bank_at]
    exact (congrArg (fun T : SourceListMachineItem.Stack M → List Bool => T k)
      (item_success_stacks M source (output.reverse ++ accumulator))).symm
  · exact (item_preserves_counter M S _ 0).trans h.count
  · exact (item_preserves_counter M S _ 1).trans h.temp
  · exact (item_preserves_final M S _).trans h.final

/-- One branch costs one binary-counter pass plus its own item-machine cost;
no operation scans the unread suffix or the already-emitted accumulator. -/
theorem positive_step (S : Stack M → List Bool)
    (input output source q q' accumulator : List Bool) (bound : Nat)
    (h : LoopInvariant M S
      (EncodedCommunication.natField input.length ++ (input ++ source)) q accumulator)
    (hq : ProtocolBinaryCounter.subOne q = some q')
    (hM : M.OutputsWithin input output bound) :
    ∃ T : Stack M → List Bool, ∃ t ≤ 4*q.length+7+
      SourceListMachineWork.itemCost M input output bound,
      LoopInvariant M T source q' (output.reverse ++ accumulator) ∧
      run M t (loopCfg M S) = loopCfg M T := by
  let framed := EncodedCommunication.natField input.length ++ (input ++ source)
  let T1 := BitMachineStackEmbedding.bank (counterStack M) S
    (SourceListMachineCounter.cfg none (SourceListMachineCounter.doneControl true) q' []).stk
  let T2 := BitMachineStackEmbedding.bank (itemStack M) T1
    (SourceListMachineItem.success M source (output.reverse ++ accumulator)).stk
  have h1 : LoopInvariant M T1 framed q' accumulator :=
    counter_bank_invariant M S framed q q' accumulator
      (SourceListMachineCounter.doneControl true) h
  have h2 : LoopInvariant M T2 source q' (output.reverse ++ accumulator) :=
    item_bank_invariant M T1 framed source q' accumulator output h1
  obtain ⟨a, ha, hra⟩ := counter_embedded M S q
  rw [counterFrame_initial M S q h.count h.temp] at hra
  simp only [hq] at hra
  rw [counterFrame_halted] at hra
  change run M a (loopCfg M S) =
    ⟨some (adminLabel M .afterCounter),
      counterControl M (SourceListMachineCounter.doneControl true), T1⟩ at hra
  have henter : advance (program M)
      ⟨some (adminLabel M .afterCounter),
        counterControl M (SourceListMachineCounter.doneControl true), T1⟩ =
      itemFrame M T1 (SourceListMachineItem.ready M framed accumulator) :=
    (afterCounter_positive M T1).trans
      (itemFrame_initial M T1 framed accumulator h1.item).symm
  obtain ⟨b, hb, hrb⟩ := item_embedded M T1 input output source accumulator bound hM
  change run M b (itemFrame M T1 (SourceListMachineItem.ready M framed accumulator)) =
    itemFrame M T1 (SourceListMachineItem.success M source
      (output.reverse ++ accumulator)) at hrb
  rw [itemFrame_halted] at hrb
  change run M b (itemFrame M T1 (SourceListMachineItem.ready M framed accumulator)) =
    ⟨some (adminLabel M .afterItem),
      itemControl M ((SourceListMachineFields.initialControl,M.initial),some true), T2⟩ at hrb
  have hexit := afterItem_success M T2
  have hfirst := (run_add M hra 1).trans (run_succ M henter 0)
  have hsecond := (run_add M hfirst b).trans hrb
  have hthird := (run_add M hsecond 1).trans (run_succ M hexit 0)
  exact ⟨T2, a+1+b+1, by omega, h2, by simpa only [loopCfg] using hthird⟩

end EthInapproximability.CurrentPaper.SourceListMachineOuter
