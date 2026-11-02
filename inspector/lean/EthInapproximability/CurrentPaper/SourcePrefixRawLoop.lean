import EthInapproximability.CurrentPaper.SourcePrefixRawVertex

namespace EthInapproximability.CurrentPaper.SourcePrefixRawLoop

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

noncomputable def program (q : Nat) := fun l =>
  stackStmt (prefixEmbedding (q := q)) (PrefixLoopCallback.program q l)

theorem framed_loop (q n : Nat) (before : Stack q → List Bool)
    (hprefix : ∀ k : PrefixLoopMachine.Stack,
      before (prefixEmbedding k) =
        PrefixLoopMachine.blank n 0 [] [] [] [] k) :
    ∃ t S, t ≤ PrefixLoopPolynomial.polynomialClock n q [] [] [] ∧
      ((advance (program q))^[t])
        (⟨some (.inr .copyScan), (PrefixLoopCallback.initial, none), before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, (PrefixLoopCallback.initial, none), S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (entryEmbedding k) = before (entryEmbedding k)) ∧
      (∀ k : SourceCSPPositiveHeader.Stack,
        S (headerEmbedding k) = before (headerEmbedding k)) ∧
      (∀ k : PrefixLoopMachine.Stack,
        S (prefixEmbedding k) =
          PrefixLoopMachine.blank n n
            ((PrefixLoopIteration.prefixFields n q n).reverse)
            [] (List.replicate (8 * n) true) [] k) ∧
      S scratch = before scratch := by
  obtain ⟨t, ht, hr⟩ := PrefixLoopPolynomial.run_polynomial n q [] [] []
  let S := bank (prefixEmbedding (q := q)) before
    (PrefixLoopMachine.blank n n
      ((PrefixLoopIteration.prefixFields n q n).reverse)
      [] (List.replicate (8 * n) true) [])
  have hrun := BitMachineStackRun.run (prefixEmbedding (q := q)) before
    (PrefixLoopCallback.program q)
    (⟨some (.inr .copyScan), (PrefixLoopCallback.initial, none),
      PrefixLoopMachine.blank n 0 [] [] [] []⟩ :
      PrefixLoopMachine.Config _ _) t
  rw [hr] at hrun
  have hstart : bank (prefixEmbedding (q := q)) before
      (PrefixLoopMachine.blank n 0 [] [] [] []) = before := by
    apply bank_eq_self
    intro k
    exact (hprefix k).symm
  refine ⟨t, S, ht, ?_, ?_, ?_, ?_, ?_⟩
  · change ((advance (program q))^[t])
        (⟨some (.inr .copyScan),
          (PrefixLoopCallback.initial, none),
          bank (prefixEmbedding (q := q)) before
            (PrefixLoopMachine.blank n 0 [] [] [] [])⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, (PrefixLoopCallback.initial, none),
          bank (prefixEmbedding (q := q)) before
            (PrefixLoopMachine.blank n n
              ((PrefixLoopIteration.prefixFields n q n).reverse ++ [])
              [] (List.replicate (8 * n) true ++ []) [])⟩ at hrun
    rw [hstart] at hrun
    simpa only [List.append_nil, S] using hrun
  · intro k
    change bank (prefixEmbedding (q := q)) before _
      (entryEmbedding k) = _
    rw [bank_outside]
    rintro ⟨j, hj⟩
    cases hj
  · intro k
    change bank (prefixEmbedding (q := q)) before _
      (headerEmbedding k) = _
    rw [bank_outside]
    rintro ⟨j, hj⟩
    cases hj
  · intro k
    change bank (prefixEmbedding (q := q)) before _
      (prefixEmbedding k) = _
    rw [bank_at]
  · change bank (prefixEmbedding (q := q)) before _ scratch = _
    rw [bank_outside]
    rintro ⟨j, hj⟩
    cases hj

end EthInapproximability.CurrentPaper.SourcePrefixRawLoop
