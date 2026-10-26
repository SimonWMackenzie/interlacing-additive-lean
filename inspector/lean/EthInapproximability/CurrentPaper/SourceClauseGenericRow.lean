import EthInapproximability.CurrentPaper.SourceClauseGenericActual
import EthInapproximability.CurrentPaper.SourceClauseGenericAllSlotPolynomial

namespace EthInapproximability.CurrentPaper.SourceClauseGenericRow

open SourceBooleanEncoding SourceClauseRowSchedule
open SourceClauseGenericAllSlots SourceClauseGenericAllSlotsClock
open SourceClauseGenericAllSlotPolynomial
open SourceClauseCallback (Circuit rowQuery)
open scoped Classical

noncomputable def inputBits {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) : ℕ :=
  ∑ x : SourceClauseRowWriterTruthFrame.Stack q,
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count x).length

private theorem word_le_inputBits {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterTruthFrame.Stack q) :
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count x).length ≤
      inputBits row n r saved output count := by
  classical
  exact Finset.single_le_sum
    (f := fun y : SourceClauseRowWriterTruthFrame.Stack q =>
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count y).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

theorem input_limits {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    n ≤ inputBits row n r saved output count ∧
    r ≤ inputBits row n r saved output count ∧
    (∀ x, (row x).length ≤ inputBits row n r saved output count) ∧
    saved.length ≤ inputBits row n r saved output count ∧
    output.length ≤ inputBits row n r saved output count ∧
    count.length ≤ inputBits row n r saved output count := by
  let H := inputBits row n r saved output count
  constructor
  · simpa [H, SourceClauseRowWriterTruthFrame.initial,
      SourceClauseRowWriterBlank.vertex] using
      word_le_inputBits row n r saved output count
        (.inl SourceClauseRowWriterOperands.vertex)
  constructor
  · simpa [H, SourceClauseRowWriterTruthFrame.initial,
      SourceClauseRowWriterBlank.row_index] using
      word_le_inputBits row n r saved output count
        (.inl SourceClauseRowWriterOperands.rowIndex)
  constructor
  · intro x
    simpa [H, SourceClauseRowWriterTruthFrame.initial,
      SourceClauseRowWriterBlank.row_word,
      SourceClauseRowWriterCleanup.rowCell] using
      word_le_inputBits row n r saved output count
        (.inl (SourceClauseRowWriterCleanup.rowCell x))
  constructor
  · simpa [H, SourceClauseRowWriterTruthFrame.initial,
      SourceClauseRowWriterBlank.saved_word] using
      word_le_inputBits row n r saved output count
        (.inl (.inl (SourceClauseRowWriterCore.gateEmbedding
          (SourceClauseRowWriterCore.gateCore (.inr 0)))))
  constructor
  · simpa [H, SourceClauseRowWriterTruthFrame.initial,
      SourceClauseRowWriterBlank.output_word] using
      word_le_inputBits row n r saved output count
        (.inl (.inl (SourceClauseRowWriterCore.gateEmbedding
          (SourceClauseRowWriterCore.gateCore (.inr 1)))))
  · simpa [H, SourceClauseRowWriterTruthFrame.initial,
      SourceClauseRowWriterBlank.count_word] using
      word_le_inputBits row n r saved output count
        (.inl (.inl (SourceClauseRowWriterCore.gateEmbedding
          (SourceClauseRowWriterCore.gateCore (.inr 2)))))

theorem row_bounded_polynomial {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hunary : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (hquery : ∀ j : Fin q, rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (a ^ q),
      table k = P.accept r (tuple a q k))
    (saved output count : List Bool) :
    Circuit.BoundedRun (allCircuit (a := a) hq)
      (allCoefficient a q * (inputBits row n r.val saved output count + 1) ^ 2)
      (SourceClauseRowWriterTruthFrame.initial row n r.val saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        ((EncodedCNF.clauseFields
          ((List.ofFn fun k : Fin (a ^ q) =>
            SourceGenericOrder.rowChain P hq r k).flatten)).reverse ++ saved)
        output
        (listCount table (List.ofFn (fun k : Fin (a ^ q) => k)) count)) := by
  let H := inputBits row n r.val saved output count
  obtain ⟨hn, hr, hwords, hs, ho, hc⟩ :=
    input_limits row n r.val saved output count
  have hclock := allCost_le_quadratic hq row n r.val H table
    saved output count hn hr hwords hs ho hc hunary
  obtain ⟨t, ht, hrun⟩ := SourceClauseGenericActual.all_bounded_actual
    P hq r row table hrow hunary hquery haccept saved output count
  exact ⟨t, ht.trans hclock, hrun⟩

#print axioms row_bounded_polynomial

end EthInapproximability.CurrentPaper.SourceClauseGenericRow
