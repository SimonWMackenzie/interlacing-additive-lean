import EthInapproximability.CurrentPaper.SourceClauseAllSlots
import EthInapproximability.CurrentPaper.SourceCSPCodec

/-! An arbitrary physically parsed row agrees with its source CSP row. -/

namespace EthInapproximability.CurrentPaper.TypedRowCorrespondence

open Turing BitMachineEncoding
open SourceBooleanEncoding SourceClauseRowSchedule

theorem query_from_parsed_row {n m q : ℕ}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hquery : ∀ j : Fin q,
      row (.inl (j, 1)) = List.replicate ((rows r).1 j).val true) :
    ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j =
        ((SourceCSPCodec.fromRows n m 2 q rows).system.query r j).val := by
  intro j
  simp [SourceClauseCallback.rowQuery, SourceCSPCodec.fromRows,
    hquery j]

theorem truth_from_parsed_row {n m q : ℕ}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (htruth : row (.inr 2) = true :: List.ofFn (rows r).2) :
    row (.inr 2) = true :: List.ofFn (fun k : Fin (2 ^ q) =>
      (SourceCSPCodec.fromRows n m 2 q rows).system.accept r
        (tuple 2 q k)) := by
  rw [htruth]
  congr 1
  apply congrArg List.ofFn
  funext k
  simp [SourceCSPCodec.fromRows, tuple]

theorem table_from_rows {n m q : ℕ}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m) :
    ∀ k : Fin (2 ^ q),
      (rows r).2 k =
        (SourceCSPCodec.fromRows n m 2 q rows).system.accept r
          (tuple 2 q k) := by
  intro k
  simp [SourceCSPCodec.fromRows, tuple]

theorem unary_from_parsed_row {n m q : ℕ}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hquery : ∀ j : Fin q,
      row (.inl (j, 1)) = List.replicate ((rows r).1 j).val true) :
    ∀ j : Fin q,
      row (.inl (j, 1)) =
        List.replicate (row (.inl (j, 1))).length true := by
  intro j
  rw [hquery j]
  simp

/-- Every slot in a typed parsed row is the actual source-indexed translated
tuple block, in ascending slot order. -/
theorem listClauses_from_parsed_row {n m q : ℕ}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hq : 0 < q)
    (hquery : ∀ j : Fin q,
      row (.inl (j, 1)) = List.replicate ((rows r).1 j).val true)
    (ks : List (Fin (2 ^ q))) :
    SourceClauseCallback.AllSlots.listClauses hq row n r.val (rows r).2 ks =
      SourceClauseCallback.AllSlots.actualListClauses
        (SourceCSPCodec.fromRows n m 2 q rows).system hq r ks := by
  exact SourceClauseCallback.AllSlots.listClauses_actual
    _ hq r row (rows r).2 ks
    (query_from_parsed_row rows r row hquery)
    (table_from_rows rows r)

/-- The existing charged all-slot circuit for any parsed row, with its
source CSP correspondence derived from the typed decoded rows. -/
theorem all_run_from_parsed_row {n m q : ℕ}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hq : 0 < q)
    (hquery : ∀ j : Fin q,
      row (.inl (j, 1)) = List.replicate ((rows r).1 j).val true)
    (htruth : row (.inr 2) = true :: List.ofFn (rows r).2)
    (saved output count : List Bool) :
    SourceClauseCallback.Circuit.Run
      (SourceClauseCallback.AllSlots.allCircuit hq)
      (SourceClauseRowWriterTruthFrame.initial row n r.val saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        ((EncodedCNF.clauseFields
          (SourceClauseCallback.AllSlots.actualListClauses
            (SourceCSPCodec.fromRows n m 2 q rows).system hq r
            (List.ofFn (fun k : Fin (2 ^ q) => k)))).reverse ++ saved)
        output
        (SourceClauseCallback.AllSlots.listCount (rows r).2
          (List.ofFn (fun k : Fin (2 ^ q) => k)) count)) := by
  exact SourceClauseCallback.AllSlots.all_run_actual
    _ hq r row (rows r).2 htruth
    (unary_from_parsed_row rows r row hquery)
    (query_from_parsed_row rows r row hquery)
    (table_from_rows rows r) saved output count


end EthInapproximability.CurrentPaper.TypedRowCorrespondence
