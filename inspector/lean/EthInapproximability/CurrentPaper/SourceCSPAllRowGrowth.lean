import EthInapproximability.CurrentPaper.SourceCSPAllRowLoop
import EthInapproximability.CurrentPaper.SourceClauseRowPrefixPolynomial
import EthInapproximability.CurrentPaper.SourceCSPNextParserGrowth

/-! Source-exact per-row payload bounds for a uniform physical loop clock. -/

namespace EthInapproximability.CurrentPaper.SourceCSPAllRowClock

open SourceCSPAllRowLoop
open SourceClauseCallback.AllSlots
open SourceClauseCallbackRowPrefixPolynomial
open SourceClauseCallbackAllSlotPolynomial

noncomputable def typedRowBank {n m q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m) :
    SourceCSPRowQueryFrame.Stack q → List Bool
  | .inl (j, 1) => List.replicate ((rows r).1 j).val true
  | .inr 2 => true :: List.ofFn (rows r).2
  | _ => []

theorem typedRowBank_words_le {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (r : Fin m)
    (hn : n ≤ H) (ht : 1 + 2 ^ q ≤ H) :
    ∀ x, (typedRowBank rows r x).length ≤ H := by
  intro x
  cases x with
  | inl p =>
      rcases p with ⟨j, s⟩
      fin_cases s <;>
        simp [typedRowBank]
      exact (Nat.le_of_lt ((rows r).1 j).isLt).trans hn
  | inr s =>
      fin_cases s <;> simp [typedRowBank] <;> omega

theorem row_payload_bytes_le {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (r : Fin m)
    (hn : n ≤ H) (hm : m ≤ H) (ht : 1 + 2 ^ q ≤ H) :
    (EncodedCNF.clauseFields (rowClauses rows hq r)).length ≤
      (2 ^ q) * (slotByteCoefficient q * (H + 1)) := by
  let V := typedRowBank rows r
  have hV := typedRowBank_words_le rows r hn ht
  have hr : r.val ≤ H :=
    (Nat.le_of_lt r.isLt).trans hm
  have hqV : ∀ j : Fin q,
      V (.inl (j, 1)) = List.replicate ((rows r).1 j).val true := by
    intro j
    rfl
  have hsave := allSaved_length_le hq V n r.val H (rows r).2
    ([] : List Bool) hn hr hV
  rw [listSaved_ordered,
    TypedRowCorrespondence.listClauses_from_parsed_row rows r V hq hqV] at hsave
  simpa only [List.length_append, List.length_reverse,
    List.length_nil, Nat.add_zero, Nat.zero_add, rowClauses] using hsave

theorem row_clause_count_le {n m q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (r : Fin m) :
    (rowClauses rows hq r).length ≤
      (2 ^ q) * (3 * q + 5) := by
  let V := typedRowBank rows r
  have hqV : ∀ j : Fin q,
      V (.inl (j, 1)) = List.replicate ((rows r).1 j).val true := by
    intro j
    rfl
  have hc := allCount_length_le (rows r).2 ([] : List Bool)
  rw [SourceClauseCallback.AllSlotsCount.list_count_actual
    (SourceCSPCodec.fromRows n m 2 q rows).system hq r V (rows r).2
    (List.ofFn (fun k : Fin (2 ^ q) => k)) []
    (TypedRowCorrespondence.query_from_parsed_row rows r V hqV)
    (TypedRowCorrespondence.table_from_rows rows r)] at hc
  simpa only [List.length_append, List.length_replicate,
    List.length_nil, Nat.add_zero, Nat.zero_add, rowClauses] using hc

theorem clauseFields_append (xs ys : List EncodedCNF.Clause) :
    EncodedCNF.clauseFields (xs ++ ys) =
      EncodedCNF.clauseFields xs ++ EncodedCNF.clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, EncodedCNF.clauseFields, ih,
        List.append_assoc]

def rowByteIncrement (q H : Nat) : Nat :=
  (2 ^ q) * (slotByteCoefficient q * (H + 1))

def rowCountIncrement (q : Nat) : Nat :=
  (2 ^ q) * (3 * q + 5)

theorem suffix_payload_bytes_le {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (hn : n ≤ H) (hm : m ≤ H)
    (ht : 1 + 2 ^ q ≤ H)
    (r k : Nat) (h : r + 1 + k ≤ m) :
    (EncodedCNF.clauseFields
      (suffixClauses rows hq r k h)).length ≤
        k * rowByteIncrement q H := by
  induction k generalizing r with
  | zero => simp [suffixClauses, EncodedCNF.clauseFields]
  | succ k ih =>
      rw [suffixClauses_succ, clauseFields_append,
        List.length_append]
      have hhead := row_payload_bytes_le rows hq
        (⟨r + 1, by omega⟩ : Fin m) hn hm ht
      have htail := ih (r + 1) (by omega)
      change (EncodedCNF.clauseFields
        (rowClauses rows hq (⟨r + 1, by omega⟩ : Fin m))).length ≤
          rowByteIncrement q H at hhead
      simp only [Nat.succ_mul]
      omega

theorem suffix_clause_count_le {n m q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (r k : Nat) (h : r + 1 + k ≤ m) :
    (suffixClauses rows hq r k h).length ≤
      k * rowCountIncrement q := by
  induction k generalizing r with
  | zero => simp [suffixClauses]
  | succ k ih =>
      rw [suffixClauses_succ, List.length_append]
      have hhead := row_clause_count_le rows hq
        (⟨r + 1, by omega⟩ : Fin m)
      have htail := ih (r + 1) (by omega)
      change (rowClauses rows hq
        (⟨r + 1, by omega⟩ : Fin m)).length ≤
          rowCountIncrement q at hhead
      simp only [Nat.succ_mul]
      omega

theorem saved_after_prefix_le {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (hn : n ≤ H) (hm : m ≤ H)
    (ht : 1 + 2 ^ q ≤ H)
    (r k : Nat) (h : r + 1 + k ≤ m)
    (saved : List Bool) :
    ((EncodedCNF.clauseFields
      (suffixClauses rows hq r k h)).reverse ++ saved).length ≤
        saved.length + k * rowByteIncrement q H := by
  have hb := suffix_payload_bytes_le rows hq hn hm ht r k h
  simp only [List.length_append, List.length_reverse]
  omega

theorem count_after_prefix_le {n m q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (r k : Nat) (h : r + 1 + k ≤ m)
    (count : List Bool) :
    (List.replicate (suffixClauses rows hq r k h).length true ++
      count).length ≤ count.length + k * rowCountIncrement q := by
  have hc := suffix_clause_count_le rows hq r k h
  simp only [List.length_append, List.length_replicate]
  omega

/-- A single envelope for all physical row-loop banks. The parser term is
fresh on every row and is not iterated into its own input bound. -/
noncomputable def loopEnvelope (q H m : Nat) : Nat :=
  H + m * (rowByteIncrement q H + rowCountIncrement q) +
    SourceCSPNextParserGrowth.parseWordCoefficient q * (H + 1) ^ 2 + 1

theorem base_le_envelope (q H m : Nat) : H ≤ loopEnvelope q H m := by
  unfold loopEnvelope
  omega

theorem parser_le_envelope (q H m : Nat) :
    SourceCSPNextParserGrowth.parseWordCoefficient q * (H + 1) ^ 2 ≤
      loopEnvelope q H m := by
  unfold loopEnvelope
  omega

theorem saved_budget_le_envelope (q H m k : Nat)
    (saved : List Bool) (hsaved : saved.length ≤ H) (hk : k ≤ m) :
    saved.length + k * rowByteIncrement q H ≤
      loopEnvelope q H m := by
  unfold loopEnvelope
  have hmul := Nat.mul_le_mul_right (rowByteIncrement q H) hk
  rw [Nat.mul_add]
  omega

theorem count_budget_le_envelope (q H m k : Nat)
    (count : List Bool) (hcount : count.length ≤ H) (hk : k ≤ m) :
    count.length + k * rowCountIncrement q ≤
      loopEnvelope q H m := by
  unfold loopEnvelope
  have hmul := Nat.mul_le_mul_right (rowCountIncrement q) hk
  rw [Nat.mul_add]
  omega

noncomputable def envelopeCoefficient (q : Nat) : Nat :=
  1 + (2 ^ q) * slotByteCoefficient q + rowCountIncrement q +
    SourceCSPNextParserGrowth.parseWordCoefficient q

theorem loopEnvelope_le_quadratic (q H m : Nat) (hm : m ≤ H) :
    loopEnvelope q H m ≤ envelopeCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let A := (2 ^ q) * slotByteCoefficient q
  let C := rowCountIncrement q
  let P := SourceCSPNextParserGrowth.parseWordCoefficient q
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hmM : m ≤ M := by dsimp [M]; omega
  have hsq : M ≤ M ^ 2 := by nlinarith
  have hmul : m * (A * M + C) ≤ M * (A * M + C) :=
    Nat.mul_le_mul_right (A * M + C) hmM
  have hC : M * C ≤ C * M ^ 2 := by
    have hx := Nat.mul_le_mul_left C hsq
    nlinarith
  dsimp [loopEnvelope, envelopeCoefficient, rowByteIncrement]
  dsimp [M, A, C, P] at hM hmM hsq hmul hC
  nlinarith

theorem withRemaining_words_le {q H G k : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hS : ∀ x, (S x).length ≤ G) (hk : k ≤ H) (hHG : H ≤ G) :
    ∀ x, (withRemaining S k x).length ≤ G := by
  intro x
  by_cases hx : x = SourceCSPHeaderRowBridge.loopCount
  · subst x
    simp [withRemaining, List.length_replicate]
    omega
  · simp only [withRemaining, Function.update_of_ne hx]
    exact hS x

theorem saved_budget_step {n m q H G k : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (r : Fin m)
    (hn : n ≤ H) (hm : m ≤ H) (ht : 1 + 2 ^ q ≤ H)
    (saved : List Bool)
    (hbudget : saved.length + (k + 1) * rowByteIncrement q H ≤ G) :
    ((EncodedCNF.clauseFields (rowClauses rows hq r)).reverse ++
      saved).length + k * rowByteIncrement q H ≤ G := by
  have hb := row_payload_bytes_le rows hq r hn hm ht
  change (EncodedCNF.clauseFields (rowClauses rows hq r)).length ≤
    rowByteIncrement q H at hb
  simp only [List.length_append, List.length_reverse]
  simp only [Nat.succ_mul] at hbudget
  omega

theorem count_budget_step {n m q G k : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hq : 0 < q) (r : Fin m)
    (count : List Bool)
    (hbudget : count.length + (k + 1) * rowCountIncrement q ≤ G) :
    (List.replicate (rowClauses rows hq r).length true ++
      count).length + k * rowCountIncrement q ≤ G := by
  have hc := row_clause_count_le rows hq r
  change (rowClauses rows hq r).length ≤
    rowCountIncrement q at hc
  simp only [List.length_append, List.length_replicate]
  simp only [Nat.succ_mul] at hbudget
  omega

end EthInapproximability.CurrentPaper.SourceCSPAllRowClock
