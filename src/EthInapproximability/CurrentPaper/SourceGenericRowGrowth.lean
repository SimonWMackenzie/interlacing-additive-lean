import EthInapproximability.CurrentPaper.SourceGenericAllRowLoop
import EthInapproximability.CurrentPaper.SourceClauseGenericAllSlotPolynomial
import EthInapproximability.CurrentPaper.SourceClauseGenericCount
import EthInapproximability.CurrentPaper.SourceGenericNextParserGrowth

/-! Source-exact per-row payload bounds for a uniform physical loop clock. -/

namespace EthInapproximability.CurrentPaper.SourceGenericAllRowClock

open SourceGenericAllRowLoop
open SourceClauseGenericAllSlots SourceClauseGenericAllSlotPolynomial
open SourceClauseGenericCount SourceBooleanEncoding

noncomputable def typedRowBank {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q) (r : Fin m) :
    SourceCSPRowQueryFrame.Stack q → List Bool
  | .inl (j, 1) => List.replicate ((rows r).1 j).val true
  | .inr 2 => true :: List.ofFn (rows r).2
  | _ => []

theorem typedRowBank_words_le {n m a q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q) (r : Fin m)
    (hn : n ≤ H) (ht : 1 + a ^ q ≤ H) :
    ∀ x, (typedRowBank rows r x).length ≤ H := by
  intro x
  cases x with
  | inl p =>
      rcases p with ⟨j, s⟩
      fin_cases s <;>
        simp [typedRowBank]
      exact (Nat.le_of_lt ((rows r).1 j).isLt).trans hn
  | inr s =>
      fin_cases s <;> simp [typedRowBank]
      omega

theorem clauseFields_append (xs ys : List EncodedCNF.Clause) :
    EncodedCNF.clauseFields (xs ++ ys) =
      EncodedCNF.clauseFields xs ++ EncodedCNF.clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, EncodedCNF.clauseFields, ih,
        List.append_assoc]

theorem row_payload_bytes_le {n m a q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r : Fin m)
    (hn : n ≤ H) (hm : m ≤ H) (ht : 1 + a ^ q ≤ H) :
    (EncodedCNF.clauseFields (rowClauses rows hq r)).length ≤
      (a ^ q) * (slotByteCoefficient a q * (H + 1)) := by
  let V := typedRowBank rows r
  have hV := typedRowBank_words_le rows r hn ht
  have hr : r.val ≤ H := (Nat.le_of_lt r.isLt).trans hm
  have hqV : ∀ j : Fin q,
      SourceClauseCallback.rowQuery V j =
        ((SourceCSPCodec.fromRows n m a q rows).system.query r j).val := by
    intro j
    simp [SourceClauseCallback.rowQuery, V, typedRowBank,
      SourceCSPCodec.fromRows]
  have haV : ∀ k : Fin (a ^ q), (rows r).2 k =
      (SourceCSPCodec.fromRows n m a q rows).system.accept r
        (SourceClauseRowSchedule.tuple a q k) := by
    intro k
    simp [SourceCSPCodec.fromRows, SourceClauseRowSchedule.tuple]
  have hslot : ∀ k : Fin (a ^ q),
      (EncodedCNF.clauseFields
        (SourceGenericOrder.rowChain
          (SourceCSPCodec.fromRows n m a q rows).system hq r k)).length ≤
        slotByteCoefficient a q * (H + 1) := by
    intro k
    rw [← SourceClauseGenericActual.slot_clause_actual
      (SourceCSPCodec.fromRows n m a q rows).system hq r V (rows r).2
      hqV haV k]
    exact slot_bytes_le hq V n r.val H k ((rows r).2 k) hn hr hV
  have hlist : ∀ (cs : List (List EncodedCNF.Clause)),
      (∀ c ∈ cs, (EncodedCNF.clauseFields c).length ≤
        slotByteCoefficient a q * (H + 1)) →
      (EncodedCNF.clauseFields cs.flatten).length ≤
        cs.length * (slotByteCoefficient a q * (H + 1)) := by
    intro cs hcs
    induction cs with
    | nil => simp [EncodedCNF.clauseFields]
    | cons c cs ih =>
        simp only [List.flatten_cons, clauseFields_append,
          List.length_append, List.length_cons, Nat.succ_mul]
        have hc : (EncodedCNF.clauseFields c).length ≤
            slotByteCoefficient a q * (H + 1) :=
          hcs c (List.mem_cons_self)
        have hcs' : ∀ d ∈ cs, (EncodedCNF.clauseFields d).length ≤
            slotByteCoefficient a q * (H + 1) := by
          intro d hd
          exact hcs d (List.mem_cons_of_mem c hd)
        have ht := ih hcs'
        omega
  simpa only [rowClauses,
    List.length_ofFn] using
      hlist (List.ofFn fun k : Fin (a ^ q) =>
        SourceGenericOrder.rowChain
          (SourceCSPCodec.fromRows n m a q rows).system hq r k)
        (by
          intro c hc
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
          exact hslot k)

theorem row_clause_count_le {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r : Fin m) :
    (rowClauses rows hq r).length ≤
      (a ^ q) * (3 * q + 5) := by
  have hslot : ∀ k : Fin (a ^ q),
      (SourceGenericOrder.rowChain
        (SourceCSPCodec.fromRows n m a q rows).system hq r k).length ≤
      3 * q + 5 := by
    intro k
    let V := typedRowBank rows r
    have hqV : ∀ j : Fin q,
        SourceClauseCallback.rowQuery V j =
          ((SourceCSPCodec.fromRows n m a q rows).system.query r j).val := by
      intro j
      simp [SourceClauseCallback.rowQuery, V, typedRowBank,
        SourceCSPCodec.fromRows]
    have haV : ∀ z : Fin (a ^ q), (rows r).2 z =
        (SourceCSPCodec.fromRows n m a q rows).system.accept r
          (SourceClauseRowSchedule.tuple a q z) := by
      intro z
      simp [SourceCSPCodec.fromRows, SourceClauseRowSchedule.tuple]
    rw [← SourceClauseGenericActual.slot_clause_actual
      (SourceCSPCodec.fromRows n m a q rows).system hq r V (rows r).2
      hqV haV k, SourceClauseGenericCount.slot_length]
    cases (rows r).2 k <;>
      simp [SourceClauseGenericDual.clauseCount]
  have hlist : ∀ (cs : List (List EncodedCNF.Clause)),
      (∀ c ∈ cs, c.length ≤ 3 * q + 5) →
      cs.flatten.length ≤ cs.length * (3 * q + 5) := by
    intro cs hcs
    induction cs with
    | nil => simp
    | cons c cs ih =>
        simp only [List.flatten_cons, List.length_append,
          List.length_cons]
        have hc := hcs c List.mem_cons_self
        have ht := ih (by intro d hd; exact hcs d (List.mem_cons_of_mem c hd))
        calc
          c.length + cs.flatten.length ≤
              (3 * q + 5) + cs.length * (3 * q + 5) :=
            Nat.add_le_add hc ht
          _ = (cs.length + 1) * (3 * q + 5) := by ring
  simpa only [rowClauses,
    List.length_ofFn] using
      hlist (List.ofFn fun k : Fin (a ^ q) =>
        SourceGenericOrder.rowChain
          (SourceCSPCodec.fromRows n m a q rows).system hq r k)
        (by
          intro c hc
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
          exact hslot k)

def rowByteIncrement (a q H : Nat) : Nat :=
  (a ^ q) * (slotByteCoefficient a q * (H + 1))

def rowCountIncrement (a q : Nat) : Nat :=
  (a ^ q) * (3 * q + 5)

theorem suffix_payload_bytes_le {n m a q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (hn : n ≤ H) (hm : m ≤ H)
    (ht : 1 + a ^ q ≤ H)
    (r k : Nat) (h : r + 1 + k ≤ m) :
    (EncodedCNF.clauseFields
      (suffixClauses rows hq r k h)).length ≤
        k * rowByteIncrement a q H := by
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
          rowByteIncrement a q H at hhead
      simp only [Nat.succ_mul]
      omega

theorem suffix_clause_count_le {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r k : Nat) (h : r + 1 + k ≤ m) :
    (suffixClauses rows hq r k h).length ≤
      k * rowCountIncrement a q := by
  induction k generalizing r with
  | zero => simp [suffixClauses]
  | succ k ih =>
      rw [suffixClauses_succ, List.length_append]
      have hhead := row_clause_count_le rows hq
        (⟨r + 1, by omega⟩ : Fin m)
      have htail := ih (r + 1) (by omega)
      change (rowClauses rows hq
        (⟨r + 1, by omega⟩ : Fin m)).length ≤
          rowCountIncrement a q at hhead
      simp only [Nat.succ_mul]
      omega

theorem saved_after_prefix_le {n m a q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (hn : n ≤ H) (hm : m ≤ H)
    (ht : 1 + a ^ q ≤ H)
    (r k : Nat) (h : r + 1 + k ≤ m)
    (saved : List Bool) :
    ((EncodedCNF.clauseFields
      (suffixClauses rows hq r k h)).reverse ++ saved).length ≤
        saved.length + k * rowByteIncrement a q H := by
  have hb := suffix_payload_bytes_le rows hq hn hm ht r k h
  simp only [List.length_append, List.length_reverse]
  omega

theorem count_after_prefix_le {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r k : Nat) (h : r + 1 + k ≤ m)
    (count : List Bool) :
    (List.replicate (suffixClauses rows hq r k h).length true ++
      count).length ≤ count.length + k * rowCountIncrement a q := by
  have hc := suffix_clause_count_le rows hq r k h
  simp only [List.length_append, List.length_replicate]
  omega

/-- A single envelope for all physical row-loop banks. The parser term is
fresh on every row and is not iterated into its own input bound. -/
noncomputable def loopEnvelope (a q H m : Nat) : Nat :=
  H + m * (rowByteIncrement a q H + rowCountIncrement a q) +
    SourceGenericNextParserGrowth.parseWordCoefficient a q * (H + 1) ^ 2 + 1

theorem base_le_envelope (a q H m : Nat) : H ≤ loopEnvelope a q H m := by
  unfold loopEnvelope
  omega

theorem parser_le_envelope (a q H m : Nat) :
    SourceGenericNextParserGrowth.parseWordCoefficient a q * (H + 1) ^ 2 ≤
      loopEnvelope a q H m := by
  unfold loopEnvelope
  omega

theorem saved_budget_le_envelope (a q H m k : Nat)
    (saved : List Bool) (hsaved : saved.length ≤ H) (hk : k ≤ m) :
    saved.length + k * rowByteIncrement a q H ≤
      loopEnvelope a q H m := by
  unfold loopEnvelope
  have hmul := Nat.mul_le_mul_right (rowByteIncrement a q H) hk
  rw [Nat.mul_add]
  omega

theorem count_budget_le_envelope (a q H m k : Nat)
    (count : List Bool) (hcount : count.length ≤ H) (hk : k ≤ m) :
    count.length + k * rowCountIncrement a q ≤
      loopEnvelope a q H m := by
  unfold loopEnvelope
  have hmul := Nat.mul_le_mul_right (rowCountIncrement a q) hk
  rw [Nat.mul_add]
  omega

noncomputable def envelopeCoefficient (a q : Nat) : Nat :=
  1 + (a ^ q) * slotByteCoefficient a q + rowCountIncrement a q +
    SourceGenericNextParserGrowth.parseWordCoefficient a q

theorem loopEnvelope_le_quadratic (a q H m : Nat) (hm : m ≤ H) :
    loopEnvelope a q H m ≤ envelopeCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  let A := (a ^ q) * slotByteCoefficient a q
  let C := rowCountIncrement a q
  let P := SourceGenericNextParserGrowth.parseWordCoefficient a q
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

theorem saved_budget_step {n m a q H G k : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r : Fin m)
    (hn : n ≤ H) (hm : m ≤ H) (ht : 1 + a ^ q ≤ H)
    (saved : List Bool)
    (hbudget : saved.length + (k + 1) * rowByteIncrement a q H ≤ G) :
    ((EncodedCNF.clauseFields (rowClauses rows hq r)).reverse ++
      saved).length + k * rowByteIncrement a q H ≤ G := by
  have hb := row_payload_bytes_le rows hq r hn hm ht
  change (EncodedCNF.clauseFields (rowClauses rows hq r)).length ≤
    rowByteIncrement a q H at hb
  simp only [List.length_append, List.length_reverse]
  simp only [Nat.succ_mul] at hbudget
  omega

theorem count_budget_step {n m a q G k : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r : Fin m)
    (count : List Bool)
    (hbudget : count.length + (k + 1) * rowCountIncrement a q ≤ G) :
    (List.replicate (rowClauses rows hq r).length true ++
      count).length + k * rowCountIncrement a q ≤ G := by
  have hc := row_clause_count_le rows hq r
  change (rowClauses rows hq r).length ≤
    rowCountIncrement a q at hc
  simp only [List.length_append, List.length_replicate]
  simp only [Nat.succ_mul] at hbudget
  omega

end EthInapproximability.CurrentPaper.SourceGenericAllRowClock
