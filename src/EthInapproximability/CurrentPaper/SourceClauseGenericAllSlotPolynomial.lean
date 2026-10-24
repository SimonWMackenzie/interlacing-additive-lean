import EthInapproximability.CurrentPaper.SourceClauseGenericAllSlotsClock
import EthInapproximability.CurrentPaper.SourceClauseGenericBlockPolynomial

/-! Fixed-arity polynomial normalization of the exact all-truth-table-slot clock. -/

namespace EthInapproximability.CurrentPaper.SourceClauseGenericAllSlotPolynomial

open SourceClauseGenericCallback SourceClauseGenericAllSlots
open SourceClauseGenericAllSlotsClock
open SourceClauseGenericBlockPolynomial
open SourceClauseGenericCircuitClock
open SourceClauseEncoding EncodedCNF
open BitMachineStackEmbedding
open SourceClauseCallback (rowQuery)
open scoped Classical

def slotByteCoefficient (a q : ℕ) : ℕ :=
  2 * unitByteCoefficient a q + (q + 1) * gateByteCoefficient a q

theorem false_slot_bytes_le {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q))
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (clauseFields (slotClauses hq row n r k false)).length ≤
      slotByteCoefficient a q * (H + 1) := by
  let js := List.ofFn (fun j : Fin q => j)
  let opening := encodeClause (unit (negative (base n r k)))
  let closing := encodeClause (unit (positive (base n r k + q)))
  have ho := opening_bytes_le n r H k hn hr
  have hc : closing.length ≤ unitByteCoefficient a q * (H + 1) := by
    have hp := base_offset_le k n r H q hn hr (by omega)
    simpa only [closing, positive] using
      unit_bytes_le_linear a q H (base n r k + q) true hp
  have hgate : ∀ j ∈ js,
      (falseGateBytes row n r k j).length ≤
        gateByteCoefficient a q * (H + 1) := by
    intro j _
    exact false_gate_bytes_le row n r H k j hn hr hrow
  have hf := foldSaved_length_le (falseGateBytes row n r k)
    js (opening.reverse ++ ([] : List Bool))
    (gateByteCoefficient a q * (H + 1)) hgate
  have hsource := SourceClauseGenericCallback.source_payload hq row n r k ([] : List Bool)
  have hlen := congrArg List.length hsource
  dsimp [slotClauses] at ⊢
  simp only [List.length_append, List.length_reverse, List.length_nil, add_zero] at hlen
  simp only [List.length_append, List.length_reverse, List.length_nil, add_zero] at hf
  have hjs : js.length = q := by simp [js]
  rw [hjs] at hf
  rw [← hlen]
  simpa only [foldSaved, false_fold_eq, opening, closing, js] using
    (show closing.length +
      (foldSaved (falseGateBytes row n r k) js (opening.reverse ++ [])).length ≤
      slotByteCoefficient a q * (H + 1) by
      dsimp [slotByteCoefficient]
      nlinarith)

theorem true_slot_bytes_le {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q))
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (clauseFields (slotClauses hq row n r k true)).length ≤
      slotByteCoefficient a q * (H + 1) := by
  let ps := List.ofFn (fun p : Fin (q + 1) => p)
  let opening := encodeClause (unit (negative (base n r k)))
  let closing := encodeClause (unit (positive (base n r k + (q + 1))))
  have ho := opening_bytes_le n r H k hn hr
  have hc : closing.length ≤ unitByteCoefficient a q * (H + 1) := by
    have hp := base_offset_le k n r H (q + 1) hn hr (by omega)
    simpa only [closing, positive] using
      unit_bytes_le_linear a q H (base n r k + (q + 1)) true hp
  have hgate : ∀ p ∈ ps,
      (trueGateBytes hq row n r k p).length ≤
        gateByteCoefficient a q * (H + 1) := by
    intro p _
    exact true_gate_bytes_le hq row n r H k p hn hr hrow
  have hf := foldSaved_length_le (trueGateBytes hq row n r k)
    ps (opening.reverse ++ ([] : List Bool))
    (gateByteCoefficient a q * (H + 1)) hgate
  have hsource := SourceClauseGenericTrue.source_payload hq row n r k ([] : List Bool)
  have hlen := congrArg List.length hsource
  dsimp [slotClauses] at ⊢
  simp only [List.length_append, List.length_reverse, List.length_nil, add_zero] at hlen
  simp only [List.length_append, List.length_reverse, List.length_nil, add_zero] at hf
  have hps : ps.length = q + 1 := by simp [ps]
  rw [hps] at hf
  rw [← hlen]
  simpa only [true_fold_eq, opening, closing, ps] using
    (show closing.length +
      (foldSaved (trueGateBytes hq row n r k) ps (opening.reverse ++ [])).length ≤
      slotByteCoefficient a q * (H + 1) by
      dsimp [slotByteCoefficient]
      nlinarith)

theorem slot_bytes_le {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q)) (b : Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (clauseFields (slotClauses hq row n r k b)).length ≤
      slotByteCoefficient a q * (H + 1) := by
  cases b with
  | false => exact false_slot_bytes_le hq row n r H k hn hr hrow
  | true => exact true_slot_bytes_le hq row n r H k hn hr hrow

theorem slotSaved_length_le {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q)) (b : Bool) (saved : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (slotSaved hq row n r k b saved).length ≤
      saved.length + slotByteCoefficient a q * (H + 1) := by
  have h := slot_bytes_le hq row n r H k b hn hr hrow
  simp only [slotSaved, List.length_append, List.length_reverse]
  omega

theorem slotCount_length_le {q : ℕ} (b : Bool) (count : List Bool) :
    (slotCount (q := q) b count).length ≤ count.length + 3 * q + 5 := by
  cases b <;> simp [slotCount, SourceClauseGenericDual.clauseCount] <;> omega

theorem finalBank_cursor {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool) (b : Bool) :
    SourceClauseGenericDual.finalBank hq row n r k saved output count remaining b (.inr 0) =
      remaining := by
  rw [SourceClauseGenericDual.finalBank]
  rw [bank_outside]
  · unfold SourceClauseRowWriterTruthFlagFrame.afterFlag
    change bank SourceClauseRowWriterTruthFrame.truthEmbedding
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (SourceClauseRowTruthFlag.flagged row b remaining)
      (SourceClauseRowWriterTruthFrame.truthEmbedding (.inr 0)) = remaining
    rw [bank_at]
    simp [SourceClauseRowTruthFlag.flagged]
  · intro ⟨x, hx⟩
    cases hx

theorem finalBank_flag {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool) (b : Bool) :
    SourceClauseGenericDual.finalBank hq row n r k saved output count remaining b (.inr 1) =
      [b] := by
  rw [SourceClauseGenericDual.finalBank]
  rw [bank_outside]
  · exact SourceClauseRowWriterTruthFlagFrame.flag_bit row n r
      saved output count b remaining
  · intro ⟨x, hx⟩
    cases hx

theorem resetCost_le {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool) (b : Bool) :
    resetCost (SourceClauseGenericDual.finalBank hq row n r k
      saved output count remaining b) ≤ remaining.length + 5 := by
  simp only [resetCost, finalBank_cursor, finalBank_flag, List.length_cons,
    List.length_nil]
  omega

noncomputable def slotCoefficient (a q : ℕ) : ℕ :=
  blockCoefficient a q + 4 * (a ^ q) + 15

theorem slotCost_le_quadratic {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) (table : Fin (a ^ q) → Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H) (houtput : output.length ≤ H)
    (hcount : count.length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    slotCost hq row n r k saved output count table ≤
      slotCoefficient a q * (H + 1) ^ 2 := by
  have hb : blockCost hq row n r k saved output count (table k) ≤
      blockCoefficient a q * (H + 1) ^ 2 := by
    cases h : table k with
    | false =>
        simpa only [blockCost, h, ite_false] using
          false_block_cost_le_quadratic row n r H k saved output count
            hn hr hrow hsaved houtput hcount hquery
    | true =>
        simpa only [blockCost, h, ite_true] using
          true_block_cost_le_quadratic hq row n r H k saved output count
            hn hr hrow hsaved houtput hcount hquery
  have hrst := resetCost_le hq row n r k saved output count
    ((List.ofFn table).drop (k.val + 1)) (table k)
  have hdrop : ((List.ofFn table).drop (k.val + 1)).length ≤ a ^ q := by
    simp only [List.length_drop, List.length_ofFn]
    omega
  have hk := k.isLt
  have hm : 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hscaled := Nat.mul_le_mul_left (4 * (a ^ q) + 15) hm
  calc
    slotCost hq row n r k saved output count table ≤
        blockCoefficient a q * (H + 1) ^ 2 + (4 * a ^ q + 15) := by
      dsimp [slotCost, fullCost, selectedCost]
      simp only [List.length_ofFn]
      omega
    _ ≤ blockCoefficient a q * (H + 1) ^ 2 +
        (4 * a ^ q + 15) * (H + 1) ^ 2 := by omega
    _ = slotCoefficient a q * (H + 1) ^ 2 := by
      dsimp [slotCoefficient]
      ring

def slotIncrement (a q H : ℕ) : ℕ :=
  slotByteCoefficient a q * (H + 1) + 3 * q + 5

theorem listCost_le_quadratic_budget {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H G : ℕ) (table : Fin (a ^ q) → Bool)
    (hn : n ≤ H) (hr : r ≤ H) (hHG : H ≤ G)
    (hrow : ∀ x, (row x).length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (ks : List (Fin (a ^ q))) (saved output count : List Bool)
    (hsaved : saved.length + ks.length * slotIncrement a q H ≤ G)
    (houtput : output.length ≤ H)
    (hcount : count.length + ks.length * slotIncrement a q H ≤ G) :
    SourceClauseGenericAllSlotsClock.listCost hq row n r table ks saved output count ≤
      ks.length * (slotCoefficient a q * (G + 1) ^ 2 + 1) + 1 := by
  induction ks generalizing saved count with
  | nil =>
      simp only [SourceClauseGenericAllSlotsClock.listCost, List.length_nil, Nat.zero_mul, zero_add]
      exact le_rfl
  | cons k ks ih =>
      have hrowG : ∀ x, (row x).length ≤ G := by
        intro x
        exact (hrow x).trans hHG
      have hsaveG : saved.length ≤ G := by
        simpa only [List.length_cons] using
          (show saved.length ≤ saved.length + (k :: ks).length * slotIncrement a q H
            from Nat.le_add_right _ _).trans hsaved
      have hcountG : count.length ≤ G := by
        exact (Nat.le_add_right _ _).trans hcount
      have hslot := slotCost_le_quadratic hq row n r G k saved output count table
        (hn.trans hHG) (hr.trans hHG) hrowG hsaveG
        (houtput.trans hHG) hcountG hquery
      have hsnext := slotSaved_length_le hq row n r H k (table k) saved
        hn hr hrow
      have hcnext := slotCount_length_le (q := q) (table k) count
      have hsbudget :
          (slotSaved hq row n r k (table k) saved).length +
            ks.length * slotIncrement a q H ≤ G := by
        dsimp [slotIncrement] at hsaved hsnext ⊢
        nlinarith
      have hcbudget :
          (slotCount (q := q) (table k) count).length +
            ks.length * slotIncrement a q H ≤ G := by
        dsimp [slotIncrement] at hcount ⊢
        nlinarith
      have htail := ih
        (slotSaved hq row n r k (table k) saved)
        (slotCount (q := q) (table k) count)
        hsbudget hcbudget
      dsimp [SourceClauseGenericAllSlotsClock.listCost]
      nlinarith

def allFactor (a q : ℕ) : ℕ :=
  1 + (a ^ q) * (slotByteCoefficient a q + 3 * q + 5)

noncomputable def allCoefficient (a q : ℕ) : ℕ :=
  (a ^ q) * (slotCoefficient a q * (allFactor a q) ^ 2 + 1) + 1

theorem allCost_le_quadratic {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (table : Fin (a ^ q) → Bool)
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H) (houtput : output.length ≤ H)
    (hcount : count.length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    allCost hq row n r table saved output count ≤
      allCoefficient a q * (H + 1) ^ 2 := by
  let N := a ^ q
  let B := slotIncrement a q H
  let G := H + N * B
  have hHG : H ≤ G := by dsimp [G]; omega
  have hsave : saved.length + (List.ofFn (fun k : Fin N => k)).length * B ≤ G := by
    simp only [List.length_ofFn]
    dsimp [G]
    omega
  have hcount' : count.length + (List.ofFn (fun k : Fin N => k)).length * B ≤ G := by
    simp only [List.length_ofFn]
    dsimp [G]
    omega
  have hlist := listCost_le_quadratic_budget hq row n r H G table
    hn hr hHG hrow hquery (List.ofFn (fun k : Fin N => k))
    saved output count hsave houtput hcount'
  have hM : 1 ≤ H + 1 := by omega
  have hmul := Nat.mul_le_mul_left (N * (3 * q + 5)) hM
  have hfactor : G + 1 ≤ allFactor a q * (H + 1) := by
    have hg : G + 1 =
        (1 + N * slotByteCoefficient a q) * (H + 1) + N * (3 * q + 5) := by
      dsimp [G, B, slotIncrement]
      ring
    have hf : allFactor a q * (H + 1) =
        (1 + N * slotByteCoefficient a q) * (H + 1) +
          N * (3 * q + 5) * (H + 1) := by
      dsimp [allFactor, N]
      ring
    rw [hg, hf]
    omega
  have hsq := Nat.pow_le_pow_left hfactor 2
  have hsq' := Nat.mul_le_mul_left (slotCoefficient a q) hsq
  have hm2 : 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hscale := Nat.mul_le_mul_left (N + 1) hm2
  dsimp [allCost, allCoefficient]
  simp only [List.length_ofFn] at hlist
  calc
    SourceClauseGenericAllSlotsClock.listCost hq row n r table
        (List.ofFn (fun k : Fin (a ^ q) => k)) saved output count ≤
        N * (slotCoefficient a q * (G + 1) ^ 2 + 1) + 1 := by
      simpa only [N] using hlist
    _ ≤ N * (slotCoefficient a q * (allFactor a q * (H + 1)) ^ 2 + 1) + 1 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left N (Nat.add_le_add_right hsq' 1)) 1
    _ = N * slotCoefficient a q * allFactor a q ^ 2 * (H + 1) ^ 2 +
        (N + 1) := by ring
    _ ≤ N * slotCoefficient a q * allFactor a q ^ 2 * (H + 1) ^ 2 +
        (N + 1) * (H + 1) ^ 2 := by omega
    _ = (N * (slotCoefficient a q * allFactor a q ^ 2 + 1) + 1) *
        (H + 1) ^ 2 := by ring

end EthInapproximability.CurrentPaper.SourceClauseGenericAllSlotPolynomial
