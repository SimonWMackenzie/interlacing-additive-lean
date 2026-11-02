import EthInapproximability.CurrentPaper.SourceGenericFirstRowJoinRun

/-!
# Generic literal accumulator identity (unit 1, segment 3)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`); CP-SOURCE-EFFECTIVE,
arbitrary fixed alphabet `a`.

The physically accumulated writer words at the end of the segment-2 body are
EXACTLY the generic source payload and count of the literal Boolean-to-three-CNF
translation of the read-back instance:

* saved: `fields(rows 1..m-1).rev ++ fields(row 0).rev ++ savedWord n a q =
  SourceGenericOrder.sourceReversePayload P hq`;
* count: `true^|rows 1..m-1| ++ true^|row 0| ++ countWord n a =
  true^(SourceGenericOrder.sourceEmittedCount P hq)`;

for `P = (SourceCSPCodec.fromRows n m a q rows).system`. The proof uses the
admitted generic `SourceGenericOrder.threeCNF_clauses_blocks` order (via the
definitions of `sourceReversePayload`/`sourceEmittedCount`) and the admitted
`SourceGenericPrefix` chains; the binary `SourceFinalPayloadIdentity` is not
used. The bridges to the literal `threeCNF` are
`SourceGenericOrder.sourceReversePayload_eq` / `sourceEmittedCount_eq`.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Payload

open SourceGenericPrefixMachine PrefixAmbientInstall EncodedCNF
open scoped Classical

private theorem fields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clauseFields, ih, List.append_assoc]

/-- The source's row-major tuple block of the read-back instance is literally
the concatenation of the physical per-row clause lists. -/
theorem rowChains_eq_rows {n m a q : Nat} (hq : 0 < q)
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    SourceGenericOrder.rowChains (SourceCSPCodec.fromRows n m a q rows).system hq =
      (List.ofFn fun r : Fin m =>
        SourceGenericAllRowLoop.rowClauses rows hq r).flatten := rfl

theorem rows_head_suffix {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    (List.ofFn fun r : Fin m =>
        SourceGenericAllRowLoop.rowClauses rows hq r).flatten =
      FirstRow.firstClauses hq hm rows ++ FirstRow.restClauses hq hm rows := by
  unfold FirstRow.firstClauses FirstRow.restClauses
  cases m with
  | zero => omega
  | succ k =>
      simp only [List.ofFn_succ, List.flatten_cons]
      congr 1
      unfold SourceGenericAllRowLoop.suffixClauses
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext j
      apply congrArg (SourceGenericAllRowLoop.rowClauses rows hq)
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

/-- Saved accumulator identity at arbitrary fixed alphabet. -/
theorem payload_identity {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    (clauseFields (FirstRow.restClauses hq hm rows)).reverse ++
        (clauseFields (FirstRow.firstClauses hq hm rows)).reverse ++
          savedWord n a q =
      SourceGenericOrder.sourceReversePayload
        (SourceCSPCodec.fromRows n m a q rows).system hq := by
  have hv : (SourceCSPCodec.fromRows n m a q rows).vertices = n := rfl
  unfold SourceGenericOrder.sourceReversePayload savedWord
    PrefixCompositeEndpoint.sourceFields
  rw [rowChains_eq_rows, rows_head_suffix hq hm rows, hv]
  simp only [fields_append, List.reverse_append, List.append_assoc]

/-- Unary count identity at arbitrary fixed alphabet. -/
theorem count_identity {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    List.replicate (FirstRow.restClauses hq hm rows).length true ++
        List.replicate (FirstRow.firstClauses hq hm rows).length true ++
          countWord n a =
      List.replicate (SourceGenericOrder.sourceEmittedCount
        (SourceCSPCodec.fromRows n m a q rows).system hq) true := by
  have hv : (SourceCSPCodec.fromRows n m a q rows).vertices = n := rfl
  unfold SourceGenericOrder.sourceEmittedCount countWord
  rw [rowChains_eq_rows, rows_head_suffix hq hm rows, hv]
  simp only [List.length_append, ← List.replicate_add]
  congr 1
  ring

/-- The same identities against the literal translation `threeCNF`. -/
theorem payload_threeCNF {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    (clauseFields (FirstRow.restClauses hq hm rows)).reverse ++
        (clauseFields (FirstRow.firstClauses hq hm rows)).reverse ++
          savedWord n a q =
      (clauseFields (SourceBooleanEncoding.threeCNF
        (SourceCSPCodec.fromRows n m a q rows).system hq).clauses).reverse := by
  rw [payload_identity, SourceGenericOrder.sourceReversePayload_eq]

theorem count_threeCNF {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    List.replicate (FirstRow.restClauses hq hm rows).length true ++
        List.replicate (FirstRow.firstClauses hq hm rows).length true ++
          countWord n a =
      List.replicate (SourceBooleanEncoding.threeCNF
        (SourceCSPCodec.fromRows n m a q rows).system hq).clauses.length true := by
  rw [count_identity, SourceGenericOrder.sourceEmittedCount_eq]

/-- The segment-2 exit bank, restated with the identified accumulators. -/
theorem finalBank_eq {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) :
    FirstRow.finalBank hq hm rows S U lastRow =
      BitMachineStackEmbedding.bank (fsbEmb q) (FirstRow.prefixedBank S U n a)
        (SourceCSPNextRowBridge.callbackBank
          (SourceGenericAllRowLoop.withRemaining
            (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0)
          lastRow n (m - 1)
          (SourceGenericOrder.sourceReversePayload
            (SourceCSPCodec.fromRows n m a q rows).system hq)
          []
          (List.replicate (SourceGenericOrder.sourceEmittedCount
            (SourceCSPCodec.fromRows n m a q rows).system hq) true)) := by
  unfold FirstRow.finalBank
  rw [payload_identity hq hm rows, count_identity hq hm rows]

#print axioms rowChains_eq_rows
#print axioms rows_head_suffix
#print axioms payload_identity
#print axioms count_identity
#print axioms payload_threeCNF
#print axioms count_threeCNF
#print axioms finalBank_eq

end EthInapproximability.CurrentPaper.SourceGenericComposite.Payload
