import EthInapproximability.CurrentPaper.SourceClauseHeaderCount
import EthInapproximability.CurrentPaper.SourceLiteralStream

/-!
# Ordered source-clause stream and its physical per-clause emission charge

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source` and
`B-effectivity-details.tex`, the exact-one Boolean encoding followed by
ordered prefix-OR chains. This module begins with a typed CSP whose queries
and fixed-size truth tables are already in the canonical validated banks,
not a supplied list of three-CNF clauses. The separate size guard is stated
where needed. Three-CNF clauses are computed from original labelled slots.

`stream` is the semantic loop invariant for a future single finite-control
machine. `physicalCharge` sums the exact times of existing literal-stream
machine calls; it is deliberately not a claim that the inter-call dispatch,
address production, header or final reversal has already been compiled.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseWriter

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

/-- The ordered clause family for one original Boolean clause occurrence. -/
def slotClauses {n m a q : Nat} (_P : CSP n m a q) (_hq : 0 < q)
    (slot : List EncodedCNF.Literal × Nat) : List EncodedCNF.Clause :=
  SourceClauseEncoding.chain
    (n * a + slot.2 * (width a q + 1)) slot.1

/-- A single physical writer call prepends the reversed encoded clause to
the accumulator. This is the bank effect certified by `stream_clause`. -/
def prependClause (c : EncodedCNF.Clause) (saved : List Bool) : List Bool :=
  (EncodedCNF.encodeClause c).reverse ++ saved

def prependSlot {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q)
    (slot : List EncodedCNF.Literal × Nat) (saved : List Bool) : List Bool :=
  (slotClauses P hq slot).foldl (fun bits c => prependClause c bits) saved

/-- The slot loop's accumulator is reverse output. The original source
clauses are generated in their canonical finite-label order. -/
def stream {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q) : List Bool :=
  ((formula P hq).clauses.zipIdx).foldl
    (fun saved slot => prependSlot P hq slot saved) []

theorem prepend_clause_correct (c : EncodedCNF.Clause) (saved : List Bool) :
    prependClause c saved = (EncodedCNF.encodeClause c).reverse ++ saved := rfl

/-- This is an actual run of the existing finite Boolean-stack instruction
table, including every sign and bit marker. The clause is produced by the
slot generator at the call site; it is not a preloaded final formula. -/
theorem physical_clause_step (c : EncodedCNF.Clause) (saved : List Bool) :
    SourceLiteralStream.run (SourceLiteralWriter.signs c)
      (SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 1)
      (SourceLiteralWriter.cfg (some (.begin 0)) none
        (SourceLiteralWriter.words c) saved []) =
    SourceLiteralWriter.cfg none none (fun _ => [])
      (prependClause c saved) [] := by
  simpa only [prependClause] using SourceLiteralStream.stream_clause c saved []

private theorem fold_prepend (cs : List EncodedCNF.Clause) (saved : List Bool) :
    cs.foldl (fun bits c => prependClause c bits) saved =
      (EncodedCNF.clauseFields cs).reverse ++ saved := by
  induction cs generalizing saved with
  | nil => simp [EncodedCNF.clauseFields]
  | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [prependClause, EncodedCNF.clauseFields, List.append_assoc]

theorem prependSlot_correct {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q)
    (slot : List EncodedCNF.Literal × Nat) (saved : List Bool) :
    prependSlot P hq slot saved =
      (EncodedCNF.clauseFields (slotClauses P hq slot)).reverse ++ saved := by
  exact fold_prepend _ _

private theorem clauseFields_append (xs ys : List EncodedCNF.Clause) :
    EncodedCNF.clauseFields (xs ++ ys) =
      EncodedCNF.clauseFields xs ++ EncodedCNF.clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp [EncodedCNF.clauseFields, ih, List.append_assoc]

private theorem fold_slots {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q)
    (slots : List (List EncodedCNF.Literal × Nat)) (saved : List Bool) :
    slots.foldl (fun bits slot => prependSlot P hq slot bits) saved =
      (EncodedCNF.clauseFields (slots.flatMap (slotClauses P hq))).reverse ++ saved := by
  induction slots generalizing saved with
  | nil => simp [EncodedCNF.clauseFields]
  | cons slot slots ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [prependSlot_correct, List.flatMap_cons, clauseFields_append,
        List.reverse_append]
      simp [List.append_assoc]

theorem ordered_slots {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q) :
    (((formula P hq).clauses.zipIdx).flatMap (slotClauses P hq)) =
      (threeCNF P hq).clauses := rfl

/-- The loop emits exactly the existing ordered three-CNF payload, with one
final reversal and no permutation of repeated clause occurrences. -/
theorem stream_correct {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q) :
    (stream P hq).reverse = EncodedCNF.clauseFields (threeCNF P hq).clauses := by
  rw [stream, fold_slots, ordered_slots]
  simp

/-- Semantic finalization: the numeric clause count is the number of emitted
prefix-chain clauses, not merely the count of original CSP constraints. -/
def withHeader {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q) : List Bool :=
  EncodedGraph.unary (threeCNF P hq).variables ++
    EncodedCommunication.natField
      (SourceClauseHeaderCount.countedClauses (formula P hq).clauses) ++
      (stream P hq).reverse

theorem withHeader_correct {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q) :
    withHeader P hq = EncodedCNF.encode (threeCNF P hq) := by
  unfold withHeader EncodedCNF.encode
  rw [stream_correct, ← SourceClauseHeaderCount.boolean_clause_count P hq]

/-- The exact transition charge of one existing physical literal-stream call.
It excludes producing its three variable words and choosing the next slot. -/
def clauseCharge (c : EncodedCNF.Clause) : Nat :=
  SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 1

theorem clauseCharge_le_bits (c : EncodedCNF.Clause) :
    clauseCharge c ≤ (EncodedCNF.encodeClause c).length + 1 := by
  have h := SourceLiteralWriter.clauseBits_length
    (SourceLiteralWriter.signs c) (SourceLiteralWriter.words c)
  rw [SourceLiteralWriter.clauseBits_eq] at h
  simp only [SourceLiteralWriter.words, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h
  simp only [clauseCharge, SourceLiteralWriter.emitTime,
    SourceLiteralWriter.words, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  omega

def physicalCharge (cs : List EncodedCNF.Clause) : Nat :=
  (cs.map clauseCharge).sum

theorem physicalCharge_le (cs : List EncodedCNF.Clause) :
    physicalCharge cs ≤ (EncodedCNF.clauseFields cs).length + cs.length := by
  induction cs with
  | nil => simp [physicalCharge, EncodedCNF.clauseFields]
  | cons c cs ih =>
      have hc := clauseCharge_le_bits c
      simp only [physicalCharge, List.map_cons, List.sum_cons,
        EncodedCNF.clauseFields, List.length_append, List.length_cons] at ih ⊢
      omega

theorem source_physicalCharge_le {n m a q : Nat} (P : CSP n m a q) (hq : 0 < q) :
    physicalCharge (threeCNF P hq).clauses ≤
      (EncodedCNF.encode (threeCNF P hq)).length +
        (threeCNF P hq).clauses.length := by
  have h := physicalCharge_le (threeCNF P hq).clauses
  simp only [EncodedCNF.encode, List.length_append] at ⊢
  omega

/-- All physical *literal-emission* calls together have a fixed quadratic
bound in the number of source constraints, once the separately validated
`n ≤ q*m` guard holds. Dispatch, address generation, field headers and final
reversal are additional costs and are not included in this bound. -/
theorem source_physicalCharge_quadratic {n m a q : Nat}
    (P : CSP n m a q) (hq : 0 < q) (hn : n ≤ q * m) :
    physicalCharge (threeCNF P hq).clauses ≤
      (6 * (threeSizeFactor a q) ^ 2 + 10 * threeSizeFactor a q + 2) *
        (m + 1) ^ 2 := by
  let S := threeSizeFactor a q
  let F := threeCNF P hq
  have hsize : F.variables + F.clauses.length ≤ S * m :=
    threeCNF_size P hq hn
  have hv : F.variables ≤ S * m := by omega
  have hc : F.clauses.length ≤ S * m := by omega
  have henc := EncodedCNF.encode_length_upper F (threeCNF_valid P hq)
  have hmul := Nat.mul_le_mul hc
    (show 6 * F.variables + 8 ≤ 6 * (S * m) + 8 by omega)
  have hphys := source_physicalCharge_le P hq
  change physicalCharge F.clauses ≤ (EncodedCNF.encode F).length + F.clauses.length at hphys
  change (EncodedCNF.encode F).length ≤
    F.variables + 2 + F.clauses.length * (6 * F.variables + 8) at henc
  change physicalCharge F.clauses ≤
    (6 * S ^ 2 + 10 * S + 2) * (m + 1) ^ 2
  nlinarith

end EthInapproximability.CurrentPaper.SourceClauseWriter
