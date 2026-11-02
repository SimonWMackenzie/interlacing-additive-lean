import EthInapproximability.CurrentPaper.SourcePrefixRawPolynomial

namespace EthInapproximability.CurrentPaper.SourcePrefixRawSourceIdentity

open Turing BitMachineEncoding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open SourcePrefixRawStash
open scoped Classical

/-- The actual first `n` Boolean source clause fields, in source slot order.
This excludes the later ordered-pair at-most slots. -/
def atLeastSourceFields {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q) (hq : 0 < q) : List Bool :=
  (List.range P.vertices).flatMap (fun k =>
    if h : k < P.vertices then
      clauseFields (SourceClauseWriter.slotClauses P.system hq
        ((formula P.system hq).clauses[
          atLeastIndex (m := P.constraints) (q := q)
            (⟨k, h⟩ : Fin P.vertices)],
          (atLeastIndex (m := P.constraints) (q := q)
            (⟨k, h⟩ : Fin P.vertices)).val))
    else [])

theorem q_pos_of_valid_size {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    0 < q := by
  cases q with
  | zero =>
      simp [SourceCSPCodec.ValidSize] at hsize
      omega
  | succ q => omega

theorem source_fields_eq_prefix {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q) (hq : 0 < q) :
    atLeastSourceFields P hq =
      PrefixLoopIteration.prefixFields P.vertices q P.vertices := by
  exact (PrefixLoopIteration.prefixFields_production P.system hq).symm

theorem savedWord_actual_source {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    savedWord P.vertices q =
      (atLeastSourceFields P (q_pos_of_valid_size P hn hsize)).reverse := by
  rw [source_fields_eq_prefix]
  rfl

/-- The unchanged raw-input program reaches an actual entry projection whose
saved stash is the reverse of the first `P.vertices` production source fields.
The raw input remains in the wrapper bank and the count is unary `8*n`. -/
theorem raw_atLeast_actual_source_polynomial {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t S, t ≤ SourcePrefixRawPolynomial.coefficient q *
        ((EncodedETHSource.constraintBits P).length + 1) ^ 5 ∧
      ((advance (SourcePrefixRawProgram.program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)),
          SourcePrefixRawFrame.initial q
            (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : SourcePrefixRawFrame.Stack q => Bool) _ _) =
        ⟨none,
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)), S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (SourcePrefixRawFrame.entryEmbedding k) =
          (SourceCSPEntryWrapper.initial q
            (EncodedETHSource.constraintBits P)
            (atLeastSourceFields P (q_pos_of_valid_size P hn hsize)).reverse
            [] (List.replicate (8 * P.vertices) true)).stk k) := by
  obtain ⟨t, S, ht, hr, he⟩ :=
    SourcePrefixRawPolynomial.raw_atLeast_stash_polynomial P hn hsize
  refine ⟨t, S, ht, hr, ?_⟩
  intro k
  rw [he k, ← savedWord_actual_source P hn hsize]
  rfl

#print axioms q_pos_of_valid_size
#print axioms source_fields_eq_prefix
#print axioms savedWord_actual_source
#print axioms raw_atLeast_actual_source_polynomial

end EthInapproximability.CurrentPaper.SourcePrefixRawSourceIdentity
