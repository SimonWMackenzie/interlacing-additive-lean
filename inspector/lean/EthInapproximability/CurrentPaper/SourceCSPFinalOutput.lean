import EthInapproximability.CurrentPaper.SourceClauseTranslatedOrder
import EthInapproximability.CurrentPaper.SourceClauseCountFinalize

/-! Source-specific charged CNF finalization from the writer accumulator. -/

namespace EthInapproximability.CurrentPaper.SourceFinalOutput

open Turing BitMachineEncoding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def sourceVariables {n m q : ℕ} (_P : CSP n m 2 q) : ℕ :=
  2 * n + (width 2 q + 1) * clauseCount n m 2 q

def sourceEmittedCount {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) : ℕ :=
  40 * n +
    ((List.ofFn fun r : Fin m =>
      SourceClauseCallback.AllSlots.actualListClauses P hq r
        (List.ofFn fun k : Fin (2 ^ q) => k)).flatten).length

def sourceReversePayload {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) : List Bool :=
  (EncodedCNF.clauseFields
    (TranslatedOrder.atLeastChains P ++ TranslatedOrder.pairChains P ++
      (List.ofFn fun r : Fin m =>
        SourceClauseCallback.AllSlots.actualListClauses P hq r
          (List.ofFn fun k : Fin (2 ^ q) => k)).flatten)).reverse

theorem sourceReversePayload_eq {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) :
    sourceReversePayload P hq =
      (EncodedCNF.clauseFields (threeCNF P hq).clauses).reverse := by
  rw [TranslatedOrder.threeCNF_clauses_blocks]
  rfl

theorem sourceVariables_eq {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) :
    sourceVariables P = (threeCNF P hq).variables := by
  simp [sourceVariables, threeCNF, SourceClauseEncoding.translate,
    formula, SourceClauseEncoding.fromIndexed, clauseCount, width,
    Nat.mul_comm]

theorem sourceEmittedCount_eq {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) :
    sourceEmittedCount P hq = (threeCNF P hq).clauses.length := by
  exact (TranslatedOrder.threeCNF_header_length P hq).symm

/-- The existing physical unary-count conversion and finalizer, specialized
to the actual source Boolean three-CNF and the precise reversed clause-field
stream accumulated by its writer. The optional suffix is preserved. -/
theorem source_count_and_finalize {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q) (output : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient *
        (sourceEmittedCount P hq + 1) ^ 2 +
        (sourceReversePayload P hq).length +
        3 * (sourceEmittedCount P hq).bits.length +
        sourceVariables P + 6,
      let c := ((advance SourceClauseCountFinalize.program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr .testFuel)),
          ((SourceClauseCountFinalize.counter.initial, none), none),
          SourceClauseCountFinalize.inputBank
            (sourceVariables P) (sourceEmittedCount P hq)
            (sourceReversePayload P hq) output⟩ :
            SourceClauseCountFinalize.Config)
      c.l = none ∧ c.stk (.inl 3) =
        EncodedCNF.encode (threeCNF P hq) ++ output := by
  obtain ⟨t, ht, hr⟩ :=
    SourceClauseCountFinalize.count_and_finalize_output
      (sourceVariables P) (sourceEmittedCount P hq)
      (sourceReversePayload P hq) output
  refine ⟨t, ht, ?_⟩
  dsimp only
  obtain ⟨hl, ho⟩ := hr
  constructor
  · exact hl
  · rw [ho, sourceVariables_eq P hq, sourceEmittedCount_eq P hq]
    rw [sourceReversePayload_eq]
    simp [EncodedCNF.encode, List.append_assoc]


end EthInapproximability.CurrentPaper.SourceFinalOutput
