import EthInapproximability.CurrentPaper.SourcePrefixRawInput

namespace EthInapproximability.CurrentPaper.SourcePrefixRawHeader

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

def program (q : Nat) := fun l =>
  stackStmt (headerEmbedding (q := q))
    (SourceCSPPositiveHeader.fullHeaderProgram 2 q l)

def startLabel (q : Nat) :=
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))) :
    BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (SourceCSPConstraintGuard.HeaderLabel 2 q)
        SourceCSPQueryRange.Label)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
        SourceCSPVertexCap.Label))

def initialControl (_q : Nat) :
    (SourceCSPConstraintGuard.HeaderControl × SourceCSPQueryRange.Control) ×
      ((Option Bool × Option Bool) × SourceCSPVertexCap.Control) :=
  (((((none, none), (((none, none), none), none)),
      ((none, none), (none, false)))),
    ((none, none), (((none, none), (none, false)), none)))

theorem framed_positive {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P)
    (before : Stack q → List Bool)
    (hheader : ∀ k : SourceCSPPositiveHeader.Stack,
      before (headerEmbedding k) =
        SourceCSPPositiveHeader.initial (EncodedETHSource.constraintBits P) k) :
    ∃ t v S,
      t ≤ SourceCSPPositiveHeader.positiveBound 2 q
        (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length P.vertices P.constraints ∧
      ((advance (program q))^[t])
        (⟨some (startLabel q), initialControl q, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, v, S⟩ ∧
      S (headerVertex (q := q)) =
        true :: List.replicate (P.vertices - 1) true ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (entryEmbedding k) = before (entryEmbedding k)) ∧
      (∀ k : PrefixLoopMachine.Stack,
        S (prefixEmbedding k) = before (prefixEmbedding k)) ∧
      S scratch = before scratch := by
  obtain ⟨t, v, U, ht, hr, hnword, _hmword⟩ :=
    SourceCSPPositiveHeader.encoded_positive_cap P hn hsize
  let c : TM2.Cfg (fun _ : SourceCSPPositiveHeader.Stack => Bool) _ _ :=
    ⟨some (startLabel q), initialControl q,
      SourceCSPPositiveHeader.initial (EncodedETHSource.constraintBits P)⟩
  let V := (((advance (SourceCSPPositiveHeader.fullHeaderProgram 2 q))^[t]) c).var
  have hconcrete : ((advance (SourceCSPPositiveHeader.fullHeaderProgram 2 q))^[t])
      c = ⟨none,
        ((((none, none), (((none, none), none), none)),
          ((none, none), (none, false))), ((none, none), v)), U⟩ := by
    simpa only [c, startLabel, initialControl] using hr
  have hlocal : ((advance (SourceCSPPositiveHeader.fullHeaderProgram 2 q))^[t])
      c = ⟨none, V, U⟩ := by
    simp only [V, hconcrete]
  let S := bank (headerEmbedding (q := q)) before U
  have hrun := BitMachineStackRun.run (headerEmbedding (q := q)) before
    (SourceCSPPositiveHeader.fullHeaderProgram 2 q) c t
  rw [hlocal] at hrun
  have hstart : stackCfg (headerEmbedding (q := q)) before c =
      (⟨some (startLabel q), initialControl q, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) _ _) := by
    simp only [stackCfg, c]
    congr 1
    apply bank_eq_self
    intro k
    exact (hheader k).symm
  refine ⟨t, V, S, ht, ?_, ?_, ?_, ?_, ?_⟩
  · change ((advance (program q))^[t])
        (stackCfg (headerEmbedding (q := q)) before c) =
          ⟨none, V, S⟩ at hrun
    rw [hstart] at hrun
    exact hrun
  · change bank (headerEmbedding (q := q)) before U
      (headerEmbedding (.inr 6)) = _
    rw [bank_at]
    exact hnword
  · intro k
    change bank (headerEmbedding (q := q)) before U
      (entryEmbedding k) = _
    rw [bank_outside]
    rintro ⟨j, hj⟩
    cases hj
  · intro k
    change bank (headerEmbedding (q := q)) before U
      (prefixEmbedding k) = _
    rw [bank_outside]
    rintro ⟨j, hj⟩
    cases hj
  · change bank (headerEmbedding (q := q)) before U scratch = _
    rw [bank_outside]
    rintro ⟨j, hj⟩
    cases hj

end EthInapproximability.CurrentPaper.SourcePrefixRawHeader
