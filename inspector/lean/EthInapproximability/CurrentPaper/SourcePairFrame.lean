import EthInapproximability.CurrentPaper.SourcePrefixRawSourceIdentity
import EthInapproximability.CurrentPaper.SourceClausePairVertexLoopMachine

namespace EthInapproximability.CurrentPaper.SourcePairBridge

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

abbrev Stack (q : Nat) :=
  SourcePrefixRawFrame.Stack q ⊕ (PairVertexLoopMachine.Stack ⊕ Fin 1)

def rawEmbedding {q : Nat} : SourcePrefixRawFrame.Stack q ↪ Stack q :=
  Function.Embedding.inl

def pairEmbedding {q : Nat} : PairVertexLoopMachine.Stack ↪ Stack q where
  toFun x := .inr (.inl x)
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)

def scratch {q : Nat} : Stack q := .inr (.inr 0)

def rawN {q : Nat} : Stack q :=
  rawEmbedding SourcePrefixRawFrame.headerVertex
def rawSaved {q : Nat} : Stack q :=
  rawEmbedding SourcePrefixRawFrame.entrySaved
def rawCount {q : Nat} : Stack q :=
  rawEmbedding SourcePrefixRawFrame.entryCount

def pairN {q : Nat} : Stack q :=
  pairEmbedding PairVertexLoopMachine.source
def pairSaved {q : Nat} : Stack q :=
  pairEmbedding (.inl (.inl (.inl 2)))
def pairCount {q : Nat} : Stack q :=
  pairEmbedding (.inl (.inl (.inl 4)))

def emptyForeign {q : Nat} : Stack q → List Bool := fun _ => []

noncomputable def initial (q : Nat) (input : List Bool) :
    Stack q → List Bool :=
  bank rawEmbedding emptyForeign (SourcePrefixRawFrame.initial q input)

noncomputable def framedRaw (S : SourcePrefixRawFrame.Stack q → List Bool) :
    Stack q → List Bool := bank rawEmbedding emptyForeign S

noncomputable def rawProgram (q : Nat) :=
  fun l => stackStmt rawEmbedding (SourcePrefixRawProgram.program q l)

theorem initial_raw (q : Nat) (input : List Bool)
    (x : SourcePrefixRawFrame.Stack q) :
    initial q input (rawEmbedding x) =
      SourcePrefixRawFrame.initial q input x := by
  exact bank_at rawEmbedding emptyForeign _ x

theorem framed_pair_empty (S : SourcePrefixRawFrame.Stack q → List Bool)
    (x : PairVertexLoopMachine.Stack) :
    framedRaw S (pairEmbedding x) = [] := by
  rw [framedRaw, bank_outside]
  · rfl
  · rintro ⟨y, hy⟩
    cases hy

theorem framed_scratch_empty (S : SourcePrefixRawFrame.Stack q → List Bool) :
    framedRaw S scratch = [] := by
  rw [framedRaw, bank_outside]
  · rfl
  · rintro ⟨y, hy⟩
    cases hy

theorem raw_lifted_run {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t S, t ≤ SourcePrefixRawPolynomial.coefficient q *
        ((EncodedETHSource.constraintBits P).length + 1) ^ 5 ∧
      ((advance (rawProgram q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)),
          initial q (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none,
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)),
          framedRaw S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (SourcePrefixRawFrame.entryEmbedding k) =
          (SourceCSPEntryWrapper.initial q
            (EncodedETHSource.constraintBits P)
            (SourcePrefixRawSourceIdentity.atLeastSourceFields P
              (SourcePrefixRawSourceIdentity.q_pos_of_valid_size
                P hn hsize)).reverse []
            (List.replicate (8 * P.vertices) true)).stk k) := by
  obtain ⟨t, S, ht, hr, he⟩ :=
    SourcePrefixRawSourceIdentity.raw_atLeast_actual_source_polynomial
      P hn hsize
  have hs := BitMachineStackRun.run rawEmbedding emptyForeign
    (SourcePrefixRawProgram.program q)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
      ((((none, SourcePrefixRawHeader.initialControl q), none),
        (PrefixLoopCallback.initial, none)), (none, none)),
      SourcePrefixRawFrame.initial q
        (EncodedETHSource.constraintBits P)⟩ :
      TM2.Cfg (fun _ : SourcePrefixRawFrame.Stack q => Bool) _ _) t
  rw [hr] at hs
  exact ⟨t, S, ht, by simpa only [rawProgram, initial,
    framedRaw, stackCfg] using hs, he⟩

end EthInapproximability.CurrentPaper.SourcePairBridge
