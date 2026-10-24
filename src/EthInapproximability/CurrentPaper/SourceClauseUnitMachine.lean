import EthInapproximability.CurrentPaper.SourceClauseCountedStream
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# Physical unit-clause template from one address word

Source: frozen v8 `06-eth.tex`, prefix-OR chain endpoints. A unit clause repeats
the same signed literal three times in the ordered 3-CNF encoding. This module
copies a single binary address word to the three literal banks, emits the
actual encoded clause, and increments the physical unary clause counter.
The address word is an input produced by the separate affine-address stage;
neither three final literal words nor an encoded clause is supplied.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseUnitMachine

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 2 ⊕ SourceClauseCountedStream.Stack

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def source : Stack := .inl 0
def temp : Stack := .inl 1
def word0 : Stack := .inr (.inl 0)
def word1 : Stack := .inr (.inl 1)
def word2 : Stack := .inr (.inl 2)
def targets : List Stack := [word0, word1, word2]

def copyProgram : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

def initial (word saved output count : List Bool) : Stack → List Bool :=
  Sum.elim ![word, []]
    (SourceClauseCountedStream.contents
      (SourceLiteralWriter.cfg (some (.begin 0)) none (fun _ => []) saved output).stk
      count)

def prepared (word saved output count : List Bool) : Stack → List Bool :=
  Sum.elim ![[], []]
    (SourceClauseCountedStream.contents
      (SourceLiteralWriter.cfg (some (.begin 0)) none (fun _ => word) saved output).stk
      count)

def finished (c : EncodedCNF.Clause) (saved output count : List Bool) :
    Stack → List Bool :=
  Sum.elim ![[], []]
    (SourceClauseCountedStream.contents
      (SourceLiteralWriter.cfg none none (fun _ => [])
        ((EncodedCNF.encodeClause c).reverse ++ saved) output).stk (true :: count))

theorem initial_source (word saved output count : List Bool) :
    initial word saved output count source = word := rfl

theorem initial_temp (word saved output count : List Bool) :
    initial word saved output count temp = [] := rfl

theorem copy_result (word saved output count : List Bool) :
    BitMachineBroadcast.copied source temp targets word
      (initial word saved output count) = prepared word saved output count := by
  funext k
  cases k with
  | inl j => fin_cases j <;> simp [BitMachineBroadcast.copied, source, temp,
      targets, initial, prepared]
  | inr j =>
      cases j with
      | inr u => cases u; simp [BitMachineBroadcast.copied, source, temp,
          targets, word0, word1, word2, initial, prepared,
          SourceClauseCountedStream.contents]
      | inl j => fin_cases j <;> simp [BitMachineBroadcast.copied, source, temp,
          targets, initial, prepared, word0, word1, word2,
          SourceClauseCountedStream.contents, SourceLiteralWriter.cfg,
          SourceLiteralWriter.contents]

theorem copy_finish (S : Stack → List Bool) (v : Unit × Option Bool) :
    advance copyProgram (⟨some .finish, v, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
        ⟨none, v, S⟩ := by simp [advance, TM2.step, copyProgram]

theorem copied_word (word saved output count : List Bool) :
    ((advance copyProgram)^[2 * word.length + 3])
      (⟨some .scan, ((), none), initial word saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), prepared word saved output count⟩ := by
  have h := BitMachineBroadcast.broadcast_run copyProgram source temp
    (by simp [source, temp]) targets
    (by simp [targets, word0, word1, word2])
    (by simp [source, targets, word0, word1, word2])
    (by simp [temp, targets, word0, word1, word2])
    .scan .restore .finish rfl rfl () none word
    (initial word saved output count) (initial_source ..) (initial_temp ..)
  rw [show 2 * word.length + 3 = (2 * word.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * word.length + 2)
      (⟨some .scan, ((), none), initial word saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  rw [copy_finish, copy_result]

def embedding : SourceClauseCountedStream.Stack ↪ Stack := Function.Embedding.inr

def writerProgram (sign : Fin 3 → Bool) (l : SourceClauseCountedStream.Label) :=
  stackStmt embedding (SourceClauseCountedStream.program sign l)

theorem writer_bank (S T : SourceClauseCountedStream.Stack → List Bool)
    (sourceWord tempWord : List Bool) :
    bank embedding (Sum.elim ![sourceWord, tempWord] S) T =
      Sum.elim ![sourceWord, tempWord] T := by
  funext k
  cases k with
  | inr j => exact bank_at embedding _ T j
  | inl j =>
      rw [bank_outside]
      · rfl
      · intro ⟨u, h⟩; cases h

def unitClause (v : Nat) (sign : Bool) : EncodedCNF.Clause :=
  SourceClauseEncoding.unit ⟨v, sign⟩

theorem unit_words (v : Nat) (sign : Bool) :
    SourceLiteralWriter.words (unitClause v sign) =
      (fun _ => v.bits) := by
  funext i; fin_cases i <;> rfl

theorem unit_signs (v : Nat) (sign : Bool) :
    SourceLiteralWriter.signs (unitClause v sign) = (fun _ => sign) := by
  funext i; fin_cases i <;> rfl

def program (sign : Bool) := BitMachineRawSequence.program copyProgram
  (writerProgram fun _ => sign)
  (BitMachineRawSequence.leftLabel (.begin 0)) ((), none) (none, ())

/-- One finite Boolean-stack program broadcasts the source address word,
writes the repeated-literal unit clause, and increments the unary count.
The preserved output suffix and reverse accumulator make it composable with
the other clause templates. -/
theorem unit_run (v : Nat) (sign : Bool) (saved output count : List Bool) :
    ∃ t ≤ 5 * v.bits.length + 13,
      ((advance (program sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel .scan), (((), none), (none, ())),
          initial v.bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label CopyLabel SourceClauseCountedStream.Label)
            ((Unit × Option Bool) × SourceClauseCountedStream.Control)) =
        ⟨none, (((), none), (none, ())),
          finished (unitClause v sign) saved output count⟩ := by
  let c := unitClause v sign
  have hb := SourceClauseCountedStream.counted_clause c saved output count
  obtain ⟨tb, htb, hrun⟩ := hb
  rw [unit_words, unit_signs] at hrun
  have hrun' := BitMachineStackRun.run embedding (prepared v.bits saved output count)
    (SourceClauseCountedStream.program fun _ => sign)
    (⟨some (BitMachineRawSequence.leftLabel (.begin 0)), (none, ()),
      SourceClauseCountedStream.contents
        (SourceLiteralWriter.cfg (some (.begin 0)) none (fun _ => v.bits)
          saved output).stk count⟩ : SourceClauseCountedStream.Config) tb
  rw [hrun] at hrun'
  have hprep : bank embedding (prepared v.bits saved output count)
      (SourceClauseCountedStream.contents
        (SourceLiteralWriter.cfg (some (.begin 0)) none (fun _ => v.bits)
          saved output).stk count) = prepared v.bits saved output count := by
    exact writer_bank _ _ [] []
  have hfin : bank embedding (prepared v.bits saved output count)
      (SourceClauseCountedStream.contents
        (SourceLiteralWriter.cfg none none (fun _ => [])
          ((EncodedCNF.encodeClause c).reverse ++ saved) output).stk
          (true :: count)) = finished c saved output count := by
    exact writer_bank _ _ [] []
  simp only [stackCfg, hprep, hfin] at hrun'
  have ha := copied_word v.bits saved output count
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copyProgram
    (writerProgram fun _ => sign) .scan
    (BitMachineRawSequence.leftLabel (.begin 0))
    ((), none) ((), none) (none, ()) (none, ())
    (initial v.bits saved output count)
    (prepared v.bits saved output count)
    (finished c saved output count)
    (2 * v.bits.length + 3) tb ha hrun'
  refine ⟨t, ?_, ?_⟩
  · have he : SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) =
      3 * v.bits.length + 6 := by
        simp [c, unitClause, SourceClauseEncoding.unit,
          SourceLiteralWriter.emitTime, SourceLiteralWriter.words]
        omega
    omega
  · simpa only [program] using hr

end EthInapproximability.CurrentPaper.SourceClauseUnitMachine
