import EthInapproximability.CurrentPaper.SourceClauseMachine
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Physical clause emission with an emitted-clause counter

Source: frozen v8 `06-eth.tex`, exact-one and prefix-chain source adapter.
One existing literal-stream call emits a three-literal clause into the
reverse accumulator. This program immediately pushes one bit onto a separate
unary clause-count bank. The count is therefore tied to actual emissions,
including accepted tuple slots' extra gates, rather than an estimated formula.

The producer of the clause's three variable words and finite sign dispatch
remain separate. No list of final clauses is supplied to this machine.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCountedStream

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceLiteralWriter.Stack ⊕ Unit
abbrev Label := BitMachineRawSequence.Label SourceLiteralWriter.Label Unit
abbrev Control := Option Bool × Unit
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def embedding : SourceLiteralWriter.Stack ↪ Stack := Function.Embedding.inl

def contents (S : SourceLiteralWriter.Stack → List Bool) (count : List Bool) :
    Stack → List Bool := Sum.elim S (fun _ => count)

def literalProgram (sign : Fin 3 → Bool) (l : SourceLiteralWriter.Label) :=
  stackStmt embedding (SourceLiteralStream.program sign l)

def countProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit
  | () => push (.inr ()) (fun _ => true) halt

def program (sign : Fin 3 → Bool) :=
  BitMachineRawSequence.program (literalProgram sign) countProgram () none ()

theorem embedded_bank (S T : SourceLiteralWriter.Stack → List Bool)
    (count : List Bool) :
    bank embedding (contents S count) T = contents T count := by
  funext k
  cases k with
  | inl j => exact bank_at embedding _ T j
  | inr j =>
      cases j
      rw [bank_outside]
      · rfl
      · intro ⟨u, h⟩
        cases h

theorem count_step (S : SourceLiteralWriter.Stack → List Bool) (count : List Bool) :
    advance countProgram
      (⟨some (), (), contents S count⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
    ⟨none, (), contents S (true :: count)⟩ := by
  simp only [advance, TM2.step, Option.getD_some, countProgram, TM2.stepAux]
  congr 1
  funext k
  cases k with
  | inl j => simp [contents]
  | inr j => cases j; simp [contents]

/-- Exact raw run on one selected clause, with the output suffix retained.
The one-bit count increment follows the physical literal write and is charged
along with the finite-control handoff. -/
theorem counted_clause (c : EncodedCNF.Clause) (saved output count : List Bool) :
    ∃ t ≤ SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 3,
      ((advance (program (SourceLiteralWriter.signs c)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.begin 0)), (none, ()),
          contents (SourceLiteralWriter.cfg (some (.begin 0)) none
            (SourceLiteralWriter.words c) saved output).stk count⟩ : Config) =
        ⟨none, (none, ()),
          contents (SourceLiteralWriter.cfg none none (fun _ => [])
            ((EncodedCNF.encodeClause c).reverse ++ saved) output).stk
            (true :: count)⟩ := by
  let S₀ := (SourceLiteralWriter.cfg (some (.begin 0)) none
    (SourceLiteralWriter.words c) saved output).stk
  let S₁ := (SourceLiteralWriter.cfg none none (fun _ => [])
    ((EncodedCNF.encodeClause c).reverse ++ saved) output).stk
  have ha := BitMachineStackRun.run embedding (contents S₀ count)
    (SourceLiteralStream.program (SourceLiteralWriter.signs c))
    (SourceLiteralWriter.cfg (some (.begin 0)) none
      (SourceLiteralWriter.words c) saved output)
    (SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 1)
  have hs := SourceLiteralStream.stream_clause c saved output
  change ((advance (SourceLiteralStream.program (SourceLiteralWriter.signs c)))^[
      SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 1])
      (SourceLiteralWriter.cfg (some (.begin 0)) none
        (SourceLiteralWriter.words c) saved output) =
      SourceLiteralWriter.cfg none none (fun _ => [])
        ((EncodedCNF.encodeClause c).reverse ++ saved) output at hs
  rw [hs] at ha
  simp only [stackCfg, embedded_bank] at ha
  have hb := count_step S₁ count
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (literalProgram (SourceLiteralWriter.signs c)) countProgram
    (.begin 0) () none none () ()
    (contents S₀ count) (contents S₁ count) (contents S₁ (true :: count))
    (SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 1) 1 ha hb
  exact ⟨t, by omega, hr⟩

end EthInapproximability.CurrentPaper.SourceClauseCountedStream
