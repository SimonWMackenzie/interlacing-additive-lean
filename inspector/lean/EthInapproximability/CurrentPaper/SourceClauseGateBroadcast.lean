import EthInapproximability.CurrentPaper.SourceClauseGateSchedule
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# Physical preparation of an OR gate's nine literal-address work banks

Source: frozen v8 `06-eth.tex`, baseWord-OR translation. An OR gate's three
clauses use only the original literal address and two adjacent baseWord-bit
addresses. This program copies those three input words into the nine work
banks in the exact slot order of `SourceClauseGateSchedule`. Input words are
consumed; no final clause or encoded output is supplied.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateBroadcast

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 4 ⊕ SourceClauseGateSchedule.Stack

def literalSource : Stack := .inl 0
def prefixSource : Stack := .inl 1
def successorSource : Stack := .inl 2
def temp : Stack := .inl 3
def word (i : Fin 9) : Stack := .inr (.inl i)
def sourceIndex (s : Fin 3) : Fin 4 := ⟨s.val, by omega⟩

def literalTargets : List Stack := [word 0, word 6]
def prefixTargets : List Stack := [word 3, word 7]
def successorTargets : List Stack := [word 1, word 2, word 4, word 5, word 8]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def copyProgram (source : Stack) (targets : List Stack) :
    CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

def initial (literal baseWord successor saved output count : List Bool) :
    Stack → List Bool :=
  Sum.elim ![literal, baseWord, successor, []]
    (SourceClauseGateSchedule.contents (fun _ => []) saved output count)

def first (literal : List Bool) (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied literalSource temp literalTargets literal S

def second (baseWord : List Bool) (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied prefixSource temp prefixTargets baseWord S

def third (successor : List Bool) (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied successorSource temp successorTargets successor S

theorem source_ne_temp (s : Fin 3) : (Sum.inl (sourceIndex s) : Stack) ≠ temp := by
  fin_cases s <;> decide

theorem copy_run (s : Fin 3) (targets : List Stack)
    (hnodup : targets.Nodup)
    (hs : (Sum.inl (sourceIndex s) : Stack) ∉ targets) (ht : temp ∉ targets)
    (bits : List Bool) (S : Stack → List Bool)
    (hbits : S (.inl (sourceIndex s)) = bits) (htemp : S temp = []) :
    ((advance (copyProgram (.inl (sourceIndex s)) targets))^[2 * bits.length + 3])
      (⟨some .scan, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none),
        BitMachineBroadcast.copied (.inl (sourceIndex s)) temp targets bits S⟩ := by
  have h := BitMachineBroadcast.broadcast_run
    (copyProgram (.inl (sourceIndex s)) targets)
    (.inl (sourceIndex s)) temp (source_ne_temp s) targets hnodup hs ht
    .scan .restore .finish rfl rfl () none bits S hbits htemp
  rw [show 2 * bits.length + 3 = (2 * bits.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  change advance (copyProgram (.inl (sourceIndex s)) targets)
    (BitMachineBroadcast.run (copyProgram (.inl (sourceIndex s)) targets)
      (2 * bits.length + 2)
      (⟨some .scan, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram]

theorem first_run (literal baseWord successor saved output count : List Bool) :
    ((advance (copyProgram literalSource literalTargets))^[2 * literal.length + 3])
      (⟨some .scan, ((), none), initial literal baseWord successor saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), first literal
        (initial literal baseWord successor saved output count)⟩ := by
  exact copy_run 0 literalTargets (by decide)
    (by simp [literalSource, literalTargets, word])
    (by simp [temp, literalTargets, word]) literal _ rfl rfl

theorem second_run (literal baseWord successor saved output count : List Bool) :
    let S₁ := first literal (initial literal baseWord successor saved output count)
    ((advance (copyProgram prefixSource prefixTargets))^[2 * baseWord.length + 3])
      (⟨some .scan, ((), none), S₁⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), second baseWord S₁⟩ := by
  dsimp only
  apply copy_run 1 prefixTargets (by decide)
    (by simp [prefixSource, prefixTargets, word])
    (by simp [temp, prefixTargets, word])
  · simp [first, BitMachineBroadcast.copied, sourceIndex,
      literalSource, prefixSource, temp, literalTargets, word, initial]
  · exact BitMachineBroadcast.copied_temp ..

theorem third_run (literal baseWord successor saved output count : List Bool) :
    let S₀ := initial literal baseWord successor saved output count
    let S₂ := second baseWord (first literal S₀)
    ((advance (copyProgram successorSource successorTargets))^[2 * successor.length + 3])
      (⟨some .scan, ((), none), S₂⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), third successor S₂⟩ := by
  dsimp only
  apply copy_run 2 successorTargets (by decide)
    (by simp [successorSource, successorTargets, word])
    (by simp [temp, successorTargets, word])
  · simp [first, second, BitMachineBroadcast.copied, sourceIndex,
      literalSource, prefixSource, successorSource, temp,
      literalTargets, prefixTargets, word, initial]
  · exact BitMachineBroadcast.copied_temp ..

def prepared (literal baseWord successor saved output count : List Bool) :
    Stack → List Bool :=
  third successor (second baseWord
    (first literal (initial literal baseWord successor saved output count)))

theorem prepared_word (literal baseWord successor saved output count : List Bool)
    (i : Fin 9) :
    prepared literal baseWord successor saved output count (word i) =
      ![literal, successor, successor, baseWord, successor, successor,
        literal, baseWord, successor] i := by
  fin_cases i <;>
    simp [prepared, third, second, first, BitMachineBroadcast.copied,
      initial, word, literalSource, prefixSource, successorSource, temp,
      literalTargets, prefixTargets, successorTargets,
      SourceClauseGateSchedule.contents]

theorem prepared_saved (literal baseWord successor saved output count : List Bool) :
    prepared literal baseWord successor saved output count
      (.inr (.inr (.inl 0))) = saved := by
  simp [prepared, third, second, first, BitMachineBroadcast.copied,
    initial, SourceClauseGateSchedule.contents,
    literalSource, prefixSource, successorSource, temp,
    literalTargets, prefixTargets, successorTargets, word]

theorem prepared_output (literal baseWord successor saved output count : List Bool) :
    prepared literal baseWord successor saved output count
      (.inr (.inr (.inl 1))) = output := by
  simp [prepared, third, second, first, BitMachineBroadcast.copied,
    initial, SourceClauseGateSchedule.contents,
    literalSource, prefixSource, successorSource, temp,
    literalTargets, prefixTargets, successorTargets, word]

theorem prepared_count (literal baseWord successor saved output count : List Bool) :
    prepared literal baseWord successor saved output count
      (.inr (.inr (.inr ()))) = count := by
  simp [prepared, third, second, first, BitMachineBroadcast.copied,
    initial, SourceClauseGateSchedule.contents,
    literalSource, prefixSource, successorSource, temp,
    literalTargets, prefixTargets, successorTargets, word]

end EthInapproximability.CurrentPaper.SourceClauseGateBroadcast
