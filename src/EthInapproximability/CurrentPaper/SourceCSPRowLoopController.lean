import EthInapproximability.CurrentPaper.SourceCSPRowLoopReset

/-!
# Fixed-stack source-row loop controller

The unary row counter and unread suffix stay on permanent stacks. One branch
consumes one counter mark and runs the physical row parser/query validator.
The `.yield` label exposes its validated query words and truth table before
the physical reset. At zero counter the controller checks actual end-of-input.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopController

open Turing TM2.Stmt BitMachineEncoding

abbrev Stack (q : Nat) := SourceCSPRowLoopReset.Stack q
abbrev QueryLabel (q H : Nat) := BitMachineRawSequence.Label
  (SourceCSPRowController.Label q H) (SourceCSPQueryBank.Label q)
abbrev QueryControl := SourceCSPRowController.Control × SourceCSPQueryBank.Control
abbrev ResetLabel (q : Nat) := SourceCSPRowLoopReset.Label q
abbrev ResetControl := SourceCSPRowLoopReset.Control

inductive Admin where
  | check | eof | yield | accept | reject
  deriving DecidableEq, Fintype

abbrev Label (q H : Nat) := QueryLabel q H ⊕ (ResetLabel q ⊕ Admin)
abbrev Control := (QueryControl × ResetControl) × Option Bool
abbrev Config (q H : Nat) := TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control

def queryStart : QueryControl :=
  ((none, none), (((none, none), (none, false)), none))
def resetStart : ResetControl := (((), none), none)
def initialControl : Control := ((queryStart, resetStart), none)

def queryLabel {q H : Nat} (l : QueryLabel q H) : Label q H := .inl l
def resetLabel {q H : Nat} (l : ResetLabel q) : Label q H := .inr (.inl l)
def adminLabel {q H : Nat} (l : Admin) : Label q H := .inr (.inr l)

def queryStack {q : Nat} : SourceCSPRowQueryFrame.Stack q ↪ Stack q :=
  ⟨Sum.inl, Sum.inl_injective⟩

def queryControl (v : QueryControl) : Control := ((v, resetStart), none)
def resetControl (v : ResetControl) : Control := ((queryStart, v), none)

def program (q H : Nat) : Label q H →
    TM2.Stmt (fun _ : Stack q => Bool) (Label q H) Control
  | .inl l => BitMachineStackEmbedding.stmt queryStack queryLabel
      queryControl (fun v => v.1.1) (some (adminLabel .yield))
      (SourceCSPRowQueryFrame.combinedProgram q H l)
  | .inr (.inl l) => BitMachineInline.stmt resetLabel resetControl
      (fun v => v.1.2) (some (adminLabel .check))
      (SourceCSPRowLoopReset.program q l)
  | .inr (.inr .check) =>
      pop (.inr 0) (fun v b => (v.1, b))
        (branch (fun v => v.2.isSome)
          (load (fun _ => initialControl)
            (goto (fun _ => queryLabel
              (BitMachineRawSequence.leftLabel
                (.start 0 : SourceCSPRowController.Label q H)))))
          (goto (fun _ => adminLabel .eof)))
  | .inr (.inr .eof) =>
      peek (.inl (.inr 0)) (fun v b => (v.1, b))
        (branch (fun v => v.2.isSome)
          (goto (fun _ => adminLabel .reject))
          (goto (fun _ => adminLabel .accept)))
  | .inr (.inr .yield) =>
      peek (.inl (.inr 4)) (fun v b => (v.1, b))
        (branch (fun v => v.2 == some true)
          (load (fun _ => initialControl)
            (goto (fun _ => resetLabel
              (BitMachineRawSequence.leftLabel 0))))
          (goto (fun _ => adminLabel .reject)))
  | .inr (.inr .accept) => load (fun v => (v.1, some true)) halt
  | .inr (.inr .reject) => load (fun v => (v.1, some false)) halt

theorem check_positive (q H : Nat) (S : Stack q → List Bool)
    (count : List Bool) (hcount : S (.inr 0) = true :: count) :
    advance (program q H)
      (⟨some (adminLabel .check), initialControl, S⟩ : Config q H) =
      ⟨some (queryLabel (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H))), initialControl,
        Function.update S (.inr 0) count⟩ := by
  simp [advance, TM2.step, program, adminLabel, queryLabel,
    TM2.stepAux, hcount,
    initialControl, queryStart, resetStart]

theorem check_zero (q H : Nat) (S : Stack q → List Bool)
    (hcount : S (.inr 0) = []) :
    advance (program q H)
      (⟨some (adminLabel .check), initialControl, S⟩ : Config q H) =
      ⟨some (adminLabel .eof), initialControl, S⟩ := by
  simp [advance, TM2.step, program, adminLabel,
    TM2.stepAux, hcount,
    initialControl]

theorem eof_empty (q H : Nat) (S : Stack q → List Bool)
    (hsource : S (.inl (.inr 0)) = []) :
    advance (program q H)
      (⟨some (adminLabel .eof), initialControl, S⟩ : Config q H) =
      ⟨some (adminLabel .accept), initialControl, S⟩ := by
  simp [advance, TM2.step, program, adminLabel,
    TM2.stepAux, hsource, initialControl]

theorem yield_true (q H : Nat) (S : Stack q → List Bool) (v : QueryControl)
    (hstatus : S (.inl (.inr 4)) = [true]) :
    advance (program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H) =
      ⟨some (resetLabel (BitMachineRawSequence.leftLabel 0)),
        initialControl, S⟩ := by
  simp [advance, TM2.step, program, adminLabel, resetLabel,
    TM2.stepAux, hstatus,
    queryControl, initialControl]

theorem accept_step (q H : Nat) (S : Stack q → List Bool) :
    advance (program q H)
      (⟨some (adminLabel .accept), initialControl, S⟩ : Config q H) =
      ⟨none, ((queryStart, resetStart), some true), S⟩ := by
  simp [advance, TM2.step, program, adminLabel,
    TM2.stepAux, initialControl]

theorem finish_empty (q H : Nat) (S : Stack q → List Bool)
    (hcount : S (.inr 0) = [])
    (hsource : S (.inl (.inr 0)) = []) :
    ((advance (program q H))^[3])
      (⟨some (adminLabel .check), initialControl, S⟩ : Config q H) =
      ⟨none, ((queryStart, resetStart), some true), S⟩ := by
  change advance (program q H)
    (advance (program q H)
      (advance (program q H)
        (⟨some (adminLabel .check), initialControl, S⟩ : Config q H))) = _
  rw [check_zero q H S hcount, eof_empty q H S hsource,
    accept_step]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopController
