import EthInapproximability.CurrentPaper.SourceCSPRowLoopController

/-!
# All-input source-row loop controller

The previously frozen controller proves the typed positive path, but its
`yield` branch checks only the range-validator flag. A row parser can already
have failed before that flag is written. This total variant keeps the same
physical stack, loop, parser, range validator, reset and EOF branch, and
additionally tests the row parser's literal leading success bit before reset.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalController

open Turing TM2.Stmt BitMachineEncoding SourceCSPRowLoopController

abbrev Stack (q : Nat) := SourceCSPRowLoopController.Stack q
abbrev Label (q H : Nat) := SourceCSPRowLoopController.Label q H
abbrev Control := SourceCSPRowLoopController.Control
abbrev Config (q H : Nat) := SourceCSPRowLoopController.Config q H

def program (q H : Nat) (l : Label q H) :
    TM2.Stmt (fun _ : Stack q => Bool) (Label q H) Control :=
  if l = adminLabel .yield then
    peek (.inl (.inr 2)) (fun v b => (v.1, b))
      (branch (fun v => v.2 == some true)
        (peek (.inl (.inr 4)) (fun v b => (v.1, b))
          (branch (fun v => v.2 == some true)
            (load (fun _ => initialControl)
              (goto (fun _ => resetLabel (BitMachineRawSequence.leftLabel 0))))
            (goto (fun _ => adminLabel .reject))))
        (goto (fun _ => adminLabel .reject)))
  else SourceCSPRowLoopController.program q H l

theorem other_step (q H : Nat) (l : Label q H)
    (hl : l ≠ adminLabel .yield) (c : Config q H)
    (hc : c.l = some l) :
    advance (program q H) c = advance (SourceCSPRowLoopController.program q H) c := by
  obtain ⟨ol, v, S⟩ := c
  cases ol with
  | none => cases hc
  | some k =>
      cases Option.some.inj hc
      simp only [advance, TM2.step, Option.getD_some, program, if_neg hl]

theorem yield_success (q H : Nat) (S : Stack q → List Bool)
    (v : QueryControl) (table : List Bool)
    (hparser : S (.inl (.inr 2)) = true :: table)
    (hquery : S (.inl (.inr 4)) = [true]) :
    advance (program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H) =
      ⟨some (resetLabel (BitMachineRawSequence.leftLabel 0)),
        initialControl, S⟩ := by
  simp only [advance, TM2.step, TM2.stepAux, Option.getD_some,
    program, if_pos, hparser, hquery]
  rfl

theorem yield_parser_failure (q H : Nat) (S : Stack q → List Bool)
    (v : QueryControl)
    (hparser : (S (.inl (.inr 2))).head? ≠ some true) :
    advance (program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H) =
      ⟨some (adminLabel .reject),
        ((v, resetStart), (S (.inl (.inr 2))).head?), S⟩ := by
  simp only [advance, TM2.step, TM2.stepAux, Option.getD_some,
    program, if_pos]
  cases hx : (S (.inl (.inr 2))).head? with
  | none => simp [queryControl]
  | some b =>
      cases b with
      | false => simp [queryControl]
      | true => exact False.elim (hparser hx)

theorem yield_query_failure (q H : Nat) (S : Stack q → List Bool)
    (v : QueryControl) (table : List Bool)
    (hparser : S (.inl (.inr 2)) = true :: table)
    (hquery : (S (.inl (.inr 4))).head? ≠ some true) :
    (advance (program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H)).l =
      some (adminLabel .reject) := by
  simp only [advance, TM2.step, TM2.stepAux, Option.getD_some,
    program, if_pos, hparser]
  cases hx : (S (.inl (.inr 4))).head? with
  | none => simp
  | some b =>
      cases b with
      | false => simp
      | true => exact False.elim (hquery hx)

theorem yield_query_false (q H : Nat) (S : Stack q → List Bool)
    (v : QueryControl) (table : List Bool)
    (hparser : S (.inl (.inr 2)) = true :: table)
    (hquery : S (.inl (.inr 4)) = [false]) :
    advance (program q H)
      (⟨some (adminLabel .yield), queryControl v, S⟩ : Config q H) =
      ⟨some (adminLabel .reject), ((v, resetStart), some false), S⟩ := by
  simp only [advance, TM2.step, TM2.stepAux, Option.getD_some,
    program, if_pos, hparser, hquery]
  rfl

theorem reject_step (q H : Nat) (S : Stack q → List Bool) (v : Control) :
    advance (program q H)
      (⟨some (adminLabel .reject), v, S⟩ : Config q H) =
      ⟨none, (v.1, some false), S⟩ := by
  have hn : (adminLabel (q := q) (H := H) .reject) ≠ adminLabel .yield := by
    simp [adminLabel]
  rw [other_step q H (adminLabel .reject) hn _ rfl]
  rfl

theorem check_positive (q H : Nat) (S : Stack q → List Bool)
    (count : List Bool) (hcount : S (.inr 0) = true :: count) :
    advance (program q H)
      (⟨some (adminLabel .check), initialControl, S⟩ : Config q H) =
      ⟨some (queryLabel (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H))), initialControl,
        Function.update S (.inr 0) count⟩ := by
  rw [other_step q H (adminLabel .check) (by simp [adminLabel]) _ rfl]
  exact SourceCSPRowLoopController.check_positive q H S count hcount

theorem check_zero (q H : Nat) (S : Stack q → List Bool)
    (hcount : S (.inr 0) = []) :
    advance (program q H)
      (⟨some (adminLabel .check), initialControl, S⟩ : Config q H) =
      ⟨some (adminLabel .eof), initialControl, S⟩ := by
  rw [other_step q H (adminLabel .check) (by simp [adminLabel]) _ rfl]
  exact SourceCSPRowLoopController.check_zero q H S hcount

theorem eof_empty (q H : Nat) (S : Stack q → List Bool)
    (hsource : S (.inl (.inr 0)) = []) :
    advance (program q H)
      (⟨some (adminLabel .eof), initialControl, S⟩ : Config q H) =
      ⟨some (adminLabel .accept), initialControl, S⟩ := by
  rw [other_step q H (adminLabel .eof) (by simp [adminLabel]) _ rfl]
  exact SourceCSPRowLoopController.eof_empty q H S hsource

theorem eof_nonempty (q H : Nat) (S : Stack q → List Bool)
    (b : Bool) (rest : List Bool)
    (hsource : S (.inl (.inr 0)) = b :: rest) :
    (advance (program q H)
      (⟨some (adminLabel .eof), initialControl, S⟩ : Config q H)).l =
      some (adminLabel .reject) := by
  rw [other_step q H (adminLabel .eof) (by simp [adminLabel]) _ rfl]
  simp [advance, TM2.step, TM2.stepAux,
    SourceCSPRowLoopController.program, adminLabel, hsource]

theorem eof_nonempty_full (q H : Nat) (S : Stack q → List Bool)
    (b : Bool) (rest : List Bool)
    (hsource : S (.inl (.inr 0)) = b :: rest) :
    advance (program q H)
      (⟨some (adminLabel .eof), initialControl, S⟩ : Config q H) =
      ⟨some (adminLabel .reject), ((queryStart, resetStart), some b), S⟩ := by
  rw [other_step q H (adminLabel .eof) (by simp [adminLabel]) _ rfl]
  simp [advance, TM2.step, TM2.stepAux,
    SourceCSPRowLoopController.program, adminLabel, hsource,
    initialControl]

theorem accept_step (q H : Nat) (S : Stack q → List Bool) :
    advance (program q H)
      (⟨some (adminLabel .accept), initialControl, S⟩ : Config q H) =
      ⟨none, ((queryStart, resetStart), some true), S⟩ := by
  rw [other_step q H (adminLabel .accept) (by simp [adminLabel]) _ rfl]
  exact SourceCSPRowLoopController.accept_step q H S

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalController
