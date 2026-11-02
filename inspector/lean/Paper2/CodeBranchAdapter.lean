import Paper2.BranchSelection
import Paper2.CodeHeaderDraw
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import Mathlib.Tactic

/-! A charged adapter between an actual loaded branch ticket and child selection. -/

namespace Paper2.CodeBranchAdapter

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

noncomputable section

abbrev Stack := LoadedTicketMachine.Stack ⊕ (Fin 7 ⊕ Fin 1)
abbrev BaseControl := LoadedTicketMachine.Control × CodeHeaderMachine.Control
abbrev Control := BranchSelection.Control × (BaseControl × Option Bool)

def d (i : Fin 16) : Stack := .inl (.inl i)
def h (i : Fin 7) : Stack := .inr (.inl i)
def output : Stack := .inr (.inr 0)

/-- Fifteen actual selector banks occupy only empty work banks and the
three header inputs plus the delimiter-stripped loaded-ticket bank. -/
def selectorSlot : BranchSelection.Stack → Stack
  | .inl (.inl (.inl j)) => d ⟨j.val + 1, by omega⟩
  | .inl (.inl (.inr _)) => d 8
  | .inl (.inr 0) => h 0
  | .inl (.inr 1) => d 9
  | .inr 0 => d 15
  | .inr 1 => h 2
  | .inr 2 => h 3
  | .inr 3 => d 13
  | .inr 4 => d 14

private theorem selectorSlot_injective : Function.Injective selectorSlot := by
  intro x y hv
  fin_cases x <;> fin_cases y <;> simp_all [selectorSlot, d, h]

def selectorEmbed : BranchSelection.Stack ↪ Stack :=
  ⟨selectorSlot, selectorSlot_injective⟩

/-- An auxiliary stack is kept out of the selector's bank image so that
the control-framing lift has an exact stack-sum target. -/
def selectorPlusSlot : BranchSelection.Stack ⊕ Unit → Stack
  | .inl j => selectorSlot j
  | .inr _ => h 6

private theorem selectorPlusSlot_injective : Function.Injective selectorPlusSlot := by
  intro x y hv
  fin_cases x <;> fin_cases y <;> simp_all [selectorPlusSlot, selectorSlot, d, h]

def selectorPlusEmbed : BranchSelection.Stack ⊕ Unit ↪ Stack :=
  ⟨selectorPlusSlot, selectorPlusSlot_injective⟩

inductive Admin where
  | route | ticketScan | ticketRestore | ticketStart
  | selectorDone
  | reverseCode | reverseRest | placeRest | placeCode | finished
  | badTicket
  deriving DecidableEq, Fintype

abbrev Label := BranchSelection.Label ⊕ Admin
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def selectorStmt (l : BranchSelection.Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  stackStmt selectorPlusEmbed
    (liftStmt (some Admin.selectorDone) (BranchSelection.program l))

def adminStmt : Admin → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .route =>
      branch (fun v => decide (v.2.1.1.2.2 = some true))
        (goto (fun _ => .inr .ticketScan))
        (goto (fun _ => .inr .badTicket))
  | .ticketScan =>
      pop (d 15) (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2 == some true)
          (push (h 4) (fun _ => true) (goto (fun _ => .inr .ticketScan)))
          (branch (fun v => v.2.2 == some false)
            (goto (fun _ => .inr .ticketRestore))
            (goto (fun _ => .inr .badTicket))))
  | .ticketRestore =>
      pop (h 4) (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.isSome)
          (push (d 15) (fun _ => true) (goto (fun _ => .inr .ticketRestore)))
          (goto (fun _ => .inr .ticketStart)))
  | .ticketStart => goto (fun _ => .inl (.unary .copyScan))
  | .selectorDone => goto (fun _ => .inr .reverseCode)
  | .reverseCode =>
      pop (h 0) (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.isSome)
          (push (h 5) (fun v => v.2.2.getD false)
            (goto (fun _ => .inr .reverseCode)))
          (goto (fun _ => .inr .reverseRest)))
  | .reverseRest =>
      pop (d 1) (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.isSome)
          (push (h 6) (fun v => v.2.2.getD false)
            (goto (fun _ => .inr .reverseRest)))
          (goto (fun _ => .inr .placeRest)))
  | .placeRest =>
      pop (h 6) (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.isSome)
          (push (h 0) (fun v => v.2.2.getD false)
            (goto (fun _ => .inr .placeRest)))
          (goto (fun _ => .inr .placeCode)))
  | .placeCode =>
      pop (h 5) (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.isSome)
          (push (h 0) (fun v => v.2.2.getD false)
            (goto (fun _ => .inr .placeCode)))
          (goto (fun _ => .inr .finished)))
  | .finished => halt
  | .badTicket => halt

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => selectorStmt l
  | .inr a => adminStmt a

def run (n : Nat) (c : Config) := ((advance program)^[n]) c

/-- All banks not named here are retained literally from the loaded draw. -/
def framedBank (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    Stack → List Bool
  | .inl (.inl 1) => suffix
  | .inl (.inl 15) => ticket
  | .inr (.inl 0) => code
  | .inr (.inl 1) => n
  | .inr (.inl 2) => a
  | .inr (.inl 3) => b
  | .inr (.inl 4) => temp
  | .inr (.inl 5) => revCode
  | .inr (.inl 6) => revRest
  | .inr (.inr _) => out
  | .inl (.inl j) =>
      if (2 ≤ j.val ∧ j.val ≤ 9) ∨ j.val = 13 ∨ j.val = 14 then []
      else foreign (.inl (.inl j))
  | j => foreign j

def phaseCfg (stage : Admin) (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) : Config :=
  ⟨some (.inr stage), (ctl, (base, scratch)),
    framedBank foreign n code suffix ticket a b temp revCode revRest out⟩

theorem route_success (ctl : BranchSelection.Control)
    (base : BaseControl) (hstatus : base.1.2.2 = some true)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .route ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .ticketScan ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux, hstatus]

theorem route_failure (ctl : BranchSelection.Control)
    (base : BaseControl) (hstatus : base.1.2.2 ≠ some true)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .route ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .badTicket ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux, hstatus]

private theorem ticketPush (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    Function.update
      (Function.update
        (framedBank foreign n code suffix (true :: ticket) a b temp revCode revRest out)
        (d 15) ticket)
      (h 4) (true :: temp) =
    framedBank foreign n code suffix ticket a b (true :: temp) revCode revRest out := by
  funext j
  rcases j with (⟨j⟩ | j)
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank, d, h]
    · simp [framedBank, d, h]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank, d, h]
    · fin_cases j <;> simp [framedBank, d, h]

private theorem ticketScan_true (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .ticketScan ctl base scratch foreign n code suffix
        (true :: ticket) a b temp revCode revRest out) =
      phaseCfg .ticketScan ctl base (some true) foreign n code suffix
        ticket a b (true :: temp) revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step,
    TM2.stepAux, framedBank, d, h]
  exact ticketPush foreign n code suffix ticket a b temp revCode revRest out

private theorem ticketScan_false (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .ticketScan ctl base scratch foreign n code suffix
        [false] a b temp revCode revRest out) =
      phaseCfg .ticketRestore ctl base (some false) foreign n code suffix
        [] a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step,
    TM2.stepAux, framedBank, d, h]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank, d, h]
    · simp [framedBank, d, h]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank, d, h]
    · fin_cases j <;> simp [framedBank, d, h]

private theorem ticketScan_nil (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .ticketScan ctl base scratch foreign n code suffix
        [] a b temp revCode revRest out) =
      phaseCfg .badTicket ctl base none foreign n code suffix
        [] a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step,
    TM2.stepAux, framedBank, d, h]

private theorem ticketRestore_true (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .ticketRestore ctl base scratch foreign n code suffix
        ticket a b (true :: temp) revCode revRest out) =
      phaseCfg .ticketRestore ctl base (some true) foreign n code suffix
        (true :: ticket) a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step,
    TM2.stepAux, framedBank, d, h]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank, d, h]
    · simp [framedBank, d, h]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank, d, h]
    · fin_cases j <;> simp [framedBank, d, h]

private theorem ticketRestore_nil (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b revCode revRest out : List Bool) :
    advance program
      (phaseCfg .ticketRestore ctl base scratch foreign n code suffix
        ticket a b [] revCode revRest out) =
      phaseCfg .ticketStart ctl base none foreign n code suffix
        ticket a b [] revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step,
    TM2.stepAux, framedBank, d, h]

private theorem ticketStart_step (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b revCode revRest out : List Bool) :
    advance program
      (phaseCfg .ticketStart ctl base scratch foreign n code suffix
        ticket a b [] revCode revRest out) =
      ⟨some (.inl (.unary .copyScan)), (ctl, (base, scratch)),
        framedBank foreign n code suffix ticket a b [] revCode revRest out⟩ := by
  rfl

private theorem run_succ {c q : Config} (hs : advance program c = q)
    (m : Nat) : run (m+1) c = run m q := by
  simp only [run, Function.iterate_succ_apply, hs]

private theorem run_add {c q : Config} {m : Nat} (hr : run m c = q)
    (k : Nat) : run (m+k) c = run k q := by
  rw [run, show m+k=k+m by omega, Function.iterate_add_apply]
  exact congrArg (fun z => ((advance program)^[k]) z) hr

private theorem replicate_true_move (i : Nat) (xs : List Bool) :
    List.replicate i true ++ true :: xs =
      true :: (List.replicate i true ++ xs) := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [List.replicate_succ] using congrArg (true :: ·) ih

theorem ticket_scan_run (i : Nat) (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix a b temp revCode revRest out : List Bool) :
    run (i+1)
      (phaseCfg .ticketScan ctl base scratch foreign n code suffix
        (List.replicate i true ++ [false]) a b temp revCode revRest out) =
      phaseCfg .ticketRestore ctl base (some false) foreign n code suffix
        [] a b (List.replicate i true ++ temp) revCode revRest out := by
  induction i generalizing scratch temp with
  | zero =>
      simpa [List.replicate] using
        run_succ (ticketScan_false ctl base scratch foreign n
          code suffix a b temp revCode revRest out) 0
  | succ i ih =>
      have hs := ticketScan_true ctl base scratch foreign n
        code suffix (List.replicate i true ++ [false]) a b temp revCode revRest out
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ hs (i+1)]
      simpa [List.replicate_succ, List.cons_append, replicate_true_move] using
        ih (some true) (true :: temp)

theorem ticket_restore_run (i : Nat) (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b revCode revRest out : List Bool) :
    run (i+1)
      (phaseCfg .ticketRestore ctl base scratch foreign n code suffix
        ticket a b (List.replicate i true) revCode revRest out) =
      phaseCfg .ticketStart ctl base none foreign n code suffix
        (List.replicate i true ++ ticket) a b [] revCode revRest out := by
  induction i generalizing scratch ticket with
  | zero =>
      simpa [List.replicate] using
        run_succ (ticketRestore_nil ctl base scratch foreign n
          code suffix ticket a b revCode revRest out) 0
  | succ i ih =>
      have hs := ticketRestore_true ctl base scratch foreign n
        code suffix ticket a b (List.replicate i true) revCode revRest out
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ hs (i+1)]
      simpa [List.replicate_succ, List.cons_append, replicate_true_move] using
        ih (some true) (true :: ticket)

/-- Exact physical transfer of a successful finCodec ticket, including the
false delimiter, to a delimiter-free unary selector input. -/
theorem ticket_ready (i : Nat) (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix a b out : List Bool) :
    run (2*i+3)
      (phaseCfg .ticketScan ctl base scratch foreign n code suffix
        (List.replicate i true ++ [false]) a b [] [] [] out) =
      ⟨some (.inl (.unary .copyScan)), (ctl, (base, none)),
        framedBank foreign n code suffix (List.replicate i true)
          a b [] [] [] out⟩ := by
  have hs := ticket_scan_run i ctl base scratch foreign n
    code suffix a b [] [] [] out
  have hr := ticket_restore_run i ctl base (some false) foreign n
    code suffix [] a b [] [] out
  have hl := ticketStart_step ctl base none foreign n
    code suffix (List.replicate i true) a b [] [] out
  have hlen : List.replicate i true ++ ([] : List Bool) = List.replicate i true := by
    simp
  have hsr : run ((i+1)+(i+1))
      (phaseCfg .ticketScan ctl base scratch foreign n code suffix
        (List.replicate i true ++ [false]) a b [] [] [] out) =
      phaseCfg .ticketStart ctl base none foreign n code suffix
        (List.replicate i true) a b [] [] [] out := by
    rw [run_add hs (i+1)]
    simpa [hlen] using hr
  rw [show 2*i+3 = ((i+1)+(i+1))+1 by omega,
    run_add hsr 1]
  simpa only [run, Function.iterate_one] using hl

private theorem selectorDone_step (ctl : BranchSelection.Control)
    (base : BaseControl) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix out : List Bool) :
    advance program
      (phaseCfg .selectorDone ctl base none foreign n code suffix
        [] [] [] [] [] [] out) =
      phaseCfg .reverseCode ctl base none foreign n code suffix
        [] [] [] [] [] [] out := rfl

private theorem reverseCode_cons (bit : Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .reverseCode ctl base scratch foreign n (bit :: code) suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .reverseCode ctl base (some bit) foreign n code suffix
        ticket a b temp (bit :: revCode) revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · simp [framedBank]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · fin_cases j <;> simp [framedBank]

private theorem reverseCode_nil (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .reverseCode ctl base scratch foreign n [] suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .reverseRest ctl base none foreign n [] suffix
        ticket a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]

private theorem reverseRest_cons (bit : Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .reverseRest ctl base scratch foreign n code (bit :: suffix)
        ticket a b temp revCode revRest out) =
      phaseCfg .reverseRest ctl base (some bit) foreign n code suffix
        ticket a b temp revCode (bit :: revRest) out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · simp [framedBank]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · fin_cases j <;> simp [framedBank]

private theorem reverseRest_nil (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .reverseRest ctl base scratch foreign n code []
        ticket a b temp revCode revRest out) =
      phaseCfg .placeRest ctl base none foreign n code []
        ticket a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]

private theorem placeRest_cons (bit : Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .placeRest ctl base scratch foreign n code suffix
        ticket a b temp revCode (bit :: revRest) out) =
      phaseCfg .placeRest ctl base (some bit) foreign n (bit :: code) suffix
        ticket a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · simp [framedBank]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · fin_cases j <;> simp [framedBank]

private theorem placeRest_nil (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode out : List Bool) :
    advance program
      (phaseCfg .placeRest ctl base scratch foreign n code suffix
        ticket a b temp revCode [] out) =
      phaseCfg .placeCode ctl base none foreign n code suffix
        ticket a b temp revCode [] out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]

private theorem placeCode_cons (bit : Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode revRest out : List Bool) :
    advance program
      (phaseCfg .placeCode ctl base scratch foreign n code suffix
        ticket a b temp (bit :: revCode) revRest out) =
      phaseCfg .placeCode ctl base (some bit) foreign n (bit :: code) suffix
        ticket a b temp revCode revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · simp [framedBank]
  · rcases j with j | j
    · fin_cases j <;> simp [framedBank]
    · fin_cases j <;> simp [framedBank]

private theorem placeCode_nil (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revRest out : List Bool) :
    advance program
      (phaseCfg .placeCode ctl base scratch foreign n code suffix
        ticket a b temp [] revRest out) =
      phaseCfg .finished ctl base none foreign n code suffix
        ticket a b temp [] revRest out := by
  simp [advance, phaseCfg, program, adminStmt, TM2.step, TM2.stepAux,
    framedBank, d, h]

theorem reverseCode_run (code : List Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (suffix ticket a b temp revCode revRest out : List Bool) :
    run (code.length+1)
      (phaseCfg .reverseCode ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .reverseRest ctl base none foreign n [] suffix
        ticket a b temp (code.reverse ++ revCode) revRest out := by
  induction code generalizing scratch revCode with
  | nil =>
      simpa using run_succ (reverseCode_nil ctl base scratch foreign n
        suffix ticket a b temp revCode revRest out) 0
  | cons bit code ih =>
      rw [List.length_cons, run_succ
        (reverseCode_cons bit ctl base scratch foreign n
          code suffix ticket a b temp revCode revRest out) (code.length+1)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit) (bit :: revCode)

theorem reverseRest_run (suffix : List Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code ticket a b temp revCode revRest out : List Bool) :
    run (suffix.length+1)
      (phaseCfg .reverseRest ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .placeRest ctl base none foreign n code []
        ticket a b temp revCode (suffix.reverse ++ revRest) out := by
  induction suffix generalizing scratch revRest with
  | nil =>
      simpa using run_succ (reverseRest_nil ctl base scratch foreign n
        code ticket a b temp revCode revRest out) 0
  | cons bit suffix ih =>
      rw [List.length_cons, run_succ
        (reverseRest_cons bit ctl base scratch foreign n
          code suffix ticket a b temp revCode revRest out) (suffix.length+1)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit) (bit :: revRest)

theorem placeRest_run (revRest : List Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revCode out : List Bool) :
    run (revRest.length+1)
      (phaseCfg .placeRest ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .placeCode ctl base none foreign n (revRest.reverse ++ code) suffix
        ticket a b temp revCode [] out := by
  induction revRest generalizing scratch code with
  | nil =>
      simpa using run_succ (placeRest_nil ctl base scratch foreign n
        code suffix ticket a b temp revCode out) 0
  | cons bit revRest ih =>
      rw [List.length_cons, run_succ
        (placeRest_cons bit ctl base scratch foreign n
          code suffix ticket a b temp revCode revRest out) (revRest.length+1)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit) (bit :: code)

theorem placeCode_run (revCode : List Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (scratch : Option Bool) (foreign : Stack → List Bool) (n : List Bool)
    (code suffix ticket a b temp revRest out : List Bool) :
    run (revCode.length+1)
      (phaseCfg .placeCode ctl base scratch foreign n code suffix
        ticket a b temp revCode revRest out) =
      phaseCfg .finished ctl base none foreign n (revCode.reverse ++ code) suffix
        ticket a b temp [] revRest out := by
  induction revCode generalizing scratch code with
  | nil =>
      simpa using run_succ (placeCode_nil ctl base scratch foreign n
        code suffix ticket a b temp revRest out) 0
  | cons bit revCode ih =>
      rw [List.length_cons, run_succ
        (placeCode_cons bit ctl base scratch foreign n
          code suffix ticket a b temp revCode revRest out) (revCode.length+1)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit) (bit :: code)

/-- From the selector's separate code and suffix stacks, every bit is moved
through physical reversal loops, leaving one selected-code-plus-rest stack. -/
theorem assemble (code rest : List Bool)
    (ctl : BranchSelection.Control) (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool) :
    run (2*code.length + 2*rest.length + 5)
      (phaseCfg .selectorDone ctl base none foreign n code rest
        [] [] [] [] [] [] out) =
      phaseCfg .finished ctl base none foreign n (code ++ rest) []
        [] [] [] [] [] [] out := by
  have h0 := selectorDone_step ctl base foreign n code rest out
  have h1 := reverseCode_run code ctl base none foreign n
    rest [] [] [] [] [] [] out
  have h2 := reverseRest_run rest ctl base none foreign n
    [] [] [] [] [] code.reverse [] out
  have h3 := placeRest_run rest.reverse ctl base none foreign n
    [] [] [] [] [] [] code.reverse out
  have h4 := placeCode_run code.reverse ctl base none foreign n
    rest [] [] [] [] [] [] out
  have h01 : run (1+(code.length+1))
      (phaseCfg .selectorDone ctl base none foreign n code rest
        [] [] [] [] [] [] out) =
      phaseCfg .reverseRest ctl base none foreign n [] rest
        [] [] [] [] code.reverse [] out := by
    rw [run_add (by simpa [run] using h0) (code.length+1)]
    simpa using h1
  have h012 : run ((1+(code.length+1))+(rest.length+1))
      (phaseCfg .selectorDone ctl base none foreign n code rest
        [] [] [] [] [] [] out) =
      phaseCfg .placeRest ctl base none foreign n [] []
        [] [] [] [] code.reverse rest.reverse out := by
    rw [run_add h01 (rest.length+1)]
    simpa using h2
  have h0123 : run (((1+(code.length+1))+(rest.length+1))+
      (rest.reverse.length+1))
      (phaseCfg .selectorDone ctl base none foreign n code rest
        [] [] [] [] [] [] out) =
      phaseCfg .placeCode ctl base none foreign n rest []
        [] [] [] [] code.reverse [] out := by
    rw [run_add h012 (rest.reverse.length+1)]
    simpa using h3
  rw [show 2*code.length + 2*rest.length + 5 =
    (((1+(code.length+1))+(rest.length+1))+
      (rest.reverse.length+1))+(code.reverse.length+1) by
      simp [List.length_reverse]; omega,
    run_add h0123 (code.reverse.length+1)]
  simpa using h4

theorem finished_halt (ctl : BranchSelection.Control)
    (base : BaseControl) (foreign : Stack → List Bool) (n code out : List Bool) :
    advance program
      (phaseCfg .finished ctl base none foreign n code []
        [] [] [] [] [] [] out) =
      ⟨none, (ctl, (base, none)),
        framedBank foreign n code [] [] [] [] [] [] [] out⟩ := by
  rfl

abbrev LocalStack := BranchSelection.Stack ⊕ Unit
abbrev LocalConfig := TM2.Cfg (fun _ : LocalStack => Bool) Label Control

def localProgram : Label → TM2.Stmt (fun _ : LocalStack => Bool) Label Control
  | .inl l => liftStmt (some Admin.selectorDone) (BranchSelection.program l)
  | .inr _ => halt

def localStart (base : BaseControl) (i a b : Nat)
    (f s t : Code) (rest : List Bool) : LocalConfig :=
  liftCfg (some Admin.selectorDone) (base, none) (fun _ => [])
    (BranchSelection.initial i a b f s t rest)

private theorem selector_step (foreign : Stack → List Bool)
    (c : LocalConfig) (l : BranchSelection.Label)
    (hl : c.l = some (.inl l)) :
    advance program (stackCfg selectorPlusEmbed foreign c) =
      stackCfg selectorPlusEmbed foreign (advance localProgram c) := by
  have hsame : advance program (stackCfg selectorPlusEmbed foreign c) =
      advance (fun q => stackStmt selectorPlusEmbed (localProgram q))
        (stackCfg selectorPlusEmbed foreign c) := by
    rcases c with ⟨lab, v, S⟩
    simp only at hl
    subst lab
    rfl
  rw [hsame]
  exact BitMachineStackRun.step selectorPlusEmbed foreign localProgram c

private theorem selector_run_until (foreign : Stack → List Bool)
    (c : LocalConfig) (m : Nat)
    (hlabels : ∀ k < m, ∃ l : BranchSelection.Label,
      (((advance localProgram)^[k]) c).l = some (.inl l)) :
    run m (stackCfg selectorPlusEmbed foreign c) =
      stackCfg selectorPlusEmbed foreign (((advance localProgram)^[m]) c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hsmall : ∀ k < m, ∃ l : BranchSelection.Label,
          (((advance localProgram)^[k]) c).l = some (.inl l) :=
        fun k hk => hlabels k (by omega)
      obtain ⟨l, hl⟩ := hlabels m (by omega)
      rw [run, Function.iterate_succ_apply', ← run, ih hsmall,
        selector_step foreign _ l hl, Function.iterate_succ_apply']

theorem selector_lifted (base : BaseControl) (i a b : Nat)
    (f s t : Code) (rest : List Bool)
    (foreign : Stack → List Bool) :
    ∃ m ≤ 60 * (i+a+b+(BranchSelection.inputWord f s t rest).length+1),
      run m (stackCfg selectorPlusEmbed foreign
        (localStart base i a b f s t rest)) =
      stackCfg selectorPlusEmbed foreign
        (liftCfg (some Admin.selectorDone) (base, none) (fun _ => [])
          (BranchSelection.output (UnaryChoice.choiceOf i a b)
            (encodeCode (if i < a then f else if i < b then s else t)) rest)) := by
  obtain ⟨bound, hbound, hr⟩ := BranchSelection.branch3_select i a b f s t rest
  let c := BranchSelection.initial i a b f s t rest
  have hhalt : (((advance BranchSelection.program)^[bound]) c).l = none := by
    rw [hr]
    rfl
  obtain ⟨m, hm, _, heq, hfirst⟩ :=
    BitMachineSubroutine.first_halt_cfg BranchSelection.program c bound hhalt
  have hlocal := BitMachineSubroutine.lift_run_until
    BranchSelection.program localProgram (some Admin.selectorDone)
    (by intro l; rfl) (base, none) (fun _ : Unit => []) c m hfirst
  have hlabels : ∀ k < m, ∃ l : BranchSelection.Label,
      (((advance localProgram)^[k]) (localStart base i a b f s t rest)).l =
        some (.inl l) := by
    intro k hk
    have hk' := BitMachineSubroutine.lift_run_until
      BranchSelection.program localProgram (some Admin.selectorDone)
      (by intro l; rfl) (base, none) (fun _ : Unit => []) c k
      (fun j hj => hfirst j (by omega))
    have hsource := hfirst k hk
    cases hvar : (((advance BranchSelection.program)^[k]) c).l with
    | none => exact (hsource hvar).elim
    | some l =>
        refine ⟨l, ?_⟩
        rw [localStart, hk', BitMachineComposition.liftCfg, hvar]
  refine ⟨m, hm.trans hbound, ?_⟩
  rw [selector_run_until foreign _ m hlabels, localStart, hlocal, heq, hr]

def selectorSource (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) : Stack → List Bool :=
  framedBank foreign n (BranchSelection.inputWord f s t rest) []
    (List.replicate i true) (List.replicate a true)
    (List.replicate b true) [] [] [] out

private theorem selector_start_bank (base : BaseControl) (foreign : Stack → List Bool)
    (n out : List Bool) (i a b : Nat) (f s t : Code) (rest : List Bool) :
    bank selectorPlusEmbed (selectorSource foreign n out i a b f s t rest)
      (localStart base i a b f s t rest).stk =
      selectorSource foreign n out i a b f s t rest := by
  apply bank_eq_self
  intro k
  fin_cases k <;>
    simp [localStart, liftCfg, BranchSelection.initial,
      BranchSelection.contents, CodeExtract.contents,
      UnaryChoice.contents, selectorSource, framedBank,
      selectorPlusEmbed, selectorPlusSlot, selectorSlot, d, h]

def selectorTarget (foreign : Stack → List Bool) (n out selected rest : List Bool) :
    Stack → List Bool :=
  framedBank foreign n selected rest [] [] [] [] [] [] out

private theorem selector_output_bank (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest selected : List Bool)
    (c : UnaryChoice.Choice) :
    bank selectorPlusEmbed (selectorSource foreign n out i a b f s t rest)
      (liftCfg (some Admin.selectorDone) (base, (none : Option Bool)) (fun _ : Unit => [])
        (BranchSelection.output c selected rest)).stk =
      selectorTarget foreign n out selected rest := by
  funext j
  by_cases hj : ∃ k : LocalStack, selectorPlusEmbed k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [bank_at]
    fin_cases k <;>
      simp [liftCfg, BranchSelection.output, BranchSelection.contents,
        CodeExtract.contents, UnaryChoice.contents, selectorTarget,
        framedBank, selectorPlusEmbed, selectorPlusSlot, selectorSlot, d, h]
  · rw [bank_outside _ _ _ _ hj]
    rcases j with j | j
    · rcases j with j | j
      · fin_cases j <;>
          simp_all [selectorSource, selectorTarget, framedBank,
            selectorPlusEmbed, selectorPlusSlot, selectorSlot, d, h]

        all_goals
          have hz := hj.2 0
          simp [selectorPlusSlot, selectorSlot] at hz
      · rfl
    · rcases j with j | j
      · fin_cases j <;>
          simp_all [selectorSource, selectorTarget, framedBank,
            selectorPlusEmbed, selectorPlusSlot, selectorSlot, d, h]

        all_goals
          first
          | solve | have hz := hj 0; simp [selectorPlusSlot, selectorSlot] at hz
          | solve | have hz := hj 1; simp [selectorPlusSlot, selectorSlot] at hz
          | solve | have hz := hj 2; simp [selectorPlusSlot, selectorSlot] at hz
      · fin_cases j <;>
          simp_all [selectorSource, selectorTarget, framedBank,
            selectorPlusEmbed, selectorPlusSlot, selectorSlot, d, h]

/-- The frozen three-child selector runs on the actual ambient stack slots;
its result leaves the selected code and untouched suffix separate. -/
theorem selector_on_framed (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    ∃ m ≤ 60 * (i+a+b+(BranchSelection.inputWord f s t rest).length+1),
      run m
        ⟨some (.inl (.unary .copyScan)),
          ((BranchSelection.initial i a b f s t rest).var, (base, none)),
          selectorSource foreign n out i a b f s t rest⟩ =
        phaseCfg .selectorDone
          (BranchSelection.output (UnaryChoice.choiceOf i a b)
            (encodeCode (if i < a then f else if i < b then s else t)) rest).var
          base none foreign n
          (encodeCode (if i < a then f else if i < b then s else t)) rest
          [] [] [] [] [] [] out := by
  obtain ⟨m, hm, hr⟩ := selector_lifted base i a b f s t rest
    (selectorSource foreign n out i a b f s t rest)
  refine ⟨m, hm, ?_⟩
  have hstart := selector_start_bank base foreign n out i a b f s t rest
  have hend := selector_output_bank base foreign n out i a b f s t rest
    (encodeCode (if i < a then f else if i < b then s else t))
    (UnaryChoice.choiceOf i a b)
  have hstart' : bank selectorPlusEmbed
      (selectorSource foreign n out i a b f s t rest)
      (Sum.elim (BranchSelection.initial i a b f s t rest).stk
        (fun _ : Unit => [])) =
      selectorSource foreign n out i a b f s t rest := by
    simpa [localStart, liftCfg] using hstart
  have hend' : bank selectorPlusEmbed
      (selectorSource foreign n out i a b f s t rest)
      (Sum.elim
        (BranchSelection.output (UnaryChoice.choiceOf i a b)
          (encodeCode (if i < a then f else if i < b then s else t)) rest).stk
        (fun _ : Unit => [])) =
      selectorTarget foreign n out
        (encodeCode (if i < a then f else if i < b then s else t)) rest := by
    simpa [liftCfg] using hend
  simp only [stackCfg, localStart, liftCfg] at hr
  rw [hstart', hend'] at hr
  simpa [phaseCfg, BranchSelection.initial, BranchSelection.output,
    selectorTarget] using hr

def initial (base : BaseControl) (foreign : Stack → List Bool)
    (n out : List Bool) (i a b : Nat)
    (f s t : Code) (rest : List Bool) : Config :=
  phaseCfg .route ((.first, none), ChildSelect.idle .first)
    base none foreign n (BranchSelection.inputWord f s t rest) []
    (List.replicate i true ++ [false])
    (List.replicate a true) (List.replicate b true) [] [] [] out

def final (base : BaseControl) (foreign : Stack → List Bool)
    (n out : List Bool) (i a b : Nat)
    (f s t : Code) (rest : List Bool) : Config :=
  ⟨none,
    ((BranchSelection.output (UnaryChoice.choiceOf i a b)
      (encodeCode (if i < a then f else if i < b then s else t)) rest).var,
      (base, none)),
    framedBank foreign n
      (encodeCode (if i < a then f else if i < b then s else t) ++ rest)
      [] [] [] [] [] [] [] out⟩

/-- One fixed physical controller consumes the actual finite-codec ticket,
selects a child using both charged unary comparisons, discards the other two
child codes, and restores `selected ++ rest` on header slot 0. -/
theorem branch_adapter (base : BaseControl)
    (hstatus : base.1.2.2 = some true)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    ∃ clock ≤ 70 *
      (i+a+b+(BranchSelection.inputWord f s t rest).length+1),
      run clock (initial base foreign n out i a b f s t rest) =
        final base foreign n out i a b f s t rest := by
  let selected := encodeCode (if i < a then f else if i < b then s else t)
  let ctl0 := (BranchSelection.initial i a b f s t rest).var
  let ctl1 := (BranchSelection.output (UnaryChoice.choiceOf i a b) selected rest).var
  obtain ⟨m, hm, hsel⟩ := selector_on_framed base foreign n out i a b f s t rest
  have hroute := route_success ctl0 base hstatus none foreign n
    (BranchSelection.inputWord f s t rest) []
    (List.replicate i true ++ [false])
    (List.replicate a true) (List.replicate b true) [] [] [] out
  have hticket := ticket_ready i ctl0 base none foreign n
    (BranchSelection.inputWord f s t rest) []
    (List.replicate a true) (List.replicate b true) out
  have hready : run (1+(2*i+3))
      (initial base foreign n out i a b f s t rest) =
      ⟨some (.inl (.unary .copyScan)), (ctl0, (base, none)),
        selectorSource foreign n out i a b f s t rest⟩ := by
    rw [run_add (by simpa [run, initial, ctl0] using hroute) (2*i+3)]
    simpa [selectorSource, ctl0] using hticket
  have hselected : run ((1+(2*i+3))+m)
      (initial base foreign n out i a b f s t rest) =
      phaseCfg .selectorDone ctl1 base none foreign n selected rest
        [] [] [] [] [] [] out := by
    rw [run_add hready m]
    simpa [selected, ctl1] using hsel
  have hass := assemble selected rest ctl1 base foreign n out
  have hassembled : run (((1+(2*i+3))+m)+
      (2*selected.length+2*rest.length+5))
      (initial base foreign n out i a b f s t rest) =
      phaseCfg .finished ctl1 base none foreign n (selected ++ rest) []
        [] [] [] [] [] [] out := by
    rw [run_add hselected (2*selected.length+2*rest.length+5)]
    exact hass
  have hfinish := finished_halt ctl1 base foreign n (selected ++ rest) out
  let clock := (((1+(2*i+3))+m)+
    (2*selected.length+2*rest.length+5))+1
  refine ⟨clock, ?_, ?_⟩
  · have hselLength : selected.length ≤
        (BranchSelection.inputWord f s t rest).length := by
      dsimp [selected, BranchSelection.inputWord]
      split_ifs <;> simp only [List.length_append] <;> omega
    have hrestLength : rest.length ≤
        (BranchSelection.inputWord f s t rest).length := by
      simp only [BranchSelection.inputWord, List.length_append]
      omega
    dsimp [clock]
    omega
  · rw [show clock = (((1+(2*i+3))+m)+
        (2*selected.length+2*rest.length+5))+1 by rfl,
      run_add hassembled 1]
    simpa [run, final, selected, ctl1] using hfinish

private theorem actual_result_bank (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q)
    (a b : Nat) (f s t : Code) (rest out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    (initial
      (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).var
      (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).stk
      (List.replicate D true) out q.val a b f s t rest).stk =
    (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
      (BranchSelection.inputWord f s t rest)
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out F).stk := by
  let inputTape := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  let suffixTape := (RecursiveSamplingTape.writeTape B R N tape.2).val
  let word := LoadedTicketMachine.resultWord D B R N hB tape
  have hwork (j : Fin 16) (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
      (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).stk (d j) = [] := by
    let k : Fin 10 := ⟨j.val, by omega⟩
    have hk : k ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [k] at hv
      omega
    have hw := LoadedTicketMachine.output_draw_work_empty
      inputTape suffixTape D B R F word k hk
    simpa [CodeHeaderDraw.resultCfg, d, CodeHeaderDraw.d, k,
      inputTape, suffixTape, word] using hw
  have h13 :
      (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).stk (d 13) = [] := by
    simpa [CodeHeaderDraw.resultCfg, d, CodeHeaderDraw.d,
      inputTape, suffixTape, word] using
      (LoadedTicketMachine.output_outer_work_empty
        inputTape suffixTape D B R F word).1
  have h14 :
      (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).stk (d 14) = [] := by
    simpa [CodeHeaderDraw.resultCfg, d, CodeHeaderDraw.d,
      inputTape, suffixTape, word] using
      (LoadedTicketMachine.output_outer_work_empty
        inputTape suffixTape D B R F word).2
  have h15 :
      (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).stk (d 15) =
        List.replicate q.val true ++ [false] := by
    have ht := LoadedTicketMachine.output_ticket
      inputTape suffixTape D B R F word
    have hword : word = List.replicate q.val true ++ [false] := by
      simp [word, CodeHeaderDraw.result_word_success D B R N hB tape q hq,
        RecursiveLabelCodecScratch.finCodec]
    simpa [CodeHeaderDraw.resultCfg, d, CodeHeaderDraw.d,
      inputTape, suffixTape, word, hword] using ht
  funext j
  rcases j with j | j
  · rcases j with j | j
    · by_cases hj : 1 ≤ j.val ∧ j.val ≤ 9
      · have hw := hwork j hj
        fin_cases j <;>
          simp_all [initial, phaseCfg, framedBank, d]
      · fin_cases j <;>
          simp_all [initial, phaseCfg, framedBank, d]
    · rfl
  · rcases j with j | j
    · fin_cases j <;>
        simp [initial, phaseCfg, framedBank,
          CodeHeaderDraw.resultCfg, CodeHeaderDraw.rightBank,
          CodeHeaderMachine.contents]
    · fin_cases j <;>
        simp [initial, phaseCfg, framedBank,
          CodeHeaderDraw.resultCfg, CodeHeaderDraw.rightBank]

/-- Adapter entry from the *actual* loaded/header result, with its genuine
success flag and the ticket word produced by the draw. No index or desired
output is supplied to the machine: `q` appears only in the correctness claim. -/
theorem branch_from_result (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q)
    (a b : Nat) (f s t : Code) (rest out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    ∃ clock ≤ 70 *
      (q.val+a+b+(BranchSelection.inputWord f s t rest).length+1),
      run clock
        ⟨some (.inr .route),
          (((.first, none), ChildSelect.idle .first),
            ((CodeHeaderDraw.resultCfg D B R N hB tape .branch3
              (BranchSelection.inputWord f s t rest)
              (List.replicate D true) (List.replicate a true)
              (List.replicate b true) out F).var, none)),
          (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
            (BranchSelection.inputWord f s t rest)
            (List.replicate D true) (List.replicate a true)
            (List.replicate b true) out F).stk⟩ =
        final
          (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
            (BranchSelection.inputWord f s t rest)
            (List.replicate D true) (List.replicate a true)
            (List.replicate b true) out F).var
          (CodeHeaderDraw.resultCfg D B R N hB tape .branch3
            (BranchSelection.inputWord f s t rest)
            (List.replicate D true) (List.replicate a true)
            (List.replicate b true) out F).stk
          (List.replicate D true) out q.val a b f s t rest := by
  let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
    (BranchSelection.inputWord f s t rest)
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) out F
  have hstatus : result.var.1.2.2 = some true := by
    simp [result, CodeHeaderDraw.resultCfg, hq]
  have hbank := actual_result_bank D B R N hB tape q hq a b f s t rest out F
  obtain ⟨clock, hclock, hrun⟩ := branch_adapter result.var hstatus
    result.stk (List.replicate D true) out q.val a b f s t rest
  refine ⟨clock, hclock, ?_⟩
  have hinitial : initial result.var result.stk (List.replicate D true)
      out q.val a b f s t rest =
      ⟨some (.inr .route),
        (((.first, none), ChildSelect.idle .first),
          (result.var, none)), result.stk⟩ := by
    simpa [initial, phaseCfg, result] using congrArg
      (fun X : Stack → List Bool =>
        (⟨some (.inr Admin.route),
          (((.first, none), ChildSelect.idle .first),
            (result.var, none)), X⟩ : Config)) hbank
  rw [hinitial] at hrun
  simpa [result] using hrun

theorem failure_route_raw (ctl : BranchSelection.Control)
    (base : BaseControl) (hstatus : base.1.2.2 ≠ some true)
    (scratch : Option Bool) (S : Stack → List Bool) :
    advance program
      (⟨some (.inr .route), (ctl, (base, scratch)), S⟩ : Config) =
      ⟨some (.inr .badTicket), (ctl, (base, scratch)), S⟩ := by
  simp [advance, program, adminStmt, TM2.step, TM2.stepAux, hstatus]

theorem failure_halt_raw (ctl : BranchSelection.Control)
    (base : BaseControl) (scratch : Option Bool)
    (S : Stack → List Bool) :
    advance program
      (⟨some (.inr .badTicket), (ctl, (base, scratch)), S⟩ : Config) =
      ⟨none, (ctl, (base, scratch)), S⟩ := rfl

/-- The failed draw is detected from its actual status in one transition and
halts in one further transition without interpreting `[]` as index zero. -/
theorem failure_from_result (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (hq : CappedSampler.runWideBits D B R hB tape.1 = none)
    (tail n a b out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (ctl : BranchSelection.Control) :
    let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
      tail n a b out F
    run 2
      ⟨some (.inr .route), (ctl, (result.var, none)), result.stk⟩ =
      ⟨none, (ctl, (result.var, none)), result.stk⟩ := by
  intro result
  have hstatus : result.var.1.2.2 ≠ some true := by
    simp [result, CodeHeaderDraw.resultCfg, hq]
  have hfirst := failure_route_raw ctl result.var hstatus none result.stk
  have hsecond := failure_halt_raw ctl result.var none result.stk
  rw [show 2 = 1+1 by omega, run_succ hfirst 1]
  simpa [run] using hsecond

theorem final_code (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    (final base foreign n out i a b f s t rest).stk (h 0) =
      encodeCode (if i < a then f else if i < b then s else t) ++ rest := rfl

theorem final_tape (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    (final base foreign n out i a b f s t rest).stk (d 0) = foreign (d 0) := rfl

theorem final_output (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    (final base foreign n out i a b f s t rest).stk output = out := rfl

theorem final_status (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    (final base foreign n out i a b f s t rest).var.2.1.1.2.2 =
      base.1.2.2 := rfl

theorem final_work_clear (base : BaseControl)
    (foreign : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    (∀ j : Fin 16,
      (1 ≤ j.val ∧ j.val ≤ 9) ∨ j.val = 13 ∨ j.val = 14 ∨ j.val = 15 →
        (final base foreign n out i a b f s t rest).stk (d j) = []) ∧
    (∀ j : Fin 7, 2 ≤ j.val →
        (final base foreign n out i a b f s t rest).stk (h j) = []) := by
  constructor
  · intro j hj
    fin_cases j <;> simp_all [final, framedBank, d]
  · intro j hj
    fin_cases j <;> simp_all [final, framedBank, h]

#print axioms branch_from_result
#print axioms failure_from_result

end
end Paper2.CodeBranchAdapter
