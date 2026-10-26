import Paper2.RecursiveRequestCodeShape
import Paper2.CodeHeaderMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-! Whole-Code output skipper (fixed finite control).

The controller walks literal serialized `GeneratorCode` syntax (header cell
0) alongside a forward generated output word (cell `out`), using a physical
pending stack of Boolean markers: `true` = traverse (consume the node's
output), `false` = skip (syntax only). Each consumed output bit is pushed
onto `used` (so `used` accumulates the consumed word reversed).

* `.emit bits`: the header leaves `bits` in header cell 5; consumed in lockstep.
* `.ticket n`: header leaves `true^n` in cell 1; if nonempty, one bounded-unary
  token `true^j false` is consumed.
* `.bit`: one output bit is consumed.
* `.append`: two markers of the current kind are pushed.
* `.branch3 n ..`: for `n = 0` all three children are skipped. Otherwise the
  header length (256 vs 512) is counted physically in finite control, the
  output prefix is inspected nondestructively (tagged: `false` / `true,false`
  / `true,true`; rows: `false` / `true ++ true^j ++ false ++ tag`) and
  restored, and markers selecting exactly one child are pushed.

The header reader is the admitted `CodeHeaderMachine.program`. No route,
layout, ticket, label boundary or decoded object is supplied. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev Stack := Fin 7 ⊕ Fin 4

def ext (P O U K : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then P else if i = 1 then O else if i = 2 then U else K

/-- The whole bank: header cells 0..6, pending, out, used, peek. -/
def bk (h0 h1 h2 h3 h4 h5 h6 P O U K : List Bool) : Stack → List Bool :=
  Sum.elim (CodeHeaderMachine.contents h0 h1 h2 h3 h4 h5 h6) (ext P O U K)

def pending : Stack := .inr 0
def out : Stack := .inr 1
def used : Stack := .inr 2
def peekC : Stack := .inr 3
def hc (i : Fin 7) : Stack := .inl i

inductive Admin where
  | check | after
  | emitNext | emitTake
  | ticketCheck | ticketTake
  | bitTake
  | branchStart | layout (c : Fin 257)
  | tagged1 | tagged2
  | rows1 | rowsScan | rowsTag
  | restore | pushRoute
  | clear (i : Fin 7)

abbrev W := Option Bool × (Option Bool × Fin 3)
abbrev Label := CodeHeaderMachine.Label ⊕ Admin
abbrev Control := CodeHeaderMachine.Control × W
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def ctl0 : Control := ((none, none), (none, (none, 0)))

/-- Record a popped bit in the scratch component. -/
def rec (v : Control) (b : Option Bool) : Control := (v.1, (b, v.2.2))
def setRoute (v : Control) (r : Fin 3) : Control := (v.1, (v.2.1, (v.2.2.1, r)))

def goClear : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  goto (fun _ => .inr (.clear 0))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Admin.after) (CodeHeaderMachine.program l)
  | .inr .check => pop pending (fun v b => (v.1, (none, (b, 0))))
      (branch (fun v => v.2.2.1.isSome)
        (load (fun v => ((none, none), v.2)) (goto (fun _ => .inl .first))) halt)
  | .inr .after =>
      branch (fun v => decide (v.2.2.1 = some true))
        (branch (fun v => decide (v.1.2 = some .emit))
          (goto (fun _ => .inr .emitNext))
          (branch (fun v => decide (v.1.2 = some .ticket))
            (goto (fun _ => .inr .ticketCheck))
            (branch (fun v => decide (v.1.2 = some .bit))
              (goto (fun _ => .inr .bitTake))
              (branch (fun v => decide (v.1.2 = some .append))
                (push pending (fun _ => true) (push pending (fun _ => true) goClear))
                (goto (fun _ => .inr .branchStart))))))
        (branch (fun v => decide (v.1.2 = some .append))
          (push pending (fun _ => false) (push pending (fun _ => false) goClear))
          (branch (fun v => decide (v.1.2 = some .branch3))
            (push pending (fun _ => false) (push pending (fun _ => false)
              (push pending (fun _ => false) goClear)))
            goClear))
  | .inr .emitNext => pop (hc 5) rec
      (branch (fun v => v.2.1.isSome) (goto (fun _ => .inr .emitTake)) goClear)
  | .inr .emitTake => pop out rec
      (push used (fun v => v.2.1.getD false) (goto (fun _ => .inr .emitNext)))
  | .inr .ticketCheck => pop (hc 1) rec
      (branch (fun v => v.2.1.isSome) (goto (fun _ => .inr .ticketTake)) goClear)
  | .inr .ticketTake => pop out rec
      (push used (fun v => v.2.1.getD false)
        (branch (fun v => decide (v.2.1 = some true))
          (goto (fun _ => .inr .ticketTake)) goClear))
  | .inr .bitTake => pop out rec
      (push used (fun v => v.2.1.getD false) goClear)
  | .inr .branchStart => pop (hc 1) rec
      (branch (fun v => v.2.1.isSome) (goto (fun _ => .inr (.layout 1)))
        (push pending (fun _ => false) (push pending (fun _ => false)
          (push pending (fun _ => false) goClear))))
  | .inr (.layout c) => pop (hc 1) rec
      (branch (fun v => v.2.1.isSome)
        (if h : c.val < 256 then goto (fun _ => .inr (.layout ⟨c.val + 1, by omega⟩))
          else goto (fun _ => .inr .rows1))
        (goto (fun _ => .inr .tagged1)))
  | .inr .tagged1 => pop out rec
      (push peekC (fun v => v.2.1.getD false)
        (branch (fun v => decide (v.2.1 = some true))
          (goto (fun _ => .inr .tagged2))
          (load (fun v => setRoute v 0) (goto (fun _ => .inr .restore)))))
  | .inr .tagged2 => pop out rec
      (push peekC (fun v => v.2.1.getD false)
        (load (fun v => setRoute v (if v.2.1 = some true then 2 else 1))
          (goto (fun _ => .inr .restore))))
  | .inr .rows1 => pop out rec
      (push peekC (fun v => v.2.1.getD false)
        (branch (fun v => decide (v.2.1 = some true))
          (goto (fun _ => .inr .rowsScan))
          (load (fun v => setRoute v 0) (goto (fun _ => .inr .restore)))))
  | .inr .rowsScan => pop out rec
      (push peekC (fun v => v.2.1.getD false)
        (branch (fun v => decide (v.2.1 = some true))
          (goto (fun _ => .inr .rowsScan)) (goto (fun _ => .inr .rowsTag))))
  | .inr .rowsTag => pop out rec
      (push peekC (fun v => v.2.1.getD false)
        (load (fun v => setRoute v (if v.2.1 = some true then 2 else 1))
          (goto (fun _ => .inr .restore))))
  | .inr .restore => pop peekC rec
      (branch (fun v => v.2.1.isSome)
        (push out (fun v => v.2.1.getD false) (goto (fun _ => .inr .restore)))
        (goto (fun _ => .inr .pushRoute)))
  | .inr .pushRoute =>
      branch (fun v => decide (v.2.2.2 = 0))
        (push pending (fun _ => false) (push pending (fun _ => false)
          (push pending (fun _ => true) goClear)))
        (branch (fun v => decide (v.2.2.2 = 1))
          (push pending (fun _ => false) (push pending (fun _ => true)
            (push pending (fun _ => false) goClear)))
          (push pending (fun _ => true) (push pending (fun _ => false)
            (push pending (fun _ => false) goClear))))
  | .inr (.clear i) =>
      if h : i.val < 6 then
        pop (hc ⟨i.val + 1, by omega⟩) rec
          (branch (fun v => v.2.1.isSome) (goto (fun _ => .inr (.clear i)))
            (goto (fun _ => .inr (.clear ⟨i.val + 1, by omega⟩))))
      else load (fun _ => ctl0) (goto (fun _ => .inr .check))

def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (m n : Nat) (c : Config) : run (m + n) c = run n (run m c) := by
  unfold run
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_one (c : Config) : run 1 c = advance program c := rfl

/-! ### Bank access and update lemmas -/

section BankLemmas
variable (h0 h1 h2 h3 h4 h5 h6 P O U K x : List Bool)

@[simp] theorem bk_P : bk h0 h1 h2 h3 h4 h5 h6 P O U K pending = P := rfl
@[simp] theorem bk_O : bk h0 h1 h2 h3 h4 h5 h6 P O U K out = O := rfl
@[simp] theorem bk_U : bk h0 h1 h2 h3 h4 h5 h6 P O U K used = U := rfl
@[simp] theorem bk_K : bk h0 h1 h2 h3 h4 h5 h6 P O U K peekC = K := rfl
@[simp] theorem bk_h1 : bk h0 h1 h2 h3 h4 h5 h6 P O U K (hc 1) = h1 := rfl
@[simp] theorem bk_h5 : bk h0 h1 h2 h3 h4 h5 h6 P O U K (hc 5) = h5 := rfl

@[simp] theorem up_P : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) pending x =
    bk h0 h1 h2 h3 h4 h5 h6 x O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_O : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) out x =
    bk h0 h1 h2 h3 h4 h5 h6 P x U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_U : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) used x =
    bk h0 h1 h2 h3 h4 h5 h6 P O x K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_K : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) peekC x =
    bk h0 h1 h2 h3 h4 h5 h6 P O U x := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_h1 : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) (hc 1) x =
    bk h0 x h2 h3 h4 h5 h6 P O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_h5 : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) (hc 5) x =
    bk h0 h1 h2 h3 h4 x h6 P O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_h2 : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) (hc 2) x =
    bk h0 h1 x h3 h4 h5 h6 P O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_h3 : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) (hc 3) x =
    bk h0 h1 h2 x h4 h5 h6 P O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_h4 : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) (hc 4) x =
    bk h0 h1 h2 h3 x h5 h6 P O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem up_h6 : Function.update (bk h0 h1 h2 h3 h4 h5 h6 P O U K) (hc 6) x =
    bk h0 h1 h2 h3 h4 h5 x P O U K := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
@[simp] theorem bk_h2 : bk h0 h1 h2 h3 h4 h5 h6 P O U K (hc 2) = h2 := rfl
@[simp] theorem bk_h3 : bk h0 h1 h2 h3 h4 h5 h6 P O U K (hc 3) = h3 := rfl
@[simp] theorem bk_h4 : bk h0 h1 h2 h3 h4 h5 h6 P O U K (hc 4) = h4 := rfl
@[simp] theorem bk_h6 : bk h0 h1 h2 h3 h4 h5 h6 P O U K (hc 6) = h6 := rfl

end BankLemmas

/-! ### Single administrative steps -/

section Steps
variable (h0 h1 h2 h3 h4 h5 h6 P O U K : List Bool) (hcv : CodeHeaderMachine.Control)
  (s m : Option Bool) (r : Fin 3)

theorem check_cons (b : Bool) (v : Control) :
    advance program ⟨some (.inr .check), v, bk h0 h1 h2 h3 h4 h5 h6 (b :: P) O U K⟩ =
      ⟨some (.inl .first), ((none, none), (none, (some b, 0))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program]

theorem check_nil (v : Control) :
    advance program ⟨some (.inr .check), v, bk h0 h1 h2 h3 h4 h5 h6 [] O U K⟩ =
      ⟨none, (v.1, (none, (none, 0))), bk h0 h1 h2 h3 h4 h5 h6 [] O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program]

theorem emitNext_cons (b : Bool) :
    advance program ⟨some (.inr .emitNext), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 (b :: h5) h6 P O U K⟩ =
      ⟨some (.inr .emitTake), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem emitNext_nil :
    advance program ⟨some (.inr .emitNext), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 [] h6 P O U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (none, (m, r))),
        bk h0 h1 h2 h3 h4 [] h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, goClear]

theorem emitTake_step (b : Bool) :
    advance program ⟨some (.inr .emitTake), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (b :: O) U K⟩ =
      ⟨some (.inr .emitNext), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O (b :: U) K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem ticketCheck_cons (b : Bool) :
    advance program ⟨some (.inr .ticketCheck), (hcv, (s, (m, r))),
      bk h0 (b :: h1) h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr .ticketTake), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem ticketCheck_nil :
    advance program ⟨some (.inr .ticketCheck), (hcv, (s, (m, r))),
      bk h0 [] h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (none, (m, r))),
        bk h0 [] h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, goClear]

theorem ticketTake_true :
    advance program ⟨some (.inr .ticketTake), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (true :: O) U K⟩ =
      ⟨some (.inr .ticketTake), (hcv, (some true, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O (true :: U) K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem ticketTake_false :
    advance program ⟨some (.inr .ticketTake), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (false :: O) U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (some false, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O (false :: U) K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, goClear]

theorem bitTake_step (b : Bool) :
    advance program ⟨some (.inr .bitTake), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (b :: O) U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O (b :: U) K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, goClear]

theorem branchStart_nil :
    advance program ⟨some (.inr .branchStart), (hcv, (s, (m, r))),
      bk h0 [] h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (none, (m, r))),
        bk h0 [] h2 h3 h4 h5 h6 (false :: false :: false :: P) O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, goClear]

theorem branchStart_cons (b : Bool) :
    advance program ⟨some (.inr .branchStart), (hcv, (s, (m, r))),
      bk h0 (b :: h1) h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.layout 1)), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem layout_cons_lt (c : Fin 257) (hc' : c.val < 256) (b : Bool) :
    advance program ⟨some (.inr (.layout c)), (hcv, (s, (m, r))),
      bk h0 (b :: h1) h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.layout ⟨c.val + 1, by omega⟩)), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, hc']

theorem layout_cons_top (b : Bool) :
    advance program ⟨some (.inr (.layout 256)), (hcv, (s, (m, r))),
      bk h0 (b :: h1) h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr .rows1), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem layout_nil (c : Fin 257) :
    advance program ⟨some (.inr (.layout c)), (hcv, (s, (m, r))),
      bk h0 [] h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr .tagged1), (hcv, (none, (m, r))),
        bk h0 [] h2 h3 h4 h5 h6 P O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem tagged1_false :
    advance program ⟨some (.inr .tagged1), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (false :: O) U K⟩ =
      ⟨some (.inr .restore), (hcv, (some false, (m, 0))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (false :: K)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, setRoute]

theorem tagged1_true :
    advance program ⟨some (.inr .tagged1), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (true :: O) U K⟩ =
      ⟨some (.inr .tagged2), (hcv, (some true, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (true :: K)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem tagged2_step (b : Bool) :
    advance program ⟨some (.inr .tagged2), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (b :: O) U K⟩ =
      ⟨some (.inr .restore), (hcv, (some b, (m, if b then 2 else 1))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (b :: K)⟩ := by
  cases b <;> simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, setRoute]

theorem rows1_false :
    advance program ⟨some (.inr .rows1), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (false :: O) U K⟩ =
      ⟨some (.inr .restore), (hcv, (some false, (m, 0))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (false :: K)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, setRoute]

theorem rows1_true :
    advance program ⟨some (.inr .rows1), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (true :: O) U K⟩ =
      ⟨some (.inr .rowsScan), (hcv, (some true, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (true :: K)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem rowsScan_true :
    advance program ⟨some (.inr .rowsScan), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (true :: O) U K⟩ =
      ⟨some (.inr .rowsScan), (hcv, (some true, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (true :: K)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem rowsScan_false :
    advance program ⟨some (.inr .rowsScan), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (false :: O) U K⟩ =
      ⟨some (.inr .rowsTag), (hcv, (some false, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (false :: K)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem rowsTag_step (b : Bool) :
    advance program ⟨some (.inr .rowsTag), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P (b :: O) U K⟩ =
      ⟨some (.inr .restore), (hcv, (some b, (m, if b then 2 else 1))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U (b :: K)⟩ := by
  cases b <;> simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec, setRoute]

theorem restore_cons (b : Bool) :
    advance program ⟨some (.inr .restore), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P O U (b :: K)⟩ =
      ⟨some (.inr .restore), (hcv, (some b, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P (b :: O) U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem restore_nil :
    advance program ⟨some (.inr .restore), (hcv, (s, (m, r))),
      bk h0 h1 h2 h3 h4 h5 h6 P O U []⟩ =
      ⟨some (.inr .pushRoute), (hcv, (none, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, rec]

theorem pushRoute_0 :
    advance program ⟨some (.inr .pushRoute), (hcv, (s, (m, 0))),
      bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (s, (m, 0))),
        bk h0 h1 h2 h3 h4 h5 h6 (true :: false :: false :: P) O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear]

theorem pushRoute_1 :
    advance program ⟨some (.inr .pushRoute), (hcv, (s, (m, 1))),
      bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (s, (m, 1))),
        bk h0 h1 h2 h3 h4 h5 h6 (false :: true :: false :: P) O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear]

theorem pushRoute_2 :
    advance program ⟨some (.inr .pushRoute), (hcv, (s, (m, 2))),
      bk h0 h1 h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (s, (m, 2))),
        bk h0 h1 h2 h3 h4 h5 h6 (false :: false :: true :: P) O U K⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear]

end Steps

#print axioms check_cons
#print axioms pushRoute_2

end Paper2.OutputSkipper
