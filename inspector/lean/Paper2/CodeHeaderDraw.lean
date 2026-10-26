import Paper2.CodeHeaderMachine
import Paper2.LoadedTicketMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import Mathlib.Tactic

/-! Physical handoff from encoded first-order draw headers to one loaded draw. -/

namespace Paper2.CodeHeaderDraw

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open GeneratorCode GeneratorSerialization

noncomputable section

abbrev DrawStack := LoadedTicketMachine.Stack
abbrev Stack := DrawStack ⊕ (Fin 7 ⊕ Fin 1)
abbrev HeaderControl := CodeHeaderMachine.Control
abbrev DrawControl := LoadedTicketMachine.Control
abbrev Control := DrawControl × HeaderControl

inductive Admin where
  | route | copyTicket (l : BitMachineCopy.Label)
  | copyBranch (l : BitMachineCopy.Label)
  | bitFirst | bitSecond | launch
  deriving DecidableEq, Fintype

abbrev Label := LoadedTicketMachine.Label ⊕ (CodeHeaderMachine.Label ⊕ Admin)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def headerSlot : Fin 7 ↪ Stack where
  toFun i := .inr (.inl i)
  inj' := by intro i j h; exact Sum.inl_injective (Sum.inr_injective h)

def h (i : Fin 7) : Stack := .inr (.inl i)
def output : Stack := .inr (.inr 0)
def d (i : Fin 16) : Stack := .inl (.inl i)

def copySlot : Fin 3 → Stack
  | 0 => h 1
  | 1 => d 10
  | _ => h 6

private theorem copySlot_injective : Function.Injective copySlot := by
  intro x y hv
  fin_cases x <;> fin_cases y <;> simp [copySlot, h, d] at hv ⊢

def copyEmbed : Fin 3 ↪ Stack := ⟨copySlot, copySlot_injective⟩

def drawInitialControl : DrawControl :=
  (LoadedTicketMachine.loaderStartControl, LoadedTicketMachine.statusStartControl)

noncomputable def headerProgram (l : CodeHeaderMachine.Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt headerSlot (fun x => .inr (.inl x))
    (fun v => (drawInitialControl, v)) Prod.snd
    (some (.inr (.inr .route))) (CodeHeaderMachine.program l)

def adminProgram : Admin → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .route =>
      branch (fun v => decide (v.2.2 = some .bit))
        (goto (fun _ => .inr (.inr .bitFirst)))
        (branch (fun v => decide (v.2.2 = some .ticket ∨ v.2.2 = some .branch3))
          (branch (fun v => decide (v.2.2 = some .ticket))
            (goto (fun _ => .inr (.inr (.copyTicket .scan))))
            (goto (fun _ => .inr (.inr (.copyBranch .scan))))) halt)
  | .copyTicket l =>
      BitMachineStackEmbedding.stmt copyEmbed
        (fun x => .inr (.inr (.copyTicket x)))
        (fun v => (drawInitialControl, (v, some .ticket)))
        (fun v => v.2.1) (some (.inr (.inr .launch)))
        (BitMachineCopy.program l)
  | .copyBranch l =>
      BitMachineStackEmbedding.stmt copyEmbed
        (fun x => .inr (.inr (.copyBranch x)))
        (fun v => (drawInitialControl, (v, some .branch3)))
        (fun v => v.2.1) (some (.inr (.inr .launch)))
        (BitMachineCopy.program l)
  | .bitFirst => push (d 10) (fun _ => true)
      (goto (fun _ => .inr (.inr .bitSecond)))
  | .bitSecond => push (d 10) (fun _ => true)
      (goto (fun _ => .inr (.inr .launch)))
  | .launch => goto (fun _ => .inl
      (BitMachineRawSequence.leftLabel LoadedTicketMachine.loaderStartLabel))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt none (LoadedTicketMachine.program l)
  | .inr (.inl l) => headerProgram l
  | .inr (.inr a) => adminProgram a

def foreignBank (outputWord : List Bool) (D B R : Nat) (tape : List Bool) :
    Stack → List Bool :=
  Sum.elim (DrawParameterLoader.initialBank tape D B R)
    (Sum.elim (fun _ => []) (fun _ => outputWord))

noncomputable def startBank (code outputWord tape : List Bool) (B R : Nat) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank headerSlot
    (foreignBank outputWord 0 B R tape)
    (CodeHeaderMachine.initial code).stk

noncomputable def start (code outputWord tape : List Bool) (B R : Nat) : Config :=
  ⟨some (.inr (.inl .first)), (drawInitialControl, (none,none)),
    startBank code outputWord tape B R⟩

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

private theorem copied_start_bank (q : List Bool) (k : DrawParameterLoader.LogCopyStack) :
    (ETHParameterScaleMachineLogCopy.start q).stk k =
      if k = .inl (0 : Fin 1) then q else [] := by
  change BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack
    (fun _ => []) (BitMachineCopy.cfg (some .scan) none q [] []).stk k = _
  by_cases hk : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
  · obtain ⟨p,rfl⟩ := hk
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases p <;>
      simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl (0 : Fin 1) : DrawParameterLoader.LogCopyStack) := by
      intro he
      exact hk ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using he.symm⟩
    simp [hne]

private theorem draw_start_bank (tape : List Bool) (D B R : Nat) :
    (LoadedTicketMachine.start tape D B R).stk =
      DrawParameterLoader.initialBank tape D B R := by
  funext j
  change BitMachineStackEmbedding.bank DrawParameterLoader.logEmbed
    (DrawParameterLoader.initialBank tape D B R)
    (ETHParameterScaleMachineLogCopy.start (List.replicate D true)).stk j = _
  by_cases hj : ∃ k : DrawParameterLoader.LogCopyStack,
      DrawParameterLoader.logEmbed k = j
  · obtain ⟨k,rfl⟩ := hj
    rw [BitMachineStackEmbedding.bank_at, copied_start_bank]
    cases k with
    | inl i => fin_cases i; rfl
    | inr i => simp [DrawParameterLoader.initialBank,
        DrawParameterLoader.mainBank, DrawParameterLoader.logEmbed]
  · exact BitMachineStackEmbedding.bank_outside _ _ _ _ hj

def stagingBank (tape : List Bool) (B R : Nat)
    (tail n a b used outputWord : List Bool) (D : Nat) : Stack → List Bool :=
  Sum.elim (DrawParameterLoader.initialBank tape D B R)
    (Sum.elim (CodeHeaderMachine.contents tail n a b [] [] used)
      (fun _ => outputWord))

def stagingCfg (stage : Admin) (scratch : Option Bool)
    (kind : CodeHeaderMachine.Kind) (tape : List Bool) (B R : Nat)
    (tail n a b used outputWord : List Bool) (D : Nat) : Config :=
  ⟨some (.inr (.inr stage)),
    (drawInitialControl, (scratch, some kind)),
    stagingBank tape B R tail n a b used outputWord D⟩

private theorem copy_bank_start (tape : List Bool) (B R : Nat)
    (tail a b outputWord : List Bool) (n : Nat) :
    BitMachineStackEmbedding.bank copyEmbed
      (stagingBank tape B R tail (List.replicate n true) a b [] outputWord 0)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate n true) [] []).stk =
    stagingBank tape B R tail (List.replicate n true) a b [] outputWord 0 := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> rfl

private theorem staging_d_update (tape : List Bool) (B R : Nat)
    (tail n a b used outputWord : List Bool) (D : Nat) :
    stagingBank tape B R tail n a b used outputWord D =
      Function.update (stagingBank tape B R tail n a b used outputWord 0)
        (d 10) (List.replicate D true) := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl i => fin_cases i <;> simp [stagingBank, d,
          DrawParameterLoader.initialBank, DrawParameterLoader.mainBank,
          Function.update]
      | inr i => simp [stagingBank, d, Function.update,
          DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
  | inr k => simp [stagingBank, d, Function.update]

private theorem copy_bank_end (tape : List Bool) (B R : Nat)
    (tail a b outputWord : List Bool) (n : Nat) :
    BitMachineStackEmbedding.bank copyEmbed
      (stagingBank tape B R tail (List.replicate n true) a b [] outputWord 0)
      (BitMachineCopy.cfg none none
        (List.replicate n true) (List.replicate n true) []).stk =
    stagingBank tape B R tail (List.replicate n true) a b [] outputWord n := by
  have hc : (BitMachineCopy.cfg none none
        (List.replicate n true) (List.replicate n true) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate n true) [] []).stk 1
        (List.replicate n true) := by
    funext k
    fin_cases k <;> simp [BitMachineCopy.cfg, BitMachineCopy.stackContents,
      Function.update]
  rw [hc, BitMachineStackEmbedding.bank_update, copy_bank_start]
  exact (staging_d_update tape B R tail (List.replicate n true) a b [] outputWord n).symm

private theorem route_ticket (tape : List Bool) (B R : Nat)
    (tail n a b outputWord : List Bool) :
    advance program (stagingCfg .route none .ticket tape B R
      tail n a b [] outputWord 0) =
    stagingCfg (.copyTicket .scan) none .ticket tape B R
      tail n a b [] outputWord 0 := by rfl

private theorem route_branch (tape : List Bool) (B R : Nat)
    (tail n a b outputWord : List Bool) :
    advance program (stagingCfg .route none .branch3 tape B R
      tail n a b [] outputWord 0) =
    stagingCfg (.copyBranch .scan) none .branch3 tape B R
      tail n a b [] outputWord 0 := by rfl

private theorem route_bit (tape : List Bool) (B R : Nat)
    (tail n a b outputWord : List Bool) :
    advance program (stagingCfg .route none .bit tape B R
      tail n a b [] outputWord 0) =
    stagingCfg .bitFirst none .bit tape B R
      tail n a b [] outputWord 0 := by rfl

private theorem launch (kind : CodeHeaderMachine.Kind)
    (tape : List Bool) (B R D : Nat)
    (tail n a b outputWord : List Bool) :
    advance program (stagingCfg .launch none kind tape B R
      tail n a b [] outputWord D) =
    ⟨some (.inl (BitMachineRawSequence.leftLabel
        LoadedTicketMachine.loaderStartLabel)),
      (drawInitialControl, (none, some kind)),
      stagingBank tape B R tail n a b [] outputWord D⟩ := by rfl

private theorem copy_ticket_run (tape : List Bool) (B R n : Nat)
    (tail a b outputWord : List Bool) :
    ∃ t ≤ 2*n+2,
      run t (stagingCfg (.copyTicket .scan) none .ticket tape B R
        tail (List.replicate n true) a b [] outputWord 0) =
      stagingCfg .launch none .ticket tape B R
        tail (List.replicate n true) a b [] outputWord n := by
  let S := stagingBank tape B R tail (List.replicate n true) a b [] outputWord 0
  let localStart := BitMachineCopy.cfg (some .scan) none
    (List.replicate n true) [] []
  have hc : BitMachineCopy.run (2*n+2) localStart =
      BitMachineCopy.cfg none none
        (List.replicate n true) (List.replicate n true) [] := by
    simpa [localStart] using BitMachineCopy.run_correct none (List.replicate n true) []
  have hh : (((advance BitMachineCopy.program)^[2*n+2]) localStart).l = none := by
    rw [← BitMachineCopy.run, hc]
    rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    copyEmbed S (fun l => .inr (.inr (.copyTicket l)))
    (fun v => (drawInitialControl, (v, some CodeHeaderMachine.Kind.ticket)))
    (fun v : Control => v.2.1) (by intro v; rfl)
    (some (.inr (.inr .launch)))
    BitMachineCopy.program program (by intro l; rfl)
    localStart (2*n+2) hh
  rw [← BitMachineCopy.run, hc] at hr
  refine ⟨t,ht,?_⟩
  simpa [run, stagingCfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    S, localStart, copy_bank_start, copy_bank_end] using hr

private theorem copy_branch_run (tape : List Bool) (B R n : Nat)
    (tail a b outputWord : List Bool) :
    ∃ t ≤ 2*n+2,
      run t (stagingCfg (.copyBranch .scan) none .branch3 tape B R
        tail (List.replicate n true) a b [] outputWord 0) =
      stagingCfg .launch none .branch3 tape B R
        tail (List.replicate n true) a b [] outputWord n := by
  let S := stagingBank tape B R tail (List.replicate n true) a b [] outputWord 0
  let localStart := BitMachineCopy.cfg (some .scan) none
    (List.replicate n true) [] []
  have hc : BitMachineCopy.run (2*n+2) localStart =
      BitMachineCopy.cfg none none
        (List.replicate n true) (List.replicate n true) [] := by
    simpa [localStart] using BitMachineCopy.run_correct none (List.replicate n true) []
  have hh : (((advance BitMachineCopy.program)^[2*n+2]) localStart).l = none := by
    rw [← BitMachineCopy.run, hc]
    rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    copyEmbed S (fun l => .inr (.inr (.copyBranch l)))
    (fun v => (drawInitialControl, (v, some CodeHeaderMachine.Kind.branch3)))
    (fun v : Control => v.2.1) (by intro v; rfl)
    (some (.inr (.inr .launch)))
    BitMachineCopy.program program (by intro l; rfl)
    localStart (2*n+2) hh
  rw [← BitMachineCopy.run, hc] at hr
  refine ⟨t,ht,?_⟩
  simpa [run, stagingCfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    S, localStart, copy_bank_start, copy_bank_end] using hr

private theorem staging_push_d (tape : List Bool) (B R D : Nat)
    (tail n a b used outputWord : List Bool) :
    Function.update (stagingBank tape B R tail n a b used outputWord D)
      (d 10) (true ::
        stagingBank tape B R tail n a b used outputWord D (d 10)) =
    stagingBank tape B R tail n a b used outputWord (D+1) := by
  have hd : stagingBank tape B R tail n a b used outputWord D (d 10) =
      List.replicate D true := rfl
  rw [hd, staging_d_update tape B R tail n a b used outputWord D]
  conv_rhs => rw [staging_d_update tape B R tail n a b used outputWord (D+1)]
  simp [Function.update_idem, List.replicate_succ]

private theorem bit_first_step (tape : List Bool) (B R D : Nat)
    (tail n a b used outputWord : List Bool) :
    advance program
      (stagingCfg .bitFirst none .bit tape B R tail n a b used outputWord D) =
    stagingCfg .bitSecond none .bit tape B R tail n a b used outputWord (D+1) := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram,
    stagingCfg, d, Option.getD_some]
  congr 1
  exact staging_push_d tape B R D tail n a b used outputWord

private theorem bit_second_step (tape : List Bool) (B R D : Nat)
    (tail n a b used outputWord : List Bool) :
    advance program
      (stagingCfg .bitSecond none .bit tape B R tail n a b used outputWord D) =
    stagingCfg .launch none .bit tape B R tail n a b used outputWord (D+1) := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram,
    stagingCfg, d, Option.getD_some]
  congr 1
  exact staging_push_d tape B R D tail n a b used outputWord

private theorem run_succ {c d : Config} (hstep : advance program c = d)
    (n : Nat) : run (n+1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, hstep]

private theorem run_add {c d : Config} {m : Nat} (hr : run m c = d)
    (n : Nat) : run (m+n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at hr ⊢
  rw [hr]

theorem ticket_preparation (tape : List Bool) (B R n : Nat)
    (tail a b outputWord : List Bool) :
    ∃ t ≤ 2*n+4,
      run t (stagingCfg .route none .ticket tape B R
        tail (List.replicate n true) a b [] outputWord 0) =
      ⟨some (.inl (BitMachineRawSequence.leftLabel
          LoadedTicketMachine.loaderStartLabel)),
        (drawInitialControl, (none, some .ticket)),
        stagingBank tape B R tail (List.replicate n true) a b
          [] outputWord n⟩ := by
  obtain ⟨tc,htc,hrc⟩ := copy_ticket_run tape B R n tail a b outputWord
  refine ⟨tc+2, by omega, ?_⟩
  rw [show tc+2 = (tc+1)+1 by omega,
    run_succ (route_ticket tape B R tail (List.replicate n true) a b outputWord)
      (tc+1), run_add hrc 1,
    run_succ (launch .ticket tape B R n tail (List.replicate n true) a b outputWord) 0]
  rfl

theorem branch_preparation (tape : List Bool) (B R n : Nat)
    (tail a b outputWord : List Bool) :
    ∃ t ≤ 2*n+4,
      run t (stagingCfg .route none .branch3 tape B R
        tail (List.replicate n true) a b [] outputWord 0) =
      ⟨some (.inl (BitMachineRawSequence.leftLabel
          LoadedTicketMachine.loaderStartLabel)),
        (drawInitialControl, (none, some .branch3)),
        stagingBank tape B R tail (List.replicate n true) a b
          [] outputWord n⟩ := by
  obtain ⟨tc,htc,hrc⟩ := copy_branch_run tape B R n tail a b outputWord
  refine ⟨tc+2, by omega, ?_⟩
  rw [show tc+2 = (tc+1)+1 by omega,
    run_succ (route_branch tape B R tail (List.replicate n true) a b outputWord)
      (tc+1), run_add hrc 1,
    run_succ (launch .branch3 tape B R n tail (List.replicate n true) a b outputWord) 0]
  rfl

theorem bit_preparation (tape : List Bool) (B R : Nat)
    (tail outputWord : List Bool) :
    run 4 (stagingCfg .route none .bit tape B R
      tail [] [] [] [] outputWord 0) =
      ⟨some (.inl (BitMachineRawSequence.leftLabel
          LoadedTicketMachine.loaderStartLabel)),
        (drawInitialControl, (none, some .bit)),
        stagingBank tape B R tail [] [] [] [] outputWord 2⟩ := by
  rw [show (4 : Nat) = 3+1 by omega,
    run_succ (route_bit tape B R tail [] [] [] outputWord) 3,
    run_succ (bit_first_step tape B R 0 tail [] [] [] [] outputWord) 2,
    run_succ (bit_second_step tape B R 1 tail [] [] [] [] outputWord) 1,
    run_succ (launch .bit tape B R 2 tail [] [] [] outputWord) 0]
  rfl

private theorem header_bank_eq (tape : List Bool) (B R : Nat)
    (tail n a b outputWord : List Bool) :
    BitMachineStackEmbedding.bank headerSlot
      (foreignBank outputWord 0 B R tape)
      (CodeHeaderMachine.contents tail n a b [] [] []) =
    stagingBank tape B R tail n a b [] outputWord 0 := by
  funext k
  cases k with
  | inl k =>
      rw [BitMachineStackEmbedding.bank_outside]
      · rfl
      · rintro ⟨i,hk⟩
        simp [headerSlot] at hk
  | inr k =>
      cases k with
      | inl i =>
          rw [← show headerSlot i = (.inr (.inl i) : Stack) by rfl,
            BitMachineStackEmbedding.bank_at]
          rfl
      | inr i =>
          rw [BitMachineStackEmbedding.bank_outside]
          · rfl
          · rintro ⟨j,hk⟩
            simp [headerSlot] at hk

/-- The full seven-stack header parser executes before the draw preparation.
All random/public/output banks are framed and unchanged by parsing. -/
theorem parsed_header (c : Code) (rest outputWord tape : List Bool)
    (B R : Nat) (hword : CodeHeaderMachine.headerWord c = []) :
    ∃ t ≤ CodeHeaderMachine.headerCost c,
      run t (start (encodeCode c ++ rest) outputWord tape B R) =
      stagingCfg .route none (CodeHeaderMachine.headerKind c) tape B R
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c)
        (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) [] outputWord 0 := by
  let input := encodeCode c ++ rest
  let S := CodeHeaderMachine.initial input
  have hc := CodeHeaderMachine.run_header c rest
  have hh : (((advance CodeHeaderMachine.program)^[CodeHeaderMachine.headerCost c])
      S).l = none := by
    rw [← CodeHeaderMachine.run, hc]
    rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    headerSlot (foreignBank outputWord 0 B R tape)
    (fun l => .inr (.inl l))
    (fun v => (drawInitialControl, v)) Prod.snd
    (by intro v; rfl) (some (.inr (.inr .route)))
    CodeHeaderMachine.program program (by intro l; rfl)
    S (CodeHeaderMachine.headerCost c) hh
  rw [← CodeHeaderMachine.run, hc] at hr
  refine ⟨t,ht,?_⟩
  rw [hword] at hr
  simpa [run, start, startBank, input, S, CodeHeaderMachine.initial,
    CodeHeaderMachine.cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    stagingCfg, header_bank_eq] using hr

def rightBank (tail n a b outputWord : List Bool) :
    (Fin 7 ⊕ Fin 1) → List Bool :=
  Sum.elim (CodeHeaderMachine.contents tail n a b [] [] [])
    (fun _ => outputWord)

private theorem loaded_from_launch (D B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind)
    (tail n a b outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ LoadedTicketMachine.loaderBound D B R +
        LoadedTicketMachine.ticketBound D B R + 1 ∧
      run t
        ⟨some (.inl (BitMachineRawSequence.leftLabel
            LoadedTicketMachine.loaderStartLabel)),
          (drawInitialControl, (none, some kind)),
          stagingBank (RecursiveSamplingTape.writeTape B R (N+1) tape).val
            B R tail n a b [] outputWord D⟩ =
        ⟨none,
          ((LoadedTicketMachine.loaderStartControl,
              ((TicketWordScratch.drawInitial, ()),
                some (CappedSampler.runWideBits D B R hB tape.1).isSome)),
            (none, some kind)),
          Sum.elim
            (LoadedTicketMachine.outputBank
              (RecursiveSamplingTape.writeTape B R (N+1) tape).val
              (RecursiveSamplingTape.writeTape B R N tape.2).val
              D B R F (LoadedTicketMachine.resultWord D B R N hB tape))
            (rightBank tail n a b outputWord)⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  let suffix := (RecursiveSamplingTape.writeTape B R N tape.2).val
  obtain ⟨td,F,htd,hrd⟩ :=
    LoadedTicketMachine.loaded_source_ticket D B R N hD hB tape
  have hh : (((advance LoadedTicketMachine.program)^[td])
      (LoadedTicketMachine.start input D B R)).l = none := by
    rw [← LoadedTicketMachine.run, hrd]
  obtain ⟨t,ht,hr⟩ := BitMachineSubroutine.lift_outputs
    LoadedTicketMachine.program program none (by intro l; rfl)
    (none, some kind) (rightBank tail n a b outputWord)
    (LoadedTicketMachine.start input D B R) td hh
  rw [← LoadedTicketMachine.run, hrd] at hr
  refine ⟨t,F,ht.trans htd,?_⟩
  simpa [run, input, suffix, stagingBank, rightBank,
    draw_start_bank,
    BitMachineComposition.liftCfg, drawInitialControl] using hr

noncomputable def resultCfg (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind)
    (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) : Config :=
  ⟨none,
    ((LoadedTicketMachine.loaderStartControl,
        ((TicketWordScratch.drawInitial, ()),
          some (CappedSampler.runWideBits D B R hB tape.1).isSome)),
      (none, some kind)),
    Sum.elim
      (LoadedTicketMachine.outputBank
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val
        (RecursiveSamplingTape.writeTape B R N tape.2).val
        D B R F (LoadedTicketMachine.resultWord D B R N hB tape))
      (rightBank tail n a b outputWord)⟩

/-- Reusable entry point for a physically parsed positive ticket header. -/
theorem prepared_ticket (n B R N : Nat) (hn : 0 < n)
    (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (tail a b outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ (2*n+4) + LoadedTicketMachine.loaderBound n B R +
        LoadedTicketMachine.ticketBound n B R + 1 ∧
      run t (stagingCfg .route none .ticket
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R
        tail (List.replicate n true) a b [] outputWord 0) =
      resultCfg n B R N hB tape .ticket tail (List.replicate n true)
        a b outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨tp,htp,hrp⟩ := ticket_preparation input B R n tail a b outputWord
  obtain ⟨td,F,htd,hrd⟩ := loaded_from_launch n B R N hn hB tape
    .ticket tail (List.replicate n true) a b outputWord
  refine ⟨tp+td,F,by omega,?_⟩
  rw [run_add hrp td]
  simpa [resultCfg, input] using hrd

/-- Reusable entry point retaining both unary branch cuts on header slots 2/3. -/
theorem prepared_branch (n B R N : Nat) (hn : 0 < n)
    (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (tail a b outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ (2*n+4) + LoadedTicketMachine.loaderBound n B R +
        LoadedTicketMachine.ticketBound n B R + 1 ∧
      run t (stagingCfg .route none .branch3
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R
        tail (List.replicate n true) a b [] outputWord 0) =
      resultCfg n B R N hB tape .branch3 tail (List.replicate n true)
        a b outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨tp,htp,hrp⟩ := branch_preparation input B R n tail a b outputWord
  obtain ⟨td,F,htd,hrd⟩ := loaded_from_launch n B R N hn hB tape
    .branch3 tail (List.replicate n true) a b outputWord
  refine ⟨tp+td,F,by omega,?_⟩
  rw [run_add hrp td]
  simpa [resultCfg, input] using hrd

/-- The bit constructor physically installs its fixed denominator 2. -/
theorem prepared_bit (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (tail outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ 4 + LoadedTicketMachine.loaderBound 2 B R +
        LoadedTicketMachine.ticketBound 2 B R + 1 ∧
      run t (stagingCfg .route none .bit
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R
        tail [] [] [] [] outputWord 0) =
      resultCfg 2 B R N hB tape .bit tail [] [] [] outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  have hp := bit_preparation input B R tail outputWord
  obtain ⟨td,F,htd,hrd⟩ := loaded_from_launch 2 B R N (by decide) hB tape
    .bit tail [] [] [] outputWord
  refine ⟨4+td,F,by omega,?_⟩
  rw [run_add hp td]
  simpa [resultCfg, input] using hrd

theorem encoded_ticket (n B R N : Nat) (hn : 0 < n)
    (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (rest outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ (n+5) + (2*n+4) + LoadedTicketMachine.loaderBound n B R +
        LoadedTicketMachine.ticketBound n B R + 1 ∧
      run t (start (encodeCode (.ticket n) ++ rest) outputWord
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
      resultCfg n B R N hB tape .ticket rest (List.replicate n true)
        [] [] outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨th,hth,hrh⟩ :=
    parsed_header (.ticket n) rest outputWord input B R rfl
  obtain ⟨td,F,htd,hrd⟩ :=
    prepared_ticket n B R N hn hB tape rest [] [] outputWord
  refine ⟨th+td,F,?_,?_⟩
  · simp only [CodeHeaderMachine.headerCost] at hth
    omega
  · rw [run_add hrh td]
    simpa [CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, input] using hrd

theorem encoded_branch (n a b B R N : Nat) (hn : 0 < n)
    (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (first second third : Code) (rest outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ (n+a+b+7) + (2*n+4) + LoadedTicketMachine.loaderBound n B R +
        LoadedTicketMachine.ticketBound n B R + 1 ∧
      run t (start (encodeCode (.branch3 n a b first second third) ++ rest)
        outputWord (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
      resultCfg n B R N hB tape .branch3
        (encodeCode first ++ encodeCode second ++ encodeCode third ++ rest)
        (List.replicate n true) (List.replicate a true) (List.replicate b true)
        outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  let tail := encodeCode first ++ encodeCode second ++ encodeCode third ++ rest
  obtain ⟨th,hth,hrh⟩ :=
    parsed_header (.branch3 n a b first second third)
      rest outputWord input B R rfl
  obtain ⟨td,F,htd,hrd⟩ :=
    prepared_branch n B R N hn hB tape tail
      (List.replicate a true) (List.replicate b true) outputWord
  refine ⟨th+td,F,?_,?_⟩
  · simp only [CodeHeaderMachine.headerCost] at hth
    omega
  · rw [run_add hrh td]
    simpa [CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, tail, input] using hrd

theorem encoded_bit (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (rest outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ 4 + 4 + LoadedTicketMachine.loaderBound 2 B R +
        LoadedTicketMachine.ticketBound 2 B R + 1 ∧
      run t (start (encodeCode .bit ++ rest) outputWord
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
      resultCfg 2 B R N hB tape .bit rest [] [] [] outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨th,hth,hrh⟩ := parsed_header .bit rest outputWord input B R rfl
  obtain ⟨td,F,htd,hrd⟩ := prepared_bit B R N hB tape rest outputWord
  refine ⟨th+td,F,?_,?_⟩
  · simp only [CodeHeaderMachine.headerCost] at hth
    omega
  · rw [run_add hrh td]
    simpa [CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, input] using hrd

inductive DrawHead : Code → Prop where
  | ticket (n : Nat) (hn : 0 < n) : DrawHead (.ticket n)
  | bit : DrawHead .bit
  | branch3 (n a b : Nat) (first second third : Code) (hn : 0 < n) :
      DrawHead (.branch3 n a b first second third)

def denominator : Code → Nat
  | .ticket n => n
  | .bit => 2
  | .branch3 n _ _ _ _ _ => n
  | _ => 0

def stagingCost : Code → Nat
  | .ticket n => 2*n+4
  | .bit => 4
  | .branch3 n _ _ _ _ _ => 2*n+4
  | _ => 0

/-- A single finite-control machine covers all three valid draw-headed
constructors. The constructor tag and sampler success bit both remain in
the terminal finite control; the final equation names every ambient stack. -/
theorem encoded_draw_head (c : Code) (hc : DrawHead c)
    (B R N : Nat) (hB : Nat.clog 2 (denominator c) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (rest outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ CodeHeaderMachine.headerCost c + stagingCost c +
        LoadedTicketMachine.loaderBound (denominator c) B R +
        LoadedTicketMachine.ticketBound (denominator c) B R + 1 ∧
      run t (start (encodeCode c ++ rest) outputWord
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
      resultCfg (denominator c) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c)
        (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) outputWord F := by
  cases hc with
  | ticket n hn =>
      obtain ⟨t,F,ht,hr⟩ := encoded_ticket n B R N hn hB tape rest outputWord
      refine ⟨t,F,?_,?_⟩
      · simpa [denominator, stagingCost, CodeHeaderMachine.headerCost]
          using ht
      · simpa [denominator, CodeHeaderMachine.headerKind,
          CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
          CodeHeaderMachine.headerA, CodeHeaderMachine.headerB] using hr

  | bit =>
      obtain ⟨t,F,ht,hr⟩ := encoded_bit B R N hB tape rest outputWord
      refine ⟨t,F,?_,?_⟩
      · simpa [denominator, stagingCost, CodeHeaderMachine.headerCost]
          using ht
      · simpa [denominator, CodeHeaderMachine.headerKind,
          CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
          CodeHeaderMachine.headerA, CodeHeaderMachine.headerB] using hr
  | branch3 n a b first second third hn =>
      obtain ⟨t,F,ht,hr⟩ := encoded_branch n a b B R N hn hB tape
        first second third rest outputWord
      refine ⟨t,F,?_,?_⟩
      · simpa [denominator, stagingCost, CodeHeaderMachine.headerCost]
          using ht
      · simpa [denominator, CodeHeaderMachine.headerKind,
          CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
          CodeHeaderMachine.headerA, CodeHeaderMachine.headerB] using hr

theorem result_header_slots (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk (h 0) = tail ∧
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk (h 1) = n ∧
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk (h 2) = a ∧
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk (h 3) = b ∧
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk output = outputWord := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem result_tape_ticket (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk (d 0) =
      (RecursiveSamplingTape.writeTape B R N tape.2).val ∧
    (resultCfg D B R N hB tape kind tail n a b outputWord F).stk (d 15) =
      LoadedTicketMachine.resultWord D B R N hB tape := by
  constructor
  · exact LoadedTicketMachine.output_tape _ _ _ _ _ _ _
  · exact LoadedTicketMachine.output_ticket _ _ _ _ _ _ _

theorem result_control (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    (resultCfg D B R N hB tape kind tail n a b outputWord F).var.1.2.2 =
      some (CappedSampler.runWideBits D B R hB tape.1).isSome ∧
    (resultCfg D B R N hB tape kind tail n a b outputWord F).var.2.2 =
      some kind := by
  exact ⟨rfl,rfl⟩

theorem result_word_success (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    LoadedTicketMachine.resultWord D B R N hB tape =
      (RecursiveLabelCodecScratch.finCodec D).encode q := by
  simp [LoadedTicketMachine.resultWord, hq]

theorem result_word_failure (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (hq : CappedSampler.runWideBits D B R hB tape.1 = none) :
    LoadedTicketMachine.resultWord D B R N hB tape = [] := by
  simp [LoadedTicketMachine.resultWord, hq]

theorem result_word_zero (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q)
    (hq0 : q.val = 0) :
    LoadedTicketMachine.resultWord D B R N hB tape = [false] := by
  rw [result_word_success D B R N hB tape q hq]
  simp [RecursiveLabelCodecScratch.finCodec, hq0]
#print axioms ticket_preparation
#print axioms branch_preparation
#print axioms bit_preparation
#print axioms parsed_header
#print axioms prepared_ticket
#print axioms prepared_branch
#print axioms prepared_bit
#print axioms encoded_ticket
#print axioms encoded_branch
#print axioms encoded_bit
#print axioms encoded_draw_head
#print axioms result_header_slots
#print axioms result_tape_ticket
#print axioms result_control
#print axioms result_word_success
#print axioms result_word_failure
#print axioms result_word_zero


end
end Paper2.CodeHeaderDraw
