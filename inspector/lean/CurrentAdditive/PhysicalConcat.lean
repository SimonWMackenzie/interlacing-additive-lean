import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

/-! A physical same-input concatenation compiler. Two fixed producers read
copies of one input; literal transfers concatenate their outputs. -/
namespace CurrentAdditive.PhysicalConcat

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

structure Producer where
  machine : BitMachine.Machine
  result : List Bool → List Bool
  clock : List Bool → Nat
  outputs : ∀ x, machine.OutputsWithin x (result x) (clock x)

variable {A B : Producer}

abbrev Stack := Fin A.machine.stackCount ⊕ (Fin B.machine.stackCount ⊕ Fin 3)

inductive Admin where
  | copyScan | copyRestore | startHeader | startBody
  | bodyScan | bodyRestore | headerScan | headerRestore | done
  deriving DecidableEq, Fintype

abbrev Label := (Fin A.machine.labelCount ⊕ Fin B.machine.labelCount) ⊕ Admin
abbrev Control := (Fin A.machine.controlCount × Fin B.machine.controlCount) × Option Bool

def initialSlot : (Stack (A := A) (B := B)) := .inr (.inr 0)
def tempSlot : (Stack (A := A) (B := B)) := .inr (.inr 1)
def outputSlot : (Stack (A := A) (B := B)) := .inr (.inr 2)
noncomputable def headerInput : (Stack (A := A) (B := B)) := .inl A.machine.input
noncomputable def bodyInput : (Stack (A := A) (B := B)) := .inr (.inl B.machine.input)
noncomputable def headerOutput : (Stack (A := A) (B := B)) := .inl A.machine.output
noncomputable def bodyOutput : (Stack (A := A) (B := B)) := .inr (.inl B.machine.output)

noncomputable def headerStack : Fin A.machine.stackCount ↪ (Stack (A := A) (B := B)) :=
  ⟨Sum.inl, Sum.inl_injective⟩
noncomputable def bodyStack : Fin B.machine.stackCount ↪ (Stack (A := A) (B := B)) :=
  ⟨fun k => .inr (.inl k), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩

def headerLabel (l : Fin A.machine.labelCount) : (Label (A := A) (B := B)) := .inl (.inl l)
def bodyLabel (l : Fin B.machine.labelCount) : (Label (A := A) (B := B)) := .inl (.inr l)
def adminLabel (l : Admin) : (Label (A := A) (B := B)) := .inr l

noncomputable def headerControl (v : Fin A.machine.controlCount) : (Control (A := A) (B := B)) :=
  ((v,B.machine.initial),none)
noncomputable def bodyControl (v : Fin B.machine.controlCount) : (Control (A := A) (B := B)) :=
  ((A.machine.initial,v),none)

noncomputable def program : (Label (A := A) (B := B)) →
    TM2.Stmt (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))
  | .inl (.inl l) => BitMachineStackEmbedding.stmt (headerStack (A := A) (B := B))
      (headerLabel (A := A) (B := B)) (headerControl (A := A) (B := B)) (fun v => v.1.1)
      (some ((adminLabel (A := A) (B := B)) .startBody)) (A.machine.program l)
  | .inl (.inr l) => BitMachineStackEmbedding.stmt (bodyStack (A := A) (B := B))
      (bodyLabel (A := A) (B := B)) (bodyControl (A := A) (B := B)) (fun v => v.1.2)
      (some ((adminLabel (A := A) (B := B)) .bodyScan)) (B.machine.program l)
  | .inr .copyScan => BitMachineBroadcast.scanStep
      (initialSlot (A := A) (B := B)) (tempSlot (A := A) (B := B)) ((adminLabel (A := A) (B := B)) .copyScan) ((adminLabel (A := A) (B := B)) .copyRestore)
  | .inr .copyRestore => BitMachineBroadcast.restoreStep
      (tempSlot (A := A) (B := B)) [(headerInput (A := A) (B := B)),(bodyInput (A := A) (B := B))] ((adminLabel (A := A) (B := B)) .copyRestore)
        ((adminLabel (A := A) (B := B)) .startHeader)
  | .inr .startHeader => load (fun _ => (headerControl (A := A) (B := B)) A.machine.initial)
      (goto (fun _ => (headerLabel (A := A) (B := B)) A.machine.start))
  | .inr .startBody => load (fun _ => (bodyControl (A := A) (B := B)) B.machine.initial)
      (goto (fun _ => (bodyLabel (A := A) (B := B)) B.machine.start))
  | .inr .bodyScan => BitMachineBroadcast.scanStep
      (bodyOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) ((adminLabel (A := A) (B := B)) .bodyScan) ((adminLabel (A := A) (B := B)) .bodyRestore)
  | .inr .bodyRestore => BitMachineBroadcast.restoreStep
      (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))] ((adminLabel (A := A) (B := B)) .bodyRestore) ((adminLabel (A := A) (B := B)) .headerScan)
  | .inr .headerScan => BitMachineBroadcast.scanStep
      (headerOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) ((adminLabel (A := A) (B := B)) .headerScan) ((adminLabel (A := A) (B := B)) .headerRestore)
  | .inr .headerRestore => BitMachineBroadcast.restoreStep
      (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))] ((adminLabel (A := A) (B := B)) .headerRestore) ((adminLabel (A := A) (B := B)) .done)
  | .inr .done => halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite (initialSlot (A := A) (B := B)) (outputSlot (A := A) (B := B)) ((adminLabel (A := A) (B := B)) .copyScan)
    ((A.machine.initial,B.machine.initial),none) (program (A := A) (B := B))

def output (packet : List Bool) : List Bool :=
  A.result packet ++ B.result packet

noncomputable def clock (packet : List Bool) : Nat :=
  2*(packet).length+2 + 1 +
  A.clock packet + 1 +
  B.clock packet +
  2*(B.result packet).length+2 +
  2*(A.result packet).length+2 + 1

private noncomputable def initialBank (x : List Bool) : (Stack (A := A) (B := B)) → List Bool :=
  fun k => if k = (initialSlot (A := A) (B := B)) then x else []

private noncomputable def copyBank (x : List Bool) : (Stack (A := A) (B := B)) → List Bool :=
  BitMachineBroadcast.copied (initialSlot (A := A) (B := B)) (tempSlot (A := A) (B := B))
    [(headerInput (A := A) (B := B)),(bodyInput (A := A) (B := B))] x ((initialBank (A := A) (B := B)) x)

private theorem initial_eq (x : List Bool) :
    rawInit (initialSlot (A := A) (B := B)) ((adminLabel (A := A) (B := B)) .copyScan)
      ((A.machine.initial,B.machine.initial),none) x =
    (⟨some ((adminLabel (A := A) (B := B)) .copyScan), ((A.machine.initial,B.machine.initial),none),
      (initialBank (A := A) (B := B)) x⟩ :
      TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) := by
  simp only [rawInit]
  congr 1

private theorem copy_input (x : List Bool) :
    ((copyBank (A := A) (B := B)) x) (headerInput (A := A) (B := B)) = x ∧
    ((copyBank (A := A) (B := B)) x) (bodyInput (A := A) (B := B)) = x ∧
    ((copyBank (A := A) (B := B)) x) (tempSlot (A := A) (B := B)) = [] ∧
    ((copyBank (A := A) (B := B)) x) (outputSlot (A := A) (B := B)) = [] := by
  simp [copyBank, BitMachineBroadcast.copied, initialBank,
    initialSlot, tempSlot, outputSlot, headerInput, bodyInput]

private theorem copy_phase (x : List Bool) :
    ((advance (program (A := A) (B := B)))^[2*x.length+2])
      (rawInit (initialSlot (A := A) (B := B)) ((adminLabel (A := A) (B := B)) .copyScan)
        ((A.machine.initial,B.machine.initial),none) x) =
      ⟨some ((adminLabel (A := A) (B := B)) .startHeader), ((A.machine.initial,B.machine.initial),none),
        (copyBank (A := A) (B := B)) x⟩ := by
  rw [(initial_eq (A := A) (B := B))]
  have h := BitMachineBroadcast.broadcast_run (program (A := A) (B := B)) (initialSlot (A := A) (B := B)) (tempSlot (A := A) (B := B))
    (by simp [initialSlot, tempSlot]) [(headerInput (A := A) (B := B)),(bodyInput (A := A) (B := B))]
    (by simp [headerInput, bodyInput])
    (by simp [initialSlot, headerInput, bodyInput])
    (by simp [tempSlot, headerInput, bodyInput])
    ((adminLabel (A := A) (B := B)) .copyScan) ((adminLabel (A := A) (B := B)) .copyRestore)
    ((adminLabel (A := A) (B := B)) .startHeader) (by rfl) (by rfl)
    (A.machine.initial,B.machine.initial) none x ((initialBank (A := A) (B := B)) x) (by simp [initialBank])
    (by simp [initialBank, tempSlot, initialSlot])
  exact h

private theorem header_initial (x : List Bool) :
    BitMachineStackEmbedding.bank (headerStack (A := A) (B := B)) ((copyBank (A := A) (B := B)) x)
      (A.machine.init x).stk = (copyBank (A := A) (B := B)) x := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  by_cases hk : k = A.machine.input
  · subst k
    simpa [headerStack, headerInput, BitMachine.Machine.init]
      using ((copy_input (A := A) (B := B)) x).1.symm
  · simp [headerStack, BitMachine.Machine.init, copyBank,
      BitMachineBroadcast.copied, initialBank,
      initialSlot, tempSlot, headerInput, bodyInput, hk]

private theorem start_header (x : List Bool) :
    advance (program (A := A) (B := B))
      (⟨some ((adminLabel (A := A) (B := B)) .startHeader), ((A.machine.initial,B.machine.initial),none),
        (copyBank (A := A) (B := B)) x⟩ : TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((headerLabel (A := A) (B := B)) A.machine.start), (headerControl (A := A) (B := B)) A.machine.initial, (copyBank (A := A) (B := B)) x⟩ := by
  rfl

private noncomputable def headerBank (x : List Bool) (t : Nat) :
    (Stack (A := A) (B := B)) → List Bool :=
  BitMachineStackEmbedding.bank (headerStack (A := A) (B := B)) ((copyBank (A := A) (B := B)) x)
    (A.machine.run t (A.machine.init x)).stk

private theorem header_phase (packet : List Bool) :
    ∃ t ≤ A.clock packet,
      ((advance (program (A := A) (B := B)))^[t])
        (⟨some ((headerLabel (A := A) (B := B)) A.machine.start), (headerControl (A := A) (B := B)) A.machine.initial,
          (copyBank (A := A) (B := B)) (packet)⟩ :
          TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((adminLabel (A := A) (B := B)) .startBody),
        (headerControl (A := A) (B := B)) (A.machine.run (A.clock packet)
          (A.machine.init (packet))).var,
        (headerBank (A := A) (B := B)) (packet)
          (A.clock packet)⟩ := by
  let x := packet
  let t := A.clock packet
  have hh := (BitMachine.outputsWithin_at_bound A.machine
    (A.outputs packet)).1
  have h := BitMachineStackEmbedding.outputs (headerStack (A := A) (B := B)) ((copyBank (A := A) (B := B)) x)
    (headerLabel (A := A) (B := B)) (headerControl (A := A) (B := B)) (fun v : (Control (A := A) (B := B)) => v.1.1)
    (by intro v; rfl) (some ((adminLabel (A := A) (B := B)) .startBody))
    A.machine.program (program (A := A) (B := B)) (by intro l; rfl) (A.machine.init x) t hh
  obtain ⟨u, hu, hr⟩ := h
  refine ⟨u, hu, ?_⟩
  have hstart : BitMachineStackEmbedding.cfg (headerStack (A := A) (B := B)) ((copyBank (A := A) (B := B)) x)
      (headerLabel (A := A) (B := B)) (headerControl (A := A) (B := B)) (some ((adminLabel (A := A) (B := B)) .startBody))
      (A.machine.init x) =
      (⟨some ((headerLabel (A := A) (B := B)) A.machine.start), (headerControl (A := A) (B := B)) A.machine.initial,
        (copyBank (A := A) (B := B)) x⟩ : TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [(header_initial (A := A) (B := B))]
    rfl
  rw [hstart] at hr
  have hrun : ((advance A.machine.program)^[t]) (A.machine.init x) =
      A.machine.run t (A.machine.init x) := rfl
  rw [hrun] at hr
  change (A.machine.run t (A.machine.init x)).l = none at hh
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    headerBank, hh] using hr

private theorem header_bank_output (packet : List Bool) :
    (headerBank (A := A) (B := B)) (packet)
      (A.clock packet) (headerOutput (A := A) (B := B)) =
      A.result packet := by
  have hout := (BitMachine.outputsWithin_at_bound A.machine
    (A.outputs packet)).2
  simpa [headerBank, headerOutput, headerStack] using
    (BitMachineStackEmbedding.bank_at (headerStack (A := A) (B := B))
      ((copyBank (A := A) (B := B)) (packet))
      (A.machine.run (A.clock packet)
        (A.machine.init (packet))).stk A.machine.output).trans hout

private theorem header_bank_outside (x : List Bool) (t : Nat)
    (k : Fin B.machine.stackCount) :
    (headerBank (A := A) (B := B)) x t ((bodyStack (A := A) (B := B)) k) = (copyBank (A := A) (B := B)) x ((bodyStack (A := A) (B := B)) k) := by
  unfold headerBank
  apply BitMachineStackEmbedding.bank_outside
  intro ⟨j,hj⟩
  cases hj

private theorem header_bank_body_initial (x : List Bool) (t : Nat) :
    BitMachineStackEmbedding.bank (bodyStack (A := A) (B := B)) ((headerBank (A := A) (B := B)) x t)
      (B.machine.init x).stk = (headerBank (A := A) (B := B)) x t := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  rw [(header_bank_outside (A := A) (B := B))]
  by_cases hk : k = B.machine.input
  · subst k
    simpa [bodyStack, bodyInput, BitMachine.Machine.init]
      using ((copy_input (A := A) (B := B)) x).2.1.symm
  · simp [bodyStack, BitMachine.Machine.init, copyBank,
      BitMachineBroadcast.copied, initialBank,
      initialSlot, tempSlot, headerInput, bodyInput, hk]

private theorem start_body (x : List Bool) (th : Nat) :
    advance (program (A := A) (B := B))
      (⟨some ((adminLabel (A := A) (B := B)) .startBody),
        (headerControl (A := A) (B := B)) (A.machine.run th (A.machine.init x)).var,
        (headerBank (A := A) (B := B)) x th⟩ :
        TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((bodyLabel (A := A) (B := B)) B.machine.start), (bodyControl (A := A) (B := B)) B.machine.initial,
        (headerBank (A := A) (B := B)) x th⟩ := by
  rfl

private noncomputable def bodyBank (x : List Bool) (th tb : Nat) :
    (Stack (A := A) (B := B)) → List Bool :=
  BitMachineStackEmbedding.bank (bodyStack (A := A) (B := B)) ((headerBank (A := A) (B := B)) x th)
    (B.machine.run tb (B.machine.init x)).stk

private theorem body_phase (packet : List Bool) :
    ∃ t ≤ B.clock packet,
      ((advance (program (A := A) (B := B)))^[t])
        (⟨some ((bodyLabel (A := A) (B := B)) B.machine.start), (bodyControl (A := A) (B := B)) B.machine.initial,
          (headerBank (A := A) (B := B)) (packet)
            (A.clock packet)⟩ :
          TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((adminLabel (A := A) (B := B)) .bodyScan),
        (bodyControl (A := A) (B := B)) (B.machine.run (B.clock packet)
          (B.machine.init (packet))).var,
        (bodyBank (A := A) (B := B)) (packet)
          (A.clock packet)
          (B.clock packet)⟩ := by
  let x := packet
  let th := A.clock packet
  let tb := B.clock packet
  have hb := (BitMachine.outputsWithin_at_bound B.machine
    (B.outputs packet)).1
  have h := BitMachineStackEmbedding.outputs (bodyStack (A := A) (B := B)) ((headerBank (A := A) (B := B)) x th)
    (bodyLabel (A := A) (B := B)) (bodyControl (A := A) (B := B)) (fun v : (Control (A := A) (B := B)) => v.1.2)
    (by intro v; rfl) (some ((adminLabel (A := A) (B := B)) .bodyScan))
    B.machine.program (program (A := A) (B := B)) (by intro l; rfl) (B.machine.init x) tb hb
  obtain ⟨u, hu, hr⟩ := h
  refine ⟨u, hu, ?_⟩
  have hstart : BitMachineStackEmbedding.cfg (bodyStack (A := A) (B := B)) ((headerBank (A := A) (B := B)) x th)
      (bodyLabel (A := A) (B := B)) (bodyControl (A := A) (B := B)) (some ((adminLabel (A := A) (B := B)) .bodyScan))
      (B.machine.init x) =
      (⟨some ((bodyLabel (A := A) (B := B)) B.machine.start), (bodyControl (A := A) (B := B)) B.machine.initial,
        (headerBank (A := A) (B := B)) x th⟩ : TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [(header_bank_body_initial (A := A) (B := B))]
    rfl
  rw [hstart] at hr
  have hrun : ((advance B.machine.program)^[tb]) (B.machine.init x) =
      B.machine.run tb (B.machine.init x) := rfl
  rw [hrun] at hr
  change (B.machine.run tb (B.machine.init x)).l = none at hb
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    bodyBank, hb] using hr

private theorem body_bank_output (packet : List Bool) :
    (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (bodyOutput (A := A) (B := B)) =
      B.result packet := by
  have hout := (BitMachine.outputsWithin_at_bound B.machine
    (B.outputs packet)).2
  simpa [bodyBank, bodyOutput, bodyStack] using
    (BitMachineStackEmbedding.bank_at (bodyStack (A := A) (B := B))
      ((headerBank (A := A) (B := B)) (packet)
        (A.clock packet))
      (B.machine.run (B.clock packet)
        (B.machine.init (packet))).stk B.machine.output).trans hout

private theorem body_bank_header (packet : List Bool) :
    (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (headerOutput (A := A) (B := B)) =
      A.result packet := by
  rw [show (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (headerOutput (A := A) (B := B)) =
      (headerBank (A := A) (B := B)) (packet)
        (A.clock packet) (headerOutput (A := A) (B := B)) by
    unfold bodyBank
    apply BitMachineStackEmbedding.bank_outside
    intro ⟨k,hk⟩
    cases hk]
  exact (header_bank_output (A := A) (B := B)) packet

private theorem body_bank_aux (packet : List Bool) :
    (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (tempSlot (A := A) (B := B)) = [] ∧
    (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (outputSlot (A := A) (B := B)) = [] := by
  constructor
  · rw [show (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (tempSlot (A := A) (B := B)) =
      (headerBank (A := A) (B := B)) (packet)
        (A.clock packet) (tempSlot (A := A) (B := B)) by
      unfold bodyBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    rw [show (headerBank (A := A) (B := B)) (packet)
      (A.clock packet) (tempSlot (A := A) (B := B)) =
      (copyBank (A := A) (B := B)) (packet) (tempSlot (A := A) (B := B)) by
      unfold headerBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    exact ((copy_input (A := A) (B := B)) _).2.2.1
  · rw [show (bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet) (outputSlot (A := A) (B := B)) =
      (headerBank (A := A) (B := B)) (packet)
        (A.clock packet) (outputSlot (A := A) (B := B)) by
      unfold bodyBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    rw [show (headerBank (A := A) (B := B)) (packet)
      (A.clock packet) (outputSlot (A := A) (B := B)) =
      (copyBank (A := A) (B := B)) (packet) (outputSlot (A := A) (B := B)) by
      unfold headerBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    exact ((copy_input (A := A) (B := B)) _).2.2.2

private noncomputable def bodyCopied (packet : List Bool) :
    (Stack (A := A) (B := B)) → List Bool :=
  BitMachineBroadcast.copied (bodyOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))]
    (B.result packet)
    ((bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet))

private theorem body_broadcast (packet : List Bool) :
    ((advance (program (A := A) (B := B)))^[2*(B.result packet).length+2])
      (⟨some ((adminLabel (A := A) (B := B)) .bodyScan),
        (bodyControl (A := A) (B := B)) (B.machine.run (B.clock packet)
          (B.machine.init (packet))).var,
        (bodyBank (A := A) (B := B)) (packet)
          (A.clock packet)
          (B.clock packet)⟩ :
          TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((adminLabel (A := A) (B := B)) .headerScan),
        (bodyControl (A := A) (B := B)) (B.machine.run (B.clock packet)
          (B.machine.init (packet))).var,
        (bodyCopied (A := A) (B := B)) packet⟩ := by
  have h := BitMachineBroadcast.broadcast_run (program (A := A) (B := B)) (bodyOutput (A := A) (B := B)) (tempSlot (A := A) (B := B))
    (by simp [bodyOutput, tempSlot]) [(outputSlot (A := A) (B := B))]
    (by simp)
    (by simp [bodyOutput, outputSlot])
    (by simp [tempSlot, outputSlot])
    ((adminLabel (A := A) (B := B)) .bodyScan) ((adminLabel (A := A) (B := B)) .bodyRestore)
    ((adminLabel (A := A) (B := B)) .headerScan) (by rfl) (by rfl)
    (A.machine.initial,
      (B.machine.run (B.clock packet)
        (B.machine.init (packet))).var)
    none (B.result packet)
    ((bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet))
    ((body_bank_output (A := A) (B := B)) packet) ((body_bank_aux (A := A) (B := B)) packet).1
  simpa only [bodyControl, bodyCopied,
    BitMachineBroadcast.run] using h

private theorem body_copied_output (packet : List Bool) :
    (bodyCopied (A := A) (B := B)) packet (outputSlot (A := A) (B := B)) = B.result packet := by
  unfold bodyCopied
  rw [BitMachineBroadcast.copied_target (bodyOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))]
    (B.result packet)
    ((bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet))
    (by simp [bodyOutput, outputSlot])
    (by simp [tempSlot, outputSlot]) (outputSlot (A := A) (B := B)) (by simp)]
  simp [(body_bank_aux packet).2]

private theorem body_copied_header (packet : List Bool) :
    (bodyCopied (A := A) (B := B)) packet (headerOutput (A := A) (B := B)) = A.result packet := by
  unfold bodyCopied
  rw [BitMachineBroadcast.copied_other (bodyOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))]
    (B.result packet)
    ((bodyBank (A := A) (B := B)) (packet)
      (A.clock packet)
      (B.clock packet)) (headerOutput (A := A) (B := B))
    (by simp [headerOutput, bodyOutput])
    (by simp [headerOutput, tempSlot])
    (by simp [headerOutput, outputSlot])]
  exact (body_bank_header (A := A) (B := B)) packet

private theorem body_copied_temp (packet : List Bool) :
    (bodyCopied (A := A) (B := B)) packet (tempSlot (A := A) (B := B)) = [] := by
  exact BitMachineBroadcast.copied_temp (bodyOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))]
    (B.result packet) _

private noncomputable def joinedBank (packet : List Bool) :
    (Stack (A := A) (B := B)) → List Bool :=
  BitMachineBroadcast.copied (headerOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))]
    (A.result packet) ((bodyCopied (A := A) (B := B)) packet)

private theorem header_broadcast (packet : List Bool) :
    ((advance (program (A := A) (B := B)))^[2*(A.result packet).length+2])
      (⟨some ((adminLabel (A := A) (B := B)) .headerScan),
        (bodyControl (A := A) (B := B)) (B.machine.run (B.clock packet)
          (B.machine.init (packet))).var,
        (bodyCopied (A := A) (B := B)) packet⟩ :
          TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((adminLabel (A := A) (B := B)) .done),
        (bodyControl (A := A) (B := B)) (B.machine.run (B.clock packet)
          (B.machine.init (packet))).var,
        (joinedBank (A := A) (B := B)) packet⟩ := by
  have h := BitMachineBroadcast.broadcast_run (program (A := A) (B := B)) (headerOutput (A := A) (B := B)) (tempSlot (A := A) (B := B))
    (by simp [headerOutput, tempSlot]) [(outputSlot (A := A) (B := B))]
    (by simp)
    (by simp [headerOutput, outputSlot])
    (by simp [tempSlot, outputSlot])
    ((adminLabel (A := A) (B := B)) .headerScan) ((adminLabel (A := A) (B := B)) .headerRestore)
    ((adminLabel (A := A) (B := B)) .done) (by rfl) (by rfl)
    (A.machine.initial,
      (B.machine.run (B.clock packet)
        (B.machine.init (packet))).var)
    none (A.result packet) ((bodyCopied (A := A) (B := B)) packet)
    ((body_copied_header (A := A) (B := B)) packet) ((body_copied_temp (A := A) (B := B)) packet)
  simpa only [bodyControl, joinedBank,
    BitMachineBroadcast.run] using h

private theorem joined_output (packet : List Bool) :
    (joinedBank (A := A) (B := B)) packet (outputSlot (A := A) (B := B)) = (output (A := A) (B := B)) packet := by
  unfold joinedBank
  rw [BitMachineBroadcast.copied_target (headerOutput (A := A) (B := B)) (tempSlot (A := A) (B := B)) [(outputSlot (A := A) (B := B))]
    (A.result packet) ((bodyCopied (A := A) (B := B)) packet)
    (by simp [headerOutput, outputSlot])
    (by simp [tempSlot, outputSlot]) (outputSlot (A := A) (B := B)) (by simp)]
  rw [(body_copied_output (A := A) (B := B))]
  rfl

private theorem run_chain
    (c₀ c₁ c₂ : TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B)))
    (a b : Nat)
    (h₁ : ((advance (program (A := A) (B := B)))^[a]) c₀ = c₁)
    (h₂ : ((advance (program (A := A) (B := B)))^[b]) c₁ = c₂) :
    ((advance (program (A := A) (B := B)))^[a+b]) c₀ = c₂ := by
  rw [show a+b=b+a by omega, Function.iterate_add_apply, h₁, h₂]

theorem outputs (packet : List Bool) :
    (machine (A := A) (B := B)).OutputsWithin (packet)
      ((output (A := A) (B := B)) packet) ((clock (A := A) (B := B)) packet) := by
  let x := packet
  let th := A.clock packet
  let tb := B.clock packet
  let u := B.result packet
  let v := A.result packet
  let tc := 2*x.length+2
  obtain ⟨qh,hqh,hH⟩ := (header_phase (A := A) (B := B)) packet
  obtain ⟨qb,hqb,hB⟩ := (body_phase (A := A) (B := B)) packet
  have h0 := (copy_phase (A := A) (B := B)) x
  have h1 : ((advance (program (A := A) (B := B)))^[1])
      (⟨some ((adminLabel (A := A) (B := B)) .startHeader), ((A.machine.initial,B.machine.initial),none),
        (copyBank (A := A) (B := B)) x⟩ : TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((headerLabel (A := A) (B := B)) A.machine.start), (headerControl (A := A) (B := B)) A.machine.initial, (copyBank (A := A) (B := B)) x⟩ :=
    (start_header (A := A) (B := B)) x
  have h2 : ((advance (program (A := A) (B := B)))^[1])
      (⟨some ((adminLabel (A := A) (B := B)) .startBody),
        (headerControl (A := A) (B := B)) (A.machine.run th (A.machine.init x)).var,
        (headerBank (A := A) (B := B)) x th⟩ :
        TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨some ((bodyLabel (A := A) (B := B)) B.machine.start), (bodyControl (A := A) (B := B)) B.machine.initial,
        (headerBank (A := A) (B := B)) x th⟩ := (start_body (A := A) (B := B)) x th
  have h3 : ((advance (program (A := A) (B := B)))^[1])
      (⟨some ((adminLabel (A := A) (B := B)) .done),
        (bodyControl (A := A) (B := B)) (B.machine.run tb (B.machine.init x)).var,
        (joinedBank (A := A) (B := B)) packet⟩ :
        TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool) (Label (A := A) (B := B)) (Control (A := A) (B := B))) =
      ⟨none, (bodyControl (A := A) (B := B)) (B.machine.run tb (B.machine.init x)).var,
        (joinedBank (A := A) (B := B)) packet⟩ := by rfl
  have h01 := (run_chain (A := A) (B := B)) _ _ _ tc 1 h0 h1
  have h012 := (run_chain (A := A) (B := B)) _ _ _ (tc+1) qh h01 hH
  have h0123 := (run_chain (A := A) (B := B)) _ _ _ (tc+1+qh) 1 h012 h2
  have h01234 := (run_chain (A := A) (B := B)) _ _ _ (tc+1+qh+1) qb h0123 hB
  have h012345 := (run_chain (A := A) (B := B)) _ _ _ (tc+1+qh+1+qb)
    (2*u.length+2) h01234 ((body_broadcast (A := A) (B := B)) packet)
  have h0123456 := (run_chain (A := A) (B := B)) _ _ _
    (tc+1+qh+1+qb+(2*u.length+2))
    (2*v.length+2) h012345 ((header_broadcast (A := A) (B := B)) packet)
  have hfull := (run_chain (A := A) (B := B)) _ _ _
    (tc+1+qh+1+qb+(2*u.length+2)+(2*v.length+2))
    1 h0123456 h3
  apply outputsWithin_of_raw_run (initialSlot (A := A) (B := B)) (outputSlot (A := A) (B := B))
    ((adminLabel (A := A) (B := B)) .copyScan) ((A.machine.initial,B.machine.initial),none) (program (A := A) (B := B))
    x ((output (A := A) (B := B)) packet)
    (tc+1+qh+1+qb+(2*u.length+2)+(2*v.length+2)+1)
    ((clock (A := A) (B := B)) packet) (by dsimp [clock,tc,u,v,th,tb,x]; omega)
  · simpa only [x] using congrArg TM2.Cfg.l hfull
  · have hout := congrArg (fun c : TM2.Cfg (fun _ : (Stack (A := A) (B := B)) => Bool)
      (Label (A := A) (B := B)) (Control (A := A) (B := B)) => c.stk (outputSlot (A := A) (B := B))) hfull
    simpa [joined_output] using hout


#print axioms outputs
end CurrentAdditive.PhysicalConcat
