import CurrentAdditive.CodeDUpdatedEntryFields
import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
A literal two-pass physical join. The initial list is broadcast to both
submachines. The body is prepended to the output bank, then the freshly
computed header is prepended, giving the canonical compact list bytes.
-/

namespace CurrentAdditive.CodeDUpdatedEntryJoin

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

private noncomputable abbrev H := CodeDUpdatedEntryFields.wordMachine
private noncomputable abbrev B := CodeDUpdatedEntryFields.weightMachine

abbrev Stack := Fin H.stackCount ⊕ (Fin B.stackCount ⊕ Fin 3)

inductive Admin where
  | copyScan | copyRestore | startHeader | startBody
  | bodyScan | bodyRestore | headerScan | headerRestore | done
  deriving DecidableEq, Fintype

abbrev Label := (Fin H.labelCount ⊕ Fin B.labelCount) ⊕ Admin
abbrev Control := (Fin H.controlCount × Fin B.controlCount) × Option Bool

def initialSlot : Stack := .inr (.inr 0)
def tempSlot : Stack := .inr (.inr 1)
def outputSlot : Stack := .inr (.inr 2)
noncomputable def headerInput : Stack := .inl H.input
noncomputable def bodyInput : Stack := .inr (.inl B.input)
noncomputable def headerOutput : Stack := .inl H.output
noncomputable def bodyOutput : Stack := .inr (.inl B.output)

noncomputable def headerStack : Fin H.stackCount ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩
noncomputable def bodyStack : Fin B.stackCount ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩

def headerLabel (l : Fin H.labelCount) : Label := .inl (.inl l)
def bodyLabel (l : Fin B.labelCount) : Label := .inl (.inr l)
def adminLabel (l : Admin) : Label := .inr l

noncomputable def headerControl (v : Fin H.controlCount) : Control :=
  ((v,B.initial),none)
noncomputable def bodyControl (v : Fin B.controlCount) : Control :=
  ((H.initial,v),none)

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl (.inl l) => BitMachineStackEmbedding.stmt headerStack
      headerLabel headerControl (fun v => v.1.1)
      (some (adminLabel .startBody)) (H.program l)
  | .inl (.inr l) => BitMachineStackEmbedding.stmt bodyStack
      bodyLabel bodyControl (fun v => v.1.2)
      (some (adminLabel .bodyScan)) (B.program l)
  | .inr .copyScan => BitMachineBroadcast.scanStep
      initialSlot tempSlot (adminLabel .copyScan) (adminLabel .copyRestore)
  | .inr .copyRestore => BitMachineBroadcast.restoreStep
      tempSlot [headerInput,bodyInput] (adminLabel .copyRestore)
        (adminLabel .startHeader)
  | .inr .startHeader => load (fun _ => headerControl H.initial)
      (goto (fun _ => headerLabel H.start))
  | .inr .startBody => load (fun _ => bodyControl B.initial)
      (goto (fun _ => bodyLabel B.start))
  | .inr .bodyScan => BitMachineBroadcast.scanStep
      bodyOutput tempSlot (adminLabel .bodyScan) (adminLabel .bodyRestore)
  | .inr .bodyRestore => BitMachineBroadcast.restoreStep
      tempSlot [outputSlot] (adminLabel .bodyRestore) (adminLabel .headerScan)
  | .inr .headerScan => BitMachineBroadcast.scanStep
      headerOutput tempSlot (adminLabel .headerScan) (adminLabel .headerRestore)
  | .inr .headerRestore => BitMachineBroadcast.restoreStep
      tempSlot [outputSlot] (adminLabel .headerRestore) (adminLabel .done)
  | .inr .done => halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite initialSlot outputSlot (adminLabel .copyScan)
    ((H.initial,B.initial),none) program

def output (packet : List Bool) : List Bool :=
  CodeDUpdatedEntryFields.wordField packet ++ CodeDUpdatedEntryFields.weightField packet

noncomputable def clock (packet : List Bool) : Nat :=
  2*(packet).length+2 + 1 +
  CodeDUpdatedEntryFields.wordClock packet + 1 +
  CodeDUpdatedEntryFields.weightClock packet +
  2*(CodeDUpdatedEntryFields.weightField packet).length+2 +
  2*(CodeDUpdatedEntryFields.wordField packet).length+2 + 1

private noncomputable def initialBank (x : List Bool) : Stack → List Bool :=
  fun k => if k = initialSlot then x else []

private noncomputable def copyBank (x : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied initialSlot tempSlot
    [headerInput,bodyInput] x (initialBank x)

private theorem initial_eq (x : List Bool) :
    rawInit initialSlot (adminLabel .copyScan)
      ((H.initial,B.initial),none) x =
    (⟨some (adminLabel .copyScan), ((H.initial,B.initial),none),
      initialBank x⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) := by
  simp only [rawInit]
  congr 1

private theorem copy_input (x : List Bool) :
    (copyBank x) headerInput = x ∧
    (copyBank x) bodyInput = x ∧
    (copyBank x) tempSlot = [] ∧
    (copyBank x) outputSlot = [] := by
  simp [copyBank, BitMachineBroadcast.copied, initialBank,
    initialSlot, tempSlot, outputSlot, headerInput, bodyInput]

private theorem copy_phase (x : List Bool) :
    ((advance program)^[2*x.length+2])
      (rawInit initialSlot (adminLabel .copyScan)
        ((H.initial,B.initial),none) x) =
      ⟨some (adminLabel .startHeader), ((H.initial,B.initial),none),
        copyBank x⟩ := by
  rw [initial_eq]
  have h := BitMachineBroadcast.broadcast_run program initialSlot tempSlot
    (by decide) [headerInput,bodyInput]
    (by simp [headerInput, bodyInput])
    (by simp [initialSlot, headerInput, bodyInput])
    (by simp [tempSlot, headerInput, bodyInput])
    (adminLabel .copyScan) (adminLabel .copyRestore)
    (adminLabel .startHeader) (by rfl) (by rfl)
    (H.initial,B.initial) none x (initialBank x) (by simp [initialBank])
    (by simp [initialBank, tempSlot, initialSlot])
  exact h

private theorem header_initial (x : List Bool) :
    BitMachineStackEmbedding.bank headerStack (copyBank x)
      (H.init x).stk = copyBank x := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  by_cases hk : k = H.input
  · subst k
    simpa [headerStack, headerInput, BitMachine.Machine.init]
      using (copy_input x).1.symm
  · simp [headerStack, BitMachine.Machine.init, copyBank,
      BitMachineBroadcast.copied, initialBank,
      initialSlot, tempSlot, headerInput, bodyInput, hk]

private theorem start_header (x : List Bool) :
    advance program
      (⟨some (adminLabel .startHeader), ((H.initial,B.initial),none),
        copyBank x⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (headerLabel H.start), headerControl H.initial, copyBank x⟩ := by
  rfl

private noncomputable def headerBank (x : List Bool) (t : Nat) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank headerStack (copyBank x)
    (H.run t (H.init x)).stk

private theorem header_phase (packet : List Bool) :
    ∃ t ≤ CodeDUpdatedEntryFields.wordClock packet,
      ((advance program)^[t])
        (⟨some (headerLabel H.start), headerControl H.initial,
          copyBank (packet)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (adminLabel .startBody),
        headerControl (H.run (CodeDUpdatedEntryFields.wordClock packet)
          (H.init (packet))).var,
        headerBank (packet)
          (CodeDUpdatedEntryFields.wordClock packet)⟩ := by
  let x := packet
  let t := CodeDUpdatedEntryFields.wordClock packet
  have hh := (BitMachine.outputsWithin_at_bound H
    (CodeDUpdatedEntryFields.word_outputs packet)).1
  have h := BitMachineStackEmbedding.outputs headerStack (copyBank x)
    headerLabel headerControl (fun v : Control => v.1.1)
    (by intro v; rfl) (some (adminLabel .startBody))
    H.program program (by intro l; rfl) (H.init x) t hh
  obtain ⟨u, hu, hr⟩ := h
  refine ⟨u, hu, ?_⟩
  have hstart : BitMachineStackEmbedding.cfg headerStack (copyBank x)
      headerLabel headerControl (some (adminLabel .startBody))
      (H.init x) =
      (⟨some (headerLabel H.start), headerControl H.initial,
        copyBank x⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [header_initial]
    rfl
  rw [hstart] at hr
  have hrun : ((advance H.program)^[t]) (H.init x) =
      H.run t (H.init x) := rfl
  rw [hrun] at hr
  change (H.run t (H.init x)).l = none at hh
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    headerBank, hh] using hr

private theorem header_bank_output (packet : List Bool) :
    headerBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet) headerOutput =
      CodeDUpdatedEntryFields.wordField packet := by
  have hout := (BitMachine.outputsWithin_at_bound H
    (CodeDUpdatedEntryFields.word_outputs packet)).2
  simpa [headerBank, headerOutput, headerStack] using
    (BitMachineStackEmbedding.bank_at headerStack
      (copyBank (packet))
      (H.run (CodeDUpdatedEntryFields.wordClock packet)
        (H.init (packet))).stk H.output).trans hout

private theorem header_bank_outside (x : List Bool) (t : Nat)
    (k : Fin B.stackCount) :
    headerBank x t (bodyStack k) = copyBank x (bodyStack k) := by
  unfold headerBank
  apply BitMachineStackEmbedding.bank_outside
  intro ⟨j,hj⟩
  cases hj

private theorem header_bank_body_initial (x : List Bool) (t : Nat) :
    BitMachineStackEmbedding.bank bodyStack (headerBank x t)
      (B.init x).stk = headerBank x t := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  rw [header_bank_outside]
  by_cases hk : k = B.input
  · subst k
    simpa [bodyStack, bodyInput, BitMachine.Machine.init]
      using (copy_input x).2.1.symm
  · simp [bodyStack, BitMachine.Machine.init, copyBank,
      BitMachineBroadcast.copied, initialBank,
      initialSlot, tempSlot, headerInput, bodyInput, hk]

private theorem start_body (x : List Bool) (th : Nat) :
    advance program
      (⟨some (adminLabel .startBody),
        headerControl (H.run th (H.init x)).var,
        headerBank x th⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (bodyLabel B.start), bodyControl B.initial,
        headerBank x th⟩ := by
  rfl

private noncomputable def bodyBank (x : List Bool) (th tb : Nat) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank bodyStack (headerBank x th)
    (B.run tb (B.init x)).stk

private theorem body_phase (packet : List Bool) :
    ∃ t ≤ CodeDUpdatedEntryFields.weightClock packet,
      ((advance program)^[t])
        (⟨some (bodyLabel B.start), bodyControl B.initial,
          headerBank (packet)
            (CodeDUpdatedEntryFields.wordClock packet)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (adminLabel .bodyScan),
        bodyControl (B.run (CodeDUpdatedEntryFields.weightClock packet)
          (B.init (packet))).var,
        bodyBank (packet)
          (CodeDUpdatedEntryFields.wordClock packet)
          (CodeDUpdatedEntryFields.weightClock packet)⟩ := by
  let x := packet
  let th := CodeDUpdatedEntryFields.wordClock packet
  let tb := CodeDUpdatedEntryFields.weightClock packet
  have hb := (BitMachine.outputsWithin_at_bound B
    (CodeDUpdatedEntryFields.weight_outputs packet)).1
  have h := BitMachineStackEmbedding.outputs bodyStack (headerBank x th)
    bodyLabel bodyControl (fun v : Control => v.1.2)
    (by intro v; rfl) (some (adminLabel .bodyScan))
    B.program program (by intro l; rfl) (B.init x) tb hb
  obtain ⟨u, hu, hr⟩ := h
  refine ⟨u, hu, ?_⟩
  have hstart : BitMachineStackEmbedding.cfg bodyStack (headerBank x th)
      bodyLabel bodyControl (some (adminLabel .bodyScan))
      (B.init x) =
      (⟨some (bodyLabel B.start), bodyControl B.initial,
        headerBank x th⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [header_bank_body_initial]
    rfl
  rw [hstart] at hr
  have hrun : ((advance B.program)^[tb]) (B.init x) =
      B.run tb (B.init x) := rfl
  rw [hrun] at hr
  change (B.run tb (B.init x)).l = none at hb
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    bodyBank, hb] using hr

private theorem body_bank_output (packet : List Bool) :
    bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) bodyOutput =
      CodeDUpdatedEntryFields.weightField packet := by
  have hout := (BitMachine.outputsWithin_at_bound B
    (CodeDUpdatedEntryFields.weight_outputs packet)).2
  simpa [bodyBank, bodyOutput, bodyStack] using
    (BitMachineStackEmbedding.bank_at bodyStack
      (headerBank (packet)
        (CodeDUpdatedEntryFields.wordClock packet))
      (B.run (CodeDUpdatedEntryFields.weightClock packet)
        (B.init (packet))).stk B.output).trans hout

private theorem body_bank_header (packet : List Bool) :
    bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) headerOutput =
      CodeDUpdatedEntryFields.wordField packet := by
  rw [show bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) headerOutput =
      headerBank (packet)
        (CodeDUpdatedEntryFields.wordClock packet) headerOutput by
    unfold bodyBank
    apply BitMachineStackEmbedding.bank_outside
    intro ⟨k,hk⟩
    cases hk]
  exact header_bank_output packet

private theorem body_bank_aux (packet : List Bool) :
    bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) tempSlot = [] ∧
    bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) outputSlot = [] := by
  constructor
  · rw [show bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) tempSlot =
      headerBank (packet)
        (CodeDUpdatedEntryFields.wordClock packet) tempSlot by
      unfold bodyBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    rw [show headerBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet) tempSlot =
      copyBank (packet) tempSlot by
      unfold headerBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    exact (copy_input _).2.2.1
  · rw [show bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet) outputSlot =
      headerBank (packet)
        (CodeDUpdatedEntryFields.wordClock packet) outputSlot by
      unfold bodyBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    rw [show headerBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet) outputSlot =
      copyBank (packet) outputSlot by
      unfold headerBank
      apply BitMachineStackEmbedding.bank_outside
      intro ⟨k,hk⟩
      cases hk]
    exact (copy_input _).2.2.2

private noncomputable def bodyCopied (packet : List Bool) :
    Stack → List Bool :=
  BitMachineBroadcast.copied bodyOutput tempSlot [outputSlot]
    (CodeDUpdatedEntryFields.weightField packet)
    (bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet))

private theorem body_broadcast (packet : List Bool) :
    ((advance program)^[2*(CodeDUpdatedEntryFields.weightField packet).length+2])
      (⟨some (adminLabel .bodyScan),
        bodyControl (B.run (CodeDUpdatedEntryFields.weightClock packet)
          (B.init (packet))).var,
        bodyBank (packet)
          (CodeDUpdatedEntryFields.wordClock packet)
          (CodeDUpdatedEntryFields.weightClock packet)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (adminLabel .headerScan),
        bodyControl (B.run (CodeDUpdatedEntryFields.weightClock packet)
          (B.init (packet))).var,
        bodyCopied packet⟩ := by
  have h := BitMachineBroadcast.broadcast_run program bodyOutput tempSlot
    (by simp [bodyOutput, tempSlot]) [outputSlot]
    (by simp)
    (by simp [bodyOutput, outputSlot])
    (by simp [tempSlot, outputSlot])
    (adminLabel .bodyScan) (adminLabel .bodyRestore)
    (adminLabel .headerScan) (by rfl) (by rfl)
    (H.initial,
      (B.run (CodeDUpdatedEntryFields.weightClock packet)
        (B.init (packet))).var)
    none (CodeDUpdatedEntryFields.weightField packet)
    (bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet))
    (body_bank_output packet) (body_bank_aux packet).1
  simpa only [bodyControl, bodyCopied,
    BitMachineBroadcast.run] using h

private theorem body_copied_output (packet : List Bool) :
    bodyCopied packet outputSlot = CodeDUpdatedEntryFields.weightField packet := by
  unfold bodyCopied
  rw [BitMachineBroadcast.copied_target bodyOutput tempSlot [outputSlot]
    (CodeDUpdatedEntryFields.weightField packet)
    (bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet))
    (by simp [bodyOutput, outputSlot])
    (by simp [tempSlot, outputSlot]) outputSlot (by simp)]
  simp [(body_bank_aux packet).2]

private theorem body_copied_header (packet : List Bool) :
    bodyCopied packet headerOutput = CodeDUpdatedEntryFields.wordField packet := by
  unfold bodyCopied
  rw [BitMachineBroadcast.copied_other bodyOutput tempSlot [outputSlot]
    (CodeDUpdatedEntryFields.weightField packet)
    (bodyBank (packet)
      (CodeDUpdatedEntryFields.wordClock packet)
      (CodeDUpdatedEntryFields.weightClock packet)) headerOutput
    (by simp [headerOutput, bodyOutput])
    (by simp [headerOutput, tempSlot])
    (by simp [headerOutput, outputSlot])]
  exact body_bank_header packet

private theorem body_copied_temp (packet : List Bool) :
    bodyCopied packet tempSlot = [] := by
  exact BitMachineBroadcast.copied_temp bodyOutput tempSlot [outputSlot]
    (CodeDUpdatedEntryFields.weightField packet) _

private noncomputable def joinedBank (packet : List Bool) :
    Stack → List Bool :=
  BitMachineBroadcast.copied headerOutput tempSlot [outputSlot]
    (CodeDUpdatedEntryFields.wordField packet) (bodyCopied packet)

private theorem header_broadcast (packet : List Bool) :
    ((advance program)^[2*(CodeDUpdatedEntryFields.wordField packet).length+2])
      (⟨some (adminLabel .headerScan),
        bodyControl (B.run (CodeDUpdatedEntryFields.weightClock packet)
          (B.init (packet))).var,
        bodyCopied packet⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (adminLabel .done),
        bodyControl (B.run (CodeDUpdatedEntryFields.weightClock packet)
          (B.init (packet))).var,
        joinedBank packet⟩ := by
  have h := BitMachineBroadcast.broadcast_run program headerOutput tempSlot
    (by simp [headerOutput, tempSlot]) [outputSlot]
    (by simp)
    (by simp [headerOutput, outputSlot])
    (by simp [tempSlot, outputSlot])
    (adminLabel .headerScan) (adminLabel .headerRestore)
    (adminLabel .done) (by rfl) (by rfl)
    (H.initial,
      (B.run (CodeDUpdatedEntryFields.weightClock packet)
        (B.init (packet))).var)
    none (CodeDUpdatedEntryFields.wordField packet) (bodyCopied packet)
    (body_copied_header packet) (body_copied_temp packet)
  simpa only [bodyControl, joinedBank,
    BitMachineBroadcast.run] using h

private theorem joined_output (packet : List Bool) :
    joinedBank packet outputSlot = output packet := by
  unfold joinedBank
  rw [BitMachineBroadcast.copied_target headerOutput tempSlot [outputSlot]
    (CodeDUpdatedEntryFields.wordField packet) (bodyCopied packet)
    (by simp [headerOutput, outputSlot])
    (by simp [tempSlot, outputSlot]) outputSlot (by simp)]
  rw [body_copied_output]
  rfl

private theorem run_chain
    (c₀ c₁ c₂ : TM2.Cfg (fun _ : Stack => Bool) Label Control)
    (a b : Nat)
    (h₁ : ((advance program)^[a]) c₀ = c₁)
    (h₂ : ((advance program)^[b]) c₁ = c₂) :
    ((advance program)^[a+b]) c₀ = c₂ := by
  rw [show a+b=b+a by omega, Function.iterate_add_apply, h₁, h₂]

theorem outputs (packet : List Bool) :
    machine.OutputsWithin (packet)
      (output packet) (clock packet) := by
  let x := packet
  let th := CodeDUpdatedEntryFields.wordClock packet
  let tb := CodeDUpdatedEntryFields.weightClock packet
  let u := CodeDUpdatedEntryFields.weightField packet
  let v := CodeDUpdatedEntryFields.wordField packet
  let tc := 2*x.length+2
  obtain ⟨qh,hqh,hH⟩ := header_phase packet
  obtain ⟨qb,hqb,hB⟩ := body_phase packet
  have h0 := copy_phase x
  have h1 : ((advance program)^[1])
      (⟨some (adminLabel .startHeader), ((H.initial,B.initial),none),
        copyBank x⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (headerLabel H.start), headerControl H.initial, copyBank x⟩ :=
    start_header x
  have h2 : ((advance program)^[1])
      (⟨some (adminLabel .startBody),
        headerControl (H.run th (H.init x)).var,
        headerBank x th⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (bodyLabel B.start), bodyControl B.initial,
        headerBank x th⟩ := start_body x th
  have h3 : ((advance program)^[1])
      (⟨some (adminLabel .done),
        bodyControl (B.run tb (B.init x)).var,
        joinedBank packet⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, bodyControl (B.run tb (B.init x)).var,
        joinedBank packet⟩ := by rfl
  have h01 := run_chain _ _ _ tc 1 h0 h1
  have h012 := run_chain _ _ _ (tc+1) qh h01 hH
  have h0123 := run_chain _ _ _ (tc+1+qh) 1 h012 h2
  have h01234 := run_chain _ _ _ (tc+1+qh+1) qb h0123 hB
  have h012345 := run_chain _ _ _ (tc+1+qh+1+qb)
    (2*u.length+2) h01234 (body_broadcast packet)
  have h0123456 := run_chain _ _ _
    (tc+1+qh+1+qb+(2*u.length+2))
    (2*v.length+2) h012345 (header_broadcast packet)
  have hfull := run_chain _ _ _
    (tc+1+qh+1+qb+(2*u.length+2)+(2*v.length+2))
    1 h0123456 h3
  apply outputsWithin_of_raw_run initialSlot outputSlot
    (adminLabel .copyScan) ((H.initial,B.initial),none) program
    x (output packet)
    (tc+1+qh+1+qb+(2*u.length+2)+(2*v.length+2)+1)
    (clock packet) (by dsimp [clock,tc,u,v,th,tb,x]; omega)
  · simpa only [x] using congrArg TM2.Cfg.l hfull
  · have hout := congrArg (fun c : TM2.Cfg (fun _ : Stack => Bool)
      Label Control => c.stk outputSlot) hfull
    simpa [joined_output] using hout

theorem writes_updated_entry
    (old : CodeDSourceCodecV2.Entry) (updated : ℚ) :
    machine.OutputsWithin
      (CodeDUpdatedEntryFields.pairPacket old updated)
      (CodeDSourceCodecV2.encodeEntry
        ⟨old.word, CodeDCanonicalSourceV2.rawOfRat updated⟩)
      (clock (CodeDUpdatedEntryFields.pairPacket old updated)) := by
  have h := outputs (CodeDUpdatedEntryFields.pairPacket old updated)
  simp only [output] at h
  rw [CodeDUpdatedEntryFields.fields_pair] at h
  exact h

#print axioms outputs
#print axioms writes_updated_entry


end CurrentAdditive.CodeDUpdatedEntryJoin
