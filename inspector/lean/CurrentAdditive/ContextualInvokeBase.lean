import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-! A fixed contextual invocation layout. Only the encoded context/request
packet is initially present; parsing installs the two fields physically. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace CurrentAdditive.ContextualInvoke
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open BitMachineBankCodec MinimumRatioContext

abbrev Stack (M : BitMachine.Machine) := MachineInvokeCore.StackN M.stackCount

def low (M : BitMachine.Machine) (k : Fin 32) : Stack M := ⟨k.val,by have := k.isLt; omega⟩

def lowEmbedding (M : BitMachine.Machine) : Fin 32 ↪ Stack M := ⟨low M,by
  intro a b h; apply Fin.ext; exact congrArg (fun k : Stack M => k.val) h⟩

def slots (M : BitMachine.Machine) : MachineInvokeCore.Slots M M.stackCount where
  machine := ⟨fun k => ⟨32+k.val,by have := k.isLt; omega⟩,by
    intro a b h; apply Fin.ext; have hv := congrArg Fin.val h; simp only [Fin.val_mk] at hv; omega⟩
  source := low M 0
  target := low M 1
  scratch := low M 2
  source_target := by intro h; have := congrArg Fin.val h; simp [low] at this
  source_scratch := by intro h; have := congrArg Fin.val h; simp [low] at this
  target_scratch := by intro h; have := congrArg Fin.val h; simp [low] at this
  source_machine := by intro k h; have := congrArg Fin.val h; simp [low] at this; omega
  target_machine := by intro k h; have := congrArg Fin.val h; simp [low] at this; omega
  scratch_machine := by intro k h; have := congrArg Fin.val h; simp [low] at this; omega

def parseLow : (Fin 2 ⊕ Fin 3) ↪ Fin 32 :=
  ⟨Sum.elim (fun k => ![3,0] k) (fun k => ![4,5,6] k),by decide⟩

def emitLow : (Fin 2 ⊕ Fin 3) ↪ Fin 32 :=
  ⟨Sum.elim (fun k => ![3,1] k) (fun k => ![4,5,6] k),by decide⟩

def parseStack (M : BitMachine.Machine) := parseLow.trans (lowEmbedding M)

def emitStack (M : BitMachine.Machine) := emitLow.trans (lowEmbedding M)

inductive Label (M : BitMachine.Machine) where
  | parse (l : ParserLabel 2)
  | invoke (l : MachineInvokeFull.LabelFull M)
  | emit (l : BitMachineBankSerialize.Label 2)
  | afterParse | afterInvoke
  deriving DecidableEq,Fintype

abbrev Control (M : BitMachine.Machine) := MachineInvokeFull.ControlFull M × Option Bool
abbrev Config (M : BitMachine.Machine) := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def localControl (M : BitMachine.Machine) := MachineInvokeFull.control (slots M)

def packetControl (M : BitMachine.Machine) (v : Option Bool) : Control M := (localControl M,v)

def liftControl (M : BitMachine.Machine) (v : MachineInvokeFull.ControlFull M) : Control M := (v,none)

def program (M : BitMachine.Machine) : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .parse l => BitMachineStackEmbedding.stmt (parseStack M) .parse (packetControl M) Prod.snd
      (some .afterParse) (parser 2 l)
  | .invoke l => BitMachineInline.stmt .invoke (liftControl M) Prod.fst
      (some .afterInvoke) (MachineInvokeFull.program (slots M) l)
  | .emit l => BitMachineStackEmbedding.stmt (emitStack M) .emit (packetControl M) Prod.snd
      none (BitMachineBankSerialize.program 2 l)
  | .afterParse => .load (fun _ => liftControl M (localControl M))
      (.goto (fun _ => .invoke (MachineInvokeFull.start (slots M))))
  | .afterInvoke => .load (fun _ => packetControl M none) (.goto (fun _ => .emit (.emit 0)))

def run (M : BitMachine.Machine) (t : Nat) (c : Config M) := ((advance (program M))^[t]) c

def packet (context request : List Bool) := encode ![context,request]

def output (context answer : List Bool) := encode ![context,answer]

def initialBank (M : BitMachine.Machine) (context request : List Bool) : Stack M → List Bool :=
  fun k => if k=low M 4 then packet context request else []

def loaded (M : BitMachine.Machine) (context request : List Bool) : Stack M → List Bool :=
  fun k => if k=low M 3 then context else if k=low M 0 then request else []

def invoked (M : BitMachine.Machine) (context request answer : List Bool) : Stack M → List Bool :=
  Function.update (loaded M context request) (low M 1) answer

noncomputable def parseFrame (M : BitMachine.Machine) (S : Stack M → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool) (ParserLabel 2) (Option Bool)) : Config M :=
  BitMachineStackEmbedding.cfg (parseStack M) S .parse (packetControl M) (some .afterParse) c

noncomputable def emitFrame (M : BitMachine.Machine) (S : Stack M → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool) (BitMachineBankSerialize.Label 2) (Option Bool)) : Config M :=
  BitMachineStackEmbedding.cfg (emitStack M) S .emit (packetControl M) none c

theorem run_add (M : BitMachine.Machine) {c c' : Config M} {n : Nat}
    (h : run M n c=c') (m : Nat) : run M (n+m) c=run M m c' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run M m) h

theorem embeddedBank_eq {K J : Type} [DecidableEq K] [DecidableEq J]
    (e : K ↪ J) (S : J → List Bool) (T : K → List Bool) (U : J → List Bool)
    (hin : ∀ k,U (e k)=T k) (hout : ∀ j, (¬∃ k,e k=j) → U j=S j) :
    BitMachineStackEmbedding.bank e S T=U := by
  classical
  funext j
  by_cases h : ∃ k,e k=j
  · obtain ⟨k,rfl⟩ := h; rw [BitMachineStackEmbedding.bank_at]; exact (hin k).symm
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]; exact (hout j h).symm

end CurrentAdditive.ContextualInvoke
