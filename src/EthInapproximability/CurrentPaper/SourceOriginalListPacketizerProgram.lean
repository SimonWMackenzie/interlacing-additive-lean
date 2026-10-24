import EthInapproximability.CurrentPaper.SourceOriginalListInfrastructure
import EthInapproximability.CurrentPaper.SourceOriginalPacketFraming
import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Fixed outer source-list packetizer program

The input is already held in two *physical* banks: original unary `n` and the
canonical sparse-list bytes emitted by the cited machine. This finite program
parses the outer binary count, decrements once per item, extracts each field,
invokes the fixed original-n packet/framing machine, clears all reusable
scratch, and finally reverses the accumulated ordered list. Correctness and
the summed runtime are proved in successor owners.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding

noncomputable section

abbrev FrameStack := SourceOriginalPacketFraming.Stack
abbrev Stack := FrameStack ⊕ Fin 10

inductive Admin where
  | startInit | afterInit | afterCounter | afterField | afterFrame
  | emit | clearFieldCount | clearFrame (i : Fin (Fintype.card FrameStack + 1))
  | checkTail | finalize | done
  deriving DecidableEq, Fintype

abbrev Label := SourceListMachineInitialize.Label ⊕
  (SourceListMachineCounter.Label ⊕
    (SourceListMachineFields.Label ⊕
      (SourceOriginalPacketFraming.Label ⊕ Admin)))

abbrev Control :=
  ((((SourceListMachineInitialize.Control × SourceListMachineCounter.Control) ×
    SourceListMachineFields.Control) × SourceOriginalPacketFraming.Control) × Option Bool)

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initLabel (l : SourceListMachineInitialize.Label) : Label := .inl l
def counterLabel (l : SourceListMachineCounter.Label) : Label := .inr (.inl l)
def fieldLabel (l : SourceListMachineFields.Label) : Label := .inr (.inr (.inl l))
def frameLabel (l : SourceOriginalPacketFraming.Label) : Label :=
  .inr (.inr (.inr (.inl l)))
def adminLabel (l : Admin) : Label := .inr (.inr (.inr (.inr l)))

def initStack : SourceListMachineInitialize.Stack ↪ Stack where
  toFun k := .inr (![0,1,2,3,4] k)
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def counterStack : SourceListMachineCounter.Stack ↪ Stack where
  toFun k := .inr (![2,3] k)
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

noncomputable def fieldStack : SourceListMachineFields.Stack ↪ Stack where
  toFun k := ![.inr 0, .inr 1, .inr 5, .inr 6, .inr 7, .inr 8,
    .inl SourceOriginalPacketFraming.wordStack] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def frameStack : SourceOriginalPacketFraming.Stack ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def frameStartLabel : SourceOriginalPacketFraming.Label :=
  .inl SourceOriginalPacketFraming.writerMachine.start

noncomputable def frameInitialControl : SourceOriginalPacketFraming.Control :=
  (SourceOriginalPacketFraming.writerMachine.initial,
    SourceOriginalPacketFraming.frameMachine.initial, none)

noncomputable def initControl (v : SourceListMachineInitialize.Control) : Control :=
  ((((v,SourceListMachineCounter.initialControl),
    SourceListMachineFields.initialControl),frameInitialControl),none)

noncomputable def counterControl (v : SourceListMachineCounter.Control) : Control :=
  ((((SourceListMachineInitialize.initialControl,v),
    SourceListMachineFields.initialControl),frameInitialControl),none)

noncomputable def fieldControl (v : SourceListMachineFields.Control) : Control :=
  ((((SourceListMachineInitialize.initialControl,
    SourceListMachineCounter.initialControl),v),frameInitialControl),none)

noncomputable def frameControl (v : SourceOriginalPacketFraming.Control) : Control :=
  ((((SourceListMachineInitialize.initialControl,
    SourceListMachineCounter.initialControl),
    SourceListMachineFields.initialControl),v),none)

noncomputable def initialControl : Control :=
  initControl SourceListMachineInitialize.initialControl

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt initStack initLabel initControl
      (fun v => v.1.1.1.1) (some (adminLabel .afterInit))
      (SourceListMachineInitialize.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt counterStack counterLabel
      counterControl (fun v => v.1.1.1.2) (some (adminLabel .afterCounter))
      (SourceListMachineCounter.program l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt fieldStack fieldLabel
      fieldControl (fun v => v.1.1.2) (some (adminLabel .afterField))
      (SourceListMachineFields.program l)
  | .inr (.inr (.inr (.inl l))) => BitMachineStackEmbedding.stmt frameStack frameLabel
      frameControl (fun v => v.1.2) (some (adminLabel .afterFrame))
      (SourceOriginalPacketFraming.program l)
  | .inr (.inr (.inr (.inr .startInit))) =>
      .load (fun _ => initControl SourceListMachineInitialize.initialControl)
        (.goto (fun _ => initLabel (.inl .scan)))
  | .inr (.inr (.inr (.inr .afterInit))) =>
      .branch (fun v => v.1.1.1.1.2 == some true)
        (.load (fun _ => counterControl SourceListMachineCounter.initialControl)
          (.goto (fun _ => counterLabel (.inr .scan))))
        .halt
  | .inr (.inr (.inr (.inr .afterCounter))) =>
      .branch (fun v => v.1.1.1.2.2.1 == some true)
        (.load (fun _ => fieldControl SourceListMachineFields.initialControl)
          (.goto (fun _ => fieldLabel (.inl .scan))))
        (.goto (fun _ => adminLabel .checkTail))
  | .inr (.inr (.inr (.inr .afterField))) =>
      .branch (fun v => v.1.1.2.2.1 == some true)
        (.load (fun _ => frameControl frameInitialControl)
          (.goto (fun _ => frameLabel frameStartLabel)))
        .halt
  | .inr (.inr (.inr (.inr .afterFrame))) =>
      .goto (fun _ => adminLabel .emit)
  | .inr (.inr (.inr (.inr .emit))) =>
      BitMachineBroadcast.scanStep
        (.inl SourceOriginalPacketFraming.outputStack) (.inr 4)
        (adminLabel .emit) (adminLabel .clearFieldCount)
  | .inr (.inr (.inr (.inr .clearFieldCount))) =>
      BitMachineClearBank.clearStep (.inr 8)
        (adminLabel .clearFieldCount) (adminLabel (.clearFrame 0))
  | .inr (.inr (.inr (.inr (.clearFrame i)))) =>
      if h : i.val < Fintype.card FrameStack then
        let k := (Fintype.equivFin FrameStack).symm ⟨i.val,h⟩
        if k = SourceOriginalPacketFraming.nStack then
          .goto (fun _ => adminLabel (.clearFrame ⟨i.val+1,by omega⟩))
        else
          .pop (.inl k) (fun v b => (v.1,b))
            (.branch (fun v => v.2.isSome)
              (.load (fun v => (v.1,none))
                (.goto (fun _ => adminLabel (.clearFrame i))))
              (.load (fun v => (v.1,none))
                (.goto (fun _ => adminLabel (.clearFrame ⟨i.val+1,by omega⟩)))))
      else .load (fun _ => counterControl SourceListMachineCounter.initialControl)
        (.goto (fun _ => counterLabel (.inr .scan)))
  | .inr (.inr (.inr (.inr .checkTail))) =>
      .pop (.inr 0) (fun v b => (v.1,b))
        (.branch (fun v => v.2.isSome) .halt
          (.goto (fun _ => adminLabel .finalize)))
  | .inr (.inr (.inr (.inr .finalize))) =>
      BitMachineBroadcast.scanStep (.inr 4) (.inr 9)
        (adminLabel .finalize) (adminLabel .done)
  | .inr (.inr (.inr (.inr .done))) => .halt

noncomputable def startBank (n : ℕ) (source : List Bool) : Stack → List Bool :=
  fun k => if k = .inl SourceOriginalPacketFraming.nStack then
    List.replicate n true
  else if k = .inr 0 then source else []

noncomputable def startCfg (n : ℕ) (source : List Bool) : Config :=
  ⟨some (adminLabel .startInit), initialControl, startBank n source⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
