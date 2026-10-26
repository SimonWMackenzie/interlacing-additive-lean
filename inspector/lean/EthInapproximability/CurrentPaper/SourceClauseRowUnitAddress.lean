import EthInapproximability.CurrentPaper.SourceClauseRowSlotAddress
import EthInapproximability.CurrentPaper.SourceLabelAddressMachine
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# Physical source-row unit-clause address

The supplied unary words `n,a,r,k,w,ell` feed a slot controller, an
independent `n*a+ell` multiply-add controller, two preserving bank transfers,
and the unary-to-binary affine address controller. The final binary word is
`(n+n*a*a+r*a^q+k)*w+n*a+ell`. Nothing supplies that slot or word initially.
This is a source-converter component under frozen v8 `06-eth.tex`.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowUnitAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceClauseRowSlotAddress.Stack ⊕
  (Fin 6 ⊕ SourceLabelAddressMachine.Stack)

def slotEmbedding : SourceClauseRowSlotAddress.Stack ↪ Stack :=
  Function.Embedding.inl
def offsetEmbedding : Fin 6 ↪ Stack where
  toFun := Sum.inr ∘ Sum.inl
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)
def labelEmbedding : SourceLabelAddressMachine.Stack ↪ Stack where
  toFun := Sum.inr ∘ Sum.inr
  inj' := by intro x y h; exact Sum.inr.inj (Sum.inr.inj h)

def slotSource : Stack := .inl SourceClauseRowSlotAddress.target
def slotTemp : Stack := .inl SourceClauseRowSlotAddress.temp
def offsetSource : Stack := .inr (.inl 5)
def offsetTemp : Stack := .inr (.inl 3)
def labelSlot : Stack := .inr (.inr (.inl 0))
def labelWidth : Stack := .inr (.inr (.inl 1))
def labelOffset : Stack := .inr (.inr (.inl 2))
noncomputable def binarySource : Stack :=
  .inr (.inr (.inr (.inl SourceLabelAddressMachine.counter.input)))

def slotValue (n r a q k : Nat) : Nat :=
  SourceClauseRowSlotAddress.slot n r a q k
def offsetValue (n a ell : Nat) : Nat := n * a + ell
def address (n r a q k w ell : Nat) : Nat :=
  slotValue n r a q k * w + offsetValue n a ell

theorem address_formula (n r a q k w ell : Nat) :
    address n r a q k w ell =
      n * a + (n + n * (a * a) + r * a ^ q + k) * w + ell := by
  unfold address slotValue offsetValue SourceClauseRowSlotAddress.slot
  ring

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def slotCopy : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep slotSource slotTemp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep slotTemp [labelSlot]
      .restore .finish
  | .finish => .halt

def offsetCopy : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep offsetSource offsetTemp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep offsetTemp [labelOffset]
      .restore .finish
  | .finish => .halt

def offsetInput (n a ell : Nat) : Fin 6 → List Bool :=
  (MatrixAddressMachine.cfg (some .outer) false
    (List.replicate n true) (List.replicate a true)
    (List.replicate ell true) [] [] []).stk

def offsetOutput (n a ell : Nat) : Fin 6 → List Bool :=
  (MatrixAddressMachine.cfg none false
    (List.replicate n true) (List.replicate a true)
    (List.replicate ell true) [] []
    (List.replicate (offsetValue n a ell) true)).stk

def labelInput (w : Nat) : SourceLabelAddressMachine.Stack → List Bool :=
  SourceLabelAddressMachine.ambient 0 w 0 (fun _ => [])

noncomputable def initial (n r a q k w ell : Nat) : Stack → List Bool :=
  Sum.elim (SourceClauseRowSlotAddress.initial n r a q k)
    (Sum.elim (offsetInput n a ell) (labelInput w))

noncomputable def slotDone (n r a q k w ell : Nat) : Stack → List Bool :=
  Sum.elim (SourceClauseRowSlotAddress.finalBank n r a q k)
    (Sum.elim (offsetInput n a ell) (labelInput w))

noncomputable def offsetDone (n r a q k w ell : Nat) : Stack → List Bool :=
  Sum.elim (SourceClauseRowSlotAddress.finalBank n r a q k)
    (Sum.elim (offsetOutput n a ell) (labelInput w))

noncomputable def slotCopied (n r a q k w ell : Nat) : Stack → List Bool :=
  BitMachineBroadcast.copied slotSource slotTemp [labelSlot]
    (List.replicate (slotValue n r a q k) true)
    (offsetDone n r a q k w ell)

noncomputable def operandsReady (n r a q k w ell : Nat) : Stack → List Bool :=
  BitMachineBroadcast.copied offsetSource offsetTemp [labelOffset]
    (List.replicate (offsetValue n a ell) true)
    (slotCopied n r a q k w ell)

noncomputable def addressed (n r a q k w ell : Nat) : Stack → List Bool :=
  bank labelEmbedding (operandsReady n r a q k w ell)
    (SourceLabelAddressMachine.outputs (slotValue n r a q k) w
      (offsetValue n a ell))

/-- The variable inputs really occupy unary machine stacks at entry; neither
the row slot nor the binary endpoint address is an initial operand. -/
theorem initial_words (n r a q k w ell : Nat) :
    initial n r a q k w ell
        (slotEmbedding (SourceClauseRowSlotAddress.firstEmbedding 0)) =
          List.replicate n true ∧
      initial n r a q k w ell
        (slotEmbedding (SourceClauseRowSlotAddress.secondEmbedding 0)) =
          List.replicate r true ∧
      initial n r a q k w ell
        (slotEmbedding (SourceClauseRowSlotAddress.secondEmbedding 2)) =
          List.replicate k true ∧
      initial n r a q k w ell (offsetEmbedding 1) =
          List.replicate a true ∧
      initial n r a q k w ell labelWidth =
          List.replicate w true ∧
      initial n r a q k w ell (offsetEmbedding 2) =
          List.replicate ell true := by
  simp [initial, slotEmbedding, offsetEmbedding, labelWidth, labelInput,
    SourceClauseRowSlotAddress.initial, SourceClauseRowSlotAddress.firstEmbedding,
    SourceClauseRowSlotAddress.secondEmbedding, offsetInput,
    SourceLabelAddressMachine.ambient, MatrixAddressMachine.cfg]

abbrev SlotLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label MatrixAddressMachine.Label
    SourceClauseRowSlotAddress.CopyLabel)
  MatrixAddressMachine.Label
abbrev SlotControl := ((Bool × (Unit × Option Bool)) × Bool)

def slotProgram (l : SlotLabel) :=
  stackStmt slotEmbedding (SourceClauseRowSlotAddress.program l)

def offsetProgram (l : MatrixAddressMachine.Label) :=
  stackStmt offsetEmbedding (MatrixAddressMachine.program l)

noncomputable def labelProgram (l : SourceLabelAddressMachine.Label) :=
  stackStmt labelEmbedding (SourceLabelAddressMachine.program l)

theorem slot_run (n r a q k w ell : Nat) :
    ∃ t ≤ SourceClauseRowSlotAddress.cost n r a q k,
      ((advance slotProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)), false), initial n r a q k w ell⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SlotLabel SlotControl) =
        ⟨none, ((false, ((), none)), false), slotDone n r a q k w ell⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceClauseRowSlotAddress.run n r a q k
  let c : TM2.Cfg (fun _ : SourceClauseRowSlotAddress.Stack => Bool)
      SlotLabel SlotControl :=
    ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
      ((false, ((), none)), false), SourceClauseRowSlotAddress.initial n r a q k⟩
  have he := BitMachineStackRun.run slotEmbedding (initial n r a q k w ell)
    SourceClauseRowSlotAddress.program c t
  have hstart : bank slotEmbedding (initial n r a q k w ell) c.stk =
      initial n r a q k w ell := by
    apply bank_eq_self
    intro i
    rfl
  have hend : bank slotEmbedding (initial n r a q k w ell)
      (SourceClauseRowSlotAddress.finalBank n r a q k) =
      slotDone n r a q k w ell := by
    funext i
    cases i with
    | inl j => exact bank_at slotEmbedding _ _ j
    | inr j =>
        rw [bank_outside]
        · rfl
        · rintro ⟨u, hu⟩
          cases hu
  rw [show ((advance SourceClauseRowSlotAddress.program)^[t]) c = _ from
    by simpa only [c] using hr] at he
  simp only [stackCfg, hstart, hend] at he
  exact ⟨t, ht, by simpa only [slotProgram, c] using he⟩

theorem offset_run (n r a q k w ell : Nat) :
    ((advance offsetProgram)^[MatrixAddressMachine.exactTime n a ell])
      (⟨some .outer, false, slotDone n r a q k w ell⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, offsetDone n r a q k w ell⟩ := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate n true) (List.replicate a true)
    (List.replicate ell true) [] [] []
  have hr := MatrixAddressMachine.address_run n a ell false []
  have he := BitMachineStackRun.run offsetEmbedding
    (slotDone n r a q k w ell) MatrixAddressMachine.program c
    (MatrixAddressMachine.exactTime n a ell)
  have hstart : bank offsetEmbedding (slotDone n r a q k w ell) c.stk =
      slotDone n r a q k w ell := by
    apply bank_eq_self
    intro i
    rfl
  have hend : bank offsetEmbedding (slotDone n r a q k w ell)
      (offsetOutput n a ell) = offsetDone n r a q k w ell := by
    funext i
    cases i with
    | inl j =>
        rw [bank_outside]
        · rfl
        · rintro ⟨u, hu⟩
          cases hu
    | inr j =>
        cases j with
        | inl j => exact bank_at offsetEmbedding _ _ j
        | inr j =>
            rw [bank_outside]
            · rfl
            · rintro ⟨u, hu⟩
              cases hu
  rw [show ((advance MatrixAddressMachine.program)^[
      MatrixAddressMachine.exactTime n a ell]) c =
      ⟨none, false, offsetOutput n a ell⟩ from by
        simpa only [c, offsetOutput, offsetValue, List.append_nil] using hr] at he
  simp only [stackCfg, hstart, hend] at he
  simpa only [offsetProgram, c] using he

theorem slot_source (n r a q k w ell : Nat) :
    offsetDone n r a q k w ell slotSource =
      List.replicate (slotValue n r a q k) true := by
  exact SourceClauseRowSlotAddress.final_slot n r a q k

theorem slot_temp (n r a q k w ell : Nat) :
    offsetDone n r a q k w ell slotTemp = [] := by
  change SourceClauseRowSlotAddress.finalBank n r a q k
    SourceClauseRowSlotAddress.temp = []
  unfold SourceClauseRowSlotAddress.finalBank
  rw [bank_outside]
  · exact BitMachineBroadcast.copied_temp _ _ _ _ _
  · rintro ⟨u, hu⟩
    fin_cases u <;> simp [SourceClauseRowSlotAddress.secondEmbedding,
      SourceClauseRowSlotAddress.temp] at hu

theorem slot_copy_run (n r a q k w ell : Nat) :
    ((advance slotCopy)^[2 * slotValue n r a q k + 3])
      (⟨some .scan, ((), none), offsetDone n r a q k w ell⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), slotCopied n r a q k w ell⟩ := by
  let bits := List.replicate (slotValue n r a q k) true
  have hr := BitMachineBroadcast.broadcast_run slotCopy slotSource slotTemp
    (by decide) [labelSlot] (by simp)
    (by simp [slotSource, labelSlot])
    (by simp [slotTemp, labelSlot])
    .scan .restore .finish rfl rfl () none bits
    (offsetDone n r a q k w ell) (slot_source ..) (slot_temp ..)
  rw [show 2 * slotValue n r a q k + 3 = 2 * bits.length + 2 + 1 by simp [bits],
    Function.iterate_succ_apply']
  change advance slotCopy
    (BitMachineBroadcast.run slotCopy (2 * bits.length + 2)
      (⟨some .scan, ((), none), offsetDone n r a q k w ell⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [hr]
  simp [advance, TM2.step, slotCopy, slotCopied, bits]

theorem offset_source (n r a q k w ell : Nat) :
    slotCopied n r a q k w ell offsetSource =
      List.replicate (offsetValue n a ell) true := by
  simp [slotCopied, BitMachineBroadcast.copied,
    slotSource, slotTemp, labelSlot, offsetSource, offsetDone,
    offsetOutput, offsetValue, MatrixAddressMachine.cfg]

theorem offset_temp (n r a q k w ell : Nat) :
    slotCopied n r a q k w ell offsetTemp = [] := by
  simp [slotCopied, BitMachineBroadcast.copied,
    slotSource, slotTemp, labelSlot, offsetTemp, offsetDone,
    offsetOutput, MatrixAddressMachine.cfg]

theorem offset_copy_run (n r a q k w ell : Nat) :
    ((advance offsetCopy)^[2 * offsetValue n a ell + 3])
      (⟨some .scan, ((), none), slotCopied n r a q k w ell⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), operandsReady n r a q k w ell⟩ := by
  let bits := List.replicate (offsetValue n a ell) true
  have hr := BitMachineBroadcast.broadcast_run offsetCopy offsetSource offsetTemp
    (by decide) [labelOffset] (by simp)
    (by simp [offsetSource, labelOffset])
    (by simp [offsetTemp, labelOffset])
    .scan .restore .finish rfl rfl () none bits
    (slotCopied n r a q k w ell) (offset_source ..) (offset_temp ..)
  rw [show 2 * offsetValue n a ell + 3 = 2 * bits.length + 2 + 1 by simp [bits],
    Function.iterate_succ_apply']
  change advance offsetCopy
    (BitMachineBroadcast.run offsetCopy (2 * bits.length + 2)
      (⟨some .scan, ((), none), slotCopied n r a q k w ell⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [hr]
  simp [advance, TM2.step, offsetCopy, operandsReady, bits]

theorem label_ready (n r a q k w ell : Nat) :
    (fun i => operandsReady n r a q k w ell (labelEmbedding i)) =
      SourceLabelAddressMachine.inputs (slotValue n r a q k) w
        (offsetValue n a ell) := by
  funext i
  cases i with
  | inl j =>
      fin_cases j <;>
        simp [operandsReady, slotCopied, BitMachineBroadcast.copied,
          labelEmbedding, labelSlot, labelOffset, slotSource, slotTemp,
          offsetSource, offsetTemp, offsetDone, labelInput,
          SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient,
          slotValue, offsetValue]
  | inr j =>
      simp [operandsReady, slotCopied, BitMachineBroadcast.copied,
        labelEmbedding, labelSlot, labelOffset, slotSource, slotTemp,
        offsetSource, offsetTemp, offsetDone, labelInput,
        SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient]

theorem label_run (n r a q k w ell : Nat) :
    ∃ t ≤ MatrixAddressMachine.exactTime
          (slotValue n r a q k) w (offsetValue n a ell) +
        UnaryBinaryEncoding.coefficient *
          (address n r a q k w ell + 1) ^ 2 + 1,
      ((advance labelProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel .outer),
          (false, (SourceLabelAddressMachine.counter.initial, none)),
          operandsReady n r a q k w ell⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SourceLabelAddressMachine.Label SourceLabelAddressMachine.Control) =
        ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
          addressed n r a q k w ell⟩ := by
  let s := slotValue n r a q k
  let c := offsetValue n a ell
  obtain ⟨t, ht, hr⟩ := SourceLabelAddressMachine.label_run s w c
  let localCfg : SourceLabelAddressMachine.Config :=
    ⟨some (BitMachineRawSequence.leftLabel .outer),
      (false, (SourceLabelAddressMachine.counter.initial, none)),
      SourceLabelAddressMachine.inputs s w c⟩
  have he := BitMachineStackRun.run labelEmbedding
    (operandsReady n r a q k w ell) SourceLabelAddressMachine.program
    localCfg t
  have hstart : bank labelEmbedding (operandsReady n r a q k w ell)
      localCfg.stk = operandsReady n r a q k w ell := by
    apply bank_eq_self
    intro i
    exact congrFun (label_ready n r a q k w ell) i |>.symm
  rw [show ((advance SourceLabelAddressMachine.program)^[t]) localCfg =
      ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
        SourceLabelAddressMachine.outputs s w c⟩ from by
        simpa only [localCfg] using hr] at he
  simp only [stackCfg, hstart] at he
  exact ⟨t, by simpa only [s, c, address] using ht,
    by simpa only [labelProgram, addressed, s, c, localCfg] using he⟩

theorem binary_result (n r a q k w ell : Nat) :
    addressed n r a q k w ell binarySource =
      (address n r a q k w ell).bits := by
  change addressed n r a q k w ell
    (labelEmbedding (.inr (.inl SourceLabelAddressMachine.counter.input))) = _
  rw [addressed, bank_at]
  simp [SourceLabelAddressMachine.outputs, SourceLabelAddressMachine.ambient,
    SourceUnaryBinaryCall.final_bank, address, slotValue, offsetValue]

abbrev PrefixLabel := BitMachineRawSequence.Label SlotLabel
  MatrixAddressMachine.Label
abbrev PrefixControl := SlotControl × Bool
def prefixProgram := BitMachineRawSequence.program slotProgram offsetProgram
  MatrixAddressMachine.Label.outer
  ((false, ((), none)), false) false

abbrev CopiesLabel := BitMachineRawSequence.Label CopyLabel CopyLabel
abbrev CopiesControl := (Unit × Option Bool) × (Unit × Option Bool)
def copiesProgram := BitMachineRawSequence.program slotCopy offsetCopy
  CopyLabel.scan ((), none) ((), none)

abbrev SetupLabel := BitMachineRawSequence.Label PrefixLabel CopiesLabel
abbrev SetupControl := PrefixControl × CopiesControl
def setupProgram := BitMachineRawSequence.program prefixProgram copiesProgram
  (BitMachineRawSequence.leftLabel CopyLabel.scan)
  (((false, ((), none)), false), false) (((), none), ((), none))

abbrev Label := BitMachineRawSequence.Label SetupLabel
  SourceLabelAddressMachine.Label
abbrev Control := SetupControl × SourceLabelAddressMachine.Control
noncomputable def program := BitMachineRawSequence.program setupProgram labelProgram
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
  ((((false, ((), none)), false), false), (((), none), ((), none)))
  (false, (SourceLabelAddressMachine.counter.initial, none))

noncomputable def cost (n r a q k w ell : Nat) : Nat :=
  let s := slotValue n r a q k
  let c := offsetValue n a ell
  let p := address n r a q k w ell
  SourceClauseRowSlotAddress.cost n r a q k +
    MatrixAddressMachine.exactTime n a ell +
    (2 * s + 3) + (2 * c + 3) +
    MatrixAddressMachine.exactTime s w c +
    UnaryBinaryEncoding.coefficient * (p + 1) ^ 2 + 5

theorem run (n r a q k w ell : Nat) :
    ∃ t ≤ cost n r a q k w ell,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  MatrixAddressMachine.Label.outer))))),
          (((((false, ((), none)), false), false),
            (((), none), ((), none))),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          initial n r a q k w ell⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,
          (((((false, ((), none)), false), false),
            (((), none), ((), none))),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          addressed n r a q k w ell⟩ := by
  obtain ⟨ts, hts, hrs⟩ := slot_run n r a q k w ell
  obtain ⟨tp, htp, hrp⟩ := BitMachineRawSequence.runs
    slotProgram offsetProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer) : SlotLabel)
    MatrixAddressMachine.Label.outer
    (((false, ((), none)), false) : SlotControl)
    ((false, ((), none)), false)
    (false : Bool) false
    (initial n r a q k w ell) (slotDone n r a q k w ell)
    (offsetDone n r a q k w ell)
    ts (MatrixAddressMachine.exactTime n a ell) hrs
    (offset_run n r a q k w ell)
  obtain ⟨tc, htc, hrc⟩ := BitMachineRawSequence.runs
    slotCopy offsetCopy CopyLabel.scan CopyLabel.scan
    (((), none) : Unit × Option Bool) ((), none)
    (((), none) : Unit × Option Bool) ((), none)
    (offsetDone n r a q k w ell) (slotCopied n r a q k w ell)
    (operandsReady n r a q k w ell)
    (2 * slotValue n r a q k + 3)
    (2 * offsetValue n a ell + 3)
    (slot_copy_run n r a q k w ell)
    (offset_copy_run n r a q k w ell)
  obtain ⟨tu, htu, hru⟩ := BitMachineRawSequence.runs
    prefixProgram copiesProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)) :
        PrefixLabel)
    (BitMachineRawSequence.leftLabel CopyLabel.scan : CopiesLabel)
    ((((false, ((), none)), false), false) : PrefixControl)
    (((false, ((), none)), false), false)
    ((((), none), ((), none)) : CopiesControl)
    (((), none), ((), none))
    (initial n r a q k w ell) (offsetDone n r a q k w ell)
    (operandsReady n r a q k w ell)
    tp tc (by simpa only [prefixProgram] using hrp)
    (by simpa only [copiesProgram] using hrc)
  obtain ⟨ta, hta, hra⟩ := label_run n r a q k w ell
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    setupProgram labelProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))) :
        SetupLabel)
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer :
      SourceLabelAddressMachine.Label)
    (((((false, ((), none)), false), false),
      (((), none), ((), none))) : SetupControl)
    ((((false, ((), none)), false), false), (((), none), ((), none)))
    ((false, (SourceLabelAddressMachine.counter.initial, none)) :
      SourceLabelAddressMachine.Control)
    (false, (SourceLabelAddressMachine.counter.initial, none))
    (initial n r a q k w ell) (operandsReady n r a q k w ell)
    (addressed n r a q k w ell)
    tu ta (by simpa only [setupProgram] using hru)
    (by simpa only [labelProgram] using hra)
  refine ⟨t, ?_, ?_⟩
  · dsimp [cost] at *
    omega
  · simpa only [program] using hr

end EthInapproximability.CurrentPaper.SourceClauseRowUnitAddress
