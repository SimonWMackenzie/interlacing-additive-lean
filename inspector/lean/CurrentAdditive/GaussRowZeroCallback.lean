import CurrentAdditive.GaussRawZeroCheck
import CurrentAdditive.PreservingV2Run
import CurrentAdditive.LargeContextListSchedulerRun
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! One fixed Fin32 callback for a row selected by the contextual list
scheduler. It copies the saved column index, selects that cell from the row,
tests its RawRat numerator for zero, appends the nonzero bit on bank 9, then
clears callback scratch. The physical run theorem is developed separately. -/

namespace CurrentAdditive.GaussRowZeroCallback

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext

abbrev Stack := Fin 32
noncomputable abbrev Z := CurrentAdditive.GaussRawZeroCheck.machine

theorem zero_stack_cap : Z.stackCount ≤ 15 := by decide

def cellSlot : PreservingV2Program.Stack ↪ Stack where
  toFun j := ![15, 16, 17, 18, 19, 20, 21, 23, 6, 22] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

noncomputable def zeroSmall (j : Fin Z.stackCount) : Fin 15 :=
  ⟨j.val, by have h := zero_stack_cap; have hj := j.isLt; omega⟩

noncomputable def zeroPerm : Fin 15 ≃ Fin 15 :=
  Equiv.swap (zeroSmall Z.input) 6

noncomputable def zeroSlot : Fin Z.stackCount ↪ Stack where
  toFun j := ⟨15 + (zeroPerm (zeroSmall j)).val, by
    have h := (zeroPerm (zeroSmall j)).isLt
    omega⟩
  inj' := by
    intro a b h
    have hv := congrArg (fun k : Stack => k.val) h
    have hp : zeroPerm (zeroSmall a) = zeroPerm (zeroSmall b) := by
      apply Fin.ext
      simpa only [Nat.add_left_cancel_iff] using hv
    have hs := zeroPerm.injective hp
    exact Fin.ext (by simpa [zeroSmall] using congrArg Fin.val hs)

theorem zero_input_slot : zeroSlot Z.input = 21 := by
  apply Fin.ext
  simp [zeroSlot, zeroPerm, zeroSmall]

def preclearBank : Fin 14 → Stack :=
  ![15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29]

def clearBank : Fin 15 → Stack :=
  ![15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

structure Base where
  get : PreservingV2Program.Control
  zero : Fin Z.controlCount
  copy : Unit × Option Bool

noncomputable def baseEquiv : Base ≃
    PreservingV2Program.Control × Fin Z.controlCount × (Unit × Option Bool) where
  toFun b := (b.get, b.zero, b.copy)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv := by intro b; cases b; rfl
  right_inv := by intro t; rcases t with ⟨p, z, c⟩; rfl

noncomputable instance : DecidableEq Base := Classical.decEq _
noncomputable instance : Fintype Base := Fintype.ofEquiv _ baseEquiv.symm

abbrev Control := Base × Option Bool

inductive Admin where
  | afterCopy | afterGet | preclear (j : Fin 14) | finishPreclear
  | afterPreclear | afterZero | clear (j : Fin 15) | finishClear | done
  deriving DecidableEq, Fintype

abbrev Label := SourceClausePreservingBroadcast.Label ⊕
  (PreservingV2Program.Label ⊕ (Fin Z.labelCount ⊕ Admin))
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def bLabel (l : SourceClausePreservingBroadcast.Label) : Label := .inl l
def pLabel (l : PreservingV2Program.Label) : Label := .inr (.inl l)
def zLabel (l : Fin Z.labelCount) : Label := .inr (.inr (.inl l))
def aLabel (l : Admin) : Label := .inr (.inr (.inr l))

noncomputable def initialBase : Base :=
  ⟨PreservingV2Program.copyControl ((), none), Z.initial, ((), none)⟩

noncomputable def pControl (v : PreservingV2Program.Control) : Control :=
  (⟨v, Z.initial, ((), none)⟩, none)
noncomputable def zControl (v : Fin Z.controlCount) : Control :=
  (⟨PreservingV2Program.copyControl ((), none), v, ((), none)⟩, none)
noncomputable def bControl (v : Unit × Option Bool) : Control :=
  (⟨PreservingV2Program.copyControl ((), none), Z.initial, v⟩, none)

def nextPreclear (j : Fin 14) : Admin :=
  if h : j.val + 1 < 14 then .preclear ⟨j.val + 1, h⟩
  else .finishPreclear

def nextClear (j : Fin 15) : Admin :=
  if h : j.val + 1 < 15 then .clear ⟨j.val + 1, h⟩
  else .finishClear

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) bLabel bControl (fun v => v.1.copy)
      (some (aLabel .afterCopy))
      (SourceClausePreservingBroadcast.program (12 : Stack) 24 [23] l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt
      cellSlot pLabel pControl (fun v => v.1.get)
      (some (aLabel .afterGet)) (PreservingV2Program.program l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt
      zeroSlot zLabel zControl (fun v => v.1.zero)
      (some (aLabel .afterZero)) (Z.program l)
  | .inr (.inr (.inr .afterCopy)) =>
      load (fun _ => pControl (PreservingV2Program.copyControl ((), none)))
        (goto (fun _ => pLabel (.inl .scan)))
  | .inr (.inr (.inr .afterGet)) => goto (fun _ => aLabel (.preclear 0))
  | .inr (.inr (.inr (.preclear j))) =>
      BitMachineClearBank.clearStep (preclearBank j)
        (aLabel (.preclear j)) (aLabel (nextPreclear j))
  | .inr (.inr (.inr .finishPreclear)) =>
      BitMachineClearBank.finishStep id (aLabel .afterPreclear)
  | .inr (.inr (.inr .afterPreclear)) =>
      load (fun _ => zControl Z.initial) (goto (fun _ => zLabel Z.start))
  | .inr (.inr (.inr .afterZero)) =>
      pop (zeroSlot Z.output) (fun v b => (v.1, b))
        (push 9 (fun v => !(v.2.getD true))
          (load (fun v => (v.1, none)) (goto (fun _ => aLabel (.clear 0)))))
  | .inr (.inr (.inr (.clear j))) =>
      BitMachineClearBank.clearStep (clearBank j)
        (aLabel (.clear j)) (aLabel (nextClear j))
  | .inr (.inr (.inr .finishClear)) =>
      BitMachineClearBank.finishStep id (aLabel .done)
  | .inr (.inr (.inr .done)) => halt

theorem finite_program :
    Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end CurrentAdditive.GaussRowZeroCallback
