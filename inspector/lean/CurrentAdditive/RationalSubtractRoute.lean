import CurrentAdditive.RationalFlatPad32
import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
Physical 32-bank operand routing. The input is the nested pair flattened into
slots 0,1,2 and 6,7,8. Seven source-preserving copies fill the product
operands and sign slots. A final destructive transfer reverses the first
denominator into the third-product multiplicand position.
-/

namespace EthInapproximability.CurrentPaper.RationalSubtractRoute

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open RationalSubtractCore

def copySlots : Fin 7 → (Fin 3 ↪ Fin 32)
  | 0 => ⟨![0,24,26], by decide⟩
  | 1 => ⟨![6,25,26], by decide⟩
  | 2 => ⟨![1,3,26], by decide⟩
  | 3 => ⟨![7,9,26], by decide⟩
  | 4 => ⟨![2,10,26], by decide⟩
  | 5 => ⟨![8,4,26], by decide⟩
  | 6 => ⟨![8,16,26], by decide⟩

inductive Label where
  | preclear (phase : Fin 3)
  | copy (phase : Fin 7) (loc : BitMachineCopy.Label)
  | reverseDen | clear (phase : Fin 6) | done
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool
def initial : Control := ((), none)
def start : Label := .preclear 0
def copyStart : Label := .copy 0 .scan

def preSlots : Fin 2 → Fin 32 := ![15,26]

def next (phase : Fin 7) : Label :=
  if h : phase.val < 6 then .copy ⟨phase.val+1, by omega⟩ .scan
  else .reverseDen

def clearSlots : Fin 5 → Fin 32 := ![0,1,6,7,8]

def program : Label → TM2.Stmt (fun _ : Fin 32 => Bool) Label Control
  | .preclear phase =>
      if h : phase.val < 2 then
        BitMachineClearBank.clearStep
          (preSlots ⟨phase.val, h⟩) (.preclear phase)
          (.preclear ⟨phase.val+1, by omega⟩)
      else BitMachineClearBank.finishStep id copyStart
  | .copy phase loc =>
      BitMachineStackEmbedding.stmt (copySlots phase) (Label.copy phase)
        (fun v => ((), v)) Prod.snd (some (next phase))
        (BitMachineCopy.program loc)
  | .reverseDen =>
      BitMachineBroadcast.scanStep 2 15 .reverseDen (.clear 0)
  | .clear phase =>
      if h : phase.val < 5 then
        BitMachineClearBank.clearStep
          (clearSlots ⟨phase.val, h⟩) (.clear phase)
          (.clear ⟨phase.val+1, by omega⟩)
      else BitMachineClearBank.finishStep id .done
  | .done => .load (fun _ => initial) halt

noncomputable def copied (phase : Fin 7) (S : Bank) : Bank :=
  bank (copySlots phase) S
    (BitMachineCopy.stackContents
      (S (copySlots phase 0))
      (S (copySlots phase 0) ++ S (copySlots phase 1)) [])

theorem copied_scratch (phase : Fin 7) (S : Bank) :
    copied phase S 26 = [] := by
  have h : copySlots phase 2 = (26 : Fin 32) := by fin_cases phase <;> rfl
  rw [← h, copied, bank_at]
  rfl

theorem copy_run (phase : Fin 7) (S : Bank) (hs : S 26 = []) :
    ∃ t ≤ 2*(S (copySlots phase 0)).length+2,
      ((advance program)^[t])
        (⟨some (.copy phase .scan), initial, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨some (next phase), initial, copied phase S⟩ := by
  let ι := copySlots phase
  let localBank : Fin 3 → List Bool :=
    BitMachineCopy.stackContents (S (ι 0)) (S (ι 1)) []
  have hlocal : bank ι S localBank = S := by
    apply bank_eq_self
    intro k
    fin_cases k
    · rfl
    · rfl
    · simpa [localBank, BitMachineCopy.stackContents,
        show ι 2 = (26 : Fin 32) by fin_cases phase <;> rfl] using hs.symm
  have hc : (((advance BitMachineCopy.program)^[2*(S (ι 0)).length+2])
      (⟨some .scan, none, localBank⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool))).l =
      none := by
    rw [show localBank = BitMachineCopy.stackContents (S (ι 0)) (S (ι 1)) [] from rfl]
    have h := BitMachineCopy.run_correct none (S (ι 0)) (S (ι 1))
    simpa only [BitMachineCopy.run, BitMachineCopy.cfg] using congrArg
      (fun c : TM2.Cfg (fun _ : Fin 3 => Bool)
        BitMachineCopy.Label (Option Bool) => c.l) h
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs ι S
    (Label.copy phase) (fun v : Option Bool => ((),v)) Prod.snd
    (by intro v; rfl) (some (next phase))
    BitMachineCopy.program program (by intro l; rfl)
    (⟨some .scan, none, localBank⟩ :
      TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool))
    (2*(S (ι 0)).length+2) hc
  have hrun := BitMachineCopy.run_correct none (S (ι 0)) (S (ι 1))
  simp only [BitMachineCopy.run, BitMachineCopy.cfg] at hrun
  rw [hrun] at hr
  refine ⟨t,ht,?_⟩
  simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, hlocal, initial, copied, ι, localBank] using hr

end EthInapproximability.CurrentPaper.RationalSubtractRoute
