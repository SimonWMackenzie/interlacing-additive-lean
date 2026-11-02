import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-! Actual V2 length-and-payload framing inside a larger context. The source
word is retained at bank 28, the correctly length-prefixed field is installed
at bank 30, and every other ambient bank is restored. This is intentionally
different from the marker-bit fields of BitMachineBankSerialize. -/

noncomputable section

namespace CurrentAdditive.V2FieldContext

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev W := SourceListMachineWriter.framingMachine true

theorem eight_stacks : W.stackCount = 8 := rfl

abbrev Stack (n : Nat) := MachineInvokeCore.StackN n

def embedded (n : Nat) (i : Fin W.stackCount) : Stack n :=
  ⟨16 + i.val, by
    have hi : i.val < 8 := by simpa only [eight_stacks] using i.isLt
    omega⟩

theorem embedded_injective (n : Nat) : Function.Injective (embedded n) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 16 + a.val = 16 + b.val at hv
  omega

def slots (n : Nat) : MachineInvokeCore.Slots W n where
  machine := ⟨embedded n, embedded_injective n⟩
  source := ⟨28, by omega⟩
  target := ⟨30, by omega⟩
  scratch := ⟨31, by omega⟩
  source_target := by intro h; have hv := congrArg Fin.val h; change 28 = 30 at hv; omega
  source_scratch := by intro h; have hv := congrArg Fin.val h; change 28 = 31 at hv; omega
  target_scratch := by intro h; have hv := congrArg Fin.val h; change 30 = 31 at hv; omega
  source_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 28 = 16 + i.val at hv
    have hi : i.val < 8 := by simpa only [eight_stacks] using i.isLt
    omega
  target_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 30 = 16 + i.val at hv
    have hi : i.val < 8 := by simpa only [eight_stacks] using i.isLt
    omega
  scratch_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 31 = 16 + i.val at hv
    have hi : i.val < 8 := by simpa only [eight_stacks] using i.isLt
    omega

def program (n : Nat) := MachineInvokeFull.program (slots n)

def field (word : List Bool) : List Bool :=
  EncodedCommunication.natField word.length ++ word

def clock (word : List Bool) : Nat :=
  MachineInvokeFull.uniformBound W word
    ((UnaryBinaryEncoding.coefficient + 7) * (word.length + 1)^2)

theorem outputs (n : Nat) (S : Stack n → List Bool) (word : List Bool)
    (h28 : S ⟨28, by omega⟩ = word)
    (h30 : S ⟨30, by omega⟩ = [])
    (h31 : S ⟨31, by omega⟩ = [])
    (hblank : ∀ i, S ((slots n).machine i) = []) :
    ∃ t ≤ clock word,
      ((advance (program n))^[t])
        (⟨some (MachineInvokeFull.start (slots n)),
          MachineInvokeFull.control (slots n), S⟩ :
          TM2.Cfg (fun _ : Stack n => Bool) _ _) =
        ⟨none, MachineInvokeFull.control (slots n),
          Function.update S ⟨30, by omega⟩ (field word)⟩ := by
  simpa only [clock, program, slots, field, SourceListMachineWriter.result,
    Bool.true_eq_false, ↓reduceIte] using
    MachineInvokeFull.invoke_run_uniform (slots n) S word (field word)
      ((UnaryBinaryEncoding.coefficient + 7) * (word.length + 1)^2)
      h28 h30 h31 hblank
      (by simpa only [field, SourceListMachineWriter.result, Bool.true_eq_false,
        ↓reduceIte] using SourceListMachineWriter.outputs true word)

#print axioms outputs

end CurrentAdditive.V2FieldContext
