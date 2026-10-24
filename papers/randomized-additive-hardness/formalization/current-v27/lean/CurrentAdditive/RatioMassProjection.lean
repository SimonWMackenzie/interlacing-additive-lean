import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.BankFieldProjection
import CurrentAdditive.CodeDSourceCodecV2

/-! Actual mass-field projection from a V2 source entry. The entry uses
an internal BankCodec packet, so its mass is projected by the literal bank
parser. This does not confuse the outer V2 list framing with internal fields. -/

noncomputable section

namespace CurrentAdditive.RatioMassProjection

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev W := BankFieldProjection.machine (1 : Fin 2)

theorem five_stacks : W.stackCount = 5 := by
  simp [W,BankFieldProjection.machine,BitMachineEncoding.ofFinite]

abbrev Stack (n : Nat) := MachineInvokeCore.StackN n

def embedded (n : Nat) (i : Fin W.stackCount) : Stack n :=
  ⟨16 + i.val, by
    have hi : i.val < 5 := by simpa only [five_stacks] using i.isLt
    omega⟩

theorem embedded_injective (n : Nat) : Function.Injective (embedded n) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 16 + a.val = 16 + b.val at hv
  omega

def slots (n : Nat) : MachineInvokeCore.Slots W n where
  machine := ⟨embedded n, embedded_injective n⟩
  source := ⟨6, by omega⟩
  target := ⟨24, by omega⟩
  scratch := ⟨31, by omega⟩
  source_target := by intro h; have hv := congrArg Fin.val h; change 6 = 24 at hv; omega
  source_scratch := by intro h; have hv := congrArg Fin.val h; change 6 = 31 at hv; omega
  target_scratch := by intro h; have hv := congrArg Fin.val h; change 24 = 31 at hv; omega
  source_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 6 = 16 + i.val at hv
    have hi : i.val < 5 := by simpa only [five_stacks] using i.isLt
    omega
  target_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 24 = 16 + i.val at hv
    have hi : i.val < 5 := by simpa only [five_stacks] using i.isLt
    omega
  scratch_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 31 = 16 + i.val at hv
    have hi : i.val < 5 := by simpa only [five_stacks] using i.isLt
    omega

def program (n : Nat) := MachineInvokeFull.program (slots n)

def clock (word : List Bool) : Nat :=
  MachineInvokeFull.uniformBound W word (8*(word.length+1))

theorem outputs (n : Nat) (S : Stack n → List Bool) (word : List Bool)
    (h6 : S (slots n).source = word) (h24 : S (slots n).target = [])
    (h31 : S (slots n).scratch = [])
    (hblank : ∀ i,S ((slots n).machine i) = []) :
    ∃ t ≤ clock word,
      ((advance (program n))^[t])
        (⟨some (MachineInvokeFull.start (slots n)),
          MachineInvokeFull.control (slots n),S⟩ :
          TM2.Cfg (fun _ : Stack n => Bool) _ _) =
        ⟨none,MachineInvokeFull.control (slots n),
          Function.update S (slots n).target (BankFieldProjection.result (1 : Fin 2) word)⟩ := by
  exact MachineInvokeFull.invoke_run_uniform (slots n) S word
    (BankFieldProjection.result (1 : Fin 2) word) (8*(word.length+1))
    h6 h24 h31 hblank (BankFieldProjection.outputs (1 : Fin 2) word)

theorem result_entry (entry : CodeDSourceCodecV2.Entry) :
    BankFieldProjection.result (1 : Fin 2) (CodeDSourceCodecV2.encodeEntry entry) =
      CodeDCodec.encodeRawRat entry.weight := by
  simp [CodeDSourceCodecV2.encodeEntry]

#print axioms outputs
#print axioms result_entry
end CurrentAdditive.RatioMassProjection
