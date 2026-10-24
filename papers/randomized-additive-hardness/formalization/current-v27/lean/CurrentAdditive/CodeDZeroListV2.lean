import CurrentAdditive.CodeDZeroEntryV2
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-!
A physical counted-list pass that marks zero-weight source entries in their
original index order.  It deliberately retains all positions.  The later
compactor must use these flags to write the shorter source list and its new
count header.
-/

namespace CurrentAdditive.CodeDZeroListV2

open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine CodeDZeroEntryV2.machine

def flags (items : List (List Bool)) : List (List Bool) :=
  items.map CodeDZeroEntryV2.result

def output (items : List (List Bool)) : List Bool :=
  CodeDCodecV2.encodeItems (flags items)

noncomputable def clock (items : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine CodeDZeroEntryV2.machine)
    items
    (SourceListMachineOuterFramed.framedOutput CodeDZeroEntryV2.result)
    (SourceListMachineOuterFramed.framedBound
      CodeDZeroEntryV2.result CodeDZeroEntryV2.clock)

theorem outputs (items : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems items)
      (output items) (clock items) := by
  have h := SourceListMachineOuterFramed.outputsWithin
    CodeDZeroEntryV2.machine items CodeDZeroEntryV2.result
    CodeDZeroEntryV2.clock
    (by intro x _; exact CodeDZeroEntryV2.outputs x)
  simpa only [machine, output, flags, clock, CodeDCodecV2.encodeItems] using h

theorem flags_entry_values (entries : List Entry)
    (hvalid : ∀ e ∈ entries, e.weight.Valid) :
    flags (entries.map encodeEntry) =
      entries.map (fun e => [decide (e.weight.value = 0)]) := by
  unfold flags
  simp only [List.map_map]
  apply List.map_congr_left
  intro e he
  have hz := CodeDZeroEntryV2.zero_flag_iff_value e (hvalid e he)
  by_cases hzero : e.weight.value = 0
  · simpa [hzero] using hz.mpr hzero
  · have hne : CodeDZeroEntryV2.result (encodeEntry e) ≠ [true] := by
      intro h
      exact hzero (hz.mp h)
    unfold CodeDZeroEntryV2.result at hne ⊢
    cases hb : (!(CodeDZeroEntryV2.numeratorWord (encodeEntry e)).any id) <;>
      simp_all

#print axioms outputs
#print axioms flags_entry_values

end CurrentAdditive.CodeDZeroListV2
