import CurrentAdditive.CodeDZeroSelectionV2

/-!
The byte-exact target for a later physical source-list compactor.  The input
items here are already the post-update Bank2 entries: a retained item must
keep the original word paired with its *updated* rational weight.

This file specifies the target and proves its codec and ordered-selection
properties.  It does not define or certify a physical compaction machine.
-/

namespace CurrentAdditive.CodeDZeroCompactSpecV2

open CodeDSourceCodecV2

def keepByte (item : List Bool) : Bool :=
  decide (CodeDZeroEntryV2.result item = [false])

def selectedBytes (items : List (List Bool)) : List (List Bool) :=
  items.filter keepByte

def output (items : List (List Bool)) : List Bool :=
  CodeDCodecV2.encodeItems (selectedBytes items)

theorem decode_output (items : List (List Bool)) :
    CodeDCodecV2.decodeItems (output items) = some (selectedBytes items) := by
  exact CodeDCodecV2.decodeItems_encodeItems _

theorem encoded_entries_selected (entries : List Entry) :
    selectedBytes (entries.map encodeEntry) =
      (entries.filter CodeDZeroSelectionV2.keepByFlag).map encodeEntry := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, selectedBytes, List.filter_cons,
        CodeDZeroSelectionV2.keepByFlag, keepByte] at *
      split <;> simp_all

theorem output_exact_positive (entries : List Entry)
    (hvalid : ∀ e ∈ entries, e.weight.Valid)
    (hnonneg : ∀ e ∈ entries, 0 ≤ e.weight.value) :
    output (entries.map encodeEntry) =
      CodeDSourceCodecV2.encodeSource
        (entries.filter CodeDZeroSelectionV2.keepPositive) := by
  rw [CodeDSourceCodecV2.encodeSource, output, encoded_entries_selected,
    CodeDZeroSelectionV2.selected_entries_exact entries hvalid hnonneg]

theorem selected_sublist (items : List (List Bool)) :
    List.Sublist (selectedBytes items) items := List.filter_sublist

theorem selected_count_le (items : List (List Bool)) :
    (selectedBytes items).length ≤ items.length :=
  (selected_sublist items).length_le

theorem decode_count_header (items : List (List Bool)) :
    CodeDCodecV2.decodeItems (output items) = some (selectedBytes items) ∧
    output items = EthInapproximability.CurrentPaper.EncodedCommunication.natField
      (selectedBytes items).length ++
      EthInapproximability.CurrentPaper.SourceListEncoding.fields
        (selectedBytes items) := by
  constructor
  · exact decode_output items
  · rfl

#print axioms decode_output
#print axioms encoded_entries_selected
#print axioms output_exact_positive
#print axioms selected_count_le
#print axioms decode_count_header

end CurrentAdditive.CodeDZeroCompactSpecV2
