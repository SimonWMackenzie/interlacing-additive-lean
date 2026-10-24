import CurrentAdditive.CodeDZeroListClockV2

/-!
Semantic target for the physical list compactor.  On nonnegative updated
weights, retaining entries whose physical zero flag is false is exactly the
strictly-positive deletion used by SequentialCode.  This file does not claim
the compactor machine exists.
-/

namespace CurrentAdditive.CodeDZeroSelectionV2

open CodeDSourceCodecV2

def keepByFlag (e : Entry) : Bool :=
  decide (CodeDZeroEntryV2.result (encodeEntry e) = [false])

def keepPositive (e : Entry) : Bool := decide (0 < e.weight.value)

theorem keepByFlag_eq_positive (e : Entry) (hv : e.weight.Valid)
    (hnonneg : 0 ≤ e.weight.value) :
    keepByFlag e = keepPositive e := by
  have hz := CodeDZeroEntryV2.zero_flag_iff_value e hv
  by_cases hzero : e.weight.value = 0
  · have hf := hz.mpr hzero
    simp [keepByFlag, keepPositive, hf, hzero]
  · have hpos : 0 < e.weight.value := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have hnot : CodeDZeroEntryV2.result (encodeEntry e) ≠ [true] := by
      intro h
      exact hzero (hz.mp h)
    unfold keepByFlag keepPositive CodeDZeroEntryV2.result at *
    cases hb : (!(CodeDZeroEntryV2.numeratorWord (encodeEntry e)).any id) <;>
      simp_all

theorem selected_entries_exact (entries : List Entry)
    (hvalid : ∀ e ∈ entries, e.weight.Valid)
    (hnonneg : ∀ e ∈ entries, 0 ≤ e.weight.value) :
    entries.filter (fun e => keepByFlag e) =
      entries.filter (fun e => keepPositive e) := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      have he := keepByFlag_eq_positive e (hvalid e (by simp))
        (hnonneg e (by simp))
      have hv : ∀ x ∈ rest, x.weight.Valid := by
        intro x hx; exact hvalid x (by simp [hx])
      have hn : ∀ x ∈ rest, 0 ≤ x.weight.value := by
        intro x hx; exact hnonneg x (by simp [hx])
      simp only [List.filter_cons, he, ih hv hn]

#print axioms keepByFlag_eq_positive
#print axioms selected_entries_exact

end CurrentAdditive.CodeDZeroSelectionV2
