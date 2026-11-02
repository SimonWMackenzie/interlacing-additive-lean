import CurrentAdditive.CodeDTargetV2
import CurrentAdditive.CodeDCompactJoinV2
import CurrentAdditive.CodeDZeroCompactSpecV2
import CurrentAdditive.LabelTrace

/-! Exact transport of the physical zero compactor to arbitrary Nat alphabet
labels. The label field is retained byte for byte, without a tuple codec. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace CurrentAdditive.CodeDAlphabetCompact
open EthInapproximability.CurrentPaper BitMachineBankCodec
open CodeDCanonicalSourceV2 CodeDCodec CodeDSourceCodecV2 CodeDTargetV2 LabelTrace

theorem numerator_alphabetEntry (entry : Nat × ℚ) :
    CodeDZeroEntryV2.numeratorWord (alphabetEntry entry) = (rawOfRat entry.2).numerator := by
  simp [CodeDZeroEntryV2.numeratorWord,CodeDZeroEntryV2.weightPacket,alphabetEntry,
    BankFieldProjection.result_encode,encodeRawRat,rawRatBank]

theorem keepByte_alphabetEntry (entry : Nat × ℚ) (hn : 0 ≤ entry.2) :
    CodeDZeroCompactSpecV2.keepByte (alphabetEntry entry)=decide (0 < entry.2) := by
  let e : Entry := ⟨[],rawOfRat entry.2⟩
  have hr : CodeDZeroEntryV2.result (alphabetEntry entry)=CodeDZeroEntryV2.result (encodeEntry e) := by
    simp only [CodeDZeroEntryV2.result,numerator_alphabetEntry,CodeDZeroEntryV2.numerator_encodeEntry]
    rfl
  have hp := CodeDZeroSelectionV2.keepByFlag_eq_positive e (rawOfRat_valid entry.2)
    (by simpa only [e,rawOfRat_value] using hn)
  simpa only [CodeDZeroCompactSpecV2.keepByte,hr,CodeDZeroSelectionV2.keepByFlag,
    CodeDZeroSelectionV2.keepPositive,e,rawOfRat_value] using hp

theorem positiveLaw_toList (alphabet : Array (Nat × ℚ)) :
    (positiveLaw alphabet).toList=alphabet.toList.filter (fun e => decide (0 < e.2)) := by
  let g : Nat → Nat × ℚ := fun i => alphabet[i]?.getD default
  have hlist : alphabet.toList=(List.range alphabet.size).map g := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hb : i < alphabet.size := by simpa using hi
      simp [g,hb]
  unfold positiveLaw SequentialZeroDeletion.retainedSource SequentialCode.positiveIndices
  simp only [Array.size_map,List.toList_toArray]
  rw [hlist,List.filter_map]
  have hp : (List.range alphabet.size).filter (fun i => decide (0 < (alphabet.map Prod.snd)[i]?.getD 0))=
      (List.range alphabet.size).filter (fun i => decide (0 < (g i).2)) := by
    apply List.filter_congr
    intro i hi
    have hb := List.mem_range.mp hi
    simp [g,hb]
  rw [hp]
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro i hi
  have hb := List.mem_range.mp (List.mem_filter.mp hi).1
  simp [g,hb]

theorem selected_alphabet (xs : List (Nat × ℚ)) (hn : ∀ e ∈ xs,0 ≤ e.2) :
    CodeDZeroCompactSpecV2.selectedBytes (xs.map alphabetEntry)=
      (xs.filter (fun e => decide (0 < e.2))).map alphabetEntry := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    have he := keepByte_alphabetEntry e (hn e (by simp))
    have ht := ih (by intro x hx;exact hn x (by simp [hx]))
    unfold CodeDZeroCompactSpecV2.selectedBytes at ht ⊢
    simp only [List.map_cons,List.filter_cons,he]
    split <;> simp only [List.map_cons,ht]

theorem output_exact (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true) :
    CodeDCompactJoinV2.output (alphabet.toList.map alphabetEntry)=alphabetBytes (positiveLaw alphabet) := by
  have hn : ∀ e ∈ alphabet.toList,0 ≤ e.2 := by
    intro e he
    obtain ⟨i,hi,hie⟩ := List.mem_iff_getElem.mp he
    have hb : i < alphabet.size := by simpa using hi
    have h := (Array.all_eq_true.mp hnonneg) i hb
    rw [← hie]
    simpa using h
  unfold CodeDCompactJoinV2.output CodeDZeroCompactSpecV2.output alphabetBytes
  rw [selected_alphabet _ hn,positiveLaw_toList]

theorem outputs (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true) :
    CodeDCompactJoinV2.machine.OutputsWithin (alphabetBytes alphabet)
      (alphabetBytes (positiveLaw alphabet))
      (CodeDCompactJoinV2.clock (alphabet.toList.map alphabetEntry)) := by
  have h := CodeDCompactJoinV2.outputs (alphabet.toList.map alphabetEntry)
  rw [output_exact alphabet hnonneg] at h
  exact h

#print axioms output_exact
#print axioms outputs
end CurrentAdditive.CodeDAlphabetCompact
