import Paper2.YaoPhysicalSlice
import Paper2.YaoPreservedFlatSlice
import EthInapproximability.CurrentPaper.MatrixWordGather

/-! A direct fixed-control selector extractor whose output is already in
the big-endian order consumed by the previous physical entry machine. -/

namespace Paper2.YaoEntryComposition

open Paper2.YaoLowerBound Paper2.YaoLowerBound.Materialization
open EthInapproximability.CurrentPaper

theorem reverse_ofFn {A : Type*} (b : ℕ) (f : Fin b → A) :
    (List.ofFn f).reverse = List.ofFn (fun i : Fin b => f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.length_reverse, List.length_ofFn] at h₁
    simp only [List.getElem_reverse, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega

theorem actual_selector_word (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    (MatrixWordGather.word
      (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) b bits.val).reverse =
      Paper2.YaoPhysicalSlice.selectorWord t b lambda bits z g := by
  rw [MatrixWordGather.word_eq_ofFn, reverse_ofFn]
  have hv := Paper2.YaoPreservedFlatSlice.reversed_selector_value t b lambda bits z g
  have hw : MatrixMaterialization.wordCode b
      (fun i : Fin b => readTape t b lambda bits (.inl (z, g, i.rev))) =
      Paper2.CappedSampler.bitsTicketEquiv b
        (fun i => readTape t b lambda bits (.inl (z, g, i))) := by
    apply Fin.ext
    rw [← MatrixBinaryAddress.valueFrom_wordCode]
    exact hv
  have hcanon := congrArg (MatrixMaterialization.wordCode b).symm hw
  simp only [Equiv.symm_apply_apply] at hcanon
  rw [Paper2.YaoPhysicalSlice.selectorWord]
  congr 1
  funext i
  have hi := congrFun hcanon i
  have hk : Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + i.rev.val <
      bits.val.length := by
    rw [bits.property]
    exact selector_offset_lt t b lambda z g i.rev
  have he : bits.val[Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g +
      i.rev.val]?.getD false = readTape t b lambda bits (.inl (z, g, i.rev)) := by
    rw [readTape_selector]
    change bits.val[Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g +
      i.rev.val]?.getD false =
      bits.val[Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + i.rev.val]
    rw [List.getElem?_eq_getElem hk]
    rfl
  exact he.trans hi

/-- A fixed eight-stack loop both extracts the actual selector block and
physically reverses it by prepending each bit. The resulting bank is
literally the canonical word consumed by `physical_matrix_entry`. -/
theorem physical_selector_word (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    ∃ steps ≤ b *
        (3 * (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) +
          3 * bits.val.length + 10) + 1,
      MatrixWordGather.run steps
        (MatrixWordGather.cfg (some (.inr false)) false
          (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) true)
          bits.val [] (List.replicate b true)) =
        MatrixWordGather.cfg none false
          (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) true)
          bits.val (Paper2.YaoPhysicalSlice.selectorWord t b lambda bits z g) [] := by
  obtain ⟨steps, ht, hr⟩ := MatrixWordGather.gather_run b
    (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) false bits.val []
  refine ⟨steps, ht, ?_⟩
  simpa only [List.append_nil, actual_selector_word] using hr

#print axioms actual_selector_word
#print axioms physical_selector_word

end Paper2.YaoEntryComposition
