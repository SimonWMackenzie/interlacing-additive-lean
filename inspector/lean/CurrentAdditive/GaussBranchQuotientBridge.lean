import CurrentAdditive.GaussBranchSelect

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.GaussListContext
open CurrentAdditive.CodeDPairProductTargetV2

/-- The physical branch selector's Bank2 output is exactly the input to the
first quotient stage specified for the corresponding typed cell context. -/
theorem selector_quotient_target (x : CellContext)
    (hcurrent : x.current.Valid) (hcolumn : x.column.Valid)
    (hrow : x.row.Valid) (hpivot : x.pivot.Valid) :
    quotientPacket (GaussBranchSelect.result (packet x)) =
      firstQuotientPacked (packet x) := by
  cases x with
  | mk flag current column row pivot =>
      simp only [packet]
      rw [GaussBranchSelect.result_cellPacket]
      rw [quotientPacket_pairBytes]
      · symm
        exact firstQuotientPacked_packet
          ⟨flag, current, column, row, pivot⟩ hcurrent hcolumn hrow hpivot
      · cases flag <;> assumption
      · exact hpivot

#print axioms selector_quotient_target

end CurrentAdditive.GaussPhysical
