import CurrentAdditive.RationalProductCellSelect
import CurrentAdditive.CodeDPairProductTargetV2

/-! Exact byte bridge from selected outer fields to the controller's
two-rational operand packet. The choice of fields is still fixed in each
physical machine, so a pivot-row branch remains an explicit controller step. -/

namespace EthInapproximability.CurrentPaper.RationalProductCellSelectBridge

open BitMachineBankCodec RationalProductCellSelect
open CurrentAdditive.CodeDCodec CurrentAdditive.CodeDPairProductTargetV2

theorem selected_pair (a b : Fin 12) (S : Bank 12)
    (x y : RawRat)
    (ha : S a = encodeRawRat x) (hb : S b = encodeRawRat y) :
    result a b (encode S) = pairBytes x y := by
  rw [result_encode]
  unfold pairBytes
  congr 1
  funext i
  fin_cases i
  · simpa [selected, pairBank] using ha
  · simpa [selected, pairBank] using hb

theorem row_pivot_outputs (S : Bank 12) (row pivot : RawRat)
    (hr : S 3 = encodeRawRat row) (hp : S 4 = encodeRawRat pivot) :
    (machine 3 4 (by decide)).OutputsWithin (encode S)
      (pairBytes row pivot) (35*((encode S).length+1)) := by
  simpa only [selected_pair 3 4 S row pivot hr hp] using
    outputs 3 4 (by decide) (encode S)

theorem column_pivot_outputs (S : Bank 12) (column pivot : RawRat)
    (hc : S 2 = encodeRawRat column) (hp : S 4 = encodeRawRat pivot) :
    (machine 2 4 (by decide)).OutputsWithin (encode S)
      (pairBytes column pivot) (35*((encode S).length+1)) := by
  simpa only [selected_pair 2 4 S column pivot hc hp] using
    outputs 2 4 (by decide) (encode S)

theorem row_pivot_packet_length (S : Bank 12) (row pivot : RawRat)
    (hr : S 3 = encodeRawRat row) (hp : S 4 = encodeRawRat pivot) :
    (pairBytes row pivot).length ≤ 4*(encode S).length+2 := by
  have h := output_length 3 4 (encode S) S (decode_encode S)
  rw [BitMachineBankSerialize.encode,
    ← BitMachineBankCodec.encode_eq_list,
    ← result_encode, selected_pair 3 4 S row pivot hr hp] at h
  exact h

theorem column_pivot_packet_length (S : Bank 12) (column pivot : RawRat)
    (hc : S 2 = encodeRawRat column) (hp : S 4 = encodeRawRat pivot) :
    (pairBytes column pivot).length ≤ 4*(encode S).length+2 := by
  have h := output_length 2 4 (encode S) S (decode_encode S)
  rw [BitMachineBankSerialize.encode,
    ← BitMachineBankCodec.encode_eq_list,
    ← result_encode, selected_pair 2 4 S column pivot hc hp] at h
  exact h

/-- The nonpivot extraction physically retains the untouched current and
pivot-row entry in the selector's foreign bank stacks. The public machine
returns only the pair packet; a later embedded continuation can reuse these
two stacks without reconstructing their contents. -/
theorem column_pivot_retains_context (S : Bank 12) (column pivot : RawRat)
    (hc : S 2 = encodeRawRat column) (hp : S 4 = encodeRawRat pivot) :
    ∃ t ≤ 35*((encode S).length+1),
      let c := RationalProductCellSelect.run 2 4 (by decide) t
        (RationalProductCellSelect.cfg (some (.inl (.scan 0))) none
          (fun _ => []) (encode S) [] [])
      c.l = none ∧ c.stk (.inr 2) = pairBytes column pivot ∧
        c.stk (.inl 1) = S 1 ∧ c.stk (.inl 3) = S 3 := by
  obtain ⟨t,ht,hh,ho,hkeep⟩ :=
    RationalProductCellSelect.valid_run 2 4 (by decide)
      (encode S) S (decode_encode S)
  refine ⟨t,ht,hh,?_,?_,?_⟩
  · rw [BitMachineBankSerialize.encode,
      ← BitMachineBankCodec.encode_eq_list,
      ← result_encode, selected_pair 2 4 S column pivot hc hp] at ho
    exact ho
  · exact hkeep 1 (by decide) (by decide)
  · exact hkeep 3 (by decide) (by decide)

end EthInapproximability.CurrentPaper.RationalProductCellSelectBridge
