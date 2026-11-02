import CurrentAdditive.CodeDZeroListV2
import EthInapproximability.CurrentPaper.SourceListMachineWork
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! A numerical clock for the physical zero-flag list pass. -/

namespace CurrentAdditive.CodeDZeroListClockV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

private noncomputable def F :=
  SourceListMachineOuterFramed.itemMachine CodeDZeroEntryV2.machine

def framedSize : Nat := (natField 1).length + 1

noncomputable def framedTime (L : Nat) : Nat :=
  24 * (L + 1) + 4 + (UnaryBinaryEncoding.coefficient + 7) * 4

noncomputable def itemEnvelope (L : Nat) : Nat :=
  20*(L+1)*(L+1) + framedTime L + 4*L + framedSize +
    F.stackCount*(L + framedTime L*F.pushBound + 1) + 9

noncomputable def polynomialClock (N L : Nat) : Nat :=
  N * (itemEnvelope L + 4*(N+1)+7+framedSize) + 11*(N+1)+17

theorem framedSize_exact (x : List Bool) :
    (SourceListMachineOuterFramed.framedOutput CodeDZeroEntryV2.result x).length =
      framedSize := by
  simp [SourceListMachineOuterFramed.framedOutput, framedSize,
    CodeDZeroEntryV2.result]

theorem framedTime_le (x : List Bool) (L : Nat) (hL : x.length ≤ L) :
    SourceListMachineOuterFramed.framedBound
      CodeDZeroEntryV2.result CodeDZeroEntryV2.clock x ≤ framedTime L := by
  have hc := CodeDZeroEntryV2.clock_le_linear x
  unfold SourceListMachineOuterFramed.framedBound framedTime
  simp only [CodeDZeroEntryV2.result, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd]
  omega

theorem clock_le_polynomial (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    CodeDZeroListV2.clock items ≤ polynomialClock items.length L := by
  have hitem : ∀ x ∈ items,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput CodeDZeroEntryV2.result x)
        (SourceListMachineOuterFramed.framedBound
          CodeDZeroEntryV2.result CodeDZeroEntryV2.clock x) ≤ itemEnvelope L := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope F x _ _ L framedSize
      (framedTime L) (hL x hx) (le_of_eq (framedSize_exact x))
      (framedTime_le x L (hL x hx))
  have hout : ∀ x ∈ items,
      (SourceListMachineOuterFramed.framedOutput CodeDZeroEntryV2.result x).length ≤
        framedSize := by
    intro x _
    exact le_of_eq (framedSize_exact x)
  have hdigits : items.length.bits.length ≤ items.length + 1 := by
    have hbits := UnaryBinaryEncoding.bits_length_le items.length
    omega
  have h := SourceListMachineOuter.canonicalBound_le_source F items
    (SourceListMachineOuterFramed.framedOutput CodeDZeroEntryV2.result)
    (SourceListMachineOuterFramed.framedBound
      CodeDZeroEntryV2.result CodeDZeroEntryV2.clock)
    items.length (fun n => n) (fun n => n+1)
    (fun _ => itemEnvelope L) (fun _ => framedSize)
    (le_refl _) hdigits hitem hout
  simpa only [CodeDZeroListV2.clock, polynomialClock] using h

#print axioms clock_le_polynomial

end CurrentAdditive.CodeDZeroListClockV2
