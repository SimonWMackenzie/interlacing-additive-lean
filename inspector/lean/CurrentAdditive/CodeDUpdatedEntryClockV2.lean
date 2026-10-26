import CurrentAdditive.CodeDUpdatedCompactPipeline
import EthInapproximability.CurrentPaper.SourceListMachineWork
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! A polynomial bound for the physical replacement-entry list writer. -/

namespace CurrentAdditive.CodeDUpdatedEntryClockV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem item_clock_le_linear (x : List Bool) :
    CodeDUpdatedEntryJoin.clock x ≤ 60*(x.length+1) := by
  have ho := BankFieldProjection.result_length (0 : Fin 2) x
  have hw := BankFieldProjection.result_length (0 : Fin 2)
    (CodeDUpdatedEntryFields.outerOld x)
  have ht := BankFieldProjection.result_length (1 : Fin 2) x
  have hfw := field_length (CodeDUpdatedEntryFields.oldWord x)
  have hft := field_length (CodeDUpdatedEntryFields.weightWord x)
  unfold CodeDUpdatedEntryJoin.clock
    CodeDUpdatedEntryFields.wordClock
    CodeDUpdatedEntryFields.weightClock
    CodeDUpdatedEntryFields.wordField
    CodeDUpdatedEntryFields.weightField
    CodeDUpdatedEntryFields.oldWord
    CodeDUpdatedEntryFields.outerOld
    CodeDUpdatedEntryFields.weightWord at *
  omega

noncomputable def itemResultBound (L : Nat) : Nat :=
  L + 60*(L+1)*CodeDUpdatedEntryJoin.machine.pushBound

noncomputable def frameBound (L : Nat) : Nat :=
  3*itemResultBound L+1

noncomputable def timeBound (L : Nat) : Nat :=
  60*(L+1)+2*itemResultBound L+2+
    (UnaryBinaryEncoding.coefficient+7)*(itemResultBound L+1)^2

private noncomputable def F :=
  SourceListMachineOuterFramed.itemMachine CodeDUpdatedEntryJoin.machine

noncomputable def itemEnvelope (L : Nat) : Nat :=
  20*(L+1)*(L+1)+timeBound L+4*L+frameBound L+
    F.stackCount*(L+timeBound L*F.pushBound+1)+9

noncomputable def polynomialClock (N L : Nat) : Nat :=
  N*(itemEnvelope L+4*(N+1)+7+frameBound L)+11*(N+1)+17

theorem result_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdatedEntryJoin.output x).length ≤ itemResultBound L := by
  have ho := BitMachine.output_length_bound
    CodeDUpdatedEntryJoin.machine (CodeDUpdatedEntryJoin.outputs x)
  have hc := item_clock_le_linear x
  unfold itemResultBound
  have hcm := Nat.mul_le_mul_right
    CodeDUpdatedEntryJoin.machine.pushBound hc
  have hm := Nat.mul_le_mul_right CodeDUpdatedEntryJoin.machine.pushBound
    (Nat.mul_le_mul_left 60 (Nat.add_le_add_right hL 1))
  omega

theorem framed_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (SourceListMachineOuterFramed.framedOutput
      CodeDUpdatedEntryJoin.output x).length ≤ frameBound L := by
  have hr := result_length_le x L hL
  have hf := EncodedGraph.natField_length_upper
    (CodeDUpdatedEntryJoin.output x).length
  unfold SourceListMachineOuterFramed.framedOutput frameBound
  simp only [List.length_append]
  omega

theorem framed_time_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    SourceListMachineOuterFramed.framedBound
      CodeDUpdatedEntryJoin.output CodeDUpdatedEntryJoin.clock x ≤
      timeBound L := by
  have hc := item_clock_le_linear x
  have hr := result_length_le x L hL
  have hp : ((CodeDUpdatedEntryJoin.output x).length+1)^2 ≤
      (itemResultBound L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hp' := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient+7) hp
  unfold SourceListMachineOuterFramed.framedBound timeBound
  omega

theorem clock_le_polynomial (pairs : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ pairs, x.length ≤ L) :
    CodeDUpdatedEntryList.clock pairs ≤
      polynomialClock pairs.length L := by
  have hitem : ∀ x ∈ pairs,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput
          CodeDUpdatedEntryJoin.output x)
        (SourceListMachineOuterFramed.framedBound
          CodeDUpdatedEntryJoin.output CodeDUpdatedEntryJoin.clock x) ≤
        itemEnvelope L := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope F x _ _ L
      (frameBound L) (timeBound L) (hL x hx)
      (framed_length_le x L (hL x hx))
      (framed_time_le x L (hL x hx))
  have hout : ∀ x ∈ pairs,
      (SourceListMachineOuterFramed.framedOutput
        CodeDUpdatedEntryJoin.output x).length ≤ frameBound L := by
    intro x hx
    exact framed_length_le x L (hL x hx)
  have hdigits : pairs.length.bits.length ≤ pairs.length+1 := by
    have hb := UnaryBinaryEncoding.bits_length_le pairs.length
    omega
  have h := SourceListMachineOuter.canonicalBound_le_source F pairs
    (SourceListMachineOuterFramed.framedOutput CodeDUpdatedEntryJoin.output)
    (SourceListMachineOuterFramed.framedBound
      CodeDUpdatedEntryJoin.output CodeDUpdatedEntryJoin.clock)
    pairs.length (fun n => n) (fun n => n+1)
    (fun _ => itemEnvelope L) (fun _ => frameBound L)
    (le_refl _) hdigits hitem hout
  simpa only [CodeDUpdatedEntryList.clock, polynomialClock] using h

noncomputable def pipelineClock (N L : Nat) : Nat :=
  polynomialClock N L +
    2*CodeDCompactClockV2.inputBound N (itemResultBound L)+2+
    CodeDCompactClockV2.polynomialClock N (itemResultBound L)

theorem pipeline_clock_le {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (L : Nat)
    (hL : ∀ x ∈ CodeDUpdatedEntryList.pairItems source updated,
      x.length ≤ L) :
    CodeDUpdatedCompactPipeline.clock source updated ≤
      pipelineClock (CodeDUpdatedEntryList.pairItems source updated).length L := by
  let pairs := CodeDUpdatedEntryList.pairItems source updated
  let entries := (CodeDCompactSequentialBridge.updatedEntries source updated).map
    CodeDSourceCodecV2.encodeEntry
  have hmap := CodeDUpdatedEntryList.pairItems_map_exact source updated
  have hsize : entries.length = pairs.length := by
    have hh := congrArg List.length hmap
    simp only [List.length_map] at hh
    simpa only [pairs, entries, List.length_map] using hh.symm
  have hentry : ∀ x ∈ entries, x.length ≤ itemResultBound L := by
    intro x hx
    change x ∈ (CodeDCompactSequentialBridge.updatedEntries source updated).map
      CodeDSourceCodecV2.encodeEntry at hx
    rw [← hmap] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact result_length_le p L (hL p hp)
  have hw := clock_le_polynomial pairs L hL
  have hi := CodeDCompactClockV2.input_length_le entries
    (itemResultBound L) hentry
  have hc := CodeDCompactClockV2.clock_le_polynomial entries
    (itemResultBound L) hentry
  rw [hsize] at hi hc
  change CodeDUpdatedEntryList.clock pairs +
    2*(CodeDCodecV2.encodeItems entries).length+2+
    CodeDCompactJoinV2.clock entries ≤
    polynomialClock pairs.length L+
    2*CodeDCompactClockV2.inputBound pairs.length (itemResultBound L)+2+
    CodeDCompactClockV2.polynomialClock pairs.length (itemResultBound L)
  omega

#print axioms item_clock_le_linear
#print axioms clock_le_polynomial
#print axioms pipeline_clock_le

end CurrentAdditive.CodeDUpdatedEntryClockV2
