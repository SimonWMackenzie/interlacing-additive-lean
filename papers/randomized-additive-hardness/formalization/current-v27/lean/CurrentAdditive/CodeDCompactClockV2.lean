import CurrentAdditive.CodeDCompactJoinV2
import CurrentAdditive.CodeDZeroListClockV2
import EthInapproximability.CurrentPaper.SourceListMachineWork
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! Separate clock certificate for the frozen physical zero compactor. -/

namespace CurrentAdditive.CodeDCompactClockV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

noncomputable def itemTime (L : Nat) : Nat :=
  2*L+2 + 1 + 24*(L+1)+1 +
    (UnaryBinaryEncoding.coefficient+7)*(L+1)^2

def itemOutput (L : Nat) : Nat := 3*(L+1)

noncomputable def itemEnvelope (L : Nat) : Nat :=
  20*(L+1)*(L+1)+itemTime L+4*L+itemOutput L+
    CodeDKeepEntryV2.machine.stackCount*
      (L+itemTime L*CodeDKeepEntryV2.machine.pushBound+1)+9

noncomputable def bodyListBound (N L : Nat) : Nat :=
  N*(itemEnvelope L+4*(N+1)+7+itemOutput L)+11*(N+1)+17

def bodyOutputBound (N L : Nat) : Nat :=
  2*N+1+N*itemOutput L

noncomputable def bodyClockBound (N L : Nat) : Nat :=
  bodyListBound N L+4*bodyOutputBound N L+5

theorem item_time_le (x : List Bool) (L : Nat) (hL : x.length ≤ L) :
    CodeDKeepEntryV2.clock x ≤ itemTime L := by
  have hz := CodeDZeroEntryV2.clock_le_linear x
  have hp : (x.length+1)^2 ≤ (L+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hp' := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient+7) hp
  unfold CodeDKeepEntryV2.clock itemTime
  omega

theorem item_output_le (x : List Bool) (L : Nat) (hL : x.length ≤ L) :
    (CodeDKeepEntryV2.result x).length ≤ itemOutput L := by
  rw [CodeDCompactBodyV2.item_result]
  split
  · have hn := EncodedGraph.natField_length_upper x.length
    simp only [List.length_append]
    unfold itemOutput
    omega
  · simp [itemOutput]

theorem body_list_clock_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    CodeDCompactBodyV2.listClock items ≤ bodyListBound items.length L := by
  have hitem : ∀ x ∈ items,
      SourceListMachineWork.itemCost CodeDKeepEntryV2.machine x
        (CodeDKeepEntryV2.result x) (CodeDKeepEntryV2.clock x) ≤
        itemEnvelope L := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope
      CodeDKeepEntryV2.machine x (CodeDKeepEntryV2.result x)
      (CodeDKeepEntryV2.clock x) L (itemOutput L) (itemTime L)
      (hL x hx) (item_output_le x L (hL x hx))
      (item_time_le x L (hL x hx))
  have hout : ∀ x ∈ items,
      (CodeDKeepEntryV2.result x).length ≤ itemOutput L := by
    intro x hx
    exact item_output_le x L (hL x hx)
  have hdigits : items.length.bits.length ≤ items.length+1 := by
    have hb := UnaryBinaryEncoding.bits_length_le items.length
    omega
  have h := SourceListMachineOuter.canonicalBound_le_source
    CodeDKeepEntryV2.machine items CodeDKeepEntryV2.result
    CodeDKeepEntryV2.clock items.length (fun n => n) (fun n => n+1)
    (fun _ => itemEnvelope L) (fun _ => itemOutput L)
    (le_refl _) hdigits hitem hout
  simpa only [CodeDCompactBodyV2.listClock, bodyListBound] using h

theorem body_output_length_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    (CodeDCompactBodyV2.listOutput items).length ≤
      bodyOutputBound items.length L := by
  have hout : ∀ x ∈ items,
      (CodeDKeepEntryV2.result x).length ≤ itemOutput L := by
    intro x hx
    exact item_output_le x L (hL x hx)
  have hj := SourceListMachineOuter.joined_length_le items
    CodeDKeepEntryV2.result (itemOutput L) hout
  have hn := EncodedGraph.natField_length_upper items.length
  unfold CodeDCompactBodyV2.listOutput bodyOutputBound
  simp only [List.length_append]
  omega

theorem body_clock_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    CodeDCompactBodyV2.clock items ≤ bodyClockBound items.length L := by
  have hc := body_list_clock_le items L hL
  have ho := body_output_length_le items L hL
  unfold CodeDCompactBodyV2.clock bodyClockBound
  omega

noncomputable def flagItemEnvelope : Nat :=
  20*2*2+1+4+1+
    CodeDKeepFlagV2.itemMachine.stackCount*
      (1+CodeDKeepFlagV2.itemMachine.pushBound+1)+9

noncomputable def keepMarkedBound (N : Nat) : Nat :=
  N*(flagItemEnvelope+4*(N+1)+8)+11*(N+1)+17

def keepMarkedOutputBound (N : Nat) : Nat := 3*N+1

noncomputable def keepFlagClockBound (N : Nat) : Nat :=
  keepMarkedBound N+4*keepMarkedOutputBound N+5

theorem flag_result_length_le (x : List Bool) :
    (CodeDKeepFlagV2.result x).length ≤ 1 := by
  by_cases h : x.head? = some false <;>
    simp [CodeDKeepFlagV2.result, h]

theorem keep_marked_clock_le (flags : List (List Bool))
    (hflags : ∀ x ∈ flags, x.length ≤ 1) :
    CodeDKeepFlagV2.markedClock flags ≤
      keepMarkedBound flags.length := by
  have hitem : ∀ x ∈ flags,
      SourceListMachineWork.itemCost CodeDKeepFlagV2.itemMachine x
        (CodeDKeepFlagV2.result x) 1 ≤ flagItemEnvelope := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope
      CodeDKeepFlagV2.itemMachine x (CodeDKeepFlagV2.result x)
      1 1 1 1 (hflags x hx) (flag_result_length_le x) le_rfl
  have hout : ∀ x ∈ flags,
      (CodeDKeepFlagV2.result x).length ≤ 1 := by
    intro x _
    exact flag_result_length_le x
  have hdigits : flags.length.bits.length ≤ flags.length+1 := by
    have hb := UnaryBinaryEncoding.bits_length_le flags.length
    omega
  have h := SourceListMachineOuter.canonicalBound_le_source
    CodeDKeepFlagV2.itemMachine flags CodeDKeepFlagV2.result
    (fun _ => 1) flags.length (fun n => n) (fun n => n+1)
    (fun _ => flagItemEnvelope) (fun _ => 1)
    (le_refl _) hdigits hitem hout
  simpa only [CodeDKeepFlagV2.markedClock, keepMarkedBound] using h

theorem keep_marked_output_le (flags : List (List Bool)) :
    (CodeDKeepFlagV2.markedOutput flags).length ≤
      keepMarkedOutputBound flags.length := by
  have hj := SourceListMachineOuter.joined_length_le flags
    CodeDKeepFlagV2.result 1 (by intro x _; exact flag_result_length_le x)
  have hn := EncodedGraph.natField_length_upper flags.length
  unfold CodeDKeepFlagV2.markedOutput keepMarkedOutputBound
  simp only [List.length_append]
  omega

theorem keep_flag_clock_le (flags : List (List Bool))
    (hflags : ∀ x ∈ flags, x.length ≤ 1) :
    CodeDKeepFlagV2.clock flags ≤
      keepFlagClockBound flags.length := by
  have hc := keep_marked_clock_le flags hflags
  have ho := keep_marked_output_le flags
  unfold CodeDKeepFlagV2.clock keepFlagClockBound
  omega

def zeroOutputBound (N : Nat) : Nat := 6*N+1

theorem zero_output_length_le (items : List (List Bool)) :
    (CodeDZeroListV2.output items).length ≤
      zeroOutputBound items.length := by
  have ht := SourceListEncoding.totalLength_map_le items
    CodeDZeroEntryV2.result 1 (by intro x _; simp [CodeDZeroEntryV2.result])
  have he := SourceListEncoding.encode_length
    (CodeDZeroListV2.flags items)
  unfold CodeDZeroListV2.output CodeDZeroListV2.flags
    CodeDCodecV2.encodeItems zeroOutputBound at *
  simp only [List.length_map] at *
  omega

noncomputable def headerClockBound (N L : Nat) : Nat :=
  CodeDZeroListClockV2.polynomialClock N L +
    2*zeroOutputBound N+2 + keepFlagClockBound N +
    2*N+2 + (UnaryBinaryEncoding.coefficient+7)*(N+1)^2

theorem header_clock_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    CodeDCompactHeaderV2.clock items ≤
      headerClockBound items.length L := by
  have hz := CodeDZeroListClockV2.clock_le_polynomial items L hL
  have ho := zero_output_length_le items
  have hflagLen : (CodeDCompactHeaderV2.flags items).length = items.length := by
    simp [CodeDCompactHeaderV2.flags, CodeDZeroListV2.flags]
  have hflags : ∀ x ∈ CodeDCompactHeaderV2.flags items, x.length ≤ 1 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    simp [CodeDZeroEntryV2.result]
  have hk := keep_flag_clock_le (CodeDCompactHeaderV2.flags items) hflags
  rw [hflagLen] at hk
  have hu : (CodeDCompactHeaderV2.unary items).length ≤ items.length := by
    rw [CodeDCompactHeaderV2.unary_exact]
    simpa [CodeDZeroCompactSpecV2.selectedBytes] using
      (List.length_filter_le CodeDZeroCompactSpecV2.keepByte items)
  have hp : ((CodeDCompactHeaderV2.unary items).length+1)^2 ≤
      (items.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hp' := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient+7) hp
  unfold CodeDCompactHeaderV2.clock CodeDCompactHeaderV2.flagClock
    headerClockBound
  omega

def inputBound (N L : Nat) : Nat := 3*(N*L)+3*N+1

theorem input_length_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    (CodeDCodecV2.encodeItems items).length ≤
      inputBound items.length L := by
  have ht := SourceListEncoding.totalLength_map_le items id L
    (by intro x hx; simpa using hL x hx)
  have he := SourceListEncoding.encode_length items
  have hm := Nat.mul_le_mul_left 3 ht
  simp only [List.map_id] at ht
  change (SourceListEncoding.encode items).length ≤
    inputBound items.length L
  unfold inputBound
  omega

noncomputable def bodyResultBound (N L : Nat) : Nat :=
  inputBound N L +
    bodyClockBound N L * CodeDCompactBodyV2.machine.pushBound

noncomputable def headerResultBound (N L : Nat) : Nat :=
  inputBound N L +
    headerClockBound N L * CodeDCompactHeaderV2.machine.pushBound

theorem body_result_length_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    (CodeDCompactBodyV2.output items).length ≤
      bodyResultBound items.length L := by
  have ho := BitMachine.output_length_bound
    CodeDCompactBodyV2.machine (CodeDCompactBodyV2.outputs items)
  have hi := input_length_le items L hL
  have hc := body_clock_le items L hL
  have hm := Nat.mul_le_mul_right CodeDCompactBodyV2.machine.pushBound hc
  unfold bodyResultBound
  omega

theorem header_result_length_le (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    (CodeDCompactHeaderV2.output items).length ≤
      headerResultBound items.length L := by
  have ho := BitMachine.output_length_bound
    CodeDCompactHeaderV2.machine (CodeDCompactHeaderV2.outputs items)
  have hi := input_length_le items L hL
  have hc := header_clock_le items L hL
  have hm := Nat.mul_le_mul_right CodeDCompactHeaderV2.machine.pushBound hc
  unfold headerResultBound
  omega

noncomputable def polynomialClock (N L : Nat) : Nat :=
  2*inputBound N L+2+1+
    headerClockBound N L+1+bodyClockBound N L+
    2*bodyResultBound N L+2+
    2*headerResultBound N L+2+1

theorem clock_le_polynomial (items : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ items, x.length ≤ L) :
    CodeDCompactJoinV2.clock items ≤
      polynomialClock items.length L := by
  have hi := input_length_le items L hL
  have hh := header_clock_le items L hL
  have hb := body_clock_le items L hL
  have hho := header_result_length_le items L hL
  have hbo := body_result_length_le items L hL
  unfold CodeDCompactJoinV2.clock polynomialClock
  omega

#print axioms body_clock_le
#print axioms header_clock_le
#print axioms clock_le_polynomial

end CurrentAdditive.CodeDCompactClockV2
