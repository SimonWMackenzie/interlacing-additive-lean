import CurrentAdditive.V39CodeDLivePacketBound

set_option autoImplicit false

namespace CurrentAdditive.V40RawLivePacketBound

open EthInapproximability.CurrentPaper
open SequentialCode SequentialSourceCode LabelTrace IntegerBitSupport
open V39CodeDLivePacketBound

private theorem payload_le_fields (xs : List (List Bool)) :
    SourceListEncoding.totalLength xs ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp [SourceListEncoding.totalLength, SourceListEncoding.fields]
  | cons x xs ih =>
      simp only [SourceListEncoding.totalLength, List.map_cons, List.sum_cons,
        SourceListEncoding.fields, List.length_append] at *
      omega

theorem entry_length_le_alphabetBytes (alphabet : Array (Nat × ℚ))
    (entry : Nat × ℚ) (he : entry ∈ alphabet) :
    (CodeDTargetV2.alphabetEntry entry).length ≤ (CodeDTargetV2.alphabetBytes alphabet).length := by
  have hmem : (CodeDTargetV2.alphabetEntry entry).length ∈
      ((alphabet.toList.map CodeDTargetV2.alphabetEntry).map List.length) := by
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨entry, Array.mem_toList_iff.mpr he, rfl⟩, rfl⟩
  have hh := List.le_sum_of_mem hmem
  have hp := payload_le_fields (alphabet.toList.map CodeDTargetV2.alphabetEntry)
  change (CodeDTargetV2.alphabetEntry entry).length ≤
    (SourceListEncoding.encode (alphabet.toList.map CodeDTargetV2.alphabetEntry)).length
  simp only [SourceListEncoding.encode, List.length_append]
  exact hh.trans (hp.trans (Nat.le_add_left _ _))

/-- Zero deletion cannot introduce an entry longer than the original packet.
The count of retained positions is charged to that same original packet. -/
theorem filtered_alphabet_length (alphabet : Array (Nat × ℚ))
    (hmass : sourceMass alphabet = 1) :
    (CodeDTargetV2.alphabetBytes (positiveLaw alphabet)).length ≤
      3 * (CodeDTargetV2.alphabetBytes alphabet).length *
        ((CodeDTargetV2.alphabetBytes alphabet).length + 1) + 1 := by
  let L := (CodeDTargetV2.alphabetBytes alphabet).length
  obtain ⟨trace, he, _⟩ := positiveLaw_trace_exact alphabet hmass
  have hentry : ∀ entry ∈ (positiveLaw alphabet).toList,
      (CodeDTargetV2.alphabetEntry entry).length ≤ L := by
    intro entry hentry
    obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hentry)
    have hs : entry = alphabet[trace ⟨i, hi⟩] := hget.symm.trans (he ⟨i, hi⟩)
    rw [hs]
    exact entry_length_le_alphabetBytes alphabet _ (Array.getElem_mem (trace ⟨i, hi⟩).isLt)
  have hs : (positiveLaw alphabet).size ≤ L :=
    (positiveLaw_size_le alphabet hmass).trans (alphabet_size_le_bytes alphabet)
  have hb := SourceListEncoding.encode_map_length_le (positiveLaw alphabet).toList
    CodeDTargetV2.alphabetEntry L hentry
  change (SourceListEncoding.encode
    ((positiveLaw alphabet).toList.map CodeDTargetV2.alphabetEntry)).length ≤ _
  exact hb.trans (by simp only [Array.length_toList]; gcongr)

def rawLivePacket (j : Nat) (alphabet : Array (Nat × ℚ))
    (current : Array ((Fin (j + 1) → Nat) × ℚ)) : List Bool :=
  BitMachineBankCodec.encode
    (![List.replicate (j + 1) true, CodeDTargetV2.alphabetBytes (positiveLaw alphabet),
      CodeDCanonicalSourceV2.encodedSource current] : Fin 3 → List Bool)

/-- The actual matrix-recomputing controller packet has one fixed polynomial
bound in the original whole input. No supplied intermediate resource bound
or machine-run premise is used. -/
theorem rawLivePacket_length_le (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (Q j : Nat) (hj : j < Q)
    (prev : Array ((Fin j → Nat) × ℚ))
    (hprev : sequentialPreprocessed D alphabet j = some prev)
    (current : Array ((Fin (j + 1) → Nat) × ℚ)) (t : Nat)
    (htrace :
      let F := generatedFeatures (j + 1) D ((positiveLaw alphabet).map Prod.fst)
      EliminationTrace F.size (fun v i => generatedFeatureValue v F[i]) t
        (appendSource prev (positiveLaw alphabet)) current) :
    (rawLivePacket j alphabet current).length ≤
      (2 * (126 * D + 1200) + 20) * ((wholeInput Q alphabet).length + 1) ^ (14 * D + 14) := by
  let X := (wholeInput Q alphabet).length + 1
  let L := (CodeDTargetV2.alphabetBytes alphabet).length
  let E := 14 * D + 14
  have hX : X = 2 * (Q + L) + 3 := by simp only [X, L, wholeInput_length]
  have hX1 : 1 ≤ X := by omega
  have hLX : L ≤ X := by omega
  have hcounter : j + 1 ≤ X := by omega
  have hX2 : X ≤ X ^ 2 := by nlinarith only [hX1]
  have hX2one : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
  have halpha : (CodeDTargetV2.alphabetBytes (positiveLaw alphabet)).length ≤ 7 * X ^ 2 := by
    calc
      _ ≤ 3 * L * (L + 1) + 1 := filtered_alphabet_length alphabet hmass
      _ ≤ 3 * X * (X + 1) + 1 := by gcongr
      _ ≤ 7 * X ^ 2 := by nlinarith only [hX2, hX2one]
  have hsource : (CodeDCanonicalSourceV2.encodedSource current).length ≤
      (126 * D + 1200) * X ^ E := by
    have hlower := BitMachineBankCodec.word_length_le_encode
      (![List.replicate (j + 1) true,
         CylinderFeatureCodec.generatedFeatureBits (j + 1) D ((positiveLaw alphabet).map Prod.fst),
         CodeDCanonicalSourceV2.encodedSource current] : Fin 3 → List Bool) 2
    have hlower' : (CodeDCanonicalSourceV2.encodedSource current).length ≤
        (livePacket D j alphabet current).length := by simpa [livePacket] using hlower
    exact hlower'.trans (livePacket_length_le D alphabet hnonneg hmass Q j hj prev hprev current t htrace)
  have hXE : X ≤ X ^ E := by simpa using Nat.pow_le_pow_right hX1 (by dsimp [E]; omega : 1 ≤ E)
  have hX2E : X ^ 2 ≤ X ^ E := Nat.pow_le_pow_right hX1 (by dsimp [E]; omega)
  have hXEone : 1 ≤ X ^ E := Nat.one_le_pow _ _ hX1
  have heq : (rawLivePacket j alphabet current).length = 2 * ((j + 1) +
      (CodeDTargetV2.alphabetBytes (positiveLaw alphabet)).length +
      (CodeDCanonicalSourceV2.encodedSource current).length) + 3 := by
    simp [rawLivePacket, BitMachineBankCodec.encode_length, Fin.sum_univ_succ, Nat.add_assoc]
  rw [heq]
  calc
    _ ≤ 2 * (X + 7 * X ^ 2 + (126 * D + 1200) * X ^ E) + 3 := by gcongr
    _ ≤ 2 * (X ^ E + 7 * X ^ E + (126 * D + 1200) * X ^ E) + 3 * X ^ E := by gcongr <;> omega
    _ ≤ (2 * (126 * D + 1200) + 20) * X ^ E := by nlinarith only [hXEone]

end CurrentAdditive.V40RawLivePacketBound
