import CurrentAdditive.V39IndependentPrefixBytes
import CurrentAdditive.FeaturePacketBound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CurrentAdditive.V39CodeDLivePacketBound

open EthInapproximability.CurrentPaper
open SequentialCode SequentialSourceCode LabelTrace IntegerBitSupport
open ZeroFilteredWeightBits V39IndependentPrefixBytes

/-- The raw fixed-degree constructor input: unary requested length, then
the original ordered rational alphabet packet. -/
def wholeInput (Q : Nat) (alphabet : Array (Nat × ℚ)) : List Bool :=
  BitMachineBankCodec.encode
    (![List.replicate Q true, CodeDTargetV2.alphabetBytes alphabet] : Fin 2 → List Bool)

/-- The three actual live fields in one independence-elimination pass. -/
def livePacket (D j : Nat) (alphabet : Array (Nat × ℚ))
    (current : Array ((Fin (j + 1) → Nat) × ℚ)) : List Bool :=
  BitMachineBankCodec.encode
    (![List.replicate (j + 1) true,
       CylinderFeatureCodec.generatedFeatureBits (j + 1) D
         ((positiveLaw alphabet).map Prod.fst),
       CodeDCanonicalSourceV2.encodedSource current] : Fin 3 → List Bool)

theorem wholeInput_length (Q : Nat) (alphabet : Array (Nat × ℚ)) :
    (wholeInput Q alphabet).length =
      2 * (Q + (CodeDTargetV2.alphabetBytes alphabet).length) + 2 := by
  simp [wholeInput, BitMachineBankCodec.encode_length, Fin.sum_univ_succ]

private theorem list_count_le_fields (xs : List (List Bool)) :
    xs.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x xs ih =>
      have hn : 1 ≤ (EncodedCommunication.natField x.length).length := by
        simp [EncodedCommunication.natField, EncodedCommunication.field_length]
      simp only [SourceListEncoding.fields, List.length_cons, List.length_append]
      omega

theorem alphabet_size_le_bytes (alphabet : Array (Nat × ℚ)) :
    alphabet.size ≤ (CodeDTargetV2.alphabetBytes alphabet).length := by
  have h := list_count_le_fields (alphabet.toList.map CodeDTargetV2.alphabetEntry)
  simpa only [List.length_map, Array.length_toList, CodeDTargetV2.alphabetBytes,
    CodeDCodecV2.encodeItems, SourceListEncoding.encode, List.length_append] using
      h.trans (Nat.le_add_left _ _)

theorem alphabet_codes_le_bytes (alphabet : Array (Nat × ℚ)) :
    ∀ entry ∈ alphabet,
      entry.1.bits.length ≤ (CodeDTargetV2.alphabetBytes alphabet).length := by
  intro entry he
  have hmem : entry.1.bits.length ∈
      (alphabet.toList.map (fun e => e.1.bits.length)) :=
    List.mem_map.mpr ⟨entry, Array.mem_toList_iff.mpr he, rfl⟩
  have hsum := List.le_sum_of_mem hmem
  have hs := FeaturePacketBound.labelBits_le_alphabetBytes alphabet
  exact hsum.trans (by simpa [FeaturePacketBound.labelBits] using hs)

private theorem filtered_codes (alphabet : Array (Nat × ℚ))
    (hmass : sourceMass alphabet = 1) :
    ∀ entry ∈ positiveLaw alphabet,
      entry.1.bits.length ≤ (CodeDTargetV2.alphabetBytes alphabet).length := by
  obtain ⟨trace, he, _⟩ := positiveLaw_trace_exact alphabet hmass
  intro entry hentry
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hentry
  have hs : entry = alphabet[trace ⟨i, hi⟩] := hget.symm.trans (he ⟨i, hi⟩)
  rw [hs]
  exact alphabet_codes_le_bytes alphabet _ (Array.getElem_mem (trace ⟨i, hi⟩).isLt)

private theorem labelBits_le (alphabet : Array (Nat × ℚ)) (U : Nat)
    (hc : ∀ entry ∈ alphabet, entry.1.bits.length ≤ U) :
    FeaturePacketBound.labelBits (alphabet.map Prod.fst) ≤ alphabet.size * U := by
  have h := SourceListEncoding.totalLength_map_le alphabet.toList
    (fun e => e.1.bits) U (by
      intro e he
      exact hc e (Array.mem_toList_iff.mp he))
  simpa [FeaturePacketBound.labelBits, SourceListEncoding.totalLength] using h

/-- Every actual live three-field packet is polynomial in the original raw
constructor input. The constants depend only on the fixed degree D. -/
theorem livePacket_length_le (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (Q j : Nat) (hj : j < Q)
    (prev : Array ((Fin j → Nat) × ℚ))
    (hprev : sequentialPreprocessed D alphabet j = some prev)
    (current : Array ((Fin (j + 1) → Nat) × ℚ)) (t : Nat)
    (htrace :
      let F := generatedFeatures (j + 1) D ((positiveLaw alphabet).map Prod.fst)
      EliminationTrace F.size (fun v i => generatedFeatureValue v F[i]) t
        (appendSource prev (positiveLaw alphabet)) current) :
    (livePacket D j alphabet current).length ≤
      (126 * D + 1200) * ((wholeInput Q alphabet).length + 1) ^ (14 * D + 14) := by
  let L := (CodeDTargetV2.alphabetBytes alphabet).length
  let X := (wholeInput Q alphabet).length + 1
  let P := (1 + Q * alphabet.size) ^ D
  let K := X ^ (2 * D + 2)
  let B := budget D Q alphabet.size L
  have hX : X = 2 * (Q + L) + 3 := by
    simp only [X, L, wholeInput_length]
  have hX1 : 1 ≤ X := by omega
  have hQX : Q ≤ X := by omega
  have hLX : L ≤ X := by omega
  have hmL : alphabet.size ≤ L := alphabet_size_le_bytes alphabet
  have hquad : 1 + Q * alphabet.size ≤ X ^ 2 := by
    have hm := Nat.mul_le_mul_left Q hmL
    rw [pow_two, hX]
    nlinarith only [hm]
  have hXK : X ≤ K := by
    simpa [K] using Nat.pow_le_pow_right hX1 (by omega : 1 ≤ 2 * D + 2)
  have hK1 : 1 ≤ K := hX1.trans hXK
  have hQ : Q ≤ K := hQX.trans hXK
  have hL : L ≤ K := hLX.trans hXK
  have hm : alphabet.size ≤ K := hmL.trans hL
  have hP : P ≤ K := by
    calc
      P ≤ (X ^ 2) ^ D := Nat.pow_le_pow_left hquad D
      _ = X ^ (2 * D) := by rw [pow_mul]
      _ ≤ K := Nat.pow_le_pow_right hX1 (by omega)
  have hPsize : Nat.size (P + 1) ≤ 2 * K := by
    have hs : Nat.size (P + 1) ≤ P + 1 :=
      Nat.size_le.mpr (P + 1).lt_two_pow_self
    omega
  have hK2 : K ^ 2 ≤ K ^ 5 := Nat.pow_le_pow_right hK1 (by omega)
  have hK5 : 1 ≤ K ^ 5 := Nat.one_le_pow _ _ hK1
  have hB : B ≤ 10 * K ^ 5 := by
    calc
      B ≤ K * K + 4 * K * K * K ^ 2 * (2 * K) + 1 := by
        change Q * L + 4 * Q * alphabet.size * P ^ 2 * Nat.size (P + 1) + 1 ≤ _
        gcongr
      _ = K ^ 2 + 8 * K ^ 5 + 1 := by ring
      _ ≤ 10 * K ^ 5 := by omega
  have hU := alphabet_codes_le_bytes alphabet
  have hsource := prefix_encodedSource_length_le D alphabet hnonneg hmass L hU
    Q j hj prev hprev current t htrace
  have hsmall : 6 * Q * (L + 1) + 8 * (2 * B + 1) + 15 ≤ 195 * K ^ 5 := by
    have hplus : L + 1 ≤ 2 * K := by omega
    calc
      6 * Q * (L + 1) + 8 * (2 * B + 1) + 15 ≤
          6 * K * (2 * K) + 8 * (2 * (10 * K ^ 5) + 1) + 15 := by gcongr
      _ = 12 * K ^ 2 + 160 * K ^ 5 + 23 := by ring
      _ ≤ 195 * K ^ 5 := by omega
  have hK7 : 1 ≤ K ^ 7 := Nat.one_le_pow _ _ hK1
  have hsource' : (CodeDCanonicalSourceV2.encodedSource current).length ≤ 586 * K ^ 7 := by
    calc
      (CodeDCanonicalSourceV2.encodedSource current).length ≤
          3 * (alphabet.size * P) * (6 * Q * (L + 1) + 8 * (2 * B + 1) + 15) + 1 := hsource
      _ ≤ 3 * (K * K) * (195 * K ^ 5) + 1 := by gcongr
      _ = 585 * K ^ 7 + 1 := by ring
      _ ≤ 586 * K ^ 7 := by omega
  let filtered := positiveLaw alphabet
  have hfiltered : filtered.size ≤ K := (positiveLaw_size_le alphabet hmass).trans hm
  have hlabels : FeaturePacketBound.labelBits (filtered.map Prod.fst) ≤ K ^ 2 := by
    have hh := labelBits_le filtered L (filtered_codes alphabet hmass)
    exact hh.trans (by nlinarith only [Nat.mul_le_mul hfiltered hL])
  have hcoord : (j + 1).bits.length ≤ K := by
    have hh : (j + 1).bits.length ≤ j + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (j + 1).lt_two_pow_self
    omega
  have hK2one : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK1
  have hKK2 : K ≤ K ^ 2 := by simpa using Nat.pow_le_pow_right hK1 (by omega : 1 ≤ 2)
  have hpair : FeaturePacketBound.pairCap (j + 1) (filtered.map Prod.fst) ≤ 6 * K ^ 2 := by
    unfold FeaturePacketBound.pairCap
    omega
  have hfeatureCount : (1 + (j + 1) * (filtered.map Prod.fst).size) ^ D ≤ K := by
    simp only [Array.size_map]
    exact (Nat.pow_le_pow_left (by
      have hh := positiveLaw_size_le alphabet hmass
      dsimp [filtered]
      gcongr; omega) D).trans hP
  have hfeature := FeaturePacketBound.packet_length_le (j + 1) D (filtered.map Prod.fst)
  have hfeature' : (CylinderFeatureCodec.generatedFeatureBits (j + 1) D
      (filtered.map Prod.fst)).length ≤ (63 * D + 7) * K ^ 3 := by
    have hinner : 3 * D * (FeaturePacketBound.pairCap (j + 1) (filtered.map Prod.fst) + 1) + 2 ≤
        (21 * D + 2) * K ^ 2 := by
      calc
        _ ≤ 3 * D * (7 * K ^ 2) + 2 * K ^ 2 := by gcongr <;> omega
        _ = (21 * D + 2) * K ^ 2 := by ring
    have hK3 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ hK1
    calc
      _ ≤ 3 * (1 + (j + 1) * (filtered.map Prod.fst).size) ^ D *
          (3 * D * (FeaturePacketBound.pairCap (j + 1) (filtered.map Prod.fst) + 1) + 2) + 1 := hfeature
      _ ≤ 3 * K * ((21 * D + 2) * K ^ 2) + 1 := by gcongr
      _ = (63 * D + 6) * K ^ 3 + 1 := by ring
      _ ≤ (63 * D + 7) * K ^ 3 := by nlinarith only [hK3]
  have hKto7 : K ≤ K ^ 7 := by simpa using Nat.pow_le_pow_right hK1 (by omega : 1 ≤ 7)
  have hK3to7 : K ^ 3 ≤ K ^ 7 := Nat.pow_le_pow_right hK1 (by omega)
  have hlive : (livePacket D j alphabet current).length ≤ (126 * D + 1200) * K ^ 7 := by
    have heq : (livePacket D j alphabet current).length =
        2 * ((j + 1) + (CylinderFeatureCodec.generatedFeatureBits (j + 1) D
          (filtered.map Prod.fst)).length + (CodeDCanonicalSourceV2.encodedSource current).length) + 3 := by
      simp [livePacket, BitMachineBankCodec.encode_length, Fin.sum_univ_succ, filtered, Nat.add_assoc]
    rw [heq]
    calc
      _ ≤ 2 * (K + (63 * D + 7) * K ^ 3 + 586 * K ^ 7) + 3 := by gcongr; omega
      _ ≤ 2 * (K ^ 7 + (63 * D + 7) * K ^ 7 + 586 * K ^ 7) + 3 * K ^ 7 := by gcongr <;> omega
      _ ≤ (126 * D + 1200) * K ^ 7 := by nlinarith only [hK7]
  have hpower : K ^ 7 = X ^ (14 * D + 14) := by
    dsimp [K]
    rw [← pow_mul]
    congr 1
    ring
  simpa only [hpower, X] using hlive

theorem fixed8192_livePacket_polynomial :
    ∃ C e : Nat, ∀ (alphabet : Array (Nat × ℚ))
      (_hnonneg : alphabet.all (fun a => decide (0 ≤ a.2)) = true)
      (_hmass : sourceMass alphabet = 1) (Q j : Nat) (_hj : j < Q)
      (prev : Array ((Fin j → Nat) × ℚ))
      (_hprev : sequentialPreprocessed 8192 alphabet j = some prev)
      (current : Array ((Fin (j + 1) → Nat) × ℚ)) (t : Nat),
      (let F := generatedFeatures (j + 1) 8192 ((positiveLaw alphabet).map Prod.fst)
       EliminationTrace F.size (fun v i => generatedFeatureValue v F[i]) t
        (appendSource prev (positiveLaw alphabet)) current) →
      (livePacket 8192 j alphabet current).length ≤
        C * ((wholeInput Q alphabet).length + 1) ^ e := by
  refine ⟨126 * 8192 + 1200, 14 * 8192 + 14, ?_⟩
  intro alphabet hnonneg hmass Q j hj prev hprev current t htrace
  exact livePacket_length_le 8192 alphabet hnonneg hmass Q j hj prev hprev current t htrace

end CurrentAdditive.V39CodeDLivePacketBound
