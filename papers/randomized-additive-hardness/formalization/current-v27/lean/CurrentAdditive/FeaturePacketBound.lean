import CurrentAdditive.CylinderPairWriter
import CurrentAdditive.SequentialFeatureCoverage
import CurrentAdditive.SequentialFeatureCount
import CurrentAdditive.CylinderMomentCountBound
import CurrentAdditive.CodeDTargetV2

/-!
Literal bit-length accounting for the ordered V2 feature packet.  This
charges every generated descriptor, including duplicate alphabet positions.
It is a resource fact for the pending physical enumerator, not a machine
construction or running-time theorem.
-/

namespace CurrentAdditive.FeaturePacketBound

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open SequentialCode

def labelBits (alphabet : Array Nat) : Nat :=
  (alphabet.toList.map (fun y => y.bits.length)).sum

def pairCap (q : Nat) (alphabet : Array Nat) : Nat :=
  2 * (q.bits.length + labelBits alphabet) + 2

private theorem label_length_le_entry (x : Nat × ℚ) :
    x.1.bits.length ≤ (CurrentAdditive.CodeDTargetV2.alphabetEntry x).length := by
  simpa [CurrentAdditive.CodeDTargetV2.alphabetEntry] using
    EthInapproximability.CurrentPaper.BitMachineBankCodec.word_length_le_encode
      (fun i : Fin 2 =>
        if i = 0 then x.1.bits else
          CurrentAdditive.CodeDCodec.encodeRawRat
            (CurrentAdditive.CodeDCanonicalSourceV2.rawOfRat x.2)) 0

private theorem label_sum_le_entry_sum (xs : List (Nat × ℚ)) :
    (xs.map (fun x => x.1.bits.length)).sum ≤
      SourceListEncoding.totalLength
        (xs.map CurrentAdditive.CodeDTargetV2.alphabetEntry) := by
  induction xs with
  | nil => simp [SourceListEncoding.totalLength]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, SourceListEncoding.totalLength] at *
      have hx := label_length_le_entry x
      omega

private theorem payload_le_encoded_list (xs : List (List Bool)) :
    SourceListEncoding.totalLength xs ≤ (SourceListEncoding.encode xs).length := by
  have hfields : SourceListEncoding.totalLength xs ≤
      (SourceListEncoding.fields xs).length := by
    induction xs with
    | nil => simp [SourceListEncoding.fields, SourceListEncoding.totalLength]
    | cons x xs ih =>
        simp only [SourceListEncoding.fields, SourceListEncoding.totalLength,
          List.map_cons, List.sum_cons, List.length_append] at *
        omega
  simpa only [SourceListEncoding.encode, List.length_append] using
    Nat.le_add_left_of_le hfields

theorem labelBits_le_alphabetBytes (alphabet : Array (Nat × ℚ)) :
    labelBits (alphabet.map Prod.fst) ≤
      (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet).length := by
  have h := label_sum_le_entry_sum alphabet.toList
  have he := payload_le_encoded_list
    (alphabet.toList.map CurrentAdditive.CodeDTargetV2.alphabetEntry)
  simpa [labelBits, CurrentAdditive.CodeDTargetV2.alphabetBytes,
    CurrentAdditive.CodeDCodecV2.encodeItems] using h.trans he

theorem pairCap_actual_input (q : Nat) (alphabet : Array (Nat × ℚ)) :
    pairCap q (alphabet.map Prod.fst) ≤
      2 * (q + (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet).length) + 2 := by
  have hq : q.bits.length ≤ q := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr q.lt_two_pow_self
  have ha := labelBits_le_alphabetBytes alphabet
  unfold pairCap
  omega

theorem generated_label_mem (q D : Nat) (alphabet : Array Nat)
    (c : List (Nat × Nat))
    (hc : c ∈ (generatedFeatures q D alphabet).toList)
    (p : Nat × Nat) (hp : p ∈ c) :
    p.2 ∈ alphabet.toList := by
  induction q generalizing c with
  | zero =>
      simp [generatedFeatures] at hc
      rcases hc with rfl
      simp at hp
  | succ q ih =>
      rw [CurrentAdditive.SequentialFeatureCoverage.generatedFeatures_succ] at hc
      rcases CurrentAdditive.SequentialFeatureCoverage.extendFeatures_mem_cases
          q D alphabet (generatedFeatures q D alphabet) c hc with
        hold | ⟨old, hold, _, y, hy, rfl⟩
      · exact ih c hold hp
      · rcases List.mem_cons.mp hp with heq | htail
        · subst p
          exact hy
        · exact ih old hold htail

theorem generated_pair_length_le (q D : Nat) (alphabet : Array Nat)
    (c : List (Nat × Nat))
    (hc : c ∈ (generatedFeatures q D alphabet).toList)
    (p : Nat × Nat) (hp : p ∈ c) :
    (encodePair p).length ≤ pairCap q alphabet := by
  have hcoord := CurrentAdditive.SequentialFeatureCoverage.generatedFeatures_valid
    q D alphabet c hc p hp
  have hq : p.1.bits.length ≤ q.bits.length := by
    simpa only [Nat.size_eq_bits_len] using
      Nat.size_le_size (Nat.le_of_lt hcoord)
  have hy : p.2.bits.length ≤ labelBits alphabet := by
    apply List.le_sum_of_mem
    exact List.mem_map.mpr
      ⟨p.2, generated_label_mem q D alphabet c hc p hp, rfl⟩
  rw [CurrentAdditive.CylinderPairWriter.pair_length]
  dsimp [pairCap]
  omega

theorem feature_length_le (q D : Nat) (alphabet : Array Nat)
    (c : List (Nat × Nat))
    (hc : c ∈ (generatedFeatures q D alphabet).toList) :
    (encodeFeature c).length ≤ 3 * D * (pairCap q alphabet + 1) + 1 := by
  have hpair : ∀ p ∈ c, (encodePair p).length ≤ pairCap q alphabet := by
    intro p hp
    exact generated_pair_length_le q D alphabet c hc p hp
  have h := SourceListEncoding.encode_map_length_le c encodePair
    (pairCap q alphabet) hpair
  have hD := CurrentAdditive.SequentialFeatureCount.generatedFeatures_length_le
    q D alphabet c hc
  simpa only [encodeFeature, CurrentAdditive.CodeDCodecV2.encodeItems] using
    h.trans (by nlinarith)

theorem packet_length_le (q D : Nat) (alphabet : Array Nat) :
    (generatedFeatureBits q D alphabet).length ≤
      3 * (1 + q * alphabet.size) ^ D *
        (3 * D * (pairCap q alphabet + 1) + 2) + 1 := by
  let fs := (generatedFeatures q D alphabet).toList
  have hfeature : ∀ c ∈ fs,
      (encodeFeature c).length ≤ 3 * D * (pairCap q alphabet + 1) + 1 := by
    intro c hc
    exact feature_length_le q D alphabet c hc
  have henc := SourceListEncoding.encode_map_length_le fs encodeFeature
    (3 * D * (pairCap q alphabet + 1) + 1) hfeature
  have hcount := CurrentAdditive.moment_count_le_one_add_pow
    q D alphabet.size
  have hsize : fs.length =
      ∑ k ∈ Finset.range (min D q + 1), q.choose k * alphabet.size ^ k := by
    simpa [fs] using
      (CurrentAdditive.SequentialFeatureCount.generatedFeatures_size_min
        q D alphabet)
  have hM : fs.length ≤ (1 + q * alphabet.size) ^ D := by
    rw [hsize]
    exact hcount
  have hL : 3 * D * (pairCap q alphabet + 1) + 1 + 1 =
      3 * D * (pairCap q alphabet + 1) + 2 := by omega
  rw [hL] at henc
  unfold generatedFeatureBits encodeFeatures CurrentAdditive.CodeDCodecV2.encodeItems
  simpa only [fs] using henc.trans (by
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right
        (3 * D * (pairCap q alphabet + 1) + 2)
        (Nat.mul_le_mul_left 3 hM)) 1)

theorem packet_length_actual_input (q D : Nat)
    (alphabet : Array (Nat × ℚ)) :
    (generatedFeatureBits q D (alphabet.map Prod.fst)).length ≤
      3 * (1 + q * alphabet.size) ^ D *
        (3 * D *
          (2 * (q + (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet).length) + 3) + 2) + 1 := by
  have h := packet_length_le q D (alphabet.map Prod.fst)
  have hp := pairCap_actual_input q alphabet
  simp only [Array.size_map] at h
  exact h.trans (by gcongr)

theorem packet_length_fixed_8192 (q : Nat)
    (alphabet : Array (Nat × ℚ)) :
    (generatedFeatureBits q 8192 (alphabet.map Prod.fst)).length ≤
      3 * (1 + q * alphabet.size) ^ 8192 *
        (3 * 8192 *
          (2 * (q + (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet).length) + 3) + 2) + 1 :=
  packet_length_actual_input q 8192 alphabet

theorem packet_length_prefix_fixed_8192 (j q : Nat)
    (alphabet : Array (Nat × ℚ)) (hj : j ≤ q) :
    (generatedFeatureBits j 8192 (alphabet.map Prod.fst)).length ≤
      3 * (1 + q * alphabet.size) ^ 8192 *
        (3 * 8192 *
          (2 * (q + (CurrentAdditive.CodeDTargetV2.alphabetBytes alphabet).length) + 3) + 2) + 1 := by
  have h := packet_length_fixed_8192 j alphabet
  exact h.trans (by gcongr)

#print axioms generated_label_mem
#print axioms generated_pair_length_le
#print axioms feature_length_le
#print axioms packet_length_le
#print axioms labelBits_le_alphabetBytes
#print axioms pairCap_actual_input
#print axioms packet_length_actual_input
#print axioms packet_length_fixed_8192
#print axioms packet_length_prefix_fixed_8192

end CurrentAdditive.FeaturePacketBound
