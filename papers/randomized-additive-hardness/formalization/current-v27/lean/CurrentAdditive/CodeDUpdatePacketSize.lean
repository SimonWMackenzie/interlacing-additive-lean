import CurrentAdditive.CodeDUpdateArithmeticClock

/-! Canonical request count and each item fit within the encoded packet length. -/

namespace CurrentAdditive.CodeDUpdatePacketSize

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem item_length_le_fields (xs : List (List Bool)) (x : List Bool)
    (hx : x ∈ xs) : x.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      cases hx with
      | inl h =>
          subst x
          simp only [SourceListEncoding.fields, List.length_append]
          omega
      | inr h =>
          have ht := ih h
          simp only [SourceListEncoding.fields, List.length_append]
          omega

theorem item_length_le_packet (xs : List (List Bool)) (x : List Bool)
    (hx : x ∈ xs) : x.length ≤ (CodeDCodecV2.encodeItems xs).length := by
  have h := item_length_le_fields xs x hx
  change x.length ≤ (SourceListEncoding.encode xs).length
  simp only [SourceListEncoding.encode, List.length_append]
  omega

theorem count_le_fields (xs : List (List Bool)) :
    xs.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x xs ih =>
      have hnat : 0 < (natField x.length).length := by
        simp [natField, field_length]
      simp only [SourceListEncoding.fields, List.length_append,
        List.length_cons]
      omega

theorem count_le_packet (xs : List (List Bool)) :
    xs.length ≤ (CodeDCodecV2.encodeItems xs).length := by
  have h := count_le_fields xs
  change xs.length ≤ (SourceListEncoding.encode xs).length
  simp only [SourceListEncoding.encode, List.length_append]
  omega

#print axioms item_length_le_packet
#print axioms count_le_packet

end CurrentAdditive.CodeDUpdatePacketSize
