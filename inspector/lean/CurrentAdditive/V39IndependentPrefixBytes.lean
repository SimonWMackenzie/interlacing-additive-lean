import CurrentAdditive.ZeroFilteredPrefixBits
import CurrentAdditive.ZeroFilterNormalized
import CurrentAdditive.DeterministicCodeDSerializedSize

set_option autoImplicit false

namespace CurrentAdditive.V39IndependentPrefixBytes

open SequentialCode SequentialSourceCode IndependentSupport IntegerBitSupport
open LabelTrace ZeroFilteredWeightBits TransientArithmetic

/-- An actual finite dependence-elimination path retains only input labels. -/
theorem trace_labels {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source current : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source current) :
    LabelsRetained source current := by
  induction htrace with
  | refl source => exact fun entry he => ⟨entry, he, rfl⟩
  | step source next current f t hfree hstep hrest ih =>
      intro entry he
      obtain ⟨mid, hmid, hm⟩ := ih entry he
      obtain ⟨old, hold, ho⟩ := compressSourceOnce_labels n φ source next hstep mid hmid
      exact ⟨old, hold, ho.trans hm⟩

/-- Every actual retained prefix has at most the original candidate count. -/
theorem trace_size {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source current : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source current) :
    current.size ≤ source.size := by
  induction htrace with
  | refl source => exact le_refl _
  | step source next current f t hfree hstep hrest ih =>
      exact ih.trans (Nat.le_of_lt
        (compressSourceOnceMaterialized_size_lt n φ source next hstep))

private theorem filtered_codes (alphabet : Array (Nat × ℚ))
    (hmass : sourceMass alphabet = 1) (U : Nat)
    (hcode : ∀ entry ∈ alphabet, entry.1.bits.length ≤ U) :
    ∀ entry ∈ positiveLaw alphabet, entry.1.bits.length ≤ U := by
  obtain ⟨trace, he, _⟩ := positiveLaw_trace_exact alphabet hmass
  intro entry hentry
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hentry
  have hsame := he ⟨i, hi⟩
  have hbound := hcode (alphabet[trace ⟨i, hi⟩])
    (Array.getElem_mem (trace ⟨i, hi⟩).isLt)
  have hs : entry = alphabet[trace ⟨i, hi⟩] := hget.symm.trans hsame
  rw [hs]
  exact hbound

/-- Completed independent-column stages use the original symbol bit bound. -/
theorem stage_codes (D : Nat) (alphabet : Array (Nat × ℚ))
    (hmass : sourceMass alphabet = 1) (U : Nat)
    (hcode : ∀ entry ∈ alphabet, entry.1.bits.length ≤ U)
    (q : Nat) (out : Array ((Fin q → Nat) × ℚ))
    (hout : sequentialPreprocessed D alphabet q = some out) :
    ∀ entry ∈ out, ∀ j : Fin q, (entry.1 j).bits.length ≤ U := by
  intro entry he j
  have hm := sequentialIndependent_coordinate_mem D (positiveLaw alphabet)
    q out hout entry he j
  rw [Array.toList_map] at hm
  obtain ⟨symbol, hs, hsymbol⟩ := List.mem_map.mp hm
  rw [← hsymbol]
  exact filtered_codes alphabet hmass U hcode symbol
    (Array.mem_toList_iff.mp hs)

private theorem append_codes {q : Nat}
    (prev : Array ((Fin q → Nat) × ℚ)) (alphabet : Array (Nat × ℚ)) (U : Nat)
    (hprev : ∀ entry ∈ prev, ∀ j : Fin q, (entry.1 j).bits.length ≤ U)
    (halphabet : ∀ entry ∈ alphabet, entry.1.bits.length ≤ U) :
    ∀ entry ∈ appendSource prev alphabet, ∀ j : Fin (q + 1),
      (entry.1 j).bits.length ≤ U := by
  intro entry he j
  have he' := Array.mem_toList_iff.mpr he
  rw [appendSource_toList] at he'
  obtain ⟨old, hold, he'⟩ := List.mem_flatMap.mp he'
  obtain ⟨symbol, hs, rfl⟩ := List.mem_map.mp he'
  by_cases hj : j.val < q
  · simpa [appendWord, hj] using
      hprev old (Array.mem_toList_iff.mp hold) ⟨j.val, hj⟩
  · simpa [appendWord, hj] using
      halphabet symbol (Array.mem_toList_iff.mp hs)

/-- The canonical source packet at every actual inner-loop prefix has a
uniform bound in the original alphabet's size, symbol bits, and input bytes.
This statement concerns serialized length, independently of machine time. -/
theorem prefix_encodedSource_length_le
    (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (U : Nat)
    (hcode : ∀ entry ∈ alphabet, entry.1.bits.length ≤ U)
    (Q q : Nat) (hq : q < Q)
    (prev : Array ((Fin q → Nat) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev)
    (current : Array ((Fin (q + 1) → Nat) × ℚ)) (t : Nat)
    (htrace :
      let F := generatedFeatures (q + 1) D ((positiveLaw alphabet).map Prod.fst)
      EliminationTrace F.size (fun v j => generatedFeatureValue v F[j]) t
        (appendSource prev (positiveLaw alphabet)) current) :
    (CodeDCanonicalSourceV2.encodedSource current).length ≤
      3 * (alphabet.size * (1 + Q * alphabet.size) ^ D) *
        (6 * Q * (U + 1) +
          8 * (2 * budget D Q alphabet.size
            (CodeDTargetV2.alphabetBytes alphabet).length + 1) + 15) + 1 := by
  let B := 2 * budget D Q alphabet.size
    (CodeDTargetV2.alphabetBytes alphabet).length + 1
  let F := generatedFeatures (q + 1) D ((positiveLaw alphabet).map Prod.fst)
  have hweights := sequentialPreprocessed_every_prefix_weights D alphabet
    hnonneg hmass Q q hq prev hprev current t htrace
  have hret := trace_labels F.size
    (fun v j => generatedFeatureValue v F[j])
    (appendSource prev (positiveLaw alphabet)) current t htrace
  have hcodes : ∀ entry ∈ current, ∀ j : Fin (q + 1),
      (entry.1 j).bits.length ≤ U := by
    intro entry he j
    obtain ⟨old, hold, hlabel⟩ := hret entry he
    rw [← hlabel]
    exact append_codes prev (positiveLaw alphabet) U
      (stage_codes D alphabet hmass U hcode q prev hprev)
      (filtered_codes alphabet hmass U hcode) old hold j
  have hsize : current.size ≤ alphabet.size * (1 + Q * alphabet.size) ^ D := by
    have hstart := trace_size F.size (fun v j => generatedFeatureValue v F[j])
      (appendSource prev (positiveLaw alphabet)) current t htrace
    rw [SequentialSourceResource.appendSource_size] at hstart
    have hp := sequentialPreprocessed_size_polynomial D alphabet hmass q prev hprev
    have hp' : prev.size ≤ (1 + Q * alphabet.size) ^ D := hp.trans
      (Nat.pow_le_pow_left (by gcongr) D)
    have ha := positiveLaw_size_le alphabet hmass
    exact hstart.trans ((Nat.mul_le_mul hp' ha).trans_eq (Nat.mul_comm _ _))
  have hbytes := DeterministicCodeDSerializedSize.encodedSource_length_le current U B
    (by intro entry he; exact hcodes entry (Array.mem_toList_iff.mp he))
    (by
      intro entry he
      obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp he)
      simpa [B, hget] using (hweights ⟨i, hi⟩).1)
    (by
      intro entry he
      obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp he)
      simpa [B, hget] using (hweights ⟨i, hi⟩).2)
  exact hbytes.trans (by dsimp only [B]; gcongr; omega)

end CurrentAdditive.V39IndependentPrefixBytes
