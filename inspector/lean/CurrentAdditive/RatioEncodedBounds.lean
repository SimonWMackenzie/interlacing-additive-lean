import CurrentAdditive.TransientArithmetic
import CurrentAdditive.MinimumRatioFoldSemanticJoin

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RatioEncodedBounds

open TransientArithmetic
open EthInapproximability.CurrentPaper

def ratioWord (p : ℚ × ℚ) : List Bool :=
  CodeDPairProductTargetV2.pairBytes
    (CodeDCanonicalSourceV2.rawOfRat p.1) (CodeDCanonicalSourceV2.rawOfRat p.2)

def ratioWords (items : List (ℚ × ℚ)) : List (List Bool) := items.map ratioWord

theorem ratioWords_length (items : List (ℚ × ℚ)) :
    (ratioWords items).length = items.length := by simp [ratioWords]

theorem ratioWord_length {b c : Nat} {p : ℚ × ℚ}
    (hp : Fits b p.1 ∧ Fits c p.2) :
    (ratioWord p).length ≤ 8 * b + 8 * c + 22 :=
  pairBytes_length p.1 p.2 b c hp.1 hp.2

theorem ratioWords_encoded_length (items : List (ℚ × ℚ)) (b c : Nat)
    (hi : ∀ p ∈ items, Fits b p.1 ∧ Fits c p.2) :
    (SourceListEncoding.encode (ratioWords items)).length ≤
      3 * items.length * (8 * b + 8 * c + 23) + 1 := by
  exact SourceListEncoding.encode_map_length_le items ratioWord _
    (by intro p hp; exact ratioWord_length (hi p hp))

theorem ratioWords_fields_length (items : List (ℚ × ℚ)) (b c : Nat)
    (hi : ∀ p ∈ items, Fits b p.1 ∧ Fits c p.2) :
    (SourceListEncoding.fields (ratioWords items)).length ≤
      3 * items.length * (8 * b + 8 * c + 23) := by
  have hp := SourceListEncoding.totalLength_map_le items ratioWord
    (8 * b + 8 * c + 22) (by intro p hp; exact ratioWord_length (hi p hp))
  have hf := SourceListEncoding.fields_length (ratioWords items)
  rw [ratioWords_length] at hf
  dsimp only [ratioWords] at hf
  change (SourceListEncoding.fields (items.map ratioWord)).length ≤
    3 * items.length * (8 * b + 8 * c + 23)
  nlinarith

/-- The physical canonical callback fold has exactly the semantic saved
best value; this connects the rational size theorem to its literal bytes. -/
theorem ratioWords_fold (items : List (ℚ × ℚ)) (best : Option ℚ) :
    (ratioWords items).foldl MinimumRatioStepSpec.step
        (MinimumRatioStepSpec.bestPacket best) =
      MinimumRatioStepSpec.bestPacket
        (items.foldl (fun prev p => MinimumRatioStepSpec.semanticStep prev p.1 p.2) best) := by
  induction items generalizing best with
  | nil => rfl
  | cons p rest ih =>
      have hs := MinimumRatioStepSpec.step_pair best
        (CodeDCanonicalSourceV2.rawOfRat p.1) (CodeDCanonicalSourceV2.rawOfRat p.2)
        (CodeDCanonicalSourceV2.rawOfRat_valid _) (CodeDCanonicalSourceV2.rawOfRat_valid _)
      simp only [CodeDCanonicalSourceV2.rawOfRat_value] at hs
      simp only [ratioWords, List.map_cons, List.foldl_cons]
      rw [show MinimumRatioStepSpec.step (MinimumRatioStepSpec.bestPacket best)
        (ratioWord p) = MinimumRatioStepSpec.bestPacket
          (MinimumRatioStepSpec.semanticStep best p.1 p.2) from hs]
      exact ih _

/-- Every actual prefix's saved-best WORD fits a fixed polynomial in the
input weight/coefficient field budgets. -/
theorem ratioWords_best_length (items : List (ℚ × ℚ)) (b c : Nat)
    (hi : ∀ p ∈ items, Fits b p.1 ∧ Fits c p.2) :
    ((ratioWords items).foldl MinimumRatioStepSpec.step []).length ≤
      4 * (b + c + 1) + 6 := by
  have hf := ratioWords_fold items none
  change ((ratioWords items).foldl MinimumRatioStepSpec.step
    (MinimumRatioStepSpec.bestPacket none)).length ≤ _
  rw [hf]
  apply bestPacket_length
  exact ratio_scan_prefix_fits items b c hi none (by simp)

theorem prefix_index_lengths (pre tail : List (ℚ × ℚ)) (p : ℚ × ℚ) :
    (List.replicate (ratioWords pre).length true).length ≤
        (pre ++ p :: tail).length ∧
      (List.replicate (ratioWords tail).length true).length ≤
        (pre ++ p :: tail).length := by
  simp only [List.length_replicate, ratioWords_length, List.length_append,
    List.length_cons]
  omega

/-- Materialize the exact rational pairs scanned by minimumRatio, keeping
each source position as a separate list item. -/
def arrayItems (weights coeff : Array ℚ) : List (ℚ × ℚ) :=
  (List.range (min weights.size coeff.size)).map
    (fun i => (weights[i]?.getD 0, coeff[i]?.getD 0))

theorem arrayItems_length (weights coeff : Array ℚ) :
    (arrayItems weights coeff).length = min weights.size coeff.size := by
  simp [arrayItems]

theorem arrayItems_fit (weights coeff : Array ℚ) (b c : Nat)
    (hw : ∀ i : Fin weights.size, Fits b weights[i])
    (hc : ∀ i : Fin coeff.size, Fits c coeff[i]) :
    ∀ p ∈ arrayItems weights coeff, Fits b p.1 ∧ Fits c p.2 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hwlt : i < weights.size :=
    (List.mem_range.mp hi).trans_le (Nat.min_le_left _ _)
  have hclt : i < coeff.size :=
    (List.mem_range.mp hi).trans_le (Nat.min_le_right _ _)
  simpa [hwlt, hclt] using And.intro (hw ⟨i, hwlt⟩) (hc ⟨i, hclt⟩)

theorem actual_array_packet_bounds (weights coeff : Array ℚ) (b c : Nat)
    (hw : ∀ i : Fin weights.size, Fits b weights[i])
    (hc : ∀ i : Fin coeff.size, Fits c coeff[i]) :
    (SourceListEncoding.encode (ratioWords (arrayItems weights coeff))).length ≤
        3 * weights.size * (8 * b + 8 * c + 23) + 1 ∧
      ((ratioWords (arrayItems weights coeff)).foldl
        MinimumRatioStepSpec.step []).length ≤ 4 * (b + c + 1) + 6 := by
  have hfit := arrayItems_fit weights coeff b c hw hc
  have hp := ratioWords_encoded_length (arrayItems weights coeff) b c hfit
  rw [arrayItems_length] at hp
  refine ⟨hp.trans ?_, ratioWords_best_length _ b c hfit⟩
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 (Nat.min_le_left _ _))) 1

#print axioms ratioWords_fold
#print axioms ratioWords_best_length
#print axioms actual_array_packet_bounds

end CurrentAdditive.RatioEncodedBounds
