import Paper2.A4ShellsTight
import Paper2.TotalFiniteResources

/-!
# Unit 4 (Paper A), N-3: the random-bit count of the selected tape law, polynomial in `|encode Φ|`

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

A lemma about the EXISTING law (`TotalFiniteConstructorScratch.select` / `experiment`), no new
model (D-A1 untouched). On the T10 graph of a valid `Φ` at any gap `k ≥ 1`:

* every tape of the selected law has EXACTLY `inputBits` bits (admitted `selected_exact_lengths`);
* `inputBits ≤ (n + 2)^(160·(k+1))`, `n` the T10 vertex count (admitted
  `TotalFiniteResourcesScratch.selected_announced_counts_le`, exact reuse);
* with the admitted-shape size bound `n + 2 ≤ CS·(|encode Φ| + 1)^ES` (`T10Size.H_T10Size_holds`),
  `inputBits ≤ CS^(160·(k+1)) · (|encode Φ| + 1)^(ES·(160·(k+1)))`: an explicit polynomial of
  `|encode Φ|` for each `k`, with exponent linear in `k + 1` and absolute constants `CS`, `ES`.

The same holds for `experiment … .output` (admitted `experiment_output_eq_select`).
**No ledger row is closed.** `D`, `B` are parameters (D-A7).
-/

namespace Paper2.Unit4Shell.RandomBits

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Every selected tape has exactly `inputBits` bits. -/
theorem tape_length_eq (Φ : ValidFormula) (k : ℕ)
    (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).Tape) :
    ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).tapeBits t).length =
    (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).inputBits := by
  obtain ⟨hm, _, _, hdeg, hloop, _, _⟩ := t10_source D B Φ
  exact (TotalFiniteConstructorScratch.selected_exact_lengths (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k hloop hdeg (source_gap_pos D B) B.degreeBound_pos hm t).2

/-- `inputBits ≤ (n+2)^(160(k+1))` on the T10 graph (exact reuse of the admitted bound). -/
theorem inputBits_le_resource (Φ : ValidFormula) (k : ℕ) (hk : 1 ≤ k) :
    (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).inputBits ≤
    ((t10Graph D B Φ).vertices + 2) ^ (160 * (k + 1)) :=
  (TotalFiniteResourcesScratch.selected_announced_counts_le (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k hk).2

/-- **N-3: random bits polynomial in `|encode Φ|`.** Absolute `CS`, `ES`; for every valid `Φ`,
every `k ≥ 1` and every selected tape, the tape has exactly `inputBits` bits and
`inputBits ≤ CS^(160(k+1))·(|encode Φ|+1)^(ES·(160(k+1)))`. Does not close a ledger row. -/
theorem random_bits_poly :
    ∃ CS ES : ℕ, ∀ (Φ : ValidFormula) (k : ℕ), 1 ≤ k →
      (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).inputBits ≤
        CS ^ (160 * (k + 1)) * ((EncodedCNF.encode Φ.val).length + 1) ^ (ES * (160 * (k + 1))) ∧
      ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).Tape,
        ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).tapeBits t).length =
        (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).inputBits := by
  obtain ⟨CS, ES, hS⟩ := T10Size.H_T10Size_holds D B
  refine ⟨CS, ES, fun Φ k hk => ⟨?_, tape_length_eq D B Φ k⟩⟩
  refine (inputBits_le_resource D B Φ k hk).trans ?_
  calc ((t10Graph D B Φ).vertices + 2) ^ (160 * (k + 1))
      ≤ (CS * ((EncodedCNF.encode Φ.val).length + 1) ^ ES) ^ (160 * (k + 1)) :=
        Nat.pow_le_pow_left (hS Φ) _
    _ = CS ^ (160 * (k + 1)) * ((EncodedCNF.encode Φ.val).length + 1) ^ (ES * (160 * (k + 1))) := by
        rw [mul_pow, ← pow_mul]

/-- The same count for the experiment law (`experiment … .output = select …`). -/
theorem experiment_inputBits_eq (Φ : ValidFormula) (k : ℕ) :
    (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).output.inputBits =
    (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).inputBits := by
  rw [TotalFiniteConstructorScratch.experiment_output_eq_select]

/-- The T01 machine input length is polynomial in `|encode Φ|` (via `random_bits_poly`):
`|pair (encode Φ) (pair (1^k) tape)| ≤ 2|encode Φ| + 2k + 2 + CS^(160(k+1))·(|encode Φ|+1)^(ES·160(k+1))`. -/
theorem uniform_input_length_le :
    ∃ CS ES : ℕ, ∀ (Φ : ValidFormula) (k : ℕ), 1 ≤ k →
      ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).Tape,
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          (EncodedComplexity.pair (List.replicate k true)
            ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
              (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
              B.degreeBound (sourceGap D B) k).tapeBits t))).length ≤
        2 * (EncodedCNF.encode Φ.val).length + 2 * k + 2 +
          CS ^ (160 * (k + 1)) * ((EncodedCNF.encode Φ.val).length + 1) ^ (ES * (160 * (k + 1))) := by
  obtain ⟨CS, ES, h⟩ := random_bits_poly D B
  refine ⟨CS, ES, fun Φ k hk t => ?_⟩
  obtain ⟨hb, hl⟩ := h Φ k hk
  have := hl t
  simp only [EncodedComplexity.pair_length, List.length_replicate]
  omega

#print axioms tape_length_eq
#print axioms inputBits_le_resource
#print axioms random_bits_poly
#print axioms experiment_inputBits_eq
#print axioms uniform_input_length_le

end Paper2.Unit4Shell.RandomBits
