import CurrentAdditive.QuarticFaithfulLiteralTable

/-! Exact sampled row-major bits and complete encoded output of the private
faithful selected good branch, on the same literal fair-bit tape. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace Paper2.GenericQuarticFaithful

open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule
open EthInapproximability.CurrentPaper

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩

theorem selected_good_literal_output {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27Faithful hn edge Δ γ k hc).Tape) :
    let L := Nat.clog 2 n
    let activity := SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1)
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      hn (by unfold width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
    ∃ rows cols,
      let T := YaoMaterialization.tabulate
        (RecursiveEntries.table (LookupSeed.matrix (LookupSeed.width L))
          activity ξ k rows cols)
      table27Faithful hn edge L Δ γ k hc bits = T ∧
      ((select27Faithful hn edge Δ γ k).table
        (selectedTape27Faithful hn edge Δ γ k hc bits)).bits = T.bits ∧
      outputBits27Faithful hn edge Δ γ k
        (selectedTape27Faithful hn edge Δ γ k hc bits) =
        EncodedCommunication.encodeInstance
          (EncodedSelectedOutput.instanceOf T
            (scheduledOutput27Faithful hn edge Δ γ k hc).budget) := by
  intro L activity ξ
  obtain ⟨rows, cols, htab⟩ :=
    table27Faithful_eq_tabulate hn edge L Δ γ k hc bits
  refine ⟨rows, cols, htab, ?_, ?_⟩
  · exact (selected_good_table_bits hn edge Δ γ k hc bits).trans
      (congrArg YaoMaterialization.SerializedTable.bits htab)
  · calc
      outputBits27Faithful hn edge Δ γ k
          (selectedTape27Faithful hn edge Δ γ k hc bits) =
          EncodedCommunication.encodeInstance
            (EncodedSelectedOutput.instanceOf
              (table27Faithful hn edge L Δ γ k hc bits)
              (scheduledOutput27Faithful hn edge Δ γ k hc).budget) :=
        selected_good_output_bits hn edge Δ γ k hc bits
      _ = _ := by rw [htab]

#print axioms selected_good_literal_output

end Paper2.GenericQuarticFaithful
