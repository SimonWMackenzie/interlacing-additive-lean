import CurrentAdditive.GenericSamplerFallbackMaterialization
import CurrentAdditive.QuarticConstructor

/-! Private source-faithful v27 scheduled matrix. It keeps the public tape,
schedule, activity scan, tails and LookupSeed, replacing only the inherited
whole-table-abort interpreter with per-draw first-symbol fallback. -/

namespace Paper2.GenericQuarticFaithful

open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

def sourceRun27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    Fin (rows27 n m L Δ γ k) → Fin (cols27 n m L Δ γ k) → Bool := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (width L) := ⟨by unfold width; positivity⟩
  letI : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
  letI : NeZero (width L - 2) := ⟨by have := width_admissible L; omega⟩
  letI : NeZero (width27 L) := ⟨by unfold width27; positivity⟩
  letI : NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
    ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩
  exact GenericSamplerFallbackTable.run
    (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity)
    (SourceActiveRank.scanAtCanonical edge (by
      have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin m) hc.1))
    (CanonicalDefaultSource.canonicalDefaultTails L n
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      hn (by unfold width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _))
    k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)
    (RecursiveSamplingTape.readTape _ _ _ bits)

def table27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    YaoMaterialization.SerializedTable
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) :=
  YaoMaterialization.tabulate (sourceRun27Faithful hn edge L Δ γ k hc bits)

theorem table27Faithful_entry {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k))
    (i : Fin (rows27 n m L Δ γ k))
    (j : Fin (cols27 n m L Δ γ k)) :
    (table27Faithful hn edge L Δ γ k hc bits).matrix i j =
      sourceRun27Faithful hn edge L Δ γ k hc bits i j :=
  YaoMaterialization.tabulate_matrix _ i j

end Paper2.GenericQuarticFaithful
