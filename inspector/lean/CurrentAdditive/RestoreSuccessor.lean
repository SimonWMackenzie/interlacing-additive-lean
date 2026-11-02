import CurrentAdditive.RestoreTheorem
import CurrentAdditive.DeterministicIndexedSuccessor

/-! Appendix I use of Appendix H `det:restore`: the restored matrix here is
literally the final `Sources.successor` used by the deterministic reduction.
The base matrix is the generated internal transpose `Sources.W`, with its
actual product law on three complete stream labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicRestoration

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Same-object upper bound for the final generated table, with no NO-side
assumptions.  Duplicate decoded tuples remain distinct input labels. -/
theorem final_restored_upper
    {μI : PositiveRationalLaw I} {w r : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource 8192 (2 ^ r) (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    D (successor src streams final R activity ξ₀) ≤
      D (W src streams R activity ξ₀) + r := by
  classical
  simpa only [successor] using
    (generated_restore_upper
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src))
      (W src streams R activity ξ₀) r final)

/-- The Appendix H theorem instantiated at the actual final `CodeSource`.
The hypotheses are precisely the pre-restoration cost, near-full lower bound
and one-step profile of the same generated internal matrix `W`. -/
theorem final_restored_profile
    {μI : PositiveRationalLaw I} {w r C : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource 8192 (2 ^ r) (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (θ φ δ : ℝ)
    (hC : 3 ≤ C) (hD : D (W src streams R activity ξ₀) = C)
    (hθpos : 0 < θ) (hφpos : 0 < φ) (hφ1 : φ ≤ 1)
    (hδpos : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : (128 : ℝ) *
      ((CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2) : ℝ) + 1) ≤
        ((2 ^ r : ℕ) : ℝ))
    (hθ : ((2 ^ r : ℕ) : ℝ) * θ ≤ 1 / 20)
    (hnear : ∀ A : Set (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)),
      ∀ B : Set (Fin w × Column src),
      θ ≤ (streams.law).toFiniteLaw.prob (· ∈ A) →
      1 - δ ≤ ((PositiveRationalLaw.uniform (Fin w)).prod
        (columnLaw src)).toFiniteLaw.prob (· ∈ B) →
      C ≤ Paper2.Compression.restrictionD
        (W src streams R activity ξ₀) A B)
    (hprofile : RestrictionProfile
      (W src streams R activity ξ₀)
      (streams.law).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin w)).prod
        (columnLaw src)).toFiniteLaw
      θ (((C - 1 : ℕ) : ℤ))) :
    D (successor src streams final R activity ξ₀) = C + r ∧
      RestrictionProfile
        (successor src streams final R activity ξ₀)
        final.law.toFiniteLaw
        ((PositiveRationalLaw.uniform (Fin (2 ^ r))).prod
          streams.law).toFiniteLaw
        φ ((C + r : ℕ) : ℤ) := by
  classical
  simpa only [successor] using
    (generated_restore (streams.law)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src))
      (W src streams R activity ξ₀) r C θ φ δ final
      hC hD hθpos hφpos hφ1 hδpos hδ1 hQ hθ hnear hprofile)

#print axioms final_restored_upper
#print axioms final_restored_profile

end CurrentAdditive.DeterministicIndexedMatrix.Sources
