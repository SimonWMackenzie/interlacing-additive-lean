import CurrentAdditive.DeterministicRankEmbedding
import CurrentAdditive.DeterministicDuplicateMerge

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.RankLeaves
  Workspace.Types.CommComplexity

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The merged matrix uses exactly the distinct decoded rows and columns
that occurred in the actual generated successor. -/
def mergedSuccessor {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    Paper2.DuplicateMerge.Decoded (fullRowDecode src final ξ₀) →
      Paper2.DuplicateMerge.Decoded (fullColumnDecode src (Q := Q) streams) → Bool :=
  fun seed a => SourceMatrix.successor (X := X) (Y := Y) (I := I)
    (q₁ := q₁) (q₂ := q₂) (s := s) R activity ξ₀ w Q seed.val a.val

theorem successor_merged_D_eq {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    Workspace.Types.CommComplexity.D (successor src streams final R activity ξ₀) =
      Workspace.Types.CommComplexity.D
        (mergedSuccessor src streams final R activity ξ₀) := by
  classical
  have hentry : successor src streams final R activity ξ₀ =
      fun seed a => SourceMatrix.successor (X := X) (Y := Y) (I := I)
        (q₁ := q₁) (q₂ := q₂) (s := s)
        R activity ξ₀ w Q
        (fullRowDecode src final ξ₀ seed)
        (fullColumnDecode src streams a) := by
    funext seed a
    exact successor_literal_entry src streams final R activity ξ₀ seed a
  rw [hentry]
  exact Paper2.DuplicateMerge.image_cost_eq
    (SourceMatrix.successor (X := X) (Y := Y) (I := I)
      (q₁ := q₁) (q₂ := q₂) (s := s) R activity ξ₀ w Q)
    (fullRowDecode src final ξ₀) (fullColumnDecode src (Q := Q) streams)

theorem successor_merged_profile_iff {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (successor src streams final R activity ξ₀)
      final.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin Q)).prod streams.law).toFiniteLaw)
      ρ d ↔
    RestrictionProfile (mergedSuccessor src streams final R activity ξ₀)
      (Paper2.DuplicateMerge.mergedOnImage final.law
        (fullRowDecode src final ξ₀)).toFiniteLaw
      (Paper2.DuplicateMerge.mergedOnImage
        ((PositiveRationalLaw.uniform (Fin Q)).prod streams.law)
        (fullColumnDecode src (Q := Q) streams)).toFiniteLaw ρ d := by
  classical
  have hentry : successor src streams final R activity ξ₀ =
      fun seed a => SourceMatrix.successor (X := X) (Y := Y) (I := I)
        (q₁ := q₁) (q₂ := q₂) (s := s)
        R activity ξ₀ w Q
        (fullRowDecode src final ξ₀ seed)
        (fullColumnDecode src streams a) := by
    funext seed a
    exact successor_literal_entry src streams final R activity ξ₀ seed a
  rw [hentry]
  exact Paper2.DuplicateMerge.image_profile_iff
    (SourceMatrix.successor (X := X) (Y := Y) (I := I)
      (q₁ := q₁) (q₂ := q₂) (s := s) R activity ξ₀ w Q)
    (fullRowDecode src final ξ₀) (fullColumnDecode src (Q := Q) streams)
    final.law ((PositiveRationalLaw.uniform (Fin Q)).prod streams.law)
    ρ d

theorem successor_merged_row_mass {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (ξ₀ : Tail s Y)
    (E : Paper2.DuplicateMerge.Decoded (fullRowDecode src final ξ₀) → Prop) :
    final.law.toFiniteLaw.prob
      (fun seed => E (Paper2.DuplicateMerge.decode
        (fullRowDecode src final ξ₀) seed)) =
    (Paper2.DuplicateMerge.mergedOnImage final.law
      (fullRowDecode src final ξ₀)).toFiniteLaw.prob E :=
  Paper2.DuplicateMerge.mergedOnImage_prob final.law
    (fullRowDecode src final ξ₀) E

theorem successor_merged_column_mass {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q]
    (streams : InternalStreams src μI w)
    (E : Paper2.DuplicateMerge.Decoded
      (fullColumnDecode src (Q := Q) streams) → Prop) :
    (((PositiveRationalLaw.uniform (Fin Q)).prod streams.law).toFiniteLaw).prob
      (fun a => E (Paper2.DuplicateMerge.decode
        (fullColumnDecode src (Q := Q) streams) a)) =
    (Paper2.DuplicateMerge.mergedOnImage
      ((PositiveRationalLaw.uniform (Fin Q)).prod streams.law)
      (fullColumnDecode src (Q := Q) streams)).toFiniteLaw.prob E :=
  Paper2.DuplicateMerge.mergedOnImage_prob
    ((PositiveRationalLaw.uniform (Fin Q)).prod streams.law)
    (fullColumnDecode src (Q := Q) streams) E

theorem successor_merged_restriction_D_eq {μI : PositiveRationalLaw I}
    {w Q : ℕ} [NeZero w] [NeZero Q]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (U : Set (Paper2.DuplicateMerge.Decoded (fullRowDecode src final ξ₀)))
    (V : Set (Paper2.DuplicateMerge.Decoded
      (fullColumnDecode src (Q := Q) streams))) :
    Compression.restrictionD (successor src streams final R activity ξ₀)
      ((Paper2.DuplicateMerge.decode (fullRowDecode src final ξ₀)) ⁻¹' U)
      ((Paper2.DuplicateMerge.decode
        (fullColumnDecode src (Q := Q) streams)) ⁻¹' V) =
    Compression.restrictionD
      (mergedSuccessor src streams final R activity ξ₀) U V := by
  classical
  have hentry : successor src streams final R activity ξ₀ =
      fun seed a => SourceMatrix.successor (X := X) (Y := Y) (I := I)
        (q₁ := q₁) (q₂ := q₂) (s := s)
        R activity ξ₀ w Q
        (fullRowDecode src final ξ₀ seed)
        (fullColumnDecode src streams a) := by
    funext seed a
    exact successor_literal_entry src streams final R activity ξ₀ seed a
  rw [hentry]
  exact Paper2.DuplicateMerge.image_restriction_cost_eq
    (SourceMatrix.successor (X := X) (Y := Y) (I := I)
      (q₁ := q₁) (q₂ := q₂) (s := s) R activity ξ₀ w Q)
    (fullRowDecode src final ξ₀) (fullColumnDecode src (Q := Q) streams) U V

#print axioms successor_merged_D_eq
#print axioms successor_merged_profile_iff
#print axioms successor_merged_row_mass
#print axioms successor_merged_column_mass
#print axioms successor_merged_restriction_D_eq

end CurrentAdditive.DeterministicIndexedMatrix.Sources
