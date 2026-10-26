import CurrentAdditive.DeterministicIndexedBounds
import Paper2.SourceRank

/-! Private Appendix I probe. The actual indexed successor is a literal
submatrix, with possible repeated rows or columns, of the full-product
successor. This is an entry identity, independent of promise profiles. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix Paper2.RankLeaves

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

namespace Sources

variable {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- A generated tagged column has a literal full-product tagged label. -/
def decodeTagged (ξ₀ : Tail s Y) : Column src →
    TaggedColumn q₁ q₂ s Y
  | .ordinary (js, γ) =>
      .unrestricted (tail (gammaWord src γ),
        fun p => outerWord src (src.outer.decode js p))
  | .fixedTail js =>
      .fixedTail (fun p => outerWord src (src.outer.decode js p))
  | .diagonal j => .diagonal (outerWord src j)

theorem forget_decodeTagged (ξ₀ : Tail s Y) (Z : Column src) :
    forgetTag ξ₀ (decodeTagged src ξ₀ Z) = decodeColumn src ξ₀ Z := by
  cases Z <;> rfl

def fullRowDecode {w Q : ℕ} [NeZero w]
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (ξ₀ : Tail s Y) (seed : final.Label) :
    Fin Q → Fin w × TaggedColumn q₁ q₂ s Y :=
  fun p => ((final.decode seed p).1,
    decodeTagged src ξ₀ (final.decode seed p).2)

def fullColumnDecode {μI : PositiveRationalLaw I} {w Q : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (a : Fin Q × (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label))) :
    Fin Q × (Fin w → RawRow q₁ q₂ s X I) :=
  (a.1, fun p => decodeRow src (InternalStreams.decode src streams a.2 p))

/-- All actual entries are full-product entries after decoding labels.
There is no surjectivity or injectivity assumption on either decoder. -/
theorem successor_literal_entry
    {μI : PositiveRationalLaw I} {w Q : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (seed : final.Label)
    (a : Fin Q × (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label))) :
    successor src streams final R activity ξ₀ seed a =
      SourceMatrix.successor (X := X) (Y := Y) (I := I)
        (q₁ := q₁) (q₂ := q₂) (s := s)
        R activity ξ₀ w Q
        (fullRowDecode src final ξ₀ seed)
        (fullColumnDecode src streams a) := by
  classical
  simp only [successor, W, SourceMatrix.successor, fullRowDecode,
    fullColumnDecode, fullInterlace_apply, SourceMatrix.N, B]
  rw [forget_decodeTagged]

/-- Rank of the actual finite indexed successor is bounded by its
full-product matrix, even when decoders repeat visible labels. -/
theorem successor_rank_le_full
    {μI : PositiveRationalLaw I} {w Q : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    (realMatrix (successor src streams final R activity ξ₀)).rank ≤
      (realMatrix (SourceMatrix.successor (X := X) (Y := Y) (I := I)
        (q₁ := q₁) (q₂ := q₂) (s := s)
        R activity ξ₀ w Q)).rank := by
  have hentry : successor src streams final R activity ξ₀ =
      fun seed a => SourceMatrix.successor (X := X) (Y := Y) (I := I)
        (q₁ := q₁) (q₂ := q₂) (s := s)
        R activity ξ₀ w Q
        (fullRowDecode src final ξ₀ seed)
        (fullColumnDecode src streams a) := by
    funext seed a
    exact successor_literal_entry src streams final R activity ξ₀ seed a
  rw [hentry]
  exact Matrix.rank_submatrix_le
    (realMatrix (SourceMatrix.successor (X := X) (Y := Y) (I := I)
      (q₁ := q₁) (q₂ := q₂) (s := s)
      R activity ξ₀ w Q))
    (fullRowDecode src final ξ₀) (fullColumnDecode src streams)

theorem successor_rank_le_factor
    {μI : PositiveRationalLaw I} {w Q : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (hI : Fintype.card I ≤ 2 * s * q₂) :
    (realMatrix (successor src streams final R activity ξ₀)).rank ≤
      w * Q * s * q₂ * (q₁ + 2) * (realMatrix R).rank :=
  (successor_rank_le_full src streams final R activity ξ₀).trans
    (SourceMatrix.successor_rank_le_factor R activity ξ₀ w Q hI)

theorem successor_rank_le_pow
    {μI : PositiveRationalLaw I} {w Q : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (a b c d : ℕ)
    (hI : Fintype.card I ≤ 2 * s * q₂)
    (hq₁ : q₁ + 2 = s)
    (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d) :
    (realMatrix (successor src streams final R activity ξ₀)).rank ≤
      2 ^ (a + a + b + c + d) * (realMatrix R).rank :=
  (successor_rank_le_full src streams final R activity ξ₀).trans
    (SourceMatrix.successor_rank_le_pow R activity ξ₀ w Q a b c d
      hI hq₁ hs hq₂ hw hQ)

#print axioms successor_literal_entry
#print axioms successor_rank_le_factor
#print axioms successor_rank_le_pow

end Sources
end CurrentAdditive.DeterministicIndexedMatrix
