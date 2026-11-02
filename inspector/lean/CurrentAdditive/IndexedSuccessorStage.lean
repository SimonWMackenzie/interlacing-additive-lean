import CurrentAdditive.IndexedStagePresentation
import CurrentAdditive.DeterministicParameters

/-!
The literal generated successor, with its original indexed row/column labels
and complete rational laws, is a stage of the fixed dependent iteration type.
The public side bound comes from the final `Fin Q` coordinate, not from an
unsupported cardinality claim about the Code_D support.
-/

namespace CurrentAdditive.IndexedStagePresentation

open Paper2 Paper2.SourceMatrix CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicParameters

universe u

variable {I X Y : Type u} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem final_column_card_ge_Q {μI : PositiveRationalLaw I}
    {w Q : ℕ} [NeZero w]
    (streams : Sources.InternalStreams src μI w) :
    Q ≤ Fintype.card (Fin Q ×
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))) := by
  have hnonempty := (Sources.InternalStreams.law src streams).nonempty
  have hpos : 0 < Fintype.card
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) :=
    Fintype.card_pos_iff.mpr hnonempty
  have hmul : Q ≤ Q * Fintype.card
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) := by
    calc
      Q = Q * 1 := by omega
      _ ≤ Q * Fintype.card
          (streams.metadataStream.Label ×
            (streams.baseStream.Label × streams.selectorStream.Label)) :=
        Nat.mul_le_mul_left Q (by omega)
  simpa only [Fintype.card_prod, Fintype.card_fin] using hmul

theorem schedule_Q_ge_N (L : ℕ) : N L ≤ Q L := by
  change N L ≤ (N L)^6
  simpa using (Nat.pow_le_pow_right (N_pos L) (by omega : 1 ≤ 6))

/-- The bit-size proof is left to the physical constructor: `S` is its
actual complete encoding size and `hS` merely records that printing the
Boolean entries costs at least one bit each.  No communication lower bound
is supplied as a premise. -/
noncomputable def successorStage {μI : PositiveRationalLaw I}
    {w Q Npub : ℕ} [NeZero w] [NeZero Q]
    (streams : Sources.InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Sources.Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (Sources.columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (S clock : ℕ)
    (hS : Fintype.card final.Label *
      Fintype.card (Fin Q ×
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))) ≤ S)
    (hNQ : Npub ≤ Q) : Stage Npub where
  Row := final.Label
  Col := Fin Q ×
    (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label))
  rowFinite := inferInstance
  colFinite := inferInstance
  rowDecEq := inferInstance
  colDecEq := inferInstance
  rowLaw := final.law
  colLaw := (PositiveRationalLaw.uniform (Fin Q)).prod
    (Sources.InternalStreams.law src streams)
  matrix := Sources.successor src streams final R activity ξ₀
  encodingSize := S
  entries_le_encoding := hS
  public_side := by
    exact hNQ.trans (le_trans (final_column_card_ge_Q src streams)
      (Nat.le_max_right _ _))
  stepClock := clock

@[simp] theorem successorStage_matrix {μI : PositiveRationalLaw I}
    {w Q Npub : ℕ} [NeZero w] [NeZero Q]
    (streams : Sources.InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Sources.Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (Sources.columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (S clock : ℕ)
    (hS : Fintype.card final.Label *
      Fintype.card (Fin Q ×
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))) ≤ S)
    (hNQ : Npub ≤ Q) :
    (successorStage src streams final R activity ξ₀ S clock hS hNQ).matrix =
      Sources.successor src streams final R activity ξ₀ := rfl

#print axioms final_column_card_ge_Q
#print axioms schedule_Q_ge_N
#print axioms successorStage_matrix

end CurrentAdditive.IndexedStagePresentation
