import CurrentAdditive.IndexedIncomingRows
import CurrentAdditive.RareBoostCanonicalSharp

/-! Appendix I `det:incoming`: a rare-boost rectangle maps entrywise to the
actual original node, with original tagged row labels and selector indices. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- The row set for one flattened selector coordinate, measured in the
original gamma-index law. -/
def incomingRows (R : Set (Fin w × Column src)) (b : Bool)
    (md : streams.metadataStream.Label) (z : Fin w × Fin q₂) :
    Set src.gamma.Label :=
  protectedFibre src w R b z.1
    (templateBin src streams md z.1) z.2

/-- A total map on row labels; on the selected rectangle it chooses an
original protected row. -/
noncomputable def incomingRowMap (R : Set (Fin w × Column src)) (b : Bool)
    (md : streams.metadataStream.Label)
    (row : (Fin w × Fin q₂) × src.gamma.Label) :
    Fin w × Column src := by
  classical
  let z := row.1
  let γ := row.2
  let p := templateBin src streams md z.1
  if hγ : γ ∈ incomingRows src streams R b md z then
    exact (z.1, incomingOriginalColumn src w R b z.1 p (z.2, γ) hγ)
  else
    exact (z.1, .diagonal (z.2, γ))

/-- The restricted lower-bound rows are actual retained node rows. -/
theorem incomingRowMap_survives (R : Set (Fin w × Column src)) (b : Bool)
    (md : streams.metadataStream.Label)
    (Q : Finset (Fin w × Fin q₂)) :
    Set.MapsTo (incomingRowMap src streams R b md)
      (CurrentAdditive.ArbitraryPrefix.rowRectangle Q
        (incomingRows src streams R b md)) R := by
  intro row hrow
  change row.1 ∈ Q ∧ row.2 ∈ incomingRows src streams R b md row.1 at hrow
  have hγ : row.2 ∈ protectedFibre src w R b row.1.1
      (templateBin src streams md row.1.1) row.1.2 := hrow.2
  simp only [incomingRowMap, dif_pos hrow.2]
  exact incomingOriginalColumn_survives src w R b row.1.1
    (templateBin src streams md row.1.1) (row.1.2, row.2) hγ

/-- The selected row map preserves every entry against a fixed complete
metadata/base configuration and any original selector index. -/
theorem incomingRowMap_entry
    (R : Set (Fin w × Column src)) (b : Bool)
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (md : streams.metadataStream.Label)
    (base : streams.baseStream.Label)
    (Q : Finset (Fin w × Fin q₂))
    (hflag : ∀ z ∈ Q, streams.metadataStream.decode md z.1 =
      .inl (templateBin src streams md z.1))
    (row : (Fin w × Fin q₂) × src.gamma.Label)
    (hrow : row ∈ CurrentAdditive.ArbitraryPrefix.rowRectangle Q
      (incomingRows src streams R b md))
    (sel : streams.selectorStream.Label) :
    W src streams R₀ activity ξ₀ (md, (base, sel))
      (incomingRowMap src streams R b md row) =
      A src R₀ row.2
        (src.inner.decode (streams.selectorStream.decode sel row.1.1)
          row.1.2) := by
  change row.1 ∈ Q ∧ row.2 ∈ incomingRows src streams R b md row.1 at hrow
  have hγ := hrow.2
  simp only [incomingRowMap, dif_pos hγ]
  exact indexed_incoming_entry src streams R₀ activity ξ₀ md base sel
    row.1.1 (templateBin src streams md row.1.1)
    (hflag row.1 hrow.1) (row.1.2, row.2)
    (incomingOriginalColumn src w R b row.1.1
      (templateBin src streams md row.1.1) (row.1.2, row.2) hγ)
    (incomingOriginalColumn_realizes src w R b row.1.1
      (templateBin src streams md row.1.1) (row.1.2, row.2) hγ)

/-- The rare-boost rectangle is an actual restriction of the original
transposed `W` node, not an independent replacement matrix. -/
theorem incoming_rectangle_cost_le_node
    (R : Set (Fin w × Column src)) (b : Bool)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (md : streams.metadataStream.Label)
    (base : streams.baseStream.Label)
    (Q : Finset (Fin w × Fin q₂))
    (hflag : ∀ z ∈ Q, streams.metadataStream.decode md z.1 =
      .inl (templateBin src streams md z.1)) :
    let K : Set streams.selectorStream.Label :=
      fun sel => (md, (base, sel)) ∈ Ystar
    Paper2.Compression.restrictionD
      (fun row sel => A src R₀ row.2
        (src.inner.decode (streams.selectorStream.decode sel row.1.1)
          row.1.2))
      (CurrentAdditive.ArbitraryPrefix.rowRectangle Q
        (incomingRows src streams R b md)) K ≤
    Paper2.Compression.restrictionD
      (fun pc t => W src streams R₀ activity ξ₀ t pc) R Ystar := by
  classical
  dsimp
  let S := CurrentAdditive.ArbitraryPrefix.rowRectangle Q
    (incomingRows src streams R b md)
  let K : Set streams.selectorStream.Label :=
    fun sel => (md, (base, sel)) ∈ Ystar
  let f := incomingRowMap src streams R b md
  let g : streams.selectorStream.Label →
      streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label) :=
    fun sel => (md, (base, sel))
  have hf : Set.MapsTo f S R := incomingRowMap_survives src streams R b md Q
  have hg : Set.MapsTo g K Ystar := by
    intro sel hsel
    exact hsel
  have hmap := Paper2.SourceProjection.restrictionD_map_le
    (fun pc t => W src streams R₀ activity ξ₀ t pc)
    f g R Ystar S K hf hg
  have heq : Paper2.Compression.restrictionD
      (fun row sel => A src R₀ row.2
        (src.inner.decode (streams.selectorStream.decode sel row.1.1)
          row.1.2)) S K =
      Paper2.Compression.restrictionD
        (fun row sel => W src streams R₀ activity ξ₀ (g sel) (f row)) S K := by
    unfold Paper2.Compression.restrictionD
    congr 1
    funext row sel
    exact (incomingRowMap_entry src streams R b R₀ activity ξ₀ md base
      Q hflag row.val row.property sel.val).symm
  rw [heq]
  exact hmap

#print axioms incoming_rectangle_cost_le_node

end CurrentAdditive.DeterministicIndexedMatrix.Sources
