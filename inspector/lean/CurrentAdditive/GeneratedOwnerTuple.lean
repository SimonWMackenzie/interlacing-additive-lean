import CurrentAdditive.GeneratedTwoStreamImageObstruction
import CurrentAdditive.DeterministicIndexedSuccessor

/-! Original indexed tuple rows at one owner copy. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

abbrev InternalLabel := streams.metadataStream.Label ×
  (streams.baseStream.Label × streams.selectorStream.Label)

/-- The original complete index tuple, restricted only by having a
template symbol at owner coordinate `i`. -/
abbrev OwnerTemplateTuple (i : Fin w) :=
  {t : InternalLabel src streams //
    ∃ p : Fin s, streams.metadataStream.decode t.1 i = .inl p}

noncomputable def ownerBin (i : Fin w) (r : OwnerTemplateTuple src streams i) : Fin s :=
  Classical.choose r.property

theorem ownerBin_eq (i : Fin w) (r : OwnerTemplateTuple src streams i) :
    streams.metadataStream.decode r.val.1 i = .inl (ownerBin src streams i r) :=
  Classical.choose_spec r.property

def ownerSelector (i : Fin w) (r : OwnerTemplateTuple src streams i) :
    src.inner.Label := streams.selectorStream.decode r.val.2.2 i

def ownerRetained (i : Fin w) (U : Set (InternalLabel src streams)) :
    Set (OwnerTemplateTuple src streams i) := fun r => r.val ∈ U

/-- The literal two-stream rectangle in the transposed W orientation.
Ordinary columns come from copy i and diagonal protected columns from j. -/
def ownerRectangle
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (c : (src.outer.Label × src.gamma.Label) ⊕ J src) : Bool :=
  match c with
  | .inl o => W src streams R₀ activity ξ₀ r.val (i, .ordinary o)
  | .inr f => W src streams R₀ activity ξ₀ r.val (j, .diagonal f)

theorem ownerRectangle_ordinary
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (o : src.outer.Label × src.gamma.Label) :
    ownerRectangle src streams R₀ activity ξ₀ i j r (.inl o) =
      T src R₀ (ownerSelector src streams i r)
        (src.outer.decode o.1 (ownerBin src streams i r)) := by
  change B src R₀ activity ξ₀
    (InternalStreams.decode src streams r.val i) (.ordinary o) = _
  simp only [InternalStreams.decode, ownerBin_eq src streams i r]
  rfl

theorem ownerRectangle_foreign
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (f : J src) (p : Fin s)
    (hj : streams.metadataStream.decode r.val.1 j = .inl p) :
    ownerRectangle src streams R₀ activity ξ₀ i j r (.inr f) =
      T src R₀ (streams.selectorStream.decode r.val.2.2 j) f := by
  change B src R₀ activity ξ₀
    (InternalStreams.decode src streams r.val j) (.diagonal f) = _
  simp only [InternalStreams.decode, hj]
  rfl

/-- The local rectangle has no more communication cost than the same
original W protocol restricted to its actual retained tuples and copy rows. -/
theorem ownerRectangle_restriction_le_W
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (V : Set (Fin w × Column src))
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set (J src))
    (hO : ∀ o ∈ O, (i, .ordinary o) ∈ V)
    (hG : ∀ f ∈ G, (j, .diagonal f) ∈ V) :
    Compression.restrictionD
      (ownerRectangle src streams R₀ activity ξ₀ i j)
      (ownerRetained src streams i U)
      (Paper2.TwoStreamInitial.retainedColumns O G) ≤
    Compression.restrictionD (W src streams R₀ activity ξ₀) U V := by
  classical
  let fr : OwnerTemplateTuple src streams i → InternalLabel src streams :=
    fun r => r.val
  let fc : ((src.outer.Label × src.gamma.Label) ⊕ J src) →
      Fin w × Column src
    | .inl o => (i, .ordinary o)
    | .inr f => (j, .diagonal f)
  have hrow : Set.MapsTo fr (ownerRetained src streams i U) U := by
    intro r hr; exact hr
  have hcol : Set.MapsTo fc (Paper2.TwoStreamInitial.retainedColumns O G) V := by
    intro c hc
    rcases c with o | f
    · exact hO o ((Paper2.TwoStreamInitial.inl_mem O G o).mp hc)
    · exact hG f ((Paper2.TwoStreamInitial.inr_mem O G f).mp hc)
  have h := Paper2.SourceProjection.restrictionD_map_le
    (W src streams R₀ activity ξ₀) fr fc U V
    (ownerRetained src streams i U)
    (Paper2.TwoStreamInitial.retainedColumns O G) hrow hcol
  have heq : (fun r c => W src streams R₀ activity ξ₀ (fr r) (fc c)) =
      ownerRectangle src streams R₀ activity ξ₀ i j := by
    funext r c
    cases c <;> rfl
  rw [heq] at h
  exact h

#print axioms ownerRectangle_ordinary
#print axioms ownerRectangle_foreign
#print axioms ownerRectangle_restriction_le_W

end CurrentAdditive.DeterministicIndexedMatrix.Sources
