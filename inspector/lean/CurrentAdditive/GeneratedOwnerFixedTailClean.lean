import CurrentAdditive.GeneratedOwnerGoodPair
import CurrentAdditive.IndexedIncomingImageFixed

/-! The fixed-tail alternative for owner-to-owner protected transfer. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- The literal W rectangle using original fixed-tail labels at foreign
position j. The foreign label is mapped to J₂ only after a bin at j is
selected. -/
def ownerRectangleFixedTail
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (c : (src.outer.Label × src.gamma.Label) ⊕ src.outer.Label) : Bool :=
  match c with
  | .inl o => W src streams R₀ activity ξ₀ r.val (i, .ordinary o)
  | .inr f => W src streams R₀ activity ξ₀ r.val (j, .fixedTail f)

theorem ownerRectangleFixedTail_ordinary
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (o : src.outer.Label × src.gamma.Label) :
    ownerRectangleFixedTail src streams R₀ activity ξ₀ i j r (.inl o) =
      T src R₀ (ownerSelector src streams i r)
        (src.outer.decode o.1 (ownerBin src streams i r)) := by
  change B src R₀ activity ξ₀
    (InternalStreams.decode src streams r.val i) (.ordinary o) = _
  simp only [InternalStreams.decode, ownerBin_eq src streams i r]
  rfl

theorem ownerRectangleFixedTail_foreign
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (f : src.outer.Label) (p : Fin s)
    (hj : streams.metadataStream.decode r.val.1 j = .inl p) :
    ownerRectangleFixedTail src streams R₀ activity ξ₀ i j r (.inr f) =
      T src R₀ (streams.selectorStream.decode r.val.2.2 j)
        (src.outer.decode f p) := by
  change B src R₀ activity ξ₀
    (InternalStreams.decode src streams r.val j) (.fixedTail f) = _
  simp only [InternalStreams.decode, hj]
  rfl

theorem ownerRectangleFixedTail_restriction_le_W
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (V : Set (Fin w × Column src))
    (O : Set (src.outer.Label × src.gamma.Label))
    (G : Set src.outer.Label)
    (hO : ∀ o ∈ O, (i, .ordinary o) ∈ V)
    (hG : ∀ f ∈ G, (j, .fixedTail f) ∈ V) :
    Compression.restrictionD
      (ownerRectangleFixedTail src streams R₀ activity ξ₀ i j)
      (ownerRetained src streams i U)
      (Paper2.TwoStreamInitial.retainedColumns O G) ≤
    Compression.restrictionD (W src streams R₀ activity ξ₀) U V := by
  classical
  let fr : OwnerTemplateTuple src streams i → InternalLabel src streams :=
    fun r => r.val
  let fc : ((src.outer.Label × src.gamma.Label) ⊕ src.outer.Label) →
      Fin w × Column src
    | .inl o => (i, .ordinary o)
    | .inr f => (j, .fixedTail f)
  have hrow : Set.MapsTo fr (ownerRetained src streams i U) U := by
    intro r hr; exact hr
  have hcol : Set.MapsTo fc
      (Paper2.TwoStreamInitial.retainedColumns O G) V := by
    intro c hc
    rcases c with o | f
    · exact hO o ((Paper2.TwoStreamInitial.inl_mem O G o).mp hc)
    · exact hG f ((Paper2.TwoStreamInitial.inr_mem O G f).mp hc)
  have h := Paper2.SourceProjection.restrictionD_map_le
    (W src streams R₀ activity ξ₀) fr fc U V
    (ownerRetained src streams i U)
    (Paper2.TwoStreamInitial.retainedColumns O G) hrow hcol
  have heq : (fun r c => W src streams R₀ activity ξ₀ (fr r) (fc c)) =
      ownerRectangleFixedTail src streams R₀ activity ξ₀ i j := by
    funext r c
    cases c <;> rfl
  rw [heq] at h
  exact h

#print axioms ownerRectangleFixedTail_foreign
#print axioms ownerRectangleFixedTail_restriction_le_W

/-- The fixed-tail version of the literal W two-stream obstruction. The
foreign J₂ mass is obtained from the retained original outer labels through
the selected second bin; no retained-law independence is assumed. -/
theorem owner_to_owner_W_lower_fixed_tail_bins
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (p r : Fin s)
    (U : Set (InternalLabel src streams))
    (V : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (pairMass ε δ : ℝ)
    (hPair : pairMass ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ ownerPairImage src streams U i j p r))
    (hMargin : 49/64 + 2*s*x < pairMass)
    (hOther : ∀ b ≠ p, 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (fun z => ∃ t ∈ U,
        streams.metadataStream.decode t.1 i = .inl b ∧
        streams.selectorStream.decode t.2.2 i = z))
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ V))
    (hF : δ ≤ src.outer.law.toFiniteLaw.prob
      (fun f => (j, .fixedTail f) ∈ V))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U V := by
  classical
  let μS := src.inner.law.toFiniteLaw
  let P0 : Finset (src.inner.Label × src.inner.Label) :=
    Finset.univ.filter (· ∈ ownerPairImage src streams U i j p r)
  have hP0 (z : src.inner.Label × src.inner.Label) :
      z ∈ P0 ↔ z ∈ ownerPairImage src streams U i j p r := by
    simp [P0]
  have hP0mass : pairMass ≤ (μS.prod μS).prob (· ∈ (P0 : Set _)) := by
    simpa only [P0, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] using hPair
  have hτpos : (0 : ℝ) < 2*s*x := by
    have hspos : (0 : ℝ) < s := by
      exact_mod_cast (show 0 < s from NeZero.pos s)
    positivity
  have hP0nonempty : P0.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : (μS.prod μS).prob (· ∈ (P0 : Set _)) = 0 := by simp [he]
    rw [hz] at hP0mass
    linarith
  obtain ⟨z₀, hz₀⟩ := hP0nonempty
  let fallback : OwnerTemplateTuple src streams i :=
    ownerPairTuple src streams U i j p r ⟨z₀, (hP0 z₀).mp hz₀⟩
  let input : (src.inner.Label × src.inner.Label) →
      OwnerTemplateTuple src streams i :=
    ownerPairInput src streams U i j p r P0 hP0 fallback
  let O : Set (src.outer.Label × src.gamma.Label) :=
    fun o => (i, .ordinary o) ∈ V
  let G : Set src.outer.Label := fun f => (j, .fixedTail f) ∈ V
  let ψ : src.outer.Label → J src := fun f => src.outer.decode f r
  let R : Set (OwnerTemplateTuple src streams i) :=
    ownerRetained src streams i U
  let M := ownerRectangleFixedTail src streams R₀ activity ξ₀ i j
  have hlabels : ∀ z ∈ P0,
      input z ∈ R ∧ ownerBin src streams i (input z) = p ∧
      ownerSelector src streams i (input z) = z.1 ∧
      streams.metadataStream.decode (input z).val.1 j = .inl r ∧
      streams.selectorStream.decode (input z).val.2.2 j = z.2 := by
    intro z hz
    exact ownerPairInput_labels src streams U i j p r P0 hP0 fallback z hz
  have hpairFirst : 2*s*x ≤ μS.prob
      (· ∈ (fun z : src.inner.Label × src.inner.Label => z.1) '' (P0 : Set _)) := by
    have hmass := ownerPairFirst_mass src P0 pairMass hP0mass
    linarith
  have hrow : ∀ b ≠ p, 2*s*x ≤ μS.prob
      (fun z => ∃ t ∈ R,
        ownerBin src streams i t = b ∧ ownerSelector src streams i t = z) := by
    intro b hb
    have hsub : (fun z => ∃ t ∈ U,
        streams.metadataStream.decode t.1 i = .inl b ∧
        streams.selectorStream.decode t.2.2 i = z) ≤
      (fun z => ∃ t ∈ R,
        ownerBin src streams i t = b ∧ ownerSelector src streams i t = z) := by
      intro z ⟨t, ht, hm, hz⟩
      let row : OwnerTemplateTuple src streams i := ⟨t, ⟨b, hm⟩⟩
      refine ⟨row, ht, ?_, hz⟩
      have hh := ownerBin_eq src streams i row
      exact Sum.inl.inj (hh.symm.trans hm)
    exact (hOther b hb).trans (μS.prob_mono hsub)
  have hret := ownerPair_retention src P0 pairMass (2*s*x) hP0mass hMargin
  have hψpush : src.outer.law.toFiniteLaw.PushesTo
      (diagonalLaw src).toFiniteLaw ψ := by
    intro E
    exact outer_position_pushes src (by omega : 1 ≤ D) r E
  have hF' : δ ≤ (diagonalLaw src).toFiniteLaw.prob (· ∈ ψ '' G) :=
    hF.trans (FiniteLaw.prob_le_image
      src.outer.law.toFiniteLaw (diagonalLaw src).toFiniteLaw ψ hψpush G)
  have hlower := generated_two_stream_image_restriction_lower src
    R₀ M H ell a hH hq hs x hx hD hA hT
    (μS.prod μS) (ownerBin src streams i)
    (ownerSelector src streams i) ψ
    (ownerRectangleFixedTail_ordinary src streams R₀ activity ξ₀ i j)
    input id (by intro E; rfl) p P0 R O G
    (fun z hz => (hlabels z hz).1)
    (fun z hz => ⟨(hlabels z hz).2.1, (hlabels z hz).2.2.1⟩)
    (by
      intro z hz f
      have hh := ownerRectangleFixedTail_foreign src streams R₀ activity ξ₀
        i j (input z) f r (hlabels z hz).2.2.2.1
      simpa only [M, ψ] using hh.trans
        (congrArg (fun zz => T src R₀ zz (src.outer.decode f r))
          (hlabels z hz).2.2.2.2))
    (by simpa only [Function.id_comp] using hpairFirst)
    hrow
    (by intro P' hsub hloss
        simpa only [Set.image_id] using hret P' hsub hloss)
    ε δ hO hF' hδ hslack hsmall hpairsmall
  exact hlower.trans (ownerRectangleFixedTail_restriction_le_W
    src streams R₀ activity ξ₀ i j U V O G
    (by intro o ho; exact ho) (by intro f hf; exact hf))

#print axioms owner_to_owner_W_lower_fixed_tail_bins

/-- The same source pair-image averaging serves retained fixed-tail foreign
columns. Their original outer-law mass is projected at the selected second
template bin inside the fixed-tail theorem. -/
theorem owner_to_owner_W_lower_fixed_tail_good_projection
    {G V Aux : Type*} [Fintype G] [Fintype V] [Fintype Aux]
    [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
    (μI' : PositiveRationalLaw (G × (V ⊕ Aux)))
    {w : ℕ} (streams : InternalStreams src μI' w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI').toFiniteLaw.prod
        (rowLaw src μI').toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U))
    (hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2)
    (hOther : ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ Vrows))
    (hF : δ ≤ src.outer.law.toFiniteLaw.prob
      (fun f => (j, .fixedTail f) ∈ Vrows))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U Vrows := by
  obtain ⟨p, r, hPair⟩ :=
    owner_pair_image_mass_of_good_projection src μI' streams U i j hgood
  exact owner_to_owner_W_lower_fixed_tail_bins src streams
    R₀ activity ξ₀ i j p r U Vrows H ell a hH hq hs x hx hD hA hT
    (((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
      (255 / 256 : ℝ)^2) ε δ hPair hmargin
    (fun b hb => hOther p b hb) hO hF hδ hslack hsmall hpairsmall

#print axioms owner_to_owner_W_lower_fixed_tail_good_projection

end CurrentAdditive.DeterministicIndexedMatrix.Sources
