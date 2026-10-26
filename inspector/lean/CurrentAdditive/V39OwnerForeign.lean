import CurrentAdditive.V39TwoStreamImageObstruction
import CurrentAdditive.V39TwoTagOwnerEmbedding
import CurrentAdditive.GeneratedOwnerPairAveraging

set_option maxHeartbeats 5000000

/-! The owner-to-owner two-stream obstruction on literal indexed W inputs. -/

namespace CurrentAdditive.V39OwnerForeign

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39TwoTagOwnerEmbedding

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- Fix the two template bins obtained by the source's averaging step.
Their actual original-tuple pair image has enough product S² mass to
survive the row-prefix deletion. Then the literal W restriction pays C.
The upstream pair-bin mass and other-bin floors remain explicit inputs. -/
theorem owner_to_owner_W_lower_fixed_bins
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (p r : Fin s)
    (U : Set (InternalLabel src streams))
    (V : Set (Fin w × V38IndexedTwoTag.Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
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
      (fun o => (i, .inl o) ∈ V))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (fun f => (j, .inr f) ∈ V))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+4*ε < δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (actualW src streams R₀ activity ξ₀) U V := by
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
    fun o => (i, .inl o) ∈ V
  let G : Set (J src) := fun f => (j, .inr f) ∈ V
  let R : Set (OwnerTemplateTuple src streams i) :=
    ownerRetained src streams i U
  let M := ownerRectangle src streams R₀ activity ξ₀ i j
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
  have hF' : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ (id '' G)) := by
    simpa only [Set.image_id, G] using hF
  have hmatrix : M = ownerRectangle src streams R₀ activity ξ₀ i j := rfl
  have hlower := V39TwoStreamImageObstruction.generated_two_stream_image_restriction_lower src
    R₀ M H ell a hH hq hs x hx hD hA hT
    (μS.prod μS) (ownerBin src streams i)
    (ownerSelector src streams i) id
    (ownerRectangle_ordinary src streams R₀ activity ξ₀ i j)
    input id (by intro E; rfl) p P0 R O G
    (fun z hz => (hlabels z hz).1)
    (fun z hz => ⟨(hlabels z hz).2.1, (hlabels z hz).2.2.1⟩)
    (by
      intro z hz f
      have hh := ownerRectangle_foreign src streams R₀ activity ξ₀ i j
        (input z) f r (hlabels z hz).2.2.2.1
      simpa only [M] using hh.trans
        (congrArg (fun zz => T src R₀ zz f)
          (hlabels z hz).2.2.2.2))
    (by simpa only [Function.id_comp] using hpairFirst)
    hrow
    (by intro P' hsub hloss
        simpa only [Set.image_id] using hret P' hsub hloss)
    ε δ hO hF' hδ hslack hsmall hpairsmall
  exact hlower.trans (ownerRectangle_restriction_le_actualW src streams R₀
    activity ξ₀ i j U V O G
    (by intro o ho; exact ho) (by intro f hf; exact hf))

#print axioms owner_to_owner_W_lower_fixed_bins

end CurrentAdditive.V39OwnerForeign
