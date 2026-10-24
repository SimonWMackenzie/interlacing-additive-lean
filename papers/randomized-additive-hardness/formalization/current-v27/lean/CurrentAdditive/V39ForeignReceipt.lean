import CurrentAdditive.V39OwnerForeign
import CurrentAdditive.GeneratedOwnerEpsilonCapsClean

/-! Current res:foreign on actual ordinary/diagonal W inputs. The strict
contradiction uses the actual retained diagonal probability as delta, so
the conclusion is non-strict with precisely 4*epsilon and one mu family. -/

namespace CurrentAdditive.V39ForeignReceipt

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39TwoTagOwnerEmbedding

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

theorem owner_to_owner_receipt_from_projections
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × V38IndexedTwoTag.Column src))
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hgood : (99/100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod (rowLaw src μI).toFiniteLaw).prob
        (· ∈ (fun t => (InternalStreams.decode src streams t i,
          InternalStreams.decode src streams t j)) '' U))
    (hmargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hOther : ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U, streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z))
    (ε : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i,.inl o) ∈ Vrows))
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8)
    (hupper : Compression.restrictionD
      (actualW src streams R₀ activity ξ₀) U Vrows ≤ H+ell+a) :
    (1/256 : ℝ) *
      (PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (fun f => (j,.inr f) ∈ Vrows) ≤
      (1/256 : ℝ)*(2*q₂*x+4*ε) := by
  classical
  let δ := (PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
    (fun f => (j,.inr f) ∈ Vrows)
  have hδ : δ ≤ 1 := FiniteLaw.prob_le_one _ _
  have hε : 0 ≤ ε := by
    have hp := (ordinaryLaw src).toFiniteLaw.prob_le_one
      (fun o => (i,.inl o) ∈ Vrows)
    linarith
  by_contra hn
  have hslack : 2*q₂*x+4*ε < δ := by
    change ¬ ((1/256 : ℝ)*δ ≤ (1/256 : ℝ)*(2*q₂*x+4*ε)) at hn
    linarith
  obtain ⟨p,r,hPair⟩ := owner_pair_image_mass_of_good_projection src μI streams U i j hgood
  have hlower := V39OwnerForeign.owner_to_owner_W_lower_fixed_bins src streams
    R₀ activity ξ₀ i j p r U Vrows H ell a hH hq hs x hx hD hA hT
    (((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2) ε δ
    hPair hmargin (fun b hb => hOther p b hb) hO (le_refl δ) hδ hslack
    hsmall hpairsmall
  omega

/-- The source's small support threshold supplies the strict pair margin. -/
theorem pair_margin (s : ℕ) (x : ℝ) (hsmall : 2*s*x ≤ 1/1000) :
    49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2 := by
  norm_num at *
  linarith

end CurrentAdditive.V39ForeignReceipt

#print axioms CurrentAdditive.V39ForeignReceipt.owner_to_owner_receipt_from_projections
#print axioms CurrentAdditive.V39ForeignReceipt.pair_margin
