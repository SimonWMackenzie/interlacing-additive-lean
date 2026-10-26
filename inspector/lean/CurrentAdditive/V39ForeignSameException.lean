import CurrentAdditive.V39ForeignReceipt
import CurrentAdditive.IndexedOwnerFixedEReceipt

/-! Actual current foreign receipt from the same exceptional set used by
an owner frontier. No second conditioning witness is selected. The pair
image and all other-bin supports are derived from the actual event's TV
bounds, and the conclusion uses one diagonal family with multiplier 4. -/

namespace CurrentAdditive.V39ForeignSameException

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

theorem owner_to_owner_receipt_from_same_E
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (Yevent : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × V38IndexedTwoTag.Column src))
    (E : Finset (Fin w))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (θ η : ℝ) (hθ : 0 < θ)
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hη : 0 < η)
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent)
          (hθ.trans_le hY)) (rowLaw src μI).toFiniteLaw
        (InternalStreams.decode src streams) J ≤
          CurrentAdditive.conditioningEpsilonR 1024 θ (η/2))
    (hfloor : 2*s*x ≤ 1 - η * (s : ℝ) / (2 * (255/256 : ℝ)))
    (hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2)
    (ε : ℝ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    ∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
      (1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
        (fun o => (i, .inl o) ∈ Vrows)) →
      (Compression.restrictionD
        (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) Yevent Vrows ≤ H+ell+a) →
      (1/256 : ℝ) *
        (PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
          (fun f => (j,.inr f) ∈ Vrows) ≤
        (1/256 : ℝ)*(2*q₂*x+4*ε) := by
  classical
  have hv1 : θ ≤ 1 := hY.trans
    (streams.law.toFiniteLaw.prob_le_one (· ∈ Yevent))
  have hεpair : CurrentAdditive.conditioningEpsilonR 1024 θ (η/2) ≤
      1/100 := owner_conditioning_epsilon_le_point01 θ η hθ.le hv1
  have hεsingle : CurrentAdditive.conditioningEpsilonR 1024 θ (η/2) ≤
      η/2 := owner_conditioning_epsilon_le_eta_half θ η
  have hsingle : ∀ i : Fin w, i ∉ E →
      (rowLaw src μI).toFiniteLaw.prob
        (fun k => k ∉ (InternalStreams.decode src streams · i) '' Yevent) ≤ η/2 := by
    intro i hi
    let e : Fin 1 → Fin w := fun _ => i
    have hsubset : Finset.univ.image e ⊆
        (Finset.univ : Finset (Fin w)) \ E := by
      intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
      simp [e, hi]
    have hcard : (Finset.univ.image e).card ≤ 8 := by
      calc
        (Finset.univ.image e).card ≤ (Finset.univ : Finset (Fin 1)).card :=
          Finset.card_image_le
        _ = 1 := by decide
        _ ≤ 8 := by omega
    exact (owner_singleton_loss_of_projectionTV src μI streams
      Yevent Yevent (Set.Subset.rfl) (hθ.trans_le hY) i
      (CurrentAdditive.conditioningEpsilonR 1024 θ (η/2))
      (hTV (Finset.univ.image e) hsubset hcard)).trans hεsingle
  have hpair : ∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
      (99 / 100 : ℝ) ≤
        ((rowLaw src μI).toFiniteLaw.prod
          (rowLaw src μI).toFiniteLaw).prob
            (· ∈ (fun t =>
              (InternalStreams.decode src streams t i,
               InternalStreams.decode src streams t j)) '' Yevent) := by
    intro i j hij hi hj
    let e : Fin 2 → Fin w := fun k => if k.val = 0 then i else j
    have he_mem (k : Fin 2) : e k ∉ E := by
      fin_cases k <;> simp [e, hi, hj]
    have hsubset : Finset.univ.image e ⊆
        (Finset.univ : Finset (Fin w)) \ E := by
      intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
      simp [he_mem k]
    have hcard : (Finset.univ.image e).card ≤ 8 := by
      calc
        (Finset.univ.image e).card ≤ (Finset.univ : Finset (Fin 2)).card :=
          Finset.card_image_le
        _ = 2 := by decide
        _ ≤ 8 := by omega
    exact owner_good_pair_image_of_projectionTV src μI streams
      Yevent Yevent (Set.Subset.rfl) (hθ.trans_le hY)
      i j hij (CurrentAdditive.conditioningEpsilonR 1024 θ (η/2))
      hεpair (hTV (Finset.univ.image e) hsubset hcard)
  intro i j hij hi hj hO hupper
  have hOther := owner_other_bins_from_singleton_loss
    src μI streams Yevent i η x (hsingle i hi) hfloor
  exact V39ForeignReceipt.owner_to_owner_receipt_from_projections src μI streams
    R₀ activity ξ₀ i j Yevent Vrows H ell a hH hq hs x hx
    (by omega : 8 ≤ 8192) hA hT (hpair i j hij hi hj) hmargin hOther
    ε hO hsmall hpairsmall hupper

end CurrentAdditive.V39ForeignSameException

#print axioms CurrentAdditive.V39ForeignSameException.owner_to_owner_receipt_from_same_E
