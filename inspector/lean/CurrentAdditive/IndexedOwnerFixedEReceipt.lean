import CurrentAdditive.IndexedOwnerGoodOriginsProd
import CurrentAdditive.GeneratedOwnerIncomingBoundCorrectedClean
import CurrentAdditive.GeneratedOwnerEpsilonCapsClean

/-! Owner-to-owner foreign receipt bound with a supplied exceptional set.
This version consumes the very same conditioned TV witness selected by the
owner initializer, rather than selecting another exceptional set. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

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
    (Vrows : Set (Fin w × Column src))
    (E : Finset (Fin w))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
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
    (ε δ : ℝ)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    ∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
      (1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
        (fun o => (i, .ordinary o) ∈ Vrows)) →
      (Compression.restrictionD
        (W src streams R₀ activity ξ₀) Yevent Vrows ≤ H+ell+a) →
      protectedReceipt src w Vrows j ≤ 2 * (1/256 : ℝ) * δ := by
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
  by_cases hδ : δ ≤ 1
  · by_contra hn
    have hreceipt : 2 * (1/256 : ℝ) * δ <
        protectedReceipt src w Vrows j := lt_of_not_ge hn
    have hOther := owner_other_bins_from_singleton_loss
      src μI streams Yevent i η x (hsingle i hi) hfloor
    rcases protected_receipt_type_dichotomy src w Vrows j δ hreceipt with
      hfixed | hdiagonal
    · have hlower := owner_to_owner_W_lower_fixed_tail_good_projection
        src μI streams R₀ activity ξ₀ i j Yevent Vrows
        H ell a hH hq hs x hx (by omega : 8 ≤ 8192) hA hT
        (hpair i j hij hi hj) hmargin hOther ε δ hO hfixed hδ
        hslack hsmall hpairsmall
      omega
    · have hlower := owner_to_owner_W_lower_good_projection
        src μI streams R₀ activity ξ₀ i j Yevent Vrows
        H ell a hH hq hs x hx (by omega : 8 ≤ 8192) hA hT
        (hpair i j hij hi hj) hmargin hOther ε δ hO hdiagonal hδ
        hslack hsmall hpairsmall
      omega
  · have hbig : 1 < δ := lt_of_not_ge hδ
    have hmax := protected_receipt_le_two_mu src w Vrows j
    nlinarith

#print axioms owner_to_owner_receipt_from_same_E

end CurrentAdditive.DeterministicIndexedMatrix.Sources
