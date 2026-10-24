import CurrentAdditive.GeneratedOwnerConditionedProjectionsClean
import CurrentAdditive.GeneratedOwnerFixedTailClean
import CurrentAdditive.GeneratedOwnerProtectedReceiptCore

/-! Appendix I:663--698 with the manuscript's actual rare tuple-column
retention. Singleton deletion comes from conditioning, not from a near-one
mass assumption on the full retained tuple set. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

/-- The source's owner-to-owner receipt bound on the literal W node.
Only a positive conditioned tuple event Yevent inside U is needed; the
original-law singleton and pair image bounds follow from one common
exceptional set. For δ>1 the receipt cap is automatic. -/
theorem owner_to_owner_incoming_receipt_bound_conditional
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (U Yevent : Set (InternalLabel src streams))
    (hYU : Yevent ⊆ U)
    (Vrows : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x)
    (hD : 8 * 1024 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (v τ η : ℝ)
    (hv : 0 < v)
    (hvY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hτ : 0 < τ)
    (hεpair : CurrentAdditive.conditioningEpsilonR 1024 v τ ≤ 1 / 100)
    (hεsingle : CurrentAdditive.conditioningEpsilonR 1024 v τ ≤ η/2)
    (hfloor : 2*s*x ≤ 1 - η * (s : ℝ) / (2 * (255/256 : ℝ)))
    (hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2)
    (ε δ : ℝ)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    ∃ E : Finset (Fin w),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      ∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
        (1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
          (fun o => (i, .ordinary o) ∈ Vrows)) →
        (Compression.restrictionD
          (W src streams R₀ activity ξ₀) U Vrows ≤ H+ell+a) →
        protectedReceipt src w Vrows j ≤ 2 * (1/256 : ℝ) * δ := by
  obtain ⟨E, hE, hsingle, hpair⟩ :=
    owner_good_singletons_and_pairs_from_conditioning
      src μI streams U Yevent hYU v τ η hv hvY hτ hD
      hεpair hεsingle
  refine ⟨E, hE, ?_⟩
  intro i j hij hi hj hO hupper
  by_cases hδ : δ ≤ 1
  · by_contra hn
    have hreceipt : 2 * (1/256 : ℝ) * δ <
        protectedReceipt src w Vrows j := lt_of_not_ge hn
    have hOther := owner_other_bins_from_singleton_loss
      src μI streams U i η x (hsingle i hi) hfloor
    rcases protected_receipt_type_dichotomy src w Vrows j δ hreceipt with
      hfixed | hdiagonal
    · have hlower := owner_to_owner_W_lower_fixed_tail_good_projection
        src μI streams R₀ activity ξ₀ i j U Vrows
        H ell a hH hq hs x hx (by omega : 8 ≤ D) hA hT
        (hpair i j hij hi hj) hmargin hOther ε δ hO hfixed hδ
        hslack hsmall hpairsmall
      omega
    · have hlower := owner_to_owner_W_lower_good_projection
        src μI streams R₀ activity ξ₀ i j U Vrows
        H ell a hH hq hs x hx (by omega : 8 ≤ D) hA hT
        (hpair i j hij hi hj) hmargin hOther ε δ hO hdiagonal hδ
        hslack hsmall hpairsmall
      omega
  · have hbig : 1 < δ := lt_of_not_ge hδ
    have hmax := protected_receipt_le_two_mu src w Vrows j
    nlinarith

#print axioms owner_to_owner_incoming_receipt_bound_conditional

end CurrentAdditive.DeterministicIndexedMatrix.Sources
