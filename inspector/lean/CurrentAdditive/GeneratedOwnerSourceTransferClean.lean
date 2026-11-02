import CurrentAdditive.GeneratedOwnerEpsilonCapsClean

/-! Appendix I:497--511 and 663--698, specialized to the actual global
retained tuple-column event Y' and the source's τ=η/2. -/

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

/-- If the actual global tuple-column event has mass at least v, then every
different nonexceptional origin j sends at most `2μδ` protected mass to a
short owner node i. This includes both original fixed-tail and diagonal
tagged populations; the event may have mass only v, not near one. -/
theorem owner_to_owner_source_receipt_bound
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (Yglobal : Set (InternalLabel src streams))
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
    (v η : ℝ)
    (hv : 0 < v)
    (hvY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yglobal))
    (hη : 0 < η)
    (hfloor : 2*s*x ≤ 1 - η * (s : ℝ) / (2 * (255/256 : ℝ)))
    (hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2)
    (ε δ : ℝ)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    ∃ E : Finset (Fin w),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR
        1024 v (η/2) ∧
      ∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
        (1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
          (fun o => (i, .ordinary o) ∈ Vrows)) →
        (Compression.restrictionD
          (W src streams R₀ activity ξ₀) Yglobal Vrows ≤ H+ell+a) →
        protectedReceipt src w Vrows j ≤ 2 * (1/256 : ℝ) * δ := by
  have hv1 : v ≤ 1 :=
    hvY.trans (streams.law.toFiniteLaw.prob_le_one (· ∈ Yglobal))
  exact owner_to_owner_incoming_receipt_bound_conditional
    src μI streams R₀ activity ξ₀ Yglobal Yglobal (Set.Subset.rfl)
    Vrows H ell a hH hq hs x hx hD hA hT
    v (η/2) η hv hvY (by linarith)
    (owner_conditioning_epsilon_le_point01 v η hv.le hv1)
    (owner_conditioning_epsilon_le_eta_half v η)
    hfloor hmargin ε δ hslack hsmall hpairsmall

#print axioms owner_to_owner_source_receipt_bound

end CurrentAdditive.DeterministicIndexedMatrix.Sources
