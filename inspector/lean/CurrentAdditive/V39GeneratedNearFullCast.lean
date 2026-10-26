import CurrentAdditive.V39GeneratedNearFull

/-! Keep the generated power-of-two selector type literally. Its equality
to the graph's repeated width is used by the same Fin.cast as graphActivity. -/

namespace CurrentAdditive.V39GeneratedNearFullCast

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicIndexedMatrix CurrentAdditive.EdgeSourceMatrix
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge

variable {D t n m r nx ny q₂ : ℕ}
  [NeZero (2^t)] [NeZero (2^t-2)] [NeZero q₂]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

theorem restriction_lower
    (src : SourceData (D := D) (q₁ := 2^t-2) (q₂ := q₂) (s := 2^t) μX μY)
    (hwidth : q₂ = LiteralEdgeEncoder.Width (2^t) m r)
    (hD : 8 ≤ D) (hs : 4 ≤ 2^t) (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (Δ : ℕ) (hΔ : 0 < Δ) (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, γ * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (R : Fin nx → Fin ny → Bool) (d ell : ℕ) (hd : 2 ≤ d)
    (hq₂ : q₂ = 2^ell) (hq2 : 2 ≤ q₂)
    (x ρ η : ℝ) (hx : 0 < x) (hρ : 0 < ρ) (hη : 0 < η)
    (hηSmall : η < 1/100)
    (hηTemplate : (256/255 : ℝ)*(2^t : ℕ)*η ≤ 1/1000)
    (hηAllowance : η ≤ deletionAllowance (V := Fin n) (E := Fin m) γ Δ (2^t))
    (hassign : 4*((2^t : ℕ) : ℝ)^2*ρ ≤ 1)
    (hmargin : 8*((2^t : ℕ) : ℝ)*(2^t-2 : ℕ) + 1024*(2^t : ℕ)*η*q₂ < (γ/24)*q₂/4)
    (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprefixGap : 2*(2 : ℝ)^t*x < 999/1000)
    (hdominant : (998/1000 : ℝ) ≤ 999/1000 - 2*((2^t : ℕ)-1 : ℕ)*x)
    (hprofileR : V38RestrictionProfiles.TwoThresholdProfile R
      μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A (toSources src) R)
      src.gamma.law.toFiniteLaw
      (product (uniform (2^t-2)) μX).toFiniteLaw x ((d+t : ℕ) : ℤ))
    (hprofileT : V38RestrictionProfiles.TwoThresholdProfile (V39GeneratedPrefix.template src R)
      src.inner.law.toFiniteLaw (product (uniform q₂) src.gamma.law).toFiniteLaw
      x ((d+t+ell : ℕ) : ℤ))
    (W : Set (src.Row (ni := 4*(2^t)*(n+(2^t-3))))) (U : Set src.Column)
    (hW : 1-η ≤ (src.rowLaw
      (μI := LiteralEdgeEncoder.indexedItemLaw (2^t) n hs hn)).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U)) :
    d+t+ell+t+1 ≤ Compression.restrictionD
      (fun c a => src.B R (fun i α => LiteralEdgeEncoder.indexedActivity
        (by omega : 3 ≤ 2^t) edge i (Fin.cast hwidth α)) a c) U W := by
  cases hwidth
  exact V39GeneratedNearFull.restriction_lower src hD hs hn edge loopless Δ hΔ hdegree
    γ hγ hE gap R d ell hd hq₂ hq2 x ρ η hx hρ hη hηSmall hηTemplate hηAllowance
    hassign hmargin hsmall hprefixGap hdominant hprofileR hprofileA hprofileT W U hW hU

end CurrentAdditive.V39GeneratedNearFullCast

#print axioms CurrentAdditive.V39GeneratedNearFullCast.restriction_lower
