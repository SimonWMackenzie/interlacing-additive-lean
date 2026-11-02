import CurrentAdditive.GeneratedWAlignmentBoundV3
import CurrentAdditive.GeneratedWAlignmentShortProtocol
import CurrentAdditive.GeneratedWUpperAtSchedule

/-! Exact indexed W cost and its original-law near-full restriction profile,
given the generated N theorem on the very same source and activity. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.CommComplexity Workspace.Types.Protocol
open CurrentAdditive.DeterministicParameters

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem indexed_W_full_from_N
    (L Δ n m d : ℕ) (γ : ℚ)
    (hL : 2004 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ) (hd : 3 ≤ d)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : G × (V ⊕ Aux) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (hD : D R₀ = d)
    (hp : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ))
    (hadm : Admissible L Δ n m
      CurrentAdditive.DeterministicAdmissibility.sourceC128Ceil γ)
    (hN : D (N src R₀ activity ξ₀) =
      d+(L+3)/4+4*L+(L+3)/4+1 ∧
      ∀ (U : Set (Column src))
        (Vrows : Set (Row (I := G × (V ⊕ Aux)) src)),
        1-(η L Δ γ : ℝ) ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U) →
        1-(η L Δ γ : ℝ) ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ Vrows) →
        d+(L+3)/4+4*L+(L+3)/4+1 ≤
          Paper2.Compression.restrictionD (N src R₀ activity ξ₀) U Vrows) :
    D (W src streams R₀ activity ξ₀) =
        d+2*((L+3)/4)+6*L+1 ∧
    ∀ (R : Set (Fin (w L) × Column src))
      (Yevent : Set (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))),
      1 - (δU L Δ γ : ℝ) ≤
        (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R) →
      (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent) →
      d+2*((L+3)/4)+6*L+1 ≤
        Paper2.Compression.restrictionD
          (W src streams R₀ activity ξ₀) Yevent R := by
  classical
  have hnear (R : Set (Fin (w L) × Column src))
      (Yevent : Set (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)))
      (hR : 1 - (δU L Δ γ : ℝ) ≤
        (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R))
      (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent)) :
      d+2*((L+3)/4)+6*L+1 ≤
        Paper2.Compression.restrictionD
          (W src streams R₀ activity ξ₀) Yevent R := by
    by_contra hn
    have hshort : Paper2.Compression.restrictionD
        (W src streams R₀ activity ξ₀) Yevent R ≤
        d+(L+3)/4+4*L+(L+3)/4+2*L := by omega
    obtain ⟨P, hPcost, hP⟩ :=
      indexed_W_short_protocol_from_restriction src streams
        R₀ activity ξ₀ R Yevent _ hshort
    exact indexed_W_short_impossible L Δ n m d γ hL hΔ hγ hd
      src μI streams R₀ activity ξ₀ hD hp hadm hN.2
      R Yevent hR hY P hP hPcost
  have hδ : (0 : ℝ) ≤ (δU L Δ γ : ℝ) := by
    exact_mod_cast (deltaU_pos L Δ γ hΔ hγ).le
  have hθ1 : (θ L : ℝ) ≤ 1 := by
    have hQ : (1 : ℚ) ≤ Q L := by exact_mod_cast Q_pos L
    have hqθ := Q_theta L
    have hθp := theta_pos L
    have hle : θ L ≤ (Q L : ℚ) * θ L := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hθp.le]
    exact_mod_cast (by linarith : θ L ≤ (1 : ℚ))
  have hRfull : 1 - (δU L Δ γ : ℝ) ≤
      (indexedFirstRowLaw src (w_pos L)).prob
        (· ∈ (Set.univ : Set (Fin (w L) × Column src))) := by
    simpa using (show 1 - (δU L Δ γ : ℝ) ≤ 1 by linarith)
  have hYfull : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob
      (· ∈ (Set.univ : Set (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)))) := by
    simpa using hθ1
  have hfull := hnear Set.univ Set.univ hRfull hYfull
  have huniv : Paper2.Compression.restrictionD
      (W src streams R₀ activity ξ₀) Set.univ Set.univ =
      D (W src streams R₀ activity ξ₀) := by
    have hh := pullback_D_eq_of_surjective
      (W src streams R₀ activity ξ₀) Subtype.val Subtype.val
      (fun z => ⟨⟨z, Set.mem_univ z⟩, rfl⟩)
      (fun z => ⟨⟨z, Set.mem_univ z⟩, rfl⟩)
    exact hh
  rw [huniv] at hfull
  have hu := generated_W_upper_at_schedule L d src streams R₀ activity ξ₀ hN.1
  constructor
  · omega
  · exact hnear

#print axioms indexed_W_full_from_N

end CurrentAdditive.DeterministicIndexedMatrix.Sources
