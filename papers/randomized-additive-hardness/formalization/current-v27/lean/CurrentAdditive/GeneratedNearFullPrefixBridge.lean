import CurrentAdditive.GeneratedBranchRelabel

/-!
Bridge from an actual common Alice prefix to the generated-source graph
collision contradiction.  The only prefix facts assumed are those supplied
by source-specific separation: a complete prefix and its dominant-bin
bijection with retained inner-label mass.  The graph branches use bins,
not the differently numbered transcript labels.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open Paper2.SourceProtocolPrefix
open Workspace.Types.Protocol

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ a : ℕ} [NeZero (2^a)] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := 2^a) μX μY)

theorem generated_near_full_from_common_prefix
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (order : SourceConstruction.Items (2^a) G ≃
      Fin (Fintype.card (SourceConstruction.Items (2^a) G)))
    (edge : E → Bool → G)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hs4 : 4 ≤ 2^a) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hqSource : q₂ = SourceItems.sourceQ0 (Fin (4*2^a)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : G → Fin 3,
      γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    (ξ₀ : Tail (2^a) Y) (d ell : ℕ) (ρ x η : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a)
    (hρ : 0 < ρ) (hx : 0 < x) (hη : 0 < η)
    (hqHead : q₁ + 3 = 2^a + 1) (hqPow : q₂ = 2 ^ ell)
    (hscale : 4 * ((2^a : ℕ) : ℝ)^2 * ρ ≤ 1)
    (hsmall : Paper2.SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (hprofileR : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      ρ (d : ℤ))
    (hprofileA : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x ((d+a : ℕ) : ℤ))
    (V : Set (Row (I := SourceConstruction.Items (2^a) G) src))
    (hshadow : 1 - deletionAllowance (V := G) (E := E) γ Δ (2^a) ≤
      (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ (2^a) hs4).toFiniteLaw.prob
        (· ∈ rawItemShadow src V))
    (U : Set (Column src))
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hSchedule : 8 * (2^a) * q₁ + 1024 * (2^a) * η * q₂ <
      witnessDensity γ * q₂ / 4)
    (P : Protocol V (Column src) Bool)
    (hP : ∀ v : V, ∀ z ∈ U,
      P.eval v z =
        N src R (SourceConstruction.activity order edge
          (by omega : 3 ≤ 2^a) r hqSource) ξ₀ z v.val)
    (hcost : P.cost ≤ d+a+ell+a)
    (hprefix : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (dom : Fin (2^a) ≃ Fin (2^a))
    (hdommass : ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (fun z =>
        Sum.inl (dom j,z) ∈ V ∧
        rowCode V P a (Sum.inl (dom j,z)) = j)) : False := by
  classical
  let code : Row (I := SourceConstruction.Items (2^a) G) src → Fin (2^a) :=
    dominantBinCode V P a dom
  let K : Fin (2^a) → Set src.inner.Label := fun i =>
    {z | Sum.inl (i,z) ∈ V ∧ code (.inl (i,z)) = i}
  let branches : ∀ i : Fin (2^a),
      Protocol (indexedBranchRows src V code i) (Column src) Bool :=
    fun i => dominantBinProtocol V P a dom i
  have hKmass : ∀ i, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (· ∈ K i) := by
    intro i
    simpa [K, code, dominantBinCode, Equiv.apply_eq_iff_eq_symm_apply]
      using hdommass (dom.symm i)
  have hKrow : ∀ i z, z ∈ K i →
      Sum.inl (i,z) ∈ indexedBranchRows src V code i := by
    intro i z hz
    exact hz
  have hBcost : ∀ i, (branches i).cost ≤ d+a+ell := by
    intro i
    exact dominantBinProtocol_cost V P a (d+a+ell) dom i
      hprefix (by omega)
  have hBcorrect : ∀ i (v : indexedBranchRows src V code i)
      (z : Column src), z ∈ U →
      (branches i).eval v z =
        N src R (SourceConstruction.activity order edge
          (by omega : 3 ≤ 2^a) r hqSource) ξ₀ z v.val := by
    intro i v z hz
    change (dominantBinProtocol V P a dom i).eval v z = _
    rw [dominantBinProtocol_eval V P a dom i hprefix v z]
    exact hP ⟨v.val, v.property.1⟩ z hz
  exact generated_near_full_from_indexed_branches_exact src hD R
    order edge loopless hs4 r Δ hΔ hqSource hdegree γ hγ hE gap
    ξ₀ d a ell ρ x η hd ha hρ hx hη rfl hqHead hqPow
    hscale hsmall hprofileR hprofileA V code hshadow K hKmass
    hKrow U hU
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hSchedule)
    branches hBcorrect hBcost

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_near_full_from_common_prefix
