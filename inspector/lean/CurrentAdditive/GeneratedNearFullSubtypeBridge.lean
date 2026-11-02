import CurrentAdditive.GeneratedProtocolExtension

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

theorem generated_near_full_from_subtype_prefix
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
    (hUne : U.Nonempty)
    (P : Protocol V U Bool)
    (hP : ∀ (v : V) (z : U),
      P.eval v z =
        N src R (SourceConstruction.activity order edge
          (by omega : 3 ≤ 2^a) r hqSource) ξ₀ z.val v.val)
    (hcost : P.cost ≤ d+a+ell+a)
    (hprefix : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (dom : Fin (2^a) ≃ Fin (2^a))
    (hdommass : ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (fun z =>
        Sum.inl (dom j,z) ∈ V ∧
        rowCode V P a (Sum.inl (dom j,z)) = j)) : False := by
  classical
  let Pext := extendColumnProtocol V U hUne P
  have hPext : ∀ v : V, ∀ z ∈ U,
      Pext.eval v z =
        N src R (SourceConstruction.activity order edge
          (by omega : 3 ≤ 2^a) r hqSource) ξ₀ z v.val := by
    intro v z hz
    rw [extendColumnProtocol_eval V U hUne P v z hz]
    exact hP v ⟨z, hz⟩
  have hcostExt : Pext.cost ≤ d+a+ell+a := by
    rw [extendColumnProtocol_cost V U hUne P]
    exact hcost
  have hprefixExt : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a Pext :=
    (extendColumnProtocol_prefix V U hUne P a).mpr hprefix
  have hdommassExt : ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (fun z =>
        Sum.inl (dom j,z) ∈ V ∧
        rowCode V Pext a (Sum.inl (dom j,z)) = j) := by
    intro j
    simpa only [Pext, extendColumnProtocol_rowCode] using hdommass j
  exact generated_near_full_from_common_prefix src hD R
    order edge loopless hs4 r Δ hΔ hqSource hdegree γ hγ hE gap
    ξ₀ d ell ρ x η hd ha hρ hx hη hqHead hqPow
    hscale hsmall hprofileR hprofileA V hshadow U hU hSchedule
    Pext hPext hcostExt hprefixExt dom hdommassExt

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_near_full_from_subtype_prefix
