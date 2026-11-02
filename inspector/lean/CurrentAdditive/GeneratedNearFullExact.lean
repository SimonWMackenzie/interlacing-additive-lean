import CurrentAdditive.GeneratedInitialState
import CurrentAdditive.GeneratedCollisionEndpointExact

/-!
The graph-derived collision branch is fed into the actual indexed frontier.
The remaining protocol inputs describe the common-prefix branch itself; no
lower-bound or contradiction is assumed.  This theorem exposes exactly what
the indexed common-prefix and row-law transport adapters must supply.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open Paper2.SourceSupportFrontier
open Paper2.SourceProjectionDiagonal

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem generated_near_full_from_indexed_branches_exact
    (hD : 8 ≤ D)
    (R : X → Y → Bool)
    (order : SourceConstruction.Items s G ≃
      Fin (Fintype.card (SourceConstruction.Items s G)))
    (edge : E → Bool → G)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hs4 : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hqSource : q₂ = SourceItems.sourceQ0 (Fin (4*s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : G → Fin 3,
      γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    (ξ₀ : Tail s Y) (d a ell : ℕ) (ρ x η : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a)
    (hρ : 0 < ρ) (hx : 0 < x) (hη : 0 < η)
    (hsPow : s = 2 ^ a) (hqHead : q₁ + 3 = s + 1)
    (hqPow : q₂ = 2 ^ ell)
    (hscale : 4 * (s : ℝ)^2 * ρ ≤ 1)
    (hsmall : Paper2.SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (hprofileR : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      ρ (d : ℤ))
    (hprofileA : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x ((d+a : ℕ) : ℤ))
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s)
    (hshadow : 1 - deletionAllowance (V := G) (E := E) γ Δ s ≤
      (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ s hs4).toFiniteLaw.prob
        (· ∈ rawItemShadow src V))
    (K : Fin s → Set src.inner.Label)
    (hKmass : ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (· ∈ K j))
    (hKrow : ∀ j z, z ∈ K j →
      Sum.inl (j,z) ∈ indexedBranchRows src V rowCode j)
    (U : Set (Column src))
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hSchedule : 8 * s * q₁ + 1024 * s * η * q₂ <
      witnessDensity γ * q₂ / 4)
    (P : ∀ j : Fin s,
      Workspace.Types.Protocol.Protocol
        (indexedBranchRows src V rowCode j) (Column src) Bool)
    (hPcorrect : ∀ j (v : indexedBranchRows src V rowCode j)
      (z : Column src), z ∈ U →
      (P j).eval v z =
        N src R (SourceConstruction.activity order edge
          (by omega : 3 ≤ s) r hqSource) ξ₀ z v.val)
    (hPcost : ∀ j, (P j).cost ≤ d+a+ell) : False := by
  classical
  have hKweak : ∀ j, (1/7 : ℝ) <
      src.inner.law.toFiniteLaw.prob (· ∈ K j) := by
    intro j
    linarith [hKmass j]
  have hxcap : 2 * (s : ℝ) * ρ ≤ 1/8 := by
    -- The graph/item scale is stronger than the template-cap threshold.
    have hspos : (4 : ℝ) ≤ s := by exact_mod_cast hs4
    nlinarith [hscale, hρ]
  obtain ⟨j, hj⟩ := select_generated_collision_branch src
    (by omega : 2 ≤ D) edge loopless hs4 r Δ hΔ hqSource
    hdegree γ hγ hE gap V rowCode hshadow K hKweak U η
    (2 * (s : ℝ) * ρ) hη hxcap hU hSchedule
  let part := assignedCoordinates edge r hqSource μX
    (rawItemShadow src V) (rawItemCode src rowCode) j
  let bad := branchBad src (K j) U (2 * (s : ℝ) * ρ)
  have hmany : 3 * bad.card < (part \ bad).card := hj.2.1
  let Vj := indexedBranchRows src V rowCode j
  let initial := initialIndexedState src U Vj (P j) bad part
  have hi := initialIndexedState_invariants src U Vj (P j)
    (K j) (2 * (s : ℝ) * ρ) x bad part rfl hsmall
  change initial.attachments ⊆ initial.coordinates ∧
    initial.coordinates.card + bad.card = q₂ ∧
    (∀ α ∈ initial.coordinates,
      Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
        Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw
          (initial.support α)) ∧
    (∀ α ∈ initial.attachments,
      (3/4 : ℝ) ≤ Paper2.SourceSupportStep.mass
        src.gamma.law.toFiniteLaw (initial.support α)) ∧
    (∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Column.diagonal (α, γ) ∈ initial.columns) at hi
  have hdata : ∀ α ∈ initial.attachments,
      (∀ r : Fin q₁, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
        (fun u => (r,u) ∈ (fun z => src.inner.decode z α) '' K j)) ∧
      ∃ i₁ i₂ i₀ : SourceConstruction.Items s G,
        ∃ p p' : Fin s,
        p ≠ p' ∧
        SourceConstruction.activity order edge (by omega : 3 ≤ s)
          r hqSource i₁ α = some p ∧
        SourceConstruction.activity order edge (by omega : 3 ≤ s)
          r hqSource i₂ α = some p' ∧
        SourceConstruction.activity order edge (by omega : 3 ≤ s)
          r hqSource i₀ α = none ∧
        ∀ t : Fin 3, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ Vj) := by
    intro α hα
    exact usable_assigned_collision_data src order edge hs4 r hqSource
      ρ hscale V rowCode (K j) U j α (by simpa [initial,
        initialIndexedState, part, bad] using hα)
  have hcorrect : ∀ (v : Vj), ∀ z ∈ initial.columns,
      initial.protocol.eval v z =
        N src R (SourceConstruction.activity order edge
          (by omega : 3 ≤ s) r hqSource) ξ₀ z v.val := by
    intro v z hz
    exact hPcorrect j v z (by simpa [initial,
      initialIndexedState] using hz)
  have hexcess : 3 * bad.card < initial.attachments.card := by
    simpa [initial, initialIndexedState] using hmany
  have hscale' : 2 * (s : ℝ) * ρ ≤ 1 := by
    nlinarith [hxcap]
  exact indexed_collision_endpoint_contradiction_exact src hD R
    (SourceConstruction.activity order edge (by omega : 3 ≤ s)
      r hqSource) ξ₀ d a ell ρ x hd ha hρ hx hsPow hqHead hqPow
    hscale' hsmall hprofileR hprofileA j (K j)
    Vj (fun z hz => hKrow j z hz) (hKmass j) initial
    hcorrect (hPcost j) hi.1 bad.card hi.2.1 hexcess
    hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
    (fun α hα r => (hdata α hα).1 r)
    (fun α hα => (hdata α hα).2)

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_near_full_from_indexed_branches_exact
