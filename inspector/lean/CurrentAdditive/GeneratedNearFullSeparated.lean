import CurrentAdditive.GeneratedPrefixDominantTransfer

/-!
Actual indexed near-full graph collision after source-specific separation.
Assuming a short restriction protocol, the proof obtains a real minimizing
protocol, applies generated-source separation to its template/fixed-tail
submatrix, and then uses the checked graph/frontier/exact-source endpoint.
All remaining premises are base/source profiles, retained-law estimates,
the graph gap, and displayed numerical inequalities.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open Workspace.Types.Protocol

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := 2^a) μX μY)

theorem generated_near_full_from_source_separation
    (R : X → Y → Bool)
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
    (ξ₀ : Tail (2^a) Y) (d ell : ℕ) (ρ x β η : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a)
    (hρ : 0 < ρ) (hx : 0 < x) (hβ : 0 < β) (hη : 0 < η)
    (hqHead : q₁ + 3 = 2^a + 1) (hqPow : q₂ = 2 ^ ell)
    (hscale : 4 * ((2^a : ℕ) : ℝ)^2 * ρ ≤ 1)
    (hsmall : Paper2.SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (hprofileR : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      ρ (d : ℤ))
    (hprofileA : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x ((d+a : ℕ) : ℤ))
    (hprofileT : RestrictionProfile (T src R)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)
      β ((d+a+ell : ℕ) : ℤ))
    (V : Set (Row (I := SourceConstruction.Items (2^a) G) src))
    (hshadow : 1 - deletionAllowance (V := G) (E := E) γ Δ (2^a) ≤
      (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ (2^a) hs4).toFiniteLaw.prob
        (· ∈ rawItemShadow src V))
    (hrow : ∀ p : Fin (2^a), (999/1000 : ℝ) ≤
      src.inner.law.toFiniteLaw.prob
        (fun z => (Sum.inl (p,z) :
          Row (I := SourceConstruction.Items (2^a) G) src) ∈ V))
    (U : Set (Column src))
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hfixed : (99/100 : ℝ) ≤ src.outer.law.toFiniteLaw.prob
      (fun js => (Column.fixedTail js : Column src) ∈ U))
    (hβbudget : ((2^a : ℕ) : ℝ) * β ≤ 1/10000)
    (hSchedule : 8 * (2^a) * q₁ + 1024 * (2^a) * η * q₂ <
      witnessDensity γ * q₂ / 4)
    (hshort : Paper2.Compression.restrictionD
      (N src R (SourceConstruction.activity order edge
        (by omega : 3 ≤ 2^a) r hqSource) ξ₀) U V ≤ d+a+ell+a) : False := by
  classical
  let activity := SourceConstruction.activity order edge
    (by omega : 3 ≤ 2^a) r hqSource
  obtain ⟨P, hPcost, hPcompute⟩ :=
    short_protocol_from_restriction src R activity ξ₀ U V
      (d+a+ell+a) hshort
  have hUne : U.Nonempty := by
    by_contra hn
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst U
    norm_num at hfixed
  have hPcomputeB : P.Computes
      (fun (v : V) (z : U) => B src R activity ξ₀ v.val z.val) := by
    intro v z
    exact hPcompute v z
  obtain ⟨Φ, hΦ, hprefix, RV, hRV, hactive, dom, hdom⟩ :=
    B_template_fixedTail_separation_998 src R activity ξ₀ V U
      (d+a+ell) β ha (by omega) hβ hprofileT hrow hβbudget
      hfixed P (by omega) hPcomputeB
  have hdommass : ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (fun z =>
        (Sum.inl (dom j,z) :
          Row (I := SourceConstruction.Items (2^a) G) src) ∈ V ∧
        Paper2.SourceProtocolPrefix.rowCode V P a
          (Sum.inl (dom j,z)) = j) :=
    dominant_mass_on_actual_rowCode src V U P Φ hΦ dom
      (fun j => (hdom j).1)
  exact generated_near_full_from_subtype_prefix src
    (by omega : 8 ≤ 8192) R order edge loopless hs4 r Δ hΔ hqSource
    hdegree γ hγ hE gap ξ₀ d ell ρ x η hd ha hρ hx hη
    hqHead hqPow hscale hsmall hprofileR hprofileA V hshadow
    U hU hSchedule hUne P hPcompute (by omega) hprefix dom hdommass

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_near_full_from_source_separation
