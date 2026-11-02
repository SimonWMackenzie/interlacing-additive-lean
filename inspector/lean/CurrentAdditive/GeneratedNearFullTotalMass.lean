import CurrentAdditive.GeneratedShadowMass

/-! Source-specific near-full contradiction with all three retention
premises extracted from the actual indexed row and column laws. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := 2^a) μX μY)

theorem generated_near_full_of_total_mass
    [Nonempty (Fin (4*2^a))] [Nonempty (Fin (2^a-3))]
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
    (hV : 1 - η ≤
      (rowLaw src
        (itemLaw (G := Fin (4*2^a)) (V := G) (A := Fin (2^a-3)))).toFiniteLaw.prob
          (· ∈ V))
    (U : Set (Column src))
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hηshadow : η ≤ deletionAllowance (V := G) (E := E) γ Δ (2^a))
    (hηrow : (256/255 : ℝ) * (2^a : ℕ) * η ≤ 1/1000)
    (hηfixed : 256 * η ≤ 1/100)
    (hβbudget : ((2^a : ℕ) : ℝ) * β ≤ 1/10000)
    (hSchedule : 8 * (2^a) * q₁ + 1024 * (2^a) * η * q₂ <
      witnessDensity γ * q₂ / 4)
    (hshort : Paper2.Compression.restrictionD
      (N src R (SourceConstruction.activity order edge
        (by omega : 3 ≤ 2^a) r hqSource) ξ₀) U V ≤ d+a+ell+a) : False := by
  letI : Nonempty (Fin (4*2^a)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (2^a-3)) := ⟨⟨0, by omega⟩⟩
  have hshadow := raw_item_shadow_retained_of_total
    (src := src) (E := E) hs4 γ Δ V η hV hηshadow
  have hrow : ∀ p : Fin (2^a), (999/1000 : ℝ) ≤
      src.inner.law.toFiniteLaw.prob
        (fun z => (Sum.inl (p,z) :
          Row (I := SourceConstruction.Items (2^a) G) src) ∈ V) := by
    intro p
    exact retained_each_template_bin_of_total src
      (itemLaw (G := Fin (4*2^a)) (V := G) (A := Fin (2^a-3)))
      V η hV hηrow p
  have hfixed := retained_fixed_tail_of_total src U η hU hηfixed
  exact generated_near_full_from_source_separation src R order edge
    loopless hs4 r Δ hΔ hqSource hdegree γ hγ hE gap ξ₀ d ell
    ρ x β η hd ha hρ hx hβ hη hqHead hqPow hscale hsmall
    hprofileR hprofileA hprofileT V hshadow hrow U hU hfixed
    hβbudget hSchedule hshort

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_near_full_of_total_mass
