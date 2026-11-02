import CurrentAdditive.QuarticSourceAmplifierUpperRank

/-! Full source quantifier scope: universal upper/rank/YES for arbitrary base F;
base cost, base profile, and graph gap only enter the NO implication. -/

namespace Paper2.SourceAmplifierFullScope

open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
  SourceSurvivingCollisions Workspace.Types.CommComplexity RankLeaves

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y]
variable
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (L : ℕ)
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hrep : 1 ≤ rep) (hΔ : 0 < Δ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (ξ₀ : Tail (width L) Y)
    (w r Q q : ℕ) (hw : w = 2 ^ r) (hw2 : 2 ≤ w)
    (hQ : Q = 2 ^ q)
    (ηq : ℚ)
    (hηq : (ηq : ℝ) = deletionAllowance (V := V) (E := E) γ Δ (width L))
    (hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop w Q ηq)
    (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)))
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      CurrentAdditive.QuarticSchedule.E27 Q ηq ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 16)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hsmallwx : (w : ℝ) * x L ≤ 1 / 10000)
    (hmargin : 2 * w * x L +
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1)
    (hL : 1 ≤ L)
    (hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (w : ℝ))))

include hinner houter hwide href loopless hrep hΔ hdegree hincident
  hγ hE hscale hcountSource hw hw2 hQ hηq hquarter hsmall
  hfirst hlast hKcheck hxsmall hstar hsmallwx hmargin hL hbridge in
/-- Every source-faithful finite mathematical clause is about the one same
full-product successor. The graph-only parameters must satisfy the listed
quartic guards; their all-large compiler is proved elsewhere. -/
theorem source_successor_full_scope27 :
    let h := exponent L + outerExponent L + exponent L + r + q
    let S := SourceMatrix.successor (q₁ := width L - 2) F
      (SourceConstruction.activity order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq)
      ξ₀ w Q
    D S ≤ D F + h + 1 ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D S ≤ D F + h) ∧
    (realMatrix S).rank ≤ 2 ^ h * (realMatrix F).rank ∧
    (∀ d : ℕ, 3 ≤ d → D F = d →
      RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ) →
      (∀ colour : V → Fin 3, γ * Fintype.card E ≤
        ((Finset.univ.filter (fun e => colour (edge e false) =
          colour (edge e true))).card : ℝ)) →
      D S = d + h + 1 ∧
      RestrictionProfile S
        (((FiniteLaw.uniformFin w (by rw [hw]; positivity)).prod
          (matrixRowLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw).iid Q)
        ((FiniteLaw.uniformFin Q (by rw [hQ]; positivity)).prod
          ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
            (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w))
        (rho L) ((d + h + 1 : ℕ) : ℤ)) := by
  have hu := SourceAmplifierUpperRank.source_successor_upper_rank27 F L order edge
    rep hrep hq hE hincident ξ₀ w r Q q hw hQ
  dsimp only at hu ⊢
  refine ⟨hu.1, hu.2.1, hu.2.2, ?_⟩
  intro d hd hD hp gap
  let C := d + exponent L + outerExponent L + exponent L + 1
  have hC : 4 ≤ C := by dsimp [C]; omega
  have hCeq : C - 1 = d + exponent L + outerExponent L + exponent L := by
    simp only [C, Nat.add_sub_cancel_right]
  exact SourceAmplifierLower.source_successor_no_cost_profile27
    μ ν F L d hd hD hp hinner houter hwide href order edge loopless
    rep Δ hΔ hq hdegree γ hγ hE gap hscale hcountSource ξ₀
    w r Q q C hw hw2 hQ hC hCeq ηq hηq hquarter hsmall hfirst hlast
    hKcheck hxsmall hstar hsmallwx hmargin hL hbridge

#print axioms source_successor_full_scope27

end Paper2.SourceAmplifierFullScope
