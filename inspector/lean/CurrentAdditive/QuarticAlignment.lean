import CurrentAdditive.QuarticNoShortProtocol
import Paper2.RestorationUpper

/-!
# Exact alignment on the actual graph-source full-product selector

This scratch assembly uses the literal transposed interlace `sourceW`.
The retained-rectangle lower bound comes from the same-source no-short
protocol theorem; the full upper bound comes from the universal source
protocol; the weaker profile is the proved reference-population profile.
-/

namespace Paper2.RestorationAlignment

open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
  SourceSurvivingCollisions
open Workspace.Types.CommComplexity Workspace.Types.Protocol

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y]
variable
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d) (hD : D F = d)
    (hp : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ))
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (ξ₀ : Tail (width L) Y)
    (w r Q C : ℕ) (hw : w = 2 ^ r) (hw2 : 2 ≤ w)
    (hQ : 0 < Q) (hC : 4 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
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

include hd hD hp hinner houter hwide href loopless hΔ hdegree hγ hE gap
  hscale hcountSource hw hw2 hQ hC hCeq hηq hquarter hsmall hfirst hlast
  hKcheck hxsmall hstar hmargin in
set_option maxRecDepth 4096 in
/-- Every original retained rectangle of the transposed graph-source
selector costs at least `C+r`; neither an incoming receipt nor a source
cost certificate is a premise. -/
theorem actual_W_restriction_lower27 :
    RestrictionLowerBound
      (RestorationUpper.sourceW F L order edge rep hq ξ₀ w)
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w)
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity))
      (RestorationCoverParameters.theta Q)
      (1 - deletionAllowance (V := V) (E := E) γ Δ (width L) / (16 * w))
      ((C + r : ℕ) : ℤ) := by
  classical
  intro Y' R0 hY hR0
  by_contra hn
  let M := RestorationUpper.sourceW F L order edge rep hq ξ₀ w
  obtain ⟨P, hPcost, hP⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty
      (fun (col : Y') (row : R0) => M col.val row.val))
  let Pt := Workspace.UpperBound.Protocol.transpose P
  have hPt : Pt.Computes (fun (row : R0) (col : Y') =>
      fullInterlace (SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀)
        w row.val col.val) := by
    intro row col
    rw [Workspace.UpperBound.Protocol.transpose_eval]
    exact hP col row
  have hPtCost : Pt.cost ≤ C + r - 1 := by
    have hc : P.cost = Compression.restrictionD M Y' R0 := hPcost
    rw [Workspace.UpperBound.Protocol.transpose_cost]
    change ¬ ((C + r : ℕ) : ℤ) ≤
      (Compression.restrictionD M Y' R0 : ℤ) at hn
    omega
  exact RestorationNoShortProtocol.no_short_protocol27
    μ ν F L d hd hD hp hinner houter hwide href order edge loopless
    rep Δ hΔ hq hdegree γ hγ hE gap hscale hcountSource ξ₀
    w r Q C hw hw2 hQ hC hCeq ηq hηq hquarter hstar
    hsmall hfirst hlast hKcheck hxsmall R0 Y' Pt hPt hPtCost hR0 hY hmargin

include hd hD hp hinner houter hwide href loopless hΔ hdegree hγ hE gap
  hscale hcountSource hw hw2 hQ hC hCeq hηq hquarter hsmall hfirst hlast
  hKcheck hxsmall hstar hsmallwx hmargin in
set_option maxRecDepth 4096 in
/-- Full frozen-v12 `res:alignment` for the literal graph-source `W`:
exact ambient cost, its one-bit-weaker three-rung profile, and the
near-full retained-rectangle lower bound. -/
theorem actual_W_alignment27 :
    D (RestorationUpper.sourceW F L order edge rep hq ξ₀ w) = C + r ∧
    RestrictionProfile
      (RestorationUpper.sourceW F L order edge rep hq ξ₀ w)
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w)
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity))
      (RestorationCoverParameters.theta Q) ((C + r - 1 : ℕ) : ℤ) ∧
    RestrictionLowerBound
      (RestorationUpper.sourceW F L order edge rep hq ξ₀ w)
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w)
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity))
      (RestorationCoverParameters.theta Q)
      (1 - deletionAllowance (V := V) (E := E) γ Δ (width L) / (16 * w))
      ((C + r : ℕ) : ℤ) := by
  classical
  have hlo := actual_W_restriction_lower27 μ ν F L d hd hD hp hinner
    houter hwide href order edge loopless rep Δ hΔ hq hdegree γ hγ hE
    gap hscale hcountSource ξ₀ w r Q C hw hw2 hQ hC hCeq ηq hηq hquarter
    hsmall hfirst hlast hKcheck hxsmall hstar hmargin
  have hupper := RestorationUpper.actual_sourceW_D_le F L d C r w hD
    (by omega) hCeq hw order edge rep hq ξ₀
  have hη : 0 ≤ deletionAllowance (V := V) (E := E) γ Δ (width L) := by
    exact (SourceDeletionParameters.eta_pos (width L) (NeZero.pos _) _ _
      (vertexTolerance_pos (V := V) (E := E) γ Δ hγ hΔ hE)
      (by unfold witnessDensity; positivity)).le
  have hfull := hlo Set.univ Set.univ
    (by simpa only [Set.mem_univ, FiniteLaw.prob_true] using
      RestorationCoverParameters.theta_le_one hQ)
    (by
      simp only [Set.mem_univ, FiniteLaw.prob_true]
      have hwpos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
      have hden : 0 ≤ deletionAllowance (V := V) (E := E) γ Δ (width L) /
          (16 * (w : ℝ)) :=
        div_nonneg hη (le_of_lt (mul_pos (by norm_num) hwpos))
      linarith)
  have huniv : Compression.restrictionD
      (RestorationUpper.sourceW F L order edge rep hq ξ₀ w)
      Set.univ Set.univ =
      D (RestorationUpper.sourceW F L order edge rep hq ξ₀ w) := by
    have hh := pullback_D_eq_of_surjective
      (RestorationUpper.sourceW F L order edge rep hq ξ₀ w)
      (fun (col : (Set.univ : Set (Fin w → RawRow (width L - 2)
        (outerWidth L) (width L) X (SourceConstruction.Items (width L) V)))) => col.val)
      (fun (row : (Set.univ : Set (Fin w × TaggedColumn (width L - 2)
        (outerWidth L) (width L) Y))) => row.val)
      (fun col => ⟨⟨col, Set.mem_univ col⟩, rfl⟩)
      (fun row => ⟨⟨row, Set.mem_univ row⟩, rfl⟩)
    simpa only [Compression.restrictionD, D] using hh
  have hlowcost : C + r ≤
      D (RestorationUpper.sourceW F L order edge rep hq ξ₀ w) := by
    rw [huniv] at hfull
    exact_mod_cast hfull
  have hCexact : C = d + exponent L + outerExponent L + exponent L + 1 := by
    omega
  let activity := SourceConstruction.activity order edge
    (by have := SourceProfiles.width_ge_four L; omega) rep hq
  have hprofile := RestorationReferenceProfileSource.source_reference_profile
    μ ν F L d w r Q C hd hD hp hinner houter hwide href activity ξ₀
    hw hQ hsmallwx hstar hCexact
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hprofile
  refine ⟨Nat.le_antisymm hupper hlowcost, ?_, hlo⟩
  simpa only [RestorationUpper.sourceW, SourceConstruction.matrix, activity]
    using hprofile

end Paper2.RestorationAlignment

#print axioms Paper2.RestorationAlignment.actual_W_restriction_lower27
#print axioms Paper2.RestorationAlignment.actual_W_alignment27
