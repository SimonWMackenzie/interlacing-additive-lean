import Paper2.SourceSurvivingCollisionsScheduled
import Paper2.SourceBranchContradiction

/-!
# The source lower bound after small deletions

Frozen v12 Section 4, `src:near-full`. The selected branch, its retained
supports, stopping tree and final contradiction all belong to the same
original protocol and the same promise-independent source table. The
public numerical checks remain explicit; their eventual parameter compiler
and the later restoration argument are separate obligations.
-/

namespace Paper2.SourceNearFull

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
open SourceProtocolPrefix SourceProtocolPrefixTree SourceSurvivingCollisions

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y]

section Scheduled

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
    (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcount : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (ξ₀ : Tail (width L) Y)

include hd hD hp hinner houter hwide href loopless hΔ hdegree hγ hE gap hscale hcount

set_option maxRecDepth 4096 in
/-- No short protocol exists for any of the stated retained source inputs.
Neither a selected branch nor an attached-witness lower bound is a premise. -/
theorem short_protocol_impossible
    (W : Set (RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    (U : Set (TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (hW : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
      (matrixColumnLaw μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw.prob (· ∈ W))
    (hU : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
      (matrixRowLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob (· ∈ U))
    (P : Protocol U W Bool)
    (hP : P.Computes (fun z w => SourceConstruction.matrix order edge
      (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀ z.val w.val))
    (hcost : P.cost ≤ d + exponent L + outerExponent L + exponent L) : False := by
  classical
  let Praw := Workspace.UpperBound.Protocol.transpose P
  let act := SourceConstruction.activity order edge
    (show 3 ≤ width L by have := SourceProfiles.width_ge_four L; omega) r hq
  obtain ⟨_, _, _, dom, b, hA, hKB, _, hBP, hBcost, _⟩ :=
    scheduled_usable_branch μ ν F L d hd hD hp hinner houter hwide href
      order edge loopless r Δ hΔ hq hdegree γ hγ hE gap hscale hcount ξ₀
      W U hW hU P hP hcost
  have hprofile := (SourceProfiles.source_profiles μ ν F L d hd hD hp
    hinner houter hwide href act ξ₀).2.1
  have hfloor : SourceSupportSchedule.floor (outerWidth L) (x L) 0 ≤ 1 / 8 := by
    rw [SourceSupportSchedule.floor_zero]
    linarith
  exact SourceBranchContradiction.branch_contradiction μ ν F ξ₀ d (outerExponent L)
    (rho L) (x L) (by omega) (by have := exponent_ge L; omega) (rho_pos L) (x_pos L)
    (SourceProfiles.width_ge_four L)
    (by change width L - 2 + 3 = width L + 1
        have := SourceProfiles.width_ge_four L
        omega) rfl hscale hfloor hp hprofile
    order edge r hq W U Praw dom b hA hKB hBP hBcost

set_option maxRecDepth 4096 in
/-- Every original restriction retaining the stated protected masses has
the full source lower bound. This is the restriction part of `src:near-full`. -/
theorem restriction_lower
    (W : Set (RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    (U : Set (TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (hW : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
      (matrixColumnLaw μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw.prob (· ∈ W))
    (hU : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
      (matrixRowLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob (· ∈ U)) :
    d + exponent L + outerExponent L + exponent L + 1 ≤
      Compression.restrictionD (SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀) U W := by
  classical
  by_contra hn
  obtain ⟨P, hcost, hP⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty (fun (z : U) (w : W) =>
      SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀ z.val w.val))
  apply short_protocol_impossible μ ν F L d hd hD hp hinner houter hwide href
    order edge loopless r Δ hΔ hq hdegree γ hγ hE gap hscale hcount ξ₀
    W U hW hU P hP
  change P.cost = Compression.restrictionD (SourceConstruction.matrix order edge
    (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀) U W at hcost
  omega

set_option maxRecDepth 4096 in
/-- The same graph-constructed table has exactly the advertised NO cost.
The universal upper bound is the existing explicit source protocol. -/
theorem full_exact :
    D (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀) =
      d + exponent L + outerExponent L + exponent L + 1 := by
  classical
  have hη : 0 < deletionAllowance (V := V) (E := E) γ Δ (width L) :=
    SourceDeletionParameters.eta_pos (width L) (NeZero.pos _) _ _
      (vertexTolerance_pos (V := V) (E := E) γ Δ hγ hΔ hE)
      (by unfold witnessDensity; positivity)
  have hlo := restriction_lower μ ν F L d hd hD hp hinner houter hwide href
    order edge loopless r Δ hΔ hq hdegree γ hγ hE gap hscale hcount ξ₀
    Set.univ Set.univ (by simp only [Set.mem_univ, FiniteLaw.prob_true]; linarith)
    (by simp only [Set.mem_univ, FiniteLaw.prob_true]; linarith)
  have hrestrict := PartialProtocol.D_reindex_le
    (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀)
    (fun z : (Set.univ : Set (TaggedColumn (width L - 2) (outerWidth L) (width L) Y)) => z.val)
    (fun w : (Set.univ : Set (RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V))) => w.val)
  have hup := (SourceConstruction.matrix_upper_budgets (q₁ := width L - 2) order edge
    (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀
    (exponent L) (outerExponent L)
    (by have := SourceProfiles.width_ge_four L; omega) rfl rfl).1
  rw [hD] at hup
  dsimp only [Compression.restrictionD, D] at hlo hrestrict hup ⊢
  exact Nat.le_antisymm hup (hlo.trans hrestrict)

end Scheduled

end Paper2.SourceNearFull

#print axioms Paper2.SourceNearFull.short_protocol_impossible
#print axioms Paper2.SourceNearFull.restriction_lower
#print axioms Paper2.SourceNearFull.full_exact
