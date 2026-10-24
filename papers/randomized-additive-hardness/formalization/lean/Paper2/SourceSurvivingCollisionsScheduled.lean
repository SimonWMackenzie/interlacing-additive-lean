import Paper2.SourceProtocolPrefixScheduled
import Paper2.SourceSurvivingCollisionsBranches

/-!
# Surviving collisions in a branch of the original source protocol

Frozen v12 Section 4, `src:near-full`, the common-assignment and
surviving-collisions paragraphs. The prefix labels, dominant template bin,
and residual protocol are derived from the original short protocol. They
are not supplied as independent branch data. The remaining support
recursion and final capacity contradiction are not proved in this file.
-/

namespace Paper2.SourceSurvivingCollisions

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
open SourceProtocolPrefix SourceProtocolPrefixTree

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y]

/-- A surviving assigned coordinate keeps its actual collision and both
sorts of usable-coordinate mass. -/
theorem usable_witness_floors {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (U : Set (TaggedColumn q₁ q₂ s Y))
    (code : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (dom : Fin s → Fin s) (b : Fin s) (xcap : ℝ)
    (α : Fin q₂)
    (hα : α ∈ assignedCoordinates edge r hq μ W code b \
      branchDeficient μ ν (branchTemplates W code dom b) U xcap) :
    collisionAt edge r hq μ W code b α ∧
    (∀ j : Fin q₁, xcap ≤ μ.toFiniteLaw.prob
      (fun u => SourceDeficiencyTemplate.projectedAt (branchTemplates W code dom b) α (j, u))) ∧
    3 / 4 ≤ (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
      (fun word => TaggedColumn.diagonal (α, word) ∈ U) := by
  classical
  obtain ⟨hαK, hαB⟩ := Finset.mem_sdiff.mp hα
  exact ⟨assignedCoordinates_collision edge r hq μ W code b α hαK,
    usable_coordinate_masses μ ν (branchTemplates W code dom b) U xcap α hαB⟩

set_option maxRecDepth 3072 in
/-- A branch of the same original protocol contains a strict excess of
actual usable collision coordinates. Its protocol keeps every retained
column, computes the same source table, and has the exact remaining depth
budget. Only the base profile, graph gap, public scalar checks and original
retained-input/protocol hypotheses are inputs. -/
theorem scheduled_usable_branch
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
    (hcost : P.cost ≤ d + exponent L + outerExponent L + exponent L) :
    let Praw := Workspace.UpperBound.Protocol.transpose P
    let code := rowCode W Praw (exponent L)
    CompleteAlicePrefix (exponent L) Praw ∧
    EveryPrefixBranchActive (@Finset.univ W (Fintype.ofFinite W)) (exponent L) Praw ∧
    (∀ w : W, ∀ z : U,
      code w.val = NPCC.Protocol.actualPrefixCodeRaw (exponent L) Praw w z) ∧
    ∃ dom : Fin (width L) ≃ Fin (width L), ∃ b : Fin (width L),
      let A := branchTemplates W code dom b
      let B := branchDeficient μ ν A U (2 * (width L : ℝ) * rho L)
      let K := assignedCoordinates edge r hq μ W code b
      (998 / 1000 : ℝ) <
        (SourceLaws.templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prob A ∧
      4 * B.card < K.card ∧
      3 * B.card < (K \ B).card ∧
      (branchProtocol W Praw (exponent L) b).Computes (fun w z =>
        SourceConstruction.matrix order edge
          (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀ z.val w.val) ∧
      (branchProtocol W Praw (exponent L) b).cost ≤ d + exponent L + outerExponent L ∧
      ∀ α ∈ K \ B,
        collisionAt edge r hq μ W code b α ∧
        (∀ j : Fin (width L - 2), 2 * (width L : ℝ) * rho L ≤ μ.toFiniteLaw.prob
          (fun u => SourceDeficiencyTemplate.projectedAt A α (j, u))) ∧
        3 / 4 ≤ (ν.iid ((width L - 2) + width L + 1)).toFiniteLaw.prob
          (fun word => TaggedColumn.diagonal (α, word) ∈ U) := by
  have hs := SourceProfiles.width_ge_four L
  have hdelta := vertexTolerance_pos (V := V) (E := E) γ Δ hγ hΔ hE
  have hzeta : 0 < witnessDensity γ := by unfold witnessDensity; positivity
  obtain ⟨hpref, hactive, _, dom, hdom⟩ :=
    scheduled_common_assignment μ ν F L d hd hD hp hinner houter hwide href
      order edge r hq ξ₀ (vertexTolerance (V := V) (E := E) γ Δ)
      (witnessDensity γ) hdelta hzeta W U hW hU P hP hcost
  let Praw := Workspace.UpperBound.Protocol.transpose P
  let code := rowCode W Praw (exponent L)
  have hA (b : Fin (width L)) :
      (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prob
        (branchTemplates W code dom b) := (hdom b).1
  obtain ⟨b, hb, hsurv⟩ := select_usable_branch edge loopless hs r Δ hΔ hq hdegree
    γ hγ hE gap μ ν (rho L) hscale hcount U W code dom hA hU hW
  refine ⟨hpref, hactive, ?_, dom, b, hA b, hb, hsurv, ?_, ?_, ?_⟩
  · intro w z
    exact rowCode_eq_actualPrefix W Praw (exponent L) hpref w z
  · apply branchProtocol_computes
      (fun w z => SourceConstruction.matrix order edge (by omega) r hq F ξ₀ z.val w)
      W Praw (exponent L) b hpref
    intro w z
    rw [Workspace.UpperBound.Protocol.transpose_eval]
    exact hP z w
  · apply branchProtocol_cost W Praw (exponent L)
      (d + exponent L + outerExponent L) b hpref
    simpa only [Praw, Workspace.UpperBound.Protocol.transpose_cost] using hcost
  · exact usable_witness_floors (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L)
      edge r hq μ ν W U
      (rowCode W (Workspace.UpperBound.Protocol.transpose P) (exponent L)) dom b
      (2 * (width L : ℝ) * rho L)

end Paper2.SourceSurvivingCollisions

#print axioms Paper2.SourceSurvivingCollisions.scheduled_usable_branch
#print axioms Paper2.SourceSurvivingCollisions.usable_witness_floors
