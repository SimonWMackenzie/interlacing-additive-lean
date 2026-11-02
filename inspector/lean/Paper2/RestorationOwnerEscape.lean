import Paper2.SourceNearFull
import Paper2.RestorationSourceMassBalance
import Paper2.ReferenceProjectionMass

/-!
# A source copy cannot stay almost entirely at its short owner

Frozen v12 Section 5, lines 450--461. The source near-full theorem is
applied to the original rows of one copy and the actual singleton image
of the retained tuple columns. The short protocol is restricted through
original surviving completions. No outgoing-mass conclusion is assumed.
-/

namespace Paper2.RestorationOwnerEscape

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
open SourceSurvivingCollisions
open ReferenceCertificateTree

/-- Protected mass originally retained but routed to a different physical
destination, in units of one complete source copy. -/
noncomputable def protectedOutgoing {B I W Y : Type*} [Fintype W] [Fintype Y]
    {q₁ q₂ t w : ℕ} [NeZero q₂]
    (μ : FiniteLaw W)
    (input : I → W → (Fin w × TaggedColumn q₁ q₂ t Y))
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (st : State (Fin w × TaggedColumn q₁ q₂ t Y) B I W)
    (ν : PositiveRationalLaw Y)
    (v : (run μ input floor d fuel st).Leaves) (i : Fin w) : ℝ :=
  (1 / 256 : ℝ) * (SourceLaws.fixedTailLaw ν q₁ q₂ t).toFiniteLaw.prob
    (fun Z => (i, .fixedTail Z) ∈ st.rows ∧
      ReferenceCertificateProtocol.destination μ input floor d fuel st (i, .fixedTail Z) ≠ v) +
  (1 / 256 : ℝ) * (SourceLaws.outerLaw ν q₁ q₂ t).toFiniteLaw.prob
    (fun Z => (i, .diagonal Z) ∈ st.rows ∧
      ReferenceCertificateProtocol.destination μ input floor d fuel st (i, .diagonal Z) ≠ v)

/-- The proved mixture identity converts the near-full violation into
actual outgoing mass. The source wrapper below supplies that violation. -/
theorem escape_of_owner_rows_lt {B I W Y : Type*} [Fintype W] [Fintype Y]
    {q₁ q₂ t w : ℕ} [NeZero q₂]
    (μ : FiniteLaw W)
    (input : I → W → (Fin w × TaggedColumn q₁ q₂ t Y))
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (st : State (Fin w × TaggedColumn q₁ q₂ t Y) B I W)
    (ν : PositiveRationalLaw Y)
    (v : (run μ input floor d fuel st).Leaves) (i : Fin w) (η : ℝ)
    (hrow : (SourceLaws.taggedLaw ν q₁ q₂ t).toFiniteLaw.prob
      (fun Z => (i, Z) ∈ ((run μ input floor d fuel st).state v).rows) < 1 - η) :
    η < (127 / 128 : ℝ) * (1 - (SourceLaws.rawLaw ν q₁ q₂ t).toFiniteLaw.prob
      (fun Z => (i, .unrestricted Z) ∈ ((run μ input floor d fuel st).state v).rows)) +
      RestorationSourceMassBalance.protectedDeleted ν st.rows i +
      protectedOutgoing μ input floor d fuel st ν v i := by
  have hid := RestorationSourceMassBalance.owner_missing_identity
    μ input floor d fuel st ν v i
  unfold protectedOutgoing
  linarith

/-- Projecting one coordinate of an actual retained interlace rectangle
gives a protocol for the retained source copy with no extra communication. -/
theorem copy_restriction_le_cost {A K : Type*} [Fintype A] [Fintype K]
    {w : ℕ} (F : A → K → Bool) (R : Set (Fin w × A))
    (O : Set (Fin w → K)) (P : Protocol (Fin w × A) (Fin w → K) Bool)
    (hP : ∀ a ∈ R, ∀ y ∈ O, P.eval a y = fullInterlace F w a y)
    (i : Fin w) :
    Compression.restrictionD F {a | (i, a) ∈ R} ((fun y => y i) '' O) ≤
      P.cost := by
  classical
  have hmap := SourceProjection.restrictionD_projected_le
    (fullInterlace F w) F (fun a => (i, a)) (fun y => y i)
    R O {a | (i, a) ∈ R} (by intro a ha; exact ha)
    (by intro a _ y _; rfl)
  let Q := Workspace.UpperBound.Protocol.comap
    (fun a : R => a.val) (fun y : O => y.val) P
  have hQ : Q.Computes (fun (a : R) (y : O) => fullInterlace F w a.val y.val) := by
    intro a y
    simpa [Q, Workspace.UpperBound.Protocol.comap_eval] using
      hP a.val a.property y.val y.property
  have hc : Compression.restrictionD (fullInterlace F w) R O ≤ Q.cost :=
    Nat.sInf_le ⟨Q, rfl, hQ⟩
  have hcost : Q.cost = P.cost := by
    simp [Q, Workspace.UpperBound.Protocol.comap_cost]
  exact hmap.trans (hcost ▸ hc)

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y]

section Source

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
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcount : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (ξ₀ : Tail (width L) Y)

include hd hD hp hinner houter hwide href loopless hΔ hdegree hγ hE gap hscale hcount

set_option maxRecDepth 4096 in
/-- The first inequality in the mass-balance paragraph: at a short owner,
the actual retained mass of its own source copy is strictly below `1-eta`.
The required near-full source lower bound is derived, not supplied. -/
theorem source_owner_rows_lt (w : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    (P : Protocol (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y)
      (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
        (SourceConstruction.Items (width L) V)) Bool)
    (hP : ∀ a ∈ R, ∀ y ∈ O, P.eval a y =
      fullInterlace (SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀) w a y)
    (i : Fin w)
    (hsingle : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
          (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw) (· ∈ O) {i})
    (hcost : P.cost ≤ d + exponent L + outerExponent L + exponent L) :
    (matrixRowLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
      (fun Z => (i, Z) ∈ R) <
        1 - deletionAllowance (V := V) (E := E) γ Δ (width L) := by
  classical
  by_contra hn
  have hcol := ReferenceProjectionMass.singleton_image_mass_ge
    (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L) (width L)
      (SourceProfiles.width_ge_four L)).toFiniteLaw O i _ hsingle
  have hlo := SourceNearFull.restriction_lower (V := V) (E := E) μ ν F L d hd hD hp
    hinner houter hwide href order edge loopless rep Δ hΔ hq hdegree
    γ hγ hE gap hscale hcount ξ₀ ((fun y => y i) '' O)
    {Z | (i, Z) ∈ R} (by convert hcol using 1) (le_of_not_gt hn)
  have hup : Compression.restrictionD
      (SourceConstruction.matrix (q₁ := width L - 2) order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀)
      {Z | (i, Z) ∈ R} ((fun y => y i) '' O) ≤ P.cost := by
    apply copy_restriction_le_cost
    exact hP
  omega

set_option maxRecDepth 4096 in
/-- At any depth-`r` destination of the actual source protocol, a good
singleton column projection forces the displayed protected escape
inequality. Correctness and the remaining budget are derived on that
physical run; no node-level source bound is supplied. -/
theorem source_final_escape (w r : ℕ)
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    (st : State (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y)
      (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
        (SourceConstruction.Items (width L) V))
      (Fin w) (RawColumn (width L - 2) (outerWidth L) (width L) Y))
    (floor : ℕ → ℝ)
    (hP : ∀ a ∈ st.rows, ∀ y ∈ O, st.protocol.eval a y =
      fullInterlace (SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀) w a y)
    (hcost : st.protocol.cost ≤ d + exponent L + outerExponent L + exponent L + r)
    (v : (run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (fun i Z => (i, .unrestricted Z)) floor 0 r st).Leaves)
    (hv : ((run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (fun i Z => (i, .unrestricted Z)) floor 0 r st).route v).length = r)
    (i : Fin w)
    (hsingle : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
          (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw) (· ∈ O) {i}) :
    let μraw := (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
    let input := fun (i : Fin w) (Z : RawColumn (width L - 2) (outerWidth L) (width L) Y) =>
      (i, TaggedColumn.unrestricted Z)
    let T := run μraw input floor 0 r st
    deletionAllowance (V := V) (E := E) γ Δ (width L) <
      (127 / 128 : ℝ) * (1 - μraw.prob (fun Z => input i Z ∈ (T.state v).rows)) +
      RestorationSourceMassBalance.protectedDeleted ν st.rows i +
      protectedOutgoing μraw input floor 0 r st ν v i := by
  classical
  let μraw := (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
  let input := fun (i : Fin w) (Z : RawColumn (width L - 2) (outerWidth L) (width L) Y) =>
    (i, TaggedColumn.unrestricted Z)
  let T := run μraw input floor 0 r st
  have hnode := ReferenceRunCorrectness.computes_on_original_rectangle
    μraw input floor 0 r st
    (fullInterlace (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀) w) O hP v
  have hremaining := ReferenceRunCorrectness.remaining_cost μraw input floor r
    (d + exponent L + outerExponent L + exponent L) st hcost v
  have hnodecost : (T.state v).protocol.cost ≤ d + exponent L + outerExponent L + exponent L := by
    rw [hv] at hremaining
    simpa using hremaining
  have hrow := source_owner_rows_lt μ ν F L d hd hD hp hinner houter hwide href
    order edge loopless rep Δ hΔ hq hdegree γ hγ hE gap hscale hcount ξ₀
    w (T.state v).rows O (T.state v).protocol hnode i hsingle hnodecost
  exact escape_of_owner_rows_lt μraw input floor 0 r st ν v i
    (deletionAllowance (V := V) (E := E) γ Δ (width L)) hrow

end Source

end Paper2.RestorationOwnerEscape

#print axioms Paper2.RestorationOwnerEscape.copy_restriction_le_cost
#print axioms Paper2.RestorationOwnerEscape.escape_of_owner_rows_lt
#print axioms Paper2.RestorationOwnerEscape.source_owner_rows_lt
#print axioms Paper2.RestorationOwnerEscape.source_final_escape
