import Paper2.ProtectedIncomingRun
import Paper2.RestorationMassComposition

/-!
# No short protocol on the actual graph-source interlace

This discharges the conditional incoming-receipt premise on the same physical
run. Public finite parameter guards remain explicit; none is a mass conclusion.
-/

namespace Paper2.RestorationNoShortProtocol

open SourceMatrix SourceLawBinding SourceProfileParameters
open Paper2.ReferencePublicDestinations
open ReferenceCertificateTree Workspace.Types.Protocol
open Workspace.Types.CommComplexity SourceDeficiency SourceSurvivingCollisions
open scoped BigOperators

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
/-- An actual retained graph-source rectangle has no protocol of cost
at most `C+r-1`. All outgoing, foreign and exceptional receipt bounds are
proved on one common run, not supplied as certificate premises. -/
theorem no_short_protocol
    {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
    [Fintype X] [Fintype Y]
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
    (hquarter : 4 * ReferenceOwners.exceptionBudget
      (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := V) (E := E) γ Δ (width L))) ≤ w)
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
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := V) (E := E) γ Δ (width L))) ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 16)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := V)
      (width L - 2) (outerWidth L) (width L) w))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀)
        w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (hR0 : 1 - deletionAllowance (V := V) (E := E) γ Δ (width L) / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : RestorationCoverParameters.theta Q ≤
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w).prob (· ∈ Y'))
    (hmargin : 2 * w * x L +
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1)
    : False := by
  classical
  apply RestorationMassComposition.no_short_protocol_of_actual_exceptional_receipts
    μ ν F L d hd hD hp hinner houter hwide href order edge loopless rep Δ hΔ
    hq hdegree γ hγ hE gap hscale hcountSource ξ₀ w r Q C hw hw2 hQ hC hCeq
    hquarter hsmall hfirst hlast hKcheck R0 Y' P hP hPcost hR0 hY hmargin
  intro E0 row0 col0
  dsimp only
  intro _ v _
  let activity := SourceConstruction.activity order edge
    (by have := SourceProfiles.width_ge_four L; omega) rep hq
  let rawμ := (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
    (width L)).toFiniteLaw
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let T := run rawμ ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
  let fam := fun z : T.Leaves => (T.state z).family
  let final := fun z : T.Leaves => (T.route z).length = r
  let O := ReferenceOwners.ownerNodes fam final
  let origin : O → Fin w := ReferenceOwners.origin fam final
  have hinj : Function.Injective origin :=
    ReferenceOwners.run_origin_injective rawμ ReferenceSourceInitial.input
      (ReferenceSchedule.floor w (x L)) r st
  let I : Finset (Fin w) := Finset.univ.image origin
  have hPgraph : P.Computes (fun row col =>
      fullInterlace (N F activity ξ₀) w row.val col.val) := by
    simpa only [SourceConstruction.matrix, activity] using hP
  have hbound := ProtectedIncomingRun.physical_incoming_mass_lt
    μ ν F L d hd hD hp hinner houter hwide href activity ξ₀
    w r Q C hw hQ (by omega) hCeq R0 Y' row0 col0 P hPgraph hPcost E0 hY
    hxsmall I v
  have hreindex : (∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i
      (T.state v).rows) = ∑ u : O, ForeignOwnerMass.protectedMass ν L w
        (origin u) (T.state v).rows := by
    exact Finset.sum_image (fun a _ b _ h => hinj h)
  rw [hreindex] at hbound
  exact hbound.le

end Paper2.RestorationNoShortProtocol

#print axioms Paper2.RestorationNoShortProtocol.no_short_protocol
