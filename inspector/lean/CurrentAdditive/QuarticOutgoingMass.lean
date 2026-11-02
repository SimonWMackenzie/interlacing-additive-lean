import CurrentAdditive.QuarticActualItemsDestinations
import Paper2.RestorationOutgoingMass

namespace Paper2.RestorationOutgoingMass

open scoped BigOperators
open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
open SourceSurvivingCollisions ReferenceCertificateTree
open ReferencePublicDestinations ReferenceOwners

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
/-- The checked source endpoint, applied to the one public graph-source
destination witness and summed over the physical owners of that same run. -/
theorem actual_owner_outgoing_lower27
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
    (ηq : ℚ)
    (hηq : (ηq : ℝ) = deletionAllowance (V := V) (E := E) γ Δ (width L))
    (hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop w Q ηq)
    (htstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)))
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
        (16 * (127 / 128 : ℝ)) < 1) :
    ∃ E0 : Finset (Fin w), ∃ row0 : R0, ∃ col0 : Y',
      let κ := matrixColumnLaw (V := V) μ (width L - 2)
        (outerWidth L) (width L) (SourceProfiles.width_ge_four L)
      let st := actualPaddedState R0 Y' row0 col0 P E0 r
      let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
        (width L)).toFiniteLaw ReferenceSourceInitial.input
        (ReferenceSchedule.floor w (x L)) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      let owners := {v : T.Leaves // v ∈ ReferenceOwners.ownerNodes fam final}
      E0.card ≤ CurrentAdditive.QuarticSchedule.e027 Q ηq ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
        1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
          ProductProjections.projectionMass (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (99 / 100 : ℝ) ≤
          ProductProjections.projectionMass (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (18 / 25 : ℝ) ≤
          ProductProjections.projectionMass (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ j : Fin (RestorationCoverParameters.tExponent Q - 2),
        ∀ S : Finset (Fin w),
          S.card = RestorationCovers.smallSize j.val → Disjoint S E0 →
            (18 / 25 : ℝ) ≤
              ProductProjections.projectionMass (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      w - CurrentAdditive.QuarticSchedule.E27 Q ηq ≤
        (ReferenceOwners.ownerNodes fam final).card ∧
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) ≤
        CurrentAdditive.QuarticSchedule.E27 Q ηq ∧
      Function.Injective (ReferenceOwners.origin fam final) ∧
      deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 2 <
        ∑ v : owners,
          RestorationOwnerEscape.protectedOutgoing
            (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
              (width L)).toFiniteLaw ReferenceSourceInitial.input
            (ReferenceSchedule.floor w (x L)) 0 r st ν v.val
            (ReferenceOwners.origin fam final v) := by
  classical
  let η := deletionAllowance (V := V) (E := E) γ Δ (width L)
  let δ := vertexTolerance (V := V) (E := E) γ Δ
  let ζ := witnessDensity γ
  let activity := SourceConstruction.activity order edge
    (by have := SourceProfiles.width_ge_four L; omega) rep hq
  have hδ : 0 < δ := vertexTolerance_pos (V := V) (E := E) γ Δ hγ hΔ hE
  have hζ : 0 < ζ := by unfold ζ witnessDensity; positivity
  have hη : 0 < η := by
    change 0 < SourceDeletionParameters.eta (width L) δ ζ
    exact SourceDeletionParameters.eta_pos (width L)
      (by have := SourceProfiles.width_ge_four L; omega) δ ζ hδ hζ
  have hwpos : 0 < w := by rw [hw]; positivity
  have hCgraph : P.Computes (fun row col =>
      fullInterlace (N F activity ξ₀) w row.val col.val) := by
    simpa only [SourceConstruction.matrix, activity] using hP
  obtain ⟨E0, row0, col0, hE0, hsingle, hpair99, hpair18, hdyadic,
    howners, hcapacity, _, _, hinj, _⟩ :=
    ReferencePublicDestinations.actual_items_destinations27 μ ν F L d hd hD hp
      hinner houter hwide href activity ξ₀ w r Q C hw hQ hC hCeq δ ζ ηq
      hδ hζ (by rw [hηq]; rfl) hquarter htstar
      R0 Y' P hCgraph hPcost
      (by simpa only [hηq] using hR0) hY
      (by simpa only [hηq] using hmargin)
  have hsingleReal : ∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
      1 - deletionAllowance (V := V) (E := E) γ Δ (width L) ≤
        ProductProjections.projectionMass
          (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
            (outerWidth L) (width L)
            (SourceProfiles.width_ge_four L)).toFiniteLaw) (· ∈ Y') S := by
    simpa only [hηq] using hsingle
  refine ⟨E0, row0, col0, hE0, hsingleReal, hpair99, hpair18, hdyadic,
    howners, hcapacity, hinj, ?_⟩
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let μraw := (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
    (width L)).toFiniteLaw
  let T := run μraw ReferenceSourceInitial.input
    (ReferenceSchedule.floor w (x L)) 0 r st
  let fam := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  let Owners := {v : T.Leaves // v ∈ ReferenceOwners.ownerNodes fam final}
  have hcost : st.protocol.cost ≤
      d + exponent L + outerExponent L + exponent L + r := by
    have hc := actualPaddedState_cost R0 Y' row0 col0 P E0 r
    change st.protocol.cost ≤ max P.cost r at hc
    omega
  have hcompute : ∀ a ∈ st.rows, ∀ y ∈ Y', st.protocol.eval a y =
      fullInterlace (SourceConstruction.matrix order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq F ξ₀) w a y := by
    intro a ha y hy
    exact (actualPaddedState_eval R0 Y' row0 col0 P E0 r
      ⟨a, ha⟩ ⟨y, hy⟩).trans (hP ⟨a, ha⟩ ⟨y, hy⟩)
  have hlocal (v : Owners) : η <
      (127 / 128 : ℝ) * (1 - μraw.prob
        (fun Z => ReferenceSourceInitial.input
          (ReferenceOwners.origin fam final v) Z ∈ (T.state v.val).rows)) +
      RestorationSourceMassBalance.protectedDeleted ν st.rows
        (ReferenceOwners.origin fam final v) +
      RestorationOwnerEscape.protectedOutgoing μraw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L))
        0 r st ν v.val (ReferenceOwners.origin fam final v) := by
    have hv : (T.route v.val).length = r :=
      ((ReferenceOwners.mem_ownerNodes fam final v.val).mp v.property).1
    have hi := ReferenceOwners.run_origin_mem_initial μraw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r st v
    have hnot : ReferenceOwners.origin fam final v ∉ E0 :=
      (Finset.mem_sdiff.mp hi).2
    have hs := hsingleReal {ReferenceOwners.origin fam final v}
      (by simp) (by simp [hnot])
    have he := RestorationOwnerEscape.source_final_escape μ ν F L d hd hD hp
      hinner houter hwide href order edge loopless rep Δ hΔ hq hdegree
      γ hγ hE gap hscale hcountSource ξ₀ w r Y' st
      (ReferenceSchedule.floor w (x L)) hcompute hcost v.val hv
      (ReferenceOwners.origin fam final v) hs
    simpa [η, μraw, T] using he
  have hreference := ReferenceActualOwnerLoss.total_reference_loss
    (X := X) (V := V) (q₁ := width L - 2) (q₂ := outerWidth L)
    (s := width L) (w := w) ν r hw R0 Y' row0 col0 P E0 η (x L)
    (by unfold x; positivity) hR0 hsmall
  have hdeletedAll := RestorationSourceMassBalance.total_protected_deleted_le
    ν hwpos st.rows η (by simpa [st, actualPaddedState, actualOriginalState] using hR0)
  have hdeleted :
      (∑ v : Owners, RestorationSourceMassBalance.protectedDeleted ν st.rows
        (ReferenceOwners.origin fam final v)) ≤ η / 16 := by
    have hnonneg (i : Fin w) :
        0 ≤ RestorationSourceMassBalance.protectedDeleted ν st.rows i :=
      RestorationSourceMassBalance.protectedDeleted_nonneg ν st.rows i
    calc
      _ = ∑ i ∈ Finset.univ.image (ReferenceOwners.origin fam final),
          RestorationSourceMassBalance.protectedDeleted ν st.rows i := by
          rw [Finset.sum_image]
          intro a _ b _ he
          exact hinj he
      _ ≤ ∑ i : Fin w, RestorationSourceMassBalance.protectedDeleted ν st.rows i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => hnonneg i)
      _ ≤ η / 16 := hdeletedAll
  have hcount : w - CurrentAdditive.QuarticSchedule.E27 Q ηq ≤ Fintype.card Owners := by
    simpa only [Owners, Fintype.card_coe] using howners
  have hreference' : (∑ v : Owners, (1 - μraw.prob
      (fun Z => ReferenceSourceInitial.input
        (ReferenceOwners.origin fam final v) Z ∈ (T.state v.val).rows))) ≤
      η / (8 * (127 / 128 : ℝ)) := by
    simpa [Owners, st, T, fam, final, μraw] using hreference
  have hout := outgoing_lower_of_owner_bounds Finset.univ w
    (CurrentAdditive.QuarticSchedule.E27 Q ηq) η
    (fun v : Owners => RestorationOwnerEscape.protectedOutgoing μraw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L))
      0 r st ν v.val (ReferenceOwners.origin fam final v))
    (fun v : Owners => 1 - μraw.prob
      (fun Z => ReferenceSourceInitial.input
        (ReferenceOwners.origin fam final v) Z ∈ (T.state v.val).rows))
    (fun v : Owners => RestorationSourceMassBalance.protectedDeleted ν st.rows
      (ReferenceOwners.origin fam final v))
    hη hw2 hquarter hcount
    (by intro v _; exact hlocal v) (by simpa using hreference')
    (by simpa using hdeleted)
  simpa [η, st, T, fam, final, Owners, μraw] using hout


end Paper2.RestorationOutgoingMass
#print axioms Paper2.RestorationOutgoingMass.actual_owner_outgoing_lower27
