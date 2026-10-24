import CurrentAdditive.QuarticOutgoingMass
import Paper2.RestorationMassComposition

namespace Paper2.RestorationMassComposition

open SourceMatrix SourceLawBinding SourceProfileParameters SourceDeficiency
open SourceSurvivingCollisions ReferenceCertificateTree
open ReferencePublicDestinations Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open scoped BigOperators

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
/-- Conditional full mass comparison on a graph source. The only remaining
mathematical input is the exact T21 receipt inequality at nonowner nodes of
each fixed original run; all other mass bounds are derived on one run. -/
theorem no_short_protocol_of_actual_exceptional_receipts27
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
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      CurrentAdditive.QuarticSchedule.E27 Q ηq ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 16)
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
    (hexceptional : ∀ E0 : Finset (Fin w), ∀ row0 : R0, ∀ col0 : Y',
      let st := actualPaddedState R0 Y' row0 col0 P E0 r
      let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
        (width L)).toFiniteLaw ReferenceSourceInitial.input
        (ReferenceSchedule.floor w (x L)) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      let O := ReferenceOwners.ownerNodes fam final
      (∀ j : Fin (RestorationCoverParameters.tExponent Q - 2),
        ∀ S : Finset (Fin w),
          S.card = RestorationCovers.smallSize j.val → Disjoint S E0 →
          (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
            (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
              (outerWidth L) (width L)
              (SourceProfiles.width_ge_four L)).toFiniteLaw) (· ∈ Y') S) →
      ∀ v : T.Leaves, v ∉ O →
      (∑ u : O, ForeignOwnerMass.protectedMass ν L w
        (ReferenceOwners.origin fam final u) (T.state v).rows) ≤
        (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
          (r + 2) * width L) *
          (2 ^ (r - (T.route v).length) : ℕ)) : False := by
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
  have hwpos : 0 < w := by omega
  have hCgraph : P.Computes (fun row col =>
      fullInterlace (N F activity ξ₀) w row.val col.val) := by
    simpa only [SourceConstruction.matrix, activity] using hP
  obtain ⟨E0, row0, col0, _, hsingle, hpair, _, hdyadic, _, hcapacity, _, hlower⟩ :=
    RestorationOutgoingMass.actual_owner_outgoing_lower27 μ ν F L d hd hD hp
      hinner houter hwide href order edge loopless rep Δ hΔ hq hdegree
      γ hγ hE gap hscale hcountSource ξ₀ w r Q C hw hw2 hQ hC hCeq
      ηq hηq hquarter htstar hsmall R0 Y' P hP hPcost hR0 hY hmargin
  have hforeign := ForeignOwnerTotalMass.actual_foreign_owner_total μ ν F L d
    hd hp hinner houter hwide href activity ξ₀ w r C hw hCeq δ ζ η
    (by rfl) hη.le R0 Y' P hCgraph hPcost hR0 hsmall hfirst hlast
    E0 row0 col0 hsingle hpair
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
    (width L)).toFiniteLaw ReferenceSourceInitial.input
    (ReferenceSchedule.floor w (x L)) 0 r st
  let fam := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  let O := ReferenceOwners.ownerNodes fam final
  let K : ℝ := 1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
    (r + 2) * width L
  have hKnonneg : 0 ≤ K := by
    have hb : (0 : ℝ) ≤ RestorationCoverParameters.B2 Q := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ (r : ℝ) + 2 :=
      add_nonneg (Nat.cast_nonneg r) (by norm_num)
    have hs : (0 : ℝ) ≤ width L := Nat.cast_nonneg _
    dsimp only [K]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hb) hr) hs
  have hpoint (v : T.Leaves) (hv : v ∉ O) :
      (∑ u : O, ForeignOwnerMass.protectedMass ν L w
        (ReferenceOwners.origin fam final u) (T.state v).rows) ≤
      K * (2 ^ (r - (T.route v).length) : ℕ) := by
    exact hexceptional E0 row0 col0 hdyadic v hv
  have hcapNat : (∑ v ∈ Finset.univ \ O,
      2 ^ (r - (T.route v).length)) =
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) := by
    unfold ReferenceOwners.exceptionalCapacity
    change (∑ v ∈ Finset.univ \ O,
      2 ^ (r - (T.route v).length)) =
      ∑ v : T.Leaves, if v ∈ O then 0 else 2 ^ (r - (T.route v).length)
    simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.filter_notMem_eq_sdiff]
  have hraw : (∑ u : O, ∑ v ∈ Finset.univ \ O,
        ForeignOwnerMass.protectedMass ν L w
          (ReferenceOwners.origin fam final u) (T.state v).rows) ≤
      K * (ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) : ℕ) := by
    calc
      _ = ∑ v ∈ Finset.univ \ O, ∑ u : O,
          ForeignOwnerMass.protectedMass ν L w
            (ReferenceOwners.origin fam final u) (T.state v).rows := by
              rw [Finset.sum_comm]
      _ ≤ ∑ v ∈ Finset.univ \ O,
          K * (2 ^ (r - (T.route v).length) : ℕ) := by
            apply Finset.sum_le_sum
            intro v hv
            exact hpoint v (by simpa using hv)
      _ = K * ∑ v ∈ Finset.univ \ O,
          (2 ^ (r - (T.route v).length) : ℕ) := by
            simp only [Nat.cast_sum, Finset.mul_sum]
      _ = K * (ReferenceOwners.exceptionalCapacity fam final
          (fun v => 2 ^ (r - (T.route v).length)) : ℕ) := by
            exact congrArg (fun n : ℕ => K * (n : ℝ)) hcapNat
  have hEreceipt :
      let st := actualPaddedState R0 Y' row0 col0 P E0 r
      let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
        (width L)).toFiniteLaw ReferenceSourceInitial.input
        (ReferenceSchedule.floor w (x L)) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      let O := ReferenceOwners.ownerNodes fam final
      (∑ u : O, ∑ v ∈ Finset.univ \ O,
        ForeignOwnerMass.protectedMass ν L w
          (ReferenceOwners.origin fam final u) (T.state v).rows) ≤ η * w / 16 := by
    have hcapR :
        (ReferenceOwners.exceptionalCapacity fam final
          (fun v => 2 ^ (r - (T.route v).length)) : ℝ) ≤
        (CurrentAdditive.QuarticSchedule.E27 Q ηq : ℝ) := by
      exact_mod_cast hcapacity
    have hm := mul_le_mul_of_nonneg_left hcapR hKnonneg
    have hk : K * (CurrentAdditive.QuarticSchedule.E27 Q ηq : ℕ) ≤ η * w / 16 := by
      simpa only [K, η] using hKcheck
    exact hraw.trans (hm.trans hk)
  exact actual_run_mass_contradiction ν L w r η hη hwpos R0 Y' P
    E0 row0 col0 hlower hforeign hEreceipt


end Paper2.RestorationMassComposition
#print axioms Paper2.RestorationMassComposition.no_short_protocol_of_actual_exceptional_receipts27
