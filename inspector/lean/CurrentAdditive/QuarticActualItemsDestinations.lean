import CurrentAdditive.QuarticRestorationRun
import Paper2.ReferencePublicDestinations

namespace Paper2.ReferencePublicDestinations

open SourceMatrix SourceLawBinding SourceProfileParameters SourceProfilesSchedule
open Workspace.Types.Protocol
open ReferenceCertificateTree ReferenceCertificates Paper2.SourceSupportFrontier

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩
local instance (L : ℕ) : Nonempty (Fin (4 * width L)) :=
  ⟨⟨0, by have h := SourceProfiles.width_ge_four L; omega⟩⟩
local instance (L : ℕ) : Nonempty (Fin (width L - 3)) := ⟨⟨0, by
  have h := SourceProfiles.width_ge_four L
  omega⟩⟩

private theorem positive_event_nonempty27 {T : Type*} [Fintype T]
    (κ : FiniteLaw T) (E : Set T) (h : 0 < κ.prob (· ∈ E)) : E.Nonempty := by
  by_contra hn
  have he : (fun t : T => t ∈ E) = fun _ => False := by
    funext t
    apply propext
    exact ⟨fun ht => (hn ⟨t, ht⟩).elim, False.elim⟩
  rw [he, FiniteLaw.prob_false] at h
  exact (not_lt_of_ge le_rfl) h

set_option maxRecDepth 4096 in
/-- Actual-Items destination package. In contrast to the reassociated
intermediate above, every leaf here is a physical leaf of the original
`Items`-column protocol. The same public exceptional set is used for the
padded count and the unpadded original-leaf exclusion. -/
theorem actual_items_destinations27
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : Workspace.Types.CommComplexity.D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r Q C : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 4 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (delta zeta : ℝ) (η : ℚ) (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (hetaDef : (η : ℝ) = SourceDeletionParameters.eta (width L) delta zeta)
    (hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop w Q η)
    (htstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := V)
      (width L - 2) (outerWidth L) (width L) w))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (hR0 : 1 - (η : ℝ) / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : RestorationCoverParameters.theta Q ≤
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w).prob (· ∈ Y'))
    (hmargin : 2 * w * x L + (η : ℝ) / (16 * (127 / 128 : ℝ)) < 1) :
    ∃ E0 : Finset (Fin w), ∃ row0 : R0, ∃ col0 : Y',
      let κ := matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (SourceProfiles.width_ge_four L)
      let st := actualPaddedState R0 Y' row0 col0 P E0 r
      let original := actualOriginalState R0 Y' row0 col0 P E0
      let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
      let O := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r original
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      E0.card ≤ CurrentAdditive.QuarticSchedule.e027 Q η ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
        1 - (η : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ j : Fin (RestorationCoverParameters.tExponent Q - 2),
        ∀ S : Finset (Fin w),
          S.card = RestorationCovers.smallSize j.val → Disjoint S E0 →
          (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
            (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      w - CurrentAdditive.QuarticSchedule.E27 Q η ≤
        (ReferenceOwners.ownerNodes fam final).card ∧
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) ≤
          CurrentAdditive.QuarticSchedule.E27 Q η ∧
      (∀ v : T.Leaves, final v → (fam v).active.card ≤ 1) ∧
      (∀ v : O.Leaves, (O.state v).protocol.cost = 0 →
        (O.state v).family.active = ∅) ∧
      Function.Injective (ReferenceOwners.origin fam final) ∧
      (∀ v : {v // v ∈ ReferenceOwners.ownerNodes fam final},
        ∀ i ∈ (fam v.val).unsplit,
          i = ReferenceOwners.origin fam final v) := by
  classical
  let κ := matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L) (width L)
    (SourceProfiles.width_ge_four L)
  let μRaw := SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)
  let floor := ReferenceSchedule.floor w (x L)
  let M : ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w →
      ActualColumns (X := X) (V := V) (width L - 2) (outerWidth L) (width L) w →
      Bool := fullInterlace (N (q₁ := width L - 2) base activity ξ₀) w
  let F : RawColumn (width L - 2) (outerWidth L) (width L) Y →
      RawRow (width L - 2) (outerWidth L) (width L) X
        (SourceConstruction.Items (width L) V) → Bool :=
    fun Z row => N base activity ξ₀ (.unrestricted Z) row
  have hwpos : 0 < w := by rw [hw]; positivity
  have heta : 0 < (η : ℝ) := by
    rw [hetaDef]
    exact SourceDeletionParameters.eta_pos (width L)
      (by have h := SourceProfiles.width_ge_four L; omega) delta zeta hdelta hzeta
  have heta2 : (η : ℝ) < 2 / 5 := by
    rw [hetaDef]
    exact RestorationSourceMargins.eta_lt_two_fifths (width L)
      (by have h := SourceProfiles.width_ge_four L; omega) delta zeta hdelta hzeta
  have heta1 : (η : ℝ) < 1 := by linarith
  have hη : (0 : ℚ) < η := by exact_mod_cast heta
  have hη1 : η < 1 := by exact_mod_cast heta1
  obtain ⟨E0, hE, hsingle, hsmall⟩ :=
    CurrentAdditive.QuarticRestorationCover.exists_v27_cover
      κ.toFiniteLaw w Q η hQ hη hη1 hquarter htstar Y' hY
  obtain ⟨hpair99, hpair18, hdyadic⟩ :=
    CurrentAdditive.QuarticRestorationRun.local_projections_of_v27_cover
      κ w Q Y' E0 hsmall
  obtain ⟨rowVal, hrowVal⟩ :=
    ReferenceSourceInitial.retained_rows_nonempty ν hwpos R0 (η : ℝ) (x L)
      (by unfold x; positivity) hR0 hmargin
  obtain ⟨colVal, hcolVal⟩ := positive_event_nonempty27 (κ.toFiniteLaw.iid w) Y'
    (lt_of_lt_of_le (RestorationCoverParameters.theta_pos hQ) hY)
  let row0 : R0 := ⟨rowVal, hrowVal⟩
  let col0 : Y' := ⟨colVal, hcolVal⟩
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let original := actualOriginalState R0 Y' row0 col0 P E0
  have hraw := (SourceProfiles.source_profiles μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀).2.2.2.2
  rw [← hCeq] at hraw
  have hreach := ReferenceSourceInitial.initialFamily_reaches R0 E0
  have hfloor := ReferenceSourceInitial.initialFamily_floor ν hwpos R0 E0
    (η : ℝ) (x L) hR0 hmargin
  have hactive : st.family.active = Finset.univ \ E0 := rfl
  have hvalid : st.family.unsplit ⊆ st.family.active := by
    exact ReferenceSourceInitial.initialFamily_valid R0 E0
  have hunits : 2 * st.family.active.card ≤ units st.family := by
    have hc := ReferenceSourceInitial.initialFamily_units R0 E0
    change units st.family = 2 * (w - E0.card) at hc
    rw [hc]
    have hsub : E0.card ≤ w := by
      simpa using Finset.card_le_card (Finset.subset_univ E0)
    have hcard : (Finset.univ \ E0).card = w - E0.card := by
      rw [Finset.card_sdiff]
      simp
    change 2 * (Finset.univ \ E0).card ≤ 2 * (w - E0.card)
    omega
  have hcomputeOrig : ∀ row ∈ original.rows, ∀ y ∈ Y',
      original.protocol.eval row y = M row y := by
    intro row hr y hy
    exact (actualOriginalState_eval R0 Y' row0 col0 P E0
      ⟨row, hr⟩ ⟨y, hy⟩).trans (hP ⟨row, hr⟩ ⟨y, hy⟩)
  have hcompute : ∀ row ∈ st.rows, ∀ y ∈ Y',
      st.protocol.eval row y = M row y := by
    intro row hr y hy
    exact (actualPaddedState_eval R0 Y' row0 col0 P E0 r
      ⟨row, hr⟩ ⟨y, hy⟩).trans (hP ⟨row, hr⟩ ⟨y, hy⟩)
  have hentry : ∀ i Z, ReferenceSourceInitial.input i Z ∈ st.rows →
      ∀ y ∈ Y', M (ReferenceSourceInitial.input i Z) y = F Z (y i) := by
    intro i Z _ y _
    rfl
  have hprefix : ReferencePrefix.NoEarlyLeaf r st.protocol :=
    ReferencePrefix.padAlicePrefix_noEarlyLeaf r _
  have hcost : st.protocol.cost ≤ (C - 1) + r := by
    have hc := actualPaddedState_cost R0 Y' row0 col0 P E0 r
    change st.protocol.cost ≤ max P.cost r at hc
    omega
  have hscale : 2 * (2 : ℝ) ^ r * x L ≤ 1 := by
    have hwreal : (w : ℝ) = (2 : ℝ) ^ r := by exact_mod_cast hw
    have htail : 0 ≤ (η : ℝ) / (16 * (127 / 128 : ℝ)) := by positivity
    rw [← hwreal]
    linarith
  have hcount := CurrentAdditive.QuarticRestorationRun.run_destinations27
    μRaw κ F M ReferenceSourceInitial.input Y' st E0 Q (C - 1) r η (x L)
    hw hE hQ (by omega) (by unfold x; positivity)
    hscale hraw hY hsmall hactive hvalid hunits
    hreach hfloor hcompute hentry hprefix hcost
  have hfinal := run_final_active_le_one μRaw κ F M
    ReferenceSourceInitial.input Y' st E0 r (C - 1) (x L) hw
    (by omega) (by unfold x; positivity) hscale hraw hpair99
    hactive hreach hfloor hcompute hentry hcost
  have hleaf := ReferenceOriginalLeaves.unpadded_run_leaf_active_empty
    μRaw κ F M ReferenceSourceInitial.input Y' original E0 r (C - 1)
    (x L) (η : ℝ) hw (by omega) (by unfold x; positivity) heta2 hraw
    hsingle rfl hreach hfloor hcomputeOrig
    (by intro i Z _ y _; rfl)
  let T := run μRaw.toFiniteLaw ReferenceSourceInitial.input floor 0 r st
  let O := run μRaw.toFiniteLaw ReferenceSourceInitial.input floor 0 r original
  let fam := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  have hvalidRun := run_valid μRaw.toFiniteLaw ReferenceSourceInitial.input
    floor 0 r st hvalid
  have hinj := ReferenceOwners.run_origin_injective μRaw.toFiniteLaw
    ReferenceSourceInitial.input floor r st
  have horigin : ∀ v : {v // v ∈ ReferenceOwners.ownerNodes fam final},
      ∀ i ∈ (fam v.val).unsplit, i = ReferenceOwners.origin fam final v := by
    intro v i hi
    exact ReferenceOwners.origin_eq_of_mem fam final hvalidRun hfinal v i hi
  refine ⟨E0, row0, col0, hE, hsingle, hpair99, hpair18, hdyadic,
    ?_, ?_, hfinal, hleaf, hinj, horigin⟩
  · exact hcount.1
  · exact hcount.2


end Paper2.ReferencePublicDestinations
#print axioms Paper2.ReferencePublicDestinations.actual_items_destinations27
