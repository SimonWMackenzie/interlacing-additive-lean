import Paper2.ReferencePublicDestinations
import Paper2.ForeignOwnerMass

/-!
# Foreign protected mass at two actual reference owners

Frozen v12 `res:foreign`, lines 401--446. The rectangle, remaining cost,
and distinct original origins below are obtained from one physical padded
run of the original retained protocol.
-/

namespace Paper2.ForeignOwnerRun

open SourceMatrix SourceLawBinding SourceProfileParameters
open Paper2.ReferencePublicDestinations
open ReferenceCertificateTree Workspace.Types.Protocol

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

theorem actual_owner_to_owner_mass
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 1000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r C : ℕ) (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (delta zeta eta : ℝ)
    (hetaDef : eta = SourceDeletionParameters.eta (width L) delta zeta)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := V)
      (width L - 2) (outerWidth L) (width L) w))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col => fullInterlace (N base activity ξ₀) w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (E0 : Finset (Fin w)) (row0 : R0) (col0 : Y')
    (hsingle : ∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
      1 - eta ≤ ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw)
        (· ∈ Y') S)
    (hpair : ∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
      (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L) (SourceProfiles.width_ge_four L)).toFiniteLaw)
        (· ∈ Y') S) :
    let st := actualPaddedState R0 Y' row0 col0 P E0 r
    let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
      (width L)).toFiniteLaw ReferenceSourceInitial.input
      (ReferenceSchedule.floor w (x L)) 0 r st
    let fam := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    ∀ v u : {v // v ∈ ReferenceOwners.ownerNodes fam final}, v ≠ u →
      ForeignOwnerMass.protectedMass ν L w (ReferenceOwners.origin fam final u)
        (T.state v.val).rows ≤
      2 * (1 / 256 : ℝ) * ForeignOwnerMass.foreignThreshold ν L w
        (ReferenceOwners.origin fam final v) (T.state v.val).rows := by
  classical
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let μraw := SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)
  let T := run μraw.toFiniteLaw ReferenceSourceInitial.input
    (ReferenceSchedule.floor w (x L)) 0 r st
  let fam := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  change ∀ v u : {v // v ∈ ReferenceOwners.ownerNodes fam final}, v ≠ u → _
  intro v u hvu
  let i := ReferenceOwners.origin fam final v
  let j := ReferenceOwners.origin fam final u
  have hinj : Function.Injective (ReferenceOwners.origin fam final) :=
    ReferenceOwners.run_origin_injective μraw.toFiniteLaw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r st
  have hij : i ≠ j := fun he => hvu (hinj he)
  have hi0 : i ∈ Finset.univ \ E0 := by
    have h := ReferenceOwners.run_origin_mem_initial μraw.toFiniteLaw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r st v
    exact h
  have hj0 : j ∈ Finset.univ \ E0 := by
    have h := ReferenceOwners.run_origin_mem_initial μraw.toFiniteLaw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r st u
    exact h
  have hnoti : i ∉ E0 := (Finset.mem_sdiff.mp hi0).2
  have hnotj : j ∉ E0 := (Finset.mem_sdiff.mp hj0).2
  have hpair' := hpair {i,j} (by simp [hij]) (by
    simp [Finset.disjoint_left, hnoti, hnotj])
  have hsingle' := hsingle {i} (by simp) (by
    simp [hnoti])
  have hcompute : ∀ a ∈ st.rows, ∀ y ∈ Y',
      st.protocol.eval a y = fullInterlace (N base activity ξ₀) w a y := by
    intro a ha y hy
    exact (actualPaddedState_eval R0 Y' row0 col0 P E0 r
      ⟨a, ha⟩ ⟨y, hy⟩).trans (hP ⟨a, ha⟩ ⟨y, hy⟩)
  have hnode := ReferenceRunCorrectness.computes_on_original_rectangle
    μraw.toFiniteLaw ReferenceSourceInitial.input
    (ReferenceSchedule.floor w (x L)) 0 r st
    (fullInterlace (N base activity ξ₀) w) Y' hcompute v.val
  have hcost : st.protocol.cost ≤ (C - 1) + r := by
    have hc := actualPaddedState_cost R0 Y' row0 col0 P E0 r
    change st.protocol.cost ≤ max P.cost r at hc
    omega
  have hremain := ReferenceRunCorrectness.remaining_cost μraw.toFiniteLaw
    ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r
    (C - 1) st hcost v.val
  have hvfinal : final v.val :=
    ((ReferenceOwners.mem_ownerNodes fam final v.val).mp v.property).1
  have hnodecost : (T.state v.val).protocol.cost ≤
      d + exponent L + outerExponent L + exponent L := by
    change (T.route v.val).length = r at hvfinal
    rw [hvfinal] at hremain
    rw [← hCeq]
    simpa using hremain
  have hsmall' := hsmall
  have hmass := ForeignOwnerMass.protected_mass_le μ ν base L d w
    activity ξ₀ i j hij (T.state v.val).rows Y' (T.state v.val).protocol
    hnode delta zeta hpair' (by simpa [hetaDef] using hsingle')
    hsmall' hd hp hinner houter hwide href hnodecost
  exact hmass

/-- Public original-Items package: the destination construction supplies the
same exceptional set and projection covers used by the foreign-owner bound. -/
theorem public_actual_owner_to_owner_mass
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
    (delta zeta eta : ℝ) (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (hetaDef : eta = SourceDeletionParameters.eta (width L) delta zeta)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := V)
      (width L - 2) (outerWidth L) (width L) w))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col => fullInterlace (N base activity ξ₀) w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (hR0 : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : RestorationCoverParameters.theta Q ≤
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w).prob (· ∈ Y'))
    (hmargin : 2 * w * x L + eta / (16 * (127 / 128 : ℝ)) < 1) :
    ∃ E0 : Finset (Fin w), ∃ row0 : R0, ∃ col0 : Y',
      let st := actualPaddedState R0 Y' row0 col0 P E0 r
      let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L)
        (width L)).toFiniteLaw ReferenceSourceInitial.input
        (ReferenceSchedule.floor w (x L)) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      ∀ v u : {v // v ∈ ReferenceOwners.ownerNodes fam final}, v ≠ u →
        ForeignOwnerMass.protectedMass ν L w (ReferenceOwners.origin fam final u)
          (T.state v.val).rows ≤
        2 * (1 / 256 : ℝ) * ForeignOwnerMass.foreignThreshold ν L w
          (ReferenceOwners.origin fam final v) (T.state v.val).rows := by
  classical
  obtain ⟨E0, row0, col0, _, hsingle, hpair, _⟩ :=
    actual_items_destinations μ ν base L d hd hD hp hinner houter hwide
      href activity ξ₀ w r Q C hw hQ hC hCeq delta zeta eta hdelta
      hzeta hetaDef R0 Y' P hP hPcost hR0 hY hmargin
  refine ⟨E0, row0, col0, ?_⟩
  exact actual_owner_to_owner_mass μ ν base L d hd hp hinner houter
    hwide href (by linarith) activity ξ₀ w r C hCeq delta zeta eta
    hetaDef R0 Y' P hP hPcost E0 row0 col0 hsingle hpair

end Paper2.ForeignOwnerRun

#print axioms Paper2.ForeignOwnerRun.actual_owner_to_owner_mass
#print axioms Paper2.ForeignOwnerRun.public_actual_owner_to_owner_mass
