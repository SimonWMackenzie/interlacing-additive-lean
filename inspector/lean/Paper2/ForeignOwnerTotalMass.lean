import Paper2.ForeignOwnerRun
import Paper2.ReferenceActualOwnerLoss

/-!
# Total foreign-owner receipts on one actual padded reference run

Frozen v12 Section 5, lines 476--483. This is only the foreign-owner upper
sum, not exceptional receipts or the final mass-balance contradiction.
-/

namespace Paper2.ForeignOwnerTotalMass

open SourceMatrix SourceLawBinding SourceProfileParameters
open Paper2.ReferencePublicDestinations
open ReferenceCertificateTree Workspace.Types.Protocol
open scoped BigOperators
open scoped Classical

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

private theorem finite_receipts_le {O : Type*} [Fintype O] [DecidableEq O]
    (w : ℕ) (δ : O → ℝ) (receipt : O → O → ℝ)
    (hδ : ∀ v, 0 ≤ δ v)
    (hcard : Fintype.card O ≤ w)
    (hpair : ∀ v u, u ≠ v → receipt u v ≤ 2 * (1 / 256 : ℝ) * δ v) :
    (∑ v : O, ∑ u ∈ Finset.univ.erase v, receipt u v) ≤
      (w : ℝ) * (2 * (1 / 256 : ℝ)) * ∑ v : O, δ v := by
  have hinner (v : O) :
      (∑ u ∈ Finset.univ.erase v, receipt u v) ≤
        (w : ℝ) * (2 * (1 / 256 : ℝ) * δ v) := by
    calc
      (∑ u ∈ Finset.univ.erase v, receipt u v) ≤
          ∑ u ∈ Finset.univ.erase v, 2 * (1 / 256 : ℝ) * δ v := by
            apply Finset.sum_le_sum
            intro u hu
            exact hpair v u (Finset.mem_erase.mp hu).1
      _ = ((Finset.univ.erase v).card : ℝ) *
            (2 * (1 / 256 : ℝ) * δ v) := by simp
      _ ≤ (w : ℝ) * (2 * (1 / 256 : ℝ) * δ v) := by
            apply mul_le_mul_of_nonneg_right _
              (mul_nonneg (by norm_num) (hδ v))
            exact_mod_cast (le_trans (Finset.card_le_card (Finset.erase_subset _ _)) hcard)
  calc
    (∑ v : O, ∑ u ∈ Finset.univ.erase v, receipt u v) ≤
      ∑ v : O, (w : ℝ) * (2 * (1 / 256 : ℝ) * δ v) :=
        Finset.sum_le_sum (by intro v _; exact hinner v)
    _ = (w : ℝ) * (2 * (1 / 256 : ℝ)) * ∑ v : O, δ v := by
      simp only [← mul_assoc, Finset.mul_sum]

set_option maxRecDepth 4096

/-- Global receipts among distinct physical owners of the same actual run.
The two cover hypotheses are precisely the outputs of the public destination
construction for `E0`; the reference-loss sum is derived, not assumed. -/
theorem actual_foreign_owner_total
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r C : ℕ) (hw : w = 2 ^ r)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (delta zeta eta : ℝ)
    (hetaDef : eta = SourceDeletionParameters.eta (width L) delta zeta)
    (heta : 0 ≤ eta)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := V)
      (width L - 2) (outerWidth L) (width L) w))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col => fullInterlace (N base activity ξ₀) w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (hR0 : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hquadratic : 2 * (w : ℝ) ^ 2 * x L ≤
      eta / (16 * (127 / 128 : ℝ)))
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤ eta / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤ eta / 32)
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
    let Owners := {v : T.Leaves // v ∈ ReferenceOwners.ownerNodes fam final}
    (∑ v : Owners, ∑ u ∈ Finset.univ.erase v,
      ForeignOwnerMass.protectedMass ν L w (ReferenceOwners.origin fam final u)
        (T.state v.val).rows) ≤ 3 * eta * w / 32 := by
  classical
  let μraw := (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let T := run μraw ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
  let fam := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  let Owners := {v : T.Leaves // v ∈ ReferenceOwners.ownerNodes fam final}
  let ε (v : Owners) := ForeignOwnerMass.referenceLoss ν L w
    (ReferenceOwners.origin fam final v) (T.state v.val).rows
  let δ (v : Owners) := ForeignOwnerMass.foreignThreshold ν L w
    (ReferenceOwners.origin fam final v) (T.state v.val).rows
  have hcard : Fintype.card Owners ≤ w := by
    have hi := ReferenceOwners.run_origin_injective μraw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r st
    simpa [Owners] using Fintype.card_le_of_injective _ hi
  have hcardR : (Fintype.card Owners : ℝ) ≤ w := by exact_mod_cast hcard
  have hx : 0 ≤ x L := by unfold x; positivity
  have hqN : 0 < outerWidth L := by unfold outerWidth; positivity
  have hq : (0 : ℝ) < outerWidth L := by exact_mod_cast hqN
  have hdiv : (0 : ℝ) ≤ 2 / outerWidth L :=
    le_of_lt (div_pos (by norm_num) hq)
  have hε (v : Owners) : 0 ≤ ε v := by
    have h := μraw.prob_le_one (fun Z =>
      ReferenceSourceInitial.input (ReferenceOwners.origin fam final v) Z ∈
        (T.state v.val).rows)
    exact sub_nonneg.mpr h
  have hδ (v : Owners) : 0 ≤ δ v := by
    have he := hε v
    change 0 ≤ 2 * outerWidth L * x L + 5 * ε v + 2 / outerWidth L
    have hprod : 0 ≤ (2 : ℝ) * outerWidth L * x L := by
      exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hq)) hx
    linarith only [hprod, he, hdiv]
  have hpairActual := ForeignOwnerRun.actual_owner_to_owner_mass μ ν base L d
    hd hp hinner houter hwide href (by linarith) activity ξ₀ w r C
    hCeq delta zeta eta hetaDef R0 Y' P hP hPcost E0 row0 col0
    hsingle hpair
  have hsum := finite_receipts_le w δ
    (fun u v : Owners => ForeignOwnerMass.protectedMass ν L w
      (ReferenceOwners.origin fam final u) (T.state v.val).rows)
    hδ hcard (by intro v u hne; exact hpairActual v u (Ne.symm hne))
  have hloss := ReferenceActualOwnerLoss.total_reference_loss ν r hw R0 Y'
    row0 col0 P E0 eta (x L) hx hR0 hquadratic
  have hloss' : (∑ v : Owners, ε v) ≤ eta / (8 * (127 / 128 : ℝ)) := by
    exact hloss
  have hδsum : (∑ v : Owners, δ v) ≤
      (w : ℝ) * (2 * outerWidth L * x L + 2 / outerWidth L) +
        5 * eta / (8 * (127 / 128 : ℝ)) := by
    have hbase : 0 ≤ 2 * (outerWidth L : ℝ) * x L +
        2 / outerWidth L := by
          have hprod : 0 ≤ (2 : ℝ) * outerWidth L * x L := by
            exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hq)) hx
          linarith only [hprod, hdiv]
    have hmul := mul_le_mul_of_nonneg_right hcardR hbase
    have hsumε := mul_le_mul_of_nonneg_left hloss' (by norm_num : (0:ℝ) ≤ 5)
    have heq : (∑ v : Owners, δ v) =
        (Fintype.card Owners : ℝ) *
          (2 * outerWidth L * x L + 2 / outerWidth L) +
          5 * ∑ v : Owners, ε v := by
      calc
        _ = ∑ v : Owners,
          ((2 * outerWidth L * x L + 2 / outerWidth L) + 5 * ε v) := by
            apply Finset.sum_congr rfl
            intro v _
            dsimp [δ, ForeignOwnerMass.foreignThreshold, ε]
            ring
        _ = (Fintype.card Owners : ℝ) *
          (2 * outerWidth L * x L + 2 / outerWidth L) +
          5 * ∑ v : Owners, ε v := by
            have hc : (∑ _v : Owners,
                (2 * (outerWidth L : ℝ) * x L + 2 / outerWidth L)) =
                (Fintype.card Owners : ℝ) *
                  (2 * outerWidth L * x L + 2 / outerWidth L) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have hs : (∑ v : Owners, 5 * ε v) =
                5 * ∑ v : Owners, ε v := by rw [Finset.mul_sum]
            rw [Finset.sum_add_distrib]
            rw [hc, hs]
    rw [heq]
    convert add_le_add hmul hsumε using 1 <;> ring
  have hmargin := RestorationSourceMargins.foreign_receipt_margin w
    (outerWidth L) eta (x L) heta hfirst hlast
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hmul := mul_le_mul_of_nonneg_left hδsum
    (mul_nonneg hw0 (by norm_num : (0:ℝ) ≤ 2 * (1 / 256 : ℝ)))
  change (∑ v : Owners, ∑ u ∈ Finset.univ.erase v,
    ForeignOwnerMass.protectedMass ν L w (ReferenceOwners.origin fam final u)
      (T.state v.val).rows) ≤ 3 * eta * w / 32
  calc
    _ ≤ (w : ℝ) * (2 * (1 / 256 : ℝ)) * ∑ v : Owners, δ v := hsum
    _ ≤ (w : ℝ) * (2 * (1 / 256 : ℝ)) *
      ((w : ℝ) * (2 * outerWidth L * x L + 2 / outerWidth L) +
        5 * eta / (8 * (127 / 128 : ℝ))) := hmul
    _ = (w : ℝ) * (2 * (1 / 256 : ℝ) * w *
      (2 * outerWidth L * x L) +
      5 * (1 / 256 : ℝ) * eta / (4 * (127 / 128 : ℝ)) +
      4 * (1 / 256 : ℝ) * w / outerWidth L) := by ring
    _ ≤ 3 * eta * w / 32 := hmargin

#print axioms Paper2.ForeignOwnerTotalMass.actual_foreign_owner_total

end Paper2.ForeignOwnerTotalMass
