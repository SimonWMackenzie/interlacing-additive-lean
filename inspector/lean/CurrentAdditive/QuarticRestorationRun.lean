import CurrentAdditive.QuarticRestorationCover
import Paper2.ReferenceDestinations

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-! Private v27 adapter: the new two-cover event controls the actual
annotated reference-certificate run. -/

namespace CurrentAdditive.QuarticRestorationRun

open Paper2 Paper2.RestorationCoverParameters
open Paper2.ReferenceCertificateTree Paper2.ReferenceCertificates
open Paper2.SourceSupportFrontier

theorem dyadic_size_le_mStar (Q : ℕ)
    (j : Fin (tExponent Q - 2)) :
    Paper2.RestorationCovers.smallSize j.val ≤ tStar Q / 4 + 1 := by
  have hm : 2 ≤ tExponent Q := tExponent_ge_two Q
  have hj : j.val + 1 ≤ tExponent Q - 2 := by
    have := j.isLt
    omega
  have hp : 2 ^ (j.val + 1) ≤ 2 ^ (tExponent Q - 2) := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) hj
  have htpow : tStar Q = 4 * 2 ^ (tExponent Q - 2) := by
    calc
      tStar Q = 2 ^ tExponent Q := tStar_pow Q
      _ = 2 ^ ((tExponent Q - 2) + 2) :=
        congrArg (fun n : ℕ => 2 ^ n) (by omega)
      _ = 4 * 2 ^ (tExponent Q - 2) := by
        rw [pow_add]
        norm_num
        omega
  unfold Paper2.RestorationCovers.smallSize
  rw [htpow]
  omega

/-- The v27 `0.99` guarantee for all sizes up to `m*` supplies the exact
local projection premises used by the checked annotated-run theorem. -/
theorem local_projections_of_v27_cover {K : Type*} [Fintype K]
    (ν : PositiveRationalLaw K) (w Q : ℕ) (O : Set (Fin w → K))
    (E₀ : Finset (Fin w))
    (hsmall : ∀ T : Finset (Fin w), T.card ≤ tStar Q / 4 + 1 →
      Disjoint T E₀ → (99 / 100 : ℝ) ≤
        ProductProjections.projectionMass
          (fun _ => ν.toFiniteLaw) (· ∈ O) T) :
    (∀ T : Finset (Fin w), T.card = 2 → Disjoint T E₀ →
      (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T) ∧
    (∀ T : Finset (Fin w), T.card = 2 → Disjoint T E₀ →
      (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T) ∧
    (∀ j : Fin (tExponent Q - 2), ∀ T : Finset (Fin w),
      T.card = Paper2.RestorationCovers.smallSize j.val →
      Disjoint T E₀ →
      (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T) := by
  have hm : 2 ≤ tStar Q / 4 + 1 := by
    have ht := tStar_ge Q
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro T hT hd
    exact hsmall T (by omega) hd
  · intro T hT hd
    have h := hsmall T (by omega) hd
    linarith
  · intro j T hT hd
    have h := hsmall T (by rw [hT]; exact dyadic_size_le_mStar Q j) hd
    linarith

variable {A K Rw : Type*} [Fintype A] [Fintype K] [Fintype Rw]
  {w : ℕ}

/-- The existing run theorem proves the first-Bob and final-node bounds
from v27's stronger cover, with the literal new exceptional count. -/
theorem run_destinations27
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (input : Fin w → A → Rw) (O : Set (Fin w → K))
    (s : State Rw (Fin w → K) (Fin w) A)
    (E₀ : Finset (Fin w)) (Q H r : ℕ) (η : ℚ) (x : ℝ)
    (hw : w = 2 ^ r) (hE : E₀.card ≤ QuarticSchedule.e027 Q η)
    (hQ : 0 < Q) (hH : 3 ≤ H) (hx : 0 < x)
    (hscale : 2 * (2 : ℝ) ^ r * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hY : theta Q ≤ (ν.toFiniteLaw.iid w).prob (· ∈ O))
    (hsmall : ∀ T : Finset (Fin w), T.card ≤ tStar Q / 4 + 1 →
      Disjoint T E₀ → (99 / 100 : ℝ) ≤
        ProductProjections.projectionMass
          (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hactive : s.family.active = Finset.univ \ E₀)
    (hvalid : s.family.unsplit ⊆ s.family.active)
    (hunits : 2 * s.family.active.card ≤ units s.family)
    (hreach : ∀ i ∈ s.family.active, ∀ a ∈ s.family.support i,
      input i a ∈ s.rows)
    (hfloor : ∀ i ∈ s.family.active,
      ReferenceSchedule.floor w x 0 ≤
        SourceSupportStep.mass μ.toFiniteLaw (s.family.support i))
    (hcompute : ∀ row ∈ s.rows, ∀ y ∈ O, s.protocol.eval row y = M row y)
    (hentry : ∀ i a, input i a ∈ s.rows → ∀ y ∈ O,
      M (input i a) y = F a (y i))
    (hprefix : ReferencePrefix.NoEarlyLeaf r s.protocol)
    (hcost : s.protocol.cost ≤ H + r) :
    let T := run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s
    let fam := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    w - QuarticSchedule.E27 Q η ≤
      (ReferenceOwners.ownerNodes fam final).card ∧
    ReferenceOwners.exceptionalCapacity fam final
      (fun v => 2 ^ (r - (T.route v).length)) ≤
        QuarticSchedule.E27 Q η := by
  obtain ⟨hpair99, hpair18, hdyadic⟩ :=
    local_projections_of_v27_cover ν w Q O E₀ hsmall
  have h := ReferenceDestinations.run_destinations μ ν F M input O s
    E₀ (QuarticSchedule.e027 Q η) Q H r x hw hE hQ hH hx hscale
    hprofile hY hpair99 hpair18 hdyadic hactive hvalid hunits
    hreach hfloor hcompute hentry hprefix hcost
  simpa only [← QuarticRestorationCover.E27_eq_referenceBudget] using h

end CurrentAdditive.QuarticRestorationRun

#print axioms CurrentAdditive.QuarticRestorationRun.dyadic_size_le_mStar
#print axioms CurrentAdditive.QuarticRestorationRun.local_projections_of_v27_cover
#print axioms CurrentAdditive.QuarticRestorationRun.run_destinations27
