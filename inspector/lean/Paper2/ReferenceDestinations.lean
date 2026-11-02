import Paper2.ReferenceOwners
import Paper2.ReferenceRunCorrectness
import Paper2.ReferenceTerminalCapacity
import Paper2.ReferenceSchedule

/-!
# Reference destinations on the actual annotated protocol tree

The first-Bob and final-node contradictions are applied to every physical
stop of the same runner. The owner count and exceptional capacity are then
derived from its conserved reference weight and exact full capacity.
Frozen Paper 2 v12, `res:destinations`, lines 250--310.
-/

namespace Paper2.ReferenceDestinations

open Workspace.Types.Protocol ReferenceCertificateTree ReferenceCertificates
open Paper2.SourceSupportFrontier

variable {A K Rw : Type*} [Fintype A] [Fintype K] [Fintype Rw]
  {w : ℕ}

theorem run_destinations
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (input : Fin w → A → Rw) (O : Set (Fin w → K))
    (s : State Rw (Fin w → K) (Fin w) A)
    (E0 : Finset (Fin w)) (e0 Q H r : ℕ) (x : ℝ)
    (hw : w = 2 ^ r) (hE : E0.card ≤ e0) (hQ : 0 < Q)
    (hH : 3 ≤ H) (hx : 0 < x) (hscale : 2 * (2 : ℝ) ^ r * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hY : RestorationCoverParameters.theta Q ≤
      (ν.toFiniteLaw.iid w).prob (· ∈ O))
    (hpair99 : ∀ T : Finset (Fin w), T.card = 2 → Disjoint T E0 →
      (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hpair18 : ∀ T : Finset (Fin w), T.card = 2 → Disjoint T E0 →
      (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hdyadic : ∀ j : Fin (RestorationCoverParameters.tExponent Q - 2),
      ∀ T : Finset (Fin w), T.card = RestorationCovers.smallSize j.val →
        Disjoint T E0 →
        (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hactive : s.family.active = Finset.univ \ E0)
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
    w - ReferenceOwners.exceptionBudget e0 ≤
      (ReferenceOwners.ownerNodes fam final).card ∧
    ReferenceOwners.exceptionalCapacity fam final
      (fun v => 2 ^ (r - (T.route v).length)) ≤
        ReferenceOwners.exceptionBudget e0 := by
  classical
  let floor := ReferenceSchedule.floor w x
  let T := run μ.toFiniteLaw input floor 0 r s
  have hrunFloor := run_floor μ.toFiniteLaw input floor
    (ReferenceSchedule.floor_half w x) 0 r s hfloor
  have hrunReach := run_reaches μ.toFiniteLaw input floor 0 r s hreach
  have hrunSets := run_sets_subset μ.toFiniteLaw input floor 0 r s
  have hrunValid := run_valid μ.toFiniteLaw input floor 0 r s hvalid
  have hfinal : ∀ v : T.Leaves, (T.route v).length = r →
      (T.state v).family.active.card ≤ 1 := by
    intro v hv
    let node := T.state v
    have hnodesub := ReferenceRunCorrectness.rows_subset
      μ.toFiniteLaw input floor 0 r s v
    have hnodecomp := ReferenceRunCorrectness.computes_on_original_rectangle
      μ.toFiniteLaw input floor 0 r s M O hcompute v
    have hnodereach := hrunReach v
    have hnodeavoid : Disjoint node.family.active E0 := by
      apply Finset.disjoint_left.mpr
      intro i hi hiE
      have hi0 := (hrunSets v).1 hi
      rw [hactive] at hi0
      exact (Finset.mem_sdiff.mp hi0).2 hiE
    have hnodefloor : ∀ i ∈ node.family.active,
        2 * x ≤ μ.toFiniteLaw.prob (· ∈ (node.family.support i : Set A)) := by
      intro i hi
      have hf := hrunFloor v i hi
      have heq : floor ((T.route v).length) = 2 * x := by
        change ReferenceSchedule.floor w x (T.route v).length = 2 * x
        rw [hv, ReferenceSchedule.floor_dyadic x hw (le_refl r)]
        simp
      have hf' : 2 * x ≤ SourceSupportStep.mass μ.toFiniteLaw (node.family.support i) := by
        simpa only [Nat.zero_add, ← heq] using hf
      simpa only [SourceSupportStep.mass] using hf'
    have hnodeentry : ∀ i a, input i a ∈ node.rows → ∀ y ∈ O,
        M (input i a) y = F a (y i) := by
      intro i a ha y hy
      exact hentry i a (hnodesub ha) y hy
    have hnodecost : node.protocol.cost ≤ H := by
      have hc := ReferenceRunCorrectness.remaining_cost
        μ.toFiniteLaw input floor r H s hcost v
      rw [hv] at hc
      simpa only [Nat.sub_self, Nat.add_zero] using hc
    have htwo : 2 * x ≤ 1 := by
      have hp : (1 : ℝ) ≤ 2 ^ r := by
        simpa only [one_pow] using
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      have hm := mul_le_mul_of_nonneg_right hp (le_of_lt hx)
      nlinarith [hscale]
    exact ReferenceTerminalCapacity.final_active_le_one μ ν F M input node.rows O
      node.protocol hnodecomp hnodeentry node.family E0 H x hnodeavoid
      hnodefloor hnodereach hpair99 (by omega) hx
      htwo hprofile hnodecost
  have hbob : ∀ v : T.Leaves, (T.route v).length ≠ r →
      (units (T.state v).family : ℝ) <
        9 * ((2 ^ (r - (T.route v).length) : ℕ) : ℝ) / 8 := by
    intro v hv
    let node := T.state v
    let d := (T.route v).length
    let l := r - d
    have hbefore := ReferenceRunCorrectness.before_depth_is_bob
      μ.toFiniteLaw input floor r s hprefix v hv
    obtain ⟨hl, query, left, right, hbeq⟩ := hbefore
    have hdepth := ReferenceRunCorrectness.depth_le
      μ.toFiniteLaw input floor 0 r s v
    have hnodesub := ReferenceRunCorrectness.rows_subset
      μ.toFiniteLaw input floor 0 r s v
    have hnodecomp := ReferenceRunCorrectness.computes_on_original_rectangle
      μ.toFiniteLaw input floor 0 r s M O hcompute v
    have hnodereach := hrunReach v
    have hnodevalid := hrunValid v
    have hnodeavoid : Disjoint node.family.active E0 := by
      apply Finset.disjoint_left.mpr
      intro i hi hiE
      have hi0 := (hrunSets v).1 hi
      rw [hactive] at hi0
      exact (Finset.mem_sdiff.mp hi0).2 hiE
    have hnodefloor : ∀ i ∈ node.family.active,
        (2 : ℝ) ^ l * x ≤
          μ.toFiniteLaw.prob (· ∈ (node.family.support i : Set A)) := by
      intro i hi
      have hf := hrunFloor v i hi
      have heq : floor d = 2 * (2 : ℝ) ^ l * x := by
        change ReferenceSchedule.floor w x (T.route v).length =
          2 * (2 : ℝ) ^ (r - (T.route v).length) * x
        exact ReferenceSchedule.floor_dyadic x hw hdepth
      have hf' : 2 * (2 : ℝ) ^ l * x ≤
          SourceSupportStep.mass μ.toFiniteLaw (node.family.support i) := by
        simpa only [Nat.zero_add, ← heq] using hf
      have hnonneg : 0 ≤ (2 : ℝ) ^ l * x := by positivity
      have hm : 2 * (2 : ℝ) ^ l * x ≤
          μ.toFiniteLaw.prob (· ∈ (node.family.support i : Set A)) := by
        simpa [SourceSupportStep.mass] using hf'
      nlinarith [hm, hnonneg]
    have hnodeentry : ∀ i a, input i a ∈ node.rows → ∀ y ∈ O,
        M (input i a) y = F a (y i) := by
      intro i a ha y hy
      exact hentry i a (hnodesub ha) y hy
    have hnodecost : node.protocol.cost ≤ H + l :=
      ReferenceRunCorrectness.remaining_cost μ.toFiniteLaw input floor r H s hcost v
    have hnodescale : (2 : ℝ) ^ l * x ≤ 1 := by
      have hpow : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ r :=
        pow_le_pow_right₀ (by norm_num) (by omega : l ≤ r)
      have hm := mul_le_mul_of_nonneg_right hpow (le_of_lt hx)
      have hp : 0 ≤ (2 : ℝ) ^ r * x := by positivity
      have hs : (2 : ℝ) ^ r * x ≤ 1 := by nlinarith [hscale, hp]
      exact hm.trans hs
    have hnodebob : ∀ row ∈ node.rows, ∀ y ∈ O,
        (Protocol.bNode query left right).eval row y = M row y := by
      intro row hr y hy
      rw [← hbeq]
      exact hnodecomp row hr y hy
    have hcostbob : (Protocol.bNode query left right).cost ≤ H + l := by
      rw [← hbeq]
      exact hnodecost
    exact ReferenceTerminalCapacity.first_bob_units_lt μ ν F M input
      node.rows O query left right hnodebob hnodeentry node.family
      hnodevalid E0 hnodeavoid Q H l x hQ hl hnodefloor hnodereach
      hpair18 hdyadic hY hH hx hnodescale hprofile hcostbob
  have hn : w ≤ s.family.active.card + e0 := by
    have hc : (Finset.univ \ E0).card = w - E0.card := by
      rw [Finset.card_sdiff]
      simp
    have hsub : E0.card ≤ w := by
      simpa using Finset.card_le_card (Finset.subset_univ E0)
    have hcard : w = s.family.active.card + E0.card := by
      rw [hactive]
      omega
    omega
  have hh := ReferenceOwners.run_owner_count μ.toFiniteLaw input floor r s
    s.family.active.card e0 hvalid hprefix (by rw [← hw]; exact hn)
    hunits hfinal hbob
  simpa only [T, floor, hw] using hh

end Paper2.ReferenceDestinations

#print axioms Paper2.ReferenceDestinations.run_destinations
