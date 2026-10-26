import CurrentAdditive.DeterministicPairCrossAdapter
import CurrentAdditive.MomentTransfer
import CurrentAdditive.BlockJointBridge
import CurrentAdditive.EvenMoment

/-! Appendix H source high moment for the actual selected pair-image tests. -/

namespace CurrentAdditive.SuffixLong

open Paper2
open scoped BigOperators

variable {Z S : Type*} [Fintype Z] [Fintype S]

private theorem pairBlock_card_le_eight {m q : ℕ}
    (e : Fin (2*m) → Fin q) (i : Fin m) :
    (pairBlock e i).card ≤ 8 := by
  calc
    (pairBlock e i).card ≤ (Finset.univ : Finset (Fin 2)).card :=
      Finset.card_image_le
    _ = 2 := by simp
    _ ≤ 8 := by omega

/-- Bounded-wise source marginals supply the exact joint Boolean law on
every set of at most 1024 selected pair tests. -/
theorem pairHit_joint_1024 (source : FiniteLaw S) (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (K : Set S) :
    IndicatorJointAgreement source
      (fun i s => pairHit decode e K i (decode s)) 1024 := by
  classical
  intro s hs E
  have h := disjoint_blocks_indicator_joint_agreement
    source ν decode hwise (pairBlock e) (pairBlock_card_le_eight e)
    (selected_pairs_disjoint e he) (localPairHit decode e K) s hs E
  simpa only [localPairHit_restrict] using h

/-- The unconditioned source and full product have the same one-pair
marginal, so centering by the ambient pair-image mass is legitimate. -/
theorem pairHit_source_marginal (source : FiniteLaw S) (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν)
    (e : Fin (2*m) → Fin q) (K : Set S) (i : Fin m) :
    source.prob (fun s => pairHit decode e K i (decode s)) =
      (ν.iid q).prob (fun c => pairHit decode e K i c) := by
  classical
  have hsize : (pairBlock e i).card ≤ 8*1024 := by
    exact (pairBlock_card_le_eight e i).trans (by omega)
  have h := hwise (pairBlock e i) hsize
    (fun z => localPairHit decode e K i z)
  have hp := FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν)
    (fun j : pairBlock e i => j.val) Subtype.val_injective
    (fun z => localPairHit decode e K i z)
  calc
    _ = (FiniteLaw.pi (fun _ : pairBlock e i => ν)).prob
          (fun z => localPairHit decode e K i z) := by
            simpa only [localPairHit_restrict] using h
    _ = _ := by
      simpa only [FiniteLaw.iid, localPairHit_restrict] using hp.symm

/-- The paper's unconditional 1024th-moment bound for actual indexed
source outcomes. It is derived from 8192-wise original-coordinate
independence, including all repeated-index monomials. -/
theorem pairHit_source_high_moment (source : FiniteLaw S) (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (K : Set S) :
    sourceMoment source (centeredPairSourceSum ν decode e K) 1024 ≤
      2 * (256 * (m : ℝ)) ^ (512 : ℕ) := by
  classical
  let F : Fin m → S → Bool := fun i s => pairHit decode e K i (decode s)
  have hjoint : IndicatorJointAgreement source F 1024 :=
    pairHit_joint_1024 source ν decode hwise e he K
  have hcenter (s : S) :
      centeredPairSourceSum ν decode e K s =
        ∑ i : Fin m, ((if F i s then (1 : ℝ) else 0) -
          source.prob (fun s' => F i s')) := by
    unfold centeredPairSourceSum
    apply Finset.sum_congr rfl
    intro i _
    simp only [FourthMoment.centeredPair, pairBaseMass, F]
    rw [pairHit_source_marginal source ν decode hwise e K i]
  have heven : Even (1024 : ℕ) := by norm_num
  have hsource :
      sourceMoment source (centeredPairSourceSum ν decode e K) 1024 =
      expectation source (fun s => |∑ i : Fin m,
        ((if F i s then (1 : ℝ) else 0) -
          source.prob (fun s' => F i s'))| ^ 1024) := by
    unfold sourceMoment expectation
    apply Finset.sum_congr rfl
    intro s _
    rw [hcenter s]
    simp only [heven.pow_abs]
  have htransfer := centered_indicator_even_moment_eq_proxy source F 1024
    heven hjoint
  have hproxy := EvenMoment.iid_centered_indicator_moment_1024 source m F
  calc
    sourceMoment source (centeredPairSourceSum ν decode e K) 1024 =
        expectation source (fun s => |∑ i : Fin m,
          ((if F i s then (1 : ℝ) else 0) -
            source.prob (fun s' => F i s'))| ^ 1024) := hsource
    _ = expectation (source.iid m) (fun ws => |∑ i : Fin m,
          ((if F i (ws i) then (1 : ℝ) else 0) -
            source.prob (fun s' => F i s'))| ^ 1024) := htransfer
    _ ≤ 2 * (256 * (m : ℝ)) ^ (512 : ℕ) := by
      simpa only [EvenMoment.ex, expectation,
        show ((1024 : ℝ) * m) / 4 = 256 * m by ring] using hproxy

#print axioms pairHit_joint_1024
#print axioms pairHit_source_marginal
#print axioms pairHit_source_high_moment

end CurrentAdditive.SuffixLong
