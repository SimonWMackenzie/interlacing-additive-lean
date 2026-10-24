import Paper2.RestorationCovers
import Paper2.RestorationCoverParameters
import CurrentAdditive.RandomizedQuarticSchedule

/-! Private v27 Section 5: the two-cover restoration exceptional set. -/

namespace CurrentAdditive.QuarticRestorationCover

open Paper2
open Paper2.RestorationCoverParameters

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

omit [Fintype ι] in
/-- Projection mass is antitone under inclusion of the retained coordinates. -/
theorem projectionMass_antitone (μ : ι → FiniteLaw K)
    (Z : (ι → K) → Prop) {S T : Finset ι} (hST : S ⊆ T) :
    ProductProjections.projectionMass μ Z T ≤
      ProductProjections.projectionMass μ Z S := by
  classical
  let e : S → T := fun i => ⟨i.val, hST i.property⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Subtype.ext (congrArg (fun z : T => z.val) hij)
  unfold ProductProjections.projectionMass
  have heq : (FiniteLaw.pi (fun i : T => μ i.val)).prob
      (fun y => ProductProjections.projected Z S (fun i => y (e i))) =
      (FiniteLaw.pi (fun i : S => μ i.val)).prob
        (ProductProjections.projected Z S) := by
    simpa only [e] using
      (FiniteLaw.pi_prob_restrict (fun i : T => μ i.val) e he
        (ProductProjections.projected Z S))
  rw [← heq]
  apply FiniteLaw.prob_mono
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨x, hx, ?_⟩
  apply funext
  intro i
  have h := congrFun hxy (e i)
  exact h

/-- The two v27 covers, before any width assumptions are used. -/
theorem exists_two_covers (κ : FiniteLaw K) (w Q : ℕ) (η : ℝ)
    (hQ : 0 < Q) (hη : 0 < η) (hη1 : η < 1)
    (Y' : Set (Fin w → K))
    (hY : theta Q ≤ (κ.iid w).prob (· ∈ Y')) :
    ∃ E₀ : Finset (Fin w),
      E₀.card ≤ (B1 Q η - 1) + (tStar Q / 4 + 1) * (B2 Q - 1) ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E₀ →
        1 - η ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = tStar Q / 4 + 1 → Disjoint S E₀ →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ) (· ∈ Y') S) := by
  classical
  have hYpi : theta Q ≤
      (FiniteLaw.pi (fun _ : Fin w => κ)).prob (· ∈ Y') := by
    rwa [Paper2.RestorationCovers.pi_const_prob]
  obtain ⟨C₁, hC₁, hcover₁⟩ := ProductProjections.projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') 1 (B1 Q η)
    (B1_pos Q hη) (theta Q) (1 - η) hYpi (B1_gap hQ hη hη1)
  obtain ⟨C₂, hC₂, hcover₂⟩ := ProductProjections.projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') (tStar Q / 4 + 1) (B2 Q)
    (B2_pos Q) (theta Q) (99 / 100) hYpi (B2_gap hQ)
  refine ⟨C₁ ∪ C₂, ?_, ?_, ?_⟩
  · have h := Finset.card_union_le C₁ C₂
    omega
  · intro S hS hd
    have hd₁ : Disjoint S C₁ := Finset.disjoint_left.mpr (by
      intro i hi hi₁
      exact (Finset.disjoint_left.mp hd) hi (Finset.mem_union_left C₂ hi₁))
    by_contra hn
    exact (hcover₁ S hS (lt_of_not_ge hn)) hd₁
  · intro S hS hd
    have hd₂ : Disjoint S C₂ := Finset.disjoint_left.mpr (by
      intro i hi hi₂
      exact (Finset.disjoint_left.mp hd) hi (Finset.mem_union_right C₁ hi₂))
    by_contra hn
    exact (hcover₂ S hS (lt_of_not_ge hn)) hd₂

/-- A cover at cardinality `m` protects every smaller projection when
there are at least `m` coordinates outside the cover. -/
theorem exists_full_cover (κ : FiniteLaw K) (w Q : ℕ) (η : ℝ)
    (hQ : 0 < Q) (hη : 0 < η) (hη1 : η < 1)
    (Y' : Set (Fin w → K))
    (hY : theta Q ≤ (κ.iid w).prob (· ∈ Y'))
    (hroom : (B1 Q η - 1) + (tStar Q / 4 + 1) * (B2 Q - 1) +
      (tStar Q / 4 + 1) ≤ w) :
    ∃ E₀ : Finset (Fin w),
      E₀.card ≤ (B1 Q η - 1) + (tStar Q / 4 + 1) * (B2 Q - 1) ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E₀ →
        1 - η ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card ≤ tStar Q / 4 + 1 → Disjoint S E₀ →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ) (· ∈ Y') S) := by
  classical
  obtain ⟨E₀, hE₀, hsingle, hbig⟩ :=
    exists_two_covers κ w Q η hQ hη hη1 Y' hY
  refine ⟨E₀, hE₀, hsingle, ?_⟩
  intro S hScard hdisj
  let R : Finset (Fin w) := Finset.univ \ E₀
  have hSR : S ⊆ R := by
    intro i hi
    simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun hiE => (Finset.disjoint_left.mp hdisj) hi hiE
  have hRcard : R.card + E₀.card = w := by
    simpa [R] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E₀))
  have hRlarge : tStar Q / 4 + 1 ≤ R.card := by omega
  obtain ⟨T, hST, hTR, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hSR hScard hRlarge
  have hTdisj : Disjoint T E₀ := by
    apply Finset.disjoint_left.mpr
    intro i hiT hiE
    have hiR := hTR hiT
    exact (Finset.mem_sdiff.mp hiR).2 hiE
  exact (hbig T hTcard hTdisj).trans
    (projectionMass_antitone (fun _ => κ) (· ∈ Y') hST)

/-- The rational exceptional count in the quartic schedule dominates the
cardinality of the two actual covers. -/
theorem e027_le_E27 (Q : ℕ) (η : ℚ) :
    QuarticSchedule.e027 Q η ≤ QuarticSchedule.E27 Q η := by
  have h : (QuarticSchedule.e027 Q η : ℚ) ≤
      16 * (QuarticSchedule.e027 Q η : ℚ) / 7 := by
    have hn : (0 : ℚ) ≤ QuarticSchedule.e027 Q η := by positivity
    linarith
  have hc : (QuarticSchedule.e027 Q η : ℚ) ≤
      (QuarticSchedule.E27 Q η : ℚ) := by
    exact h.trans (by
      unfold QuarticSchedule.E27
      exact Nat.le_ceil _)
  exact_mod_cast hc

/-- The cover budget uses exactly the ceiling in the checked generic
reference-owner counting theorem. -/
theorem E27_eq_referenceBudget (Q : ℕ) (η : ℚ) :
    QuarticSchedule.E27 Q η =
      ReferenceOwners.exceptionBudget (QuarticSchedule.e027 Q η) := by
  have hc : Nat.ceil
      ((((16 * (QuarticSchedule.e027 Q η : ℚ)) / 7 : ℚ) : ℝ)) =
      Nat.ceil ((16 * (QuarticSchedule.e027 Q η : ℚ)) / 7) := by
    rw [← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]
  unfold QuarticSchedule.E27 ReferenceOwners.exceptionBudget
  rw [← hc]
  congr 1
  push_cast
  rfl

theorem initial_count_from_cover {w Q : ℕ} {η : ℚ}
    {E₀ : Finset (Fin w)} (hE₀ : E₀.card ≤ QuarticSchedule.e027 Q η) :
    w ≤ (w - E₀.card) + QuarticSchedule.e027 Q η := by
  have hcard : E₀.card ≤ w := by simpa using Finset.card_le_univ E₀
  omega

/-- The checked reference-owner counting theorem instantiated with the
new cover, so its conclusion uses the literal v27 `E`. The tree-local
communication estimates and conserved-weight premise remain visible. -/
theorem owner_count27 {V W : Type*} [Fintype V]
    (w Q : ℕ) (η : ℚ)
    (family : V → ReferenceCertificates.Family (Fin w) W)
    (final : V → Prop) (capacity : V → ℕ)
    (E₀ : Finset (Fin w))
    (hE₀ : E₀.card ≤ QuarticSchedule.e027 Q η)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → capacity v = 1 ∧ (family v).active.card ≤ 1)
    (hbob : ∀ v, ¬ final v →
      (ReferenceCertificates.units (family v) : ℝ) < 9 * (capacity v : ℝ) / 8)
    (hcapacity : ∑ v, capacity v = w)
    (hweight : 2 * (w - E₀.card) ≤
      ∑ v, ReferenceCertificates.units (family v)) :
    w - QuarticSchedule.E27 Q η ≤
      (ReferenceOwners.ownerNodes family final).card ∧
    ReferenceOwners.exceptionalCapacity family final capacity ≤
      QuarticSchedule.E27 Q η := by
  have h := ReferenceOwners.owner_count family final capacity
    w (w - E₀.card) (QuarticSchedule.e027 Q η)
    hvalid hfinal hbob hcapacity hweight (initial_count_from_cover hE₀)
  simpa only [← E27_eq_referenceBudget] using h

/-- The exact v27 rational exceptional count, with the actual quartic
schedule's two room checks, gives all small-set projection conclusions. -/
theorem exists_v27_cover (κ : FiniteLaw K) (w Q : ℕ) (η : ℚ)
    (hQ : 0 < Q) (hη : 0 < η) (hη1 : η < 1)
    (hquarter : QuarticSchedule.quarterCheck27Prop w Q η)
    (htstar : 4 * tStar Q ≤ w)
    (Y' : Set (Fin w → K))
    (hY : theta Q ≤ (κ.iid w).prob (· ∈ Y')) :
    ∃ E₀ : Finset (Fin w),
      E₀.card ≤ QuarticSchedule.e027 Q η ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E₀ →
        1 - (η : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card ≤ tStar Q / 4 + 1 → Disjoint S E₀ →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ) (· ∈ Y') S) := by
  have hηreal : (0 : ℝ) < η := by exact_mod_cast hη
  have hηreal1 : (η : ℝ) < 1 := by exact_mod_cast hη1
  have hm : tStar Q / 4 + 1 ≤ tStar Q := by
    have ht := tStar_ge Q
    omega
  have hroom : (B1 Q (η : ℝ) - 1) +
      (tStar Q / 4 + 1) * (B2 Q - 1) +
      (tStar Q / 4 + 1) ≤ w := by
    have he := e027_le_E27 Q η
    have hq : 4 * QuarticSchedule.E27 Q η ≤ w := hquarter
    rw [← Paper2.RationalCoverSchedule.B1_real] at *
    unfold QuarticSchedule.e027 at he
    omega
  simpa only [← Paper2.RationalCoverSchedule.B1_real,
    QuarticSchedule.e027] using
    (exists_full_cover κ w Q (η : ℝ) hQ hηreal hηreal1 Y' hY hroom)

end CurrentAdditive.QuarticRestorationCover

#print axioms CurrentAdditive.QuarticRestorationCover.projectionMass_antitone
#print axioms CurrentAdditive.QuarticRestorationCover.exists_two_covers
#print axioms CurrentAdditive.QuarticRestorationCover.exists_full_cover
#print axioms CurrentAdditive.QuarticRestorationCover.e027_le_E27
#print axioms CurrentAdditive.QuarticRestorationCover.E27_eq_referenceBudget
#print axioms CurrentAdditive.QuarticRestorationCover.initial_count_from_cover
#print axioms CurrentAdditive.QuarticRestorationCover.owner_count27
#print axioms CurrentAdditive.QuarticRestorationCover.exists_v27_cover
