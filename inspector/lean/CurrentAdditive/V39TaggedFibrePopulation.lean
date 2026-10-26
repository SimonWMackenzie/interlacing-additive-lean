import Paper2.PairedSelectorPopulation

/-! Current res:paired initial count, including zero ordinary deletion.
All qualifying ordinary and foreign fibres are counted as distinct tagged
coordinates. There is no old three-pairs-per-bad-fibre requirement. -/

namespace CurrentAdditive.V39TaggedFibrePopulation

open Paper2 Paper2.PairedSelectorPopulation

variable {I W : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype W]

noncomputable def taggedGood (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    Finset (Bool × I) :=
  (good μ O t).image (fun i => (false,i)) ∪
    (good μ F t).image (fun i => (true,i))

theorem taggedGood_card (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    (taggedGood μ O F t).card = (good μ O t).card + (good μ F t).card := by
  classical
  have hi (b : Bool) : Function.Injective (fun i : I => (b,i)) := by
    intro i j h
    exact congrArg Prod.snd h
  have hd : Disjoint ((good μ O t).image (fun i => (false,i)))
      ((good μ F t).image (fun i => (true,i))) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hb
    have he := congrArg Prod.fst (hi.trans hj.symm)
    cases he
  rw [taggedGood,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (hi false),
    Finset.card_image_of_injective _ (hi true)]

/-- More foreign good fibres than missing ordinary good fibres, from the
source's exact strict inequality delta>t+epsilon. In particular epsilon=0
requires no additive 2/q slack. -/
theorem foreign_good_gt_bad (μ : PositiveRationalLaw W)
    (O F : Set (I × W)) (t ε δ : ℝ)
    (hO : 1-ε ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ F))
    (hε : 0 ≤ ε) (hδ : δ ≤ 1) (hslack : t+ε < δ) :
    (Finset.univ \ good μ.toFiniteLaw O t).card <
      (good μ.toFiniteLaw F t).card := by
  classical
  let B := Finset.univ \ good μ.toFiniteLaw O t
  let G := good μ.toFiniteLaw F t
  have hN : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have ht : t < 1 := by linarith
  have hB : B = Finset.univ.filter
      (fun i => μ.toFiniteLaw.prob (fun w => (i,w) ∈ O) < t) := by
    ext i
    simp [B]
  have hb : (B.card : ℝ)*(1-t) ≤ ε*Fintype.card I := by
    rw [hB]
    apply deficient_card_mul_le _ t ε (fun _ => μ.toFiniteLaw.prob_le_one _)
    simpa only [column_average] using hO
  have hf : (Fintype.card I : ℝ)*(δ-t) ≤ (G.card : ℝ)*(1-t) := by
    apply good_card_mul_ge _ t δ (fun _ => μ.toFiniteLaw.prob_le_one _)
    simpa only [column_average] using hF
  have hs := mul_lt_mul_of_pos_left hslack hN
  have hcard : (B.card : ℝ) < G.card := by nlinarith
  exact_mod_cast hcard

theorem tagged_good_count_gt (μ : PositiveRationalLaw W)
    (O F : Set (I × W)) (t ε δ : ℝ)
    (hO : 1-ε ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ F))
    (hε : 0 ≤ ε) (hδ : δ ≤ 1) (hslack : t+ε < δ) :
    Fintype.card I < (taggedGood μ.toFiniteLaw O F t).card := by
  have hh := foreign_good_gt_bad μ O F t ε δ hO hF hε hδ hslack
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (good μ.toFiniteLaw O t))
  rw [taggedGood_card]
  simp only [Finset.card_univ] at hc
  omega

/-- Every counted tagged coordinate has its actual original retained
word fibre, and is measured under the unconditioned base-row law. -/
theorem tagged_good_floor (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    ∀ a ∈ taggedGood μ O F t,
      t ≤ SourceSupportStep.mass μ (PairedSelectorPopulation.support O F a) := by
  classical
  intro a ha
  rcases Finset.mem_union.mp ha with ho | hf
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ho
    simpa [PairedSelectorPopulation.support,SourceSupportStep.mass,mem_fibre] using
      (mem_good μ O t i).mp hi
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    simpa [PairedSelectorPopulation.support,SourceSupportStep.mass,mem_fibre] using
      (mem_good μ F t i).mp hi

end CurrentAdditive.V39TaggedFibrePopulation

#print axioms CurrentAdditive.V39TaggedFibrePopulation.taggedGood_card
#print axioms CurrentAdditive.V39TaggedFibrePopulation.foreign_good_gt_bad
#print axioms CurrentAdditive.V39TaggedFibrePopulation.tagged_good_count_gt
#print axioms CurrentAdditive.V39TaggedFibrePopulation.tagged_good_floor
