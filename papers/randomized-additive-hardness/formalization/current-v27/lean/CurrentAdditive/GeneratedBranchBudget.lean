import CurrentAdditive.GeneratedDiagonalDeficit
import Paper2.SourceCollisionPartition

/-!
The actual generated `det:near-full` deficit budget and collision branch
selection (I:311–334). The witness set and its branch-witness predicate are
outputs of the separate graph item-witness argument; this file selects the
branch and removes its actual deficient coordinates.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceDeficiencyTemplate
open Paper2.SourceCollisionPartition

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

noncomputable def templateBad
    (K : Set src.inner.Label) (xcap : ℝ) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter (fun α => ∃ r : Fin q₁,
    μX.toFiniteLaw.prob (fun x =>
      projectedAt (fun t : Template q₁ q₂ X =>
        ∃ z ∈ K, src.inner.decode z = t) α (r, x)) < xcap)

noncomputable def branchBad
    (K : Set src.inner.Label) (U : Set (Column src))
    (xcap : ℝ) : Finset (Fin q₂) :=
  templateBad src K xcap ∪ diagonalBad src U

/-- Every coordinate outside the actual branch deficit has all q₁ template
row blocks at the source threshold and a diagonal gamma-index fibre of
original mass at least 3/4. -/
theorem usable_coordinate_masses
    (K : Set src.inner.Label) (U : Set (Column src))
    (xcap : ℝ) (α : Fin q₂)
    (hα : α ∉ branchBad src K U xcap) :
    (∀ r : Fin q₁, xcap ≤ μX.toFiniteLaw.prob (fun x =>
      projectedAt (fun t : Template q₁ q₂ X =>
        ∃ z ∈ K, src.inner.decode z = t) α (r, x))) ∧
    3 / 4 ≤ src.gamma.law.toFiniteLaw.prob
      (fun γ => Column.diagonal (α, γ) ∈ U) := by
  classical
  have hnot : α ∉ templateBad src K xcap ∧ α ∉ diagonalBad src U := by
    simpa only [branchBad, Finset.mem_union, not_or] using hα
  constructor
  · intro r
    by_contra hh
    have hlt : μX.toFiniteLaw.prob (fun x =>
      projectedAt (fun t : Template q₁ q₂ X =>
        ∃ z ∈ K, src.inner.decode z = t) α (r, x)) < xcap :=
      lt_of_not_ge hh
    apply hnot.1
    simp only [templateBad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, hlt⟩
  · exact le_of_not_gt (by
      intro hh
      exact hnot.2 ((mem_diagonalBad src U α).mpr hh))

theorem branchBad_card_lt
    (hD : 2 ≤ D) (K : Set src.inner.Label)
    (hKmass : (1 / 7 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (U : Set (Column src)) (η xcap : ℝ)
    (hη : 0 < η) (hxcap : xcap ≤ 1 / 8)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U)) :
    ((branchBad src K U xcap).card : ℝ) <
      8 * q₁ + 1024 * η * q₂ := by
  have ht : (templateBad src K xcap).card < 8 * q₁ :=
    deficient_cap_card_lt src hD K hKmass xcap hxcap
  have hd := diagonalBad_card_lt src U η hη hU
  have hu : ((branchBad src K U xcap).card : ℝ) ≤
      (templateBad src K xcap).card + (diagonalBad src U).card := by
    exact_mod_cast Finset.card_union_le (templateBad src K xcap) (diagonalBad src U)
  have ht' : ((templateBad src K xcap).card : ℝ) < 8 * q₁ := by
    exact_mod_cast ht
  linarith

theorem sum_branchBad_card_lt
    (hD : 2 ≤ D) (K : Fin s → Set src.inner.Label)
    (hKmass : ∀ j, (1 / 7 : ℝ) <
      src.inner.law.toFiniteLaw.prob (· ∈ K j))
    (U : Set (Column src)) (η xcap : ℝ)
    (hη : 0 < η) (hxcap : xcap ≤ 1 / 8)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U)) :
    (∑ j : Fin s, ((branchBad src (K j) U xcap).card : ℝ)) <
      8 * s * q₁ + 1024 * s * η * q₂ := by
  have hh := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin s)).Nonempty)
    (fun j _ => branchBad_card_lt src hD (K j) (hKmass j)
      U η xcap hη hxcap hU)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  calc
    _ < (s : ℝ) * (8 * q₁ + 1024 * η * q₂) := hh
    _ = _ := by ring

/-- From actual graph witness coordinates and their witnessing branches,
the source's numerical schedule picks one branch with more than four
witnesses per local deficit. This branch is derived by filtering the actual
witness set, and every surviving coordinate keeps its witness predicate. -/
theorem select_usable_witness_branch
    (hD : 2 ≤ D) (K : Fin s → Set src.inner.Label)
    (hKmass : ∀ j, (1 / 7 : ℝ) <
      src.inner.law.toFiniteLaw.prob (· ∈ K j))
    (U : Set (Column src)) (η xcap ζ : ℝ)
    (hη : 0 < η) (hxcap : xcap ≤ 1 / 8)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (W : Finset (Fin q₂)) (WitnessAt : Fin s → Fin q₂ → Prop)
    (hWitness : ∀ α ∈ W, ∃ j, WitnessAt j α)
    (hW : ζ * q₂ ≤ (W.card : ℝ))
    (hSchedule : 8 * s * q₁ + 1024 * s * η * q₂ < ζ * q₂ / 4) :
    ∃ j : Fin s,
      let part := SourceCollisionPartition.part W
        (SourceCollisionPartition.chooseBranch W WitnessAt hWitness) j
      let bad := branchBad src (K j) U xcap
      4 * bad.card < part.card ∧
        3 * bad.card < (part \ bad).card ∧
        ∀ α ∈ part \ bad,
          α ∈ W ∧ WitnessAt j α ∧ α ∉ bad := by
  have hsum := sum_branchBad_card_lt src hD K hKmass U η xcap hη hxcap hU
  have hbad : (∑ j : Fin s,
      ((branchBad src (K j) U xcap).card : ℝ)) < ζ * q₂ / 4 :=
    lt_trans hsum hSchedule
  exact SourceCollisionPartition.select_witness_branch W WitnessAt hWitness
    (fun j => branchBad src (K j) U xcap) (ζ * q₂) hW hbad

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.usable_coordinate_masses
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.branchBad_card_lt
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.sum_branchBad_card_lt
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.select_usable_witness_branch
