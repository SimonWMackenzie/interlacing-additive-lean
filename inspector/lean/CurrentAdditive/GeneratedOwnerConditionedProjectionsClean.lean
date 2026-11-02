import CurrentAdditive.GeneratedOwnerGoodSingleton

/-! Appendix I:501--511. One conditioning witness gives both the near-full
singleton images and the 0.99 pair images of a possibly rare retained
complete-tuple event. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

/-- One exceptional set simultaneously controls all singleton and pair
projections of the actual complete-stream source. `U` may itself be rare;
only `Yevent⊆U` and positive `Yevent` mass are required. -/
theorem owner_good_singletons_and_pairs_from_conditioning
    {w : ℕ} (streams : InternalStreams src μI w)
    (U Yevent : Set (InternalLabel src streams))
    (hYU : Yevent ⊆ U)
    (v τ η : ℝ)
    (hv : 0 < v)
    (hvY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hτ : 0 < τ)
    (hD : 8 * 1024 ≤ D)
    (hεpair : CurrentAdditive.conditioningEpsilonR 1024 v τ ≤ 1 / 100)
    (hεsingle : CurrentAdditive.conditioningEpsilonR 1024 v τ ≤ η/2) :
    ∃ E : Finset (Fin w),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      (∀ i : Fin w, i ∉ E →
        (rowLaw src μI).toFiniteLaw.prob
          (fun k => k ∉ (InternalStreams.decode src streams · i) '' U) ≤ η/2) ∧
      (∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
        (99 / 100 : ℝ) ≤
          ((rowLaw src μI).toFiniteLaw.prod
            (rowLaw src μI).toFiniteLaw).prob
              (· ∈ (fun t =>
                (InternalStreams.decode src streams t i,
                 InternalStreams.decode src streams t j)) '' U)) := by
  classical
  have hwise : IsDWise (8 * 1024) streams.law.toFiniteLaw
      (InternalStreams.decode src streams) (rowLaw src μI).toFiniteLaw := by
    intro J hJ A
    exact (internal_streams_row_dwise src μI streams) J (by omega) A
  obtain ⟨E, hEcard, hTV⟩ :=
    CurrentAdditive.conditioning_exceptional_coordinates_R
      (by decide : Even 1024) (by decide : 8 ≤ 1024)
      streams.law.toFiniteLaw (rowLaw src μI).toFiniteLaw
      (InternalStreams.decode src streams) (· ∈ Yevent)
      v τ hv hvY hτ hwise
  refine ⟨E, hEcard, ?_, ?_⟩
  · intro i hi
    let e : Fin 1 → Fin w := fun _ => i
    have hsubset : Finset.univ.image e ⊆
        (Finset.univ : Finset (Fin w)) \ E := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      simp [e, hi]
    have hcard : (Finset.univ.image e).card ≤ 8 := by
      calc
        (Finset.univ.image e).card ≤ (Finset.univ : Finset (Fin 1)).card :=
          Finset.card_image_le
        _ = 1 := by decide
        _ ≤ 8 := by omega
    exact (owner_singleton_loss_of_projectionTV src μI streams U Yevent
      hYU (lt_of_lt_of_le hv hvY) i
      (CurrentAdditive.conditioningEpsilonR 1024 v τ)
      (hTV (Finset.univ.image e) hsubset hcard)).trans hεsingle
  · intro i j hij hi hj
    let e : Fin 2 → Fin w := fun k => if k.val = 0 then i else j
    have he_mem (k : Fin 2) : e k ∉ E := by
      fin_cases k <;> simp [e, hi, hj]
    have hsubset : Finset.univ.image e ⊆
        (Finset.univ : Finset (Fin w)) \ E := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      simp [he_mem k]
    have hcard : (Finset.univ.image e).card ≤ 8 := by
      calc
        (Finset.univ.image e).card ≤ (Finset.univ : Finset (Fin 2)).card :=
          Finset.card_image_le
        _ = 2 := by decide
        _ ≤ 8 := by omega
    exact owner_good_pair_image_of_projectionTV src μI streams U Yevent
      hYU (lt_of_lt_of_le hv hvY) i j hij
      (CurrentAdditive.conditioningEpsilonR 1024 v τ) hεpair
      (hTV (Finset.univ.image e) hsubset hcard)

#print axioms owner_good_singletons_and_pairs_from_conditioning

end CurrentAdditive.DeterministicIndexedMatrix.Sources
