import CurrentAdditive.ConditioningExceptionSet
import CurrentAdditive.ConditioningMoments
import Paper2.FiniteSampling

/-!
Finite-law interface for v27, Appendix H, `det:conditioning`. The indexed
source has a law on seed indices `Ω` and a decoding map to `Z^q`; the ambient
comparison law is the full product `μ.iid q`.
-/

namespace CurrentAdditive

open scoped BigOperators

/-- Restrict a decoded tuple to the finite coordinate set `J`. -/
def projection {Ω Z : Type*} {q : ℕ} (draw : Ω → Fin q → Z)
    (J : Finset (Fin q)) (ω : Ω) : J → Z := fun j => draw ω j.1

/-- Difference of probabilities of one event on a finite projection. -/
noncomputable def projectionEventDifference
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (J : Finset (Fin q))
    (A : Finset (J → Z)) : ℝ :=
  ρ.prob (fun ω => projection draw J ω ∈ A) -
    (μ.iid q).prob (fun z => projection id J z ∈ A)

/-- Total variation of the projected indexed law and the ambient product
law: the maximum signed event-probability difference. Taking the complement
of an event reverses the sign, so this is the usual total variation distance
on a finite sample space. -/
noncomputable def projectionTV
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (J : Finset (Fin q)) : ℝ :=
  (Finset.univ : Finset (Finset (J → Z))).sup'
    ⟨∅, Finset.mem_univ _⟩ (projectionEventDifference ρ μ draw J)

/-- A strict total-variation violation has a genuine witnessing event. -/
theorem projectionTV_witness
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (J : Finset (Fin q)) (ε : ℝ)
    (h : ε < projectionTV ρ μ draw J) :
    ∃ A : Finset (J → Z),
      ε < projectionEventDifference ρ μ draw J A := by
  obtain ⟨A, _, hA⟩ := (Finset.lt_sup'_iff _).mp h
  exact ⟨A, hA⟩

/-- Every projection onto the empty set is the unique empty tuple, so its
total variation is exactly zero. -/
theorem projectionTV_empty
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) :
    projectionTV ρ μ draw (∅ : Finset (Fin q)) = 0 := by
  classical
  have hdiff (A : Finset ((∅ : Finset (Fin q)) → Z)) :
      projectionEventDifference ρ μ draw ∅ A = 0 := by
    let a₀ := projection draw (∅ : Finset (Fin q))
      (Classical.choice ρ.nonempty)
    have hsource (ω : Ω) : projection draw ∅ ω = a₀ := Subsingleton.elim _ _
    have hambient (z : Fin q → Z) : projection id ∅ z = a₀ := Subsingleton.elim _ _
    by_cases hA : a₀ ∈ A
    · have hsourceEvent : (fun ω => projection draw ∅ ω ∈ A) =
          (fun _ : Ω => True) := by
        funext ω
        apply propext
        simp [hsource ω, hA]
      have hambientEvent : (fun z => projection id ∅ z ∈ A) =
          (fun _ : Fin q → Z => True) := by
        funext z
        apply propext
        simp [hambient z, hA]
      simp [projectionEventDifference, hsourceEvent, hambientEvent]
    · have hsourceEvent : (fun ω => projection draw ∅ ω ∈ A) =
          (fun _ : Ω => False) := by
        funext ω
        apply propext
        simp [hsource ω, hA]
      have hambientEvent : (fun z => projection id ∅ z ∈ A) =
          (fun _ : Fin q → Z => False) := by
        funext z
        apply propext
        simp [hambient z, hA]
      simp [projectionEventDifference, hsourceEvent, hambientEvent]
  unfold projectionTV
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).mpr
    intro A _
    exact le_of_eq (hdiff A)
  · have hle := Finset.le_sup'
        (projectionEventDifference ρ μ draw (∅ : Finset (Fin q)))
        (Finset.mem_univ (∅ : Finset ((∅ : Finset (Fin q)) → Z)))
    rw [hdiff] at hle
    exact hle

/-- The actual finite family of bad coordinate sets at threshold `ε`. -/
noncomputable def badCoordinateSets
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ) : Finset (Finset (Fin q)) := by
  classical
  exact (Finset.univ : Finset (Fin q)).powerset.filter
    (fun J => J.card ≤ 8 ∧ ε < projectionTV ρ μ draw J)

theorem mem_badCoordinateSets_iff
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ) (J : Finset (Fin q)) :
    J ∈ badCoordinateSets ρ μ draw ε ↔
      J.card ≤ 8 ∧ ε < projectionTV ρ μ draw J := by
  classical
  simp [badCoordinateSets]

theorem badCoordinateSets_nonempty
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ J ∈ badCoordinateSets ρ μ draw ε, J.Nonempty := by
  apply bad_family_nonempty_of_zero_empty
    (badCoordinateSets ρ μ draw ε) (projectionTV ρ μ draw) ε hε
    (projectionTV_empty ρ μ draw)
  intro J hJ
  exact (mem_badCoordinateSets_iff ρ μ draw ε J).mp hJ |>.2

theorem badCoordinateSets_witness
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (J : Finset (Fin q)) (hJ : J ∈ badCoordinateSets ρ μ draw ε) :
    ∃ A : Finset (J → Z),
      ε < projectionEventDifference ρ μ draw J A := by
  exact projectionTV_witness ρ μ draw J ε
    ((mem_badCoordinateSets_iff ρ μ draw ε J).mp hJ).2

/-- Finite event equality for every projection of at most `D` coordinates.
For an indexed source this is the exact bounded-independence input used in
`det:conditioning`; it compares the decoded law with the full product law. -/
def ExactlyKWiseIndependent
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ν : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (D : ℕ) : Prop :=
  ∀ J : Finset (Fin q), J.card ≤ D → ∀ A : Finset (J → Z),
    ν.prob (fun ω => projection draw J ω ∈ A) =
      (μ.iid q).prob (fun z => projection id J z ∈ A)

theorem expectation_indicator_eq_prob
    {Ω : Type*} [Fintype Ω] (ν : Paper2.FiniteLaw Ω)
    (P : Ω → Bool) :
    expectation ν (fun ω => if P ω then (1 : ℝ) else 0) =
      ν.prob (fun ω => P ω) := by
  classical
  unfold expectation Paper2.FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro ω _
  cases hP : P ω <;> simp [hP]

/-- One event witnessing badness is chosen for each bad set. No desired
probability or exceptional-set conclusion is hidden in this choice. -/
noncomputable def chosenBadEvent
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ) (J : Finset (Fin q)) :
    Finset (J → Z) := by
  classical
  exact if hJ : J ∈ badCoordinateSets ρ μ draw ε then
    Classical.choose (badCoordinateSets_witness ρ μ draw ε J hJ)
  else ∅

theorem chosenBadEvent_witness
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (J : Finset (Fin q)) (hJ : J ∈ badCoordinateSets ρ μ draw ε) :
    ε < projectionEventDifference ρ μ draw J
      (chosenBadEvent ρ μ draw ε J) := by
  classical
  unfold chosenBadEvent
  simp only [dif_pos hJ]
  exact Classical.choose_spec (badCoordinateSets_witness ρ μ draw ε J hJ)

/-- The paper fixes `R=1024` and `D=8R=8192`. -/
noncomputable def conditioningEpsilon (v τ : ℝ) : ℝ :=
  min τ (((2 : ℝ) ^ (-(20 : ℝ))) / 1024 * v ^ ((4 : ℝ) / 1024))

theorem conditioningEpsilon_pos {v τ : ℝ} (hv : 0 < v) (hτ : 0 < τ) :
    0 < conditioningEpsilon v τ := by
  unfold conditioningEpsilon
  exact lt_min hτ (mul_pos
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num))
    (Real.rpow_pos_of_pos hv _))

noncomputable def conditioningExceptionCount (v τ : ℝ) : ℕ :=
  8 * ⌈(1024 : ℝ) * (conditioningEpsilon v τ) ^ (-(2 : ℝ)) *
    v ^ (-(2 / (1024 : ℝ)))⌉₊

/-- The Boolean test on the selected bad set indexed by `i`. -/
noncomputable def selectedBadTest
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (F : Finset (Finset (Fin q))) (i : Fin F.card) (ω : Ω) : Bool := by
  classical
  let J : Finset (Fin q) := ((F.equivFin).symm i).1
  exact decide (projection draw J ω ∈ chosenBadEvent ρ μ draw ε J)

/-- Sum of the selected tests after subtracting their expectations under the
original, unconditioned indexed law. -/
noncomputable def centeredBadSum
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ν ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (F : Finset (Finset (Fin q))) (ω : Ω) : ℝ :=
  ∑ i : Fin F.card,
    ((if selectedBadTest ρ μ draw ε F i ω then (1 : ℝ) else 0) -
      expectation ν (fun ω' =>
        if selectedBadTest ρ μ draw ε F i ω' then (1 : ℝ) else 0))

private theorem selectedBadTest_prob
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (σ ρ : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (F : Finset (Finset (Fin q))) (i : Fin F.card) :
    expectation σ (fun ω =>
      if selectedBadTest ρ μ draw ε F i ω then (1 : ℝ) else 0) =
      σ.prob (fun ω =>
        projection draw (((F.equivFin).symm i).1) ω ∈
          chosenBadEvent ρ μ draw ε (((F.equivFin).symm i).1)) := by
  classical
  rw [expectation_indicator_eq_prob]
  simp [selectedBadTest]

/-- An actual TV violation yields a centered Boolean test with the
conditional/unconditional expectation gap required by the moment count. -/
theorem selectedBadTest_discrepancy
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ν : Paper2.FiniteLaw Ω) (Y : Ω → Prop)
    (hY : 0 < ν.prob Y) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (hind : ExactlyKWiseIndependent ν μ draw 8192)
    (F : Finset (Finset (Fin q)))
    (hF : F ⊆ badCoordinateSets (condition ν Y hY) μ draw ε)
    (i : Fin F.card) :
    ε < expectation (condition ν Y hY)
        (fun ω => if selectedBadTest (condition ν Y hY) μ draw ε F i ω
          then (1 : ℝ) else 0) -
      expectation ν
        (fun ω => if selectedBadTest (condition ν Y hY) μ draw ε F i ω
          then (1 : ℝ) else 0) := by
  classical
  let J : Finset (Fin q) := ((F.equivFin).symm i).1
  have hJF : J ∈ F := ((F.equivFin).symm i).2
  have hJbad := hF hJF
  have hJsize : J.card ≤ 8 :=
    ((mem_badCoordinateSets_iff (condition ν Y hY) μ draw ε J).mp hJbad).1
  have hJwide : J.card ≤ 8192 := by omega
  have hW := chosenBadEvent_witness (condition ν Y hY) μ draw ε J hJbad
  have hindJ := hind J hJwide (chosenBadEvent (condition ν Y hY) μ draw ε J)
  have hρ := selectedBadTest_prob (condition ν Y hY)
    (condition ν Y hY) μ draw ε F i
  have hν := selectedBadTest_prob ν (condition ν Y hY) μ draw ε F i
  change ε < _ - _
  rw [hρ, hν]
  change ε < (condition ν Y hY).prob
      (fun ω => projection draw J ω ∈ chosenBadEvent (condition ν Y hY) μ draw ε J) -
    ν.prob
      (fun ω => projection draw J ω ∈ chosenBadEvent (condition ν Y hY) μ draw ε J)
  rw [hindJ]
  exact hW

/-- Conditional `det:conditioning` endpoint. The sole unfinished analytic
premise is `hEvenMoment`: the manuscript derives it from exact 8192-wise
independence and the order-1024 bounded-variable moment estimate. It is
stated on the **actual selected witness sum**, not on an arbitrary claimed
exceptional set or on a pre-assumed packing bound. -/
theorem conditioning_exceptional_coordinates_of_even_moment
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ν : Paper2.FiniteLaw Ω) (μ : Paper2.FiniteLaw Z)
    (draw : Ω → Fin q → Z) (Y : Ω → Prop)
    (v τ : ℝ) (hv : 0 < v) (hvY : v ≤ ν.prob Y) (hτ : 0 < τ)
    (hind : ExactlyKWiseIndependent ν μ draw 8192)
    (hEvenMoment : ∀ F : Finset (Finset (Fin q)),
      F ⊆ badCoordinateSets (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw
        (conditioningEpsilon v τ) →
      (F : Set (Finset (Fin q))).Pairwise Disjoint → 0 < F.card →
      expectation ν (fun ω =>
        |centeredBadSum ν (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw
          (conditioningEpsilon v τ) F ω| ^ (1024 : ℝ)) ≤
        2 * ((1024 : ℝ) * F.card / 4) ^ ((1024 : ℝ) / 2)) :
    ∃ E : Finset (Fin q), E.card ≤ conditioningExceptionCount v τ ∧
      ∀ J : Finset (Fin q),
        J ⊆ (Finset.univ : Finset (Fin q)) \ E → J.card ≤ 8 →
          projectionTV (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw J ≤
            conditioningEpsilon v τ := by
  classical
  let hY : 0 < ν.prob Y := lt_of_lt_of_le hv hvY
  let ρ := condition ν Y hY
  let ε := conditioningEpsilon v τ
  let bad := badCoordinateSets ρ μ draw ε
  have hε : 0 < ε := conditioningEpsilon_pos hv hτ
  have hnonempty : ∀ J ∈ bad, J.Nonempty :=
    badCoordinateSets_nonempty ρ μ draw ε hε.le
  have hsize : ∀ J ∈ bad, J.card ≤ 8 := by
    intro J hJ
    exact ((mem_badCoordinateSets_iff ρ μ draw ε J).mp hJ).1
  let B : ℝ := (1024 : ℝ) * ε ^ (-(2 : ℝ)) *
    v ^ (-(2 / (1024 : ℝ)))
  have hpacking : ∀ F : Finset (Finset (Fin q)), F ⊆ bad →
      (F : Set (Finset (Fin q))).Pairwise Disjoint → (F.card : ℝ) ≤ B := by
    intro F hF hpair
    by_cases hm : 0 < F.card
    · let test : Fin F.card → Ω → Bool := selectedBadTest ρ μ draw ε F
      have hdisc : ∀ i : Fin F.card,
          ε < expectation ρ (fun ω => if test i ω then (1 : ℝ) else 0) -
            expectation ν (fun ω => if test i ω then (1 : ℝ) else 0) := by
        intro i
        exact selectedBadTest_discrepancy ν Y hY μ draw ε hind F hF i
      have hmean : (F.card : ℝ) * ε <
          expectation ρ (centeredBadSum ν ρ μ draw ε F) := by
        exact centered_indicator_sum_large_mean ν Y hY F.card hm test ε hdisc
      have hM := hEvenMoment F hF hpair hm
      have hcount := witness_count_lt_mass_lower_bound ν Y v hv hvY
        (centeredBadSum ν ρ μ draw ε F) (1024 : ℝ) (by norm_num)
        F.card hm ε hε hmean hM
      exact hcount.le
    · have hzero : F.card = 0 := by omega
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      simpa [hzero] using hB
  obtain ⟨E, hEcard, hcover⟩ :=
    finite_exceptional_cover_ceiling bad B hnonempty hsize hpacking
  refine ⟨E, ?_, ?_⟩
  · simpa [conditioningExceptionCount, B, ε] using hEcard
  · intro J hJremaining hJsize
    by_contra hgood
    have hJbad : J ∈ bad :=
      (mem_badCoordinateSets_iff ρ μ draw ε J).mpr
        ⟨hJsize, lt_of_not_ge hgood⟩
    exact (no_bad_subset_complement hcover hJremaining) hJbad

#print axioms projectionTV_empty
#print axioms badCoordinateSets_nonempty
#print axioms selectedBadTest_discrepancy
#print axioms conditioning_exceptional_coordinates_of_even_moment

end CurrentAdditive
