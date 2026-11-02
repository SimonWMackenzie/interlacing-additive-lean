import CurrentAdditive.DeterministicIndexedMatrix
import CurrentAdditive.PairwiseMissedEvents

/-!
Pairwise missed-event independence for the *actual* indexed inner source.
This is the distributional input to v27 `det:near-full`'s coordinate-defect
count. Only two selected distinct source coordinates are used.
-/

namespace CurrentAdditive.GeneratedPairwiseMissedEvents

open Paper2 Paper2.FiniteLaw
attribute [local instance] Classical.propDecidable

variable {ι A Ω : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype Ω]

/-- Distinct decoded coordinates have the exact product law for arbitrary
events, as a direct consequence of the indexed two-wise source statement. -/
theorem dwise_pair_event (D : ℕ) (ν : FiniteLaw Ω)
    (decode : Ω → ι → A) (μ : FiniteLaw A)
    (hD : 2 ≤ D) (hwise : IsDWise D ν decode μ)
    (i j : ι) (hij : i ≠ j) (E F : A → Prop) :
    ν.prob (fun z => E (decode z i) ∧ F (decode z j)) =
      μ.prob E * μ.prob F := by
  classical
  let S : Finset ι := {i, j}
  have hi : i ∈ S := by simp [S]
  have hj : j ∈ S := by simp [S]
  have hcard : S.card ≤ D := by
    simpa [S, hij] using hD
  let G : S → A → Prop := fun p a => if p.val = i then E a else F a
  have hevent (x : S → A) :
      (∀ p : S, G p (x p)) ↔
        E (x ⟨i, hi⟩) ∧ F (x ⟨j, hj⟩) := by
    constructor
    · intro h
      constructor
      · simpa [G] using h ⟨i, hi⟩
      · simpa [G, hij.symm] using h ⟨j, hj⟩
    · rintro ⟨hE, hF⟩ p
      have hp : p.val = i ∨ p.val = j := by
        have hp' : p.val ∈ insert i ({j} : Finset ι) := p.property
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hp'
      rcases hp with hp | hp
      · have hpeq : p = ⟨i, hi⟩ := Subtype.ext hp
        subst p
        simpa [G] using hE
      · have hpeq : p = ⟨j, hj⟩ := Subtype.ext hp
        subst p
        simpa [G, hij.symm] using hF
  have hprod :
      (FiniteLaw.pi (fun _ : S => μ)).prob
          (fun x => ∀ p : S, G p (x p)) =
        μ.prob E * μ.prob F := by
    rw [FiniteLaw.pi_prob_coordinatewise]
    simp only [G]
    have hpoint (p : S) :
        μ.prob (fun a => if p.val = i then E a else F a) =
          if p.val = i then μ.prob E else μ.prob F := by
      by_cases hp : p.val = i <;> simp [hp]
    simp_rw [hpoint]
    rw [← Finset.prod_subtype S (by intro x; rfl)
      (fun a => if a = i then μ.prob E else μ.prob F)]
    simp [S, hij, hij.symm]
  calc
    ν.prob (fun z => E (decode z i) ∧ F (decode z j)) =
      ν.prob (fun z => ∀ p : S, G p (decode z p.val)) := by
        congr 1
        funext z
        exact propext (hevent (fun p => decode z p.val)).symm
    _ = (FiniteLaw.pi (fun _ : S => μ)).prob
        (fun x => ∀ p : S, G p (x p)) := by
          exact hwise S hcard (fun x : S → A => ∀ p : S, G p (x p))
    _ = _ := hprod

/-- The exact one-coordinate marginal used to turn the second-moment
denominator into the paper's explicit missed-event masses. -/
theorem dwise_single_event (D : ℕ) (ν : FiniteLaw Ω)
    (decode : Ω → ι → A) (μ : FiniteLaw A)
    (hD : 1 ≤ D) (hwise : IsDWise D ν decode μ)
    (i : ι) (E : A → Prop) :
    ν.prob (fun z => E (decode z i)) = μ.prob E := by
  classical
  let S : Finset ι := {i}
  have hi : i ∈ S := by simp [S]
  have hcard : S.card ≤ D := by simpa [S] using hD
  have hsource := hwise S hcard (fun x : S → A => E (x ⟨i, hi⟩))
  have hproduct :
      (FiniteLaw.pi (fun _ : S => μ)).prob
        (fun x => E (x ⟨i, hi⟩)) = μ.prob E := by
    have hpredicate (x : S → A) :
        E (x ⟨i, hi⟩) ↔ ∀ p : S, E (x p) := by
      constructor
      · intro h p
        have hp' : p.val ∈ ({i} : Finset ι) := p.property
        have hp : p = ⟨i, hi⟩ := Subtype.ext (Finset.mem_singleton.mp hp')
        simpa [hp] using h
      · intro h
        exact h ⟨i, hi⟩
    calc
      _ = (FiniteLaw.pi (fun _ : S => μ)).prob
          (fun x => ∀ p : S, E (x p)) := by
            congr 1; funext x; exact propext (hpredicate x)
      _ = ∏ _p : S, μ.prob E := FiniteLaw.pi_prob_coordinatewise _ _
      _ = μ.prob E := by simp [S]
  calc
    ν.prob (fun z => E (decode z i)) =
      ν.prob (fun z => E ((fun p : S => decode z p.val) ⟨i, hi⟩)) := rfl
    _ = (FiniteLaw.pi (fun _ : S => μ)).prob
        (fun x => E (x ⟨i, hi⟩)) := hsource
    _ = μ.prob E := hproduct

end CurrentAdditive.GeneratedPairwiseMissedEvents

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- For actual generated inner labels, every retained event avoiding a list
of missed coordinate events has the pairwise second-moment mass bound. The
list uses distinct *indices*, even if decoded values happen to coincide. -/
theorem inner_avoid_mass_le
    (hD : 2 ≤ D) (m : ℕ) (e : Fin m → Fin q₂)
    (he : Function.Injective e)
    (E : Fin m → (Fin q₁ × X) → Prop)
    (K : Set src.inner.Label)
    (hK : ∀ z ∈ K, ∀ k : Fin m,
      ¬ E k (src.inner.decode z (e k)))
    (hM : 0 < ∑ k : Fin m,
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob (E k)) :
    src.inner.law.toFiniteLaw.prob (· ∈ K) ≤
      1 / (∑ k : Fin m,
        ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob (E k)) := by
  let ν := src.inner.law.toFiniteLaw
  let μ := ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
  let F : Fin m → src.inner.Label → Prop :=
    fun k z => E k (src.inner.decode z (e k))
  have hsingle (k : Fin m) : ν.prob (F k) = μ.prob (E k) :=
    GeneratedPairwiseMissedEvents.dwise_single_event D ν src.inner.decode μ
      (by omega) src.inner.exactLaw (e k) (E k)
  have hpair (i j : Fin m) (hij : i ≠ j) :
      ν.prob (fun z => F i z ∧ F j z) =
        ν.prob (F i) * ν.prob (F j) := by
    rw [hsingle i, hsingle j]
    exact GeneratedPairwiseMissedEvents.dwise_pair_event D ν src.inner.decode μ
      hD src.inner.exactLaw (e i) (e j) (fun h => hij (he h)) (E i) (E j)
  have hM' : 0 < ∑ k : Fin m, ν.prob (F k) := by
    simpa only [hsingle] using hM
  have hbound := PairwiseMissedEvents.avoid_mass_le_of_pairwise ν m F
    (· ∈ K) hpair (by intro z hz k; exact hK z hz k) hM'
  simpa only [hsingle] using hbound

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.GeneratedPairwiseMissedEvents.dwise_pair_event
#print axioms CurrentAdditive.GeneratedPairwiseMissedEvents.dwise_single_event
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.inner_avoid_mass_le
