import CurrentAdditive.IndexedIncomingDensity
import CurrentAdditive.IndexedSelectorFlat

/-! The chosen protected type has a large image in the original J₂ law at
each fixed template bin. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

private theorem outer_coordinate_pushes (hD : 1 ≤ D) (p : Fin s)
    (E : J src → Prop) :
    src.outer.law.toFiniteLaw.prob
      (fun js => E (src.outer.decode js p)) =
      (diagonalLaw src).toFiniteLaw.prob E := by
  classical
  let S : Finset (Fin s) := {p}
  let pS : S := ⟨p, by simp [S]⟩
  have hS : S.card ≤ D := by simpa [S] using hD
  have hsource := src.outer.exactLaw S hS (fun f : S → J src => E (f pS))
  rw [hsource]
  have huniq (i : S) : i = pS := by
    rcases i with ⟨i, hi⟩
    apply Subtype.ext
    exact Finset.mem_singleton.mp hi
  have hev : (fun f : S → J src => E (f pS)) =
      (fun f => ∀ i : S, (if i = pS then E (f i) else True)) := by
    funext f
    apply propext
    simp [huniq]
  rw [hev]
  have hpi := FiniteLaw.pi_prob_coordinatewise
    (fun _ : S => (diagonalLaw src).toFiniteLaw)
    (fun i a => if i = pS then E a else True)
  change (FiniteLaw.pi (fun _ : S => (diagonalLaw src).toFiniteLaw)).prob
    (fun f => ∀ i : S, if i = pS then E (f i) else True) = _
  rw [hpi]
  have huniv : (Finset.univ : Finset S) = {pS} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact huniq i
  change (Finset.univ : Finset S).prod
    (fun i => (diagonalLaw src).toFiniteLaw.prob
      (fun a => if i = pS then E a else True)) =
    (diagonalLaw src).toFiniteLaw.prob E
  rw [huniv]
  simp

/-- The exact set of J₂ labels exposed by the incoming protected rows at
one original position and one fixed template bin. -/
def protectedImage (w : ℕ) (R : Set (Fin w × Column src))
    (b : Bool) (i : Fin w) (p : Fin s) : Set (J src) :=
  fun j => if b then (i, Column.diagonal j) ∈ R else
    ∃ js : src.outer.Label,
      (i, Column.fixedTail js) ∈ R ∧ src.outer.decode js p = j

/-- The image has at least the actual protected conditional density; for
diagonal rows this is equality, while fixed-tail rows use one exact outer
source coordinate. -/
theorem protected_image_mass_ge (w : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w))
    (b : Bool) (i : Fin w) (hi : i ∈ I) (p : Fin s)
    (hD : 1 ≤ D) :
    protectedDensity src w R I b i ≤
      (diagonalLaw src).toFiniteLaw.prob
        (fun j => j ∈ protectedImage src w R b i p) := by
  cases b with
  | true =>
      simp only [protectedDensity, hi, ite_true, protectedImage]
      exact le_refl _
  | false =>
      simp only [protectedDensity, hi, ite_true, Bool.false_eq_true, ite_false]
      rw [← outer_coordinate_pushes src hD p]
      apply FiniteLaw.prob_mono
      intro js hjs
      exact ⟨js, hjs, rfl⟩

#print axioms protected_image_mass_ge

end CurrentAdditive.DeterministicIndexedMatrix.Sources
