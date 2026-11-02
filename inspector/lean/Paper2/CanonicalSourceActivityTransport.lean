import Paper2.CanonicalSourceLabels
import Paper2.SourceSuccessorConjugacy

/-!
# Relating canonical coordinates to the existing source construction

Frozen v12 Section 4 and Appendix D: this supplies the exact coordinate
permutation required to use the already proved recursive conjugacy. It
does not identify the canonical enumeration with `Fintype.equivOfCardEq`.
The activity below still uses the proof-side ordered active rank; its
bounded-scan implementation is a separate obligation.
-/

namespace Paper2.CanonicalSourceActivityTransport

open SourceMatrix SourceCoordinateConjugacy SourceSuccessorConjugacy

variable {s n m rep q₂ : ℕ} [NeZero s]

/-- New numeric coordinate to old numeric coordinate. This map is used
only in the proof correspondence, not by the executable enumeration. -/
noncomputable def coordinatePermutation
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep) :
    Fin q₂ ≃ Fin q₂ :=
  (CanonicalSourceLabels.coordOrder s m rep q₂ hq).trans
    (SourceConstruction.coordinateEquiv rep hq).symm

noncomputable def canonicalActivity (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep) :
    SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s) :=
  fun i α => SourceConstruction.orderedActivity
    (CanonicalSourceLabels.itemOrder s n) edge hs rep i
    (CanonicalSourceLabels.coordOrder s m rep q₂ hq α)

theorem canonicalActivity_eq (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep) :
    canonicalActivity edge hs hq =
      activityNew (coordinatePermutation hq)
        (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
          edge hs rep hq) := by
  funext i α
  simp only [canonicalActivity, activityNew, SourceConstruction.activity,
    coordinatePermutation, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The same full-product iteration on canonical coordinates, after the
explicit carrier and tail transport, has the original matrix entries. -/
theorem canonical_matrix_map {X Y : Type} {q₁ w Q : ℕ}
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (F : X → Y → Bool)
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q) (k : ℕ)
    (x : RecursiveEntries.Row X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k)
    (y : RecursiveEntries.Column X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k) :
    RecursiveEntries.matrix F (canonicalActivity edge hs hq)
      (tailsMap (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y) ξ) k
      ((carrierEquivs (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y) k).1 x)
      ((carrierEquivs (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y) k).2 y) =
    RecursiveEntries.matrix F
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n) edge hs rep hq)
      ξ k x y := by
  rw [canonicalActivity_eq]
  exact matrix_map (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y)
    F F (fun _ _ => rfl) _ ξ k x y

#print axioms canonicalActivity_eq
#print axioms canonical_matrix_map

end Paper2.CanonicalSourceActivityTransport
