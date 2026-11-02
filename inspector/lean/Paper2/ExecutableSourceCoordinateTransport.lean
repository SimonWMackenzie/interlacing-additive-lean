import Paper2.SourceActiveRank
import Paper2.CanonicalSourceActivityTransport

/-!
# Executable activity with an arbitrary canonical tail family

The scan is computational. The inverse permutation and inverse tail family
below are used only to apply the existing mathematical theorems; the
canonical construction does not need to compute either of them.
-/

namespace Paper2.ExecutableSourceCoordinateTransport

open SourceMatrix SourceSuccessorConjugacy CanonicalSourceActivityTransport

variable {s n m rep q₁ q₂ w Q : ℕ} [NeZero s] {X Y : Type}

theorem scan_eq_canonical (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep) :
    SourceActiveRank.scanAtCanonical edge hs hq = canonicalActivity edge hs hq := by
  funext i α
  exact SourceActiveRank.scanAtCanonical_eq_orderedActivity edge hs hq i α

/-- Proof-side old tails for any supplied canonical tail family. -/
noncomputable def oldTails
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q) :
    RecursiveEntries.Tails X Y (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q :=
  fun k t => ((carrierEquivs (coordinatePermutation hq)
    (Equiv.refl X) (Equiv.refl Y) k).2).symm (ξ k t)

theorem tailsMap_oldTails
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q) :
    tailsMap (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y)
      (oldTails hq ξ) = ξ := by
  funext k t
  exact ((carrierEquivs (coordinatePermutation hq)
    (Equiv.refl X) (Equiv.refl Y) k).2).apply_symm_apply (ξ k t)

/-- A directly scanned canonical construction, with any fixed tail family
chosen on its own labels, is the relabelled original iteration. -/
theorem scanned_matrix_map (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (F : X → Y → Bool)
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q) (k : ℕ)
    (x : RecursiveEntries.Row X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k)
    (y : RecursiveEntries.Column X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k) :
    RecursiveEntries.matrix F (SourceActiveRank.scanAtCanonical edge hs hq) ξ k
      ((carrierEquivs (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y) k).1 x)
      ((carrierEquivs (coordinatePermutation hq) (Equiv.refl X) (Equiv.refl Y) k).2 y) =
    RecursiveEntries.matrix F
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n) edge hs rep hq)
      (oldTails hq ξ) k x y := by
  have h := canonical_matrix_map edge hs hq F (oldTails hq ξ) k x y
  rw [tailsMap_oldTails] at h
  rw [scan_eq_canonical]
  exact h

#print axioms scan_eq_canonical
#print axioms tailsMap_oldTails
#print axioms scanned_matrix_map

end Paper2.ExecutableSourceCoordinateTransport
