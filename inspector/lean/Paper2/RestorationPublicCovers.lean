import Paper2.RestorationCovers
import Paper2.RestorationCoverParameters

/-!
# Restoration covers with the displayed public constants

Frozen v12 Section 5, equations `eq:projection-constants` and
`eq:exception-count`. The retained event is the same original iid-product
event throughout. All three strict power inequalities are derived here,
not requested as hypotheses. Constructing Q and eta from an encoded
source, and proving the later exceptional-mass checks, remain separate.
-/

namespace Paper2.RestorationPublicCovers

open RestorationCoverParameters RestorationCovers

noncomputable def e0 (Q : ℕ) (eta : ℝ) : ℕ :=
  exceptionBudget (B0 Q) (B1 Q eta) (B2 Q) (tExponent Q)

/-- The original event supplies the actual covers, with the public
power and ceiling choices rather than assumed projection properties. -/
theorem exists_cover {K : Type*} [Fintype K]
    (κ : FiniteLaw K) (w Q : ℕ) (hQ : 0 < Q)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (Y' : Set (Fin w → K)) (hY : theta Q ≤ (κ.iid w).prob (· ∈ Y')) :
    ∃ E0 : Finset (Fin w), E0.card ≤ e0 Q eta ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
        1 - eta ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (18 / 25 : ℝ) ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ j : Fin (tExponent Q - 2), ∀ S : Finset (Fin w),
        S.card = smallSize j.val → Disjoint S E0 →
          (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
            (fun _ => κ) (· ∈ Y') S) :=
  cover_three_families κ w (tExponent Q) (B0 Q) (B1 Q eta) (B2 Q)
    (tExponent_ge_two Q) (B0_pos Q) (B1_pos Q heta) (B2_pos Q)
    Y' (theta Q) eta hY (B0_gap hQ) (B1_gap hQ heta heta1) (B2_gap hQ)

end Paper2.RestorationPublicCovers

#print axioms Paper2.RestorationPublicCovers.exists_cover
