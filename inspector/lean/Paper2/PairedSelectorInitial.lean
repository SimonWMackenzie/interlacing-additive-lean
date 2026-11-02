import Paper2.PairedSelectorPopulation
import Paper2.PairedSelectorMatrixCore
import Paper2.PairedSupportFrontier
import Paper2.SourceSupportInitialCore

/-!
# Starting the actual paired-selector conversation

Frozen v12 Section 5, `res:paired`. The state uses the literal retained
ordinary and foreign columns. Extending a protocol to ambient columns is
only a carrier retraction: its depth and its values on retained inputs do
not change. Initial counts, support floors and reachability are derived
from these retained fibres, not assumed as a frontier certificate.
-/

namespace Paper2.PairedSelectorInitial

open PairedSelectorPopulation PairedSelectorMatrix PairedSupportFrontier
open Workspace.Types.Protocol

variable {W J A : Type*} [Fintype W] {q : ℕ}

noncomputable def initial (μ : FiniteLaw W)
    (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool) :
    State A (Column q W) (Fin q) W where
  protocol := SourceSupportInitial.extendColumns (columns O F) default P
  columns := columns O F
  singles := singles μ O F t
  pairs := pairs μ O F t
  support := support O F

theorem valid (μ : FiniteLaw W) (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool) :
    (initial μ O F t default P).Valid :=
  initial_valid μ O F t

theorem count (μ : FiniteLaw W) (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool) :
    (initial μ O F t default P).h + (bad μ O t).card = q := by
  simpa only [initial, State.h, Fintype.card_fin] using initial_count μ O F t

theorem floors (μ : FiniteLaw W) (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool) :
    ∀ a ∈ (initial μ O F t default P).blocks,
      t ≤ SourceSupportStep.mass μ ((initial μ O F t default P).support a) :=
  initial_floor μ O F t

theorem reaches (μ : FiniteLaw W) (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool) :
    ∀ a ∈ (initial μ O F t default P).blocks,
      ∀ w ∈ (initial μ O F t default P).support a,
        (a, w) ∈ (initial μ O F t default P).columns := by
  intro a _ w hw
  exact initial_reaches O F a w hw

theorem cost (μ : FiniteLaw W) (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool) :
    (initial μ O F t default P).protocol.cost = P.cost :=
  SourceSupportInitial.extendColumns_cost _ _ _

theorem computesOn (μ : FiniteLaw W) (O F : Set (Fin q × W)) (t : ℝ)
    (default : columns O F) (P : Protocol A (columns O F) Bool)
    (M : A → Column q W → Bool)
    (hP : P.Computes (fun a c => M a c.val)) :
    ∀ a c, c ∈ (initial μ O F t default P).columns →
      (initial μ O F t default P).protocol.eval a c = M a c :=
  SourceSupportInitial.extendColumns_computesOn _ _ _ M hP

/-- Positive retained foreign mass supplies a genuine column label for
the ambient-carrier retraction; no arbitrary default outside the domain. -/
theorem columns_nonempty [NeZero q] (μ : PositiveRationalLaw W)
    (O F : Set (Fin q × W)) (δ : ℝ) (hδ : 0 < δ)
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ F)) :
    (columns O F).Nonempty := by
  have hnon : F.Nonempty := by
    by_contra hn
    have he : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Set.mem_empty_iff_false, FiniteLaw.prob_false] at hF
    linarith
  obtain ⟨c, hc⟩ := hnon
  exact ⟨((true, c.1), c.2), hc⟩

end Paper2.PairedSelectorInitial
