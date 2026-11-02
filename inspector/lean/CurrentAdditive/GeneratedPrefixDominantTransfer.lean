import CurrentAdditive.GeneratedShortProtocol
import CurrentAdditive.GeneratedSeparationNumeric

/-!
The generated separation theorem labels dominant template mass through its
retained-row representative map.  On a genuinely retained template row that
representative is the original row, so its prefix code is the row code used
by the graph collision partition.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceProtocolPrefix
open Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ t : ℕ} [NeZero (2^t)] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := 2^t) μX μY)

theorem dominant_mass_on_actual_rowCode
    (V : Set (Row (I := I) src)) (U : Set (Column src))
    (P : Protocol V U Bool)
    (Φ : (Fin (2^t) × src.inner.Label) → V)
    (hΦ : ∀ p z (h : (Sum.inl (p,z) : Row (I := I) src) ∈ V),
      Φ (p,z) = ⟨.inl (p,z),h⟩)
    (dom : Fin (2^t) ≃ Fin (2^t))
    (hdom : ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (fun z =>
        (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
        NPCC.Protocol.prefixCodeRaw t P (Φ (dom j,z)) = j)) :
    ∀ j, (998/1000 : ℝ) <
      src.inner.law.toFiniteLaw.prob (fun z =>
        (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
        rowCode V P t (Sum.inl (dom j,z)) = j) := by
  intro j
  have hevent : (fun z : src.inner.Label =>
      (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
      NPCC.Protocol.prefixCodeRaw t P (Φ (dom j,z)) = j) =
    (fun z =>
      (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
      rowCode V P t (Sum.inl (dom j,z)) = j) := by
    funext z
    apply propext
    by_cases hz : (Sum.inl (dom j,z) : Row (I := I) src) ∈ V
    · simp only [hz, true_and]
      rw [hΦ (dom j) z hz]
      simp only [rowCode, dif_pos hz]
    · simp only [hz, false_and]
  simpa only [hevent] using hdom j

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.dominant_mass_on_actual_rowCode
