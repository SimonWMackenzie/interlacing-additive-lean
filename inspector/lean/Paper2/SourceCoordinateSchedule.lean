import Paper2.SourceRepetition
import Paper2.SourceDensitySchedule

/-!
Deriving the first two v12 coordinate admissibility checks from the
actual indexed graph and the public dyadic widths.
-/

namespace Paper2.SourceCoordinateScheduleScratch

open SourceProfileParameters SourceRepetitionScratch SourceDensityScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- The first displayed admissibility check, with no cardinality estimate
supplied by the caller. -/
theorem coordinate_admissible (edge : E → Bool → V) (L Delta : ℕ)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta)
    (hsize : Fintype.card V ≤ 2 ^ L)
    (hwidth : 6 * Delta ≤ width L) :
    SourceRepetitionScratch.coordinateAdmissible L E := by
  have hdeg := twice_edges_le_degree_vertices edge Delta hdegree
  have hraw : 12 * width L * Fintype.card E ≤ outerWidth L := by
    calc
      12 * width L * Fintype.card E =
          (6 * width L) * (2 * Fintype.card E) := by ring
      _ ≤ (6 * width L) * (Delta * Fintype.card V) :=
        Nat.mul_le_mul_left _ hdeg
      _ ≤ (6 * width L) * (Delta * 2 ^ L) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsize)
      _ = (6 * Delta) * (2 ^ L * width L) := by ring
      _ ≤ width L * (2 ^ L * width L) :=
        Nat.mul_le_mul_right _ hwidth
      _ = outerWidth L := by rw [outerWidth_eq]; ring
  have hexp : Nat.clog 2 (12 * width L * Fintype.card E) ≤
      outerExponent L := by
    apply Nat.clog_le_of_le_pow
    simpa only [outerWidth] using hraw
  unfold SourceRepetitionScratch.coordinateAdmissible SourcePadding.powTwoCeil
  change 2 ^ Nat.clog 2 (12 * width L * Fintype.card E) ≤
    2 ^ outerExponent L
  exact pow_le_pow_right₀ (by omega) hexp

/-- Source repetition and the exact downstream factorization, derived
from the graph degree bound rather than an assumed coordinate check. -/
theorem source_rep_receipt (edge : E → Bool → V) (L Delta : ℕ)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta)
    (hsize : Fintype.card V ≤ 2 ^ L)
    (hwidth : 6 * Delta ≤ width L) :
    0 < SourceRepetitionScratch.sourceRep L E ∧
    outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E *
      SourceRepetitionScratch.sourceRep L E ∧
    Fintype.card (SourceItems.SourceCoord (Fin (4 * width L)) E
      (SourceRepetitionScratch.sourceRep L E)) = outerWidth L := by
  have h := coordinate_admissible edge L Delta hdegree hsize hwidth
  exact ⟨SourceRepetitionScratch.sourceRep_pos L E h,
    SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L E h,
    SourceRepetitionScratch.sourceCoord_schedule_card L E h⟩

/-- The second displayed admissibility check. `L ≥ 16` is the
manuscript's threshold, though the arithmetic uses only `s ≥ 4`. -/
theorem item_size_admissible (L : ℕ) (hL : 16 ≤ L)
    (n : ℕ) (hsize : n ≤ 2 ^ L) :
    2 * (n + width L - 3) ≤ outerWidth L := by
  let A := 2 ^ L
  let s := width L
  have hA : 1 ≤ A := by
    have hp : 0 < A := by unfold A; positivity
    omega
  have hs : 4 ≤ s := by
    have h := width_admissible L
    dsimp [s]
    omega
  have hsum : n + s ≤ A * (1 + s) := by
    have hmul : s ≤ A * s := by
      calc
        s = 1 * s := by omega
        _ ≤ A * s := Nat.mul_le_mul_right s hA
    change n ≤ A at hsize
    calc
      n + s ≤ A + s := Nat.add_le_add_right hsize s
      _ ≤ A + A * s := Nat.add_le_add_left hmul A
      _ = A * (1 + s) := by ring
  have hquad : 2 * (1 + s) ≤ s ^ 2 := by nlinarith
  have hmain : 2 * (n + s) ≤ A * s ^ 2 := by
    calc
      2 * (n + s) ≤ 2 * (A * (1 + s)) := Nat.mul_le_mul_left _ hsum
      _ = A * (2 * (1 + s)) := by ring
      _ ≤ A * s ^ 2 := Nat.mul_le_mul_left _ hquad
  have hsub : 2 * (n + s - 3) ≤ 2 * (n + s) :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  calc
    _ ≤ 2 * (n + s) := hsub
    _ ≤ A * s ^ 2 := hmain
    _ = outerWidth L := by rw [outerWidth_eq]

#print axioms coordinate_admissible
#print axioms source_rep_receipt
#print axioms item_size_admissible

end Paper2.SourceCoordinateScheduleScratch
