import Paper2.ReferenceRunCorrectness

/-!
# Conservation of original row mass at physical destinations

Frozen v12 Section 5, final mass balance (lines 459--481). Every original
row follows exactly one Alice-prefix path. The equalities below hold for
the actual annotated runner and any fixed original population law, hence
also separately for each protected tag and source copy. They do not
assume a partition, and do not condition the law on the surviving rows.
-/

namespace Paper2.RestorationRowPartition

open ReferenceCertificateTree ReferenceCertificateProtocol
open scoped BigOperators

variable {A C I W Z : Type*} [Fintype W] [Fintype Z]

/-- Total incoming population mass equals its original retained mass. -/
theorem run_mass_partition (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (ν : FiniteLaw Z) (embed : Z → A) :
    let T := run μ input floor d fuel s
    (∑ v : T.Leaves, ν.prob (fun z => embed z ∈ (T.state v).rows)) =
      ν.prob (fun z => embed z ∈ s.rows) := by
  classical
  dsimp only
  unfold FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : embed z ∈ s.rows
  · have hmem (v : (run μ input floor d fuel s).Leaves) :
        embed z ∈ ((run μ input floor d fuel s).state v).rows ↔
          v = destination μ input floor d fuel s (embed z) :=
      rows_iff_destination μ input floor d fuel s (embed z) hz v
    simp only [hmem, hz, if_true]
    simp
  · have hmem (v : (run μ input floor d fuel s).Leaves) :
        embed z ∉ ((run μ input floor d fuel s).state v).rows :=
      fun h => hz (ReferenceRunCorrectness.rows_subset μ input floor d fuel s v h)
    simp [hmem, hz]

/-- The same equality restricted to any set of physical destinations. -/
theorem run_mass_in_destinations (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (ν : FiniteLaw Z) (embed : Z → A)
    (V : Finset (run μ input floor d fuel s).Leaves) :
    (∑ v ∈ V, ν.prob (fun z => embed z ∈
      ((run μ input floor d fuel s).state v).rows)) =
      ν.prob (fun z => embed z ∈ s.rows ∧
        destination μ input floor d fuel s (embed z) ∈ V) := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : embed z ∈ s.rows
  · have hmem (v : (run μ input floor d fuel s).Leaves) :
        embed z ∈ ((run μ input floor d fuel s).state v).rows ↔
          v = destination μ input floor d fuel s (embed z) :=
      rows_iff_destination μ input floor d fuel s (embed z) hz v
    simp only [hmem, hz, true_and]
    simp
  · have hmem (v : (run μ input floor d fuel s).Leaves) :
        embed z ∉ ((run μ input floor d fuel s).state v).rows :=
      fun h => hz (ReferenceRunCorrectness.rows_subset μ input floor d fuel s v h)
    simp [hmem, hz]

/-- Outgoing rows go either to another owner or a nonowner, never both.
The owner set here is any set of physical nodes; the source proof uses
the derived reference owners. No incoming upper bound is assumed. -/
theorem outgoing_owner_partition (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (ν : FiniteLaw Z) (embed : Z → A)
    (O : Finset (run μ input floor d fuel s).Leaves)
    (owner : (run μ input floor d fuel s).Leaves) (howner : owner ∈ O) :
    ν.prob (fun z => embed z ∈ s.rows ∧
      destination μ input floor d fuel s (embed z) ≠ owner) =
      (∑ v ∈ O.erase owner, ν.prob (fun z => embed z ∈
        ((run μ input floor d fuel s).state v).rows)) +
      (∑ v ∈ Finset.univ \ O, ν.prob (fun z => embed z ∈
        ((run μ input floor d fuel s).state v).rows)) := by
  classical
  rw [run_mass_in_destinations, run_mass_in_destinations]
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hr : embed z ∈ s.rows
  · by_cases he : destination μ input floor d fuel s (embed z) = owner
    · simp [hr, he, howner]
    · by_cases ho : destination μ input floor d fuel s (embed z) ∈ O <;>
        simp [hr, he, ho]
  · simp [hr]

end Paper2.RestorationRowPartition

#print axioms Paper2.RestorationRowPartition.run_mass_partition
#print axioms Paper2.RestorationRowPartition.run_mass_in_destinations
#print axioms Paper2.RestorationRowPartition.outgoing_owner_partition
