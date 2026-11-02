import CurrentV43.TimeTradeoff.SourceCorrectness

/-! The nonnegativity of the effective error bound follows from the
accuracy premise itself. It is not an extra hypothesis of v43's implication. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open V39PermittedNumericalExtraction V39RandomEstimatorNormalization
open Workspace.Types.CommComplexity
open scoped Classical

 theorem error_nonnegative_of_probability {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (error : α → ℝ) (u : ℝ) (he : ∀ x,0 ≤ error x)
    (hp : (2:ℝ)/3 ≤ μ.prob (fun x=>error x ≤ u)) : 0 ≤ u := by
  by_contra hn
  have hevent:(fun x=>error x ≤ u)=(fun _=>False) := by
    funext x
    exact propext (iff_false_intro (fun h=>hn ((he x).trans h)))
  rw [hevent,FiniteLaw.prob_false] at hp
  norm_num at hp

 theorem randomized_error_nonnegative (A : PermittedEstimator)
    (a : ℕ → ℝ) (ha : Monotone a) (T₀ m S : ℕ)
    (hA : RandomizedSquareAccuracy A a T₀) (f : Fin m → Fin m → Bool)
    (hm : 0 < m) (hp : ∃ e,m=2^e) (hT : T₀ ≤ m^2) (hS : m^2 ≤ S) : 0 ≤ a S := by
  have h:=randomized_error_mono A a ha T₀ m S hA f hm hp hT hS
  exact error_nonnegative_of_probability _ _ (a S) (fun _=>abs_nonneg _) h

 theorem randomized_sample_error_nonnegative (A : PermittedEstimator)
    (a : ℕ → ℝ) (ha : Monotone a) (T₀ S L K : ℕ)
    (hA : RandomizedSquareAccuracy A a T₀)
    (hT : T₀ ≤ V42PublicSchedule.sampleEntries L K)
    (hS : V42PublicSchedule.sampleEntries L K ≤ S) : 0 ≤ a S :=
  randomized_error_nonnegative A a ha T₀ (V42PublicSchedule.sampleSide L K) S hA
    (fun _ _=>false) (V42RandomPermittedFamily.side_pos L K) ⟨_,rfl⟩ hT hS

 theorem randomized_stored_error_nonnegative (A : PermittedEstimator)
    (a : ℕ → ℝ) (ha : Monotone a) (T₀ S : ℕ)
    (hA : RandomizedSquareAccuracy A a T₀) (R : V39GeneratedConstruction.StoredMatrix)
    (hT : T₀ ≤ V42ActualLower.entryCount R)
    (hS : V42ActualLower.entryCount R ≤ S) : 0 ≤ a S :=
  randomized_error_nonnegative A a ha T₀ (SquarePadding.side R.rows R.cols) S hA
    R.square (SquarePadding.side_pos _ _) R.square_side_power hT hS

#print axioms randomized_error_nonnegative
#print axioms randomized_sample_error_nonnegative
#print axioms randomized_stored_error_nonnegative
end
end CurrentV43.TimeTradeoff
