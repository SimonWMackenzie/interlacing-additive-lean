import CurrentAdditive.QuarticSelectedUpper

namespace Paper2.CurrentAdditive.QuarticConstructor

open Workspace.Types.CommComplexity

/-- Exact finite guarantees of the single v27 public selector. -/
def Guarantees27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : Prop :=
  let o := select27 hn edge Δ γ k
  (∀ t : o.Tape, D (o.table t).matrix ≤ o.budget + k) ∧
  (FiniteFallbackOutput.ThreeColourable edge →
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget) ∧
  ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
    ((Finset.univ.filter (fun e => colour (edge e false) =
      colour (edge e true))).card : ℝ)) →
    1 - (1 / 2 : ℝ) ^ 11 ≤ successProbability27 hn edge Δ γ k) ∧
  (∀ t : o.Tape,
    (o.table t).bits.length = o.rows * o.cols ∧
    (o.tapeBits t).length = o.inputBits) ∧
  (experiment27 hn edge Δ γ k).output = o

theorem selected_finite_guarantees27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m) :
    Guarantees27 hn edge Δ γ k := by
  dsimp only [Guarantees27]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact selected_all_cost_le27 hn edge Δ γ k hk loopless hdegree hγ hΔ hm
  · intro hcolour
    exact selected_yes_cost_le27 hn edge Δ γ k loopless hdegree
      hγ hΔ hm hcolour
  · intro gap
    exact selected_no_success27 hn edge Δ γ k hk loopless hdegree
      hγ hΔ hm gap
  · exact select27_exact_lengths hn edge Δ γ k
  · exact experiment27_output_eq_select27 hn edge Δ γ k

#print axioms selected_finite_guarantees27

end Paper2.CurrentAdditive.QuarticConstructor
