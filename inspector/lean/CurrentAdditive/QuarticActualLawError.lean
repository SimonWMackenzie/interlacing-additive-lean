import CurrentAdditive.QuarticPerGraphError

/-!
# The actual v27 selected-tape law

This replaces the abstract first-stage law of the per-graph probability
lemma by `experiment27.tapeLaw`. The estimator sees the table selected by the
same tape whose source success event is measured.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem selected_no_mass27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    let exp := experiment27 hn edge Δ γ k
    letI : Fintype exp.output.Tape := exp.tapeFintype
    1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
      exp.output.budget + k ≤ D (exp.output.table t).matrix) := by
  dsimp only
  let exp := experiment27 hn edge Δ γ k
  letI : Fintype exp.output.Tape := exp.tapeFintype
  have hfinite := selected_finite_guarantees27 hn edge Δ γ k
    hk loopless hdegree hγ hΔ hm
  have hmass : 1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
      D (exp.output.table t).matrix = exp.output.budget + k) := by
    exact hfinite.2.2.1 gap
  exact hmass.trans (exp.tapeLaw.prob_mono (fun t ht => by
    simp only [exp] at ht ⊢
    omega))

theorem classifier_tape_length_constant27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (E : SelectedTape.Algorithm) :
    let o := select27 hn edge Δ γ k
    let s := (HeaderStrip.selectedClassifier E).cR *
      ((natField (2 * o.budget + k)).length +
        (natField o.rows).length + (natField o.cols).length +
        o.rows * o.cols + 1) ^ (HeaderStrip.selectedClassifier E).dR
    ∀ t : o.Tape,
      (HeaderStrip.selectedClassifier E).tapeLength
        (natField (2 * o.budget + k) ++ matrixWord27 hn edge Δ γ k t) = s := by
  intro o s t
  have hbits := (select27_exact_lengths hn edge Δ γ k t).1
  simp only [SelectedTape.Algorithm.tapeLength, matrixWord27,
    AModel.matrixWord, List.length_append] at *
  rw [hbits]
  ring

#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.selected_no_mass27
#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.classifier_tape_length_constant27

end Paper2.CurrentAdditive.QuarticClassEndpoint
