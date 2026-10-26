import CurrentAdditive.QuarticActualJoint

/-!
# Actual-law v27 classifier at large source size

The statement uses the literal v27 selector, its own finite fair-bit law,
the eventual matrix-entry estimator domain, and the exact rectangular
matrix word. Its probability conclusion is source-promise conditional.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open _root_.CurrentAdditive.Eventual

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem actual_rectangular_joint_at_large27
    (E : SelectedTape.Algorithm) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c)
    (Δ p : ℕ) (hΔ : 0 < Δ) (γ : ℚ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ {n m : ℕ} (hn : 0 < n)
      (edge : Fin m → Bool → Fin n),
      (∀ e, edge e false ≠ edge e true) →
      (∀ v, ∃ e b, edge e b = v) →
      (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n →
      n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      let k := kOf N
      let exp := experiment27 hn edge Δ γ k
      letI : Fintype exp.output.Tape := exp.tapeFintype
      let s := (HeaderStrip.selectedClassifier E).cR *
        ((natField (2 * exp.output.budget + k)).length +
          (natField exp.output.rows).length +
          (natField exp.output.cols).length +
          exp.output.rows * exp.output.cols + 1) ^
          (HeaderStrip.selectedClassifier E).dR
      (FiniteFallbackOutput.ThreeColourable edge →
        99 / 100 ≤ (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
          (HeaderStrip.selectedClassifier E).output
            (natField (2 * exp.output.budget + k) ++
              AModel.matrixWord exp.output.rows exp.output.cols
                (exp.output.table x.1).bits) (List.ofFn x.2) = [true])) ∧
      ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
          ((Finset.univ.filter (fun e =>
            colour (edge e false) = colour (edge e true))).card : ℝ)) →
        (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
          (HeaderStrip.selectedClassifier E).output
            (natField (2 * exp.output.budget + k) ++
              AModel.matrixWord exp.output.rows exp.output.cols
                (exp.output.table x.1).bits) (List.ofFn x.2) = [true]) ≤
          (1 / 2 : ℝ) ^ 11 + 1 / 100) ∧
      (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3 := by
  obtain ⟨Nc, hNc⟩ := rectangular_classifier_at_large27 E c hc0 hc hE Δ p hΔ γ hγ
  refine ⟨max Nc 36, ?_⟩
  intro N hN n m hn edge hloop hincident hdegree hNm hmn hexp k exp s
  have hNcN : Nc ≤ N := (le_max_left _ _).trans hN
  have h36 : 36 ≤ N := (le_max_right _ _).trans hN
  have hk : 1 ≤ kOf N := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  have hm : 0 < m := by omega
  letI : Fintype exp.output.Tape := exp.tapeFintype
  have hO : exp.output = select27 hn edge Δ γ k :=
    experiment27_output_eq_select27 hn edge Δ γ k
  have hfinite := selected_finite_guarantees27 hn edge Δ γ k
    hk hloop hdegree hγ hΔ hm
  have hper := hNc N hNcN hn edge hincident hdegree hNm hmn hexp
  have hfixed : ∀ t : exp.output.Tape,
      (HeaderStrip.selectedClassifier E).tapeLength
        (natField (2 * exp.output.budget + k) ++
          AModel.matrixWord exp.output.rows exp.output.cols
            (exp.output.table t).bits) = s := by
    dsimp only [s]
    rw [hO]
    simpa only [matrixWord27] using
      classifier_tape_length_constant27 hn edge Δ γ k E
  have hyes : FiniteFallbackOutput.ThreeColourable edge →
      ∀ t : exp.output.Tape,
        D (exp.output.table t).matrix ≤ exp.output.budget := by
    rw [hO]
    exact hfinite.2.1
  have hgood :
      (∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
        ((Finset.univ.filter (fun e =>
          colour (edge e false) = colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
        exp.output.budget + k ≤ D (exp.output.table t).matrix) := by
    intro gap
    exact selected_no_mass27 hn edge Δ γ k hk hloop hdegree hγ hΔ hm gap
  have hclass : ∀ t : exp.output.Tape,
      (D (exp.output.table t).matrix ≤ exp.output.budget →
        99 / 100 ≤ (HeaderStrip.selectedClassifier E).prob
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord exp.output.rows exp.output.cols
              (exp.output.table t).bits) (· = [true])) ∧
      (exp.output.budget + k ≤ D (exp.output.table t).matrix →
        (HeaderStrip.selectedClassifier E).prob
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord exp.output.rows exp.output.cols
              (exp.output.table t).bits) (· = [true]) ≤ 1 / 100) := by
    rw [hO]
    simpa only [matrixWord27] using hper
  exact actual_joint_of_class_bias27 exp k E s
    (FiniteFallbackOutput.ThreeColourable edge)
    (∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    hfixed hyes hgood hclass

#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.actual_rectangular_joint_at_large27

end Paper2.CurrentAdditive.QuarticClassEndpoint
