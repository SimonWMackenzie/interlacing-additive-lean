import CurrentAdditive.QuarticActualLarge

open _root_.CurrentAdditive.Eventual

/-!
# Square power-of-two output of the same v27 selected table

The square word repeats the selected table's rows and columns. Its decoded
communication cost is the same, and its printed length is tape-independent.
The estimator guarantee is required only on sufficiently large square words.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem classifier_square_tape_length_constant27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (E : SelectedTape.Algorithm) :
    let o := select27 hn edge Δ γ k
    let q := SquarePadding.side o.rows o.cols
    let s := (HeaderStrip.selectedClassifier E).cR *
      ((natField (2 * o.budget + k)).length +
        2 * (natField q).length + q * q + 1) ^
          (HeaderStrip.selectedClassifier E).dR
    ∀ t : o.Tape,
      (HeaderStrip.selectedClassifier E).tapeLength
        (natField (2 * o.budget + k) ++ squareWord27 hn edge Δ γ k t) = s := by
  intro o q s t
  have hlen := MatrixMaterialization.rowMajor_length (ASquare.squareTable o t)
  simp only [SelectedTape.Algorithm.tapeLength, squareWord27,
    AModel.matrixWord, List.length_append]
  rw [hlen]
  dsimp only [s, q, o]
  ring

theorem actual_square_joint_at_large27
    (E : SelectedTape.Algorithm) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c)
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
      let q := SquarePadding.side exp.output.rows exp.output.cols
      let s := (HeaderStrip.selectedClassifier E).cR *
        ((natField (2 * exp.output.budget + k)).length +
          2 * (natField q).length + q * q + 1) ^
          (HeaderStrip.selectedClassifier E).dR
      (FiniteFallbackOutput.ThreeColourable edge →
        99 / 100 ≤ (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
          (HeaderStrip.selectedClassifier E).output
            (natField (2 * exp.output.budget + k) ++
              AModel.matrixWord q q
                (MatrixMaterialization.rowMajor
                  (ASquare.squareTable exp.output x.1)))
            (List.ofFn x.2) = [true])) ∧
      ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
          ((Finset.univ.filter (fun e =>
            colour (edge e false) = colour (edge e true))).card : ℝ)) →
        (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
          (HeaderStrip.selectedClassifier E).output
            (natField (2 * exp.output.budget + k) ++
              AModel.matrixWord q q
                (MatrixMaterialization.rowMajor
                  (ASquare.squareTable exp.output x.1)))
            (List.ofFn x.2) = [true]) ≤
          (1 / 2 : ℝ) ^ 11 + 1 / 100) ∧
      (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3 := by
  obtain ⟨Nc, hNc⟩ := square_classifier_at_large27 E c hc0 hc hE Δ p hΔ γ hγ
  refine ⟨max Nc 36, ?_⟩
  intro N hN n m hn edge hloop hincident hdegree hNm hmn hexp k exp q s
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
          AModel.matrixWord q q
            (MatrixMaterialization.rowMajor
              (ASquare.squareTable exp.output t))) = s := by
    dsimp only [s, q]
    rw [hO]
    simpa only [squareWord27] using
      classifier_square_tape_length_constant27 hn edge Δ γ k E
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
            AModel.matrixWord q q
              (MatrixMaterialization.rowMajor
                (ASquare.squareTable exp.output t))) (· = [true])) ∧
      (exp.output.budget + k ≤ D (exp.output.table t).matrix →
        (HeaderStrip.selectedClassifier E).prob
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord q q
              (MatrixMaterialization.rowMajor
                (ASquare.squareTable exp.output t))) (· = [true]) ≤ 1 / 100) := by
    dsimp only [q]
    rw [hO]
    simpa only [squareWord27] using hper
  exact two_stage_classifier_error27 exp.tapeLaw s
    (fun t => natField (2 * exp.output.budget + k) ++
      AModel.matrixWord q q
        (MatrixMaterialization.rowMajor (ASquare.squareTable exp.output t)))
    E (FiniteFallbackOutput.ThreeColourable edge)
    (∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    (fun t => exp.output.budget + k ≤ D (exp.output.table t).matrix)
    hfixed (fun hy t => (hclass t).1 (hyes hy t)) hgood
    (fun _ t ht => (hclass t).2 ht)

#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.classifier_square_tape_length_constant27
#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.actual_square_joint_at_large27

end Paper2.CurrentAdditive.QuarticClassEndpoint
