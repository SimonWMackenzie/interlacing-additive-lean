import CurrentAdditive.QuarticJointError
import CurrentAdditive.QuarticSelectedFiniteGuarantees

/-!
# The v27 rectangular selected graph and estimator law

The source's selected table is used unchanged in the estimator word and
communication-cost event. This is the finite per-graph probability argument;
binding it to the source formula and a physical decider comes later.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open _root_.CurrentAdditive.Eventual

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem rectangular_joint_at_large27
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
      let o := select27 hn edge Δ γ k
      ∀ [Fintype o.Tape] (μ : FiniteLaw o.Tape) (s : ℕ),
        (∀ t : o.Tape,
          (HeaderStrip.selectedClassifier E).tapeLength
            (natField (2 * o.budget + k) ++ matrixWord27 hn edge Δ γ k t) = s) →
        ((∀ colour : Fin n → Fin 3,
            (γ : ℝ) * m ≤
              ((Finset.univ.filter (fun e =>
                colour (edge e false) = colour (edge e true))).card : ℝ)) →
          1 - (1 / 2 : ℝ) ^ 11 ≤
            μ.prob (fun t => o.budget + k ≤ D (o.table t).matrix)) →
        (FiniteFallbackOutput.ThreeColourable edge →
          99 / 100 ≤ (μ.prod (uniformTape s)).prob (fun x =>
            (HeaderStrip.selectedClassifier E).output
              (natField (2 * o.budget + k) ++
                matrixWord27 hn edge Δ γ k x.1) (List.ofFn x.2) = [true])) ∧
        ((∀ colour : Fin n → Fin 3,
            (γ : ℝ) * m ≤
              ((Finset.univ.filter (fun e =>
                colour (edge e false) = colour (edge e true))).card : ℝ)) →
          (μ.prod (uniformTape s)).prob (fun x =>
            (HeaderStrip.selectedClassifier E).output
              (natField (2 * o.budget + k) ++
                matrixWord27 hn edge Δ γ k x.1) (List.ofFn x.2) = [true]) ≤
            (1 / 2 : ℝ) ^ 11 + 1 / 100) ∧
        (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3 := by
  obtain ⟨Nc, hNc⟩ := rectangular_classifier_at_large27 E c hc0 hc hE Δ p hΔ γ hγ
  refine ⟨max Nc 36, ?_⟩
  intro N hN n m hn edge hloop hincident hdegree hNm hmn hexp k o _ μ s hfixed hgood
  have hNcN : Nc ≤ N := (le_max_left _ _).trans hN
  have h36 : 36 ≤ N := (le_max_right _ _).trans hN
  have hk : 1 ≤ kOf N := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  have hm : 0 < m := by omega
  have hfinite := selected_finite_guarantees27 hn edge Δ γ (kOf N)
    hk hloop hdegree hγ hΔ hm
  have hclass := hNc N hNcN hn edge hincident hdegree hNm hmn hexp
  dsimp only at hfinite hclass ⊢
  exact two_stage_classifier_error27 μ s
    (fun t => natField (2 * o.budget + k) ++ matrixWord27 hn edge Δ γ k t)
    E (FiniteFallbackOutput.ThreeColourable edge)
    (∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    (fun t => o.budget + k ≤ D (o.table t).matrix) hfixed
    (fun hyes t => (hclass t).1 (hfinite.2.1 hyes t)) hgood
    (fun _ t ht => (hclass t).2 ht)

#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.rectangular_joint_at_large27

end Paper2.CurrentAdditive.QuarticClassEndpoint
