import CurrentAdditive.QuarticSuccessLift
import CurrentAdditive.QuarticSourceSize
import Paper2.A3U

/-! The v27 failed-check branch uses the same fixed finite fallback table machine,
with the source's literal quartic size threshold. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticUnschedFinite

open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly.Unsched
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.TotalFiniteConstructorScratch

/-- Failure of the literal v27 public check bounds the graph order. -/
theorem failed_schedule_run27 {v e : ℕ} [Nonempty (Fin v)]
    (edge : Fin e → Bool → Fin v) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ u, ∃ i b, edge i b = u)
    (hdegree : ∀ u, SourceItems.degree edge u ≤ Δ)
    (hfail : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin v) (Edges := Fin e) (Nat.clog 2 v) Δ γ) (k : ℕ) :
    ∃ t ≤ FallbackFiniteClock.coefficient
        (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ * 2 ^ (3 * k),
      ∃ (ctl : FallbackBranchT.ACtl) (q : List Bool),
        FallbackFiniteClock.RunsToTable edge k t ctl q := by
  have hv : v < CurrentAdditive.QuarticSchedule.threshold27 Δ γ := by
    simpa only [Fintype.card_fin] using
      CurrentAdditive.QuarticSchedule.failure_below_size_threshold27
        edge Δ γ hγ hΔ hincident hdegree
        (by simpa only [Fintype.card_fin] using hfail)
  exact FallbackFiniteClock.bounded_input_run edge k hv.le hdegree

/-- The failed v27 selector has the existing exact fallback table word and an
empty selected randomness tape. -/
theorem outputBits_unscheduled27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (select27 hn edge Δ γ k).Tape) :
    outputBits27 hn edge Δ γ k t =
      EncodedCommunication.encodeInstance
        ⟨FiniteFallbackOutput.rows k, FiniteFallbackOutput.cols k, 0,
          MatrixMaterialization.rowMajor (FiniteFallbackOutput.fallbackMatrix edge k)⟩ ∧
    (select27 hn edge Δ γ k).tapeBits t = [] := by
  have key : ∀ (o : SelectedOutput) (_ : o = TotalFiniteConstructorScratch.fallbackOutput edge k)
      (t : o.Tape),
      EncodedCommunication.encodeInstance
        (EncodedSelectedOutput.instanceOf (o.table t) o.budget) =
        EncodedCommunication.encodeInstance
          ⟨FiniteFallbackOutput.rows k, FiniteFallbackOutput.cols k, 0,
            MatrixMaterialization.rowMajor (FiniteFallbackOutput.fallbackMatrix edge k)⟩ ∧
      o.tapeBits t = [] := by
    intro o h t
    subst h
    exact ⟨rfl, rfl⟩
  exact key _ (select27_bad hn edge Δ γ k hc) t

#print axioms failed_schedule_run27
#print axioms outputBits_unscheduled27

end Paper2.CurrentAdditive.QuarticUnschedFinite
