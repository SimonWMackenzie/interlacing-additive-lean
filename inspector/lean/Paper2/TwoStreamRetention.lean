import Paper2.ProjectedSupportFrontierScheduled
import Paper2.TwoStreamMatrix

/-!
# Paired retention along the actual outer-bin walk

Frozen v12, Section 5, `eq:paired-retention` and `res:two-stream`.
The hypothesis is precisely retention after small loss in the original
ambient paired-row law. The loss is derived for the generated walk;
surviving joint pair mass is not an extra frontier hypothesis.
-/

namespace Paper2.TwoStreamRetention

open ProjectedSupportFrontier

variable {A C I W S : Type*} [Fintype W] [Fintype S] [DecidableEq I] [DecidableEq W]

theorem retained_pair_mass (κ : FiniteLaw W) (μ : FiniteLaw S)
    (ζ : W → S × S) (hζ : κ.PushesTo (μ.prod μ) ζ)
    (σ : I → W → S) (star : I) (hfirst : σ star = fun w => (ζ w).1)
    (input : I → W → C) (floor : ℕ → ℝ)
    (hhalf : ∀ d, floor d = 2 * floor (d + 1)) (hpos : ∀ d, 0 < floor d)
    (fuel : ℕ) (initial : State A C I W)
    (hZ : initial.attachments = {star})
    (hretain : ∀ P' : Finset W, P' ⊆ initial.support star →
      SourceSupportStep.mass κ (initial.support star \ P') < floor 0 →
      (49 / 64 : ℝ) ≤ (μ.prod μ).prob (· ∈ ζ '' (P' : Set W))) :
    let K := runScheduled μ σ input floor 0 fuel initial
    ∀ v : K.Leaves, star ∈ (K.state v).attachments →
      (49 / 64 : ℝ) ≤ (μ.prod μ).prob
        (· ∈ ζ '' ((K.state v).support star : Set W)) := by
  classical
  intro K v hv
  have hpush : ∀ i ∈ initial.attachments, κ.PushesTo μ (σ i) := by
    intro i hi
    have he : i = star := by simpa [hZ] using hi
    subst i
    rw [hfirst]
    exact TwoStreamMatrix.paired_first_pushes μ κ ζ hζ
  have hloss := runScheduled_raw_loss_lt (fun _ => κ) μ σ input floor
    hhalf hpos 0 fuel initial hpush v star hv
  have hsub := (runScheduled_sets_subset μ σ input floor 0 fuel initial v).2.2 star
  exact hretain ((K.state v).support star) hsub hloss

end Paper2.TwoStreamRetention

#print axioms Paper2.TwoStreamRetention.retained_pair_mass
