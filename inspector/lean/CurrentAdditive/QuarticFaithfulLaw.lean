import CurrentAdditive.QuarticFaithfulSelectedCodec
import Paper2.AModelTapeBridge

/-! Exact fair-bit law for the manuscript-faithful selected output.  The
per-draw fallback changes tables, not the public fair-bit tape. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.GenericQuarticFaithful
open Paper2.Unit4Shell.Definitions (uniformTape)
open EthInapproximability.CurrentPaper

noncomputable section
set_option maxHeartbeats 8000000

def scheduledExperiment27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    TotalFiniteConstructorScratch.SelectedExperiment :=
  { output := scheduledOutput27Faithful hn edge Δ γ k hc
    tapeFintype := by
      dsimp only [scheduledOutput27Faithful, scheduledOutput27]
      infer_instance
    tapeLaw := by
      dsimp only [scheduledOutput27Faithful, scheduledOutput27]
      exact (scheduledExperiment27 hn edge Δ γ k hc).tapeLaw }

def experiment27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    TotalFiniteConstructorScratch.SelectedExperiment :=
  if hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ then
    scheduledExperiment27Faithful hn edge Δ γ k hc
  else TotalFiniteConstructorScratch.fallbackExperiment edge k

theorem experiment27Faithful_output_eq_select27Faithful {n m : ℕ}
    (hn : 0 < n) (edge : Fin m → Bool → Fin n)
    (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    (experiment27Faithful hn edge Δ γ k).output =
      select27Faithful hn edge Δ γ k := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · simp [experiment27Faithful, select27Faithful, hc,
      scheduledExperiment27Faithful]
  · simp [experiment27Faithful, select27Faithful, hc,
      TotalFiniteConstructorScratch.fallbackExperiment]

theorem faithful_uniformExact27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    AEndpoint.uniformExact (experiment27Faithful hn edge Δ γ k).output.Tape
      (experiment27Faithful hn edge Δ γ k).tapeFintype
      (experiment27Faithful hn edge Δ γ k).tapeLaw
      (experiment27Faithful hn edge Δ γ k).output.tapeBits := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [show experiment27Faithful hn edge Δ γ k =
        scheduledExperiment27Faithful hn edge Δ γ k hc by
          simp [experiment27Faithful, hc]]
    unfold AEndpoint.uniformExact
    dsimp only [scheduledExperiment27Faithful, scheduledOutput27Faithful]
    exact ⟨_, fun t => t.property, Subtype.val_injective,
      fun w hw => ⟨⟨w, hw⟩, rfl⟩, fun _ => rfl⟩
  · rw [show experiment27Faithful hn edge Δ γ k =
        TotalFiniteConstructorScratch.fallbackExperiment edge k by
          simp [experiment27Faithful, hc]]
    unfold AEndpoint.uniformExact
    refine ⟨0, fun _ => rfl, fun _ _ _ => rfl,
      fun w hw => ⟨(), ?_⟩, fun _ => ?_⟩
    · exact (List.eq_nil_of_length_eq_zero hw).symm
    · show (1 : ℝ) = (1 / 2 : ℝ) ^ 0
      simp

theorem faithful_prob_uniform27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    ∃ r : ℕ,
      (∀ t, ((experiment27Faithful hn edge Δ γ k).output.tapeBits t).length = r) ∧
      ∀ F : List Bool → Prop,
        @FiniteLaw.prob _ (experiment27Faithful hn edge Δ γ k).tapeFintype
          (experiment27Faithful hn edge Δ γ k).tapeLaw
          (fun t => F ((experiment27Faithful hn edge Δ γ k).output.tapeBits t)) =
        (uniformTape r).prob (fun s => F (List.ofFn s)) :=
  @Paper2.AModel.prob_of_uniformExact _
    (experiment27Faithful hn edge Δ γ k).tapeFintype _ _
      (faithful_uniformExact27 hn edge Δ γ k)

#print axioms faithful_uniformExact27
#print axioms faithful_prob_uniform27

end
end Paper2.CurrentAdditive.QuarticClassEndpoint
