import CurrentAdditive.QuarticSourceMachine
import Paper2.AModelTapeBridge

/-!
# Exact fair-bit law of the literal v27 selector tape

The scheduled branch is a fixed-length list of independent fair bits; the
fallback branch has the unique empty tape. The word encoding is a bijection
in both branches, so the actual selected law is exactly uniform on a fixed
number of bits.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem experiment_uniformExact27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    AEndpoint.uniformExact (experiment27 hn edge Δ γ k).output.Tape
      (experiment27 hn edge Δ γ k).tapeFintype
      (experiment27 hn edge Δ γ k).tapeLaw
      (experiment27 hn edge Δ γ k).output.tapeBits := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [show experiment27 hn edge Δ γ k =
        scheduledExperiment27 hn edge Δ γ k hc by simp [experiment27, hc]]
    unfold AEndpoint.uniformExact
    dsimp only [scheduledExperiment27, scheduledOutput27]
    exact ⟨_, fun t => t.property, Subtype.val_injective,
      fun w hw => ⟨⟨w, hw⟩, rfl⟩, fun _ => rfl⟩
  · rw [show experiment27 hn edge Δ γ k =
        TotalFiniteConstructorScratch.fallbackExperiment edge k by
          simp [experiment27, hc]]
    unfold AEndpoint.uniformExact
    refine ⟨0, fun _ => rfl, fun _ _ _ => rfl,
      fun w hw => ⟨(), ?_⟩, fun _ => ?_⟩
    · exact (List.eq_nil_of_length_eq_zero hw).symm
    · show (1 : ℝ) = (1 / 2 : ℝ) ^ 0
      simp

theorem experiment_prob_uniform27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    ∃ r : ℕ,
      (∀ t, ((experiment27 hn edge Δ γ k).output.tapeBits t).length = r) ∧
      ∀ F : List Bool → Prop,
        @FiniteLaw.prob _ (experiment27 hn edge Δ γ k).tapeFintype
          (experiment27 hn edge Δ γ k).tapeLaw
          (fun t => F ((experiment27 hn edge Δ γ k).output.tapeBits t)) =
        (uniformTape r).prob (fun s => F (List.ofFn s)) :=
  @Paper2.AModel.prob_of_uniformExact _ (experiment27 hn edge Δ γ k).tapeFintype
    _ _ (experiment_uniformExact27 hn edge Δ γ k)

theorem experiment_prob_prefix27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    ∃ r : ℕ,
      (∀ t, ((experiment27 hn edge Δ γ k).output.tapeBits t).length = r) ∧
      ∀ R : ℕ, r ≤ R → ∀ F : List Bool → Prop,
        @FiniteLaw.prob _ (experiment27 hn edge Δ γ k).tapeFintype
          (experiment27 hn edge Δ γ k).tapeLaw
          (fun t => F ((experiment27 hn edge Δ γ k).output.tapeBits t)) =
        (uniformTape R).prob (fun s => F ((List.ofFn s).take r)) := by
  obtain ⟨r, hlen, hF⟩ := experiment_prob_uniform27 hn edge Δ γ k
  exact ⟨r, hlen, fun R hR F => by
    rw [hF F, Paper2.AModel.uniformTape_take_prob hR F]⟩

#print axioms experiment_uniformExact27
#print axioms experiment_prob_uniform27
#print axioms experiment_prob_prefix27

end Paper2.CurrentAdditive.QuarticClassEndpoint
