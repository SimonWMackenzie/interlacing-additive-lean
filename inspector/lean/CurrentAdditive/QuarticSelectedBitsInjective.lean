import CurrentAdditive.QuarticSourcePhysicalFit
import CurrentAdditive.QuarticUniformExact

/-! The literal selector's fair-bit serialization determines its tape. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor

theorem selected_tapeBits_injective27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    Function.Injective (select27 hn edge Δ γ k).tapeBits := by
  obtain ⟨r, hlen, hinj, hsurj, hprob⟩ :=
    experiment_uniformExact27 hn edge Δ γ k
  have hO := experiment27_output_eq_select27 hn edge Δ γ k
  rw [hO] at hinj
  exact hinj

#print axioms selected_tapeBits_injective27

end Paper2.CurrentAdditive.QuarticClassEndpoint
