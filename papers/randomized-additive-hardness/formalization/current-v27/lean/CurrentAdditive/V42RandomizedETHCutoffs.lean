import CurrentAdditive.V42RandomizedETHFits

/-! Common eventual cutoff for the exact current square table, its growing
error margin, and the physical amplified classifier's actual request length.
The graph bounds remain explicit until the concrete source owner is joined. -/
namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2
open Paper2.Unit4Shell.Asymptotics
open V42PublicSchedule
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def growingError (c : ℝ) (T : ℕ) : ℝ :=
  c*(Real.logb 2 T / Real.logb 2 (Real.logb 2 T))

theorem growingError_nonnegative (c : ℝ) (hc : 0 ≤ c) (T : ℕ) (hT : 4 ≤ T) :
    0 ≤ growingError c T := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (by omega : 0<T)
  have hlog : 1 < Real.logb 2 T := by
    have h2 : (2 : ℝ) < T := by exact_mod_cast (by omega : 2<T)
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
      (by norm_num : (0 : ℝ)<2) h2
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using h
  have hden : 0 < Real.logb 2 (Real.logb 2 T) :=
    Real.logb_pos (by norm_num) hlog
  exact mul_nonneg hc (div_nonneg (by linarith) hden.le)

/-- One cutoff handles positive iteration, sufficiently large table, the
sharp c<1/8 separation, and every payload's actual classifier resource fit. -/
theorem current_numeric_cutoff (Δ p T₀ : ℕ) (hΔ : 0 < Δ)
    (C : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c) (hc : c<1/8) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → N ≤ Δ*n → n ≤ N*(Nat.clog 2 (N+2))^p →
      let L := Nat.clog 2 n
      let k := kOf N
      let T := sampleEntries L k
      1 ≤ k ∧ T₀ ≤ T ∧ 4 ≤ T ∧
      0 ≤ growingError c T ∧ 2*growingError c T < (k : ℝ) ∧
      ∀ f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool,
        C.tapeLength (requestedWord L k f) ≤ C.cR*AEth.expLen N ∧
        C.cT*((requestedWord L k f).length+1)^C.dT ≤ C.cT*AEth.expLen N := by
  obtain ⟨Ng,hg⟩ := V42ETHArithmetic.gap_exceeds_twice_error Δ p hΔ c hc0 hc
  obtain ⟨Nk,hk⟩ := V42ETHArithmetic.iterations_eventually_ge 1
  obtain ⟨Nt,ht⟩ := V42ETHArithmetic.entries_eventually_ge (max 4 T₀)
  obtain ⟨Nf,hf⟩ := classifier_fits C p
  refine ⟨1+Ng+Nk+Nt+Nf,by omega,?_⟩
  intro N hN n hn hlow hhigh
  dsimp only
  have h4 : 4 ≤ sampleEntries (Nat.clog 2 n) (kOf N) :=
    (le_max_left _ _).trans (ht N (by omega) _)
  refine ⟨hk N (by omega),(le_max_right _ _).trans (ht N (by omega) _),h4,
    growingError_nonnegative c hc0 _ h4,?_,?_⟩
  · have h := hg N (by omega) n hn hlow hhigh
    simpa only [growingError,mul_div_assoc,mul_assoc] using h
  · exact hf N (by omega) n hn hhigh

#print axioms growingError_nonnegative
#print axioms current_numeric_cutoff
end
end CurrentAdditive.V42RandomizedETHEndpoint

