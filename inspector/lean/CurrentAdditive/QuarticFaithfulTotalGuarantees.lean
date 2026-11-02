import CurrentAdditive.QuarticFaithfulEncodedGuarantees

/-! Total finite guarantees for the manuscript-faithful selector. The failed
public-check branch is the existing finite fallback; failed capped draws on
the scheduled branch remain inside the faithful recursive table. -/

namespace Paper2.GenericQuarticFaithful

open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticClassEndpoint
open Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem faithful_selected_yes_cost {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hcolour : FiniteFallbackOutput.ThreeColourable edge) :
    let o := select27Faithful hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget := by
  intro o
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · obtain ⟨colour, proper⟩ := hcolour
    exact faithful_good_yes_cost hn edge Δ γ k hγ hΔ hm hc
      colour proper
  · change ∀ t : (select27Faithful hn edge Δ γ k).Tape,
      D ((select27Faithful hn edge Δ γ k).table t).matrix ≤
        (select27Faithful hn edge Δ γ k).budget
    rw [select27Faithful_bad hn edge Δ γ k hc]
    intro t
    change D (FiniteFallbackOutput.fallbackTable edge k).matrix ≤
      FiniteFallbackOutput.budget
    exact Nat.le_of_eq (FiniteFallbackOutput.fallback_yes_D edge k hcolour)

theorem faithful_selected_yes_language {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hcolour : FiniteFallbackOutput.ThreeColourable edge)
    (t : (select27Faithful hn edge Δ γ k).Tape) :
    outputBits27Faithful hn edge Δ γ k t ∈ EncodedCommunication.Language :=
  (faithful_output_language_iff hn edge Δ γ k t).mpr
    (faithful_selected_yes_cost hn edge Δ γ k hγ hΔ hm hcolour t)

theorem faithful_selected_no_mass {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    let exp := experiment27Faithful hn edge Δ γ k
    letI : Fintype exp.output.Tape := exp.tapeFintype
    1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
      D (exp.output.table t).matrix = exp.output.budget + k) := by
  intro exp
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · exact faithful_good_no_mass hn edge Δ γ k loopless hdegree
      hγ hΔ hm hc gap
  · have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
    have hD := FiniteFallbackSourceGap.fallback_source_no_D
      edge (γ : ℝ) hγR hm gap k hk
    have hD' : D (FiniteFallbackOutput.fallbackTable edge k).matrix = k := by
      simpa [FiniteFallbackOutput.budget] using hD
    have he : exp = TotalFiniteConstructorScratch.fallbackExperiment edge k := by
      simp [exp, experiment27Faithful, hc]
    rw [he]
    letI := (TotalFiniteConstructorScratch.fallbackExperiment edge k).tapeFintype
    let e := TotalFiniteConstructorScratch.fallbackExperiment edge k
    have hEvent : (fun t : e.output.Tape =>
      D (e.output.table t).matrix = e.output.budget + k) =
        (fun _ : e.output.Tape => True) := by
      funext t
      apply propext
      change D (FiniteFallbackOutput.fallbackTable edge k).matrix = 0 + k ↔ True
      simp [hD']
    rw [hEvent]
    rw [FiniteLaw.prob_true]
    norm_num

theorem faithful_selected_no_language_mass {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    let exp := experiment27Faithful hn edge Δ γ k
    letI : Fintype exp.output.Tape := exp.tapeFintype
    1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
      EncodedCommunication.encodeInstance
        (EncodedSelectedOutput.instanceOf (exp.output.table t)
          exp.output.budget) ∉ EncodedCommunication.Language) := by
  intro exp
  letI : Fintype exp.output.Tape := exp.tapeFintype
  have hmass := faithful_selected_no_mass hn edge Δ γ k hk
    loopless hdegree hγ hΔ hm gap
  change 1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
    D (exp.output.table t).matrix = exp.output.budget + k) at hmass
  apply hmass.trans
  apply FiniteLaw.prob_mono
  intro t ht
  have hp : 0 < exp.output.rows ∧ 0 < exp.output.cols := by
    rw [show exp.output = select27Faithful hn edge Δ γ k from
      experiment27Faithful_output_eq_select27Faithful hn edge Δ γ k]
    exact select27Faithful_dimensions_pos hn edge Δ γ k
  rw [EncodedSelectedOutput.encode_instance_language_iff _ _ hp.1 hp.2, ht]
  omega

#print axioms faithful_selected_yes_cost
#print axioms faithful_selected_yes_language
#print axioms faithful_selected_no_mass
#print axioms faithful_selected_no_language_mass

end Paper2.GenericQuarticFaithful
