import CurrentAdditive.QuarticFaithfulSelectedGuarantees

/-! Language membership of the *new* encoded selected output.  These finite
statements deliberately do not identify it with the old zero-on-exhaustion
selector or assert a physical machine. -/

namespace Paper2.GenericQuarticFaithful

open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticClassEndpoint
open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity

theorem faithful_output_language_iff {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27Faithful hn edge Δ γ k).Tape) :
    outputBits27Faithful hn edge Δ γ k t ∈ EncodedCommunication.Language ↔
      D ((select27Faithful hn edge Δ γ k).table t).matrix ≤
        (select27Faithful hn edge Δ γ k).budget := by
  exact EncodedSelectedOutput.encode_instance_language_iff _ _
    (select27Faithful_dimensions_pos hn edge Δ γ k).1
    (select27Faithful_dimensions_pos hn edge Δ γ k).2

theorem faithful_good_yes_language {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (colour : Fin n → Fin 3)
    (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (t : (select27Faithful hn edge Δ γ k).Tape) :
    outputBits27Faithful hn edge Δ γ k t ∈ EncodedCommunication.Language :=
  (faithful_output_language_iff hn edge Δ γ k t).mpr
    (faithful_good_yes_cost hn edge Δ γ k hγ hΔ hm hc colour proper t)

theorem faithful_exact_gap_not_language {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k) (t : (select27Faithful hn edge Δ γ k).Tape)
    (hcost : D ((select27Faithful hn edge Δ γ k).table t).matrix =
      (select27Faithful hn edge Δ γ k).budget + k) :
    outputBits27Faithful hn edge Δ γ k t ∉ EncodedCommunication.Language := by
  rw [faithful_output_language_iff, hcost]
  omega

theorem faithful_good_no_language_mass {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (kGap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
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
  have hm0 := faithful_good_no_mass hn edge Δ γ k loopless hdegree
    hγ hΔ hm hc kGap
  change 1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
      D (exp.output.table t).matrix = exp.output.budget + k) at hm0
  apply hm0.trans
  apply FiniteLaw.prob_mono
  intro t ht
  have hp : 0 < exp.output.rows ∧ 0 < exp.output.cols := by
    rw [show exp.output = select27Faithful hn edge Δ γ k from
      experiment27Faithful_output_eq_select27Faithful hn edge Δ γ k]
    exact select27Faithful_dimensions_pos hn edge Δ γ k
  rw [EncodedSelectedOutput.encode_instance_language_iff _ _ hp.1 hp.2, ht]
  omega

#print axioms faithful_output_language_iff
#print axioms faithful_good_yes_language
#print axioms faithful_good_no_language_mass

end Paper2.GenericQuarticFaithful
