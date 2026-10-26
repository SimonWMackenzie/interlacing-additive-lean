import CurrentAdditive.QuarticFaithfulNoMass

/-! Finite YES and NO guarantees for the corrected selected output on the
publicly admitted scheduled branch. They concern the new table on every tape. -/

namespace Paper2.GenericQuarticFaithful

open Paper2 SourceProfileParameters SourceRecursiveNoSampling
  Workspace.Types.CommComplexity CurrentAdditive.RandomizedSchedule
  Paper2.CurrentAdditive.QuarticConstructor
  Paper2.CurrentAdditive.QuarticClassEndpoint

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private theorem cost_eq_budget_add (L r q k : ℕ) :
    sourceCost L r q k = sourceBudget L r q k + k := by
  simp only [sourceCost, sourceBudget]
  ring

/-- Row-major table length and tape length hold for both public-check
branches of the new selector. The fallback branch here is the public-check
fallback; a capped draw on the scheduled branch keeps sampling. -/
theorem select27Faithful_exact_lengths {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let o := select27Faithful hn edge Δ γ k
    ∀ t : o.Tape,
      (o.table t).bits.length = o.rows * o.cols ∧
      (o.tapeBits t).length = o.inputBits := by
  intro o
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · change ∀ t : (select27Faithful hn edge Δ γ k).Tape,
      ((select27Faithful hn edge Δ γ k).table t).bits.length =
        (select27Faithful hn edge Δ γ k).rows *
          (select27Faithful hn edge Δ γ k).cols ∧
      ((select27Faithful hn edge Δ γ k).tapeBits t).length =
        (select27Faithful hn edge Δ γ k).inputBits
    rw [select27Faithful_good hn edge Δ γ k hc]
    intro t
    constructor
    · change (table27Faithful hn edge (Nat.clog 2 n) Δ γ k hc t).bits.length = _
      exact YaoMaterialization.tabulate_length _
    · exact t.property
  · change ∀ t : (select27Faithful hn edge Δ γ k).Tape,
      ((select27Faithful hn edge Δ γ k).table t).bits.length =
        (select27Faithful hn edge Δ γ k).rows *
          (select27Faithful hn edge Δ γ k).cols ∧
      ((select27Faithful hn edge Δ γ k).tapeBits t).length =
        (select27Faithful hn edge Δ γ k).inputBits
    rw [select27Faithful_bad hn edge Δ γ k hc]
    intro t
    constructor
    · simpa only [TotalFiniteConstructorScratch.fallbackOutput] using
        FiniteFallbackOutput.fallbackTable_bits_length edge k
    · rfl

theorem faithful_good_all_cost {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    let o := select27Faithful hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget + k := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  intro o
  change ∀ t : (select27Faithful hn edge Δ γ k).Tape,
    D ((select27Faithful hn edge Δ γ k).table t).matrix ≤
      (select27Faithful hn edge Δ γ k).budget + k
  rw [select27Faithful_good hn edge Δ γ k hc]
  intro t
  have h := scheduled_faithful_all_cost (Nat.clog 2 n) Δ γ edge
    hγ hΔ hm hc k t
  simpa only [scheduledOutput27Faithful, scheduledOutput27,
    cost_eq_budget_add] using h

theorem faithful_good_yes_cost {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (colour : Fin n → Fin 3)
    (proper : ∀ e, colour (edge e false) ≠ colour (edge e true)) :
    let o := select27Faithful hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  intro o
  change ∀ t : (select27Faithful hn edge Δ γ k).Tape,
    D ((select27Faithful hn edge Δ γ k).table t).matrix ≤
      (select27Faithful hn edge Δ γ k).budget
  rw [select27Faithful_good hn edge Δ γ k hc]
  intro t
  have h := scheduled_faithful_yes_cost (Nat.clog 2 n) Δ γ edge
    hγ hΔ hm hc k t colour proper
  simpa only [scheduledOutput27Faithful, scheduledOutput27] using h

theorem faithful_good_no_mass {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
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
      D (exp.output.table t).matrix = exp.output.budget + k) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  intro exp
  letI : Fintype exp.output.Tape := exp.tapeFintype
  have h := scheduled_faithful_no_mass Δ γ edge loopless hdegree
    hγ hΔ hm hc k kGap
  have he : exp = scheduledExperiment27Faithful hn edge Δ γ k hc := by
    simpa only [exp] using
      (show experiment27Faithful hn edge Δ γ k =
        scheduledExperiment27Faithful hn edge Δ γ k hc by
        simp [experiment27Faithful, hc])
  rw [he]
  simpa only [
    scheduledExperiment27Faithful, scheduledOutput27Faithful,
    scheduledOutput27, cost_eq_budget_add] using h

#print axioms faithful_good_all_cost
#print axioms faithful_good_yes_cost
#print axioms faithful_good_no_mass
#print axioms select27Faithful_exact_lengths

end Paper2.GenericQuarticFaithful
