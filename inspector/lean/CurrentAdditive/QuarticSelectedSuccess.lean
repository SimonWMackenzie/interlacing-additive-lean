import CurrentAdditive.QuarticScheduledFiniteGuarantees

namespace Paper2.CurrentAdditive.QuarticConstructor

open SourceProfileParameters SourceRecursiveNoSampling
  Workspace.Types.CommComplexity

private theorem sourceCost_eq_budget_add27 (L r q k : ℕ) :
    sourceCost L r q k = sourceBudget L r q k + k := by
  simp only [sourceCost, sourceBudget]
  ring

/-- The NO-cost success event under the law of the actual v27 selector. -/
noncomputable def successProbability27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℝ := by
  let e := experiment27 hn edge Δ γ k
  letI := e.tapeFintype
  exact e.tapeLaw.prob
    (fun t => D (e.output.table t).matrix = e.output.budget + k)

private theorem successProbability27_good {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    successProbability27 hn edge Δ γ k =
      (RecursiveSamplingMaterialization.tapeListLaw
        (Fin n) (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
        (outerWidth (Nat.clog 2 n))
        (CurrentAdditive.RandomizedSchedule.width27 (Nat.clog 2 n))
        (CurrentAdditive.RandomizedSchedule.Q27
          (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)
        (LookupSeed.width (Nat.clog 2 n)) k
        (rows27 n m (Nat.clog 2 n) Δ γ k)
        (cols27 n m (Nat.clog 2 n) Δ γ k)).prob
        (fun bits => D (scheduledTable27 hn edge (Nat.clog 2 n) Δ γ k
          hc bits).matrix =
          sourceBudget (Nat.clog 2 n)
            (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
            (CurrentAdditive.RandomizedSchedule.q27
              (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k + k) := by
  unfold successProbability27
  dsimp only
  have he : experiment27 hn edge Δ γ k =
      scheduledExperiment27 hn edge Δ γ k hc := by
    simp [experiment27, hc]
  rw [he]
  rfl

private theorem successProbability27_bad_of_gap {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hm : 0 < m) (hk : 1 ≤ k)
    (hc : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    successProbability27 hn edge Δ γ k = 1 := by
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hD := FiniteFallbackSourceGap.fallback_source_no_D
    edge (γ : ℝ) hγR hm gap k hk
  have hD' : D (FiniteFallbackOutput.fallbackTable edge k).matrix = k := by
    simpa [FiniteFallbackOutput.budget] using hD
  unfold successProbability27
  dsimp only
  have he : experiment27 hn edge Δ γ k =
      TotalFiniteConstructorScratch.fallbackExperiment edge k := by
    simp [experiment27, hc]
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
  exact FiniteLaw.prob_true _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The actual selected v27 constructor attains its announced NO cost
with the v27 finite success probability, including the fallback branch. -/
theorem selected_no_success27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    1 - (1 / 2 : ℝ) ^ 11 ≤ successProbability27 hn edge Δ γ k := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    have hG := scheduled_table_finite_guarantees27
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    rw [successProbability27_good hn edge Δ γ k hc]
    simpa only [sourceCost_eq_budget_add27] using (hG.2.2.1 gap).2
  · rw [successProbability27_bad_of_gap hn edge Δ γ k hγ hm hk hc gap]
    norm_num

#print axioms selected_no_success27

end Paper2.CurrentAdditive.QuarticConstructor
