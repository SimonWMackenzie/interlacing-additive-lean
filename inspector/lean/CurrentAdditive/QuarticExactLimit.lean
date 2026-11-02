import CurrentAdditive.QuarticExactScheduled

/-! The manuscript's `o(1)` has its ordinary sequence meaning: the exact
logarithmic error tends to zero as the source length tends to infinity. -/

namespace CurrentAdditive.QuarticExactAsymptotics

open Filter Paper2 Paper2.SourceRecursiveNoSampling

theorem source_budget_tendsto_atTop
    (L r q k : ℕ → ℕ)
    (hL : Tendsto L atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i => sourceBudget (L i) (r i) (q i) (k i))
      atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [hL.eventually_ge_atTop b, hk] with i hLi hki
  exact hLi.trans (source_budget_ge_length (L i) (r i) (q i) (k i) hki)

theorem source_log_error_tendsto_zero
    (L r q k : ℕ → ℕ)
    (hL : Tendsto L atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i : ℕ =>
      let B := sourceBudget (L i) (r i) (q i) (k i)
      let T := sourceRows (L i) (r i) (q i) (k i) *
        sourceCols (L i) (r i) (q i) (k i)
      Real.logb 2 (((L i * T : ℕ) : ℝ) /
        (2^(6*B+2*k i-5) : ℝ))) atTop (nhds 0) := by
  let B (i : ℕ) := sourceBudget (L i) (r i) (q i) (k i)
  let T (i : ℕ) := sourceRows (L i) (r i) (q i) (k i) *
    sourceCols (L i) (r i) (q i) (k i)
  let e (i : ℕ) : ℝ := Real.logb 2 (((L i * T i : ℕ) : ℝ) /
    (2^(6*B i+2*k i-5) : ℝ))
  have hB : Tendsto B atTop atTop :=
    source_budget_tendsto_atTop L r q k hL hk
  have hBm : Tendsto (fun i => B i - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hB
  have hPow : Tendsto (fun i => (2:ℝ)^(B i-1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hBm
  have hInv : Tendsto (fun i => ((2:ℝ)^(B i-1))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hPow
  have hFrac : Tendsto (fun i => (271:ℝ) /
      ((2^(B i-1):ℕ):ℝ)) atTop (nhds 0) := by
    simpa [Nat.cast_pow, div_eq_mul_inv] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (271:ℝ)) atTop (nhds 271)).mul hInv)
  have hArg : Tendsto (fun i => (1:ℝ) + 271 /
      ((2^(B i-1):ℕ):ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hFrac :
      Tendsto (fun i => (1:ℝ) + 271 / ((2^(B i-1):ℕ):ℝ)) atTop (nhds (1+0)))
  have hUpper : Tendsto (fun i => Real.logb 2 (1 + 271 /
      ((2^(B i-1):ℕ):ℝ))) atTop (nhds 0) := by
    have hc := (Real.continuousAt_logb (b := (2:ℝ))
      (x := (1:ℝ)) (by norm_num)).tendsto.comp hArg
    simpa using hc
  have hL1 : ∀ᶠ i in atTop, 1 ≤ L i := hL.eventually_ge_atTop 1
  have hbound : ∀ᶠ i in atTop,
      0 ≤ e i ∧ e i ≤ Real.logb 2 (1 + 271 /
        ((2^(B i-1):ℕ):ℝ)) := by
    filter_upwards [hL1, hk] with i hLi hki
    have hh := source_log_expansion (L i) (r i) (q i) (k i) hLi hki
    exact ⟨hh.1, hh.2.1⟩
  have he : Tendsto e atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper (hbound.mono fun i hi => hi.1)
        (hbound.mono fun i hi => hi.2)
  simpa only [e, T, B] using he

theorem clog_two_tendsto_atTop (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => Nat.clog 2 (n i)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [hn.eventually_ge_atTop (2^b)] with i hi
  have hc := Nat.clog_mono_right 2 hi
  simpa only [Nat.clog_pow 2 b (by decide)] using hc

/-- Literal v27 printed output: the additive error in the exact display
`log₂ T = 6B+2k-log₂ L-5+error` tends to zero as graph size grows, with
at least one iteration eventually. -/
theorem printedT27_log_error_tendsto_zero
    (n m k : ℕ → ℕ) (Δ : ℕ) (γ : ℚ)
    (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i : ℕ =>
      let L := Nat.clog 2 (n i)
      let r := 4 * RestorationWidthScheduleScratch.ell L
      let q := CurrentAdditive.RandomizedSchedule.q27
        (V := Fin (n i)) (E := Fin (m i)) L γ Δ
      let B := sourceBudget L r q (k i)
      let T := CurrentAdditive.QuarticAsymptotics.printedT27
        (n i) (m i) Δ γ (k i)
      Real.logb 2 (((L*T : ℕ) : ℝ) /
        (2^(6*B+2*k i-5) : ℝ))) atTop (nhds 0) := by
  let L (i : ℕ) := Nat.clog 2 (n i)
  let r (i : ℕ) := 4 * RestorationWidthScheduleScratch.ell (L i)
  let q (i : ℕ) := CurrentAdditive.RandomizedSchedule.q27
    (V := Fin (n i)) (E := Fin (m i)) (L i) γ Δ
  have hh := source_log_error_tendsto_zero L r q k
    (clog_two_tendsto_atTop n hn) hk
  simpa only [CurrentAdditive.QuarticAsymptotics.printedT27,
    L, r, q] using hh

theorem printedT27_exact_expansion
    (n m k : ℕ → ℕ) (Δ : ℕ) (γ : ℚ)
    (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i : ℕ =>
      let L := Nat.clog 2 (n i)
      let r := 4 * RestorationWidthScheduleScratch.ell L
      let q := CurrentAdditive.RandomizedSchedule.q27
        (V := Fin (n i)) (E := Fin (m i)) L γ Δ
      let B := sourceBudget L r q (k i)
      let T := CurrentAdditive.QuarticAsymptotics.printedT27
        (n i) (m i) Δ γ (k i)
      Real.logb 2 (T:ℝ) -
        ((6*B+2*k i-5:ℕ):ℝ) + Real.logb 2 (L:ℝ))
      atTop (nhds 0) := by
  have herr := printedT27_log_error_tendsto_zero n m k Δ γ hn hk
  have hn2 : ∀ᶠ i in atTop, 2 ≤ n i := hn.eventually_ge_atTop 2
  apply herr.congr'
  filter_upwards [hn2, hk] with i hni hki
  have hh := printedT27_log_expansion (n i) (m i) Δ γ (k i) hni hki
  dsimp at hh ⊢
  linarith [hh.2.2]

/-- The manuscript's real-valued display, including its constant `-5` and
the row-length correction `-log₂ L`, for every growing graph-size sequence
and every eventually positive iteration count. -/
theorem printedT27_manuscript_asymptotic
    (n m k : ℕ → ℕ) (Δ : ℕ) (γ : ℚ)
    (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i : ℕ =>
      let L := Nat.clog 2 (n i)
      let r := 4 * RestorationWidthScheduleScratch.ell L
      let q := CurrentAdditive.RandomizedSchedule.q27
        (V := Fin (n i)) (E := Fin (m i)) L γ Δ
      let B := sourceBudget L r q (k i)
      let T := CurrentAdditive.QuarticAsymptotics.printedT27
        (n i) (m i) Δ γ (k i)
      Real.logb 2 (T:ℝ) -
        ((6:ℝ)*(B:ℝ) + 2*(k i:ℝ) - Real.logb 2 (L:ℝ) - 5))
      atTop (nhds 0) := by
  have hh := printedT27_exact_expansion n m k Δ γ hn hk
  apply hh.congr'
  have hn2 : ∀ᶠ i in atTop, 2 ≤ n i := hn.eventually_ge_atTop 2
  filter_upwards [hn2, hk] with i hni hki
  let L := Nat.clog 2 (n i)
  let r := 4 * RestorationWidthScheduleScratch.ell L
  let q := CurrentAdditive.RandomizedSchedule.q27
    (V := Fin (n i)) (E := Fin (m i)) L γ Δ
  let B := sourceBudget L r q (k i)
  have hB : 1 ≤ B := by dsimp [B, sourceBudget]; omega
  have hp : ((6*B+2*k i-5:ℕ):ℝ) =
      (6:ℝ)*(B:ℝ) + 2*(k i:ℝ) - 5 := by
    rw [Nat.cast_sub (by omega : 5 ≤ 6*B+2*k i)]
    push_cast
    ring
  dsimp
  rw [hp]
  ring

end CurrentAdditive.QuarticExactAsymptotics
