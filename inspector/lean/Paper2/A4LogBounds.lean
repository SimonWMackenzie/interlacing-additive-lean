import Paper2.A4ShellsTight

/-!
# Unit 4 (Paper A), A4-S7 made explicit: the two T24 logarithm bounds and a proved `kOf` cutoff

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

Lock v12 `06-reduction.tex`, proof of `thm:quantitative`: with `k = ⌊N/⌈log N⌉²⌋`,
`L = ⌈log n⌉`, `n ≤ N·(log(N+2))^p`: `log T = (6+o(1)) k log N` and `log log T = (1+o(1)) log N`.

The sharp public-schedule overhead `h ≤ (1+ε/12)L` is ALREADY admitted
(`SharpRelative.relative_overhead` inside `SharpOutputSize.at_graph_size_printed_entries_le_six_plus`,
used by the admitted `A4Asymptotics.gap_exceeds_twice_error`); the coarse `SourceOverheadBounds`
are not used. The admitted proof only states the final comparison `2c·log T/log log T < k`.
This module states the two logarithm bounds themselves (`log_bounds`, generic source with the
T45 relations as hypotheses; `log_bounds_t10`, the actual T10 graph of a sparse valid `Φ`, T45
relations DERIVED), both with an explicit `N₀` built from public cutoffs, and replaces the ad hoc
`⌈2^98⌉` of `T24Actual.T24_actual` by the proved sharp cutoff `kOf_pos : 36 ≤ N → 1 ≤ kOf N`
(`T24_actual_cut`, same statement). **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.AsymptoticsExplicit

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

/-- `c² ≤ 2^(c-1)` for `c ≥ 7`. -/
theorem sq_le_two_pow_pred (c : ℕ) (hc : 7 ≤ c) : c ^ 2 ≤ 2 ^ (c - 1) := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
      have h1 : (c + 1) ^ 2 ≤ 2 * c ^ 2 := by nlinarith
      have h2 : 2 ^ (c + 1 - 1) = 2 * 2 ^ (c - 1) := by
        rw [show c + 1 - 1 = (c - 1) + 1 by omega, pow_succ]; ring
      rw [h2]; omega

/-- **Proved sharp cutoff:** `kOf N ≥ 1` for every `N ≥ 36` (`kOf 35 = 0`, so `36` is the
least cutoff valid for all larger `N`). -/
theorem kOf_pos (N : ℕ) (hN : 36 ≤ N) : 1 ≤ kOf N := by
  unfold kOf
  set C := Nat.clog 2 N with hC
  have hC1 : 1 ≤ C := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hsq : C ^ 2 ≤ N := by
    rcases Nat.lt_or_ge C 7 with h | h
    · have : C ^ 2 ≤ 6 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    · have h1 := sq_le_two_pow_pred C h
      have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (by omega : 1 < N)
      rw [← hC, Nat.pred_eq_sub_one] at h2
      omega
  have hpos : 0 < C ^ 2 := by positivity
  exact (Nat.le_div_iff_mul_le hpos).mpr (by simpa using hsq)

theorem kOf_35 : kOf 35 = 0 := by decide

/-- **A4-S7, the two logarithm bounds (generic source).** For fixed `Δ, γ, p` and every rational
`0 < ε ≤ 1/100` there is an explicit `N₀` such that for every `N ≥ N₀` and every source graph
with the T45 relations, `T = printedT n m Δ γ (kOf N)` satisfies
`kOf N ≤ log₂ T ≤ (6+ε)(1+ε)·kOf N·log₂ N` and `(1-ε)·log₂ N ≤ log₂ log₂ T`, and `1 ≤ kOf N`.
Does not close a ledger row. -/
theorem log_bounds (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (p : ℕ)
    (ε : ℚ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (n m : ℕ) [NeZero n] (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) → (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      1 ≤ kOf N ∧
      (kOf N : ℝ) ≤ Real.logb 2 (printedT n m Δ γ (kOf N)) ∧
      Real.logb 2 (printedT n m Δ γ (kOf N)) ≤
        (6 + (ε : ℝ)) * (1 + (ε : ℝ)) * (kOf N : ℝ) * Real.logb 2 N ∧
      (1 - (ε : ℝ)) * Real.logb 2 N ≤ Real.logb 2 (Real.logb 2 (printedT n m Δ γ (kOf N))) := by
  set εr : ℝ := (ε : ℝ) with hεr
  have hεr0 : 0 < εr := by rw [hεr]; exact_mod_cast hε0
  have hεr1 : εr ≤ 1 / 100 := by
    rw [hεr]; have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast hε1
    simpa using this
  set Icut : ℕ := max 1 (SharpOutputSize.iterationCutoff ε) with hIcut
  set Y1 : ℝ := ((3 * (p : ℝ) + 1 + 2) / εr + 1) ^ 2
  set Y2 : ℝ := ((3 * 2 + 1 + 2) / εr + 1) ^ 2
  set Y3 : ℝ := 2 * Real.logb 2 Icut + 1
  set Y : ℝ := max Y1 (max Y2 Y3)
  refine ⟨max (max 2 (Δ * SharpOutputSize.graphSizeCutoff Δ γ ε)) ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN n m _ edge hincident hdegree hNm hmn hsize
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNG : Δ * SharpOutputSize.graphSizeCutoff Δ γ ε ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hℓY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N (le_trans (le_max_right _ _) hN)
  have hY1 : Y1 ≤ Y := le_max_left _ _
  have hY2 : Y2 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY3 : Y3 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hnG : SharpOutputSize.graphSizeCutoff Δ γ ε ≤ n := by
    have h1 : Δ * SharpOutputSize.graphSizeCutoff Δ γ ε ≤ Δ * n := by
      have : 2 * N ≤ Δ * n := le_trans (by omega) hmn
      omega
    exact Nat.le_of_mul_le_mul_left h1 hΔ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hℓ0 : 0 ≤ Real.logb 2 N :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N))
  have hY1' : Y1 ≤ Real.logb 2 N + 2 := by linarith
  have hY2' : Y2 ≤ Real.logb 2 N + 2 := by linarith
  have hL := L_le p N n εr hεr0 (by linarith) hN2 hn1 hsize hY1'
  obtain ⟨hk1, hklog⟩ := k_log_ge N εr hεr0 (by linarith) hN2 hY2'
  have hY2pos : (1 : ℝ) ≤ Y2 := by
    have : (1 : ℝ) ≤ (3 * 2 + 1 + 2) / εr + 1 := by
      have : (0 : ℝ) ≤ (3 * 2 + 1 + 2) / εr := by positivity
      linarith
    show (1 : ℝ) ≤ ((3 * 2 + 1 + 2) / εr + 1) ^ 2
    exact one_le_pow₀ this
  have hℓpos : 0 < Real.logb 2 N := by linarith
  have hkI : SharpOutputSize.iterationCutoff ε ≤ kOf N := by
    have hIcR : (1 : ℝ) ≤ Icut := by exact_mod_cast (le_max_left 1 _)
    have hkpos : (0 : ℝ) < kOf N := by exact_mod_cast hk1
    have hlog : Real.logb 2 Icut ≤ Real.logb 2 (kOf N) := by
      have : Real.logb 2 Icut ≤ (1 - εr) * Real.logb 2 N := by
        have h3 : 2 * Real.logb 2 Icut + 1 ≤ Real.logb 2 N := by linarith
        nlinarith
      linarith
    have hle := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by linarith) hkpos).mp hlog
    have : Icut ≤ kOf N := by exact_mod_cast hle
    exact le_trans (le_max_right _ _) this
  have hsharp := SharpOutputSize.at_graph_size_printed_entries_le_six_plus n m Δ (kOf N) γ ε
    edge hγ hΔ hε0 hincident hdegree hnG hkI
  have hsharpR : (Nat.clog 2 (printedT n m Δ γ (kOf N)) : ℝ) ≤
      (6 + εr) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsharp
    push_cast at h
    simpa [printedT, hεr] using h
  have hG : 2 ≤ SharpOutputSize.graphSizeCutoff Δ γ ε := by
    unfold SharpOutputSize.graphSizeCutoff
    have : 2 ≤ 2 ^ SharpOutputSize.lengthCutoff Δ γ ε := by
      have : 1 ≤ SharpOutputSize.lengthCutoff Δ γ ε := by
        unfold SharpOutputSize.lengthCutoff; omega
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by decide) this
    omega
  have hLpos : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hlow := two_pow_le_entries (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
    (coverDepth n m (Nat.clog 2 n) Δ γ) (kOf N) hLpos
  have hT1 : 1 ≤ printedT n m Δ γ (kOf N) := le_trans Nat.one_le_two_pow hlow
  have hXk : (kOf N : ℝ) ≤ Real.logb 2 (printedT n m Δ γ (kOf N)) := by
    have hTR : (2 : ℝ) ^ (kOf N) ≤ (printedT n m Δ γ (kOf N) : ℝ) := by
      exact_mod_cast hlow
    have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
      (lt_of_lt_of_le (by positivity) hTR)).mpr hTR
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at this
  have hX := (logb_le_clog _ hT1).trans hsharpR
  have hkR0 : (0 : ℝ) ≤ kOf N := by positivity
  have hup : Real.logb 2 (printedT n m Δ γ (kOf N)) ≤
      (6 + εr) * (1 + εr) * (kOf N : ℝ) * Real.logb 2 N := by
    have h6k : 0 ≤ (6 + εr) * (kOf N : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hL h6k
    nlinarith
  have hkpos : (0 : ℝ) < kOf N := by exact_mod_cast hk1
  have hll : Real.logb 2 (kOf N) ≤ Real.logb 2 (Real.logb 2 (printedT n m Δ γ (kOf N))) :=
    (Real.logb_le_logb (by norm_num) hkpos (by linarith)).mpr hXk
  exact ⟨hk1, hXk, hup, hklog.trans hll⟩

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **A4-S7 on the actual T10 source.** For every sparsity density `cs` and rational
`0 < ε ≤ 1/100`, beyond an explicit `N₀`, every valid `Φ` with `clauses ≤ cs·N`
(`N = Φ.val.variables`) has, for `T = printedT` of its T10 graph at `kOf N`:
`kOf N ≤ log₂T ≤ (6+ε)(1+ε)·kOf N·log₂N`, `(1-ε)·log₂N ≤ log₂log₂T`, `1 ≤ kOf N`. The T45
relations are derived (`T10Size.t45_relations`, `t45_shell_form`). Does not close a ledger row. -/
theorem log_bounds_t10 (cs : ℕ) (ε : ℚ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      1 ≤ kOf Φ.val.variables ∧
      (kOf Φ.val.variables : ℝ) ≤ Real.logb 2 (printedT (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B) (kOf Φ.val.variables)) ∧
      Real.logb 2 (printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)) ≤
        (6 + (ε : ℝ)) * (1 + (ε : ℝ)) * (kOf Φ.val.variables : ℝ) *
          Real.logb 2 Φ.val.variables ∧
      (1 - (ε : ℝ)) * Real.logb 2 Φ.val.variables ≤
        Real.logb 2 (Real.logb 2 (printedT (t10Graph D B Φ).vertices
          (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B)
          (kOf Φ.val.variables))) := by
  obtain ⟨N₀', hN₀'⟩ := log_bounds B.degreeBound (sourceGap D B) (source_gap_pos D B)
    (by have := B.degreeBound_pos; omega) (D.sizeExponent + 2) ε hε0 hε1
  refine ⟨max N₀' (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)), ?_⟩
  intro Φ hsparse hN
  haveI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  obtain ⟨hNm, hmn, _⟩ := T10Size.t45_relations D B Φ
  have hsize := T10Size.t45_shell_form D B cs Φ hsparse (le_trans (le_max_right _ _) hN)
  exact hN₀' Φ.val.variables (le_trans (le_max_left _ _) hN) _ _
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) hinc hdeg hNm hmn
    hsize

#print axioms sq_le_two_pow_pred
#print axioms kOf_pos
#print axioms kOf_35
#print axioms log_bounds
#print axioms log_bounds_t10

end Paper2.Unit4Shell.AsymptoticsExplicit
