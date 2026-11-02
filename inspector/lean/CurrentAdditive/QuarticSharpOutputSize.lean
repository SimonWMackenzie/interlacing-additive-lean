import CurrentAdditive.QuarticSharpRelative
import CurrentAdditive.QuarticSourceSize
import Paper2.SharpOutputSize

namespace CurrentAdditive.QuarticSharpOutputSize

open Paper2 Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
  CurrentAdditive.RandomizedSchedule

def lengthCutoff27 (Δ : ℕ) (γ ε : ℚ) : ℕ :=
  max (QuarticSharpRelative.cutoff Δ γ (ε / 12))
    (max 16 (Nat.ceil (8 / ε)))

def iterationCutoff27 (ε : ℚ) : ℕ := Nat.ceil (28 / ε)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem printed_entries_le_six_plus27 (n m L Δ k : ℕ) [NeZero n]
    (γ ε : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (hL : lengthCutoff27 Δ γ ε ≤ L)
    (hk : iterationCutoff27 ε ≤ k) :
    (Nat.clog 2 (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k *
      sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) : ℚ) ≤
      (6 + ε) * (k : ℚ) * (L : ℚ) := by
  let h := overhead27 (V := Fin n) (E := Fin m) L Δ γ
  let d₀ := LookupSeed.exponent L + 1
  let r := 4 * RestorationWidthScheduleScratch.ell L
  let q := q27 (V := Fin n) (E := Fin m) L γ Δ
  let B := sourceBudget L r q k
  let T := sourceRows L r q k * sourceCols L r q k
  have hL16 : 16 ≤ L := by unfold lengthCutoff27 at hL; omega
  have hL1 : 1 ≤ L := by omega
  have hseed : d₀ ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hseed⟩
    exact hseed
  have hB : B = d₀ + k * h := by
    dsimp [B, sourceBudget, d₀, h, overhead27, r, q]
  have hδpos : 0 < ε / 12 := by positivity
  have hδ : (h : ℚ) ≤ (1 + ε / 12) * (L : ℚ) := by
    have hcut : QuarticSharpRelative.cutoff Δ γ (ε / 12) ≤ L := by
      unfold lengthCutoff27 at hL
      omega
    exact (QuarticSharpRelative.relative_overhead27
      (V := Fin n) (E := Fin m) edge L Δ γ (ε / 12)
      hcut hγ hΔ hδpos hincident hdegree).2
  have hK : (28 : ℚ) ≤ ε * (k : ℚ) := by
    have hc : (28 : ℚ) / ε ≤ (iterationCutoff27 ε : ℚ) := Nat.le_ceil _
    have hn : (iterationCutoff27 ε : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have h := (div_le_iff₀ hε).mp (hc.trans hn)
    nlinarith
  have hLε : (8 : ℚ) ≤ ε * (L : ℚ) := by
    have hn : Nat.ceil ((8 : ℚ) / ε) ≤ L := by
      unfold lengthCutoff27 at hL
      omega
    have hc : (8 : ℚ) / ε ≤ (Nat.ceil ((8 : ℚ) / ε) : ℚ) := Nat.le_ceil _
    have hnq : (Nat.ceil ((8 : ℚ) / ε) : ℚ) ≤ (L : ℚ) := by exact_mod_cast hn
    have h := (div_le_iff₀ hε).mp (hc.trans hnq)
    nlinarith
  have hBound := Paper2.SharpOutputSize.entries_le_sharp_budget L r q k hL1
  have hclogNat : Nat.clog 2 T ≤ 6 * B + 2 * k + 14 := by
    exact Nat.clog_le_of_le_pow hBound
  have hclog : (Nat.clog 2 T : ℚ) ≤ 6 * (B : ℚ) + 2 * (k : ℚ) + 14 := by
    exact_mod_cast hclogNat
  have hBq : (B : ℚ) ≤ (L : ℚ) + (k : ℚ) * ((1 + ε / 12) * (L : ℚ)) := by
    have hseedq : (d₀ : ℚ) ≤ (L : ℚ) := by exact_mod_cast hseed
    have hkh := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg k : (0 : ℚ) ≤ k)
    rw [hB]
    push_cast
    linarith
  have hLq : (14 : ℚ) ≤ (L : ℚ) := by exact_mod_cast (show 14 ≤ L by omega)
  have hKq : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hLq0 : (0 : ℚ) ≤ L := Nat.cast_nonneg L
  have hseedTerm : 7 * (L : ℚ) ≤ (ε / 4) * (k : ℚ) * (L : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_right hK hLq0]
  have hextraTerm : 2 * (k : ℚ) ≤ (ε / 4) * (k : ℚ) * (L : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_left hLε hKq]
  change (Nat.clog 2 T : ℚ) ≤ (6 + ε) * (k : ℚ) * (L : ℚ)
  nlinarith

def graphSizeCutoff27 (Δ : ℕ) (γ ε : ℚ) : ℕ :=
  max (CurrentAdditive.QuarticSchedule.threshold27 Δ γ)
    (2 ^ lengthCutoff27 Δ γ ε)

theorem at_graph_size_printed_entries_le_six_plus27
    (n m Δ k : ℕ) [NeZero n]
    (γ ε : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hn : graphSizeCutoff27 Δ γ ε ≤ n)
    (hk : iterationCutoff27 ε ≤ k) :
    (Nat.clog 2 (sourceRows (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k *
      sourceCols (Nat.clog 2 n)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
        (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k) : ℚ) ≤
      (6 + ε) * (k : ℚ) * (Nat.clog 2 n : ℚ) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (NeZero.pos n)
  have hsize : CurrentAdditive.QuarticSchedule.threshold27 Δ γ ≤ n := by
    unfold graphSizeCutoff27 at hn
    omega
  have hL : lengthCutoff27 Δ γ ε ≤ Nat.clog 2 n := by
    have hpow : 2 ^ lengthCutoff27 Δ γ ε ≤ n := by
      unfold graphSizeCutoff27 at hn
      omega
    have hc := Nat.clog_mono_right 2 hpow
    simpa only [Nat.clog_pow 2 (lengthCutoff27 Δ γ ε) (by decide)] using hc
  have hchecks : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ := by
    have hh := CurrentAdditive.QuarticSchedule.all_large_checks27_at_graph
      (V := Fin n) (Edges := Fin m) edge Δ γ hγ hΔ hincident hdegree
      (by simpa only [Fintype.card_fin] using hsize)
    simpa only [Fintype.card_fin] using hh
  exact printed_entries_le_six_plus27 n m (Nat.clog 2 n) Δ k γ ε edge
    hγ hΔ hε hincident hdegree hchecks hL hk

#print axioms printed_entries_le_six_plus27
#print axioms at_graph_size_printed_entries_le_six_plus27

end CurrentAdditive.QuarticSharpOutputSize
