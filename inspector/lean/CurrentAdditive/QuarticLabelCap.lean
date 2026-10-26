import CurrentAdditive.QuarticClockCaps

namespace Paper2.CurrentAdditive.QuarticClockCaps

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
  Paper2.GeneratorSize Paper2.RecursiveLabelCodecScratch
open CurrentAdditive.RandomizedSchedule

theorem label_maxLen_cap27 {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin n) (Edges := Fin m) L Δ γ) (k : ℕ) :
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).1.maxLen ≤ 2 ^ (26 * (k + 1) * L) ∧
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).2.maxLen ≤ 2 ^ (26 * (k + 1) * L) := by
  obtain ⟨_, hn, hp, hs, hq₁, hq₂, hw, hQ, _, hL⟩ := scalar_caps27 L Δ γ hc
  let B := 2 ^ (7 * L)
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let ci := defaultItemCodec n s
  let M := max 1 (max p (max p ci.maxLen))
  let T := labelStepCap s (s - 2) (SourceProfileParameters.outerWidth L) (width27 L)
    (Q27 (V := Fin n) (E := Fin m) L γ Δ)
  have hB : 1 ≤ B := Nat.one_le_two_pow
  have hci : ci.maxLen ≤ 6 * B := by
    rw [show ci.maxLen = 4 * s + (1 + max n (s - 3)) from default_item_maxLen n s]
    have : max n (s - 3) ≤ B := max_le hn (le_trans (Nat.sub_le _ _) hs)
    change s ≤ B at hs
    omega
  have hM : M ≤ 8 * B := by
    have hp' : p ≤ B := hp
    dsimp only [M]; omega
  have hT : T ≤ 32 * B ^ 3 := labelStepCap_le_cube _ _ _ _ _ B hB hs hq₁ hq₂ hw hQ
  have hMpow : M ≤ 2 ^ (8 * L) := by
    calc
      M ≤ 8 * B := hM
      _ = 2 ^ (3 + 7 * L) := by norm_num [B, pow_add]
      _ ≤ 2 ^ (8 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hTpow : T ≤ 2 ^ (26 * L) := by
    calc
      T ≤ 32 * B ^ 3 := hT
      _ = 2 ^ (5 + 21 * L) := by
        have he : 21 * L = (7 * L) * 3 := by omega
        rw [he, pow_add, pow_mul]
        norm_num [B]
      _ ≤ 2 ^ (26 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hb := carrierCodecs_maxLen_le s (s - 2) (SourceProfileParameters.outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) (piCodec boolCodec p) (finCodec p) ci k
  simp only [piCodec_maxLen, boolCodec, mul_one] at hb
  have htarget : M * T ^ k ≤ 2 ^ (26 * (k + 1) * L) := by
    have hpow := Nat.pow_le_pow_left hTpow k
    calc
      M * T ^ k ≤ 2 ^ (8 * L) * (2 ^ (26 * L)) ^ k := Nat.mul_le_mul hMpow hpow
      _ = 2 ^ ((8 + 26 * k) * L) := by rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (26 * (k + 1) * L) := by
        have he : 8 + 26 * k ≤ 26 * (k + 1) := by omega
        exact pow_le_pow_right₀ (by omega) (Nat.mul_le_mul_right L he)
  exact ⟨hb.1.trans htarget, hb.2.trans htarget⟩

/-- Label caps at every level `k ≤ K`, in the common exponent `26*T`, `T = (K+1)*L`. -/
theorem label_cap27 {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin n) (Edges := Fin m) L Δ γ)
    (K k : ℕ) (hk : k ≤ K) :
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).1.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) ∧
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).2.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) := by
  have h := label_maxLen_cap27 L Δ γ hc k
  have hm : 2 ^ (26 * (k + 1) * L) ≤ 2 ^ (26 * ((K + 1) * L)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  exact ⟨h.1.trans hm, h.2.trans hm⟩

#print axioms label_maxLen_cap27
#print axioms label_cap27

end Paper2.CurrentAdditive.QuarticClockCaps
