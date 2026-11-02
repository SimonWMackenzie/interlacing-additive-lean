import Paper2.SCCaps

/-! Lane a-success-clock-owner-2: the maximum encoded lengths of the level-`k`
codecs that one level step reads are bounded by the maximum lengths of the two
level-`k+1` carrier codecs (literal production `carrierCodecs`). Pure arithmetic. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.SuccessClock2

open Paper2.RecursiveLabelCodecScratch

theorem maxLen_derived {X₀ Y₀ I : Type} (s q₁ q₂ w Q : ℕ) (hs : 1 ≤ s) (hq₂ : 1 ≤ q₂)
    (hw : 1 ≤ w) (hQ : 1 ≤ Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀) (ci : PrefixCodec I) (k : ℕ) :
    let C := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k
    let C' := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci (k + 1)
    (outerColumnCodec q₁ q₂ s C.2).maxLen ≤ C'.1.maxLen ∧
    (piCodec (outerColumnCodec q₁ q₂ s C.2) s).maxLen ≤ C'.1.maxLen ∧
    (piCodec C.2 (s + 1)).maxLen ≤ C'.1.maxLen ∧
    (piCodec C.2 (q₁ + s + 1)).maxLen ≤ C'.1.maxLen ∧
    (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).maxLen ≤ C'.1.maxLen ∧
    (taggedColumnCodec q₁ q₂ s C.2).maxLen ≤ C'.1.maxLen ∧
    C.2.maxLen ≤ C'.1.maxLen ∧
    (rawRowCodec q₁ q₂ s C.1 ci).maxLen ≤ C'.2.maxLen ∧
    (prodCodec (finCodec q₁) C.1).maxLen ≤ C'.2.maxLen ∧
    C.1.maxLen ≤ C'.2.maxLen := by
  intro C C'
  have e1 : C'.1.maxLen = Q * (w + (taggedColumnCodec q₁ q₂ s C.2).maxLen) := by
    show (piCodec (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)) Q).maxLen = _
    rw [piCodec_maxLen]; rfl
  have e2 : C'.2.maxLen = Q + w * (rawRowCodec q₁ q₂ s C.1 ci).maxLen := by
    show (prodCodec (finCodec Q) (piCodec (rawRowCodec q₁ q₂ s C.1 ci) w)).maxLen = _
    show Q + (piCodec (rawRowCodec q₁ q₂ s C.1 ci) w).maxLen = _
    rw [piCodec_maxLen]
  have eo : (outerColumnCodec q₁ q₂ s C.2).maxLen = q₂ + (q₁ + s + 1) * C.2.maxLen := by
    show q₂ + (piCodec C.2 (q₁ + s + 1)).maxLen = _
    rw [piCodec_maxLen]
  have et : (taggedColumnCodec q₁ q₂ s C.2).maxLen =
      1 + max ((s + 1) * C.2.maxLen + s * (outerColumnCodec q₁ q₂ s C.2).maxLen)
        (1 + max (s * (outerColumnCodec q₁ q₂ s C.2).maxLen)
          (outerColumnCodec q₁ q₂ s C.2).maxLen) := by
    show 1 + max ((piCodec C.2 (s + 1)).maxLen +
        (piCodec (outerColumnCodec q₁ q₂ s C.2) s).maxLen)
      (1 + max (piCodec (outerColumnCodec q₁ q₂ s C.2) s).maxLen
        (outerColumnCodec q₁ q₂ s C.2).maxLen) = _
    rw [piCodec_maxLen, piCodec_maxLen]
  have er : (rawRowCodec q₁ q₂ s C.1 ci).maxLen =
      1 + max (s + q₂ * (q₁ + C.1.maxLen)) (ci.maxLen + C.1.maxLen) := by
    show 1 + max (s + (piCodec (prodCodec (finCodec q₁) C.1) q₂).maxLen)
      (ci.maxLen + C.1.maxLen) = _
    rw [piCodec_maxLen]; rfl
  have hpo : (piCodec (outerColumnCodec q₁ q₂ s C.2) s).maxLen =
      s * (outerColumnCodec q₁ q₂ s C.2).maxLen := piCodec_maxLen _ _
  have hp1 : (piCodec C.2 (s + 1)).maxLen = (s + 1) * C.2.maxLen := piCodec_maxLen _ _
  have hp2 : (piCodec C.2 (q₁ + s + 1)).maxLen = (q₁ + s + 1) * C.2.maxLen := piCodec_maxLen _ _
  have hpw : (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).maxLen =
      w + (taggedColumnCodec q₁ q₂ s C.2).maxLen := rfl
  have hpq : (prodCodec (finCodec q₁) C.1).maxLen = q₁ + C.1.maxLen := rfl
  -- generalize the atoms
  generalize (taggedColumnCodec q₁ q₂ s C.2).maxLen = T at *
  generalize (outerColumnCodec q₁ q₂ s C.2).maxLen = O at *
  generalize (rawRowCodec q₁ q₂ s C.1 ci).maxLen = R at *
  generalize C.2.maxLen = y at *
  generalize C.1.maxLen = x at *
  have m1 : w + T ≤ Q * (w + T) := Nat.le_mul_of_pos_left _ (by omega)
  have m2 : R ≤ w * R := Nat.le_mul_of_pos_left _ (by omega)
  have m3 : y ≤ (q₁ + s + 1) * y := Nat.le_mul_of_pos_left _ (by omega)
  have m4 : q₁ + x ≤ q₂ * (q₁ + x) := Nat.le_mul_of_pos_left _ (by omega)
  have m5 : O ≤ s * O := Nat.le_mul_of_pos_left _ (by omega)
  have m6 : (s + 1) * y ≤ (q₁ + s + 1) * y := Nat.mul_le_mul_right _ (by omega)
  have mx1 := le_max_left ((s + 1) * y + s * O) (1 + max (s * O) O)
  have mx2 := le_max_right ((s + 1) * y + s * O) (1 + max (s * O) O)
  have mx3 := le_max_left (s * O) O
  have mx4 := le_max_left (s + q₂ * (q₁ + x)) (ci.maxLen + x)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.maxLen_derived
