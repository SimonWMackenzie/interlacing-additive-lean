import CurrentAdditive.QuarticLegacyFrontBridge
import Paper2.QIdent

/-! The existing physical Q producer is generic in its unary width input.
This file identifies its value, with that input set to the quartic width,
with the literal v27 rational schedule. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront

open CurrentAdditive.RandomizedSchedule
open SourceProfileParameters

theorem quartic_ceil_threshold (n m L Δ a b s w : ℕ) (γ : ℚ)
    (hγab : γ = (a : ℚ) / (b : ℚ))
    (ha : 0 < a) (hb : 0 < b) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hs : width L = s) (hw : width27 L = w) :
    ⌈RestorationPublicQScratch.threshold L
        (deltaU27 (V := Fin n) (E := Fin m) L γ Δ)⌉₊ =
      max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w))
        (QProducer.A3 a b L s w) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hΔQ : (0 : ℚ) < Δ := by exact_mod_cast hΔ
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hγ : 0 < γ := by rw [hγab]; positivity
  obtain ⟨vt, hvt⟩ : ∃ vt : ℚ, vt = γ * (m : ℚ) / (2 * (Δ : ℚ) * (n : ℚ)) := ⟨_, rfl⟩
  obtain ⟨cw, hcw⟩ : ∃ cw : ℚ, cw = 1 / 256 * (γ / 24) := ⟨_, rfl⟩
  have hvt_pos : 0 < vt := by rw [hvt]; positivity
  have hcw_pos : 0 < cw := by rw [hcw]; positivity
  have hthr : RestorationPublicQScratch.threshold L
      (deltaU27 (V := Fin n) (E := Fin m) L γ Δ) =
      ((QProducer.C0 L s w : ℕ) : ℚ) / min (min 1 vt) cw := by
    unfold RestorationPublicQScratch.threshold deltaU27
      SourceRationalScheduleScratch.eta SourceRationalScheduleScratch.vertexTolerance
      SourceRationalScheduleScratch.witnessDensity
    rw [Fintype.card_fin, Fintype.card_fin, hs, hw, ← hvt, ← hcw,
      div_div_eq_mul_div, div_div_eq_mul_div]
    exact congrArg (· / min (min 1 vt) cw) (by unfold QProducer.C0; push_cast; ring)
  rw [hthr, QProducer.div_min _ _ _ (Nat.cast_nonneg _) (lt_min one_pos hvt_pos) hcw_pos,
    QProducer.div_min _ _ _ (Nat.cast_nonneg _) one_pos hvt_pos,
    QProducer.ceil_max, QProducer.ceil_max, div_one, Nat.ceil_natCast]
  have h2 : ((QProducer.C0 L s w : ℕ) : ℚ) / vt =
      ((QProducer.C0 L s w * (2 * b * Δ) * n : ℕ) : ℚ) / ((a * m : ℕ) : ℚ) := by
    rw [hvt, hγab]
    push_cast
    field_simp
  have h3 : ((QProducer.C0 L s w : ℕ) : ℚ) / cw =
      ((QProducer.C0 L s w * (6144 * b) : ℕ) : ℚ) / ((a : ℕ) : ℚ) := by
    rw [hcw, hγab]
    push_cast
    field_simp
    ring
  rw [h2, h3, QProducer.ceil_div_nat _ _ (Nat.mul_pos ha hm),
    QProducer.ceil_div_nat _ _ ha]
  unfold QProducer.A2 QProducer.A3
  have e3 : a + QProducer.C0 L s w * (6144 * b) - 1 =
      a - 1 + QProducer.C0 L s w * (6144 * b) := by omega
  rw [e3]

/-- The old, *physical* Q producer computes this exact v27 value when its
width input is the quartic width. -/
theorem qVal_quartic_eq_Q27 (n m L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m) :
    QProducer.qVal γ.num.toNat γ.den Δ n m L (width L) (width27 L) =
      Q27 (V := Fin n) (E := Fin m) L γ Δ := by
  have hnum : 0 < γ.num := Rat.num_pos.mpr hγ
  have haq : ((γ.num.toNat : ℕ) : ℚ) = (γ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have ha : 0 < γ.num.toNat := by omega
  have hγab : γ = ((γ.num.toNat : ℕ) : ℚ) / ((γ.den : ℕ) : ℚ) := by
    rw [haq, Rat.num_div_den]
  unfold Q27 RestorationPublicQScratch.publicQ SourcePadding.powTwoCeil QProducer.qVal
  rw [quartic_ceil_threshold n m L Δ γ.num.toNat γ.den (width L) (width27 L)
    γ hγab ha γ.den_pos hΔ hn hm rfl rfl]

end Paper2.CurrentAdditive.QuarticNumericFront

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.quartic_ceil_threshold
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.qVal_quartic_eq_Q27
