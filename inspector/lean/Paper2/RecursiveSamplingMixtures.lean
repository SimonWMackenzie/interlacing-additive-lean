import Paper2.SourceLawBinding

/-!
# The elementary mixture tickets used by recursive input generation

Frozen v12 Appendix D, input-label generation, and Section 4 `eq:mixture`.
One uniform ticket with denominator 256 chooses the three tagged families;
one with denominator 512 chooses template, vertex and auxiliary rows.
Only these fixed small alphabets are counted here, never a complete matrix
input carrier. The arbitrary-payoff identities preserve the actual labels.
-/

namespace Paper2.RecursiveSamplingMixtures

open SourceMatrix

theorem sum_two_rare (n : ℕ) (a b c : ℝ) :
    (∑ t : Fin (n + 2), if t.val < n then a else if t.val = n then b else c) =
      (n : ℝ) * a + b + c := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hn : ¬ n + 1 < n := by omega
  have hne : n + 1 ≠ n := by omega
  simp only [hn, hne, ↓reduceIte, lt_self_iff_false]
  simp

theorem tagged_ticket_average (a b c : ℝ) :
    (256 : ℝ)⁻¹ *
        (∑ t : Fin 256, if t.val < 254 then a else if t.val = 254 then b else c) =
      (127 / 128 : ℝ) * a + (1 / 256 : ℝ) * b + (1 / 256 : ℝ) * c := by
  rw [sum_two_rare 254]
  norm_num
  ring

theorem row_ticket_average (a b c : ℝ) :
    (512 : ℝ)⁻¹ *
        (∑ t : Fin 512, if t.val < 510 then a else if t.val = 510 then b else c) =
      (255 / 256 : ℝ) * a + (1 / 512 : ℝ) * b + (1 / 512 : ℝ) * c := by
  rw [sum_two_rare 510]
  norm_num
  ring

theorem tagged_expect {Y : Type*} [Fintype Y]
    (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ) [NeZero q₂]
    (f : TaggedColumn q₁ q₂ s Y → ℝ) :
    (∑ Z, (SourceLaws.taggedLaw ν q₁ q₂ s).toFiniteLaw.weight Z * f Z) =
      (127 / 128 : ℝ) *
        (∑ Z, (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.weight Z * f (.unrestricted Z)) +
      (1 / 256 : ℝ) *
        (∑ js, (SourceLaws.fixedTailLaw ν q₁ q₂ s).toFiniteLaw.weight js * f (.fixedTail js)) +
      (1 / 256 : ℝ) *
        (∑ j, (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.weight j * f (.diagonal j)) := by
  rw [SourceLaws.sum_tagged]
  simp only [PositiveRationalLaw.toFiniteLaw, SourceLaws.taggedLaw, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum, mul_assoc]

theorem row_expect {X V A : Type*} [Fintype X] [Fintype V] [Fintype A]
    [Nonempty V] [Nonempty A] (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] (f : RawRow q₁ q₂ s X (V ⊕ A) → ℝ) :
    (∑ k, (SourceLaws.rowLaw μ q₁ q₂ s).toFiniteLaw.weight k * f k) =
      (255 / 256 : ℝ) *
        (∑ k, (SourceLaws.templateRowLaw μ q₁ q₂ s).toFiniteLaw.weight k * f (.inl k)) +
      (1 / 512 : ℝ) *
        (∑ k : V × X, (SourceLaws.itemRowLaw μ V).toFiniteLaw.weight k *
          f (.inr (.inl k.1, k.2))) +
      (1 / 512 : ℝ) *
        (∑ k : A × X, (SourceLaws.itemRowLaw μ A).toFiniteLaw.weight k *
          f (.inr (.inr k.1, k.2))) := by
  rw [SourceLaws.sum_rows]
  simp only [PositiveRationalLaw.toFiniteLaw, SourceLaws.rowLaw, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum, mul_assoc]

end Paper2.RecursiveSamplingMixtures
