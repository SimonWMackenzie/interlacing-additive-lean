import CurrentAdditive.DeterministicIndexedProfileMass

/-! The selector stream remains exact after fixing whole, independent
metadata and base streams in the actual indexed internal interlace. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources.InternalStreams

variable {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

theorem selector_exact_after_complete_streams
    (m : streams.metadataStream.Label)
    (b : streams.baseStream.Label)
    (S : Finset (Fin w)) (hS : S.card ≤ D)
    (E : (S → src.inner.Label) → Prop) :
    (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b ∧
          E (fun p : S => streams.selectorStream.decode a.2.2 p)) /
      (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b) =
      (Paper2.FiniteLaw.pi (fun _ : S => src.inner.law.toFiniteLaw)).prob E := by
  let ρ := streams.metadataStream.law.toFiniteLaw
  let σ := streams.baseStream.law.toFiniteLaw
  let τ := streams.selectorStream.law.toFiniteLaw
  have hlaw : streams.law.toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, law, PositiveRationalLaw.toFiniteLaw_prod]
  rw [hlaw]
  have hnum : (ρ.prod (σ.prod τ)).prob
        (fun a => a.1 = m ∧ a.2.1 = b ∧
          E (fun p : S => streams.selectorStream.decode a.2.2 p)) =
      ρ.weight m * σ.weight b *
        τ.prob (fun t => E (fun p : S => streams.selectorStream.decode t p)) := by
    rw [Paper2.FiniteLaw.prod_prob_fixed_fst ρ (σ.prod τ) m
      (fun a => a.1 = b ∧
        E (fun p : S => streams.selectorStream.decode a.2 p))]
    rw [Paper2.FiniteLaw.prod_prob_fixed_fst σ τ b
      (fun t => E (fun p : S => streams.selectorStream.decode t p))]
    ring
  have hden : (ρ.prod (σ.prod τ)).prob
        (fun a => a.1 = m ∧ a.2.1 = b) =
      ρ.weight m * σ.weight b := by
    have houter := Paper2.FiniteLaw.prod_prob_fixed_fst ρ (σ.prod τ) m
      (fun a => a.1 = b)
    have hinner := Paper2.FiniteLaw.prod_prob_fixed_fst σ τ b (fun _ => True)
    simp only [Paper2.FiniteLaw.prob_true, mul_one] at hinner
    have hinner' : (σ.prod τ).prob (fun a => a.1 = b) = σ.weight b := by
      simpa only [and_true] using hinner
    rw [houter, hinner']
  have hm : 0 < ρ.weight m := by
    change (0 : ℝ) < (streams.metadataStream.law.weight m : ℝ)
    exact_mod_cast streams.metadataStream.law.positive m
  have hb : 0 < σ.weight b := by
    change (0 : ℝ) < (streams.baseStream.law.weight b : ℝ)
    exact_mod_cast streams.baseStream.law.positive b
  rw [hnum, hden]
  have hnon : ρ.weight m * σ.weight b ≠ 0 := ne_of_gt (mul_pos hm hb)
  calc
    _ = τ.prob (fun t => E (fun p : S => streams.selectorStream.decode t p)) := by
      rw [mul_div_cancel_left₀ _ hnon]
    _ = (Paper2.FiniteLaw.pi (fun _ : S => src.inner.law.toFiniteLaw)).prob E :=
      streams.selectorStream.exactLaw S hS E

end Sources.InternalStreams

end CurrentAdditive.DeterministicIndexedMatrix
