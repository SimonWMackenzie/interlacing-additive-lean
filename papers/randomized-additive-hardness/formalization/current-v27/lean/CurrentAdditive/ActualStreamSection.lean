import CurrentAdditive.DeterministicIndexedStreamConditioning
import CurrentAdditive.GeneratedSelectorTransfer

/-!
The actual internal interlace uses a right-associated product of complete
metadata, base-label, and selector-index streams.  Fixing both first
indices leaves the third *whole* stream with its original law.  This is
before a separate retained-section condition and does not assert that a
retained section remains independent.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources.InternalStreams

open Paper2 Paper2.FiniteLaw

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

/-- On the actual right-associated stream law, conditioning on *complete*
metadata and base-label indices leaves every event of the entire selector
index stream unchanged. -/
theorem fixed_whole_selector_event
    (m : streams.metadataStream.Label) (b : streams.baseStream.Label)
    (E : streams.selectorStream.Label → Prop) :
    (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b ∧ E a.2.2) /
      (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b) =
      streams.selectorStream.law.toFiniteLaw.prob E := by
  let ρ := streams.metadataStream.law.toFiniteLaw
  let σ := streams.baseStream.law.toFiniteLaw
  let τ := streams.selectorStream.law.toFiniteLaw
  have hlaw : streams.law.toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, law, PositiveRationalLaw.toFiniteLaw_prod]
  rw [hlaw]
  have hnum : (ρ.prod (σ.prod τ)).prob
        (fun a => a.1 = m ∧ a.2.1 = b ∧ E a.2.2) =
      ρ.weight m * σ.weight b * τ.prob E := by
    rw [FiniteLaw.prod_prob_fixed_fst ρ (σ.prod τ) m
      (fun a => a.1 = b ∧ E a.2)]
    rw [FiniteLaw.prod_prob_fixed_fst σ τ b E]
    ring
  have hden : (ρ.prod (σ.prod τ)).prob
        (fun a => a.1 = m ∧ a.2.1 = b) =
      ρ.weight m * σ.weight b := by
    rw [FiniteLaw.prod_prob_fixed_fst ρ (σ.prod τ) m
      (fun a => a.1 = b)]
    have hb := FiniteLaw.prod_prob_fixed_fst σ τ b (fun _ => True)
    simp only [FiniteLaw.prob_true, mul_one] at hb
    simpa only [and_true] using congrArg (fun v => ρ.weight m * v) hb
  have hm : 0 < ρ.weight m := by
    change (0 : ℝ) < (streams.metadataStream.law.weight m : ℝ)
    exact_mod_cast streams.metadataStream.law.positive m
  have hb : 0 < σ.weight b := by
    change (0 : ℝ) < (streams.baseStream.law.weight b : ℝ)
    exact_mod_cast streams.baseStream.law.positive b
  rw [hnum, hden]
  exact mul_div_cancel_left₀ (τ.prob E) (ne_of_gt (mul_pos hm hb))

/-- Every at most-D set of flattened selector coordinates has the exact
product marginal after the two complete metadata indices are fixed. -/
theorem fixed_flattened_event
    (m : streams.metadataStream.Label) (b : streams.baseStream.Label)
    (C : Finset (Fin w × Fin q₂)) (hC : C.card ≤ D)
    (E : (C → Fin q₁ × X) → Prop) :
    (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b ∧
          E (fun p : C => src.inner.decode
            (streams.selectorStream.decode a.2.2 p.val.1) p.val.2)) /
      (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b) =
      (FiniteLaw.pi (fun _ : C =>
        ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)).prob E := by
  rw [fixed_whole_selector_event src streams m b
    (fun t => E (fun p : C => src.inner.decode
      (streams.selectorStream.decode t p.val.1) p.val.2))]
  classical
  exact CurrentAdditive.flatten_dwise D src.inner.law.toFiniteLaw
    streams.selectorStream.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    src.inner.decode streams.selectorStream.decode
    src.inner.exactLaw streams.selectorStream.exactLaw C hC E

/-- A retained selector section is projected to *actual* surviving
flattened words after fixing metadata. Its ambient product-image mass is
at least the section's conditional mass; no product law is assigned to
the retained section itself. -/
theorem fixed_flattened_image_mass
    (m : streams.metadataStream.Label) (b : streams.baseStream.Label)
    (C : Finset (Fin w × Fin q₂)) (hC : C.card ≤ D)
    (K : Set streams.selectorStream.Label) :
    (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b ∧ a.2.2 ∈ K) /
      (streams.law.toFiniteLaw).prob
        (fun a => a.1 = m ∧ a.2.1 = b) ≤
      (FiniteLaw.pi (fun _ : C =>
        ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)).prob
        (· ∈ (fun t (p : C) => src.inner.decode
          (streams.selectorStream.decode t p.val.1) p.val.2) '' K) := by
  rw [fixed_whole_selector_event src streams m b (· ∈ K)]
  exact CurrentAdditive.GeneratedSelectorTransfer.selected_flatten_image_mass
    D src.inner.law.toFiniteLaw streams.selectorStream.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    src.inner.decode streams.selectorStream.decode
    src.inner.exactLaw streams.selectorStream.exactLaw C hC K

end CurrentAdditive.DeterministicIndexedMatrix.Sources.InternalStreams

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.InternalStreams.fixed_whole_selector_event
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.InternalStreams.fixed_flattened_event
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.InternalStreams.fixed_flattened_image_mass
