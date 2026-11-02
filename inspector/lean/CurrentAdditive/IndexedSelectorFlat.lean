import CurrentAdditive.IndexedTemplateSection

/-! Appendix I `det:incoming`: exact flattened selector law after complete
metadata and base streams are fixed. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

/-- The selector stream still has exactly D-wise J marginals on distinct
flattened `(outer position, inner address)` coordinates. -/
theorem selector_flatten_dwise :
    IsDWise D streams.selectorStream.law.toFiniteLaw
      (fun sel (p : Fin w × Fin q₂) =>
        src.inner.decode (streams.selectorStream.decode sel p.1) p.2)
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
  exact flatten_dwise D src.inner.law.toFiniteLaw
    streams.selectorStream.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    src.inner.decode streams.selectorStream.decode
    src.inner.exactLaw streams.selectorStream.exactLaw

/-- The same D-wise law holds as a conditional probability on the original
three-stream product after fixing both complete nonselector indices. -/
theorem fixed_stream_flatten_dwise
    (md : streams.metadataStream.Label)
    (base : streams.baseStream.Label)
    (S : Finset (Fin w × Fin q₂)) (hS : S.card ≤ D)
    (E : (S → Fin q₁ × X) → Prop) :
    streams.law.toFiniteLaw.prob
        (fun a => a.1 = md ∧ a.2.1 = base ∧
          E (fun p : S => src.inner.decode
            (streams.selectorStream.decode a.2.2 p.val.1) p.val.2)) /
      streams.law.toFiniteLaw.prob
        (fun a => a.1 = md ∧ a.2.1 = base) =
      (FiniteLaw.pi (fun _ : S =>
        ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)).prob E := by
  let ρ := streams.metadataStream.law.toFiniteLaw
  let σ := streams.baseStream.law.toFiniteLaw
  let τ := streams.selectorStream.law.toFiniteLaw
  have hlaw : streams.law.toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, Sources.InternalStreams.law,
      PositiveRationalLaw.toFiniteLaw_prod]
  rw [hlaw]
  have hnum : (ρ.prod (σ.prod τ)).prob
        (fun a => a.1 = md ∧ a.2.1 = base ∧
          E (fun p : S => src.inner.decode
            (streams.selectorStream.decode a.2.2 p.val.1) p.val.2)) =
      ρ.weight md * σ.weight base *
        τ.prob (fun sel => E (fun p : S => src.inner.decode
          (streams.selectorStream.decode sel p.val.1) p.val.2)) := by
    rw [FiniteLaw.prod_prob_fixed_fst ρ (σ.prod τ) md
      (fun a => a.1 = base ∧
        E (fun p : S => src.inner.decode
          (streams.selectorStream.decode a.2 p.val.1) p.val.2))]
    rw [FiniteLaw.prod_prob_fixed_fst σ τ base
      (fun sel => E (fun p : S => src.inner.decode
        (streams.selectorStream.decode sel p.val.1) p.val.2))]
    ring
  have hden : (ρ.prod (σ.prod τ)).prob
        (fun a => a.1 = md ∧ a.2.1 = base) =
      ρ.weight md * σ.weight base := by
    have houter := FiniteLaw.prod_prob_fixed_fst ρ (σ.prod τ) md
      (fun a => a.1 = base)
    have hinner := FiniteLaw.prod_prob_fixed_fst σ τ base (fun _ => True)
    simp only [FiniteLaw.prob_true, mul_one] at hinner
    have hinner' : (σ.prod τ).prob (fun a => a.1 = base) = σ.weight base := by
      simpa only [and_true] using hinner
    rw [houter, hinner']
  have hmd : 0 < ρ.weight md := by
    change (0 : ℝ) < (streams.metadataStream.law.weight md : ℝ)
    exact_mod_cast streams.metadataStream.law.positive md
  have hbase : 0 < σ.weight base := by
    change (0 : ℝ) < (streams.baseStream.law.weight base : ℝ)
    exact_mod_cast streams.baseStream.law.positive base
  rw [hnum, hden]
  have hnon : ρ.weight md * σ.weight base ≠ 0 :=
    ne_of_gt (mul_pos hmd hbase)
  calc
    _ = τ.prob (fun sel => E (fun p : S => src.inner.decode
          (streams.selectorStream.decode sel p.val.1) p.val.2)) := by
      rw [mul_div_cancel_left₀ _ hnon]
    _ = _ := (selector_flatten_dwise src streams) S hS E

#print axioms selector_flatten_dwise
#print axioms fixed_stream_flatten_dwise

end CurrentAdditive.DeterministicIndexedMatrix
