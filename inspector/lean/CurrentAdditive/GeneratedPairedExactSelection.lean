import CurrentAdditive.GeneratedPairedSelectors
import CurrentAdditive.ExactBoost

/-! Source-specific terminal call for Appendix I `det:paired`.  The
underlying row inputs are two complete indexed selector labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open CurrentAdditive.ArbitraryPrefix

/-- Injectively selecting coordinates of a bounded-wise indexed source
preserves its bounded-wise product marginals. -/
theorem dwise_comp_injective
    {I K A Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] [Fintype A] [Fintype Ω]
    (D : ℕ) (ρ : FiniteLaw Ω) (μ : FiniteLaw A)
    (draw : Ω → I → A) (hwise : IsDWise D ρ draw μ)
    (e : K → I) (he : Function.Injective e) :
    IsDWise D ρ (fun ω k => draw ω (e k)) μ := by
  classical
  intro s hs E
  let t : Finset I := s.image e
  have ht : t.card ≤ D := (Finset.card_image_le).trans hs
  have hemem (k : s) : e k.val ∈ t :=
    Finset.mem_image.mpr ⟨k.val, k.property, rfl⟩
  let f : s → t := fun k => ⟨e k.val, hemem k⟩
  have hf : Function.Injective f := by
    intro k l h
    exact Subtype.ext (he (congrArg Subtype.val h))
  let E' : (t → A) → Prop := fun z => E (fun k => z (f k))
  calc
    ρ.prob (fun ω => E (fun k : s => draw ω (e k.val))) =
        (FiniteLaw.pi (fun _ : t => μ)).prob E' := by
      simpa only [E', f] using hwise t ht E'
    _ = (FiniteLaw.pi (fun _ : s => μ)).prob E := by
      simpa only [E', FiniteLaw.iid] using
        (FiniteLaw.pi_prob_restrict (fun _ : t => μ) f hf E)

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- On any selected distinct tagged blocks, `det:exact` applies to the
actual pair-source labels.  It uses only eight-wise marginals of the
original pair law, not independence of a retained pair set. -/
theorem selected_paired_exact_lower
    (R₀ : X → Y → Bool) (d a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (d : ℤ))
    (e : Fin n → Bool × Fin q₂) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (Rows : Fin n → Set src.gamma.Label)
    (hrow : ∀ i : Fin n,
      (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (9/25 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K)) :
    d+a ≤ Compression.restrictionD
      (fun (u : Fin n × src.gamma.Label) z =>
        pairedIndexed src R₀ z ((e u.1).1, ((e u.1).2, u.2)))
      (rowRectangle Finset.univ Rows) K := by
  have hwiseD := dwise_comp_injective D
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    (taggedDecode src) (pair_tagged_exact src) e he
  have hwise8 : IsDWise 8
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      (fun z (i : Fin n) => taggedDecode src z (e i))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
    intro J hJ E
    exact hwiseD J (hJ.trans hD) E
  have hcount' : 2^(a-1)+1 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hcount
  have hrow' : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _
    exact hrow i
  simpa only [pairedIndexed_entry] using
    exactboost src.gamma.law
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
      (A src R₀)
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      (fun z (i : Fin n) => taggedDecode src z (e i))
      hwise8 Finset.univ Rows K d a x ha hd hx hscale hprofile
      hcount' hrow' hK

#print axioms dwise_comp_injective
#print axioms selected_paired_exact_lower

end CurrentAdditive.DeterministicIndexedMatrix.Sources
