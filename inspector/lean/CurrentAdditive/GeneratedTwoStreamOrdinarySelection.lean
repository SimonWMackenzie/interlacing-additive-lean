import CurrentAdditive.GeneratedPairedObstruction
import CurrentAdditive.GeneratedOuterOrdinary
import CurrentAdditive.ExactBoost

/-! Selected ordinary bins in Appendix I `det:two-stream`: the whole
ordinary source is indexed, while only its bounded-size marginals are iid. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open CurrentAdditive.ArbitraryPrefix

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The complete ordinary index/tail product has the outer source's
bounded-wise bin law. This does not assert full independence of all s bins. -/
theorem ordinary_dwise :
    IsDWise D (ordinaryLaw src).toFiniteLaw
      (fun c (i : Fin s) => src.outer.decode c.1 i)
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw := by
  intro C hC E
  calc
    (ordinaryLaw src).toFiniteLaw.prob
        (fun c => E (fun i : C => src.outer.decode c.1 i.val)) =
      src.outer.law.toFiniteLaw.prob
        (fun js => E (fun i : C => src.outer.decode js i.val)) :=
        ordinary_first_marginal src
          (fun js => E (fun i : C => src.outer.decode js i.val))
    _ = (FiniteLaw.pi (fun _ : C =>
          ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)).prob E :=
      src.outer.exactLaw C hC E

/-- The exact suffix theorem on any distinct selected ordinary bins,
keeping the original ordinary source labels as columns. -/
theorem selected_ordinary_exact_lower
    (R₀ : X → Y → Bool) (H a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (e : Fin n → Fin s) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (Rows : Fin n → Set src.inner.Label)
    (hrow : ∀ i : Fin n,
      (2 : ℝ)^a*x ≤ src.inner.law.toFiniteLaw.prob (· ∈ Rows i))
    (O : Set (src.outer.Label × src.gamma.Label))
    (hO : (9/25 : ℝ) ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O)) :
    H+a ≤ Compression.restrictionD
      (fun (u : Fin n × src.inner.Label) c =>
        T src R₀ u.2 (src.outer.decode c.1 (e u.1)))
      (rowRectangle Finset.univ Rows) O := by
  have hwiseD := dwise_comp_injective D
    (ordinaryLaw src).toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
    (fun c (i : Fin s) => src.outer.decode c.1 i)
    (ordinary_dwise src) e he
  have hwise8 : IsDWise 8 (ordinaryLaw src).toFiniteLaw
      (fun c (i : Fin n) => src.outer.decode c.1 (e i))
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw := by
    intro C hC E
    exact hwiseD C (hC.trans hD) E
  have hcount' : 2^(a-1)+1 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hcount
  have hrow' : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (2 : ℝ)^a*x ≤ src.inner.law.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _
    exact hrow i
  exact exactboost src.inner.law
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law)
    (T src R₀) (ordinaryLaw src).toFiniteLaw
    (fun c (i : Fin n) => src.outer.decode c.1 (e i))
    hwise8 Finset.univ Rows O H a x ha hH hx hscale hprofile
    hcount' hrow' hO

#print axioms ordinary_dwise
#print axioms selected_ordinary_exact_lower

end CurrentAdditive.DeterministicIndexedMatrix.Sources
