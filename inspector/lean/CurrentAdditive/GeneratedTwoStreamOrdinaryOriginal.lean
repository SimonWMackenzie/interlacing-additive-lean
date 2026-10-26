import CurrentAdditive.GeneratedTwoStreamOrdinarySelection
import Paper2.TwoStreamOrdinaryCapacity

/-! Selected ordinary-bin lower bound on original generated two-stream rows. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceProjection
open CurrentAdditive.ArbitraryPrefix

variable {X Y I Rw F : Type*}
  [Fintype X] [Fintype Y] [Fintype I] [Fintype Rw] [Nonempty Rw]
  [Fintype F] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The exact indexed ordinary source bound transfers pointwise to
surviving original rows. A representative original row is chosen once for
each selected bin/selector label, before any ordinary column is seen. -/
theorem selected_ordinary_original_lower
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (hordinary : ∀ r c, M r (.inl c) =
      T src R₀ (selector r) (src.outer.decode c.1 (bin r)))
    (H a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (e : Fin n → Fin s) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (R : Set Rw) (O : Set (src.outer.Label × src.gamma.Label))
    (hrow : ∀ i : Fin n, (2 : ℝ)^a*x ≤
      src.inner.law.toFiniteLaw.prob
        (fun z => ∃ r ∈ R, bin r = e i ∧ selector r = z))
    (hO : (9/25 : ℝ) ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O)) :
    H+a ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  classical
  let Rows : Fin n → Set src.inner.Label :=
    fun i z => ∃ r ∈ R, bin r = e i ∧ selector r = z
  have hl := selected_ordinary_exact_lower src R₀ H a n x hD ha hH hx
    hscale hprofile e he hcount Rows (by intro i; exact hrow i) O hO
  let f : Fin n × src.inner.Label → Rw := fun u =>
    if h : ∃ r ∈ R, bin r = e u.1 ∧ selector r = u.2 then
      Classical.choose h else Classical.choice inferInstance
  have hf : ∀ u ∈ rowRectangle Finset.univ Rows,
      f u ∈ R ∧ bin (f u) = e u.1 ∧ selector (f u) = u.2 := by
    intro u hu
    have hex : ∃ r ∈ R, bin r = e u.1 ∧ selector r = u.2 := by
      simpa only [rowRectangle, Finset.mem_univ, true_and, Rows] using hu
    simpa [f, hex] using Classical.choose_spec hex
  have hmap : Compression.restrictionD
      (fun (u : Fin n × src.inner.Label) c =>
        T src R₀ u.2 (src.outer.decode c.1 (e u.1)))
      (rowRectangle Finset.univ Rows) O ≤
      Compression.restrictionD M R (Sum.inl '' O) := by
    have heq : Compression.restrictionD
        (fun (u : Fin n × src.inner.Label) c =>
          T src R₀ u.2 (src.outer.decode c.1 (e u.1)))
        (rowRectangle Finset.univ Rows) O =
        Compression.restrictionD (fun u c => M (f u) (.inl c))
          (rowRectangle Finset.univ Rows) O := by
      unfold Compression.restrictionD
      congr 1
      funext u c
      have hs := hf u.val u.property
      change T src R₀ u.val.2 (src.outer.decode c.val.1 (e u.val.1)) =
        M (f u.val) (.inl c.val)
      rw [hordinary (f u.val) c.val, hs.2.1, hs.2.2]
    have h := restrictionD_map_le M f Sum.inl R (Sum.inl '' O)
      (rowRectangle Finset.univ Rows) O
      (fun u hu => (hf u hu).1)
      (by intro c hc; exact ⟨c, hc, rfl⟩)
    rw [heq]
    exact h
  exact hl.trans hmap

end CurrentAdditive.DeterministicIndexedMatrix.Sources
