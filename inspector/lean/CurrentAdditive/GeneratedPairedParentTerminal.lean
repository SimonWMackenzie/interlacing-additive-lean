import CurrentAdditive.GeneratedPairedLiveStops
import Paper2.PairedSelectorCapacityPair

/-! Capacity-one attached pair for the generated indexed source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceProjection Paper2.PairedSelectorCapacityPair
open CurrentAdditive.ArbitraryPrefix

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Two supports at the same inner index have different tags, hence
different source coordinates. Their common retained pair event is kept joint. -/
theorem paired_parent_cost
    (R₀ : X → Y → Bool) (H : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2*x ≤ 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (α : Fin q₂) (K : Set (src.inner.Label × src.inner.Label))
    (ordinary foreign : Set src.gamma.Label)
    (C : Set ((Bool × Fin q₂) × src.gamma.Label))
    (hordinary : ∀ γ ∈ ordinary, ((false, α), γ) ∈ C)
    (hforeign : ∀ γ ∈ foreign, ((true, α), γ) ∈ C)
    (hO : 2*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ ordinary))
    (hF : 2*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ foreign))
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K)) :
    H+1 ≤ Compression.restrictionD
      (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))) K C := by
  classical
  let e : Fin 2 → Bool × Fin q₂ := pairBlock α
  let Rows : Fin 2 → Set src.gamma.Label :=
    fun i => if i = 0 then ordinary else foreign
  have hrow : ∀ i : Fin 2,
      (2 : ℝ)^1*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i
    fin_cases i
    · simpa [Rows] using hO
    · simpa [Rows] using hF
  have hK' : (9/25 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K) := by
    linarith
  have hl := selected_paired_exact_lower src R₀ H 1 2 x hD (by omega)
    hH hx (by simpa only [pow_one] using hscale) hprofile
    e (pairBlock_injective α) (by norm_num) Rows hrow K hK'
  let M : (src.inner.Label × src.inner.Label) →
      ((Bool × Fin q₂) × src.gamma.Label) → Bool :=
    fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))
  have hRows : ∀ u ∈ rowRectangle Finset.univ Rows, (e u.1, u.2) ∈ C := by
    intro u hu
    have hRu : u.2 ∈ Rows u.1 := by
      simpa only [rowRectangle, Finset.mem_univ, true_and] using hu
    rcases u with ⟨i, γ⟩
    fin_cases i
    · exact hordinary γ (by simpa [Rows] using hRu)
    · exact hforeign γ (by simpa [Rows] using hRu)
  have hmap : Compression.restrictionD
      (fun (u : Fin 2 × src.gamma.Label) z => M z (e u.1, u.2))
      (rowRectangle Finset.univ Rows) K ≤
      Compression.restrictionD (fun c z => M z c) C K := by
    exact restrictionD_map_le (fun c z => M z c)
      (fun u : Fin 2 × src.gamma.Label => (e u.1, u.2))
      (fun z : src.inner.Label × src.inner.Label => z)
      C K (rowRectangle Finset.univ Rows) K hRows
      (by intro z hz; exact hz)
  have htrans := restrictionD_transpose M K C
  change H+1 ≤ Compression.restrictionD
    (fun (u : Fin 2 × src.gamma.Label) z => M z (e u.1, u.2))
    (rowRectangle Finset.univ Rows) K at hl
  exact hl.trans (hmap.trans_eq htrans)

#print axioms paired_parent_cost

end CurrentAdditive.DeterministicIndexedMatrix.Sources
