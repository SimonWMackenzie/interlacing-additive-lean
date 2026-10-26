import CurrentAdditive.V42IncomingSelection
import CurrentAdditive.V42IncomingWeightedTail

namespace CurrentAdditive.V42IncomingSharpBound

open Paper2 Paper2.ProtectedDensityGroups
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- v42 `res:incoming`: the exact incoming diagonal mass is less than
`2sκ` for every collection of original copies. The weighted moment and
heavy-fiber count remove the former dyadic grouping factor. -/
theorem incoming_diagonal_mass_lt
    (r κ d a : ℕ) (x θ : ℝ)
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s Y)
    (hw : w = 2^r) (hκ : 1 ≤ κ) (ha : 1 ≤ a) (hd : 2 ≤ d)
    (hpow : 2^a = 2*s*κ*q₂) (hx : 0 < x) (hθ : 0 < θ)
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (d : ℤ))
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : ∀ W : ℝ, 512*(s : ℝ)*κ ≤ W →
      (((2 : ℝ)^14*W)^128) / ((((255/256 : ℝ)-1/2)*W)^256) ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hnode : Compression.restrictionD
      (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀) R Ystar < d+a) :
    ∑ i ∈ I₀, V39IncomingDensity.receipt (diagonalLaw src).toFiniteLaw w R i <
      2*(s : ℝ)*κ := by
  classical
  by_contra hn
  have hmass := le_of_not_gt hn
  let dens := V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀
  let D₀ : ℝ := ∑ i, dens i
  have hlarge : 512*(s : ℝ)*κ ≤ D₀ := by
    rw [V39IncomingDensity.total_receipt] at hmass
    dsimp [D₀,dens]
    linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast (NeZero.pos s)
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast (by omega : 0 < κ)
  have hDpos : 0 < D₀ := lt_of_lt_of_le (by positivity) hlarge
  have hDle : D₀ ≤ w := by
    calc
      D₀ ≤ ∑ _i : Fin w, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun i _ =>
          V39IncomingDensity.density_le_one (diagonalLaw src).toFiniteLaw w R I₀ i)
      _ = _ := by simp
  have hbad : streams.metadataStream.law.toFiniteLaw.prob
      (fun md => V42IncomingWeightedSection.templateMass src streams dens md < D₀/2) ≤ θ/4 :=
    (V42IncomingWeightedTail.metadata_weighted_half_template_tail src streams dens
      (V39IncomingDensity.density_nonneg _ _ _ _)
      (V39IncomingDensity.density_le_one _ _ _ _) hDpos).trans (hguard D₀ hlarge)
  have hwposNat : 0 < w := by rw [hw]; positivity
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hwposNat
  have hwone : (1 : ℝ) ≤ w := by
    exact_mod_cast (by omega : 1 ≤ w)
  obtain ⟨md,base,hsection,E,Q,hQcard,hQ,hTV⟩ :=
    V42IncomingSelection.select_weighted_diagonal_blocks src streams κ x θ R I₀
      Ystar hκ (by omega) hx hθ hwidth hlarge hYstar hbad hException
  have hpowR : (2 : ℝ)^a = 2*(s : ℝ)*κ*q₂ := by exact_mod_cast hpow
  have hscale : (2 : ℝ)^a*x ≤ 1 := by
    rw [hpowR]
    have hscaled : (w : ℝ)^2*(2*(s : ℝ)*κ*q₂*x) ≤ 2*(s : ℝ)*κ := by
      have hh := mul_le_mul_of_nonneg_left hwidth
        (show 0 ≤ 2*(s : ℝ)*κ by positivity)
      nlinarith
    have hw2 : 2*(s : ℝ)*κ ≤ (w : ℝ)^2 := by nlinarith
    by_contra hn
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) (sq_pos_of_pos hwpos)
    nlinarith
  let e : Fin (w*q₂) ≃ Fin w × Fin q₂ := incomingCoord
  let Good := Q.image e.symm
  let Bad := E.image e.symm
  have hmem (i : Fin (w*q₂)) (hi : i ∈ Good) : e i ∈ Q := by
    obtain ⟨z,hz,hzi⟩ := Finset.mem_image.mp hi
    have he : e i = z := by rw [← hzi,e.apply_symm_apply]
    simpa [he] using hz
  have hBad (i : Fin (w*q₂)) (hi : i ∈ Bad) : e i ∈ E := by
    obtain ⟨z,hz,hzi⟩ := Finset.mem_image.mp hi
    have he : e i = z := by rw [← hzi,e.apply_symm_apply]
    simpa [he] using hz
  have hcount : 2^(a-1)+1 ≤ Good.card := by
    rw [show Good.card = Q.card from Finset.card_image_of_injective Q e.symm.injective,
      hQcard]
    have he : 2^a = 2*2^(a-1) := by
      rw [← pow_succ']
      congr 1
      omega
    nlinarith
  have hOutside : ∀ i ∈ Good, i ∉ Bad := by
    intro i hi hn
    exact (hQ (e i) (hmem i hi)).1 (hBad i hn)
  have hrows : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob
      (fun γ => ((e i).1,Sum.inr ((e i).2,γ)) ∈ R) := by
    intro i hi
    rw [hpowR]
    exact (hQ (e i) (hmem i hi)).2.2
  have hflags : ∀ i ∈ Good, ∃ p : Fin s,
      streams.metadataStream.decode md (e i).1 = .inl p := by
    intro i hi
    exact (hQ (e i) (hmem i hi)).2.1
  have hv : 0 < θ/4 := by linarith
  have hv1 : θ/4 ≤ 1 :=
    hsection.trans (streams.selectorStream.law.toFiniteLaw.prob_le_one _)
  have hlower := V39IndexedIncomingLocal.selected_diagonal_section_cost
    src streams R₀ activity ξ₀ R Ystar md base Good Bad d a x (θ/4) 1
    ha hd hx hscale hprofile hcount hOutside hrows hflags hv hv1
    (by norm_num) hsection hTV
  omega

end CurrentAdditive.V42IncomingSharpBound

#print axioms CurrentAdditive.V42IncomingSharpBound.incoming_diagonal_mass_lt
