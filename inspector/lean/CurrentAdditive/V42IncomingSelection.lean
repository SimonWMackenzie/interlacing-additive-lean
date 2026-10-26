import CurrentAdditive.V42IncomingHeavyFibres

namespace CurrentAdditive.V42IncomingSelection

open Paper2
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

/-- v42 selection from the entire weighted incoming family. The selected
coordinates are genuine original `(i,α)` addresses and use threshold
`K₀*x`, with exactly the source's cap-one exception budget. -/
theorem select_weighted_diagonal_blocks
    (κ : ℕ) (x θ : ℝ)
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (hκ : 1 ≤ κ) (hw : 1 ≤ w) (hx : 0 < x) (hθ : 0 < θ)
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hlarge : 512*(s : ℝ)*κ ≤
      ∑ i, V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀ i)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hbad : streams.metadataStream.law.toFiniteLaw.prob
      (fun md => V42IncomingWeightedSection.templateMass src streams
        (V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀) md <
          (∑ i, V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀ i)/2) ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂) :
    ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
      ∃ hsection : θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
        (fun sel => (md,(base,sel)) ∈ Ystar),
      ∃ E Q : Finset (Fin w × Fin q₂),
        Q.card = s*κ*q₂+1 ∧
        (∀ z ∈ Q, z ∉ E ∧
          (∃ p : Fin s, streams.metadataStream.decode md z.1 = .inl p) ∧
          2*(s : ℝ)*κ*q₂*x ≤ src.gamma.law.toFiniteLaw.prob
            (fun γ => (z.1,Sum.inr (z.2,γ)) ∈ R)) ∧
        (∀ J : Finset (Fin (w*q₂)),
          J ⊆ Finset.univ \ E.image (incomingCoord (q₂ := q₂) (w := w)).symm →
          J.card ≤ 8 → projectionTV
            (condition streams.selectorStream.law.toFiniteLaw
              (fun sel => (md,(base,sel)) ∈ Ystar)
              (lt_of_lt_of_le (by linarith : 0 < θ/4) hsection))
            ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
            (incomingDecode src streams) J ≤ V38Moments.epsilon (θ/4) 1) := by
  classical
  obtain ⟨md,base,hweighted,hsection⟩ :=
    V42IncomingWeightedSection.complete_weighted_template_section src streams
      (V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀)
      θ hθ Ystar hYstar hbad
  let K : Set streams.selectorStream.Label := fun sel => (md,(base,sel)) ∈ Ystar
  obtain ⟨Efin,hEfin,hTV⟩ := V38Moments.conditioning_outside_exception
    streams.selectorStream.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    (incomingDecode src streams) (incoming_fin_dwise src streams)
    K (θ/4) 1 (by linarith) (by norm_num) hsection
  let e : Fin (w*q₂) ≃ Fin w × Fin q₂ := incomingCoord
  let E := Efin.image e
  let H := Finset.univ.filter (fun z : Fin w × Fin q₂ =>
    2*(s : ℝ)*κ*q₂*x ≤
      V42IncomingHeavyFibres.retainedFibreMass src streams R I₀ md z)
  have hEcard : E.card ≤ s*q₂ := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact hEfin.trans hException
  have hmany : 2*s*κ*q₂ < H.card :=
    V42IncomingHeavyFibres.many_heavy_fibres src streams κ x R I₀ md
      hκ hw hx hwidth hlarge hweighted
  have hdiff : H.card ≤ (H \ E).card + E.card :=
    Finset.card_le_card_sdiff_add_card
  have hneed : s*κ*q₂+1 ≤ (H \ E).card := by
    have hk : s*q₂ ≤ s*κ*q₂ := by nlinarith
    have hmany' : 2*(s*κ*q₂) < H.card := by nlinarith
    omega
  obtain ⟨Q,hQ,hQcard⟩ := Finset.exists_subset_card_eq hneed
  refine ⟨md,base,hsection,E,Q,hQcard,?_,?_⟩
  · intro z hz
    have hz' := Finset.mem_sdiff.mp (hQ hz)
    have hf := (Finset.mem_filter.mp hz'.1).2
    have ht : 0 < 2*(s : ℝ)*κ*q₂*x := by
      have hk : (0 : ℝ) < κ := by exact_mod_cast (by omega : 0 < κ)
      have hs : (0 : ℝ) < s := by exact_mod_cast (NeZero.pos s)
      have hq : (0 : ℝ) < q₂ := by exact_mod_cast (NeZero.pos q₂)
      positivity
    have hg : z.1 ∈ I₀ ∧
        isTemplateFlag (streams.metadataStream.decode md z.1) := by
      by_contra hn
      simp [V42IncomingHeavyFibres.retainedFibreMass,hn] at hf
      linarith
    have hf' : 2*(s : ℝ)*κ*q₂*x ≤
        V42IncomingHeavyFibres.fibreMass src R z.1 z.2 := by
      simpa [V42IncomingHeavyFibres.retainedFibreMass,hg] using hf
    refine ⟨hz'.2,?_,hf'⟩
    exact ⟨templateBin src streams md z.1,
      templateBin_eq_of_flag src streams md z.1 hg.2⟩
  · intro J hJ hcard
    have hEeq : E.image e.symm = Efin := by ext i; simp [E]
    change J ⊆ Finset.univ \ E.image e.symm at hJ
    rw [hEeq] at hJ
    exact hTV J hJ hcard

end CurrentAdditive.V42IncomingSelection

#print axioms CurrentAdditive.V42IncomingSelection.select_weighted_diagonal_blocks
