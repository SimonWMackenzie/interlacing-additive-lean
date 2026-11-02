import CurrentAdditive.GeneratedSeparationN

/-! The numerical specialization used immediately after `det:separation` in
the generated-source near-full argument. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ t : ℕ} [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := 2^t) μX μY)

theorem B_template_fixedTail_separation_998
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : Paper2.SourceMatrix.Tail (2^t) Y)
    (V : Set (Row (I := I) src)) (U : Set (Column src))
    (d : ℕ) (ρ : ℝ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hprofile : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)
      ρ (d : ℤ))
    (hrow : ∀ p : Fin (2^t), (999/1000 : ℝ) ≤ src.inner.law.toFiniteLaw.prob
      (fun z => (Sum.inl (p,z) : Row (I := I) src) ∈ V))
    (hbudget : ((2^t : ℕ) : ℝ) * ρ ≤ 1/10000)
    (hK : (99/100 : ℝ) ≤ src.outer.law.toFiniteLaw.prob
      (fun js => (Column.fixedTail js : Column src) ∈ U))
    (P : Protocol V U Bool)
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun a c => B src R₀ activity ξ₀ a.1 c.1)) :
    ∃ Φ : (Fin (2^t) × src.inner.Label) → V,
      (∀ p z (h : (Sum.inl (p,z) : Row (I := I) src) ∈ V),
        Φ (p,z) = ⟨.inl (p,z),h⟩) ∧
      Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
      ∃ RV : Finset V, (∀ a, a ∈ RV) ∧
        Paper2.SourceProtocolPrefixTree.EveryPrefixBranchActive RV t P ∧
      ∃ dom : Fin (2^t) ≃ Fin (2^t),
        ∀ j, (998/1000 : ℝ) <
            src.inner.law.toFiniteLaw.prob (fun z =>
              (Sum.inl (dom j,z) : Row (I := I) src) ∈ V ∧
                NPCC.Protocol.prefixCodeRaw t P (Φ (dom j,z)) = j) ∧
          (∀ i, i ≠ dom j →
            src.inner.law.toFiniteLaw.prob (fun z =>
              (Sum.inl (i,z) : Row (I := I) src) ∈ V ∧
                NPCC.Protocol.prefixCodeRaw t P (Φ (i,z)) = j) < 2*ρ) := by
  have hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < (999/1000 : ℝ) := by
    linarith
  have hK' : (18/25 : ℝ) ≤ src.outer.law.toFiniteLaw.prob
      (fun js => (Column.fixedTail js : Column src) ∈ U) := by
    linarith
  obtain ⟨Φ, hΦ, hp, RV, hRV, hactive, dom, hdom⟩ :=
    B_template_fixedTail_separation src R₀ activity ξ₀ V U d ρ (999/1000)
      ht hd hρ hprofile hrow hgap hK' P hcost hcompute
  have hnumeric : (998/1000 : ℝ) <
      (999/1000 : ℝ) - (2^t-1 : ℕ) * (2*ρ) := by
    have hnat : 2^t-1 ≤ 2^t := Nat.sub_le _ _
    have hreal : (((2^t-1 : ℕ) : ℝ)) ≤ (((2^t : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (by linarith : 0 ≤ 2*ρ)
    nlinarith
  refine ⟨Φ, hΦ, hp, RV, hRV, hactive, dom, ?_⟩
  intro j
  exact ⟨hnumeric.trans (hdom j).1, (hdom j).2⟩

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.B_template_fixedTail_separation_998

end CurrentAdditive.DeterministicIndexedMatrix.Sources
