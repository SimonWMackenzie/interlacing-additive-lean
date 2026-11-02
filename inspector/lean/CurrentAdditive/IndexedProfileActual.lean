import CurrentAdditive.IndexedProfileConditioning

/-! The three `det:profiles` population inputs with the actual Gamma, S,
and CalJ index sets and their original rational laws. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

theorem Sources.M₁_conditioned_population
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (U : Set (Fin q₁ × X)) (W : Set src.gamma.Label)
    (n : ℕ) (β t v τ : ℝ)
    (ht : t < 1) (hv : 0 < v) (hτ : 0 < τ)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob
      (· ∈ U))
    (hW : v ≤ src.gamma.law.toFiniteLaw.prob (· ∈ W))
    (hbudget : ((n + CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) *
      (1 - t) ≤ (q₁ : ℝ) * (β - t)) :
    ∃ (E : Finset (Fin q₁)) (e : Fin n ↪ Fin q₁),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      (∀ j, e j ∉ E) ∧
      (∀ j, t ≤ μX.toFiniteLaw.prob (fun x => (e j,x) ∈ U)) ∧
      (∀ J : Finset (Fin q₁), J ⊆ Finset.univ \ E → J.card ≤ 8 →
        CurrentAdditive.projectionTV
          (CurrentAdditive.condition src.gamma.law.toFiniteLaw (· ∈ W)
            (hv.trans_le hW))
          μY.toFiniteLaw
          (fun γ i => src.gamma.decode γ ⟨i.val, by omega⟩) J ≤
            CurrentAdditive.conditioningEpsilonR 1024 v τ) := by
  exact codeSource_select_conditioned_blocks μX μY
    (Sources.headCodeSource src) U W n β t v τ ht hv hτ hU hW hbudget

theorem Sources.T_conditioned_population
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (U : Set (Fin q₂ × src.gamma.Label)) (W : Set src.inner.Label)
    (n : ℕ) (β t v τ : ℝ)
    (ht : t < 1) (hv : 0 < v) (hτ : 0 < τ)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q₂)).prod
      src.gamma.law).toFiniteLaw.prob (· ∈ U))
    (hW : v ≤ src.inner.law.toFiniteLaw.prob (· ∈ W))
    (hbudget : ((n + CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) *
      (1 - t) ≤ (q₂ : ℝ) * (β - t)) :
    ∃ (E : Finset (Fin q₂)) (e : Fin n ↪ Fin q₂),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      (∀ j, e j ∉ E) ∧
      (∀ j, t ≤ src.gamma.law.toFiniteLaw.prob
        (fun γ => (e j,γ) ∈ U)) ∧
      (∀ J : Finset (Fin q₂), J ⊆ Finset.univ \ E → J.card ≤ 8 →
        CurrentAdditive.projectionTV
          (CurrentAdditive.condition src.inner.law.toFiniteLaw (· ∈ W)
            (hv.trans_le hW))
          (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
          src.inner.decode J ≤
            CurrentAdditive.conditioningEpsilonR 1024 v τ) := by
  exact codeSource_select_conditioned_blocks src.gamma.law
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
    src.inner U W n β t v τ ht hv hτ hU hW hbudget

theorem Sources.Nref_conditioned_population
    {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (U : Set (Row (I := G × (V ⊕ A)) src)) (W : Set src.outer.Label)
    (n : ℕ) (β t v τ : ℝ)
    (ht : t < 1) (hv : 0 < v) (hτ : 0 < τ)
    (hU : β ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ U))
    (hW : v ≤ src.outer.law.toFiniteLaw.prob (· ∈ W))
    (hbudget : ((n + CurrentAdditive.conditioningExceptionCountR 1024 v τ : ℕ) : ℝ) *
      (1 - t) ≤ (s : ℝ) *
        ((β - (1 - 255 / 256)) / (255 / 256) - t)) :
    ∃ (E : Finset (Fin s)) (e : Fin n ↪ Fin s),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 v τ ∧
      (∀ j, e j ∉ E) ∧
      (∀ j, t ≤ src.inner.law.toFiniteLaw.prob
        (fun z => Sum.inl (e j,z) ∈ U)) ∧
      (∀ J : Finset (Fin s), J ⊆ Finset.univ \ E → J.card ≤ 8 →
        CurrentAdditive.projectionTV
          (CurrentAdditive.condition src.outer.law.toFiniteLaw (· ∈ W)
            (hv.trans_le hW))
          (((PositiveRationalLaw.uniform (Fin q₂)).prod
            src.gamma.law).toFiniteLaw)
          src.outer.decode J ≤
            CurrentAdditive.conditioningEpsilonR 1024 v τ) := by
  have htemplate := Sources.template_retained src μI U β hU
  exact codeSource_select_conditioned_blocks src.inner.law
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law)
    src.outer (fun pz => Sum.inl pz ∈ U) W n
    ((β - (1 - 255 / 256)) / (255 / 256)) t v τ ht hv hτ
    (by simpa [templateRowLaw] using htemplate) hW hbudget

end CurrentAdditive.DeterministicIndexedMatrix
