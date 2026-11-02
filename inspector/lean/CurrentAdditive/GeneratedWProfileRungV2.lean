import CurrentAdditive.GeneratedWProfileMassV2

/-! The three weaker rungs of the literal generated internal matrix, with
the exact source law and the ordinary tagged-column projection. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity

variable {G V Aux X Y : Type*} [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq G] [DecidableEq V]
  [DecidableEq Aux] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The three independent complete stream labels, packaged without changing
their product law or identifying labels with equal decoded rows. -/
noncomputable def internalRowCodeSource
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI w)
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) (rowLaw src μI).toFiniteLaw) :
    CodeSource 8192 w (Row (I := G × (V ⊕ Aux)) src)
      (rowLaw src μI) := by
  classical
  exact {
    Label := streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)
    finite := inferInstance
    decEq := Classical.decEq _
    law := streams.law
    decode := InternalStreams.decode src streams
    exactLaw := hwise
  }

theorem generated_W_profile_from_rung_guards
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI w)
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (d a : ℕ) (x θ τ : ℝ)
    (hd : 2 ≤ d) (ha : 3 ≤ a) (hx : 0 < x) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hτ : 0 < τ)
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) (rowLaw src μI).toFiniteLaw)
    (hprofile : RestrictionProfile (Nref src R activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw x (d : ℤ))
    (hscale : ∀ j : Fin 3, (2 : ℝ)^(a-j.val) * x < 1)
    (hbudget : ∀ j : Fin 3,
      (((2^((a-j.val)-1)+1) +
        CurrentAdditive.conditioningExceptionCountR 1024 θ τ : ℕ) : ℝ) *
          (1 - (2 : ℝ)^(a-j.val) * x) ≤
        (w : ℝ) *
          (((3/5 : ℝ) * (1/2 : ℝ)^j.val - (1-127/128)) /
            (127/128) - (2 : ℝ)^(a-j.val) * x)) :
    RestrictionProfile (W src streams R activity ξ₀)
      streams.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (columnLaw src)).toFiniteLaw)
      θ ((d+a : ℕ) : ℤ) := by
  classical
  intro j U V hU hV
  let β := ((3/5 : ℝ) * (1/2 : ℝ)^j.val - (1-127/128)) / (127/128)
  let Uo := WordinarySelected src V
  have hUo : β ≤
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (ordinaryLaw src)).toFiniteLaw).prob (· ∈ Uo) := by
    exact ordinarySelected_mass src V
      ((3/5 : ℝ) * (1/2 : ℝ)^j.val) hV
  let code := internalRowCodeSource src μI streams hwise
  have hcost := CurrentAdditive.DeterministicIndexedMatrix.codeSource_profile_rung
    (ordinaryLaw src) (rowLaw src μI) (Nref src R activity ξ₀)
    code Uo U d (a-j.val) x β θ τ
    (by omega) hd hx (hscale j) hprofile hUo (hbudget j)
    hθ hθ1 hU hτ
  have hentry : (fun (row : Fin w ×
      (src.outer.Label × src.gamma.Label))
      (col : streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) =>
      Nref src R activity ξ₀ row.2 (code.decode col row.1)) =
      fun (row : Fin w × (src.outer.Label × src.gamma.Label))
        (col : streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label)) =>
        W src streams R activity ξ₀ col
        (row.1, Column.ordinary row.2) := by
    funext row col
    rfl
  have hcostW : d+(a-j.val) ≤ Paper2.Compression.restrictionD
      (fun row col => W src streams R activity ξ₀ col
        (row.1, Column.ordinary row.2)) Uo U := by
    simpa only [hentry] using hcost
  have hsub : Set.MapsTo
      (fun row : Fin w × (src.outer.Label × src.gamma.Label) =>
        (row.1, Column.ordinary row.2)) Uo V := by
    intro row hr
    exact hr
  have hmap : d+(a-j.val) ≤ Paper2.Compression.restrictionD
      (W src streams R activity ξ₀)
      U V := by
    have hm := Paper2.SourceProjection.restrictionD_map_le
      (W src streams R activity ξ₀) id
      (fun row : Fin w × (src.outer.Label × src.gamma.Label) =>
        (row.1, Column.ordinary row.2))
      U V U Uo (fun _ h => h) hsub
    have htrans : Paper2.Compression.restrictionD
        (fun row col => W src streams R activity ξ₀ col
          (row.1, Column.ordinary row.2)) Uo U =
      Paper2.Compression.restrictionD
        (fun col row => W src streams R activity ξ₀ col
          (row.1, Column.ordinary row.2)) U Uo := by
      exact Paper2.SourceProjection.restrictionD_transpose _ U Uo
    rw [htrans] at hcostW
    exact hcostW.trans hm
  have hcast : (((d+a : ℕ) : ℤ) - j.val) ≤
      (Paper2.Compression.restrictionD
        (W src streams R activity ξ₀) U V : ℤ) := by omega
  exact hcast

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_W_profile_from_rung_guards
