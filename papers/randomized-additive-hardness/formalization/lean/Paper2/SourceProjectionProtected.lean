import Paper2.SourceProjection
import Paper2.SourceProjectionRetention

/-!
# Protected projections of the graph-constructed source

Frozen v12 Section 4, `src:profiles` and `src:near-full`. These statements
combine actual protected-family laws with actual retained-input matrix
pullbacks. The source matrix and its activity map are the graph constructor,
not a separately assumed source satisfying a projection contract.
-/

namespace Paper2.SourceProjectionProtected

open SourceMatrix SourceLawBinding SourceProjection

variable {V E X Y : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Y]
  {q₁ q₂ s k : ℕ} [NeZero s]

omit [Fintype X] [Fintype Y] in
theorem graph_position_injective
    (order : SourceConstruction.Items s V ≃ Fin (Fintype.card (SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r) (α : Fin q₂)
    (i j : SourceConstruction.Items s V) (p : Fin s)
    (hi : SourceConstruction.activity order edge hs r hq i α = some p)
    (hj : SourceConstruction.activity order edge hs r hq j α = some p) : i = j :=
  SourceConstruction.orderedActivity_injective order edge hs r
    (SourceConstruction.coordinateEquiv r hq α) i j p hi hj

omit [Fintype X] [Fintype Y] in
/-- The combinatorial T11 witness supplies three actual source-position
requests in the canonical ordered activity map used by the matrix. Thus
distinct selected tail slots are derived, not an added witness assumption. -/
theorem graph_witness_positions
    (order : SourceConstruction.Items s V ≃ Fin (Fintype.card (SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r) (α : Fin q₂)
    (keep : SourceConstruction.Items s V → Prop) (bin : SourceConstruction.Items s V → Fin s)
    (hw : SourcePadding.Witness (SourceItems.sourceActive edge r) keep bin
      (SourceConstruction.coordinateEquiv r hq α)) :
    ∃ i j h p p', i ≠ j ∧ p ≠ p' ∧ keep i ∧ keep j ∧ keep h ∧
      bin i = bin j ∧ bin i = bin h ∧
      SourceConstruction.activity order edge hs r hq i α = some p ∧
      SourceConstruction.activity order edge hs r hq j α = some p' ∧
      SourceConstruction.activity order edge hs r hq h α = none := by
  obtain ⟨i, j, h, hij, hi, hj, hh, hai, haj, hah, hbij, hbih⟩ := hw
  obtain ⟨p, hp⟩ :=
    (SourceConstruction.orderedActivity_some_iff order edge hs r i _).mpr hai
  obtain ⟨p', hp'⟩ :=
    (SourceConstruction.orderedActivity_some_iff order edge hs r j _).mpr haj
  have hd : p ≠ p' := by
    intro heq
    subst p'
    exact hij (graph_position_injective order edge hs r hq α i j p hp hp')
  have hn : SourceConstruction.activity order edge hs r hq h α = none := by
    cases hc : SourceConstruction.activity order edge hs r hq h α with
    | none => rfl
    | some b =>
      exact False.elim (hah
        ((SourceConstruction.orderedActivity_some_iff order edge hs r h _).mp ⟨b, hc⟩))
  exact ⟨i, j, h, p, p', hij, hd, hi, hj, hh, hbij, hbih, hp, hp', hn⟩

/-- Simultaneously keep the conditional mass and the literal source
restriction when projecting a retained fixed-tail family. -/
theorem fixedTail_mass_and_matrix [NeZero q₂]
    (ν : PositiveRationalLaw Y)
    (order : SourceConstruction.Items s V ≃ Fin (Fintype.card (SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (e : Fin k → Fin s) (he : Function.Injective e)
    (U : Set (TaggedColumn q₁ q₂ s Y))
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (A : Set (Fin k × Template q₁ q₂ X))
    (hA : ∀ a ∈ A, Sum.inl (e a.1, a.2) ∈ W) (η : ℝ)
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    1 - 256 * η ≤ ((SourceLaws.outerLaw ν q₁ q₂ s).iid k).toFiniteLaw.prob
      (· ∈ (fun z j => z (e j)) '' (TaggedColumn.fixedTail ⁻¹' U)) ∧
    Compression.restrictionD (fullInterlace (T R) k) A
      ((fun z j => z (e j)) '' (TaggedColumn.fixedTail ⁻¹' U)) ≤
        Compression.restrictionD (SourceConstruction.matrix order edge hs r hq R ξ₀) U W := by
  refine ⟨?_, ?_⟩
  · exact (SourceProjectionRetention.fixed_tail_rows_retained ν (· ∈ U) η hU).trans
      (fixedTail_projection_mass ν e he (TaggedColumn.fixedTail ⁻¹' U))
  · exact fixedTail_projection_D_le R (SourceConstruction.activity order edge hs r hq)
      ξ₀ e U W A hA

/-- The actual graph source on diagonal words contains the literal M₁
restriction projected from surviving rows in one template bin. -/
theorem diagonal_template_matrix
    (order : SourceConstruction.Items s V ≃ Fin (Fintype.card (SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (p : Fin s) (α : Fin q₂)
    (A : Set (Template q₁ q₂ X)) (J : Set (Word q₁ s Y))
    (U : Set (TaggedColumn q₁ q₂ s Y))
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ W)
    (hJ : ∀ γ ∈ J, TaggedColumn.diagonal (α, γ) ∈ U) :
    Compression.restrictionD (M₁ R) ((fun z => z α) '' A) J ≤
      Compression.restrictionD (SourceConstruction.matrix order edge hs r hq R ξ₀) U W :=
  diagonal_template_D_le R (SourceConstruction.activity order edge hs r hq) ξ₀ p α A J U W hA hJ

omit [Fintype E] [Fintype Y] [NeZero s] in
/-- Every fixed template bin, then every fixed coordinate in that bin,
inherits the quantitatively protected retained mass. -/
theorem template_coordinate_retained [Nonempty V] [NeZero q₁]
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) (η : ℝ)
    (hW : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W))
    (p : Fin s) (α : Fin q₂) :
    1 - η * (s : ℝ) / (255 / 256 : ℝ) ≤
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw.prob
        (· ∈ (fun z => z α) '' {z | Sum.inl (p, z) ∈ W}) :=
  (SourceProjectionRetention.template_bin_retained μ hs (· ∈ W) η hW p).trans
    (template_coordinate_mass μ α {z | Sum.inl (p, z) ∈ W})

omit [Fintype V] [Fintype E] [Fintype X] [NeZero s] in
/-- The protected diagonal family controls the average retained word mass
over the actual public coordinates, before any deficiency counting. -/
theorem diagonal_average_retained [NeZero q₂] (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (η : ℝ)
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    1 - 256 * η ≤ (q₂ : ℝ)⁻¹ * ∑ α : Fin q₂,
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => TaggedColumn.diagonal (α, γ) ∈ U) := by
  have h := SourceProjectionRetention.diagonal_rows_retained ν (· ∈ U) η hU
  change 1 - 256 * η ≤ (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
    (· ∈ TaggedColumn.diagonal ⁻¹' U) at h
  rw [outer_word_average ν (TaggedColumn.diagonal ⁻¹' U)] at h
  exact h

end Paper2.SourceProjectionProtected

#print axioms Paper2.SourceProjectionProtected.fixedTail_mass_and_matrix
#print axioms Paper2.SourceProjectionProtected.diagonal_template_matrix
#print axioms Paper2.SourceProjectionProtected.template_coordinate_retained
#print axioms Paper2.SourceProjectionProtected.diagonal_average_retained
#print axioms Paper2.SourceProjectionProtected.graph_witness_positions
