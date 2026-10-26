import CurrentAdditive.EdgeSource
import Paper2.SourceMatrix
import Paper2.SourceProtocols
import Paper2.SourceLawBinding

/-!
Literal v37 edge-only source matrix: a finite, noncomputable interface.
The raw and tagged row/column formulas are Paper2.SourceMatrix; the new
coordinate carrier and order-preserving activity are defined here.
-/

namespace CurrentAdditive.EdgeSourceMatrix

open Workspace.Types.CommComplexity
open Paper2.RankLeaves
open CurrentAdditive.EdgeSource

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] {s q₁ q₂ : ℕ} [NeZero s]

abbrev Items (s : ℕ) (V : Type*) :=
  EdgeSource.Item (Fin (4 * s)) V (Fin (s - 3))

noncomputable def coordinateEquiv (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r) :
    Fin q₂ ≃ EdgeSource.SourceCoord (Fin (4 * s)) E r :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, EdgeSource.card_sourceCoord, hq])

noncomputable def activeLabels
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (r : ℕ)
    (c : EdgeSource.SourceCoord (Fin (4 * s)) E r) :
    Finset (Fin (Fintype.card (Items s V))) := by
  classical
  exact Finset.univ.filter (fun j => EdgeSource.sourceActive edge r c (order.symm j))

theorem activeLabels_card_le
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (c : EdgeSource.SourceCoord (Fin (4 * s)) E r) :
    (activeLabels order edge r c).card ≤ s := by
  classical
  let A := activeLabels order edge r c
  have hex (j : A) : ∃ b, EdgeSource.sourceActivity edge hs r (order.symm j) c = some b := by
    apply (EdgeSource.sourceActivity_some_iff edge hs r _ c).mpr
    exact (Finset.mem_filter.mp j.property).2
  let f : A → Fin s := fun j => Classical.choose (hex j)
  have hf : Function.Injective f := by
    intro i j hij
    have hi := Classical.choose_spec (hex i)
    have hj := Classical.choose_spec (hex j)
    change EdgeSource.sourceActivity edge hs r (order.symm i) c = some (f i) at hi
    change EdgeSource.sourceActivity edge hs r (order.symm j) c = some (f j) at hj
    rw [← hij] at hj
    have he := EdgeSource.sourceActivity_position_injective edge hs r c hi hj
    exact Subtype.ext (order.symm.injective he)
  have h := Fintype.card_le_of_injective f hf
  simpa [A] using h

/-- The dense ordinal rank of an active item in the public item ordering. -/
noncomputable def orderedActivity
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (i : Items s V) (c : EdgeSource.SourceCoord (Fin (4 * s)) E r) :
    Option (Fin s) := by
  classical
  let A := activeLabels order edge r c
  exact if hi : order i ∈ A then
    some (Fin.castLE (activeLabels_card_le order edge hs r c)
      ((A.orderIsoOfFin rfl).symm ⟨order i, hi⟩))
  else none

theorem orderedActivity_some_iff
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (i : Items s V) (c : EdgeSource.SourceCoord (Fin (4 * s)) E r) :
    (∃ b, orderedActivity order edge hs r i c = some b) ↔
      EdgeSource.sourceActive edge r c i := by
  classical
  simp [orderedActivity, activeLabels]

theorem orderedActivity_injective
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (c : EdgeSource.SourceCoord (Fin (4 * s)) E r) (i j : Items s V)
    (b : Fin s)
    (hi : orderedActivity order edge hs r i c = some b)
    (hj : orderedActivity order edge hs r j c = some b) : i = j := by
  classical
  have hai : order i ∈ activeLabels order edge r c := by
    simpa [activeLabels] using
      (orderedActivity_some_iff order edge hs r i c).mp ⟨b, hi⟩
  have haj : order j ∈ activeLabels order edge r c := by
    simpa [activeLabels] using
      (orderedActivity_some_iff order edge hs r j c).mp ⟨b, hj⟩
  unfold orderedActivity at hi hj
  dsimp only at hi hj
  rw [dif_pos hai] at hi
  rw [dif_pos haj] at hj
  have he := Option.some.inj (hi.trans hj.symm)
  have hf : ((activeLabels order edge r c).orderIsoOfFin rfl).symm ⟨order i, hai⟩ =
      ((activeLabels order edge r c).orderIsoOfFin rfl).symm ⟨order j, haj⟩ :=
    Fin.ext (congrArg (fun x : Fin s => x.val) he)
  have hsub := (Finset.orderIsoOfFin (activeLabels order edge r c) rfl).symm.injective hf
  exact order.injective (congrArg Subtype.val hsub)

theorem orderedActivity_preserves_order
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (c : EdgeSource.SourceCoord (Fin (4 * s)) E r)
    (i j : Items s V) (bi bj : Fin s)
    (hi : orderedActivity order edge hs r i c = some bi)
    (hj : orderedActivity order edge hs r j c = some bj)
    (hij : order i < order j) : bi < bj := by
  classical
  have hai : order i ∈ activeLabels order edge r c := by
    simpa [activeLabels] using
      (orderedActivity_some_iff order edge hs r i c).mp ⟨bi, hi⟩
  have haj : order j ∈ activeLabels order edge r c := by
    simpa [activeLabels] using
      (orderedActivity_some_iff order edge hs r j c).mp ⟨bj, hj⟩
  unfold orderedActivity at hi hj
  dsimp only at hi hj
  rw [dif_pos hai] at hi
  rw [dif_pos haj] at hj
  have hlt : ((activeLabels order edge r c).orderIsoOfFin rfl).symm
      ⟨order i, hai⟩ <
      ((activeLabels order edge r c).orderIsoOfFin rfl).symm
      ⟨order j, haj⟩ :=
    ((activeLabels order edge r c).orderIsoOfFin rfl).symm.strictMono hij
  have hcast : Fin.castLE (activeLabels_card_le order edge hs r c)
      (((activeLabels order edge r c).orderIsoOfFin rfl).symm ⟨order i, hai⟩) <
      Fin.castLE (activeLabels_card_le order edge hs r c)
      (((activeLabels order edge r c).orderIsoOfFin rfl).symm ⟨order j, haj⟩) := by
    exact hlt
  have hbi := Option.some.inj hi
  have hbj := Option.some.inj hj
  exact hbi ▸ hbj ▸ hcast

noncomputable def activity
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r) :
    Items s V → Fin q₂ → Option (Fin s) :=
  fun i α => orderedActivity order edge hs r i (coordinateEquiv r hq α)

theorem activity_collisionFree
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (colour : V → Fin 3)
    (proper : ∀ e, colour (edge e false) ≠ colour (edge e true)) :
    Paper2.SourceMatrix.CollisionFree
      (Paper2.SourceItems.yesAssignment hs colour)
      (activity order edge hs r hq) := by
  intro α i j b b' hi hj heq
  have hai := (orderedActivity_some_iff order edge hs r i _).mp ⟨b, hi⟩
  have haj := (orderedActivity_some_iff order edge hs r j _).mp ⟨b', hj⟩
  exact EdgeSource.source_yes edge hs r colour proper _ hai haj heq

/-- The source N is the transpose of the literal tagged raw matrix. -/
noncomputable def matrix
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y) :=
  Paper2.SourceMatrix.N (q₁ := q₁) R (activity order edge hs r hq) ξ₀

theorem matrix_template
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : Paper2.SourceMatrix.TaggedColumn q₁ q₂ s Y)
    (p : Fin s) (z : Paper2.SourceMatrix.Template q₁ q₂ X) :
    matrix order edge hs r hq R ξ₀ Z (.inl (p, z)) =
      Paper2.SourceMatrix.M₂ R ((Paper2.SourceMatrix.forgetTag ξ₀ Z).2 p) z := rfl

theorem matrix_source
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : Paper2.SourceMatrix.TaggedColumn q₁ q₂ s Y)
    (i : Items s V) (u : X) :
    matrix order edge hs r hq R ξ₀ Z (.inr (i, u)) =
      R u (Paper2.SourceMatrix.sourceColumn (activity order edge hs r hq) i
        (Paper2.SourceMatrix.forgetTag ξ₀ Z)) := rfl

/-- On a diagonal outer-coordinate tuple, an active item reads its ordered
position in the source tail, exactly as in the v37 raw-row equation. -/
theorem matrix_source_common_active
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : Paper2.SourceMatrix.RawColumn q₁ q₂ s Y)
    (i : Items s V) (u : X) (b : Fin s)
    (hcommon : ∀ p, (Z.2 p).1 = (Z.2 0).1)
    (ha : activity order edge hs r hq i (Z.2 0).1 = some b) :
    matrix order edge hs r hq R ξ₀ (.unrestricted Z) (.inr (i, u)) =
      R u (Z.1 b.castSucc) := by
  simp [matrix, Paper2.SourceMatrix.N, Paper2.SourceMatrix.raw,
    Paper2.SourceMatrix.baseRequest, Paper2.SourceMatrix.sourceColumn,
    Paper2.SourceMatrix.sourcePosition, Paper2.SourceMatrix.forgetTag,
    hcommon, ha]

theorem matrix_source_inactive
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : Paper2.SourceMatrix.RawColumn q₁ q₂ s Y)
    (i : Items s V) (u : X)
    (ha : activity order edge hs r hq i (Z.2 0).1 = none) :
    matrix order edge hs r hq R ξ₀ (.unrestricted Z) (.inr (i, u)) =
      R u (Z.1 (Fin.last s)) := by
  simp [matrix, Paper2.SourceMatrix.N, Paper2.SourceMatrix.raw,
    Paper2.SourceMatrix.baseRequest, Paper2.SourceMatrix.sourceColumn,
    Paper2.SourceMatrix.sourcePosition, Paper2.SourceMatrix.forgetTag, ha]

theorem matrix_source_offDiagonal
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : Paper2.SourceMatrix.RawColumn q₁ q₂ s Y)
    (i : Items s V) (u : X)
    (h : ¬ ∀ p, (Z.2 p).1 = (Z.2 0).1) :
    matrix order edge hs r hq R ξ₀ (.unrestricted Z) (.inr (i, u)) =
      R u (Z.1 (Fin.last s)) := by
  simp [matrix, Paper2.SourceMatrix.N, Paper2.SourceMatrix.raw,
    Paper2.SourceMatrix.baseRequest, Paper2.SourceMatrix.sourceColumn,
    Paper2.SourceMatrix.sourcePosition, Paper2.SourceMatrix.forgetTag, h]

theorem matrix_upper_budgets [NeZero q₂]
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y) (a b : ℕ)
    (hq₁ : q₁ + 2 = s) (hsa : s = 2 ^ a) (hqb : q₂ = 2 ^ b) :
    D (matrix (q₁ := q₁) order edge hs r hq R ξ₀) ≤ D R + a + b + a + 1 ∧
      (∀ colour : V → Fin 3,
        (∀ e, colour (edge e false) ≠ colour (edge e true)) →
        D (matrix (q₁ := q₁) order edge hs r hq R ξ₀) ≤ D R + a + b + a) := by
  obtain ⟨hu, hy⟩ := Paper2.SourceMatrix.source_upper_budgets
    (activity order edge hs r hq) R ξ₀ a b hq₁ hsa hqb
  refine ⟨hu, fun colour proper => ?_⟩
  exact hy (Paper2.SourceItems.yesAssignment hs colour)
    (activity_collisionFree order edge hs r hq colour proper)

theorem matrix_rank_le
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    (realMatrix (matrix (q₁ := q₁) order edge hs r hq R ξ₀)).rank ≤
      (s * q₁ * q₂ + Fintype.card (Items s V)) * (realMatrix R).rank :=
  Paper2.SourceMatrix.N_rank_le R (activity order edge hs r hq) ξ₀

/-- The probability laws are on the identical raw-row and tagged-column
carriers, so the old proofs of the specified masses apply unchanged. -/
noncomputable def matrixRowLaw [NeZero q₂]
    (ν : Paper2.PositiveRationalLaw Y) :
    Paper2.PositiveRationalLaw
      (Paper2.SourceMatrix.TaggedColumn q₁ q₂ s Y) :=
  Paper2.SourceLawBinding.matrixRowLaw ν q₁ q₂ s

noncomputable def matrixColumnLaw [Nonempty V] [NeZero q₁]
    (μ : Paper2.PositiveRationalLaw X) (hs : 4 ≤ s) :
    Paper2.PositiveRationalLaw
      (Paper2.SourceMatrix.RawRow q₁ q₂ s X (Items s V)) :=
  Paper2.SourceLawBinding.matrixColumnLaw μ q₁ q₂ s hs

theorem row_tag_masses [NeZero q₂]
    (ν : Paper2.PositiveRationalLaw Y) :
    (matrixRowLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob
      (fun Z => Paper2.SourceLaws.tagIndex Z = 0) = 127 / 128 ∧
    (matrixRowLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob
      (fun Z => Paper2.SourceLaws.tagIndex Z = 1) = 1 / 256 ∧
    (matrixRowLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob
      (fun Z => Paper2.SourceLaws.tagIndex Z = 2) = 1 / 256 :=
  Paper2.SourceLawBinding.row_tag_masses ν

theorem column_family_masses [Nonempty V] [NeZero q₁]
    (μ : Paper2.PositiveRationalLaw X) (hs : 4 ≤ s) :
    (matrixColumnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 0) = 255 / 256 ∧
    (matrixColumnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 1) = 1 / 512 ∧
    (matrixColumnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 2) = 1 / 512 :=
  Paper2.SourceLawBinding.column_family_masses μ hs

#print axioms orderedActivity_some_iff
#print axioms orderedActivity_injective
#print axioms orderedActivity_preserves_order
#print axioms activity_collisionFree
#print axioms matrix_template
#print axioms matrix_source
#print axioms matrix_source_common_active
#print axioms matrix_source_inactive
#print axioms matrix_source_offDiagonal
#print axioms matrix_upper_budgets
#print axioms matrix_rank_le
#print axioms row_tag_masses
#print axioms column_family_masses

end CurrentAdditive.EdgeSourceMatrix
