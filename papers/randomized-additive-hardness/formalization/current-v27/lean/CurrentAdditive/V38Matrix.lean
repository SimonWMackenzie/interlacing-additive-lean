import CurrentAdditive.OrderedMatrix

/-!
The selected v38 source matrix has two column families.  OrderedMatrix
provides the unchanged edge-only activity and ordered active positions;
the old three-tag matrix is used only as a proof vehicle for an upper bound.
-/

namespace CurrentAdditive.V38Matrix

open Workspace.Types.CommComplexity Paper2 Paper2.RankLeaves
open CurrentAdditive.EdgeSourceMatrix

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] {s q₁ q₂ : ℕ} [NeZero s]

abbrev TaggedColumn (q₁ q₂ s : ℕ) (Y : Type*) :=
  Paper2.SourceMatrix.RawColumn q₁ q₂ s Y ⊕
    Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y

def forgetTag (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    TaggedColumn q₁ q₂ s Y → Paper2.SourceMatrix.RawColumn q₁ q₂ s Y
  | .inl Z => Z
  | .inr j => (Paper2.SourceMatrix.tail j.2, fun _ => j)

theorem forgetTag_surjective (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    Function.Surjective (forgetTag (q₁ := q₁) (q₂ := q₂) ξ₀) :=
  fun Z => ⟨.inl Z, rfl⟩

def oldTag : TaggedColumn q₁ q₂ s Y →
    Paper2.SourceMatrix.TaggedColumn q₁ q₂ s Y
  | .inl Z => .unrestricted Z
  | .inr j => .diagonal j

theorem forgetTag_eq_old (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : TaggedColumn q₁ q₂ s Y) :
    forgetTag ξ₀ Z = Paper2.SourceMatrix.forgetTag ξ₀ (oldTag Z) := by
  cases Z <;> rfl

noncomputable def matrix
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    TaggedColumn q₁ q₂ s Y →
      Paper2.SourceMatrix.RawRow q₁ q₂ s X (Items s V) → Bool :=
  fun Z k => Paper2.SourceMatrix.raw R
    (activity order edge hs r hq) k (forgetTag ξ₀ Z)

theorem matrix_eq_oldTag
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : TaggedColumn q₁ q₂ s Y)
    (k : Paper2.SourceMatrix.RawRow q₁ q₂ s X (Items s V)) :
    matrix order edge hs r hq R ξ₀ Z k =
      EdgeSourceMatrix.matrix order edge hs r hq R ξ₀ (oldTag Z) k := by
  cases Z <;> rfl

theorem matrix_ordinary
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (Z : Paper2.SourceMatrix.RawColumn q₁ q₂ s Y)
    (k : Paper2.SourceMatrix.RawRow q₁ q₂ s X (Items s V)) :
    matrix order edge hs r hq R ξ₀ (.inl Z) k =
      Paper2.SourceMatrix.raw R (activity order edge hs r hq) k Z := rfl

theorem matrix_diagonal
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (j : Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y)
    (k : Paper2.SourceMatrix.RawRow q₁ q₂ s X (Items s V)) :
    matrix order edge hs r hq R ξ₀ (.inr j) k =
      Paper2.SourceMatrix.raw R (activity order edge hs r hq) k
        (Paper2.SourceMatrix.tail j.2, fun _ => j) := rfl

theorem matrix_diagonal_source_active
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (j : Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y)
    (i : Items s V) (u : X) (b : Fin s)
    (ha : activity order edge hs r hq i j.1 = some b) :
    matrix order edge hs r hq R ξ₀ (.inr j) (.inr (i, u)) =
      R u (Paper2.SourceMatrix.tail j.2 b.castSucc) := by
  simp [matrix, Paper2.SourceMatrix.raw, Paper2.SourceMatrix.baseRequest,
    Paper2.SourceMatrix.sourceColumn, Paper2.SourceMatrix.sourcePosition,
    forgetTag, ha]

theorem matrix_diagonal_source_inactive
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (j : Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y)
    (i : Items s V) (u : X)
    (ha : activity order edge hs r hq i j.1 = none) :
    matrix order edge hs r hq R ξ₀ (.inr j) (.inr (i, u)) =
      R u (Paper2.SourceMatrix.tail j.2 (Fin.last s)) := by
  simp [matrix, Paper2.SourceMatrix.raw, Paper2.SourceMatrix.baseRequest,
    Paper2.SourceMatrix.sourceColumn, Paper2.SourceMatrix.sourcePosition,
    forgetTag, ha]

theorem q₂_positive {r : ℕ} (hr : 0 < r)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r) : 0 < q₂ := by
  rw [hq]
  exact EdgeSource.sourceQ2_pos hr

theorem q₁_positive (hs : 4 ≤ s) (hq₁ : q₁ + 2 = s) : 0 < q₁ := by
  omega

theorem vertices_nonempty (edge : E → Bool → V) (hE : 0 < Fintype.card E) :
    Nonempty V := by
  classical
  have hne : Nonempty E := Fintype.card_pos_iff.mp hE
  exact ⟨edge (Classical.choice hne) false⟩

theorem matrix_rank_le
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    (realMatrix (matrix (q₁ := q₁) order edge hs r hq R ξ₀)).rank ≤
      (s * q₁ * q₂ + Fintype.card (Items s V)) * (realMatrix R).rank := by
  change (realMatrix (fun Z k => Paper2.SourceMatrix.raw (q₁ := q₁) R
    (activity order edge hs r hq) k (forgetTag ξ₀ Z))).rank ≤ _
  rw [transpose_rank]
  have heq : (realMatrix (fun k Z => Paper2.SourceMatrix.raw (q₁ := q₁) R
      (activity order edge hs r hq) k (forgetTag ξ₀ Z))).rank =
      (realMatrix (Paper2.SourceMatrix.raw (q₁ := q₁) R
        (activity order edge hs r hq))).rank := by
    simpa only [id] using
      (pullback_rank_eq_of_surjective
        (Paper2.SourceMatrix.raw (q₁ := q₁) R (activity order edge hs r hq)) id
        (forgetTag ξ₀) Function.surjective_id (forgetTag_surjective ξ₀))
  rw [heq]
  exact Paper2.SourceMatrix.raw_rank_le R (activity order edge hs r hq)

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
  have hm : D (matrix (q₁ := q₁) order edge hs r hq R ξ₀) ≤
      D (EdgeSourceMatrix.matrix (q₁ := q₁) order edge hs r hq R ξ₀) := by
    have hp := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
      (EdgeSourceMatrix.matrix (q₁ := q₁) order edge hs r hq R ξ₀)
      (oldTag (q₁ := q₁) (q₂ := q₂) (s := s)) id
    simpa only [id, ← matrix_eq_oldTag] using hp
  obtain ⟨hu, hy⟩ := EdgeSourceMatrix.matrix_upper_budgets
    order edge hs r hq R ξ₀ a b hq₁ hsa hqb
  refine ⟨hm.trans hu, ?_⟩
  intro colour proper
  exact hm.trans (hy colour proper)

/-- Exactly the two v38 tagged input families. -/
noncomputable def taggedLaw [NeZero q₂]
    (ν : Paper2.PositiveRationalLaw Y) :
    Paper2.PositiveRationalLaw (TaggedColumn q₁ q₂ s Y) where
  weight
    | .inl Z => (255 / 256) *
        (Paper2.SourceLaws.rawLaw ν q₁ q₂ s).weight Z
    | .inr j => (1 / 256) *
        (Paper2.SourceLaws.outerLaw ν q₁ q₂ s).weight j
  positive Z := by
    cases Z with
    | inl Z =>
      exact mul_pos (by norm_num) ((Paper2.SourceLaws.rawLaw ν q₁ q₂ s).positive Z)
    | inr j =>
      exact mul_pos (by norm_num) ((Paper2.SourceLaws.outerLaw ν q₁ q₂ s).positive j)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum, Paper2.PositiveRationalLaw.total, mul_one]
    norm_num

theorem tagged_prob [NeZero q₂]
    (ν : Paper2.PositiveRationalLaw Y)
    (P : TaggedColumn q₁ q₂ s Y → Prop) :
    (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob P =
      (255 / 256 : ℝ) *
        (Paper2.SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => P (.inl Z)) +
      (1 / 256 : ℝ) *
        (Paper2.SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob (fun j => P (.inr j)) := by
  classical
  unfold Paper2.FiniteLaw.prob
  rw [Fintype.sum_sum_type]
  simp only [Paper2.PositiveRationalLaw.toFiniteLaw, taggedLaw,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum]
  simp only [mul_ite, mul_zero]

theorem tag_masses [NeZero q₂]
    (ν : Paper2.PositiveRationalLaw Y) :
    (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob
      (fun Z => ∃ j, Z = Sum.inl j) = 255 / 256 ∧
    (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob
      (fun Z => ∃ j, Z = Sum.inr j) = 1 / 256 := by
  simp only [tagged_prob]
  simp

theorem bin_marginal [NeZero q₂]
    (ν : Paper2.PositiveRationalLaw Y)
    (ξ₀ : Paper2.SourceMatrix.Tail s Y) (p : Fin s)
    (P : Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y → Prop) :
    (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.prob
      (fun Z => P ((forgetTag ξ₀ Z).2 p)) =
      (Paper2.SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob P := by
  rw [tagged_prob]
  change (255 / 256 : ℝ) *
      (Paper2.SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => P (Z.2 p)) +
      (1 / 256 : ℝ) *
      (Paper2.SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob P = _
  rw [Paper2.SourceLaws.unrestricted_bin_marginal]
  ring

noncomputable def columnLaw [Nonempty V] [NeZero q₁]
    (μ : Paper2.PositiveRationalLaw X) (hs : 4 ≤ s) :
    Paper2.PositiveRationalLaw
      (Paper2.SourceMatrix.RawRow q₁ q₂ s X (Items s V)) :=
  EdgeSourceMatrix.matrixColumnLaw μ hs

theorem column_family_masses [Nonempty V] [NeZero q₁]
    (μ : Paper2.PositiveRationalLaw X) (hs : 4 ≤ s) :
    (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 0) = 255 / 256 ∧
    (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 1) = 1 / 512 ∧
    (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 2) = 1 / 512 :=
  EdgeSourceMatrix.column_family_masses μ hs

#print axioms matrix_rank_le
#print axioms matrix_diagonal_source_active
#print axioms matrix_diagonal_source_inactive
#print axioms matrix_upper_budgets
#print axioms tagged_prob
#print axioms tag_masses
#print axioms bin_marginal
#print axioms column_family_masses

end CurrentAdditive.V38Matrix
