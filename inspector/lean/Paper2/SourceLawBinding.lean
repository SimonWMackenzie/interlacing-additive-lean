import Paper2.SourceConstruction
import Paper2.SourceLaws

/-!
# Protected laws on the graph-constructed source matrix

Frozen v12 Section 4, the input laws preceding and following `eq:mixture`.
`SourceLaws` first separates vertex and auxiliary item families as a sum of
two products. The actual graph constructor uses a product with that sum.
The explicit distributivity equivalence below transports the law, with no
change to the activity map, matrix entries, labels within either family,
or protected masses. The final matrix is transposed: its row law is the
tagged-column law, and its column law is the transported raw-row law.

The assumption `4 ≤ s` ensures that the auxiliary population is nonempty;
its positive mass must not be placed on an empty carrier. These are finite
distributional constructions, not a machine-time sampling bound.
-/

namespace Paper2

namespace PositiveRationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Push a positive rational law through an actual bijection of labels. -/
noncomputable def relabel (μ : PositiveRationalLaw A) (e : A ≃ B) :
    PositiveRationalLaw B where
  weight b := μ.weight (e.symm b)
  positive b := μ.positive (e.symm b)
  total := (e.symm.sum_comp μ.weight).trans μ.total

theorem relabel_prob (μ : PositiveRationalLaw A) (e : A ≃ B) (E : B → Prop) :
    (μ.relabel e).toFiniteLaw.prob E = μ.toFiniteLaw.prob (fun a => E (e a)) := by
  classical
  have h := e.symm.sum_comp (fun a => if E (e a) then (μ.weight a : ℝ) else 0)
  simpa only [FiniteLaw.prob, toFiniteLaw, relabel, e.apply_symm_apply] using h

end PositiveRationalLaw

namespace SourceLawBinding

open SourceMatrix

variable {V X Y : Type*} {q₁ q₂ s : ℕ}

/-- The same labelled items, reassociated without identifying any labels. -/
def itemEquiv (s : ℕ) (V : Type*) :
    ((Fin (4 * s) × V) ⊕ (Fin (4 * s) × Fin (s - 3))) ≃
      SourceConstruction.Items s V where
  toFun
    | .inl (g, v) => (g, .inl v)
    | .inr (g, a) => (g, .inr a)
  invFun
    | (g, .inl v) => .inl (g, v)
    | (g, .inr a) => .inr (g, a)
  left_inv i := by rcases i with ⟨g, v⟩ | ⟨g, a⟩ <;> rfl
  right_inv i := by rcases i with ⟨g, v | a⟩ <;> rfl

def rawRowEquiv (q₁ q₂ s : ℕ) (X V : Type*) :
    RawRow q₁ q₂ s X ((Fin (4 * s) × V) ⊕ (Fin (4 * s) × Fin (s - 3))) ≃
      RawRow q₁ q₂ s X (SourceConstruction.Items s V) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (itemEquiv s V) (Equiv.refl X))

/-- The law on the actual *rows* of the transposed graph source. -/
noncomputable def matrixRowLaw [Fintype Y] (ν : PositiveRationalLaw Y)
    (q₁ q₂ s : ℕ) [NeZero q₂] :
    PositiveRationalLaw (TaggedColumn q₁ q₂ s Y) := SourceLaws.taggedLaw ν q₁ q₂ s

/-- The law on the actual *columns* of the transposed graph source. -/
noncomputable def matrixColumnLaw [Fintype V] [Nonempty V] [Fintype X]
    (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ) [NeZero q₁] (hs : 4 ≤ s) :
    PositiveRationalLaw (RawRow q₁ q₂ s X (SourceConstruction.Items s V)) := by
  letI : NeZero s := ⟨by omega⟩
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  exact (SourceLaws.rowLaw (V := Fin (4 * s) × V) (A := Fin (4 * s) × Fin (s - 3))
    μ q₁ q₂ s).relabel (rawRowEquiv q₁ q₂ s X V)

def columnFamilyIndex : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin 3
  | .inl _ => 0
  | .inr ((_, .inl _), _) => 1
  | .inr ((_, .inr _), _) => 2

theorem familyIndex_equiv
    (k : RawRow q₁ q₂ s X ((Fin (4 * s) × V) ⊕ (Fin (4 * s) × Fin (s - 3)))) :
    columnFamilyIndex (rawRowEquiv q₁ q₂ s X V k) = SourceLaws.rowFamilyIndex k := by
  rcases k with k | ⟨⟨g, v⟩ | ⟨g, a⟩, x⟩ <;> rfl

section ColumnLaw

variable [Fintype V] [Nonempty V] [Fintype X] [NeZero q₁]

noncomputable def templateFamilyLaw (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] (hs : 4 ≤ s) : PositiveRationalLaw (Fin s × Template q₁ q₂ X) := by
  letI : NeZero s := ⟨by omega⟩
  exact SourceLaws.templateRowLaw μ q₁ q₂ s

noncomputable def vertexFamilyLaw (μ : PositiveRationalLaw X) (s : ℕ) (hs : 4 ≤ s) :
    PositiveRationalLaw ((Fin (4 * s) × V) × X) := by
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  exact SourceLaws.itemRowLaw μ (Fin (4 * s) × V)

noncomputable def auxiliaryFamilyLaw (μ : PositiveRationalLaw X) (s : ℕ) (hs : 4 ≤ s) :
    PositiveRationalLaw ((Fin (4 * s) × Fin (s - 3)) × X) := by
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  exact SourceLaws.itemRowLaw μ (Fin (4 * s) × Fin (s - 3))

theorem column_prob (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (E : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop) :
    (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob E =
      (255 / 256 : ℝ) * (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw.prob
        (fun k => E (.inl k)) +
      (1 / 512 : ℝ) * (vertexFamilyLaw μ s hs).toFiniteLaw.prob
        (fun k => E (.inr ((k.1.1, .inl k.1.2), k.2))) +
      (1 / 512 : ℝ) * (auxiliaryFamilyLaw μ s hs).toFiniteLaw.prob
        (fun k => E (.inr ((k.1.1, .inr k.1.2), k.2))) := by
  letI : NeZero s := ⟨by omega⟩
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  unfold matrixColumnLaw
  rw [PositiveRationalLaw.relabel_prob, SourceLaws.row_prob]
  rfl

theorem column_family_masses (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prob
      (fun k => columnFamilyIndex k = 0) = 255 / 256 ∧
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prob
      (fun k => columnFamilyIndex k = 1) = 1 / 512 ∧
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prob
      (fun k => columnFamilyIndex k = 2) = 1 / 512 := by
  letI : NeZero s := ⟨by omega⟩
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  simp only [column_prob, columnFamilyIndex]
  norm_num [Fin.ext_iff]

def templateBinEvent (p : Fin s) (E : Template q₁ q₂ X → Prop) :
    RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop
  | .inl k => k.1 = p ∧ E k.2
  | .inr _ => False

theorem column_template_bin_law (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (p : Fin s) (E : Template q₁ q₂ X → Prop) :
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prob (templateBinEvent p E) =
      (255 / 256 : ℝ) * (s : ℝ)⁻¹ * (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob E := by
  letI : NeZero s := ⟨by omega⟩
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  rw [column_prob]
  simp only [templateBinEvent, FiniteLaw.prob_false, mul_zero, add_zero]
  change (255 / 256 : ℝ) * (SourceLaws.templateRowLaw μ q₁ q₂ s).toFiniteLaw.prob
    (fun k => k.1 = p ∧ E k.2) = _
  rw [SourceLaws.fixed_template_bin_law]
  ring

def vertexEvent (E : ((Fin (4 * s) × V) × X) → Prop) :
    RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop
  | .inr ((g, .inl v), x) => E ((g, v), x)
  | _ => False

def auxiliaryEvent (E : ((Fin (4 * s) × Fin (s - 3)) × X) → Prop) :
    RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop
  | .inr ((g, .inr a), x) => E ((g, a), x)
  | _ => False

/-- Retaining arbitrary vertex-label/base-row events gives exactly their
uniform-label, original-base-law mass, scaled by the protected family mass. -/
theorem column_vertex_law (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (E : ((Fin (4 * s) × V) × X) → Prop) :
    (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (vertexEvent E) =
      (1 / 512 : ℝ) * (vertexFamilyLaw μ s hs).toFiniteLaw.prob E := by
  rw [column_prob]
  simp [vertexEvent]

theorem column_auxiliary_law (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (E : ((Fin (4 * s) × Fin (s - 3)) × X) → Prop) :
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prob (auxiliaryEvent E) =
      (1 / 512 : ℝ) * (auxiliaryFamilyLaw μ s hs).toFiniteLaw.prob E := by
  rw [column_prob]
  simp [auxiliaryEvent]

omit [NeZero q₁] in
theorem vertex_base_marginal (μ : PositiveRationalLaw X) (hs : 4 ≤ s) (E : X → Prop) :
    (vertexFamilyLaw (V := V) μ s hs).toFiniteLaw.prob (fun k => E k.2) =
      μ.toFiniteLaw.prob E := by
  unfold vertexFamilyLaw SourceLaws.itemRowLaw
  rw [PositiveRationalLaw.toFiniteLaw_prod, FiniteLaw.prod_prob_snd]

omit [NeZero q₁] [Fintype V] [Nonempty V] in
theorem auxiliary_base_marginal (μ : PositiveRationalLaw X) (hs : 4 ≤ s) (E : X → Prop) :
    (auxiliaryFamilyLaw μ s hs).toFiniteLaw.prob (fun k => E k.2) =
      μ.toFiniteLaw.prob E := by
  unfold auxiliaryFamilyLaw SourceLaws.itemRowLaw
  rw [PositiveRationalLaw.toFiniteLaw_prod, FiniteLaw.prod_prob_snd]

end ColumnLaw

section RowLaw

variable [Fintype Y] [NeZero q₂]

theorem row_tag_masses (ν : PositiveRationalLaw Y) :
    (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => SourceLaws.tagIndex Z = 0) = 127 / 128 ∧
    (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => SourceLaws.tagIndex Z = 1) = 1 / 256 ∧
    (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => SourceLaws.tagIndex Z = 2) = 1 / 256 :=
  SourceLaws.tag_masses ν q₁ q₂ s

theorem row_bin_marginal (ν : PositiveRationalLaw Y) (ξ₀ : Tail s Y) (p : Fin s)
    (E : OuterColumn q₁ q₂ s Y → Prop) :
    (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => E (SourceLaws.binProjection ξ₀ p Z)) =
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob E :=
  SourceLaws.tagged_bin_marginal ν q₁ q₂ s ξ₀ p E

end RowLaw

/-- The label bijection used by the law commutes with the actual source
entry formula. It changes neither the graph activity nor the selected base
entry; only the association of the vertex/auxiliary item type changes. -/
theorem matrix_entry_relabel {E : Type*} [Fintype E] [Fintype V]
    [NeZero s]
    (order : SourceConstruction.Items s V ≃ Fin (Fintype.card (SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (Z : TaggedColumn q₁ q₂ s Y)
    (k : RawRow q₁ q₂ s X ((Fin (4 * s) × V) ⊕ (Fin (4 * s) × Fin (s - 3)))) :
    SourceConstruction.matrix order edge hs r hq R ξ₀ Z (rawRowEquiv q₁ q₂ s X V k) =
      N R (fun i α => SourceConstruction.activity order edge hs r hq (itemEquiv s V i) α)
        ξ₀ Z k := by
  rcases k with k | ⟨i, x⟩ <;> rfl

end SourceLawBinding
end Paper2
