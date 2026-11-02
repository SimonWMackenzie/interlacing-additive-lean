import Paper2.SourceCoordinateConjugacy
import Paper2.CoordinateLawTransport

/-! One-step transport of the literal protected source laws. The coordinate
equivalence is oriented from new addresses to old addresses. -/

namespace Paper2.SourceLawCoordinateTransport

open SourceMatrix SourceLaws SourceCoordinateConjugacy

variable {X X' Y Y' V A : Type*} {q₁ q₂ s : ℕ}
variable [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']

private theorem uniform_weight {B C : Type*} [Fintype B] [Fintype C]
    [Nonempty B] [Nonempty C] (e : B ≃ C) (b : B) :
    (PositiveRationalLaw.uniform C).weight (e b) =
      (PositiveRationalLaw.uniform B).weight b := by
  simp [PositiveRationalLaw.uniform, Fintype.card_congr e]

private theorem prod_weight {B B' C C' : Type*}
    [Fintype B] [Fintype B'] [Fintype C] [Fintype C']
    (μ : PositiveRationalLaw B) (μ' : PositiveRationalLaw B')
    (ν : PositiveRationalLaw C) (ν' : PositiveRationalLaw C')
    (eB : B ≃ B') (eC : C ≃ C')
    (hB : ∀ b, μ'.weight (eB b) = μ.weight b)
    (hC : ∀ c, ν'.weight (eC c) = ν.weight c)
    (p : B × C) :
    (μ'.prod ν').weight (eB p.1, eC p.2) = (μ.prod ν).weight p := by
  simp [PositiveRationalLaw.prod, hB, hC]

private theorem law_pushes {B C : Type*} [Fintype B] [Fintype C]
    (μ : PositiveRationalLaw B) (ν : PositiveRationalLaw C)
    (e : B ≃ C) (h : ∀ b, ν.weight (e b) = μ.weight b) :
    μ.toFiniteLaw.PushesTo ν.toFiniteLaw e := by
  intro E
  classical
  unfold FiniteLaw.prob
  have hs := e.sum_comp (fun c => if E c then (ν.weight c : ℝ) else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw, h] using hs

def outerEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    OuterColumn q₁ q₂ s Y ≃ OuterColumn q₁ q₂ s Y' :=
  Equiv.prodCongr π.symm
    (CoordinateLawTransport.tupleEquiv (q₁ + s + 1) (Equiv.refl _) eY)

def fixedTailEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    (Fin s → OuterColumn q₁ q₂ s Y) ≃
      (Fin s → OuterColumn q₁ q₂ s Y') :=
  CoordinateLawTransport.tupleEquiv s (Equiv.refl _) (outerEquiv π eY)

theorem outer_weight [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (j : OuterColumn q₁ q₂ s Y) :
    (outerLaw ν' q₁ q₂ s).weight (outerMap π eY j) =
      (outerLaw ν q₁ q₂ s).weight j := by
  simp only [outerLaw, PositiveRationalLaw.prod, outerMap]
  rw [uniform_weight π.symm j.1]
  exact congrArg ((PositiveRationalLaw.uniform (Fin q₂)).weight j.1 * ·)
    (CoordinateLawTransport.iid_weight ν ν' (q₁ + s + 1)
      (Equiv.refl _) eY hY j.2)

theorem fixedTail_weight [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (js : Fin s → OuterColumn q₁ q₂ s Y) :
    (fixedTailLaw ν' q₁ q₂ s).weight (fun p => outerMap π eY (js p)) =
      (fixedTailLaw ν q₁ q₂ s).weight js := by
  simp only [fixedTailLaw, PositiveRationalLaw.iid]
  simp_rw [outer_weight ν ν' π eY hY]

theorem raw_weight [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (Z : RawColumn q₁ q₂ s Y) :
    (rawLaw ν' q₁ q₂ s).weight (rawColumnMap π eY Z) =
      (rawLaw ν q₁ q₂ s).weight Z := by
  simp only [rawLaw, PositiveRationalLaw.prod, rawColumnMap]
  simp only [PositiveRationalLaw.iid]
  simp_rw [hY, outer_weight ν ν' π eY hY]

theorem tagged_weight [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (Z : TaggedColumn q₁ q₂ s Y) :
    (taggedLaw ν' q₁ q₂ s).weight (taggedMap π eY Z) =
      (taggedLaw ν q₁ q₂ s).weight Z := by
  cases Z with
  | unrestricted raw => exact congrArg ((127 / 128 : ℚ) * ·) (raw_weight ν ν' π eY hY raw)
  | fixedTail js => exact congrArg ((1 / 256 : ℚ) * ·) (fixedTail_weight ν ν' π eY hY js)
  | diagonal j => exact congrArg ((1 / 256 : ℚ) * ·) (outer_weight ν ν' π eY hY j)

theorem outer_pushes [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) :
    (outerLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      (outerLaw ν' q₁ q₂ s).toFiniteLaw (outerEquiv π eY) :=
  law_pushes _ _ _ (outer_weight ν ν' π eY hY)

theorem fixedTail_pushes [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) :
    (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      (fixedTailLaw ν' q₁ q₂ s).toFiniteLaw (fixedTailEquiv π eY) :=
  law_pushes _ _ _ (fixedTail_weight ν ν' π eY hY)

theorem raw_pushes [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) :
    (rawLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      (rawLaw ν' q₁ q₂ s).toFiniteLaw (rawColumnEquiv π eY) :=
  law_pushes _ _ _ (raw_weight ν ν' π eY hY)

theorem tagged_pushes [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) :
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      (taggedLaw ν' q₁ q₂ s).toFiniteLaw (taggedEquiv π eY) :=
  law_pushes _ _ _ (tagged_weight ν ν' π eY hY)

section Rows

variable [Fintype V] [Fintype A] [Nonempty V] [Nonempty A]

theorem template_weight [NeZero q₁]
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (z : Template q₁ q₂ X) :
    (templateLaw μ' q₁ q₂).weight (templateMap π eX z) =
      (templateLaw μ q₁ q₂).weight z := by
  have hinner : ∀ a : InnerRow q₁ X,
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ').weight
        ((Equiv.prodCongr (Equiv.refl _) eX) a) =
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).weight a := by
    intro a
    simp [PositiveRationalLaw.prod, hX]
  exact CoordinateLawTransport.iid_weight
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ') q₂ π
    (Equiv.prodCongr (Equiv.refl _) eX) hinner z

theorem templateRow_weight [NeZero q₁] [NeZero s]
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (k : Fin s × Template q₁ q₂ X) :
    (templateRowLaw μ' q₁ q₂ s).weight (k.1, templateMap π eX k.2) =
      (templateRowLaw μ q₁ q₂ s).weight k := by
  simp only [templateRowLaw, PositiveRationalLaw.prod]
  rw [template_weight μ μ' π eX hX k.2]

theorem itemRow_weight {J : Type*} [Fintype J] [Nonempty J]
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (eX : X ≃ X') (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (k : J × X) :
    (itemRowLaw μ' J).weight (k.1, eX k.2) =
      (itemRowLaw μ J).weight k := by
  simp [itemRowLaw, PositiveRationalLaw.prod, hX]

theorem row_weight [NeZero q₁] [NeZero s]
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (k : RawRow q₁ q₂ s X (V ⊕ A)) :
    (rowLaw (V := V) (A := A) μ' q₁ q₂ s).weight (rawRowMap π eX k) =
      (rowLaw (V := V) (A := A) μ q₁ q₂ s).weight k := by
  rcases k with k | ⟨i, x⟩
  · exact congrArg ((255 / 256 : ℚ) * ·) (templateRow_weight μ μ' π eX hX k)
  · rcases i with v | a
    · exact congrArg ((1 / 512 : ℚ) * ·) (itemRow_weight μ μ' eX hX (v, x))
    · exact congrArg ((1 / 512 : ℚ) * ·) (itemRow_weight μ μ' eX hX (a, x))

theorem row_pushes [NeZero q₁] [NeZero s]
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x) :
    (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.PushesTo
      (rowLaw (V := V) (A := A) μ' q₁ q₂ s).toFiniteLaw
      (rawRowEquiv (I := V ⊕ A) π eX) :=
  law_pushes _ _ _ (row_weight μ μ' π eX hX)

end Rows

section GraphCarrier

variable [Fintype V] [Nonempty V] [NeZero q₁]

omit [Fintype X] [Fintype X'] [Fintype V] [Nonempty V] [NeZero q₁] in
/-- Reassociation of the two item families commutes with changing base-row
values and permuting the labelled template coordinates. -/
theorem binding_rawRow_commutes
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (k : RawRow q₁ q₂ s X
      ((Fin (4 * s) × V) ⊕ (Fin (4 * s) × Fin (s - 3)))) :
    rawRowMap π eX (SourceLawBinding.rawRowEquiv q₁ q₂ s X V k) =
      SourceLawBinding.rawRowEquiv q₁ q₂ s X' V (rawRowMap π eX k) := by
  rcases k with k | ⟨i, x⟩
  · rfl
  · rcases i with ⟨g, v⟩ | ⟨g, a⟩ <;> rfl

/-- The actual graph source's transposed column law, after its
item-family reassociation, is preserved pointwise. -/
theorem matrixColumn_weight (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (k : RawRow q₁ q₂ s X (SourceConstruction.Items s V)) :
    (SourceLawBinding.matrixColumnLaw μ' q₁ q₂ s hs).weight
      (rawRowMap π eX k) =
      (SourceLawBinding.matrixColumnLaw μ q₁ q₂ s hs).weight k := by
  letI : NeZero s := ⟨by omega⟩
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k₀, rfl⟩ := (SourceLawBinding.rawRowEquiv q₁ q₂ s X V).surjective k
  rw [binding_rawRow_commutes]
  simp only [SourceLawBinding.matrixColumnLaw, PositiveRationalLaw.relabel,
    Equiv.symm_apply_apply]
  exact row_weight (V := Fin (4 * s) × V)
    (A := Fin (4 * s) × Fin (s - 3)) μ μ' π eX hX k₀

theorem matrixColumn_pushes (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x) :
    (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.PushesTo
      (SourceLawBinding.matrixColumnLaw (V := V) μ' q₁ q₂ s hs).toFiniteLaw
      (rawRowEquiv (I := SourceConstruction.Items s V) π eX) :=
  law_pushes _ _ _ (matrixColumn_weight hs μ μ' π eX hX)

omit [NeZero q₁] in
theorem matrixRow_pushes [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) :
    (SourceLawBinding.matrixRowLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      (SourceLawBinding.matrixRowLaw ν' q₁ q₂ s).toFiniteLaw
      (taggedEquiv π eY) :=
  tagged_pushes ν ν' π eY hY

end GraphCarrier

end Paper2.SourceLawCoordinateTransport

#print axioms Paper2.SourceLawCoordinateTransport.outer_pushes
#print axioms Paper2.SourceLawCoordinateTransport.fixedTail_pushes
#print axioms Paper2.SourceLawCoordinateTransport.raw_pushes
#print axioms Paper2.SourceLawCoordinateTransport.tagged_pushes
#print axioms Paper2.SourceLawCoordinateTransport.row_pushes
#print axioms Paper2.SourceLawCoordinateTransport.matrixColumn_pushes
#print axioms Paper2.SourceLawCoordinateTransport.matrixRow_pushes
