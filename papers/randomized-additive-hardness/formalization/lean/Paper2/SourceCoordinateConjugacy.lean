import Paper2.SourceMatrix

/-!
One-step coordinate conjugacy for the literal source matrix. The permutation
maps new numerical addresses to old numerical addresses.
-/

namespace Paper2.SourceCoordinateConjugacy

open SourceMatrix

variable {X X' Y Y' I : Type*} {q₁ q₂ s : ℕ}

def activityNew (π : Fin q₂ ≃ Fin q₂)
    (activity : I → Fin q₂ → Option (Fin s)) :
    I → Fin q₂ → Option (Fin s) := fun i α => activity i (π α)

def templateMap (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (z : Template q₁ q₂ X) : Template q₁ q₂ X' :=
  fun α => ((z (π α)).1, eX ((z (π α)).2))

def outerMap (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (j : OuterColumn q₁ q₂ s Y) : OuterColumn q₁ q₂ s Y' :=
  (π.symm j.1, fun t => eY (j.2 t))

def rawRowMap (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (k : RawRow q₁ q₂ s X I) : RawRow q₁ q₂ s X' I :=
  match k with
  | .inl (p, z) => .inl (p, templateMap π eX z)
  | .inr (i, x) => .inr (i, eX x)

def rawColumnMap (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (Z : RawColumn q₁ q₂ s Y) : RawColumn q₁ q₂ s Y' :=
  (fun t => eY (Z.1 t), fun p => outerMap π eY (Z.2 p))

def taggedMap (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (Z : TaggedColumn q₁ q₂ s Y) : TaggedColumn q₁ q₂ s Y' :=
  match Z with
  | .unrestricted raw => .unrestricted (rawColumnMap π eY raw)
  | .fixedTail js => .fixedTail (fun p => outerMap π eY (js p))
  | .diagonal j => .diagonal (outerMap π eY j)

def tailMap (eY : Y ≃ Y') (ξ : Tail s Y) : Tail s Y' :=
  fun t => eY (ξ t)

theorem templateMap_inverse (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (z : Template q₁ q₂ X) :
    templateMap π.symm eX.symm (templateMap π eX z) = z := by
  funext α
  simp [templateMap]

theorem outerMap_inverse (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (j : OuterColumn q₁ q₂ s Y) :
    outerMap π.symm eY.symm (outerMap π eY j) = j := by
  ext <;> simp [outerMap]

theorem rawRowMap_inverse (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (k : RawRow q₁ q₂ s X I) :
    rawRowMap π.symm eX.symm (rawRowMap π eX k) = k := by
  rcases k with ⟨p,z⟩ | ⟨i,x⟩
  · simp [rawRowMap, templateMap_inverse]
  · simp [rawRowMap]

theorem rawColumnMap_inverse (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (Z : RawColumn q₁ q₂ s Y) :
    rawColumnMap π.symm eY.symm (rawColumnMap π eY Z) = Z := by
  ext <;> simp [rawColumnMap, outerMap_inverse]

theorem taggedMap_inverse (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (Z : TaggedColumn q₁ q₂ s Y) :
    taggedMap π.symm eY.symm (taggedMap π eY Z) = Z := by
  cases Z with
  | unrestricted raw => simp [taggedMap, rawColumnMap_inverse]
  | fixedTail js => simp [taggedMap, outerMap_inverse]
  | diagonal j => simp [taggedMap, outerMap_inverse]

def rawRowEquiv (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') :
    RawRow q₁ q₂ s X I ≃ RawRow q₁ q₂ s X' I where
  toFun := rawRowMap π eX
  invFun := rawRowMap π.symm eX.symm
  left_inv := rawRowMap_inverse π eX
  right_inv := rawRowMap_inverse π.symm eX.symm

def rawColumnEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    RawColumn q₁ q₂ s Y ≃ RawColumn q₁ q₂ s Y' where
  toFun := rawColumnMap π eY
  invFun := rawColumnMap π.symm eY.symm
  left_inv := rawColumnMap_inverse π eY
  right_inv := rawColumnMap_inverse π.symm eY.symm

def taggedEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    TaggedColumn q₁ q₂ s Y ≃ TaggedColumn q₁ q₂ s Y' where
  toFun := taggedMap π eY
  invFun := taggedMap π.symm eY.symm
  left_inv := taggedMap_inverse π eY
  right_inv := taggedMap_inverse π.symm eY.symm

theorem sourcePosition_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eY : Y ≃ Y') (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (Z : RawColumn q₁ q₂ s Y) :
    sourcePosition (activityNew π activity) i (rawColumnMap π eY Z) =
      sourcePosition activity i Z := by
  have htest :
      (∀ p, ((rawColumnMap π eY Z).2 p).1 =
        ((rawColumnMap π eY Z).2 0).1) ↔
      (∀ p, (Z.2 p).1 = (Z.2 0).1) := by
    simp only [rawColumnMap, outerMap]
    constructor
    · intro h p
      exact π.symm.injective (h p)
    · intro h p
      exact congrArg π.symm (h p)
  unfold sourcePosition
  by_cases h : ∀ p, (Z.2 p).1 = (Z.2 0).1
  · rw [if_pos h, if_pos (htest.mpr h)]
    simp [activityNew, rawColumnMap, outerMap]
  · rw [if_neg h, if_neg (fun hh => h (htest.mp hh))]

theorem offDiagonal_fallback_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eY : Y ≃ Y') (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (Z : RawColumn q₁ q₂ s Y)
    (h : ¬ ∀ p, (Z.2 p).1 = (Z.2 0).1) :
    sourcePosition (activityNew π activity) i (rawColumnMap π eY Z) =
      Fin.last s ∧ sourcePosition activity i Z = Fin.last s := by
  have hold := SourceMatrix.sourcePosition_offDiagonal activity i Z h
  exact ⟨(sourcePosition_map π eY activity i Z).trans hold, hold⟩

theorem inactive_diagonal_fallback_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eY : Y ≃ Y') (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (j : OuterColumn q₁ q₂ s Y) (ξ : Tail s Y)
    (h : activity i j.1 = none) :
    sourcePosition (activityNew π activity) i
      (forgetTag (tailMap eY ξ) (.diagonal (outerMap π eY j))) = Fin.last s ∧
    sourcePosition activity i (forgetTag ξ (.diagonal j)) = Fin.last s := by
  have hold := SourceMatrix.sourcePosition_diagonal activity i j ξ
  have hnew := SourceMatrix.sourcePosition_diagonal
    (activityNew π activity) i (outerMap π eY j) (tailMap eY ξ)
  constructor
  · rw [hnew]
    simp [activityNew, outerMap, h]
  · rw [hold]
    simp [h]

theorem sourceColumn_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eY : Y ≃ Y') (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (Z : RawColumn q₁ q₂ s Y) :
    sourceColumn (activityNew π activity) i (rawColumnMap π eY Z) =
      eY (sourceColumn activity i Z) := by
  change eY (Z.1 (sourcePosition (activityNew π activity) i
    (rawColumnMap π eY Z))) = eY (Z.1 (sourcePosition activity i Z))
  rw [sourcePosition_map]

theorem baseRequest_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X ≃ X') (eY : Y ≃ Y')
    (activity : I → Fin q₂ → Option (Fin s))
    (k : RawRow q₁ q₂ s X I) (Z : RawColumn q₁ q₂ s Y) :
    baseRequest (activityNew π activity) (rawRowMap π eX k)
      (rawColumnMap π eY Z) =
      (eX (baseRequest activity k Z).1,
        eY (baseRequest activity k Z).2) := by
  rcases k with ⟨p,z⟩ | ⟨i,x⟩
  · simp [baseRequest, rawRowMap, rawColumnMap, outerMap,
      templateMap, head]
  · simp [baseRequest, rawRowMap, sourceColumn_map]

theorem forgetTag_map (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (ξ : Tail s Y) (Z : TaggedColumn q₁ q₂ s Y) :
    forgetTag (tailMap eY ξ) (taggedMap π eY Z) =
      rawColumnMap π eY (forgetTag ξ Z) := by
  cases Z with
  | unrestricted raw => rfl
  | fixedTail js => rfl
  | diagonal j =>
      ext <;> simp [forgetTag, rawColumnMap, taggedMap, outerMap,
        tail]

theorem N_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X ≃ X') (eY : Y ≃ Y')
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tail s Y) (Z : TaggedColumn q₁ q₂ s Y)
    (k : RawRow q₁ q₂ s X I) :
    N (fun x y => R (eX.symm x) (eY.symm y))
      (activityNew π activity) (tailMap eY ξ)
      (taggedMap π eY Z) (rawRowMap π eX k) =
        N R activity ξ Z k := by
  simp only [N, raw, forgetTag_map, baseRequest_map]
  simp

#print axioms baseRequest_map
#print axioms offDiagonal_fallback_map
#print axioms inactive_diagonal_fallback_map
#print axioms forgetTag_map
#print axioms N_map

end Paper2.SourceCoordinateConjugacy
