import CurrentAdditive.EntryArithmetic

namespace CurrentAdditive.EliminationEntryBounds

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialArrayBridge
open CurrentAdditive.SequentialCompressionTotality

theorem featureRows_zero_one_local {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1) :
    ∀ i : Fin (featureRows n φ source).size,
      ∀ j : Fin (columnCount (featureRows n φ source)),
        matrixOfArray (featureRows n φ source) i j = 0 ∨
          matrixOfArray (featureRows n φ source) i j = 1 := by
  intro i j
  let a := featureRows n φ source
  have hi : i.val < n := by simpa [a, featureRows] using i.isLt
  by_cases hj : j.val < source.size
  · have hcell : matrixOfArray a i j = φ (source[j.val]).1 ⟨i.val, hi⟩ := by
      simp [matrixOfArray, cell, a, featureRows, hi, hj]
    rw [hcell]
    exact hφ _ _
  · have hcell : matrixOfArray a i j = 0 := by
      simp [matrixOfArray, cell, a, featureRows, hi, hj]
    exact Or.inl hcell

/-- Reinterpret the actual array matrix as an integer zero--one matrix. This
is an exact equality after casting, including the array default cells. -/
theorem array_zero_one_integerization (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1) :
    ∃ A : Matrix (Fin a.size) (Fin (columnCount a)) ℤ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (fun i j => (A i j : ℚ)) = matrixOfArray a := by
  classical
  let A : Matrix (Fin a.size) (Fin (columnCount a)) ℤ :=
    fun i j => if matrixOfArray a i j = 0 then 0 else 1
  refine ⟨A, ?_, ?_⟩
  · intro i j
    by_cases hz : matrixOfArray a i j = 0
    · left; simp [A, hz]
    · right; simp [A, hz]
  · funext i j
    rcases h01 i j with hz | ho
    · simp [A, hz]
    · simp [A, ho]

/-- The eager cursor associated with any actual zero--one array has bounded
canonical rational entries after every recursive scan step. -/
theorem array_everyGaussStep_bits (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1)
    (t : ℕ) (ht : t ≤ columnCount a)
    (i : Fin a.size) (j : Fin (columnCount a)) :
    let B := (cursorAfter (matrixOfArray a) t).B
    Nat.size (B i j).den ≤
      (a.size + 3) * (a.size + 1) ^ 2 + 1 ∧
    Nat.size (B i j).num.natAbs ≤
      (a.size + 3) * (a.size + 1) ^ 2 + 1 := by
  obtain ⟨A, hA, hcast⟩ := array_zero_one_integerization a h01
  change Nat.size ((cursorAfter (matrixOfArray a) t).B i j).den ≤
      (a.size + 3) * (a.size + 1) ^ 2 + 1 ∧
    Nat.size ((cursorAfter (matrixOfArray a) t).B i j).num.natAbs ≤
      (a.size + 3) * (a.size + 1) ^ 2 + 1
  rw [← hcast]
  exact every_actual_step_entry_bits A hA t ht i j

theorem featureRows_everyGaussStep_bits {α : Type*}
    (n : ℕ) (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (t : ℕ) (ht : t ≤ columnCount (featureRows n φ source))
    (i : Fin (featureRows n φ source).size)
    (j : Fin (columnCount (featureRows n φ source))) :
    let a := featureRows n φ source
    let B := (cursorAfter (matrixOfArray a) t).B
    Nat.size (B i j).den ≤
      (a.size + 3) * (a.size + 1) ^ 2 + 1 ∧
    Nat.size (B i j).num.natAbs ≤
      (a.size + 3) * (a.size + 1) ^ 2 + 1 := by
  exact array_everyGaussStep_bits (featureRows n φ source)
    (featureRows_zero_one_local n φ source hφ) t ht i j

theorem featureRows_shape {α : Type*}
    (n : ℕ) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (hn : 0 < n) :
    (featureRows n φ source).size = n ∧
    columnCount (featureRows n φ source) = source.size := by
  constructor
  · simp [featureRows]
  · exact featureRows_columnCount n φ source hn

theorem generatedFeatureRows_everyGaussStep_bits {Y : Type*}
    [DecidableEq Y] (q D : ℕ) (alphabet : Array Y)
    (source : Array ((Fin q → Y) × ℚ))
    (t : ℕ)
    (ht : t ≤ columnCount
      (featureRows (generatedFeatures q D alphabet).size
        (fun v j => generatedFeatureValue v
          (generatedFeatures q D alphabet)[j]) source)) :
    let F := generatedFeatures q D alphabet
    let φ : (Fin q → Y) → Fin F.size → ℚ :=
      fun v j => generatedFeatureValue v F[j]
    let a := featureRows F.size φ source
    ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      let B := (cursorAfter (matrixOfArray a) t).B
      Nat.size (B i j).den ≤
        (a.size + 3) * (a.size + 1) ^ 2 + 1 ∧
      Nat.size (B i j).num.natAbs ≤
        (a.size + 3) * (a.size + 1) ^ 2 + 1 := by
  intro F φ a i j
  apply featureRows_everyGaussStep_bits F.size φ source
  · intro v h
    dsimp [φ, generatedFeatureValue]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact ht

end CurrentAdditive.EliminationEntryBounds
