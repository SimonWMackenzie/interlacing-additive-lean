import CurrentAdditive.V39ExecutableGenerated

/-! Explicit intermediate storage for det:reduction. Each round stores its
Boolean cells and both rational weight vectors. The next round reads these
stored arrays; it does not receive a source/profile certificate as input. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Workspace.Types.CommComplexity
open scoped BigOperators

structure StoredMatrix where
  rows : ℕ
  cols : ℕ
  cells : Vector Bool (rows*cols)
  rowWeights : Vector ℚ rows
  colWeights : Vector ℚ cols
  rowPositive : ∀ i : Fin rows, 0 < rowWeights[i]
  colPositive : ∀ i : Fin cols, 0 < colWeights[i]
  rowTotal : ∑ i : Fin rows, rowWeights[i] = 1
  colTotal : ∑ i : Fin cols, colWeights[i] = 1

namespace StoredMatrix

def rowLaw (R : StoredMatrix) : PositiveRationalLaw (Fin R.rows) :=
  ⟨fun i => R.rowWeights[i], R.rowPositive, R.rowTotal⟩

def colLaw (R : StoredMatrix) : PositiveRationalLaw (Fin R.cols) :=
  ⟨fun i => R.colWeights[i], R.colPositive, R.colTotal⟩

def entry (R : StoredMatrix) (r : Fin R.rows) (c : Fin R.cols) : Bool :=
  R.cells[finProdFinEquiv (r,c)]

def numbered (R : StoredMatrix) : NumberedMatrix :=
  ⟨R.rows, R.cols, R.rowLaw, R.colLaw, R.entry⟩

def ofNumbered (R : NumberedMatrix) : StoredMatrix where
  rows := R.rows
  cols := R.cols
  cells := Vector.ofFn (fun i => R.entry (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm i).2)
  rowWeights := Vector.ofFn R.rowLaw.weight
  colWeights := Vector.ofFn R.colLaw.weight
  rowPositive i := by simpa using R.rowLaw.positive i
  colPositive i := by simpa using R.colLaw.positive i
  rowTotal := by simpa using R.rowLaw.total
  colTotal := by simpa using R.colLaw.total

@[simp] theorem ofNumbered_entry (R : NumberedMatrix)
    (r : Fin R.rows) (c : Fin R.cols) :
    (ofNumbered R).entry r c = R.entry r c := by
  change (Vector.ofFn (fun i : Fin (R.rows*R.cols) =>
    R.entry (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2))[
      (finProdFinEquiv (r,c)).val] = R.entry r c
  rw [Vector.getElem_ofFn]
  change R.entry (finProdFinEquiv.symm (finProdFinEquiv (r,c))).1
    (finProdFinEquiv.symm (finProdFinEquiv (r,c))).2 = R.entry r c
  rw [Equiv.symm_apply_apply]

private theorem law_eq_of_weights {n : ℕ}
    (μ ν : PositiveRationalLaw (Fin n)) (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

@[simp] theorem ofNumbered_numbered (R : NumberedMatrix) :
    (ofNumbered R).numbered = R := by
  cases R with
  | mk rows cols rowLaw colLaw entry =>
    simp only [ofNumbered, numbered]
    congr
    · apply law_eq_of_weights
      funext i
      change (Vector.ofFn rowLaw.weight)[i.val] = rowLaw.weight i
      rw [Vector.getElem_ofFn]
    · apply law_eq_of_weights
      funext i
      change (Vector.ofFn colLaw.weight)[i.val] = colLaw.weight i
      rw [Vector.getElem_ofFn]
    · funext r c
      exact ofNumbered_entry ⟨rows, cols, rowLaw, colLaw, entry⟩ r c

variable {q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

def step (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    StoredMatrix :=
  ofNumbered (executableStep (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity R.numbered)

def iterate (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (k : ℕ) (R : StoredMatrix) : StoredMatrix :=
  Nat.rec R (fun _ M => step (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity M) k

theorem iterate_numbered (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (k : ℕ) (R : StoredMatrix) :
    (iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R).numbered =
      executableIterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
        μI activity k R.numbered := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (ofNumbered (executableStep (q₁ := q₁) (s := s) (w := w) (Q := Q)
      μI activity (iterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
        μI activity k R).numbered)).numbered = _
    rw [ofNumbered_numbered, ih]
    rfl

theorem iterate_yes (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (k : ℕ) (R : StoredMatrix) (assign : Fin ni → Fin s)
    (hc : Paper2.SourceMatrix.CollisionFree assign activity) :
    D (iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R).entry ≤
      D R.entry + k*(Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+2)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  have he := iterate_numbered (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity k R
  have hy := executable_yes (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity k R.numbered assign hc
  rw [← he] at hy
  exact hy

def rectangle (R : StoredMatrix) (b : ℕ) := R.numbered.rectangle b

theorem rectangle_valid (R : StoredMatrix) (b : ℕ) : (R.rectangle b).Valid :=
  R.numbered.rectangle_valid b

end StoredMatrix
end CurrentAdditive.V39GeneratedConstruction
