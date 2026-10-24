import EthInapproximability.CurrentPaper.MatrixIndexSplit
import EthInapproximability.CurrentPaper.MatrixUnaryCut
import EthInapproximability.CurrentPaper.MatrixWeightedTable

/-!
# Explicit quotient/remainder addresses for the weighted duplicate

The column address first removes the uniform-copy digit, then selects exactly
one of the `182`-weighted full support and `2`-weighted diagonal support.
Each group address is then split into an underlying label and its rational-
blowup copy digit.  The row address has four, not three, groups.  These are
total arithmetic decoders for ordinal addresses.  `split_run` supplies the
finite-stack unary quotient/remainder primitive; a complete compound decoder
with runtime remains an additional implementation obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedArithmetic

open WeightedDuplication MatrixMaterialization

universe u

/-- The two actual column groups, with the uniform digit kept last. -/
abbrev ColumnAddress (M D S : ℕ) :=
  ((Fin M × Fin (182 * D)) ⊕ (Fin D × Fin (2 * M))) × Fin S

def decodeColumn (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S)) : ColumnAddress M D S :=
  let outer := finProdFinEquiv.symm i
  let group := finSumFinEquiv.symm outer.1
  (match group with
    | .inl x => .inl (finProdFinEquiv.symm x)
    | .inr x => .inr (finProdFinEquiv.symm x), outer.2)

/-- The first quotient/remainder stage is an actual finite-stack run on the
unary ordinal and the unary uniform-copy divisor, including divisor zero. -/
def uniform_split_run (ordinal S : ℕ) :=
  MatrixIndexSplit.split_run ordinal S

/-- After removing the uniform digit, the fixed cut program decides whether
the address belongs to the full 182-weight group, preserving the threshold
and returning the diagonal group's residual address when appropriate. -/
def column_group_cut_run (ordinal M D S : ℕ) :=
  MatrixUnaryCut.cut_run (ordinal / S) (M * (182 * D))

/-- Both group-specific quotient/remainder stages use the same fixed unary
program; the divisors are the actual manuscript copy counts. -/
def full_group_split_run (ordinal D : ℕ) :=
  MatrixIndexSplit.split_run ordinal (182 * D)

def diagonal_group_split_run (ordinal M : ℕ) :=
  MatrixIndexSplit.split_run ordinal (2 * M)

/-- The four public row groups, with group-specific copy counts. -/
abbrev RowAddress (X T V B cx ct cv cb : ℕ) :=
  (Fin X × Fin cx) ⊕
    ((Fin T × Fin ct) ⊕ ((Fin V × Fin cv) ⊕ (Fin B × Fin cb)))

def decodeRow (X T V B cx ct cv cb : ℕ)
    (i : Fin (X * cx + (T * ct + (V * cv + B * cb)))) :
    RowAddress X T V B cx ct cv cb :=
  match finSumFinEquiv.symm i with
  | .inl x => .inl (finProdFinEquiv.symm x)
  | .inr rest =>
    match finSumFinEquiv.symm rest with
    | .inl x => .inr (.inl (finProdFinEquiv.symm x))
    | .inr rest' =>
      match finSumFinEquiv.symm rest' with
      | .inl x => .inr (.inr (.inl (finProdFinEquiv.symm x)))
      | .inr x => .inr (.inr (.inr (finProdFinEquiv.symm x)))

/-- The 182:2 split has precisely the manuscript's total, before the
uniform factor; this equality lets the arithmetic address target the actual
`WeightedDuplication.Columns` carrier count. -/
theorem column_total (M D S : ℕ) :
    (M * (182 * D) + D * (2 * M)) * S = 184 * M * D * S := by ring

/-- The four copy counts sum to the exact `2^22` protected-row factor. -/
theorem row_total (X T V B : ℕ) :
    X * ((2 ^ 22 - 4) * T * V * B) +
      (T * (2 * X * V * B) +
        (V * (X * T * B) + B * (X * T * V))) =
      2 ^ 22 * X * T * V * B := by
  norm_num
  ring

variable {X T V B Ω Δ : Type u}
variable [Fintype X] [Fintype T] [Fintype V] [Fintype B]
variable [Fintype Ω] [Fintype Δ]

/-- Actual typed column label decoded by the arithmetic 182:2 address. -/
def typedColumn (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (i : Fin (Fintype.card (Columns Ω Δ S))) : Columns Ω Δ S := by
  let M := Fintype.card Ω
  let D := Fintype.card Δ
  let a : Fin ((M * (182 * D) + D * (2 * M)) * S) :=
    i.cast (by rw [card_columns, column_total])
  let decoded := decodeColumn M D S a
  rcases decoded with ⟨tag, uniform⟩
  refine (match tag with
    | .inl ⟨x, copy⟩ =>
      (⟨0, (eΩ.symm x, copy.cast ?_)⟩, uniform)
    | .inr ⟨x, copy⟩ =>
      (⟨1, (eΔ.symm x, copy.cast ?_)⟩, uniform))
  · have he : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
    simp [copies, columnSupport, columnWeight, he]
    rfl
  · have he : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
    simp [copies, columnSupport, columnWeight, he]
    rfl

/-- Actual typed row label decoded from the four grouped quotients. -/
def typedRow (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (i : Fin (Fintype.card (Rows X T V B))) : Rows X T V B := by
  let x := Fintype.card X
  let t := Fintype.card T
  let v := Fintype.card V
  let b := Fintype.card B
  let cx := copies (rowSupport X T V B) rowWeight 0
  let ct := copies (rowSupport X T V B) rowWeight 1
  let cv := copies (rowSupport X T V B) rowWeight 2
  let cb := copies (rowSupport X T V B) rowWeight 3
  let a : Fin (x * cx + (t * ct + (v * cv + b * cb))) :=
    i.cast (by
      simp only [Rows, Carrier, Fintype.card_sigma]
      simp [Fin.sum_univ_succ, Fintype.card_prod, Fintype.card_fin,
        cx, ct, cv, cb, x, t, v, b])
  let decoded := decodeRow x t v b cx ct cv cb a
  match decoded with
  | .inl ⟨j, c⟩ => exact ⟨0, (eX.symm j, c)⟩
  | .inr (.inl ⟨j, c⟩) => exact ⟨1, (eT.symm j, c)⟩
  | .inr (.inr (.inl ⟨j, c⟩)) => exact ⟨2, (eV.symm j, c)⟩
  | .inr (.inr (.inr ⟨j, c⟩)) => exact ⟨3, (eB.symm j, c)⟩

/-- Row-major table directly indexed by quotient/remainder addresses. -/
def table (H : X → Ω → Bool) (iT : T → X) (iV : V → X)
    (iB : B → X) (iD : Δ → Ω) (S : ℕ)
    (eX : X ≃ Fin (Fintype.card X)) (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V)) (eB : B ≃ Fin (Fintype.card B))
    (eΩ : Ω ≃ Fin (Fintype.card Ω)) (eΔ : Δ ≃ Fin (Fintype.card Δ)) :
    List Bool :=
  rowMajor (fun i j => H (rowForget iT iV iB (typedRow eX eT eV eB j))
    (columnForget iD (typedColumn eΩ eΔ S i)))

theorem table_entry (H : X → Ω → Bool) (iT : T → X) (iV : V → X)
    (iB : B → X) (iD : Δ → Ω) (S : ℕ)
    (eX : X ≃ Fin (Fintype.card X)) (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V)) (eB : B ≃ Fin (Fintype.card B))
    (eΩ : Ω ≃ Fin (Fintype.card Ω)) (eΔ : Δ ≃ Fin (Fintype.card Δ))
    (i : Fin (Fintype.card (Columns Ω Δ S)))
    (j : Fin (Fintype.card (Rows X T V B))) :
    (table H iT iV iB iD S eX eT eV eB eΩ eΔ)[
      i.val * Fintype.card (Rows X T V B) + j.val]? =
      some (transposedMatrix H iT iV iB iD S
        (typedColumn eΩ eΔ S i) (typedRow eX eT eV eB j)) := by
  rw [table, rowMajor_entry]
  rfl

open Construction MatrixWeightedTable

/-- Arithmetic-addressed materialisation of the actual `N`, including the
joint-tail diagonal embedding and `|Rows(M₂)|^s` uniform copies. -/
def actualTable {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) : List Bool :=
  table (rawMatrix R a s q L nv nb hs family order vectors cap)
    (fun r : TemplateSupport s L => Sum.inl r.down)
    (fun r => Sum.inr (Sum.inl r)) (fun r => Sum.inr (Sum.inr r))
    diagonal (uniformCopies (Y := Fin cy) a s q)
    (rawRowCode s L nv nb rx order) (templateCode s L)
    (vertexCode nv rx) (auxiliaryCode nb rx)
    (rawColumnCode' a s q cy) (diagonalCode a s q cy)

@[simp] theorem actualTable_length {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    (actualTable R a s q L nv nb hs family order vectors cap).length =
      Fintype.card (ProtectedColumns a s q (Fin cy)) *
      Fintype.card (ProtectedRows s L nv nb (Fin rx)) := by
  simp [actualTable, table]

theorem actualTable_entry {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (j : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) :
    (actualTable R a s q L nv nb hs family order vectors cap)[
      i.val * Fintype.card (ProtectedRows s L nv nb (Fin rx)) + j.val]? =
      some (protectedMatrix R a s q L nv nb hs family order vectors cap
        (typedColumn (rawColumnCode' a s q cy) (diagonalCode a s q cy)
          (uniformCopies (Y := Fin cy) a s q) i)
        (typedRow (rawRowCode s L nv nb rx order) (templateCode s L)
          (vertexCode nv rx) (auxiliaryCode nb rx) j)) := by
  exact table_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _

end EthInapproximability.CurrentPaper.MatrixWeightedArithmetic
